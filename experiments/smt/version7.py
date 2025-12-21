# version6.py  (or version3.py if you like)
#
# Monolithic zone-based SMT encoding of:
#  - TaskNet abstract syntax (mirror of Lean)
#  - Schedule constraints (StartEndTimesOk + NoSimultaneousAssignments)
#  - Zone-based execution with impacts
#  - Timeline ranges + pre/inv/post checked on the zone trace
#
# One solver call gives: schedule + zone-trace satisfying all constraints.

from __future__ import annotations
from dataclasses import dataclass
from typing import List, Optional, Dict, Union, Literal, Tuple

from z3 import (
    Solver, Int, Real, Bool,
    And, Or, Not, If,
    sat,
)

# ============================================================
# 1. Python AST (mirror of Lean TaskNet syntax)
# ============================================================

TaskNetName  = str
TaskName     = str
TaskId       = int
TimeLineName = str
Time         = int

@dataclass
class IntRange:
    low: int
    high: int

@dataclass
class RealRange:
    low: float
    high: float

# ----- Values -----

@dataclass
class IntVal:
    v: int

@dataclass
class RealVal:
    v: float

@dataclass
class StrVal:
    v: str

@dataclass
class BoolVal:
    v: bool

Value = Union[IntVal, RealVal, StrVal, BoolVal]

# ----- Timelines -----

@dataclass
class StateTimeline:
    id: TimeLineName
    states: List[str]
    initial: str

@dataclass
class AtomicTimeline:
    id: TimeLineName

@dataclass
class ClaimableTimeline:
    id: TimeLineName
    range: RealRange
    initial: float

@dataclass
class CumulativeTimeline:
    id: TimeLineName
    range: RealRange
    bounds: RealRange
    initial: float

@dataclass
class RateTimeline:
    id: TimeLineName
    range: RealRange
    bounds: RealRange
    initial: float

Timeline = Union[
    StateTimeline,
    AtomicTimeline,
    ClaimableTimeline,
    CumulativeTimeline,
    RateTimeline,
]

# ----- Impacts -----

ImpactWhen = Literal["pre", "maint", "post"]

@dataclass
class ImpactAssign:
    v: Value

@dataclass
class ImpactCumulative:
    v: float

@dataclass
class ImpactRate:
    r: float

ImpactHow = Union[ImpactAssign, ImpactCumulative, ImpactRate]

@dataclass
class Impact:
    id: TimeLineName
    when: ImpactWhen
    how: ImpactHow

# ----- Conditions -----

@dataclass
class ConVal:
    v: Value

@dataclass
class ConIntRange:
    r: IntRange

@dataclass
class ConRealRange:
    r: RealRange

Con = Union[ConVal, ConIntRange, ConRealRange]

@dataclass
class TlCon:
    id: TimeLineName
    cons: List[Con]

# ----- Tasks -----

@dataclass
class TaskDef:
    id: TaskName
    ident: TaskId
    priority: int
    startrng: IntRange
    endrng: IntRange
    dur: int
    start: int  # "intended" start, not enforced by solver
    after: List[str]
    pre: List[TlCon]
    inv: List[TlCon]
    post: List[TlCon]
    impacts: List[Impact]

@dataclass
class TaskNet:
    id: TaskNetName
    timelines: List[Timeline]
    tasks: List[TaskDef]
    endTime: int

# ============================================================
# 2. Zone-based SMT encoding
# ============================================================

class TaskNetSMT:
    """
    Zone-based SMT encoding:

      - start/end times for each task
      - zone boundaries (0, task starts/ends, endTime)
      - state of each timeline at each zone boundary
      - impact semantics over each zone
      - range constraints for numeric timelines
      - pre/inv/post obligations over the zone trace

    Uses *one* solver call to find schedule + trace satisfying everything.
    """

    def __init__(self, tn: TaskNet):
        self.tn = tn
        self.solver = Solver()
        # self.T = tn.endTime  # final time

        # === 2.1 Schedule variables ===
        self.start_vars: Dict[str, object] = {}
        self.end_vars: Dict[str, object] = {}
        self._mk_schedule_vars()
        self._encode_start_end_times_ok()
        self._encode_no_simultaneous_assignments()

        # === 2.2 Zone boundaries ===
        # At most 2*|tasks| + 2 unique boundaries: 0, endTime, all start/end's
        self.zone_count = 2 * len(tn.tasks) + 2
        self.zones = [Int(f"z_{i}") for i in range(self.zone_count)]
        self._encode_zones()

        # === 2.3 State at each zone for each timeline ===
        # state timelines: id -> (states, str->idx, idx->str, [Int vars])
        self.state_tl_zone: Dict[str, Tuple[List[str], Dict[str, int], Dict[int, str], List]] = {}
        # atomic timelines: id -> [Bool vars]
        self.atomic_tl_zone: Dict[str, List] = {}
        # numeric timelines: id -> (range, bounds_opt, [Real vars])
        self.numeric_tl_zone: Dict[str, Tuple[RealRange, Optional[RealRange], List]] = {}

        self._mk_zone_state_vars()
        self._encode_initial_state_zones()
        self._encode_zone_transitions()
        self._encode_timeline_ranges()
        self._encode_pre_inv_post_zones()

    # ------------------------------
    # 2.1 Schedule vars + constraints
    # ------------------------------

    def _mk_schedule_vars(self):
        for t in self.tn.tasks:
            s = Int(f"start_{t.id}")
            e = Int(f"end_{t.id}")
            self.start_vars[t.id] = s
            self.end_vars[t.id] = e

    def _encode_start_end_times_ok(self):
        n = self.tn.endTime
        tasks = self.tn.tasks

        # Basic constraints for each task
        for t in tasks:
            s = self.start_vars[t.id]
            e = self.end_vars[t.id]

            # Start/end within global horizon and ordered
            self.solver.add(s >= 0, s <= e, e <= n)

            # start,end within given ranges
            self.solver.add(s >= t.startrng.low, s <= t.startrng.high)
            self.solver.add(e >= t.endrng.low,   e <= t.endrng.high)

            # duration
            self.solver.add(e - s == t.dur)

            # after dependencies
            for bid in t.after:
                if bid not in self.end_vars:
                    # ill-formed TaskNet — forbid
                    self.solver.add(False)
                else:
                    self.solver.add(self.end_vars[bid] <= s)

        # --- NEW: all task boundaries are pairwise distinct ---
        for i in range(len(tasks)):
            ti = tasks[i]
            si = self.start_vars[ti.id]
            ei = self.end_vars[ti.id]
            for j in range(i + 1, len(tasks)):
                tj = tasks[j]
                sj = self.start_vars[tj.id]
                ej = self.end_vars[tj.id]

                # no start/start, end/end, start/end, end/start coincidences
                self.solver.add(si != sj)
                self.solver.add(ei != ej)
                self.solver.add(si != ej)
                self.solver.add(ei != sj)

    def _encode_no_simultaneous_assignments(self):
        """
        No two tasks may assign the same timeline at the same time.
        (Only for ImpactAssign; numeric impacts can overlap.)
        """
        tasks = self.tn.tasks
        assign_points: List[Tuple[TaskName, TimeLineName, object]] = []

        for t in tasks:
            s = self.start_vars[t.id]
            e = self.end_vars[t.id]
            for imp in t.impacts:
                if isinstance(imp.how, ImpactAssign):
                    if imp.when == "pre":
                        assign_points.append((t.id, imp.id, s))
                    elif imp.when == "post":
                        assign_points.append((t.id, imp.id, e))
                    else:  # maint + assign is disallowed per spec
                        self.solver.add(False)

        m = len(assign_points)
        for i in range(m):
            _, id_i, time_i = assign_points[i]
            for j in range(i + 1, m):
                _, id_j, time_j = assign_points[j]
                if id_i == id_j:
                    self.solver.add(time_i != time_j)

    # ------------------------------
    # 2.2 Zones
    # ------------------------------

    def _encode_zones(self):
        """
        zones[i] = time of zone boundary i, with
          z_0   = 0
          z_last = endTime
          z_i < z_{i+1}  (strictly increasing)

        and we enforce a *bijection* between internal zones z_1..z_{last-1}
        and all task start/end times:

          - every task start/end equals some internal z_j
          - every internal z_j equals some task start or end
        """
        n = self.tn.endTime
        z = self.zones
        last = self.zone_count - 1
        tasks = self.tn.tasks

        # First / last
        self.solver.add(z[0] == 0)
        self.solver.add(z[last] == n)

        # Strictly increasing
        for i in range(last):
            self.solver.add(z[i] < z[i + 1])

        # Each start/end must be equal to *some* internal zone
        for t in tasks:
            s = self.start_vars[t.id]
            e = self.end_vars[t.id]
            self.solver.add(Or(*[s == z[j] for j in range(1, last)]))
            self.solver.add(Or(*[e == z[j] for j in range(1, last)]))

        # Each internal zone must be equal to *some* start or end
        for j in range(1, last):
            self.solver.add(
                Or(*[
                    Or(self.start_vars[t.id] == z[j],
                       self.end_vars[t.id] == z[j])
                    for t in tasks
                ])
            )

    # ------------------------------
    # 2.3 State-at-zone variables
    # ------------------------------

    def _mk_zone_state_vars(self):
        Z = self.zone_count
        for tl in self.tn.timelines:
            if isinstance(tl, StateTimeline):
                states = tl.states
                s2i = {s: i for (i, s) in enumerate(states)}
                i2s = {i: s for (i, s) in enumerate(states)}
                vars_z = [Int(f"{tl.id}_z{j}") for j in range(Z)]
                self.state_tl_zone[tl.id] = (states, s2i, i2s, vars_z)
                # Constrain domain of state
                for v in vars_z:
                    self.solver.add(v >= 0, v < len(states))

            elif isinstance(tl, AtomicTimeline):
                vars_z = [Bool(f"{tl.id}_z{j}") for j in range(Z)]
                self.atomic_tl_zone[tl.id] = vars_z

            elif isinstance(tl, ClaimableTimeline):
                vars_z = [Real(f"{tl.id}_z{j}") for j in range(Z)]
                self.numeric_tl_zone[tl.id] = (tl.range, None, vars_z)

            elif isinstance(tl, CumulativeTimeline):
                vars_z = [Real(f"{tl.id}_z{j}") for j in range(Z)]
                self.numeric_tl_zone[tl.id] = (tl.range, tl.bounds, vars_z)

            elif isinstance(tl, RateTimeline):
                vars_z = [Real(f"{tl.id}_z{j}") for j in range(Z)]
                self.numeric_tl_zone[tl.id] = (tl.range, tl.bounds, vars_z)

    def _encode_initial_state_zones(self):
        # Zone 0 corresponds to time 0
        z0_idx = 0
        for tl in self.tn.timelines:
            if isinstance(tl, StateTimeline):
                _, s2i, _, vars_z = self.state_tl_zone[tl.id]
                self.solver.add(vars_z[z0_idx] == s2i[tl.initial])

            elif isinstance(tl, AtomicTimeline):
                vars_z = self.atomic_tl_zone[tl.id]
                self.solver.add(vars_z[z0_idx] == False)

            elif isinstance(tl, ClaimableTimeline):
                _, _, vars_z = self.numeric_tl_zone[tl.id]
                self.solver.add(vars_z[z0_idx] == tl.initial)

            elif isinstance(tl, CumulativeTimeline):
                _, _, vars_z = self.numeric_tl_zone[tl.id]
                self.solver.add(vars_z[z0_idx] == tl.initial)

            elif isinstance(tl, RateTimeline):
                _, _, vars_z = self.numeric_tl_zone[tl.id]
                self.solver.add(vars_z[z0_idx] == tl.initial)

    # ------------------------------
    # 2.4 Impact semantics over zones
    # ------------------------------

    def _numeric_delta_zone(self, tl_id: str, zone_i: int):
        """
        Sum of all numeric deltas over zone i for numeric timelines
        (cumulative + rate).
        Zone i spans [z_i, z_{i+1}].
        """
        z = self.zones
        zi = z[zone_i]
        zi1 = z[zone_i + 1]
        dt = zi1 - zi  # length of zone i as an Int expression

        terms = []
        for t in self.tn.tasks:
            s = self.start_vars[t.id]
            e = self.end_vars[t.id]
            for imp in t.impacts:
                if imp.id != tl_id:
                    continue
                how = imp.how
                when = imp.when

                # CUMULATIVE: no dependence on dt, just boundary events
                if isinstance(how, ImpactCumulative):
                    v = how.v
                    if when == "pre":
                        # instant change at start time: applied at boundary zi
                        terms.append(If(zi == s, v, 0.0))
                    elif when == "maint":
                        # +v at start, -v at end (as in previous discrete encoding)
                        terms.append(
                            If(zi == s, v,
                               If(zi == e, -v, 0.0))
                        )
                    elif when == "post":
                        terms.append(If(zi == e, v, 0.0))

                # RATE: r * dt while task active over the entire zone
                elif isinstance(how, ImpactRate):
                    r = how.r

                    # We assume zi, zi1, dt are already defined above in your function.
                    # Semantics:
                    #   pre   : rate active from start time onward
                    #   maint : rate active only while task is active (start <= t < end)
                    #   post  : rate active from end time onward

                    active_pre   = (zi >= s)                 # t ≥ start
                    active_maint = And(zi >= s, zi < e)      # start ≤ t < end
                    active_post  = (zi >= e)                 # t ≥ end

                    if when == "pre":
                        terms.append(If(active_pre, r * dt, 0.0))
                    elif when == "maint":
                        terms.append(If(active_maint, r * dt, 0.0))
                    elif when == "post":
                        terms.append(If(active_post, r * dt, 0.0))
                # Assign to numeric timelines is not used in example; forbid
                elif isinstance(how, ImpactAssign):
                    # If this occurs, treat as ill-typed
                    self.solver.add(False)

        if not terms:
            return 0.0
        total = terms[0]
        for term in terms[1:]:
            total = total + term
        return total

    def _encode_zone_transitions(self):
        """
        For each zone i, encode state_z[i+1] as a function of state_z[i],
        schedule, and impacts over that zone.
        """
        Z = self.zone_count

        # State / atomic timelines: assign-only, no numeric deltas
        for tl in self.tn.timelines:
            if isinstance(tl, StateTimeline):
                _, s2i, _, vars_z = self.state_tl_zone[tl.id]
                for i in range(Z - 1):
                    cur = vars_z[i]
                    expr = cur
                    zi = self.zones[i]
                    # Apply assigns at boundaries (pre/post)
                    for t in self.tn.tasks:
                        s = self.start_vars[t.id]
                        e = self.end_vars[t.id]
                        for imp in t.impacts:
                            if imp.id != tl.id:
                                continue
                            if not isinstance(imp.how, ImpactAssign):
                                continue
                            v = imp.how.v
                            if not isinstance(v, StrVal):
                                self.solver.add(False)
                                continue
                            idx = s2i[v.v]
                            # We apply assignments at the boundary *after* checking pre,
                            # i.e. they affect the transition to zone i+1.
                            if imp.when == "pre":
                                expr = If(zi == s, idx, expr)
                            elif imp.when == "post":
                                expr = If(zi == e, idx, expr)
                            else:
                                # maint+assign disallowed
                                self.solver.add(False)
                    self.solver.add(vars_z[i + 1] == expr)

            elif isinstance(tl, AtomicTimeline):
                vars_z = self.atomic_tl_zone[tl.id]
                for i in range(Z - 1):
                    cur = vars_z[i]
                    expr = cur
                    zi = self.zones[i]
                    for t in self.tn.tasks:
                        s = self.start_vars[t.id]
                        e = self.end_vars[t.id]
                        for imp in t.impacts:
                            if imp.id != tl.id:
                                continue
                            if not isinstance(imp.how, ImpactAssign):
                                continue
                            v = imp.how.v
                            if not isinstance(v, BoolVal):
                                self.solver.add(False)
                                continue
                            if imp.when == "pre":
                                expr = If(zi == s, v.v, expr)
                            elif imp.when == "post":
                                expr = If(zi == e, v.v, expr)
                            else:
                                self.solver.add(False)
                    self.solver.add(vars_z[i + 1] == expr)

        # Numeric timelines: deltas + clamping by bounds (not by range!)
        for tl in self.tn.timelines:
            if isinstance(tl, (ClaimableTimeline, CumulativeTimeline, RateTimeline)):
                range_r, bounds_opt, vars_z = self.numeric_tl_zone[tl.id]

                if bounds_opt is not None:
                    low_bnd, high_bnd = bounds_opt.low, bounds_opt.high
                else:
                    low_bnd, high_bnd = None, None

                for i in range(Z - 1):
                    cur = vars_z[i]
                    delta = self._numeric_delta_zone(tl.id, i)
                    raw = cur + delta

                    if bounds_opt is not None:
                        clamped = If(raw < low_bnd, low_bnd,
                                     If(raw > high_bnd, high_bnd, raw))
                    else:
                        clamped = raw

                    self.solver.add(vars_z[i + 1] == clamped)

    def _encode_timeline_ranges(self):
        """
        Enforce TimeLineRangeOk: for numeric timelines, the value at *all*
        zone boundaries lies within the declared RealRange.
        (State timelines are already domain-restricted, atomic are Bool.)
        """
        for tl_id, (range_r, _bounds, vars_z) in self.numeric_tl_zone.items():
            lo, hi = range_r.low, range_r.high
            for v in vars_z:
                self.solver.add(v >= lo, v <= hi)

    # ------------------------------
    # 2.5 pre / inv / post (zone-based)
    # ------------------------------

    def _tl_value_at_zone(self, tl_id: str, zi: int):
        """
        Return a pair (kind, expr) describing the value of timeline tl_id at zone index zi.
        kind in {"state", "atomic", "real"} with the appropriate Z3 expression.
        """
        if tl_id in self.state_tl_zone:
            _, _, _, vars_z = self.state_tl_zone[tl_id]
            return "state", vars_z[zi]
        if tl_id in self.atomic_tl_zone:
            vars_z = self.atomic_tl_zone[tl_id]
            return "atomic", vars_z[zi]
        if tl_id in self.numeric_tl_zone:
            _, _, vars_z = self.numeric_tl_zone[tl_id]
            return "real", vars_z[zi]
        # Unknown timeline id: impossible in well-formed spec
        self.solver.add(False)
        dummy = Real("dummy_unknown_timeline")
        return "real", dummy

    def _con_holds_zone(self, tl_id: str, con: Con, zi: int):
        """
        SMT formula for a single Con on timeline tl_id at zone index zi.
        A TlCon is OR over such formulas.
        """
        kind, expr = self._tl_value_at_zone(tl_id, zi)

        if isinstance(con, ConVal):
            v = con.v
            if isinstance(v, StrVal):
                if kind != "state":
                    self.solver.add(False)
                    return False
                _, s2i, _, _ = self.state_tl_zone[tl_id]
                idx = s2i[v.v]
                return expr == idx

            if isinstance(v, BoolVal):
                if kind != "atomic":
                    self.solver.add(False)
                    return False
                return expr == v.v

            if isinstance(v, IntVal):
                # Treat as equality on real-valued numeric TL
                if kind != "real":
                    self.solver.add(False)
                    return False
                return expr == v.v

            if isinstance(v, RealVal):
                if kind != "real":
                    self.solver.add(False)
                    return False
                return expr == v.v

        elif isinstance(con, ConRealRange):
            if kind != "real":
                self.solver.add(False)
                return False
            lo, hi = con.r.low, con.r.high
            return And(expr >= lo, expr <= hi)

        elif isinstance(con, ConIntRange):
            if kind != "real":
                self.solver.add(False)
                return False
            lo, hi = con.r.low, con.r.high
            return And(expr >= lo, expr <= hi)

        # Unsupported combination; forbid
        self.solver.add(False)
        return False

    def _tlcon_holds_zone(self, tlc: TlCon, zi: int):
        """
        SMT formula for one TlCon at zone index zi:
          OR over its cons.
        """
        if not tlc.cons:
            # Empty list => False
            return False
        clauses = [self._con_holds_zone(tlc.id, c, zi) for c in tlc.cons]
        return Or(*clauses)

    def _conds_holds_zone(self, conds: List[TlCon], zi: int):
        """
        SMT formula for a list of TlCon at zone index zi:
          AND over TlCon (each TlCon is an OR of Cons).
        Empty list => True.
        """
        if not conds:
            return True
        return And(*[self._tlcon_holds_zone(c, zi) for c in conds])

    def _encode_pre_inv_post_zones(self):
        """
        Zone-based obligations:

        For each task t:

          - PRE:
              For each zone index j:
                (start_t == z_j) -> pre holds at zone j.

          - POST:
              For each zone index j:
                (end_t == z_j) -> post holds at zone j.

          - INV:
              For each zone index j:
                (z_j in [start_t, end_t]) -> inv holds at zone j.
        """
        Z = self.zone_count
        z = self.zones

        for t in self.tn.tasks:
            s = self.start_vars[t.id]
            e = self.end_vars[t.id]

            for j in range(Z):
                pre_formula  = self._conds_holds_zone(t.pre, j)
                inv_formula  = self._conds_holds_zone(t.inv, j)
                post_formula = self._conds_holds_zone(t.post, j)

                zj = z[j]

                # PRE at start
                self.solver.add(Or(zj != s, pre_formula))

                # POST at end
                self.solver.add(Or(zj != e, post_formula))

                # INV whenever active (inclusive bounds)
                self.solver.add(
                    Or(
                        zj < s,
                        zj > e,
                        inv_formula
                    )
                )

    # ------------------------------
    # 2.6 Solving + pretty-printing
    # ------------------------------

    def solve(self):
        res = self.solver.check()
        if res != sat:
            print("TaskNet constraints (schedule + zone trace):", res)
            return None
        return self.solver.model()

    def extract_schedule(self, model):
        sched: Dict[str, Tuple[int, int]] = {}
        for t in self.tn.tasks:
            s_val = model[self.start_vars[t.id]]
            e_val = model[self.end_vars[t.id]]
            sched[t.id] = (int(s_val.as_long()), int(e_val.as_long()))
        return sched

    def pretty_print(self, model):
        # 1) Schedule
        print(f"Schedule for TaskNet `{self.tn.id}`:")
        sched = self.extract_schedule(model)
        for t in self.tn.tasks:
            s, e = sched[t.id]
            print(f"  {t.id:14s}: start = {s:4d}, end = {e:4d}")

        # 2) Zone boundaries
        print("\nZone boundaries (z_i):")
        for i, zi in enumerate(self.zones):
            val = model[zi].as_long()
            print(f"  z_{i:2d} = {val}")

        # 3) Values in each zone ( (z_j, z_{j+1}] )
        print("\nValues in each zone:")
        Z = self.zone_count
        for j in range(Z - 1):
            t0 = model[self.zones[j]].as_long()
            t1 = model[self.zones[j + 1]].as_long()
            print(f"\n  -- zone {j}: ({t0}, {t1}] --")

            # Use LEFT boundary t0 to decide activity:
            # task active in zone j iff start_t ≤ t0 < end_t
            active: List[str] = []
            for t in self.tn.tasks:
                s, e = sched[t.id]
                if s <= t0 < e:
                    active.append(t.id)

            if active:
                print(f"    active tasks : {', '.join(active)}")
            else:
                print(f"    active tasks : (none)")

            # For non-rate timelines, interior value is piecewise constant
            # and represented by state at boundary j+1.
            idx_interior = j + 1

            for tl in self.tn.timelines:
                # --- State timelines ---
                if isinstance(tl, StateTimeline):
                    _, _, i2s, vars_z = self.state_tl_zone[tl.id]
                    idx = model[vars_z[idx_interior]].as_long()
                    print(f"    {tl.id:14s} = {i2s[idx]}")

                # --- Atomic timelines ---
                elif isinstance(tl, AtomicTimeline):
                    vars_z = self.atomic_tl_zone[tl.id]
                    val = model[vars_z[idx_interior]]
                    print(f"    {tl.id:14s} = {val}")

                # --- Numeric timelines: piecewise-constant types ---
                elif isinstance(tl, (ClaimableTimeline, CumulativeTimeline)):
                    _, _, vars_z = self.numeric_tl_zone[tl.id]
                    val = model[vars_z[idx_interior]]
                    print(f"    {tl.id:14s} = {val.as_decimal(6)}")

                # --- Numeric timelines: rate types ---
                elif isinstance(tl, RateTimeline):
                    _, _, vars_z = self.numeric_tl_zone[tl.id]
                    v_start = model[vars_z[j]]
                    v_end   = model[vars_z[j + 1]]
                    print(
                        f"    {tl.id:14s} = "
                        f"{v_start.as_decimal(6)} -> {v_end.as_decimal(6)}"
                    )
      
# ============================================================
# 3. Your Heat/Drive/Communicate TaskNet in Python
# ============================================================

def make_example_tasknet() -> TaskNet:
    timelines: List[Timeline] = [
        StateTimeline("heating",       ["off", "on"], "off"),
        StateTimeline("driving",       ["off", "on"], "off"),
        StateTimeline("communicating", ["off", "on"], "off"),
        AtomicTimeline("radio"),
        ClaimableTimeline("memory", RealRange(0.0, 100.0), 100.0),
        RateTimeline("distance", RealRange(0.0, 100.0), RealRange(0.0, 100.0), 100.0),
        RateTimeline("temperature", RealRange(0.0, 100.0), RealRange(0.0, 100.0), 50.0),
        RateTimeline("battery",     RealRange(20.0, 100.0), RealRange(0.0, 100.0), 100.0),
    ]

    off = StrVal("off")
    on  = StrVal("on")

    heating = TaskDef(
        id       = "heating",
        ident    = 1,
        priority = 1,
        startrng = IntRange(0, 20),
        endrng   = IntRange(80, 100),
        dur      = 80,
        start    = 10,
        after    = [],
        pre = [
            TlCon("driving",       [ConVal(off)]),
            TlCon("communicating", [ConVal(off)]),
            TlCon("battery",       [ConRealRange(RealRange(40.0, 100.0))]),
        ],
        inv = [
            TlCon("driving",       [ConVal(off)]),
            TlCon("communicating", [ConVal(off)]),
            TlCon("battery",       [ConRealRange(RealRange(30.0, 100.0))]),
        ],
        post = [
            TlCon("temperature",   [ConRealRange(RealRange(20.0, 100.0))]),
        ],
        impacts = [
            Impact("heating",     "pre",   ImpactAssign(on)),
            Impact("heating",     "post",  ImpactAssign(off)),
            Impact("temperature", "maint", ImpactRate(+1.0)),
            Impact("battery",     "maint", ImpactRate(-0.01)),
        ],
    )

    driving = TaskDef(
        id       = "driving",
        ident    = 2,
        priority = 1,
        startrng = IntRange(100, 120),
        endrng   = IntRange(180, 200),
        dur      = 80,
        start    = 110,
        after    = ["heating"],
        pre = [
            TlCon("communicating", [ConVal(off)]),
            TlCon("distance",      [ConRealRange(RealRange(5.0, 100.0))]),
            TlCon("temperature",   [ConRealRange(RealRange(50.0, 100.0))]),
            TlCon("battery",       [ConRealRange(RealRange(40.0, 100.0))]),
        ],
        inv = [
            TlCon("communicating", [ConVal(off)]),
            TlCon("temperature",   [ConRealRange(RealRange(50.0, 100.0))]),
            TlCon("battery",       [ConRealRange(RealRange(20.0, 100.0))]),
        ],
        post = [
            TlCon("distance",      [ConRealRange(RealRange(10.0, 50.0))]),
        ],
        impacts = [
            Impact("driving",     "pre",   ImpactAssign(on)),
            Impact("driving",     "post",  ImpactAssign(off)),
            Impact("distance",    "maint", ImpactRate(-1.0)),
            Impact("temperature", "maint", ImpactRate(-0.2)),
            Impact("battery",     "maint", ImpactRate(-0.2)),
        ],
    )

    communicating = TaskDef(
        id       = "communicating",
        ident    = 3,
        priority = 1,
        startrng = IntRange(200, 220),
        endrng   = IntRange(280, 300),
        dur      = 80,
        start    = 210,
        after    = [],
        pre = [
            TlCon("driving", [ConVal(off)]),
            TlCon("radio",   [ConVal(BoolVal(False))]),
            TlCon("memory",  [ConRealRange(RealRange(40.0, 100.0))]),
            TlCon("battery", [ConRealRange(RealRange(50.0, 100.0))]),
        ],
        inv = [
            # TlCon("driving", [ConVal(off)]),
            TlCon("battery", [ConRealRange(RealRange(20.0, 100.0))]),
        ],
        post = [
            TlCon("memory", [ConRealRange(RealRange(0.0, 100.0))]),
        ],
        impacts = [
            Impact("communicating", "pre",   ImpactAssign(on)),
            Impact("communicating", "post",  ImpactAssign(off)),
            Impact("radio",         "pre",   ImpactAssign(BoolVal(True))),
            Impact("radio",         "post",  ImpactAssign(BoolVal(False))),
            Impact("memory",        "post",  ImpactCumulative(-100.0)),
            Impact("battery",       "maint", ImpactRate(-0.2)),
        ],
    )

    return TaskNet(
        id        = "HeatDriveCommunicate",
        timelines = timelines,
        tasks     = [heating, driving, communicating],
        endTime   = 300,
    )

# ============================================================
# 4. Run
# ============================================================

def main():
    tn = make_example_tasknet()
    enc = TaskNetSMT(tn)
    print("TaskNet SMT Example (zone-based, monolithic)")
    print("Solving TaskNet constraints...")
    model = enc.solve()
    print("Finished.\n")
    if model is not None:
        enc.pretty_print(model)

if __name__ == "__main__":
    print('\n\n\n\n\n\n\n*** NEW SCHEDULE***\n')
    main()
