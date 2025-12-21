# version5.py
#
# Zone-based SMT encoding of:
#  - TaskNet abstract syntax (mirror of Lean)
#  - A *fixed* schedule (using TaskDef.start and dur)
#  - Trace execution with impacts over zones
#  - Timeline ranges + pre/inv/post checked at zone boundaries
#
# This version does *not* search over schedules; it assumes the schedule
# encoded in the TaskNet (start + dur) and checks that the resulting
# execution trace satisfies all obligations.

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
    start: int  # fixed "intended" start (we use this)
    after: List[str]  # names of tasks that must finish before this starts (ignored in v5)
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
# 2. Zone-based SMT encoding (fixed schedule)
# ============================================================

class TaskNetSMTZones:
    """
    Zone-based encoding *for a fixed schedule*:

      - Zones are defined by 0, all task starts/ends, and endTime.
      - For each timeline we create a value at each zone boundary.
      - Numeric timelines are advanced by integrating constant rates over
        each zone, plus cumulative jumps at boundaries, with clamping.
      - State/atomic timelines are updated by assign-impacts at boundaries.
      - pre/inv/post are checked on boundary states.

    There are NO schedule variables; TaskDef.start and dur define the schedule.
    """

    def __init__(self, tn: TaskNet):
        self.tn = tn
        self.solver = Solver()

        # ---------------------------------------------------
        # 2.1 Fix schedule from TaskDef.start + dur
        # ---------------------------------------------------
        # For each task we compute concrete start/end times
        self.task_start: Dict[str, int] = {}
        self.task_end: Dict[str, int]   = {}

        for t in self.tn.tasks:
            s = t.start
            e = t.start + t.dur
            self.task_start[t.id] = s
            self.task_end[t.id]   = e

            # sanity: within declared ranges
            self.solver.add(s >= t.startrng.low, s <= t.startrng.high)
            self.solver.add(e >= t.endrng.low,   e <= t.endrng.high)

        # ---------------------------------------------------
        # 2.2 Build zone boundaries
        # ---------------------------------------------------
        bset = {0, self.tn.endTime}
        for t in self.tn.tasks:
            bset.add(self.task_start[t.id])
            bset.add(self.task_end[t.id])
        self.boundaries: List[int] = sorted(bset)
        self.numZones = len(self.boundaries) - 1

        # map time -> boundary index
        self.boundary_index: Dict[int, int] = {
            t: i for i, t in enumerate(self.boundaries)
        }

        # ---------------------------------------------------
        # 2.3 State variables at boundaries
        # ---------------------------------------------------
        # State timelines: id -> (states, str->idx, idx->str, [Int vars per boundary])
        self.state_tl: Dict[str, Tuple[List[str], Dict[str, int], Dict[int, str], List]] = {}
        # Atomic timelines: id -> [Bool vars per boundary]
        self.atomic_tl: Dict[str, List] = {}
        # Numeric timelines: id -> (range, bounds_opt, [Real vars per boundary])
        self.numeric_tl: Dict[str, Tuple[RealRange, Optional[RealRange], List]] = {}

        self._mk_state_vars()
        self._encode_initial_state()
        self._encode_transitions()
        self._encode_ranges()
        self._encode_pre_inv_post()

    # ------------------------------
    # 2.3.1 Create per-boundary vars
    # ------------------------------

    def _mk_state_vars(self):
        B = len(self.boundaries)
        for tl in self.tn.timelines:
            if isinstance(tl, StateTimeline):
                states = tl.states
                s2i = {s: i for (i, s) in enumerate(states)}
                i2s = {i: s for (i, s) in enumerate(states)}
                vars_k = [Int(f"{tl.id}_b{i}") for i in range(B)]
                self.state_tl[tl.id] = (states, s2i, i2s, vars_k)
                # constrain domain (0 .. len(states)-1)
                for v in vars_k:
                    self.solver.add(v >= 0, v < len(states))

            elif isinstance(tl, AtomicTimeline):
                vars_k = [Bool(f"{tl.id}_b{i}") for i in range(B)]
                self.atomic_tl[tl.id] = vars_k

            elif isinstance(tl, ClaimableTimeline):
                vars_k = [Real(f"{tl.id}_b{i}") for i in range(B)]
                self.numeric_tl[tl.id] = (tl.range, None, vars_k)

            elif isinstance(tl, CumulativeTimeline):
                vars_k = [Real(f"{tl.id}_b{i}") for i in range(B)]
                self.numeric_tl[tl.id] = (tl.range, tl.bounds, vars_k)

            elif isinstance(tl, RateTimeline):
                vars_k = [Real(f"{tl.id}_b{i}") for i in range(B)]
                self.numeric_tl[tl.id] = (tl.range, tl.bounds, vars_k)

    # ------------------------------
    # 2.3.2 Initial state (boundary 0)
    # ------------------------------

    def _encode_initial_state(self):
        # boundary 0 corresponds to time 0
        for tl in self.tn.timelines:
            if isinstance(tl, StateTimeline):
                _, s2i, _, vars_k = self.state_tl[tl.id]
                self.solver.add(vars_k[0] == s2i[tl.initial])

            elif isinstance(tl, AtomicTimeline):
                vars_k = self.atomic_tl[tl.id]
                self.solver.add(vars_k[0] == False)

            elif isinstance(tl, ClaimableTimeline):
                _, _, vars_k = self.numeric_tl[tl.id]
                self.solver.add(vars_k[0] == tl.initial)

            elif isinstance(tl, CumulativeTimeline):
                _, _, vars_k = self.numeric_tl[tl.id]
                self.solver.add(vars_k[0] == tl.initial)

            elif isinstance(tl, RateTimeline):
                _, _, vars_k = self.numeric_tl[tl.id]
                self.solver.add(vars_k[0] == tl.initial)

    # ------------------------------
    # 2.3.3 Helper: active tasks in a zone
    # ------------------------------

    def _tasks_active_in_zone(self, z: int) -> List[TaskDef]:
        """
        Returns tasks active throughout zone z = [τ_z, τ_{z+1}).
        """
        t0 = self.boundaries[z]
        t1 = self.boundaries[z + 1]
        active = []
        for t in self.tn.tasks:
            s = self.task_start[t.id]
            e = self.task_end[t.id]
            # active throughout the whole interval
            if s <= t0 and e >= t1:
                active.append(t)
        return active

    # ------------------------------
    # 2.3.4 Impact semantics (transitions)
    # ------------------------------

    def _encode_transitions(self):
        B = len(self.boundaries)

        # === State / atomic timelines: assignments at boundaries ===
        for tl in self.tn.timelines:
            if isinstance(tl, StateTimeline):
                _, s2i, _, vars_k = self.state_tl[tl.id]
                for bi in range(1, B):
                    # start from previous boundary value
                    expr = vars_k[bi - 1]
                    time = self.boundaries[bi]

                    # apply any assign-impacts that fire at this boundary
                    for t in self.tn.tasks:
                        s = self.task_start[t.id]
                        e = self.task_end[t.id]
                        for imp in t.impacts:
                            if imp.id != tl.id:
                                continue
                            if not isinstance(imp.how, ImpactAssign):
                                continue
                            v = imp.how.v
                            if not isinstance(v, StrVal):
                                # ill-typed
                                self.solver.add(False)
                                continue
                            idx = s2i[v.v]
                            if imp.when == "pre" and time == s:
                                expr = idx
                            elif imp.when == "post" and time == e:
                                expr = idx
                            elif imp.when == "maint":
                                # maint+assign disallowed in our spec
                                self.solver.add(False)
                    self.solver.add(vars_k[bi] == expr)

            elif isinstance(tl, AtomicTimeline):
                vars_k = self.atomic_tl[tl.id]
                for bi in range(1, B):
                    expr = vars_k[bi - 1]
                    time = self.boundaries[bi]
                    for t in self.tn.tasks:
                        s = self.task_start[t.id]
                        e = self.task_end[t.id]
                        for imp in t.impacts:
                            if imp.id != tl.id:
                                continue
                            if not isinstance(imp.how, ImpactAssign):
                                continue
                            v = imp.how.v
                            if not isinstance(v, BoolVal):
                                self.solver.add(False)
                                continue
                            if imp.when == "pre" and time == s:
                                expr = v.v
                            elif imp.when == "post" and time == e:
                                expr = v.v
                            elif imp.when == "maint":
                                self.solver.add(False)
                    self.solver.add(vars_k[bi] == expr)

        # === Numeric timelines: integrate rates over zones + cumulative jumps ===
        for tl in self.tn.timelines:
            if not isinstance(tl, (ClaimableTimeline, CumulativeTimeline, RateTimeline)):
                continue

            range_r, bounds_opt, vars_k = self.numeric_tl[tl.id]
            lo_rng, hi_rng = range_r.low, range_r.high

            # precompute bounds for clamping (if any)
            if bounds_opt is not None:
                lo_bnd, hi_bnd = bounds_opt.low, bounds_opt.high
            else:
                lo_bnd, hi_bnd = None, None

            # For each zone [τ_z, τ_{z+1}), accumulate rate; apply cumulative at τ_{z+1}
            for z in range(self.numZones):
                t0 = self.boundaries[z]
                t1 = self.boundaries[z + 1]
                dt = float(t1 - t0)

                cur = vars_k[z]

                # sum of rates for tasks active in this zone
                rate_terms = []
                active = self._tasks_active_in_zone(z)
                for t in active:
                    s = self.task_start[t.id]
                    e = self.task_end[t.id]
                    for imp in t.impacts:
                        if imp.id != tl.id:
                            continue
                        if isinstance(imp.how, ImpactRate) and imp.when == "maint":
                            r = imp.how.r
                            # active throughout zone by construction of `active`
                            rate_terms.append(r * dt)
                        elif isinstance(imp.how, ImpactRate):
                            # pre/post rates not handled in this v5 (not in example)
                            self.solver.add(False)

                raw = cur
                for term in rate_terms:
                    raw = raw + term

                # apply cumulative jumps at the *next* boundary t1
                jump = 0.0
                for t in self.tn.tasks:
                    s = self.task_start[t.id]
                    e = self.task_end[t.id]
                    for imp in t.impacts:
                        if imp.id != tl.id:
                            continue
                        if isinstance(imp.how, ImpactCumulative):
                            v = imp.how.v
                            if imp.when == "pre" and t1 == s:
                                jump = jump + v
                            elif imp.when == "post" and t1 == e:
                                jump = jump + v
                            elif imp.when == "maint":
                                # maint+cumulative not used in your example; forbid for now
                                self.solver.add(False)

                raw2 = raw + jump

                # clamp according to bounds (if any)
                if bounds_opt is not None:
                    clamped = If(raw2 < lo_bnd, lo_bnd,
                                 If(raw2 > hi_bnd, hi_bnd, raw2))
                else:
                    clamped = raw2

                self.solver.add(vars_k[z + 1] == clamped)

            # enforce main range (TimeLineRangeOk)
            for bi in range(B):
                self.solver.add(vars_k[bi] >= lo_rng, vars_k[bi] <= hi_rng)

    # ------------------------------
    # 2.3.5 Ranges already done for numeric timelines
    # ------------------------------

    def _encode_ranges(self):
        """
        For numeric timelines, we've enforced ranges in _encode_transitions.
        For state/atomic timelines, domains were enforced in _mk_state_vars.
        Nothing extra needed here in v5, but we keep the hook.
        """
        return

    # ------------------------------
    # 2.4 pre / inv / post constraints (at boundaries)
    # ------------------------------

    def _tl_value_at_boundary(self, tl_id: str, bi: int):
        """
        Return a pair (kind, expr) describing the value of timeline tl_id
        at boundary index bi.
        kind in {"state", "atomic", "real"}.
        """
        if tl_id in self.state_tl:
            _, _, _, vars_k = self.state_tl[tl_id]
            return "state", vars_k[bi]
        if tl_id in self.atomic_tl:
            vars_k = self.atomic_tl[tl_id]
            return "atomic", vars_k[bi]
        if tl_id in self.numeric_tl:
            _, _, vars_k = self.numeric_tl[tl_id]
            return "real", vars_k[bi]

        # Unknown timeline id: impossible in well-formed spec
        self.solver.add(False)
        dummy = Real("dummy_unknown_timeline")
        return "real", dummy

    def _con_holds(self, tl_id: str, con: Con, bi: int):
        """
        SMT formula for a single Con on timeline tl_id at boundary bi.
        """
        kind, expr = self._tl_value_at_boundary(tl_id, bi)

        if isinstance(con, ConVal):
            v = con.v
            if isinstance(v, StrVal):
                if kind != "state":
                    self.solver.add(False)
                    return False
                _, s2i, _, _ = self.state_tl[tl_id]
                idx = s2i[v.v]
                return expr == idx

            if isinstance(v, BoolVal):
                if kind != "atomic":
                    self.solver.add(False)
                    return False
                return expr == v.v

            if isinstance(v, IntVal):
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

        self.solver.add(False)
        return False

    def _tlcon_holds(self, tlc: TlCon, bi: int):
        """
        SMT formula for one TlCon at boundary bi:
          OR over its cons.
        """
        if not tlc.cons:
            return False
        clauses = [self._con_holds(tlc.id, c, bi) for c in tlc.cons]
        return Or(*clauses)

    def _conds_holds(self, conds: List[TlCon], bi: int):
        """
        SMT formula for a list of TlCon at boundary bi:
          AND over TlCon (each TlCon is an OR of Cons).
        Empty list => True.
        """
        if not conds:
            return True
        return And(*[self._tlcon_holds(c, bi) for c in conds])

    def _encode_pre_inv_post(self):
        """
        For each task t with fixed start/end times:

          - pre must hold at the boundary for t.start
          - inv must hold at all boundaries between start and end
          - post must hold at the boundary for t.end

        Note: This is a boundary-based approximation of the original
        step-by-step semantics, but matches your intuitive "check only
        at key times" idea for the zone model.
        """
        for t in self.tn.tasks:
            s = self.task_start[t.id]
            e = self.task_end[t.id]
            if s not in self.boundary_index or e not in self.boundary_index:
                # ill-formed schedule vs boundaries
                self.solver.add(False)
                continue

            bi_s = self.boundary_index[s]
            bi_e = self.boundary_index[e]

            # pre at start
            self.solver.add(self._conds_holds(t.pre, bi_s))

            # inv on all boundaries in [s, e]
            for bi in range(bi_s, bi_e + 1):
                self.solver.add(self._conds_holds(t.inv, bi))

            # post at end
            self.solver.add(self._conds_holds(t.post, bi_e))

    # ------------------------------
    # 2.5 Solving + printing
    # ------------------------------

    def solve(self):
        if self.solver.check() != sat:
            print("TaskNet (fixed schedule + trace + obligations): UNSAT.")
            return None
        return self.solver.model()

    def pretty_print(self, model):
        print(f"Zone boundaries for TaskNet `{self.tn.id}`:")
        for i, t in enumerate(self.boundaries):
            print(f"  b{i}: t = {t}")
        print()

        print("Tasks (fixed schedule):")
        for t in self.tn.tasks:
            s = self.task_start[t.id]
            e = self.task_end[t.id]
            print(f"  {t.id:14s}: start = {s:4d}, end = {e:4d}")
        print()

        # Print values at a subset of boundaries (all of them here)
        print("Trace at zone boundaries:")
        for bi, t in enumerate(self.boundaries):
            print(f"\n  boundary b{bi}, t = {t}")
            for tl in self.tn.timelines:
                if isinstance(tl, StateTimeline):
                    _, _, i2s, vars_k = self.state_tl[tl.id]
                    idx = model[vars_k[bi]].as_long()
                    print(f"    {tl.id:14s} = {i2s[idx]}")
                elif isinstance(tl, AtomicTimeline):
                    vars_k = self.atomic_tl[tl.id]
                    val = model[vars_k[bi]]
                    print(f"    {tl.id:14s} = {val}")
                else:
                    _, _, vars_k = self.numeric_tl[tl.id]
                    val = model[vars_k[bi]]
                    # val.as_decimal may return a string
                    try:
                        s = val.as_decimal(6)
                    except Exception:
                        s = str(val)
                    print(f"    {tl.id:14s} = {s}")


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
        CumulativeTimeline("distance", RealRange(0.0, 100.0), RealRange(0.0, 100.0), 100.0),
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
        start    = 10,       # fixed in v5
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
        start    = 110,      # fixed in v5
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
        start    = 210,      # fixed in v5
        after    = [],
        pre = [
            TlCon("driving", [ConVal(off)]),
            TlCon("radio",   [ConVal(BoolVal(False))]),
            TlCon("memory",  [ConRealRange(RealRange(40.0, 100.0))]),
            TlCon("battery", [ConRealRange(RealRange(50.0, 100.0))]),
        ],
        inv = [
            # TlCon("driving", [ConVal(off)]),  -- commented out in Lean spec as well
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
    enc = TaskNetSMTZones(tn)
    print("TaskNet SMT (zone-based, version 5)")
    print("Solving TaskNet constraints...\n")
    model = enc.solve()
    print()
    if model is not None:
        enc.pretty_print(model)


if __name__ == "__main__":
    main()
