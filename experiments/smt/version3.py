# version3.py
#
# SMT encoding of:
#  - TaskNet abstract syntax (mirror of Lean)
#  - Schedule constraints (StartEndTimesOk + NoSimultaneousAssignments)
#  - Trace execution with impacts (Execute-like)
#  - Timeline ranges + pre/inv/post checked on the trace
#
# Solves for a schedule and trace that satisfy *all* of the above.

from __future__ import annotations
from dataclasses import dataclass
from typing import List, Optional, Dict, Union, Literal, Tuple, Any

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
    start: int  # original "intended" start; not used by solver
    after: List[str]  # names of tasks that must finish before this starts
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
# 2. SMT encoding: schedule + trace + obligations
# ============================================================

class TaskNetSMT:
    """
    Encodes one TaskNet instance into SMT:

      - start/end times for each task
      - initial state at time 0 for all timelines
      - transitions state[k] -> state[k+1] from impacts (with clamping)
      - range constraints for numeric timelines
      - pre/inv/post obligations on the trace

    Checks satisfiability and can print schedule + sample trace.
    """

    def __init__(self, tn: TaskNet):
        self.tn = tn
        self.solver = Solver()
        self.T = tn.endTime  # discrete time horizon, states 0..T

        # === 2.1 Schedule variables ===
        self.start_vars: Dict[str, Any] = {}
        self.end_vars: Dict[str, Any] = {}
        self._mk_schedule_vars()
        self._encode_start_end_times_ok()
        self._encode_no_simultaneous_assignments()

        # === 2.2 State variables per timeline ===
        # state timelines: id -> (states, str->idx, idx->str, [Int vars])
        self.state_tl: Dict[str, Tuple[List[str], Dict[str, int], Dict[int, str], List[Any]]] = {}
        # atomic timelines: id -> [Bool vars]
        self.atomic_tl: Dict[str, List[Any]] = {}
        # numeric timelines (claimable/cumulative/rate): id -> (range, bounds_opt, [Real vars])
        self.numeric_tl: Dict[str, Tuple[RealRange, Optional[RealRange], List[Any]]] = {}

        self._mk_state_vars()
        self._encode_initial_state()
        self._encode_transitions()
        self._encode_ranges()
        self._encode_pre_inv_post()

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
        for t in self.tn.tasks:
            s = self.start_vars[t.id]
            e = self.end_vars[t.id]

            # end <= n
            self.solver.add(e <= n)

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

    def _encode_no_simultaneous_assignments(self):
        """
        No two tasks may assign the same timeline at the same time.
        (Only for ImpactAssign; numeric impacts can overlap.)
        """
        tasks = self.tn.tasks
        assign_points: List[Tuple[TaskName, TimeLineName, Any]] = []

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
    # 2.2 State variables
    # ------------------------------

    def _mk_state_vars(self):
        T = self.T
        for tl in self.tn.timelines:
            if isinstance(tl, StateTimeline):
                states = tl.states
                s2i = {s: i for (i, s) in enumerate(states)}
                i2s = {i: s for (i, s) in enumerate(states)}
                vars_k = [Int(f"{tl.id}_{k}") for k in range(T + 1)]
                self.state_tl[tl.id] = (states, s2i, i2s, vars_k)
                # constrain domain of state (0 .. len(states)-1)
                for v in vars_k:
                    self.solver.add(v >= 0, v < len(states))

            elif isinstance(tl, AtomicTimeline):
                vars_k = [Bool(f"{tl.id}_{k}") for k in range(T + 1)]
                self.atomic_tl[tl.id] = vars_k

            elif isinstance(tl, ClaimableTimeline):
                vars_k = [Real(f"{tl.id}_{k}") for k in range(T + 1)]
                self.numeric_tl[tl.id] = (tl.range, None, vars_k)

            elif isinstance(tl, CumulativeTimeline):
                vars_k = [Real(f"{tl.id}_{k}") for k in range(T + 1)]
                self.numeric_tl[tl.id] = (tl.range, tl.bounds, vars_k)

            elif isinstance(tl, RateTimeline):
                vars_k = [Real(f"{tl.id}_{k}") for k in range(T + 1)]
                self.numeric_tl[tl.id] = (tl.range, tl.bounds, vars_k)

    def _encode_initial_state(self):
        # time 0
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
    # 2.3 Impact semantics (transitions)
    # ------------------------------

    def _numeric_delta_expr(self, tl_id: str, k: int):
        """
        Sum of all numeric deltas for numeric timelines (cumulative + rate),
        based on ImpactChange semantics.
        """
        terms = []
        for t in self.tn.tasks:
            s = self.start_vars[t.id]
            e = self.end_vars[t.id]
            for imp in t.impacts:
                if imp.id != tl_id:
                    continue
                how = imp.how
                when = imp.when

                if isinstance(how, ImpactCumulative):
                    v = how.v
                    if when == "pre":
                        terms.append(If(s == k, v, 0.0))
                    elif when == "maint":
                        terms.append(
                            If(s == k, v,
                               If(e == k, -v, 0.0))
                        )
                    elif when == "post":
                        terms.append(If(e == k, v, 0.0))

                elif isinstance(how, ImpactRate):
                    r = how.r
                    if when == "pre":
                        terms.append(If(s <= k, r, 0.0))
                    elif when == "maint":
                        terms.append(If(And(s <= k, k <= e), r, 0.0))
                    elif when == "post":
                        terms.append(If(e <= k, r, 0.0))

                # Assign to numeric timelines is ignored for now (not used in example)

        if not terms:
            return 0.0
        total = terms[0]
        for term in terms[1:]:
            total = total + term
        return total

    def _encode_transitions(self):
        T = self.T

        # State / atomic timelines: only assign impacts (no deltas)
        for tl in self.tn.timelines:
            if isinstance(tl, StateTimeline):
                _, s2i, _, vars_k = self.state_tl[tl.id]
                for k in range(T):
                    cur = vars_k[k]
                    expr = cur
                    # apply assigns if any
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
                                # ill-typed; forbid
                                self.solver.add(False)
                                continue
                            idx = s2i[v.v]
                            if imp.when == "pre":
                                expr = If(s == k, idx, expr)
                            elif imp.when == "post":
                                expr = If(e == k, idx, expr)
                            else:
                                # maint+assign forbidden
                                self.solver.add(False)
                    self.solver.add(vars_k[k + 1] == expr)

            elif isinstance(tl, AtomicTimeline):
                vars_k = self.atomic_tl[tl.id]
                for k in range(T):
                    cur = vars_k[k]
                    expr = cur
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
                                expr = If(s == k, v.v, expr)
                            elif imp.when == "post":
                                expr = If(e == k, v.v, expr)
                            else:
                                self.solver.add(False)
                    self.solver.add(vars_k[k + 1] == expr)

        # Numeric timelines: deltas + optional clamping (+ range in _encode_ranges)
        for tl in self.tn.timelines:
            if isinstance(tl, (ClaimableTimeline, CumulativeTimeline, RateTimeline)):
                range_r, bounds_opt, vars_k = self.numeric_tl[tl.id]

                if bounds_opt is not None:
                    low_bnd, high_bnd = bounds_opt.low, bounds_opt.high
                else:
                    low_bnd, high_bnd = None, None

                for k in range(T):
                    cur = vars_k[k]
                    delta = self._numeric_delta_expr(tl.id, k)
                    raw = cur + delta

                    if bounds_opt is not None:
                        clamped = If(raw < low_bnd, low_bnd,
                                     If(raw > high_bnd, high_bnd, raw))
                    else:
                        clamped = raw

                    self.solver.add(vars_k[k + 1] == clamped)

    def _encode_ranges(self):
        """
        TimeLineRangeOk: for numeric timelines, enforce that at all times
        the value lies within the declared RealRange.
        (State timelines' domains are already enforced in _mk_state_vars;
         atomic timelines are Booleans.)
        """
        for tl_id, (range_r, _bounds, vars_k) in self.numeric_tl.items():
            lo, hi = range_r.low, range_r.high
            for v in vars_k:
                self.solver.add(v >= lo, v <= hi)

    # ------------------------------
    # 2.4 pre / inv / post constraints
    # ------------------------------

    def _tl_value_at(self, tl_id: str, k: int):
        """
        Return a pair (kind, expr) describing the value of timeline tl_id at time k.
        kind in {"state", "atomic", "real"} with the appropriate Z3 expression.
        """
        if tl_id in self.state_tl:
            _, _, _, vars_k = self.state_tl[tl_id]
            return "state", vars_k[k]
        if tl_id in self.atomic_tl:
            vars_k = self.atomic_tl[tl_id]
            return "atomic", vars_k[k]
        if tl_id in self.numeric_tl:
            _, _, vars_k = self.numeric_tl[tl_id]
            return "real", vars_k[k]
        # Unknown timeline id: impossible in well-formed spec
        self.solver.add(False)
        # Dummy expression (never used if spec is well-formed)
        dummy = Real("dummy_unknown_timeline")
        return "real", dummy

    def _con_holds(self, tl_id: str, con: Con, k: int):
        """
        SMT formula for a single Con on timeline tl_id at time k.
        Cons is OR over such formulas.
        """
        kind, expr = self._tl_value_at(tl_id, k)

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
                if kind not in ("atomic",):
                    self.solver.add(False)
                    return False
                return expr == v.v

            if isinstance(v, IntVal):
                # For numeric timelines, treat as equality with integer
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

    def _tlcon_holds(self, tlc: TlCon, k: int):
        """
        SMT formula for one TlCon at time k:
          OR over its cons.
        """
        if not tlc.cons:
            # Empty list => False (Lean's Cons [] returns False)
            return False
        clauses = [self._con_holds(tlc.id, c, k) for c in tlc.cons]
        return Or(*clauses)

    def _conds_holds(self, conds: List[TlCon], k: int):
        """
        SMT formula for a list of TlCon at time k:
          AND over TlCon (each TlCon is an OR of Cons).
        Empty list => True.
        """
        if not conds:
            return True
        return And(*[self._tlcon_holds(c, k) for c in conds])

    def _encode_pre_inv_post(self):
        """
        For each task, for each time k in 0..T-1:
          - if k = start_t => pre holds on state[k]
          - if start_t <= k <= end_t => inv holds on state[k]
          - if k = end_t => post holds on state[k+1]
        """
        T = self.T
        for t in self.tn.tasks:
            s = self.start_vars[t.id]
            e = self.end_vars[t.id]

            for k in range(T):  # k from 0..T-1 (state[k+1] exists)
                pre_formula = self._conds_holds(t.pre, k)
                inv_formula = self._conds_holds(t.inv, k)
                post_formula = self._conds_holds(t.post, k + 1)

                # (k = s) -> pre
                self.solver.add(Or(s != k, pre_formula))

                # (s <= k <= e) -> inv
                self.solver.add(
                    Or(
                        k < s,
                        k > e,
                        inv_formula
                    )
                )

                # (k = e) -> post
                self.solver.add(Or(e != k, post_formula))

    # ------------------------------
    # 2.5 Solving + printing
    # ------------------------------

    def solve(self):
        # Optional: safety timeout so it never hangs indefinitely
        # self.solver.set(timeout=10000)
        if self.solver.check() != sat:
            print("TaskNet constraints (schedule + trace): UNSAT or UNKNOWN.")
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
        # Schedule
        sched = self.extract_schedule(model)
        print(f"Schedule for TaskNet `{self.tn.id}`:")
        for t in self.tn.tasks:
            s, e = sched[t.id]
            print(f"  {t.id:14s}: start = {s:4d}, end = {e:4d}")

        print("\nSample trace values at a few times:")
        for k in [0, 10, 90, 110, 190, 210, 290, self.tn.endTime]:
            if k > self.T:
                continue
            print(f"\n  t = {k}")
            for tl in self.tn.timelines:
                if isinstance(tl, StateTimeline):
                    _, _, i2s, vars_k = self.state_tl[tl.id]
                    idx = model[vars_k[k]].as_long()
                    print(f"    {tl.id:14s} = {i2s[idx]}")
                elif isinstance(tl, AtomicTimeline):
                    vars_k = self.atomic_tl[tl.id]
                    val = model[vars_k[k]]
                    print(f"    {tl.id:14s} = {val}")
                else:
                    _, _, vars_k = self.numeric_tl[tl.id]
                    val = model[vars_k[k]]
                    print(f"    {tl.id:14s} = {val.as_decimal(6)}")


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

    # Small helpers
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
    enc = TaskNetSMT(tn)
    print("Solving TaskNet constraints...")
    model = enc.solve()
    print("finished.\n")
    if model is not None:
        enc.pretty_print(model)


if __name__ == "__main__":
    print("TaskNet SMT Example (version 3)")
    main()
