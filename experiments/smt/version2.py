# tasknet_smt.py

from __future__ import annotations
from dataclasses import dataclass
from typing import List, Optional, Dict, Union, Literal
from z3 import (
    Solver, Int, And, Or, Not, sat, IntVal
)
import z3

# =============
# 1. Python AST 
# =============

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
    start: int  # original field in Lean; not used in synthesis here
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
# 2. SMT encoding of schedules (StartEndTimesOk + NoSimultaneousAssignments)
# ============================================================

@dataclass
class ScheduleSMT:
    tn: TaskNet

    def __post_init__(self):
        self.solver = Solver()
        self.start_vars: Dict[str, "z3.IntNumRef"] = {}
        self.end_vars: Dict[str, "z3.IntNumRef"] = {}
        self._mk_vars()
        self._encode_start_end_times_ok()
        self._encode_no_simultaneous_assignments()

    def _mk_vars(self):
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

            self.solver.add(e <= n)

            self.solver.add(s >= t.startrng.low, s <= t.startrng.high)
            self.solver.add(e >= t.endrng.low,   e <= t.endrng.high)

            self.solver.add(e - s == t.dur)

            for bid in t.after:
                if bid not in self.end_vars:
                    self.solver.add(False)
                else:
                    self.solver.add(self.end_vars[bid] <= s)

    def _encode_no_simultaneous_assignments(self):
        tasks = self.tn.tasks
        n = len(tasks)

        assign_points: List[tuple[TaskName, TimeLineName, "z3.ArithRef"]] = []

        for t in tasks:
            s = self.start_vars[t.id]
            e = self.end_vars[t.id]
            for imp in t.impacts:
                if isinstance(imp.how, ImpactAssign):
                    if imp.when == "pre":
                        assign_points.append((t.id, imp.id, s))
                    elif imp.when == "post":
                        assign_points.append((t.id, imp.id, e))
                    else:
                        self.solver.add(False)

        m = len(assign_points)
        for i in range(m):
            ti, id_i, time_i = assign_points[i]
            for j in range(i + 1, m):
                tj, id_j, time_j = assign_points[j]
                if id_i == id_j:
                    # if they assign to same timeline, times must be different
                    self.solver.add(time_i != time_j)
    
    def solve(self):
        if self.solver.check() != sat:
            print("Schedule constraints: UNSAT (no schedule exists).")
            return None
        model = self.solver.model()
        schedule: Dict[str, tuple[int, int]] = {}
        for t in self.tn.tasks:
            s_val = model[self.start_vars[t.id]]
            e_val = model[self.end_vars[t.id]]
            schedule[t.id] = (int(s_val.as_long()), int(e_val.as_long()))
        return schedule

    def pretty_print(self, schedule: Dict[str, tuple[int, int]]):
        print(f"Schedule for TaskNet `{self.tn.id}`:")
        for t in self.tn.tasks:
            s, e = schedule[t.id]
            print(f"  {t.id:14s}: start = {s:4d}, end = {e:4d}")


# ==============================
# Heat/Drive/Communicate Example
# ==============================

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

    # Small helpers for Value
    off = StrVal("off")
    on  = StrVal("on")

    heating = TaskDef(
        id       = "heating",
        ident    = 1,
        priority = 1,
        startrng = IntRange(0, 20),
        endrng   = IntRange(80, 100),
        dur      = 80,
        start    = 10,   # not used by solver; just copied
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
            TlCon("temperature",   [ConRealRange(RealRange(20.0, 100.0))])
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
            # TlCon("driving", [ConVal(off)]),  -- commented out like in Lean
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

def main():
    tn = make_example_tasknet()
    enc = ScheduleSMT(tn)
    schedule = enc.solve()
    if schedule is not None:
        enc.pretty_print(schedule)


if __name__ == "__main__":
    main()
