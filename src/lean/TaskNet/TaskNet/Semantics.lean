
import Std
import TaskNet.Syntax

open Std

namespace TaskNet

-- =========
-- SEMANTICS
-- =========

-----------------------
-- Library functions --
-----------------------

def dom {α β} [BEq α] [Hashable α] (m : Std.HashMap α β) : Std.HashSet α :=
  m.fold (init := ∅) (fun s k _ => s.insert k)

abbrev Set (α : Type) := α → Prop

def hashSetDiff [BEq α] [Hashable α]
    (s₁ s₂ : HashSet α) : HashSet α :=
  s₁.fold (init := HashSet.emptyWithCapacity) fun acc a =>
    if s₂.contains a then acc else acc.insert a

----------------------------
-- Semantic base domains --
----------------------------

abbrev Interval := Float × Float
abbrev TimeInterval := Time × Time
abbrev Schedule    := Std.HashMap TaskName TimeInterval
abbrev State       := Std.HashMap TimeLineName Value
abbrev Trace       := List State
abbrev IntervalMap := Std.HashMap TimeLineName Interval
abbrev Change      := Option Value × Option Float
abbrev ChangeMap   := Std.HashMap TimeLineName Change

---------------
-- Functions --
---------------

def mergeChanges (c1 c2 : Change) : Change :=
  let (as1, d1) := c1
  let (as2, d2) := c2
  let asgn  := as2 <|> as1
  let delta := some ((d1.getD 0) + (d2.getD 0))
  (asgn, delta)

def inIntRange (r : IntRange) (t : Nat) : Prop :=
  r.low ≤ Int.ofNat t ∧ Int.ofNat t ≤ r.high

def valueToReal? : Value → Option Float
  | .intVal i  => some (Float.ofInt i)
  | .realVal r => some r
  | .strVal _  => none
  | .boolVal _ => none

def addValues (v : Value) (δ : Float) : Option Value :=
  match v with
  | .intVal i  => some (.realVal (Float.ofInt i + δ))
  | .realVal r => some (.realVal (r + δ))
  | .strVal _  => none
  | .boolVal _ => none

def clamp (x low high : Float) : Float :=
  if x < low then low else if x > high then high else x

-------------------------
--- Semantic Equations --
-------------------------

-- Names and ids

def ImpactId (imp : Impact) : TimeLineName :=
  imp.id

def TaskNameOf (tsk : TaskDef) : TaskName :=
  tsk.id

def TaskNamesOf (tsks : List TaskDef) : HashSet TaskName :=
  tsks.foldl (fun acc t => acc.insert (TaskNameOf t)) (HashSet.emptyWithCapacity)

-- ObligationsHold

def ConHolds (c : Con) (v : Value) : Prop :=
  match c with
  | Con.val v'      => v = v'
  | Con.i_rng r     =>
      match v with
      | .intVal i   => r.low ≤ i ∧ i ≤ r.high
      | _           => False
  | Con.r_rng r     =>
      match valueToReal? v with
      | some x      => r.low ≤ x ∧ x ≤ r.high
      | none        => False

def Cons (cons : List Con) (v : Value) : Prop :=
  match cons with
  | []       => False
  | c :: cs  => ConHolds c v ∨ Cons cs v

def TimeLineCondition (cond : TlCon) (state : State) : Prop :=
  match state.get? cond.id with
  | some v => Cons cond.cons v
  | none   => False   -- no value for this timeline ⇒ condition fails

def TimeLineConditions (conds : List TlCon) (state : State) : Prop :=
  match conds with
  | []        => True
  | c :: cs   => TimeLineCondition c state ∧ TimeLineConditions cs state

def PreInvPostOk (tsk : TaskDef) (sch : Schedule) (state : State) (k : Time) : Prop :=
  match sch.get? tsk.id with
  | none => False   -- task must be scheduled; StartEndTimesOk ensures this globally
  | some (st, en) =>
      ((k = st) → TimeLineConditions tsk.pre  state) ∧
      ((st ≤ k ∧ k ≤ en) → TimeLineConditions tsk.inv  state) ∧
      ((k = en) → TimeLineConditions tsk.post state)

def PresInvsPostsOk (tsks : List TaskDef) (sch : Schedule)(state : State) (k : Time) : Prop :=
  match tsks with
  | []       => True
  | t :: ts  => PreInvPostOk t sch state k ∧ PresInvsPostsOk ts sch state k

def TimeLineRangeOk (tl : Timeline) (state : State) : Prop :=
  match tl with
  | .stateTimeline _ _ _ => True
  | .atomicTimeline _    => True

  | .claimableTimeline id range _ =>
      match state.get? id with
      | some v =>
          match valueToReal? v with
          | some r => range.low ≤ r ∧ r ≤ range.high
          | none   => False
      | none => False

  | .cumulativeTimeline id range _ _ =>
      match state.get? id with
      | some v =>
          match valueToReal? v with
          | some r => range.low ≤ r ∧ r ≤ range.high
          | none   => False
      | none => False

  | .rateTimeline id range _ _ =>
      match state.get? id with
      | some v =>
          match valueToReal? v with
          | some r => range.low ≤ r ∧ r ≤ range.high
          | none   => False
      | none => False

def TimeLineRangesOk (tls : List Timeline) (state : State) : Prop :=
  match tls with
  | []       => True
  | tl :: ts => TimeLineRangeOk tl state ∧ TimeLineRangesOk ts state

def ObligationsHold (tn : TaskNet) (sch : Schedule) (σ : Trace) : Prop :=
  ∀ k : Nat, k < σ.length →
    TimeLineRangesOk tn.timelines (σ[k]!) ∧
    PresInvsPostsOk tn.tasks sch (σ[k]!) k

-- Impacts

def Bound (tl : Timeline) : IntervalMap :=
  match tl with
  | .stateTimeline _ _ _        => ({} : IntervalMap)
  | .atomicTimeline _           => ({} : IntervalMap)
  | .claimableTimeline _ _ _ => ({} : IntervalMap)
  | .cumulativeTimeline id _ bounds _ =>
      ({} : IntervalMap).insert id (bounds.low, bounds.high)
  | .rateTimeline id _ bounds _ =>
      ({} : IntervalMap).insert id (bounds.low, bounds.high)

def Bounds (tls : List Timeline) : IntervalMap :=
  match tls with
  | []        => ({} : IntervalMap)
  | tl :: ts  =>
      let rest := Bounds ts
      let b    := Bound tl
      b.fold (init := rest) (fun acc id iv => acc.insert id iv)

def ImpactChange (imp : Impact) (i : TimeInterval) (k : Time) : Change :=
  let (st, en) := i
  match imp.when, imp.how with
  -- assign
  | .pre,   .assign v => if k = st then (some v, none) else (none, none)
  | .maint, .assign _ => (none, none)   -- not well-formed per spec; handled by a WF check
  | .post,  .assign v => if k = en then (some v, none) else (none, none)
  -- cumulative
  | .pre,   .cumulative v => if k = st then (none, some v) else (none, none)
  | .maint, .cumulative v =>
      if k = st then (none, some v)
      else if k = en then (none, some (-v))
      else (none, none)
  | .post,  .cumulative v => if k = en then (none, some v) else (none, none)
  -- rate
  | .pre,   .rate r => if st ≤ k then (none, some r) else (none, none)
  | .maint, .rate r =>
      if st ≤ k then
        if k ≤ en then (none, some r) else (none, none)
      else (none, none)
  | .post,  .rate r => if en ≤ k then (none, some r) else (none, none)

def ComputeChangesByTaskImpacts(imps : List Impact) (i : TimeInterval) (k : Time) : ChangeMap :=
  match imps with
  | [] => (Std.HashMap.emptyWithCapacity : ChangeMap)
  | imp :: is =>
      let id     := ImpactId imp
      let change := ImpactChange imp i k
      let tail   := ComputeChangesByTaskImpacts is i k
      tail.insert id change

def ComputeChangesByTask (tsk : TaskDef) (sch : Schedule) (k : Time) : ChangeMap :=
  match sch.get? tsk.id with
  | some (st, en) => ComputeChangesByTaskImpacts tsk.impacts (st, en) k
  | none          => (Std.HashMap.emptyWithCapacity : ChangeMap)

def ComputeChanges (tsks : List TaskDef) (sch : Schedule) (k : Time) : ChangeMap :=
  match tsks with
  | []       => (Std.HashMap.emptyWithCapacity : ChangeMap)
  | t :: ts  =>
    let m1 := ComputeChangesByTask t sch k
    let m2 := ComputeChanges ts sch k
    m1.fold (init := m2) (fun acc id c1 =>
      match acc.get? id with
      | some c2 => acc.insert id (mergeChanges c1 c2)
      | none    => acc.insert id c1)

-- Initial state verification

def InitialTimeLine (tl : Timeline) (σ0 : State) : Prop :=
  match tl with
  | .stateTimeline id _ initial =>
      σ0.get? id = some (Value.strVal initial)
  | .atomicTimeline id =>
      σ0.get? id = some (Value.boolVal false)
  | .claimableTimeline id _ initial =>
      σ0.get? id = some (Value.realVal initial)
  | .cumulativeTimeline id _ _ initial =>
      σ0.get? id = some (Value.realVal initial)
  | .rateTimeline id _ _ initial =>
      σ0.get? id = some (Value.realVal initial)

def InitialTimeLines (tls : List Timeline) (σ0 : State) : Prop :=
  match tls with
  | []        => True
  | tl :: tls => InitialTimeLine tl σ0 ∧ InitialTimeLines tls σ0

-- StartEndTimesOk

def AssignmentsByTaskImpact (imp : Impact) (i : TimeInterval): List (TimeLineName × Time) :=
  let (st, en) := i
  match imp.when, imp.how with
  | .pre,  .assign _ => [(imp.id, st)]
  | .post, .assign _ => [(imp.id, en)]
  | .maint, .assign _ => []          -- “error” in spec; here: no assignment
  | _,     .cumulative _ => []
  | _,     .rate _       => []

def AssignmentsByTaskImpacts (imps : List Impact) (i : TimeInterval): List (TimeLineName × Time) :=
  match imps with
  | []        => []
  | imp :: is => AssignmentsByTaskImpact imp i ++ AssignmentsByTaskImpacts is i


def AssignmentsByTask (tsk : TaskDef) (sch : Schedule) : List (TimeLineName × Time) :=
  match sch.get? tsk.id with
  | some (st, en) => AssignmentsByTaskImpacts tsk.impacts (st, en)
  | none => []


def Assignments (tsks : List TaskDef) (sch : Schedule) : List (TimeLineName × Time) :=
  match tsks with
  | [] => []
  | t :: ts => AssignmentsByTask t sch ++ Assignments ts sch


def NoSimultaneousAssignments (tsks : List TaskDef) (sch : Schedule) : Prop :=
  let asgns := Assignments tsks sch
  ∀ i j,
    i < asgns.length →
    j < asgns.length →
    i ≠ j →
    let (x₁, t₁) := asgns[i]!
    let (x₂, t₂) := asgns[j]!
    x₁ = x₂ → t₁ ≠ t₂

def StartEndTimesOkTask(tsk : TaskDef) (sch : Schedule) (n : Time) : Prop :=
  match sch.get? tsk.id with
  | some (st, en) =>
      en ≤ n ∧
      inIntRange tsk.startrng st ∧
      inIntRange tsk.endrng   en ∧
      en - st = tsk.dur ∧
      tsk.after.all (fun bid =>
        match sch.get? bid with
        | some (_, ben) => ben ≤ st
        | none => false)
  | none => false

def StartEndTimesOkTasks (tsks : List TaskDef) (sch : Schedule) (n : Time) : Prop :=
  match tsks with
  | []       => True
  | t :: ts  => StartEndTimesOkTask t sch n ∧ StartEndTimesOkTasks ts sch n

def StartEndTimesOk (tn : TaskNet) (sch : Schedule) : Prop :=
  let ids := TaskNamesOf tn.tasks
  let domOk := dom sch = ids
  let noSimul := NoSimultaneousAssignments tn.tasks sch
  let timeOk := StartEndTimesOkTasks tn.tasks sch tn.endTime
  domOk ∧ noSimul ∧ timeOk

-- Execution

def ExecutionSteps (tsks : List TaskDef) (sch : Schedule)(σ : Trace) (k : Time) (bnds : IntervalMap) : Prop :=
  let changeMap := ComputeChanges tsks sch k
  let oldState  := σ[k]!
  let newState  := σ[k + 1]!
  let changed   := dom changeMap
  let unchanged := hashSetDiff (dom oldState) changed
  (∀ tl, tl ∈ unchanged.toList →
          newState.get? tl = oldState.get? tl)
  ∧
  (∀ tl, tl ∈ changed.toList →
    match changeMap.get? tl, oldState.get? tl, newState.get? tl with
    | some (asgn?, add?), some oldV, some newV =>
        -- start value: assignment overrides old
        let startV :=
          match asgn? with | some v => v | none => oldV
        -- result after optional additive delta
        let resultV :=
          match add? with
          | some δ =>
              match addValues startV δ with
              | some v => v
              | none   => startV
          | none => startV
        -- clamp if bounds exist; otherwise result must equal new
        match bnds.get? tl with
        | some (low, high) =>
            match valueToReal? resultV with
            | some r => newV = Value.realVal (clamp r low high)
            | none   => False
        | none => newV = resultV
    | _, _, _ => False)

def Execution (tn : TaskNet) (sch : Schedule) (σ : Trace) : Prop :=
  σ.length > 0 ∧
  InitialTimeLines tn.timelines (σ[0]!) ∧
  let bnds := Bounds tn.timelines
  ∀ k : Nat, k + 1 < σ.length →
    ExecutionSteps tn.tasks sch σ k bnds

-- Task networks

def TaskNetworkSem (tn : TaskNet) : Set Schedule :=
  fun sch =>
    StartEndTimesOk tn sch ∧
    ∀ σ : Trace, Execution tn sch σ → ObligationsHold tn sch σ

end TaskNet
