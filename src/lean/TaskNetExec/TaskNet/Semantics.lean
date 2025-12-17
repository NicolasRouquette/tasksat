
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

abbrev Set (α : Type) := α → Bool

def hashSetEq [BEq α] [Hashable α] (s₁ s₂ : HashSet α) : Bool :=
  s₁.toList.all (fun x => s₂.contains x) &&
  s₂.toList.all (fun x => s₁.contains x)

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

-------------------------
-- Auxiliary Functions --
-------------------------

def mergeChanges (c1 c2 : Change) : Change :=
  let (as1, d1) := c1
  let (as2, d2) := c2
  let asgn  := as2 <|> as1
  let delta := some ((d1.getD 0) + (d2.getD 0))
  (asgn, delta)

def inIntRange (r : IntRange) (t : Nat) : Bool :=
  let ti := Int.ofNat t
  r.low ≤ ti ∧ ti ≤ r.high

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

def ConHolds (c : Con) (v : Value) : Bool :=
  match c with
  | Con.val v'      => v == v'
  | Con.i_rng r     =>
      match v with
      | .intVal i   => r.low ≤ i ∧ i ≤ r.high
      | _           => False
  | Con.r_rng r     =>
      match valueToReal? v with
      | some x      => r.low ≤ x ∧ x ≤ r.high
      | none        => False

def Cons (cons : List Con) (v : Value) : Bool :=
  match cons with
  | []       => False
  | c :: cs  => ConHolds c v ∨ Cons cs v

def TimeLineCondition (cond : TlCon) (state : State) : Bool :=
  match state.get? cond.id with
  | some v => Cons cond.cons v
  | none   => False   -- no value for this timeline ⇒ condition fails

def TimeLineConditions (conds : List TlCon) (state : State) : Bool :=
  match conds with
  | []        => True
  | c :: cs   => TimeLineCondition c state ∧ TimeLineConditions cs state

def TimeLineRangeOk (tl : Timeline) (state : State) : Bool :=
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

def TimeLineRangesOk (tls : List Timeline) (state : State) : Bool :=
  match tls with
  | []       => True
  | tl :: ts => TimeLineRangeOk tl state ∧ TimeLineRangesOk ts state

def PreInvPostAt (tsk : TaskDef) (sch : Schedule)
  (cur next : State) (k : Time) : Bool :=
  match sch.get? tsk.id with
  | none => false
  | some (st, en) =>
      let preOk  := if k = st                 then TimeLineConditions tsk.pre  cur  else true
      let invOk  := if st ≤ k ∧ k ≤ en        then TimeLineConditions tsk.inv  cur  else true
      let postOk := if k = en                 then TimeLineConditions tsk.post next else true
      preOk && invOk && postOk

def ObligationsHold (tn : TaskNet) (sch : Schedule) (σ : Trace) : Bool :=
  let len := σ.length
  let rec loop (k : Nat) : Bool :=
    if k < len then
      let cur  := σ[k]!
      let next := if k + 1 < len then σ[k+1]! else cur
      let ok1  := TimeLineRangesOk tn.timelines cur
      let ok2  :=
        match tn.tasks with
        | []       => true
        | _        => tn.tasks.all (fun t => PreInvPostAt t sch cur next k)
      if ok1 && ok2 then loop (k+1) else false
    else true
  loop 0

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

def ComputeChangesByTaskImpacts (imps : List Impact) (i : TimeInterval) (k : Time) : ChangeMap :=
  match imps with
  | [] => (Std.HashMap.emptyWithCapacity : ChangeMap)
  | imp :: is =>
      let id     := ImpactId imp
      let change := ImpactChange imp i k
      let tail   := ComputeChangesByTaskImpacts is i k
      -- small fix: skip no-ops and merge when key already present
      match change with
      | (none, none) => tail
      | _ => tail.insert id change

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

 def NoSimultaneousAssignments (tsks : List TaskDef) (sch : Schedule) : Bool :=
  let asgns := Assignments tsks sch
  let n := asgns.length
  (List.range n).all (fun i =>
    (List.range n).all (fun j =>
      if i == j then true
      else
        let (x₁, t₁) := asgns[i]!
        let (x₂, t₂) := asgns[j]!
        if x₁ == x₂ then t₁ ≠ t₂ else true))

def StartEndTimesOkTask(tsk : TaskDef) (sch : Schedule) (n : Time) : Bool :=
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

def StartEndTimesOkTasks (tsks : List TaskDef) (sch : Schedule) (n : Time) : Bool :=
  match tsks with
  | []       => True
  | t :: ts  => StartEndTimesOkTask t sch n ∧ StartEndTimesOkTasks ts sch n

def StartEndTimesOk (tn : TaskNet) (sch : Schedule) : Bool :=
  let ids    := TaskNamesOf tn.tasks
  let domOk  := hashSetEq (dom sch) ids
  let noSim  := NoSimultaneousAssignments tn.tasks sch
  let timeOk := StartEndTimesOkTasks tn.tasks sch tn.endTime
  domOk && noSim && timeOk

-- Task networks

/-- Build the deterministic initial state from timelines. -/
def initialState (tls : List Timeline) : State :=
  tls.foldl
    (fun st tl =>
      match tl with
      | .stateTimeline id _ initial => st.insert id (Value.strVal initial)
      | .atomicTimeline id          => st.insert id (Value.boolVal false)
      | .claimableTimeline id _ i   => st.insert id (Value.realVal i)
      | .cumulativeTimeline id _ _ i=> st.insert id (Value.realVal i)
      | .rateTimeline id _ _ i      => st.insert id (Value.realVal i))
    (Std.HashMap.emptyWithCapacity)

/-- Apply one tick of changes with clamping. -/
def applyChanges (oldState : State) (changeMap : ChangeMap) (bnds : IntervalMap) : State :=
  changeMap.fold (init := oldState) (fun acc tl change =>
    let (asgn?, add?) := change
    let startV :=
      match asgn? with
      | some v => v
      | none   => acc.getD tl (Value.strVal "<undef>")
    let resultV :=
      match add? with
      | some δ =>
          match addValues startV δ with
          | some v => v
          | none   => startV
      | none => startV
    let finalV :=
      match bnds.get? tl with
      | some (low, high) =>
          match valueToReal? resultV with
          | some r => Value.realVal (clamp r low high)
          | none   => resultV
      | none => resultV
    acc.insert tl finalV)

/-- Execute the schedule to produce the unique trace (length = endTime + 1). -/
def Execute (tn : TaskNet) (sch : Schedule) : Trace :=
  let bnds := Bounds tn.timelines
  let σ0   := initialState tn.timelines
  let rec go (r : Nat) (k : Nat) (cur : State) (acc : List State) : List State :=
    match r with
    | 0      => (cur :: acc).reverse
    | r'+1   =>
        let cm  := ComputeChanges tn.tasks sch k
        let nxt := applyChanges cur cm bnds
        go r' (k+1) nxt (cur :: acc)
  go tn.endTime 0 σ0 []

def Admissible (tn : TaskNet) (sch : Schedule) : Bool :=
  let σ := Execute tn sch
  StartEndTimesOk tn sch && ObligationsHold tn sch σ

end TaskNet
