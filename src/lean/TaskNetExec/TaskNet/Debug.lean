import TaskNet.Syntax
import TaskNet.Semantics

namespace TaskNet
namespace Debug

open Std

namespace Ansi
  /- Toggle this. When `false`, colors/bold are no-ops. -/
  def useAnsi : Bool := false

  def esc     : String := "\u001b["
  def reset   : String := esc ++ "0m"

  private def wrap (code : String) (s : String) : String :=
    if useAnsi then esc ++ code ++ "m" ++ s ++ reset else s

  def red   (s : String) := wrap "31" s
  def green (s : String) := wrap "32" s
  def yellow(s : String) := wrap "33" s
  def blue  (s : String) := wrap "34" s
  def gray  (s : String) := wrap "90" s
  def bold  (s : String) := wrap "1"  s

  def okBadge (b : Bool) : String :=
    if b then green "✓" else red "✗"

  def okWord (b : Bool) : String :=
    if b then green "true" else red "false"
end Ansi

/-- Pretty-print a `Value`. -/
def showVal : Value → String
  | .intVal i  => s!"{i}"
  | .realVal r => s!"{r}"
  | .strVal s  => s!"\"{s}\""
  | .boolVal b => s!"{b}"

/-- Lookup and pretty-print the value of a timeline in a state. -/
def showAt (σ : State) (id : TimeLineName) : String :=
  match σ.get? id with
  | some v => showVal v
  | none   => "<none>"

/-- First failing reason across range & PRE/INV/POST; `none` if all good. -/
def checkTaskAt
  (t : TaskDef) (sch : Schedule) (cur next : State) (k : Time)
  : Option String :=
  match sch.get? t.id with
  | none => some s!"task {t.id} is missing from schedule"
  | some (st,en) =>
    let preBad  := (k = st) && !TimeLineConditions t.pre  cur
    let invBad  := (st ≤ k ∧ k ≤ en) && !TimeLineConditions t.inv  cur
    let postBad := (k = en) && !TimeLineConditions t.post next
    if preBad      then some s!"{t.id}: PRE fails at k={k}"
    else if invBad then some s!"{t.id}: INV fails at k={k}"
    else if postBad then some s!"{t.id}: POST fails at k={k}"
    else none

/-- First failing reason (range or any task) scanning the trace. -/
def firstFailure (tn : TaskNet) (sch : Schedule) (σ : Trace) : Option String :=
  let len := σ.length
  let rec loop (k : Nat) : Option String :=
    if k < len then
      let cur  := σ[k]!
      let next := if k + 1 < len then σ[k + 1]! else cur
      let ok1  := TimeLineRangesOk tn.timelines cur
      if !ok1 then
        some (
          "RANGE fails at k=" ++ toString k ++ " | "
          ++ "mem="  ++ showAt cur "memory"      ++ " "
          ++ "dist=" ++ showAt cur "distance"    ++ " "
          ++ "temp=" ++ showAt cur "temperature" ++ " "
          ++ "batt=" ++ showAt cur "battery"
        )
      else
        match tn.tasks.findSome? (fun t => checkTaskAt t sch cur next k) with
        | some msg => some msg
        | none     => loop (k + 1)
    else
      none
  loop 0

/-- Insert `x` into an ascending list without duplicates. -/
def insertSortedUnique (x : Nat) : List Nat → List Nat
  | []        => [x]
  | y :: ys   =>
    if x < y then x :: y :: ys
    else if x = y then y :: ys
    else y :: insertSortedUnique x ys

/-- Sort ascending + dedup. -/
def sortUnique (xs : List Nat) : List Nat :=
  xs.foldl (fun acc x => insertSortedUnique x acc) []

/-- Collect all start/end times from a schedule, **sorted** ascending, deduped. -/
def boundaryTimes (sch : Schedule) : List Nat :=
  let pairs := sch.fold (init := ([] : List (Nat × Nat)))
                (fun acc _ (st,en) => (st,en) :: acc)
  let flat  := pairs.foldl (fun acc (st,en) => acc ++ [st, en]) []
  sortUnique flat

/-- Single-line verdict with first failure if any. -/
def verdict (tn : TaskNet) (sch : Schedule) : String :=
  let σ   := Execute tn sch
  let okS := StartEndTimesOk tn sch
  let okO := ObligationsHold tn sch σ
  match firstFailure tn sch σ with
  | some msg => s!"StartEndTimesOk={okS} ObligationsHold={okO}\nFirst failure: {msg}"
  | none     => s!"StartEndTimesOk={okS} ObligationsHold={okO}\n(no failures)"

/-- Collect all timeline ids, in a stable sorted order. -/
def timelineIds (tls : List Timeline) : List TimeLineName :=
  let rec go : List Timeline → List TimeLineName
    | [] => []
    | (tl : Timeline) :: xs =>
      match tl with
      | .stateTimeline id _ _        => id :: go xs
      | .atomicTimeline id           => id :: go xs
      | .claimableTimeline id _ _    => id :: go xs
      | .cumulativeTimeline id _ _ _ => id :: go xs
      | .rateTimeline id _ _ _       => id :: go xs
  (go tls).mergeSort (· ≤ ·)

/-- Which tasks start at k. -/
def taskStartsAt (tsks : List TaskDef) (sch : Schedule) (k : Nat) : List TaskName :=
  (tsks.filterMap fun t =>
    match sch.get? t.id with
    | some (st, _) => if st = k then some t.id else none
    | none         => none)

/-- Which tasks end at k. -/
def taskEndsAt (tsks : List TaskDef) (sch : Schedule) (k : Nat) : List TaskName :=
  (tsks.filterMap fun t =>
    match sch.get? t.id with
    | some (_, en) => if en = k then some t.id else none
    | none         => none)

/-- Which tasks are active (for INV) at k (inclusive interval). -/
def tasksActiveAt (tsks : List TaskDef) (sch : Schedule) (k : Nat) : List TaskName :=
  (tsks.filterMap fun t =>
    match sch.get? t.id with
    | some (st,en) => if st ≤ k ∧ k ≤ en then some t.id else none
    | none         => none)

/-- Pretty print the whole state for all timelines on one line. -/
def showStateLine (tn : TaskNet) (σ : State) : String :=
  let ids := timelineIds tn.timelines
  let parts := ids.map (fun id => s!"{id}={showAt σ id}")
  String.intercalate ", " parts

/-- Changes at time k, sorted by timeline id. -/
def dumpChangesSorted (tn : TaskNet) (sch : Schedule) (k : Nat) : String :=
  let cm  := ComputeChanges tn.tasks sch k
  let ids := (dom cm).toList.mergeSort (· ≤ ·)
  let items :=
    ids.map (fun id =>
      match cm.get? id with
      | some (some v, _)    => s!"{id}: assign {showVal v}"
      | some (none, some r) => s!"{id}: delta {r}"
      | some (none, none)   => s!"{id}: no-change"
      | none                => s!"{id}: <missing!?>")
  String.intercalate "\n" items

/-- Diffs (only timelines that actually changed) from k to k+1. -/
def dumpDiffs (tn : TaskNet) (σ : Trace) (k : Nat) : String :=
  let cur  := σ[k]!
  let next := if k + 1 < σ.length then σ[k+1]! else cur
  let ids  := timelineIds tn.timelines
  let changed :=
    ids.filter (fun id =>
      match cur.get? id, next.get? id with
      | some v1, some v2 => v1 != v2
      | none, none       => false
      | _, _             => true)
  let lines :=
    changed.map (fun id =>
      s!"{id}: {showAt cur id} -> {showAt next id}")
  String.intercalate "\n" lines

/-- Pretty print expected set for a single `Con`. -/
def expectStr : Con → String
  | .val v =>
      match v with
      | .strVal s  => "\"" ++ s ++ "\""
      | .boolVal b => toString b
      | .intVal i  => toString i
      | .realVal r => toString r
  | .i_rng r => s!"[{r.low}, {r.high}]"
  | .r_rng r => s!"[{r.low}, {r.high}]"

/-- Evaluate one `TlCon` on a state with a small (colorized) explanation. -/
def explainCon (state : State) (c : TlCon) : String :=
  let actual := showAt state c.id
  let holds  := TimeLineCondition c state
  let want   := String.intercalate " OR " (c.cons.map expectStr)
  let badge  := Ansi.okBadge holds
  -- Color the whole line lightly, but especially highlight the result.
  let lhs := s!"{c.id}: {actual} ∈ {want}"
  let lhsColored := if holds then Ansi.green lhs else Ansi.red lhs
  s!"{badge} {lhsColored}"

/-- Pretty print a block for PRE/INV/POST at time k for a given task (colorized). -/
def preInvPostBlock
  (t : TaskDef) (sch : Schedule) (cur next : State) (k : Nat) : String :=
  match sch.get? t.id with
  | none => s!"{Ansi.bold t.id}\n  {Ansi.red "<not in schedule>"}\n"
  | some (st,en) =>
    let preActive  := (k = st)
    let invActive  := (st ≤ k ∧ k ≤ en)
    let postActive := (k = en)
    let preOk  := if preActive  then TimeLineConditions t.pre  cur  else true
    let invOk  := if invActive  then TimeLineConditions t.inv  cur  else true
    let postOk := if postActive then TimeLineConditions t.post next else true
    let preLines  := if t.pre.isEmpty  then ["(none)"] else t.pre.map (explainCon cur)
    let invLines  := if t.inv.isEmpty  then ["(none)"] else t.inv.map (explainCon cur)
    let postLines := if t.post.isEmpty then ["(none)"] else t.post.map (explainCon next)

    let showSec (label : String) (active : Bool) (ok : Bool) (ls : List String) : String :=
      if !active then s!"  {Ansi.gray (label ++ ": n/a")}\n"
      else
        let hdr := s!"  {label}: {Ansi.okWord ok}"
        let hdrColored := if ok then Ansi.green hdr else Ansi.red hdr
        hdrColored ++ "\n" ++
        (if ls.isEmpty then "" else "    " ++ String.intercalate "\n    " ls ++ "\n")

    s!"{Ansi.bold t.id}\n"
    ++ showSec "PRE"  preActive  preOk  preLines
    ++ showSec "INV"  invActive  invOk  invLines
    ++ showSec "POST" postActive postOk postLines

/-- All task intervals (for the header at a boundary line). -/
def showTaskTimes (sch : Schedule) (names : List TaskName) : String :=
  let bits := names.map (fun n =>
    match sch.get? n with
    | some (st,en) => s!"{n}({st},{en})"
    | none         => s!"{n}(?,?)")
  String.intercalate ", " bits

/-- One rich step report at boundary k, now with PRE/INV/POST evaluations. -/
def stepReport (tn : TaskNet) (sch : Schedule) (k : Nat) : String :=
  let σ      := Execute tn sch
  let len    := σ.length
  let cur    := σ[k]!
  let next   := if k + 1 < len then σ[k+1]! else cur
  let starts := taskStartsAt tn.tasks sch k
  let ends   := taskEndsAt   tn.tasks sch k
  let actives := tasksActiveAt tn.tasks sch k
  -- union (starts ∪ ends ∪ actives), de-duped and sorted
  let union := (starts ++ ends ++ actives).foldl (fun acc n => if acc.elem n then acc else acc ++ [n]) []
  let tasksHere := union.mergeSort (· ≤ ·)
  let startsStr := if starts.isEmpty then "—" else showTaskTimes sch starts
  let endsStr   := if ends.isEmpty   then "—" else showTaskTimes sch ends
  let chg   := dumpChangesSorted tn sch k
  let diffs := dumpDiffs tn σ k
  let pip   := String.intercalate "" (tasksHere.map (fun n =>
                match tn.tasks.find? (fun t => t.id = n) with
                | some t => preInvPostBlock t sch cur next k
                | none   => s!"{n}\n  <not defined>\n"))
  "────────────────────────────────────\n"
  ++ s!"k = {k}\n"
  ++ s!"start: {startsStr}\n"
  ++ s!"end:   {endsStr}\n"
  ++ Ansi.blue "== state before: ==" ++ "\n" ++ showStateLine tn cur ++ "\n"
  ++ Ansi.blue "== changes: =="      ++ "\n" ++ (if chg = "" then "  <none>\n" else chg ++ "\n")
  ++ Ansi.blue "== diffs: =="        ++ "\n" ++ (if diffs = "" then "  <none>\n" else diffs ++ "\n")
  ++ Ansi.blue "== PRE/INV/POST =="  ++ "\n" ++ pip
  ++ Ansi.blue "== state after: =="  ++ "\n" ++ showStateLine tn next

/-- All boundaries (already sorted) then pretty print all reports. -/
def scheduleReport (tn : TaskNet) (sch : Schedule) : String :=
  let ks := boundaryTimes sch
  String.intercalate "\n" (ks.map (stepReport tn sch))

end Debug
end TaskNet
