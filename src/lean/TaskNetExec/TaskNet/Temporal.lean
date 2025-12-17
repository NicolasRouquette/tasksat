import Std
import TaskNet.Syntax
import TaskNet.Semantics

namespace TaskNet
namespace Temp

abbrev Pred  := State → Bool
abbrev TPred := Trace → Nat → Bool

-- -----------------
-- Small list ranges
-- -----------------

/-- [k, k+1, …, n-1] (empty if k ≥ n). -/
def rangeFrom (n k : Nat) : List Nat :=
  if k < n then Id.run do
    let m := n - k
    (List.range m).map (fun d => k + d)
  else
    []

/-- [0, 1, …, k]. -/
def rangeUpTo (k : Nat) : List Nat :=
  List.range (k + 1)

-- ----------------------
-- Boolean connectives on Bool
-- ----------------------

@[inline] def bNot (b : Bool) : Bool := b = false
@[inline] def bAnd (p q : Bool) : Bool := p && q
@[inline] def bOr  (p q : Bool) : Bool := p || q
@[inline] def bImp (p q : Bool) : Bool := (!p) || q

-- -------------------------
-- Temporal combinators (Bool)
-- -------------------------

/-- Lift a state predicate to now. -/
def now (φ : Pred) : TPred := fun σ k => φ (σ[k]!)

def tTrue : TPred := fun _ _ => true
def tFalse : TPred := fun _ _ => false
def tnot (φ : TPred) : TPred := fun σ k => bNot (φ σ k)
def tand (φ ψ : TPred) : TPred := fun σ k => bAnd (φ σ k) (ψ σ k)
def tor  (φ ψ : TPred) : TPred := fun σ k => bOr (φ σ k) (ψ σ k)
def timp (φ ψ : TPred) : TPred := fun σ k => bImp (φ σ k) (ψ σ k)

def X (φ : TPred) : TPred :=
  fun σ k => if k + 1 < σ.length then φ σ (k + 1) else false

def Always (φ : TPred) : TPred :=
  fun σ k0 => (rangeFrom σ.length k0).all (fun j => φ σ j)

def Eventually (φ : TPred) : TPred :=
  fun σ k0 => (rangeFrom σ.length k0).any (fun j => φ σ j)

def Prev (φ : TPred) : TPred :=
  fun σ k => if k = 0 then false else φ σ (k - 1)

def Once (φ : TPred) : TPred :=
  fun σ k0 => (rangeUpTo k0).any (fun j => φ σ j)

def Historically (φ : TPred) : TPred :=
  fun σ k0 => (rangeUpTo k0).all (fun j => φ σ j)

def Until (φ ψ : TPred) : TPred :=
  fun σ k0 =>
    (rangeFrom σ.length k0).any (fun j =>
      ψ σ j &&
      (List.range (j - k0)).all (fun d =>
        let i := k0 + d
        φ σ i))

def Since (φ ψ : TPred) : TPred :=
  fun σ k0 =>
    (rangeUpTo k0).any (fun j =>
      ψ σ j &&
      (List.range (k0 - j)).all (fun d =>
        let i := j + 1 + d
        φ σ i))

def EventuallyWithin (n : Nat) (φ : TPred) : TPred :=
  fun σ k0 =>
    let hi := Nat.min (σ.length - 1) (k0 + n)
    (List.range (hi - k0 + 1)).any (fun d => φ σ (k0 + d))

def AlwaysWithin (n : Nat) (φ : TPred) : TPred :=
  fun σ k0 =>
    let hi := Nat.min (σ.length - 1) (k0 + n)
    (List.range (hi - k0 + 1)).all (fun d => φ σ (k0 + d))

def OnceWithin (n : Nat) (φ : TPred) : TPred :=
  fun σ k0 =>
    let lo := k0 - n          -- truncated at 0, so this is max(0, k0-n)
    let count := k0 - lo + 1  -- number of indices in [lo .. k0]
    (List.range count).any (fun d =>
      let j := lo + d
      φ σ j)

def HistoricallyWithin (n : Nat) (φ : TPred) : TPred :=
  fun σ k0 =>
    let lo := k0 - n
    let count := k0 - lo + 1
    (List.range count).all (fun d =>
      let j := lo + d
      φ σ j)

def UntilWithin (n : Nat) (φ ψ : TPred) : TPred :=
  fun σ k0 =>
    if σ.length = 0 then
      false
    else
      let last := σ.length - 1
      let hi   := Nat.min last (k0 + n)
      if k0 ≤ hi then
        let count := hi - k0 + 1
        (List.range count).any (fun d =>
          let j := k0 + d
          ψ σ j &&
          -- φ must hold on [k0 .. j-1]
          (List.range (j - k0)).all (fun dd =>
            let i := k0 + dd
            φ σ i))
      else
        false

def SinceWithin (n : Nat) (φ ψ : TPred) : TPred :=
  fun σ k0 =>
    let lo := k0 - n
    let count := k0 - lo + 1  -- indices [lo .. k0]
    (List.range count).any (fun d =>
      let j := lo + d
      ψ σ j &&
      -- φ must hold on (j .. k0], i.e. j+1 .. k0
      (List.range (k0 - j)).all (fun dd =>
        let i := j + 1 + dd
        φ σ i))

-- ------------
-- Notation (scoped)
-- ------------

-- Future-time symbols

scoped notation:60 "□"  φ => TaskNet.Temp.Always φ
scoped notation:60 "◇"  φ => TaskNet.Temp.Eventually φ
scoped notation:60 "◯"  φ => TaskNet.Temp.X φ
scoped infixr:55   " ∧ " => TaskNet.Temp.tand
scoped infixr:54   " ∨ " => TaskNet.Temp.tor
scoped infixr:53   " ⟹ " => TaskNet.Temp.timp
scoped prefix:60   "¬"    => TaskNet.Temp.tnot

-- Past-time symbols

scoped notation:60 "□-"  φ => TaskNet.Temp.Historically φ
scoped notation:60 "◇-"  φ => TaskNet.Temp.Once φ
scoped notation:60 "◯-"  φ => TaskNet.Temp.Prev φ

-- Lift state predicates to "now"

scoped notation "⟨" φ "⟩" => TaskNet.Temp.now φ

-- -------------------------
-- Atomic predicates (State)
-- -------------------------

/-- Get String value at timeline id. -/
def getStr? (st : State) (id : String) : Option String :=
  match st.get? id with
  | some (.strVal s) => some s
  | _                => none

/-- Get Bool value at timeline id. -/
def getBool? (st : State) (id : String) : Option Bool :=
  match st.get? id with
  | some (.boolVal b) => some b
  | _                 => none

/-- Get Float (promoting int→float) at timeline id. -/
def getReal? (st : State) (id : String) : Option Float :=
  match st.get? id with
  | some v => valueToReal? v
  | none   => none

-- String atoms (categorical timelines)
def eqStr  (id val : String) : Pred := fun st => getStr? st id = some val
def on     (id : String)     : Pred := eqStr id "on"
def off    (id : String)     : Pred := eqStr id "off"

-- Boolean atoms
def boolIs (id : String) (b : Bool) : Pred :=
  fun st => match getBool? st id with | some b' => b' = b | none => false

def trueAt  (id : String) : Pred := boolIs id true
def falseAt (id : String) : Pred := boolIs id false

-- Numeric atoms

def realGT (id : String) (a : Float) : Pred :=
  fun st =>
    match getReal? st id with
    | some x => x > a
    | none   => false

def realGE (id : String) (a : Float) : Pred :=
  fun st =>
    match getReal? st id with
    | some x => x ≥ a
    | none   => false

def realLT (id : String) (a : Float) : Pred :=
  fun st =>
    match getReal? st id with
    | some x => x < a
    | none   => false

def realLE (id : String) (a : Float) : Pred :=
  fun st =>
    match getReal? st id with
    | some x => x ≤ a
    | none   => false

def realBetween (id : String) (lo hi : Float) : Pred :=
  fun st =>
    match getReal? st id with
    | some x => decide (lo ≤ x) ∧ decide (x ≤ hi)
    | none   => false

def realEq (id : String) (a : Float) : Pred :=
  fun st =>
    match getReal? st id with
    | some x => x == a
    | none   => false

def realApproxEq (id : String) (a : Float) (eps : Float := 1e-6) : Pred :=
  fun st =>
    match getReal? st id with
    | some x => decide (Float.abs (x - a) ≤ eps)
    | none   => false

-- ---------------------------
-- Event detectors (Bool TPred)
-- ---------------------------

def changeFrom (id : String) (fromVal toVal : String) : TPred :=
  (Prev (now (eqStr id fromVal))) ∧ (now (eqStr id toVal))

/-- Threshold cross up: ≤ thr then ≥ thr. -/
def crossesUp (id : String) (thr : Float) : TPred :=
  (Prev (now (realLT id thr))) ∧ (now (realGE id thr))

/-- Threshold cross down: ≥ thr then ≤ thr. -/
def crossesDown (id : String) (thr : Float) : TPred :=
  (Prev (now (realGT id thr))) ∧ (now (realLE id thr))

-- -----------------------
-- Running on a schedule
-- -----------------------

/-- Evaluate a temporal property from the beginning of the (deterministic) trace. -/
def TemporalHolds (tn : TaskNet) (sch : Schedule) (φ : TPred) : Bool :=
  let σ := Execute tn sch
  φ σ 0

/-- Check if a schedule is satisfactory with respect to a temporal property. -/
def Satisfactory (tn : TaskNet) (sch : Schedule) (φ : TPred) : Bool :=
  StartEndTimesOk tn sch &&
  let σ := Execute tn sch
  ObligationsHold tn sch σ && φ σ 0

end Temp
end TaskNet
