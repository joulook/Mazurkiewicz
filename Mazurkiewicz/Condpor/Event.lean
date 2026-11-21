import Mathlib.Data.Finset.Card

/-!
# Events with symbolic labels

Labels, thread events and events. This is `Trust/Event.lean` with four more
labels: generation of a symbolic value, evaluation of a constraint, blocking
and error.

* A read label `R(x)` carries no value, as in `Trust`.
* `gen s` is the label `A(s)`: the symbolic value `s` is generated.
* `cons φ` is the label of the evaluation of the constraint `φ`. The label is
  the formula of the program; the outcome of the evaluation (whether `φ` or
  its negation is assumed) is a component of the graph (`Graph.pol`), like the
  source of a read. So a thread has one next event, whatever the outcome.
* `block` and `error` are the labels of a blocked thread and of a program
  error.

`Act.loc` is `0` on the four new labels, which have no location; it is used
only for reads and writes.

Symbolic expressions are codes (`SExpr := ℕ`), like values. Which codes stand
for which expressions is fixed by a program and by an interpretation of the
formulas (`Sem`), not here.
-/

namespace Condpor

/-- Thread identifiers. -/
abbrev Tid := ℕ
/-- Shared memory locations. -/
abbrev Loc := ℕ
/-- Values. -/
abbrev Val := ℕ
/-- Symbolic expressions (codes). -/
abbrev SExpr := ℕ

/-- Labels. -/
inductive Act
  | read (x : Loc)
  | write (x : Loc) (v : Val)
  | gen (s : SExpr)
  | cons (φ : SExpr)
  | block
  | error
  deriving DecidableEq, Repr

namespace Act

/-- The location of a read or write label (`0` for the other labels, which
have none). -/
def loc : Act → Loc
  | read x => x
  | write x _ => x
  | _ => 0

/-- `a` is a read label. -/
def IsRead : Act → Prop
  | read _ => True
  | _ => False

/-- `a` is a write label. -/
def IsWrite : Act → Prop
  | write _ _ => True
  | _ => False

/-- `a` is a constraint-evaluation label. -/
def IsCons : Act → Prop
  | cons _ => True
  | _ => False

/-- `a` is neither a read nor a write: it touches no shared location. -/
def IsLocal : Act → Prop
  | read _ => False
  | write _ _ => False
  | _ => True

instance : DecidablePred IsRead := fun a => by cases a <;> unfold IsRead <;> infer_instance
instance : DecidablePred IsWrite := fun a => by cases a <;> unfold IsWrite <;> infer_instance
instance : DecidablePred IsCons := fun a => by cases a <;> unfold IsCons <;> infer_instance
instance : DecidablePred IsLocal := fun a => by cases a <;> unfold IsLocal <;> infer_instance

theorem isRead_or_isWrite_or_isLocal (a : Act) : a.IsRead ∨ a.IsWrite ∨ a.IsLocal := by
  cases a <;> simp [IsRead, IsWrite, IsLocal]

theorem not_isRead_and_isWrite (a : Act) : ¬ (a.IsRead ∧ a.IsWrite) := by
  cases a <;> simp [IsRead, IsWrite]

theorem IsLocal.not_isRead {a : Act} (h : a.IsLocal) : ¬ a.IsRead := by
  cases a <;> simp_all [IsRead, IsLocal]

theorem IsLocal.not_isWrite {a : Act} (h : a.IsLocal) : ¬ a.IsWrite := by
  cases a <;> simp_all [IsWrite, IsLocal]

theorem IsCons.isLocal {a : Act} (h : a.IsCons) : a.IsLocal := by
  cases a <;> simp_all [IsCons, IsLocal]

theorem IsWrite.not_isRead {a : Act} (h : a.IsWrite) : ¬ a.IsRead := by
  cases a <;> simp_all [IsRead, IsWrite]

end Act

/-- A thread event `⟨t, i, ℓ⟩`: the event number `i` (from `0`) of thread `t`,
with label `ℓ`. -/
structure TEv where
  /-- the thread -/
  tid : Tid
  /-- the index in the thread, from `0` -/
  idx : ℕ
  /-- the label -/
  act : Act
  deriving DecidableEq, Repr

/-- An event: the initialization event or a thread event. -/
inductive Ev
  | init
  | th (e : TEv)
  deriving DecidableEq, Repr

namespace TEv

/-- The location of a thread event. -/
abbrev loc (e : TEv) : Loc := e.act.loc
/-- `e` is a read. -/
abbrev IsRead (e : TEv) : Prop := e.act.IsRead
/-- `e` is a write. -/
abbrev IsWrite (e : TEv) : Prop := e.act.IsWrite
/-- `e` is a constraint evaluation. -/
abbrev IsCons (e : TEv) : Prop := e.act.IsCons
/-- `e` is neither a read nor a write. -/
abbrev IsLocal (e : TEv) : Prop := e.act.IsLocal

/-- A write carries a write label to its location. -/
theorem IsWrite.exists_act {e : TEv} (h : e.IsWrite) : ∃ v, e.act = .write e.loc v := by
  unfold IsWrite at h
  unfold loc
  cases hact : e.act <;> simp_all [Act.IsWrite, Act.loc]

/-- A read carries a read label to its location. -/
theorem IsRead.exists_act {e : TEv} (h : e.IsRead) : e.act = .read e.loc := by
  unfold IsRead at h
  unfold loc
  cases hact : e.act <;> simp_all [Act.IsRead, Act.loc]

/-- A constraint evaluation carries a formula. -/
theorem IsCons.exists_act {e : TEv} (h : e.IsCons) : ∃ φ, e.act = .cons φ := by
  unfold IsCons at h
  cases hact : e.act <;> simp_all [Act.IsCons]

end TEv

end Condpor
