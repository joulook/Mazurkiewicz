import Mathlib.Data.Finset.Card

/-!
# Events

Labels, thread events and events (paper, Def. 3.1; `induction-popl`,
def:labels and def:events).

Relation to the paper's Def. 3.1:

* same: one initialization event `init`; a thread event `⟨t, i, lab⟩`; a read
  label `R(l)` carries no value;
* narrower (scope of the port, as in Coq): no kinds `k` on labels, no fence
  label, no error label;
* different numbering: indices start at `0` here; the paper's Def. A.8 counts
  from `1`.

Differences from the Coq development (`basic/Labels.v`, `basic/Events.v`),
where this file follows the paper: Coq has one initialization event per
location and a read label that carries a value.
-/

namespace Trust

/-- Thread identifiers. -/
abbrev Tid := ℕ
/-- Shared memory locations. -/
abbrev Loc := ℕ
/-- Values. -/
abbrev Val := ℕ

/-- Labels: `R(x)` and `W(x,v)`. -/
inductive Act
  | read (x : Loc)
  | write (x : Loc) (v : Val)
  deriving DecidableEq, Repr

namespace Act

/-- The location of a label. -/
def loc : Act → Loc
  | read x => x
  | write x _ => x

/-- `a` is a read label. -/
def IsRead : Act → Prop
  | read _ => True
  | write _ _ => False

/-- `a` is a write label. -/
def IsWrite : Act → Prop
  | read _ => False
  | write _ _ => True

instance : DecidablePred IsRead := fun a => by cases a <;> unfold IsRead <;> infer_instance
instance : DecidablePred IsWrite := fun a => by cases a <;> unfold IsWrite <;> infer_instance

theorem isRead_or_isWrite (a : Act) : a.IsRead ∨ a.IsWrite := by
  cases a <;> simp [IsRead, IsWrite]

theorem not_isRead_and_isWrite (a : Act) : ¬ (a.IsRead ∧ a.IsWrite) := by
  cases a <;> simp [IsRead, IsWrite]

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

/-- A write carries a write label to its location. -/
theorem IsWrite.exists_act {e : TEv} (h : e.IsWrite) : ∃ v, e.act = .write e.loc v := by
  unfold IsWrite at h
  unfold loc
  cases hact : e.act with
  | read x => rw [hact] at h; exact absurd h (by simp [Act.IsWrite])
  | write x v => exact ⟨v, rfl⟩

end TEv

end Trust
