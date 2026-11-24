import Mathlib.Data.Finset.Card

/-!
# Events of Must (Definition 3.1)

Paper: Section 3.1, Definition 3.1. Plan: `plan/must/lean/LEAN-PLAN.md`, decisions Q1, Q6, Q14.

* `Tid`, `Val` are `ℕ` (Q14); indices are `ℕ`.
* `Comm` is the set of communication models `asyn`, `p2p`, `cd`, `mbox`.
* `RAttr` is the set of receive attributes `⟨M, V⟩`: a model and `blocking = true` for `b`,
  `false` for `nb`.
* `Lab Q` is the set of labels. The receive predicate `vals` of `R_a(vals)` is an element of a
  type `Q` read through a membership relation `v ∈ vals` (`[Membership Val Q]`): with `Q := Set Val`
  every predicate on values is a label; with `Q := Finset Val` or `Q := VPred` labels have
  decidable equality. The abstract theory is stated for an arbitrary `Q` (Q14).
* `nd S` is the label `ND_S`, `S` a finite set of values; the outcome is not part of the label
  (Q6): it is a component of the graph (`Graph.nd`). Non-emptiness of `S` is not part of the
  label; it follows from well-formedness for every ND event of a graph (`Graph.Wf.nd_nonempty`).
* An event is `⟨t, i, l⟩`; in a well-formed graph it is determined by `(t, i)`
  (`Graph.Wf.idx_inj`, Q1).
-/

namespace Must

/-- Thread identifiers. -/
abbrev Tid := ℕ
/-- Values. -/
abbrev Val := ℕ

/-- Communication models. -/
inductive Comm
  | asyn
  | p2p
  | cd
  | mbox
  deriving DecidableEq

/-- Receive attributes `⟨M, V⟩`: the model of the receive, and whether it is blocking
(`V = b`) or not (`V = nb`). -/
structure RAttr where
  /-- the communication model -/
  model : Comm
  /-- `true` for a blocking receive, `false` for a non-blocking one -/
  blocking : Bool
  deriving DecidableEq

/-- Labels, over a type `Q` of receive predicates. -/
inductive Lab (Q : Type)
  /-- `R_a(vals)` -/
  | recv (a : RAttr) (vals : Q)
  /-- `S_M(t, v)`: model `M`, destination `t`, value `v` -/
  | send (m : Comm) (dst : Tid) (v : Val)
  /-- `ND_S` -/
  | nd (S : Finset Val)
  /-- `B` -/
  | block
  /-- `error` -/
  | error
  deriving DecidableEq

/-- A predicate on values with decidable equality and decidable membership: every value, or the
values of a finite set. Used by computed instances (Q14). -/
inductive VPred
  | any
  | fin (s : Finset Val)
  deriving DecidableEq

namespace VPred

/-- Membership of a value in a predicate. -/
def Mem (p : VPred) (v : Val) : Prop :=
  match p with
  | any => True
  | fin s => v ∈ s

instance : Membership Val VPred := ⟨Mem⟩

@[simp] theorem mem_any (v : Val) : v ∈ (any : VPred) := trivial
@[simp] theorem mem_fin (s : Finset Val) (v : Val) : v ∈ fin s ↔ v ∈ s := Iff.rfl

instance (v : Val) (p : VPred) : Decidable (v ∈ p) :=
  match p with
  | any => isTrue trivial
  | fin s => inferInstanceAs (Decidable (v ∈ s))

end VPred

variable {Q : Type}

namespace Lab

/-- `l` is a receive label. -/
def IsRecv : Lab Q → Prop
  | recv _ _ => True
  | _ => False

/-- `l` is a send label. -/
def IsSend : Lab Q → Prop
  | send _ _ _ => True
  | _ => False

/-- `l` is an ND label. -/
def IsND : Lab Q → Prop
  | nd _ => True
  | _ => False

/-- `l` is a blocking receive label (`R^b`). -/
def IsRecvB : Lab Q → Prop
  | recv a _ => a.blocking = true
  | _ => False

/-- `l` is a non-blocking receive label (`R^nb`). -/
def IsRecvNB : Lab Q → Prop
  | recv a _ => a.blocking = false
  | _ => False

/-- `l` is a block or error label. -/
def IsLoc : Lab Q → Prop
  | block => True
  | error => True
  | _ => False

/-- The set `S` of an ND label (`∅` for the other labels). -/
def ndSet : Lab Q → Finset Val
  | nd S => S
  | _ => ∅

/-- The model of a send or receive label. -/
def model? : Lab Q → Option Comm
  | recv a _ => some a.model
  | send m _ _ => some m
  | _ => none

instance : DecidablePred (IsRecv (Q := Q)) := fun l => by
  cases l <;> unfold IsRecv <;> infer_instance
instance : DecidablePred (IsSend (Q := Q)) := fun l => by
  cases l <;> unfold IsSend <;> infer_instance
instance : DecidablePred (IsND (Q := Q)) := fun l => by
  cases l <;> unfold IsND <;> infer_instance
instance : DecidablePred (IsRecvB (Q := Q)) := fun l => by
  cases l <;> unfold IsRecvB <;> infer_instance
instance : DecidablePred (IsRecvNB (Q := Q)) := fun l => by
  cases l <;> unfold IsRecvNB <;> infer_instance
instance : DecidablePred (IsLoc (Q := Q)) := fun l => by
  cases l <;> unfold IsLoc <;> infer_instance

theorem isRecv_iff (l : Lab Q) : l.IsRecv ↔ ∃ a vals, l = recv a vals := by
  cases l <;> simp [IsRecv]

theorem isSend_iff (l : Lab Q) : l.IsSend ↔ ∃ m d v, l = send m d v := by
  cases l <;> simp [IsSend]

theorem isND_iff (l : Lab Q) : l.IsND ↔ ∃ S, l = nd S := by
  cases l <;> simp [IsND]

theorem IsRecvB.isRecv {l : Lab Q} (h : l.IsRecvB) : l.IsRecv := by
  cases l <;> simp_all [IsRecvB, IsRecv]

theorem IsRecvNB.isRecv {l : Lab Q} (h : l.IsRecvNB) : l.IsRecv := by
  cases l <;> simp_all [IsRecvNB, IsRecv]

/-- A receive is blocking or non-blocking. -/
theorem IsRecv.recvB_or_recvNB {l : Lab Q} (h : l.IsRecv) : l.IsRecvB ∨ l.IsRecvNB := by
  cases l <;> simp_all [IsRecv, IsRecvB, IsRecvNB]

theorem not_isRecvB_of_isRecvNB {l : Lab Q} (h : l.IsRecvNB) : ¬ l.IsRecvB := by
  cases l <;> simp_all [IsRecvB, IsRecvNB]

theorem IsSend.not_isRecv {l : Lab Q} (h : l.IsSend) : ¬ l.IsRecv := by
  cases l <;> simp_all [IsSend, IsRecv]

theorem IsND.not_isRecv {l : Lab Q} (h : l.IsND) : ¬ l.IsRecv := by
  cases l <;> simp_all [IsND, IsRecv]

theorem IsLoc.not_isRecv {l : Lab Q} (h : l.IsLoc) : ¬ l.IsRecv := by
  cases l <;> simp_all [IsLoc, IsRecv]

theorem IsSend.not_isND {l : Lab Q} (h : l.IsSend) : ¬ l.IsND := by
  cases l <;> simp_all [IsSend, IsND]

theorem IsLoc.not_isND {l : Lab Q} (h : l.IsLoc) : ¬ l.IsND := by
  cases l <;> simp_all [IsLoc, IsND]

theorem IsRecv.not_isND {l : Lab Q} (h : l.IsRecv) : ¬ l.IsND := by
  cases l <;> simp_all [IsRecv, IsND]

theorem IsRecv.not_isSend {l : Lab Q} (h : l.IsRecv) : ¬ l.IsSend := by
  cases l <;> simp_all [IsRecv, IsSend]

/-- Every label is exactly one of: receive, send, ND, block or error. -/
theorem cases_lab (l : Lab Q) : l.IsRecv ∨ l.IsSend ∨ l.IsND ∨ l.IsLoc := by
  cases l <;> simp [IsRecv, IsSend, IsND, IsLoc]

end Lab

/-- An event `⟨t, i, l⟩`. -/
structure Ev (Q : Type) where
  /-- the thread -/
  tid : Tid
  /-- the index in the thread, from `0` -/
  idx : ℕ
  /-- the label -/
  lab : Lab Q
  deriving DecidableEq

namespace Ev

/-- `e` is a receive. -/
abbrev IsRecv (e : Ev Q) : Prop := e.lab.IsRecv
/-- `e` is a send. -/
abbrev IsSend (e : Ev Q) : Prop := e.lab.IsSend
/-- `e` is an ND event. -/
abbrev IsND (e : Ev Q) : Prop := e.lab.IsND
/-- `e` is a blocking receive. -/
abbrev IsRecvB (e : Ev Q) : Prop := e.lab.IsRecvB
/-- `e` is a non-blocking receive. -/
abbrev IsRecvNB (e : Ev Q) : Prop := e.lab.IsRecvNB
/-- `e` is a block or error event. -/
abbrev IsLoc (e : Ev Q) : Prop := e.lab.IsLoc
/-- The set of an ND event. -/
abbrev ndSet (e : Ev Q) : Finset Val := e.lab.ndSet

variable [Membership Val Q]

/-- The send `s` and the receive `r` match (Definition 3.3, fourth item): the destination of
`s` is the thread of `r`, the value of `s` satisfies the predicate of `r`, and both have the same
model. False unless `s` is a send and `r` a receive. -/
def Matches (s r : Ev Q) : Prop :=
  match s.lab, r.lab with
  | .send m d v, .recv a vals => d = r.tid ∧ v ∈ vals ∧ a.model = m
  | _, _ => False

/-- The value of `s` satisfies the predicate of `r` (the relation `mval` of Section 3.1 on
labels). False unless `s` is a send and `r` a receive. -/
def ValMatches (s r : Ev Q) : Prop :=
  match s.lab, r.lab with
  | .send _ _ v, .recv _ vals => v ∈ vals
  | _, _ => False

instance [∀ (v : Val) (q : Q), Decidable (v ∈ q)] (s r : Ev Q) : Decidable (Matches s r) := by
  unfold Matches
  split <;> infer_instance

instance [∀ (v : Val) (q : Q), Decidable (v ∈ q)] (s r : Ev Q) : Decidable (ValMatches s r) := by
  unfold ValMatches
  split <;> infer_instance

theorem Matches.isSend {s r : Ev Q} (h : Matches s r) : s.IsSend := by
  unfold Matches at h
  split at h
  · next h1 _ => simp [IsSend, h1, Lab.IsSend]
  · exact h.elim

theorem Matches.isRecv {s r : Ev Q} (h : Matches s r) : r.IsRecv := by
  unfold Matches at h
  split at h
  · next _ h2 => simp [IsRecv, h2, Lab.IsRecv]
  · exact h.elim

theorem Matches.valMatches {s r : Ev Q} (h : Matches s r) : ValMatches s r := by
  unfold Matches at h
  unfold ValMatches
  split at h
  · exact h.2.1
  · exact h.elim

theorem Matches.dst {s r : Ev Q} (h : Matches s r) :
    ∃ m v, s.lab = .send m r.tid v := by
  unfold Matches at h
  split at h
  · next m d v _ _ h1 _ => exact ⟨m, v, h.1 ▸ h1⟩
  · exact h.elim

theorem Matches.model {s r : Ev Q} (h : Matches s r) : s.lab.model? = r.lab.model? := by
  unfold Matches at h
  split at h
  · next h1 h2 => simp [h1, h2, Lab.model?, h.2.2]
  · exact h.elim

end Ev

end Must
