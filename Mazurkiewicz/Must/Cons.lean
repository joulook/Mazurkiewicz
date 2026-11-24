import Mazurkiewicz.Must.Compute

/-!
# Consistency for `asyn` and `p2p`, executable (Definitions 3.4, 3.5, 3.8)

Paper: Section 3.2, Definitions 3.4, 3.5, 3.8. Plan: decisions Q1–Q4.

* `WfD G`: the clauses of `Wf` quantified over the events of `G` only; decidable; on graphs with
  `Supp` (every well-formed graph and every restriction of one) it is `Wf` (`wfD_iff`).
* `P2Pb G`, `P2Pc G`: conditions (b), (c) of Definition 3.5 with `so = [S^p2p]; po; [S^p2p]`,
  `so|dst` the `so` edges between sends with the same destination, `mval` the value relation:
  (b) `[US]; so|dst; rf ∩ mval = ∅`, (c) `po; rf⁻¹; (so|dst; rf ∩ mval)` irreflexive. Global
  `po` and `rf` (Q4).
* `ConsAsyn G := G.Wf` (Definition 3.4); `ConsAP G := G.Wf ∧ P2Pb G ∧ P2Pc G`: Definition 3.8
  for graphs whose events use `asyn` and `p2p` (for a graph without `p2p` sends, (b) and (c)
  hold trivially, so `ConsAP` is `consistent_asyn`). This domain is not enforced by the type:
  on a graph with `cd` or `mbox` events `ConsAP` applies no `cd`/`mbox` condition, so it is not
  Definition 3.8 there (M3 adds those models).
* `consAsynB`, `consAPB : Graph Q → Bool`, and `consAPB_iff`, `consAsynB_iff`.

Everything after this file takes the consistency test as a parameter `cons : Graph Q → Bool`,
so M3 can add `cd`, `mbox` and the combination.
-/

namespace Must

namespace Graph

open Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)]

/-- The send of a source, if it is a real send. -/
def srcOf : Option (Src Q) → Option (Ev Q)
  | some (.snd s) => some s
  | _ => none

omit [DecidableEq Q] [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
@[simp] theorem mem_srcOf {x : Option (Src Q)} {s : Ev Q} : s ∈ srcOf x ↔ x = some (.snd s) := by
  rcases x with _ | _ | s' <;> simp [srcOf]

variable (G : Graph Q)

/-- The clauses of well-formedness, over the events of the graph. -/
def WfD : Prop :=
  (∀ e ∈ G.events, ∀ e' ∈ G.events, e.tid = e'.tid → e.idx = e'.idx → e = e') ∧
  (∀ e ∈ G.events, ∀ i < e.idx, ∃ e' ∈ G.events, e'.tid = e.tid ∧ e'.idx = i) ∧
  (∀ e ∈ G.events, ((G.rf e).isSome ↔ e.IsRecv)) ∧
  (∀ r ∈ G.events, G.rf r = some .bot → r.IsRecvNB) ∧
  (∀ r ∈ G.events, ∀ s ∈ srcOf (G.rf r), s ∈ G.events ∧ s.Matches r) ∧
  (∀ r ∈ G.events, ∀ r' ∈ G.events, ∀ s ∈ srcOf (G.rf r), G.rf r' = some (.snd s) → r = r') ∧
  (∀ e ∈ G.events, ((G.nd e).isSome ↔ e.IsND)) ∧
  (∀ e ∈ G.events, ∀ v ∈ G.nd e, v ∈ e.ndSet) ∧
  (∀ a ∈ G.events, ¬ G.porf a a)

instance : Decidable G.WfD := by
  unfold WfD
  infer_instance

variable {G}

omit [DecidableEq Q] [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
/-- The target of a causal path is an event of the graph. -/
theorem mem_of_porf_right {a b : Ev Q} (h : G.porf a b) : b ∈ G.events := by
  obtain ⟨c, -, hc⟩ := TransGen.tail'_iff.mp h
  rcases hc with ⟨-, hb, -⟩ | ⟨hb, -⟩ <;> exact hb

omit [DecidableEq Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
/-- On graphs with `Supp`, `WfD` is well-formedness. -/
theorem wfD_iff (hS : G.Supp) : G.WfD ↔ G.Wf := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    have hrf : ∀ r x, G.rf r = some x → r ∈ G.events := fun r x h => by
      by_contra hr
      rw [(hS r hr).1] at h
      cases h
    have hnd : ∀ e v, G.nd e = some v → e ∈ G.events := fun e v h => by
      by_contra he
      rw [(hS e he).2] at h
      cases h
    refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e
      by_cases he : e ∈ G.events
      · simp [he, h3 e he]
      · simp [he, (hS e he).1]
    · exact fun r h => h4 r (hrf r _ h) h
    · exact fun r s h => (h5 r (hrf r _ h) s (mem_srcOf.mpr h)).1
    · exact fun r r' s h h' => h6 r (hrf r _ h) r' (hrf r' _ h') s (mem_srcOf.mpr h) h'
    · exact fun r s h => (h5 r (hrf r _ h) s (mem_srcOf.mpr h)).2
    · intro e
      by_cases he : e ∈ G.events
      · simp [he, h7 e he]
      · simp [he, (hS e he).2]
    · exact fun e v h => h8 e (hnd e v h) v h
    · exact fun a h => h9 a (mem_of_porf_right h) h
  · intro hG
    refine ⟨hG.idx_inj, hG.idx_contig, fun e he => ?_, fun r _ h => hG.rf_bot r h,
      fun r _ s hs => ?_, fun r _ r' _ s hs h => hG.rf_once r r' s (mem_srcOf.mp hs) h,
      fun e he => ?_, fun e _ v hv => hG.nd_mem e v hv, fun a _ => hG.porf_irrefl a⟩
    · simp [hG.rf_isSome, he]
    · exact ⟨hG.rf_mem r s (mem_srcOf.mp hs), hG.rf_match r s (mem_srcOf.mp hs)⟩
    · simp [hG.nd_isSome, he]

/-! ### The `p2p` conditions -/

variable (G)

/-- The destination of a send label. -/
def dstOf : Lab Q → Option Tid
  | .send _ d _ => some d
  | _ => none

/-- `so = [S^p2p]; po; [S^p2p]`, restricted to sends with the same destination (`so|dst`). -/
def SoDst (a b : Ev Q) : Prop :=
  a.lab.model? = some .p2p ∧ a.IsSend ∧ b.lab.model? = some .p2p ∧ b.IsSend ∧ G.po a b ∧
    dstOf a.lab = dstOf b.lab

instance (a b : Ev Q) : Decidable (G.SoDst a b) := by
  unfold SoDst
  infer_instance

/-- Definition 3.5 (b): `[US]; so|dst; rf ∩ mval = ∅`. -/
def P2Pb : Prop :=
  ∀ s' ∈ G.US, ∀ s ∈ G.events, ∀ r ∈ G.events,
    ¬ (G.SoDst s' s ∧ G.rf r = some (.snd s) ∧ s'.ValMatches r)

/-- Definition 3.5 (c): `po; rf⁻¹; (so|dst; rf ∩ mval)` is irreflexive. -/
def P2Pc : Prop :=
  ∀ r ∈ G.events, ∀ q ∈ G.events, ∀ s' ∈ G.events, ∀ s ∈ G.events,
    ¬ (G.po r q ∧ G.rf q = some (.snd s') ∧ G.SoDst s' s ∧ G.rf r = some (.snd s) ∧
      s'.ValMatches r)

instance : Decidable G.P2Pb := by
  unfold P2Pb
  infer_instance

instance : Decidable G.P2Pc := by
  unfold P2Pc
  infer_instance

/-- `consistent_asyn` (Definition 3.4). -/
def ConsAsyn : Prop := G.Wf

/-- Definition 3.8 for graphs of `asyn` and `p2p` events (Q4). -/
def ConsAP : Prop := G.Wf ∧ G.P2Pb ∧ G.P2Pc

/-- `consistent_asyn`, computed. -/
def consAsynB : Bool := decide G.WfD

/-- Consistency for `asyn` and `p2p`, computed. -/
def consAPB : Bool := decide (G.WfD ∧ G.P2Pb ∧ G.P2Pc)

variable {G}

theorem consAsynB_iff (hS : G.Supp) : G.consAsynB = true ↔ G.ConsAsyn := by
  rw [consAsynB, decide_eq_true_iff, wfD_iff hS, ConsAsyn]

theorem consAPB_iff (hS : G.Supp) : G.consAPB = true ↔ G.ConsAP := by
  rw [consAPB, decide_eq_true_iff, wfD_iff hS, ConsAP]

end Graph

end Must
