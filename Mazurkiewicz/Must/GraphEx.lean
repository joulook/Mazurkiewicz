import Mazurkiewicz.Must.Compute
import Mazurkiewicz.Must.OpsMore

/-!
# Computed examples of Must graphs

Receive predicates are `VPred` (decidable). Threads `T1, T2, T3` are `1, 2, 3`.

* Example 3.1 of the paper: the program
  `T1: send(T3, 1); send(T2, 2)`, `T2: recv(); send(T3, 3)`, `T3: recv(); recv()` (p2p, blocking
  receives, every value accepted) and its two graphs `ex31a`, `ex31b`, built by the additions of
  `Ops.lean`; both are well-formed, and they differ in the sources of `T3`.
* At least one graph for each of the ten clauses of `Wf`, violating that clause (proved not
  well-formed through it; that the other clauses hold is not proved): two events with the same
  `(tid, idx)`, a lone event with index `1`, a receive without a source, `⊥` read by a blocking
  receive, a dangling source, a send read twice, a destination mismatch, a value outside the
  predicate, a model mismatch, an ND event without an outcome, an outcome outside its set, a
  `porf` cycle.
* A restriction to a set that is not closed and is not well-formed; non-blocking receives
  sharing `⊥`, well-formed.
* Computed checks with the instances of `Compute.lean`: `porf`, `Closed`, `pred`, keys, and a
  revisit (`Wf.revisit`).
-/

namespace Must

namespace GraphEx

open Graph Relation

/-- A blocking p2p receive accepting every value. -/
abbrev rb : Lab VPred := .recv ⟨.p2p, true⟩ .any

/-- `T1: send(T3, 1)` -/
abbrev s10 : Ev VPred := ⟨1, 0, .send .p2p 3 1⟩
/-- `T1: send(T2, 2)` -/
abbrev s11 : Ev VPred := ⟨1, 1, .send .p2p 2 2⟩
/-- `T2: recv()` -/
abbrev r20 : Ev VPred := ⟨2, 0, rb⟩
/-- `T2: send(T3, 3)` -/
abbrev s21 : Ev VPred := ⟨2, 1, .send .p2p 3 3⟩
/-- `T3: recv()` (first) -/
abbrev r30 : Ev VPred := ⟨3, 0, rb⟩
/-- `T3: recv()` (second) -/
abbrev r31 : Ev VPred := ⟨3, 1, rb⟩

/-- The common part of the two graphs of Example 3.1: `T1`, `T2` complete, `T2` reads
`send(T2, 2)`. -/
abbrev ex31base : Graph VPred :=
  (((empty.addSend s10).addSend s11).addRecv r20 (.snd s11)).addSend s21

/-- Example 3.1, graph 1: `T3` reads `1`, then `3`. -/
abbrev ex31a : Graph VPred := (ex31base.addRecv r30 (.snd s10)).addRecv r31 (.snd s21)

/-- Example 3.1, graph 2: `T3` reads `3`, then `1`. -/
abbrev ex31b : Graph VPred := (ex31base.addRecv r30 (.snd s21)).addRecv r31 (.snd s10)

theorem ex31base_wf : ex31base.Wf := by
  have h1 := (empty_wf (Q := VPred)).addSend (e := s10) (by decide) (by decide)
  have h2 := h1.addSend (e := s11) (by decide) (by decide)
  have h3 := h2.addRecv (e := r20) (s := s11) (by decide) (by decide) (by decide)
  exact h3.addSend (e := s21) (by decide) (by decide)

theorem ex31a_wf : ex31a.Wf :=
  (ex31base_wf.addRecv (e := r30) (s := s10) (by decide) (by decide) (by decide)).addRecv
    (e := r31) (s := s21) (by decide) (by decide) (by decide)

theorem ex31b_wf : ex31b.Wf :=
  (ex31base_wf.addRecv (e := r30) (s := s21) (by decide) (by decide) (by decide)).addRecv
    (e := r31) (s := s10) (by decide) (by decide) (by decide)

theorem ex31a_ne_ex31b : ex31a ≠ ex31b := fun h => by
  have := congrArg (fun G => G.rf r30) h
  revert this
  decide

/-- Every send of graph 1 is read. -/
theorem ex31a_US : ex31a.US = ∅ := by decide

/-- Removing the receives of `T3` makes the sends to `T3` unread. -/
theorem ex31a_remove_US : (ex31a.remove {r30, r31}).US = {s10, s21} := by decide

/-- The removal of the receives of `T3` is a prefix. -/
theorem ex31a_remove_isPrefixOf : (ex31a.remove {r30, r31}).IsPrefixOf ex31a := by
  refine ex31a_wf.remove_isPrefixOf (fun q hq b hb => ?_)
  have hb' := (ex31a_wf.mem_of_porfStep hb).2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl <;> rcases hb with ⟨-, -, ht, hi⟩ | ⟨-, hrf⟩
  · revert hb' ht hi
    decide +revert
  · revert hrf
    decide +revert
  · revert hb' ht hi
    decide +revert
  · revert hrf
    decide +revert

/-! ### One violation per clause (`rf_bot`, `rf_once`, `rf_match`, `porf_irrefl`) -/

/-- A graph of one receive `r` with source `x`, and a list of sends. -/
def single (r : Ev VPred) (x : Src VPred) (ss : Finset (Ev VPred)) : Graph VPred where
  events := insert r ss
  rf := fun e => if e = r then some x else none
  nd := fun _ => none

/-- A blocking receive reading `⊥`. -/
theorem not_wf_bot : ¬ (single ⟨2, 0, rb⟩ .bot ∅).Wf := fun h => by
  have := h.rf_bot ⟨2, 0, rb⟩ (by simp [single])
  revert this
  decide

/-- A send read twice. -/
def twice : Graph VPred where
  events := {⟨1, 0, .send .p2p 2 1⟩, ⟨2, 0, rb⟩, ⟨2, 1, rb⟩}
  rf := fun e => if e = ⟨2, 0, rb⟩ ∨ e = ⟨2, 1, rb⟩ then some (.snd ⟨1, 0, .send .p2p 2 1⟩)
    else none
  nd := fun _ => none

theorem not_wf_twice : ¬ twice.Wf := fun h => by
  have := h.rf_once ⟨2, 0, rb⟩ ⟨2, 1, rb⟩ ⟨1, 0, .send .p2p 2 1⟩ (by decide) (by decide)
  revert this
  decide

/-- A destination mismatch: a send to `T3` read by `T2`. -/
theorem not_wf_dst :
    ¬ (single ⟨2, 0, rb⟩ (.snd ⟨1, 0, .send .p2p 3 1⟩) {⟨1, 0, .send .p2p 3 1⟩}).Wf :=
  fun h => by
    have := h.rf_match ⟨2, 0, rb⟩ ⟨1, 0, .send .p2p 3 1⟩ (by simp [single])
    revert this
    decide

/-- A value outside the predicate: `1` read by a receive accepting only `0`. -/
theorem not_wf_val :
    ¬ (single ⟨2, 0, .recv ⟨.p2p, true⟩ (.fin {0})⟩ (.snd ⟨1, 0, .send .p2p 2 1⟩)
      {⟨1, 0, .send .p2p 2 1⟩}).Wf :=
  fun h => by
    have := h.rf_match ⟨2, 0, .recv ⟨.p2p, true⟩ (.fin {0})⟩ ⟨1, 0, .send .p2p 2 1⟩
      (by simp [single])
    revert this
    decide

/-- A model mismatch: a `p2p` send read by a `cd` receive. -/
theorem not_wf_model :
    ¬ (single ⟨2, 0, .recv ⟨.cd, true⟩ .any⟩ (.snd ⟨1, 0, .send .p2p 2 1⟩)
      {⟨1, 0, .send .p2p 2 1⟩}).Wf :=
  fun h => by
    have := h.rf_match ⟨2, 0, .recv ⟨.cd, true⟩ .any⟩ ⟨1, 0, .send .p2p 2 1⟩ (by simp [single])
    revert this
    decide

/-- `T1: recv(); send(T2, 1)`, `T2: recv(); send(T1, 2)`, each receive reading the other
thread's send. -/
def cyc : Graph VPred where
  events := {⟨1, 0, rb⟩, ⟨1, 1, .send .p2p 2 1⟩, ⟨2, 0, rb⟩, ⟨2, 1, .send .p2p 1 2⟩}
  rf := fun e =>
    if e = ⟨1, 0, rb⟩ then some (.snd ⟨2, 1, .send .p2p 1 2⟩)
    else if e = ⟨2, 0, rb⟩ then some (.snd ⟨1, 1, .send .p2p 2 1⟩)
    else none
  nd := fun _ => none

/-- The causal cycle `r₁ po s₁ rf r₂ po s₂ rf r₁`. -/
theorem not_wf_cyc : ¬ cyc.Wf := fun h => by
  refine h.porf_irrefl ⟨1, 0, rb⟩ ?_
  have s1 : cyc.porfStep ⟨1, 0, rb⟩ ⟨1, 1, .send .p2p 2 1⟩ := Or.inl (by decide)
  have s2 : cyc.porfStep ⟨1, 1, .send .p2p 2 1⟩ ⟨2, 0, rb⟩ := Or.inr (by decide)
  have s3 : cyc.porfStep ⟨2, 0, rb⟩ ⟨2, 1, .send .p2p 1 2⟩ := Or.inl (by decide)
  have s4 : cyc.porfStep ⟨2, 1, .send .p2p 1 2⟩ ⟨1, 0, rb⟩ := Or.inr (by decide)
  exact (((TransGen.single s1).tail s2).tail s3).tail s4

/-! ### One violation per clause (the other clauses) -/

/-- Two events with the same `(tid, idx)` (`idx_inj`). -/
def dupIdx : Graph VPred := ⟨{⟨1, 0, .block⟩, ⟨1, 0, .error⟩}, fun _ => none, fun _ => none⟩

theorem not_wf_dupIdx : ¬ dupIdx.Wf := fun h => by
  have := h.idx_inj ⟨1, 0, .block⟩ (by decide) ⟨1, 0, .error⟩ (by decide) rfl rfl
  revert this
  decide

/-- A lone event with index `1` (`idx_contig`). -/
def gapIdx : Graph VPred := ⟨{⟨1, 1, .block⟩}, fun _ => none, fun _ => none⟩

theorem not_wf_gapIdx : ¬ gapIdx.Wf := fun h => by
  obtain ⟨e, he, -, hi⟩ := h.idx_contig ⟨1, 1, .block⟩ (by decide) 0 (by decide)
  simp only [gapIdx, Finset.mem_singleton] at he
  subst he
  exact absurd hi (by decide)

/-- A receive without a source (`rf_isSome`). -/
def noSrc : Graph VPred := ⟨{⟨2, 0, rb⟩}, fun _ => none, fun _ => none⟩

theorem not_wf_noSrc : ¬ noSrc.Wf := fun h => by
  have := (h.rf_isSome ⟨2, 0, rb⟩).mpr ⟨by decide, by decide⟩
  revert this
  decide

/-- A dangling source: a matching send outside the graph (`rf_mem`). -/
theorem not_wf_dangling : ¬ (single ⟨2, 0, rb⟩ (.snd ⟨1, 0, .send .p2p 2 1⟩) ∅).Wf := fun h => by
  have := h.rf_mem ⟨2, 0, rb⟩ ⟨1, 0, .send .p2p 2 1⟩ (by simp [single])
  revert this
  decide

/-- An ND event without an outcome (`nd_isSome`). -/
def noOut : Graph VPred := ⟨{⟨1, 0, .nd {0, 1}⟩}, fun _ => none, fun _ => none⟩

theorem not_wf_noOut : ¬ noOut.Wf := fun h => by
  have := (h.nd_isSome ⟨1, 0, .nd {0, 1}⟩).mpr ⟨by decide, by decide⟩
  revert this
  decide

/-- An ND outcome outside its set (`nd_mem`). -/
def badOut : Graph VPred where
  events := {⟨1, 0, .nd {0, 1}⟩}
  rf := fun _ => none
  nd := fun e => if e = ⟨1, 0, .nd {0, 1}⟩ then some 2 else none

theorem not_wf_badOut : ¬ badOut.Wf := fun h => by
  have := h.nd_mem ⟨1, 0, .nd {0, 1}⟩ 2 (by decide)
  revert this
  decide

/-! ### Restriction, `⊥`, computed checks -/

/-- Removing `send(T3, 1)` from graph 1 does not give a closed set ... -/
theorem ex31a_erase_not_closed : ¬ ex31a.Closed (ex31a.events.erase s10) := by decide

/-- ... and the restriction is not well-formed: `T3`'s first receive has a dangling source. -/
theorem not_wf_ex31a_erase : ¬ (ex31a.restrict (ex31a.events.erase s10)).Wf := fun h => by
  have := h.rf_mem r30 s10 (by decide)
  revert this
  decide

/-- A non-blocking receive. -/
abbrev rnb : Lab VPred := .recv ⟨.asyn, false⟩ .any

/-- Two non-blocking receives of `T1` both reading `⊥`: well-formed (read once concerns real
sends only). -/
theorem nb_bot_wf : ((empty.addRecv ⟨1, 0, rnb⟩ .bot).addRecv ⟨1, 1, rnb⟩ .bot :
    Graph VPred).Wf :=
  ((empty_wf (Q := VPred)).addRecv_bot (by decide) (by decide)).addRecv_bot (by decide)
    (by decide)

theorem ex31a_porf_s10_r30 : ex31a.porf s10 r30 := by decide
theorem ex31a_porf_s10_r31 : ex31a.porf s10 r31 := by decide
theorem ex31a_not_porf_r30_s10 : ¬ ex31a.porf r30 s10 := by decide

/-- The strict causal predecessors of `T3`'s second receive in graph 1: all other events. -/
theorem ex31a_pred_r31 : ex31a.pred r31 = {s10, s11, r20, s21, r30} := by decide

theorem ex31a_closed_pred : ex31a.Closed (ex31a.pred r30) := by decide

theorem ex31a_key_ne : ex31a.key ≠ ex31b.key := by decide

/-- The two graphs differ as elements of `{G // G.Supp}`, by the computed equality. -/
theorem ex31a_ne_ex31b_supp :
    (⟨ex31a, ex31a_wf.supp⟩ : {G : Graph VPred // G.Supp}) ≠ ⟨ex31b, ex31b_wf.supp⟩ := by
  decide

/-- `T3`'s first receive reads `1`; `send(T3, 3)` is unread. -/
abbrev hrv : Graph VPred := (ex31base.addRecv r30 (.snd s10))

theorem hrv_wf : hrv.Wf := ex31base_wf.addRecv (by decide) (by decide) (by decide)

/-- The revisit of `T3`'s first receive by `send(T3, 3)`, deleting nothing. -/
theorem hrv_revisit_wf : (hrv.revisit r30 s21 ∅).Wf :=
  hrv_wf.revisit (by decide) (by decide) (by decide) (by decide) (by decide) (by simp)
    (fun _ _ _ _ => by simp) (fun _ _ _ _ _ _ => by simp)

/-- After the revisit, `send(T3, 1)` is unread. -/
theorem hrv_revisit_US : (hrv.revisit r30 s21 ∅).US = {s10} := by decide

end GraphEx

end Must
