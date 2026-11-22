import Mazurkiewicz.Condpor.Rmw.PrevTerm
import Mazurkiewicz.Condpor.Rf.Complete

/-!
# Read-modify-write accesses: completeness

Proposition A.28, Lemma A.29 and Theorem A.30 of the TruSt appendix (Theorem 4
of ConDpor) for a model with `ExtensibleX`: Algorithm 1 reaches every
well-formed, consistent, full execution of a bounded program.

* The case of a non-revisit step is the proof of `Complete.lean` (text
  generated from it), with `PrevReach.invX` and `PrevReach.next_of_prevStepX`.
* The case of a revisit step is `RvData'.step` of `Rf/Complete.lean`, which
  has no hypothesis on the model: the revisit is a step because its result,
  the graph `X` of the backward chain, is consistent.
-/

namespace Condpor

open Program

variable {P : XProgram} {M : Model} {S : Solver} {τ : TieBreak S}

/-- Proposition A.28, the case of a non-revisit step. -/
theorem Reach.step_of_prevStep_nrX {Gf X : Graph} {c : Config} {e : TEv}
    (hM : ExtensibleX P M) (hGf : Gf.Wf) (hEf : P.toProgram.Exec Gf) (hcf : (M.sym S).cons Gf)
    (hff : P.toProgram.Full Gf)
    (hX : PrevReach P.toProgram τ Gf X) (hc : Reach P.toProgram (M.sym S) τ c)
    (hs : PrevStep P.toProgram τ X e .nr c.abs) :
    ∃ c', StepL P.toProgram (M.sym S) τ c e .nr c' ∧ c'.abs = X := by
  obtain ⟨hXW, -, hXc, -, -⟩ := PrevReach.invX hM hGf hEf hcf hff hX
  obtain ⟨-, -, hcc, -⟩ := hc.sound
  have hnext := PrevReach.next_of_prevStepX hM hGf hEf hcf hff hX hs
  obtain ⟨hme, habs, -⟩ := hs.nr_inv
  have he : e ∈ X.events := hme.1
  have hsink : ∀ q, X.rf q ≠ some (.th e) := by
    intro q hq
    exact hme.2.1 (.th q)
      (Relation.TransGen.single (Or.inr ⟨q, rfl, (hXW.rf_source_mem hq).1, hq⟩))
  rcases e.act.isRead_or_isWrite_or_isLocal with hk | hw | hk
  · have hact := TEv.IsRead.exists_act hk
    obtain ⟨w, hrf, hwt⟩ := hXW.rf_read e he _ hact
    have hdec : (c.addRead e w).abs = X := by
      rw [Config.addRead_abs, habs]
      exact Graph.remove_addRead hXW he hact hrf hsink
    have hwt' : c.abs.IsWriteTo e.loc w := by
      rw [habs]
      cases w with
      | init => trivial
      | th w' =>
        refine ⟨Finset.mem_inter.mpr ⟨hwt.1, Finset.mem_sdiff.mpr ⟨hwt.1, ?_⟩⟩, hwt.2⟩
        rw [Finset.mem_singleton]
        rintro rfl
        obtain ⟨v, hv⟩ := hwt.2
        exact absurd (hact.symm.trans hv) (by simp)
    exact ⟨c.addRead e w, StepL.read hcc hnext hact hwt' (hdec ▸ hXc), hdec⟩
  · obtain ⟨wp, hwp, hco⟩ := Graph.remove_addWrite_co hXW he hw
    have hdec : (c.addWrite e wp).abs = X := by
      rw [Config.addWrite_abs, habs]
      apply Graph.ext
      · rfl
      · exact Graph.remove_singleton_insert he
      · funext q
        rw [Graph.addWrite_rf]
        by_cases hqe : q = e
        · rw [hqe, hXW.rf_none e (Or.inr hw.not_isRead)]
          exact X.restrict_rf_of_not_mem (by simp)
        · exact Graph.remove_singleton_rf hXW hqe (hsink q)
      · exact hco
      · exact Graph.remove_singleton_pol hXW (fun h => h.isLocal.not_isWrite hw)
    exact ⟨c.addWrite e wp, StepL.write hcc hnext hw (habs ▸ hwp) (hdec ▸ hXc), hdec⟩
  · have hdec : (c.addLoc e (X.pol e)).abs = X := by
      rw [Config.addLoc_abs, habs]
      exact Graph.remove_addLoc hXW he hk hsink
    by_cases hcs : e.IsCons
    · obtain ⟨b, hb⟩ := hXW.exists_pol he hcs
      rw [hb] at hdec
      exact ⟨_, StepL.sym hcc hnext hcs (hdec ▸ hXc), hdec⟩
    · have hb : X.pol e = none := by
        by_contra h
        obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h
        exact hcs (hXW.pol_some hb).2
      rw [hb] at hdec
      exact ⟨_, StepL.loc hcc hnext hk hcs (hdec ▸ hXc), hdec⟩

/-- Proposition A.28, the case of a revisit step. -/
theorem Reach.step_of_prevStep_rvX {Gf X : Graph} {c : Config} {a e : TEv}
    (hM : ExtensibleX P M) (hGf : Gf.Wf) (hEf : P.toProgram.Exec Gf)
    (hcf : (M.sym S).cons Gf) (hff : P.toProgram.Full Gf)
    (hX : PrevReach P.toProgram τ Gf X) (hc : Reach P.toProgram (M.sym S) τ c)
    (hs : PrevStep P.toProgram τ X e (.rv a) c.abs) :
    ∃ c', StepL P.toProgram (M.sym S) τ c e (.rv a) c' ∧ c'.abs = X := by
  obtain ⟨hXW, hXE, hXc, -, hS1⟩ := PrevReach.invX hM hGf hEf hcf hff hX
  obtain ⟨hcW, hcpo, hcc, -⟩ := hc.sound
  have D : RvData' P.toProgram τ X c a e :=
    ⟨hXW, hXE, (M.sym S).porf_acyclic X hXW hXc, hS1, hcW, hcpo, hc.inv,
      fun hbw hpo => hc.bw_po_lt hbw hpo, hs⟩
  obtain ⟨wp, h1, h2, h3, h4, h5, h6, h7, habs⟩ := D.step
  exact ⟨c.revisit a e wp, StepL.revisit hcc h1 h2 h3 h4 h5 h6 h7 (habs ▸ hXc), habs⟩

/-- Proposition A.28: a backward step into the graph of a reached
configuration is matched by a step of Algorithm 1 from that configuration,
with the same event and kind. -/
theorem Reach.step_of_prevStepX {Gf X : Graph} {c : Config} {e : TEv} {k : Kind}
    (hM : ExtensibleX P M) (hGf : Gf.Wf) (hEf : P.toProgram.Exec Gf)
    (hcf : (M.sym S).cons Gf) (hff : P.toProgram.Full Gf)
    (hX : PrevReach P.toProgram τ Gf X) (hc : Reach P.toProgram (M.sym S) τ c)
    (hs : PrevStep P.toProgram τ X e k c.abs) :
    ∃ c', StepL P.toProgram (M.sym S) τ c e k c' ∧ c'.abs = X := by
  cases k with
  | nr => exact Reach.step_of_prevStep_nrX hM hGf hEf hcf hff hX hc hs
  | rv a => exact Reach.step_of_prevStep_rvX hM hGf hEf hcf hff hX hc hs

/-- Lemma A.29: a graph of the backward chain from `G_f` from which the
backward steps reach the graph without thread events is the graph of a
reached configuration. -/
theorem PrevReach.reachX {Gf X : Graph} (hM : ExtensibleX P M) (hGf : Gf.Wf)
    (hEf : P.toProgram.Exec Gf) (hcf : (M.sym S).cons Gf) (hff : P.toProgram.Full Gf)
    (hX : PrevReach P.toProgram τ Gf X)
    (h0 : Relation.ReflTransGen (fun G G' => ∃ e k, PrevStep P.toProgram τ G e k G') X
      (Graph.init P.mem)) :
    ∃ c, Reach P.toProgram (M.sym S) τ c ∧ c.abs = X := by
  revert hX
  induction h0 using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro _
    exact ⟨Config.init P.mem, Relation.ReflTransGen.refl, Config.init_abs _⟩
  | head hs _ ih =>
    intro hX
    obtain ⟨e, k, hs⟩ := hs
    obtain ⟨c, hc, habs⟩ := ih (hX.tail ⟨e, k, hs⟩)
    rw [← habs] at hs
    obtain ⟨c', hst, h'⟩ := Reach.step_of_prevStepX hM hGf hEf hcf hff hX hc hs
    exact ⟨c', hc.tail ⟨e, k, hst⟩, h'⟩

/-- Theorem A.30 (completeness; Theorem 4 of ConDpor) with read-modify-write
accesses: Algorithm 1 reaches every well-formed, consistent, full execution of
a bounded program, for a model with `ExtensibleX`. -/
theorem Rmw.complete {n : ℕ} (hn : P.toProgram.Bounded n) (hM : ExtensibleX P M) {Gf : Graph}
    (hGf : Gf.Wf) (hEf : P.toProgram.Exec Gf) (hcf : (M.sym S).cons Gf)
    (hff : P.toProgram.Full Gf) :
    ∃ c, Reach P.toProgram (M.sym S) τ c ∧ c.abs = Gf :=
  PrevReach.reachX hM hGf hEf hcf hff Relation.ReflTransGen.refl
    (PrevReach.initX hn hM hGf hEf hcf hff)

/-- Completeness for `SC` with atomicity. -/
theorem Rmw.complete_sc {n : ℕ} (hn : P.toProgram.Bounded n) {Gf : Graph}
    (hGf : Gf.Wf) (hEf : P.toProgram.Exec Gf) (hcf : ((Model.atomic P SC).sym S).cons Gf)
    (hff : P.toProgram.Full Gf) :
    ∃ c, Reach P.toProgram ((Model.atomic P SC).sym S) τ c ∧ c.abs = Gf :=
  Rmw.complete hn (SC.extensibleX P) hGf hEf hcf hff

end Condpor
