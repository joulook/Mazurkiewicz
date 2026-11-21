import Mazurkiewicz.Condpor.GetNext
import Mazurkiewicz.Condpor.Variants

/-!
# The prefix order as printed is too small

The paper defines `G₁ ⊑ G₂` by "a series of non-revisit steps" of the
algorithm (`NrLe`). For `r := x ‖ x := 1`, reader first, the execution in
which the read reads from the write is not above the initial graph in that
order: the first non-revisit step adds the read with source `init`. So
"calling `GetNext` in a fixpoint" from the initial graph needs the prefix
order (`IsPrefixOf`, equivalently operational steps: `opLe_iff_isPrefixOf`),
for which the initial graph is below every execution.
-/

namespace Condpor

open Program

theorem rwProg_trace_init (t : Tid) : (Graph.init rwProg.mem).trace t = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [Graph.trace_length]
  simp [Graph.cnt, Graph.init]

theorem rwProg_avail_init {e : TEv} (he : e ∈ rwProg.avail (Graph.init rwProg.mem)) :
    e = ⟨0, 0, .read 0⟩ ∨ e = ⟨1, 0, .write 0 1⟩ := by
  obtain ⟨ht, hi, hs⟩ := mem_avail_iff.mp he
  rw [rwProg_trace_init] at hs
  have hi' : e.idx = 0 := by rw [hi]; simp [Graph.cnt, Graph.init]
  obtain ⟨t, i, a⟩ := e
  simp only at ht hi' hs
  subst hi'
  have ht' : t = 0 ∨ t = 1 := by simpa [rwProg, mkProg] using ht
  rcases ht' with rfl | rfl
  · left
    have : rwProg.step 0 [] = some (.read 0) := by decide
    rw [this] at hs
    cases hs
    rfl
  · right
    have : rwProg.step 1 [] = some (.write 0 1) := by decide
    rw [this] at hs
    cases hs
    rfl

theorem rwProg_read_avail : (⟨0, 0, .read 0⟩ : TEv) ∈ rwProg.avail (Graph.init rwProg.mem) := by
  refine mem_avail_iff.mpr ⟨by decide, by simp [Graph.cnt, Graph.init], ?_⟩
  rw [rwProg_trace_init]
  decide

/-- An execution of `⟦P⟧` that is not above the initial graph in the printed
order. -/
theorem nrLe_fails : ∃ Gt : Graph, Gt.Wf ∧ rwProg.Exec Gt ∧
    (SC.sym EqSem.solver).cons Gt ∧ rwProg.Full Gt ∧
    (Graph.init rwProg.mem).IsPrefixOf Gt ∧
    ¬ NrLe rwProg (SC.sym EqSem.solver) (TieBreak.se EqSem.solver) (Graph.init rwProg.mem) Gt := by
  obtain ⟨G, hG, hrf⟩ := List.any_eq_true.mp n0_lost.1
  have hrf' : G.rf ⟨0, 0, .read 0⟩ = some (.th ⟨1, 0, .write 0 1⟩) := by simpa using hrf
  obtain ⟨hW, hE, hc, hF⟩ :=
    ((exploreC_spec eqOracleSe (mkProg_bounded _ _ _ _ _)).2 G).mp hG
  refine ⟨G, hW, hE, hc, hF, ?_, ?_⟩
  · have hmem : rwProg.mem = G.mem := hE.1.symm
    rw [hmem]
    exact Graph.init_isPrefixOf G
  rintro ⟨c, c', hc0, rfl, hsteps⟩
  rcases Relation.ReflTransGen.cases_head hsteps with rfl | ⟨c1, ⟨e, hs⟩, hrest⟩
  · rw [hc0] at hrf'
    cases hrf'
  · have hW0 : c.abs.Wf := hc0 ▸ Graph.init_wf _
    obtain ⟨-, hnext, hcase⟩ := hs.nr_inv
    rw [hc0] at hnext
    have he : e = ⟨0, 0, .read 0⟩ := by
      rcases rwProg_avail_init hnext.1 with h | h
      · exact h
      · exfalso
        have := hnext.2 _ rwProg_read_avail (by rw [h]; decide)
        rw [h] at this
        simp [nextLt] at this
    subst he
    have hop := hs.opStep hW0
    have hpre : c1.abs.IsPrefixOf c'.abs :=
      ((NrLe.opLe hop.1 ⟨c1, c', rfl, rfl, hrest⟩).isPrefixOf hop.1).1
    have hc1 : c1.abs.rf ⟨0, 0, .read 0⟩ = some .init := by
      rcases hcase with ⟨x, w, -, hw, rfl⟩ | ⟨wp, hact, -, -⟩ | ⟨b, hact, -⟩ | ⟨hl, -, -⟩
      · rw [Config.addRead_abs, Graph.addRead_rf, Function.update_self]
        cases w with
        | init => rfl
        | th q =>
          rw [hc0] at hw
          exact absurd hw.1 (by simp [Graph.init])
      · exact absurd hact (by simp [TEv.IsWrite, Act.IsWrite])
      · exact absurd hact (by simp [TEv.IsCons, Act.IsCons])
      · exact absurd hl (by simp [TEv.IsLocal, Act.IsLocal])
    obtain ⟨s, -, hY⟩ := hpre
    rw [hY] at hc1
    have := (c'.abs.restrict_rf_eq_some hc1).1
    rw [hrf'] at this
    cases this

end Condpor
