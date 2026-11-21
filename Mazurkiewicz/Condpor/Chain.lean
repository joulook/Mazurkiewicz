import Mazurkiewicz.Condpor.Variants

/-!
# Maximal addition as a chain

The paper states the test of a backward revisit as a chain: there are graphs
with `G' →r G'' →d₁ ⋯ →dₙ G|E∖{a}`, where `d₁, …, dₙ` are the deleted events
in the order of their insertion and each step adds its event in the maximal
way. `Alg.lean` states the test event by event (`IsMaximallyAdded`, over
`Previous`), as TruSt does. The two forms are related as follows.

* `MaxCompl P p G₀ a G` is the chain: starting from `G₀`, the next event is
  added in the maximal way (`Graph.addMax`: a read from the last write, a
  write placed last, a constraint evaluation with the outcome `p` chooses)
  until the next event is `a`, and the result is `G`. It is a relation between
  graphs: the insertion order plays no role. (With the insertion order the
  printed equality cannot hold: the chain adds `r` after the kept events that
  were added after `r`.)
* `revisit_chain`: if the algorithm takes a revisit step of `r` by `a` from a
  reached configuration `c` to `c'`, then the chain exists: from the graph of
  `c'` without `r` and `a` (the kept events without `r`: the paper's `G'`),
  with the choice of outcomes for the context of the kept events, the chain
  ends in the graph of `c` (the paper's `G|E∖{a}`: `c` is the configuration
  before `a` is added).
* A converse is `Reach.step_of_prevStep_rv` (in `Complete.lean`): a backward
  revisit step `PrevStep P τ X a (.rv r) c.abs` into the graph of a reached
  configuration `c`, from a graph `X` on the backward path from a full
  execution, is matched by a revisit step of the algorithm from `c` with
  result `X`. Its premise is the whole backward step, of which the chain is
  one component (the others: `r` is the `<next`-maximal event of `X`, it
  reads from `a`, `r <next a`, and `r` is the only causal successor of `a`).
  The converse is not proved from the chain alone, nor for an arbitrary `X`.
-/

namespace Condpor

open Program

variable {P : Program} {M : Model} {S : Solver} {τ : TieBreak S}

/-- A revisit step that the algorithm takes has the paper's chain of maximal
additions. -/
theorem revisit_chain {c c' : Config} {a r : TEv} (hc : Reach P (M.sym S) τ c)
    (hs : StepL P (M.sym S) τ c a (.rv r) c') :
    MaxCompl P (τ.pref (c'.abs.remove {r, a}).F) (c'.abs.remove {r, a}) a c.abs :=
  (hc.prevStep_of_step_rv hs).rv_inv.2.2.2.2.2

/-- The context of the chain is the context of the test: the literals of the
events that the revisit keeps. -/
theorem revisit_chain_ctx {c c' : Config} {a r : TEv}
    (hs : StepL P (M.sym S) τ c a (.rv r) c') : c'.abs.F = c.ctx r a := by
  obtain ⟨wp, rfl, -, -, hw, -⟩ := hs.rv_inv
  exact Config.revisit_F c r wp hw

end Condpor
