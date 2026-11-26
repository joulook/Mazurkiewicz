import Mazurkiewicz.Induction.MP.Steps

/-!
# Message passing: more on steps (follow-up of the C0-C1b reviews)

`induction-popl`, `prelim.tex` def:step, prop:reach-exec (plan `plan/ind/TRACK-C-PLAN.md`,
milestone C1a; Opus review of C0-C1b).

* `preach_iff`: reachability by chains of def:step steps (`PStep`) from the empty graph is
  `MReach` (operational reachability), hence `Exec_M(P)` (`mreach_iff`).
* `ExecM.of_opStepG`: an operational step from a consistent execution gives a consistent
  execution with the old graph as a prefix.
-/

namespace Must

namespace Ind

open Graph Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q]
variable {M : Model Q} {P : Program Q} {G G' : Graph Q}

/-- An operational step from a consistent execution gives a consistent execution of which the
old graph is a prefix. -/
theorem ExecM.of_opStepG (hG : ExecM M P G) (h : OpStepG M P G G') :
    ExecM M P G' ∧ G.IsPrefixOf G' := by
  obtain ⟨e, src, out, hop, rfl⟩ := h
  have hw := M.wf _ hG.2
  obtain ⟨t, ht⟩ := hop.nextEv
  exact ⟨⟨P.exec_add hG.1 hw ht src out, hop.2.2⟩, hw.isPrefixOf_add (Model.idx_of_nextEv ht)⟩

/-- def:step, prop:reach-exec: the graphs reached from the empty graph by chains of `PStep`
are the reachable graphs `MReach`. -/
theorem preach_iff : ReflTransGen (PStep M P) Graph.empty G ↔ MReach M P G := by
  constructor
  · intro h
    induction h with
    | refl => exact ReflTransGen.refl
    | tail _ hs ih => exact ih.tail ((pstep_iff (mreach_iff.mp ih)).mp hs)
  · intro h
    induction h with
    | refl => exact ReflTransGen.refl
    | @tail G₁ G₂ h₁ hs ih => exact ih.tail ((pstep_iff (mreach_iff.mp h₁)).mpr hs)

end Ind

end Must
