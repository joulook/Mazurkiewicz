import Mazurkiewicz.Condpor.Rmw.LifecycleGate3Fwd

/-!
# Gate clause 3 (LC2-c)

**`gate3 : Gate3`**: for a fragment program, two maximal runs have the same graph iff they
are Mazurkiewicz-equivalent.

* ⇐ is `gate3_bwd` (`LifecycleGate3Bwd.lean`): Levi's lemma moves the first occurrence of one
  run to the front of the other through runs only (`commute` on states, `emit_comm` on
  builders, the fragment for the injectivity of resources to locations).
* ⇒ is `gate3_fwd`: `fwd_core` (`LifecycleGate3Fwd.lean`) with the simulation invariant of gate
  clause 1 at an adequate bound (`Gate3` has none; the machine does not depend on it, the bound
  `adequateBound P` is only used for the invariant).
-/

namespace Condpor

namespace Life

namespace Sem

/-- An adequate bound for every thread of `P`. -/
def adequateBound (P : LProg) : ℕ := (P.threads.map (fun t => 2 * (P.code t).length + 3)).sum

theorem adequateB_adequateBound (P : LProg) : adequateB P (adequateBound P) = true := by
  unfold adequateB adequateBound
  rw [List.all_eq_true]
  intro t ht
  rw [decide_eq_true_eq]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨t, ht, rfl⟩)

/-- **Gate clause 3, direction ⇒**: maximal runs with the same graph are equivalent. -/
theorem gate3_fwd {P : LProg} (hf : fragB P = true) {rs₁ rs₂ : List Occ} {s₁ s₂ : MState}
    (h₁ : MaxRun P rs₁ s₁) (h₂ : MaxRun P rs₂ s₂)
    (he : (runCfg P rs₁ s₁).abs = (runCfg P rs₂ s₂).abs) : MEquiv rs₁ rs₂ := by
  have hF := frag_of_fragB hf
  exact fwd_core hF (adequateB_adequateBound P) rs₁ _ GB.empty (sinv_init hF _) s₁ rs₂ s₂
    h₁.1 h₁.2 h₂.1 h₂.2 he

/-- **Gate clause 3.** -/
theorem gate3 : Gate3 := by
  intro P hf rs₁ s₁ rs₂ s₂ h₁ h₂
  exact ⟨gate3_fwd hf h₁ h₂, gate3_bwd hf h₁ h₂⟩

end Sem

end Life

end Condpor
