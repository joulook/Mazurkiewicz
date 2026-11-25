import Mazurkiewicz.Condpor.Rmw.LifecycleGate2

/-!
# Gate clause 2, part 1: linearizations (LC2-b, continuation 2)

`g2Lin : G2Lin`: a well-formed SC-consistent graph has a linearization of its events along
which every `po ∪ rf ∪ co ∪ fr` edge goes forward. Built by removing a maximal element of the
transitive closure, the one with the most predecessors.
-/

namespace Condpor

namespace Life

namespace Sem

open Relation

theorem scStep_mem {G : Graph} (hG : G.Wf) {a b : TEv} (h : G.scStep (.th a) (.th b)) :
    a ∈ G.events ∧ b ∈ G.events := by
  rcases h with h | h | h | h
  · exact ⟨h.1, h.2.1⟩
  · obtain ⟨e, he, hm, hr⟩ := h
    cases he
    obtain ⟨w, hw, hwt⟩ := hG.rf_read b hm _ (TEv.IsRead.exists_act (by
      by_contra hn; rw [hG.rf_none b (Or.inr hn)] at hr; cases hr))
    rw [hr] at hw; cases hw
    exact ⟨hwt.1, hm⟩
  · obtain ⟨x, hx⟩ := h
    exact ⟨((hG.co_mem x a).mp hx.1).1, ((hG.co_mem x b).mp hx.2.1).1⟩
  · obtain ⟨e, e', x, he, he', hm, -, hco, -⟩ := h
    cases he; cases he'
    exact ⟨hm, ((hG.co_mem x _).mp hco).1⟩

theorem lin_finset {G : Graph} (hac : SC.cons G) :
    ∀ S : Finset TEv, ∃ L : List TEv, L.Nodup ∧ (∀ e, e ∈ L ↔ e ∈ S) ∧
      ∀ a ∈ S, ∀ b ∈ S, TransGen G.scStep (.th a) (.th b) → L.Before a b := by
  classical
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hS : S = ∅
    · subst hS; exact ⟨[], by simp, by simp, by simp⟩
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    -- the element with the most predecessors in `S` has no successor in `S`
    let c := fun e => (S.filter (fun a => TransGen G.scStep (.th a) (.th e))).card
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image S c ⟨x, hx⟩
    have hnosucc : ∀ b ∈ S, ¬ TransGen G.scStep (.th m) (.th b) := by
      intro b hb hmb
      have hsub : S.filter (fun a => TransGen G.scStep (.th a) (.th m)) ⊂
          S.filter (fun a => TransGen G.scStep (.th a) (.th b)) := by
        refine Finset.ssubset_iff_of_subset (fun a ha => ?_) |>.mpr ⟨m, ?_, ?_⟩
        · simp only [Finset.mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.trans hmb⟩
        · simp [hm, hmb]
        · simp only [Finset.mem_filter, not_and]; exact fun _ h => hac _ h
      have h1 := Finset.card_lt_card hsub
      have h2 : c b ≤ c m := hmax b hb
      simp only [c] at h2
      omega
    obtain ⟨L, hn, hmem, hord⟩ := ih (S.erase m) (Finset.erase_ssubset hm)
    have hmL : m ∉ L := fun h => by simpa using (hmem m).mp h
    refine ⟨L ++ [m], List.nodup_append.mpr ⟨hn, List.nodup_singleton _, ?_⟩, ?_, ?_⟩
    · intro a ha b hb; rw [List.mem_singleton] at hb; subst hb; exact fun h => hmL (h ▸ ha)
    · intro e
      rw [List.mem_append, hmem, List.mem_singleton, Finset.mem_erase]
      constructor
      · rintro (⟨-, h⟩ | rfl); exacts [h, hm]
      · intro h; by_cases he : e = m
        · exact Or.inr he
        · exact Or.inl ⟨he, h⟩
    · intro a ha b hb hab
      rw [List.before_append_singleton_iff hmL]
      by_cases hbm : b = m
      · subst hbm
        have ham : a ≠ b := fun h => by subst h; exact hac _ hab
        exact Or.inr ⟨(hmem a).mpr (Finset.mem_erase.mpr ⟨ham, ha⟩), rfl⟩
      · have ham : a ≠ m := fun h => by subst h; exact hnosucc b hb hab
        exact Or.inl (hord a (Finset.mem_erase.mpr ⟨ham, ha⟩) b
          (Finset.mem_erase.mpr ⟨hbm, hb⟩) hab)

/-- **Gate clause 2, part 1.** -/
theorem g2Lin : G2Lin := by
  intro G hG hac
  obtain ⟨L, hn, hmem, hord⟩ := lin_finset hac G.events
  refine ⟨L, hn, hmem, fun a b h => ?_⟩
  obtain ⟨ha, hb⟩ := scStep_mem hG h
  exact hord a ha b hb (TransGen.single h)

end Sem

end Life

end Condpor
