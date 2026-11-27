import Mazurkiewicz.Condpor.Rmw.LifecycleGateStep

/-!
# Gate clause 1: the simulation invariant is preserved by steps (LC2-b, part 8)

`SInv.step`: a step preserves `SInv` (fragment program, adequate bound).
`SInv.steps`: so does a run from the initial state.
-/

namespace Condpor

namespace Life

namespace Sem

variable {P : LProg} {n : ℕ} {s : MState} {g : GB}

/-- What a step does not change for another thread. -/
theorem eff_other {o : Occ} (he : Enabled P s o) {t : Tid} (ht : t ≠ o.tid) :
    (eff s o).status t = s.status t ∧ (eff s o).rest t = s.rest t ∧
      holdsM (eff s o) t = holdsM s t ∧ (∀ l, (eff s o).owner l = some t → s.owner l = some t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases he <;> simp only [Occ.tid] at ht <;>
      simp [eff, MState.adv, MState.setSt, ht]
  · cases he <;> simp only [Occ.tid] at ht <;>
      simp [eff, MState.adv, MState.setSt, ht]
  · funext l
    cases he <;> simp only [Occ.tid] at ht <;>
      simp only [holdsM, eff, MState.adv, MState.setSt, Function.update_apply] <;>
      split_ifs <;> simp_all [heldB_eq_true, heldB_eq_false]
  · intro l h
    cases he <;> simp only [Occ.tid] at ht <;>
      simp only [eff, MState.adv, MState.setSt, Function.update_apply] at h <;>
      (try split_ifs at h) <;> simp_all

/-- A step shortens the remaining calls. -/
theorem rest_suffix {o : Occ} (he : Enabled P s o) (t : Tid) : (eff s o).rest t <:+ s.rest t := by
  cases he <;> simp only [eff, MState.adv, MState.setSt, Function.update_apply] <;>
    (try split_ifs) <;> subst_vars <;>
    first
    | exact List.suffix_refl _
    | exact List.tail_suffix _
    | exact (List.drop_suffix _ _).trans (List.tail_suffix _)

theorem started_eff {o : Occ} (he : Enabled P s o) {u : Tid} (h : (eff s o).started u = true) :
    s.started u = true ∨ ∃ t0, o = .start t0 u := by
  cases he <;> simp only [eff, MState.adv, MState.setSt, Function.update_apply] at h <;>
    (try split_ifs at h) <;> subst_vars <;> simp_all

theorem trel_other {o : Occ} (he : Enabled P s o) {t : Tid} (ht : t ≠ o.tid)
    {u : List (Option Val)} (h : TRel P s t u) : TRel P (eff s o) t u := by
  obtain ⟨h1, h2, h3, h4⟩ := eff_other he ht
  unfold TRel at h ⊢
  rw [h1, h2, h3]
  cases hs : s.status t <;> simp only [hs] at h ⊢
  · exact ⟨h.1, h.2.1, fun l hl => h.2.2 l (h4 l hl)⟩
  all_goals exact h

/-- **A step preserves the simulation invariant.** -/
theorem SInv.step (hF : Frag P) (hn : adequateB P n = true) (hI : SInv P n s g) {o : Occ}
    {s' : MState} (h : Step P s o s') : SInv P n s' (emit P g o) := by
  obtain ⟨he, rfl⟩ := h
  obtain ⟨hex, htr, hrel⟩ := hI.thread hF hn he
  have hoT : o.tid ∈ P.threads := enabled_tid_mem he
  refine ⟨emit_ok P hI.ok o, hI.minv.step hF ⟨he, rfl⟩, hex, ?_, ?_,
    Step.lockInv ⟨he, rfl⟩ hI.lockInv, ?_, ?_, ?_, ?_⟩
  · -- noStart
    intro u t ht hsu hru hm
    have hsub := (rest_suffix he t).subset hm
    rcases started_eff he hsu with hs0 | ⟨t0, rfl⟩
    · exact hI.noStart u t ht hs0 hru hsub
    · -- the start just executed
      cases he with
      | start ht0 hs0 hc0 =>
        have hc := rest_cons hc0
        by_cases htt : t = t0
        · subst htt
          have h1 : (P.code t).count (.start u) ≤ 1 := hF.one_start u (by
            have := callOk_head hF hI ht hc0
            simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at this
            exact this.1.1) t ht
          have h2 := (hI.minv.suffix t).sublist.count_le (TOp.start u)
          rw [hc, List.count_cons_self] at h2
          have h3 : (s.rest t).tail.count (.start u) = 0 := by omega
          have : (eff s (.start t u)).rest t = (s.rest t).tail := by simp [eff, MState.adv]
          rw [this] at hm
          exact absurd (List.count_pos_iff.mpr hm) (by omega)
        · have hu : u ∈ P.threads := by
            have := callOk_head hF hI ht0 hc0
            simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at this
            exact this.1.1
          have hin0 : TOp.start u ∈ P.code t0 := hI.minv.head_mem hc0
          have hin : TOp.start u ∈ P.code t := (hI.minv.suffix t).subset hsub
          exact htt (hF.one_starter u hu t ht t0 ht0 hin hin0)
  · -- newRoot
    intro t hr hnew
    apply hI.newRoot t hr
    cases he <;> simp only [eff, MState.adv, MState.setSt, Function.update_apply] at hnew <;>
      (try split_ifs at hnew) <;> simp_all
  · -- vData
    intro x hx
    rw [last_emit, hI.vData x hx]
    have hxl : P.isLock x = false := by
      simp only [LProg.isData, Bool.and_eq_true, Bool.not_eq_true'] at hx; exact hx.1
    have hxs : P.isSt x = false := by
      simp only [LProg.isData, Bool.and_eq_true, Bool.not_eq_true'] at hx; exact hx.2
    have hlk : ∀ l, P.isLock l = true → l ≠ x := fun l hl h => by rw [h, hxl] at hl; cases hl
    have hst : ∀ u ∈ P.threads, P.st u ≠ x := fun u hu h => by
      rw [← h, hF.isSt_st hu] at hxs; cases hxs
    cases he
    case acq t l ht hs hc hh hf =>
      have := hlk l (by simpa [callOk] using callOk_head hF hI ht hc)
      simp [writeLoc, eff, MState.adv, this]
    case tryAcq t l k ht hs hc hh hf =>
      have := hlk l (by simpa [callOk] using callOk_head hF hI ht hc)
      simp [writeLoc, eff, MState.adv, this]
    case release t l ht hs hc hh h1 =>
      have := hlk l (by simpa [callOk] using callOk_head hF hI ht hc)
      simp [writeLoc, eff, MState.adv, this]
    case wr t y v ht hs hc =>
      by_cases hy : y = x
      · subst hy; simp [writeLoc, writeVal, eff, MState.adv]
      · simp [writeLoc, eff, MState.adv, hy, Ne.symm hy]
    case start t u ht hs hc =>
      have hu : u ∈ P.threads := by
        have := callOk_head hF hI ht hc
        simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.1.1
      simp [writeLoc, eff, MState.adv, hst u hu]
    case fin t ht hs hc => simp [writeLoc, eff, MState.setSt, hst t ht]
    all_goals simp [writeLoc, eff, MState.adv, MState.setSt]
  · -- vLock
    intro l hl
    rw [last_emit, hI.vLock l hl]
    have hst : ∀ u ∈ P.threads, P.st u ≠ l := fun u hu h => by
      rw [← h, hF.st_not_lock u hu] at hl; cases hl
    cases he
    case acq t l0 ht hs hc hh hf =>
      by_cases h0 : l0 = l
      · subst h0; simp [writeLoc, writeVal, eff, MState.adv]
      · simp [writeLoc, eff, MState.adv, h0, Ne.symm h0]
    case tryAcq t l0 k ht hs hc hh hf =>
      by_cases h0 : l0 = l
      · subst h0; simp [writeLoc, writeVal, eff, MState.adv]
      · simp [writeLoc, eff, MState.adv, h0, Ne.symm h0]
    case release t l0 ht hs hc hh h1 =>
      by_cases h0 : l0 = l
      · subst h0; simp [writeLoc, writeVal, eff, MState.adv]
      · simp [writeLoc, eff, MState.adv, h0, Ne.symm h0]
    case reacq t l0 ht hs hc hh =>
      have hp := (heldB_eq_true.mp hh).2
      by_cases h0 : l0 = l
      · subst h0; simp [writeLoc, eff, MState.adv]; omega
      · simp [writeLoc, eff, MState.adv, Ne.symm h0]
    case tryRe t l0 k ht hs hc hh =>
      have hp := (heldB_eq_true.mp hh).2
      by_cases h0 : l0 = l
      · subst h0; simp [writeLoc, eff, MState.adv]; omega
      · simp [writeLoc, eff, MState.adv, Ne.symm h0]
    case unlockRe t l0 ht hs hc hh h1 =>
      by_cases h0 : l0 = l
      · subst h0
        have e1 : s.count l0 ≠ 0 := by omega
        have e2 : s.count l0 - 1 ≠ 0 := by omega
        simp [writeLoc, eff, MState.adv, e1, e2]
      · simp [writeLoc, eff, MState.adv, Ne.symm h0]
    case wr t y v ht hs hc =>
      have hy : P.isData y = true := by simpa [callOk] using callOk_head hF hI ht hc
      have : y ≠ l := fun h => by
        rw [h] at hy; simp [LProg.isData, hl] at hy
      simp [writeLoc, eff, MState.adv, this]; rfl
    case start t u ht hs hc =>
      have hu : u ∈ P.threads := by
        have := callOk_head hF hI ht hc
        simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.1.1
      simp [writeLoc, eff, MState.adv, hst u hu]; rfl
    case fin t ht hs hc => simp [writeLoc, eff, MState.setSt, hst t ht]; rfl
    all_goals simp [writeLoc, eff, MState.adv, MState.setSt] <;> rfl
  · -- vLife
    intro t ht
    rw [last_emit, hI.vLife t ht]
    have hnl : P.isLock (P.st t) = false := hF.st_not_lock t ht
    have hns : ∀ x, P.isData x = true → x ≠ P.st t := fun x hx h => by
      rw [h, hF.isData_st ht] at hx; cases hx
    cases he
    case begin t0 ht0 hs0 h0 =>
      by_cases h : t0 = t
      · subst h; simp [writeLoc, eff, MState.setSt, hs0, h0]
      · simp [writeLoc, eff, MState.setSt, Ne.symm h]
    case unlockErr t0 l ht0 hs0 hc hh =>
      by_cases h : t0 = t
      · subst h; simp [writeLoc, eff, MState.setSt, hs0, hI.minv.started_of t0 (by simp [hs0])]
      · simp [writeLoc, eff, MState.setSt, Ne.symm h]
    case asmStop t0 x v ht0 hs0 hc hv =>
      by_cases h : t0 = t
      · subst h; simp [writeLoc, eff, MState.setSt, hs0, hI.minv.started_of t0 (by simp [hs0])]
      · simp [writeLoc, eff, MState.setSt, Ne.symm h]
    case fin t0 ht0 hs0 hc =>
      by_cases h : t0 = t
      · subst h; simp [writeLoc, writeVal, eff, MState.setSt,
          hI.minv.started_of t0 (by simp [hs0])]
      · have : P.st t0 ≠ P.st t := fun h' => h (hF.st_inj t0 ht0 t ht h')
        simp [writeLoc, eff, MState.setSt, Ne.symm h, this]
    case start t0 u ht0 hs0 hc =>
      have hu : u ∈ P.threads ∧ P.isRoot u = false := by
        have := callOk_head hF hI ht0 hc
        simp only [callOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at this
        exact ⟨this.1.1, this.1.2⟩
      by_cases h : u = t
      · subst h
        have hns0 : s.started u = false := by
          cases hsu : s.started u
          · rfl
          · exact absurd (hI.minv.head_mem hc) (fun hm => hI.noStart u t0 ht0 hsu hu.2
              ((List.mem_of_mem_head? hc)))
        have hnew : s.status u = .new := by
          by_contra hne; rw [hI.minv.started_of u hne] at hns0; cases hns0
        simp [writeLoc, writeVal, eff, MState.adv, hnew]
      · have : P.st u ≠ P.st t := fun h' => h (hF.st_inj u hu.1 t ht h')
        simp [writeLoc, eff, MState.adv, Ne.symm h, this]; rfl
    case acq t0 l ht0 hs0 hc hh hf =>
      have hl : P.isLock l = true := by simpa [callOk] using callOk_head hF hI ht0 hc
      have : l ≠ P.st t := fun h => by rw [h, hnl] at hl; cases hl
      simp [writeLoc, eff, MState.adv, this]; rfl
    case tryAcq t0 l k ht0 hs0 hc hh hf =>
      have hl : P.isLock l = true := by simpa [callOk] using callOk_head hF hI ht0 hc
      have : l ≠ P.st t := fun h => by rw [h, hnl] at hl; cases hl
      simp [writeLoc, eff, MState.adv, this]; rfl
    case release t0 l ht0 hs0 hc hh h1 =>
      have hl : P.isLock l = true := by simpa [callOk] using callOk_head hF hI ht0 hc
      have : l ≠ P.st t := fun h => by rw [h, hnl] at hl; cases hl
      simp [writeLoc, eff, MState.adv, this]; rfl
    case wr t0 x v ht0 hs0 hc =>
      have := hns x (by simpa [callOk] using callOk_head hF hI ht0 hc)
      simp [writeLoc, eff, MState.adv, this]; rfl
    all_goals simp [writeLoc, eff, MState.adv] <;> rfl
  · -- rel
    intro t ht
    by_cases hto : t = o.tid
    · subst hto; exact hrel
    · rw [htr t hto]; exact trel_other he hto (hI.rel t ht)

end Sem

end Life

end Condpor
