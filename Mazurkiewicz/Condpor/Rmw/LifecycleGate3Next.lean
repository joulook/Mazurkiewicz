import Mazurkiewicz.Condpor.Rmw.LifecycleGate3Ord

/-!
# Gate clause 3, part 5: the next occurrence of a thread is fixed by its state and one value

* `dloc P s t`: the location whose last written value decides the outcome of the next call
  of `t` (a `lock`/`tryLock` of a lock `t` does not hold, an `assume`, a `join`); none for the
  calls whose outcome the thread's own state decides.
* `first_read`: in those cases the next occurrence begins with a read of that location.
* **`next_same`**: if another state agrees with `s` on the status, the remaining calls and the
  hold counts of `t`, keeps its started flag, and the last value of `dloc P s t` agrees (both
  states with the simulation invariant `SInv`), then the next occurrence of `t` is the same.
-/

namespace Condpor

namespace Life

namespace Sem

variable {P : LProg} {n : ℕ} {s s' : MState} {g g' : GB}

/-- The deciding location of the next call of `t`. -/
def dloc (P : LProg) (s : MState) (t : Tid) : Option Loc :=
  match s.status t with
  | .running =>
    match (s.rest t).head? with
    | some (.lock l) => if holdsM s t l = 0 then some l else none
    | some (.tryLock l _) => if holdsM s t l = 0 then some l else none
    | some (.assume x _) => some x
    | some (.join u) => some (P.st u)
    | _ => none
  | _ => none

theorem first_read {t : Tid} {a : Occ} {x : Loc} (ha : next P s t = some a)
    (hd : dloc P s t = some x) : ∃ ps, prims P a = .rd t x :: ps := by
  unfold next at ha
  unfold dloc at hd
  cases hs : s.status t <;> simp only [hs, reduceCtorEq] at ha hd
  cases hh : (s.rest t).head? with
  | none => simp [hh] at hd
  | some c =>
    have lk : ∀ l, (if holdsM s t l = 0 then some l else none) = some x → s.heldB t l = false ∧
        l = x := by
      intro l h
      split_ifs at h with h0
      · obtain rfl := Option.some.inj h
        refine ⟨?_, rfl⟩
        cases hb : s.heldB t l
        · rfl
        · rw [heldB_iff_holdsM] at hb; omega
    cases c with
    | lock l =>
      simp only [hh] at ha hd
      obtain ⟨hb, rfl⟩ := lk l hd
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha
      split_ifs at ha
      obtain rfl := Option.some.inj ha; exact ⟨_, rfl⟩
    | tryLock l k =>
      simp only [hh] at ha hd
      obtain ⟨hb, rfl⟩ := lk l hd
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha
      split_ifs at ha
      · obtain rfl := Option.some.inj ha; exact ⟨_, rfl⟩
      · obtain rfl := Option.some.inj ha; exact ⟨_, rfl⟩
    | unlock l => simp [hh] at hd
    | rd y => simp [hh] at hd
    | wr y v => simp [hh] at hd
    | start u => simp [hh] at hd
    | join u =>
      simp only [hh, Option.some.injEq] at ha hd
      split_ifs at ha; cases ha; subst hd; exact ⟨_, rfl⟩
    | assume y v =>
      simp only [hh, Option.some.injEq] at ha hd
      split_ifs at ha
      · obtain rfl := Option.some.inj ha; subst hd; exact ⟨_, rfl⟩
      · obtain rfl := Option.some.inj ha; subst hd; exact ⟨_, rfl⟩

theorem count_zero_iff_val (hI : SInv P n s g) {l : Loc} (hl : P.isLock l = true) :
    s.count l = 0 ↔ valE P l (g.last l) = 0 := by
  rw [hI.vLock l hl]; split_ifs with h <;> simp [h]

theorem joinOk_iff_val (hI : SInv P n s g) {u : Tid} (hu : u ∈ P.threads) :
    s.joinOkB u = true ↔ valE P (P.st u) (g.last (P.st u)) ≠ 1 := by
  rw [joinOkB_eq_true, hI.vLife u hu]
  have h1 := hI.minv.started_of u
  cases hsd : s.started u
  · have : s.status u = .new := by
      by_contra h; have := h1 h; rw [hsd] at this; cases this
    simp [this]
  · simp only [Bool.true_eq_false, and_false, false_or, ↓reduceIte]
    by_cases h : s.status u = .term <;> simp [h]

theorem mem_eq_val (hI : SInv P n s g) {x : Loc} (hx : P.isData x = true) :
    s.mem x = valE P x (g.last x) := (hI.vData x hx).symm

/-- **The next occurrence is the same.** -/
theorem next_same (hF : Frag P) (hI : SInv P n s g) (hI' : SInv P n s' g') {t : Tid}
    (ht : t ∈ P.threads) (hst : s'.status t = s.status t) (hre : s'.rest t = s.rest t)
    (hho : holdsM s' t = holdsM s t) (hsd : s.started t = true → s'.started t = true)
    (hv : ∀ x, dloc P s t = some x → valE P x (g.last x) = valE P x (g'.last x))
    {a : Occ} (ha : next P s t = some a) : next P s' t = some a := by
  have hheld : ∀ l, s'.heldB t l = s.heldB t l := fun l =>
    Bool.eq_iff_iff.mpr (by rw [heldB_iff_holdsM, heldB_iff_holdsM, hho])
  have hok : ∀ {c}, (s.rest t).head? = some c → callOk P t c = true :=
    fun hc => hF.calls t ht _ (hI.minv.head_mem hc)
  unfold next at ha ⊢
  rw [hst, hre]
  cases hs : s.status t <;> simp only [hs] at ha ⊢
  · split_ifs at ha with h
    simp only [hsd h, ↓reduceIte]; exact ha
  · have hd : dloc P s t = (match (s.rest t).head? with
        | some (.lock l) => if holdsM s t l = 0 then some l else none
        | some (.tryLock l _) => if holdsM s t l = 0 then some l else none
        | some (.assume x _) => some x
        | some (.join u) => some (P.st u)
        | _ => none) := by simp only [dloc, hs]
    cases hh : (s.rest t).head? with
    | none => simp only [hh] at ha ⊢; exact ha
    | some c =>
      have hc := hok hh
      simp only [hh] at ha ⊢ hd
      cases c with
      | lock l =>
        simp only [callOk] at hc
        simp only at ha ⊢ hd
        rw [hheld l]
        cases hb : s.heldB t l
        · have h0 : holdsM s t l = 0 := holdsM_zero hb
          have hval := hv l (by simp only [hd, h0, ↓reduceIte])
          have hiff : s'.count l = 0 ↔ s.count l = 0 := by
            rw [count_zero_iff_val hI hc, count_zero_iff_val hI' hc, hval]
          simp only [hb] at ha ⊢
          simp only [hiff]; exact ha
        · simp only [hb] at ha ⊢; exact ha
      | tryLock l k =>
        simp only [callOk] at hc
        simp only at ha ⊢ hd
        rw [hheld l]
        cases hb : s.heldB t l
        · have h0 : holdsM s t l = 0 := holdsM_zero hb
          have hval := hv l (by simp only [hd, h0, ↓reduceIte])
          have hiff : s'.count l = 0 ↔ s.count l = 0 := by
            rw [count_zero_iff_val hI hc, count_zero_iff_val hI' hc, hval]
          simp only [hb] at ha ⊢
          simp only [hiff]; exact ha
        · simp only [hb] at ha ⊢; exact ha
      | unlock l =>
        simp only at ha ⊢
        rw [hheld l]
        cases hb : s.heldB t l
        · simp only [hb] at ha ⊢; exact ha
        · have hb' : s'.heldB t l = true := by rw [hheld l]; exact hb
          have hc' : s'.count l = s.count l := by
            rw [← holdsM_count hb', ← holdsM_count hb, hho]
          simp only [hb, hc'] at ha ⊢; exact ha
      | rd x => exact ha
      | wr x v => exact ha
      | start u => exact ha
      | assume x v =>
        simp only [callOk] at hc
        simp only at ha ⊢ hd
        have hval := hv x hd
        have hm : s'.mem x = s.mem x := by rw [mem_eq_val hI hc, mem_eq_val hI' hc, hval]
        rw [hm]; exact ha
      | join u =>
        simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at hc
        simp only at ha ⊢ hd
        have hval := hv (P.st u) hd
        have hj : s'.joinOkB u = s.joinOkB u := Bool.eq_iff_iff.mpr (by
          rw [joinOk_iff_val hI hc.1.1, joinOk_iff_val hI' hc.1.1, hval])
        rw [hj]; exact ha
  · cases ha
  · cases ha
  · cases ha

end Sem

end Life

end Condpor
