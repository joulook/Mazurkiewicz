import Mazurkiewicz.Condpor.Rmw.LifecycleGate2Lin

/-!
# Gate clause 2, part 2: adjacent exclusive pairs (LC2-b, continuation 3)

`g2Adj : G2Adj`. From a linearization `L` of an atomic SC graph, a new order: every event
`e` gets the key `2 * pos(mate e) + t`, where `mate r = w` for a completed pair `(r, w)` and
`mate e = e` otherwise, and `t = 0` exactly for the read of a pair. So the read of each pair
is delayed to just before its write (the write keeps its place).

The key fact (`rmw_out`): an SC edge out of the read `r` of a pair `(r, w)` to an event
`y ≠ w` gives an SC edge out of `w` to `y` (po: `y` is after `w` in the thread; fr: `y` is
coherence-after the source of `r`, hence after `w`, its immediate successor). So every SC edge
increases the key.
-/

namespace Condpor

namespace Life

namespace Sem

/-! ### Lists -/

theorem idxOf_imm {p w : TEv} {l₂ : List TEv} :
    ∀ l₁ : List TEv, (l₁ ++ p :: w :: l₂).Nodup →
      (l₁ ++ p :: w :: l₂).idxOf w = (l₁ ++ p :: w :: l₂).idxOf p + 1
  | [], h => by
    have hpw : p ≠ w := fun e => by subst e; simp at h
    simp only [List.nil_append]
    rw [List.idxOf_cons_self, List.idxOf_cons_ne _ hpw, List.idxOf_cons_self]
  | a :: l₁, h => by
    have ha : a ∉ l₁ ++ p :: w :: l₂ := (List.nodup_cons.mp h).1
    have hap : a ≠ p := fun e => ha (by simp [e])
    have haw : a ≠ w := fun e => ha (by simp [e])
    simp only [List.cons_append]
    rw [List.idxOf_cons_ne _ haw, List.idxOf_cons_ne _ hap, idxOf_imm l₁ (List.nodup_cons.mp h).2]

/-- In `l₁ ++ p :: w :: l₂`, an element after `p` other than `w` is after `w`. -/
theorem before_of_imm {p w y : TEv} {l₁ l₂ : List TEv} (hn : (l₁ ++ p :: w :: l₂).Nodup)
    (h : (l₁ ++ p :: w :: l₂).Before p y) (hy : y ≠ w) : (l₁ ++ p :: w :: l₂).Before w y := by
  have hw : w ∈ l₁ ++ p :: w :: l₂ := by simp
  refine (List.Before.total hw h.2.1 (Ne.symm hy)).resolve_right (fun h' => ?_)
  have := idxOf_imm l₁ hn
  have h1 := h.2.2
  have h2 := h'.2.2
  omega

/-- No element strictly between `r` and `w`: they are adjacent. -/
theorem adj_of_no_between {L : List TEv} {r w : TEv} (hn : L.Nodup) (hrw : L.Before r w)
    (hb : ∀ e ∈ L, e ≠ r → e ≠ w → L.Before e r ∨ L.Before w e) :
    ∃ l₁ l₂, L = l₁ ++ r :: w :: l₂ := by
  obtain ⟨hr, hw, hlt⟩ := hrw
  have hwl := List.idxOf_lt_length_of_mem hw
  have hrl := List.idxOf_lt_length_of_mem hr
  have hsucc : L.idxOf w = L.idxOf r + 1 := by
    by_contra hne
    have hi : L.idxOf r + 1 < L.length := by omega
    have hidx := hn.idxOf_getElem (L.idxOf r + 1) hi
    have he : L[L.idxOf r + 1] ∈ L := List.getElem_mem hi
    have her : L[L.idxOf r + 1] ≠ r := fun e => by rw [e] at hidx; omega
    have hew : L[L.idxOf r + 1] ≠ w := fun e => by rw [e] at hidx; omega
    rcases hb _ he her hew with h | h
    · have := h.2.2; omega
    · have := h.2.2; omega
  refine ⟨L.take (L.idxOf r), L.drop (L.idxOf r + 2), ?_⟩
  conv_lhs => rw [← List.take_append_drop (L.idxOf r) L]
  congr 1
  rw [List.drop_eq_getElem_cons hrl, List.getElem_idxOf hrl,
    List.drop_eq_getElem_cons (by omega : L.idxOf r + 1 < L.length)]
  have : L[L.idxOf r + 1] = w := by
    have := List.getElem_idxOf hwl
    simp only [hsucc] at this
    exact this
  rw [this]

/-- A list of a finite set along which keys increase. -/
theorem lin_key {α : Type*} [DecidableEq α] (k : α → ℕ) :
    ∀ S : Finset α, ∃ L : List α, L.Nodup ∧ (∀ e, e ∈ L ↔ e ∈ S) ∧
      ∀ a ∈ S, ∀ b ∈ S, k a < k b → L.Before a b := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hS : S = ∅
    · subst hS; exact ⟨[], by simp, by simp, by simp⟩
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image S k ⟨x, hx⟩
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
        have ham : a ≠ b := fun h => by subst h; omega
        exact Or.inr ⟨(hmem a).mpr (Finset.mem_erase.mpr ⟨ham, ha⟩), rfl⟩
      · have ham : a ≠ m := fun h => by subst h; have := hmax b hb; omega
        exact Or.inl (hord a (Finset.mem_erase.mpr ⟨ham, ha⟩) b
          (Finset.mem_erase.mpr ⟨hbm, hb⟩) hab)

/-! ### Completed pairs -/

section

variable {X : XProgram} {G : Graph}

theorem not_read_write {e : TEv} (hr : e.IsRead) (hw : e.IsWrite) : False := by
  obtain ⟨v, hv⟩ := hw.exists_act
  have := hr.exists_act.symm.trans hv
  cases this

theorem rmw_w_unique (hG : G.Wf) {r w w' : TEv} (h : X.RMW G r w) (h' : X.RMW G r w') :
    w = w' :=
  hG.idx_inj w h.2.1 w' h'.2.1 (h.2.2.1.trans h'.2.2.1.symm) (h.2.2.2.1.trans h'.2.2.2.1.symm)

theorem rmw_r_unique (hG : G.Wf) {r r' w : TEv} (h : X.RMW G r w) (h' : X.RMW G r' w) :
    r = r' := by
  have := h.2.2.2.1; have := h'.2.2.2.1
  exact hG.idx_inj r h.1 r' h'.1 (h.2.2.1.symm.trans h'.2.2.1) (by omega)

theorem rmw_po {r w : TEv} (h : X.RMW G r w) : G.scStep (.th r) (.th w) :=
  Or.inl ⟨h.1, h.2.1, h.2.2.1.symm, by rw [h.2.2.2.1]; omega⟩

/-- An SC edge out of the read of a pair, not to its write, also leaves the write. -/
theorem rmw_out (hG : G.Wf) (hE : X.toProgram.Exec G) (hat : X.Atomic G) {r w y : TEv}
    (hrw : X.RMW G r w) (hy : y ≠ w) (h : G.scStep (.th r) (.th y)) :
    G.scStep (.th w) (.th y) := by
  have hact := XProgram.RMW.read_act hE hrw
  obtain ⟨hr, hw, ht, hi, -, -, -, -⟩ := id hrw
  rcases h with h | h | h | h
  · obtain ⟨-, hyE, hty, hlt⟩ := h
    have hlt' : w.idx < y.idx := by
      by_contra hn
      exact hy (hG.idx_inj y hyE w hw (hty.symm.trans ht.symm) (by omega))
    exact Or.inl ⟨hw, hyE, ht.trans hty, hlt'⟩
  · obtain ⟨e, he, heE, hrf⟩ := h
    cases he
    obtain ⟨w', hw', hwt⟩ := hG.rf_read y heE _ (TEv.IsRead.exists_act (e := y) (by
      by_contra hn; rw [hG.rf_none y (Or.inr hn)] at hrf; cases hrf))
    rw [hrf] at hw'; cases hw'
    obtain ⟨-, v, hv⟩ := hwt
    rw [hact] at hv; cases hv
  · obtain ⟨x, hx⟩ := h
    obtain ⟨-, v, hv⟩ := (hG.co_mem x r).mp hx.1
    rw [hact] at hv; cases hv
  · obtain ⟨e, e', x, he, he', -, hex, hco, hsrc⟩ := h
    cases he; cases he'
    rw [hact] at hex; cases hex
    refine Or.inr (Or.inr (Or.inl ⟨w.loc, ?_⟩))
    rcases hsrc with hs | ⟨p, hs, hb⟩
    · obtain ⟨l, hl⟩ := hat r w hrw _ hs
      rw [hl] at hco ⊢
      rcases List.mem_cons.mp hco with h | h
      · exact absurd h hy
      · exact List.before_cons_self h (Ne.symm hy)
    · obtain ⟨l₁, l₂, hl⟩ := hat r w hrw _ hs
      have hn := hG.co_nodup w.loc
      rw [hl] at hn hb ⊢
      exact before_of_imm hn hb hy

/-! ### The key -/

open Classical in
/-- The write of the pair whose read is `e`, else `e`. -/
noncomputable def mate (X : XProgram) (G : Graph) (e : TEv) : TEv :=
  if h : ∃ w, X.RMW G e w then h.choose else e

open Classical in
/-- The key of `e` in the new order. -/
noncomputable def akey (X : XProgram) (G : Graph) (L : List TEv) (e : TEv) : ℕ :=
  2 * L.idxOf (mate X G e) + if ∃ w, X.RMW G e w then 0 else 1

theorem mate_of_rmw (hG : G.Wf) {r w : TEv} (h : X.RMW G r w) : mate X G r = w := by
  have hex : ∃ w, X.RMW G r w := ⟨w, h⟩
  simp only [mate, hex, dite_true]
  exact rmw_w_unique hG hex.choose_spec h

theorem mate_of_not {e : TEv} (h : ¬ ∃ w, X.RMW G e w) : mate X G e = e := by
  simp only [mate, h, dite_false]

theorem akey_of_rmw (hG : G.Wf) (L : List TEv) {r w : TEv} (h : X.RMW G r w) :
    akey X G L r = 2 * L.idxOf w := by
  have hex : ∃ w, X.RMW G r w := ⟨w, h⟩
  simp only [akey, mate_of_rmw hG h, hex, ite_true, add_zero]

theorem akey_of_not (L : List TEv) {e : TEv} (h : ¬ ∃ w, X.RMW G e w) :
    akey X G L e = 2 * L.idxOf e + 1 := by
  simp only [akey, mate_of_not h, h, ite_false]

theorem not_rmw_of_write {w : TEv} (hw : w.IsWrite) : ¬ ∃ w', X.RMW G w w' :=
  fun ⟨_, h⟩ => not_read_write h.2.2.2.2.1 hw

/-- Every SC edge increases the key. -/
theorem akey_lt (hG : G.Wf) (hE : X.toProgram.Exec G) (hat : X.Atomic G) {L : List TEv}
    (hL : IsLin G L) {a b : TEv} (h : G.scStep (.th a) (.th b)) :
    akey X G L a < akey X G L b := by
  have hab := hL.2.2 a b h
  by_cases ha : ∃ w, X.RMW G a w
  · obtain ⟨w, hw⟩ := ha
    rw [akey_of_rmw hG L hw]
    by_cases hb : ∃ w', X.RMW G b w'
    · obtain ⟨w', hw'⟩ := hb
      rw [akey_of_rmw hG L hw']
      have hbw : b ≠ w := fun e => not_read_write hw'.2.2.2.2.1 (e ▸ hw.2.2.2.2.2.1)
      have h1 := (hL.2.2 _ _ (rmw_out hG hE hat hw hbw h)).2.2
      have h2 := (hL.2.2 _ _ (rmw_po hw')).2.2
      omega
    · rw [akey_of_not L hb]
      by_cases hbw : b = w
      · subst hbw; omega
      · have h1 := (hL.2.2 _ _ (rmw_out hG hE hat hw hbw h)).2.2
        omega
  · rw [akey_of_not L ha]
    by_cases hb : ∃ w', X.RMW G b w'
    · obtain ⟨w', hw'⟩ := hb
      rw [akey_of_rmw hG L hw']
      have h2 := (hL.2.2 _ _ (rmw_po hw')).2.2
      have h1 := hab.2.2
      omega
    · rw [akey_of_not L hb]
      have h1 := hab.2.2
      omega

/-- Only the pair itself has the keys of a pair. -/
theorem akey_pair (hG : G.Wf) {L : List TEv} (hL : IsLin G L) {r w e : TEv}
    (hrw : X.RMW G r w) (he : e ∈ G.events) (her : e ≠ r) (hew : e ≠ w) :
    akey X G L e < akey X G L r ∨ akey X G L w + 1 ≤ akey X G L e := by
  rw [akey_of_rmw hG L hrw, akey_of_not L (not_rmw_of_write hrw.2.2.2.2.2.1)]
  have hwL : w ∈ L := (hL.2.1 w).mpr hrw.2.1
  by_cases hx : ∃ w', X.RMW G e w'
  · obtain ⟨w', hw'⟩ := hx
    rw [akey_of_rmw hG L hw']
    have hww : w' ≠ w := fun h => by subst h; exact her (rmw_r_unique hG hw' hrw)
    have hne : L.idxOf w' ≠ L.idxOf w := fun h =>
      hww ((List.idxOf_inj ((hL.2.1 w').mpr hw'.2.1)).mp h)
    omega
  · rw [akey_of_not L hx]
    have hne : L.idxOf e ≠ L.idxOf w := fun h => hew ((List.idxOf_inj ((hL.2.1 e).mpr he)).mp h)
    omega

end

/-- **Gate clause 2, part 2.** -/
theorem g2Adj : G2Adj := by
  intro P n c hT ⟨L, hL⟩
  obtain ⟨-, -, hw, hE, hc, -, -⟩ := hT
  have hG : c.abs.Wf := hw.1
  obtain ⟨-, hat⟩ := Model.atomic_cons_iff.mp (Model.sym_cons_iff.mp hc).1
  obtain ⟨L', hn, hmem, hord⟩ := lin_key (akey (lifeSys P n) c.abs L) c.abs.events
  refine ⟨L', ⟨hn, hmem, fun a b h => ?_⟩, ?_⟩
  · obtain ⟨ha, hb⟩ := scStep_mem hG h
    exact hord a ha b hb (akey_lt hG hE hat hL h)
  · intro r w hrw
    have hrE := hrw.1
    have hwE := hrw.2.1
    have hrw' : L'.Before r w :=
      hord r hrE w hwE (by
        rw [akey_of_rmw hG L hrw, akey_of_not L (not_rmw_of_write hrw.2.2.2.2.2.1)]; omega)
    refine adj_of_no_between hn hrw' (fun e he her hew => ?_)
    have heE := (hmem e).mp he
    rcases akey_pair hG hL hrw heE her hew with h | h
    · exact Or.inl (hord e heE r hrE h)
    · exact Or.inr (hord w hwE e heE (by omega))

end Sem

end Life

end Condpor
