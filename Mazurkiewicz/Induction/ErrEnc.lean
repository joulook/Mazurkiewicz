import Mazurkiewicz.Induction.ErrGraph

/-!
# Errors as writes

`induction-popl`, `dpor.tex`, lem:errenc, cor:errenc and the remark after it.

* lem:errenc (1): `enc_bounded`. (`Q̂` is a plain program by its type, and
  a Lean function defined from `Q.step`.)
* lem:errenc (2), between `DTail` and `DHatTail`: `psi_dHatTail`,
  `psiInv_dTail`, `psiInv_psi`, `psi_psiInv`, `psi_mem`, `psi_cons`,
  `psi_trace`. The paper states the bijection between the larger sets `D`,
  `D̂`.
* lem:errenc (3): `ExecE.dTail`, `exec_enc_dHatTail`, `execE_iff`.
* lem:errenc (4): `fullE_iff`, `fullESC_iff`, `fullSC_enc`.
* cor:errenc: `encEnum` with `encEnum_complete`, `encEnum_sound`,
  `encEnum_optimal` (the last for a sound enumerator).
* The remark after cor:errenc: `safeE_iff`, `safeE_badErr_iff`,
  `badMark_extClosed`, `check_sound_err`. `Check` runs on the plain program
  `Q̂`; `Bad_err`-safety of `Q` is transferred from it.
-/

namespace Trust

variable (m : Markers) {Q : SProgram}

/-- SC-consistency ignores the error events. -/
theorem EGraph.consE_iff (E : EGraph) : E.consE ↔ SC.cons E.G := by
  have hlift : ∀ a b, Relation.TransGen E.G.scStep a b →
      Relation.TransGen E.scStepE (.ev a) (.ev b) := by
    intro a b h
    induction h with
    | single h => exact .single h
    | tail _ h ih => exact ih.tail h
  have hdown : ∀ p q, Relation.TransGen E.scStepE p q → ∀ a b, p = .ev a → q = .ev b →
      Relation.TransGen E.G.scStep a b := by
    intro p q h
    induction h with
    | single h =>
      rintro a b rfl rfl
      exact .single h
    | @tail c d _ h ih =>
      rintro a b rfl rfl
      cases c with
      | ev c' => exact (ih a c' rfl rfl).tail h
      | err t => exact absurd h (by simp [EGraph.scStepE])
  constructor
  · intro h a ha
    exact h (.ev a) (hlift a a ha)
  · intro h p hp
    cases p with
    | ev a => exact h a (hdown _ _ hp a a rfl rfl)
    | err t =>
      rcases Relation.TransGen.head'_iff.mp hp with ⟨c, hc, -⟩
      exact absurd hc (by simp [EGraph.scStepE])

/-! ### lem:errenc (1) -/

theorem SProgram.enc_bounded (Q : SProgram) (n : ℕ) : (Q.enc m).Bounded n ↔ Q.Bounded n := by
  refine forall_congr' (fun t => forall_congr' (fun u => imp_congr_right (fun _ => ?_)))
  exact Option.map_eq_none_iff

/-! ### `Ψ`, one error event at a time -/

theorem Markers.own_lam (t : Tid) : m.own (m.lam t) = some t := (m.own_iff _ _).mpr rfl

theorem Markers.lam_injective {t t' : Tid} (h : m.lam t = m.lam t') : t = t' := by
  have h1 := m.own_lam t
  rw [h, m.own_lam t'] at h1
  exact (Option.some.inj h1).symm

theorem EGraph.mark_isWrite (E : EGraph) (t : Tid) : (E.mark m t).IsWrite := by
  simp [EGraph.mark, TEv.IsWrite, Act.IsWrite]

theorem EGraph.mem_psi_events {E : EGraph} {e : TEv} :
    e ∈ (E.psi m).events ↔ e ∈ E.G.events ∨ ∃ t ∈ E.errs, e = E.mark m t := by
  simp only [EGraph.psi, Finset.mem_union, Finset.mem_image]
  exact or_congr Iff.rfl ⟨fun ⟨t, ht, h⟩ => ⟨t, ht, h.symm⟩, fun ⟨t, ht, h⟩ => ⟨t, ht, h.symm⟩⟩

/-- Adding the error event of one more thread is adding its marker write
after `init`. -/
theorem EGraph.psi_insert (G : Graph) {s : Finset Tid} {t : Tid} (ht : t ∉ s) :
    (EGraph.mk G (insert t s)).psi m =
      ((EGraph.mk G s).psi m).addWrite ((EGraph.mk G s).mark m t) .init := by
  apply Graph.ext
  · rfl
  · ext e
    simp only [EGraph.psi, Graph.addWrite_events, Finset.image_insert, Finset.mem_union,
      Finset.mem_insert, Finset.mem_image, EGraph.mark]
    tauto
  · rfl
  · funext x
    have hloc : ((EGraph.mk G s).mark m t).loc = m.lam t := rfl
    by_cases hx : x = m.lam t
    · subst hx
      rw [← hloc, Graph.addWrite_co_self, hloc]
      simp only [EGraph.psi, m.own_lam, Finset.mem_insert, true_or, ite_true,
        ite_eq_right_of_eq_false _ _ (eq_false ht)]
      rfl
    · rw [Graph.addWrite_co_of_ne _ _ _ (hloc ▸ hx)]
      simp only [EGraph.psi]
      cases hown : m.own x with
      | none => rfl
      | some t' =>
        have hne : t' ≠ t := by
          rintro rfl
          exact hx ((m.own_iff x t').mp hown).symm
        simp [hne, EGraph.mark]

/-- The facts on `Ψ` that hold for every well-formed plain graph. -/
theorem EGraph.psi_facts {G : Graph} (hG : G.Wf) (s : Finset Tid) :
    ((EGraph.mk G s).psi m).Wf ∧
      (∀ t, ((EGraph.mk G s).psi m).cnt t = G.cnt t + if t ∈ s then 1 else 0) ∧
      (∀ t, ((EGraph.mk G s).psi m).trace t = G.trace t ++ if t ∈ s then [none] else []) ∧
      G.IsPrefixOf ((EGraph.mk G s).psi m) := by
  induction s using Finset.induction_on with
  | empty =>
    have h0 : (EGraph.mk G ∅).psi m = G := by
      apply Graph.ext
      · rfl
      · simp [EGraph.psi]
      · rfl
      · funext x
        simp only [EGraph.psi]
        cases m.own x <;> simp
    rw [h0]
    refine ⟨hG, by simp, by simp, ⟨G.events, ?_, hG.restrict_self.symm⟩⟩
    intro a b h hb
    cases a with
    | init => trivial
    | th e =>
      have : e ∈ G.events := by
        rcases h with h | h
        · cases b with
          | init => exact absurd h (by simp [Graph.po])
          | th e' => exact h.1
        · obtain ⟨r, -, -, hr⟩ := h
          simpa [Graph.evSet] using (hG.rf_source_mem hr).2
      simpa [Graph.evSet] using this
  | insert t s ht ih =>
    obtain ⟨hW, hcnt, htr, hpre⟩ := ih
    have hidx : ((EGraph.mk G s).mark m t).idx =
        ((EGraph.mk G s).psi m).cnt ((EGraph.mk G s).mark m t).tid := by
      change G.cnt t = ((EGraph.mk G s).psi m).cnt t
      rw [hcnt t, ite_eq_right_of_eq_false _ _ (eq_false ht)]
      rfl
    have hact := (EGraph.mk G s).mark_isWrite m t
    have hwp : ((EGraph.mk G s).psi m).IsWriteTo ((EGraph.mk G s).mark m t).loc .init := trivial
    rw [EGraph.psi_insert m G ht]
    refine ⟨hW.addWrite hidx hact hwp, fun t' => ?_, fun t' => ?_,
      hpre.trans (hW.isPrefixOf_addWrite hidx)⟩
    · rw [Graph.cnt_addWrite hW hidx, hcnt t']
      change (if t' = t then _ else _) = _
      by_cases h : t' = t
      · subst h
        simp [ht]
      · simp [h]
    · rw [Graph.trace_addWrite hW hidx hact hwp, htr t']
      change (if t' = t then _ else _) = _
      by_cases h : t' = t
      · subst h
        simp [ht]
      · simp [h]

theorem EGraph.psi_wf {E : EGraph} (hE : E.G.Wf) : (E.psi m).Wf := (EGraph.psi_facts m hE E.errs).1

theorem EGraph.isPrefixOf_psi {E : EGraph} (hE : E.G.Wf) : E.G.IsPrefixOf (E.psi m) :=
  (EGraph.psi_facts m hE E.errs).2.2.2

theorem EGraph.psi_empty (G : Graph) : (EGraph.mk G ∅).psi m = G := by
  apply Graph.ext
  · rfl
  · simp [EGraph.psi]
  · rfl
  · funext x
    simp only [EGraph.psi]
    cases m.own x <;> simp

theorem EGraph.mark_not_mem {E : EGraph} (hE : E.G.Wf) (t : Tid) : E.mark m t ∉ E.G.events :=
  hE.not_mem_of_idx_eq_cnt rfl

theorem Markers.isMark_eq_false_iff {e : TEv} : m.isMark e = false ↔ m.own e.loc = none := by
  unfold Markers.isMark
  cases m.own e.loc <;> simp

theorem Markers.isMark_eq_true_iff {e : TEv} : m.isMark e = true ↔ ∃ t, m.own e.loc = some t := by
  unfold Markers.isMark
  cases m.own e.loc <;> simp

theorem EGraph.isMark_mark (E : EGraph) (t : Tid) : m.isMark (E.mark m t) = true :=
  m.isMark_eq_true_iff.mpr ⟨t, m.own_lam t⟩

/-- The plain graph is the restriction of `Ψ(E)` to its events. -/
theorem EGraph.psi_restrict {E : EGraph} (hE : E.G.Wf) : (E.psi m).restrict E.G.events = E.G := by
  apply Graph.ext
  · rfl
  · exact Finset.union_inter_cancel_left
  · funext e
    by_cases he : e ∈ (E.psi m).events ∩ E.G.events
    · exact (E.psi m).restrict_rf_of_source_kept he (fun w hw => (hE.rf_source_mem hw).2)
    · rw [(E.psi m).restrict_rf_of_not_mem he]
      refine (hE.rf_none e (Or.inl (fun h => he ?_))).symm
      exact Finset.mem_inter.mpr ⟨(EGraph.mem_psi_events m).mpr (Or.inl h), h⟩
  · funext x
    rw [Graph.restrict_co]
    change List.filter _ (_ ++ E.G.co x) = _
    rw [List.filter_append]
    have h1 : (E.G.co x).filter (fun e => decide (e ∈ E.G.events)) = E.G.co x := by
      rw [List.filter_eq_self]
      intro a ha
      simpa using ((hE.co_mem x a).mp ha).1
    rw [h1]
    cases m.own x with
    | none => rfl
    | some t =>
      by_cases ht : t ∈ E.errs
      · simp [ht, EGraph.mark_not_mem m hE t]
      · simp [ht]

theorem SAct.enc_ofAct (t : Tid) (a : Act) : SAct.enc m t (SAct.ofAct a) = a := by
  cases a <;> rfl

/-! ### lem:errenc (2) -/

@[simp] theorem EGraph.psi_mem (E : EGraph) : (E.psi m).mem = E.G.mem := rfl

theorem psi_dHatTail {E : EGraph} (hE : DTail m E) : DHatTail m (E.psi m) := by
  refine ⟨EGraph.psi_wf m hE.1, decide_eq_true (fun e he => ?_)⟩
  rcases (EGraph.mem_psi_events m).mp he with h | ⟨t, ht, rfl⟩
  · unfold Markers.markOK
    simp only [hE.2 e h]
  · have hown : m.own (E.mark m t).loc = some t := m.own_lam t
    unfold Markers.markOK
    simp only [hown]
    refine decide_eq_true ⟨rfl, rfl, ?_⟩
    rw [(EGraph.psi_facts m hE.1 E.errs).2.1 t, ite_eq_left_of_eq_true _ _ (eq_true ht)]
    rfl

/-! The inverse direction: graphs of `D̂`. -/

section inverse

variable {m} {H : Graph}

theorem DHatTail.spec (hH : DHatTail m H) {e : TEv} (he : e ∈ H.events) {t : Tid}
    (hown : m.own e.loc = some t) :
    e.tid = t ∧ e.act = .write (m.lam t) m.ve ∧ e.idx + 1 = H.cnt t := by
  have h := of_decide_eq_true hH.2 e he
  unfold Markers.markOK at h
  simp only [hown] at h
  exact of_decide_eq_true h

/-- A thread has at most one event on a marker. -/
theorem DHatTail.unique (hH : DHatTail m H) {e e' : TEv} (he : e ∈ H.events)
    (he' : e' ∈ H.events) {t : Tid} (h : m.own e.loc = some t) (h' : m.own e'.loc = some t) :
    e = e' := by
  obtain ⟨h1, -, h3⟩ := hH.spec he h
  obtain ⟨h1', -, h3'⟩ := hH.spec he' h'
  exact hH.1.idx_inj e he e' he' (h1.trans h1'.symm) (by omega)

theorem mem_keep {e : TEv} :
    e ∈ H.events.filter (fun e => m.isMark e = false) ↔ e ∈ H.events ∧ m.own e.loc = none := by
  rw [Finset.mem_filter, m.isMark_eq_false_iff]

theorem DHatTail.keep_po (hH : DHatTail m H) :
    Maz.PrefixClosed H.po
      (Graph.evSet (H.events ∩ H.events.filter (fun e => m.isMark e = false))) := by
  intro a b hab hb
  cases a with
  | init => trivial
  | th e =>
    cases b with
    | init => exact absurd hab (by simp [Graph.po])
    | th e' =>
      obtain ⟨he, he', htid, hlt⟩ := hab
      change e ∈ H.events ∩ _
      refine Finset.mem_inter.mpr ⟨he, mem_keep.mpr ⟨he, ?_⟩⟩
      cases hown : m.own e.loc with
      | none => rfl
      | some t =>
        obtain ⟨ht, -, hlast⟩ := hH.spec he hown
        have := hH.1.idx_lt_cnt he'
        rw [← htid, ht] at this
        omega

theorem DHatTail.keep_rf (hH : DHatTail m H) :
    ∀ q ∈ H.events ∩ H.events.filter (fun e => m.isMark e = false), ∀ w, H.rf q = some w →
      w ∈ Graph.evSet (H.events.filter (fun e => m.isMark e = false)) := by
  intro q hq w hw
  obtain ⟨hqe, hqk⟩ := Finset.mem_inter.mp hq
  have hqn := (mem_keep.mp hqk).2
  cases w with
  | init => trivial
  | th w =>
    change w ∈ H.events.filter _
    cases hact : q.act with
    | write x v =>
      rw [hH.1.rf_none q (Or.inr (by simp [TEv.IsWrite, hact, Act.IsWrite]))] at hw
      cases hw
    | read x =>
      obtain ⟨w0, hw0, hwr⟩ := hH.1.rf_read q hqe x hact
      rw [hw] at hw0
      cases hw0
      obtain ⟨hwe, v, hv⟩ := hwr
      refine mem_keep.mpr ⟨hwe, ?_⟩
      rw [TEv.loc, hact] at hqn
      rw [TEv.loc, hv]
      exact hqn

theorem mem_psiInv_errs (hH : DHatTail m H) {t : Tid} :
    t ∈ (H.psiInv m).errs ↔ ∃ e ∈ H.events, m.own e.loc = some t := by
  change t ∈ Finset.image _ _ ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨e, he, rfl⟩
    obtain ⟨he, hm⟩ := Finset.mem_filter.mp he
    obtain ⟨t, ht⟩ := m.isMark_eq_true_iff.mp hm
    exact ⟨e, he, (hH.spec he ht).1 ▸ ht⟩
  · rintro ⟨e, he, ht⟩
    exact ⟨e, Finset.mem_filter.mpr ⟨he, m.isMark_eq_true_iff.mpr ⟨t, ht⟩⟩, (hH.spec he ht).1⟩

/-- The marker event of `t` in `H` is the write that `Ψ` adds. -/
theorem mark_psiInv (hH : DHatTail m H) {e : TEv} (he : e ∈ H.events) {t : Tid}
    (hown : m.own e.loc = some t) : (H.psiInv m).mark m t = e := by
  obtain ⟨h1, h2, h3⟩ := hH.spec he hown
  have hsplit : H.events.filter (fun q => q.tid = t) =
      insert e ((H.psiInv m).G.events.filter (fun q => q.tid = t)) := by
    ext q
    change _ ↔ q ∈ insert e ((H.events ∩ _).filter _)
    rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_filter, Finset.mem_inter, mem_keep]
    constructor
    · rintro ⟨hq, hqt⟩
      cases hq' : m.own q.loc with
      | none => exact Or.inr ⟨⟨hq, hq, rfl⟩, hqt⟩
      | some t' =>
        have : t' = t := (hH.spec hq hq').1.symm.trans hqt
        subst this
        exact Or.inl (hH.unique hq he hq' hown)
    · rintro (rfl | ⟨⟨hq, -⟩, hqt⟩)
      · exact ⟨he, h1⟩
      · exact ⟨hq, hqt⟩
  have hnot : e ∉ (H.psiInv m).G.events.filter (fun q => q.tid = t) := by
    intro h
    have h' : e ∈ H.events ∩ _ := (Finset.mem_filter.mp h).1
    have := (mem_keep.mp (Finset.mem_inter.mp h').2).2
    rw [hown] at this
    cases this
  have hcnt : H.cnt t = (H.psiInv m).G.cnt t + 1 := by
    unfold Graph.cnt
    rw [hsplit, Finset.card_insert_of_notMem hnot]
  obtain ⟨et, ei, ea⟩ := e
  simp only at h1 h2 h3
  simp only [EGraph.mark, TEv.mk.injEq]
  exact ⟨h1.symm, by omega, h2.symm⟩

end inverse

theorem psiInv_dTail {H : Graph} (hH : DHatTail m H) : DTail m (H.psiInv m) := by
  refine ⟨hH.1.restrict_of_sources hH.keep_po hH.keep_rf, fun e he => ?_⟩
  have he' : e ∈ H.events ∩ _ := he
  exact (mem_keep.mp (Finset.mem_inter.mp he').2).2

theorem psiInv_psi {E : EGraph} (hE : DTail m E) : (E.psi m).psiInv m = E := by
  have hfil : (E.psi m).events.filter (fun e => m.isMark e = false) = E.G.events := by
    ext e
    rw [Finset.mem_filter, EGraph.mem_psi_events]
    constructor
    · rintro ⟨h | ⟨t, -, rfl⟩, hm⟩
      · exact h
      · rw [EGraph.isMark_mark] at hm
        cases hm
    · exact fun h => ⟨Or.inl h, m.isMark_eq_false_iff.mpr (hE.2 e h)⟩
  apply EGraph.ext
  · change (E.psi m).restrict _ = _
    rw [hfil, EGraph.psi_restrict m hE.1]
  · ext t
    change t ∈ Finset.image _ _ ↔ _
    rw [Finset.mem_image]
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨he, hm⟩ := Finset.mem_filter.mp he
      rcases (EGraph.mem_psi_events m).mp he with h | ⟨t, ht, rfl⟩
      · rw [m.isMark_eq_false_iff.mpr (hE.2 e h)] at hm
        cases hm
      · exact ht
    · exact fun ht => ⟨E.mark m t, Finset.mem_filter.mpr
        ⟨(EGraph.mem_psi_events m).mpr (Or.inr ⟨t, ht, rfl⟩), E.isMark_mark m t⟩, rfl⟩

private theorem eq_singleton_of_nodup {α : Type} {l : List α} {e : α} (hn : l.Nodup)
    (hall : ∀ a ∈ l, a = e) (he : e ∈ l) : l = [e] := by
  cases l with
  | nil => cases he
  | cons a l' =>
    have ha : a = e := hall a List.mem_cons_self
    subst ha
    cases l' with
    | nil => rfl
    | cons b l'' =>
      have hb : b = a := hall b (List.mem_cons_of_mem _ List.mem_cons_self)
      subst hb
      exact absurd List.mem_cons_self (List.nodup_cons.mp hn).1

theorem psi_psiInv {H : Graph} (hH : DHatTail m H) : (H.psiInv m).psi m = H := by
  apply Graph.ext
  · rfl
  · ext q
    rw [EGraph.mem_psi_events]
    constructor
    · rintro (h | ⟨t, ht, rfl⟩)
      · exact (Finset.mem_inter.mp (show q ∈ H.events ∩ _ from h)).1
      · obtain ⟨e, he, hown⟩ := (mem_psiInv_errs hH).mp ht
        rw [mark_psiInv hH he hown]
        exact he
    · intro hq
      cases hown : m.own q.loc with
      | none => exact Or.inl (Finset.mem_inter.mpr ⟨hq, mem_keep.mpr ⟨hq, hown⟩⟩)
      | some t =>
        exact Or.inr ⟨t, (mem_psiInv_errs hH).mpr ⟨q, hq, hown⟩, (mark_psiInv hH hq hown).symm⟩
  · funext q
    change (H.restrict _).rf q = H.rf q
    by_cases hq : q ∈ H.events ∩ H.events.filter (fun e => m.isMark e = false)
    · exact H.restrict_rf_of_source_kept hq (hH.keep_rf q hq)
    · rw [H.restrict_rf_of_not_mem hq]
      symm
      by_cases hqe : q ∈ H.events
      · cases hown : m.own q.loc with
        | none => exact absurd (Finset.mem_inter.mpr ⟨hqe, mem_keep.mpr ⟨hqe, hown⟩⟩) hq
        | some t =>
          refine hH.1.rf_none q (Or.inr ?_)
          simp [TEv.IsWrite, (hH.spec hqe hown).2.1, Act.IsWrite]
      · exact hH.1.rf_none q (Or.inl hqe)
  · funext x
    change (match m.own x with
      | some t => if t ∈ (H.psiInv m).errs then [(H.psiInv m).mark m t] else []
      | none => []) ++ (H.co x).filter _ = H.co x
    have hloc : ∀ a ∈ H.co x, a ∈ H.events ∧ a.loc = x := by
      intro a ha
      obtain ⟨hae, v, hv⟩ := (hH.1.co_mem x a).mp ha
      exact ⟨hae, by rw [TEv.loc, hv]; rfl⟩
    cases hown : m.own x with
    | none =>
      rw [List.nil_append, List.filter_eq_self]
      intro a ha
      obtain ⟨hae, hax⟩ := hloc a ha
      exact decide_eq_true (mem_keep.mpr ⟨hae, hax ▸ hown⟩)
    | some t =>
      have hfil : (H.co x).filter (fun e => decide (e ∈ H.events.filter
          (fun e => m.isMark e = false))) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha hk
        obtain ⟨-, hax⟩ := hloc a ha
        have := (mem_keep.mp (of_decide_eq_true hk)).2
        rw [hax, hown] at this
        cases this
      rw [hfil, List.append_nil]
      by_cases ht : t ∈ (H.psiInv m).errs
      · obtain ⟨e, he, hoe⟩ := (mem_psiInv_errs hH).mp ht
        simp only [ite_eq_left_of_eq_true _ _ (eq_true ht)]
        rw [mark_psiInv hH he hoe]
        have hex : e.loc = x := by
          have h1 := (m.own_iff _ _).mp hoe
          have h2 := (m.own_iff _ _).mp hown
          exact h1.symm.trans h2
        have hmem : e ∈ H.co x := by
          refine (hH.1.co_mem x e).mpr ⟨he, m.ve, ?_⟩
          rw [(hH.spec he hoe).2.1, (m.own_iff _ _).mp hown]
        refine (eq_singleton_of_nodup (hH.1.co_nodup x) (fun a ha => ?_) hmem).symm
        obtain ⟨hae, hax⟩ := hloc a ha
        exact hH.unique hae he (hax ▸ hown) hoe
      · simp only [ite_eq_right_of_eq_false _ _ (eq_false ht)]
        symm
        refine List.eq_nil_iff_forall_not_mem.mpr (fun a ha => ?_)
        obtain ⟨hae, hax⟩ := hloc a ha
        exact ht ((mem_psiInv_errs hH).mpr ⟨a, hae, hax ▸ hown⟩)

/-- `Ψ` preserves SC-consistency. -/
theorem psi_cons {E : EGraph} (hE : DTail m E) : E.consE ↔ SC.cons (E.psi m) := by
  rw [EGraph.consE_iff]
  refine ⟨fun hc => ?_, fun hc =>
    SC.prefix_closed _ _ (EGraph.psi_wf m hE.1) hc (EGraph.isPrefixOf_psi m hE.1)⟩
  have key : ∀ s : Finset Tid, SC.cons ((EGraph.mk E.G s).psi m) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rwa [EGraph.psi_empty]
    | insert t s ht ih =>
      obtain ⟨hW, hcnt, -, -⟩ := EGraph.psi_facts m hE.1 s
      have hidx : ((EGraph.mk E.G s).mark m t).idx =
          ((EGraph.mk E.G s).psi m).cnt ((EGraph.mk E.G s).mark m t).tid := by
        change E.G.cnt t = ((EGraph.mk E.G s).psi m).cnt t
        rw [hcnt t, ite_eq_right_of_eq_false _ _ (eq_false ht)]
        rfl
      have hact := (EGraph.mk E.G s).mark_isWrite m t
      have hco : E.G.co (m.lam t) = [] := by
        refine List.eq_nil_iff_forall_not_mem.mpr (fun e he => ?_)
        obtain ⟨hev, v, hv⟩ := (hE.1.co_mem _ e).mp he
        have := hE.2 e hev
        rw [TEv.loc, hv] at this
        rw [show (Act.write (m.lam t) v).loc = m.lam t from rfl, m.own_lam] at this
        cases this
      have hmax : ((EGraph.mk E.G s).psi m).maxWrite ((EGraph.mk E.G s).mark m t).loc = .init := by
        change ((EGraph.mk E.G s).psi m).maxWrite (m.lam t) = .init
        unfold Graph.maxWrite
        have : ((EGraph.mk E.G s).psi m).co (m.lam t) = [] := by
          simp only [EGraph.psi, m.own_lam, ite_eq_right_of_eq_false _ _ (eq_false ht), hco]
          rfl
        rw [this]
        rfl
      have := SC.extensible.cons_addMax hW ih hidx
      rw [Graph.addMax_write hact, hmax] at this
      rwa [EGraph.psi_insert m E.G ht]
  exact key E.errs

/-- `Ψ` preserves the returned values: the traces agree. -/
theorem psi_trace {E : EGraph} (hE : E.G.Wf) (t : Tid) : (E.psi m).trace t = E.trace t :=
  (EGraph.psi_facts m hE E.errs).2.2.1 t

/-- The number of events of a thread: one more for an error event. -/
theorem psi_cnt {E : EGraph} (hE : E.G.Wf) (t : Tid) :
    (E.psi m).cnt t = E.G.cnt t + if t ∈ E.errs then 1 else 0 :=
  (EGraph.psi_facts m hE E.errs).2.1 t

/-! ### lem:errenc (3) -/

/-- Every execution of `Q` is in `D`. -/
theorem SProgram.ExecE.dTail (hQ : Q.NoMark m) {E : EGraph} (hwf : E.G.Wf) (h : Q.ExecE E) :
    DTail m E := by
  refine ⟨hwf, fun e he => ?_⟩
  have h' := h.2.1 e he
  cases hact : e.act with
  | read x =>
    rw [hact] at h'
    simpa [TEv.loc, hact, Act.loc] using (hQ _ _).1 x h'
  | write x v =>
    rw [hact] at h'
    simpa [TEv.loc, hact, Act.loc] using (hQ _ _).2 x v h' 

/-- Every execution of `Q̂` is in `D̂`. -/
theorem exec_enc_dHatTail (hQ : Q.NoMark m) {H : Graph} (hwf : H.Wf) (h : (Q.enc m).Exec H) :
    DHatTail m H := by
  refine ⟨hwf, decide_eq_true (fun e he => ?_)⟩
  unfold Markers.markOK
  cases hown : m.own e.loc with
  | none => rfl
  | some t =>
    have h' : (Q.step e.tid (H.traceBefore e.tid e.idx)).map (SAct.enc m e.tid) = some e.act :=
      h.2 e he
    cases hs : Q.step e.tid (H.traceBefore e.tid e.idx) with
    | none =>
      rw [hs] at h'
      cases h'
    | some a =>
      rw [hs] at h'
      have h'' : SAct.enc m e.tid a = e.act := Option.some.inj h'
      cases a with
      | read x =>
        have := (hQ _ _).1 x hs
        rw [TEv.loc, ← h''] at hown
        rw [show (SAct.enc m e.tid (.read x)).loc = x from rfl, this] at hown
        cases hown
      | write x v =>
        have := (hQ _ _).2 x v hs
        rw [TEv.loc, ← h''] at hown
        rw [show (SAct.enc m e.tid (.write x v)).loc = x from rfl, this] at hown
        cases hown
      | err =>
        have hact : e.act = .write (m.lam e.tid) m.ve := h''.symm
        have hown' := hown
        rw [TEv.loc, hact] at hown'
        rw [show (Act.write (m.lam e.tid) m.ve).loc = m.lam e.tid from rfl, m.own_lam] at hown'
        have ht : e.tid = t := Option.some.inj hown'
        subst ht
        refine decide_eq_true ⟨rfl, hact, ?_⟩
        have hlt := hwf.idx_lt_cnt he
        by_contra hne
        have hlt' : e.idx + 1 < H.cnt e.tid := by omega
        obtain ⟨e', he', het, hei⟩ := (hwf.exists_idx_iff e.tid (e.idx + 1)).mpr hlt'
        have h2 : (Q.step e'.tid (H.traceBefore e'.tid e'.idx)).map (SAct.enc m e'.tid) =
            some e'.act := h.2 e' he'
        rw [het, hei, Graph.traceBefore_succ, hwf.evAt_eq_some he] at h2
        have hret : H.ret e = none := by
          unfold Graph.ret
          rw [hact]
        rw [Option.bind_some, hret, Q.stop _ _ hs] at h2
        cases h2

/-- `G ∈ D` is an execution of `Q` iff `Ψ(G)` is an execution of `Q̂`. -/
theorem execE_iff (hQ : Q.NoMark m) {E : EGraph} (hE : DTail m E) :
    Q.ExecE E ↔ (Q.enc m).Exec (E.psi m) := by
  have hG := hE.1
  constructor
  · intro h
    have hbase : (Q.enc m).Exec E.G := by
      refine ⟨h.1, fun e he => ?_⟩
      change (Q.step _ _).map _ = _
      rw [h.2.1 e he, Option.map_some, SAct.enc_ofAct]
    have key : ∀ s : Finset Tid, (∀ t ∈ s, Q.step t (E.G.trace t) = some .err) →
        (Q.enc m).Exec ((EGraph.mk E.G s).psi m) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro _
        rwa [EGraph.psi_empty]
      | insert t s ht ih =>
        intro hs
        obtain ⟨hW, hcnt, htr, -⟩ := EGraph.psi_facts m hG s
        have hidx : ((EGraph.mk E.G s).mark m t).idx =
            ((EGraph.mk E.G s).psi m).cnt ((EGraph.mk E.G s).mark m t).tid := by
          change E.G.cnt t = ((EGraph.mk E.G s).psi m).cnt t
          rw [hcnt t, ite_eq_right_of_eq_false _ _ (eq_false ht)]
          rfl
        have hact := (EGraph.mk E.G s).mark_isWrite m t
        have hst := hs t (Finset.mem_insert_self t s)
        have hthr : t ∈ Q.threads := by
          by_contra hnt
          have hc0 : E.G.cnt t = 0 := by
            by_contra hpos
            obtain ⟨e, he, het, -⟩ := (hG.exists_idx_iff t 0).mpr (Nat.pos_of_ne_zero hpos)
            exact hnt (het ▸ hbase.tid_mem hG he)
          have htr0 : E.G.trace t = [] :=
            List.eq_nil_of_length_eq_zero ((E.G.traceBefore_length t _).trans hc0)
          rw [htr0, Q.step_none t hnt] at hst
          cases hst
        rw [EGraph.psi_insert m E.G ht]
        refine Program.Exec.addWrite hW (ih (fun t' ht' => hs t' (Finset.mem_insert_of_mem ht')))
          (Program.mem_avail_iff.mpr ⟨hthr, hidx, ?_⟩) hact trivial
        change (Q.step t (((EGraph.mk E.G s).psi m).trace t)).map _ = _
        rw [htr t, ite_eq_right_of_eq_false _ _ (eq_false ht), List.append_nil, hst]
        rfl
    exact key E.errs h.2.2
  · intro h
    have hGex := h.of_isPrefixOf (EGraph.psi_wf m hG) (EGraph.isPrefixOf_psi m hG)
    refine ⟨h.1, fun e he => ?_, fun t ht => ?_⟩
    · have h' : (Q.step e.tid (E.G.traceBefore e.tid e.idx)).map (SAct.enc m e.tid) = some e.act :=
        hGex.2 e he
      cases hs : Q.step e.tid (E.G.traceBefore e.tid e.idx) with
      | none =>
        rw [hs] at h'
        cases h'
      | some a =>
        rw [hs] at h'
        have h'' : SAct.enc m e.tid a = e.act := Option.some.inj h'
        cases a with
        | read x => rw [← h'']; rfl
        | write x v => rw [← h'']; rfl
        | err =>
          have := hE.2 e he
          rw [TEv.loc, ← h''] at this
          rw [show (SAct.enc m e.tid .err).loc = m.lam e.tid from rfl, m.own_lam] at this
          cases this
    · have hmk : E.mark m t ∈ (E.psi m).events :=
        (EGraph.mem_psi_events m).mpr (Or.inr ⟨t, ht, rfl⟩)
      have h' := h.2 _ hmk
      have hle : E.G.cnt t ≤ (E.psi m).cnt t := by
        rw [(EGraph.psi_facts m hG E.errs).2.1 t]
        exact Nat.le_add_right _ _
      have htb : (E.psi m).traceBefore t (E.G.cnt t) = E.G.trace t := by
        rw [Graph.traceBefore_eq_take _ t hle, (EGraph.psi_facts m hG E.errs).2.2.1 t]
        exact List.take_left' (E.G.traceBefore_length t _)
      change (Q.step t ((E.psi m).traceBefore t (E.G.cnt t))).map (SAct.enc m t) =
        some (.write (m.lam t) m.ve) at h'
      rw [htb] at h'
      cases hs : Q.step t (E.G.trace t) with
      | none =>
        rw [hs] at h'
        cases h'
      | some a =>
        rw [hs] at h'
        have h'' : SAct.enc m t a = .write (m.lam t) m.ve := Option.some.inj h'
        cases a with
        | read x => cases h''
        | write x v =>
          have hx : x = m.lam t := (Act.write.inj h'').1
          have := (hQ t (E.G.trace t)).2 x v hs
          rw [hx, m.own_lam] at this
          cases this
        | err => rfl

/-- The same with well-formedness and consistency. -/
theorem execESC_iff (hQ : Q.NoMark m) {E : EGraph} (hE : DTail m E) :
    Q.ExecESC E ↔ ExecSC (Q.enc m) (E.psi m) :=
  ⟨fun ⟨_, hex, hc⟩ => ⟨EGraph.psi_wf m hE.1, (execE_iff m hQ hE).mp hex, (psi_cons m hE).mp hc⟩,
    fun ⟨_, hex, hc⟩ => ⟨hE.1, (execE_iff m hQ hE).mpr hex, (psi_cons m hE).mpr hc⟩⟩

/-- Every consistent execution of `Q̂` is `Ψ` of a consistent execution of `Q`. -/
theorem execSC_enc (hQ : Q.NoMark m) {H : Graph} (h : ExecSC (Q.enc m) H) :
    Q.ExecESC (H.psiInv m) ∧ (H.psiInv m).psi m = H := by
  have hD := exec_enc_dHatTail m hQ h.1 h.2.1
  have heq := psi_psiInv m hD
  refine ⟨(execESC_iff m hQ (psiInv_dTail m hD)).mpr ?_, heq⟩
  rw [heq]
  exact h

/-! ### lem:errenc (4) -/

theorem fullE_iff {E : EGraph} (hE : E.G.Wf) :
    Q.FullE E ↔ (Q.enc m).Full (E.psi m) := by
  rw [Program.full_iff]
  refine forall_congr' (fun t => imp_congr_right (fun _ => ?_))
  change _ ↔ (Q.step t ((E.psi m).trace t)).map _ = none
  rw [psi_trace m hE, Option.map_eq_none_iff]

/-- `Ψ` maps `Full(Q)` into `Full(Q̂)`. -/
theorem fullESC_iff (hQ : Q.NoMark m) {E : EGraph} (hE : DTail m E) :
    Q.FullESC E ↔ FullSC (Q.enc m) (E.psi m) :=
  and_congr (execESC_iff m hQ hE) (fullE_iff m hE.1)

/-- ... and onto. -/
theorem fullSC_enc (hQ : Q.NoMark m) {H : Graph} (h : FullSC (Q.enc m) H) :
    Q.FullESC (H.psiInv m) ∧ (H.psiInv m).psi m = H := by
  have hD := exec_enc_dHatTail m hQ h.1.1 h.1.2.1
  have heq := psi_psiInv m hD
  refine ⟨(fullESC_iff m hQ (psiInv_dTail m hD)).mpr ?_, heq⟩
  rw [heq]
  exact h

/-! ### cor:errenc -/

/-- The enumerator of cor:errenc: drop the graphs that fail the marker test
of `D̂`, apply `Ψ⁻¹` to the others. (The test does not check
well-formedness, which a sound enumerator gives.) -/
def encEnum (E₁ : Enumerator) (Q : SProgram) (n : ℕ) : List EGraph :=
  (E₁ (Q.enc m) n).filterMap (fun H => if dHatTailB m H then some (H.psiInv m) else none)

theorem mem_encEnum {E₁ : Enumerator} {n : ℕ} {E : EGraph} :
    E ∈ encEnum m E₁ Q n ↔ ∃ H ∈ E₁ (Q.enc m) n, dHatTailB m H = true ∧ H.psiInv m = E := by
  unfold encEnum
  rw [List.mem_filterMap]
  refine exists_congr (fun H => and_congr_right (fun _ => ?_))
  cases dHatTailB m H <;> simp

theorem encEnum_complete {E₁ : Enumerator} (h₁ : E₁.Complete) (hQ : Q.NoMark m) {n : ℕ}
    (hn : Q.Bounded n) {E : EGraph} (hE : Q.FullESC E) : E ∈ encEnum m E₁ Q n := by
  have hD := hE.1.2.1.dTail m hQ hE.1.1
  exact (mem_encEnum m).mpr ⟨E.psi m,
    h₁ _ n ((Q.enc_bounded m n).mpr hn) _ ((fullESC_iff m hQ hD).mp hE),
    (psi_dHatTail m hD).2, psiInv_psi m hD⟩

theorem encEnum_sound {E₁ : Enumerator} (h₁ : E₁.Sound) (hQ : Q.NoMark m) {n : ℕ}
    (hn : Q.Bounded n) {E : EGraph} (hE : E ∈ encEnum m E₁ Q n) : Q.FullESC E := by
  obtain ⟨H, hH, -, rfl⟩ := (mem_encEnum m).mp hE
  exact (fullSC_enc m hQ (h₁ _ n ((Q.enc_bounded m n).mpr hn) H hH)).1

/-- For a sound enumerator the filter drops nothing. -/
theorem encEnum_eq_map {E₁ : Enumerator} (h₁ : E₁.Sound) (hQ : Q.NoMark m) {n : ℕ}
    (hn : Q.Bounded n) : encEnum m E₁ Q n = (E₁ (Q.enc m) n).map (Graph.psiInv m) := by
  have hall : ∀ H ∈ E₁ (Q.enc m) n, dHatTailB m H = true := fun H hH =>
    have hF := h₁ _ n ((Q.enc_bounded m n).mpr hn) H hH
    (exec_enc_dHatTail m hQ hF.1.1 hF.1.2.1).2
  unfold encEnum
  generalize E₁ (Q.enc m) n = l at hall
  induction l with
  | nil => rfl
  | cons H l ih =>
    rw [List.filterMap_cons, hall H List.mem_cons_self, List.map_cons,
      ih (fun H' hH' => hall H' (List.mem_cons_of_mem _ hH'))]
    rfl

/-- Optimality, for a sound enumerator: `Ψ⁻¹` is injective on `D̂`, and a
graph value listed by an unsound enumerator need not be well-formed. -/
theorem encEnum_optimal {E₁ : Enumerator} (h₁ : E₁.Sound) (h₂ : E₁.Optimal) (hQ : Q.NoMark m)
    {n : ℕ} (hn : Q.Bounded n) : (encEnum m E₁ Q n).Nodup := by
  rw [encEnum_eq_map m h₁ hQ hn]
  refine List.Nodup.map_on (fun H hH H' hH' heq => ?_) (h₂ _ n ((Q.enc_bounded m n).mpr hn))
  have h1 := (fullSC_enc m hQ (h₁ _ n ((Q.enc_bounded m n).mpr hn) H hH)).2
  have h2 := (fullSC_enc m hQ (h₁ _ n ((Q.enc_bounded m n).mpr hn) H' hH')).2
  rw [← h1, ← h2, heq]

/-- With the explorer of TruSt: the list is `Full(Q)` without repetition. -/
theorem encEnum_exploreC (hQ : Q.NoMark m) {n : ℕ} (hn : Q.Bounded n) :
    (encEnum m exploreC Q n).Nodup ∧ ∀ E, E ∈ encEnum m exploreC Q n ↔ Q.FullESC E :=
  ⟨encEnum_optimal m exploreC_sound exploreC_optimal hQ hn, fun _ =>
    ⟨encEnum_sound m exploreC_sound hQ hn, encEnum_complete m exploreC_complete hQ hn⟩⟩

/-! ### Safety by the encoding -/

/-- Safety of `Q` for a property is safety of `Q̂` for its image. -/
theorem safeE_iff (hQ : Q.NoMark m) (Bad : Set EGraph) :
    Q.SafeE Bad ↔ Safe (Q.enc m) SC (EGraph.psi m '' (Bad ∩ {E | DTail m E})) := by
  constructor
  · rintro h G hG ⟨E, ⟨hbad, hD⟩, rfl⟩
    exact h E ((execESC_iff m hQ hD).mpr (greach_iff.mp hG)) hbad
  · intro h E hE hbad
    have hD := hE.2.1.dTail m hQ hE.1
    exact h _ (greach_iff.mpr ((execESC_iff m hQ hD).mp hE)) ⟨E, ⟨hbad, hD⟩, rfl⟩

/-- Assertion safety of `Q` is: no reachable graph of `Q̂` has an event on a
marker. -/
theorem safeE_badErr_iff (hQ : Q.NoMark m) :
    Q.SafeE BadErr ↔ Safe (Q.enc m) SC (BadMark m) := by
  constructor
  · rintro h G hG ⟨e, he, hm⟩
    have hG' := greach_iff.mp hG
    have hD := exec_enc_dHatTail m hQ hG'.1 hG'.2.1
    obtain ⟨t, ht⟩ := m.isMark_eq_true_iff.mp hm
    exact h _ (execSC_enc m hQ hG').1 ⟨t, (mem_psiInv_errs hD).mpr ⟨e, he, ht⟩⟩
  · rintro h E hE ⟨t, ht⟩
    have hD := hE.2.1.dTail m hQ hE.1
    exact h _ (greach_iff.mpr ((execESC_iff m hQ hD).mp hE))
      ⟨E.mark m t, (EGraph.mem_psi_events m).mpr (Or.inr ⟨t, ht, rfl⟩), E.isMark_mark m t⟩

/-- `BadMark` is extension-closed. -/
theorem badMark_extClosed (P : Program) : ExtClosed P (BadMark m) := by
  rintro G G' - - ⟨e, he, hm⟩ ⟨s, -, rfl⟩
  exact ⟨e, (Finset.mem_inter.mp he).1, hm⟩

/-- cor:enum (1) for the assertion property of a simple program: if `Check`
with the explorer accepts on the encoding, `Q` is safe for `Bad_err`. -/
theorem check_sound_err {A : Type} [DecidableEq A] (hQ : Q.NoMark m)
    (Abs : Abstraction (Q.enc m) A) {abad : A → Bool}
    (hdet : Abs.Determines (BadMark m) {a | abad a = true})
    {B : List A} (hinit : Abs.α (Graph.init (Q.enc m).mem) ∈ B)
    (hdisj : ∀ b ∈ B, abad b = false) {K : ℕ} (hK : 1 ≤ K) (f : A → Graph → A)
    (hf : ∀ G, ExecSC (Q.enc m) G → Abs.α G ∈ B →
      ∀ H, GReach ((Q.enc m).residual G.trace G.memOf) SC H → H.size ≤ K + 1 →
        f (Abs.α G) H = Abs.α (G.comp H))
    (hacc : (Check exploreC (Q.enc m) B abad Abs.u Abs.μ f K).1 = true) : Q.SafeE BadErr :=
  (safeE_badErr_iff m hQ).mpr
    (check_sound Abs hdet (badMark_extClosed m _) hinit hdisj hK f hf hacc)

end Trust
