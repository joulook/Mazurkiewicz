import Mazurkiewicz.Must.Ops

/-!
# More lemmas on the operations

* Restriction of the relations and sets (`po`, `rfRel`, `mval`, `S`, `R`).
* Restriction and addition commute or cancel; a graph is a prefix of its addition; `porf` into a
  new event; removing a `porf`-maximal event and adding it back.
* `setRF`: unread sends after a change of source (the old real source is released), causality
  steps kept.
* Prefixes: same sources and outcomes, `porf` contained, strictly fewer events if different.
* The revisit successor of plan decision Q15, `revisit H r s Del`, and `Wf.revisit`.
-/

namespace Must

namespace Graph

open Relation

variable {Q : Type} [DecidableEq Q] {G : Graph Q}

/-! ### Restriction of relations and sets -/

@[simp] theorem po_restrict_iff {E : Finset (Ev Q)} {a b : Ev Q} :
    (G.restrict E).po a b ↔ G.po a b ∧ a ∈ E ∧ b ∈ E := by
  simp only [po, restrict_events, Finset.mem_inter]
  tauto

@[simp] theorem rfRel_restrict_iff {E : Finset (Ev Q)} {s r : Ev Q} :
    (G.restrict E).rfRel s r ↔ G.rfRel s r ∧ r ∈ E := by
  simp only [rfRel, restrict_events, Finset.mem_inter, restrict_rf]
  by_cases h : r ∈ E <;> simp [h]

@[simp] theorem mval_restrict_iff [Membership Val Q] {E : Finset (Ev Q)} {s r : Ev Q} :
    (G.restrict E).mval s r ↔ G.mval s r ∧ s ∈ E ∧ r ∈ E := by
  simp only [mval, restrict_events, Finset.mem_inter]
  tauto

@[simp] theorem mem_S_restrict {E : Finset (Ev Q)} {e : Ev Q} :
    e ∈ (G.restrict E).S ↔ e ∈ G.S ∧ e ∈ E := by
  simp only [mem_S, restrict_events, Finset.mem_inter]
  tauto

@[simp] theorem mem_R_restrict {E : Finset (Ev Q)} {e : Ev Q} :
    e ∈ (G.restrict E).R ↔ e ∈ G.R ∧ e ∈ E := by
  simp only [mem_R, restrict_events, Finset.mem_inter]
  tauto

/-! ### Restriction and addition -/

variable {e : Ev Q} {src : Option (Src Q)} {out : Option Val}

theorem restrict_add_of_mem {E : Finset (Ev Q)} (he : e ∈ E) :
    (G.add e src out).restrict E = (G.restrict E).add e src out := by
  apply Graph.ext
  · ext q
    simp only [restrict_events, add_events, Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | h, hq⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨h, hq⟩
    · rintro (rfl | ⟨h, hq⟩)
      · exact ⟨Or.inl rfl, he⟩
      · exact ⟨Or.inr h, hq⟩
  · funext q
    by_cases hq : q = e
    · subst hq
      simp [he]
    · simp [Function.update_of_ne hq]
  · funext q
    by_cases hq : q = e
    · subst hq
      simp [he]
    · simp [Function.update_of_ne hq]

theorem restrict_add_of_not_mem {E : Finset (Ev Q)} (he : e ∉ E) :
    (G.add e src out).restrict E = G.restrict E := by
  apply Graph.ext
  · ext q
    simp only [restrict_events, add_events, Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | h, hq⟩
      · exact absurd hq he
      · exact ⟨h, hq⟩
    · rintro ⟨h, hq⟩
      exact ⟨Or.inr h, hq⟩
  · funext q
    by_cases hq : q ∈ E
    · have hne : q ≠ e := fun h => he (h ▸ hq)
      simp [hq, Function.update_of_ne hne]
    · simp [hq]
  · funext q
    by_cases hq : q ∈ E
    · have hne : q ≠ e := fun h => he (h ▸ hq)
      simp [hq, Function.update_of_ne hne]
    · simp [hq]

variable [Membership Val Q]

/-- A graph is a prefix of its addition of the next event of a thread. -/
theorem Wf.isPrefixOf_add (hG : G.Wf) (hidx : e.idx = G.cnt e.tid) :
    G.IsPrefixOf (G.add e src out) := by
  have he := hG.not_mem_of_idx_eq_cnt hidx
  refine ⟨G.events, fun a b hab hb => ?_, ?_⟩
  · have hb := Finset.mem_coe.mp hb
    have hbG : b ∈ G.events := (Finset.mem_inter.mp hb).2
    have hne : b ≠ e := fun h => he (h ▸ hbG)
    rcases hG.porfStep_add_cases hidx hab with h | h
    · have ha := (hG.mem_of_porfStep h).1
      exact Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem ha, ha⟩)
    · exact absurd h hne
  · rw [restrict_add_of_not_mem he, hG.restrict_self]

/-- `porf` into the new event: a last step into it, after a `porf` path of `G` or nothing. -/
theorem Wf.porf_add_right_iff (hG : G.Wf) (hidx : e.idx = G.cnt e.tid)
    (hsrc : ∀ s, src = some (.snd s) → s ∈ G.events) {a : Ev Q} :
    (G.add e src out).porf a e ↔
      ∃ c, ((c ∈ G.events ∧ c.tid = e.tid) ∨ src = some (.snd c)) ∧
        ReflTransGen G.porfStep a c := by
  have he := hG.not_mem_of_idx_eq_cnt hidx
  have hcG : ∀ c, ((c ∈ G.events ∧ c.tid = e.tid) ∨ src = some (.snd c)) → c ∈ G.events :=
    fun c h => h.elim (·.1) (hsrc c)
  constructor
  · intro h
    obtain ⟨c, hac, hce⟩ := TransGen.tail'_iff.mp h
    have hc := (hG.porfStep_add_right_iff hidx).mp hce
    have hne : c ≠ e := fun h' => he (h' ▸ hcG c hc)
    refine ⟨c, hc, ?_⟩
    rcases reflTransGen_iff_eq_or_transGen.mp hac with h' | h'
    · rw [h']
    · exact ((hG.porf_add_iff hidx hsrc hne).mp h').to_reflTransGen
  · rintro ⟨c, hc, hac⟩
    have hce := (hG.porfStep_add_right_iff hidx (out := out)).mpr hc
    refine TransGen.tail'_iff.mpr ⟨c, ?_, hce⟩
    exact hac.lift id (fun _ _ h => hG.porfStep_add_of_porfStep hidx h)

omit [DecidableEq Q] in
/-- An event with no outgoing causality step is the last of its thread. -/
theorem Wf.idx_eq_of_maximal (hG : G.Wf) {e : Ev Q} (he : e ∈ G.events)
    (hmax : ∀ b, ¬ G.porfStep e b) : e.idx + 1 = G.cnt e.tid := by
  have hlt := hG.idx_lt_cnt he
  by_contra hne
  obtain ⟨b, hb, ht, hi⟩ := (hG.exists_idx_iff e.tid (e.idx + 1)).mpr (by omega)
  exact hmax b (Or.inl ⟨he, hb, ht.symm, by omega⟩)

/-- Removing an event with no outgoing causality step gives a graph of which it is the next
event of its thread. -/
theorem Wf.idx_eq_cnt_remove (hG : G.Wf) {e : Ev Q} (he : e ∈ G.events)
    (hmax : ∀ b, ¬ G.porfStep e b) : e.idx = (G.remove {e}).cnt e.tid := by
  have h1 := hG.idx_eq_of_maximal he hmax
  have hev : (G.remove {e}).events = G.events.erase e := by
    ext q
    simp only [Graph.remove, restrict_events, Finset.mem_inter, Finset.mem_sdiff,
      Finset.mem_singleton, Finset.mem_erase]
    tauto
  have hc : (G.remove {e}).cnt e.tid + 1 = G.cnt e.tid := by
    unfold cnt
    rw [hev, Finset.filter_erase]
    exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨he, rfl⟩)
  omega

/-- Removing an event of the graph and adding it back with its source and outcome gives the
graph. -/
theorem Wf.add_remove (hG : G.Wf) {e : Ev Q} (he : e ∈ G.events) :
    (G.remove {e}).add e (G.rf e) (G.nd e) = G := by
  apply Graph.ext
  · ext q
    simp only [add_events, Graph.remove, restrict_events, Finset.mem_insert, Finset.mem_inter,
      Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro (rfl | ⟨h, -⟩)
      · exact he
      · exact h
    · intro h
      by_cases hq : q = e
      · exact Or.inl hq
      · exact Or.inr ⟨h, h, hq⟩
  · funext q
    by_cases hq : q = e
    · subst hq
      simp
    · rw [add_rf, Function.update_of_ne hq]
      simp only [Graph.remove, restrict_rf, Finset.mem_sdiff, Finset.mem_singleton]
      split_ifs with h
      · rfl
      · exact (hG.rf_none (Or.inl fun h' => h ⟨h', hq⟩)).symm
  · funext q
    by_cases hq : q = e
    · subst hq
      simp
    · rw [add_nd, Function.update_of_ne hq]
      simp only [Graph.remove, restrict_nd, Finset.mem_sdiff, Finset.mem_singleton]
      split_ifs with h
      · rfl
      · exact (hG.nd_none (Or.inl fun h' => h ⟨h', hq⟩)).symm

/-! ### Changing a source -/

variable {r : Ev Q} {x : Src Q}

omit [Membership Val Q] in
/-- The unread sends after `setRF r x`, for a receive `r` of the graph. -/
theorem mem_US_setRF (hr : r ∈ G.events) {s' : Ev Q} :
    s' ∈ (G.setRF r x).US ↔
      s' ∈ G.events ∧ s'.IsSend ∧ x ≠ .snd s' ∧
        ∀ r' ∈ G.events, r' ≠ r → G.rf r' ≠ some (.snd s') := by
  rw [mem_US, setRF_events]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun h => h3 r hr (by rw [setRF_rf, Function.update_self, h]), ?_⟩
    intro r' hr' hne
    have := h3 r' hr'
    rwa [setRF_rf, Function.update_of_ne hne] at this
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, fun r' hr' => ?_⟩
    by_cases hne : r' = r
    · rw [hne, setRF_rf, Function.update_self]
      exact fun h => h3 (Option.some.inj h)
    · rw [setRF_rf, Function.update_of_ne hne]
      exact h4 r' hr' hne

/-- The old real source of `r` becomes unread when the new source is different. -/
theorem Wf.old_source_mem_US_setRF (hG : G.Wf) {s₀ : Ev Q} (hold : G.rf r = some (.snd s₀))
    (hne : x ≠ .snd s₀) : s₀ ∈ (G.setRF r x).US := by
  have hr := (hG.rf_some hold).1
  refine (mem_US_setRF hr).mpr ⟨hG.rf_mem _ _ hold, (hG.rf_match _ _ hold).isSend, hne, ?_⟩
  intro r' _ hr' h
  exact hr' (hG.rf_once _ _ _ h hold)

omit [Membership Val Q] in
/-- `po` is unchanged by `setRF`. -/
@[simp] theorem po_setRF {a b : Ev Q} : (G.setRF r x).po a b ↔ G.po a b := Iff.rfl

omit [Membership Val Q] in
/-- A causality step into an event other than `r` is kept by `setRF`. -/
theorem porfStep_setRF_of {a b : Ev Q} (h : G.porfStep a b) (hb : b ≠ r) :
    (G.setRF r x).porfStep a b := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, by rw [setRF_rf, Function.update_of_ne hb]; exact h2⟩

omit [Membership Val Q] in
/-- The new edge of `setRF r (.snd s)`. -/
theorem porfStep_setRF_new (hr : r ∈ G.events) (s : Ev Q) :
    (G.setRF r (.snd s)).porfStep s r :=
  Or.inr ⟨hr, by rw [setRF_rf, Function.update_self]⟩

/-! ### Prefixes -/

omit [Membership Val Q] in
/-- A prefix has the sources of the larger graph on its events. -/
theorem IsPrefixOf.rf_eq {G' : Graph Q} (h : G'.IsPrefixOf G) {e : Ev Q} (he : e ∈ G'.events) :
    G'.rf e = G.rf e := by
  obtain ⟨E, -, rfl⟩ := h
  simp only [restrict_rf, (Finset.mem_inter.mp he).2, ↓reduceIte]

omit [Membership Val Q] in
/-- A prefix has the outcomes of the larger graph on its events. -/
theorem IsPrefixOf.nd_eq {G' : Graph Q} (h : G'.IsPrefixOf G) {e : Ev Q} (he : e ∈ G'.events) :
    G'.nd e = G.nd e := by
  obtain ⟨E, -, rfl⟩ := h
  simp only [restrict_nd, (Finset.mem_inter.mp he).2, ↓reduceIte]

omit [Membership Val Q] in
theorem IsPrefixOf.porf_le {G' : Graph Q} (h : G'.IsPrefixOf G) {a b : Ev Q}
    (hab : G'.porf a b) : G.porf a b := by
  obtain ⟨E, -, rfl⟩ := h
  exact porf_restrict_le E hab

omit [Membership Val Q] in
/-- `porf` of a prefix into one of its events is `porf` of the larger graph. -/
theorem IsPrefixOf.porf_iff {G' : Graph Q} (h : G'.IsPrefixOf G) {a b : Ev Q}
    (hb : b ∈ G'.events) : G'.porf a b ↔ G.porf a b := by
  obtain ⟨E, hE, rfl⟩ := h
  exact porf_restrict_iff hE hb

/-- A prefix different from a well-formed graph has strictly fewer events. -/
theorem IsPrefixOf.card_lt {G' : Graph Q} (hG : G.Wf) (h : G'.IsPrefixOf G) (hne : G' ≠ G) :
    G'.events.card < G.events.card := by
  have hsub := h.events_subset
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun hev => hne ?_⟩)
  obtain ⟨E, -, rfl⟩ := h
  refine hG.restrict_of_subset (fun q hq => ?_)
  rw [← hev] at hq
  exact (Finset.mem_inter.mp hq).2

/-! ### The revisit successor (Q15) -/

variable (G) in
/-- The revisit of the receive `r` by the send `s`, deleting `Del`: `r` reads `s`, then the
events of `Del` are removed. -/
def revisit (r s : Ev Q) (Del : Finset (Ev Q)) : Graph Q :=
  (G.setRF r (.snd s)).restrict (G.events \ Del)

/-- The revisit successor is well-formed when `s` is a matching send read by no other receive
and not causally after `r`, `s` is kept, and the kept set is closed under
`po`-predecessors and contains the sources of the kept receives other than `r`. -/
theorem Wf.revisit (hG : G.Wf) {r s : Ev Q} {Del : Finset (Ev Q)} (hr : r ∈ G.events)
    (hs : s ∈ G.events) (hm : s.Matches r)
    (hread : ∀ r' ∈ G.events, r' ≠ r → G.rf r' ≠ some (.snd s)) (hcyc : ¬ G.porf r s)
    (hsD : s ∉ Del)
    (hpo : ∀ a b, G.po a b → b ∉ Del → a ∉ Del)
    (hsrc : ∀ q ∈ G.events, q ∉ Del → q ≠ r → ∀ s', G.rf q = some (.snd s') → s' ∉ Del) :
    (G.revisit r s Del).Wf := by
  have h1 : (G.setRF r (.snd s)).Wf :=
    hG.setRF hr (fun h => by cases h) (fun s' h => by cases h; exact ⟨hs, hm, hread, hcyc⟩)
  refine h1.restrict_of (fun a b hab hb => ?_) (fun q hq s' hs' => ?_)
  · have hab' : G.po a b := hab
    have hb' := Finset.mem_sdiff.mp hb
    exact Finset.mem_sdiff.mpr ⟨hab'.1, hpo a b hab' hb'.2⟩
  · obtain ⟨hqG, hqE⟩ := Finset.mem_inter.mp hq
    have hqD := (Finset.mem_sdiff.mp hqE).2
    by_cases hqr : q = r
    · rw [hqr, setRF_rf, Function.update_self] at hs'
      cases hs'
      exact Finset.mem_sdiff.mpr ⟨hs, hsD⟩
    · rw [setRF_rf, Function.update_of_ne hqr] at hs'
      exact Finset.mem_sdiff.mpr ⟨hG.rf_mem _ _ hs', hsrc q hqG hqD hqr s' hs'⟩

end Graph

end Must
