import Mazurkiewicz.Induction.Budgets

/-!
# Obligations over full executions

`induction-popl`, `dpor.tex` sec:full-obl: thm:full-prefix, def:extclosed,
lem:compose-mono, thm:full-ext.

How the text is read here.

* The paper fixes a compositional abstraction, a realised `b ∈ B` and writes
  `b ⊙ F`. Here the theorems are stated for a graph `G` (a witness of
  `b = α G`; thm:full-ext asks `ExecSC P G`), with `α (G.comp F)` for
  `b ⊙ F`. Neither `α G ∈ B`, nor that the abstraction is compositional, nor
  `1 ≤ K` is assumed: the proofs do not use them in this form. "The
  obligation of `b` holds" is `Abs.StepOK Abad B K G`
  (equivalent to the safety of the obligation program of `α G` by
  `Abstraction.stepOK_iff_obligation`, when `ExecSC P G` holds; without it
  both sides of thm:full-prefix still speak of the residual on the traces of
  `G` and of the total composition, and are equivalent).
* `Q` is the residual program `P.residual G.trace G.memOf`.
* lem:compose-mono is stated with the hypothesis that `G ⊙ F` is well-formed
  (which holds when `F` is consistent with `F.mem = mem_G`, by
  lem:compose-graph); no hypothesis on memories is needed.
* The direction (⇐) of both theorems needs `P.threads ≠ []` (prop:cover (1)).
-/

namespace Trust

open Program

/-- `Bad` is extension-closed for `P` (def:extclosed). -/
def ExtClosed (P : Program) (Bad : Set Graph) : Prop :=
  ∀ G G', ExecSC P G → ExecSC P G' → G ∈ Bad → G.IsPrefixOf G' → G' ∈ Bad

/-! ### lem:compose-mono -/

/-- lem:compose-mono: composition is monotone in the fragment. -/
theorem Graph.comp_isPrefixOf_comp {G H F : Graph} (hG : G.Wf) (hF : F.Wf)
    (hGF : (G.comp F).Wf) (h : H.IsPrefixOf F) : (G.comp H).IsPrefixOf (G.comp F) := by
  obtain ⟨sH, hcl, rfl⟩ := h
  let s : Finset TEv := G.events ∪ (F.events ∩ sH).image G.emb
  have hs_sub : s ⊆ (G.comp F).events := by
    intro q hq
    rcases Finset.mem_union.mp hq with h | h
    · exact Finset.mem_union_left _ h
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_inter.mp hr).1)
  have hinter : (G.comp F).events ∩ s = s := Finset.inter_eq_right.mpr hs_sub
  have hemb_s : ∀ r, G.emb r ∈ s ↔ r ∈ F.events ∩ sH := by
    intro r
    constructor
    · intro h
      rcases Finset.mem_union.mp h with h | h
      · exact absurd h (Graph.emb_not_mem hG r)
      · obtain ⟨r', hr', he⟩ := Finset.mem_image.mp h
        rw [← G.emb_injective he]
        exact hr'
    · exact fun h => Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
  have hGs : ∀ q ∈ G.events, q ∈ s := fun q hq => Finset.mem_union_left _ hq
  -- the sources of the kept events of `F` are kept
  have hsrcF : ∀ r ∈ F.events ∩ sH, ∀ w, F.rf r = some w →
      w ∈ Graph.evSet (F.events ∩ sH) := fun r hr w hw =>
    hcl (Or.inr ⟨r, rfl, (Finset.mem_inter.mp hr).1, hw⟩) hr
  have hHrf : ∀ r ∈ F.events ∩ sH, (F.restrict sH).rf r = F.rf r := fun r hr =>
    F.restrict_rf_of_source_kept hr
      (fun w hw => Graph.evSet_mono Finset.inter_subset_right (hsrcF r hr w hw))
  -- the embedded source of a kept event is kept
  have hsrc_emb : ∀ r ∈ F.events ∩ sH, ∀ w, F.rf r = some w →
      G.embSrc r.loc w ∈ Graph.evSet s := by
    intro r hr w hw
    cases w with
    | init =>
      have hm := Graph.maxWrite_isWriteTo hG r.loc
      change G.maxWrite r.loc ∈ Graph.evSet s
      cases hmw : G.maxWrite r.loc with
      | init => trivial
      | th m =>
        rw [hmw] at hm
        exact hGs m hm.1
    | th w' => exact (hemb_s w').mpr (hsrcF r hr _ hw)
  refine ⟨s, ?_, ?_⟩
  · -- prefix-closed
    rw [hinter]
    intro a b hab hb
    cases a with
    | init => trivial
    | th p =>
      have hpC : p ∈ (G.comp F).events := (hGF.mem_of_porfStep hab).1
      cases b with
      | init => exact absurd hab ((G.comp F).not_porfStep_init _)
      | th q =>
        have hq : q ∈ s := hb
        change p ∈ s
        rcases hab with hpo | ⟨q', hq', -, hrf⟩
        · obtain ⟨-, -, ht, hi⟩ := hpo
          rcases Finset.mem_union.mp hpC with hp | hp
          · exact hGs p hp
          · obtain ⟨r', hr', rfl⟩ := Finset.mem_image.mp hp
            rcases Finset.mem_union.mp hq with hqG | hqI
            · exfalso
              have h1 := G.cnt_le_emb_idx r'
              rw [ht] at h1
              exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt h1 (hi.trans (hG.idx_lt_cnt hqG)))
            · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hqI
              have ht' : r'.tid = r.tid := ht
              have hi' : G.cnt r'.tid + r'.idx < G.cnt r.tid + r.idx := hi
              rw [ht'] at hi'
              have hstep : F.porfStep (.th r') (.th r) :=
                Or.inl (show F.po (.th r') (.th r) from
                  ⟨hr', (Finset.mem_inter.mp hr).1, ht', Nat.lt_of_add_lt_add_left hi'⟩)
              exact (hemb_s r').mpr (hcl hstep hr)
        · rw [← Ev.th.inj hq'] at hrf
          rcases Finset.mem_union.mp hq with hqG | hqI
          · rw [Graph.comp_rf_old hqG] at hrf
            exact hGs p (hG.rf_source_mem hrf).2
          · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hqI
            rw [Graph.comp_rf_emb hG (Finset.mem_inter.mp hr).1] at hrf
            cases hfr : F.rf r with
            | none =>
              rw [hfr] at hrf
              cases hrf
            | some w =>
              rw [hfr] at hrf
              have := hsrc_emb r hr w hfr
              rw [Option.some.inj hrf] at this
              exact this
  · -- the restriction is the composition with the prefix
    apply Graph.ext
    · rfl
    · change G.events ∪ (F.restrict sH).events.image G.emb = (G.comp F).events ∩ s
      rw [hinter]
      rfl
    · funext q
      by_cases hq : q ∈ s
      · have hq' : q ∈ (G.comp F).events ∩ s := hinter.symm ▸ hq
        rcases Finset.mem_union.mp hq with hqG | hqI
        · rw [Graph.comp_rf_old hqG, (G.comp F).restrict_rf_of_source_kept hq' (fun w hw => ?_),
            Graph.comp_rf_old hqG]
          rw [Graph.comp_rf_old hqG] at hw
          cases w with
          | init => trivial
          | th w' => exact hGs w' (hG.rf_source_mem hw).2
        · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hqI
          have hrF := (Finset.mem_inter.mp hr).1
          rw [Graph.comp_rf_emb hG (show r ∈ (F.restrict sH).events from hr), hHrf r hr,
            (G.comp F).restrict_rf_of_source_kept hq' (fun w hw => ?_),
            Graph.comp_rf_emb hG hrF]
          rw [Graph.comp_rf_emb hG hrF] at hw
          cases hfr : F.rf r with
          | none =>
            rw [hfr] at hw
            cases hw
          | some w₀ =>
            rw [hfr] at hw
            rw [← Option.some.inj hw]
            exact hsrc_emb r hr w₀ hfr
      · have hqG : q ∉ G.events := fun h => hq (hGs q h)
        rw [(G.comp F).restrict_rf_of_not_mem (fun h => hq (Finset.mem_inter.mp h).2),
          Graph.comp_rf_none hqG (fun h => hq ?_)]
        rw [← G.emb_unemb h.2]
        exact (hemb_s _).mpr h.1
    · funext x
      change G.co x ++ ((F.co x).filter (fun e => decide (e ∈ sH))).map G.emb =
        (G.co x ++ (F.co x).map G.emb).filter (fun e => decide (e ∈ s))
      rw [List.filter_append, List.filter_map]
      congr 1
      · symm
        refine List.filter_eq_self.mpr (fun w hw => ?_)
        exact decide_eq_true (hGs w ((hG.co_mem x w).mp hw).1)
      · congr 1
        apply List.filter_congr
        intro w hw
        have hwF := ((hF.co_mem x w).mp hw).1
        have := hemb_s w
        simp only [Finset.mem_inter, hwF, true_and] at this
        simp [this]

variable {P : Program} {A : Type} (Abs : Abstraction P A)

/-! ### thm:full-prefix and thm:full-ext -/

/-- thm:full-prefix. -/
theorem Abstraction.stepOK_iff_full_prefix (hne : P.threads ≠ []) {Abad B : Set A} {K : ℕ}
    {G : Graph} :
    Abs.StepOK Abad B K G ↔
      ∀ κ, IsBudget P.threads K κ → ∀ F, FullSC ((P.residual G.trace G.memOf).trunc κ) F →
        (F.size = K + 1 → Abs.α (G.comp F) ∈ B) ∧
        ∀ H, H.IsPrefixOf F → H.size ≤ K → Abs.α (G.comp H) ∉ Abad := by
  constructor
  · intro hok κ hκ F hF
    have hκ' : IsBudget (P.residual G.trace G.memOf).threads K κ := hκ
    refine ⟨fun hsz => ?_, fun H hp hsz => ?_⟩
    · exact (hok F (cover_prefix hκ' hF hF.1.1.isPrefixOf_refl).1).1 hsz
    · exact (hok H (cover_prefix hκ' hF hp).1).2 hsz
  · intro h H hH
    have hne' : (P.residual G.trace G.memOf).threads ≠ [] := hne
    refine ⟨fun hsz => ?_, fun hsz => ?_⟩
    · obtain ⟨hκ, hfull⟩ := cover_full hH hsz
      exact (h _ hκ H hfull).1 hsz
    · obtain ⟨κ, hκ, F, hF, hp⟩ := cover_exists hne' (K := K) hH (by omega)
      exact (h κ hκ F hF).2 H hp hsz

/-- thm:full-ext. -/
theorem Abstraction.stepOK_iff_full (hne : P.threads ≠ []) {Bad : Set Graph} {Abad B : Set A}
    {K : ℕ} (hdet : Abs.Determines Bad Abad) (hext : ExtClosed P Bad)
    (hdisj : ∀ b ∈ B, b ∉ Abad) {G : Graph} (hG : ExecSC P G) :
    Abs.StepOK Abad B K G ↔
      ∀ κ, IsBudget P.threads K κ → ∀ F, FullSC ((P.residual G.trace G.memOf).trunc κ) F →
        (F.size = K + 1 → Abs.α (G.comp F) ∈ B) ∧
        (F.size ≤ K → Abs.α (G.comp F) ∉ Abad) := by
  rw [Abs.stepOK_iff_full_prefix hne]
  constructor
  · intro h κ hκ F hF
    exact ⟨(h κ hκ F hF).1, fun hsz => (h κ hκ F hF).2 F hF.1.1.isPrefixOf_refl hsz⟩
  · intro h κ hκ F hF
    refine ⟨(h κ hκ F hF).1, fun H hp hsz hbad => ?_⟩
    have hκ' : IsBudget (P.residual G.trace G.memOf).threads K κ := hκ
    obtain ⟨hHr, -⟩ := cover_prefix hκ' hF hp
    obtain ⟨hFr, hFsz⟩ := cover_prefix hκ' hF hF.1.1.isPrefixOf_refl
    have hGH := greach_iff.mp (greach_comp hG hHr).1
    have hGF := greach_iff.mp (greach_comp hG hFr).1
    have hbadH : G.comp H ∈ Bad := (hdet _ hGH).mpr hbad
    have hpre := Graph.comp_isPrefixOf_comp hG.1 hF.1.1 hGF.1 hp
    have hbadF : Abs.α (G.comp F) ∈ Abad := (hdet _ hGF).mp (hext _ _ hGH hGF hbadH hpre)
    by_cases hle : F.size ≤ K
    · exact (h κ hκ F hF).2 hle hbadF
    · exact hdisj _ ((h κ hκ F hF).1 (by omega)) hbadF

end Trust
