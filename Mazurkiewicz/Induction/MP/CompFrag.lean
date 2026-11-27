import Mazurkiewicz.Induction.MP.SeedCompRet
import Mazurkiewicz.Induction.MP.StepsModel
import Mazurkiewicz.Induction.MP.StepsMore

/-!
# Message passing: composition of fragments (milestone C4a)

`induction-popl`, `mp.tex` lem:mp-compose (1), (3), (4) and `p2p.tex` lem:p2p-compose (1),
(3), (4), for the one construction `Graph.scomp` over a setting `S : MPSetting Q` (plan
`plan/ind/TRACK-C-PLAN.md`, milestone C4a).

Context (plan C4a, section variables): `S : MPSetting Q`, `M := Model.ofSet S.ms` (written
out), `hG : ExecM M S.P G`, `hu : ∀ t ∈ S.P.threads, FutEq (S.P.step t) (u t) (G.trace t)`,
`hW : ∀ t ∉ S.ts, W t = []`, `hρ : SeedOK G S.m W ρ S.ord`, `R := S.P.seedRes S.ι S.hι S.m u W`
(written out). Each theorem takes the context hypotheses its proof uses.

* `frag_scomp` (lem:mp-compose (1), lem:p2p-compose (3)): `G ⊕ H` is a consistent execution of
  `P` with `G` as a prefix. Proof (plan, "proof strategy"): along a derivation
  `Z_w →* H` (`isPrefixOf_opLe`), with `scomp_seed` and `scomp_add`; each step of `R` from a
  fragment is a step of `P` from the composition (`fwd_step`).
* `us_scomp` (`US(G ⊕ H) = ê(US(H))`), `pendM_scomp`, `pend_scomp` (needs `S.ord`; false with
  `ord = False`, Opus B1, plan Section 4.1) (lem:mp-compose (3), lem:p2p-compose (1)).
* `scomp_mono` (lem:mp-compose (4), lem:p2p-compose (4)), `frag_scomp_injective`.
* Helpers: `Ev.matches_congr`, `Ev.valMatches_congr`, `msgOf_congr`, `soDst_iff`, facts on
  `Graph.unreadSeq` (`unreadEvAt_spec`, `mem_unreadSeq`, `unreadSeq_pairwise`),
  `eq_of_pairwise_idx`; `frag_wf`, `frag_seed_eq`, `frag_tid`, `frag_step`; `cons_addRecv_scomp`
  (the receive case of the forward step), `fwd_step`.
-/

namespace Must

open Graph Relation

/-! ### Generic helpers -/

namespace Ev

variable {Q : Type} [Membership Val Q]

theorem matches_congr {s s' r r' : Ev Q} (hs : s.lab = s'.lab) (hr : r.lab = r'.lab)
    (ht : r.tid = r'.tid) : s.Matches r ↔ s'.Matches r' := by
  unfold Matches
  rw [hs, hr, ht]

theorem valMatches_congr {s s' r r' : Ev Q} (hs : s.lab = s'.lab) (hr : r.lab = r'.lab) :
    s.ValMatches r ↔ s'.ValMatches r' := by
  unfold ValMatches
  rw [hs, hr]

end Ev

namespace Ind

variable {Q : Type} [DecidableEq Q] [Membership Val Q]

omit [DecidableEq Q] [Membership Val Q] in
theorem msgOf_congr {a b : Ev Q} (h : a.lab = b.lab) : msgOf a = msgOf b := by
  unfold msgOf
  rw [h]

omit [DecidableEq Q] [Membership Val Q] in
/-- The port's `so|dst` is `soP2P` with the same destination. -/
theorem soDst_iff {G : Graph Q} {a b : Ev Q} :
    G.SoDst a b ↔ G.soP2P a b ∧ a.lab.dst? = b.lab.dst? := by
  unfold Graph.SoDst Graph.soP2P Graph.soP2PWith Ev.SendOf
  rw [Model.dstOf_eq, Model.dstOf_eq]
  tauto

omit [DecidableEq Q] [Membership Val Q] in
/-- Two lists of events strictly sorted by index with the same members are equal. -/
theorem eq_of_pairwise_idx {l₁ l₂ : List (Ev Q)} (h₁ : l₁.Pairwise (fun a b => a.idx < b.idx))
    (h₂ : l₂.Pairwise (fun a b => a.idx < b.idx)) (hm : ∀ a, a ∈ l₁ ↔ a ∈ l₂) : l₁ = l₂ := by
  have hn : ∀ {l : List (Ev Q)}, l.Pairwise (fun a b => a.idx < b.idx) → l.Nodup :=
    fun h => h.imp fun {a b} h' e => by subst e; exact lt_irrefl _ h'
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => absurd (hab.trans hba) (lt_irrefl _))
    h₁ h₂ ((List.perm_ext_iff_of_nodup (hn h₁) (hn h₂)).mpr hm)

/-! ### Unread sends of a thread in index order -/

omit [Membership Val Q] in
theorem unreadEvAt_spec {G : Graph Q} {t i : ℕ} {e : Ev Q} (h : G.unreadEvAt t i = some e) :
    e ∈ G.US ∧ e.tid = t ∧ e.idx = i := by
  unfold Graph.unreadEvAt at h
  split at h
  · next hex =>
    cases h
    exact Classical.choose_spec hex
  · cases h

theorem mem_unreadSeq {G : Graph Q} (hG : G.Wf) {t : Tid} {s : Ev Q} :
    s ∈ G.unreadSeq t ↔ s ∈ G.US ∧ s.tid = t := by
  unfold Graph.unreadSeq
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨i, -, h⟩
    exact ⟨(unreadEvAt_spec h).1, (unreadEvAt_spec h).2.1⟩
  · rintro ⟨hs, rfl⟩
    exact ⟨s.idx, List.mem_range.mpr (hG.idx_lt_cnt ((G.mem_US).mp hs).1), hG.unreadEvAt_eq hs⟩

omit [Membership Val Q] in
theorem unreadSeq_pairwise (G : Graph Q) (t : Tid) :
    (G.unreadSeq t).Pairwise (fun a b => a.idx < b.idx) := by
  unfold Graph.unreadSeq
  rw [List.pairwise_filterMap]
  refine List.pairwise_lt_range.imp fun {i j} hij a ha b hb => ?_
  rw [(unreadEvAt_spec (Option.mem_def.mp ha)).2.2, (unreadEvAt_spec (Option.mem_def.mp hb)).2.2]
  exact hij

/-! ### The context -/

variable (S : MPSetting Q) {G H H' F : Graph Q} {u : Tid → List (Option Val)}
  {W : Tid → List Msg} {ρ : Ev Q → Ev Q}
variable (hG : ExecM (Model.ofSet S.ms) S.P G)
  (hu : ∀ t ∈ S.P.threads, FutEq (S.P.step t) (u t) (G.trace t))
  (hW : ∀ t ∉ S.ts, W t = []) (hρ : SeedOK G S.m W ρ S.ord)

theorem frag_wf (hH : Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W H) : H.Wf :=
  (Model.ofSet S.ms).wf _ hH.1.2

/-- In a fragment, an event at a seed position is the seed event. -/
theorem frag_seed_eq (hH : Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W H)
    {x : Ev Q} (hx : x ∈ H.events) (hi : x.idx < (W x.tid).length) :
    x = seedEv S.m W x.tid x.idx :=
  seed_eq (frag_wf S hH) (fun _ _ hj => frag_seedEv hH hj) hx hi

/-- In a fragment, an event past its seeds is in a thread of the program. -/
theorem frag_tid (hH : Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W H)
    {e : Ev Q} (he : e ∈ H.events) (hi : (W e.tid).length ≤ e.idx) : e.tid ∈ S.P.threads := by
  have hw := frag_wf S hH
  have ht := hw.tid_mem_threads hH.1.1 he
  change e.tid ∈ S.P.threads ++ S.ι at ht
  by_cases hP : e.tid ∈ S.P.threads
  · exact hP
  · have hι : e.tid ∈ S.ι := (List.mem_append.mp ht).resolve_left hP
    have := frag_cnt_idle hH hι hP
    have := hw.idx_lt_cnt he
    omega

/-- A step of a fragment gives a fragment. -/
theorem frag_step (hH : Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W H)
    (h : OpStepG (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) H H') :
    Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W H' := by
  obtain ⟨hE, hp⟩ := ExecM.of_opStepG hH.1 h
  refine ⟨hE, fun t => (hH.2 t).trans ?_⟩
  obtain ⟨E, -, rfl⟩ := hp
  exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.inter_subset_left)

include hG hρ in
/-- lem:mp-compose (3), lem:p2p-compose (1): the unread sends of `G ⊕ H` are the images of the
unread sends of `H`. -/
theorem us_scomp (hH : Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W H) :
    (G.scomp H W ρ).US = H.US.image (G.ehat W ρ) := by
  have hGw : G.Wf := (Model.ofSet S.ms).wf _ hG.2
  have hHw := frag_wf S hH
  have hseed : ∀ t j, j < (W t).length → seedEv S.m W t j ∈ H.events :=
    fun _ _ hj => frag_seedEv hH hj
  have hsd := fun x (hx : x ∈ H.events) hi => frag_seed_eq S hH hx hi
  -- a receive of `H` is past its seeds
  have hrW : ∀ r ∈ H.events, r.IsRecv → (W r.tid).length ≤ r.idx := fun r hr hR => by
    by_contra hlt
    push Not at hlt
    have hS : r.IsSend := by rw [hsd r hr hlt]; exact seedLab_isSend hlt
    exact Lab.IsSend.not_isRecv hS hR
  ext s
  rw [Finset.mem_image, mem_US]
  constructor
  · rintro ⟨hs, hS, hU⟩
    rcases mem_scomp.mp hs with hsG | ⟨z, hz, hzi, rfl⟩
    · have hsU : s ∈ G.US := (G.mem_US).mpr ⟨hsG, hS, fun r hr h => hU r
        (mem_scomp.mpr (Or.inl hr)) (by rw [scomp_rf_old hr]; exact h)⟩
      obtain ⟨t, j, hj, rfl⟩ := hρ.surj s hsU
      have hej : G.ehat W ρ (seedEv S.m W t j) = ρ (seedEv S.m W t j) :=
        ehat_of_lt (x := seedEv S.m W t j) hj
      refine ⟨seedEv S.m W t j, (H.mem_US).mpr ⟨hseed t j hj, seedLab_isSend hj, fun r hr h => ?_⟩,
        hej⟩
      have hri := hrW r hr (hHw.rf_match _ _ h).isRecv
      refine hU _ (mem_scomp.mpr (Or.inr ⟨r, hr, hri, rfl⟩)) ?_
      rw [scomp_rf_emb hGw hr hri, h]
      simp [Src.map, hej]
    · refine ⟨z, (H.mem_US).mpr ⟨hz, hS, fun r hr h => ?_⟩, ehat_of_ge hzi⟩
      have hri := hrW r hr (hHw.rf_match _ _ h).isRecv
      refine hU _ (mem_scomp.mpr (Or.inr ⟨r, hr, hri, rfl⟩)) ?_
      rw [scomp_rf_emb hGw hr hri, h]
      simp [Src.map, ehat_of_ge hzi]
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxH, hxS, hxU⟩ := (H.mem_US).mp hx
    have hxS' : x ∈ H.S := (H.mem_S).mpr ⟨hxH, hxS⟩
    refine ⟨ehat_mem hGw hHw hseed hρ hxS', ?_, fun r hr h => ?_⟩
    · change (G.ehat W ρ x).lab.IsSend
      rw [ehat_lab hHw hseed hρ x hxS']
      exact hxS
    · rcases mem_scomp.mp hr with hrG | ⟨y, hy, hyi, rfl⟩
      · rw [scomp_rf_old hrG] at h
        have hmem := hGw.rf_mem _ _ h
        rcases Nat.lt_or_ge x.idx (W x.tid).length with hi | hi
        · rw [ehat_of_lt hi, hsd x hxH hi] at h
          exact ((G.mem_US).mp (hρ.mem _ _ hi)).2.2 r hrG h
        · rw [ehat_of_ge hi] at hmem
          exact hGw.emb_not_mem x hmem
      · rw [scomp_rf_emb hGw hy hyi] at h
        rcases hy' : H.rf y with _ | (_ | x')
        · rw [hy'] at h
          cases h
        · rw [hy'] at h
          cases h
        · rw [hy'] at h
          simp only [Option.map_some, Src.map, Option.some.injEq, Src.snd.injEq] at h
          have hx'H := hHw.rf_mem _ _ hy'
          have := hρ.ehat_inj hGw (hsd x' hx'H) (hsd x hxH) h
          subst this
          exact hxU y hy hy'

include hG hρ in
/-- The receive case of a step of `R` mapped to `G ⊕ H`. -/
theorem cons_addRecv_scomp (hH : Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W H)
    (hC : (Model.ofSet S.ms).cons (G.scomp H W ρ)) {e x : Ev Q} (hidx : e.idx = H.cnt e.tid)
    (hc' : (Model.ofSet S.ms).cons (H.addRecv e (.snd x))) :
    (Model.ofSet S.ms).cons ((G.scomp H W ρ).addRecv (G.emb W e) (.snd (G.ehat W ρ x))) := by
  have hGw : G.Wf := (Model.ofSet S.ms).wf _ hG.2
  have hHw := frag_wf S hH
  have hseed : ∀ t j, j < (W t).length → seedEv S.m W t j ∈ H.events :=
    fun _ _ hj => frag_seedEv hH hj
  have hsd := fun x (hx : x ∈ H.events) hi => frag_seed_eq S hH hx hi
  obtain ⟨hxU, hxm⟩ := (Model.ofSet S.ms).src_of_cons hH.1.2 hidx hc'
  have hxH := ((H.mem_US).mp hxU).1
  have hxS : x ∈ H.S := H.US_subset_S hxU
  have hus := us_scomp S hG hρ hH
  have hU' : G.ehat W ρ x ∈ (G.scomp H W ρ).US := by
    rw [hus]
    exact Finset.mem_image_of_mem _ hxU
  have hm' : (G.ehat W ρ x).Matches (G.emb W e) :=
    (Ev.matches_congr (ehat_lab hHw hseed hρ x hxS) rfl rfl).mpr hxm
  have hCw := (Model.ofSet S.ms).wf _ hC
  have hidx' : (G.emb W e).idx = (G.scomp H W ρ).cnt (G.emb W e).tid := by
    rw [scomp_cnt hGw hHw hH.2]
    simp only [emb_idx, emb_tid]
    rw [hidx]
  have hW' := hCw.addRecv hidx' hU' hm'
  change Graph.ConsOf S.ms _
  refine ⟨hW', fun hp => ?_, fun hc => absurd hc S.hms.1, fun hm => absurd hm S.hms.2⟩
  have ho := S.hord hp
  have hbc : (G.scomp H W ρ).BC (G.scomp H W ρ).soP2P := hC.2.1 hp
  refine hCw.bc_add hidx' hW' hbc (fun a ha b hb ⟨x1, y1, z1⟩ => ⟨x1, y1, po_add_of_mem ha hb z1⟩)
    (fun b _ ⟨_, _, z1⟩ => hCw.not_po_add_left hidx' b z1) ?_
  intro s₀ hs₀ s' hs' hne hso hd hv
  cases hs₀
  rw [hus, Finset.mem_image] at hs'
  obtain ⟨y, hyU, rfl⟩ := hs'
  have hyS : y ∈ H.S := H.US_subset_S hyU
  have hyx : y ≠ x := fun h => hne (h ▸ rfl)
  have hsoH : H.SoDst y x :=
    (ehat_soDst hGw hHw hseed hρ ho y hyS x hxS).mpr (soDst_iff.mpr ⟨hso, hd⟩)
  have hv' : y.ValMatches e := (Ev.valMatches_congr (ehat_lab hHw hseed hρ y hyS) rfl).mp hv
  have hbH : (H.addRecv e (.snd x)).BC (H.addRecv e (.snd x)).soP2P := hc'.2.1 hp
  have hsrc : ∀ z, some (Src.snd x) = some (.snd z) → z ∈ H.events := fun z hz => by
    cases hz
    exact hxH
  have hyU' : y ∈ (H.addRecv e (.snd x)).US :=
    (hHw.mem_US_add hidx hsrc).mpr (Or.inr ⟨hyU, fun h => hyx (by cases h; rfl)⟩)
  obtain ⟨hso', hd'⟩ := soDst_iff.mp hsoH
  refine hbH.1 y hyU' x (Finset.mem_insert_of_mem hxH) e (Finset.mem_insert_self _ _)
    ⟨⟨hso'.1, hso'.2.1, ?_⟩, hd', by simp, hv'⟩
  exact ⟨Finset.mem_insert_of_mem hso'.2.2.1, Finset.mem_insert_of_mem hso'.2.2.2.1,
    hso'.2.2.2.2⟩

include hG hu hρ in
/-- A step of `R` from a fragment is a step of `P` from the composition. -/
theorem fwd_step (hH : Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W H)
    (hC : ExecM (Model.ofSet S.ms) S.P (G.scomp H W ρ))
    (h : OpStepG (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) H H') :
    OpStepG (Model.ofSet S.ms) S.P (G.scomp H W ρ) (G.scomp H' W ρ) := by
  have hGw : G.Wf := (Model.ofSet S.ms).wf _ hG.2
  have hHw := frag_wf S hH
  have hseed : ∀ t j, j < (W t).length → seedEv S.m W t j ∈ H.events :=
    fun _ _ hj => frag_seedEv hH hj
  obtain ⟨e, src, out, ⟨hav, hadm, hc'⟩, rfl⟩ := h
  obtain ⟨t, -, hn, -⟩ := (Model.ofSet S.ms).mem_availM_iff'.mp hav
  have hidx := Model.idx_of_nextEv hn
  unfold Program.nextEv at hn
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp hn
  have hcW : (W t).length ≤ H.cnt t := hH.2 t
  have hlen : (W t).length ≤ (H.trace t).length := by
    unfold trace
    rw [traceBefore_length]
    exact hcW
  have htP : t ∈ S.P.threads ∧ S.P.step t (u t ++ (H.trace t).drop (W t).length) = some l := by
    change (if t ∈ S.P.threads then _ else _) = some l at hl
    split_ifs at hl with h1 h2
    · rw [prefixStep_of_le hlen] at hl
      exact ⟨h1, hl⟩
    · rw [prefixStep_of_le hlen] at hl
      cases hl
  set e : Ev Q := ⟨t, H.cnt t, l⟩ with he
  have hse : (W e.tid).length ≤ e.idx := hcW
  have hstep : S.P.step t ((G.scomp H W ρ).trace t) = some l := by
    rw [scomp_trace hGw hHw hH.2 hseed hρ t, ← hu t htP.1]
    exact htP.2
  have hidx' : (G.emb W e).idx = (G.scomp H W ρ).cnt (G.emb W e).tid := by
    rw [scomp_cnt hGw hHw hH.2]
    rfl
  have hnP : S.P.nextEv (G.scomp H W ρ) t = some (G.emb W e) := by
    unfold Program.nextEv
    rw [hstep]
    simp only [Option.map_some, Option.some.injEq]
    rw [scomp_cnt hGw hHw hH.2]
    rfl
  rw [scomp_add hGw hHw hidx hse]
  have hCw := (Model.ofSet S.ms).wf _ hC.2
  -- admissibility and consistency
  have key : Adm (G.scomp H W ρ) (G.emb W e) (src.map (Src.map (G.ehat W ρ))) out ∧
      (Model.ofSet S.ms).cons ((G.scomp H W ρ).add (G.emb W e)
        (src.map (Src.map (G.ehat W ρ))) out) := by
    rcases hadm with ⟨hR, rfl, rfl | ⟨x, hx, rfl⟩⟩ | ⟨hN, rfl, v, hv, rfl⟩ | ⟨hR, hN, rfl, rfl⟩
    · have hNB : e.IsRecvNB := ((Model.ofSet S.ms).wf _ hc').rf_bot e (by simp)
      exact ⟨Or.inl ⟨hR, rfl, Or.inl rfl⟩,
        (Model.ofSet S.ms).ext_bot _ (G.emb W e) hC.2 hidx' hNB⟩
    · have hc := cons_addRecv_scomp S hG hρ hH hC.2 hidx hc'
      have hxS : G.ehat W ρ x ∈ (G.scomp H W ρ).S := by
        rcases (ehat_bij hGw hHw hseed hρ).mapsTo (Finset.mem_coe.mpr hx) with h | h
        · exact (mem_S _).mpr ⟨mem_scomp.mpr (Or.inl ((G.mem_US).mp (Finset.mem_coe.mp h)).1),
            ((G.mem_US).mp (Finset.mem_coe.mp h)).2.1⟩
        · exact (Finset.mem_sdiff.mp (Finset.mem_coe.mp h)).1
      exact ⟨Or.inl ⟨hR, rfl, Or.inr ⟨_, hxS, rfl⟩⟩, hc⟩
    · exact ⟨Or.inr (Or.inl ⟨hN, rfl, v, hv, rfl⟩),
        (Model.ofSet S.ms).ext_nd _ (G.emb W e) v hC.2 hidx' hN hv⟩
    · exact ⟨Or.inr (Or.inr ⟨hR, hN, rfl, rfl⟩),
        (Model.ofSet S.ms).ext_plain _ (G.emb W e) hC.2 hidx' hR hN⟩
  refine ⟨G.emb W e, _, out, ⟨?_, key.1, key.2⟩, rfl⟩
  refine (Model.ofSet S.ms).mem_availM_iff'.mpr ⟨t, htP.1, hnP, ?_⟩
  by_cases hB : (G.emb W e).IsRecvB
  · right
    rcases key.1 with ⟨-, hout, hb | ⟨s, hs, hsrc⟩⟩ | ⟨hN, -⟩ | ⟨hR, -⟩
    · have := ((Model.ofSet S.ms).wf _ key.2).rf_bot (G.emb W e) (by simp [hb])
      exact absurd hB (Lab.not_isRecvB_of_isRecvNB this)
    · refine ⟨s, hs, ?_⟩
      have := key.2
      rw [hsrc, hout] at this
      exact this
    · exact absurd (Lab.IsRecvB.isRecv hB) (Lab.IsND.not_isRecv hN)
    · exact absurd (Lab.IsRecvB.isRecv hB) hR
  · exact Or.inl hB

include hG hu hW hρ in
/-- lem:mp-compose (1), lem:p2p-compose (3): `G ⊕ H` is a consistent execution of `P` and an
extension of `G`. -/
theorem frag_scomp (hH : Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W H) :
    ExecM (Model.ofSet S.ms) S.P (G.scomp H W ρ) ∧ G.IsPrefixOf (G.scomp H W ρ) := by
  have hGw : G.Wf := (Model.ofSet S.ms).wf _ hG.2
  have hop := isPrefixOf_opLe hH.1.2 hH.1.1 (seed_isPrefixOf hW hH)
  suffices ∀ K, OpLe (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W)
      (seedGraph (S.P.threads ++ S.ι) S.m W) K →
      Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W K ∧
      ExecM (Model.ofSet S.ms) S.P (G.scomp K W ρ) ∧ G.IsPrefixOf (G.scomp K W ρ) from
    (this H hop).2
  intro K hK
  induction hK with
  | refl =>
    rw [scomp_seed hGw]
    exact ⟨frag_seed hW, hG, hGw.isPrefixOf_refl⟩
  | tail _ hs ih =>
    obtain ⟨hF, hC, hp⟩ := ih
    obtain ⟨hC', hp'⟩ := ExecM.of_opStepG hC (fwd_step S hG hu hρ hF hC hs)
    exact ⟨frag_step S hF hs, hC', hp.trans hp'⟩

include hG hρ in
/-- lem:mp-compose (3): `pend(G ⊕ H) = pend(H)`. -/
theorem pendM_scomp (hH : Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W H) :
    (G.scomp H W ρ).pendM = H.pendM := by
  have hGw : G.Wf := (Model.ofSet S.ms).wf _ hG.2
  have hHw := frag_wf S hH
  have hseed : ∀ t j, j < (W t).length → seedEv S.m W t j ∈ H.events :=
    fun _ _ hj => frag_seedEv hH hj
  unfold Graph.pendM
  rw [us_scomp S hG hρ hH, Finset.image_val_of_injOn (fun x hx y hy h =>
    (ehat_bij hGw hHw hseed hρ).injOn (Finset.mem_coe.mpr (H.US_subset_S (Finset.mem_coe.mp hx)))
      (Finset.mem_coe.mpr (H.US_subset_S (Finset.mem_coe.mp hy))) h)]
  rw [Multiset.filterMap_map, ← Finset.coe_toList H.US, Multiset.filterMap_coe,
    Multiset.filterMap_coe, Multiset.coe_eq_coe]
  refine (List.Perm.of_eq (List.filterMap_congr fun x hx => ?_))
  exact msgOf_congr (ehat_lab hHw hseed hρ x (H.US_subset_S (Finset.mem_toList.mp hx)))

include hG hu hW hρ in
/-- lem:p2p-compose (1): `pend_t(G ⊕ H) = pend_t(H)` when the order is kept. With `ord = False`
false (Opus B1, plan Section 4.1): a sender-swapping `ρ` exchanges `pend_1` and `pend_2`. -/
theorem pend_scomp (ho : S.ord) (hH : Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W H)
    (t : Tid) : (G.scomp H W ρ).pend t = H.pend t := by
  have hGw : G.Wf := (Model.ofSet S.ms).wf _ hG.2
  have hHw := frag_wf S hH
  have hseed : ∀ t j, j < (W t).length → seedEv S.m W t j ∈ H.events :=
    fun _ _ hj => frag_seedEv hH hj
  have hCw := (Model.ofSet S.ms).wf _ (frag_scomp S hG hu hW hρ hH).1.2
  have hseq : (G.scomp H W ρ).unreadSeq t = (H.unreadSeq t).map (G.ehat W ρ) := by
    refine eq_of_pairwise_idx (unreadSeq_pairwise _ t) ?_ fun s => ?_
    · rw [List.pairwise_map]
      refine (unreadSeq_pairwise H t).imp_of_mem fun {a b} ha hb hab => ?_
      obtain ⟨haU, hat⟩ := (mem_unreadSeq hHw).mp ha
      obtain ⟨hbU, hbt⟩ := (mem_unreadSeq hHw).mp hb
      exact (ehat_idx hGw hHw hseed hρ ho a (H.US_subset_S haU) b (H.US_subset_S hbU)
        (hat.trans hbt.symm)).mp hab
    · rw [mem_unreadSeq hCw, us_scomp S hG hρ hH, Finset.mem_image, List.mem_map]
      constructor
      · rintro ⟨⟨x, hx, rfl⟩, ht⟩
        refine ⟨x, (mem_unreadSeq hHw).mpr ⟨hx, ?_⟩, rfl⟩
        rw [← ht, ehat_tid hHw hseed hρ ho x (H.US_subset_S hx)]
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨hxU, hxt⟩ := (mem_unreadSeq hHw).mp hx
        exact ⟨⟨x, hxU, rfl⟩, by rw [ehat_tid hHw hseed hρ ho x (H.US_subset_S hxU), hxt]⟩
  rw [hCw.pend_eq, hHw.pend_eq, hseq, List.filterMap_map]
  refine List.filterMap_congr fun x hx => ?_
  exact msgOf_congr (ehat_lab hHw hseed hρ x (H.US_subset_S ((mem_unreadSeq hHw).mp hx).1))

include hG hu hW hρ in
/-- lem:mp-compose (4), lem:p2p-compose (4): composition is monotone. -/
theorem scomp_mono (hH : Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W H)
    (hF : Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W F) (hp : H.IsPrefixOf F) :
    (G.scomp H W ρ).IsPrefixOf (G.scomp F W ρ) := by
  have hop := isPrefixOf_opLe hF.1.2 hF.1.1 hp
  suffices ∀ K, OpLe (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) H K →
      Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W K ∧
      OpLe (Model.ofSet S.ms) S.P (G.scomp H W ρ) (G.scomp K W ρ) from
    (OpLe.isPrefixOf (frag_scomp S hG hu hW hρ hH).1.2 (this F hop).2).1
  intro K hK
  induction hK with
  | refl => exact ⟨hH, ReflTransGen.refl⟩
  | tail _ hs ih =>
    obtain ⟨hK1, hop1⟩ := ih
    exact ⟨frag_step S hK1 hs,
      hop1.tail (fwd_step S hG hu hρ hK1 (frag_scomp S hG hu hW hρ hK1).1 hs)⟩

include hG hρ in
/-- The composition determines the fragment. -/
theorem frag_scomp_injective (hH : Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W H)
    (hH' : Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W H') :
    G.scomp H W ρ = G.scomp H' W ρ → H = H' := by
  have hGw : G.Wf := (Model.ofSet S.ms).wf _ hG.2
  refine scomp_injective hGw (frag_wf S hH) (frag_wf S hH') hH.2 hH'.2
    (fun t j hj => ⟨frag_seedEv hH hj, frag_seedEv hH' hj⟩) hρ ?_
  intro t j hj e he ht hi
  subst ht hi
  rcases Finset.mem_union.mp he with he | he
  · exact frag_seed_eq S hH he hj
  · exact frag_seed_eq S hH' he hj

end Ind

end Must
