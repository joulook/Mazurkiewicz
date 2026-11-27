import Mazurkiewicz.Induction.MP.CompFrag
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Message passing: steps commute with composition (milestone C4b)

`induction-popl`, `mp.tex` prop:mp-compose and `p2p.tex` prop:p2p-compose, for the one
construction `Graph.scomp` over a setting `S : MPSetting Q` (plan `plan/ind/TRACK-C-PLAN.md`,
milestone C4b). Context as in `MP/CompFrag.lean`.

* (1) `step_scomp`: a step of the fragment program `R` from a fragment is a step of `P` from
  the composition, to a fragment.
* (2) `scomp_step`: every step of `P` from `G ⊕ H` comes from a unique step of `R` from `H`.
  Under `p2p` the receive case uses `ehat_soDst` (needs `S.ord`, from `S.hord`).
* (3) `stepsN_iff_frag`: `m` steps from `G` reach exactly the compositions with fragments of
  length `m`.
* Helpers: `cons_addRecv_of_scomp` (the receive case of (2)), `seedGraph_card`,
  `card_frag_ge`, `stepsN_scomp`.
-/

namespace Must

namespace Ind

open Graph Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q]

variable (S : MPSetting Q) {G H H' : Graph Q} {u : Tid → List (Option Val)}
  {W : Tid → List Msg} {ρ : Ev Q → Ev Q}
variable (hG : ExecM (Model.ofSet S.ms) S.P G)
  (hu : ∀ t ∈ S.P.threads, FutEq (S.P.step t) (u t) (G.trace t))
  (hW : ∀ t ∉ S.ts, W t = []) (hρ : SeedOK G S.m W ρ S.ord)

include hG hu hW hρ in
/-- prop:mp-compose (1), prop:p2p-compose (1). -/
theorem step_scomp (hH : Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W H)
    (h : OpStepG (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) H H') :
    Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W H' ∧
      OpStepG (Model.ofSet S.ms) S.P (G.scomp H W ρ) (G.scomp H' W ρ) :=
  ⟨frag_step S hH h, fwd_step S hG hu hρ hH (frag_scomp S hG hu hW hρ hH).1 h⟩

include hG hρ in
/-- The receive case of a step of `P` from `G ⊕ H`, pulled back to `H`. -/
theorem cons_addRecv_of_scomp
    (hH : Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W H)
    (hC : (Model.ofSet S.ms).cons (G.scomp H W ρ)) {e x : Ev Q} (hidx : e.idx = H.cnt e.tid)
    (hxU : x ∈ H.US) (hxm : x.Matches e)
    (hc : (Model.ofSet S.ms).cons ((G.scomp H W ρ).addRecv (G.emb W e) (.snd (G.ehat W ρ x)))) :
    (Model.ofSet S.ms).cons (H.addRecv e (.snd x)) := by
  have hGw : G.Wf := (Model.ofSet S.ms).wf _ hG.2
  have hHw := frag_wf S hH
  have hseed : ∀ t j, j < (W t).length → seedEv S.m W t j ∈ H.events :=
    fun _ _ hj => frag_seedEv hH hj
  have hsd := fun x (hx : x ∈ H.events) hi => frag_seed_eq S hH hx hi
  have hxH := ((H.mem_US).mp hxU).1
  have hxS : x ∈ H.S := H.US_subset_S hxU
  have hCw := (Model.ofSet S.ms).wf _ hC
  have hus := us_scomp S hG hρ hH
  have hidx' : (G.emb W e).idx = (G.scomp H W ρ).cnt (G.emb W e).tid := by
    rw [scomp_cnt hGw hHw hH.2]
    simp only [emb_idx, emb_tid]
    rw [hidx]
  have hW' := hHw.addRecv hidx hxU hxm
  change Graph.ConsOf S.ms _
  refine ⟨hW', fun hp => ?_, fun hc => absurd hc S.hms.1, fun hm => absurd hm S.hms.2⟩
  have ho := S.hord hp
  have hbc : H.BC H.soP2P := hH.1.2.2.1 hp
  refine hHw.bc_add hidx hW' hbc (fun a ha b hb ⟨x1, y1, z1⟩ => ⟨x1, y1, po_add_of_mem ha hb z1⟩)
    (fun b _ ⟨_, _, z1⟩ => hHw.not_po_add_left hidx b z1) ?_
  intro s₀ hs₀ y hyU hne hso hd hv
  cases hs₀
  have hyS : y ∈ H.S := H.US_subset_S hyU
  have hsoK : (G.scomp H W ρ).SoDst (G.ehat W ρ y) (G.ehat W ρ x) :=
    (ehat_soDst hGw hHw hseed hρ ho y hyS x hxS).mp (soDst_iff.mpr ⟨hso, hd⟩)
  have hv' : (G.ehat W ρ y).ValMatches (G.emb W e) :=
    (Ev.valMatches_congr (ehat_lab hHw hseed hρ y hyS) rfl).mpr hv
  have hne' : G.ehat W ρ y ≠ G.ehat W ρ x := fun h =>
    hne (hρ.ehat_inj hGw (hsd y ((H.mem_US).mp hyU).1) (hsd x hxH) h)
  have hbK := hc.2.1 hp
  have hsrc : ∀ z, some (Src.snd (G.ehat W ρ x)) = some (.snd z) →
      z ∈ (G.scomp H W ρ).events := fun z hz => by
    cases hz
    exact ehat_mem hGw hHw hseed hρ hxS
  have hyU' : G.ehat W ρ y ∈ ((G.scomp H W ρ).addRecv (G.emb W e) (.snd (G.ehat W ρ x))).US := by
    refine (hCw.mem_US_add hidx' hsrc).mpr (Or.inr ⟨?_, fun h => hne' (by
      simp only [Option.some.injEq, Src.snd.injEq] at h
      exact h.symm)⟩)
    rw [hus]
    exact Finset.mem_image_of_mem _ hyU
  obtain ⟨hso', hd'⟩ := soDst_iff.mp hsoK
  refine hbK.1 _ hyU' _ (Finset.mem_insert_of_mem (ehat_mem hGw hHw hseed hρ hxS)) _
    (Finset.mem_insert_self _ _) ⟨⟨hso'.1, hso'.2.1, ?_⟩, hd', by simp, hv'⟩
  exact ⟨Finset.mem_insert_of_mem hso'.2.2.1, Finset.mem_insert_of_mem hso'.2.2.2.1,
    hso'.2.2.2.2⟩

include hG hu hW hρ in
/-- prop:mp-compose (2), prop:p2p-compose (2): a step of `P` from `G ⊕ H` comes from a unique
step of `R` from `H`. -/
theorem scomp_step (hH : Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W H)
    {G' : Graph Q} (h : OpStepG (Model.ofSet S.ms) S.P (G.scomp H W ρ) G') :
    ∃! H', Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W H' ∧
      OpStepG (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) H H' ∧ G' = G.scomp H' W ρ := by
  have hGw : G.Wf := (Model.ofSet S.ms).wf _ hG.2
  have hHw := frag_wf S hH
  have hseed : ∀ t j, j < (W t).length → seedEv S.m W t j ∈ H.events :=
    fun _ _ hj => frag_seedEv hH hj
  have hC := (frag_scomp S hG hu hW hρ hH).1
  refine existsUnique_of_exists_of_unique ?_ fun H₁ H₂ ⟨h1, _, e1⟩ ⟨h2, _, e2⟩ =>
    frag_scomp_injective S hG hρ h1 h2 (e1.symm.trans e2)
  obtain ⟨e', src', out', ⟨hav, hadm, hc'⟩, rfl⟩ := h
  obtain ⟨t, ht, hn, -⟩ := (Model.ofSet S.ms).mem_availM_iff'.mp hav
  have hidx' := Model.idx_of_nextEv hn
  unfold Program.nextEv at hn
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp hn
  set e : Ev Q := ⟨t, H.cnt t, l⟩ with he
  have hidx : e.idx = H.cnt e.tid := rfl
  have hse : (W e.tid).length ≤ e.idx := hH.2 t
  have hemb : G.emb W e = ⟨t, (G.scomp H W ρ).cnt t, l⟩ := by
    rw [scomp_cnt hGw hHw hH.2]
    rfl
  have hlen : (W t).length ≤ (H.trace t).length := by
    unfold trace
    rw [traceBefore_length]
    exact hH.2 t
  have hRstep : (S.P.seedRes S.ι S.hι S.m u W).step t (H.trace t) = some l := by
    change (if t ∈ S.P.threads then _ else _) = some l
    simp only [ht, ↓reduceIte]
    rw [prefixStep_of_le hlen, hu t ht]
    rw [scomp_trace hGw hHw hH.2 hseed hρ t] at hl
    exact hl
  have hnR : (S.P.seedRes S.ι S.hι S.m u W).nextEv H t = some e := by
    simp [Program.nextEv, hRstep, e]
  have htR : t ∈ (S.P.seedRes S.ι S.hι S.m u W).threads := List.mem_append_left _ ht
  -- the step of `R`, case by case
  have key : ∃ src out, Adm H e src out ∧
      (Model.ofSet S.ms).cons (H.add e src out) ∧
      src' = src.map (Src.map (G.ehat W ρ)) ∧ out' = out := by
    rcases hadm with ⟨hR, rfl, rfl | ⟨s', hs', rfl⟩⟩ | ⟨hN, rfl, v, hv, rfl⟩ |
        ⟨hR, hN, rfl, rfl⟩
    · have hNB : e.IsRecvNB :=
        ((Model.ofSet S.ms).wf _ hc').rf_bot ⟨t, (G.scomp H W ρ).cnt t, l⟩ (by simp)
      exact ⟨some .bot, none, Or.inl ⟨hR, rfl, Or.inl rfl⟩,
        (Model.ofSet S.ms).ext_bot _ e hH.1.2 hidx hNB, rfl, rfl⟩
    · obtain ⟨hU, hm⟩ := (Model.ofSet S.ms).src_of_cons hC.2 hidx' hc'
      rw [us_scomp S hG hρ hH, Finset.mem_image] at hU
      obtain ⟨x, hxU, rfl⟩ := hU
      have hxS : x ∈ H.S := H.US_subset_S hxU
      have hxm : x.Matches e :=
        (Ev.matches_congr (ehat_lab hHw hseed hρ x hxS) rfl rfl).mp hm
      have hc'' : (Model.ofSet S.ms).cons
          ((G.scomp H W ρ).addRecv (G.emb W e) (.snd (G.ehat W ρ x))) := by
        rw [hemb]
        exact hc'
      exact ⟨some (.snd x), none, Or.inl ⟨hR, rfl, Or.inr ⟨x, hxS, rfl⟩⟩,
        cons_addRecv_of_scomp S hG hρ hH hC.2 hidx hxU hxm hc'', rfl, rfl⟩
    · exact ⟨none, some v, Or.inr (Or.inl ⟨hN, rfl, v, hv, rfl⟩),
        (Model.ofSet S.ms).ext_nd _ e v hH.1.2 hidx hN hv, rfl, rfl⟩
    · exact ⟨none, none, Or.inr (Or.inr ⟨hR, hN, rfl, rfl⟩),
        (Model.ofSet S.ms).ext_plain _ e hH.1.2 hidx hR hN, rfl, rfl⟩
  obtain ⟨src, out, hadm', hcons, hsrc, hout'⟩ := key
  have hop : OpAdd (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) H e src out := by
    refine ⟨(Model.ofSet S.ms).mem_availM_iff'.mpr ⟨t, htR, hnR, ?_⟩, hadm', hcons⟩
    by_cases hB : e.IsRecvB
    · right
      rcases hadm' with ⟨-, hout, hb | ⟨s, hs, rfl⟩⟩ | ⟨hN, -⟩ | ⟨hR, -⟩
      · have := ((Model.ofSet S.ms).wf _ hcons).rf_bot e (by simp [hb])
        exact absurd hB (Lab.not_isRecvB_of_isRecvNB this)
      · refine ⟨s, hs, ?_⟩
        rw [hout] at hcons
        exact hcons
      · exact absurd (Lab.IsRecvB.isRecv hB) (Lab.IsND.not_isRecv hN)
      · exact absurd (Lab.IsRecvB.isRecv hB) hR
    · exact Or.inl hB
  refine ⟨H.add e src out, frag_step S hH ⟨e, src, out, hop, rfl⟩, ⟨e, src, out, hop, rfl⟩, ?_⟩
  rw [hout', scomp_add hGw hHw hidx hse, hemb, ← hsrc]

omit [Membership Val Q] in
/-- The number of seed events. -/
theorem seedGraph_card {ts : List Tid} (hts : ts.Nodup) (m : Comm) (W : Tid → List Msg) :
    (seedGraph ts m W : Graph Q).events.card = seedCard ts W := by
  unfold seedGraph seedCard
  rw [Finset.card_biUnion]
  · rw [← List.sum_toFinset _ hts]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.card_image_of_injective _ (fun j j' h => by
      have := congrArg Ev.idx h
      simpa [seedEv] using this), Finset.card_range]
  · intro t _ t' _ htt'
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j', -, h⟩ := Finset.mem_image.mp hx'
    exact htt' (congrArg Ev.tid h).symm

include hW in
/-- A fragment contains its seeds. -/
theorem card_frag_ge (hH : Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W H) :
    seedCard S.ts W ≤ H.events.card := by
  have hc := seedGraph_card (Q := Q) S.hι S.m W
  change seedCard (S.P.threads ++ S.ι) W ≤ _
  rw [← hc]
  exact Finset.card_le_card (seed_isPrefixOf hW hH).events_subset

include hG hu hW hρ in
/-- Steps of `R` from `Z_w` give steps of `P` from `G`. -/
theorem stepsN_scomp {k : ℕ} {K : Graph Q} :
    StepsN (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) k (seedGraph S.ts S.m W) K →
    Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W K ∧
      StepsN (Model.ofSet S.ms) S.P k G (G.scomp K W ρ) := by
  have hGw : G.Wf := (Model.ofSet S.ms).wf _ hG.2
  induction k generalizing K with
  | zero =>
    rintro rfl
    exact ⟨frag_seed hW, (scomp_seed hGw).symm⟩
  | succ k ih =>
    rintro ⟨K'', hK'', hst⟩
    obtain ⟨hF, hs⟩ := ih hK''
    obtain ⟨hF', hst'⟩ := step_scomp S hG hu hW hρ hF hst
    exact ⟨hF', _, hs, hst'⟩

include hG hu hW hρ in
/-- prop:mp-compose (3), prop:p2p-compose (3): `m` steps from `G` reach exactly the
compositions with fragments of length `m`. -/
theorem stepsN_iff_frag (n : ℕ) (G' : Graph Q) :
    StepsN (Model.ofSet S.ms) S.P n G G' ↔
      ∃ H, Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W H ∧ H.len S.ts W = n ∧
        G' = G.scomp H W ρ := by
  have hGw : G.Wf := (Model.ofSet S.ms).wf _ hG.2
  have hseedF := frag_seed (M := Model.ofSet S.ms) (u := u) (m := S.m) (hι := S.hι) hW
  have hcard := seedGraph_card (Q := Q) S.hι S.m W
  constructor
  · induction n generalizing G' with
    | zero =>
      rintro rfl
      refine ⟨seedGraph S.ts S.m W, hseedF, ?_, (scomp_seed hGw).symm⟩
      unfold Graph.len
      change (seedGraph (S.P.threads ++ S.ι) S.m W : Graph Q).events.card - _ = 0
      rw [hcard]
      exact Nat.sub_self _
    | succ n ih =>
      rintro ⟨G'', h'', hst⟩
      obtain ⟨H'', hF'', hlen'', rfl⟩ := ih G'' h''
      obtain ⟨H', ⟨hF', hst', rfl⟩, -⟩ := scomp_step S hG hu hW hρ hF'' hst
      refine ⟨H', hF', ?_, rfl⟩
      have h1 := (StepsN.execM hF''.1 (n := 1) ⟨H'', rfl, hst'⟩).2.2
      have h2 := card_frag_ge S hW hF''
      unfold Graph.len at hlen'' ⊢
      omega
  · rintro ⟨H, hF, hlen, rfl⟩
    have hk := (stepsN_iff hseedF.1).mpr ⟨hF.1, seed_isPrefixOf hW hF,
      (Nat.add_sub_of_le (Finset.card_le_card (seed_isPrefixOf hW hF).events_subset)).symm⟩
    have := (stepsN_scomp S hG hu hW hρ hk).2
    have heq : H.events.card -
        (seedGraph (S.P.threads ++ S.ι) S.m W : Graph Q).events.card = n := by
      rw [hcard]
      exact hlen
    rw [heq] at this
    exact this

end Ind

end Must
