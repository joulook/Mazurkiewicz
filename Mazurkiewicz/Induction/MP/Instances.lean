import Mazurkiewicz.Induction.MP.Commute

/-!
# Message passing: the instances of Sections 6 and 7 (milestone C5)

`induction-popl`, `mp.tex` def:env, def:mp-compose, lem:mp-compose, prop:mp-compose (Section
6, model `asyn`, environment thread `ν`) and `p2p.tex` def:p2p-frag, def:p2p-compose,
lem:p2p-compose, prop:p2p-compose (Section 7), as instances of the one construction of
`MP/SeedComp.lean`-`MP/Commute.lean` (plan `plan/ind/TRACK-C-PLAN.md`, milestone C5).

* Section 6: `ρEnv σ` (seed `j` of `ν` to `s_{j+1}` of the pending enumeration `σ`),
  `Program.envRes` (`P_{s,w}` of def:env), `compEnv` (`G ⊕_σ H`); `envRes_eq`, `seedOK_env`,
  `pendEnum_of_pendM`, `seedOK_env_enum`; `mp_compose_1`-`mp_compose_4`,
  `mp_compose_steps_1`-`mp_compose_steps_3` under the Section 6 context, which includes
  `hP : P.Tagged .asyn` (without it `mp_compose_1` and the label part of `mp_compose_3` are
  false, Astra r2 B1: a `.p2p` unread send of `G` re-sent by `ν` tagged `.asyn`).
* Section 7: `ρP2P G` (seed `j` of `t` to the `j`-th unread send of `t`, noncomputable),
  `Program.p2pRes`, `compP2P` (`G ⊕ H`, noncomputable); `p2pRes_eq`, `seedOK_p2p`,
  `seedOK_p2p_unique`, `scomp_eq_compP2P`; `p2p_compose_1`-`p2p_compose_4`,
  `p2p_compose_steps_1`-`p2p_compose_steps_3` for `S` with `S.ι = []` and `S.ord`
  (`p2pSetting`, `p2pAsynSetting`).
* Bridging (Opus r2 N2): `scomp_congr_seed` (the composition depends on `ρ` on the seeds
  only).
* Helpers: `SeedOK.weaken`, `word_eq_map`, `exists_perm_filterMap`, `pend_nil`,
  `getElem_lt_iff_of_pairwise`, `ρP2P_seed`, `length_pend`.
-/

namespace Must

open Graph Relation

open Ind in
/-- `P_{s,w}` of def:env: the environment thread `ν` sends `w`, the threads of `P` continue
after `u`. -/
def Program.envRes {Q : Type} (P : Program Q) (ν : Tid) (hν : ν ∉ P.threads)
    (u : Tid → List (Option Val)) (w : List Msg) : Program Q :=
  P.seedRes [ν] (nodup_env P hν) .asyn u (envW ν w)

open Ind in
/-- `P_{s,w}` of def:p2p-frag: every thread first sends its own words `w t`. -/
def Program.p2pRes {Q : Type} (P : Program Q) (m : Comm) (u : Tid → List (Option Val))
    (w : Tid → List Msg) : Program Q :=
  P.seedRes [] (nodup_nil P) m u w

namespace Ind

variable {Q : Type} [DecidableEq Q] [Membership Val Q]

/-- Section 6: the seed `j` goes to the `j`-th element of `σ`. -/
def ρEnv {Q : Type} (σ : List (Ev Q)) (x : Ev Q) : Ev Q := σ.getD x.idx x

/-- Section 7: the seed `(t, j)` goes to the `j`-th unread send of `t`. -/
noncomputable def ρP2P (G : Graph Q) (x : Ev Q) : Ev Q := (G.unreadAt x.tid x.idx).getD x

/-- `G ⊕_σ H` (def:mp-compose). -/
def compEnv (G : Graph Q) (ν : Tid) (σ : List (Ev Q)) (H : Graph Q) : Graph Q :=
  G.scomp H (envW ν (word σ)) (ρEnv σ)

/-- `G ⊕ H` (def:p2p-compose). -/
noncomputable def compP2P (G H : Graph Q) : Graph Q := G.scomp H G.pend (ρP2P G)

/-! ### Helpers -/

omit [Membership Val Q] in
/-- A weaker order flag. -/
theorem SeedOK.weaken {G : Graph Q} {m : Comm} {W : Tid → List Msg} {ρ : Ev Q → Ev Q}
    {ord ord' : Prop} (h : SeedOK G m W ρ ord) (hord : ord' → ord) : SeedOK G m W ρ ord' :=
  ⟨h.mem, h.lab, h.inj, h.surj, fun o => h.tid (hord o), fun o => h.mono (hord o)⟩

omit [DecidableEq Q] [Membership Val Q] in
theorem msgOf_send {s : Ev Q} (hs : s.IsSend) :
    ∃ m d v, s.lab = .send m d v ∧ msgOf s = some (d, v) := by
  obtain ⟨m, d, v, h⟩ := (Lab.isSend_iff s.lab).mp hs
  exact ⟨m, d, v, h, by simp [msgOf, h]⟩

omit [DecidableEq Q] [Membership Val Q] in
/-- The word of a list of sends. -/
theorem word_eq_map {σ : List (Ev Q)} (hS : ∀ s ∈ σ, s.IsSend) :
    word σ = σ.map fun s => (msgOf s).getD (0, 0) := by
  induction σ with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨m, d, v, -, ha⟩ := msgOf_send (hS a (List.mem_cons_self))
    unfold word at ih ⊢
    rw [List.filterMap_cons_some ha, ih fun s hs => hS s (List.mem_cons_of_mem _ hs)]
    simp [ha]

omit [Membership Val Q] in
/-- A list whose `filterMap` is a permutation of `w` has a permutation with `filterMap` `w`. -/
theorem exists_perm_filterMap {α β : Type} (f : α → Option β) :
    ∀ (w : List β) (l : List α), (l.filterMap f).Perm w →
      ∃ l' : List α, l'.Perm l ∧ l'.filterMap f = w
  | [], l, h => ⟨l, List.Perm.refl _, List.Perm.nil_eq h.symm |>.symm⟩
  | b :: w, l, h => by
    classical
    obtain ⟨x, hx, hfx⟩ := List.mem_filterMap.mp (h.symm.subset List.mem_cons_self)
    have hp := List.perm_cons_erase hx
    have h2 : (b :: (l.erase x).filterMap f).Perm (b :: w) := by
      have := (hp.filterMap f).symm.trans h
      rwa [List.filterMap_cons_some hfx] at this
    obtain ⟨l'', hl'', hw⟩ := exists_perm_filterMap f w (l.erase x) ((List.perm_cons b).mp h2)
    exact ⟨x :: l'', ((List.perm_cons x).mpr hl'').trans hp.symm, by
      rw [List.filterMap_cons_some hfx, hw]⟩

omit [Membership Val Q] in
/-- The elements of `unreadSeq` are sends. -/
theorem unreadSeq_isSend {G : Graph Q} {t : Tid} :
    ∀ s ∈ G.unreadSeq t, s.IsSend := fun s hs => by
  obtain ⟨i, -, h⟩ := List.mem_filterMap.mp hs
  exact ((G.mem_US).mp (unreadEvAt_spec h).1).2.1

theorem length_pend {G : Graph Q} (hG : G.Wf) (t : Tid) :
    (G.pend t).length = (G.unreadSeq t).length := by
  rw [hG.pend_eq, ← word, word_eq_map unreadSeq_isSend, List.length_map]

omit [DecidableEq Q] [Membership Val Q] in
/-- In a list strictly sorted by index, the positions are ordered as the indices. -/
theorem getElem_lt_iff_of_pairwise {l : List (Ev Q)} (h : l.Pairwise fun a b => a.idx < b.idx)
    {j j' : ℕ} (hj : j < l.length) (hj' : j' < l.length) : j < j' ↔ l[j].idx < l[j'].idx := by
  have hp := List.pairwise_iff_getElem.mp h
  constructor
  · exact hp j j' hj hj'
  · intro hlt
    rcases Nat.lt_trichotomy j j' with h1 | h1 | h1
    · exact h1
    · subst h1
      exact absurd hlt (lt_irrefl _)
    · exact absurd (hp j' j hj' hj h1) (lt_asymm hlt)

omit [Membership Val Q] in
theorem ρP2P_seed {G : Graph Q} {m : Comm} {W : Tid → List Msg} {t j : ℕ} :
    ρP2P G (seedEv m W t j) = ((G.unreadSeq t)[j]?).getD (seedEv m W t j) := rfl

omit [DecidableEq Q] [Membership Val Q] in
theorem ρEnv_seed {σ : List (Ev Q)} {m : Comm} {W : Tid → List Msg} {t j : ℕ} :
    ρEnv σ (seedEv m W t j) = (σ[j]?).getD (seedEv m W t j) := by
  unfold ρEnv
  rw [List.getD_eq_getElem?_getD]
  rfl

/-- A thread of no event has no pending messages. -/
theorem pend_nil {G : Graph Q} {P : Program Q} (hG : G.Wf) (hE : P.Exec G) {t : Tid}
    (ht : t ∉ P.threads) : G.pend t = [] := by
  have h0 : G.cnt t = 0 := by
    unfold cnt
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx hxt
    exact ht (hxt ▸ hG.tid_mem_threads hE hx)
  unfold Graph.pend
  rw [h0]
  rfl

/-! ### Section 6: the seeds -/

/-- Section 6: `P_{s,w}` of the setting is `envRes`. -/
theorem envRes_eq {P : Program Q} {ν : Tid} {hν : ν ∉ P.threads} (hP : P.Tagged .asyn)
    {u : Tid → List (Option Val)} {w : List Msg} :
    (envSetting P ν hν hP).P.seedRes (envSetting P ν hν hP).ι (envSetting P ν hν hP).hι .asyn u
      (envW ν w) = P.envRes ν hν u w := rfl

/-- Section 6: a pending enumeration gives seeds (`ord = False`). -/
theorem seedOK_env {P : Program Q} {G : Graph Q} {σ : List (Ev Q)} {ν : Tid}
    (hG : ExecM Model.asyn P G) (hP : P.Tagged .asyn) (hσ : IsPendEnum G σ) :
    SeedOK G .asyn (envW ν (word σ)) (ρEnv σ) False := by
  have hS : ∀ s ∈ σ, s.IsSend := fun s hs => ((G.mem_US).mp ((hσ.2 s).mp hs)).2.1
  have hT := sendsTagged_of_exec hP hG.1
  have hw := word_eq_map hS
  have hlen : (word σ).length = σ.length := by rw [hw, List.length_map]
  -- a seed position is a position of `ν` in `σ`
  have hpos : ∀ t j, j < (envW ν (word σ) t).length → t = ν ∧ j < σ.length := by
    intro t j hj
    by_cases ht : t = ν
    · subst ht
      simp only [envW, ↓reduceIte] at hj
      exact ⟨rfl, hlen ▸ hj⟩
    · simp [envW, ht] at hj
  have hρs : ∀ t j, j < (envW ν (word σ) t).length →
      ∃ h : j < σ.length, ρEnv σ (seedEv .asyn (envW ν (word σ)) t j) = σ[j] := by
    intro t j hj
    obtain ⟨-, hjσ⟩ := hpos t j hj
    exact ⟨hjσ, by rw [ρEnv_seed, List.getElem?_eq_getElem hjσ]; rfl⟩
  refine ⟨fun t j hj => ?_, fun t j hj => ?_, fun t j t' j' hj hj' h => ?_, fun s hs => ?_,
    fun h => h.elim, fun h => h.elim⟩
  · obtain ⟨hjσ, he⟩ := hρs t j hj
    rw [he]
    exact (hσ.2 _).mp (List.getElem_mem hjσ)
  · obtain ⟨hjσ, he⟩ := hρs t j hj
    obtain ⟨rfl, -⟩ := hpos t j hj
    rw [he]
    have hmem := (G.mem_US).mp ((hσ.2 _).mp (List.getElem_mem hjσ))
    obtain ⟨m, d, v, hl, hmsg⟩ := msgOf_send hmem.2.1
    have hm : m = .asyn := by
      have := hT _ hmem.1 hmem.2.1
      rw [hl] at this
      simpa [Lab.model?] using this
    subst hm
    have hwj : (word σ)[j]? = some (d, v) := by
      rw [hw, List.getElem?_map, List.getElem?_eq_getElem hjσ]
      simp [hmsg]
    simp only [seedLab, envW, ↓reduceIte, hwj]
    exact hl
  · obtain ⟨hjσ, he⟩ := hρs t j hj
    obtain ⟨hjσ', he'⟩ := hρs t' j' hj'
    obtain ⟨rfl, -⟩ := hpos t j hj
    obtain ⟨rfl, -⟩ := hpos t' j' hj'
    rw [he, he'] at h
    exact ⟨rfl, (hσ.1.getElem_inj_iff).mp h⟩
  · obtain ⟨j, hjσ, rfl⟩ := List.mem_iff_getElem.mp ((hσ.2 s).mpr hs)
    have hj : j < (envW ν (word σ) ν).length := by simp [envW, hlen, hjσ]
    exact ⟨ν, j, hj, (hρs ν j hj).2⟩

omit [Membership Val Q] in
/-- Section 6, `asynAbs.hconf` (plan C5): a word equal to `pend(G)` as a multiset is the word of
a pending enumeration. -/
theorem pendEnum_of_pendM {G : Graph Q} {w : List Msg} (h : (↑w : Multiset Msg) = G.pendM) :
    ∃ σ, IsPendEnum G σ ∧ word σ = w := by
  unfold Graph.pendM at h
  rw [← Finset.coe_toList G.US, Multiset.filterMap_coe, Multiset.coe_eq_coe] at h
  obtain ⟨σ, hp, hw⟩ := exists_perm_filterMap msgOf w G.US.toList h.symm
  exact ⟨σ, ⟨hp.nodup_iff.mpr G.US.nodup_toList, fun s => by
    rw [hp.mem_iff, Finset.mem_toList]⟩, hw⟩

/-! ### Section 7: the seeds -/

/-- Section 7: `P_{s,w}` of the setting is `p2pRes`. -/
theorem p2pRes_eq (S : MPSetting Q) (hS : S.ι = []) {u : Tid → List (Option Val)}
    {w : Tid → List Msg} : S.P.seedRes S.ι S.hι S.m u w = S.P.p2pRes S.m u w := by
  obtain ⟨ms, hms, ord, hord, m, P, hP, ι, hι⟩ := S
  simp only at hS
  subst hS
  rfl

/-- Section 7, `p2pAbs.hconf` (plan C5): the canonical seeds `ρP2P G` (`ord = True`). (The
premise `hS` of the plan is not needed.) -/
theorem seedOK_p2p (S : MPSetting Q) (_hS : S.ι = []) {G : Graph Q}
    (hG : ExecM (Model.ofSet S.ms) S.P G) : SeedOK G S.m G.pend (ρP2P G) True := by
  have hGw : G.Wf := (Model.ofSet S.ms).wf _ hG.2
  have hT := sendsTagged_of_exec S.hP hG.1
  have hlenp := length_pend hGw
  have hρs : ∀ t j, j < (G.pend t).length → ∃ h : j < (G.unreadSeq t).length,
      ρP2P G (seedEv S.m G.pend t j) = (G.unreadSeq t)[j] := by
    intro t j hj
    have hj' : j < (G.unreadSeq t).length := hlenp t ▸ hj
    exact ⟨hj', by rw [ρP2P_seed, List.getElem?_eq_getElem hj']; rfl⟩
  have hmemL : ∀ t j (h : j < (G.unreadSeq t).length), (G.unreadSeq t)[j] ∈ G.US ∧
      ((G.unreadSeq t)[j]).tid = t :=
    fun t j h => (mem_unreadSeq hGw).mp (List.getElem_mem h)
  have hnd : ∀ t, (G.unreadSeq t).Nodup := fun t =>
    (unreadSeq_pairwise G t).imp fun {a b} h e => by subst e; exact lt_irrefl _ h
  refine ⟨fun t j hj => ?_, fun t j hj => ?_, fun t j t' j' hj hj' h => ?_, fun s hs => ?_,
    fun _ t j hj => ?_, fun _ t j j' hj hj' => ?_⟩
  · obtain ⟨h1, he⟩ := hρs t j hj
    rw [he]
    exact (hmemL t j h1).1
  · obtain ⟨h1, he⟩ := hρs t j hj
    rw [he]
    have hmem := (G.mem_US).mp (hmemL t j h1).1
    obtain ⟨m, d, v, hl, hmsg⟩ := msgOf_send hmem.2.1
    have hm : m = S.m := by
      have := hT _ hmem.1 hmem.2.1
      rw [hl] at this
      simpa [Lab.model?] using this
    subst hm
    have hpj : (G.pend t)[j]? = some (d, v) := by
      rw [hGw.pend_eq, ← word, word_eq_map unreadSeq_isSend, List.getElem?_map,
        List.getElem?_eq_getElem h1]
      simp [hmsg]
    simp only [seedLab, hpj]
    exact hl
  · obtain ⟨h1, he⟩ := hρs t j hj
    obtain ⟨h1', he'⟩ := hρs t' j' hj'
    rw [he, he'] at h
    have htt : t = t' := by
      rw [← (hmemL t j h1).2, ← (hmemL t' j' h1').2, h]
    subst htt
    exact ⟨rfl, ((hnd t).getElem_inj_iff).mp h⟩
  · have hsL : s ∈ G.unreadSeq s.tid := (mem_unreadSeq hGw).mpr ⟨hs, rfl⟩
    obtain ⟨j, hj, hjs⟩ := List.mem_iff_getElem.mp hsL
    have hj' : j < (G.pend s.tid).length := (hlenp s.tid).symm ▸ hj
    exact ⟨s.tid, j, hj', by rw [(hρs _ _ hj').2, hjs]⟩
  · obtain ⟨h1, he⟩ := hρs t j hj
    rw [he]
    exact (hmemL t j h1).2
  · obtain ⟨h1, he⟩ := hρs t j hj
    obtain ⟨h1', he'⟩ := hρs t j' hj'
    rw [he, he']
    exact getElem_lt_iff_of_pairwise (unreadSeq_pairwise G t) h1 h1'

/-! ### Bridging lemmas -/

omit [DecidableEq Q] [Membership Val Q] in
theorem ehat_congr_seed {G : Graph Q} {W : Tid → List Msg} {ρ ρ' : Ev Q → Ev Q} {m : Comm}
    {s : Ev Q} (hs : s.idx < (W s.tid).length → s = seedEv m W s.tid s.idx)
    (h : ∀ t j, j < (W t).length → ρ (seedEv m W t j) = ρ' (seedEv m W t j)) :
    G.ehat W ρ s = G.ehat W ρ' s := by
  rcases Nat.lt_or_ge s.idx (W s.tid).length with hi | hi
  · rw [ehat_of_lt hi, ehat_of_lt hi, hs hi]
    exact h _ _ hi
  · rw [ehat_of_ge hi, ehat_of_ge hi]

/-- The composition depends on `ρ` on the seeds only (Opus r2 N2). (The premise `hs` of the
plan is not needed.) -/
theorem scomp_congr_seed {G H : Graph Q} {W : Tid → List Msg} {ρ ρ' : Ev Q → Ev Q} {m : Comm}
    (hH : H.Wf) (_hs : ∀ t, (W t).length ≤ H.cnt t)
    (hlab : ∀ e ∈ H.events, e.idx < (W e.tid).length → e = seedEv m W e.tid e.idx)
    (h : ∀ t j, j < (W t).length → ρ (seedEv m W t j) = ρ' (seedEv m W t j)) :
    G.scomp H W ρ = G.scomp H W ρ' := by
  apply Graph.ext
  · rfl
  · funext e
    simp only [Graph.scomp]
    split_ifs with h1 h2
    · rfl
    · rcases hx : H.rf (G.unemb W e) with _ | (_ | s)
      · rfl
      · rfl
      · simp only [Option.map_some, Src.map]
        rw [ehat_congr_seed (hlab s (hH.rf_mem _ _ hx)) h]
    · rfl
  · rfl

/-- Under `ord = True` the seeds are the canonical ones (Opus r2 N2). (The premise `hS` of the
plan is not needed.) -/
theorem seedOK_p2p_unique (S : MPSetting Q) (_hS : S.ι = []) {G : Graph Q}
    (hG : ExecM (Model.ofSet S.ms) S.P G) {ρ : Ev Q → Ev Q}
    (hρ : SeedOK G S.m G.pend ρ True) :
    ∀ t j, j < (G.pend t).length → ρ (seedEv S.m G.pend t j) = ρP2P G (seedEv S.m G.pend t j) := by
  have hGw : G.Wf := (Model.ofSet S.ms).wf _ hG.2
  intro t j hj
  have hL : List.ofFn (fun i : Fin (G.pend t).length => ρ (seedEv S.m G.pend t i)) =
      G.unreadSeq t := by
    refine eq_of_pairwise_idx ?_ (unreadSeq_pairwise G t) fun s => ?_
    · rw [List.pairwise_ofFn]
      intro i i' hii'
      exact (hρ.mono trivial t i i' i.2 i'.2).mp hii'
    · rw [List.mem_ofFn, mem_unreadSeq hGw]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨hρ.mem t i i.2, hρ.tid trivial t i i.2⟩
      · rintro ⟨hs, rfl⟩
        obtain ⟨t', j', hj', rfl⟩ := hρ.surj s hs
        have ht := hρ.tid trivial t' j' hj'
        rw [ht]
        exact ⟨⟨j', hj'⟩, rfl⟩
  rw [ρP2P_seed, ← hL, List.getElem?_ofFn]
  simp [hj]

/-- `G.scomp H G.pend ρ` is `compP2P G H` for every seeds `ρ` with `ord = True`. (The premise
`hS` of the plan is not needed.) -/
theorem scomp_eq_compP2P (S : MPSetting Q) (_hS : S.ι = []) {G H : Graph Q}
    (hG : ExecM (Model.ofSet S.ms) S.P G) {ρ : Ev Q → Ev Q} (hρ : SeedOK G S.m G.pend ρ True)
    {u : Tid → List (Option Val)}
    (hH : Frag (Model.ofSet S.ms) (S.P.p2pRes S.m u G.pend) G.pend H) :
    G.scomp H G.pend ρ = compP2P G H := by
  have hHw : H.Wf := (Model.ofSet S.ms).wf _ hH.1.2
  refine scomp_congr_seed hHw hH.2 (fun e he hi => ?_) (seedOK_p2p_unique S _hS hG hρ)
  exact hHw.idx_inj e he _ (frag_seedEv hH hi) rfl rfl

/-- Section 6: every seeds `ρ` (`ord = False`) come from a pending enumeration (Opus r2 N2).
(The premises `hG`, `hP` of the plan are not needed.) -/
theorem seedOK_env_enum {P : Program Q} {G : Graph Q} {ν : Tid} {hν : ν ∉ P.threads}
    {w : List Msg} {ρ : Ev Q → Ev Q} (_hG : ExecM Model.asyn P G) (_hP : P.Tagged .asyn)
    (hρ : SeedOK G .asyn (envW ν w) ρ False) :
    ∃ σ, IsPendEnum G σ ∧ word σ = w ∧
      ∀ u H, Frag Model.asyn (P.envRes ν hν u w) (envW ν w) H →
        G.scomp H (envW ν w) ρ = compEnv G ν σ H := by
  have hWν : envW ν w ν = w := by simp [envW]
  have hpos : ∀ t j, j < (envW ν w t).length → t = ν := by
    intro t j hj
    by_contra ht
    simp [envW, ht] at hj
  let f : Fin w.length → Ev Q := fun j => ρ (seedEv .asyn (envW ν w) ν j)
  have hfj : ∀ j : Fin w.length, j.1 < (envW ν w ν).length := fun j => by rw [hWν]; exact j.2
  have hword : word (List.ofFn f) = w := by
    have hmsg : ∀ j : Fin w.length, msgOf (f j) = some (w[j.1]) := fun j => by
      have hl := hρ.lab ν j (hfj j)
      have hwj : (envW ν w ν)[j.1]? = some w[j.1] := by
        rw [hWν, List.getElem?_eq_getElem j.2]
      unfold seedLab at hl
      rw [hwj] at hl
      simp [msgOf, f, hl]
    unfold word
    rw [List.ofFn_eq_map, List.filterMap_map]
    rw [show (msgOf ∘ f) = fun j => some (w[j.1]) from funext hmsg, List.filterMap_eq_map',
      ← List.ofFn_eq_map, List.ofFn_getElem]
  refine ⟨List.ofFn f, ⟨List.nodup_ofFn_ofInjective fun i i' h =>
    Fin.ext (hρ.inj ν i ν i' (hfj i) (hfj i') h).2, fun s => ?_⟩, hword, fun u H hH => ?_⟩
  · rw [List.mem_ofFn]
    constructor
    · rintro ⟨i, rfl⟩
      exact hρ.mem ν i (hfj i)
    · intro hs
      obtain ⟨t, j, hj, rfl⟩ := hρ.surj s hs
      obtain rfl := hpos t j hj
      exact ⟨⟨j, hWν ▸ hj⟩, rfl⟩
  · have hHw : H.Wf := Model.asyn.wf _ hH.1.2
    unfold compEnv
    rw [hword]
    refine scomp_congr_seed (m := .asyn) hHw hH.2 (fun e he hi => ?_) fun t j hj => ?_
    · exact hHw.idx_inj e he _ (frag_seedEv hH hi) rfl rfl
    · obtain rfl := hpos t j hj
      rw [ρEnv_seed, List.getElem?_ofFn]
      have hj' : j < w.length := hWν ▸ hj
      simp [hj', f]

/-! ### Section 6: lem:mp-compose and prop:mp-compose -/

section Env

variable {P : Program Q} {ν : Tid} (hν : ν ∉ P.threads) (hP : P.Tagged .asyn) {G H F : Graph Q}
  (hG : ExecM Model.asyn P G) {σ : List (Ev Q)} (hσ : IsPendEnum G σ)

omit [DecidableEq Q] [Membership Val Q] in
theorem envW_nil {ν t : Tid} {w : List Msg} (ht : t ≠ ν) : envW ν w t = [] := by
  simp [envW, ht]

include hν in
theorem env_hW : ∀ t ∉ (envSetting P ν hν hP).ts, envW ν (word σ) t = [] := fun t ht =>
  envW_nil fun h => ht (List.mem_append_right _ (h ▸ List.mem_singleton_self _))

include hν in
theorem env_hu : ∀ t ∈ (envSetting P ν hν hP).P.threads,
    FutEq ((envSetting P ν hν hP).P.step t) (G.trace t) (G.trace t) := fun _ _ _ => rfl

include hP hG hσ in
/-- lem:mp-compose (1). -/
theorem mp_compose_1 (hH : Frag Model.asyn (P.envRes ν hν G.trace (word σ)) (envW ν (word σ)) H) :
    ExecM Model.asyn P (compEnv G ν σ H) ∧ G.IsPrefixOf (compEnv G ν σ H) ∧
    compEnv G ν σ (seedGraph (P.threads ++ [ν]) .asyn (envW ν (word σ))) = G :=
  ⟨(frag_scomp (envSetting P ν hν hP) hG (env_hu hν hP) (env_hW hν hP) (seedOK_env hG hP hσ) hH).1,
    (frag_scomp (envSetting P ν hν hP) hG (env_hu hν hP) (env_hW hν hP) (seedOK_env hG hP hσ) hH).2,
    scomp_seed (Model.asyn.wf _ hG.2)⟩

include hP hG hσ in
/-- lem:mp-compose (2). -/
theorem mp_compose_2 (hH : Frag Model.asyn (P.envRes ν hν G.trace (word σ)) (envW ν (word σ)) H) :
    (∀ e ∈ H.events, e.tid ≠ ν → (compEnv G ν σ H).ret (G.emb (envW ν (word σ)) e) = H.ret e) ∧
    (∀ e ∈ G.events, (compEnv G ν σ H).ret e = G.ret e) ∧
    ∀ t ∈ P.threads, (compEnv G ν σ H).trace t = G.trace t ++ H.trace t := by
  have hGw : G.Wf := Model.asyn.wf _ hG.2
  have hHw : H.Wf := Model.asyn.wf _ hH.1.2
  have hρ := seedOK_env (ν := ν) hG hP hσ
  have hseed := fun t j (hj : j < (envW ν (word σ) t).length) => frag_seedEv hH hj
  refine ⟨fun e he hne => ?_, fun e he => scomp_ret_old he, fun t ht => ?_⟩
  · exact scomp_ret_emb hGw hHw hseed hρ he (by rw [envW_nil hne]; exact Nat.zero_le _)
  · have htν : t ≠ ν := fun h => hν (h ▸ ht)
    unfold compEnv
    rw [scomp_trace hGw hHw hH.2 hseed hρ t, envW_nil htν]
    rfl

include hP hG hσ in
/-- lem:mp-compose (3). -/
theorem mp_compose_3 (hH : Frag Model.asyn (P.envRes ν hν G.trace (word σ)) (envW ν (word σ)) H) :
    Set.BijOn (G.ehat (envW ν (word σ)) (ρEnv σ)) ↑H.S
      (↑σ.toFinset ∪ ↑((compEnv G ν σ H).S \ G.events)) ∧
    (∀ x ∈ H.S, (G.ehat (envW ν (word σ)) (ρEnv σ) x).lab = x.lab) ∧
    (compEnv G ν σ H).US = H.US.image (G.ehat (envW ν (word σ)) (ρEnv σ)) ∧
    (compEnv G ν σ H).pendM = H.pendM := by
  have hGw : G.Wf := Model.asyn.wf _ hG.2
  have hHw : H.Wf := Model.asyn.wf _ hH.1.2
  have hρ := seedOK_env (ν := ν) hG hP hσ
  have hseed := fun t j (hj : j < (envW ν (word σ) t).length) => frag_seedEv hH hj
  have hσU : σ.toFinset = G.US := by
    ext s
    rw [List.mem_toFinset]
    exact hσ.2 s
  refine ⟨?_, ehat_lab hHw hseed hρ, us_scomp (envSetting P ν hν hP) hG hρ hH,
    pendM_scomp (envSetting P ν hν hP) hG hρ hH⟩
  rw [hσU]
  exact ehat_bij hGw hHw hseed hρ

include hP hG hσ in
/-- lem:mp-compose (4). -/
theorem mp_compose_4 (hH : Frag Model.asyn (P.envRes ν hν G.trace (word σ)) (envW ν (word σ)) H)
    (hF : Frag Model.asyn (P.envRes ν hν G.trace (word σ)) (envW ν (word σ)) F)
    (hp : H.IsPrefixOf F) : (compEnv G ν σ H).IsPrefixOf (compEnv G ν σ F) :=
  scomp_mono (envSetting P ν hν hP) hG (env_hu hν hP) (env_hW hν hP) (seedOK_env hG hP hσ) hH hF
    hp

include hP hG hσ in
/-- prop:mp-compose (1). -/
theorem mp_compose_steps_1
    (hH : Frag Model.asyn (P.envRes ν hν G.trace (word σ)) (envW ν (word σ)) H)
    (h : OpStepG Model.asyn (P.envRes ν hν G.trace (word σ)) H H') :
    Frag Model.asyn (P.envRes ν hν G.trace (word σ)) (envW ν (word σ)) H' ∧
      OpStepG Model.asyn P (compEnv G ν σ H) (compEnv G ν σ H') :=
  step_scomp (envSetting P ν hν hP) hG (env_hu hν hP) (env_hW hν hP) (seedOK_env hG hP hσ) hH h

include hP hG hσ in
/-- prop:mp-compose (2). -/
theorem mp_compose_steps_2
    (hH : Frag Model.asyn (P.envRes ν hν G.trace (word σ)) (envW ν (word σ)) H) {G' : Graph Q}
    (h : OpStepG Model.asyn P (compEnv G ν σ H) G') :
    ∃! H', Frag Model.asyn (P.envRes ν hν G.trace (word σ)) (envW ν (word σ)) H' ∧
      OpStepG Model.asyn (P.envRes ν hν G.trace (word σ)) H H' ∧ G' = compEnv G ν σ H' :=
  scomp_step (envSetting P ν hν hP) hG (env_hu hν hP) (env_hW hν hP) (seedOK_env hG hP hσ) hH h

include hP hG hσ in
/-- prop:mp-compose (3). -/
theorem mp_compose_steps_3 (n : ℕ) (G' : Graph Q) :
    StepsN Model.asyn P n G G' ↔
      ∃ H, Frag Model.asyn (P.envRes ν hν G.trace (word σ)) (envW ν (word σ)) H ∧
        H.len (P.threads ++ [ν]) (envW ν (word σ)) = n ∧ G' = compEnv G ν σ H :=
  stepsN_iff_frag (envSetting P ν hν hP) hG (env_hu hν hP) (env_hW hν hP)
    (seedOK_env hG hP hσ) n G'

end Env

/-! ### Section 7: lem:p2p-compose and prop:p2p-compose -/

section P2P

variable (S : MPSetting Q) (hS : S.ι = []) (hT : S.ord) {G H H' F : Graph Q}
  (hG : ExecM (Model.ofSet S.ms) S.P G)

include hG in
theorem p2p_hW : ∀ t ∉ S.ts, G.pend t = [] := fun _ ht =>
  pend_nil ((Model.ofSet S.ms).wf _ hG.2) hG.1 fun h => ht (List.mem_append_left _ h)

include hS hG in
theorem p2p_hρ : SeedOK G S.m G.pend (ρP2P G) S.ord :=
  (seedOK_p2p S hS hG).weaken fun _ => trivial

theorem p2p_hu : ∀ t ∈ S.P.threads, FutEq (S.P.step t) (G.trace t) (G.trace t) :=
  fun _ _ _ => rfl

include hS in
theorem p2p_R : S.P.p2pRes S.m G.trace G.pend = S.P.seedRes S.ι S.hι S.m G.trace G.pend :=
  (p2pRes_eq S hS).symm

include hS hT hG in
/-- lem:p2p-compose (1). -/
theorem p2p_compose_1 (hH : Frag (Model.ofSet S.ms) (S.P.p2pRes S.m G.trace G.pend) G.pend H) :
    Set.BijOn (G.ehat G.pend (ρP2P G)) ↑H.S (↑G.US ∪ ↑((compP2P G H).S \ G.events)) ∧
    (∀ x ∈ H.S, (G.ehat G.pend (ρP2P G) x).lab = x.lab ∧
      (G.ehat G.pend (ρP2P G) x).tid = x.tid) ∧
    (∀ x ∈ H.S, ∀ y ∈ H.S, x.tid = y.tid →
      (x.idx < y.idx ↔ (G.ehat G.pend (ρP2P G) x).idx < (G.ehat G.pend (ρP2P G) y).idx)) ∧
    (∀ x ∈ H.S, ∀ y ∈ H.S, (H.soPaper x y ↔
      (compP2P G H).soPaper (G.ehat G.pend (ρP2P G) x) (G.ehat G.pend (ρP2P G) y))) ∧
    (compP2P G H).US = H.US.image (G.ehat G.pend (ρP2P G)) ∧
    ∀ t, (compP2P G H).pend t = H.pend t := by
  rw [p2p_R S hS] at hH
  have hGw : G.Wf := (Model.ofSet S.ms).wf _ hG.2
  have hHw : H.Wf := (Model.ofSet S.ms).wf _ hH.1.2
  have hρ := p2p_hρ S hS hG
  have hseed := fun t j (hj : j < (G.pend t).length) => frag_seedEv hH hj
  exact ⟨ehat_bij hGw hHw hseed hρ,
    fun x hx => ⟨ehat_lab hHw hseed hρ x hx, ehat_tid hHw hseed hρ hT x hx⟩,
    ehat_idx hGw hHw hseed hρ hT, ehat_soPaper hGw hHw hseed hρ hT,
    us_scomp S hG hρ hH, pend_scomp S hG (p2p_hu S) (p2p_hW S hG) hρ hT hH⟩

include hS hG in
/-- lem:p2p-compose (2). -/
theorem p2p_compose_2 (hH : Frag (Model.ofSet S.ms) (S.P.p2pRes S.m G.trace G.pend) G.pend H) :
    (∀ e ∈ H.events, (G.pend e.tid).length ≤ e.idx →
      (compP2P G H).ret (G.emb G.pend e) = H.ret e) ∧
    (∀ e ∈ G.events, (compP2P G H).ret e = G.ret e) ∧
    ∀ t, (compP2P G H).trace t = G.trace t ++ (H.trace t).drop (G.pend t).length := by
  rw [p2p_R S hS] at hH
  have hGw : G.Wf := (Model.ofSet S.ms).wf _ hG.2
  have hHw : H.Wf := (Model.ofSet S.ms).wf _ hH.1.2
  have hρ := p2p_hρ S hS hG
  have hseed := fun t j (hj : j < (G.pend t).length) => frag_seedEv hH hj
  exact ⟨fun e he hi => scomp_ret_emb hGw hHw hseed hρ he hi, fun e he => scomp_ret_old he,
    scomp_trace hGw hHw hH.2 hseed hρ⟩

include hS hG in
/-- lem:p2p-compose (3). -/
theorem p2p_compose_3 (hH : Frag (Model.ofSet S.ms) (S.P.p2pRes S.m G.trace G.pend) G.pend H) :
    ExecM (Model.ofSet S.ms) S.P (compP2P G H) ∧ G.IsPrefixOf (compP2P G H) ∧
    compP2P G (seedGraph S.P.threads S.m G.pend) = G := by
  rw [p2p_R S hS] at hH
  exact ⟨(frag_scomp S hG (p2p_hu S) (p2p_hW S hG) (p2p_hρ S hS hG) hH).1,
    (frag_scomp S hG (p2p_hu S) (p2p_hW S hG) (p2p_hρ S hS hG) hH).2,
    scomp_seed ((Model.ofSet S.ms).wf _ hG.2)⟩

include hS hG in
/-- lem:p2p-compose (4). -/
theorem p2p_compose_4 (hH : Frag (Model.ofSet S.ms) (S.P.p2pRes S.m G.trace G.pend) G.pend H)
    (hF : Frag (Model.ofSet S.ms) (S.P.p2pRes S.m G.trace G.pend) G.pend F)
    (hp : H.IsPrefixOf F) : (compP2P G H).IsPrefixOf (compP2P G F) := by
  rw [p2p_R S hS] at hH hF
  exact scomp_mono S hG (p2p_hu S) (p2p_hW S hG) (p2p_hρ S hS hG) hH hF hp

include hS hG in
/-- prop:p2p-compose (1). -/
theorem p2p_compose_steps_1
    (hH : Frag (Model.ofSet S.ms) (S.P.p2pRes S.m G.trace G.pend) G.pend H)
    (h : OpStepG (Model.ofSet S.ms) (S.P.p2pRes S.m G.trace G.pend) H H') :
    Frag (Model.ofSet S.ms) (S.P.p2pRes S.m G.trace G.pend) G.pend H' ∧
      OpStepG (Model.ofSet S.ms) S.P (compP2P G H) (compP2P G H') := by
  rw [p2p_R S hS] at hH h ⊢
  exact step_scomp S hG (p2p_hu S) (p2p_hW S hG) (p2p_hρ S hS hG) hH h

include hS hG in
/-- prop:p2p-compose (2). -/
theorem p2p_compose_steps_2
    (hH : Frag (Model.ofSet S.ms) (S.P.p2pRes S.m G.trace G.pend) G.pend H) {G' : Graph Q}
    (h : OpStepG (Model.ofSet S.ms) S.P (compP2P G H) G') :
    ∃! H', Frag (Model.ofSet S.ms) (S.P.p2pRes S.m G.trace G.pend) G.pend H' ∧
      OpStepG (Model.ofSet S.ms) (S.P.p2pRes S.m G.trace G.pend) H H' ∧ G' = compP2P G H' := by
  rw [p2p_R S hS] at hH ⊢
  exact scomp_step S hG (p2p_hu S) (p2p_hW S hG) (p2p_hρ S hS hG) hH h

include hS hG in
/-- prop:p2p-compose (3). -/
theorem p2p_compose_steps_3 (n : ℕ) (G' : Graph Q) :
    StepsN (Model.ofSet S.ms) S.P n G G' ↔
      ∃ H, Frag (Model.ofSet S.ms) (S.P.p2pRes S.m G.trace G.pend) G.pend H ∧
        H.len S.P.threads G.pend = n ∧ G' = compP2P G H := by
  rw [p2p_R S hS]
  have hts : S.ts = S.P.threads := by
    unfold MPSetting.ts
    rw [hS, List.append_nil]
  rw [← hts]
  exact stepsN_iff_frag S hG (p2p_hu S) (p2p_hW S hG) (p2p_hρ S hS hG) n G'

end P2P

end Ind

end Must
