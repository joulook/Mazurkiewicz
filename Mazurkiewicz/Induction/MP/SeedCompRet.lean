import Mazurkiewicz.Induction.MP.SeedComp

/-!
# Message passing: values, traces and sends of a composition (milestone C3b)

`induction-popl`, `mp.tex` lem:mp-compose (2) (returned values, traces) and `p2p.tex`
lem:p2p-compose (1) (`ê` a label-, thread- and order-preserving bijection from the sends of
the fragment onto the unread sends of `G` and the new sends; `so` iff) and (2), for the one
construction `Graph.scomp` (plan `plan/ind/TRACK-C-PLAN.md`, milestone C3b).

Context (plan C3b): `hG : G.Wf`, `hH : H.Wf`, `hs : ∀ t, (W t).length ≤ H.cnt t`,
`hseed : ∀ t j, j < (W t).length → seedEv m W t j ∈ H.events`, `hρ : SeedOK G m W ρ ord`,
`G⁺ := G.scomp H W ρ`. Each theorem takes the hypotheses of the context that its proof uses
(the others are omitted; the statements are then stronger).

* `scomp_ret_old`, `scomp_ret_emb`, `scomp_trace` (lem:mp-compose (2), lem:p2p-compose (2)).
* `ehat_lab`, `ehat_bij`: `ê` is a label-preserving bijection from the sends of `H` onto
  `G.US ∪ (G⁺.S \ G.E)` (lem:mp-compose (3), first part; lem:p2p-compose (1)).
* Under `ord`: `ehat_tid`, `ehat_idx` (thread and index order kept), `ehat_soDst`,
  `ehat_soPaper` (`so|dst` of the port and `so` of def:p2p are kept both ways).
* Helpers: `seed_eq`, `ehat_lab_mem`, `scomp_retAt_old`, `scomp_retAt_emb`, `ehat_mem`,
  `ehat_po`.
-/

namespace Must

namespace Ind

open Graph

variable {Q : Type} [DecidableEq Q] [Membership Val Q]
variable {G H : Graph Q} {W : Tid → List Msg} {ρ : Ev Q → Ev Q} {m : Comm} {ord : Prop}
variable (hG : G.Wf) (hH : H.Wf) (hs : ∀ t, (W t).length ≤ H.cnt t)
  (hseed : ∀ t j, j < (W t).length → seedEv m W t j ∈ H.events) (hρ : SeedOK G m W ρ ord)

omit [DecidableEq Q] in
include hH hseed in
/-- An event of `H` at a seed position is the seed event. -/
theorem seed_eq {x : Ev Q} (hx : x ∈ H.events) (hi : x.idx < (W x.tid).length) :
    x = seedEv m W x.tid x.idx :=
  hH.idx_inj x hx _ (hseed _ _ hi) rfl rfl

include hH hseed hρ in
/-- `ê` keeps the label of an event of `H`. -/
theorem ehat_lab_mem {x : Ev Q} (hx : x ∈ H.events) : (G.ehat W ρ x).lab = x.lab := by
  rcases Nat.lt_or_ge x.idx (W x.tid).length with hi | hi
  · have hρx : ρ x = ρ (seedEv m W x.tid x.idx) := congrArg ρ (seed_eq hH hseed hx hi)
    rw [ehat_of_lt hi, hρx, hρ.lab _ _ hi, seed_eq hH hseed hx hi]
    rfl
  · rw [ehat_of_ge hi]
    rfl

include hH hseed hρ in
/-- lem:p2p-compose (1): `ê` keeps labels. -/
theorem ehat_lab : ∀ x ∈ H.S, (G.ehat W ρ x).lab = x.lab :=
  fun _ hx => ehat_lab_mem hH hseed hρ ((H.mem_S).mp hx).1

omit [Membership Val Q] in
/-- lem:mp-compose (2): the returned values of the events of `G` are kept. -/
theorem scomp_ret_old {e : Ev Q} (he : e ∈ G.events) : (G.scomp H W ρ).ret e = G.ret e := by
  unfold Graph.ret
  rw [scomp_rf_old he, scomp_nd_old he]

include hG hH hseed hρ in
/-- lem:mp-compose (2): an embedded event returns what it returns in `H`. -/
theorem scomp_ret_emb {e : Ev Q} (he : e ∈ H.events) (hi : (W e.tid).length ≤ e.idx) :
    (G.scomp H W ρ).ret (G.emb W e) = H.ret e := by
  unfold Graph.ret
  rw [scomp_rf_emb hG he hi, scomp_nd_emb hG he hi]
  rcases h : H.rf e with _ | (_ | s)
  · rfl
  · rfl
  · simp only [Option.map_some, Src.map]
    rw [ehat_lab_mem hH hseed hρ (hH.rf_mem e s h)]

omit [Membership Val Q] in
/-- The values returned before `G.cnt t` are those of `G`. -/
theorem scomp_retAt_old {t : Tid} {j : ℕ} (hj : j < G.cnt t) :
    (G.scomp H W ρ).retAt t j = G.retAt t j := by
  refine (retAt_congr (fun x h1 h2 => ⟨fun h => mem_scomp.mpr (Or.inl h), fun h => ?_⟩)
    (fun x hx _ _ => ⟨(scomp_rf_old hx).symm, (scomp_nd_old hx).symm⟩)).symm
  rcases mem_scomp.mp h with h | ⟨e, -, -, rfl⟩
  · exact h
  · simp only [emb_tid, emb_idx] at h1 h2
    rw [h1] at h2
    omega

include hG hH hseed hρ in
/-- The values returned from `G.cnt t` on are those of `H` from `(W t).length` on. -/
theorem scomp_retAt_emb {t : Tid} {k : ℕ} (hk : (W t).length + k < H.cnt t) :
    (G.scomp H W ρ).retAt t (G.cnt t + k) = H.retAt t ((W t).length + k) := by
  obtain ⟨y, hy, rfl, hyi⟩ := (hH.exists_idx_iff t _).mpr hk
  have hyW : (W y.tid).length ≤ y.idx := by omega
  have hf : (G.scomp H W ρ).events.filter (fun x => x.tid = y.tid ∧ x.idx = G.cnt y.tid + k) =
      {G.emb W y} := by
    ext x
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, h1, h2⟩
      rcases mem_scomp.mp hx with hx | ⟨z, hz, hzi, rfl⟩
      · have := hG.idx_lt_cnt hx
        rw [h1, h2] at this
        omega
      · simp only [emb_tid, emb_idx] at h1 h2
        rw [h1] at h2 hzi
        have : z = y := hH.idx_inj z hz y hy h1 (by omega)
        rw [this]
    · rintro rfl
      exact ⟨mem_scomp.mpr (Or.inr ⟨y, hy, hyW, rfl⟩), rfl, by simp; omega⟩
  unfold retAt
  rw [hf, Finset.sup_singleton, decR_encR, scomp_ret_emb hG hH hseed hρ hy hyW, ← hyi,
    ← hH.retAt_eq hy]
  rfl

include hG hH hs hseed hρ in
/-- lem:mp-compose (2), lem:p2p-compose (2): the trace of a thread in `G ⊕ H` is its trace in
`G` followed by its trace in `H` after the seeds. -/
theorem scomp_trace (t : Tid) :
    (G.scomp H W ρ).trace t = G.trace t ++ (H.trace t).drop (W t).length := by
  unfold trace traceBefore
  rw [scomp_cnt hG hH hs t, List.range_add, List.map_append]
  have hH' : H.cnt t = (W t).length + (H.cnt t - (W t).length) := by have := hs t; omega
  rw [hH', List.range_add, List.map_append, List.drop_left' (by simp), ← hH']
  congr 1
  · exact List.map_congr_left fun j hj => scomp_retAt_old (List.mem_range.mp hj)
  · rw [List.map_map, List.map_map]
    refine List.map_congr_left fun k hk => ?_
    exact scomp_retAt_emb hG hH hseed hρ (by have := List.mem_range.mp hk; omega)

include hG hH hseed hρ in
/-- lem:mp-compose (3), lem:p2p-compose (1): `ê` is a bijection from the sends of `H` onto the
unread sends of `G` and the new sends. -/
theorem ehat_bij :
    Set.BijOn (G.ehat W ρ) ↑H.S (↑G.US ∪ ↑((G.scomp H W ρ).S \ G.events)) := by
  have hsd : ∀ x ∈ H.events, x.idx < (W x.tid).length → x = seedEv m W x.tid x.idx :=
    fun x hx hi => seed_eq hH hseed hx hi
  refine ⟨fun x hx => ?_, fun x hx y hy h => ?_, fun y hy => ?_⟩
  · have hx := (H.mem_S).mp (Finset.mem_coe.mp hx)
    rcases Nat.lt_or_ge x.idx (W x.tid).length with hi | hi
    · left
      rw [Finset.mem_coe, ehat_of_lt hi, hsd x hx.1 hi]
      exact hρ.mem _ _ hi
    · right
      rw [Finset.mem_coe, ehat_of_ge hi, Finset.mem_sdiff, mem_S]
      exact ⟨⟨mem_scomp.mpr (Or.inr ⟨x, hx.1, hi, rfl⟩), hx.2⟩, hG.emb_not_mem x⟩
  · have hx := ((H.mem_S).mp (Finset.mem_coe.mp hx)).1
    have hy := ((H.mem_S).mp (Finset.mem_coe.mp hy)).1
    exact hρ.ehat_inj hG (hsd x hx) (hsd y hy) h
  · rcases hy with hy | hy
    · obtain ⟨t, j, hj, rfl⟩ := hρ.surj y (Finset.mem_coe.mp hy)
      refine ⟨seedEv m W t j, Finset.mem_coe.mpr ((H.mem_S).mpr ⟨hseed t j hj, ?_⟩), ?_⟩
      · exact seedLab_isSend hj
      · exact ehat_of_lt hj
    · obtain ⟨hyS, hyG⟩ := Finset.mem_sdiff.mp (Finset.mem_coe.mp hy)
      obtain ⟨hyE, hyS⟩ := (mem_S _).mp hyS
      rcases mem_scomp.mp hyE with h | ⟨z, hz, hzi, rfl⟩
      · exact absurd h hyG
      · exact ⟨z, Finset.mem_coe.mpr ((H.mem_S).mpr ⟨hz, hyS⟩), ehat_of_ge hzi⟩

include hG hH hseed hρ in
/-- `ê` maps the sends of `H` into the events of `G ⊕ H`. -/
theorem ehat_mem {x : Ev Q} (hx : x ∈ H.S) : G.ehat W ρ x ∈ (G.scomp H W ρ).events := by
  rcases (ehat_bij hG hH hseed hρ).mapsTo (Finset.mem_coe.mpr hx) with h | h
  · exact mem_scomp.mpr (Or.inl ((G.mem_US).mp (Finset.mem_coe.mp h)).1)
  · exact ((mem_S _).mp (Finset.mem_sdiff.mp (Finset.mem_coe.mp h)).1).1

include hH hseed hρ in
/-- lem:p2p-compose (1), under `ord`: `ê` keeps the thread of a send. -/
theorem ehat_tid (ho : ord) : ∀ x ∈ H.S, (G.ehat W ρ x).tid = x.tid := by
  intro x hx
  rcases Nat.lt_or_ge x.idx (W x.tid).length with hi | hi
  · have hρx : ρ x = ρ (seedEv m W x.tid x.idx) :=
      congrArg ρ (seed_eq hH hseed ((H.mem_S).mp hx).1 hi)
    rw [ehat_of_lt hi, hρx, hρ.tid ho _ _ hi]
  · rw [ehat_of_ge hi]
    rfl

include hG hH hseed hρ in
/-- lem:p2p-compose (1), under `ord`: `ê` keeps the index order within a thread. -/
theorem ehat_idx (ho : ord) : ∀ x ∈ H.S, ∀ y ∈ H.S, x.tid = y.tid →
    (x.idx < y.idx ↔ (G.ehat W ρ x).idx < (G.ehat W ρ y).idx) := by
  intro x hx y hy hxy
  have hxH := ((H.mem_S).mp hx).1
  have hyH := ((H.mem_S).mp hy).1
  -- a seed of thread `t` goes to an event of `G` of thread `t`
  have hlt : ∀ z ∈ H.events, z.idx < (W z.tid).length →
      (ρ z).idx < G.cnt z.tid := fun z hz hi => by
    have hzs : ρ z = ρ (seedEv m W z.tid z.idx) := congrArg ρ (seed_eq hH hseed hz hi)
    have hmem := ((G.mem_US).mp (hρ.mem _ _ hi)).1
    have := hG.idx_lt_cnt hmem
    rw [hρ.tid ho _ _ hi] at this
    rw [hzs]
    exact this
  rcases Nat.lt_or_ge x.idx (W x.tid).length with hi | hi <;>
    rcases Nat.lt_or_ge y.idx (W y.tid).length with hj | hj
  · have hρx : ρ x = ρ (seedEv m W x.tid x.idx) := congrArg ρ (seed_eq hH hseed hxH hi)
    have hρy : ρ y = ρ (seedEv m W y.tid y.idx) := congrArg ρ (seed_eq hH hseed hyH hj)
    rw [ehat_of_lt hi, ehat_of_lt hj, hρx, hρy, ← hxy]
    exact hρ.mono ho _ _ _ hi (hxy ▸ hj)
  · rw [ehat_of_lt hi, ehat_of_ge hj, emb_idx, ← hxy]
    have := hlt x hxH hi
    rw [← hxy] at hj
    exact iff_of_true (by omega) (by omega)
  · rw [ehat_of_ge hi, ehat_of_lt hj, emb_idx, hxy]
    have := hlt y hyH hj
    rw [hxy] at hi
    exact iff_of_false (by omega) (by omega)
  · rw [ehat_of_ge hi, ehat_of_ge hj, emb_idx, emb_idx, ← hxy]
    rw [← hxy] at hj
    omega

include hG hH hseed hρ in
/-- Under `ord`, `ê` keeps `po` between sends. -/
theorem ehat_po (ho : ord) : ∀ x ∈ H.S, ∀ y ∈ H.S,
    (H.po x y ↔ (G.scomp H W ρ).po (G.ehat W ρ x) (G.ehat W ρ y)) := by
  intro x hx y hy
  have htx := ehat_tid hH hseed hρ ho x hx
  have hty := ehat_tid hH hseed hρ ho y hy
  have hidx := ehat_idx hG hH hseed hρ ho x hx y hy
  constructor
  · rintro ⟨-, -, ht, hi⟩
    exact ⟨ehat_mem hG hH hseed hρ hx, ehat_mem hG hH hseed hρ hy, by rw [htx, hty, ht],
      (hidx ht).mp hi⟩
  · rintro ⟨-, -, ht, hi⟩
    have ht' : x.tid = y.tid := by rw [← htx, ← hty, ht]
    exact ⟨((H.mem_S).mp hx).1, ((H.mem_S).mp hy).1, ht', (hidx ht').mpr hi⟩

include hG hH hseed hρ in
/-- lem:p2p-compose (1), under `ord`: `so|dst` of the port is kept both ways. -/
theorem ehat_soDst (ho : ord) : ∀ x ∈ H.S, ∀ y ∈ H.S,
    (H.SoDst x y ↔ (G.scomp H W ρ).SoDst (G.ehat W ρ x) (G.ehat W ρ y)) := by
  intro x hx y hy
  have hlx := ehat_lab hH hseed hρ x hx
  have hly := ehat_lab hH hseed hρ y hy
  have hpo := ehat_po hG hH hseed hρ ho x hx y hy
  have hsx : (G.ehat W ρ x).IsSend ↔ x.IsSend := by
    change (G.ehat W ρ x).lab.IsSend ↔ x.lab.IsSend
    rw [hlx]
  have hsy : (G.ehat W ρ y).IsSend ↔ y.IsSend := by
    change (G.ehat W ρ y).lab.IsSend ↔ y.lab.IsSend
    rw [hly]
  unfold Graph.SoDst
  rw [hlx, hly, hsx, hsy, ← hpo]

include hG hH hseed hρ in
/-- lem:p2p-compose (1), under `ord`: `so` of def:p2p is kept both ways. -/
theorem ehat_soPaper (ho : ord) : ∀ x ∈ H.S, ∀ y ∈ H.S,
    (H.soPaper x y ↔ (G.scomp H W ρ).soPaper (G.ehat W ρ x) (G.ehat W ρ y)) := by
  intro x hx y hy
  have hlx := ehat_lab hH hseed hρ x hx
  have hly := ehat_lab hH hseed hρ y hy
  have htx := ehat_tid hH hseed hρ ho x hx
  have hty := ehat_tid hH hseed hρ ho y hy
  have hidx := ehat_idx hG hH hseed hρ ho x hx y hy
  have hxS := (H.mem_S).mp hx
  have hyS := (H.mem_S).mp hy
  have hsx : (G.ehat W ρ x).IsSend := by
    change (G.ehat W ρ x).lab.IsSend
    rw [hlx]
    exact hxS.2
  have hsy : (G.ehat W ρ y).IsSend := by
    change (G.ehat W ρ y).lab.IsSend
    rw [hly]
    exact hyS.2
  constructor
  · rintro ⟨-, -, -, -, ht, hd, hi⟩
    exact ⟨ehat_mem hG hH hseed hρ hx, ehat_mem hG hH hseed hρ hy, hsx, hsy,
      by rw [htx, hty, ht], by rw [hlx, hly, hd], (hidx ht).mp hi⟩
  · rintro ⟨-, -, -, -, ht, hd, hi⟩
    have ht' : x.tid = y.tid := by rw [← htx, ← hty, ht]
    exact ⟨hxS.1, hyS.1, hxS.2, hyS.2, ht', by rw [← hlx, ← hly, hd], (hidx ht').mpr hi⟩

end Ind

end Must
