import Mazurkiewicz.Induction.MP.Programs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Message passing: composition with a seeded fragment (milestone C3a)

`induction-popl`, `mp.tex` def:mp-compose (`G ⊕_σ H`, `emb`, `ê`) and `p2p.tex`
def:p2p-compose (`G ⊕ H`), as one construction (plan `plan/ind/TRACK-C-PLAN.md`, Section 4.1
and milestone C3a).

* `Graph.emb G W e`: the event `e` of a fragment, past its seeds, moved behind the events of its
  thread in `G` (`emb` of def:mp-compose); `Graph.unemb` its inverse.
* `Graph.ehat G W ρ`: `ê`: a seed is sent to its unread send of `G` by `ρ`, another event by
  `emb`. `Src.map` applies it to a source.
* `Graph.scomp G H W ρ`: `G ⊕ H`: `G`, and the non-seed events of `H` embedded, with sources
  through `ê` and outcomes kept.
* `SeedOK G m W ρ ord`: `ρ` is a label-preserving bijection from the seed events onto `G.US`,
  and, if `ord`, it keeps the thread and the index order (Section 7).
* `scomp_seed` (`G ⊕ Z_w = G`), `scomp_add` (composition commutes with adding a non-seed
  event), `scomp_cnt`, `scomp_injective`.
* Helpers: `emb`/`unemb` lemmas, `mem_scomp`, `scomp_rf_old`, `scomp_rf_emb`, `scomp_nd_old`,
  `scomp_nd_emb`, `Wf.card_filter_ge`, `SeedOK.ehat_inj`.
-/

namespace Must

open Ind

/-- A source mapped by a function on events. -/
def Src.map {Q : Type} (f : Ev Q → Ev Q) : Src Q → Src Q
  | .bot => .bot
  | .snd s => .snd (f s)

namespace Graph

variable {Q : Type} [DecidableEq Q]

/-- `emb` (def:mp-compose): a non-seed event of a fragment behind the events of its thread in
`G`. -/
def emb (G : Graph Q) (W : Tid → List Msg) (e : Ev Q) : Ev Q :=
  ⟨e.tid, G.cnt e.tid + (e.idx - (W e.tid).length), e.lab⟩

/-- The inverse of `emb`. -/
def unemb (G : Graph Q) (W : Tid → List Msg) (e : Ev Q) : Ev Q :=
  ⟨e.tid, e.idx - G.cnt e.tid + (W e.tid).length, e.lab⟩

/-- `ê` (def:mp-compose, def:p2p-compose): seeds by `ρ`, the other events by `emb`. -/
def ehat (G : Graph Q) (W : Tid → List Msg) (ρ : Ev Q → Ev Q) (x : Ev Q) : Ev Q :=
  if x.idx < (W x.tid).length then ρ x else G.emb W x

/-- `G ⊕ H` (def:mp-compose, def:p2p-compose). -/
def scomp (G H : Graph Q) (W : Tid → List Msg) (ρ : Ev Q → Ev Q) : Graph Q where
  events := G.events ∪ (H.events.filter fun e => (W e.tid).length ≤ e.idx).image (G.emb W)
  rf e := if e ∈ G.events then G.rf e
    else if G.cnt e.tid ≤ e.idx ∧ G.unemb W e ∈ H.events then
      (H.rf (G.unemb W e)).map (Src.map (G.ehat W ρ)) else none
  nd e := if e ∈ G.events then G.nd e
    else if G.cnt e.tid ≤ e.idx ∧ G.unemb W e ∈ H.events then H.nd (G.unemb W e) else none

variable {G H : Graph Q} {W : Tid → List Msg} {ρ : Ev Q → Ev Q}

omit [DecidableEq Q] in
@[simp] theorem emb_tid (e : Ev Q) : (G.emb W e).tid = e.tid := rfl
omit [DecidableEq Q] in
@[simp] theorem emb_idx (e : Ev Q) : (G.emb W e).idx = G.cnt e.tid + (e.idx - (W e.tid).length) :=
  rfl
omit [DecidableEq Q] in
@[simp] theorem emb_lab (e : Ev Q) : (G.emb W e).lab = e.lab := rfl

omit [DecidableEq Q] in
theorem unemb_emb {e : Ev Q} (h : (W e.tid).length ≤ e.idx) : G.unemb W (G.emb W e) = e := by
  rcases e with ⟨t, i, l⟩
  simp only [unemb, emb, Ev.mk.injEq, true_and, and_true] at h ⊢
  omega

omit [DecidableEq Q] in
theorem emb_unemb {e : Ev Q} (h : G.cnt e.tid ≤ e.idx) : G.emb W (G.unemb W e) = e := by
  rcases e with ⟨t, i, l⟩
  simp only [unemb, emb, Ev.mk.injEq, true_and, and_true] at h ⊢
  omega

omit [DecidableEq Q] in
theorem emb_inj {a b : Ev Q} (ha : (W a.tid).length ≤ a.idx) (hb : (W b.tid).length ≤ b.idx)
    (h : G.emb W a = G.emb W b) : a = b := by
  rw [← unemb_emb (G := G) ha, ← unemb_emb (G := G) hb, h]

omit [DecidableEq Q] in
theorem ehat_of_lt {x : Ev Q} (h : x.idx < (W x.tid).length) : G.ehat W ρ x = ρ x := by
  simp [ehat, h]

omit [DecidableEq Q] in
theorem ehat_of_ge {x : Ev Q} (h : (W x.tid).length ≤ x.idx) : G.ehat W ρ x = G.emb W x := by
  simp [ehat, Nat.not_lt.mpr h]

variable [Membership Val Q]

omit [DecidableEq Q] in
/-- An embedded event is not an event of `G`. -/
theorem Wf.emb_not_mem (hG : G.Wf) (e : Ev Q) : G.emb W e ∉ G.events := fun h => by
  have := hG.idx_lt_cnt h
  simp at this

omit [Membership Val Q] in
theorem mem_scomp {x : Ev Q} :
    x ∈ (G.scomp H W ρ).events ↔
      x ∈ G.events ∨ ∃ e ∈ H.events, (W e.tid).length ≤ e.idx ∧ x = G.emb W e := by
  simp only [scomp, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro (h | ⟨e, ⟨he, hi⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e, he, hi, rfl⟩
  · rintro (h | ⟨e, he, hi, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e, ⟨he, hi⟩, rfl⟩

omit [Membership Val Q] in
theorem scomp_rf_old {x : Ev Q} (hx : x ∈ G.events) : (G.scomp H W ρ).rf x = G.rf x := by
  simp [scomp, hx]

omit [Membership Val Q] in
theorem scomp_nd_old {x : Ev Q} (hx : x ∈ G.events) : (G.scomp H W ρ).nd x = G.nd x := by
  simp [scomp, hx]

theorem scomp_rf_emb (hG : G.Wf) {e : Ev Q} (he : e ∈ H.events)
    (hi : (W e.tid).length ≤ e.idx) :
    (G.scomp H W ρ).rf (G.emb W e) = (H.rf e).map (Src.map (G.ehat W ρ)) := by
  simp [scomp, hG.emb_not_mem, unemb_emb hi, he]

theorem scomp_nd_emb (hG : G.Wf) {e : Ev Q} (he : e ∈ H.events)
    (hi : (W e.tid).length ≤ e.idx) : (G.scomp H W ρ).nd (G.emb W e) = H.nd e := by
  simp [scomp, hG.emb_not_mem, unemb_emb hi, he]

omit [DecidableEq Q] in
/-- The events of thread `t` from index `k` on. -/
theorem Wf.card_filter_ge (hH : H.Wf) (t k : ℕ) :
    (H.events.filter fun e => e.tid = t ∧ k ≤ e.idx).card = H.cnt t - k := by
  classical
  have hinj : Set.InjOn Ev.idx
      (↑(H.events.filter fun e => e.tid = t ∧ k ≤ e.idx) : Set (Ev Q)) := by
    intro a ha b hb h
    have ha := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
    have hb := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
    exact hH.idx_inj a ha.1 b hb.1 (ha.2.1.trans hb.2.1.symm) h
  rw [← Finset.card_image_of_injOn hinj]
  have himg : (H.events.filter fun e => e.tid = t ∧ k ≤ e.idx).image Ev.idx =
      Finset.Ico k (H.cnt t) := by
    ext i
    rw [Finset.mem_image, Finset.mem_Ico, ← hH.exists_idx_iff t i]
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨he, ht, hk⟩ := Finset.mem_filter.mp he
      exact ⟨hk, e, he, ht, rfl⟩
    · rintro ⟨hk, e, he, ht, rfl⟩
      exact ⟨e, Finset.mem_filter.mpr ⟨he, ht, hk⟩, rfl⟩
  rw [himg, Nat.card_Ico]

end Graph

namespace Ind

variable {Q : Type} [DecidableEq Q] [Membership Val Q]

/-- `ρ` sends the seed events of `W` bijectively onto the unread sends of `G`, with their
labels; if `ord`, also with their thread and index order. -/
structure SeedOK (G : Graph Q) (m : Comm) (W : Tid → List Msg) (ρ : Ev Q → Ev Q)
    (ord : Prop) : Prop where
  /-- a seed goes to an unread send -/
  mem : ∀ t j, j < (W t).length → ρ (seedEv m W t j) ∈ G.US
  /-- with the label of the seed -/
  lab : ∀ t j, j < (W t).length → (ρ (seedEv m W t j)).lab = seedLab m W t j
  /-- injective on the seeds -/
  inj : ∀ t j t' j', j < (W t).length → j' < (W t').length →
    ρ (seedEv m W t j) = ρ (seedEv m W t' j') → t = t' ∧ j = j'
  /-- onto the unread sends -/
  surj : ∀ s ∈ G.US, ∃ t j, j < (W t).length ∧ ρ (seedEv m W t j) = s
  /-- if `ord`: the seed of `t` goes to a send of `t` -/
  tid : ord → ∀ t j, j < (W t).length → (ρ (seedEv m W t j)).tid = t
  /-- if `ord`: the index order of the seeds of `t` is kept -/
  mono : ord → ∀ t j j', j < (W t).length → j' < (W t).length →
    (j < j' ↔ (ρ (seedEv m W t j)).idx < (ρ (seedEv m W t j')).idx)

variable {G H H' : Graph Q} {W : Tid → List Msg} {ρ : Ev Q → Ev Q} {m : Comm} {ord : Prop}

/-- `ê` is injective on events that are seed events at their seed positions. -/
theorem SeedOK.ehat_inj (hG : G.Wf) (hρ : SeedOK G m W ρ ord) {s s' : Ev Q}
    (hs : s.idx < (W s.tid).length → s = seedEv m W s.tid s.idx)
    (hs' : s'.idx < (W s'.tid).length → s' = seedEv m W s'.tid s'.idx)
    (h : G.ehat W ρ s = G.ehat W ρ s') : s = s' := by
  have hmemG : ∀ x : Ev Q, x.idx < (W x.tid).length → x = seedEv m W x.tid x.idx →
      G.ehat W ρ x ∈ G.events := fun x hx hxe => by
    rw [Graph.ehat_of_lt hx, hxe]
    exact ((G.mem_US).mp (hρ.mem _ _ hx)).1
  rcases Nat.lt_or_ge s.idx (W s.tid).length with h1 | h1 <;>
    rcases Nat.lt_or_ge s'.idx (W s'.tid).length with h2 | h2
  · have e1 := hs h1
    have e2 := hs' h2
    rw [Graph.ehat_of_lt h1, Graph.ehat_of_lt h2, e1, e2] at h
    obtain ⟨ht, hj⟩ := hρ.inj _ _ _ _ h1 h2 h
    rw [e1, e2, ht, hj]
  · have := hmemG s h1 (hs h1)
    rw [h, Graph.ehat_of_ge h2] at this
    exact absurd this (hG.emb_not_mem _)
  · have := hmemG s' h2 (hs' h2)
    rw [← h, Graph.ehat_of_ge h1] at this
    exact absurd this (hG.emb_not_mem _)
  · rw [Graph.ehat_of_ge h1, Graph.ehat_of_ge h2] at h
    exact Graph.emb_inj h1 h2 h

/-- `G ⊕ Z_w = G` (lem:mp-compose (1), lem:p2p-compose (3), last part). Without `hG` false
(Astra C3): `G` with `rf e ≠ none` for some `e ∉ G.events`. -/
theorem scomp_seed (hG : G.Wf) {ts : List Tid} :
    G.scomp (seedGraph ts m W) W ρ = G := by
  have hnot : ∀ e ∈ (seedGraph ts m W : Graph Q).events, ¬ (W e.tid).length ≤ e.idx :=
    fun e he h => by have := (mem_seedGraph.mp he).2.1; omega
  have hc : ∀ x : Ev Q, ¬ (G.cnt x.tid ≤ x.idx ∧ G.unemb W x ∈ (seedGraph ts m W).events) := by
    rintro x ⟨h1, h2⟩
    exact hnot _ h2 (by simp [Graph.unemb])
  apply Graph.ext
  · ext x
    rw [Graph.mem_scomp]
    constructor
    · rintro (h | ⟨e, he, hi, -⟩)
      · exact h
      · exact absurd hi (hnot e he)
    · exact Or.inl
  · funext x
    by_cases hx : x ∈ G.events
    · exact Graph.scomp_rf_old hx
    · simp [Graph.scomp, hx, hc x, hG.rf_none (Or.inl hx)]
  · funext x
    by_cases hx : x ∈ G.events
    · exact Graph.scomp_nd_old hx
    · simp [Graph.scomp, hx, hc x, hG.nd_none (Or.inl hx)]

/-- Composition commutes with adding a non-seed event to the fragment. Without `hG` false
(Astra C3, Opus B2): `W = []`, `H` empty, `G` one ND event at index 1 of `t` (a gap), `e` at
index 0 with that label: `emb e` is the old event; `.add` overwrites `G.nd`. (The premises `hH`
and `hidx` of the plan are not needed.) -/
theorem scomp_add (hG : G.Wf) (_hH : H.Wf) {e : Ev Q} (_hidx : e.idx = H.cnt e.tid)
    (hs : (W e.tid).length ≤ e.idx) {src : Option (Src Q)} {out : Option Val} :
    G.scomp (H.add e src out) W ρ =
      (G.scomp H W ρ).add (G.emb W e) (src.map (Src.map (G.ehat W ρ))) out := by
  have hne : ∀ x, x ≠ G.emb W e → G.cnt x.tid ≤ x.idx → G.unemb W x ≠ e := fun x hx hc h =>
    hx (by rw [← h, Graph.emb_unemb hc])
  apply Graph.ext
  · ext x
    rw [Graph.mem_scomp]
    simp only [Graph.add_events]
    rw [Finset.mem_insert, Graph.mem_scomp]
    constructor
    · rintro (h | ⟨e', he', hi, rfl⟩)
      · exact Or.inr (Or.inl h)
      · rw [Finset.mem_insert] at he'
        rcases he' with rfl | he'
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ⟨e', he', hi, rfl⟩)
    · rintro (rfl | h | ⟨e', he', hi, rfl⟩)
      · exact Or.inr ⟨e, Finset.mem_insert_self _ _, hs, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨e', Finset.mem_insert_of_mem he', hi, rfl⟩
  · funext x
    by_cases hx : x = G.emb W e
    · subst hx
      rw [Graph.scomp_rf_emb hG (Finset.mem_insert_self _ _) hs, Graph.add_rf,
        Function.update_self, Graph.add_rf, Function.update_self]
    · rw [Graph.add_rf, Function.update_of_ne hx]
      by_cases hxG : x ∈ G.events
      · rw [Graph.scomp_rf_old hxG, Graph.scomp_rf_old hxG]
      · by_cases hc : G.cnt x.tid ≤ x.idx
        · simp [Graph.scomp, hxG, hc, hne x hx hc]
        · simp [Graph.scomp, hxG, hc]
  · funext x
    by_cases hx : x = G.emb W e
    · subst hx
      rw [Graph.scomp_nd_emb hG (Finset.mem_insert_self _ _) hs, Graph.add_nd,
        Function.update_self, Graph.add_nd, Function.update_self]
    · rw [Graph.add_nd, Function.update_of_ne hx]
      by_cases hxG : x ∈ G.events
      · rw [Graph.scomp_nd_old hxG, Graph.scomp_nd_old hxG]
      · by_cases hc : G.cnt x.tid ≤ x.idx
        · simp [Graph.scomp, hxG, hc, hne x hx hc]
        · simp [Graph.scomp, hxG, hc]

/-- The events of a thread in `G ⊕ H`. (The premise `hs` of the plan is not needed.) -/
theorem scomp_cnt (hG : G.Wf) (hH : H.Wf) (_hs : ∀ t, (W t).length ≤ H.cnt t) (t : Tid) :
    (G.scomp H W ρ).cnt t = G.cnt t + (H.cnt t - (W t).length) := by
  unfold Graph.cnt
  change ((G.events ∪ (H.events.filter fun e => (W e.tid).length ≤ e.idx).image (G.emb W)).filter
    fun e => e.tid = t).card = _
  rw [Finset.filter_union, Finset.card_union_of_disjoint, Finset.filter_image,
    Finset.card_image_of_injOn, Finset.filter_filter]
  · congr 1
    have hk := hH.card_filter_ge t (W t).length
    unfold Graph.cnt at hk
    rw [← hk]
    congr 1
    refine Finset.filter_congr fun e _ => ?_
    simp only [Graph.emb_tid]
    constructor
    · rintro ⟨h1, rfl⟩
      exact ⟨rfl, h1⟩
    · rintro ⟨rfl, h1⟩
      exact ⟨h1, rfl⟩
  · intro a ha b hb h
    have ha := (Finset.mem_filter.mp (Finset.mem_coe.mp ha))
    have hb := (Finset.mem_filter.mp (Finset.mem_coe.mp hb))
    exact Graph.emb_inj (Finset.mem_filter.mp ha.1).2 (Finset.mem_filter.mp hb.1).2 h
  · rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨hx', -⟩ := Finset.mem_filter.mp hx'
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hx'
    exact hG.emb_not_mem e (Finset.mem_filter.mp hx).1

/-- The events of `A` reappear in `B` if the compositions agree (one direction of
`scomp_injective`). -/
theorem mem_of_scomp_eq (hG : G.Wf) {A B : Graph Q}
    (hseedB : ∀ t j, j < (W t).length → seedEv m W t j ∈ B.events)
    (hlabA : ∀ t j, j < (W t).length → ∀ e ∈ A.events, e.tid = t → e.idx = j →
      e = seedEv m W t j)
    (heq : G.scomp A W ρ = G.scomp B W ρ) {e : Ev Q} (he : e ∈ A.events) : e ∈ B.events := by
  rcases Nat.lt_or_ge e.idx (W e.tid).length with hi | hi
  · rw [hlabA _ _ hi e he rfl rfl]
    exact hseedB _ _ hi
  · have hm : G.emb W e ∈ (G.scomp A W ρ).events :=
      Graph.mem_scomp.mpr (Or.inr ⟨e, he, hi, rfl⟩)
    rw [heq, Graph.mem_scomp] at hm
    rcases hm with hm | ⟨e', he', hi', h⟩
    · exact absurd hm (hG.emb_not_mem e)
    · rw [Graph.emb_inj hi hi' h]
      exact he'

/-- The composition determines the fragment (stated for well-formed fragments; C4a restates it
for `Frag`). (The premises `hs`, `hs'` of the plan are not needed.) -/
theorem scomp_injective (hG : G.Wf) (hH : H.Wf) (hH' : H'.Wf)
    (_hs : ∀ t, (W t).length ≤ H.cnt t) (_hs' : ∀ t, (W t).length ≤ H'.cnt t)
    (hseed : ∀ t j, j < (W t).length → seedEv m W t j ∈ H.events ∧ seedEv m W t j ∈ H'.events)
    (hρ : SeedOK G m W ρ ord)
    (hlab : ∀ t j, j < (W t).length → ∀ e ∈ H.events ∪ H'.events, e.tid = t → e.idx = j →
      e = seedEv m W t j) :
    G.scomp H W ρ = G.scomp H' W ρ → H = H' := by
  intro heq
  have hlabH := fun t j hj e he => hlab t j hj e (Finset.mem_union_left _ he)
  have hlabH' := fun t j hj e he => hlab t j hj e (Finset.mem_union_right _ he)
  have hev : ∀ e, e ∈ H.events ↔ e ∈ H'.events := fun e =>
    ⟨mem_of_scomp_eq hG (fun t j hj => (hseed t j hj).2) hlabH heq,
      mem_of_scomp_eq hG (fun t j hj => (hseed t j hj).1) hlabH' heq.symm⟩
  have hsend : ∀ e ∈ H.events, e.idx < (W e.tid).length → ¬ e.IsRecv ∧ ¬ e.IsND := by
    intro e he hi
    have hS : e.IsSend := by rw [hlabH _ _ hi e he rfl rfl]; exact seedLab_isSend hi
    exact ⟨Lab.IsSend.not_isRecv hS, Lab.IsSend.not_isND hS⟩
  -- a source of a fragment is a seed event at a seed position
  have hsrc : ∀ (A : Graph Q), A.Wf → (∀ t j, j < (W t).length → ∀ e ∈ A.events, e.tid = t →
      e.idx = j → e = seedEv m W t j) → ∀ r s, A.rf r = some (.snd s) →
      (s.idx < (W s.tid).length → s = seedEv m W s.tid s.idx) :=
    fun A hA hl r s h hi => hl _ _ hi s (hA.rf_mem r s h) rfl rfl
  refine hH.ext hH' (Finset.ext hev) (fun e he => ?_) (fun e he => ?_)
  · rcases Nat.lt_or_ge e.idx (W e.tid).length with hi | hi
    · rw [hH.rf_none (Or.inr (hsend e he hi).1),
        hH'.rf_none (Or.inr ((hsend e he hi).1))]
    · have h := congrArg (fun K : Graph Q => K.rf (G.emb W e)) heq
      rw [Graph.scomp_rf_emb hG he hi, Graph.scomp_rf_emb hG ((hev e).mp he) hi] at h
      have hx := hsrc H hH hlabH e
      have hy := hsrc H' hH' hlabH' e
      generalize H.rf e = a at h hx ⊢
      generalize H'.rf e = b at h hy ⊢
      rcases a with _ | (_ | s) <;> rcases b with _ | (_ | s') <;>
        simp only [Option.map_none, Option.map_some, Src.map, reduceCtorEq, Option.some.injEq,
          Src.snd.injEq] at h ⊢
      exact hρ.ehat_inj hG (hx s rfl) (hy s' rfl) h
  · rcases Nat.lt_or_ge e.idx (W e.tid).length with hi | hi
    · rw [hH.nd_none (Or.inr (hsend e he hi).2), hH'.nd_none (Or.inr ((hsend e he hi).2))]
    · have h := congrArg (fun K : Graph Q => K.nd (G.emb W e)) heq
      rwa [Graph.scomp_nd_emb hG he hi, Graph.scomp_nd_emb hG ((hev e).mp he) hi] at h

end Ind

end Must
