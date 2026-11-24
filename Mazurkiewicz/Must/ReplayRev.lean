import Mazurkiewicz.Must.Replay

/-!
# The replay base of a revisit and the revisit condition as a replay (milestone M5)

Paper: Section 4, `RevisitCondition` and p. 19 ("the revisit will only take place from one of
these graphs"). Plan: decisions Q10 (i), Q15, Section 2b ("Canonical replay base of a revisit"),
fate row "Section 4, p. 19" (R: `RevisitCondition` ⇔ canonical replay of the supplied list).

Setting: a configuration `H` with `Config.Inv`, a send `s` of `H` that is unread and last in the
insertion order (`H = c.add s` for a step of Algorithm 1), and a receive `r` of `H` with
`¬ (r, s) ∈ H.porf`. `Deleted = H.del r s` (Q15).

* `Config.base H r s` = `K := H.E \ (Deleted ∪ {r, s})`; `Config.delList H r s`: `Deleted` in
  insertion order.
* `base_closed`: `K` is `porf`-closed in `H` (hence closed under sources), given
  `RevisitCondition` of the deleted sends (line 21). This is closure of `K`, not of
  `H \ Deleted` (`AlgInv.lean`), which keeps `r` and `s`. `base_cons`, `base_exec`: the graph on
  `K` is a consistent execution of `P`.
* `replay_restrict_iff` (every graph): replaying a list `l` from the restriction of a
  well-formed execution `F` to a set `E` reproduces `F` on `E ∪ l` iff every listed event has
  its source and outcome of `F` as canonical choice at its turn (`CanonList`), provided `l`
  respects `po` and `E ∪ l` contains the thread predecessors of every listed event.
* `revCond_iff_replay`: `RevisitCondition(H, e, s)` for every `e ∈ Deleted ∪ {r}` iff `K` is
  `porf`-closed and the canonical replay from the graph on `K` of `r` followed by `Deleted` in
  insertion order reproduces `H \ {s}`. The closure conjunct is necessary: `ReplayEx.lean`
  (`replay_without_closure`) has a reachable revisit attempt where the replay reproduces
  `H \ {s}` but `RevisitCondition` of a deleted send fails (a kept receive reads it).
* `revCond_iff_replay_step`: the same for the revisit of Algorithm 1 (`H = c.add s`), where
  `H \ {s}` is the configuration before the send.

Every result holds for every model `M` and every tie-break with `TieQ9 M tie`.
-/

namespace Must

open Graph Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q]
variable {M : Model Q} {P : Program Q} {tie : Tie Q}

/-! ### Restriction and addition -/

namespace Graph

omit [Membership Val Q] in
/-- Adding an event of `F` with its source and outcome to a restriction of `F`. -/
theorem restrict_add_self {F : Graph Q} {E : Finset (Ev Q)} {e : Ev Q} (he : e ∈ F.events) :
    (F.restrict E).add e (F.rf e) (F.nd e) = F.restrict (insert e E) := by
  apply Graph.ext
  · ext x
    simp only [add_events, restrict_events, Finset.mem_insert, Finset.mem_inter]
    constructor
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨he, Or.inl rfl⟩
      · exact ⟨h1, Or.inr h2⟩
    · rintro ⟨h1, rfl | h2⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨h1, h2⟩
  · funext x
    by_cases hx : x = e
    · subst hx
      simp
    · simp [hx]
  · funext x
    by_cases hx : x = e
    · subst hx
      simp
    · simp [hx]

end Graph

/-! ### Restrictions of executions -/

omit [Membership Val Q] in
/-- The restriction of an execution of `P` to a set closed under `po`-predecessors is an
execution of `P`. -/
theorem Program.exec_restrict {F : Graph Q} (hE : P.Exec F) {E : Finset (Ev Q)}
    (hpo : ∀ a b, F.po a b → b ∈ E → a ∈ E) : P.Exec (F.restrict E) := by
  refine P.exec_of_agree hE fun x hx => ?_
  obtain ⟨hxF, hxE⟩ := Finset.mem_inter.mp hx
  refine ⟨hxF, fun y h1 h2 => ⟨?_, fun hy => ?_⟩⟩
  · rw [restrict_events, Finset.mem_inter]
    exact ⟨fun hy => ⟨hy, hpo y x ⟨hy, hxF, h1, h2⟩ hxE⟩, fun h => h.1⟩
  · have hyE := hpo y x ⟨hy, hxF, h1, h2⟩ hxE
    simp [hyE]

omit [DecidableEq Q] in
/-- The events of a thread of a well-formed graph below a given index of an event of the thread
are as many as that index. -/
theorem Graph.Wf.card_below {F : Graph Q} (hF : F.Wf) {e : Ev Q} (he : e ∈ F.events) :
    (F.events.filter (fun x => x.tid = e.tid ∧ x.idx < e.idx)).card = e.idx := by
  have hinj : Set.InjOn Ev.idx
      (↑(F.events.filter (fun x => x.tid = e.tid ∧ x.idx < e.idx)) : Set (Ev Q)) := by
    intro x hx y hy hxy
    rw [Finset.coe_filter] at hx hy
    exact hF.idx_inj x hx.1 y hy.1 (hx.2.1.trans hy.2.1.symm) hxy
  have him : (F.events.filter (fun x => x.tid = e.tid ∧ x.idx < e.idx)).image Ev.idx =
      Finset.range e.idx := by
    ext j
    rw [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (Finset.mem_filter.mp hx).2.2
    · intro hj
      obtain ⟨y, hy, hyt, hyi⟩ := hF.idx_contig e he j hj
      exact ⟨y, Finset.mem_filter.mpr ⟨hy, hyt, hyi ▸ hj⟩, hyi⟩
  rw [← Finset.card_image_of_injOn hinj, him, Finset.card_range]

/-- An event of a well-formed execution `F` whose thread predecessors are in `E` and whose
thread successors are not is the next event of its thread in the restriction of `F` to `E`. -/
theorem nextEv_restrict {F : Graph Q} (hF : F.Wf) (hE : P.Exec F) {E : Finset (Ev Q)}
    {e : Ev Q} (he : e ∈ F.events) (heE : e ∉ E) (hpre : ∀ a, F.po a e → a ∈ E)
    (hsuc : ∀ b ∈ E, ¬ F.po e b) : P.nextEv (F.restrict E) e.tid = some e := by
  have hmem : ∀ x, x.tid = e.tid → (x ∈ F.events ∩ E ↔ x ∈ F.events ∧ x.idx < e.idx) := by
    intro x hxt
    rw [Finset.mem_inter]
    constructor
    · rintro ⟨hx, hxE⟩
      refine ⟨hx, ?_⟩
      rcases lt_trichotomy x.idx e.idx with h | h | h
      · exact h
      · exact absurd (hF.idx_inj x hx e he hxt h ▸ hxE) heE
      · exact absurd ⟨he, hx, hxt.symm, h⟩ (hsuc x hxE)
    · rintro ⟨hx, hlt⟩
      exact ⟨hx, hpre x ⟨hx, he, hxt, hlt⟩⟩
  have hcnt : (F.restrict E).cnt e.tid = e.idx := by
    rw [← hF.card_below he]
    unfold Graph.cnt
    congr 1
    ext x
    simp only [Finset.mem_filter, restrict_events]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨((hmem x h2).mp h1).1, h2, ((hmem x h2).mp h1).2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(hmem x h2).mpr ⟨h1, h3⟩, h2⟩
  have htr : (F.restrict E).trace e.tid = F.traceBefore e.tid e.idx := by
    unfold trace
    rw [hcnt]
    refine traceBefore_congr fun j hj => retAt_congr (fun y h1 h2 => ?_) (fun y hy h1 h2 => ?_)
    · rw [restrict_events, hmem y h1, h2]
      exact ⟨fun h => h.1, fun h => ⟨h, hj⟩⟩
    · have hyE := (Finset.mem_inter.mp hy).2
      simp [hyE]
  unfold Program.nextEv
  rw [htr, hE e he, hcnt]
  rfl

/-! ### Replay from a restriction -/

/-- Every listed event has its source and outcome of `F` as canonical choice at its turn: in the
restriction of `F` to `E` and the events listed before it. -/
def CanonList (tie : Tie Q) (F : Graph Q) : Finset (Ev Q) → List (Ev Q) → Prop
  | _, [] => True
  | E, e :: l => Canon tie (F.restrict E) e (F.rf e) (F.nd e) ∧ CanonList tie F (insert e E) l

/-- The events listed before `e` in `l`. -/
def before (l : List (Ev Q)) (e : Ev Q) : Finset (Ev Q) :=
  (l.takeWhile (fun x => decide (x ≠ e))).toFinset

omit [Membership Val Q] in
/-- A canonical replay leaves the source and outcome of an event not in the list unchanged. -/
theorem Replay.rf_nd_of_not_mem {G G' : Graph Q} {l : List (Ev Q)} (h : Replay tie P G l G')
    {x : Ev Q} (hx : x ∉ l) : G'.rf x = G.rf x ∧ G'.nd x = G.nd x := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | @cons G G₁ G' e l hs _ ih =>
    obtain ⟨-, src, out, -, rfl⟩ := hs
    have hxe : x ≠ e := fun h => hx (h ▸ List.mem_cons_self)
    obtain ⟨h1, h2⟩ := ih (fun h => hx (List.mem_cons_of_mem _ h))
    rw [h1, h2]
    simp [Function.update_of_ne hxe]

/-- Replay from a restriction (every model, every tie-break): for a well-formed execution `F`, a
set `E` and a duplicate-free list `l` of events of `F` outside `E` that respects `po`, such that
`E ∪ l` contains the thread predecessors of every listed event and no listed event is a thread
predecessor of an event of `E`, the canonical replay of `l` from `F|E` reproduces `F|(E ∪ l)` iff
`CanonList tie F E l`. -/
theorem replay_restrict_iff {F : Graph Q} (hF : F.Wf) (hE : P.Exec F) :
    ∀ (l : List (Ev Q)) (E : Finset (Ev Q)), l.Nodup → (∀ e ∈ l, e ∈ F.events ∧ e ∉ E) →
      l.Pairwise (fun a b => ¬ F.po b a) → (∀ e ∈ l, ∀ a, F.po a e → a ∈ E ∨ a ∈ l) →
      (∀ b ∈ E, ∀ a ∈ l, ¬ F.po a b) →
      (Replay tie P (F.restrict E) l (F.restrict (E ∪ l.toFinset)) ↔ CanonList tie F E l)
  | [], E, _, _, _, _, _ => by
    simp only [List.toFinset_nil, Finset.union_empty, CanonList, iff_true]
    exact .nil _
  | e :: l, E, hnd, hmem, hpw, hpre, hsuc => by
    obtain ⟨heF, heE⟩ := hmem e List.mem_cons_self
    have hel : e ∉ l := (List.nodup_cons.mp hnd).1
    have hset : E ∪ (e :: l).toFinset = insert e E ∪ l.toFinset := by
      ext x
      simp only [Finset.mem_union, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset]
      tauto
    have ih := replay_restrict_iff hF hE l (insert e E) (List.nodup_cons.mp hnd).2
      (fun x hx => ⟨(hmem x (List.mem_cons_of_mem _ hx)).1, by
        rw [Finset.mem_insert, not_or]
        exact ⟨fun h => hel (h ▸ hx), (hmem x (List.mem_cons_of_mem _ hx)).2⟩⟩)
      (List.pairwise_cons.mp hpw).2
      (fun x hx a ha => by
        rcases hpre x (List.mem_cons_of_mem _ hx) a ha with h | h
        · exact Or.inl (Finset.mem_insert_of_mem h)
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inl (Finset.mem_insert_self _ _)
          · exact Or.inr h)
      (fun b hb a ha hab => by
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact (List.pairwise_cons.mp hpw).1 a ha hab
        · exact hsuc b hb a (List.mem_cons_of_mem _ ha) hab)
    have hpre' : ∀ a, F.po a e → a ∈ E := by
      intro a ha
      rcases hpre e List.mem_cons_self a ha with h | h
      · exact h
      · rcases List.mem_cons.mp h with rfl | h
        · exact absurd ha.2.2.2 (lt_irrefl _)
        · exact absurd ha ((List.pairwise_cons.mp hpw).1 a h)
    have hn : P.nextEv (F.restrict E) e.tid = some e :=
      nextEv_restrict hF hE heF heE hpre' (fun b hb => hsuc b hb e List.mem_cons_self)
    rw [hset, CanonList, ← ih]
    constructor
    · intro h
      cases h with
      | cons hs hr =>
        obtain ⟨-, src, out, hc, rfl⟩ := hs
        obtain ⟨h1, h2⟩ := hr.rf_nd_of_not_mem hel
        have he1 : F.rf e = src := by
          have : (F.restrict (insert e E ∪ l.toFinset)).rf e = F.rf e := by simp
          rw [← this, h1]
          simp
        have he2 : F.nd e = out := by
          have : (F.restrict (insert e E ∪ l.toFinset)).nd e = F.nd e := by simp
          rw [← this, h2]
          simp
        subst he1 he2
        rw [Graph.restrict_add_self heF] at hr
        exact ⟨hc, hr⟩
    · rintro ⟨hc, hr⟩
      refine .cons ⟨hn, F.rf e, F.nd e, hc, (Graph.restrict_add_self heF).symm⟩ hr

omit [Membership Val Q] in
theorem before_cons_self (l : List (Ev Q)) (e : Ev Q) : before (e :: l) e = ∅ := by
  simp [before]

omit [Membership Val Q] in
theorem before_cons_of_ne {l : List (Ev Q)} {a e : Ev Q} (h : a ≠ e) :
    before (a :: l) e = insert a (before l e) := by
  unfold before
  rw [List.takeWhile_cons_of_pos (by simpa using h), List.toFinset_cons]

omit [Membership Val Q] in
/-- `CanonList` as a condition on each listed event, with the events listed before it. -/
theorem canonList_iff {F : Graph Q} :
    ∀ (l : List (Ev Q)) (E : Finset (Ev Q)), l.Nodup →
      (CanonList tie F E l ↔
        ∀ e ∈ l, Canon tie (F.restrict (E ∪ before l e)) e (F.rf e) (F.nd e))
  | [], E, _ => by simp [CanonList]
  | a :: l, E, hnd => by
    have hal : a ∉ l := (List.nodup_cons.mp hnd).1
    rw [CanonList, canonList_iff l (insert a E) (List.nodup_cons.mp hnd).2, List.forall_mem_cons,
      before_cons_self, Finset.union_empty]
    refine and_congr Iff.rfl (forall₂_congr fun x hx => ?_)
    have hax : a ≠ x := fun h => hal (h ▸ hx)
    rw [before_cons_of_ne hax, Finset.union_insert, Finset.insert_union]

omit [Membership Val Q] in
/-- The elements before `d` in a filtered list are the elements of the filter with a smaller
index in the original list. -/
theorem mem_before_filter (p : Ev Q → Bool) :
    ∀ (L : List (Ev Q)) {d x : Ev Q}, d ∈ L → p d = true →
      (x ∈ before (L.filter p) d ↔ x ∈ L ∧ p x = true ∧ L.idxOf x < L.idxOf d)
  | [], _, _, h, _ => absurd h List.not_mem_nil
  | a :: L, d, x, hd, hpd => by
    by_cases had : a = d
    · subst had
      simp [List.filter_cons_of_pos hpd, before_cons_self]
    · have hdL : d ∈ L := (List.mem_cons.mp hd).resolve_left (Ne.symm had)
      have ih := mem_before_filter p L (x := x) hdL hpd
      rw [List.idxOf_cons_ne L had]
      by_cases hpa : p a = true
      · rw [List.filter_cons_of_pos hpa, before_cons_of_ne had, Finset.mem_insert, ih]
        by_cases hxa : x = a
        · subst hxa
          simp [hpa]
        · rw [List.idxOf_cons_ne L (Ne.symm hxa)]
          simp [hxa]
      · rw [List.filter_cons_of_neg hpa, ih]
        by_cases hxa : x = a
        · subst hxa
          simp [hpa]
        · rw [List.idxOf_cons_ne L (Ne.symm hxa)]
          simp [hxa]

/-! ### The replay base of a revisit -/

namespace Config

/-- The replay base of the revisit of `r` by `s` (Section 2b): `K := H.E \ (Deleted ∪ {r, s})`. -/
def base (H : Config Q) (r s : Ev Q) : Finset (Ev Q) :=
  H.G.events \ insert r (insert s (H.del r s))

/-- `Deleted` in insertion order. -/
def delList (H : Config Q) (r s : Ev Q) : List (Ev Q) :=
  H.order.filter (fun d => decide (d ∈ H.del r s))

variable {H : Config Q} {r s : Ev Q}

omit [Membership Val Q] in
theorem mem_base {x : Ev Q} :
    x ∈ H.base r s ↔ x ∈ H.G.events ∧ x ≠ r ∧ x ≠ s ∧ x ∉ H.del r s := by
  unfold base
  simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]

/-- The source of a kept receive other than `r` is not deleted, from `RevisitCondition` of the
deleted sends (line 21); `del_src` (`AlgInv.lean`) with only the guards it uses. -/
theorem del_src' (hH : H.Inv M P) (hsS : s.IsSend)
    (hsend : ∀ d ∈ H.del r s, d.IsSend → RevCond tie H d s) {q s' : Ev Q}
    (hq : q ∈ H.G.events) (hqd : q ∉ H.del r s) (hqr : q ≠ r) (hrf : H.G.rf q = some (.snd s')) :
    s' ∉ H.del r s := by
  intro hs'
  have hs'send : s'.IsSend := (hH.wf.rf_match _ _ hrf).isSend
  have hqR : q.IsRecv := (hH.wf.rf_some hrf).2
  have hqs : q ≠ s := by
    rintro rfl
    exact Lab.IsSend.not_isRecv hsS hqR
  have hd' := mem_del.mp hs'
  have hprev : q ∈ H.prev s' s := by
    unfold prev
    rw [Finset.mem_filter]
    refine ⟨hq, ?_⟩
    by_cases hp : H.G.porf q s
    · exact Or.inr hp
    · left
      have hnot : ¬ H.pos r < H.pos q := fun h => hqd (mem_del.mpr ⟨hq, hqs, h, hp⟩)
      have hne : H.pos q ≠ H.pos r := fun h => hqr ((pos_inj ((hH.mem q).mpr hq)).mp h)
      have := hd'.2.2.1
      omega
  exact RevCond.of_send (hsend s' hs' hs'send) hs'send q hprev hqR hrf

/-- Item 2 of M5: the replay base `K` is `porf`-closed in `H` (so it contains the sources of its
receives), for an unread `po`-maximal send `s`, a receive `r` not causally before `s`, and
`RevisitCondition` of the deleted sends. -/
theorem base_closed (hH : H.Inv M P) (hsS : s.IsSend) (hread : ∀ r', H.G.rf r' ≠ some (.snd s))
    (hmax : ∀ a, ¬ H.G.po s a) (hR : r.IsRecv) (hnp : ¬ H.G.porf r s)
    (hsend : ∀ d ∈ H.del r s, d.IsSend → RevCond tie H d s) : H.G.Closed (H.base r s) := by
  intro a b hab hb
  have hb := Finset.mem_coe.mp hb
  obtain ⟨hbH, hbK⟩ := Finset.mem_inter.mp hb
  obtain ⟨-, hbr, hbs, hbd⟩ := mem_base.mp hbK
  have haH := (hH.wf.mem_of_porfStep hab).1
  refine Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨haH, mem_base.mpr ⟨haH, ?_, ?_, ?_⟩⟩)
  · rintro rfl
    rcases hab with hpo | ⟨-, hrf⟩
    · exact hbd (po_del hH hnp hpo)
    · exact Lab.IsSend.not_isRecv (hH.wf.rf_match _ _ hrf).isSend hR
  · rintro rfl
    rcases hab with hpo | ⟨-, hrf⟩
    · exact hmax b hpo
    · exact hread b hrf
  · rcases hab with hpo | ⟨-, hrf⟩
    · exact del_po hH hpo hbd
    · exact del_src' hH hsS hsend hbH hbd hbr hrf

/-- The graph on `K` is consistent. -/
theorem base_cons (hH : H.Inv M P) (hK : H.G.Closed (H.base r s)) :
    M.cons (H.G.restrict (H.base r s)) :=
  M.prefixClosed _ _ hH.cons hK

/-- The graph on `K` is an execution of `P`. -/
theorem base_exec (hH : H.Inv M P) (hK : H.G.Closed (H.base r s)) :
    P.Exec (H.G.restrict (H.base r s)) := by
  refine P.exec_restrict hH.exec fun a b hab hb => ?_
  have := Finset.mem_coe.mp (hK (Or.inl hab) (Finset.mem_coe.mpr
    (Finset.mem_inter.mpr ⟨hab.2.1, hb⟩)))
  exact (Finset.mem_inter.mp this).2

omit [Membership Val Q] in
/-- The revisit successor and `H` agree on `K`: the successor's events are `K ∪ {r, s}`. -/
theorem revisitCfg_restrict_base :
    (H.revisitCfg r s).G.restrict (H.base r s) = H.G.restrict (H.base r s) := by
  apply Graph.ext
  · ext x
    simp only [revisitCfg, Graph.revisit, restrict_events, setRF_events, Finset.mem_inter,
      Finset.mem_sdiff, mem_base]
    tauto
  · funext x
    by_cases hx : x ∈ H.base r s
    · have hxr : x ≠ r := (mem_base.mp hx).2.1
      have hxd : x ∈ H.G.events \ H.del r s :=
        Finset.mem_sdiff.mpr ⟨(mem_base.mp hx).1, (mem_base.mp hx).2.2.2⟩
      simp [revisitCfg, Graph.revisit, hx, hxd, Function.update_of_ne hxr]
    · simp [hx]
  · funext x
    by_cases hx : x ∈ H.base r s
    · have hxd : x ∈ H.G.events \ H.del r s :=
        Finset.mem_sdiff.mpr ⟨(mem_base.mp hx).1, (mem_base.mp hx).2.2.2⟩
      simp [revisitCfg, Graph.revisit, hx, hxd]
    · simp [hx]

omit [Membership Val Q] in
theorem mem_revisitCfg_iff_base {x : Ev Q} (hs : s ∈ H.G.events) (hr : r ∈ H.G.events)
    (hrd : r ∉ H.del r s) :
    x ∈ (H.revisitCfg r s).G.events ↔ x ∈ H.base r s ∨ x = r ∨ x = s := by
  rw [mem_revisitCfg_events, mem_base]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hxr : x = r
    · exact Or.inr (Or.inl hxr)
    · by_cases hxs : x = s
      · exact Or.inr (Or.inr hxs)
      · exact Or.inl ⟨h1, hxr, hxs, h2⟩
  · rintro (⟨h1, -, -, h2⟩ | rfl | rfl)
    · exact ⟨h1, h2⟩
    · exact ⟨hr, hrd⟩
    · exact ⟨hs, fun h => (mem_del.mp h).2.1 rfl⟩

/-! ### The revisit condition as a replay -/

omit [Membership Val Q] in
theorem mem_prev {e x : Ev Q} :
    x ∈ H.prev e s ↔ x ∈ H.G.events ∧ (H.pos x ≤ H.pos e ∨ H.G.porf x s) := by
  unfold prev
  rw [Finset.mem_filter]

omit [Membership Val Q] in
/-- The events of the oracle context `(H|Previous) \ {e}` of `RevisitCondition`. -/
theorem mem_ctx {e x : Ev Q} :
    x ∈ ((H.G.restrict (H.prev e s)).remove {e}).events ↔ x ∈ H.prev e s ∧ x ≠ e := by
  simp only [Graph.remove, restrict_events, Finset.mem_inter, Finset.mem_sdiff,
    Finset.mem_singleton, mem_prev]
  tauto

/-- At the turn of `e ∈ Deleted ∪ {r}` the replay has added the base `K` and the events listed
before `e`: on the events of `H` this is `Previous(e) \ {e}`. -/
theorem base_before_iff (hH : H.Inv M P) (hlast : ∀ x ∈ H.G.events, x ≠ s → H.pos x < H.pos s)
    (hrs : r ≠ s) (hr : r ∈ H.G.events) {e : Ev Q} (he : e ∈ insert r (H.del r s)) {x : Ev Q}
    (hx : x ∈ H.G.events) :
    x ∈ H.base r s ∪ before (r :: H.delList r s) e ↔ x ∈ H.prev e s ∧ x ≠ e := by
  have hirr := hH.wf.porf_irrefl
  rw [Finset.mem_union, mem_base, mem_prev]
  by_cases her : e = r
  · subst her
    rw [before_cons_self]
    simp only [Finset.notMem_empty, or_false]
    have hlr := hlast e hr hrs
    constructor
    · rintro ⟨-, hxr, hxs, hxd⟩
      refine ⟨⟨hx, ?_⟩, hxr⟩
      by_cases hp : H.G.porf x s
      · exact Or.inr hp
      · exact Or.inl (not_lt.mp fun h => hxd (mem_del.mpr ⟨hx, hxs, h, hp⟩))
    · rintro ⟨⟨-, hp⟩, hxr⟩
      refine ⟨hx, hxr, ?_, fun hd => ?_⟩
      · rintro rfl
        rcases hp with h | h
        · omega
        · exact hirr _ h
      · obtain ⟨-, -, h1, h2⟩ := mem_del.mp hd
        rcases hp with h | h
        · omega
        · exact h2 h
  · have hed : e ∈ H.del r s := (Finset.mem_insert.mp he).resolve_left her
    obtain ⟨heH, hes, hre, hns⟩ := mem_del.mp hed
    have hle := hlast e heH hes
    rw [before_cons_of_ne (Ne.symm her), Finset.mem_insert, delList,
      mem_before_filter (fun d => decide (d ∈ H.del r s)) H.order ((hH.mem e).mpr heH)
        (by simpa using hed)]
    simp only [decide_eq_true_eq]
    have hpos : ∀ y, H.pos y = H.order.idxOf y := fun _ => rfl
    constructor
    · rintro (⟨-, hxr, hxs, hxd⟩ | rfl | ⟨-, hxd, hlt⟩)
      · refine ⟨⟨hx, ?_⟩, fun h => hxd (h ▸ hed)⟩
        by_cases hp : H.G.porf x s
        · exact Or.inr hp
        · have := not_lt.mp fun h => hxd (mem_del.mpr ⟨hx, hxs, h, hp⟩)
          exact Or.inl (by omega)
      · exact ⟨⟨hx, Or.inl (by omega)⟩, fun h => her h.symm⟩
      · refine ⟨⟨hx, Or.inl (by rw [hpos, hpos]; omega)⟩, ?_⟩
        rintro rfl
        exact lt_irrefl _ hlt
    · rintro ⟨⟨-, hp⟩, hxe⟩
      by_cases hxr : x = r
      · exact Or.inr (Or.inl hxr)
      by_cases hxs : x = s
      · subst hxs
        rcases hp with h | h
        · omega
        · exact absurd h (hirr _)
      by_cases hxd : x ∈ H.del r s
      · obtain ⟨-, -, -, hxn⟩ := mem_del.mp hxd
        have hle' : H.pos x ≤ H.pos e := hp.resolve_right hxn
        have hne : H.pos x ≠ H.pos e := fun h =>
          hxe ((pos_inj ((hH.mem x).mpr hx)).mp h)
        refine Or.inr (Or.inr ⟨(hH.mem x).mpr hx, hxd, ?_⟩)
        rw [← hpos, ← hpos]
        omega
      · exact Or.inl ⟨hx, hxr, hxs, hxd⟩

omit [Membership Val Q] in
theorem revCond_recvB {e : Ev Q} (hB : e.IsRecvB) :
    RevCond tie H e s ↔ ∃ s', H.G.rf e = some (.snd s') ∧
      tie ((H.G.restrict (H.prev e s)).remove {e}) e = some (s'.tid, s'.idx) := by
  have h1 : ¬ e.IsRecvNB := fun h => Lab.not_isRecvB_of_isRecvNB h hB
  have h2 : ¬ e.IsND := fun h => Lab.IsND.not_isRecv h (Lab.IsRecvB.isRecv hB)
  unfold RevCond
  simp only [h1, h2, hB, ↓reduceIte]

omit [Membership Val Q] in
theorem revCond_recvNB {e : Ev Q} (hNB : e.IsRecvNB) :
    RevCond tie H e s ↔ H.G.rf e = some .bot := by
  unfold RevCond
  simp only [hNB, ↓reduceIte]

omit [Membership Val Q] in
theorem revCond_nd {e : Ev Q} (hN : e.IsND) :
    RevCond tie H e s ↔ H.G.nd e = minVal e.ndSet := by
  have h1 : ¬ e.IsRecvNB := fun h => Lab.IsND.not_isRecv hN (Lab.IsRecvNB.isRecv h)
  unfold RevCond
  simp only [h1, hN, ↓reduceIte]

omit [Membership Val Q] in
theorem revCond_other {e : Ev Q} (hR : ¬ e.IsRecv) (hN : ¬ e.IsND) :
    RevCond tie H e s ↔ ∀ q ∈ H.prev e s, q.IsRecv → H.G.rf q ≠ some (.snd e) := by
  have h1 : ¬ e.IsRecvNB := fun h => hR (Lab.IsRecvNB.isRecv h)
  have h3 : ¬ e.IsRecvB := fun h => hR (Lab.IsRecvB.isRecv h)
  unfold RevCond
  simp only [h1, hN, h3, ↓reduceIte]

/-- For a receive or an ND event of `H`, the canonical choice in the oracle context is its
source and outcome iff `RevisitCondition` holds (Q9 for the blocking case). -/
theorem canon_iff_revCond (hT : TieQ9 M tie) (hH : H.Inv M P) {e : Ev Q}
    (he : e ∈ H.G.events) (hRN : e.IsRecv ∨ e.IsND) :
    Canon tie ((H.G.restrict (H.prev e s)).remove {e}) e (H.G.rf e) (H.G.nd e) ↔
      RevCond tie H e s := by
  have hw := hH.wf
  set X := (H.G.restrict (H.prev e s)).remove {e} with hXdef
  have hXs : X.Supp := (hw.supp_restrict _).restrict _
  rcases hRN with hR | hN
  · have hnd : H.G.nd e = none := hw.nd_none (Or.inr (Lab.IsRecv.not_isND hR))
    rcases Lab.IsRecv.recvB_or_recvNB hR with hB | hNB
    · rw [revCond_recvB hB]
      constructor
      · intro h
        obtain ⟨s'', -, ht, hrf, -⟩ := h.recvB hB
        exact ⟨s'', hrf, ht⟩
      · rintro ⟨s', hrf, ht⟩
        obtain ⟨s₂, hs₂, -, hid⟩ := hT.1 X e _ hXs ht
        rw [Prod.mk.injEq] at hid
        have hs₂X := ((Graph.mem_S _).mp hs₂).1
        have hs₂H : s₂ ∈ H.G.events := (Finset.mem_inter.mp (Finset.mem_inter.mp hs₂X).1).1
        have := hw.idx_inj s₂ hs₂H s' (hw.rf_mem _ _ hrf) hid.1 hid.2
        subst this
        exact Canon.intro (fun _ => ⟨s₂, hs₂X, ht, hrf, hnd⟩)
          (fun h => absurd hB (Lab.not_isRecvB_of_isRecvNB h))
          (fun h => absurd hR (Lab.IsND.not_isRecv h)) (fun h => absurd hR h)
    · rw [revCond_recvNB hNB]
      constructor
      · intro h
        exact (h.recvNB hNB).1
      · intro h
        exact Canon.intro (fun h' => absurd h' (Lab.not_isRecvB_of_isRecvNB hNB))
          (fun _ => ⟨h, hnd⟩) (fun h' => absurd hR (Lab.IsND.not_isRecv h'))
          (fun h' => absurd hR h')
  · rw [revCond_nd hN]
    have hrf : H.G.rf e = none := hw.rf_none (Or.inr (Lab.IsND.not_isRecv hN))
    obtain ⟨v, hv⟩ := hw.exists_nd he hN
    constructor
    · intro h
      obtain ⟨-, w, hw', hw''⟩ := h.nd hN
      rw [hw', hw'']
    · intro h
      rw [hv] at h
      exact Canon.intro (fun h' => absurd (Lab.IsRecvB.isRecv h') (Lab.IsND.not_isRecv hN))
        (fun h' => absurd (Lab.IsRecvNB.isRecv h') (Lab.IsND.not_isRecv hN))
        (fun _ => ⟨hrf, v, h.symm, hv⟩) (fun _ h' => absurd hN h')

omit [DecidableEq Q] in
/-- An event that is neither a receive nor an ND event has the canonical choice `(none, none)`,
which is its source and outcome in a well-formed graph. -/
theorem canon_other {F X : Graph Q} (hF : F.Wf) {e : Ev Q} (hR : ¬ e.IsRecv) (hN : ¬ e.IsND) :
    Canon tie X e (F.rf e) (F.nd e) :=
  Canon.intro (fun h => absurd (Lab.IsRecvB.isRecv h) hR)
    (fun h => absurd (Lab.IsRecvNB.isRecv h) hR) (fun h => absurd h hN)
    (fun _ _ => ⟨hF.rf_none (Or.inr hR), hF.nd_none (Or.inr hN)⟩)

/-- `revCond_iff_replay` (plan row M5, Section 2b, fate row p. 19): for a configuration `H` with
the invariant, a send `s` of `H` that is unread and last in the insertion order, and a receive
`r` of `H` not causally before `s`: `RevisitCondition(H, e, s)` holds for every
`e ∈ Deleted ∪ {r}` iff the replay base `K` is `porf`-closed in `H` and the canonical replay
from `H|K` of `r` followed by `Deleted` in insertion order reproduces `H \ {s}`. Every model,
every tie-break with `TieQ9`. -/
theorem revCond_iff_replay (hT : TieQ9 M tie) (hH : H.Inv M P) (hs : s ∈ H.G.events)
    (hsS : s.IsSend) (hread : ∀ r', H.G.rf r' ≠ some (.snd s))
    (hlast : ∀ x ∈ H.G.events, x ≠ s → H.pos x < H.pos s) (hr : r ∈ H.G.events)
    (hR : r.IsRecv) (hnp : ¬ H.G.porf r s) :
    (∀ d ∈ insert r (H.del r s), RevCond tie H d s) ↔
      H.G.Closed (H.base r s) ∧
        Replay tie P (H.G.restrict (H.base r s)) (r :: H.delList r s) (H.G.remove {s}) := by
  have hw := hH.wf
  have hmax : ∀ a, ¬ H.G.po s a := fun a h => by
    have h1 := hH.pos_lt h
    have hne : a ≠ s := by
      rintro rfl
      exact lt_irrefl _ h.2.2.2
    have h2 := hlast a h.2.1 hne
    omega
  have hrs : r ≠ s := fun h => Lab.IsSend.not_isRecv hsS (h ▸ hR)
  have hrd : r ∉ H.del r s := fun h => lt_irrefl _ (mem_del.mp h).2.2.1
  have hmemD : ∀ x, x ∈ H.delList r s ↔ x ∈ H.del r s := by
    intro x
    unfold delList
    rw [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨(hH.mem x).mpr (mem_del.mp h).1, h⟩⟩
  have hmemL : ∀ x, x ∈ r :: H.delList r s ↔ x ∈ insert r (H.del r s) := by
    intro x
    rw [List.mem_cons, hmemD, Finset.mem_insert]
  have hnd : (r :: H.delList r s).Nodup :=
    List.nodup_cons.mpr ⟨fun h => hrd ((hmemD r).mp h), hH.nodup.filter _⟩
  have hmem : ∀ e ∈ r :: H.delList r s, e ∈ H.G.events ∧ e ∉ H.base r s := by
    intro e he
    rcases Finset.mem_insert.mp ((hmemL e).mp he) with rfl | hd
    · exact ⟨hr, fun h => (mem_base.mp h).2.1 rfl⟩
    · exact ⟨(mem_del.mp hd).1, fun h => (mem_base.mp h).2.2.2 hd⟩
  have hpw : (r :: H.delList r s).Pairwise (fun a b => ¬ H.G.po b a) := by
    refine List.pairwise_cons.mpr ⟨fun d hd h => ?_, hH.po.filter _⟩
    have h1 := hH.pos_lt h
    have h2 := (mem_del.mp ((hmemD d).mp hd)).2.2.1
    omega
  have hpre : ∀ e ∈ r :: H.delList r s, ∀ a, H.G.po a e →
      a ∈ H.base r s ∨ a ∈ r :: H.delList r s := by
    intro e _ a ha
    by_cases har : a = r
    · exact Or.inr (har ▸ List.mem_cons_self)
    by_cases has : a = s
    · exact absurd (has ▸ ha) (hmax e)
    by_cases had : a ∈ H.del r s
    · exact Or.inr (List.mem_cons_of_mem _ ((hmemD a).mpr had))
    · exact Or.inl (mem_base.mpr ⟨ha.1, har, has, had⟩)
  have hsuc : ∀ b ∈ H.base r s, ∀ a ∈ r :: H.delList r s, ¬ H.G.po a b := by
    intro b hb a ha hab
    obtain ⟨-, -, -, hbd⟩ := mem_base.mp hb
    rcases Finset.mem_insert.mp ((hmemL a).mp ha) with rfl | had
    · exact hbd (po_del hH hnp hab)
    · exact del_po hH hab hbd had
  have hfin : H.G.restrict (H.base r s ∪ (r :: H.delList r s).toFinset) = H.G.remove {s} := by
    unfold Graph.remove
    refine hw.supp.restrict_congr fun x hx => ?_
    rw [Finset.mem_union, List.mem_toFinset, hmemL, Finset.mem_insert, mem_base,
      Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro (⟨-, -, hxs, -⟩ | rfl | hd)
      · exact ⟨hx, hxs⟩
      · exact ⟨hx, hrs⟩
      · exact ⟨hx, (mem_del.mp hd).2.1⟩
    · rintro ⟨-, hxs⟩
      by_cases hxr : x = r
      · exact Or.inr (Or.inl hxr)
      by_cases hxd : x ∈ H.del r s
      · exact Or.inr (Or.inr hxd)
      · exact Or.inl ⟨hx, hxr, hxs, hxd⟩
  have hctx : ∀ e ∈ r :: H.delList r s, H.G.restrict (H.base r s ∪ before (r :: H.delList r s) e)
      = (H.G.restrict (H.prev e s)).remove {e} := by
    intro e he
    unfold Graph.remove
    rw [restrict_restrict]
    refine hw.supp.restrict_congr fun x hx => ?_
    rw [base_before_iff hH hlast hrs hr ((hmemL e).mp he) hx]
    simp only [Finset.mem_inter, restrict_events, Finset.mem_sdiff, Finset.mem_singleton]
    tauto
  have hrep := replay_restrict_iff (tie := tie) hw hH.exec (r :: H.delList r s) (H.base r s)
    hnd hmem hpw hpre hsuc
  rw [hfin, canonList_iff _ _ hnd] at hrep
  rw [hrep]
  constructor
  · intro hc
    refine ⟨base_closed hH hsS hread hmax hR hnp fun d hd _ =>
      hc d (Finset.mem_insert_of_mem hd), fun e he => ?_⟩
    rw [hctx e he]
    have heH := (hmem e he).1
    by_cases hRN : e.IsRecv ∨ e.IsND
    · exact (canon_iff_revCond hT hH heH hRN).mpr (hc e ((hmemL e).mp he))
    · exact canon_other hw (fun h => hRN (Or.inl h)) (fun h => hRN (Or.inr h))
  · rintro ⟨hK, hall⟩
    have hall' : ∀ e ∈ insert r (H.del r s),
        Canon tie ((H.G.restrict (H.prev e s)).remove {e}) e (H.G.rf e) (H.G.nd e) := by
      intro e he
      rw [← hctx e ((hmemL e).mpr he)]
      exact hall e ((hmemL e).mpr he)
    -- a receive of `Deleted ∪ {r}` does not read an event outside its context
    have hsrc : ∀ q ∈ insert r (H.del r s), ∀ d, H.G.rf q = some (.snd d) →
        d ∈ H.prev q s := by
      intro q hq d hrf
      have hqR : q.IsRecv := (hw.rf_some hrf).2
      rcases Lab.IsRecv.recvB_or_recvNB hqR with hB | hNB
      · obtain ⟨s'', hs'', -, hrf', -⟩ := (hall' q hq).recvB hB
        rw [hrf, Option.some.injEq, Src.snd.injEq] at hrf'
        subst hrf'
        exact (mem_ctx.mp hs'').1
      · rw [(hall' q hq).recvNB hNB |>.1] at hrf
        cases hrf
    intro d hd
    have hdH : d ∈ H.G.events := (hmem d ((hmemL d).mpr hd)).1
    by_cases hRN : d.IsRecv ∨ d.IsND
    · exact (canon_iff_revCond hT hH hdH hRN).mp (hall' d hd)
    have hdR : ¬ d.IsRecv := fun h => hRN (Or.inl h)
    rw [revCond_other hdR (fun h => hRN (Or.inr h))]
    intro q hq hqR hrf
    have hdd : d ∈ H.del r s := (Finset.mem_insert.mp hd).resolve_left fun h => hdR (h ▸ hR)
    obtain ⟨-, -, hrd', hnd'⟩ := mem_del.mp hdd
    have hqH := (hw.rf_some hrf).1
    by_cases hqs : q = s
    · exact Lab.IsSend.not_isRecv hsS (hqs ▸ hqR)
    by_cases hqr : q = r
    · subst hqr
      rcases (mem_prev.mp (hsrc q (Finset.mem_insert_self _ _) d hrf)).2 with h | h
      · omega
      · exact hnd' h
    by_cases hqd : q ∈ H.del r s
    · have hpq := (mem_prev.mp (hsrc q (Finset.mem_insert_of_mem hqd) d hrf)).2
      have hqd' := (mem_prev.mp hq).2
      obtain ⟨-, -, -, hqn⟩ := mem_del.mp hqd
      have h1 : H.pos d ≤ H.pos q := hpq.resolve_right hnd'
      have h2 : H.pos q ≤ H.pos d := hqd'.resolve_right hqn
      have := (pos_inj ((hH.mem q).mpr hqH)).mp (le_antisymm h2 h1)
      subst this
      exact hdR hqR
    · have hqK : q ∈ H.base r s := mem_base.mpr ⟨hqH, hqr, hqs, hqd⟩
      have := Finset.mem_coe.mp (hK (Or.inr ⟨hqH, hrf⟩)
        (Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨hqH, hqK⟩)))
      exact (mem_base.mp (Finset.mem_inter.mp this).2).2.2.2 hdd

end Config

open Config

/-- `revCond_iff_replay` for the revisit of Algorithm 1 (lines 10–12 with Q15): `H = c.add s`
for a reachable-shaped configuration `c` (the invariant) and the send `s = next_P(c)`; the
guards `RevisitCondition(H, e', s)` for `e' ∈ Deleted ∪ {r}` and `RevisitCondition(H, s, s)`
hold iff `K` is `porf`-closed and the canonical replay from `H|K` of `r` followed by `Deleted`
in insertion order reproduces the graph of `c`. -/
theorem revCond_iff_replay_step (hT : TieQ9 M tie) {c : Config Q} (hc : c.Inv M P) {s r : Ev Q}
    (hn : M.nextP P c.G = some s) (hsS : s.IsSend) (hr : r ∈ (c.add s none none).G.events)
    (hR : r.IsRecv) (hnp : ¬ (c.add s none none).G.porf r s) :
    ((∀ d ∈ insert r ((c.add s none none).del r s), RevCond tie (c.add s none none) d s) ∧
        RevCond tie (c.add s none none) s s) ↔
      (c.add s none none).G.Closed ((c.add s none none).base r s) ∧
        Replay tie P ((c.add s none none).G.restrict ((c.add s none none).base r s))
          (r :: (c.add s none none).delList r s) c.G := by
  obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hn
  have hidx := Model.idx_of_nextEv ht
  have hsc : s ∉ c.order := fun h => hc.wf.not_mem_of_idx_eq_cnt hidx ((hc.mem s).mp h)
  have hH := hc.addSend ht hsS
  obtain ⟨hs, hread, -⟩ := addSend_facts hc ht
  have hlast : ∀ x ∈ (c.add s none none).G.events, x ≠ s →
      (c.add s none none).pos x < (c.add s none none).pos s := by
    intro x hx hxs
    have hxc : x ∈ c.order := (hc.mem x).mpr
      ((Finset.mem_insert.mp hx).resolve_left hxs)
    simp only [Config.pos, Config.add, List.idxOf_append_of_mem hxc,
      List.idxOf_append_of_notMem hsc, List.idxOf_cons_self]
    exact (List.idxOf_lt_length_of_mem hxc).trans_le (Nat.le_add_right _ _)
  have hrem : (c.add s none none).G.remove {s} = c.G := hc.wf.remove_add hidx
  rw [← hrem, ← revCond_iff_replay hT hH hs hsS hread hlast hr hR hnp]
  exact ⟨fun h => h.1, fun h => ⟨h, revCond_self hsS hread⟩⟩

end Must

#print axioms Must.Program.exec_restrict
#print axioms Must.nextEv_restrict
#print axioms Must.replay_restrict_iff
#print axioms Must.canonList_iff
#print axioms Must.mem_before_filter
#print axioms Must.Config.base_closed
#print axioms Must.Config.base_cons
#print axioms Must.Config.base_exec
#print axioms Must.Config.revisitCfg_restrict_base
#print axioms Must.Config.base_before_iff
#print axioms Must.Config.canon_iff_revCond
#print axioms Must.Config.revCond_iff_replay
#print axioms Must.revCond_iff_replay_step
