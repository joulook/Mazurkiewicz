import Mazurkiewicz.Must.Prefix

/-!
# `PrefixExtension` (Lemma A.13) and `availPrefix` (Definition A.6) (milestone M6)

Paper: Lemma A.13 and Definition A.6 (p. 30); their use in Algorithm 2 (p. 31, lines 13, 16).
Plan: `plan/must/lean/LEAN-PLAN.md`, fate rows A.13 and "Def. A.4, A.6"; Section 2b.

Lemma A.13 as printed (p. 30): "Given two executions `G` and `G'` s.t. `G∅ ⊑ G ⊏ G'`, and an
event `e ∈ G'.E \ G.E`, there is a unique execution `G_p` s.t. `G ⊑ G_p ⊑ G'` and
`G_p.E \ G.E = dom(G'.porf; [e]) \ G.E`." Here `dom(G'.porf; [e]) = G'.pred e` (the strict causal
predecessors of `e`; `porf` is a transitive closure, not reflexive).

* `prefixExt Gs Gt e := Gt|(Gs.E ∪ Gt.pred e)` (`PrefixExtension(G_s, G_t, e)`).
* For `Gs ⊑ Gt`: `closed_extSet` (the set is `porf`-closed in `Gt`), `Pfx.prefixExt_right`
  (`prefixExt ⊑ Gt`: consistent, an execution, a prefix), `Pfx.prefixExt_left`
  (`Gs ⊑ prefixExt`), `prefixExt_events`, `prefixExt_sdiff` (the printed property),
  `prefixExt_rf`, `prefixExt_nd` (sources and outcomes of `Gt`), `prefixExt_not_mem` (`e` is not
  in it when `e ∉ Gs`), `prefixExt_eq_of_mem` (it is `Gs` when `e ∈ Gs`).
* `prefixExt_unique`, `prefixExt_existsUnique` (Lemma A.13): of the printed `Gs ⊏ Gt` only
  `Gs ⊑ Gt` is used (the strictness component is not); `e ∈ Gt.E \ Gs.E` is not needed
  for existence and uniqueness; `e ∉ Gs` is needed for the exclusion `e ∉ prefixExt`.
  `prefixExt_least`: it is the least `⊑`-graph between `Gs` and `Gt` containing the strict
  predecessors of `e`.
* Definition A.6 (p. 30): `availPrefix(G, e) ≜ G|dom(G.porf?; [e'])`, `e'` the `po`-last event
  of the thread of `e` in `G`. Here `availSet G t` = the events of `G` that are, or are causally
  before, an event of thread `t`, and `availPrefix G e := G|availSet G e.tid`. For a thread with
  events this is the printed set (`availSet_eq_last`); for a thread without events it is empty
  (`availSet_eq_empty`, `availPrefix_eq_empty`: the empty graph; plan row "Def. A.6: empty
  thread: empty prefix").
* For `GetNext` (M7): `Pfx.availPrefix` (`availPrefix G e ⊑ G`), `availPrefix_pfx_iff` (the test
  of line 16, `availPrefix(G, e) ⊑ X` for `X ⊑ Gt`, is `availSet ⊆ X.E`; both graphs must be
  prefixes of one common graph, in line 16 the current maximal completion, not `G_t`),
  `availSet_congr` (it depends only on the events of the thread), `availSet_subset_of_mem`
  (A.16 ⟨8⟩2: the set of `availPrefix(G, e)` is in every `X ⊑ F` containing `e`), and the
  decomposition of the causal predecessors of the next event `e` of a thread of `Gs` in `Gt`:
  `mem_pred_next_iff`
  (`a ∈ Gt.pred e ↔ a ∈ availSet Gs e.tid ∨ a = s ∨ (a, s) ∈ Gt.porf` for the real source `s` of
  `e` in `Gt`), `pred_next_of_no_src`, `pred_next_of_src`.
* Next events: `Pfx.mem_of_po_next` (a thread predecessor in `Gt` of the next event of `Gs` is in
  `Gs`), `porfStep_next` (a causal step into it comes from `Gs` or is its source),
  `Pfx.eq_nextEv` (an event of `Gt` with the identity of the next event of a thread of `Gs` is
  that event: same label).

All results hold for every model `M` and every program `P`.
-/

namespace Must

open Graph Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q]
variable {M : Model Q} {P : Program Q}

/-- `PrefixExtension(G_s, G_t, e)` (Lemma A.13): the restriction of `G_t` to the events of `G_s`
and the strict causal predecessors of `e` in `G_t`. -/
def prefixExt (Gs Gt : Graph Q) (e : Ev Q) : Graph Q := Gt.restrict (Gs.events ∪ Gt.pred e)

variable {Gs Gt G G'' X : Graph Q} {e a : Ev Q}

/-! ### Lemma A.13 -/

/-- The set `Gs.E ∪ Gt.pred e` is `porf`-closed in `Gt`. -/
theorem closed_extSet (hGt : Gt.Wf) (hp : Gs.IsPrefixOf Gt) (e : Ev Q) :
    Gt.Closed (Gs.events ∪ Gt.pred e) :=
  closed_union hp.closed_events (hGt.closed_pred e)

omit [Membership Val Q] in
theorem prefixExt_events (hsub : Gs.events ⊆ Gt.events) :
    (prefixExt Gs Gt e).events = Gs.events ∪ Gt.pred e := by
  unfold prefixExt
  rw [restrict_events]
  exact Finset.inter_eq_right.mpr (Finset.union_subset hsub fun x hx => (mem_pred.mp hx).1)

omit [Membership Val Q] in
theorem mem_prefixExt (hsub : Gs.events ⊆ Gt.events) {x : Ev Q} :
    x ∈ (prefixExt Gs Gt e).events ↔ x ∈ Gs.events ∨ (x ∈ Gt.events ∧ Gt.porf x e) := by
  rw [prefixExt_events hsub, Finset.mem_union, mem_pred]

omit [Membership Val Q] in
/-- `prefixExt` has the sources of `Gt`. -/
theorem prefixExt_rf {x : Ev Q} (hx : x ∈ (prefixExt Gs Gt e).events) :
    (prefixExt Gs Gt e).rf x = Gt.rf x := by
  unfold prefixExt at hx ⊢
  simp [(Finset.mem_inter.mp hx).2]

omit [Membership Val Q] in
/-- `prefixExt` has the outcomes of `Gt`. -/
theorem prefixExt_nd {x : Ev Q} (hx : x ∈ (prefixExt Gs Gt e).events) :
    (prefixExt Gs Gt e).nd x = Gt.nd x := by
  unfold prefixExt at hx ⊢
  simp [(Finset.mem_inter.mp hx).2]

/-- `PrefixExtension(G_s, G_t, e) ⊑ G_t`. -/
theorem Pfx.prefixExt_right (hp : Pfx M P Gs Gt) (e : Ev Q) : Pfx M P (prefixExt Gs Gt e) Gt :=
  Pfx.of_isPrefixOf hp.cons' hp.exec' ⟨_, closed_extSet hp.wf' hp.pre e, rfl⟩

/-- `G_s ⊑ PrefixExtension(G_s, G_t, e)`. -/
theorem Pfx.prefixExt_left (hp : Pfx M P Gs Gt) (e : Ev Q) : Pfx M P Gs (prefixExt Gs Gt e) :=
  Pfx.of_between hp (hp.prefixExt_right e) (by
    rw [prefixExt_events hp.events_subset]
    exact Finset.subset_union_left)

omit [Membership Val Q] in
/-- The printed property of A.13: `G_p.E \ G_s.E = dom(G_t.porf; [e]) \ G_s.E`. -/
theorem prefixExt_sdiff (hsub : Gs.events ⊆ Gt.events) :
    (prefixExt Gs Gt e).events \ Gs.events = Gt.pred e \ Gs.events := by
  rw [prefixExt_events hsub, Finset.union_sdiff_left]

/-- `e` is not in `PrefixExtension(G_s, G_t, e)` when it is not in `G_s`. -/
theorem prefixExt_not_mem (hGt : Gt.Wf) (he : e ∉ Gs.events) :
    e ∉ (prefixExt Gs Gt e).events := by
  intro h
  unfold prefixExt at h
  rcases Finset.mem_union.mp (Finset.mem_inter.mp h).2 with h | h
  · exact he h
  · exact hGt.porf_irrefl e (mem_pred.mp h).2

/-- For `e ∈ G_s`, `PrefixExtension(G_s, G_t, e) = G_s`. -/
theorem prefixExt_eq_of_mem (hp : Pfx M P Gs Gt) (he : e ∈ Gs.events) : prefixExt Gs Gt e = Gs := by
  refine (Pfx.eq_of_events_eq (hp.prefixExt_right e) hp ?_)
  rw [prefixExt_events hp.events_subset]
  refine Finset.union_eq_left.mpr fun x hx => ?_
  have hx := mem_pred.mp hx
  have h := (closed_iff_porf Gt Gs.events).mp hp.closed hx.2
    (Finset.mem_inter.mpr ⟨hp.events_subset he, he⟩)
  exact (Finset.mem_inter.mp h).2

/-- Lemma A.13, uniqueness: an execution `G''` with `G_s ⊑ G'' ⊑ G_t` and
`G''.E \ G_s.E = dom(G_t.porf; [e]) \ G_s.E` is `PrefixExtension(G_s, G_t, e)`. -/
theorem prefixExt_unique (hp : Pfx M P Gs Gt) (h₁ : Pfx M P Gs G'') (h₂ : Pfx M P G'' Gt)
    (h₃ : G''.events \ Gs.events = Gt.pred e \ Gs.events) : G'' = prefixExt Gs Gt e := by
  refine Pfx.eq_of_events_eq h₂ (hp.prefixExt_right e) ?_
  rw [prefixExt_events hp.events_subset, ← Finset.union_sdiff_self_eq_union, ← h₃,
    Finset.union_sdiff_of_subset h₁.events_subset]

/-- Lemma A.13 (p. 30) for `G_s ⊑ G_t` and every event `e`: there is exactly one execution `G_p`
with `G_s ⊑ G_p ⊑ G_t` and `G_p.E \ G_s.E = dom(G_t.porf; [e]) \ G_s.E`. The printed hypotheses
`G_s ≠ G_t` (strictness of `G_s ⊏ G_t`; `G_s ⊑ G_t` is used) and `e ∈ G_t.E \ G_s.E` are not
used; `e ∉ G_s` is needed only for the exclusion `prefixExt_not_mem`. -/
theorem prefixExt_existsUnique (hp : Pfx M P Gs Gt) (e : Ev Q) :
    ∃! Gp, Pfx M P Gs Gp ∧ Pfx M P Gp Gt ∧ Gp.events \ Gs.events = Gt.pred e \ Gs.events :=
  ⟨prefixExt Gs Gt e, ⟨hp.prefixExt_left e, hp.prefixExt_right e,
      prefixExt_sdiff hp.events_subset⟩,
    fun _ h => prefixExt_unique hp h.1 h.2.1 h.2.2⟩

/-- `PrefixExtension(G_s, G_t, e)` is below every `G''` with `G_s ⊑ G'' ⊑ G_t` that contains the
strict causal predecessors of `e`. -/
theorem prefixExt_least (hp : Pfx M P Gs Gt) (h₁ : Pfx M P Gs G'') (h₂ : Pfx M P G'' Gt)
    (h₃ : Gt.pred e ⊆ G''.events) : Pfx M P (prefixExt Gs Gt e) G'' :=
  Pfx.of_between (hp.prefixExt_right e) h₂ (by
    rw [prefixExt_events hp.events_subset]
    exact Finset.union_subset h₁.events_subset h₃)

/-! ### Next events of a thread -/

omit [DecidableEq Q] in
/-- A thread predecessor in `Gt` of the next event `e` of its thread in `Gs ⊆ Gt` is in `Gs`. -/
theorem mem_of_po_next (hGs : Gs.Wf) (hGt : Gt.Wf) (hsub : Gs.events ⊆ Gt.events)
    (hidx : e.idx = Gs.cnt e.tid) (hpo : Gt.po a e) : a ∈ Gs.events := by
  obtain ⟨ha, -, ht, hi⟩ := hpo
  obtain ⟨a', ha', hat, hai⟩ := (hGs.exists_idx_iff e.tid a.idx).mpr (hidx ▸ hi)
  rwa [hGt.idx_inj a' (hsub ha') a ha (hat.trans ht.symm) hai] at ha'

/-- A causal step of `Gt` into the next event `e` of its thread in `Gs` comes from `Gs` or is
the edge from the source of `e`. -/
theorem porfStep_next (hp : Pfx M P Gs Gt) (hidx : e.idx = Gs.cnt e.tid)
    (h : Gt.porfStep a e) : a ∈ Gs.events ∨ Gt.rf e = some (.snd a) := by
  rcases h with hpo | ⟨-, hrf⟩
  · exact Or.inl (mem_of_po_next hp.wf hp.wf' hp.events_subset hidx hpo)
  · exact Or.inr hrf

/-- An event of `Gt` with the identity `(t, |Gs.E_t|)` of the next event `e` of thread `t` in
`Gs ⊑ Gt` is `e`: executions of `P` give it the same label. -/
theorem Pfx.eq_nextEv (hp : Pfx M P Gs Gt) {t : Tid} (hn : P.nextEv Gs t = some e)
    {x : Ev Q} (hx : x ∈ Gt.events) (hxt : x.tid = t) (hxi : x.idx = Gs.cnt t) : x = e := by
  have hGs := hp.wf
  have hGt := hp.wf'
  have hsub := hp.events_subset
  have htr : Gt.traceBefore t (Gs.cnt t) = Gs.trace t := by
    unfold trace
    refine traceBefore_congr fun j hj => (retAt_congr (fun y h1 h2 => ?_)
      (fun y hy _ _ => ?_)).symm
    · refine ⟨fun h => hsub h, fun h => ?_⟩
      obtain ⟨y', hy', h1', h2'⟩ := hGs.exists_of_lt_cnt (h2 ▸ hj : y.idx < Gs.cnt t)
      rwa [← hGt.idx_inj y' (hsub hy') y h (h1'.trans h1.symm) h2']
    · exact ⟨hp.rf_eq hy, hp.nd_eq hy⟩
  have hl := hp.exec' x hx
  rw [hxt, hxi, htr] at hl
  unfold Program.nextEv at hn
  rw [hl] at hn
  simp only [Option.map_some, Option.some.injEq] at hn
  rw [← hn]
  cases x
  simp_all

/-! ### Definition A.6: `availPrefix` -/

/-- `dom(G.porf?; [thread t])`: the events of `G` that are, or are causally before, an event of
thread `t`. -/
def Graph.availSet (G : Graph Q) (t : Tid) : Finset (Ev Q) :=
  G.events.filter (fun a => ∃ x ∈ G.events, x.tid = t ∧ (a = x ∨ G.porf a x))

/-- `availPrefix(G, e)` (Definition A.6). -/
def availPrefix (G : Graph Q) (e : Ev Q) : Graph Q := G.restrict (G.availSet e.tid)

omit [Membership Val Q] in
theorem mem_availSet {t : Tid} {a : Ev Q} :
    a ∈ G.availSet t ↔ a ∈ G.events ∧ ∃ x ∈ G.events, x.tid = t ∧ (a = x ∨ G.porf a x) := by
  unfold Graph.availSet
  rw [Finset.mem_filter]

omit [Membership Val Q] in
theorem availSet_subset (t : Tid) : G.availSet t ⊆ G.events := Finset.filter_subset _ _

omit [Membership Val Q] in
theorem availPrefix_events : (availPrefix G e).events = G.availSet e.tid := by
  unfold availPrefix
  rw [restrict_events]
  exact Finset.inter_eq_right.mpr (availSet_subset _)

/-- The set of `availPrefix` is `porf`-closed. -/
theorem Graph.Wf.closed_availSet (hG : G.Wf) (t : Tid) : G.Closed (G.availSet t) := by
  intro a b hab hb
  have hb := mem_availSet.mp (Finset.mem_inter.mp (Finset.mem_coe.mp hb)).2
  have ha := (hG.mem_of_porfStep hab).1
  obtain ⟨x, hx, hxt, hbx⟩ := hb.2
  have hax : G.porf a x := by
    rcases hbx with rfl | hbx
    · exact TransGen.single hab
    · exact TransGen.head hab hbx
  exact Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨ha, mem_availSet.mpr ⟨ha, x, hx, hxt,
    Or.inr hax⟩⟩)

/-- `availPrefix(G, e) ⊑ G`. -/
theorem Pfx.availPrefix (hc : M.cons G) (hE : P.Exec G) (e : Ev Q) :
    Pfx M P (availPrefix G e) G :=
  Pfx.of_isPrefixOf hc hE ⟨_, (M.wf _ hc).closed_availSet e.tid, rfl⟩

/-- Definition A.6 for a thread with events: with `e'` the `po`-last event of the thread,
`availSet G t = dom(G.porf?; [e'])`. -/
theorem availSet_eq_last (hG : G.Wf) {t : Tid} {x : Ev Q} (hx : x ∈ G.events) (hxt : x.tid = t)
    (hlast : x.idx + 1 = G.cnt t) : G.availSet t = insert x (G.pred x) := by
  ext a
  rw [mem_availSet, Finset.mem_insert, mem_pred]
  constructor
  · rintro ⟨ha, y, hy, hyt, hay⟩
    have hyx : y = x ∨ G.po y x := by
      by_cases h : y.idx = x.idx
      · exact Or.inl (hG.idx_inj y hy x hx (hyt.trans hxt.symm) h)
      · have := hG.idx_lt_cnt hy
        rw [hyt] at this
        exact Or.inr ⟨hy, hx, hyt.trans hxt.symm, by omega⟩
    rcases hyx with rfl | hyx
    · rcases hay with rfl | hay
      · exact Or.inl rfl
      · exact Or.inr ⟨ha, hay⟩
    · rcases hay with rfl | hay
      · exact Or.inr ⟨ha, TransGen.single (Or.inl hyx)⟩
      · exact Or.inr ⟨ha, TransGen.tail hay (Or.inl hyx)⟩
  · rintro (rfl | ⟨ha, hax⟩)
    · exact ⟨hx, a, hx, hxt, Or.inl rfl⟩
    · exact ⟨ha, x, hx, hxt, Or.inr hax⟩

omit [DecidableEq Q] in
/-- The last event of a thread with events. -/
theorem exists_last (hG : G.Wf) {t : Tid} (h : 0 < G.cnt t) :
    ∃ x ∈ G.events, x.tid = t ∧ x.idx + 1 = G.cnt t := by
  obtain ⟨x, hx, hxt, hxi⟩ := (hG.exists_idx_iff t (G.cnt t - 1)).mpr (by omega)
  exact ⟨x, hx, hxt, by omega⟩

omit [Membership Val Q] in
/-- Definition A.6 for a thread without events (plan: "empty thread: empty prefix"). -/
theorem availSet_eq_empty {t : Tid} (h : ∀ x ∈ G.events, x.tid ≠ t) : G.availSet t = ∅ := by
  ext a
  rw [mem_availSet]
  simp only [Finset.notMem_empty, iff_false, not_and]
  rintro - ⟨x, hx, hxt, -⟩
  exact h x hx hxt

omit [Membership Val Q] in
/-- The restriction to `∅` is the empty graph. -/
theorem restrict_empty (G : Graph Q) : G.restrict ∅ = Graph.empty := by
  apply Graph.ext
  · simp [empty]
  · funext x
    simp [empty]
  · funext x
    simp [empty]

/-- `availPrefix(G, e)` is the empty graph when the thread of `e` has no event in `G`. -/
theorem availPrefix_eq_empty (hG : G.Wf) (h : G.cnt e.tid = 0) :
    availPrefix G e = Graph.empty := by
  unfold availPrefix
  rw [availSet_eq_empty fun x hx hxt => by
    have := hG.idx_lt_cnt hx
    rw [hxt] at this
    omega, restrict_empty]

/-- The test of Algorithm 2, line 16: for `G ⊑ Gt` and `X ⊑ Gt`, `availPrefix(G, e) ⊑ X` iff the
set of `availPrefix(G, e)` is contained in `X.E`. Both graphs must be prefixes of one common
graph; in line 16 that graph is the current maximal completion `MaxCompletion(G_p, A)` (the second
argument of the recursive call), not `G_t`. -/
theorem availPrefix_pfx_iff {Gt : Graph Q} (hG : Pfx M P G Gt) (hX : Pfx M P X Gt) :
    Pfx M P (availPrefix G e) X ↔ G.availSet e.tid ⊆ X.events := by
  constructor
  · intro h
    rw [← availPrefix_events]
    exact h.events_subset
  · intro h
    refine Pfx.of_between ((Pfx.availPrefix hG.cons hG.exec e).trans hG) hX ?_
    rw [availPrefix_events]
    exact h

/-- `availSet` depends only on the events of the thread: for `G ⊑ G'` with the same events of
thread `t`, the sets are equal. -/
theorem availSet_congr {G' : Graph Q} (hp : Pfx M P G G') {t : Tid}
    (hthr : ∀ x ∈ G'.events, x.tid = t → x ∈ G.events) : G.availSet t = G'.availSet t := by
  ext a
  rw [mem_availSet, mem_availSet]
  constructor
  · rintro ⟨ha, x, hx, hxt, hax⟩
    refine ⟨hp.events_subset ha, x, hp.events_subset hx, hxt, ?_⟩
    rcases hax with rfl | hax
    · exact Or.inl rfl
    · exact Or.inr ((hp.pre.porf_iff hx).mp hax)
  · rintro ⟨ha, x, hx, hxt, hax⟩
    have hxG := hthr x hx hxt
    rcases hax with rfl | hax
    · exact ⟨hxG, a, hxG, hxt, Or.inl rfl⟩
    · have h := (closed_iff_porf G' G.events).mp hp.closed hax (Finset.mem_inter.mpr ⟨hx, hxG⟩)
      exact ⟨(Finset.mem_inter.mp h).2, x, hxG, hxt, Or.inr ((hp.pre.porf_iff hxG).mpr hax)⟩

/-- `availPrefix` depends only on the events of the thread. -/
theorem availPrefix_congr {G' : Graph Q} (hp : Pfx M P G G')
    (hthr : ∀ x ∈ G'.events, x.tid = e.tid → x ∈ G.events) :
    availPrefix G e = availPrefix G' e := by
  unfold availPrefix
  rw [← availSet_congr hp hthr]
  refine (congrArg (fun H : Graph Q => H.restrict (G.availSet e.tid)) hp.eq_restrict).trans ?_
  rw [restrict_restrict]
  congr 1
  ext x
  simp only [Finset.mem_inter]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨availSet_subset _ h, h⟩

/-! ### The causal predecessors of the next event -/

/-- For `Gs ⊑ Gt` and the next event `e` of its thread in `Gs`, an event of `Gt`: the strict
causal predecessors of `e` in `Gt` are the set of `availPrefix(Gs, e)`, the real source `s` of
`e` in `Gt` and the strict causal predecessors of `s`. -/
theorem mem_pred_next_iff (hp : Pfx M P Gs Gt) (he : e ∈ Gt.events)
    (hidx : e.idx = Gs.cnt e.tid) :
    a ∈ Gt.pred e ↔
      a ∈ Gs.availSet e.tid ∨ ∃ s, Gt.rf e = some (.snd s) ∧ (a = s ∨ Gt.porf a s) := by
  have hGt := hp.wf'
  have hGs := hp.wf
  rw [mem_pred]
  constructor
  · rintro ⟨ha, hae⟩
    obtain ⟨c, hac, hce⟩ := TransGen.tail'_iff.mp hae
    have hac' := reflTransGen_iff_eq_or_transGen.mp hac
    rcases hce with hpo | ⟨-, hrf⟩
    · left
      have hcG := mem_of_po_next hGs hGt hp.events_subset hidx hpo
      refine mem_availSet.mpr ?_
      rcases hac' with hca | hac'
      · exact ⟨hca ▸ hcG, c, hcG, hpo.2.2.1, Or.inl hca.symm⟩
      · have h := (closed_iff_porf Gt Gs.events).mp hp.closed hac'
          (Finset.mem_inter.mpr ⟨hpo.1, hcG⟩)
        exact ⟨(Finset.mem_inter.mp h).2, c, hcG, hpo.2.2.1,
          Or.inr ((hp.pre.porf_iff hcG).mpr hac')⟩
    · right
      rcases hac' with hca | hac'
      · exact ⟨c, hrf, Or.inl hca.symm⟩
      · exact ⟨c, hrf, Or.inr hac'⟩
  · rintro (h | ⟨s, hrf, has⟩)
    · obtain ⟨ha, x, hx, hxt, hax⟩ := mem_availSet.mp h
      have hxe : Gt.porfStep x e :=
        Or.inl ⟨hp.events_subset hx, he, hxt, hidx ▸ (hxt ▸ hGs.idx_lt_cnt hx)⟩
      refine ⟨hp.events_subset ha, ?_⟩
      rcases hax with rfl | hax
      · exact TransGen.single hxe
      · exact TransGen.tail (hp.pre.porf_le hax) hxe
    · have hse : Gt.porfStep s e := Or.inr ⟨he, hrf⟩
      rcases has with rfl | has
      · exact ⟨hGt.rf_mem _ _ hrf, TransGen.single hse⟩
      · exact ⟨(hGt.mem_of_porf has).1, TransGen.tail has hse⟩

/-- `pred_next`: without a real source of `e` in `Gt`, the strict causal predecessors of `e` are
the set of `availPrefix(Gs, e)`. -/
theorem pred_next_of_no_src (hp : Pfx M P Gs Gt) (he : e ∈ Gt.events)
    (hidx : e.idx = Gs.cnt e.tid) (hns : ∀ s, Gt.rf e ≠ some (.snd s)) :
    Gt.pred e = Gs.availSet e.tid := by
  ext a
  rw [mem_pred_next_iff hp he hidx]
  constructor
  · rintro (h | ⟨s, hs, -⟩)
    · exact h
    · exact absurd hs (hns s)
  · exact Or.inl

/-- With the real source `s` of `e` in `Gt`: `Gt.pred e = availSet Gs e.tid ∪ {s} ∪ Gt.pred s`. -/
theorem pred_next_of_src (hp : Pfx M P Gs Gt) (he : e ∈ Gt.events)
    (hidx : e.idx = Gs.cnt e.tid) {s : Ev Q} (hs : Gt.rf e = some (.snd s)) :
    Gt.pred e = Gs.availSet e.tid ∪ insert s (Gt.pred s) := by
  have hGt := hp.wf'
  ext a
  rw [mem_pred_next_iff hp he hidx, Finset.mem_union, Finset.mem_insert, mem_pred]
  constructor
  · rintro (h | ⟨s', hs', has⟩)
    · exact Or.inl h
    · rw [hs] at hs'
      cases hs'
      rcases has with rfl | has
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨(hGt.mem_of_porf has).1, has⟩)
  · rintro (h | has | ⟨-, has⟩)
    · exact Or.inl h
    · exact Or.inr ⟨s, hs, Or.inl has⟩
    · exact Or.inr ⟨s, hs, Or.inr has⟩

/-- Helper for A.16 ⟨8⟩2: if `e`, the next event of its thread in `G`, is an event of `X`, with
`G ⊑ F` and `X ⊑ F`, then the set of `availPrefix(G, e)` is contained in `X.E`. -/
theorem availSet_subset_of_mem {F : Graph Q} (hG : Pfx M P G F) (hX : Pfx M P X F)
    (hn : P.nextEv G e.tid = some e) (heX : e ∈ X.events) : G.availSet e.tid ⊆ X.events := by
  intro a ha
  obtain ⟨haG, x, hx, hxt, hax⟩ := mem_availSet.mp ha
  have heF := hX.events_subset heX
  have hidx := Model.idx_of_nextEv hn
  have hxe : F.porfStep x e :=
    Or.inl ⟨hG.events_subset hx, heF, hxt, hidx ▸ (hxt ▸ hG.wf.idx_lt_cnt hx)⟩
  have hae : F.porf a e := by
    rcases hax with rfl | hax
    · exact TransGen.single hxe
    · exact TransGen.tail (hG.pre.porf_le hax) hxe
  exact (Finset.mem_inter.mp ((closed_iff_porf F X.events).mp hX.closed hae
    (Finset.mem_inter.mpr ⟨heF, heX⟩))).2

end Must

#print axioms Must.availSet_subset_of_mem

#print axioms Must.closed_extSet
#print axioms Must.prefixExt_events
#print axioms Must.Pfx.prefixExt_right
#print axioms Must.Pfx.prefixExt_left
#print axioms Must.prefixExt_sdiff
#print axioms Must.prefixExt_not_mem
#print axioms Must.prefixExt_eq_of_mem
#print axioms Must.prefixExt_unique
#print axioms Must.prefixExt_existsUnique
#print axioms Must.prefixExt_least
#print axioms Must.mem_of_po_next
#print axioms Must.porfStep_next
#print axioms Must.Pfx.eq_nextEv
#print axioms Must.Graph.Wf.closed_availSet
#print axioms Must.Pfx.availPrefix
#print axioms Must.availSet_eq_last
#print axioms Must.availSet_eq_empty
#print axioms Must.availPrefix_eq_empty
#print axioms Must.availPrefix_pfx_iff
#print axioms Must.availSet_congr
#print axioms Must.availPrefix_congr
#print axioms Must.mem_pred_next_iff
#print axioms Must.pred_next_of_no_src
#print axioms Must.pred_next_of_src
