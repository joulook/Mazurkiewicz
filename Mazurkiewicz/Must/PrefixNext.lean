import Mazurkiewicz.Must.PrefixExt

/-!
# Lemma A.14 (Next prefix) (milestone M6)

Paper: Lemma A.14 (p. 30); Algorithm 2, lines 9, 11–13, 22 (p. 31). Plan:
`plan/must/lean/LEAN-PLAN.md`, Section 2b (A.14, repaired signature and two cases), fate row
A.14.

Lemma A.14 as printed (p. 30): "Given two executions `G_s` and `G_t` s.t. `G∅ ⊑ G_s ⊏ G_t`, and
an event `e ∈ avail(G_s) ∩ G_t.E`, either there exists a step `t = e@_` and an execution `G'`
s.t. `G_s →t G' ⊑ G_t`, or `e ∈ R` and there is an execution `G'` s.t.
`PrefixExtension(G_s, G_t, event(t)) →t →e@p G' ⊑ G_t`, where `⟨t, p⟩ = GetSend(G_s, G_t, e)`,
and there is no execution `G''` s.t. `e ∈ G''.E` and `G_s ⊏ G'' ⊏ G'`." `GetSend` takes a graph
and a receive and returns its source (Algorithm 2, lines 24–25); the printed call has three
arguments and a pair as result. Repaired reading (plan): `s₀ = G_t.rf(e)` (line 12 calls
`GetSend(G_t, r)`, with `r` unbound: `r₀` of line 11 is meant). `G_s.rf(e)` is undefined since
`e ∉ G_s` (`getSend_source_graph`, an illustration of the typing repair, not a witness of
falsity).

* `revTarget Gs Gt s₀ r₀` = `AddRecv(Add(G_p, s₀), r₀, s₀)` with `G_p = prefixExt Gs Gt s₀`
  (line 22, `G_n`).
* `Pfx.step_of_next` (the common step): for `X ⊑ Gt` and the next event `x` of its thread in
  `X`, an event of `Gt` all of whose causal steps in `Gt` come from `X`, adding `x` with its source
  and outcome in `Gt` is an operational step (A.2 with Q7) to a graph `⊑ Gt`; that graph is
  `Gt|(X.E ∪ {x})` (`Pfx.add_eq`).
* Case 1 (`next_prefix_case1`): the source of `e` in `Gt` is not a real send outside `Gs`;
  `case1_iff`: an operational step from `Gs` adding `e` to a graph `⊑ Gt` exists iff Case 1
  holds; `case1_unique`: its source and outcome are those of `Gt` (Algorithm 2, line 9).
* Case 2 (`next_prefix_case2`): `e` is a receive reading `s₀ ∉ Gs` in `Gt`: `s₀` is the next
  event of its thread in `G_p`, adding it is an operational step, then adding `e` reading `s₀` is
  one; the result `G' = revTarget Gs Gt s₀ e` is `⊑ Gt`, `Gs ⊏ G'`, and it is
  `Gt|(Gs.E ∪ Gt.pred s₀ ∪ {s₀, e})` (`revTarget_eq`). Minimality, stronger than printed
  (`revTarget_minimal`): every `G''` with `Gs ⊑ G'' ⊑ G'` and `e ∈ G''.E` is `G'`; the printed
  form is `revTarget_no_between`.
* `next_prefix` (plan signature: `Gs ⊏ Gt`, `e = next_P(Gs) ∈ Gt.E`) and `next_prefix_avail`
  (printed hypothesis `e ∈ avail(Gs) ∩ Gt.E`): exactly one of the two cases, with its
  conclusions.

* For M7/M8: `case2_unread` (`s₀` is read by no receive of `G_p`, and is unread in `G_p + s₀`),
  `case2_nextEv_e_Gp` (`r₀` is the next event of its thread in `G_p`), `revTarget_least`
  (`G' ⊑ G''` for every `Gs ⊑ G'' ⊑ Gt` with `e ∈ G''.E`), `next_prefix_result` (in both cases
  the result `G'` satisfies `G' ⊑ Gt`, `Gs ⊏ G'` and contains `next_P(Gs)`).

All results hold for every model `M` and every program `P`; strictness of `Gs ⊏ Gt` and
availability of `e` are not used (only that `e` is the next event of its thread in `Gs`).
-/

namespace Must

open Graph Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q]
variable {M : Model Q} {P : Program Q}

/-- `G_n = AddRecv(Add(G_p, s₀), r₀, s₀)` with `G_p = PrefixExtension(Gs, Gt, s₀)` (Algorithm 2,
line 22). -/
def revTarget (Gs Gt : Graph Q) (s₀ r₀ : Ev Q) : Graph Q :=
  ((prefixExt Gs Gt s₀).addSend s₀).addRecv r₀ (.snd s₀)

variable {Gs Gt G'' X : Graph Q} {e x s₀ : Ev Q}

omit [DecidableEq Q] [Membership Val Q] in
/-- The next event of thread `t` is in thread `t`. -/
theorem nextEv_tid {G : Graph Q} {t : Tid} (h : P.nextEv G t = some e) : e.tid = t := by
  unfold Program.nextEv at h
  obtain ⟨l, -, rfl⟩ := Option.map_eq_some_iff.mp h
  rfl

/-- `next_P(G) = e` makes `e` the next event of its thread. -/
theorem nextEv_of_nextP {G : Graph Q} (h : M.nextP P G = some e) : P.nextEv G e.tid = some e := by
  obtain ⟨t, ht⟩ := exists_nextEv_of_nextP h
  rwa [nextEv_tid ht]

/-- An available event is the next event of its thread. -/
theorem nextEv_of_mem_availM {G : Graph Q} (h : e ∈ M.availM P G) : P.nextEv G e.tid = some e := by
  obtain ⟨t, -, ht, -⟩ := M.mem_availM_iff'.mp h
  rwa [nextEv_tid ht]

omit [DecidableEq Q] in
/-- An illustration of the typing repair of A.14 (not a witness of falsity): the printed
`GetSend(G_s, …)` would read the source of `e` in `G_s`, which is undefined (`none`), since the
next event of a thread is not in the graph. -/
theorem getSend_source_graph {G : Graph Q} (hG : G.Wf) (hn : P.nextEv G e.tid = some e) :
    G.rf e = none :=
  hG.rf_none (Or.inl (hG.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv hn)))

omit [DecidableEq Q] in
/-- The source and outcome of an event of `Gt` are admissible over a graph containing its real
source (A.2). -/
theorem adm_of_mem {G : Graph Q} (hGt : Gt.Wf) (he : e ∈ Gt.events)
    (hsrc : ∀ s, Gt.rf e = some (.snd s) → s ∈ G.events) : Adm G e (Gt.rf e) (Gt.nd e) := by
  rcases Lab.cases_lab e.lab with hR | hS | hN | hL
  · obtain ⟨y, hy⟩ := hGt.exists_rf he hR
    refine Or.inl ⟨hR, hGt.nd_none (Or.inr (Lab.IsRecv.not_isND hR)), ?_⟩
    cases y with
    | bot => exact Or.inl hy
    | snd s =>
      exact Or.inr ⟨s, (Graph.mem_S _).mpr ⟨hsrc s hy, (hGt.rf_match _ _ hy).isSend⟩, hy⟩
  · exact Or.inr (Or.inr ⟨Lab.IsSend.not_isRecv hS, Lab.IsSend.not_isND hS,
      hGt.rf_none (Or.inr (Lab.IsSend.not_isRecv hS)),
      hGt.nd_none (Or.inr (Lab.IsSend.not_isND hS))⟩)
  · obtain ⟨v, hv⟩ := hGt.exists_nd he hN
    exact Or.inr (Or.inl ⟨hN, hGt.rf_none (Or.inr (Lab.IsND.not_isRecv hN)), v,
      hGt.nd_mem e v hv, hv⟩)
  · exact Or.inr (Or.inr ⟨Lab.IsLoc.not_isRecv hL, Lab.IsLoc.not_isND hL,
      hGt.rf_none (Or.inr (Lab.IsLoc.not_isRecv hL)),
      hGt.nd_none (Or.inr (Lab.IsLoc.not_isND hL))⟩)

/-- Adding an event of `Gt` with its source and outcome in `Gt` to `X ⊑ Gt` is the restriction of
`Gt` to `X.E ∪ {x}`. -/
theorem Pfx.add_eq (hX : Pfx M P X Gt) (hx : x ∈ Gt.events) :
    X.add x (Gt.rf x) (Gt.nd x) = Gt.restrict (insert x X.events) := by
  calc X.add x (Gt.rf x) (Gt.nd x) = (Gt.restrict X.events).add x (Gt.rf x) (Gt.nd x) := by
        rw [← hX.eq_restrict]
    _ = Gt.restrict (insert x X.events) := restrict_add_self hx

/-- The common step of A.14. For `X ⊑ Gt` and an event `x` of `Gt` that is the next event of its
thread in `X` and whose causal steps in `Gt` all come from `X`: adding `x` with its source and
outcome in `Gt` is an operational step (A.2 with Q7, premised) whose result is `⊑ Gt`. -/
theorem Pfx.step_of_next (hX : Pfx M P X Gt) (hx : x ∈ Gt.events)
    (hn : P.nextEv X x.tid = some x) (hst : ∀ a, Gt.porfStep a x → a ∈ X.events) :
    OpAdd M P X x (Gt.rf x) (Gt.nd x) ∧ Pfx M P (X.add x (Gt.rf x) (Gt.nd x)) Gt := by
  have hGt := hX.wf'
  have hcl := closed_insert hGt hX.closed hst
  have hpfx : Pfx M P (X.add x (Gt.rf x) (Gt.nd x)) Gt := by
    rw [hX.add_eq hx]
    exact Pfx.of_isPrefixOf hX.cons' hX.exec' ⟨_, hcl, rfl⟩
  have hsrc : ∀ s, Gt.rf x = some (.snd s) → s ∈ X.events :=
    fun s hs => hst s (Or.inr ⟨hx, hs⟩)
  refine ⟨⟨M.mem_availM_iff'.mpr ⟨x.tid, tid_mem_of_nextEv hX.wf hX.exec hn, hn, ?_⟩,
    adm_of_mem hGt hx hsrc, hpfx.cons⟩, hpfx⟩
  by_cases hB : x.IsRecvB
  · right
    obtain ⟨y, hy⟩ := hGt.exists_rf hx (Lab.IsRecvB.isRecv hB)
    cases y with
    | bot => exact absurd (hGt.rf_bot x hy) (Lab.not_isRecvB_of_isRecvNB · hB)
    | snd s =>
      refine ⟨s, (Graph.mem_S _).mpr ⟨hsrc s hy, (hGt.rf_match _ _ hy).isSend⟩, ?_⟩
      have hnd : Gt.nd x = none := hGt.nd_none (Or.inr (Lab.IsRecv.not_isND
        (Lab.IsRecvB.isRecv hB)))
      have h := hpfx.cons
      rw [hy, hnd] at h
      exact h
  · exact Or.inl hB

/-! ### Case 1 -/

/-- Lemma A.14, Case 1: the source of `e` in `Gt` is not a real send outside `Gs` (`e` is not a
receive, or it reads `⊥`, or a send of `Gs`). Then `Gs → Gs + e` with the outcome of `e` in `Gt`
is an operational step and `Gs + e ⊑ Gt`. -/
theorem next_prefix_case1 (hp : Pfx M P Gs Gt) (hn : P.nextEv Gs e.tid = some e)
    (he : e ∈ Gt.events) (hsrc : ∀ s, Gt.rf e = some (.snd s) → s ∈ Gs.events) :
    OpAdd M P Gs e (Gt.rf e) (Gt.nd e) ∧ Pfx M P (Gs.add e (Gt.rf e) (Gt.nd e)) Gt := by
  refine hp.step_of_next he hn fun a ha => ?_
  rcases porfStep_next hp (Model.idx_of_nextEv hn) ha with h | h
  · exact h
  · exact hsrc a h

/-- A step from `Gs` adding `e` to a graph `⊑ Gt` adds `e` with its source and outcome in
`Gt`. -/
theorem case1_unique
    {src : Option (Src Q)} {out : Option Val} (h : Pfx M P (Gs.add e src out) Gt) :
    src = Gt.rf e ∧ out = Gt.nd e := by
  have hmem : e ∈ (Gs.add e src out).events := Finset.mem_insert_self _ _
  have h1 := h.rf_eq hmem
  have h2 := h.nd_eq hmem
  simp only [add_rf, add_nd, Function.update_self] at h1 h2
  exact ⟨h1, h2⟩

/-- Algorithm 2, line 9: a (printed, unpremised) operational step from `Gs` adding `e` to a graph
`⊑ Gt` exists iff Case 1 holds. -/
theorem case1_iff (hp : Pfx M P Gs Gt) (hn : P.nextEv Gs e.tid = some e) (he : e ∈ Gt.events) :
    (∃ src out, OpAdd₀ M P Gs e src out ∧ Pfx M P (Gs.add e src out) Gt) ↔
      ∀ s, Gt.rf e = some (.snd s) → s ∈ Gs.events := by
  constructor
  · rintro ⟨src, out, ⟨-, hadm⟩, h⟩ s hs
    obtain ⟨h1, -⟩ := case1_unique h
    exact hadm.src_mem (h1.trans hs)
  · intro hsrc
    obtain ⟨h1, h2⟩ := next_prefix_case1 hp hn he hsrc
    exact ⟨_, _, ⟨h1.1, h1.2.1⟩, h2⟩

/-! ### Case 2 -/

/-- Case 2: `s₀` is a send of `Gt`, `e` a receive. -/
theorem case2_facts (hp : Pfx M P Gs Gt) (hs : Gt.rf e = some (.snd s₀)) :
    s₀ ∈ Gt.events ∧ s₀.IsSend ∧ e.IsRecv ∧ s₀ ≠ e := by
  have hm := hp.wf'.rf_match _ _ hs
  refine ⟨hp.wf'.rf_mem _ _ hs, hm.isSend, hm.isRecv, fun h => ?_⟩
  exact Lab.IsSend.not_isRecv hm.isSend (h ▸ hm.isRecv)

/-- `s₀` is the next event of its thread in `G_p = PrefixExtension(Gs, Gt, s₀)`. -/
theorem case2_nextEv_s₀ (hp : Pfx M P Gs Gt) (hs : Gt.rf e = some (.snd s₀))
    (hs₀ : s₀ ∉ Gs.events) :
    P.nextEv (prefixExt Gs Gt s₀) s₀.tid = some s₀ := by
  have hGt := hp.wf'
  obtain ⟨hs₀Gt, -, -, -⟩ := case2_facts hp hs
  refine nextEv_restrict hGt hp.exec' hs₀Gt ?_ (fun a ha => ?_) (fun b hb hpo => ?_)
  · rintro h
    rcases Finset.mem_union.mp h with h | h
    · exact hs₀ h
    · exact hGt.porf_irrefl s₀ (mem_pred.mp h).2
  · exact Finset.mem_union_right _ (mem_pred.mpr ⟨ha.1, TransGen.single (Or.inl ha)⟩)
  · rcases Finset.mem_union.mp hb with hb | hb
    · have h := (closed_iff_porf Gt Gs.events).mp hp.closed (TransGen.single (Or.inl hpo))
        (Finset.mem_inter.mpr ⟨hpo.2.1, hb⟩)
      exact hs₀ (Finset.mem_inter.mp h).2
    · exact hGt.porf_irrefl s₀ (TransGen.head (Or.inl hpo) (mem_pred.mp hb).2)

/-- Case 2, first step: `G_p → G_p + s₀` is an operational step, and `G_p + s₀ ⊑ Gt`. -/
theorem case2_step₁ (hp : Pfx M P Gs Gt) (hs : Gt.rf e = some (.snd s₀)) (hs₀ : s₀ ∉ Gs.events) :
    OpAdd M P (prefixExt Gs Gt s₀) s₀ none none ∧
      Pfx M P ((prefixExt Gs Gt s₀).addSend s₀) Gt := by
  have hGt := hp.wf'
  obtain ⟨hs₀Gt, hS, -, -⟩ := case2_facts hp hs
  have h := (hp.prefixExt_right s₀).step_of_next hs₀Gt (case2_nextEv_s₀ hp hs hs₀)
    fun a ha => by
      rw [prefixExt_events hp.events_subset]
      exact Finset.mem_union_right _ (mem_pred.mpr ⟨(hGt.mem_of_porfStep ha).1,
        TransGen.single ha⟩)
  rwa [hGt.rf_none (Or.inr (Lab.IsSend.not_isRecv hS)),
    hGt.nd_none (Or.inr (Lab.IsSend.not_isND hS))] at h

/-- The events of `G_p + s₀`. -/
theorem case2_events₁ (hp : Pfx M P Gs Gt) (s₀ : Ev Q) :
    ((prefixExt Gs Gt s₀).addSend s₀).events = insert s₀ (Gs.events ∪ Gt.pred s₀) := by
  rw [add_events, prefixExt_events hp.events_subset]

/-- `e` is the next event of its thread in `G_p + s₀`. -/
theorem case2_nextEv_e (hp : Pfx M P Gs Gt) (hn : P.nextEv Gs e.tid = some e) (he : e ∈ Gt.events)
    (hs : Gt.rf e = some (.snd s₀)) (hs₀ : s₀ ∉ Gs.events) :
    P.nextEv ((prefixExt Gs Gt s₀).addSend s₀) e.tid = some e := by
  have hGt := hp.wf'
  obtain ⟨hs₀Gt, hS, -, hne⟩ := case2_facts hp hs
  have hidx := Model.idx_of_nextEv hn
  have heGs := hp.wf.not_mem_of_idx_eq_cnt hidx
  have hrf : Gt.porfStep s₀ e := Or.inr ⟨he, hs⟩
  have heq : (prefixExt Gs Gt s₀).addSend s₀ =
      Gt.restrict (insert s₀ (prefixExt Gs Gt s₀).events) := by
    have := (hp.prefixExt_right s₀).add_eq hs₀Gt
    rwa [hGt.rf_none (Or.inr (Lab.IsSend.not_isRecv hS)),
      hGt.nd_none (Or.inr (Lab.IsSend.not_isND hS))] at this
  rw [heq, prefixExt_events hp.events_subset]
  refine nextEv_restrict hGt hp.exec' he ?_ (fun a ha => ?_) (fun b hb hpo => ?_)
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hne h.symm
    rcases Finset.mem_union.mp h with h | h
    · exact heGs h
    · exact hGt.porf_irrefl e (TransGen.tail (mem_pred.mp h).2 hrf)
  · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
      (mem_of_po_next hp.wf hGt hp.events_subset hidx ha))
  · rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hGt.porf_irrefl e (TransGen.head (Or.inl hpo) (TransGen.single hrf))
    rcases Finset.mem_union.mp hb with hb | hb
    · have h := (closed_iff_porf Gt Gs.events).mp hp.closed (TransGen.single (Or.inl hpo))
        (Finset.mem_inter.mpr ⟨hpo.2.1, hb⟩)
      exact heGs (Finset.mem_inter.mp h).2
    · exact hGt.porf_irrefl e
        (TransGen.head (Or.inl hpo) (TransGen.tail (mem_pred.mp hb).2 hrf))

/-- Case 2, second step: `G_p + s₀ → G_p + s₀ + e@s₀` is an operational step, and
`G' = G_p + s₀ + e@s₀ ⊑ Gt`. -/
theorem case2_step₂ (hp : Pfx M P Gs Gt) (hn : P.nextEv Gs e.tid = some e) (he : e ∈ Gt.events)
    (hs : Gt.rf e = some (.snd s₀)) (hs₀ : s₀ ∉ Gs.events) :
    OpAdd M P ((prefixExt Gs Gt s₀).addSend s₀) e (some (.snd s₀)) none ∧
      Pfx M P (revTarget Gs Gt s₀ e) Gt := by
  have hGt := hp.wf'
  obtain ⟨-, -, hR, -⟩ := case2_facts hp hs
  have hidx := Model.idx_of_nextEv hn
  have h := (case2_step₁ hp hs hs₀).2.step_of_next he (case2_nextEv_e hp hn he hs hs₀)
    fun a ha => by
      rw [case2_events₁ hp s₀]
      rcases porfStep_next hp hidx ha with h | h
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ h)
      · rw [hs] at h
        cases h
        exact Finset.mem_insert_self _ _
  rw [hs, hGt.nd_none (Or.inr (Lab.IsRecv.not_isND hR))] at h
  exact h

/-- The events of `G'`: `G' = Gt|(Gs.E ∪ Gt.pred s₀ ∪ {s₀, e})`. -/
theorem revTarget_eq (hp : Pfx M P Gs Gt) (he : e ∈ Gt.events) (hs : Gt.rf e = some (.snd s₀))
    (hs₀ : s₀ ∉ Gs.events) :
    revTarget Gs Gt s₀ e = Gt.restrict (insert e (insert s₀ (Gs.events ∪ Gt.pred s₀))) := by
  have hGt := hp.wf'
  obtain ⟨-, -, hR, -⟩ := case2_facts hp hs
  have := (case2_step₁ hp hs hs₀).2.add_eq he
  rw [hs, hGt.nd_none (Or.inr (Lab.IsRecv.not_isND hR)), case2_events₁ hp s₀] at this
  exact this

theorem revTarget_events (hp : Pfx M P Gs Gt) (s₀ e : Ev Q) :
    (revTarget Gs Gt s₀ e).events = insert e (insert s₀ (Gs.events ∪ Gt.pred s₀)) := by
  unfold revTarget
  rw [add_events, case2_events₁ hp s₀]

/-- `Gs ⊏ G'`. -/
theorem case2_sPfx (hp : Pfx M P Gs Gt) (hn : P.nextEv Gs e.tid = some e) (he : e ∈ Gt.events)
    (hs : Gt.rf e = some (.snd s₀)) (hs₀ : s₀ ∉ Gs.events) :
    SPfx M P Gs (revTarget Gs Gt s₀ e) := by
  have h2 := (case2_step₂ hp hn he hs hs₀).2
  have hev := revTarget_events hp s₀ e
  refine sPfx_iff_exists.mpr ⟨Pfx.of_between hp h2 ?_, e, ?_, ?_⟩
  · rw [hev]
    exact fun x hx => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ hx))
  · rw [hev]
    exact Finset.mem_insert_self _ _
  · exact hp.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv hn)

/-- Minimality in Case 2, stronger than printed: every `G''` with `Gs ⊑ G'' ⊑ G'` and
`e ∈ G''.E` is `G'`. -/
theorem revTarget_minimal (hp : Pfx M P Gs Gt) (hn : P.nextEv Gs e.tid = some e)
    (he : e ∈ Gt.events) (hs : Gt.rf e = some (.snd s₀)) (hs₀ : s₀ ∉ Gs.events)
    (h₁ : Pfx M P Gs G'') (h₂ : Pfx M P G'' (revTarget Gs Gt s₀ e))
    (heG : e ∈ G''.events) : G'' = revTarget Gs Gt s₀ e := by
  have hGt := hp.wf'
  have hG' := (case2_step₂ hp hn he hs hs₀).2
  have hev := revTarget_events hp s₀ e
  have hcl := (closed_iff_porf _ G''.events).mp h₂.closed
  have he' : e ∈ (revTarget Gs Gt s₀ e).events := by rw [hev]; exact Finset.mem_insert_self _ _
  have hs₀' : s₀ ∈ (revTarget Gs Gt s₀ e).events := by
    rw [hev]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hrf' : (revTarget Gs Gt s₀ e).rfRel s₀ e := ⟨he', by rw [hG'.rf_eq he']; exact hs⟩
  have hs₀G : s₀ ∈ G''.events :=
    (Finset.mem_inter.mp (hcl (TransGen.single (Or.inr hrf')) (Finset.mem_inter.mpr
      ⟨he', heG⟩))).2
  refine h₂.eq_of_subset fun x hx => ?_
  rw [hev] at hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact heG
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hs₀G
  rcases Finset.mem_union.mp hx with hx | hx
  · exact h₁.events_subset hx
  · have hxs := (hG'.pre.porf_iff hs₀').mpr (mem_pred.mp hx).2
    exact (Finset.mem_inter.mp (hcl hxs (Finset.mem_inter.mpr ⟨hs₀', hs₀G⟩))).2

/-- Minimality in Case 2 as printed: there is no `G''` with `e ∈ G''.E` and
`Gs ⊏ G'' ⊏ G'`. -/
theorem revTarget_no_between (hp : Pfx M P Gs Gt) (hn : P.nextEv Gs e.tid = some e)
    (he : e ∈ Gt.events) (hs : Gt.rf e = some (.snd s₀)) (hs₀ : s₀ ∉ Gs.events) :
    ¬ ∃ G'', e ∈ G''.events ∧ SPfx M P Gs G'' ∧ SPfx M P G'' (revTarget Gs Gt s₀ e) := by
  rintro ⟨G'', heG, h₁, h₂⟩
  exact h₂.2 (revTarget_minimal hp hn he hs hs₀ h₁.1 h₂.1 heG)

/-- Lemma A.14, Case 2 (repaired): `e` is a receive reading `s₀ ∉ Gs` in `Gt`. With
`G_p = PrefixExtension(Gs, Gt, s₀)`: `G_p → G_p + s₀ → G_p + s₀ + e@s₀ = G'` are operational
steps, `G' ⊑ Gt`, `Gs ⊏ G'`, and there is no `G''` with `e ∈ G''.E` and `Gs ⊏ G'' ⊏ G'`. -/
theorem next_prefix_case2 (hp : Pfx M P Gs Gt) (hn : P.nextEv Gs e.tid = some e)
    (he : e ∈ Gt.events) (hs : Gt.rf e = some (.snd s₀)) (hs₀ : s₀ ∉ Gs.events) :
    e.IsRecv ∧ OpAdd M P (prefixExt Gs Gt s₀) s₀ none none ∧
      OpAdd M P ((prefixExt Gs Gt s₀).addSend s₀) e (some (.snd s₀)) none ∧
      Pfx M P (revTarget Gs Gt s₀ e) Gt ∧ SPfx M P Gs (revTarget Gs Gt s₀ e) ∧
      ¬ ∃ G'', e ∈ G''.events ∧ SPfx M P Gs G'' ∧ SPfx M P G'' (revTarget Gs Gt s₀ e) :=
  ⟨(case2_facts hp hs).2.2.1, (case2_step₁ hp hs hs₀).1, (case2_step₂ hp hn he hs hs₀).1,
    (case2_step₂ hp hn he hs hs₀).2, case2_sPfx hp hn he hs hs₀,
    revTarget_no_between hp hn he hs hs₀⟩

/-! ### Lemma A.14 -/

/-- Lemma A.14 for the next event of a thread of `Gs ⊑ Gt` that is an event of `Gt`: Case 1 or
Case 2 (exclusive: `case1_iff`). -/
theorem next_prefix_of_nextEv (hp : Pfx M P Gs Gt) (hn : P.nextEv Gs e.tid = some e)
    (he : e ∈ Gt.events) :
    ((∀ s, Gt.rf e = some (.snd s) → s ∈ Gs.events) ∧
      OpAdd M P Gs e (Gt.rf e) (Gt.nd e) ∧ Pfx M P (Gs.add e (Gt.rf e) (Gt.nd e)) Gt) ∨
    (∃ s₀, Gt.rf e = some (.snd s₀) ∧ s₀ ∉ Gs.events ∧ e.IsRecv ∧
      OpAdd M P (prefixExt Gs Gt s₀) s₀ none none ∧
      OpAdd M P ((prefixExt Gs Gt s₀).addSend s₀) e (some (.snd s₀)) none ∧
      Pfx M P (revTarget Gs Gt s₀ e) Gt ∧ SPfx M P Gs (revTarget Gs Gt s₀ e) ∧
      ¬ ∃ G'', e ∈ G''.events ∧ SPfx M P Gs G'' ∧ SPfx M P G'' (revTarget Gs Gt s₀ e)) := by
  by_cases h : ∀ s, Gt.rf e = some (.snd s) → s ∈ Gs.events
  · exact Or.inl ⟨h, next_prefix_case1 hp hn he h⟩
  · push Not at h
    obtain ⟨s₀, hs, hs₀⟩ := h
    exact Or.inr ⟨s₀, hs, hs₀, next_prefix_case2 hp hn he hs hs₀⟩

/-- Lemma A.14 with the plan's repaired signature (`LEAN-PLAN.md` Section 2b): `Gs ⊏ Gt`
consistent executions, `e = next_P(Gs) ∈ Gt.E`. Case 1 (the outcome of `e` in `Gt` is available
in `Gs`): one operational step `Gs → G'` with that outcome and `G' ⊑ Gt`. Case 2 (`e` a receive
whose source `s₀` in `Gt` is not in `Gs`): with `G_p := PrefixExtension(Gs, Gt, s₀)`, adding `s₀`
and then `e` with source `s₀` are operational steps giving `G' ⊑ Gt`, and there is no `G''` with
`e ∈ G''.E` and `Gs ⊏ G'' ⊏ G'`. -/
theorem next_prefix (hp : SPfx M P Gs Gt) (hn : M.nextP P Gs = some e) (he : e ∈ Gt.events) :
    ((∀ s, Gt.rf e = some (.snd s) → s ∈ Gs.events) ∧
      OpAdd M P Gs e (Gt.rf e) (Gt.nd e) ∧ Pfx M P (Gs.add e (Gt.rf e) (Gt.nd e)) Gt) ∨
    (∃ s₀, Gt.rf e = some (.snd s₀) ∧ s₀ ∉ Gs.events ∧ e.IsRecv ∧
      OpAdd M P (prefixExt Gs Gt s₀) s₀ none none ∧
      OpAdd M P ((prefixExt Gs Gt s₀).addSend s₀) e (some (.snd s₀)) none ∧
      Pfx M P (revTarget Gs Gt s₀ e) Gt ∧ SPfx M P Gs (revTarget Gs Gt s₀ e) ∧
      ¬ ∃ G'', e ∈ G''.events ∧ SPfx M P Gs G'' ∧ SPfx M P G'' (revTarget Gs Gt s₀ e)) :=
  next_prefix_of_nextEv hp.1 (nextEv_of_nextP hn) he

/-- Lemma A.14 with the printed hypothesis `e ∈ avail(Gs) ∩ Gt.E` (and `Gs ⊑ Gt`). -/
theorem next_prefix_avail (hp : Pfx M P Gs Gt) (hav : e ∈ M.availM P Gs) (he : e ∈ Gt.events) :
    ((∀ s, Gt.rf e = some (.snd s) → s ∈ Gs.events) ∧
      OpAdd M P Gs e (Gt.rf e) (Gt.nd e) ∧ Pfx M P (Gs.add e (Gt.rf e) (Gt.nd e)) Gt) ∨
    (∃ s₀, Gt.rf e = some (.snd s₀) ∧ s₀ ∉ Gs.events ∧ e.IsRecv ∧
      OpAdd M P (prefixExt Gs Gt s₀) s₀ none none ∧
      OpAdd M P ((prefixExt Gs Gt s₀).addSend s₀) e (some (.snd s₀)) none ∧
      Pfx M P (revTarget Gs Gt s₀ e) Gt ∧ SPfx M P Gs (revTarget Gs Gt s₀ e) ∧
      ¬ ∃ G'', e ∈ G''.events ∧ SPfx M P Gs G'' ∧ SPfx M P G'' (revTarget Gs Gt s₀ e)) :=
  next_prefix_of_nextEv hp (nextEv_of_mem_availM hav) he

/-! ### Facts for `GetNext` (M7) and optimality (M8) -/

/-- Case 2: `s₀` is read by no receive of `G_p = PrefixExtension(Gs, Gt, s₀)`, and it is an unread
send of `G_p + s₀`. -/
theorem case2_unread (hp : Pfx M P Gs Gt) (hn : P.nextEv Gs e.tid = some e)
    (hs : Gt.rf e = some (.snd s₀)) :
    (∀ q ∈ (prefixExt Gs Gt s₀).events, (prefixExt Gs Gt s₀).rf q ≠ some (.snd s₀)) ∧
      s₀ ∈ ((prefixExt Gs Gt s₀).addSend s₀).US := by
  have hGt := hp.wf'
  obtain ⟨-, hS, -, -⟩ := case2_facts hp hs
  have he := (hGt.rf_some hs).1
  have heGp : e ∉ (prefixExt Gs Gt s₀).events := by
    rw [mem_prefixExt hp.events_subset]
    rintro (h | ⟨-, h⟩)
    · exact hp.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv hn) h
    · exact hGt.porf_irrefl e (TransGen.tail h (Or.inr ⟨he, hs⟩))
  have h1 : ∀ q ∈ (prefixExt Gs Gt s₀).events, (prefixExt Gs Gt s₀).rf q ≠ some (.snd s₀) := by
    intro q hq h
    rw [prefixExt_rf hq] at h
    exact heGp (hGt.rf_once _ _ _ h hs ▸ hq)
  refine ⟨h1, (Graph.mem_US _).mpr ⟨Finset.mem_insert_self _ _, hS, fun q hq h => ?_⟩⟩
  by_cases hqs : q = s₀
  · rw [hqs, add_rf, Function.update_self] at h
    cases h
  · rw [add_rf, Function.update_of_ne hqs] at h
    rcases Finset.mem_insert.mp hq with hq | hq
    · exact hqs hq
    · exact h1 q hq h

/-- Case 2: `r₀ = e` is the next event of its thread already in `G_p`. -/
theorem case2_nextEv_e_Gp (hp : Pfx M P Gs Gt) (hn : P.nextEv Gs e.tid = some e)
    (hs : Gt.rf e = some (.snd s₀)) : P.nextEv (prefixExt Gs Gt s₀) e.tid = some e := by
  have hGt := hp.wf'
  have he := (hGt.rf_some hs).1
  have hidx := Model.idx_of_nextEv hn
  have heGs := hp.wf.not_mem_of_idx_eq_cnt hidx
  have hrf : Gt.porfStep s₀ e := Or.inr ⟨he, hs⟩
  refine nextEv_restrict hGt hp.exec' he ?_ (fun a ha => ?_) (fun b hb hpo => ?_)
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · exact heGs h
    · exact hGt.porf_irrefl e (TransGen.tail (mem_pred.mp h).2 hrf)
  · exact Finset.mem_union_left _ (mem_of_po_next hp.wf hGt hp.events_subset hidx ha)
  · rcases Finset.mem_union.mp hb with hb | hb
    · have h := (closed_iff_porf Gt Gs.events).mp hp.closed (TransGen.single (Or.inl hpo))
        (Finset.mem_inter.mpr ⟨hpo.2.1, hb⟩)
      exact heGs (Finset.mem_inter.mp h).2
    · exact hGt.porf_irrefl e
        (TransGen.head (Or.inl hpo) (TransGen.tail (mem_pred.mp hb).2 hrf))

/-- Case 2: `G' = revTarget Gs Gt s₀ e` is below every `G''` with `Gs ⊑ G'' ⊑ Gt` and
`e ∈ G''.E`. -/
theorem revTarget_least (hp : Pfx M P Gs Gt) (hn : P.nextEv Gs e.tid = some e)
    (he : e ∈ Gt.events) (hs : Gt.rf e = some (.snd s₀)) (hs₀ : s₀ ∉ Gs.events)
    (h₁ : Pfx M P Gs G'') (h₂ : Pfx M P G'' Gt) (heG : e ∈ G''.events) :
    Pfx M P (revTarget Gs Gt s₀ e) G'' := by
  refine Pfx.of_between (case2_step₂ hp hn he hs hs₀).2 h₂ ?_
  have hcl := (closed_iff_porf Gt G''.events).mp h₂.closed
  have hs₀G : s₀ ∈ G''.events := (Finset.mem_inter.mp (hcl (TransGen.single (Or.inr ⟨he, hs⟩))
    (Finset.mem_inter.mpr ⟨he, heG⟩))).2
  rw [revTarget_events hp s₀ e]
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact heG
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hs₀G
  rcases Finset.mem_union.mp hx with hx | hx
  · exact h₁.events_subset hx
  · exact (Finset.mem_inter.mp (hcl (mem_pred.mp hx).2
      (Finset.mem_inter.mpr ⟨(case2_facts hp hs).1, hs₀G⟩))).2

/-- Lemma A.14 in the form `GetNext`'s specification uses: for `Gs ⊏ Gt` and
`e = next_P(Gs) ∈ Gt.E`, the graph `G'` produced (Case 1: `Gs + e` with the outcome of `Gt`;
Case 2: `revTarget Gs Gt s₀ e`) satisfies `G' ⊑ Gt`, `Gs ⊏ G'` and contains `next_P(Gs)`. -/
theorem next_prefix_result (hp : SPfx M P Gs Gt) (hn : M.nextP P Gs = some e)
    (he : e ∈ Gt.events) :
    ∃ G', Pfx M P G' Gt ∧ SPfx M P Gs G' ∧ e ∈ G'.events ∧
      (((∀ s, Gt.rf e = some (.snd s) → s ∈ Gs.events) ∧ OpAdd M P Gs e (Gt.rf e) (Gt.nd e) ∧
          G' = Gs.add e (Gt.rf e) (Gt.nd e)) ∨
        (∃ s₀, Gt.rf e = some (.snd s₀) ∧ s₀ ∉ Gs.events ∧ G' = revTarget Gs Gt s₀ e)) := by
  rcases next_prefix hp hn he with ⟨hc, h1, h2⟩ | ⟨s₀, hs, hs₀, -, -, -, h3, h4, -⟩
  · have heGs := hp.1.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv (nextEv_of_nextP hn))
    refine ⟨_, h2, sPfx_iff_exists.mpr ⟨Pfx.of_between hp.1 h2
      (fun x hx => Finset.mem_insert_of_mem hx), e, Finset.mem_insert_self _ _, heGs⟩,
      Finset.mem_insert_self _ _, Or.inl ⟨hc, h1, rfl⟩⟩
  · refine ⟨_, h3, h4, ?_, Or.inr ⟨s₀, hs, hs₀, rfl⟩⟩
    rw [revTarget_events hp.1 s₀ e]
    exact Finset.mem_insert_self _ _

end Must

#print axioms Must.getSend_source_graph
#print axioms Must.Pfx.add_eq
#print axioms Must.Pfx.step_of_next
#print axioms Must.next_prefix_case1
#print axioms Must.case1_unique
#print axioms Must.case1_iff
#print axioms Must.case2_nextEv_s₀
#print axioms Must.case2_step₁
#print axioms Must.case2_nextEv_e
#print axioms Must.case2_step₂
#print axioms Must.revTarget_eq
#print axioms Must.case2_sPfx
#print axioms Must.revTarget_minimal
#print axioms Must.revTarget_no_between
#print axioms Must.next_prefix_case2
#print axioms Must.next_prefix_of_nextEv
#print axioms Must.next_prefix
#print axioms Must.next_prefix_avail
#print axioms Must.case2_unread
#print axioms Must.case2_nextEv_e_Gp
#print axioms Must.revTarget_least
#print axioms Must.next_prefix_result
