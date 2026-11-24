import Mazurkiewicz.Must.GetNextSpec

/-!
# The revisit of line 23 is an algorithmic step (milestone M7)

Paper: Algorithm 2, lines 22–23; Lemma A.16 ⟨3⟩4 (p. 33: "the revisit step `s₀@− ⇒rv r₀` will
thus be enabled, and the resulting execution will be `G_n = G_p`", repaired to
`G_n = G_p + s₀ + r₀`). Plan: Q15, the addenda after M5 (closure conjunct of
`revCond_iff_replay`) and after M6 (all obligations of `StepM.revisit`; the list equation; no
lemma assumes that sources precede their readers).

Setting: Case 2 of `GetNext(c₀.G, Gt)` (`Ctx`), the loop at its break: `LoopInv` at `(c, A, X)`
and `next_P(c.G) = s₀`. `H := c.add s₀` is the configuration in which Algorithm 1 tests the
revisit of `r₀` by `s₀`.

* `brk_pfx_H` (`G ⊑ H`), `brk_Y` (`G_p + s₀ ⊑ H`), `brk_porf`, `brk_porf'`: the causal
  predecessors of `s₀` in `H` are events of `G_p`, and every event of `G_p \ G_s` is one.
* `del_iff` (Q15's `Deleted` is `A \ {r₀}`), `base_eq` (the replay base `K` is `G_p.E`),
  `delList_eq` (the list equation `r₀ :: H.delList r₀ s₀ = A`: the list replayed by the revisit
  condition is the deferred list; its order is the insertion order).
* `revGuard`: every guard of `StepM.revisit`: `r₀ ∈ H`, `r₀` a receive, matching, `(r₀, s₀) ∉
  H.porf`, `RevisitCondition(H, e, s₀)` for `e ∈ Deleted ∪ {r₀}` (by `revCond_iff_replay_step`:
  the closure conjunct `H.Closed K` holds because `K = G_p.E` and `G_p ⊑ H`; the replay conjunct
  is `MaxCompletion(G_p, A) = G`), and `RevisitCondition(H, s₀, s₀)`.
* `revisit_graph`: the graph of the revisit successor is `G_n = AddRecv(Add(G_p, s₀), r₀, s₀)`
  (`revTarget`); `stepM_revisit`: the revisit is a `StepM` step (the scheduler's choice is
  `next_P(c.G) = s₀`; the successor is consistent since `G_n ⊑ G_t`); `revisit_order`: the
  insertion order of the successor starts with `c₀.order ++ [r₀]`.

Every result holds for every model `M` and every tie-break with `TieQ9 M tie`.
-/

namespace Must

open Graph Relation Config

variable {Q : Type} [DecidableEq Q] [Membership Val Q]
variable {M : Model Q} {P : Program Q} {tie : Tie Q}

namespace LoopInv

variable {c₀ c : Config Q} {Gt X : Graph Q} {r₀ s₀ : Ev Q} {A : List (Ev Q)}

/-- `G ⊑ H = G + s₀`. -/
theorem brk_pfx_H (hx : Ctx M P c₀ Gt r₀ s₀) (hI : LoopInv M tie P c₀ Gt r₀ s₀ c A X)
    (hn : M.nextP P c.G = some s₀) : Pfx M P c.G (c.add s₀ none none).G := by
  have hS := hx.facts.2.1
  have hHi := hI.inv.addSend (nextEv_of_nextP hn) hS
  refine pfx_iff_opLe.mpr ⟨hI.inv.cons, hHi.cons, hHi.exec, ReflTransGen.single
    ⟨s₀, none, none, ⟨Model.mem_availM_of_nextP hn, Or.inr (Or.inr ⟨Lab.IsSend.not_isRecv hS,
      Lab.IsSend.not_isND hS, rfl, rfl⟩), hHi.cons⟩, rfl⟩⟩

/-- `G_p ⊑ G` at the break. -/
theorem brk_gp (hT : TieQ9 M tie) (hx : Ctx M P c₀ Gt r₀ s₀)
    (hI : LoopInv M tie P c₀ Gt r₀ s₀ c A X) (hn : M.nextP P c.G = some s₀) :
    Pfx M P (prefixExt c₀.G Gt s₀) c.G := by
  rw [hI.eq_of_brk hx hT hn]
  exact hI.gp_pfx hx hT

/-- `G_p + s₀ ⊑ H`. -/
theorem brk_Y (hT : TieQ9 M tie) (hx : Ctx M P c₀ Gt r₀ s₀)
    (hI : LoopInv M tie P c₀ Gt r₀ s₀ c A X) (hn : M.nextP P c.G = some s₀) :
    Pfx M P ((prefixExt c₀.G Gt s₀).addSend s₀) (c.add s₀ none none).G := by
  have hGpH := (hI.brk_gp hT hx hn).trans (hI.brk_pfx_H hx hn)
  have hidx : s₀.idx = c.G.cnt s₀.tid := Model.idx_of_nextEv (nextEv_of_nextP hn)
  have h := hGpH.step_of_next (x := s₀) (Finset.mem_insert_self _ _) hx.nextEv_s₀
    fun a ha => by
      rcases (hI.inv.wf.porfStep_add_right_iff (src := none) (out := none) hidx).mp ha with
        ⟨ha, hat⟩ | h
      · exact hI.thr_sub hx hT ha hat
      · cases h
  have e1 : (c.add s₀ none none).G.rf s₀ = none := by
    change (c.G.add s₀ none none).rf s₀ = none
    simp
  have e2 : (c.add s₀ none none).G.nd s₀ = none := by
    change (c.G.add s₀ none none).nd s₀ = none
    simp
  rw [e1, e2] at h
  exact h.2

/-- A causal predecessor of `s₀` in `H` is an event of `G_p`. -/
theorem brk_porf (hT : TieQ9 M tie) (hx : Ctx M P c₀ Gt r₀ s₀)
    (hI : LoopInv M tie P c₀ Gt r₀ s₀ c A X) (hn : M.nextP P c.G = some s₀) {x : Ev Q}
    (h : (c.add s₀ none none).G.porf x s₀) : x ∈ (prefixExt c₀.G Gt s₀).events := by
  have hY := hI.brk_Y hT hx hn
  have hs₀Y : s₀ ∈ ((prefixExt c₀.G Gt s₀).addSend s₀).events := Finset.mem_insert_self _ _
  have := (closed_iff_porf _ _).mp hY.closed h
    (Finset.mem_inter.mpr ⟨hY.events_subset hs₀Y, hs₀Y⟩)
  rcases Finset.mem_insert.mp (Finset.mem_inter.mp this).2 with rfl | h'
  · exact absurd h (hY.wf'.porf_irrefl _)
  · exact h'

/-- Every event of `G_p \ G_s` is a causal predecessor of `s₀` in `H`. -/
theorem brk_porf' (hT : TieQ9 M tie) (hx : Ctx M P c₀ Gt r₀ s₀)
    (hI : LoopInv M tie P c₀ Gt r₀ s₀ c A X) (hn : M.nextP P c.G = some s₀) {x : Ev Q}
    (hxGp : x ∈ (prefixExt c₀.G Gt s₀).events) (hxc₀ : x ∉ c₀.G.events) :
    (c.add s₀ none none).G.porf x s₀ := by
  obtain ⟨-, hxs⟩ := ((mem_prefixExt hx.dom.pfx.events_subset).mp hxGp).resolve_left hxc₀
  have hYGt := (case2_step₁ hx.dom.pfx hx.src hx.nmem).2
  have hs₀Y : s₀ ∈ ((prefixExt c₀.G Gt s₀).addSend s₀).events := Finset.mem_insert_self _ _
  exact (hI.brk_Y hT hx hn).pre.porf_le ((hYGt.pre.porf_iff hs₀Y).mpr hxs)

/-- Q15's `Deleted` for the revisit of `r₀` by `s₀` in `H` is `A \ {r₀}`. -/
theorem del_iff (hT : TieQ9 M tie) (hx : Ctx M P c₀ Gt r₀ s₀)
    (hI : LoopInv M tie P c₀ Gt r₀ s₀ c A X) (hn : M.nextP P c.G = some s₀) {x : Ev Q} :
    x ∈ (c.add s₀ none none).del r₀ s₀ ↔ x ∈ A ∧ x ≠ r₀ := by
  have hcX := hI.eq_of_brk hx hT hn
  have hHi := hI.inv.addSend (nextEv_of_nextP hn) hx.facts.2.1
  have hpos : ∀ y ∈ (c.add s₀ none none).G.events, ((c.add s₀ none none).pos r₀ <
      (c.add s₀ none none).pos y ↔ y ∉ c₀.G.events ∧ y ≠ r₀) := by
    intro y hy
    have hpre : c₀.order ++ [r₀] <+: (c.add s₀ none none).order :=
      hI.ord.trans (List.prefix_append c.order [s₀])
    unfold Config.pos
    rw [idxOf_lt_iff_of_prefix hHi.nodup hpre ((hHi.mem y).mpr hy), hx.dom.inv.mem]
  rw [mem_del]
  constructor
  · rintro ⟨hxH, hxs, hpx, hnp⟩
    have hxc : x ∈ c.G.events := (Finset.mem_insert.mp hxH).resolve_left hxs
    obtain ⟨hxc₀, hxr⟩ := (hpos x hxH).mp hpx
    rw [hcX] at hxc
    rcases (hI.mem_X).mp hxc with h | h
    · exact absurd (hI.brk_porf' hT hx hn h hxc₀) hnp
    · exact ⟨h, hxr⟩
  · rintro ⟨hxA, hxr⟩
    have hxc := hI.sub x hxA
    have hxH : x ∈ (c.add s₀ none none).G.events := Finset.mem_insert_of_mem hxc
    refine ⟨hxH, fun h => hI.ns₀ (h ▸ hxc), (hpos x hxH).mpr ⟨fun h => hI.disj x hxA
      (hx.gp_left.events_subset h), hxr⟩, fun h => hI.disj x hxA (hI.brk_porf hT hx hn h)⟩

/-- The replay base `K` of the revisit is `G_p.E`. -/
theorem base_eq (hT : TieQ9 M tie) (hx : Ctx M P c₀ Gt r₀ s₀)
    (hI : LoopInv M tie P c₀ Gt r₀ s₀ c A X) (hn : M.nextP P c.G = some s₀) :
    (c.add s₀ none none).base r₀ s₀ = (prefixExt c₀.G Gt s₀).events := by
  have hcX := hI.eq_of_brk hx hT hn
  have hGpc := hI.brk_gp hT hx hn
  ext x
  rw [mem_base, hI.del_iff hT hx hn]
  constructor
  · rintro ⟨hxH, hxr, hxs, hxd⟩
    have hxc : x ∈ c.G.events := (Finset.mem_insert.mp hxH).resolve_left hxs
    rw [hcX] at hxc
    rcases (hI.mem_X).mp hxc with h | h
    · exact h
    · exact absurd ⟨h, hxr⟩ hxd
  · intro h
    refine ⟨Finset.mem_insert_of_mem (hGpc.events_subset h), fun e => hx.r₀_not_mem (e ▸ h),
      fun e => hx.s₀_not_mem (e ▸ h), fun hd => hI.disj x hd.1 h⟩

/-- The list equation: `r₀ :: H.delList r₀ s₀ = A`. -/
theorem delList_eq (hT : TieQ9 M tie) (hx : Ctx M P c₀ Gt r₀ s₀)
    (hI : LoopInv M tie P c₀ Gt r₀ s₀ c A X) (hn : M.nextP P c.G = some s₀) :
    r₀ :: (c.add s₀ none none).delList r₀ s₀ = A := by
  obtain ⟨A'', hA⟩ := hI.head
  have hnd := hI.nodup
  rw [hA] at hnd
  have hr₀ : r₀ ∉ A'' := (List.nodup_cons.mp hnd).1
  have hdel := fun x => hI.del_iff hT hx hn (x := x)
  have hs₀d : s₀ ∉ (c.add s₀ none none).del r₀ s₀ := fun h =>
    hI.ns₀ (hI.sub s₀ ((hdel s₀).mp h).1)
  unfold Config.delList
  change r₀ :: (c.order ++ [s₀]).filter (fun d => decide (d ∈ (c.add s₀ none none).del r₀ s₀)) = A
  have h1 : c.order.filter (fun d => decide (d ∈ (c.add s₀ none none).del r₀ s₀)) =
      (c.order.filter (fun x => decide (x ∈ A))).filter (fun x => decide (x ≠ r₀)) := by
    rw [List.filter_filter]
    exact List.filter_congr fun x _ => by simp [hdel x, and_comm]
  rw [List.filter_append, h1, hI.filt, hA, List.filter_cons_of_neg (by simp)]
  have h2 : A''.filter (fun x => decide (x ≠ r₀)) = A'' :=
    List.filter_eq_self.mpr fun x hxA => by
      simp only [ne_eq, decide_eq_true_eq]
      rintro rfl
      exact hr₀ hxA
  rw [h2]
  simp [hs₀d]

/-- Every guard of the revisit of `r₀` by `s₀` (`RevGuard`, Q15) holds in `H`. -/
theorem revGuard (hT : TieQ9 M tie) (hx : Ctx M P c₀ Gt r₀ s₀)
    (hI : LoopInv M tie P c₀ Gt r₀ s₀ c A X) (hn : M.nextP P c.G = some s₀) :
    RevGuard tie (c.add s₀ none none) r₀ s₀ := by
  have hcX := hI.eq_of_brk hx hT hn
  have hGpH := (hI.brk_gp hT hx hn).trans (hI.brk_pfx_H hx hn)
  have hr : r₀ ∈ (c.add s₀ none none).G.events := Finset.mem_insert_of_mem (hI.sub r₀ hI.r₀_mem)
  have hnp : ¬ (c.add s₀ none none).G.porf r₀ s₀ :=
    fun h => hx.r₀_not_mem (hI.brk_porf hT hx hn h)
  have hrestr : (c.add s₀ none none).G.restrict ((c.add s₀ none none).base r₀ s₀) =
      prefixExt c₀.G Gt s₀ := by
    rw [hI.base_eq hT hx hn]
    exact hGpH.eq_restrict.symm
  have hcl : (c.add s₀ none none).G.Closed ((c.add s₀ none none).base r₀ s₀) := by
    rw [hI.base_eq hT hx hn]
    exact hGpH.closed
  have hrep : Replay tie P ((c.add s₀ none none).G.restrict ((c.add s₀ none none).base r₀ s₀))
      (r₀ :: (c.add s₀ none none).delList r₀ s₀) c.G := by
    rw [hrestr, hI.delList_eq hT hx hn, hcX]
    exact hI.replay
  obtain ⟨hcond, hcs⟩ := (revCond_iff_replay_step hT hI.inv hn hx.facts.2.1 hr hx.facts.2.2.1
    hnp).mpr ⟨hcl, hrep⟩
  exact ⟨hr, hx.facts.2.2.1, hx.smatch, hnp, hcond, hcs⟩

/-- The graph of the revisit successor is `G_n = AddRecv(Add(G_p, s₀), r₀, s₀)` (line 22). -/
theorem revisit_graph (hT : TieQ9 M tie) (hx : Ctx M P c₀ Gt r₀ s₀)
    (hI : LoopInv M tie P c₀ Gt r₀ s₀ c A X) (hn : M.nextP P c.G = some s₀) :
    ((c.add s₀ none none).revisitCfg r₀ s₀).G = revTarget c₀.G Gt s₀ r₀ := by
  have hcX := hI.eq_of_brk hx hT hn
  have hGpc := hI.brk_gp hT hx hn
  have hg := hI.revGuard hT hx hn
  have hdel := fun x => hI.del_iff hT hx hn (x := x)
  have hHi := hI.inv.addSend (nextEv_of_nextP hn) hx.facts.2.1
  obtain ⟨hsH, hread, -⟩ := addSend_facts hI.inv (nextEv_of_nextP hn)
  have hw1 := revisit_wf hHi hsH hread hg
  have hn₂ := case2_step₂ hx.dom.pfx hx.nextEv hx.dom.mem hx.src hx.nmem
  have hw2 := hn₂.2.wf
  have hr₀c : r₀ ∈ c.G.events := hI.sub r₀ hI.r₀_mem
  have hr₀s₀ : r₀ ≠ s₀ := hx.facts.2.2.2.symm
  have hkept : ∀ x, x ∈ ((c.add s₀ none none).revisitCfg r₀ s₀).G.events ↔
      x = r₀ ∨ x = s₀ ∨ x ∈ (prefixExt c₀.G Gt s₀).events := by
    intro x
    rw [mem_revisitCfg_events, hdel]
    constructor
    · rintro ⟨hxH, hxd⟩
      rcases Finset.mem_insert.mp hxH with rfl | hxc
      · exact Or.inr (Or.inl rfl)
      · rw [hcX] at hxc
        rcases (hI.mem_X).mp hxc with h | h
        · exact Or.inr (Or.inr h)
        · by_cases hxr : x = r₀
          · exact Or.inl hxr
          · exact absurd ⟨h, hxr⟩ hxd
    · rintro (rfl | rfl | h)
      · exact ⟨Finset.mem_insert_of_mem hr₀c, fun h => h.2 rfl⟩
      · exact ⟨Finset.mem_insert_self _ _, fun h => hI.ns₀ (hI.sub _ h.1)⟩
      · exact ⟨Finset.mem_insert_of_mem (hGpc.events_subset h), fun hd => hI.disj x hd.1 h⟩
  have hev : (revTarget c₀.G Gt s₀ r₀).events =
      insert r₀ (insert s₀ (prefixExt c₀.G Gt s₀).events) := by
    rw [revTarget_events hx.dom.pfx, prefixExt_events hx.dom.pfx.events_subset]
  have hkeep : ∀ x, x ∈ ((c.add s₀ none none).revisitCfg r₀ s₀).G.events →
      x ∈ (c.add s₀ none none).G.events \ (c.add s₀ none none).del r₀ s₀ := fun x hx' =>
    Finset.mem_sdiff.mpr ((mem_revisitCfg_events).mp hx')
  refine hw1.ext hw2 ?_ (fun x hx' => ?_) (fun x hx' => ?_)
  · ext x
    rw [hkept, hev, Finset.mem_insert, Finset.mem_insert]
  · have hk := hkeep x hx'
    simp only [revisitCfg, Graph.revisit, restrict_rf, hk, ↓reduceIte, setRF_rf, revTarget, add_rf]
    by_cases hxr : x = r₀
    · subst hxr
      simp
    · rw [Function.update_of_ne hxr, Function.update_of_ne hxr]
      change (c.G.add s₀ none none).rf x = _
      rw [add_rf]
      by_cases hxs : x = s₀
      · subst hxs
        simp
      · rw [Function.update_of_ne hxs, Function.update_of_ne hxs]
        have hxGp : x ∈ (prefixExt c₀.G Gt s₀).events := by
          rcases (hkept x).mp hx' with h | h | h
          exacts [absurd h hxr, absurd h hxs, h]
        exact (hGpc.rf_eq hxGp).symm
  · have hk := hkeep x hx'
    simp only [revisitCfg, Graph.revisit, restrict_nd, hk, ↓reduceIte, setRF_nd, revTarget, add_nd]
    change (c.G.add s₀ none none).nd x = _
    rw [add_nd]
    by_cases hxr : x = r₀
    · subst hxr
      rw [Function.update_of_ne hr₀s₀, Function.update_self]
      exact hI.inv.wf.nd_none (Or.inr (Lab.IsRecv.not_isND hx.facts.2.2.1))
    · rw [Function.update_of_ne hxr]
      by_cases hxs : x = s₀
      · subst hxs
        simp
      · rw [Function.update_of_ne hxs, Function.update_of_ne hxs]
        have hxGp : x ∈ (prefixExt c₀.G Gt s₀).events := by
          rcases (hkept x).mp hx' with h | h | h
          exacts [absurd h hxr, absurd h hxs, h]
        exact (hGpc.nd_eq hxGp).symm

/-- The revisit of line 23 is an algorithmic step: `StepM.revisit` from `c` (the scheduler's
choice `next_P(c.G) = s₀`, a send, the guards, and a consistent successor). -/
theorem stepM_revisit (hT : TieQ9 M tie) (hx : Ctx M P c₀ Gt r₀ s₀)
    (hI : LoopInv M tie P c₀ Gt r₀ s₀ c A X) (hn : M.nextP P c.G = some s₀) :
    StepM M tie P c ((c.add s₀ none none).revisitCfg r₀ s₀) := by
  refine .revisit hn hx.facts.2.1 (hI.revGuard hT hx hn) ?_
  rw [hI.revisit_graph hT hx hn]
  exact (case2_step₂ hx.dom.pfx hx.nextEv hx.dom.mem hx.src hx.nmem).2.cons

/-- The insertion order of the revisit successor starts with `c₀.order ++ [r₀]`: the revisit
deletes no event of `G_s` and not `r₀`. -/
theorem revisit_order (hT : TieQ9 M tie) (hx : Ctx M P c₀ Gt r₀ s₀)
    (hI : LoopInv M tie P c₀ Gt r₀ s₀ c A X) (hn : M.nextP P c.G = some s₀) :
    c₀.order ++ [r₀] <+: ((c.add s₀ none none).revisitCfg r₀ s₀).order := by
  have hdel := fun x => hI.del_iff hT hx hn (x := x)
  obtain ⟨L, hL⟩ := hI.ord
  have hkeep : (c₀.order ++ [r₀]).filter
      (fun d => decide (d ∉ (c.add s₀ none none).del r₀ s₀ ∧ d ≠ s₀)) = c₀.order ++ [r₀] := by
    refine List.filter_eq_self.mpr fun x hx' => ?_
    rcases List.mem_append.mp hx' with h | h
    · have hxc₀ : x ∈ c₀.G.events := (hx.dom.inv.mem x).mp h
      simp only [decide_eq_true_eq]
      exact ⟨fun hd => hI.disj x ((hdel x).mp hd).1 (hx.gp_left.events_subset hxc₀),
        fun hs => hx.nmem (hs ▸ hxc₀)⟩
    · rw [List.mem_singleton] at h
      subst h
      simp only [decide_eq_true_eq]
      exact ⟨fun hd => ((hdel x).mp hd).2 rfl, hx.facts.2.2.2.symm⟩
  change c₀.order ++ [r₀] <+: (c.order ++ [s₀]).filter _ ++ [s₀]
  rw [← hL, List.filter_append, List.filter_append, hkeep, List.append_assoc,
    List.append_assoc]
  exact List.prefix_append _ _

end LoopInv

end Must

#print axioms Must.LoopInv.brk_pfx_H
#print axioms Must.LoopInv.brk_Y
#print axioms Must.LoopInv.brk_porf
#print axioms Must.LoopInv.brk_porf'
#print axioms Must.LoopInv.del_iff
#print axioms Must.LoopInv.base_eq
#print axioms Must.LoopInv.delList_eq
#print axioms Must.LoopInv.revGuard
#print axioms Must.LoopInv.revisit_graph
#print axioms Must.LoopInv.stepM_revisit
#print axioms Must.LoopInv.revisit_order
