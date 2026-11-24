import Mazurkiewicz.Must.AlgSound

/-!
# The relation `StepM` agrees with M2's executable `stepM`

Plan row M4, `stepM_iff_compute`. For a model `M` and a Boolean test `consB` that decides
`M.cons` on graphs with `Supp`, and a selection `T` (Q9), the relation
`StepM M (T.pick consB) P` and M2's `stepM consB (Variant.repaired consB T) P` agree on every
configuration satisfying the invariant: `stepM` is `none` iff `next_P = ⊥`, and the successor
list contains exactly the `StepM`-successors.

* `revCond_iff`: M2's `revCond` with the oracle `oracleQ9` is `RevCond` with `T.pick consB`.
* `mem_revisitsOf_iff`, `stepM_eq_none_iff`, `mem_stepM_iff` (every model with a decision
  procedure); `stepM_iff_compute_asyn`, `stepM_iff_compute_p2p` (with `consAsynB`, `consAPB`);
  `stepM_iff_compute_cd` (with `consCDB`). There is no decision procedure for `mbox` (M3), so
  no agreement is stated for `mbox` or `comb`.
* `tieQ9_pick`: `T.pick consB` satisfies Q9 for the model.
-/

namespace Must

open Graph

variable {Q : Type} [DecidableEq Q] [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)]
variable {M : Model Q} {consB : Graph Q → Bool}

omit [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
/-- M2's oracle `oracleQ9` is `RevCond`'s reading of line 22 with the tie-break `T.pick consB`. -/
theorem revCond_iff (T : Sel Q) (H : Config Q) (e s : Ev Q) :
    revCond (oracleQ9 consB T) H e s = true ↔ RevCond (T.pick consB) H e s := by
  unfold revCond RevCond
  split_ifs with h1 h2 h3
  · simp
  · simp
  · simp only [oracleQ9]
    cases hp : T.pick consB ((H.G.restrict (H.prev e s)).remove {e}) e with
    | none => simp
    | some id =>
      simp only [decide_eq_true_eq, mem_srcOf, Option.some.injEq]
      constructor
      · rintro ⟨s', h, rfl⟩
        exact ⟨s', h, rfl⟩
      · rintro ⟨s', h, rfl⟩
        exact ⟨s', h, rfl⟩
  · simp

omit [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
/-- `T.pick consB` satisfies Q9 for `M`. -/
theorem tieQ9_pick (hc : ∀ H : Graph Q, H.Supp → (consB H = true ↔ M.cons H)) (T : Sel Q) :
    TieQ9 M (T.pick consB) := by
  refine ⟨fun X e id hX h => ?_, fun X e hX ⟨s, hs, hcs⟩ => ?_⟩
  · obtain ⟨s, hs, hcs, hid⟩ := T.pick_spec consB h
    exact ⟨s, hs, (hc _ (hX.add _ _ _)).mp hcs, hid⟩
  · exact T.pick_isSome consB ⟨s, hs, (hc _ (hX.add _ _ _)).mpr hcs⟩

omit [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
/-- The two kinds of algorithmic steps. -/
theorem stepM_cases {tie : Tie Q} {P : Program Q} {c c' : Config Q} :
    StepM M tie P c c' ↔
      (∃ e src out, NrAdd M P c.G e src out ∧ c' = c.add e src out) ∨
      (∃ e r, M.nextP P c.G = some e ∧ e.IsSend ∧ RevGuard tie (c.add e none none) r e ∧
        M.cons ((c.add e none none).revisitCfg r e).G ∧
        c' = (c.add e none none).revisitCfg r e) := by
  constructor
  · rintro (⟨h⟩ | ⟨h1, h2, h3, h4⟩)
    · exact Or.inl ⟨_, _, _, h, rfl⟩
    · exact Or.inr ⟨_, _, h1, h2, h3, h4, rfl⟩
  · rintro (⟨e, src, out, h, rfl⟩ | ⟨e, r, h1, h2, h3, h4, rfl⟩)
    · exact .nr h
    · exact .revisit h1 h2 h3 h4

variable (hc : ∀ H : Graph Q, H.Supp → (consB H = true ↔ M.cons H))
include hc

/-- M2's revisits by the last send `s` of `H` are the revisit successors of `StepM`. -/
theorem mem_revisitsOf_iff (T : Sel Q) {H : Config Q} (hS : H.G.Supp)
    (hmem : ∀ x, x ∈ H.order ↔ x ∈ H.G.events) (s : Ev Q) (c' : Config Q) :
    c' ∈ revisitsOf consB (Variant.repaired consB T) H s ↔
      ∃ r, RevGuard (T.pick consB) H r s ∧ M.cons (H.revisitCfg r s).G ∧
        c' = H.revisitCfg r s := by
  have hrev : ∀ r, r ∈ H.G.events → (H.revisitCfg r s).G.Supp := fun r hr =>
    (hS.setRF hr _).restrict _
  unfold revisitsOf
  simp only [List.mem_filterMap, List.mem_filter, decide_eq_true_eq, Variant.repaired,
    Bool.false_eq_true, ↓reduceIte]
  constructor
  · rintro ⟨r, ⟨hr, hR, hm, hp⟩, h⟩
    split_ifs at h with hA hB
    cases h
    have hrG := (hmem r).mp hr
    replace hA := Bool.and_eq_true _ _ ▸ hA
    exact ⟨r, ⟨hrG, hR, hm, hp, fun d hd => (revCond_iff T H d s).mp (of_decide_eq_true hA.1 d hd),
      (revCond_iff T H s s).mp hA.2⟩, (hc _ (hrev r hrG)).mp hB, rfl⟩
  · rintro ⟨r, hg, hcons, rfl⟩
    refine ⟨r, ⟨(hmem r).mpr hg.mem, hg.recv, hg.smatch, hg.nporf⟩, ?_⟩
    have hB : consB (H.revisitCfg r s).G = true := (hc _ (hrev r hg.mem)).mpr hcons
    split_ifs with hA hB'
    · rfl
    · exact absurd hB hB'
    · exact absurd (Bool.and_eq_true _ _ ▸ ⟨decide_eq_true fun d hd =>
        (revCond_iff T H d s).mpr (hg.cond d hd),
        (revCond_iff T H s s).mpr hg.cond_s⟩) hA

/-- M2's `stepM` is `none` iff `next_P = ⊥`. -/
theorem stepM_eq_none_iff (T : Sel Q) (P : Program Q) {c : Config Q} (hS : c.G.Supp) :
    stepM consB (Variant.repaired consB T) P c = none ↔ M.nextP P c.G = none := by
  have hn : (Variant.repaired consB T).next P c.G = M.nextP P c.G := Model.nextP_eq consB hc P hS
  unfold stepM
  rw [hn]
  cases M.nextP P c.G <;> simp

/-- M2's successor list is the set of `StepM`-successors, on configurations satisfying the
invariant. -/
theorem mem_stepM_iff (T : Sel Q) (P : Program Q) {c : Config Q} (hi : c.Inv M P)
    (c' : Config Q) :
    c' ∈ (stepM consB (Variant.repaired consB T) P c).getD [] ↔
      StepM M (T.pick consB) P c c' := by
  have hS := hi.wf.supp
  have hn : (Variant.repaired consB T).next P c.G = M.nextP P c.G := Model.nextP_eq consB hc P hS
  have key : ∀ e, M.nextP P c.G = some e → (StepM M (T.pick consB) P c c' ↔
      (∃ src out, ((∃ S v, e.lab = .nd S ∧ v ∈ S ∧ src = none ∧ out = some v) ∨
        (e.IsRecv ∧ out = none ∧ (src = some .bot ∨ ∃ s ∈ c.G.S, src = some (.snd s)) ∧
          M.cons (c.G.add e src out)) ∨
        (e.IsSend ∧ src = none ∧ out = none ∧ M.cons (c.G.add e src out)) ∨
        (e.IsLoc ∧ src = none ∧ out = none)) ∧ c' = c.add e src out) ∨
      (∃ r, e.IsSend ∧ RevGuard (T.pick consB) (c.add e none none) r e ∧
        M.cons ((c.add e none none).revisitCfg r e).G ∧
        c' = (c.add e none none).revisitCfg r e)) := by
    intro e he
    rw [stepM_cases]
    constructor
    · rintro (⟨e', src, out, ⟨h1, h2⟩, rfl⟩ | ⟨e', r, h1, h2⟩)
      · obtain rfl : e = e' := Option.some.inj (he.symm.trans h1)
        exact Or.inl ⟨src, out, h2, rfl⟩
      · obtain rfl : e = e' := Option.some.inj (he.symm.trans h1)
        exact Or.inr ⟨r, h2⟩
    · rintro (⟨src, out, h2, rfl⟩ | ⟨r, h2⟩)
      · exact Or.inl ⟨e, src, out, ⟨he, h2⟩, rfl⟩
      · exact Or.inr ⟨e, r, he, h2⟩
  unfold stepM
  rw [hn]
  rcases hne : M.nextP P c.G with _ | e
  · simp only [Option.getD_none, List.not_mem_nil, false_iff]
    intro h
    cases h with
    | nr h => rw [h.1] at hne; cases hne
    | revisit h => rw [h] at hne; cases hne
  · simp only [Option.getD_some]
    rw [key e hne]
    have hsupp : ∀ src out, (c.add e src out).G.Supp := fun src out => hS.add e src out
    split
    next S hl =>
      have hR : ¬ e.IsRecv := by simp [Ev.IsRecv, hl, Lab.IsRecv]
      have hSd : ¬ e.IsSend := by simp [Ev.IsSend, hl, Lab.IsSend]
      have hL : ¬ e.IsLoc := by simp [Ev.IsLoc, hl, Lab.IsLoc]
      constructor
      · intro h
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
        exact Or.inl ⟨none, some v, Or.inl ⟨S, v, hl, mem_ndList.mp hv, rfl, rfl⟩, rfl⟩
      · rintro (⟨src, out, h, rfl⟩ | ⟨r, h, -⟩)
        · rcases h with ⟨S', v, hl', hv, rfl, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
          · rw [hl] at hl'
            cases hl'
            exact List.mem_map.mpr ⟨v, mem_ndList.mpr hv, rfl⟩
          · exact absurd h hR
          · exact absurd h hSd
          · exact absurd h hL
        · exact absurd h hSd
    next a vals hl =>
      have hR : e.IsRecv := by simp [Ev.IsRecv, hl, Lab.IsRecv]
      have hSd : ¬ e.IsSend := Lab.IsRecv.not_isSend hR
      have hL : ¬ e.IsLoc := by simp [Ev.IsLoc, hl, Lab.IsLoc]
      constructor
      · intro h
        obtain ⟨x, hx, h⟩ := List.mem_filterMap.mp h
        split_ifs at h with hcB
        cases h
        refine Or.inl ⟨some x, none, Or.inr (Or.inl ⟨hR, rfl, ?_, (hc _ (hsupp _ _)).mp hcB⟩), rfl⟩
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
          obtain ⟨hd1, hd2⟩ := List.mem_filter.mp hd
          exact Or.inr ⟨d, (Graph.mem_S _).mpr ⟨(hi.mem d).mp hd1, of_decide_eq_true hd2⟩, rfl⟩
        · rw [List.mem_singleton] at hx
          exact Or.inl (by rw [hx])
      · rintro (⟨src, out, h, rfl⟩ | ⟨r, h, -⟩)
        · rcases h with ⟨S', v, hl', -⟩ | ⟨-, rfl, hsrc, hcons⟩ | ⟨h, -⟩ | ⟨h, -⟩
          · rw [hl] at hl'
            cases hl'
          · rcases hsrc with rfl | ⟨s, hs, rfl⟩
            · refine List.mem_filterMap.mpr ⟨.bot,
                List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
              simp [(hc _ (hsupp _ _)).mpr hcons]
            · obtain ⟨hsG, hsS⟩ := (Graph.mem_S _).mp hs
              refine List.mem_filterMap.mpr ⟨.snd s, List.mem_append_left _ (List.mem_map.mpr
                ⟨s, List.mem_filter.mpr ⟨(hi.mem s).mpr hsG, decide_eq_true hsS⟩, rfl⟩), ?_⟩
              simp [(hc _ (hsupp _ _)).mpr hcons]
          · exact absurd h hSd
          · exact absurd h hL
        · exact absurd h hSd
    next m dst v hl =>
      have hSd : e.IsSend := by simp [Ev.IsSend, hl, Lab.IsSend]
      have hR : ¬ e.IsRecv := Lab.IsSend.not_isRecv hSd
      have hL : ¬ e.IsLoc := by simp [Ev.IsLoc, hl, Lab.IsLoc]
      have hmem : ∀ x, x ∈ (c.add e none none).order ↔ x ∈ (c.add e none none).G.events := by
        intro x
        simp only [Config.add, List.mem_append, List.mem_singleton, add_events,
          Finset.mem_insert, hi.mem]
        exact or_comm
      rw [List.mem_append, mem_revisitsOf_iff hc T (hsupp _ _) hmem]
      constructor
      · rintro (h | ⟨r, h1, h2, rfl⟩)
        · split_ifs at h with hcB
          · rw [List.mem_singleton] at h
            subst h
            exact Or.inl ⟨none, none, Or.inr (Or.inr (Or.inl ⟨hSd, rfl, rfl,
              (hc _ (hsupp _ _)).mp hcB⟩)), rfl⟩
          · exact absurd h List.not_mem_nil
        · exact Or.inr ⟨r, hSd, h1, h2, rfl⟩
      · rintro (⟨src, out, h, rfl⟩ | ⟨r, -, h1, h2, rfl⟩)
        · rcases h with ⟨S', v, hl', -⟩ | ⟨h, -⟩ | ⟨-, rfl, rfl, hcons⟩ | ⟨h, -⟩
          · rw [hl] at hl'
            cases hl'
          · exact absurd h hR
          · left
            simp [(hc _ (hsupp _ _)).mpr hcons]
          · exact absurd h hL
        · exact Or.inr ⟨r, h1, h2, rfl⟩
    next l h1 h2 h3 =>
      have hR : ¬ e.IsRecv := fun h => by
        obtain ⟨a, vals, h'⟩ := (Lab.isRecv_iff _).mp h
        exact h2 a vals h'
      have hSd : ¬ e.IsSend := fun h => by
        obtain ⟨m, d, v, h'⟩ := (Lab.isSend_iff _).mp h
        exact h3 m d v h'
      have hN : ¬ e.IsND := fun h => by
        obtain ⟨S, h'⟩ := (Lab.isND_iff _).mp h
        exact h1 S h'
      have hL : e.IsLoc := by
        rcases Lab.cases_lab e.lab with h | h | h | h
        · exact absurd h hR
        · exact absurd h hSd
        · exact absurd h hN
        · exact h
      rw [List.mem_singleton]
      constructor
      · rintro rfl
        exact Or.inl ⟨none, none, Or.inr (Or.inr (Or.inr ⟨hL, rfl, rfl⟩)), rfl⟩
      · rintro (⟨src, out, h, rfl⟩ | ⟨r, h, -⟩)
        · rcases h with ⟨S', v, hl', -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, rfl, rfl⟩
          · exact absurd hl' (h1 S')
          · exact absurd h hR
          · exact absurd h hSd
          · rfl
        · exact absurd h hSd

/-- `stepM_iff_compute` for a model with a decision procedure: on a configuration satisfying the
invariant, M2's `stepM` is `none` iff there is no next event, and its successor list contains
exactly the `StepM`-successors. -/
theorem stepM_iff_compute (T : Sel Q) (P : Program Q) {c : Config Q} (hi : c.Inv M P) :
    (stepM consB (Variant.repaired consB T) P c = none ↔ M.nextP P c.G = none) ∧
      ∀ c', c' ∈ (stepM consB (Variant.repaired consB T) P c).getD [] ↔
        StepM M (T.pick consB) P c c' :=
  ⟨stepM_eq_none_iff hc T P hi.wf.supp, mem_stepM_iff hc T P hi⟩

omit hc

/-- `stepM_iff_compute` for `asyn`, with M2's `consAsynB`. -/
theorem stepM_iff_compute_asyn (T : Sel Q) (P : Program Q) {c : Config Q}
    (hi : c.Inv Model.asyn P) :
    (stepM consAsynB (Variant.repaired consAsynB T) P c = none ↔
        Model.asyn.nextP P c.G = none) ∧
      ∀ c', c' ∈ (stepM consAsynB (Variant.repaired consAsynB T) P c).getD [] ↔
        StepM Model.asyn (T.pick consAsynB) P c c' :=
  stepM_iff_compute consAsynB_iff_asyn T P hi

/-- `stepM_iff_compute` for `p2p`, with M2's `consAPB`. -/
theorem stepM_iff_compute_p2p (T : Sel Q) (P : Program Q) {c : Config Q}
    (hi : c.Inv Model.p2p P) :
    (stepM consAPB (Variant.repaired consAPB T) P c = none ↔ Model.p2p.nextP P c.G = none) ∧
      ∀ c', c' ∈ (stepM consAPB (Variant.repaired consAPB T) P c).getD [] ↔
        StepM Model.p2p (T.pick consAPB) P c c' :=
  stepM_iff_compute consAPB_iff_p2p T P hi

/-- `stepM_iff_compute` for `cd`, with M3's `consCDB`. -/
theorem stepM_iff_compute_cd (T : Sel Q) (P : Program Q) {c : Config Q}
    (hi : c.Inv Model.cd P) :
    (stepM Model.consCDB (Variant.repaired Model.consCDB T) P c = none ↔
        Model.cd.nextP P c.G = none) ∧
      ∀ c', c' ∈ (stepM Model.consCDB (Variant.repaired Model.consCDB T) P c).getD [] ↔
        StepM Model.cd (T.pick Model.consCDB) P c c' :=
  stepM_iff_compute (fun _ hH => Model.consCDB_iff hH) T P hi

end Must

#print axioms Must.revCond_iff
#print axioms Must.tieQ9_pick
#print axioms Must.mem_revisitsOf_iff
#print axioms Must.stepM_eq_none_iff
#print axioms Must.mem_stepM_iff
#print axioms Must.stepM_iff_compute
#print axioms Must.stepM_iff_compute_asyn
#print axioms Must.stepM_iff_compute_p2p
#print axioms Must.stepM_iff_compute_cd
