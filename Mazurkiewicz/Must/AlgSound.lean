import Mazurkiewicz.Must.AlgInv
import Mazurkiewicz.Must.ModelComb

/-!
# Soundness of Algorithm 1, and the three orders of Q13

Paper: Appendix A.1 ("Must is trivially sound"), Definitions A.4, A.7. Plan: Section 3 rows
"soundness" (R, split in two), "Def. A.4, A.6, A.7, A.8" (Q13).

* `ReachM.sound` (every model): every configuration reachable by algorithmic steps satisfies
  `Config.Inv`: its graph is a well-formed `M`-consistent execution of `P`, its insertion order
  lists its events once each and contains `po`.
* `reported_mem_sem` (every model): a reachable configuration without next event (line 4) is
  in `⟦P⟧` (`Model.Sem`); `reported_mem_sem_asyn`, `reported_mem_sem_p2p`: the same for M2's
  `Program.Sem` with `consAsynB`, `consAPB`.
* Q13, three relations on graphs: `OpLe` (operational reachability `→*`, Definition A.4 without
  its consistency premises), `IsPrefixOf` (restriction to a `porf`-closed set, M1), `NrLe`
  (reachability by non-revisit steps of the algorithm). Proved, for every model, from a
  consistent graph: `NrLe.opLe` (`NrLe ⊆ OpLe`), `OpLe.isPrefixOf` (`OpLe ⊆ IsPrefixOf`),
  `OpLe.exec` (operational steps keep executions). The converse `IsPrefixOf ⊆ OpLe` for a
  consistent execution as the larger graph is `isPrefixOf_opLe` (below, via the removal of a
  `porf`-maximal event, `Graph.Wf.remove_max_*`). Counterexamples for `OpLe ⊄ NrLe`,
  `IsPrefixOf ⊄ NrLe`, and `IsPrefixOf ⊄ OpLe` without the execution premise: `AlgEx.lean`.
-/

namespace Must

open Graph Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q]
variable {M : Model Q} {P : Program Q} {tie : Tie Q}

/-! ### Soundness -/

/-- Soundness, first part: every reachable configuration satisfies the invariant (a
well-formed consistent execution of `P` with a valid insertion order). -/
theorem ReachM.sound {c : Config Q} (h : ReachM M tie P c) : c.Inv M P := by
  induction h with
  | refl => exact Config.inv_init
  | tail _ hs ih => exact hs.inv ih

/-- Soundness, second part: a reachable configuration with `next_P = ⊥` (reported, line 4) is
in `⟦P⟧`. -/
theorem reported_mem_sem {c : Config Q} (h : ReachM M tie P c) (hn : M.nextP P c.G = none) :
    M.Sem P c.G := by
  have hi := h.sound
  exact ⟨hi.wf, hi.exec, hi.cons, Model.nextP_eq_none_iff.mp hn⟩

/-- For `asyn` the consistency check of the revisit successor (line 13) is implied by the
guards: the successor is well-formed (`Config.revisit_wf`), and `asyn` is well-formedness. -/
theorem asyn_revisit_cons {H : Config Q} {r s : Ev Q} (hH : H.Inv Model.asyn P)
    (hs : s ∈ H.G.events) (hread : ∀ r', H.G.rf r' ≠ some (.snd s)) (hg : RevGuard tie H r s) :
    Model.asyn.cons (H.revisitCfg r s).G :=
  Model.asyn_cons_iff.mpr (Config.revisit_wf hH hs hread hg)

section M2

variable [∀ (v : Val) (q : Q), Decidable (v ∈ q)]

/-- `consAsynB` decides `asyn` on graphs with `Supp`. -/
theorem consAsynB_iff_asyn (H : Graph Q) (hH : H.Supp) :
    H.consAsynB = true ↔ (Model.asyn (Q := Q)).cons H :=
  (consAsynB_iff hH).trans Model.asyn_cons_iff.symm

/-- `consAPB` decides `p2p` on graphs with `Supp`. -/
theorem consAPB_iff_p2p (H : Graph Q) (hH : H.Supp) :
    H.consAPB = true ↔ (Model.p2p (Q := Q)).cons H :=
  (consAPB_iff hH).trans Model.p2p_cons_iff.symm

/-- Soundness for `asyn` in M2's terms: a reported configuration is in `Program.Sem` with
`consAsynB`. -/
theorem reported_mem_sem_asyn {c : Config Q} (h : ReachM Model.asyn tie P c)
    (hn : Model.asyn.nextP P c.G = none) : P.Sem Graph.consAsynB c.G :=
  (Model.sem_iff _ consAsynB_iff_asyn P h.sound.wf.supp).mpr (reported_mem_sem h hn)

/-- Soundness for `p2p` in M2's terms: a reported configuration is in `Program.Sem` with
`consAPB`. -/
theorem reported_mem_sem_p2p {c : Config Q} (h : ReachM Model.p2p tie P c)
    (hn : Model.p2p.nextP P c.G = none) : P.Sem Graph.consAPB c.G :=
  (Model.sem_iff _ consAPB_iff_p2p P h.sound.wf.supp).mpr (reported_mem_sem h hn)

end M2

/-! ### The three orders of Q13 -/

/-- Operational reachability `G →* G'` (Definition A.4, without its consistency premises). -/
def OpLe (M : Model Q) (P : Program Q) : Graph Q → Graph Q → Prop := ReflTransGen (OpStepG M P)

/-- Operational reachability by the printed steps (no consistency premise). -/
def OpLe₀ (M : Model Q) (P : Program Q) : Graph Q → Graph Q → Prop :=
  ReflTransGen (OpStepG₀ M P)

/-- Premised operational reachability is printed operational reachability. The converse to a
consistent endpoint is an M5 obligation (`M.cons G → M.cons G' → OpLe₀ M P G G' →
OpLe M P G G'`). -/
theorem OpLe.opLe₀ {G G' : Graph Q} (h : OpLe M P G G') : OpLe₀ M P G G' := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hs ih =>
    obtain ⟨e, src, out, ⟨h1, h2, -⟩, rfl⟩ := hs
    exact ih.tail ⟨e, src, out, ⟨h1, h2⟩, rfl⟩

/-- Reachability by non-revisit steps of the algorithm. -/
def NrLe (M : Model Q) (P : Program Q) : Graph Q → Graph Q → Prop := ReflTransGen (NrStepG M P)

variable {G G' : Graph Q} {e : Ev Q} {src : Option (Src Q)} {out : Option Val}

/-- The new event of a non-revisit step is the next event of a thread. -/
theorem NrAdd.nextEv (h : NrAdd M P G e src out) : ∃ t, P.nextEv G t = some e :=
  exists_nextEv_of_nextP h.1

/-- A non-revisit step from a consistent graph is an operational step. -/
theorem NrAdd.opAdd (hG : M.cons G) (h : NrAdd M P G e src out) : OpAdd M P G e src out := by
  obtain ⟨t, ht⟩ := h.nextEv
  have hidx := Model.idx_of_nextEv ht
  refine ⟨Model.mem_availM_of_nextP h.1, ?_⟩
  obtain ⟨-, h⟩ := h
  rcases h with ⟨S, v, hl, hv, rfl, rfl⟩ | ⟨hR, rfl, hs, hc⟩ | ⟨hS, rfl, rfl, hc⟩ |
      ⟨hL, rfl, rfl⟩
  · have hN : e.IsND := by simp [Ev.IsND, hl, Lab.IsND]
    have hv' : v ∈ e.ndSet := by simpa [Ev.ndSet, hl, Lab.ndSet] using hv
    exact ⟨Or.inr (Or.inl ⟨hN, rfl, v, hv', rfl⟩), M.ext_nd _ e v hG hidx hN hv'⟩
  · exact ⟨Or.inl ⟨hR, rfl, hs⟩, hc⟩
  · exact ⟨Or.inr (Or.inr ⟨Lab.IsSend.not_isRecv hS, Lab.IsSend.not_isND hS, rfl, rfl⟩), hc⟩
  · exact ⟨Or.inr (Or.inr ⟨Lab.IsLoc.not_isRecv hL, Lab.IsLoc.not_isND hL, rfl, rfl⟩),
      M.ext_plain _ e hG hidx (Lab.IsLoc.not_isRecv hL) (Lab.IsLoc.not_isND hL)⟩

/-- `NrLe ⊆ OpLe` from a consistent graph; the target is consistent. -/
theorem NrLe.opLe (hG : M.cons G) (h : NrLe M P G G') : OpLe M P G G' ∧ M.cons G' := by
  induction h with
  | refl => exact ⟨ReflTransGen.refl, hG⟩
  | tail _ hs ih =>
    obtain ⟨e, src, out, ha, rfl⟩ := hs
    have ho := ha.opAdd ih.2
    exact ⟨ih.1.tail ⟨e, src, out, ho, rfl⟩, ho.2.2⟩

/-- An operational step from a well-formed graph adds the next event of a thread. -/
theorem OpAdd.nextEv (h : OpAdd M P G e src out) : ∃ t, P.nextEv G t = some e := by
  obtain ⟨t, -, ht, -⟩ := M.mem_availM_iff'.mp h.1
  exact ⟨t, ht⟩

/-- `OpLe ⊆ IsPrefixOf` from a consistent graph; the target is consistent. -/
theorem OpLe.isPrefixOf (hG : M.cons G) (h : OpLe M P G G') :
    G.IsPrefixOf G' ∧ M.cons G' := by
  induction h with
  | refl => exact ⟨(M.wf _ hG).isPrefixOf_refl, hG⟩
  | tail _ hs ih =>
    obtain ⟨e, src, out, ha, rfl⟩ := hs
    obtain ⟨t, ht⟩ := ha.nextEv
    exact ⟨ih.1.trans ((M.wf _ ih.2).isPrefixOf_add (Model.idx_of_nextEv ht)), ha.2.2⟩

/-- Operational steps keep executions of `P`. -/
theorem OpLe.exec (hG : M.cons G) (hE : P.Exec G) (h : OpLe M P G G') : P.Exec G' := by
  induction h with
  | refl => exact hE
  | @tail G₁ G₂ h₁ hs ih =>
    obtain ⟨e, src, out, ha, rfl⟩ := hs
    obtain ⟨t, ht⟩ := ha.nextEv
    exact P.exec_add ih (M.wf _ (OpLe.isPrefixOf hG h₁).2) ht src out

/-! ### Removing a `porf`-maximal event -/

namespace Graph

omit [DecidableEq Q] in
/-- An event of an execution of `P` is in a thread of `P`. -/
theorem Wf.tid_mem_threads (hG : G.Wf) (hE : P.Exec G) (he : e ∈ G.events) :
    e.tid ∈ P.threads := by
  by_contra ht
  have h0 : ∃ y ∈ G.events, y.tid = e.tid ∧ y.idx = 0 := by
    rcases Nat.eq_zero_or_pos e.idx with h | h
    · exact ⟨e, he, rfl, h⟩
    · exact hG.idx_contig e he 0 h
  obtain ⟨y, hy, h1, h2⟩ := h0
  have := hE y hy
  rw [h1, h2] at this
  simp [traceBefore, P.step_none _ ht] at this

omit [Membership Val Q] in
theorem mem_remove_single {x : Ev Q} : x ∈ (G.remove {e}).events ↔ x ∈ G.events ∧ x ≠ e := by
  simp only [Graph.remove, restrict_events, Finset.mem_inter, Finset.mem_sdiff,
    Finset.mem_singleton]
  tauto

/-- Removing a `porf`-maximal event keeps well-formedness. -/
theorem Wf.remove_max_wf (hG : G.Wf) (hmax : ∀ b, ¬ G.porfStep e b) : (G.remove {e}).Wf :=
  hG.remove fun q hq b hb => by
    rw [Finset.mem_singleton] at hq
    subst hq
    exact absurd hb (hmax b)

omit [Membership Val Q] in
/-- Removing a `porf`-maximal event keeps executions. -/
theorem Wf.remove_max_exec (hE : P.Exec G) (hmax : ∀ b, ¬ G.porfStep e b) :
    P.Exec (G.remove {e}) := by
  refine P.exec_of_agree hE fun x hx => ?_
  obtain ⟨hxG, hxe⟩ := mem_remove_single.mp hx
  refine ⟨hxG, fun y h1 h2 => ⟨?_, fun hy => ?_⟩⟩
  · rw [mem_remove_single]
    refine ⟨fun hy => ⟨hy, ?_⟩, fun h => h.1⟩
    rintro rfl
    exact hmax x (Or.inl ⟨hy, hxG, h1, h2⟩)
  · have hye : y ≠ e := by
      rintro rfl
      exact hmax x (Or.inl ⟨hy, hxG, h1, h2⟩)
    have hyE : y ∈ G.events \ {e} := by simp [hy, hye]
    simp [Graph.remove, hyE]

/-- A `porf`-maximal event of an execution of `P` is the next event of its thread in the graph
without it. -/
theorem Wf.nextEv_remove_max (hG : G.Wf) (hE : P.Exec G) (he : e ∈ G.events)
    (hmax : ∀ b, ¬ G.porfStep e b) : P.nextEv (G.remove {e}) e.tid = some e := by
  have hcnt := hG.idx_eq_cnt_remove he hmax
  have htr : (G.remove {e}).trace e.tid = G.traceBefore e.tid e.idx := by
    unfold trace
    rw [← hcnt]
    refine traceBefore_congr fun j hj => retAt_congr (fun y h1 h2 => ?_) (fun y hy h1 h2 => ?_)
    · rw [mem_remove_single]
      refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      rintro rfl
      omega
    · obtain ⟨hyG, hye⟩ := mem_remove_single.mp hy
      have hyE : y ∈ G.events \ {e} := by simp [hyG, hye]
      simp [Graph.remove, hyE]
  unfold Program.nextEv
  rw [htr, hE e he, ← hcnt]
  rfl

/-- For a `porf`-maximal event `e` of a consistent execution `G`, adding `e` with its source and
outcome to `G` without `e` is an operational step that gives `G`. -/
theorem Wf.opAdd_remove_max (hc : M.cons G) (hE : P.Exec G) (he : e ∈ G.events)
    (hmax : ∀ b, ¬ G.porfStep e b) :
    OpAdd M P (G.remove {e}) e (G.rf e) (G.nd e) ∧ (G.remove {e}).add e (G.rf e) (G.nd e) = G := by
  have hG := M.wf _ hc
  have hback := hG.add_remove he
  have hS : ∀ s, G.rf e = some (.snd s) → s ∈ (G.remove {e}).S := by
    intro s hs
    have hsG := hG.rf_mem _ _ hs
    have hsS := (hG.rf_match _ _ hs).isSend
    have hse : s ≠ e := by
      rintro rfl
      exact Lab.IsSend.not_isRecv hsS (hG.rf_match _ _ hs).isRecv
    exact (Graph.mem_S _).mpr ⟨mem_remove_single.mpr ⟨hsG, hse⟩, hsS⟩
  refine ⟨⟨M.mem_availM_iff'.mpr ⟨e.tid, hG.tid_mem_threads hE he,
    hG.nextEv_remove_max hE he hmax, ?_⟩, ?_, by rw [hback]; exact hc⟩, hback⟩
  · by_cases hB : e.IsRecvB
    · right
      obtain ⟨x, hx⟩ := hG.exists_rf he (Lab.IsRecvB.isRecv hB)
      cases x with
      | bot => exact absurd (hG.rf_bot e hx) (Lab.not_isRecvB_of_isRecvNB · hB)
      | snd s =>
        refine ⟨s, hS s hx, ?_⟩
        have hnd : G.nd e = none := hG.nd_none (Or.inr (Lab.IsRecv.not_isND
          (Lab.IsRecvB.isRecv hB)))
        have hb2 := hback
        rw [hx, hnd] at hb2
        change M.cons ((G.remove {e}).add e (some (.snd s)) none)
        rw [hb2]
        exact hc
    · exact Or.inl hB
  · rcases Lab.cases_lab e.lab with hR | hS' | hN | hL
    · obtain ⟨x, hx⟩ := hG.exists_rf he hR
      refine Or.inl ⟨hR, hG.nd_none (Or.inr (Lab.IsRecv.not_isND hR)), ?_⟩
      cases x with
      | bot => exact Or.inl hx
      | snd s => exact Or.inr ⟨s, hS s hx, hx⟩
    · exact Or.inr (Or.inr ⟨Lab.IsSend.not_isRecv hS', Lab.IsSend.not_isND hS',
        hG.rf_none (Or.inr (Lab.IsSend.not_isRecv hS')),
        hG.nd_none (Or.inr (Lab.IsSend.not_isND hS'))⟩)
    · obtain ⟨v, hv⟩ := hG.exists_nd he hN
      exact Or.inr (Or.inl ⟨hN, hG.rf_none (Or.inr (Lab.IsND.not_isRecv hN)), v,
        hG.nd_mem e v hv, hv⟩)
    · exact Or.inr (Or.inr ⟨Lab.IsLoc.not_isRecv hL, Lab.IsLoc.not_isND hL,
        hG.rf_none (Or.inr (Lab.IsLoc.not_isRecv hL)),
        hG.nd_none (Or.inr (Lab.IsLoc.not_isND hL))⟩)

omit [DecidableEq Q] in
/-- A non-empty set of events of a well-formed graph has a `porf`-maximal element. -/
theorem Wf.exists_porf_max (hG : G.Wf) {U : Finset (Ev Q)} (hU : U.Nonempty) :
    ∃ m ∈ U, ∀ x ∈ U, ¬ G.porf m x :=
  exists_min_of_strict U (fun a b => G.porf b a) (fun a _ => hG.porf_irrefl a)
    (fun _ _ _ _ _ _ h1 h2 => porf_trans h2 h1) hU

/-- A prefix by restriction, recognised by its events, sources and outcomes. -/
theorem isPrefixOf_of (hG : G.Wf) (hG' : G'.Wf) (hsub : G.events ⊆ G'.events)
    (hcl : G'.Closed G.events) (hrf : ∀ x ∈ G.events, G.rf x = G'.rf x)
    (hnd : ∀ x ∈ G.events, G.nd x = G'.nd x) : G.IsPrefixOf G' := by
  refine ⟨G.events, hcl, hG.ext (hG'.restrict hcl) ?_ (fun x hx => ?_) (fun x hx => ?_)⟩
  · rw [restrict_events, Finset.inter_eq_right.mpr hsub]
  · rw [restrict_rf]
    simp [hx, hrf x hx]
  · rw [restrict_nd]
    simp [hx, hnd x hx]

omit [Membership Val Q] in
/-- The events of a prefix form a closed set of the larger graph. -/
theorem IsPrefixOf.closed_events (h : G.IsPrefixOf G') : G'.Closed G.events := by
  obtain ⟨E, hE, rfl⟩ := h
  intro a b hab hb
  have hb := Finset.mem_coe.mp hb
  rw [Finset.mem_inter, restrict_events, Finset.mem_inter] at hb
  have := Finset.mem_coe.mp (hE hab (Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨hb.1, hb.2.2⟩)))
  refine Finset.mem_coe.mpr ?_
  rw [Finset.mem_inter, restrict_events]
  exact ⟨(Finset.mem_inter.mp this).1, this⟩

end Graph

/-- `IsPrefixOf ⊆ OpLe` towards a consistent execution of `P` (plan Section 2b, "operational
prefix", one direction): a prefix of a consistent execution reaches it by operational steps
(the events outside the prefix are added in reverse order of removal of `porf`-maximal
events). -/
theorem isPrefixOf_opLe (hc : M.cons G') (hE : P.Exec G') (hp : G.IsPrefixOf G') :
    OpLe M P G G' := by
  induction hn : G'.events.card generalizing G' with
  | zero =>
    have hG' := M.wf _ hc
    have h0 : G'.events = ∅ := Finset.card_eq_zero.mp hn
    have : G = G' := by
      by_contra hne
      have := hp.card_lt hG' hne
      omega
    rw [this]
    exact ReflTransGen.refl
  | succ n ih =>
    have hG' := M.wf _ hc
    by_cases hGG : G = G'
    · rw [hGG]
      exact ReflTransGen.refl
    have hsub := hp.events_subset
    have hG : G.Wf := hG'.of_isPrefixOf hp
    have hlt := hp.card_lt hG' hGG
    have hU : (G'.events \ G.events).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, Ne, Finset.sdiff_eq_empty_iff_subset]
      intro h
      have := Finset.card_le_card h
      omega
    obtain ⟨m, hm, hmax⟩ := hG'.exists_porf_max hU
    obtain ⟨hmG', hmG⟩ := Finset.mem_sdiff.mp hm
    have hcl := hp.closed_events
    have hstep : ∀ b, ¬ G'.porfStep m b := by
      intro b hb
      have hbG' := (hG'.mem_of_porfStep hb).2
      by_cases hbG : b ∈ G.events
      · have := Finset.mem_coe.mp (hcl hb (Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨hbG', hbG⟩)))
        exact hmG (Finset.mem_inter.mp this).2
      · exact hmax b (Finset.mem_sdiff.mpr ⟨hbG', hbG⟩) (TransGen.single hb)
    obtain ⟨hop, hback⟩ := Graph.Wf.opAdd_remove_max hc hE hmG' hstep
    set G'' := G'.remove {m} with hG''
    have hG''w : G''.Wf := hG'.remove_max_wf hstep
    have hc'' : M.cons G'' := M.prefixClosed _ _ hc (hG'.remove_closed fun q hq b hb => by
      rw [Finset.mem_singleton] at hq
      subst hq
      exact absurd hb (hstep b))
    have hE'' : P.Exec G'' := Graph.Wf.remove_max_exec hE hstep
    have hcard : G''.events.card = n := by
      have : G''.events = G'.events.erase m := by
        ext x
        rw [mem_remove_single, Finset.mem_erase]
        tauto
      rw [this, Finset.card_erase_of_mem hmG', hn]
      rfl
    have hmE : ∀ x ∈ G.events, x ≠ m := fun x hx h => hmG (h ▸ hx)
    have hp'' : G.IsPrefixOf G'' := by
      refine isPrefixOf_of hG hG''w (fun x hx => mem_remove_single.mpr ⟨hsub hx, hmE x hx⟩)
        (fun a b hab hb => ?_) (fun x hx => ?_) (fun x hx => ?_)
      · have hb := Finset.mem_coe.mp hb
        have hab' := porfStep_restrict_le _ hab
        have ha := Finset.mem_coe.mp (hcl hab' (Finset.mem_coe.mpr
          (Finset.mem_inter.mpr ⟨hsub (Finset.mem_inter.mp hb).2, (Finset.mem_inter.mp hb).2⟩)))
        have haG := (Finset.mem_inter.mp ha).2
        exact Finset.mem_coe.mpr (Finset.mem_inter.mpr
          ⟨mem_remove_single.mpr ⟨hsub haG, hmE _ haG⟩, haG⟩)
      · have hxE : x ∈ G'.events \ {m} := by simp [hsub hx, hmE x hx]
        rw [hp.rf_eq hx]
        simp [G'', Graph.remove, hxE]
      · have hxE : x ∈ G'.events \ {m} := by simp [hsub hx, hmE x hx]
        rw [hp.nd_eq hx]
        simp [G'', Graph.remove, hxE]
    exact (ih hc'' hE'' hp'' hcard).tail ⟨m, _, _, hop, hback.symm⟩

/-! ### Revisit steps, fruitless configurations (Definition A.2), `≈` -/

/-- A step that changes the source of an event of the graph is a revisit (the `revisit`
constructor). -/
theorem StepM.revisit_of_rf_ne {tie : Tie Q} {c c' : Config Q} (h : StepM M tie P c c')
    (hc : c.Inv M P) {x : Ev Q} (hx : x ∈ c.G.events) (hne : c'.G.rf x ≠ c.G.rf x) :
    ∃ e r, M.nextP P c.G = some e ∧ e.IsSend ∧ RevGuard tie (c.add e none none) r e ∧
      M.cons ((c.add e none none).revisitCfg r e).G ∧ c' = (c.add e none none).revisitCfg r e := by
  cases h with
  | nr h =>
    rename_i e src out
    obtain ⟨t, ht⟩ := h.nextEv
    have heG := hc.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv ht)
    have hxe : x ≠ e := fun h' => heG (h' ▸ hx)
    exact absurd (by simp [Config.add, Function.update_of_ne hxe]) hne
  | revisit hn hS hg hcons => exact ⟨_, _, hn, hS, hg, hcons, rfl⟩

/-- `c` leads by algorithmic steps to a configuration without next event (a call
`Visit_P(G_f)` that reports, line 4). -/
def LeadsToReport (M : Model Q) (tie : Tie Q) (P : Program Q) (c : Config Q) : Prop :=
  ∃ c', ReflTransGen (StepM M tie P) c c' ∧ M.nextP P c'.G = none

/-- Definition A.2 (p. 28): the visit of `c` is fruitless if it leads to no report. It is a
property of one configuration and its descendants; it is not `≈` (`Config.Approx`, equality up
to the insertion order, Theorem A.3 (a)), which compares two configurations. Theorem A.3 (b)
(no reachable configuration is fruitless) needs completion, M5 (`ReachM.reaches_full`). -/
def Fruitless (M : Model Q) (tie : Tie Q) (P : Program Q) (c : Config Q) : Prop :=
  ¬ LeadsToReport M tie P c

/-- A reported configuration is not fruitless. -/
theorem not_fruitless_of_nextP {tie : Tie Q} {c : Config Q} (hn : M.nextP P c.G = none) :
    ¬ Fruitless M tie P c :=
  fun h => h ⟨c, ReflTransGen.refl, hn⟩

/-- Fruitlessness passes to successors. -/
theorem Fruitless.of_step {tie : Tie Q} {c c' : Config Q} (h : Fruitless M tie P c)
    (hs : StepM M tie P c c') : Fruitless M tie P c' :=
  fun ⟨d, hd, hn⟩ => h ⟨d, ReflTransGen.head hs hd, hn⟩

/-- For a reachable configuration, "not fruitless" is Definition A.2's "leads to a visit of a
graph of `⟦P⟧`". -/
theorem leadsToReport_iff {tie : Tie Q} {c : Config Q} (hr : ReachM M tie P c) :
    LeadsToReport M tie P c ↔ ∃ c', ReflTransGen (StepM M tie P) c c' ∧ M.Sem P c'.G := by
  constructor
  · rintro ⟨c', hc', hn⟩
    exact ⟨c', hc', reported_mem_sem (hr.trans hc') hn⟩
  · rintro ⟨c', hc', hs⟩
    exact ⟨c', hc', Model.nextP_eq_none_iff.mpr hs.2.2.2⟩

omit [Membership Val Q] in
/-- `≈` (`Config.Approx`, equal keys) is equality of the graphs, on graphs with `Supp` (every
configuration satisfying the invariant). -/
theorem Config.approx_iff {c c' : Config Q} (hc : c.G.Supp) (hc' : c'.G.Supp) :
    c.Approx c' ↔ c.G = c'.G :=
  (eq_iff_key hc hc').symm

/-- Plan Section 2b, "operational prefix": between consistent graphs, the larger a consistent
execution of `P`, operational reachability is the causal-prefix order. -/
theorem opLe_iff_isPrefixOf (hG : M.cons G) (hG' : M.cons G') (hE' : P.Exec G') :
    OpLe M P G G' ↔ G.IsPrefixOf G' :=
  ⟨fun h => (OpLe.isPrefixOf hG h).1, isPrefixOf_opLe hG' hE'⟩

end Must

#print axioms Must.asyn_revisit_cons
#print axioms Must.OpLe.opLe₀
#print axioms Must.StepM.revisit_of_rf_ne
#print axioms Must.Fruitless.of_step
#print axioms Must.leadsToReport_iff
#print axioms Must.Config.approx_iff
#print axioms Must.opLe_iff_isPrefixOf
#print axioms Must.ReachM.sound
#print axioms Must.reported_mem_sem
#print axioms Must.reported_mem_sem_asyn
#print axioms Must.reported_mem_sem_p2p
#print axioms Must.NrLe.opLe
#print axioms Must.OpLe.isPrefixOf
#print axioms Must.OpLe.exec
#print axioms Must.Graph.Wf.opAdd_remove_max
#print axioms Must.isPrefixOf_opLe
