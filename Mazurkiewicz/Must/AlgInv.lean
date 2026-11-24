import Mazurkiewicz.Must.Alg

/-!
# Preservation of the configuration invariant

Plan row M4: "invariant preservation by `StepM` (all cases, including the revisit) and by
operational steps". Every result holds for every model `M`.

* Traces depend only on the events of a thread before an index and on their sources and
  outcomes (`retAt_congr`, `traceBefore_congr`); hence `Program.exec_of_agree` (an execution
  stays one when the earlier events of every kept event are kept with their sources and
  outcomes) and `Program.exec_add` (adding the next event of a thread).
* `Config.Inv.pos_lt`: the insertion order contains `po`, as positions.
* `Config.Inv.add`: adding the next event of a thread with a consistent result.
* The revisit (Q15), for a send `s` of `H` that is unread and `po`-maximal and the guards
  `RevGuard`: `Config.del_po` (the kept set is closed under `po`-predecessors),
  `Config.po_del` (every `po`-successor of `r` is deleted), `Config.del_src` (the source of a
  kept receive other than `r` is kept: from `RevisitCondition` of the deleted sends, line 21,
  not from the order), `Config.Inv.revisit`. No lemma assumes that a source precedes its reader.
* `StepM.inv`, `OpStep.inv`, `Config.inv_init`.
-/

namespace Must

open Graph

variable {Q : Type} [DecidableEq Q] [Membership Val Q]

/-! ### Traces -/

namespace Graph

omit [DecidableEq Q] [Membership Val Q] in
/-- The value returned at `(t, j)` depends only on the events with this identity and on their
sources and outcomes. -/
theorem retAt_congr {G G' : Graph Q} {t : Tid} {j : ℕ}
    (hev : ∀ x : Ev Q, x.tid = t → x.idx = j → (x ∈ G.events ↔ x ∈ G'.events))
    (hrn : ∀ x ∈ G.events, x.tid = t → x.idx = j → G.rf x = G'.rf x ∧ G.nd x = G'.nd x) :
    G.retAt t j = G'.retAt t j := by
  unfold retAt
  have hf : G.events.filter (fun e => e.tid = t ∧ e.idx = j) =
      G'.events.filter (fun e => e.tid = t ∧ e.idx = j) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h, h1, h2⟩
      exact ⟨(hev x h1 h2).mp h, h1, h2⟩
    · rintro ⟨h, h1, h2⟩
      exact ⟨(hev x h1 h2).mpr h, h1, h2⟩
  congr 1
  refine Finset.sup_congr hf (fun x hx => ?_)
  rw [← hf] at hx
  obtain ⟨hx, h1, h2⟩ := Finset.mem_filter.mp hx
  obtain ⟨hr, hn⟩ := hrn x hx h1 h2
  unfold ret
  rw [hr, hn]

omit [DecidableEq Q] [Membership Val Q] in
theorem traceBefore_congr {G G' : Graph Q} {t : Tid} {i : ℕ}
    (h : ∀ j < i, G.retAt t j = G'.retAt t j) : G.traceBefore t i = G'.traceBefore t i :=
  List.map_congr_left fun j hj => h j (List.mem_range.mp hj)

end Graph

namespace Program

omit [DecidableEq Q] [Membership Val Q] in
/-- An execution stays one when every event of the new graph is an old event whose earlier
events in its thread are kept with their sources and outcomes. -/
theorem exec_of_agree (P : Program Q) {G G' : Graph Q} (hE : P.Exec G)
    (h : ∀ x ∈ G'.events, x ∈ G.events ∧ ∀ y : Ev Q, y.tid = x.tid → y.idx < x.idx →
      (y ∈ G.events ↔ y ∈ G'.events) ∧ (y ∈ G.events → G.rf y = G'.rf y ∧ G.nd y = G'.nd y)) :
    P.Exec G' := by
  intro x hx
  obtain ⟨hxG, hy⟩ := h x hx
  have htr : G.traceBefore x.tid x.idx = G'.traceBefore x.tid x.idx :=
    traceBefore_congr fun j hj => retAt_congr
      (fun y h1 h2 => (hy y h1 (h2 ▸ hj)).1)
      (fun y hyG h1 h2 => (hy y h1 (h2 ▸ hj)).2 hyG)
  rw [← htr]
  exact hE x hxG

/-- Adding the next event of a thread to an execution gives an execution. -/
theorem exec_add (P : Program Q) {G : Graph Q} (hE : P.Exec G) (hG : G.Wf) {t : Tid}
    {e : Ev Q} (hn : P.nextEv G t = some e) (src : Option (Src Q)) (out : Option Val) :
    P.Exec (G.add e src out) := by
  have hidx := Model.idx_of_nextEv hn
  have heG := hG.not_mem_of_idx_eq_cnt hidx
  have hagree : ∀ i, i ≤ e.idx → ∀ u : Tid,
      (G.add e src out).traceBefore u i = G.traceBefore u i := by
    intro i hi u
    refine traceBefore_congr fun j hj => retAt_congr (fun y h1 h2 => ?_) (fun y hy h1 h2 => ?_)
    · rw [add_events, Finset.mem_insert]
      constructor
      · rintro (rfl | h)
        · omega
        · exact h
      · exact Or.inr
    · rw [add_events, Finset.mem_insert] at hy
      have hne : y ≠ e := by rintro rfl; omega
      rw [add_rf, add_nd, Function.update_of_ne hne, Function.update_of_ne hne]
      exact ⟨rfl, rfl⟩
  intro x hx
  rw [add_events, Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · unfold nextEv at hn
    obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp hn
    rw [hagree _ le_rfl]
    exact hl
  · have hlt : x.idx < G.cnt x.tid := hG.idx_lt_cnt hx
    have key : (G.add e src out).traceBefore x.tid x.idx = G.traceBefore x.tid x.idx := by
      refine traceBefore_congr fun j hj => retAt_congr (fun y h1 h2 => ?_) (fun y hy h1 h2 => ?_)
      · rw [add_events, Finset.mem_insert]
        constructor
        · rintro (rfl | h)
          · rw [h1] at hidx
            omega
          · exact h
        · exact Or.inr
      · rw [add_events, Finset.mem_insert] at hy
        have hne : y ≠ e := by
          rintro rfl
          rw [h1] at hidx
          omega
        rw [add_rf, add_nd, Function.update_of_ne hne, Function.update_of_ne hne]
        exact ⟨rfl, rfl⟩
    rw [key]
    exact hE x hx

end Program

/-! ### Positions -/

namespace Config

variable {M : Model Q} {P : Program Q} {c : Config Q}

omit [Membership Val Q] in
/-- Positions of events of the order are injective. -/
theorem pos_inj {a b : Ev Q} (ha : a ∈ c.order) : c.pos a = c.pos b ↔ a = b :=
  List.idxOf_inj ha

/-- The insertion order contains `po`. -/
theorem Inv.pos_lt (hc : c.Inv M P) {a b : Ev Q} (h : c.G.po a b) : c.pos a < c.pos b := by
  have ha : a ∈ c.order := (hc.mem a).mpr h.1
  have hb : b ∈ c.order := (hc.mem b).mpr h.2.1
  have hab : a ≠ b := by
    rintro rfl
    exact lt_irrefl _ h.2.2.2
  by_contra hle
  have hlt : c.pos b < c.pos a := by
    rcases Nat.lt_or_eq_of_le (not_lt.mp hle) with h' | h'
    · exact h'
    · exact absurd ((pos_inj hb).mp h').symm hab
  have hla := List.idxOf_lt_length_of_mem ha
  have hlb := List.idxOf_lt_length_of_mem hb
  have := List.pairwise_iff_getElem.mp hc.po _ _ hlb hla hlt
  rw [List.getElem_idxOf, List.getElem_idxOf] at this
  exact this h

/-! ### Addition -/

/-- Adding the next event of a thread with a consistent result keeps the invariant. -/
theorem Inv.add (hc : c.Inv M P) {t : Tid} {e : Ev Q} (hn : P.nextEv c.G t = some e)
    {src : Option (Src Q)} {out : Option Val} (hcons : M.cons (c.G.add e src out)) :
    (c.add e src out).Inv M P := by
  have hidx := Model.idx_of_nextEv hn
  have heG := hc.wf.not_mem_of_idx_eq_cnt hidx
  have heo : e ∉ c.order := fun h => heG ((hc.mem e).mp h)
  refine ⟨?_, ?_, ?_, M.wf _ hcons, P.exec_add hc.exec hc.wf hn src out, hcons⟩
  · refine List.nodup_append.mpr ⟨hc.nodup, List.nodup_singleton e, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb
    subst hb
    exact fun h => heo (h ▸ ha)
  · intro x
    simp only [Config.add, List.mem_append, List.mem_singleton, add_events, Finset.mem_insert,
      hc.mem]
    exact or_comm
  · refine List.pairwise_append.mpr ⟨?_, List.pairwise_singleton _ e, fun a ha b hb => ?_⟩
    · refine hc.po.imp_of_mem fun ha hb h h' => h ?_
      exact po_add_of_mem ((hc.mem _).mp hb) ((hc.mem _).mp ha) h'
    · rw [List.mem_singleton] at hb
      subst hb
      exact hc.wf.not_po_add_left hidx a

/-- The initial configuration satisfies the invariant. -/
theorem inv_init : (init : Config Q).Inv M P where
  nodup := List.nodup_nil
  mem := by simp [init, Graph.empty]
  po := List.Pairwise.nil
  wf := Graph.empty_wf
  exec := by simp [Program.Exec, init, Graph.empty]
  cons := M.empty

/-! ### The revisit (Q15) -/

variable {tie : Tie Q} {H : Config Q} {r s : Ev Q}

omit [Membership Val Q] in
theorem mem_del {d : Ev Q} :
    d ∈ H.del r s ↔ d ∈ H.G.events ∧ d ≠ s ∧ H.pos r < H.pos d ∧ ¬ H.G.porf d s := by
  unfold del
  rw [Finset.mem_filter]

/-- The kept set is closed under `po`-predecessors. -/
theorem del_po (hH : H.Inv M P) {a b : Ev Q} (hab : H.G.po a b) (hb : b ∉ H.del r s) :
    a ∉ H.del r s := by
  intro ha
  obtain ⟨-, has, hra, hna⟩ := mem_del.mp ha
  have hbs : b ≠ s := by
    rintro rfl
    exact hna (Relation.TransGen.single (Or.inl hab))
  have hnb : ¬ H.G.porf b s := fun h => hna (Relation.TransGen.head (Or.inl hab) h)
  have hrb : ¬ H.pos r < H.pos b := fun h => hb (mem_del.mpr ⟨hab.2.1, hbs, h, hnb⟩)
  have := hH.pos_lt hab
  omega

/-- Every `po`-successor of `r` other than `s` is deleted when `r` is not causally before `s`. -/
theorem po_del (hH : H.Inv M P) (hnp : ¬ H.G.porf r s) {b : Ev Q} (hrb : H.G.po r b) :
    b ∈ H.del r s := by
  refine mem_del.mpr ⟨hrb.2.1, ?_, hH.pos_lt hrb, fun h => hnp
    (Relation.TransGen.head (Or.inl hrb) h)⟩
  rintro rfl
  exact hnp (Relation.TransGen.single (Or.inl hrb))

omit [Membership Val Q] in
/-- `RevisitCondition` of a send: no receive of `Previous` reads it (line 21). -/
theorem RevCond.of_send {e : Ev Q} (h : RevCond tie H e s) (he : e.IsSend) :
    ∀ q ∈ H.prev e s, q.IsRecv → H.G.rf q ≠ some (.snd e) := by
  have hR := Lab.IsSend.not_isRecv he
  have h1 : ¬ e.IsRecvNB := fun h' => hR (Lab.IsRecvNB.isRecv h')
  have h2 : ¬ e.IsND := Lab.IsSend.not_isND he
  have h3 : ¬ e.IsRecvB := fun h' => hR (Lab.IsRecvB.isRecv h')
  unfold RevCond at h
  simpa [h1, h2, h3] using h

/-- The source of a kept receive other than `r` is kept: the guard `RevisitCondition` of a
deleted send says that no receive of its `Previous` reads it, and a kept receive is in it. -/
theorem del_src (hH : H.Inv M P) (hg : RevGuard tie H r s) {q s' : Ev Q} (hq : q ∈ H.G.events)
    (hqd : q ∉ H.del r s) (hqr : q ≠ r) (hrf : H.G.rf q = some (.snd s')) : s' ∉ H.del r s := by
  intro hs'
  have hs'send : s'.IsSend := (hH.wf.rf_match _ _ hrf).isSend
  have hqR : q.IsRecv := (hH.wf.rf_some hrf).2
  have hqs : q ≠ s := by
    rintro rfl
    exact Lab.IsSend.not_isRecv hg.smatch.isSend hqR
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
  exact RevCond.of_send (hg.cond s' (Finset.mem_insert_of_mem hs')) hs'send q hprev hqR hrf

omit [Membership Val Q] in
/-- `RevisitCondition(H, s, s)` holds for an unread send `s`: the guard `cond_s` of Q15 is
implied. -/
theorem revCond_self (hS : s.IsSend) (hread : ∀ r', H.G.rf r' ≠ some (.snd s)) :
    RevCond tie H s s := by
  have hR := Lab.IsSend.not_isRecv hS
  have h1 : ¬ s.IsRecvNB := fun h' => hR (Lab.IsRecvNB.isRecv h')
  have h2 : ¬ s.IsND := Lab.IsSend.not_isND hS
  have h3 : ¬ s.IsRecvB := fun h' => hR (Lab.IsRecvB.isRecv h')
  unfold RevCond
  simp only [h1, h2, h3, ↓reduceIte]
  exact fun q _ _ => hread q

omit [Membership Val Q] in
theorem mem_revisitCfg_events {x : Ev Q} :
    x ∈ (H.revisitCfg r s).G.events ↔ x ∈ H.G.events ∧ x ∉ H.del r s := by
  simp only [revisitCfg, Graph.revisit, restrict_events, setRF_events, Finset.mem_inter,
    Finset.mem_sdiff]
  tauto

/-- The revisit successor of Q15 is well-formed under the guards, for an unread send `s` of `H`
(the premises of `Graph.Wf.revisit`, M1b); its consistency is not needed for this. -/
theorem revisit_wf (hH : H.Inv M P) (hs : s ∈ H.G.events)
    (hread : ∀ r', H.G.rf r' ≠ some (.snd s)) (hg : RevGuard tie H r s) :
    (H.revisitCfg r s).G.Wf :=
  hH.wf.revisit hg.mem hs hg.smatch (fun r' _ _ => hread r') hg.nporf
    (fun h => (mem_del.mp h).2.1 rfl) (fun _ _ hab hb => del_po hH hab hb)
    (fun _ hq hqd hqr _ h => del_src hH hg hq hqd hqr h)

/-- The revisit successor of Q15 satisfies the invariant when it is consistent, for an unread
`po`-maximal send `s` of `H` and the guards of Q15. -/
theorem Inv.revisit (hH : H.Inv M P) (hs : s ∈ H.G.events)
    (hread : ∀ r', H.G.rf r' ≠ some (.snd s)) (hmax : ∀ a, ¬ H.G.po s a)
    (hg : RevGuard tie H r s) (hcons : M.cons (H.revisitCfg r s).G) :
    (H.revisitCfg r s).Inv M P := by
  set D := H.del r s with hD
  have hsD : s ∉ D := fun h => (mem_del.mp h).2.1 rfl
  have hmem := fun x => (mem_revisitCfg_events (H := H) (r := r) (s := s) (x := x))
  refine ⟨?_, ?_, ?_, revisit_wf hH hs hread hg, ?_, hcons⟩
  · refine List.nodup_append.mpr ⟨hH.nodup.filter _, List.nodup_singleton s,
      fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb
    subst hb
    have := (List.mem_filter.mp ha).2
    simp only [decide_eq_true_eq] at this
    exact this.2
  · intro x
    rw [hmem x]
    simp only [revisitCfg, List.mem_append, List.mem_filter, List.mem_singleton,
      decide_eq_true_eq, hH.mem]
    constructor
    · rintro (⟨h1, h2, -⟩ | rfl)
      · exact ⟨h1, h2⟩
      · exact ⟨hs, hsD⟩
    · rintro ⟨h1, h2⟩
      by_cases hx : x = s
      · exact Or.inr hx
      · exact Or.inl ⟨h1, h2, hx⟩
  · have hpo : ∀ a b, (H.revisitCfg r s).G.po a b → H.G.po a b := fun a b h =>
      ⟨((hmem a).mp h.1).1, ((hmem b).mp h.2.1).1, h.2.2⟩
    refine List.pairwise_append.mpr ⟨?_, List.pairwise_singleton _ s, fun a _ b hb => ?_⟩
    · exact (hH.po.filter _).imp fun h h' => h (hpo _ _ h')
    · rw [List.mem_singleton] at hb
      subst hb
      exact fun h' => hmax a (hpo _ _ h')
  · refine P.exec_of_agree hH.exec fun x hx => ?_
    obtain ⟨hxH, hxD⟩ := (hmem x).mp hx
    refine ⟨hxH, fun y h1 h2 => ⟨?_, fun hy => ?_⟩⟩
    · constructor
      · intro hy
        exact (hmem y).mpr ⟨hy, del_po hH ⟨hy, hxH, h1, h2⟩ hxD⟩
      · exact fun hy => ((hmem y).mp hy).1
    · have hyD : y ∉ D := del_po hH ⟨hy, hxH, h1, h2⟩ hxD
      have hyr : y ≠ r := by
        rintro rfl
        exact hxD (po_del hH hg.nporf ⟨hy, hxH, h1, h2⟩)
      have hyE : y ∈ H.G.events \ D := Finset.mem_sdiff.mpr ⟨hy, hyD⟩
      simp only [revisitCfg, Graph.revisit, restrict_rf, restrict_nd, setRF_rf, setRF_nd,
        ← hD, hyE, ↓reduceIte, Function.update_of_ne hyr]
      simp

end Config

/-! ### Steps -/

open Config

variable {M : Model Q} {P : Program Q} {c : Config Q} {tie : Tie Q}

/-- The new event of a step is the next event of a thread. -/
theorem exists_nextEv_of_nextP {G : Graph Q} {e : Ev Q} (h : M.nextP P G = some e) :
    ∃ t, P.nextEv G t = some e := by
  obtain ⟨t, -, ht, -⟩ := M.mem_availM_iff'.mp (Model.mem_availM_of_nextP h)
  exact ⟨t, ht⟩

/-- A non-revisit step gives a consistent graph. -/
theorem NrAdd.cons (hc : c.Inv M P) {e : Ev Q} {src : Option (Src Q)} {out : Option Val}
    (h : NrAdd M P c.G e src out) : M.cons (c.G.add e src out) := by
  obtain ⟨hn, h⟩ := h
  obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hn
  have hidx := Model.idx_of_nextEv ht
  rcases h with ⟨S, v, hl, hv, rfl, rfl⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨hL, rfl, rfl⟩
  · have hN : e.IsND := by simp [Ev.IsND, hl, Lab.IsND]
    exact M.ext_nd _ e v hc.cons hidx hN (by simpa [Ev.ndSet, hl, Lab.ndSet] using hv)
  · exact h
  · exact h
  · exact M.ext_plain _ e hc.cons hidx (Lab.IsLoc.not_isRecv hL) (Lab.IsLoc.not_isND hL)

/-- Adding a send that is the next event of a thread keeps the invariant. -/
theorem Config.Inv.addSend (hc : c.Inv M P) {t : Tid} {e : Ev Q} (hn : P.nextEv c.G t = some e)
    (hS : e.IsSend) : (c.add e none none).Inv M P :=
  hc.add hn (M.ext_plain _ e hc.cons (Model.idx_of_nextEv hn) (Lab.IsSend.not_isRecv hS)
    (Lab.IsSend.not_isND hS))

/-- The send added by a step is unread and `po`-maximal. -/
theorem addSend_facts (hc : c.Inv M P) {t : Tid} {e : Ev Q} (hn : P.nextEv c.G t = some e) :
    e ∈ (c.add e none none).G.events ∧ (∀ r', (c.add e none none).G.rf r' ≠ some (.snd e)) ∧
      ∀ a, ¬ (c.add e none none).G.po e a := by
  have hidx := Model.idx_of_nextEv hn
  have heG := hc.wf.not_mem_of_idx_eq_cnt hidx
  refine ⟨Finset.mem_insert_self _ _, fun r' h => ?_, hc.wf.not_po_add_left hidx⟩
  simp only [Config.add, add_rf] at h
  by_cases hr : r' = e
  · rw [hr, Function.update_self] at h
    cases h
  · rw [Function.update_of_ne hr] at h
    exact heG (hc.wf.rf_mem _ _ h)

/-- The invariant is preserved by every algorithmic step. -/
theorem StepM.inv {c c' : Config Q} (h : StepM M tie P c c') (hc : c.Inv M P) :
    c'.Inv M P := by
  cases h with
  | nr h =>
    obtain ⟨t, ht⟩ := exists_nextEv_of_nextP h.1
    exact hc.add ht (h.cons hc)
  | revisit hn hS hg hcons =>
    obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hn
    obtain ⟨h1, h2, h3⟩ := addSend_facts hc ht
    exact (hc.addSend ht hS).revisit h1 h2 h3 hg hcons

/-- The invariant is preserved by every operational step. -/
theorem OpStep.inv {c c' : Config Q} (h : OpStep M P c c') (hc : c.Inv M P) : c'.Inv M P := by
  obtain ⟨e, src, out, ⟨he, -, hcons⟩, rfl⟩ := h
  obtain ⟨t, -, ht, -⟩ := M.mem_availM_iff'.mp he
  exact hc.add ht hcons

end Must

#print axioms Must.Program.exec_of_agree
#print axioms Must.Program.exec_add
#print axioms Must.Config.Inv.pos_lt
#print axioms Must.Config.Inv.add
#print axioms Must.Config.del_po
#print axioms Must.Config.po_del
#print axioms Must.Config.del_src
#print axioms Must.Config.Inv.revisit
#print axioms Must.Config.revisit_wf
#print axioms Must.Config.revCond_self
#print axioms Must.StepM.inv
#print axioms Must.OpStep.inv
