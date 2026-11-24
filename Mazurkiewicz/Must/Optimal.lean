import Mazurkiewicz.Must.CompleteM

/-!
# Optimality, part 1: protected events and Lemma A.17 (milestone M8)

Paper: Appendix A.9, Lemma A.17 (p. 34: "there is no later step that deletes" a send that
revisited; the paper cites TruSt and gives no proof). Plan: `plan/must/lean/LEAN-PLAN.md`, rows
A.17 and M8 (`revisit_send_persists`).

The proof here is new: it does not use TruSt's invariants, and no lemma assumes that a source
precedes its reader in the insertion order.

* `Config.BwRead c y x`: `y` reads `x` *backward*, i.e. `x` comes after `y` in the insertion
  order. Only a revisit creates such a pair (the revisiting send is appended after the receive).
* `Config.Prot c x`: `x` is *protected*: `x` is causally before (or equal to) a send that is read
  backward.
* `Config.prot_not_del`: in a revisit allowed by the guards (`RevGuard`), no protected event is
  deleted. The argument: a `porf` path from a deleted event (after `r`) to a backward-read send
  must contain a backward-read send `u` after `r`; `u` is not causally before the revisiting
  send (else the deleted event would be), so `u` is deleted, but `RevisitCondition(H, u, s)` of
  a send (line 21) forbids a reader of `u` in `Previous`, and the backward reader is in it.
* `Config.not_prot_r`: the revisited receive is not protected (for the same reason, using
  `¬ porf r s`).
* `StepM.prot`: protection is preserved by every algorithmic step, and the protected event stays
  in the graph. In a revisit whose deleted or revisited receive `y` read the backward-read send
  `x'`, line 22 (`tie` returns a send of `Previous`, Q9) forces `x'` to be causally before the
  new send, which is read backward by `r` in the successor.
* `StepM.revisit_prot`: the send of a revisit step is protected in the successor.
* `revisit_send_persists` (A.17): after a revisit step by the send `s`, every configuration of
  every later sequence of algorithmic steps contains `s`, and no later revisit deletes it.
* `StepM.porf_of_prot`: `porf` paths into a protected event survive every step (used by A.18).

Hypotheses: the configuration invariant `Config.Inv` (true of every reachable configuration,
`ReachM.sound`) and the first half of `TieQ9` (the tie-break returns a send of its argument), for
every model.
-/

namespace Must

open Graph Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q]
variable {M : Model Q} {P : Program Q} {tie : Tie Q}

/-! ### Lists and relations -/

omit [Membership Val Q] in
/-- A path that starts above `p` and ends at or below `p` (for a numbering `f`) crosses `p` in
one step. -/
theorem rtg_cross {α : Type*} {R : α → α → Prop} (f : α → ℕ) (p : ℕ) {a b : α}
    (h : ReflTransGen R a b) (ha : p < f a) (hb : f b ≤ p) :
    ∃ u v, ReflTransGen R a u ∧ R u v ∧ p < f u ∧ f v ≤ p := by
  induction h with
  | refl => omega
  | @tail b' c hab hbc ih =>
    by_cases hb' : p < f b'
    · exact ⟨b', c, hab, hbc, hb', hb⟩
    · exact ih (by omega)

omit [Membership Val Q] in
/-- Lift a path along a step relation whose steps between nodes with a property `Q'` are steps
of another relation; every node of the path must have the property. -/
theorem rtg_lift {α : Type*} {R R' : α → α → Prop} (Q' : α → Prop) {a b : α}
    (h : ReflTransGen R a b) (hQ : ∀ z, ReflTransGen R z b → Q' z)
    (hR : ∀ u v, R u v → Q' u → Q' v → R' u v) : ReflTransGen R' a b := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head hac hcb ih =>
    exact .head (hR _ _ hac (hQ _ (.head hac hcb)) (hQ _ hcb)) ih

omit [Membership Val Q] in
/-- In a duplicate-free list, `a` has a smaller index than `b` iff `[a, b]` is a sublist. -/
theorem idxOf_lt_iff_sublist {α : Type} [DecidableEq α] {l : List α} {a b : α}
    (hnd : l.Nodup) (ha : a ∈ l) (hb : b ∈ l) : l.idxOf a < l.idxOf b ↔ List.Sublist [a, b] l := by
  induction l with
  | nil => exact absurd ha List.not_mem_nil
  | cons x t ih =>
    have hxt : x ∉ t := (List.nodup_cons.mp hnd).1
    have hnd' := (List.nodup_cons.mp hnd).2
    by_cases hax : a = x
    · subst hax
      rw [List.idxOf_cons_self]
      by_cases hba : b = a
      · subst hba
        simp only [List.idxOf_cons_self, lt_irrefl, false_iff]
        intro h
        rcases List.sublist_cons_iff.mp h with h | ⟨r, hr, hrt⟩
        · exact hxt (h.subset (by simp))
        · cases hr
          exact hxt (hrt.subset (by simp))
      · rw [List.idxOf_cons_ne _ (Ne.symm hba)]
        have hbt : b ∈ t := (List.mem_cons.mp hb).resolve_left hba
        simp only [Nat.zero_lt_succ, true_iff]
        exact List.cons_sublist_cons.mpr (List.singleton_sublist.mpr hbt)
    · have hat : a ∈ t := (List.mem_cons.mp ha).resolve_left hax
      rw [List.idxOf_cons_ne _ (Ne.symm hax)]
      by_cases hbx : b = x
      · subst hbx
        simp only [List.idxOf_cons_self, Nat.not_lt_zero, false_iff]
        intro h
        rcases List.sublist_cons_iff.mp h with h | ⟨r, hr, -⟩
        · exact hxt (h.subset (by simp))
        · cases hr
          exact hax rfl
      · have hbt : b ∈ t := (List.mem_cons.mp hb).resolve_left hbx
        rw [List.idxOf_cons_ne _ (Ne.symm hbx), Nat.succ_lt_succ_iff, ih hnd' hat hbt]
        constructor
        · exact fun h => h.cons x
        · intro h
          rcases List.sublist_cons_iff.mp h with h | ⟨r, hr, -⟩
          · exact h
          · cases hr
            exact absurd rfl hax

namespace Config

/-! ### Backward reads and protected events -/

/-- `y` reads `x` backward in `c`: `y` reads `x` and comes before `x` in the insertion order. -/
def BwRead (c : Config Q) (y x : Ev Q) : Prop := c.G.rfRel x y ∧ c.pos y < c.pos x

/-- `x` is protected in `c`: it is causally before (or equal to) a send read backward. -/
def Prot (c : Config Q) (x : Ev Q) : Prop :=
  ∃ x' y, ReflTransGen c.G.porfStep x x' ∧ c.BwRead y x'

variable {c : Config Q}

/-- A step of causality that goes backward in the insertion order is a backward read. -/
theorem Inv.rfRel_of_porfStep_lt (hc : c.Inv M P) {u v : Ev Q} (h : c.G.porfStep u v)
    (hlt : c.pos v < c.pos u) : c.G.rfRel u v := by
  rcases h with h | h
  · exact absurd (hc.pos_lt h) (by omega)
  · exact h

/-- From an event after position `p` that is causally before a backward-read send, there is a
backward-read send after `p` that the event is causally before (or equal to). -/
theorem Inv.find_bw (hc : c.Inv M P) {p : ℕ} {a x' y : Ev Q} (ha : p < c.pos a)
    (h : ReflTransGen c.G.porfStep a x') (hy : c.BwRead y x') :
    ∃ u v, ReflTransGen c.G.porfStep a u ∧ c.BwRead v u ∧ p < c.pos u := by
  by_cases hx : p < c.pos x'
  · exact ⟨x', y, h, hy, hx⟩
  · obtain ⟨u, v, h1, h2, h3, h4⟩ := rtg_cross c.pos p h ha (by omega)
    exact ⟨u, v, h1, ⟨hc.rfRel_of_porfStep_lt h2 (by omega), by omega⟩, h3⟩

/-- A backward-read send is an event of the graph. -/
theorem BwRead.mem (hc : c.Inv M P) {y x : Ev Q} (h : c.BwRead y x) : x ∈ c.G.events :=
  hc.wf.rf_mem _ _ h.1.2

/-- A protected event is an event of the graph. -/
theorem Prot.mem (hc : c.Inv M P) {x : Ev Q} (h : c.Prot x) : x ∈ c.G.events := by
  obtain ⟨x', y, hxx', hy⟩ := h
  rcases hxx'.cases_head with rfl | ⟨w, hxw, -⟩
  · exact hy.mem hc
  · exact (hc.wf.mem_of_porfStep hxw).1

/-! ### The revisit guards and protected events -/

variable {H : Config Q} {r s : Ev Q}

/-- In a revisit allowed by the guards, a backward-read send after `r` is causally before the
revisiting send `s` (else it would be deleted, and line 21 forbids deleting a send with a
reader in `Previous`). -/
theorem bw_porf (hH : H.Inv M P) (hg : RevGuard tie H r s)
    (hread : ∀ r', H.G.rf r' ≠ some (.snd s)) {u v : Ev Q} (huv : H.BwRead v u)
    (hru : H.pos r < H.pos u) : H.G.porf u s := by
  by_contra hn
  obtain ⟨⟨hv, hrf⟩, hlt⟩ := huv
  have huE : u ∈ H.G.events := hH.wf.rf_mem _ _ hrf
  have hus : u ≠ s := by
    rintro rfl
    exact hread v hrf
  have hdel : u ∈ H.del r s := mem_del.mpr ⟨huE, hus, hru, hn⟩
  have hsend : u.IsSend := (hH.wf.rf_match _ _ hrf).isSend
  have hcond := RevCond.of_send (hg.cond u (Finset.mem_insert_of_mem hdel)) hsend
  have hvprev : v ∈ H.prev u s := Finset.mem_filter.mpr ⟨hv, Or.inl hlt.le⟩
  exact hcond v hvprev (hH.wf.rf_some hrf).2 hrf

/-- No protected event is deleted by a revisit allowed by the guards. -/
theorem prot_not_del (hH : H.Inv M P) (hg : RevGuard tie H r s)
    (hread : ∀ r', H.G.rf r' ≠ some (.snd s)) {x : Ev Q} (hx : H.Prot x) :
    x ∉ H.del r s := by
  intro hd
  obtain ⟨-, -, hrx, hn⟩ := mem_del.mp hd
  obtain ⟨x', y, hxx', hy⟩ := hx
  obtain ⟨u, v, hxu, hvu, hru⟩ := hH.find_bw hrx hxx' hy
  exact hn (TransGen.trans_right hxu (bw_porf hH hg hread hvu hru))

/-- The revisited receive is not protected. -/
theorem not_prot_r (hH : H.Inv M P) (hg : RevGuard tie H r s)
    (hread : ∀ r', H.G.rf r' ≠ some (.snd s)) : ¬ H.Prot r := by
  rintro ⟨x', y, hrx, hy⟩
  have hxs : x'.IsSend := (hH.wf.rf_match _ _ hy.1.2).isSend
  rcases hrx.cases_head with rfl | ⟨w, hrw, hwx⟩
  · exact Lab.IsSend.not_isRecv hxs hg.recv
  · have hpo : H.pos r < H.pos w := by
      rcases hrw with h | h
      · exact hH.pos_lt h
      · exact absurd (hH.wf.rf_match _ _ h.2).isSend fun h' => Lab.IsSend.not_isRecv h' hg.recv
    obtain ⟨u, v, hwu, hvu, hru⟩ := hH.find_bw hpo hwx hy
    exact hg.nporf (TransGen.head' hrw (ReflTransGen.trans hwu
      (TransGen.to_reflTransGen (bw_porf hH hg hread hvu hru))))


/-! ### Line 22 and `Previous` -/

/-- Line 22 with Q9: if a deleted or revisited receive `y` reads the send `x'`, then `x'` is in
`Previous(y)` (the tie-break returns a send of its argument). -/
theorem RevCond.src_mem_prev (hT : TieQ9 M tie) (hH : H.Inv M P) {y x' : Ev Q}
    (h : RevCond tie H y s) (hrf : H.G.rf y = some (.snd x')) : x' ∈ H.prev y s := by
  have hyR : y.IsRecv := (hH.wf.rf_some hrf).2
  have hnd : ¬ y.IsND := Lab.IsRecv.not_isND hyR
  unfold RevCond at h
  by_cases hnb : y.IsRecvNB
  · simp only [hnb, ↓reduceIte, hrf] at h
    cases h
  · have hb : y.IsRecvB := (Lab.IsRecv.recvB_or_recvNB hyR).resolve_right hnb
    simp only [hnb, hnd, hb, ↓reduceIte] at h
    obtain ⟨s', hs', ht⟩ := h
    rw [hrf] at hs'
    cases hs'
    have hS : ((H.G.restrict (H.prev y s)).remove {y}).Supp :=
      (hH.wf.supp.restrict _).restrict _
    obtain ⟨s'', hs''X, -, hid⟩ := hT.1 _ _ _ hS ht
    have hs''E := (mem_S _).mp hs''X
    simp only [Graph.remove, restrict_events, Finset.mem_inter, Finset.mem_sdiff] at hs''E
    have hx'E : x' ∈ H.G.events := hH.wf.rf_mem _ _ hrf
    obtain ⟨ht', hi'⟩ := Prod.mk.inj hid
    have : s'' = x' := hH.wf.eq_of_tid_idx hs''E.1.1.1 hx'E ht' hi'
    rw [← this]
    exact hs''E.1.1.2

/-! ### Adding an event -/

omit [Membership Val Q] in
/-- Steps of causality survive the addition of a fresh event. -/
theorem porfStep_add {G : Graph Q} {e : Ev Q} (he : e ∉ G.events) {src : Option (Src Q)}
    {out : Option Val} {a b : Ev Q} (h : G.porfStep a b) : (G.add e src out).porfStep a b := by
  rcases h with h | h
  · exact Or.inl ⟨Finset.mem_insert_of_mem h.1, Finset.mem_insert_of_mem h.2.1, h.2.2⟩
  · have hbe : b ≠ e := fun h' => he (h' ▸ h.1)
    refine Or.inr ⟨Finset.mem_insert_of_mem h.1, ?_⟩
    rw [add_rf, Function.update_of_ne hbe]
    exact h.2

omit [Membership Val Q] in
/-- Causality survives the addition of a fresh event. -/
theorem porf_add {G : Graph Q} {e : Ev Q} (he : e ∉ G.events) {src : Option (Src Q)}
    {out : Option Val} {a b : Ev Q} (h : G.porf a b) : (G.add e src out).porf a b := by
  induction h with
  | single h => exact .single (porfStep_add he h)
  | tail _ h ih => exact .tail ih (porfStep_add he h)

omit [Membership Val Q] in
/-- Positions of old events are unchanged by an addition. -/
theorem pos_add {c : Config Q} {e x : Ev Q} {src : Option (Src Q)} {out : Option Val}
    (hx : x ∈ c.order) : (c.add e src out).pos x = c.pos x := by
  simp only [pos, add, List.idxOf_append_of_mem hx]

/-- Protection survives the addition of a fresh event. -/
theorem Prot.add {c : Config Q} (hc : c.Inv M P) {e x : Ev Q} (he : e ∉ c.G.events)
    {src : Option (Src Q)} {out : Option Val} (h : c.Prot x) : (c.add e src out).Prot x := by
  obtain ⟨x', y, hxx', ⟨hrf, hlt⟩⟩ := h
  refine ⟨x', y, ?_, ⟨?_, ?_⟩⟩
  · exact rtg_lift (fun _ => True) hxx' (fun _ _ => trivial) fun u v h _ _ => porfStep_add he h
  · have hye : y ≠ e := fun h' => he (h' ▸ hrf.1)
    refine ⟨Finset.mem_insert_of_mem hrf.1, ?_⟩
    change Function.update c.G.rf e src y = _
    rw [Function.update_of_ne hye]
    exact hrf.2
  · have hy := (hc.mem y).mpr hrf.1
    have hx := (hc.mem x').mpr (hc.wf.rf_mem _ _ hrf.2)
    rw [pos_add hy, pos_add hx]
    exact hlt

/-! ### The revisit successor -/

omit [Membership Val Q] in
/-- The source of a kept event other than `r` is unchanged by the revisit; `r` reads `s`. -/
theorem revisitCfg_rf {z : Ev Q} (hz : z ∈ H.G.events) (hzd : z ∉ H.del r s) :
    (H.revisitCfg r s).G.rf z = if z = r then some (.snd s) else H.G.rf z := by
  simp only [revisitCfg, Graph.revisit, restrict_rf, setRF_rf, Finset.mem_sdiff, hz, hzd,
    not_false_eq_true, and_self, ↓reduceIte]
  by_cases hzr : z = r
  · subst hzr
    simp
  · simp [hzr]

omit [Membership Val Q] in
/-- Steps of causality between kept events, into an event other than `r`, survive the
revisit. -/
theorem porfStep_revisitCfg {a b : Ev Q} (h : H.G.porfStep a b) (ha : a ∈ H.G.events)
    (hb : b ∈ H.G.events) (had : a ∉ H.del r s) (hbd : b ∉ H.del r s) (hbr : b ≠ r) :
    (H.revisitCfg r s).G.porfStep a b := by
  have ha' := mem_revisitCfg_events.mpr ⟨ha, had⟩
  have hb' := mem_revisitCfg_events.mpr ⟨hb, hbd⟩
  rcases h with h | h
  · exact Or.inl ⟨ha', hb', h.2.2⟩
  · refine Or.inr ⟨hb', ?_⟩
    rw [revisitCfg_rf hb hbd]
    simpa [hbr] using h.2

omit [Membership Val Q] in
/-- The order of the revisit successor: the kept events other than `s` in their old order,
then `s`. -/
theorem revisitCfg_order : (H.revisitCfg r s).order =
    H.order.filter (fun d => decide (d ∉ H.del r s ∧ d ≠ s)) ++ [s] := rfl

/-- Kept events other than `s` keep their relative order in the revisit successor. -/
theorem revisitCfg_pos_lt_iff (hH : H.Inv M P) {a b : Ev Q} (ha : a ∈ H.G.events)
    (hb : b ∈ H.G.events) (had : a ∉ H.del r s) (hbd : b ∉ H.del r s) (has : a ≠ s)
    (hbs : b ≠ s) : (H.revisitCfg r s).pos a < (H.revisitCfg r s).pos b ↔ H.pos a < H.pos b := by
  set f := fun d => decide (d ∉ H.del r s ∧ d ≠ s) with hf
  have hao : a ∈ H.order := (hH.mem a).mpr ha
  have hbo : b ∈ H.order := (hH.mem b).mpr hb
  have haf : a ∈ H.order.filter f := List.mem_filter.mpr ⟨hao, by simp [hf, had, has]⟩
  have hbf : b ∈ H.order.filter f := List.mem_filter.mpr ⟨hbo, by simp [hf, hbd, hbs]⟩
  have hndf : (H.order.filter f).Nodup := hH.nodup.filter _
  simp only [pos, revisitCfg_order, ← hf, List.idxOf_append_of_mem haf,
    List.idxOf_append_of_mem hbf]
  rw [idxOf_lt_iff_sublist hndf haf hbf, idxOf_lt_iff_sublist hH.nodup hao hbo]
  constructor
  · exact fun h => h.trans List.filter_sublist
  · intro h
    have := h.filter f
    simpa [hf, had, has, hbd, hbs] using this

/-- In the revisit successor, every kept event other than `s` comes before `s`. -/
theorem revisitCfg_pos_lt_s {a : Ev Q} (hH : H.Inv M P) (ha : a ∈ H.G.events)
    (had : a ∉ H.del r s) (has : a ≠ s) :
    (H.revisitCfg r s).pos a < (H.revisitCfg r s).pos s := by
  set f := fun d => decide (d ∉ H.del r s ∧ d ≠ s) with hf
  have haf : a ∈ H.order.filter f :=
    List.mem_filter.mpr ⟨(hH.mem a).mpr ha, by simp [hf, had, has]⟩
  have hsf : s ∉ H.order.filter f := fun h => by simpa [hf] using (List.mem_filter.mp h).2
  simp only [pos, revisitCfg_order, ← hf, List.idxOf_append_of_mem haf,
    List.idxOf_append_of_notMem hsf, List.idxOf_cons_self, add_zero]
  exact List.idxOf_lt_length_of_mem haf

/-- In the revisit successor `r` reads `s` backward. -/
theorem revisitCfg_bwRead (hH : H.Inv M P) (hg : RevGuard tie H r s) (hrs : r ≠ s) :
    (H.revisitCfg r s).BwRead r s := by
  have hrd : r ∉ H.del r s := fun h => lt_irrefl _ (mem_del.mp h).2.2.1
  refine ⟨⟨mem_revisitCfg_events.mpr ⟨hg.mem, hrd⟩, ?_⟩, revisitCfg_pos_lt_s hH hg.mem hrd hrs⟩
  rw [revisitCfg_rf hg.mem hrd]
  simp

/-- Protection survives a revisit allowed by the guards, for an unread `po`-maximal send. -/
theorem Prot.revisit (hT : TieQ9 M tie) (hH : H.Inv M P) (hg : RevGuard tie H r s)
    (hs : s ∈ H.G.events) (hread : ∀ r', H.G.rf r' ≠ some (.snd s)) {x : Ev Q} (hx : H.Prot x) :
    x ∈ (H.revisitCfg r s).G.events ∧ (H.revisitCfg r s).Prot x := by
  have hrs : r ≠ s := fun h => Lab.IsSend.not_isRecv hg.smatch.isSend (h ▸ hg.recv)
  have hkeep : ∀ z, H.Prot z → z ∈ H.G.events ∧ z ∉ H.del r s ∧ z ≠ r := fun z hz =>
    ⟨hz.mem hH, prot_not_del hH hg hread hz, fun h => not_prot_r hH hg hread (h ▸ hz)⟩
  refine ⟨mem_revisitCfg_events.mpr ⟨(hkeep x hx).1, (hkeep x hx).2.1⟩, ?_⟩
  obtain ⟨x', y, hxx', ⟨hrf, hlt⟩⟩ := hx
  have hx'E : x' ∈ H.G.events := hH.wf.rf_mem _ _ hrf.2
  have hx's : x' ≠ s := fun h => hread y (h ▸ hrf.2)
  have hprotx' : H.Prot x' := ⟨x', y, .refl, ⟨hrf, hlt⟩⟩
  have hlift : ∀ {a b : Ev Q}, ReflTransGen H.G.porfStep a b →
      (∀ z, ReflTransGen H.G.porfStep z b → z ∈ H.G.events ∧ z ∉ H.del r s ∧ z ≠ r) →
      ReflTransGen (H.revisitCfg r s).G.porfStep a b := fun h hQ =>
    rtg_lift (fun z => z ∈ H.G.events ∧ z ∉ H.del r s ∧ z ≠ r) h hQ
      fun u v huv hu hv => porfStep_revisitCfg huv hu.1 hv.1 hu.2.1 hv.2.1 hv.2.2
  by_cases hy : y ∈ insert r (H.del r s)
  · -- the reader of `x'` is revisited or deleted: `x'` is causally before `s`
    have hmem := RevCond.src_mem_prev hT hH (hg.cond y hy) hrf.2
    have hx's' : H.G.porf x' s := by
      rcases (Finset.mem_filter.mp hmem).2 with h | h
      · exact absurd h (not_le.mpr hlt)
      · exact h
    have hxs : ReflTransGen H.G.porfStep x s := hxx'.trans hx's'.to_reflTransGen
    refine ⟨s, r, hlift hxs fun z hz => ?_, revisitCfg_bwRead hH hg hrs⟩
    rcases reflTransGen_iff_eq_or_transGen.mp hz with rfl | hz
    · exact ⟨hs, fun h => (mem_del.mp h).2.1 rfl, hrs.symm⟩
    · refine ⟨(hH.wf.mem_of_porf hz).1, fun h => (mem_del.mp h).2.2.2 hz, ?_⟩
      rintro rfl
      exact hg.nporf hz
  · -- the reader of `x'` is kept: the backward read survives
    have hyr : y ≠ r := fun h => hy (h ▸ Finset.mem_insert_self _ _)
    have hyd : y ∉ H.del r s := fun h => hy (Finset.mem_insert_of_mem h)
    have hys : y ≠ s := fun h => Lab.IsSend.not_isRecv hg.smatch.isSend
      (h ▸ (hH.wf.rf_some hrf.2).2)
    refine ⟨x', y, hlift hxx' fun z hz => hkeep z ⟨x', y, hz, ⟨hrf, hlt⟩⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · exact mem_revisitCfg_events.mpr ⟨hrf.1, hyd⟩
    · rw [revisitCfg_rf hrf.1 hyd]
      simpa [hyr] using hrf.2
    · exact (revisitCfg_pos_lt_iff hH hrf.1 hx'E hyd (hkeep x' hprotx').2.1 hys hx's).mpr hlt


/-- A `porf` path into the revisiting send survives the revisit. -/
theorem porf_revisit_to_s (hH : H.Inv M P) (hg : RevGuard tie H r s) (hs : s ∈ H.G.events)
    {a : Ev Q} (has : H.G.porf a s) : (H.revisitCfg r s).G.porf a s := by
  have hrs : r ≠ s := fun h => Lab.IsSend.not_isRecv hg.smatch.isSend (h ▸ hg.recv)
  have hQ : ∀ z, ReflTransGen H.G.porfStep z s → z ∈ H.G.events ∧ z ∉ H.del r s ∧ z ≠ r :=
    fun z hz => by
      rcases reflTransGen_iff_eq_or_transGen.mp hz with rfl | hz
      · exact ⟨hs, fun h => (mem_del.mp h).2.1 rfl, hrs.symm⟩
      · refine ⟨(hH.wf.mem_of_porf hz).1, fun h => (mem_del.mp h).2.2.2 hz, ?_⟩
        rintro rfl
        exact hg.nporf hz
  obtain ⟨w, haw, hws⟩ := TransGen.head'_iff.mp has
  refine TransGen.head' (porfStep_revisitCfg haw (hQ a (.head haw hws)).1 (hQ w hws).1
    (hQ a (.head haw hws)).2.1 (hQ w hws).2.1 (hQ w hws).2.2) ?_
  exact rtg_lift (fun z => z ∈ H.G.events ∧ z ∉ H.del r s ∧ z ≠ r) hws hQ
    fun u v huv hu hv => porfStep_revisitCfg huv hu.1 hv.1 hu.2.1 hv.2.1 hv.2.2

/-- `porf` paths into a protected event survive a revisit allowed by the guards. -/
theorem porf_revisit_of_prot (hH : H.Inv M P) (hg : RevGuard tie H r s)
    (hread : ∀ r', H.G.rf r' ≠ some (.snd s)) {a b : Ev Q} (hb : H.Prot b)
    (hab : H.G.porf a b) : (H.revisitCfg r s).G.porf a b := by
  obtain ⟨x', y, hbx', hy⟩ := hb
  have hQ : ∀ z, ReflTransGen H.G.porfStep z b → z ∈ H.G.events ∧ z ∉ H.del r s ∧ z ≠ r :=
    fun z hz => by
      have hp : H.Prot z := ⟨x', y, hz.trans hbx', hy⟩
      exact ⟨hp.mem hH, prot_not_del hH hg hread hp, fun h => not_prot_r hH hg hread (h ▸ hp)⟩
  obtain ⟨w, haw, hwb⟩ := TransGen.head'_iff.mp hab
  refine TransGen.head' (porfStep_revisitCfg haw (hQ a (.head haw hwb)).1 (hQ w hwb).1
    (hQ a (.head haw hwb)).2.1 (hQ w hwb).2.1 (hQ w hwb).2.2) ?_
  exact rtg_lift (fun z => z ∈ H.G.events ∧ z ∉ H.del r s ∧ z ≠ r) hwb hQ
    fun u v huv hu hv => porfStep_revisitCfg huv hu.1 hv.1 hu.2.1 hv.2.1 hv.2.2

end Config

open Config

/-! ### Steps -/

variable {c c' : Config Q}

/-- Protection is preserved by every algorithmic step, and a protected event stays in the
graph. -/
theorem StepM.prot (hT : TieQ9 M tie) (h : StepM M tie P c c') (hc : c.Inv M P) {x : Ev Q}
    (hx : c.Prot x) : x ∈ c'.G.events ∧ c'.Prot x := by
  cases h with
  | nr h =>
    obtain ⟨t, ht⟩ := exists_nextEv_of_nextP h.1
    have he := hc.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv ht)
    exact ⟨Finset.mem_insert_of_mem (hx.mem hc), hx.add hc he⟩
  | revisit hn hS hg hcons =>
    obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hn
    have he := hc.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv ht)
    obtain ⟨h1, h2, -⟩ := addSend_facts hc ht
    exact Prot.revisit hT (hc.addSend ht hS) hg h1 h2 (hx.add hc he)

/-- A protected event is not deleted by a revisit step. -/
theorem StepM.not_del_of_prot {e r x : Ev Q} (hc : c.Inv M P) (hn : M.nextP P c.G = some e)
    (hS : e.IsSend) (hg : RevGuard tie (c.add e none none) r e) (hx : c.Prot x) :
    x ∉ (c.add e none none).del r e := by
  obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hn
  have he := hc.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv ht)
  obtain ⟨-, h2, -⟩ := addSend_facts hc ht
  exact prot_not_del (hc.addSend ht hS) hg h2 (hx.add hc he)

/-- The send of a revisit step is read backward, hence protected, in the successor. -/
theorem StepM.revisit_prot {e r : Ev Q} (hc : c.Inv M P) (hn : M.nextP P c.G = some e)
    (hS : e.IsSend) (hg : RevGuard tie (c.add e none none) r e) :
    ((c.add e none none).revisitCfg r e).Prot e := by
  obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hn
  have hre : r ≠ e := fun h => Lab.IsSend.not_isRecv hS (h ▸ hg.recv)
  exact ⟨e, r, .refl, revisitCfg_bwRead (hc.addSend ht hS) hg hre⟩

/-- `porf` paths into a protected event survive every algorithmic step. -/
theorem StepM.porf_of_prot (h : StepM M tie P c c') (hc : c.Inv M P) {a b : Ev Q}
    (hb : c.Prot b) (hab : c.G.porf a b) : c'.G.porf a b := by
  cases h with
  | nr h =>
    obtain ⟨t, ht⟩ := exists_nextEv_of_nextP h.1
    have he := hc.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv ht)
    exact porf_add he hab
  | revisit hn hS hg hcons =>
    obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hn
    have he := hc.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv ht)
    obtain ⟨-, h2, -⟩ := addSend_facts hc ht
    exact porf_revisit_of_prot (hc.addSend ht hS) hg h2 (hb.add hc he)
      (porf_add he hab)

/-- Along a sequence of algorithmic steps, a protected event stays protected and in the graph;
paths into it survive. -/
theorem StepSeq.prot (hT : TieQ9 M tie) {S : List (Config Q)} {d : Config Q}
    (h : StepSeq M tie P c S d) (hc : c.Inv M P) {x : Ev Q} (hx : c.Prot x) :
    (∀ d' ∈ S, x ∈ d'.G.events ∧ d'.Prot x) ∧ x ∈ d.G.events ∧ d.Prot x := by
  induction h with
  | nil c => exact ⟨fun _ h => absurd h List.not_mem_nil, hx.mem hc, hx⟩
  | cons hs _ ih =>
    obtain ⟨h1, h2⟩ := hs.prot hT hc hx
    obtain ⟨ih1, ih2⟩ := ih (hs.inv hc) h2
    refine ⟨fun d' hd' => ?_, ih2⟩
    rcases List.mem_cons.mp hd' with rfl | hd'
    · exact ⟨h1, h2⟩
    · exact ih1 d' hd'

/-- **Lemma A.17** (`revisit_send_persists`). After a revisit step by the send `s` from a
configuration with the invariant (every reachable one, `ReachM.sound`), every configuration of
every later sequence of algorithmic steps contains `s`, and `s` stays protected there (so no
later revisit deletes it: `StepM.not_del_of_prot`). For every model and every tie-break with
Q9. -/
theorem revisit_send_persists (hT : TieQ9 M tie) {r s : Ev Q} {S : List (Config Q)}
    {d : Config Q} (hc : c.Inv M P) (hn : M.nextP P c.G = some s) (hS : s.IsSend)
    (hg : RevGuard tie (c.add s none none) r s)
    (hcons : M.cons ((c.add s none none).revisitCfg r s).G)
    (h : StepSeq M tie P ((c.add s none none).revisitCfg r s) S d) :
    (∀ d' ∈ S, s ∈ d'.G.events ∧ d'.Prot s) ∧ s ∈ d.G.events := by
  have hc' := (StepM.revisit hn hS hg hcons).inv hc
  obtain ⟨h1, h2, -⟩ := h.prot hT hc' (StepM.revisit_prot hc hn hS hg)
  exact ⟨h1, h2⟩

end Must

#print axioms Must.rtg_cross
#print axioms Must.idxOf_lt_iff_sublist
#print axioms Must.Config.prot_not_del
#print axioms Must.Config.not_prot_r
#print axioms Must.Config.RevCond.src_mem_prev
#print axioms Must.Config.Prot.revisit
#print axioms Must.Config.porf_revisit_to_s
#print axioms Must.Config.porf_revisit_of_prot
#print axioms Must.StepM.prot
#print axioms Must.StepM.not_del_of_prot
#print axioms Must.StepM.revisit_prot
#print axioms Must.StepM.porf_of_prot
#print axioms Must.StepSeq.prot
#print axioms Must.revisit_send_persists
