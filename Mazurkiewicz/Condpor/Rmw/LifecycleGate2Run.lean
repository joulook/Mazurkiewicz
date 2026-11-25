import Mazurkiewicz.Condpor.Rmw.LifecycleGate2Adj

/-!
# Gate clause 2, part 3a: the run list (LC2-b, continuation 3)

Machine-independent. For a graph `G` with a linearization `L` in which completed pairs are
adjacent:

* `SubLin G l`: `l` lists some events of `G`, all its writes among them, and every SC edge
  between members of `l` goes forward in `l`. Then the source of every read of `l` is the
  last earlier write of `l` to its location (`SubLin.rf_eq`) and `co x` is the list of the
  writes to `x` in the order of `l` (`SubLin.co_eq`): the two facts the builder `GB.Ok`
  states of its own list.
* The *tail* events (`IsTail`): a read of a non-data location followed by a `block`, and that
  `block` (the final waits that the machine emits in `finalize`). An *assumption pair*
  (`AsmPair`): a read of a data location followed by a `block`.
* `RunList P X G l`: `SubLin G l`, the members of `l` are exactly the non-tail events, every
  completed pair of `X` and every assumption pair is adjacent in `l`.
* `exists_runList`: such a list exists. Built from `L` with the key `2·pos e`, except that the
  `block` of an assumption pair gets `2·pos p + 1` (it moves to just after its read `p`).
-/

namespace Condpor

namespace Life

namespace Sem

open _root_.List

/-! ### Lists -/

theorem before_of_pre_before {L : List TEv} {e a b : TEv} (he : e ∈ L)
    (h : (pre L e).Before a b) : L.Before a b := by
  obtain ⟨post, hp⟩ := pre_split he
  rw [hp]
  obtain ⟨ha, hb, hlt⟩ := h
  refine ⟨mem_append_left _ ha, mem_append_left _ hb, ?_⟩
  rw [idxOf_append_of_mem ha, idxOf_append_of_mem hb]; exact hlt

theorem mem_pre_of_before {L : List TEv} (hL : L.Nodup) {e w : TEv} (h : L.Before w e) :
    w ∈ pre L e := by
  obtain ⟨post, hp⟩ := pre_split h.2.1
  have hw := h.1
  by_contra hn
  rw [hp] at hw
  rcases mem_append.mp hw with hw | hw
  · exact hn hw
  · rcases mem_cons.mp hw with hw | hw
    · exact h.ne hw
    · have hn' : (pre L e ++ [e] ++ post).Nodup := by rw [hp] at hL; simpa using hL
      have := before_append_of_mem hn' (a := e) (by simp) hw
      have hh : pre L e ++ [e] ++ post = L := by
        rw [List.append_assoc, List.singleton_append]; exact hp.symm
      rw [hh] at this
      exact this.asymm h

theorem pairwise_before_self {m : List TEv} (hm : m.Nodup) : m.Pairwise (m.Before) := by
  induction m with
  | nil => exact Pairwise.nil
  | cons a m ih =>
    have ha := (nodup_cons.mp hm).1
    refine pairwise_cons.mpr ⟨fun b hb => before_cons_self hb (fun e => ha (e ▸ hb)), ?_⟩
    exact (ih (nodup_cons.mp hm).2).imp (fun h => before_cons_of_before ha h)

/-- Two lists without repetition, with the same members, both ordered by `l`: equal. -/
theorem eq_of_pairwise_before {l : List TEv} :
    ∀ m₁ m₂ : List TEv, m₁.Nodup → m₂.Nodup → (∀ e, e ∈ m₁ ↔ e ∈ m₂) →
      m₁.Pairwise (l.Before) → m₂.Pairwise (l.Before) → m₁ = m₂
  | [], [], _, _, _, _, _ => rfl
  | [], b :: _, _, _, h, _, _ => absurd ((h b).mpr mem_cons_self) (by simp)
  | a :: _, [], _, _, h, _, _ => absurd ((h a).mp mem_cons_self) (by simp)
  | a :: t₁, b :: t₂, h1, h2, h, p1, p2 => by
    have hab : a = b := by
      by_contra hne
      have ha : a ∈ t₂ := ((mem_cons.mp ((h a).mp mem_cons_self)).resolve_left hne)
      have hb : b ∈ t₁ := ((mem_cons.mp ((h b).mpr mem_cons_self)).resolve_left (Ne.symm hne))
      exact ((pairwise_cons.mp p1).1 b hb).asymm ((pairwise_cons.mp p2).1 a ha)
    subst hab
    have ha1 := (nodup_cons.mp h1).1
    have ha2 := (nodup_cons.mp h2).1
    refine congrArg _ (eq_of_pairwise_before t₁ t₂ (nodup_cons.mp h1).2 (nodup_cons.mp h2).2
      (fun e => ?_) (pairwise_cons.mp p1).2 (pairwise_cons.mp p2).2)
    constructor
    · intro he
      have hne : e ≠ a := fun h' => ha1 (h' ▸ he)
      exact (mem_cons.mp ((h e).mp (mem_cons_of_mem _ he))).resolve_left hne
    · intro he
      have hne : e ≠ a := fun h' => ha2 (h' ▸ he)
      exact (mem_cons.mp ((h e).mpr (mem_cons_of_mem _ he))).resolve_left hne

/-! ### Sub-linearizations -/

/-- `l` lists some events of `G` (all writes among them); every SC edge between members of
`l` goes forward in `l`. -/
structure SubLin (G : Graph) (l : List TEv) : Prop where
  nodup : l.Nodup
  sub : ∀ e ∈ l, e ∈ G.events
  writes : ∀ e ∈ G.events, e.IsWrite → e ∈ l
  fwd : ∀ a ∈ l, ∀ b ∈ l, G.scStep (.th a) (.th b) → l.Before a b

section

variable {G : Graph} {l : List TEv}

theorem SubLin.mem_co (hG : G.Wf) (hl : SubLin G l) {x : Loc} {y : TEv} (hy : y ∈ l)
    (hw : writesB x y = true) : y ∈ G.co x :=
  (hG.co_mem x y).mpr ⟨hl.sub y hy, writesB_iff.mp hw⟩

/-- The source of a read of `l` is the last earlier write of `l` to its location. -/
theorem SubLin.rf_eq (hG : G.Wf) (hl : SubLin G l) {e : TEv} (he : e ∈ l) {x : Loc}
    (hx : e.act = .read x) : G.rf e = some (lastW (pre l e) x) := by
  have heG := hl.sub e he
  obtain ⟨src, hs, hsw⟩ := hG.rf_read e heG x hx
  rw [hs]
  congr 1
  have hpn : (pre l e).Nodup := hl.nodup.sublist (pre_sublist _ _)
  have hpl : ∀ y ∈ pre l e, y ∈ l := fun y hy => (pre_sublist l e).subset hy
  cases src with
  | init =>
    have hnil : (pre l e).filter (writesB x) = [] := by
      apply eq_nil_iff_forall_not_mem.mpr
      intro y hy
      obtain ⟨hy1, hy2⟩ := mem_filter.mp hy
      have hyco := hl.mem_co hG (hpl y hy1) hy2
      have hfr : G.scStep (.th e) (.th y) :=
        Or.inr (Or.inr (Or.inr ⟨e, y, x, rfl, rfl, heG, hx, hyco, Or.inl hs⟩))
      exact (hl.fwd e he y (hpl y hy1) hfr).asymm (before_of_pre hl.nodup he hy1)
    simp [lastW, hnil]
  | th w =>
    obtain ⟨hwG, v, hwv⟩ := hsw
    have hwl : w ∈ l := hl.writes w hwG (by simp [TEv.IsWrite, hwv, Act.IsWrite])
    have hrf : G.scStep (.th w) (.th e) := Or.inr (Or.inl ⟨e, rfl, heG, hs⟩)
    have hwpre : w ∈ pre l e := mem_pre_of_before hl.nodup (hl.fwd w hwl e he hrf)
    have hwx : writesB x w = true := writesB_iff.mpr ⟨v, hwv⟩
    have hwf : w ∈ (pre l e).filter (writesB x) := mem_filter.mpr ⟨hwpre, hwx⟩
    have hfn : ((pre l e).filter (writesB x)).Nodup := hpn.filter _
    unfold lastW
    cases hz : ((pre l e).filter (writesB x)).getLast? with
    | none => rw [getLast?_eq_none_iff] at hz; rw [hz] at hwf; cases hwf
    | some z =>
      simp only
      congr 1
      by_contra hzw'
      have hzw : z ≠ w := fun h => hzw' h.symm
      have hzf := mem_of_getLast? hz
      obtain ⟨hz1, hz2⟩ := mem_filter.mp hzf
      have hzl := hpl z hz1
      have hzco := hl.mem_co hG hzl hz2
      have hwco := hl.mem_co hG hwl hwx
      rcases Before.total hzco hwco hzw with hb | hb
      · -- `z` co-before `w`: `z` before `w` in `l`; but `w` before `z` (the last)
        have h1 : l.Before z w := hl.fwd z hzl w hwl (Or.inr (Or.inr (Or.inl ⟨x, hb⟩)))
        obtain ⟨ys, hys⟩ := getLast?_eq_some_iff.mp hz
        have hwy : w ∈ ys := by
          have := hwf; rw [hys] at this
          rcases mem_append.mp this with h | h
          · exact h
          · exact absurd (mem_singleton.mp h) (Ne.symm hzw)
        have h2 : ((pre l e).filter (writesB x)).Before w z := by
          rw [hys]; rw [hys] at hfn; exact before_append_of_mem hfn hwy (by simp)
        have h3 := before_of_pre_before he (before_filter_iff.mp h2).1
        exact h1.asymm h3
      · -- `w` co-before `z`: from-read edge from `e` to `z`
        have hfr : G.scStep (.th e) (.th z) :=
          Or.inr (Or.inr (Or.inr ⟨e, z, x, rfl, rfl, heG, hx, hzco, Or.inr ⟨w, hs, hb⟩⟩))
        exact (hl.fwd e he z hzl hfr).asymm (before_of_pre hl.nodup he hz1)

/-- Coherence is the order of `l` on the writes. -/
theorem SubLin.co_eq (hG : G.Wf) (hl : SubLin G l) (x : Loc) :
    G.co x = l.filter (writesB x) := by
  have hn1 := hG.co_nodup x
  have hn2 : (l.filter (writesB x)).Nodup := hl.nodup.filter _
  have hmem : ∀ e, e ∈ G.co x ↔ e ∈ l.filter (writesB x) := by
    intro e
    rw [mem_filter, hG.co_mem, writesB_iff]
    constructor
    · rintro ⟨he, v, hv⟩
      exact ⟨hl.writes e he (by simp [TEv.IsWrite, hv, Act.IsWrite]), v, hv⟩
    · rintro ⟨he, v, hv⟩
      exact ⟨hl.sub e he, v, hv⟩
  refine eq_of_pairwise_before (l := l) _ _ hn1 hn2 hmem ?_ ?_
  · refine (pairwise_before_self hn1).imp_of_mem (fun {a b} ha hb h => ?_)
    exact hl.fwd a ((mem_filter.mp ((hmem a).mp ha)).1) b ((mem_filter.mp ((hmem b).mp hb)).1)
      (Or.inr (Or.inr (Or.inl ⟨x, h⟩)))
  · exact (pairwise_before_self hn2).imp (fun h => (before_filter_iff.mp h).1)

end

/-! ### Waits -/

/-- `p` is a read of `x` and `b` the `block` after it in its thread. -/
def WaitPair (G : Graph) (p b : TEv) (x : Loc) : Prop :=
  p ∈ G.events ∧ b ∈ G.events ∧ b.tid = p.tid ∧ b.idx = p.idx + 1 ∧ p.act = .read x ∧
    b.act = .block

/-- The events of a final wait at a lock or lifecycle location (emitted by `finalize`). -/
def IsTail (P : LProg) (G : Graph) (e : TEv) : Prop :=
  ∃ p b x, WaitPair G p b x ∧ P.isData x = false ∧ (e = p ∨ e = b)

/-- A failed assumption: the read of a data location and the `block` after it. -/
def AsmPair (P : LProg) (G : Graph) (p b : TEv) : Prop :=
  ∃ x, WaitPair G p b x ∧ P.isData x = true

/-- The run list: the non-tail events, in an SC order with adjacent completed pairs and
adjacent assumption pairs. -/
structure RunList (P : LProg) (X : XProgram) (G : Graph) (l : List TEv) : Prop where
  sub : SubLin G l
  mem : ∀ e, e ∈ l ↔ e ∈ G.events ∧ ¬ IsTail P G e
  rmw : ∀ r w, X.RMW G r w → ∃ l₁ l₂, l = l₁ ++ r :: w :: l₂
  asm : ∀ p b, AsmPair P G p b → ∃ l₁ l₂, l = l₁ ++ p :: b :: l₂

section

variable {P : LProg} {X : XProgram} {G : Graph}

theorem block_not_read {e : TEv} (h : e.act = .block) : ¬ e.IsRead := by
  simp [TEv.IsRead, h, Act.IsRead]

theorem block_not_write {e : TEv} (h : e.act = .block) : ¬ e.IsWrite := by
  simp [TEv.IsWrite, h, Act.IsWrite]

/-- An SC edge into a `block` is a po edge. -/
theorem scStep_into_block (hG : G.Wf) {a b : TEv} (hb : b.act = .block)
    (h : G.scStep (.th a) (.th b)) :
    a ∈ G.events ∧ b ∈ G.events ∧ a.tid = b.tid ∧ a.idx < b.idx := by
  rcases h with h | h | h | h
  · exact h
  · obtain ⟨e, he, heE, hrf⟩ := h
    cases he
    rw [hG.rf_none b (Or.inr (block_not_read hb))] at hrf; cases hrf
  · obtain ⟨x, hx⟩ := h
    obtain ⟨-, v, hv⟩ := (hG.co_mem x b).mp hx.2.1
    rw [hb] at hv; cases hv
  · obtain ⟨e, e', x, he, he', -, -, hco, -⟩ := h
    cases he; cases he'
    obtain ⟨-, v, hv⟩ := (hG.co_mem x b).mp hco
    rw [hb] at hv; cases hv

/-- An SC edge out of a `block` is a po edge. -/
theorem scStep_out_block (hG : G.Wf) {a b : TEv} (ha : a.act = .block)
    (h : G.scStep (.th a) (.th b)) :
    a ∈ G.events ∧ b ∈ G.events ∧ a.tid = b.tid ∧ a.idx < b.idx := by
  rcases h with h | h | h | h
  · exact h
  · obtain ⟨e, he, heE, hrf⟩ := h
    cases he
    obtain ⟨w, hw, hwt⟩ := hG.rf_read b heE _ (TEv.IsRead.exists_act (e := b) (by
      by_contra hn; rw [hG.rf_none b (Or.inr hn)] at hrf; cases hrf))
    rw [hrf] at hw; cases hw
    obtain ⟨-, v, hv⟩ := hwt
    rw [ha] at hv; cases hv
  · obtain ⟨x, hx⟩ := h
    obtain ⟨-, v, hv⟩ := (hG.co_mem x a).mp hx.1
    rw [ha] at hv; cases hv
  · obtain ⟨e, e', x, he, he', -, hex, -, -⟩ := h
    cases he; cases he'
    rw [ha] at hex; cases hex

theorem waitPair_pred_unique (hG : G.Wf) {p p' b : TEv} {x x' : Loc} (h : WaitPair G p b x)
    (h' : WaitPair G p' b x') : p = p' := by
  obtain ⟨hp, -, ht, hi, -⟩ := h
  obtain ⟨hp', -, ht', hi', -⟩ := h'
  exact hG.idx_inj p hp p' hp' (ht.symm.trans ht') (by omega)

theorem waitPair_succ_unique (hG : G.Wf) {p b b' : TEv} {x x' : Loc} (h : WaitPair G p b x)
    (h' : WaitPair G p b' x') : b = b' := by
  obtain ⟨-, hb, ht, hi, -⟩ := h
  obtain ⟨-, hb', ht', hi', -⟩ := h'
  exact hG.idx_inj b hb b' hb' (ht.trans ht'.symm) (by omega)

/-- The successor in its thread of an event of a wait pair is the `block`. -/
theorem waitPair_succ_eq (hG : G.Wf) {p b e : TEv} {x : Loc} (h : WaitPair G p b x)
    (he : e ∈ G.events) (ht : e.tid = p.tid) (hi : e.idx = p.idx + 1) : e = b :=
  hG.idx_inj e he b h.2.1 (ht.trans h.2.2.1.symm) (hi.trans h.2.2.2.1.symm)

end

/-! ### The key of the run list -/

open Classical in
/-- The key of an event: `2·pos e`, and `2·pos p + 1` for the `block` of an assumption pair
`(p, e)`. -/
noncomputable def rkey (P : LProg) (G : Graph) (L : List TEv) (e : TEv) : ℕ :=
  if h : ∃ p, AsmPair P G p e then 2 * L.idxOf h.choose + 1 else 2 * L.idxOf e

section

variable {P : LProg} {X : XProgram} {G : Graph} {L : List TEv}

theorem rkey_asm (hG : G.Wf) {p b : TEv} (h : AsmPair P G p b) :
    rkey P G L b = 2 * L.idxOf p + 1 := by
  have hex : ∃ p, AsmPair P G p b := ⟨p, h⟩
  have hc := hex.choose_spec
  obtain ⟨x, hx, -⟩ := h
  obtain ⟨x', hx', -⟩ := hc
  have := waitPair_pred_unique hG hx' hx
  simp only [rkey, hex, dite_true, this]

theorem rkey_not (h : ¬ ∃ p, AsmPair P G p e) : rkey P G L e = 2 * L.idxOf e := by
  simp only [rkey, h, dite_false]

theorem not_asm_of_not_block {e : TEv} (h : e.act ≠ .block) : ¬ ∃ p, AsmPair P G p e :=
  fun ⟨_, _, hw, _⟩ => h hw.2.2.2.2.2

/-- Along every SC edge the key increases (for a linearization `L`). -/
theorem rkey_lt (hG : G.Wf) (hL : IsLin G L) {a b : TEv} (h : G.scStep (.th a) (.th b)) :
    rkey P G L a < rkey P G L b := by
  have po_lt : ∀ {u v : TEv}, u ∈ G.events → v ∈ G.events → u.tid = v.tid → u.idx < v.idx →
      L.idxOf u < L.idxOf v := fun hu hv ht hi => (hL.2.2 _ _ (Or.inl ⟨hu, hv, ht, hi⟩)).2.2
  by_cases ha : ∃ p, AsmPair P G p a
  · obtain ⟨p, hp⟩ := ha
    obtain ⟨x, hpw, -⟩ := id hp
    obtain ⟨hpE, -, hpt, hpi, -, hab⟩ := hpw
    rw [rkey_asm hG hp]
    obtain ⟨-, hbE, htab, hiab⟩ := scStep_out_block hG hab h
    by_cases hb : ∃ q, AsmPair P G q b
    · obtain ⟨q, hq⟩ := hb
      obtain ⟨y, hqw, -⟩ := id hq
      obtain ⟨hqE, -, hqt, hqi, -⟩ := hqw
      rw [rkey_asm hG hq]
      have := po_lt hpE hqE (hpt.symm.trans (htab.trans hqt)) (by omega)
      omega
    · rw [rkey_not hb]
      have := po_lt hpE hbE (hpt.symm.trans htab) (by omega)
      omega
  · rw [rkey_not ha]
    by_cases hb : ∃ q, AsmPair P G q b
    · obtain ⟨q, hq⟩ := hb
      obtain ⟨y, hqw, -⟩ := id hq
      obtain ⟨hqE, -, hqt, hqi, -, hqb⟩ := hqw
      rw [rkey_asm hG hq]
      obtain ⟨haE, -, htab, hiab⟩ := scStep_into_block hG hqb h
      by_cases haq : a = q
      · subst haq; omega
      · have hlt : a.idx < q.idx := by
          by_contra hn
          exact haq (hG.idx_inj a haE q hqE (htab.trans hqt) (by omega))
        have := po_lt haE hqE (htab.trans hqt) hlt
        omega
    · rw [rkey_not hb]
      have := (hL.2.2 _ _ h).2.2
      omega

/-- Keys `2·pos e` are taken only by `e`; odd keys only by assumption blocks. -/
theorem rkey_cases (hG : G.Wf) (e : TEv) :
    (rkey P G L e = 2 * L.idxOf e ∧ ¬ ∃ p, AsmPair P G p e) ∨
      ∃ p, AsmPair P G p e ∧ rkey P G L e = 2 * L.idxOf p + 1 := by
  by_cases h : ∃ p, AsmPair P G p e
  · obtain ⟨p, hp⟩ := h
    exact Or.inr ⟨p, hp, rkey_asm hG hp⟩
  · exact Or.inl ⟨rkey_not h, h⟩

theorem idxOf_inj_ev (hL : IsLin G L) {a b : TEv} (ha : a ∈ G.events)
    (h : L.idxOf a = L.idxOf b) : a = b :=
  (List.idxOf_inj ((hL.2.1 a).mpr ha)).mp h

end

/-! ### Existence of the run list -/

theorem adj_of_keys {α : Type*} [DecidableEq α] {L : List α} {S : Finset α} {k : α → ℕ}
    (hn : L.Nodup) (hmem : ∀ e, e ∈ L ↔ e ∈ S) (hord : ∀ a ∈ S, ∀ b ∈ S, k a < k b → L.Before a b)
    {a b : α} (ha : a ∈ S) (hb : b ∈ S) (hab : k a < k b)
    (hout : ∀ e ∈ S, e ≠ a → e ≠ b → k e < k a ∨ k b < k e) :
    ∃ l₁ l₂, L = l₁ ++ a :: b :: l₂ := by
  have hrw : L.Before a b := hord a ha b hb hab
  obtain ⟨hr, hw, hlt⟩ := hrw
  have hwl := List.idxOf_lt_length_of_mem hw
  have hrl := List.idxOf_lt_length_of_mem hr
  have hsucc : L.idxOf b = L.idxOf a + 1 := by
    by_contra hne
    have hi : L.idxOf a + 1 < L.length := by omega
    have hidx := hn.idxOf_getElem (L.idxOf a + 1) hi
    have he : L[L.idxOf a + 1] ∈ L := List.getElem_mem hi
    have her : L[L.idxOf a + 1] ≠ a := fun e => by rw [e] at hidx; omega
    have hew : L[L.idxOf a + 1] ≠ b := fun e => by rw [e] at hidx; omega
    rcases hout _ ((hmem _).mp he) her hew with h | h
    · have := (hord _ ((hmem _).mp he) a ha h).2.2; omega
    · have := (hord b hb _ ((hmem _).mp he) h).2.2; omega
  refine ⟨L.take (L.idxOf a), L.drop (L.idxOf a + 2), ?_⟩
  conv_lhs => rw [← List.take_append_drop (L.idxOf a) L]
  congr 1
  rw [List.drop_eq_getElem_cons hrl, List.getElem_idxOf hrl,
    List.drop_eq_getElem_cons (by omega : L.idxOf a + 1 < L.length)]
  have : L[L.idxOf a + 1] = b := by
    have := List.getElem_idxOf hwl
    simp only [hsucc] at this
    exact this
  rw [this]

/-- **The run list exists.** -/
theorem exists_runList {P : LProg} {X : XProgram} {G : Graph} (hG : G.Wf) {L : List TEv}
    (hL : IsLin G L) (hadj : ∀ r w, X.RMW G r w → ∃ l₁ l₂, L = l₁ ++ r :: w :: l₂) :
    ∃ l, RunList P X G l := by
  classical
  let S := G.events.filter (fun e => ¬ IsTail P G e)
  obtain ⟨l, hn, hmem, hord⟩ := lin_key (rkey P G L) S
  have hmS : ∀ e, e ∈ S ↔ e ∈ G.events ∧ ¬ IsTail P G e := fun e => Finset.mem_filter
  have hfwd : ∀ a ∈ l, ∀ b ∈ l, G.scStep (.th a) (.th b) → l.Before a b := fun a ha b hb h =>
    hord a ((hmem a).mp ha) b ((hmem b).mp hb) (rkey_lt hG hL h)
  refine ⟨l, ⟨⟨hn, fun e he => ((hmS e).mp ((hmem e).mp he)).1, ?_, hfwd⟩,
    fun e => (hmem e).trans (hmS e), ?_, ?_⟩⟩
  · -- writes are not tail events
    intro e he hw
    refine (hmem e).mpr ((hmS e).mpr ⟨he, ?_⟩)
    rintro ⟨p, b, x, ⟨-, -, -, -, hpx, hbb⟩, -, rfl | rfl⟩
    · exact not_read_write (by simp [TEv.IsRead, hpx, Act.IsRead]) hw
    · exact block_not_write hbb hw
  · -- completed pairs
    intro r w hrw
    obtain ⟨hrE, hwE, hwt, hwi, hrR, hwW, -, -⟩ := id hrw
    have hrnb : r.act ≠ .block := fun h => block_not_read h hrR
    have hwnb : w.act ≠ .block := fun h => block_not_write h hwW
    have hrS : r ∈ S := (hmS r).mpr ⟨hrE, by
      rintro ⟨p, b, x, hpw, -, rfl | rfl⟩
      · exact hwnb (waitPair_succ_eq hG hpw hwE hwt hwi ▸ hpw.2.2.2.2.2)
      · exact hrnb hpw.2.2.2.2.2⟩
    have hwS : w ∈ S := (hmS w).mpr ⟨hwE, by
      rintro ⟨p, b, x, hpw, -, rfl | rfl⟩
      · exact not_read_write (by simp [TEv.IsRead, hpw.2.2.2.2.1, Act.IsRead]) hwW
      · exact hwnb hpw.2.2.2.2.2⟩
    obtain ⟨l₁, l₂, hl⟩ := hadj r w hrw
    have hpos : L.idxOf w = L.idxOf r + 1 := by rw [hl]; exact idxOf_imm l₁ (hl ▸ hL.1)
    have hkr : rkey P G L r = 2 * L.idxOf r := rkey_not (not_asm_of_not_block hrnb)
    have hkw : rkey P G L w = 2 * L.idxOf r + 2 := by
      rw [rkey_not (not_asm_of_not_block hwnb), hpos]; omega
    refine adj_of_keys hn hmem hord hrS hwS (by omega) (fun e heS her hew => ?_)
    have heE := ((hmS e).mp heS).1
    rcases rkey_cases (P := P) (L := L) hG e with ⟨hk, -⟩ | ⟨p, hp, hk⟩
    · have h1 : L.idxOf e ≠ L.idxOf r := fun h => her (idxOf_inj_ev hL heE h)
      have h2 : L.idxOf e ≠ L.idxOf w := fun h => hew (idxOf_inj_ev hL heE h)
      omega
    · obtain ⟨x, hpw, -⟩ := hp
      have h1 : L.idxOf p ≠ L.idxOf r := fun h => by
        have hpr := idxOf_inj_ev hL hpw.1 h
        rw [← hpr] at hwt hwi
        exact hew (waitPair_succ_eq hG hpw hwE hwt hwi).symm
      omega
  · -- assumption pairs
    intro p b hpb
    obtain ⟨x, hpw, hxd⟩ := id hpb
    obtain ⟨hpE, hbE, hbt, hbi, hpx, hbb⟩ := id hpw
    have hpnb : p.act ≠ .block := by rw [hpx]; simp
    have notTail : ∀ e, (e = p ∨ e = b) → ¬ IsTail P G e := by
      rintro e he ⟨p', b', x', hw', hx', he'⟩
      have hpp : p' = p := by
        rcases he with he | he <;> rcases he' with h | h
        · exact h.symm.trans he
        · exfalso; have := hw'.2.2.2.2.2; rw [← h, he, hpx] at this; cases this
        · exfalso; have := hw'.2.2.2.2.1; rw [← h, he, hbb] at this; cases this
        · have hw2 : WaitPair G p' b x' := by rw [← he, h]; exact hw'
          exact waitPair_pred_unique hG hw2 hpw
      have := hw'.2.2.2.2.1
      rw [hpp, hpx] at this
      cases this
      rw [hxd] at hx'; cases hx'
    have hpS : p ∈ S := (hmS p).mpr ⟨hpE, notTail p (Or.inl rfl)⟩
    have hbS : b ∈ S := (hmS b).mpr ⟨hbE, notTail b (Or.inr rfl)⟩
    have hkp : rkey P G L p = 2 * L.idxOf p := rkey_not (not_asm_of_not_block hpnb)
    have hkb : rkey P G L b = 2 * L.idxOf p + 1 := rkey_asm hG hpb
    refine adj_of_keys hn hmem hord hpS hbS (by omega) (fun e heS hep heb => ?_)
    have heE := ((hmS e).mp heS).1
    rcases rkey_cases (P := P) (L := L) hG e with ⟨hk, -⟩ | ⟨q, hq, hk⟩
    · have h1 : L.idxOf e ≠ L.idxOf p := fun h => hep (idxOf_inj_ev hL heE h)
      omega
    · obtain ⟨y, hqw, -⟩ := hq
      have h1 : L.idxOf q ≠ L.idxOf p := fun h => by
        have hqp := idxOf_inj_ev hL hqw.1 h
        subst hqp
        exact heb (waitPair_succ_unique hG hqw hpw)
      omega

end Sem

end Life

end Condpor
