import Mazurkiewicz.Trust.Terminate

/-!
# The backward step

Paper: Section 4.3 (Algorithm 3) and Appendix A, Def. A.13, A.14 with
Algorithm 5 (`Prev`, `MaxCompletion`), Proposition A.23 and Lemma A.24. Coq:
`trust/Prev.v` (`Completion`, `MaxCompletion`, `Prev_step`, `Prev`).

`Prev(G)` undoes the last step of the exploration that led to `G`, without
knowing the insertion order: it looks at `a = me(G)`.

* If `a` is a read whose source `e` is a thread write with `a <next e` and
  `a` is the only event causally after `e`, the last step was a revisit of `a`
  by `e`: remove `a` and `e`, and add back the deleted events, which are the
  events that `MaxCompletion` adds (Algorithm 5, lines 3-6).
* Otherwise the last step added `a`: remove it (line 7).

`MaxCompletion(G, e)` adds the next event again and again, each time in the
maximal way (a read reads from the last write of its location, a write goes
last in the coherence order of its location), until the next event is `e`
(lines 8-18).

How the text is read here.

* `Prev` is a partial function in the paper. Here it is a relation
  `PrevStep P G e k G'`, read "`Prev(G) = ⟨G', e, k⟩`" (Def. A.14: `G ⇝ G'`);
  it is a function by `PrevStep.det`, and it is defined on every well-formed
  consistent execution with a thread event of a bounded program
  (`exists_prevStep`).
* Line 7 of Algorithm 5 returns `⟨G \\ {e}, e, nr⟩` although `e` is bound only
  in the branch of line 4; the event removed is `a = me(G)` (as in Algorithm
  3 and in the proofs).
* `G \\ S` is the restriction of `G` to the events outside `S`.
* The loop of `MaxCompletion` is the reflexive-transitive closure of one
  step, `ComplStep`, ending in a graph whose next event is `e`.
  Algorithm 5 assigns `a ← next(G)` once, before the loop; the next event is
  meant to be taken again in every round (as in Algorithm 3 and in Coq's
  `Completion`), and `ComplStep` does so.
  Algorithm 3 ends `MaxCompletion` with `return G \\ {e}`, which is `G`, since
  `e` is not in `G`.
* Line 4 may bind `e` to `init`. Such a read falls under line 7: `a <next init`
  never holds.
* In the statements of Proposition A.23, Lemma A.24 and later, the paper
  writes `G ⇝* G_f` for a graph `G` obtained from `G_f` by backward steps.
  Here: `PrevReach P G_f G`.
* Proposition A.23 (S2) is about exclusive events and is out of scope. (S1)
  and (S3) are `PrevReach.s1` and `PrevReach.inv`; the latter also carries
  well-formedness and being an execution, which the paper has in its notion
  of graph.
-/

namespace Trust

open Program

variable {P : Program} {M : Model}

/-- `G \ S`: the graph without the events of `S`. -/
def Graph.remove (G : Graph) (S : Finset TEv) : Graph := G.restrict (G.events \ S)

/-- One round of the loop of `MaxCompletion(·, e)`: the next event is not `e`
and is added in the maximal way (Algorithm 5, lines 9-17). -/
def ComplStep (P : Program) (e : TEv) (G G' : Graph) : Prop :=
  ∃ a, P.IsNext G a ∧ a ≠ e ∧ G' = G.addMax a

/-- `MaxCompletion(G, e) = G'` (Algorithm 5, lines 8-18). -/
def MaxCompl (P : Program) (G : Graph) (e : TEv) (G' : Graph) : Prop :=
  Relation.ReflTransGen (ComplStep P e) G G' ∧ P.IsNext G' e

/-- `Prev(G) = ⟨G', e, k⟩` (Algorithm 5, lines 1-7; Def. A.14). -/
inductive PrevStep (P : Program) : Graph → TEv → Kind → Graph → Prop
  /-- lines 3-6: the last step was a revisit of `a` by `e` -/
  | rv {G G' : Graph} {a e : TEv} :
      G.IsMe (.th a) → a.IsRead → G.rf a = some (.th e) → nextLt a e →
      (∀ b, G.porf (.th e) b ↔ b = .th a) →
      MaxCompl P (G.remove {a, e}) e G' → PrevStep P G e (.rv a) G'
  /-- line 7: the last step added `a = me(G)` -/
  | nr {G : Graph} {a : TEv} :
      G.IsMe (.th a) →
      (¬ ∃ e, a.IsRead ∧ G.rf a = some (.th e) ∧ nextLt a e ∧
        ∀ b, G.porf (.th e) b ↔ b = .th a) →
      PrevStep P G a .nr (G.remove {a})

/-- The graphs obtained from `G_f` by backward steps (the paper's `G ⇝* G_f`). -/
def PrevReach (P : Program) (Gf G : Graph) : Prop :=
  Relation.ReflTransGen (fun G G' => ∃ e k, PrevStep P G e k G') Gf G

/-! ### Auxiliary facts on the maximal extension and on restrictions -/

namespace Graph

theorem addMax_events (G : Graph) (a : TEv) : (G.addMax a).events = insert a G.events := by
  unfold addMax
  split <;> rfl

theorem trace_addMax_of_ne {G : Graph} (hG : G.Wf) {a : TEv} (hidx : a.idx = G.cnt a.tid)
    {t : Tid} (ht : t ≠ a.tid) : (G.addMax a).trace t = G.trace t := by
  cases h : a.act with
  | read x =>
    rw [addMax_read h, trace_addRead hG hidx h (maxWrite_isWriteTo hG x)]
    simp [ht]
  | write x v =>
    have hw : a.IsWrite := by simp [TEv.IsWrite, h, Act.IsWrite]
    rw [addMax_write hw, trace_addWrite hG hidx hw (maxWrite_isWriteTo hG a.loc)]
    simp [ht]

theorem restrict_addMax {G : Graph} (hG : G.Wf) {a : TEv} (ha : a ∉ G.events) :
    (G.addMax a).restrict G.events = G := by
  unfold addMax
  split
  · exact restrict_addRead hG ha
  · exact restrict_addWrite hG ha

/-- The index of an event whose predecessors in its thread are kept, and
which is itself removed, is the count of its thread in the restriction. -/
theorem cnt_restrict_last {G : Graph} (hG : G.Wf) {s : Finset TEv} {e : TEv}
    (he : e ∈ G.events) (hes : e ∉ s)
    (hkeep : ∀ q ∈ G.events, q.tid = e.tid → q.idx < e.idx → q ∈ s)
    (hW : (G.restrict s).Wf) : (G.restrict s).cnt e.tid = e.idx := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨q, hq, ht, hi⟩ := hG.idx_contig e he _ hlt
    have hqs : q ∈ s := hkeep q hq ht (hi ▸ hlt)
    have := (hW.exists_idx_iff e.tid _).mp ⟨q, Finset.mem_inter.mpr ⟨hq, hqs⟩, ht, hi⟩
    exact Nat.lt_irrefl _ this
  · obtain ⟨q, hq, ht, hi⟩ := (hW.exists_idx_iff e.tid e.idx).mpr hlt
    have hq' := Finset.mem_inter.mp hq
    have : q = e := hG.idx_inj q hq'.1 e he ht hi
    exact hes (this ▸ hq'.2)

/-- The trace of a thread whose events and their sources are all kept. -/
theorem trace_restrict_of_thread {G : Graph} (hG : G.Wf) {s : Finset TEv} {t : Tid}
    (hkeep : ∀ q ∈ G.events, q.tid = t → q ∈ s)
    (hsrc : ∀ q ∈ G.events, q.tid = t → ∀ w, G.rf q = some w → w ∈ evSet s) :
    (G.restrict s).trace t = G.trace t := by
  unfold trace
  rw [cnt_restrict G hkeep]
  exact traceBefore_restrict_of_keep hG (Nat.le_refl _) (fun q hq ht _ => hkeep q hq ht)
    (fun q hq ht _ => hsrc q hq ht)

/-- Removing a set of events that is closed under causal successors leaves a
prefix. -/
theorem remove_prefixClosed {G : Graph} (hG : G.Wf) {S : Finset TEv}
    (hS : ∀ q ∈ S, ∀ b, G.porfStep (.th q) b → ∃ q' ∈ S, b = .th q') :
    Maz.PrefixClosed G.porfStep (evSet (G.events ∩ (G.events \ S))) := by
  intro x y hxy hy
  cases x with
  | init => trivial
  | th q =>
    have hq : q ∈ G.events := (hG.mem_of_porfStep hxy).1
    by_cases hqS : q ∈ S
    · obtain ⟨q', hq', rfl⟩ := hS q hqS y hxy
      have h' : q' ∈ G.events ∩ (G.events \ S) := hy
      exact absurd hq' (Finset.mem_sdiff.mp (Finset.mem_inter.mp h').2).2
    · exact Finset.mem_inter.mpr ⟨hq, Finset.mem_sdiff.mpr ⟨hq, hqS⟩⟩

theorem remove_isPrefixOf {G : Graph} (hG : G.Wf) {S : Finset TEv}
    (hS : ∀ q ∈ S, ∀ b, G.porfStep (.th q) b → ∃ q' ∈ S, b = .th q') :
    (G.remove S).IsPrefixOf G :=
  ⟨G.events \ S, remove_prefixClosed hG hS, rfl⟩

theorem addMax_rf_of_ne (G : Graph) {a q : TEv} (h : q ≠ a) : (G.addMax a).rf q = G.rf q := by
  unfold addMax
  split
  · rw [addRead_rf, Function.update_of_ne h]
  · rfl

/-- Only reads have a source. -/
theorem Wf.isRead_of_rf {G : Graph} (hG : G.Wf) {q : TEv} {w : Ev} (h : G.rf q = some w) :
    q.IsRead := by
  cases hact : q.act with
  | read x => simp [TEv.IsRead, hact, Act.IsRead]
  | write x v =>
    have := hG.rf_none q (Or.inr (by simp [TEv.IsWrite, hact, Act.IsWrite]))
    rw [this] at h
    cases h

end Graph

/-- An event of an execution is available in a restriction that removes it
and keeps its predecessors in its thread together with their sources. -/
theorem Program.mem_avail_restrict {G : Graph} (hG : G.Wf) (hE : P.Exec G) {s : Finset TEv}
    {e : TEv} (he : e ∈ G.events) (hes : e ∉ s)
    (hkeep : ∀ q ∈ G.events, q.tid = e.tid → q.idx < e.idx → q ∈ s)
    (hsrc : ∀ q ∈ G.events, q.tid = e.tid → q.idx < e.idx → ∀ w, G.rf q = some w →
      w ∈ Graph.evSet s)
    (hW : (G.restrict s).Wf) : e ∈ P.avail (G.restrict s) := by
  have hc := Graph.cnt_restrict_last hG he hes hkeep hW
  refine mem_avail_iff.mpr ⟨hE.tid_mem hG he, hc.symm, ?_⟩
  unfold Graph.trace
  rw [hc, Graph.traceBefore_restrict_of_keep hG (Nat.le_of_lt (hG.idx_lt_cnt he)) hkeep hsrc]
  exact hE.2 e he

theorem Program.isNext_unique {G : Graph} {a b : TEv} (ha : P.IsNext G a) (hb : P.IsNext G b) :
    a = b := by
  by_contra h
  exact nextLt_irrefl a (nextLt_trans (ha.2 b hb.1 (Ne.symm h)) (hb.2 a ha.1 h))

/-! ### `MaxCompletion` -/

/-- A round of the loop adds an event that is `<next`-before `e`, keeps `e`
available, and keeps a well-formed execution one. -/
theorem ComplStep.facts {e : TEv} {G G' : Graph} (hG : G.Wf) (hE : P.Exec G)
    (he : e ∈ P.avail G) (h : ComplStep P e G G') :
    ∃ a, G' = G.addMax a ∧ a ∈ P.avail G ∧ nextLt a e ∧ a.tid ≠ e.tid ∧
      G'.Wf ∧ P.Exec G' ∧ e ∈ P.avail G' ∧ G'.events = insert a G.events ∧
      G = G'.restrict G.events := by
  obtain ⟨a, ⟨ha, hmin⟩, hae, rfl⟩ := h
  have hidx := idx_eq_of_mem_avail ha
  have hna := not_mem_of_mem_avail hG ha
  have htid : a.tid ≠ e.tid := fun h => hae (avail_tid_inj ha he h)
  refine ⟨a, rfl, ha, hmin e he (Ne.symm hae), htid, hG.addMax hidx, hE.addMax hG ha, ?_,
    G.addMax_events a, (Graph.restrict_addMax hG hna).symm⟩
  obtain ⟨ht, hi, hs⟩ := mem_avail_iff.mp he
  have htr := Graph.trace_addMax_of_ne hG hidx (Ne.symm htid)
  refine mem_avail_iff.mpr ⟨ht, ?_, ?_⟩
  · rw [← Graph.trace_length, htr, Graph.trace_length]
    exact hi
  · rw [htr]
    exact hs

/-- A round of the loop keeps a consistent graph consistent (Def. A.17). -/
theorem ComplStep.cons {e : TEv} {G G' : Graph} (hM : M.Extensible) (hG : G.Wf)
    (hc : M.cons G) (h : ComplStep P e G G') : M.cons G' := by
  obtain ⟨a, ⟨ha, -⟩, -, rfl⟩ := h
  exact hM.cons_addMax hG hc (idx_eq_of_mem_avail ha)

theorem ComplStep.det {e : TEv} {G G1 G2 : Graph} (h1 : ComplStep P e G G1)
    (h2 : ComplStep P e G G2) : G1 = G2 := by
  obtain ⟨a, ha, -, rfl⟩ := h1
  obtain ⟨b, hb, -, rfl⟩ := h2
  rw [isNext_unique ha hb]

/-- The loop stops when the next event is `e`. -/
theorem ComplStep.not_of_isNext {e : TEv} {G G' : Graph} (h : P.IsNext G e) :
    ¬ ComplStep P e G G' := by
  rintro ⟨a, ha, hae, -⟩
  exact hae (isNext_unique ha h)

/-- The loop is deterministic. -/
theorem MaxCompl.det {G G1 G2 : Graph} {e : TEv} (h1 : MaxCompl P G e G1)
    (h2 : MaxCompl P G e G2) : G1 = G2 := by
  obtain ⟨c1, n1⟩ := h1
  obtain ⟨c2, n2⟩ := h2
  revert c2
  induction c1 using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro c2
    rcases Relation.ReflTransGen.cases_head c2 with h | ⟨c, hs, -⟩
    · exact h
    · exact absurd hs (ComplStep.not_of_isNext n1)
  | head hs _ ih =>
    intro c2
    rcases Relation.ReflTransGen.cases_head c2 with h | ⟨c, hs', hc⟩
    · rw [h] at hs
      exact absurd hs (ComplStep.not_of_isNext n2)
    · rw [← hs.det hs'] at hc
      exact ih hc

/-- The facts that every graph of the loop satisfies. -/
theorem ComplStep.chain {e : TEv} {G G' : Graph} (hG : G.Wf) (hE : P.Exec G)
    (he : e ∈ P.avail G) (h : Relation.ReflTransGen (ComplStep P e) G G') :
    G'.Wf ∧ P.Exec G' ∧ e ∈ P.avail G' ∧ G.events ⊆ G'.events ∧
      G = G'.restrict G.events ∧ (∀ b ∈ G'.events, b ∉ G.events → nextLt b e) ∧
      ∀ q ∈ G.events, G'.rf q = G.rf q := by
  induction h with
  | refl =>
    exact ⟨hG, hE, he, subset_rfl, hG.restrict_self.symm, fun b hb hb' => absurd hb hb',
      fun _ _ => rfl⟩
  | tail _ hs ih =>
    obtain ⟨hW, hE1, he1, hsub, hres, hnew, hrf⟩ := ih
    obtain ⟨a, rfl, ha, hlt, -, hW2, hE2, he2, hev, hres2⟩ := ComplStep.facts hW hE1 he1 hs
    refine ⟨hW2, hE2, he2, ?_, ?_, ?_, fun q hq => ?_⟩
    rotate_left 3
    · rw [← hrf q hq]
      exact Graph.addMax_rf_of_ne _ (fun h => not_mem_of_mem_avail hW ha (h ▸ hsub hq))
    · rw [hev]
      exact hsub.trans (Finset.subset_insert _ _)
    · calc G = _ := hres
        _ = _ := congrArg (fun H => H.restrict G.events) hres2
        _ = _ := by rw [Graph.restrict_restrict, Finset.inter_eq_right.mpr hsub]
    · intro b hb hb'
      rw [hev] at hb
      rcases Finset.mem_insert.mp hb with rfl | hb1
      · exact hlt
      · exact hnew b hb1 hb'

/-- The loop terminates for a bounded program: `MaxCompletion(G, e)` is
defined when `e` is available in the well-formed execution `G`. -/
theorem MaxCompl.exists {n : ℕ} (hn : P.Bounded n) {G : Graph} {e : TEv} (hG : G.Wf)
    (hE : P.Exec G) (he : e ∈ P.avail G) : ∃ G', MaxCompl P G e G' := by
  have step : ∀ G : Graph, G.Wf → P.Exec G → e ∈ P.avail G → ¬ P.IsNext G e →
      ∃ G1, ComplStep P e G G1 ∧ G1.Wf ∧ P.Exec G1 ∧ e ∈ P.avail G1 ∧
        G1.events.card = G.events.card + 1 := by
    intro G hG hE he hnx
    have hnf : ¬ P.Full G := fun hf => by
      rw [Full] at hf
      rw [hf] at he
      exact absurd he (by simp)
    obtain ⟨a, ha, -⟩ := exists_unique_isNext hnf
    have hae : a ≠ e := fun h => hnx (h ▸ ha)
    have hs : ComplStep P e G (G.addMax a) := ⟨a, ha, hae, rfl⟩
    obtain ⟨a', -, ha', -, -, hW, hE', he', hev, -⟩ := ComplStep.facts hG hE he hs
    exact ⟨_, hs, hW, hE', he', by
      rw [hev, Finset.card_insert_of_notMem (not_mem_of_mem_avail hG ha')]⟩
  have key : ∀ k (G : Graph), G.Wf → P.Exec G → e ∈ P.avail G →
      n * P.threads.length - G.events.card ≤ k → ∃ G', MaxCompl P G e G' := by
    intro k
    induction k with
    | zero =>
      intro G hG hE he hk
      by_cases hnx : P.IsNext G e
      · exact ⟨G, .refl, hnx⟩
      · obtain ⟨G1, -, hW, hE', -, hcard⟩ := step G hG hE he hnx
        have := hE'.card_le hW hn
        omega
    | succ k ih =>
      intro G hG hE he hk
      by_cases hnx : P.IsNext G e
      · exact ⟨G, .refl, hnx⟩
      · obtain ⟨G1, hs, hW, hE', he', hcard⟩ := step G hG hE he hnx
        obtain ⟨G', hc, hnx'⟩ := ih G1 hW hE' he' (by omega)
        exact ⟨G', .head hs hc, hnx'⟩
  exact key _ G hG hE he (Nat.le_refl _)

/-- What `MaxCompletion` returns: a well-formed execution that extends `G`,
in which `e` is the next event, and whose new events are `<next`-before `e`. -/
theorem MaxCompl.facts {G G' : Graph} {e : TEv} (hG : G.Wf) (hE : P.Exec G)
    (he : e ∈ P.avail G) (h : MaxCompl P G e G') :
    G'.Wf ∧ P.Exec G' ∧ P.IsNext G' e ∧ G.events ⊆ G'.events ∧
      G = G'.restrict G.events ∧ (∀ b ∈ G'.events, b ∉ G.events → nextLt b e) ∧
      ∀ q ∈ G.events, G'.rf q = G.rf q := by
  obtain ⟨hW, hE', -, hsub, hres, hnew, hrf⟩ := ComplStep.chain hG hE he h.1
  exact ⟨hW, hE', h.2, hsub, hres, hnew, hrf⟩

theorem MaxCompl.cons {G G' : Graph} {e : TEv} (hM : M.Extensible) (hG : G.Wf)
    (hE : P.Exec G) (he : e ∈ P.avail G) (hc : M.cons G) (h : MaxCompl P G e G') :
    M.cons G' := by
  obtain ⟨h, -⟩ := h
  induction h with
  | refl => exact hc
  | tail hch hs ih => exact hs.cons hM (ComplStep.chain hG hE he hch).1 ih

/-! ### The graphs that a backward step restricts to -/

/-- Line 6: `G \ {a, e}` is a prefix of `G` in which `e` is available. -/
theorem rv_remove {G : Graph} {a e : TEv} (hG : G.Wf) (hE : P.Exec G) (hme : G.IsMe (.th a))
    (hrf : G.rf a = some (.th e)) (hpo : ∀ b, G.porf (.th e) b ↔ b = .th a) :
    (G.remove {a, e}).IsPrefixOf G ∧ e ∈ P.avail (G.remove {a, e}) := by
  have hamax : ∀ b, ¬ G.porfStep (.th a) b := fun b h => hme.2.1 b (Relation.TransGen.single h)
  have he : e ∈ G.events := (hG.rf_source_mem hrf).2
  have hp : (G.remove {a, e}).IsPrefixOf G := by
    refine Graph.remove_isPrefixOf hG (fun q hq b hb => ?_)
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact absurd hb (hamax b)
    · rw [Finset.mem_singleton.mp hq] at hb
      exact ⟨a, by simp, (hpo b).mp (Relation.TransGen.single hb)⟩
  refine ⟨hp, ?_⟩
  have hqa : ∀ q ∈ G.events, q.tid = e.tid → q.idx < e.idx → q ≠ a := by
    rintro q hq ht hi rfl
    exact hamax (.th e) (Or.inl ⟨hq, he, ht, hi⟩)
  refine mem_avail_restrict hG hE he (by simp) (fun q hq ht hi => ?_) (fun q hq ht hi w hw => ?_)
    (hG.of_isPrefixOf hp)
  · refine Finset.mem_sdiff.mpr ⟨hq, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hqa q hq ht hi, fun h => Nat.lt_irrefl _ (h ▸ hi)⟩
  · cases w with
    | init => trivial
    | th w' =>
      have hw' : w' ∈ G.events := (hG.rf_source_mem hw).2
      refine Finset.mem_sdiff.mpr ⟨hw', ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h => hamax (.th q) (Or.inr ⟨q, rfl, hq, h ▸ hw⟩), fun h => ?_⟩
      have := (hpo (.th q)).mp (Relation.TransGen.single (Or.inr ⟨q, rfl, hq, h ▸ hw⟩))
      exact hqa q hq ht hi (Ev.th.inj this)

/-- Line 7: `G \ {a}` is a prefix of `G`; its available events are `a` and
available events of `G`. -/
theorem nr_remove {G : Graph} {a : TEv} (hG : G.Wf) (hE : P.Exec G) (hme : G.IsMe (.th a)) :
    (G.remove {a}).IsPrefixOf G ∧ a ∈ P.avail (G.remove {a}) ∧
      ∀ y ∈ P.avail (G.remove {a}), y = a ∨ y ∈ P.avail G := by
  have hamax : ∀ b, ¬ G.porfStep (.th a) b := fun b h => hme.2.1 b (Relation.TransGen.single h)
  have ha : a ∈ G.events := hme.1
  have hp : (G.remove {a}).IsPrefixOf G := by
    refine Graph.remove_isPrefixOf hG (fun q hq b hb => ?_)
    rw [Finset.mem_singleton.mp hq] at hb
    exact absurd hb (hamax b)
  have hsrc : ∀ q ∈ G.events, ∀ w, G.rf q = some w → w ∈ Graph.evSet (G.events \ {a}) := by
    intro q hq w hw
    cases w with
    | init => trivial
    | th w' =>
      refine Finset.mem_sdiff.mpr ⟨(hG.rf_source_mem hw).2, ?_⟩
      rw [Finset.mem_singleton]
      exact fun h => hamax (.th q) (Or.inr ⟨q, rfl, hq, h ▸ hw⟩)
  have hav : a ∈ P.avail (G.remove {a}) := by
    refine mem_avail_restrict hG hE ha (by simp) (fun q hq ht hi => ?_)
      (fun q hq _ _ w hw => hsrc q hq w hw) (hG.of_isPrefixOf hp)
    refine Finset.mem_sdiff.mpr ⟨hq, ?_⟩
    rw [Finset.mem_singleton]
    exact fun h => Nat.lt_irrefl _ (h ▸ hi)
  refine ⟨hp, hav, fun y hy => ?_⟩
  by_cases ht : y.tid = a.tid
  · exact Or.inl (avail_tid_inj hy hav ht)
  · right
    have htr : (G.remove {a}).trace y.tid = G.trace y.tid := by
      refine Graph.trace_restrict_of_thread hG (fun q hq hqt => ?_)
        (fun q hq _ w hw => hsrc q hq w hw)
      refine Finset.mem_sdiff.mpr ⟨hq, ?_⟩
      rw [Finset.mem_singleton]
      exact fun h => ht (h ▸ hqt).symm
    obtain ⟨h1, h2, h3⟩ := mem_avail_iff.mp hy
    refine mem_avail_iff.mpr ⟨h1, ?_, ?_⟩
    · rw [← Graph.trace_length, ← htr, Graph.trace_length]
      exact h2
    · rw [← htr]
      exact h3

/-! ### The backward step is a function, defined on non-initial graphs -/

theorem PrevStep.rv_inv {G G' : Graph} {a e : TEv} (h : PrevStep P G e (.rv a) G') :
    G.IsMe (.th a) ∧ a.IsRead ∧ G.rf a = some (.th e) ∧ nextLt a e ∧
      (∀ b, G.porf (.th e) b ↔ b = .th a) ∧ MaxCompl P (G.remove {a, e}) e G' := by
  cases h with
  | rv h1 h2 h3 h4 h5 h6 => exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem PrevStep.nr_inv {G G' : Graph} {e : TEv} (h : PrevStep P G e .nr G') :
    G.IsMe (.th e) ∧ G' = G.remove {e} ∧
      ¬ ∃ w, e.IsRead ∧ G.rf e = some (.th w) ∧ nextLt e w ∧
        ∀ b, G.porf (.th w) b ↔ b = .th e := by
  cases h with
  | nr h1 h2 => exact ⟨h1, rfl, h2⟩

/-- `Prev` is a function. -/
theorem PrevStep.det {G G1 G2 : Graph} {e1 e2 : TEv} {k1 k2 : Kind}
    (h1 : PrevStep P G e1 k1 G1) (h2 : PrevStep P G e2 k2 G2) :
    e1 = e2 ∧ k1 = k2 ∧ G1 = G2 := by
  cases k1 with
  | rv a =>
    obtain ⟨hme, hr, hrf, hlt, hpo, hmc⟩ := h1.rv_inv
    cases k2 with
    | rv a' =>
      obtain ⟨hme', -, hrf', -, -, hmc'⟩ := h2.rv_inv
      have ha : a = a' := Ev.th.inj (hme.unique hme')
      subst ha
      have he : e1 = e2 := by
        rw [hrf] at hrf'
        exact Ev.th.inj (Option.some.inj hrf')
      subst he
      exact ⟨rfl, rfl, hmc.det hmc'⟩
    | nr =>
      obtain ⟨hme', -, hneg⟩ := h2.nr_inv
      have ha : a = e2 := Ev.th.inj (hme.unique hme')
      subst ha
      exact absurd ⟨e1, hr, hrf, hlt, hpo⟩ hneg
  | nr =>
    obtain ⟨hme, hG1, hneg⟩ := h1.nr_inv
    cases k2 with
    | rv a' =>
      obtain ⟨hme', hr', hrf', hlt', hpo', -⟩ := h2.rv_inv
      have ha : e1 = a' := Ev.th.inj (hme.unique hme')
      subst ha
      exact absurd ⟨e2, hr', hrf', hlt', hpo'⟩ hneg
    | nr =>
      obtain ⟨hme', hG2, -⟩ := h2.nr_inv
      have ha : e1 = e2 := Ev.th.inj (hme.unique hme')
      subst ha
      exact ⟨rfl, rfl, hG1.trans hG2.symm⟩

/-- `Prev(G)` is defined for a well-formed consistent execution `G` of a
bounded program that has a thread event (Proposition A.26, step ⟨1⟩1). -/
theorem exists_prevStep {n : ℕ} (hn : P.Bounded n) {G : Graph} (hG : G.Wf) (hE : P.Exec G)
    (hc : M.cons G) (hne : G.events.Nonempty) : ∃ e k G', PrevStep P G e k G' := by
  obtain ⟨m, hm⟩ := Graph.exists_isMe hG (M.porf_acyclic G hG hc)
  obtain ⟨b, hb⟩ := hne
  cases m with
  | init =>
    have hib : G.porf .init (.th b) := Relation.TransGen.single (Or.inl hb)
    exact absurd hib (hm.2.1 (.th b))
  | th a =>
    by_cases hcnd : ∃ e, a.IsRead ∧ G.rf a = some (.th e) ∧ nextLt a e ∧
        ∀ b, G.porf (.th e) b ↔ b = .th a
    · obtain ⟨e, hr, hrf, hlt, hpo⟩ := hcnd
      obtain ⟨hp, hav⟩ := rv_remove hG hE hm hrf hpo
      obtain ⟨G', hG'⟩ := MaxCompl.exists hn (hG.of_isPrefixOf hp) (hE.of_isPrefixOf hG hp) hav
      exact ⟨e, .rv a, G', .rv hm hr hrf hlt hpo hG'⟩
    · exact ⟨a, .nr, _, .nr hm hcnd⟩

/-- The graph without thread events has no backward step. -/
theorem not_prevStep_init (μ : Loc → Val) (e : TEv) (k : Kind) (G' : Graph) :
    ¬ PrevStep P (Graph.init μ) e k G' := by
  intro h
  cases h with
  | rv hme => exact absurd hme.1 (by simp [Graph.evSet, Graph.init])
  | nr hme => exact absurd hme.1 (by simp [Graph.evSet, Graph.init])

/-! ### Statements: Proposition A.23 and Lemma A.24

For a well-formed, consistent, full execution `G_f` and a maximally extensible
model. -/

/-- A backward step from a well-formed consistent execution gives one
(Proposition A.23 (S3), with well-formedness and being an execution). -/
theorem PrevStep.inv {G G' : Graph} {e : TEv} {k : Kind} (hM : M.Extensible) (hG : G.Wf)
    (hE : P.Exec G) (hc : M.cons G) (h : PrevStep P G e k G') :
    G'.Wf ∧ P.Exec G' ∧ M.cons G' := by
  cases h with
  | rv hme hr hrf hlt hpo hmc =>
    obtain ⟨hp, hav⟩ := rv_remove hG hE hme hrf hpo
    obtain ⟨hW0, hc0⟩ := M.cons_prefix hG hc hp
    have hE0 := hE.of_isPrefixOf hG hp
    obtain ⟨hW', hE', -⟩ := hmc.facts hW0 hE0 hav
    exact ⟨hW', hE', hmc.cons hM hW0 hE0 hav hc0⟩
  | nr hme _ =>
    obtain ⟨hp, -, -⟩ := nr_remove (P := P) hG hE hme
    obtain ⟨hW0, hc0⟩ := M.cons_prefix hG hc hp
    exact ⟨hW0, hE.of_isPrefixOf hG hp, hc0⟩

theorem PrevReach.inv {Gf G : Graph} (hM : M.Extensible) (hGf : Gf.Wf) (hEf : P.Exec Gf)
    (hcf : M.cons Gf) (h : PrevReach P Gf G) : G.Wf ∧ P.Exec G ∧ M.cons G := by
  induction h with
  | refl => exact ⟨hGf, hEf, hcf⟩
  | tail _ hs ih =>
    obtain ⟨e, k, hs⟩ := hs
    obtain ⟨h1, h2, h3⟩ := ih
    exact hs.inv hM h1 h2 h3

/-- One backward step: Lemma A.24 for this step, and (S1) for the graph it
returns, from (S1) for the graph it starts from. -/
theorem PrevStep.s1_step {X Y : Graph} {e : TEv} {k : Kind} (hX : X.Wf) (hE : P.Exec X)
    (ih : ∀ y ∈ P.avail X, ∀ m, X.IsMe m → ¬ nextLtEv (.th y) m)
    (hs : PrevStep P X e k Y) :
    P.IsNext Y e ∧ ∀ y ∈ P.avail Y, ∀ m, Y.IsMe m → ¬ nextLtEv (.th y) m := by
  -- it is enough that `e` is next in `Y` and that `me(Y)` is not `<next`-after `e`
  suffices h : P.IsNext Y e ∧ ∀ m', Y.IsMe (.th m') → ¬ nextLt e m' by
    refine ⟨h.1, fun y hy m hm => ?_⟩
    cases m with
    | init => exact fun h => h
    | th m' =>
      intro hlt
      refine h.2 m' hm ?_
      by_cases hye : y = e
      · exact hye ▸ hlt
      · exact nextLt_trans (h.1.2 y hy hye) hlt
  cases k with
  | nr =>
    obtain ⟨hme, rfl, hneg⟩ := hs.nr_inv
    obtain ⟨hp, hav, havs⟩ := nr_remove hX hE hme
    have hamax : ∀ b, ¬ X.porfStep (.th e) b := fun b h => hme.2.1 b (Relation.TransGen.single h)
    have hcl : Maz.PrefixClosed X.porfStep (Graph.evSet (X.events ∩ (X.events \ {e}))) := by
      refine Graph.remove_prefixClosed hX (fun q hq b hb => ?_)
      rw [Finset.mem_singleton.mp hq] at hb
      exact absurd hb (hamax b)
    refine ⟨⟨hav, fun y hy hye => ?_⟩, fun m' hm hlt => ?_⟩
    · exact (nextLt_total hye).resolve_left (ih y ((havs y hy).resolve_left hye) _ hme)
    · have hm' : m' ∈ X.events ∩ (X.events \ {e}) := hm.1
      have hmX : m' ∈ X.events := (Finset.mem_inter.mp hm').1
      have hne : m' ≠ e := fun h =>
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp hm').2).2 (Finset.mem_singleton.mpr h)
      -- every causality step of `X` from `m'` goes to `e`
      have first : ∀ c, X.porfStep (.th m') c → c = .th e := by
        intro c hc
        cases c with
        | init => exact absurd hc (X.not_porfStep_init _)
        | th q =>
          by_contra hqe
          have hq : q ∈ X.events := (hX.mem_of_porfStep hc).2
          have hqY : Ev.th q ∈ Graph.evSet (X.events ∩ (X.events \ {e})) :=
            Finset.mem_inter.mpr ⟨hq, Finset.mem_sdiff.mpr ⟨hq, fun h =>
              hqe (congrArg Ev.th (Finset.mem_singleton.mp h))⟩⟩
          exact hm.2.1 (.th q)
            ((Graph.porf_restrict_iff hcl hqY).mpr (Relation.TransGen.single hc))
      by_cases hmax : ∀ b, ¬ X.porf (.th m') b
      · have : nextLt m' e := hme.2.2 (.th m') hmX hmax (fun h => hne (Ev.th.inj h))
        exact nextLt_irrefl _ (nextLt_trans this hlt)
      · obtain ⟨b, hb⟩ := not_forall_not.mp hmax
        obtain ⟨c, hc, -⟩ := Relation.TransGen.head'_iff.mp hb
        have hce := first c hc
        rw [hce] at hc
        rcases hc with hpo | ⟨q, hq, hqm, hrf⟩
        · exact nextLt_irrefl _ (nextLt_trans (nextLt_of_poT ⟨hpo.2.2.1, hpo.2.2.2⟩) hlt)
        · rw [← Ev.th.inj hq] at hrf
          refine hneg ⟨m', hX.isRead_of_rf hrf, hrf, hlt, fun b => ⟨fun hb => ?_, fun hb => ?_⟩⟩
          · obtain ⟨c, hc, hrest⟩ := Relation.TransGen.head'_iff.mp hb
            rw [first c hc] at hrest
            rcases Relation.ReflTransGen.cases_head hrest with h0 | ⟨c2, hc2, -⟩
            · exact h0.symm
            · exact absurd hc2 (hamax c2)
          · rw [hb]
            exact Relation.TransGen.single (Or.inr ⟨e, rfl, hme.1, hrf⟩)
  | rv a =>
    obtain ⟨hme, hr, hrf, hlt, hpo, hmc⟩ := hs.rv_inv
    obtain ⟨hp, hav⟩ := rv_remove hX hE hme hrf hpo
    have hamax : ∀ b, ¬ X.porfStep (.th a) b := fun b h => hme.2.1 b (Relation.TransGen.single h)
    have heX : e ∈ X.events := (hX.rf_source_mem hrf).2
    have hcl : Maz.PrefixClosed X.porfStep (Graph.evSet (X.events ∩ (X.events \ {a, e}))) := by
      refine Graph.remove_prefixClosed hX (fun q hq b hb => ?_)
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact absurd hb (hamax b)
      · rw [Finset.mem_singleton.mp hq] at hb
        exact ⟨a, by simp, (hpo b).mp (Relation.TransGen.single hb)⟩
    have hW0 := hX.of_isPrefixOf hp
    obtain ⟨-, -, hnext, hsub, -, hnew, hrfY⟩ := hmc.facts hW0 (hE.of_isPrefixOf hX hp) hav
    refine ⟨hnext, fun m' hm hlt' => ?_⟩
    by_cases hm0 : m' ∈ (X.remove {a, e}).events
    · have hm0' : m' ∈ X.events ∩ (X.events \ {a, e}) := hm0
      have hmX : m' ∈ X.events := (Finset.mem_inter.mp hm0').1
      have hnin : m' ∉ ({a, e} : Finset TEv) := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hm0').2).2
      have hma : m' ≠ a := fun h => hnin (by simp [h])
      have hmax : ∀ b, ¬ X.porf (.th m') b := by
        intro b hb
        obtain ⟨c, hc, -⟩ := Relation.TransGen.head'_iff.mp hb
        cases c with
        | init => exact absurd hc (X.not_porfStep_init _)
        | th q =>
          have hq : q ∈ X.events := (hX.mem_of_porfStep hc).2
          by_cases hqa : q = a
          · rw [hqa] at hc
            rcases hc with hpo' | ⟨q', hq', -, hrf'⟩
            · exact nextLt_irrefl _ (nextLt_trans (nextLt_trans
                (nextLt_of_poT ⟨hpo'.2.2.1, hpo'.2.2.2⟩) hlt) hlt')
            · rw [← Ev.th.inj hq', hrf] at hrf'
              exact hnin (by simp [Ev.th.inj (Option.some.inj hrf')])
          · by_cases hqe : q = e
            · rw [hqe] at hc
              rcases hc with hpo' | ⟨q', hq', -, hrf'⟩
              · exact nextLt_irrefl _ (nextLt_trans (nextLt_of_poT ⟨hpo'.2.2.1, hpo'.2.2.2⟩) hlt')
              · rw [← Ev.th.inj hq'] at hrf'
                have hre : e.IsRead := hX.isRead_of_rf hrf'
                obtain ⟨x, hx⟩ : ∃ x, a.act = .read x := by
                  cases hact : a.act with
                  | read x => exact ⟨x, rfl⟩
                  | write x v => simp [TEv.IsRead, hact, Act.IsRead] at hr
                obtain ⟨w, hw, hwt⟩ := hX.rf_read a hme.1 x hx
                rw [hrf] at hw
                rw [← Option.some.inj hw] at hwt
                obtain ⟨-, v, hv⟩ := hwt
                simp [TEv.IsRead, hv, Act.IsRead] at hre
            · have hqY : Ev.th q ∈ Graph.evSet (X.events ∩ (X.events \ {a, e})) :=
                Finset.mem_inter.mpr ⟨hq, Finset.mem_sdiff.mpr ⟨hq, by simp [hqa, hqe]⟩⟩
              have h0 : (X.remove {a, e}).porf (.th m') (.th q) :=
                (Graph.porf_restrict_iff hcl hqY).mpr (Relation.TransGen.single hc)
              exact hm.2.1 (.th q) (Graph.porf_mono hsub hrfY h0)
      have : nextLt m' a := hme.2.2 (.th m') hmX hmax (fun h => hma (Ev.th.inj h))
      exact nextLt_irrefl _ (nextLt_trans (nextLt_trans this hlt) hlt')
    · exact nextLt_irrefl _ (nextLt_trans (hnew m' hm.1 hm0) hlt')

/-- Proposition A.23 (S1): `[avail(G)]; <next; [me(G)] = ∅`. -/
theorem PrevReach.s1 {Gf G : Graph} (hM : M.Extensible) (hGf : Gf.Wf) (hEf : P.Exec Gf)
    (hcf : M.cons Gf) (hff : P.Full Gf) (h : PrevReach P Gf G) {a : TEv} {m : Ev}
    (ha : a ∈ P.avail G) (hm : G.IsMe m) : ¬ nextLtEv (.th a) m := by
  have key : ∀ y ∈ P.avail G, ∀ m, G.IsMe m → ¬ nextLtEv (.th y) m := by
    clear ha hm
    induction h with
    | refl =>
      intro y hy
      rw [Full] at hff
      rw [hff] at hy
      exact absurd hy (by simp)
    | tail hch hs ih =>
      obtain ⟨e, k, hs⟩ := hs
      obtain ⟨hW, hE, -⟩ := PrevReach.inv hM hGf hEf hcf hch
      exact (hs.s1_step hW hE ih).2
  exact key a ha m hm

/-- Lemma A.24: the event that a backward step removes is the next event of
the graph it returns. -/
theorem PrevReach.next_of_prevStep {Gf G G' : Graph} {e : TEv} {k : Kind} (hM : M.Extensible)
    (hGf : Gf.Wf) (hEf : P.Exec Gf) (hcf : M.cons Gf) (hff : P.Full Gf)
    (h : PrevReach P Gf G) (hs : PrevStep P G e k G') : P.IsNext G' e := by
  obtain ⟨hW, hE, -⟩ := PrevReach.inv hM hGf hEf hcf h
  exact (hs.s1_step hW hE (fun y hy m hm => PrevReach.s1 hM hGf hEf hcf hff h hy hm)).1

/-! ### An instance -/

namespace Examples

/-- `Prev` is defined on the graph `G2` that the checked run reaches by a
revisit: the hypotheses of `exists_prevStep` hold for it at SC. -/
example : ∃ e k G', PrevStep revProg G2 e k G' := by
  obtain ⟨-, -, hc, hE⟩ := revisit_reach.sound
  rw [C1_revisit_abs] at hc hE
  exact exists_prevStep revProg_bounded G2_wf hE hc ⟨r, by rw [G2_eq]; simp⟩

end Examples

end Trust
