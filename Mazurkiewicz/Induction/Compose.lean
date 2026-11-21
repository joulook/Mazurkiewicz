import Mazurkiewicz.Induction.Residual

/-!
# Fragment composition

`induction-popl`, `bridge.tex` sec:compose: def:compose, lem:compose-graph,
prop:compose, cor:compose.

How the text is read here.

* def:compose: `G.comp H`. The events of `H` are shifted by the counts of
  `G` (`Graph.emb`); a read of `H` that reads from the initialization event of
  `H` reads from the last write of `G` to its location (`Graph.embSrc`); the
  coherence order of a location is that of `G` followed by that of `H`. The
  definition is total: it does not look at `H.mem`, and gives no source to a
  shifted event without source.
* lem:compose-graph is stated for a well-formed `G` and a well-formed,
  SC-consistent `H` with `H.mem = mem_G`. The paper states it for every graph
  `H`; all its uses are for consistent `H`. With consistency the lemma is
  proved by induction along maximal extensions of `H`
  (`Graph.sc_induction`), from the equations `comp_init` and `comp_addMax`,
  instead of a direct verification of the conditions of def:graph.
* prop:compose and cor:compose are for `P' = P.residual G.trace G.memOf`,
  the program `P_{h(G)}`.
* cor:compose (2), "obtained from `G` by `m` maximal steps": `MSteps P τ G G'`
  with `τ.length = m`.
* lem:compose-graph (1) also states that single returned values are kept;
  only the resulting equation on traces is exported.
* prop:compose (1) assumes `H ∈ Exec_SC(P')`, and (2) assumes
  `G ⊙ H ∈ Exec_SC(P)`; here each follows from the given maximal step.
-/

namespace Trust

open Program

namespace Graph

/-- The event of `G ⊙ H` for the thread event `e` of `H` (def:compose). -/
def emb (G : Graph) (e : TEv) : TEv := ⟨e.tid, G.cnt e.tid + e.idx, e.act⟩

/-- The inverse of `emb` on the events that `emb` produces. -/
def unemb (G : Graph) (q : TEv) : TEv := ⟨q.tid, q.idx - G.cnt q.tid, q.act⟩

/-- The source in `G ⊙ H` for a source `w` of `H` at location `x`
(def:compose, `emb_l`). -/
def embSrc (G : Graph) (x : Loc) : Ev → Ev
  | .init => G.maxWrite x
  | .th w => .th (G.emb w)

/-- The composition `G ⊙ H` (def:compose). -/
def comp (G H : Graph) : Graph where
  mem := G.mem
  events := G.events ∪ H.events.image G.emb
  rf := fun q =>
    if q ∈ G.events then G.rf q
    else if G.unemb q ∈ H.events ∧ G.cnt q.tid ≤ q.idx then
      (H.rf (G.unemb q)).map (G.embSrc q.loc)
    else none
  co := fun x => G.co x ++ (H.co x).map G.emb

/-! ### The embedding -/

theorem emb_injective (G : Graph) : Function.Injective G.emb := by
  rintro ⟨t, i, a⟩ ⟨t', i', a'⟩ h
  simp only [emb, TEv.mk.injEq] at h
  obtain ⟨rfl, hi, rfl⟩ := h
  rw [Nat.add_left_cancel hi]

theorem unemb_emb (G : Graph) (e : TEv) : G.unemb (G.emb e) = e := by
  cases e
  simp [emb, unemb]

theorem emb_unemb (G : Graph) {q : TEv} (h : G.cnt q.tid ≤ q.idx) : G.emb (G.unemb q) = q := by
  cases q
  simp only [emb, unemb, TEv.mk.injEq, true_and, and_true]
  exact Nat.add_sub_cancel' h

theorem cnt_le_emb_idx (G : Graph) (e : TEv) : G.cnt (G.emb e).tid ≤ (G.emb e).idx :=
  Nat.le_add_right _ _

/-- A shifted event is not an event of `G`. -/
theorem emb_not_mem {G : Graph} (hG : G.Wf) (e : TEv) : G.emb e ∉ G.events := by
  intro h
  have h1 := hG.idx_lt_cnt h
  have h2 := G.cnt_le_emb_idx e
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h1 h2)

/-! ### The components of a composition -/

theorem comp_rf_old {G H : Graph} {q : TEv} (hq : q ∈ G.events) : (G.comp H).rf q = G.rf q := by
  simp [comp, hq]

theorem comp_rf_emb {G H : Graph} (hG : G.Wf) {e : TEv} (he : e ∈ H.events) :
    (G.comp H).rf (G.emb e) = (H.rf e).map (G.embSrc e.loc) := by
  have h1 := emb_not_mem hG e
  have h2 : G.unemb (G.emb e) ∈ H.events ∧ G.cnt (G.emb e).tid ≤ (G.emb e).idx :=
    ⟨by rw [unemb_emb]; exact he, G.cnt_le_emb_idx e⟩
  change (if G.emb e ∈ G.events then G.rf (G.emb e)
    else if G.unemb (G.emb e) ∈ H.events ∧ G.cnt (G.emb e).tid ≤ (G.emb e).idx then
      (H.rf (G.unemb (G.emb e))).map (G.embSrc (G.emb e).loc) else none) = _
  rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2),
    unemb_emb]
  rfl

theorem comp_rf_none {G H : Graph} {q : TEv} (h1 : q ∉ G.events)
    (h2 : ¬ (G.unemb q ∈ H.events ∧ G.cnt q.tid ≤ q.idx)) : (G.comp H).rf q = none := by
  simp [comp, h1, h2]

/-- An event outside `G` whose index is at least the count of `G` is a
shifted event. -/
theorem comp_rf_cases {G : Graph} (q : TEv) :
    q ∈ G.events ∨ (q ∉ G.events ∧ ∃ r, q = G.emb r) ∨
      (q ∉ G.events ∧ ¬ G.cnt q.tid ≤ q.idx) := by
  by_cases h1 : q ∈ G.events
  · exact Or.inl h1
  · by_cases h2 : G.cnt q.tid ≤ q.idx
    · exact Or.inr (Or.inl ⟨h1, G.unemb q, (G.emb_unemb h2).symm⟩)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)

/-- The sources in `G ⊙ H'` and in `G ⊙ H`, away from a new event `e` of
`H'`. -/
theorem comp_rf_extend {G H H' : Graph} (hG : G.Wf) {e : TEv}
    (hev : H'.events = insert e H.events) (hrf : ∀ r, r ≠ e → H'.rf r = H.rf r) {q : TEv}
    (hq : q ≠ G.emb e) : (G.comp H').rf q = (G.comp H).rf q := by
  rcases comp_rf_cases (G := G) q with h | ⟨h1, r, rfl⟩ | ⟨h1, h2⟩
  · rw [comp_rf_old h, comp_rf_old h]
  · have hre : r ≠ e := fun h => hq (h ▸ rfl)
    by_cases hr : r ∈ H.events
    · have hr' : r ∈ H'.events := by rw [hev]; exact Finset.mem_insert_of_mem hr
      rw [comp_rf_emb hG hr', comp_rf_emb hG hr, hrf r hre]
    · have hr' : r ∉ H'.events := by
        rw [hev]
        exact fun h => (Finset.mem_insert.mp h).elim hre hr
      rw [comp_rf_none h1 (fun h => hr' (by rw [← G.unemb_emb r]; exact h.1)),
        comp_rf_none h1 (fun h => hr (by rw [← G.unemb_emb r]; exact h.1))]
  · rw [comp_rf_none h1 (fun h => h2 h.2), comp_rf_none h1 (fun h => h2 h.2)]

/-- lem:compose-graph (2), first part: the last write of `G ⊙ H` to a
location. -/
theorem comp_maxWrite (G H : Graph) (x : Loc) :
    (G.comp H).maxWrite x = G.embSrc x (H.maxWrite x) := by
  have hco : (G.comp H).co x = G.co x ++ (H.co x).map G.emb := rfl
  unfold maxWrite
  rw [hco, List.getLast?_append, List.getLast?_map]
  cases h : (H.co x).getLast? with
  | none => simp [embSrc, maxWrite]
  | some m => simp [embSrc]

/-- The counts of `G ⊙ H`. -/
theorem comp_cnt {G : Graph} (hG : G.Wf) (H : Graph) (t : Tid) :
    (G.comp H).cnt t = G.cnt t + H.cnt t := by
  unfold cnt
  have hev : (G.comp H).events = G.events ∪ H.events.image G.emb := rfl
  rw [hev, Finset.filter_union, Finset.card_union_of_disjoint]
  · congr 1
    have : (H.events.image G.emb).filter (fun e => e.tid = t) =
        (H.events.filter (fun e => e.tid = t)).image G.emb := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨r, hr, rfl⟩, ht⟩
        exact ⟨r, ⟨hr, ht⟩, rfl⟩
      · rintro ⟨r, ⟨hr, ht⟩, rfl⟩
        exact ⟨⟨r, hr, rfl⟩, ht⟩
    rw [this, Finset.card_image_of_injective _ G.emb_injective]
  · rw [Finset.disjoint_left]
    intro q hq hq'
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hq').1
    exact emb_not_mem hG r (Finset.mem_filter.mp hq).1

/-! ### Maximal extensions, without a program -/

theorem trace_init (μ : Loc → Val) (t : Tid) : (Graph.init μ).trace t = [] := by
  have h0 : (Graph.init μ).cnt t = 0 := by simp [cnt, Graph.init]
  unfold trace
  rw [h0]
  rfl

theorem trace_addMax_read {G : Graph} (hG : G.Wf) {e : TEv} (hidx : e.idx = G.cnt e.tid)
    {x : Loc} (hact : e.act = .read x) (t : Tid) :
    (G.addMax e).trace t =
      if t = e.tid then G.trace t ++ [some (G.memOf x)] else G.trace t := by
  rw [addMax_read hact, trace_addRead hG hidx hact (maxWrite_isWriteTo hG x) t]
  rfl

theorem trace_addMax_write {G : Graph} (hG : G.Wf) {e : TEv} (hidx : e.idx = G.cnt e.tid)
    (hw : e.IsWrite) (t : Tid) :
    (G.addMax e).trace t = if t = e.tid then G.trace t ++ [none] else G.trace t := by
  rw [addMax_write hw, trace_addWrite hG hidx hw (maxWrite_isWriteTo hG _) t]

theorem memOf_addMax_read {G : Graph} {e : TEv} {x : Loc} (hact : e.act = .read x) :
    (G.addMax e).memOf = G.memOf := by
  rw [addMax_read hact]
  rfl

theorem memOf_addMax_write {G : Graph} (hG : G.Wf) {e : TEv} {x : Loc} {v : Val}
    (hact : e.act = .write x v) : (G.addMax e).memOf = Function.update G.memOf x v := by
  have hw : e.IsWrite := by simp [TEv.IsWrite, hact, Act.IsWrite]
  have hloc : e.loc = x := by simp [TEv.loc, hact, Act.loc]
  rw [addMax_write hw]
  funext y
  by_cases hy : y = x
  · subst hy
    have hm := maxWrite_addWrite_maxWrite hG e
    have hm' : (G.addWrite e (G.maxWrite e.loc)).maxWrite y = .th e := by
      rw [← hloc]
      exact hm
    rw [Function.update_self]
    unfold memOf
    rw [hm']
    simp [valAt, hact]
  · have hmw : ∀ wp, (G.addWrite e wp).maxWrite y = G.maxWrite y := by
      intro wp
      unfold maxWrite
      rw [G.addWrite_co_of_ne e wp (y := y) (hloc ▸ hy)]
    rw [Function.update_of_ne hy]
    unfold memOf
    rw [hmw]
    rfl

/-- The program that replays a graph: thread `t` performs the labels of its
events in `H`, whatever it reads. -/
noncomputable def replay (H : Graph) : Program where
  threads := (H.events.image TEv.tid).toList
  threads_nodup := Finset.nodup_toList _
  step := fun t u => if u.length < H.cnt t then (H.evAt t u.length).map TEv.act else none
  mem := H.mem
  step_none := by
    intro t ht
    have h0 : H.cnt t = 0 := by
      unfold cnt
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e he hte
      exact ht (Finset.mem_toList.mpr (Finset.mem_image.mpr ⟨e, he, hte⟩))
    simp [h0]

theorem replay_exec {H : Graph} (hH : H.Wf) : H.replay.Exec H := by
  refine ⟨rfl, fun e he => ?_⟩
  change (if (H.traceBefore e.tid e.idx).length < H.cnt e.tid then
    (H.evAt e.tid (H.traceBefore e.tid e.idx).length).map TEv.act else none) = some e.act
  rw [traceBefore_length, ite_eq_left_of_eq_true _ _ (eq_true (hH.idx_lt_cnt he)),
    hH.evAt_eq_some he]
  rfl

/-- Every well-formed SC-consistent graph is obtained from the initial graph
by maximal extensions. -/
theorem sc_induction {motive : Graph → Prop} (μ : Loc → Val)
    (hinit : motive (Graph.init μ))
    (hstep : ∀ (H : Graph) (e : TEv), H.Wf → SC.cons H → H.mem = μ → e.idx = H.cnt e.tid →
      (H.addMax e).Wf → SC.cons (H.addMax e) → motive H → motive (H.addMax e))
    {H : Graph} (hH : H.Wf) (hc : SC.cons H) (hμ : H.mem = μ) : motive H := by
  obtain ⟨P₀, hmem, hr⟩ : ∃ P₀ : Program, P₀.mem = μ ∧ MReach P₀ H :=
    ⟨H.replay, hμ, mreach_iff.mpr (greach_iff.mpr ⟨hH, replay_exec hH, hc⟩)⟩
  clear hH hc hμ
  unfold MReach at hr
  rw [hmem] at hr
  induction hr with
  | refl => exact hinit
  | tail _ hs ih =>
    obtain ⟨t, hs⟩ := hs
    obtain ⟨⟨hW, hE, hc₁⟩, e, hav, -, rfl⟩ := mstep_iff.mp hs
    obtain ⟨hW₂, -, hc₂⟩ := hs.execSC_right
    exact hstep _ e hW hc₁ (hE.1.trans hmem) (idx_eq_of_mem_avail hav) hW₂ hc₂ ih

/-! ### lem:compose-graph -/

/-- lem:compose-graph: `G ⊙ G₀ = G`. -/
theorem comp_init {G : Graph} (hG : G.Wf) (μ : Loc → Val) : G.comp (Graph.init μ) = G := by
  apply Graph.ext
  · rfl
  · simp [comp, Graph.init]
  · funext q
    by_cases hq : q ∈ G.events
    · exact comp_rf_old hq
    · rw [comp_rf_none hq (by simp [Graph.init]), hG.rf_none q (Or.inl hq)]
  · funext x
    simp [comp, Graph.init]

/-- Composition commutes with a maximal extension of the fragment. -/
theorem comp_addMax {G H : Graph} (hG : G.Wf) (hH : H.Wf) (hGH : (G.comp H).Wf) {e : TEv}
    (hidx : e.idx = H.cnt e.tid) : G.comp (H.addMax e) = (G.comp H).addMax (G.emb e) := by
  have he : e ∉ H.events := hH.not_mem_of_idx_eq_cnt hidx
  have hev : ∀ H' : Graph, H'.events = insert e H.events →
      (G.comp H').events = insert (G.emb e) (G.comp H).events := by
    intro H' h
    change G.events ∪ H'.events.image G.emb = insert (G.emb e) (G.events ∪ H.events.image G.emb)
    rw [h, Finset.image_insert, Finset.union_insert]
  cases hact : e.act with
  | read x =>
    have hact' : (G.emb e).act = .read x := hact
    have hloc : e.loc = x := by simp [TEv.loc, hact, Act.loc]
    rw [addMax_read hact, addMax_read hact', comp_maxWrite]
    apply Graph.ext
    · rfl
    · exact hev _ rfl
    · funext q
      rw [addRead_rf]
      by_cases hq : q = G.emb e
      · rw [hq, Function.update_self, comp_rf_emb hG (Finset.mem_insert_self _ _), addRead_rf,
          Function.update_self, hloc]
        rfl
      · rw [Function.update_of_ne hq]
        exact comp_rf_extend (H := H) (H' := H.addRead e (H.maxWrite x)) hG rfl
          (fun r hr => by rw [addRead_rf, Function.update_of_ne hr]) hq
    · rfl
  | write x v =>
    have hw : e.IsWrite := by simp [TEv.IsWrite, hact, Act.IsWrite]
    have hw' : (G.emb e).IsWrite := hw
    rw [addMax_write hw, addMax_write hw']
    apply Graph.ext
    · rfl
    · exact hev _ rfl
    · funext q
      rw [addWrite_rf]
      by_cases hq : q = G.emb e
      · rw [hq, comp_rf_emb hG (Finset.mem_insert_self _ _), addWrite_rf,
          hH.rf_none e (Or.inl he),
          comp_rf_none (emb_not_mem hG e) (fun h => he (by rw [← G.unemb_emb e]; exact h.1))]
        rfl
      · exact comp_rf_extend (H := H) (H' := H.addWrite e (H.maxWrite e.loc)) hG rfl
          (fun r _ => rfl) hq
    · funext y
      have h1 := addWrite_maxWrite_co_eq hH e y
      have h2 := addWrite_maxWrite_co_eq hGH (G.emb e) y
      rw [h2]
      change G.co y ++ ((H.addWrite e (H.maxWrite e.loc)).co y).map G.emb = _
      rw [h1]
      have hloc' : (G.emb e).loc = e.loc := rfl
      rw [hloc']
      by_cases hy : y = e.loc
      · simp only [hy, ↓reduceIte, List.map_append, List.map_cons, List.map_nil]
        change _ = (G.co e.loc ++ (H.co e.loc).map G.emb) ++ [G.emb e]
        rw [List.append_assoc]
      · simp only [hy, ↓reduceIte]
        rfl

/-- lem:compose-graph: `G ⊙ H` is an execution graph with the initial memory
of `G`; (1) its traces; (2) its last writes and its memory. -/
theorem comp_facts {G H : Graph} (hG : G.Wf) (hH : H.Wf) (hc : SC.cons H)
    (hμ : H.mem = G.memOf) :
    (G.comp H).Wf ∧ (G.comp H).mem = G.mem ∧
      (∀ t, (G.comp H).cnt t = G.cnt t + H.cnt t) ∧
      (∀ t, (G.comp H).trace t = G.trace t ++ H.trace t) ∧
      (∀ x, (G.comp H).maxWrite x = G.embSrc x (H.maxWrite x)) ∧
      (G.comp H).memOf = H.memOf := by
  have key : (G.comp H).Wf ∧ (∀ t, (G.comp H).trace t = G.trace t ++ H.trace t) ∧
      (G.comp H).memOf = H.memOf := by
    refine sc_induction (motive := fun H => (G.comp H).Wf ∧
      (∀ t, (G.comp H).trace t = G.trace t ++ H.trace t) ∧ (G.comp H).memOf = H.memOf)
      G.memOf ?_ ?_ hH hc hμ
    · rw [comp_init hG]
      exact ⟨hG, fun t => by rw [trace_init, List.append_nil], rfl⟩
    · rintro H e hH - - hidx - - ⟨ihW, ihT, ihM⟩
      have hidx' : (G.emb e).idx = (G.comp H).cnt (G.emb e).tid := by
        rw [comp_cnt hG]
        change G.cnt e.tid + e.idx = G.cnt e.tid + H.cnt e.tid
        rw [hidx]
      rw [comp_addMax hG hH ihW hidx]
      refine ⟨ihW.addMax hidx', ?_, ?_⟩
      · intro t
        cases hact : e.act with
        | read x =>
          have hact' : (G.emb e).act = .read x := hact
          rw [trace_addMax_read ihW hidx' hact' t, trace_addMax_read hH hidx hact t, ihT, ihM]
          change (if t = e.tid then _ else _) = _
          by_cases ht : t = e.tid
          · simp only [ht, ↓reduceIte, List.append_assoc]
          · simp only [ht, ↓reduceIte]
        | write x v =>
          have hw : e.IsWrite := by simp [TEv.IsWrite, hact, Act.IsWrite]
          have hw' : (G.emb e).IsWrite := hw
          rw [trace_addMax_write ihW hidx' hw' t, trace_addMax_write hH hidx hw t, ihT]
          change (if t = e.tid then _ else _) = _
          by_cases ht : t = e.tid
          · simp only [ht, ↓reduceIte, List.append_assoc]
          · simp only [ht, ↓reduceIte]
      · cases hact : e.act with
        | read x =>
          have hact' : (G.emb e).act = .read x := hact
          rw [memOf_addMax_read hact', memOf_addMax_read hact, ihM]
        | write x v =>
          have hact' : (G.emb e).act = .write x v := hact
          rw [memOf_addMax_write ihW hact', memOf_addMax_write hH hact, ihM]
  exact ⟨key.1, rfl, comp_cnt hG H, key.2.1, comp_maxWrite G H, key.2.2⟩

end Graph

variable {P : Program}

/-- prop:compose (1). -/
theorem MStep.comp {G H H' : Graph} {t : Tid} (hG : ExecSC P G)
    (hGH : ExecSC P (G.comp H)) (h : MStep (P.residual G.trace G.memOf) t H H') :
    MStep P t (G.comp H) (G.comp H') := by
  obtain ⟨⟨hHW, hHE, hHc⟩, e, hav, ht, rfl⟩ := mstep_iff.mp h
  obtain ⟨hW, -, hcnt, htr, -, -⟩ := Graph.comp_facts hG.1 hHW hHc hHE.1
  obtain ⟨h1, h2, h3⟩ := mem_avail_iff.mp hav
  have h1' : e.tid ∈ P.threads := h1
  have h3' : (if e.tid ∈ P.threads then P.step e.tid (G.trace e.tid ++ H.trace e.tid)
      else none) = some e.act := h3
  rw [ite_eq_left_of_eq_true _ _ (eq_true h1')] at h3'
  refine mstep_iff.mpr ⟨hGH, G.emb e, mem_avail_iff.mpr ⟨h1', ?_, ?_⟩, ht,
    Graph.comp_addMax hG.1 hHW hW h2⟩
  · rw [hcnt]
    change G.cnt e.tid + e.idx = G.cnt e.tid + H.cnt e.tid
    rw [h2]
  · change P.step e.tid ((G.comp H).trace e.tid) = some e.act
    rw [htr]
    exact h3'

/-- prop:compose (2). -/
theorem mstep_comp_inv {G H G' : Graph} {t : Tid} (hG : ExecSC P G)
    (hH : ExecSC (P.residual G.trace G.memOf) H) (h : MStep P t (G.comp H) G') :
    ∃ H', MStep (P.residual G.trace G.memOf) t H H' ∧ G' = G.comp H' := by
  obtain ⟨-, ⟨t', i', a'⟩, hav', ht, rfl⟩ := mstep_iff.mp h
  obtain ⟨hW, -, hcnt, htr, -, -⟩ := Graph.comp_facts hG.1 hH.1 hH.2.2 hH.2.1.1
  obtain ⟨h1, h2, h3⟩ := mem_avail_iff.mp hav'
  simp only at ht h1 h2 h3
  rw [htr] at h3
  rw [hcnt] at h2
  have hav : (⟨t', H.cnt t', a'⟩ : TEv) ∈ (P.residual G.trace G.memOf).avail H := by
    refine mem_avail_iff.mpr ⟨h1, rfl, ?_⟩
    change (if t' ∈ P.threads then P.step t' (G.trace t' ++ H.trace t') else none) = some a'
    rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
    exact h3
  have hemb : G.emb ⟨t', H.cnt t', a'⟩ = ⟨t', i', a'⟩ := by
    simp only [Graph.emb, TEv.mk.injEq, true_and, and_true]
    exact h2.symm
  refine ⟨H.addMax ⟨t', H.cnt t', a'⟩, mstep_iff.mpr ⟨hH, _, hav, ht, rfl⟩, ?_⟩
  rw [Graph.comp_addMax hG.1 hH.1 hW rfl, hemb]

/-- cor:compose (1). -/
theorem greach_comp {G H : Graph} (hG : ExecSC P G)
    (hH : GReach (P.residual G.trace G.memOf) SC H) :
    GReach P SC (G.comp H) ∧ G.IsPrefixOf (G.comp H) ∧
      conf P (G.comp H) = (fun t => ((conf P G).1 t).appList (H.trace t), H.memOf) := by
  have hHE := greach_iff.mp hH
  have key : GReach P SC (G.comp H) ∧ G.IsPrefixOf (G.comp H) := by
    have hm := mreach_iff.mpr hH
    induction hm with
    | refl =>
      change GReach P SC (G.comp (Graph.init G.memOf)) ∧
        G.IsPrefixOf (G.comp (Graph.init G.memOf))
      rw [Graph.comp_init hG.1]
      exact ⟨greach_iff.mpr hG, hG.1.isPrefixOf_refl⟩
    | tail hr hs ih =>
      obtain ⟨t, hs⟩ := hs
      obtain ⟨ih1, ih2⟩ := ih (mreach_iff.mp hr) hs.execSC_left
      have hstep := (MStep.comp hG (greach_iff.mp ih1) hs).gstep
      exact ⟨ih1.tail hstep, Graph.IsPrefixOf.trans ih2 hstep.prefix⟩
  obtain ⟨-, -, -, htr, -, hmem⟩ := Graph.comp_facts hG.1 hHE.1 hHE.2.2 hHE.2.1.1
  refine ⟨key.1, key.2, Prod.ext (funext fun t => ?_) hmem⟩
  change St.mk (P.step t) ((G.comp H).trace t) = (St.mk (P.step t) (G.trace t)).appList _
  rw [htr, St.appList_mk]

/-- cor:compose (2). -/
theorem msteps_decomp {G G' : Graph} {τ : List Tid} (hG : ExecSC P G) (h : MSteps P τ G G') :
    ∃ H, GReach (P.residual G.trace G.memOf) SC H ∧ H.size = τ.length + 1 ∧
      G' = G.comp H := by
  induction τ generalizing G' with
  | nil =>
    refine ⟨Graph.init G.memOf, Relation.ReflTransGen.refl, by simp [Graph.size, Graph.init], ?_⟩
    rw [Graph.comp_init hG.1]
    exact h
  | cons t τ ih =>
    obtain ⟨G₁, hG₁, hs⟩ := h
    obtain ⟨H₁, hr, hsz, rfl⟩ := ih hG₁
    obtain ⟨H', hs', rfl⟩ := mstep_comp_inv hG (greach_iff.mp hr) hs
    refine ⟨H', hr.tail hs'.gstep, ?_, rfl⟩
    rw [hs'.gstep.size, hsz]
    rfl

/-! ### Instances -/

namespace Examples

/-- cor:compose (2) on the checked run: the full graph `G3` is the composition
of the initial graph with a fragment of size 4 that is reachable in the
residual program. -/
example : ∃ H, GReach (revProg.residual (Graph.init revProg.mem).trace
    (Graph.init revProg.mem).memOf) SC H ∧ H.size = 4 ∧
    G3 = (Graph.init revProg.mem).comp H := by
  obtain ⟨τ, hl, hm⟩ := greach_iff_msteps.mp
    (greach_iff.mpr ⟨G3_facts.1, G3_facts.2.1, G3_facts.2.2.1⟩)
  obtain ⟨H, hH, hsz, heq⟩ :=
    msteps_decomp ⟨Graph.init_wf _, exec_init revProg, SC.cons_init _⟩ hm
  refine ⟨H, hH, ?_, heq⟩
  have h3 : G3.events.card = 3 := by
    rw [← C3_abs]
    rfl
  rw [hsz, hl, h3]

/-- cor:compose on a non-initial graph and a non-empty fragment: the maximal
step from `G2` by its available event `d` is the composition of `G2` with a
fragment `H` of size 2 that is reachable in the residual program of `G2`
((2)); and for this `H`, (1) gives that `G2 ⊙ H` is reachable with `G2` as a
prefix. -/
example : ∃ H, GReach (revProg.residual G2.trace G2.memOf) SC H ∧ H.size = 2 ∧
    G2.addMax d = G2.comp H ∧ GReach revProg SC (G2.comp H) ∧ G2.IsPrefixOf (G2.comp H) := by
  obtain ⟨-, -, hc, hE⟩ := revisit_reach.sound
  rw [C1_revisit_abs] at hc hE
  have hG2 : ExecSC revProg G2 := ⟨G2_wf, hE, hc⟩
  have hnx : revProg.IsNext C2.abs d := (Program.nextC_eq_some_iff C2_wf).mp (by decide)
  rw [C2_abs] at hnx
  have hstep : MStep revProg d.tid G2 (G2.addMax d) := mstep_iff.mpr ⟨hG2, d, hnx.1, rfl, rfl⟩
  obtain ⟨H, hH, hsz, heq⟩ := msteps_decomp (τ := [d.tid]) hG2 ⟨G2, rfl, hstep⟩
  exact ⟨H, hH, hsz, heq, (greach_comp hG2 hH).1, (greach_comp hG2 hH).2.1⟩

end Examples

end Trust
