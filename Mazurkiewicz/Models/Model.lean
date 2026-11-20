import Mazurkiewicz.Trust.Program
import Mazurkiewicz.Trust.Examples

/-!
# Memory models

Paper: Section 3.1 (the assumptions on the consistency predicate) and
Appendix A.2, Def. A.15-A.17. `induction-popl`: def:model with (A1), (A2);
`dpor.tex`, lem:trust-model.

A model is a consistency predicate on graphs. It takes a `Graph`, which has no
insertion order, so the paper's requirement that consistency does not depend
on `≤_G` holds by typing.

* `Model`: the consistency predicate with what `induction-popl` assumes of a
  model: the initial graph is consistent, (A1) a consistent graph has no
  causality cycle (the paper's *well-formed* model, Def. A.15), (A2)
  consistency is closed under prefixes (*prefix-closed*, Def. A.16).
* `Model.Extensible`: *maximal extensibility* (Def. A.17, for events that are
  not exclusive): adding a read that reads from the last write of its
  location, or a write placed last in the coherence order of its location,
  keeps a graph consistent.

Differences from the paper, all in the plan's table:

* The assumptions are stated for well-formed graphs (`Graph.Wf` is the
  paper's definition of a graph, Def. 3.2, plus contiguous indices).
* Def. A.17 quantifies over every event `e`. Here `e` is the next event of
  its thread (index `cnt G t`). For an event with a smaller index the
  statement is false already for sequential consistency; Section 3.1 of the
  paper states the property for a po-maximal extension.
* Def. A.16 is stated with `dom(G.porf; [E]) ⊆ E`; here with `IsPrefixOf`,
  the restriction to a set closed under one step of `po ∪ rf`, which is the
  same condition. Def. A.16 as printed omits the premise that `G` is
  consistent; it is included here, following Section 3.1 ("restricting a
  consistent graph to any porf-prefix-closed subset of its events yields a
  consistent graph") and `ass:trust`(c) of `dpor.tex`. A restriction keeps
  `init` (it is implicit).
* The paper describes sequential consistency informally (Section 3.1); `SC`
  is the standard formulation with the four relations, def:sc of
  `induction-popl`, with `fr` per location.
* Consistency does not imply that `rf` is total on reads (in Coq it does:
  `cons_complete`). Totality is part of `Graph.Wf`. So every graph to which an
  assumption is applied (reached graphs, the graphs of the backward steps and
  of maximal completions) must be shown well-formed; the paper's use of
  "consistent, hence `rf` total" (proof of Lemma A.20) becomes a use of
  well-formedness.
* "The last write of the location" is `maxWrite`, per location
  (`max_{G.co} G.W_loc(e)` in the paper).
-/

namespace Trust

/-- A memory model: a consistency predicate with the assumptions (A1) and
(A2). -/
structure Model where
  /-- the consistency predicate -/
  cons : Graph → Prop
  /-- every initial graph is consistent -/
  cons_init : ∀ μ, cons (Graph.init μ)
  /-- (A1), Def. A.15: a consistent graph has no causality cycle -/
  porf_acyclic : ∀ G : Graph, G.Wf → cons G → Maz.Acyclic G.porfStep
  /-- (A2), Def. A.16: a prefix of a consistent graph is consistent -/
  prefix_closed : ∀ G G' : Graph, G.Wf → cons G → G'.IsPrefixOf G → cons G'

/-- Maximal extensibility (Def. A.17, without exclusive writes). -/
structure Model.Extensible (M : Model) : Prop where
  /-- a new read that reads from the last write of its location -/
  ext_read : ∀ (G : Graph) (e : TEv) (x : Loc), G.Wf → M.cons G → e.idx = G.cnt e.tid →
    e.act = .read x → M.cons (G.addRead e (G.maxWrite x))
  /-- a new write placed last in the coherence order of its location -/
  ext_write : ∀ (G : Graph) (e : TEv), G.Wf → M.cons G → e.idx = G.cnt e.tid →
    e.IsWrite → M.cons (G.addWrite e (G.maxWrite e.loc))

/-- `porf` is irreflexive in a consistent graph (the form of (A1) used in the
paper's proofs). -/
theorem Model.porf_irrefl (M : Model) {G : Graph} (hG : G.Wf) (hc : M.cons G) (a : Ev) :
    ¬ G.porf a a :=
  M.porf_acyclic G hG hc a

/-- A prefix of a well-formed consistent graph is well-formed and consistent. -/
theorem Model.cons_prefix (M : Model) {G G' : Graph} (hG : G.Wf) (hc : M.cons G)
    (hp : G'.IsPrefixOf G) : G'.Wf ∧ M.cons G' :=
  ⟨hG.of_isPrefixOf hp, M.prefix_closed G G' hG hc hp⟩

namespace Graph

variable (G : Graph)

/-- One step of the sequential-consistency order: `po ∪ rf ∪ co ∪ fr`
(`induction-popl`, def:sc). -/
def scStep (a b : Ev) : Prop := G.po a b ∨ G.rfRel a b ∨ G.coRel a b ∨ G.frRel a b

/-- The maximal extension of `G` by the event `e`: a read reads from the last
write of its location, a write is placed last in the coherence order of its
location (Def. A.17; the extension that `MaxCompletion` uses). -/
def addMax (e : TEv) : Graph :=
  match e.act with
  | .read x => G.addRead e (G.maxWrite x)
  | .write _ _ => G.addWrite e (G.maxWrite e.loc)

variable {G}

theorem addMax_read {e : TEv} {x : Loc} (hact : e.act = .read x) :
    G.addMax e = G.addRead e (G.maxWrite x) := by
  simp [addMax, hact]

theorem addMax_write {e : TEv} (hact : e.IsWrite) :
    G.addMax e = G.addWrite e (G.maxWrite e.loc) := by
  unfold addMax
  cases h : e.act with
  | read x => simp [TEv.IsWrite, h, Act.IsWrite] at hact
  | write x v => rfl

theorem Wf.addMax (hG : G.Wf) {e : TEv} (hidx : e.idx = G.cnt e.tid) : (G.addMax e).Wf := by
  cases h : e.act with
  | read x =>
    rw [addMax_read h]
    exact hG.addRead hidx h (maxWrite_isWriteTo hG x)
  | write x v =>
    have hw : e.IsWrite := by simp [TEv.IsWrite, h, Act.IsWrite]
    rw [addMax_write hw]
    exact hG.addWrite hidx hw (maxWrite_isWriteTo hG e.loc)

/-! ### The new event of an extension is a sink -/

/-- Program-order steps of a graph with one more event, the next event of
its thread: old steps, or steps into the new event. -/
theorem po_of_events_insert {G' : Graph} (hG : G.Wf) {e : TEv} (hidx : e.idx = G.cnt e.tid)
    (hev : G'.events = insert e G.events) {a b : Ev} (h : G'.po a b) :
    G.po a b ∨ b = .th e := by
  cases b with
  | init => cases a <;> exact absurd h (by simp [po])
  | th q =>
    by_cases hqe : q = e
    · exact Or.inr (congrArg Ev.th hqe)
    · left
      cases a with
      | init =>
        have hq : q ∈ G'.events := h
        rw [hev] at hq
        exact (Finset.mem_insert.mp hq).resolve_left hqe
      | th q' =>
        obtain ⟨h1, h2, h3, h4⟩ := h
        rw [hev] at h1 h2
        have hq : q ∈ G.events := (Finset.mem_insert.mp h2).resolve_left hqe
        have hq' : q' ∈ G.events := by
          rcases Finset.mem_insert.mp h1 with hq'e | hq'
          · have hlt := hG.idx_lt_cnt hq
            rw [hq'e] at h3 h4
            rw [← h3] at hlt
            omega
          · exact hq'
        exact ⟨hq', hq, h3, h4⟩

/-- The new event has no program-order successor. -/
theorem not_po_of_events_insert {G' : Graph} (hG : G.Wf) {e : TEv}
    (hidx : e.idx = G.cnt e.tid) (hev : G'.events = insert e G.events) (b : Ev) :
    ¬ G'.po (.th e) b := by
  intro h
  cases b with
  | init => exact absurd h (by simp [po])
  | th q =>
    obtain ⟨-, h2, h3, h4⟩ := h
    rw [hev] at h2
    rcases Finset.mem_insert.mp h2 with hqe | hq
    · rw [hqe] at h4
      exact Nat.lt_irrefl _ h4
    · have hlt := hG.idx_lt_cnt hq
      rw [← h3] at hlt
      omega

/-- Causality steps of `G.addRead e w`: old steps, or steps into `e`. -/
theorem porfStep_addRead (hG : G.Wf) {e : TEv} {w : Ev} (hidx : e.idx = G.cnt e.tid)
    {a b : Ev} (h : (G.addRead e w).porfStep a b) : G.porfStep a b ∨ b = .th e := by
  rcases h with h | ⟨q, hq, hqm, hrf⟩
  · exact (po_of_events_insert hG hidx rfl h).imp Or.inl id
  · by_cases hqe : q = e
    · exact Or.inr (hq.trans (congrArg Ev.th hqe))
    · left
      rw [addRead_rf, Function.update_of_ne hqe] at hrf
      exact Or.inr ⟨q, hq, (Finset.mem_insert.mp hqm).resolve_left hqe, hrf⟩

/-- The new read, with a write of the graph as source, has no causality
successor. -/
theorem not_porfStep_addRead_self (hG : G.Wf) {e : TEv} {x : Loc} {w : Ev}
    (hidx : e.idx = G.cnt e.tid) (hw : G.IsWriteTo x w) (b : Ev) :
    ¬ (G.addRead e w).porfStep (.th e) b := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  rintro (h | ⟨q, -, -, hrf⟩)
  · exact not_po_of_events_insert hG hidx rfl b h
  · by_cases hqe : q = e
    · rw [hqe, addRead_rf, Function.update_self] at hrf
      cases hrf
      exact he hw.1
    · rw [addRead_rf, Function.update_of_ne hqe] at hrf
      exact he (hG.rf_source_mem hrf).2

theorem porfStep_addWrite (hG : G.Wf) {e : TEv} {wp : Ev} (hidx : e.idx = G.cnt e.tid)
    {a b : Ev} (h : (G.addWrite e wp).porfStep a b) : G.porfStep a b ∨ b = .th e := by
  rcases h with h | ⟨q, hq, hqm, hrf⟩
  · exact (po_of_events_insert hG hidx rfl h).imp Or.inl id
  · by_cases hqe : q = e
    · exact Or.inr (hq.trans (congrArg Ev.th hqe))
    · exact Or.inl (Or.inr ⟨q, hq, (Finset.mem_insert.mp hqm).resolve_left hqe, hrf⟩)

theorem not_porfStep_addWrite_self (hG : G.Wf) {e : TEv} {wp : Ev}
    (hidx : e.idx = G.cnt e.tid) (b : Ev) : ¬ (G.addWrite e wp).porfStep (.th e) b := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  rintro (h | ⟨q, -, -, hrf⟩)
  · exact not_po_of_events_insert hG hidx rfl b h
  · exact he (hG.rf_source_mem hrf).2

/-- Steps of the SC order after adding a read from the last write. -/
theorem scStep_addRead_maxWrite (hG : G.Wf) {e : TEv} {x : Loc} (hidx : e.idx = G.cnt e.tid)
    (hact : e.act = .read x) {a b : Ev} (h : (G.addRead e (G.maxWrite x)).scStep a b) :
    G.scStep a b ∨ b = .th e := by
  rcases h with h | h | h | ⟨q, q', y, rfl, rfl, hqm, hqact, hq'co, hrf⟩
  · exact (porfStep_addRead hG hidx (Or.inl h)).imp
      (fun h' => h'.elim Or.inl (fun h'' => Or.inr (Or.inl h''))) id
  · exact (porfStep_addRead hG hidx (Or.inr h)).imp
      (fun h' => h'.elim Or.inl (fun h'' => Or.inr (Or.inl h''))) id
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · left
    have hq'co' : q' ∈ G.co y := hq'co
    by_cases hqe : q = e
    · -- the new read reads the last write: it is from-read-before nothing
      exfalso
      rw [hqe, hact] at hqact
      have hxy : x = y := Act.read.inj hqact
      rw [← hxy] at hq'co' hrf
      rw [hqe, addRead_rf, Function.update_self] at hrf
      have hw' : G.IsWriteTo x (.th q') := (hG.co_mem x q').mp hq'co'
      refine maxWrite_co_maximal hG x hw' ?_
      rcases hrf with hrf | ⟨e'', hrf, hbef⟩
      · rw [Option.some.inj hrf]
        exact ⟨x, hq'co'⟩
      · rw [Option.some.inj hrf]
        exact ⟨x, hbef⟩
    · rw [addRead_rf, Function.update_of_ne hqe] at hrf
      exact Or.inr (Or.inr (Or.inr ⟨q, q', y, rfl, rfl,
        (Finset.mem_insert.mp hqm).resolve_left hqe, hqact, hq'co', hrf⟩))

theorem not_scStep_addRead_maxWrite_self (hG : G.Wf) {e : TEv} {x : Loc}
    (hidx : e.idx = G.cnt e.tid) (hact : e.act = .read x) (b : Ev) :
    ¬ (G.addRead e (G.maxWrite x)).scStep (.th e) b := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  rintro (h | h | h | ⟨q, q', y, hq, rfl, hqm, hqact, hq'co, hrf⟩)
  · exact not_porfStep_addRead_self hG hidx (maxWrite_isWriteTo hG x) b (Or.inl h)
  · exact not_porfStep_addRead_self hG hidx (maxWrite_isWriteTo hG x) b (Or.inr h)
  · cases b with
    | init => exact absurd h (by simp [coRel])
    | th q' =>
      obtain ⟨y, hbef⟩ := h
      have : e ∈ G.co y := hbef.1
      exact he ((hG.co_mem y e).mp this).1
  · have hqe : q = e := (Ev.th.inj hq).symm
    have hq'co' : q' ∈ G.co y := hq'co
    rw [hqe, hact] at hqact
    have hxy : x = y := Act.read.inj hqact
    rw [← hxy] at hq'co' hrf
    rw [hqe, addRead_rf, Function.update_self] at hrf
    have hw' : G.IsWriteTo x (.th q') := (hG.co_mem x q').mp hq'co'
    refine maxWrite_co_maximal hG x hw' ?_
    rcases hrf with hrf | ⟨e'', hrf, hbef⟩
    · rw [Option.some.inj hrf]
      exact ⟨x, hq'co'⟩
    · rw [Option.some.inj hrf]
      exact ⟨x, hbef⟩

/-- The coherence lists after adding a write last. -/
theorem addWrite_maxWrite_co_eq (hG : G.Wf) (e : TEv) (y : Loc) :
    (G.addWrite e (G.maxWrite e.loc)).co y = if y = e.loc then G.co y ++ [e] else G.co y := by
  by_cases hy : y = e.loc
  · simp only [hy, ↓reduceIte]
    exact addWrite_maxWrite_co hG e
  · simp only [hy, ↓reduceIte]
    exact G.addWrite_co_of_ne e _ hy

/-- Steps of the SC order after adding a write last in coherence. -/
theorem scStep_addWrite_maxWrite (hG : G.Wf) {e : TEv} (hidx : e.idx = G.cnt e.tid)
    (hact : e.IsWrite) {a b : Ev} (h : (G.addWrite e (G.maxWrite e.loc)).scStep a b) :
    G.scStep a b ∨ b = .th e := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  have heco : ∀ y, e ∉ G.co y := fun y h => he ((hG.co_mem y e).mp h).1
  have hmem : ∀ y q, q ≠ e → q ∈ (G.addWrite e (G.maxWrite e.loc)).co y → q ∈ G.co y := by
    intro y q hqe hq
    rw [addWrite_maxWrite_co_eq hG e y] at hq
    split at hq
    · rcases List.mem_append.mp hq with hq | hq
      · exact hq
      · exact absurd (List.mem_singleton.mp hq) hqe
    · exact hq
  have hbef : ∀ y p q, q ≠ e → ((G.addWrite e (G.maxWrite e.loc)).co y).Before p q →
      (G.co y).Before p q := by
    intro y p q hqe hpq
    rw [addWrite_maxWrite_co_eq hG e y] at hpq
    split at hpq
    · rcases (List.before_append_singleton_iff (heco y)).mp hpq with h1 | ⟨-, h2⟩
      · exact h1
      · exact absurd h2 hqe
    · exact hpq
  rcases h with h | h | h | ⟨q, q', y, rfl, rfl, hqm, hqact, hq'co, hrf⟩
  · exact (porfStep_addWrite hG hidx (Or.inl h)).imp
      (fun h' => h'.elim Or.inl (fun h'' => Or.inr (Or.inl h''))) id
  · exact (porfStep_addWrite hG hidx (Or.inr h)).imp
      (fun h' => h'.elim Or.inl (fun h'' => Or.inr (Or.inl h''))) id
  · cases b with
    | init => cases a <;> exact absurd h (by simp [coRel])
    | th q =>
      by_cases hqe : q = e
      · exact Or.inr (congrArg Ev.th hqe)
      · left
        refine Or.inr (Or.inr (Or.inl ?_))
        cases a with
        | init =>
          obtain ⟨y, hy⟩ := h
          exact ⟨y, hmem y q hqe hy⟩
        | th q' =>
          obtain ⟨y, hy⟩ := h
          exact ⟨y, hbef y q' q hqe hy⟩
  · by_cases hq'e : q' = e
    · exact Or.inr (congrArg Ev.th hq'e)
    · left
      have hqe : q ≠ e := by
        intro hqe
        rw [hqe] at hqact
        simp [TEv.IsWrite, hqact, Act.IsWrite] at hact
      refine Or.inr (Or.inr (Or.inr ⟨q, q', y, rfl, rfl,
        (Finset.mem_insert.mp hqm).resolve_left hqe, hqact, hmem y q' hq'e hq'co, ?_⟩))
      rcases hrf with hrf | ⟨e'', hrf, hb⟩
      · exact Or.inl hrf
      · exact Or.inr ⟨e'', hrf, hbef y e'' q' hq'e hb⟩

theorem not_scStep_addWrite_maxWrite_self (hG : G.Wf) {e : TEv}
    (hidx : e.idx = G.cnt e.tid) (hact : e.IsWrite) (b : Ev) :
    ¬ (G.addWrite e (G.maxWrite e.loc)).scStep (.th e) b := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  have heco : ∀ y, e ∉ G.co y := fun y h => he ((hG.co_mem y e).mp h).1
  rintro (h | h | h | ⟨q, q', y, hq, rfl, -, hqact, -, -⟩)
  · exact not_porfStep_addWrite_self hG hidx b (Or.inl h)
  · exact not_porfStep_addWrite_self hG hidx b (Or.inr h)
  · cases b with
    | init => exact absurd h (by simp [coRel])
    | th q' =>
      obtain ⟨y, hy⟩ := h
      rw [addWrite_maxWrite_co_eq hG e y] at hy
      split at hy
      · rcases (List.before_append_singleton_iff (heco y)).mp hy with h1 | ⟨h2, -⟩
        · exact heco y h1.1
        · exact heco y h2
      · exact heco y hy.1
  · have hqe : q = e := (Ev.th.inj hq).symm
    rw [hqe] at hqact
    simp [TEv.IsWrite, hqact, Act.IsWrite] at hact

/-- A step of the SC order of a restriction is a step of the graph. -/
theorem scStep_restrict (hG : G.Wf) (s : Finset TEv) {a b : Ev}
    (h : (G.restrict s).scStep a b) : G.scStep a b := by
  rcases h with h | ⟨q, hq, hqm, hrf⟩ | h | h
  · left
    cases a with
    | init =>
      cases b with
      | init => exact absurd h (by simp [po])
      | th q => exact (Finset.mem_inter.mp h).1
    | th q' =>
      cases b with
      | init => exact absurd h (by simp [po])
      | th q => exact ⟨(Finset.mem_inter.mp h.1).1, (Finset.mem_inter.mp h.2.1).1, h.2.2⟩
  · exact Or.inr (Or.inl ⟨q, hq, (Finset.mem_inter.mp hqm).1, (G.restrict_rf_eq_some hrf).1⟩)
  · exact Or.inr (Or.inr (Or.inl ((coRel_restrict_iff hG s a b).mp h).1))
  · exact Or.inr (Or.inr (Or.inr (frRel_restrict_mono G s h)))

/-- The initial graph has no step of the SC order. -/
theorem not_scStep_init (μ : Loc → Val) (a b : Ev) : ¬ (Graph.init μ).scStep a b := by
  rintro (h | ⟨q, -, hq, -⟩ | h | ⟨q, -, -, -, -, hq, -⟩)
  · cases a <;> cases b <;> simp [po, Graph.init] at h
  · simp [Graph.init] at hq
  · cases a <;> cases b <;> simp [coRel, Graph.init, List.Before] at h
  · simp [Graph.init] at hq

end Graph

/-- The maximal extension keeps a consistent graph consistent. -/
theorem Model.Extensible.cons_addMax {M : Model} (hM : M.Extensible) {G : Graph} (hG : G.Wf)
    (hc : M.cons G) {e : TEv} (hidx : e.idx = G.cnt e.tid) : M.cons (G.addMax e) := by
  cases h : e.act with
  | read x =>
    rw [Graph.addMax_read h]
    exact hM.ext_read G e x hG hc hidx h
  | write x v =>
    have hw : e.IsWrite := by simp [TEv.IsWrite, h, Act.IsWrite]
    rw [Graph.addMax_write hw]
    exact hM.ext_write G e hG hc hidx hw

/-- The maximal extension by an available event is an execution. -/
theorem Program.Exec.addMax {P : Program} {G : Graph} (hG : G.Wf) (h : P.Exec G) {e : TEv}
    (he : e ∈ P.avail G) : P.Exec (G.addMax e) := by
  cases hact : e.act with
  | read x =>
    rw [Graph.addMax_read hact]
    exact h.addRead hG he hact (Graph.maxWrite_isWriteTo hG x)
  | write x v =>
    have hw : e.IsWrite := by simp [TEv.IsWrite, hact, Act.IsWrite]
    rw [Graph.addMax_write hw]
    exact h.addWrite hG he hw (Graph.maxWrite_isWriteTo hG e.loc)

/-! ### The models -/

/-- A prefix of a graph without causality cycle has none. -/
private theorem acyclic_restrict_porfStep {G : Graph} (hG : G.Wf) {s : Finset TEv}
    (hs : Maz.PrefixClosed G.porfStep (Graph.evSet (G.events ∩ s)))
    (hac : Maz.Acyclic G.porfStep) : Maz.Acyclic (G.restrict s).porfStep := by
  intro a haa
  have hG0 := hG.restrict hs
  have ham : a ∈ Graph.evSet (G.events ∩ s) := by
    obtain ⟨c, _, hca⟩ := Relation.TransGen.tail'_iff.mp haa
    exact (hG0.mem_of_porfStep hca).2
  exact hac a ((Graph.porf_restrict_iff hs ham).mp haa)

/-- The model that requires only a causality order: `porf` has no cycle. -/
def Free : Model where
  cons := fun G => Maz.Acyclic G.porfStep
  cons_init := by
    intro μ a ha
    obtain ⟨c, hc⟩ := Maz.exists_first_of_transGen ha
    exact Graph.not_scStep_init μ a c (hc.elim Or.inl (fun h => Or.inr (Or.inl h)))
  porf_acyclic := fun _ _ h => h
  prefix_closed := by
    rintro G G' hG hc ⟨s, hs, rfl⟩
    exact acyclic_restrict_porfStep hG hs hc

theorem Free.extensible : Free.Extensible where
  ext_read := fun _ _ x hG hc hidx _ =>
    Maz.Acyclic.of_sink hc (fun _ _ h => Graph.porfStep_addRead hG hidx h)
      (Graph.not_porfStep_addRead_self hG hidx (Graph.maxWrite_isWriteTo hG x))
  ext_write := fun _ _ hG hc hidx _ =>
    Maz.Acyclic.of_sink hc (fun _ _ h => Graph.porfStep_addWrite hG hidx h)
      (Graph.not_porfStep_addWrite_self hG hidx)

/-- Sequential consistency: `po ∪ rf ∪ co ∪ fr` has no cycle
(`induction-popl`, def:sc; the paper's SC). -/
def SC : Model where
  cons := fun G => Maz.Acyclic G.scStep
  cons_init := by
    intro μ a ha
    obtain ⟨c, hc⟩ := Maz.exists_first_of_transGen ha
    exact Graph.not_scStep_init μ a c hc
  porf_acyclic := fun _ _ hc =>
    hc.mono (fun _ _ h => h.elim Or.inl (fun h' => Or.inr (Or.inl h')))
  prefix_closed := by
    rintro G G' hG hc ⟨s, -, rfl⟩
    exact hc.mono (fun _ _ h => Graph.scStep_restrict hG s h)

theorem SC.extensible : SC.Extensible where
  ext_read := fun _ _ _ hG hc hidx hact =>
    Maz.Acyclic.of_sink hc (fun _ _ h => Graph.scStep_addRead_maxWrite hG hidx hact h)
      (Graph.not_scStep_addRead_maxWrite_self hG hidx hact)
  ext_write := fun _ _ hG hc hidx hact =>
    Maz.Acyclic.of_sink hc (fun _ _ h => Graph.scStep_addWrite_maxWrite hG hidx hact h)
      (Graph.not_scStep_addWrite_maxWrite_self hG hidx hact)

/-! ### Example: a graph of Fig. 4 is SC-consistent

Graph 4 of Fig. 4 (both reads read from the writes) is obtained from the
initial graph by four maximal extensions, so it is consistent under every
maximally extensible model, in particular under `SC`. -/

namespace Examples

open Graph

theorem fig4_4_cons (M : Model) (hM : M.Extensible) : M.cons (fig4 (.th wx) (.th wy)) := by
  have h0 : M.cons (Graph.init μ) := M.cons_init μ
  have w0 := Graph.init_wf μ
  have h1 : M.cons ((Graph.init μ).addWrite wx .init) :=
    hM.ext_write _ wx w0 h0 (by decide) (by decide)
  have w1 := w0.addWrite (e := wx) (wp := .init) (by decide) (by decide) trivial
  have h2 : M.cons (((Graph.init μ).addWrite wx .init).addWrite wy .init) :=
    hM.ext_write _ wy w1 h1 (by decide) (by decide)
  have w2 := fig4_writes_wf
  have h3 : M.cons ((((Graph.init μ).addWrite wx .init).addWrite wy .init).addRead rx (.th wx)) :=
    hM.ext_read _ rx 0 w2 h2 (by decide) rfl
  have w3 := w2.addRead (e := rx) (x := 0) (w := .th wx) (by decide) rfl ⟨by decide, 1, rfl⟩
  exact hM.ext_read _ ry 1 w3 h3 (by decide) rfl

example : SC.cons (fig4 (.th wx) (.th wy)) := fig4_4_cons SC SC.extensible
example : Free.cons (fig4 (.th wx) (.th wy)) := fig4_4_cons Free Free.extensible

end Examples

end Trust
