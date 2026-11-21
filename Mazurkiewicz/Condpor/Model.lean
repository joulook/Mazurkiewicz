import Mazurkiewicz.Condpor.Program
import Mazurkiewicz.Condpor.Solver

/-!
# Memory models, and the model with satisfiable constraints

`Models/Model.lean` for graphs with symbolic events.

* `Model`: a consistency predicate with: the initial graph is consistent,
  (A1) a consistent graph has no causality cycle, (A2) consistency is closed
  under prefixes.
* `Model.Extensible`: maximal extensibility of the underlying model. For a
  read and a write as in `Trust`. For an event that is neither (`ext_loc`):
  adding it as the next event of its thread keeps the graph consistent,
  whatever outcome a constraint evaluation gets. These assumptions require
  that consistency is kept under local extension; they do not require that it
  is invariant under changes to existing symbolic events.
* `M.sym S`: the paper's `M_S`: a graph is consistent if it is `M`-consistent
  and its literal set is satisfiable. It is a `Model`
  (`Model.sym`); it is extensible for reads, writes and for local events
  without outcome (`sym_ext_read`, `sym_ext_write`, `sym_ext_loc_none`); for a
  constraint evaluation one of the two outcomes keeps it consistent
  (`sym_ext_cons`), and so does the outcome that a tie-break chooses
  (`sym_cons_addMax`, `sym_cons_of_inv`). The form "either outcome" is not
  provable for `M.sym S` in general: an outcome may be unsatisfiable.
* `Graph.addMax p e`: the maximal extension by `e`. A read reads from the last
  write of its location, a write goes last in coherence, a constraint
  evaluation of `φ` gets the outcome `p G.F φ`, where `p` is the choice of a
  tie-break for a fixed context.
* `Free`, `SC`: the two models of `Trust`, for the new graphs.
-/

namespace Condpor

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
  /-- a new event that is neither a read nor a write, with any outcome -/
  ext_loc : ∀ (G : Graph) (e : TEv) (o : Option Bool), G.Wf → M.cons G →
    e.idx = G.cnt e.tid → e.IsLocal → (o.isSome ↔ e.IsCons) → M.cons (G.addLoc e o)

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
location, a constraint evaluation of `φ` gets the outcome `p G.F φ`, any other
event is added as it is. -/
def addMax (p : Finset Lit → SExpr → Bool) (e : TEv) : Graph :=
  match e.act with
  | .read x => G.addRead e (G.maxWrite x)
  | .write _ _ => G.addWrite e (G.maxWrite e.loc)
  | .cons φ => G.addLoc e (some (p G.F φ))
  | _ => G.addLoc e none

variable {G} {p : Finset Lit → SExpr → Bool}

theorem addMax_read {e : TEv} {x : Loc} (hact : e.act = .read x) :
    G.addMax p e = G.addRead e (G.maxWrite x) := by
  simp [addMax, hact]

theorem addMax_write {e : TEv} (hact : e.IsWrite) :
    G.addMax p e = G.addWrite e (G.maxWrite e.loc) := by
  obtain ⟨v, hv⟩ := TEv.IsWrite.exists_act hact
  simp only [addMax, hv]

theorem addMax_cons {e : TEv} {φ : SExpr} (hact : e.act = .cons φ) :
    G.addMax p e = G.addLoc e (some (p G.F φ)) := by
  simp [addMax, hact]

/-- The maximal extension by a local event adds it with an outcome exactly if
it is a constraint evaluation. -/
theorem addMax_local {e : TEv} (hl : e.IsLocal) :
    ∃ o : Option Bool, (o.isSome ↔ e.IsCons) ∧ G.addMax p e = G.addLoc e o := by
  unfold addMax
  cases h : e.act with
  | read x => simp [TEv.IsLocal, h, Act.IsLocal] at hl
  | write x v => simp [TEv.IsLocal, h, Act.IsLocal] at hl
  | cons φ => exact ⟨_, by simp [TEv.IsCons, h, Act.IsCons], rfl⟩
  | gen s => exact ⟨none, by simp [TEv.IsCons, h, Act.IsCons], rfl⟩
  | block => exact ⟨none, by simp [TEv.IsCons, h, Act.IsCons], rfl⟩
  | error => exact ⟨none, by simp [TEv.IsCons, h, Act.IsCons], rfl⟩

theorem addMax_events (G : Graph) (p : Finset Lit → SExpr → Bool) (a : TEv) :
    (G.addMax p a).events = insert a G.events := by
  unfold addMax
  split <;> rfl

theorem Wf.addMax (hG : G.Wf) {e : TEv} (hidx : e.idx = G.cnt e.tid) : (G.addMax p e).Wf := by
  rcases e.act.isRead_or_isWrite_or_isLocal with h | h | h
  · rw [addMax_read (TEv.IsRead.exists_act h)]
    exact hG.addRead hidx (TEv.IsRead.exists_act h) (maxWrite_isWriteTo hG _)
  · rw [addMax_write h]
    exact hG.addWrite hidx h (maxWrite_isWriteTo hG e.loc)
  · obtain ⟨o, ho, heq⟩ := addMax_local (G := G) (p := p) h
    rw [heq]
    exact hG.addLoc hidx h ho

/-- The literals of the maximal extension: one more for a constraint
evaluation, the same otherwise. -/
theorem F_addMax (hG : G.Wf) {e : TEv} (hidx : e.idx = G.cnt e.tid) :
    (G.addMax p e).F = match e.act with
      | .cons φ => insert (φ, p G.F φ) G.F
      | _ => G.F := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  cases h : e.act with
  | read x => rw [addMax_read h]; exact F_addRead hG _ he
  | write x v =>
    have hw : e.IsWrite := by simp [TEv.IsWrite, h, Act.IsWrite]
    rw [addMax_write hw]; exact F_addWrite hG _ he
  | cons φ => rw [addMax_cons h]; exact F_addLoc_cons _ he h
  | gen s => simp only [addMax, h]; exact F_addLoc_none he
  | block => simp only [addMax, h]; exact F_addLoc_none he
  | error => simp only [addMax, h]; exact F_addLoc_none he

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

/-- Causality steps of `G.addLoc e o`: old steps, or steps into `e`. -/
theorem porfStep_addLoc (hG : G.Wf) {e : TEv} {o : Option Bool} (hidx : e.idx = G.cnt e.tid)
    {a b : Ev} (h : (G.addLoc e o).porfStep a b) : G.porfStep a b ∨ b = .th e := by
  rcases h with h | ⟨q, hq, hqm, hrf⟩
  · exact (po_of_events_insert hG hidx rfl h).imp Or.inl id
  · by_cases hqe : q = e
    · exact Or.inr (hq.trans (congrArg Ev.th hqe))
    · exact Or.inl (Or.inr ⟨q, hq, (Finset.mem_insert.mp hqm).resolve_left hqe, hrf⟩)

theorem not_porfStep_addLoc_self (hG : G.Wf) {e : TEv} {o : Option Bool}
    (hidx : e.idx = G.cnt e.tid) (b : Ev) : ¬ (G.addLoc e o).porfStep (.th e) b := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  rintro (h | ⟨q, -, -, hrf⟩)
  · exact not_po_of_events_insert hG hidx rfl b h
  · exact he (hG.rf_source_mem hrf).2

/-- Steps of the SC order after adding a local event. -/
theorem scStep_addLoc (hG : G.Wf) {e : TEv} {o : Option Bool} (hidx : e.idx = G.cnt e.tid)
    (hact : e.IsLocal) {a b : Ev} (h : (G.addLoc e o).scStep a b) :
    G.scStep a b ∨ b = .th e := by
  rcases h with h | h | h | ⟨q, q', y, rfl, rfl, hqm, hqact, hq'co, hrf⟩
  · exact (porfStep_addLoc hG hidx (Or.inl h)).imp
      (fun h' => h'.elim Or.inl (fun h'' => Or.inr (Or.inl h''))) id
  · exact (porfStep_addLoc hG hidx (Or.inr h)).imp
      (fun h' => h'.elim Or.inl (fun h'' => Or.inr (Or.inl h''))) id
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · left
    have hqe : q ≠ e := by
      rintro rfl
      exact hact.not_isRead (by simp [hqact, Act.IsRead])
    exact Or.inr (Or.inr (Or.inr ⟨q, q', y, rfl, rfl,
      (Finset.mem_insert.mp hqm).resolve_left hqe, hqact, hq'co, hrf⟩))

theorem not_scStep_addLoc_self (hG : G.Wf) {e : TEv} {o : Option Bool}
    (hidx : e.idx = G.cnt e.tid) (hact : e.IsLocal) (b : Ev) :
    ¬ (G.addLoc e o).scStep (.th e) b := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  rintro (h | h | h | ⟨q, q', y, hq, rfl, -, hqact, -, -⟩)
  · exact not_porfStep_addLoc_self hG hidx b (Or.inl h)
  · exact not_porfStep_addLoc_self hG hidx b (Or.inr h)
  · cases b with
    | init => exact absurd h (by simp [coRel])
    | th q' =>
      obtain ⟨y, hbef⟩ := h
      have : e ∈ G.co y := hbef.1
      exact he ((hG.co_mem y e).mp this).1
  · have hqe : q = e := (Ev.th.inj hq).symm
    rw [hqe] at hqact
    exact hact.not_isRead (by simp [hqact, Act.IsRead])

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

/-- The maximal extension keeps a graph consistent in an extensible model,
whatever the choice of outcomes. -/
theorem Model.Extensible.cons_addMax {M : Model} (hM : M.Extensible) {G : Graph} (hG : G.Wf)
    (hc : M.cons G) {e : TEv} (hidx : e.idx = G.cnt e.tid) (p : Finset Lit → SExpr → Bool) :
    M.cons (G.addMax p e) := by
  rcases e.act.isRead_or_isWrite_or_isLocal with h | h | h
  · rw [Graph.addMax_read (TEv.IsRead.exists_act h)]
    exact hM.ext_read G e _ hG hc hidx (TEv.IsRead.exists_act h)
  · rw [Graph.addMax_write h]
    exact hM.ext_write G e hG hc hidx h
  · obtain ⟨o, ho, heq⟩ := Graph.addMax_local (G := G) (p := p) h
    rw [heq]
    exact hM.ext_loc G e o hG hc hidx h ho

/-- The maximal extension by an available event is an execution. -/
theorem Program.Exec.addMax {P : Program} {G : Graph} (hG : G.Wf) (h : P.Exec G) {e : TEv}
    (he : e ∈ P.avail G) (p : Finset Lit → SExpr → Bool) : P.Exec (G.addMax p e) := by
  rcases e.act.isRead_or_isWrite_or_isLocal with hk | hk | hk
  · rw [Graph.addMax_read (TEv.IsRead.exists_act hk)]
    exact h.addRead hG he (TEv.IsRead.exists_act hk) (Graph.maxWrite_isWriteTo hG _)
  · rw [Graph.addMax_write hk]
    exact h.addWrite hG he hk (Graph.maxWrite_isWriteTo hG e.loc)
  · obtain ⟨o, ho, heq⟩ := Graph.addMax_local (G := G) (p := p) hk
    rw [heq]
    exact h.addLoc hG he hk ho

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
  ext_loc := fun _ _ _ hG hc hidx _ _ =>
    Maz.Acyclic.of_sink hc (fun _ _ h => Graph.porfStep_addLoc hG hidx h)
      (Graph.not_porfStep_addLoc_self hG hidx)

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
  ext_loc := fun _ _ _ hG hc hidx hact _ =>
    Maz.Acyclic.of_sink hc (fun _ _ h => Graph.scStep_addLoc hG hidx hact h)
      (Graph.not_scStep_addLoc_self hG hidx hact)

/-! ### The model with satisfiable constraints -/

/-- The paper's `M_S`: `M`-consistent, and the literals are satisfiable. -/
def Model.sym (M : Model) (S : Solver) : Model where
  cons := fun G => M.cons G ∧ S.sat G.F
  cons_init := fun μ => ⟨M.cons_init μ, by
    have : (Graph.init μ).F = ∅ := by simp [Graph.F, Graph.init]
    rw [this]
    exact S.sat_empty⟩
  porf_acyclic := fun G hG hc => M.porf_acyclic G hG hc.1
  prefix_closed := fun G G' hG hc hp =>
    ⟨M.prefix_closed G G' hG hc.1 hp, S.sat_mono (Graph.F_subset_of_isPrefixOf hp) hc.2⟩

variable {M : Model} {S : Solver}

theorem Model.sym_cons_iff {G : Graph} : (M.sym S).cons G ↔ M.cons G ∧ S.sat G.F := by
  unfold Model.sym
  exact Iff.rfl

/-- `M_S` is extensible for a read from the last write. -/
theorem Model.sym_ext_read (hM : M.Extensible) {G : Graph} {e : TEv} {x : Loc} (hG : G.Wf)
    (hc : (M.sym S).cons G) (hidx : e.idx = G.cnt e.tid) (hact : e.act = .read x) :
    (M.sym S).cons (G.addRead e (G.maxWrite x)) := by
  obtain ⟨hc1, hc2⟩ := Model.sym_cons_iff.mp hc
  refine Model.sym_cons_iff.mpr ⟨hM.ext_read G e x hG hc1 hidx hact, ?_⟩
  rw [Graph.F_addRead hG _ (hG.not_mem_of_idx_eq_cnt hidx)]
  exact hc2

/-- `M_S` is extensible for a write placed last. -/
theorem Model.sym_ext_write (hM : M.Extensible) {G : Graph} {e : TEv} (hG : G.Wf)
    (hc : (M.sym S).cons G) (hidx : e.idx = G.cnt e.tid) (hact : e.IsWrite) :
    (M.sym S).cons (G.addWrite e (G.maxWrite e.loc)) := by
  obtain ⟨hc1, hc2⟩ := Model.sym_cons_iff.mp hc
  refine Model.sym_cons_iff.mpr ⟨hM.ext_write G e hG hc1 hidx hact, ?_⟩
  rw [Graph.F_addWrite hG _ (hG.not_mem_of_idx_eq_cnt hidx)]
  exact hc2

/-- `M_S` is extensible for a local event without outcome (generation, block,
error). -/
theorem Model.sym_ext_loc_none (hM : M.Extensible) {G : Graph} {e : TEv} (hG : G.Wf)
    (hc : (M.sym S).cons G) (hidx : e.idx = G.cnt e.tid) (hact : e.IsLocal)
    (hnc : ¬ e.IsCons) : (M.sym S).cons (G.addLoc e none) := by
  obtain ⟨hc1, hc2⟩ := Model.sym_cons_iff.mp hc
  refine Model.sym_cons_iff.mpr ⟨hM.ext_loc G e none hG hc1 hidx hact (by simp [hnc]), ?_⟩
  rw [Graph.F_addLoc_none (hG.not_mem_of_idx_eq_cnt hidx)]
  exact hc2

/-- For a constraint evaluation, one of the two outcomes keeps `M_S`
consistency. -/
theorem Model.sym_ext_cons (hM : M.Extensible) {G : Graph} {e : TEv} {φ : SExpr} (hG : G.Wf)
    (hc : (M.sym S).cons G) (hidx : e.idx = G.cnt e.tid) (hact : e.act = .cons φ) :
    ∃ b, (M.sym S).cons (G.addLoc e (some b)) := by
  obtain ⟨hc1, hc2⟩ := Model.sym_cons_iff.mp hc
  have he := hG.not_mem_of_idx_eq_cnt hidx
  have hl : e.IsLocal := by simp [TEv.IsLocal, hact, Act.IsLocal]
  have hcs : e.IsCons := by simp [TEv.IsCons, hact, Act.IsCons]
  rcases S.sat_split φ hc2 with h | h
  · refine ⟨true, Model.sym_cons_iff.mpr ⟨hM.ext_loc G e _ hG hc1 hidx hl (by simp [hcs]), ?_⟩⟩
    rw [Graph.F_addLoc_cons true he hact]
    exact h
  · refine ⟨false, Model.sym_cons_iff.mpr ⟨hM.ext_loc G e _ hG hc1 hidx hl (by simp [hcs]), ?_⟩⟩
    rw [Graph.F_addLoc_cons false he hact]
    exact h

/-- `M`-consistency and the invariant of a tie-break give `M_S`-consistency. -/
theorem Model.sym_cons_of_inv (τ : TieBreak S) {K : Finset Lit} {G : Graph} (hc : M.cons G)
    (hinv : τ.inv K G.F) : (M.sym S).cons G :=
  Model.sym_cons_iff.mpr ⟨hc, τ.inv_sat hinv⟩

/-- The maximal extension with the outcomes of a tie-break keeps
`M`-consistency and the invariant of the tie-break, for a fixed context. -/
theorem Model.sym_cons_addMax (hM : M.Extensible) (τ : TieBreak S) {K : Finset Lit}
    {G : Graph} (hG : G.Wf) (hc : M.cons G) (hinv : τ.inv K G.F) {e : TEv}
    (hidx : e.idx = G.cnt e.tid) :
    M.cons (G.addMax (τ.pref K) e) ∧ τ.inv K (G.addMax (τ.pref K) e).F := by
  refine ⟨hM.cons_addMax hG hc hidx _, ?_⟩
  rw [Graph.F_addMax hG hidx]
  cases h : e.act with
  | cons φ => exact τ.inv_step φ hinv
  | read x => exact hinv
  | write x v => exact hinv
  | gen s => exact hinv
  | block => exact hinv
  | error => exact hinv

end Condpor
