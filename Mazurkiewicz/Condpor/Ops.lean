import Mazurkiewicz.Condpor.Graph
import Mazurkiewicz.Lib.Finset

/-!
# Operations on graphs

`Trust/Ops.lean` for graphs with symbolic events. Counting, traces,
restriction and prefixes, and the updates of Algorithm 1: adding a read with
its source, adding a write at a place in the coherence order, changing the
source of a read, and (new) `addLoc`: adding an event that is neither a read
nor a write, with its outcome if it is a constraint evaluation (`SetSYM`).
A restriction keeps the outcome of the events it keeps. The last section is
about the literal set `G.F`: which updates keep it, which add a literal, and
that a restriction or a prefix has fewer literals.

Paper: Section 3.1 (restriction `G|E`, prefixes), Algorithm 1 (`SetRF`,
`SetCO`). Coq: `basic/Execution.v` (`Restr`, `Add`, `SetRF`, `SetCO`),
`trust/Execution_Aux.v`.

Differences from the paper and Coq:

* An event is added together with its place in the graph: a read with its
  source (`addRead`), a write with its coherence predecessor (`addWrite`).
  The paper first adds the event (`next_P` "adds it to `G.E`" without updating
  `rf` and `co`) and then calls `SetRF` or `SetCO`. So the paper's `G + e` is
  not a graph value here. Where the paper uses `(G + e).porf` for a write `e`
  (Def. A.6), any `G.addWrite e wp` can be used: its `porf` does not depend on
  `wp` (`porf_addWrite_wp`).
* The only graph values with a read without a source are the intermediate
  graphs of a revisit, described by `WfExcept`.
* `restrict` removes the source of a kept read when that source is removed
  (as Coq's `Restr`, which restricts `rf` at both ends). The paper's `G|E`
  and def:prefix of `induction-popl` are stated for the function `rf`
  restricted to the kept reads. The two readings agree whenever the source of
  every kept read is kept (`restrict_rf_of_source_kept`), in particular on
  prefixes; in a revisit they agree on every read except possibly the
  revisited one, which gets its new source at once (`Wf.restrict_except`,
  `WfExcept.setRF`).

`evAt`, `trace` and `traceBefore` are noncomputable (a `Finset` has no
computable enumeration). The computable versions used for `#eval` work on the
order list of a configuration and are defined with the programs.
-/

namespace Condpor

namespace Graph

open Relation

variable (G : Graph)

/-! ### Events of a thread, traces -/

/-- The event of thread `t` with index `i`, if there is one. -/
noncomputable def evAt (t : Tid) (i : ℕ) : Option TEv :=
  open Classical in
  if h : ∃ e ∈ G.events, e.tid = t ∧ e.idx = i then some h.choose else none

/-- The trace of thread `t` before its event number `i`: the values returned
by its events with index below `i`, in the order of their indices. -/
noncomputable def traceBefore (t : Tid) (i : ℕ) : List (Option Val) :=
  (List.range i).map (fun j => (G.evAt t j).bind G.ret)

/-- The trace of thread `t`: the values returned by all its events
(`induction-popl`, def:trace). -/
noncomputable def trace (t : Tid) : List (Option Val) := G.traceBefore t (G.cnt t)

/-! ### Restriction and prefixes -/

/-- The events selected by a set of thread events, as a set of events: the
initialization event is always selected. -/
def evSet (s : Finset TEv) : Set Ev := {a | match a with | .init => True | .th e => e ∈ s}

/-- The restriction `G|s` of `G` to the thread events in `s` (and `init`): the
events outside `s` are removed, a read whose source is removed loses its
source, and the coherence lists are filtered. See the header of this file for
the relation to the paper's `G|E`. -/
def restrict (s : Finset TEv) : Graph where
  mem := G.mem
  events := G.events ∩ s
  rf := fun e =>
    if e ∈ G.events ∩ s then
      match G.rf e with
      | some (.th w) => if w ∈ s then some (.th w) else none
      | o => o
    else none
  co := fun x => (G.co x).filter (fun e => e ∈ s)
  pol := fun e => if e ∈ G.events ∩ s then G.pol e else none

/-- `G'` is a prefix of `G`: the restriction of `G` to a `porf`-prefix-closed
set of events (paper, Section 3.1; `induction-popl`, def:prefix). -/
def IsPrefixOf (G' G : Graph) : Prop :=
  ∃ s : Finset TEv, Maz.PrefixClosed G.porfStep (evSet (G.events ∩ s)) ∧ G' = G.restrict s

/-! ### The updates of Algorithm 1 -/

/-- Add the read `e` with source `w`. (`SetRF (Add G e) e w`.) -/
def addRead (e : TEv) (w : Ev) : Graph where
  mem := G.mem
  events := insert e G.events
  rf := Function.update G.rf e (some w)
  co := G.co
  pol := G.pol

/-- Add the write `e` immediately after the write `wp` in the coherence order
of its location. (`SetCO (Add G e) wp e`.) After `init` this is the front of
the list.

The paper's formula for `SetCO` (Section 4.1) speaks of the predecessors and
successors of `wp` in `G.co`. It is read at the location of `e`
(`coRelAt e.loc`): only the list `co e.loc` changes. Read literally for
`wp = init`, which is coherence-before the writes of every location, the
formula would also order `e` before the writes of the other locations,
against Def. 3.2(4). -/
def addWrite (e : TEv) (wp : Ev) : Graph where
  mem := G.mem
  events := insert e G.events
  rf := G.rf
  co := Function.update G.co e.loc
    (match wp with
     | .init => e :: G.co e.loc
     | .th p => (G.co e.loc).insertAfter p e)
  pol := G.pol

/-- Add the event `e`, which is neither a read nor a write, with outcome `o`:
`some b` for a constraint evaluation (`SetSYM (Add G e) e b`), `none` for the
other labels. -/
def addLoc (e : TEv) (o : Option Bool) : Graph where
  mem := G.mem
  events := insert e G.events
  rf := G.rf
  co := G.co
  pol := Function.update G.pol e o

/-- Change the source of the read `r` to `w`. (`SetRF G r w`.) -/
def setRF (r : TEv) (w : Ev) : Graph where
  mem := G.mem
  events := G.events
  rf := Function.update G.rf r (some w)
  co := G.co
  pol := G.pol

@[simp] theorem restrict_mem (s : Finset TEv) : (G.restrict s).mem = G.mem := rfl
@[simp] theorem addRead_mem (e : TEv) (w : Ev) : (G.addRead e w).mem = G.mem := rfl
@[simp] theorem addWrite_mem (e : TEv) (w : Ev) : (G.addWrite e w).mem = G.mem := rfl
@[simp] theorem setRF_mem (r : TEv) (w : Ev) : (G.setRF r w).mem = G.mem := rfl

@[simp] theorem setRF_rf (r : TEv) (w : Ev) :
    (G.setRF r w).rf = Function.update G.rf r (some w) := rfl
@[simp] theorem setRF_events (r : TEv) (w : Ev) : (G.setRF r w).events = G.events := rfl
@[simp] theorem setRF_co (r : TEv) (w : Ev) : (G.setRF r w).co = G.co := rfl
@[simp] theorem setRF_pol (r : TEv) (w : Ev) : (G.setRF r w).pol = G.pol := rfl
@[simp] theorem addRead_pol (e : TEv) (w : Ev) : (G.addRead e w).pol = G.pol := rfl
@[simp] theorem addWrite_pol (e : TEv) (w : Ev) : (G.addWrite e w).pol = G.pol := rfl
@[simp] theorem addLoc_mem (e : TEv) (o : Option Bool) : (G.addLoc e o).mem = G.mem := rfl
@[simp] theorem addLoc_events (e : TEv) (o : Option Bool) :
    (G.addLoc e o).events = insert e G.events := rfl
@[simp] theorem addLoc_rf (e : TEv) (o : Option Bool) : (G.addLoc e o).rf = G.rf := rfl
@[simp] theorem addLoc_co (e : TEv) (o : Option Bool) : (G.addLoc e o).co = G.co := rfl
@[simp] theorem addLoc_pol (e : TEv) (o : Option Bool) :
    (G.addLoc e o).pol = Function.update G.pol e o := rfl
@[simp] theorem restrict_pol (s : Finset TEv) (e : TEv) :
    (G.restrict s).pol e = if e ∈ G.events ∩ s then G.pol e else none := rfl
@[simp] theorem addRead_rf (e : TEv) (w : Ev) :
    (G.addRead e w).rf = Function.update G.rf e (some w) := rfl
@[simp] theorem addRead_events (e : TEv) (w : Ev) :
    (G.addRead e w).events = insert e G.events := rfl
@[simp] theorem addRead_co (e : TEv) (w : Ev) : (G.addRead e w).co = G.co := rfl
@[simp] theorem addWrite_rf (e : TEv) (w : Ev) : (G.addWrite e w).rf = G.rf := rfl
@[simp] theorem addWrite_events (e : TEv) (w : Ev) :
    (G.addWrite e w).events = insert e G.events := rfl
theorem addWrite_co_self (e : TEv) (wp : Ev) :
    (G.addWrite e wp).co e.loc =
      (match wp with
       | .init => e :: G.co e.loc
       | .th p => (G.co e.loc).insertAfter p e) := by
  simp [addWrite]

theorem addWrite_co_of_ne (e : TEv) (wp : Ev) {y : Loc} (hy : y ≠ e.loc) :
    (G.addWrite e wp).co y = G.co y := by
  simp [addWrite, Function.update_of_ne hy]

@[simp] theorem restrict_events (s : Finset TEv) : (G.restrict s).events = G.events ∩ s := rfl
@[simp] theorem restrict_co (s : Finset TEv) (x : Loc) :
    (G.restrict s).co x = (G.co x).filter (fun e => e ∈ s) := rfl

/-- The value of a write depends only on the initial memory. -/
theorem valAt_congr {G G' : Graph} (h : G'.mem = G.mem) : G'.valAt = G.valAt := by
  funext x a
  cases a <;> simp [valAt, h]

@[simp] theorem valAt_restrict (s : Finset TEv) : (G.restrict s).valAt = G.valAt :=
  valAt_congr rfl
@[simp] theorem valAt_addRead (e : TEv) (w : Ev) : (G.addRead e w).valAt = G.valAt :=
  valAt_congr rfl
@[simp] theorem valAt_addWrite (e : TEv) (w : Ev) : (G.addWrite e w).valAt = G.valAt :=
  valAt_congr rfl
@[simp] theorem valAt_setRF (r : TEv) (w : Ev) : (G.setRF r w).valAt = G.valAt :=
  valAt_congr rfl

@[simp] theorem mem_evSet_init (s : Finset TEv) : Ev.init ∈ evSet s := trivial
@[simp] theorem mem_evSet_th (s : Finset TEv) (e : TEv) : Ev.th e ∈ evSet s ↔ e ∈ s := Iff.rfl

theorem evSet_mono {s s' : Finset TEv} (h : s ⊆ s') {a : Ev} (ha : a ∈ evSet s) : a ∈ evSet s' := by
  cases a with
  | init => trivial
  | th e => exact h ha

theorem restrict_rf_of_not_mem {s : Finset TEv} {e : TEv} (he : e ∉ G.events ∩ s) :
    (G.restrict s).rf e = none := by
  simp only [restrict, he, ↓reduceIte]

theorem restrict_rf_of_mem {s : Finset TEv} {e : TEv} (he : e ∈ G.events ∩ s) :
    (G.restrict s).rf e =
      (match G.rf e with
       | some (.th w) => if w ∈ s then some (.th w) else none
       | o => o) := by
  simp only [restrict, he, ↓reduceIte]

/-- A kept read whose source is kept has the same source in the restriction. -/
theorem restrict_rf_of_source_kept {s : Finset TEv} {e : TEv} (he : e ∈ G.events ∩ s)
    (hsrc : ∀ w, G.rf e = some w → w ∈ evSet s) : (G.restrict s).rf e = G.rf e := by
  rw [G.restrict_rf_of_mem he]
  cases h : G.rf e with
  | none => rfl
  | some w =>
    cases w with
    | init => rfl
    | th w0 =>
      have hw : w0 ∈ s := hsrc _ h
      simp [hw]

/-- The source of a read in a restriction, if any, is its source in the graph. -/
theorem restrict_rf_eq_some {s : Finset TEv} {e : TEv} {w : Ev}
    (h : (G.restrict s).rf e = some w) : G.rf e = some w ∧ e ∈ G.events ∩ s ∧ w ∈ evSet s := by
  by_cases he : e ∈ G.events ∩ s
  · rw [G.restrict_rf_of_mem he] at h
    cases h' : G.rf e with
    | none => rw [h'] at h; cases h
    | some w' =>
      rw [h'] at h
      cases w' with
      | init => cases h; exact ⟨rfl, he, trivial⟩
      | th w0 =>
        by_cases hw : w0 ∈ s
        · simp only [hw, ↓reduceIte] at h
          cases h
          exact ⟨rfl, he, hw⟩
        · simp only [hw, ↓reduceIte] at h
          cases h
  · rw [G.restrict_rf_of_not_mem he] at h
    cases h

variable {G}

/-! ### Counting -/

/-- Thread `t` has exactly the indices below `cnt t`. -/
theorem WfExcept.exists_idx_iff {r : TEv} (hG : G.WfExcept r) (t : Tid) (i : ℕ) :
    (∃ e ∈ G.events, e.tid = t ∧ e.idx = i) ↔ i < G.cnt t := by
  set F := G.events.filter (fun e => e.tid = t) with hF
  have hinj : Set.InjOn TEv.idx (F : Set TEv) := by
    intro e he e' he'
    have he := Finset.mem_filter.mp (Finset.mem_coe.mp he)
    have he' := Finset.mem_filter.mp (Finset.mem_coe.mp he')
    exact fun h => hG.idx_inj e he.1 e' he'.1 (he.2.trans he'.2.symm) h
  have hcard : (F.image TEv.idx).card = G.cnt t := Finset.card_image_of_injOn hinj
  have hdown : ∀ i ∈ F.image TEv.idx, ∀ j < i, j ∈ F.image TEv.idx := by
    intro i hi j hj
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
    have he := Finset.mem_filter.mp he
    obtain ⟨e', he', ht, rfl⟩ := hG.idx_contig e he.1 j hj
    exact Finset.mem_image.mpr ⟨e', Finset.mem_filter.mpr ⟨he', ht.trans he.2⟩, rfl⟩
  have hrange := Finset.eq_range_of_downClosed hdown
  rw [hcard] at hrange
  rw [← Finset.mem_range, ← hrange, Finset.mem_image]
  constructor
  · rintro ⟨e, he, ht, hi⟩; exact ⟨e, Finset.mem_filter.mpr ⟨he, ht⟩, hi⟩
  · rintro ⟨e, he, hi⟩
    have he := Finset.mem_filter.mp he
    exact ⟨e, he.1, he.2, hi⟩

theorem Wf.exists_idx_iff (hG : G.Wf) (t : Tid) (i : ℕ) :
    (∃ e ∈ G.events, e.tid = t ∧ e.idx = i) ↔ i < G.cnt t :=
  (hG.wfExcept ⟨0, 0, .read 0⟩).exists_idx_iff t i

theorem Wf.idx_lt_cnt (hG : G.Wf) {e : TEv} (he : e ∈ G.events) : e.idx < G.cnt e.tid :=
  (hG.exists_idx_iff e.tid e.idx).mp ⟨e, he, rfl, rfl⟩

theorem evAt_eq_some_of_inj
    (hinj : ∀ e ∈ G.events, ∀ e' ∈ G.events, e.tid = e'.tid → e.idx = e'.idx → e = e')
    {e : TEv} (he : e ∈ G.events) : G.evAt e.tid e.idx = some e := by
  unfold evAt
  have h : ∃ e' ∈ G.events, e'.tid = e.tid ∧ e'.idx = e.idx := ⟨e, he, rfl, rfl⟩
  rw [dite_eq_left_of_eq_true (eq_true h)]
  have hc := h.choose_spec
  exact congrArg some (hinj _ hc.1 _ he hc.2.1 hc.2.2)

/-- The event at a position, given an event of the graph at that position. -/
theorem evAt_eq_some_of_inj'
    (hinj : ∀ e ∈ G.events, ∀ e' ∈ G.events, e.tid = e'.tid → e.idx = e'.idx → e = e')
    {e : TEv} (he : e ∈ G.events) {t : Tid} {i : ℕ} (ht : e.tid = t) (hi : e.idx = i) :
    G.evAt t i = some e := by
  subst ht; subst hi
  exact evAt_eq_some_of_inj hinj he

/-- If `evAt` finds an event, it is an event of the graph at that position. -/
theorem evAt_eq_some_iff_spec {t : Tid} {i : ℕ} {q : TEv} (h : G.evAt t i = some q) :
    q ∈ G.events ∧ q.tid = t ∧ q.idx = i := by
  unfold evAt at h
  split at h
  · next hex =>
    cases h
    exact hex.choose_spec
  · cases h

theorem traceBefore_length (G : Graph) (t : Tid) (i : ℕ) : (G.traceBefore t i).length = i := by
  simp [traceBefore]

theorem Wf.evAt_eq_some (hG : G.Wf) {e : TEv} (he : e ∈ G.events) :
    G.evAt e.tid e.idx = some e := by
  unfold evAt
  have h : ∃ e' ∈ G.events, e'.tid = e.tid ∧ e'.idx = e.idx := ⟨e, he, rfl, rfl⟩
  rw [dite_eq_left_of_eq_true (eq_true h)]
  have hc := h.choose_spec
  exact congrArg some (hG.idx_inj _ hc.1 _ he hc.2.1 hc.2.2)

/-- The next event of a thread is not in the graph. -/
theorem Wf.not_mem_of_idx_eq_cnt (hG : G.Wf) {e : TEv} (hidx : e.idx = G.cnt e.tid) :
    e ∉ G.events := by
  intro he
  have := hG.idx_lt_cnt he
  omega

theorem trace_length (G : Graph) (t : Tid) : (G.trace t).length = G.cnt t := by
  simp [trace, traceBefore]

theorem traceBefore_eq_take (G : Graph) (t : Tid) {i : ℕ} (hi : i ≤ G.cnt t) :
    G.traceBefore t i = (G.trace t).take i := by
  unfold trace traceBefore
  rw [← List.map_take, List.take_range, Nat.min_eq_left hi]

theorem WfExcept.not_mem_of_idx_eq_cnt {r : TEv} (hG : G.WfExcept r) {e : TEv}
    (hidx : e.idx = G.cnt e.tid) : e ∉ G.events := by
  intro he
  have := (hG.exists_idx_iff e.tid e.idx).mp ⟨e, he, rfl, rfl⟩
  omega

/-- `IsWriteTo` depends only on the events, and is kept when events are added. -/
theorem IsWriteTo.mono {G G' : Graph} (h : G.events ⊆ G'.events) {x : Loc} {w : Ev}
    (hw : G.IsWriteTo x w) : G'.IsWriteTo x w := by
  cases w with
  | init => trivial
  | th e => exact ⟨h hw.1, hw.2⟩

/-- A graph that is well-formed except at `r` is well-formed if `r` is not one
of its reads. -/
theorem WfExcept.wf {r : TEv} (hG : G.WfExcept r)
    (hr : r ∈ G.events → ∀ x, r.act ≠ .read x) : G.Wf where
  idx_inj := hG.idx_inj
  idx_contig := hG.idx_contig
  rf_read := by
    intro e1 h1 y hy
    by_cases h : e1 = r
    · subst h
      exact absurd hy (hr h1 y)
    · exact hG.rf_read e1 h1 h y hy
  rf_none := hG.rf_none
  co_mem := hG.co_mem
  co_nodup := hG.co_nodup
  pol_isSome := hG.pol_isSome

/-- An event outside the graph has no outcome. -/
theorem Wf.pol_none (hG : G.Wf) {e : TEv} (he : e ∉ G.events) : G.pol e = none := by
  by_contra h
  exact he ((hG.pol_isSome e).mp (Option.isSome_iff_ne_none.mpr h)).1

/-- An event with an outcome is a constraint evaluation of the graph. -/
theorem Wf.pol_some (hG : G.Wf) {e : TEv} {b : Bool} (h : G.pol e = some b) :
    e ∈ G.events ∧ e.IsCons :=
  (hG.pol_isSome e).mp (by simp [h])

/-- A constraint evaluation of the graph has an outcome. -/
theorem Wf.exists_pol (hG : G.Wf) {e : TEv} (he : e ∈ G.events) (hc : e.IsCons) :
    ∃ b, G.pol e = some b :=
  Option.isSome_iff_exists.mp ((hG.pol_isSome e).mpr ⟨he, hc⟩)

/-! ### Well-formedness of the updates -/

/-- Adding a read as the next event of its thread, with a write to its location
as source, keeps the graph well-formed. -/
theorem Wf.addRead (hG : G.Wf) {e : TEv} {x : Loc} {w : Ev}
    (hidx : e.idx = G.cnt e.tid) (hact : e.act = .read x) (hw : G.IsWriteTo x w) :
    (G.addRead e w).Wf := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  have hsub : G.events ⊆ (G.addRead e w).events := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e1 h1 e2 h2 ht hi
    simp only [addRead_events, Finset.mem_insert] at h1 h2
    rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
    · rfl
    · have := hG.idx_lt_cnt h2
      rw [← ht] at this
      omega
    · have := hG.idx_lt_cnt h1
      rw [ht] at this
      omega
    · exact hG.idx_inj _ h1 _ h2 ht hi
  · intro e1 h1 i hi
    simp only [addRead_events, Finset.mem_insert] at h1
    rcases h1 with rfl | h1
    · rw [hidx] at hi
      obtain ⟨e', he', ht, hi'⟩ := (hG.exists_idx_iff _ _).mpr hi
      exact ⟨e', Finset.mem_insert_of_mem he', ht, hi'⟩
    · obtain ⟨e', he', ht, hi'⟩ := hG.idx_contig e1 h1 i hi
      exact ⟨e', Finset.mem_insert_of_mem he', ht, hi'⟩
  · intro e1 h1 y hy
    simp only [addRead_events, Finset.mem_insert] at h1
    by_cases h : e1 = e
    · subst h
      have hxy : x = y := by rw [hact] at hy; exact Act.read.inj hy
      subst hxy
      exact ⟨w, by simp, hw.mono hsub⟩
    · have h1' : e1 ∈ G.events := h1.resolve_left h
      obtain ⟨w', hw', hw''⟩ := hG.rf_read e1 h1' y hy
      exact ⟨w', by simp [Function.update_of_ne h, hw'], hw''.mono hsub⟩
  · intro e1 h1
    have hne : e1 ≠ e := by
      rintro rfl
      rcases h1 with h1 | h1
      · exact h1 (by simp)
      · simp [TEv.IsRead, hact, Act.IsRead] at h1
    have h1' : e1 ∉ G.events ∨ ¬ e1.IsRead :=
      h1.imp (fun h hm => h (Finset.mem_insert_of_mem hm)) id
    simp [Function.update_of_ne hne, hG.rf_none e1 h1']
  · intro y e1
    rw [addRead_co, hG.co_mem]
    simp only [addRead_events, Finset.mem_insert]
    constructor
    · rintro ⟨h, hv⟩
      exact ⟨Or.inr h, hv⟩
    · rintro ⟨h | h, v, hv⟩
      · subst h
        rw [hact] at hv
        cases hv
      · exact ⟨h, v, hv⟩
  · intro y
    exact hG.co_nodup y
  · intro e1
    rw [addRead_pol, hG.pol_isSome]
    simp only [addRead_events, Finset.mem_insert]
    constructor
    · rintro ⟨h, hc⟩
      exact ⟨Or.inr h, hc⟩
    · rintro ⟨h | h, hc⟩
      · subst h
        simp [TEv.IsCons, hact, Act.IsCons] at hc
      · exact ⟨h, hc⟩

/-- Adding a write as the next event of its thread, after `init` or after a
write to the same location. -/
theorem WfExcept.addWrite {r : TEv} (hG : G.WfExcept r) {e : TEv} {wp : Ev}
    (hidx : e.idx = G.cnt e.tid) (hact : e.IsWrite) (hwp : G.IsWriteTo e.loc wp) :
    (G.addWrite e wp).WfExcept r := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  have hlt : ∀ q ∈ G.events, q.idx < G.cnt q.tid :=
    fun q hq => (hG.exists_idx_iff _ _).mp ⟨q, hq, rfl, rfl⟩
  have hsub : G.events ⊆ (G.addWrite e wp).events := by simp
  obtain ⟨v, hact'⟩ := TEv.IsWrite.exists_act hact
  have heco : e ∉ G.co e.loc := fun h => he ((hG.co_mem e.loc e).mp h).1
  have hL : ∀ e1, e1 ∈ (G.addWrite e wp).co e.loc ↔ e1 = e ∨ e1 ∈ G.co e.loc := by
    intro e1
    rw [G.addWrite_co_self e wp]
    cases wp <;> simp
  have hLn : ((G.addWrite e wp).co e.loc).Nodup := by
    rw [G.addWrite_co_self e wp]
    cases wp with
    | init => exact List.nodup_cons.mpr ⟨heco, hG.co_nodup e.loc⟩
    | th p => exact (hG.co_nodup e.loc).insertAfter heco
  have hother : ∀ y, y ≠ e.loc → (G.addWrite e wp).co y = G.co y :=
    fun y hy => G.addWrite_co_of_ne e wp hy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e1 h1 e2 h2 ht hi
    simp only [addWrite_events, Finset.mem_insert] at h1 h2
    rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
    · rfl
    · have := hlt _ h2
      rw [← ht] at this
      omega
    · have := hlt _ h1
      rw [ht] at this
      omega
    · exact hG.idx_inj _ h1 _ h2 ht hi
  · intro e1 h1 i hi
    simp only [addWrite_events, Finset.mem_insert] at h1
    rcases h1 with rfl | h1
    · rw [hidx] at hi
      obtain ⟨e', he', ht, hi'⟩ := (hG.exists_idx_iff _ _).mpr hi
      exact ⟨e', Finset.mem_insert_of_mem he', ht, hi'⟩
    · obtain ⟨e', he', ht, hi'⟩ := hG.idx_contig e1 h1 i hi
      exact ⟨e', Finset.mem_insert_of_mem he', ht, hi'⟩
  · intro e1 h1 hne y hy
    simp only [addWrite_events, Finset.mem_insert] at h1
    have h1' : e1 ∈ G.events := by
      rcases h1 with rfl | h1
      · rw [hact'] at hy
        cases hy
      · exact h1
    obtain ⟨w', hw', hw''⟩ := hG.rf_read e1 h1' hne y hy
    exact ⟨w', hw', hw''.mono hsub⟩
  · intro e1 h1
    exact hG.rf_none e1 (h1.imp (fun h hm => h (Finset.mem_insert_of_mem hm)) id)
  · intro y e1
    simp only [addWrite_events, Finset.mem_insert]
    by_cases hy : y = e.loc
    · rw [hy, hL, hG.co_mem]
      constructor
      · rintro (rfl | ⟨h, hv⟩)
        · exact ⟨Or.inl rfl, v, hact'⟩
        · exact ⟨Or.inr h, hv⟩
      · rintro ⟨rfl | h, hv⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h, hv⟩
    · rw [hother y hy, hG.co_mem]
      constructor
      · rintro ⟨h, hv⟩
        exact ⟨Or.inr h, hv⟩
      · rintro ⟨rfl | h, v', hv⟩
        · rw [hact'] at hv
          exact absurd (Act.write.inj hv).1.symm hy
        · exact ⟨h, v', hv⟩
  · intro y
    by_cases hy : y = e.loc
    · rw [hy]
      exact hLn
    · rw [hother y hy]
      exact hG.co_nodup y
  · intro e1
    rw [addWrite_pol, hG.pol_isSome]
    simp only [addWrite_events, Finset.mem_insert]
    constructor
    · rintro ⟨h, hc⟩
      exact ⟨Or.inr h, hc⟩
    · rintro ⟨h | h, hc⟩
      · subst h
        simp [TEv.IsCons, hact', Act.IsCons] at hc
      · exact ⟨h, hc⟩

theorem Wf.addWrite (hG : G.Wf) {e : TEv} {wp : Ev}
    (hidx : e.idx = G.cnt e.tid) (hact : e.IsWrite) (hwp : G.IsWriteTo e.loc wp) :
    (G.addWrite e wp).Wf := by
  refine ((hG.wfExcept e).addWrite hidx hact hwp).wf (fun _ x h => ?_)
  simp [TEv.IsWrite, h, Act.IsWrite] at hact

/-- Giving the read `r` a source, a write of the graph to its location, makes
a graph that is well-formed except at `r` well-formed. -/
theorem WfExcept.setRF {r : TEv} (hG : G.WfExcept r) {x : Loc} {w : Ev}
    (hr : r ∈ G.events) (hact : r.act = .read x) (hw : G.IsWriteTo x w) :
    (G.setRF r w).Wf := by
  refine ⟨hG.idx_inj, hG.idx_contig, ?_, ?_, hG.co_mem, hG.co_nodup, hG.pol_isSome⟩
  · intro e1 h1 y hy
    by_cases h : e1 = r
    · subst h
      have hxy : x = y := by rw [hact] at hy; exact Act.read.inj hy
      subst hxy
      exact ⟨w, by simp, hw⟩
    · obtain ⟨w', hw', hw''⟩ := hG.rf_read e1 h1 h y hy
      exact ⟨w', by simp [Function.update_of_ne h, hw'], hw''⟩
  · intro e1 h1
    have hne : e1 ≠ r := by
      rintro rfl
      rcases h1 with h1 | h1
      · exact h1 hr
      · simp [TEv.IsRead, hact, Act.IsRead] at h1
    simp [Function.update_of_ne hne, hG.rf_none e1 h1]

/-- Restriction to a set that is closed under program order and keeps the
source of every kept read other than `r`. In a revisit, this is the removal of
the deleted events (Algorithm 1, line 25 gives the condition on sources). -/
theorem Wf.restrict_except (hG : G.Wf) {s : Finset TEv} {r : TEv}
    (hpo : Maz.PrefixClosed G.po (evSet (G.events ∩ s)))
    (hrf : ∀ q ∈ G.events ∩ s, q ≠ r → ∀ w, G.rf q = some w → w ∈ evSet s) :
    (G.restrict s).WfExcept r := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e1 h1 e2 h2
    exact hG.idx_inj e1 (Finset.mem_inter.mp h1).1 e2 (Finset.mem_inter.mp h2).1
  · intro e1 h1 i hi
    have h1' := (Finset.mem_inter.mp h1).1
    obtain ⟨e', he', ht, hi'⟩ := hG.idx_contig e1 h1' i hi
    have hpo' : G.po (.th e') (.th e1) := ⟨he', h1', ht, by omega⟩
    exact ⟨e', hpo hpo' h1, ht, hi'⟩
  · intro e1 h1 hne y hy
    obtain ⟨w', hw', hw''⟩ := hG.rf_read e1 (Finset.mem_inter.mp h1).1 y hy
    have hk : ∀ w, G.rf e1 = some w → w ∈ evSet s := hrf e1 h1 hne
    refine ⟨w', by rw [G.restrict_rf_of_source_kept h1 hk, hw'], ?_⟩
    have hw's := hk w' hw'
    cases w' with
    | init => trivial
    | th w0 => exact ⟨Finset.mem_inter.mpr ⟨hw''.1, hw's⟩, hw''.2⟩
  · intro e1 h1
    by_cases he1 : e1 ∈ G.events ∩ s
    · have hw : ¬ e1.IsRead := h1.resolve_left (fun h => h he1)
      rw [G.restrict_rf_of_mem he1, hG.rf_none e1 (Or.inr hw)]
    · exact G.restrict_rf_of_not_mem he1
  · intro y e1
    rw [restrict_co, List.mem_filter, hG.co_mem, restrict_events, Finset.mem_inter]
    simp only [decide_eq_true_eq]
    tauto
  · intro y
    exact (hG.co_nodup y).filter _
  · intro e1
    rw [restrict_pol]
    by_cases he1 : e1 ∈ G.events ∩ s
    · simp only [he1, ↓reduceIte]
      rw [hG.pol_isSome]
      exact ⟨fun h => ⟨he1, h.2⟩, fun h => ⟨(Finset.mem_inter.mp he1).1, h.2⟩⟩
    · simp [he1]

/-- Restriction to a set that is closed under program order and keeps the
source of every kept read. -/
theorem Wf.restrict_of_sources (hG : G.Wf) {s : Finset TEv}
    (hpo : Maz.PrefixClosed G.po (evSet (G.events ∩ s)))
    (hrf : ∀ q ∈ G.events ∩ s, ∀ w, G.rf q = some w → w ∈ evSet s) :
    (G.restrict s).Wf := by
  refine (hG.restrict_except (r := ⟨0, 0, .write 0 0⟩) hpo
    (fun q hq _ => hrf q hq)).wf (fun _ x h => ?_)
  cases h

/-- The restriction to a `porf`-prefix-closed set is well-formed. -/
theorem Wf.restrict (hG : G.Wf) {s : Finset TEv}
    (hs : Maz.PrefixClosed G.porfStep (evSet (G.events ∩ s))) :
    (G.restrict s).Wf := by
  refine hG.restrict_of_sources (hs.mono (fun _ _ h => Or.inl h)) ?_
  intro q hq w hw
  have hrf : G.rfRel w (.th q) := ⟨q, rfl, (Finset.mem_inter.mp hq).1, hw⟩
  exact evSet_mono Finset.inter_subset_right (hs (Or.inr hrf) hq)

theorem Wf.of_isPrefixOf {G' : Graph} (hG : G.Wf) (h : G'.IsPrefixOf G) : G'.Wf := by
  obtain ⟨s, hs, rfl⟩ := h
  exact hG.restrict hs

/-- A read with a source is in the graph, and so is its source. -/
theorem Wf.rf_source_mem (hG : G.Wf) {e : TEv} {w : Ev} (h : G.rf e = some w) :
    e ∈ G.events ∧ w ∈ evSet G.events := by
  have he : e ∈ G.events := by
    by_contra hne
    rw [hG.rf_none e (Or.inl hne)] at h
    cases h
  refine ⟨he, ?_⟩
  have hr : e.IsRead := by
    by_contra hn
    rw [hG.rf_none e (Or.inr hn)] at h
    cases h
  obtain ⟨w', hw', hw''⟩ := hG.rf_read e he _ (TEv.IsRead.exists_act hr)
  rw [hw'] at h
  cases h
  cases w with
  | init => trivial
  | th w0 => exact hw''.1

/-- Both ends of a causality step are events of the graph. -/
theorem Wf.mem_of_porfStep (hG : G.Wf) {a b : Ev} (h : G.porfStep a b) :
    a ∈ evSet G.events ∧ b ∈ evSet G.events := by
  rcases h with h | ⟨e, rfl, he, hrf⟩
  · cases a with
    | init =>
      cases b with
      | init => exact absurd h (by simp [po])
      | th e' => exact ⟨trivial, h⟩
    | th e =>
      cases b with
      | init => exact absurd h (by simp [po])
      | th e' => exact ⟨h.1, h.2.1⟩
  · exact ⟨(hG.rf_source_mem hrf).2, he⟩

theorem ret_of_isWrite (G : Graph) {e : TEv} (he : e.IsWrite) : G.ret e = none := by
  obtain ⟨v, hv⟩ := TEv.IsWrite.exists_act he
  simp only [ret, hv]

theorem traceBefore_succ (G : Graph) (t : Tid) (i : ℕ) :
    G.traceBefore t (i + 1) = G.traceBefore t i ++ [(G.evAt t i).bind G.ret] := by
  simp [traceBefore, List.range_succ]

/-! ### Returned values and traces -/

/-- A kept event whose source is kept returns the same value. -/
theorem ret_restrict_of_source_kept {s : Finset TEv} {q : TEv}
    (hq : q ∈ G.events ∩ s) (hsrc : ∀ w, G.rf q = some w → w ∈ evSet s) :
    (G.restrict s).ret q = G.ret q := by
  unfold ret
  rw [G.restrict_rf_of_source_kept hq hsrc, valAt_restrict, restrict_pol]
  simp only [hq, ↓reduceIte]

/-- A kept event returns the same value in a prefix. -/
theorem ret_restrict {s : Finset TEv}
    (hs : Maz.PrefixClosed G.porfStep (evSet (G.events ∩ s))) {e : TEv}
    (he : e ∈ G.events ∩ s) : (G.restrict s).ret e = G.ret e := by
  refine ret_restrict_of_source_kept he ?_
  intro w hw
  have hrf : G.rfRel w (.th e) := ⟨e, rfl, (Finset.mem_inter.mp he).1, hw⟩
  exact evSet_mono Finset.inter_subset_right (hs (Or.inr hrf) he)

theorem ret_setRF_of_ne (G : Graph) {q r : TEv} {w : Ev} (hqr : q ≠ r) :
    (G.setRF r w).ret q = G.ret q := by
  unfold ret
  cases q.act <;> simp [Function.update_of_ne hqr]

theorem ret_setRF_self (G : Graph) {r : TEv} {x : Loc} {w : Ev} (hact : r.act = .read x) :
    (G.setRF r w).ret r = some (G.valAt x w) := by
  unfold ret
  simp [hact]

theorem ret_addRead_self (G : Graph) {e : TEv} {x : Loc} {w : Ev} (hact : e.act = .read x) :
    (G.addRead e w).ret e = some (G.valAt x w) := by
  unfold ret
  simp [hact]

theorem ret_addRead_of_ne (G : Graph) {e q : TEv} {w : Ev} (hq : q ≠ e) :
    (G.addRead e w).ret q = G.ret q := by
  unfold ret
  cases q.act <;> simp [Function.update_of_ne hq]

theorem ret_addWrite (G : Graph) (e q : TEv) (wp : Ev) :
    (G.addWrite e wp).ret q = G.ret q := by
  unfold ret
  cases q.act <;> simp

theorem cnt_addRead (hG : G.Wf) {e : TEv} {w : Ev} (hidx : e.idx = G.cnt e.tid) (t : Tid) :
    (G.addRead e w).cnt t = if t = e.tid then G.cnt t + 1 else G.cnt t := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  unfold cnt
  rw [addRead_events, Finset.filter_insert]
  by_cases ht : t = e.tid
  · subst ht
    simp only [↓reduceIte]
    rw [Finset.card_insert_of_notMem]
    exact fun h => he (Finset.mem_filter.mp h).1
  · have ht' : ¬ e.tid = t := fun h => ht h.symm
    simp only [ht, ht', ↓reduceIte]

theorem cnt_addWrite (hG : G.Wf) {e : TEv} {wp : Ev} (hidx : e.idx = G.cnt e.tid) (t : Tid) :
    (G.addWrite e wp).cnt t = if t = e.tid then G.cnt t + 1 else G.cnt t := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  unfold cnt
  rw [addWrite_events, Finset.filter_insert]
  by_cases ht : t = e.tid
  · subst ht
    simp only [↓reduceIte]
    rw [Finset.card_insert_of_notMem]
    exact fun h => he (Finset.mem_filter.mp h).1
  · have ht' : ¬ e.tid = t := fun h => ht h.symm
    simp only [ht, ht', ↓reduceIte]

/-- Restriction keeps the count of a thread all of whose events are kept. -/
theorem cnt_restrict (G : Graph) {s : Finset TEv} {t : Tid}
    (h : ∀ q ∈ G.events, q.tid = t → q ∈ s) : (G.restrict s).cnt t = G.cnt t := by
  unfold cnt
  congr 1
  ext q
  simp only [restrict_events, Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h q h1 h2⟩, h2⟩

/-- The trace of thread `t` before position `i` is unchanged by a restriction
that keeps the events of `t` before `i` and their sources. -/
theorem traceBefore_restrict_of_keep (hG : G.Wf) {s : Finset TEv} {t : Tid} {i : ℕ}
    (hi : i ≤ G.cnt t)
    (hkeep : ∀ q ∈ G.events, q.tid = t → q.idx < i → q ∈ s)
    (hsrc : ∀ q ∈ G.events, q.tid = t → q.idx < i → ∀ w, G.rf q = some w → w ∈ evSet s) :
    (G.restrict s).traceBefore t i = G.traceBefore t i := by
  unfold traceBefore
  apply List.map_congr_left
  intro j hj
  have hj' : j < i := List.mem_range.mp hj
  obtain ⟨q, hq, ht, hqi⟩ := (hG.exists_idx_iff t j).mpr (lt_of_lt_of_le hj' hi)
  have hqs : q ∈ G.events ∩ s := Finset.mem_inter.mpr ⟨hq, hkeep q hq ht (by omega)⟩
  have h1 : G.evAt t j = some q := evAt_eq_some_of_inj' hG.idx_inj hq ht hqi
  have h2 : (G.restrict s).evAt t j = some q :=
    evAt_eq_some_of_inj' (fun a ha b hb => hG.idx_inj a (Finset.mem_inter.mp ha).1 b
      (Finset.mem_inter.mp hb).1) hqs ht hqi
  rw [h1, h2]
  exact ret_restrict_of_source_kept hqs (hsrc q hq ht (by omega))

/-- A well-formed graph without thread events is the initial graph. -/
theorem Wf.eq_init_of_events_eq_empty (hG : G.Wf) (h : G.events = ∅) :
    G = Graph.init G.mem := by
  apply Graph.ext
  · rfl
  · exact h
  · funext e
    exact hG.rf_none e (Or.inl (by simp [h]))
  · funext x
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    have := ((hG.co_mem x a).mp ha).1
    simp [h] at this
  · funext e
    exact hG.pol_none (by simp [h])

/-- The trace before a kept event is unchanged by a restriction that keeps the
earlier events of its thread and their sources. -/
theorem traceBefore_restrict_of_sources (hG : G.Wf) {s : Finset TEv}
    (hpo : Maz.PrefixClosed G.po (evSet (G.events ∩ s))) {e : TEv} (he : e ∈ G.events ∩ s)
    (hsrc : ∀ q ∈ G.events, q.tid = e.tid → q.idx < e.idx →
      ∀ w, G.rf q = some w → w ∈ evSet s) :
    (G.restrict s).traceBefore e.tid e.idx = G.traceBefore e.tid e.idx := by
  unfold traceBefore
  apply List.map_congr_left
  intro j hj
  have hj' : j < e.idx := List.mem_range.mp hj
  have he' := (Finset.mem_inter.mp he).1
  obtain ⟨q, hq, ht, hi⟩ := hG.idx_contig e he' j hj'
  have hpo' : G.po (.th q) (.th e) := ⟨hq, he', ht, by omega⟩
  have hqs : q ∈ G.events ∩ s := hpo hpo' he
  have h1 : G.evAt e.tid j = some q := evAt_eq_some_of_inj' hG.idx_inj hq ht hi
  have h2 : (G.restrict s).evAt e.tid j = some q :=
    evAt_eq_some_of_inj' (fun a ha b hb => hG.idx_inj a (Finset.mem_inter.mp ha).1 b
      (Finset.mem_inter.mp hb).1) hqs ht hi
  rw [h1, h2]
  exact ret_restrict_of_source_kept hqs (hsrc q hq ht (by omega))

/-- The trace before an event of a prefix is the same as in the graph. -/
theorem traceBefore_restrict (hG : G.Wf) {s : Finset TEv}
    (hs : Maz.PrefixClosed G.porfStep (evSet (G.events ∩ s))) {e : TEv}
    (he : e ∈ G.events ∩ s) :
    (G.restrict s).traceBefore e.tid e.idx = G.traceBefore e.tid e.idx := by
  refine traceBefore_restrict_of_sources hG (hs.mono (fun _ _ h => Or.inl h)) he ?_
  intro q hq ht hi w hw
  have he' := (Finset.mem_inter.mp he).1
  have hpo' : G.porfStep (.th q) (.th e) := Or.inl ⟨hq, he', ht, hi⟩
  have hqs : q ∈ G.events ∩ s := hs hpo' he
  have hrf : G.rfRel w (.th q) := ⟨q, rfl, hq, hw⟩
  exact evSet_mono Finset.inter_subset_right (hs (Or.inr hrf) hqs)

theorem traceBefore_addRead_le (hG : G.Wf) {e : TEv} {x : Loc} {w : Ev}
    (hidx : e.idx = G.cnt e.tid) (hact : e.act = .read x) (hw : G.IsWriteTo x w)
    (t : Tid) {i : ℕ} (hi : i ≤ G.cnt t) :
    (G.addRead e w).traceBefore t i = G.traceBefore t i := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  have hG' := hG.addRead hidx hact hw
  unfold traceBefore
  apply List.map_congr_left
  intro j hj
  have hj' : j < G.cnt t := lt_of_lt_of_le (List.mem_range.mp hj) hi
  obtain ⟨q, hq, ht, hi'⟩ := (hG.exists_idx_iff t j).mpr hj'
  have h1 : G.evAt t j = some q := evAt_eq_some_of_inj' hG.idx_inj hq ht hi'
  have h2 : (G.addRead e w).evAt t j = some q :=
    evAt_eq_some_of_inj' hG'.idx_inj (Finset.mem_insert_of_mem hq) ht hi'
  rw [h1, h2]
  exact G.ret_addRead_of_ne (fun h => he (h ▸ hq))

theorem traceBefore_addWrite_le (hG : G.Wf) {e : TEv} {wp : Ev}
    (hidx : e.idx = G.cnt e.tid) (hact : e.IsWrite) (hwp : G.IsWriteTo e.loc wp)
    (t : Tid) {i : ℕ} (hi : i ≤ G.cnt t) :
    (G.addWrite e wp).traceBefore t i = G.traceBefore t i := by
  have hG' := hG.addWrite hidx hact hwp
  unfold traceBefore
  apply List.map_congr_left
  intro j hj
  have hj' : j < G.cnt t := lt_of_lt_of_le (List.mem_range.mp hj) hi
  obtain ⟨q, hq, ht, hi'⟩ := (hG.exists_idx_iff t j).mpr hj'
  have h1 : G.evAt t j = some q := evAt_eq_some_of_inj' hG.idx_inj hq ht hi'
  have h2 : (G.addWrite e wp).evAt t j = some q :=
    evAt_eq_some_of_inj' hG'.idx_inj (Finset.mem_insert_of_mem hq) ht hi'
  rw [h1, h2]
  exact G.ret_addWrite e q wp

/-- Adding a read does not change the trace before any event of the new graph;
for the new event this is the whole old trace of its thread. -/
theorem traceBefore_addRead (hG : G.Wf) {e : TEv} {x : Loc} {w : Ev}
    (hidx : e.idx = G.cnt e.tid) (hact : e.act = .read x) (hw : G.IsWriteTo x w)
    {q : TEv} (hq : q ∈ (G.addRead e w).events) :
    (G.addRead e w).traceBefore q.tid q.idx = G.traceBefore q.tid q.idx := by
  refine traceBefore_addRead_le hG hidx hact hw q.tid ?_
  rcases Finset.mem_insert.mp hq with rfl | hq
  · exact le_of_eq hidx
  · exact le_of_lt (hG.idx_lt_cnt hq)

theorem traceBefore_addWrite (hG : G.Wf) {e : TEv} {wp : Ev}
    (hidx : e.idx = G.cnt e.tid) (hact : e.IsWrite) (hwp : G.IsWriteTo e.loc wp)
    {q : TEv} (hq : q ∈ (G.addWrite e wp).events) :
    (G.addWrite e wp).traceBefore q.tid q.idx = G.traceBefore q.tid q.idx := by
  refine traceBefore_addWrite_le hG hidx hact hwp q.tid ?_
  rcases Finset.mem_insert.mp hq with rfl | hq
  · exact le_of_eq hidx
  · exact le_of_lt (hG.idx_lt_cnt hq)

theorem trace_addRead (hG : G.Wf) {e : TEv} {x : Loc} {w : Ev}
    (hidx : e.idx = G.cnt e.tid) (hact : e.act = .read x) (hw : G.IsWriteTo x w) (t : Tid) :
    (G.addRead e w).trace t =
      if t = e.tid then G.trace t ++ [some (G.valAt x w)] else G.trace t := by
  have hG' := hG.addRead hidx hact hw
  unfold trace
  rw [cnt_addRead hG hidx]
  by_cases ht : t = e.tid
  · subst ht
    simp only [↓reduceIte]
    rw [traceBefore_succ, traceBefore_addRead_le hG hidx hact hw _ le_rfl,
      evAt_eq_some_of_inj' hG'.idx_inj (Finset.mem_insert_self e G.events) rfl hidx]
    simp [G.ret_addRead_self hact]
  · simp only [ht, ↓reduceIte]
    exact traceBefore_addRead_le hG hidx hact hw t le_rfl

theorem trace_addWrite (hG : G.Wf) {e : TEv} {wp : Ev}
    (hidx : e.idx = G.cnt e.tid) (hact : e.IsWrite) (hwp : G.IsWriteTo e.loc wp) (t : Tid) :
    (G.addWrite e wp).trace t = if t = e.tid then G.trace t ++ [none] else G.trace t := by
  have hG' := hG.addWrite hidx hact hwp
  unfold trace
  rw [cnt_addWrite hG hidx]
  by_cases ht : t = e.tid
  · subst ht
    simp only [↓reduceIte]
    rw [traceBefore_succ, traceBefore_addWrite_le hG hidx hact hwp _ le_rfl,
      evAt_eq_some_of_inj' hG'.idx_inj (Finset.mem_insert_self e G.events) rfl hidx]
    simp [G.ret_addWrite, G.ret_of_isWrite hact]
  · simp only [ht, ↓reduceIte]
    exact traceBefore_addWrite_le hG hidx hact hwp t le_rfl

/-! ### Relations under restriction -/

/-- In a prefix, `porf` is the restriction of `porf`. -/
theorem porf_restrict_iff {s : Finset TEv}
    (hs : Maz.PrefixClosed G.porfStep (evSet (G.events ∩ s))) {a b : Ev}
    (hb : b ∈ evSet (G.events ∩ s)) : (G.restrict s).porf a b ↔ G.porf a b := by
  have hstep : (G.restrict s).porfStep = Maz.Restrict G.porfStep (evSet (G.events ∩ s)) := by
    funext a b
    apply propext
    constructor
    · rintro (h | ⟨e, rfl, he, hrf⟩)
      · cases a with
        | init =>
          cases b with
          | init => exact absurd h (by simp [po])
          | th e' => exact ⟨Or.inl (Finset.mem_inter.mp h).1, trivial, h⟩
        | th e =>
          cases b with
          | init => exact absurd h (by simp [po])
          | th e' =>
            exact ⟨Or.inl ⟨(Finset.mem_inter.mp h.1).1, (Finset.mem_inter.mp h.2.1).1, h.2.2⟩,
              h.1, h.2.1⟩
      · obtain ⟨hrf', -, -⟩ := G.restrict_rf_eq_some hrf
        have hstep' : G.porfStep a (.th e) := Or.inr ⟨e, rfl, (Finset.mem_inter.mp he).1, hrf'⟩
        exact ⟨hstep', hs hstep' he, he⟩
    · rintro ⟨h | ⟨e, rfl, he, hrf⟩, ha, hb⟩
      · cases a with
        | init =>
          cases b with
          | init => exact absurd h (by simp [po])
          | th e' => exact Or.inl hb
        | th e =>
          cases b with
          | init => exact absurd h (by simp [po])
          | th e' => exact Or.inl ⟨ha, hb, h.2.2⟩
      · refine Or.inr ⟨e, rfl, hb, ?_⟩
        rw [G.restrict_rf_of_source_kept hb, hrf]
        intro w hw
        rw [hrf] at hw
        cases hw
        exact evSet_mono Finset.inter_subset_right ha
  unfold porf
  rw [hstep]
  exact Maz.transGen_restrict_iff hs hb

theorem coRel_restrict_iff (hG : G.Wf) (s : Finset TEv) (a b : Ev) :
    (G.restrict s).coRel a b ↔
      G.coRel a b ∧ a ∈ evSet (G.events ∩ s) ∧ b ∈ evSet (G.events ∩ s) := by
  cases a with
  | init =>
    cases b with
    | init => simp [coRel]
    | th e' =>
      simp only [coRel, restrict_co, List.mem_filter, decide_eq_true_eq, mem_evSet_init,
        mem_evSet_th, Finset.mem_inter, true_and]
      constructor
      · rintro ⟨x, hx, hs⟩
        exact ⟨⟨x, hx⟩, ((hG.co_mem x e').mp hx).1, hs⟩
      · rintro ⟨⟨x, hx⟩, -, hs⟩
        exact ⟨x, hx, hs⟩
  | th e =>
    cases b with
    | init => simp [coRel]
    | th e' =>
      simp only [coRel, restrict_co, List.before_filter_iff, decide_eq_true_eq, mem_evSet_th,
        Finset.mem_inter]
      constructor
      · rintro ⟨x, hx, hs, hs'⟩
        exact ⟨⟨x, hx⟩, ⟨((hG.co_mem x e).mp hx.1).1, hs⟩, ((hG.co_mem x e').mp hx.2.1).1, hs'⟩
      · rintro ⟨⟨x, hx⟩, ⟨-, hs⟩, -, hs'⟩
        exact ⟨x, hx, hs, hs'⟩

/-- A from-read pair of a restriction is a from-read pair of the graph. -/
theorem frRel_restrict_mono (G : Graph) (s : Finset TEv) {a b : Ev} :
    (G.restrict s).frRel a b → G.frRel a b := by
  rintro ⟨e, e', x, rfl, rfl, he, hact, hco, hrf⟩
  refine ⟨e, e', x, rfl, rfl, (Finset.mem_inter.mp he).1, hact, (List.mem_filter.mp hco).1, ?_⟩
  rcases hrf with hrf | ⟨e'', hrf, hbef⟩
  · exact Or.inl (G.restrict_rf_eq_some hrf).1
  · exact Or.inr ⟨e'', (G.restrict_rf_eq_some hrf).1, (List.before_filter_iff.mp hbef).1⟩

/-! ### Causality into an event -/

theorem not_porfStep_init (G : Graph) (a : Ev) : ¬ G.porfStep a .init := by
  rintro (h | ⟨e, he, -, -⟩)
  · cases a <;> exact absurd h (by simp [po])
  · cases he

/-- Causality steps are kept when events are added and the sources of the old
reads are unchanged. -/
theorem porfStep_mono {G G' : Graph} (hev : G.events ⊆ G'.events)
    (hrf : ∀ q ∈ G.events, G'.rf q = G.rf q) {a b : Ev} (h : G.porfStep a b) :
    G'.porfStep a b := by
  rcases h with h | ⟨q, hq, hqm, hqrf⟩
  · left
    cases a with
    | init =>
      cases b with
      | init => exact absurd h (by simp [po])
      | th y => exact hev h
    | th x =>
      cases b with
      | init => exact absurd h (by simp [po])
      | th y => exact ⟨hev h.1, hev h.2.1, h.2.2⟩
  · exact Or.inr ⟨q, hq, hev hqm, (hrf q hqm).trans hqrf⟩

theorem porf_mono {G G' : Graph} (hev : G.events ⊆ G'.events)
    (hrf : ∀ q ∈ G.events, G'.rf q = G.rf q) {a b : Ev} (h : G.porf a b) : G'.porf a b :=
  Relation.TransGen.mono (fun _ _ h' => porfStep_mono hev hrf h') _ _ h

/-- If `init` is the only event one causality step before `b`, then it is the
only event causally before `b`. -/
theorem eq_init_of_porf (G : Graph) {a b : Ev} (hb : ∀ c, G.porfStep c b → c = .init)
    (h : G.porf a b) : a = .init := by
  obtain ⟨c, hac, hcb⟩ := Relation.TransGen.tail'_iff.mp h
  have hc := hb c hcb
  subst hc
  rcases Relation.ReflTransGen.cases_tail hac with h0 | ⟨d, -, hd⟩
  · exact h0.symm
  · exact absurd hd (G.not_porfStep_init d)

/-- Causality after adding a write does not depend on its place in the
coherence order. So the paper's `(G + e).porf` (Def. A.6) is the `porf` of any
`G.addWrite e wp`. -/
theorem porf_addWrite_wp (G : Graph) (e : TEv) (wp wp' : Ev) :
    (G.addWrite e wp).porf = (G.addWrite e wp').porf := by
  have h : (G.addWrite e wp).porfStep = (G.addWrite e wp').porfStep := by
    funext a b
    cases a <;> cases b <;> rfl
  unfold porf
  rw [h]

/-! ### Prefixes -/

/-- Restricting a well-formed graph to its own events changes nothing. -/
theorem Wf.restrict_self (hG : G.Wf) : G.restrict G.events = G := by
  apply Graph.ext
  · rfl
  · simp
  · funext e
    by_cases he : e ∈ G.events ∩ G.events
    · exact G.restrict_rf_of_source_kept he
        (fun w hw => (hG.rf_source_mem hw).2)
    · rw [G.restrict_rf_of_not_mem he, hG.rf_none e (Or.inl (by simpa using he))]
  · funext x
    rw [restrict_co, List.filter_eq_self]
    intro a ha
    simpa using ((hG.co_mem x a).mp ha).1
  · funext q
    by_cases hq : q ∈ G.events
    · simp [hq]
    · simp [hq, hG.pol_none hq]

theorem restrict_restrict (G : Graph) (s s' : Finset TEv) :
    (G.restrict s).restrict s' = G.restrict (s ∩ s') := by
  apply Graph.ext
  · rfl
  · simp [Finset.inter_assoc]
  · funext e
    by_cases he : e ∈ G.events ∩ (s ∩ s')
    · have he1 : e ∈ G.events ∩ s := by
        simp only [Finset.mem_inter] at he ⊢
        tauto
      have he2 : e ∈ (G.restrict s).events ∩ s' := by
        simp only [restrict_events, Finset.mem_inter] at he ⊢
        tauto
      rw [(G.restrict s).restrict_rf_of_mem he2, G.restrict_rf_of_mem he1,
        G.restrict_rf_of_mem he]
      cases h : G.rf e with
      | none => rfl
      | some w =>
        cases w with
        | init => rfl
        | th w0 =>
          by_cases h1 : w0 ∈ s <;> by_cases h2 : w0 ∈ s' <;> simp [h1, h2]
    · have he2 : e ∉ (G.restrict s).events ∩ s' := by
        simp only [restrict_events, Finset.mem_inter] at he ⊢
        tauto
      rw [(G.restrict s).restrict_rf_of_not_mem he2, G.restrict_rf_of_not_mem he]
  · funext x
    simp only [restrict_co, List.filter_filter, Finset.mem_inter]
    congr 1
    funext a
    simp [Bool.and_comm]
  · funext e
    simp only [restrict_pol, restrict_events, Finset.mem_inter]
    by_cases h1 : e ∈ G.events <;> by_cases h2 : e ∈ s <;> by_cases h3 : e ∈ s' <;>
      simp [h1, h2, h3]

/-- Every well-formed graph is a prefix of itself. -/
theorem Wf.isPrefixOf_refl (hG : G.Wf) : G.IsPrefixOf G := by
  refine ⟨G.events, ?_, hG.restrict_self.symm⟩
  intro a b h _
  simpa using (hG.mem_of_porfStep h).1

/-- The initial graph is a prefix of every graph with the same memory. -/
theorem init_isPrefixOf (G : Graph) : (Graph.init G.mem).IsPrefixOf G := by
  refine ⟨∅, ?_, ?_⟩
  · intro a b h hb
    cases b with
    | init =>
      rcases h with h | ⟨e, he, -, -⟩
      · cases a <;> exact absurd h (by simp [po])
      · cases he
    | th e => simp at hb
  · apply Graph.ext
    · rfl
    · simp [Graph.init]
    · funext e
      rw [G.restrict_rf_of_not_mem (by simp)]
      rfl
    · funext x
      simp [Graph.init]
    · funext e
      simp [Graph.init]

/-- `G` is the restriction of `G.addRead e w` to the events of `G`. -/
theorem restrict_addRead (hG : G.Wf) {e : TEv} {w : Ev} (he : e ∉ G.events) :
    (G.addRead e w).restrict G.events = G := by
  apply Graph.ext
  · rfl
  · simp
  · funext q
    by_cases hq : q ∈ G.events
    · have hne : q ≠ e := fun h => he (h ▸ hq)
      have hq' : q ∈ (G.addRead e w).events ∩ G.events := by simp [hq]
      have hrf : (G.addRead e w).rf q = G.rf q := by simp [Function.update_of_ne hne]
      rw [(G.addRead e w).restrict_rf_of_source_kept hq', hrf]
      intro w' hw'
      rw [hrf] at hw'
      exact (hG.rf_source_mem hw').2
    · rw [(G.addRead e w).restrict_rf_of_not_mem (by simp [hq]), hG.rf_none q (Or.inl hq)]
  · funext x
    rw [restrict_co, addRead_co, List.filter_eq_self]
    intro a ha
    simpa using ((hG.co_mem x a).mp ha).1
  · funext q
    by_cases hq : q ∈ G.events
    · simp [hq]
    · simp [hq, hG.pol_none hq]

/-- `G` is the restriction of `G.addWrite e wp` to the events of `G`. -/
theorem restrict_addWrite (hG : G.Wf) {e : TEv} {wp : Ev} (he : e ∉ G.events) :
    (G.addWrite e wp).restrict G.events = G := by
  have hfil : ∀ x, (G.co x).filter (fun a => a ∈ G.events) = G.co x := by
    intro x
    rw [List.filter_eq_self]
    intro a ha
    simpa using ((hG.co_mem x a).mp ha).1
  apply Graph.ext
  · rfl
  · simp
  · funext q
    by_cases hq : q ∈ G.events
    · have hq' : q ∈ (G.addWrite e wp).events ∩ G.events := by simp [hq]
      rw [(G.addWrite e wp).restrict_rf_of_source_kept hq']
      · rfl
      · intro w' hw'
        exact (hG.rf_source_mem hw').2
    · rw [(G.addWrite e wp).restrict_rf_of_not_mem (by simp [hq])]
      exact (hG.rf_none q (Or.inl hq)).symm
  · funext x
    rw [restrict_co]
    by_cases hx : x = e.loc
    · subst hx
      rw [G.addWrite_co_self e wp]
      cases wp with
      | init => simp [he, hfil]
      | th p => rw [List.filter_insertAfter_of_neg (by simp [he]), hfil]
    · rw [G.addWrite_co_of_ne e wp hx, hfil]
  · funext q
    by_cases hq : q ∈ G.events
    · simp [hq]
    · simp [hq, hG.pol_none hq]

theorem Wf.isPrefixOf_addRead (hG : G.Wf) {e : TEv} {w : Ev}
    (hidx : e.idx = G.cnt e.tid) :
    G.IsPrefixOf (G.addRead e w) := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  refine ⟨G.events, ?_, (restrict_addRead hG he).symm⟩
  intro a b h hb
  cases a with
  | init => trivial
  | th q' =>
    cases b with
    | init =>
      rcases h with h | ⟨q, hq, -, -⟩
      · exact absurd h (by simp [po])
      · cases hq
    | th q =>
      have hq : q ∈ G.events := (Finset.mem_inter.mp hb).2
      have hne : q ≠ e := fun h => he (h ▸ hq)
      suffices hq' : q' ∈ G.events by
        simp only [mem_evSet_th, addRead_events, Finset.mem_inter, Finset.mem_insert]
        exact ⟨Or.inr hq', hq'⟩
      rcases h with h | ⟨q₀, hq₀, -, hrf⟩
      · rcases Finset.mem_insert.mp h.1 with rfl | h1
        · have := hG.idx_lt_cnt hq
          have h3 := h.2.2.1
          have h4 := h.2.2.2
          rw [← h3] at this
          omega
        · exact h1
      · cases hq₀
        rw [addRead_rf, Function.update_of_ne hne] at hrf
        exact (hG.rf_source_mem hrf).2

theorem Wf.isPrefixOf_addWrite (hG : G.Wf) {e : TEv} {wp : Ev}
    (hidx : e.idx = G.cnt e.tid) :
    G.IsPrefixOf (G.addWrite e wp) := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  refine ⟨G.events, ?_, (restrict_addWrite hG he).symm⟩
  intro a b h hb
  cases a with
  | init => trivial
  | th q' =>
    cases b with
    | init =>
      rcases h with h | ⟨q, hq, -, -⟩
      · exact absurd h (by simp [po])
      · cases hq
    | th q =>
      have hq : q ∈ G.events := (Finset.mem_inter.mp hb).2
      suffices hq' : q' ∈ G.events by
        simp only [mem_evSet_th, addWrite_events, Finset.mem_inter, Finset.mem_insert]
        exact ⟨Or.inr hq', hq'⟩
      rcases h with h | ⟨q₀, hq₀, -, hrf⟩
      · rcases Finset.mem_insert.mp h.1 with rfl | h1
        · have := hG.idx_lt_cnt hq
          have h3 := h.2.2.1
          have h4 := h.2.2.2
          rw [← h3] at this
          omega
        · exact h1
      · cases hq₀
        exact (hG.rf_source_mem hrf).2

/-! ### Local events: generation, constraint evaluation, block, error -/

/-- Adding an event that is neither a read nor a write as the next event of
its thread, with an outcome exactly if it is a constraint evaluation. -/
theorem Wf.addLoc (hG : G.Wf) {e : TEv} {o : Option Bool}
    (hidx : e.idx = G.cnt e.tid) (hact : e.IsLocal) (ho : o.isSome ↔ e.IsCons) :
    (G.addLoc e o).Wf := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e1 h1 e2 h2 ht hi
    simp only [addLoc_events, Finset.mem_insert] at h1 h2
    rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
    · rfl
    · have := hG.idx_lt_cnt h2
      rw [← ht] at this
      omega
    · have := hG.idx_lt_cnt h1
      rw [ht] at this
      omega
    · exact hG.idx_inj _ h1 _ h2 ht hi
  · intro e1 h1 i hi
    simp only [addLoc_events, Finset.mem_insert] at h1
    rcases h1 with rfl | h1
    · rw [hidx] at hi
      obtain ⟨e', he', ht, hi'⟩ := (hG.exists_idx_iff _ _).mpr hi
      exact ⟨e', Finset.mem_insert_of_mem he', ht, hi'⟩
    · obtain ⟨e', he', ht, hi'⟩ := hG.idx_contig e1 h1 i hi
      exact ⟨e', Finset.mem_insert_of_mem he', ht, hi'⟩
  · intro e1 h1 y hy
    simp only [addLoc_events, Finset.mem_insert] at h1
    have h1' : e1 ∈ G.events := by
      rcases h1 with rfl | h1
      · exact absurd (show e1.IsRead by simp [TEv.IsRead, hy, Act.IsRead]) hact.not_isRead
      · exact h1
    obtain ⟨w', hw', hw''⟩ := hG.rf_read e1 h1' y hy
    exact ⟨w', hw', hw''.mono (by simp)⟩
  · intro e1 h1
    rw [addLoc_rf]
    by_cases h : e1 ∈ G.events
    · exact hG.rf_none e1 (Or.inr (h1.resolve_left (fun hn => hn (by simp [h]))))
    · exact hG.rf_none e1 (Or.inl h)
  · intro y e1
    rw [addLoc_co, hG.co_mem]
    simp only [addLoc_events, Finset.mem_insert]
    constructor
    · rintro ⟨h, hv⟩
      exact ⟨Or.inr h, hv⟩
    · rintro ⟨h | h, v, hv⟩
      · subst h
        exact absurd (show e1.IsWrite by simp [TEv.IsWrite, hv, Act.IsWrite]) hact.not_isWrite
      · exact ⟨h, v, hv⟩
  · intro y
    exact hG.co_nodup y
  · intro e1
    rw [addLoc_pol]
    simp only [addLoc_events, Finset.mem_insert]
    by_cases h : e1 = e
    · subst h
      rw [Function.update_self, ho]
      exact ⟨fun hc => ⟨Or.inl rfl, hc⟩, fun hc => hc.2⟩
    · rw [Function.update_of_ne h, hG.pol_isSome]
      exact ⟨fun hc => ⟨Or.inr hc.1, hc.2⟩, fun hc => ⟨hc.1.resolve_left h, hc.2⟩⟩

@[simp] theorem valAt_addLoc (G : Graph) (e : TEv) (o : Option Bool) :
    (G.addLoc e o).valAt = G.valAt := valAt_congr rfl

theorem ret_addLoc_of_ne (G : Graph) {e q : TEv} {o : Option Bool} (hq : q ≠ e) :
    (G.addLoc e o).ret q = G.ret q := by
  unfold ret
  cases q.act <;> simp [Function.update_of_ne hq]

/-- The value returned by a new local event: its outcome, as a value. -/
theorem ret_addLoc_self (G : Graph) {e : TEv} {o : Option Bool} (hact : e.IsLocal)
    (ho : o.isSome ↔ e.IsCons) :
    (G.addLoc e o).ret e = o.map (fun b => if b then 1 else 0) := by
  unfold ret
  cases h : e.act with
  | read x => simp [TEv.IsLocal, h, Act.IsLocal] at hact
  | write x v => simp [TEv.IsLocal, h, Act.IsLocal] at hact
  | cons φ => simp
  | gen s =>
    have : o = none := by
      cases o with
      | none => rfl
      | some b => simp [TEv.IsCons, h, Act.IsCons] at ho
    simp [this]
  | block =>
    have : o = none := by
      cases o with
      | none => rfl
      | some b => simp [TEv.IsCons, h, Act.IsCons] at ho
    simp [this]
  | error =>
    have : o = none := by
      cases o with
      | none => rfl
      | some b => simp [TEv.IsCons, h, Act.IsCons] at ho
    simp [this]

theorem cnt_addLoc (hG : G.Wf) {e : TEv} {o : Option Bool} (hidx : e.idx = G.cnt e.tid)
    (t : Tid) : (G.addLoc e o).cnt t = if t = e.tid then G.cnt t + 1 else G.cnt t := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  unfold cnt
  rw [addLoc_events, Finset.filter_insert]
  by_cases ht : t = e.tid
  · subst ht
    simp only [↓reduceIte]
    rw [Finset.card_insert_of_notMem]
    exact fun h => he (Finset.mem_filter.mp h).1
  · have ht' : ¬ e.tid = t := fun h => ht h.symm
    simp only [ht, ht', ↓reduceIte]

theorem traceBefore_addLoc_le (hG : G.Wf) {e : TEv} {o : Option Bool}
    (hidx : e.idx = G.cnt e.tid) (hact : e.IsLocal) (ho : o.isSome ↔ e.IsCons)
    (t : Tid) {i : ℕ} (hi : i ≤ G.cnt t) :
    (G.addLoc e o).traceBefore t i = G.traceBefore t i := by
  have hG' := hG.addLoc hidx hact ho
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  unfold traceBefore
  apply List.map_congr_left
  intro j hj
  have hj' : j < G.cnt t := lt_of_lt_of_le (List.mem_range.mp hj) hi
  obtain ⟨q, hq, ht, hi'⟩ := (hG.exists_idx_iff t j).mpr hj'
  have h1 : G.evAt t j = some q := evAt_eq_some_of_inj' hG.idx_inj hq ht hi'
  have h2 : (G.addLoc e o).evAt t j = some q :=
    evAt_eq_some_of_inj' hG'.idx_inj (Finset.mem_insert_of_mem hq) ht hi'
  rw [h1, h2]
  exact G.ret_addLoc_of_ne (fun h => he (h ▸ hq))

theorem traceBefore_addLoc (hG : G.Wf) {e : TEv} {o : Option Bool}
    (hidx : e.idx = G.cnt e.tid) (hact : e.IsLocal) (ho : o.isSome ↔ e.IsCons)
    {q : TEv} (hq : q ∈ (G.addLoc e o).events) :
    (G.addLoc e o).traceBefore q.tid q.idx = G.traceBefore q.tid q.idx := by
  refine traceBefore_addLoc_le hG hidx hact ho q.tid ?_
  rcases Finset.mem_insert.mp hq with rfl | hq
  · exact le_of_eq hidx
  · exact le_of_lt (hG.idx_lt_cnt hq)

/-- The trace of the thread of a new local event gets the outcome of the
event, as a value. -/
theorem trace_addLoc (hG : G.Wf) {e : TEv} {o : Option Bool}
    (hidx : e.idx = G.cnt e.tid) (hact : e.IsLocal) (ho : o.isSome ↔ e.IsCons) (t : Tid) :
    (G.addLoc e o).trace t =
      if t = e.tid then G.trace t ++ [o.map (fun b => if b then 1 else 0)] else G.trace t := by
  have hG' := hG.addLoc hidx hact ho
  unfold trace
  rw [cnt_addLoc hG hidx]
  by_cases ht : t = e.tid
  · subst ht
    simp only [↓reduceIte]
    rw [traceBefore_succ, traceBefore_addLoc_le hG hidx hact ho _ le_rfl,
      evAt_eq_some_of_inj' hG'.idx_inj (Finset.mem_insert_self e G.events) rfl hidx]
    simp [G.ret_addLoc_self hact ho]
  · simp only [ht, ↓reduceIte]
    exact traceBefore_addLoc_le hG hidx hact ho t le_rfl

/-- `G` is the restriction of `G.addLoc e o` to the events of `G`. -/
theorem restrict_addLoc (hG : G.Wf) {e : TEv} {o : Option Bool} (he : e ∉ G.events) :
    (G.addLoc e o).restrict G.events = G := by
  apply Graph.ext
  · rfl
  · simp
  · funext q
    by_cases hq : q ∈ G.events
    · have hq' : q ∈ (G.addLoc e o).events ∩ G.events := by simp [hq]
      rw [(G.addLoc e o).restrict_rf_of_source_kept hq']
      · rfl
      · intro w' hw'
        exact (hG.rf_source_mem hw').2
    · rw [(G.addLoc e o).restrict_rf_of_not_mem (by simp [hq])]
      exact (hG.rf_none q (Or.inl hq)).symm
  · funext x
    rw [restrict_co, addLoc_co, List.filter_eq_self]
    intro a ha
    simpa using ((hG.co_mem x a).mp ha).1
  · funext q
    by_cases hq : q ∈ G.events
    · have hne : q ≠ e := fun h => he (h ▸ hq)
      simp [hq, Function.update_of_ne hne]
    · simp [hq, hG.pol_none hq]

theorem Wf.isPrefixOf_addLoc (hG : G.Wf) {e : TEv} {o : Option Bool}
    (hidx : e.idx = G.cnt e.tid) :
    G.IsPrefixOf (G.addLoc e o) := by
  have he : e ∉ G.events := hG.not_mem_of_idx_eq_cnt hidx
  refine ⟨G.events, ?_, (restrict_addLoc hG he).symm⟩
  intro a b h hb
  cases a with
  | init => trivial
  | th q' =>
    cases b with
    | init =>
      rcases h with h | ⟨q, hq, -, -⟩
      · exact absurd h (by simp [po])
      · cases hq
    | th q =>
      have hq : q ∈ G.events := (Finset.mem_inter.mp hb).2
      suffices hq' : q' ∈ G.events by
        simp only [mem_evSet_th, addLoc_events, Finset.mem_inter, Finset.mem_insert]
        exact ⟨Or.inr hq', hq'⟩
      rcases h with h | ⟨q₀, hq₀, -, hrf⟩
      · rcases Finset.mem_insert.mp h.1 with rfl | h1
        · have := hG.idx_lt_cnt hq
          have h3 := h.2.2.1
          have h4 := h.2.2.2
          rw [← h3] at this
          omega
        · exact h1
      · cases hq₀
        exact (hG.rf_source_mem hrf).2

/-! ### Literals -/

theorem lit_eq_some_iff (G : Graph) (e : TEv) (φ : SExpr) (b : Bool) :
    G.lit e = some (φ, b) ↔ e.act = .cons φ ∧ G.pol e = some b := by
  unfold lit
  cases e.act <;> cases G.pol e <;> simp

/-- An event without an outcome has no literal. -/
theorem lit_of_pol_none (G : Graph) {e : TEv} (h : G.pol e = none) : G.lit e = none := by
  unfold lit
  rw [h]
  cases e.act <;> rfl

/-- An event that is not a constraint evaluation has no literal. -/
theorem lit_of_not_isCons (G : Graph) {e : TEv} (h : ¬ e.IsCons) : G.lit e = none := by
  unfold lit
  cases hact : e.act <;> first | rfl | skip
  exact absurd (show e.IsCons by simp [TEv.IsCons, hact, Act.IsCons]) h

/-- The literals depend on the events and their outcomes only. -/
theorem lit_congr {G G' : Graph} {e : TEv} (h : G'.pol e = G.pol e) : G'.lit e = G.lit e := by
  unfold lit
  rw [h]

theorem F_congr {G G' : Graph} (he : G'.events = G.events)
    (hp : ∀ e ∈ G.events, G'.pol e = G.pol e) :
    G'.F = G.F := by
  ext l
  rw [mem_F, mem_F, he]
  exact ⟨fun ⟨e, h1, h2⟩ => ⟨e, h1, by rw [← lit_congr (hp e h1)]; exact h2⟩,
    fun ⟨e, h1, h2⟩ => ⟨e, h1, by rw [lit_congr (hp e h1)]; exact h2⟩⟩

/-- Adding an event without a literal keeps the literals. -/
theorem F_insert_of_lit_none {G G' : Graph} {e : TEv} (he : G'.events = insert e G.events)
    (hp : ∀ q ∈ G.events, G'.pol q = G.pol q) (hl : G'.lit e = none) : G'.F = G.F := by
  ext l
  rw [mem_F, mem_F, he]
  constructor
  · rintro ⟨q, h1, h2⟩
    rcases Finset.mem_insert.mp h1 with rfl | h1
    · rw [hl] at h2
      cases h2
    · exact ⟨q, h1, by rw [← lit_congr (hp q h1)]; exact h2⟩
  · rintro ⟨q, h1, h2⟩
    exact ⟨q, Finset.mem_insert_of_mem h1, by rw [lit_congr (hp q h1)]; exact h2⟩

@[simp] theorem F_setRF (G : Graph) (r : TEv) (w : Ev) : (G.setRF r w).F = G.F :=
  F_congr rfl (fun _ _ => rfl)

theorem F_addRead (hG : G.Wf) {e : TEv} (w : Ev) (he : e ∉ G.events) :
    (G.addRead e w).F = G.F :=
  F_insert_of_lit_none rfl (fun _ _ => rfl) (lit_of_pol_none _ (hG.pol_none he))

theorem F_addWrite (hG : G.Wf) {e : TEv} (wp : Ev) (he : e ∉ G.events) :
    (G.addWrite e wp).F = G.F :=
  F_insert_of_lit_none rfl (fun _ _ => rfl) (lit_of_pol_none _ (hG.pol_none he))

/-- A new event without an outcome adds no literal. -/
theorem F_addLoc_none {e : TEv} (he : e ∉ G.events) : (G.addLoc e none).F = G.F :=
  F_insert_of_lit_none rfl
    (fun q hq => by
      have hne : q ≠ e := fun h => he (h ▸ hq)
      simp [Function.update_of_ne hne])
    (lit_of_pol_none _ (by simp))

/-- A new constraint evaluation adds its literal. -/
theorem F_addLoc_cons {e : TEv} {φ : SExpr} (b : Bool) (he : e ∉ G.events)
    (hact : e.act = .cons φ) : (G.addLoc e (some b)).F = insert (φ, b) G.F := by
  ext l
  rw [Finset.mem_insert, mem_F, mem_F]
  have hp : ∀ q ∈ G.events, (G.addLoc e (some b)).pol q = G.pol q := by
    intro q hq
    have hne : q ≠ e := fun h => he (h ▸ hq)
    simp [Function.update_of_ne hne]
  have hle : (G.addLoc e (some b)).lit e = some (φ, b) :=
    (lit_eq_some_iff _ _ _ _).mpr ⟨hact, by simp⟩
  constructor
  · rintro ⟨q, h1, h2⟩
    rcases Finset.mem_insert.mp h1 with rfl | h1
    · rw [hle] at h2
      exact Or.inl (Option.some.inj h2).symm
    · exact Or.inr ⟨q, h1, by rw [← lit_congr (hp q h1)]; exact h2⟩
  · rintro (rfl | ⟨q, h1, h2⟩)
    · exact ⟨e, Finset.mem_insert_self _ _, hle⟩
    · exact ⟨q, Finset.mem_insert_of_mem h1, by rw [lit_congr (hp q h1)]; exact h2⟩

/-- A kept event keeps its literal. -/
theorem lit_restrict {s : Finset TEv} {q : TEv} (hq : q ∈ G.events ∩ s) :
    (G.restrict s).lit q = G.lit q :=
  lit_congr (by simp only [restrict_pol, hq, ↓reduceIte])

/-- A restriction has fewer literals. -/
theorem F_restrict_subset (s : Finset TEv) : (G.restrict s).F ⊆ G.F := by
  intro l hl
  obtain ⟨q, hq, h⟩ := (mem_F _).mp hl
  exact (mem_F _).mpr ⟨q, (Finset.mem_inter.mp hq).1, by rw [← G.lit_restrict hq]; exact h⟩

/-- A prefix keeps the outcome of its events. -/
theorem pol_of_isPrefixOf {G' : Graph} (h : G'.IsPrefixOf G) {q : TEv} (hq : q ∈ G'.events) :
    G'.pol q = G.pol q := by
  obtain ⟨s, -, rfl⟩ := h
  simp only [restrict_pol]
  rw [restrict_events] at hq
  simp only [hq, ↓reduceIte]

/-- A prefix has fewer literals. -/
theorem F_subset_of_isPrefixOf {G' : Graph} (h : G'.IsPrefixOf G) : G'.F ⊆ G.F := by
  obtain ⟨s, -, rfl⟩ := h
  exact G.F_restrict_subset s

/-! ### The last write of a location -/

theorem maxWrite_isWriteTo (hG : G.Wf) (x : Loc) : G.IsWriteTo x (G.maxWrite x) := by
  unfold maxWrite
  cases h : (G.co x).getLast? with
  | none => trivial
  | some p => exact (hG.co_mem x p).mp (List.mem_of_getLast? h)

/-- Nothing is coherence-after the last write of a location, among the writes
to that location. -/
theorem maxWrite_co_maximal (hG : G.Wf) (x : Loc) {w : Ev} (hw : G.IsWriteTo x w) :
    ¬ G.coRel (G.maxWrite x) w := by
  unfold maxWrite
  cases h : (G.co x).getLast? with
  | none =>
    have h0 : G.co x = [] := List.getLast?_eq_none_iff.mp h
    cases w with
    | init => simp [coRel]
    | th e =>
      have : e ∈ G.co x := (hG.co_mem x e).mpr hw
      rw [h0] at this
      cases this
  | some p =>
    cases w with
    | init => simp [coRel]
    | th e =>
      rintro ⟨y, hbef⟩
      have hp : p ∈ G.co x := List.mem_of_getLast? h
      obtain ⟨-, v, hv⟩ := (hG.co_mem x p).mp hp
      obtain ⟨-, v', hv'⟩ := (hG.co_mem y p).mp hbef.1
      rw [hv] at hv'
      have hxy : x = y := (Act.write.inj hv').1
      subst hxy
      have hne : G.co x ≠ [] := fun h0 => by rw [h0] at hp; cases hp
      have hlast : (G.co x).getLast hne = p := by
        have := List.getLast?_eq_some_getLast hne
        rw [h] at this
        exact (Option.some.inj this).symm
      exact List.not_before_getLast (hG.co_nodup x) hne e (hlast ▸ hbef)

/-- Adding a write after the last write of its location puts it at the end of
the coherence list. -/
theorem addWrite_maxWrite_co (hG : G.Wf) (e : TEv) :
    (G.addWrite e (G.maxWrite e.loc)).co e.loc = G.co e.loc ++ [e] := by
  rw [G.addWrite_co_self e (G.maxWrite e.loc)]
  unfold maxWrite
  cases h : (G.co e.loc).getLast? with
  | none =>
    have h0 : G.co e.loc = [] := List.getLast?_eq_none_iff.mp h
    simp [h0]
  | some p =>
    have hp : p ∈ G.co e.loc := List.mem_of_getLast? h
    have hne : G.co e.loc ≠ [] := fun h0 => by rw [h0] at hp; cases hp
    have hlast : (G.co e.loc).getLast hne = p := by
      have := List.getLast?_eq_some_getLast hne
      rw [h] at this
      exact (Option.some.inj this).symm
    simp only
    rw [← hlast]
    exact List.insertAfter_getLast (hG.co_nodup e.loc) hne e

theorem maxWrite_addWrite_maxWrite (hG : G.Wf) (e : TEv) :
    (G.addWrite e (G.maxWrite e.loc)).maxWrite e.loc = .th e := by
  have h := addWrite_maxWrite_co hG e
  unfold maxWrite at h ⊢
  rw [h]
  simp

end Graph

/-! ### Examples

Two locations with different initial values; a read from `init` while another
location has a write. -/

section Examples

open Graph

private def μ₀ : Loc → Val := fun x => if x = 0 then 3 else 5
private def w₀ : TEv := ⟨0, 0, .write 1 7⟩
private def r₀ : TEv := ⟨1, 0, .read 0⟩
private def G₀ : Graph := ((Graph.init μ₀).addWrite w₀ .init).addRead r₀ .init

-- the read of location `0` from `init` returns the initial value of location `0`
example : G₀.ret r₀ = some 3 := by decide
-- a write returns no value
example : G₀.ret w₀ = none := by decide
example : G₀.cnt 0 = 1 ∧ G₀.cnt 1 = 1 ∧ G₀.cnt 2 = 0 := by decide
example : G₀.co 1 = [w₀] ∧ G₀.co 0 = [] := by decide
example : G₀.maxWrite 1 = .th w₀ ∧ G₀.maxWrite 0 = .init := by decide
-- the read of location `0` is not from-read-before the write to location `1`
example : ¬ G₀.frRel (.th r₀) (.th w₀) := by
  rintro ⟨e, e', x, he, he', -, hact, hco, -⟩
  cases he; cases he'
  have hx : x = 0 := by simpa [r₀] using hact.symm
  subst hx
  exact absurd hco (by decide)
-- restriction to the write only: the read is removed
example : (G₀.restrict {w₀}).events = {w₀} := by decide
-- changing the source of the read (here to a write of another value at its location)
example : ((G₀.addWrite ⟨0, 1, .write 0 9⟩ .init).setRF r₀ (.th ⟨0, 1, .write 0 9⟩)).ret r₀
    = some 9 := by decide

end Examples

end Condpor
