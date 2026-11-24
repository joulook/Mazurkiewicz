import Mazurkiewicz.Must.Event
import Mazurkiewicz.Lib.Rel
import Mazurkiewicz.Lib.Finset

/-!
# Execution graphs of Must (Definitions 3.2 and 3.3)

Paper: Section 3.1, Definitions 3.2, 3.3. Plan: `plan/must/lean/LEAN-PLAN.md`, decisions Q1, Q2,
Q3, Q6.

Representation. A graph is a triple `⟨events, rf, nd⟩`:

* `events : Finset (Ev Q)`;
* `rf r = some (.snd s)`: the receive `r` reads from the send `s`; `rf r = some .bot`: `r` reads
  `⊥`; `rf e = none`: `e` is not a receive of the graph;
* `nd e = some v`: the ND event `e` has outcome `v`; `nd e = none`: `e` is not an ND event of the
  graph.

A graph has no insertion order. Well-formedness fixes `rf` and `nd` outside the events of the
graph (`none`), so two well-formed graphs are equal iff they have the same events and agree on
`rf` and `nd` on these events (`Wf.ext`): equality of graphs "as unordered graphs" is ordinary
equality.

Well-formedness (`Wf`) is Definition 3.3 with the repairs Q1–Q3, Q6:

* (Q1) unique `(tid, idx)`, indices of a thread contiguous from `0`; `po` is derived:
  `po a b := a, b ∈ G ∧ tid a = tid b ∧ idx a < idx b`;
* (Q2) `rf` is total on the receives of the graph; a source is `⊥` or a send of the graph; `⊥`
  only for a non-blocking receive; `porf = (po ∪ rf)⁺` with real-send `rf` edges only;
* (Q3) read once: `rf r = rf r' = some (.snd s) → r = r'`; `⊥` is not constrained;
* matching destination, value in the predicate, same model (`Ev.Matches`);
* (Q6) `nd` total on the ND events of the graph, outcome in the set of the label;
* `porf` irreflexive.

"Receives read a single value" (`rf` functional) holds by construction.
-/

namespace Must

open Relation

/-- A source of a receive: `⊥`, or a send. -/
inductive Src (Q : Type)
  | bot
  | snd (s : Ev Q)
  deriving DecidableEq

/-- An execution graph. -/
@[ext]
structure Graph (Q : Type) where
  /-- the events -/
  events : Finset (Ev Q)
  /-- the source of each receive -/
  rf : Ev Q → Option (Src Q)
  /-- the outcome of each ND event -/
  nd : Ev Q → Option Val

namespace Graph

variable {Q : Type} (G : Graph Q)

/-! ### Relations -/

/-- Program order (Q1). -/
def po (a b : Ev Q) : Prop :=
  a ∈ G.events ∧ b ∈ G.events ∧ a.tid = b.tid ∧ a.idx < b.idx

/-- Reads-from with a real send, from the send to the receive. -/
def rfRel (s r : Ev Q) : Prop := r ∈ G.events ∧ G.rf r = some (.snd s)

/-- One step of causality: `po` or a real-send `rf` edge. -/
def porfStep (a b : Ev Q) : Prop := G.po a b ∨ G.rfRel a b

instance [DecidableEq Q] (a b : Ev Q) : Decidable (G.po a b) := by
  unfold po
  infer_instance

instance [DecidableEq Q] (s r : Ev Q) : Decidable (G.rfRel s r) := by
  unfold rfRel
  infer_instance

instance [DecidableEq Q] (a b : Ev Q) : Decidable (G.porfStep a b) := by
  unfold porfStep
  infer_instance

/-- Causality `porf = (po ∪ rf)⁺`. -/
def porf : Ev Q → Ev Q → Prop := TransGen G.porfStep

/-- `E` is causally prefix-closed in `G`: every causal predecessor of an event of `G` in `E` is
in `E` (Section 3.2.1: `dom(G.porf; [E]) ⊆ E`, here for `G.events ∩ E`). -/
def Closed [DecidableEq Q] (E : Finset (Ev Q)) : Prop :=
  Maz.PrefixClosed G.porfStep (↑(G.events ∩ E) : Set (Ev Q))

variable {G} in
theorem porf_trans {a b c : Ev Q} (h1 : G.porf a b) (h2 : G.porf b c) : G.porf a c :=
  TransGen.trans h1 h2

/-- `porf`-closedness of a set is closedness under the steps or under `porf`. -/
theorem closed_iff_porf [DecidableEq Q] (E : Finset (Ev Q)) :
    G.Closed E ↔ ∀ ⦃a b⦄, G.porf a b → b ∈ G.events ∩ E → a ∈ G.events ∩ E :=
  ⟨fun h => h.transGen, fun h _ _ hab hb => h (TransGen.single hab) hb⟩

/-! ### Sets of events -/

/-- The number of events of thread `t`. -/
def cnt (t : Tid) : ℕ := (G.events.filter (fun e => e.tid = t)).card

/-- The receives of the graph, `G.R`. -/
def R : Finset (Ev Q) := G.events.filter Ev.IsRecv

/-- The sends of the graph, `G.S`. -/
def S : Finset (Ev Q) := G.events.filter Ev.IsSend

/-- The ND events of the graph, `G.ND`. -/
def ND : Finset (Ev Q) := G.events.filter Ev.IsND

/-- The unread sends of the graph, `G.US`: sends read by no receive of the graph. -/
def US [DecidableEq Q] : Finset (Ev Q) :=
  G.events.filter (fun s => s.IsSend ∧ ∀ r ∈ G.events, G.rf r ≠ some (.snd s))

/-- Matching values, `G.mval = {⟨s, r⟩ ∈ G.S × G.R | val s ∈ vals r}`. -/
def mval [Membership Val Q] (s r : Ev Q) : Prop :=
  s ∈ G.events ∧ r ∈ G.events ∧ s.ValMatches r

@[simp] theorem mem_R {e : Ev Q} : e ∈ G.R ↔ e ∈ G.events ∧ e.IsRecv := Finset.mem_filter
@[simp] theorem mem_S {e : Ev Q} : e ∈ G.S ↔ e ∈ G.events ∧ e.IsSend := Finset.mem_filter
@[simp] theorem mem_ND {e : Ev Q} : e ∈ G.ND ↔ e ∈ G.events ∧ e.IsND := Finset.mem_filter

theorem mem_US [DecidableEq Q] {s : Ev Q} :
    s ∈ G.US ↔ s ∈ G.events ∧ s.IsSend ∧ ∀ r ∈ G.events, G.rf r ≠ some (.snd s) := by
  simp [US]

theorem US_subset_S [DecidableEq Q] : G.US ⊆ G.S := by
  intro s hs
  have := (G.mem_US).mp hs
  exact (G.mem_S).mpr ⟨this.1, this.2.1⟩

/-! ### Well-formedness -/

variable [Membership Val Q]

/-- Well-formedness (Definition 3.3, repaired by Q1–Q3, Q6). -/
structure Wf : Prop where
  /-- an event is determined by its thread and index -/
  idx_inj : ∀ e ∈ G.events, ∀ e' ∈ G.events, e.tid = e'.tid → e.idx = e'.idx → e = e'
  /-- the indices of a thread are contiguous from `0` -/
  idx_contig : ∀ e ∈ G.events, ∀ i < e.idx, ∃ e' ∈ G.events, e'.tid = e.tid ∧ e'.idx = i
  /-- `rf` is defined exactly on the receives of the graph -/
  rf_isSome : ∀ e, (G.rf e).isSome ↔ e ∈ G.events ∧ e.IsRecv
  /-- only non-blocking receives read `⊥` -/
  rf_bot : ∀ r, G.rf r = some .bot → r.IsRecvNB
  /-- a source is an event of the graph -/
  rf_mem : ∀ r s, G.rf r = some (.snd s) → s ∈ G.events
  /-- a send is read at most once -/
  rf_once : ∀ r r' s, G.rf r = some (.snd s) → G.rf r' = some (.snd s) → r = r'
  /-- a source matches its receive: destination, value, model -/
  rf_match : ∀ r s, G.rf r = some (.snd s) → s.Matches r
  /-- `nd` is defined exactly on the ND events of the graph -/
  nd_isSome : ∀ e, (G.nd e).isSome ↔ e ∈ G.events ∧ e.IsND
  /-- an outcome is in the set of its label -/
  nd_mem : ∀ e v, G.nd e = some v → v ∈ e.ndSet
  /-- no causal cycle -/
  porf_irrefl : ∀ a, ¬ G.porf a a

/-- The empty graph. -/
def empty : Graph Q where
  events := ∅
  rf := fun _ => none
  nd := fun _ => none

theorem empty_wf : (empty : Graph Q).Wf where
  idx_inj := by simp [empty]
  idx_contig := by simp [empty]
  rf_isSome := by simp [empty]
  rf_bot := by simp [empty]
  rf_mem := by simp [empty]
  rf_once := by simp [empty]
  rf_match := by simp [empty]
  nd_isSome := by simp [empty]
  nd_mem := by simp [empty]
  porf_irrefl := by
    intro a h
    obtain ⟨c, hc⟩ := Maz.exists_first_of_transGen h
    rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [empty] at h1

/-! ### Basic facts -/

variable {G}

theorem Wf.acyclic (hG : G.Wf) : Maz.Acyclic G.porfStep := hG.porf_irrefl

theorem Wf.rf_none (hG : G.Wf) {e : Ev Q} (he : e ∉ G.events ∨ ¬ e.IsRecv) : G.rf e = none := by
  have : ¬ (G.rf e).isSome := fun h => by
    have := (hG.rf_isSome e).mp h
    tauto
  simpa using this

theorem Wf.nd_none (hG : G.Wf) {e : Ev Q} (he : e ∉ G.events ∨ ¬ e.IsND) : G.nd e = none := by
  have : ¬ (G.nd e).isSome := fun h => by
    have := (hG.nd_isSome e).mp h
    tauto
  simpa using this

/-- A receive of the graph has a source. -/
theorem Wf.exists_rf (hG : G.Wf) {r : Ev Q} (hr : r ∈ G.events) (hR : r.IsRecv) :
    ∃ x, G.rf r = some x :=
  Option.isSome_iff_exists.mp ((hG.rf_isSome r).mpr ⟨hr, hR⟩)

/-- An ND event of the graph has an outcome. -/
theorem Wf.exists_nd (hG : G.Wf) {e : Ev Q} (he : e ∈ G.events) (hN : e.IsND) :
    ∃ v, G.nd e = some v :=
  Option.isSome_iff_exists.mp ((hG.nd_isSome e).mpr ⟨he, hN⟩)

/-- An event with a source is a receive of the graph. -/
theorem Wf.rf_some (hG : G.Wf) {r : Ev Q} {x : Src Q} (h : G.rf r = some x) :
    r ∈ G.events ∧ r.IsRecv :=
  (hG.rf_isSome r).mp (by simp [h])

/-- The set of an ND event of the graph is not empty. -/
theorem Wf.nd_nonempty (hG : G.Wf) {e : Ev Q} (he : e ∈ G.events) (hN : e.IsND) :
    e.ndSet.Nonempty := by
  obtain ⟨v, hv⟩ := hG.exists_nd he hN
  exact ⟨v, hG.nd_mem e v hv⟩

/-- The source of a receive is a send of the graph. -/
theorem Wf.rf_mem_S (hG : G.Wf) {r s : Ev Q} (h : G.rf r = some (.snd s)) : s ∈ G.S :=
  (G.mem_S).mpr ⟨hG.rf_mem r s h, (hG.rf_match r s h).isSend⟩

/-- In a well-formed graph an event is determined by `(tid, idx)`. -/
theorem Wf.eq_of_tid_idx (hG : G.Wf) {e e' : Ev Q} (he : e ∈ G.events) (he' : e' ∈ G.events)
    (ht : e.tid = e'.tid) (hi : e.idx = e'.idx) : e = e' :=
  hG.idx_inj e he e' he' ht hi

/-- Two well-formed graphs with the same events that agree on `rf` and `nd` on these events are
equal. -/
theorem Wf.ext {G' : Graph Q} (hG : G.Wf) (hG' : G'.Wf) (hev : G.events = G'.events)
    (hrf : ∀ e ∈ G.events, G.rf e = G'.rf e) (hnd : ∀ e ∈ G.events, G.nd e = G'.nd e) :
    G = G' := by
  apply Graph.ext hev
  · funext e
    by_cases he : e ∈ G.events
    · exact hrf e he
    · rw [hG.rf_none (Or.inl he), hG'.rf_none (Or.inl (hev ▸ he))]
  · funext e
    by_cases he : e ∈ G.events
    · exact hnd e he
    · rw [hG.nd_none (Or.inl he), hG'.nd_none (Or.inl (hev ▸ he))]

theorem Wf.mem_of_porfStep (hG : G.Wf) {a b : Ev Q} (h : G.porfStep a b) :
    a ∈ G.events ∧ b ∈ G.events := by
  rcases h with ⟨ha, hb, -⟩ | ⟨hb, hrf⟩
  · exact ⟨ha, hb⟩
  · exact ⟨hG.rf_mem b a hrf, hb⟩

theorem Wf.mem_of_porf (hG : G.Wf) {a b : Ev Q} (h : G.porf a b) :
    a ∈ G.events ∧ b ∈ G.events := by
  induction h with
  | single h => exact hG.mem_of_porfStep h
  | tail _ h ih => exact ⟨ih.1, (hG.mem_of_porfStep h).2⟩

/-! ### Counting -/

/-- Thread `t` has exactly the indices below `cnt t`. -/
theorem Wf.exists_idx_iff (hG : G.Wf) (t : Tid) (i : ℕ) :
    (∃ e ∈ G.events, e.tid = t ∧ e.idx = i) ↔ i < G.cnt t := by
  set F := G.events.filter (fun e => e.tid = t) with hF
  have hinj : Set.InjOn Ev.idx (F : Set (Ev Q)) := by
    intro e he e' he'
    have he := Finset.mem_filter.mp (Finset.mem_coe.mp he)
    have he' := Finset.mem_filter.mp (Finset.mem_coe.mp he')
    exact fun h => hG.idx_inj e he.1 e' he'.1 (he.2.trans he'.2.symm) h
  have hcard : (F.image Ev.idx).card = G.cnt t := Finset.card_image_of_injOn hinj
  have hdown : ∀ i ∈ F.image Ev.idx, ∀ j < i, j ∈ F.image Ev.idx := by
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

theorem Wf.idx_lt_cnt (hG : G.Wf) {e : Ev Q} (he : e ∈ G.events) : e.idx < G.cnt e.tid :=
  (hG.exists_idx_iff e.tid e.idx).mp ⟨e, he, rfl, rfl⟩

/-- The next event of a thread is not in the graph. -/
theorem Wf.not_mem_of_idx_eq_cnt (hG : G.Wf) {e : Ev Q} (hidx : e.idx = G.cnt e.tid) :
    e ∉ G.events := by
  intro he
  have := hG.idx_lt_cnt he
  omega

end Graph

end Must
