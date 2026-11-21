import Mazurkiewicz.Condpor.Event
import Mazurkiewicz.Lib.Rel
import Mazurkiewicz.Lib.ListOrder
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Option

/-!
# Execution graphs with symbolic events

`Trust/Graph.lean` with one more component: the outcome `pol` of the
constraint evaluations (the paper's `SetSYM`, as `rf` is its `SetRF`). A graph
has no insertion order; a configuration (`Config`) is a graph with an
insertion order.

Representation:

* `events` holds the thread events; the initialization event is implicit;
* `mem` is the initial memory, the value that `init` writes to each location;
* `rf e = some w` for a read `e` with source `w`;
* `co x` lists the thread writes to `x` in coherence order; `init` is before
  all of them;
* `pol e = some b` for a constraint evaluation `e` of the graph: `b = true` if
  the formula of `e` is assumed, `false` if its negation is.

`G.F` is the set of literals `(φ, b)` of the constraint evaluations of `G`: the
paper's `G.F` is their conjunction.

Well-formedness differs from `Trust.Graph.Wf` in two points: `rf` is `none` on
every event that is not a read (not only on writes), and `pol` is defined
exactly on the constraint evaluations of the graph.
-/

namespace Condpor

/-- A literal: a formula with an outcome. -/
abbrev Lit := SExpr × Bool

open Relation

/-- An execution graph. -/
@[ext]
structure Graph where
  /-- the initial memory -/
  mem : Loc → Val
  /-- the thread events -/
  events : Finset TEv
  /-- the source of each read -/
  rf : TEv → Option Ev
  /-- the thread writes to each location, in coherence order -/
  co : Loc → List TEv
  /-- the outcome of each constraint evaluation -/
  pol : TEv → Option Bool

namespace Graph

variable (G : Graph)

/-- `w` is a write to `x` in `G`: the initialization event, or a thread write
to `x`. -/
def IsWriteTo (x : Loc) : Ev → Prop
  | .init => True
  | .th e => e ∈ G.events ∧ ∃ v, e.act = .write x v

/-- The value that the write `w` gives to location `x`. -/
def valAt (x : Loc) : Ev → Val
  | .init => G.mem x
  | .th e => match e.act with
    | .write _ v => v
    | _ => 0

/-- The value returned by a thread event: the value read, for a read with a
source; `1` or `0` for a constraint evaluation with outcome true or false;
`none` otherwise. -/
def ret (e : TEv) : Option Val :=
  match e.act with
  | .read x => (G.rf e).map (G.valAt x)
  | .cons _ => (G.pol e).map (fun b => if b then 1 else 0)
  | _ => none

/-- The literal of a thread event: `(φ, b)` for an evaluation of `φ` with
outcome `b`. -/
def lit (e : TEv) : Option Lit :=
  match e.act, G.pol e with
  | .cons φ, some b => some (φ, b)
  | _, _ => none

/-- The literals of the constraint evaluations of the graph (the paper's
`G.F`, as a set of conjuncts). It is computed from the events: two events may
carry the same literal. -/
def F : Finset Lit := G.events.biUnion (fun e => (G.lit e).toFinset)

theorem mem_F {l : Lit} : l ∈ G.F ↔ ∃ e ∈ G.events, G.lit e = some l := by
  simp [F]

/-- The number of events of thread `t`. -/
def cnt (t : Tid) : ℕ := (G.events.filter (fun e => e.tid = t)).card

/-- The last write to `x` in coherence order: the last element of `co x`, or
the initialization event. -/
def maxWrite (x : Loc) : Ev :=
  match (G.co x).getLast? with
  | some e => .th e
  | none => .init

/-- Program order: `init` is before every thread event, and the events of one
thread are ordered by index. The paper's `po` (Section 3.1) is a relation on
all events and is intersected with `G.E × G.E` only inside `porf`; `G.po` is
that intersection. The graph-free program order that Def. A.7 uses
(`po ⊆ <next`) is `Program.poT`, defined with the programs. -/
def po : Ev → Ev → Prop
  | .init, .th e => e ∈ G.events
  | .th e, .th e' => e ∈ G.events ∧ e' ∈ G.events ∧ e.tid = e'.tid ∧ e.idx < e'.idx
  | _, .init => False

/-- Reads-from as a relation, from the source to the read. -/
def rfRel (w r : Ev) : Prop :=
  ∃ e, r = .th e ∧ e ∈ G.events ∧ G.rf e = some w

/-- Coherence at location `x`: `init` first, then the order of the list `co x`. -/
def coRelAt (x : Loc) : Ev → Ev → Prop
  | .init, .th e => e ∈ G.co x
  | .th e, .th e' => (G.co x).Before e e'
  | _, .init => False

/-- Coherence as one relation, the paper's `G.co ⊆ ⋃ₗ Wₗ × Wₗ` (Def. 3.2(4)).
Since `init` is a write to every location, `init` is coherence-before the
thread writes of *every* location. Notions that speak of coherence-maximality
among the writes of one location (maximal extension, `Previous`, line 27 of
Algorithm 1) must therefore use `coRelAt`, not this relation. -/
def coRel : Ev → Ev → Prop
  | .init, .th e => ∃ x, e ∈ G.co x
  | .th e, .th e' => ∃ x, (G.co x).Before e e'
  | _, .init => False

theorem coRel_iff_exists (a b : Ev) : G.coRel a b ↔ ∃ x, G.coRelAt x a b := by
  cases a <;> cases b <;> simp [coRel, coRelAt]

/-- From-read, per location (`induction-popl`, def:sc): the read `r` of `x`
reads from a write that is coherence-before the write `w` to `x`. -/
def frRel (r w : Ev) : Prop :=
  ∃ e e' x, r = .th e ∧ w = .th e' ∧ e ∈ G.events ∧ e.act = .read x ∧ e' ∈ G.co x ∧
    (G.rf e = some .init ∨ ∃ e'', G.rf e = some (.th e'') ∧ (G.co x).Before e'' e')

/-- One step of causality: program order or reads-from. -/
def porfStep (a b : Ev) : Prop := G.po a b ∨ G.rfRel a b

/-- Causality `porf = (po ∪ rf)⁺`. -/
def porf : Ev → Ev → Prop := TransGen G.porfStep

/-- Well-formedness: the conditions of the paper's Def. 3.2 that the
representation does not give by construction, and one more.

* `idx_inj` is Def. 3.2(1);
* `rf_read`, `rf_none` say that `rf` is a function from the reads of the graph
  to same-location writes of the graph, Def. 3.2(3) (in Coq this totality is
  part of consistency, `cons_complete`);
* `co_mem`, `co_nodup` say that `co x` is a strict total order on the thread
  writes to `x`, Def. 3.2(4); that `init` is coherence-first is built in (not in
  Def. 3.2(4) itself, but stated in footnote 3 of Section 3.4 of the paper:
  "All writes are co-after the initializing writes");
* `idx_contig`, contiguity of the indices of a thread, is in neither Def. 3.2
  nor Coq's `Wf`. It holds for every graph the algorithm builds, is presupposed
  by `avail` (Def. A.8) and by traces, and is part of the graphs of
  `induction-popl` (def:graph).

Acyclicity of `porf` is not part of well-formedness of a graph here: it is the
paper's well-formedness of a memory model (Def. A.15). -/
structure Wf : Prop where
  /-- a thread has at most one event per index -/
  idx_inj : ∀ e ∈ G.events, ∀ e' ∈ G.events, e.tid = e'.tid → e.idx = e'.idx → e = e'
  /-- the indices of a thread are contiguous from `0` -/
  idx_contig : ∀ e ∈ G.events, ∀ i < e.idx, ∃ e' ∈ G.events, e'.tid = e.tid ∧ e'.idx = i
  /-- every read of the graph has a source, a write of the graph to its location -/
  rf_read : ∀ e ∈ G.events, ∀ x, e.act = .read x → ∃ w, G.rf e = some w ∧ G.IsWriteTo x w
  /-- `rf` is `none` outside the reads of the graph -/
  rf_none : ∀ e, (e ∉ G.events ∨ ¬ e.IsRead) → G.rf e = none
  /-- `co x` contains exactly the thread writes to `x` -/
  co_mem : ∀ x e, e ∈ G.co x ↔ e ∈ G.events ∧ ∃ v, e.act = .write x v
  /-- `co x` has no repetition -/
  co_nodup : ∀ x, (G.co x).Nodup
  /-- `pol` is defined exactly on the constraint evaluations of the graph -/
  pol_isSome : ∀ e, (G.pol e).isSome ↔ e ∈ G.events ∧ e.IsCons

/-- Well-formedness except that the read `r` may lack a source. This is the
state of a graph in the middle of a revisit: the events after `r` have been
removed, and `r` has not yet been given its new source. -/
structure WfExcept (r : TEv) : Prop where
  /-- a thread has at most one event per index -/
  idx_inj : ∀ e ∈ G.events, ∀ e' ∈ G.events, e.tid = e'.tid → e.idx = e'.idx → e = e'
  /-- the indices of a thread are contiguous from `0` -/
  idx_contig : ∀ e ∈ G.events, ∀ i < e.idx, ∃ e' ∈ G.events, e'.tid = e.tid ∧ e'.idx = i
  /-- every read of the graph other than `r` has a source -/
  rf_read : ∀ e ∈ G.events, e ≠ r → ∀ x, e.act = .read x →
    ∃ w, G.rf e = some w ∧ G.IsWriteTo x w
  /-- `rf` is `none` outside the reads of the graph -/
  rf_none : ∀ e, (e ∉ G.events ∨ ¬ e.IsRead) → G.rf e = none
  /-- `co x` contains exactly the thread writes to `x` -/
  co_mem : ∀ x e, e ∈ G.co x ↔ e ∈ G.events ∧ ∃ v, e.act = .write x v
  /-- `co x` has no repetition -/
  co_nodup : ∀ x, (G.co x).Nodup
  /-- `pol` is defined exactly on the constraint evaluations of the graph -/
  pol_isSome : ∀ e, (G.pol e).isSome ↔ e ∈ G.events ∧ e.IsCons

variable {G} in
theorem Wf.wfExcept (hG : G.Wf) (r : TEv) : G.WfExcept r where
  idx_inj := hG.idx_inj
  idx_contig := hG.idx_contig
  rf_read := fun e he _ => hG.rf_read e he
  rf_none := hG.rf_none
  co_mem := hG.co_mem
  co_nodup := hG.co_nodup
  pol_isSome := hG.pol_isSome

/-- The initial graph for the memory `μ`: no thread event. -/
def init (μ : Loc → Val) : Graph where
  mem := μ
  events := ∅
  rf := fun _ => none
  co := fun _ => []
  pol := fun _ => none

theorem init_wf (μ : Loc → Val) : (init μ).Wf where
  idx_inj := by simp [init]
  idx_contig := by simp [init]
  rf_read := by simp [init]
  rf_none := by simp [init]
  co_mem := by simp [init]
  co_nodup := by simp [init]
  pol_isSome := by simp [init]

end Graph

/-- A configuration: a graph together with the insertion order of its events
(paper: the order `≤_G`, Def. 3.2(2) and Def. A.1). `order` lists the thread
events only, newest first; `init`, the only event of the initial graph, is
implicitly first in `≤_G`. -/
structure Config where
  /-- the initial memory -/
  mem : Loc → Val
  /-- the thread events, newest first -/
  order : List TEv
  /-- the source of each read -/
  rf : TEv → Option Ev
  /-- the thread writes to each location, in coherence order -/
  co : Loc → List TEv
  /-- the outcome of each constraint evaluation -/
  pol : TEv → Option Bool

/-- The graph of a configuration: forget the insertion order. Two
configurations are equivalent in the sense of the paper (`≈`) iff they have
the same graph. -/
def Config.abs (c : Config) : Graph where
  mem := c.mem
  events := c.order.toFinset
  rf := c.rf
  co := c.co
  pol := c.pol

/-- A configuration is well-formed if its graph is and its order list has no
repetition. In the order list, `c.order.Before b a` says that `a` was added
before `b` (the list is newest first). The insertion order need not extend
`rf`: after a revisit, a read is older than its source. -/
def Config.Wf (c : Config) : Prop := c.abs.Wf ∧ c.order.Nodup

end Condpor
