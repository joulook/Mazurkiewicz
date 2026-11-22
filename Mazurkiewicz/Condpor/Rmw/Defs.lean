import Mazurkiewicz.Condpor.GetNext

/-!
# Read-modify-write accesses: definitions

TruSt treats the two events of a read-modify-write instruction (a lock
acquire, a CAS, a fetch-and-add) as an *exclusive* read followed by an
*exclusive* write, and asks of the memory model that no write to the location
comes between the source of the read and the write (atomicity). Its appendix
uses `R^ex`, `W^ex`, `RMW` and `R^ex_pending` without defining them. This file
fixes the definitions.

The labels of `Event.lean` have no kind. The kind of an access is given with
the program, as a function of the position of the access in its thread
(`XProgram.ex`: "the action of thread `t` after the trace `u` is exclusive").
For an execution of the program this is the kind of the instruction that
produced the event. So the graphs, the operations and the steps of the
development are used as they are; the algorithm with RMW is the relation
`StepL` of `Alg.lean` for the model `Model.atomic P M`.

* `P.IsEx G e`: the event `e` of `G` is exclusive.
* `P.RMW G r w`: a completed pair of `G`.
* `P.Mate G r w`: a prospective pair: `r` is an exclusive read, the last event
  of its thread in `G`, and `w`, the available event of that thread, is an
  exclusive write. `P.Pending G r`: `r` has a mate (`r ∈ G.R^ex_pending`).
* An exclusive read whose thread continues with something else (a failed
  CAS) is in no pair and has no mate.
* `Atomic P G`: the write of every completed pair is the immediate coherence
  successor of the source of its read. Pending reads are not constrained.
-/

namespace Condpor

open Program

/-- A program with exclusive accesses. -/
structure XProgram extends Program where
  /-- the action of thread `t` after the trace `u` is exclusive -/
  ex : Tid → List (Option Val) → Bool
  /-- only reads and writes are exclusive -/
  ex_rw : ∀ t u, ex t u = true → ∃ a, step t u = some a ∧ (a.IsRead ∨ a.IsWrite)
  /-- an exclusive write comes directly after an exclusive read of the same
  location by the same thread -/
  ex_write : ∀ t u x v, ex t u = true → step t u = some (.write x v) →
    ∃ u₀ a, u = u₀ ++ [some a] ∧ ex t u₀ = true ∧ step t u₀ = some (.read x)

namespace XProgram

variable (P : XProgram)

/-- The event `e` of `G` is exclusive. -/
def IsEx (G : Graph) (e : TEv) : Prop := P.ex e.tid (G.traceBefore e.tid e.idx) = true

/-- A completed pair of `G`: an exclusive read and the exclusive write that
follows it in its thread. The locations are not compared: in an execution of
`P` they are equal (`XProgram.RMW.read_act`, by `ex_write`). -/
def RMW (G : Graph) (r w : TEv) : Prop :=
  r ∈ G.events ∧ w ∈ G.events ∧ w.tid = r.tid ∧ w.idx = r.idx + 1 ∧ r.IsRead ∧ w.IsWrite ∧
    P.IsEx G r ∧ P.IsEx G w

/-- A prospective pair: `r` is an exclusive read of `G`, the last event of its
thread, and the available event `w` of that thread is an exclusive write. -/
def Mate (G : Graph) (r w : TEv) : Prop :=
  r ∈ G.events ∧ r.IsRead ∧ P.IsEx G r ∧ w ∈ P.avail G ∧ w.tid = r.tid ∧ w.idx = r.idx + 1 ∧
    w.IsWrite ∧ P.ex w.tid (G.trace w.tid) = true

/-- `r` is a pending exclusive read of `G`. -/
def Pending (G : Graph) (r : TEv) : Prop := ∃ w, P.Mate G r w

end XProgram

/-- `w` is the immediate successor of the write `s` in the coherence order of
location `x`. -/
def Graph.ImmCo (G : Graph) (x : Loc) : Ev → TEv → Prop
  | .init, w => ∃ l, G.co x = w :: l
  | .th p, w => ∃ l₁ l₂, G.co x = l₁ ++ p :: w :: l₂

/-- Atomicity: the write of every completed pair is the immediate coherence
successor of the source of its read. -/
def XProgram.Atomic (P : XProgram) (G : Graph) : Prop :=
  ∀ r w, P.RMW G r w → ∀ s, G.rf r = some s → G.ImmCo w.loc s w

namespace Graph

theorem ImmCo.restrict {G : Graph} {x : Loc} {s : Ev} {w : TEv} {S : Finset TEv}
    (h : G.ImmCo x s w) (hw : w ∈ S) (hs : s ∈ evSet S) : (G.restrict S).ImmCo x s w := by
  cases s with
  | init =>
    obtain ⟨l, hl⟩ := h
    refine ⟨l.filter (fun e => e ∈ S), ?_⟩
    rw [restrict_co, hl, List.filter_cons_of_pos (by simpa using hw)]
  | th p =>
    obtain ⟨l₁, l₂, hl⟩ := h
    have hp : p ∈ S := hs
    refine ⟨l₁.filter (fun e => e ∈ S), l₂.filter (fun e => e ∈ S), ?_⟩
    rw [restrict_co, hl, List.filter_append, List.filter_cons_of_pos (by simpa using hp),
      List.filter_cons_of_pos (by simpa using hw)]

end Graph

/-- The kind of a kept event of a prefix is its kind in the graph. -/
theorem XProgram.isEx_restrict (P : XProgram) {G : Graph} (hG : G.Wf) {S : Finset TEv}
    (hS : Maz.PrefixClosed G.porfStep (Graph.evSet (G.events ∩ S))) {e : TEv}
    (he : e ∈ G.events ∩ S) : P.IsEx (G.restrict S) e ↔ P.IsEx G e := by
  unfold XProgram.IsEx
  rw [Graph.traceBefore_restrict hG hS he]

/-- A completed pair of a prefix is a completed pair of the graph. -/
theorem XProgram.RMW.of_restrict (P : XProgram) {G : Graph} (hG : G.Wf) {S : Finset TEv}
    (hS : Maz.PrefixClosed G.porfStep (Graph.evSet (G.events ∩ S))) {r w : TEv}
    (h : P.RMW (G.restrict S) r w) : P.RMW G r w := by
  obtain ⟨hr, hw, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨(Finset.mem_inter.mp hr).1, (Finset.mem_inter.mp hw).1, h1, h2, h3, h4,
    (P.isEx_restrict hG hS hr).mp h5, (P.isEx_restrict hG hS hw).mp h6⟩

/-- A prefix of an atomic graph is atomic. -/
theorem XProgram.Atomic.restrict (P : XProgram) {G : Graph} (hG : G.Wf) (h : P.Atomic G)
    {S : Finset TEv} (hS : Maz.PrefixClosed G.porfStep (Graph.evSet (G.events ∩ S))) :
    P.Atomic (G.restrict S) := by
  intro r w hrw s hs
  have hrwG := XProgram.RMW.of_restrict P hG hS hrw
  obtain ⟨hsG, -, hsS⟩ := G.restrict_rf_eq_some hs
  have hw : w ∈ S := (Finset.mem_inter.mp hrw.2.1).2
  exact (h r w hrwG s hsG).restrict hw hsS

/-- The model `M` with atomicity for the program `P`. -/
def Model.atomic (P : XProgram) (M : Model) : Model where
  cons := fun G => M.cons G ∧ P.Atomic G
  cons_init := fun μ => ⟨M.cons_init μ, fun r w h => absurd h.1 (by simp [Graph.init])⟩
  porf_acyclic := fun G hG hc => M.porf_acyclic G hG hc.1
  prefix_closed := by
    rintro G G' hG ⟨hc, hat⟩ ⟨S, hS, rfl⟩
    exact ⟨M.prefix_closed G _ hG hc ⟨S, hS, rfl⟩, XProgram.Atomic.restrict P hG hat hS⟩

theorem Model.atomic_cons_iff {P : XProgram} {M : Model} {G : Graph} :
    (Model.atomic P M).cons G ↔ M.cons G ∧ P.Atomic G := Iff.rfl

end Condpor

/-! ### What the accepted development gives for the algorithm with RMW

The algorithm with RMW is `StepL` for the model `(Model.atomic P M).sym S`.
The statements of the accepted development that hold for every model are
repeated here for it. -/

namespace Condpor

variable {P : XProgram} {M : Model} {S : Solver} {τ : TieBreak S}

/-- X-1 (soundness): a reached configuration is well-formed, its graph is an
execution of the program, `M`-consistent with satisfiable constraints, and
atomic. -/
theorem Rmw.sound {c : Config}
    (h : Reach P.toProgram ((Model.atomic P M).sym S) τ c) :
    c.Wf ∧ c.PoLt ∧ P.toProgram.Exec c.abs ∧ M.cons c.abs ∧ P.Atomic c.abs ∧ S.sat c.abs.F := by
  obtain ⟨hw, hpo, hc, hE⟩ := h.sound
  obtain ⟨⟨hm, hat⟩, hs⟩ := Model.sym_cons_iff.mp hc
  exact ⟨hw, hpo, hE, hm, hat, hs⟩

/-- X-5 (Theorem 5(a)): two runs from the initial configuration that end in
the same graph are the same run, and a reached configuration is determined by
its graph. -/
theorem Rmw.path_unique {p1 p2 : List Config} {c1 c2 : Config}
    (h1 : Maz.Path (Step P.toProgram ((Model.atomic P M).sym S) τ)
      (Config.init P.toProgram.mem) p1 c1)
    (h2 : Maz.Path (Step P.toProgram ((Model.atomic P M).sym S) τ)
      (Config.init P.toProgram.mem) p2 c2) (h : c1.abs = c2.abs) : p1 = p2 :=
  Condpor.path_unique h1 h2 h

theorem Rmw.eq_of_abs_eq {c1 c2 : Config}
    (h1 : Reach P.toProgram ((Model.atomic P M).sym S) τ c1)
    (h2 : Reach P.toProgram ((Model.atomic P M).sym S) τ c2) (h : c1.abs = c2.abs) : c1 = c2 :=
  Reach.eq_of_abs_eq h1 h2 h

end Condpor
