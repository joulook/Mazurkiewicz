import Mazurkiewicz.Induction.Check

/-!
# Error actions: simple programs, graphs with error events, the encoding

`induction-popl`, `dpor.tex`, def:errenc, with the definitions of `prelim.tex`
that it needs (def:labels, def:events, def:trace, def:program (i), def:exec,
def:safety, def:sc), for simple programs (read, write and error actions).

How the text is read here.

* A simple program is an `SProgram`. Of the domain conditions of def:program
  it keeps one: no action after an error (`stop`), for the value `⊥` that an
  error event returns.
* A graph with error events is an `EGraph`: a plain graph `G` and the finite
  set `errs` of the threads that have an error event. The error event of `t`
  is the event after the last event of `t` in `G`. These are the graphs of the
  paper with read, write and error events in which a thread has at most one
  error event and it is its last event. Every execution of a simple program
  is of this kind; the set `D` of def:errenc is larger.
* The events are `EEv`; `scStepE` is the base relation of SC on them: an
  error event is neither a source nor a sink (def:events), so it has the
  incoming `po` edges only.
* No step relation is defined on `EGraph`. Safety (`SafeE`) is stated over the
  consistent executions, which are the reachable graphs by prop:reach-exec.
* The markers `λ_t` are a `Markers`: the function `lam`, with a partial
  inverse `own` (so `lam` is injective, and "is a marker" is decidable), and
  the value `v_e`.
* `Ψ` is `EGraph.psi`, its inverse `Graph.psiInv`. `DTail`, `DHatTail` are
  the sets `D`, `D̂` of def:errenc restricted to trailing error events and to
  marker writes that are the last event of their thread.
-/

namespace Trust

/-- The actions of a simple program: read, write, error. -/
inductive SAct
  | read (x : Loc)
  | write (x : Loc) (v : Val)
  | err
  deriving DecidableEq, Repr

/-- A plain action as an action of a simple program. -/
def SAct.ofAct : Act → SAct
  | .read x => .read x
  | .write x v => .write x v

/-- A simple program (def:errenc): as `Program`, with error actions, and no
action after an error (def:program (i)). -/
structure SProgram where
  /-- the threads -/
  threads : List Tid
  /-- no thread is listed twice -/
  threads_nodup : threads.Nodup
  /-- the next action of a thread after a trace -/
  step : Tid → List (Option Val) → Option SAct
  /-- the initial memory -/
  mem : Loc → Val
  /-- threads outside the list do nothing -/
  step_none : ∀ t, t ∉ threads → step t [] = none
  /-- no action after an error -/
  stop : ∀ t u, step t u = some .err → step t (u ++ [none]) = none

/-- No thread performs more than `n` events. -/
def SProgram.Bounded (Q : SProgram) (n : ℕ) : Prop :=
  ∀ t u, n ≤ u.length → Q.step t u = none

/-- A graph with error events: a plain graph and the threads that have an
error event after their last event of the plain graph. -/
@[ext]
structure EGraph where
  /-- the read and write events -/
  G : Graph
  /-- the threads with an error event -/
  errs : Finset Tid

/-- The events of a graph with error events: an event of the plain graph, or
the error event of a thread. -/
inductive EEv
  | ev (a : Ev)
  | err (t : Tid)

namespace EGraph

variable (E : EGraph)

/-- The base relation of SC (def:sc) on a graph with error events: that of
the plain graph, and the `po` edges into the error events. -/
def scStepE : EEv → EEv → Prop
  | .ev a, .ev b => E.G.scStep a b
  | .ev .init, .err t => t ∈ E.errs
  | .ev (.th e), .err t => e ∈ E.G.events ∧ e.tid = t ∧ t ∈ E.errs
  | .err _, _ => False

/-- SC-consistency of a graph with error events. -/
def consE : Prop := Maz.Acyclic E.scStepE

/-- The trace of a thread (def:trace): an error event returns `⊥`. -/
noncomputable def trace (t : Tid) : List (Option Val) :=
  E.G.trace t ++ if t ∈ E.errs then [none] else []

end EGraph

namespace SProgram

variable (Q : SProgram)

/-- `E` is an execution of `Q` (def:exec). -/
def ExecE (E : EGraph) : Prop :=
  E.G.mem = Q.mem ∧
    (∀ e ∈ E.G.events, Q.step e.tid (E.G.traceBefore e.tid e.idx) = some (SAct.ofAct e.act)) ∧
    ∀ t ∈ E.errs, Q.step t (E.G.trace t) = some .err

/-- `E` is full (def:exec): no listed thread has a next action. -/
def FullE (E : EGraph) : Prop := ∀ t ∈ Q.threads, Q.step t (E.trace t) = none

/-- `E ∈ Exec_SC(Q)`, well-formed. -/
def ExecESC (E : EGraph) : Prop := E.G.Wf ∧ Q.ExecE E ∧ E.consE

/-- `E ∈ Full(Q)`. -/
def FullESC (E : EGraph) : Prop := Q.ExecESC E ∧ Q.FullE E

/-- `Q` is safe for `Bad` under SC (def:safety, over `Exec_SC`). -/
def SafeE (Bad : Set EGraph) : Prop := ∀ E, Q.ExecESC E → E ∉ Bad

end SProgram

/-- The assertion property `Bad_err` (def:safety). -/
def BadErr : Set EGraph := {E | E.errs.Nonempty}

/-! ### The encoding (def:errenc) -/

/-- The markers `λ_t` and the value `v_e`. `own` is the partial inverse of
`lam`. -/
structure Markers where
  /-- the marker of a thread -/
  lam : Tid → Loc
  /-- the thread whose marker a location is -/
  own : Loc → Option Tid
  /-- `own` is the partial inverse of `lam` -/
  own_iff : ∀ x t, own x = some t ↔ lam t = x
  /-- the value written to a marker -/
  ve : Val

variable (m : Markers)

/-- No action of `Q` is a read of or a write to a marker. -/
def SProgram.NoMark (Q : SProgram) : Prop :=
  ∀ t u, (∀ x, Q.step t u = some (.read x) → m.own x = none) ∧
    (∀ x v, Q.step t u = some (.write x v) → m.own x = none)

/-- The encoding of an action of thread `t`. -/
def SAct.enc (t : Tid) : SAct → Act
  | .read x => .read x
  | .write x v => .write x v
  | .err => .write (m.lam t) m.ve

/-- The error encoding `Q̂` (def:errenc). -/
def SProgram.enc (Q : SProgram) : Program where
  threads := Q.threads
  threads_nodup := Q.threads_nodup
  step := fun t u => (Q.step t u).map (SAct.enc m t)
  mem := Q.mem
  step_none := fun t ht => by rw [Q.step_none t ht]; rfl

/-- The write that encodes the error event of `t`. -/
def EGraph.mark (E : EGraph) (t : Tid) : TEv := ⟨t, E.G.cnt t, .write (m.lam t) m.ve⟩

/-- `Ψ` (def:errenc): every error event becomes a write to the marker of its
thread, coherence-after `init` only. -/
def EGraph.psi (E : EGraph) : Graph where
  mem := E.G.mem
  events := E.G.events ∪ E.errs.image (E.mark m)
  rf := E.G.rf
  co := fun x =>
    (match m.own x with
    | some t => if t ∈ E.errs then [E.mark m t] else []
    | none => []) ++ E.G.co x

/-- The event is on a marker. -/
def Markers.isMark (e : TEv) : Bool := (m.own e.loc).isSome

/-- `Ψ⁻¹`: the events on markers become error events. -/
def Graph.psiInv (H : Graph) : EGraph where
  G := H.restrict (H.events.filter (fun e => m.isMark e = false))
  errs := (H.events.filter (fun e => m.isMark e = true)).image TEv.tid

/-- The condition of `D̂` on one event. -/
def Markers.markOK (H : Graph) (e : TEv) : Bool :=
  match m.own e.loc with
  | none => true
  | some t => decide (e.tid = t ∧ e.act = .write (m.lam t) m.ve ∧ e.idx + 1 = H.cnt t)

/-- `D`, for trailing error events: no event of the plain graph is on a
marker. -/
def DTail (E : EGraph) : Prop := E.G.Wf ∧ ∀ e ∈ E.G.events, m.own e.loc = none

/-- The marker test of `D̂` (membership in `DHatTail` for a well-formed
graph; well-formedness itself is not tested): an
event on the marker of `t` is the write of `v_e` by `t`, and the last event of
`t`. -/
def dHatTailB (H : Graph) : Bool :=
  decide (∀ e ∈ H.events, m.markOK H e = true)

/-- `D̂`, for marker writes that are last in their thread. -/
def DHatTail (H : Graph) : Prop := H.Wf ∧ dHatTailB m H = true

/-- Some event is on a marker: the property of the graphs of `Q̂` that
corresponds to `Bad_err`. -/
def BadMark : Set Graph := {H | ∃ e ∈ H.events, m.isMark e = true}

end Trust
