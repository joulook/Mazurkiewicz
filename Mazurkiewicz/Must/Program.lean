import Mazurkiewicz.Must.Compute
import Mazurkiewicz.Must.OpsMore
import Mazurkiewicz.Must.Fast
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Permutation

/-!
# Programs, traces, executions (Section 3.3)

Paper: Section 3.3, Example 3.2. Plan: `plan/must/lean/LEAN-PLAN.md`, Section 2b (programs,
returned values), decisions Q6, Q8.

* A program (`Program Q`) is a finite list of threads, in the thread order used by `next_P`
  (Q7), and for every thread a function `step t` from the trace of returned values to the next
  label or to termination (`none`); it is total on traces. Fields: threads outside the list do
  nothing; after `block`, `error` and a blocking receive that returned `⊥` the thread has
  terminated (3.3); an ND label has a non-empty set.
* Returned value (`Graph.ret`): a receive returns the value of its source, or `⊥` (`none`); an ND
  event its outcome; a send, block, error return `⊥`. A payload is not a returned value.
* `Graph.retAt G t i`: the value returned by the event `(t, i)` (`none` if there is none);
  computed as a supremum over the events with identity `(t, i)` of a code of the value, so it is
  computable on a `Finset`; on a well-formed graph it is `ret` of that event
  (`Wf.retAt_eq`).
* `traceBefore G t i`, `trace G t`; `Exec P G` (Section 2b); `Bounded`.
* Computed instances: `MustFast.Code` (a finite tree of actions, `Must/Fast.lean`) denotes a
  thread through `MustFast.Code.run`; `ofCodes` turns a list of codes into a `Program VPred`,
  with the fields proved for every code (`run_stop`, `run_nd`). An ND action with an empty set is
  not representable.
-/

namespace Must

variable {Q : Type}

/-! ### Returned values and traces -/

namespace Graph

variable (G : Graph Q)

/-- The value carried by a send label. -/
def sendVal : Lab Q → Option Val
  | .send _ _ v => some v
  | _ => none

/-- The value returned by the event `e` (Section 2b). -/
def ret (e : Ev Q) : Option Val :=
  match G.rf e with
  | some (.snd s) => sendVal s.lab
  | some .bot => none
  | none => G.nd e

/-- A code of a returned value: `⊥ ↦ 0`, `v ↦ v + 1`. -/
def encR : Option Val → ℕ
  | none => 0
  | some v => v + 1

/-- The inverse of `encR`. -/
def decR : ℕ → Option Val
  | 0 => none
  | n + 1 => some n

@[simp] theorem decR_encR (x : Option Val) : decR (encR x) = x := by cases x <;> rfl

/-- The value returned by the event `(t, i)` of `G`. -/
def retAt (t : Tid) (i : ℕ) : Option Val :=
  decR ((G.events.filter (fun e => e.tid = t ∧ e.idx = i)).sup (fun e => encR (G.ret e)))

/-- The values returned by the first `i` events of thread `t`. -/
def traceBefore (t : Tid) (i : ℕ) : List (Option Val) := (List.range i).map (G.retAt t)

/-- The trace of thread `t` (`trace_G(t)`). -/
def trace (t : Tid) : List (Option Val) := G.traceBefore t (G.cnt t)

variable {G}

/-- On a well-formed graph, `retAt` of the identity of an event is its returned value. -/
theorem Wf.retAt_eq [Membership Val Q] (hG : G.Wf) {e : Ev Q} (he : e ∈ G.events) :
    G.retAt e.tid e.idx = G.ret e := by
  have hf : G.events.filter (fun e' => e'.tid = e.tid ∧ e'.idx = e.idx) = {e} := by
    ext e'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact hG.idx_inj e' h1 e he h2 h3
    · rintro rfl
      exact ⟨he, rfl, rfl⟩
  unfold retAt
  rw [hf, Finset.sup_singleton, decR_encR]

end Graph

/-! ### Programs -/

/-- After this label the thread has terminated if it returned `⊥`: block, error, blocking
receive (3.3). -/
def Lab.Stops : Lab Q → Prop
  | .block => True
  | .error => True
  | .recv a _ => a.blocking = true
  | _ => False

/-- A program (Section 3.3, Section 2b). -/
structure Program (Q : Type) where
  /-- the threads, in thread order -/
  threads : List Tid
  /-- no thread is listed twice -/
  nodup : threads.Nodup
  /-- the next label of a thread after a trace, `none` if it has terminated -/
  step : Tid → List (Option Val) → Option (Lab Q)
  /-- a thread outside the list has no first action (so no event in an execution; its later
  traces are not constrained, and never arise) -/
  step_none : ∀ t, t ∉ threads → step t [] = none
  /-- no action after `block`, `error`, or a blocking receive that returned `⊥` -/
  stop : ∀ t u l, step t u = some l → l.Stops → step t (u ++ [none]) = none
  /-- an ND label has a non-empty set -/
  nd_ne : ∀ t u S, step t u = some (.nd S) → S.Nonempty

namespace Program

variable [DecidableEq Q] (P : Program Q)

/-- `G` is an execution of `P` (Section 2b): every event carries the label that its thread
performs after the values returned by the earlier events of the thread. -/
def Exec (G : Graph Q) : Prop :=
  ∀ e ∈ G.events, P.step e.tid (G.traceBefore e.tid e.idx) = some e.lab

instance (G : Graph Q) : Decidable (P.Exec G) := by
  unfold Exec
  infer_instance

/-- No thread performs more than `n` events. This is a bound per thread; an execution of `P`
then has at most `N = |threads| · n` events (the bound `N` of the plan, Section 2b, bounds the
events of an execution, not the length of an exploration path). -/
def Bounded (n : ℕ) : Prop := ∀ t u, n ≤ u.length → P.step t u = none

/-- The next event of thread `t` in `G`, if the thread has not terminated: index `cnt t`, label
`step t (trace t)`. -/
def nextEv (G : Graph Q) (t : Tid) : Option (Ev Q) :=
  (P.step t (G.trace t)).map (fun l => ⟨t, G.cnt t, l⟩)

/-- The same program with the threads in another order. -/
def reorder (l : List Tid) (h : l.Perm P.threads) : Program Q where
  threads := l
  nodup := h.nodup_iff.mpr P.nodup
  step := P.step
  step_none := fun t ht => P.step_none t (fun h' => ht (h.mem_iff.mpr h'))
  stop := P.stop
  nd_ne := P.nd_ne

/-- The program under every order of its threads. -/
def orders : List (Program Q) :=
  P.threads.permutations.attach.map fun ⟨l, h⟩ => P.reorder l (List.mem_permutations.mp h)

end Program

/-! ### Programs from codes -/

namespace MustFast'

open MustFast

/-- The model of the core as a model of `Must/Event.lean`. -/
def ofModel : MustFast.Model → Comm
  | .asyn => .asyn
  | .p2p => .p2p

/-- A predicate of the core as a `VPred`. -/
def ofPred : FPred → VPred
  | .any => .any
  | .only vs => .fin vs.toFinset

/-- A label of the core as a label. -/
def ofLab : FLab → Lab VPred
  | .recv m b p => .recv ⟨ofModel m, b⟩ (ofPred p)
  | .send m d v => .send (ofModel m) d v
  | .nd vs => .nd vs.toFinset
  | .block => .block
  | .error => .error

/-- The thread `t` of a list of codes, as a step function. -/
def codeStep (cs : List Code) (t : Tid) (u : List (Option Val)) : Option (Lab VPred) :=
  ((cs.getD t .done).run u).map ofLab

theorem run_stop (c : Code) (u : List (Option Val)) (l : FLab) (h : c.run u = some l)
    (hs : (ofLab l).Stops) : c.run (u ++ [none]) = none := by
  induction u generalizing c with
  | nil =>
    cases c with
    | done => simp [Code.run] at h
    | send m d v k =>
      simp only [Code.run, Option.some.injEq] at h
      subst h
      simp [ofLab, Lab.Stops] at hs
    | recv m b p ks kd kb =>
      simp only [Code.run, Option.some.injEq] at h
      subst h
      simp only [ofLab, Lab.Stops] at hs
      simp [Code.run, hs]
    | nd v vs ks kd =>
      simp only [Code.run, Option.some.injEq] at h
      subst h
      simp [ofLab, Lab.Stops] at hs
    | block => rfl
    | error => rfl
  | cons x u ih =>
    cases c with
    | done => simp [Code.run] at h
    | send m d v k => exact ih k h
    | recv m b p ks kd kb =>
      cases x with
      | some v => exact ih _ h
      | none =>
        by_cases hb : b
        · simp [Code.run, hb] at h
        · simp only [Code.run, hb, List.cons_append] at h ⊢
          exact ih kb h
    | nd v vs ks kd =>
      cases x with
      | some w => exact ih _ h
      | none => simp [Code.run] at h
    | block => simp [Code.run] at h
    | error => simp [Code.run] at h

theorem run_nd (c : Code) (u : List (Option Val)) (vs : List Nat) (h : c.run u = some (.nd vs)) :
    vs ≠ [] := by
  induction u generalizing c with
  | nil =>
    cases c with
    | nd v vs' ks kd =>
      simp only [Code.run, Option.some.injEq, FLab.nd.injEq] at h
      subst h
      intro h'
      have hne : ∀ a l, insSorted a l ≠ [] := fun a l => by
        cases l with
        | nil => simp [insSorted]
        | cons b l => unfold insSorted; split_ifs <;> simp
      exact hne v _ (by simpa [sortDedup] using h')
    | send => simp [Code.run] at h
    | recv => simp [Code.run] at h
    | done => simp [Code.run] at h
    | block => simp [Code.run] at h
    | error => simp [Code.run] at h
  | cons x u ih =>
    cases c with
    | done => simp [Code.run] at h
    | send m d v k => exact ih k h
    | recv m b p ks kd kb =>
      cases x with
      | some v => exact ih _ h
      | none =>
        by_cases hb : b
        · simp [Code.run, hb] at h
        · simp only [Code.run, hb] at h
          exact ih kb h
    | nd v vs ks kd =>
      cases x with
      | some w => exact ih _ h
      | none => simp [Code.run] at h
    | block => simp [Code.run] at h
    | error => simp [Code.run] at h

/-- A list of codes as a program: thread `t` runs code number `t`; the threads are
`0, …, n - 1` in this order (other orders: `Program.reorder`, `Program.orders`). -/
def ofCodes (cs : List Code) : Program VPred where
  threads := List.range cs.length
  nodup := List.nodup_range
  step := codeStep cs
  step_none := fun t ht => by
    have : cs.length ≤ t := by simpa using ht
    simp [codeStep, List.getD_eq_getElem?_getD, List.getElem?_eq_none this, Code.run]
  stop := fun t u l h hs => by
    unfold codeStep at h ⊢
    obtain ⟨l', h1, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [run_stop _ u l' h1 hs]
    rfl
  nd_ne := fun t u S h => by
    unfold codeStep at h
    obtain ⟨l', h1, h2⟩ := Option.map_eq_some_iff.mp h
    cases l' with
    | nd vs =>
      simp only [ofLab, Lab.nd.injEq] at h2
      subst h2
      have := run_nd _ u vs h1
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil vs this
      exact ⟨v, List.mem_toFinset.mpr hv⟩
    | _ => simp [ofLab] at h2

end MustFast'

end Must
