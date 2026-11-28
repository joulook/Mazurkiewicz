import Mazurkiewicz.Pct.Position
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Programs, the start-event transformation and static programs

`pctdpor`, `prelim.tex` (def:events, def:trace, def:program, def:gof, the
parts that concern schedules), `testing.tex` (def:start) and `depth.tex`
(lem:strip read on schedules, lem:position, def:positions, def:static,
lem:static-sched and the sentence after it, and thm:static, prop:sh-eq and
def:pviolates read on the schedules of a static program). This file connects
programs to the schedule sets of `Basic.lean`, to `ord` and `Prog.Local` of
`Position.lean`, and to `PSched`, `Complete` and `PGuar` of `Static.lean`.

How the text is read here.

* def:events, def:program: `Act` has the read, write and error labels and a
  fourth label `start`. A `Program` has an initial memory, a finite set
  `tids` of thread identifiers (the text fixes `Tid = [n]`; here `Tid = ℕ`
  and `act t σ` is undefined for `t ∉ tids`), and `act t σ` for `P_t(σ)`.
  A trace is a list over `Option Val` with the **earliest entry at the
  head** (`none` is `⊥`), while a schedule has the latest step at the head.
* def:gof, def:trace: no execution graph is built. `run P S` gives, after
  the steps of `S`, the trace of every thread (`tr`) and the value of the
  latest write to every location (`mem`): a read returns `mem` at its
  location, every other event returns `⊥`, and a write updates `mem`. This
  is `G_S` under `SC` restricted to what a schedule can observe. `run` is
  total: a step of a thread whose next label is undefined changes nothing.
  `IsSched` is "`G_S` is defined" and `sched P` is `Sched(P)`.
* lem:position, its proof: `tr_cons_of_ne` (a step of another thread does
  not change the trace of `t`), `cons_cons_mem_sched_iff` (it neither
  enables nor disables `t`, started or not), `sched_local`, `length_tr`
  (the trace of `t` has `count t S` entries) and `posNext_sched` (`posNext`
  of `Position.lean` is the `nxt` of the text).
* def:start: `plus P` is `P⁺`. The start event of the text writes
  `m₀(z_t)` to a fresh location `z_t`. Here it has the label `Act.start`,
  which changes no location and returns `⊥`; no other event accesses `z_t`,
  so the schedules and the traces are the same. The set of locations is not
  extended. `Act.start` is a label of `Act` and so is available to
  untransformed programs too: the model is an extension of that of the
  text, not literally a restriction of it. The abstraction preserves the
  schedules and the returned traces, not the labelled graphs.
* lem:strip, on schedules: `strip S` removes the first step of every thread.
  `run_plus` relates the memory and the traces of `P⁺` after `S` to those
  of `P` after `strip S`, and `mem_sched_plus_iff` characterises
  `Sched(P⁺)`. `complete_plus_iff` is the part on full executions: `S` is
  complete in `P⁺` iff `strip S` is complete in `P` and every thread of `P`
  has started. `plus_act_of_notMem`: the first step of a thread in a
  schedule of `P⁺` is its start event; by the definition of `ord` it emits
  no position.
* sec:static on schedule sets: `Prog.HasLen Q len` says that thread `t` is
  enabled after a schedule iff it has taken fewer than `len t` steps. It
  holds for `Sched(P)` with `len = Prog.len` if `P` is static and bounded
  (`Static.hasLen`, through `Prog.Uniform`), and then for `Sched(P⁺)` with
  one more step for every thread of `P` (`hasLen_plus`, `lenPlus`,
  `Static.len_plus`). All results on order words are proved for an
  arbitrary schedule set with `HasLen` and then stated for `P⁺`.
* def:static: `Program.Static`. The text quantifies over the executions
  `G ∈ Exec(P)` and the prefixes of `trace_G(t)`; here the quantification is
  over the schedules `S` of `P` and the traces `tr S t`. The two agree by
  cor:classes and because a prefix of a trace is the trace after a prefix of
  the schedule; this is not formalised. Only the part on definedness is
  used; the part on labels (`Act.SameAccess`) is carried along and shown to
  be preserved by `P ↦ P⁺` (`Static.plus`).
* Boundedness (`Prog.Bounded`) is a hypothesis where a length is needed; the
  text assumes it for every program after def:program.
* def:positions, sec:static: `Pos len` is the set of the positions `(t, i)`
  with `1 ≤ i < len t`, a structure with the order "same thread, smaller
  index" (`Pos.lt_iff`); it is finite if finitely many threads have a
  non-zero length (`Pos.finite`, `finite_pos`). `Pos.name` is the name
  `(t, i)` of the position labelling. `Prog.HasLen.exists_mem_ord_iff`: these
  are the names that some schedule emits. `ordP len S` is the order word as
  a list of positions, and `map_name_ordP` identifies it with `ord S`.
* lem:static-sched and the sentence after it: `psched_ordP` (the order word
  is a `PSched` list; this holds for every sequence of thread identifiers),
  `Prog.HasLen.exists_ordP_eq` (every `PSched` list is the order word of a
  schedule), `Prog.HasLen.complete_ordP` and
  `Prog.HasLen.exists_complete_ordP_eq` (the two halves of
  lem:static-sched), and the versions for a bounded static `P`:
  `Static.psched_ord`, `Static.exists_sched_ord_eq`, `Static.complete_ord`,
  `Static.exists_complete_ord_eq`.
* Complete schedules and complete order words are not the same.
  `Prog.HasLen.complete_iff_ordP`: `S` is complete iff `ordP len S` is
  complete and every thread of length `1` has taken its step. For `P⁺`
  (`Static.complete_iff`) these are the threads of `P` without events: with
  `tids = {1, 2}`, one write in thread `1` and no event in thread `2`, the
  schedule `1 1` of `P⁺` has the complete order word `(1, 1)` and is not
  complete, as the start event of thread `2` is enabled. The text states
  only the implication from left to right and the existence of a complete
  schedule for every linear extension, and both hold
  (`exists_complete_extension` adds the missing start events).
* def:pviolates, thm:static, prop:sh-eq on schedules: a directive on
  positions is a `PDir (Pos len) d`; `PDir.toDirective` is the same
  directive on names. For a labelling with `IsPos` (for instance `posLab`,
  `cntLab`), `Prog.HasLen.pviolates_iff_viol` is lem:viol-order with the
  list of positions, and `Prog.HasLen.pguarantees_iff_pguar` states that
  `Directive.PGuarantees` for the schedule bug `{S | ordP len S ∈ B}` is
  `PGuar D B` of `Static.lean`. With it and `Directive.PGuarantees.mono`,
  `stronglyGuar_of_pguarantees` (thm:static (1)), `pguarantees_chainDir`
  (thm:static (2), as def:hdep states it) and
  `exists_pguarantees_of_stronglyGuar` (prop:sh-eq, direction `≥`) are the
  results of `Static.lean` on schedules, each for an arbitrary schedule bug
  `B : Set Sched`: hitting, strong hitting and p-violation depend on the
  order word only, so no assumption on `B` is needed and lem:ord-graph is
  not used. The versions with the suffix `_ord` are the instances for a bug
  `{S | ordP len S ∈ B}`. The condition "all targets are emitted" in
  condition 2 of def:pviolates holds because the names are positions.

Not formalised: events, execution graphs, `rf`, `co`, `SC`-consistency,
linearisations, prop:sched-to-graph, prop:graph-to-sched, cor:classes,
prop:traces; the fresh locations `z_t` and `strip` as a bijection of graphs
(lem:strip is read on schedules only: `mem_sched_plus_iff`,
`complete_plus_iff`; `strip` is not injective on schedules and no bijection
is claimed); `maxsteps` and `maxsteps(P⁺) = maxsteps(P) + n`; lem:ord-graph
and `G_α`, so a bug is a set of schedules or a set of order words and not a
set of graphs. This concerns def:shdep only, whose statement with `G_α`
needs that a graph bug `\widehat{B}` is of the form `{S | ordP len S ∈ B}`
on complete schedules; thm:static (1), (2) and prop:sh-eq `≥` are stated on
schedules and do not need it. Also not formalised: the reading
"`G_S` has an event of thread `t` with index `i`" of lem:position; the
canonical labelling; directives with names that are not positions; the
depths `hdep`, `shdep`, `pdep` as numbers; sec:branching. `Pos_P` is defined
only through `HasLen`, that is, for static bounded programs. The equivalence
of `Program.Static` with def:static stated on graphs is not proved.
-/

namespace Pct

/-! ### Programs and their schedules (def:program, def:gof) -/

/-- Labels (def:events): a read of a location, a write of a value to a
location, the error label, and the label of a start event (def:start). -/
inductive Act (Loc Val : Type) where
  | read (x : Loc)
  | write (x : Loc) (v : Val)
  | err
  | start

/-- A trace (def:trace): the values returned by the events of a thread, in
index order (the earliest at the head); `none` is `⊥`. -/
abbrev Trace (Val : Type) := List (Option Val)

/-- A program (def:program): for every thread a partial function from traces
to labels. The threads are those of `tids`. -/
structure Program (Loc Val : Type) where
  /-- The initial memory. -/
  init : Loc → Val
  /-- The thread identifiers of the program. -/
  tids : Finset Tid
  /-- The next label of a thread after a trace. -/
  act : Tid → Trace Val → Option (Act Loc Val)
  act_none : ∀ t, t ∉ tids → ∀ σ, act t σ = none

/-- The traces of all threads and the memory after a schedule. -/
structure State (Loc Val : Type) where
  /-- The trace of every thread. -/
  tr : Tid → Trace Val
  /-- The value of the latest write to every location. -/
  mem : Loc → Val

variable {Loc Val : Type}

/-- The value returned by an event with the given label in the memory `m`
(def:trace). -/
def Act.ret (m : Loc → Val) : Act Loc Val → Option Val
  | .read x => some (m x)
  | _ => none

/-- The memory after an event with the given label (def:gof). -/
def Act.upd [DecidableEq Loc] (m : Loc → Val) : Act Loc Val → Loc → Val
  | .write x v => Function.update m x v
  | _ => m

namespace Program

variable [DecidableEq Loc] (P : Program Loc Val)

/-- The traces and the memory after the steps of `S` (def:gof). A step of a
thread whose next label is undefined changes nothing. -/
def run : Sched → State Loc Val
  | [] => ⟨fun _ => [], P.init⟩
  | t :: S =>
    match P.act t ((run S).tr t) with
    | none => run S
    | some a =>
      ⟨Function.update (run S).tr t ((run S).tr t ++ [a.ret (run S).mem]), a.upd (run S).mem⟩

/-- The trace of `t` after `S` (`trace_{G_S}(t)`). -/
def tr (S : Sched) (t : Tid) : Trace Val := (P.run S).tr t

/-- The memory after `S`: the value of the latest write to every location. -/
def mem (S : Sched) : Loc → Val := (P.run S).mem

/-- `G_S` is defined (def:gof). -/
def IsSched : Sched → Prop
  | [] => True
  | t :: S => IsSched S ∧ (P.act t (P.tr S t)).isSome

/-- The schedules of the program, `Sched(P)` (def:gof). -/
def sched : Prog where
  mem := {S | P.IsSched S}
  nil_mem := trivial
  tail_mem := fun h => h.1

/-- Membership in `Sched(P)` at a step. -/
theorem cons_mem_sched {t : Tid} {S : Sched} :
    t :: S ∈ P.sched.mem ↔ S ∈ P.sched.mem ∧ (P.act t (P.tr S t)).isSome := Iff.rfl

/-- The traces are empty after the empty schedule. -/
@[simp] theorem tr_nil (t : Tid) : P.tr [] t = [] := rfl

/-- The memory after the empty schedule is the initial memory. -/
@[simp] theorem mem_nil : P.mem [] = P.init := rfl

/-- A step with an undefined label changes nothing. -/
theorem run_cons_of_none {t : Tid} {S : Sched} (h : P.act t (P.tr S t) = none) :
    P.run (t :: S) = P.run S := by
  have h' : P.act t ((P.run S).tr t) = none := h
  simp only [run, h']

/-- A step with an undefined label does not change the traces. -/
theorem tr_cons_of_none {t : Tid} {S : Sched} (h : P.act t (P.tr S t) = none) (u : Tid) :
    P.tr (t :: S) u = P.tr S u := by
  unfold tr
  rw [P.run_cons_of_none h]

/-- A step with an undefined label does not change the memory. -/
theorem mem_cons_of_none {t : Tid} {S : Sched} (h : P.act t (P.tr S t) = none) :
    P.mem (t :: S) = P.mem S := by
  unfold mem
  rw [P.run_cons_of_none h]

/-- A step of `t` extends the trace of `t` by the returned value (def:gof,
def:trace). -/
theorem tr_cons_self {t : Tid} {S : Sched} {a : Act Loc Val} (h : P.act t (P.tr S t) = some a) :
    P.tr (t :: S) t = P.tr S t ++ [a.ret (P.mem S)] := by
  have h' : P.act t ((P.run S).tr t) = some a := h
  simp only [tr, mem, run, h', Function.update_self]

/-- The memory after a step (def:gof). -/
theorem mem_cons_of_some {t : Tid} {S : Sched} {a : Act Loc Val}
    (h : P.act t (P.tr S t) = some a) : P.mem (t :: S) = a.upd (P.mem S) := by
  have h' : P.act t ((P.run S).tr t) = some a := h
  simp only [mem, run, h']

/-- A step of another thread does not change the trace of `t` (proof of
lem:position). -/
theorem tr_cons_of_ne {t t' : Tid} (S : Sched) (h : t' ≠ t) : P.tr (t' :: S) t = P.tr S t := by
  cases h' : P.act t' ((P.run S).tr t') with
  | none => simp only [tr, run, h']
  | some a => simp only [tr, run, h', Function.update_of_ne h.symm]

/-- Steps of other threads do not change the trace of `t`. -/
theorem tr_append_of_notMem {t : Tid} {U : Sched} (S : Sched) (h : t ∉ U) :
    P.tr (U ++ S) t = P.tr S t := by
  induction U with
  | nil => rfl
  | cons u U ih =>
    rw [List.cons_append, P.tr_cons_of_ne _ (fun e => h (by simp [e])),
      ih (fun m => h (List.mem_cons_of_mem _ m))]

/-- A thread that has taken no step has the empty trace. -/
theorem tr_of_notMem {t : Tid} {S : Sched} (h : t ∉ S) : P.tr S t = [] := by
  have := P.tr_append_of_notMem [] h
  simpa using this

/-- In a schedule of `P` the trace of `t` has one entry for every step of
`t`. -/
theorem length_tr {S : Sched} (h : S ∈ P.sched.mem) (t : Tid) :
    (P.tr S t).length = S.count t := by
  induction S with
  | nil => rfl
  | cons u S ih =>
    obtain ⟨hS, hu⟩ := (P.cons_mem_sched).mp h
    by_cases hut : u = t
    · subst hut
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hu
      rw [P.tr_cons_self ha, List.length_append, ih hS, List.count_cons_self]
      rfl
    · rw [P.tr_cons_of_ne _ hut, ih hS, List.count_cons_of_ne hut]

/-- A step of another thread neither enables nor disables `t` (proof of
lem:position); `t` need not have started. -/
theorem cons_cons_mem_sched_iff {S : Sched} {t t' : Tid} (h : t' :: S ∈ P.sched.mem)
    (hne : t' ≠ t) : t :: t' :: S ∈ P.sched.mem ↔ t :: S ∈ P.sched.mem := by
  rw [P.cons_mem_sched, P.cons_mem_sched, P.tr_cons_of_ne _ hne]
  exact ⟨fun k => ⟨h.1, k.2⟩, fun k => ⟨h, k.2⟩⟩

/-- `Sched(P)` is local (lem:position). -/
theorem sched_local : P.sched.Local :=
  fun _ _ _ h hne _ => P.cons_cons_mem_sched_iff h hne

/-- lem:position: on `Sched(P)` the function `posNext` is the `nxt` of the
text, `(t, |σ|)` with `σ` the trace of `t` if `|σ| ≥ 1` and `P_t(σ)` is
defined. -/
theorem posNext_sched {S : Sched} (h : S ∈ P.sched.mem) (t : Tid) (a : Tid × ℕ) :
    posNext P.sched S t = some a ↔
      1 ≤ (P.tr S t).length ∧ (P.act t (P.tr S t)).isSome ∧ a = (t, (P.tr S t).length) := by
  rw [posNext_eq_some, P.length_tr h, P.cons_mem_sched]
  exact ⟨fun k => ⟨k.1, k.2.1.2, k.2.2⟩, fun k => ⟨k.1, ⟨h, k.2.1⟩, k.2.2⟩⟩

/-! ### The start-event transformation (def:start, lem:strip) -/

/-- `P⁺_t` (def:start): the start label on the empty trace, `P_t(σ)` on
`⊥ · σ`, undefined elsewhere. -/
def plusAct (t : Tid) : Trace Val → Option (Act Loc Val)
  | [] => if t ∈ P.tids then some Act.start else none
  | none :: σ => P.act t σ
  | some _ :: _ => none

/-- The program `P⁺` (def:start). -/
def plus : Program Loc Val where
  init := P.init
  tids := P.tids
  act := P.plusAct
  act_none := by
    intro t ht σ
    match σ with
    | [] => simp [plusAct, ht]
    | none :: σ => exact P.act_none t ht σ
    | some _ :: _ => rfl

omit [DecidableEq Loc] in
/-- def:start: the first label of every thread of `P⁺` is the start
label. -/
theorem plus_act_nil {t : Tid} (h : t ∈ P.tids) : P.plus.act t [] = some Act.start := by
  simp [plus, plusAct, h]

omit [DecidableEq Loc] in
/-- def:start: `P⁺_t(⊥ · σ) = P_t(σ)`. -/
@[simp] theorem plus_act_cons (t : Tid) (σ : Trace Val) :
    P.plus.act t (none :: σ) = P.act t σ := rfl

/-- def:start: the first step of a thread in a schedule of `P⁺` is its start
event. -/
theorem plus_act_of_notMem {S : Sched} {t : Tid} (h : t :: S ∈ P.plus.sched.mem)
    (ht : t ∉ S) : P.plus.act t (P.plus.tr S t) = some Act.start := by
  have hsome := ((P.plus).cons_mem_sched.mp h).2
  rw [(P.plus).tr_of_notMem ht] at hsome ⊢
  by_cases hT : t ∈ P.tids
  · exact P.plus_act_nil hT
  · rw [P.plus.act_none t hT] at hsome
    simp at hsome

/-- `Sched(P⁺)` is local. -/
theorem sched_plus_local : P.plus.sched.Local := P.plus.sched_local

/-- The schedule of `P` that a schedule of `P⁺` stands for: the first step
of every thread is removed (`strip` of lem:strip, read on schedules). -/
def strip : Sched → Sched
  | [] => []
  | t :: S => if t ∈ S then t :: strip S else strip S

/-- A thread occurs in `strip S` only if it occurs in `S`. -/
theorem mem_of_mem_strip {S : Sched} {t : Tid} (h : t ∈ strip S) : t ∈ S := by
  induction S with
  | nil => simp [strip] at h
  | cons u S ih =>
    unfold strip at h
    split_ifs at h with hu
    · rcases List.mem_cons.mp h with e | h
      · exact List.mem_cons.mpr (Or.inl e)
      · exact List.mem_cons_of_mem _ (ih h)
    · exact List.mem_cons_of_mem _ (ih h)

/-- `strip` removes one step of every thread that occurs. -/
theorem count_strip (S : Sched) (t : Tid) : (strip S).count t = S.count t - 1 := by
  induction S with
  | nil => rfl
  | cons u S ih =>
    unfold strip
    by_cases hu : u ∈ S
    · rw [ite_eq_left hu]
      by_cases hut : u = t
      · subst hut
        have := List.count_pos_iff.mpr hu
        rw [List.count_cons_self, List.count_cons_self, ih]
        omega
      · rw [List.count_cons_of_ne hut, List.count_cons_of_ne hut, ih]
    · rw [ite_eq_right hu, ih]
      by_cases hut : u = t
      · subst hut
        rw [List.count_cons_self, List.count_eq_zero.mpr hu]
      · rw [List.count_cons_of_ne hut]

/-- lem:strip, read on schedules: after steps of threads of `P`, the memory
of `P⁺` after `S` is the memory of `P` after `strip S`, and the trace of a
thread that has started is `⊥` followed by its trace in `P`. -/
theorem run_plus {S : Sched} (hT : ∀ t ∈ S, t ∈ P.tids) :
    P.plus.mem S = P.mem (strip S) ∧
      ∀ t, P.plus.tr S t = if t ∈ S then none :: P.tr (strip S) t else [] := by
  induction S with
  | nil => exact ⟨rfl, fun t => rfl⟩
  | cons u S ih =>
    obtain ⟨ihm, iht⟩ := ih (fun t ht => hT t (List.mem_cons_of_mem _ ht))
    have huT : u ∈ P.tids := hT u (List.mem_cons.mpr (Or.inl rfl))
    by_cases hu : u ∈ S
    · have hs : strip (u :: S) = u :: strip S := by rw [strip, ite_eq_left hu]
      have htr : P.plus.tr S u = none :: P.tr (strip S) u := by rw [iht u, ite_eq_left hu]
      have hact : P.plus.act u (P.plus.tr S u) = P.act u (P.tr (strip S) u) := by
        rw [htr, plus_act_cons]
      rw [hs]
      cases ha : P.act u (P.tr (strip S) u) with
      | none =>
        rw [ha] at hact
        refine ⟨by rw [P.plus.mem_cons_of_none hact, P.mem_cons_of_none ha, ihm], fun t => ?_⟩
        rw [P.plus.tr_cons_of_none hact, P.tr_cons_of_none ha, iht t]
        by_cases htu : t = u
        · subst htu
          simp [hu]
        · simp [htu]
      | some a =>
        rw [ha] at hact
        refine ⟨by rw [P.plus.mem_cons_of_some hact, P.mem_cons_of_some ha, ihm], fun t => ?_⟩
        by_cases htu : t = u
        · subst htu
          rw [P.plus.tr_cons_self hact, P.tr_cons_self ha, htr, ihm]
          simp
        · have hne : u ≠ t := fun e => htu e.symm
          rw [P.plus.tr_cons_of_ne _ hne, P.tr_cons_of_ne _ hne, iht t]
          simp [htu]
    · have hs : strip (u :: S) = strip S := by rw [strip, ite_eq_right hu]
      have htr : P.plus.tr S u = [] := P.plus.tr_of_notMem hu
      have hact : P.plus.act u (P.plus.tr S u) = some Act.start := by
        rw [htr]
        exact P.plus_act_nil huT
      rw [hs]
      refine ⟨by rw [P.plus.mem_cons_of_some hact, ihm]; rfl, fun t => ?_⟩
      by_cases htu : t = u
      · subst htu
        rw [P.plus.tr_cons_self hact, htr, P.tr_of_notMem (fun m => hu (mem_of_mem_strip m))]
        simp [Act.ret]
      · have hne : u ≠ t := fun e => htu e.symm
        rw [P.plus.tr_cons_of_ne _ hne, iht t]
        simp [htu]

/-- Every step of a schedule of `P` is a step of a thread of `P`. -/
theorem mem_tids_of_mem_sched {S : Sched} (h : S ∈ P.sched.mem) {t : Tid} (ht : t ∈ S) :
    t ∈ P.tids := by
  induction S with
  | nil => simp at ht
  | cons u S ih =>
    obtain ⟨hS, hu⟩ := P.cons_mem_sched.mp h
    rcases List.mem_cons.mp ht with e | ht
    · by_contra hn
      rw [P.act_none u (e ▸ hn)] at hu
      simp at hu
    · exact ih hS ht

/-- lem:strip, read on schedules: `S` is a schedule of `P⁺` iff its steps are
steps of threads of `P` and `strip S` is a schedule of `P`. -/
theorem mem_sched_plus_iff {S : Sched} :
    S ∈ P.plus.sched.mem ↔ (∀ t ∈ S, t ∈ P.tids) ∧ strip S ∈ P.sched.mem := by
  induction S with
  | nil => exact ⟨fun _ => ⟨by simp, trivial⟩, fun _ => trivial⟩
  | cons u S ih =>
    rw [P.plus.cons_mem_sched, ih]
    constructor
    · rintro ⟨⟨hT, hS⟩, hu⟩
      have huT : u ∈ P.tids := by
        by_contra hn
        rw [P.plus.act_none u hn] at hu
        simp at hu
      refine ⟨fun t ht => ?_, ?_⟩
      · rcases List.mem_cons.mp ht with e | ht
        · rw [e]
          exact huT
        · exact hT t ht
      · by_cases hmem : u ∈ S
        · rw [(P.run_plus hT).2 u, ite_eq_left hmem, plus_act_cons] at hu
          rw [strip, ite_eq_left hmem]
          exact ⟨hS, hu⟩
        · rw [strip, ite_eq_right hmem]
          exact hS
    · rintro ⟨hT, hS⟩
      have hT' : ∀ t ∈ S, t ∈ P.tids := fun t ht => hT t (List.mem_cons_of_mem _ ht)
      by_cases hmem : u ∈ S
      · rw [strip, ite_eq_left hmem] at hS
        refine ⟨⟨hT', hS.1⟩, ?_⟩
        rw [(P.run_plus hT').2 u, ite_eq_left hmem, plus_act_cons]
        exact hS.2
      · rw [strip, ite_eq_right hmem] at hS
        refine ⟨⟨hT', hS⟩, ?_⟩
        rw [P.plus.tr_of_notMem hmem, P.plus_act_nil (hT u (List.mem_cons.mpr (Or.inl rfl)))]
        rfl

/-- lem:strip, the part on full executions, read on schedules: a schedule of
`P⁺` is complete iff `strip S` is a complete schedule of `P` and every thread
of `P` has started. -/
theorem complete_plus_iff {S : Sched} :
    P.plus.sched.Complete S ↔
      S ∈ P.plus.sched.mem ∧ P.sched.Complete (strip S) ∧ ∀ t ∈ P.tids, t ∈ S := by
  constructor
  · rintro ⟨hS, hn⟩
    obtain ⟨hT, hs⟩ := P.mem_sched_plus_iff.mp hS
    have hall : ∀ t ∈ P.tids, t ∈ S := by
      intro t ht
      by_contra hm
      refine hn t (P.mem_sched_plus_iff.mpr ⟨?_, ?_⟩)
      · exact fun u hu => (List.mem_cons.mp hu).elim (fun e => e ▸ ht) (hT u)
      · rw [strip, ite_eq_right hm]
        exact hs
    refine ⟨hS, ⟨hs, fun t ht => ?_⟩, hall⟩
    have htT : t ∈ P.tids := P.mem_tids_of_mem_sched ht List.mem_cons_self
    refine hn t (P.mem_sched_plus_iff.mpr
      ⟨fun u hu => (List.mem_cons.mp hu).elim (fun e => e ▸ htT) (hT u), ?_⟩)
    rw [strip, ite_eq_left (hall t htT)]
    exact ht
  · rintro ⟨hS, hc, hall⟩
    refine ⟨hS, fun t ht => ?_⟩
    obtain ⟨hT, hs⟩ := P.mem_sched_plus_iff.mp ht
    have hm : t ∈ S := hall t (hT t List.mem_cons_self)
    rw [strip, ite_eq_left hm] at hs
    exact hc.2 t hs

end Program

/-! ### Schedule sets with thread lengths (def:static, on schedule sets) -/

/-- The schedule set is that of threads of fixed lengths: after a schedule
`S`, thread `t` is enabled iff it has taken fewer than `len t` steps. -/
def Prog.HasLen (Q : Prog) (len : Tid → ℕ) : Prop :=
  ∀ ⦃S : Sched⦄, S ∈ Q.mem → ∀ t, t :: S ∈ Q.mem ↔ S.count t < len t

/-- Whether a thread is enabled depends only on the number of steps it has
taken (def:static, the part on definedness, read on the schedule set). -/
def Prog.Uniform (Q : Prog) : Prop :=
  ∀ ⦃S S' : Sched⦄ (t : Tid), S ∈ Q.mem → S' ∈ Q.mem → S.count t = S'.count t →
    t :: S ∈ Q.mem → t :: S' ∈ Q.mem

/-- The largest number of steps of `t` in a schedule (`len_t` of sec:static
for a bounded uniform schedule set). -/
noncomputable def Prog.len (Q : Prog) (t : Tid) : ℕ := sSup {n | ∃ S ∈ Q.mem, S.count t = n}

/-- A schedule in which `t` takes more than `i` steps has a prefix that ends
with the step of `t` with index `i`. -/
theorem exists_suffix_count {t : Tid} {S : Sched} {i : ℕ} (h : i < S.count t) :
    ∃ S', t :: S' <:+ S ∧ S'.count t = i := by
  induction S with
  | nil => simp at h
  | cons u S ih =>
    by_cases hut : u = t
    · subst hut
      rw [List.count_cons_self] at h
      by_cases e : i = S.count u
      · exact ⟨S, List.suffix_refl _, e.symm⟩
      · obtain ⟨S', hs, hc⟩ := ih (by omega)
        exact ⟨S', hs.trans (List.suffix_cons _ _), hc⟩
    · rw [List.count_cons_of_ne hut] at h
      obtain ⟨S', hs, hc⟩ := ih h
      exact ⟨S', hs.trans (List.suffix_cons _ _), hc⟩

/-- sec:static: in a bounded uniform schedule set every thread `t` has a
length `len_t`, and it is enabled iff it has taken fewer than `len_t`
steps. -/
theorem Prog.Uniform.hasLen {Q : Prog} (hU : Q.Uniform) {k : ℕ} (hB : Q.Bounded k) :
    Q.HasLen Q.len := by
  intro S hS t
  have hbdd : BddAbove {n | ∃ S ∈ Q.mem, S.count t = n} :=
    ⟨k, by rintro n ⟨S, hS, rfl⟩; exact (List.count_le_length).trans (hB S hS)⟩
  constructor
  · intro h
    have : S.count t + 1 ≤ Q.len t := le_csSup hbdd ⟨t :: S, h, List.count_cons_self⟩
    omega
  · intro h
    have hne : {n | ∃ S ∈ Q.mem, S.count t = n}.Nonempty := ⟨0, [], Q.nil_mem, rfl⟩
    obtain ⟨S₀, hS₀, hc⟩ := Nat.sSup_mem hne hbdd
    obtain ⟨S', hs, hc'⟩ := exists_suffix_count (t := t) (S := S₀) (i := S.count t)
      (by rw [hc]; exact h)
    have h' := Q.suffix_mem hS₀ hs
    exact hU t (Q.tail_mem h') hS hc' h'

section HasLen

variable {Q : Prog} {len : Tid → ℕ}

/-- The schedules are the sequences in which every thread `t` takes at most
`len t` steps. -/
theorem Prog.HasLen.mem_iff (hQ : Q.HasLen len) {S : Sched} :
    S ∈ Q.mem ↔ ∀ t, S.count t ≤ len t := by
  induction S with
  | nil => exact ⟨fun _ t => by simp, fun _ => Q.nil_mem⟩
  | cons u S ih =>
    constructor
    · intro h t
      have hS := Q.tail_mem h
      have h1 := (hQ hS u).mp h
      have h2 := ih.mp hS t
      by_cases hut : u = t
      · subst hut
        rw [List.count_cons_self]
        omega
      · rw [List.count_cons_of_ne hut]
        exact h2
    · intro h
      have hS : S ∈ Q.mem := ih.mpr fun t => (List.count_le_count_cons).trans (h t)
      have := h u
      rw [List.count_cons_self] at this
      exact (hQ hS u).mpr (by omega)

/-- A schedule is complete iff every thread `t` has taken `len t` steps. -/
theorem Prog.HasLen.complete_iff (hQ : Q.HasLen len) {S : Sched} :
    Q.Complete S ↔ S ∈ Q.mem ∧ ∀ t, len t ≤ S.count t := by
  constructor
  · rintro ⟨hS, hn⟩
    exact ⟨hS, fun t => by have := mt (hQ hS t).mpr (hn t); omega⟩
  · rintro ⟨hS, hc⟩
    exact ⟨hS, fun t h => by have := (hQ hS t).mp h; have := hc t; omega⟩

/-- Thread `t` alone can take `len t` steps. -/
theorem Prog.HasLen.replicate_mem (hQ : Q.HasLen len) (t : Tid) :
    List.replicate (len t) t ∈ Q.mem := by
  refine hQ.mem_iff.mpr fun u => ?_
  by_cases hut : t = u
  · subst hut
    simp
  · rw [List.count_eq_zero.mpr (fun m => hut (List.eq_of_mem_replicate m).symm)]
    exact Nat.zero_le _

/-- def:positions with sec:static: the positions emitted in some schedule
are the pairs `(t, i)` with `1 ≤ i < len t`. -/
theorem Prog.HasLen.exists_mem_ord_iff (hQ : Q.HasLen len) {t : Tid} {i : ℕ} :
    (∃ S ∈ Q.mem, (t, i) ∈ ord S) ↔ 1 ≤ i ∧ i < len t := by
  constructor
  · rintro ⟨S, hS, hm⟩
    have := mem_ord_iff.mp hm
    have := hQ.mem_iff.mp hS t
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨_, hQ.replicate_mem t, mem_ord_iff.mpr ⟨h1, by simpa using h2⟩⟩

/-- The thread lengths are determined by the schedule set: `len t` is the
largest number of steps of `t` in a schedule. -/
theorem Prog.HasLen.len_eq (hQ : Q.HasLen len) : Q.len = len := by
  funext t
  refine IsGreatest.csSup_eq ⟨⟨_, hQ.replicate_mem t, by simp⟩, ?_⟩
  rintro n ⟨S, hS, rfl⟩
  exact hQ.mem_iff.mp hS t

end HasLen

/-! ### The poset of positions and the order word as a list of positions -/

/-- A position of a schedule set with thread lengths `len`: a thread `t` and
an index `i` with `1 ≤ i < len t` (`Pos_P` of def:positions, for a static
program, sec:static). -/
@[ext] structure Pos (len : Tid → ℕ) where
  /-- The thread of the position. -/
  thr : Tid
  /-- The index of the position. -/
  idx : ℕ
  one_le : 1 ≤ idx
  lt_len : idx < len thr

variable {len : Tid → ℕ}

/-- The position as a name of the position labelling. -/
def Pos.name (x : Pos len) : Tid × ℕ := (x.thr, x.idx)

/-- Positions are determined by their names. -/
theorem Pos.name_injective : Function.Injective (Pos.name (len := len)) := by
  intro x y h
  exact Pos.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- sec:static: `(t, i) ≤ (t, j)` iff `i ≤ j`; positions of different threads
are incomparable. -/
instance (len : Tid → ℕ) : PartialOrder (Pos len) where
  le x y := x.thr = y.thr ∧ x.idx ≤ y.idx
  le_refl _ := ⟨rfl, le_rfl⟩
  le_trans _ _ _ h k := ⟨h.1.trans k.1, h.2.trans k.2⟩
  le_antisymm _ _ h k := Pos.ext h.1 (le_antisymm h.2 k.2)

/-- sec:static: `(t, i) < (t, j)` iff `i < j`. -/
theorem Pos.lt_iff {x y : Pos len} : x < y ↔ x.thr = y.thr ∧ x.idx < y.idx := by
  rw [lt_iff_le_not_ge]
  constructor
  · rintro ⟨⟨e, _⟩, hn⟩
    refine ⟨e, ?_⟩
    by_contra hlt
    exact hn ⟨e.symm, by omega⟩
  · rintro ⟨e, h⟩
    exact ⟨⟨e, h.le⟩, fun k => by have := k.2; omega⟩

/-- There are finitely many positions if finitely many threads have a
non-zero length. -/
theorem Pos.finite (T : Finset Tid) (hT : ∀ t, 0 < len t → t ∈ T) : Finite (Pos len) := by
  have hmem : ∀ x : Pos len, (x.thr, x.idx) ∈ T ×ˢ Finset.range (T.sup len) := fun x =>
    have hx : x.thr ∈ T := hT _ (by have := x.lt_len; omega)
    Finset.mem_product.mpr ⟨hx, Finset.mem_range.mpr (x.lt_len.trans_le (Finset.le_sup hx))⟩
  refine Finite.of_injective
    (fun x : Pos len => (⟨(x.thr, x.idx), hmem x⟩ : ↥(T ×ˢ Finset.range (T.sup len)))) ?_
  intro x y h
  have := congrArg Subtype.val h
  exact Pos.ext (congrArg Prod.fst this) (congrArg Prod.snd this)

/-- The order word as a list of positions (def:positions), the latest at the
head: the step of `t` after `S` contributes `(t, count t S)` if this is a
position. -/
def ordP (len : Tid → ℕ) : Sched → List (Pos len)
  | [] => []
  | t :: S =>
    if h : 1 ≤ S.count t ∧ S.count t < len t then ⟨t, S.count t, h.1, h.2⟩ :: ordP len S
    else ordP len S

/-- `ordP` at a step that emits a position. -/
theorem ordP_cons_of {t : Tid} {S : Sched} (h : 1 ≤ S.count t ∧ S.count t < len t) :
    ordP len (t :: S) = ⟨t, S.count t, h.1, h.2⟩ :: ordP len S := by
  rw [ordP, dite_eq_left h]

/-- `ordP` at a step that emits no position. -/
theorem ordP_cons_of_not {t : Tid} {S : Sched} (h : ¬ (1 ≤ S.count t ∧ S.count t < len t)) :
    ordP len (t :: S) = ordP len S := by
  rw [ordP, dite_eq_right h]

/-- def:positions: the position `(t, i)` occurs in the order word of `S` iff
`t` has taken more than `i` steps in `S`. -/
theorem mem_ordP_iff {S : Sched} {x : Pos len} : x ∈ ordP len S ↔ x.idx < S.count x.thr := by
  obtain ⟨t, i, h1, h2⟩ := x
  simp only
  induction S with
  | nil => simp [ordP]
  | cons u S ih =>
    by_cases h : 1 ≤ S.count u ∧ S.count u < len u
    · rw [ordP_cons_of h, List.mem_cons, ih, Pos.mk.injEq]
      by_cases hut : u = t
      · subst hut
        rw [List.count_cons_self]
        constructor
        · rintro (⟨-, rfl⟩ | h) <;> omega
        · intro h
          by_cases e : i = S.count u
          · exact Or.inl ⟨rfl, e⟩
          · exact Or.inr (by omega)
      · rw [List.count_cons_of_ne hut]
        exact ⟨fun k => k.resolve_left (fun k' => hut k'.1.symm), Or.inr⟩
    · rw [ordP_cons_of_not h, ih]
      by_cases hut : u = t
      · subst hut
        rw [List.count_cons_self]
        omega
      · rw [List.count_cons_of_ne hut]

/-- sec:static, the sentence after lem:static-sched, first half: the order
word of a schedule is a sequence of distinct positions in which every
position is preceded by all positions below it. -/
theorem psched_ordP (len : Tid → ℕ) (S : Sched) : PSched (ordP len S) := by
  induction S with
  | nil => exact psched_nil
  | cons u S ih =>
    by_cases h : 1 ≤ S.count u ∧ S.count u < len u
    · rw [ordP_cons_of h]
      refine psched_cons.mpr ⟨ih, fun hm => ?_, fun y hy => ?_⟩
      · have := mem_ordP_iff.mp hm
        simp at this
      · obtain ⟨e, hlt⟩ := Pos.lt_iff.mp hy
        rw [mem_ordP_iff, e]
        exact hlt
    · rw [ordP_cons_of_not h]
      exact ih

/-- lem:static-sched, first half, for the list of positions: the order word
of `S` contains every position iff every thread with a position has taken
all its steps. -/
theorem complete_ordP_iff {S : Sched} :
    Complete (ordP len S) ↔ ∀ t, 2 ≤ len t → len t ≤ S.count t := by
  constructor
  · intro h t ht
    have := mem_ordP_iff.mp (h ⟨t, len t - 1, by omega, by omega⟩)
    simp only at this
    omega
  · intro h x
    rw [mem_ordP_iff]
    have := x.one_le
    have := x.lt_len
    have := h x.thr (by omega)
    omega

section HasLen

variable {Q : Prog}

/-- The list of positions `ordP len S` is the order word `ord S`
(def:positions) for a schedule `S`. -/
theorem Prog.HasLen.map_name_ordP (hQ : Q.HasLen len) {S : Sched} (h : S ∈ Q.mem) :
    (ordP len S).map Pos.name = ord S := by
  induction S with
  | nil => rfl
  | cons u S ih =>
    have hS := Q.tail_mem h
    have hlt := (hQ hS u).mp h
    rw [ord_cons]
    by_cases hc : 1 ≤ S.count u
    · rw [ordP_cons_of ⟨hc, hlt⟩, ite_eq_left hc, List.map_cons, ih hS]
      rfl
    · rw [ordP_cons_of_not (fun k => hc k.1), ite_eq_right hc, ih hS]

/-- sec:static: if the order word of `S` followed by the position `x` is a
partial schedule of the poset, then the thread of `x` is enabled after `S`,
and its step emits `x`, or it is the first step of the thread, emits nothing,
and the next step of the thread emits `x`. -/
theorem Prog.HasLen.step (hQ : Q.HasLen len) {S : Sched} (hS : S ∈ Q.mem) {x : Pos len}
    (hx : PSched (x :: ordP len S)) :
    x.thr :: S ∈ Q.mem ∧ (ordP len (x.thr :: S) = x :: ordP len S ∨
      (ordP len (x.thr :: S) = ordP len S ∧ x.thr :: x.thr :: S ∈ Q.mem ∧
        ordP len (x.thr :: x.thr :: S) = x :: ordP len S)) := by
  obtain ⟨-, hnot, hdown⟩ := psched_cons.mp hx
  obtain ⟨t, i, h1, h2⟩ := x
  simp only
  have hle : S.count t ≤ i := by
    have := mt mem_ordP_iff.mpr hnot
    simpa using this
  by_cases hc : S.count t = i
  · subst hc
    exact ⟨(hQ hS t).mpr h2, Or.inl (ordP_cons_of ⟨h1, h2⟩)⟩
  · have hi : i = 1 := by
      by_contra hne
      have := mem_ordP_iff.mp (hdown ⟨t, i - 1, by omega, by omega⟩
        (Pos.lt_iff.mpr ⟨rfl, by simp only; omega⟩))
      simp only at this
      omega
    subst hi
    have h0 : S.count t = 0 := by omega
    have hm : t :: S ∈ Q.mem := (hQ hS t).mpr (by omega)
    have hc1 : (t :: S).count t = 1 := by rw [List.count_cons_self, h0]
    refine ⟨hm, Or.inr ⟨ordP_cons_of_not (by omega), (hQ hm t).mpr (by omega), ?_⟩⟩
    rw [ordP_cons_of (S := t :: S) (t := t) ⟨by omega, by omega⟩, ordP_cons_of_not (by omega)]
    congr 1
    exact Pos.ext rfl hc1

/-- sec:static, the sentence after lem:static-sched, second half: every
sequence of distinct positions in which every position is preceded by all
positions below it is the order word of a schedule. -/
theorem Prog.HasLen.exists_ordP_eq (hQ : Q.HasLen len) {s : List (Pos len)} (hs : PSched s) :
    ∃ S ∈ Q.mem, ordP len S = s := by
  induction s with
  | nil => exact ⟨[], Q.nil_mem, rfl⟩
  | cons x s ih =>
    obtain ⟨S, hS, rfl⟩ := ih (psched_cons.mp hs).1
    obtain ⟨hm, h | ⟨-, hm', h⟩⟩ := hQ.step hS hs
    · exact ⟨_, hm, h⟩
    · exact ⟨_, hm', h⟩

/-- A schedule can be extended, without a change of its order word, by the
first steps of the threads of a finite set that have not started. -/
theorem Prog.HasLen.exists_started (hQ : Q.HasLen len) (T : Finset Tid) {S : Sched}
    (hS : S ∈ Q.mem) :
    ∃ S', S <:+ S' ∧ S' ∈ Q.mem ∧ ordP len S' = ordP len S ∧ ∀ t ∈ T, 0 < len t → t ∈ S' := by
  induction T using Finset.induction_on with
  | empty => exact ⟨S, List.suffix_refl _, hS, rfl, by simp⟩
  | insert a T _ ih =>
    obtain ⟨S', hs, hS', ho, hall⟩ := ih
    by_cases ha : 0 < len a ∧ a ∉ S'
    · have h0 : S'.count a = 0 := List.count_eq_zero.mpr ha.2
      refine ⟨a :: S', hs.trans (List.suffix_cons _ _), (hQ hS' a).mpr (by omega), ?_, ?_⟩
      · rw [ordP_cons_of_not (by omega), ho]
      · intro t ht hl
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hall t ht hl)
    · refine ⟨S', hs, hS', ho, fun t ht hl => ?_⟩
      rcases Finset.mem_insert.mp ht with rfl | ht
      · by_contra hn
        exact ha ⟨hl, hn⟩
      · exact hall t ht hl

/-- lem:static-sched, first half, with its converse: a schedule is complete
iff its order word contains every position and every thread of length `1`
(a thread whose only step is its start event) has taken its step. -/
theorem Prog.HasLen.complete_iff_ordP (hQ : Q.HasLen len) {S : Sched} :
    Q.Complete S ↔ S ∈ Q.mem ∧ Pct.Complete (ordP len S) ∧ ∀ t, len t = 1 → t ∈ S := by
  rw [hQ.complete_iff, complete_ordP_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    exact ⟨fun t _ => h t, fun t ht => List.count_pos_iff.mp (by have := h t; omega)⟩
  · rintro ⟨h2, h1⟩ t
    by_cases ht : 2 ≤ len t
    · exact h2 t ht
    · by_cases ht1 : len t = 1
      · have := List.count_pos_iff.mpr (h1 t ht1)
        omega
      · omega

/-- lem:static-sched, first half: the order word of a complete schedule
contains every position (with `psched_ordP`: it is a linear extension). -/
theorem Prog.HasLen.complete_ordP (hQ : Q.HasLen len) {S : Sched} (h : Q.Complete S) :
    Pct.Complete (ordP len S) := (hQ.complete_iff_ordP.mp h).2.1

/-- A schedule whose order word contains every position extends to a
complete schedule with the same order word, if finitely many threads have a
non-zero length. -/
theorem Prog.HasLen.exists_complete_extension (hQ : Q.HasLen len) (T : Finset Tid)
    (hT : ∀ t, 0 < len t → t ∈ T) {S : Sched} (hS : S ∈ Q.mem) (hc : Pct.Complete (ordP len S)) :
    ∃ S', S <:+ S' ∧ Q.Complete S' ∧ ordP len S' = ordP len S := by
  obtain ⟨S', hs, hS', ho, hall⟩ := hQ.exists_started T hS
  refine ⟨S', hs, hQ.complete_iff_ordP.mpr ⟨hS', by rw [ho]; exact hc, fun t ht => ?_⟩, ho⟩
  exact hall t (hT t (by omega)) (by omega)

/-- lem:static-sched, second half: every linear extension of the poset of
positions is the order word of a complete schedule. -/
theorem Prog.HasLen.exists_complete_ordP_eq (hQ : Q.HasLen len) (T : Finset Tid)
    (hT : ∀ t, 0 < len t → t ∈ T) {s : List (Pos len)} (hs : PSched s) (hc : Pct.Complete s) :
    ∃ S, Q.Complete S ∧ ordP len S = s := by
  obtain ⟨S, hS, rfl⟩ := hQ.exists_ordP_eq hs
  obtain ⟨S', -, hS', ho⟩ := hQ.exists_complete_extension T hT hS hc
  exact ⟨S', hS', ho⟩

end HasLen

/-! ### Directives on positions (lem:viol-order, thm:static, prop:sh-eq) -/

/-- `Before` is preserved and reflected by an injective renaming. -/
theorem before_map {X Y : Type} {f : X → Y} (hf : Function.Injective f) {s : List X}
    {x y : X} : Before (s.map f) (f x) (f y) ↔ Before s x y := by
  induction s with
  | nil => exact Iff.rfl
  | cons z s ih =>
    rw [List.map_cons, before_cons_iff, before_cons_iff, ih, hf.eq_iff,
      List.mem_map_of_injective hf]

/-- A directive on the poset of positions as a directive on the names of the
position labelling. -/
def PDir.toDirective {d : ℕ} (D : PDir (Pos len) d) : Directive (Tid × ℕ) d where
  A i := Pos.name '' D.A i
  b i := (D.b i).name
  b_inj := Pos.name_injective.comp D.b_inj

/-- A directive that p-guarantees a bug p-guarantees every bug that contains
the same complete schedules (def:pviolates). -/
theorem Directive.PGuarantees.mono {Q : Prog} {L : Type} {d : ℕ} {D : Directive L d}
    {E : Labelling Q L} {B₁ B : Set Sched} (g : D.PGuarantees E B₁)
    (h : ∀ S, Q.Complete S → S ∈ B₁ → S ∈ B) : D.PGuarantees E B :=
  ⟨g.cond1, fun S hS hnv => ⟨(g.cond2 S hS hnv).1, h S hS (g.cond2 S hS hnv).2⟩⟩

section Directives

variable {Q : Prog} {d : ℕ}

/-- The criterion of lem:viol-order on the order word `ord S` and on the
list of positions `ordP len S` is the same. -/
theorem Prog.HasLen.viol_ord_iff (hQ : Q.HasLen len) {S : Sched} (h : S ∈ Q.mem)
    (D : PDir (Pos len) d) : Viol (ord S) D.toDirective.toPDir ↔ Viol (ordP len S) D := by
  rw [← hQ.map_name_ordP h]
  have hf := Pos.name_injective (len := len)
  constructor
  · rintro ⟨i, hi, ⟨c, ⟨c', hc', rfl⟩, hne, hnb⟩ | ⟨j, hj, hnb⟩⟩
    · exact ⟨i, (List.mem_map_of_injective hf).mp hi, Or.inl ⟨c', hc',
        fun e => hne (congrArg _ e), fun hb => hnb ((before_map hf).mpr hb)⟩⟩
    · exact ⟨i, (List.mem_map_of_injective hf).mp hi, Or.inr ⟨j, hj,
        fun hb => hnb ((before_map hf).mpr hb)⟩⟩
  · rintro ⟨i, hi, ⟨c, hc, hne, hnb⟩ | ⟨j, hj, hnb⟩⟩
    · exact ⟨i, (List.mem_map_of_injective hf).mpr hi, Or.inl ⟨c.name, ⟨c, hc, rfl⟩,
        fun e => hne (hf e), fun hb => hnb ((before_map hf).mp hb)⟩⟩
    · exact ⟨i, (List.mem_map_of_injective hf).mpr hi, Or.inr ⟨j, hj,
        fun hb => hnb ((before_map hf).mp hb)⟩⟩

/-- lem:viol-order for a directive on positions: a schedule p-violates the
directive iff its list of positions violates it in the sense of
`Static.lean`. -/
theorem Prog.HasLen.pviolates_iff_viol (hQ : Q.HasLen len) {E : Labelling Q (Tid × ℕ)}
    (hE : E.IsPos) (D : PDir (Pos len) d) {S : Sched} (h : S ∈ Q.mem) :
    D.toDirective.PViolates E S ↔ Viol (ordP len S) D :=
  (hE.pviolates_iff_viol _ h).trans (hQ.viol_ord_iff h D)

/-- Condition 1 of def:pviolates on the schedules gives condition 1 on the
poset of positions. -/
theorem Prog.HasLen.cond1_of_pguarantees (hQ : Q.HasLen len) (T : Finset Tid)
    (hT : ∀ t, 0 < len t → t ∈ T) {E : Labelling Q (Tid × ℕ)} (hE : E.IsPos)
    {D : PDir (Pos len) d}
    (h : ∀ S, Q.Partial S → ¬ D.toDirective.PViolates E S →
      ∃ t, t :: S ∈ Q.mem ∧ ¬ D.toDirective.PViolates E (t :: S)) : Cond1 D := by
  intro s hs hv hc
  obtain ⟨S₀, hS₀, e₀⟩ := hQ.exists_ordP_eq hs
  obtain ⟨S, -, hS, ho, hall⟩ := hQ.exists_started T hS₀
  have e : ordP len S = s := ho.trans e₀
  subst e
  have hpart : Q.Partial S := by
    refine ⟨hS, ?_⟩
    by_contra hno
    exact hc (hQ.complete_ordP ⟨hS, fun t ht => hno ⟨t, ht⟩⟩)
  obtain ⟨t, ht, hnv⟩ := h S hpart (fun k => hv ((hQ.pviolates_iff_viol hE D hS).mp k))
  have hlt : S.count t < len t := (hQ hS t).mp ht
  have hpos : 1 ≤ S.count t :=
    List.count_pos_iff.mpr (hall t (hT t (by omega)) (by omega))
  have ho' := ordP_cons_of (len := len) (t := t) (S := S) ⟨hpos, hlt⟩
  refine ⟨⟨t, S.count t, hpos, hlt⟩, ?_, ?_⟩
  · rw [← ho']
    exact psched_ordP len (t :: S)
  · rw [← ho']
    exact fun hv' => hnv ((hQ.pviolates_iff_viol hE D ht).mpr hv')

/-- Condition 1 on the poset of positions gives condition 1 of def:pviolates
on the schedules. -/
theorem Prog.HasLen.pguarantees_cond1 (hQ : Q.HasLen len) {E : Labelling Q (Tid × ℕ)}
    (hE : E.IsPos) {D : PDir (Pos len) d} (h : Cond1 D) {S : Sched} (hp : Q.Partial S)
    (hnv : ¬ D.toDirective.PViolates E S) :
    ∃ t, t :: S ∈ Q.mem ∧ ¬ D.toDirective.PViolates E (t :: S) := by
  obtain ⟨hS, t₀, ht₀⟩ := hp
  have hv : ¬ Viol (ordP len S) D := fun k => hnv ((hQ.pviolates_iff_viol hE D hS).mpr k)
  by_cases hc : Pct.Complete (ordP len S)
  · refine ⟨t₀, ht₀, fun k => ?_⟩
    have hk := (hQ.pviolates_iff_viol hE D ht₀).mp k
    by_cases hstep : 1 ≤ S.count t₀ ∧ S.count t₀ < len t₀
    · have hps := psched_ordP len (t₀ :: S)
      rw [ordP_cons_of hstep] at hps
      exact (psched_cons.mp hps).2.1 (hc _)
    · rw [ordP_cons_of_not hstep] at hk
      exact hv hk
  · obtain ⟨x, hx, hxv⟩ := h _ (psched_ordP len S) hv hc
    obtain ⟨hm, ho | ⟨ho, -, -⟩⟩ := hQ.step hS hx
    · refine ⟨x.thr, hm, fun k => ?_⟩
      have hk := (hQ.pviolates_iff_viol hE D hm).mp k
      rw [ho] at hk
      exact hxv hk
    · refine ⟨x.thr, hm, fun k => ?_⟩
      have hk := (hQ.pviolates_iff_viol hE D hm).mp k
      rw [ho] at hk
      exact hv hk

/-- def:pviolates and sec:static: for a bug given by a set `B` of order
words, a directive on positions p-guarantees the bug on the schedules iff it
p-guarantees `B` on the poset of positions. -/
theorem Prog.HasLen.pguarantees_iff_pguar (hQ : Q.HasLen len) (T : Finset Tid)
    (hT : ∀ t, 0 < len t → t ∈ T) {E : Labelling Q (Tid × ℕ)} (hE : E.IsPos)
    (D : PDir (Pos len) d) (B : Set (List (Pos len))) :
    D.toDirective.PGuarantees E {S | ordP len S ∈ B} ↔ PGuar D B := by
  constructor
  · intro g
    refine ⟨hQ.cond1_of_pguarantees T hT hE g.cond1, fun s hs hc hv => ?_⟩
    obtain ⟨S, hS, rfl⟩ := hQ.exists_complete_ordP_eq T hT hs hc
    exact (g.cond2 S hS (fun k => hv ((hQ.pviolates_iff_viol hE D hS.1).mp k))).2
  · rintro ⟨c1, c2⟩
    refine ⟨fun S hp hnv => hQ.pguarantees_cond1 hE c1 hp hnv, fun S hS hnv => ?_⟩
    have hc := hQ.complete_ordP hS
    have hv : ¬ Viol (ordP len S) D := fun k => hnv ((hQ.pviolates_iff_viol hE D hS.1).mpr k)
    refine ⟨⟨hnv, fun i => ?_⟩, c2 _ (psched_ordP len S) hc hv⟩
    rw [hE.mem_names_iff_mem_ord hS.1, ← hQ.map_name_ordP hS.1]
    exact List.mem_map_of_mem (hc _)

/-- thm:static (1) on schedules, for a schedule bug `B`: if a directive on
positions p-guarantees `B`, then every complete schedule whose order word
strongly hits the targets is in `B`. -/
theorem Prog.HasLen.stronglyGuar_of_pguarantees (hQ : Q.HasLen len) (T : Finset Tid)
    (hT : ∀ t, 0 < len t → t ∈ T) {E : Labelling Q (Tid × ℕ)} (hE : E.IsPos)
    {D : PDir (Pos len) d} {B : Set Sched} (g : D.toDirective.PGuarantees E B) {S : Sched}
    (hS : Q.Complete S)
    (hit : StronglyHits (LinExt.ofSched (ordP len S) (psched_ordP len S) (hQ.complete_ordP hS))
      D.b) : S ∈ B := by
  have := Pos.finite T hT
  have hg : PGuar D {s | ∀ S, Q.Complete S → ordP len S = s → S ∈ B} := by
    refine ⟨hQ.cond1_of_pguarantees T hT hE g.cond1, fun s hs hc hv S hS e => ?_⟩
    subst e
    exact (g.cond2 S hS (fun k => hv ((hQ.pviolates_iff_viol hE D hS.1).mp k))).2
  exact stronglyGuar_of_pguar hg _ (psched_ordP len S) (hQ.complete_ordP hS) hit S hS rfl

/-- prop:sh-eq, direction `≥`, on schedules, for a schedule bug `B`: if
every complete schedule whose order word strongly hits the tuple is in `B`,
then some directive on positions of the same size p-guarantees `B`. -/
theorem Prog.HasLen.exists_pguarantees_of_stronglyGuar (hQ : Q.HasLen len) (T : Finset Tid)
    (hT : ∀ t, 0 < len t → t ∈ T) {E : Labelling Q (Tid × ℕ)} (hE : E.IsPos)
    {B : Set Sched} (x : Fin d → Pos len) (hx : Function.Injective x)
    (hB : ∀ S (hS : Q.Complete S),
      StronglyHits (LinExt.ofSched (ordP len S) (psched_ordP len S) (hQ.complete_ordP hS)) x →
        S ∈ B) :
    ∃ D : PDir (Pos len) d, D.toDirective.PGuarantees E B := by
  have := Pos.finite T hT
  obtain ⟨D, hD⟩ := exists_pguar_of_stronglyGuar
    (B := {s | ∀ S, Q.Complete S → ordP len S = s → S ∈ B}) x hx (by
      intro s hs hc hit S hS e
      subst e
      exact hB S hS hit)
  exact ⟨D, ((hQ.pguarantees_iff_pguar T hT hE D _).mpr hD).mono fun S hS h => h S hS rfl⟩

/-- prop:sh-eq, direction `≥`, on schedules, for a bug given by a set `B` of
order words. -/
theorem Prog.HasLen.exists_pguarantees_of_stronglyGuar_ord (hQ : Q.HasLen len)
    (T : Finset Tid) (hT : ∀ t, 0 < len t → t ∈ T) {E : Labelling Q (Tid × ℕ)}
    (hE : E.IsPos) {B : Set (List (Pos len))} (x : Fin d → Pos len)
    (hx : Function.Injective x)
    (hB : ∀ S (hS : Q.Complete S),
      StronglyHits (LinExt.ofSched (ordP len S) (psched_ordP len S) (hQ.complete_ordP hS)) x →
        ordP len S ∈ B) :
    ∃ D : PDir (Pos len) d, D.toDirective.PGuarantees E {S | ordP len S ∈ B} :=
  hQ.exists_pguarantees_of_stronglyGuar T hT hE x hx hB

/-- thm:static (2) on schedules, for a schedule bug `B` (def:hdep): if some
complete schedule hits the tuple and every complete schedule that hits it is
in `B`, then the directive of the tuple p-guarantees `B`. -/
theorem Prog.HasLen.pguarantees_chainDir (hQ : Q.HasLen len) (T : Finset Tid)
    (hT : ∀ t, 0 < len t → t ∈ T) {E : Labelling Q (Tid × ℕ)} (hE : E.IsPos)
    {B : Set Sched} (a : Fin (d + 1) → Pos len) (ha : Function.Injective a)
    (hadm : ∃ S, ∃ hS : Q.Complete S,
      Hits (LinExt.ofSched (ordP len S) (psched_ordP len S) (hQ.complete_ordP hS)) a)
    (hB : ∀ S (hS : Q.Complete S),
      Hits (LinExt.ofSched (ordP len S) (psched_ordP len S) (hQ.complete_ordP hS)) a →
        S ∈ B) :
    (chainDir a ha).toDirective.PGuarantees E B := by
  obtain ⟨S₀, hS₀, hit₀⟩ := hadm
  have hg : PGuar (chainDir a ha) {s | ∀ S, Q.Complete S → ordP len S = s → S ∈ B} := by
    refine pguar_chainDir a ha ⟨_, psched_ordP len S₀, hQ.complete_ordP hS₀, hit₀⟩ ?_
    intro s hs hc hit S hS e
    subst e
    exact hB S hS hit
  exact ((hQ.pguarantees_iff_pguar T hT hE _ _).mpr hg).mono fun S hS h => h S hS rfl

/-- thm:static (2) on schedules, for a bug given by a set `B` of order
words. -/
theorem Prog.HasLen.pguarantees_chainDir_ord (hQ : Q.HasLen len) (T : Finset Tid)
    (hT : ∀ t, 0 < len t → t ∈ T) {E : Labelling Q (Tid × ℕ)} (hE : E.IsPos)
    {B : Set (List (Pos len))} (a : Fin (d + 1) → Pos len) (ha : Function.Injective a)
    (hadm : ∃ S, ∃ hS : Q.Complete S,
      Hits (LinExt.ofSched (ordP len S) (psched_ordP len S) (hQ.complete_ordP hS)) a)
    (hB : ∀ S (hS : Q.Complete S),
      Hits (LinExt.ofSched (ordP len S) (psched_ordP len S) (hQ.complete_ordP hS)) a →
        ordP len S ∈ B) :
    (chainDir a ha).toDirective.PGuarantees E {S | ordP len S ∈ B} :=
  hQ.pguarantees_chainDir T hT hE a ha hadm hB

end Directives

/-! ### Static programs (def:static, lem:static-sched) -/

/-- Two labels are equal or are writes to the same location (def:static). -/
def Act.SameAccess {Loc Val : Type} (a a' : Act Loc Val) : Prop :=
  a = a' ∨ ∃ x v v', a = Act.write x v ∧ a' = Act.write x v'

namespace Program

variable {Loc Val : Type} [DecidableEq Loc] (P : Program Loc Val)

/-- def:static, with the executions of `P` given by its schedules: for
traces of `t` of the same length after two schedules, `P_t` is defined on
both or on none, and then the two labels are equal or are writes to the same
location. -/
def Static : Prop :=
  ∀ ⦃S S' : Sched⦄ (t : Tid), S ∈ P.sched.mem → S' ∈ P.sched.mem →
    (P.tr S t).length = (P.tr S' t).length →
      ((P.act t (P.tr S t)).isSome ↔ (P.act t (P.tr S' t)).isSome) ∧
        ∀ a a', P.act t (P.tr S t) = some a → P.act t (P.tr S' t) = some a' → a.SameAccess a'

variable {P}

/-- In a static program, whether a thread is enabled depends only on the
number of steps it has taken. -/
theorem Static.uniform (h : P.Static) : P.sched.Uniform := by
  intro S S' t hS hS' hc hm
  have hl : (P.tr S t).length = (P.tr S' t).length := by
    rw [P.length_tr hS, P.length_tr hS', hc]
  exact ⟨hS', ((h t hS hS' hl).1).mp hm.2⟩

/-- sec:static: in a bounded static program every thread `t` is enabled iff
it has taken fewer than `len_t` steps. -/
theorem Static.hasLen (h : P.Static) {k : ℕ} (hB : P.sched.Bounded k) :
    P.sched.HasLen P.sched.len := h.uniform.hasLen hB

/-- sec:static: if `P` is static then so is `P⁺`. -/
theorem Static.plus (h : P.Static) : P.plus.Static := by
  intro S S' t hS hS' hl
  obtain ⟨hT, hs⟩ := P.mem_sched_plus_iff.mp hS
  obtain ⟨hT', hs'⟩ := P.mem_sched_plus_iff.mp hS'
  rw [(P.run_plus hT).2 t, (P.run_plus hT').2 t] at hl ⊢
  by_cases hm : t ∈ S <;> by_cases hm' : t ∈ S'
  · rw [ite_eq_left hm, ite_eq_left hm'] at hl ⊢
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [plus_act_cons]
    exact h t hs hs' hl
  · rw [ite_eq_left hm, ite_eq_right hm'] at hl
    simp at hl
  · rw [ite_eq_right hm, ite_eq_left hm'] at hl
    simp at hl
  · rw [ite_eq_right hm, ite_eq_right hm']
    exact ⟨Iff.rfl, fun a a' e e' => Or.inl (Option.some.inj (e.symm.trans e'))⟩

variable (P)

/-- The lengths of the threads of `P⁺` from those of `P`: one more step for
every thread of `P` (def:start). -/
def plusLen (len : Tid → ℕ) (t : Tid) : ℕ := if t ∈ P.tids then len t + 1 else 0

omit [DecidableEq Loc] in
/-- Only the threads of `P` have a non-zero length in `P⁺`. -/
theorem mem_tids_of_plusLen_pos {len : Tid → ℕ} (t : Tid) (h : 0 < P.plusLen len t) :
    t ∈ P.tids := by
  by_contra hn
  rw [plusLen, ite_eq_right hn] at h
  exact Nat.lt_irrefl _ h

/-- def:start on schedule sets: if the threads of `P` have the lengths
`len`, then the threads of `P⁺` have the lengths `len + 1`. -/
theorem hasLen_plus {len : Tid → ℕ} (h : P.sched.HasLen len) :
    P.plus.sched.HasLen (P.plusLen len) := by
  intro S hS t
  obtain ⟨hT, hs⟩ := P.mem_sched_plus_iff.mp hS
  rw [P.mem_sched_plus_iff]
  unfold plusLen
  by_cases ht : t ∈ P.tids
  · rw [ite_eq_left ht]
    have hT' : ∀ u ∈ t :: S, u ∈ P.tids := fun u hu =>
      (List.mem_cons.mp hu).elim (fun e => e ▸ ht) (hT u)
    by_cases hm : t ∈ S
    · have hst : strip (t :: S) = t :: strip S := by rw [strip, ite_eq_left hm]
      have := List.count_pos_iff.mpr hm
      rw [hst, h hs t, count_strip]
      constructor
      · rintro ⟨-, k⟩
        omega
      · intro k
        exact ⟨hT', by omega⟩
    · have hst : strip (t :: S) = strip S := by rw [strip, ite_eq_right hm]
      rw [hst, List.count_eq_zero.mpr hm]
      exact ⟨fun _ => by omega, fun _ => ⟨hT', hs⟩⟩
  · rw [ite_eq_right ht]
    constructor
    · rintro ⟨k, -⟩
      exact absurd (k t List.mem_cons_self) ht
    · intro k
      omega

/-- sec:static: `len_t` for the threads of `P⁺`, for a bounded static `P`. -/
noncomputable def lenPlus : Tid → ℕ := P.plusLen P.sched.len

variable {P}

/-- sec:static: for a bounded static `P`, a thread of `P⁺` is enabled iff it
has taken fewer than `len_t` steps. -/
theorem Static.hasLen_plus (h : P.Static) {k : ℕ} (hB : P.sched.Bounded k) :
    P.plus.sched.HasLen P.lenPlus := P.hasLen_plus (h.hasLen hB)

/-- sec:static, the sentence after lem:static-sched, for programs: for a
bounded static `P` and every sequence `S` of thread identifiers, in
particular every schedule of `P⁺`, the order word of `S` is a partial
schedule of the poset of positions, and for a schedule of `P⁺` it is the
order word `ord S` of def:positions. -/
theorem Static.psched_ord (h : P.Static) {k : ℕ} (hB : P.sched.Bounded k) {S : Sched}
    (hS : S ∈ P.plus.sched.mem) :
    PSched (ordP P.lenPlus S) ∧ (ordP P.lenPlus S).map Pos.name = ord S :=
  ⟨psched_ordP _ S, (h.hasLen_plus hB).map_name_ordP hS⟩

/-- sec:static, the sentence after lem:static-sched, for programs: for a
bounded static `P`, every partial schedule of the poset of positions is the
order word of a schedule of `P⁺`. -/
theorem Static.exists_sched_ord_eq (h : P.Static) {k : ℕ} (hB : P.sched.Bounded k)
    {s : List (Pos P.lenPlus)} (hs : PSched s) :
    ∃ S ∈ P.plus.sched.mem, ordP P.lenPlus S = s ∧ ord S = s.map Pos.name := by
  obtain ⟨S, hS, rfl⟩ := (h.hasLen_plus hB).exists_ordP_eq hs
  exact ⟨S, hS, rfl, ((h.hasLen_plus hB).map_name_ordP hS).symm⟩

/-- lem:static-sched, first half, for programs: the order word of a complete
schedule of `P⁺` is a linear extension of the poset of positions. -/
theorem Static.complete_ord (h : P.Static) {k : ℕ} (hB : P.sched.Bounded k) {S : Sched}
    (hS : P.plus.sched.Complete S) :
    PSched (ordP P.lenPlus S) ∧ Pct.Complete (ordP P.lenPlus S) :=
  ⟨psched_ordP _ S, (h.hasLen_plus hB).complete_ordP hS⟩

/-- lem:static-sched, second half, for programs: every linear extension of
the poset of positions is the order word of a complete schedule of `P⁺`. -/
theorem Static.exists_complete_ord_eq (h : P.Static) {k : ℕ} (hB : P.sched.Bounded k)
    {s : List (Pos P.lenPlus)} (hs : PSched s) (hc : Pct.Complete s) :
    ∃ S, P.plus.sched.Complete S ∧ ordP P.lenPlus S = s :=
  (h.hasLen_plus hB).exists_complete_ordP_eq P.tids (P.mem_tids_of_plusLen_pos) hs hc

/-- The relation between complete schedules of `P⁺` and complete order
words, for a bounded static `P`: a schedule of `P⁺` is complete iff its
order word contains every position and every thread of `P` without events
has taken its start step. -/
theorem Static.complete_iff (h : P.Static) {k : ℕ} (hB : P.sched.Bounded k) {S : Sched} :
    P.plus.sched.Complete S ↔ S ∈ P.plus.sched.mem ∧ Pct.Complete (ordP P.lenPlus S) ∧
      ∀ t ∈ P.tids, P.sched.len t = 0 → t ∈ S := by
  rw [(h.hasLen_plus hB).complete_iff_ordP]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro k t ht h0
    exact k t (by rw [lenPlus, plusLen, ite_eq_left ht, h0])
  · intro k t h1
    have ht : t ∈ P.tids := P.mem_tids_of_plusLen_pos t (by rw [← lenPlus, h1]; exact Nat.one_pos)
    rw [lenPlus, plusLen, ite_eq_left ht] at h1
    exact k t ht (by omega)

/-- sec:static: for a bounded static `P`, `len_t` of `P⁺` is the largest
number of steps of `t` in a schedule of `P⁺`, and it is `len_t + 1` for the
`len_t` of `P` (def:start). -/
theorem Static.len_plus (h : P.Static) {k : ℕ} (hB : P.sched.Bounded k) :
    P.plus.sched.len = P.lenPlus := (h.hasLen_plus hB).len_eq

/-- def:positions for a bounded static `P`: `(t, i)` is a position iff some
schedule of `P⁺` emits it. -/
theorem Static.exists_mem_ord_iff (h : P.Static) {k : ℕ} (hB : P.sched.Bounded k) {t : Tid}
    {i : ℕ} : (∃ S ∈ P.plus.sched.mem, (t, i) ∈ ord S) ↔ 1 ≤ i ∧ i < P.lenPlus t :=
  (h.hasLen_plus hB).exists_mem_ord_iff

/-- There are finitely many positions `(t, i)` with `1 ≤ i < len_t`. -/
theorem finite_pos (P : Program Loc Val) : Finite (Pos P.lenPlus) :=
  Pos.finite P.tids P.mem_tids_of_plusLen_pos

/-- thm:static (1) for programs, for a schedule bug `B` of `P⁺`: if a
directive on positions with a position labelling p-guarantees `B`, then
every complete schedule of `P⁺` whose order word strongly hits the targets
is in `B`. -/
theorem Static.stronglyGuar_of_pguarantees (h : P.Static) {k : ℕ} (hB : P.sched.Bounded k)
    {E : Labelling P.plus.sched (Tid × ℕ)} (hE : E.IsPos) {d : ℕ}
    {D : PDir (Pos P.lenPlus) d} {B : Set Sched} (g : D.toDirective.PGuarantees E B)
    {S : Sched} (hS : P.plus.sched.Complete S)
    (hit : StronglyHits (LinExt.ofSched (ordP P.lenPlus S) (psched_ordP _ S)
      ((h.hasLen_plus hB).complete_ordP hS)) D.b) : S ∈ B :=
  (h.hasLen_plus hB).stronglyGuar_of_pguarantees P.tids P.mem_tids_of_plusLen_pos hE g hS hit

/-- thm:static (2) for programs, for a schedule bug `B` of `P⁺` (def:hdep):
if some complete schedule of `P⁺` hits the tuple and every complete schedule
that hits it is in `B`, then the directive of the tuple, with a position
labelling, p-guarantees `B`. -/
theorem Static.pguarantees_chainDir (h : P.Static) {k : ℕ} (hB : P.sched.Bounded k)
    {E : Labelling P.plus.sched (Tid × ℕ)} (hE : E.IsPos) {d : ℕ} {B : Set Sched}
    (a : Fin (d + 1) → Pos P.lenPlus) (ha : Function.Injective a)
    (hadm : ∃ S, ∃ hS : P.plus.sched.Complete S,
      Hits (LinExt.ofSched (ordP P.lenPlus S) (psched_ordP _ S)
        ((h.hasLen_plus hB).complete_ordP hS)) a)
    (hbug : ∀ S (hS : P.plus.sched.Complete S),
      Hits (LinExt.ofSched (ordP P.lenPlus S) (psched_ordP _ S)
        ((h.hasLen_plus hB).complete_ordP hS)) a → S ∈ B) :
    (chainDir a ha).toDirective.PGuarantees E B :=
  (h.hasLen_plus hB).pguarantees_chainDir P.tids P.mem_tids_of_plusLen_pos hE a ha hadm hbug

/-- prop:sh-eq, direction `≥`, for programs, for a schedule bug `B` of `P⁺`:
if every complete schedule of `P⁺` whose order word strongly hits the tuple
is in `B`, then some directive on positions of the same size, with a
position labelling, p-guarantees `B`. -/
theorem Static.exists_pguarantees_of_stronglyGuar (h : P.Static) {k : ℕ}
    (hB : P.sched.Bounded k) {E : Labelling P.plus.sched (Tid × ℕ)} (hE : E.IsPos) {d : ℕ}
    {B : Set Sched} (x : Fin d → Pos P.lenPlus) (hx : Function.Injective x)
    (hbug : ∀ S (hS : P.plus.sched.Complete S),
      StronglyHits (LinExt.ofSched (ordP P.lenPlus S) (psched_ordP _ S)
        ((h.hasLen_plus hB).complete_ordP hS)) x → S ∈ B) :
    ∃ D : PDir (Pos P.lenPlus) d, D.toDirective.PGuarantees E B :=
  (h.hasLen_plus hB).exists_pguarantees_of_stronglyGuar P.tids P.mem_tids_of_plusLen_pos hE
    x hx hbug

/-- def:pviolates and sec:static for programs, for a bug given by a set `B`
of order words: a directive on positions with a position labelling
p-guarantees the bug on the schedules of `P⁺` iff it p-guarantees `B` on the
poset of positions. -/
theorem Static.pguarantees_iff_pguar (h : P.Static) {k : ℕ} (hB : P.sched.Bounded k)
    {E : Labelling P.plus.sched (Tid × ℕ)} (hE : E.IsPos) {d : ℕ}
    (D : PDir (Pos P.lenPlus) d) (B : Set (List (Pos P.lenPlus))) :
    D.toDirective.PGuarantees E {S | ordP P.lenPlus S ∈ B} ↔ PGuar D B :=
  (h.hasLen_plus hB).pguarantees_iff_pguar P.tids P.mem_tids_of_plusLen_pos hE D B

end Program

end Pct
