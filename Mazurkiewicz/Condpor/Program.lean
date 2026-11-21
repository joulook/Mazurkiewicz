import Mazurkiewicz.Condpor.Ops
import Mathlib.Data.Finset.Max
import Mathlib.Order.Preorder.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Programs with symbolic actions and their executions

`Trust/Program.lean` for the six labels of `Condpor/Event.lean`. A program
gives, for every thread, the next action as a function of the values the
thread's events have returned so far (its trace). A read returns the value
read; a constraint evaluation returns `1` or `0`, its outcome; the other
actions return nothing. So the control flow of a thread after an evaluation
of `φ` depends on the outcome, as after `if (φ)` in the paper's programs, and
a thread has exactly one next action whatever outcome an evaluation will get.

`stop`: a thread performs no action after `block` or `error`. For `block`
this is the paper's "`next_P` returns an event from a thread that is not
blocked or finished"; for `error` it is a convention of this formalisation
(Algorithm 1 exits at an error, so the paper says nothing about what follows).
A graph in which every thread is finished, blocked or stopped by an error is
full.

* `Exec P G`: `G` is an execution of `P`.
* `avail P G`: the next events of the threads that have one.
* `IsNext P G e`: `e` is the `<next`-least available event. `<next` is the
  lexicographic order on (thread, index, label).
* `Full P G`: no available event.

The examples of `Trust/Program.lean` are not copied; the examples of this
development are in the files of the algorithm.
-/

namespace Condpor

/-- A program: finitely many threads, the next action of each thread as a
function of its trace, and the initial memory. A thread outside `threads`
has no first action, hence no event in any execution. -/
structure Program where
  /-- the threads -/
  threads : List Tid
  /-- no thread is listed twice -/
  threads_nodup : threads.Nodup
  /-- the next action of a thread after a trace, `none` if it has terminated -/
  step : Tid → List (Option Val) → Option Act
  /-- the initial memory -/
  mem : Loc → Val
  /-- threads outside the list do nothing -/
  step_none : ∀ t, t ∉ threads → step t [] = none
  /-- no action after `block` or `error` -/
  stop : ∀ t u, (step t u = some .block ∨ step t u = some .error) → step t (u ++ [none]) = none

namespace Program

variable (P : Program)

/-- No thread performs more than `n` events (`induction-popl`, def:program). -/
def Bounded (n : ℕ) : Prop := ∀ t u, n ≤ u.length → P.step t u = none

/-- `G` is an execution of `P`: it has the initial memory of `P`, and every
event carries the action that its thread performs after the values returned
by the earlier events of the thread (`induction-popl`, def:exec). -/
def Exec (G : Graph) : Prop :=
  G.mem = P.mem ∧ ∀ e ∈ G.events, P.step e.tid (G.traceBefore e.tid e.idx) = some e.act

/-- The next event of thread `t` in `G`, if the thread has not terminated. -/
noncomputable def nextOf (G : Graph) (t : Tid) : Option TEv :=
  (P.step t (G.trace t)).map (fun a => ⟨t, G.cnt t, a⟩)

/-- The available events: the next events of the threads that have one
(paper, Def. A.8; `dpor.tex`, def:avail). -/
noncomputable def avail (G : Graph) : List TEv := P.threads.filterMap (P.nextOf G)

/-- A code of a label: its kind and its arguments. -/
def _root_.Condpor.Act.code : Act → ℕ × ℕ × ℕ
  | .read x => (0, x, 0)
  | .write x v => (1, x, v)
  | .gen s => (2, s, 0)
  | .cons φ => (3, φ, 0)
  | .block => (4, 0, 0)
  | .error => (5, 0, 0)

theorem _root_.Condpor.Act.code_injective {a b : Act} (h : a.code = b.code) : a = b := by
  cases a <;> cases b <;> simp_all [Act.code]

/-- A strict total order on labels, used only to make `<next` total: the
lexicographic order on the codes. -/
def actLt (a b : Act) : Prop :=
  a.code.1 < b.code.1 ∨ (a.code.1 = b.code.1 ∧
    (a.code.2.1 < b.code.2.1 ∨ (a.code.2.1 = b.code.2.1 ∧ a.code.2.2 < b.code.2.2)))

/-- The program order on thread events, without reference to a graph (the
`po` of the paper's Section 3.1, on thread events). -/
def poT (e e' : TEv) : Prop := e.tid = e'.tid ∧ e.idx < e'.idx

/-- `<next`: the lexicographic order on (thread, index, label). It is a strict
total order on thread events and contains the program order (paper, Def. A.7,
for programs without RMW). Two events of one graph, or an event of a graph and
an available event, never agree on thread and index, so the label is compared
only between events that cannot occur together. -/
def nextLt (e e' : TEv) : Prop :=
  e.tid < e'.tid ∨ (e.tid = e'.tid ∧ e.idx < e'.idx) ∨
    (e.tid = e'.tid ∧ e.idx = e'.idx ∧ actLt e.act e'.act)

/-- `<next` on events: `init` is first (Def. A.13 takes the `<next`-maximum
over events of a graph, which include `init`). -/
def nextLtEv : Ev → Ev → Prop
  | .init, .th _ => True
  | .th e, .th e' => nextLt e e'
  | _, .init => False

/-- `e` is the next event of `G`: the `<next`-least available event
(paper, Def. A.9). -/
def IsNext (G : Graph) (e : TEv) : Prop :=
  e ∈ P.avail G ∧ ∀ e' ∈ P.avail G, e' ≠ e → nextLt e e'

/-- `G` is full: no event is available (paper, Def. A.10). -/
def Full (G : Graph) : Prop := P.avail G = []

/-! ### Statements -/

variable {P}

theorem mem_avail_iff {G : Graph} {e : TEv} :
    e ∈ P.avail G ↔
      e.tid ∈ P.threads ∧ e.idx = G.cnt e.tid ∧ P.step e.tid (G.trace e.tid) = some e.act := by
  simp only [avail, nextOf, List.mem_filterMap, Option.map_eq_some_iff]
  constructor
  · rintro ⟨t, ht, a, ha, rfl⟩
    exact ⟨ht, rfl, ha⟩
  · rintro ⟨ht, hi, hs⟩
    refine ⟨e.tid, ht, e.act, hs, ?_⟩
    cases e
    simp_all

/-- An available event is not in the graph. -/
theorem not_mem_of_mem_avail {G : Graph} (hG : G.Wf) {e : TEv} (he : e ∈ P.avail G) :
    e ∉ G.events := by
  exact hG.not_mem_of_idx_eq_cnt (mem_avail_iff.mp he).2.1

/-- `Full`, unfolded over the listed threads. -/
theorem full_iff {G : Graph} : P.Full G ↔ ∀ t ∈ P.threads, P.step t (G.trace t) = none := by
  simp [Full, avail, nextOf, List.filterMap_eq_nil_iff]

theorem actLt_irrefl (a : Act) : ¬ actLt a a := by
  unfold actLt
  omega

theorem actLt_trans {a b c : Act} (hab : actLt a b) (hbc : actLt b c) : actLt a c := by
  unfold actLt at *
  omega

theorem actLt_total {a b : Act} (h : a ≠ b) : actLt a b ∨ actLt b a := by
  have hne : a.code ≠ b.code := fun hc => h (Act.code_injective hc)
  have : ¬ (a.code.1 = b.code.1 ∧ a.code.2.1 = b.code.2.1 ∧ a.code.2.2 = b.code.2.2) := by
    rintro ⟨h1, h2, h3⟩
    exact hne (Prod.ext h1 (Prod.ext h2 h3))
  unfold actLt
  omega

/-- `po ⊆ <next` (Def. A.7). -/
theorem nextLt_of_poT {e e' : TEv} (h : poT e e') : nextLt e e' :=
  Or.inr (Or.inl h)

theorem nextLt_irrefl (e : TEv) : ¬ nextLt e e := by
  rintro (h | ⟨_, h⟩ | ⟨_, _, h⟩)
  · exact Nat.lt_irrefl _ h
  · exact Nat.lt_irrefl _ h
  · exact actLt_irrefl _ h

theorem nextLt_trans {a b c : TEv} (hab : nextLt a b) (hbc : nextLt b c) : nextLt a c := by
  unfold nextLt at *
  rcases hab with h1 | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ <;> rcases hbc with k1 | ⟨k1, k2⟩ | ⟨k1, k2, k3⟩
  · exact Or.inl (Nat.lt_trans h1 k1)
  · exact Or.inl (k1 ▸ h1)
  · exact Or.inl (k1 ▸ h1)
  · exact Or.inl (h1 ▸ k1)
  · exact Or.inr (Or.inl ⟨h1.trans k1, Nat.lt_trans h2 k2⟩)
  · exact Or.inr (Or.inl ⟨h1.trans k1, k2 ▸ h2⟩)
  · exact Or.inl (h1 ▸ k1)
  · exact Or.inr (Or.inl ⟨h1.trans k1, h2 ▸ k2⟩)
  · exact Or.inr (Or.inr ⟨h1.trans k1, h2.trans k2, actLt_trans h3 k3⟩)

/-- `<next` is total (Def. A.7). -/
theorem nextLt_total {e e' : TEv} (h : e ≠ e') : nextLt e e' ∨ nextLt e' e := by
  unfold nextLt
  rcases Nat.lt_trichotomy e.tid e'.tid with h1 | h1 | h1
  · exact Or.inl (Or.inl h1)
  · rcases Nat.lt_trichotomy e.idx e'.idx with h2 | h2 | h2
    · exact Or.inl (Or.inr (Or.inl ⟨h1, h2⟩))
    · have hact : e.act ≠ e'.act := by
        intro h3
        apply h
        cases e; cases e'; simp_all
      rcases actLt_total hact with h3 | h3
      · exact Or.inl (Or.inr (Or.inr ⟨h1, h2, h3⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h1.symm, h2.symm, h3⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨h1.symm, h2⟩))
  · exact Or.inr (Or.inl h1)

/-- An available event has the next index of its thread. -/
theorem idx_eq_of_mem_avail {G : Graph} {e : TEv} (he : e ∈ P.avail G) :
    e.idx = G.cnt e.tid := by
  exact (mem_avail_iff.mp he).2.1

/-- There is at most one available event per thread. -/
theorem avail_tid_inj {G : Graph} {e e' : TEv} (he : e ∈ P.avail G) (he' : e' ∈ P.avail G)
    (h : e.tid = e'.tid) : e = e' := by
  obtain ⟨-, hi, hs⟩ := mem_avail_iff.mp he
  obtain ⟨-, hi', hs'⟩ := mem_avail_iff.mp he'
  cases e with
  | mk t i a =>
    cases e' with
    | mk t' i' a' =>
      simp only at h hi hs hi' hs'
      subst h
      rw [hs] at hs'
      rw [hi, hi', Option.some.inj hs']

/-- The available events depend only on the traces of the threads. -/
theorem avail_congr {G G' : Graph} (h : ∀ t, G.trace t = G'.trace t) :
    P.avail G = P.avail G' := by
  have hc : ∀ t, G.cnt t = G'.cnt t := fun t => by
    rw [← Graph.trace_length, ← Graph.trace_length, h t]
  unfold avail
  congr 1
  funext t
  simp [nextOf, h t, hc t]

/-- Every non-full graph has exactly one next event. -/
theorem exists_unique_isNext {G : Graph} (h : ¬ P.Full G) : ∃! e, P.IsNext G e := by
  have hne : (P.avail G).toFinset.Nonempty := by
    rw [List.toFinset_nonempty_iff]
    exact h
  obtain ⟨e, he, hmin⟩ := (P.avail G).toFinset.exists_min_image TEv.tid hne
  have he' : e ∈ P.avail G := List.mem_toFinset.mp he
  refine ⟨e, ⟨he', ?_⟩, ?_⟩
  · intro e' hav hne'
    have hle := hmin e' (List.mem_toFinset.mpr hav)
    rcases Nat.lt_or_ge e.tid e'.tid with hlt | hge
    · exact Or.inl hlt
    · exact absurd (avail_tid_inj hav he' (Nat.le_antisymm hge hle)) hne'
  · intro e2 h2
    by_contra hne'
    have h12 := h2.2 e he' (fun h => hne' h.symm)
    have h21 : nextLt e e2 := by
      have hle := hmin e2 (List.mem_toFinset.mpr h2.1)
      rcases Nat.lt_or_ge e.tid e2.tid with hlt | hge
      · exact Or.inl hlt
      · exact absurd (avail_tid_inj h2.1 he' (Nat.le_antisymm hge hle)) hne'
    exact nextLt_irrefl e (nextLt_trans h21 h12)

/-- The initial graph is an execution. -/
theorem exec_init (P : Program) : P.Exec (Graph.init P.mem) := by
  exact ⟨rfl, by simp [Graph.init]⟩

/-- The events of an execution belong to threads of the program. -/
theorem Exec.tid_mem {G : Graph} (hG : G.Wf) (h : P.Exec G) {e : TEv} (he : e ∈ G.events) :
    e.tid ∈ P.threads := by
  obtain ⟨e0, he0, ht0, hi0⟩ : ∃ e0 ∈ G.events, e0.tid = e.tid ∧ e0.idx = 0 := by
    by_cases hi : e.idx = 0
    · exact ⟨e, he, rfl, hi⟩
    · exact hG.idx_contig e he 0 (Nat.pos_of_ne_zero hi)
  have hs := h.2 e0 he0
  rw [hi0] at hs
  have h0 : G.traceBefore e0.tid 0 = [] := by simp [Graph.traceBefore]
  rw [h0, ht0] at hs
  by_contra hne
  rw [P.step_none e.tid hne] at hs
  cases hs

/-- Adding an available read with a source gives an execution. -/
theorem Exec.addRead {G : Graph} (hG : G.Wf) (h : P.Exec G) {e : TEv} {x : Loc} {w : Ev}
    (he : e ∈ P.avail G) (hact : e.act = .read x) (hw : G.IsWriteTo x w) :
    P.Exec (G.addRead e w) := by
  obtain ⟨-, hidx, hs⟩ := mem_avail_iff.mp he
  refine ⟨h.1, fun q hq => ?_⟩
  rw [Graph.traceBefore_addRead hG hidx hact hw hq]
  rcases Finset.mem_insert.mp hq with rfl | hq'
  · rw [hidx]
    exact hs
  · exact h.2 q hq'

/-- Adding an available write gives an execution. -/
theorem Exec.addWrite {G : Graph} (hG : G.Wf) (h : P.Exec G) {e : TEv} {wp : Ev}
    (he : e ∈ P.avail G) (hact : e.IsWrite) (hwp : G.IsWriteTo e.loc wp) :
    P.Exec (G.addWrite e wp) := by
  obtain ⟨-, hidx, hs⟩ := mem_avail_iff.mp he
  refine ⟨h.1, fun q hq => ?_⟩
  rw [Graph.traceBefore_addWrite hG hidx hact hwp hq]
  rcases Finset.mem_insert.mp hq with rfl | hq'
  · rw [hidx]
    exact hs
  · exact h.2 q hq'

/-- Adding an available event that is neither a read nor a write gives an
execution. -/
theorem Exec.addLoc {G : Graph} (hG : G.Wf) (h : P.Exec G) {e : TEv} {o : Option Bool}
    (he : e ∈ P.avail G) (hact : e.IsLocal) (ho : o.isSome ↔ e.IsCons) :
    P.Exec (G.addLoc e o) := by
  obtain ⟨-, hidx, hs⟩ := mem_avail_iff.mp he
  refine ⟨h.1, fun q hq => ?_⟩
  rw [Graph.traceBefore_addLoc hG hidx hact ho hq]
  rcases Finset.mem_insert.mp hq with rfl | hq'
  · rw [hidx]
    exact hs
  · exact h.2 q hq'

/-- A thread whose last event is `block` or `error` has no next event. -/
theorem Exec.no_next_of_stop {G : Graph} (hG : G.Wf) (h : P.Exec G) {e : TEv}
    (he : e ∈ G.events) (hlast : e.idx + 1 = G.cnt e.tid)
    (hact : e.act = .block ∨ e.act = .error) : P.step e.tid (G.trace e.tid) = none := by
  have hs := h.2 e he
  have hret : G.ret e = none := by
    unfold Graph.ret
    rcases hact with h1 | h1 <;> rw [h1]
  have htr : G.trace e.tid = G.traceBefore e.tid e.idx ++ [none] := by
    unfold Graph.trace
    rw [← hlast, Graph.traceBefore_succ, hG.evAt_eq_some he]
    simp [hret]
  rw [htr]
  refine P.stop _ _ ?_
  rcases hact with h1 | h1
  · exact Or.inl (h1 ▸ hs)
  · exact Or.inr (h1 ▸ hs)

/-- A prefix of an execution is an execution (`dpor.tex`, lem:budget(3)). -/
theorem Exec.of_isPrefixOf {G G' : Graph} (hG : G.Wf) (h : P.Exec G) (hp : G'.IsPrefixOf G) :
    P.Exec G' := by
  obtain ⟨s, hs, rfl⟩ := hp
  refine ⟨h.1, fun e he => ?_⟩
  rw [Graph.traceBefore_restrict hG hs he]
  exact h.2 e (Finset.mem_inter.mp he).1

/-- For a well-formed execution, `Full` is the definition of `induction-popl`
(def:exec): the program of every thread is undefined at its trace
(`dpor.tex`, lem:built(3)). -/
theorem Exec.full_iff {G : Graph} (hG : G.Wf) (h : P.Exec G) :
    P.Full G ↔ ∀ t, P.step t (G.trace t) = none := by
  rw [Program.full_iff]
  constructor
  · intro hf t
    by_cases ht : t ∈ P.threads
    · exact hf t ht
    · have hc : G.cnt t = 0 := by
        unfold Graph.cnt
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e he hte
        exact ht (hte ▸ h.tid_mem hG he)
      have h0 : G.trace t = [] := by simp [Graph.trace, Graph.traceBefore, hc]
      rw [h0]
      exact P.step_none t ht
  · intro hf t _
    exact hf t

/-- Being an execution is transported along a graph with fewer events and the
same traces before its events. No well-formedness is assumed, so this applies
to the intermediate graphs of a revisit. -/
theorem Exec.of_traceBefore_eq {G G' : Graph} (h : P.Exec G) (hm : G'.mem = G.mem)
    (hs : G'.events ⊆ G.events)
    (ht : ∀ e ∈ G'.events, G'.traceBefore e.tid e.idx = G.traceBefore e.tid e.idx) :
    P.Exec G' := by
  refine ⟨hm.trans h.1, fun e he => ?_⟩
  rw [ht e he]
  exact h.2 e (hs he)

/-- The restriction of a revisit is an execution: the kept set is closed under
program order and keeps the sources of the kept reads, except possibly the
source of `r`, and no kept event is after `r` in its thread. -/
theorem Exec.restrict_except {G : Graph} (hG : G.Wf) (h : P.Exec G) {s : Finset TEv} {r : TEv}
    (hpo : Maz.PrefixClosed G.po (Graph.evSet (G.events ∩ s)))
    (hrf : ∀ q ∈ G.events ∩ s, q ≠ r → ∀ w, G.rf q = some w → w ∈ Graph.evSet s)
    (hlast : ∀ q ∈ G.events ∩ s, q.tid = r.tid → q.idx ≤ r.idx) :
    P.Exec (G.restrict s) := by
  refine h.of_traceBefore_eq rfl Finset.inter_subset_left (fun e he => ?_)
  refine Graph.traceBefore_restrict_of_sources hG hpo he ?_
  intro q hq htid hidx w hw
  have he' := (Finset.mem_inter.mp he).1
  have hpo' : G.po (.th q) (.th e) := ⟨hq, he', htid, hidx⟩
  have hqs : q ∈ G.events ∩ s := hpo hpo' he
  have hne : q ≠ r := by
    rintro rfl
    have := hlast e he htid.symm
    omega
  exact hrf q hqs hne w hw

/-- Receptiveness (Coq: `p_sem_RF`): changing the source of `r` keeps an
execution when no event of the thread of `r` is after `r`. -/
theorem Exec.setRF {G : Graph} {r : TEv} (h : P.Exec G) {w : Ev}
    (hlast : ∀ q ∈ G.events, q.tid = r.tid → q.idx ≤ r.idx) :
    P.Exec (G.setRF r w) := by
  refine h.of_traceBefore_eq rfl (Finset.Subset.refl _) (fun e he => ?_)
  unfold Graph.traceBefore
  apply List.map_congr_left
  intro j hj
  have hj' : j < e.idx := List.mem_range.mp hj
  have hev : (G.setRF r w).evAt e.tid j = G.evAt e.tid j := rfl
  rw [hev]
  cases hq : G.evAt e.tid j with
  | none => rfl
  | some q =>
    obtain ⟨hqm, hqt, hqi⟩ := Graph.evAt_eq_some_iff_spec hq
    have hne : q ≠ r := by
      rintro rfl
      have := hlast e he hqt.symm
      omega
    exact G.ret_setRF_of_ne hne

/-- In an execution of a program bounded by `n`, no thread has more than `n`
events. -/
theorem Exec.cnt_le {G : Graph} (hG : G.Wf) (h : P.Exec G) {n : ℕ} (hn : P.Bounded n)
    (t : Tid) : G.cnt t ≤ n := by
  by_contra hlt
  have hlt' : n < G.cnt t := Nat.lt_of_not_le hlt
  obtain ⟨e, he, ht, hi⟩ := (hG.exists_idx_iff t n).mpr hlt'
  have hs := h.2 e he
  rw [hn e.tid _ (by rw [Graph.traceBefore_length, hi])] at hs
  cases hs

/-- The size bound that replaces Coq's `p_sem_finite`. -/
theorem Exec.card_le {G : Graph} (hG : G.Wf) (h : P.Exec G) {n : ℕ} (hn : P.Bounded n) :
    G.events.card ≤ n * P.threads.length := by
  have hsub : G.events ⊆
      P.threads.toFinset.biUnion (fun t => G.events.filter (fun e => e.tid = t)) := by
    intro e he
    simp only [Finset.mem_biUnion, List.mem_toFinset, Finset.mem_filter]
    exact ⟨e.tid, h.tid_mem hG he, he, rfl⟩
  calc G.events.card
      ≤ (P.threads.toFinset.biUnion (fun t => G.events.filter (fun e => e.tid = t))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ t ∈ P.threads.toFinset, (G.events.filter (fun e => e.tid = t)).card :=
        Finset.card_biUnion_le
    _ ≤ P.threads.toFinset.card • n :=
        Finset.sum_le_card_nsmul _ _ _ (fun t _ => h.cnt_le hG hn t)
    _ ≤ n * P.threads.length := by
        rw [nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
        exact Nat.mul_le_mul_left n (List.toFinset_card_le _)

/-! ### Built graphs (`dpor.tex`, def:avail and lem:built) -/

/-- `G` is built for `P`: obtained from the initial graph by adding one
available event at a time, each time as an extension of the previous graph
(`dpor.tex`, def:avail). The premise `G'.Wf` states what the TeX definition
has by speaking of graphs; the new event is not in the old graph
(`Built.fresh`), so `insert` is the disjoint union of the TeX definition. -/
inductive Built (P : Program) : Graph → Prop
  | init : Built P (Graph.init P.mem)
  | step {G G' : Graph} {e : TEv} : Built P G → G'.Wf → e ∈ P.avail G →
      G'.events = insert e G.events → G = G'.restrict G.events → Built P G'

/-- If `G` is the restriction of `G'` to the events of `G`, the reads of `G`
have the same source in `G'`. -/
theorem rf_of_restrict_eq {G G' : Graph} (hG : G.Wf) (hG' : G'.Wf)
    (hres : G = G'.restrict G.events) {q : TEv} (hq : q ∈ G.events) {w : Ev}
    (h : G'.rf q = some w) : G.rf q = some w ∧ w ∈ Graph.evSet G.events := by
  have hr : q.IsRead := by
    by_contra hn
    rw [hG'.rf_none q (Or.inr hn)] at h
    cases h
  have hact := TEv.IsRead.exists_act hr
  · obtain ⟨w0, hw0, -⟩ := hG.rf_read q hq _ hact
    have h1 : (G'.restrict G.events).rf q = some w0 := by
      rw [← hres]
      exact hw0
    obtain ⟨h2, -, h3⟩ := G'.restrict_rf_eq_some h1
    rw [h] at h2
    cases h2
    exact ⟨hw0, h3⟩

/-- lem:built(1): a built graph is a well-formed execution. -/
theorem Built.exec {G : Graph} (h : P.Built G) : G.Wf ∧ P.Exec G := by
  induction h with
  | init => exact ⟨Graph.init_wf _, exec_init P⟩
  | @step G G' e hB hG' he hev hres ih =>
    obtain ⟨hG, hE⟩ := ih
    refine ⟨hG', ?_⟩
    obtain ⟨-, hidx, hstep⟩ := mem_avail_iff.mp he
    have hm : G.mem = G'.mem := by
      have := congrArg Graph.mem hres
      exact this
    have hcnt' : ∀ t, G.cnt t ≤ G'.cnt t := by
      intro t
      unfold Graph.cnt
      rw [hev]
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    have key : ∀ t i, i ≤ G.cnt t → G'.traceBefore t i = G.traceBefore t i := by
      intro t i hi
      have keep : ∀ q ∈ G'.events, q.tid = t → q.idx < i → q ∈ G.events := by
        intro q hq ht hqi
        rw [hev] at hq
        rcases Finset.mem_insert.mp hq with hqe | hq'
        · rw [hqe] at ht hqi
          rw [ht] at hidx
          omega
        · exact hq'
      have src : ∀ q ∈ G'.events, q.tid = t → q.idx < i →
          ∀ w, G'.rf q = some w → w ∈ Graph.evSet G.events := by
        intro q hq ht hqi w hw
        exact (rf_of_restrict_eq hG hG' hres (keep q hq ht hqi) hw).2
      have h1 := Graph.traceBefore_restrict_of_keep hG' (le_trans hi (hcnt' t)) keep src
      rw [← hres] at h1
      exact h1.symm
    refine ⟨hm.symm.trans hE.1, fun q hq => ?_⟩
    rw [hev] at hq
    rcases Finset.mem_insert.mp hq with rfl | hq'
    · rw [key _ _ (le_of_eq hidx), hidx]
      exact hstep
    · rw [key _ _ (le_of_lt (hG.idx_lt_cnt hq'))]
      exact hE.2 q hq'

/-- In a step of `Built`, the added event is new. -/
theorem Built.fresh {G : Graph} (h : P.Built G) {e : TEv} (he : e ∈ P.avail G) :
    e ∉ G.events := by
  exact not_mem_of_mem_avail h.exec.1 he

/-- A built graph has no causality cycle. -/
theorem Built.acyclic {G : Graph} (h : P.Built G) : Maz.Acyclic G.porfStep := by
  induction h with
  | init =>
    intro a ha
    obtain ⟨c, hc⟩ := Maz.exists_first_of_transGen ha
    rcases hc with hc | ⟨q, -, hq, -⟩
    · cases a <;> cases c <;> simp [Graph.po, Graph.init] at hc
    · simp [Graph.init] at hq
  | @step G G' e hB hG' he hev hres ih =>
    obtain ⟨hG, -⟩ := hB.exec
    have hfresh := not_mem_of_mem_avail hG he
    obtain ⟨-, hidx, -⟩ := mem_avail_iff.mp he
    refine Maz.Acyclic.of_sink (e := Ev.th e) ih ?_ ?_
    · intro a b hab
      cases b with
      | init => exact absurd hab (G'.not_porfStep_init a)
      | th q =>
        by_cases hqe : q = e
        · exact Or.inr (congrArg Ev.th hqe)
        · left
          rcases hab with hpo | ⟨q0, hq0, hq0m, hrf⟩
          · cases a with
            | init =>
              have hqm : q ∈ G'.events := hpo
              rw [hev] at hqm
              exact Or.inl ((Finset.mem_insert.mp hqm).resolve_left hqe)
            | th q' =>
              obtain ⟨h1, h2, h3, h4⟩ := hpo
              rw [hev] at h1 h2
              have hq : q ∈ G.events := (Finset.mem_insert.mp h2).resolve_left hqe
              have hq' : q' ∈ G.events := by
                rcases Finset.mem_insert.mp h1 with hq'e | hq'
                · have hlt := hG.idx_lt_cnt hq
                  rw [hq'e] at h3 h4
                  rw [← h3] at hlt
                  omega
                · exact hq'
              exact Or.inl ⟨hq', hq, h3, h4⟩
          · have hq0' : q0 = q := (Ev.th.inj hq0).symm
            rw [hq0'] at hq0m hrf
            rw [hev] at hq0m
            have hq : q ∈ G.events := (Finset.mem_insert.mp hq0m).resolve_left hqe
            exact Or.inr ⟨q, rfl, hq, (rf_of_restrict_eq hG hG' hres hq hrf).1⟩
    · intro b hb
      cases b with
      | init => exact G'.not_porfStep_init _ hb
      | th q =>
        rcases hb with hpo | ⟨q0, hq0, hq0m, hrf⟩
        · obtain ⟨-, h2, h3, h4⟩ := hpo
          rw [hev] at h2
          rcases Finset.mem_insert.mp h2 with hqe | hq
          · rw [hqe] at h4
            exact Nat.lt_irrefl _ h4
          · have hlt := hG.idx_lt_cnt hq
            rw [← h3] at hlt
            omega
        · have hq0' : q0 = q := (Ev.th.inj hq0).symm
          rw [hq0'] at hq0m hrf
          rw [hev] at hq0m
          rcases Finset.mem_insert.mp hq0m with hqe | hq
          · rw [hqe] at hrf
            have hem := (hG'.rf_source_mem hrf).1
            have hr : e.IsRead := by
              by_contra hn
              rw [hG'.rf_none e (Or.inr hn)] at hrf
              cases hrf
            have hact := TEv.IsRead.exists_act hr
            obtain ⟨w', hw', hw''⟩ := hG'.rf_read e hem _ hact
            rw [hrf] at hw'
            cases hw'
            obtain ⟨-, v, hv⟩ := hw''
            rw [hact] at hv
            cases hv
          · exact hfresh (rf_of_restrict_eq hG hG' hres hq hrf).2

/-- lem:built(2): a well-formed execution without a causality cycle is built. -/
theorem Exec.built {G : Graph} (hG : G.Wf) (h : P.Exec G) (hac : Maz.Acyclic G.porfStep) :
    P.Built G := by
  suffices H : ∀ n, ∀ G : Graph, G.events.card = n → G.Wf → P.Exec G →
      Maz.Acyclic G.porfStep → P.Built G from H _ G rfl hG h hac
  intro n
  induction n with
  | zero =>
    intro G hc hG h _
    have h0 : G.events = ∅ := Finset.card_eq_zero.mp hc
    rw [hG.eq_init_of_events_eq_empty h0, h.1]
    exact Built.init
  | succ n ih =>
    intro G hc hG h hac
    have hne : G.events.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha, hmax⟩ := hac.exists_maximal (G.events.image Ev.th) (hne.image _)
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    have hmax' : ∀ b, ¬ G.porfStep (.th e) b := by
      intro b hb
      have hbm := (hG.mem_of_porfStep hb).2
      cases b with
      | init => exact G.not_porfStep_init _ hb
      | th q => exact hmax _ (Finset.mem_image.mpr ⟨q, hbm, rfl⟩) hb
    have hEv : G.events ∩ G.events.erase e = G.events.erase e :=
      Finset.inter_eq_right.mpr (Finset.erase_subset _ _)
    have hpre : Maz.PrefixClosed G.porfStep (Graph.evSet (G.events ∩ G.events.erase e)) := by
      intro a b hab hb
      rw [hEv]
      cases a with
      | init => trivial
      | th q =>
        have hq := (hG.mem_of_porfStep hab).1
        refine Finset.mem_erase.mpr ⟨?_, hq⟩
        intro hqe
        rw [hqe] at hab
        exact hmax' _ hab
    have hG0 : (G.restrict (G.events.erase e)).Wf := hG.restrict hpre
    have hE0 : P.Exec (G.restrict (G.events.erase e)) := h.of_isPrefixOf hG ⟨_, hpre, rfl⟩
    have hac0 : Maz.Acyclic (G.restrict (G.events.erase e)).porfStep := by
      intro a haa
      have ham : a ∈ Graph.evSet (G.events ∩ G.events.erase e) := by
        obtain ⟨c, _, hca⟩ := Relation.TransGen.tail'_iff.mp haa
        exact (hG0.mem_of_porfStep hca).2
      exact hac a ((Graph.porf_restrict_iff hpre ham).mp haa)
    have hevs : (G.restrict (G.events.erase e)).events = G.events.erase e := hEv
    have hcard : (G.restrict (G.events.erase e)).events.card = n := by
      rw [hevs, Finset.card_erase_of_mem he]
      omega
    have hB0 := ih _ hcard hG0 hE0 hac0
    refine Built.step (e := e) hB0 hG ?_ ?_ ?_
    · rw [mem_avail_iff]
      have hcnt : (G.restrict (G.events.erase e)).cnt e.tid = e.idx := by
        have h1 : ¬ e.idx < (G.restrict (G.events.erase e)).cnt e.tid := by
          intro hlt
          obtain ⟨q, hq, ht, hi⟩ := (hG0.exists_idx_iff _ _).mpr hlt
          rw [hevs] at hq
          have hq' := Finset.mem_erase.mp hq
          exact hq'.1 (hG.idx_inj q hq'.2 e he ht hi)
        have h2 : ¬ (G.restrict (G.events.erase e)).cnt e.tid < e.idx := by
          intro hlt
          obtain ⟨q, hq, ht, hi⟩ := hG.idx_contig e he _ hlt
          have hqs : q ∈ (G.restrict (G.events.erase e)).events := by
            rw [hevs]
            refine Finset.mem_erase.mpr ⟨?_, hq⟩
            intro hqe
            rw [hqe] at hi
            omega
          have hlt' := hG0.idx_lt_cnt hqs
          rw [ht, hi] at hlt'
          omega
        omega
      refine ⟨h.tid_mem hG he, hcnt.symm, ?_⟩
      have htr : (G.restrict (G.events.erase e)).trace e.tid = G.traceBefore e.tid e.idx := by
        unfold Graph.trace
        rw [hcnt]
        refine Graph.traceBefore_restrict_of_keep hG (le_of_lt (hG.idx_lt_cnt he)) ?_ ?_
        · intro q hq ht hi
          refine Finset.mem_erase.mpr ⟨?_, hq⟩
          intro hqe
          rw [hqe] at hi
          omega
        · intro q hq ht hi w hw
          have hstep : G.porfStep w (.th q) := Or.inr ⟨q, rfl, hq, hw⟩
          have hwm := (hG.mem_of_porfStep hstep).1
          cases w with
          | init => trivial
          | th w0 =>
            refine Finset.mem_erase.mpr ⟨?_, hwm⟩
            intro hwe
            rw [hwe] at hstep
            exact hmax' _ hstep
      rw [htr]
      exact h.2 e he
    · rw [hevs]
      exact (Finset.insert_erase he).symm
    · rw [hevs]

/-! ### Computable versions on configurations

`Graph.trace` is not computable. On a configuration the order list gives a
computable enumeration of the events; the definitions below are used for
`#eval` and for the executable explorer, and agree with the definitions on
graphs for well-formed configurations. -/

end Program

namespace Config

/-- The event of thread `t` with index `i` in the order list. -/
def evAt (c : Config) (t : Tid) (i : ℕ) : Option TEv :=
  c.order.find? (fun e => decide (e.tid = t ∧ e.idx = i))

/-- The number of events of thread `t`. -/
def cnt (c : Config) (t : Tid) : ℕ := (c.order.filter (fun e => decide (e.tid = t))).length

/-- The trace of thread `t`. -/
def trace (c : Config) (t : Tid) : List (Option Val) :=
  (List.range (c.cnt t)).map (fun i => (c.evAt t i).bind c.abs.ret)

theorem evAt_eq (c : Config) (hc : c.Wf) (t : Tid) (i : ℕ) : c.evAt t i = c.abs.evAt t i := by
  unfold evAt
  cases hf : c.order.find? (fun e => decide (e.tid = t ∧ e.idx = i)) with
  | none =>
    cases hg : c.abs.evAt t i with
    | none => rfl
    | some q =>
      obtain ⟨hqm, ht, hi⟩ := Graph.evAt_eq_some_iff_spec hg
      have := List.find?_eq_none.mp hf q (List.mem_toFinset.mp hqm)
      simp [ht, hi] at this
  | some q =>
    have hq := List.find?_some hf
    have hqm := List.mem_of_find?_eq_some hf
    simp only [decide_eq_true_eq] at hq
    exact (Graph.evAt_eq_some_of_inj' hc.1.idx_inj (List.mem_toFinset.mpr hqm) hq.1 hq.2).symm

theorem cnt_eq (c : Config) (hc : c.Wf) (t : Tid) : c.cnt t = c.abs.cnt t := by
  unfold Config.cnt Graph.cnt
  have hnd : (c.order.filter (fun e => decide (e.tid = t))).Nodup := hc.2.filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext e
  simp [Config.abs]

theorem trace_eq (c : Config) (hc : c.Wf) (t : Tid) : c.trace t = c.abs.trace t := by
  unfold Config.trace Graph.trace Graph.traceBefore
  rw [cnt_eq c hc]
  apply List.map_congr_left
  intro i _
  rw [evAt_eq c hc]

end Config

namespace Program

variable (P : Program)

/-- Computable `avail`. -/
def availC (c : Config) : List TEv :=
  P.threads.filterMap (fun t => (P.step t (c.trace t)).map (fun a => ⟨t, c.cnt t, a⟩))

/-- Computable `next`: the available event of the least thread. -/
def nextC (c : Config) : Option TEv :=
  (P.availC c).foldl
    (fun acc e => match acc with
      | none => some e
      | some a => if e.tid < a.tid then some e else some a) none

variable {P}

/-- The fold of `nextC`: it returns an element of least thread among the
accumulator and the list. -/
private theorem foldl_min_spec (l : List TEv) (acc : Option TEv) :
    ((l.foldl (fun acc e => match acc with
        | none => some e
        | some a => if e.tid < a.tid then some e else some a) acc = none) ↔
        (acc = none ∧ l = [])) ∧
      ∀ a, l.foldl (fun acc e => match acc with
        | none => some e
        | some a => if e.tid < a.tid then some e else some a) acc = some a →
        (acc = some a ∨ a ∈ l) ∧ (∀ x, acc = some x → a.tid ≤ x.tid) ∧
          ∀ b ∈ l, a.tid ≤ b.tid := by
  induction l generalizing acc with
  | nil =>
    refine ⟨by simp, fun a ha => ?_⟩
    have ha' : acc = some a := ha
    refine ⟨Or.inl ha', fun x hx => ?_, by simp⟩
    rw [ha'] at hx
    cases hx
    exact Nat.le_refl _
  | cons e l ih =>
    simp only [List.foldl_cons]
    cases acc with
    | none =>
      obtain ⟨h1, h2⟩ := ih (some e)
      refine ⟨by simp [h1], fun a ha => ?_⟩
      obtain ⟨h3, h4, h5⟩ := h2 a ha
      refine ⟨Or.inr ?_, by simp, ?_⟩
      · rcases h3 with h3 | h3
        · cases h3; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ h3
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact h4 _ rfl
        · exact h5 b hb
    | some x =>
      by_cases hlt : e.tid < x.tid
      · simp only [hlt, ↓reduceIte]
        obtain ⟨h1, h2⟩ := ih (some e)
        refine ⟨by simp [h1], fun a ha => ?_⟩
        obtain ⟨h3, h4, h5⟩ := h2 a ha
        have hae := h4 e rfl
        refine ⟨Or.inr ?_, ?_, ?_⟩
        · rcases h3 with h3 | h3
          · cases h3; exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ h3
        · intro y hy
          cases hy
          exact Nat.le_of_lt (Nat.lt_of_le_of_lt hae hlt)
        · intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact hae
          · exact h5 b hb
      · simp only [hlt, ↓reduceIte]
        obtain ⟨h1, h2⟩ := ih (some x)
        refine ⟨by simp [h1], fun a ha => ?_⟩
        obtain ⟨h3, h4, h5⟩ := h2 a ha
        have hax := h4 x rfl
        refine ⟨?_, ?_, ?_⟩
        · rcases h3 with h3 | h3
          · exact Or.inl h3
          · exact Or.inr (List.mem_cons_of_mem _ h3)
        · intro y hy
          cases hy
          exact hax
        · intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact Nat.le_trans hax (Nat.le_of_not_lt hlt)
          · exact h5 b hb

theorem availC_eq {c : Config} (hc : c.Wf) : P.availC c = P.avail c.abs := by
  unfold availC avail nextOf
  congr 1
  funext t
  rw [Config.trace_eq c hc, Config.cnt_eq c hc]

theorem nextC_eq_none_iff {c : Config} (hc : c.Wf) : P.nextC c = none ↔ P.Full c.abs := by
  unfold nextC Full
  rw [(foldl_min_spec (P.availC c) none).1, availC_eq hc]
  simp

theorem nextC_eq_some_iff {c : Config} (hc : c.Wf) {e : TEv} :
    P.nextC c = some e ↔ P.IsNext c.abs e := by
  have hfwd : ∀ e, P.nextC c = some e → P.IsNext c.abs e := by
    intro e he
    obtain ⟨h1, -, h3⟩ := (foldl_min_spec (P.availC c) none).2 e he
    rw [availC_eq hc] at h1 h3
    have hmem : e ∈ P.avail c.abs := h1.resolve_left (by simp)
    refine ⟨hmem, fun e' he' hne => ?_⟩
    have hle := h3 e' he'
    rcases Nat.lt_or_ge e.tid e'.tid with hlt | hge
    · exact Or.inl hlt
    · exact absurd (avail_tid_inj he' hmem (Nat.le_antisymm hge hle)) hne
  refine ⟨hfwd e, fun h => ?_⟩
  have hnf : ¬ P.Full c.abs := by
    intro hf
    have := h.1
    rw [show P.avail c.abs = [] from hf] at this
    cases this
  cases hn : P.nextC c with
  | none => exact absurd ((nextC_eq_none_iff hc).mp hn) hnf
  | some e2 => exact congrArg some ((exists_unique_isNext hnf).unique (hfwd e2 hn) h)

end Program


end Condpor
