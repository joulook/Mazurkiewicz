import Mathlib.Data.List.Infix
import Mathlib.Data.Set.Basic

/-!
# PCT programs, labellings and directives

`pctdpor`, `testing.tex` (def:pct-program, def:labelling, def:directive) and
`depth.tex` (def:pviolates, lem:literal-prefix, lem:emission, def:strict).

How the text is read here.

* A schedule is a list of thread identifiers with the **latest step at the
  head**: `t :: S` is the schedule `S` followed by a step of `t`. A prefix of
  a schedule in the text is a suffix of the list (`S' <:+ S`).
* A PCT program is a set of schedules that contains the empty schedule and
  is closed under removing the last step (`Prog`).
* def:labelling: `Labelling Q L`. The four conditions are asked for the
  schedules of `Q`. A name `a` is emitted by the step of `t` after `S'`
  (`EmitStep`) if `S' = U ++ S''` with `S''` non-empty, `next S'' t = a` and
  no step of `t` in `U`; `names S` collects the names emitted by the steps
  of `S`. This is the definition of the text, word for word.
* def:directive: `Directive L d` has targets `b i` and sets `A i` for
  `i : Fin d`; `Violates` is the literal reading, `PViolates` the prefix
  reading (def:pviolates).
-/

namespace Pct

/-- Thread identifiers. -/
abbrev Tid := ℕ

/-- Schedules, latest step first. -/
abbrev Sched := List Tid

/-- A PCT program: a prefix-closed set of schedules (def:pct-program). -/
structure Prog where
  /-- The schedules of the program. -/
  mem : Set Sched
  nil_mem : [] ∈ mem
  tail_mem : ∀ {t S}, t :: S ∈ mem → S ∈ mem

namespace Prog

variable (Q : Prog)

theorem suffix_mem {S S' : Sched} (h : S ∈ Q.mem) (hs : S' <:+ S) : S' ∈ Q.mem := by
  induction S with
  | nil => simpa [List.suffix_nil.mp hs] using h
  | cons t S ih =>
    rcases List.suffix_cons_iff.mp hs with rfl | hs'
    · exact h
    · exact ih (Q.tail_mem h) hs'

/-- The threads enabled after `S`. -/
def en (S : Sched) : Set Tid := {t | t :: S ∈ Q.mem}

/-- `S` is a complete schedule. -/
def Complete (S : Sched) : Prop := S ∈ Q.mem ∧ ∀ t, t :: S ∉ Q.mem

/-- `S` is a partial schedule. -/
def Partial (S : Sched) : Prop := S ∈ Q.mem ∧ ∃ t, t :: S ∈ Q.mem

/-- Every schedule has at most `k` steps. -/
def Bounded (k : ℕ) : Prop := ∀ S ∈ Q.mem, S.length ≤ k

end Prog

/-- An event labelling (def:labelling). -/
structure Labelling (Q : Prog) (L : Type) where
  thr : L → Tid
  next : Sched → Tid → Option L
  affinity : ∀ {S t a}, S ∈ Q.mem → next S t = some a → thr a = t
  stability : ∀ {S t t' a}, t' :: S ∈ Q.mem → next S t = some a → t' ≠ t →
    next (t' :: S) t = some a
  uniqueness : ∀ {S₁ S₂ t a}, S₂ ++ S₁ ∈ Q.mem → next S₁ t = some a →
    next (S₂ ++ S₁) t = some a → t ∉ S₂
  notFirst : ∀ t, next [] t = none

/-- A strict labelling (def:strict). -/
structure Labelling.Strict {Q : Prog} {L : Type} (E : Labelling Q L) : Prop where
  started : ∀ {S t a}, S ∈ Q.mem → E.next S t = some a → t ∈ S
  backStability : ∀ {S t t' a}, t' :: S ∈ Q.mem → E.next (t' :: S) t = some a → t' ≠ t →
    E.next S t = some a

namespace Labelling

variable {Q : Prog} {L : Type} (E : Labelling Q L)

/-- The step of `t` after `S'` emits `a` (def:labelling). -/
def EmitStep (S' : Sched) (t : Tid) (a : L) : Prop :=
  ∃ U S'', S' = U ++ S'' ∧ S'' ≠ [] ∧ t ∉ U ∧ E.next S'' t = some a

/-- The names emitted in `S` (def:labelling). -/
def names (S : Sched) : Set L :=
  {a | ∃ t S', t :: S' <:+ S ∧ E.EmitStep S' t a}

/-- Stability over several steps of other threads. -/
theorem stability_append {S U : Sched} {t : Tid} {a : L} (h : U ++ S ∈ Q.mem)
    (hn : E.next S t = some a) (ht : t ∉ U) : E.next (U ++ S) t = some a := by
  induction U with
  | nil => simpa using hn
  | cons u U ih =>
    have hU : U ++ S ∈ Q.mem := Q.tail_mem h
    have : u ≠ t := fun e => ht (by simp [e])
    exact E.stability h (ih hU (fun m => ht (List.mem_cons_of_mem _ m))) this

/-- lem:emission (1), the step: what the step of `t` after `S` emits. -/
theorem emitStep_iff {S : Sched} {t : Tid} {a : L} (h : t :: S ∈ Q.mem) :
    E.EmitStep S t a ↔ E.next S t = some a := by
  constructor
  · rintro ⟨U, S'', rfl, -, hU, hn⟩
    exact E.stability_append (Q.tail_mem h) hn hU
  · intro hn
    refine ⟨[], S, rfl, ?_, by simp, hn⟩
    rintro rfl
    simp [E.notFirst] at hn

/-- lem:emission (1). -/
theorem names_cons {S : Sched} {t : Tid} (h : t :: S ∈ Q.mem) :
    E.names (t :: S) = E.names S ∪ {a | E.next S t = some a} := by
  ext a
  simp only [names, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨t', S', hs, he⟩
    rcases List.suffix_cons_iff.mp hs with heq | hs'
    · obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      exact Or.inr ((E.emitStep_iff h).mp he)
    · exact Or.inl ⟨t', S', hs', he⟩
  · rintro (⟨t', S', hs, he⟩ | hn)
    · exact ⟨t', S', hs.trans (List.suffix_cons _ _), he⟩
    · exact ⟨t, S, List.suffix_refl _, (E.emitStep_iff h).mpr hn⟩

@[simp] theorem names_nil : E.names [] = ∅ := by
  ext a
  simp [names]

theorem names_mono {S S' : Sched} (hs : S' <:+ S) : E.names S' ⊆ E.names S := by
  rintro a ⟨t, T, hT, he⟩
  exact ⟨t, T, hT.trans hs, he⟩

/-- lem:emission (2): the next name of a thread has not been emitted. -/
theorem next_not_mem_names {S : Sched} {t : Tid} {a : L} (h : S ∈ Q.mem)
    (hn : E.next S t = some a) : a ∉ E.names S := by
  rintro ⟨u, S', hs, he⟩
  obtain ⟨V, rfl⟩ := hs
  have hS' : u :: S' ∈ Q.mem := Q.suffix_mem h (List.suffix_append _ _)
  have hu : E.next S' u = some a := (E.emitStep_iff hS').mp he
  have hut : u = t := by
    rw [← E.affinity (Q.tail_mem hS') hu, E.affinity h hn]
  subst hut
  have : u ∉ V ++ [u] := E.uniqueness (S₁ := S') (S₂ := V ++ [u]) (by simpa using h) hu
    (by simpa using hn)
  simp at this

end Labelling

/-- A directive of size `d` (def:directive). -/
structure Directive (L : Type) (d : ℕ) where
  A : Fin d → Set L
  b : Fin d → L
  b_inj : Function.Injective b

namespace Directive

variable {Q : Prog} {L : Type} {d : ℕ} (D : Directive L d) (E : Labelling Q L)

/-- The literal reading of "violates" (def:directive). -/
def Violates (S : Sched) : Prop :=
  (∃ i, ∃ a ∈ D.A i, D.b i ∈ E.names S ∧ a ∉ E.names S) ∨
  (∃ i j, i < j ∧ D.b j ∈ E.names S ∧ D.b i ∉ E.names S)

/-- The prefix reading (def:pviolates). -/
def PViolates (S : Sched) : Prop := ∃ S', S' <:+ S ∧ D.Violates E S'

/-- `S` p-satisfies the directive. -/
def PSatisfies (S : Sched) : Prop := ¬ D.PViolates E S ∧ ∀ i, D.b i ∈ E.names S

/-- The directive p-guarantees the bug `B` (def:pviolates). -/
structure PGuarantees (B : Set Sched) : Prop where
  cond1 : ∀ S, Q.Partial S → ¬ D.PViolates E S → ∃ t, t :: S ∈ Q.mem ∧ ¬ D.PViolates E (t :: S)
  cond2 : ∀ S, Q.Complete S → ¬ D.PViolates E S → D.PSatisfies E S ∧ S ∈ B

/-- The literal reading of "guarantees" (def:directive). -/
structure Guarantees (B : Set Sched) : Prop where
  cond1 : ∀ S, Q.Partial S → ¬ D.Violates E S → ∃ t, t :: S ∈ Q.mem ∧ ¬ D.Violates E (t :: S)
  cond2 : ∀ S, Q.Complete S → ¬ D.Violates E S →
    (¬ D.Violates E S ∧ ∀ i, D.b i ∈ E.names S) ∧ S ∈ B

theorem not_violates_nil : ¬ D.Violates E [] := by
  simp [Violates]

theorem pviolates_cons {S : Sched} {t : Tid} :
    D.PViolates E (t :: S) ↔ D.PViolates E S ∨ D.Violates E (t :: S) := by
  constructor
  · rintro ⟨S', hs, hv⟩
    rcases List.suffix_cons_iff.mp hs with rfl | hs'
    · exact Or.inr hv
    · exact Or.inl ⟨S', hs', hv⟩
  · rintro (⟨S', hs, hv⟩ | hv)
    · exact ⟨S', hs.trans (List.suffix_cons _ _), hv⟩
    · exact ⟨_, List.suffix_refl _, hv⟩

theorem not_pviolates_nil : ¬ D.PViolates E [] := by
  rintro ⟨S', hs, hv⟩
  rw [List.suffix_nil.mp hs] at hv
  exact D.not_violates_nil E hv

/-- lem:emission (3): a step that creates a violation emits a target. -/
theorem next_target_of_violates {S : Sched} {t : Tid} (h : t :: S ∈ Q.mem)
    (hS : ¬ D.Violates E S) (hv : D.Violates E (t :: S)) : ∃ i, E.next S t = some (D.b i) := by
  by_contra hne
  push Not at hne
  apply hS
  have key : ∀ i, D.b i ∈ E.names (t :: S) → D.b i ∈ E.names S := by
    intro i hi
    rw [E.names_cons h] at hi
    rcases hi with hi | hi
    · exact hi
    · exact absurd hi (hne i)
  have mono : ∀ a, a ∉ E.names (t :: S) → a ∉ E.names S :=
    fun a ha m => ha (E.names_mono (List.suffix_cons _ _) m)
  rcases hv with ⟨i, a, haA, hb, ha⟩ | ⟨i, j, hij, hb, ha⟩
  · exact Or.inl ⟨i, a, haA, key i hb, mono a ha⟩
  · exact Or.inr ⟨i, j, hij, key j hb, mono _ ha⟩

/-- lem:literal-prefix. -/
theorem Guarantees.pGuarantees {B : Set Sched} (hg : D.Guarantees E B) : D.PGuarantees E B := by
  refine ⟨?_, ?_⟩
  · intro S hp hnv
    have hS : ¬ D.Violates E S := fun hv => hnv ⟨S, List.suffix_refl _, hv⟩
    obtain ⟨t, ht, hv⟩ := hg.cond1 S hp hS
    refine ⟨t, ht, ?_⟩
    rw [pviolates_cons]
    rintro (h | h)
    · exact hnv h
    · exact hv h
  · intro S hc hnv
    have hS : ¬ D.Violates E S := fun hv => hnv ⟨S, List.suffix_refl _, hv⟩
    obtain ⟨⟨-, hb⟩, hB⟩ := hg.cond2 S hc hS
    exact ⟨⟨hnv, hb⟩, hB⟩

end Directive

end Pct
