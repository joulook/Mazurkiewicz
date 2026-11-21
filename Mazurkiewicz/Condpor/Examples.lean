import Mazurkiewicz.Condpor.EqSolver

/-!
# The examples of Section 2.2 of the paper

Programs are built with `mkProg` from a table of next actions: a thread
outside the list does nothing, a thread performs at most `n` actions, and no
action follows `block` or `error`.

Encoding of the examples: locations `x = 0`, `y = 1`; the symbol `s` has the
number `1`; a value `1000 + i` stands for the symbol `i`, a smaller value for
itself; the formula `s = k` has the code `fEq s k`. `assert(b)` is
`if !b error()` as in Section 3 of the paper: a failing assertion gives an
`error` event, after which the thread stops.
-/

namespace Condpor

/-- The action stops its thread. -/
def isStop : Option Act → Bool
  | some .block => true
  | some .error => true
  | _ => false

/-- Some earlier action of the thread was `block` or `error`. -/
def stopped (f : Tid → List (Option Val) → Option Act) (t : Tid) (u : List (Option Val)) :
    Bool :=
  (List.range u.length).any (fun i => isStop (f t (u.take i)))

/-- The program with the table `f` of next actions, for the listed threads,
cut at `n` actions per thread and after `block` or `error`. -/
def mkProg (threads : List Tid) (hnd : threads.Nodup)
    (f : Tid → List (Option Val) → Option Act) (mem : Loc → Val) (n : ℕ) : Program where
  threads := threads
  threads_nodup := hnd
  step := fun t u => if n ≤ u.length ∨ t ∉ threads ∨ stopped f t u = true then none else f t u
  mem := mem
  step_none := by
    intro t ht
    simp [ht]
  stop := by
    intro t u h
    by_cases hc : n ≤ u.length ∨ t ∉ threads ∨ stopped f t u = true
    · simp [hc] at h
    · simp only [hc, ↓reduceIte] at h
      have hs : isStop (f t u) = true := by
        rcases h with h | h <;> rw [h] <;> rfl
      have : stopped f t (u ++ [none]) = true := by
        unfold stopped
        rw [List.any_eq_true]
        exact ⟨u.length, by simp, by simpa using hs⟩
      simp [this]

theorem mkProg_bounded (threads : List Tid) (hnd : threads.Nodup)
    (f : Tid → List (Option Val) → Option Act) (mem : Loc → Val) (n : ℕ) :
    (mkProg threads hnd f mem n).Bounded n := by
  intro t u hu
  simp [mkProg, hu]

/-! ### Fig. 1: `w+sw+r+r` -/

/-- `x := 1 ‖ y := nondet() ‖ assert(y = 42) ‖ b := x`. -/
def fig1Tab : Tid → List (Option Val) → Option Act
  | 0, [] => some (.write 0 1)
  | 1, [] => some (.gen 1)
  | 1, [none] => some (.write 1 1001)
  | 2, [] => some (.read 1)
  | 2, [some v] =>
    if 1000 ≤ v then some (.cons (fEq (v - 1000) 42))
    else if v = 42 then none else some .error
  | 2, [some _, some b] => if b = 0 then some .error else none
  | 3, [] => some (.read 0)
  | _, _ => none

/-- The program of Fig. 1. -/
def fig1 : Program := mkProg [0, 1, 2, 3] (by decide) fig1Tab (fun _ => 0) 3

theorem fig1_count : (exploreC fig1 eqOracleSe 3).length = 6 := by decide +kernel

/-- Fig. 1: `w+sw+r+r` has exactly six full consistent executions under SC
with satisfiable constraints. (They are the graphs of the figure, with the
`error` event of each failing assertion: the read of `y` from `init` gives an
error, and so does the outcome `s ≠ 42`.) -/
theorem fig1_six : ∃ l : List Graph, l.Nodup ∧ l.length = 6 ∧
    ∀ G, G ∈ l ↔ G.Wf ∧ fig1.Exec G ∧ (SC.sym EqSem.solver).cons G ∧ fig1.Full G :=
  ⟨_, (exploreC_spec eqOracleSe (mkProg_bounded _ _ _ _ _)).1, fig1_count,
    (exploreC_spec eqOracleSe (mkProg_bounded _ _ _ _ _)).2⟩

/-! ### Example 1: `rs+w` -/

/-- `a := x; b := nondet(); assert(a = 0 ∨ b ≠ 42) ‖ x := 1`. The comparison
of `b` is evaluated also when `a = 0`, as in Fig. 2 of the paper, and its
formula is `s = 42`. -/
def ex1Tab : Tid → List (Option Val) → Option Act
  | 0, [] => some (.read 0)
  | 0, [some _] => some (.gen 1)
  | 0, [some _, none] => some (.cons (fEq 1 42))
  | 0, [some v, none, some b] => if v = 0 ∨ b = 0 then none else some .error
  | 1, [] => some (.write 0 1)
  | _, _ => none

/-- The program of Example 1. -/
def ex1 : Program := mkProg [0, 1] (by decide) ex1Tab (fun _ => 0) 4

theorem ex1_count : (exploreC ex1 eqOracleSe 4).length = 4 := by decide +kernel

/-- Example 1 has four full consistent executions: the read of `x` from
`init` or from the write, with either outcome of the comparison. -/
theorem ex1_four : ∃ l : List Graph, l.Nodup ∧ l.length = 4 ∧
    ∀ G, G ∈ l ↔ G.Wf ∧ ex1.Exec G ∧ (SC.sym EqSem.solver).cons G ∧ ex1.Full G :=
  ⟨_, (exploreC_spec eqOracleSe (mkProg_bounded _ _ _ _ _)).1, ex1_count,
    (exploreC_spec eqOracleSe (mkProg_bounded _ _ _ _ _)).2⟩

/-- The read of `x`. -/
def ex1r : TEv := ⟨0, 0, .read 0⟩
/-- The generation of `s`. -/
def ex1g : TEv := ⟨0, 1, .gen 1⟩
/-- The evaluation of `s = 42`. -/
def ex1s : TEv := ⟨0, 2, .cons (fEq 1 42)⟩
/-- The write of `x`. -/
def ex1w : TEv := ⟨1, 0, .write 0 1⟩

/-- Graphs B (`b = true`: `s = 42`) and C (`b = false`: `s ≠ 42`) of Fig. 2,
before the write of `x` is added: the read of `x` from `init`, the generation
and the evaluation. -/
def ex1BC (b : Bool) : Config :=
  ⟨fun _ => 0, [ex1s, ex1g, ex1r], fun e => if e = ex1r then some .init else none,
    fun _ => [], fun e => if e = ex1s then some b else none⟩

/-- Example 1, "`R(x)` is only revisited in exploration B": in B the deleted
events and the read are maximally added, so the write of `x` revisits the
read. -/
theorem ex1_revisit_B :
    ¬ ((ex1BC true).plus ex1w).porf (.th ex1r) (.th ex1w) ∧
      ∀ d, ((ex1BC true).Deleted ex1r ex1w d ∨ d = ex1r) →
        (ex1BC true).IsMaximallyAdded (TieBreak.se EqSem.solver)
          ((ex1BC true).ctx ex1r ex1w) d ex1w :=
  ((ex1BC true).revisitOKB_iff (TieBreak.se EqSem.solver) eqOracleSe.prefB_eq
    (by decide) ex1w).mp (by decide +kernel)

/-- In C the evaluation is not maximally added (its outcome `s ≠ 42` is not
the preferred one), so the write of `x` does not revisit the read. -/
theorem ex1_no_revisit_C :
    ¬ (¬ ((ex1BC false).plus ex1w).porf (.th ex1r) (.th ex1w) ∧
      ∀ d, ((ex1BC false).Deleted ex1r ex1w d ∨ d = ex1r) →
        (ex1BC false).IsMaximallyAdded (TieBreak.se EqSem.solver)
          ((ex1BC false).ctx ex1r ex1w) d ex1w) := fun h =>
  absurd (((ex1BC false).revisitOKB_iff (TieBreak.se EqSem.solver) eqOracleSe.prefB_eq
    (by decide) ex1w).mpr h) (by decide +kernel)

/-! ### The litmus test of Section 2.2.1 -/

/-- `x := 1; y := 1 ‖ a := y; b := x`. -/
def sbTab : Tid → List (Option Val) → Option Act
  | 0, [] => some (.write 0 1)
  | 0, [none] => some (.write 1 1)
  | 1, [] => some (.read 1)
  | 1, [some _] => some (.read 0)
  | _, _ => none

/-- The program of the litmus test. -/
def sb : Program := mkProg [0, 1] (by decide) sbTab (fun _ => 0) 2

theorem sb_check : (exploreC sb eqOracleSe 2).all (fun G =>
    !(decide (G.rf ⟨1, 0, .read 1⟩ = some (.th ⟨0, 1, .write 1 1⟩)) &&
      decide (G.rf ⟨1, 1, .read 0⟩ = some .init))) = true := by decide +kernel

/-- Under sequential consistency thread II cannot read `a = 1` (from the write
of `y`) and `b = 0` (from `init`). -/
theorem sb_forbidden (G : Graph) (hG : G.Wf) (hE : sb.Exec G)
    (hc : (SC.sym EqSem.solver).cons G) (hf : sb.Full G) :
    ¬ (G.rf ⟨1, 0, .read 1⟩ = some (.th ⟨0, 1, .write 1 1⟩) ∧
      G.rf ⟨1, 1, .read 0⟩ = some .init) := by
  have hm := ((exploreC_spec eqOracleSe (mkProg_bounded _ _ _ _ _)).2 G).mpr ⟨hG, hE, hc, hf⟩
  have := List.all_eq_true.mp sb_check G hm
  rintro ⟨h1, h2⟩
  simp [h1, h2] at this

end Condpor
