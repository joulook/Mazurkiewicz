import Mazurkiewicz.Condpor.Stack
import Mazurkiewicz.Condpor.Examples

/-!
# Section 2.1 with several pushes per thread: instances

`length_interleavings_div` counts the interleavings of `n` sequences of
length `k`: `(kn)!/(k!)^n`. That the full SC-consistent executions of `n`
threads with `k` accesses to the counter are as many is proved for `k = 1`
and every `n` (`ctr_executions`); for `n = 2` with `k = 2, 3`, and for
`n = 3` with `k = 2`, it is checked here by evaluation of the computed
explorer.
-/

namespace Condpor

/-- Thread `t < 2` writes `k` times to location `0`. -/
def ctrkTab (k : ℕ) : Tid → List (Option Val) → Option Act
  | t, u => if u.length < k then some (.write 0 (10 * (t + 1) + u.length)) else none

/-- Two threads with `k` accesses each. -/
def ctrkProg (k : ℕ) : Program := mkProg [0, 1] (by decide) (ctrkTab k) (fun _ => 0) k

theorem ctrk_2_2 : (exploreC (ctrkProg 2) eqOracleSe 2).length = 6 := by decide +kernel

theorem ctrk_2_3 : (exploreC (ctrkProg 3) eqOracleSe 3).length = 20 := by decide +kernel

/-- Two threads with two accesses each: `4!/(2!)^2 = 6` full SC-consistent
executions, the number of interleavings. -/
theorem ctr_executions_2_2 : ∃ l : List Graph, l.Nodup ∧
    l.length = (interleavings [[1, 2], [3, 4]]).length ∧ l.length = (2 * 2).factorial / 2 ^ 2 ∧
    ∀ G, G ∈ l ↔ G.Wf ∧ (ctrkProg 2).Exec G ∧ (SC.sym EqSem.solver).cons G ∧
      (ctrkProg 2).Full G :=
  ⟨_, (exploreC_spec eqOracleSe (mkProg_bounded _ _ _ _ _)).1,
    ctrk_2_2.trans (by rw [length_interleavings_div 2 _ (by simp)]; decide),
    ctrk_2_2.trans (by decide), (exploreC_spec eqOracleSe (mkProg_bounded _ _ _ _ _)).2⟩

/-- Two threads with three accesses each: `6!/(3!)^2 = 20`. -/
theorem ctr_executions_2_3 : ∃ l : List Graph, l.Nodup ∧
    l.length = (interleavings [[1, 2, 3], [4, 5, 6]]).length ∧
    l.length = (3 * 2).factorial / 6 ^ 2 ∧
    ∀ G, G ∈ l ↔ G.Wf ∧ (ctrkProg 3).Exec G ∧ (SC.sym EqSem.solver).cons G ∧
      (ctrkProg 3).Full G :=
  ⟨_, (exploreC_spec eqOracleSe (mkProg_bounded _ _ _ _ _)).1,
    ctrk_2_3.trans (by rw [length_interleavings_div 3 _ (by simp)]; decide),
    ctrk_2_3.trans (by decide), (exploreC_spec eqOracleSe (mkProg_bounded _ _ _ _ _)).2⟩

/-- Three threads with `k` accesses each. -/
def ctrk3Prog (k : ℕ) : Program := mkProg [0, 1, 2] (by decide) (ctrkTab k) (fun _ => 0) k

theorem ctrk_3_2 : (exploreC (ctrk3Prog 2) eqOracleSe 2).length = 90 := by decide +kernel

/-- Three threads with two accesses each: `6!/(2!)^3 = 90`. -/
theorem ctr_executions_3_2 : ∃ l : List Graph, l.Nodup ∧
    l.length = (interleavings [[1, 2], [3, 4], [5, 6]]).length ∧
    l.length = (2 * 3).factorial / 2 ^ 3 ∧
    ∀ G, G ∈ l ↔ G.Wf ∧ (ctrk3Prog 2).Exec G ∧ (SC.sym EqSem.solver).cons G ∧
      (ctrk3Prog 2).Full G :=
  ⟨_, (exploreC_spec eqOracleSe (mkProg_bounded _ _ _ _ _)).1,
    ctrk_3_2.trans (by rw [length_interleavings_div 2 _ (by simp)]; decide),
    ctrk_3_2.trans (by decide), (exploreC_spec eqOracleSe (mkProg_bounded _ _ _ _ _)).2⟩

end Condpor
