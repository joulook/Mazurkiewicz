import Mazurkiewicz.Condpor.Rmw.Locks

/-!
# Locks: computed instances

Seven programs with the lock `0`. The counts were derived by hand before the
evaluation (`plan/condpor/lean/LOCKS-PLAN.md`, Section 4); they are computed
here by the kernel on the explorer for `SC` with atomicity.

| program | full executions | without a blocked thread |
|---|---|---|
| T0: `lock; unlock` ‖ `lock; unlock` | 4 | 2 |
| T1: `lock; unlock` ‖ `tryLock; unlock if true` | 4 | 3 |
| T2: both threads `tryLock; unlock if true` | 4 | 4 |
| T3: `tryLock` (on failure stop); `tryLock`; `unlock`; `unlock` ‖ `lock; unlock` | 4 | 3 |
| T4: `lock; lock; unlock; unlock` ‖ `lock; unlock` | 4 | 2 |
| T5: `lock; unlock; unlock` | 1 | 1 |
| T6: twice `tryLock; unlock if true` ‖ `lock; unlock` | 8 | 6 |

In every execution the writes of the lock alternate, in coherence order,
between an acquire and the release by the same thread (`lockOkB`): mutual
exclusion. The second `unlock` of T5 is an `error` event.
-/

namespace Condpor

open Program

/-- The writes of the lock `l` alternate in coherence order between an acquire
(value `1`) of a thread and a release (value `0`) by that thread, starting
free. -/
def lockOkB (G : Graph) (l : Loc) : Bool :=
  ((G.co l).foldl
    (fun (st : Option (Option Tid)) w =>
      match st with
      | none => none
      | some h =>
        match w.act with
        | .write _ v =>
          if v = 1 then (if h = none then some (some w.tid) else none)
          else if v = 0 then (if h = some w.tid then some none else none)
          else none
        | _ => none)
    (some none)).isSome

/-- No thread of the graph ends blocked. -/
def noBlockB (G : Graph) : Bool := decide (∀ e ∈ G.events, e.act ≠ .block)

/-- The graph has an `error` event. -/
def hasErrorB (G : Graph) : Bool := decide (∃ e ∈ G.events, e.act = .error)

/-- The numbers of an evaluation: full executions, those without a blocked
thread, and whether every one satisfies `lockOkB` for the lock `0`. -/
noncomputable def lockReport (P : XProgram) (n : ℕ) : ℕ × ℕ × Bool :=
  ((exploreAt P eqOracleSe n).length, ((exploreAt P eqOracleSe n).filter noBlockB).length,
    (exploreAt P eqOracleSe n).all (fun G => lockOkB G 0))

def codeT1 : Tid → List LOp
  | 0 => [.lock 0, .unlock 0]
  | _ => [.tryLock 0 1, .unlock 0]

def codeT2 : Tid → List LOp
  | _ => [.tryLock 0 1, .unlock 0]

def codeT3 : Tid → List LOp
  | 0 => [.tryLock 0 3, .tryLock 0 0, .unlock 0, .unlock 0]
  | _ => [.lock 0, .unlock 0]

def codeT4 : Tid → List LOp
  | 0 => [.lock 0, .lock 0, .unlock 0, .unlock 0]
  | _ => [.lock 0, .unlock 0]

def codeT5 : Tid → List LOp
  | _ => [.lock 0, .unlock 0, .unlock 0]

def codeT6 : Tid → List LOp
  | 0 => [.tryLock 0 1, .unlock 0, .tryLock 0 1, .unlock 0]
  | _ => [.lock 0, .unlock 0]

def progT1 : XProgram := lockSys [0, 1] (by decide) codeT1 6
def progT2 : XProgram := lockSys [0, 1] (by decide) codeT2 6
def progT3 : XProgram := lockSys [0, 1] (by decide) codeT3 6
def progT4 : XProgram := lockSys [0, 1] (by decide) codeT4 6
def progT5 : XProgram := lockSys [0] (by decide) codeT5 6
def progT6 : XProgram := lockSys [0, 1] (by decide) codeT6 8

/-- T1: `lock` against `tryLock`. -/
theorem lockT1 : lockReport progT1 6 = (4, 3, true) := by decide +kernel

/-- T2: `tryLock` against `tryLock`. -/
theorem lockT2 : lockReport progT2 6 = (4, 4, true) := by decide +kernel

/-- T3: `tryLock` by the holder. -/
theorem lockT3 : lockReport progT3 6 = (4, 3, true) := by decide +kernel

/-- T4: `lock` by the holder; the first `unlock` does not release. -/
theorem lockT4 : lockReport progT4 6 = (4, 2, true) := by decide +kernel

/-- T5: `unlock` by a thread that does not hold the lock is an error. -/
theorem lockT5 : lockReport progT5 6 = (1, 1, true) ∧
    (exploreAt progT5 eqOracleSe 6).all hasErrorB = true := by decide +kernel

/-- T6: repeated attempts. -/
theorem lockT6 : lockReport progT6 8 = (8, 6, true) := by decide +kernel

/-- The lists are the full consistent executions (from `lockSys_explore`). -/
theorem lockT1_execs : HasExecs progT1 4 := hasExecs_of_count (by decide +kernel)
theorem lockT2_execs : HasExecs progT2 4 := hasExecs_of_count (by decide +kernel)
theorem lockT3_execs : HasExecs progT3 4 := hasExecs_of_count (by decide +kernel)
theorem lockT4_execs : HasExecs progT4 4 := hasExecs_of_count (by decide +kernel)
theorem lockT5_execs : HasExecs progT5 1 := hasExecs_of_count (by decide +kernel)
theorem lockT6_execs : HasExecs progT6 8 := hasExecs_of_count (by decide +kernel)

/-- T0: two threads `lock; unlock`. -/
def codeT0 : Tid → List LOp
  | _ => [.lock 0, .unlock 0]

def progT0 : XProgram := lockSys [0, 1] (by decide) codeT0 6

theorem lockT0 : lockReport progT0 6 = (4, 2, true) := by decide +kernel

/-- None of T0-T4 and T6 has a reached configuration that is not full and has
no step. (An observation: these programs have no constraint evaluation,
unlike the program of `lock_dead`.) -/
theorem lockT_no_dead : ¬ HasDead progT0 ∧ ¬ HasDead progT1 ∧ ¬ HasDead progT2 ∧
    ¬ HasDead progT3 ∧ ¬ HasDead progT4 ∧ ¬ HasDead progT6 :=
  ⟨not_hasDead_of_count (by decide +kernel), not_hasDead_of_count (by decide +kernel),
    not_hasDead_of_count (by decide +kernel), not_hasDead_of_count (by decide +kernel),
    not_hasDead_of_count (by decide +kernel), not_hasDead_of_count (by decide +kernel)⟩

end Condpor
