import Mazurkiewicz.Condpor.Rmw.LocksEx

/-!
# Locks: a query of the lock, and a constraint evaluation

Programs with the lock `0` in which a thread reads the lock location without
acquiring it (`rd 0`: the query "is the lock held?"; the answer is the value
read), and one program with a constraint evaluation inside a critical
section. The counts are computed by the kernel on the explorer for `SC` with
atomicity. They were not derived by hand first.

| program | full executions | without a blocked thread |
|---|---|---|
| Q1: `lock; unlock` ‖ query | 3 | 3 |
| Q2: `tryLock; unlock if true` ‖ query | 3 | 3 |
| Q3: `lock; unlock` ‖ two queries | 6 | 6 |
| Q4: `lock; unlock` ‖ `lock; unlock` ‖ query | 16 | 10 |
| Q5: `lock; unlock` ‖ query ‖ query | 9 | 9 |
| Q6: `lock; unlock` ‖ `tryLock; unlock if true` ‖ query | 16 | 13 |
| S1: `lock; evaluate; unlock` ‖ `tryLock; unlock if true` | 7 | 6 |
-/

namespace Condpor

open Program

def codeQ1 : Tid → List LOp
  | 0 => [.lock 0, .unlock 0]
  | _ => [.rd 0]

def codeQ2 : Tid → List LOp
  | 0 => [.tryLock 0 1, .unlock 0]
  | _ => [.rd 0]

def codeQ3 : Tid → List LOp
  | 0 => [.lock 0, .unlock 0]
  | _ => [.rd 0, .rd 0]

def codeQ4 : Tid → List LOp
  | 2 => [.rd 0]
  | _ => [.lock 0, .unlock 0]

def codeQ5 : Tid → List LOp
  | 0 => [.lock 0, .unlock 0]
  | _ => [.rd 0]

def codeQ6 : Tid → List LOp
  | 0 => [.lock 0, .unlock 0]
  | 1 => [.tryLock 0 1, .unlock 0]
  | _ => [.rd 0]

def codeS1 : Tid → List LOp
  | 0 => [.lock 0, .ev 0 42, .unlock 0]
  | _ => [.tryLock 0 1, .unlock 0]

def progQ1 : XProgram := lockSys [0, 1] (by decide) codeQ1 6
def progQ2 : XProgram := lockSys [0, 1] (by decide) codeQ2 6
def progQ3 : XProgram := lockSys [0, 1] (by decide) codeQ3 6
def progQ4 : XProgram := lockSys [0, 1, 2] (by decide) codeQ4 9
def progQ5 : XProgram := lockSys [0, 1, 2] (by decide) codeQ5 9
def progQ6 : XProgram := lockSys [0, 1, 2] (by decide) codeQ6 9
def progS1 : XProgram := lockSys [0, 1] (by decide) codeS1 7

theorem lockQ1 : lockReport progQ1 6 = (3, 3, true) := by decide +kernel
theorem lockQ2 : lockReport progQ2 6 = (3, 3, true) := by decide +kernel
theorem lockQ3 : lockReport progQ3 6 = (6, 6, true) := by decide +kernel
theorem lockQ4 : lockReport progQ4 9 = (16, 10, true) := by decide +kernel
theorem lockQ5 : lockReport progQ5 9 = (9, 9, true) := by decide +kernel
theorem lockQ6 : lockReport progQ6 9 = (16, 13, true) := by decide +kernel

/-- S1: a constraint evaluation in the critical section, against `tryLock`. -/
theorem lockS1 : lockReport progS1 7 = (7, 6, true) := by decide +kernel

end Condpor
