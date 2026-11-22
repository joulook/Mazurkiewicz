import Mazurkiewicz.Condpor.Rmw.LocksEx

/-!
# Locks: further computed instances

Eleven programs with the lock `0`: three threads, repeated attempts, or a
thread that ends holding the lock. The counts are computed by
the kernel on the explorer for `SC` with atomicity. (Unlike those of
`LocksEx`, they were not derived by hand first.)

| program | full executions | without a blocked thread |
|---|---|---|
| T7: three threads `tryLock; unlock if true` | 21 | 21 |
| T8: `lock; unlock` ‖ `lock; unlock` ‖ `tryLock; unlock if true` | 21 | 10 |
| T9: `lock; unlock` ‖ `tryLock; unlock if true` ‖ `tryLock; unlock if true` | 21 | 15 |
| T10: twice `lock; unlock` ‖ twice `tryLock; unlock if true` | 21 | 15 |
| T11: twice `tryLock; unlock if true` ‖ `tryLock; unlock if true` ‖ `lock; unlock` | 62 | 44 |
| T12: `tryLock; unlock if true; lock; unlock` ‖ `lock; unlock` | 8 | 4 |
| T13: both threads twice `tryLock; unlock if true` | 26 | 26 |
| T14: twice `lock; unlock` ‖ three times `tryLock; unlock if true` | 48 | 35 |
| T15: `lock; unlock` ‖ `lock; unlock` ‖ twice `tryLock; unlock if true` | 62 | 30 |
| T16: `lock; unlock` ‖ `tryLock` (kept) | 3 | 2 |
| T17: `lock; unlock` ‖ `lock` (kept) | 3 | 1 |

The number without a blocked thread is the number of executions that a checker
has to report when a `lock` that finds the lock held waits instead of adding an
event.
-/

namespace Condpor

open Program

def codeT7 : Tid → List LOp
  | _ => [.tryLock 0 1, .unlock 0]

def codeT8 : Tid → List LOp
  | 2 => [.tryLock 0 1, .unlock 0]
  | _ => [.lock 0, .unlock 0]

def codeT9 : Tid → List LOp
  | 0 => [.lock 0, .unlock 0]
  | _ => [.tryLock 0 1, .unlock 0]

def codeT10 : Tid → List LOp
  | 0 => [.lock 0, .unlock 0, .lock 0, .unlock 0]
  | _ => [.tryLock 0 1, .unlock 0, .tryLock 0 1, .unlock 0]

def codeT11 : Tid → List LOp
  | 0 => [.tryLock 0 1, .unlock 0, .tryLock 0 1, .unlock 0]
  | 1 => [.tryLock 0 1, .unlock 0]
  | _ => [.lock 0, .unlock 0]

def codeT12 : Tid → List LOp
  | 0 => [.tryLock 0 1, .unlock 0, .lock 0, .unlock 0]
  | _ => [.lock 0, .unlock 0]

def codeT13 : Tid → List LOp
  | _ => [.tryLock 0 1, .unlock 0, .tryLock 0 1, .unlock 0]

def codeT14 : Tid → List LOp
  | 0 => [.lock 0, .unlock 0, .lock 0, .unlock 0]
  | _ => [.tryLock 0 1, .unlock 0, .tryLock 0 1, .unlock 0, .tryLock 0 1, .unlock 0]

def codeT15 : Tid → List LOp
  | 2 => [.tryLock 0 1, .unlock 0, .tryLock 0 1, .unlock 0]
  | _ => [.lock 0, .unlock 0]

def codeT16 : Tid → List LOp
  | 0 => [.lock 0, .unlock 0]
  | _ => [.tryLock 0 0]

def codeT17 : Tid → List LOp
  | 0 => [.lock 0, .unlock 0]
  | _ => [.lock 0]

def progT7 : XProgram := lockSys [0, 1, 2] (by decide) codeT7 9
def progT8 : XProgram := lockSys [0, 1, 2] (by decide) codeT8 9
def progT9 : XProgram := lockSys [0, 1, 2] (by decide) codeT9 9

def progT10 : XProgram := lockSys [0, 1] (by decide) codeT10 12
def progT11 : XProgram := lockSys [0, 1, 2] (by decide) codeT11 12
def progT12 : XProgram := lockSys [0, 1] (by decide) codeT12 9

def progT13 : XProgram := lockSys [0, 1] (by decide) codeT13 12
def progT14 : XProgram := lockSys [0, 1] (by decide) codeT14 15
def progT15 : XProgram := lockSys [0, 1, 2] (by decide) codeT15 12
def progT16 : XProgram := lockSys [0, 1] (by decide) codeT16 6
def progT17 : XProgram := lockSys [0, 1] (by decide) codeT17 6

/-- T7: three `tryLock`s; no thread blocks. -/
theorem lockT7 : lockReport progT7 9 = (21, 21, true) := by decide +kernel

/-- T8: two `lock`s against a `tryLock`. -/
theorem lockT8 : lockReport progT8 9 = (21, 10, true) := by decide +kernel

/-- T9: a `lock` against two `tryLock`s. -/
theorem lockT9 : lockReport progT9 9 = (21, 15, true) := by decide +kernel

/-- T10: two critical sections against two attempts. -/
theorem lockT10 : lockReport progT10 12 = (21, 15, true) := by decide +kernel

/-- T11: repeated attempts with three threads. -/
theorem lockT11 : lockReport progT11 12 = (62, 44, true) := by decide +kernel

/-- T12: an attempt, then `lock`, in one thread. -/
theorem lockT12 : lockReport progT12 9 = (8, 4, true) := by decide +kernel

/-- T13: repeated attempts on both sides. -/
theorem lockT13 : lockReport progT13 12 = (26, 26, true) := by decide +kernel

/-- T14: two critical sections against three attempts. -/
theorem lockT14 : lockReport progT14 15 = (48, 35, true) := by decide +kernel

/-- T15: two `lock` threads against two attempts. -/
theorem lockT15 : lockReport progT15 12 = (62, 30, true) := by decide +kernel

/-- T16: the thread of the `tryLock` ends holding the lock. In the third
execution the other thread is blocked. -/
theorem lockT16 : lockReport progT16 6 = (3, 2, true) := by decide +kernel

/-- T17: a thread ends holding the lock after `lock`. -/
theorem lockT17 : lockReport progT17 6 = (3, 1, true) := by decide +kernel

/-- The lists are the full consistent executions (from `lockSys_explore`). -/
theorem lockT7_execs : HasExecs progT7 21 := hasExecs_of_count (by decide +kernel)
theorem lockT8_execs : HasExecs progT8 21 := hasExecs_of_count (by decide +kernel)
theorem lockT9_execs : HasExecs progT9 21 := hasExecs_of_count (by decide +kernel)

end Condpor
