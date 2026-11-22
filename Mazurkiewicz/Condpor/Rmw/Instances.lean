import Mazurkiewicz.Condpor.Rmw.ExploreC
import Mazurkiewicz.Condpor.Examples

/-!
# Read-modify-write accesses: programs and computed instances

Programs with exclusive accesses are given by a table of next actions and a
table of flags (`mkXProg`). All counts are computed by the kernel
(`decide +kernel`) on the computed explorer `exploreAt` of `Rmw/ExploreC.lean`
for `SC` with atomicity and the equality solver.

* Fetch-and-add: two threads have 2 executions (4 with a plain read and
  write); three threads have 6.
* A lock as a read-modify-write access with a blocked acquire, the program of
  `plan/condpor/lean/JMC-CHECK.md`: 7 full executions, 4 of them without a
  blocked thread. The variant that lets a deleted constraint evaluation pass
  when the revisiting write is exclusive reports 10, resp. 6.
* Theorem 5(b) of ConDpor as printed fails with read-modify-write accesses:
  `x := 5 ‖ FAA(x) ‖ FAA(x)` and `FAA(x) ‖ c := x ‖ FAA(x)` have a reached
  configuration that is not full and has no step. So have three
  fetch-and-adds and the lock program. Two fetch-and-adds have none
  (`faa2_no_dead`; the computed list of such configurations is complete for a
  bounded program, `exists_dead_iff_deadAt`).
-/

namespace Condpor

open Program

variable {S : Solver} {τ : TieBreak S}

/-! ### Programs with exclusive accesses from a table -/

/-- The kind of the action after the trace `u`, from a table `x` of flags: a
read is exclusive if flagged; a write is exclusive if flagged and it comes
directly after a flagged read of the same location that returned a value. -/
def exFlag (g : Tid → List (Option Val) → Option Act) (x : Tid → List (Option Val) → Bool)
    (t : Tid) (u : List (Option Val)) : Bool :=
  match g t u with
  | some (.read _) => x t u
  | some (.write l _) =>
    x t u && (match u.getLast? with
      | some (some _) => x t u.dropLast && decide (g t u.dropLast = some (.read l))
      | _ => false)
  | _ => false

theorem exFlag_rw {g : Tid → List (Option Val) → Option Act}
    {x : Tid → List (Option Val) → Bool} {t : Tid} {u : List (Option Val)}
    (h : exFlag g x t u = true) : ∃ a, g t u = some a ∧ (a.IsRead ∨ a.IsWrite) := by
  unfold exFlag at h
  cases hs : g t u with
  | none => simp [hs] at h
  | some a =>
    cases a with
    | read l => exact ⟨_, rfl, Or.inl trivial⟩
    | write l v => exact ⟨_, rfl, Or.inr trivial⟩
    | cons φ => simp [hs] at h
    | gen s => simp [hs] at h
    | block => simp [hs] at h
    | error => simp [hs] at h

theorem exFlag_write {g : Tid → List (Option Val) → Option Act}
    {x : Tid → List (Option Val) → Bool} {t : Tid} {u : List (Option Val)} {l : Loc} {v : Val}
    (h : exFlag g x t u = true) (hs : g t u = some (.write l v)) :
    ∃ u₀ a, u = u₀ ++ [some a] ∧ exFlag g x t u₀ = true ∧ g t u₀ = some (.read l) := by
  unfold exFlag at h
  rw [hs] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, h2⟩ := h
  cases hl : u.getLast? with
  | none => simp [hl] at h2
  | some o =>
    cases o with
    | none => simp [hl] at h2
    | some a =>
      simp only [hl, Bool.and_eq_true, decide_eq_true_eq] at h2
      refine ⟨u.dropLast, a, (List.dropLast_append_getLast? _ hl).symm, ?_, h2.2⟩
      unfold exFlag
      rw [h2.2]
      exact h2.1

/-- The program with the table `f` of next actions and the table `x` of
flags. -/
def mkXProg (threads : List Tid) (hnd : threads.Nodup)
    (f : Tid → List (Option Val) → Option Act) (x : Tid → List (Option Val) → Bool)
    (mem : Loc → Val) (n : ℕ) : XProgram where
  toProgram := mkProg threads hnd f mem n
  ex := exFlag (mkProg threads hnd f mem n).step x
  ex_rw := fun _ _ h => exFlag_rw h
  ex_write := fun _ _ _ _ h hs => exFlag_write h hs

theorem mkXProg_bounded (threads : List Tid) (hnd : threads.Nodup)
    (f : Tid → List (Option Val) → Option Act) (x : Tid → List (Option Val) → Bool)
    (mem : Loc → Val) (n : ℕ) : (mkXProg threads hnd f x mem n).toProgram.Bounded n :=
  mkProg_bounded _ _ _ _ _

/-! ### Programs -/

/-- A fetch-and-add on location `0` in every thread. -/
def faaTab : Tid → List (Option Val) → Option Act
  | _, [] => some (.read 0)
  | _, [some v] => some (.write 0 (v + 1))
  | _, _ => none

/-- Two threads with one fetch-and-add each. -/
def faa2 : XProgram := mkXProg [0, 1] (by decide) faaTab (fun _ _ => true) (fun _ => 0) 2

/-- The same two threads with a plain read and a plain write. -/
def rw2 : XProgram := mkXProg [0, 1] (by decide) faaTab (fun _ _ => false) (fun _ => 0) 2

/-- Three threads with one fetch-and-add each. -/
def faa3 : XProgram := mkXProg [0, 1, 2] (by decide) faaTab (fun _ _ => true) (fun _ => 0) 2

/-- `x := 5 ‖ FAA(x) ‖ FAA(x)`. -/
def wfaaTab : Tid → List (Option Val) → Option Act
  | 0, [] => some (.write 0 5)
  | 0, _ => none
  | t, u => faaTab t u

def wfaa2 : XProgram :=
  mkXProg [0, 1, 2] (by decide) wfaaTab (fun t _ => decide (t ≠ 0)) (fun _ => 0) 2

/-- `FAA(x) ‖ c := x ‖ FAA(x)`. -/
def faarTab : Tid → List (Option Val) → Option Act
  | 1, [] => some (.read 0)
  | 1, _ => none
  | t, u => faaTab t u

def faar : XProgram :=
  mkXProg [0, 1, 2] (by decide) faarTab (fun t _ => decide (t ≠ 1)) (fun _ => 0) 2

/-- A lock on location `0`: thread `0` acquires (an exclusive read of `0`;
on `0` an exclusive write of `1`, otherwise it blocks), evaluates `s = 42`
and releases; thread `1` acquires and releases. -/
def lockTab : Tid → List (Option Val) → Option Act
  | _, [] => some (.read 0)
  | _, [some v] => if v = 0 then some (.write 0 1) else some .block
  | 0, [some _, none] => some (.cons (fEq 1 42))
  | 0, [some _, none, some _] => some (.write 0 0)
  | 1, [some _, none] => some (.write 0 0)
  | _, _ => none

def lockProg : XProgram :=
  mkXProg [0, 1] (by decide) lockTab (fun _ u => decide (u.length ≤ 1)) (fun _ => 0) 4

/-! ### A variant of the computed explorer: another test for revisits -/

/-- The steps of the variant with the test `ok` for a revisit. -/
def succsAtV (ok : Config → TEv → TEv → Bool) (P : XProgram) (O : Oracle τ) (c : Config) :
    List Config :=
  match P.nextC c with
  | none => []
  | some e =>
    match e.act with
    | .read x =>
      ((writesOf c.order x).filter (fun w => (c.addRead e w).consX P O)).map (c.addRead e)
    | .write x _ =>
      ((writesOf c.order x).filter (fun wp => (c.addWrite e wp).consX P O)).map (c.addWrite e) ++
        (c.order.filter (fun r => r.readsLoc x)).flatMap (fun r =>
          if ok c r e then
            ((writesOf (c.order.filter (fun d => decide (d ∈ c.keepC r e))) x).filter
              (fun wp => (c.revisitC r e wp).consX P O)).map (c.revisitC r e)
          else [])
    | .cons _ =>
      ([true, false].filter (fun b => (c.addLoc e (some b)).consX P O)).map
        (fun b => c.addLoc e (some b))
    | _ => if (c.addLoc e none).consX P O then [c.addLoc e none] else []

/-- The run of the variant, to depth `f`. -/
def exploreFromAtV (ok : Config → TEv → TEv → Bool) (P : XProgram) (O : Oracle τ) :
    ℕ → Config → List Graph
  | 0, _ => []
  | f + 1, c =>
    if c.consX P O then
      if P.nextC c = none then [c.abs]
      else (succsAtV ok P O c).flatMap (exploreFromAtV ok P O f)
    else []

/-- The graphs that the variant reports. -/
def exploreAtV (ok : Config → TEv → TEv → Bool) (P : XProgram) (O : Oracle τ) (n : ℕ) :
    List Graph :=
  exploreFromAtV ok P O (P.toProgram.bound n + 1) (Config.init P.mem)

theorem exploreFromAtV_std (P : XProgram) (O : Oracle τ) (f : ℕ) (c : Config) :
    exploreFromAtV (fun c r w => c.revisitOKB O.prefB r w) P O f c = exploreFromAt P O f c := by
  induction f generalizing c with
  | zero => rfl
  | succ f ih =>
    unfold exploreFromAtV exploreFromAt
    have h : exploreFromAtV (fun c r w => c.revisitOKB O.prefB r w) P O f =
        exploreFromAt P O f := funext ih
    rw [h]
    rfl

/-- With the test of the algorithm the variant is the computed explorer. -/
theorem exploreAtV_std (P : XProgram) (O : Oracle τ) (n : ℕ) :
    exploreAtV (fun c r w => c.revisitOKB O.prefB r w) P O n = exploreAt P O n :=
  exploreFromAtV_std P O _ _

/-- The test of a revisit in which, when the revisiting write is exclusive, a
deleted constraint evaluation always passes (the omission found in JMC's
`handleLockAcquireWrite`); for other writes, the test of the algorithm. -/
def okNoSymAtEx (P : XProgram) (O : Oracle τ) (c : Config) (r w : TEv) : Bool :=
  if P.ex w.tid (c.trace w.tid) then
    !c.plusPorfB w (.th r) (.th w) &&
      c.order.all (fun d => !(c.deletedB r w d || decide (d = r)) ||
        (decide d.IsCons || c.maxAddedB (O.prefB (c.ctxC r w)) d w))
  else c.revisitOKB O.prefB r w

/-! ### Instances -/

/-- The full consistent executions of `P`, as a list without repetition of
the given length. -/
def HasExecs (P : XProgram) (k : ℕ) : Prop :=
  ∃ l : List Graph, l.Nodup ∧ l.length = k ∧
    ∀ G, G ∈ l ↔ G.Wf ∧ P.toProgram.Exec G ∧
      ((Model.atomic P SC).sym EqSem.solver).cons G ∧ P.toProgram.Full G

theorem hasExecs_of_count {threads : List Tid} {hnd : threads.Nodup}
    {f : Tid → List (Option Val) → Option Act} {x : Tid → List (Option Val) → Bool}
    {mem : Loc → Val} {n k : ℕ}
    (h : (exploreAt (mkXProg threads hnd f x mem n) eqOracleSe n).length = k) :
    HasExecs (mkXProg threads hnd f x mem n) k :=
  ⟨_, (exploreAt_spec eqOracleSe (mkXProg_bounded _ _ _ _ _ _)).1, h,
    (exploreAt_spec eqOracleSe (mkXProg_bounded _ _ _ _ _ _)).2⟩

/-- A reached configuration that is not full and has no step. -/
def HasDead (P : XProgram) : Prop :=
  ∃ d, Reach P.toProgram ((Model.atomic P SC).sym EqSem.solver) (TieBreak.se EqSem.solver) d ∧
    ¬ P.toProgram.Full d.abs ∧
    ¬ ∃ c', Step P.toProgram ((Model.atomic P SC).sym EqSem.solver)
      (TieBreak.se EqSem.solver) d c'

theorem hasDead_of_count {P : XProgram} {n k : ℕ}
    (h : (deadAt P eqOracleSe n).length = k + 1) : HasDead P :=
  exists_dead_of_deadAt eqOracleSe (fun h' => by rw [h'] at h; cases h)

theorem faa2_count : (exploreAt faa2 eqOracleSe 2).length = 2 := by decide +kernel

/-- Two fetch-and-adds: two executions. -/
theorem faa2_two : HasExecs faa2 2 := hasExecs_of_count faa2_count

theorem rw2_count : (exploreAt rw2 eqOracleSe 2).length = 4 := by decide +kernel

/-- The same threads with a plain read and a plain write: four executions. -/
theorem rw2_four : HasExecs rw2 4 := hasExecs_of_count rw2_count

theorem faa3_count : (exploreAt faa3 eqOracleSe 2).length = 6 := by decide +kernel

/-- Three fetch-and-adds: `3!` executions. -/
theorem faa3_six : HasExecs faa3 6 := hasExecs_of_count faa3_count

theorem lock_count : (exploreAt lockProg eqOracleSe 4).length = 7 ∧
    ((exploreAt lockProg eqOracleSe 4).filter
      (fun G => decide (∀ e ∈ G.events, e.act ≠ .block))).length = 4 := by decide +kernel

/-- The lock program: seven full executions, four without a blocked thread
(two orders of the critical sections, two outcomes of the evaluation). -/
theorem lock_seven : HasExecs lockProg 7 := hasExecs_of_count lock_count.1

/-- The variant that lets a deleted constraint evaluation pass at a revisit by
an exclusive write reports ten graphs for the seven executions of the lock
program, six for the four without a blocked thread. -/
theorem lock_variant :
    (exploreAtV (okNoSymAtEx lockProg eqOracleSe) lockProg eqOracleSe 4).length = 10 ∧
    ((exploreAtV (okNoSymAtEx lockProg eqOracleSe) lockProg eqOracleSe 4).filter
      (fun G => decide (∀ e ∈ G.events, e.act ≠ .block))).length = 6 := by decide +kernel

theorem wfaa2_count : (exploreAt wfaa2 eqOracleSe 2).length = 6 ∧
    (deadAt wfaa2 eqOracleSe 2).length = 1 := by decide +kernel

/-- `x := 5 ‖ FAA(x) ‖ FAA(x)` has a reached configuration that is not full
and has no step: Theorem 5(b) of ConDpor fails as printed. -/
theorem wfaa2_dead : HasDead wfaa2 := hasDead_of_count wfaa2_count.2

theorem faar_count : (exploreAt faar eqOracleSe 2).length = 6 ∧
    (deadAt faar eqOracleSe 2).length = 1 := by decide +kernel

/-- `FAA(x) ‖ c := x ‖ FAA(x)` has a reached configuration that is not full
and has no step. -/
theorem faar_dead : HasDead faar := hasDead_of_count faar_count.2

theorem faa3_dead_count : (deadAt faa3 eqOracleSe 2).length = 2 := by decide +kernel

/-- Three fetch-and-adds have such a configuration too. -/
theorem faa3_dead : HasDead faa3 := hasDead_of_count faa3_dead_count

theorem lock_dead_count : (deadAt lockProg eqOracleSe 4).length = 1 := by decide +kernel

/-- And so has the lock program. -/
theorem lock_dead : HasDead lockProg := hasDead_of_count lock_dead_count

theorem not_hasDead_of_count {threads : List Tid} {hnd : threads.Nodup}
    {f : Tid → List (Option Val) → Option Act} {x : Tid → List (Option Val) → Bool}
    {mem : Loc → Val} {n : ℕ}
    (h : (deadAt (mkXProg threads hnd f x mem n) eqOracleSe n).length = 0) :
    ¬ HasDead (mkXProg threads hnd f x mem n) := fun hd =>
  (exists_dead_iff_deadAt eqOracleSe (mkXProg_bounded _ _ _ _ _ _)).mp hd
    (List.length_eq_zero_iff.mp h)

theorem faa2_dead_count : (deadAt faa2 eqOracleSe 2).length = 0 ∧
    (deadAt rw2 eqOracleSe 2).length = 0 := by decide +kernel

/-- Two fetch-and-adds have no reached configuration that is not full and has
no step; nor has the variant with a plain read and write. -/
theorem faa2_no_dead : ¬ HasDead faa2 ∧ ¬ HasDead rw2 :=
  ⟨not_hasDead_of_count faa2_dead_count.1, not_hasDead_of_count faa2_dead_count.2⟩

end Condpor
