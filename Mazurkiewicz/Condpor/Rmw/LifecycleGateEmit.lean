import Mazurkiewicz.Condpor.Rmw.LifecycleGateTrace

/-!
# Gate clause 1: emitting one event (LC2-b, part 5)

The effect of the builder primitives on the traces `tr` and on `ExecT`, and the value of the
last write after an occurrence. `step_of_lifeTab`: under an adequate bound, the compiled step
of a listed, not stopped thread is its table entry.
-/

namespace Condpor

namespace Life

namespace Sem

open List

variable {P : LProg}

/-- Under an adequate bound, the compiled step of a listed thread that has not stopped is its
table entry. -/
theorem step_of_lifeTab {n : ℕ} (hn : adequateB P n = true) {t : Tid} (ht : t ∈ P.threads)
    {u : List (Option Val)} (hs : stopped (lifeTab P) t u = false) {a : Act}
    (h : lifeTab P t u = some a) : (lifeSys P n).toProgram.step t u = some a := by
  have hl := lifeTab_length P t u hs (by rw [h]; simp)
  have hb : 2 * (P.code t).length + 3 ≤ n := by
    have := List.all_eq_true.mp hn t ht
    simpa using this
  simp only [lifeSys, mkXProg, mkProg]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp [ht, hs]; omega))]
  exact h

/-- What adding an event of thread `t` with value `v` does to the traces. -/
theorem tr_push {g g' : GB} {t : Tid} {a : Act} {v : Option Val}
    (hL : g'.L = g.L ++ [g.ev t a]) (hret : ∀ e ∈ g.L, retG P g' e = retG P g e)
    (hv : retG P g' (g.ev t a) = v) (t' : Tid) :
    tr P g' t' = tr P g t' ++ (if t = t' then [v] else []) := by
  unfold tr
  rw [thr_append hL, map_append]
  congr 1
  · exact map_congr_left (fun e he => hret e (mem_filter.mp he).1)
  · by_cases h : t = t'
    · subst h; simp [GB.ev, ← hv]
    · simp [GB.ev, h]

theorem retG_readLast {g : GB} (hg : g.Ok) (t : Tid) (x : Loc) :
    (∀ e ∈ g.L, retG P (g.readLast t x) e = retG P g e) ∧
      retG P (g.readLast t x) (g.ev t (.read x)) = some (valE P x (g.last x)) := by
  have hn := hg.not_mem_ev t (.read x)
  refine ⟨fun e he => ?_, ?_⟩
  · have hne : e ≠ g.ev t (.read x) := fun h => hn (h ▸ he)
    simp [retG, GB.readLast, GB.read, GB.push, hne]
  · simp [retG, GB.readLast, GB.read, GB.push, GB.ev]

theorem retG_read {g : GB} (hg : g.Ok) (t : Tid) (x : Loc) (src : Ev) :
    (∀ e ∈ g.L, retG P (g.read t x src) e = retG P g e) ∧
      retG P (g.read t x src) (g.ev t (.read x)) = some (valE P x src) := by
  have hn := hg.not_mem_ev t (.read x)
  refine ⟨fun e he => ?_, ?_⟩
  · have hne : e ≠ g.ev t (.read x) := fun h => hn (h ▸ he)
    simp [retG, GB.read, GB.push, hne]
  · simp [retG, GB.read, GB.push, GB.ev]

theorem retG_write {g : GB} (t : Tid) (x : Loc) (v : Val) :
    (∀ e ∈ g.L, retG P (g.write t x v) e = retG P g e) ∧
      retG P (g.write t x v) (g.ev t (.write x v)) = none := by
  refine ⟨fun e _ => ?_, ?_⟩
  · simp [retG, GB.write, GB.push]
  · simp [retG, GB.ev]

theorem retG_loc0 {g : GB} (t : Tid) (a : Act) (ha : a.IsLocal) :
    (∀ e ∈ g.L, retG P (g.loc0 t a) e = retG P g e) ∧ retG P (g.loc0 t a) (g.ev t a) = none := by
  refine ⟨fun e _ => ?_, ?_⟩
  · simp [retG, GB.loc0, GB.push]
  · cases a <;> simp_all [retG, GB.ev, Act.IsLocal]

/-! ### The four primitives, as one statement each -/

/-- Emitting the read `read x` from `src` (the compiled step of `t`). -/
theorem emit_read {n : ℕ} {g : GB} (hg : g.Ok) (he : ExecT P n g) {t : Tid} {x : Loc} {src : Ev}
    (hs : (lifeSys P n).toProgram.step t (tr P g t) = some (.read x)) :
    ExecT P n (g.read t x src) ∧ ∀ t', tr P (g.read t x src) t' =
      tr P g t' ++ (if t = t' then [some (valE P x src)] else []) := by
  obtain ⟨h1, h2⟩ := retG_read (P := P) hg t x src
  exact ⟨he.push (GB.L_push g _) h1 hs, tr_push (GB.L_push g _) h1 h2⟩

theorem emit_write {n : ℕ} {g : GB} (he : ExecT P n g) {t : Tid} {x : Loc} {v : Val}
    (hs : (lifeSys P n).toProgram.step t (tr P g t) = some (.write x v)) :
    ExecT P n (g.write t x v) ∧ ∀ t', tr P (g.write t x v) t' =
      tr P g t' ++ (if t = t' then [none] else []) := by
  obtain ⟨h1, h2⟩ := retG_write (P := P) (g := g) t x v
  exact ⟨he.push (GB.L_push g _) h1 hs, tr_push (GB.L_push g _) h1 h2⟩

theorem emit_loc0 {n : ℕ} {g : GB} (he : ExecT P n g) {t : Tid} {a : Act} (ha : a.IsLocal)
    (hs : (lifeSys P n).toProgram.step t (tr P g t) = some a) :
    ExecT P n (g.loc0 t a) ∧ ∀ t', tr P (g.loc0 t a) t' =
      tr P g t' ++ (if t = t' then [none] else []) := by
  obtain ⟨h1, h2⟩ := retG_loc0 (P := P) (g := g) t a ha
  exact ⟨he.push (GB.L_push g _) h1 hs, tr_push (GB.L_push g _) h1 h2⟩

/-! ### The value of the last write after an occurrence -/

/-- The value an occurrence writes. -/
def writeVal : Occ → Val
  | .acq _ _ | .tryAcq _ _ _ | .start _ _ => 1
  | .release _ _ => 0
  | .wr _ _ v => v
  | .fin _ => 2
  | _ => 0

theorem last_emit (P : LProg) (g : GB) (o : Occ) (x : Loc) :
    valE P x ((emit P g o).last x) =
      if writeLoc P o = some x then writeVal o else valE P x (g.last x) := by
  cases o <;>
    simp [emit, writeLoc, writeVal, GB.last, GB.readLast, GB.read, GB.write, GB.loc0, GB.push,
      Function.update_apply, valE, GB.ev] <;>
    split_ifs <;> simp_all

end Sem

end Life

end Condpor
