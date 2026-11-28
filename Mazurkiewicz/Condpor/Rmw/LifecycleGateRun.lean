import Mazurkiewicz.Condpor.Rmw.LifecycleGateGB
import Mazurkiewicz.Condpor.Rmw.LifecycleLemmas

/-!
# Thread lifecycle machine: the graph of a maximal run is well-formed and SC (LC2-b, part 3)

* `emit_ok`, `foldl_emit_ok`, `finalize_ok`: the builder invariant `GB.Ok` along a run and
  through the synthetic events (the read of a never-started thread from `init` needs that its
  lifecycle location has no write).
* `MInv`: a machine invariant along runs of a fragment program: the remaining calls are a
  suffix of the code; a thread that is not new is started; a thread that is not started has
  no write of its lifecycle location in the graph so far. `MInv.step`: preserved by steps.
* `runCfg_wf_sc`: for a fragment program, the graph of every maximal run is well-formed and
  SC-consistent, and its literals are satisfiable (there are none) — the `Wf` and the SC part
  of gate clause 1.
-/

namespace Condpor

namespace Life

namespace Sem

open List

variable {P : LProg}

/-! ### The builder invariant along a run -/

theorem emit_ok (P : LProg) {g : GB} (hg : g.Ok) (o : Occ) : (emit P g o).Ok := by
  have hl : ∀ a : Act, a = .gen 0 ∨ a = .block ∨ a = .error → a.IsLocal ∧ ¬ a.IsCons := by
    rintro a (rfl | rfl | rfl) <;> simp [Act.IsLocal, Act.IsCons]
  cases o <;> simp only [emit]
  all_goals first
    | exact hg.readLast _ _
    | exact (hg.readLast _ _).write _ _ _
    | exact hg.write _ _ _
    | exact hg.loc0 _ _ (hl _ (by simp)).1 (hl _ (by simp)).2
    | exact (hg.readLast _ _).loc0 _ _ (hl _ (by simp)).1 (hl _ (by simp)).2

theorem foldl_emit_ok (P : LProg) {g : GB} (hg : g.Ok) (rs : List Occ) :
    (rs.foldl (emit P) g).Ok := by
  induction rs generalizing g with
  | nil => exact hg
  | cons o rs ih => exact ih (emit_ok P hg o)

theorem synth_co (P : LProg) (s : MState) (g : GB) (t : Tid) : (synth P s g t).co = g.co := by
  unfold synth
  split
  · rfl
  · split
    · split_ifs <;> rfl
    · split_ifs <;> rfl
    · rfl
  · rfl

theorem synth_ok (P : LProg) (s : MState) {g : GB} (hg : g.Ok) (t : Tid)
    (hnew : s.status t = .new → g.co (P.st t) = []) : (synth P s g t).Ok := by
  have hb : Act.block.IsLocal ∧ ¬ Act.block.IsCons := by simp [Act.IsLocal, Act.IsCons]
  unfold synth
  split
  next h => exact (hg.read_init _ _ (hnew h)).loc0 _ _ hb.1 hb.2
  · split
    · split_ifs
      · exact (hg.readLast _ _).loc0 _ _ hb.1 hb.2
      · exact hg
    · split_ifs
      · exact (hg.readLast _ _).loc0 _ _ hb.1 hb.2
      · exact hg
    · exact hg
  · exact hg

theorem finalize_ok (P : LProg) (s : MState) {g : GB} (hg : g.Ok)
    (hnew : ∀ t ∈ P.threads, s.status t = .new → g.co (P.st t) = []) :
    (finalize P g s).Ok := by
  unfold finalize
  suffices ∀ (l : List Tid) (g : GB), g.Ok → (∀ t ∈ l, s.status t = .new → g.co (P.st t) = []) →
      (l.foldl (synth P s) g).Ok from this _ g hg hnew
  intro l
  induction l with
  | nil => intro g hg _; exact hg
  | cons t l ih =>
    intro g hg h
    refine ih _ (synth_ok P s hg t (h t mem_cons_self)) ?_
    intro t' ht' hn
    rw [synth_co]
    exact h t' (mem_cons_of_mem _ ht') hn

/-! ### Locations written by an occurrence -/

/-- The location an occurrence writes, if any. -/
def writeLoc (P : LProg) : Occ → Option Loc
  | .acq _ l | .tryAcq _ l _ | .release _ l => some l
  | .wr _ x _ => some x
  | .start _ u => some (P.st u)
  | .fin t => some (P.st t)
  | _ => none

theorem emit_co (P : LProg) (g : GB) (o : Occ) {x : Loc} (hx : writeLoc P o ≠ some x) :
    (emit P g o).co x = g.co x := by
  cases o <;> simp only [writeLoc, ne_eq, Option.some.injEq] at hx <;>
    simp [emit, GB.readLast, GB.read, GB.write, GB.loc0, GB.push, Function.update_apply,
      Ne.symm hx]

/-! ### The machine invariant -/

/-- The machine invariant used for the never-started threads. -/
structure MInv (P : LProg) (s : MState) (g : GB) : Prop where
  suffix : ∀ t, s.rest t <:+ P.code t
  started_of : ∀ t, s.status t ≠ .new → s.started t = true
  life : ∀ t ∈ P.threads, s.started t = false → g.co (P.st t) = []

theorem minv_init (P : LProg) : MInv P (MState.init P) GB.empty where
  suffix := fun t => suffix_refl _
  started_of := by
    intro t h
    simp only [MState.init] at h ⊢
    split_ifs at h with hr
    · exact hr
    · exact absurd rfl h
  life := by simp [GB.empty]

/-- The head call of a thread is a call of its code. -/
theorem MInv.head_mem {s : MState} {g : GB} (hm : MInv P s g) {t : Tid} {c : TOp}
    (h : (s.rest t).head? = some c) : c ∈ P.code t :=
  (hm.suffix t).subset (mem_of_mem_head? h)

theorem MInv.step (hF : Frag P) {s s' : MState} {g : GB} {o : Occ} (hm : MInv P s g)
    (h : Step P s o s') : MInv P s' (emit P g o) := by
  obtain ⟨he, rfl⟩ := h
  have hok : ∀ {t c}, t ∈ P.threads → (s.rest t).head? = some c → callOk P t c = true :=
    fun ht hc => hF.calls _ ht _ (hm.head_mem hc)
  refine ⟨?_, ?_, ?_⟩
  · intro t
    have hs := hm.suffix t
    cases he <;> simp only [eff, MState.adv, MState.setSt, Function.update_apply] <;>
      (try split_ifs) <;> subst_vars <;>
      first
      | exact hs
      | exact (tail_suffix _).trans hs
      | exact ((drop_suffix _ _).trans (tail_suffix _)).trans hs
  · intro t ht
    have h1 := hm.started_of t
    cases he <;> simp only [eff, MState.adv, MState.setSt, Function.update_apply] at ht ⊢ <;>
      (try split_ifs at ht ⊢) <;> subst_vars <;> simp_all
  · intro t ht hst
    -- the started flag only grows
    have hst0 : s.started t = false := by
      cases he <;> simp only [eff, MState.adv, MState.setSt, Function.update_apply] at hst <;>
        (try split_ifs at hst) <;> simp_all
    have hco := hm.life t ht hst0
    rw [emit_co P g o, hco]
    intro hw
    have hnl : P.isLock (P.st t) = false := hF.st_not_lock t ht
    cases he <;> simp only [writeLoc, Option.some.injEq, reduceCtorEq] at hw
    case acq t0 l0 ht0 _ hc0 _ _ =>
      have := hok ht0 hc0
      simp only [callOk] at this
      rw [hw] at this; rw [this] at hnl; cases hnl
    case tryAcq t0 l0 k0 ht0 _ hc0 _ _ =>
      have := hok ht0 hc0
      simp only [callOk] at this
      rw [hw] at this; rw [this] at hnl; cases hnl
    case release t0 l0 ht0 _ hc0 _ _ =>
      have := hok ht0 hc0
      simp only [callOk] at this
      rw [hw] at this; rw [this] at hnl; cases hnl
    case wr t0 x0 v0 ht0 _ hc0 =>
      have := hok ht0 hc0
      simp only [callOk] at this
      rw [hw, hF.isData_st ht] at this; cases this
    case start t0 u ht0 _ hc0 =>
      have := hok ht0 hc0
      simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at this
      have hu := hF.st_inj u this.1.1 t ht hw
      subst hu
      simp [eff, MState.adv] at hst
    case fin t0 ht0 hs0 _ =>
      have hu := hF.st_inj t0 ht0 t ht hw
      subst hu
      have := hm.started_of t0 (by rw [hs0]; simp)
      rw [this] at hst0
      cases hst0

theorem MInv.steps (hF : Frag P) {s s' : MState} {g : GB} {rs : List Occ} (hm : MInv P s g)
    (h : Steps P s rs s') : MInv P s' (rs.foldl (emit P) g) := by
  induction h generalizing g with
  | nil => exact hm
  | cons h _ ih => exact ih (hm.step hF h)

/-! ### Well-formedness and SC of the graph of a maximal run -/

theorem runCfg_ok (hF : Frag P) {rs : List Occ} {s : MState} (hr : MaxRun P rs s) :
    (finalize P (rs.foldl (emit P) GB.empty) s).Ok := by
  have hm := (minv_init P).steps hF hr.1
  refine finalize_ok P s (foldl_emit_ok P ok_empty rs) ?_
  intro t ht hn
  refine hm.life t ht ?_
  cases h : s.started t
  · rfl
  · exact absurd (Enabled.begin ht hn h) (hr.2 _)

theorem runCfg_F (rs : List Occ) (s : MState) : (runCfg P rs s).abs.F = ∅ := by
  simp only [Graph.F, Graph.lit, runCfg, GB.toCfg, Config.abs]
  ext l
  simp

/-- **Gate clause 1, the `Wf` and SC parts**: the graph of a maximal run of a fragment
program is well-formed, SC-consistent, and its literals are satisfiable. -/
theorem runCfg_wf_sc (hF : Frag P) {rs : List Occ} {s : MState} (hr : MaxRun P rs s) :
    (runCfg P rs s).Wf ∧ SC.cons (runCfg P rs s).abs ∧ EqSem.solver.sat (runCfg P rs s).abs.F := by
  have hok := runCfg_ok hF hr
  refine ⟨hok.wf P, hok.sc P, ?_⟩
  rw [runCfg_F]
  exact EqSem.solver.sat_empty

end Sem

end Life

end Condpor
