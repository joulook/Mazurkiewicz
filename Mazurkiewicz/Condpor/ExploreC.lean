import Mazurkiewicz.Condpor.Compute

/-!
# The computed explorer for sequential consistency with a solver

`Trust/ExploreC.lean` for the symbolic algorithm. An `Oracle τ` computes the
solver and the tie-break: a Boolean satisfiability test and a Boolean choice
of outcomes, with their specifications. `exploreC P O n` is the explorer for
`SC.sym S`, computed; `exploreC_eq`: it is `explore P (SC.sym S) τ n`, as a
list; `exploreC_spec`: for a bounded program it lists, without repetition,
exactly the well-formed, `SC_S`-consistent, full executions.
-/

namespace Condpor

open Program

variable {P : Program} {M : Model} {S : Solver} {τ : TieBreak S}

/-- A computable solver and tie-break. -/
structure Oracle {S : Solver} (τ : TieBreak S) where
  /-- satisfiability, as a test -/
  satB : Finset Lit → Bool
  /-- the test decides satisfiability -/
  satB_iff : ∀ F, satB F = true ↔ S.sat F
  /-- the choice of outcomes, computed -/
  prefB : Finset Lit → Finset Lit → SExpr → Bool
  /-- it is the choice of the tie-break -/
  prefB_eq : ∀ K F φ, prefB K F φ = τ.pref K F φ

/-- Consistency under `SC` with satisfiable constraints, as a test. -/
def Config.consS (O : Oracle τ) (c : Config) : Bool := c.consC && O.satB c.abs.F

theorem Config.consS_iff (O : Oracle τ) (c : Config) (hc : c.abs.Wf) :
    c.consS O = true ↔ (SC.sym S).cons c.abs := by
  unfold Config.consS
  rw [Bool.and_eq_true, Config.consC_iff _ hc, O.satB_iff, Model.sym_cons_iff]

/-! ### When a choice is a step -/

theorem StepL.cons_src {c c' : Config} {e : TEv} {k : Kind} (h : StepL P M τ c e k c') :
    M.cons c.abs := by
  cases k with
  | nr => exact h.nr_inv.1
  | rv r =>
    obtain ⟨wp, -, h', -⟩ := h.rv_inv
    exact h'

theorem StepL.isNext {c c' : Config} {e : TEv} {k : Kind} (h : StepL P M τ c e k c') :
    P.IsNext c.abs e := by
  cases k with
  | nr => exact h.nr_inv.2.1
  | rv r =>
    obtain ⟨wp, -, -, h', -⟩ := h.rv_inv
    exact h'

theorem step_addRead_iff {c : Config} {e : TEv} {x : Loc} {w : Ev} (hnext : P.IsNext c.abs e)
    (hact : e.act = .read x) (hw : c.abs.IsWriteTo x w) :
    Step P M τ c (c.addRead e w) ↔ M.cons c.abs ∧ M.cons (c.addRead e w).abs := by
  constructor
  · rintro ⟨e', k, hs⟩
    exact ⟨hs.cons_src, hs.cons⟩
  · rintro ⟨h1, h2⟩
    exact ⟨e, .nr, StepL.read h1 hnext hact hw h2⟩

theorem step_addWrite_iff {c : Config} {e : TEv} {wp : Ev} (hnext : P.IsNext c.abs e)
    (hew : e.IsWrite) (hwp : c.abs.IsWriteTo e.loc wp) :
    Step P M τ c (c.addWrite e wp) ↔ M.cons c.abs ∧ M.cons (c.addWrite e wp).abs := by
  constructor
  · rintro ⟨e', k, hs⟩
    exact ⟨hs.cons_src, hs.cons⟩
  · rintro ⟨h1, h2⟩
    exact ⟨e, .nr, StepL.write h1 hnext hew hwp h2⟩

theorem step_addLoc_some_iff {c : Config} {e : TEv} {b : Bool} (hnext : P.IsNext c.abs e)
    (hcs : e.IsCons) :
    Step P M τ c (c.addLoc e (some b)) ↔ M.cons c.abs ∧ M.cons (c.addLoc e (some b)).abs := by
  constructor
  · rintro ⟨e', k, hs⟩
    exact ⟨hs.cons_src, hs.cons⟩
  · rintro ⟨h1, h2⟩
    exact ⟨e, .nr, StepL.sym h1 hnext hcs h2⟩

theorem step_addLoc_none_iff {c : Config} {e : TEv} (hnext : P.IsNext c.abs e)
    (hl : e.IsLocal) (hnc : ¬ e.IsCons) :
    Step P M τ c (c.addLoc e none) ↔ M.cons c.abs ∧ M.cons (c.addLoc e none).abs := by
  constructor
  · rintro ⟨e', k, hs⟩
    exact ⟨hs.cons_src, hs.cons⟩
  · rintro ⟨h1, h2⟩
    exact ⟨e, .nr, StepL.loc h1 hnext hl hnc h2⟩

/-- A revisit of `r` by the next event `e` is a step exactly when the tests of
lines 15-17 pass and both graphs are consistent. -/
theorem step_revisit_iff {c : Config} {e r : TEv} {wp : Ev} (hc : c.Wf)
    (hnext : P.IsNext c.abs e) (hew : e.IsWrite) (hr : r ∈ c.order)
    (hract : r.act = .read e.loc)
    (hwp : (c.abs.restrict (c.keep r e)).IsWriteTo e.loc wp) :
    Step P M τ c (c.revisit r e wp) ↔
      (M.cons c.abs ∧ ¬ (c.plus e).porf (.th r) (.th e) ∧
        (∀ d, (c.Deleted r e d ∨ d = r) → c.IsMaximallyAdded τ (c.ctx r e) d e) ∧
        M.cons (c.revisit r e wp).abs) := by
  constructor
  · rintro ⟨e', k, hs⟩
    have hcons' := hs.cons
    have hee : e' = e := isNext_unique hs.isNext hnext
    subst hee
    have heE : e' ∉ c.abs.events :=
      hc.1.not_mem_of_idx_eq_cnt (idx_eq_of_mem_avail hnext.1)
    have hnoe : ∀ q, c.abs.rf q ≠ some (.th e') := fun q h => heE (hc.1.rf_source_mem h).2
    cases k with
    | nr =>
      exfalso
      obtain ⟨-, -, hcase⟩ := hs.nr_inv
      rcases hcase with ⟨x, w, hact, -, -⟩ | ⟨wp', -, -, heq⟩ | ⟨b, hcs, -⟩ | ⟨hl, -, -⟩
      rotate_left 2
      · exact hcs.isLocal.not_isWrite hew
      · exact hl.not_isWrite hew
      · exact TEv.not_isRead_of_isWrite hew (by simp [TEv.IsRead, hact, Act.IsRead])
      · have h' := congrFun (congrArg Config.rf heq) r
        simp only [Config.revisit, Config.addWrite, Graph.setRF_rf, Graph.addWrite_rf,
          Function.update_self] at h'
        exact hnoe r h'.symm
    | rv r' =>
      obtain ⟨wp', heq, hcs, -, -, -, -, hnp, hmax, -⟩ := hs.rv_inv
      have hrr : r' = r := by
        by_contra hne
        have h' := congrFun (congrArg Config.rf heq) r
        simp only [Config.revisit, Graph.setRF_rf, Graph.addWrite_rf, Function.update_self,
          Function.update_of_ne (Ne.symm hne)] at h'
        exact hnoe r (c.abs.restrict_rf_eq_some h'.symm).1
      subst hrr
      exact ⟨hcs, hnp, hmax, hcons'⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨e, .rv r, StepL.revisit h1 hnext hew hr hract h2 h3 hwp h4⟩

/-! ### The computed explorer -/

/-- The steps from `c` under `SC` with the solver, computed (see `succsC_eq`). -/
def succsC (P : Program) (O : Oracle τ) (c : Config) : List Config :=
  match P.nextC c with
  | none => []
  | some e =>
    match e.act with
    | .read x =>
      ((writesOf c.order x).filter (fun w => (c.addRead e w).consS O)).map (c.addRead e)
    | .write x _ =>
      ((writesOf c.order x).filter (fun wp => (c.addWrite e wp).consS O)).map (c.addWrite e) ++
        (c.order.filter (fun r => r.readsLoc x)).flatMap (fun r =>
          if c.revisitOKB O.prefB r e then
            ((writesOf (c.order.filter (fun d => decide (d ∈ c.keepC r e))) x).filter
              (fun wp => (c.revisitC r e wp).consS O)).map (c.revisitC r e)
          else [])
    | .cons _ =>
      ([true, false].filter (fun b => (c.addLoc e (some b)).consS O)).map
        (fun b => c.addLoc e (some b))
    | _ => if (c.addLoc e none).consS O then [c.addLoc e none] else []

/-- `Visit`, computed, to depth `f`. -/
def exploreFromC (P : Program) (O : Oracle τ) : ℕ → Config → List Graph
  | 0, _ => []
  | f + 1, c =>
    if c.consS O then
      if P.nextC c = none then [c.abs] else (succsC P O c).flatMap (exploreFromC P O f)
    else []

/-- The graphs that Algorithm 1 reports for `P` under `SC` with the solver,
computed. -/
def exploreC (P : Program) (O : Oracle τ) (n : ℕ) : List Graph :=
  exploreFromC P O (P.bound n + 1) (Config.init P.mem)

theorem succsC_eq (O : Oracle τ) {c : Config} (hc : c.Wf) (hpo : c.PoLt)
    (hcons : (SC.sym S).cons c.abs) :
    succsC P O c = succs P (SC.sym S) τ c := by
  classical
  unfold succsC succs cands
  cases hnx : P.nextC c with
  | none => rfl
  | some e =>
    have hnext := (nextC_eq_some_iff hc).mp hnx
    have hidx := idx_eq_of_mem_avail hnext.1
    have hlocal : e.IsLocal → ¬ e.IsCons →
        (if (c.addLoc e none).consS O then [c.addLoc e none] else []) =
          [c.addLoc e none].filter (fun c' => decide (Step P (SC.sym S) τ c c')) := by
      intro hl hnc
      have hwf : (c.addLoc e none).abs.Wf := by
        rw [Config.addLoc_abs]
        exact hc.1.addLoc hidx hl (iff_of_false (by simp) hnc)
      have hiff : (c.addLoc e none).consS O = true ↔ Step P (SC.sym S) τ c (c.addLoc e none) := by
        rw [Config.consS_iff O _ hwf, step_addLoc_none_iff hnext hl hnc]
        exact ⟨fun h => ⟨hcons, h⟩, fun h => h.2⟩
      by_cases h : Step P (SC.sym S) τ c (c.addLoc e none)
      · simp [hiff.mpr h, h]
      · have h' : (c.addLoc e none).consS O = false := by
          rw [← Bool.not_eq_true]
          exact fun hb => h (hiff.mp hb)
        simp [h', h]
    cases hact : e.act with
    | read x =>
      simp only [hact]
      rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro w hw
      have hw' : c.abs.IsWriteTo x w := by
        have := mem_writesOf.mp hw
        cases w with
        | init => trivial
        | th q => exact ⟨List.mem_toFinset.mpr this.1, this.2⟩
      have hwf : (c.addRead e w).abs.Wf := by
        rw [Config.addRead_abs]
        exact hc.1.addRead hidx hact hw'
      rw [Function.comp, Bool.eq_iff_iff, decide_eq_true_eq, Config.consS_iff O _ hwf,
        step_addRead_iff hnext hact hw']
      exact ⟨fun h => ⟨hcons, h⟩, fun h => h.2⟩
    | write x v =>
      simp only [hact]
      have hew : e.IsWrite := by simp [TEv.IsWrite, hact, Act.IsWrite]
      have hloc : e.loc = x := by simp [TEv.loc, hact, Act.loc]
      rw [List.filter_append, List.filter_map, List.filter_flatMap]
      congr 1
      · congr 1
        apply List.filter_congr
        intro wp hwp
        have hwp' : c.abs.IsWriteTo e.loc wp := by
          rw [hloc]
          have := mem_writesOf.mp hwp
          cases wp with
          | init => trivial
          | th q => exact ⟨List.mem_toFinset.mpr this.1, this.2⟩
        have hwf : (c.addWrite e wp).abs.Wf := by
          rw [Config.addWrite_abs]
          exact hc.1.addWrite hidx hew hwp'
        rw [Function.comp, Bool.eq_iff_iff, decide_eq_true_eq, Config.consS_iff O _ hwf,
          step_addWrite_iff hnext hew hwp']
        exact ⟨fun h => ⟨hcons, h⟩, fun h => h.2⟩
      · apply List.flatMap_congr
        intro r hr
        obtain ⟨hro, hrx⟩ := List.mem_filter.mp hr
        have hract : r.act = .read e.loc := by
          rw [hloc]
          exact TEv.readsLoc_iff.mp hrx
        have hrev : c.revisitC r e = c.revisit r e := funext (c.revisitC_eq r e)
        rw [hrev, c.keepC_eq]
        have hval : ∀ wp, wp ∈ writesOf (c.order.filter (fun d => decide (d ∈ c.keep r e))) x →
            (c.abs.restrict (c.keep r e)).IsWriteTo e.loc wp := by
          intro wp hwp
          rw [hloc]
          have := mem_writesOf.mp hwp
          cases wp with
          | init => trivial
          | th q =>
            obtain ⟨hq1, hq2⟩ := List.mem_filter.mp this.1
            exact ⟨Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hq1, by simpa using hq2⟩, this.2⟩
        by_cases hok : c.revisitOKB O.prefB r e = true
        · obtain ⟨hnp, hmax⟩ := (c.revisitOKB_iff τ O.prefB_eq hro e).mp hok
          rw [ite_eq_left_of_eq_true _ _ (eq_true hok), List.filter_map]
          congr 1
          apply List.filter_congr
          intro wp hwp
          have hwp' := hval wp hwp
          have hwf : (c.revisit r e wp).abs.Wf :=
            (Config.revisit_wf hc hpo hidx hew hro hract (fun d hd => hmax d (Or.inl hd)) hwp').1
          rw [Function.comp, Bool.eq_iff_iff, decide_eq_true_eq, Config.consS_iff O _ hwf,
            step_revisit_iff hc hnext hew hro hract hwp']
          exact ⟨fun h => ⟨hcons, hnp, hmax, h⟩, fun h => h.2.2.2⟩
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hok)]
          symm
          refine List.filter_eq_nil_iff.mpr (fun c' hc' hstep => ?_)
          obtain ⟨wp, hwp, rfl⟩ := List.mem_map.mp hc'
          have hs := of_decide_eq_true hstep
          obtain ⟨-, hnp, hmax, -⟩ :=
            (step_revisit_iff hc hnext hew hro hract (hval wp hwp)).mp hs
          exact hok ((c.revisitOKB_iff τ O.prefB_eq hro e).mpr ⟨hnp, hmax⟩)
    | cons φ =>
      simp only [hact]
      have hcs : e.IsCons := by simp [TEv.IsCons, hact, Act.IsCons]
      rw [show [c.addLoc e (some true), c.addLoc e (some false)] =
        [true, false].map (fun b => c.addLoc e (some b)) from rfl, List.filter_map]
      congr 1
      apply List.filter_congr
      intro b _
      have hwf : (c.addLoc e (some b)).abs.Wf := by
        rw [Config.addLoc_abs]
        exact hc.1.addLoc hidx hcs.isLocal (iff_of_true rfl hcs)
      rw [Function.comp, Bool.eq_iff_iff, decide_eq_true_eq, Config.consS_iff O _ hwf,
        step_addLoc_some_iff hnext hcs]
      exact ⟨fun h => ⟨hcons, h⟩, fun h => h.2⟩
    | gen s =>
      simp only [hact]
      exact hlocal (by simp [TEv.IsLocal, hact, Act.IsLocal])
        (by simp [TEv.IsCons, hact, Act.IsCons])
    | block =>
      simp only [hact]
      exact hlocal (by simp [TEv.IsLocal, hact, Act.IsLocal])
        (by simp [TEv.IsCons, hact, Act.IsCons])
    | error =>
      simp only [hact]
      exact hlocal (by simp [TEv.IsLocal, hact, Act.IsLocal])
        (by simp [TEv.IsCons, hact, Act.IsCons])

theorem exploreFromC_eq (O : Oracle τ) {c : Config} (hc : Reach P (SC.sym S) τ c) (f : ℕ) :
    exploreFromC P O f c = exploreFrom P (SC.sym S) τ f c := by
  induction f generalizing c with
  | zero => rfl
  | succ f ih =>
    obtain ⟨hcw, hpo, hcons, -⟩ := hc.sound
    unfold exploreFromC exploreFrom
    rw [ite_eq_left_of_eq_true _ _ (eq_true ((c.consS_iff O hcw.1).mpr hcons)),
      ite_eq_left_of_eq_true _ _ (eq_true hcons), succsC_eq O hcw hpo hcons]
    by_cases hnx : P.nextC c = none
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hnx), ite_eq_left_of_eq_true _ _ (eq_true hnx)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hnx), ite_eq_right_of_eq_false _ _ (eq_false hnx)]
      apply List.flatMap_congr
      intro c1 hc1
      exact ih (Relation.ReflTransGen.tail hc ((mem_succs hcw).mp hc1))

/-- The computed explorer is the explorer, as a list. -/
theorem exploreC_eq (P : Program) (O : Oracle τ) (n : ℕ) :
    exploreC P O n = explore P (SC.sym S) τ n :=
  exploreFromC_eq O Relation.ReflTransGen.refl _

/-- The specification of the computed explorer: for a bounded program it
lists, without repetition, exactly the well-formed, SC-consistent, full
executions of the program. -/
theorem exploreC_spec (O : Oracle τ) {n : ℕ} (hn : P.Bounded n) :
    (exploreC P O n).Nodup ∧
      ∀ G, G ∈ exploreC P O n ↔ G.Wf ∧ P.Exec G ∧ (SC.sym S).cons G ∧ P.Full G := by
  rw [exploreC_eq P O]
  exact explore_spec hn SC.extensible

end Condpor
