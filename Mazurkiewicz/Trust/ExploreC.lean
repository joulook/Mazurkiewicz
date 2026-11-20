import Mazurkiewicz.Trust.Compute

/-!
# The explorer, computed

`exploreC P n` is `explore P SC n` (`Trust/Explore.lean`) with the tests done
by the functions of `Trust/Compute.lean`. It is computable, and it is the
same list: `exploreC_eq`. So the specification of `explore` holds for it
(`exploreC_spec`), and it can be run on examples.

* `succsC` lists, for each choice of Algorithm 1 at `c`, the result when the
  tests pass: consistency of the new graph (line 4 of the call), and for a
  revisit first the tests of lines 15-17 (`Config.revisitOKB`).
* `succsC_eq`: on a well-formed, consistent configuration whose insertion
  order extends the program order (every reached configuration is one),
  `succsC P c = succs P SC c`, as lists.
* `exploreFromC_eq`, `exploreC_eq`: the traversals agree, as lists.
-/

namespace Trust

open Program

variable {P : Program} {M : Model}

/-! ### When a choice is a step -/

theorem StepL.cons_src {c c' : Config} {e : TEv} {k : Kind} (h : StepL P M c e k c') :
    M.cons c.abs := by
  cases k with
  | nr => exact h.nr_inv.1
  | rv r =>
    obtain ⟨wp, -, h', -⟩ := h.rv_inv
    exact h'

theorem StepL.isNext {c c' : Config} {e : TEv} {k : Kind} (h : StepL P M c e k c') :
    P.IsNext c.abs e := by
  cases k with
  | nr => exact h.nr_inv.2.1
  | rv r =>
    obtain ⟨wp, -, -, h', -⟩ := h.rv_inv
    exact h'

theorem step_addRead_iff {c : Config} {e : TEv} {x : Loc} {w : Ev} (hnext : P.IsNext c.abs e)
    (hact : e.act = .read x) (hw : c.abs.IsWriteTo x w) :
    Step P M c (c.addRead e w) ↔ M.cons c.abs ∧ M.cons (c.addRead e w).abs := by
  constructor
  · rintro ⟨e', k, hs⟩
    exact ⟨hs.cons_src, hs.cons⟩
  · rintro ⟨h1, h2⟩
    exact ⟨e, .nr, StepL.read h1 hnext hact hw h2⟩

theorem step_addWrite_iff {c : Config} {e : TEv} {wp : Ev} (hnext : P.IsNext c.abs e)
    (hew : e.IsWrite) (hwp : c.abs.IsWriteTo e.loc wp) :
    Step P M c (c.addWrite e wp) ↔ M.cons c.abs ∧ M.cons (c.addWrite e wp).abs := by
  constructor
  · rintro ⟨e', k, hs⟩
    exact ⟨hs.cons_src, hs.cons⟩
  · rintro ⟨h1, h2⟩
    exact ⟨e, .nr, StepL.write h1 hnext hew hwp h2⟩

/-- A revisit of `r` by the next event `e` is a step exactly when the tests of
lines 15-17 pass and both graphs are consistent. -/
theorem step_revisit_iff {c : Config} {e r : TEv} {wp : Ev} (hc : c.Wf)
    (hnext : P.IsNext c.abs e) (hew : e.IsWrite) (hr : r ∈ c.order)
    (hract : r.act = .read e.loc)
    (hwp : (c.abs.restrict (c.keep r e)).IsWriteTo e.loc wp) :
    Step P M c (c.revisit r e wp) ↔
      (M.cons c.abs ∧ ¬ (c.plus e).porf (.th r) (.th e) ∧
        (∀ d, (c.Deleted r e d ∨ d = r) → c.IsMaximallyAdded d e) ∧
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
      rcases hcase with ⟨x, w, hact, -, -⟩ | ⟨wp', -, -, heq⟩
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

/-- The steps from `c` under SC, computed (see `succsC_eq`). -/
def succsC (P : Program) (c : Config) : List Config :=
  match P.nextC c with
  | none => []
  | some e =>
    match e.act with
    | .read x =>
      ((writesOf c.order x).filter (fun w => (c.addRead e w).consC)).map (c.addRead e)
    | .write x _ =>
      ((writesOf c.order x).filter (fun wp => (c.addWrite e wp).consC)).map (c.addWrite e) ++
        (c.order.filter (fun r => r.readsLoc x)).flatMap (fun r =>
          if c.revisitOKB r e then
            ((writesOf (c.order.filter (fun d => decide (d ∈ c.keepC r e))) x).filter
              (fun wp => (c.revisitC r e wp).consC)).map (c.revisitC r e)
          else [])

/-- `Visit` under SC, computed, to depth `f`. -/
def exploreFromC (P : Program) : ℕ → Config → List Graph
  | 0, _ => []
  | f + 1, c =>
    if c.consC then
      if P.nextC c = none then [c.abs] else (succsC P c).flatMap (exploreFromC P f)
    else []

/-- The graphs that Algorithm 1 reports for `P` under SC, computed. -/
def exploreC (P : Program) (n : ℕ) : List Graph :=
  exploreFromC P (P.bound n + 1) (Config.init P.mem)

theorem succsC_eq {c : Config} (hc : c.Wf) (hpo : c.PoLt) (hcons : SC.cons c.abs) :
    succsC P c = succs P SC c := by
  classical
  unfold succsC succs cands
  cases hnx : P.nextC c with
  | none => rfl
  | some e =>
    have hnext := (nextC_eq_some_iff hc).mp hnx
    have hidx := idx_eq_of_mem_avail hnext.1
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
      rw [Function.comp, Bool.eq_iff_iff, decide_eq_true_eq, Config.consC_iff _ hwf,
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
        rw [Function.comp, Bool.eq_iff_iff, decide_eq_true_eq, Config.consC_iff _ hwf,
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
        by_cases hok : c.revisitOKB r e = true
        · obtain ⟨hnp, hmax⟩ := (c.revisitOKB_iff hro e).mp hok
          rw [ite_eq_left_of_eq_true _ _ (eq_true hok), List.filter_map]
          congr 1
          apply List.filter_congr
          intro wp hwp
          have hwp' := hval wp hwp
          have hwf : (c.revisit r e wp).abs.Wf :=
            (Config.revisit_wf hc hpo hidx hew hro hract (fun d hd => hmax d (Or.inl hd)) hwp').1
          rw [Function.comp, Bool.eq_iff_iff, decide_eq_true_eq, Config.consC_iff _ hwf,
            step_revisit_iff hc hnext hew hro hract hwp']
          exact ⟨fun h => ⟨hcons, hnp, hmax, h⟩, fun h => h.2.2.2⟩
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hok)]
          symm
          refine List.filter_eq_nil_iff.mpr (fun c' hc' hstep => ?_)
          obtain ⟨wp, hwp, rfl⟩ := List.mem_map.mp hc'
          have hs := of_decide_eq_true hstep
          obtain ⟨-, hnp, hmax, -⟩ :=
            (step_revisit_iff hc hnext hew hro hract (hval wp hwp)).mp hs
          exact hok ((c.revisitOKB_iff hro e).mpr ⟨hnp, hmax⟩)

theorem exploreFromC_eq {c : Config} (hc : Reach P SC c) (f : ℕ) :
    exploreFromC P f c = exploreFrom P SC f c := by
  induction f generalizing c with
  | zero => rfl
  | succ f ih =>
    obtain ⟨hcw, hpo, hcons, -⟩ := hc.sound
    unfold exploreFromC exploreFrom
    rw [ite_eq_left_of_eq_true _ _ (eq_true ((c.consC_iff hcw.1).mpr hcons)),
      ite_eq_left_of_eq_true _ _ (eq_true hcons), succsC_eq hcw hpo hcons]
    by_cases hnx : P.nextC c = none
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hnx), ite_eq_left_of_eq_true _ _ (eq_true hnx)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hnx), ite_eq_right_of_eq_false _ _ (eq_false hnx)]
      apply List.flatMap_congr
      intro c1 hc1
      exact ih (hc.tail ((mem_succs hcw).mp hc1))

/-- The computed explorer is the explorer, as a list. -/
theorem exploreC_eq (P : Program) (n : ℕ) : exploreC P n = explore P SC n :=
  exploreFromC_eq Relation.ReflTransGen.refl _

/-- The specification of the computed explorer: for a bounded program it
lists, without repetition, exactly the well-formed, SC-consistent, full
executions of the program. -/
theorem exploreC_spec {n : ℕ} (hn : P.Bounded n) :
    (exploreC P n).Nodup ∧
      ∀ G, G ∈ exploreC P n ↔ G.Wf ∧ P.Exec G ∧ SC.cons G ∧ P.Full G := by
  rw [exploreC_eq]
  exact explore_spec hn SC.extensible

/-! ### Running the explorer

`#guard` evaluates its argument with the compiler when the file is built and
fails the build if it is not `true`. These are tests, not theorems; what is
proved about `exploreC` is `exploreC_spec`. -/

namespace Examples

set_option linter.hashCommand false

-- `w+w+rr` (Fig. 4): four graphs
#guard (exploreC wwrr 2).length == 4
-- the same program with the threads numbered the other way
#guard (exploreC wwrrRev 2).length == 4
-- `r+w+w` (Fig. 8): six graphs
#guard (exploreC rww 2).length == 6
-- `r+ww` (Fig. 9): the read sees the initial value, 1 or 2
#guard (exploreC rwwSeq 2).length == 3
-- the program of the checked run: the read sees the initial value or 2
#guard (exploreC revProg 2).length == 2
-- a thread that writes the value it read: one graph
#guard (exploreC copy 2).length == 1
-- the empty program: the initial graph
#guard (exploreC emptyP 0).length == 1

end Examples

end Trust
