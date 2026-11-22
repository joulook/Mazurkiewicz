import Mazurkiewicz.Condpor.Rmw.Exit
import Mazurkiewicz.Condpor.ExploreC

/-!
# Read-modify-write accesses: the explorer, and the computed explorer for `SC`

* `Rmw.explore_spec`: for a bounded program and a model with `ExtensibleX`,
  the explorer of `Explore.lean` lists, without repetition, exactly the
  well-formed, consistent, full executions.
* `Config.atomicB`: atomicity, computed. `exploreAt P O n`: the explorer for
  `(Model.atomic P SC).sym S`, computed; the text is that of `ExploreC.lean`
  with the consistency test extended by atomicity (generated from it).
-/

namespace Condpor

open Program

variable {P : XProgram} {M : Model} {S : Solver} {τ : TieBreak S}

/-- The specification of the explorer with read-modify-write accesses. -/
theorem Rmw.explore_spec {n : ℕ} (hn : P.toProgram.Bounded n) (hM : ExtensibleX P M) :
    (explore P.toProgram (M.sym S) τ n).Nodup ∧
      ∀ G, G ∈ explore P.toProgram (M.sym S) τ n ↔
        G.Wf ∧ P.toProgram.Exec G ∧ (M.sym S).cons G ∧ P.toProgram.Full G := by
  have h0 : Reach P.toProgram (M.sym S) τ (Config.init P.mem) := Relation.ReflTransGen.refl
  refine ⟨explore_nodup n, fun G => ⟨explore_sound, ?_⟩⟩
  unfold explore
  rw [mem_exploreFrom h0]
  rintro ⟨hW, hE, hc, hfull⟩
  obtain ⟨c, hreach, rfl⟩ := Rmw.complete hn hM hW hE hc hfull
  obtain ⟨p, hp⟩ := Maz.Path.of_reflTransGen hreach
  exact ⟨p, c, hp, Nat.lt_succ_of_le (terminates_bound hn p c hp), hfull, rfl⟩

/-! ### Atomicity, computed -/

namespace Config

/-- `evAt_eq` of `Program.lean` from well-formedness of the graph. -/
theorem evAt_eq' (c : Config) (hc : c.abs.Wf) (t : Tid) (i : ℕ) :
    c.evAt t i = c.abs.evAt t i := by
  unfold evAt
  cases hf : c.order.find? (fun e => decide (e.tid = t ∧ e.idx = i)) with
  | none =>
    cases hg : c.abs.evAt t i with
    | none => rfl
    | some q =>
      obtain ⟨hqm, ht, hi⟩ := Graph.evAt_eq_some_iff_spec hg
      have := List.find?_eq_none.mp hf q (List.mem_toFinset.mp hqm)
      simp [ht, hi] at this
  | some q =>
    have hq := List.find?_some hf
    have hqm := List.mem_of_find?_eq_some hf
    simp only [decide_eq_true_eq] at hq
    exact (Graph.evAt_eq_some_of_inj' hc.idx_inj (List.mem_toFinset.mpr hqm) hq.1 hq.2).symm

/-- The trace of thread `t` before its event number `i`, computed. -/
def traceBeforeC (c : Config) (t : Tid) (i : ℕ) : List (Option Val) :=
  (List.range i).map (fun j => (c.evAt t j).bind c.abs.ret)

theorem traceBeforeC_eq (c : Config) (hc : c.abs.Wf) (t : Tid) (i : ℕ) :
    c.traceBeforeC t i = c.abs.traceBefore t i := by
  unfold traceBeforeC Graph.traceBefore
  apply List.map_congr_left
  intro j _
  rw [evAt_eq' c hc]

end Config

/-- `p` is directly followed by `w` in the list. -/
def adjB : List TEv → TEv → TEv → Bool
  | a :: b :: l, p, w => (decide (a = p) && decide (b = w)) || adjB (b :: l) p w
  | _, _, _ => false

theorem adjB_iff {l : List TEv} {p w : TEv} :
    adjB l p w = true ↔ ∃ l₁ l₂, l = l₁ ++ p :: w :: l₂ := by
  induction l with
  | nil =>
    simp only [adjB, Bool.false_eq_true, false_iff]
    rintro ⟨l₁, l₂, h⟩
    cases l₁ <;> cases h
  | cons a l ih =>
    cases l with
    | nil =>
      simp only [adjB, Bool.false_eq_true, false_iff]
      rintro ⟨l₁, l₂, h⟩
      cases l₁ with
      | nil => cases h
      | cons x l₁ =>
        have := congrArg List.length h
        simp at this
    | cons b l' =>
      simp only [adjB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨h1, h2⟩ | h)
        · exact ⟨[], l', by simp [h1, h2]⟩
        · obtain ⟨l₁, l₂, h'⟩ := ih.mp h
          exact ⟨a :: l₁, l₂, by simp [h']⟩
      · rintro ⟨l₁, l₂, h⟩
        cases l₁ with
        | nil =>
          left
          simp only [List.nil_append, List.cons.injEq] at h
          exact ⟨h.1, h.2.1⟩
        | cons x l₁ =>
          right
          simp only [List.cons_append, List.cons.injEq] at h
          exact ih.mpr ⟨l₁, l₂, h.2⟩

/-- `w` is the immediate successor of `s` in the list. -/
def immCoB (l : List TEv) : Ev → TEv → Bool
  | .init, w => decide (l.head? = some w)
  | .th p, w => adjB l p w

theorem immCoB_iff (G : Graph) (x : Loc) (s : Ev) (w : TEv) :
    immCoB (G.co x) s w = true ↔ G.ImmCo x s w := by
  cases s with
  | init =>
    simp only [immCoB, decide_eq_true_eq, Graph.ImmCo]
    cases G.co x with
    | nil => simp
    | cons a l => simp
  | th p => exact adjB_iff

namespace Config

/-- `(r, w)` is a completed pair, as a test on events of the order. -/
def pairB (P : XProgram) (c : Config) (r w : TEv) : Bool :=
  decide (w.tid = r.tid) && decide (w.idx = r.idx + 1) && decide r.IsRead &&
    decide w.IsWrite && P.ex r.tid (c.traceBeforeC r.tid r.idx) &&
    P.ex w.tid (c.traceBeforeC w.tid w.idx)

theorem pairB_iff (P : XProgram) (c : Config) (hc : c.abs.Wf) {r w : TEv} (hr : r ∈ c.order)
    (hw : w ∈ c.order) : c.pairB P r w = true ↔ P.RMW c.abs r w := by
  unfold pairB XProgram.RMW XProgram.IsEx
  simp only [Bool.and_eq_true, decide_eq_true_eq, traceBeforeC_eq c hc]
  constructor
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    exact ⟨List.mem_toFinset.mpr hr, List.mem_toFinset.mpr hw, h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨-, -, h1, h2, h3, h4, h5, h6⟩
    exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩

/-- Atomicity, as a test. -/
def atomicB (P : XProgram) (c : Config) : Bool :=
  c.order.all fun r => c.order.all fun w =>
    !c.pairB P r w ||
      (match c.rf r with
       | some s => immCoB (c.co w.loc) s w
       | none => true)

theorem atomicB_iff (P : XProgram) (c : Config) (hc : c.abs.Wf) :
    c.atomicB P = true ↔ P.Atomic c.abs := by
  unfold atomicB
  constructor
  · intro h r w hrw s hs
    have hr := List.mem_toFinset.mp hrw.1
    have hw := List.mem_toFinset.mp hrw.2.1
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp h r hr) w hw
    rw [(c.pairB_iff P hc hr hw).mpr hrw] at h1
    have hs' : c.rf r = some s := hs
    rw [hs'] at h1
    simp only [Bool.not_true, Bool.false_or] at h1
    have h2 : immCoB (c.abs.co w.loc) s w = true := h1
    exact (immCoB_iff c.abs _ _ _).mp h2
  · intro h
    refine List.all_eq_true.mpr (fun r hr => List.all_eq_true.mpr (fun w hw => ?_))
    by_cases hp : c.pairB P r w = true
    · rw [hp]
      have hrw := (c.pairB_iff P hc hr hw).mp hp
      cases hs : c.rf r with
      | none => rfl
      | some s =>
        have h2 : immCoB (c.abs.co w.loc) s w = true :=
          (immCoB_iff c.abs _ _ _).mpr (h r w hrw s hs)
        simp only [Bool.not_true, Bool.false_or]
        exact h2
    · rw [Bool.not_eq_true] at hp
      rw [hp]
      rfl

/-- Consistency under `SC` with atomicity and satisfiable constraints, as a
test. -/
def consX (P : XProgram) (O : Oracle τ) (c : Config) : Bool :=
  c.consC && c.atomicB P && O.satB c.abs.F

theorem consX_iff (P : XProgram) (O : Oracle τ) (c : Config) (hc : c.abs.Wf) :
    c.consX P O = true ↔ ((Model.atomic P SC).sym S).cons c.abs := by
  unfold consX
  rw [Bool.and_eq_true, Bool.and_eq_true, Config.consC_iff _ hc, c.atomicB_iff P hc,
    O.satB_iff, Model.sym_cons_iff, Model.atomic_cons_iff]

end Config

/-! ### The computed explorer -/

/-- The steps from `c` under `SC` with atomicity and the solver, computed (see `succsAt_eq`). -/
def succsAt (P : XProgram) (O : Oracle τ) (c : Config) : List Config :=
  match P.nextC c with
  | none => []
  | some e =>
    match e.act with
    | .read x =>
      ((writesOf c.order x).filter (fun w => (c.addRead e w).consX P O)).map (c.addRead e)
    | .write x _ =>
      ((writesOf c.order x).filter (fun wp => (c.addWrite e wp).consX P O)).map (c.addWrite e) ++
        (c.order.filter (fun r => r.readsLoc x)).flatMap (fun r =>
          if c.revisitOKB O.prefB r e then
            ((writesOf (c.order.filter (fun d => decide (d ∈ c.keepC r e))) x).filter
              (fun wp => (c.revisitC r e wp).consX P O)).map (c.revisitC r e)
          else [])
    | .cons _ =>
      ([true, false].filter (fun b => (c.addLoc e (some b)).consX P O)).map
        (fun b => c.addLoc e (some b))
    | _ => if (c.addLoc e none).consX P O then [c.addLoc e none] else []

/-- `Visit`, computed, to depth `f`. -/
def exploreFromAt (P : XProgram) (O : Oracle τ) : ℕ → Config → List Graph
  | 0, _ => []
  | f + 1, c =>
    if c.consX P O then
      if P.nextC c = none then [c.abs] else (succsAt P O c).flatMap (exploreFromAt P O f)
    else []

/-- The graphs that Algorithm 1 reports for `P` under `SC` with atomicity and the solver,
computed. -/
def exploreAt (P : XProgram) (O : Oracle τ) (n : ℕ) : List Graph :=
  exploreFromAt P O (P.toProgram.bound n + 1) (Config.init P.mem)

theorem succsAt_eq (O : Oracle τ) {c : Config} (hc : c.Wf) (hpo : c.PoLt)
    (hcons : ((Model.atomic P SC).sym S).cons c.abs) :
    succsAt P O c = succs P.toProgram ((Model.atomic P SC).sym S) τ c := by
  classical
  unfold succsAt succs cands
  cases hnx : P.nextC c with
  | none => rfl
  | some e =>
    have hnext := (nextC_eq_some_iff hc).mp hnx
    have hidx := idx_eq_of_mem_avail hnext.1
    have hlocal : e.IsLocal → ¬ e.IsCons →
        (if (c.addLoc e none).consX P O then [c.addLoc e none] else []) =
          [c.addLoc e none].filter (fun c' => decide (Step P.toProgram
              ((Model.atomic P SC).sym S) τ c c')) := by
      intro hl hnc
      have hwf : (c.addLoc e none).abs.Wf := by
        rw [Config.addLoc_abs]
        exact hc.1.addLoc hidx hl (iff_of_false (by simp) hnc)
      have hiff : (c.addLoc e none).consX P O = true ↔ Step P.toProgram
          ((Model.atomic P SC).sym S) τ c (c.addLoc e none) := by
        rw [Config.consX_iff P O _ hwf, step_addLoc_none_iff hnext hl hnc]
        exact ⟨fun h => ⟨hcons, h⟩, fun h => h.2⟩
      by_cases h : Step P.toProgram ((Model.atomic P SC).sym S) τ c (c.addLoc e none)
      · simp [hiff.mpr h, h]
      · have h' : (c.addLoc e none).consX P O = false := by
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
      rw [Function.comp, Bool.eq_iff_iff, decide_eq_true_eq, Config.consX_iff P O _ hwf,
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
        rw [Function.comp, Bool.eq_iff_iff, decide_eq_true_eq, Config.consX_iff P O _ hwf,
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
          rw [Function.comp, Bool.eq_iff_iff, decide_eq_true_eq, Config.consX_iff P O _ hwf,
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
      rw [Function.comp, Bool.eq_iff_iff, decide_eq_true_eq, Config.consX_iff P O _ hwf,
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

theorem exploreFromAt_eq (O : Oracle τ) {c : Config} (hc : Reach P.toProgram
    ((Model.atomic P SC).sym S) τ c) (f : ℕ) :
    exploreFromAt P O f c = exploreFrom P.toProgram ((Model.atomic P SC).sym S) τ f c := by
  induction f generalizing c with
  | zero => rfl
  | succ f ih =>
    obtain ⟨hcw, hpo, hcons, -⟩ := hc.sound
    unfold exploreFromAt exploreFrom
    rw [ite_eq_left_of_eq_true _ _ (eq_true ((c.consX_iff P O hcw.1).mpr hcons)),
      ite_eq_left_of_eq_true _ _ (eq_true hcons), succsAt_eq O hcw hpo hcons]
    by_cases hnx : P.nextC c = none
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hnx), ite_eq_left_of_eq_true _ _ (eq_true hnx)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hnx), ite_eq_right_of_eq_false _ _ (eq_false hnx)]
      apply List.flatMap_congr
      intro c1 hc1
      exact ih (Relation.ReflTransGen.tail hc ((mem_succs hcw).mp hc1))

/-- The computed explorer is the explorer, as a list. -/
theorem exploreAt_eq (P : XProgram) (O : Oracle τ) (n : ℕ) :
    exploreAt P O n = explore P.toProgram ((Model.atomic P SC).sym S) τ n :=
  exploreFromAt_eq O Relation.ReflTransGen.refl _

/-- The specification of the computed explorer: for a bounded program it
lists, without repetition, exactly the well-formed, full executions that are SC-consistent
and atomic with satisfiable constraints. -/
theorem exploreAt_spec (O : Oracle τ) {n : ℕ} (hn : P.toProgram.Bounded n) :
    (exploreAt P O n).Nodup ∧
      ∀ G, G ∈ exploreAt P O n ↔ G.Wf ∧ P.toProgram.Exec G ∧
          ((Model.atomic P SC).sym S).cons G ∧ P.toProgram.Full G := by
  rw [exploreAt_eq P O]
  exact Rmw.explore_spec hn (SC.extensibleX P)


/-! ### Configurations that are not full and have no step -/

/-- The reached configurations of the run to depth `f` from `c` that are not
full and have no step, computed. -/
def deadFromAt (P : XProgram) (O : Oracle τ) : ℕ → Config → List Config
  | 0, _ => []
  | f + 1, c =>
    if c.consX P O then
      if P.nextC c = none then []
      else if (succsAt P O c).isEmpty then [c]
      else (succsAt P O c).flatMap (deadFromAt P O f)
    else []

/-- The configurations of the run from the initial one that are not full and
have no step, computed. -/
def deadAt (P : XProgram) (O : Oracle τ) (n : ℕ) : List Config :=
  deadFromAt P O (P.toProgram.bound n + 1) (Config.init P.mem)

theorem mem_deadFromAt (O : Oracle τ) {c : Config}
    (hc : Reach P.toProgram ((Model.atomic P SC).sym S) τ c) (f : ℕ) {d : Config}
    (h : d ∈ deadFromAt P O f c) :
    Reach P.toProgram ((Model.atomic P SC).sym S) τ d ∧ ¬ P.toProgram.Full d.abs ∧
      ¬ ∃ c', Step P.toProgram ((Model.atomic P SC).sym S) τ d c' := by
  induction f generalizing c with
  | zero => simp [deadFromAt] at h
  | succ f ih =>
    obtain ⟨hcw, hpo, hcons, -⟩ := hc.sound
    unfold deadFromAt at h
    rw [ite_eq_left_of_eq_true _ _ (eq_true ((c.consX_iff P O hcw.1).mpr hcons))] at h
    by_cases hnx : P.nextC c = none
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hnx)] at h
      simp at h
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hnx)] at h
      by_cases hemp : (succsAt P O c).isEmpty = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hemp)] at h
        have hd : d = c := List.mem_singleton.mp h
        subst hd
        refine ⟨hc, ?_, ?_⟩
        · intro hf
          obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hnx
          have hav := ((nextC_eq_some_iff hcw).mp he).1
          rw [Program.Full] at hf
          rw [hf] at hav
          simp at hav
        · rintro ⟨c', hs⟩
          have hmem := (mem_succs hcw).mpr hs
          rw [← succsAt_eq O hcw hpo hcons, List.isEmpty_iff.mp hemp] at hmem
          simp at hmem
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hemp)] at h
        obtain ⟨c1, hc1, hd⟩ := List.mem_flatMap.mp h
        rw [succsAt_eq O hcw hpo hcons] at hc1
        exact ih (hc.tail ((mem_succs hcw).mp hc1)) hd

/-- If the computed list is not empty, some reached configuration is not full
and has no step. -/
theorem exists_dead_of_deadAt (O : Oracle τ) {n : ℕ} (h : deadAt P O n ≠ []) :
    ∃ d, Reach P.toProgram ((Model.atomic P SC).sym S) τ d ∧ ¬ P.toProgram.Full d.abs ∧
      ¬ ∃ c', Step P.toProgram ((Model.atomic P SC).sym S) τ d c' := by
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ h
  exact ⟨d, mem_deadFromAt O Relation.ReflTransGen.refl _ hd⟩

/-- The computed list is complete: a configuration that is not full and has no
step, at the end of a run from `c` of length below the depth, is listed. -/
theorem mem_deadFromAt_of_path (O : Oracle τ) {d : Config}
    (hnf : ¬ P.toProgram.Full d.abs)
    (hb : ¬ ∃ c', Step P.toProgram ((Model.atomic P SC).sym S) τ d c') (f : ℕ) :
    ∀ {c : Config} {p : List Config}, Reach P.toProgram ((Model.atomic P SC).sym S) τ c →
      Maz.Path (Step P.toProgram ((Model.atomic P SC).sym S) τ) c p d → p.length < f →
      d ∈ deadFromAt P O f c := by
  induction f with
  | zero => exact fun _ _ h => absurd h (Nat.not_lt_zero _)
  | succ f ih =>
    intro c p hc hp hl
    obtain ⟨hcw, hpo, hcons, -⟩ := hc.sound
    unfold deadFromAt
    rw [ite_eq_left_of_eq_true _ _ (eq_true ((c.consX_iff P O hcw.1).mpr hcons))]
    cases hp with
    | nil =>
      have hnx : ¬ P.nextC d = none := fun h => hnf ((nextC_eq_none_iff hcw).mp h)
      have hemp : (succsAt P O d).isEmpty = true := by
        rw [List.isEmpty_iff]
        by_contra hne
        obtain ⟨c1, hc1⟩ := List.exists_mem_of_ne_nil _ hne
        rw [succsAt_eq O hcw hpo hcons] at hc1
        exact hb ⟨c1, (mem_succs hcw).mp hc1⟩
      rw [ite_eq_right_of_eq_false _ _ (eq_false hnx), ite_eq_left_of_eq_true _ _ (eq_true hemp)]
      exact List.mem_singleton.mpr rfl
    | @cons _ c1 _ p' hstep hrest =>
      have hnx : ¬ P.nextC c = none := fun h => hstep.not_full ((nextC_eq_none_iff hcw).mp h)
      have hmem : c1 ∈ succsAt P O c := by
        rw [succsAt_eq O hcw hpo hcons]
        exact (mem_succs hcw).mpr hstep
      have hemp : ¬ (succsAt P O c).isEmpty = true := by
        rw [List.isEmpty_iff]
        exact List.ne_nil_of_mem hmem
      rw [ite_eq_right_of_eq_false _ _ (eq_false hnx), ite_eq_right_of_eq_false _ _ (eq_false hemp)]
      exact List.mem_flatMap.mpr ⟨c1, hmem,
        ih (hc.tail hstep) hrest (Nat.lt_of_succ_lt_succ hl)⟩

/-- For a bounded program, some reached configuration is not full and has no
step exactly if the computed list is not empty. -/
theorem exists_dead_iff_deadAt (O : Oracle τ) {n : ℕ} (hn : P.toProgram.Bounded n) :
    (∃ d, Reach P.toProgram ((Model.atomic P SC).sym S) τ d ∧ ¬ P.toProgram.Full d.abs ∧
      ¬ ∃ c', Step P.toProgram ((Model.atomic P SC).sym S) τ d c') ↔ deadAt P O n ≠ [] := by
  constructor
  · rintro ⟨d, hd, hnf, hb⟩
    obtain ⟨p, hp⟩ := Maz.Path.of_reflTransGen hd
    exact List.ne_nil_of_mem (mem_deadFromAt_of_path O hnf hb _ Relation.ReflTransGen.refl hp
      (Nat.lt_succ_of_le (terminates_bound hn p d hp)))
  · exact exists_dead_of_deadAt O

end Condpor
