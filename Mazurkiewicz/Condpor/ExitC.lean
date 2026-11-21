import Mazurkiewicz.Condpor.Concolic

/-!
# The visited configurations, and the explorer with exit

* `visitC P O n`: the configurations that the computed explorer visits, in the
  order of the depth-first run. `mem_visitC`: they are exactly the reached
  configurations.
* `exploreX P O EO n`: the result of the run that exits at the first erroneous
  graph it visits: `inl G` for that graph, or `inr l` for the list of full
  executions if no visited graph is erroneous. It is defined from the list of
  visits (the first erroneous one), which is what the run with exit returns.
  - `exploreX_err`: a reported graph is erroneous and is the graph of a
    reached configuration (so it is a well-formed consistent execution);
  - `exploreX_ok`: if a list is reported, no reached configuration is
    erroneous, and the list is the list of all full consistent executions,
    without repetition;
  - `exploreX_finds`: if some consistent execution of the program is
    erroneous, an erroneous graph is reported.
* Example 1 of the paper on the reached configurations: a revisit of the read
  of `x` by the write of `x` starts only from a configuration in which the
  constraint has the outcome `s = 42` (exploration B), and there is such a
  step.
* Fig. 1: the six executions are the six graphs of the figure: the read of
  `y` from `init`, or from the write with the outcome `s = 42` or `s ≠ 42`,
  and the read of `x` from `init` or from the write.
-/

namespace Condpor

open Program

variable {P : Program} {S : Solver} {τ : TieBreak S}

/-- The configurations visited from `c`, to depth `f`. -/
def visitFromC (P : Program) (O : Oracle τ) : ℕ → Config → List Config
  | 0, _ => []
  | f + 1, c =>
    if c.consS O then c :: (succsC P O c).flatMap (visitFromC P O f) else []

/-- The configurations that the computed explorer visits. -/
def visitC (P : Program) (O : Oracle τ) (n : ℕ) : List Config :=
  visitFromC P O (P.bound n + 1) (Config.init P.mem)

theorem mem_visitFromC (O : Oracle τ) {c : Config} (hc : Reach P (SC.sym S) τ c) (f : ℕ)
    (c' : Config) :
    c' ∈ visitFromC P O f c ↔
      ∃ p, Maz.Path (Step P (SC.sym S) τ) c p c' ∧ p.length < f := by
  induction f generalizing c with
  | zero =>
    simp only [visitFromC, List.not_mem_nil, false_iff]
    rintro ⟨p, -, h⟩
    exact Nat.not_lt_zero _ h
  | succ f ih =>
    obtain ⟨hcw, hpo, hcons, -⟩ := hc.sound
    unfold visitFromC
    rw [ite_eq_left_of_eq_true _ _ (eq_true ((c.consS_iff O hcw.1).mpr hcons)), List.mem_cons,
      List.mem_flatMap, succsC_eq O hcw hpo hcons]
    constructor
    · rintro (rfl | ⟨c1, hc1, h⟩)
      · exact ⟨[], Maz.Path.nil _, Nat.succ_pos _⟩
      · have hstep := (mem_succs hcw).mp hc1
        obtain ⟨p, hp, hl⟩ := (ih (Relation.ReflTransGen.tail hc hstep)).mp h
        exact ⟨c1 :: p, Maz.Path.cons hstep hp, Nat.succ_lt_succ hl⟩
    · rintro ⟨p, hp, hl⟩
      cases hp with
      | nil => exact Or.inl rfl
      | @cons _ c1 _ p' hstep hrest =>
        exact Or.inr ⟨c1, (mem_succs hcw).mpr hstep,
          (ih (Relation.ReflTransGen.tail hc hstep)).mpr
            ⟨p', hrest, Nat.lt_of_succ_lt_succ hl⟩⟩

/-- The visited configurations are the reached ones. -/
theorem mem_visitC (O : Oracle τ) {n : ℕ} (hn : P.Bounded n) (c : Config) :
    c ∈ visitC P O n ↔ Reach P (SC.sym S) τ c := by
  unfold visitC
  rw [mem_visitFromC O Relation.ReflTransGen.refl]
  constructor
  · rintro ⟨p, hp, -⟩
    exact hp.reflTransGen
  · intro hc
    obtain ⟨p, hp⟩ := Maz.Path.of_reflTransGen hc
    exact ⟨p, hp, Nat.lt_succ_of_le (terminates_bound (M := SC) hn p c hp)⟩

/-! ### The explorer with exit -/

/-- A computable error predicate. -/
structure ErrOracle (E : ErrPred) where
  /-- the test -/
  errB : Graph → Bool
  /-- it decides the predicate -/
  errB_iff : ∀ G, errB G = true ↔ E.isErr G

/-- The test for an `error` event. -/
def ErrOracle.label : ErrOracle ErrPred.label where
  errB := fun G => decide (∃ e ∈ G.events, e.act = .error)
  errB_iff := fun _ => decide_eq_true_iff

variable {E : ErrPred}

/-- The result of the run with exit: the first erroneous graph visited, or the
list of the full executions. -/
def exploreX (P : Program) (O : Oracle τ) (EO : ErrOracle E) (n : ℕ) : Graph ⊕ List Graph :=
  match (visitC P O n).find? (fun c => EO.errB c.abs) with
  | some c => .inl c.abs
  | none => .inr (exploreC P O n)

/-- A reported graph is erroneous, and it is the graph of a reached
configuration. -/
theorem exploreX_err (O : Oracle τ) (EO : ErrOracle E) {n : ℕ} (hn : P.Bounded n) {G : Graph}
    (h : exploreX P O EO n = .inl G) :
    E.isErr G ∧ ∃ c, Reach P (SC.sym S) τ c ∧ c.abs = G := by
  unfold exploreX at h
  cases hf : (visitC P O n).find? (fun c => EO.errB c.abs) with
  | none => rw [hf] at h; cases h
  | some c =>
    rw [hf] at h
    have hG : c.abs = G := Sum.inl.inj h
    have h1 := List.find?_some hf
    have h2 := List.mem_of_find?_eq_some hf
    exact ⟨hG ▸ (EO.errB_iff _).mp h1, c, (mem_visitC O hn c).mp h2, hG⟩

/-- If a list is reported, no reached configuration is erroneous, and the
list is that of the full consistent executions, without repetition. -/
theorem exploreX_ok (O : Oracle τ) (EO : ErrOracle E) {n : ℕ} (hn : P.Bounded n)
    {l : List Graph} (h : exploreX P O EO n = .inr l) :
    (∀ c, Reach P (SC.sym S) τ c → ¬ E.isErr c.abs) ∧ l.Nodup ∧
      ∀ G, G ∈ l ↔ G.Wf ∧ P.Exec G ∧ (SC.sym S).cons G ∧ P.Full G := by
  unfold exploreX at h
  cases hf : (visitC P O n).find? (fun c => EO.errB c.abs) with
  | some c => rw [hf] at h; cases h
  | none =>
    rw [hf] at h
    have hl : exploreC P O n = l := Sum.inr.inj h
    have hnone := List.find?_eq_none.mp hf
    refine ⟨fun c hc he => ?_, hl ▸ (exploreC_spec O hn).1, hl ▸ (exploreC_spec O hn).2⟩
    exact hnone c ((mem_visitC O hn c).mpr hc) ((EO.errB_iff _).mpr he)

/-- If some consistent execution of the program is erroneous, the run with
exit reports an erroneous graph. -/
theorem exploreX_finds (O : Oracle τ) (EO : ErrOracle E) {n : ℕ} (hn : P.Bounded n)
    {G : Graph} (hG : G.Wf) (hE : P.Exec G) (hc : (SC.sym S).cons G) (herr : E.isErr G) :
    ∃ G', exploreX P O EO n = .inl G' := by
  obtain ⟨c, hcx, hce⟩ := exists_reachX_err (E := E) (τ := τ) hn SC.extensible hG hE hc herr
  unfold exploreX
  cases hf : (visitC P O n).find? (fun c => EO.errB c.abs) with
  | some c' => exact ⟨c'.abs, rfl⟩
  | none =>
    exact absurd ((EO.errB_iff _).mpr hce)
      (List.find?_eq_none.mp hf c ((mem_visitC O hn c).mpr hcx.reach))

/-! ### Example 1 on the reached configurations -/

theorem ex1_bounded : ex1.Bounded 4 := mkProg_bounded _ _ _ _ _

theorem ex1_check : (visitC ex1 eqOracleSe 4).all (fun c =>
    !(decide (ex1.nextC c = some ex1w) && decide (ex1r ∈ c.order) &&
      c.revisitOKB eqOracleSe.prefB ex1r ex1w) || decide (c.pol ex1s = some true)) = true := by
  decide +kernel

/-- Example 1, "`R(x)` is only revisited in exploration B": every revisit of
the read of `x` by the write of `x` starts from a reached configuration in
which the constraint has the outcome `s = 42`. -/
theorem ex1_revisit_only_B {c c' : Config}
    (hc : Reach ex1 (SC.sym EqSem.solver) (TieBreak.se EqSem.solver) c)
    (hs : StepL ex1 (SC.sym EqSem.solver) (TieBreak.se EqSem.solver) c ex1w (.rv ex1r) c') :
    c.pol ex1s = some true := by
  obtain ⟨wp, -, -, hnext, -, hr, -, hnp, hmax, -⟩ := hs.rv_inv
  have hok := (c.revisitOKB_iff (TieBreak.se EqSem.solver) eqOracleSe.prefB_eq hr ex1w).mpr
    ⟨hnp, hmax⟩
  have hnx := (nextC_eq_some_iff hc.sound.1).mpr hnext
  have chk := List.all_eq_true.mp ex1_check c ((mem_visitC eqOracleSe ex1_bounded c).mpr hc)
  simpa [hok, hnx, hr] using chk

theorem ex1_exists : (visitC ex1 eqOracleSe 4).any (fun c =>
    decide (ex1.nextC c = some ex1w) && decide (ex1r ∈ c.order) &&
      c.revisitOKB eqOracleSe.prefB ex1r ex1w && decide (c.pol ex1s = some true) &&
      (c.revisitC ex1r ex1w .init).consS eqOracleSe) = true := by
  decide +kernel

/-- There is such a revisit: from a reached configuration with the outcome
`s = 42`, the write of `x` revisits the read of `x`. -/
theorem ex1_revisit_from_B : ∃ c c' : Config,
    Reach ex1 (SC.sym EqSem.solver) (TieBreak.se EqSem.solver) c ∧ c.pol ex1s = some true ∧
      StepL ex1 (SC.sym EqSem.solver) (TieBreak.se EqSem.solver) c ex1w (.rv ex1r) c' := by
  obtain ⟨c, hmem, hp⟩ := List.any_eq_true.mp ex1_exists
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨⟨hnx, hr⟩, hok⟩, hpol⟩, hcs⟩ := hp
  have hc := (mem_visitC eqOracleSe ex1_bounded c).mp hmem
  obtain ⟨hcw, hpo, hcons, -⟩ := hc.sound
  have hnext := (nextC_eq_some_iff hcw).mp hnx
  obtain ⟨hnp, hmax⟩ :=
    (c.revisitOKB_iff (TieBreak.se EqSem.solver) eqOracleSe.prefB_eq hr ex1w).mp hok
  have hw : ex1w.IsWrite := by decide
  have hwf := Config.revisit_wf (wp := .init) hcw hpo (idx_eq_of_mem_avail hnext.1) hw hr rfl
    (fun d hd => hmax d (Or.inl hd)) trivial
  have hcons' : (SC.sym EqSem.solver).cons (c.revisit ex1r ex1w .init).abs := by
    rw [← c.revisitC_eq]
    rw [← c.revisitC_eq] at hwf
    exact (Config.consS_iff eqOracleSe _ hwf.1).mp hcs
  exact ⟨c, _, hc, hpol,
    StepL.revisit (wp := .init) hcons hnext hw hr rfl hnp hmax trivial hcons'⟩

/-! ### Fig. 1: the six graphs -/

/-- What distinguishes the graphs of Fig. 1: the source of the read of `y`,
the source of the read of `x`, and the outcome of the constraint. -/
def fig1Sig (G : Graph) : Option Ev × Option Ev × Option Bool :=
  (G.rf ⟨2, 0, .read 1⟩, G.rf ⟨3, 0, .read 0⟩, G.pol ⟨2, 1, .cons (fEq 1 42)⟩)

/-- The six graphs of Fig. 1, in the numbering of the figure: the read of `x`
from the write (1-3) or from `init` (4-6); the read of `y` from `init` (1, 4),
or from the write with `s = 42` (2, 5) or `s ≠ 42` (3, 6). -/
def fig1Expected : List (Option Ev × Option Ev × Option Bool) :=
  [(some .init, some (.th ⟨0, 0, .write 0 1⟩), none),
   (some (.th ⟨1, 1, .write 1 1001⟩), some (.th ⟨0, 0, .write 0 1⟩), some true),
   (some (.th ⟨1, 1, .write 1 1001⟩), some (.th ⟨0, 0, .write 0 1⟩), some false),
   (some .init, some .init, none),
   (some (.th ⟨1, 1, .write 1 1001⟩), some .init, some true),
   (some (.th ⟨1, 1, .write 1 1001⟩), some .init, some false)]

/-- The six full executions of `w+sw+r+r` are the six graphs of Fig. 1. -/
theorem fig1_graphs : ∀ x ∈ fig1Expected, x ∈ (exploreC fig1 eqOracleSe 3).map fig1Sig := by
  decide +kernel

end Condpor
