import Mazurkiewicz.Must.Exit
import Mazurkiewicz.Must.ExploreMEx

/-!
# M9 follow-up: `dead = 0`, optimality (b) for the explorer, every model, early exit and (b)

Follow-up to the M9 reviews (Opus N1-N4, Astra 3 and 6).

* `stepM_ne_nil`, `dfs_dead`, `explore_dead`: a reachable configuration never has an empty
  successor list, so the reference explorer's `dead` counter is 0, for every fuel (Opus N2).
* `explore_not_fruitless`: Theorem 4.1 (b) for the reference explorer, every fuel: no visited
  configuration is fruitless (from `explore_sound` and `ReachM.not_fruitless`; Opus N3).
* `consCl`, `consCl_iff`: the classical (noncomputable) decision procedure of any model
  satisfies the hypothesis `hc` of `exploreM_spec` and `completeM_exit`. The instances
  `exploreM_spec_mbox`, `exploreM_spec_comb`, `completeM_exit_mbox`, `completeM_exit_comb` show
  that both theorems hold for every model (Opus N1). What `mbox` and `comb` lack is a
  computable `consB`: the explorer cannot be evaluated on them.
* `StepX`, `FruitlessX`, `fruitless_with_exit`: the fate row Thm 4.1/A.3 (b) "F with early exit"
  (Opus N4, Astra 6). With early exit no step leaves a configuration with an error event; a
  visit is fruitless with early exit if no such path leads to a report. On `pE` the explorer
  with early exit returns (visits) a configuration that is fruitless with early exit, while the
  same configuration is not fruitless for the exhaustive relation.
-/

namespace Must

open Graph Config Relation

section General

variable {Q : Type} [DecidableEq Q] [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)]
variable {M : Model Q} {P : Program Q} {consB : Graph Q → Bool}

/-- A reachable configuration never has an empty successor list. -/
theorem stepM_ne_nil (hc : ∀ H : Graph Q, H.Supp → (consB H = true ↔ M.cons H)) (T : Sel Q)
    {k : ℕ} (hb : P.Bounded k) {c : Config Q} (hcR : ReachM M (T.pick consB) P c) :
    stepM consB (Variant.repaired consB T) P c ≠ some [] := by
  intro hs
  obtain ⟨c', h1, -, h3, -⟩ := hcR.reaches_full hb
  rcases Relation.ReflTransGen.cases_head h1 with h | ⟨y, hy, -⟩
  · subst h
    have := (stepM_eq_none_iff hc T P hcR.sound.wf.supp).mpr h3
    rw [hs] at this; cases this
  · have hy' : StepM M (T.pick consB) P c y := NrStep.stepM hy
    have := (mem_stepM_iff hc T P hcR.sound y).mpr hy'
    rw [hs] at this; simp at this

/-- A search from a reachable configuration does not change the `dead` counter. -/
theorem dfs_dead (hc : ∀ H : Graph Q, H.Supp → (consB H = true ↔ M.cons H)) (T : Sel Q)
    {k : ℕ} (hb : P.Bounded k) :
    ∀ (n d : ℕ) (c : Config Q) (r : Result Q), ReachM M (T.pick consB) P c →
      (dfs consB (Variant.repaired consB T) P n d c r).dead = r.dead
  | 0, _, _, _, _ => rfl
  | n + 1, d, c, r, hcR => by
    have hf : ∀ (l : List (Config Q)) (r : Result Q), (∀ a ∈ l, ReachM M (T.pick consB) P a) →
        (dfsFold consB (Variant.repaired consB T) P n d l r).dead = r.dead := by
      intro l
      induction l with
      | nil => intro r _; rfl
      | cons a l ihl =>
        intro r hl
        simp only [dfsFold, List.foldl_cons] at ihl ⊢
        rw [ihl _ (fun b hb' => hl b (.tail _ hb')),
          dfs_dead hc T hb n (d + 1) a r (hl a (.head _))]
    rw [dfs_succ]
    split_ifs
    · rfl
    rcases hs : stepM consB (Variant.repaired consB T) P c with _ | l
    · rfl
    rcases l with _ | ⟨a, l⟩
    · exact absurd hs (stepM_ne_nil hc T hb hcR)
    obtain ⟨-, hmem⟩ := children_spec hc T hcR hs
    simp only
    rw [hf _ _ (fun b hb' => hcR.tail ((hmem b).mp hb'))]
    rfl

/-- **`explore_dead`**: for every fuel, the reference explorer meets no configuration with an
empty successor list (`dead = 0`). Every model with a decision procedure, every selection,
every bounded program. -/
theorem explore_dead (hc : ∀ H : Graph Q, H.Supp → (consB H = true ↔ M.cons H)) (T : Sel Q)
    {k : ℕ} (hb : P.Bounded k) (fuel : ℕ) :
    (explore consB (Variant.repaired consB T) P fuel).dead = 0 :=
  dfs_dead hc T hb fuel 0 .init { fuel := fuel } .refl

/-- **`explore_not_fruitless`** (Theorem 4.1 (b) for the reference explorer): for every fuel,
no visited configuration is fruitless. Every model with a decision procedure, every selection,
every bounded program. -/
theorem explore_not_fruitless (hc : ∀ H : Graph Q, H.Supp → (consB H = true ↔ M.cons H))
    (T : Sel Q) {k : ℕ} (hb : P.Bounded k) (fuel : ℕ) :
    ∀ x ∈ (explore consB (Variant.repaired consB T) P fuel).seen,
      ¬ Fruitless M (T.pick consB) P x :=
  fun x hx => ((explore_sound hc T).1 x hx).not_fruitless hb

/-! ### Every model: a classical decision procedure -/

open Classical in
/-- The classical decision procedure of a model (noncomputable). -/
noncomputable def consCl (M : Model Q) : Graph Q → Bool := fun G => decide (M.cons G)

omit [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
/-- `consCl M` satisfies the hypothesis `hc` of `exploreM_spec` and `completeM_exit`. -/
theorem consCl_iff (M : Model Q) : ∀ H : Graph Q, H.Supp → (consCl M H = true ↔ M.cons H) := by
  intro H _
  simp [consCl]

/-- `exploreM_spec` for `mbox` (classical `consB`). -/
theorem exploreM_spec_mbox (T : Sel Q) {k fuel : ℕ} (hb : P.Bounded k)
    (hf : {c | ReachM Model.mbox (T.pick (consCl Model.mbox)) P c}.ncard ≤ fuel) :
    let R := explore (consCl Model.mbox) (Variant.repaired (consCl Model.mbox) T) P fuel
    R.exhausted = false ∧ (R.reported.map Config.G).Nodup ∧
      (∀ G, G ∈ R.reported.map Config.G ↔ Model.mbox.Sem P G) ∧ (R.seen.map Config.G).Nodup ∧
      ∀ c, c ∈ R.seen ↔ ReachM Model.mbox (T.pick (consCl Model.mbox)) P c :=
  exploreM_spec (consCl_iff Model.mbox) T hb hf

/-- `exploreM_spec` for `comb` (classical `consB`). -/
theorem exploreM_spec_comb (T : Sel Q) {k fuel : ℕ} (hb : P.Bounded k)
    (hf : {c | ReachM Model.comb (T.pick (consCl Model.comb)) P c}.ncard ≤ fuel) :
    let R := explore (consCl Model.comb) (Variant.repaired (consCl Model.comb) T) P fuel
    R.exhausted = false ∧ (R.reported.map Config.G).Nodup ∧
      (∀ G, G ∈ R.reported.map Config.G ↔ Model.comb.Sem P G) ∧ (R.seen.map Config.G).Nodup ∧
      ∀ c, c ∈ R.seen ↔ ReachM Model.comb (T.pick (consCl Model.comb)) P c :=
  exploreM_spec (consCl_iff Model.comb) T hb hf

/-- `completeM_exit` for `mbox` (classical `consB`). -/
theorem completeM_exit_mbox (T : Sel Q) {k fuel : ℕ} (hb : P.Bounded k)
    (hf : {c | ReachM Model.mbox (T.pick (consCl Model.mbox)) P c}.ncard ≤ fuel) :
    let R := exploreX (consCl Model.mbox) (Variant.repaired (consCl Model.mbox) T) P fuel
    R.exhausted = false ∧ (R.err.isSome ↔ Erroneous Model.mbox P) ∧
      ∀ x, R.err = some x → ReachM Model.mbox (T.pick (consCl Model.mbox)) P x ∧ HasErr x.G :=
  completeM_exit (consCl_iff Model.mbox) T hb hf

/-- `completeM_exit` for `comb` (classical `consB`). -/
theorem completeM_exit_comb (T : Sel Q) {k fuel : ℕ} (hb : P.Bounded k)
    (hf : {c | ReachM Model.comb (T.pick (consCl Model.comb)) P c}.ncard ≤ fuel) :
    let R := exploreX (consCl Model.comb) (Variant.repaired (consCl Model.comb) T) P fuel
    R.exhausted = false ∧ (R.err.isSome ↔ Erroneous Model.comb P) ∧
      ∀ x, R.err = some x → ReachM Model.comb (T.pick (consCl Model.comb)) P x ∧ HasErr x.G :=
  completeM_exit (consCl_iff Model.comb) T hb hf

end General

/-! ### Early exit and Theorem A.3 (b) -/

section Exit

variable {Q : Type} [DecidableEq Q] [Membership Val Q]

/-- A step of Algorithm 1 with early exit: an algorithmic step from a configuration without an
error event (line 5 exits at an error, so an erroneous configuration has no successor). -/
def StepX (M : Model Q) (tie : Tie Q) (P : Program Q) (c c' : Config Q) : Prop :=
  ¬ HasErr c.G ∧ StepM M tie P c c'

/-- Definition A.2 with early exit: the visit of `c` leads to no report by steps with early
exit. -/
def FruitlessX (M : Model Q) (tie : Tie Q) (P : Program Q) (c : Config Q) : Prop :=
  ¬ ∃ c', ReflTransGen (StepX M tie P) c c' ∧ M.nextP P c'.G = none

/-- A configuration with an error event and a next event is fruitless with early exit. -/
theorem fruitlessX_of_err {M : Model Q} {tie : Tie Q} {P : Program Q} {c : Config Q}
    (he : HasErr c.G) (hn : M.nextP P c.G ≠ none) : FruitlessX M tie P c := by
  rintro ⟨c', h1, h2⟩
  rcases Relation.ReflTransGen.cases_head h1 with rfl | ⟨y, hy, -⟩
  · exact hn h2
  · exact hy.1 he

end Exit

namespace ExploreMEx

open MustFast MustFast' Examples

/-- `T0: send(T1,1)`; `T1: r = recv(); if r = 1 then error`; `T2: send(T1,0)`. The error is
added before `T2` runs. -/
def pE : Program VPred :=
  ofCodes [sa 1 1, .recv .asyn true .any [(1, .error)] .done .done, sa 1 0]

theorem pE_bounded : pE.Bounded 2 := ofCodes_bounded (by decide +kernel)

/-- **`fruitless_with_exit`** (fate row Thm 4.1/A.3 (b): F with early exit): the explorer with
early exit visits and returns a reachable configuration of `pE` that is fruitless with early
exit (it has a next event and no step), although it is not fruitless for the exhaustive
relation (`ReachM.not_fruitless`). -/
theorem fruitless_with_exit : ∃ x, (exploreX AP (rep .least) pE 100).err = some x ∧
    ReachM Model.p2p (Sel.least.pick AP) pE x ∧
    FruitlessX Model.p2p (Sel.least.pick AP) pE x ∧
    ¬ Fruitless Model.p2p (Sel.least.pick AP) pE x := by
  cases h : (exploreX AP (rep .least) pE 100).err with
  | none => exact absurd h (by decide +kernel)
  | some x =>
    obtain ⟨hR, he, -⟩ := exploreX_sound consAPB_iff_p2p .least pE_bounded h
    have hk : ((exploreX AP (rep .least) pE 100).err.map
        fun x => (pE.nextP AP x.G).isSome) = some true := by decide +kernel
    rw [h] at hk
    have hn : pE.nextP AP x.G ≠ none := by
      intro h0; simp [h0] at hk
    rw [Model.nextP_eq AP consAPB_iff_p2p pE hR.sound.wf.supp] at hn
    exact ⟨x, rfl, hR, fruitlessX_of_err he hn, hR.not_fruitless pE_bounded⟩

end ExploreMEx

end Must

#print axioms Must.stepM_ne_nil
#print axioms Must.explore_dead
#print axioms Must.explore_not_fruitless
#print axioms Must.consCl_iff
#print axioms Must.exploreM_spec_mbox
#print axioms Must.exploreM_spec_comb
#print axioms Must.completeM_exit_mbox
#print axioms Must.completeM_exit_comb
#print axioms Must.fruitlessX_of_err
#print axioms Must.ExploreMEx.fruitless_with_exit
