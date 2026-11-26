import Mazurkiewicz.Induction.MP.Terminal
import Mazurkiewicz.Must.ExploreM
import Mazurkiewicz.Induction.Check

/-!
# Message passing: the executable check (milestone C8a)

`induction-popl`, `mp.tex` para mp:329 (the decision procedure of thm:mp-terminal, as cor:enum),
for the one construction over a setting `S` (plan `plan/ind/TRACK-C-PLAN.md`, milestone C8a).
The enumerator of the terminal executions of a budget program is the port's repaired explorer
(the R-claim of the plan, Section 2.5).

* `runTerm consB T fuel R`: the port's `explore consB (Variant.repaired consB T) R fuel`.
  `runTerm_spec` (the R-claim): for a decision procedure `consB` of `M` on `Supp` graphs and a
  bounded `R`, a run that reports no exhaustion reports, without repetition, exactly the
  terminal executions `Term M R`. `runTerm_fuel`: such a fuel exists.
* `budgetProgOf S u W b κ`: `Q_b|κ` from the functions `u`, `W` (equal to
  `SAbs.budgetProg` for `u = Abs.u`, `W = Abs.W`, by `rfl`). `checkRuns`: one run per value of
  `B` and budget of size `K` (Track A's `Trust.budgets`). `checkOK`: the test of one terminal
  execution (`‖F‖ = K`: `f b F ∈ B`; else `f b F ∉ Abad`). `CheckS`: the verdict (no run
  exhausted and every test passes) and the count of tests (evaluations of `f`); no early stop.
  `checkTests`: the list of tests. All of them are computable; none calls a noncomputable
  definition.
* `checkS_fst`, `checkS_snd`: the verdict and the count in closed form. `checkS_fuel` (no
  realisability needed: every budget program is bounded), `checkS_count` (count = sum over
  values and budgets of the number of terminal executions; no `B.Nodup`, no acceptance),
  `checkS_once` (cor:enum (3), last clause: every fragment of length `K` of a realised value of
  `B` is tested exactly once; needs `B.Nodup`).
* Smoke test: a two-thread `p2p` program with one message; `CheckS` evaluates by `decide +kernel`
  to `(true, 2)`.
-/

namespace Must

namespace Ind

open Graph Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)]

/-! ### Runs of the explorer -/

/-- The port's repaired explorer on `R`. -/
def runTerm (consB : Graph Q → Bool) (T : Sel Q) (fuel : ℕ) (R : Program Q) : Result Q :=
  explore consB (Variant.repaired consB T) R fuel

/-- The R-claim (plan Section 2.5): a run without exhaustion reports, without repetition,
exactly the terminal executions. -/
theorem runTerm_spec {M : Model Q} {consB : Graph Q → Bool} {T : Sel Q} {fuel k : ℕ}
    {R : Program Q} (hc : ∀ H : Graph Q, H.Supp → (consB H = true ↔ M.cons H))
    (hb : R.Bounded k) (hex : (runTerm consB T fuel R).exhausted = false) :
    ((runTerm consB T fuel R).reported.map Config.G).Nodup ∧
    ∀ F, F ∈ (runTerm consB T fuel R).reported.map Config.G ↔ Term M R F := by
  obtain ⟨h1, h2, -⟩ := exploreM_spec_of_not_exhausted hc T hb hex
  exact ⟨h1, fun F => (h2 F).trans term_iff_sem.symm⟩

/-- A fuel without exhaustion exists. -/
theorem runTerm_fuel {M : Model Q} {consB : Graph Q → Bool} {T : Sel Q} {k : ℕ} {R : Program Q}
    (hc : ∀ H : Graph Q, H.Supp → (consB H = true ↔ M.cons H)) (hb : R.Bounded k) :
    ∃ N, ∀ fuel, N ≤ fuel → (runTerm consB T fuel R).exhausted = false :=
  ⟨_, fun _ hN => explore_not_exhausted (M := M) hc T hb hN⟩

omit [DecidableEq Q] [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
/-- A truncation is bounded by the sum of its bounds on the listed threads. -/
theorem trunc_bounded_sum (R : Program Q) (κ : Tid → ℕ) :
    (R.trunc κ).Bounded (R.threads.map κ).sum :=
  trunc_bounded fun _ ht => Trust.le_sum_map_of_mem ht

/-! ### The check -/

/-- `Q_b|κ` from the functions `u`, `W`. -/
def budgetProgOf (S : MPSetting Q) {A : Type} (u : A → Tid → List (Option Val))
    (W : A → Tid → List Msg) (b : A) (κ : Tid → ℕ) : Program Q :=
  (S.P.seedRes S.ι S.hι S.m (u b) (W b)).trunc (fun t => (W b t).length + κ t)

/-- One run per value of `B` and budget of size `K`. -/
def checkRuns (consB : Graph Q → Bool) (T : Sel Q) (fuel : ℕ) (S : MPSetting Q) {A : Type}
    (B : List A) (u : A → Tid → List (Option Val)) (W : A → Tid → List Msg) (K : ℕ) :
    List (A × Result Q) :=
  B.flatMap fun b => (Trust.budgets S.P.threads K).map fun κ =>
    (b, runTerm consB T fuel (budgetProgOf S u W b κ))

/-- The test of one terminal execution. -/
def checkOK (S : MPSetting Q) {A : Type} [DecidableEq A] (B : List A) (abad : A → Bool)
    (W : A → Tid → List Msg) (f : A → Graph Q → A) (K : ℕ) (b : A) (F : Graph Q) : Bool :=
  if F.len S.ts (W b) = K then decide (f b F ∈ B) else !abad (f b F)

/-- The check: the verdict (no run exhausted, every test passes) and the number of tests. -/
def CheckS (consB : Graph Q → Bool) (T : Sel Q) (fuel : ℕ) (S : MPSetting Q) {A : Type}
    [DecidableEq A] (B : List A) (abad : A → Bool) (u : A → Tid → List (Option Val))
    (W : A → Tid → List Msg) (f : A → Graph Q → A) (K : ℕ) : Bool × ℕ :=
  let runs := checkRuns consB T fuel S B u W K
  (runs.foldl (fun acc x => (x.2.reported.map Config.G).foldl
      (fun acc F => (checkOK S B abad W f K x.1 F && acc.1, acc.2 + 1)) acc)
    (runs.all (fun x => !x.2.exhausted), 0))

/-- The tests, as pairs of a value and a terminal execution. -/
def checkTests (consB : Graph Q → Bool) (T : Sel Q) (fuel : ℕ) (S : MPSetting Q) {A : Type}
    (B : List A) (u : A → Tid → List (Option Val)) (W : A → Tid → List Msg) (K : ℕ) :
    List (A × Graph Q) :=
  (checkRuns consB T fuel S B u W K).flatMap fun x => (x.2.reported.map Config.G).map (x.1, ·)

/-! ### Closed forms -/

omit [DecidableEq Q] [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
theorem foldl_runs {X : Type} (runs : List (X × Result Q)) (g : X → Graph Q → Bool)
    (acc : Bool × ℕ) :
    runs.foldl (fun acc x => (x.2.reported.map Config.G).foldl
        (fun acc F => (g x.1 F && acc.1, acc.2 + 1)) acc) acc =
      (runs.all (fun x => (x.2.reported.map Config.G).all (g x.1)) && acc.1,
        acc.2 + (runs.map fun x => x.2.reported.length).sum) := by
  induction runs generalizing acc with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, Trust.foldl_check, ih]
    simp only [List.all_cons, List.map_cons, List.sum_cons, List.length_map, Prod.mk.injEq]
    constructor
    · cases (x.2.reported.map Config.G).all (g x.1) <;>
        cases l.all (fun x => (x.2.reported.map Config.G).all (g x.1)) <;> cases acc.1 <;> rfl
    · omega

/-- The verdict of `CheckS`. -/
theorem checkS_fst (consB : Graph Q → Bool) (T : Sel Q) (fuel : ℕ) (S : MPSetting Q) {A : Type}
    [DecidableEq A] (B : List A) (abad : A → Bool) (u : A → Tid → List (Option Val))
    (W : A → Tid → List Msg) (f : A → Graph Q → A) (K : ℕ) :
    (CheckS consB T fuel S B abad u W f K).1 =
      ((checkRuns consB T fuel S B u W K).all
          (fun x => (x.2.reported.map Config.G).all (checkOK S B abad W f K x.1)) &&
        (checkRuns consB T fuel S B u W K).all (fun x => !x.2.exhausted)) := by
  unfold CheckS
  rw [foldl_runs]

/-- The count of `CheckS`. -/
theorem checkS_snd (consB : Graph Q → Bool) (T : Sel Q) (fuel : ℕ) (S : MPSetting Q) {A : Type}
    [DecidableEq A] (B : List A) (abad : A → Bool) (u : A → Tid → List (Option Val))
    (W : A → Tid → List Msg) (f : A → Graph Q → A) (K : ℕ) :
    (CheckS consB T fuel S B abad u W f K).2 =
      ((checkRuns consB T fuel S B u W K).map fun x => x.2.reported.length).sum := by
  unfold CheckS
  rw [foldl_runs, Nat.zero_add]

theorem mem_checkRuns {consB : Graph Q → Bool} {T : Sel Q} {fuel : ℕ} {S : MPSetting Q}
    {A : Type} {B : List A} {u : A → Tid → List (Option Val)} {W : A → Tid → List Msg} {K : ℕ}
    {x : A × Result Q} :
    x ∈ checkRuns consB T fuel S B u W K ↔
      ∃ b ∈ B, ∃ κ, Trust.IsBudget S.P.threads K κ ∧
        x = (b, runTerm consB T fuel (budgetProgOf S u W b κ)) := by
  unfold checkRuns
  simp only [List.mem_flatMap, List.mem_map, Trust.mem_budgets S.P.nodup]
  constructor
  · rintro ⟨b, hb, κ, hκ, rfl⟩
    exact ⟨b, hb, κ, hκ, rfl⟩
  · rintro ⟨b, hb, κ, hκ, rfl⟩
    exact ⟨b, hb, κ, hκ, rfl⟩

omit [DecidableEq Q] [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
/-- A property eventually true for every element of a list is eventually true for all. -/
theorem exists_bound_list {X : Type} (p : X → ℕ → Prop) :
    ∀ l : List X, (∀ x ∈ l, ∃ N, ∀ n, N ≤ n → p x n) → ∃ N, ∀ n, N ≤ n → ∀ x ∈ l, p x n
  | [], _ => ⟨0, fun _ _ x hx => absurd hx (List.not_mem_nil)⟩
  | a :: l, h => by
    obtain ⟨N₁, h₁⟩ := h a List.mem_cons_self
    obtain ⟨N₂, h₂⟩ := exists_bound_list p l fun x hx => h x (List.mem_cons_of_mem _ hx)
    refine ⟨max N₁ N₂, fun n hn x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h₁ n (le_of_max_le_left hn)
    · exact h₂ n (le_of_max_le_right hn) x hx

/-- A fuel without exhaustion of any run exists (no realisability needed: every budget program
is bounded by its guarded truncation). -/
theorem checkS_fuel {consB : Graph Q → Bool} {T : Sel Q} {S : MPSetting Q} {A : Type}
    {B : List A} {u : A → Tid → List (Option Val)} {W : A → Tid → List Msg} {K : ℕ}
    (hc : ∀ H : Graph Q, H.Supp → (consB H = true ↔ (Model.ofSet S.ms).cons H)) :
    ∃ N, ∀ fuel, N ≤ fuel →
      (checkRuns consB T fuel S B u W K).all (fun x => !x.2.exhausted) = true := by
  obtain ⟨N, hN⟩ := exists_bound_list
    (fun (x : A × (Tid → ℕ)) fuel =>
      (runTerm consB T fuel (budgetProgOf S u W x.1 x.2)).exhausted = false)
    (B.flatMap fun b => (Trust.budgets S.P.threads K).map fun κ => (b, κ))
    fun x _ => runTerm_fuel hc (trunc_bounded_sum _ _)
  refine ⟨N, fun fuel hf => List.all_eq_true.mpr fun x hx => ?_⟩
  obtain ⟨b, hb, κ, hκ, rfl⟩ := mem_checkRuns.mp hx
  have := hN fuel hf (b, κ) (List.mem_flatMap.mpr ⟨b, hb, List.mem_map.mpr
    ⟨κ, (Trust.mem_budgets S.P.nodup).mpr hκ, rfl⟩⟩)
  simp [this]

omit [DecidableEq Q] [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
theorem sum_map_flatMap {X Y : Type} (l : List X) (g : X → List Y) (h : Y → ℕ) :
    ((l.flatMap g).map h).sum = (l.map fun a => ((g a).map h).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- With no run exhausted, the number of reported graphs of a run is the number of terminal
executions. -/
theorem length_reported_eq {M : Model Q} {consB : Graph Q → Bool} {T : Sel Q} {fuel k : ℕ}
    {R : Program Q} (hc : ∀ H : Graph Q, H.Supp → (consB H = true ↔ M.cons H))
    (hb : R.Bounded k) (hex : (runTerm consB T fuel R).exhausted = false) :
    (runTerm consB T fuel R).reported.length = {F | Term M R F}.ncard := by
  classical
  obtain ⟨hnd, hmem⟩ := runTerm_spec hc hb hex
  have hs : {F | Term M R F} = ↑(((runTerm consB T fuel R).reported.map Config.G).toFinset) := by
    ext F
    rw [Finset.mem_coe, List.mem_toFinset, hmem]
    rfl
  rw [hs, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map]

/-- The count of `CheckS` is the number of terminal executions, summed over the values of `B`
and the budgets (the paper's "tests"). No acceptance and no `B.Nodup` needed. -/
theorem checkS_count {consB : Graph Q → Bool} {T : Sel Q} {fuel : ℕ} {S : MPSetting Q}
    {A : Type} [DecidableEq A] {B : List A} {abad : A → Bool} {u : A → Tid → List (Option Val)}
    {W : A → Tid → List Msg} {f : A → Graph Q → A} {K : ℕ}
    (hc : ∀ H : Graph Q, H.Supp → (consB H = true ↔ (Model.ofSet S.ms).cons H))
    (hex : (checkRuns consB T fuel S B u W K).all (fun x => !x.2.exhausted) = true) :
    (CheckS consB T fuel S B abad u W f K).2 =
      (B.map fun b => ((Trust.budgets S.P.threads K).map fun κ =>
        {F | Term (Model.ofSet S.ms) (budgetProgOf S u W b κ) F}.ncard).sum).sum := by
  rw [checkS_snd]
  have hex' := List.all_eq_true.mp hex
  unfold checkRuns at hex' ⊢
  rw [sum_map_flatMap]
  refine congrArg List.sum (List.map_congr_left fun b hb => ?_)
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun κ hκ => ?_)
  have := hex' _ (List.mem_flatMap.mpr ⟨b, hb, List.mem_map.mpr ⟨κ, hκ, rfl⟩⟩)
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at this
  exact length_reported_eq hc (trunc_bounded_sum _ _) this

omit [DecidableEq Q] [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
theorem sum_ite_of_unique {X : Type} {l : List X} (hl : l.Nodup) {a : X} (ha : a ∈ l)
    (p : X → Prop) [DecidablePred p] (hp : ∀ x ∈ l, p x ↔ x = a) (c : ℕ) :
    (l.map fun x => if p x then c else 0).sum = c := by
  induction l with
  | nil => exact absurd ha List.not_mem_nil
  | cons x l ih =>
    obtain ⟨hxl, hl'⟩ := List.nodup_cons.mp hl
    rw [List.map_cons, List.sum_cons]
    by_cases hxa : x = a
    · subst hxa
      have h0 : (l.map fun y => if p y then c else 0) = l.map fun _ => 0 :=
        List.map_congr_left fun y hy => ite_eq_right fun h =>
          hxl (((hp y (List.mem_cons_of_mem _ hy)).mp h) ▸ hy)
      rw [ite_eq_left ((hp x List.mem_cons_self).mpr rfl), h0]
      simp
    · have hal : a ∈ l := (List.mem_cons.mp ha).resolve_left (Ne.symm hxa)
      rw [ite_eq_right fun h => hxa ((hp x List.mem_cons_self).mp h),
        ih hl' hal fun y hy => hp y (List.mem_cons_of_mem _ hy)]
      simp

omit [DecidableEq Q] [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
theorem sum_ite_of_none {X : Type} {l : List X} (p : X → Prop) [DecidablePred p]
    (hp : ∀ x ∈ l, ¬ p x) (c : ℕ) : (l.map fun x => if p x then c else 0).sum = 0 := by
  rw [List.map_congr_left (g := fun _ => 0) fun x hx => ite_eq_right (hp x hx)]
  simp

open Classical in
/-- cor:enum (3), last clause: every fragment of length `K` of a value of `B` is tested exactly
once. `B.Nodup` is needed: a repeated value repeats its tests. (The premise `hreal` of the plan
is not needed: `cover_unique` holds for every fragment.) -/
theorem checkS_once {consB : Graph Q → Bool} {T : Sel Q} {fuel : ℕ} {S : MPSetting Q}
    {A : Type} {B : List A} {K : ℕ} {b : A} {H : Graph Q} (Abs : SAbs S A)
    (hc : ∀ H : Graph Q, H.Supp → (consB H = true ↔ (Model.ofSet S.ms).cons H)) (hB : B.Nodup)
    (hex : (checkRuns consB T fuel S B Abs.u Abs.W K).all (fun x => !x.2.exhausted) = true)
    (hb : b ∈ B) (_hreal : Abs.Realised b)
    (hH : Frag (Model.ofSet S.ms) (Abs.res b) (Abs.W b) H) (hK : H.len S.ts (Abs.W b) = K) :
    (checkTests consB T fuel S B Abs.u Abs.W K).count (b, H) = 1 := by
  have hex' := List.all_eq_true.mp hex
  obtain ⟨hT, huniq, hbud⟩ := Abs.cover_unique _hreal hH hK
  set κH : Tid → ℕ := fun t => if t ∈ S.P.threads then H.cnt t - (Abs.W b t).length else 0
    with hκH
  have hκHm : κH ∈ Trust.budgets S.P.threads K := (Trust.mem_budgets S.P.nodup).mpr hbud
  -- the count in the run of `(b', κ)`
  have hrun : ∀ b' ∈ B, ∀ κ ∈ Trust.budgets S.P.threads K,
      (((runTerm consB T fuel (budgetProgOf S Abs.u Abs.W b' κ)).reported.map Config.G).map
        (b', ·)).count (b, H) = if b' = b ∧ κ = κH then 1 else 0 := by
    intro b' hb' κ hκ
    have hx := hex' _ (List.mem_flatMap.mpr ⟨b', hb', List.mem_map.mpr ⟨κ, hκ, rfl⟩⟩)
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hx
    obtain ⟨hnd, hmem⟩ := runTerm_spec hc (trunc_bounded_sum _ _) hx
    have hnd' : (((runTerm consB T fuel (budgetProgOf S Abs.u Abs.W b' κ)).reported.map
        Config.G).map (b', ·)).Nodup := hnd.map (f := fun F => (b', F)) fun F F' h =>
      (Prod.mk.inj h).2
    rw [hnd'.count]
    have hiff : (b, H) ∈ ((runTerm consB T fuel (budgetProgOf S Abs.u Abs.W b' κ)).reported.map
        Config.G).map (b', ·) ↔ b' = b ∧ κ = κH := by
      constructor
      · intro h'
        obtain ⟨F, hF, hFe⟩ := List.mem_map.mp h'
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hFe
        exact ⟨rfl, funext (huniq κ ((Trust.mem_budgets S.P.nodup).mp hκ)
          (mreach_iff.mp ((hmem F).mp hF).1))⟩
      · rintro ⟨rfl, rfl⟩
        exact List.mem_map.mpr ⟨H, (hmem H).mpr hT, rfl⟩
    by_cases hp : b' = b ∧ κ = κH
    · rw [ite_eq_left (hiff.mpr hp), ite_eq_left hp]
    · rw [ite_eq_right (fun h => hp (hiff.mp h)), ite_eq_right hp]
  unfold checkTests
  rw [List.count_flatMap]
  unfold checkRuns
  rw [sum_map_flatMap]
  have hper : ∀ b' ∈ B, (((Trust.budgets S.P.threads K).map fun κ =>
      (b', runTerm consB T fuel (budgetProgOf S Abs.u Abs.W b' κ))).map
        (List.count (b, H) ∘ fun x => (x.2.reported.map Config.G).map (x.1, ·))).sum =
      if b' = b then 1 else 0 := by
    intro b' hb'
    rw [List.map_map]
    refine (congrArg List.sum (List.map_congr_left
      (g := fun κ => if b' = b ∧ κ = κH then 1 else 0) fun κ hκ => hrun b' hb' κ hκ)).trans ?_
    · by_cases hbb : b' = b
      · rw [ite_eq_left hbb]
        exact sum_ite_of_unique (Trust.budgets_nodup S.P.nodup K) hκHm _
          (fun κ _ => ⟨fun h => h.2, fun h => ⟨hbb, h⟩⟩) 1
      · rw [ite_eq_right hbb]
        exact sum_ite_of_none _ (fun κ _ h => hbb h.1) 1
  rw [List.map_congr_left hper]
  exact sum_ite_of_unique hB hb _ (fun _ _ => Iff.rfl) 1

/-! ### A smoke test -/

/-- Thread `0` sends `5` to thread `1`, which receives it (blocking, any value). -/
def smokeStep : Tid → List (Option Val) → Option (Lab VPred)
  | 0, [] => some (.send .p2p 1 5)
  | 1, [] => some (.recv ⟨.p2p, true⟩ .any)
  | _, _ => none

/-- The smoke-test program. -/
def smokeProg : Program VPred where
  threads := [0, 1]
  nodup := by decide
  step := smokeStep
  step_none t ht := by
    match t with
    | 0 => simp at ht
    | 1 => simp at ht
    | t + 2 => rfl
  stop t u l h hs := by
    match t, u with
    | 0, [] => simp only [smokeStep, Option.some.injEq] at h; subst h; simp [Lab.Stops] at hs
    | 1, [] => rfl
    | 0, _ :: _ => simp [smokeStep] at h
    | 1, _ :: _ => simp [smokeStep] at h
    | t + 2, _ => simp [smokeStep] at h
  nd_ne t u S h := by
    match t, u with
    | 0, [] => simp [smokeStep] at h
    | 1, [] => simp [smokeStep] at h
    | 0, _ :: _ => simp [smokeStep] at h
    | 1, _ :: _ => simp [smokeStep] at h
    | t + 2, _ => simp [smokeStep] at h

theorem smokeProg_tagged : smokeProg.Tagged .p2p := by
  intro t u l h
  change smokeStep t u = some l at h
  match t, u with
  | 0, [] => simp only [smokeStep, Option.some.injEq] at h; subst h; simp [Lab.model?]
  | 1, [] => simp only [smokeStep, Option.some.injEq] at h; subst h; simp [Lab.model?]
  | 0, _ :: _ => simp [smokeStep] at h
  | 1, _ :: _ => simp [smokeStep] at h
  | t + 2, _ => simp [smokeStep] at h

/-- With `K = 1`, one abstract value, no seeds: the budgets `(1, 0)` (the send; one terminal
execution of length `1`) and `(0, 1)` (the receive is stuck; the empty graph, length `0`): two
tests, both passing. -/
example : CheckS Graph.consAPB Sel.least 50 (p2pSetting smokeProg smokeProg_tagged) [()]
    (fun _ => false) (fun _ _ => []) (fun _ _ => []) (fun _ _ => ()) 1 = (true, 2) := by
  decide +kernel

end Ind

end Must
