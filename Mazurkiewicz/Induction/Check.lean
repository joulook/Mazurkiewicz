import Mazurkiewicz.Induction.FullObl
import Mathlib.Data.Set.Card

/-!
# Enumerators and the procedure `Check`

`induction-popl`, `dpor.tex` sec:enum (def:enumerator, cor:enum) and
sec:trust-enum (prop:trust-enum), for plain programs under SC.

How the text is read here.

* def:enumerator: an enumerator is a function `E : Program → ℕ → List Graph`;
  the second argument is a bound on the number of events of a thread
  (`Program.Bounded`). It is complete, sound, optimal if for every program
  `Q` bounded by `n` the list `E Q n` contains every element of `Full(Q)`,
  only elements of `Full(Q)`, and no element twice. The properties are asked
  of every bounded program, not of a class. "Procedure" and "terminates"
  are rendered by a total Lean function to finite lists; that it can be run
  is a property of a particular enumerator and of its inputs (`exploreC` is
  computable). (The paper's enumerator gets only `Q`;
  lem:exhaustive, an enumerator that needs no bound, is not formalised.)
* prop:trust-enum: `exploreC` of the port is a complete, sound and optimal
  enumerator (`exploreC_complete`, `exploreC_sound`, `exploreC_optimal`).
  This is a theorem about the port's transcription of Algorithm 1 of TruSt
  for read and write labels and the lexicographic `<next`; `ass:trust` of the
  paper is not used.
* cor:enum: `Check` goes through `b ∈ B`, the budgets `κ` of size `K`
  (`budgets P.threads K`) and the graphs `F` of
  `E ((P.residual (u b) (μ b)).trunc κ) K`; the triples `(b, κ, F)` with
  `|F| ≤ K + 1` are `checkItems`; `Check` folds over all of them, evaluates
  and tests `f b F` on each (`checkOK`) whatever the earlier tests gave, and
  returns the verdict and the number of evaluations (`check_fst`,
  `check_count`). In Lean this number is a property of the definition; the
  theorems below say what it is equal to.
  `B` is a list; `Abad` is given by a Boolean function `abad`.
* cor:enum (1): `check_sound_of_complete` for a complete enumerator, and
  `check_sound` for `exploreC`. The abstraction is not assumed compositional
  (the hypothesis `hf` is stated for every graph `G` with `α G ∈ B`);
  `check_sound_paper` has the paper's hypothesis in addition. A program
  without threads is covered (its only reachable graph is the initial one).
* cor:enum (2): `check_accepts`. cor:enum (3): `checkItems_nodup` (it needs
  only optimality), 
  `mem_checkItems`, `check_count`, `check_count_eq_sum`,
  `check_count_eq_sum_ncard` (the paper's number), `exists_unique_budget`,
  `unique_triple`; "exactly once" needs a list `B` without repetition.
-/

namespace Trust

open Program

/-- An enumerator (def:enumerator), with the bound as an argument. -/
abbrev Enumerator := Program → ℕ → List Graph

namespace Enumerator

/-- Complete: every full execution is listed. -/
def Complete (E : Enumerator) : Prop :=
  ∀ (Q : Program) (n : ℕ), Q.Bounded n → ∀ F, FullSC Q F → F ∈ E Q n

/-- Sound: only full executions are listed. -/
def Sound (E : Enumerator) : Prop :=
  ∀ (Q : Program) (n : ℕ), Q.Bounded n → ∀ F, F ∈ E Q n → FullSC Q F

/-- Optimal: no graph is listed twice. -/
def Optimal (E : Enumerator) : Prop :=
  ∀ (Q : Program) (n : ℕ), Q.Bounded n → (E Q n).Nodup

end Enumerator

variable {A : Type}

/-- The triples `(b, κ, F)` on which `Check` evaluates `f`. -/
def checkItems (E : Enumerator) (P : Program) (B : List A) (u : A → Tid → List (Option Val))
    (μ : A → Loc → Val) (K : ℕ) : List (A × (Tid → ℕ) × Graph) :=
  B.flatMap (fun b => (budgets P.threads K).flatMap (fun κ =>
    ((E ((P.residual (u b) (μ b)).trunc κ) K).filter (fun F => decide (F.size ≤ K + 1))).map
      (fun F => (b, κ, F))))

/-- The two tests of `Check` on one graph. -/
def checkOK [DecidableEq A] (B : List A) (abad : A → Bool) (f : A → Graph → A) (K : ℕ)
    (b : A) (F : Graph) : Bool :=
  if F.size = K + 1 then decide (f b F ∈ B) else !abad (f b F)

/-- The procedure `Check` of cor:enum: it goes through all triples, without
stopping at a failed test; on each it evaluates `f` once (inside `checkOK`),
and it returns the verdict and the number of evaluations. -/
def Check [DecidableEq A] (E : Enumerator) (P : Program) (B : List A) (abad : A → Bool)
    (u : A → Tid → List (Option Val)) (μ : A → Loc → Val) (f : A → Graph → A) (K : ℕ) :
    Bool × ℕ :=
  (checkItems E P B u μ K).foldl
    (fun acc x => (checkOK B abad f K x.1 x.2.2 && acc.1, acc.2 + 1))
    (true, 0)

/-! ### Statements -/

/-- prop:trust-enum: the explorer is a complete enumerator. -/
theorem exploreC_complete : Enumerator.Complete exploreC := by
  rintro Q n hn F ⟨⟨hW, hE, hc⟩, hf⟩
  exact ((exploreC_spec hn).2 F).mpr ⟨hW, hE, hc, hf⟩

/-- prop:trust-enum: the explorer is a sound enumerator. -/
theorem exploreC_sound : Enumerator.Sound exploreC := by
  intro Q n hn F hF
  obtain ⟨hW, hE, hc, hf⟩ := ((exploreC_spec hn).2 F).mp hF
  exact ⟨⟨hW, hE, hc⟩, hf⟩

/-- prop:trust-enum: the explorer is an optimal enumerator. -/
theorem exploreC_optimal : Enumerator.Optimal exploreC :=
  fun _ _ hn => (exploreC_spec hn).1

/-- The budget programs are bounded by `K`. -/
theorem budget_program_bounded {P : Program} {u : Tid → List (Option Val)} {μ : Loc → Val}
    {K : ℕ} {κ : Tid → ℕ} (hκ : IsBudget P.threads K κ) :
    ((P.residual u μ).trunc κ).Bounded K :=
  Program.trunc_bounded hκ.le

variable {P : Program}

/-- The result of the traversal of `Check`. -/
theorem foldl_check {α : Type} (l : List α) (t : α → Bool) (acc : Bool × ℕ) :
    l.foldl (fun acc x => (t x && acc.1, acc.2 + 1)) acc =
      (l.all t && acc.1, acc.2 + l.length) := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    simp only [List.all_cons, List.length_cons, Prod.mk.injEq]
    constructor
    · cases t a <;> cases l.all t <;> cases acc.1 <;> rfl
    · omega

/-- The verdict of `Check`: all tests succeed. -/
theorem check_fst [DecidableEq A] (E : Enumerator) (P : Program) (B : List A) (abad : A → Bool)
    (u : A → Tid → List (Option Val)) (μ : A → Loc → Val) (f : A → Graph → A) (K : ℕ) :
    (Check E P B abad u μ f K).1 =
      (checkItems E P B u μ K).all (fun x => checkOK B abad f K x.1 x.2.2) := by
  have h := foldl_check (checkItems E P B u μ K)
    (fun x => checkOK B abad f K x.1 x.2.2) (true, 0)
  unfold Check
  rw [h]
  simp

/-- A sound, complete and optimal enumerator lists `Full(Q)`: the length of
its list is the number of full executions. -/
theorem Enumerator.length_eq_ncard {E : Enumerator} (hS : E.Sound) (hC : E.Complete)
    (hO : E.Optimal) {Q : Program} {n : ℕ} (hn : Q.Bounded n) :
    (E Q n).length = Set.ncard {F | FullSC Q F} := by
  classical
  have hset : {F | FullSC Q F} = ↑(E Q n).toFinset := by
    ext F
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset]
    exact ⟨hC Q n hn F, hS Q n hn F⟩
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup (hO Q n hn)]


/-- The triples of `Check` for a sound enumerator. -/
theorem mem_checkItems {E : Enumerator} (hE : E.Sound) {B : List A}
    {u : A → Tid → List (Option Val)} {μ : A → Loc → Val} {K : ℕ} {b : A} {κ : Tid → ℕ}
    {F : Graph} (hin : (b, κ, F) ∈ checkItems E P B u μ K) :
    b ∈ B ∧ IsBudget P.threads K κ ∧ FullSC ((P.residual (u b) (μ b)).trunc κ) F ∧
      F.size ≤ K + 1 := by
  unfold checkItems at hin
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter] at hin
  obtain ⟨b', hb', κ', hκ', F', ⟨hF', hsz⟩, heq⟩ := hin
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  have hκ := (mem_budgets P.threads_nodup).mp hκ'
  exact ⟨hb', hκ, hE _ K (budget_program_bounded hκ) _ hF', of_decide_eq_true hsz⟩

/-- For a complete enumerator, every full execution of a budget program of an
element of `B` is among the triples. -/
theorem checkItems_complete {E : Enumerator} (hE : E.Complete) {B : List A}
    {u : A → Tid → List (Option Val)} {μ : A → Loc → Val} {K : ℕ} {b : A} (hb : b ∈ B)
    {κ : Tid → ℕ} (hκ : IsBudget P.threads K κ) {F : Graph}
    (hF : FullSC ((P.residual (u b) (μ b)).trunc κ) F) :
    (b, κ, F) ∈ checkItems E P B u μ K := by
  have hκ' : IsBudget (P.residual (u b) (μ b)).threads K κ := hκ
  exact List.mem_flatMap.mpr ⟨b, hb, List.mem_flatMap.mpr ⟨κ,
    (mem_budgets P.threads_nodup).mpr hκ, List.mem_map.mpr ⟨F, List.mem_filter.mpr
      ⟨hE _ K (budget_program_bounded hκ) F hF,
        decide_eq_true (size_le_of_exec_trunc hκ' hF.1)⟩, rfl⟩⟩⟩

/-- cor:enum (1), for a complete enumerator: if `Check` accepts, `P` is safe. -/
theorem check_sound_of_complete [DecidableEq A] {E : Enumerator} (hE : E.Complete)
    (Abs : Abstraction P A)
    {Bad : Set Graph} {abad : A → Bool}
    (hdet : Abs.Determines Bad {a | abad a = true}) (hext : ExtClosed P Bad)
    {B : List A} (hinit : Abs.α (Graph.init P.mem) ∈ B) (hdisj : ∀ b ∈ B, abad b = false)
    {K : ℕ} (hK : 1 ≤ K) (f : A → Graph → A)
    (hf : ∀ G, ExecSC P G → Abs.α G ∈ B →
      ∀ H, GReach (P.residual G.trace G.memOf) SC H → H.size ≤ K + 1 →
        f (Abs.α G) H = Abs.α (G.comp H))
    (hacc : (Check E P B abad Abs.u Abs.μ f K).1 = true) : Safe P SC Bad := by
  have hall : (checkItems E P B Abs.u Abs.μ K).all
      (fun x => checkOK B abad f K x.1 x.2.2) = true := by
    rw [← check_fst]
    exact hacc
  by_cases hne : P.threads = []
  · -- no thread: the initial graph is the only reachable graph
    intro G hG hbad
    have hGE : ExecSC P G := greach_iff.mp hG
    have hemp : G.events = ∅ := by
      by_contra h
      obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr h
      have := hGE.2.1.tid_mem hGE.1 he
      rw [hne] at this
      cases this
    have hinitG : G = Graph.init P.mem := by
      rw [← hGE.2.1.1]
      exact hGE.1.eq_init_of_events_eq_empty hemp
    have h1 : abad (Abs.α G) = true := (hdet G hGE).mp hbad
    rw [hinitG, hdisj _ hinit] at h1
    cases h1
  · refine Abs.ksound (B := {a | a ∈ B}) hdet hK ⟨hinit, fun G hG hα => ?_⟩
    have hα' : Abs.α G ∈ B := hα
    refine (Abs.stepOK_iff_full hne hdet hext (fun b hb h => ?_) hG).mpr ?_
    · have hb' : b ∈ B := hb
      have h' : abad b = true := h
      rw [hdisj b hb'] at h'
      cases h'
    · intro κ hκ F hF
      have hreach : GReach (P.residual G.trace G.memOf) SC F :=
        (cover_prefix (Q := P.residual G.trace G.memOf) hκ hF hF.1.1.isPrefixOf_refl).1
      have hsz : F.size ≤ K + 1 :=
        size_le_of_exec_trunc (Q := P.residual G.trace G.memOf) hκ hF.1
      rw [← Abs.res_eq hG] at hF
      have hin := checkItems_complete hE hα' hκ hF
      have hok : checkOK B abad f K (Abs.α G) F = true := List.all_eq_true.mp hall _ hin
      unfold checkOK at hok
      rw [hf G hG hα' F hreach hsz] at hok
      refine ⟨fun h => ?_, fun h hb => ?_⟩
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at hok
        exact of_decide_eq_true hok
      · have hne' : ¬ F.size = K + 1 := by omega
        have hb' : abad (Abs.α (G.comp F)) = true := hb
        rw [ite_eq_right_of_eq_false _ _ (eq_false hne'), hb'] at hok
        cases hok

/-- cor:enum (1) with the verified explorer of TruSt as the enumerator. -/
theorem check_sound [DecidableEq A] (Abs : Abstraction P A) {Bad : Set Graph} {abad : A → Bool}
    (hdet : Abs.Determines Bad {a | abad a = true}) (hext : ExtClosed P Bad)
    {B : List A} (hinit : Abs.α (Graph.init P.mem) ∈ B) (hdisj : ∀ b ∈ B, abad b = false)
    {K : ℕ} (hK : 1 ≤ K) (f : A → Graph → A)
    (hf : ∀ G, ExecSC P G → Abs.α G ∈ B →
      ∀ H, GReach (P.residual G.trace G.memOf) SC H → H.size ≤ K + 1 →
        f (Abs.α G) H = Abs.α (G.comp H))
    (hacc : (Check exploreC P B abad Abs.u Abs.μ f K).1 = true) : Safe P SC Bad :=
  check_sound_of_complete exploreC_complete Abs hdet hext hinit hdisj hK f hf hacc

/-- cor:enum (1) with the hypotheses of the paper: the abstraction is
compositional. The hypothesis is not used. -/
theorem check_sound_paper [DecidableEq A] (Abs : Abstraction P A) (_hcomp : Abs.Compositional)
    {Bad : Set Graph} {abad : A → Bool}
    (hdet : Abs.Determines Bad {a | abad a = true}) (hext : ExtClosed P Bad)
    {B : List A} (hinit : Abs.α (Graph.init P.mem) ∈ B) (hdisj : ∀ b ∈ B, abad b = false)
    {K : ℕ} (hK : 1 ≤ K) (f : A → Graph → A)
    (hf : ∀ G, ExecSC P G → Abs.α G ∈ B →
      ∀ H, GReach (P.residual G.trace G.memOf) SC H → H.size ≤ K + 1 →
        f (Abs.α G) H = Abs.α (G.comp H))
    (hacc : (Check exploreC P B abad Abs.u Abs.μ f K).1 = true) : Safe P SC Bad :=
  check_sound Abs hdet hext hinit hdisj hK f hf hacc

/-- cor:enum (2): for a sound enumerator, a `K`-inductive list of realised
values is accepted. -/
theorem check_accepts [DecidableEq A] {E : Enumerator} (hE : E.Sound) (Abs : Abstraction P A)
    {abad : A → Bool} {B : List A} {K : ℕ}
    (hB : Abs.KInductive {a | abad a = true} {a | a ∈ B} K)
    (hreal : ∀ b ∈ B, Abs.Realised b) (f : A → Graph → A)
    (hf : ∀ G, ExecSC P G → Abs.α G ∈ B →
      ∀ H, GReach (P.residual G.trace G.memOf) SC H → H.size ≤ K + 1 →
        f (Abs.α G) H = Abs.α (G.comp H)) :
    (Check E P B abad Abs.u Abs.μ f K).1 = true := by
  rw [check_fst]
  refine List.all_eq_true.mpr ?_
  rintro ⟨b, κ, F⟩ hin
  obtain ⟨hb, hκ, hF, hsz⟩ := mem_checkItems hE hin
  obtain ⟨G, hG, rfl⟩ := hreal b hb
  have hF' : FullSC ((P.residual G.trace G.memOf).trunc κ) F := by
    rw [← Abs.res_eq hG]
    exact hF
  have hreach : GReach (P.residual G.trace G.memOf) SC F :=
    (cover_prefix (Q := P.residual G.trace G.memOf) hκ hF' hF'.1.1.isPrefixOf_refl).1
  obtain ⟨h1, h2⟩ := hB.2 G hG hb F hreach
  change checkOK B abad f K (Abs.α G) F = true
  unfold checkOK
  rw [hf G hG hb F hreach hsz]
  by_cases h : F.size = K + 1
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
    exact decide_eq_true (h1 h)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
    have h3 : ¬ abad (Abs.α (G.comp F)) = true := h2 (by omega)
    cases hx : abad (Abs.α (G.comp F))
    · rfl
    · exact absurd hx h3

/-- cor:enum (3): for a sound and optimal enumerator and a list `B` without
repetition, no triple is evaluated twice. -/
theorem checkItems_nodup {E : Enumerator} (hO : E.Optimal) {B : List A}
    (hB : B.Nodup) (u : A → Tid → List (Option Val)) (μ : A → Loc → Val) (K : ℕ) :
    (checkItems E P B u μ K).Nodup := by
  unfold checkItems
  refine List.nodup_flatMap.mpr ⟨fun b _ => ?_, ?_⟩
  · refine List.nodup_flatMap.mpr ⟨fun κ hκ => ?_, ?_⟩
    · have hκ' := (mem_budgets P.threads_nodup).mp hκ
      exact ((hO _ K (budget_program_bounded hκ')).filter _).map
        (fun _ _ h => (Prod.mk.inj (Prod.mk.inj h).2).2)
    · refine List.Pairwise.imp (fun {κ κ'} hne => ?_) (budgets_nodup P.threads_nodup K)
      intro x h₁ h₂
      obtain ⟨F₁, -, rfl⟩ := List.mem_map.mp h₁
      obtain ⟨F₂, -, h⟩ := List.mem_map.mp h₂
      exact hne (Prod.mk.inj (Prod.mk.inj h).2).1.symm
  · refine List.Pairwise.imp (fun {b b'} hne => ?_) hB
    intro x h₁ h₂
    obtain ⟨κ₁, -, h₁'⟩ := List.mem_flatMap.mp h₁
    obtain ⟨F₁, -, rfl⟩ := List.mem_map.mp h₁'
    obtain ⟨κ₂, -, h₂'⟩ := List.mem_flatMap.mp h₂
    obtain ⟨F₂, -, h⟩ := List.mem_map.mp h₂'
    exact hne (Prod.mk.inj h).1.symm

/-- cor:enum (3): the number of evaluations is the number of triples. -/
theorem check_count [DecidableEq A] (E : Enumerator) (B : List A) (abad : A → Bool)
    (u : A → Tid → List (Option Val)) (μ : A → Loc → Val) (f : A → Graph → A) (K : ℕ) :
    (Check E P B abad u μ f K).2 = (checkItems E P B u μ K).length := by
  have h := foldl_check (checkItems E P B u μ K)
    (fun x => checkOK B abad f K x.1 x.2.2) (true, 0)
  unfold Check
  rw [h]
  simp

/-- cor:enum (3), first clause: for a sound enumerator the number of
evaluations is the sum over `b ∈ B` and the budgets `κ` of size `K` of the
lengths of the lists of the budget programs (for a sound, complete and optimal
enumerator these lists are the sets `Full(Q^b|_κ)` without repetition). -/
theorem check_count_eq_sum [DecidableEq A] {E : Enumerator} (hE : E.Sound) (B : List A)
    (abad : A → Bool) (u : A → Tid → List (Option Val)) (μ : A → Loc → Val)
    (f : A → Graph → A) (K : ℕ) :
    (Check E P B abad u μ f K).2 =
      (B.map (fun b => ((budgets P.threads K).map (fun κ =>
        (E ((P.residual (u b) (μ b)).trunc κ) K).length)).sum)).sum := by
  rw [check_count]
  unfold checkItems
  rw [List.length_flatMap]
  congr 1
  refine List.map_congr_left (fun b _ => ?_)
  rw [List.length_flatMap]
  congr 1
  refine List.map_congr_left (fun κ hκ => ?_)
  have hκ' := (mem_budgets P.threads_nodup).mp hκ
  have hκ'' : IsBudget (P.residual (u b) (μ b)).threads K κ := hκ'
  rw [List.length_map, List.filter_eq_self.mpr]
  intro F hF
  exact decide_eq_true
    (size_le_of_exec_trunc hκ'' (hE _ K (budget_program_bounded hκ') F hF).1)

/-- cor:enum (3), first clause: for a sound, complete and optimal enumerator
`Check` evaluates `f` exactly `Σ_{b ∈ B} Σ_{|κ| = K} |Full(Q^b|_κ)|` times. -/
theorem check_count_eq_sum_ncard [DecidableEq A] {E : Enumerator} (hS : E.Sound)
    (hC : E.Complete) (hO : E.Optimal) (B : List A) (abad : A → Bool)
    (u : A → Tid → List (Option Val)) (μ : A → Loc → Val) (f : A → Graph → A) (K : ℕ) :
    (Check E P B abad u μ f K).2 =
      (B.map (fun b => ((budgets P.threads K).map (fun κ =>
        Set.ncard {F | FullSC ((P.residual (u b) (μ b)).trunc κ) F})).sum)).sum := by
  rw [check_count_eq_sum hS]
  congr 1
  refine List.map_congr_left (fun b _ => ?_)
  congr 1
  refine List.map_congr_left (fun κ hκ => ?_)
  exact Enumerator.length_eq_ncard hS hC hO
    (budget_program_bounded ((mem_budgets P.threads_nodup).mp hκ))

/-- cor:enum (3): a reachable graph of size `K + 1` of the residual program of
`b` belongs to exactly one triple of `b` (which occurs once in the traversal
by `checkItems_nodup`). -/
theorem unique_triple {E : Enumerator} (hS : E.Sound) (hC : E.Complete)
    {B : List A} {u : A → Tid → List (Option Val)}
    {μ : A → Loc → Val} {K : ℕ} {b : A} (hb : b ∈ B) {H : Graph}
    (hH : GReach (P.residual (u b) (μ b)) SC H) (hsz : H.size = K + 1) :
    ∃ κ, (b, κ, H) ∈ checkItems E P B u μ K ∧
      ∀ x ∈ checkItems E P B u μ K, x.1 = b → x.2.2 = H → x = (b, κ, H) := by
  obtain ⟨hκ, hF⟩ := cover_full hH hsz
  have hκP : IsBudget P.threads K H.cnt := hκ
  refine ⟨H.cnt, checkItems_complete (P := P) (u := u) (μ := μ) hC hb hκP hF, ?_⟩
  rintro ⟨b', κ', H'⟩ hin rfl rfl
  obtain ⟨-, hκ', hF', -⟩ := mem_checkItems (P := P) hS hin
  rw [cover_unique (Q := P.residual (u b') (μ b')) hκ' hF'.1 hsz]

/-- cor:enum (3), last part: a reachable graph of size `K + 1` of the residual
program of `b` is evaluated for exactly one budget. -/
theorem exists_unique_budget {E : Enumerator} (hS : E.Sound) (hC : E.Complete) {B : List A}
    {u : A → Tid → List (Option Val)} {μ : A → Loc → Val} {K : ℕ} {b : A} (hb : b ∈ B)
    {H : Graph} (hH : GReach (P.residual (u b) (μ b)) SC H) (hsz : H.size = K + 1) :
    ∃! κ, (b, κ, H) ∈ checkItems E P B u μ K := by
  obtain ⟨hκ, hF⟩ := cover_full hH hsz
  have hκP : IsBudget P.threads K H.cnt := hκ
  refine ⟨H.cnt, checkItems_complete (P := P) (u := u) (μ := μ) hC hb hκP hF, fun κ' hin => ?_⟩
  obtain ⟨-, hκ', hF', -⟩ := mem_checkItems (P := P) hS hin
  exact cover_unique (Q := P.residual (u b) (μ b)) hκ' hF'.1 hsz

end Trust
