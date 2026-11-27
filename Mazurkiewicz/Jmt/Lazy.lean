import Mazurkiewicz.Jmt.Structure

/-!
# Unjustified reads and lazy states

A read of an execution is *unjustified* if its source does not happen before
it. This file proves that in a justification of `T` the unjustified reads of
the execution of stage `i` are exactly the unjustified reads of `T` committed
before stage `i`. It then defines *lazy states* `(E, θ, Z)`, which record an
execution, an obligation for each of its unjustified reads and frozen edges,
and *lazy steps* between them, and proves that the valid executions are the
executions of the lazy states reachable from an initial lazy state.

Facts about the executions of a program are hypotheses here, because the
abstract executions of `Jmt/Stage` do not include them: the initialization
key is not a read; a committed key that is a read of `T` is a read of the
execution of its stage (whether a key is a read depends on the key only);
and, to commit a set one key at a time along happens-before, executions are
`KExec.Regular` (finitely many actions, happens-before a strict partial
order).

Main statements:

* `Jmt.Justifies.unj_eq`: `unj (E (i + 1)) = unj T ∩ C i`.
* `Jmt.LStep.K_eq`: the commit set of the target of a lazy step is `K₁ ∪ B`.
* `Jmt.LReach.reach`: a reachable lazy state `(E, θ, Z)` gives the reachable
  stage state `(E, K, K, Z)`, with `K` its commit set.
* `Jmt.Justifies.lreach`: a justification of `T` gives a reachable lazy state
  with execution `T`.
* `Jmt.lazy`: **lazy form**, `T` is valid iff a lazy state with execution `T`
  is reachable.
-/

namespace Jmt

variable {Key Val : Type*}

/-- The unjustified reads of an execution: the reads whose source does not
happen before them. -/
def KExec.unj (E : KExec Key Val) : Set Key :=
  {r | ∃ w, E.rf r = some w ∧ ¬ E.hb w r}

variable {Ex : Set (KExec Key Val)} {init : Key}

/-- Commit sets grow. -/
theorem Justifies.mono_le {T : KExec Key Val} {n : ℕ} {E : ℕ → KExec Key Val}
    {C : ℕ → Set Key} (h : Justifies Ex init T n E C) :
    ∀ {i j : ℕ}, i ≤ j → j ≤ n → C i ⊆ C j := by
  intro i j hij
  induction hij with
  | refl => exact fun _ => subset_rfl
  | step _ ih => exact fun hj => (ih (by omega)).trans (h.mono _ (by omega))

/-- A committed key other than the initialization key is committed at some
stage. -/
theorem Justifies.commit_stage {T : KExec Key Val} {n : ℕ} {E : ℕ → KExec Key Val}
    {C : ℕ → Set Key} (h : Justifies Ex init T n E C) {r : Key} (hr : r ≠ init) :
    ∀ {i : ℕ}, r ∈ C i → ∃ j < i, r ∈ C (j + 1) ∧ r ∉ C j
  | 0, hi => by
    rw [h.c0] at hi
    exact absurd hi hr
  | i + 1, hi => by
    by_cases hc : r ∈ C i
    · obtain ⟨j, hj, h1, h2⟩ := h.commit_stage hr hc
      exact ⟨j, by omega, h1, h2⟩
    · exact ⟨i, by omega, hi, hc⟩

/-- The source in `T` of a committed read of `T` is committed, at the latest
together with the read's predecessor stage. -/
theorem Justifies.source_mem {T : KExec Key Val} {n : ℕ} {E : ℕ → KExec Key Val}
    {C : ℕ → Set Key} (h : Justifies Ex init T n E C) (hinit : T.rf init = none)
    (hrd : ∀ i < n, ∀ r ∈ C (i + 1), (T.rf r).isSome → ((E (i + 1)).rf r).isSome)
    {i : ℕ} (hi : i ≤ n) {r w : Key} (hr : r ∈ C i) (hw : T.rf r = some w) : w ∈ C i := by
  have hne : r ≠ init := by
    rintro rfl
    rw [hinit] at hw
    exact absurd hw (by simp)
  obtain ⟨j, hj, h1, h2⟩ := h.commit_stage hne hr
  have hjn : j < n := by omega
  obtain ⟨w0, hw0⟩ := Option.isSome_iff_exists.mp (hrd j hjn r h1 (by simp [hw]))
  obtain ⟨-, w', hw', hmem⟩ := h.j7 j hjn r h1 h2 w0 hw0
  rw [hw] at hw'
  cases hw'
  exact h.mono_le (by omega) hi hmem

/-- **Unjustified reads of a stage.** In a justification of `T`, the
unjustified reads of the execution of stage `i + 1` are the unjustified reads
of `T` in the commit set of stage `i`. -/
theorem Justifies.unj_eq {T : KExec Key Val} {n : ℕ} {E : ℕ → KExec Key Val}
    {C : ℕ → Set Key} (h : Justifies Ex init T n E C) (hinit : T.rf init = none)
    (hrd : ∀ i < n, ∀ r ∈ C (i + 1), (T.rf r).isSome → ((E (i + 1)).rf r).isSome)
    {i : ℕ} (hi : i < n) : (E (i + 1)).unj = T.unj ∩ C i := by
  ext r
  constructor
  · rintro ⟨w, hw, hnb⟩
    have hr : r ∈ C i := by
      by_contra hc
      exact hnb (h.j6 i hi r w hw hc)
    have hT : T.rf r = some w := by rw [← h.j5 i hi r hr]; exact hw
    have hwC : w ∈ C i := h.source_mem hinit hrd (by omega) hr hT
    refine ⟨⟨w, hT, fun hb => hnb ?_⟩, hr⟩
    exact (h.j2 i hi w (h.mono i hi hwC) r (h.mono i hi hr)).mpr hb
  · rintro ⟨⟨w, hT, hnb⟩, hr⟩
    have hwC : w ∈ C i := h.source_mem hinit hrd (by omega) hr hT
    refine ⟨w, by rw [h.j5 i hi r hr]; exact hT, fun hb => hnb ?_⟩
    exact (h.j2 i hi w (h.mono i hi hwC) r (h.mono i hi hr)).mp hb

/-- The unjustified reads of a justified execution are committed before the
last stage. -/
theorem Justifies.unj_subset {T : KExec Key Val} {n : ℕ} {E : ℕ → KExec Key Val}
    {C : ℕ → Set Key} (h : Justifies Ex init T n E C) (hinit : T.rf init = none)
    (hrd : ∀ i < n, ∀ r ∈ C (i + 1), (T.rf r).isSome → ((E (i + 1)).rf r).isSome) :
    T.unj ⊆ C (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := h.pos; omega⟩
  have := h.unj_eq hinit hrd (i := m) (by omega)
  rw [h.en] at this
  intro r hr
  have hr' : r ∈ T.unj ∩ C m := by rw [← this]; exact hr
  simpa using hr'.2

/-! ## Closure, lazy states and lazy steps -/

/-- The keys reachable from `X` by following sources: `x ∈ X`, and the source
of a key of the closure is in the closure. -/
inductive KExec.Cl (E : KExec Key Val) (X : Set Key) : Key → Prop
  | base {x : Key} : x ∈ X → E.Cl X x
  | rf {x w : Key} : E.Cl X x → E.rf x = some w → E.Cl X w

/-- The closure `cl_E(X)`: the least set containing `X` that contains the
source of each of its reads (`KExec.subset_cl`, `KExec.cl_rf`,
`KExec.cl_subset`). -/
def KExec.cl (E : KExec Key Val) (X : Set Key) : Set Key :=
  {x | E.Cl X x}

theorem KExec.subset_cl {E : KExec Key Val} {X : Set Key} : X ⊆ E.cl X :=
  fun _ h => KExec.Cl.base h

theorem KExec.cl_rf {E : KExec Key Val} {X : Set Key} {x w : Key} (hx : x ∈ E.cl X)
    (hw : E.rf x = some w) : w ∈ E.cl X :=
  KExec.Cl.rf hx hw

/-- The closure is contained in every set that contains `X` and the sources of
its keys. -/
theorem KExec.cl_subset {E : KExec Key Val} {X Y : Set Key} (hX : X ⊆ Y)
    (hY : ∀ y ∈ Y, ∀ w, E.rf y = some w → w ∈ Y) : E.cl X ⊆ Y := by
  intro x hx
  induction hx with
  | base h => exact hX h
  | rf _ hw ih => exact hY _ ih _ hw

/-- The reads of an execution: the actions that have a source. -/
def KExec.Rd (E : KExec Key Val) : Set Key :=
  {r | r ∈ E.A ∧ (E.rf r).isSome}

/-- The image `E.rf[S]` of a set under the source map. -/
def KExec.rfImg (E : KExec Key Val) (S : Set Key) : Set Key :=
  {w | ∃ r ∈ S, E.rf r = some w}

/-- The commit set `K(λ) = cl_E({init} ∪ unj(E) ∪ θ[unj(E)])` of a lazy state
with execution `E` and obligations `θ`. -/
def KExec.lazyK (E : KExec Key Val) (init : Key) (θ : Key → Key) : Set Key :=
  E.cl ({init} ∪ E.unj ∪ θ '' E.unj)

/-- The set `K₁ = cl_E(K ∪ E.rf[B] ∪ E⁺.rf[B])` of a lazy step from execution
`E` with obligations `θ` to execution `E'` with batch `B`. -/
def lazyK1 (init : Key) (E : KExec Key Val) (θ : Key → Key) (E' : KExec Key Val)
    (B : Set Key) : Set Key :=
  E.cl (E.lazyK init θ ∪ E.rfImg B ∪ E'.rfImg B)

section Closure

variable {E E' : KExec Key Val} {θ : Key → Key} {B : Set Key}

theorem KExec.init_mem_lazyK : init ∈ E.lazyK init θ :=
  KExec.subset_cl (Or.inl (Or.inl (Set.mem_singleton init)))

theorem KExec.unj_subset_lazyK : E.unj ⊆ E.lazyK init θ :=
  fun _ hr => KExec.subset_cl (Or.inl (Or.inr hr))

theorem KExec.obl_mem_lazyK {r : Key} (hr : r ∈ E.unj) : θ r ∈ E.lazyK init θ :=
  KExec.subset_cl (Or.inr ⟨r, hr, rfl⟩)

theorem lazyK_subset_lazyK1 : E.lazyK init θ ⊆ lazyK1 init E θ E' B :=
  fun _ hx => KExec.subset_cl (Or.inl (Or.inl hx))

theorem rfImg_subset_lazyK1 : E.rfImg B ⊆ lazyK1 init E θ E' B :=
  fun _ hx => KExec.subset_cl (Or.inl (Or.inr hx))

theorem rfImg'_subset_lazyK1 : E'.rfImg B ⊆ lazyK1 init E θ E' B :=
  fun _ hx => KExec.subset_cl (Or.inr hx)

theorem lazyK1_rf {x w : Key} (hx : x ∈ lazyK1 init E θ E' B) (hw : E.rf x = some w) :
    w ∈ lazyK1 init E θ E' B :=
  KExec.cl_rf hx hw

theorem lazyK1_subset {Y : Set Key}
    (hX : E.lazyK init θ ∪ E.rfImg B ∪ E'.rfImg B ⊆ Y)
    (hY : ∀ y ∈ Y, ∀ w, E.rf y = some w → w ∈ Y) : lazyK1 init E θ E' B ⊆ Y :=
  KExec.cl_subset hX hY

end Closure

/-- A lazy state `(E, θ, Z)`. The obligation map `θ` is a total function; only
its values on the unjustified reads of `E` matter (`IsLazy`, `LState.K`). -/
structure LState (Key Val : Type*) where
  E : KExec Key Val
  θ : Key → Key
  Z : Set (Key × Key)

/-- The commit set `K(λ)` of a lazy state. -/
def LState.K (init : Key) (l : LState Key Val) : Set Key :=
  l.E.lazyK init l.θ

/-- `l` is a lazy state: `θ` maps the unjustified reads of `l.E` to actions
of `l.E`, and `(E, K(λ), K(λ), Z)` is a stage state (which includes
`E ∈ Ex`). -/
structure IsLazy (Ex : Set (KExec Key Val)) (init : Key) (l : LState Key Val) : Prop where
  obl_mem : ∀ r ∈ l.E.unj, l.θ r ∈ l.E.A
  stage : IsStage Ex init ⟨l.E, l.K init, l.K init, l.Z⟩

/-- An initial lazy state: no unjustified reads and no frozen edges. -/
def IsLInit (Ex : Set (KExec Key Val)) (init : Key) (l : LState Key Val) : Prop :=
  IsLazy Ex init l ∧ l.E.unj = ∅ ∧ l.Z = ∅

/-- A lazy step `l ⇝ l'` with batch `B`. The fields `obl_old` and `obl_new`
say `θ⁺ = θ ∪ {r ↦ E.rf r | r ∈ B}` on `unj(E⁺) = unj(E) ∪ B`. The field
`chain` gives the stage steps
`(E, K, K, Z) → (E, D₀, D₁, ·) → ⋯ → (E, D_{k-1}, D_k, ·) → (E, K₁, K₂, ·) →
(E⁺, K₂, K₂, Z⁺)` with `K = D₀`, `D_k = K₁` and `K₂ = K₁ ∪ B`: the sets `D_j`
are the commit sets of `σ j`, and the second and fourth components of the
intermediate states are determined by `Step.before_eq` and (F8). -/
structure LStep (Ex : Set (KExec Key Val)) (init : Key) (l l' : LState Key Val)
    (B : Set Key) : Prop where
  src : IsLazy Ex init l
  tgt : IsLazy Ex init l'
  ne : B.Nonempty
  batch : B ⊆ l.E.Rd \ l.K init
  unj_eq : l'.E.unj = l.E.unj ∪ B
  disj : Disjoint l.E.unj B
  rf_mem : ∀ r ∈ B, ∀ w, l'.E.rf r = some w → w ∈ l.E.A
  obl_old : ∀ r ∈ l.E.unj, l'.θ r = l.θ r
  obl_new : ∀ r ∈ B, l.E.rf r = some (l'.θ r)
  chain : ∃ (k : ℕ) (σ : ℕ → State Key Val),
    σ 0 = ⟨l.E, l.K init, l.K init, l.Z⟩ ∧
    (∀ j ≤ k + 1, (σ j).E = l.E) ∧
    (σ k).commit = lazyK1 init l.E l.θ l'.E B ∧
    (σ (k + 1)).commit = lazyK1 init l.E l.θ l'.E B ∪ B ∧
    σ (k + 2) = ⟨l'.E, lazyK1 init l.E l.θ l'.E B ∪ B,
      lazyK1 init l.E l.θ l'.E B ∪ B, l'.Z⟩ ∧
    ∀ j < k + 2, Step Ex init (σ j) (σ (j + 1))

/-- The lazy states reachable from an initial lazy state by lazy steps. -/
def LReach (Ex : Set (KExec Key Val)) (init : Key) (l : LState Key Val) : Prop :=
  ∃ l₀, IsLInit Ex init l₀ ∧ Relation.ReflTransGen (fun a b => ∃ B, LStep Ex init a b B) l₀ l

/-! ## The commit set after a lazy step -/

/-- **Commit set after a lazy step** (core form). The hypotheses are the
conditions of a lazy step that the statement uses; `hf2`, `hf5`, `hf7` are
(F2), (F5), (F7) of the last stage step `(E, K₁, K₂, ·) → (E', K₂, K₂, ·)`. -/
theorem lazyK_step {E E' : KExec Key Val} {θ θ' : Key → Key} {B : Set Key}
    (hB : B ⊆ E.Rd \ E.lazyK init θ) (hunj : E'.unj = E.unj ∪ B)
    (hθ : ∀ r ∈ E.unj, θ' r = θ r) (hθB : ∀ r ∈ B, E.rf r = some (θ' r))
    (hf2 : ∀ a ∈ lazyK1 init E θ E' B ∪ B, ∀ b ∈ lazyK1 init E θ E' B ∪ B,
      E'.hb a b ↔ E.hb a b)
    (hf5 : ∀ a ∈ lazyK1 init E θ E' B, E'.rf a = E.rf a)
    (hf7 : ∀ r ∈ B, r ∉ lazyK1 init E θ E' B → ∀ w, E.rf r = some w →
      ∃ w', E'.rf r = some w' ∧ w' ∈ lazyK1 init E θ E' B) :
    E'.lazyK init θ' = lazyK1 init E θ E' B ∪ B := by
  set K1 := lazyK1 init E θ E' B with hK1
  have hKK1 : E.lazyK init θ ⊆ K1 := lazyK_subset_lazyK1
  -- `B` and `K₁` are disjoint
  have hdisj : ∀ r ∈ B, r ∉ K1 := by
    intro r hrB hrK1
    obtain ⟨⟨-, hsome⟩, hnK⟩ := hB hrB
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hsome
    have hhb : E.hb w r := by
      by_contra hn
      exact hnK (KExec.unj_subset_lazyK ⟨w, hw, hn⟩)
    have hwK1 : w ∈ K1 := lazyK1_rf hrK1 hw
    have hw' : E'.rf r = some w := (hf5 r hrK1).trans hw
    have hu : r ∈ E'.unj := by rw [hunj]; exact Or.inr hrB
    obtain ⟨w2, hw2, hn2⟩ := hu
    rw [hw'] at hw2
    obtain rfl := Option.some.inj hw2
    exact hn2 ((hf2 w (Or.inl hwK1) r (Or.inr hrB)).mpr hhb)
  -- `K₂` is closed under the sources of `E'`
  have hcl2 : ∀ y ∈ K1 ∪ B, ∀ w, E'.rf y = some w → w ∈ K1 ∪ B := by
    rintro y (hy | hy) w hw
    · rw [hf5 y hy] at hw
      exact Or.inl (lazyK1_rf hy hw)
    · obtain ⟨w0, hw0⟩ := Option.isSome_iff_exists.mp (hB hy).1.2
      obtain ⟨w', hw', hmem⟩ := hf7 y hy (hdisj y hy) w0 hw0
      rw [hw'] at hw
      obtain rfl := Option.some.inj hw
      exact Or.inl hmem
  apply Set.Subset.antisymm
  · refine KExec.cl_subset ?_ hcl2
    rintro x ((hx | hx) | ⟨r, hr, rfl⟩)
    · rw [Set.mem_singleton_iff.1 hx]
      exact Or.inl (hKK1 KExec.init_mem_lazyK)
    · rw [hunj] at hx
      rcases hx with hx | hx
      · exact Or.inl (hKK1 (KExec.unj_subset_lazyK hx))
      · exact Or.inr hx
    · rw [hunj] at hr
      rcases hr with hr | hr
      · rw [hθ r hr]
        exact Or.inl (hKK1 (KExec.obl_mem_lazyK hr))
      · exact Or.inl (rfImg_subset_lazyK1 ⟨r, hr, hθB r hr⟩)
  · set L := E'.lazyK init θ' with hL
    have hBL : B ⊆ L := fun r hr => KExec.unj_subset_lazyK (by rw [hunj]; exact Or.inr hr)
    have hclS : ∀ y ∈ K1 ∩ L, ∀ w, E.rf y = some w → w ∈ K1 ∩ L := by
      rintro y ⟨hy1, hy2⟩ w hw
      refine ⟨lazyK1_rf hy1 hw, KExec.cl_rf hy2 ?_⟩
      rw [hf5 y hy1]
      exact hw
    have hKS : E.lazyK init θ ⊆ K1 ∩ L := by
      refine KExec.cl_subset ?_ hclS
      rintro x ((hx | hx) | ⟨r, hr, rfl⟩)
      · rw [Set.mem_singleton_iff.1 hx]
        exact ⟨hKK1 KExec.init_mem_lazyK, KExec.init_mem_lazyK⟩
      · refine ⟨hKK1 (KExec.unj_subset_lazyK hx), KExec.unj_subset_lazyK ?_⟩
        rw [hunj]
        exact Or.inl hx
      · refine ⟨hKK1 (KExec.obl_mem_lazyK hr), ?_⟩
        rw [← hθ r hr]
        exact KExec.obl_mem_lazyK (by rw [hunj]; exact Or.inl hr)
    have hK1S : K1 ⊆ K1 ∩ L := by
      refine lazyK1_subset ?_ hclS
      rintro x ((hx | ⟨r, hr, hw⟩) | ⟨r, hr, hw⟩)
      · exact hKS hx
      · refine ⟨rfImg_subset_lazyK1 ⟨r, hr, hw⟩, ?_⟩
        rw [hθB r hr] at hw
        obtain rfl := Option.some.inj hw
        exact KExec.obl_mem_lazyK (by rw [hunj]; exact Or.inr hr)
      · exact ⟨rfImg'_subset_lazyK1 ⟨r, hr, hw⟩, KExec.cl_rf (hBL hr) hw⟩
    rintro x (hx | hx)
    · exact (hK1S hx).2
    · exact hBL hx

/-- **Commit set after a lazy step** (`lem:lazy-commit`): if `l ⇝ l'` with
batch `B`, then `K(l') = K₁ ∪ B`. -/
theorem LStep.K_eq {l l' : LState Key Val} {B : Set Key} (h : LStep Ex init l l' B) :
    l'.K init = lazyK1 init l.E l.θ l'.E B ∪ B := by
  obtain ⟨k, σ, -, hE, hk, hk1, hlast, hsteps⟩ := h.chain
  have hs : Step Ex init (σ (k + 1)) (σ (k + 2)) := hsteps (k + 1) (by omega)
  have hE1 : (σ (k + 1)).E = l.E := hE (k + 1) le_rfl
  have hb1 : (σ (k + 1)).before = lazyK1 init l.E l.θ l'.E B :=
    (hsteps k (by omega)).before_eq.trans hk
  have hE2 : (σ (k + 2)).E = l'.E := by rw [hlast]
  refine lazyK_step h.batch h.unj_eq h.obl_old h.obl_new ?_ ?_ ?_
  · intro a ha b hb
    have := hs.f2 a (by rw [hk1]; exact ha) b (by rw [hk1]; exact hb)
    rwa [hE1, hE2] at this
  · intro a ha
    have := hs.f5 a (by rw [hb1]; exact ha)
    rwa [hE1, hE2] at this
  · intro r hr hr' w hw
    obtain ⟨w', hw', hmem⟩ := hs.f7 r (by rw [hk1]; exact Or.inr hr) (by rw [hb1]; exact hr') w
      (by rw [hE1]; exact hw)
    rw [hE2] at hw'
    rw [hb1] at hmem
    exact ⟨w', hw', hmem⟩

/-! ## From lazy states to stage states -/

/-- The commit set of an initial lazy state is `{init}`, if the
initialization key is not a read. -/
theorem IsLInit.K_eq {l : LState Key Val} (h : IsLInit Ex init l)
    (hinit : l.E.rf init = none) : l.K init = {init} := by
  apply Set.Subset.antisymm
  · refine KExec.cl_subset ?_ ?_
    · rintro x ((hx | hx) | ⟨r, hr, -⟩)
      · exact hx
      · rw [h.2.1] at hx
        exact absurd hx (Set.notMem_empty x)
      · rw [h.2.1] at hr
        exact absurd hr (Set.notMem_empty r)
    · intro y hy w hw
      rw [Set.mem_singleton_iff.1 hy, hinit] at hw
      exact absurd hw (by simp)
  · rw [Set.singleton_subset_iff]
    exact KExec.init_mem_lazyK

/-- **Lazy form, `⇐`, stage form.** A reachable lazy state `(E, θ, Z)` gives
the reachable stage state `(E, K, K, Z)` with `K = K(λ)`. The hypothesis says
that the initialization key is not a read of an execution of the program. -/
theorem LReach.reach (hinit : ∀ E ∈ Ex, E.rf init = none) {l : LState Key Val}
    (h : LReach Ex init l) : Reach Ex init ⟨l.E, l.K init, l.K init, l.Z⟩ := by
  obtain ⟨l₀, h₀, hst⟩ := h
  induction hst with
  | refl =>
    have hK := h₀.K_eq (hinit _ h₀.1.stage.ex)
    exact ⟨0, fun _ => ⟨l₀.E, l₀.K init, l₀.K init, l₀.Z⟩,
      ⟨⟨h₀.1.stage, hK, hK, h₀.2.2⟩, fun i hi => absurd hi (by omega)⟩, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨B, hB⟩ := hstep
    obtain ⟨k, σ, h0, -, -, -, hlast, hsteps⟩ := hB.chain
    have hr : ∀ j ≤ k + 2, Reach Ex init (σ j) := by
      intro j hj
      induction j with
      | zero => rw [h0]; exact ih
      | succ j ihj => exact (ihj (by omega)).step (hsteps j (by omega))
    have := hr (k + 2) le_rfl
    rw [hlast, ← hB.K_eq] at this
    exact this

/-- **Lazy form, `⇐`.** The execution of a reachable lazy state is valid. -/
theorem LReach.valid (hinit : ∀ E ∈ Ex, E.rf init = none) (hreg : ∀ E ∈ Ex, E.Regular)
    {l : LState Key Val} (h : LReach Ex init l) : Valid Ex init l.E :=
  (h.reach hinit).valid hreg

/-! ## From a justification to a lazy path -/

/-- A sequence with a new first element. -/
def consSeq {α : Type*} (a : α) (σ : ℕ → α) : ℕ → α
  | 0 => a
  | j + 1 => σ j

/-- A stage step that keeps the execution and commits more keys. -/
theorem Step.same {s : State Key Val} (hs : IsStage Ex init s) {c : Set Key}
    (hsub : s.commit ⊆ c) (hact : c ⊆ s.E.A)
    (hi1 : ∀ r w, s.E.rf r = some w → r ∉ s.commit → s.E.hb w r)
    (hi2 : ∀ r ∈ c, r ∉ s.commit → ∀ w, s.E.rf r = some w → w ∈ s.commit) :
    Step Ex init s ⟨s.E, s.commit, c, s.Z ∪ s.E.frz c⟩ where
  src := hs
  tgt :=
    { ex := hs.ex
      init_mem := hs.sub hs.init_mem
      sub := hsub
      act := hact
      i1 := hi1
      i2 := hi2
      i3 := by
        rintro p (hp | hp)
        · exact hs.i3 p hp
        · exact s.E.frz_sw _ hp }
  before_eq := rfl
  f2 := fun _ _ _ _ => Iff.rfl
  f3 := fun _ _ _ _ => Iff.rfl
  f4 := fun _ _ => rfl
  f5 := fun _ _ => rfl
  f7 := fun r hr hr' w hw => ⟨w, hw, hs.i2 r hr hr' w hw⟩
  f8 := rfl

/-- **Committing a set inside one execution.** From a stage state whose
unjustified reads are committed, a set `D` of actions that contains the
commit set and the sources of its keys is committed one key at a time,
along happens-before. This needs a regular execution. -/
theorem IsStage.chain {D : Set Key} :
    ∀ (N : ℕ) (s : State Key Val), IsStage Ex init s → s.E.Regular → s.E.unj ⊆ s.commit →
      s.commit ⊆ D → D ⊆ s.E.A → (∀ x ∈ D, ∀ w, s.E.rf x = some w → w ∈ D) →
      (D \ s.commit).ncard = N →
      ∃ (k : ℕ) (σ : ℕ → State Key Val), σ 0 = s ∧ (∀ j ≤ k, (σ j).E = s.E) ∧
        (σ k).commit = D ∧ (σ k).Z ⊆ s.Z ∪ s.E.frz D ∧ IsStage Ex init (σ k) ∧
        ∀ j < k, Step Ex init (σ j) (σ (j + 1)) := by
  intro N
  induction N with
  | zero =>
    intro s hs hreg hunj hsub hD hcl hN
    have hfin : (D \ s.commit).Finite := (hreg.finite.subset hD).sdiff
    have hempty : D \ s.commit = ∅ := (Set.ncard_eq_zero hfin).1 hN
    have hDc : D = s.commit := Set.Subset.antisymm (Set.sdiff_eq_empty.1 hempty) hsub
    exact ⟨0, fun _ => s, rfl, fun _ _ => rfl, hDc.symm, Set.subset_union_left, hs,
      fun j hj => absurd hj (by omega)⟩
  | succ N ih =>
    intro s hs hreg hunj hsub hD hcl hN
    have hfin : (D \ s.commit).Finite := (hreg.finite.subset hD).sdiff
    have hne : (D \ s.commit).Nonempty := by
      rw [← Set.ncard_pos hfin]
      omega
    obtain ⟨a, ha, hmin⟩ := hreg.exists_min (Set.sdiff_subset.trans hD) hne
    have hstep : Step Ex init s
        ⟨s.E, s.commit, insert a s.commit, s.Z ∪ s.E.frz (insert a s.commit)⟩ := by
      refine Step.same hs (Set.subset_insert _ _) (Set.insert_subset (hD ha.1) hs.act) ?_ ?_
      · intro r w hw hr
        by_contra hn
        exact hr (hunj ⟨w, hw, hn⟩)
      · intro r hr hr' w hw
        have hra : r = a := by
          rcases hr with h | h
          · exact h
          · exact absurd h hr'
        subst hra
        have hhb : s.E.hb w r := by
          by_contra hn
          exact hr' (hunj ⟨w, hw, hn⟩)
        by_contra hwc
        exact hmin w ⟨hcl r ha.1 w hw, hwc⟩ hhb
    have e : D \ insert a s.commit = (D \ s.commit) \ {a} := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have hcard : (D \ insert a s.commit).ncard = N := by
      rw [e, Set.ncard_sdiff_singleton_of_mem ha, hN]
      rfl
    obtain ⟨k, σ, h0, hE, hc, hZ, hst, hsteps⟩ :=
      ih _ hstep.tgt hreg (fun x hx => Set.mem_insert_of_mem _ (hunj hx))
        (Set.insert_subset ha.1 hsub) hD hcl hcard
    refine ⟨k + 1, consSeq s σ, rfl, ?_, hc, ?_, hst, ?_⟩
    · intro j hj
      cases j with
      | zero => rfl
      | succ j => exact hE j (by omega)
    · refine hZ.trans (Set.union_subset (Set.union_subset Set.subset_union_left ?_)
        Set.subset_union_right)
      exact (s.E.frz_mono (Set.insert_subset ha.1 hsub)).trans Set.subset_union_right
    · intro j hj
      cases j with
      | zero =>
        change Step Ex init s (σ 0)
        rw [h0]
        exact hstep
      | succ j => exact hsteps j (by omega)

open Classical in
/-- The obligation of a read in a justification: its source in the execution
of the stage that commits it. -/
noncomputable def obl (n : ℕ) (E : ℕ → KExec Key Val) (C : ℕ → Set Key) (r : Key) : Key :=
  if hex : ∃ j w, j < n ∧ r ∈ C (j + 1) ∧ r ∉ C j ∧ (E (j + 1)).rf r = some w then
    hex.choose_spec.choose
  else r

section Justification

variable {T : KExec Key Val} {n : ℕ} {E : ℕ → KExec Key Val} {C : ℕ → Set Key}

/-- A key is committed at one stage only. -/
theorem Justifies.stage_unique (h : Justifies Ex init T n E C) {r : Key} {j j' : ℕ}
    (hj : j < n) (hj' : j' < n) (h1 : r ∈ C (j + 1)) (h2 : r ∉ C j)
    (h1' : r ∈ C (j' + 1)) (h2' : r ∉ C j') : j = j' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact h2' (h.mono_le (by omega) (by omega) h1)
  · exact h2 (h.mono_le (by omega) (by omega) h1')

theorem Justifies.obl_eq (h : Justifies Ex init T n E C) {r w : Key} {j : ℕ} (hj : j < n)
    (h1 : r ∈ C (j + 1)) (h2 : r ∉ C j) (hw : (E (j + 1)).rf r = some w) :
    obl n E C r = w := by
  have hex : ∃ j w, j < n ∧ r ∈ C (j + 1) ∧ r ∉ C j ∧ (E (j + 1)).rf r = some w :=
    ⟨j, w, hj, h1, h2, hw⟩
  have key : ∀ j0 w0, (j0 < n ∧ r ∈ C (j0 + 1) ∧ r ∉ C j0 ∧ (E (j0 + 1)).rf r = some w0) →
      w0 = w := by
    rintro j0 w0 ⟨hj0, h10, h20, hw0⟩
    obtain rfl := h.stage_unique hj0 hj h10 h20 h1 h2
    rw [hw] at hw0
    exact (Option.some.inj hw0).symm
  unfold obl
  split_ifs
  exact key _ _ hex.choose_spec.choose_spec

variable (hinit : T.rf init = none)
  (hrd : ∀ i < n, ∀ r ∈ C (i + 1), (T.rf r).isSome → ((E (i + 1)).rf r).isSome)
include hinit hrd

/-- The commit set of stage `i` contains the sources in `E (i + 1)` of its
keys. -/
theorem Justifies.commit_closed (h : Justifies Ex init T n E C) {i : ℕ} (hi : i < n) :
    ∀ x ∈ C i, ∀ w, (E (i + 1)).rf x = some w → w ∈ C i := by
  intro x hx w hw
  rw [h.j5 i hi x hx] at hw
  exact h.source_mem hinit hrd (by omega) hx hw

omit hinit in
/-- The source of an unjustified read of `T` in the stage that commits it is
its obligation. -/
theorem Justifies.obl_rf (h : Justifies Ex init T n E C) {m : ℕ} (hm : m < n) {r : Key}
    (hr : r ∈ T.unj) (h1 : r ∈ C (m + 1)) (h2 : r ∉ C m) :
    (E (m + 1)).rf r = some (obl n E C r) := by
  obtain ⟨w, hw, -⟩ := hr
  obtain ⟨w0, hw0⟩ := Option.isSome_iff_exists.mp (hrd m hm r h1 (by simp [hw]))
  rw [h.obl_eq hm h1 h2 hw0]
  exact hw0

/-- The obligation of a committed unjustified read of `T` is committed. -/
theorem Justifies.obl_mem (h : Justifies Ex init T n E C) {r : Key} (hr : r ∈ T.unj)
    {i : ℕ} (hi : i ≤ n) (hri : r ∈ C i) : obl n E C r ∈ C i := by
  have hne : r ≠ init := by
    rintro rfl
    obtain ⟨w, hw, -⟩ := hr
    simp [hinit] at hw
  obtain ⟨j, hj, h1, h2⟩ := h.commit_stage hne hri
  have hjn : j < n := by omega
  obtain ⟨w0, hw0⟩ := Option.isSome_iff_exists.mp
    (hrd j hjn r h1 (by obtain ⟨w, hw, -⟩ := hr; simp [hw]))
  have := (h.j7 j hjn r h1 h2 w0 hw0).1
  rw [h.obl_eq hjn h1 h2 hw0]
  exact h.mono_le (by omega) hi this

/-- The commit set of the lazy state of stage `s + 1` is contained in `C s`. -/
theorem Justifies.lazyK_sub (h : Justifies Ex init T n E C) {s : ℕ} (hs : s < n) :
    (E (s + 1)).lazyK init (obl n E C) ⊆ C s := by
  refine KExec.cl_subset ?_ (h.commit_closed hinit hrd hs)
  rintro x ((hx | hx) | ⟨r, hr, rfl⟩)
  · rw [Set.mem_singleton_iff.1 hx]
    exact h.init_mem s (by omega)
  · rw [h.unj_eq hinit hrd hs] at hx
    exact hx.2
  · rw [h.unj_eq hinit hrd hs] at hr
    exact h.obl_mem hinit hrd hr.1 (by omega) hr.2

/-- The lazy state of stage `s + 1` with frozen edges `Z ⊆ sw (s + 1)`. -/
theorem Justifies.isLazy (h : Justifies Ex init T n E C) {s : ℕ} (hs : s < n)
    {Z : Set (Key × Key)} (hZ : ∀ p ∈ Z, (E (s + 1)).sw p.1 p.2) :
    IsLazy Ex init ⟨E (s + 1), obl n E C, Z⟩ where
  obl_mem := by
    intro r hr
    have hr' : r ∈ T.unj ∩ C s := by rw [← h.unj_eq hinit hrd hs]; exact hr
    exact h.j1 s hs (h.mono s hs (h.obl_mem hinit hrd hr'.1 (by omega) hr'.2))
  stage :=
    { ex := h.ex s hs
      init_mem := KExec.init_mem_lazyK
      sub := subset_rfl
      act := (h.lazyK_sub hinit hrd hs).trans ((h.mono s hs).trans (h.j1 s hs))
      i1 := by
        intro r w hw hr
        by_contra hn
        exact hr (KExec.unj_subset_lazyK ⟨w, hw, hn⟩)
      i2 := fun r hr hr' => absurd hr hr'
      i3 := hZ }

omit hrd in
/-- If unjustified reads of `T` are committed before stage `s + 1`, then the
last stage `m + 1 ≤ s` that commits some of them commits all of them that
are committed before stage `s + 1` and not before stage `m + 1`. -/
theorem Justifies.last_batch (h : Justifies Ex init T n E C) :
    ∀ {s : ℕ}, s ≤ n → (T.unj ∩ C s).Nonempty →
      ∃ m < s, (T.unj ∩ (C (m + 1) \ C m)).Nonempty ∧ T.unj ∩ C s = T.unj ∩ C (m + 1)
  | 0, _, hne => by
    exfalso
    obtain ⟨r, ⟨w, hw, -⟩, hr⟩ := hne
    rw [h.c0, Set.mem_singleton_iff] at hr
    simp [hr, hinit] at hw
  | s + 1, hs, hne => by
    by_cases heq : T.unj ∩ C (s + 1) = T.unj ∩ C s
    · rw [heq] at hne ⊢
      obtain ⟨m, hm, hB, he⟩ := h.last_batch (by omega) hne
      exact ⟨m, by omega, hB, he⟩
    · refine ⟨s, by omega, ?_, rfl⟩
      by_contra hB
      apply heq
      ext x
      constructor
      · rintro ⟨hx, hxC⟩
        refine ⟨hx, ?_⟩
        by_contra hxs
        exact hB ⟨x, hx, hxC, hxs⟩
      · rintro ⟨hx, hxC⟩
        exact ⟨hx, h.mono s (by omega) hxC⟩

/-- The lazy step from the lazy state of stage `m + 1`, which commits the
batch `B = unj T ∩ (C (m + 1) \ C m)`, to the lazy state of a later stage
`s + 1` before which no further unjustified read is committed. -/
theorem Justifies.lstep (h : Justifies Ex init T n E C)
    (hreg : ∀ i < n, (E (i + 1)).Regular) {m s : ℕ} (hms : m < s) (hs : s < n)
    (heq : T.unj ∩ C s = T.unj ∩ C (m + 1)) (hB : (T.unj ∩ (C (m + 1) \ C m)).Nonempty)
    {Z : Set (Key × Key)} (hZ : ∀ j, m ≤ j → j < n → ∀ p ∈ Z, (E (j + 1)).sw p.1 p.2) :
    ∃ Z' : Set (Key × Key), (∀ j, s ≤ j → j < n → ∀ p ∈ Z', (E (j + 1)).sw p.1 p.2) ∧
      LStep Ex init ⟨E (m + 1), obl n E C, Z⟩ ⟨E (s + 1), obl n E C, Z'⟩
        (T.unj ∩ (C (m + 1) \ C m)) := by
  have hm : m < n := by omega
  set B := T.unj ∩ (C (m + 1) \ C m) with hBdef
  set K := (E (m + 1)).lazyK init (obl n E C) with hK
  set K1 := lazyK1 init (E (m + 1)) (obl n E C) (E (s + 1)) B with hK1
  have hBC : B ⊆ C (m + 1) := fun r hr => hr.2.1
  have hCms : C (m + 1) ⊆ C s := h.mono_le (by omega) (by omega)
  have hCs : C s ⊆ C (s + 1) := h.mono s hs
  have hKsub : K ⊆ C m := h.lazyK_sub hinit hrd hm
  have hKK1 : K ⊆ K1 := lazyK_subset_lazyK1
  have hK1sub : K1 ⊆ C m := by
    refine lazyK1_subset ?_ (h.commit_closed hinit hrd hm)
    rintro x ((hx | ⟨r, hr, hw⟩) | ⟨r, hr, hw⟩)
    · exact hKsub hx
    · exact (h.j7 m hm r hr.2.1 hr.2.2 x hw).1
    · rw [h.j5 s hs r (hCms hr.2.1)] at hw
      obtain ⟨w0, hw0⟩ := Option.isSome_iff_exists.mp (hrd m hm r hr.2.1 (by simp [hw]))
      obtain ⟨-, w', hw', hmem⟩ := h.j7 m hm r hr.2.1 hr.2.2 w0 hw0
      rw [hw] at hw'
      obtain rfl := Option.some.inj hw'
      exact hmem
  have hK2sub : K1 ∪ B ⊆ C (m + 1) := Set.union_subset (hK1sub.trans (h.mono m hm)) hBC
  have hK2s : K1 ∪ B ⊆ C (s + 1) := hK2sub.trans (hCms.trans hCs)
  have hAm : C (m + 1) ⊆ (E (m + 1)).A := h.j1 m hm
  have hlz : IsLazy Ex init ⟨E (m + 1), obl n E C, Z⟩ :=
    h.isLazy hinit hrd hm (hZ m le_rfl hm)
  -- the chain from `(E, K, K, Z)` to a state with commit set `K₁`
  obtain ⟨k, σ, h0, hσE, hσc, hσZ, hσst, hσsteps⟩ :=
    IsStage.chain (D := K1) _ _ hlz.stage (hreg m hm) KExec.unj_subset_lazyK hKK1
      (hK1sub.trans ((h.mono m hm).trans hAm)) (fun x hx w hw => lazyK1_rf hx hw) rfl
  have hEk : (σ k).E = E (m + 1) := hσE k le_rfl
  -- the step committing the batch
  have hstep1 := Step.same (c := K1 ∪ B) hσst (by rw [hσc]; exact Set.subset_union_left)
    (by rw [hEk]; exact hK2sub.trans hAm)
    (by
      rw [hEk, hσc]
      intro r w hw hr
      by_contra hn
      exact hr (hKK1 (KExec.unj_subset_lazyK ⟨w, hw, hn⟩)))
    (by
      rw [hEk, hσc]
      rintro r (hr | hr) hr' w hw
      · exact absurd hr hr'
      · exact rfImg_subset_lazyK1 ⟨r, hr, hw⟩)
  set t1 : State Key Val := ⟨(σ k).E, (σ k).commit, K1 ∪ B, (σ k).Z ∪ (σ k).E.frz (K1 ∪ B)⟩
    with ht1
  set Z' := t1.Z ∪ (E (s + 1)).frz (K1 ∪ B) with hZ'
  have hZ'sw : ∀ j, s ≤ j → j < n → ∀ p ∈ Z', (E (j + 1)).sw p.1 p.2 := by
    intro j hj hjn p hp
    rcases hp with (hp | hp) | hp
    · rcases hσZ hp with hp | hp
      · exact hZ j (by omega) hjn p hp
      · exact h.j8 m hm j (by omega) hjn p
          ((E (m + 1)).frz_mono (hK1sub.trans (h.mono m hm)) hp)
    · rw [hEk] at hp
      exact h.j8 m hm j (by omega) hjn p ((E (m + 1)).frz_mono hK2sub hp)
    · exact h.j8 s hs j hj hjn p ((E (s + 1)).frz_mono hK2s hp)
  -- the last step, to the execution of stage `s + 1`
  have hstep2 : Step Ex init t1 ⟨E (s + 1), K1 ∪ B, K1 ∪ B, Z'⟩ :=
    { src := hstep1.tgt
      tgt :=
        { ex := h.ex s hs
          init_mem := Or.inl (hKK1 KExec.init_mem_lazyK)
          sub := subset_rfl
          act := hK2s.trans (h.j1 s hs)
          i1 := by
            intro r w hw hr
            by_contra hn
            have hu : r ∈ (E (s + 1)).unj := ⟨w, hw, hn⟩
            rw [h.unj_eq hinit hrd hs, heq] at hu
            apply hr
            by_cases hrm : r ∈ C m
            · left
              apply hKK1 (KExec.unj_subset_lazyK _)
              rw [h.unj_eq hinit hrd hm]
              exact ⟨hu.1, hrm⟩
            · exact Or.inr ⟨hu.1, hu.2, hrm⟩
          i2 := fun r hr hr' => absurd hr hr'
          i3 := hZ'sw s le_rfl hs }
      before_eq := rfl
      f2 := by
        intro a ha b hb
        change (E (s + 1)).hb a b ↔ (σ k).E.hb a b
        rw [hEk]
        exact (h.j2 s hs a (hK2s ha) b (hK2s hb)).trans
          (h.j2 m hm a (hK2sub ha) b (hK2sub hb)).symm
      f3 := by
        intro a ha b hb
        change (E (s + 1)).so a b ↔ (σ k).E.so a b
        rw [hEk]
        exact (h.j3 s hs a (hK2s ha) b (hK2s hb)).trans
          (h.j3 m hm a (hK2sub ha) b (hK2sub hb)).symm
      f4 := by
        intro a ha
        change (E (s + 1)).val a = (σ k).E.val a
        rw [hEk]
        exact (h.j4 s hs a (hK2s ha)).trans (h.j4 m hm a (hK2sub ha)).symm
      f5 := by
        intro a ha
        change (E (s + 1)).rf a = (σ k).E.rf a
        have ha' : a ∈ K1 := by rw [← hσc]; exact ha
        rw [hEk]
        exact (h.j5 s hs a (h.mono_le (by omega) (by omega) (hK1sub ha'))).trans
          (h.j5 m hm a (hK1sub ha')).symm
      f7 := by
        intro r hr hr' w hw
        have hr'' : r ∉ K1 := by rw [← hσc]; exact hr'
        have hrB : r ∈ B := by
          rcases hr with hr | hr
          · exact absurd hr hr''
          · exact hr
        obtain ⟨w', hw', -⟩ := hrB.1
        have hw'' : (E (s + 1)).rf r = some w' := (h.j5 s hs r (hCms hrB.2.1)).trans hw'
        refine ⟨w', hw'', ?_⟩
        change w' ∈ (σ k).commit
        rw [hσc]
        exact rfImg'_subset_lazyK1 ⟨r, hrB, hw''⟩
      f8 := rfl }
  -- the whole chain of stage steps
  let σ' : ℕ → State Key Val := fun j =>
    if j ≤ k then σ j else if j = k + 1 then t1 else ⟨E (s + 1), K1 ∪ B, K1 ∪ B, Z'⟩
  have hσ'le : ∀ j ≤ k, σ' j = σ j := fun j hj => by simp [σ', hj]
  have hσ'1 : σ' (k + 1) = t1 := by simp [σ']
  have hσ'2 : σ' (k + 2) = ⟨E (s + 1), K1 ∪ B, K1 ∪ B, Z'⟩ := by simp [σ']
  refine ⟨Z', hZ'sw, ?_⟩
  exact
    { src := hlz
      tgt := h.isLazy hinit hrd hs (hZ'sw s le_rfl hs)
      ne := hB
      batch := by
        intro r hr
        refine ⟨⟨hAm hr.2.1, hrd m hm r hr.2.1 ?_⟩, fun hk => hr.2.2 (hKsub hk)⟩
        obtain ⟨w, hw, -⟩ := hr.1
        simp [hw]
      unj_eq := by
        change (E (s + 1)).unj = (E (m + 1)).unj ∪ B
        rw [h.unj_eq hinit hrd hs, h.unj_eq hinit hrd hm, heq]
        ext x
        constructor
        · rintro ⟨hx, hxC⟩
          by_cases hxm : x ∈ C m
          · exact Or.inl ⟨hx, hxm⟩
          · exact Or.inr ⟨hx, hxC, hxm⟩
        · rintro (⟨hx, hxC⟩ | ⟨hx, hxC, -⟩)
          · exact ⟨hx, h.mono m hm hxC⟩
          · exact ⟨hx, hxC⟩
      disj := by
        rw [Set.disjoint_left]
        intro x hx hxB
        have hx' : x ∈ T.unj ∩ C m := by rw [← h.unj_eq hinit hrd hm]; exact hx
        exact hxB.2.2 hx'.2
      rf_mem := fun r hr w hw =>
        hAm (h.mono m hm (hK1sub (rfImg'_subset_lazyK1 ⟨r, hr, hw⟩)))
      obl_old := fun _ _ => rfl
      obl_new := fun r hr => h.obl_rf hrd hm hr.1 hr.2.1 hr.2.2
      chain := ⟨k, σ', by rw [hσ'le 0 (Nat.zero_le _)]; exact h0,
        fun j hj => by
          by_cases hjk : j ≤ k
          · rw [hσ'le j hjk]
            exact hσE j hjk
          · rw [show j = k + 1 by omega, hσ'1]
            exact hEk,
        by rw [hσ'le k le_rfl]; exact hσc, by rw [hσ'1], by rw [hσ'2],
        fun j hj => by
          by_cases hjk : j + 1 ≤ k
          · rw [hσ'le j (by omega), hσ'le (j + 1) hjk]
            exact hσsteps j (by omega)
          · by_cases hjk' : j = k
            · subst hjk'
              rw [hσ'le j le_rfl, hσ'1]
              exact hstep1
            · rw [show j = k + 1 by omega, hσ'1, hσ'2]
              exact hstep2⟩ }

/-- The lazy state of every stage `s + 1` of a justification is reachable,
with frozen edges that are synchronizes-with edges of all later stages. -/
theorem Justifies.lreach_stage (h : Justifies Ex init T n E C)
    (hreg : ∀ i < n, (E (i + 1)).Regular) :
    ∀ s < n, ∃ Z : Set (Key × Key), (∀ j, s ≤ j → j < n → ∀ p ∈ Z, (E (j + 1)).sw p.1 p.2) ∧
      LReach Ex init ⟨E (s + 1), obl n E C, Z⟩ := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro hs
  by_cases hne : (T.unj ∩ C s).Nonempty
  · obtain ⟨m, hms, hB, heq⟩ := h.last_batch hinit (by omega) hne
    obtain ⟨Z, hZ, l₀, h₀, hst⟩ := ih m hms (by omega)
    obtain ⟨Z', hZ', hstep⟩ := h.lstep hinit hrd hreg hms hs heq hB hZ
    exact ⟨Z', hZ', l₀, h₀, hst.tail ⟨_, hstep⟩⟩
  · refine ⟨∅, fun _ _ _ p hp => absurd hp (Set.notMem_empty p), _,
      ⟨h.isLazy hinit hrd hs (fun p hp => absurd hp (Set.notMem_empty p)), ?_, rfl⟩,
      Relation.ReflTransGen.refl⟩
    change (E (s + 1)).unj = ∅
    rw [h.unj_eq hinit hrd hs]
    exact Set.not_nonempty_iff_eq_empty.1 hne

/-- **Lazy form, `⇒`.** A justification of `T` gives a reachable lazy state
with execution `T`. Besides `hinit` and `hrd` (see the module docstring), the
stage executions are `Regular`, which is used to commit the keys of `K₁ \ K`
one at a time along happens-before. -/
theorem Justifies.lreach (h : Justifies Ex init T n E C)
    (hreg : ∀ i < n, (E (i + 1)).Regular) :
    ∃ (θ : Key → Key) (Z : Set (Key × Key)), LReach Ex init ⟨T, θ, Z⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := h.pos; omega⟩
  obtain ⟨Z, -, hr⟩ := h.lreach_stage hinit hrd hreg m (by omega)
  rw [h.en] at hr
  exact ⟨_, Z, hr⟩

end Justification

/-- **Lazy form** (`thm:lazy`). An execution is valid iff a lazy state with
this execution is reachable from an initial lazy state by lazy steps. The
hypotheses are facts about the executions of a program: the initialization
key is not a read (`hinit`); executions are `Regular` (`hreg`); and whether
an action is a read depends on its key only (`hkind`). -/
theorem lazy (hinit : ∀ E ∈ Ex, E.rf init = none) (hreg : ∀ E ∈ Ex, E.Regular)
    (hkind : ∀ E ∈ Ex, ∀ E' ∈ Ex, ∀ r ∈ E'.A, (E.rf r).isSome → (E'.rf r).isSome)
    (T : KExec Key Val) :
    Valid Ex init T ↔ ∃ (θ : Key → Key) (Z : Set (Key × Key)), LReach Ex init ⟨T, θ, Z⟩ := by
  constructor
  · rintro ⟨n, E, C, h⟩
    exact h.lreach (hinit T h.mem)
      (fun i hi r hr hT => hkind T h.mem (E (i + 1)) (h.ex i hi) r (h.j1 i hi hr) hT)
      (fun i hi => hreg _ (h.ex i hi))
  · rintro ⟨θ, Z, hl⟩
    exact hl.valid hinit hreg

end Jmt
