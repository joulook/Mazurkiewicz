import Mazurkiewicz.Pct.Coverage
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The coverage theorem as a count

`pctdpor`, `depth.tex`, thm:coverage: the bound `1/(n k^(d-1))`.

The parameters of RandS for `n + 1` threads `0, …, n`, depth `d` and length
bound `K` are a permutation `σ` of the threads and `d - 1` change points in
`[1, K]`: the type `Params n d K`, with `(n+1)! * K^(d-1)` elements
(`card_params`). A parameter is `Good` if RandS with it reaches a complete
schedule and every complete schedule it reaches is in the bug. `card_good`:
at least `n!` parameters are good. So a uniformly chosen parameter is good
with probability at least `n! / ((n+1)! K^(d-1)) = 1 / ((n+1) K^(d-1))`.

* `rhoOf σ` is the initial order: `σ t` for a thread `t ≤ n`, and `t` itself
  for the identifiers above `n`, which is injective.
* `kOf k` puts the change point `k i + 1` at the target `i + 1`.
-/

namespace Pct

open Function Relation

variable {Q : Prog} {L : Type} {d n K : ℕ}
variable {E : Labelling Q L} {D : Directive L d} {B : Set Sched}

/-- The parameters of RandS. -/
abbrev Params (n d K : ℕ) : Type := Equiv.Perm (Fin (n + 1)) × (Fin (d - 1) → Fin K)

/-- The initial order of a permutation of the threads `0, …, n`. -/
def rhoOf (σ : Equiv.Perm (Fin (n + 1))) (t : ℕ) : ℕ :=
  if h : t < n + 1 then (σ ⟨t, h⟩ : ℕ) else t

theorem rhoOf_injective (σ : Equiv.Perm (Fin (n + 1))) : Injective (rhoOf σ) := by
  intro (t : ℕ) (u : ℕ) h
  unfold rhoOf at h
  by_cases ht : t < n + 1 <;> by_cases hu : u < n + 1
  · simp only [ht, hu, ↓reduceDIte] at h
    have := σ.injective (Fin.ext h)
    exact Fin.mk.inj this
  · simp only [ht, hu, ↓reduceDIte] at h
    have := (σ ⟨t, ht⟩).isLt
    omega
  · simp only [ht, hu, ↓reduceDIte] at h
    have := (σ ⟨u, hu⟩).isLt
    omega
  · simp only [ht, hu, ↓reduceDIte] at h
    exact h

/-- The change points of RandS, indexed by the targets. -/
def kOf (k : Fin (d - 1) → Fin K) (j : Fin d) : ℕ :=
  if h : 1 ≤ j.val then (k ⟨j.val - 1, by have := j.isLt; omega⟩ : ℕ) + 1 else 0

/-- RandS with the parameter `x` reaches a complete schedule, and every
complete schedule that it reaches is in `B`. -/
def Good (Q : Prog) (B : Set Sched) (x : Params n d K) : Prop :=
  (∃ s, RandReach Q d (rhoOf x.1) (kOf x.2) s ∧ Q.Complete s.1) ∧
    ∀ s, RandReach Q d (rhoOf x.1) (kOf x.2) s → Q.Complete s.1 → s.1 ∈ B

theorem RandStep.congr {k k' : Fin d → ℕ} (h : ∀ j : Fin d, 1 ≤ j.val → k j = k' j)
    {x y : Sched × (Tid → ℕ)} (hs : RandStep Q d k x y) : RandStep Q d k' x y := by
  obtain ⟨t, ht, hS, hc⟩ := hs
  refine ⟨t, ht, hS, ?_⟩
  rcases hc with ⟨hno, hp⟩ | ⟨j, hj1, hk, hp, hmax⟩
  · exact Or.inl ⟨fun j hj1 => h j hj1 ▸ hno j hj1, hp⟩
  · exact Or.inr ⟨j, hj1, h j hj1 ▸ hk, hp, fun j' hj1' hk' => hmax j' hj1' (h j' hj1' ▸ hk')⟩

theorem RandReach.congr {ρ : Tid → ℕ} {k k' : Fin d → ℕ}
    (h : ∀ j : Fin d, 1 ≤ j.val → k j = k' j) {s : Sched × (Tid → ℕ)}
    (hs : RandReach Q d ρ k s) : RandReach Q d ρ k' s := by
  induction hs with
  | refl => exact ReflTransGen.refl
  | tail _ hstep ih => exact ReflTransGen.tail ih (hstep.congr h)

/-- For every permutation that puts the thread of the first target last
there are change points that make the parameter good. -/
theorem exists_good (hK : Q.Bounded K)
    (hmax : ∀ (p : Tid → ℕ) (S : Sched), (∃ t, t :: S ∈ Q.mem) → ∃ t, IsMaxEn Q p S t)
    (hE : E.Strict) (hd : 0 < d) (hg : D.PGuarantees E B)
    (ha : E.thr (D.b ⟨0, hd⟩) < n + 1) (σ : Equiv.Perm (Fin (n + 1)))
    (hσ : σ ⟨E.thr (D.b ⟨0, hd⟩), ha⟩ = 0) :
    ∃ k : Fin (d - 1) → Fin K, Good Q B (σ, k) := by
  have H : Hyp E D (rhoOf σ) B :=
    ⟨hE, rhoOf_injective σ, hd, by simp [rhoOf, ha, hσ], hg⟩
  obtain ⟨ℓ, hrange, -, hex, hall⟩ := coverage hK hmax H
  have hlt : ∀ i : Fin (d - 1), i.val + 1 < d := fun i => by have := i.isLt; omega
  let k : Fin (d - 1) → Fin K := fun i =>
    ⟨ℓ ⟨i.val + 1, hlt i⟩ - 1, by
      have := hrange ⟨i.val + 1, hlt i⟩ (by simp)
      omega⟩
  have hk : ∀ j : Fin d, 1 ≤ j.val → ℓ j = kOf k j := by
    intro j hj1
    have hj : (⟨j.val - 1 + 1, hlt ⟨j.val - 1, by have := j.isLt; omega⟩⟩ : Fin d) = j :=
      Fin.ext (by simp; omega)
    have h1 := (hrange j hj1).1
    simp only [kOf, hj1, ↓reduceDIte, k, hj]
    omega
  refine ⟨k, ?_, ?_⟩
  · obtain ⟨s, hs, hc⟩ := hex
    exact ⟨s, hs.congr hk, hc⟩
  · intro s hs hc
    exact hall s (hs.congr (fun j hj1 => (hk j hj1).symm)) hc

/-- thm:coverage as a count: at least `n!` of the parameters are good. -/
theorem card_good (hK : Q.Bounded K)
    (hmax : ∀ (p : Tid → ℕ) (S : Sched), (∃ t, t :: S ∈ Q.mem) → ∃ t, IsMaxEn Q p S t)
    (hE : E.Strict) (hd : 0 < d) (hg : D.PGuarantees E B)
    (ha : E.thr (D.b ⟨0, hd⟩) < n + 1) :
    n.factorial ≤ Nat.card {x : Params n d K // Good Q B x} := by
  let a : Fin (n + 1) := ⟨E.thr (D.b ⟨0, hd⟩), ha⟩
  let τ : Equiv.Perm (Fin n) → Equiv.Perm (Fin (n + 1)) :=
    fun e => (Equiv.Perm.decomposeFin.symm (a, e))⁻¹
  have hτ : ∀ e, τ e a = 0 := by
    intro e
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (Equiv.Perm.decomposeFin_symm_apply_zero a e).symm
  have hτinj : Injective τ := by
    intro e e' h
    have h' := inv_injective h
    have := Equiv.Perm.decomposeFin.symm.injective h'
    exact (Prod.mk.inj this).2
  have hgood := fun e => exists_good (n := n) (K := K) hK hmax hE hd hg ha (τ e) (hτ e)
  choose k hk using hgood
  let f : Equiv.Perm (Fin n) → {x : Params n d K // Good Q B x} := fun e => ⟨(τ e, k e), hk e⟩
  have hf : Injective f := by
    intro e e' h
    have := congrArg (fun x => x.1.1) h
    exact hτinj this
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at this

/-- The number of parameters. -/
theorem card_params : Nat.card (Params n d K) = (n + 1).factorial * K ^ (d - 1) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

end Pct
