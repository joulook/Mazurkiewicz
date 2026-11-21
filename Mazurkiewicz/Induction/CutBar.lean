import Mazurkiewicz.Induction.Bars
import Mazurkiewicz.Induction.Budgets
import Mazurkiewicz.Induction.MonoExample

/-!
# Cut states

`induction-popl`, `cuts.tex`, sec:cutstates: def:cutbar, lem:cutbar, for
plain programs under SC.

How the text is read here.

* A cut family is `C : ∀ t, Set (St (P.step t))`.
* The cut bar is defined from representatives `u t` of the local states
  `s_t`: `cutBar C u` is the set of the graphs `H` in which some thread `t`
  has a non-empty prefix `x` of its trace with `[u t ++ x] ∈ C t` (the thread
  has passed through a cut state; not: is at one). The paper's bar is its
  part in `Reach_SC(Q_b)`. `cutBar_congr`: on executions it does not depend
  on the representatives.
* `SegBound`: def:cutbar, with "defined on all proper prefixes of `x`" for
  the residual program.
* lem:cutbar: `init_not_mem_cutBar`, `cutBar_extClosed`, `cutBar_depthLe`
  (the sum is over the listed threads), `mem_boundary_cutBar`.
-/

namespace Trust

open Program

variable {P : Program}

/-- The cut bar (def:cutbar), from representatives `u` of the local states. -/
def cutBar (C : ∀ t, Set (St (P.step t))) (u : Tid → List (Option Val)) : Set Graph :=
  {H | ∃ t x, x ≠ [] ∧ x <+: H.trace t ∧ St.mk (P.step t) (u t ++ x) ∈ C t}

/-- A segment bound (def:cutbar). -/
def SegBound (C : ∀ t, Set (St (P.step t))) (u : Tid → List (Option Val)) (μ : Loc → Val)
    (L : Tid → ℕ) : Prop :=
  ∀ t ∈ P.threads, 1 ≤ L t ∧ ∀ x : List (Option Val), x.length = L t →
    (∀ y, y <+: x → y ≠ x → (P.residual u μ).step t y ≠ none) →
    ∃ x', x' ≠ [] ∧ x' <+: x ∧ St.mk (P.step t) (u t ++ x') ∈ C t

variable (C : ∀ t, Set (St (P.step t))) (u : Tid → List (Option Val))

/-- lem:cutbar: the initial graph is not in the cut bar. -/
theorem init_not_mem_cutBar (μ : Loc → Val) : Graph.init μ ∉ cutBar C u := by
  rintro ⟨t, x, hx, hpre, -⟩
  rw [Graph.trace_init] at hpre
  exact hx (List.prefix_nil.mp hpre)

/-- lem:cutbar: the cut bar is closed under extension. -/
theorem cutBar_extClosed (P' : Program) : BarExtClosed P' (cutBar C u) := by
  rintro H H' - hH' ⟨t, x, hx, hpre, hC⟩ hp
  obtain ⟨l, hl⟩ := Mono.trace_of_isPrefixOf (greach_iff.mp hH').1 hp t
  exact ⟨t, x, hx, hpre.trans (hl ▸ List.prefix_append _ _), hC⟩

/-- On executions the cut bar does not depend on the representatives. -/
theorem cutBar_congr {u u' : Tid → List (Option Val)}
    (h : ∀ t ∈ P.threads, FutEq (P.step t) (u t) (u' t)) {P' : Program}
    (hthr : P'.threads = P.threads) {H : Graph} (hH : ExecSC P' H) :
    H ∈ cutBar C u ↔ H ∈ cutBar C u' := by
  have key : ∀ {u u' : Tid → List (Option Val)},
      (∀ t ∈ P.threads, FutEq (P.step t) (u t) (u' t)) → H ∈ cutBar C u → H ∈ cutBar C u' := by
    rintro u u' h ⟨t, x, hx, hpre, hC⟩
    have ht : t ∈ P.threads := by
      by_contra hnt
      rw [hH.trace_of_not_mem (hthr ▸ hnt)] at hpre
      exact hx (List.prefix_nil.mp hpre)
    refine ⟨t, x, hx, hpre, ?_⟩
    rwa [← St.mk_eq_mk.mpr ((h t ht).append x)]
  exact ⟨key h, key (fun t ht => (futEq_equivalence _).symm (h t ht))⟩

/-- lem:cutbar: with a segment bound, the cut bar has depth at most
`1 + Σ_t (L_t - 1)`. -/
theorem cutBar_depthLe {μ : Loc → Val} {L : Tid → ℕ} (hL : SegBound C u μ L) :
    DepthLe (P.residual u μ) (cutBar C u) (1 + (P.threads.map (fun t => L t - 1)).sum) := by
  intro H hH hsz
  have hE : ExecSC (P.residual u μ) H := greach_iff.mp hH
  have hsum := hE.sum_cnt
  have hthr : (P.residual u μ).threads = P.threads := rfl
  rw [hthr] at hsum
  obtain ⟨t, ht, hLt⟩ : ∃ t ∈ P.threads, L t ≤ H.cnt t := by
    by_contra hno
    have hle : (P.threads.map H.cnt).sum ≤ (P.threads.map (fun t => L t - 1)).sum := by
      refine List.sum_le_sum (fun t ht => ?_)
      have h1 := (hL t ht).1
      have h2 : ¬ L t ≤ H.cnt t := fun h => hno ⟨t, ht, h⟩
      omega
    unfold Graph.size at hsz
    omega
  obtain ⟨-, hseg⟩ := hL t ht
  have hlen : ((H.trace t).take (L t)).length = L t := by
    rw [List.length_take, Graph.trace_length]
    omega
  obtain ⟨x', hx', hpre, hC⟩ := hseg _ hlen (by
    intro y hy hne
    have hylt : y.length < L t := by
      have h1 := hy.length_le
      rw [hlen] at h1
      rcases Nat.lt_or_ge y.length (L t) with h | h
      · exact h
      · exact absurd (hy.eq_of_length_le (by rw [hlen]; exact h)) hne
    have hy' : y <+: H.trace t := hy.trans (List.take_prefix _ _)
    have hyeq : y = H.traceBefore t y.length := by
      rw [Graph.traceBefore_eq_take H t (by omega)]
      exact List.prefix_iff_eq_take.mp hy'
    obtain ⟨e, he, het, hei⟩ := (hE.1.exists_idx_iff t y.length).mpr (by omega)
    have := hE.2.1.2 e he
    rw [het, hei, ← hyeq] at this
    rw [this]
    simp)
  exact ⟨t, x', hx', hpre.trans (List.take_prefix _ _), hC⟩

/-- lem:cutbar: the boundary of the cut bar. -/
theorem mem_boundary_cutBar (P' : Program) {H : Graph} :
    H ∈ boundary P' (cutBar C u) ↔
      GReach P' SC H ∧ ∃ H' t, GReach P' SC H' ∧ H' ∉ cutBar C u ∧ MStep P' t H' H ∧
        St.mk (P.step t) (u t ++ H.trace t) ∈ C t := by
  constructor
  · rintro ⟨⟨t', x, hx, hpre, hC⟩, hH, H', t, hH', hout, hs⟩
    refine ⟨hH, H', t, hH', hout, hs, ?_⟩
    obtain ⟨a, -, ha, -⟩ := hs.new_event
    have htr := hs.trace ha t'
    by_cases htt : t' = t
    · subst htt
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)] at htr
      rw [htr] at hpre
      rcases List.prefix_concat_iff.mp hpre with heq | hpre'
      · rw [htr, ← heq]
        exact hC
      · exact absurd ⟨t', x, hx, hpre', hC⟩ hout
    · rw [ite_eq_right_of_eq_false _ _ (eq_false htt)] at htr
      rw [htr] at hpre
      exact absurd ⟨t', x, hx, hpre, hC⟩ hout
  · rintro ⟨hH, H', t, hH', hout, hs, hC⟩
    refine ⟨⟨t, H.trace t, ?_, List.prefix_refl _, hC⟩, hH, H', t, hH', hout, hs⟩
    obtain ⟨a, -, ha, -⟩ := hs.new_event
    have htr := hs.trace ha t
    rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)] at htr
    rw [htr]
    simp

end Trust
