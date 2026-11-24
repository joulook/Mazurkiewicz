import Mazurkiewicz.Must.AlgEx

/-!
# Optimality on examples (milestone M8)

Plan: row M8, deliverable "kernel-checked examples". For four programs (`pFuel`, Example 4.3,
the two p. 19 programs `pOp` (`p19_opus`) and `pAs` (`p19_astra`)), the reachable configurations
of the relation `StepM` (model `p2p`, consistency `consAPB`; tie-breaks `Sel.least` and, for
Example 4.3, `Sel.byRecv`) are pairwise distinct as graphs, and each graph is reached by one
configuration only:

  `ReachM M tie P c₁ → ReachM M tie P c₂ → c₁.G = c₂.G → c₁ = c₂`.

Method (no assumption on the explorer): the list `L` of configurations visited by M2's
reference explorer is computed by the kernel; `closedB` checks (kernel) that `L` contains the
initial configuration and is closed under the computed successors, and `keysNodup` that the
graphs of `L` are pairwise distinct. The bridge `stepM_iff_compute_p2p` (M4) turns closedness
under computed successors into closedness under `StepM`, so every reachable configuration is in
`L` (`reach_mem`), and the graphs of reachable configurations determine them (`optimal_of`).
Graphs are compared through `Graph.normalize` (which has `Supp`), so no `Supp` fact about the
computed list is needed.
-/

namespace Must

namespace OptimalEx

open MustFast MustFast' Examples Graph AlgEx

/-- A configuration with its graph normalized. -/
def nz (d : Config VPred) : Config VPred := ⟨d.G.normalize, d.order⟩

/-- `L` contains the initial configuration (by order and key). -/
def hasInit (L : List (Config VPred)) : Bool :=
  L.any fun d => decide (d.order = [] ∧ d.G.normalize.key = (Graph.empty : Graph VPred).key)

/-- `L` is closed under the computed successors (of the normalized configurations), by order
and key. -/
def closedB (V : Variant VPred) (P : Program VPred) (L : List (Config VPred)) : Bool :=
  L.all fun d => ((stepM AP V P (nz d)).getD []).all fun c' =>
    L.any fun d' => decide (d'.order = c'.order ∧ d'.G.normalize.key = c'.G.key)

/-- The graphs of `L` are pairwise distinct. -/
def keysNodup (L : List (Config VPred)) : Bool :=
  decide ((L.map fun d => d.G.normalize.key).Nodup)

/-- Every reachable configuration is, up to normalization of its graph, in a list that
contains the initial configuration and is closed under the computed successors. -/
theorem reach_mem {T : Sel VPred} {P : Program VPred} {L : List (Config VPred)}
    (hinit : hasInit L = true) (hcl : closedB (rep T) P L = true) {c : Config VPred}
    (hc : ReachM Model.p2p (T.pick AP) P c) :
    ∃ d ∈ L, d.order = c.order ∧ d.G.normalize.key = c.G.key := by
  induction hc with
  | refl =>
    obtain ⟨d, hd, hdk⟩ := List.any_eq_true.mp hinit
    exact ⟨d, hd, (of_decide_eq_true hdk).1, (of_decide_eq_true hdk).2⟩
  | @tail c c' hreach hstep ih =>
    obtain ⟨d, hd, hord, hkey⟩ := ih
    have hi : c.Inv Model.p2p P := ReachM.sound hreach
    have hceq : c = nz d := by
      have hG : d.G.normalize = c.G :=
        (eq_iff_key (supp_normalize _) hi.wf.supp).mpr hkey
      cases c
      simp only [nz, Config.mk.injEq]
      exact ⟨hG.symm, hord.symm⟩
    have hmem : c' ∈ (stepM AP (rep T) P (nz d)).getD [] := by
      rw [← hceq]
      exact ((stepM_iff_compute_p2p T P hi).2 c').mpr hstep
    have h1 := List.all_eq_true.mp hcl d hd
    obtain ⟨d', hd', hk⟩ := List.any_eq_true.mp (List.all_eq_true.mp h1 c' hmem)
    exact ⟨d', hd', (of_decide_eq_true hk).1, (of_decide_eq_true hk).2⟩

/-- If a list containing the initial configuration and closed under the computed successors
has pairwise distinct graphs, then reachable configurations with equal graphs are equal. -/
theorem optimal_of {T : Sel VPred} {P : Program VPred} {L : List (Config VPred)}
    (hinit : hasInit L = true) (hcl : closedB (rep T) P L = true)
    (hnd : keysNodup L = true) {c₁ c₂ : Config VPred}
    (h₁ : ReachM Model.p2p (T.pick AP) P c₁) (h₂ : ReachM Model.p2p (T.pick AP) P c₂)
    (hG : c₁.G = c₂.G) : c₁ = c₂ := by
  obtain ⟨d₁, hd₁, ho₁, hk₁⟩ := reach_mem hinit hcl h₁
  obtain ⟨d₂, hd₂, ho₂, hk₂⟩ := reach_mem hinit hcl h₂
  have hnd' := of_decide_eq_true hnd
  have hd : d₁ = d₂ := List.inj_on_of_nodup_map hnd' hd₁ hd₂ (hk₁.trans (hG ▸ hk₂.symm))
  subst hd
  cases c₁
  cases c₂
  simp only [Config.mk.injEq] at hG ⊢
  exact ⟨hG, ho₁.symm.trans ho₂⟩

/-! ### The examples -/

/-- The configurations visited by the reference explorer. -/
def seenOf (T : Sel VPred) (P : Program VPred) (fuel : ℕ) : List (Config VPred) :=
  (explore AP (rep T) P fuel).seen

/-- `pFuel` (`T0: a = send(T1,0)`, `T1: r = recv(); c = send(T0,0)`, `T2: b = send(T1,1)`; a
path of five steps that deletes and re-adds `c`): reachable configurations are determined by
their graphs. -/
theorem pFuel_optimal {c₁ c₂ : Config VPred} (h₁ : ReachM Model.p2p (Sel.least.pick AP) pFuel c₁)
    (h₂ : ReachM Model.p2p (Sel.least.pick AP) pFuel c₂) (hG : c₁.G = c₂.G) : c₁ = c₂ :=
  optimal_of (L := seenOf .least pFuel 100) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) h₁ h₂ hG

/-- Example 4.3 with the least tie-break. -/
theorem ex43_optimal {c₁ c₂ : Config VPred} (h₁ : ReachM Model.p2p (Sel.least.pick AP) ex43 c₁)
    (h₂ : ReachM Model.p2p (Sel.least.pick AP) ex43 c₂) (hG : c₁.G = c₂.G) : c₁ = c₂ :=
  optimal_of (L := seenOf .least ex43 1000) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) h₁ h₂ hG

/-- Example 4.3 with the receive-dependent tie-break `byRecv`. -/
theorem ex43_optimal_byRecv {c₁ c₂ : Config VPred}
    (h₁ : ReachM Model.p2p (Sel.byRecv.pick AP) ex43 c₁)
    (h₂ : ReachM Model.p2p (Sel.byRecv.pick AP) ex43 c₂) (hG : c₁.G = c₂.G) : c₁ = c₂ :=
  optimal_of (L := seenOf .byRecv ex43 1000) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) h₁ h₂ hG

/-- The program of `p19_opus` (the revisit source is not the scheduler's completion). -/
theorem pOp_optimal {c₁ c₂ : Config VPred} (h₁ : ReachM Model.p2p (Sel.least.pick AP) pOp c₁)
    (h₂ : ReachM Model.p2p (Sel.least.pick AP) pOp c₂) (hG : c₁.G = c₂.G) : c₁ = c₂ :=
  optimal_of (L := seenOf .least pOp 1000) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) h₁ h₂ hG

/-- The program of `p19_astra` (the deleted events are not inserted in scheduler order). -/
theorem pAs_optimal {c₁ c₂ : Config VPred} (h₁ : ReachM Model.p2p (Sel.least.pick AP) pAs c₁)
    (h₂ : ReachM Model.p2p (Sel.least.pick AP) pAs c₂) (hG : c₁.G = c₂.G) : c₁ = c₂ :=
  optimal_of (L := seenOf .least pAs 1000) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) h₁ h₂ hG

end OptimalEx

end Must

#print axioms Must.OptimalEx.reach_mem
#print axioms Must.OptimalEx.optimal_of
#print axioms Must.OptimalEx.pFuel_optimal
#print axioms Must.OptimalEx.ex43_optimal
#print axioms Must.OptimalEx.ex43_optimal_byRecv
#print axioms Must.OptimalEx.pOp_optimal
#print axioms Must.OptimalEx.pAs_optimal
