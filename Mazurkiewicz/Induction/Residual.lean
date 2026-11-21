import Mazurkiewicz.Induction.Interleave

/-!
# Residual and truncated programs

`induction-popl`, `bridge.tex` sec:residual: def:residual, lem:residual.

How the text is read here.

* The residual `p_[u]` of a sequential program is `SeqProg.resid p u`.
* The residual program `P_{s,μ}` is `Program.residual P u μ`, given by
  representatives `u t` of the local states `s_t` (lem:residual (2): it does
  not depend on them). It has the threads of `P` and no action for a thread
  that is not listed, on every trace: `Program` requires this at the empty
  trace, and `u t` need not be the trace of an execution.
* The `K`-truncation `P|_K` is `Program.trunc P (fun _ => K)` of the port
  (`Trust/Budget.lean`).
* lem:residual (1): the closure claim ("are sequential programs") is vacuous
  here, since no domain condition is imposed on programs (plan, decision
  D1). Its second half, `p|_K` bounded by `K`, is `Program.trunc_bounded`.
* lem:residual (4) is `Program.exec_trunc_iff` of the port; its last sentence
  is `Program.exec_trunc_of_size_le`.
-/

namespace Trust

open Program

/-- The residual `p_[u]` of a sequential program after `u` (def:residual). -/
def SeqProg.resid (p : SeqProg) (u : List (Option Val)) : SeqProg := fun x => p (u ++ x)

/-- The residual program `P_{s,μ}` (def:residual), from representatives `u t`
of the local states. -/
def Program.residual (P : Program) (u : Tid → List (Option Val)) (μ : Loc → Val) : Program where
  threads := P.threads
  threads_nodup := P.threads_nodup
  step := fun t x => if t ∈ P.threads then P.step t (u t ++ x) else none
  mem := μ
  step_none := by
    intro t ht
    simp [ht]

/-! ### Statements -/

/-- lem:residual (2) for sequential programs: `p_[u] = p_[u']` iff
`u ≈_p u'`. -/
theorem SeqProg.resid_eq_iff {p : SeqProg} {u u' : List (Option Val)} :
    p.resid u = p.resid u' ↔ FutEq p u u' :=
  ⟨fun h x => congrFun h x, fun h => funext h⟩

/-- lem:residual (2): the residual program does not depend on the
representatives. -/
theorem Program.residual_eq_iff {P : Program} {u u' : Tid → List (Option Val)} {μ : Loc → Val} :
    P.residual u μ = P.residual u' μ ↔ ∀ t ∈ P.threads, FutEq (P.step t) (u t) (u' t) := by
  constructor
  · intro h t ht x
    have := congrFun (congrFun (congrArg Program.step h) t) x
    simpa [Program.residual, ht] using this
  · intro h
    have hstep : (fun t x => if t ∈ P.threads then P.step t (u t ++ x) else none) =
        (fun t x => if t ∈ P.threads then P.step t (u' t ++ x) else none) := by
      funext t x
      by_cases ht : t ∈ P.threads
      · simp only [ht, ↓reduceIte]
        exact h t ht x
      · simp only [ht, ↓reduceIte]
    unfold Program.residual
    simp only [hstep]

/-- The map `[x]_{p_[u]} ↦ [u · x]_p` of lem:residual (3). -/
def St.ofResid {p : SeqProg} (u : List (Option Val)) (s : St (p.resid u)) : St p :=
  Quotient.liftOn s (fun x => St.mk p (u ++ x)) (fun x x' h => by
    refine St.mk_eq_mk.mpr (fun y => ?_)
    rw [List.append_assoc, List.append_assoc]
    exact h y)

/-- lem:residual (3): the map is injective. -/
theorem St.ofResid_injective {p : SeqProg} (u : List (Option Val)) :
    Function.Injective (St.ofResid (p := p) u) := by
  intro s s'
  refine Quotient.inductionOn₂ s s' (fun x x' h => ?_)
  have h' : FutEq p (u ++ x) (u ++ x') := St.mk_eq_mk.mp h
  refine St.mk_eq_mk.mpr (fun y => ?_)
  have := h' y
  rw [List.append_assoc, List.append_assoc] at this
  exact this

/-- lem:residual (4), last sentence: an execution of `P` with at most `K`
thread events is an execution of `P|_K`. -/
theorem Program.exec_trunc_of_size_le {P : Program} {G : Graph} (hG : G.Wf) (hE : P.Exec G)
    {K : ℕ} (h : G.size ≤ K + 1) : (P.trunc (fun _ => K)).Exec G := by
  refine (Program.exec_trunc_iff hG _).mpr ⟨hE, fun t => ?_⟩
  have h1 : G.cnt t ≤ G.events.card := Finset.card_filter_le _ _
  unfold Graph.size at h
  omega

end Trust
