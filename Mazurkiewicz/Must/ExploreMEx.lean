import Mazurkiewicz.Must.Exit
import Mazurkiewicz.Must.AlgEx

/-!
# M9 on examples: `⟦P⟧` counted by the explorer, early exit

Plan: row M9, deliverable "kernel-checked examples". Model `p2p` with M2's `consAPB` (`AP`),
tie-break `Sel.least` (`rep .least`). For each program the kernel evaluates one run of M2's
explorer (`decide +kernel`: the run is not exhausted, and its counters); the general theorems
of `ExploreM.lean` and `Exit.lean` then give statements about `⟦P⟧` and about the reachable
configurations that do not mention the explorer.

* `Code.boundedB`, `ofCodes_bounded`: a decidable sufficient condition for `Program.Bounded`
  of a program given by codes.
* `pFuel` (the program of the fuel contract, a revisit that deletes an event), Example 4.1
  (`ex41`), Example 4.3 (`ex43`), Example 3.1 (`ex31`, p2p sends), `pOp`, `pAs` (the p. 19
  programs): `|⟦P⟧|` and the number of reachable configurations (= visits).
* Early exit: `pErr` (`T0: send(T1,0)`, `T1: r = recv(); if r = 1 then error`, `T2:
  send(T1,1)`) is erroneous; `pOk` (error only on value 5) is not; both by `completeM_exit`.
-/

namespace Must

namespace ExploreMEx

open MustFast MustFast' Examples Graph

/-! ### A decidable bound for programs given by codes -/

/-- Every trace of length at least `n` terminates the code. -/
def Code.boundedB : ℕ → Code → Bool
  | 0, .done => true
  | 0, _ => false
  | _ + 1, .done => true
  | n + 1, .send _ _ _ k => Code.boundedB n k
  | n + 1, .recv _ b _ ks kd kb =>
    (ks.all fun p => Code.boundedB n p.2) && Code.boundedB n kd && (b || Code.boundedB n kb)
  | n + 1, .nd _ _ ks kd => (ks.all fun p => Code.boundedB n p.2) && Code.boundedB n kd
  | _ + 1, .block => true
  | _ + 1, .error => true

theorem boundedB_branch {n : ℕ} {ks : List (ℕ × Code)} {kd : Code}
    (h1 : ks.all (fun p => Code.boundedB n p.2) = true) (h2 : Code.boundedB n kd = true)
    (v : ℕ) : Code.boundedB n (branch ks kd v) = true := by
  unfold branch
  cases hl : ks.lookup v with
  | none => exact h2
  | some k =>
    obtain ⟨p, hp, hpk⟩ : ∃ p ∈ ks, p.2 = k := by
      induction ks with
      | nil => simp at hl
      | cons q ks ih =>
        rcases q with ⟨a, b⟩
        by_cases hab : v = a
        · subst hab
          simp only [List.lookup_cons_self, Option.some.injEq] at hl
          exact ⟨(v, b), .head _, hl⟩
        · have hne : (v == a) = false := by simpa using hab
          simp only [List.lookup, hne] at hl
          obtain ⟨p, hp, hpk⟩ := ih (by rw [List.all_cons, Bool.and_eq_true] at h1; exact h1.2) hl
          exact ⟨p, .tail _ hp, hpk⟩
    rw [← hpk]
    exact List.all_eq_true.mp h1 p hp

theorem run_none_of_boundedB : ∀ (n : ℕ) (c : Code), Code.boundedB n c = true →
    ∀ u : List (Option ℕ), n ≤ u.length → c.run u = none
  | 0, .done, _, u, _ => by cases u <;> rfl
  | 0, .send .., h, _, _ => by simp [Code.boundedB] at h
  | 0, .recv .., h, _, _ => by simp [Code.boundedB] at h
  | 0, .nd .., h, _, _ => by simp [Code.boundedB] at h
  | 0, .block, h, _, _ => by simp [Code.boundedB] at h
  | 0, .error, h, _, _ => by simp [Code.boundedB] at h
  | _ + 1, _, _, [], hu => by simp at hu
  | n + 1, .done, _, _ :: _, _ => by simp [Code.run]
  | n + 1, .send _ _ _ k, h, _ :: tr, hu =>
    run_none_of_boundedB n k h tr (by simp at hu; omega)
  | n + 1, .recv _ b _ ks kd kb, h, x :: tr, hu => by
    simp only [Code.boundedB, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have hl : n ≤ tr.length := by simp at hu; omega
    cases x with
    | some v => exact run_none_of_boundedB n _ (boundedB_branch h1 h2 v) tr hl
    | none =>
      cases b with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, false_or] at h3
        exact run_none_of_boundedB n kb h3 tr hl
  | n + 1, .nd _ _ ks kd, h, x :: tr, hu => by
    simp only [Code.boundedB, Bool.and_eq_true] at h
    cases x with
    | some w => exact run_none_of_boundedB n _ (boundedB_branch h.1 h.2 w) tr (by simp at hu; omega)
    | none => rfl
  | n + 1, .block, _, _ :: _, _ => rfl
  | n + 1, .error, _, _ :: _, _ => rfl

theorem boundedB_done : ∀ n, Code.boundedB n .done = true
  | 0 => rfl
  | _ + 1 => rfl

/-- A program given by codes all bounded by `n` is bounded by `n`. -/
theorem ofCodes_bounded {cs : List Code} {n : ℕ} (h : cs.all (Code.boundedB n) = true) :
    (ofCodes cs).Bounded n := by
  intro t u hu
  change (codeStep cs t u) = none
  unfold codeStep
  have hb : Code.boundedB n (cs.getD t .done) = true := by
    rw [List.getD_eq_getElem?_getD]
    cases ht : cs[t]? with
    | none => exact boundedB_done n
    | some c => exact List.all_eq_true.mp h c (List.mem_of_getElem? ht)
  rw [run_none_of_boundedB n _ hb u hu]
  rfl

/-! ### `⟦P⟧` counted -/

/-- The explorer of the examples. -/
abbrev run (P : Program VPred) (fuel : ℕ) : Result VPred := explore AP (rep .least) P fuel

/-- The members of `⟦P⟧` and the reachable configurations, counted by a completed run. -/
theorem counts {P : Program VPred} {k fuel : ℕ} (hb : P.Bounded k)
    (hex : (run P fuel).exhausted = false) :
    {G | Model.p2p.Sem P G}.ncard = (run P fuel).reported.length ∧
      {c | ReachM Model.p2p (Sel.least.pick AP) P c}.ncard = (run P fuel).seen.length :=
  ⟨sem_ncard_of_not_exhausted consAPB_iff_p2p .least hb hex,
    reach_ncard_of_not_exhausted consAPB_iff_p2p .least hb hex⟩

theorem pFuel_bounded : pFuel.Bounded 2 := ofCodes_bounded (by decide +kernel)

/-- `pFuel`: `⟦P⟧` has 2 members, 7 configurations are reachable, and every fuel of at least
7 makes the explorer report exactly `⟦P⟧`, each member once. -/
theorem pFuel_counts : {G | Model.p2p.Sem pFuel G}.ncard = 2 ∧
    {c | ReachM Model.p2p (Sel.least.pick AP) pFuel c}.ncard = 7 := by
  have h := counts pFuel_bounded (fuel := 100) (by decide +kernel)
  rw [h.1, h.2]
  decide +kernel

theorem pFuel_spec {fuel : ℕ} (hf : 7 ≤ fuel) :
    (run pFuel fuel).exhausted = false ∧ ((run pFuel fuel).reported.map Config.G).Nodup ∧
      ∀ G, G ∈ (run pFuel fuel).reported.map Config.G ↔ Model.p2p.Sem pFuel G := by
  have h := exploreM_spec consAPB_iff_p2p .least pFuel_bounded
    (fuel := fuel) (by rw [pFuel_counts.2]; exact hf)
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem reorder_bounded {Q : Type} {P : Program Q} {n : ℕ} (hb : P.Bounded n)
    (l : List Tid) (h : l.Perm P.threads) : (P.reorder l h).Bounded n := hb

/-- Example 4.1 (threads `T3, T1, T2`): `⟦P⟧` has 2 members, 5 reachable configurations. -/
theorem ex41_counts : {G | Model.p2p.Sem ex41 G}.ncard = 2 ∧
    {c | ReachM Model.p2p (Sel.least.pick AP) ex41 c}.ncard = 5 := by
  have hb : ex41.Bounded 1 := reorder_bounded (ofCodes_bounded (by decide +kernel)) _ _
  have h := counts hb (fuel := 100) (by decide +kernel)
  rw [h.1, h.2]
  decide +kernel

/-- Example 3.1 (p2p sends): `⟦P⟧` has 2 members, 9 reachable configurations. -/
theorem ex31_bounded : ex31.Bounded 2 := ofCodes_bounded (by decide +kernel)

theorem ex31_counts : {G | Model.p2p.Sem ex31 G}.ncard = 2 ∧
    {c | ReachM Model.p2p (Sel.least.pick AP) ex31 c}.ncard = 9 := by
  have h := counts ex31_bounded (fuel := 100) (by decide +kernel)
  rw [h.1, h.2]
  decide +kernel

/-- Example 4.3: `⟦P⟧` has 4 members, 14 reachable configurations. -/
theorem ex43_bounded : ex43.Bounded 2 := ofCodes_bounded (by decide +kernel)

theorem ex43_counts : {G | Model.p2p.Sem ex43 G}.ncard = 4 ∧
    {c | ReachM Model.p2p (Sel.least.pick AP) ex43 c}.ncard = 14 := by
  have h := counts ex43_bounded (fuel := 100) (by decide +kernel)
  rw [h.1, h.2]
  decide +kernel

/-- The p. 19 program `pOp`: `⟦P⟧` has 4 members, 12 reachable configurations. -/
theorem pOp_bounded : pOp.Bounded 2 := ofCodes_bounded (by decide +kernel)

theorem pOp_counts : {G | Model.p2p.Sem pOp G}.ncard = 4 ∧
    {c | ReachM Model.p2p (Sel.least.pick AP) pOp c}.ncard = 12 := by
  have h := counts pOp_bounded (fuel := 100) (by decide +kernel)
  rw [h.1, h.2]
  decide +kernel

/-- The p. 19 program `pAs`: `⟦P⟧` has 2 members, 8 reachable configurations. -/
theorem pAs_bounded : pAs.Bounded 2 := ofCodes_bounded (by decide +kernel)

theorem pAs_counts : {G | Model.p2p.Sem pAs G}.ncard = 2 ∧
    {c | ReachM Model.p2p (Sel.least.pick AP) pAs c}.ncard = 8 := by
  have h := counts pAs_bounded (fuel := 100) (by decide +kernel)
  rw [h.1, h.2]
  decide +kernel

/-! ### Early exit -/

/-- `T0: send(T1,0)`; `T1: r = recv(); if r = 1 then error`; `T2: send(T1,1)`. -/
def pErr : Program VPred :=
  ofCodes [sa 1 0, .recv .asyn true .any [(1, .error)] .done .done, sa 1 1]

/-- The same program with the error only on the value 5 (never sent). -/
def pOk : Program VPred :=
  ofCodes [sa 1 0, .recv .asyn true .any [(5, .error)] .done .done, sa 1 1]

theorem pErr_bounded : pErr.Bounded 2 := ofCodes_bounded (by decide +kernel)
theorem pOk_bounded : pOk.Bounded 2 := ofCodes_bounded (by decide +kernel)

/-- `pErr` is erroneous: the explorer with early exit returns a configuration (soundness of
the early exit, any fuel). -/
theorem pErr_erroneous : Erroneous Model.p2p pErr := by
  cases h : (exploreX AP (rep .least) pErr 100).err with
  | none => exact absurd h (by decide +kernel)
  | some x => exact (exploreX_sound consAPB_iff_p2p .least pErr_bounded h).2.2

/-- `pOk` is not erroneous: with enough fuel (5 reachable configurations) the explorer with
early exit returns nothing, and `completeM_exit` turns this into a statement on `⟦P⟧`. -/
theorem pOk_not_erroneous : ¬ Erroneous Model.p2p pOk := by
  have hn := (counts pOk_bounded (fuel := 100) (by decide +kernel)).2
  have h := completeM_exit consAPB_iff_p2p .least pOk_bounded (fuel := 100)
    (by rw [hn]; decide +kernel)
  intro he
  have := h.2.1.mpr he
  revert this
  decide +kernel

end ExploreMEx

end Must

#print axioms Must.ExploreMEx.boundedB_branch
#print axioms Must.ExploreMEx.run_none_of_boundedB
#print axioms Must.ExploreMEx.ofCodes_bounded
#print axioms Must.ExploreMEx.counts
#print axioms Must.ExploreMEx.pFuel_counts
#print axioms Must.ExploreMEx.pFuel_spec
#print axioms Must.ExploreMEx.ex41_counts
#print axioms Must.ExploreMEx.ex31_counts
#print axioms Must.ExploreMEx.ex43_counts
#print axioms Must.ExploreMEx.pOp_counts
#print axioms Must.ExploreMEx.pAs_counts
#print axioms Must.ExploreMEx.pErr_erroneous
#print axioms Must.ExploreMEx.pOk_not_erroneous
