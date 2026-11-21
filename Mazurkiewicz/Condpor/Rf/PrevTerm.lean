import Mazurkiewicz.Condpor.Rf.Optimal

/-!
# The reads-from version: the backward steps reach the initial graph

Lemma A.25 and Proposition A.26 of the TruSt appendix for the backward steps
of `Rf/Prev.lean`. The statements about one backward step are those of
`PrevTerm.lean`, applied through `PrevStepR.lift`; the inductions over the
backward chain are repeated.
-/

namespace Condpor

open Program

variable {P : Program} {M : Model} {S : Solver} {τ : TieBreak S}

/-- `PrevStep.noEarlierSucc` of `PrevTerm.lean`, with the same proof, from
the two consequences of consistency that the proof uses: the result is
well-formed, and `porf` has no cycle. -/
theorem PrevStep.noEarlierSucc' {X Y : Graph} {e' e : TEv} {k : Kind}
    (hX : X.Wf) (hE : P.Exec X) (hWY : Y.Wf) (hac : Maz.Acyclic X.porfStep)
    (hs1 : ∀ y ∈ P.avail X, ∀ m, X.IsMe m → ¬ nextLtEv (.th y) m)
    (hs : PrevStep P τ X e' k Y) (h : X.NoEarlierSucc e) : Y.NoEarlierSucc e := by
  by_cases heY : e ∈ Y.events
  swap
  · exact Or.inl heY
  right
  intro c hpc hlt
  have hcY : c ∈ Y.events := (hWY.mem_of_porf hpc).2
  cases k with
  | nr =>
    obtain ⟨hme, rfl, -⟩ := hs.nr_inv
    have heX : e ∈ X.events := (Finset.mem_inter.mp heY).1
    exact h.resolve_left (not_not.mpr heX) c
      ((Graph.porf_restrict_iff (nr_closed hX hme) hcY).mp hpc) hlt
  | rv a =>
    obtain ⟨hme, hr, hrf, hlt', hpo, hmc⟩ := hs.rv_inv
    obtain ⟨hp, hav⟩ := rv_remove hX hE hme hrf hpo
    have hW0 := hX.of_isPrefixOf hp
    have hE0 := hE.of_isPrefixOf hX hp
    obtain ⟨-, -, c2, c3, c4⟩ := ComplStep.order hW0 hE0 hav hmc.1
    by_cases he0 : e ∈ (X.remove {a, e'}).events
    · have he0' : e ∈ X.events ∩ (X.events \ {a, e'}) := he0
      have heX : e ∈ X.events := (Finset.mem_inter.mp he0').1
      have hea : e ≠ a := fun h =>
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp he0').2).2 (by simp [h])
      by_cases hc0 : c ∈ (X.remove {a, e'}).events
      · have h0 : (X.remove {a, e'}).porf (.th e) (.th c) := c4 _ _ hpc hc0
        exact h.resolve_left (not_not.mpr heX) c
          ((Graph.porf_restrict_iff (rv_closed hX hme hpo) hc0).mp h0) hlt
      · obtain ⟨y, hy, hyc⟩ := c2 c hcY hc0
        have hya : ¬ nextLt y a := by
          rcases rv_avail hX hE hme hrf hpo y hy with rfl | rfl | hyX
          · exact nextLt_irrefl _
          · exact fun h => nextLt_irrefl _ (nextLt_trans h hlt')
          · exact hs1 y hyX _ hme
        have hea' : nextLt e a := (nextLt_total hea).resolve_right
          (h.me_ge hX hac heX hme)
        have hca : nextLt c a := nextLt_trans hlt hea'
        rcases hyc with rfl | hyc
        · exact hya hca
        · exact hya (nextLt_trans hyc hca)
    · exact nextLt_irrefl _ (nextLt_trans (c3 e c he0 hpc) hlt)

variable {γ : CoChoice (M.sym S)}

/-- A backward step on pairs with the set `RW`. -/
def PrevStepRWR (P : Program) {M : Model} {S : Solver} (γ : CoChoice (M.sym S)) (τ : TieBreak S)
    (x y : Graph × Finset TEv) : Prop :=
  ∃ e k, PrevStepR P γ τ x.1 e k y.1 ∧ y.2 = k.rw e x.2

/-- The pairs obtained from `⟨G_f, ∅⟩` by backward steps. -/
def PrevReachRWR (P : Program) {M : Model} {S : Solver} (γ : CoChoice (M.sym S))
    (τ : TieBreak S) (Gf : Graph) (x : Graph × Finset TEv) : Prop :=
  Relation.ReflTransGen (PrevStepRWR P γ τ) (Gf, ∅) x

theorem PrevReachRWR.reach {Gf : Graph} {x : Graph × Finset TEv}
    (h : PrevReachRWR P γ τ Gf x) : PrevReachR P γ τ Gf x.1 := by
  unfold PrevReachRWR at h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    obtain ⟨e, k, hs, -⟩ := hs
    exact ih.tail ⟨e, k, hs⟩

theorem PrevStepR.noEarlierSucc {X Y : Graph} {e' e : TEv} {k : Kind}
    (hX : X.Wf) (hE : P.Exec X) (hcan : X.IsCanon) (hac : Maz.Acyclic X.porfStep)
    (hs1 : ∀ y ∈ P.avail X, ∀ m, X.IsMe m → ¬ nextLtEv (.th y) m)
    (hs : PrevStepR P γ τ X e' k Y) (h : X.NoEarlierSucc e) : Y.NoEarlierSucc e := by
  obtain ⟨co, Y', hW, hWY, rfl, hs'⟩ := hs.lift hX hE hcan
  have h' := hs'.noEarlierSucc' hW hE hWY hac hs1 h
  exact h'

theorem PrevStepR.not_noEarlierSucc {G G' : Graph} {a e : TEv} (hG : G.Wf)
    (hs : PrevStepR P γ τ G e (.rv a) G') : ¬ G.NoEarlierSucc e := by
  obtain ⟨-, -, hrf, hlt, hpo, -⟩ := hs.rv_inv
  rintro (h | h)
  · exact h (hG.rf_source_mem hrf).2
  · exact h a ((hpo _).mpr rfl) hlt

section Chain

variable {Gf : Graph} (hM : M.Extensible) (hGf : Gf.Wf) (hEf : P.Exec Gf) (hcan : Gf.IsCanon)
  (hcf : (M.sym S).rf.cons Gf) (hff : P.Full Gf)

include hM hGf hEf hcan hcf hff

/-- `NoEarlierSucc e` is kept along the backward steps from `G_f`. -/
theorem PrevReachR.noEarlierSucc {G G2 : Graph} {e : TEv} (h1 : PrevReachR P γ τ Gf G)
    (h2 : Relation.ReflTransGen (fun G G' => ∃ e k, PrevStepR P γ τ G e k G') G G2)
    (h : G.NoEarlierSucc e) : G2.NoEarlierSucc e := by
  induction h2 with
  | refl => exact h
  | tail hch hs ih =>
    obtain ⟨e', k, hs⟩ := hs
    have hr : PrevReachR P γ τ Gf _ := Relation.ReflTransGen.trans h1 hch
    obtain ⟨hW, hE, hcn, hc⟩ := PrevReachR.inv hM hGf hEf hcan hcf hr
    exact hs.noEarlierSucc hW hE hcn ((M.sym S).rf.porf_acyclic _ hW hc)
      (fun y hy m hm => PrevReachR.s1 hM hGf hEf hcan hcf hff hr hy hm) ih

/-- The revisiting write of a backward revisit step is an event of `G_f`. -/
theorem PrevReachR.rv_mem {G G' : Graph} {a e : TEv} (h : PrevReachR P γ τ Gf G)
    (hs : PrevStepR P γ τ G e (.rv a) G') : e ∈ Gf.events := by
  by_contra he
  exact hs.not_noEarlierSucc (PrevReachR.inv hM hGf hEf hcan hcf h).1
    (PrevReachR.noEarlierSucc hM hGf hEf hcan hcf hff Relation.ReflTransGen.refl h (Or.inl he))

/-- Every write of `RW` is an event of `G_f` and satisfies `NoEarlierSucc`
in the current graph. -/
theorem PrevReachRWR.inv {x : Graph × Finset TEv} (h : PrevReachRWR P γ τ Gf x) :
    ∀ e ∈ x.2, x.1.NoEarlierSucc e ∧ e ∈ Gf.events := by
  unfold PrevReachRWR at h
  induction h with
  | refl => exact fun e he => absurd he (by simp)
  | @tail x y hch hs ih =>
    obtain ⟨e', k, hs, hrw⟩ := hs
    have hr : PrevReachR P γ τ Gf x.1 := PrevReachRWR.reach hch
    obtain ⟨hW, hE, hcn, hc⟩ := PrevReachR.inv hM hGf hEf hcan hcf hr
    have keep : ∀ e, x.1.NoEarlierSucc e → y.1.NoEarlierSucc e := fun e he =>
      hs.noEarlierSucc hW hE hcn ((M.sym S).rf.porf_acyclic _ hW hc)
        (fun y hy m hm => PrevReachR.s1 hM hGf hEf hcan hcf hff hr hy hm) he
    intro e he
    rw [hrw] at he
    cases k with
    | nr => exact ⟨keep e (ih e he).1, (ih e he).2⟩
    | rv a =>
      rcases Finset.mem_insert.mp he with rfl | he
      · obtain ⟨hWY, -, -, -⟩ := hs.inv hM hW hE hcn hc
        refine ⟨Or.inl ?_, PrevReachR.rv_mem hM hGf hEf hcan hcf hff hr hs⟩
        exact not_mem_of_mem_avail hWY
          (PrevReachR.next_of_prevStep hM hGf hEf hcan hcf hff hr hs).1
      · exact ⟨keep e (ih e he).1, (ih e he).2⟩

/-- Lemma A.25: the revisiting write of a backward revisit step is not in the
set `RW` collected so far. -/
theorem PrevReachRWR.a25 {G G' : Graph} {rw : Finset TEv} {a e : TEv}
    (h : PrevReachRWR P γ τ Gf (G, rw)) (hs : PrevStepR P γ τ G e (.rv a) G') : e ∉ rw := by
  intro he
  exact hs.not_noEarlierSucc (PrevReachR.inv hM hGf hEf hcan hcf (PrevReachRWR.reach h)).1
    (PrevReachRWR.inv hM hGf hEf hcan hcf hff h e he).1

/-- Proposition A.26: from a well-formed full execution of a bounded program
that is consistent for some coherence order, the backward steps reach the
graph without thread events. -/
theorem PrevReachR.init {n : ℕ} (hn : P.Bounded n) :
    PrevReachR P γ τ Gf (Graph.init P.mem) := by
  let K := n * P.threads.length
  let f : Graph × Finset TEv → ℕ := fun x => x.2.card * (K + 1) + (K - x.1.events.card)
  have hK : ∀ x, PrevReachRWR P γ τ Gf x → x.1.events.card ≤ K := fun x hx =>
    let ⟨hW, hE, _, _⟩ := PrevReachR.inv hM hGf hEf hcan hcf (PrevReachRWR.reach hx)
    hE.card_le hW hn
  have hRW : ∀ x, PrevReachRWR P γ τ Gf x → x.2.card ≤ K := fun x hx =>
    (Finset.card_le_card
      (fun e he => (PrevReachRWR.inv hM hGf hEf hcan hcf hff hx e he).2)).trans
      (hEf.card_le hGf hn)
  have hinc : ∀ x y, Relation.ReflTransGen (PrevStepRWR P γ τ) (Gf, ∅) x →
      PrevStepRWR P γ τ x y → f x < f y := by
    intro x y hx hxy
    have hy : PrevReachRWR P γ τ Gf y := Relation.ReflTransGen.tail hx hxy
    have h1 := hK x hx
    have h2 := hK y hy
    obtain ⟨X, rwX⟩ := x
    obtain ⟨Y, rwY⟩ := y
    obtain ⟨e, k, hs, hrw⟩ := hxy
    simp only at hs hrw h1 h2
    simp only [f]
    cases k with
    | nr =>
      obtain ⟨hme, rfl, -⟩ := hs.nr_inv
      have he : e ∈ X.events := hme.1
      have hcard := Finset.card_erase_of_mem he
      have hpos : 0 < X.events.card := Finset.card_pos.mpr ⟨e, he⟩
      rw [hrw, Graph.remove_singleton_events]
      simp only [Kind.rw]
      omega
    | rv a =>
      have h25 : e ∉ rwX := PrevReachRWR.a25 hM hGf hEf hcan hcf hff hx hs
      rw [hrw]
      simp only [Kind.rw]
      rw [Finset.card_insert_of_notMem h25, Nat.add_mul, Nat.one_mul]
      omega
  have hbd : ∀ x, Relation.ReflTransGen (PrevStepRWR P γ τ) (Gf, ∅) x →
      f x ≤ K * (K + 1) + K := by
    intro x hx
    have h1 := hRW x hx
    have h2 : x.2.card * (K + 1) ≤ K * (K + 1) := Nat.mul_le_mul_right _ h1
    simp only [f]
    omega
  obtain ⟨x, hx, hsink⟩ := Maz.exists_sink_of_bounded_measure f (K * (K + 1) + K) hinc hbd
  obtain ⟨hW, hE, -, hc⟩ := PrevReachR.inv hM hGf hEf hcan hcf (PrevReachRWR.reach hx)
  have hemp : x.1.events = ∅ := by
    by_contra hne
    obtain ⟨e, k, G', hs⟩ :=
      exists_prevStepR (γ := γ) (τ := τ) hn hW hE ((M.sym S).rf.porf_acyclic _ hW hc)
        (Finset.nonempty_iff_ne_empty.mpr hne)
    exact hsink (G', k.rw e x.2) ⟨e, k, hs, rfl⟩
  have hinit : x.1 = Graph.init P.mem := by
    rw [← hE.1]
    exact hW.eq_init_of_events_eq_empty hemp
  rw [← hinit]
  exact PrevReachRWR.reach hx

end Chain

end Condpor
