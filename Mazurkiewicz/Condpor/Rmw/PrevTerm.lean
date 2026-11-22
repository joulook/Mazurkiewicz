import Mazurkiewicz.Condpor.Rmw.Prev
import Mazurkiewicz.Condpor.Rf.PrevTerm

/-!
# Read-modify-write accesses: the backward steps reach the initial graph

Lemma A.25 and Proposition A.26 of the TruSt appendix for a model with
`ExtensibleX`. The statements about one backward step are those of
`PrevTerm.lean` (`PrevStep.noEarlierSucc'` of `Rf/PrevTerm.lean` for the
only one that used consistency). The inductions over the backward chain are
those of `PrevTerm.lean`, repeated with `PrevReach.invX` in place of
`PrevReach.inv` and `PrevReach.s1`.
-/

namespace Condpor

open Program

variable {P : XProgram} {M : Model} {S : Solver} {τ : TieBreak S}

/-- `NoEarlierSucc e` is kept along the backward steps from `G_f`. -/
theorem PrevReach.noEarlierSuccX {Gf G G2 : Graph} {e : TEv} (hM : ExtensibleX P M) (hGf : Gf.Wf)
    (hEf : P.toProgram.Exec Gf) (hcf : (M.sym S).cons Gf) (hff : P.toProgram.Full Gf)
    (h1 : PrevReach P.toProgram τ Gf G)
    (h2 : Relation.ReflTransGen (fun G G' => ∃ e k, PrevStep P.toProgram τ G e k G') G G2)
    (h : G.NoEarlierSucc e) : G2.NoEarlierSucc e := by
  induction h2 with
  | refl => exact h
  | tail hch hs ih =>
    obtain ⟨e', k, hs⟩ := hs
    have hr : PrevReach P.toProgram τ Gf _ := Relation.ReflTransGen.trans h1 hch
    obtain ⟨hW, hE, hc, hS2, hS1⟩ := PrevReach.invX hM hGf hEf hcf hff hr
    exact hs.noEarlierSucc' hW hE (hs.invX hM hW hE hc hS1 hS2).1
      ((M.sym S).porf_acyclic _ hW hc) hS1 ih

/-- The revisiting write of a backward revisit step is an event of `G_f`. -/
theorem PrevReach.rv_memX {Gf G G' : Graph} {a e : TEv} (hM : ExtensibleX P M) (hGf : Gf.Wf)
    (hEf : P.toProgram.Exec Gf) (hcf : (M.sym S).cons Gf) (hff : P.toProgram.Full Gf)
    (h : PrevReach P.toProgram τ Gf G)
    (hs : PrevStep P.toProgram τ G e (.rv a) G') : e ∈ Gf.events := by
  by_contra he
  exact hs.not_noEarlierSucc (PrevReach.invX hM hGf hEf hcf hff h).1
    (PrevReach.noEarlierSuccX hM hGf hEf hcf hff Relation.ReflTransGen.refl h (Or.inl he))

/-- Every write of `RW` is an event of `G_f` and satisfies `NoEarlierSucc`
in the current graph. -/
theorem PrevReachRW.invX {Gf : Graph} {x : Graph × Finset TEv} (hM : ExtensibleX P M)
    (hGf : Gf.Wf) (hEf : P.toProgram.Exec Gf) (hcf : (M.sym S).cons Gf) (hff : P.toProgram.Full Gf)
    (h : PrevReachRW P.toProgram τ Gf x) : ∀ e ∈ x.2, x.1.NoEarlierSucc e ∧ e ∈ Gf.events := by
  unfold PrevReachRW at h
  induction h with
  | refl => exact fun e he => absurd he (by simp)
  | @tail x y hch hs ih =>
    obtain ⟨e', k, hs, hrw⟩ := hs
    have hr : PrevReach P.toProgram τ Gf x.1 := PrevReachRW.reach hch
    obtain ⟨hW, hE, hc, hS2, hS1⟩ := PrevReach.invX hM hGf hEf hcf hff hr
    have keep : ∀ e, x.1.NoEarlierSucc e → y.1.NoEarlierSucc e := fun e he =>
      hs.noEarlierSucc' hW hE (hs.invX hM hW hE hc hS1 hS2).1
        ((M.sym S).porf_acyclic _ hW hc) hS1 he
    intro e he
    rw [hrw] at he
    cases k with
    | nr => exact ⟨keep e (ih e he).1, (ih e he).2⟩
    | rv a =>
      rcases Finset.mem_insert.mp he with rfl | he
      · obtain ⟨hWY, -, -, -⟩ := hs.invX hM hW hE hc hS1 hS2
        refine ⟨Or.inl ?_, PrevReach.rv_memX hM hGf hEf hcf hff hr hs⟩
        exact not_mem_of_mem_avail hWY hs.rv_inv.2.2.2.2.2.2.1
      · exact ⟨keep e (ih e he).1, (ih e he).2⟩

/-- The set `RW` consists of events of `G_f`. -/
theorem PrevReachRW.subsetX {Gf G : Graph} {rw : Finset TEv} (hM : ExtensibleX P M) (hGf : Gf.Wf)
    (hEf : P.toProgram.Exec Gf) (hcf : (M.sym S).cons Gf) (hff : P.toProgram.Full Gf)
    (h : PrevReachRW P.toProgram τ Gf (G, rw)) :
    rw ⊆ Gf.events :=
  fun e he => (PrevReachRW.invX hM hGf hEf hcf hff h e he).2

/-- Lemma A.25: the revisiting write of a backward revisit step is not in the
set `RW` collected so far. -/
theorem PrevReachRW.a25X {Gf G G' : Graph} {rw : Finset TEv} {a e : TEv} (hM : ExtensibleX P M)
    (hGf : Gf.Wf) (hEf : P.toProgram.Exec Gf) (hcf : (M.sym S).cons Gf) (hff : P.toProgram.Full Gf)
    (h : PrevReachRW P.toProgram τ Gf (G, rw)) (hs : PrevStep P.toProgram τ G e
    (.rv a) G') : e ∉ rw := by
  intro he
  exact hs.not_noEarlierSucc (PrevReach.invX hM hGf hEf hcf hff (PrevReachRW.reach h)).1
    (PrevReachRW.invX hM hGf hEf hcf hff h e he).1

/-- Proposition A.26: from a well-formed, consistent, full execution of a
bounded program, the backward steps reach the graph without thread events. -/
theorem PrevReach.initX {n : ℕ} (hn : P.toProgram.Bounded n) (hM : ExtensibleX P M) {Gf : Graph}
    (hGf : Gf.Wf) (hEf : P.toProgram.Exec Gf) (hcf : (M.sym S).cons Gf)
    (hff : P.toProgram.Full Gf) :
    PrevReach P.toProgram τ Gf (Graph.init P.mem) := by
  let K := n * P.threads.length
  let f : Graph × Finset TEv → ℕ := fun x => x.2.card * (K + 1) + (K - x.1.events.card)
  have hK : ∀ x, PrevReachRW P.toProgram τ Gf x → x.1.events.card ≤ K := fun x hx =>
    let ⟨hW, hE, _, _, _⟩ := PrevReach.invX hM hGf hEf hcf hff (PrevReachRW.reach hx)
    hE.card_le hW hn
  have hRW : ∀ x, PrevReachRW P.toProgram τ Gf x → x.2.card ≤ K := fun x hx =>
    (Finset.card_le_card (fun e he => (PrevReachRW.invX hM hGf hEf hcf hff hx e he).2)).trans
      (hEf.card_le hGf hn)
  have hinc : ∀ x y, Relation.ReflTransGen (PrevStepRW P.toProgram τ)
    (Gf, ∅) x → PrevStepRW P.toProgram τ x y →
      f x < f y := by
    intro x y hx hxy
    have hy : PrevReachRW P.toProgram τ Gf y := Relation.ReflTransGen.tail hx hxy
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
      have h25 : e ∉ rwX := PrevReachRW.a25X hM hGf hEf hcf hff hx hs
      rw [hrw]
      simp only [Kind.rw]
      rw [Finset.card_insert_of_notMem h25, Nat.add_mul, Nat.one_mul]
      omega
  have hbd : ∀ x, Relation.ReflTransGen (PrevStepRW P.toProgram τ) (Gf, ∅) x → f x ≤ K *
    (K + 1) + K := by
    intro x hx
    have h1 := hRW x hx
    have h2 : x.2.card * (K + 1) ≤ K * (K + 1) := Nat.mul_le_mul_right _ h1
    simp only [f]
    omega
  obtain ⟨x, hx, hsink⟩ := Maz.exists_sink_of_bounded_measure f (K * (K + 1) + K) hinc hbd
  obtain ⟨hW, hE, hc, -, -⟩ := PrevReach.invX hM hGf hEf hcf hff (PrevReachRW.reach hx)
  have hemp : x.1.events = ∅ := by
    by_contra hne
    obtain ⟨e, k, G', hs⟩ :=
      exists_prevStep hn hW hE hc (Finset.nonempty_iff_ne_empty.mpr hne)
    exact hsink (G', k.rw e x.2) ⟨e, k, hs, rfl⟩
  have hinit : x.1 = Graph.init P.mem := by
    rw [← hE.1]
    exact hW.eq_init_of_events_eq_empty hemp
  rw [← hinit]
  exact PrevReachRW.reach hx

/-- The graphs of the backward chain have at most `n * |threads|` events. -/
theorem PrevReach.card_leX {n : ℕ} (hn : P.toProgram.Bounded n)
    (hM : ExtensibleX P M) {Gf G : Graph}
    (hGf : Gf.Wf) (hEf : P.toProgram.Exec Gf) (hcf : (M.sym S).cons Gf)
    (hff : P.toProgram.Full Gf) (h : PrevReach P.toProgram τ Gf G) :
    G.events.card ≤ n * P.threads.length := by
  obtain ⟨hW, hE, -⟩ := PrevReach.invX hM hGf hEf hcf hff h
  exact hE.card_le hW hn


end Condpor
