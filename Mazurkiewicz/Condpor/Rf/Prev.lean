import Mazurkiewicz.Condpor.Rf.Inv

/-!
# The backward step of the reads-from version

`Prev` of `Prev.lean` on graphs with a canonical coherence order. Undoing a
revisit of `a` by `e`: the graph without `a` and `e` gets the coherence order
that `γ` chooses for it, the deleted events are added back by `MaxCompl` (the
relation of `Prev.lean`), and the result is put in canonical form.

A backward step of this file is a backward step of `Prev.lean` from the same
graph with another coherence order (`PrevStepR.lift`), so the accepted
statements about one backward step apply.
-/

namespace Condpor

open Program

variable {P : Program} {M : Model} {S : Solver} {τ : TieBreak S} {γ : CoChoice (M.sym S)}

/-- `Prev(G) = ⟨G', e, k⟩` for the reads-from version. -/
inductive PrevStepR (P : Program) {M : Model} {S : Solver} (γ : CoChoice (M.sym S))
    (τ : TieBreak S) : Graph → TEv → Kind → Graph → Prop
  /-- the last step was a revisit of `a` by `e` -/
  | rv {G H : Graph} {a e : TEv} :
      G.IsMe (.th a) → a.IsRead → G.rf a = some (.th e) → nextLt a e →
      (∀ b, G.porf (.th e) b ↔ b = .th a) →
      MaxCompl P (τ.pref (G.remove {a, e}).F) (γ.apply (G.remove {a, e})) e H →
      PrevStepR P γ τ G e (.rv a) H.canon
  /-- the last step added `a = me(G)` -/
  | nr {G : Graph} {a : TEv} :
      G.IsMe (.th a) →
      (¬ ∃ e, a.IsRead ∧ G.rf a = some (.th e) ∧ nextLt a e ∧
        ∀ b, G.porf (.th e) b ↔ b = .th a) →
      PrevStepR P γ τ G a .nr (G.remove {a})

/-- The graphs obtained from `G_f` by backward steps. -/
def PrevReachR (P : Program) {M : Model} {S : Solver} (γ : CoChoice (M.sym S))
    (τ : TieBreak S) (Gf G : Graph) : Prop :=
  Relation.ReflTransGen (fun G G' => ∃ e k, PrevStepR P γ τ G e k G') Gf G

theorem PrevStepR.rv_inv {G G' : Graph} {a e : TEv} (h : PrevStepR P γ τ G e (.rv a) G') :
    G.IsMe (.th a) ∧ a.IsRead ∧ G.rf a = some (.th e) ∧ nextLt a e ∧
      (∀ b, G.porf (.th e) b ↔ b = .th a) ∧
      ∃ H, MaxCompl P (τ.pref (G.remove {a, e}).F) (γ.apply (G.remove {a, e})) e H ∧
        G' = H.canon := by
  cases h with
  | rv h1 h2 h3 h4 h5 h6 => exact ⟨h1, h2, h3, h4, h5, _, h6, rfl⟩

theorem PrevStepR.nr_inv {G G' : Graph} {e : TEv} (h : PrevStepR P γ τ G e .nr G') :
    G.IsMe (.th e) ∧ G' = G.remove {e} ∧
      ¬ ∃ w, e.IsRead ∧ G.rf e = some (.th w) ∧ nextLt e w ∧
        ∀ b, G.porf (.th w) b ↔ b = .th e := by
  cases h with
  | nr h1 h2 => exact ⟨h1, rfl, h2⟩

/-- `Prev` is a function. -/
theorem PrevStepR.det {G G1 G2 : Graph} {e1 e2 : TEv} {k1 k2 : Kind}
    (h1 : PrevStepR P γ τ G e1 k1 G1) (h2 : PrevStepR P γ τ G e2 k2 G2) :
    e1 = e2 ∧ k1 = k2 ∧ G1 = G2 := by
  cases k1 with
  | rv a =>
    obtain ⟨hme, hr, hrf, hlt, hpo, H, hmc, rfl⟩ := h1.rv_inv
    cases k2 with
    | rv a' =>
      obtain ⟨hme', -, hrf', -, -, H', hmc', rfl⟩ := h2.rv_inv
      have ha : a = a' := Ev.th.inj (hme.unique hme')
      subst ha
      have he : e1 = e2 := by
        rw [hrf] at hrf'
        exact Ev.th.inj (Option.some.inj hrf')
      subst he
      exact ⟨rfl, rfl, by rw [hmc.det hmc']⟩
    | nr =>
      obtain ⟨hme', -, hneg⟩ := h2.nr_inv
      have ha : a = e2 := Ev.th.inj (hme.unique hme')
      subst ha
      exact absurd ⟨e1, hr, hrf, hlt, hpo⟩ hneg
  | nr =>
    obtain ⟨hme, hG1, hneg⟩ := h1.nr_inv
    cases k2 with
    | rv a' =>
      obtain ⟨hme', hr', hrf', hlt', hpo', -⟩ := h2.rv_inv
      have ha : e1 = a' := Ev.th.inj (hme.unique hme')
      subst ha
      exact absurd ⟨e2, hr', hrf', hlt', hpo'⟩ hneg
    | nr =>
      obtain ⟨hme', hG2, -⟩ := h2.nr_inv
      have ha : e1 = e2 := Ev.th.inj (hme.unique hme')
      subst ha
      exact ⟨rfl, rfl, hG1.trans hG2.symm⟩

/-- The graph without `a` and `e`, with the chosen coherence order, is
well-formed and has `e` available. -/
theorem rv_removeR {G : Graph} {a e : TEv} (hG : G.Wf) (hE : P.Exec G) (hme : G.IsMe (.th a))
    (hrf : G.rf a = some (.th e)) (hpo : ∀ b, G.porf (.th e) b ↔ b = .th a) :
    (G.remove {a, e}).Wf ∧ (γ.apply (G.remove {a, e})).Wf ∧ P.Exec (γ.apply (G.remove {a, e})) ∧
      e ∈ P.avail (γ.apply (G.remove {a, e})) := by
  obtain ⟨hp, hav⟩ := rv_remove hG hE hme hrf hpo
  have hW0 := hG.of_isPrefixOf hp
  exact ⟨hW0, γ.wf _ hW0, (Program.exec_withCo P _ _).mpr (hE.of_isPrefixOf hG hp), hav⟩

/-- `Prev(G)` is defined for a well-formed execution `G` with a thread event
and an acyclic `porf`, for a bounded program. -/
theorem exists_prevStepR {n : ℕ} (hn : P.Bounded n) {G : Graph} (hG : G.Wf) (hE : P.Exec G)
    (hac : Maz.Acyclic G.porfStep) (hne : G.events.Nonempty) :
    ∃ e k G', PrevStepR P γ τ G e k G' := by
  obtain ⟨m, hm⟩ := Graph.exists_isMe hG hac
  obtain ⟨b, hb⟩ := hne
  cases m with
  | init =>
    have hib : G.porf .init (.th b) := Relation.TransGen.single (Or.inl hb)
    exact absurd hib (hm.2.1 (.th b))
  | th a =>
    by_cases hcnd : ∃ e, a.IsRead ∧ G.rf a = some (.th e) ∧ nextLt a e ∧
        ∀ b, G.porf (.th e) b ↔ b = .th a
    · obtain ⟨e, hr, hrf, hlt, hpo⟩ := hcnd
      obtain ⟨-, hW, hE0, hav⟩ := rv_removeR (γ := γ) hG hE hm hrf hpo
      obtain ⟨G', hG'⟩ := MaxCompl.exists hn hW hE0 hav
      exact ⟨e, .rv a, _, .rv hm hr hrf hlt hpo hG'⟩
    · exact ⟨a, .nr, _, .nr hm hcnd⟩

theorem not_prevStepR_init (μ : Loc → Val) (e : TEv) (k : Kind) (G' : Graph) :
    ¬ PrevStepR P γ τ (Graph.init μ) e k G' := by
  intro h
  cases h with
  | rv hme => exact absurd hme.1 (by simp [Graph.evSet, Graph.init])
  | nr hme => exact absurd hme.1 (by simp [Graph.evSet, Graph.init])

/-! ### A backward step is a backward step of `Prev.lean` for another coherence order -/

/-- The coherence order with which the backward step of `Prev.lean` undoes the
revisit of `a` by `e` in the same way: the chosen order of the graph without
`a` and `e`, then `e`. -/
def Graph.liftCo (γ : CoChoice (M.sym S)) (G : Graph) (a e : TEv) (x : Loc) : List TEv :=
  γ.co (G.remove {a, e}) x ++ (if e.writesTo x = true then [e] else [])

theorem Graph.liftCo_wf {G : Graph} {a e : TEv} (hG : G.Wf) (hE : P.Exec G)
    (hme : G.IsMe (.th a)) (hr : a.IsRead) (hrf : G.rf a = some (.th e))
    (hpo : ∀ b, G.porf (.th e) b ↔ b = .th a) : (G.withCo (G.liftCo γ a e)).Wf := by
  obtain ⟨hW0, hWγ, -, -⟩ := rv_removeR (γ := γ) hG hE hme hrf hpo
  have heE : e ∈ G.events := (hG.rf_source_mem hrf).2
  have hmemK : ∀ q, q ∈ (G.remove {a, e}).events ↔ q ∈ G.events ∧ q ≠ a ∧ q ≠ e := by
    intro q
    simp only [Graph.remove, Graph.restrict_events, Finset.mem_inter, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    tauto
  refine hG.withCo (fun x q => ?_) (fun x => ?_)
  · have h1 : q ∈ γ.co (G.remove {a, e}) x ↔
        q ∈ (G.remove {a, e}).events ∧ ∃ v, q.act = .write x v := hWγ.co_mem x q
    unfold Graph.liftCo
    rw [List.mem_append, h1, hmemK]
    constructor
    · rintro (⟨⟨hq, -, -⟩, hw⟩ | hq)
      · exact ⟨hq, hw⟩
      · split_ifs at hq with hwx
        · rw [List.mem_singleton.mp hq]
          exact ⟨heE, TEv.writesTo_iff.mp hwx⟩
        · cases hq
    · rintro ⟨hq, hw⟩
      by_cases hqe : q = e
      · right
        subst hqe
        simp [TEv.writesTo_iff.mpr hw]
      · left
        refine ⟨⟨hq, ?_, hqe⟩, hw⟩
        rintro rfl
        obtain ⟨v, hv⟩ := hw
        simp [TEv.IsRead, hv, Act.IsRead] at hr
  · unfold Graph.liftCo
    refine List.Nodup.append (hWγ.co_nodup x) (by split_ifs <;> simp) ?_
    intro q hq1 hq2
    split_ifs at hq2
    · rw [List.mem_singleton.mp hq2] at hq1
      exact ((hmemK e).mp ((hWγ.co_mem x e).mp hq1).1).2.2 rfl
    · cases hq2

theorem Graph.liftCo_remove {G : Graph} {a e : TEv} (hG : G.Wf) (hE : P.Exec G)
    (hme : G.IsMe (.th a)) (hrf : G.rf a = some (.th e))
    (hpo : ∀ b, G.porf (.th e) b ↔ b = .th a) :
    (G.withCo (G.liftCo γ a e)).remove {a, e} = γ.apply (G.remove {a, e}) := by
  obtain ⟨hW0, hWγ, -, -⟩ := rv_removeR (γ := γ) hG hE hme hrf hpo
  change ((G.withCo (G.liftCo γ a e)).restrict (G.events \ {a, e})) = _
  rw [Graph.withCo_restrict]
  change _ = (G.remove {a, e}).withCo (γ.co (G.remove {a, e}))
  unfold Graph.remove
  congr 1
  funext x
  unfold Graph.liftCo
  rw [List.filter_append]
  have h1 : (γ.co (G.remove {a, e}) x).filter (fun q => q ∈ G.events \ {a, e}) =
      γ.co (G.remove {a, e}) x := by
    rw [List.filter_eq_self]
    intro q hq
    have hq' : q ∈ (G.remove {a, e}).events := ((hWγ.co_mem x q).mp hq).1
    have : q ∈ G.events \ {a, e} := (Finset.mem_inter.mp hq').2
    simpa using this
  have h2 : (if e.writesTo x = true then [e] else []).filter (fun q => q ∈ G.events \ {a, e})
      = [] := by
    split_ifs <;> simp
  rw [h2, List.append_nil]
  exact h1

/-- A backward step from a canonical graph is a backward step of `Prev.lean`
from the same graph with another coherence order; its result is the canonical
form of the result of the latter. -/
theorem PrevStepR.lift {X Y : Graph} {e : TEv} {k : Kind} (hX : X.Wf) (hE : P.Exec X)
    (hcan : X.IsCanon) (hs : PrevStepR P γ τ X e k Y) :
    ∃ co Y', (X.withCo co).Wf ∧ Y'.Wf ∧ Y = Y'.canon ∧ PrevStep P τ (X.withCo co) e k Y' := by
  cases k with
  | rv a =>
    obtain ⟨hme, hr, hrf, hlt, hpo, H, hmc, rfl⟩ := hs.rv_inv
    obtain ⟨-, hWγ, hE0, hav⟩ := rv_removeR (γ := γ) hX hE hme hrf hpo
    refine ⟨X.liftCo γ a e, H, Graph.liftCo_wf hX hE hme hr hrf hpo,
      (hmc.facts hWγ hE0 hav).1, rfl, ?_⟩
    refine PrevStep.rv hme hr hrf hlt hpo ?_
    rw [Graph.liftCo_remove hX hE hme hrf hpo]
    exact hmc
  | nr =>
    obtain ⟨hme, rfl, hneg⟩ := hs.nr_inv
    obtain ⟨hp, -, -⟩ := nr_remove (P := P) hX hE hme
    refine ⟨X.co, X.remove {e}, hX, hX.of_isPrefixOf hp, ?_, PrevStep.nr hme hneg⟩
    exact ((hcan.restrict _).canon_eq).symm

/-! ### Invariants of the backward steps -/

theorem PrevStepR.inv {G G' : Graph} {e : TEv} {k : Kind} (hM : M.Extensible) (hG : G.Wf)
    (hE : P.Exec G) (hcan : G.IsCanon) (hc : (M.sym S).rf.cons G)
    (h : PrevStepR P γ τ G e k G') :
    G'.Wf ∧ P.Exec G' ∧ G'.IsCanon ∧ (M.sym S).rf.cons G' := by
  cases k with
  | rv a =>
    obtain ⟨hme, hr, hrf, hlt, hpo, H, hmc, rfl⟩ := h.rv_inv
    obtain ⟨hp, -⟩ := rv_remove hG hE hme hrf hpo
    obtain ⟨hW0, hWγ, hE0, hav⟩ := rv_removeR (γ := γ) hG hE hme hrf hpo
    have hc0 : (M.sym S).rf.cons (G.remove {a, e}) := (M.sym S).rf.prefix_closed _ _ hG hc hp
    have hcγ : (M.sym S).cons (γ.apply (G.remove {a, e})) := γ.cons _ hW0 hc0
    obtain ⟨hW', hE', -⟩ := hmc.facts hWγ hE0 hav
    have hcH := hmc.cons_sym hM hWγ hE0 hav hcγ
    exact ⟨hW'.canon, hE', Graph.canon_isCanon _,
      (Model.rf_cons_congr (Graph.rfEq_canon _)).mp (Model.rf_cons_of_cons hW' hcH)⟩
  | nr =>
    obtain ⟨hme, rfl, -⟩ := h.nr_inv
    obtain ⟨hp, -, -⟩ := nr_remove (P := P) hG hE hme
    exact ⟨hG.of_isPrefixOf hp, hE.of_isPrefixOf hG hp, hcan.restrict _,
      (M.sym S).rf.prefix_closed _ _ hG hc hp⟩

theorem PrevReachR.inv {Gf G : Graph} (hM : M.Extensible) (hGf : Gf.Wf) (hEf : P.Exec Gf)
    (hcan : Gf.IsCanon) (hcf : (M.sym S).rf.cons Gf) (h : PrevReachR P γ τ Gf G) :
    G.Wf ∧ P.Exec G ∧ G.IsCanon ∧ (M.sym S).rf.cons G := by
  induction h with
  | refl => exact ⟨hGf, hEf, hcan, hcf⟩
  | tail _ hs ih =>
    obtain ⟨e, k, hs⟩ := hs
    obtain ⟨h1, h2, h3, h4⟩ := ih
    exact hs.inv hM h1 h2 h3 h4

/-- One backward step: the removed event is the next event of the graph it
returns, and (S1) is kept. -/
theorem PrevStepR.s1_step {X Y : Graph} {e : TEv} {k : Kind} (hX : X.Wf) (hE : P.Exec X)
    (hcan : X.IsCanon)
    (ih : ∀ y ∈ P.avail X, ∀ m, X.IsMe m → ¬ nextLtEv (.th y) m)
    (hs : PrevStepR P γ τ X e k Y) :
    P.IsNext Y e ∧ ∀ y ∈ P.avail Y, ∀ m, Y.IsMe m → ¬ nextLtEv (.th y) m := by
  obtain ⟨co, Y', hW, -, rfl, hs'⟩ := hs.lift hX hE hcan
  have h := hs'.s1_step hW hE ih
  exact h

/-- Proposition A.23 (S1): `[avail(G)]; <next; [me(G)] = ∅`. -/
theorem PrevReachR.s1 {Gf G : Graph} (hM : M.Extensible) (hGf : Gf.Wf) (hEf : P.Exec Gf)
    (hcan : Gf.IsCanon) (hcf : (M.sym S).rf.cons Gf) (hff : P.Full Gf)
    (h : PrevReachR P γ τ Gf G) {a : TEv} {m : Ev}
    (ha : a ∈ P.avail G) (hm : G.IsMe m) : ¬ nextLtEv (.th a) m := by
  have key : ∀ y ∈ P.avail G, ∀ m, G.IsMe m → ¬ nextLtEv (.th y) m := by
    clear ha hm
    induction h with
    | refl =>
      intro y hy
      rw [Full] at hff
      rw [hff] at hy
      exact absurd hy (by simp)
    | tail hch hs ih =>
      obtain ⟨e, k, hs⟩ := hs
      obtain ⟨hW, hE, hcn, -⟩ := PrevReachR.inv hM hGf hEf hcan hcf hch
      exact (hs.s1_step hW hE hcn ih).2
  exact key a ha m hm

/-- Lemma A.24: the event that a backward step removes is the next event of
the graph it returns. -/
theorem PrevReachR.next_of_prevStep {Gf G G' : Graph} {e : TEv} {k : Kind} (hM : M.Extensible)
    (hGf : Gf.Wf) (hEf : P.Exec Gf) (hcan : Gf.IsCanon) (hcf : (M.sym S).rf.cons Gf)
    (hff : P.Full Gf) (h : PrevReachR P γ τ Gf G) (hs : PrevStepR P γ τ G e k G') :
    P.IsNext G' e := by
  obtain ⟨hW, hE, hcn, -⟩ := PrevReachR.inv hM hGf hEf hcan hcf h
  exact (hs.s1_step hW hE hcn
    (fun y hy m hm => PrevReachR.s1 hM hGf hEf hcan hcf hff h hy hm)).1

end Condpor
