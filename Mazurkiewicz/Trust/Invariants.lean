import Mazurkiewicz.Trust.Alg

/-!
# Invariants of the exploration: Lemma A.20 and Proposition A.22

Paper: Appendix A.3, Lemma A.20 (D1)-(D3) and Proposition A.22 (P1)-(P6),
(P9). Clauses (P7) and (P8) of Proposition A.22 are about exclusive
(read-modify-write) events and are out of scope. Coq: `trust/Alg.v` (the
lemmas on `D`, `Da`, and `B23`, `B23_P6`).

Notation of the paper and its reading here.

* `G.rf ∩ >` is the set of pairs `⟨s, q⟩` with `G.rf(q) = s` and `s > q`: the
  read `q` reads from a write `s` that was added after it. Such a pair exists
  only after `s` has revisited `q`. Here: `c.Bw s q`.
* `<next` is `Program.nextLt` on thread events.
* `me(G)` (Def. A.13) is the `<next`-greatest event among the `porf`-maximal
  events of `G`. Here: `G.IsMe a`, a relation. The appendix's `G.E` omits
  `init` (its base case has `G.E = {e}`); `IsMe` agrees with Def. A.13 on
  graphs with a thread event, and that `me` of a graph without thread events
  is `init` is a convention of this file.
* In Lemma A.20 the step is a revisit `⟨G, <⟩ ⇒ ⟨G', <'⟩` of the read `a` by
  the new write `e`; `D = Del(⟨G, <⟩, a, e)` and `D_a = D ∪ {a}`; `G.porf` is
  the causality of the graph before `e`.
* In Proposition A.22 the step is `⟨G̃, <̃⟩ ⇒ ⟨G, <⟩`, adding `e`; (P1), (P2),
  (P4), (P5), (P6) speak of the configuration after the step, (P3) and (P9) of
  the deleted events of a revisit, which are events of the configuration
  before it.
-/

namespace Trust

/- Paper typography. (P3) is printed with an unadorned `<` restricted to a set
of events deleted by the step; the induction target on p. 49:35 uses the order
before the step, which is the only reading that makes sense, and (P3), (P9)
are stated so here. The `G'.rf` in the first statement of (P6) denotes the
graph after the step; all relations of (P6) belong to that configuration.

Coq (`trust/Alg.v`): `Del_rf_l`, `Da_hb_cD`, `Da_hb_rf_l` are (D1), (D2),
(D3); `B23.LR_l` is (P2) with the last factor `<next ∩ <`, stronger than the
paper's; `avail_LR_l` states (P5), second part, positively. -/

namespace Config

/-- `⟨s, q⟩ ∈ G.rf ∩ >`: the read `q` reads from the write `s`, which was
added after `q`. -/
def Bw (c : Config) (s q : TEv) : Prop := c.rf q = some (.th s) ∧ c.lt q s

end Config

namespace Graph

/-- `a` is `me(G)` (Def. A.13): a `porf`-maximal event of `G` that is
`<next`-above every other `porf`-maximal event. -/
def IsMe (G : Graph) (a : Ev) : Prop :=
  a ∈ evSet G.events ∧ (∀ b, ¬ G.porf a b) ∧
    ∀ b ∈ evSet G.events, (∀ c, ¬ G.porf b c) → b ≠ a → Program.nextLtEv b a

theorem _root_.Trust.Program.nextLtEv_asymm {a b : Ev} (h : Program.nextLtEv a b) :
    ¬ Program.nextLtEv b a := by
  cases a with
  | init =>
    cases b with
    | init => exact fun h' => h'
    | th q => exact fun h' => h'
  | th p =>
    cases b with
    | init => exact absurd h (fun h' => h')
    | th q => exact fun h' => Program.nextLt_irrefl p (Program.nextLt_trans h h')

/-- A non-empty finite set of thread events has a `<next`-greatest element. -/
theorem _root_.Trust.Program.exists_nextLt_max (S : Finset TEv) (hS : S.Nonempty) :
    ∃ m ∈ S, ∀ b ∈ S, b ≠ m → Program.nextLt b m := by
  classical
  induction hS using Finset.Nonempty.cons_induction with
  | singleton a =>
    refine ⟨a, Finset.mem_singleton_self a, fun b hb hne => ?_⟩
    exact absurd (Finset.mem_singleton.mp hb) hne
  | cons a s ha _ ih =>
    obtain ⟨m, hm, hmax⟩ := ih
    have ham : a ≠ m := fun h => ha (h ▸ hm)
    rcases Program.nextLt_total ham with h | h
    · refine ⟨m, Finset.mem_cons.mpr (Or.inr hm), fun b hb hne => ?_⟩
      rcases Finset.mem_cons.mp hb with rfl | hb
      · exact h
      · exact hmax b hb hne
    · refine ⟨a, Finset.mem_cons_self a s, fun b hb hne => ?_⟩
      rcases Finset.mem_cons.mp hb with hba | hb
      · exact absurd hba hne
      · by_cases hbm : b = m
        · exact hbm ▸ h
        · exact Program.nextLt_trans (hmax b hb hbm) h

/-- In the graph without thread events, `me` is `init` (a convention). -/
theorem isMe_init (μ : Loc → Val) : (Graph.init μ).IsMe .init := by
  refine ⟨trivial, fun b hb => ?_, fun b hb _ hne => ?_⟩
  · obtain ⟨c, hc⟩ := Maz.exists_first_of_transGen hb
    rcases hc with hc | ⟨q, -, hq, -⟩
    · cases c with
      | init => exact hc
      | th q => simp [Graph.po, Graph.init] at hc
    · simp [Graph.init] at hq
  · cases b with
    | init => exact absurd rfl hne
    | th q => simp [Graph.init] at hb

/-- `me(G)` is unique. -/
theorem IsMe.unique {G : Graph} {a b : Ev} (ha : G.IsMe a) (hb : G.IsMe b) : a = b := by
  by_contra hne
  have h1 := ha.2.2 b hb.1 hb.2.1 (Ne.symm hne)
  have h2 := hb.2.2 a ha.1 ha.2.1 hne
  exact Program.nextLtEv_asymm h1 h2

/-- A well-formed graph without causality cycle has a `me`. -/
theorem exists_isMe {G : Graph} (hG : G.Wf) (hac : Maz.Acyclic G.porfStep) : ∃ a, G.IsMe a := by
  classical
  by_cases h0 : G.events = ∅
  · refine ⟨.init, trivial, fun b hb => ?_, fun b hb _ hne => ?_⟩
    · obtain ⟨c, hc⟩ := Maz.exists_first_of_transGen hb
      have := (hG.mem_of_porfStep hc).2
      cases c with
      | init => exact G.not_porfStep_init _ hc
      | th q => simp [h0] at this
    · cases b with
      | init => exact absurd rfl hne
      | th q => simp [h0] at hb
  · have hne : G.events.Nonempty := Finset.nonempty_iff_ne_empty.mpr h0
    -- the porf-maximal thread events
    have hmaxEx : ∃ e ∈ G.events, ∀ b, ¬ G.porf (.th e) b := by
      obtain ⟨a, ha, hmax⟩ := hac.exists_maximal (G.events.image Ev.th) (hne.image _)
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
      refine ⟨e, he, fun b hb => ?_⟩
      obtain ⟨c, hc⟩ := Maz.exists_first_of_transGen hb
      have hcm := (hG.mem_of_porfStep hc).2
      cases c with
      | init => exact G.not_porfStep_init _ hc
      | th q => exact hmax _ (Finset.mem_image.mpr ⟨q, hcm, rfl⟩) hc
    obtain ⟨e0, he0, hmax0⟩ := hmaxEx
    have hS : (G.events.filter (fun e => ∀ b, ¬ G.porf (.th e) b)).Nonempty :=
      ⟨e0, Finset.mem_filter.mpr ⟨he0, hmax0⟩⟩
    obtain ⟨m, hm, hmm⟩ := Program.exists_nextLt_max _ hS
    obtain ⟨hmE, hmMax⟩ := Finset.mem_filter.mp hm
    refine ⟨.th m, hmE, hmMax, fun b hb hbmax hne' => ?_⟩
    cases b with
    | init =>
      -- `init` is causally before every thread event
      have hstep : G.porfStep .init (.th m) := Or.inl hmE
      exact absurd (Relation.TransGen.single hstep) (hbmax (.th m))
    | th q =>
      exact hmm q (Finset.mem_filter.mpr ⟨hb, hbmax⟩) (fun h => hne' (congrArg Ev.th h))

end Graph

/-! ### Lemma A.20

For a revisit of the read `r` by the new write `w` from the configuration
`c`. `D` is `c.Deleted r w`, and `D_a` adds `r`. The hypotheses are those of
the rule, on a well-formed configuration whose insertion order extends the
program order (every reached configuration, by `Reach.sound`). -/

section A20

variable {c : Config} {r w : TEv}

/-- (D1) `[D]; (G.rf ∩ >) = ∅`: no read reads from a deleted event that was
added after it. -/
theorem A20_D1 (hc : c.Wf)
    (hmax : ∀ e, (c.Deleted r w e ∨ e = r) → c.IsMaximallyAdded e w)
    {d q : TEv} (hd : c.Deleted r w d) : ¬ c.Bw d q := by
  rintro ⟨hrf, hlt⟩
  have hq : q ∈ c.order := List.mem_toFinset.mp (hc.1.rf_source_mem hrf).1
  by_cases hqd : c.Deleted r w q
  · -- the reader is deleted too: its source is in `Previous` (line 27)
    obtain ⟨-, e', he', hprev, -⟩ := hmax q (Or.inl hqd)
    cases hact : q.act with
    | write x v =>
      have hw : q.IsWrite := by simp [TEv.IsWrite, hact, Act.IsWrite]
      have hnone := hc.1.rf_none q (Or.inr hw)
      rw [show c.abs.rf q = c.rf q from rfl, hrf] at hnone
      cases hnone
    | read x =>
      rw [hact] at he'
      simp only at he'
      rw [hrf] at he'
      cases he'
      obtain ⟨-, hle | hpf⟩ := hprev
      · rcases hle with hdq | h
        · rw [hdq] at hlt
          exact List.Before.irrefl _ _ hlt
        · exact List.Before.asymm h hlt
      · exact hd.2.2 hpf
  · -- the reader is kept: line 25 for the deleted source
    have hk : q ∈ c.abs.events ∩ c.keep r w :=
      Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hq, (Config.mem_keep_iff c r w q).mpr ⟨hq, hqd⟩⟩
    have hdk := Config.keep_sources hc (fun e he => hmax e (Or.inl he)) hk hrf
    exact ((Config.mem_keep_iff c r w d).mp hdk).2 hd

/-- One causality step into an event that is not deleted does not start in
`D_a` (the steps ⟨2⟩1 of the paper's proof of (D2), and line 25). -/
theorem A20_step (hc : c.Wf) (hpo : c.PoLt) (hr : r ∈ c.order)
    (hnp : ¬ (c.plus w).porf (.th r) (.th w))
    (hmax : ∀ e, (c.Deleted r w e ∨ e = r) → c.IsMaximallyAdded e w)
    {z y : TEv} (hstep : c.abs.porfStep (.th z) (.th y)) (hy : y ∈ c.order)
    (hny : ¬ c.Deleted r w y) : ¬ (c.Deleted r w z ∨ z = r) := by
  intro hz
  have hym : y ∈ c.abs.events := List.mem_toFinset.mpr hy
  rcases hstep with hpo' | ⟨q, hq, -, hrf⟩
  · obtain ⟨hzm, -, ht, hi⟩ := hpo'
    have hzo : z ∈ c.order := List.mem_toFinset.mp hzm
    have hlt : c.lt z y := hpo z hzo y hy ht hi
    by_cases hpf : (c.plus w).porf (.th y) (.th w)
    · have hst : (c.plus w).porfStep (.th z) (.th y) :=
        Or.inl ⟨Finset.mem_insert_of_mem hzm, Finset.mem_insert_of_mem hym, ht, hi⟩
      have hzw : (c.plus w).porf (.th z) (.th w) := Relation.TransGen.head hst hpf
      rcases hz with hz | hzr
      · exact hz.2.2 hzw
      · exact hnp (hzr ▸ hzw)
    · have hnlt : ¬ c.lt r y := fun h => hny ⟨hy, h, hpf⟩
      rcases hz with hz | hzr
      · exact hnlt (List.Before.trans hlt hz.2.1)
      · exact hnlt (hzr ▸ hlt)
  · have hqy : q = y := (Ev.th.inj hq).symm
    rw [hqy] at hrf
    rcases hz with hz | hzr
    · -- the source is deleted and the reader is kept: line 25
      have hk : y ∈ c.abs.events ∩ c.keep r w :=
        Finset.mem_inter.mpr ⟨hym, (Config.mem_keep_iff c r w y).mpr ⟨hy, hny⟩⟩
      have hzk := Config.keep_sources hc (fun e he => hmax e (Or.inl he)) hk hrf
      exact ((Config.mem_keep_iff c r w z).mp hzk).2 hz
    · -- the source is the revisited event: line 25 for `r`
      rw [hzr] at hrf
      refine (hmax r (Or.inr rfl)).1 ⟨y, ⟨hy, ?_⟩, hrf⟩
      by_cases hpf : (c.plus w).porf (.th y) (.th w)
      · exact Or.inr hpf
      · left
        have hnlt : ¬ c.lt r y := fun h => hny ⟨hy, h, hpf⟩
        by_cases hyr : y = r
        · exact Or.inl hyr
        · rcases List.Before.total hy hr hyr with h | h
          · exact absurd h hnlt
          · exact Or.inr h

/-- (D2) `[D_a]; G.porf; [G.E \\ D] = ∅`: no deleted event, and not the
revisited read, is causally before an event that is not deleted. -/
theorem A20_D2 (hc : c.Wf) (hpo : c.PoLt) (hr : r ∈ c.order)
    (hnp : ¬ (c.plus w).porf (.th r) (.th w))
    (hmax : ∀ e, (c.Deleted r w e ∨ e = r) → c.IsMaximallyAdded e w)
    {x y : TEv} (hx : c.Deleted r w x ∨ x = r) (hy : y ∈ c.order)
    (hny : ¬ c.Deleted r w y) : ¬ c.abs.porf (.th x) (.th y) := by
  intro hp
  have key : ∀ a, Relation.TransGen c.abs.porfStep a (.th y) →
      ∀ z, a = .th z → ¬ (c.Deleted r w z ∨ z = r) := by
    intro a ha
    induction ha using Relation.TransGen.head_induction_on with
    | single h =>
      intro z hz
      rw [hz] at h
      exact A20_step hc hpo hr hnp hmax h hy hny
    | @head a b h _ ih =>
      intro z hz
      rw [hz] at h
      cases b with
      | init => exact absurd h (c.abs.not_porfStep_init _)
      | th y' =>
        have hy'm : y' ∈ c.order := List.mem_toFinset.mp (hc.1.mem_of_porfStep h).2
        have hny' : ¬ c.Deleted r w y' := fun hd => ih y' rfl (Or.inl hd)
        exact A20_step hc hpo hr hnp hmax h hy'm hny'
  exact key _ hp x rfl hx

/-- (D3) `[D_a]; G.porf?; (G.rf ∩ >) = ∅`: no deleted event, and not the
revisited read, is equal to or causally before a write that was added after a
read that reads from it. -/
theorem A20_D3 (hc : c.Wf) (hpo : c.PoLt) (hr : r ∈ c.order)
    (hnp : ¬ (c.plus w).porf (.th r) (.th w))
    (hmax : ∀ e, (c.Deleted r w e ∨ e = r) → c.IsMaximallyAdded e w)
    {x s q : TEv} (hx : c.Deleted r w x ∨ x = r)
    (hxs : x = s ∨ c.abs.porf (.th x) (.th s)) : ¬ c.Bw s q := by
  rintro ⟨hrf, hlt⟩
  have hs : s ∈ c.order := List.mem_toFinset.mp (hc.1.rf_source_mem hrf).2
  have hq : q ∈ c.order := List.mem_toFinset.mp (hc.1.rf_source_mem hrf).1
  by_cases hsd : c.Deleted r w s
  · exact A20_D1 hc hmax hsd ⟨hrf, hlt⟩
  · rcases hxs with hxs | hxs
    · -- `x = s` is not deleted, so it is `r`: line 25 for `r`
      have hsr : s = r := by
        rcases hx with hx | hx
        · exact absurd (hxs ▸ hx) hsd
        · exact hxs.symm.trans hx
      rw [hsr] at hrf hlt
      exact (hmax r (Or.inr rfl)).1 ⟨q, ⟨hq, Or.inl (Or.inr hlt)⟩, hrf⟩
    · exact A20_D2 hc hpo hr hnp hmax hx hs hsd hxs

end A20

/-! ### Proposition A.22 -/

/-- The event that Proposition A.22 (P4) names as `me` of the new graph: the
revisited read for a revisit, the added event otherwise. -/
def Kind.me (e : TEv) : Kind → TEv
  | .nr => e
  | .rv r => r

/-- The clauses (P1)-(P6) and (P9) of Proposition A.22 for a step
`c ⇒ c'` that adds `e` with kind `k`. -/
structure A22 (P : Program) (c : Config) (e : TEv) (k : Kind) (c' : Config) : Prop where
  /-- (P1) `G.rf ∩ > ∩ <next = ∅` -/
  p1 : ∀ s q, c'.Bw s q → ¬ Program.nextLt s q
  /-- (P2) `(<next ∩ >)⁻¹ ⊆ G.porf?; (G.rf ∩ >); <next` -/
  p2 : ∀ x ∈ c'.order, ∀ y ∈ c'.order, Program.nextLt x y → c'.lt y x →
    ∃ s q, (y = s ∨ c'.abs.porf (.th y) (.th s)) ∧ c'.Bw s q ∧ Program.nextLt q x
  /-- (P3) for a revisit of `r`: on `Del ∪ {r}` the insertion order of `c` (the
  configuration before the step, the paper's `<̃`) is `<next` -/
  p3 : ∀ r, k = .rv r → ∀ x y, (c.Deleted r e x ∨ x = r) → (c.Deleted r e y ∨ y = r) →
    (c.lt x y ↔ Program.nextLt x y)
  /-- (P4) `me(G)` is the revisited read, or the added event -/
  p4 : c'.abs.IsMe (.th (k.me e))
  /-- (P5), first part: `(<next ∩ >); [me(G)] = ∅` -/
  p5a : ∀ x ∈ c'.order, Program.nextLt x (k.me e) → ¬ c'.lt (k.me e) x
  /-- (P5), second part: `[avail(G)]; <next; [me(G)] = ∅` -/
  p5b : ∀ a ∈ P.avail c'.abs, ¬ Program.nextLt a (k.me e)
  /-- (P6), in the configuration after the step (the paper's first statement of
  this clause writes `G'.rf` for the `rf` of that graph) -/
  p6 : ∀ s q p, p ≠ s → p ≠ q → c'.Bw s q → Program.nextLt q p → p ∈ c'.order →
    c'.lt p q ∨ c'.lt s p ∨ c'.abs.porf (.th p) (.th s)
  /-- (P9) for a revisit of `r`: `[e]; <next; [Del] = ∅`, with `Del` the deleted
  events of this step -/
  p9 : ∀ r, k = .rv r → ∀ d, c.Deleted r e d → ¬ Program.nextLt e d

end Trust
