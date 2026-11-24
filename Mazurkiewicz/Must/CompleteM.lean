import Mazurkiewicz.Must.GetNextRev

/-!
# Termination of `GetNext`, Lemma A.16, completeness (milestone M7)

Paper: Lemma A.16 (pp. 31–34), Theorem A.1 / Theorem 4.1 (completeness, p. 28). Plan: fate rows
"Algorithm 2", A.16, "Thm 4.1/A.1"; Section 5 row M7 (`getNext_spec`,
`productionSequence_reaches`, `completeM`); the addendum after M6.

* `getNext_exists` (termination and totality of `GetNext` on its domain, with its
  specification): by well-founded induction on the measure `⟨N − |G_s.E|, |G_t.S|⟩`
  (lexicographic; `N = |threads| · n` bounds the events of every execution of a program bounded
  by `n`, so the subtraction is the remaining capacity). Case 1 of line 9: one non-revisit step.
  Case 2: the first iteration of the loop calls `GetNext(G_s, MaxCompletion(G_p, [r₀]))`, whose
  target has strictly fewer sends than `G_t` (`sends_lt`; the printed "one less send", A.16 ⟨5⟩3);
  every later call starts from a graph with more events than `G_s`; the loop itself terminates by
  `loop_exists`; line 23 is `stepM_revisit`.
* `getNext_total`, `GetNext.det` (in `GetNext.lean`): on its domain `GetNext` is a total
  function. `getNext_spec`: every result satisfies the specification (A.16 ⟨1⟩1: P1–P3,
  repaired).
* `productionSequence_reaches` (Lemma A.16): for `G_f ∈ ⟦P⟧` of a bounded program,
  `ProductionSequence(G_f)` from the initial configuration terminates and its steps are a path of
  `StepM` (so of `ReachM`) to a configuration with graph `G_f`.
* `completeM` (Theorem A.1 repaired, plan row "Thm 4.1/A.1"): every `G ∈ ⟦P⟧` is the graph of a
  reachable configuration with no next event (reported by line 4 of Algorithm 1).
  `reported_iff_sem`: with M4's `reported_mem_sem`, the reported graphs are exactly `⟦P⟧`.

Hypotheses: every model `M`; a tie-break with `TieQ9 M tie`; a program with `P.Bounded n`.
-/

namespace Must

open Graph Relation Config

variable {Q : Type} [DecidableEq Q] [Membership Val Q]
variable {M : Model Q} {P : Program Q} {tie : Tie Q}

/-- Case 1 of line 9 as a derivation: `GetNext` adds `e` with its source and outcome in `G_t`. -/
theorem getNext_case1_of {c : Config Q} {Gt : Graph Q} {e : Ev Q} (hd : CallDom M P c Gt e)
    (hc1 : ∀ s, Gt.rf e = some (.snd s) → s ∈ c.G.events) :
    GetNext M tie P (.call c Gt) [c.add e (Gt.rf e) (Gt.nd e)] (c.add e (Gt.rf e) (Gt.nd e)) :=
  have h := next_prefix_case1 hd.pfx (nextEv_of_nextP hd.next) hd.mem hc1
  .case1 hd.next ⟨h.1.1, h.1.2.1⟩ h.2

/-- Case 1 of line 9: one non-revisit step adds `e` with its source and outcome in `G_t`. -/
theorem case1_exists {c : Config Q} {Gt : Graph Q} {e : Ev Q} (hd : CallDom M P c Gt e)
    (hc1 : ∀ s, Gt.rf e = some (.snd s) → s ∈ c.G.events) :
    ∃ S c', GetNext M tie P (.call c Gt) S c' ∧ CallSpec M tie P c Gt e S c' := by
  obtain ⟨hop, hpf⟩ := next_prefix_case1 hd.pfx (nextEv_of_nextP hd.next) hd.mem hc1
  have heG := hd.inv.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv (nextEv_of_nextP hd.next))
  have hsp : SPfx M P c.G (c.G.add e (Gt.rf e) (Gt.nd e)) :=
    sPfx_iff_exists.mpr ⟨Pfx.of_between hd.pfx hpf (fun x hx => Finset.mem_insert_of_mem hx), e,
      Finset.mem_insert_self _ _, heG⟩
  refine ⟨_, _, .case1 hd.next ⟨hop.1, hop.2.1⟩ hpf, ?_⟩
  refine ⟨StepSeq.single (.nr (opAdd_nrAdd hd.next hop)), hpf, hsp,
    Finset.mem_insert_self _ _, List.prefix_refl _, fun d hd' => ?_⟩
  rw [List.mem_singleton] at hd'
  subst hd'
  exact ⟨List.prefix_refl _, hsp.1.pre⟩

/-- A.16 ⟨5⟩3 ("one less send", read as "strictly fewer sends"): `MaxCompletion(G_p, [r₀])`
adds the receive `r₀` to `G_p`, which lacks the send `s₀` of `G_t`. -/
theorem sends_lt {c₀ : Config Q} {Gt : Graph Q} {r₀ s₀ : Ev Q} (hx : Ctx M P c₀ Gt r₀ s₀)
    {X₁ : Graph Q} (hX₁ : X₁.events = insert r₀ (prefixExt c₀.G Gt s₀).events) :
    X₁.S.card < Gt.S.card := by
  have h1 : X₁.S = (prefixExt c₀.G Gt s₀).S := by
    unfold Graph.S
    have hns : ¬ r₀.IsSend := Lab.IsRecv.not_isSend hx.facts.2.2.1
    rw [hX₁, Finset.filter_insert]
    simp only [hns, ↓reduceIte]
  rw [h1]
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨fun x hxS => ?_, fun heq => ?_⟩)
  · rw [Graph.mem_S] at hxS ⊢
    exact ⟨hx.gp_right.events_subset hxS.1, hxS.2⟩
  · have hs : s₀ ∈ Gt.S := (Graph.mem_S _).mpr ⟨hx.facts.1, hx.facts.2.1⟩
    rw [← heq] at hs
    exact hx.s₀_not_mem ((Graph.mem_S _).mp hs).1

/-- Termination and totality of `GetNext` on its domain, with its specification (Lemma A.16
⟨1⟩1, ⟨2⟩3), by induction on `⟨N − |G_s.E|, |G_t.S|⟩`. -/
theorem getNext_exists (hT : TieQ9 M tie) {n : ℕ} (hb : P.Bounded n) :
    ∀ (a b : ℕ) (c : Config Q) (Gt : Graph Q) (e : Ev Q),
      P.threads.length * n - c.G.events.card = a → Gt.S.card = b → CallDom M P c Gt e →
      ∃ S c', GetNext M tie P (.call c Gt) S c' ∧ CallSpec M tie P c Gt e S c' := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a iha =>
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ihb =>
  intro c Gt e ha hbS hd
  by_cases hc1 : ∀ s, Gt.rf e = some (.snd s) → s ∈ c.G.events
  · exact case1_exists hd hc1
  push Not at hc1
  obtain ⟨s₀, hs, hs₀⟩ := hc1
  have hx : Ctx M P c Gt e s₀ := ⟨hd, hs, hs₀⟩
  have IH : ∀ (c' : Config Q) (X : Graph Q) (e' : Ev Q), CallDom M P c' X e' →
      c.G.events.card < c'.G.events.card →
      ∃ S c'', GetNext M tie P (.call c' X) S c'' ∧ CallSpec M tie P c' X e' S c'' := by
    intro c' X e' hd' hlt
    have hle := card_le_of_bounded hd'.inv.wf hd'.inv.exec hb
    exact iha _ (by omega) _ c' X e' rfl rfl hd'
  -- the first iteration: `r₀ = e` is deferred, `A = [r₀]`
  have heGp := hx.r₀_not_mem
  have hav : e ∈ M.availM P (prefixExt c.G Gt s₀) :=
    availM_stable hd.inv.cons hx.gp_right.cons hx.gp_right.exec hx.gp_left.pre
      (Model.mem_availM_of_nextP hd.next) heGp
  obtain ⟨X₁, hX₁, hs₁, hGpX₁⟩ := maxCompletion_snoc (A := []) hT hx.gp_right.cons
    hx.gp_right.exec maxCompletion_nil hav
  have hX₁e : X₁.events = insert e (prefixExt c.G Gt s₀).events := by
    obtain ⟨-, src, out, -, rfl⟩ := hs₁
    rfl
  have hd₁ : CallDom M P c X₁ e :=
    ⟨hd.inv, hx.gp_left.trans hGpX₁, hd.next, by rw [hX₁e]; exact Finset.mem_insert_self _ _⟩
  have hlt₁ : X₁.S.card < b := hbS ▸ sends_lt hx hX₁e
  obtain ⟨S₁, c₁, h₁, hsp₁⟩ := ihb _ hlt₁ c X₁ e ha rfl hd₁
  have hI₁ : LoopInv M tie P c Gt e s₀ c₁ ([] ++ [e]) X₁ :=
    loopInv_of_call hx hd.inv List.nodup_nil (by simp) (by simp) (by simp)
      hd.inv.wf.isPrefixOf_refl (List.prefix_refl _) hd.next (Or.inr ⟨rfl, heGp⟩) ⟨[], rfl⟩
      (by simpa using hx.facts.2.2.2) hX₁ hsp₁
  -- the remaining iterations
  obtain ⟨S₂, cL, AL, XL, h₂, hp₂, hk₂, hnL, hIL⟩ := loop_exists hT hb hx IH _ c₁ _ X₁ rfl hI₁
  have hnt : ¬ LoopTest M P (prefixExt c.G Gt s₀) s₀ c.G e :=
    fun h => h.2.elim heGp (fun h' => hx.facts.2.2.2 h'.symm)
  have hloop : GetNext M tie P (.loop (prefixExt c.G Gt s₀) s₀ c []) (S₁ ++ S₂) cL :=
    .defer hd.next hnt hX₁ h₁ h₂
  -- line 23
  have hstep := hIL.stepM_revisit hT hx hnL
  have hgraph := hIL.revisit_graph hT hx hnL
  have hord := hIL.revisit_order hT hx hnL
  have hn₂ := case2_step₂ hd.pfx hx.nextEv hd.mem hs hs₀
  have hsp₂ := case2_sPfx hd.pfx hx.nextEv hd.mem hs hs₀
  refine ⟨_, _, .case2 hd.next hx.not_test hs hloop, ?_⟩
  refine ⟨(hsp₁.path.append hp₂).append (StepSeq.single hstep), by rw [hgraph]; exact hn₂.2,
    by rw [hgraph]; exact hsp₂, ?_, hord, fun d hd' => ?_⟩
  · rw [hgraph, revTarget_events hd.pfx]
    exact Finset.mem_insert_self _ _
  · rcases List.mem_append.mp hd' with hd' | hd'
    · rcases List.mem_append.mp hd' with hd' | hd'
      · exact hsp₁.keep d hd'
      · obtain ⟨k1, k2⟩ := hk₂ d hd'
        exact ⟨hsp₁.ord.trans k1, hsp₁.spfx.1.pre.trans k2⟩
    · rw [List.mem_singleton] at hd'
      subst hd'
      refine ⟨hord, ?_⟩
      rw [hgraph]
      exact hsp₂.1.pre

/-- `GetNext` is total on its domain: termination of Algorithm 2's `GetNext` (A.16 ⟨2⟩3). -/
theorem getNext_total (hT : TieQ9 M tie) {n : ℕ} (hb : P.Bounded n) {c : Config Q}
    {Gt : Graph Q} {e : Ev Q} (hd : CallDom M P c Gt e) :
    ∃ S c', GetNext M tie P (.call c Gt) S c' ∧ CallSpec M tie P c Gt e S c' :=
  getNext_exists hT hb _ _ c Gt e rfl rfl hd

/-- `getNext_spec` (Lemma A.16 ⟨1⟩1, repaired): on the strengthened domain (`c.G ⊑ Gt`,
`e = next_P(c.G) ∈ Gt.E`, the configuration invariant), the result of `GetNext(c.G, Gt)` is a
sequence of algorithmic steps from `c` to `c'` (P2) with `c.G ⊏ c'.G ⊑ Gt` and `e ∈ c'.G.E`
(P1, strengthened), every configuration of which keeps `c.order ++ [e]` as a prefix of its order
and `c.G` as a causal prefix of its graph (P3). -/
theorem getNext_spec (hT : TieQ9 M tie) {n : ℕ} (hb : P.Bounded n) {c : Config Q}
    {Gt : Graph Q} {e : Ev Q} {S : List (Config Q)} {c' : Config Q} (hd : CallDom M P c Gt e)
    (h : GetNext M tie P (.call c Gt) S c') : CallSpec M tie P c Gt e S c' := by
  obtain ⟨S', c'', h', hs⟩ := getNext_total hT hb hd
  obtain ⟨rfl, rfl⟩ := h.det h'
  exact hs

/-- The outer loop of `ProductionSequence` from a configuration below a full `G_f`. -/
theorem prodSeq_exists (hT : TieQ9 M tie) {n : ℕ} (hb : P.Bounded n) {Gf : Graph Q}
    (hf : M.FullM P Gf) :
    ∀ (k : ℕ) (c : Config Q), P.threads.length * n - c.G.events.card = k → c.Inv M P →
      Pfx M P c.G Gf →
      ∃ S c', ProdSeq M tie P Gf c S c' ∧ StepSeq M tie P c S c' ∧ c'.G = Gf := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro c hk hc hp
  by_cases heq : c.G = Gf
  · exact ⟨[], c, .done heq, .nil c, heq⟩
  have hsp : SPfx M P c.G Gf := ⟨hp, heq⟩
  obtain ⟨y, -, -, hy⟩ := exists_avail_of_sPfx hsp
  obtain ⟨e, hn⟩ := nextP_isSome_of_mem hy
  have he : e ∈ Gf.events := by
    by_contra he
    have := availM_stable hp.cons hp.cons' hp.exec' hp.pre (Model.mem_availM_of_nextP hn) he
    rw [show M.availM P Gf = [] from hf] at this
    exact List.not_mem_nil this
  obtain ⟨S₁, c₁, h₁, hs₁⟩ := getNext_total hT hb ⟨hc, hp, hn, he⟩
  have hc₁ := (hs₁.path.inv hc).1
  have hlt : P.threads.length * n - c₁.G.events.card < k := by
    have h1 := hs₁.spfx.card_lt
    have h2 := card_le_of_bounded hc₁.wf hc₁.exec hb
    omega
  obtain ⟨S₂, c₂, h₂, hp₂, heq₂⟩ := ih _ hlt c₁ rfl hc₁ hs₁.pfx
  exact ⟨S₁ ++ S₂, c₂, .step heq h₁ h₂, hs₁.path.append hp₂, heq₂⟩

/-- `productionSequence_reaches` (Lemma A.16): for `G_f ∈ ⟦P⟧` of a bounded program,
`ProductionSequence(G_f)` from `⟨G∅, ∅⟩` returns a sequence of algorithmic steps (`StepM`) that
leads to a configuration with graph `G_f`; that configuration is reachable. -/
theorem productionSequence_reaches (hT : TieQ9 M tie) {n : ℕ} (hb : P.Bounded n) {Gf : Graph Q}
    (hG : M.Sem P Gf) :
    ∃ S c', ProdSeq M tie P Gf Config.init S c' ∧ StepSeq M tie P Config.init S c' ∧
      c'.G = Gf ∧ ReachM M tie P c' := by
  obtain ⟨-, hE, hc, hf⟩ := hG
  obtain ⟨S, c', h1, h2, h3⟩ := prodSeq_exists hT hb hf _ Config.init rfl Config.inv_init
    (Pfx.of_isPrefixOf hc hE (Graph.empty_isPrefixOf Gf))
  exact ⟨S, c', h1, h2, h3, h2.reachM .refl⟩

/-- `completeM` (Theorem A.1 / 4.1 completeness, repaired): for a bounded program, every
`G ∈ ⟦P⟧` is the graph of a reachable configuration without next event, i.e. a graph reported by
line 4 of Algorithm 1. -/
theorem completeM (hT : TieQ9 M tie) {n : ℕ} (hb : P.Bounded n) {G : Graph Q}
    (hG : M.Sem P G) : ∃ c, ReachM M tie P c ∧ c.G = G ∧ M.nextP P c.G = none := by
  obtain ⟨S, c, -, -, h3, h4⟩ := productionSequence_reaches hT hb hG
  refine ⟨c, h4, h3, ?_⟩
  rw [h3]
  exact Model.nextP_eq_none_iff.mpr hG.2.2.2

/-- Soundness (M4) and completeness together: for a bounded program, the graphs of the reachable
configurations without next event are exactly `⟦P⟧`. -/
theorem reported_iff_sem (hT : TieQ9 M tie) {n : ℕ} (hb : P.Bounded n) {G : Graph Q} :
    (∃ c, ReachM M tie P c ∧ M.nextP P c.G = none ∧ c.G = G) ↔ M.Sem P G := by
  constructor
  · rintro ⟨c, h1, h2, rfl⟩
    exact reported_mem_sem h1 h2
  · intro h
    obtain ⟨c, h1, h2, h3⟩ := completeM hT hb h
    exact ⟨c, h1, h3, h2⟩

end Must

#print axioms Must.getNext_case1_of
#print axioms Must.case1_exists
#print axioms Must.sends_lt
#print axioms Must.getNext_exists
#print axioms Must.getNext_total
#print axioms Must.getNext_spec
#print axioms Must.prodSeq_exists
#print axioms Must.productionSequence_reaches
#print axioms Must.completeM
#print axioms Must.reported_iff_sem
