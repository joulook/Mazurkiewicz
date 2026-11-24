import Mazurkiewicz.Must.OptimalPersist

/-!
# Optimality, part 3: forcing, Theorem A.19 and optimality (milestone M8)

Paper: Appendix A.9, Theorem A.19 (p. 34–35: "Given a full, consistent execution `G_f`, there is
exactly one production sequence that reaches a configuration `⟨G_f, −⟩`") and its proof ("any
sequence of algorithmic steps that reaches an execution `Ĝ ⊒ G_t` from `G_s` ... must start with
the steps in `S`"); Theorem 4.1 (a). Plan: rows A.19, Thm 4.1/A.3 (a), M8 (`production_unique`),
M9 (`ReachM.eq_of_abs_eq`).

Results (every model `M`, every tie-break with `TieQ9`, every bounded program; no stability of
the tie-break is assumed):

* `getNext_forced` (A.19's induction): for every derivation of `GetNext(c.G, Gt)` on its domain,
  every sequence of algorithmic steps from `c` that reaches a configuration containing `Gt` (same
  sources and outcomes, `Sub`) starts with the steps returned by `GetNext`. Proof by induction on
  the derivation: Case 1 (`next_after_frozen`, A.18); Case 2 (`case2_tau`: the revisit of `r₀` by
  `s₀` happens, its replay base is `G_p`, and the configuration before it is the canonical replay
  of `r₀ :: Deleted` from `G_p` (M5's `revCond_iff_replay`)); the loop: the break (`s₀` cannot be
  added and deleted again: the send of the deleting revisit is protected, so kept, so in `G_p`,
  which is already in the configuration), `good`/`defer` (the deferred list is a prefix of
  `r₀ :: Deleted` because the loop state stays frozen up to the revisit (A.18 with the
  intermediate target), so the recursive target `MaxCompletion(G_p, A)` is contained in the
  configuration before the revisit and the recursive call is forced).
* `optimality` (Theorem 4.1 (a)): two sequences of steps from the initial configuration that end
  in configurations with the same graph are equal, and so are their ends;
  `ReachM.eq_of_abs_eq`, `stepSeq_unique`, `StepM.pred_unique`, `production_unique` (A.19).
-/

namespace Must

open Graph Relation Config

variable {Q : Type} [DecidableEq Q] [Membership Val Q]
variable {M : Model Q} {P : Program Q} {tie : Tie Q}

/-! ### Paths as lists of configurations -/

namespace StepSeq

variable {c d : Config Q} {πs : List (Config Q)}

/-- The last configuration of a sequence of steps. -/
theorem getElem_length (h : StepSeq M tie P c πs d) :
    (c :: πs)[πs.length]'(by simp) = d := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simpa using ih

/-- The `i`-th step of a sequence. -/
theorem step (h : StepSeq M tie P c πs d) {i : ℕ} (hi : i < πs.length) :
    StepM M tie P ((c :: πs)[i]'(by simp; omega)) (πs[i]) := by
  induction h generalizing i with
  | nil => simp at hi
  | cons hs _ ih =>
    rcases i with _ | i
    · simpa using hs
    · simpa using ih (i := i) (by simpa using hi)

/-- The suffix of a sequence from the `i`-th configuration. -/
theorem drop (h : StepSeq M tie P c πs d) {i : ℕ} (hi : i ≤ πs.length) :
    StepSeq M tie P ((c :: πs)[i]'(by simp; omega)) (πs.drop i) d := by
  induction h generalizing i with
  | nil => rw [List.length_nil, Nat.le_zero] at hi; subst hi; exact .nil _
  | cons hs h' ih =>
    rcases i with _ | i
    · exact .cons hs h'
    · simpa using ih (i := i) (by simpa using hi)

/-- The prefix of a sequence up to the `i`-th configuration. -/
theorem take (h : StepSeq M tie P c πs d) {i : ℕ} (hi : i ≤ πs.length) :
    StepSeq M tie P c (πs.take i) ((c :: πs)[i]'(by simp; omega)) := by
  induction h generalizing i with
  | nil => rw [List.length_nil, Nat.le_zero] at hi; subst hi; exact .nil _
  | cons hs h' ih =>
    rcases i with _ | i
    · exact .nil _
    · simpa using StepSeq.cons hs (ih (i := i) (by simpa using hi))

/-- Every configuration of a sequence from a configuration with the invariant has it. -/
theorem inv_at (h : StepSeq M tie P c πs d) (hc : c.Inv M P) {i : ℕ} (hi : i ≤ πs.length) :
    ((c :: πs)[i]'(by simp; omega)).Inv M P := by
  rcases i with _ | i
  · exact hc
  · exact (h.inv hc).2 _ (List.getElem_mem _)

/-- A sequence whose list starts with the list of another sequence from the same
configuration passes through the end of the other sequence. -/
theorem getElem_of_prefix {S : List (Config Q)} {c' : Config Q} (h : StepSeq M tie P c S c')
    (hp : S <+: πs) : (c :: πs)[S.length]'(by simp; have := hp.length_le; omega) = c' := by
  obtain ⟨R, rfl⟩ := hp
  have e1 : (c :: (S ++ R))[S.length]'(by simp; omega) =
      ((c :: S) ++ R)[S.length]'(by simp; omega) := rfl
  rw [e1, List.getElem_append_left (by simp)]
  exact h.getElem_length

end StepSeq

/-- Reachability gives a sequence of steps from the initial configuration. -/
theorem ReachM.exists_stepSeq {c : Config Q} (h : ReachM M tie P c) :
    ∃ S, StepSeq M tie P Config.init S c := by
  induction h with
  | refl => exact ⟨[], .nil _⟩
  | tail _ hs ih =>
    obtain ⟨S, hS⟩ := ih
    exact ⟨_, hS.append (.single hs)⟩

/-! ### Containment with the same sources -/

/-- `X` is contained in `G` with the same sources and outcomes. -/
def Sub (X G : Graph Q) : Prop :=
  ∀ x ∈ X.events, x ∈ G.events ∧ G.rf x = X.rf x ∧ G.nd x = X.nd x

theorem Pfx.sub {X G : Graph Q} (h : Pfx M P X G) : Sub X G :=
  fun _ hx => ⟨h.events_subset hx, (h.rf_eq hx).symm, (h.nd_eq hx).symm⟩

omit [DecidableEq Q] [Membership Val Q] in
theorem Sub.trans {X Y G : Graph Q} (h₁ : Sub X Y) (h₂ : Sub Y G) : Sub X G := fun x hx =>
  have h := h₁ x hx
  have h' := h₂ x h.1
  ⟨h'.1, h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩

omit [DecidableEq Q] in
/-- Causal predecessors in `G` of an event of a well-formed `X` contained in a well-formed `G`
are causal predecessors in `X`. -/
theorem Sub.porf_of {X G : Graph Q} (h : Sub X G) (hX : X.Wf) (hG : G.Wf) {a b : Ev Q}
    (hab : G.porf a b) (hb : b ∈ X.events) : X.porf a b := by
  have step : ∀ {u v : Ev Q}, G.porfStep u v → v ∈ X.events → X.porfStep u v ∧ u ∈ X.events := by
    intro u v huv hv
    rcases huv with hpo | hrf
    · obtain ⟨y, hy, hyt, hyi⟩ := (hX.exists_idx_iff v.tid u.idx).mpr
        (lt_of_lt_of_le hpo.2.2.2 (hX.idx_lt_cnt hv).le)
      have hyu : y = u := hG.idx_inj y (h y hy).1 u hpo.1 (hyt.trans hpo.2.2.1.symm) hyi
      subst hyu
      exact ⟨Or.inl ⟨hy, hv, hpo.2.2⟩, hy⟩
    · have hrf' : X.rf v = some (.snd u) := (h v hv).2.1.symm.trans hrf.2
      exact ⟨Or.inr ⟨hv, hrf'⟩, hX.rf_mem _ _ hrf'⟩
  induction hab with
  | single huv => exact .single (step huv hb).1
  | tail _ huv ih =>
    obtain ⟨h1, h2⟩ := step huv hb
    exact .tail (ih h2) h1

omit [DecidableEq Q] [Membership Val Q] in
/-- Causality of a contained graph is causality of the containing one. -/
theorem Sub.porf_to {X G : Graph Q} (h : Sub X G) {a b : Ev Q} (hab : X.porf a b) :
    G.porf a b := by
  have step : ∀ {u v : Ev Q}, X.porfStep u v → G.porfStep u v := by
    intro u v huv
    rcases huv with hpo | hrf
    · exact Or.inl ⟨(h u hpo.1).1, (h v hpo.2.1).1, hpo.2.2⟩
    · exact Or.inr ⟨(h v hrf.1).1, (h v hrf.1).2.1.trans hrf.2⟩
  induction hab with
  | single huv => exact .single (step huv)
  | tail _ huv ih => exact .tail ih (step huv)

/-! ### Protected events under steps -/

variable {c c' : Config Q}

/-- A protected event keeps its source and outcome under a step. -/
theorem StepM.rf_nd_of_prot (h : StepM M tie P c c') (hc : c.Inv M P) {x : Ev Q}
    (hx : c.Prot x) : c'.G.rf x = c.G.rf x ∧ c'.G.nd x = c.G.nd x := by
  have hxE := hx.mem hc
  cases h with
  | nr hnr =>
    rename_i e src out
    obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hnr.1
    have heA := hc.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv ht)
    have hxe : x ≠ e := fun h' => heA (h' ▸ hxE)
    simp only [Config.add, add_rf, add_nd, Function.update_of_ne hxe, and_self]
  | revisit hn hS hg hcons =>
    rename_i e r
    obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hn
    have heA := hc.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv ht)
    have hHi := hc.addSend ht hS
    obtain ⟨-, h2, -⟩ := addSend_facts hc ht
    have hxH : (c.add e none none).Prot x := hx.add hc heA
    have hxd := prot_not_del hHi hg h2 hxH
    have hxr : x ≠ r := fun h' => not_prot_r hHi hg h2 (h' ▸ hxH)
    have hxe : x ≠ e := fun h' => heA (h' ▸ hxE)
    have hxH' : x ∈ (c.add e none none).G.events := Finset.mem_insert_of_mem hxE
    refine ⟨?_, ?_⟩
    · rw [revisitCfg_rf hxH' hxd, ite_eq_right hxr]
      change Function.update c.G.rf e none x = _
      rw [Function.update_of_ne hxe]
    · rw [revisitCfg_nd hxH' hxd]
      change Function.update c.G.nd e none x = _
      rw [Function.update_of_ne hxe]

/-- The causal past of a protected event does not grow under a step. -/
theorem StepM.porf_rev_of_prot (h : StepM M tie P c c') (hc : c.Inv M P) {a b : Ev Q}
    (hb : c.Prot b) (hab : c'.G.porf a b) : c.G.porf a b := by
  have hc' := h.inv hc
  -- one step of causality in `c'` into a protected event of `c` is one in `c`
  have step : ∀ {u v : Ev Q}, c'.G.porfStep u v → c.Prot v → c.G.porfStep u v := by
    intro u v huv hv
    have hvE := hv.mem hc
    rcases huv with hpo | hrf
    · -- the new event is `po`-after every event of its thread, so `u` is old
      have hu : u ∈ c.G.events := by
        by_contra hu
        cases h with
        | nr hnr =>
          rename_i e src out
          obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hnr.1
          have hidx := Model.idx_of_nextEv ht
          have hue : u = e := by
            have := hpo.1
            simp only [Config.add, add_events, Finset.mem_insert] at this
            exact this.resolve_right hu
          subst hue
          have := hc.wf.idx_lt_cnt hvE
          rw [← hpo.2.2.1, ← hidx] at this
          exact absurd hpo.2.2.2 (by omega)
        | revisit hn hS hg hcons =>
          rename_i e r
          obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hn
          have hidx := Model.idx_of_nextEv ht
          have hu' := (mem_revisitCfg_events.mp hpo.1).1
          simp only [Config.add, add_events, Finset.mem_insert] at hu'
          have hue : u = e := hu'.resolve_right hu
          subst hue
          have := hc.wf.idx_lt_cnt hvE
          rw [← hpo.2.2.1, ← hidx] at this
          exact absurd hpo.2.2.2 (by omega)
      exact Or.inl ⟨hu, hvE, hpo.2.2⟩
    · have hrf' := (h.rf_nd_of_prot hc hv).1
      exact Or.inr ⟨hvE, hrf'.symm.trans hrf.2⟩
  induction hab with
  | single huv => exact .single (step huv hb)
  | @tail v b' _ hvb ih =>
    have h1 := step hvb hb
    obtain ⟨x', y, hbx, hy⟩ := hb
    exact .tail (ih ⟨x', y, .head h1 hbx, hy⟩) h1


/-! ### Positions and prefixes of the order -/

omit [Membership Val Q] in
theorem pos_lt_of_prefix {d : Config Q} {L : List (Ev Q)} (hp : L <+: d.order) {y : Ev Q}
    (hy : y ∈ L) : d.pos y < L.length := by
  obtain ⟨R, hR⟩ := hp
  simp only [Config.pos, ← hR, List.idxOf_append_of_mem hy]
  exact List.idxOf_lt_length_of_mem hy

omit [Membership Val Q] in
theorem le_pos_of_prefix {d : Config Q} {L : List (Ev Q)} (hp : L <+: d.order) {y : Ev Q}
    (hy : y ∉ L) : L.length ≤ d.pos y := by
  obtain ⟨R, hR⟩ := hp
  simp only [Config.pos, ← hR, List.idxOf_append_of_notMem hy]
  omega

/-- The invariant of the event `e` added right after a frozen configuration `c`: it stays right
after `c` in the order, keeps its outcome, and its source is the original one or a send that is
not an event of `c`. -/
def AfterJ (c : Config Q) (e : Ev Q) (src : Option (Src Q)) (out : Option Val) (x : Config Q) :
    Prop :=
  c.order ++ [e] <+: x.order ∧ x.G.nd e = out ∧
    (x.G.rf e = src ∨ ∃ t, x.G.rf e = some (.snd t) ∧ t ∉ c.G.events)

/-- One step keeps `AfterJ` while `c` stays frozen (a revisit installs a fresh send). -/
theorem after_frozen_step {c a₁ b : Config Q} {e : Ev Q} {src : Option (Src Q)}
    {out : Option Val} (hc : c.Inv M P) (hs : StepM M tie P a₁ b) (hai : a₁.Inv M P)
    (hfa : Frozen c.order.length c a₁) (hfb : Frozen c.order.length c b)
    (hJa : AfterJ c e src out a₁) : AfterJ c e src out b := by
  have hea : e ∈ a₁.G.events := (hai.mem e).mp (hJa.1.subset (by simp))
  cases hs with
  | @nr e' src' out' hnr =>
    obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hnr.1
    have he'A := hai.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv ht)
    have hee' : e ≠ e' := fun h' => he'A (h' ▸ hea)
    refine ⟨prefix_add hJa.1, ?_, ?_⟩
    · simp only [Config.add, add_nd, Function.update_of_ne hee']
      exact hJa.2.1
    · simp only [Config.add, add_rf, Function.update_of_ne hee']
      exact hJa.2.2
  | @revisit e' r' hn hS hg hcons =>
    set H := a₁.add e' none none with hHdef
    obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hn
    have he'A := hai.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv ht)
    have hee' : e ≠ e' := fun h' => he'A (h' ▸ hea)
    have hrd : r' ∉ H.del r' e' := fun h' => lt_irrefl _ (mem_del.mp h').2.2.1
    have hr'c : r' ∉ c.order := by
      intro hr
      have hr' : r' ∈ c.order.take c.order.length := by rwa [List.take_length]
      have h1 := (hfb.2 r' hr').1
      rw [revisitCfg_rf hg.mem hrd] at h1
      simp only [↓reduceIte] at h1
      rw [← (hfa.2 r' hr').1] at h1
      exact he'A (hai.wf.rf_mem _ _ h1.symm)
    have hpreH : c.order ++ [e] <+: H.order := prefix_add hJa.1
    have hcH : c.order <+: H.order := (List.prefix_append _ _).trans hpreH
    have hr'pos : c.order.length ≤ H.pos r' := le_pos_of_prefix hcH hr'c
    have hkeep : ∀ y ∈ c.order ++ [e], y ∉ H.del r' e' ∧ y ≠ e' := by
      intro y hy
      refine ⟨fun hd => ?_, fun h' => he'A (h' ▸ (hai.mem y).mp (hJa.1.subset hy))⟩
      have h1 := pos_lt_of_prefix hpreH hy
      have h2 := (mem_del.mp hd).2.2.1
      simp at h1
      omega
    have heH : e ∈ H.G.events := Finset.mem_insert_of_mem hea
    have hed : e ∉ H.del r' e' := (hkeep e (by simp)).1
    refine ⟨prefix_revisitCfg hpreH hkeep, ?_, ?_⟩
    · rw [revisitCfg_nd heH hed]
      change Function.update a₁.G.nd e' none e = _
      rw [Function.update_of_ne hee']
      exact hJa.2.1
    · rw [revisitCfg_rf heH hed]
      split_ifs with her
      · exact Or.inr ⟨e', rfl, fun h' => he'A ((hai.mem e').mp
          ((List.prefix_append _ _).trans hJa.1 |>.subset ((hc.mem e').mpr h')))⟩
      · have hHe : H.G.rf e = a₁.G.rf e := by
          change Function.update a₁.G.rf e' none e = _
          rw [Function.update_of_ne hee']
        rw [hHe]
        exact hJa.2.2

/-! ### Indexed paths -/

/-- The `i`-th configuration of `c :: πs` (`c` itself beyond the end). -/
abbrev pt (c : Config Q) (πs : List (Config Q)) (i : ℕ) : Config Q := (c :: πs).getD i c

omit [DecidableEq Q] [Membership Val Q] in
theorem pt_eq {c : Config Q} {πs : List (Config Q)} {i : ℕ} (hi : i ≤ πs.length) :
    pt c πs i = (c :: πs)[i]'(by simp; omega) :=
  by unfold pt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]; rfl

omit [DecidableEq Q] [Membership Val Q] in
theorem pt_zero {c : Config Q} {πs : List (Config Q)} : pt c πs 0 = c := rfl

namespace StepSeq

variable {c d : Config Q} {πs : List (Config Q)}

theorem step' (h : StepSeq M tie P c πs d) {i : ℕ} (hi : i < πs.length) :
    StepM M tie P (pt c πs i) (pt c πs (i + 1)) := by
  rw [pt_eq hi.le, pt_eq hi]
  simpa using h.step hi

theorem pt_last (h : StepSeq M tie P c πs d) : pt c πs πs.length = d := by
  rw [pt_eq le_rfl]
  exact h.getElem_length

theorem pt_inv (h : StepSeq M tie P c πs d) (hc : c.Inv M P) {i : ℕ} (hi : i ≤ πs.length) :
    (pt c πs i).Inv M P := by
  rw [pt_eq hi]
  exact h.inv_at hc hi

theorem segment (h : StepSeq M tie P c πs d) {i k : ℕ} (hik : i ≤ k) (hk : k ≤ πs.length) :
    ∃ S, StepSeq M tie P (pt c πs i) S (pt c πs k) := by
  induction k, hik using Nat.le_induction with
  | base => exact ⟨[], .nil _⟩
  | succ k _ ih =>
    obtain ⟨S, hS⟩ := ih (by omega)
    exact ⟨_, hS.append (.single (h.step' (by omega)))⟩

theorem segment_take (h : StepSeq M tie P c πs d) {k : ℕ} (hk : k ≤ πs.length) :
    StepSeq M tie P c (πs.take k) (pt c πs k) := by
  rw [pt_eq hk]
  exact h.take hk

omit [DecidableEq Q] [Membership Val Q] in
theorem pt_mem_take {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ πs.length) :
    pt c πs i ∈ πs.take j := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [pt_eq (by omega)]
  simp only [List.getElem_cons_succ]
  exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩

end StepSeq

/-- The first step from a configuration that stays frozen is a non-revisit step (a revisit would
change the source of an event of the configuration). -/
theorem first_step_nr {c p : Config Q} (hc : c.Inv M P) (h : StepM M tie P c p)
    (hfr : ∀ y ∈ c.G.events, p.G.rf y = c.G.rf y) :
    ∃ e src out, NrAdd M P c.G e src out ∧ p = c.add e src out := by
  cases h with
  | @nr e src out hnr => exact ⟨e, src, out, hnr, rfl⟩
  | @revisit e r hn hS hg hcons =>
    exfalso
    obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hn
    have heA := hc.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv ht)
    have hre : r ≠ e := fun h' => Lab.IsSend.not_isRecv hS (h' ▸ hg.recv)
    have hrc : r ∈ c.G.events := by
      have := hg.mem
      simp only [Config.add, add_events, Finset.mem_insert] at this
      exact this.resolve_left hre
    have hrd : r ∉ (c.add e none none).del r e := fun h' => lt_irrefl _ (mem_del.mp h').2.2.1
    have h1 := hfr r hrc
    rw [revisitCfg_rf hg.mem hrd] at h1
    simp only [↓reduceIte] at h1
    exact heA (hc.wf.rf_mem _ _ h1.symm)

/-- Along a sequence of steps a protected event keeps its causal past (as a set of pairs), and
the events of its causal past and itself keep their sources and outcomes. -/
theorem StepSeq.prot_frozen (hT : TieQ9 M tie) {a b : Config Q} {S : List (Config Q)}
    (h : StepSeq M tie P a S b) (ha : a.Inv M P) {x : Ev Q} (hx : a.Prot x) :
    (∀ y, a.G.porf y x ↔ b.G.porf y x) ∧
      ∀ y, (y = x ∨ a.G.porf y x) → b.G.rf y = a.G.rf y ∧ b.G.nd y = a.G.nd y := by
  induction h with
  | nil => exact ⟨fun _ => Iff.rfl, fun _ _ => ⟨rfl, rfl⟩⟩
  | @cons a₁ b₁ d₁ S₁ hs _ ih =>
    obtain ⟨-, hxb⟩ := hs.prot hT ha hx
    obtain ⟨ih1, ih2⟩ := ih (hs.inv ha) hxb
    have hporf : ∀ y, a₁.G.porf y x ↔ b₁.G.porf y x := fun y =>
      ⟨fun h' => hs.porf_of_prot ha hx h', fun h' => hs.porf_rev_of_prot ha hx h'⟩
    refine ⟨fun y => (hporf y).trans (ih1 y), fun y hy => ?_⟩
    have hyp : a₁.Prot y := by
      rcases hy with rfl | hy
      · exact hx
      · obtain ⟨x', y', hxx, hb⟩ := hx
        exact ⟨x', y', hy.to_reflTransGen.trans hxx, hb⟩
    have h1 := hs.rf_nd_of_prot ha hyp
    have h2 := ih2 y (hy.imp id fun h' => (hporf y).mp h')
    exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

omit [Membership Val Q] in
/-- A canonical replay of a concatenation splits. -/
theorem Replay.split {G G' : Graph Q} {l₁ l₂ : List (Ev Q)}
    (h : Replay tie P G (l₁ ++ l₂) G') : ∃ Z, Replay tie P G l₁ Z ∧ Replay tie P Z l₂ G' := by
  induction l₁ generalizing G with
  | nil => exact ⟨G, .nil G, h⟩
  | cons e l ih =>
    cases h with
    | cons hs hr =>
      obtain ⟨Z, h1, h2⟩ := ih hr
      exact ⟨Z, .cons hs h1, h2⟩

omit [Membership Val Q] in
/-- An event of `H` is revisited or deleted iff it is not in the replay base and is not `s`. -/
theorem mem_insert_del_iff {H : Config Q} {r s x : Ev Q} (hx : x ∈ H.G.events) (hrs : r ≠ s) :
    x ∈ insert r (H.del r s) ↔ x ∉ H.base r s ∧ x ≠ s := by
  rw [mem_base, Finset.mem_insert]
  constructor
  · rintro (rfl | hd)
    · exact ⟨fun h' => h'.2.1 rfl, hrs⟩
    · exact ⟨fun h' => h'.2.2.2 hd, (mem_del.mp hd).2.1⟩
  · rintro ⟨h1, h2⟩
    by_cases hxr : x = r
    · exact Or.inl hxr
    · right
      by_contra hd
      exact h1 ⟨hx, hxr, h2, hd⟩

/-- `r` followed by `Deleted` in insertion order is the insertion order filtered by
`Deleted ∪ {r}`. -/
theorem cons_delList {H : Config Q} {r s : Ev Q} (hH : H.Inv M P) (hr : r ∈ H.G.events) :
    r :: H.delList r s = H.order.filter (fun x => decide (x ∈ insert r (H.del r s))) := by
  have hro : r ∈ H.order := (hH.mem r).mpr hr
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hro
  have hnd := hH.nodup
  rw [hsplit] at hnd
  have hrpre : r ∉ pre := fun h' => by
    have := (List.nodup_append.mp hnd).2.2 r h' r (by simp)
    exact this rfl
  have hrpost : r ∉ post := fun h' => by
    have := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
    exact this h'
  have hposr : H.pos r = pre.length := by
    simp only [Config.pos, hsplit, List.idxOf_append_of_notMem hrpre, List.idxOf_cons_self,
      add_zero]
  have hpre : ∀ x ∈ pre, x ∉ H.del r s := by
    intro x hx hd
    have h1 := (mem_del.mp hd).2.2.1
    have h2 : H.pos x < pre.length := by
      simp only [Config.pos, hsplit, List.idxOf_append_of_mem hx]
      exact List.idxOf_lt_length_of_mem hx
    omega
  have hf1 : pre.filter (fun x => decide (x ∈ H.del r s)) = [] :=
    List.filter_eq_nil_iff.mpr fun x hx => by simpa using hpre x hx
  have hf2 : pre.filter (fun x => decide (x ∈ insert r (H.del r s))) = [] :=
    List.filter_eq_nil_iff.mpr fun x hx => by
      simp only [Finset.mem_insert, decide_eq_true_eq, not_or]
      exact ⟨fun h' => hrpre (h' ▸ hx), hpre x hx⟩
  have hrd : r ∉ H.del r s := fun h' => lt_irrefl _ (mem_del.mp h').2.2.1
  have hf3 : post.filter (fun x => decide (x ∈ insert r (H.del r s))) =
      post.filter (fun x => decide (x ∈ H.del r s)) :=
    List.filter_congr fun x hx => by
      have hxr : x ≠ r := fun h' => hrpost (h' ▸ hx)
      simp [hxr]
  unfold delList
  rw [hsplit, List.filter_append, List.filter_append, hf1, hf2, List.filter_cons,
    List.filter_cons, hf3]
  simp [hrd]

/-- A predicate false at `0` and true at `j` switches on between two consecutive indices. -/
theorem exists_switch (Qp : ℕ → Prop) {j : ℕ} (h0 : ¬ Qp 0) (hj : Qp j) :
    ∃ i, i < j ∧ ¬ Qp i ∧ Qp (i + 1) := by
  induction j with
  | zero => exact absurd hj h0
  | succ j ih =>
    by_cases hq : Qp j
    · obtain ⟨i, hi, h1, h2⟩ := ih hq
      exact ⟨i, by omega, h1, h2⟩
    · exact ⟨j, by omega, hq, hj⟩


/-! ### Case 2: the revisit of `r₀` by `s₀` -/

/-- The facts at the revisit of `r₀` by `s₀` from `h` (with `c` the configuration of the call
`GetNext(c.G, Gt)`) that the loop of Algorithm 2 needs. -/
structure TauFacts (M : Model Q) (tie : Tie Q) (P : Program Q) (c : Config Q) (Gt : Graph Q)
    (r₀ s₀ : Ev Q) (h cτ : Config Q) : Prop where
  /-- the step is the revisit of `r₀` by `s₀` -/
  step : cτ = (h.add s₀ none none).revisitCfg r₀ s₀
  /-- `s₀ = next_P(h)` -/
  next : M.nextP P h.G = some s₀
  /-- the guards -/
  guard : RevGuard tie (h.add s₀ none none) r₀ s₀
  /-- the replay base is `G_p` -/
  base : (h.add s₀ none none).base r₀ s₀ = (prefixExt c.G Gt s₀).events
  /-- `h` is the canonical replay of `r₀` and `Deleted` from `G_p` -/
  replay : Replay tie P (prefixExt c.G Gt s₀) (r₀ :: (h.add s₀ none none).delList r₀ s₀) h.G
  /-- `c` is frozen in `h` -/
  frozen : ∀ x ∈ c.G.events, h.G.rf x = c.G.rf x
  /-- the invariant -/
  inv : h.Inv M P

/-- Case 2 of the forcing argument (A.19, "the test fails"): a sequence of algorithmic steps from
`c` (Case 2 of `GetNext(c.G, Gt)`: `r₀ = next_P(c.G)` reads `s₀ ∉ c` in `Gt`) that reaches a
configuration containing `Gt` performs, before it, the revisit of `r₀` by `s₀`; the facts
`TauFacts` hold there. Proof: `c` stays frozen (A.18); the first step adds `r₀` with a source in
`c` or `⊥` (`first_step_nr`); `r₀` stays right after `c` and changes its source only by revisits
(`after_frozen_step`), so some step switches it to `s₀`; after it `s₀` is protected (A.17), so its
causal past and the sources there are those of `Gt` (`StepSeq.prot_frozen`, `Sub.porf_of`); the
replay base is `G_p`, and `revCond_iff_replay` (M5) gives the replay. -/
theorem case2_tau (hT : TieQ9 M tie) {c d : Config Q} {Gt : Graph Q} {r₀ s₀ : Ev Q}
    {πs : List (Config Q)} (hx : Ctx M P c Gt r₀ s₀) (h : StepSeq M tie P c πs d) {j : ℕ}
    (hj : j ≤ πs.length) (hsub : Sub Gt (pt c πs j).G) :
    ∃ i, i < j ∧ TauFacts M tie P c Gt r₀ s₀ (pt c πs i) (pt c πs (i + 1)) := by
  have hd := hx.dom
  have hc := hd.inv
  have hGt : Gt.Wf := hd.pfx.wf'
  have hcGt : c.G.events ⊆ Gt.events := hd.pfx.events_subset
  have hr₀c := hx.r₀_not_mem_c₀
  have hs₀c := hx.nmem
  obtain ⟨hs₀Gt, hs₀S, hr₀R, -⟩ := hx.facts
  -- `c` stays frozen up to `j` (A.18)
  have hfin : ∀ x ∈ c.G.events, (pt c πs j).G.rf x = c.G.rf x := fun x hx' =>
    (hsub x (hcGt hx')).2.1.trans (hd.pfx.rf_eq hx').symm
  have hA18 := no_revisit_of_prefix' hT hc (h.segment_take hj) hfin
  have hfrz : ∀ i ≤ j, Frozen c.order.length c (pt c πs i) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact frozen_refl _ c
    · obtain ⟨h1, h2⟩ := hA18 _ (StepSeq.pt_mem_take hi0 hi hj)
      refine ⟨by rwa [List.take_length], fun y hy => ?_⟩
      rw [List.take_length] at hy
      exact h2 y ((hc.mem y).mp hy)
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with rfl | h'
    · exact absurd (hsub r₀ hd.mem).1 hr₀c
    · exact h'
  -- the first step adds `r₀` with a source in `c` or `⊥`
  obtain ⟨e, src, out, hnr, h1eq⟩ := first_step_nr hc (h.step' (i := 0) (by omega))
    (fun y hy => ((hfrz 1 hj1).2 y (by rw [List.take_length]; exact (hc.mem y).mpr hy)).1)
  have he : e = r₀ := Option.some.inj (hnr.1.symm.trans hd.next)
  subst he
  have hsrc' : src ≠ some (.snd s₀) := by
    rintro rfl
    rcases hnr.2 with ⟨-, -, -, -, h', -⟩ | ⟨-, -, hs', -⟩ | ⟨-, h', -⟩ | ⟨-, h', -⟩
    · cases h'
    · rcases hs' with h' | ⟨s, hs, h'⟩
      · cases h'
      · cases h'
        exact hs₀c ((Graph.mem_S _).mp hs).1
    · cases h'
    · cases h'
  -- `r₀` stays right after `c`
  have hJ : ∀ i, 1 ≤ i → i ≤ j → AfterJ c e src out (pt c πs i) := by
    intro i hi1 hij
    induction i, hi1 using Nat.le_induction with
    | base =>
      have : pt c πs 1 = c.add e src out := h1eq
      rw [this]
      exact ⟨List.prefix_refl _, by simp [Config.add], Or.inl (by simp [Config.add])⟩
    | succ i hi ih =>
      exact after_frozen_step hc (h.step' (by omega)) (h.pt_inv hc (by omega))
        (hfrz i (by omega)) (hfrz (i + 1) hij) (ih (by omega))
  -- some step switches the source of `r₀` to `s₀`
  let Qp : ℕ → Prop := fun k => (pt c πs (k + 1)).G.rf e = some (.snd s₀)
  have hQ0 : ¬ Qp 0 := by
    intro hq
    have : pt c πs (0 + 1) = c.add e src out := h1eq
    simp only [Qp, this, Config.add, add_rf, Function.update_self] at hq
    exact hsrc' hq
  have hQj : Qp (j - 1) := by
    simp only [Qp]
    rw [show j - 1 + 1 = j by omega]
    exact (hsub e hd.mem).2.1.trans hx.src
  obtain ⟨k, hk, hnq, hq⟩ := exists_switch Qp hQ0 hQj
  refine ⟨k + 1, by omega, ?_⟩
  have hiπ : k + 1 < πs.length := by omega
  have hai := h.pt_inv hc (i := k + 1) (by omega)
  have hbi := h.pt_inv hc (i := k + 1 + 1) (by omega)
  have hstep := h.step' hiπ
  have hJi := hJ (k + 1) (by omega) (by omega)
  have hfrzi := hfrz (k + 1) (by omega)
  obtain ⟨S₂, hS₂⟩ := h.segment (i := k + 1 + 1) (k := j) (by omega) hj
  simp only [Qp] at hnq hq
  generalize hA : pt c πs (k + 1) = a at hai hstep hJi hfrzi hnq
  generalize hB : pt c πs (k + 1 + 1) = b at hbi hstep hq hS₂
  have hr₀a : e ∈ a.G.events := (hai.mem e).mp (hJi.1.subset (by simp))
  cases hstep with
  | @nr e' src' out' hnr' =>
    exfalso
    obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hnr'.1
    have he'A := hai.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv ht)
    have hee' : e ≠ e' := fun h' => he'A (h' ▸ hr₀a)
    simp only [Config.add, add_rf, Function.update_of_ne hee'] at hq
    exact hnq hq
  | @revisit e' r' hn hS hg hcons =>
    set H := a.add e' none none with hHdef
    have hr₀b : e ∈ ((a.add e' none none).revisitCfg r' e').G.events :=
      (hbi.wf.rf_some hq).1
    have hr₀d := (mem_revisitCfg_events.mp hr₀b).2
    rw [revisitCfg_rf (Finset.mem_insert_of_mem hr₀a) hr₀d] at hq
    split_ifs at hq with her
    swap
    · exfalso
      change Function.update a.G.rf e' none e = _ at hq
      rw [Function.update_of_ne (fun (h' : e = e') => (hai.wf.not_mem_of_idx_eq_cnt
        (Model.idx_of_nextEv (exists_nextEv_of_nextP hn).choose_spec)) (h' ▸ hr₀a))] at hq
      exact hnq hq
    subst her
    have he's : e' = s₀ := by
      have := Option.some.inj hq
      exact Src.snd.inj this
    subst he's
    obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hn
    have hs₀a := hai.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv ht)
    have hHi : H.Inv M P := hai.addSend ht hS
    obtain ⟨hs₀H, hread, -⟩ := addSend_facts hai ht
    -- `s₀` is protected from the revisit on; its causal past is that of `Gt`
    have hprot : ((a.add e' none none).revisitCfg e e').Prot e' :=
      StepM.revisit_prot hai hn hS hg
    have hre : e ≠ e' := fun h' => Lab.IsSend.not_isRecv hS (h' ▸ hg.recv)
    have hbj := h.pt_inv hc (i := j) hj
    obtain ⟨hpo, hrfnd⟩ := hS₂.prot_frozen hT hbi hprot
    have hporfGt : ∀ y, ((a.add e' none none).revisitCfg e e').G.porf y e' ↔ Gt.porf y e' :=
      fun y => (hpo y).trans
        ⟨fun h' => hsub.porf_of hGt hbj.wf h' hs₀Gt, fun h' => hsub.porf_to h'⟩
    -- positions: `c`, then `r₀`
    have hpreH : c.order ++ [e] <+: H.order := prefix_add hJi.1
    have hcH : c.order <+: H.order := (List.prefix_append _ _).trans hpreH
    have hposr : H.pos e = c.order.length := by
      have h1 := pos_lt_of_prefix hpreH (List.mem_append_right _ (List.mem_singleton_self e))
      have h2 := le_pos_of_prefix hcH (fun h' => hr₀c ((hc.mem e).mp h'))
      simp at h1
      omega
    -- the replay base is `G_p`
    have hbase : H.base e e' = (prefixExt c.G Gt e').events := by
      ext x
      rw [mem_base, mem_prefixExt hcGt]
      constructor
      · rintro ⟨hxH, hxr, hxs, hxd⟩
        by_cases hxc : x ∈ c.order
        · exact Or.inl ((hc.mem x).mp hxc)
        · right
          have hle := le_pos_of_prefix hcH hxc
          have hne : H.pos x ≠ H.pos e := fun h' => hxr ((pos_inj ((hHi.mem x).mpr hxH)).mp h')
          have hpx : H.G.porf x e' := by
            by_contra hn'
            exact hxd (mem_del.mpr ⟨hxH, hxs, by omega, hn'⟩)
          have := (hporfGt x).mp (porf_revisit_to_s hHi hg hs₀H hpx)
          exact ⟨(hGt.mem_of_porf this).1, this⟩
      · rintro (hxc | ⟨-, hxp⟩)
        · have hxo : x ∈ c.order := (hc.mem x).mpr hxc
          have hxH : x ∈ H.G.events := (hHi.mem x).mp (hcH.subset hxo)
          refine ⟨hxH, fun h' => hr₀c (h' ▸ hxc), fun h' => hs₀c (h' ▸ hxc), fun hd => ?_⟩
          have h1 := pos_lt_of_prefix hcH hxo
          have h2 := (mem_del.mp hd).2.2.1
          omega
        · have hb' := (hporfGt x).mpr hxp
          have hxb := (hbi.wf.mem_of_porf hb').1
          obtain ⟨hxH, hxd⟩ := mem_revisitCfg_events.mp hxb
          refine ⟨hxH, ?_, ?_, hxd⟩
          · rintro rfl
            exact hbi.wf.porf_irrefl _ (hb'.tail (Or.inr (revisitCfg_bwRead hHi hg hre).1))
          · rintro rfl
            exact hbi.wf.porf_irrefl _ hb'
    -- sources and outcomes on the base are those of `Gt`
    have hsrcs : ∀ x ∈ H.base e e', H.G.rf x = Gt.rf x ∧ H.G.nd x = Gt.nd x := by
      intro x hxb
      obtain ⟨hxH, hxr, hxs, hxd⟩ := mem_base.mp hxb
      have hHa : H.G.rf x = a.G.rf x ∧ H.G.nd x = a.G.nd x := by
        refine ⟨?_, ?_⟩
        · change Function.update a.G.rf e' none x = _
          rw [Function.update_of_ne hxs]
        · change Function.update a.G.nd e' none x = _
          rw [Function.update_of_ne hxs]
      rw [hHa.1, hHa.2]
      rcases (mem_prefixExt hcGt).mp (hbase ▸ hxb) with hxc | ⟨-, hxp⟩
      · have hxt : x ∈ c.order.take c.order.length := by
          rw [List.take_length]
          exact (hc.mem x).mpr hxc
        obtain ⟨h1, h2⟩ := hfrzi.2 x hxt
        exact ⟨h1.trans (hd.pfx.rf_eq hxc), h2.trans (hd.pfx.nd_eq hxc)⟩
      · have hb' := (hporfGt x).mpr hxp
        obtain ⟨h1, h2⟩ := hrfnd x (Or.inr hb')
        have h3 := hsub x (hGt.mem_of_porf hxp).1
        have h4 : ((a.add e' none none).revisitCfg e e').G.rf x = a.G.rf x := by
          rw [revisitCfg_rf hxH hxd, ite_eq_right hxr]
          exact hHa.1
        have h5 : ((a.add e' none none).revisitCfg e e').G.nd x = a.G.nd x := by
          rw [revisitCfg_nd hxH hxd]
          exact hHa.2
        exact ⟨h4.symm.trans (h1.symm.trans h3.2.1), h5.symm.trans (h2.symm.trans h3.2.2)⟩
    have hGpS : (prefixExt c.G Gt e').Supp := hx.gp_right.wf.supp
    have hgraph : H.G.restrict (H.base e e') = prefixExt c.G Gt e' := by
      have hbaseH : H.base e e' ⊆ H.G.events := fun x hx' => (mem_base.mp hx').1
      apply Graph.ext
      · rw [restrict_events, Finset.inter_eq_right.mpr hbaseH, hbase]
      · funext x
        rw [restrict_rf]
        split_ifs with hxb
        · rw [(hsrcs x hxb).1, prefixExt_rf (hbase ▸ hxb)]
        · exact ((hGpS x (hbase ▸ hxb)).1).symm
      · funext x
        rw [restrict_nd]
        split_ifs with hxb
        · rw [(hsrcs x hxb).2, prefixExt_nd (hbase ▸ hxb)]
        · exact ((hGpS x (hbase ▸ hxb)).2).symm
    -- the replay (M5)
    have hlast : ∀ x ∈ H.G.events, x ≠ e' → H.pos x < H.pos e' := by
      intro x hx' hxs
      have hxa : x ∈ a.order := by
        refine (hai.mem x).mpr ?_
        have : x ∈ insert e' a.G.events := hx'
        exact (Finset.mem_insert.mp this).resolve_left hxs
      have hsa : e' ∉ a.order := fun h' => hs₀a ((hai.mem e').mp h')
      simp only [H, Config.pos, Config.add, List.idxOf_append_of_mem hxa,
        List.idxOf_append_of_notMem hsa, List.idxOf_cons_self, add_zero]
      exact List.idxOf_lt_length_of_mem hxa
    have hrep := ((revCond_iff_replay hT hHi hs₀H hS hread hlast hg.mem hg.recv
      hg.nporf).mp hg.cond).2
    have hrem : H.G.remove {e'} = a.G := hai.wf.remove_add (Model.idx_of_nextEv ht)
    rw [hgraph, hrem] at hrep
    refine ⟨rfl, hn, hg, hbase, hrep, fun x hx' => ?_, hai⟩
    exact (hfrzi.2 x (by rw [List.take_length]; exact (hc.mem x).mpr hx')).1


/-! ### Helpers for the forcing argument -/

/-- The event added by a step is in the successor. -/
theorem StepM.next_mem {a b : Config Q} {e : Ev Q} (h : StepM M tie P a b)
    (hn : M.nextP P a.G = some e) : e ∈ b.G.events := by
  cases h with
  | @nr e' src out hnr =>
    cases Option.some.inj (hn.symm.trans hnr.1)
    exact Finset.mem_insert_self _ _
  | @revisit e' r hn' hS hg hcons =>
    cases Option.some.inj (hn.symm.trans hn')
    exact mem_revisitCfg_events.mpr ⟨Finset.mem_insert_self _ _,
      fun h' => (mem_del.mp h').2.1 rfl⟩

/-- A sequence from `c` whose configuration at index `j ≥ 1` has the sources of `c` keeps `c`
frozen up to `j`; its first step adds `next_P(c.G)` by a non-revisit step, and that event stays
right after `c` (`AfterJ`). -/
theorem next_after_frozen (hT : TieQ9 M tie) {c d : Config Q} {πs : List (Config Q)}
    (hc : c.Inv M P) (h : StepSeq M tie P c πs d) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ πs.length)
    (hfin : ∀ x ∈ c.G.events, (pt c πs j).G.rf x = c.G.rf x) {e : Ev Q}
    (hn : M.nextP P c.G = some e) :
    ∃ src out, NrAdd M P c.G e src out ∧ pt c πs 1 = c.add e src out ∧
      AfterJ c e src out (pt c πs j) := by
  have hA18 := no_revisit_of_prefix' hT hc (h.segment_take hj) hfin
  have hfrz : ∀ i ≤ j, Frozen c.order.length c (pt c πs i) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact frozen_refl _ c
    · obtain ⟨h1, h2⟩ := hA18 _ (StepSeq.pt_mem_take hi0 hi hj)
      refine ⟨by rwa [List.take_length], fun y hy => ?_⟩
      rw [List.take_length] at hy
      exact h2 y ((hc.mem y).mp hy)
  obtain ⟨e', src, out, hnr, h1eq⟩ := first_step_nr hc (h.step' (i := 0) (by omega))
    (fun y hy => ((hfrz 1 hj1).2 y (by rw [List.take_length]; exact (hc.mem y).mpr hy)).1)
  have he : e' = e := Option.some.inj (hnr.1.symm.trans hn)
  subst he
  have hJ : ∀ i, 1 ≤ i → i ≤ j → AfterJ c e' src out (pt c πs i) := by
    intro i hi1 hij
    induction i, hi1 using Nat.le_induction with
    | base =>
      have : pt c πs 1 = c.add e' src out := h1eq
      rw [this]
      exact ⟨List.prefix_refl _, by simp [Config.add], Or.inl (by simp [Config.add])⟩
    | succ i hi ih =>
      exact after_frozen_step hc (h.step' (by omega)) (h.pt_inv hc (by omega))
        (hfrz i (by omega)) (hfrz (i + 1) hij) (ih (by omega))
  exact ⟨src, out, hnr, h1eq, hJ j hj1 le_rfl⟩

/-- The order prefix part of `next_after_frozen`. -/
theorem prefix_next_of_frozen (hT : TieQ9 M tie) {c d : Config Q} {πs : List (Config Q)}
    (hc : c.Inv M P) (h : StepSeq M tie P c πs d) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ πs.length)
    (hfin : ∀ x ∈ c.G.events, (pt c πs j).G.rf x = c.G.rf x) {e : Ev Q}
    (hn : M.nextP P c.G = some e) : c.order ++ [e] <+: (pt c πs j).order := by
  obtain ⟨_, _, _, _, hJ⟩ := next_after_frozen hT hc h hj1 hj hfin hn
  exact hJ.1

/-- A deferred list that is a prefix of `r₀ :: Deleted` gives a target contained in `h`. -/
theorem sub_of_tau (hT : TieQ9 M tie) {c₀ : Config Q} {Gt : Graph Q} {r₀ s₀ : Ev Q}
    {h cτ : Config Q} (hx : Ctx M P c₀ Gt r₀ s₀) (tau : TauFacts M tie P c₀ Gt r₀ s₀ h cτ)
    {A' : List (Ev Q)} {X' : Graph Q}
    (hX' : maxCompletion tie P (prefixExt c₀.G Gt s₀) A' = some X')
    (hpre : A' <+: r₀ :: (h.add s₀ none none).delList r₀ s₀) : Sub X' h.G := by
  obtain ⟨L₂, hL⟩ := hpre
  have hrep := tau.replay
  rw [← hL] at hrep
  obtain ⟨Z, h1, h2⟩ := Replay.split hrep
  have hGp := hx.gp_right
  have hZ : Z = X' := replay_det hT hGp.cons h1 (maxCompletion_replay hX')
  subst hZ
  have hZc := h1.consistent hT hGp.cons
  have hZe := h1.exec hT hGp.cons hGp.exec
  exact (h2.pfx hT hZc hZe).sub

/-- A deferred list is a prefix of `r₀ :: Deleted` when it is the filter of a prefix `L` of the
order of `h` by membership in `Deleted ∪ {r₀}`. -/
theorem prefix_delList {c₀ : Config Q} {Gt : Graph Q} {r₀ s₀ : Ev Q} {h cτ : Config Q}
    (hx : Ctx M P c₀ Gt r₀ s₀) (tau : TauFacts M tie P c₀ Gt r₀ s₀ h cτ)
    {L A' : List (Ev Q)} (hL : L <+: h.order)
    (hiff : ∀ x ∈ L, x ∈ insert r₀ ((h.add s₀ none none).del r₀ s₀) ↔ x ∈ A')
    (hfilt : L.filter (fun x => decide (x ∈ A')) = A') :
    A' <+: r₀ :: (h.add s₀ none none).delList r₀ s₀ := by
  set H := h.add s₀ none none with hHdef
  obtain ⟨t, ht⟩ := exists_nextEv_of_nextP tau.next
  have hHi : H.Inv M P := tau.inv.addSend ht hx.facts.2.1
  rw [cons_delList hHi tau.guard.mem]
  obtain ⟨R, hR⟩ := hL
  have hs₀ : s₀ ∉ insert r₀ (H.del r₀ s₀) := by
    rw [Finset.mem_insert, not_or]
    exact ⟨hx.facts.2.2.2, fun h' => (mem_del.mp h').2.1 rfl⟩
  have hHo : H.order = L ++ (R ++ [s₀]) := by
    simp only [H, Config.add, ← hR, List.append_assoc]
  rw [hHo, List.filter_append]
  have : L.filter (fun x => decide (x ∈ insert r₀ (H.del r₀ s₀))) = A' := by
    rw [← hfilt]
    exact List.filter_congr fun x hx' => by simp only [hiff x hx']
  rw [this]
  exact List.prefix_append _ _

omit [DecidableEq Q] [Membership Val Q] in
theorem pt_succ_eq {c : Config Q} {πs : List (Config Q)} {i : ℕ} (hi : i < πs.length) :
    pt c πs (i + 1) = πs[i] := by
  rw [pt_eq hi]
  rfl

omit [DecidableEq Q] [Membership Val Q] in
theorem take_succ_pt {c : Config Q} {πs : List (Config Q)} {i : ℕ} (hi : i < πs.length) :
    πs.take i ++ [pt c πs (i + 1)] = πs.take (i + 1) := by
  rw [pt_succ_eq hi, List.take_add_one, List.getElem?_eq_getElem hi]
  rfl

omit [DecidableEq Q] [Membership Val Q] in
theorem pt_append {c c₁ : Config Q} {S πs : List (Config Q)}
    (hc₁ : pt c (S ++ πs) S.length = c₁) {i : ℕ} (hi : i ≤ πs.length) :
    pt c (S ++ πs) (S.length + i) = pt c₁ πs i := by
  rcases i with _ | i
  · simpa using hc₁
  · rw [pt_eq (by simp; omega), pt_eq hi]
    have e1 : (c :: (S ++ πs))[S.length + (i + 1)]'(by simp; omega) =
        (S ++ πs)[S.length + i]'(by simp; omega) := rfl
    rw [e1, List.getElem_append_right (by omega)]
    simp


/-- The membership in `Deleted ∪ {r₀}` of an event of a loop state `c` is membership in the
deferred list. -/
theorem loopInv_mem_iff {c₀ : Config Q} {Gt : Graph Q} {r₀ s₀ : Ev Q} {c h cτ : Config Q}
    {A : List (Ev Q)} {X : Graph Q} (hx : Ctx M P c₀ Gt r₀ s₀)
    (hI : LoopInv M tie P c₀ Gt r₀ s₀ c A X) (tau : TauFacts M tie P c₀ Gt r₀ s₀ h cτ)
    (hch : c.order <+: h.order) {x : Ev Q} (hxc : x ∈ c.order) :
    x ∈ insert r₀ ((h.add s₀ none none).del r₀ s₀) ↔ x ∈ A := by
  have hxH : x ∈ (h.add s₀ none none).G.events :=
    Finset.mem_insert_of_mem ((tau.inv.mem x).mp (hch.subset hxc))
  rw [mem_insert_del_iff hxH (Ne.symm hx.facts.2.2.2), tau.base]
  have hxcE := (hI.inv.mem x).mp hxc
  constructor
  · rintro ⟨h1, -⟩
    rcases (hI.mem_X).mp (hI.pfx.events_subset hxcE) with h' | h'
    · exact absurd h' h1
    · exact h'
  · intro hA
    exact ⟨hI.disj x hA, fun h' => hI.ns₀ (h' ▸ hxcE)⟩

/-- The same for the first state of the loop, `c₀` with `A = []`. -/
theorem init_mem_iff {c₀ : Config Q} {Gt : Graph Q} {r₀ s₀ : Ev Q} {h cτ : Config Q}
    (hx : Ctx M P c₀ Gt r₀ s₀) (tau : TauFacts M tie P c₀ Gt r₀ s₀ h cτ)
    (hch : c₀.order <+: h.order) {x : Ev Q} (hxc : x ∈ c₀.order) :
    x ∈ insert r₀ ((h.add s₀ none none).del r₀ s₀) ↔ x ∈ ([] : List (Ev Q)) := by
  have hxH : x ∈ (h.add s₀ none none).G.events :=
    Finset.mem_insert_of_mem ((tau.inv.mem x).mp (hch.subset hxc))
  rw [mem_insert_del_iff hxH (Ne.symm hx.facts.2.2.2), tau.base]
  simp only [List.not_mem_nil, iff_false, not_and, not_not]
  exact fun h' => absurd (hx.gp_left.events_subset ((hx.dom.inv.mem x).mp hxc)) h'

/-! ### The forcing argument -/

/-- `S` is forced from `c` toward `Gt`: every sequence of algorithmic steps from `c` that
reaches a configuration containing `Gt` (same sources and outcomes) starts with `S`, and reaches
it not before the end of `S`. -/
def ForcedCall (M : Model Q) (tie : Tie Q) (P : Program Q) (c : Config Q) (Gt : Graph Q)
    (S : List (Config Q)) : Prop :=
  ∀ (πs : List (Config Q)) (d : Config Q), StepSeq M tie P c πs d →
    ∀ j ≤ πs.length, Sub Gt (pt c πs j).G → S <+: πs ∧ S.length ≤ j

/-- The loop of Algorithm 2 is forced: a sequence from a loop state that performs the revisit
of `r₀` by `s₀` from `h` (with the facts `TauFacts`) and keeps the state frozen up to `h` runs
exactly through the loop's steps and reaches `h` at the break. -/
def ForcedLoop (M : Model Q) (tie : Tie Q) (P : Program Q) (Gp : Graph Q) (s₀ : Ev Q)
    (c : Config Q) (A : List (Ev Q)) (S : List (Config Q)) (cL : Config Q) : Prop :=
  ∀ (c₀ : Config Q) (Gt : Graph Q) (r₀ : Ev Q), Ctx M P c₀ Gt r₀ s₀ →
    Gp = prefixExt c₀.G Gt s₀ →
    ((A = [] ∧ c = c₀) ∨ ∃ X, LoopInv M tie P c₀ Gt r₀ s₀ c A X) →
    ∀ (πs : List (Config Q)) (d : Config Q), StepSeq M tie P c πs d →
    ∀ jh < πs.length, TauFacts M tie P c₀ Gt r₀ s₀ (pt c πs jh) (pt c πs (jh + 1)) →
      (∀ x ∈ c.G.events, (pt c πs jh).G.rf x = c.G.rf x) →
      S = πs.take jh ∧ cL = pt c πs jh

/-- The forcing property of a task of Algorithm 2. -/
def Forced (M : Model Q) (tie : Tie Q) (P : Program Q) :
    Task Q → List (Config Q) → Config Q → Prop
  | .call c Gt, S, _ => ∀ e, CallDom M P c Gt e → ForcedCall M tie P c Gt S
  | .loop Gp s₀ c A, S, cL => ForcedLoop M tie P Gp s₀ c A S cL

/-- The common part of the `good` and `defer` cases: after the forced sub-call, the rest of the
sequence starts at the sub-call's result and the loop continues. -/
theorem loop_continue {c₀ : Config Q} {Gt : Graph Q} {r₀ s₀ : Ev Q} {c c₁ c₂ d : Config Q}
    {A' : List (Ev Q)} {X : Graph Q} {S₁ S₂ πs : List (Config Q)} (hx : Ctx M P c₀ Gt r₀ s₀)
    (hπ : StepSeq M tie P c (S₁ ++ πs) d) (hpath : StepSeq M tie P c S₁ c₁)
    (hpfx : Pfx M P c₁.G X) (hI₁ : LoopInv M tie P c₀ Gt r₀ s₀ c₁ A' X)
    {jh : ℕ} (hl : S₁.length ≤ jh) (hjh : jh < (S₁ ++ πs).length)
    (tau : TauFacts M tie P c₀ Gt r₀ s₀ (pt c (S₁ ++ πs) jh) (pt c (S₁ ++ πs) (jh + 1)))
    (hsubX : Sub X (pt c (S₁ ++ πs) jh).G)
    (ih₂ : ForcedLoop M tie P (prefixExt c₀.G Gt s₀) s₀ c₁ A' S₂ c₂) :
    S₁ ++ S₂ = (S₁ ++ πs).take jh ∧ c₂ = pt c (S₁ ++ πs) jh := by
  have hc₁ : pt c (S₁ ++ πs) S₁.length = c₁ := by
    rw [pt_eq (by simp)]
    exact hpath.getElem_of_prefix (List.prefix_append _ _)
  have hπ' : StepSeq M tie P c₁ πs d := by
    have := hπ.drop (i := S₁.length) (by simp)
    rw [← pt_eq (by simp), hc₁] at this
    simpa using this
  obtain ⟨jh', rfl⟩ : ∃ jh', jh = S₁.length + jh' := ⟨jh - S₁.length, by omega⟩
  have hjh' : jh' < πs.length := by simp at hjh; omega
  rw [pt_append hc₁ hjh'.le, show S₁.length + jh' + 1 = S₁.length + (jh' + 1) by omega,
    pt_append hc₁ hjh'] at tau
  rw [pt_append hc₁ hjh'.le] at hsubX ⊢
  have hfrz : ∀ x ∈ c₁.G.events, (pt c₁ πs jh').G.rf x = c₁.G.rf x := fun x hx' =>
    (hsubX x (hpfx.events_subset hx')).2.1.trans (hpfx.rf_eq hx').symm
  obtain ⟨h1, h2⟩ := ih₂ c₀ Gt r₀ hx rfl (Or.inr ⟨X, hI₁⟩) πs d hπ' jh' hjh' tau hfrz
  refine ⟨?_, h2⟩
  rw [h1, List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

/-- **The forcing theorem** (A.19's induction, repaired and completed): every derivation of
Algorithm 2 is forced. For a call `GetNext(c.G, Gt)` on its domain: every sequence of
algorithmic steps from `c` that reaches a configuration containing `Gt` starts with the steps
returned by `GetNext`. For every model, every tie-break with Q9, every bounded program. -/
theorem getNext_forced (hT : TieQ9 M tie) {n : ℕ} (hb : P.Bounded n) {t : Task Q}
    {S : List (Config Q)} {cL : Config Q} (h : GetNext M tie P t S cL) : Forced M tie P t S cL := by
  induction h with
  | @case1 c Gt e src out hn hop hpf =>
    intro e₁ hd πs d hπ j hj hsub
    have hc := hd.inv
    have heA := hc.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv (nextEv_of_nextP hn))
    have heGt : e ∈ Gt.events := hpf.events_subset (Finset.mem_insert_self _ _)
    have hcGt := hd.pfx.events_subset
    have hfin : ∀ x ∈ c.G.events, (pt c πs j).G.rf x = c.G.rf x := fun x hx' =>
      (hsub x (hcGt hx')).2.1.trans (hd.pfx.rf_eq hx').symm
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | h'
      · exact absurd (hsub e heGt).1 heA
      · exact h'
    obtain ⟨src₁, out₁, -, h1eq, hJ⟩ := next_after_frozen hT hc hπ hj1 hj hfin hn
    have hsrc : src = Gt.rf e := by
      have := hpf.rf_eq (Finset.mem_insert_self e c.G.events)
      simpa using this
    have hout : out = Gt.nd e := by
      have := hpf.nd_eq (Finset.mem_insert_self e c.G.events)
      simpa using this
    have hout₁ : out₁ = out := hJ.2.1.symm.trans ((hsub e heGt).2.2.trans hout.symm)
    have hsrc₁ : src₁ = src := by
      rcases hJ.2.2 with h' | ⟨t, ht, htc⟩
      · exact h'.symm.trans ((hsub e heGt).2.1.trans hsrc.symm)
      · exfalso
        have hGt := (hsub e heGt).2.1
        rw [ht] at hGt
        have hpw := hpf.wf
        have h2 : (c.G.add e src out).rf e = some (.snd t) := by
          rw [hpf.rf_eq (Finset.mem_insert_self _ _)]
          exact hGt.symm
        have htm := hpw.rf_mem _ _ h2
        have hte : t ≠ e := by
          rintro rfl
          exact Lab.IsSend.not_isRecv (hpw.rf_match _ _ h2).isSend (hpw.rf_some h2).2
        exact htc ((Finset.mem_insert.mp htm).resolve_left hte)
    subst hout₁ hsrc₁
    rcases πs with _ | ⟨y, ys⟩
    · simp at hj; omega
    · have hy : y = c.add e src₁ out₁ := h1eq
      subst hy
      exact ⟨⟨ys, rfl⟩, by simpa using hj1⟩
  | @case2 c Gt r₀ s₀ S c₁ hn hnt hs hloop ih =>
    intro e₁ hd πs d hπ j hj hsub
    have he₁ : e₁ = r₀ := Option.some.inj (hd.next.symm.trans hn)
    subst he₁
    have hs₀c : s₀ ∉ c.G.events := fun h' =>
      hnt ((case1_iff hd.pfx (nextEv_of_nextP hn) hd.mem).mpr fun s hs' => by
        rw [hs] at hs'
        cases hs'
        exact h')
    have hx : Ctx M P c Gt e₁ s₀ := ⟨hd, hs, hs₀c⟩
    obtain ⟨i, hij, tau⟩ := case2_tau hT hx hπ hj hsub
    have hiπ : i < πs.length := by omega
    have ih' : ForcedLoop M tie P (prefixExt c.G Gt s₀) s₀ c [] S c₁ := ih
    obtain ⟨h1, h2⟩ := ih' c Gt e₁ hx rfl (Or.inl ⟨rfl, rfl⟩) πs d hπ i hiπ tau tau.frozen
    subst h1 h2
    rw [← tau.step, take_succ_pt hiπ]
    exact ⟨List.take_prefix _ _, by simp; omega⟩
  | @brk Gp s₀ c A hn ht =>
    intro c₀ Gt r₀ hx hGp hst πs d hπ jh hjh tau hfrz
    subst hGp
    rcases hst with ⟨-, rfl⟩ | ⟨X, hI⟩
    · exact absurd (Option.some.inj (hx.dom.next.symm.trans hn)) (Ne.symm hx.facts.2.2.2)
    have hcX := hI.eq_of_brk hx hT hn
    have hGpc : (prefixExt c₀.G Gt s₀).events ⊆ c.G.events := by
      rw [hcX]
      exact (hI.gp_pfx hx hT).events_subset
    have hc := hI.inv
    by_contra hne
    have hjh1 : 1 ≤ jh := by
      rcases Nat.eq_zero_or_pos jh with rfl | h'
      · exact (hne ⟨by simp, rfl⟩).elim
      · exact h'
    have hA18 := no_revisit_of_prefix' hT hc (hπ.segment_take hjh.le) hfrz
    have hs₁ : s₀ ∈ (pt c πs 1).G.events := (hπ.step' (i := 0) (by omega)).next_mem hn
    have hsh : s₀ ∉ (pt c πs jh).G.events :=
      tau.inv.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv (nextEv_of_nextP tau.next))
    let Qp : ℕ → Prop := fun k => s₀ ∉ (pt c πs (k + 1)).G.events
    have hQ0 : ¬ Qp 0 := fun h' => h' hs₁
    have hQj : Qp (jh - 1) := by
      simp only [Qp]
      rw [show jh - 1 + 1 = jh by omega]
      exact hsh
    obtain ⟨k, hk, hnq, hq⟩ := exists_switch Qp hQ0 hQj
    simp only [Qp, not_not] at hnq hq
    have hkπ : k + 1 < πs.length := by omega
    have hai := hπ.pt_inv hc (i := k + 1) (by omega)
    have hstep := hπ.step' hkπ
    obtain ⟨S₂, hS₂⟩ := hπ.segment (i := k + 1 + 1) (k := jh) (by omega) hjh.le
    have hck : c.order <+: (pt c πs (k + 1)).order :=
      (hA18 _ (StepSeq.pt_mem_take (by omega) (by omega) hjh.le)).1
    generalize hA : pt c πs (k + 1) = a at hai hstep hnq hck
    generalize hB : pt c πs (k + 1 + 1) = b at hstep hq hS₂
    cases hstep with
    | @nr e' src' out' hnr' => exact hq (Finset.mem_insert_of_mem hnq)
    | @revisit e' r' hn' hS hg hcons =>
      obtain ⟨t, ht'⟩ := exists_nextEv_of_nextP hn'
      have he'a := hai.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv ht')
      have hbi := (StepM.revisit hn' hS hg hcons).inv hai
      have hprot := StepM.revisit_prot hai hn' hS hg
      obtain ⟨-, he'h, hph⟩ := hS₂.prot hT hbi hprot
      obtain ⟨t₂, ht₂⟩ := exists_nextEv_of_nextP tau.next
      have hhe := tau.inv.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv ht₂)
      have hHi := tau.inv.addSend ht₂ hx.facts.2.1
      obtain ⟨-, hread, -⟩ := addSend_facts tau.inv ht₂
      have hnd := prot_not_del hHi tau.guard hread (hph.add tau.inv hhe)
      have he'base : e' ∈ ((pt c πs jh).add s₀ none none).base r₀ s₀ :=
        mem_base.mpr ⟨Finset.mem_insert_of_mem he'h,
          fun h' => Lab.IsSend.not_isRecv hS (h' ▸ hx.facts.2.2.1),
          fun h' => hsh (h' ▸ he'h), hnd⟩
      rw [tau.base] at he'base
      exact he'a ((hai.mem e').mp (hck.subset ((hc.mem e').mpr (hGpc he'base))))
  | @good Gp s₀ c A e X S₁ c₁ S₂ c₂ hn hne ht hX h₁ h₂ ih₁ ih₂ =>
    intro c₀ Gt r₀ hx hGp hst πs d hπ jh hjh tau hfrz
    subst hGp
    have heGp : e ∈ (prefixExt c₀.G Gt s₀).events := ht.2.resolve_right hne
    rcases hst with ⟨-, rfl⟩ | ⟨X₀, hI⟩
    · have : e = r₀ := Option.some.inj (hn.symm.trans hx.dom.next)
      exact absurd (this ▸ heGp) hx.r₀_not_mem
    have hX₀ : X₀ = X := Option.some.inj (hI.mc.symm.trans hX)
    subst hX₀
    have hc := hI.inv
    have hdom : CallDom M P c X₀ e := ⟨hc, hI.pfx, hn, (hI.gp_pfx hx hT).events_subset heGp⟩
    have hjh1 : 1 ≤ jh := by
      rcases Nat.eq_zero_or_pos jh with rfl | h'
      · exact absurd (Option.some.inj (hn.symm.trans tau.next)) hne
      · exact h'
    have hcpre := prefix_next_of_frozen hT hc hπ hjh1 hjh.le hfrz hn
    have hcpre' : c.order <+: (pt c πs jh).order := (List.prefix_append _ _).trans hcpre
    have hsubX : Sub X₀ (pt c πs jh).G :=
      sub_of_tau hT hx tau hX (prefix_delList hx tau hcpre'
        (fun x hxc => loopInv_mem_iff hx hI tau hcpre' hxc) hI.filt)
    have ih₁' : ForcedCall M tie P c X₀ S₁ := ih₁ e hdom
    obtain ⟨⟨πs', rfl⟩, hl₁⟩ := ih₁' πs d hπ jh hjh.le hsubX
    have hspec := getNext_spec hT hb hdom h₁
    have hI₁ : LoopInv M tie P c₀ Gt r₀ s₀ c₁ A X₀ :=
      loopInv_of_call hx hc hI.nodup hI.sub hI.disj hI.filt hI.base
        (hI.ord.trans (List.prefix_append _ _)) hn (Or.inl ⟨rfl, heGp⟩) hI.head
        (fun h' => hI.ns₀ (hI.sub _ h')) hI.mc hspec
    exact loop_continue hx hπ hspec.path hspec.pfx hI₁ hl₁ hjh tau hsubX ih₂
  | @defer Gp s₀ c A e X S₁ c₁ S₂ c₂ hn hnt hX h₁ h₂ ih₁ ih₂ =>
    intro c₀ Gt r₀ hx hGp hst πs d hπ jh hjh tau hfrz
    subst hGp
    have hGp := hx.gp_right
    have hGpX : Pfx M P (prefixExt c₀.G Gt s₀) X := maxCompletion_pfx hT hGp.cons hGp.exec hX
    have heX : e ∈ X.events := by
      rw [(maxCompletion_replay hX).events]
      simp
    -- facts on the state
    obtain ⟨hc, heGp, hes, hcX, hmem, hfilt0, hI₁⟩ : c.Inv M P ∧
        e ∉ (prefixExt c₀.G Gt s₀).events ∧ e ≠ s₀ ∧ Pfx M P c.G X ∧
        (∀ x, c.order <+: (pt c πs jh).order → x ∈ c.order →
          (x ∈ insert r₀ (((pt c πs jh).add s₀ none none).del r₀ s₀) ↔ x ∈ A)) ∧
        c.order.filter (fun x => decide (x ∈ A)) = A ∧
        (∀ (hspec : CallSpec M tie P c X e S₁ c₁),
          LoopInv M tie P c₀ Gt r₀ s₀ c₁ (A ++ [e]) X) := by
      rcases hst with ⟨rfl, rfl⟩ | ⟨X₀, hI⟩
      · have he : e = r₀ := Option.some.inj (hn.symm.trans hx.dom.next)
        subst he
        refine ⟨hx.dom.inv, hx.r₀_not_mem, Ne.symm hx.facts.2.2.2, hx.gp_left.trans hGpX,
          fun x hch hxc => init_mem_iff hx tau hch hxc, by simp, fun hspec => ?_⟩
        exact loopInv_of_call hx hx.dom.inv List.nodup_nil (by simp) (by simp) (by simp)
          hx.dom.inv.wf.isPrefixOf_refl (List.prefix_refl _) hn (Or.inr ⟨rfl, hx.r₀_not_mem⟩)
          ⟨[], rfl⟩ (by simpa using hx.facts.2.2.2) hX hspec
      · obtain ⟨h1, h2, -, Y, hY, hXY, -⟩ := hI.defer_facts hx hT hn hnt
        have hYX : Y = X := Option.some.inj (hY.symm.trans hX)
        subst hYX
        obtain ⟨A'', hA''⟩ := hI.head
        refine ⟨hI.inv, h1, h2, hI.pfx.trans hXY,
          fun x hch hxc => loopInv_mem_iff hx hI tau hch hxc, hI.filt, fun hspec => ?_⟩
        exact loopInv_of_call hx hI.inv hI.nodup hI.sub hI.disj hI.filt hI.base
          (hI.ord.trans (List.prefix_append _ _)) hn (Or.inr ⟨rfl, h1⟩)
          ⟨A'' ++ [e], by rw [hA'']; rfl⟩
          (by
            rw [List.mem_append, List.mem_singleton, not_or]
            exact ⟨fun h' => hI.ns₀ (hI.sub _ h'), fun h' => h2 h'.symm⟩) hX hspec
    have hdom : CallDom M P c X e := ⟨hc, hcX, hn, heX⟩
    have hjh1 : 1 ≤ jh := by
      rcases Nat.eq_zero_or_pos jh with rfl | h'
      · exact absurd (Option.some.inj (hn.symm.trans tau.next)) hes
      · exact h'
    have hcpre := prefix_next_of_frozen hT hc hπ hjh1 hjh.le hfrz hn
    have hcpre' : c.order <+: (pt c πs jh).order := (List.prefix_append _ _).trans hcpre
    have heo : e ∉ c.order := fun h' => (hc.wf.not_mem_of_idx_eq_cnt
      (Model.idx_of_nextEv (nextEv_of_nextP hn))) ((hc.mem e).mp h')
    have hiff : ∀ x ∈ c.order ++ [e],
        x ∈ insert r₀ (((pt c πs jh).add s₀ none none).del r₀ s₀) ↔ x ∈ A ++ [e] := by
      intro x hx'
      rcases List.mem_append.mp hx' with hxc | hxe
      · have hxe : x ≠ e := fun h' => heo (h' ▸ hxc)
        rw [hmem x hcpre' hxc]
        simp [hxe]
      · rw [List.mem_singleton] at hxe
        subst hxe
        have hxH : x ∈ ((pt c πs jh).add s₀ none none).G.events :=
          Finset.mem_insert_of_mem ((tau.inv.mem x).mp (hcpre.subset (by simp)))
        rw [mem_insert_del_iff hxH (Ne.symm hx.facts.2.2.2), tau.base]
        simp [heGp, hes]
    have hfilt : (c.order ++ [e]).filter (fun x => decide (x ∈ A ++ [e])) = A ++ [e] := by
      rw [List.filter_append]
      have : c.order.filter (fun x => decide (x ∈ A ++ [e])) =
          c.order.filter (fun x => decide (x ∈ A)) :=
        List.filter_congr fun x hx' => by
          have hxe : x ≠ e := fun h' => heo (h' ▸ hx')
          simp [hxe]
      rw [this, hfilt0]
      simp
    have hsubX : Sub X (pt c πs jh).G :=
      sub_of_tau hT hx tau hX (prefix_delList hx tau hcpre hiff hfilt)
    have ih₁' : ForcedCall M tie P c X S₁ := ih₁ e hdom
    obtain ⟨⟨πs', rfl⟩, hl₁⟩ := ih₁' πs d hπ jh hjh.le hsubX
    have hspec := getNext_spec hT hb hdom h₁
    exact loop_continue hx hπ hspec.path hspec.pfx (hI₁ hspec) hl₁ hjh tau hsubX ih₂

/-! ### Optimality -/

/-- The next event of a configuration with a step. -/
theorem StepM.exists_next {a b : Config Q} (h : StepM M tie P a b) :
    ∃ e, M.nextP P a.G = some e := by
  cases h with
  | @nr e src out hnr => exact ⟨e, hnr.1⟩
  | @revisit e r hn hS hg hcons => exact ⟨e, hn⟩

/-- A nonempty sequence of algorithmic steps never returns to the graph it started from. -/
theorem StepSeq.eq_nil_of_graph_eq (hT : TieQ9 M tie) {c d : Config Q} {πs : List (Config Q)}
    (hc : c.Inv M P) (h : StepSeq M tie P c πs d) (hG : d.G = c.G) : πs = [] := by
  by_contra hne
  have hlen : 1 ≤ πs.length := List.length_pos_iff.mpr hne
  have hd : pt c πs πs.length = d := h.pt_last
  obtain ⟨e, hn⟩ := (h.step' (i := 0) (by omega)).exists_next
  have hpre := prefix_next_of_frozen hT hc h hlen le_rfl
    (fun x _ => by rw [hd, hG]) hn
  rw [hd] at hpre
  have hed : e ∈ d.G.events := ((h.inv hc).1.mem e).mp (hpre.subset (by simp))
  rw [hG] at hed
  exact hc.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv (nextEv_of_nextP hn)) hed

/-- **Uniqueness of paths to a graph.** For a bounded program, every model and every tie-break
with Q9: from a configuration `c` with the invariant and `c.G ⊑ G`, any two sequences of
algorithmic steps that end in configurations with graph `G` are equal. Proof: iterate
`GetNext(c.G, G)` (Algorithm 2, M7) and the forcing theorem `getNext_forced`. -/
theorem stepSeq_unique_of_pfx (hT : TieQ9 M tie) {n : ℕ} (hb : P.Bounded n) {G : Graph Q} :
    ∀ (k : ℕ) (c : Config Q), P.threads.length * n - c.G.events.card = k → c.Inv M P →
      Pfx M P c.G G → ∀ {πs₁ πs₂ : List (Config Q)} {d₁ d₂ : Config Q},
      StepSeq M tie P c πs₁ d₁ → StepSeq M tie P c πs₂ d₂ → d₁.G = G → d₂.G = G → πs₁ = πs₂ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro c hk hc hp πs₁ πs₂ d₁ d₂ h₁ h₂ hG₁ hG₂
  by_cases heq : c.G = G
  · rw [h₁.eq_nil_of_graph_eq hT hc (hG₁.trans heq.symm),
      h₂.eq_nil_of_graph_eq hT hc (hG₂.trans heq.symm)]
  have hne₁ : πs₁ ≠ [] := by
    rintro rfl
    cases h₁
    exact heq hG₁
  have hlen₁ : 1 ≤ πs₁.length := List.length_pos_iff.mpr hne₁
  obtain ⟨e, hn⟩ := (h₁.step' (i := 0) (by omega)).exists_next
  have hd₁ : pt c πs₁ πs₁.length = d₁ := h₁.pt_last
  have hd₂ : pt c πs₂ πs₂.length = d₂ := h₂.pt_last
  have hfin₁ : ∀ x ∈ c.G.events, (pt c πs₁ πs₁.length).G.rf x = c.G.rf x := fun x hx' => by
    rw [hd₁, hG₁]
    exact (hp.rf_eq hx').symm
  have hpre := prefix_next_of_frozen hT hc h₁ hlen₁ le_rfl hfin₁ hn
  rw [hd₁] at hpre
  have heG : e ∈ G.events := by
    rw [← hG₁]
    exact ((h₁.inv hc).1.mem e).mp (hpre.subset (by simp))
  have hdom : CallDom M P c G e := ⟨hc, hp, hn, heG⟩
  obtain ⟨S, c', hgn, hspec⟩ := getNext_total hT hb hdom
  have hF : ForcedCall M tie P c G S := getNext_forced hT hb hgn e hdom
  have hsub₁ : Sub G (pt c πs₁ πs₁.length).G := by
    rw [hd₁, hG₁]
    exact fun x hx' => ⟨hx', rfl, rfl⟩
  have hsub₂ : Sub G (pt c πs₂ πs₂.length).G := by
    rw [hd₂, hG₂]
    exact fun x hx' => ⟨hx', rfl, rfl⟩
  obtain ⟨⟨ρ₁, rfl⟩, -⟩ := hF πs₁ d₁ h₁ _ le_rfl hsub₁
  obtain ⟨⟨ρ₂, rfl⟩, -⟩ := hF πs₂ d₂ h₂ _ le_rfl hsub₂
  have hc'₁ : pt c (S ++ ρ₁) S.length = c' := by
    rw [pt_eq (by simp)]
    exact hspec.path.getElem_of_prefix (List.prefix_append _ _)
  have hc'₂ : pt c (S ++ ρ₂) S.length = c' := by
    rw [pt_eq (by simp)]
    exact hspec.path.getElem_of_prefix (List.prefix_append _ _)
  have hρ₁ : StepSeq M tie P c' ρ₁ d₁ := by
    have := h₁.drop (i := S.length) (by simp)
    rw [← pt_eq (by simp), hc'₁] at this
    simpa using this
  have hρ₂ : StepSeq M tie P c' ρ₂ d₂ := by
    have := h₂.drop (i := S.length) (by simp)
    rw [← pt_eq (by simp), hc'₂] at this
    simpa using this
  have hc' := (hspec.path.inv hc).1
  have hlt : P.threads.length * n - c'.G.events.card < k := by
    have h1 := hspec.spfx.card_lt
    have h2 := card_le_of_bounded hc'.wf hc'.exec hb
    omega
  rw [ih _ hlt c' rfl hc' hspec.pfx hρ₁ hρ₂ hG₁ hG₂]

/-- **Optimality** (Theorem 4.1 (a), repaired; plan rows M8, M9 `ReachM.eq_of_abs_eq`): for a
bounded program, every model and every tie-break with Q9, two sequences of algorithmic steps
from the initial configuration that end in configurations with the same graph are equal, and so
are their ends. So no two reachable configurations have the same graph, and each is reached
along one sequence of configurations only. That one step is one branch of Algorithm 1 (the
computed successor list has no duplicates) is not stated here; it belongs to M9. -/
theorem optimality (hT : TieQ9 M tie) {n : ℕ} (hb : P.Bounded n) {S₁ S₂ : List (Config Q)}
    {c₁ c₂ : Config Q} (h₁ : StepSeq M tie P Config.init S₁ c₁)
    (h₂ : StepSeq M tie P Config.init S₂ c₂) (hG : c₁.G = c₂.G) : S₁ = S₂ ∧ c₁ = c₂ := by
  have hi : (Config.init : Config Q).Inv M P := Config.inv_init
  have hc₁ := (h₁.inv hi).1
  have hp : Pfx M P (Config.init : Config Q).G c₁.G :=
    Pfx.of_isPrefixOf hc₁.cons hc₁.exec (Graph.empty_isPrefixOf _)
  have hS := stepSeq_unique_of_pfx hT hb _ Config.init rfl hi hp h₁ h₂ rfl hG.symm
  subst hS
  exact ⟨rfl, h₁.pt_last.symm.trans h₂.pt_last⟩

/-- `ReachM.eq_of_abs_eq` (plan row M9): reachable configurations with the same graph are equal
(no graph is visited twice, Theorem 4.1 (a)). -/
theorem ReachM.eq_of_abs_eq (hT : TieQ9 M tie) {n : ℕ} (hb : P.Bounded n) {c₁ c₂ : Config Q}
    (h₁ : ReachM M tie P c₁) (h₂ : ReachM M tie P c₂) (hG : c₁.G = c₂.G) : c₁ = c₂ := by
  obtain ⟨S₁, hS₁⟩ := h₁.exists_stepSeq
  obtain ⟨S₂, hS₂⟩ := h₂.exists_stepSeq
  exact (optimality hT hb hS₁ hS₂ hG).2

/-- Every reachable configuration is reached along exactly one sequence of algorithmic steps
from the initial configuration. -/
theorem stepSeq_unique (hT : TieQ9 M tie) {n : ℕ} (hb : P.Bounded n) {S₁ S₂ : List (Config Q)}
    {c : Config Q} (h₁ : StepSeq M tie P Config.init S₁ c)
    (h₂ : StepSeq M tie P Config.init S₂ c) : S₁ = S₂ :=
  (optimality hT hb h₁ h₂ rfl).1

/-- **Theorem A.19** (`production_unique`), repaired: for a full consistent execution `G_f ∈ ⟦P⟧`
of a bounded program, there is exactly one sequence of algorithmic steps from the initial
configuration to a configuration with graph `G_f`, and it is `ProductionSequence(G_f)`. -/
theorem production_unique (hT : TieQ9 M tie) {n : ℕ} (hb : P.Bounded n) {Gf : Graph Q}
    (hG : M.Sem P Gf) :
    ∃ S c, ProdSeq M tie P Gf Config.init S c ∧ StepSeq M tie P Config.init S c ∧ c.G = Gf ∧
      ∀ S' c', StepSeq M tie P Config.init S' c' → c'.G = Gf → S' = S ∧ c' = c := by
  obtain ⟨S, c, h1, h2, h3, -⟩ := productionSequence_reaches hT hb hG
  exact ⟨S, c, h1, h2, h3, fun S' c' h' hG' => optimality hT hb h' h2 (hG'.trans h3.symm)⟩

/-- Predecessors are unique: two reachable configurations with a step to the same configuration
are equal. -/
theorem StepM.pred_unique (hT : TieQ9 M tie) {n : ℕ} (hb : P.Bounded n) {a₁ a₂ b : Config Q}
    (h₁ : ReachM M tie P a₁) (h₂ : ReachM M tie P a₂) (s₁ : StepM M tie P a₁ b)
    (s₂ : StepM M tie P a₂ b) : a₁ = a₂ := by
  obtain ⟨S₁, hS₁⟩ := h₁.exists_stepSeq
  obtain ⟨S₂, hS₂⟩ := h₂.exists_stepSeq
  have h := (optimality hT hb (hS₁.append (.single s₁)) (hS₂.append (.single s₂)) rfl).1
  have hl : S₁.length = S₂.length := by
    have := congrArg List.length h
    simpa using this
  have e₁ := hS₁.pt_last
  have e₂ := hS₂.pt_last
  have k₁ : pt Config.init (S₁ ++ [b]) S₁.length = a₁ := by
    rw [pt_eq (by simp), ← e₁, pt_eq le_rfl]
    have e : (Config.init :: (S₁ ++ [b]))[S₁.length]'(by simp; omega) =
        ((Config.init :: S₁) ++ [b])[S₁.length]'(by simp; omega) := rfl
    rw [e, List.getElem_append_left (by simp)]
  have k₂ : pt Config.init (S₂ ++ [b]) S₂.length = a₂ := by
    rw [pt_eq (by simp), ← e₂, pt_eq le_rfl]
    have e : (Config.init :: (S₂ ++ [b]))[S₂.length]'(by simp; omega) =
        ((Config.init :: S₂) ++ [b])[S₂.length]'(by simp; omega) := rfl
    rw [e, List.getElem_append_left (by simp)]
  rw [← k₁, ← k₂, h, hl]

end Must

#print axioms Must.revisit_send_persists
#print axioms Must.no_revisit_of_prefix
#print axioms Must.case2_tau
#print axioms Must.getNext_forced
#print axioms Must.stepSeq_unique_of_pfx
#print axioms Must.optimality
#print axioms Must.ReachM.eq_of_abs_eq
#print axioms Must.stepSeq_unique
#print axioms Must.production_unique
#print axioms Must.StepM.pred_unique
