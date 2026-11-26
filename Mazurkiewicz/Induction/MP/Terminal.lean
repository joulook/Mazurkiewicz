import Mazurkiewicz.Induction.MP.KInd
import Mazurkiewicz.Induction.Budgets

/-!
# Message passing: budget programs and terminal executions (milestone C7)

`induction-popl`, `mp.tex` def:terminal, prop:mp-cover, thm:mp-terminal, and `p2p.tex`
thm:p2p (2), (3), for the one construction over a setting `S` and an abstraction
`Abs : SAbs S A` (plan `plan/ind/TRACK-C-PLAN.md`, milestone C7). Budgets are Track A's
`Trust.IsBudget S.P.threads K κ` (`Induction/Budgets.lean`).

* `SAbs.budgetProg b κ` is `Q_b|κ`: `Q_b` truncated at `(W b t).length + κ t`, i.e. after the
  seeds of `t` and `κ t` further events. The truncation also applies to the idle threads `ι`
  (the environment thread `ν` of Section 6), where `κ` is `0` (a budget vanishes outside
  `S.P.threads`): the bound is `(W b ν).length`, exactly the seeds that `ν` sends, so `ν` is not
  restricted (`frag_cnt_idle`). The paper's def:terminal leaves `ν` untruncated (Opus review of
  C2-C3b); both give the same executions.
* `budgetProg_bounded`; prop:mp-cover (1) `cover_exists`, (2) `cover_frag` (needs
  `Abs.Realised b`), (3) `cover_unique` (also concluding `IsBudget` for the canonical budget);
  thm:mp-terminal `fragOK_iff_term`.
* Helpers (generic): `card_eq_sum_cnt`, `sum_map_sub`, `cnt_le_of_isPrefixOf`,
  `cnt_eq_zero_of_not_mem`, `cnt_le_of_bounded`, `exists_term_ext` (a consistent execution of a
  bounded program extends to a terminal one); for a setting: `frag_len_eq`
  (`‖H‖ = Σ_{t ∈ P} (cnt t - |W t|)`), `res_step_of_lt`.
-/

namespace Must

namespace Ind

open Graph Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q]

/-! ### Generic helpers -/

omit [DecidableEq Q] [Membership Val Q] in
/-- The events of a graph whose threads are in `ts`, counted by thread. -/
theorem card_eq_sum_cnt {H : Graph Q} {ts : List Tid} (hts : ts.Nodup)
    (h : ∀ e ∈ H.events, e.tid ∈ ts) : H.events.card = (ts.map H.cnt).sum := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Ev.tid) (t := ts.toFinset)
    (fun e he => List.mem_toFinset.mpr (h e (Finset.mem_coe.mp he)))]
  exact List.sum_toFinset _ hts

omit [DecidableEq Q] [Membership Val Q] in
theorem sum_map_sub {l : List Tid} {f g : Tid → ℕ} (h : ∀ t ∈ l, g t ≤ f t) :
    (l.map fun t => f t - g t).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a List.mem_cons_self
    have h2 := Trust.sum_map_le_sum_map (fun t ht => h t (List.mem_cons_of_mem _ ht))
    rw [ih fun t ht => h t (List.mem_cons_of_mem _ ht)]
    omega

omit [Membership Val Q] in
theorem cnt_le_of_isPrefixOf {H F : Graph Q} (hp : H.IsPrefixOf F) (t : Tid) :
    H.cnt t ≤ F.cnt t :=
  Finset.card_le_card (Finset.filter_subset_filter _ hp.events_subset)

omit [DecidableEq Q] in
theorem cnt_eq_zero_of_not_mem {P : Program Q} {H : Graph Q} (hH : H.Wf) (hE : P.Exec H)
    {t : Tid} (ht : t ∉ P.threads) : H.cnt t = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx hxt
  exact ht (hxt ▸ hH.tid_mem_threads hE hx)

omit [DecidableEq Q] in
/-- No thread of an execution of a bounded program performs more than the bound. -/
theorem cnt_le_of_bounded {P : Program Q} {n : ℕ} (hb : P.Bounded n) {H : Graph Q} (hH : H.Wf)
    (hE : P.Exec H) (t : Tid) : H.cnt t ≤ n := by
  by_contra hlt
  push Not at hlt
  obtain ⟨e, he, rfl, hi⟩ := (hH.exists_idx_iff t n).mpr hlt
  have := hE e he
  rw [hb _ _ (by rw [traceBefore_length, hi])] at this
  cases this

/-- A consistent execution of a bounded program extends to a terminal execution. -/
theorem exists_term_ext {M : Model Q} {P : Program Q} {n : ℕ} (hb : P.Bounded n) {H : Graph Q}
    (hH : ExecM M P H) : ∃ F, Term M P F ∧ H.IsPrefixOf F := by
  have hcard : ∀ K : Graph Q, ExecM M P K → K.events.card ≤ (P.threads.map fun _ => n).sum := by
    intro K hK
    have hKw := M.wf _ hK.2
    rw [card_eq_sum_cnt P.nodup fun e he => hKw.tid_mem_threads hK.1 he]
    exact Trust.sum_map_le_sum_map fun t _ => cnt_le_of_bounded hb hKw hK.1 t
  suffices ∀ m (K : Graph Q), ExecM M P K →
      (P.threads.map fun _ => n).sum - K.events.card = m → ∃ F, Term M P F ∧ K.IsPrefixOf F from
    this _ H hH rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro K hK hm
    by_cases hst : ∃ K', OpStepG M P K K'
    · obtain ⟨K', hs⟩ := hst
      obtain ⟨hK', hp⟩ := ExecM.of_opStepG hK hs
      have h1 := (StepsN.execM hK (n := 1) ⟨K, rfl, hs⟩).2.2
      have h2 := hcard K' hK'
      obtain ⟨F, hF, hpF⟩ := ih _ (by omega) K' hK' rfl
      exact ⟨F, hF, hp.trans hpF⟩
    · push Not at hst
      exact ⟨K, ⟨mreach_iff.mpr hK, hst⟩, (M.wf _ hK.2).isPrefixOf_refl⟩

/-! ### Fragments of a setting -/

section Setting

variable (S : MPSetting Q) {u : Tid → List (Option Val)} {W : Tid → List Msg} {H : Graph Q}

theorem idle_not_mem {t : Tid} (ht : t ∈ S.ι) : t ∉ S.P.threads := fun h =>
  (List.nodup_append.mp S.hι).2.2 t h t ht rfl

/-- `‖H‖ = Σ_{t ∈ P} (cnt t - |W t|)` for a fragment. -/
theorem frag_len_eq (hH : Frag (Model.ofSet S.ms) (S.P.seedRes S.ι S.hι S.m u W) W H) :
    H.len S.ts W = (S.P.threads.map fun t => H.cnt t - (W t).length).sum := by
  have hHw : H.Wf := (Model.ofSet S.ms).wf _ hH.1.2
  have hc := card_eq_sum_cnt (H := H) S.hι fun e he => hHw.tid_mem_threads hH.1.1 he
  have hidle : (S.ι.map H.cnt).sum = (S.ι.map fun t => (W t).length).sum :=
    congrArg List.sum (List.map_congr_left fun t ht => frag_cnt_idle hH ht (idle_not_mem S ht))
  have hle := Trust.sum_map_le_sum_map (l := S.P.threads) fun t _ => hH.2 t
  rw [sum_map_sub fun t _ => hH.2 t]
  unfold Graph.len seedCard
  change H.events.card - ((S.P.threads ++ S.ι).map fun t => (W t).length).sum = _
  rw [hc, List.map_append, List.map_append, List.sum_append, List.sum_append, hidle]
  omega

/-- Before its seeds are sent, a thread of `Q_b` sends. -/
theorem res_step_of_lt {t : Tid} (ht : t ∈ S.ts) {x : List (Option Val)}
    (hl : x.length < (W t).length) :
    ∃ d v, (S.P.seedRes S.ι S.hι S.m u W).step t x = some (.send S.m d v) := by
  change ∃ d v, (if t ∈ S.P.threads then _ else _) = _
  split_ifs with h1 h2
  · rw [prefixStep_of_lt hl]
    exact ⟨_, _, rfl⟩
  · rw [prefixStep_of_lt hl]
    exact ⟨_, _, rfl⟩
  · exact absurd (List.mem_append.mp ht) (by tauto)

end Setting

/-! ### Budget programs -/

namespace SAbs

variable {S : MPSetting Q} {A : Type} (Abs : SAbs S A)

/-- `Q_b|κ` (def:terminal): `Q_b`, every thread truncated after its seeds and `κ t` further
events (for an idle thread `κ = 0`: its seeds only). -/
def budgetProg (b : A) (κ : Tid → ℕ) : Program Q :=
  (Abs.res b).trunc (fun t => (Abs.W b t).length + κ t)

/-- A budget program is bounded. -/
theorem budgetProg_bounded {b : A} {K : ℕ} {κ : Tid → ℕ}
    (hκ : Trust.IsBudget S.P.threads K κ) :
    (Abs.budgetProg b κ).Bounded (seedCard S.ts (Abs.W b) + K) :=
  trunc_bounded fun t ht => Nat.add_le_add
    (Trust.le_sum_map_of_mem (f := fun t => (Abs.W b t).length) ht) (hκ.le t)

/-- The bounds of a fragment that is an execution of the budget program. -/
theorem exec_budgetProg_iff {b : A} {κ : Tid → ℕ} {H : Graph Q} (hH : H.Wf) :
    (Abs.budgetProg b κ).Exec H ↔ (Abs.res b).Exec H ∧ ∀ t, H.cnt t ≤ (Abs.W b t).length + κ t :=
  exec_trunc_iff hH

/-- prop:mp-cover (1): a fragment of length at most `K` is a prefix of a terminal execution of
a budget program of size `K`. (The premise `hb` of the plan is not needed.) -/
theorem cover_exists {b : A} {K : ℕ} {H : Graph Q} (hne : S.P.threads ≠ [])
    (_hb : Abs.Realised b) (hH : Frag (Model.ofSet S.ms) (Abs.res b) (Abs.W b) H)
    (hK : H.len S.ts (Abs.W b) ≤ K) :
    ∃ κ, Trust.IsBudget S.P.threads K κ ∧
      ∃ F, Term (Model.ofSet S.ms) (Abs.budgetProg b κ) F ∧ H.IsPrefixOf F := by
  have hHw : H.Wf := (Model.ofSet S.ms).wf _ hH.1.2
  have hlen := frag_len_eq S hH
  set κ₀ : Tid → ℕ := fun t => if t ∈ S.P.threads then H.cnt t - (Abs.W b t).length else 0
    with hκ₀
  have hs₀ : (S.P.threads.map κ₀).sum = H.len S.ts (Abs.W b) := by
    rw [hlen]
    exact congrArg List.sum (List.map_congr_left fun t ht => by simp [κ₀, ht])
  set t₀ := S.P.threads.head hne
  have ht₀ : t₀ ∈ S.P.threads := List.head_mem hne
  set κ := Function.update κ₀ t₀ (κ₀ t₀ + (K - H.len S.ts (Abs.W b))) with hκ
  have hbud : Trust.IsBudget S.P.threads K κ := by
    refine ⟨fun t ht => ?_, ?_⟩
    · have hne' : t ≠ t₀ := fun h => ht (h ▸ ht₀)
      simp [κ, Function.update_of_ne hne', κ₀, ht]
    · rw [Trust.sum_map_update_add S.P.nodup ht₀, hs₀]
      omega
  have hge : ∀ t, κ₀ t ≤ κ t := fun t => by
    by_cases h : t = t₀
    · subst h
      simp [κ]
    · simp [κ, Function.update_of_ne h]
  have hE : ExecM (Model.ofSet S.ms) (Abs.budgetProg b κ) H := by
    refine ⟨(Abs.exec_budgetProg_iff hHw).mpr ⟨hH.1.1, fun t => ?_⟩, hH.1.2⟩
    by_cases hP : t ∈ S.P.threads
    · have h1 := hge t
      have h2 : κ₀ t = H.cnt t - (Abs.W b t).length := by simp [κ₀, hP]
      omega
    · by_cases hι : t ∈ S.ι
      · rw [frag_cnt_idle hH hι hP]
        exact Nat.le_add_right _ _
      · have : t ∉ (Abs.res b).threads := fun h => (List.mem_append.mp h).elim hP hι
        rw [cnt_eq_zero_of_not_mem hHw hH.1.1 this]
        exact Nat.zero_le _
  obtain ⟨F, hF, hp⟩ := exists_term_ext (Abs.budgetProg_bounded hbud) hE
  exact ⟨κ, hbud, F, hF, hp⟩

/-- prop:mp-cover (2): a terminal execution of a budget program of size `K` is a fragment of
length at most `K`, and so is every graph between `Z_b` and it. Without `hb` false (Astra C7,
Opus B2): `P.threads = [1]`, all actions undefined, `α` constant `a`, `W a = []`; an unrealised
`b` with one message in `W b 2`, `2 ∉ ts`: the empty graph is terminal, not a fragment. -/
theorem cover_frag {b : A} {K : ℕ} {κ : Tid → ℕ} {F : Graph Q} (hb : Abs.Realised b)
    (hκ : Trust.IsBudget S.P.threads K κ) (hF : Term (Model.ofSet S.ms) (Abs.budgetProg b κ) F) :
    Frag (Model.ofSet S.ms) (Abs.res b) (Abs.W b) F ∧ F.len S.ts (Abs.W b) ≤ K ∧
    ∀ H, (seedGraph S.ts S.m (Abs.W b)).IsPrefixOf H → H.IsPrefixOf F →
      Frag (Model.ofSet S.ms) (Abs.res b) (Abs.W b) H ∧ H.len S.ts (Abs.W b) ≤ K := by
  have hE := mreach_iff.mp hF.1
  have hFw : F.Wf := (Model.ofSet S.ms).wf _ hE.2
  obtain ⟨hER, hbd⟩ := (Abs.exec_budgetProg_iff hFw).mp hE.1
  have hW : ∀ t ∉ S.ts, Abs.W b t = [] := by
    obtain ⟨G, hG, rfl⟩ := hb
    exact (Abs.hconf G hG).2.1
  have hst := (term_iff_stuck hE).mp hF
  -- every seed is sent
  have hseeds : ∀ t, (Abs.W b t).length ≤ F.cnt t := by
    intro t
    by_contra hlt
    push Not at hlt
    have hts : t ∈ S.ts := by
      by_contra h
      rw [hW t h] at hlt
      simp at hlt
    have hl : (F.trace t).length < (Abs.W b t).length := by
      unfold trace
      rw [traceBefore_length]
      exact hlt
    obtain ⟨d, v, hstep⟩ := res_step_of_lt S hts (u := Abs.u b) hl
    have hstep' : (Abs.budgetProg b κ).step t (F.trace t) = some (.send S.m d v) := by
      change (if t ∈ (Abs.res b).threads ∧ (F.trace t).length < _ then _ else none) = _
      split_ifs with hc
      · exact hstep
      · exact absurd ⟨hts, by change (F.trace t).length < (Abs.W b t).length + κ t; omega⟩ hc
    obtain ⟨l, hl', hB, -⟩ := hst t hts (by rw [hstep']; rfl)
    rw [hstep'] at hl'
    cases hl'
    exact hB
  have hfrag : Frag (Model.ofSet S.ms) (Abs.res b) (Abs.W b) F := ⟨⟨hER, hE.2⟩, hseeds⟩
  have hlenF : F.len S.ts (Abs.W b) ≤ K := by
    have hc : F.events.card = (S.ts.map F.cnt).sum :=
      card_eq_sum_cnt S.hι fun e he => hFw.tid_mem_threads hER he
    have h1 := Trust.sum_map_le_sum_map (l := S.ts) fun t _ => hbd t
    rw [List.sum_map_add] at h1
    have h2 : (S.ts.map κ).sum = K := by
      unfold MPSetting.ts
      rw [List.map_append, List.sum_append, hκ.2]
      have : (S.ι.map κ).sum = 0 := by
        rw [List.sum_eq_zero_iff]
        intro x hx
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
        exact hκ.1 t (idle_not_mem S ht)
      omega
    have hl : F.len S.ts (Abs.W b) = F.events.card - (S.ts.map fun t => (Abs.W b t).length).sum :=
      rfl
    rw [hl, Nat.sub_le_iff_le_add, hc]
    refine h1.trans ?_
    rw [h2, Nat.add_comm]
  refine ⟨hfrag, hlenF, fun H hsH hHF => ?_⟩
  have hHE : ExecM (Model.ofSet S.ms) (Abs.res b) H :=
    ⟨exec_of_isPrefixOf hER hFw hHF, (Model.ofSet S.ms).cons_of_isPrefixOf hE.2 hHF⟩
  refine ⟨⟨hHE, fun t => ?_⟩, ?_⟩
  · rw [← seedGraph_cnt (Q := Q) (m := S.m) hW t]
    exact cnt_le_of_isPrefixOf hsH t
  · have := Finset.card_le_card hHF.events_subset
    unfold Graph.len at hlenF ⊢
    omega

/-- prop:mp-cover (3): a fragment of length `K` is terminal for its own budget, which is a
budget of size `K`, and it is an execution of no other budget program of size `K`. (The premise
`hb` of the plan is not needed: `Frag` already gives `W b t = []` for every thread without
events.) -/
theorem cover_unique {b : A} {K : ℕ} {H : Graph Q} (_hb : Abs.Realised b)
    (hH : Frag (Model.ofSet S.ms) (Abs.res b) (Abs.W b) H) (hK : H.len S.ts (Abs.W b) = K) :
    Term (Model.ofSet S.ms) (Abs.budgetProg b
      (fun t => if t ∈ S.P.threads then H.cnt t - (Abs.W b t).length else 0)) H ∧
    (∀ κ', Trust.IsBudget S.P.threads K κ' →
      ExecM (Model.ofSet S.ms) (Abs.budgetProg b κ') H →
      ∀ t, κ' t = if t ∈ S.P.threads then H.cnt t - (Abs.W b t).length else 0) ∧
    Trust.IsBudget S.P.threads K
      (fun t => if t ∈ S.P.threads then H.cnt t - (Abs.W b t).length else 0) := by
  have hHw : H.Wf := (Model.ofSet S.ms).wf _ hH.1.2
  have hsum : (S.P.threads.map fun t =>
      if t ∈ S.P.threads then H.cnt t - (Abs.W b t).length else 0).sum = K := by
    rw [← hK, frag_len_eq S hH]
    exact congrArg List.sum (List.map_congr_left fun t ht => by simp [ht])
  have hbud : Trust.IsBudget S.P.threads K
      (fun t => if t ∈ S.P.threads then H.cnt t - (Abs.W b t).length else 0) :=
    ⟨fun t ht => by simp [ht], hsum⟩
  -- the bound of every thread is reached
  have hbound : ∀ t, H.cnt t =
      (Abs.W b t).length + (if t ∈ S.P.threads then H.cnt t - (Abs.W b t).length else 0) ∨
      t ∉ (Abs.res b).threads := by
    intro t
    by_cases hP : t ∈ S.P.threads
    · left
      have := hH.2 t
      simp only [hP, ↓reduceIte]
      omega
    · by_cases hι : t ∈ S.ι
      · left
        simp only [hP, ↓reduceIte, Nat.add_zero]
        exact frag_cnt_idle hH hι hP
      · exact Or.inr fun h => (List.mem_append.mp h).elim hP hι
  have hE : ExecM (Model.ofSet S.ms) (Abs.budgetProg b
      (fun t => if t ∈ S.P.threads then H.cnt t - (Abs.W b t).length else 0)) H := by
    refine ⟨(Abs.exec_budgetProg_iff hHw).mpr ⟨hH.1.1, fun t => ?_⟩, hH.1.2⟩
    rcases hbound t with h | h
    · exact h.le
    · rw [cnt_eq_zero_of_not_mem hHw hH.1.1 h]
      exact Nat.zero_le _
  refine ⟨(term_iff_stuck hE).mpr fun t ht hs => ?_, fun κ' hκ' hE' => ?_, hbud⟩
  · exfalso
    have hnone : (Abs.budgetProg b
        (fun t => if t ∈ S.P.threads then H.cnt t - (Abs.W b t).length else 0)).step t
          (H.trace t) = none := by
      change (if t ∈ (Abs.res b).threads ∧ (H.trace t).length < _ then _ else none) = none
      have hlen : (H.trace t).length = H.cnt t := by
        unfold trace
        rw [traceBefore_length]
      split_ifs with hc
      · exfalso
        rcases hbound t with h | h
        · have hc2 := hc.2
          simp only [hlen] at hc2
          rw [← h] at hc2
          exact lt_irrefl _ hc2
        · exact h hc.1
      · rfl
    rw [hnone] at hs
    cases hs
  · obtain ⟨-, hbd'⟩ := (Abs.exec_budgetProg_iff hHw).mp hE'.1
    have hle : ∀ t ∈ S.P.threads,
        (if t ∈ S.P.threads then H.cnt t - (Abs.W b t).length else 0) ≤ κ' t := by
      intro t ht
      have := hbd' t
      simp only [ht, ↓reduceIte]
      omega
    have heq := Trust.eq_of_le_of_sum_map_eq hle (by rw [hsum, hκ'.2])
    intro t
    by_cases ht : t ∈ S.P.threads
    · exact (heq t ht).symm
    · rw [hκ'.1 t ht]
      simp [ht]

/-- thm:mp-terminal: for an extension-closed α-determined property and `B ∩ Abad = ∅`, the
conditions of thm:mp-reduction (2) at `G` need to be checked on terminal executions of the
budget programs only. (The premise `hb : Abs.α G ∈ B` of the plan is not needed.) -/
theorem fragOK_iff_term {Bad : Set (Graph Q)} {Abad B : Set A} {K : ℕ} {G : Graph Q}
    {ρ : Ev Q → Ev Q} (hne : S.P.threads ≠ []) (hdet : Abs.Determines Bad Abad)
    (hext : Abs.ExtClosed Bad) (hdisj : Disjoint B Abad)
    (hG : ExecM (Model.ofSet S.ms) S.P G) (_hb : Abs.α G ∈ B)
    (hρ : SeedOK G S.m (Abs.W (Abs.α G)) ρ S.ord) :
    Abs.FragOK Abad B K G ρ ↔ ∀ κ, Trust.IsBudget S.P.threads K κ →
      ∀ F, Term (Model.ofSet S.ms) (Abs.budgetProg (Abs.α G) κ) F →
        (F.len S.ts (Abs.W (Abs.α G)) = K → Abs.α (G.scomp F (Abs.W (Abs.α G)) ρ) ∈ B) ∧
        (F.len S.ts (Abs.W (Abs.α G)) < K → Abs.α (G.scomp F (Abs.W (Abs.α G)) ρ) ∉ Abad) := by
  have hreal : Abs.Realised (Abs.α G) := ⟨G, hG, rfl⟩
  obtain ⟨hu, hW, -⟩ := Abs.hconf G hG
  constructor
  · intro hok κ hκ F hF
    exact hok F (Abs.cover_frag hreal hκ hF).1
  · intro h H hH
    refine ⟨fun hl => ?_, fun hl hbad => ?_⟩
    · obtain ⟨hT, -, hbud⟩ := Abs.cover_unique hreal hH hl
      exact (h _ hbud H hT).1 hl
    · obtain ⟨κ, hκ, F, hF, hp⟩ := Abs.cover_exists hne hreal hH hl.le
      obtain ⟨hFF, hFK, -⟩ := Abs.cover_frag hreal hκ hF
      have hCH := (frag_scomp S hG hu hW hρ hH).1
      have hCF := (frag_scomp S hG hu hW hρ hFF).1
      have hbadF := (hdet _ hCF).mp (hext _ _ hCH hCF ((hdet _ hCH).mpr hbad)
        (scomp_mono S hG hu hW hρ hH hFF hp))
      rcases Nat.lt_or_ge (F.len S.ts (Abs.W (Abs.α G))) K with hlt | hge
      · exact (h κ hκ F hF).2 hlt hbadF
      · exact Set.disjoint_left.mp hdisj ((h κ hκ F hF).1 (le_antisymm hFK hge)) hbadF

end SAbs

end Ind

end Must
