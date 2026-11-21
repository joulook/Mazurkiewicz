import Mazurkiewicz.Induction.KInductive

/-!
# Budgets

`induction-popl`, `dpor.tex` sec:budget: def:budget, prop:cover (lem:budget
is in the port, `Trust/Budget.lean`).

How the text is read here.

* A budget for a program with the threads `ts` and of size `K` is a function
  `κ : Tid → ℕ` that is `0` outside `ts` and whose values on `ts` add up to
  `K`: `IsBudget ts K κ`. (The paper's `Tid` is the finite set of threads of
  the program; here thread identifiers are natural numbers, and a budget
  that is not `0` outside `ts` would have the same truncated program as
  another one.)
* `budgets ts K` lists the budgets of size `K`, each once (`mem_budgets`,
  `budgets_nodup`). It is executable.
* `Full(Q)` is `FullSC Q`: the full, well-formed, SC-consistent executions.
* The count `cnt(H)` is `H.cnt`; for an execution it is a budget of size
  `|H| - 1` (`ExecSC.isBudget_cnt`).
* prop:cover (1) needs a thread to which the unused part of the budget is
  given: `Q.threads ≠ []` (the paper's `k ≥ 1`).
-/

namespace Trust

open Program

/-- A budget of size `K` for the threads `ts` (def:budget). -/
def IsBudget (ts : List Tid) (K : ℕ) (κ : Tid → ℕ) : Prop :=
  (∀ t, t ∉ ts → κ t = 0) ∧ (ts.map κ).sum = K

/-- The budgets of size `K` for the threads `ts`. -/
def budgets : List Tid → ℕ → List (Tid → ℕ)
  | [], K => if K = 0 then [fun _ => 0] else []
  | t :: ts, K =>
    (List.range (K + 1)).flatMap (fun k =>
      (budgets ts (K - k)).map (fun κ => Function.update κ t k))

/-- `Full(Q)`: the full SC-consistent executions (def:budget). -/
def FullSC (Q : Program) (F : Graph) : Prop := ExecSC Q F ∧ Q.Full F

/-! ### Sums over the list of threads -/

theorem le_sum_map_of_mem {l : List Tid} {f : Tid → ℕ} {t : Tid} (ht : t ∈ l) :
    f t ≤ (l.map f).sum := by
  induction l with
  | nil => cases ht
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp ht with rfl | h
    · exact Nat.le_add_right _ _
    · exact (ih h).trans (Nat.le_add_left _ _)

theorem sum_map_le_sum_map {l : List Tid} {f g : Tid → ℕ} (h : ∀ t ∈ l, f t ≤ g t) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a List.mem_cons_self) (ih (fun t ht => h t (List.mem_cons_of_mem _ ht)))

theorem eq_of_le_of_sum_map_eq {l : List Tid} {f g : Tid → ℕ} (h : ∀ t ∈ l, f t ≤ g t)
    (hs : (l.map f).sum = (l.map g).sum) : ∀ t ∈ l, f t = g t := by
  induction l with
  | nil => exact fun t ht => absurd ht (by simp)
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons] at hs
    have h1 := h a List.mem_cons_self
    have h2 := sum_map_le_sum_map (fun t ht => h t (List.mem_cons_of_mem _ ht))
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht'
    · omega
    · exact ih (fun t ht => h t (List.mem_cons_of_mem _ ht)) (by omega) t ht'

theorem sum_map_update_of_notMem {l : List Tid} {f : Tid → ℕ} {t : Tid} (ht : t ∉ l) (k : ℕ) :
    (l.map (Function.update f t k)).sum = (l.map f).sum := by
  congr 1
  refine List.map_congr_left (fun t' ht' => Function.update_of_ne (fun h => ht ?_) _ _)
  rw [← h]
  exact ht'

theorem sum_map_update_add {l : List Tid} (hl : l.Nodup) {f : Tid → ℕ} {t : Tid} (ht : t ∈ l)
    (d : ℕ) : (l.map (Function.update f t (f t + d))).sum = (l.map f).sum + d := by
  induction l with
  | nil => cases ht
  | cons a l ih =>
    obtain ⟨ha, hl'⟩ := List.nodup_cons.mp hl
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp ht with rfl | ht'
    · rw [Function.update_self, sum_map_update_of_notMem ha]
      omega
    · have hne : a ≠ t := fun h => ha (h ▸ ht')
      rw [Function.update_of_ne hne, ih hl' ht']
      omega

theorem IsBudget.le {ts : List Tid} {K : ℕ} {κ : Tid → ℕ} (h : IsBudget ts K κ) (t : Tid) :
    κ t ≤ K := by
  by_cases ht : t ∈ ts
  · exact h.2 ▸ le_sum_map_of_mem ht
  · rw [h.1 t ht]
    exact Nat.zero_le _

/-! ### The enumeration of the budgets -/

/-- `budgets` lists exactly the budgets. -/
theorem mem_budgets {ts : List Tid} (hts : ts.Nodup) {K : ℕ} {κ : Tid → ℕ} :
    κ ∈ budgets ts K ↔ IsBudget ts K κ := by
  induction ts generalizing K κ with
  | nil =>
    by_cases hK : K = 0
    · subst hK
      simp [budgets, IsBudget, funext_iff]
    · simp [budgets, hK, IsBudget, Ne.symm hK]
  | cons t ts ih =>
    obtain ⟨htn, hts'⟩ := List.nodup_cons.mp hts
    simp only [budgets, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨k, hk, κ', hκ', rfl⟩
      obtain ⟨h0, hsum⟩ := (ih hts').mp hκ'
      refine ⟨fun t' ht' => ?_, ?_⟩
      · have hne : t' ≠ t := fun h => ht' (h ▸ List.mem_cons_self)
        rw [Function.update_of_ne hne]
        exact h0 t' (fun h => ht' (List.mem_cons_of_mem _ h))
      · rw [List.map_cons, List.sum_cons, Function.update_self, sum_map_update_of_notMem htn,
          hsum]
        omega
    · rintro ⟨h0, hsum⟩
      rw [List.map_cons, List.sum_cons] at hsum
      refine ⟨κ t, by omega, Function.update κ t 0, (ih hts').mpr ⟨fun t' ht' => ?_, ?_⟩, ?_⟩
      · by_cases h : t' = t
        · rw [h, Function.update_self]
        · rw [Function.update_of_ne h]
          exact h0 t' (fun hm => (List.mem_cons.mp hm).elim h ht')
      · rw [sum_map_update_of_notMem htn]
        omega
      · funext t'
        by_cases h : t' = t
        · rw [h, Function.update_self]
        · rw [Function.update_of_ne h, Function.update_of_ne h]

/-- `budgets` lists no budget twice. -/
theorem budgets_nodup {ts : List Tid} (hts : ts.Nodup) (K : ℕ) : (budgets ts K).Nodup := by
  induction ts generalizing K with
  | nil =>
    unfold budgets
    split <;> simp
  | cons t ts ih =>
    obtain ⟨htn, hts'⟩ := List.nodup_cons.mp hts
    unfold budgets
    refine List.nodup_flatMap.mpr ⟨fun k _ => ?_, ?_⟩
    · refine List.Nodup.map_on (fun κ₁ h₁ κ₂ h₂ h => ?_) (ih hts' _)
      funext t'
      by_cases ht' : t' = t
      · rw [ht', ((mem_budgets hts').mp h₁).1 t htn, ((mem_budgets hts').mp h₂).1 t htn]
      · have := congrFun h t'
        rwa [Function.update_of_ne ht', Function.update_of_ne ht'] at this
    · refine List.Pairwise.imp (fun {k k'} hne => ?_) List.nodup_range
      intro κ h₁ h₂
      obtain ⟨κ₁, -, rfl⟩ := List.mem_map.mp h₁
      obtain ⟨κ₂, -, h⟩ := List.mem_map.mp h₂
      have := congrFun h t
      rw [Function.update_self, Function.update_self] at this
      exact hne this.symm

variable {Q : Program}

/-! ### Counts and budgets -/

/-- The counts of an execution add up to the number of its thread events. -/
theorem ExecSC.sum_cnt {H : Graph} (hH : ExecSC Q H) :
    (Q.threads.map H.cnt).sum = H.events.card := by
  have h1 : H.events.card =
      ∑ t ∈ Q.threads.toFinset, (H.events.filter (fun e => e.tid = t)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun e he => List.mem_toFinset.mpr (hH.2.1.tid_mem hH.1 he))
  have h2 : (Q.threads.map H.cnt).sum = ∑ t ∈ Q.threads.toFinset, H.cnt t :=
    (List.sum_toFinset _ Q.threads_nodup).symm
  rw [h2, h1]
  rfl

/-- The count of an execution is a budget of size `|H| - 1`. -/
theorem ExecSC.isBudget_cnt {H : Graph} (hH : ExecSC Q H) :
    IsBudget Q.threads H.events.card H.cnt :=
  ⟨fun _ ht => hH.cnt_of_not_mem ht, hH.sum_cnt⟩

/-- An execution of the truncation is an execution of the program. -/
theorem ExecSC.of_trunc {κ : Tid → ℕ} {F : Graph} (hF : ExecSC (Q.trunc κ) F) :
    ExecSC Q F ∧ ∀ t, F.cnt t ≤ κ t := by
  obtain ⟨hW, hE, hc⟩ := hF
  obtain ⟨hE', hle⟩ := (Program.exec_trunc_iff hW κ).mp hE
  exact ⟨⟨hW, hE', hc⟩, hle⟩

/-- An execution of a truncation by a budget of size `K` has at most `K`
thread events. -/
theorem size_le_of_exec_trunc {κ : Tid → ℕ} {K : ℕ} (hκ : IsBudget Q.threads K κ) {F : Graph}
    (hF : ExecSC (Q.trunc κ) F) : F.size ≤ K + 1 := by
  obtain ⟨hF', hle⟩ := hF.of_trunc
  have h1 := sum_map_le_sum_map (l := Q.threads) (fun t _ => hle t)
  rw [hF'.sum_cnt, hκ.2] at h1
  exact Nat.succ_le_succ h1

/-! ### prop:cover -/

/-- prop:cover (1). -/
theorem cover_exists (hne : Q.threads ≠ []) {K : ℕ} {H : Graph} (hH : GReach Q SC H)
    (hsz : H.size ≤ K + 1) :
    ∃ κ, IsBudget Q.threads K κ ∧ ∃ F, FullSC (Q.trunc κ) F ∧ H.IsPrefixOf F := by
  obtain ⟨t₀, ht₀⟩ := List.exists_mem_of_ne_nil _ hne
  have hHE : ExecSC Q H := greach_iff.mp hH
  have hcard : H.events.card ≤ K := Nat.le_of_succ_le_succ hsz
  let κ : Tid → ℕ := Function.update H.cnt t₀ (H.cnt t₀ + (K - H.events.card))
  have hκ : IsBudget Q.threads K κ := by
    refine ⟨fun t ht => ?_, ?_⟩
    · have hne' : t ≠ t₀ := fun h => ht (h ▸ ht₀)
      change Function.update H.cnt t₀ _ t = 0
      rw [Function.update_of_ne hne']
      exact hHE.cnt_of_not_mem ht
    · change (Q.threads.map (Function.update H.cnt t₀ _)).sum = K
      rw [sum_map_update_add Q.threads_nodup ht₀, hHE.sum_cnt]
      omega
  have hle : ∀ t, H.cnt t ≤ κ t := by
    intro t
    change H.cnt t ≤ Function.update H.cnt t₀ _ t
    by_cases h : t = t₀
    · rw [h, Function.update_self]
      exact Nat.le_add_right _ _
    · rw [Function.update_of_ne h]
  have hHt : GReach (Q.trunc κ) SC H :=
    greach_iff.mpr ⟨hHE.1, (Program.exec_trunc_iff hHE.1 κ).mpr ⟨hHE.2.1, hle⟩, hHE.2.2⟩
  obtain ⟨F, hF, hfull, hp⟩ :=
    exists_full_extension (Program.trunc_bounded (P := Q) hκ.le) hHt
  exact ⟨κ, hκ, F, ⟨greach_iff.mp hF, hfull⟩, hp⟩

/-- prop:cover (2). -/
theorem cover_prefix {κ : Tid → ℕ} {K : ℕ} (hκ : IsBudget Q.threads K κ) {F H : Graph}
    (hF : FullSC (Q.trunc κ) F) (hp : H.IsPrefixOf F) : GReach Q SC H ∧ H.size ≤ K + 1 := by
  obtain ⟨⟨hW, hE, hc⟩, -⟩ := hF.1.of_trunc
  refine ⟨greach_iff.mpr ⟨hW.of_isPrefixOf hp, hE.of_isPrefixOf hW hp,
    SC.prefix_closed F H hW hc hp⟩, ?_⟩
  have h1 := size_le_of_exec_trunc hκ hF.1
  obtain ⟨s, -, rfl⟩ := hp
  have h2 : (F.restrict s).events.card ≤ F.events.card :=
    Finset.card_le_card Finset.inter_subset_left
  unfold Graph.size at h1 ⊢
  omega

/-- prop:cover (3), first part: a reachable graph of size `K + 1` is a full
execution of the truncation by its own count, a budget of size `K`. -/
theorem cover_full {K : ℕ} {H : Graph} (hH : GReach Q SC H) (hsz : H.size = K + 1) :
    IsBudget Q.threads K H.cnt ∧ FullSC (Q.trunc H.cnt) H := by
  have hHE : ExecSC Q H := greach_iff.mp hH
  have hcard : H.events.card = K := Nat.succ.inj hsz
  obtain ⟨hE', hfull⟩ := hHE.2.1.full_trunc_cnt hHE.1
  exact ⟨hcard ▸ hHE.isBudget_cnt, ⟨hHE.1, hE', hHE.2.2⟩, hfull⟩

/-- prop:cover (3), second part: it is an execution of the truncation by no
other budget of size `K`. -/
theorem cover_unique {κ : Tid → ℕ} {K : ℕ} (hκ : IsBudget Q.threads K κ) {H : Graph}
    (hH : ExecSC (Q.trunc κ) H) (hsz : H.size = K + 1) : κ = H.cnt := by
  obtain ⟨hH', hle⟩ := hH.of_trunc
  have hcard : H.events.card = K := Nat.succ.inj hsz
  have hsum : (Q.threads.map H.cnt).sum = (Q.threads.map κ).sum := by
    rw [hH'.sum_cnt, hκ.2, hcard]
  funext t
  by_cases ht : t ∈ Q.threads
  · exact (eq_of_le_of_sum_map_eq (fun t _ => hle t) hsum t ht).symm
  · rw [hκ.1 t ht, hH'.cnt_of_not_mem ht]

/-! ### Instances -/

namespace Examples

set_option linter.hashCommand false

-- the budgets of size 2 for two threads (ex:mono-enum): (0,2), (1,1), (2,0)
#guard (budgets [0, 1] 2).map (fun κ => (κ 0, κ 1)) == [(0, 2), (1, 1), (2, 0)]
-- three threads, size 2: six budgets
#guard (budgets [0, 1, 2] 2).length == 6

/-- prop:cover (3) on the full graph `G3` of the checked run: it is a full
execution of the truncation by its own count, a budget of size 3. -/
example : IsBudget revProg.threads 3 G3.cnt ∧ FullSC (revProg.trunc G3.cnt) G3 := by
  have h3 : G3.size = 3 + 1 := by
    have : G3.events.card = 3 := by
      rw [← C3_abs]
      rfl
    unfold Graph.size
    rw [this]
  exact cover_full (greach_iff.mpr ⟨G3_facts.1, G3_facts.2.1, G3_facts.2.2.1⟩) h3

end Examples

end Trust
