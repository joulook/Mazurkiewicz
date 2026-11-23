import Mazurkiewicz.Condpor.Rmw.Monitors

/-!
# Faithfulness of the wait-set encoding `WComp` (without `signal`)

The reference machine `R` is the wait-set semantics of JLS 17.2 for one wait
set: a thread is idle, waiting (in the wait set), or removed and not yet
resumed, with the cause of its removal (notified or not). Steps: `wait t` of an
idle thread; `notify` (nothing if the wait set is empty, else any member is
removed, notified); `notifyAll`; a silent spurious removal of any member
(un-notified); `resume t b` of a thread removed with cause `b`.

The machine `C` is the encoding of `Monitors.lean`: a `WComp` and the set `U`
of the threads that wait with an un-notified outcome (they are never in `W`).
`wait t` either enters `W` (`WComp.wait`) or `U`; `notify` is `WComp.notify`,
`notifyAll` is `WComp.notifyAll`; `resume t true` is a thread of `W` with
`exitN t = some k'`; `resume t false` is a thread of `U`. In both machines a
thread waits only if it is not currently waiting (well-formedness); budgets are
left out (a bound is a filter on the number of `resume t false` labels).

Main theorem `traces_eq`: the finite label sequences of `R` from the empty
state are exactly those of `C` from `(WComp.init, ∅)`.

Proof, through the intermediate machine `Q` (`R` in which the spurious removal
happens at the `wait`, as the step `waitU`):
* `R ⊆ Q`: backward simulation `Bq` (moves each spurious removal to its wait);
  `Q ⊆ R`: each `waitU` is a `wait` followed by a spurious removal.
* `Q ⊆ C`: forward simulation `Rel` with a witnessed matching `m` of the
  unconsumed notifications `T` onto the notified waiters after the last
  `notifyAll`, injective, `g < j`; consuming the least entitled notification
  preserves it (`H_resumeTok`, an exchange).
* `C ⊆ Q`: backward simulation with the same `Rel`, plus the invariant that
  some `Rel`-state exists for every reachable state of `C` (`inv_step`; the
  exchange `H_resumeSwap` covers a waiter that takes a notification matched to
  another one).

A second theorem `traces_eq_signal` covers `signal` (for a condition:
`await`, `signal`, `signalAll`, no `notify`): the reference keeps the waiters
in a FIFO queue, `signal` removes the head (notified), `signalAll` all, a silent
spurious removal any member; the encoding uses `WComp.signal` and
`WComp.notifyAll`. Proof: the same move of spurious removals to the wait
(`Bs`), then a functional abstraction `absS` (queue = pending waiters; a waiter
of `W` that is not pending is removed, notified) that is a simulation in both
directions.
-/

namespace Condpor

namespace MonSpec

open Function

/-- Visible labels. -/
inductive MLabel
  | wait (t : Tid)
  | notify
  | notifyAll
  | resume (t : Tid) (notified : Bool)
  deriving DecidableEq, Repr

/-- The state of a thread in the reference machine. -/
inductive RS
  | idle
  | waiting
  | removed (notified : Bool)
  deriving DecidableEq, Repr

abbrev RState := Tid → RS

def RState.init : RState := fun _ => .idle

/-- `notifyAll` of the reference: every member of the wait set is removed. -/
def RState.removeAll (s : RState) : RState :=
  fun u => if s u = .waiting then .removed true else s u

/-- The reference machine (JLS 17.2); `none` is the silent spurious removal. -/
inductive RStep : RState → Option MLabel → RState → Prop
  | wait (s : RState) (t : Tid) : s t = .idle → RStep s (some (.wait t)) (update s t .waiting)
  | notifyNone (s : RState) : (∀ u, s u ≠ .waiting) → RStep s (some .notify) s
  | notifyOne (s : RState) (u : Tid) : s u = .waiting →
      RStep s (some .notify) (update s u (.removed true))
  | notifyAll (s : RState) : RStep s (some .notifyAll) s.removeAll
  | spurious (s : RState) (u : Tid) : s u = .waiting → RStep s none (update s u (.removed false))
  | resume (s : RState) (t : Tid) (b : Bool) : s t = .removed b →
      RStep s (some (.resume t b)) (update s t .idle)

/-- Runs of the reference machine, silent steps anywhere. -/
inductive RRun : RState → List MLabel → RState → Prop
  | nil (s : RState) : RRun s [] s
  | tau {s s₁ s₂ : RState} {l : List MLabel} : RStep s none s₁ → RRun s₁ l s₂ → RRun s l s₂
  | step {s s₁ s₂ : RState} {x : MLabel} {l : List MLabel} :
      RStep s (some x) s₁ → RRun s₁ l s₂ → RRun s (x :: l) s₂

/-- Runs of a machine without silent steps. -/
inductive LRun {σ α : Type} (step : σ → α → σ → Prop) : σ → List α → σ → Prop
  | nil (s : σ) : LRun step s [] s
  | cons {s s₁ s₂ : σ} {x : α} {l : List α} :
      step s x s₁ → LRun step s₁ l s₂ → LRun step s (x :: l) s₂

/-- The intermediate machine `Q`: the reference machine in which a thread that is
removed spuriously is removed at its `wait`. -/
inductive QStep : RState → MLabel → RState → Prop
  | wait (s : RState) (t : Tid) : s t = .idle → QStep s (.wait t) (update s t .waiting)
  | waitU (s : RState) (t : Tid) : s t = .idle → QStep s (.wait t) (update s t (.removed false))
  | notifyNone (s : RState) : (∀ u, s u ≠ .waiting) → QStep s .notify s
  | notifyOne (s : RState) (u : Tid) : s u = .waiting →
      QStep s .notify (update s u (.removed true))
  | notifyAll (s : RState) : QStep s .notifyAll s.removeAll
  | resume (s : RState) (t : Tid) (b : Bool) : s t = .removed b →
      QStep s (.resume t b) (update s t .idle)

/-! ### `Q` ⊆ `R` -/

theorem QRun.toRRun {s s' : RState} {l : List MLabel} (h : LRun QStep s l s') : RRun s l s' := by
  induction h with
  | nil s => exact .nil s
  | cons hs _ ih =>
    cases hs with
    | wait t h => exact .step (.wait _ t h) ih
    | waitU t h =>
      refine .step (.wait _ t h) (.tau (RStep.spurious _ t (by simp)) ?_)
      simpa using ih
    | notifyNone h => exact .step (.notifyNone _ h) ih
    | notifyOne u h => exact .step (.notifyOne _ u h) ih
    | notifyAll => exact .step (.notifyAll _) ih
    | resume t b h => exact .step (.resume _ t b h) ih

/-! ### `R` ⊆ `Q`: a backward simulation (the spurious removal is moved to the wait) -/

/-- `q` agrees with `r`, except that a waiting thread of `r` may already be
removed spuriously in `q`. -/
def Bq (r q : RState) : Prop := ∀ t, r t = q t ∨ (r t = .waiting ∧ q t = .removed false)

theorem Bq.back {r r₁ q₁ : RState} {x : Option MLabel} (hs : RStep r x r₁) (hb : Bq r₁ q₁) :
    ∃ q, Bq r q ∧ (x = none → q = q₁) ∧ (∀ y, x = some y → QStep q y q₁) := by
  cases hs with
  | wait t h =>
    have ht := hb t
    simp only [update_self] at ht
    refine ⟨update q₁ t .idle, ?_, by simp, ?_⟩
    · intro u
      by_cases hu : u = t
      · subst hu; simp [h]
      · have := hb u; simpa [hu] using this
    · rintro y ⟨⟩
      rcases ht with ht | ⟨-, ht⟩
      · have := QStep.wait (update q₁ t .idle) t (by simp)
        rwa [update_idem, ht, update_eq_self] at this
      · have := QStep.waitU (update q₁ t .idle) t (by simp)
        rwa [update_idem, ← ht, update_eq_self] at this
  | notifyNone h =>
    refine ⟨q₁, hb, by simp, ?_⟩
    rintro y ⟨⟩
    refine .notifyNone _ (fun u hu => ?_)
    rcases hb u with h' | ⟨-, h'⟩
    · exact h u (h'.trans hu)
    · rw [h'] at hu; cases hu
  | notifyOne u h =>
    have hu := hb u
    simp only [update_self] at hu
    have hq : q₁ u = .removed true := by
      rcases hu with hu | ⟨hu, -⟩
      · exact hu.symm
      · cases hu
    refine ⟨update q₁ u .waiting, ?_, by simp, ?_⟩
    · intro v
      by_cases hv : v = u
      · subst hv; simp [h]
      · have := hb v; simpa [hv] using this
    · rintro y ⟨⟩
      have := QStep.notifyOne (update q₁ u .waiting) u (by simp)
      rwa [update_idem, ← hq, update_eq_self] at this
  | notifyAll =>
    refine ⟨fun t => if r t = .waiting then .waiting else q₁ t, ?_, by simp, ?_⟩
    · intro t
      by_cases ht : r t = .waiting
      · simp [ht]
      · have := hb t
        simp only [RState.removeAll, ht, ite_false] at this
        simpa [ht] using this
    · rintro y ⟨⟩
      have key : RState.removeAll (fun t => if r t = .waiting then .waiting else q₁ t) = q₁ := by
        funext t
        by_cases ht : r t = .waiting
        · have := hb t
          simp only [RState.removeAll, ht, ite_true] at this
          rcases this with h' | ⟨h', -⟩
          · simp [RState.removeAll, ht, h']
          · cases h'
        · have := hb t
          simp only [RState.removeAll, ht, ite_false] at this
          have hq : q₁ t ≠ .waiting := by
            rcases this with h' | ⟨-, h'⟩
            · rw [← h']; exact ht
            · rw [h']; simp
          simp [RState.removeAll, ht, hq]
      have := QStep.notifyAll (fun t => if r t = .waiting then .waiting else q₁ t)
      rwa [key] at this
  | spurious u h =>
    refine ⟨q₁, ?_, fun _ => rfl, by simp⟩
    intro v
    by_cases hv : v = u
    · subst hv
      have := hb v
      simp only [update_self] at this
      rcases this with h' | ⟨h', -⟩
      · exact .inr ⟨h, h'.symm⟩
      · cases h'
    · have := hb v; simpa [hv] using this
  | resume t b h =>
    have ht := hb t
    simp only [update_self] at ht
    have hq : q₁ t = .idle := by
      rcases ht with ht | ⟨ht, -⟩
      · exact ht.symm
      · cases ht
    refine ⟨update q₁ t (.removed b), ?_, by simp, ?_⟩
    · intro u
      by_cases hu : u = t
      · subst hu; simp [h]
      · have := hb u; simpa [hu] using this
    · rintro y ⟨⟩
      have := QStep.resume (update q₁ t (.removed b)) t b (by simp)
      rwa [update_idem, ← hq, update_eq_self] at this

theorem RRun.toQ {r r' : RState} {l : List MLabel} (h : RRun r l r') :
    ∀ q', Bq r' q' → ∃ q, Bq r q ∧ LRun QStep q l q' := by
  induction h with
  | nil s => exact fun q' hq => ⟨q', hq, .nil _⟩
  | tau hs _ ih =>
    intro q' hq'
    obtain ⟨q₁, hb₁, hr₁⟩ := ih q' hq'
    obtain ⟨q, hb, he, -⟩ := Bq.back hs hb₁
    exact ⟨q, hb, by rw [he rfl]; exact hr₁⟩
  | step hs _ ih =>
    intro q' hq'
    obtain ⟨q₁, hb₁, hr₁⟩ := ih q' hq'
    obtain ⟨q, hb, -, hst⟩ := Bq.back hs hb₁
    exact ⟨q, hb, .cons (hst _ rfl) hr₁⟩

theorem RRun.toQRun {l : List MLabel} {r' : RState} (h : RRun RState.init l r') :
    LRun QStep RState.init l r' := by
  obtain ⟨q, hb, hq⟩ := h.toQ r' (fun t => .inl rfl)
  have : q = RState.init := by
    funext t
    rcases hb t with h' | ⟨h', -⟩
    · exact h'.symm
    · cases h'
  rwa [this] at hq


/-! ### The machine `C`: the encoding `WComp` -/

/-- A state of `C`: the component, and the threads waiting with an un-notified
outcome (they are not in `W`). -/
structure CState where
  k : WComp
  U : Tid → Bool

def CState.init : CState := ⟨WComp.init, fun _ => false⟩

inductive CStep : CState → MLabel → CState → Prop
  | waitN (s : CState) (t : Tid) : t ∉ s.k.W.map Prod.fst → s.U t = false →
      CStep s (.wait t) ⟨s.k.wait t, s.U⟩
  | waitU (s : CState) (t : Tid) : t ∉ s.k.W.map Prod.fst → s.U t = false →
      CStep s (.wait t) ⟨s.k, update s.U t true⟩
  | notify (s : CState) : CStep s .notify ⟨s.k.notify, s.U⟩
  | notifyAll (s : CState) : CStep s .notifyAll ⟨s.k.notifyAll, s.U⟩
  | resumeN (s : CState) (t : Tid) (k' : WComp) : t ∈ s.k.W.map Prod.fst →
      s.k.exitN t = some k' → CStep s (.resume t true) ⟨k', s.U⟩
  | resumeU (s : CState) (t : Tid) : s.U t = true →
      CStep s (.resume t false) ⟨s.k, update s.U t false⟩

/-! ### Invariants of `C` that do not mention `R` -/

structure Basic (k : WComp) (U : Tid → Bool) : Prop where
  S_nil : k.S = []
  nodup : (k.W.map Prod.fst).Nodup
  a_le : k.a ≤ k.c
  g_le : ∀ w ∈ k.W, w.2 ≤ k.c
  T_sorted : k.T.Pairwise (· < ·)
  T_range : ∀ j ∈ k.T, k.a < j ∧ j ≤ k.c
  disj : ∀ t, U t = true → t ∉ k.W.map Prod.fst

theorem mem_fst {W : List (Tid × ℕ)} {t : Tid} : t ∈ W.map Prod.fst ↔ ∃ g, (t, g) ∈ W := by
  simp

theorem mem_drop {k : WComp} {t u : Tid} {g : ℕ} : (u, g) ∈ k.drop t ↔ (u, g) ∈ k.W ∧ u ≠ t := by
  simp [WComp.drop]

theorem mem_fst_drop {k : WComp} {t u : Tid} :
    u ∈ (k.drop t).map Prod.fst ↔ u ∈ k.W.map Prod.fst ∧ u ≠ t := by
  simp only [mem_fst, mem_drop]
  constructor
  · rintro ⟨g, h, h'⟩; exact ⟨⟨g, h⟩, h'⟩
  · rintro ⟨⟨g, h⟩, h'⟩; exact ⟨g, h, h'⟩

theorem Basic.uniq {k : WComp} {U : Tid → Bool} (hb : Basic k U) {t : Tid} {g₁ g₂ : ℕ}
    (h₁ : (t, g₁) ∈ k.W) (h₂ : (t, g₂) ∈ k.W) : g₁ = g₂ :=
  (Prod.mk.inj (List.inj_on_of_nodup_map hb.nodup h₁ h₂ rfl)).2

theorem find_of_mem {W : List (Tid × ℕ)} {t : Tid} {g : ℕ} (hnd : (W.map Prod.fst).Nodup)
    (h : (t, g) ∈ W) : W.find? (fun w => decide (w.1 = t)) = some (t, g) := by
  induction W with
  | nil => simp at h
  | cons w W ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 h with h | h
    · subst h; simp
    · have hw : w.1 ≠ t := fun e => hnd.1 (by rw [e]; exact mem_fst.2 ⟨g, h⟩)
      simp [hw, ih hnd.2 h]

theorem Basic.entry {k : WComp} {U : Tid → Bool} (hb : Basic k U) {t : Tid} {g : ℕ}
    (h : (t, g) ∈ k.W) : k.entry t = g := by
  simp [WComp.entry, find_of_mem hb.nodup h]

theorem Basic.pending {k : WComp} {U : Tid → Bool} (hb : Basic k U) :
    k.pending = k.W.filter (fun w => decide (k.a ≤ w.2)) := by
  simp [WComp.pending, hb.S_nil]

theorem head_filter {T : List ℕ} (hT : T.Pairwise (· < ·)) {g j₀ : ℕ}
    (h : T.find? (fun j => decide (g < j)) = some j₀) :
    j₀ ∈ T ∧ g < j₀ ∧ ∀ j ∈ T, g < j → j₀ ≤ j := by
  induction T with
  | nil => simp at h
  | cons x T ih =>
    rw [List.pairwise_cons] at hT
    by_cases hx : g < x
    · simp only [List.find?_cons, hx, decide_true, Option.some.injEq] at h
      subst h
      refine ⟨by simp, hx, ?_⟩
      intro j hj _
      rcases List.mem_cons.1 hj with rfl | hj
      · exact le_rfl
      · exact (hT.1 j hj).le
    · simp only [List.find?_cons, hx, decide_false] at h
      obtain ⟨h1, h2, h3⟩ := ih hT.2 h
      refine ⟨List.mem_cons_of_mem _ h1, h2, ?_⟩
      intro j hj hgj
      rcases List.mem_cons.1 hj with rfl | hj
      · exact absurd hgj hx
      · exact h3 j hj hgj

theorem head_filter_some {T : List ℕ} {g j : ℕ} (hj : j ∈ T) (hg : g < j) :
    ∃ j₀, T.find? (fun j => decide (g < j)) = some j₀ := by
  cases h : T.find? (fun j => decide (g < j)) with
  | some j₀ => exact ⟨j₀, rfl⟩
  | none =>
    rw [List.find?_eq_none] at h
    exact absurd hg (by simpa using h j hj)

/-- Return by `notifyAll`. -/
theorem Basic.exitN_lt {k : WComp} {U : Tid → Bool} (hb : Basic k U) {t : Tid} {g : ℕ}
    (h : (t, g) ∈ k.W) (hg : g < k.a) : k.exitN t = some { k with W := k.drop t } := by
  simp [WComp.exitN, hb.entry h, hg]

/-- Return by the least notification of `notify` after the entry. -/
theorem Basic.exitN_find {k : WComp} {U : Tid → Bool} (hb : Basic k U) {t : Tid} {g : ℕ}
    (h : (t, g) ∈ k.W) (hg : k.a ≤ g) {j₀ : ℕ}
    (hf : k.T.find? (fun j => decide (g < j)) = some j₀) :
    k.exitN t = some { k with T := k.T.erase j₀, W := k.drop t } := by
  simp [WComp.exitN, hb.entry h, not_lt.2 hg, hb.S_nil, hf]

theorem Basic.exitN_some {k : WComp} {U : Tid → Bool} (hb : Basic k U) {t : Tid} {g : ℕ}
    (h : (t, g) ∈ k.W) (hg : k.a ≤ g) {k' : WComp} (hex : k.exitN t = some k') :
    ∃ j₀, k.T.find? (fun j => decide (g < j)) = some j₀ ∧
      k' = { k with T := k.T.erase j₀, W := k.drop t } := by
  cases hf : k.T.find? (fun j => decide (g < j)) with
  | none => simp [WComp.exitN, hb.entry h, not_lt.2 hg, hb.S_nil, hf] at hex
  | some j₀ =>
    rw [hb.exitN_find h hg hf] at hex
    exact ⟨j₀, rfl, (Option.some.inj hex).symm⟩

theorem Basic.init : Basic CState.init.k CState.init.U where
  S_nil := rfl
  nodup := by simp [CState.init, WComp.init]
  a_le := le_rfl
  g_le := by simp [CState.init, WComp.init]
  T_sorted := by simp [CState.init, WComp.init]
  T_range := by simp [CState.init, WComp.init]
  disj := by simp [CState.init]

theorem Basic.step {s s' : CState} {x : MLabel} (hb : Basic s.k s.U) (h : CStep s x s') :
    Basic s'.k s'.U := by
  cases h with
  | waitN t ht hU =>
    refine ⟨hb.S_nil, ?_, hb.a_le, ?_, hb.T_sorted, hb.T_range, ?_⟩
    · simp only [WComp.wait, List.map_append, List.map_cons, List.map_nil]
      rw [List.nodup_append]
      refine ⟨hb.nodup, by simp, ?_⟩
      intro a ha b hb' e
      simp only [List.mem_singleton] at hb'
      subst hb'; subst e; exact ht ha
    · intro w hw
      simp only [WComp.wait, List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact hb.g_le w hw
      · exact le_rfl
    · intro u hu
      simp only [WComp.wait, List.map_append, List.mem_append, List.map_cons, List.map_nil,
        List.mem_singleton, not_or]
      refine ⟨hb.disj u hu, ?_⟩
      rintro rfl; rw [hU] at hu; cases hu
  | waitU t ht hU =>
    refine ⟨hb.S_nil, hb.nodup, hb.a_le, hb.g_le, hb.T_sorted, hb.T_range, ?_⟩
    intro u hu
    by_cases hut : u = t
    · subst hut; exact ht
    · exact hb.disj u (by simpa [hut] using hu)
  | notify =>
    unfold WComp.notify
    split_ifs with hlt
    · refine ⟨hb.S_nil, hb.nodup, Nat.le_succ_of_le hb.a_le, fun w hw => Nat.le_succ_of_le
        (hb.g_le w hw), ?_, ?_, hb.disj⟩
      · simp only
        rw [List.pairwise_append]
        refine ⟨hb.T_sorted, by simp, ?_⟩
        intro a ha b hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact Nat.lt_succ_of_le (hb.T_range a ha).2
      · intro j hj
        simp only [List.mem_append, List.mem_singleton] at hj
        rcases hj with hj | rfl
        · exact ⟨(hb.T_range j hj).1, Nat.le_succ_of_le (hb.T_range j hj).2⟩
        · exact ⟨Nat.lt_succ_of_le hb.a_le, le_rfl⟩
    · exact hb
  | notifyAll =>
    refine ⟨rfl, hb.nodup, le_rfl, fun w hw => Nat.le_succ_of_le (hb.g_le w hw),
      by simp [WComp.notifyAll],
      by simp [WComp.notifyAll], hb.disj⟩
  | resumeN t k' hm hex =>
    obtain ⟨g, hg⟩ := mem_fst.1 hm
    have hdrop : ∀ k'' : WComp, k''.W = s.k.drop t → k''.c = s.k.c → k''.a = s.k.a →
        k''.S = s.k.S → k''.T.Sublist s.k.T → Basic k'' s.U := by
      intro k'' hW hc ha hS hT
      have hsub : (k''.W.map Prod.fst).Sublist (s.k.W.map Prod.fst) := by
        rw [hW]; exact (List.filter_sublist).map _
      refine ⟨hS.trans hb.S_nil, hb.nodup.sublist hsub, by rw [hc, ha]; exact hb.a_le, ?_,
        hb.T_sorted.sublist hT, ?_, ?_⟩
      · intro w hw; rw [hW] at hw; rw [hc]; exact hb.g_le w (List.filter_sublist.subset hw)
      · intro j hj; rw [hc, ha]; exact hb.T_range j (hT.subset hj)
      · intro u hu hu'; exact hb.disj u hu (hsub.subset hu')
    by_cases hlt : g < s.k.a
    · rw [hb.exitN_lt hg hlt] at hex
      cases hex
      exact hdrop _ rfl rfl rfl rfl (List.Sublist.refl _)
    · obtain ⟨j₀, -, rfl⟩ := hb.exitN_some hg (not_lt.1 hlt) hex
      exact hdrop _ rfl rfl rfl rfl List.erase_sublist
  | resumeU t hU =>
    refine ⟨hb.S_nil, hb.nodup, hb.a_le, hb.g_le, hb.T_sorted, hb.T_range, ?_⟩
    intro u hu
    by_cases hut : u = t
    · subst hut; simp at hu
    · exact hb.disj u (by simpa [hut] using hu)


/-! ### The relation between `Q` and `C` (the matching invariant) -/

/-- `r` is a state of `Q` consistent with the state `(k, U)` of `C`, with the
matching `m` of the unconsumed notifications to removed (notified) waiters:
`m` is a bijection from `T` onto the waiters of `W` after the last
`notifyAll` that are removed in `r`, and maps each notification `j` to a waiter
that entered before `j` was issued (Hall's condition, witnessed). -/
structure Rel (r : RState) (m : ℕ → Tid) (k : WComp) (U : Tid → Bool) : Prop where
  hU : ∀ t, U t = true → r t = .removed false
  hW : ∀ t g, (t, g) ∈ k.W → r t = .waiting ∨ r t = .removed true
  hWa : ∀ t g, (t, g) ∈ k.W → g < k.a → r t = .removed true
  hI : ∀ t, t ∉ k.W.map Prod.fst → U t = false → r t = .idle
  mT : ∀ j ∈ k.T, ∃ g, (m j, g) ∈ k.W ∧ k.a ≤ g ∧ g < j ∧ r (m j) = .removed true
  inj : ∀ j₁ ∈ k.T, ∀ j₂ ∈ k.T, m j₁ = m j₂ → j₁ = j₂
  surj : ∀ t g, (t, g) ∈ k.W → k.a ≤ g → r t = .removed true → ∃ j ∈ k.T, m j = t

section RelLemmas

variable {r : RState} {m : ℕ → Tid} {k : WComp} {U : Tid → Bool}

theorem Rel.waiting (hr : Rel r m k U) {t : Tid} (h : r t = .waiting) :
    ∃ g, (t, g) ∈ k.W ∧ k.a ≤ g := by
  cases hU : U t
  · by_cases hm : t ∈ k.W.map Prod.fst
    · obtain ⟨g, hg⟩ := mem_fst.1 hm
      refine ⟨g, hg, not_lt.1 fun hlt => ?_⟩
      rw [hr.hWa t g hg hlt] at h; cases h
    · rw [hr.hI t hm hU] at h; cases h
  · rw [hr.hU t hU] at h; cases h

theorem Rel.removedT (hr : Rel r m k U) {t : Tid} (h : r t = .removed true) :
    ∃ g, (t, g) ∈ k.W := by
  cases hU : U t
  · by_cases hm : t ∈ k.W.map Prod.fst
    · exact mem_fst.1 hm
    · rw [hr.hI t hm hU] at h; cases h
  · rw [hr.hU t hU] at h; cases h

theorem Rel.removedF (hr : Rel r m k U) {t : Tid} (h : r t = .removed false) : U t = true := by
  cases hU : U t
  · by_cases hm : t ∈ k.W.map Prod.fst
    · obtain ⟨g, hg⟩ := mem_fst.1 hm
      rcases hr.hW t g hg with h' | h' <;> rw [h'] at h <;> cases h
    · rw [hr.hI t hm hU] at h; cases h
  · rfl

theorem Rel.idle (hr : Rel r m k U) {t : Tid} (h : r t = .idle) :
    t ∉ k.W.map Prod.fst ∧ U t = false := by
  cases hU : U t
  · refine ⟨fun hm => ?_, rfl⟩
    obtain ⟨g, hg⟩ := mem_fst.1 hm
    rcases hr.hW t g hg with h' | h' <;> rw [h'] at h <;> cases h
  · rw [hr.hU t hU] at h; cases h

theorem Basic.not_U {t : Tid} {g : ℕ} (hb : Basic k U) (ht : (t, g) ∈ k.W) : U t = false := by
  cases h : U t
  · rfl
  · exact absurd (mem_fst.2 ⟨g, ht⟩) (hb.disj t h)

/-! #### Counting: when `notify` issues a notification -/

theorem count_lt (hb : Basic k U) (hr : Rel r m k U) {u : Tid} {g : ℕ} (hu : (u, g) ∈ k.W)
    (ha : k.a ≤ g) (hw : r u = .waiting) : k.T.length < k.pending.length := by
  classical
  rw [hb.pending]
  have hPnd : ((k.W.filter (fun w => decide (k.a ≤ w.2))).map Prod.fst).Nodup :=
    hb.nodup.sublist (List.filter_sublist.map _)
  have hPmem : ∀ v g', (v, g') ∈ k.W → k.a ≤ g' →
      v ∈ ((k.W.filter (fun w => decide (k.a ≤ w.2))).map Prod.fst).toFinset := by
    intro v g' h h'
    rw [List.mem_toFinset]
    exact List.mem_map.2 ⟨(v, g'), List.mem_filter.2 ⟨h, by simpa using h'⟩, rfl⟩
  have hsub : k.T.toFinset.image m ⊆
      ((k.W.filter (fun w => decide (k.a ≤ w.2))).map Prod.fst).toFinset.erase u := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    rw [List.mem_toFinset] at hj
    obtain ⟨g', hg', hag', -, hrm⟩ := hr.mT j hj
    exact Finset.mem_erase.2 ⟨(fun e => by rw [e, hw] at hrm; cases hrm), hPmem _ _ hg' hag'⟩
  have hinj : Set.InjOn m (k.T.toFinset : Set ℕ) := by
    intro j₁ hj₁ j₂ hj₂ e
    simp only [Finset.mem_coe, List.mem_toFinset] at hj₁ hj₂
    exact hr.inj j₁ hj₁ j₂ hj₂ e
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem (hPmem u g hu ha),
    List.toFinset_card_of_nodup hb.T_sorted.nodup, List.toFinset_card_of_nodup hPnd,
    List.length_map] at hcard
  have hpos : 0 < (k.W.filter (fun w => decide (k.a ≤ w.2))).length :=
    List.length_pos_of_mem (List.mem_filter.2 ⟨hu, by simpa using ha⟩)
  omega

theorem count_ge (hb : Basic k U) (hr : Rel r m k U) (hw : ∀ u, r u ≠ .waiting) :
    k.pending.length ≤ k.T.length := by
  classical
  rw [hb.pending]
  have hPnd : ((k.W.filter (fun w => decide (k.a ≤ w.2))).map Prod.fst).Nodup :=
    hb.nodup.sublist (List.filter_sublist.map _)
  have hsub : ((k.W.filter (fun w => decide (k.a ≤ w.2))).map Prod.fst).toFinset ⊆
      k.T.toFinset.image m := by
    intro x hx
    rw [List.mem_toFinset] at hx
    obtain ⟨⟨v, g'⟩, hv, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hv, ha'⟩ := List.mem_filter.1 hv
    have hrv : r v = .removed true := (hr.hW v g' hv).resolve_left (hw v)
    obtain ⟨j, hj, hjv⟩ := hr.surj v g' hv (by simpa using ha') hrv
    exact Finset.mem_image.2 ⟨j, List.mem_toFinset.2 hj, hjv⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := k.T.toFinset) (f := m)
  have h3 := List.toFinset_card_le k.T
  rw [List.toFinset_card_of_nodup hPnd, List.length_map] at h1
  omega

/-- The component after a `notify` that issues a notification. -/
def issue (k : WComp) : WComp := { k with c := k.c + 1, T := k.T ++ [k.c + 1] }

theorem notify_issue (h : k.T.length < k.pending.length) : k.notify = issue k := by
  simp [WComp.notify, h, issue]

theorem notify_self (h : ¬ k.T.length < k.pending.length) : k.notify = k := by
  simp [WComp.notify, h]

/-! #### The relation after each step (forward) -/

theorem H_waitN (hb : Basic k U) (hr : Rel r m k U) {t : Tid} (ht : t ∉ k.W.map Prod.fst)
    (hU : U t = false) : Rel (update r t .waiting) m (k.wait t) U := by
  have hrt : r t = .idle := hr.hI t ht hU
  have hne : ∀ u g, (u, g) ∈ k.W → u ≠ t := fun u g h e => ht (e ▸ mem_fst.2 ⟨g, h⟩)
  refine ⟨?_, ?_, ?_, ?_, ?_, hr.inj, ?_⟩
  · intro u hu
    have : u ≠ t := by rintro rfl; rw [hU] at hu; cases hu
    rw [update_of_ne this]; exact hr.hU u hu
  · intro u g hg
    simp only [WComp.wait, List.mem_append, List.mem_singleton, Prod.mk.injEq] at hg
    rcases hg with hg | ⟨rfl, rfl⟩
    · rw [update_of_ne (hne u g hg)]; exact hr.hW u g hg
    · simp
  · intro u g hg hlt
    simp only [WComp.wait, List.mem_append, List.mem_singleton, Prod.mk.injEq] at hg
    rcases hg with hg | ⟨rfl, rfl⟩
    · rw [update_of_ne (hne u g hg)]; exact hr.hWa u g hg hlt
    · exact absurd hb.a_le (not_le.2 hlt)
  · intro u hu hU'
    simp only [WComp.wait, List.map_append, List.mem_append, List.map_cons, List.map_nil,
      List.mem_singleton, not_or] at hu
    rw [update_of_ne hu.2]; exact hr.hI u hu.1 hU'
  · intro j hj
    obtain ⟨g, hg, h1, h2, h3⟩ := hr.mT j hj
    have : m j ≠ t := by intro e; rw [e, hrt] at h3; cases h3
    exact ⟨g, List.mem_append_left _ hg, h1, h2, by rw [update_of_ne this]; exact h3⟩
  · intro u g hg ha hu
    simp only [WComp.wait, List.mem_append, List.mem_singleton, Prod.mk.injEq] at hg
    rcases hg with hg | ⟨rfl, rfl⟩
    · rw [update_of_ne (hne u g hg)] at hu; exact hr.surj u g hg ha hu
    · simp at hu

theorem H_waitU (hr : Rel r m k U) {t : Tid} (ht : t ∉ k.W.map Prod.fst) :
    Rel (update r t (.removed false)) m k (update U t true) := by
  have hne : ∀ u g, (u, g) ∈ k.W → u ≠ t := fun u g h e => ht (e ▸ mem_fst.2 ⟨g, h⟩)
  refine ⟨?_, ?_, ?_, ?_, ?_, hr.inj, ?_⟩
  · intro u hu
    by_cases e : u = t
    · rw [e, update_self]
    · rw [update_of_ne e] at hu ⊢; exact hr.hU u hu
  · intro u g hg; rw [update_of_ne (hne u g hg)]; exact hr.hW u g hg
  · intro u g hg hlt; rw [update_of_ne (hne u g hg)]; exact hr.hWa u g hg hlt
  · intro u hu hU'
    have e : u ≠ t := by rintro rfl; simp at hU'
    rw [update_of_ne e] at hU' ⊢; exact hr.hI u hu hU'
  · intro j hj
    obtain ⟨g, hg, h1, h2, h3⟩ := hr.mT j hj
    exact ⟨g, hg, h1, h2, by rw [update_of_ne (hne _ _ hg)]; exact h3⟩
  · intro u g hg ha hu
    rw [update_of_ne (hne u g hg)] at hu; exact hr.surj u g hg ha hu

theorem H_pick (hb : Basic k U) (hr : Rel r m k U) {u : Tid} {g : ℕ} (hu : (u, g) ∈ k.W)
    (ha : k.a ≤ g) (hw : r u = .waiting) :
    Rel (update r u (.removed true)) (update m (k.c + 1) u) (issue k) U := by
  have hTc : ∀ j ∈ k.T, j ≠ k.c + 1 := fun j hj e => by
    have := (hb.T_range j hj).2; omega
  have hmu : ∀ j ∈ k.T, m j ≠ u := fun j hj e' => by
    obtain ⟨_, _, _, _, h3⟩ := hr.mT j hj; rw [e', hw] at h3; cases h3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have : v ≠ u := by rintro rfl; rw [hr.hU v hv] at hw; cases hw
    rw [update_of_ne this]; exact hr.hU v hv
  · intro v g' hg'
    by_cases e : v = u
    · rw [e, update_self]; exact .inr rfl
    · rw [update_of_ne e]; exact hr.hW v g' hg'
  · intro v g' hg' hlt
    by_cases e : v = u
    · rw [e, update_self]
    · rw [update_of_ne e]; exact hr.hWa v g' hg' hlt
  · intro v hv hU'
    have : v ≠ u := fun e => hv (e ▸ mem_fst.2 ⟨g, hu⟩)
    rw [update_of_ne this]; exact hr.hI v hv hU'
  · intro j hj
    simp only [issue, List.mem_append, List.mem_singleton] at hj
    rcases hj with hj | rfl
    · obtain ⟨g', hg', h1, h2, h3⟩ := hr.mT j hj
      refine ⟨g', by rw [update_of_ne (hTc j hj)]; exact hg', h1, h2, ?_⟩
      rw [update_of_ne (hTc j hj), update_of_ne (hmu j hj)]; exact h3
    · refine ⟨g, ?_, ha, ?_, ?_⟩
      · rw [update_self]; exact hu
      · exact Nat.lt_succ_of_le (hb.g_le _ hu)
      · rw [update_self, update_self]
  · intro j₁ hj₁ j₂ hj₂ e
    simp only [issue, List.mem_append, List.mem_singleton] at hj₁ hj₂
    rcases hj₁ with hj₁ | rfl <;> rcases hj₂ with hj₂ | rfl
    · rw [update_of_ne (hTc j₁ hj₁), update_of_ne (hTc j₂ hj₂)] at e
      exact hr.inj j₁ hj₁ j₂ hj₂ e
    · rw [update_of_ne (hTc j₁ hj₁), update_self] at e; exact absurd e (hmu j₁ hj₁)
    · rw [update_of_ne (hTc j₂ hj₂), update_self] at e; exact absurd e.symm (hmu j₂ hj₂)
    · rfl
  · intro v g' hg' ha' hv
    by_cases e : v = u
    · exact ⟨k.c + 1, by simp [issue], by rw [e, update_self]⟩
    · rw [update_of_ne e] at hv
      obtain ⟨j, hj, hj'⟩ := hr.surj v g' hg' ha' hv
      exact ⟨j, by simp [issue, hj], by rw [update_of_ne (hTc j hj)]; exact hj'⟩

theorem H_notifyAll (hb : Basic k U) (hr : Rel r m k U) (m' : ℕ → Tid) :
    Rel r.removeAll m' k.notifyAll U := by
  have hrem : ∀ t g, (t, g) ∈ k.W → r.removeAll t = .removed true := by
    intro t g hg
    rcases hr.hW t g hg with h | h <;> simp [RState.removeAll, h]
  refine ⟨?_, fun t g hg => .inr (hrem t g hg), fun t g hg _ => hrem t g hg, ?_, ?_, ?_, ?_⟩
  · intro t ht; simp [RState.removeAll, hr.hU t ht]
  · intro t ht hU; simp [RState.removeAll, hr.hI t ht hU]
  · simp [WComp.notifyAll]
  · simp [WComp.notifyAll]
  · intro t g hg ha
    exact absurd ha (not_le.2 (Nat.lt_succ_of_le (hb.g_le _ hg)))

theorem H_resumeAll (hb : Basic k U) (hr : Rel r m k U) {t : Tid} {g : ℕ} (ht : (t, g) ∈ k.W)
    (hlt : g < k.a) : Rel (update r t .idle) m { k with W := k.drop t } U := by
  have htU : U t = false := hb.not_U ht
  refine ⟨?_, ?_, ?_, ?_, ?_, hr.inj, ?_⟩
  · intro u hu
    have : u ≠ t := by rintro rfl; rw [htU] at hu; cases hu
    rw [update_of_ne this]; exact hr.hU u hu
  · intro u g' hg'
    obtain ⟨hg', hut⟩ := mem_drop.1 hg'
    rw [update_of_ne hut]; exact hr.hW u g' hg'
  · intro u g' hg' hlt'
    obtain ⟨hg', hut⟩ := mem_drop.1 hg'
    rw [update_of_ne hut]; exact hr.hWa u g' hg' hlt'
  · intro u hu hU'
    by_cases e : u = t
    · rw [e, update_self]
    · rw [update_of_ne e]
      exact hr.hI u (fun h => hu (mem_fst_drop.2 ⟨h, e⟩)) hU'
  · intro j hj
    obtain ⟨g', hg', h1, h2, h3⟩ := hr.mT j hj
    have : m j ≠ t := by
      intro e; rw [e] at hg'; have := hb.uniq hg' ht; omega
    exact ⟨g', mem_drop.2 ⟨hg', this⟩, h1, h2, by rw [update_of_ne this]; exact h3⟩
  · intro u g' hg' ha hu
    obtain ⟨hg', hut⟩ := mem_drop.1 hg'
    rw [update_of_ne hut] at hu
    exact hr.surj u g' hg' ha hu

theorem H_resumeTok (hb : Basic k U) (hr : Rel r m k U) {t : Tid} {g : ℕ} (ht : (t, g) ∈ k.W)
    (ha : k.a ≤ g) (hrt : r t = .removed true) {j₀ : ℕ} (hj₀ : j₀ ∈ k.T)
    (hmin : ∀ j ∈ k.T, g < j → j₀ ≤ j) :
    ∃ m', Rel (update r t .idle) m' { k with T := k.T.erase j₀, W := k.drop t } U := by
  obtain ⟨j₁, hj₁, hm₁⟩ := hr.surj t g ht ha hrt
  have hg₁ : g < j₁ := by
    obtain ⟨g', hg', -, h2, -⟩ := hr.mT j₁ hj₁
    rw [hm₁] at hg'; rw [hb.uniq ht hg']; exact h2
  have hTnd : k.T.Nodup := hb.T_sorted.nodup
  have hmemE : ∀ {j}, j ∈ k.T.erase j₀ ↔ j ≠ j₀ ∧ j ∈ k.T := fun {j} => hTnd.mem_erase_iff
  have htU : U t = false := hb.not_U ht
  have hmt : ∀ j ∈ k.T, m j = t → j = j₁ := fun j hj e => hr.inj j hj j₁ hj₁ (e.trans hm₁.symm)
  refine ⟨update m j₁ (m j₀), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    have : u ≠ t := by rintro rfl; rw [htU] at hu; cases hu
    rw [update_of_ne this]; exact hr.hU u hu
  · intro u g' hg'
    obtain ⟨hg', hut⟩ := mem_drop.1 hg'
    rw [update_of_ne hut]; exact hr.hW u g' hg'
  · intro u g' hg' hlt'
    obtain ⟨hg', hut⟩ := mem_drop.1 hg'
    rw [update_of_ne hut]; exact hr.hWa u g' hg' hlt'
  · intro u hu hU'
    by_cases e : u = t
    · rw [e, update_self]
    · rw [update_of_ne e]
      exact hr.hI u (fun h => hu (mem_fst_drop.2 ⟨h, e⟩)) hU'
  · intro j hj
    obtain ⟨hne, hj⟩ := hmemE.1 hj
    by_cases e : j = j₁
    · rw [e, update_self]
      obtain ⟨gu, hgu, h1, h2, h3⟩ := hr.mT j₀ hj₀
      have hut : m j₀ ≠ t := fun e' => hne (e.trans (hmt j₀ hj₀ e').symm)
      exact ⟨gu, mem_drop.2 ⟨hgu, hut⟩, h1, lt_of_lt_of_le h2 (hmin j₁ hj₁ hg₁),
        by rw [update_of_ne hut]; exact h3⟩
    · rw [update_of_ne e]
      obtain ⟨g', hg', h1, h2, h3⟩ := hr.mT j hj
      have hut : m j ≠ t := fun e' => e (hmt j hj e')
      exact ⟨g', mem_drop.2 ⟨hg', hut⟩, h1, h2, by rw [update_of_ne hut]; exact h3⟩
  · intro j hj j' hj' e
    obtain ⟨hne, hj⟩ := hmemE.1 hj
    obtain ⟨hne', hj'⟩ := hmemE.1 hj'
    by_cases e1 : j = j₁ <;> by_cases e2 : j' = j₁
    · exact e1.trans e2.symm
    · rw [e1, update_self, update_of_ne e2] at e
      exact absurd (hr.inj j₀ hj₀ j' hj' e).symm hne'
    · rw [e2, update_self, update_of_ne e1] at e
      exact absurd (hr.inj j hj j₀ hj₀ e) hne
    · rw [update_of_ne e1, update_of_ne e2] at e; exact hr.inj j hj j' hj' e
  · intro v gv hgv ha' hv
    obtain ⟨hgv, hvt⟩ := mem_drop.1 hgv
    rw [update_of_ne hvt] at hv
    obtain ⟨j, hj, hjv⟩ := hr.surj v gv hgv ha' hv
    have hj1 : j ≠ j₁ := fun e => hvt (by rw [← hjv, e, hm₁])
    by_cases e0 : j = j₀
    · refine ⟨j₁, hmemE.2 ⟨fun e' => hvt ?_, hj₁⟩, ?_⟩
      · rw [← hjv, e0, ← e', hm₁]
      · rw [update_self, ← e0, hjv]
    · exact ⟨j, hmemE.2 ⟨e0, hj⟩, by rw [update_of_ne hj1]; exact hjv⟩

theorem H_resumeSwap (hb : Basic k U) (hr : Rel r m k U) {t : Tid}
    (hrt : r t = .waiting) {j₀ : ℕ} (hj₀ : j₀ ∈ k.T) :
    Rel (update (update r t .idle) (m j₀) .waiting) m
      { k with T := k.T.erase j₀, W := k.drop t } U := by
  obtain ⟨gu, hgu, hau, -, hru⟩ := hr.mT j₀ hj₀
  have hut : m j₀ ≠ t := fun e => by rw [e, hrt] at hru; cases hru
  have hTnd : k.T.Nodup := hb.T_sorted.nodup
  have hmemE : ∀ {j}, j ∈ k.T.erase j₀ ↔ j ≠ j₀ ∧ j ∈ k.T := fun {j} => hTnd.mem_erase_iff
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have h1 := hr.hU v hv
    have e1 : v ≠ m j₀ := fun e => by rw [e, hru] at h1; cases h1
    have e2 : v ≠ t := fun e => by rw [e, hrt] at h1; cases h1
    rw [update_of_ne e1, update_of_ne e2]; exact h1
  · intro v g' hg'
    obtain ⟨hg', hvt⟩ := mem_drop.1 hg'
    by_cases e : v = m j₀
    · rw [e, update_self]; exact .inl rfl
    · rw [update_of_ne e, update_of_ne hvt]; exact hr.hW v g' hg'
  · intro v g' hg' hlt
    obtain ⟨hg', hvt⟩ := mem_drop.1 hg'
    have e : v ≠ m j₀ := fun e => by
      rw [e] at hg'; have := hb.uniq hg' hgu; simp only at hlt; omega
    rw [update_of_ne e, update_of_ne hvt]; exact hr.hWa v g' hg' hlt
  · intro v hv hU'
    by_cases e2 : v = t
    · rw [e2, update_of_ne hut.symm, update_self]
    · have hv' : v ∉ k.W.map Prod.fst := fun h => hv (mem_fst_drop.2 ⟨h, e2⟩)
      have e1 : v ≠ m j₀ := fun e => hv' (e ▸ mem_fst.2 ⟨gu, hgu⟩)
      rw [update_of_ne e1, update_of_ne e2]; exact hr.hI v hv' hU'
  · intro j hj
    obtain ⟨hne, hj⟩ := hmemE.1 hj
    obtain ⟨g', hg', h1, h2, h3⟩ := hr.mT j hj
    have e1 : m j ≠ m j₀ := fun e => hne (hr.inj j hj j₀ hj₀ e)
    have e2 : m j ≠ t := fun e => by rw [e, hrt] at h3; cases h3
    exact ⟨g', mem_drop.2 ⟨hg', e2⟩, h1, h2, by rw [update_of_ne e1, update_of_ne e2]; exact h3⟩
  · intro j hj j' hj' e; exact hr.inj j (hmemE.1 hj).2 j' (hmemE.1 hj').2 e
  · intro v gv hgv ha' hv
    obtain ⟨hgv, hvt⟩ := mem_drop.1 hgv
    have e1 : v ≠ m j₀ := fun e => by rw [e, update_self] at hv; cases hv
    rw [update_of_ne e1, update_of_ne hvt] at hv
    obtain ⟨j, hj, hjv⟩ := hr.surj v gv hgv ha' hv
    exact ⟨j, hmemE.2 ⟨fun e => e1 (by rw [← hjv, e]), hj⟩, hjv⟩

theorem H_resumeU (hb : Basic k U) (hr : Rel r m k U) {t : Tid} (hU : U t = true) :
    Rel (update r t .idle) m k (update U t false) := by
  have htW := hb.disj t hU
  have hne : ∀ u g, (u, g) ∈ k.W → u ≠ t := fun u g h e => htW (e ▸ mem_fst.2 ⟨g, h⟩)
  refine ⟨?_, ?_, ?_, ?_, ?_, hr.inj, ?_⟩
  · intro u hu
    have e : u ≠ t := by rintro rfl; simp at hu
    rw [update_of_ne e] at hu ⊢; exact hr.hU u hu
  · intro u g hg; rw [update_of_ne (hne u g hg)]; exact hr.hW u g hg
  · intro u g hg hlt; rw [update_of_ne (hne u g hg)]; exact hr.hWa u g hg hlt
  · intro u hu hU'
    by_cases e : u = t
    · rw [e, update_self]
    · rw [update_of_ne e] at hU' ⊢; exact hr.hI u hu hU'
  · intro j hj
    obtain ⟨g, hg, h1, h2, h3⟩ := hr.mT j hj
    exact ⟨g, hg, h1, h2, by rw [update_of_ne (hne _ _ hg)]; exact h3⟩
  · intro u g hg ha hu; rw [update_of_ne (hne u g hg)] at hu; exact hr.surj u g hg ha hu

end RelLemmas


section Backward

variable {k : WComp} {U : Tid → Bool}

/-! #### The relation before each step (backward) -/

theorem B_waitN (hb : Basic k U) {t : Tid} (hb' : Basic (k.wait t) U) (ht : t ∉ k.W.map Prod.fst)
    (hU : U t = false) {r' : RState} {m' : ℕ → Tid} (hr : Rel r' m' (k.wait t) U) :
    r' t = .waiting ∧ Rel (update r' t .idle) m' k U := by
  have hmem : (t, k.c) ∈ (k.wait t).W := by simp [WComp.wait]
  have hne : ∀ u g, (u, g) ∈ k.W → u ≠ t := fun u g h e => ht (e ▸ mem_fst.2 ⟨g, h⟩)
  have hwt : r' t = .waiting := by
    rcases hr.hW t k.c hmem with h | h
    · exact h
    · exfalso
      obtain ⟨j, hj, hjt⟩ := hr.surj t k.c hmem hb.a_le h
      obtain ⟨g', hg', -, h2, -⟩ := hr.mT j hj
      rw [hjt] at hg'
      have := hb'.uniq hg' hmem
      have := (hb.T_range j hj).2
      omega
  refine ⟨hwt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    have e : u ≠ t := by rintro rfl; rw [hU] at hu; cases hu
    rw [update_of_ne e]; exact hr.hU u hu
  · intro u g hg; rw [update_of_ne (hne u g hg)]; exact hr.hW u g (List.mem_append_left _ hg)
  · intro u g hg hlt
    rw [update_of_ne (hne u g hg)]; exact hr.hWa u g (List.mem_append_left _ hg) hlt
  · intro u hu hU'
    by_cases e : u = t
    · rw [e, update_self]
    · rw [update_of_ne e]
      refine hr.hI u ?_ hU'
      simp only [WComp.wait, List.map_append, List.mem_append, List.map_cons, List.map_nil,
        List.mem_singleton, not_or]
      exact ⟨hu, e⟩
  · intro j hj
    obtain ⟨g, hg, h1, h2, h3⟩ := hr.mT j hj
    have e : m' j ≠ t := fun e => by rw [e, hwt] at h3; cases h3
    simp only [WComp.wait, List.mem_append, List.mem_singleton, Prod.mk.injEq] at hg
    exact ⟨g, hg.resolve_right (fun h => e h.1), h1, h2, by rw [update_of_ne e]; exact h3⟩
  · exact hr.inj
  · intro u g hg ha hu
    rw [update_of_ne (hne u g hg)] at hu
    exact hr.surj u g (List.mem_append_left _ hg) ha hu

theorem B_waitU {t : Tid} (ht : t ∉ k.W.map Prod.fst) (hU : U t = false) {r' : RState}
    {m' : ℕ → Tid} (hr : Rel r' m' k (update U t true)) :
    r' t = .removed false ∧ Rel (update r' t .idle) m' k U := by
  have hne : ∀ u g, (u, g) ∈ k.W → u ≠ t := fun u g h e => ht (e ▸ mem_fst.2 ⟨g, h⟩)
  refine ⟨hr.hU t (by simp), ?_, ?_, ?_, ?_, ?_, hr.inj, ?_⟩
  · intro u hu
    have e : u ≠ t := by rintro rfl; rw [hU] at hu; cases hu
    rw [update_of_ne e]; exact hr.hU u (by rw [update_of_ne e]; exact hu)
  · intro u g hg; rw [update_of_ne (hne u g hg)]; exact hr.hW u g hg
  · intro u g hg hlt; rw [update_of_ne (hne u g hg)]; exact hr.hWa u g hg hlt
  · intro u hu hU'
    by_cases e : u = t
    · rw [e, update_self]
    · rw [update_of_ne e]; exact hr.hI u hu (by rw [update_of_ne e]; exact hU')
  · intro j hj
    obtain ⟨g, hg, h1, h2, h3⟩ := hr.mT j hj
    exact ⟨g, hg, h1, h2, by rw [update_of_ne (hne _ _ hg)]; exact h3⟩
  · intro u g hg ha hu
    rw [update_of_ne (hne u g hg)] at hu; exact hr.surj u g hg ha hu

theorem B_issue (hb : Basic k U) {r' : RState} {m' : ℕ → Tid} (hr : Rel r' m' (issue k) U) :
    r' (m' (k.c + 1)) = .removed true ∧ Rel (update r' (m' (k.c + 1)) .waiting) m' k U := by
  have hc : k.c + 1 ∈ (issue k).T := by simp [issue]
  obtain ⟨gu, hgu, hau, -, hru⟩ := hr.mT _ hc
  have hTc : ∀ j ∈ k.T, j ≠ k.c + 1 := fun j hj e => by
    have := (hb.T_range j hj).2; omega
  have hTi : ∀ j ∈ k.T, j ∈ (issue k).T := fun j hj => by simp [issue, hj]
  refine ⟨hru, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have h1 := hr.hU v hv
    have e : v ≠ m' (k.c + 1) := fun e => by rw [e, hru] at h1; cases h1
    rw [update_of_ne e]; exact h1
  · intro v g hg
    by_cases e : v = m' (k.c + 1)
    · rw [e, update_self]; exact .inl rfl
    · rw [update_of_ne e]; exact hr.hW v g hg
  · intro v g hg hlt
    have e : v ≠ m' (k.c + 1) := fun e => by
      rw [e] at hg; have := hb.uniq hg hgu; simp only [issue] at hau; omega
    rw [update_of_ne e]; exact hr.hWa v g hg hlt
  · intro v hv hU'
    have e : v ≠ m' (k.c + 1) := fun e => hv (e ▸ mem_fst.2 ⟨gu, hgu⟩)
    rw [update_of_ne e]; exact hr.hI v hv hU'
  · intro j hj
    obtain ⟨g, hg, h1, h2, h3⟩ := hr.mT j (hTi j hj)
    have e : m' j ≠ m' (k.c + 1) := fun e => hTc j hj (hr.inj j (hTi j hj) _ hc e)
    exact ⟨g, hg, h1, h2, by rw [update_of_ne e]; exact h3⟩
  · intro j₁ hj₁ j₂ hj₂ e; exact hr.inj j₁ (hTi j₁ hj₁) j₂ (hTi j₂ hj₂) e
  · intro v g hg ha hv
    have e : v ≠ m' (k.c + 1) := fun e => by rw [e, update_self] at hv; cases hv
    rw [update_of_ne e] at hv
    obtain ⟨j, hj, hjv⟩ := hr.surj v g hg ha hv
    simp only [issue, List.mem_append, List.mem_singleton] at hj
    rcases hj with hj | rfl
    · exact ⟨j, hj, hjv⟩
    · exact absurd hjv.symm e

theorem B_notifyAll (hb : Basic k U) {r₀ : RState} {m₀ : ℕ → Tid} (hr₀ : Rel r₀ m₀ k U)
    {r' : RState} {m' : ℕ → Tid} (hr : Rel r' m' k.notifyAll U) : r₀.removeAll = r' := by
  funext t
  cases hU : U t
  · by_cases hm : t ∈ k.W.map Prod.fst
    · obtain ⟨g, hg⟩ := mem_fst.1 hm
      have h1 : r' t = .removed true := hr.hWa t g hg (Nat.lt_succ_of_le (hb.g_le _ hg))
      rcases hr₀.hW t g hg with h | h <;> simp [RState.removeAll, h, h1]
    · simp [RState.removeAll, hr₀.hI t hm hU, hr.hI t hm hU]
  · simp [RState.removeAll, hr₀.hU t hU, hr.hU t hU]

theorem B_resumeAll (hb : Basic k U) {t : Tid} {g : ℕ} (ht : (t, g) ∈ k.W) (hlt : g < k.a)
    {r' : RState} {m' : ℕ → Tid} (hr : Rel r' m' { k with W := k.drop t } U) :
    r' t = .idle ∧ Rel (update r' t (.removed true)) m' k U := by
  have htU := hb.not_U ht
  have hrt : r' t = .idle := hr.hI t (fun h => (mem_fst_drop.1 h).2 rfl) htU
  refine ⟨hrt, ?_, ?_, ?_, ?_, ?_, hr.inj, ?_⟩
  · intro u hu
    have : u ≠ t := by rintro rfl; rw [htU] at hu; cases hu
    rw [update_of_ne this]; exact hr.hU u hu
  · intro u g' hg'
    by_cases e : u = t
    · rw [e, update_self]; exact .inr rfl
    · rw [update_of_ne e]; exact hr.hW u g' (mem_drop.2 ⟨hg', e⟩)
  · intro u g' hg' hlt'
    by_cases e : u = t
    · rw [e, update_self]
    · rw [update_of_ne e]; exact hr.hWa u g' (mem_drop.2 ⟨hg', e⟩) hlt'
  · intro u hu hU'
    have e : u ≠ t := fun e => hu (e ▸ mem_fst.2 ⟨g, ht⟩)
    rw [update_of_ne e]; exact hr.hI u (fun h => hu (mem_fst_drop.1 h).1) hU'
  · intro j hj
    obtain ⟨g', hg', h1, h2, h3⟩ := hr.mT j hj
    obtain ⟨hg', e⟩ := mem_drop.1 hg'
    exact ⟨g', hg', h1, h2, by rw [update_of_ne e]; exact h3⟩
  · intro u g' hg' ha hu
    by_cases e : u = t
    · rw [e] at hg'; have := hb.uniq hg' ht; omega
    · rw [update_of_ne e] at hu; exact hr.surj u g' (mem_drop.2 ⟨hg', e⟩) ha hu

theorem B_resumeTok (hb : Basic k U) {t : Tid} {g : ℕ} (ht : (t, g) ∈ k.W) (ha : k.a ≤ g)
    {j₀ : ℕ} (hj₀ : j₀ ∈ k.T) (hg₀ : g < j₀) {r' : RState} {m' : ℕ → Tid}
    (hr : Rel r' m' { k with T := k.T.erase j₀, W := k.drop t } U) :
    r' t = .idle ∧ Rel (update r' t (.removed true)) (update m' j₀ t) k U := by
  have htU := hb.not_U ht
  have hrt : r' t = .idle := hr.hI t (fun h => (mem_fst_drop.1 h).2 rfl) htU
  have hmemE : ∀ {j}, j ∈ k.T.erase j₀ ↔ j ≠ j₀ ∧ j ∈ k.T := fun {j} =>
    hb.T_sorted.nodup.mem_erase_iff
  refine ⟨hrt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    have : u ≠ t := by rintro rfl; rw [htU] at hu; cases hu
    rw [update_of_ne this]; exact hr.hU u hu
  · intro u g' hg'
    by_cases e : u = t
    · rw [e, update_self]; exact .inr rfl
    · rw [update_of_ne e]; exact hr.hW u g' (mem_drop.2 ⟨hg', e⟩)
  · intro u g' hg' hlt'
    by_cases e : u = t
    · rw [e, update_self]
    · rw [update_of_ne e]; exact hr.hWa u g' (mem_drop.2 ⟨hg', e⟩) hlt'
  · intro u hu hU'
    have e : u ≠ t := fun e => hu (e ▸ mem_fst.2 ⟨g, ht⟩)
    rw [update_of_ne e]; exact hr.hI u (fun h => hu (mem_fst_drop.1 h).1) hU'
  · intro j hj
    by_cases e : j = j₀
    · rw [e, update_self, update_self]; exact ⟨g, ht, ha, hg₀, rfl⟩
    · rw [update_of_ne e]
      obtain ⟨g', hg', h1, h2, h3⟩ := hr.mT j (hmemE.2 ⟨e, hj⟩)
      obtain ⟨hg', e'⟩ := mem_drop.1 hg'
      exact ⟨g', hg', h1, h2, by rw [update_of_ne e']; exact h3⟩
  · intro j hj j' hj' e
    have hne : ∀ j ∈ k.T, j ≠ j₀ → m' j ≠ t := fun j hj h e' => by
      obtain ⟨g', hg', -⟩ := hr.mT j (hmemE.2 ⟨h, hj⟩)
      rw [e'] at hg'; exact (mem_drop.1 hg').2 rfl
    by_cases e1 : j = j₀ <;> by_cases e2 : j' = j₀
    · exact e1.trans e2.symm
    · rw [e1, update_self, update_of_ne e2] at e; exact absurd e.symm (hne j' hj' e2)
    · rw [e2, update_self, update_of_ne e1] at e; exact absurd e (hne j hj e1)
    · rw [update_of_ne e1, update_of_ne e2] at e
      exact hr.inj j (hmemE.2 ⟨e1, hj⟩) j' (hmemE.2 ⟨e2, hj'⟩) e
  · intro u g' hg' ha' hu
    by_cases e : u = t
    · exact ⟨j₀, hj₀, by rw [update_self, e]⟩
    · rw [update_of_ne e] at hu
      obtain ⟨j, hj, hju⟩ := hr.surj u g' (mem_drop.2 ⟨hg', e⟩) ha' hu
      obtain ⟨hne, hj⟩ := hmemE.1 hj
      exact ⟨j, hj, by rw [update_of_ne hne]; exact hju⟩

theorem B_resumeU (hb : Basic k U) {t : Tid} (hU : U t = true) {r' : RState} {m' : ℕ → Tid}
    (hr : Rel r' m' k (update U t false)) :
    r' t = .idle ∧ Rel (update r' t (.removed false)) m' k U := by
  have htW := hb.disj t hU
  have hne : ∀ u g, (u, g) ∈ k.W → u ≠ t := fun u g h e => htW (e ▸ mem_fst.2 ⟨g, h⟩)
  have hrt : r' t = .idle := hr.hI t htW (by simp)
  refine ⟨hrt, ?_, ?_, ?_, ?_, ?_, hr.inj, ?_⟩
  · intro u hu
    by_cases e : u = t
    · rw [e, update_self]
    · rw [update_of_ne e]; exact hr.hU u (by rw [update_of_ne e]; exact hu)
  · intro u g hg; rw [update_of_ne (hne u g hg)]; exact hr.hW u g hg
  · intro u g hg hlt; rw [update_of_ne (hne u g hg)]; exact hr.hWa u g hg hlt
  · intro u hu hU'
    have e : u ≠ t := by rintro rfl; rw [hU] at hU'; cases hU'
    rw [update_of_ne e]; exact hr.hI u hu (by rw [update_of_ne e]; exact hU')
  · intro j hj
    obtain ⟨g, hg, h1, h2, h3⟩ := hr.mT j hj
    exact ⟨g, hg, h1, h2, by rw [update_of_ne (hne _ _ hg)]; exact h3⟩
  · intro u g hg ha hu; rw [update_of_ne (hne u g hg)] at hu; exact hr.surj u g hg ha hu

end Backward

/-! ### The three simulations -/

/-- Forward simulation of `Q` by `C`. -/
theorem fwd {s : CState} {r r' : RState} {m : ℕ → Tid} {x : MLabel} (hb : Basic s.k s.U)
    (hr : Rel r m s.k s.U) (h : QStep r x r') : ∃ s' m', CStep s x s' ∧ Rel r' m' s'.k s'.U := by
  cases h with
  | wait t ht =>
    obtain ⟨h1, h2⟩ := hr.idle ht
    exact ⟨_, m, .waitN s t h1 h2, H_waitN hb hr h1 h2⟩
  | waitU t ht =>
    obtain ⟨h1, h2⟩ := hr.idle ht
    exact ⟨_, m, .waitU s t h1 h2, H_waitU hr h1⟩
  | notifyNone hw =>
    refine ⟨_, m, .notify s, ?_⟩
    dsimp only
    rw [notify_self (not_lt.2 (count_ge hb hr hw))]; exact hr
  | notifyOne u hw =>
    obtain ⟨g, hg, ha⟩ := hr.waiting hw
    refine ⟨_, update m (s.k.c + 1) u, .notify s, ?_⟩
    dsimp only
    rw [notify_issue (count_lt hb hr hg ha hw)]; exact H_pick hb hr hg ha hw
  | notifyAll => exact ⟨_, m, .notifyAll s, H_notifyAll hb hr m⟩
  | resume t b ht =>
    cases b with
    | false => exact ⟨_, m, .resumeU s t (hr.removedF ht), H_resumeU hb hr (hr.removedF ht)⟩
    | true =>
      obtain ⟨g, hg⟩ := hr.removedT ht
      by_cases hlt : g < s.k.a
      · exact ⟨_, m, .resumeN s t _ (mem_fst.2 ⟨g, hg⟩) (hb.exitN_lt hg hlt),
          H_resumeAll hb hr hg hlt⟩
      · have ha := not_lt.1 hlt
        obtain ⟨j₁, hj₁, hm₁⟩ := hr.surj t g hg ha ht
        have hg₁ : g < j₁ := by
          obtain ⟨g', hg', -, h2, -⟩ := hr.mT j₁ hj₁
          rw [hm₁] at hg'; rw [hb.uniq hg hg']; exact h2
        obtain ⟨j₀, hf⟩ := head_filter_some hj₁ hg₁
        obtain ⟨hj₀, -, hmin⟩ := head_filter hb.T_sorted hf
        obtain ⟨m', hr'⟩ := H_resumeTok hb hr hg ha ht hj₀ hmin
        exact ⟨_, m', .resumeN s t _ (mem_fst.2 ⟨g, hg⟩) (hb.exitN_find hg ha hf), hr'⟩

/-- Every step of `C` keeps some consistent state of `Q` (non-emptiness of the
set of consistent states; the exchange in `H_resumeSwap`). -/
theorem inv_step {s s' : CState} {x : MLabel} {r : RState} {m : ℕ → Tid} (hb : Basic s.k s.U)
    (hr : Rel r m s.k s.U) (h : CStep s x s') : ∃ r' m', Rel r' m' s'.k s'.U := by
  cases h with
  | waitN t h1 h2 => exact ⟨_, _, H_waitN hb hr h1 h2⟩
  | waitU t h1 h2 => exact ⟨_, _, H_waitU hr h1⟩
  | notify =>
    dsimp only
    by_cases hlt : s.k.T.length < s.k.pending.length
    · rw [notify_issue hlt]
      have : ∃ u, r u = .waiting := by
        by_contra hno
        simp only [not_exists] at hno
        exact absurd hlt (not_lt.2 (count_ge hb hr hno))
      obtain ⟨u, hw⟩ := this
      obtain ⟨g, hg, ha⟩ := hr.waiting hw
      exact ⟨_, _, H_pick hb hr hg ha hw⟩
    · rw [notify_self hlt]; exact ⟨r, m, hr⟩
  | notifyAll => exact ⟨_, _, H_notifyAll hb hr m⟩
  | resumeN t k' hm hex =>
    dsimp only
    obtain ⟨g, hg⟩ := mem_fst.1 hm
    by_cases hlt : g < s.k.a
    · rw [hb.exitN_lt hg hlt] at hex; cases hex
      exact ⟨_, _, H_resumeAll hb hr hg hlt⟩
    · have ha := not_lt.1 hlt
      obtain ⟨j₀, hf, rfl⟩ := hb.exitN_some hg ha hex
      obtain ⟨hj₀, -, hmin⟩ := head_filter hb.T_sorted hf
      rcases hr.hW t g hg with hw | ht
      · exact ⟨_, _, H_resumeSwap hb hr hw hj₀⟩
      · obtain ⟨m', hr'⟩ := H_resumeTok hb hr hg ha ht hj₀ hmin
        exact ⟨_, _, hr'⟩
  | resumeU t hU => exact ⟨_, _, H_resumeU hb hr hU⟩

/-- Backward simulation of `C` by `Q`. -/
theorem back_step {s s' : CState} {x : MLabel} (hb : Basic s.k s.U)
    (hinv : ∃ r₀ m₀, Rel r₀ m₀ s.k s.U) (h : CStep s x s') {r' : RState} {m' : ℕ → Tid}
    (hr : Rel r' m' s'.k s'.U) : ∃ r m, Rel r m s.k s.U ∧ QStep r x r' := by
  have hb' := hb.step h
  cases h with
  | waitN t h1 h2 =>
    obtain ⟨hw, hr1⟩ := B_waitN hb hb' h1 h2 hr
    refine ⟨_, _, hr1, ?_⟩
    have := QStep.wait (update r' t .idle) t (by simp)
    rwa [update_idem, ← hw, update_eq_self] at this
  | waitU t h1 h2 =>
    obtain ⟨hw, hr1⟩ := B_waitU h1 h2 hr
    refine ⟨_, _, hr1, ?_⟩
    have := QStep.waitU (update r' t .idle) t (by simp)
    rwa [update_idem, ← hw, update_eq_self] at this
  | notify =>
    by_cases hlt : s.k.T.length < s.k.pending.length
    · have hr2 : Rel r' m' (issue s.k) s.U := by rw [← notify_issue hlt]; exact hr
      obtain ⟨hu, hr1⟩ := B_issue hb hr2
      refine ⟨_, _, hr1, ?_⟩
      have := QStep.notifyOne (update r' (m' (s.k.c + 1)) .waiting) (m' (s.k.c + 1)) (by simp)
      rwa [update_idem, ← hu, update_eq_self] at this
    · have hr2 : Rel r' m' s.k s.U := by rw [← notify_self hlt]; exact hr
      refine ⟨r', m', hr2, .notifyNone _ fun u hw => ?_⟩
      obtain ⟨g, hg, ha⟩ := hr2.waiting hw
      exact hlt (count_lt hb hr2 hg ha hw)
  | notifyAll =>
    obtain ⟨r₀, m₀, hr₀⟩ := hinv
    refine ⟨r₀, m₀, hr₀, ?_⟩
    rw [← B_notifyAll hb hr₀ hr]; exact .notifyAll r₀
  | resumeN t k' hm hex =>
    obtain ⟨g, hg⟩ := mem_fst.1 hm
    by_cases hlt : g < s.k.a
    · rw [hb.exitN_lt hg hlt] at hex; cases hex
      obtain ⟨hi, hr1⟩ := B_resumeAll hb hg hlt hr
      refine ⟨_, _, hr1, ?_⟩
      have := QStep.resume (update r' t (.removed true)) t true (by simp)
      rwa [update_idem, ← hi, update_eq_self] at this
    · have ha := not_lt.1 hlt
      obtain ⟨j₀, hf, rfl⟩ := hb.exitN_some hg ha hex
      obtain ⟨hj₀, hg₀, -⟩ := head_filter hb.T_sorted hf
      obtain ⟨hi, hr1⟩ := B_resumeTok hb hg ha hj₀ hg₀ hr
      refine ⟨_, _, hr1, ?_⟩
      have := QStep.resume (update r' t (.removed true)) t true (by simp)
      rwa [update_idem, ← hi, update_eq_self] at this
  | resumeU t hU =>
    obtain ⟨hi, hr1⟩ := B_resumeU hb hU hr
    refine ⟨_, _, hr1, ?_⟩
    have := QStep.resume (update r' t (.removed false)) t false (by simp)
    rwa [update_idem, ← hi, update_eq_self] at this

/-! ### Runs -/

theorem inv_run {s s' : CState} {l : List MLabel} (h : LRun CStep s l s') :
    Basic s.k s.U → (∃ r m, Rel r m s.k s.U) → Basic s'.k s'.U ∧ ∃ r m, Rel r m s'.k s'.U := by
  induction h with
  | nil => exact fun hb hi => ⟨hb, hi⟩
  | cons hs _ ih =>
    rintro hb ⟨r, m, hr⟩
    exact ih (hb.step hs) (inv_step hb hr hs)

theorem C_back {s s' : CState} {l : List MLabel} (h : LRun CStep s l s') :
    Basic s.k s.U → (∃ r m, Rel r m s.k s.U) →
    ∀ r' m', Rel r' m' s'.k s'.U → ∃ r m, Rel r m s.k s.U ∧ LRun QStep r l r' := by
  induction h with
  | nil s => exact fun _ _ r' m' hr => ⟨r', m', hr, .nil _⟩
  | cons hs _ ih =>
    rintro hb ⟨r₀, m₀, hr₀⟩ r' m' hr'
    obtain ⟨r₁, m₁, hr₁, hq₁⟩ := ih (hb.step hs) (inv_step hb hr₀ hs) r' m' hr'
    obtain ⟨r, m, hr, hq⟩ := back_step hb ⟨r₀, m₀, hr₀⟩ hs hr₁
    exact ⟨r, m, hr, .cons hq hq₁⟩

theorem Q_fwd {r r' : RState} {l : List MLabel} (h : LRun QStep r l r') :
    ∀ s m, Basic s.k s.U → Rel r m s.k s.U → ∃ s', LRun CStep s l s' := by
  induction h with
  | nil => exact fun s _ _ _ => ⟨s, .nil s⟩
  | cons hq _ ih =>
    intro s m hb hr
    obtain ⟨s₁, m₁, hs, hr₁⟩ := fwd hb hr hq
    obtain ⟨s', hs'⟩ := ih s₁ m₁ (hb.step hs) hr₁
    exact ⟨s', .cons hs hs'⟩

theorem Rel.init : Rel RState.init id CState.init.k CState.init.U := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [RState.init, CState.init, WComp.init]

theorem Rel.init_eq {r : RState} {m : ℕ → Tid} (h : Rel r m CState.init.k CState.init.U) :
    r = RState.init := by
  funext t; exact h.hI t (by simp [CState.init, WComp.init]) rfl

/-! ### The theorems -/

/-- The reference machine and `Q` have the same traces. -/
theorem traces_R_Q (l : List MLabel) :
    (∃ r, RRun RState.init l r) ↔ (∃ r, LRun QStep RState.init l r) :=
  ⟨fun ⟨r, h⟩ => ⟨r, h.toQRun⟩, fun ⟨r, h⟩ => ⟨r, QRun.toRRun h⟩⟩

/-- `Q` and the encoding `C` have the same traces. -/
theorem traces_Q_C (l : List MLabel) :
    (∃ r, LRun QStep RState.init l r) ↔ (∃ s, LRun CStep CState.init l s) := by
  constructor
  · rintro ⟨r, h⟩
    exact Q_fwd h CState.init id Basic.init Rel.init
  · rintro ⟨s, h⟩
    obtain ⟨-, r', m', hr'⟩ := inv_run h Basic.init ⟨_, _, Rel.init⟩
    obtain ⟨r, m, hr, hq⟩ := C_back h Basic.init ⟨_, _, Rel.init⟩ r' m' hr'
    rw [Rel.init_eq hr] at hq
    exact ⟨r', hq⟩

/-- **Faithfulness of the wait-set encoding** (without `signal`): the reference
wait-set semantics (JLS 17.2, with spurious removals) and the encoding `WComp`
have the same finite traces. -/
theorem traces_eq (l : List MLabel) :
    (∃ r, RRun RState.init l r) ↔ (∃ s, LRun CStep CState.init l s) :=
  (traces_R_Q l).trans (traces_Q_C l)



/-! ## `signal`: the first pending waiter, against a FIFO queue

For a condition of a lock (`await`, `signal`, `signalAll`; no `notify`). The
reference machine keeps the waiters in a FIFO queue (as the condition queue
of `AbstractQueuedSynchronizer`): `signal` removes the head (notified),
`signalAll` all, a silent spurious removal any member (un-notified). -/

inductive SLabel
  | wait (t : Tid)
  | signal
  | signalAll
  | resume (t : Tid) (notified : Bool)
  deriving DecidableEq, Repr

/-- A state of the FIFO reference: the queue and, for each thread, the cause
of its removal if it is removed and not resumed. -/
@[ext] structure SR where
  qu : List Tid
  gone : Tid → Option Bool

def SR.init : SR := ⟨[], fun _ => none⟩

inductive SRStep : SR → Option SLabel → SR → Prop
  | wait (s : SR) (t : Tid) : t ∉ s.qu → s.gone t = none →
      SRStep s (some (.wait t)) ⟨s.qu ++ [t], s.gone⟩
  | signalNone (s : SR) : s.qu = [] → SRStep s (some .signal) s
  | signalOne (s : SR) (h : Tid) (rest : List Tid) : s.qu = h :: rest →
      SRStep s (some .signal) ⟨rest, update s.gone h (some true)⟩
  | signalAll (s : SR) :
      SRStep s (some .signalAll) ⟨[], fun u => if u ∈ s.qu then some true else s.gone u⟩
  | spurious (s : SR) (u : Tid) : u ∈ s.qu →
      SRStep s none ⟨s.qu.erase u, update s.gone u (some false)⟩
  | resume (s : SR) (t : Tid) (b : Bool) : s.gone t = some b →
      SRStep s (some (.resume t b)) ⟨s.qu, update s.gone t none⟩

inductive SRRun : SR → List SLabel → SR → Prop
  | nil (s : SR) : SRRun s [] s
  | tau {s s₁ s₂ : SR} {l : List SLabel} : SRStep s none s₁ → SRRun s₁ l s₂ → SRRun s l s₂
  | step {s s₁ s₂ : SR} {x : SLabel} {l : List SLabel} :
      SRStep s (some x) s₁ → SRRun s₁ l s₂ → SRRun s (x :: l) s₂

/-- The FIFO reference with the spurious removal at the wait. -/
inductive SQStep : SR → SLabel → SR → Prop
  | wait (s : SR) (t : Tid) : t ∉ s.qu → s.gone t = none → SQStep s (.wait t) ⟨s.qu ++ [t], s.gone⟩
  | waitU (s : SR) (t : Tid) : t ∉ s.qu → s.gone t = none →
      SQStep s (.wait t) ⟨s.qu, update s.gone t (some false)⟩
  | signalNone (s : SR) : s.qu = [] → SQStep s .signal s
  | signalOne (s : SR) (h : Tid) (rest : List Tid) : s.qu = h :: rest →
      SQStep s .signal ⟨rest, update s.gone h (some true)⟩
  | signalAll (s : SR) :
      SQStep s .signalAll ⟨[], fun u => if u ∈ s.qu then some true else s.gone u⟩
  | resume (s : SR) (t : Tid) (b : Bool) : s.gone t = some b →
      SQStep s (.resume t b) ⟨s.qu, update s.gone t none⟩

theorem SQRun.toSRRun {s s' : SR} {l : List SLabel} (h : LRun SQStep s l s') : SRRun s l s' := by
  induction h with
  | nil s => exact .nil s
  | cons hs _ ih =>
    cases hs with
    | wait t h1 h2 => exact .step (.wait _ t h1 h2) ih
    | waitU t h1 h2 =>
      refine .step (.wait _ t h1 h2) (.tau (SRStep.spurious _ t (by simp)) ?_)
      simpa [List.erase_append_right _ h1] using ih
    | signalNone h => exact .step (.signalNone _ h) ih
    | signalOne h rest e => exact .step (.signalOne _ h rest e) ih
    | signalAll => exact .step (.signalAll _) ih
    | resume t b h => exact .step (.resume _ t b h) ih

/-- Invariant of the reference: the queue has no repetition and its members are
not removed. -/
def SR.Inv (s : SR) : Prop := s.qu.Nodup ∧ ∀ u ∈ s.qu, s.gone u = none

theorem SR.Inv.step {s s' : SR} {x : Option SLabel} (hi : s.Inv) (h : SRStep s x s') : s'.Inv := by
  obtain ⟨hnd, hq⟩ := hi
  cases h with
  | wait t h1 h2 =>
    try dsimp only [SR.Inv] at *
    refine ⟨?_, ?_⟩
    · rw [List.nodup_append]; refine ⟨hnd, by simp, ?_⟩
      intro a ha b hb e; simp only [List.mem_singleton] at hb; subst hb; subst e; exact h1 ha
    · intro u hu
      simp only [List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · exact hq u hu
      · exact h2
  | signalNone h => exact ⟨hnd, hq⟩
  | signalOne h rest e =>
    try dsimp only [SR.Inv] at *
    rw [e, List.nodup_cons] at hnd
    refine ⟨hnd.2, fun u hu => ?_⟩
    have : u ≠ h := fun e' => hnd.1 (e' ▸ hu)
    rw [update_of_ne this]; exact hq u (by rw [e]; exact List.mem_cons_of_mem _ hu)
  | signalAll => exact ⟨List.nodup_nil, by simp⟩
  | spurious u h =>
    try dsimp only [SR.Inv] at *
    refine ⟨hnd.erase u, fun v hv => ?_⟩
    have : v ≠ u := fun e => by
      rw [e] at hv; exact (List.Nodup.not_mem_erase hnd) hv
    rw [update_of_ne this]; exact hq v (List.mem_of_mem_erase hv)
  | resume t b h =>
    try dsimp only [SR.Inv] at *
    refine ⟨hnd, fun u hu => ?_⟩
    have : u ≠ t := fun e => by rw [e] at hu; rw [hq t hu] at h; cases h
    rw [update_of_ne this]; exact hq u hu

theorem filter_erase_of_not {l : List Tid} {p : Tid → Bool} {u : Tid} (hp : p u = false) :
    (l.erase u).filter p = l.filter p := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.erase_cons]
    by_cases hx : x = u
    · subst hx; simp [hp]
    · simp only [beq_iff_eq, hx, ite_false, List.filter_cons, ih]

/-- `q` is `r` in which some queued threads are already removed spuriously. -/
def Bs (r q : SR) : Prop :=
  (∀ u, q.gone u = r.gone u ∨ (u ∈ r.qu ∧ q.gone u = some false)) ∧
  q.qu = r.qu.filter (fun u => decide (q.gone u ≠ some false))

theorem Bs.back {r r₁ q₁ : SR} {x : Option SLabel} (hi : r.Inv) (hs : SRStep r x r₁)
    (hb : Bs r₁ q₁) : ∃ q, Bs r q ∧ (x = none → q = q₁) ∧ (∀ y, x = some y → SQStep q y q₁) := by
  obtain ⟨hnd, hqn⟩ := hi
  obtain ⟨hg, hqq⟩ := hb
  cases hs with
  | wait t h1 h2 =>
    rcases hg t with ht | ⟨-, ht⟩
    · -- `t` enters the queue of `Q` too
      refine ⟨⟨r.qu.filter (fun u => decide (q₁.gone u ≠ some false)), q₁.gone⟩, ⟨?_, rfl⟩,
        by simp, ?_⟩
      all_goals try dsimp only
      · intro u
        rcases hg u with h | ⟨hu, h⟩
        · exact .inl h
        · refine .inr ⟨?_, h⟩
          simp only [List.mem_append, List.mem_singleton] at hu
          rcases hu with hu | rfl
          · exact hu
          · rw [ht, h2] at h; cases h
      · rintro y ⟨⟩
        have e : q₁ = ⟨r.qu.filter (fun u => decide (q₁.gone u ≠ some false)) ++ [t], q₁.gone⟩ := by
          ext1
          · rw [hqq, List.filter_append]; simp [ht, h2]
          · rfl
        rw [e]
        refine .wait _ t (fun h => h1 (List.mem_of_mem_filter h)) ?_
        exact ht.trans h2
    · -- `t` is removed spuriously at once
      refine ⟨⟨q₁.qu, update q₁.gone t none⟩, ⟨?_, ?_⟩, by simp, ?_⟩
      all_goals try dsimp only
      · intro u
        by_cases e : u = t
        · rw [e, update_self]; exact .inl h2.symm
        · rw [update_of_ne e]
          rcases hg u with h | ⟨hu, h⟩
          · exact .inl h
          · refine .inr ⟨?_, h⟩
            simp only [List.mem_append, List.mem_singleton] at hu
            exact hu.resolve_right e
      · show q₁.qu = _
        rw [hqq, List.filter_append]
        simp only [ht, ne_eq, not_true_eq_false, decide_false, List.filter_cons, List.filter_nil,
          Bool.false_eq_true, ite_false, List.append_nil]
        apply List.filter_congr
        intro u hu
        have e : u ≠ t := fun e => h1 (e ▸ hu)
        simp [update_of_ne e]
      · rintro y ⟨⟩
        have hnq : t ∉ q₁.qu := by
          rw [hqq]; intro h; simpa [ht] using (List.mem_filter.1 h).2
        have := SQStep.waitU ⟨q₁.qu, update q₁.gone t none⟩ t hnq (by simp)
        simp only [update_idem] at this
        rwa [← ht, update_eq_self] at this
  | signalNone h =>
    refine ⟨q₁, ⟨hg, hqq⟩, by simp, ?_⟩
    rintro y ⟨⟩
    exact .signalNone _ (by rw [hqq, h]; rfl)
  | signalOne h rest e =>
    rw [e, List.nodup_cons] at hnd
    have hh : q₁.gone h = some true := by
      rcases hg h with h' | ⟨h', -⟩
      · rw [h']; simp
      · exact absurd h' hnd.1
    refine ⟨⟨h :: q₁.qu, update q₁.gone h none⟩, ⟨?_, ?_⟩, by simp, ?_⟩
    all_goals try dsimp only
    · intro u
      by_cases eu : u = h
      · rw [eu, update_self]; exact .inl (hqn h (by rw [e]; simp)).symm
      · rw [update_of_ne eu]
        rcases hg u with h' | ⟨hu, h'⟩
        · exact .inl (by rw [h']; exact update_of_ne eu _ _)
        · exact .inr ⟨by rw [e]; exact List.mem_cons_of_mem _ hu, h'⟩
    · show h :: q₁.qu = _
      rw [e, List.filter_cons]
      simp only [update_self, ne_eq, reduceCtorEq, not_false_eq_true, decide_true, ite_true]
      rw [hqq]
      congr 1
      apply List.filter_congr
      intro u hu
      have eu : u ≠ h := fun e' => hnd.1 (e' ▸ hu)
      simp [update_of_ne eu]
    · rintro y ⟨⟩
      have := SQStep.signalOne ⟨h :: q₁.qu, update q₁.gone h none⟩ h q₁.qu rfl
      simp only [update_idem] at this
      rwa [← hh, update_eq_self] at this
  | signalAll =>
    refine ⟨⟨r.qu, fun u => if u ∈ r.qu then none else q₁.gone u⟩, ⟨?_, ?_⟩, by simp, ?_⟩
    all_goals try dsimp only
    · intro u
      by_cases hu : u ∈ r.qu
      · simp only [hu, ite_true]; exact .inl (hqn u hu).symm
      · simp only [hu, ite_false]
        rcases hg u with h' | ⟨h', -⟩
        · exact .inl (by rw [h']; simp [hu])
        · simp at h'
    · show r.qu = _
      symm; rw [List.filter_eq_self]
      intro u hu; simp [hu]
    · rintro y ⟨⟩
      have key : (⟨[], fun u => if u ∈ r.qu then some true else
          (fun u => if u ∈ r.qu then none else q₁.gone u) u⟩ : SR) = q₁ := by
        ext1
        · rw [hqq]; rfl
        · funext u
          by_cases hu : u ∈ r.qu
          · simp only [hu, ite_true]
            rcases hg u with h' | ⟨h', -⟩
            · rw [h']; simp [hu]
            · simp at h'
          · simp [hu]
      have hst : SQStep ⟨r.qu, fun u => if u ∈ r.qu then none else q₁.gone u⟩ .signalAll
          ⟨[], fun u => if u ∈ r.qu then some true else
            (fun u => if u ∈ r.qu then none else q₁.gone u) u⟩ := SQStep.signalAll _
      rw [key] at hst; exact hst
  | spurious u h =>
    refine ⟨q₁, ⟨?_, ?_⟩, fun _ => rfl, by simp⟩
    · intro v
      by_cases e : v = u
      · rw [e]
        refine .inr ⟨h, ?_⟩
        rcases hg u with h' | ⟨-, h'⟩
        · rw [h']; simp
        · exact h'
      · rcases hg v with h' | ⟨hv, h'⟩
        · exact .inl (by rw [h']; exact update_of_ne e _ _)
        · exact .inr ⟨List.mem_of_mem_erase hv, h'⟩
    · rw [hqq]
      apply filter_erase_of_not
      have : q₁.gone u = some false := by
        rcases hg u with h' | ⟨-, h'⟩
        · rw [h']; simp
        · exact h'
      simp [this]
  | resume t b h =>
    have htq : t ∉ r.qu := fun ht => by rw [hqn t ht] at h; cases h
    have hq0 : q₁.gone t = none := by
      rcases hg t with h' | ⟨h', -⟩
      · rw [h']; simp
      · exact absurd h' htq
    refine ⟨⟨q₁.qu, update q₁.gone t (some b)⟩, ⟨?_, ?_⟩, by simp, ?_⟩
    all_goals try dsimp only
    · intro u
      by_cases e : u = t
      · rw [e, update_self]; exact .inl h.symm
      · rw [update_of_ne e]
        rcases hg u with h' | ⟨hu, h'⟩
        · exact .inl (by rw [h']; exact update_of_ne e _ _)
        · exact .inr ⟨hu, h'⟩
    · show q₁.qu = _
      rw [hqq]
      apply List.filter_congr
      intro u hu
      have e : u ≠ t := fun e => htq (e ▸ hu)
      simp [update_of_ne e]
    · rintro y ⟨⟩
      have := SQStep.resume ⟨q₁.qu, update q₁.gone t (some b)⟩ t b (by simp)
      simp only [update_idem] at this
      rwa [← hq0, update_eq_self] at this

theorem SRRun.inv {r r' : SR} {l : List SLabel} (h : SRRun r l r') (hi : r.Inv) : r'.Inv := by
  induction h with
  | nil => exact hi
  | tau hs _ ih => exact ih (hi.step hs)
  | step hs _ ih => exact ih (hi.step hs)

theorem SRRun.toQ {r r' : SR} {l : List SLabel} (h : SRRun r l r') :
    r.Inv → ∀ q', Bs r' q' → ∃ q, Bs r q ∧ LRun SQStep q l q' := by
  induction h with
  | nil s => exact fun _ q' hq => ⟨q', hq, .nil _⟩
  | tau hs _ ih =>
    intro hi q' hq'
    obtain ⟨q₁, hb₁, hr₁⟩ := ih (hi.step hs) q' hq'
    obtain ⟨q, hb, he, -⟩ := Bs.back hi hs hb₁
    exact ⟨q, hb, by rw [he rfl]; exact hr₁⟩
  | step hs _ ih =>
    intro hi q' hq'
    obtain ⟨q₁, hb₁, hr₁⟩ := ih (hi.step hs) q' hq'
    obtain ⟨q, hb, -, hst⟩ := Bs.back hi hs hb₁
    exact ⟨q, hb, .cons (hst _ rfl) hr₁⟩

theorem SR.Inv.init : SR.init.Inv := ⟨List.nodup_nil, by simp [SR.init]⟩

theorem traces_SR_SQ (l : List SLabel) :
    (∃ r, SRRun SR.init l r) ↔ (∃ r, LRun SQStep SR.init l r) := by
  constructor
  · rintro ⟨r', h⟩
    have hi := h.inv SR.Inv.init
    have hself : Bs r' r' := by
      refine ⟨fun u => .inl rfl, ?_⟩
      symm; rw [List.filter_eq_self]
      intro u hu; simp [hi.2 u hu]
    obtain ⟨q, hb, hq⟩ := h.toQ SR.Inv.init r' hself
    have : q = SR.init := by
      ext1
      · rw [hb.2]; rfl
      · funext u
        rcases hb.1 u with h' | ⟨h', -⟩
        · exact h'
        · simp [SR.init] at h'
    exact ⟨r', this ▸ hq⟩
  · rintro ⟨r, h⟩; exact ⟨r, SQRun.toSRRun h⟩


/-! ### The encoding with `signal` -/

inductive CSStep : CState → SLabel → CState → Prop
  | waitN (s : CState) (t : Tid) : t ∉ s.k.W.map Prod.fst → s.U t = false →
      CSStep s (.wait t) ⟨s.k.wait t, s.U⟩
  | waitU (s : CState) (t : Tid) : t ∉ s.k.W.map Prod.fst → s.U t = false →
      CSStep s (.wait t) ⟨s.k, update s.U t true⟩
  | signal (s : CState) : CSStep s .signal ⟨s.k.signal, s.U⟩
  | signalAll (s : CState) : CSStep s .signalAll ⟨s.k.notifyAll, s.U⟩
  | resumeN (s : CState) (t : Tid) (k' : WComp) : t ∈ s.k.W.map Prod.fst →
      s.k.exitN t = some k' → CSStep s (.resume t true) ⟨k', s.U⟩
  | resumeU (s : CState) (t : Tid) : s.U t = true →
      CSStep s (.resume t false) ⟨s.k, update s.U t false⟩

structure Basic2 (k : WComp) (U : Tid → Bool) : Prop where
  T_nil : k.T = []
  nodup : (k.W.map Prod.fst).Nodup
  a_le : k.a ≤ k.c
  g_le : ∀ w ∈ k.W, w.2 ≤ k.c
  S_nodup : k.S.Nodup
  S_sub : ∀ u ∈ k.S, ∃ g, (u, g) ∈ k.W ∧ k.a ≤ g
  disj : ∀ t, U t = true → t ∉ k.W.map Prod.fst

/-- The reference state of a state of the encoding: the queue is the list of
pending waiters; a waiter of `W` that is not pending is removed, notified. -/
def absS (k : WComp) (U : Tid → Bool) : SR :=
  ⟨k.pending.map Prod.fst, fun u => if U u = true then some false
    else if u ∈ k.W.map Prod.fst ∧ u ∉ k.pending.map Prod.fst then some true else none⟩

section Signal

variable {k : WComp} {U : Tid → Bool}

theorem mem_pm {u : Tid} : u ∈ k.pending.map Prod.fst ↔ ∃ g, (u, g) ∈ k.W ∧ k.a ≤ g ∧ u ∉ k.S := by
  simp [WComp.pending]

theorem pm_sub {u : Tid} (h : u ∈ k.pending.map Prod.fst) : u ∈ k.W.map Prod.fst := by
  obtain ⟨g, hg, -⟩ := mem_pm.1 h; exact mem_fst.2 ⟨g, hg⟩

theorem Basic2.pm_nodup (hb : Basic2 k U) : (k.pending.map Prod.fst).Nodup :=
  hb.nodup.sublist (List.filter_sublist.map _)

theorem Basic2.not_S {t : Tid} (hb : Basic2 k U) (ht : t ∉ k.W.map Prod.fst) : t ∉ k.S := by
  intro h; obtain ⟨g, hg, -⟩ := hb.S_sub t h; exact ht (mem_fst.2 ⟨g, hg⟩)

theorem Basic2.uniq' (hb : Basic2 k U) {t : Tid} {g₁ g₂ : ℕ}
    (h₁ : (t, g₁) ∈ k.W) (h₂ : (t, g₂) ∈ k.W) : g₁ = g₂ :=
  (Prod.mk.inj (List.inj_on_of_nodup_map hb.nodup h₁ h₂ rfl)).2

theorem entry_of_nodup {t : Tid} {g : ℕ} (hnd : (k.W.map Prod.fst).Nodup) (h : (t, g) ∈ k.W) :
    k.entry t = g := by
  simp [WComp.entry, find_of_mem hnd h]

theorem P_wait (hb : Basic2 k U) {t : Tid} (ht : t ∉ k.W.map Prod.fst) :
    (k.wait t).pending = k.pending ++ [(t, k.c)] := by
  have htS := hb.not_S ht
  change (k.W ++ [(t, k.c)]).filter (fun w => decide (k.a ≤ w.2 ∧ w.1 ∉ k.S)) =
    k.W.filter (fun w => decide (k.a ≤ w.2 ∧ w.1 ∉ k.S)) ++ [(t, k.c)]
  rw [List.filter_append]
  congr 1
  simp [hb.a_le, htS]

theorem P_signal (hb : Basic2 k U) {w : Tid × ℕ} {rest : List (Tid × ℕ)}
    (hP : k.pending = w :: rest) : ({ k with S := k.S ++ [w.1] } : WComp).pending = rest := by
  have hnd : ((w :: rest).map Prod.fst).Nodup := hP ▸ hb.pm_nodup
  simp only [List.map_cons, List.nodup_cons] at hnd
  have hfun : (fun x : Tid × ℕ => decide (k.a ≤ x.2 ∧ x.1 ∉ k.S ++ [w.1])) =
      fun x => decide (x.1 ≠ w.1) && decide (k.a ≤ x.2 ∧ x.1 ∉ k.S) := by
    funext x
    by_cases h1 : x.1 = w.1 <;> by_cases h2 : x.1 ∈ k.S <;> by_cases h3 : k.a ≤ x.2 <;>
      simp [h1, h2, h3]
  change k.W.filter (fun x => decide (k.a ≤ x.2 ∧ x.1 ∉ k.S ++ [w.1])) = rest
  rw [hfun, ← List.filter_filter]
  change k.pending.filter _ = rest
  rw [hP, List.filter_cons]
  simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false]
  rw [List.filter_eq_self]
  intro x hx
  have : x.1 ≠ w.1 := fun e => hnd.1 (e ▸ List.mem_map_of_mem hx)
  simp [this]

theorem P_nA (hb : Basic2 k U) : k.notifyAll.pending = [] := by
  rw [WComp.pending, List.filter_eq_nil_iff]
  intro x hx
  have := hb.g_le x hx
  intro hx'
  have h' := of_decide_eq_true hx'
  exact absurd h'.1 (by simp only [WComp.notifyAll]; omega)

theorem P_drop (_hb : Basic2 k U) {t : Tid} (htp : t ∉ k.pending.map Prod.fst) (S' : List Tid)
    (hS' : ∀ u, u ≠ t → (u ∈ S' ↔ u ∈ k.S)) :
    ({ k with S := S', W := k.drop t } : WComp).pending = k.pending := by
  simp only [WComp.pending, WComp.drop]
  rw [List.filter_filter]
  apply List.filter_congr
  intro x hx
  by_cases e : x.1 = t
  · have : ¬ (k.a ≤ x.2 ∧ x.1 ∉ k.S) := fun h =>
      htp (mem_pm.2 ⟨x.2, by rw [← e]; exact hx, h.1, by rw [← e]; exact h.2⟩)
    have h' : k.a ≤ x.2 → t ∈ k.S := fun h => by
      by_contra h2; exact this ⟨h, by rw [e]; exact h2⟩
    simp only [e, ne_eq, not_true_eq_false, decide_false, Bool.and_false]
    simp only [Bool.false_eq, decide_eq_false_iff_not, not_and, not_not]
    exact h'
  · have := hS' x.1 e
    simp [e, this]

theorem E_lt (hb : Basic2 k U) {t : Tid} {g : ℕ} (h : (t, g) ∈ k.W) (hg : g < k.a) :
    k.exitN t = some { k with W := k.drop t } := by
  simp [WComp.exitN, entry_of_nodup hb.nodup h, hg]

theorem E_S (hb : Basic2 k U) {t : Tid} {g : ℕ} (h : (t, g) ∈ k.W) (hg : k.a ≤ g)
    (hS : t ∈ k.S) : k.exitN t = some { k with S := k.S.erase t, W := k.drop t } := by
  simp [WComp.exitN, entry_of_nodup hb.nodup h, not_lt.2 hg, hS]

theorem E_none (hb : Basic2 k U) {t : Tid} {g : ℕ} (h : (t, g) ∈ k.W) (hg : k.a ≤ g)
    (hS : t ∉ k.S) : k.exitN t = none := by
  simp [WComp.exitN, entry_of_nodup hb.nodup h, not_lt.2 hg, hS, hb.T_nil]

theorem Basic2.init : Basic2 CState.init.k CState.init.U where
  T_nil := rfl
  nodup := by simp [CState.init, WComp.init]
  a_le := le_rfl
  g_le := by simp [CState.init, WComp.init]
  S_nodup := by simp [CState.init, WComp.init]
  S_sub := by simp [CState.init, WComp.init]
  disj := by simp [CState.init]

end Signal

theorem Basic2.step {s s' : CState} {x : SLabel} (hb : Basic2 s.k s.U) (h : CSStep s x s') :
    Basic2 s'.k s'.U := by
  cases h with
  | waitN t ht hU =>
    refine ⟨hb.T_nil, ?_, hb.a_le, ?_, hb.S_nodup, ?_, ?_⟩
    · simp only [WComp.wait, List.map_append, List.map_cons, List.map_nil]
      rw [List.nodup_append]
      refine ⟨hb.nodup, by simp, ?_⟩
      intro a ha b hb' e
      simp only [List.mem_singleton] at hb'
      subst hb'; subst e; exact ht ha
    · intro w hw
      simp only [WComp.wait, List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact hb.g_le w hw
      · exact le_rfl
    · intro u hu
      obtain ⟨g, hg, ha⟩ := hb.S_sub u hu
      exact ⟨g, List.mem_append_left _ hg, ha⟩
    · intro u hu
      simp only [WComp.wait, List.map_append, List.mem_append, List.map_cons, List.map_nil,
        List.mem_singleton, not_or]
      refine ⟨hb.disj u hu, ?_⟩
      rintro rfl; rw [hU] at hu; cases hu
  | waitU t ht hU =>
    refine ⟨hb.T_nil, hb.nodup, hb.a_le, hb.g_le, hb.S_nodup, hb.S_sub, ?_⟩
    intro u hu
    by_cases hut : u = t
    · subst hut; exact ht
    · exact hb.disj u (by simpa [hut] using hu)
  | signal =>
    unfold WComp.signal
    split
    · rename_i w hw
      obtain ⟨tl, htl⟩ := List.head?_eq_some_iff.1 hw
      have hwP : w ∈ s.k.pending := by rw [htl]; exact List.mem_cons_self
      rw [WComp.pending, List.mem_filter] at hwP
      simp only [decide_eq_true_eq] at hwP
      refine ⟨hb.T_nil, hb.nodup, hb.a_le, hb.g_le, ?_, ?_, hb.disj⟩
      · simp only
        rw [List.nodup_append]
        refine ⟨hb.S_nodup, by simp, ?_⟩
        intro a ha b hb' e
        simp only [List.mem_singleton] at hb'
        subst hb'; subst e; exact hwP.2.2 ha
      · intro u hu
        simp only [List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · exact hb.S_sub u hu
        · exact ⟨w.2, hwP.1, hwP.2.1⟩
    · exact hb
  | signalAll =>
    refine ⟨rfl, hb.nodup, le_rfl, fun w hw => Nat.le_succ_of_le (hb.g_le w hw),
      by simp [WComp.notifyAll], by simp [WComp.notifyAll], hb.disj⟩
  | resumeN t k' hm hex =>
    obtain ⟨g, hg⟩ := mem_fst.1 hm
    have hsub : ((s.k.drop t).map Prod.fst).Sublist (s.k.W.map Prod.fst) :=
      (List.filter_sublist).map _
    by_cases hlt : g < s.k.a
    · rw [E_lt hb hg hlt] at hex; cases hex
      refine ⟨hb.T_nil, hb.nodup.sublist hsub, hb.a_le,
        fun w hw => hb.g_le w (List.filter_sublist.subset hw), hb.S_nodup, ?_,
        fun u hu hu' => hb.disj u hu (hsub.subset hu')⟩
      intro u hu
      obtain ⟨g', hg', ha⟩ := hb.S_sub u hu
      refine ⟨g', mem_drop.2 ⟨hg', ?_⟩, ha⟩
      rintro rfl; have := hb.uniq' hg' hg; omega
    · by_cases hS : t ∈ s.k.S
      · rw [E_S hb hg (not_lt.1 hlt) hS] at hex; cases hex
        refine ⟨hb.T_nil, hb.nodup.sublist hsub, hb.a_le,
          fun w hw => hb.g_le w (List.filter_sublist.subset hw), hb.S_nodup.erase t, ?_,
          fun u hu hu' => hb.disj u hu (hsub.subset hu')⟩
        intro u hu
        rw [hb.S_nodup.mem_erase_iff] at hu
        obtain ⟨g', hg', ha⟩ := hb.S_sub u hu.2
        exact ⟨g', mem_drop.2 ⟨hg', hu.1⟩, ha⟩
      · rw [E_none hb hg (not_lt.1 hlt) hS] at hex; cases hex
  | resumeU t hU =>
    refine ⟨hb.T_nil, hb.nodup, hb.a_le, hb.g_le, hb.S_nodup, hb.S_sub, ?_⟩
    intro u hu
    by_cases hut : u = t
    · subst hut; simp at hu
    · exact hb.disj u (by simpa [hut] using hu)


section Abs

variable {k : WComp} {U : Tid → Bool}

theorem gone_st {t : Tid} (h : (absS k U).gone t = some true) :
    U t = false ∧ t ∈ k.W.map Prod.fst ∧ t ∉ k.pending.map Prod.fst := by
  simp only [absS] at h
  split_ifs at h with h1 h2 <;> (try cases h)
  exact ⟨by simpa using h1, h2.1, h2.2⟩

theorem gone_sf {t : Tid} (h : (absS k U).gone t = some false) : U t = true := by
  simp only [absS] at h
  split_ifs at h with h1 h2 <;> (try cases h)
  exact h1

theorem gone_none {t : Tid} (h : (absS k U).gone t = none) :
    U t = false ∧ (t ∈ k.W.map Prod.fst → t ∈ k.pending.map Prod.fst) := by
  simp only [absS] at h
  split_ifs at h with h1 h2
  try cases h
  exact ⟨by simpa using h1, fun hm => by by_contra hp; exact h2 ⟨hm, hp⟩⟩

theorem abs_waitN (hb : Basic2 k U) {t : Tid} (ht : t ∉ k.W.map Prod.fst) (hU : U t = false) :
    absS (k.wait t) U = ⟨(absS k U).qu ++ [t], (absS k U).gone⟩ := by
  ext1
  · simp [absS, P_wait hb ht]
  · funext u
    simp only [absS, P_wait hb ht]
    by_cases e : u = t
    · subst e
      have : u ∉ k.pending.map Prod.fst := fun h => ht (pm_sub h)
      simp [hU, ht, WComp.wait]
    · have h1 : u ∈ (k.wait t).W.map Prod.fst ↔ u ∈ k.W.map Prod.fst := by simp [WComp.wait, e]
      have h2 : u ∈ (k.pending ++ [(t, k.c)]).map Prod.fst ↔ u ∈ k.pending.map Prod.fst := by
        simp [e]
      simp only [h1, h2]

theorem abs_waitU {t : Tid} :
    absS k (update U t true) = ⟨(absS k U).qu, update (absS k U).gone t (some false)⟩ := by
  ext1
  · rfl
  · funext u
    by_cases e : u = t
    · subst e; simp [absS]
    · simp [absS, e]

theorem abs_sig (hb : Basic2 k U) {w : Tid × ℕ} {rest : List (Tid × ℕ)}
    (hP : k.pending = w :: rest) :
    absS { k with S := k.S ++ [w.1] } U =
      ⟨rest.map Prod.fst, update (absS k U).gone w.1 (some true)⟩ := by
  ext1
  · simp [absS, P_signal hb hP]
  · funext u
    have hw : w.1 ∈ k.W.map Prod.fst := pm_sub (by rw [hP]; simp)
    have hnd : ((w :: rest).map Prod.fst).Nodup := hP ▸ hb.pm_nodup
    simp only [List.map_cons, List.nodup_cons] at hnd
    by_cases e : u = w.1
    · subst e
      have hU : U w.1 = false := by
        cases h : U w.1
        · rfl
        · exact absurd hw (hb.disj _ h)
      simp [absS, P_signal hb hP, hU, hw, hnd.1]
    · change _ = update (absS k U).gone w.1 (some true) u
      rw [update_of_ne e]
      simp only [absS, P_signal hb hP, hP, List.map_cons, List.mem_cons, e, false_or]

theorem abs_nA (hb : Basic2 k U) :
    absS k.notifyAll U =
      ⟨[], fun u => if u ∈ (absS k U).qu then some true else (absS k U).gone u⟩ := by
  ext1
  · simp [absS, P_nA hb]
  · funext u
    by_cases hu : u ∈ k.pending.map Prod.fst
    · have hU : U u = false := by
        cases h : U u
        · rfl
        · exact absurd (pm_sub hu) (hb.disj _ h)
      simp only [absS, P_nA hb]
      simp [hu, hU, pm_sub hu, show k.notifyAll.W = k.W from rfl]
    · simp only [absS, P_nA hb]
      simp only [WComp.notifyAll]
      simp only [hu, List.map_nil, List.not_mem_nil, not_false_eq_true, and_true, ↓reduceIte]

theorem abs_drop (hb : Basic2 k U) {t : Tid} {g : ℕ} (ht : (t, g) ∈ k.W)
    (htp : t ∉ k.pending.map Prod.fst) (S' : List Tid) (hS' : ∀ u, u ≠ t → (u ∈ S' ↔ u ∈ k.S)) :
    absS { k with S := S', W := k.drop t } U =
      ⟨(absS k U).qu, update (absS k U).gone t none⟩ := by
  ext1
  · simp only [absS, P_drop hb htp S' hS']
  · funext u
    have hU : U t = false := by
      cases h : U t
      · rfl
      · exact absurd (mem_fst.2 ⟨g, ht⟩) (hb.disj _ h)
    by_cases e : u = t
    · subst e
      have : u ∉ (k.drop u).map Prod.fst := fun h => (mem_fst_drop.1 h).2 rfl
      simp [absS, hU, this]
    · change _ = update (absS k U).gone t none u
      rw [update_of_ne e]
      have : u ∈ (k.drop t).map Prod.fst ↔ u ∈ k.W.map Prod.fst := by
        rw [mem_fst_drop]; simp [e]
      simp only [absS, P_drop hb htp S' hS', this]

theorem abs_resumeU (hb : Basic2 k U) {t : Tid} (hU : U t = true) :
    absS k (update U t false) = ⟨(absS k U).qu, update (absS k U).gone t none⟩ := by
  ext1
  · rfl
  · funext u
    by_cases e : u = t
    · subst e; simp [absS, hb.disj u hU]
    · simp [absS, e]

end Abs

theorem bwdS {s s' : CState} {x : SLabel} (hb : Basic2 s.k s.U) (h : CSStep s x s') :
    SQStep (absS s.k s.U) x (absS s'.k s'.U) := by
  cases h with
  | waitN t ht hU =>
    dsimp only
    rw [abs_waitN hb ht hU]
    exact .wait _ t (fun h => ht (pm_sub h)) (by simp [absS, hU, ht])
  | waitU t ht hU =>
    dsimp only
    rw [abs_waitU]
    exact .waitU _ t (fun h => ht (pm_sub h)) (by simp [absS, hU, ht])
  | signal =>
    dsimp only
    cases hP : s.k.pending with
    | nil =>
      rw [show s.k.signal = s.k by simp [WComp.signal, hP]]
      exact .signalNone _ (by simp [absS, hP])
    | cons w rest =>
      rw [show s.k.signal = { s.k with S := s.k.S ++ [w.1] } by simp [WComp.signal, hP],
        abs_sig hb hP]
      exact .signalOne _ w.1 (rest.map Prod.fst) (by simp [absS, hP])
  | signalAll => dsimp only; rw [abs_nA hb]; exact .signalAll _
  | resumeN t k' hm hex =>
    obtain ⟨g, hg⟩ := mem_fst.1 hm
    have hU : s.U t = false := by
      cases h : s.U t
      · rfl
      · exact absurd hm (hb.disj _ h)
    have key : ∃ S', (∀ u, u ≠ t → (u ∈ S' ↔ u ∈ s.k.S)) ∧ t ∉ s.k.pending.map Prod.fst ∧
        k' = { s.k with S := S', W := s.k.drop t } := by
      by_cases hlt : g < s.k.a
      · rw [E_lt hb hg hlt] at hex; cases hex
        refine ⟨s.k.S, fun _ _ => Iff.rfl, fun h => ?_, rfl⟩
        obtain ⟨g', hg', ha, -⟩ := mem_pm.1 h; have := hb.uniq' hg hg'; omega
      · by_cases hS : t ∈ s.k.S
        · rw [E_S hb hg (not_lt.1 hlt) hS] at hex; cases hex
          refine ⟨s.k.S.erase t, fun u hu => ?_, fun h => ?_, rfl⟩
          · rw [hb.S_nodup.mem_erase_iff]; simp [hu]
          · obtain ⟨_, _, _, hS'⟩ := mem_pm.1 h; exact hS' hS
        · rw [E_none hb hg (not_lt.1 hlt) hS] at hex; cases hex
    obtain ⟨S', hS', htp, rfl⟩ := key
    dsimp only
    rw [abs_drop hb hg htp S' hS']
    exact .resume _ t true (by simp [absS, hU, hm, htp])
  | resumeU t hU =>
    dsimp only; rw [abs_resumeU hb hU]
    exact .resume _ t false (by simp [absS, hU])

theorem fwdS {s : CState} {q' : SR} {x : SLabel} (hb : Basic2 s.k s.U)
    (h : SQStep (absS s.k s.U) x q') : ∃ s', CSStep s x s' ∧ q' = absS s'.k s'.U := by
  generalize hq : absS s.k s.U = q at h
  cases h with
  | wait t h1 h2 =>
    subst hq
    obtain ⟨hU, hW⟩ := gone_none h2
    have ht : t ∉ s.k.W.map Prod.fst := fun h => h1 (hW h)
    exact ⟨_, .waitN s t ht hU, (abs_waitN hb ht hU).symm⟩
  | waitU t h1 h2 =>
    subst hq
    obtain ⟨hU, hW⟩ := gone_none h2
    have ht : t ∉ s.k.W.map Prod.fst := fun h => h1 (hW h)
    exact ⟨_, .waitU s t ht hU, abs_waitU.symm⟩
  | signalNone h =>
    subst hq
    have hP : s.k.pending = [] := List.map_eq_nil_iff.1 h
    refine ⟨_, .signal s, ?_⟩
    dsimp only
    rw [show s.k.signal = s.k by simp [WComp.signal, hP]]
  | signalOne h rest e =>
    subst hq
    obtain ⟨w, prest, hP, hw, hr⟩ : ∃ w prest, s.k.pending = w :: prest ∧ w.1 = h ∧
        prest.map Prod.fst = rest := by
      cases hP : s.k.pending with
      | nil => simp [absS, hP] at e
      | cons w prest =>
        simp only [absS, hP, List.map_cons, List.cons.injEq] at e
        exact ⟨w, prest, rfl, e.1, e.2⟩
    refine ⟨_, .signal s, ?_⟩
    dsimp only
    rw [show s.k.signal = { s.k with S := s.k.S ++ [w.1] } by simp [WComp.signal, hP],
      abs_sig hb hP, hw, hr]
  | signalAll => subst hq; exact ⟨_, .signalAll s, (abs_nA hb).symm⟩
  | resume t b h =>
    subst hq
    cases b with
    | true =>
      obtain ⟨hU, hm, htp⟩ := gone_st h
      obtain ⟨g, hg⟩ := mem_fst.1 hm
      by_cases hlt : g < s.k.a
      · refine ⟨_, .resumeN s t _ hm (E_lt hb hg hlt), ?_⟩
        dsimp only
        rw [abs_drop hb hg htp s.k.S (fun _ _ => Iff.rfl)]
      · have hS : t ∈ s.k.S := by
          by_contra hS; exact htp (mem_pm.2 ⟨g, hg, not_lt.1 hlt, hS⟩)
        refine ⟨_, .resumeN s t _ hm (E_S hb hg (not_lt.1 hlt) hS), ?_⟩
        dsimp only
        rw [abs_drop hb hg htp (s.k.S.erase t)
          (fun u hu => by rw [hb.S_nodup.mem_erase_iff]; simp [hu])]
    | false =>
      have hU := gone_sf h
      exact ⟨_, .resumeU s t hU, (abs_resumeU hb hU).symm⟩

theorem CS_run {s s' : CState} {l : List SLabel} (h : LRun CSStep s l s') :
    Basic2 s.k s.U → LRun SQStep (absS s.k s.U) l (absS s'.k s'.U) := by
  induction h with
  | nil => exact fun _ => .nil _
  | cons hs _ ih => exact fun hb => .cons (bwdS hb hs) (ih (hb.step hs))

theorem SQ_run {q q' : SR} {l : List SLabel} (h : LRun SQStep q l q') :
    ∀ s : CState, Basic2 s.k s.U → q = absS s.k s.U → ∃ s', LRun CSStep s l s' := by
  induction h with
  | nil => exact fun s _ _ => ⟨s, .nil s⟩
  | cons hq _ ih =>
    intro s hb e
    subst e
    obtain ⟨s₁, hs, e₁⟩ := fwdS hb hq
    obtain ⟨s', h'⟩ := ih s₁ (hb.step hs) e₁
    exact ⟨s', .cons hs h'⟩

theorem absS_init : absS CState.init.k CState.init.U = SR.init := by
  ext1
  · rfl
  · funext u; simp [absS, CState.init, WComp.init, SR.init]

theorem traces_SQ_CS (l : List SLabel) :
    (∃ r, LRun SQStep SR.init l r) ↔ (∃ s, LRun CSStep CState.init l s) := by
  constructor
  · rintro ⟨r, h⟩; exact SQ_run h CState.init Basic2.init absS_init.symm
  · rintro ⟨s, h⟩
    have := CS_run h Basic2.init
    rw [absS_init] at this
    exact ⟨_, this⟩

/-- **Faithfulness of `signal`**: the FIFO reference (condition queue; `signal`
removes the head, `signalAll` all, spurious removals anywhere) and the encoding
with `WComp.signal` and `WComp.notifyAll` have the same finite traces. -/
theorem traces_eq_signal (l : List SLabel) :
    (∃ r, SRRun SR.init l r) ↔ (∃ s, LRun CSStep CState.init l s) :=
  (traces_SR_SQ l).trans (traces_SQ_CS l)

end MonSpec

end Condpor
