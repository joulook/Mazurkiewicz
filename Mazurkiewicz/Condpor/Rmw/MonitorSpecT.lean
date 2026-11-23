import Mazurkiewicz.Condpor.Rmw.MonitorSpecB

/-!
# Timed waits for the wait-set encoding

Extends `MonitorSpecB.lean` (one wait set, per-thread budgets) with timed waits
(MODEL Sections 1, 4, 5). A wait is timed or not (`wait t timed`); it returns
notified, spuriously or by time-out (`resume t o`). Two budgets per thread:
`ks` (spurious returns of any wait) and `kt` (time-outs of timed waits).

* Reference `RTStep` (JLS 17.2 with time-outs): a thread is idle, waiting (with
  its timed flag), or removed and not yet resumed (with the cause). Silent
  removals: spurious (any waiter, needs `0 < ks u`, consumes one unit) and
  time-out (a timed waiter, needs `0 < kt u`, consumes one unit).
* Encoding `CTStep`: the machine `C` of `MonitorSpec.lean` (the `WComp` part is
  unchanged), with the timed flag of the current wait (`tm`) and the cause of an
  un-notified outcome (`tOut`, `true` = timed out). A wait first fixes its outcome
  (MODEL Section 4): by notification (enters `W`), spurious (needs and consumes
  `ks`), or timed out (timed waits only, needs and consumes `kt`).
* `traces_eq_timed Ks Kt`: equal traces from the initial states, for every pair
  of budgets. `stuck_eq_timed`: equal quiescent endpoints, where the observation
  is the trace, both final budgets and the untimed and timed waiters left.
* The same for `signal` (FIFO reference): `traces_eq_signal_timed`,
  `stuck_eq_signal_timed`; and `stuck_eq_signal` (unbounded, no time-outs).

Proof: as in `MonitorSpecB`, through an intermediate machine `QTStep` (the
removal done at the wait), by a backward simulation `BT` with one budget
equation per cause; `QTStep` and `CTStep` are related by `Rel` of
`MonitorSpec.lean` through the decoration `lift` (reusing `fwd`, `back_step`
and the `H_*` lemmas). For `signal`, `BST` and the abstraction `absT` (reusing
`bwdS`, `fwdS` and the `abs_*` lemmas).

Reading MODEL Section 5 off `stuck_eq_timed` (observation `Xu`, `Xt`, final
`κs`, `κt`): `Xu` are the untimed waiters without a notification (deadlock);
the `t ∈ Xt` with `κt t = 0` are the timed waiters that can no longer time out
(bound reached); the `t ∈ Xt` with `0 < κt t` still have a time-out step in the
reference (`quietT_tau`), so the endpoint is not final there.
-/

namespace Condpor

namespace MonSpec

open Function

/-! ## Labels and the reference machine -/

/-- The outcome of a wait. -/
inductive Outcome
  | notified
  | spurious
  | timedOut
  deriving DecidableEq, Repr

/-- Visible labels with timed waits (`notify`). -/
inductive TLabel
  | wait (t : Tid) (timed : Bool)
  | notify
  | notifyAll
  | resume (t : Tid) (o : Outcome)
  deriving DecidableEq, Repr

/-- The state of a thread in the timed reference. -/
inductive TS
  | idle
  | waiting (timed : Bool)
  | removed (o : Outcome)
  deriving DecidableEq, Repr

/-- The thread is in the wait set. -/
def TS.isW : TS → Bool
  | .waiting _ => true
  | _ => false

@[simp] theorem TS.isW_idle : TS.idle.isW = false := rfl
@[simp] theorem TS.isW_waiting (τ : Bool) : (TS.waiting τ).isW = true := rfl
@[simp] theorem TS.isW_removed (o : Outcome) : (TS.removed o).isW = false := rfl

theorem TS.not_isW_removed {a : TS} {o : Outcome} : ¬ (a.isW = true ∧ a = .removed o) := by
  rintro ⟨h1, rfl⟩; cases h1

theorem TS.ne_removed_of_isW {a : TS} {o : Outcome} (h : a.isW = true) : a ≠ .removed o :=
  fun e => TS.not_isW_removed ⟨h, e⟩

abbrev RTState := Tid → TS

def RTState.init : RTState := fun _ => .idle

def RTState.removeAll (s : RTState) : RTState :=
  fun u => if (s u).isW = true then .removed .notified else s u

/-- A state of the timed reference with the budgets of spurious returns and of
time-outs. -/
abbrev RT := RTState × Bud × Bud

/-- The timed reference; `none` is a silent removal (spurious or time-out). -/
inductive RTStep : RT → Option TLabel → RT → Prop
  | wait (s : RTState) (ks kt : Bud) (t : Tid) (τ : Bool) : s t = .idle →
      RTStep (s, ks, kt) (some (.wait t τ)) (update s t (.waiting τ), ks, kt)
  | notifyNone (s : RTState) (ks kt : Bud) : (∀ u, (s u).isW = false) →
      RTStep (s, ks, kt) (some .notify) (s, ks, kt)
  | notifyOne (s : RTState) (ks kt : Bud) (u : Tid) : (s u).isW = true →
      RTStep (s, ks, kt) (some .notify) (update s u (.removed .notified), ks, kt)
  | notifyAll (s : RTState) (ks kt : Bud) :
      RTStep (s, ks, kt) (some .notifyAll) (s.removeAll, ks, kt)
  | spurious (s : RTState) (ks kt : Bud) (u : Tid) : (s u).isW = true → 0 < ks u →
      RTStep (s, ks, kt) none (update s u (.removed .spurious), update ks u (ks u - 1), kt)
  | timeout (s : RTState) (ks kt : Bud) (u : Tid) : s u = .waiting true → 0 < kt u →
      RTStep (s, ks, kt) none (update s u (.removed .timedOut), ks, update kt u (kt u - 1))
  | resume (s : RTState) (ks kt : Bud) (t : Tid) (o : Outcome) : s t = .removed o →
      RTStep (s, ks, kt) (some (.resume t o)) (update s t .idle, ks, kt)

/-- The intermediate machine: the removal is done at the wait (proof device). -/
inductive QTStep : RT → TLabel → RT → Prop
  | wait (s : RTState) (ks kt : Bud) (t : Tid) (τ : Bool) : s t = .idle →
      QTStep (s, ks, kt) (.wait t τ) (update s t (.waiting τ), ks, kt)
  | waitS (s : RTState) (ks kt : Bud) (t : Tid) (τ : Bool) : s t = .idle → 0 < ks t →
      QTStep (s, ks, kt) (.wait t τ) (update s t (.removed .spurious), update ks t (ks t - 1), kt)
  | waitT (s : RTState) (ks kt : Bud) (t : Tid) : s t = .idle → 0 < kt t →
      QTStep (s, ks, kt) (.wait t true)
        (update s t (.removed .timedOut), ks, update kt t (kt t - 1))
  | notifyNone (s : RTState) (ks kt : Bud) : (∀ u, (s u).isW = false) →
      QTStep (s, ks, kt) .notify (s, ks, kt)
  | notifyOne (s : RTState) (ks kt : Bud) (u : Tid) : (s u).isW = true →
      QTStep (s, ks, kt) .notify (update s u (.removed .notified), ks, kt)
  | notifyAll (s : RTState) (ks kt : Bud) : QTStep (s, ks, kt) .notifyAll (s.removeAll, ks, kt)
  | resume (s : RTState) (ks kt : Bud) (t : Tid) (o : Outcome) : s t = .removed o →
      QTStep (s, ks, kt) (.resume t o) (update s t .idle, ks, kt)

/-! ### `Q` ⊆ `R` -/

theorem QTRun.toRT {p p' : RT} {l : List TLabel} (h : LRun QTStep p l p') :
    TRun RTStep p l p' := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih =>
    cases hs with
    | wait s ks kt t τ h => exact .step (.wait _ _ _ t τ h) ih
    | waitS s ks kt t τ h hb =>
      refine .step (.wait _ _ _ t τ h) (.tau (RTStep.spurious _ _ _ t (by simp) hb) ?_)
      simpa using ih
    | waitT s ks kt t h hb =>
      refine .step (.wait _ _ _ t true h) (.tau (RTStep.timeout _ _ _ t (by simp) hb) ?_)
      simpa using ih
    | notifyNone s ks kt h => exact .step (.notifyNone _ _ _ h) ih
    | notifyOne s ks kt u h => exact .step (.notifyOne _ _ _ u h) ih
    | notifyAll => exact .step (.notifyAll _ _ _) ih
    | resume s ks kt t o h => exact .step (.resume _ _ _ t o h) ih

/-! ### `R` ⊆ `Q`: a backward simulation; one budget equation per cause -/

/-- `b` is `a`, or `a` is waiting and `b` already removed spuriously, or `a` is a
timed waiter and `b` already timed out. -/
def bt (a b : TS) : Prop :=
  a = b ∨ (a.isW = true ∧ b = .removed .spurious) ∨ (a = .waiting true ∧ b = .removed .timedOut)

def iS (r q : RTState) (t : Tid) : ℕ :=
  if (r t).isW = true ∧ q t = .removed .spurious then 1 else 0

def iT (r q : RTState) (t : Tid) : ℕ :=
  if (r t).isW = true ∧ q t = .removed .timedOut then 1 else 0

def BT (p p' : RT) : Prop :=
  (∀ t, bt (p.1 t) (p'.1 t)) ∧ (∀ t, p.2.1 t = p'.2.1 t + iS p.1 p'.1 t) ∧
    (∀ t, p.2.2 t = p'.2.2 t + iT p.1 p'.1 t)

theorem bt_of_not_isW {a b : TS} (ha : a.isW = false) (h : bt a b) : b = a := by
  rcases h with h | ⟨h, -⟩ | ⟨h, -⟩
  · exact h.symm
  · rw [ha] at h; cases h
  · subst h; cases ha

/-- A step that changes one thread `t` to a state `a₁` outside the wait set. -/
theorem BT.local {r q₁ : RTState} {ks kt ks' kt' : Bud} {t : Tid} {a₁ : TS}
    (hb : BT (update r t a₁, ks, kt) (q₁, ks', kt')) (ha₁ : a₁.isW = false) :
    q₁ t = a₁ ∧ BT (r, ks, kt) (update q₁ t (r t), ks', kt') := by
  obtain ⟨hb, hs, ht⟩ := hb
  simp only at hb hs ht
  have hq : q₁ t = a₁ := bt_of_not_isW ha₁ (by simpa using hb t)
  refine ⟨hq, ?_, ?_, ?_⟩
  · intro v
    by_cases hv : v = t
    · subst hv; simp only [update_self]; exact .inl rfl
    · have := hb v; simpa [hv] using this
  · intro v
    dsimp only
    rw [hs v]
    by_cases hv : v = t
    · subst hv; simp [iS, ha₁, TS.not_isW_removed]
    · simp [iS, hv]
  · intro v
    dsimp only
    rw [ht v]
    by_cases hv : v = t
    · subst hv; simp [iT, ha₁, TS.not_isW_removed]
    · simp [iT, hv]

theorem BT.back {p p₁ p₁' : RT} {x : Option TLabel} (hs : RTStep p x p₁) (hb : BT p₁ p₁') :
    ∃ p', BT p p' ∧ (x = none → p' = p₁') ∧ (∀ y, x = some y → QTStep p' y p₁') := by
  obtain ⟨q₁, ks', kt'⟩ := p₁'
  cases hs with
  | wait r ks kt t τ h =>
    obtain ⟨hq, hs, htt⟩ := hb
    simp only at hq hs htt
    have ht := hq t
    simp only [update_self, bt, TS.isW_waiting, true_and, TS.waiting.injEq] at ht
    have hbt : ∀ v, v ≠ t → bt (r v) (update q₁ t .idle v) := by
      intro v hv; have := hq v; simpa [hv] using this
    rcases ht with ht | ht | ⟨rfl, ht⟩
    · refine ⟨(update q₁ t .idle, ks', kt'), ⟨?_, ?_, ?_⟩, by simp, ?_⟩
      · intro v
        by_cases hv : v = t
        · subst hv; simp [h, bt]
        · exact hbt v hv
      · intro v
        dsimp only
        rw [hs v]
        by_cases hv : v = t
        · subst hv; simp [iS, ← ht]
        · simp [iS, hv]
      · intro v
        dsimp only
        rw [htt v]
        by_cases hv : v = t
        · subst hv; simp [iT, ← ht]
        · simp [iT, hv]
      · rintro y ⟨⟩
        have := QTStep.wait (update q₁ t .idle) ks' kt' t τ (by simp)
        rwa [update_idem, ht, update_eq_self] at this
    · refine ⟨(update q₁ t .idle, update ks' t (ks' t + 1), kt'), ⟨?_, ?_, ?_⟩, by simp, ?_⟩
      · intro v
        by_cases hv : v = t
        · subst hv; simp [h, bt]
        · exact hbt v hv
      · intro v
        dsimp only
        rw [hs v]
        by_cases hv : v = t
        · subst hv; simp [iS, ht, h]
        · simp [iS, hv]
      · intro v
        dsimp only
        rw [htt v]
        by_cases hv : v = t
        · subst hv; simp [iT, ht, h]
        · simp [iT, hv]
      · rintro y ⟨⟩
        have := QTStep.waitS (update q₁ t .idle) (update ks' t (ks' t + 1)) kt' t τ (by simp)
          (by simp)
        rwa [update_idem, update_idem, update_self, Nat.add_sub_cancel, ← ht, update_eq_self,
          update_eq_self] at this
    · refine ⟨(update q₁ t .idle, ks', update kt' t (kt' t + 1)), ⟨?_, ?_, ?_⟩, by simp, ?_⟩
      · intro v
        by_cases hv : v = t
        · subst hv; simp [h, bt]
        · exact hbt v hv
      · intro v
        dsimp only
        rw [hs v]
        by_cases hv : v = t
        · subst hv; simp [iS, ht, h]
        · simp [iS, hv]
      · intro v
        dsimp only
        rw [htt v]
        by_cases hv : v = t
        · subst hv; simp [iT, ht, h]
        · simp [iT, hv]
      · rintro y ⟨⟩
        have := QTStep.waitT (update q₁ t .idle) ks' (update kt' t (kt' t + 1)) t (by simp)
          (by simp)
        rwa [update_idem, update_idem, update_self, Nat.add_sub_cancel, ← ht, update_eq_self,
          update_eq_self] at this
  | notifyNone r ks kt h =>
    refine ⟨(q₁, ks', kt'), hb, by simp, ?_⟩
    rintro y ⟨⟩
    refine .notifyNone _ _ _ fun u => ?_
    have := bt_of_not_isW (h u) (hb.1 u)
    simp only at this
    rw [this]; exact h u
  | notifyOne r ks kt u h =>
    obtain ⟨hq, hb'⟩ := BT.local hb rfl
    refine ⟨_, hb', by simp, ?_⟩
    rintro y ⟨⟩
    have := QTStep.notifyOne (update q₁ u (r u)) ks' kt' u (by simpa using h)
    rwa [update_idem, ← hq, update_eq_self] at this
  | notifyAll r ks kt =>
    obtain ⟨hq, hs, htt⟩ := hb
    simp only at hq hs htt
    have hA : ∀ t, (r t).isW = true → q₁ t = .removed .notified := by
      intro t ht
      have := bt_of_not_isW (by simp [RTState.removeAll, ht]) (hq t)
      simpa [RTState.removeAll, ht] using this
    have hN : ∀ t, (r t).isW = false → q₁ t = r t := by
      intro t ht
      have := bt_of_not_isW (by simp [RTState.removeAll, ht]) (hq t)
      simpa [RTState.removeAll, ht] using this
    refine ⟨(fun t => if (r t).isW = true then r t else q₁ t, ks', kt'), ⟨?_, ?_, ?_⟩, by simp,
      ?_⟩
    · intro t
      by_cases ht : (r t).isW = true
      · simp only [ht, ite_true]; exact .inl rfl
      · simp only [ht]
        rw [hN t (by simpa using ht)]; exact .inl rfl
    · intro v
      dsimp only
      rw [hs v]
      by_cases ht : (r v).isW = true
      · simp [iS, RTState.removeAll, ht, TS.ne_removed_of_isW ht]
      · simp [iS, RTState.removeAll, ht]
    · intro v
      dsimp only
      rw [htt v]
      by_cases ht : (r v).isW = true
      · simp [iT, RTState.removeAll, ht, TS.ne_removed_of_isW ht]
      · simp [iT, RTState.removeAll, ht]
    · rintro y ⟨⟩
      have key : RTState.removeAll (fun t => if (r t).isW = true then r t else q₁ t) = q₁ := by
        funext t
        by_cases ht : (r t).isW = true
        · simp [RTState.removeAll, ht, hA t ht]
        · have h' := hN t (by simpa using ht)
          simp only [Bool.not_eq_true] at ht
          simp [RTState.removeAll, ht, h']
      have := QTStep.notifyAll (fun t => if (r t).isW = true then r t else q₁ t) ks' kt'
      rwa [key] at this
  | spurious r ks kt u h hpos =>
    obtain ⟨hq, hs, htt⟩ := hb
    simp only at hq hs htt
    have hqu : q₁ u = .removed .spurious := by
      have := bt_of_not_isW (by simp) (hq u); simpa using this
    refine ⟨(q₁, ks', kt'), ⟨?_, ?_, ?_⟩, fun _ => rfl, by simp⟩
    · intro v
      by_cases hv : v = u
      · subst hv; exact .inr (.inl ⟨h, hqu⟩)
      · have := hq v; simpa [hv] using this
    · intro v
      have := hs v
      by_cases hv : v = u
      · subst hv
        simp only [update_self, iS, TS.isW_removed, Bool.false_eq_true, false_and, ite_false,
          add_zero] at this
        simp only [iS, h, hqu, and_self, ite_true]
        omega
      · simpa [iS, hv] using this
    · intro v
      have := htt v
      by_cases hv : v = u
      · subst hv
        simpa [iT, hqu] using this
      · simpa [iT, hv] using this
  | timeout r ks kt u h hpos =>
    obtain ⟨hq, hs, htt⟩ := hb
    simp only at hq hs htt
    have hqu : q₁ u = .removed .timedOut := by
      have := bt_of_not_isW (by simp) (hq u); simpa using this
    refine ⟨(q₁, ks', kt'), ⟨?_, ?_, ?_⟩, fun _ => rfl, by simp⟩
    · intro v
      by_cases hv : v = u
      · subst hv; exact .inr (.inr ⟨h, hqu⟩)
      · have := hq v; simpa [hv] using this
    · intro v
      have := hs v
      by_cases hv : v = u
      · subst hv
        simpa [iS, hqu] using this
      · simpa [iS, hv] using this
    · intro v
      have := htt v
      by_cases hv : v = u
      · subst hv
        simp only [update_self, iT, TS.isW_removed, Bool.false_eq_true, false_and, ite_false,
          add_zero] at this
        simp only [iT, h, hqu, TS.isW_waiting, and_self, ite_true]
        omega
      · simpa [iT, hv] using this
  | resume r ks kt t o h =>
    obtain ⟨hq, hb'⟩ := BT.local hb rfl
    refine ⟨_, hb', by simp, ?_⟩
    rintro y ⟨⟩
    have := QTStep.resume (update q₁ t (r t)) ks' kt' t o (by simpa using h)
    rwa [update_idem, ← hq, update_eq_self] at this

theorem RTRun.toQ {p p' : RT} {l : List TLabel} (h : TRun RTStep p l p') :
    ∀ p₁', BT p' p₁' → ∃ p₀', BT p p₀' ∧ LRun QTStep p₀' l p₁' := by
  induction h with
  | nil s => exact fun q' hq => ⟨q', hq, .nil _⟩
  | tau hs _ ih =>
    intro q' hq'
    obtain ⟨q₁, hb₁, hr₁⟩ := ih q' hq'
    obtain ⟨q, hb, he, -⟩ := BT.back hs hb₁
    exact ⟨q, hb, by rw [he rfl]; exact hr₁⟩
  | step hs _ ih =>
    intro q' hq'
    obtain ⟨q₁, hb₁, hr₁⟩ := ih q' hq'
    obtain ⟨q, hb, -, hst⟩ := BT.back hs hb₁
    exact ⟨q, hb, .cons (hst _ rfl) hr₁⟩

theorem BT.refl (p : RT) : BT p p :=
  ⟨fun _ => .inl rfl, fun t => by simp [iS, TS.not_isW_removed],
    fun t => by simp [iT, TS.not_isW_removed]⟩

theorem BT.init_eq {Ks Kt : Bud} {p : RT} (h : BT (RTState.init, Ks, Kt) p) :
    p = (RTState.init, Ks, Kt) := by
  obtain ⟨q, ks, kt⟩ := p
  obtain ⟨h1, h2, h3⟩ := h
  have hq : q = RTState.init := by
    funext t
    exact bt_of_not_isW rfl (h1 t)
  subst hq
  have e2 : ks = Ks := by funext t; have := h2 t; simpa [iS, RTState.init] using this.symm
  have e3 : kt = Kt := by funext t; have := h3 t; simpa [iT, RTState.init] using this.symm
  rw [e2, e3]

/-! ## The timed encoding -/

/-- The cause of an un-notified outcome (`true`: timed out). -/
def cause : Bool → Outcome
  | true => .timedOut
  | false => .spurious

/-- A state of the timed encoding: `C` of `MonitorSpec.lean`, the timed flag of
each thread's current wait, and the cause of each un-notified outcome (`tOut`). -/
structure CT where
  c : CState
  tm : Tid → Bool
  tOut : Tid → Bool

def CT.init : CT := ⟨CState.init, fun _ => false, fun _ => false⟩

/-- The timed encoding with budgets. A wait first fixes its outcome: by
notification (`waitN`, enters `W`), spurious (`waitS`, consumes `ks`), timed out
(`waitT`, timed waits only, consumes `kt`). -/
inductive CTStep : CT × Bud × Bud → TLabel → CT × Bud × Bud → Prop
  | waitN (s : CT) (ks kt : Bud) (t : Tid) (τ : Bool) : t ∉ s.c.k.W.map Prod.fst →
      s.c.U t = false →
      CTStep (s, ks, kt) (.wait t τ) (⟨⟨s.c.k.wait t, s.c.U⟩, update s.tm t τ, s.tOut⟩, ks, kt)
  | waitS (s : CT) (ks kt : Bud) (t : Tid) (τ : Bool) : t ∉ s.c.k.W.map Prod.fst →
      s.c.U t = false → 0 < ks t →
      CTStep (s, ks, kt) (.wait t τ)
        (⟨⟨s.c.k, update s.c.U t true⟩, update s.tm t τ, update s.tOut t false⟩,
          update ks t (ks t - 1), kt)
  | waitT (s : CT) (ks kt : Bud) (t : Tid) : t ∉ s.c.k.W.map Prod.fst →
      s.c.U t = false → 0 < kt t →
      CTStep (s, ks, kt) (.wait t true)
        (⟨⟨s.c.k, update s.c.U t true⟩, update s.tm t true, update s.tOut t true⟩,
          ks, update kt t (kt t - 1))
  | notify (s : CT) (ks kt : Bud) :
      CTStep (s, ks, kt) .notify (⟨⟨s.c.k.notify, s.c.U⟩, s.tm, s.tOut⟩, ks, kt)
  | notifyAll (s : CT) (ks kt : Bud) :
      CTStep (s, ks, kt) .notifyAll (⟨⟨s.c.k.notifyAll, s.c.U⟩, s.tm, s.tOut⟩, ks, kt)
  | resumeN (s : CT) (ks kt : Bud) (t : Tid) (k' : WComp) : t ∈ s.c.k.W.map Prod.fst →
      s.c.k.exitN t = some k' →
      CTStep (s, ks, kt) (.resume t .notified) (⟨⟨k', s.c.U⟩, s.tm, s.tOut⟩, ks, kt)
  | resumeU (s : CT) (ks kt : Bud) (t : Tid) : s.c.U t = true →
      CTStep (s, ks, kt) (.resume t (cause (s.tOut t)))
        (⟨⟨s.c.k, update s.c.U t false⟩, s.tm, s.tOut⟩, ks, kt)

/-- The label of `MonitorSpec.lean`. -/
def TLabel.base : TLabel → MLabel
  | .wait t _ => .wait t
  | .notify => .notify
  | .notifyAll => .notifyAll
  | .resume t o => .resume t (decide (o = .notified))

theorem base_cause (t : Tid) (b : Bool) : (TLabel.resume t (cause b)).base = .resume t false := by
  cases b <;> rfl

theorem CTStep.base {p p' : CT × Bud × Bud} {x : TLabel} (h : CTStep p x p') :
    CStep p.1.c x.base p'.1.c := by
  cases h with
  | waitN s ks kt t τ h1 h2 => exact .waitN s.c t h1 h2
  | waitS s ks kt t τ h1 h2 _ => exact .waitU s.c t h1 h2
  | waitT s ks kt t h1 h2 _ => exact .waitU s.c t h1 h2
  | notify s => exact .notify s.c
  | notifyAll s => exact .notifyAll s.c
  | resumeN s ks kt t k' h1 h2 => exact .resumeN s.c t k' h1 h2
  | resumeU s ks kt t h => rw [base_cause]; exact .resumeU s.c t h

/-! ### The decoration of a state of `Q` -/

/-- A thread state of `Q` (`MonitorSpec.lean`) with the timed flag and the cause. -/
def liftS : RS → Bool → Bool → TS
  | .idle, _, _ => .idle
  | .waiting, τ, _ => .waiting τ
  | .removed true, _, _ => .removed .notified
  | .removed false, _, b => .removed (cause b)

def lift (r : RState) (tm tOut : Tid → Bool) : RTState := fun t => liftS (r t) (tm t) (tOut t)

section Lift

variable {a : RS} {τ b : Bool}

theorem liftS_isW : (liftS a τ b).isW = true ↔ a = .waiting := by
  rcases a with _ | _ | ⟨_ | _⟩ <;> simp [liftS]

theorem liftS_idle : liftS a τ b = .idle ↔ a = .idle := by
  rcases a with _ | _ | ⟨_ | _⟩ <;> simp [liftS]

theorem liftS_waiting {τ' : Bool} : liftS a τ b = .waiting τ' ↔ a = .waiting ∧ τ = τ' := by
  rcases a with _ | _ | ⟨_ | _⟩ <;> simp [liftS]

theorem liftS_removed {o : Outcome} (h : liftS a τ b = .removed o) :
    a = .removed (decide (o = .notified)) ∧ (o ≠ .notified → o = cause b) := by
  rcases a with _ | _ | ⟨_ | _⟩ <;> simp only [liftS, reduceCtorEq, TS.removed.injEq] at h
  · subst h; cases b <;> simp [cause]
  · subst h; simp

theorem lift_upd (r : RState) (tm tOut : Tid → Bool) (t : Tid) (a : RS) (τ b : Bool) :
    lift (update r t a) (update tm t τ) (update tOut t b) =
      update (lift r tm tOut) t (liftS a τ b) := by
  funext v
  by_cases hv : v = t
  · subst hv; simp [lift]
  · simp [lift, hv]

theorem lift_upd₁ (r : RState) (tm tOut : Tid → Bool) (t : Tid) (a : RS) :
    lift (update r t a) tm tOut = update (lift r tm tOut) t (liftS a (tm t) (tOut t)) := by
  have := lift_upd r tm tOut t a (tm t) (tOut t)
  rwa [update_eq_self, update_eq_self] at this

theorem lift_upd₂ (r : RState) (tm tOut : Tid → Bool) (t : Tid) (a : RS) (τ : Bool) :
    lift (update r t a) (update tm t τ) tOut = update (lift r tm tOut) t (liftS a τ (tOut t)) := by
  have := lift_upd r tm tOut t a τ (tOut t)
  rwa [update_eq_self] at this

theorem lift_removeAll (r : RState) (tm tOut : Tid → Bool) :
    lift r.removeAll tm tOut = (lift r tm tOut).removeAll := by
  funext t
  by_cases h : r t = .waiting
  · simp [lift, RState.removeAll, RTState.removeAll, h, liftS]
  · have : (liftS (r t) (tm t) (tOut t)).isW = false := by
      cases e : (liftS (r t) (tm t) (tOut t)).isW
      · rfl
      · exact absurd (liftS_isW.1 e) h
    simp [lift, RState.removeAll, RTState.removeAll, h, this]

theorem lift_init (tm tOut : Tid → Bool) : lift RState.init tm tOut = RTState.init := rfl

end Lift

/-! ### `Q` ↔ `C`, timed -/

theorem fwdT {s : CT} {p : RT} {r : RState} {m : ℕ → Tid} {x : TLabel} {q' : RT}
    (hb : Basic s.c.k s.c.U) (hr : Rel r m s.c.k s.c.U) (e : p.1 = lift r s.tm s.tOut)
    (h : QTStep p x q') :
    ∃ s' m' r', CTStep (s, p.2) x (s', q'.2) ∧ Rel r' m' s'.c.k s'.c.U ∧
      q'.1 = lift r' s'.tm s'.tOut := by
  obtain ⟨q, ks, kt⟩ := p
  obtain rfl : q = lift r s.tm s.tOut := e
  cases h with
  | wait _ _ _ t τ h0 =>
    obtain ⟨h1, h2⟩ := hr.idle (liftS_idle.1 h0)
    exact ⟨_, m, _, .waitN s ks kt t τ h1 h2, H_waitN hb hr h1 h2,
      (lift_upd₂ r s.tm s.tOut t .waiting τ).symm⟩
  | waitS _ _ _ t τ h0 hpos =>
    obtain ⟨h1, h2⟩ := hr.idle (liftS_idle.1 h0)
    exact ⟨_, m, _, .waitS s ks kt t τ h1 h2 hpos, H_waitU hr h1,
      (lift_upd r s.tm s.tOut t (.removed false) τ false).symm⟩
  | waitT _ _ _ t h0 hpos =>
    obtain ⟨h1, h2⟩ := hr.idle (liftS_idle.1 h0)
    exact ⟨_, m, _, .waitT s ks kt t h1 h2 hpos, H_waitU hr h1,
      (lift_upd r s.tm s.tOut t (.removed false) true true).symm⟩
  | notifyNone _ _ _ h0 =>
    have hw : ∀ u, r u ≠ .waiting := fun u hu => by
      have := h0 u
      rw [show (lift r s.tm s.tOut u).isW = true from liftS_isW.2 hu] at this
      cases this
    refine ⟨_, m, r, .notify s ks kt, ?_, rfl⟩
    dsimp only
    rw [notify_self (not_lt.2 (count_ge hb hr hw))]; exact hr
  | notifyOne _ _ _ u h0 =>
    have hw : r u = .waiting := liftS_isW.1 h0
    obtain ⟨g, hg, ha⟩ := hr.waiting hw
    refine ⟨_, update m (s.c.k.c + 1) u, _, .notify s ks kt, ?_,
      (lift_upd₁ r s.tm s.tOut u (.removed true)).symm⟩
    dsimp only
    rw [notify_issue (count_lt hb hr hg ha hw)]; exact H_pick hb hr hg ha hw
  | notifyAll => exact ⟨_, m, _, .notifyAll s ks kt, H_notifyAll hb hr m,
    (lift_removeAll r s.tm s.tOut).symm⟩
  | resume _ _ _ t o h0 =>
    obtain ⟨hrt, ho⟩ := liftS_removed h0
    cases o with
    | notified =>
      obtain ⟨c', m', hc, hr'⟩ := fwd hb hr (QStep.resume r t true hrt)
      cases hc
      rename_i k' hm hex
      exact ⟨⟨⟨k', s.c.U⟩, s.tm, s.tOut⟩, m', _, .resumeN s ks kt t k' hm hex, hr',
        (lift_upd₁ r s.tm s.tOut t .idle).symm⟩
    | spurious =>
      have hU := hr.removedF hrt
      have e : Outcome.spurious = cause (s.tOut t) := ho (by simp)
      refine ⟨⟨⟨s.c.k, update s.c.U t false⟩, s.tm, s.tOut⟩, m, _, ?_, H_resumeU hb hr hU,
        (lift_upd₁ r s.tm s.tOut t .idle).symm⟩
      rw [e]; exact .resumeU s ks kt t hU
    | timedOut =>
      have hU := hr.removedF hrt
      have e : Outcome.timedOut = cause (s.tOut t) := ho (by simp)
      refine ⟨⟨⟨s.c.k, update s.c.U t false⟩, s.tm, s.tOut⟩, m, _, ?_, H_resumeU hb hr hU,
        (lift_upd₁ r s.tm s.tOut t .idle).symm⟩
      rw [e]; exact .resumeU s ks kt t hU

theorem backT {s s' : CT} {ks kt ks' kt' : Bud} {x : TLabel} (hb : Basic s.c.k s.c.U)
    (hinv : ∃ r₀ m₀, Rel r₀ m₀ s.c.k s.c.U) (h : CTStep (s, ks, kt) x (s', ks', kt'))
    {r' : RState} {m' : ℕ → Tid} (hr' : Rel r' m' s'.c.k s'.c.U) :
    ∃ r m, Rel r m s.c.k s.c.U ∧
      QTStep (lift r s.tm s.tOut, ks, kt) x (lift r' s'.tm s'.tOut, ks', kt') := by
  obtain ⟨r, m, hr, hq⟩ := back_step hb hinv h.base hr'
  refine ⟨r, m, hr, ?_⟩
  cases h with
  | waitN _ _ _ t τ h1 h2 =>
    change QStep r (.wait t) r' at hq
    cases hq with
    | wait _ h0 =>
      rw [lift_upd₂]; exact .wait _ _ _ t τ (liftS_idle.2 h0)
    | waitU _ h0 =>
      have := hr'.removedF (t := t) (by simp)
      simp [h2] at this
  | waitS _ _ _ t τ h1 h2 hpos =>
    change QStep r (.wait t) r' at hq
    cases hq with
    | wait _ h0 =>
      have := hr'.hU t (by simp)
      simp at this
    | waitU _ h0 =>
      rw [lift_upd]; exact .waitS _ _ _ t τ (liftS_idle.2 h0) hpos
  | waitT _ _ _ t h1 h2 hpos =>
    change QStep r (.wait t) r' at hq
    cases hq with
    | wait _ h0 =>
      have := hr'.hU t (by simp)
      simp at this
    | waitU _ h0 =>
      rw [lift_upd]; exact .waitT _ _ _ t (liftS_idle.2 h0) hpos
  | notify =>
    change QStep r .notify r' at hq
    cases hq with
    | notifyNone h0 =>
      exact .notifyNone _ _ _ fun u => Bool.eq_false_iff.2 fun e => h0 u (liftS_isW.1 e)
    | notifyOne u h0 =>
      rw [lift_upd₁]; exact .notifyOne _ _ _ u (liftS_isW.2 h0)
  | notifyAll =>
    change QStep r .notifyAll r' at hq
    cases hq
    rw [lift_removeAll]; exact .notifyAll _ _ _
  | resumeN _ _ _ t k' h1 h2 =>
    change QStep r (.resume t true) r' at hq
    cases hq with
    | resume _ _ h0 =>
      rw [lift_upd₁]; exact .resume _ _ _ t _ (by simp [lift, h0, liftS])
  | resumeU _ _ _ t h1 =>
    rw [base_cause] at hq
    cases hq with
    | resume _ _ h0 =>
      rw [lift_upd₁]; exact .resume _ _ _ t _ (by simp [lift, h0, liftS])

theorem inv_runT {c c' : CT × Bud × Bud} {l : List TLabel} (h : LRun CTStep c l c') :
    Basic c.1.c.k c.1.c.U → (∃ r m, Rel r m c.1.c.k c.1.c.U) →
    Basic c'.1.c.k c'.1.c.U ∧ ∃ r m, Rel r m c'.1.c.k c'.1.c.U := by
  induction h with
  | nil => exact fun hb hi => ⟨hb, hi⟩
  | cons hs _ ih =>
    rintro hb ⟨r, m, hr⟩
    exact ih (hb.step hs.base) (inv_step hb hr hs.base)

theorem C_backT {c c' : CT × Bud × Bud} {l : List TLabel} (h : LRun CTStep c l c') :
    Basic c.1.c.k c.1.c.U → (∃ r m, Rel r m c.1.c.k c.1.c.U) →
    ∀ r' m', Rel r' m' c'.1.c.k c'.1.c.U →
      ∃ r m, Rel r m c.1.c.k c.1.c.U ∧
        LRun QTStep (lift r c.1.tm c.1.tOut, c.2) l (lift r' c'.1.tm c'.1.tOut, c'.2) := by
  induction h with
  | nil s => exact fun _ _ r' m' hr => ⟨r', m', hr, .nil _⟩
  | cons hs _ ih =>
    rename_i c c₁ _ _ _
    rintro hb ⟨r₀, m₀, hr₀⟩ r' m' hr'
    obtain ⟨r₁, m₁, hr₁, hq₁⟩ :=
      ih (hb.step hs.base) (inv_step hb hr₀ hs.base) r' m' hr'
    obtain ⟨s, ks, kt⟩ := c
    obtain ⟨s₁, ks₁, kt₁⟩ := c₁
    obtain ⟨r, m, hr, hq⟩ := backT hb ⟨r₀, m₀, hr₀⟩ hs hr₁
    exact ⟨r, m, hr, .cons hq hq₁⟩

theorem Q_fwdT {p p' : RT} {l : List TLabel} (h : LRun QTStep p l p') :
    ∀ (s : CT) r m, Basic s.c.k s.c.U → Rel r m s.c.k s.c.U → p.1 = lift r s.tm s.tOut →
    ∃ s' r' m', LRun CTStep (s, p.2) l (s', p'.2) ∧ Rel r' m' s'.c.k s'.c.U ∧
      Basic s'.c.k s'.c.U ∧ p'.1 = lift r' s'.tm s'.tOut := by
  induction h with
  | nil => exact fun s r m hb hr e => ⟨s, r, m, .nil _, hr, hb, e⟩
  | cons hq _ ih =>
    intro s r m hb hr e
    obtain ⟨s₁, m₁, r₁, hs, hr₁, e₁⟩ := fwdT hb hr e hq
    obtain ⟨s', r', m', h', hr', hb', e'⟩ := ih s₁ r₁ m₁ (hb.step hs.base) hr₁ e₁
    exact ⟨s', r', m', .cons hs h', hr', hb', e'⟩

/-- **Timed waits (notify).** For every pair of budgets (spurious returns,
time-outs), the timed reference and the timed encoding have the same finite
traces. -/
theorem traces_eq_timed (Ks Kt : Bud) (l : List TLabel) :
    (∃ p, TRun RTStep (RTState.init, Ks, Kt) l p) ↔
    (∃ c, LRun CTStep (CT.init, Ks, Kt) l c) := by
  constructor
  · rintro ⟨p, h⟩
    obtain ⟨p₀, hb₀, hq⟩ := RTRun.toQ h p (BT.refl p)
    rw [BT.init_eq hb₀] at hq
    obtain ⟨s', -, -, hc, -⟩ := Q_fwdT hq CT.init RState.init id Basic.init Rel.init rfl
    exact ⟨_, hc⟩
  · rintro ⟨c, h⟩
    obtain ⟨-, r', m', hr'⟩ := inv_runT h Basic.init ⟨_, _, Rel.init⟩
    obtain ⟨r, m, hr, hq⟩ := C_backT h Basic.init ⟨_, _, Rel.init⟩ r' m' hr'
    rw [Rel.init_eq hr] at hq
    exact ⟨_, QTRun.toRT hq⟩

/-! ### Final states, timed -/

/-- A final state of the timed reference: no removed thread is left un-resumed;
`Xu` are the untimed and `Xt` the timed waiters. -/
def RQuietT (q : RTState) (Xu Xt : Tid → Prop) : Prop :=
  (∀ t o, q t ≠ .removed o) ∧ (∀ t, q t = .waiting false ↔ Xu t) ∧
    (∀ t, q t = .waiting true ↔ Xt t)

/-- A final state of the timed encoding: no un-notified outcome left, no waiter
entitled to return; `Xu` / `Xt` are the waiters of `W` with an untimed / timed
wait. -/
def CQuietT (s : CT) (Xu Xt : Tid → Prop) : Prop :=
  (∀ t, s.c.U t = false) ∧ (∀ t ∈ s.c.k.W.map Prod.fst, s.c.k.exitN t = none) ∧
    (∀ t, (t ∈ s.c.k.W.map Prod.fst ∧ s.tm t = false) ↔ Xu t) ∧
    (∀ t, (t ∈ s.c.k.W.map Prod.fst ∧ s.tm t = true) ↔ Xt t)

theorem quietT_iff {r : RState} {m : ℕ → Tid} {s : CT} (Xu Xt : Tid → Prop)
    (hb : Basic s.c.k s.c.U) (hr : Rel r m s.c.k s.c.U) :
    RQuietT (lift r s.tm s.tOut) Xu Xt ↔ CQuietT s Xu Xt := by
  have hw : ∀ t τ, lift r s.tm s.tOut t = .waiting τ ↔ r t = .waiting ∧ s.tm t = τ :=
    fun _ _ => liftS_waiting
  constructor
  · rintro ⟨hrem, hXu, hXt⟩
    have hR : RQuiet r (fun t => r t = .waiting) := by
      refine ⟨fun t b h => ?_, fun _ => Iff.rfl⟩
      cases b with
      | true => exact hrem t .notified (by simp [lift, h, liftS])
      | false => exact hrem t (cause (s.tOut t)) (by simp [lift, h, liftS])
    obtain ⟨hU, hex, hW⟩ := (quiet_iff _ hb hr).1 hR
    refine ⟨hU, hex, fun t => ?_, fun t => ?_⟩
    · rw [hW, ← hw, hXu]
    · rw [hW, ← hw, hXt]
  · rintro ⟨hU, hex, hXu, hXt⟩
    obtain ⟨hrem, hW⟩ := (quiet_iff (fun t => t ∈ s.c.k.W.map Prod.fst) hb hr).2
      ⟨hU, hex, fun _ => Iff.rfl⟩
    refine ⟨fun t o h => ?_, fun t => ?_, fun t => ?_⟩
    · exact hrem t _ (liftS_removed h).1
    · rw [hw, hW, hXu]
    · rw [hw, hW, hXt]

/-- **Final states (notify, timed).** The observation is the trace, the final
budgets `κs`, `κt`, and the untimed and timed waiters left (`Xu`, `Xt`). -/
theorem stuck_eq_timed (Ks Kt : Bud) (l : List TLabel) (Xu Xt : Tid → Prop) (κs κt : Bud) :
    (∃ q, TRun RTStep (RTState.init, Ks, Kt) l (q, κs, κt) ∧ RQuietT q Xu Xt) ↔
    (∃ s, LRun CTStep (CT.init, Ks, Kt) l (s, κs, κt) ∧ CQuietT s Xu Xt) := by
  constructor
  · rintro ⟨q, h, hq⟩
    obtain ⟨p₀, hb₀, hqr⟩ := RTRun.toQ h (q, κs, κt) (BT.refl _)
    rw [BT.init_eq hb₀] at hqr
    obtain ⟨s', r', m', hc, hr', hb', e⟩ :=
      Q_fwdT hqr CT.init RState.init id Basic.init Rel.init rfl
    obtain rfl : q = lift r' s'.tm s'.tOut := e
    exact ⟨s', hc, (quietT_iff Xu Xt hb' hr').1 hq⟩
  · rintro ⟨s, h, hq⟩
    obtain ⟨hb', r', m', hr'⟩ := inv_runT h Basic.init ⟨_, _, Rel.init⟩
    obtain ⟨r, m, hr, hqr⟩ := C_backT h Basic.init ⟨_, _, Rel.init⟩ r' m' hr'
    rw [Rel.init_eq hr] at hqr
    exact ⟨_, QTRun.toRT hqr, (quietT_iff Xu Xt hb' hr').2 hq⟩

/-- At a quiescent state of the timed reference, a silent removal is possible
iff some waiter has a spurious budget left or some timed waiter has a time-out
budget left. In particular, a timed waiter with `0 < κt t` can still time out:
the endpoint is not final in the reference (MODEL Section 5, first class). -/
theorem quietT_tau {q : RTState} {Xu Xt : Tid → Prop} {κs κt : Bud} (hq : RQuietT q Xu Xt) :
    (∃ p, RTStep (q, κs, κt) none p) ↔
    ∃ t, ((Xu t ∨ Xt t) ∧ 0 < κs t) ∨ (Xt t ∧ 0 < κt t) := by
  obtain ⟨-, hXu, hXt⟩ := hq
  constructor
  · rintro ⟨p, hs⟩
    cases hs with
    | spurious _ _ _ u h hpos =>
      refine ⟨u, .inl ⟨?_, hpos⟩⟩
      cases e : q u with
      | idle => rw [e] at h; cases h
      | removed o => rw [e] at h; cases h
      | waiting τ =>
        cases τ
        · exact .inl ((hXu u).1 e)
        · exact .inr ((hXt u).1 e)
    | timeout _ _ _ u h hpos => exact ⟨u, .inr ⟨(hXt u).1 h, hpos⟩⟩
  · rintro ⟨t, ⟨hX, hpos⟩ | ⟨hX, hpos⟩⟩
    · have hw : (q t).isW = true := by
        rcases hX with hX | hX
        · rw [(hXu t).2 hX]; rfl
        · rw [(hXt t).2 hX]; rfl
      exact ⟨_, .spurious _ _ _ t hw hpos⟩
    · exact ⟨_, .timeout _ _ _ t ((hXt t).2 hX) hpos⟩

/-! ## `signal`, timed: the FIFO reference -/

/-- Visible labels with timed waits (`signal`). -/
inductive TSLabel
  | wait (t : Tid) (timed : Bool)
  | signal
  | signalAll
  | resume (t : Tid) (o : Outcome)
  deriving DecidableEq, Repr

/-- A state of the timed FIFO reference: the queue, the timed flag of each
thread's current wait, and the cause of each removal not yet resumed. -/
@[ext] structure SRT where
  qu : List Tid
  tm : Tid → Bool
  gone : Tid → Option Outcome

def SRT.init : SRT := ⟨[], fun _ => false, fun _ => none⟩

inductive SRTStep : SRT × Bud × Bud → Option TSLabel → SRT × Bud × Bud → Prop
  | wait (s : SRT) (ks kt : Bud) (t : Tid) (τ : Bool) : t ∉ s.qu → s.gone t = none →
      SRTStep (s, ks, kt) (some (.wait t τ)) (⟨s.qu ++ [t], update s.tm t τ, s.gone⟩, ks, kt)
  | signalNone (s : SRT) (ks kt : Bud) : s.qu = [] → SRTStep (s, ks, kt) (some .signal) (s, ks, kt)
  | signalOne (s : SRT) (ks kt : Bud) (h : Tid) (rest : List Tid) : s.qu = h :: rest →
      SRTStep (s, ks, kt) (some .signal) (⟨rest, s.tm, update s.gone h (some .notified)⟩, ks, kt)
  | signalAll (s : SRT) (ks kt : Bud) :
      SRTStep (s, ks, kt) (some .signalAll)
        (⟨[], s.tm, fun u => if u ∈ s.qu then some .notified else s.gone u⟩, ks, kt)
  | spurious (s : SRT) (ks kt : Bud) (u : Tid) : u ∈ s.qu → 0 < ks u →
      SRTStep (s, ks, kt) none
        (⟨s.qu.erase u, s.tm, update s.gone u (some .spurious)⟩, update ks u (ks u - 1), kt)
  | timeout (s : SRT) (ks kt : Bud) (u : Tid) : u ∈ s.qu → s.tm u = true → 0 < kt u →
      SRTStep (s, ks, kt) none
        (⟨s.qu.erase u, s.tm, update s.gone u (some .timedOut)⟩, ks, update kt u (kt u - 1))
  | resume (s : SRT) (ks kt : Bud) (t : Tid) (o : Outcome) : s.gone t = some o →
      SRTStep (s, ks, kt) (some (.resume t o)) (⟨s.qu, s.tm, update s.gone t none⟩, ks, kt)

/-- The timed FIFO reference with the removal at the wait (proof device). -/
inductive SQTStep : SRT × Bud × Bud → TSLabel → SRT × Bud × Bud → Prop
  | wait (s : SRT) (ks kt : Bud) (t : Tid) (τ : Bool) : t ∉ s.qu → s.gone t = none →
      SQTStep (s, ks, kt) (.wait t τ) (⟨s.qu ++ [t], update s.tm t τ, s.gone⟩, ks, kt)
  | waitS (s : SRT) (ks kt : Bud) (t : Tid) (τ : Bool) : t ∉ s.qu → s.gone t = none →
      0 < ks t → SQTStep (s, ks, kt) (.wait t τ)
        (⟨s.qu, update s.tm t τ, update s.gone t (some .spurious)⟩, update ks t (ks t - 1), kt)
  | waitT (s : SRT) (ks kt : Bud) (t : Tid) : t ∉ s.qu → s.gone t = none →
      0 < kt t → SQTStep (s, ks, kt) (.wait t true)
        (⟨s.qu, update s.tm t true, update s.gone t (some .timedOut)⟩, ks, update kt t (kt t - 1))
  | signalNone (s : SRT) (ks kt : Bud) : s.qu = [] → SQTStep (s, ks, kt) .signal (s, ks, kt)
  | signalOne (s : SRT) (ks kt : Bud) (h : Tid) (rest : List Tid) : s.qu = h :: rest →
      SQTStep (s, ks, kt) .signal (⟨rest, s.tm, update s.gone h (some .notified)⟩, ks, kt)
  | signalAll (s : SRT) (ks kt : Bud) :
      SQTStep (s, ks, kt) .signalAll
        (⟨[], s.tm, fun u => if u ∈ s.qu then some .notified else s.gone u⟩, ks, kt)
  | resume (s : SRT) (ks kt : Bud) (t : Tid) (o : Outcome) : s.gone t = some o →
      SQTStep (s, ks, kt) (.resume t o) (⟨s.qu, s.tm, update s.gone t none⟩, ks, kt)

theorem SQTRun.toSRT {p p' : SRT × Bud × Bud} {l : List TSLabel} (h : LRun SQTStep p l p') :
    TRun SRTStep p l p' := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih =>
    cases hs with
    | wait s ks kt t τ h1 h2 => exact .step (.wait _ _ _ t τ h1 h2) ih
    | waitS s ks kt t τ h1 h2 hb =>
      refine .step (.wait _ _ _ t τ h1 h2) (.tau (SRTStep.spurious _ _ _ t (by simp) hb) ?_)
      simpa [List.erase_append_right _ h1] using ih
    | waitT s ks kt t h1 h2 hb =>
      refine .step (.wait _ _ _ t true h1 h2)
        (.tau (SRTStep.timeout _ _ _ t (by simp) (by simp) hb) ?_)
      simpa [List.erase_append_right _ h1] using ih
    | signalNone s ks kt h => exact .step (.signalNone _ _ _ h) ih
    | signalOne s ks kt h rest e => exact .step (.signalOne _ _ _ h rest e) ih
    | signalAll => exact .step (.signalAll _ _ _) ih
    | resume s ks kt t o h => exact .step (.resume _ _ _ t o h) ih

/-- Invariant of the timed FIFO reference. -/
def SRT.Inv (s : SRT) : Prop := s.qu.Nodup ∧ ∀ u ∈ s.qu, s.gone u = none

theorem SRT.Inv.step {p p' : SRT × Bud × Bud} {x : Option TSLabel} (hi : p.1.Inv)
    (h : SRTStep p x p') : p'.1.Inv := by
  cases h with
  | wait s ks kt t τ h1 h2 =>
    obtain ⟨hnd, hq⟩ := hi
    refine ⟨?_, ?_⟩
    · rw [List.nodup_append]; refine ⟨hnd, by simp, ?_⟩
      intro a ha b hb e; simp only [List.mem_singleton] at hb; subst hb; subst e; exact h1 ha
    · intro u hu
      simp only [List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · exact hq u hu
      · exact h2
  | signalNone => exact hi
  | signalOne s ks kt h rest e =>
    obtain ⟨hnd, hq⟩ := hi
    simp only at hnd hq
    rw [e, List.nodup_cons] at hnd
    refine ⟨hnd.2, fun u hu => ?_⟩
    have : u ≠ h := fun e' => hnd.1 (e' ▸ hu)
    change update s.gone h _ u = none
    rw [update_of_ne this]; exact hq u (by rw [e]; exact List.mem_cons_of_mem _ hu)
  | signalAll => exact ⟨List.nodup_nil, by simp⟩
  | spurious s ks kt u h =>
    obtain ⟨hnd, hq⟩ := hi
    refine ⟨hnd.erase u, fun v hv => ?_⟩
    have : v ≠ u := fun e => by
      rw [e] at hv; exact (List.Nodup.not_mem_erase hnd) hv
    change update s.gone u _ v = none
    rw [update_of_ne this]; exact hq v (List.mem_of_mem_erase hv)
  | timeout s ks kt u h =>
    obtain ⟨hnd, hq⟩ := hi
    refine ⟨hnd.erase u, fun v hv => ?_⟩
    have : v ≠ u := fun e => by
      rw [e] at hv; exact (List.Nodup.not_mem_erase hnd) hv
    change update s.gone u _ v = none
    rw [update_of_ne this]; exact hq v (List.mem_of_mem_erase hv)
  | resume s ks kt t o h =>
    obtain ⟨hnd, hq⟩ := hi
    refine ⟨hnd, fun u hu => ?_⟩
    have : u ≠ t := fun e => by rw [e] at hu; rw [hq t hu] at h; cases h
    change update s.gone t _ u = none
    rw [update_of_ne this]; exact hq u hu

theorem SRT.Inv.init : SRT.init.Inv := ⟨List.nodup_nil, by simp [SRT.init]⟩

theorem SRTRun.inv {p p' : SRT × Bud × Bud} {l : List TSLabel} (h : TRun SRTStep p l p')
    (hi : p.1.Inv) : p'.1.Inv := by
  induction h with
  | nil => exact hi
  | tau hs _ ih => exact ih (hi.step hs)
  | step hs _ ih => exact ih (hi.step hs)

/-! ### `R` ⊆ `Q`, timed FIFO -/

/-- `q` is `r` in which some queued threads are already removed (spuriously, or
by time-out if their wait is timed). -/
def BST (r q : SRT) : Prop :=
  q.tm = r.tm ∧
  (∀ u, q.gone u = r.gone u ∨ (u ∈ r.qu ∧ q.gone u = some .spurious) ∨
    (u ∈ r.qu ∧ r.tm u = true ∧ q.gone u = some .timedOut)) ∧
  q.qu = r.qu.filter (fun u => decide (q.gone u = none))

def jS (r q : SRT) (t : Tid) : ℕ := if t ∈ r.qu ∧ q.gone t = some .spurious then 1 else 0

def jT (r q : SRT) (t : Tid) : ℕ := if t ∈ r.qu ∧ q.gone t = some .timedOut then 1 else 0

def BSTB (p p' : SRT × Bud × Bud) : Prop :=
  BST p.1 p'.1 ∧ (∀ t, p.2.1 t = p'.2.1 t + jS p.1 p'.1 t) ∧
    (∀ t, p.2.2 t = p'.2.2 t + jT p.1 p'.1 t)

theorem BSTB.back {p p₁ p₁' : SRT × Bud × Bud} {x : Option TSLabel} (hi : p.1.Inv)
    (hs : SRTStep p x p₁) (hb : BSTB p₁ p₁') :
    ∃ p', BSTB p p' ∧ (x = none → p' = p₁') ∧ (∀ y, x = some y → SQTStep p' y p₁') := by
  obtain ⟨q₁, ks', kt'⟩ := p₁'
  obtain ⟨⟨htm, hg, hqq⟩, hbs, hbt⟩ := hb
  simp only at htm hg hqq hbs hbt
  cases hs with
  | wait r ks kt t τ h1 h2 =>
    obtain ⟨hnd, hqn⟩ := hi
    simp only at hnd hqn htm hg hqq hbs hbt
    have hgo : ∀ u, u ≠ t → q₁.gone u = r.gone u ∨ (u ∈ r.qu ∧ q₁.gone u = some .spurious) ∨
        (u ∈ r.qu ∧ r.tm u = true ∧ q₁.gone u = some .timedOut) := by
      intro u hu
      rcases hg u with h | ⟨hm, h⟩ | ⟨hm, ht, h⟩
      · exact .inl h
      · simp only [List.mem_append, List.mem_singleton, hu, or_false] at hm
        exact .inr (.inl ⟨hm, h⟩)
      · simp only [List.mem_append, List.mem_singleton, hu, or_false] at hm
        rw [update_of_ne hu] at ht
        exact .inr (.inr ⟨hm, ht, h⟩)
    rcases hg t with ht | ⟨-, ht⟩ | ⟨-, hτ, ht⟩
    · rw [h2] at ht
      refine ⟨(⟨r.qu.filter (fun u => decide (q₁.gone u = none)), r.tm, q₁.gone⟩, ks', kt'),
        ⟨⟨rfl, ?_, rfl⟩, ?_, ?_⟩, by simp, ?_⟩
      · intro u
        by_cases hu : u = t
        · subst hu; exact .inl (ht.trans h2.symm)
        · exact hgo u hu
      · intro v
        dsimp only
        rw [hbs v]
        by_cases hv : v = t
        · subst hv; simp [jS, ht]
        · simp [jS, hv]
      · intro v
        dsimp only
        rw [hbt v]
        by_cases hv : v = t
        · subst hv; simp [jT, ht]
        · simp [jT, hv]
      · rintro y ⟨⟩
        have e : q₁ = ⟨r.qu.filter (fun u => decide (q₁.gone u = none)) ++ [t],
            update r.tm t τ, q₁.gone⟩ := by
          ext1
          · rw [hqq, List.filter_append]; simp [ht]
          · exact htm
          · rfl
        rw [e]
        exact .wait _ _ _ t τ (fun h => h1 (List.mem_of_mem_filter h)) ht
    · have hnq : t ∉ q₁.qu := by
        rw [hqq]; intro h; simpa [ht] using (List.mem_filter.1 h).2
      refine ⟨(⟨q₁.qu, r.tm, update q₁.gone t none⟩, update ks' t (ks' t + 1), kt'),
        ⟨⟨rfl, ?_, ?_⟩, ?_, ?_⟩, by simp, ?_⟩
      · intro u
        by_cases hu : u = t
        · subst hu; simp only [update_self]; exact .inl h2.symm
        · simp only [update_of_ne hu]; exact hgo u hu
      · change q₁.qu = _
        rw [hqq, List.filter_append]
        simp only [ht, reduceCtorEq, decide_false, List.filter_cons, List.filter_nil,
          Bool.false_eq_true, ite_false, List.append_nil]
        apply List.filter_congr
        intro u hu
        have e : u ≠ t := fun e => h1 (e ▸ hu)
        simp [update_of_ne e]
      · intro v
        dsimp only
        rw [hbs v]
        by_cases hv : v = t
        · subst hv; simp [jS, ht, h1]
        · simp [jS, hv]
      · intro v
        dsimp only
        rw [hbt v]
        by_cases hv : v = t
        · subst hv; simp [jT, ht, h1]
        · simp [jT, hv]
      · rintro y ⟨⟩
        have := SQTStep.waitS ⟨q₁.qu, r.tm, update q₁.gone t none⟩ (update ks' t (ks' t + 1)) kt'
          t τ hnq (by simp) (by simp)
        simp only [update_idem, update_self, Nat.add_sub_cancel, update_eq_self] at this
        rwa [← ht, update_eq_self, ← htm, show (⟨q₁.qu, q₁.tm, q₁.gone⟩ : SRT) = q₁ from rfl]
          at this
    · simp only [update_self] at hτ
      subst hτ
      have hnq : t ∉ q₁.qu := by
        rw [hqq]; intro h; simpa [ht] using (List.mem_filter.1 h).2
      refine ⟨(⟨q₁.qu, r.tm, update q₁.gone t none⟩, ks', update kt' t (kt' t + 1)),
        ⟨⟨rfl, ?_, ?_⟩, ?_, ?_⟩, by simp, ?_⟩
      · intro u
        by_cases hu : u = t
        · subst hu; simp only [update_self]; exact .inl h2.symm
        · simp only [update_of_ne hu]; exact hgo u hu
      · change q₁.qu = _
        rw [hqq, List.filter_append]
        simp only [ht, reduceCtorEq, decide_false, List.filter_cons, List.filter_nil,
          Bool.false_eq_true, ite_false, List.append_nil]
        apply List.filter_congr
        intro u hu
        have e : u ≠ t := fun e => h1 (e ▸ hu)
        simp [update_of_ne e]
      · intro v
        dsimp only
        rw [hbs v]
        by_cases hv : v = t
        · subst hv; simp [jS, ht, h1]
        · simp [jS, hv]
      · intro v
        dsimp only
        rw [hbt v]
        by_cases hv : v = t
        · subst hv; simp [jT, ht, h1]
        · simp [jT, hv]
      · rintro y ⟨⟩
        have := SQTStep.waitT ⟨q₁.qu, r.tm, update q₁.gone t none⟩ ks' (update kt' t (kt' t + 1))
          t hnq (by simp) (by simp)
        simp only [update_idem, update_self, Nat.add_sub_cancel, update_eq_self] at this
        rwa [← ht, update_eq_self, ← htm, show (⟨q₁.qu, q₁.tm, q₁.gone⟩ : SRT) = q₁ from rfl]
          at this
  | signalNone r ks kt h =>
    refine ⟨(q₁, ks', kt'), ⟨⟨htm, hg, hqq⟩, hbs, hbt⟩, by simp, ?_⟩
    rintro y ⟨⟩
    exact .signalNone _ _ _ (by rw [hqq, h]; rfl)
  | signalOne r ks kt h rest e =>
    obtain ⟨hnd, hqn⟩ := hi
    simp only at hnd hqn
    rw [e, List.nodup_cons] at hnd
    have hh : q₁.gone h = some .notified := by
      rcases hg h with h' | ⟨h', -⟩ | ⟨h', -⟩
      · rw [h']; simp
      · exact absurd h' hnd.1
      · exact absurd h' hnd.1
    refine ⟨(⟨h :: q₁.qu, r.tm, update q₁.gone h none⟩, ks', kt'), ⟨⟨rfl, ?_, ?_⟩, ?_, ?_⟩,
      by simp, ?_⟩
    · intro u
      by_cases eu : u = h
      · simp only [eu, update_self]; exact .inl (hqn h (by rw [e]; simp)).symm
      · simp only [update_of_ne eu]
        rcases hg u with h' | ⟨hu, h'⟩ | ⟨hu, ht, h'⟩
        · exact .inl (by rw [h']; exact update_of_ne eu _ _)
        · exact .inr (.inl ⟨by rw [e]; exact List.mem_cons_of_mem _ hu, h'⟩)
        · exact .inr (.inr ⟨by rw [e]; exact List.mem_cons_of_mem _ hu, ht, h'⟩)
    · change h :: q₁.qu = _
      rw [e, List.filter_cons]
      simp only [update_self, decide_true, ite_true]
      rw [hqq]
      congr 1
      apply List.filter_congr
      intro u hu
      have eu : u ≠ h := fun e' => hnd.1 (e' ▸ hu)
      simp [update_of_ne eu]
    · intro v
      rw [hbs v]
      by_cases hv : v = h
      · subst hv; simp [jS, e, hnd.1]
      · simp [jS, e, hv]
    · intro v
      rw [hbt v]
      by_cases hv : v = h
      · subst hv; simp [jT, e, hnd.1]
      · simp [jT, e, hv]
    · rintro y ⟨⟩
      have := SQTStep.signalOne ⟨h :: q₁.qu, r.tm, update q₁.gone h none⟩ ks' kt' h q₁.qu rfl
      simp only [update_idem] at this
      rw [← hh, update_eq_self] at this
      rwa [show (⟨q₁.qu, r.tm, q₁.gone⟩ : SRT) = q₁ by rw [← htm]] at this
  | signalAll r ks kt =>
    obtain ⟨hnd, hqn⟩ := hi
    simp only at hnd hqn
    have hall : ∀ u ∈ r.qu, q₁.gone u = some .notified := by
      intro u hu
      rcases hg u with h' | ⟨h', -⟩ | ⟨h', -⟩
      · rw [h']; simp [hu]
      · simp at h'
      · simp at h'
    refine ⟨(⟨r.qu, r.tm, fun u => if u ∈ r.qu then none else q₁.gone u⟩, ks', kt'),
      ⟨⟨rfl, ?_, ?_⟩, ?_, ?_⟩, by simp, ?_⟩
    · intro u
      by_cases hu : u ∈ r.qu
      · simp only [hu, ite_true]; exact .inl (hqn u hu).symm
      · simp only [hu, ite_false]
        rcases hg u with h' | ⟨h', -⟩ | ⟨h', -⟩
        · exact .inl (by rw [h']; simp [hu])
        · simp at h'
        · simp at h'
    · change r.qu = _
      symm; rw [List.filter_eq_self]
      intro u hu; simp [hu]
    · intro v
      rw [hbs v]
      by_cases hv : v ∈ r.qu
      · simp [jS, hv]
      · simp [jS, hv]
    · intro v
      rw [hbt v]
      by_cases hv : v ∈ r.qu
      · simp [jT, hv]
      · simp [jT, hv]
    · rintro y ⟨⟩
      have key : (⟨[], r.tm, fun u => if u ∈ r.qu then some .notified else
          (fun u => if u ∈ r.qu then none else q₁.gone u) u⟩ : SRT) = q₁ := by
        ext1
        · rw [hqq]; rfl
        · exact htm.symm
        · funext u
          by_cases hu : u ∈ r.qu
          · simp [hu, hall u hu]
          · simp [hu]
      have hst := SQTStep.signalAll
        ⟨r.qu, r.tm, fun u => if u ∈ r.qu then none else q₁.gone u⟩ ks' kt'
      rw [key] at hst
      exact hst
  | spurious r ks kt u h hpos =>
    obtain ⟨hnd, hqn⟩ := hi
    simp only at hnd hqn
    have hne : u ∉ r.qu.erase u := List.Nodup.not_mem_erase hnd
    have hqu : q₁.gone u = some .spurious := by
      rcases hg u with h' | ⟨h', -⟩ | ⟨h', -⟩
      · rw [h']; simp
      · exact absurd h' hne
      · exact absurd h' hne
    refine ⟨(q₁, ks', kt'), ⟨⟨htm, ?_, ?_⟩, ?_, ?_⟩, fun _ => rfl, by simp⟩
    · intro v
      by_cases e : v = u
      · rw [e]; exact .inr (.inl ⟨h, hqu⟩)
      · rcases hg v with h' | ⟨hv, h'⟩ | ⟨hv, ht, h'⟩
        · exact .inl (by rw [h']; exact update_of_ne e _ _)
        · exact .inr (.inl ⟨List.mem_of_mem_erase hv, h'⟩)
        · exact .inr (.inr ⟨List.mem_of_mem_erase hv, ht, h'⟩)
    · rw [hqq]
      apply filter_erase_of_not
      simp [hqu]
    · intro v
      have := hbs v
      by_cases hv : v = u
      · subst hv
        simp only [update_self, jS, hne, false_and, ite_false, add_zero] at this
        simp only [jS, h, hqu, and_self, ite_true]
        omega
      · have hm : v ∈ r.qu.erase u ↔ v ∈ r.qu := List.mem_erase_of_ne hv
        simpa [jS, hv, hm] using this
    · intro v
      have := hbt v
      by_cases hv : v = u
      · subst hv
        simpa [jT, hne, hqu] using this
      · have hm : v ∈ r.qu.erase u ↔ v ∈ r.qu := List.mem_erase_of_ne hv
        simpa [jT, hv, hm] using this
  | timeout r ks kt u h htu hpos =>
    obtain ⟨hnd, hqn⟩ := hi
    simp only at hnd hqn
    have hne : u ∉ r.qu.erase u := List.Nodup.not_mem_erase hnd
    have hqu : q₁.gone u = some .timedOut := by
      rcases hg u with h' | ⟨h', -⟩ | ⟨h', -⟩
      · rw [h']; simp
      · exact absurd h' hne
      · exact absurd h' hne
    refine ⟨(q₁, ks', kt'), ⟨⟨htm, ?_, ?_⟩, ?_, ?_⟩, fun _ => rfl, by simp⟩
    · intro v
      by_cases e : v = u
      · rw [e]; exact .inr (.inr ⟨h, htu, hqu⟩)
      · rcases hg v with h' | ⟨hv, h'⟩ | ⟨hv, ht, h'⟩
        · exact .inl (by rw [h']; exact update_of_ne e _ _)
        · exact .inr (.inl ⟨List.mem_of_mem_erase hv, h'⟩)
        · exact .inr (.inr ⟨List.mem_of_mem_erase hv, ht, h'⟩)
    · rw [hqq]
      apply filter_erase_of_not
      simp [hqu]
    · intro v
      have := hbs v
      by_cases hv : v = u
      · subst hv
        simpa [jS, hne, hqu] using this
      · have hm : v ∈ r.qu.erase u ↔ v ∈ r.qu := List.mem_erase_of_ne hv
        simpa [jS, hv, hm] using this
    · intro v
      have := hbt v
      by_cases hv : v = u
      · subst hv
        simp only [update_self, jT, hne, false_and, ite_false, add_zero] at this
        simp only [jT, h, hqu, and_self, ite_true]
        omega
      · have hm : v ∈ r.qu.erase u ↔ v ∈ r.qu := List.mem_erase_of_ne hv
        simpa [jT, hv, hm] using this
  | resume r ks kt t o h =>
    obtain ⟨hnd, hqn⟩ := hi
    simp only at hnd hqn
    have htq : t ∉ r.qu := fun ht => by rw [hqn t ht] at h; cases h
    have hq0 : q₁.gone t = none := by
      rcases hg t with h' | ⟨h', -⟩ | ⟨h', -⟩
      · rw [h']; simp
      · exact absurd h' htq
      · exact absurd h' htq
    refine ⟨(⟨q₁.qu, r.tm, update q₁.gone t (some o)⟩, ks', kt'), ⟨⟨rfl, ?_, ?_⟩, ?_, ?_⟩,
      by simp, ?_⟩
    · intro u
      by_cases e : u = t
      · simp only [e, update_self]; exact .inl h.symm
      · simp only [update_of_ne e]
        rcases hg u with h' | ⟨hu, h'⟩ | ⟨hu, ht, h'⟩
        · exact .inl (by rw [h']; exact update_of_ne e _ _)
        · exact .inr (.inl ⟨hu, h'⟩)
        · exact .inr (.inr ⟨hu, ht, h'⟩)
    · change q₁.qu = _
      rw [hqq]
      apply List.filter_congr
      intro u hu
      have e : u ≠ t := fun e => htq (e ▸ hu)
      simp [update_of_ne e]
    · intro v
      rw [hbs v]
      by_cases hv : v = t
      · subst hv; simp [jS, htq]
      · simp [jS, hv]
    · intro v
      rw [hbt v]
      by_cases hv : v = t
      · subst hv; simp [jT, htq]
      · simp [jT, hv]
    · rintro y ⟨⟩
      have := SQTStep.resume ⟨q₁.qu, r.tm, update q₁.gone t (some o)⟩ ks' kt' t o (by simp)
      simp only [update_idem] at this
      rw [← hq0, update_eq_self] at this
      rwa [show (⟨q₁.qu, r.tm, q₁.gone⟩ : SRT) = q₁ by rw [← htm]] at this

theorem SRTRun.toQ {p p' : SRT × Bud × Bud} {l : List TSLabel} (h : TRun SRTStep p l p') :
    p.1.Inv → ∀ q', BSTB p' q' → ∃ q, BSTB p q ∧ LRun SQTStep q l q' := by
  induction h with
  | nil s => exact fun _ q' hq => ⟨q', hq, .nil _⟩
  | tau hs _ ih =>
    intro hi q' hq'
    obtain ⟨q₁, hb₁, hr₁⟩ := ih (hi.step hs) q' hq'
    obtain ⟨q, hb, he, -⟩ := BSTB.back hi hs hb₁
    exact ⟨q, hb, by rw [he rfl]; exact hr₁⟩
  | step hs _ ih =>
    intro hi q' hq'
    obtain ⟨q₁, hb₁, hr₁⟩ := ih (hi.step hs) q' hq'
    obtain ⟨q, hb, -, hst⟩ := BSTB.back hi hs hb₁
    exact ⟨q, hb, .cons (hst _ rfl) hr₁⟩

theorem BSTB.refl {p : SRT × Bud × Bud} (hi : p.1.Inv) : BSTB p p := by
  refine ⟨⟨rfl, fun u => .inl rfl, ?_⟩, fun t => ?_, fun t => ?_⟩
  · symm; rw [List.filter_eq_self]
    intro u hu; simp [hi.2 u hu]
  · have : ¬ (t ∈ p.1.qu ∧ p.1.gone t = some .spurious) := fun ⟨h1, h2⟩ => by
      rw [hi.2 t h1] at h2; cases h2
    simp [jS, this]
  · have : ¬ (t ∈ p.1.qu ∧ p.1.gone t = some .timedOut) := fun ⟨h1, h2⟩ => by
      rw [hi.2 t h1] at h2; cases h2
    simp [jT, this]

theorem BSTB.init_eq {Ks Kt : Bud} {p : SRT × Bud × Bud} (h : BSTB (SRT.init, Ks, Kt) p) :
    p = (SRT.init, Ks, Kt) := by
  obtain ⟨q, ks, kt⟩ := p
  obtain ⟨⟨h0, h1, h2⟩, h3, h4⟩ := h
  have hq : q = SRT.init := by
    ext1
    · rw [h2]; rfl
    · exact h0
    · funext u
      rcases h1 u with h' | ⟨h', -⟩ | ⟨h', -⟩
      · exact h'
      · simp [SRT.init] at h'
      · simp [SRT.init] at h'
  subst hq
  have e3 : ks = Ks := by funext t; have := h3 t; simpa [jS, SRT.init] using this.symm
  have e4 : kt = Kt := by funext t; have := h4 t; simpa [jT, SRT.init] using this.symm
  rw [e3, e4]

/-! ### The timed encoding with `signal` -/

/-- As `CTStep`, with `WComp.signal` and, for `signalAll`, `WComp.notifyAll`. -/
inductive CSTStep : CT × Bud × Bud → TSLabel → CT × Bud × Bud → Prop
  | waitN (s : CT) (ks kt : Bud) (t : Tid) (τ : Bool) : t ∉ s.c.k.W.map Prod.fst →
      s.c.U t = false →
      CSTStep (s, ks, kt) (.wait t τ) (⟨⟨s.c.k.wait t, s.c.U⟩, update s.tm t τ, s.tOut⟩, ks, kt)
  | waitS (s : CT) (ks kt : Bud) (t : Tid) (τ : Bool) : t ∉ s.c.k.W.map Prod.fst →
      s.c.U t = false → 0 < ks t →
      CSTStep (s, ks, kt) (.wait t τ)
        (⟨⟨s.c.k, update s.c.U t true⟩, update s.tm t τ, update s.tOut t false⟩,
          update ks t (ks t - 1), kt)
  | waitT (s : CT) (ks kt : Bud) (t : Tid) : t ∉ s.c.k.W.map Prod.fst →
      s.c.U t = false → 0 < kt t →
      CSTStep (s, ks, kt) (.wait t true)
        (⟨⟨s.c.k, update s.c.U t true⟩, update s.tm t true, update s.tOut t true⟩,
          ks, update kt t (kt t - 1))
  | signal (s : CT) (ks kt : Bud) :
      CSTStep (s, ks, kt) .signal (⟨⟨s.c.k.signal, s.c.U⟩, s.tm, s.tOut⟩, ks, kt)
  | signalAll (s : CT) (ks kt : Bud) :
      CSTStep (s, ks, kt) .signalAll (⟨⟨s.c.k.notifyAll, s.c.U⟩, s.tm, s.tOut⟩, ks, kt)
  | resumeN (s : CT) (ks kt : Bud) (t : Tid) (k' : WComp) : t ∈ s.c.k.W.map Prod.fst →
      s.c.k.exitN t = some k' →
      CSTStep (s, ks, kt) (.resume t .notified) (⟨⟨k', s.c.U⟩, s.tm, s.tOut⟩, ks, kt)
  | resumeU (s : CT) (ks kt : Bud) (t : Tid) : s.c.U t = true →
      CSTStep (s, ks, kt) (.resume t (cause (s.tOut t)))
        (⟨⟨s.c.k, update s.c.U t false⟩, s.tm, s.tOut⟩, ks, kt)

theorem CSTStep.base {p p' : CT × Bud × Bud} {x : TSLabel} (h : CSTStep p x p') :
    Basic2 p.1.c.k p.1.c.U → Basic2 p'.1.c.k p'.1.c.U := by
  intro hb
  cases h with
  | waitN s ks kt t τ h1 h2 => exact hb.step (.waitN s.c t h1 h2)
  | waitS s ks kt t τ h1 h2 _ => exact hb.step (.waitU s.c t h1 h2)
  | waitT s ks kt t h1 h2 _ => exact hb.step (.waitU s.c t h1 h2)
  | signal s => exact hb.step (.signal s.c)
  | signalAll s => exact hb.step (.signalAll s.c)
  | resumeN s ks kt t k' h1 h2 => exact hb.step (.resumeN s.c t k' h1 h2)
  | resumeU s ks kt t h => exact hb.step (.resumeU s.c t h)

/-- The decoration of a state of the FIFO reference. -/
def liftG (q : SR) (tm tOut : Tid → Bool) : SRT :=
  ⟨q.qu, tm, fun u => (q.gone u).map (fun b => if b then .notified else cause (tOut u))⟩

/-- The timed reference state of a state of the timed encoding. -/
def absT (s : CT) : SRT := liftG (absS s.c.k s.c.U) s.tm s.tOut

theorem liftG_upd (qu : List Tid) (g : Tid → Option Bool) (tm tOut : Tid → Bool) (t : Tid)
    (v : Option Bool) (z : Bool) :
    liftG ⟨qu, update g t v⟩ tm (update tOut t z) =
      ⟨qu, tm, update (liftG ⟨qu, g⟩ tm tOut).gone t
        (v.map (fun b => if b then .notified else cause z))⟩ := by
  ext1
  · rfl
  · rfl
  · funext u
    by_cases hu : u = t
    · subst hu; simp [liftG]
    · simp [liftG, hu]

theorem liftG_upd₁ (qu : List Tid) (g : Tid → Option Bool) (tm tOut : Tid → Bool) (t : Tid)
    (v : Option Bool) :
    liftG ⟨qu, update g t v⟩ tm tOut =
      ⟨qu, tm, update (liftG ⟨qu, g⟩ tm tOut).gone t
        (v.map (fun b => if b then .notified else cause (tOut t)))⟩ := by
  have := liftG_upd qu g tm tOut t v (tOut t)
  rwa [update_eq_self] at this

theorem absT_none {s : CT} {t : Tid} :
    (absT s).gone t = none ↔ (absS s.c.k s.c.U).gone t = none := by
  simp [absT, liftG]

theorem bwdST {s s' : CT} {ks kt ks' kt' : Bud} {x : TSLabel} (hb : Basic2 s.c.k s.c.U)
    (h : CSTStep (s, ks, kt) x (s', ks', kt')) :
    SQTStep (absT s, ks, kt) x (absT s', ks', kt') := by
  cases h with
  | waitN _ _ _ t τ ht hU =>
    change SQTStep _ _ (liftG (absS (s.c.k.wait t) s.c.U) _ _, _, _)
    rw [abs_waitN hb ht hU]
    exact .wait _ _ _ t τ (fun h => ht (pm_sub h)) (absT_none.2 (by simp [absS, hU, ht]))
  | waitS _ _ _ t τ ht hU hpos =>
    change SQTStep _ _ (liftG (absS s.c.k (update s.c.U t true)) _ _, _, _)
    rw [abs_waitU, liftG_upd]
    exact .waitS _ _ _ t τ (fun h => ht (pm_sub h)) (absT_none.2 (by simp [absS, hU, ht])) hpos
  | waitT _ _ _ t ht hU hpos =>
    change SQTStep _ _ (liftG (absS s.c.k (update s.c.U t true)) _ _, _, _)
    rw [abs_waitU, liftG_upd]
    exact .waitT _ _ _ t (fun h => ht (pm_sub h)) (absT_none.2 (by simp [absS, hU, ht])) hpos
  | signal =>
    change SQTStep _ _ (liftG (absS s.c.k.signal s.c.U) _ _, _, _)
    cases hP : s.c.k.pending with
    | nil =>
      rw [show s.c.k.signal = s.c.k by simp [WComp.signal, hP]]
      exact .signalNone _ _ _ (by simp [absT, liftG, absS, hP])
    | cons w rest =>
      rw [show s.c.k.signal = { s.c.k with S := s.c.k.S ++ [w.1] } by simp [WComp.signal, hP],
        abs_sig hb hP, liftG_upd₁]
      exact .signalOne _ _ _ w.1 (rest.map Prod.fst) (by simp [absT, liftG, absS, hP])
  | signalAll =>
    change SQTStep _ _ (liftG (absS s.c.k.notifyAll s.c.U) _ _, _, _)
    rw [abs_nA hb]
    have e : liftG ⟨[], fun u => if u ∈ (absS s.c.k s.c.U).qu then some true
        else (absS s.c.k s.c.U).gone u⟩ s.tm s.tOut =
        ⟨[], (absT s).tm,
          fun u => if u ∈ (absT s).qu then some .notified else (absT s).gone u⟩ := by
      ext1
      · rfl
      · rfl
      · funext u
        by_cases hu : u ∈ (absS s.c.k s.c.U).qu
        · simp [liftG, absT, hu]
        · simp [liftG, absT, hu]
    rw [e]; exact .signalAll _ _ _
  | resumeN _ _ _ t k' hm hex =>
    obtain ⟨g, hg⟩ := mem_fst.1 hm
    have hU : s.c.U t = false := by
      cases h : s.c.U t
      · rfl
      · exact absurd hm (hb.disj _ h)
    have key : ∃ S', (∀ u, u ≠ t → (u ∈ S' ↔ u ∈ s.c.k.S)) ∧
        t ∉ s.c.k.pending.map Prod.fst ∧ k' = { s.c.k with S := S', W := s.c.k.drop t } := by
      by_cases hlt : g < s.c.k.a
      · rw [E_lt hb hg hlt] at hex; cases hex
        refine ⟨s.c.k.S, fun _ _ => Iff.rfl, fun h => ?_, rfl⟩
        obtain ⟨g', hg', ha, -⟩ := mem_pm.1 h; have := hb.uniq' hg hg'; omega
      · by_cases hS : t ∈ s.c.k.S
        · rw [E_S hb hg (not_lt.1 hlt) hS] at hex; cases hex
          refine ⟨s.c.k.S.erase t, fun u hu => ?_, fun h => ?_, rfl⟩
          · rw [hb.S_nodup.mem_erase_iff]; simp [hu]
          · obtain ⟨_, _, _, hS'⟩ := mem_pm.1 h; exact hS' hS
        · rw [E_none hb hg (not_lt.1 hlt) hS] at hex; cases hex
    obtain ⟨S', hS', htp, rfl⟩ := key
    change SQTStep _ _ (liftG (absS { s.c.k with S := S', W := s.c.k.drop t } s.c.U) _ _, _, _)
    rw [abs_drop hb hg htp S' hS', liftG_upd₁]
    exact .resume _ _ _ t _ (by simp [absT, liftG, absS, hU, hm, htp])
  | resumeU _ _ _ t hU =>
    change SQTStep _ _ (liftG (absS s.c.k (update s.c.U t false)) _ _, _, _)
    rw [abs_resumeU hb hU, liftG_upd₁]
    exact .resume _ _ _ t _ (by simp [absT, liftG, absS, hU])

theorem fwdST {s : CT} {p q' : SRT × Bud × Bud} {x : TSLabel} (hb : Basic2 s.c.k s.c.U)
    (e : p.1 = absT s) (h : SQTStep p x q') :
    ∃ s', CSTStep (s, p.2) x (s', q'.2) ∧ q'.1 = absT s' := by
  obtain ⟨q, ks, kt⟩ := p
  obtain rfl : q = absT s := e
  cases h with
  | wait _ _ _ t τ h1 h2 =>
    obtain ⟨hU, hW⟩ := gone_none (absT_none.1 h2)
    have ht : t ∉ s.c.k.W.map Prod.fst := fun h => h1 (hW h)
    refine ⟨_, .waitN s ks kt t τ ht hU, ?_⟩
    change _ = liftG (absS (s.c.k.wait t) s.c.U) _ _
    rw [abs_waitN hb ht hU]; rfl
  | waitS _ _ _ t τ h1 h2 hpos =>
    obtain ⟨hU, hW⟩ := gone_none (absT_none.1 h2)
    have ht : t ∉ s.c.k.W.map Prod.fst := fun h => h1 (hW h)
    refine ⟨_, .waitS s ks kt t τ ht hU hpos, ?_⟩
    change _ = liftG (absS s.c.k (update s.c.U t true)) _ _
    rw [abs_waitU, liftG_upd]; rfl
  | waitT _ _ _ t h1 h2 hpos =>
    obtain ⟨hU, hW⟩ := gone_none (absT_none.1 h2)
    have ht : t ∉ s.c.k.W.map Prod.fst := fun h => h1 (hW h)
    refine ⟨_, .waitT s ks kt t ht hU hpos, ?_⟩
    change _ = liftG (absS s.c.k (update s.c.U t true)) _ _
    rw [abs_waitU, liftG_upd]; rfl
  | signalNone _ _ _ h =>
    have hP : s.c.k.pending = [] := List.map_eq_nil_iff.1 h
    refine ⟨_, .signal s ks kt, ?_⟩
    change _ = liftG (absS s.c.k.signal s.c.U) _ _
    rw [show s.c.k.signal = s.c.k by simp [WComp.signal, hP]]; rfl
  | signalOne _ _ _ h rest e =>
    obtain ⟨w, prest, hP, hw, hr⟩ : ∃ w prest, s.c.k.pending = w :: prest ∧ w.1 = h ∧
        prest.map Prod.fst = rest := by
      cases hP : s.c.k.pending with
      | nil => simp [absT, liftG, absS, hP] at e
      | cons w prest =>
        simp only [absT, liftG, absS, hP, List.map_cons, List.cons.injEq] at e
        exact ⟨w, prest, rfl, e.1, e.2⟩
    refine ⟨_, .signal s ks kt, ?_⟩
    change _ = liftG (absS s.c.k.signal s.c.U) _ _
    rw [show s.c.k.signal = { s.c.k with S := s.c.k.S ++ [w.1] } by simp [WComp.signal, hP],
      abs_sig hb hP, liftG_upd₁, hw, hr]
    rfl
  | signalAll =>
    refine ⟨_, .signalAll s ks kt, ?_⟩
    change _ = liftG (absS s.c.k.notifyAll s.c.U) _ _
    rw [abs_nA hb]
    ext1
    · rfl
    · rfl
    · funext u
      by_cases hu : u ∈ (absS s.c.k s.c.U).qu
      · simp [liftG, absT, hu]
      · simp [liftG, absT, hu]
  | resume _ _ _ t o h =>
    obtain ⟨b, hb', ho⟩ := Option.map_eq_some_iff.1 h
    cases b with
    | true =>
      simp only [ite_true] at ho
      subst ho
      obtain ⟨hU, hm, htp⟩ := gone_st hb'
      obtain ⟨g, hg⟩ := mem_fst.1 hm
      by_cases hlt : g < s.c.k.a
      · refine ⟨_, .resumeN s ks kt t _ hm (E_lt hb hg hlt), ?_⟩
        change _ = liftG (absS { s.c.k with W := s.c.k.drop t } s.c.U) _ _
        rw [abs_drop hb hg htp s.c.k.S (fun _ _ => Iff.rfl), liftG_upd₁]; rfl
      · have hS : t ∈ s.c.k.S := by
          by_contra hS; exact htp (mem_pm.2 ⟨g, hg, not_lt.1 hlt, hS⟩)
        refine ⟨_, .resumeN s ks kt t _ hm (E_S hb hg (not_lt.1 hlt) hS), ?_⟩
        change _ = liftG (absS { s.c.k with S := s.c.k.S.erase t, W := s.c.k.drop t } s.c.U) _ _
        rw [abs_drop hb hg htp (s.c.k.S.erase t)
          (fun u hu => by rw [hb.S_nodup.mem_erase_iff]; simp [hu]), liftG_upd₁]; rfl
    | false =>
      simp only [Bool.false_eq_true, ite_false] at ho
      subst ho
      have hU := gone_sf hb'
      refine ⟨_, .resumeU s ks kt t hU, ?_⟩
      change _ = liftG (absS s.c.k (update s.c.U t false)) _ _
      rw [abs_resumeU hb hU, liftG_upd₁]; rfl

theorem CST_run {c c' : CT × Bud × Bud} {l : List TSLabel} (h : LRun CSTStep c l c') :
    Basic2 c.1.c.k c.1.c.U →
    LRun SQTStep (absT c.1, c.2) l (absT c'.1, c'.2) ∧ Basic2 c'.1.c.k c'.1.c.U := by
  induction h with
  | nil => exact fun hb => ⟨.nil _, hb⟩
  | @cons c c₁ c₂ x l hs _ ih =>
    intro hb
    obtain ⟨h', hb'⟩ := ih (hs.base hb)
    obtain ⟨s, ks, kt⟩ := c
    obtain ⟨s₁, ks₁, kt₁⟩ := c₁
    exact ⟨.cons (bwdST hb hs) h', hb'⟩

theorem SQT_run {p p' : SRT × Bud × Bud} {l : List TSLabel} (h : LRun SQTStep p l p') :
    ∀ s : CT, Basic2 s.c.k s.c.U → p.1 = absT s →
    ∃ s', LRun CSTStep (s, p.2) l (s', p'.2) ∧ p'.1 = absT s' ∧ Basic2 s'.c.k s'.c.U := by
  induction h with
  | nil => exact fun s hb e => ⟨s, .nil _, e, hb⟩
  | cons hq _ ih =>
    intro s hb e
    obtain ⟨s₁, hs, e₁⟩ := fwdST hb e hq
    obtain ⟨s', h', e', hb'⟩ := ih s₁ (hs.base hb) e₁
    exact ⟨s', .cons hs h', e', hb'⟩

theorem absT_init : absT CT.init = SRT.init := by
  ext1
  · rfl
  · rfl
  · funext u; simp [absT, liftG, absS, CT.init, CState.init, WComp.init, SRT.init]

/-- **Timed waits (signal).** For every pair of budgets, the timed FIFO reference
and the timed encoding with `signal` have the same finite traces. -/
theorem traces_eq_signal_timed (Ks Kt : Bud) (l : List TSLabel) :
    (∃ p, TRun SRTStep (SRT.init, Ks, Kt) l p) ↔
    (∃ c, LRun CSTStep (CT.init, Ks, Kt) l c) := by
  constructor
  · rintro ⟨p, h⟩
    obtain ⟨p₀, hb₀, hq⟩ := SRTRun.toQ h SRT.Inv.init p (BSTB.refl (SRTRun.inv h SRT.Inv.init))
    rw [BSTB.init_eq hb₀] at hq
    obtain ⟨s', hc, -⟩ := SQT_run hq CT.init Basic2.init absT_init.symm
    exact ⟨_, hc⟩
  · rintro ⟨c, h⟩
    obtain ⟨hq, -⟩ := CST_run h Basic2.init
    rw [absT_init] at hq
    exact ⟨_, SQTRun.toSRT hq⟩

/-- A final state of the timed FIFO reference: no removed thread left; `Xu` /
`Xt` are the queued threads with an untimed / timed wait. -/
def SRQuietT (r : SRT) (Xu Xt : Tid → Prop) : Prop :=
  (∀ t, r.gone t = none) ∧ (∀ t, (t ∈ r.qu ∧ r.tm t = false) ↔ Xu t) ∧
    (∀ t, (t ∈ r.qu ∧ r.tm t = true) ↔ Xt t)

theorem quietST_iff {s : CT} (Xu Xt : Tid → Prop) (hb : Basic2 s.c.k s.c.U) :
    SRQuietT (absT s) Xu Xt ↔ CQuietT s Xu Xt := by
  constructor
  · rintro ⟨hg, hXu, hXt⟩
    obtain ⟨hU, hex, hW⟩ := (quietS_iff (fun t => t ∈ (absS s.c.k s.c.U).qu) hb).1
      ⟨fun t => absT_none.1 (hg t), fun _ => Iff.rfl⟩
    exact ⟨hU, hex, fun t => by rw [hW]; exact hXu t, fun t => by rw [hW]; exact hXt t⟩
  · rintro ⟨hU, hex, hXu, hXt⟩
    obtain ⟨hg, hW⟩ := (quietS_iff (fun t => t ∈ s.c.k.W.map Prod.fst) hb).2
      ⟨hU, hex, fun _ => Iff.rfl⟩
    refine ⟨fun t => absT_none.2 (hg t), fun t => ?_, fun t => ?_⟩
    · change (t ∈ (absS s.c.k s.c.U).qu ∧ _) ↔ _
      rw [hW]; exact hXu t
    · change (t ∈ (absS s.c.k s.c.U).qu ∧ _) ↔ _
      rw [hW]; exact hXt t

/-- **Final states (signal, timed).** -/
theorem stuck_eq_signal_timed (Ks Kt : Bud) (l : List TSLabel) (Xu Xt : Tid → Prop)
    (κs κt : Bud) :
    (∃ r, TRun SRTStep (SRT.init, Ks, Kt) l (r, κs, κt) ∧ SRQuietT r Xu Xt) ↔
    (∃ s, LRun CSTStep (CT.init, Ks, Kt) l (s, κs, κt) ∧ CQuietT s Xu Xt) := by
  constructor
  · rintro ⟨r, h, hq⟩
    obtain ⟨p₀, hb₀, hqr⟩ :=
      SRTRun.toQ h SRT.Inv.init (r, κs, κt) (BSTB.refl (SRTRun.inv h SRT.Inv.init))
    rw [BSTB.init_eq hb₀] at hqr
    obtain ⟨s', hc, e, hb'⟩ := SQT_run hqr CT.init Basic2.init absT_init.symm
    obtain rfl : r = absT s' := e
    exact ⟨s', hc, (quietST_iff Xu Xt hb').1 hq⟩
  · rintro ⟨s, h, hq⟩
    obtain ⟨hqr, hb'⟩ := CST_run h Basic2.init
    rw [absT_init] at hqr
    exact ⟨_, SQTRun.toSRT hqr, (quietST_iff Xu Xt hb').2 hq⟩

/-- At a quiescent state of the timed FIFO reference, a silent removal is
possible iff some queued thread has a spurious budget left or some timed queued
thread has a time-out budget left. -/
theorem quietST_tau {r : SRT} {Xu Xt : Tid → Prop} {κs κt : Bud} (hq : SRQuietT r Xu Xt) :
    (∃ p, SRTStep (r, κs, κt) none p) ↔
    ∃ t, ((Xu t ∨ Xt t) ∧ 0 < κs t) ∨ (Xt t ∧ 0 < κt t) := by
  obtain ⟨-, hXu, hXt⟩ := hq
  constructor
  · rintro ⟨p, hs⟩
    cases hs with
    | spurious _ _ _ u h hpos =>
      refine ⟨u, .inl ⟨?_, hpos⟩⟩
      cases e : r.tm u
      · exact .inl ((hXu u).1 ⟨h, e⟩)
      · exact .inr ((hXt u).1 ⟨h, e⟩)
    | timeout _ _ _ u h htu hpos => exact ⟨u, .inr ⟨(hXt u).1 ⟨h, htu⟩, hpos⟩⟩
  · rintro ⟨t, ⟨hX, hpos⟩ | ⟨hX, hpos⟩⟩
    · have hm : t ∈ r.qu := by
        rcases hX with hX | hX
        · exact ((hXu t).2 hX).1
        · exact ((hXt t).2 hX).1
      exact ⟨_, .spurious _ _ _ t hm hpos⟩
    · obtain ⟨hm, ht⟩ := (hXt t).2 hX
      exact ⟨_, .timeout _ _ _ t hm ht hpos⟩

/-! ## `signal`, unbounded and untimed: final states -/

theorem SQ_run' {q q' : SR} {l : List SLabel} (h : LRun SQStep q l q') :
    ∀ s : CState, Basic2 s.k s.U → q = absS s.k s.U →
    ∃ s', LRun CSStep s l s' ∧ q' = absS s'.k s'.U ∧ Basic2 s'.k s'.U := by
  induction h with
  | nil => exact fun s hb e => ⟨s, .nil s, e, hb⟩
  | cons hq _ ih =>
    intro s hb e
    subst e
    obtain ⟨s₁, hs, e₁⟩ := fwdS hb hq
    obtain ⟨s', h', e', hb'⟩ := ih s₁ (hb.step hs) e₁
    exact ⟨s', .cons hs h', e', hb'⟩

theorem CS_run_basic {s s' : CState} {l : List SLabel} (h : LRun CSStep s l s') :
    Basic2 s.k s.U → Basic2 s'.k s'.U := by
  induction h with
  | nil => exact id
  | cons hs _ ih => exact fun hb => ih (hb.step hs)

/-- **Final states (signal, unbounded).** -/
theorem stuck_eq_signal (l : List SLabel) (X : Tid → Prop) :
    (∃ r, SRRun SR.init l r ∧ SRQuiet r X) ↔
    (∃ s, LRun CSStep CState.init l s ∧ CQuiet s X) := by
  constructor
  · rintro ⟨r, h, hq⟩
    have hi := h.inv SR.Inv.init
    have hself : Bs r r := by
      refine ⟨fun u => .inl rfl, ?_⟩
      symm; rw [List.filter_eq_self]
      intro u hu; simp [hi.2 u hu]
    obtain ⟨q, hb, hqr⟩ := h.toQ SR.Inv.init r hself
    have : q = SR.init := by
      ext1
      · rw [hb.2]; rfl
      · funext u
        rcases hb.1 u with h' | ⟨h', -⟩
        · exact h'
        · simp [SR.init] at h'
    subst this
    obtain ⟨s', hc, e, hb'⟩ := SQ_run' hqr CState.init Basic2.init absS_init.symm
    subst e
    exact ⟨s', hc, (quietS_iff X hb').1 hq⟩
  · rintro ⟨s, h, hq⟩
    have hqr := CS_run h Basic2.init
    rw [absS_init] at hqr
    exact ⟨_, SQRun.toSRRun hqr, (quietS_iff X (CS_run_basic h Basic2.init)).2 hq⟩

end MonSpec

end Condpor
