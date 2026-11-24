import Mazurkiewicz.Condpor.Rmw.MonitorSpec

/-!
# Budgets and final (stuck) states for the wait-set encoding

Extends `MonitorSpec.lean` (one wait set).

**Budgets.** A budget `b : Tid → ℕ` gives, per thread, the number of
un-notified returns it may still take.
* `RBStep`: the reference machine `R`, in which a spurious removal of `u` needs
  `0 < b u` and consumes one unit at the removal.
* `CBStep`: the encoding `C`, in which the un-notified outcome needs `0 < b t`
  and consumes one unit at the `wait`, as `MState.spurNext` does. Every other
  step of `C` keeps the budget.
* `traces_eq_bounded K`: equal traces from `(init, K)`, for every `K`.
  `traces_eq_signal_bounded K` is the same for `signal` against the FIFO
  reference.

**Final states.** An observation is a trace, the final budget `κ`, and a set
`X` of threads.
* Reference side, `RQuiet r X`: no thread is removed and not yet resumed, and
  `X` is exactly the set of threads still in the wait set.
* Encoding side, `CQuiet s X`: no thread has an un-notified outcome pending
  (`U = ∅`), no thread of `W` is entitled to return (`exitN t = none`), and `X`
  is exactly the set of threads of `W`.
* `stuck_eq`, `stuck_eq_bounded` and `stuck_eq_signal_bounded`: `R` has a run
  with trace `l` ending in a quiescent state with set `X` (and budget `κ`) iff
  `C` has one.
* The threads of `X` with `κ t = 0` are the waiters that can never leave
  without a further `notify`/`notifyAll`/`signal`. In the reference, a waiter
  with budget left may still be removed spuriously; in `C`, that is the run in
  which it chose the un-notified outcome at its wait.
-/

namespace Condpor

namespace MonSpec

open Function

/-- Runs with silent steps. -/
inductive TRun {σ α : Type} (step : σ → Option α → σ → Prop) : σ → List α → σ → Prop
  | nil (s : σ) : TRun step s [] s
  | tau {s s₁ s₂ : σ} {l : List α} : step s none s₁ → TRun step s₁ l s₂ → TRun step s l s₂
  | step {s s₁ s₂ : σ} {x : α} {l : List α} :
      step s (some x) s₁ → TRun step s₁ l s₂ → TRun step s (x :: l) s₂

/-- Budgets of un-notified returns, per thread. -/
abbrev Bud := Tid → ℕ

/-! ## `notify`: bounded machines -/

/-- The bounded reference: the visible steps of `R` keep the budget; a spurious
removal consumes one unit of the removed thread. -/
inductive RBStep : RState × Bud → Option MLabel → RState × Bud → Prop
  | step {r r' : RState} {b : Bud} {x : MLabel} : RStep r (some x) r' →
      RBStep (r, b) (some x) (r', b)
  | spurious (r : RState) (b : Bud) (u : Tid) : r u = .waiting → 0 < b u →
      RBStep (r, b) none (update r u (.removed false), update b u (b u - 1))

/-- The bounded encoding: the steps of `C` that make no thread un-notified keep
the budget; the un-notified outcome consumes one unit at the wait. -/
inductive CBStep : CState × Bud → MLabel → CState × Bud → Prop
  | step {s s' : CState} {b : Bud} {x : MLabel} : CStep s x s' →
      (∀ t, s'.U t = true → s.U t = true) → CBStep (s, b) x (s', b)
  | waitU (s : CState) (b : Bud) (t : Tid) : t ∉ s.k.W.map Prod.fst → s.U t = false →
      0 < b t → CBStep (s, b) (.wait t) (⟨s.k, update s.U t true⟩, update b t (b t - 1))

/-- The bounded `Q` (proof device). -/
inductive QBStep : RState × Bud → MLabel → RState × Bud → Prop
  | step {q q' : RState} {b : Bud} {x : MLabel} : QStep q x q' →
      (∀ t, q' t = .removed false → q t = .removed false) → QBStep (q, b) x (q', b)
  | waitU (q : RState) (b : Bud) (t : Tid) : q t = .idle → 0 < b t →
      QBStep (q, b) (.wait t) (update q t (.removed false), update b t (b t - 1))

theorem CBStep.base {c c' : CState × Bud} {x : MLabel} (h : CBStep c x c') : CStep c.1 x c'.1 := by
  cases h with
  | step h _ => exact h
  | waitU s b t h1 h2 _ => exact .waitU s t h1 h2

/-! ### `Q` ⊆ `R`, bounded -/

theorem QBRun.toRB {p p' : RState × Bud} {l : List MLabel} (h : LRun QBStep p l p') :
    TRun RBStep p l p' := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih =>
    cases hs with
    | step hq hside =>
      cases hq with
      | wait t h => exact .step (.step (.wait _ t h)) ih
      | waitU t h => exact absurd (hside t (by simp)) (by simp [h])
      | notifyNone h => exact .step (.step (.notifyNone _ h)) ih
      | notifyOne u h => exact .step (.step (.notifyOne _ u h)) ih
      | notifyAll => exact .step (.step (.notifyAll _)) ih
      | resume t b h => exact .step (.step (.resume _ t b h)) ih
    | waitU q b t h hb =>
      refine .step (.step (.wait _ t h)) (.tau (RBStep.spurious _ _ t (by simp) hb) ?_)
      simpa using ih

/-! ### `R` ⊆ `Q`, bounded: the budget of a waiter that is already removed in `Q`
is already consumed there -/

def ind (r q : RState) (t : Tid) : ℕ := if r t = .waiting ∧ q t = .removed false then 1 else 0

def BqB (p p' : RState × Bud) : Prop := Bq p.1 p'.1 ∧ ∀ t, p.2 t = p'.2 t + ind p.1 p'.1 t

theorem BqB.back {p p₁ p₁' : RState × Bud} {x : Option MLabel} (hs : RBStep p x p₁)
    (hb : BqB p₁ p₁') :
    ∃ p', BqB p p' ∧ (x = none → p' = p₁') ∧ (∀ y, x = some y → QBStep p' y p₁') := by
  obtain ⟨q₁, b₁'⟩ := p₁'
  obtain ⟨hb, hbud⟩ := hb
  simp only at hb hbud
  cases hs with
  | step hr =>
    rename_i r r₁ b x
    cases hr with
    | wait t h =>
      have ht := hb t
      simp only [update_self] at ht
      have hBq : Bq r (update q₁ t .idle) := by
        intro u
        by_cases hu : u = t
        · subst hu; simp [h]
        · have := hb u; simpa [hu] using this
      rcases ht with ht | ⟨-, ht⟩
      · refine ⟨(update q₁ t .idle, b₁'), ⟨hBq, ?_⟩, by simp, ?_⟩
        · intro v
          rw [hbud v]
          by_cases hv : v = t
          · subst hv; simp [ind, h, ← ht]
          · simp [ind, hv]
        · rintro y ⟨⟩
          refine .step ?_ ?_
          · have := QStep.wait (update q₁ t .idle) t (by simp)
            rwa [update_idem, ht, update_eq_self] at this
          · intro v hv
            by_cases e : v = t
            · rw [e, ← ht] at hv; cases hv
            · rwa [update_of_ne e]
      · refine ⟨(update q₁ t .idle, update b₁' t (b₁' t + 1)), ⟨hBq, ?_⟩, by simp, ?_⟩
        · intro v
          rw [hbud v]
          by_cases hv : v = t
          · subst hv; simp [ind, h, ht]
          · simp [ind, hv]
        · rintro y ⟨⟩
          have := QBStep.waitU (update q₁ t .idle) (update b₁' t (b₁' t + 1)) t (by simp)
            (by simp)
          rwa [update_idem, update_idem, update_self, Nat.add_sub_cancel, ← ht, update_eq_self,
            update_eq_self] at this
    | notifyNone h =>
      refine ⟨(q₁, b₁'), ⟨hb, hbud⟩, by simp, ?_⟩
      rintro y ⟨⟩
      refine .step (.notifyNone _ fun u hu => ?_) (fun _ h => h)
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
      refine ⟨(update q₁ u .waiting, b₁'), ⟨?_, ?_⟩, by simp, ?_⟩
      · intro v
        by_cases hv : v = u
        · subst hv; simp [h]
        · have := hb v; simpa [hv] using this
      · intro v
        rw [hbud v]
        by_cases hv : v = u
        · subst hv; simp [ind, h]
        · simp [ind, hv]
      · rintro y ⟨⟩
        refine .step ?_ ?_
        · have := QStep.notifyOne (update q₁ u .waiting) u (by simp)
          rwa [update_idem, ← hq, update_eq_self] at this
        · intro v hv
          by_cases e : v = u
          · rw [e, hq] at hv; cases hv
          · rwa [update_of_ne e]
    | notifyAll =>
      have hQ : ∀ t, r t = .waiting → q₁ t = .removed true := by
        intro t ht
        have := hb t
        simp only [RState.removeAll, ht, ite_true] at this
        rcases this with h' | ⟨h', -⟩
        · exact h'.symm
        · cases h'
      refine ⟨(fun t => if r t = .waiting then .waiting else q₁ t, b₁'), ⟨?_, ?_⟩, by simp, ?_⟩
      · intro t
        by_cases ht : r t = .waiting
        · simp [ht]
        · have := hb t
          simp only [RState.removeAll, ht, ite_false] at this
          simpa [ht] using this
      · intro v
        rw [hbud v]
        by_cases hv : r v = .waiting
        · simp [ind, RState.removeAll, hv]
        · simp [ind, RState.removeAll, hv]
      · rintro y ⟨⟩
        refine .step ?_ ?_
        · have key :
              RState.removeAll (fun t => if r t = .waiting then .waiting else q₁ t) = q₁ := by
            funext t
            by_cases ht : r t = .waiting
            · simp [RState.removeAll, ht, hQ t ht]
            · have := hb t
              simp only [RState.removeAll, ht, ite_false] at this
              have hq : q₁ t ≠ .waiting := by
                rcases this with h' | ⟨-, h'⟩
                · rw [← h']; exact ht
                · rw [h']; simp
              simp [RState.removeAll, ht, hq]
          have := QStep.notifyAll (fun t => if r t = .waiting then .waiting else q₁ t)
          rwa [key] at this
        · intro v hv
          by_cases ht : r v = .waiting
          · rw [hQ v ht] at hv; cases hv
          · simpa [ht] using hv
    | resume t b0 h =>
      have ht := hb t
      simp only [update_self] at ht
      have hq : q₁ t = .idle := by
        rcases ht with ht | ⟨ht, -⟩
        · exact ht.symm
        · cases ht
      refine ⟨(update q₁ t (.removed b0), b₁'), ⟨?_, ?_⟩, by simp, ?_⟩
      · intro u
        by_cases hu : u = t
        · subst hu; simp [h]
        · have := hb u; simpa [hu] using this
      · intro v
        rw [hbud v]
        by_cases hv : v = t
        · subst hv; simp [ind, h]
        · simp [ind, hv]
      · rintro y ⟨⟩
        refine .step ?_ ?_
        · have := QStep.resume (update q₁ t (.removed b0)) t b0 (by simp)
          rwa [update_idem, ← hq, update_eq_self] at this
        · intro v hv
          by_cases e : v = t
          · rw [e, hq] at hv; cases hv
          · rwa [update_of_ne e]
  | spurious r b u h hpos =>
    have hqu : q₁ u = .removed false := by
      have := hb u
      simp only [update_self] at this
      rcases this with h' | ⟨h', -⟩
      · exact h'.symm
      · cases h'
    refine ⟨(q₁, b₁'), ⟨?_, ?_⟩, fun _ => rfl, by simp⟩
    · intro v
      by_cases hv : v = u
      · subst hv; exact .inr ⟨h, hqu⟩
      · have := hb v; simpa [hv] using this
    · intro v
      have := hbud v
      by_cases hv : v = u
      · subst hv
        simp only [update_self, ind, reduceCtorEq, false_and, ite_false, add_zero] at this
        simp only [ind, h, hqu, and_self, ite_true]
        omega
      · simpa [ind, hv] using this

theorem RBRun.toQB {p p' : RState × Bud} {l : List MLabel} (h : TRun RBStep p l p') :
    ∀ p₁', BqB p' p₁' → ∃ p₀', BqB p p₀' ∧ LRun QBStep p₀' l p₁' := by
  induction h with
  | nil s => exact fun q' hq => ⟨q', hq, .nil _⟩
  | tau hs _ ih =>
    intro q' hq'
    obtain ⟨q₁, hb₁, hr₁⟩ := ih q' hq'
    obtain ⟨q, hb, he, -⟩ := BqB.back hs hb₁
    exact ⟨q, hb, by rw [he rfl]; exact hr₁⟩
  | step hs _ ih =>
    intro q' hq'
    obtain ⟨q₁, hb₁, hr₁⟩ := ih q' hq'
    obtain ⟨q, hb, -, hst⟩ := BqB.back hs hb₁
    exact ⟨q, hb, .cons (hst _ rfl) hr₁⟩

theorem BqB.refl (p : RState × Bud) : BqB p p := by
  refine ⟨fun _ => .inl rfl, fun t => ?_⟩
  have : ¬ (p.1 t = .waiting ∧ p.1 t = .removed false) := fun ⟨h1, h2⟩ => by
    rw [h1] at h2; cases h2
  simp [ind, this]

theorem BqB.init_eq {K : Bud} {p : RState × Bud} (h : BqB (RState.init, K) p) :
    p = (RState.init, K) := by
  obtain ⟨q, b⟩ := p
  obtain ⟨h1, h2⟩ := h
  have hq : q = RState.init := by
    funext t
    rcases h1 t with h' | ⟨h', -⟩
    · exact h'.symm
    · cases h'
  subst hq
  have : b = K := by funext t; have := h2 t; simpa [ind, RState.init] using this.symm
  rw [this]

/-! ### `Q` ↔ `C`, bounded -/

theorem fwdB {s : CState} {q q' : RState} {m : ℕ → Tid} {b b' : Bud} {x : MLabel}
    (hb : Basic s.k s.U) (hr : Rel q m s.k s.U) (h : QBStep (q, b) x (q', b')) :
    ∃ s' m', CBStep (s, b) x (s', b') ∧ Rel q' m' s'.k s'.U := by
  cases h with
  | step hq hside =>
    obtain ⟨s', m', hc, hr'⟩ := fwd hb hr hq
    exact ⟨s', m', .step hc fun t ht => hr.removedF (hside t (hr'.hU t ht)), hr'⟩
  | waitU _ _ t h hpos =>
    obtain ⟨h1, h2⟩ := hr.idle h
    exact ⟨_, m, .waitU s b t h1 h2 hpos, H_waitU hr h1⟩

theorem backB {s s' : CState} {b b' : Bud} {x : MLabel} (hb : Basic s.k s.U)
    (hinv : ∃ r₀ m₀, Rel r₀ m₀ s.k s.U) (h : CBStep (s, b) x (s', b')) {q' : RState}
    {m' : ℕ → Tid} (hr' : Rel q' m' s'.k s'.U) :
    ∃ q m, Rel q m s.k s.U ∧ QBStep (q, b) x (q', b') := by
  cases h with
  | step hc hside =>
    obtain ⟨q, m, hr, hq⟩ := back_step hb hinv hc hr'
    exact ⟨q, m, hr, .step hq fun t ht => hr.hU t (hside t (hr'.removedF ht))⟩
  | waitU _ _ t h1 h2 hpos =>
    obtain ⟨hw, hr1⟩ := B_waitU h1 h2 hr'
    refine ⟨_, _, hr1, ?_⟩
    have := QBStep.waitU (update q' t .idle) b t (by simp) hpos
    rwa [update_idem, ← hw, update_eq_self] at this

theorem inv_runB {c c' : CState × Bud} {l : List MLabel} (h : LRun CBStep c l c') :
    Basic c.1.k c.1.U → (∃ r m, Rel r m c.1.k c.1.U) →
    Basic c'.1.k c'.1.U ∧ ∃ r m, Rel r m c'.1.k c'.1.U := by
  induction h with
  | nil => exact fun hb hi => ⟨hb, hi⟩
  | cons hs _ ih =>
    rintro hb ⟨r, m, hr⟩
    exact ih (hb.step hs.base) (inv_step hb hr hs.base)

theorem C_backB {c c' : CState × Bud} {l : List MLabel} (h : LRun CBStep c l c') :
    Basic c.1.k c.1.U → (∃ r m, Rel r m c.1.k c.1.U) →
    ∀ q' m', Rel q' m' c'.1.k c'.1.U →
      ∃ q m, Rel q m c.1.k c.1.U ∧ LRun QBStep (q, c.2) l (q', c'.2) := by
  induction h with
  | nil s => exact fun _ _ r' m' hr => ⟨r', m', hr, .nil _⟩
  | cons hs _ ih =>
    rename_i c c₁ _ _ _
    rintro hb ⟨r₀, m₀, hr₀⟩ q' m' hr'
    obtain ⟨q₁, m₁, hr₁, hq₁⟩ := ih (hb.step hs.base) (inv_step hb hr₀ hs.base) q' m' hr'
    obtain ⟨s, b⟩ := c
    obtain ⟨s₁, b₁⟩ := c₁
    obtain ⟨q, m, hr, hq⟩ := backB hb ⟨r₀, m₀, hr₀⟩ hs hr₁
    exact ⟨q, m, hr, .cons hq hq₁⟩

theorem Q_fwdB {p p' : RState × Bud} {l : List MLabel} (h : LRun QBStep p l p') :
    ∀ s m, Basic s.k s.U → Rel p.1 m s.k s.U →
    ∃ s' m', LRun CBStep (s, p.2) l (s', p'.2) ∧ Rel p'.1 m' s'.k s'.U ∧ Basic s'.k s'.U := by
  induction h with
  | nil => exact fun s m hb hr => ⟨s, m, .nil _, hr, hb⟩
  | cons hq _ ih =>
    rename_i p p₁ _ _ _
    intro s m hb hr
    obtain ⟨q, b⟩ := p
    obtain ⟨q₁, b₁⟩ := p₁
    obtain ⟨s₁, m₁, hs, hr₁⟩ := fwdB hb hr hq
    obtain ⟨s', m', h', hr', hb'⟩ := ih s₁ m₁ (hb.step hs.base) hr₁
    exact ⟨s', m', .cons hs h', hr', hb'⟩

/-- **Budgets (notify).** For every budget, the bounded reference and the
bounded encoding have the same finite traces. -/
theorem traces_eq_bounded (K : Bud) (l : List MLabel) :
    (∃ p, TRun RBStep (RState.init, K) l p) ↔ (∃ c, LRun CBStep (CState.init, K) l c) := by
  constructor
  · rintro ⟨p, h⟩
    obtain ⟨p₀, hb₀, hq⟩ := RBRun.toQB h p (BqB.refl p)
    rw [BqB.init_eq hb₀] at hq
    obtain ⟨s', m', hc, -⟩ := Q_fwdB hq CState.init id Basic.init Rel.init
    exact ⟨_, hc⟩
  · rintro ⟨c, h⟩
    obtain ⟨-, r', m', hr'⟩ := inv_runB h Basic.init ⟨_, _, Rel.init⟩
    obtain ⟨q, m, hr, hq⟩ := C_backB h Basic.init ⟨_, _, Rel.init⟩ r' m' hr'
    rw [Rel.init_eq hr] at hq
    exact ⟨_, QBRun.toRB hq⟩

/-! ### Final states -/

/-- A final state of the reference: no removed thread is left un-resumed, and
`X` is the wait set. -/
def RQuiet (r : RState) (X : Tid → Prop) : Prop :=
  (∀ t b, r t ≠ .removed b) ∧ ∀ t, r t = .waiting ↔ X t

/-- A final state of the encoding: no un-notified outcome is left, no waiter is
entitled to return, and `X` is the set of the waiters. -/
def CQuiet (s : CState) (X : Tid → Prop) : Prop :=
  (∀ t, s.U t = false) ∧ (∀ t ∈ s.k.W.map Prod.fst, s.k.exitN t = none) ∧
    ∀ t, t ∈ s.k.W.map Prod.fst ↔ X t

theorem quiet_iff {r : RState} {m : ℕ → Tid} {s : CState} (X : Tid → Prop)
    (hb : Basic s.k s.U) (hr : Rel r m s.k s.U) : RQuiet r X ↔ CQuiet s X := by
  have hrt : (∀ t, s.U t = false) → (∀ t ∈ s.k.W.map Prod.fst, s.k.exitN t = none) →
      ∀ t, r t ≠ .removed true := by
    intro hU hex t ht
    obtain ⟨g, hg⟩ := hr.removedT ht
    have hn := hex t (mem_fst.2 ⟨g, hg⟩)
    by_cases hlt : g < s.k.a
    · rw [hb.exitN_lt hg hlt] at hn; cases hn
    · obtain ⟨j₁, hj₁, hm₁⟩ := hr.surj t g hg (not_lt.1 hlt) ht
      obtain ⟨g', hg', -, h2, -⟩ := hr.mT j₁ hj₁
      rw [hm₁] at hg'
      have := hb.uniq hg hg'
      obtain ⟨j₀, hf⟩ := head_filter_some hj₁ (show g < j₁ by omega)
      rw [hb.exitN_find hg (not_lt.1 hlt) hf] at hn; cases hn
  constructor
  · rintro ⟨hrem, hX⟩
    have hU : ∀ t, s.U t = false := fun t => by
      cases h : s.U t
      · rfl
      · exact absurd (hr.hU t h) (hrem t false)
    refine ⟨hU, ?_, ?_⟩
    · intro t ht
      obtain ⟨g, hg⟩ := mem_fst.1 ht
      have hw : r t = .waiting := (hr.hW t g hg).resolve_right (hrem t true)
      have ha : s.k.a ≤ g := not_lt.1 fun hlt => hrem t true (hr.hWa t g hg hlt)
      cases hex : s.k.exitN t with
      | none => rfl
      | some k' =>
        obtain ⟨j₀, hf, -⟩ := hb.exitN_some hg ha hex
        obtain ⟨hj₀, -⟩ := head_filter hb.T_sorted hf
        obtain ⟨_, _, _, _, h3⟩ := hr.mT j₀ hj₀
        exact absurd h3 (hrem _ true)
    · intro t
      constructor
      · intro ht
        obtain ⟨g, hg⟩ := mem_fst.1 ht
        exact (hX t).1 ((hr.hW t g hg).resolve_right (hrem t true))
      · intro ht
        obtain ⟨g, hg, -⟩ := hr.waiting ((hX t).2 ht)
        exact mem_fst.2 ⟨g, hg⟩
  · rintro ⟨hU, hex, hX⟩
    have hT := hrt hU hex
    refine ⟨fun t b => ?_, fun t => ?_⟩
    · cases b with
      | false => exact fun h => absurd (hr.removedF h) (by simp [hU t])
      | true => exact hT t
    · constructor
      · intro h
        obtain ⟨g, hg, -⟩ := hr.waiting h
        exact (hX t).1 (mem_fst.2 ⟨g, hg⟩)
      · intro h
        obtain ⟨g, hg⟩ := mem_fst.1 ((hX t).2 h)
        exact (hr.hW t g hg).resolve_right (hT t)

/-- **Final states (notify, bounded).** -/
theorem stuck_eq_bounded (K : Bud) (l : List MLabel) (X : Tid → Prop) (κ : Bud) :
    (∃ r, TRun RBStep (RState.init, K) l (r, κ) ∧ RQuiet r X) ↔
    (∃ s, LRun CBStep (CState.init, K) l (s, κ) ∧ CQuiet s X) := by
  constructor
  · rintro ⟨r, h, hq⟩
    obtain ⟨p₀, hb₀, hqr⟩ := RBRun.toQB h (r, κ) (BqB.refl _)
    rw [BqB.init_eq hb₀] at hqr
    obtain ⟨s', m', hc, hr', hb'⟩ := Q_fwdB hqr CState.init id Basic.init Rel.init
    exact ⟨s', hc, (quiet_iff X hb' hr').1 hq⟩
  · rintro ⟨s, h, hq⟩
    obtain ⟨hb', r', m', hr'⟩ := inv_runB h Basic.init ⟨_, _, Rel.init⟩
    obtain ⟨q, m, hr, hqr⟩ := C_backB h Basic.init ⟨_, _, Rel.init⟩ r' m' hr'
    rw [Rel.init_eq hr] at hqr
    exact ⟨r', QBRun.toRB hqr, (quiet_iff X hb' hr').2 hq⟩

theorem Q_fwd' {r r' : RState} {l : List MLabel} (h : LRun QStep r l r') :
    ∀ s m, Basic s.k s.U → Rel r m s.k s.U →
    ∃ s' m', LRun CStep s l s' ∧ Rel r' m' s'.k s'.U ∧ Basic s'.k s'.U := by
  induction h with
  | nil => exact fun s m hb hr => ⟨s, m, .nil _, hr, hb⟩
  | cons hq _ ih =>
    intro s m hb hr
    obtain ⟨s₁, m₁, hs, hr₁⟩ := fwd hb hr hq
    obtain ⟨s', m', h', hr', hb'⟩ := ih s₁ m₁ (hb.step hs) hr₁
    exact ⟨s', m', .cons hs h', hr', hb'⟩

/-- **Final states (notify, unbounded).** -/
theorem stuck_eq (l : List MLabel) (X : Tid → Prop) :
    (∃ r, RRun RState.init l r ∧ RQuiet r X) ↔
    (∃ s, LRun CStep CState.init l s ∧ CQuiet s X) := by
  constructor
  · rintro ⟨r, h, hq⟩
    obtain ⟨s', m', hc, hr', hb'⟩ := Q_fwd' h.toQRun CState.init id Basic.init Rel.init
    exact ⟨s', hc, (quiet_iff X hb' hr').1 hq⟩
  · rintro ⟨s, h, hq⟩
    obtain ⟨hb', r', m', hr'⟩ := inv_run h Basic.init ⟨_, _, Rel.init⟩
    obtain ⟨q, m, hr, hqr⟩ := C_back h Basic.init ⟨_, _, Rel.init⟩ r' m' hr'
    rw [Rel.init_eq hr] at hqr
    exact ⟨r', QRun.toRRun hqr, (quiet_iff X hb' hr').2 hq⟩


/-! ## `signal`: bounded machines -/

inductive SRBStep : SR × Bud → Option SLabel → SR × Bud → Prop
  | step {r r' : SR} {b : Bud} {x : SLabel} : SRStep r (some x) r' → SRBStep (r, b) (some x) (r', b)
  | spurious (r : SR) (b : Bud) (u : Tid) : u ∈ r.qu → 0 < b u →
      SRBStep (r, b) none (⟨r.qu.erase u, update r.gone u (some false)⟩, update b u (b u - 1))

inductive CSBStep : CState × Bud → SLabel → CState × Bud → Prop
  | step {s s' : CState} {b : Bud} {x : SLabel} : CSStep s x s' →
      (∀ t, s'.U t = true → s.U t = true) → CSBStep (s, b) x (s', b)
  | waitU (s : CState) (b : Bud) (t : Tid) : t ∉ s.k.W.map Prod.fst → s.U t = false →
      0 < b t → CSBStep (s, b) (.wait t) (⟨s.k, update s.U t true⟩, update b t (b t - 1))

inductive SQBStep : SR × Bud → SLabel → SR × Bud → Prop
  | step {q q' : SR} {b : Bud} {x : SLabel} : SQStep q x q' →
      (∀ t, q'.gone t = some false → q.gone t = some false) → SQBStep (q, b) x (q', b)
  | waitU (q : SR) (b : Bud) (t : Tid) : t ∉ q.qu → q.gone t = none → 0 < b t →
      SQBStep (q, b) (.wait t) (⟨q.qu, update q.gone t (some false)⟩, update b t (b t - 1))

theorem CSBStep.base {c c' : CState × Bud} {x : SLabel} (h : CSBStep c x c') :
    CSStep c.1 x c'.1 := by
  cases h with
  | step h _ => exact h
  | waitU s b t h1 h2 _ => exact .waitU s t h1 h2

theorem SRBStep.base {p p' : SR × Bud} {x : Option SLabel} (h : SRBStep p x p') :
    SRStep p.1 x p'.1 := by
  cases h with
  | step h => exact h
  | spurious r b u h _ => exact .spurious r u h

theorem SQBRun.toSRB {p p' : SR × Bud} {l : List SLabel} (h : LRun SQBStep p l p') :
    TRun SRBStep p l p' := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih =>
    cases hs with
    | step hq hside =>
      cases hq with
      | wait t h1 h2 => exact .step (.step (.wait _ t h1 h2)) ih
      | waitU t h1 h2 => exact absurd (hside t (by simp)) (by simp [h2])
      | signalNone h => exact .step (.step (.signalNone _ h)) ih
      | signalOne h rest e => exact .step (.step (.signalOne _ h rest e)) ih
      | signalAll => exact .step (.step (.signalAll _)) ih
      | resume t b h => exact .step (.step (.resume _ t b h)) ih
    | waitU q b t h1 h2 hb =>
      refine .step (.step (.wait _ t h1 h2))
        (.tau (SRBStep.spurious _ _ t (by simp) hb) ?_)
      simpa [List.erase_append_right _ h1] using ih

def indS (r q : SR) (t : Tid) : ℕ := if t ∈ r.qu ∧ q.gone t = some false then 1 else 0

def BsB (p p' : SR × Bud) : Prop := Bs p.1 p'.1 ∧ ∀ t, p.2 t = p'.2 t + indS p.1 p'.1 t

theorem BsB.back {p p₁ p₁' : SR × Bud} {x : Option SLabel} (hi : p.1.Inv) (hs : SRBStep p x p₁)
    (hb : BsB p₁ p₁') :
    ∃ p', BsB p p' ∧ (x = none → p' = p₁') ∧ (∀ y, x = some y → SQBStep p' y p₁') := by
  obtain ⟨q₁, b₁'⟩ := p₁'
  obtain ⟨⟨hg, hqq⟩, hbud⟩ := hb
  simp only at hg hqq hbud
  cases hs with
  | step hr =>
    rename_i r r₁ b x
    obtain ⟨hnd, hqn⟩ := hi
    simp only at hnd hqn
    cases hr with
    | wait t h1 h2 =>
      simp only at hg hqq hbud
      rcases hg t with ht | ⟨-, ht⟩
      · refine ⟨(⟨r.qu.filter (fun u => decide (q₁.gone u ≠ some false)), q₁.gone⟩, b₁'),
          ⟨⟨?_, rfl⟩, ?_⟩, by simp, ?_⟩
        · intro u
          rcases hg u with h | ⟨hu, h⟩
          · exact .inl h
          · refine .inr ⟨?_, h⟩
            simp only [List.mem_append, List.mem_singleton] at hu
            rcases hu with hu | rfl
            · exact hu
            · rw [ht, h2] at h; cases h
        · intro v
          dsimp only
          rw [hbud v]
          by_cases hv : v = t
          · subst hv; simp [indS, ht, h2, h1]
          · simp [indS, hv]
        · rintro y ⟨⟩
          have e : q₁ = ⟨r.qu.filter (fun u => decide (q₁.gone u ≠ some false)) ++ [t],
              q₁.gone⟩ := by
            ext1
            · rw [hqq, List.filter_append]; simp [ht, h2]
            · rfl
          refine .step ?_ (fun _ h => h)
          rw [e]
          exact .wait _ t (fun h => h1 (List.mem_of_mem_filter h)) (ht.trans h2)
      · have hnq : t ∉ q₁.qu := by
          rw [hqq]; intro h; simpa [ht] using (List.mem_filter.1 h).2
        refine ⟨(⟨q₁.qu, update q₁.gone t none⟩, update b₁' t (b₁' t + 1)), ⟨⟨?_, ?_⟩, ?_⟩,
          by simp, ?_⟩
        · intro u
          by_cases e : u = t
          · simp only [e, update_self]; exact .inl h2.symm
          · simp only [update_of_ne e]
            rcases hg u with h | ⟨hu, h⟩
            · exact .inl h
            · refine .inr ⟨?_, h⟩
              simp only [List.mem_append, List.mem_singleton] at hu
              exact hu.resolve_right e
        · change q₁.qu = _
          rw [hqq, List.filter_append]
          simp only [ht, ne_eq, not_true_eq_false, decide_false, List.filter_cons,
            List.filter_nil, Bool.false_eq_true, ite_false, List.append_nil]
          apply List.filter_congr
          intro u hu
          have e : u ≠ t := fun e => h1 (e ▸ hu)
          simp [update_of_ne e]
        · intro v
          dsimp only
          rw [hbud v]
          by_cases hv : v = t
          · subst hv; simp [indS, ht, h1]
          · simp [indS, hv]
        · rintro y ⟨⟩
          have := SQBStep.waitU ⟨q₁.qu, update q₁.gone t none⟩ (update b₁' t (b₁' t + 1)) t hnq
            (by simp) (by simp)
          simp only [update_idem, update_self, Nat.add_sub_cancel, update_eq_self] at this
          rwa [← ht, update_eq_self] at this
    | signalNone h =>
      refine ⟨(q₁, b₁'), ⟨⟨hg, hqq⟩, hbud⟩, by simp, ?_⟩
      rintro y ⟨⟩
      exact .step (.signalNone _ (by rw [hqq, h]; rfl)) (fun _ h => h)
    | signalOne h rest e =>
      rw [e, List.nodup_cons] at hnd
      have hh : q₁.gone h = some true := by
        rcases hg h with h' | ⟨h', -⟩
        · rw [h']; simp
        · exact absurd h' hnd.1
      refine ⟨(⟨h :: q₁.qu, update q₁.gone h none⟩, b₁'), ⟨⟨?_, ?_⟩, ?_⟩, by simp, ?_⟩
      · intro u
        by_cases eu : u = h
        · simp only [eu, update_self]; exact .inl (hqn h (by rw [e]; simp)).symm
        · simp only [update_of_ne eu]
          rcases hg u with h' | ⟨hu, h'⟩
          · exact .inl (by rw [h']; exact update_of_ne eu _ _)
          · exact .inr ⟨by rw [e]; exact List.mem_cons_of_mem _ hu, h'⟩
      · change h :: q₁.qu = _
        rw [e, List.filter_cons]
        simp only [update_self, ne_eq, reduceCtorEq, not_false_eq_true, decide_true, ite_true]
        rw [hqq]
        congr 1
        apply List.filter_congr
        intro u hu
        have eu : u ≠ h := fun e' => hnd.1 (e' ▸ hu)
        simp [update_of_ne eu]
      · intro v
        rw [hbud v]
        by_cases hv : v = h
        · subst hv; simp [indS, e, hnd.1]
        · simp [indS, e, hv]
      · rintro y ⟨⟩
        refine .step ?_ ?_
        · have := SQStep.signalOne ⟨h :: q₁.qu, update q₁.gone h none⟩ h q₁.qu rfl
          simp only [update_idem] at this
          rwa [← hh, update_eq_self] at this
        · intro v hv
          by_cases eu : v = h
          · rw [eu, hh] at hv; cases hv
          · simpa [update_of_ne eu] using hv
    | signalAll =>
      have hall : ∀ u ∈ r.qu, q₁.gone u = some true := by
        intro u hu
        rcases hg u with h' | ⟨h', -⟩
        · rw [h']; simp [hu]
        · simp at h'
      refine ⟨(⟨r.qu, fun u => if u ∈ r.qu then none else q₁.gone u⟩, b₁'), ⟨⟨?_, ?_⟩, ?_⟩,
        by simp, ?_⟩
      · intro u
        by_cases hu : u ∈ r.qu
        · simp only [hu, ite_true]; exact .inl (hqn u hu).symm
        · simp only [hu, ite_false]
          rcases hg u with h' | ⟨h', -⟩
          · exact .inl (by rw [h']; simp [hu])
          · simp at h'
      · change r.qu = _
        symm; rw [List.filter_eq_self]
        intro u hu; simp [hu]
      · intro v
        rw [hbud v]
        by_cases hv : v ∈ r.qu
        · simp [indS, hv]
        · simp [indS, hv]
      · rintro y ⟨⟩
        have key : (⟨[], fun u => if u ∈ r.qu then some true else
            (fun u => if u ∈ r.qu then none else q₁.gone u) u⟩ : SR) = q₁ := by
          ext1
          · rw [hqq]; rfl
          · funext u
            by_cases hu : u ∈ r.qu
            · simp [hu, hall u hu]
            · simp [hu]
        have hst : SQStep ⟨r.qu, fun u => if u ∈ r.qu then none else q₁.gone u⟩ .signalAll
            ⟨[], fun u => if u ∈ r.qu then some true else
              (fun u => if u ∈ r.qu then none else q₁.gone u) u⟩ := SQStep.signalAll _
        rw [key] at hst
        refine .step hst ?_
        intro v hv
        by_cases hu : v ∈ r.qu
        · rw [hall v hu] at hv; cases hv
        · simpa [hu] using hv
    | resume t b0 h =>
      have htq : t ∉ r.qu := fun ht => by rw [hqn t ht] at h; cases h
      have hq0 : q₁.gone t = none := by
        rcases hg t with h' | ⟨h', -⟩
        · rw [h']; simp
        · exact absurd h' htq
      refine ⟨(⟨q₁.qu, update q₁.gone t (some b0)⟩, b₁'), ⟨⟨?_, ?_⟩, ?_⟩, by simp, ?_⟩
      · intro u
        by_cases e : u = t
        · simp only [e, update_self]; exact .inl h.symm
        · simp only [update_of_ne e]
          rcases hg u with h' | ⟨hu, h'⟩
          · exact .inl (by rw [h']; exact update_of_ne e _ _)
          · exact .inr ⟨hu, h'⟩
      · change q₁.qu = _
        rw [hqq]
        apply List.filter_congr
        intro u hu
        have e : u ≠ t := fun e => htq (e ▸ hu)
        simp [update_of_ne e]
      · intro v
        rw [hbud v]
        by_cases hv : v = t
        · subst hv; simp [indS, htq]
        · simp [indS, hv]
      · rintro y ⟨⟩
        refine .step ?_ ?_
        · have := SQStep.resume ⟨q₁.qu, update q₁.gone t (some b0)⟩ t b0 (by simp)
          simp only [update_idem] at this
          rwa [← hq0, update_eq_self] at this
        · intro v hv
          by_cases e : v = t
          · rw [e, hq0] at hv; cases hv
          · simpa [update_of_ne e] using hv
  | spurious r b u h hpos =>
    obtain ⟨hnd, hqn⟩ := hi
    have hqu : q₁.gone u = some false := by
      rcases hg u with h' | ⟨-, h'⟩
      · rw [h']; simp
      · exact h'
    refine ⟨(q₁, b₁'), ⟨⟨?_, ?_⟩, ?_⟩, fun _ => rfl, by simp⟩
    · intro v
      by_cases e : v = u
      · rw [e]; exact .inr ⟨h, hqu⟩
      · rcases hg v with h' | ⟨hv, h'⟩
        · exact .inl (by rw [h']; exact update_of_ne e _ _)
        · exact .inr ⟨List.mem_of_mem_erase hv, h'⟩
    · rw [hqq]
      apply filter_erase_of_not
      simp [hqu]
    · intro v
      have := hbud v
      by_cases hv : v = u
      · subst hv
        have hne : v ∉ r.qu.erase v := List.Nodup.not_mem_erase hnd
        simp only [update_self, indS, hne, false_and, ite_false, add_zero] at this
        simp only [indS, h, hqu, and_self, ite_true]
        omega
      · have hm : v ∈ r.qu.erase u ↔ v ∈ r.qu := List.mem_erase_of_ne hv
        simpa [indS, hv, hm] using this

theorem SRBRun.toQB {p p' : SR × Bud} {l : List SLabel} (h : TRun SRBStep p l p') :
    p.1.Inv → ∀ q', BsB p' q' → ∃ q, BsB p q ∧ LRun SQBStep q l q' := by
  induction h with
  | nil s => exact fun _ q' hq => ⟨q', hq, .nil _⟩
  | tau hs _ ih =>
    intro hi q' hq'
    obtain ⟨q₁, hb₁, hr₁⟩ := ih (hi.step hs.base) q' hq'
    obtain ⟨q, hb, he, -⟩ := BsB.back hi hs hb₁
    exact ⟨q, hb, by rw [he rfl]; exact hr₁⟩
  | step hs _ ih =>
    intro hi q' hq'
    obtain ⟨q₁, hb₁, hr₁⟩ := ih (hi.step hs.base) q' hq'
    obtain ⟨q, hb, -, hst⟩ := BsB.back hi hs hb₁
    exact ⟨q, hb, .cons (hst _ rfl) hr₁⟩

theorem SRBRun.inv {p p' : SR × Bud} {l : List SLabel} (h : TRun SRBStep p l p') (hi : p.1.Inv) :
    p'.1.Inv := by
  induction h with
  | nil => exact hi
  | tau hs _ ih => exact ih (hi.step hs.base)
  | step hs _ ih => exact ih (hi.step hs.base)

theorem BsB.refl {p : SR × Bud} (hi : p.1.Inv) : BsB p p := by
  refine ⟨⟨fun u => .inl rfl, ?_⟩, fun t => ?_⟩
  · symm; rw [List.filter_eq_self]
    intro u hu; simp [hi.2 u hu]
  · have : ¬ (t ∈ p.1.qu ∧ p.1.gone t = some false) := fun ⟨h1, h2⟩ => by
      rw [hi.2 t h1] at h2; cases h2
    simp [indS, this]

theorem BsB.init_eq {K : Bud} {p : SR × Bud} (h : BsB (SR.init, K) p) : p = (SR.init, K) := by
  obtain ⟨q, b⟩ := p
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hq : q = SR.init := by
    ext1
    · rw [h2]; rfl
    · funext u
      rcases h1 u with h' | ⟨h', -⟩
      · exact h'
      · simp [SR.init] at h'
  subst hq
  have : b = K := by funext t; have := h3 t; simpa [indS, SR.init] using this.symm
  rw [this]

theorem gone_sf_of {k : WComp} {U : Tid → Bool} {t : Tid} (h : U t = true) :
    (absS k U).gone t = some false := by simp [absS, h]

theorem fwdSB {s : CState} {q' : SR} {b b' : Bud} {x : SLabel} (hb : Basic2 s.k s.U)
    (h : SQBStep (absS s.k s.U, b) x (q', b')) :
    ∃ s', CSBStep (s, b) x (s', b') ∧ q' = absS s'.k s'.U := by
  generalize hq : absS s.k s.U = q at h
  cases h with
  | step hstep hside =>
    subst hq
    obtain ⟨s', hc, rfl⟩ := fwdS hb hstep
    exact ⟨s', .step hc fun t ht => gone_sf (hside t (gone_sf_of ht)), rfl⟩
  | waitU _ _ t h1 h2 hpos =>
    subst hq
    obtain ⟨hU, hW⟩ := gone_none h2
    have ht : t ∉ s.k.W.map Prod.fst := fun h => h1 (hW h)
    exact ⟨_, .waitU s b t ht hU hpos, abs_waitU.symm⟩

theorem bwdSB {s s' : CState} {b b' : Bud} {x : SLabel} (hb : Basic2 s.k s.U)
    (h : CSBStep (s, b) x (s', b')) :
    SQBStep (absS s.k s.U, b) x (absS s'.k s'.U, b') := by
  cases h with
  | step hc hside =>
    exact .step (bwdS hb hc) fun t ht => gone_sf_of (hside t (gone_sf ht))
  | waitU _ _ t ht hU hpos =>
    rw [abs_waitU]
    exact .waitU _ b t (fun h => ht (pm_sub h)) (by simp [absS, hU, ht]) hpos

theorem CSB_run {c c' : CState × Bud} {l : List SLabel} (h : LRun CSBStep c l c') :
    Basic2 c.1.k c.1.U →
    LRun SQBStep (absS c.1.k c.1.U, c.2) l (absS c'.1.k c'.1.U, c'.2) ∧ Basic2 c'.1.k c'.1.U := by
  induction h with
  | nil => exact fun hb => ⟨.nil _, hb⟩
  | @cons c c₁ c₂ x l hs _ ih =>
    intro hb
    obtain ⟨h', hb'⟩ := ih (hb.step hs.base)
    obtain ⟨s, b⟩ := c
    obtain ⟨s₁, b₁⟩ := c₁
    exact ⟨.cons (bwdSB hb hs) h', hb'⟩

theorem SQB_run {p p' : SR × Bud} {l : List SLabel} (h : LRun SQBStep p l p') :
    ∀ s : CState, Basic2 s.k s.U → p.1 = absS s.k s.U →
    ∃ s', LRun CSBStep (s, p.2) l (s', p'.2) ∧ p'.1 = absS s'.k s'.U ∧ Basic2 s'.k s'.U := by
  induction h with
  | nil => exact fun s hb e => ⟨s, .nil _, e, hb⟩
  | @cons p p₁ p₂ x l hq _ ih =>
    intro s hb e
    obtain ⟨q, b⟩ := p
    obtain ⟨q₁, b₁⟩ := p₁
    subst e
    obtain ⟨s₁, hs, e₁⟩ := fwdSB hb hq
    obtain ⟨s', h', e', hb'⟩ := ih s₁ (hb.step hs.base) e₁
    exact ⟨s', .cons hs h', e', hb'⟩

/-- **Budgets (signal).** -/
theorem traces_eq_signal_bounded (K : Bud) (l : List SLabel) :
    (∃ p, TRun SRBStep (SR.init, K) l p) ↔ (∃ c, LRun CSBStep (CState.init, K) l c) := by
  constructor
  · rintro ⟨p, h⟩
    obtain ⟨p₀, hb₀, hq⟩ := SRBRun.toQB h SR.Inv.init p (BsB.refl (SRBRun.inv h SR.Inv.init))
    rw [BsB.init_eq hb₀] at hq
    obtain ⟨s', hc, -⟩ := SQB_run hq CState.init Basic2.init absS_init.symm
    exact ⟨_, hc⟩
  · rintro ⟨c, h⟩
    obtain ⟨hq, -⟩ := CSB_run h Basic2.init
    rw [absS_init] at hq
    exact ⟨_, SQBRun.toSRB hq⟩

/-- A final state of the FIFO reference: no removed thread left, `X` is the
queue (as a set). -/
def SRQuiet (r : SR) (X : Tid → Prop) : Prop :=
  (∀ t, r.gone t = none) ∧ ∀ t, t ∈ r.qu ↔ X t

theorem quietS_iff {s : CState} (X : Tid → Prop) (hb : Basic2 s.k s.U) :
    SRQuiet (absS s.k s.U) X ↔ CQuiet s X := by
  constructor
  · rintro ⟨hg, hX⟩
    have hU : ∀ t, s.U t = false := fun t => (gone_none (hg t)).1
    refine ⟨hU, fun t ht => ?_, fun t => ?_⟩
    · obtain ⟨g, hg', ha, hS⟩ := mem_pm.1 ((gone_none (hg t)).2 ht)
      exact E_none hb hg' ha hS
    · exact ⟨fun ht => (hX t).1 ((gone_none (hg t)).2 ht), fun ht => pm_sub ((hX t).2 ht)⟩
  · rintro ⟨hU, hex, hX⟩
    have hpm : ∀ t, t ∈ s.k.W.map Prod.fst → t ∈ s.k.pending.map Prod.fst := by
      intro t ht
      obtain ⟨g, hg⟩ := mem_fst.1 ht
      have hn := hex t ht
      by_cases hlt : g < s.k.a
      · rw [E_lt hb hg hlt] at hn; cases hn
      · by_cases hS : t ∈ s.k.S
        · rw [E_S hb hg (not_lt.1 hlt) hS] at hn; cases hn
        · exact mem_pm.2 ⟨g, hg, not_lt.1 hlt, hS⟩
    refine ⟨fun t => ?_, fun t => ⟨fun ht => (hX t).1 (pm_sub ht), fun ht => hpm t ((hX t).2 ht)⟩⟩
    have := hpm t
    simp only [absS, hU t, Bool.false_eq_true, ite_false]
    split_ifs with h1
    · exact absurd (this h1.1) h1.2
    · rfl

/-- **Final states (signal, bounded).** -/
theorem stuck_eq_signal_bounded (K : Bud) (l : List SLabel) (X : Tid → Prop) (κ : Bud) :
    (∃ r, TRun SRBStep (SR.init, K) l (r, κ) ∧ SRQuiet r X) ↔
    (∃ s, LRun CSBStep (CState.init, K) l (s, κ) ∧ CQuiet s X) := by
  constructor
  · rintro ⟨r, h, hq⟩
    obtain ⟨p₀, hb₀, hqr⟩ := SRBRun.toQB h SR.Inv.init (r, κ) (BsB.refl (SRBRun.inv h SR.Inv.init))
    rw [BsB.init_eq hb₀] at hqr
    obtain ⟨s', hc, e, hb'⟩ := SQB_run hqr CState.init Basic2.init absS_init.symm
    simp only at e
    subst e
    exact ⟨s', hc, (quietS_iff X hb').1 hq⟩
  · rintro ⟨s, h, hq⟩
    obtain ⟨hqr, hb'⟩ := CSB_run h Basic2.init
    rw [absS_init] at hqr
    exact ⟨_, SQBRun.toSRB hqr, (quietS_iff X hb').2 hq⟩

end MonSpec

end Condpor
