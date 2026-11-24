import Mazurkiewicz.Must.Extend
import Mazurkiewicz.Must.AlgCompute
import Mazurkiewicz.Must.EnumSpec

/-!
# The two replays of M2 and their relations (milestone M5)

Plan: decision Q10 (two replays), plan row M5 item "agreement with M2's executable `replay`",
`completion_congr` for M2's `schedComplete`.

For a selection `T` and a Boolean test `consB`, the tie-break is `T.pick consB` (M2). The
configurations are those of M2 whose order lists exactly the events of the graph (`OrdMem`; the
first component of `Config.Good`, `EnumSpec.lean`).

* `canonAdd_some`, `canonAdd_of_canonStep`: M2's `canonAdd` is `CanonStep` (no model needed for
  the first; the second needs a well-formed graph, for `byId`).
* `replay_some`, `replay_of_Replay`: M2's `replay` is `Replay` (Q10 (i)); the second for a
  consistent start and `TieQ9`.
* `Completion.Spec`, `schedComplete_spec`: M2's `schedComplete` (Q10 (ii)) is a run of
  `SchedStep`; from a consistent graph it never ends in `failed` (Lemma A.10).
* `schedComplete_congr`: M2's scheduler-following completion of two configurations with the same
  graph ends in the same graph and in the same way (`completion_congr` for M2's procedure).

Every result holds for every model `M` with a Boolean test `consB` deciding `M.cons` on graphs
with `Supp` (where `M` occurs).
-/

namespace Must

open Graph Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q]
variable {M : Model Q} {P : Program Q} {consB : Graph Q → Bool} {T : Sel Q}

/-- The insertion order lists exactly the events of the graph. -/
def Config.OrdMem (c : Config Q) : Prop := ∀ x, x ∈ c.order ↔ x ∈ c.G.events

omit [Membership Val Q] in
theorem Config.OrdMem.add {c : Config Q} (h : c.OrdMem) (e : Ev Q) (src : Option (Src Q))
    (out : Option Val) : (c.add e src out).OrdMem := by
  intro x
  simp only [Config.add, List.mem_append, List.mem_singleton, add_events, Finset.mem_insert, h x]
  exact or_comm

omit [DecidableEq Q] [Membership Val Q] in
/-- `byId` returns an event of the graph with the identity. -/
theorem Config.byId_some {c : Config Q} (hc : c.OrdMem) {id : Tid × ℕ} {s : Ev Q}
    (h : c.byId id = some s) : s ∈ c.G.events ∧ (s.tid, s.idx) = id := by
  unfold Config.byId at h
  have h1 := List.find?_some h
  have h2 := List.mem_of_find?_eq_some h
  simp only [decide_eq_true_eq] at h1
  exact ⟨(hc s).mp h2, Prod.ext h1.1 h1.2⟩

omit [DecidableEq Q] in
/-- In a well-formed graph, `byId` of the identity of an event returns the event. -/
theorem Config.byId_eq {c : Config Q} (hc : c.OrdMem) (hw : c.G.Wf) {s : Ev Q}
    (hs : s ∈ c.G.events) : c.byId (s.tid, s.idx) = some s := by
  unfold Config.byId
  cases h : c.order.find? (fun e => decide (e.tid = s.tid ∧ e.idx = s.idx)) with
  | none =>
    have := List.find?_eq_none.mp h s ((hc s).mpr hs)
    simp at this
  | some s₀ =>
    have h1 := List.find?_some h
    have h2 := List.mem_of_find?_eq_some h
    simp only [decide_eq_true_eq] at h1
    rw [hw.idx_inj s₀ ((hc s₀).mp h2) s hs h1.1 h1.2]

/-! ### `canonAdd` and `replay` -/

omit [DecidableEq Q] [Membership Val Q] in
private theorem nextEv_tid {G : Graph Q} {t : Tid} {e : Ev Q} (h : P.nextEv G t = some e) :
    e.tid = t := by
  unfold Program.nextEv at h
  obtain ⟨l, -, rfl⟩ := Option.map_eq_some_iff.mp h
  rfl

omit [Membership Val Q] in
/-- M2's `canonAdd` is a canonical step. -/
theorem canonAdd_some {c c' : Config Q} {e : Ev Q} (hc : c.OrdMem)
    (h : canonAdd consB T P c e = some c') :
    ∃ src out, c' = c.add e src out ∧ CanonStep (T.pick consB) P c.G e (c.G.add e src out) := by
  unfold canonAdd at h
  by_cases hn : P.nextEv c.G e.tid = some e
  · simp only [hn, ne_eq, not_true_eq_false, ↓reduceIte] at h
    obtain ⟨t, i, l⟩ := e
    cases l with
    | recv a vals =>
      cases hb : a.blocking with
      | true =>
        have hB : (⟨t, i, .recv a vals⟩ : Ev Q).IsRecvB := by simp [Ev.IsRecvB, Lab.IsRecvB, hb]
        simp only [hb, ↓reduceIte] at h
        cases hp : T.pick consB c.G ⟨t, i, .recv a vals⟩ with
        | none => simp [hp] at h
        | some id =>
          cases hi : c.byId id with
          | none => simp [hp, hi] at h
          | some s =>
            simp only [hp, hi, Option.some.injEq] at h
            subst h
            obtain ⟨hs, rfl⟩ := Config.byId_some hc hi
            exact ⟨_, _, rfl, hn, _, _, Canon.intro (fun _ => ⟨s, hs, hp, rfl, rfl⟩)
              (fun h' => absurd hB (Lab.not_isRecvB_of_isRecvNB h'))
              (fun h' => absurd trivial (Lab.IsND.not_isRecv h'))
              (fun h' => absurd trivial h'), rfl⟩
      | false =>
        have hNB : (⟨t, i, .recv a vals⟩ : Ev Q).IsRecvNB := by
          simp [Ev.IsRecvNB, Lab.IsRecvNB, hb]
        simp only [hb, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h
        exact ⟨_, _, rfl, hn, _, _, Canon.intro
          (fun h' => absurd h' (Lab.not_isRecvB_of_isRecvNB hNB)) (fun _ => ⟨rfl, rfl⟩)
          (fun h' => absurd trivial (Lab.IsND.not_isRecv h')) (fun h' => absurd trivial h'), rfl⟩
    | send m d v =>
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨_, _, rfl, hn, _, _, Canon.intro (fun h' => h'.elim) (fun h' => h'.elim)
        (fun h' => h'.elim) (fun _ _ => ⟨rfl, rfl⟩), rfl⟩
    | nd S =>
      cases hv : minVal S with
      | none => simp [hv] at h
      | some v =>
        simp only [hv, Option.some.injEq] at h
        subst h
        exact ⟨_, _, rfl, hn, _, _, Canon.intro (fun h' => h'.elim) (fun h' => h'.elim)
          (fun _ => ⟨rfl, v, hv, rfl⟩) (fun _ h' => absurd trivial h'), rfl⟩
    | block =>
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨_, _, rfl, hn, _, _, Canon.intro (fun h' => h'.elim) (fun h' => h'.elim)
        (fun h' => h'.elim) (fun _ _ => ⟨rfl, rfl⟩), rfl⟩
    | error =>
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨_, _, rfl, hn, _, _, Canon.intro (fun h' => h'.elim) (fun h' => h'.elim)
        (fun h' => h'.elim) (fun _ _ => ⟨rfl, rfl⟩), rfl⟩
  · simp [hn] at h

/-- A canonical step from a well-formed graph is computed by M2's `canonAdd`. -/
theorem canonAdd_of_canonStep {c : Config Q} {e : Ev Q} {G' : Graph Q} (hc : c.OrdMem)
    (hw : c.G.Wf) (h : CanonStep (T.pick consB) P c.G e G') :
    ∃ c', canonAdd consB T P c e = some c' ∧ c' = c.add e (G'.rf e) (G'.nd e) ∧ c'.G = G' := by
  obtain ⟨hn, src, out, hcan, rfl⟩ := h
  have hrf : (c.G.add e src out).rf e = src := by simp
  have hnd : (c.G.add e src out).nd e = out := by simp
  rw [hrf, hnd]
  refine ⟨c.add e src out, ?_, rfl, rfl⟩
  unfold canonAdd
  simp only [hn, ne_eq, not_true_eq_false, ↓reduceIte]
  obtain ⟨t, i, l⟩ := e
  cases l with
  | recv a vals =>
    cases hb : a.blocking with
    | true =>
      have hB : (⟨t, i, .recv a vals⟩ : Ev Q).IsRecvB := by simp [Ev.IsRecvB, Lab.IsRecvB, hb]
      obtain ⟨s, hs, hp, rfl, rfl⟩ := hcan.recvB hB
      simp [hb, hp, Config.byId_eq hc hw hs]
    | false =>
      have hNB : (⟨t, i, .recv a vals⟩ : Ev Q).IsRecvNB := by
        simp [Ev.IsRecvNB, Lab.IsRecvNB, hb]
      obtain ⟨rfl, rfl⟩ := hcan.recvNB hNB
      simp [hb]
  | send m d v =>
    obtain ⟨rfl, rfl⟩ := hcan.other (fun h => h.elim) (fun h => h.elim)
    rfl
  | nd S =>
    obtain ⟨rfl, v, hv, rfl⟩ := hcan.nd trivial
    simp only [Ev.ndSet, Lab.ndSet] at hv
    simp [hv]
  | block =>
    obtain ⟨rfl, rfl⟩ := hcan.other (fun h => h.elim) (fun h => h.elim)
    rfl
  | error =>
    obtain ⟨rfl, rfl⟩ := hcan.other (fun h => h.elim) (fun h => h.elim)
    rfl

omit [Membership Val Q] in
/-- M2's `replay` is canonical replay (Q10 (i)); no model is needed. -/
theorem replay_some :
    ∀ (l : List (Ev Q)) {c c' : Config Q}, c.OrdMem → replay consB T P c l = some c' →
      Replay (T.pick consB) P c.G l c'.G ∧ c'.order = c.order ++ l
  | [], c, c', _, h => by
    simp only [replay, Option.some.injEq] at h
    subst h
    exact ⟨.nil _, by simp⟩
  | e :: l, c, c', hc, h => by
    simp only [replay] at h
    cases ha : canonAdd consB T P c e with
    | none => simp [ha] at h
    | some c₁ =>
      simp only [ha] at h
      obtain ⟨src, out, rfl, hs⟩ := canonAdd_some hc ha
      obtain ⟨h1, h2⟩ := replay_some l (hc.add e src out) h
      exact ⟨.cons hs h1, by rw [h2]; simp [Config.add]⟩

/-- A canonical replay from a consistent graph is computed by M2's `replay`. -/
theorem replay_of_Replay (hT : TieQ9 M (T.pick consB)) :
    ∀ (l : List (Ev Q)) {c : Config Q} {G' : Graph Q}, c.OrdMem → M.cons c.G →
      Replay (T.pick consB) P c.G l G' → ∃ c', replay consB T P c l = some c' ∧ c'.G = G'
  | [], c, G', _, _, h => by
    cases h
    exact ⟨c, rfl, rfl⟩
  | e :: l, c, G', hc, hcons, h => by
    cases h with
    | cons hs hr =>
      obtain ⟨c₁, h1, hc₁, h3⟩ := canonAdd_of_canonStep hc (M.wf _ hcons) hs
      subst h3
      have hc1 : c₁.OrdMem := hc₁ ▸ hc.add _ _ _
      obtain ⟨c', h4, h5⟩ := replay_of_Replay hT l hc1 (hs.cons hT hcons) hr
      exact ⟨c', by simp only [replay, h1]; exact h4, h5⟩

/-! ### `schedComplete` -/

/-- What M2's `schedComplete` from `G` returns, as a run of `SchedStep`. -/
def Completion.Spec (M : Model Q) (tie : Tie Q) (P : Program Q) (stop : Ev Q → Bool)
    (G : Graph Q) : Completion Q → Prop
  | .full c' => ReflTransGen (SchedStep M tie P stop) G c'.G ∧ M.nextP P c'.G = none
  | .stopped c' => ReflTransGen (SchedStep M tie P stop) G c'.G ∧
      ∃ e, M.nextP P c'.G = some e ∧ stop e = true
  | .outOfFuel c' => ReflTransGen (SchedStep M tie P stop) G c'.G
  | .failed _ _ => False

/-- `schedComplete_spec`: from a consistent graph, M2's `schedComplete` is a run of scheduler
steps; it ends full, stopped, or out of fuel, never `failed` (Lemma A.10). -/
theorem schedComplete_spec (hcB : ∀ H : Graph Q, H.Supp → (consB H = true ↔ M.cons H))
    (hT : TieQ9 M (T.pick consB)) (stop : Ev Q → Bool) :
    ∀ (k : ℕ) (c : Config Q), c.OrdMem → M.cons c.G →
      (schedComplete consB T P stop k c).Spec M (T.pick consB) P stop c.G
  | 0, c, _, _ => ReflTransGen.refl
  | k + 1, c, hc, hcons => by
    have hS := (M.wf _ hcons).supp
    have hnx : P.nextP consB c.G = M.nextP P c.G := Model.nextP_eq consB hcB P hS
    simp only [schedComplete]
    cases hn : P.nextP consB c.G with
    | none => exact ⟨ReflTransGen.refl, hnx ▸ hn⟩
    | some e =>
      simp only
      cases hs : stop e with
      | true => exact ⟨ReflTransGen.refl, e, hnx ▸ hn, hs⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        obtain ⟨G', e', he', -, hst⟩ := exists_schedStep hT hcons (hnx ▸ hn) hs
        rw [← hnx, hn, Option.some.injEq] at he'
        subst he'
        obtain ⟨c₁, h1, hc₁, h3⟩ := canonAdd_of_canonStep hc (M.wf _ hcons) hst
        subst h3
        simp only [h1]
        have hc1 : c₁.OrdMem := hc₁ ▸ hc.add _ _ _
        have ih := schedComplete_spec hcB hT stop k c₁ hc1 (hst.cons hT hcons)
        have hstep : SchedStep M (T.pick consB) P stop c.G c₁.G := ⟨e, hnx ▸ hn, hs, hst⟩
        revert ih
        cases schedComplete consB T P stop k c₁ with
        | full c' =>
          simp only [Completion.Spec]
          exact fun ih => ⟨ReflTransGen.head hstep ih.1, ih.2⟩
        | stopped c' =>
          simp only [Completion.Spec]
          exact fun ih => ⟨ReflTransGen.head hstep ih.1, ih.2⟩
        | outOfFuel c' =>
          simp only [Completion.Spec]
          exact fun ih => ReflTransGen.head hstep ih
        | failed c' e' =>
          simp only [Completion.Spec]
          exact fun ih => ih.elim

/-- `completion_congr` for M2's procedure: the scheduler-following completions of two
configurations with the same consistent graph end in the same graph and in the same way. -/
theorem schedComplete_congr (hcB : ∀ H : Graph Q, H.Supp → (consB H = true ↔ M.cons H))
    (hT : TieQ9 M (T.pick consB)) (stop : Ev Q → Bool) :
    ∀ (k : ℕ) (c c' : Config Q), c.OrdMem → c'.OrdMem → c.G = c'.G → M.cons c.G →
      (schedComplete consB T P stop k c).cfg.G = (schedComplete consB T P stop k c').cfg.G ∧
      (schedComplete consB T P stop k c).isStopped =
        (schedComplete consB T P stop k c').isStopped
  | 0, c, c', _, _, hG, _ => ⟨hG, rfl⟩
  | k + 1, c, c', hc, hc', hG, hcons => by
    simp only [schedComplete]
    rw [← hG]
    cases hn : P.nextP consB c.G with
    | none => exact ⟨hG, rfl⟩
    | some e =>
      simp only
      cases hs : stop e with
      | true => exact ⟨hG, rfl⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hnx : P.nextP consB c.G = M.nextP P c.G :=
          Model.nextP_eq consB hcB P (M.wf _ hcons).supp
        obtain ⟨G', e', he', -, hst⟩ := exists_schedStep hT hcons (hnx ▸ hn) hs
        rw [← hnx, hn, Option.some.injEq] at he'
        subst he'
        have hcons' := hst.cons hT hcons
        obtain ⟨c₁, h1, hc₁, h3⟩ := canonAdd_of_canonStep hc (M.wf _ hcons) hst
        obtain ⟨c₂, h1', hc₂, h3'⟩ := canonAdd_of_canonStep hc' (hG ▸ M.wf _ hcons)
          (hG ▸ hst)
        simp only [h1, h1']
        exact schedComplete_congr hcB hT stop k _ _ (hc₁ ▸ hc.add _ _ _) (hc₂ ▸ hc'.add _ _ _)
          (h3.trans h3'.symm) (h3 ▸ hcons')

end Must

#print axioms Must.Config.byId_eq
#print axioms Must.canonAdd_some
#print axioms Must.canonAdd_of_canonStep
#print axioms Must.replay_some
#print axioms Must.replay_of_Replay
#print axioms Must.schedComplete_spec
#print axioms Must.schedComplete_congr
