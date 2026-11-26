import Mazurkiewicz.Induction.MP.CheckSound

/-!
# Message passing: two-thread state-machine programs (helpers for C9, C10)

`induction-popl`, `mp.tex` ex:pingpong and `p2p.tex` ex:p2p describe each thread as a state
machine over the values returned by its events ("as functions of traces"). This file gives
that construction once, for the two examples (plan `plan/ind/TRACK-C-PLAN.md`, milestones
C9a, C10a), and the parts of the hypotheses of `checkAsyn_sound` / `checkP2P_sound` that do not
depend on the particular machines.

* `runSt δ s u`: the state after the trace `u` from `s` (a left fold). `Mach Q St`: a machine
  with an initial state, a dead state `†` (no action, absorbing), the action of a state and the
  next state on a returned value; a stopping action returning `⊥` leads to `†`, no ND action.
  `Mach.prog t₁ t₂ h M₁ M₂`: the trace-function program with threads `[t₁, t₂]` (not bounded,
  not `ofCodes`).
* `ValOK l r`: a returned value fits its label (sends and errors return `⊥`, blocking receives
  a value); `Wf.valOK_ret`: true on well-formed graphs. `exec_at`: the event `(t, i)` of an
  execution. `badErr_iff`: `G` has an error event iff the second machine is in `†` (the
  invariant behind `hdet`), under a local condition on the second machine.
* Section 6: `envAlpha` (the states and `pend(G)`), `envF`, `envWord` (a computable sorted
  representative `msort` of the multiset), `repU` (representative traces); `envAlpha_hconf`,
  `envF_hf` (from `mp_compose_2`, `mp_compose_3`).
* Section 7: `p2pAlpha` (the states and `pend_1(G)`, `pend_2(G)`), `p2pWords`, `p2pF`;
  `p2pAlpha_hconf`, `p2pF_hf` (from `p2p_compose_1`, `p2p_compose_2`).
-/

namespace Must

namespace Ind

open Graph

/-! ### Runs of a state machine -/

/-- The state after the trace `u` from `s`. -/
def runSt {St : Type} (δ : St → Option Val → St) (s : St) (u : List (Option Val)) : St :=
  u.foldl δ s

theorem runSt_append {St : Type} (δ : St → Option Val → St) (s : St) (u v : List (Option Val)) :
    runSt δ s (u ++ v) = runSt δ (runSt δ s u) v :=
  List.foldl_append

theorem runSt_snoc {St : Type} (δ : St → Option Val → St) (s : St) (u : List (Option Val))
    (r : Option Val) : runSt δ s (u ++ [r]) = δ (runSt δ s u) r := by
  rw [runSt_append]
  rfl

/-- A thread as a state machine over returned values. -/
structure Mach (Q St : Type) where
  /-- the initial state -/
  s0 : St
  /-- the state `†`: no action, absorbing -/
  dead : St
  /-- the action of a state -/
  act : St → Option (Lab Q)
  /-- the next state on a returned value -/
  next : St → Option Val → St
  /-- `†` has no action -/
  act_dead : act dead = none
  /-- `†` is absorbing -/
  next_dead : ∀ r, next dead r = dead
  /-- a stopping action that returns `⊥` leads to `†` -/
  stops : ∀ s l, act s = some l → l.Stops → next s none = dead
  /-- no ND action -/
  no_nd : ∀ s S, act s ≠ some (.nd S)

namespace Mach

variable {Q St : Type} (M : Mach Q St)

/-- The state of the machine after the trace `u`. -/
def st (u : List (Option Val)) : St := runSt M.next M.s0 u

theorem st_append (u v : List (Option Val)) : M.st (u ++ v) = runSt M.next (M.st u) v :=
  runSt_append _ _ _ _

theorem st_snoc (u : List (Option Val)) (r : Option Val) : M.st (u ++ [r]) = M.next (M.st u) r :=
  runSt_snoc _ _ _ _

theorem runSt_dead (x : List (Option Val)) : runSt M.next M.dead x = M.dead := by
  induction x using List.reverseRecOn with
  | nil => rfl
  | append_singleton x r ih => rw [runSt_snoc, ih, M.next_dead]

variable {S₁ S₂ : Type}

/-- The program with the threads `[t₁, t₂]` running the machines `M₁`, `M₂`. -/
def prog (t₁ t₂ : Tid) (h : t₁ ≠ t₂) (M₁ : Mach Q S₁) (M₂ : Mach Q S₂) : Program Q where
  threads := [t₁, t₂]
  nodup := by simp [h]
  step t u := if t = t₁ then M₁.act (M₁.st u) else if t = t₂ then M₂.act (M₂.st u) else none
  step_none t ht := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ht
    simp [ht.1, ht.2]
  stop t u l hl hs := by
    by_cases h1 : t = t₁
    · subst h1
      simp only [↓reduceIte] at hl ⊢
      rw [M₁.st_snoc, M₁.stops _ _ hl hs, M₁.act_dead]
    · by_cases h2 : t = t₂
      · subst h2
        simp only [h1, ↓reduceIte] at hl ⊢
        rw [M₂.st_snoc, M₂.stops _ _ hl hs, M₂.act_dead]
      · simp [h1, h2] at hl
  nd_ne t u S hl := by
    by_cases h1 : t = t₁
    · subst h1
      simp only [↓reduceIte] at hl
      exact absurd hl (M₁.no_nd _ _)
    · by_cases h2 : t = t₂
      · subst h2
        simp only [h1, ↓reduceIte] at hl
        exact absurd hl (M₂.no_nd _ _)
      · simp [h1, h2] at hl

variable {t₁ t₂ : Tid} {h : t₁ ≠ t₂} {M₁ : Mach Q S₁} {M₂ : Mach Q S₂}

theorem prog_step₁ (u : List (Option Val)) : (prog t₁ t₂ h M₁ M₂).step t₁ u = M₁.act (M₁.st u) :=
  ite_eq_left rfl

theorem prog_step₂ (u : List (Option Val)) : (prog t₁ t₂ h M₁ M₂).step t₂ u = M₂.act (M₂.st u) :=
  (ite_eq_right (Ne.symm h)).trans (ite_eq_left rfl)

theorem prog_step_other {t : Tid} (h1 : t ≠ t₁) (h2 : t ≠ t₂) (u : List (Option Val)) :
    (prog t₁ t₂ h M₁ M₂).step t u = none :=
  (ite_eq_right h1).trans (ite_eq_right h2)

theorem mem_prog_threads {t : Tid} : t ∈ (prog t₁ t₂ h M₁ M₂).threads ↔ t = t₁ ∨ t = t₂ := by
  change t ∈ [t₁, t₂] ↔ _
  simp

/-- A program of tagged machines is tagged. -/
theorem prog_tagged (m : Comm) (h₁ : ∀ s l, M₁.act s = some l → l.model? = none ∨ l.model? = some m)
    (h₂ : ∀ s l, M₂.act s = some l → l.model? = none ∨ l.model? = some m) :
    (prog t₁ t₂ h M₁ M₂).Tagged m := by
  intro t u l hl
  by_cases ht1 : t = t₁
  · subst ht1
    rw [prog_step₁] at hl
    exact h₁ _ _ hl
  · by_cases ht2 : t = t₂
    · subst ht2
      rw [prog_step₂] at hl
      exact h₂ _ _ hl
    · rw [prog_step_other ht1 ht2] at hl
      cases hl

/-- Two traces with the same state are equivalent (def:state). -/
theorem prog_futEq {t : Tid} (ht : t ∈ (prog t₁ t₂ h M₁ M₂).threads) {u u' : List (Option Val)}
    (h₁ : t = t₁ → M₁.st u = M₁.st u') (h₂ : t = t₂ → M₂.st u = M₂.st u') :
    FutEq ((prog t₁ t₂ h M₁ M₂).step t) u u' := by
  intro x
  rcases mem_prog_threads.mp ht with rfl | rfl
  · rw [prog_step₁, prog_step₁, M₁.st_append, M₁.st_append, h₁ rfl]
  · rw [prog_step₂, prog_step₂, M₂.st_append, M₂.st_append, h₂ rfl]

end Mach

/-! ### Returned values of an execution -/

/-- A returned value fits its label: sends and errors return `⊥`, blocking receives a value. -/
def ValOK {Q : Type} (l : Lab Q) (r : Option Val) : Prop :=
  (l.IsSend → r = none) ∧ (l = .error → r = none) ∧ (l.IsRecvB → r.isSome)

variable {Q : Type} [DecidableEq Q] [Membership Val Q]

omit [DecidableEq Q] in
theorem _root_.Must.Graph.Wf.valOK_ret {G : Graph Q} (hG : G.Wf) {e : Ev Q} (he : e ∈ G.events) :
    ValOK e.lab (G.ret e) := by
  have hnone : ¬ e.IsRecv → G.ret e = G.nd e := fun hr => by
    unfold Graph.ret
    rw [hG.rf_none (Or.inr hr)]
  refine ⟨fun hs => ?_, fun he' => ?_, fun hb => ?_⟩
  · rw [hnone hs.not_isRecv]
    exact hG.nd_none (Or.inr hs.not_isND)
  · have hr : ¬ e.IsRecv := by
      change ¬ e.lab.IsRecv
      rw [he']
      exact id
    have hn : ¬ e.IsND := by
      change ¬ e.lab.IsND
      rw [he']
      exact id
    rw [hnone hr]
    exact hG.nd_none (Or.inr hn)
  · have hs : (G.rf e).isSome := (hG.rf_isSome e).mpr ⟨he, hb.isRecv⟩
    unfold Graph.ret
    rcases hrf : G.rf e with _ | _ | s
    · rw [hrf] at hs
      cases hs
    · exact absurd hb (Lab.not_isRecvB_of_isRecvNB (hG.rf_bot e hrf))
    · have hm := hG.rf_match e s hrf
      unfold Ev.Matches at hm
      change (Graph.sendVal s.lab).isSome = true
      rcases hsl : s.lab with _ | ⟨m, d, v⟩ | _ | _ | _ <;> rw [hsl] at hm <;>
        first | exact absurd hm id | rfl

omit [DecidableEq Q] [Membership Val Q] in
theorem traceBefore_succ (G : Graph Q) (t i : ℕ) :
    G.traceBefore t (i + 1) = G.traceBefore t i ++ [G.retAt t i] := by
  simp [Graph.traceBefore, List.range_succ]

omit [DecidableEq Q] in
/-- The event `(t, i)` of an execution: its label is the action of `t` after the earlier values,
and the value it returns fits the label. -/
theorem exec_at {P : Program Q} {G : Graph Q} (hG : G.Wf) (hE : P.Exec G) {t i : ℕ}
    (hi : i < G.cnt t) :
    ∃ y ∈ G.events, y.tid = t ∧ y.idx = i ∧ P.step t (G.traceBefore t i) = some y.lab ∧
      ValOK y.lab (G.retAt t i) := by
  obtain ⟨y, hy, rfl, rfl⟩ := hG.exists_of_lt_cnt hi
  exact ⟨y, hy, rfl, rfl, hE y hy, (hG.retAt_eq hy) ▸ hG.valOK_ret hy⟩

/-! ### The error invariant (`hdet`) -/

section BadErr

variable {S₁ S₂ : Type} {t₁ t₂ : Tid} {h : t₁ ≠ t₂} {M₁ : Mach Q S₁} {M₂ : Mach Q S₂}

omit [DecidableEq Q] [Membership Val Q] in
theorem st_traceBefore_dead {St : Type} (M : Mach Q St) (G : Graph Q) (t : Tid) {i j : ℕ}
    (hij : i ≤ j) (hd : M.st (G.traceBefore t i) = M.dead) : M.st (G.traceBefore t j) = M.dead := by
  induction j, hij using Nat.le_induction with
  | base => exact hd
  | succ j _ ih => rw [traceBefore_succ, M.st_snoc, ih, M.next_dead]

omit [DecidableEq Q] in
/-- `G` has an error event iff the second machine is in `†` after its trace: the first machine
has no error action, and the second enters `†` from a live state only by its error action
(given a fitting returned value). -/
theorem badErr_iff {G : Graph Q} (hG : G.Wf) (hE : (Mach.prog t₁ t₂ h M₁ M₂).Exec G)
    (h₁ : ∀ s, M₁.act s ≠ some .error)
    (hloc : ∀ s l r, s ≠ M₂.dead → M₂.act s = some l → M₂.next s r = M₂.dead → ValOK l r →
      l = .error)
    (hs0 : M₂.s0 ≠ M₂.dead) :
    G ∈ BadErr ↔ M₂.st (G.trace t₂) = M₂.dead := by
  constructor
  · rintro ⟨e, he, hl⟩
    have hs := hE e he
    rw [hl] at hs
    have hi := hG.idx_lt_cnt he
    have hr : G.retAt e.tid e.idx = none := by
      rw [hG.retAt_eq he]
      exact (hG.valOK_ret he).2.1 hl
    by_cases ht1 : e.tid = t₁
    · rw [ht1, Mach.prog_step₁] at hs
      exact absurd hs (h₁ _)
    · by_cases ht2 : e.tid = t₂
      · rw [ht2, Mach.prog_step₂] at hs
        rw [ht2] at hi hr
        have hd : M₂.st (G.traceBefore t₂ (e.idx + 1)) = M₂.dead := by
          rw [traceBefore_succ, M₂.st_snoc, hr]
          exact M₂.stops _ _ hs trivial
        exact st_traceBefore_dead M₂ G t₂ hi hd
      · rw [Mach.prog_step_other ht1 ht2] at hs
        cases hs
  · intro hd
    suffices hsuff : ∀ i, i ≤ G.cnt t₂ → M₂.st (G.traceBefore t₂ i) = M₂.dead → G ∈ BadErr from
      hsuff _ le_rfl hd
    intro i
    induction i with
    | zero => exact fun _ h0 => absurd h0 hs0
    | succ i ih =>
      intro hi hd'
      by_cases hdi : M₂.st (G.traceBefore t₂ i) = M₂.dead
      · exact ih (by omega) hdi
      · obtain ⟨y, hy, -, -, hs, hv⟩ := exec_at hG hE (by omega : i < G.cnt t₂)
        rw [Mach.prog_step₂] at hs
        rw [traceBefore_succ, M₂.st_snoc] at hd'
        exact ⟨y, hy, hloc _ _ _ hdi hs hd' hv⟩

omit [Membership Val Q] in
/-- `Bad_err` is extension-closed. -/
theorem badErr_ext {G G' : Graph Q} (hb : G ∈ BadErr) (hp : G.IsPrefixOf G') : G' ∈ BadErr := by
  obtain ⟨e, he, hl⟩ := hb
  exact ⟨e, hp.events_subset he, hl⟩

end BadErr

/-! ### A computable representative of a multiset of messages -/

/-- Messages ordered by their pairing code (a decidable total order). -/
def msgLe (a b : Msg) : Prop := Nat.pair a.1 a.2 ≤ Nat.pair b.1 b.2

instance : DecidableRel msgLe := fun _ _ => inferInstanceAs (Decidable (_ ≤ _))

instance : IsTrans Msg msgLe := ⟨fun _ _ _ => Nat.le_trans⟩

instance : Std.Total msgLe := ⟨fun _ _ => Nat.le_total _ _⟩

instance : Std.Antisymm msgLe := ⟨fun a b h1 h2 => by
  have h := Nat.pair_eq_pair.mp (Nat.le_antisymm h1 h2)
  exact Prod.ext h.1 h.2⟩

/-- The sorted list of a multiset of messages (insertion sort; structural, so it reduces in the
kernel). Computable, unlike `Multiset.toList`. -/
def msort (s : Multiset Msg) : List Msg :=
  Quot.liftOn s (List.insertionSort msgLe) fun l₁ l₂ hp =>
    List.Perm.eq_of_pairwise' (List.pairwise_insertionSort msgLe l₁)
      (List.pairwise_insertionSort msgLe l₂)
      (((List.perm_insertionSort msgLe l₁).trans hp).trans (List.perm_insertionSort msgLe l₂).symm)

theorem coe_msort (s : Multiset Msg) : (↑(msort s) : Multiset Msg) = s :=
  Quot.inductionOn s fun l => Quot.sound (List.perm_insertionSort msgLe l)

/-! ### Section 6: the abstraction `h` for two machines -/

section Env

variable {S₁ S₂ : Type} (t₁ t₂ : Tid) (M₁ : Mach Q S₁) (M₂ : Mach Q S₂)

/-- `h` of def:mp-abstraction for two machines: the two states and `pend(G)`. -/
def envAlpha (G : Graph Q) : S₁ × S₂ × Multiset Msg :=
  (M₁.st (G.trace t₁), M₂.st (G.trace t₂), G.pendM)

/-- The abstract value after a fragment: run the machines on the fragment's traces; the pending
messages are those of the fragment. -/
def envF (b : S₁ × S₂ × Multiset Msg) (H : Graph Q) : S₁ × S₂ × Multiset Msg :=
  (runSt M₁.next b.1 (H.trace t₁), runSt M₂.next b.2.1 (H.trace t₂), H.pendM)

/-- The seed word of an abstract value: the sorted pending messages. -/
def envWord (b : S₁ × S₂ × Multiset Msg) : List Msg := msort b.2.2

/-- Representative traces of the states of an abstract value. -/
def repU {X : Type} (r₁ : S₁ → List (Option Val)) (r₂ : S₂ → List (Option Val))
    (b : S₁ × S₂ × X) : Tid → List (Option Val) :=
  fun t => if t = t₁ then r₁ b.1 else if t = t₂ then r₂ b.2.1 else []

variable {t₁ t₂ M₁ M₂} {h : t₁ ≠ t₂}

omit [DecidableEq Q] [Membership Val Q] in
theorem repU_fut {X : Type} {r₁ : S₁ → List (Option Val)} {r₂ : S₂ → List (Option Val)}
    (hr₁ : ∀ s, M₁.st (r₁ s) = s) (hr₂ : ∀ s, M₂.st (r₂ s) = s) (b : S₁ × S₂ × X)
    {t : Tid} (ht : t ∈ (Mach.prog t₁ t₂ h M₁ M₂).threads) {u : List (Option Val)}
    (hu₁ : t = t₁ → M₁.st u = b.1) (hu₂ : t = t₂ → M₂.st u = b.2.1) :
    FutEq ((Mach.prog t₁ t₂ h M₁ M₂).step t) (repU t₁ t₂ r₁ r₂ b t) u := by
  refine Mach.prog_futEq ht (fun h1 => ?_) (fun h2 => ?_)
  · subst h1
    simp only [repU, ↓reduceIte]
    rw [hr₁, hu₁ rfl]
  · subst h2
    simp only [repU, Ne.symm h, ↓reduceIte]
    rw [hr₂, hu₂ rfl]

/-- `hconf` of `checkAsyn_sound` for `envAlpha`: true for every graph. -/
theorem envAlpha_hconf {r₁ : S₁ → List (Option Val)} {r₂ : S₂ → List (Option Val)}
    (hr₁ : ∀ s, M₁.st (r₁ s) = s) (hr₂ : ∀ s, M₂.st (r₂ s) = s) (M : Model Q) :
    ∀ G, ExecM M (Mach.prog t₁ t₂ h M₁ M₂) G →
      (∀ t ∈ (Mach.prog t₁ t₂ h M₁ M₂).threads, FutEq ((Mach.prog t₁ t₂ h M₁ M₂).step t)
        (repU t₁ t₂ r₁ r₂ (envAlpha t₁ t₂ M₁ M₂ G) t) (G.trace t)) ∧
      (↑(envWord (envAlpha t₁ t₂ M₁ M₂ G)) : Multiset Msg) = G.pendM := fun _ _ =>
  ⟨fun _ ht => repU_fut hr₁ hr₂ _ ht (fun h1 => h1 ▸ rfl) (fun h2 => h2 ▸ rfl), coe_msort _⟩

/-- `hf` of `checkAsyn_sound` for `envAlpha`, `envF` (lem:mp-compose (2), (3)). -/
theorem envF_hf {ν : Tid} (hν : ν ∉ (Mach.prog t₁ t₂ h M₁ M₂).threads)
    (hP : (Mach.prog t₁ t₂ h M₁ M₂).Tagged .asyn) {A : Set (S₁ × S₂ × Multiset Msg)} {K : ℕ} :
    ∀ G, ExecM Model.asyn (Mach.prog t₁ t₂ h M₁ M₂) G → envAlpha t₁ t₂ M₁ M₂ G ∈ A →
      ∀ σ, IsPendEnum G σ → word σ = envWord (envAlpha t₁ t₂ M₁ M₂ G) →
      ∀ H, Frag Model.asyn ((Mach.prog t₁ t₂ h M₁ M₂).envRes ν hν G.trace (word σ))
          (envW ν (word σ)) H →
        H.len ((Mach.prog t₁ t₂ h M₁ M₂).threads ++ [ν]) (envW ν (word σ)) ≤ K →
        envF t₁ t₂ M₁ M₂ (envAlpha t₁ t₂ M₁ M₂ G) H =
          envAlpha t₁ t₂ M₁ M₂ (compEnv G ν σ H) := by
  intro G hG _ σ hσ _ H hH _
  obtain ⟨-, -, htr⟩ := mp_compose_2 hν hP hG hσ hH
  obtain ⟨-, -, -, hpm⟩ := mp_compose_3 hν hP hG hσ hH
  simp only [envF, envAlpha]
  rw [htr t₁ (Mach.mem_prog_threads.mpr (Or.inl rfl)),
    htr t₂ (Mach.mem_prog_threads.mpr (Or.inr rfl)), hpm, M₁.st_append, M₂.st_append]

end Env

/-! ### Section 7: the abstraction `h` for two machines -/

section P2P

variable {S₁ S₂ : Type} (t₁ t₂ : Tid) (M₁ : Mach Q S₁) (M₂ : Mach Q S₂)

/-- `h` of def:p2p-frag for two machines: the two states and `pend_1(G)`, `pend_2(G)`. -/
def p2pAlpha (G : Graph Q) : S₁ × S₂ × List Msg × List Msg :=
  (M₁.st (G.trace t₁), M₂.st (G.trace t₂), G.pend t₁, G.pend t₂)

/-- The seed words of an abstract value. -/
def p2pWords (b : S₁ × S₂ × List Msg × List Msg) : Tid → List Msg :=
  fun t => if t = t₁ then b.2.2.1 else if t = t₂ then b.2.2.2 else []

/-- The abstract value after a fragment: run the machines on the fragment's traces after the
seeds; the pending messages are those of the fragment. -/
def p2pF (b : S₁ × S₂ × List Msg × List Msg) (H : Graph Q) : S₁ × S₂ × List Msg × List Msg :=
  (runSt M₁.next b.1 ((H.trace t₁).drop b.2.2.1.length),
    runSt M₂.next b.2.1 ((H.trace t₂).drop b.2.2.2.length), H.pend t₁, H.pend t₂)

variable {t₁ t₂ M₁ M₂} {h : t₁ ≠ t₂}

/-- `hconf` of `checkP2P_sound` for `p2pAlpha`. -/
theorem p2pAlpha_hconf {r₁ : S₁ → List (Option Val)} {r₂ : S₂ → List (Option Val)}
    (hr₁ : ∀ s, M₁.st (r₁ s) = s) (hr₂ : ∀ s, M₂.st (r₂ s) = s) (M : Model Q) :
    ∀ G, ExecM M (Mach.prog t₁ t₂ h M₁ M₂) G →
      (∀ t ∈ (Mach.prog t₁ t₂ h M₁ M₂).threads, FutEq ((Mach.prog t₁ t₂ h M₁ M₂).step t)
        (repU t₁ t₂ r₁ r₂ (p2pAlpha t₁ t₂ M₁ M₂ G) t) (G.trace t)) ∧
      ∀ t, p2pWords t₁ t₂ (p2pAlpha t₁ t₂ M₁ M₂ G) t = G.pend t := by
  intro G hG
  refine ⟨fun _ ht => repU_fut hr₁ hr₂ _ ht (fun h1 => h1 ▸ rfl) (fun h2 => h2 ▸ rfl),
    fun t => ?_⟩
  by_cases h1 : t = t₁
  · subst h1
    simp [p2pWords, p2pAlpha]
  · by_cases h2 : t = t₂
    · subst h2
      simp [p2pWords, p2pAlpha, h1]
    · simp only [p2pWords, h1, h2, ↓reduceIte]
      exact (pend_nil (M.wf _ hG.2) hG.1 fun ht =>
        (Mach.mem_prog_threads.mp ht).elim h1 h2).symm

/-- `hf` of `checkP2P_sound` (and of `checkP2PAsyn_sound`) for `p2pAlpha`, `p2pF`
(lem:p2p-compose (1), (2)), for every Section 7 setting. -/
theorem p2pF_hf (S : MPSetting Q) (hS : S.ι = []) (hT : S.ord)
    {A : Set (S₁ × S₂ × List Msg × List Msg)} {K : ℕ} :
    ∀ G, ExecM (Model.ofSet S.ms) S.P G → p2pAlpha t₁ t₂ M₁ M₂ G ∈ A →
      ∀ H, Frag (Model.ofSet S.ms) (S.P.p2pRes S.m G.trace G.pend) G.pend H →
        H.len S.P.threads G.pend ≤ K →
        p2pF t₁ t₂ M₁ M₂ (p2pAlpha t₁ t₂ M₁ M₂ G) H = p2pAlpha t₁ t₂ M₁ M₂ (compP2P G H) := by
  intro G hG _ H hH _
  obtain ⟨-, -, htr⟩ := p2p_compose_2 S hS hG hH
  obtain ⟨-, -, -, -, -, hpd⟩ := p2p_compose_1 S hS hT hG hH
  simp only [p2pF, p2pAlpha]
  rw [htr t₁, htr t₂, hpd t₁, hpd t₂, M₁.st_append, M₂.st_append]

end P2P

end Ind

end Must
