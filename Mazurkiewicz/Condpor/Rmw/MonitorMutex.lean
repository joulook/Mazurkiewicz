import Mazurkiewicz.Condpor.Rmw.MonitorCode
import Mazurkiewicz.Condpor.Rmw.LockMutex

/-!
# Monitors: mutual exclusion and hold counts

The analogue of `LockMutex.lean` for monitor programs (`monSys`). A release
of a monitor writes an even value (`freeVal σ = 2 * sigCode σ`) instead of `0`.

* The machine of a thread (`MState`): an invariant of reachable states
  (`MState.Inv`: a wait in progress on `l` holds `l`, saved and restored hold
  counts are positive); the writes of a thread to a monitor location that no
  plain write names (`MState.act_write`: an acquire writes `1` in the phase
  `acquire`, every other write is even and made while holding the monitor).
* Along a trace (`monState`): `monState_holds_pos_iff` (the hold count of `l`
  is positive exactly after an acquire phase and before the next write of the
  thread to `l`), `monState_release` (a release is preceded by an acquire of
  the same thread with no write to `l` between), `monState_wait_restore` (a
  wait releases its monitor, other counts unchanged, and the acquire that ends
  it restores the saved count).
* Graphs: `MonLike` (`LockLike` with "even" for a release),
  `MonLike.alternates`, `monSys_monLike`, `monSys_mutex`.
-/

/-- Closes the goals of a case of the machine of a monitor thread. -/
macro "mfin" : tactic => `(tactic| first
  | omega
  | (simp_all; done)
  | (simp_all; omega)
  | (refine ⟨by omega, fun w hw => ?_⟩; cases hw; simp_all; done)
  | (left; simp_all; done)
  | (right; refine ⟨by omega, fun w hw => ?_⟩; cases hw; simp_all; done)
  | (right; refine ⟨by omega, fun w hw => ?_⟩; simp_all; done)
  | (right; refine ⟨by omega, ?_⟩; simp_all; done)
  | (right; refine ⟨?_, ?_⟩ <;> simp_all <;> omega))

/-- Unfolds the case distinctions of the machine of a monitor thread in the
hypothesis `h` and the goal. -/
macro "msplit" h:ident : tactic => `(tactic| (
  try simp only [Condpor.MState.local, Condpor.MState.spurNext, Condpor.MState.spurAct,
    Condpor.MState.waitWrite, Function.update_apply] at $h:ident ⊢
  repeat' (first | split_ifs at $h:ident ⊢ | split at $h:ident | split |
    simp only [Function.update_apply] at $h:ident ⊢)))

namespace Condpor

/-! ### The machine of a thread -/

namespace MState

/-- The invariant of reachable states: a wait in progress on `l` holds `l`,
and a saved or restored hold count is positive. -/
def Inv (s : MState) : Prop :=
  match s.phase with
  | .acquire _ h => 0 < h
  | .spur l _ => 0 < s.holds l
  | .release l _ _ => 0 < s.holds l
  | .waiting _ _ _ h => 0 < h
  | _ => True

theorem spurNext_ops (s : MState) (l : Loc) (i : ℕ) (v : Option Val) :
    (s.spurNext l i v).ops = s.ops := by
  unfold spurNext; split_ifs <;> rfl

theorem next_ops_subset (s : MState) (v : Option Val) :
    ∀ op ∈ (s.next v).ops, op ∈ s.ops := by
  intro op hop
  unfold MState.next at hop
  cases hph : s.phase with
  | ready =>
    simp only [hph] at hop
    cases hops : s.ops with
    | nil => simp only [hops] at hop; exact hop
    | cons o rest =>
      simp only [hops] at hop
      refine List.mem_cons_of_mem _ ?_
      cases o <;> simp only [MState.local] at hop <;>
        (try split_ifs at hop) <;> (try split at hop) <;> (try split_ifs at hop) <;>
        first | exact List.mem_of_mem_drop hop | exact hop |
          (rw [spurNext_ops] at hop; exact hop)
  | spur l i => simp only [hph, spurNext_ops] at hop; exact hop
  | waiting l i b h =>
    simp only [hph] at hop
    repeat' (first | split at hop | split_ifs at hop)
    all_goals exact hop
  | _ => simp only [hph] at hop; exact hop

/-- One step: if the thread holds `l` afterwards, the step was the acquire
write of `l`, or the thread held `l` before and the step was not a write to
`l`. -/
theorem holds_next {s : MState} {v : Option Val} {l : Loc} (hinv : s.Inv)
    (hpriv : ∀ w, MOp.wr l w ∉ s.ops) (h : 0 < (s.next v).holds l) :
    (∃ h, s.phase = .acquire l h) ∨ (0 < s.holds l ∧ ∀ w, s.act ≠ some (.write l w)) := by
  unfold MState.next at h
  unfold MState.act
  unfold MState.Inv at hinv
  cases hph : s.phase with
  | ready =>
    simp only [hph] at h hinv ⊢
    cases hops : s.ops with
    | nil => simp only [hops] at h ⊢; exact Or.inr ⟨h, by simp⟩
    | cons o rest =>
      simp only [hops] at h ⊢
      cases o <;> msplit h <;> mfin
  | _ => simp only [hph] at h hinv ⊢; msplit h <;> mfin

attribute [local simp] freeVal_mod_two freeVal_ne_one

/-- The writes of a thread to a location `l` that no plain write names: the
acquire write (value `1`, phase `acquire`), or a release (an even value,
written while the thread holds `l`). -/
theorem act_write {s : MState} {l : Loc} {w : ℕ} (hinv : s.Inv)
    (hpriv : ∀ w, MOp.wr l w ∉ s.ops) (h : s.act = some (.write l w)) :
    ((∃ h, s.phase = .acquire l h) ∧ w = 1) ∨
      (0 < s.holds l ∧ w % 2 = 0 ∧ ∀ h, s.phase ≠ .acquire l h) := by
  unfold MState.act at h
  unfold MState.Inv at hinv
  cases hph : s.phase with
  | ready =>
    simp only [hph] at h hinv ⊢
    cases hops : s.ops with
    | nil => simp only [hops] at h; cases h
    | cons o rest =>
      simp only [hops] at h
      cases o <;> msplit h <;> (try cases h) <;>
        first | mfin | exact absurd (by rw [hops]; exact List.mem_cons_self) (hpriv _)
  | _ => simp only [hph] at h hinv ⊢; msplit h <;> (try cases h) <;> mfin

/-- The hold count stays positive along a step that does not write `l`. -/
theorem holds_pos_next {s : MState} {v : Option Val} {l : Loc} (hinv : s.Inv)
    (h0 : 0 < s.holds l) (hw : ∀ w, s.act ≠ some (.write l w)) :
    0 < (s.next v).holds l := by
  unfold MState.next
  unfold MState.act at hw
  unfold MState.Inv at hinv
  cases hph : s.phase with
  | ready =>
    simp only [hph] at hw hinv ⊢
    cases hops : s.ops with
    | nil => exact h0
    | cons o rest =>
      simp only [hops] at hw ⊢
      cases o <;> msplit hw <;> mfin
  | _ => simp only [hph] at hw hinv ⊢; msplit hw <;> mfin

/-- The invariant is preserved by a step. -/
theorem inv_next {s : MState} (v : Option Val) (hinv : s.Inv) : (s.next v).Inv := by
  unfold MState.next
  unfold MState.Inv at hinv
  cases hph : s.phase with
  | ready =>
    simp only [hph] at hinv
    cases hops : s.ops with
    | nil => simp only [MState.Inv, hph]
    | cons o rest =>
      cases o <;> msplit hinv <;> (simp_all [MState.Inv] <;> omega)
  | _ => simp only [hph] at hinv; msplit hinv <;> simp_all [MState.Inv]

/-- The acquire phase is entered only from an exclusive read of the monitor
that returned an even (free) value. -/
theorem acquire_of_next {s : MState} {v : Option Val} {l : Loc} {k : ℕ}
    (h : (s.next v).phase = .acquire l k) :
    s.act = some (.read l) ∧ s.isEx = true ∧ ∃ x : ℕ, v = some x ∧ x % 2 = 0 := by
  unfold MState.next at h
  unfold MState.act MState.isEx
  cases hph : s.phase with
  | ready =>
    simp only [hph] at h ⊢
    cases hops : s.ops with
    | nil => simp only [hops] at h; simp [hph] at h
    | cons o rest =>
      simp only [hops] at h ⊢
      cases o <;> msplit h <;> simp_all
  | _ => simp only [hph] at h ⊢; msplit h <;> simp_all

/-- A write to `l` other than the acquire write sets the hold count to `0`. -/
theorem release_next {s : MState} {v : Option Val} {l : Loc} {w : ℕ}
    (hpriv : ∀ w, MOp.wr l w ∉ s.ops) (h : s.act = some (.write l w))
    (hne : ∀ k, s.phase ≠ .acquire l k) : (s.next v).holds l = 0 := by
  unfold MState.next
  unfold MState.act at h
  cases hph : s.phase with
  | ready =>
    simp only [hph] at h ⊢
    cases hops : s.ops with
    | nil => simp only [hops] at h; cases h
    | cons o rest =>
      simp only [hops] at h ⊢
      cases o <;> msplit h <;> (try cases h) <;>
        first | (simp_all; done) | omega |
          exact absurd (by rw [hops]; exact List.mem_cons_self) (hpriv _)
  | _ => simp only [hph] at h hne ⊢; msplit h <;> (try cases h) <;> simp_all

/-- The waiting phase is entered only by the release write of a wait: the
saved count is the count before it, which is positive; the count of `l`
becomes `0`, the other counts are unchanged. -/
theorem waiting_of_next {s : MState} {v : Option Val} {l : Loc} {i : ℕ} {b : Bool} {k : ℕ}
    (hinv : s.Inv) (h : (s.next v).phase = .waiting l i b k) :
    k = s.holds l ∧ 0 < k ∧ (s.next v).holds = Function.update s.holds l 0 ∧
      ∃ w, s.act = some (.write l w) := by
  unfold MState.Inv at hinv
  have e := h
  clear h
  unfold MState.next at e ⊢
  unfold MState.act
  cases hph : s.phase with
  | ready =>
    simp only [hph] at e hinv ⊢
    cases hops : s.ops with
    | nil => simp only [hops] at e; simp [hph] at e
    | cons o rest =>
      simp only [hops] at e ⊢
      cases o <;> msplit e <;>
        (try (simp only [MPhase.waiting.injEq] at e; obtain ⟨rfl, rfl, rfl, rfl⟩ := e)) <;>
        first | (simp_all; done) | (simp_all; omega)
  | _ =>
    simp only [hph] at e hinv ⊢
    msplit e <;>
      (try (simp only [MPhase.waiting.injEq] at e; obtain ⟨rfl, rfl, rfl, rfl⟩ := e)) <;>
      simp_all

/-- A waiter's exclusive read leads to the acquire phase with the saved count,
or blocks; the counts are unchanged. -/
theorem waiting_next {s : MState} (v : Option Val) {l : Loc} {i : ℕ} {b : Bool} {k : ℕ}
    (h : s.phase = .waiting l i b k) :
    ((s.next v).phase = .acquire l k ∨ (s.next v).phase = .blocking) ∧
      (s.next v).holds = s.holds := by
  unfold MState.next
  simp only [h]
  repeat' (first | split | split_ifs)
  all_goals simp

theorem acquire_next {s : MState} (v : Option Val) {l : Loc} {k : ℕ}
    (h : s.phase = .acquire l k) :
    (s.next v).holds = Function.update s.holds l k ∧ (s.next v).phase = .ready := by
  unfold MState.next
  simp [h]

theorem acquire_act {s : MState} {l : Loc} {k : ℕ} (h : s.phase = .acquire l k) :
    s.act = some (.write l 1) ∧ s.isEx = true := by
  unfold MState.act MState.isEx
  simp [h]

end MState


/-! ### The machine along a trace -/

section Trace

variable (t : Tid) (ops : List MOp) (K K' : ℕ)

theorem monState_snoc (u : List (Option Val)) (v : Option Val) :
    monState t ops K K' (u ++ [v]) = (monState t ops K K' u).next v := by
  simp [monState, List.foldl_append]

theorem monState_ops_subset (u : List (Option Val)) :
    ∀ op ∈ (monState t ops K K' u).ops, op ∈ ops := by
  induction u using List.reverseRecOn with
  | nil => exact fun op h => h
  | append_singleton u v ih =>
    intro op hop
    rw [monState_snoc] at hop
    exact ih op (MState.next_ops_subset _ v op hop)

/-- Every state along a trace satisfies the invariant. -/
theorem monState_inv (u : List (Option Val)) : (monState t ops K K' u).Inv := by
  induction u using List.reverseRecOn with
  | nil => simp [monState, MState.Inv]
  | append_singleton u v ih =>
    rw [monState_snoc]
    exact MState.inv_next v ih

variable {t ops K K'}

/-- The hold count of `l` is positive exactly after an acquire write (the
action of the phase `acquire l _` at position `j`) and before the next write of
the thread to `l`. -/
theorem monState_holds_pos_iff {l : Loc} (hpriv : ∀ w, MOp.wr l w ∉ ops)
    (u : List (Option Val)) :
    0 < (monState t ops K K' u).holds l ↔
      ∃ j, j < u.length ∧ (∃ h, (monState t ops K K' (u.take j)).phase = .acquire l h) ∧
        ∀ k, j < k → k < u.length →
          ∀ w, (monState t ops K K' (u.take k)).act ≠ some (.write l w) := by
  induction u using List.reverseRecOn with
  | nil =>
    simp only [List.length_nil, Nat.not_lt_zero, false_and, exists_false, iff_false]
    simp [monState]
  | append_singleton u v ih =>
    have hp : ∀ w, MOp.wr l w ∉ (monState t ops K K' u).ops :=
      fun w hm => hpriv w (monState_ops_subset t ops K K' u _ hm)
    have hinv := monState_inv t ops K K' u
    rw [monState_snoc]
    constructor
    · intro h
      rcases MState.holds_next hinv hp h with hacq | ⟨hpos, hact⟩
      · refine ⟨u.length, by simp, by simpa using hacq, fun k h1 h2 => ?_⟩
        simp only [List.length_append, List.length_singleton] at h2
        omega
      · obtain ⟨j, hj, hjp, hbet⟩ := ih.mp hpos
        refine ⟨j, by simp; omega, ?_, fun k h1 h2 => ?_⟩
        · rw [List.take_append_of_le_length (Nat.le_of_lt hj)]
          exact hjp
        · simp only [List.length_append, List.length_singleton] at h2
          by_cases hk : k < u.length
          · rw [List.take_append_of_le_length (Nat.le_of_lt hk)]
            exact hbet k h1 hk
          · have hku : k = u.length := by omega
            rw [hku, List.take_left']
            · exact hact
            · rfl
    · rintro ⟨j, hj, ⟨h, hjp⟩, hbet⟩
      simp only [List.length_append, List.length_singleton] at hj hbet
      by_cases hju : j = u.length
      · subst hju
        rw [List.take_left' rfl] at hjp
        have hh : 0 < h := by
          have := hinv
          unfold MState.Inv at this
          rwa [hjp] at this
        rw [(MState.acquire_next v hjp).1, Function.update_self]
        exact hh
      · have hpos : 0 < (monState t ops K K' u).holds l := by
          refine ih.mpr ⟨j, by omega, ?_, fun k h1 h2 => ?_⟩
          · rw [List.take_append_of_le_length (by omega)] at hjp
            exact ⟨h, hjp⟩
          · have := hbet k h1 (by omega)
            rwa [List.take_append_of_le_length (by omega)] at this
        refine MState.holds_pos_next hinv hpos ?_
        have := hbet u.length (by omega) (by omega)
        rwa [List.take_left' rfl] at this

/-- For a monitor that no plain write names, the writes of `1` by the thread
are exactly the actions of the acquire phase. -/
theorem monState_write_one_iff {l : Loc} (hpriv : ∀ w, MOp.wr l w ∉ ops)
    (u : List (Option Val)) :
    (monState t ops K K' u).act = some (.write l 1) ↔
      ∃ k, (monState t ops K K' u).phase = .acquire l k := by
  constructor
  · intro h
    have hp : ∀ w, MOp.wr l w ∉ (monState t ops K K' u).ops :=
      fun w hm => hpriv w (monState_ops_subset t ops K K' u _ hm)
    rcases MState.act_write (monState_inv t ops K K' u) hp h with ⟨hk, -⟩ | ⟨-, h1, -⟩
    · exact hk
    · exact absurd h1 (by decide)
  · rintro ⟨k, hk⟩
    exact (MState.acquire_act hk).1

/-- A write of the thread to `l` that is not an acquire is a release: its
value is even, and the thread acquired `l` earlier and has not written `l`
since. -/
theorem monState_release {l : Loc} (hpriv : ∀ w, MOp.wr l w ∉ ops) {u : List (Option Val)}
    {w : ℕ} (h : (monState t ops K K' u).act = some (.write l w))
    (hne : ∀ k, (monState t ops K K' u).phase ≠ .acquire l k) :
    w % 2 = 0 ∧ 0 < (monState t ops K K' u).holds l ∧
      ∃ j, j < u.length ∧ (∃ h, (monState t ops K K' (u.take j)).phase = .acquire l h) ∧
        ∀ k, j < k → k < u.length →
          ∀ w, (monState t ops K K' (u.take k)).act ≠ some (.write l w) := by
  have hp : ∀ w, MOp.wr l w ∉ (monState t ops K K' u).ops :=
    fun w hm => hpriv w (monState_ops_subset t ops K K' u _ hm)
  rcases MState.act_write (monState_inv t ops K K' u) hp h with ⟨⟨k, hk⟩, -⟩ | ⟨hpos, hev, -⟩
  · exact absurd hk (hne k)
  · exact ⟨hev, hpos, (monState_holds_pos_iff hpriv u).mp hpos⟩

/-- After a release write, the hold count of `l` is `0`. -/
theorem monState_release_holds {l : Loc} (hpriv : ∀ w, MOp.wr l w ∉ ops)
    {u : List (Option Val)} {w : ℕ} (h : (monState t ops K K' u).act = some (.write l w))
    (hne : ∀ k, (monState t ops K K' u).phase ≠ .acquire l k) (v : Option Val) :
    (monState t ops K K' (u ++ [v])).holds l = 0 := by
  rw [monState_snoc]
  exact MState.release_next (fun w hm => hpriv w (monState_ops_subset t ops K K' u _ hm)) h hne

/-- Hold restoration: a wait releases its monitor `l` by a write of `l` (count
of `l` becomes `0`, the other counts unchanged) and saves the count it had; if
the exclusive read of the waiter is followed by the acquire phase, the count of
that phase is the saved count, and after the acquire write the counts are
those before the wait. -/
theorem monState_wait_restore {l : Loc} {i : ℕ} {b : Bool} {k k' : ℕ}
    (u : List (Option Val)) (v1 v2 v3 : Option Val)
    (h1 : (monState t ops K K' (u ++ [v1])).phase = .waiting l i b k)
    (h2 : (monState t ops K K' (u ++ [v1] ++ [v2])).phase = .acquire l k') :
    k = (monState t ops K K' u).holds l ∧ 0 < k ∧ k' = k ∧
      (∃ w, (monState t ops K K' u).act = some (.write l w)) ∧
      (monState t ops K K' (u ++ [v1])).holds =
        Function.update (monState t ops K K' u).holds l 0 ∧
      (monState t ops K K' (u ++ [v1] ++ [v2] ++ [v3])).holds =
        (monState t ops K K' u).holds := by
  rw [monState_snoc] at h1
  obtain ⟨hk, hpos, hhold, hw⟩ := MState.waiting_of_next (monState_inv t ops K K' u) h1
  rw [monState_snoc, monState_snoc] at h2
  obtain ⟨hph, hh2⟩ := MState.waiting_next v2 h1
  have hkk : k' = k := by
    rcases hph with hph | hph
    · rw [hph] at h2
      cases h2
      rfl
    · rw [hph] at h2
      cases h2
  subst hkk
  refine ⟨hk, hpos, rfl, hw, by rw [monState_snoc]; exact hhold, ?_⟩
  rw [monState_snoc, monState_snoc, monState_snoc, (MState.acquire_next v3 h2).1, hh2, hhold,
    Function.update_idem, hk, Function.update_eq_self]

end Trace


/-! ### Monitor locations: the graph theorem -/

/-- The writes of `l` behave as the acquires (value `1`) and releases (an even
value, the code of a monitor state) of a monitor. `LockLike` with "even"
instead of "`0`" for a release. -/
structure MonLike (G : Graph) (l : Loc) : Prop where
  h1 : ∀ w ∈ G.co l, G.valAt l (.th w) % 2 = 0 ∨ G.valAt l (.th w) = 1
  h2 : ∀ w ∈ G.co l, G.valAt l (.th w) = 1 → ∃ s, G.ImmCo l s w ∧ G.valAt l s % 2 = 0
  h3 : ∀ w ∈ G.co l, G.valAt l (.th w) % 2 = 0 →
    ∃ a ∈ G.co l, G.valAt l (.th a) = 1 ∧ a.tid = w.tid ∧ a.idx < w.idx ∧
      ∀ w' ∈ G.co l, G.valAt l (.th w') % 2 = 0 → w'.tid = w.tid →
        ¬ (a.idx < w'.idx ∧ w'.idx < w.idx)

/-- The coherence list of a monitor alternates between an acquire (value `1`)
and a release (even value) by the same thread, starting with an acquire. -/
theorem MonLike.alternates {G : Graph} {l : Loc} (hG : G.Wf) (hc : Maz.Acyclic G.scStep)
    (h : MonLike G l) :
    ∀ i (hi : i < (G.co l).length),
      (i % 2 = 0 → G.valAt l (.th (G.co l)[i]) = 1) ∧
      (i % 2 = 1 → G.valAt l (.th (G.co l)[i]) % 2 = 0 ∧
        ∃ hi' : i - 1 < (G.co l).length, (G.co l)[i].tid = (G.co l)[i - 1].tid) := by
  have hnd := hG.co_nodup l
  have h10 : ¬ (1 : ℕ) % 2 = 0 := by decide
  -- the contradiction for a release whose acquire is not its neighbour
  have key : ∀ (i j : ℕ) (hi : i < (G.co l).length) (hj : j + 1 < (G.co l).length),
      j + 1 < i →
      G.valAt l (.th (G.co l)[j + 1]) % 2 = 0 → (G.co l)[j + 1].tid = (G.co l)[j].tid →
      (G.co l)[j].tid = (G.co l)[i].tid → (G.co l)[j].idx < (G.co l)[i].idx →
      (∀ w' ∈ G.co l, G.valAt l (.th w') % 2 = 0 → w'.tid = (G.co l)[i].tid →
        ¬ ((G.co l)[j].idx < w'.idx ∧ w'.idx < (G.co l)[i].idx)) → False := by
    intro i j hi hj hji hv ht1 ht2 hidx hno
    have hmi := List.getElem_mem hi
    have hmj := List.getElem_mem (show j < (G.co l).length by omega)
    have hmj1 := List.getElem_mem hj
    have hEi := ((hG.co_mem l _).mp hmi).1
    have hEj := ((hG.co_mem l _).mp hmj).1
    have hEj1 := ((hG.co_mem l _).mp hmj1).1
    rcases Nat.lt_trichotomy (G.co l)[j + 1].idx (G.co l)[j].idx with h1 | h1 | h1
    · exact Graph.not_before_of_po hG hc hmj1 hmj ht1 h1
        ((List.before_getElem_iff hnd _ _).mpr (Nat.lt_succ_self j))
    · have := hG.idx_inj _ hEj1 _ hEj ht1 h1
      have := hnd.getElem_inj_iff.mp this
      omega
    · rcases Nat.lt_trichotomy (G.co l)[j + 1].idx (G.co l)[i].idx with h2 | h2 | h2
      · exact hno _ hmj1 hv (ht1.trans ht2) ⟨h1, h2⟩
      · have := hG.idx_inj _ hEj1 _ hEi (ht1.trans ht2) h2
        have := hnd.getElem_inj_iff.mp this
        omega
      · exact Graph.not_before_of_po hG hc hmi hmj1 (ht1.trans ht2).symm h2
          ((List.before_getElem_iff hnd _ _).mpr hji)
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hmi := List.getElem_mem hi
    -- the acquire of a release at position `i`, as a position
    have acq : G.valAt l (.th (G.co l)[i]) % 2 = 0 →
        ∃ j, ∃ hj : j < (G.co l).length, j < i ∧ G.valAt l (.th (G.co l)[j]) = 1 ∧
          (G.co l)[j].tid = (G.co l)[i].tid ∧ (G.co l)[j].idx < (G.co l)[i].idx ∧
          ∀ w' ∈ G.co l, G.valAt l (.th w') % 2 = 0 → w'.tid = (G.co l)[i].tid →
            ¬ ((G.co l)[j].idx < w'.idx ∧ w'.idx < (G.co l)[i].idx) := by
      intro hv
      obtain ⟨a, ha, hva, hta, hia, hno⟩ := h.h3 _ hmi hv
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      refine ⟨j, hj, ?_, hva, hta, hia, hno⟩
      by_contra hji
      have hne : j ≠ i := by
        intro hji'
        subst hji'
        omega
      exact Graph.not_before_of_po hG hc ha hmi hta hia
        ((List.before_getElem_iff hnd _ _).mpr (by omega))
    -- a release at position `i` whose acquire is at position `j < i`: `j = i - 1`
    have rel : G.valAt l (.th (G.co l)[i]) % 2 = 0 →
        0 < i ∧ ∃ hi' : i - 1 < (G.co l).length, (G.co l)[i].tid = (G.co l)[i - 1].tid ∧
          (i - 1) % 2 = 0 := by
      intro hv
      obtain ⟨j, hj, hji, hva, hta, hia, hno⟩ := acq hv
      have hjeven : j % 2 = 0 := by
        by_contra hodd
        have := ((ih j hji hj).2 (by omega)).1
        rw [hva] at this
        exact h10 this
      by_cases hjn : j + 1 = i
      · subst hjn
        exact ⟨by omega, by simpa using hj, by simpa using hta.symm, by simpa using hjeven⟩
      · exfalso
        have hj1 : j + 1 < (G.co l).length := by omega
        obtain ⟨hv1, hi', ht1⟩ := (ih (j + 1) (by omega) hj1).2 (by omega)
        exact key i j hi hj1 (by omega) hv1 (by simpa using ht1) hta hia hno
    constructor
    · intro heven
      rcases h.h1 _ hmi with hv | hv
      · obtain ⟨hpos, hi', -, hpar⟩ := rel hv
        omega
      · exact hv
    · intro hodd
      rcases h.h1 _ hmi with hv | hv
      · obtain ⟨hpos, hi', ht, -⟩ := rel hv
        exact ⟨hv, hi', ht⟩
      · exfalso
        obtain ⟨s, hs, hs0⟩ := h.h2 _ hmi hv
        rcases Graph.ImmCo.pred hG hi hs with ⟨h0, -⟩ | ⟨hi', hpos, rfl⟩
        · omega
        · have := (ih (i - 1) (by omega) hi').1 (by omega)
          rw [this] at hs0
          exact h10 hs0

/-! ### Monitor programs satisfy `MonLike` -/

section Sys

variable {threads : List Tid} {hnd : threads.Nodup} {code : Tid → List MOp} {K K' n : ℕ}

/-- A step of the program is the action of the machine. -/
theorem monSys_step {t : Tid} {u : List (Option Val)} {a : Act}
    (h : (monSys threads hnd code K K' n).toProgram.step t u = some a) :
    (monState t (code t) K K' u).act = some a := by
  unfold monSys mkXProg mkProg at h
  simp only at h
  split at h
  · cases h
  · exact h

variable {G : Graph}

/-- The action of an event of an execution is the action of the machine of
its thread after the trace before it. -/
theorem monSys_act (hE : (monSys threads hnd code K K' n).toProgram.Exec G) {e : TEv}
    (he : e ∈ G.events) :
    (monState e.tid (code e.tid) K K' (G.traceBefore e.tid e.idx)).act = some e.act :=
  monSys_step (hE.2 e he)

/-- The state after an event. -/
theorem monSys_state_succ (hG : G.Wf) {e : TEv} (he : e ∈ G.events) :
    monState e.tid (code e.tid) K K' (G.traceBefore e.tid (e.idx + 1)) =
      (monState e.tid (code e.tid) K K' (G.traceBefore e.tid e.idx)).next (G.ret e) := by
  rw [Graph.traceBefore_succ, monState_snoc, hG.evAt_eq_some he]
  rfl

/-- In an atomic execution of a monitor program, a location that no plain
write names behaves as a monitor. -/
theorem monSys_monLike (hG : G.Wf) (hE : (monSys threads hnd code K K' n).toProgram.Exec G)
    (hat : (monSys threads hnd code K K' n).Atomic G) {l : Loc}
    (hpriv : ∀ t v, MOp.wr l v ∉ code t) : MonLike G l := by
  have hp : ∀ (t : Tid) (u : List (Option Val)) (v' : Val),
      MOp.wr l v' ∉ (monState t (code t) K K' u).ops :=
    fun t u v' hm => hpriv t v' (monState_ops_subset _ _ _ _ u _ hm)
  have hinv : ∀ (t : Tid) (u : List (Option Val)), (monState t (code t) K K' u).Inv :=
    fun t u => monState_inv _ _ _ _ u
  have hval : ∀ {w : TEv} {v : Val}, w.act = .write l v → G.valAt l (.th w) = v := by
    intro w v hv
    simp [Graph.valAt, hv]
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨hwE, v, hv⟩ := (hG.co_mem l w).mp hw
    have ha := monSys_act hE hwE
    rw [hv] at ha
    rw [hval hv]
    rcases MState.act_write (hinv _ _) (hp _ _) ha with ⟨-, rfl⟩ | ⟨-, hev, -⟩
    · exact Or.inr rfl
    · exact Or.inl hev
  · intro w hw hw1
    obtain ⟨hwE, v, hv⟩ := (hG.co_mem l w).mp hw
    rw [hval hv] at hw1
    subst hw1
    have ha := monSys_act hE hwE
    rw [hv] at ha
    obtain ⟨k, hph⟩ : ∃ k,
        (monState w.tid (code w.tid) K K' (G.traceBefore w.tid w.idx)).phase = .acquire l k := by
      rcases MState.act_write (hinv _ _) (hp _ _) ha with ⟨h1, -⟩ | ⟨-, h1, -⟩
      · exact h1
      · exact absurd h1 (by decide)
    -- the event before `w` in its thread
    obtain ⟨i, hwi⟩ : ∃ i, w.idx = i + 1 := by
      cases hwi : w.idx with
      | zero =>
        rw [hwi] at hph
        simp [Graph.traceBefore, monState] at hph
      | succ i => exact ⟨i, rfl⟩
    obtain ⟨r, hr, hrt, hri⟩ := hG.idx_contig w hwE i (by omega)
    have hsucc := monSys_state_succ (code := code) (K := K) (K' := K') hG hr
    rw [hrt, hri, ← hwi] at hsucc
    rw [hsucc] at hph
    obtain ⟨hract0, hexr, x, hret, hxev⟩ := MState.acquire_of_next hph
    -- the read
    have hract : r.act = .read l := by
      have := monSys_act hE hr
      rw [hrt, hri, hract0] at this
      exact (Option.some.inj this).symm
    have hexw : (monState w.tid (code w.tid) K K' (G.traceBefore w.tid (i + 1))).isEx = true := by
      rw [← hwi, hsucc]
      exact (MState.acquire_act hph).2
    have hstepr := hE.2 r hr
    rw [hrt, hri, hract] at hstepr
    have hstepw := hE.2 w hwE
    rw [hv] at hstepw
    have htr : G.traceBefore w.tid w.idx = G.traceBefore w.tid i ++ [some x] := by
      rw [hwi, Graph.traceBefore_succ]
      have := hG.evAt_eq_some hr
      rw [hrt, hri] at this
      rw [this]
      exact congrArg (fun x => G.traceBefore w.tid i ++ [x]) hret
    have hrmw : (monSys threads hnd code K K' n).RMW G r w := by
      refine ⟨hr, hwE, hrt.symm, by omega, by simp [TEv.IsRead, hract, Act.IsRead],
        by simp [TEv.IsWrite, hv, Act.IsWrite], ?_, ?_⟩
      · change exFlag (monSys threads hnd code K K' n).toProgram.step (msFlag code K K') r.tid
          (G.traceBefore r.tid r.idx) = true
        rw [hrt, hri]
        unfold exFlag
        rw [hstepr]
        exact hexr
      · change exFlag (monSys threads hnd code K K' n).toProgram.step (msFlag code K K') w.tid
          (G.traceBefore w.tid w.idx) = true
        unfold exFlag
        rw [hstepw]
        have hfl : msFlag code K K' w.tid (G.traceBefore w.tid w.idx) = true := by
          unfold msFlag
          rw [hwi]
          exact hexw
        rw [hfl, htr]
        simp only [List.getLast?_concat, List.dropLast_concat, Bool.true_and]
        rw [hstepr]
        simpa [msFlag] using hexr
    obtain ⟨s, hs, -⟩ := hG.rf_read r hr l hract
    have hloc : w.loc = l := by simp [TEv.loc, hv, Act.loc]
    refine ⟨s, hloc ▸ hat r w hrmw s hs, ?_⟩
    have : G.ret r = some (G.valAt l s) := by
      unfold Graph.ret
      rw [hract, hs]
      rfl
    rw [this] at hret
    rw [Option.some.inj hret]
    exact hxev
  · intro w hw hw0
    obtain ⟨hwE, v, hv⟩ := (hG.co_mem l w).mp hw
    rw [hval hv] at hw0
    have ha := monSys_act hE hwE
    rw [hv] at ha
    have hne : ∀ k, (monState w.tid (code w.tid) K K'
        (G.traceBefore w.tid w.idx)).phase ≠ .acquire l k := by
      intro k hk
      have := (MState.acquire_act hk).1
      rw [this] at ha
      have h1 : v = 1 := by cases ha; rfl
      rw [h1] at hw0
      exact absurd hw0 (by decide)
    obtain ⟨-, -, j, hj, ⟨k, hjp⟩, hbet⟩ := monState_release (hpriv w.tid) ha hne
    rw [Graph.traceBefore_length] at hj hbet
    rw [Graph.traceBefore_take G w.tid (Nat.le_of_lt hj)] at hjp
    obtain ⟨a, haE, hat', hai⟩ := hG.idx_contig w hwE j hj
    have haact : a.act = .write l 1 := by
      have := monSys_act hE haE
      rw [hat', hai, (MState.acquire_act hjp).1] at this
      exact (Option.some.inj this).symm
    refine ⟨a, (hG.co_mem l a).mpr ⟨haE, 1, haact⟩, hval haact, hat', by omega, ?_⟩
    intro w' hw' _ hw't ⟨h1, h2⟩
    obtain ⟨hw'E, v', hv'⟩ := (hG.co_mem l w').mp hw'
    have := monSys_act hE hw'E
    rw [hw't, hv'] at this
    refine hbet w'.idx (by omega) h2 v' ?_
    rw [Graph.traceBefore_take G w.tid (Nat.le_of_lt h2)]
    exact this

/-- Mutual exclusion for monitor programs: in every well-formed,
SC-consistent, atomic execution, the writes of a monitor location that no
plain write names alternate in coherence order between an acquire (value `1`)
by a thread and a release (an even value `2 * sigCode σ`) by the same thread,
starting with an acquire. A release is the write of `unlock` with hold count
`1` or the release write of a `wait`.

Not stated (as for `lockSys_mutex`): that critical sections do not interleave
in the SC order; anything about a thread that ends, blocks or is cut while it
holds the monitor; fairness; that the monitor is released eventually. -/
theorem monSys_mutex (hG : G.Wf) (hE : (monSys threads hnd code K K' n).toProgram.Exec G)
    (hc : (Model.atomic (monSys threads hnd code K K' n) SC).cons G) {l : Loc}
    (hpriv : ∀ t v, MOp.wr l v ∉ code t) :
    ∀ i (hi : i < (G.co l).length),
      (i % 2 = 0 → G.valAt l (.th (G.co l)[i]) = 1) ∧
      (i % 2 = 1 → G.valAt l (.th (G.co l)[i]) % 2 = 0 ∧
        ∃ hi' : i - 1 < (G.co l).length, (G.co l)[i].tid = (G.co l)[i - 1].tid) :=
  (monSys_monLike hG hE hc.2 hpriv).alternates hG hc.1

end Sys

end Condpor
