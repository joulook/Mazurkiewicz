import Mazurkiewicz.Induction.ErrEnc
import Mazurkiewicz.Induction.MonoExample

/-!
# A worked example with an assertion

An instance of the remark after cor:errenc (`induction-popl`, `dpor.tex`), in
the style of ex:mono. It is not an example of the paper.

The simple program `rwa`: thread `0` writes `1` to the location `0` forever;
thread `1` reads the location `0` forever, and fails (error action) when a
read that returned `1` is followed by a read that returned `0`. It is
unbounded.

`assert_safe`: `rwa` is safe for the assertion property `Bad_err` under SC,
for executions of every length. The proof is `check_sound_err`: `Check` with
the verified explorer of TruSt runs on the error encoding of `rwa`
(`assert_check`, by evaluation in the kernel), and safety is transferred to
`rwa`.

The abstraction, on the graphs of the encoding: the value of the location
`0`, and the local state of the reader, one of four classes: `0` no `1` read
yet, `1` a `1` read and no `0` after it, `2` the next action is the error,
`3` stopped after the error (its marker is written). The property `BadMark`
is determined by the class `3`.
-/

namespace Trust.Assert

open Program
open Trust.Mono (seenL zeroL badL seenL_append zeroL_append badL_append)

/-- The trace contains `⊥`: an error event has occurred. -/
def stopL (l : List (Option Val)) : Bool := l.any (fun v => v == none)

theorem stopL_append (l₁ l₂ : List (Option Val)) :
    stopL (l₁ ++ l₂) = (stopL l₁ || stopL l₂) := List.any_append

/-- The reader/writer program with an assertion in the reader. -/
def rwa : SProgram where
  threads := [0, 1]
  threads_nodup := by decide
  step := fun t u =>
    match t with
    | 0 => some (.write 0 1)
    | 1 => if stopL u then none else if badL u then some .err else some (.read 0)
    | _ => none
  mem := fun _ => 0
  step_none := by
    intro t ht
    match t with
    | 0 | 1 => simp at ht
    | _ + 2 => rfl
  stop := by
    intro t u h
    match t with
    | 0 => cases h
    | 1 =>
      have hs : stopL (u ++ [none]) = true := by simp [stopL]
      change (if stopL (u ++ [none]) then none else _) = none
      rw [hs]
      rfl
    | _ + 2 => rfl

theorem rwa_step1 (u : List (Option Val)) :
    rwa.step 1 u = if stopL u then none else if badL u then some .err else some (.read 0) := rfl

/-- The markers: thread `t` has the location `t + 1`; the value written is `1`. -/
def mk : Markers where
  lam := fun t => t + 1
  own := fun x => if x = 0 then none else some (x - 1)
  own_iff := by
    intro (x : ℕ) (t : ℕ)
    change (if x = 0 then none else some (x - 1 : ℕ)) = some t ↔ t + 1 = x
    by_cases hx : x = 0
    · subst hx
      simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hx)]
      constructor
      · intro h
        have h' : x - 1 = t := Option.some.inj h
        omega
      · intro h
        have h' : x - 1 = t := by omega
        exact congrArg some h'
  ve := 1

theorem rwa_noMark : rwa.NoMark mk := by
  intro t u
  match t with
  | 0 =>
    refine ⟨fun x h => ?_, fun x v h => ?_⟩
    · cases h
    · cases h
      rfl
  | 1 =>
    rw [rwa_step1]
    by_cases h1 : stopL u = true
    · simp [h1]
    · by_cases h2 : badL u = true
      · simp [h1, h2]
      · refine ⟨fun x h => ?_, fun x v h => ?_⟩
        · simp only [h1, h2] at h
          cases h
          rfl
        · simp [h1, h2] at h
  | _ + 2 => exact ⟨fun x h => (by cases h), fun x v h => (by cases h)⟩

/-- The error encoding of `rwa`: a plain program. -/
abbrev P : Program := rwa.enc mk

/-! ### Programs that step like the encoding -/

/-- The actions of the encoding and of its residual programs. -/
def Shape (Q : Program) : Prop :=
  ∀ t u a, Q.step t u = some a →
    (t = 0 ∧ a = .write 0 1) ∨ (t = 1 ∧ (a = .read 0 ∨ a = .write 2 1))

theorem shape_P : Shape P := by
  intro t u a h
  match t with
  | 0 => exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
  | 1 =>
    change (rwa.step 1 u).map (SAct.enc mk 1) = some a at h
    rw [rwa_step1] at h
    by_cases h1 : stopL u = true
    · simp [h1] at h
    · by_cases h2 : badL u = true
      · simp only [h1, h2, ite_true, Bool.false_eq_true, ite_false, Option.map_some] at h
        exact Or.inr ⟨rfl, Or.inr (Option.some.inj h).symm⟩
      · simp only [h1, h2, Bool.false_eq_true, ite_false, Option.map_some] at h
        exact Or.inr ⟨rfl, Or.inl (Option.some.inj h).symm⟩
  | _ + 2 => cases h

theorem shape_residual (u : Tid → List (Option Val)) (μ : Loc → Val) :
    Shape (P.residual u μ) := by
  intro t x a h
  change (if t ∈ P.threads then P.step t (u t ++ x) else none) = some a at h
  by_cases ht : t ∈ P.threads
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ht)] at h
    exact shape_P _ _ _ h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false ht)] at h
    cases h

variable {Q : Program} {G : Graph}

theorem act_of_exec (hQ : Shape Q) (hE : Q.Exec G) {e : TEv} (he : e ∈ G.events) :
    (e.tid = 0 ∧ e.act = .write 0 1) ∨ (e.tid = 1 ∧ (e.act = .read 0 ∨ e.act = .write 2 1)) :=
  hQ _ _ _ (hE.2 e he)

/-- The values in the trace of a thread are the values returned by its events. -/
theorem mem_trace (hG : G.Wf) {t : Tid} {v : Option Val} :
    v ∈ G.trace t ↔ ∃ e ∈ G.events, e.tid = t ∧ G.ret e = v := by
  unfold Graph.trace Graph.traceBefore
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨q, hq, ht, hidx⟩ := (hG.exists_idx_iff t i).mpr (List.mem_range.mp hi)
    have hev := hG.evAt_eq_some hq
    rw [ht, hidx] at hev
    exact ⟨q, hq, ht, by rw [hev]; rfl⟩
  · rintro ⟨e, he, rfl, rfl⟩
    exact ⟨e.idx, List.mem_range.mpr (hG.idx_lt_cnt he), by rw [hG.evAt_eq_some he]; rfl⟩

theorem ret_write {e : TEv} {x : Loc} {v : Val} (h : e.act = .write x v) : G.ret e = none := by
  unfold Graph.ret
  rw [h]

theorem ret_read (hG : G.Wf) {e : TEv} (he : e ∈ G.events) {x : Loc} (h : e.act = .read x) :
    G.ret e ≠ none := by
  obtain ⟨w, hw, -⟩ := hG.rf_read e he x h
  unfold Graph.ret
  rw [h]
  simp [hw]

/-- The reader has stopped iff its marker is written. -/
theorem stop_iff_mark (hQ : Shape Q) (hG : G.Wf) (hE : Q.Exec G) :
    stopL (G.trace 1) = true ↔ G ∈ BadMark mk := by
  unfold stopL
  rw [List.any_eq_true]
  constructor
  · rintro ⟨v, hv, hvn⟩
    have hv' : v = none := by simpa using hvn
    subst hv'
    obtain ⟨e, he, ht, hr⟩ := (mem_trace hG).mp hv
    refine ⟨e, he, ?_⟩
    rcases act_of_exec hQ hE he with ⟨h0, -⟩ | ⟨-, h | h⟩
    · exact absurd (h0.symm.trans ht) (by decide)
    · exact absurd hr (ret_read hG he h)
    · unfold Markers.isMark
      rw [TEv.loc, h]
      rfl
  · rintro ⟨e, he, hm⟩
    rcases act_of_exec hQ hE he with ⟨-, h⟩ | ⟨ht, h | h⟩
    · unfold Markers.isMark at hm
      rw [TEv.loc, h] at hm
      cases hm
    · unfold Markers.isMark at hm
      rw [TEv.loc, h] at hm
      cases hm
    · exact ⟨none, (mem_trace hG).mpr ⟨e, he, ht, ret_write h⟩, rfl⟩

/-- The memory outside the location `0`: the marker of the reader has the
value `1` once the reader has stopped. -/
theorem memOf_of_ne (hQ : Shape Q) (hG : G.Wf) (hE : Q.Exec G) {x : Loc} (hx : x ≠ 0) :
    G.memOf x = if x = 2 then (if stopL (G.trace 1) then 1 else G.mem x) else G.mem x := by
  unfold Graph.memOf Graph.maxWrite
  cases hl : (G.co x).getLast? with
  | none =>
    have hco : G.co x = [] := List.getLast?_eq_none_iff.mp hl
    have hns : x = 2 → stopL (G.trace 1) = false := by
      rintro rfl
      by_contra hs
      obtain ⟨e, he, hm⟩ := (stop_iff_mark hQ hG hE).mp (by simpa using hs)
      have hin : e ∈ G.co 2 := by
        refine (hG.co_mem 2 e).mpr ⟨he, 1, ?_⟩
        rcases act_of_exec hQ hE he with ⟨-, h⟩ | ⟨-, h | h⟩
        · unfold Markers.isMark at hm
          rw [TEv.loc, h] at hm
          cases hm
        · unfold Markers.isMark at hm
          rw [TEv.loc, h] at hm
          cases hm
        · exact h
      rw [hco] at hin
      cases hin
    by_cases h2 : x = 2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), hns h2]
      rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]
      rfl
  | some e =>
    have hin : e ∈ G.co x := List.mem_of_getLast? hl
    obtain ⟨he, v, hv⟩ := (hG.co_mem x e).mp hin
    have hs : stopL (G.trace 1) = true ∧ x = 2 ∧ v = 1 := by
      rcases act_of_exec hQ hE he with ⟨-, h⟩ | ⟨ht, h | h⟩
      · rw [h] at hv
        exact absurd (Act.write.inj hv).1.symm hx
      · rw [h] at hv
        cases hv
      · rw [h] at hv
        obtain ⟨h1, h2⟩ := Act.write.inj hv
        refine ⟨(stop_iff_mark hQ hG hE).mpr ⟨e, he, ?_⟩, h1.symm, h2.symm⟩
        unfold Markers.isMark
        rw [TEv.loc, h]
        rfl
    obtain ⟨h1, h2, h3⟩ := hs
    rw [ite_eq_left_of_eq_true _ _ (eq_true h2), h1]
    change (match e.act with | .write _ v => v | .read _ => 0) = 1
    rw [hv, h3]

/-- The values returned by the events of thread `1`, computed: a read of the
location `0` returns its value, the marker write returns `⊥`. -/
def traceC (H : Graph) : List (Option Val) :=
  (List.range (H.cnt 1)).map
    (fun i => if (⟨1, i, .read 0⟩ : TEv) ∈ H.events then H.ret ⟨1, i, .read 0⟩ else none)

theorem traceC_eq (hQ : Shape Q) (hG : G.Wf) (hE : Q.Exec G) : traceC G = G.trace 1 := by
  unfold traceC Graph.trace Graph.traceBefore
  refine List.map_congr_left (fun i hi => ?_)
  obtain ⟨q, hq, ht, hidx⟩ := (hG.exists_idx_iff 1 i).mpr (List.mem_range.mp hi)
  have hev := hG.evAt_eq_some hq
  rw [ht, hidx] at hev
  rw [hev]
  obtain ⟨qt, qi, qa⟩ := q
  simp only at ht hidx
  subst ht hidx
  rcases act_of_exec hQ hE hq with ⟨h, -⟩ | ⟨-, h | h⟩
  · cases h
  · simp only at h
    subst h
    rw [ite_eq_left_of_eq_true _ _ (eq_true hq)]
    rfl
  · simp only at h
    subst h
    have hnot : (⟨1, qi, .read 0⟩ : TEv) ∉ G.events := by
      intro h'
      have := hG.idx_inj _ h' _ hq rfl rfl
      cases this
    rw [ite_eq_right_of_eq_false _ _ (eq_false hnot)]
    rfl

/-! ### The abstraction -/

/-- The local state of the reader after the trace `u`. -/
def rstate (u : List (Option Val)) : ℕ :=
  if stopL u then 3 else if badL u then 2 else if seenL u then 1 else 0

/-- A representative trace of each local state of the reader. -/
def rep : ℕ → List (Option Val)
  | 0 => []
  | 1 => [some 1]
  | 2 => [some 1, some 0]
  | _ => [some 1, some 0, none]

/-- The local state after `u ++ w`, from the local state after `u`. -/
def comb (s : ℕ) (w : List (Option Val)) : ℕ :=
  if s == 3 || stopL w then 3
  else if s == 2 || badL w || (decide (1 ≤ s) && zeroL w) then 2
  else if decide (1 ≤ s) || seenL w then 1 else 0

theorem comb_eq (u w : List (Option Val)) : comb (rstate u) w = rstate (u ++ w) := by
  unfold comb rstate
  rw [stopL_append, badL_append, seenL_append]
  generalize stopL u = a
  generalize badL u = b
  generalize seenL u = c
  generalize stopL w = d
  generalize badL w = e
  generalize seenL w = f
  generalize zeroL w = g
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> rfl

theorem rstate_eq_three (u : List (Option Val)) : rstate u = 3 ↔ stopL u = true := by
  unfold rstate
  generalize stopL u = a
  generalize badL u = b
  generalize seenL u = c
  cases a <;> cases b <;> cases c <;> simp

/-- The reader continues from the representative of its state as from its
trace. -/
theorem step_rep (u x : List (Option Val)) :
    P.step 1 (rep (rstate u) ++ x) = P.step 1 (u ++ x) := by
  change (rwa.step 1 _).map _ = (rwa.step 1 _).map _
  rw [rwa_step1, rwa_step1, stopL_append, stopL_append, badL_append, badL_append]
  unfold rstate
  generalize hd : stopL x = d
  generalize he : badL x = e
  generalize hg : zeroL x = g
  cases ha : stopL u <;> cases hb : badL u <;> cases hc : seenL u <;>
    simp [rep, stopL, badL, seenL, zeroL]

abbrev A := Val × ℕ

/-- `α(G)`: the value of the location `0`, the local state of the reader. -/
noncomputable def αA (G : Graph) : A := (G.memOf 0, rstate (G.trace 1))

def uA (b : A) (t : Tid) : List (Option Val) := if t = 1 then rep b.2 else []

def μA (b : A) : Loc → Val :=
  fun x => if x = 0 then b.1 else if x = 2 then (if b.2 = 3 then 1 else 0) else 0

def fA (b : A) (H : Graph) : A := (H.memOf 0, comb b.2 (traceC H))

def abadA (b : A) : Bool := b.2 == 3

def BA : List A := [(0, 0), (1, 0), (1, 1)]

noncomputable def absA : Abstraction P A where
  α := αA
  u := uA
  μ := μA
  hconf := by
    intro G hG
    refine ⟨fun t ht x => ?_, ?_⟩
    · have ht' : t = 0 ∨ t = 1 := by simpa [P, SProgram.enc, rwa] using ht
      rcases ht' with rfl | rfl
      · rfl
      · exact step_rep (G.trace 1) x
    · funext x
      by_cases hx : x = 0
      · subst hx
        rfl
      · rw [memOf_of_ne shape_P hG.1 hG.2.1 hx, hG.2.1.1]
        change (if x = 0 then _ else if x = 2 then (if rstate (G.trace 1) = 3 then 1 else 0) else 0)
          = _
        rw [ite_eq_right_of_eq_false _ _ (eq_false hx)]
        by_cases h2 : x = 2
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true h2)]
          by_cases hs : stopL (G.trace 1) = true
          · rw [ite_eq_left_of_eq_true _ _ (eq_true ((rstate_eq_three _).mpr hs)), hs]
            rfl
          · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hs ((rstate_eq_three _).mp h)))]
            simp [hs]
            rfl
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h2),
            ite_eq_right_of_eq_false _ _ (eq_false h2)]
          rfl

/-- `BadMark` is determined by the local state "stopped". -/
theorem absA_determines : absA.Determines (BadMark mk) {a | abadA a = true} := by
  intro G hG
  rw [← stop_iff_mark shape_P hG.1 hG.2.1, ← rstate_eq_three]
  change _ ↔ (rstate (G.trace 1) == 3) = true
  simp

theorem fA_eq {G H : Graph} (hG : ExecSC P G)
    (hH : GReach (P.residual G.trace G.memOf) SC H) : fA (absA.α G) H = absA.α (G.comp H) := by
  have hHE := greach_iff.mp hH
  obtain ⟨-, -, -, htr, -, hmem⟩ := Graph.comp_facts hG.1 hHE.1 hHE.2.2 hHE.2.1.1
  have htc := traceC_eq (shape_residual G.trace G.memOf) hHE.1 hHE.2.1
  change (H.memOf 0, comb (rstate (G.trace 1)) (traceC H)) =
    ((G.comp H).memOf 0, rstate ((G.comp H).trace 1))
  rw [htc, htr, hmem, comb_eq]

/-! ### Running `Check` -/

/-- `Check` with the explorer accepts on the encoding, for `K = 2`. -/
theorem assert_check : Check exploreC P BA abadA uA μA fA 2 = (true, 12) := by
  decide +kernel

/-- `rwa` is safe for the assertion property under SC: in no execution, of
any length, does the reader reach its error action. -/
theorem assert_safe : rwa.SafeE BadErr := by
  refine check_sound_err mk rwa_noMark absA absA_determines (B := BA) (K := 2) ?_
    (by decide) (by decide) fA (fun G hG _ H hH _ => fA_eq hG hH) ?_
  · change (((Graph.init P.mem).memOf 0, rstate ((Graph.init P.mem).trace 1)) : A) ∈ BA
    rw [Graph.trace_init]
    decide
  · change (Check exploreC P BA abadA uA μA fA 2).1 = true
    rw [assert_check]

/-- Without the value "a `1` was read" the check fails. -/
theorem assert_reject :
    (Check exploreC P [(0, 0), (1, 0)] abadA uA μA fA 2).1 = false := by
  decide +kernel

end Trust.Assert
