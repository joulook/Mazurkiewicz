import Mazurkiewicz.Induction.BarCheck
import Mazurkiewicz.Induction.CutBar

/-!
# The worked example of Section 5: a loop with two phases

`induction-popl`, `cuts.tex`, ex:toggle.

The program `P^tg`: thread `0` repeats "write `1`, write `0`" to the location
`0`, thread `1` reads it forever. The property `Bad^tg`: at the head of the
loop the location has the value `1`.

`toggle_safe`: `P^tg` is safe for `Bad^tg` under SC, for executions of every
length. The proof is `checkBar_sound` applied to a run of `CheckBar` with the
cut bars of the example (`toggle_check`: accepted after 8 tests, the number
of ex:toggle; by evaluation in the kernel).

How the text is read here.

* Threads `1`, `2` of the paper are `0`, `1`; the location `x` is `0`.
* `α = h` is given as the pair (parity of the number of events of the
  writer, value of the location): the writer has two local states, the
  reader one, and only the location `0` is written.
* The cut family `C_1 = {s^0}`, `C_2 =` all states is `Ctg`; the bar test
  `barB` used by `CheckBar` is the cut bar of `Ctg` (`mem_cutBar_tg`), and the
  segment bounds `(2,1)`, `(1,1)` of the example are proved
  (`segBound_even`, `segBound_odd`).
-/

namespace Trust.Toggle

open Program

/-- `P^tg` (ex:toggle). -/
def tg : Program where
  threads := [0, 1]
  threads_nodup := by decide
  step := fun t u =>
    match t with
    | 0 => if u.length % 2 = 0 then some (.write 0 1) else some (.write 0 0)
    | 1 => some (.read 0)
    | _ => none
  mem := fun _ => 0
  step_none := by
    intro t ht
    match t with
    | 0 | 1 => simp at ht
    | _ + 2 => rfl

theorem tg_step0 (u : List (Option Val)) :
    tg.step 0 u = if u.length % 2 = 0 then some (.write 0 1) else some (.write 0 0) := rfl

/-- The two local states of the writer. -/
theorem futEq_tg0 (u u' : List (Option Val)) :
    FutEq (tg.step 0) u u' ↔ u.length % 2 = u'.length % 2 := by
  constructor
  · intro h
    have h0 := h []
    rw [List.append_nil, List.append_nil, tg_step0, tg_step0] at h0
    by_cases h1 : u.length % 2 = 0 <;> by_cases h2 : u'.length % 2 = 0 <;>
      simp [h1, h2] at h0 <;> omega
  · intro h x
    have : (u ++ x).length % 2 = (u' ++ x).length % 2 := by
      rw [List.length_append, List.length_append]
      omega
    rw [tg_step0, tg_step0, this]

/-! ### Executions of programs that act on the location `0` only -/

/-- All actions are on the location `0`. -/
def Loc0 (Q : Program) : Prop := ∀ t u a, Q.step t u = some a → a.loc = 0

theorem loc0_tg : Loc0 tg := by
  intro t u a h
  match t with
  | 0 =>
    rw [tg_step0] at h
    by_cases h1 : u.length % 2 = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)] at h
      cases h
      rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)] at h
      cases h
      rfl
  | 1 =>
    cases h
    rfl
  | _ + 2 => cases h

theorem memOf_of_ne {Q : Program} (hQ : Loc0 Q) {G : Graph} (hG : G.Wf) (hE : Q.Exec G)
    {x : Loc} (hx : x ≠ 0) : G.memOf x = G.mem x := by
  have hco : G.co x = [] := by
    refine List.eq_nil_iff_forall_not_mem.mpr (fun e he => ?_)
    obtain ⟨hev, v, hv⟩ := (hG.co_mem x e).mp he
    have := hQ _ _ _ (hE.2 e hev)
    rw [hv] at this
    exact hx this
  unfold Graph.memOf Graph.maxWrite
  rw [hco]
  rfl

/-! ### The abstraction -/

abbrev A := ℕ × Val

/-- `α = h`: the local state of the writer (the parity of its number of
events) and the value of the location. -/
def αA (G : Graph) : A := (G.cnt 0 % 2, G.memOf 0)

def uA (b : A) (t : Tid) : List (Option Val) :=
  if t = 0 then (if b.1 = 0 then [] else [none]) else []

def μA (b : A) : Loc → Val := fun x => if x = 0 then b.2 else 0

def fA (b : A) (H : Graph) : A := ((b.1 + H.cnt 0) % 2, H.memOf 0)

def abadA (b : A) : Bool := b == (0, 1)

def BA : List A := [(0, 0), (1, 1)]

/-- `Bad^tg`: at the head of the loop the location has the value `1`. -/
def BadTg : Set Graph := {G | αA G = (0, 1)}

def absA : Abstraction tg A where
  α := αA
  u := uA
  μ := μA
  hconf := by
    intro G hG
    refine ⟨fun t ht => ?_, ?_⟩
    · have ht' : t = 0 ∨ t = 1 := by simpa [tg] using ht
      rcases ht' with rfl | rfl
      · rw [futEq_tg0, Graph.trace_length]
        change (if G.cnt 0 % 2 = 0 then ([] : List (Option Val)) else [none]).length % 2 = _
        by_cases h : G.cnt 0 % 2 = 0
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h), h]
          rfl
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
          change 1 % 2 = _
          omega
      · intro x
        rfl
    · funext x
      by_cases hx : x = 0
      · subst hx
        rfl
      · rw [memOf_of_ne loc0_tg hG.1 hG.2.1 hx, hG.2.1.1]
        change (if x = 0 then _ else 0) = _
        rw [ite_eq_right_of_eq_false _ _ (eq_false hx)]
        rfl

theorem absA_determines : absA.Determines BadTg {a | abadA a = true} := by
  intro G _
  change αA G = (0, 1) ↔ (αA G == (0, 1)) = true
  simp

theorem fA_eq {G H : Graph} (hG : ExecSC tg G)
    (hH : GReach (tg.residual G.trace G.memOf) SC H) : fA (absA.α G) H = absA.α (G.comp H) := by
  have hHE := greach_iff.mp hH
  obtain ⟨-, -, hcnt, -, -, hmem⟩ := Graph.comp_facts hG.1 hHE.1 hHE.2.2 hHE.2.1.1
  change ((G.cnt 0 % 2 + H.cnt 0) % 2, H.memOf 0) = ((G.comp H).cnt 0 % 2, (G.comp H).memOf 0)
  rw [hcnt, hmem, Nat.mod_add_mod]

/-! ### The cut bars -/

/-- The cut family: the head of the loop of the writer, the only state of
the reader. -/
def Ctg : ∀ t, Set (St (tg.step t))
  | 0 => {s | s = St.mk (tg.step 0) []}
  | 1 => Set.univ
  | _ + 2 => ∅

/-- The cut bar, as a test: the reader has an event, or the writer has passed
the head of its loop. -/
def barB (b : A) (H : Graph) : Bool :=
  decide (1 ≤ H.cnt 1) || (if b.1 = 0 then decide (2 ≤ H.cnt 0) else decide (1 ≤ H.cnt 0))

theorem uA_length (b : A) (hb : b.1 = 0 ∨ b.1 = 1) : (uA b 0).length = b.1 := by
  unfold uA
  rcases hb with h | h <;> simp [h]

/-- The test `barB` is the cut bar of `Ctg`. -/
theorem mem_cutBar_tg (b : A) (hb : b.1 = 0 ∨ b.1 = 1) (H : Graph) :
    H ∈ cutBar Ctg (uA b) ↔ barB b H = true := by
  have hlen := uA_length b hb
  constructor
  · rintro ⟨t, x, hx, hpre, hC⟩
    have h1 : 1 ≤ x.length := List.length_pos_iff.mpr hx
    have h2 : x.length ≤ H.cnt t := by
      have := hpre.length_le
      rwa [Graph.trace_length] at this
    match t with
    | 0 =>
      have hC' : St.mk (tg.step 0) (uA b 0 ++ x) = St.mk (tg.step 0) [] := hC
      have hpar := (futEq_tg0 _ _).mp (St.mk_eq_mk.mp hC')
      rw [List.length_append, hlen, List.length_nil] at hpar
      unfold barB
      rcases hb with h | h
      · have : 2 ≤ H.cnt 0 := by omega
        simp [h, this]
      · have : 1 ≤ H.cnt 0 := by omega
        simp [h, this]
    | 1 =>
      unfold barB
      have : 1 ≤ H.cnt 1 := by omega
      simp [this]
    | _ + 2 => exact absurd hC (by simp [Ctg])
  · intro h
    unfold barB at h
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · have h' : 1 ≤ H.cnt 1 := of_decide_eq_true h
      refine ⟨1, H.trace 1, ?_, List.prefix_refl _, Set.mem_univ _⟩
      intro hnil
      have := Graph.trace_length H 1
      rw [hnil] at this
      simp at this
      omega
    · rcases hb with hb | hb
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hb)] at h
        have h' : 2 ≤ H.cnt 0 := of_decide_eq_true h
        have hl : ((H.trace 0).take 2).length = 2 := by
          rw [List.length_take, Graph.trace_length]
          omega
        refine ⟨0, (H.trace 0).take 2, (fun hnil => by rw [hnil] at hl; cases hl),
          List.take_prefix _ _, ?_⟩
        change St.mk (tg.step 0) _ = St.mk (tg.step 0) []
        rw [St.mk_eq_mk, futEq_tg0, List.length_append, hlen, hl, hb]
        rfl
      · have hne : ¬ b.1 = 0 := by omega
        rw [ite_eq_right_of_eq_false _ _ (eq_false hne)] at h
        have h' : 1 ≤ H.cnt 0 := of_decide_eq_true h
        have hl : ((H.trace 0).take 1).length = 1 := by
          rw [List.length_take, Graph.trace_length]
          omega
        refine ⟨0, (H.trace 0).take 1, (fun hnil => by rw [hnil] at hl; cases hl),
          List.take_prefix _ _, ?_⟩
        change St.mk (tg.step 0) _ = St.mk (tg.step 0) []
        rw [St.mk_eq_mk, futEq_tg0, List.length_append, hlen, hl, hb]
        rfl

/-- The segment bound `(2,1)` of ex:toggle for the values with the writer at
the head of its loop. -/
theorem segBound_even (b : A) (hb : b.1 = 0) :
    SegBound Ctg (uA b) (μA b) (fun t => if t = 0 then 2 else 1) := by
  intro t ht
  have ht' : t = 0 ∨ t = 1 := by simpa [tg] using ht
  rcases ht' with rfl | rfl
  · refine ⟨by decide, fun x hx _ =>
      ⟨x, (fun h => by rw [h] at hx; cases hx), List.prefix_refl _, ?_⟩⟩
    change St.mk (tg.step 0) _ = St.mk (tg.step 0) []
    rw [St.mk_eq_mk, futEq_tg0, List.length_append, uA_length b (Or.inl hb), hx, hb]
    rfl
  · exact ⟨by decide, fun x hx _ =>
      ⟨x, (fun h => by rw [h] at hx; cases hx), List.prefix_refl _, Set.mem_univ _⟩⟩

/-- The segment bound `(1,1)` for the values with the writer inside its loop. -/
theorem segBound_odd (b : A) (hb : b.1 = 1) : SegBound Ctg (uA b) (μA b) (fun _ => 1) := by
  intro t ht
  have ht' : t = 0 ∨ t = 1 := by simpa [tg] using ht
  rcases ht' with rfl | rfl
  · refine ⟨by decide, fun x hx _ =>
      ⟨x, (fun h => by rw [h] at hx; cases hx), List.prefix_refl _, ?_⟩⟩
    change St.mk (tg.step 0) _ = St.mk (tg.step 0) []
    rw [St.mk_eq_mk, futEq_tg0, List.length_append, uA_length b (Or.inr hb), hx, hb]
    rfl
  · exact ⟨by decide, fun x hx _ =>
      ⟨x, (fun h => by rw [h] at hx; cases hx), List.prefix_refl _, Set.mem_univ _⟩⟩

/-! ### Running `CheckBar` -/

/-- `CheckBar` accepts `B` with the cut bars, after 8 tests (ex:toggle). -/
theorem toggle_check : CheckBar tg BA abadA uA μA fA barB 2 = (true, 8) := by
  decide +kernel

/-- `P^tg` is safe for `Bad^tg` under SC, for executions of every length. -/
theorem toggle_safe : Safe tg SC BadTg := by
  refine absA.checkBar_sound absA_determines (B := BA) (N := 2) (barB := barB) ?_ fA
    (fun G hG _ H hH _ => fA_eq hG hH) ?_
  · change (((Graph.init tg.mem).cnt 0 % 2, (Graph.init tg.mem).memOf 0) : A) ∈ BA
    decide
  · change (CheckBar tg BA abadA uA μA fA barB 2).1 = true
    rw [toggle_check]

/-- With fuel `1` the check fails for `(0,0)`: the fragment `W` is outside
the bar and has a successor. -/
theorem toggle_reject_fuel : (CheckBar tg BA abadA uA μA fA barB 1).1 = false := by
  decide +kernel

/-- Without the value `(1,1)` the check fails. -/
theorem toggle_reject : (CheckBar tg [(0, 0)] abadA uA μA fA barB 2).1 = false := by
  decide +kernel

end Trust.Toggle
