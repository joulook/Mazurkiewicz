import Mazurkiewicz.Must.ExploreM

/-!
# Early exit (milestone M9)

Paper: Algorithm 1 with early exit at an error (Section 4); Theorem 4.1. Plan: decision Q12
("procedure with early exit: exits iff `P` is erroneous; correspondence proved"), row M9
(`completeM_exit`), fate row Thm 4.1/A.3 (b) (`fruitless_with_exit`: with early exit, (b) fails).

* `HasErr G`: `G` contains an error event. `Erroneous M P`: some member of `⟦P⟧` contains an
  error event.
* `dfsX`, `exploreX`: M2's depth-first search (same fuel and depth contract as `dfs`) that stops
  at the first visited configuration whose graph contains an error event and returns it
  (`err`); later calls do nothing.
* `reach_err_iff`: some reachable configuration contains an error event iff `P` is erroneous
  (`⇒` by `ReachM.reaches_full`: non-revisit steps keep the events; `⇐` by `completeM`).
* `exploreX_sound`: for every fuel, a returned configuration is reachable, contains an error
  event, and `P` is erroneous.
* `completeM_exit`: with a fuel of at least the number of reachable configurations, the search
  does not exhaust, and it exits with an error iff `P` is erroneous.
-/

namespace Must

open Graph Config Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q]
variable {M : Model Q} {P : Program Q} {tie : Tie Q}

/-- `G` contains an error event. -/
def HasErr (G : Graph Q) : Prop := ∃ e ∈ G.events, e.lab = .error

instance (G : Graph Q) : Decidable (HasErr G) := by
  unfold HasErr
  infer_instance

/-- `P` is erroneous: some member of `⟦P⟧` contains an error event. -/
def Erroneous (M : Model Q) (P : Program Q) : Prop := ∃ G, M.Sem P G ∧ HasErr G

omit [DecidableEq Q] [Membership Val Q] in
theorem HasErr.mono {G G' : Graph Q} (h : HasErr G) (hs : G.events ⊆ G'.events) : HasErr G' := by
  obtain ⟨e, he, hl⟩ := h
  exact ⟨e, hs he, hl⟩

/-- Some reachable configuration contains an error event iff `P` is erroneous (bounded
program, every model, Q9 tie-break). -/
theorem reach_err_iff (hT : TieQ9 M tie) {k : ℕ} (hb : P.Bounded k) :
    (∃ c, ReachM M tie P c ∧ HasErr c.G) ↔ Erroneous M P := by
  constructor
  · rintro ⟨c, hcR, he⟩
    obtain ⟨c', h1, -, -, h4⟩ := hcR.reaches_full hb
    refine ⟨c'.G, h4, he.mono ?_⟩
    clear h4
    induction h1 with
    | refl => exact subset_rfl
    | tail _ hs ih =>
      obtain ⟨e, src, out, -, rfl⟩ := hs
      exact ih.trans (Finset.subset_insert _ _)
  · rintro ⟨G, hG, he⟩
    obtain ⟨c, hcR, rfl, -⟩ := completeM hT hb hG
    exact ⟨c, hcR, he⟩

variable [∀ (v : Val) (q : Q), Decidable (v ∈ q)] {consB : Graph Q → Bool}

/-- The result of a search with early exit. -/
structure XResult (Q : Type) where
  /-- remaining fuel -/
  fuel : ℕ
  /-- the first visited configuration with an error event -/
  err : Option (Config Q) := none
  /-- fuel or depth exhausted -/
  exhausted : Bool := false

/-- `Visit` with early exit, depth-first; the first argument bounds the depth, `fuel` the number
of visits. A call after an error has been found does nothing. -/
def dfsX (cons : Graph Q → Bool) (V : Variant Q) (P : Program Q) :
    ℕ → Config Q → XResult Q → XResult Q
  | 0, _, r => if r.err.isSome then r else { r with exhausted := true }
  | n + 1, c, r =>
    if r.err.isSome then r else
    if r.fuel = 0 then { r with exhausted := true } else
    let r : XResult Q := { r with fuel := r.fuel - 1 }
    if decide (HasErr c.G) then { r with err := some c } else
    match stepM cons V P c with
    | none => r
    | some l => l.foldl (fun r c' => dfsX cons V P n c' r) r

/-- The explorer with early exit from the empty configuration with `fuel` visits. -/
def exploreX (cons : Graph Q → Bool) (V : Variant Q) (P : Program Q) (fuel : ℕ) : XResult Q :=
  dfsX cons V P fuel .init { fuel := fuel }

/-- The fold over the successors in `dfsX`. -/
abbrev dfsXFold (consB : Graph Q → Bool) (V : Variant Q) (P : Program Q) (n : ℕ)
    (l : List (Config Q)) (r : XResult Q) : XResult Q :=
  l.foldl (fun r c' => dfsX consB V P n c' r) r

theorem dfsX_succ (V : Variant Q) (P : Program Q) (n : ℕ) (c : Config Q) (r : XResult Q) :
    dfsX consB V P (n + 1) c r =
      if r.err.isSome then r else
      if r.fuel = 0 then { r with exhausted := true } else
      if HasErr c.G then { r with fuel := r.fuel - 1, err := some c } else
      match stepM consB V P c with
      | none => { r with fuel := r.fuel - 1 }
      | some l => dfsXFold consB V P n l { r with fuel := r.fuel - 1 } := by
  simp only [dfsX, dfsXFold, decide_eq_true_eq]

omit [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
theorem dfsX_found [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] (V : Variant Q)
    (P : Program Q) (n : ℕ) (c : Config Q) (r : XResult Q) (h : r.err.isSome) :
    dfsX consB V P n c r = r := by
  cases n <;> simp [dfsX, h]

theorem dfsXFold_found (V : Variant Q) (P : Program Q) (n : ℕ) :
    ∀ (l : List (Config Q)) (r : XResult Q), r.err.isSome → dfsXFold consB V P n l r = r := by
  intro l
  induction l with
  | nil => exact fun _ _ => rfl
  | cons a l ih =>
    intro r h
    simp only [dfsXFold, List.foldl_cons] at ih ⊢
    rw [dfsX_found V P n a r h]
    exact ih r h

theorem dfsXFold_cons (V : Variant Q) (P : Program Q) (n : ℕ) (a : Config Q)
    (l : List (Config Q)) (r : XResult Q) :
    dfsXFold consB V P n (a :: l) r = dfsXFold consB V P n l (dfsX consB V P n a r) := rfl

/-- Soundness invariant: a found configuration is reachable and contains an error event. -/
def SoundX (M : Model Q) (tie : Tie Q) (P : Program Q) (r : XResult Q) : Prop :=
  ∀ x, r.err = some x → ReachM M tie P x ∧ HasErr x.G

variable (hc : ∀ H : Graph Q, H.Supp → (consB H = true ↔ M.cons H)) (T : Sel Q)
include hc

/-- Soundness of `dfsX` for every fuel. -/
theorem dfsX_sound :
    ∀ (n : ℕ) (c : Config Q) (r : XResult Q), ReachM M (T.pick consB) P c →
      SoundX M (T.pick consB) P r →
      SoundX M (T.pick consB) P (dfsX consB (Variant.repaired consB T) P n c r)
  | 0, c, r, _, h => by
    unfold dfsX
    split_ifs
    · exact h
    · exact h
  | n + 1, c, r, hcR, h => by
    have hf : ∀ (l : List (Config Q)) (r : XResult Q),
        (∀ a ∈ l, ReachM M (T.pick consB) P a) → SoundX M (T.pick consB) P r →
        SoundX M (T.pick consB) P (dfsXFold consB (Variant.repaired consB T) P n l r) := by
      intro l
      induction l with
      | nil => exact fun r _ h => h
      | cons a l ihl =>
        intro r hl h
        exact ihl _ (fun b hb' => hl b (.tail _ hb')) (dfsX_sound n a r (hl a (.head _)) h)
    rw [dfsX_succ]
    split_ifs with h1 h2 h3
    · exact h
    · exact h
    · rintro x hx
      cases hx
      exact ⟨hcR, h3⟩
    rcases hs : stepM consB (Variant.repaired consB T) P c with _ | l
    · exact h
    obtain ⟨-, hmem⟩ := children_spec hc T hcR hs
    exact hf l _ (fun b hb' => hcR.tail ((hmem b).mp hb')) h

/-- **Soundness of the early exit for every fuel**: a returned configuration is reachable and
contains an error event, and `P` is erroneous. -/
theorem exploreX_sound {k : ℕ} (hb : P.Bounded k) {fuel : ℕ} {x : Config Q}
    (h : (exploreX consB (Variant.repaired consB T) P fuel).err = some x) :
    ReachM M (T.pick consB) P x ∧ HasErr x.G ∧ Erroneous M P := by
  have h' := dfsX_sound (P := P) hc T fuel .init { fuel := fuel } .refl
    (fun x hx => by cases hx) x h
  exact ⟨h'.1, h'.2, (reach_err_iff (tieQ9_pick hc T) hb).mp ⟨x, h'⟩⟩

omit hc in
/-- The fold with enough fuel and depth: no exhaustion, and if no error is found, the fuel
decreases by the number of descendants and no descendant contains an error event. -/
theorem dfsXFold_fuel (U : Finset (Config Q)) {n : ℕ}
    (ih : ∀ (c : Config Q) (r : XResult Q), ReachM M (T.pick consB) P c → r.err = none →
      r.exhausted = false → (descF U (StepM M (T.pick consB) P) c).card ≤ n →
      (descF U (StepM M (T.pick consB) P) c).card ≤ r.fuel →
      (dfsX consB (Variant.repaired consB T) P n c r).exhausted = false ∧
      ((dfsX consB (Variant.repaired consB T) P n c r).err = none →
        (dfsX consB (Variant.repaired consB T) P n c r).fuel +
          (descF U (StepM M (T.pick consB) P) c).card = r.fuel ∧
        ∀ x, ReflTransGen (StepM M (T.pick consB) P) c x → ¬ HasErr x.G))
    {c : Config Q} (hcR : ReachM M (T.pick consB) P c) :
    ∀ (l : List (Config Q)) (r : XResult Q), (∀ a ∈ l, StepM M (T.pick consB) P c a) →
      r.err = none → r.exhausted = false →
      (∀ a ∈ l, (descF U (StepM M (T.pick consB) P) a).card ≤ n) →
      (l.map fun a => (descF U (StepM M (T.pick consB) P) a).card).sum ≤ r.fuel →
      (dfsXFold consB (Variant.repaired consB T) P n l r).exhausted = false ∧
      ((dfsXFold consB (Variant.repaired consB T) P n l r).err = none →
        (dfsXFold consB (Variant.repaired consB T) P n l r).fuel +
          (l.map fun a => (descF U (StepM M (T.pick consB) P) a).card).sum = r.fuel ∧
        ∀ a ∈ l, ∀ x, ReflTransGen (StepM M (T.pick consB) P) a x → ¬ HasErr x.G) := by
  intro l
  induction l with
  | nil => exact fun r _ _ hr _ _ => ⟨hr, fun _ => ⟨by simp, by simp⟩⟩
  | cons a l ihl =>
    intro r hl he hr hn hf
    simp only [List.map_cons, List.sum_cons] at hf ⊢
    have haR : ReachM M (T.pick consB) P a := hcR.tail (hl a (.head _))
    obtain ⟨h1, h2⟩ := ih a r haR he hr (hn a (.head _)) (by omega)
    rw [dfsXFold_cons]
    cases hea : (dfsX consB (Variant.repaired consB T) P n a r).err with
    | some x =>
      have hfound := dfsXFold_found (consB := consB) (Variant.repaired consB T) P n l _
        (by rw [hea]; rfl)
      rw [hfound]
      exact ⟨h1, fun h => by rw [hea] at h; cases h⟩
    | none =>
      obtain ⟨h21, h22⟩ := h2 hea
      obtain ⟨k1, k2⟩ := ihl _ (fun b hb' => hl b (.tail _ hb')) hea h1
        (fun b hb' => hn b (.tail _ hb')) (by omega)
      refine ⟨k1, fun h => ?_⟩
      obtain ⟨k21, k22⟩ := k2 h
      refine ⟨by omega, fun b hb' => ?_⟩
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact h22
      · exact k22 b hb'

/-- **Fuel for the early exit**: with depth and fuel at least the number of descendants, a call
does not exhaust; if it finds no error, it consumed exactly that fuel and no descendant
contains an error event. -/
theorem dfsX_fuel {k : ℕ} (hb : P.Bounded k) (U : Finset (Config Q))
    (hU : ∀ x, ReachM M (T.pick consB) P x → x ∈ U) :
    ∀ (n : ℕ) (c : Config Q) (r : XResult Q), ReachM M (T.pick consB) P c → r.err = none →
      r.exhausted = false → (descF U (StepM M (T.pick consB) P) c).card ≤ n →
      (descF U (StepM M (T.pick consB) P) c).card ≤ r.fuel →
      (dfsX consB (Variant.repaired consB T) P n c r).exhausted = false ∧
      ((dfsX consB (Variant.repaired consB T) P n c r).err = none →
        (dfsX consB (Variant.repaired consB T) P n c r).fuel +
          (descF U (StepM M (T.pick consB) P) c).card = r.fuel ∧
        ∀ x, ReflTransGen (StepM M (T.pick consB) P) c x → ¬ HasErr x.G)
  | n, c, r, hcR, he, hr, hn, hf => by
    have hpos : 0 < (descF U (StepM M (T.pick consB) P) c).card :=
      Finset.card_pos.mpr ⟨c, mem_descF.mpr ⟨hU c hcR, .refl⟩⟩
    cases n with
    | zero => omega
    | succ n =>
      have hf0 : r.fuel ≠ 0 := by omega
      have he' : r.err.isSome = false := by rw [he]; rfl
      rw [dfsX_succ]
      simp only [he', hf0, Bool.false_eq_true, ↓reduceIte]
      by_cases hE : HasErr c.G
      · simp only [hE, ↓reduceIte]
        exact ⟨hr, fun h => by cases h⟩
      simp only [hE, ↓reduceIte]
      rcases hs : stepM consB (Variant.repaired consB T) P c with _ | l
      · -- no next event: `c` is the only descendant
        have hone : descF U (StepM M (T.pick consB) P) c = {c} := by
          ext x
          rw [mem_descF, Finset.mem_singleton]
          constructor
          · rintro ⟨-, h⟩
            rcases ReflTransGen.cases_head h with h | ⟨y, hy, -⟩
            · exact h.symm
            · have := (stepM_eq_none_iff hc T P hcR.sound.wf.supp).mp hs
              cases hy with
              | nr h' => rw [h'.1] at this; cases this
              | revisit h' => rw [h'] at this; cases this
          · rintro rfl
            exact ⟨hU x hcR, .refl⟩
        refine ⟨hr, fun _ => ⟨?_, fun x hx => ?_⟩⟩
        · rw [hone, Finset.card_singleton]
          simp only
          omega
        · have : x ∈ descF U (StepM M (T.pick consB) P) c := mem_descF.mpr ⟨hU x (hcR.trans hx), hx⟩
          rw [hone, Finset.mem_singleton] at this
          rw [this]
          exact hE
      dsimp only
      have hcard := card_descF hc T hb U hU hcR hs
      obtain ⟨-, hmem⟩ := children_spec hc T hcR hs
      obtain ⟨k1, k2⟩ := dfsXFold_fuel T U (dfsX_fuel hb U hU n) hcR l
        { r with fuel := r.fuel - 1 } (fun b hb' => (hmem b).mp hb') he hr (fun b hbl => by
          have := List.le_sum_of_mem (List.mem_map_of_mem
            (f := fun a => (descF U (StepM M (T.pick consB) P) a).card) hbl)
          omega) (by simp only; omega)
      refine ⟨k1, fun h => ?_⟩
      obtain ⟨k21, k22⟩ := k2 h
      refine ⟨by simp only at k21; omega, fun x hx => ?_⟩
      rcases (desc_iff hc T hcR hs x).mp hx with rfl | ⟨a, ha, hax⟩
      · exact hE
      · exact k22 a ha x hax

/-- **`completeM_exit`** (plan row M9, Q12: the procedure with early exit exits iff `P` is
erroneous): for a model with a decision procedure, every selection and every bounded program,
with a fuel of at least the number of reachable configurations, the search with early exit
does not exhaust, and it returns a configuration iff some member of `⟦P⟧` contains an error
event; a returned configuration is reachable and contains an error event. -/
theorem completeM_exit {k : ℕ} (hb : P.Bounded k) {fuel : ℕ}
    (hfuel : {c | ReachM M (T.pick consB) P c}.ncard ≤ fuel) :
    (exploreX consB (Variant.repaired consB T) P fuel).exhausted = false ∧
      ((exploreX consB (Variant.repaired consB T) P fuel).err.isSome ↔ Erroneous M P) ∧
      ∀ x, (exploreX consB (Variant.repaired consB T) P fuel).err = some x →
        ReachM M (T.pick consB) P x ∧ HasErr x.G := by
  have hT := tieQ9_pick (M := M) hc T
  have hfin := reach_finite hT hb
  have hU : ∀ x, ReachM M (T.pick consB) P x → x ∈ hfin.toFinset := fun x hx =>
    hfin.mem_toFinset.mpr hx
  have hcard : hfin.toFinset.card = {c | ReachM M (T.pick consB) P c}.ncard :=
    (Set.ncard_eq_toFinset_card _ hfin).symm
  have hD : (descF hfin.toFinset (StepM M (T.pick consB) P) Config.init).card ≤
      hfin.toFinset.card := by
    unfold descF
    classical
    exact Finset.card_filter_le _ _
  obtain ⟨h1, h2⟩ := dfsX_fuel hc T hb hfin.toFinset hU fuel .init { fuel := fuel } .refl rfl rfl
    (by omega) (by simp only; omega)
  have hsound : ∀ x, (exploreX consB (Variant.repaired consB T) P fuel).err = some x →
      ReachM M (T.pick consB) P x ∧ HasErr x.G := fun x hx =>
    (exploreX_sound hc T hb hx).imp_right And.left
  refine ⟨h1, ⟨fun h => ?_, fun h => ?_⟩, hsound⟩
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    exact (exploreX_sound hc T hb hx).2.2
  · cases hx : (exploreX consB (Variant.repaired consB T) P fuel).err with
    | some x => rfl
    | none =>
      obtain ⟨c, hcR, hE⟩ := (reach_err_iff hT hb).mpr h
      exact absurd hE ((h2 hx).2 c hcR)

end Must

#print axioms Must.HasErr.mono
#print axioms Must.reach_err_iff
#print axioms Must.dfsX_succ
#print axioms Must.dfsX_found
#print axioms Must.dfsXFold_found
#print axioms Must.dfsX_sound
#print axioms Must.exploreX_sound
#print axioms Must.dfsXFold_fuel
#print axioms Must.dfsX_fuel
#print axioms Must.completeM_exit
