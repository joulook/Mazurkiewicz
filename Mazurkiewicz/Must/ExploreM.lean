import Mazurkiewicz.Must.Branch
import Mazurkiewicz.Must.EnumSpec
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Set.Card

/-!
# The reference explorer reports every member of `⟦P⟧` exactly once (milestone M9)

Paper: Theorem 4.1 (a) and completeness, Algorithm 1. Plan: row M9 (`exploreM_spec`), Section 2b
(explorer's fuel contract: "search completed" vs "fuel exhausted"; termination of the search for
every bounded program is a theorem of M9).

The explorer is M2's `explore consB (Variant.repaired consB T) P fuel` (`ExploreC.lean`), for a
model `M` with a decision procedure `consB` (agreeing with `M.cons` on graphs with `Supp`: `asyn`,
`p2p`, `cd`), a selection `T` (the tie-break `T.pick consB`, Q9 by `tieQ9_pick`) and a bounded
program.

* `StepM.not_back`, `StepM.desc_disjoint`: from a reachable configuration there is no cycle, and
  the descendants of two different successors are disjoint (from `stepSeq_unique`, M8).
* `dfs_spec`: if a call of the depth-first search does not report exhaustion, it visits exactly
  the configurations reachable from its argument, each once, and reports exactly those of them
  without next event (in the visiting order).
* `dfs_sound`: for every fuel, visited configurations are reachable and reported ones have no
  next event.
* `reach_finite`: a bounded program has finitely many reachable configurations (reachable
  configurations are determined by their graphs, `ReachM.eq_of_abs_eq`, and the graphs are
  well-formed executions with at most `|threads| · n` events, all enumerated by M2's `lvl`).
* `dfs_fuel`, `explore_not_exhausted`: a fuel of at least the number of reachable configurations
  suffices (it bounds both the depth and the number of visits).
* `exploreM_spec`: with that fuel the search completes, the reported graphs are pairwise
  distinct and are exactly `⟦P⟧`, and the visited configurations are exactly the reachable ones,
  with pairwise distinct graphs (no `Visit` of two `≈` graphs). `exploreM_spec_of_not_exhausted`:
  the same conclusion for any fuel with which the run reports no exhaustion.
-/

namespace Must

open Graph Config Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q]
variable {M : Model Q} {P : Program Q} {tie : Tie Q}

/-! ### No cycles, disjoint subtrees -/

theorem StepSeq.of_reflTransGen {c d : Config Q}
    (h : ReflTransGen (StepM M tie P) c d) : ∃ S, StepSeq M tie P c S d := by
  induction h with
  | refl => exact ⟨[], .nil _⟩
  | tail _ hs ih =>
    obtain ⟨S, hS⟩ := ih
    exact ⟨_, hS.append (.single hs)⟩

/-- No cycle through a reachable configuration. -/
theorem StepM.not_back (hT : TieQ9 M tie) {k : ℕ} (hb : P.Bounded k) {c d : Config Q}
    (hc : ReachM M tie P c) (hs : StepM M tie P c d) : ¬ ReflTransGen (StepM M tie P) d c := by
  intro h
  obtain ⟨S, hS⟩ := hc.exists_stepSeq
  obtain ⟨S', hS'⟩ := StepSeq.of_reflTransGen h
  have h1 := congrArg List.length (stepSeq_unique hT hb (hS.append (.cons hs hS')) hS)
  simp at h1

/-- The descendants of two successors of a reachable configuration are disjoint unless the
successors are equal. -/
theorem StepM.desc_disjoint (hT : TieQ9 M tie) {k : ℕ} (hb : P.Bounded k) {c d₁ d₂ x : Config Q}
    (hc : ReachM M tie P c) (h₁ : StepM M tie P c d₁) (h₂ : StepM M tie P c d₂)
    (hx₁ : ReflTransGen (StepM M tie P) d₁ x) (hx₂ : ReflTransGen (StepM M tie P) d₂ x) :
    d₁ = d₂ := by
  obtain ⟨S, hS⟩ := hc.exists_stepSeq
  obtain ⟨S₁, hS₁⟩ := StepSeq.of_reflTransGen hx₁
  obtain ⟨S₂, hS₂⟩ := StepSeq.of_reflTransGen hx₂
  have h := List.append_cancel_left
    (stepSeq_unique hT hb (hS.append (.cons h₁ hS₁)) (hS.append (.cons h₂ hS₂)))
  exact (List.cons.inj h).1

/-! ### The depth-first search -/

variable [∀ (v : Val) (q : Q), Decidable (v ∈ q)] {consB : Graph Q → Bool}

omit [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
/-- **Finiteness**: a bounded program has finitely many reachable configurations. -/
theorem reach_finite (hT : TieQ9 M tie) {k : ℕ} (hb : P.Bounded k) :
    {c : Config Q | ReachM M tie P c}.Finite := by
  classical
  set Gs : Finset (Graph Q) :=
    (((List.range (P.threads.length * k + 1)).flatMap (lvl P)).map Config.G).toFinset
  refine Set.Finite.of_finite_image (f := Config.G) (Gs.finite_toSet.subset ?_) ?_
  · rintro _ ⟨c, hcR, rfl⟩
    have hcR' : ReachM M tie P c := hcR
    have hi := hcR'.sound
    obtain ⟨c', hc', he⟩ := mem_lvl_of_exec (P := P) c.G.events.card hi.wf hi.exec rfl
    have hle := card_le_of_bounded hi.wf hi.exec hb
    simp only [Gs, Finset.mem_coe, List.mem_toFinset, List.mem_map, List.mem_flatMap,
      List.mem_range]
    exact ⟨c', ⟨_, by omega, hc'⟩, he⟩
  · intro x hx y hy h
    exact ReachM.eq_of_abs_eq hT hb hx hy h

/-- The configurations of `U` reachable from `c` by `R`. -/
noncomputable def descF (U : Finset (Config Q)) (R : Config Q → Config Q → Prop) (c : Config Q) :
    Finset (Config Q) :=
  @Finset.filter _ (fun x => ReflTransGen R c x) (Classical.decPred _) U

omit [DecidableEq Q] [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
theorem mem_descF {U : Finset (Config Q)} {R : Config Q → Config Q → Prop} {c x : Config Q} :
    x ∈ descF U R c ↔ x ∈ U ∧ ReflTransGen R c x := by
  unfold descF
  classical
  exact Finset.mem_filter

/-- The fold over the successors in `dfs`. -/
abbrev dfsFold (consB : Graph Q → Bool) (V : Variant Q) (P : Program Q) (n d : ℕ)
    (l : List (Config Q)) (r : Result Q) : Result Q :=
  l.foldl (fun r c' => dfs consB V P n (d + 1) c' r) r

/-- The visit of `c` at depth `d` (the bookkeeping of `dfs` before the successors). -/
def visitR (r : Result Q) (d : ℕ) (c : Config Q) : Result Q :=
  { r with fuel := r.fuel - 1, visited := r.visited + 1, maxDepth := max r.maxDepth d,
           maxEvents := max r.maxEvents c.order.length, seen := r.seen ++ [c] }

theorem dfs_succ (V : Variant Q) (P : Program Q) (n d : ℕ) (c : Config Q) (r : Result Q) :
    dfs consB V P (n + 1) d c r =
      if r.fuel = 0 then { r with exhausted := true } else
      match stepM consB V P c with
      | none => { visitR r d c with reported := r.reported ++ [c] }
      | some [] => { visitR r d c with dead := r.dead + 1 }
      | some (a :: l) => dfsFold consB V P n d (a :: l) (visitR r d c) := by
  simp only [dfs, visitR, dfsFold]
  split_ifs
  · rfl
  · rcases stepM consB V P c with _ | _ | ⟨a, l⟩ <;> rfl

/-- Exhaustion is never undone. -/
theorem dfs_exhausted (V : Variant Q) (P : Program Q) :
    ∀ (n d : ℕ) (c : Config Q) (r : Result Q), r.exhausted = true →
      (dfs consB V P n d c r).exhausted = true
  | 0, _, _, _, _ => rfl
  | n + 1, d, c, r, h => by
    have hf : ∀ (l : List (Config Q)) (r : Result Q), r.exhausted = true →
        (dfsFold consB V P n d l r).exhausted = true := by
      intro l
      induction l with
      | nil => exact fun r h => h
      | cons a l ih => exact fun r h => ih _ (dfs_exhausted V P n (d + 1) a r h)
    unfold dfs
    split_ifs
    · rfl
    · split
      · exact h
      · exact h
      · exact hf _ _ h

theorem dfsFold_exhausted (V : Variant Q) (P : Program Q) (n d : ℕ) :
    ∀ (l : List (Config Q)) (r : Result Q), r.exhausted = true →
      (dfsFold consB V P n d l r).exhausted = true := by
  intro l
  induction l with
  | nil => exact fun r h => h
  | cons a l ih => exact fun r h => ih _ (dfs_exhausted V P n (d + 1) a r h)

/-- A configuration is terminal for the explorer: `stepM` is `none` (no next event). -/
abbrev term (consB : Graph Q → Bool) (T : Sel Q) (P : Program Q) (x : Config Q) : Bool :=
  (stepM consB (Variant.repaired consB T) P x).isNone

/-- The outcome of a completed call from `c`: `L` is appended to `seen`, its terminal members
to `reported`, the fuel decreases by its length, it has no duplicates, and its members are
the configurations accepted by `R`. -/
structure Covers (consB : Graph Q → Bool) (T : Sel Q) (P : Program Q) (r r' : Result Q)
    (R : Config Q → Prop) (L : List (Config Q)) : Prop where
  seen : r'.seen = r.seen ++ L
  reported : r'.reported = r.reported ++ L.filter (term consB T P)
  fuel : r'.fuel + L.length = r.fuel
  nodup : L.Nodup
  mem : ∀ x, x ∈ L ↔ R x

variable (hc : ∀ H : Graph Q, H.Supp → (consB H = true ↔ M.cons H)) (T : Sel Q)
include hc

/-- The successor list computed by `dfs` at a reachable configuration. -/
theorem children_spec {c : Config Q} (hcR : ReachM M (T.pick consB) P c) {l : List (Config Q)}
    (hs : stepM consB (Variant.repaired consB T) P c = some l) :
    l.Nodup ∧ ∀ c', c' ∈ l ↔ StepM M (T.pick consB) P c c' := by
  have h := stepM_spec hc T P hcR.sound
  rw [hs] at h
  exact h

/-- The fold over the successors: under `dfs_spec` for the depth `n`, a fold that does not
report exhaustion covers the descendants of the folded configurations. -/
theorem dfsFold_spec {k : ℕ} (hb : P.Bounded k) {n : ℕ}
    (ih : ∀ (d : ℕ) (c : Config Q) (r : Result Q), ReachM M (T.pick consB) P c →
      (dfs consB (Variant.repaired consB T) P n d c r).exhausted = false →
      ∃ L, Covers consB T P r (dfs consB (Variant.repaired consB T) P n d c r)
        (ReflTransGen (StepM M (T.pick consB) P) c) L)
    (d : ℕ) {c : Config Q} (hcR : ReachM M (T.pick consB) P c) :
    ∀ (l : List (Config Q)) (r : Result Q), (∀ a ∈ l, StepM M (T.pick consB) P c a) → l.Nodup →
      (dfsFold consB (Variant.repaired consB T) P n d l r).exhausted = false →
      ∃ L, Covers consB T P r (dfsFold consB (Variant.repaired consB T) P n d l r)
        (fun x => ∃ a ∈ l, ReflTransGen (StepM M (T.pick consB) P) a x) L := by
  intro l
  induction l with
  | nil =>
    intro r _ _ _
    exact ⟨[], ⟨by simp, by simp, by simp, List.nodup_nil, by simp⟩⟩
  | cons a l ihl =>
    intro r hl hnd hex
    have hb' := hb
    obtain ⟨ha, hnd'⟩ := List.nodup_cons.mp hnd
    have hex₁ : (dfs consB (Variant.repaired consB T) P n (d + 1) a r).exhausted = false := by
      cases h : (dfs consB (Variant.repaired consB T) P n (d + 1) a r).exhausted
      · rfl
      · have := dfsFold_exhausted (consB := consB) (Variant.repaired consB T) P n d l _ h
        simp only [dfsFold, List.foldl_cons] at hex
        rw [this] at hex
        cases hex
    have haR : ReachM M (T.pick consB) P a := hcR.tail (hl a (.head _))
    obtain ⟨L₁, h₁⟩ := ih (d + 1) a r haR hex₁
    obtain ⟨L₂, h₂⟩ := ihl _ (fun b hb => hl b (.tail _ hb)) hnd' hex
    refine ⟨L₁ ++ L₂, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · simp only [dfsFold, List.foldl_cons] at h₂ ⊢
      rw [h₂.seen, h₁.seen, List.append_assoc]
    · simp only [dfsFold, List.foldl_cons] at h₂ ⊢
      rw [h₂.reported, h₁.reported, List.filter_append, List.append_assoc]
    · have e₁ := h₁.fuel
      have e₂ := h₂.fuel
      simp only [dfsFold, List.foldl_cons] at e₂ ⊢
      simp only [List.length_append]
      omega
    · refine List.nodup_append.mpr ⟨h₁.nodup, h₂.nodup, fun x hx₁ y hx₂ hxy => ?_⟩
      subst hxy
      obtain ⟨b, hbl, hbx⟩ := (h₂.mem x).mp hx₂
      have hax := (h₁.mem x).mp hx₁
      have hab := StepM.desc_disjoint (tieQ9_pick (M := M) hc T) hb' hcR (hl a (.head _))
        (hl b (.tail _ hbl)) hax hbx
      subst hab
      exact ha hbl
    · intro x
      rw [List.mem_append, h₁.mem, h₂.mem]
      simp only [List.mem_cons, exists_eq_or_imp]

/-- **`dfs_spec`**: a call of the depth-first search from a reachable configuration `c` that
does not report exhaustion visits exactly the configurations reachable from `c`, each once, and
reports exactly the terminal ones among them, in visiting order. -/
theorem dfs_spec {k : ℕ} (hb : P.Bounded k) :
    ∀ (n d : ℕ) (c : Config Q) (r : Result Q), ReachM M (T.pick consB) P c →
      (dfs consB (Variant.repaired consB T) P n d c r).exhausted = false →
      ∃ L, Covers consB T P r (dfs consB (Variant.repaired consB T) P n d c r)
        (ReflTransGen (StepM M (T.pick consB) P) c) L
  | 0, _, _, _, _, hex => by simp [dfs] at hex
  | n + 1, d, c, r, hcR, hex => by
    have ih := dfs_spec hb n
    have hT := tieQ9_pick (M := M) hc T
    by_cases hf : r.fuel = 0
    · simp [dfs, hf] at hex
    have hnone : ∀ x, StepM M (T.pick consB) P c x → stepM consB (Variant.repaired consB T) P c ≠
        none := by
      intro x hx h
      have := (stepM_eq_none_iff hc T P hcR.sound.wf.supp).mp h
      cases hx with
      | nr h' => rw [h'.1] at this; cases this
      | revisit h' => rw [h'] at this; cases this
    rw [dfs_succ] at hex ⊢
    simp only [hf, ↓reduceIte] at hex ⊢
    rcases hs : stepM consB (Variant.repaired consB T) P c with _ | l
    · -- no next event: `c` is reported
      refine ⟨[c], ⟨rfl, by simp [term, hs], by simp [visitR]; omega, List.nodup_singleton _,
        fun x => ?_⟩⟩
      rw [List.mem_singleton]
      constructor
      · rintro rfl
        exact .refl
      · intro h
        rcases ReflTransGen.cases_head h with h | ⟨y, hy, -⟩
        · exact h.symm
        · exact absurd hs (hnone y hy)
    obtain ⟨hnd, hmem⟩ := children_spec hc T hcR hs
    have hterm : term consB T P c = false := by simp [term, hs]
    have hdesc : ∀ x, ReflTransGen (StepM M (T.pick consB) P) c x ↔
        x = c ∨ ∃ a ∈ l, ReflTransGen (StepM M (T.pick consB) P) a x := by
      intro x
      constructor
      · intro h
        rcases ReflTransGen.cases_head h with h | ⟨y, hy, hyx⟩
        · exact Or.inl h.symm
        · exact Or.inr ⟨y, (hmem y).mpr hy, hyx⟩
      · rintro (rfl | ⟨a, ha, hax⟩)
        · exact .refl
        · exact ReflTransGen.head ((hmem a).mp ha) hax
    have hnotin : ∀ a ∈ l, ¬ ReflTransGen (StepM M (T.pick consB) P) a c := fun a ha =>
      StepM.not_back hT hb hcR ((hmem a).mp ha)
    cases l with
    | nil =>
      refine ⟨[c], ⟨rfl, by simp [hterm, visitR], by simp [visitR]; omega,
        List.nodup_singleton _, fun x => ?_⟩⟩
      rw [hdesc x, List.mem_singleton]
      simp
    | cons a l =>
      simp only [hs] at hex ⊢
      obtain ⟨L, hL⟩ := dfsFold_spec hc T hb ih d hcR (a :: l) (visitR r d c)
        (fun b hb => (hmem b).mp hb) hnd hex
      refine ⟨c :: L, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
      · rw [hL.seen, visitR, List.append_assoc, List.singleton_append]
      · rw [hL.reported, List.filter_cons, hterm]
        rfl
      · have := hL.fuel
        have hv : (visitR r d c).fuel = r.fuel - 1 := rfl
        simp only [List.length_cons]
        omega
      · refine List.nodup_cons.mpr ⟨fun hc' => ?_, hL.nodup⟩
        obtain ⟨b, hb, hbc⟩ := (hL.mem c).mp hc'
        exact hnotin b hb hbc
      · intro x
        rw [List.mem_cons, hL.mem, hdesc x]

/-- The descendants of a configuration with computed successor list `l`. -/
theorem desc_iff {c : Config Q} (hcR : ReachM M (T.pick consB) P c) {l : List (Config Q)}
    (hs : stepM consB (Variant.repaired consB T) P c = some l) (x : Config Q) :
    ReflTransGen (StepM M (T.pick consB) P) c x ↔
      x = c ∨ ∃ a ∈ l, ReflTransGen (StepM M (T.pick consB) P) a x := by
  obtain ⟨-, hmem⟩ := children_spec hc T hcR hs
  constructor
  · intro h
    rcases ReflTransGen.cases_head h with h | ⟨y, hy, hyx⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨y, (hmem y).mpr hy, hyx⟩
  · rintro (rfl | ⟨a, ha, hax⟩)
    · exact .refl
    · exact ReflTransGen.head ((hmem a).mp ha) hax

/-- The number of descendants of a configuration is one more than the sum over its computed
successors (the subtrees are disjoint and do not contain the configuration). -/
theorem card_descF {k : ℕ} (hb : P.Bounded k) (U : Finset (Config Q))
    (hU : ∀ x, ReachM M (T.pick consB) P x → x ∈ U) {c : Config Q}
    (hcR : ReachM M (T.pick consB) P c) {l : List (Config Q)}
    (hs : stepM consB (Variant.repaired consB T) P c = some l) :
    (descF U (StepM M (T.pick consB) P) c).card =
      1 + (l.map fun a => (descF U (StepM M (T.pick consB) P) a).card).sum := by
  classical
  have hT := tieQ9_pick (M := M) hc T
  obtain ⟨hnd, hmem⟩ := children_spec hc T hcR hs
  have key : descF U (StepM M (T.pick consB) P) c =
      insert c (l.toFinset.biUnion (descF U (StepM M (T.pick consB) P))) := by
    ext x
    rw [Finset.mem_insert, Finset.mem_biUnion, mem_descF, desc_iff hc T hcR hs]
    constructor
    · rintro ⟨-, rfl | ⟨a, ha, hax⟩⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨a, List.mem_toFinset.mpr ha, mem_descF.mpr
          ⟨hU x (hcR.trans (ReflTransGen.head ((hmem a).mp ha) hax)), hax⟩⟩
    · rintro (rfl | ⟨a, ha, hx⟩)
      · exact ⟨hU x hcR, Or.inl rfl⟩
      · exact ⟨(mem_descF.mp hx).1, Or.inr ⟨a, List.mem_toFinset.mp ha, (mem_descF.mp hx).2⟩⟩
  have hnot : c ∉ l.toFinset.biUnion (descF U (StepM M (T.pick consB) P)) := by
    intro h
    obtain ⟨a, ha, hx⟩ := Finset.mem_biUnion.mp h
    exact StepM.not_back hT hb hcR ((hmem a).mp (List.mem_toFinset.mp ha)) (mem_descF.mp hx).2
  rw [key, Finset.card_insert_of_notMem hnot, Finset.card_biUnion, List.sum_toFinset _ hnd,
    add_comm]
  intro a ha b hb' hab
  rw [Function.onFun]
  refine Finset.disjoint_left.mpr fun x hxa hxb => hab ?_
  exact StepM.desc_disjoint hT hb hcR ((hmem a).mp (List.mem_toFinset.mp (Finset.mem_coe.mp ha)))
    ((hmem b).mp (List.mem_toFinset.mp (Finset.mem_coe.mp hb'))) (mem_descF.mp hxa).2
    (mem_descF.mp hxb).2

/-- The fold with enough fuel and depth for every successor does not exhaust. -/
theorem dfsFold_fuel {k : ℕ} (hb : P.Bounded k) (U : Finset (Config Q))
    (hU : ∀ x, ReachM M (T.pick consB) P x → x ∈ U) {n : ℕ}
    (ih : ∀ (d : ℕ) (c : Config Q) (r : Result Q), ReachM M (T.pick consB) P c →
      r.exhausted = false → (descF U (StepM M (T.pick consB) P) c).card ≤ n →
      (descF U (StepM M (T.pick consB) P) c).card ≤ r.fuel →
      (dfs consB (Variant.repaired consB T) P n d c r).exhausted = false)
    (d : ℕ) {c : Config Q} (hcR : ReachM M (T.pick consB) P c) :
    ∀ (l : List (Config Q)) (r : Result Q), (∀ a ∈ l, StepM M (T.pick consB) P c a) →
      r.exhausted = false → (∀ a ∈ l, (descF U (StepM M (T.pick consB) P) a).card ≤ n) →
      (l.map fun a => (descF U (StepM M (T.pick consB) P) a).card).sum ≤ r.fuel →
      (dfsFold consB (Variant.repaired consB T) P n d l r).exhausted = false := by
  intro l
  induction l with
  | nil => exact fun r _ hr _ _ => hr
  | cons a l ihl =>
    intro r hl hr hn hf
    simp only [List.map_cons, List.sum_cons] at hf
    have haR : ReachM M (T.pick consB) P a := hcR.tail (hl a (.head _))
    have h1 := ih (d + 1) a r haR hr (hn a (.head _)) (by omega)
    obtain ⟨L, hL⟩ := dfs_spec hc T hb n (d + 1) a r haR h1
    have hlen : L.length = (descF U (StepM M (T.pick consB) P) a).card := by
      classical
      rw [← List.toFinset_card_of_nodup hL.nodup]
      congr 1
      ext x
      rw [List.mem_toFinset, hL.mem, mem_descF]
      exact ⟨fun h => ⟨hU x (haR.trans h), h⟩, fun h => h.2⟩
    have hfu := hL.fuel
    simp only [dfsFold, List.foldl_cons]
    exact ihl _ (fun b hb' => hl b (.tail _ hb')) h1 (fun b hb' => hn b (.tail _ hb'))
      (by omega)

/-- **Fuel**: a call from a reachable configuration with depth bound and fuel at least the
number of its descendants does not exhaust. -/
theorem dfs_fuel {k : ℕ} (hb : P.Bounded k) (U : Finset (Config Q))
    (hU : ∀ x, ReachM M (T.pick consB) P x → x ∈ U) :
    ∀ (n d : ℕ) (c : Config Q) (r : Result Q), ReachM M (T.pick consB) P c →
      r.exhausted = false → (descF U (StepM M (T.pick consB) P) c).card ≤ n →
      (descF U (StepM M (T.pick consB) P) c).card ≤ r.fuel →
      (dfs consB (Variant.repaired consB T) P n d c r).exhausted = false
  | n, d, c, r, hcR, hr, hn, hf => by
    have hpos : 0 < (descF U (StepM M (T.pick consB) P) c).card :=
      Finset.card_pos.mpr ⟨c, mem_descF.mpr ⟨hU c hcR, .refl⟩⟩
    cases n with
    | zero => omega
    | succ n =>
      have hf0 : r.fuel ≠ 0 := by omega
      rw [dfs_succ]
      simp only [hf0, ↓reduceIte]
      rcases hs : stepM consB (Variant.repaired consB T) P c with _ | l
      · exact hr
      rcases l with _ | ⟨a, l⟩
      · exact hr
      have hcard := card_descF hc T hb U hU hcR hs
      obtain ⟨-, hmem⟩ := children_spec hc T hcR hs
      refine dfsFold_fuel hc T hb U hU (dfs_fuel hb U hU n) d hcR (a :: l) _
        (fun b hb' => (hmem b).mp hb') hr (fun b hbl => ?_) ?_
      · have := List.le_sum_of_mem (List.mem_map_of_mem
          (f := fun a => (descF U (StepM M (T.pick consB) P) a).card) hbl)
        omega
      · have hv : (visitR r d c).fuel = r.fuel - 1 := rfl
        omega

/-- The invariant of `dfs_sound`: visited configurations are reachable, reported ones have no
next event. -/
def SoundR (M : Model Q) (tie : Tie Q) (P : Program Q) (r : Result Q) : Prop :=
  (∀ x ∈ r.seen, ReachM M tie P x) ∧ ∀ x ∈ r.reported, ReachM M tie P x ∧ M.nextP P x.G = none

/-- **Soundness for every fuel**: every configuration visited by a call from a reachable
configuration is reachable, and every reported one has no next event. -/
theorem dfs_sound :
    ∀ (n d : ℕ) (c : Config Q) (r : Result Q), ReachM M (T.pick consB) P c →
      SoundR M (T.pick consB) P r →
      SoundR M (T.pick consB) P (dfs consB (Variant.repaired consB T) P n d c r)
  | 0, _, _, r, _, h => h
  | n + 1, d, c, r, hcR, h => by
    have hv : SoundR M (T.pick consB) P (visitR r d c) := by
      refine ⟨fun x hx => ?_, h.2⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact h.1 x hx
      · rw [List.mem_singleton.mp hx]
        exact hcR
    have hf : ∀ (l : List (Config Q)) (r : Result Q), (∀ a ∈ l, ReachM M (T.pick consB) P a) →
        SoundR M (T.pick consB) P r →
        SoundR M (T.pick consB) P (dfsFold consB (Variant.repaired consB T) P n d l r) := by
      intro l
      induction l with
      | nil => exact fun r _ h => h
      | cons a l ihl =>
        intro r hl h
        exact ihl _ (fun b hb' => hl b (.tail _ hb'))
          (dfs_sound n (d + 1) a r (hl a (.head _)) h)
    rw [dfs_succ]
    split_ifs
    · exact h
    rcases hs : stepM consB (Variant.repaired consB T) P c with _ | l
    · refine ⟨hv.1, fun x hx => ?_⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact h.2 x hx
      · rw [List.mem_singleton.mp hx]
        exact ⟨hcR, (stepM_eq_none_iff hc T P hcR.sound.wf.supp).mp hs⟩
    rcases l with _ | ⟨a, l⟩
    · exact hv
    obtain ⟨-, hmem⟩ := children_spec hc T hcR hs
    exact hf _ _ (fun b hb' => hcR.tail ((hmem b).mp hb')) hv

/-- Soundness of the explorer for every fuel: every visited configuration is reachable, and
every reported graph is in `⟦P⟧`. -/
theorem explore_sound {fuel : ℕ} :
    (∀ x ∈ (explore consB (Variant.repaired consB T) P fuel).seen, ReachM M (T.pick consB) P x) ∧
      ∀ x ∈ (explore consB (Variant.repaired consB T) P fuel).reported, M.Sem P x.G := by
  have h := dfs_sound (P := P) hc T fuel 0 .init { fuel := fuel } .refl ⟨by simp, by simp⟩
  exact ⟨h.1, fun x hx => reported_mem_sem (h.2 x hx).1 (h.2 x hx).2⟩

/-- **`exploreM_spec`, conditional form**: if the explorer reports no exhaustion, the reported
graphs are pairwise distinct and are exactly `⟦P⟧`, the visited configurations are exactly the
reachable ones and have pairwise distinct graphs (no two visits of `≈` graphs), and the reported
configurations are exactly the reachable ones without next event. -/
theorem exploreM_spec_of_not_exhausted {k : ℕ} (hb : P.Bounded k) {fuel : ℕ}
    (hex : (explore consB (Variant.repaired consB T) P fuel).exhausted = false) :
    ((explore consB (Variant.repaired consB T) P fuel).reported.map Config.G).Nodup ∧
      (∀ G, G ∈ (explore consB (Variant.repaired consB T) P fuel).reported.map Config.G ↔
        M.Sem P G) ∧
      ((explore consB (Variant.repaired consB T) P fuel).seen.map Config.G).Nodup ∧
      (∀ c, c ∈ (explore consB (Variant.repaired consB T) P fuel).seen ↔
        ReachM M (T.pick consB) P c) ∧
      (∀ c, c ∈ (explore consB (Variant.repaired consB T) P fuel).reported ↔
        ReachM M (T.pick consB) P c ∧ M.nextP P c.G = none) := by
  have hT := tieQ9_pick (M := M) hc T
  obtain ⟨L, hL⟩ := dfs_spec hc T hb fuel 0 .init { fuel := fuel } .refl hex
  have hseen : (explore consB (Variant.repaired consB T) P fuel).seen = L := by
    simpa [explore] using hL.seen
  have hrep : (explore consB (Variant.repaired consB T) P fuel).reported =
      L.filter (term consB T P) := by
    simpa [explore] using hL.reported
  have hmemL : ∀ c, c ∈ L ↔ ReachM M (T.pick consB) P c := hL.mem
  have hinj : ∀ x ∈ L, ∀ y ∈ L, x.G = y.G → x = y := fun x hx y hy h =>
    ReachM.eq_of_abs_eq hT hb ((hmemL x).mp hx) ((hmemL y).mp hy) h
  have hrepmem : ∀ c, c ∈ (explore consB (Variant.repaired consB T) P fuel).reported ↔
      ReachM M (T.pick consB) P c ∧ M.nextP P c.G = none := by
    intro c
    rw [hrep, List.mem_filter, hmemL]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (stepM_eq_none_iff hc T P h1.sound.wf.supp).mp (Option.isNone_iff_eq_none.mp h2)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Option.isNone_iff_eq_none.mpr ((stepM_eq_none_iff hc T P h1.sound.wf.supp).mpr h2)⟩
  refine ⟨?_, fun G => ?_, ?_, fun c => ?_, hrepmem⟩
  · rw [hrep]
    exact (hL.nodup.filter _).map_on fun x hx y hy h =>
      hinj x (List.mem_of_mem_filter hx) y (List.mem_of_mem_filter hy) h
  · rw [List.mem_map, ← reported_iff_sem hT hb]
    constructor
    · rintro ⟨c, hc', rfl⟩
      exact ⟨c, ((hrepmem c).mp hc').1, ((hrepmem c).mp hc').2, rfl⟩
    · rintro ⟨c, h1, h2, rfl⟩
      exact ⟨c, (hrepmem c).mpr ⟨h1, h2⟩, rfl⟩
  · rw [hseen]
    exact hL.nodup.map_on hinj
  · rw [hseen]
    exact hmemL c

/-- **Termination with explicit fuel**: a fuel of at least the number of reachable
configurations (finite, `reach_finite`) makes the explorer complete its search. -/
theorem explore_not_exhausted {k : ℕ} (hb : P.Bounded k) {fuel : ℕ}
    (hfuel : {c | ReachM M (T.pick consB) P c}.ncard ≤ fuel) :
    (explore consB (Variant.repaired consB T) P fuel).exhausted = false := by
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
  exact dfs_fuel hc T hb hfin.toFinset hU fuel 0 .init { fuel := fuel } .refl rfl (by omega)
    (by simp only; omega)

/-- **`exploreM_spec`** (plan row M9; Theorem 4.1 for the reference explorer): for a model with
a decision procedure, every selection and every bounded program, with a fuel of at least the
number of reachable configurations the explorer completes its search, reports pairwise distinct
graphs, exactly the members of `⟦P⟧`, and visits every reachable configuration once, with
pairwise distinct graphs. -/
theorem exploreM_spec {k : ℕ} (hb : P.Bounded k) {fuel : ℕ}
    (hfuel : {c | ReachM M (T.pick consB) P c}.ncard ≤ fuel) :
    (explore consB (Variant.repaired consB T) P fuel).exhausted = false ∧
      ((explore consB (Variant.repaired consB T) P fuel).reported.map Config.G).Nodup ∧
      (∀ G, G ∈ (explore consB (Variant.repaired consB T) P fuel).reported.map Config.G ↔
        M.Sem P G) ∧
      ((explore consB (Variant.repaired consB T) P fuel).seen.map Config.G).Nodup ∧
      (∀ c, c ∈ (explore consB (Variant.repaired consB T) P fuel).seen ↔
        ReachM M (T.pick consB) P c) :=
  have hex := explore_not_exhausted hc T hb hfuel
  have h := exploreM_spec_of_not_exhausted hc T hb hex
  ⟨hex, h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- With a completed search, the number of reachable configurations is the number of visits. -/
theorem reach_ncard_of_not_exhausted {k : ℕ} (hb : P.Bounded k) {fuel : ℕ}
    (hex : (explore consB (Variant.repaired consB T) P fuel).exhausted = false) :
    {c | ReachM M (T.pick consB) P c}.ncard =
      (explore consB (Variant.repaired consB T) P fuel).seen.length := by
  classical
  obtain ⟨-, -, hnd, hmem, -⟩ := exploreM_spec_of_not_exhausted hc T hb hex
  have hs : {c | ReachM M (T.pick consB) P c} =
      ↑((explore consB (Variant.repaired consB T) P fuel).seen.toFinset) := by
    ext c
    rw [Finset.mem_coe, List.mem_toFinset, hmem]
    rfl
  rw [hs, Set.ncard_coe_finset, List.toFinset_card_of_nodup (hnd.of_map _)]

/-- With a completed search, the number of members of `⟦P⟧` is the number of reports. -/
theorem sem_ncard_of_not_exhausted {k : ℕ} (hb : P.Bounded k) {fuel : ℕ}
    (hex : (explore consB (Variant.repaired consB T) P fuel).exhausted = false) :
    {G | M.Sem P G}.ncard = (explore consB (Variant.repaired consB T) P fuel).reported.length := by
  classical
  obtain ⟨hnd, hmem, -⟩ := exploreM_spec_of_not_exhausted hc T hb hex
  have hs : {G | M.Sem P G} =
      ↑(((explore consB (Variant.repaired consB T) P fuel).reported.map Config.G).toFinset) := by
    ext G
    rw [Finset.mem_coe, List.mem_toFinset, hmem]
    rfl
  rw [hs, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map]

end Must

#print axioms Must.StepSeq.of_reflTransGen
#print axioms Must.StepM.not_back
#print axioms Must.StepM.desc_disjoint
#print axioms Must.reach_finite
#print axioms Must.dfs_succ
#print axioms Must.dfs_exhausted
#print axioms Must.children_spec
#print axioms Must.dfsFold_spec
#print axioms Must.dfs_spec
#print axioms Must.desc_iff
#print axioms Must.card_descF
#print axioms Must.dfsFold_fuel
#print axioms Must.dfs_fuel
#print axioms Must.dfs_sound
#print axioms Must.explore_sound
#print axioms Must.exploreM_spec_of_not_exhausted
#print axioms Must.explore_not_exhausted
#print axioms Must.exploreM_spec
#print axioms Must.dfsFold_exhausted
#print axioms Must.reach_ncard_of_not_exhausted
#print axioms Must.sem_ncard_of_not_exhausted
