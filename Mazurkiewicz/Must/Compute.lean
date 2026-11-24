import Mazurkiewicz.Must.Ops
import Mathlib.Data.Finset.Union

/-!
# Computation on Must graphs

Decision procedures for concrete graphs (milestone M2 needs them).

* `reach G a`: the causal successors of `a`, computed by iterating one-step successors
  `G.events.card + 1` times; `porf_iff_mem_reach` (no hypothesis on `G`); `Decidable (G.porf a b)`.
* `closed_iff_fin`: closedness checked on the events of the graph and the sources of its
  receives; `Decidable (G.Closed E)`.
* `Supp G`: `rf` and `nd` are `none` outside the events (true for well-formed graphs and for every
  restriction of a graph with `Supp`, in particular for raw restrictions with a dangling source).
  `key G` is the finite set of triples `(e, rf e, nd e)` over the events; on graphs with `Supp`,
  equality is equality of keys (`eq_iff_key`), and `{G // G.Supp}` has decidable equality.
* `pred G e`: the strict causal predecessors of `e`; it is closed, and so is `insert e (pred e)`.

The premises of `Wf.add` and `Wf.setRF` are decidable on concrete inputs: `e.idx = G.cnt e.tid`,
`s ∈ G.US`, `s.Matches e` (for decidable membership in `Q`), `∀ r' ∈ G.events, …` by the
`Finset` instances, and `¬ G.porf r s` by the instance below.
-/

namespace Must

namespace Graph

open Relation

variable {Q : Type} [DecidableEq Q] (G : Graph Q)

/-! ### Reachability -/

/-- The one-step causal successors of `a`. -/
def succ (a : Ev Q) : Finset (Ev Q) := G.events.filter (G.porfStep a)

/-- The events reachable from `a` in at most `n + 1` steps. -/
def reachN (a : Ev Q) : ℕ → Finset (Ev Q)
  | 0 => G.succ a
  | n + 1 => reachN a n ∪ (reachN a n).biUnion G.succ

/-- The causal successors of `a`. -/
def reach (a : Ev Q) : Finset (Ev Q) := G.reachN a G.events.card

variable {G}

theorem mem_succ {a b : Ev Q} : b ∈ G.succ a ↔ G.porfStep a b := by
  unfold succ
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rcases h with ⟨-, hb, -⟩ | ⟨hb, -⟩ <;> exact hb

theorem reachN_succ (a : Ev Q) (n : ℕ) :
    G.reachN a (n + 1) = G.reachN a n ∪ (G.reachN a n).biUnion G.succ := rfl

theorem reachN_subset_succ (a : Ev Q) (n : ℕ) : G.reachN a n ⊆ G.reachN a (n + 1) := by
  rw [reachN_succ]
  exact Finset.subset_union_left

theorem reachN_mono {a : Ev Q} {m n : ℕ} (h : m ≤ n) : G.reachN a m ⊆ G.reachN a n := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · exact (ih (Nat.lt_succ_iff.mp h)).trans (reachN_subset_succ a n)
    · rw [h]

theorem reachN_subset_events (a : Ev Q) : ∀ n, G.reachN a n ⊆ G.events
  | 0 => Finset.filter_subset _ _
  | n + 1 => by
    rw [reachN_succ]
    exact Finset.union_subset (reachN_subset_events a n)
      (Finset.biUnion_subset.mpr fun _ _ => Finset.filter_subset _ _)

theorem porf_of_mem_reachN {a : Ev Q} : ∀ {n b}, b ∈ G.reachN a n → G.porf a b
  | 0, _, h => TransGen.single (mem_succ.mp h)
  | n + 1, b, h => by
    rw [reachN_succ] at h
    rcases Finset.mem_union.mp h with h | h
    · exact porf_of_mem_reachN h
    · obtain ⟨c, hc, hcb⟩ := Finset.mem_biUnion.mp h
      exact (porf_of_mem_reachN hc).tail (mem_succ.mp hcb)

theorem step_mem_reachN {a b c : Ev Q} {n : ℕ} (hb : b ∈ G.reachN a n) (h : G.porfStep b c) :
    c ∈ G.reachN a (n + 1) := by
  rw [reachN_succ]
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b, hb, mem_succ.mpr h⟩)

/-- Once the iteration is stationary, it stays so. -/
theorem reachN_stable {a : Ev Q} {k : ℕ} (hk : G.reachN a k = G.reachN a (k + 1)) :
    ∀ m, G.reachN a (k + m) = G.reachN a k
  | 0 => rfl
  | m + 1 => by
    have ih := reachN_stable hk m
    rw [← Nat.add_assoc, reachN_succ, ih, ← reachN_succ]
    exact hk.symm

/-- While the iteration grows strictly, the `n`-th set has at least `n` elements. -/
theorem card_reachN_ge {a : Ev Q} :
    ∀ n, (∀ k < n, G.reachN a k ≠ G.reachN a (k + 1)) → n ≤ (G.reachN a n).card
  | 0, _ => Nat.zero_le _
  | n + 1, h => by
    have ih := card_reachN_ge n (fun k hk => h k (Nat.lt_succ_of_lt hk))
    have hss : G.reachN a n ⊂ G.reachN a (n + 1) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨reachN_subset_succ a n, h n (Nat.lt_succ_self n)⟩
    have := Finset.card_lt_card hss
    omega

/-- The iteration is stationary at `G.events.card`. -/
theorem reach_stable (a : Ev Q) : G.reachN a (G.events.card + 1) = G.reach a := by
  have hex : ∃ k < G.events.card + 1, G.reachN a k = G.reachN a (k + 1) := by
    by_contra hno
    push Not at hno
    have h1 := card_reachN_ge (G := G) (a := a) _ hno
    have h2 := Finset.card_le_card (reachN_subset_events (G := G) a (G.events.card + 1))
    omega
  obtain ⟨k, hk, hkeq⟩ := hex
  have e1 := reachN_stable hkeq (G.events.card - k)
  have e2 := reachN_stable hkeq (G.events.card + 1 - k)
  rw [show k + (G.events.card - k) = G.events.card by omega] at e1
  rw [show k + (G.events.card + 1 - k) = G.events.card + 1 by omega] at e2
  unfold reach
  rw [e1, e2]

/-- `reach` is closed under causality steps. -/
theorem step_mem_reach {a b c : Ev Q} (hb : b ∈ G.reach a) (h : G.porfStep b c) :
    c ∈ G.reach a := by
  rw [← reach_stable a]
  exact step_mem_reachN hb h

/-- `porf` is membership in `reach`. -/
theorem porf_iff_mem_reach {a b : Ev Q} : G.porf a b ↔ b ∈ G.reach a := by
  constructor
  · intro h
    induction h with
    | single h =>
      have : _ ∈ G.reachN a 0 := mem_succ.mpr h
      exact reachN_mono (Nat.zero_le _) this
    | tail _ h ih => exact step_mem_reach ih h
  · exact porf_of_mem_reachN

instance (a b : Ev Q) : Decidable (G.porf a b) :=
  decidable_of_iff _ porf_iff_mem_reach.symm

/-! ### Closedness -/

variable (G) in
/-- The source of `b`, if it is a real send, is in `F`. -/
def SrcIn (F : Finset (Ev Q)) (b : Ev Q) : Prop :=
  match G.rf b with
  | some (.snd s) => s ∈ F
  | _ => True

instance (F : Finset (Ev Q)) (b : Ev Q) : Decidable (G.SrcIn F b) := by
  unfold SrcIn
  split <;> infer_instance

omit [DecidableEq Q] in
theorem srcIn_iff {F : Finset (Ev Q)} {b : Ev Q} :
    G.SrcIn F b ↔ ∀ s, G.rf b = some (.snd s) → s ∈ F := by
  unfold SrcIn
  split
  · next s h => exact ⟨fun h' s' hs' => by rw [h] at hs'; cases hs'; exact h', fun h' => h' s h⟩
  · next h => exact ⟨fun _ s hs => absurd hs (h s), fun _ => trivial⟩

/-- Closedness, checked on the events of the graph and the sources of its receives. -/
theorem closed_iff_fin {E : Finset (Ev Q)} :
    G.Closed E ↔
      ∀ b ∈ G.events ∩ E, (∀ a ∈ G.events, G.po a b → a ∈ E) ∧ G.SrcIn (G.events ∩ E) b := by
  constructor
  · intro h b hb
    refine ⟨fun a _ hab => ?_, srcIn_iff.mpr fun s hs => ?_⟩
    · exact (Finset.mem_inter.mp (Finset.mem_coe.mp (h (Or.inl hab) (Finset.mem_coe.mpr hb)))).2
    · exact Finset.mem_coe.mp (h (Or.inr ⟨(Finset.mem_inter.mp hb).1, hs⟩)
        (Finset.mem_coe.mpr hb))
  · intro h a b hab hb
    have hb := Finset.mem_coe.mp hb
    refine Finset.mem_coe.mpr ?_
    rcases hab with hpo | ⟨-, hrf⟩
    · exact Finset.mem_inter.mpr ⟨hpo.1, (h b hb).1 a hpo.1 hpo⟩
    · exact srcIn_iff.mp (h b hb).2 a hrf

instance (E : Finset (Ev Q)) : Decidable (G.Closed E) :=
  decidable_of_iff _ closed_iff_fin.symm

/-! ### Support and keys -/

variable (G) in
/-- `rf` and `nd` are `none` outside the events. -/
def Supp : Prop := ∀ e ∉ G.events, G.rf e = none ∧ G.nd e = none

variable (G) in
/-- The key of a graph: its events with their sources and outcomes. -/
def key : Finset (Ev Q × Option (Src Q) × Option Val) :=
  G.events.image (fun e => (e, G.rf e, G.nd e))

variable (G) in
/-- The graph with `rf` and `nd` cut to its events. -/
def normalize : Graph Q := G.restrict G.events

omit [DecidableEq Q] in
theorem Wf.supp [Membership Val Q] (hG : G.Wf) : G.Supp :=
  fun _ he => ⟨hG.rf_none (Or.inl he), hG.nd_none (Or.inl he)⟩

theorem Supp.restrict (hG : G.Supp) (E : Finset (Ev Q)) : (G.restrict E).Supp := by
  intro e he
  rw [restrict_events, Finset.mem_inter, not_and_or] at he
  by_cases hE : e ∈ E
  · have hG' := hG e (he.resolve_right (not_not.mpr hE))
    simp [hE, hG'.1, hG'.2]
  · simp [hE]

/-- Every restriction of a well-formed graph has `Supp`, also one with a dangling source. -/
theorem Wf.supp_restrict [Membership Val Q] (hG : G.Wf) (E : Finset (Ev Q)) :
    (G.restrict E).Supp :=
  hG.supp.restrict E

theorem Supp.add (hG : G.Supp) (e : Ev Q) (src : Option (Src Q)) (out : Option Val) :
    (G.add e src out).Supp := by
  intro q hq
  rw [add_events, Finset.mem_insert, not_or] at hq
  rw [add_rf, add_nd, Function.update_of_ne hq.1, Function.update_of_ne hq.1]
  exact hG q hq.2

theorem Supp.setRF (hG : G.Supp) {r : Ev Q} (hr : r ∈ G.events) (x : Src Q) :
    (G.setRF r x).Supp := by
  intro q hq
  rw [setRF_events] at hq
  have hne : q ≠ r := fun h => hq (h ▸ hr)
  rw [setRF_rf, setRF_nd, Function.update_of_ne hne]
  exact hG q hq

theorem supp_normalize (G : Graph Q) : G.normalize.Supp := by
  intro e he
  simp only [normalize, restrict_events, Finset.inter_self] at he
  simp [normalize, he]

theorem Supp.normalize_eq (hG : G.Supp) : G.normalize = G := by
  apply Graph.ext
  · simp [normalize]
  · funext e
    simp only [normalize, restrict_rf]
    split_ifs with he
    · rfl
    · exact (hG e he).1.symm
  · funext e
    simp only [normalize, restrict_nd]
    split_ifs with he
    · rfl
    · exact (hG e he).2.symm

theorem mem_key {G : Graph Q} {t : Ev Q × Option (Src Q) × Option Val} :
    t ∈ G.key ↔ t.1 ∈ G.events ∧ t.2.1 = G.rf t.1 ∧ t.2.2 = G.nd t.1 := by
  unfold key
  rw [Finset.mem_image]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨he, rfl, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨e, x, o⟩ := t
    simp only at h1 h2 h3
    exact ⟨e, h1, by rw [h2, h3]⟩

/-- On graphs with `Supp`, equality is equality of keys. -/
theorem eq_iff_key {G' : Graph Q} (hG : G.Supp) (hG' : G'.Supp) : G = G' ↔ G.key = G'.key := by
  constructor
  · rintro rfl
    rfl
  · intro h
    have hmem : ∀ e, e ∈ G.events → e ∈ G'.events ∧ G'.rf e = G.rf e ∧ G'.nd e = G.nd e := by
      intro e he
      have : (e, G.rf e, G.nd e) ∈ G'.key := h ▸ mem_key.mpr ⟨he, rfl, rfl⟩
      obtain ⟨h1, h2, h3⟩ := mem_key.mp this
      exact ⟨h1, h2.symm, h3.symm⟩
    have hmem' : ∀ e, e ∈ G'.events → e ∈ G.events := by
      intro e he
      have : (e, G'.rf e, G'.nd e) ∈ G.key := h.symm ▸ mem_key.mpr ⟨he, rfl, rfl⟩
      exact (mem_key.mp this).1
    have hev : G.events = G'.events := Finset.ext fun e => ⟨fun he => (hmem e he).1, hmem' e⟩
    apply Graph.ext hev
    · funext e
      by_cases he : e ∈ G.events
      · exact (hmem e he).2.1.symm
      · rw [(hG e he).1, (hG' e (hev ▸ he)).1]
    · funext e
      by_cases he : e ∈ G.events
      · exact (hmem e he).2.2.symm
      · rw [(hG e he).2, (hG' e (hev ▸ he)).2]

instance : DecidableEq {G : Graph Q // G.Supp} := fun a b =>
  decidable_of_iff (a.1.key = b.1.key) (by rw [Subtype.ext_iff, eq_iff_key a.2 b.2])

/-! ### Causal predecessors -/

variable (G) in
/-- The strict causal predecessors of `e`. -/
def pred (e : Ev Q) : Finset (Ev Q) := G.events.filter (fun a => G.porf a e)

theorem mem_pred {a e : Ev Q} : a ∈ G.pred e ↔ a ∈ G.events ∧ G.porf a e := by
  unfold pred
  rw [Finset.mem_filter]

variable [Membership Val Q]

/-- The strict causal predecessors of an event form a closed set. -/
theorem Wf.closed_pred (hG : G.Wf) (e : Ev Q) : G.Closed (G.pred e) := by
  intro a b hab hb
  have hb := Finset.mem_coe.mp hb
  have hbe := (mem_pred.mp (Finset.mem_inter.mp hb).2).2
  have ha := (hG.mem_of_porfStep hab).1
  exact Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨ha, mem_pred.mpr ⟨ha, TransGen.head hab hbe⟩⟩)

/-- The causal predecessors of an event together with the event form a closed set. -/
theorem Wf.closed_pred_insert (hG : G.Wf) (e : Ev Q) : G.Closed (insert e (G.pred e)) := by
  intro a b hab hb
  have hb := Finset.mem_coe.mp hb
  have ha := (hG.mem_of_porfStep hab).1
  refine Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨ha, Finset.mem_insert_of_mem ?_⟩)
  rcases Finset.mem_insert.mp (Finset.mem_inter.mp hb).2 with rfl | hb'
  · exact mem_pred.mpr ⟨ha, TransGen.single hab⟩
  · exact mem_pred.mpr ⟨ha, TransGen.head hab (mem_pred.mp hb').2⟩

end Graph

end Must
