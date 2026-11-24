import Mazurkiewicz.Must.ModelComb
import Mathlib.Order.Extension.Linear

/-!
# Mailbox: the two forms of decision Q5

Paper: Section 3.2, Definition 3.7. Plan: decision Q5 (`PLAN-r1-astra.md`, "Q5: the two mailbox
repairs are equivalent").

`mbox` (`ModelComb.lean`) is (b), (c) for some strict total order `L` on the mailbox sends of the
graph that contains `porf` between them (one global order, not one per destination). The
equivalent form: (b), (c) for the restriction to mailbox sends of a strict total order `T` on
all events of the graph that contains `po ∪ rf` (`TotalOn`).

`mbox_iff_total_on_events`: the two are equivalent on well-formed graphs. From `T` to `L`:
restriction (`porf ⊆ T` by transitivity). From `L` to `T`: `po ∪ rf ∪ L` is acyclic (a cycle
through an `L` edge compresses, between mailbox sends, to an `L` cycle, `porf ⊆ L`); a linear
extension of its reflexive-transitive closure (Szpilrajn, `extend_partialOrder`) agrees with `L`
on the mailbox sends, so (b), (c) carry over.

Not formalised (plan, Section 7): the selective acyclicity form `po ∪ rf ∪ K`, and the
equivalence with the definition of Di Giusto et al. cited on p. 14.
-/

namespace Must

namespace Graph

open Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q] {G : Graph Q}

variable (G) in
/-- `T` is a strict total order on the events of `G` that contains `po ∪ rf` (Q5). -/
structure TotalOn (T : Ev Q → Ev Q → Prop) : Prop where
  /-- irreflexive on the events -/
  irrefl : ∀ a ∈ G.events, ¬ T a a
  /-- transitive on the events -/
  trans : ∀ a ∈ G.events, ∀ b ∈ G.events, ∀ c ∈ G.events, T a b → T b c → T a c
  /-- total on the events -/
  total : ∀ a ∈ G.events, ∀ b ∈ G.events, a ≠ b → T a b ∨ T b a
  /-- contains `po ∪ rf` -/
  porfStep : ∀ a b, G.porfStep a b → T a b

omit [DecidableEq Q] in
/-- A total order on the events containing `po ∪ rf` contains `porf`. -/
theorem Wf.porf_le_of_totalOn (hG : G.Wf) {T : Ev Q → Ev Q → Prop} (hT : G.TotalOn T)
    {a b : Ev Q} (h : G.porf a b) : T a b := by
  induction h with
  | single h => exact hT.porfStep _ _ h
  | @tail c d hac hcd ih =>
    have ha := (hG.mem_of_porf hac).1
    have hc := (hG.mem_of_porf hac).2
    have hd := (hG.mem_of_porfStep hcd).2
    exact hT.trans _ ha _ hc _ hd ih (hT.porfStep _ _ hcd)

variable (G) in
/-- `po ∪ rf ∪ L`, with `L` between mailbox sends. -/
def stepL (L : Ev Q → Ev Q → Prop) (a b : Ev Q) : Prop :=
  G.porfStep a b ∨ (G.MboxSend a ∧ G.MboxSend b ∧ L a b)

omit [DecidableEq Q] [Membership Val Q] in
/-- A path of `po ∪ rf ∪ L` is a `porf` path, or passes from mailbox send `x` to mailbox send `y`
by `L`, with `porf` paths before and after. -/
theorem MboxOrd.stepL_path {L : Ev Q → Ev Q → Prop} (hL : G.MboxOrd L) {a b : Ev Q}
    (h : TransGen (G.stepL L) a b) :
    G.porf a b ∨ ∃ x y, G.MboxSend x ∧ G.MboxSend y ∧ ReflTransGen G.porfStep a x ∧ L x y ∧
      ReflTransGen G.porfStep y b := by
  induction h with
  | single h =>
    rcases h with h | ⟨hx, hy, h⟩
    · exact Or.inl (TransGen.single h)
    · exact Or.inr ⟨_, _, hx, hy, ReflTransGen.refl, h, ReflTransGen.refl⟩
  | @tail c d _ hcd ih =>
    rcases hcd with hcd | ⟨hc, hd, hLcd⟩
    · rcases ih with ih | ⟨x, y, hx, hy, h1, h2, h3⟩
      · exact Or.inl (ih.tail hcd)
      · exact Or.inr ⟨x, y, hx, hy, h1, h2, h3.tail hcd⟩
    · rcases ih with ih | ⟨x, y, hx, hy, h1, h2, h3⟩
      · exact Or.inr ⟨c, d, hc, hd, ih.to_reflTransGen, hLcd, ReflTransGen.refl⟩
      · refine Or.inr ⟨x, d, hx, hd, h1, ?_, ReflTransGen.refl⟩
        rcases reflTransGen_iff_eq_or_transGen.mp h3 with h3 | h3
        · subst h3
          exact hL.trans _ _ _ hx hy hd h2 hLcd
        · exact hL.trans _ _ _ hx hc hd (hL.trans _ _ _ hx hy hc h2 (hL.porf _ _ hy hc h3)) hLcd

omit [DecidableEq Q] in
/-- `po ∪ rf ∪ L` is acyclic. -/
theorem Wf.stepL_acyclic (hG : G.Wf) {L : Ev Q → Ev Q → Prop} (hL : G.MboxOrd L) :
    Maz.Acyclic (G.stepL L) := by
  intro a h
  rcases hL.stepL_path h with h | ⟨x, y, hx, hy, h1, h2, h3⟩
  · exact hG.porf_irrefl a h
  · rcases reflTransGen_iff_eq_or_transGen.mp (h3.trans h1) with h4 | h4
    · subst h4
      exact hL.irrefl _ hy h2
    · exact hL.irrefl _ hx (hL.trans _ _ _ hx hy hx h2 (hL.porf _ _ hy hx h4))

/-- Decision Q5: on a well-formed graph, (b), (c) for a strict total order on the mailbox sends
containing `porf` between them is equivalent to (b), (c) for the restriction to mailbox sends of a
strict total order on all events containing `po ∪ rf`. -/
theorem mbox_iff_total_on_events (hG : G.Wf) :
    (∃ L, G.MboxOrd L ∧ G.BC (soMbox L)) ↔ ∃ T, G.TotalOn T ∧ G.BC (soMbox T) := by
  constructor
  · rintro ⟨L, hL, hb⟩
    let r := ReflTransGen (G.stepL L)
    have hac := hG.stepL_acyclic hL
    have hpo : IsPartialOrder (Ev Q) r :=
      { refl := fun _ => ReflTransGen.refl
        trans := fun _ _ _ h1 h2 => h1.trans h2
        antisymm := fun a b h1 h2 => by
          rcases reflTransGen_iff_eq_or_transGen.mp h1 with h | h
          · exact h.symm
          · exact absurd (h.trans_right h2) (hac b) }
    obtain ⟨s, hs, hrs⟩ := extend_partialOrder r
    have hsym : ∀ a b, s a b → s b a → a = b := fun a b h1 h2 => hs.antisymm a b h1 h2
    have hstep : ∀ a b, G.stepL L a b → s a b := fun a b h => hrs _ _ (ReflTransGen.single h)
    let T : Ev Q → Ev Q → Prop := fun a b => s a b ∧ a ≠ b
    have hTL : ∀ a b, G.MboxSend a → G.MboxSend b → T a b → L a b := by
      rintro a b ha hb ⟨h, hne⟩
      rcases hL.total a b ha hb hne with h' | h'
      · exact h'
      · exact absurd (hsym a b h (hstep _ _ (Or.inr ⟨hb, ha, h'⟩))) hne
    refine ⟨T, ⟨fun a _ h => h.2 rfl, fun a _ b _ c _ h1 h2 => ⟨hs.trans _ _ _ h1.1 h2.1, ?_⟩,
      fun a _ b _ hne => ?_, fun a b h => ⟨hstep _ _ (Or.inl h), ?_⟩⟩, ?_⟩
    · rintro rfl
      exact h1.2 (hsym _ _ h1.1 h2.1)
    · rcases hs.total a b with h | h
      · exact Or.inl ⟨h, hne⟩
      · exact Or.inr ⟨h, fun h' => hne h'.symm⟩
    · rintro rfl
      exact hG.porf_irrefl a (TransGen.single h)
    · exact hb.mono fun a ha b hb' ⟨x, y, z⟩ => ⟨x, y, hTL a b ⟨ha, x⟩ ⟨hb', y⟩ z⟩
  · rintro ⟨T, hT, hb⟩
    exact ⟨T, ⟨fun a ha => hT.irrefl a ha.1,
      fun a b c ha hb hc => hT.trans a ha.1 b hb.1 c hc.1,
      fun a b ha hb => hT.total a ha.1 b hb.1,
      fun a b _ _ h => hG.porf_le_of_totalOn hT h⟩, hb⟩

end Graph

namespace Model

open Graph

variable {Q : Type} [DecidableEq Q] [Membership Val Q]

/-- `mbox` in the form of Q5 with a total order on all events. -/
theorem mbox_cons_iff_total {G : Graph Q} :
    mbox.cons G ↔ G.Wf ∧ ∃ T, G.TotalOn T ∧ G.BC (soMbox T) := by
  rw [mbox_cons_iff]
  exact ⟨fun h => ⟨h.1, (mbox_iff_total_on_events h.1).mp h.2⟩,
    fun h => ⟨h.1, (mbox_iff_total_on_events h.1).mpr h.2⟩⟩

end Model

end Must

#print axioms Must.Graph.Wf.stepL_acyclic
#print axioms Must.Graph.mbox_iff_total_on_events
#print axioms Must.Model.mbox_cons_iff_total
