import Mazurkiewicz.Must.OpsMore
import Mazurkiewicz.Must.Compute

/-!
# Conditions (b), (c) of Definitions 3.5–3.7, for an arbitrary order on sends

Paper: Section 3.2, Definitions 3.5, 3.6, 3.7. Plan: `plan/must/lean/LEAN-PLAN.md`, decisions Q1,
Q4, Q5, Q11.

For a relation `so` on events (the order on sends of a model), with `so|dst` the `so` edges
between sends with the same destination and `mval` the value relation:

* `CondB so`: (b) `[US]; so|dst; rf ∩ mval = ∅`;
* `CondCWith po so`: (c) `po; rf⁻¹; (so|dst; rf ∩ mval)` irreflexive, for an explicit program
  order `po` (used by the witness of the printed `po`, `ModelEx.lean`); `CondC so` is it for the
  program order `G.po` of Q1;
* `BC so := CondB so ∧ CondC so`.

Composition binds tighter than `∩`, and `∩ mval` is kept in both conditions (predicate-sensitive
reading, `M0-astra.md` items 6–7).

The orders of the models (global `po`, `porf`, Q4): `soP2PWith po` (`[S^p2p]; po; [S^p2p]`),
`soCD G` (`[S^cd]; porf; [S^cd]`), `soMbox L` (`[S^mbox]; L; [S^mbox]` for an order `L`), and
`MboxOrd G L`: `L` is a strict total order on the mailbox sends of `G` that contains `porf` between
them (Q5).

Generic lemmas, for any `so`:

* `BC.mono`: (b), (c) are antitone in `so` (on the events of the graph);
* `Wf.bc_restrict`: (b), (c) for a fixed `so` survive restriction to a `porf`-closed set. The
  argument: a kept send made unread by the restriction was read by a removed receive `q` of the
  thread of the kept reader `r`; `q po r` puts `q` in the closed set, `r po q` is a (c) violation
  of the graph. It needs `po` total on each thread (Q1);
* `Wf.bc_add`: (b), (c) survive the addition of the next event of a thread, for `so` of the
  graph and `so'` of the extension, if `so'` between old events is in `so`, the new event is not
  `so'`-before an old event, and a new source `s₀` has no `so`-predecessor among the unread sends
  matching the new receive in destination and value.
* `exists_min_of_strict`: a finite non-empty set has a minimal element for a relation that is
  irreflexive and transitive on it.
-/

namespace Must

open Relation

variable {Q : Type}

/-- The destination of a send label. -/
def Lab.dst? : Lab Q → Option Tid
  | .send _ d _ => some d
  | _ => none

namespace Ev

/-- `a` is a send of the model `m`. -/
def SendOf (m : Comm) (a : Ev Q) : Prop := a.IsSend ∧ a.lab.model? = some m

instance (m : Comm) (a : Ev Q) : Decidable (SendOf m a) := by
  unfold SendOf
  infer_instance

variable [Membership Val Q]

/-- Matching (`Ev.Matches`) as a conjunction of its parts. -/
theorem matches_iff {s r : Ev Q} :
    s.Matches r ↔ s.IsSend ∧ r.IsRecv ∧ s.lab.dst? = some r.tid ∧ s.ValMatches r ∧
      s.lab.model? = r.lab.model? := by
  rcases s with ⟨ts, is, ls⟩
  rcases r with ⟨tr, ir, lr⟩
  cases ls <;> cases lr <;>
    simp [Matches, ValMatches, Lab.dst?, Lab.model?, Ev.IsSend, Ev.IsRecv, Lab.IsSend, Lab.IsRecv,
      eq_comm]

/-- The destination of a matching send is the thread of the receive. -/
theorem Matches.dst? {s r : Ev Q} (h : s.Matches r) : s.lab.dst? = some r.tid :=
  (matches_iff.mp h).2.2.1

end Ev

/-- A finite non-empty set has a minimal element for a relation irreflexive and transitive on
it. -/
theorem exists_min_of_strict {α : Type*} (U : Finset α) (R : α → α → Prop)
    (hirr : ∀ a ∈ U, ¬ R a a)
    (htr : ∀ a ∈ U, ∀ b ∈ U, ∀ c ∈ U, R a b → R b c → R a c) (hne : U.Nonempty) :
    ∃ m ∈ U, ∀ x ∈ U, ¬ R x m := by
  let R' : α → α → Prop := fun a b => a ∈ U ∧ b ∈ U ∧ R b a
  have key : ∀ a b, TransGen R' a b → a ∈ U ∧ b ∈ U ∧ R b a := by
    intro a b h
    induction h with
    | single h => exact h
    | tail _ h ih => exact ⟨ih.1, h.2.1, htr _ h.2.1 _ h.1 _ ih.1 h.2.2 ih.2.2⟩
  have hac : Maz.Acyclic R' := fun a h => by
    have := key a a h
    exact hirr a this.1 this.2.2
  obtain ⟨m, hm, hmax⟩ := hac.exists_maximal U hne
  exact ⟨m, hm, fun x hx hxm => hmax x hx ⟨hm, hx, hxm⟩⟩

namespace Graph

variable [DecidableEq Q] [Membership Val Q] (G : Graph Q)

/-! ### The conditions -/

/-- Definitions 3.5–3.7 (b) for the order `so`: `[US]; so|dst; rf ∩ mval = ∅`. -/
def CondB (so : Ev Q → Ev Q → Prop) : Prop :=
  ∀ s' ∈ G.US, ∀ s ∈ G.events, ∀ r ∈ G.events,
    ¬ (so s' s ∧ s'.lab.dst? = s.lab.dst? ∧ G.rf r = some (.snd s) ∧ s'.ValMatches r)

/-- Definitions 3.5–3.7 (c) for the order `so` and the program order `po`:
`po; rf⁻¹; (so|dst; rf ∩ mval)` is irreflexive. -/
def CondCWith (po so : Ev Q → Ev Q → Prop) : Prop :=
  ∀ r ∈ G.events, ∀ q ∈ G.events, ∀ s' ∈ G.events, ∀ s ∈ G.events,
    ¬ (po r q ∧ G.rf q = some (.snd s') ∧ so s' s ∧ s'.lab.dst? = s.lab.dst? ∧
      G.rf r = some (.snd s) ∧ s'.ValMatches r)

/-- (c) with the program order of Q1. -/
def CondC (so : Ev Q → Ev Q → Prop) : Prop := G.CondCWith G.po so

/-- (b) and (c) for the order `so`. -/
def BC (so : Ev Q → Ev Q → Prop) : Prop := G.CondB so ∧ G.CondC so

instance [∀ (v : Val) (q : Q), Decidable (v ∈ q)] (so : Ev Q → Ev Q → Prop) [DecidableRel so] :
    Decidable (G.CondB so) := by
  unfold CondB
  infer_instance

instance [∀ (v : Val) (q : Q), Decidable (v ∈ q)] (po so : Ev Q → Ev Q → Prop)
    [DecidableRel po] [DecidableRel so] : Decidable (G.CondCWith po so) := by
  unfold CondCWith
  infer_instance

instance [∀ (v : Val) (q : Q), Decidable (v ∈ q)] (so : Ev Q → Ev Q → Prop) [DecidableRel so] :
    Decidable (G.CondC so) := by
  unfold CondC
  infer_instance

instance [∀ (v : Val) (q : Q), Decidable (v ∈ q)] (so : Ev Q → Ev Q → Prop) [DecidableRel so] :
    Decidable (G.BC so) := by
  unfold BC
  infer_instance

/-! ### The orders of the models (Q4, Q5) -/

/-- `[S^p2p]; po; [S^p2p]` for a program order `po`. -/
def soP2PWith (po : Ev Q → Ev Q → Prop) (a b : Ev Q) : Prop :=
  a.SendOf .p2p ∧ b.SendOf .p2p ∧ po a b

/-- `so` of p2p (Definition 3.5): `[S^p2p]; po; [S^p2p]`. -/
def soP2P : Ev Q → Ev Q → Prop := soP2PWith G.po

/-- `so` of cd (Definition 3.6): `[S^cd]; porf; [S^cd]`. -/
def soCD (a b : Ev Q) : Prop := a.SendOf .cd ∧ b.SendOf .cd ∧ G.porf a b

omit [DecidableEq Q] [Membership Val Q] in
/-- `so` of mbox for an order `L` (Q5): `[S^mbox]; L; [S^mbox]`. -/
def soMbox (L : Ev Q → Ev Q → Prop) (a b : Ev Q) : Prop :=
  a.SendOf .mbox ∧ b.SendOf .mbox ∧ L a b

/-- `a` is a mailbox send of `G`. -/
def MboxSend (a : Ev Q) : Prop := a ∈ G.events ∧ a.SendOf .mbox

/-- `L` is a strict total order on the mailbox sends of `G` containing `porf` between them
(Q5). -/
structure MboxOrd (L : Ev Q → Ev Q → Prop) : Prop where
  /-- irreflexive -/
  irrefl : ∀ a, G.MboxSend a → ¬ L a a
  /-- transitive -/
  trans : ∀ a b c, G.MboxSend a → G.MboxSend b → G.MboxSend c → L a b → L b c → L a c
  /-- total -/
  total : ∀ a b, G.MboxSend a → G.MboxSend b → a ≠ b → L a b ∨ L b a
  /-- contains `porf` -/
  porf : ∀ a b, G.MboxSend a → G.MboxSend b → G.porf a b → L a b

omit [DecidableEq Q] [Membership Val Q] in
instance (po : Ev Q → Ev Q → Prop) [DecidableRel po] : DecidableRel (soP2PWith po) :=
  fun a b => by
    unfold soP2PWith
    infer_instance

instance [DecidableRel (α := Ev Q) G.po] : DecidableRel (G.soP2P) := fun a b => by
  unfold soP2P soP2PWith
  infer_instance

instance : DecidableRel (G.soCD) := fun a b => by
  unfold soCD
  infer_instance

instance (L : Ev Q → Ev Q → Prop) [DecidableRel L] : DecidableRel (soMbox L) := fun a b => by
  unfold soMbox
  infer_instance

variable {G}

/-! ### Monotonicity -/

/-- (b), (c) are antitone in the order, on the events of the graph. -/
theorem BC.mono {so so' : Ev Q → Ev Q → Prop} (h : G.BC so)
    (hle : ∀ a ∈ G.events, ∀ b ∈ G.events, so' a b → so a b) : G.BC so' := by
  refine ⟨fun s' hs' s hs r hr ⟨h1, h2, h3, h4⟩ => ?_,
    fun r hr q hq s' hs' s hs ⟨h1, h2, h3, h4, h5, h6⟩ => ?_⟩
  · exact h.1 s' hs' s hs r hr ⟨hle s' ((G.mem_US).mp hs').1 s hs h1, h2, h3, h4⟩
  · exact h.2 r hr q hq s' hs' s hs ⟨h1, h2, hle s' hs' s hs h3, h4, h5, h6⟩

/-! ### Program order is total on a thread -/

omit [DecidableEq Q] in
/-- Two different events of a thread are ordered by `po` (Q1). -/
theorem Wf.po_total (hG : G.Wf) {a b : Ev Q} (ha : a ∈ G.events) (hb : b ∈ G.events)
    (ht : a.tid = b.tid) (hne : a ≠ b) : G.po a b ∨ G.po b a := by
  rcases Nat.lt_trichotomy a.idx b.idx with h | h | h
  · exact Or.inl ⟨ha, hb, ht, h⟩
  · exact absurd (hG.idx_inj a ha b hb ht h) hne
  · exact Or.inr ⟨hb, ha, ht.symm, h⟩

omit [DecidableEq Q] in
/-- The reader of a send is in the thread of its destination. -/
theorem Wf.tid_of_rf (hG : G.Wf) {r s : Ev Q} (h : G.rf r = some (.snd s)) :
    s.lab.dst? = some r.tid :=
  (hG.rf_match r s h).dst?

/-! ### Restriction -/

/-- (b), (c) for a fixed order survive restriction to a `porf`-closed set. -/
theorem Wf.bc_restrict (hG : G.Wf) {E : Finset (Ev Q)} (hE : G.Closed E)
    {so : Ev Q → Ev Q → Prop} (h : G.BC so) : (G.restrict E).BC so := by
  refine ⟨fun s' hs' s hs r hr ⟨h1, h2, h3, h4⟩ => ?_,
    fun r hr q hq s' hs' s hs ⟨h1, h2, h3, h4, h5, h6⟩ => ?_⟩
  · obtain ⟨hs'E, hs'S, hs'U⟩ := mem_US_restrict.mp hs'
    rw [restrict_events] at hs hr
    have hrf := (restrict_rf_eq_some h3).1
    have hrG := (Finset.mem_inter.mp hr).1
    have hsG := (Finset.mem_inter.mp hs).1
    have hs'G := (Finset.mem_inter.mp hs'E).1
    by_cases hU : s' ∈ G.US
    · exact h.1 s' hU s hsG r hrG ⟨h1, h2, hrf, h4⟩
    · have : ¬ ∀ q ∈ G.events, G.rf q ≠ some (.snd s') := fun hall =>
        hU ((G.mem_US).mpr ⟨hs'G, hs'S, hall⟩)
      push Not at this
      obtain ⟨q, hqG, hq⟩ := this
      have hqE : q ∉ E := fun hqE => hs'U q (Finset.mem_inter.mpr ⟨hqG, hqE⟩) hq
      have ht : q.tid = r.tid := by
        have e1 := hG.tid_of_rf hq
        have e2 := hG.tid_of_rf hrf
        rw [h2, e2] at e1
        exact (Option.some.inj e1).symm
      have hne : r ≠ q := fun e => hqE (e ▸ (Finset.mem_inter.mp hr).2)
      rcases hG.po_total hrG hqG ht.symm hne with hpo | hpo
      · exact h.2 r hrG q hqG s' hs'G s hsG ⟨hpo, hq, h1, h2, hrf, h4⟩
      · have := hE (Or.inl hpo) (Finset.mem_coe.mpr hr)
        exact hqE (Finset.mem_inter.mp (Finset.mem_coe.mp this)).2
  · rw [restrict_events] at hr hq hs' hs
    rw [po_restrict_iff] at h1
    exact h.2 r (Finset.mem_inter.mp hr).1 q (Finset.mem_inter.mp hq).1 s'
      (Finset.mem_inter.mp hs').1 s (Finset.mem_inter.mp hs).1
      ⟨h1.1, (restrict_rf_eq_some h2).1, h3, h4, (restrict_rf_eq_some h5).1, h6⟩

/-! ### Addition of the next event of a thread -/

variable {e : Ev Q} {src : Option (Src Q)} {out : Option Val}

/-- In a well-formed addition of the next event of a thread, a real source is an unread send of
the graph that matches the new event. -/
theorem Wf.src_of_add (hG : G.Wf) (hidx : e.idx = G.cnt e.tid) (hG' : (G.add e src out).Wf)
    {s : Ev Q} (hs : src = some (.snd s)) : s ∈ G.US ∧ s.Matches e := by
  have he := hG.not_mem_of_idx_eq_cnt hidx
  have hrf : (G.add e src out).rf e = some (.snd s) := by
    rw [add_rf, Function.update_self, hs]
  have hm := hG'.rf_match e s hrf
  have hsE := hG'.rf_mem e s hrf
  have hse : s ≠ e := fun h => Lab.IsSend.not_isRecv hm.isSend (h ▸ hm.isRecv)
  rw [add_events, Finset.mem_insert] at hsE
  have hsG := hsE.resolve_left hse
  refine ⟨(G.mem_US).mpr ⟨hsG, hm.isSend, fun r hr h => ?_⟩, hm⟩
  have hre : r ≠ e := fun h' => he (h' ▸ hr)
  have h' : (G.add e src out).rf r = some (.snd s) := by
    rw [add_rf, Function.update_of_ne hre]
    exact h
  exact hre (hG'.rf_once r e s h' hrf)

omit [Membership Val Q] in
/-- `po` of an addition between old events is `po` of the graph. -/
theorem po_add_of_mem {a b : Ev Q} (ha : a ∈ G.events) (hb : b ∈ G.events)
    (h : (G.add e src out).po a b) : G.po a b :=
  ⟨ha, hb, h.2.2⟩

omit [Membership Val Q] in
/-- The new event, the next of its thread, has no `po`-successor. -/
theorem Wf.not_po_add_left [Membership Val Q] (hG : G.Wf) (hidx : e.idx = G.cnt e.tid)
    (b : Ev Q) : ¬ (G.add e src out).po e b := by
  rintro ⟨-, hb, ht, hi⟩
  rw [add_events, Finset.mem_insert] at hb
  rcases hb with rfl | hb
  · omega
  · have := hG.idx_lt_of_idx_eq_cnt hidx hb ht.symm
    omega

/-- (b), (c) survive the addition of the next event of a thread, given the three conditions on
the orders `so` (of the graph) and `so'` (of the extension). -/
theorem Wf.bc_add (hG : G.Wf) (hidx : e.idx = G.cnt e.tid) (hG' : (G.add e src out).Wf)
    {so so' : Ev Q → Ev Q → Prop} (h : G.BC so)
    (h1 : ∀ a ∈ G.events, ∀ b ∈ G.events, so' a b → so a b)
    (h2 : ∀ b ∈ G.events, ¬ so' e b)
    (h3 : ∀ s₀, src = some (.snd s₀) → ∀ s' ∈ G.US, s' ≠ s₀ → so s' s₀ →
      s'.lab.dst? = s₀.lab.dst? → s'.ValMatches e → False) :
    (G.add e src out).BC so' := by
  have he := hG.not_mem_of_idx_eq_cnt hidx
  have hsrc : ∀ s, src = some (.snd s) → s ∈ G.events :=
    fun s hs => ((G.mem_US).mp (hG.src_of_add hidx hG' hs).1).1
  have hmem : ∀ x ∈ (G.add e src out).events, x ≠ e → x ∈ G.events := fun x hx hxe => by
    rw [add_events, Finset.mem_insert] at hx
    exact hx.resolve_left hxe
  have hrfo : ∀ x, x ≠ e → (G.add e src out).rf x = G.rf x := fun x hx => by
    rw [add_rf, Function.update_of_ne hx]
  refine ⟨fun s' hs' s hs r hr ⟨hso, hd, hrf, hv⟩ => ?_,
    fun r hr q hq s' hs' s hs ⟨hpo, hq', hso, hd, hrf, hv⟩ => ?_⟩
  · rcases (hG.mem_US_add hidx hsrc).mp hs' with ⟨hse, -⟩ | ⟨hU, hne⟩
    · rw [hse] at hso
      by_cases hre : r = e
      · subst hre
        rw [add_rf, Function.update_self] at hrf
        exact h2 s (hsrc s hrf) hso
      · rw [hrfo r hre] at hrf
        exact h2 s (hG.rf_mem _ _ hrf) hso
    · have hs'G := ((G.mem_US).mp hU).1
      by_cases hre : r = e
      · subst hre
        rw [add_rf, Function.update_self] at hrf
        have hsG := hsrc s hrf
        have hss : s' ≠ s := fun h' => hne (h' ▸ hrf)
        exact h3 s hrf s' hU hss (h1 s' hs'G s hsG hso) hd hv
      · rw [hrfo r hre] at hrf
        have hsG := hG.rf_mem _ _ hrf
        exact h.1 s' hU s hsG r (hmem r hr hre) ⟨h1 s' hs'G s hsG hso, hd, hrf, hv⟩
  · have hre : r ≠ e := fun h' => hG.not_po_add_left hidx q (h' ▸ hpo)
    have hrG := hmem r hr hre
    rw [hrfo r hre] at hrf
    have hsG := hG.rf_mem _ _ hrf
    by_cases hqe : q = e
    · subst hqe
      rw [add_rf, Function.update_self] at hq'
      have hU := (hG.src_of_add hidx hG' hq').1
      have hs'G := ((G.mem_US).mp hU).1
      exact h.1 s' hU s hsG r hrG ⟨h1 s' hs'G s hsG hso, hd, hrf, hv⟩
    · rw [hrfo q hqe] at hq'
      have hqG := hmem q hq hqe
      have hs'G := hG.rf_mem _ _ hq'
      exact h.2 r hrG q hqG s' hs'G s hsG
        ⟨po_add_of_mem hrG hqG hpo, hq', h1 s' hs'G s hsG hso, hd, hrf, hv⟩

end Graph

end Must

#print axioms Must.Ev.matches_iff
#print axioms Must.exists_min_of_strict
#print axioms Must.Graph.BC.mono
#print axioms Must.Graph.Wf.po_total
#print axioms Must.Graph.Wf.bc_restrict
#print axioms Must.Graph.Wf.src_of_add
#print axioms Must.Graph.Wf.bc_add
