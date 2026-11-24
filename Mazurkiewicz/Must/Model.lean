import Mazurkiewicz.Must.ModelCond
import Mazurkiewicz.Must.Exec

/-!
# Communication models: the interface (Section 3.2.1, Appendix A.5)

Paper: Section 3.2.1 (No "Out-of-Thin-Air", Prefix-closedness, Conditional Extensibility),
Appendix A.5 (Axioms 1, 2). Plan: `plan/must/lean/LEAN-PLAN.md`, decisions Q1, Q2, Q7, Q11.

A model is a consistency predicate `cons` on graphs with:

* `wf`: a consistent graph is well-formed; in particular `porf` is irreflexive (`Wf.porf_irrefl`);
* `empty`: the empty graph is consistent;
* `prefixClosed` (repaired prefix notion): the restriction of a consistent graph to a `porf`-closed
  set is consistent;
* conditional extensibility (Q11), for a consistent `G` and a legal fresh event `e` (the next
  event of its thread, `e.idx = G.cnt e.tid`; old events, sources and outcomes unchanged):
  `ext_plain` (send, block, error), `ext_nd` (ND, with every outcome of its set), `ext_bot` (a
  non-blocking receive reading `⊥`), `ext_recvB` (a blocking receive has a consistent source, or
  every send of the graph matching it in destination, value and model is read).

Derived, for every model:

* `porf_irrefl` (No "Out-of-Thin-Air");
* `exists_src_iff` (Q7): for a consistent `G` and a fresh receive, a consistent source exists iff
  an unread matching send exists;
* `exists_add_of_not_recvB` (3.2.1, "all events apart from blocking receives can always be
  added", repaired: an ND event needs a non-empty set);
* `Usable`, `availM` (Q7) for a model, `mem_availM_iff`, and `availM_eq`: M2's `Program.availM`
  for a Boolean test that agrees with `cons` on graphs with `Supp` is the model's `availM`.
-/

namespace Must

open Graph

/-- A communication model (Section 3.2.1, Q11). -/
structure Model (Q : Type) [DecidableEq Q] [Membership Val Q] where
  /-- the consistency predicate -/
  cons : Graph Q → Prop
  /-- consistent graphs are well-formed (hence `porf` is irreflexive) -/
  wf : ∀ G, cons G → G.Wf
  /-- the empty graph is consistent -/
  empty : cons Graph.empty
  /-- prefix-closedness: restriction to a `porf`-closed set -/
  prefixClosed : ∀ G E, cons G → G.Closed E → cons (G.restrict E)
  /-- a fresh send, block or error event extends -/
  ext_plain : ∀ G (e : Ev Q), cons G → e.idx = G.cnt e.tid → ¬ e.IsRecv → ¬ e.IsND →
    cons (G.add e none none)
  /-- a fresh ND event extends with every outcome of its set -/
  ext_nd : ∀ G (e : Ev Q) v, cons G → e.idx = G.cnt e.tid → e.IsND → v ∈ e.ndSet →
    cons (G.addND e v)
  /-- a fresh non-blocking receive extends with `⊥` -/
  ext_bot : ∀ G (e : Ev Q), cons G → e.idx = G.cnt e.tid → e.IsRecvNB → cons (G.addRecv e .bot)
  /-- a fresh blocking receive has a consistent source, or every matching send is read -/
  ext_recvB : ∀ G (e : Ev Q), cons G → e.idx = G.cnt e.tid → e.IsRecvB →
    (∃ s ∈ G.S, cons (G.addRecv e (.snd s))) ∨
      (∀ s ∈ G.S, s.Matches e → ∃ r ∈ G.events, G.rf r = some (.snd s))

namespace Model

variable {Q : Type} [DecidableEq Q] [Membership Val Q] (M : Model Q)

/-- No "Out-of-Thin-Air" (3.2.1, p. 14: "given a graph `G` with `consistent(G)`, then
`G.porf` is irreflexive"): a consistent graph has no causal cycle. -/
theorem porf_irrefl {G : Graph Q} (h : M.cons G) (a : Ev Q) : ¬ G.porf a a :=
  (M.wf G h).porf_irrefl a

/-- A prefix of a consistent graph is consistent. -/
theorem cons_of_isPrefixOf {G G' : Graph Q} (h : M.cons G) (hp : G'.IsPrefixOf G) :
    M.cons G' := by
  obtain ⟨E, hE, rfl⟩ := hp
  exact M.prefixClosed G E h hE

/-- A consistent source of a fresh receive is an unread matching send. -/
theorem src_of_cons {G : Graph Q} {e s : Ev Q} (hG : M.cons G) (hidx : e.idx = G.cnt e.tid)
    (h : M.cons (G.addRecv e (.snd s))) : s ∈ G.US ∧ s.Matches e :=
  (M.wf G hG).src_of_add hidx (M.wf _ h) rfl

/-- Q7: for a consistent graph and a fresh blocking receive, a consistent source exists iff an
unread send with matching destination, model and value exists. -/
theorem exists_src_iff {G : Graph Q} {e : Ev Q} (hG : M.cons G) (hidx : e.idx = G.cnt e.tid)
    (hB : e.IsRecvB) :
    (∃ s ∈ G.S, M.cons (G.addRecv e (.snd s))) ↔ ∃ s ∈ G.US, s.Matches e := by
  constructor
  · rintro ⟨s, -, hs⟩
    exact ⟨s, M.src_of_cons hG hidx hs⟩
  · rintro ⟨s, hU, hm⟩
    rcases M.ext_recvB G e hG hidx hB with h | h
    · exact h
    · obtain ⟨r, hr, hrs⟩ := h s (G.US_subset_S hU) hm
      exact absurd hrs (((G.mem_US).mp hU).2.2 r hr)

/-- 3.2.1, p. 14: "the conditions above imply that all events apart from blocking receives can
always be added in a consistent manner". Repaired: every fresh event other than a blocking
receive and other than an ND event with an empty set can be added consistently. Printed clause
(ii) does give a non-blocking receive some consistent source; what it lacks is the specific
contract "a non-blocking receive always extends with `⊥`" (`ext_bot`), which the canonical replay
(Q10 (i)) needs; this theorem uses it. -/
theorem exists_add_of_not_recvB {G : Graph Q} {e : Ev Q} (hG : M.cons G)
    (hidx : e.idx = G.cnt e.tid) (hB : ¬ e.IsRecvB) (hN : e.IsND → e.ndSet.Nonempty) :
    ∃ src out, M.cons (G.add e src out) := by
  by_cases hR : e.IsRecv
  · have hNB : e.IsRecvNB := (Lab.IsRecv.recvB_or_recvNB hR).resolve_left hB
    exact ⟨_, _, M.ext_bot G e hG hidx hNB⟩
  · by_cases hD : e.IsND
    · obtain ⟨v, hv⟩ := hN hD
      exact ⟨_, _, M.ext_nd G e v hG hidx hD hv⟩
    · exact ⟨_, _, M.ext_plain G e hG hidx hR hD⟩

/-! ### Availability (Q7) -/

/-- The fresh event `e` can be added (Q7): it is not a blocking receive, or it has a consistent
source. -/
def Usable (G : Graph Q) (e : Ev Q) : Prop :=
  ¬ e.IsRecvB ∨ ∃ s ∈ G.S, M.cons (G.addRecv e (.snd s))

/-- Q7 for `Usable`: on a consistent graph, a fresh event is usable iff it is not a blocking
receive or an unread matching send exists. -/
theorem usable_iff {G : Graph Q} {e : Ev Q} (hG : M.cons G) (hidx : e.idx = G.cnt e.tid) :
    M.Usable G e ↔ ¬ e.IsRecvB ∨ ∃ s ∈ G.US, s.Matches e := by
  unfold Usable
  by_cases hB : e.IsRecvB
  · simp only [hB, not_true_eq_false, false_or]
    exact M.exists_src_iff hG hidx hB
  · simp [hB]

/-- `availM` of the model (Q7): the usable next events of the threads, in thread order. -/
noncomputable def availM (P : Program Q) (G : Graph Q) : List (Ev Q) :=
  P.threads.filterMap fun t =>
    (P.nextEv G t).filter (fun e => @decide (M.Usable G e) (Classical.propDecidable _))

omit [DecidableEq Q] [Membership Val Q] in
/-- The next event of a thread is fresh. -/
theorem idx_of_nextEv {P : Program Q} {G : Graph Q} {t : Tid} {e : Ev Q}
    (h : P.nextEv G t = some e) : e.idx = G.cnt e.tid := by
  unfold Program.nextEv at h
  obtain ⟨l, -, rfl⟩ := Option.map_eq_some_iff.mp h
  rfl

/-- Membership in `availM`: a next event of a thread of the program that is usable. -/
theorem mem_availM_iff' {P : Program Q} {G : Graph Q} {e : Ev Q} :
    e ∈ M.availM P G ↔ ∃ t ∈ P.threads, P.nextEv G t = some e ∧ M.Usable G e := by
  unfold availM
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨t, ht, h⟩
    obtain ⟨h1, h2⟩ := Option.filter_eq_some_iff.mp h
    exact ⟨t, ht, h1, @of_decide_eq_true _ (Classical.propDecidable _) h2⟩
  · rintro ⟨t, ht, h1, h2⟩
    refine ⟨t, ht, Option.filter_eq_some_iff.mpr ⟨h1, ?_⟩⟩
    exact @decide_eq_true _ (Classical.propDecidable _) h2

/-- Q7 for `availM`: on a consistent graph, the available events are the next events of the
threads that are not blocking receives or have an unread matching send. -/
theorem mem_availM_iff {P : Program Q} {G : Graph Q} {e : Ev Q} (hG : M.cons G) :
    e ∈ M.availM P G ↔
      ∃ t ∈ P.threads, P.nextEv G t = some e ∧ (¬ e.IsRecvB ∨ ∃ s ∈ G.US, s.Matches e) := by
  rw [mem_availM_iff']
  constructor
  · rintro ⟨t, ht, h1, h2⟩
    exact ⟨t, ht, h1, (M.usable_iff hG (idx_of_nextEv h1)).mp h2⟩
  · rintro ⟨t, ht, h1, h2⟩
    exact ⟨t, ht, h1, (M.usable_iff hG (idx_of_nextEv h1)).mpr h2⟩

/-- M2's `Usable` for a Boolean test that agrees with `cons` on graphs with `Supp` is the model's
`Usable`, on graphs with `Supp` (every well-formed graph). -/
theorem usable_congr (cons : Graph Q → Bool) (hc : ∀ H : Graph Q, H.Supp → (cons H = true ↔
    M.cons H)) {G : Graph Q} (hS : G.Supp) (e : Ev Q) :
    Program.Usable cons G e ↔ M.Usable G e := by
  unfold Program.Usable Usable
  refine or_congr Iff.rfl (exists_congr fun s => and_congr Iff.rfl ?_)
  exact hc _ (hS.add e _ _)

/-- M2's `availM` for a Boolean test that agrees with `cons` on graphs with `Supp` is the
model's `availM`, on graphs with `Supp`. -/
theorem availM_eq (cons : Graph Q → Bool) (hc : ∀ H : Graph Q, H.Supp → (cons H = true ↔
    M.cons H)) (P : Program Q) {G : Graph Q} (hS : G.Supp) :
    P.availM cons G = M.availM P G := by
  unfold Program.availM availM
  congr 1
  funext t
  congr 1
  funext e
  exact @decide_eq_decide _ _ _ (Classical.propDecidable _) |>.mpr (M.usable_congr cons hc hS e)

end Model

end Must

#print axioms Must.Model.porf_irrefl
#print axioms Must.Model.cons_of_isPrefixOf
#print axioms Must.Model.src_of_cons
#print axioms Must.Model.exists_src_iff
#print axioms Must.Model.exists_add_of_not_recvB
#print axioms Must.Model.usable_iff
#print axioms Must.Model.mem_availM_iff
#print axioms Must.Model.usable_congr
#print axioms Must.Model.availM_eq
