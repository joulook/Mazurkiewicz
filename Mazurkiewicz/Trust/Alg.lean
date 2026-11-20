import Mazurkiewicz.Models.Model

/-!
# Algorithm 1 as a transition relation

Paper: Section 3.4 (maximal extensions), Section 4.1 with Algorithm 1, and
Appendix A, Def. A.1-A.6. Coq: `trust/Alg.v` (`TruSt_step`, `IsMaximal`,
`TruSt`).

A step `c ⇒ c'` of the algorithm (Def. A.2) is: calling `Visit` on the
configuration `c` immediately calls `Visit` on `c'`, and `c'` passes the
consistency check of line 4. There are three rules, labelled as in Def. A.3:

* `read` (lines 10-12): the next event is a read; it reads from any write of
  its location.
* `write` (lines 13-14, 21-22): the next event is a write; it is placed after
  any write of its location in the coherence order.
* `revisit` (lines 15-18, 21-22): the next event is a write `w`; a read `r` of
  its location that is not causally before `w` is made to read from `w`; the
  events added after `r` that are not causally before `w` are deleted; `w` is
  then placed in the coherence order.

How the text of Algorithm 1 is read here (plan, table "Differences from the
paper"):

* The paper's `next_P` adds the new event `a` to the graph before the case
  distinction; lines 15-17 then speak of `G` with `a` in it, and of `G.porf`
  with `a`. Here `c` is the configuration before `a`; the graph with `a` is
  `c.plus a` (`porf` does not depend on the coherence place of `a`,
  `Graph.porf_addWrite_wp`).
* Line 16 read literally puts `a` itself into `Deleted`. We follow Def. A.6:
  the deleted events are events of the graph before `a`.
* Lines 24-27: `Previous` consists of events of the graph before `a`, and of
  `init`. Co-maximality (line 27) is among the writes of the location of the
  event (`coRelAt`).
* Line 22: the coherence predecessor of `a` is a write of the graph that
  remains after the deletion (or `init`), not `a` itself.
* The consistency check of line 4 is a premise of every rule, on the graph
  the step starts from (`Visit` returns at once on an inconsistent graph) and
  on the new graph (Def. A.2: the call produced must pass the check). On
  reached configurations the first is redundant. Coq's `TruSt_step` checks
  the new graph only.
* Well-formedness of the new graph is not a premise: it is proved
  (`StepL.wf`). The paper's proofs obtain that `rf` is total from consistency
  (proof of Lemma A.20); here it follows for a revisit from line 25, which
  forbids deleting the source of a read that is kept (`Config.keep_sources`).
* Coq's `IsMaximal` omits line 25; there it follows from line 27 and from
  consistency implying that `rf` is total. We keep the paper's line.
* Section 3.4 and Def. 3.3 speak of a graph that already contains the
  revisiting write and count it among the events that must be maximally
  added. Algorithm 1 with Def. A.6 tests the deleted events and the revisited
  read only, and then tries every coherence place for the new write (line
  22). The rule follows Algorithm 1: there is no maximality premise on the new
  write.
-/

namespace Trust

namespace Config

/-- The initial configuration: no thread event. (`G_∅`, Algorithm 1, line 2.) -/
def init (μ : Loc → Val) : Config := ⟨μ, [], fun _ => none, fun _ => []⟩

/-- `a` was added before `b` (`a <_G b` on thread events). The order list is
newest first. -/
def lt (c : Config) (a b : TEv) : Prop := c.order.Before b a

/-- `a ≤_G b` on thread events. -/
def le (c : Config) (a b : TEv) : Prop := a = b ∨ c.lt a b

/-- The insertion order extends the program order. -/
def PoLt (c : Config) : Prop :=
  ∀ a ∈ c.order, ∀ b ∈ c.order, a.tid = b.tid → a.idx < b.idx → c.lt a b

/-- Add the read `e` with source `w`, as the newest event. -/
def addRead (c : Config) (e : TEv) (w : Ev) : Config :=
  ⟨c.mem, e :: c.order, (c.abs.addRead e w).rf, (c.abs.addRead e w).co⟩

/-- Add the write `e` after `wp` in coherence, as the newest event. -/
def addWrite (c : Config) (e : TEv) (wp : Ev) : Config :=
  ⟨c.mem, e :: c.order, (c.abs.addWrite e wp).rf, (c.abs.addWrite e wp).co⟩

/-- The paper's `G + w` for a new write `w`, used only for `porf`. -/
def plus (c : Config) (w : TEv) : Graph := c.abs.addWrite w .init

/-- `d` is deleted when the new write `w` revisits the read `r` (Def. A.6):
`d` was added after `r` and is not causally before `w`. -/
def Deleted (c : Config) (r w d : TEv) : Prop :=
  d ∈ c.order ∧ c.lt r d ∧ ¬ (c.plus w).porf (.th d) (.th w)

/-- The events that remain when `w` revisits `r`. -/
noncomputable def keep (c : Config) (r w : TEv) : Finset TEv :=
  open Classical in c.order.toFinset.filter (fun d => ¬ c.Deleted r w d)

/-- `Previous_G(e, w)` (Section 3.4; Algorithm 1, line 24): the events added
before `e`, `e` itself, and the events causally before `w`. -/
def Previous (c : Config) (e w : TEv) : Ev → Prop
  | .init => True
  | .th q => q ∈ c.order ∧ (c.le q e ∨ (c.plus w).porf (.th q) (.th w))

/-- `IsMaximallyAdded(G, e, w)` (Algorithm 1, lines 23-27; Section 3.4, "`e` is
maximally added before `w`"): no read of `Previous` reads from `e` (line 25),
and the write `e`, or the source of the read `e`, is in `Previous` and
coherence-maximal there among the writes of its location (lines 26-27). -/
def IsMaximallyAdded (c : Config) (e w : TEv) : Prop :=
  (¬ ∃ q, c.Previous e w (.th q) ∧ c.rf q = some (.th e)) ∧
  ∃ e' : Ev,
    (match e.act with
      | .read _ => c.rf e = some e'
      | .write _ _ => e' = .th e) ∧
    c.Previous e w e' ∧ ¬ ∃ w', c.Previous e w w' ∧ c.abs.coRelAt e.loc e' w'

/-- The configuration after `w` revisits `r`: the deleted events are removed,
`w` is added after `wp` in coherence as the newest event, and `r` reads from
`w` (Algorithm 1, line 18 with line 22). -/
noncomputable def revisit (c : Config) (r w : TEv) (wp : Ev) : Config :=
  let G' := ((c.abs.restrict (c.keep r w)).addWrite w wp).setRF r (.th w)
  ⟨c.mem, w :: c.order.filter (fun d => decide (d ∈ c.keep r w)), G'.rf, G'.co⟩

end Config

/-- The kind of a step (Def. A.3): a plain addition, or a revisit of a read. -/
inductive Kind
  | nr
  | rv (r : TEv)

/-- A step of Algorithm 1, labelled with the added event and the kind of the
step (Def. A.2, A.3). -/
inductive StepL (P : Program) (M : Model) : Config → TEv → Kind → Config → Prop
  /-- lines 10-12 -/
  | read {c : Config} {e : TEv} {x : Loc} {w : Ev} :
      M.cons c.abs → P.IsNext c.abs e → e.act = .read x → c.abs.IsWriteTo x w →
      M.cons (c.addRead e w).abs → StepL P M c e .nr (c.addRead e w)
  /-- lines 13-14 and 21-22 -/
  | write {c : Config} {e : TEv} {wp : Ev} :
      M.cons c.abs → P.IsNext c.abs e → e.IsWrite → c.abs.IsWriteTo e.loc wp →
      M.cons (c.addWrite e wp).abs → StepL P M c e .nr (c.addWrite e wp)
  /-- lines 15-18 and 21-22 -/
  | revisit {c : Config} {w r : TEv} {wp : Ev} :
      M.cons c.abs → P.IsNext c.abs w → w.IsWrite → r ∈ c.order → r.act = .read w.loc →
      ¬ (c.plus w).porf (.th r) (.th w) →
      (∀ e, (c.Deleted r w e ∨ e = r) → c.IsMaximallyAdded e w) →
      (c.abs.restrict (c.keep r w)).IsWriteTo w.loc wp →
      M.cons (c.revisit r w wp).abs → StepL P M c w (.rv r) (c.revisit r w wp)

/-- A step of Algorithm 1 (Def. A.2). -/
def Step (P : Program) (M : Model) (c c' : Config) : Prop := ∃ e k, StepL P M c e k c'

/-- The configurations that Algorithm 1 reaches from the initial one. -/
def Reach (P : Program) (M : Model) (c : Config) : Prop :=
  Relation.ReflTransGen (Step P M) (Config.init P.mem) c

/-! ### Statements: the graphs of the new configurations -/

namespace Config

@[simp] theorem init_abs (μ : Loc → Val) : (init μ).abs = Graph.init μ := by
  apply Graph.ext <;> simp [init, Config.abs, Graph.init]

theorem addRead_abs (c : Config) (e : TEv) (w : Ev) :
    (c.addRead e w).abs = c.abs.addRead e w := by
  apply Graph.ext
  · rfl
  · simp [addRead, Config.abs]
  · rfl
  · rfl

theorem addWrite_abs (c : Config) (e : TEv) (wp : Ev) :
    (c.addWrite e wp).abs = c.abs.addWrite e wp := by
  apply Graph.ext
  · rfl
  · simp [addWrite, Config.abs]
  · rfl
  · rfl

theorem revisit_abs (c : Config) (r w : TEv) (wp : Ev) :
    (c.revisit r w wp).abs =
      ((c.abs.restrict (c.keep r w)).addWrite w wp).setRF r (.th w) := by
  apply Graph.ext
  · rfl
  · ext d
    simp only [revisit, Config.abs, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
      List.mem_filter, decide_eq_true_eq, Graph.setRF_events, Graph.addWrite_events,
      Graph.restrict_events, Finset.mem_inter]
  · rfl
  · rfl

theorem mem_keep_iff (c : Config) (r w d : TEv) :
    d ∈ c.keep r w ↔ d ∈ c.order ∧ ¬ c.Deleted r w d := by
  classical
  simp [keep, Finset.mem_filter, List.mem_toFinset]

/-- The initial configuration is well-formed and its order extends `po`. -/
theorem init_wf (μ : Loc → Val) : (init μ).Wf := by
  refine ⟨?_, List.nodup_nil⟩
  rw [init_abs]
  exact Graph.init_wf μ

theorem init_poLt (μ : Loc → Val) : (init μ).PoLt := by
  intro a ha
  cases ha

end Config

/-! ### Statements: what a revisit keeps

For a revisit of `r` by `w` in a well-formed configuration whose insertion
order extends `po`. -/

section Revisit

variable {P : Program} {M : Model} {c : Config} {r w : TEv}

/-- The revisited read is kept. -/
theorem Config.mem_keep_self (hr : r ∈ c.order) : r ∈ c.keep r w := by
  rw [Config.mem_keep_iff]
  exact ⟨hr, fun h => List.Before.irrefl _ _ h.2.1⟩

/-- The events causally before `w` are kept. -/
theorem Config.mem_keep_of_porf {q : TEv} (hq : q ∈ c.order)
    (h : (c.plus w).porf (.th q) (.th w)) : q ∈ c.keep r w := by
  rw [Config.mem_keep_iff]
  exact ⟨hq, fun hd => hd.2.2 h⟩

/-- The kept events are closed under program order. -/
theorem Config.keep_po_closed (hpo : c.PoLt) :
    Maz.PrefixClosed c.abs.po (Graph.evSet (c.abs.events ∩ c.keep r w)) := by
  intro a b hab hb
  cases a with
  | init => trivial
  | th q' =>
    cases b with
    | init => exact absurd hab (by simp [Graph.po])
    | th q =>
      obtain ⟨hq'm, hqm, ht, hi⟩ := hab
      have hb' : q ∈ c.abs.events ∩ c.keep r w := hb
      have hqk : q ∈ c.keep r w := (Finset.mem_inter.mp hb').2
      have hq'o : q' ∈ c.order := List.mem_toFinset.mp hq'm
      have hqo : q ∈ c.order := List.mem_toFinset.mp hqm
      refine Finset.mem_inter.mpr ⟨hq'm, ?_⟩
      rw [Config.mem_keep_iff]
      refine ⟨hq'o, fun hd => ?_⟩
      have hnd : ¬ c.Deleted r w q := ((Config.mem_keep_iff c r w q).mp hqk).2
      by_cases hpf : (c.plus w).porf (.th q) (.th w)
      · -- `q'` is program-order before `q`, hence causally before `w`
        have hstep : (c.plus w).porfStep (.th q') (.th q) :=
          Or.inl ⟨Finset.mem_insert_of_mem hq'm, Finset.mem_insert_of_mem hqm, ht, hi⟩
        exact hd.2.2 (Relation.TransGen.head hstep hpf)
      · -- `q` was not added after `r`, and `q'` was added before `q`
        have hlt : c.lt q' q := hpo q' hq'o q hqo ht hi
        exact hnd ⟨hqo, List.Before.trans hlt hd.2.1, hpf⟩

/-- Line 25 of Algorithm 1: if every deleted event is maximally added, the
source of every kept read is kept. This includes the revisited read `r`: if
its source `s` were deleted, then `r <_G s`, so `r` is in `Previous(s, w)` and
reads from `s`, against line 25 for `s`. -/
theorem Config.keep_sources (hc : c.Wf)
    (hmax : ∀ e, c.Deleted r w e → c.IsMaximallyAdded e w)
    {q : TEv} (hq : q ∈ c.abs.events ∩ c.keep r w) {s : Ev} (hs : c.abs.rf q = some s) :
    s ∈ Graph.evSet (c.keep r w) := by
  cases s with
  | init => trivial
  | th s0 =>
    have hqo : q ∈ c.order := List.mem_toFinset.mp (Finset.mem_inter.mp hq).1
    have hs0 : s0 ∈ c.order := List.mem_toFinset.mp (hc.1.rf_source_mem hs).2
    have hnd : ¬ c.Deleted r w q := ((Config.mem_keep_iff c r w q).mp (Finset.mem_inter.mp hq).2).2
    change s0 ∈ c.keep r w
    rw [Config.mem_keep_iff]
    refine ⟨hs0, fun hd => ?_⟩
    -- line 25 for the deleted `s0`: no read of `Previous(s0, w)` reads from it
    refine (hmax s0 hd).1 ⟨q, ⟨hqo, ?_⟩, hs⟩
    by_cases hpf : (c.plus w).porf (.th q) (.th w)
    · exact Or.inr hpf
    · left
      have hnlt : ¬ c.lt r q := fun h => hnd ⟨hqo, h, hpf⟩
      have hr : r ∈ c.order := hd.2.1.2.1
      by_cases hqr : q = r
      · exact Or.inr (hqr ▸ hd.2.1)
      · rcases List.Before.total hqo hr hqr with h | h
        · exact absurd h hnlt
        · exact Or.inr (List.Before.trans hd.2.1 h)

/-- No kept event of the thread of `r` is after `r`. -/
theorem Config.keep_last (hpo : c.PoLt) (hr : r ∈ c.order) (hnp : ¬ (c.plus w).porf (.th r) (.th w))
    {q : TEv} (hq : q ∈ c.keep r w) (ht : q.tid = r.tid) : q.idx ≤ r.idx := by
  by_contra hlt
  have hqo : q ∈ c.order := ((Config.mem_keep_iff c r w q).mp hq).1
  have hnd : ¬ c.Deleted r w q := ((Config.mem_keep_iff c r w q).mp hq).2
  have hrq : c.lt r q := hpo r hr q hqo ht.symm (by omega)
  by_cases hpf : (c.plus w).porf (.th q) (.th w)
  · have hstep : (c.plus w).porfStep (.th r) (.th q) :=
      Or.inl ⟨Finset.mem_insert_of_mem (List.mem_toFinset.mpr hr),
        Finset.mem_insert_of_mem (List.mem_toFinset.mpr hqo), ht.symm, by omega⟩
    exact hnp (Relation.TransGen.head hstep hpf)
  · exact hnd ⟨hqo, hrq, hpf⟩

/-- All events of the thread of `w` are kept. -/
theorem Config.keep_thread (hc : c.Wf) (hidx : w.idx = c.abs.cnt w.tid)
    {q : TEv} (hq : q ∈ c.order) (ht : q.tid = w.tid) : q ∈ c.keep r w := by
  refine Config.mem_keep_of_porf hq (Relation.TransGen.single (Or.inl ?_))
  have hqm : q ∈ c.abs.events := List.mem_toFinset.mpr hq
  have hlt := hc.1.idx_lt_cnt hqm
  rw [ht, ← hidx] at hlt
  exact ⟨Finset.mem_insert_of_mem hqm, Finset.mem_insert_self _ _, ht, hlt⟩

/-- The graph that remains after the deletion is well-formed. -/
theorem Config.restrict_keep_wf (hc : c.Wf) (hpo : c.PoLt)
    (hmax : ∀ e, c.Deleted r w e → c.IsMaximallyAdded e w) :
    (c.abs.restrict (c.keep r w)).Wf :=
  hc.1.restrict_of_sources (Config.keep_po_closed hpo)
    (fun _ hq _ hs => Config.keep_sources hc hmax hq hs)

/-- The deletion does not change the number of events of the thread of `w`. -/
theorem Config.cnt_restrict_keep (hc : c.Wf) (hidx : w.idx = c.abs.cnt w.tid) :
    (c.abs.restrict (c.keep r w)).cnt w.tid = c.abs.cnt w.tid :=
  Graph.cnt_restrict _ (fun _ hq ht => Config.keep_thread hc hidx (List.mem_toFinset.mp hq) ht)

/-- The configuration after a revisit is well-formed. -/
theorem Config.revisit_wf (hc : c.Wf) (hpo : c.PoLt) {wp : Ev}
    (hidx : w.idx = c.abs.cnt w.tid) (hw : w.IsWrite) (hr : r ∈ c.order)
    (hract : r.act = .read w.loc)
    (hmax : ∀ e, c.Deleted r w e → c.IsMaximallyAdded e w)
    (hwp : (c.abs.restrict (c.keep r w)).IsWriteTo w.loc wp) : (c.revisit r w wp).Wf := by
  have hwo : w ∉ c.order := fun hm =>
    hc.1.not_mem_of_idx_eq_cnt hidx (List.mem_toFinset.mpr hm)
  have hR := Config.restrict_keep_wf hc hpo hmax
  have hidx' : w.idx = (c.abs.restrict (c.keep r w)).cnt w.tid := by
    rw [Config.cnt_restrict_keep hc hidx]
    exact hidx
  have hA := hR.addWrite hidx' hw hwp
  obtain ⟨v, hv⟩ := hw.exists_act
  refine ⟨?_, List.nodup_cons.mpr ⟨fun hm => hwo (List.mem_filter.mp hm).1, hc.2.filter _⟩⟩
  rw [Config.revisit_abs]
  refine (hA.wfExcept r).setRF ?_ hract ⟨Finset.mem_insert_self _ _, v, hv⟩
  exact Finset.mem_insert_of_mem
    (Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hr, Config.mem_keep_self hr⟩)

/-- Adding the next event of a thread on top of a sublist of the order keeps
the insertion order an extension of the program order. -/
theorem Config.poLt_cons (hc : c.Wf) (hpo : c.PoLt) {e : TEv} (hidx : e.idx = c.abs.cnt e.tid)
    (l' : List TEv) (hsub : ∀ a ∈ l', a ∈ c.order)
    (hbef : ∀ a ∈ l', ∀ b ∈ l', c.order.Before b a → l'.Before b a) :
    ∀ a ∈ e :: l', ∀ b ∈ e :: l', a.tid = b.tid → a.idx < b.idx → (e :: l').Before b a := by
  have he : e ∉ c.order := fun hm =>
    hc.1.not_mem_of_idx_eq_cnt hidx (List.mem_toFinset.mpr hm)
  have he' : e ∉ l' := fun h => he (hsub e h)
  intro a ha b hb ht hi
  rcases List.mem_cons.mp ha with hae | ha' <;> rcases List.mem_cons.mp hb with hbe | hb'
  · rw [hae, hbe] at hi
    exact absurd hi (Nat.lt_irrefl _)
  · have hlt := hc.1.idx_lt_cnt (List.mem_toFinset.mpr (hsub b hb'))
    rw [hae] at ht hi
    rw [← ht] at hlt
    omega
  · rw [hbe]
    exact List.before_cons_self ha' (fun h => he' (h ▸ ha'))
  · exact List.before_cons_of_before he'
      (hbef a ha' b hb' (hpo a (hsub a ha') b (hsub b hb') ht hi))

end Revisit

/-! ### Statements: soundness

Every reached configuration is well-formed, consistent, and its graph is an
execution of the program (Section 4.3 of the paper: soundness). -/

section Sound

variable {P : Program} {M : Model}

/-- The configuration after a revisit is an execution of the program. -/
theorem Config.revisit_exec {c : Config} {r w : TEv} {wp : Ev} (hc : c.Wf) (hpo : c.PoLt)
    (hE : P.Exec c.abs) (hav : w ∈ P.avail c.abs) (hw : w.IsWrite) (hr : r ∈ c.order)
    (hnp : ¬ (c.plus w).porf (.th r) (.th w))
    (hmax : ∀ e, c.Deleted r w e → c.IsMaximallyAdded e w)
    (hwp : (c.abs.restrict (c.keep r w)).IsWriteTo w.loc wp) :
    P.Exec (c.revisit r w wp).abs := by
  obtain ⟨htid, hidx, hstep⟩ := Program.mem_avail_iff.mp hav
  have hR := Config.restrict_keep_wf hc hpo hmax
  have hcnt := Config.cnt_restrict_keep (r := r) hc hidx
  -- the restriction is an execution
  have hER : P.Exec (c.abs.restrict (c.keep r w)) :=
    hE.restrict_except hc.1 (r := r) (Config.keep_po_closed hpo)
      (fun _ hq _ _ hs => Config.keep_sources hc hmax hq hs)
      (fun _ hq ht => Config.keep_last hpo hr hnp (Finset.mem_inter.mp hq).2 ht)
  -- the new write is available in the restriction: its thread is untouched
  have htr : (c.abs.restrict (c.keep r w)).trace w.tid = c.abs.trace w.tid := by
    unfold Graph.trace
    rw [hcnt]
    refine Graph.traceBefore_restrict_of_keep hc.1 (le_refl _) ?_ ?_
    · intro q hq ht _
      exact Config.keep_thread hc hidx (List.mem_toFinset.mp hq) ht
    · intro q hq ht _ s hs
      exact Config.keep_sources hc hmax (Finset.mem_inter.mpr
        ⟨hq, Config.keep_thread hc hidx (List.mem_toFinset.mp hq) ht⟩) hs
  have hav' : w ∈ P.avail (c.abs.restrict (c.keep r w)) :=
    Program.mem_avail_iff.mpr ⟨htid, by rw [hcnt]; exact hidx, by rw [htr]; exact hstep⟩
  have hEA := hER.addWrite hR hav' hw hwp
  rw [Config.revisit_abs]
  refine hEA.setRF ?_
  intro q hq ht
  rcases Finset.mem_insert.mp hq with hqw | hq'
  · -- `w` is not in the thread of `r`: otherwise `r` would be causally before `w`
    exfalso
    rw [hqw] at ht
    have hrm : r ∈ c.abs.events := List.mem_toFinset.mpr hr
    have hlt := hc.1.idx_lt_cnt hrm
    rw [← ht, ← hidx] at hlt
    exact hnp (Relation.TransGen.single (Or.inl
      ⟨Finset.mem_insert_of_mem hrm, Finset.mem_insert_self _ _, ht.symm, hlt⟩))
  · exact Config.keep_last hpo hr hnp (Finset.mem_inter.mp hq').2 ht

/-- The added event is new and becomes the newest event. -/
theorem StepL.order {c c' : Config} {e : TEv} {k : Kind} (hc : c.Wf)
    (h : StepL P M c e k c') : e ∉ c.order ∧ c'.order.head? = some e := by
  have key : ∀ e, P.IsNext c.abs e → e ∉ c.order := fun e he hm =>
    Program.not_mem_of_mem_avail hc.1 he.1 (List.mem_toFinset.mpr hm)
  cases h with
  | read _ h1 _ _ _ => exact ⟨key _ h1, rfl⟩
  | write _ h1 _ _ _ => exact ⟨key _ h1, rfl⟩
  | revisit _ h1 _ _ _ _ _ _ _ => exact ⟨key _ h1, rfl⟩

/-- A step keeps the initial memory. -/
theorem StepL.mem {c c' : Config} {e : TEv} {k : Kind} (h : StepL P M c e k c') :
    c'.mem = c.mem := by
  cases h <;> rfl

/-- A step preserves well-formedness. For a revisit this uses line 25. -/
theorem StepL.wf {c c' : Config} {e : TEv} {k : Kind} (hc : c.Wf) (hpo : c.PoLt)
    (h : StepL P M c e k c') : c'.Wf := by
  cases h with
  | read _ h1 h2 h3 _ =>
    have hidx := Program.idx_eq_of_mem_avail h1.1
    refine ⟨?_, List.nodup_cons.mpr ⟨fun hm =>
      hc.1.not_mem_of_idx_eq_cnt hidx (List.mem_toFinset.mpr hm), hc.2⟩⟩
    rw [Config.addRead_abs]
    exact hc.1.addRead hidx h2 h3
  | write _ h1 h2 h3 _ =>
    have hidx := Program.idx_eq_of_mem_avail h1.1
    refine ⟨?_, List.nodup_cons.mpr ⟨fun hm =>
      hc.1.not_mem_of_idx_eq_cnt hidx (List.mem_toFinset.mpr hm), hc.2⟩⟩
    rw [Config.addWrite_abs]
    exact hc.1.addWrite hidx h2 h3
  | revisit _ h1 h2 h3 h4 _ h6 h7 _ =>
    exact Config.revisit_wf hc hpo (Program.idx_eq_of_mem_avail h1.1) h2 h3 h4
      (fun e he => h6 e (Or.inl he)) h7

/-- A step preserves that the insertion order extends the program order. -/
theorem StepL.poLt {c c' : Config} {e : TEv} {k : Kind} (hc : c.Wf) (hpo : c.PoLt)
    (h : StepL P M c e k c') : c'.PoLt := by
  cases h with
  | read _ h1 _ _ _ =>
    exact Config.poLt_cons hc hpo (Program.idx_eq_of_mem_avail h1.1) c.order
      (fun _ h => h) (fun _ _ _ _ h => h)
  | write _ h1 _ _ _ =>
    exact Config.poLt_cons hc hpo (Program.idx_eq_of_mem_avail h1.1) c.order
      (fun _ h => h) (fun _ _ _ _ h => h)
  | revisit _ h1 _ _ _ _ _ _ _ =>
    exact Config.poLt_cons hc hpo (Program.idx_eq_of_mem_avail h1.1) _
      (fun _ h => (List.mem_filter.mp h).1)
      (fun _ ha _ hb h => List.before_filter_iff.mpr
        ⟨h, (List.mem_filter.mp hb).2, (List.mem_filter.mp ha).2⟩)

/-- The graph after a step is consistent (line 4). -/
theorem StepL.cons {c c' : Config} {e : TEv} {k : Kind} (h : StepL P M c e k c') :
    M.cons c'.abs := by
  cases h <;> assumption

/-- A step preserves being an execution of the program. -/
theorem StepL.exec {c c' : Config} {e : TEv} {k : Kind} (hc : c.Wf) (hpo : c.PoLt)
    (hE : P.Exec c.abs) (h : StepL P M c e k c') : P.Exec c'.abs := by
  cases h with
  | read _ h1 h2 h3 _ =>
    rw [Config.addRead_abs]
    exact hE.addRead hc.1 h1.1 h2 h3
  | write _ h1 h2 h3 _ =>
    rw [Config.addWrite_abs]
    exact hE.addWrite hc.1 h1.1 h2 h3
  | revisit _ h1 h2 h3 _ h5 h6 h7 _ =>
    exact Config.revisit_exec hc hpo hE h1.1 h2 h3 h5 (fun e he => h6 e (Or.inl he)) h7

/-- Inversion of a revisit step. -/
theorem StepL.rv_inv {c c' : Config} {e r : TEv} (h : StepL P M c e (.rv r) c') :
    ∃ wp, c' = c.revisit r e wp ∧ M.cons c.abs ∧ P.IsNext c.abs e ∧ e.IsWrite ∧ r ∈ c.order ∧
      r.act = .read e.loc ∧ ¬ (c.plus e).porf (.th r) (.th e) ∧
      (∀ x, (c.Deleted r e x ∨ x = r) → c.IsMaximallyAdded x e) ∧
      (c.abs.restrict (c.keep r e)).IsWriteTo e.loc wp := by
  cases h with
  | revisit h0 h1 h2 h3 h4 h5 h6 h7 h8 => exact ⟨_, rfl, h0, h1, h2, h3, h4, h5, h6, h7⟩

/-- Inversion of a step that is not a revisit. -/
theorem StepL.nr_inv {c c' : Config} {e : TEv} (h : StepL P M c e .nr c') :
    M.cons c.abs ∧ P.IsNext c.abs e ∧
      ((∃ x w, e.act = .read x ∧ c.abs.IsWriteTo x w ∧ c' = c.addRead e w) ∨
       (∃ wp, e.IsWrite ∧ c.abs.IsWriteTo e.loc wp ∧ c' = c.addWrite e wp)) := by
  cases h with
  | read h0 h1 h2 h3 h4 => exact ⟨h0, h1, Or.inl ⟨_, _, h2, h3, rfl⟩⟩
  | write h0 h1 h2 h3 h4 => exact ⟨h0, h1, Or.inr ⟨_, h2, h3, rfl⟩⟩

/-- Soundness: every reached configuration is well-formed, its insertion order
extends the program order, and its graph is a consistent execution of the
program. -/
theorem Reach.sound {c : Config} (h : Reach P M c) :
    c.Wf ∧ c.PoLt ∧ M.cons c.abs ∧ P.Exec c.abs := by
  unfold Reach at h
  induction h with
  | refl =>
    refine ⟨Config.init_wf _, Config.init_poLt _, ?_, ?_⟩
    · rw [Config.init_abs]
      exact M.cons_init _
    · rw [Config.init_abs]
      exact Program.exec_init P
  | tail _ hs ih =>
    obtain ⟨hw, hpo, _, hE⟩ := ih
    obtain ⟨e, k, hs⟩ := hs
    exact ⟨hs.wf hw hpo, hs.poLt hw hpo, hs.cons, hs.exec hw hpo hE⟩

/-- The graphs that Algorithm 1 reports (line 7: no next event) are
well-formed, consistent, full executions of the program. -/
theorem Reach.sound_full {c : Config} (h : Reach P M c) (hf : P.Full c.abs) :
    c.abs.Wf ∧ P.Exec c.abs ∧ M.cons c.abs ∧ P.Full c.abs := by
  obtain ⟨hw, _, hc, hE⟩ := h.sound
  exact ⟨hw.1, hE, hc, hf⟩

/-- The reported graphs in the form of `ass:trust`(2) of `dpor.tex`:
consistent, built for the program, with no available event. -/
theorem Reach.sound_built_full {c : Config} (h : Reach P M c) (hf : P.Full c.abs) :
    M.cons c.abs ∧ P.Built c.abs ∧ P.Full c.abs := by
  obtain ⟨hw, _, hc, hE⟩ := h.sound
  exact ⟨hc, hE.built hw.1 (M.porf_acyclic _ hw.1 hc), hf⟩

end Sound

end Trust
