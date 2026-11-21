import Mazurkiewicz.Induction.States
import Mathlib.Basic.Finite.Prod

/-!
# The interleaving semantics

`induction-popl`, `concepts.tex` sec:sc: def:op, prop:bisim, cor:op (1), (3),
for plain programs.

How the text is read here.

* `Conf_P` is `Conf P`: a local state for every thread identifier and a
  memory. A thread identifier outside `P.threads` has the state of the empty
  trace in every reachable configuration, and no action there.
* def:op: the rows for write and read actions. `OpStep P t c c'`.
* `h(G)` is `conf P G`: the classes of the traces and the memory `mem_G`.
* prop:bisim: `conf_init`, `MStep.opStep`, `exists_mstep_of_opStep`.
* cor:op (1): `conf_reach`. cor:op (2) is about error actions (plan,
  Section 2). cor:op (3): `opReach_finite`; "finite-state" is asked of the
  listed threads only.
* The facts on a maximal step that the proof of prop:bisim computes are
  `MStep.trace` and `MStep.memOf`.
* The proof of cor:op (3): the listed threads have finitely many states,
  hence finitely many actions; a reachable memory differs from `P.mem` only
  at a location of one of these actions, where it has the initial value or
  the value of a write action among them. No finiteness of `Loc`, `Val` or
  of the image of `P.mem` is needed.
-/

namespace Trust

open Program

variable {P : Program}

/-- The configurations `Conf_P` (def:op). -/
abbrev Conf (P : Program) : Type := ((t : Tid) → St (P.step t)) × (Loc → Val)

/-- The initial configuration `c₀` (def:op). -/
def conf₀ (P : Program) : Conf P := (fun t => St.mk (P.step t) [], P.mem)

/-- The configuration `h(G)` of a graph (def:op). -/
noncomputable def conf (P : Program) (G : Graph) : Conf P :=
  (fun t => St.mk (P.step t) (G.trace t), G.memOf)

/-- A transition `c →ᵗ c'` of the interleaving semantics (def:op). -/
def OpStep (P : Program) (t : Tid) (c c' : Conf P) : Prop :=
  ∃ a, (c.1 t).act = some a ∧
    match a with
    | .write x v => c' = (Function.update c.1 t ((c.1 t).app none), Function.update c.2 x v)
    | .read x => c' = (Function.update c.1 t ((c.1 t).app (some (c.2 x))), c.2)

/-- The configurations reachable from `c₀`. -/
def OpReach (P : Program) (c : Conf P) : Prop :=
  Relation.ReflTransGen (fun c c' => ∃ t, OpStep P t c c') (conf₀ P) c

/-! ### Traces of threads outside the program -/

/-- A thread that is not listed has no event in an execution. -/
theorem ExecSC.cnt_of_not_mem {G : Graph} (hG : ExecSC P G) {t : Tid} (ht : t ∉ P.threads) :
    G.cnt t = 0 := by
  by_contra h
  obtain ⟨e, he, het, -⟩ := (hG.1.exists_idx_iff t 0).mpr (Nat.pos_of_ne_zero h)
  exact ht (het ▸ hG.2.1.tid_mem hG.1 he)

theorem ExecSC.trace_of_not_mem {G : Graph} (hG : ExecSC P G) {t : Tid} (ht : t ∉ P.threads) :
    G.trace t = [] := by
  unfold Graph.trace
  rw [hG.cnt_of_not_mem ht]
  rfl

/-- Two graphs have the same configuration iff their traces are
future-equivalent and their memories are equal. -/
theorem conf_eq_iff {G G' : Graph} :
    conf P G = conf P G' ↔
      (∀ t, FutEq (P.step t) (G.trace t) (G'.trace t)) ∧ G.memOf = G'.memOf := by
  constructor
  · intro h
    exact ⟨fun t => St.mk_eq_mk.mp (congrFun (congrArg Prod.fst h) t), congrArg Prod.snd h⟩
  · rintro ⟨h1, h2⟩
    exact Prod.ext (funext fun t => St.mk_eq_mk.mpr (h1 t)) h2

/-- For consistent executions it is enough to compare the listed threads. -/
theorem conf_eq_iff_threads {G G' : Graph} (hG : ExecSC P G) (hG' : ExecSC P G') :
    conf P G = conf P G' ↔
      (∀ t ∈ P.threads, FutEq (P.step t) (G.trace t) (G'.trace t)) ∧ G.memOf = G'.memOf := by
  rw [conf_eq_iff]
  refine and_congr ⟨fun h t _ => h t, fun h t => ?_⟩ Iff.rfl
  by_cases ht : t ∈ P.threads
  · exact h t ht
  · rw [hG.trace_of_not_mem ht, hG'.trace_of_not_mem ht]
    exact (futEq_equivalence _).refl _

/-! ### A maximal step, computed -/

/-- The traces after a maximal step of `t` with action `a`: the trace of `t`
gets the value returned by the new event, a read of `x` returns `mem_G(x)`. -/
theorem MStep.trace {t : Tid} {G G' : Graph} (h : MStep P t G G') {a : Act}
    (ha : P.step t (G.trace t) = some a) (t' : Tid) :
    G'.trace t' =
      if t' = t then
        G.trace t ++ [match a with
          | .read x => some (G.memOf x)
          | .write _ _ => none]
      else G.trace t' := by
  have hG := h.execSC_left.1
  obtain ⟨a', -, ha', rfl⟩ := h.new_event
  rw [ha] at ha'
  cases Option.some.inj ha'
  cases a with
  | read x =>
    have hact : (⟨t, G.cnt t, .read x⟩ : TEv).act = .read x := rfl
    rw [Graph.addMax_read hact,
      Graph.trace_addRead hG rfl hact (Graph.maxWrite_isWriteTo hG x) t']
    by_cases htt : t' = t
    · subst htt
      simp [Graph.memOf]
    · simp [htt]
  | write x v =>
    have hw : (⟨t, G.cnt t, .write x v⟩ : TEv).IsWrite := by simp [TEv.IsWrite, Act.IsWrite]
    rw [Graph.addMax_write hw,
      Graph.trace_addWrite hG rfl hw (Graph.maxWrite_isWriteTo hG _) t']
    by_cases htt : t' = t
    · subst htt
      simp
    · simp [htt]

/-- The memory after a maximal step of `t` with action `a`. -/
theorem MStep.memOf {t : Tid} {G G' : Graph} (h : MStep P t G G') {a : Act}
    (ha : P.step t (G.trace t) = some a) :
    G'.memOf =
      match a with
      | .read _ => G.memOf
      | .write x v => Function.update G.memOf x v := by
  have hG := h.execSC_left.1
  obtain ⟨a', -, ha', rfl⟩ := h.new_event
  rw [ha] at ha'
  cases Option.some.inj ha'
  cases a with
  | read x =>
    have hact : (⟨t, G.cnt t, .read x⟩ : TEv).act = .read x := rfl
    rw [Graph.addMax_read hact]
    rfl
  | write x v =>
    have hw : (⟨t, G.cnt t, .write x v⟩ : TEv).IsWrite := by simp [TEv.IsWrite, Act.IsWrite]
    rw [Graph.addMax_write hw]
    change _ = Function.update G.memOf x v
    funext y
    by_cases hy : y = x
    · subst hy
      have hm := Graph.maxWrite_addWrite_maxWrite hG ⟨t, G.cnt t, .write y v⟩
      have hm' : (G.addWrite ⟨t, G.cnt t, .write y v⟩
          (G.maxWrite (⟨t, G.cnt t, .write y v⟩ : TEv).loc)).maxWrite y =
          .th ⟨t, G.cnt t, .write y v⟩ := hm
      simp only [Function.update_self]
      unfold Graph.memOf
      rw [hm']
      rfl
    · have hmw : ∀ wp, (G.addWrite ⟨t, G.cnt t, .write x v⟩ wp).maxWrite y = G.maxWrite y := by
        intro wp
        unfold Graph.maxWrite
        rw [G.addWrite_co_of_ne ⟨t, G.cnt t, .write x v⟩ wp (y := y) hy]
      rw [Function.update_of_ne hy]
      unfold Graph.memOf
      rw [hmw]
      rfl

/-- The number of events of each thread after a maximal step of `t`. -/
theorem MStep.cnt {t : Tid} {G G' : Graph} (h : MStep P t G G') (t' : Tid) :
    G'.cnt t' = if t' = t then G.cnt t + 1 else G.cnt t' := by
  obtain ⟨a, -, ha, -⟩ := h.new_event
  have := congrArg List.length (h.trace ha t')
  rw [Graph.trace_length] at this
  rw [this]
  by_cases htt : t' = t
  · simp [htt, Graph.trace_length]
  · simp [htt, Graph.trace_length]

/-! ### prop:bisim and cor:op -/

/-- prop:bisim: `h(G_init) = c₀`. -/
theorem conf_init (P : Program) : conf P (Graph.init P.mem) = conf₀ P := by
  have hE : ExecSC P (Graph.init P.mem) := ⟨Graph.init_wf _, exec_init P, SC.cons_init _⟩
  refine Prod.ext (funext fun t => ?_) (funext fun x => ?_)
  · change St.mk (P.step t) ((Graph.init P.mem).trace t) = St.mk (P.step t) []
    have h0 : (Graph.init P.mem).cnt t = 0 := by simp [Graph.cnt, Graph.init]
    unfold Graph.trace
    rw [h0]
    rfl
  · rfl

/-- prop:bisim (1). -/
theorem MStep.opStep {t : Tid} {G G' : Graph} (h : MStep P t G G') :
    OpStep P t (conf P G) (conf P G') := by
  obtain ⟨a, -, ha, -⟩ := h.new_event
  have htr := h.trace ha
  have hmem := h.memOf ha
  refine ⟨a, ha, ?_⟩
  cases a with
  | write x v =>
    refine Prod.ext (funext fun t' => ?_) hmem
    change St.mk (P.step t') (G'.trace t') = _
    rw [htr t']
    by_cases htt : t' = t
    · subst htt
      simp [conf]
    · simp [htt, conf]
  | read x =>
    refine Prod.ext (funext fun t' => ?_) hmem
    change St.mk (P.step t') (G'.trace t') = _
    rw [htr t']
    by_cases htt : t' = t
    · subst htt
      simp [conf]
    · simp [htt, conf]

/-- prop:bisim (2). -/
theorem exists_mstep_of_opStep {t : Tid} {G : Graph} (hG : ExecSC P G) {c' : Conf P}
    (h : OpStep P t (conf P G) c') : ∃ G', MStep P t G G' ∧ conf P G' = c' := by
  obtain ⟨a, hact, hc'⟩ := h
  have ha : P.step t (G.trace t) = some a := hact
  have ht : t ∈ P.threads := by
    by_contra ht
    rw [hG.trace_of_not_mem ht, P.step_none t ht] at ha
    cases ha
  obtain ⟨G', hstep, -⟩ := exists_mstep hG ht ha
  refine ⟨G', hstep, ?_⟩
  obtain ⟨a₂, h₂, heq⟩ := hstep.opStep
  have h₂' : P.step t (G.trace t) = some a₂ := h₂
  rw [ha] at h₂'
  cases Option.some.inj h₂'
  cases a with
  | write x v => exact heq.trans hc'.symm
  | read x => exact heq.trans hc'.symm

/-- cor:op (1): the configurations of the reachable graphs are the reachable
configurations. -/
theorem conf_reach (P : Program) (c : Conf P) :
    (∃ G, GReach P SC G ∧ conf P G = c) ↔ OpReach P c := by
  constructor
  · rintro ⟨G, hG, rfl⟩
    have hm := mreach_iff.mpr hG
    induction hm with
    | refl =>
      rw [conf_init]
      exact Relation.ReflTransGen.refl
    | tail hr hs ih =>
      obtain ⟨t, hs⟩ := hs
      exact (ih (mreach_iff.mp hr)).tail ⟨t, hs.opStep⟩
  · intro h
    induction h with
    | refl => exact ⟨Graph.init P.mem, Relation.ReflTransGen.refl, conf_init P⟩
    | tail _ hs ih =>
      obtain ⟨t, hs⟩ := hs
      obtain ⟨G, hG, rfl⟩ := ih
      obtain ⟨G', hstep, hc⟩ := exists_mstep_of_opStep (greach_iff.mp hG) hs
      exact ⟨G', hG.tail hstep.gstep, hc⟩

/-- cor:op (3): if the listed threads are finite-state, there are finitely
many reachable configurations. -/
theorem opReach_finite (P : Program) (hfin : ∀ t ∈ P.threads, Finite (St (P.step t))) :
    {c | OpReach P c}.Finite := by
  classical
  -- the actions of the states of the listed threads
  let A : Set Act := {a | ∃ t ∈ P.threads, ∃ s : St (P.step t), s.act = some a}
  have hA : A.Finite := by
    refine (Set.Finite.biUnion (List.finite_toSet P.threads)
      (t := fun t => {a | ∃ s : St (P.step t), s.act = some a}) (fun t ht => ?_)).subset ?_
    · have := hfin t ht
      exact ((Set.finite_range (fun s : St (P.step t) => s.act)).preimage
        (Option.some_injective _).injOn).subset (fun a ⟨s, hs⟩ => ⟨s, hs⟩)
    · rintro a ⟨t, ht, s, hs⟩
      exact Set.mem_biUnion ht ⟨s, hs⟩
  let L : Set Loc := Act.loc '' A
  have hL : L.Finite := hA.image _
  let wv : Act → Val := fun a =>
    match a with
    | .write _ v => v
    | .read _ => 0
  let V : Set Val := wv '' A ∪ P.mem '' L
  have hV : V.Finite := (hA.image _).union (hL.image _)
  let T : Set Tid := {t | t ∈ P.threads}
  have iT : Finite ↥T := (List.finite_toSet P.threads).to_subtype
  have iL : Finite ↥L := hL.to_subtype
  have iV : Finite ↥V := hV.to_subtype
  have iS : ∀ t : ↥T, Finite (St (P.step t)) := fun t => hfin t t.2
  have i1 : Finite ((t : ↥T) → St (P.step t)) := Pi.finite
  have i2 : Finite (↥L → ↥V) := Pi.finite
  have i3 : Finite (((t : ↥T) → St (P.step t)) × (↥L → ↥V)) := inferInstance
  let F : ((t : ↥T) → St (P.step t)) × (↥L → ↥V) → Conf P := fun sm =>
    (fun t => if h : t ∈ P.threads then sm.1 ⟨t, h⟩ else St.mk (P.step t) [],
     fun x => if h : x ∈ L then (sm.2 ⟨x, h⟩ : Val) else P.mem x)
  refine (Set.finite_range F).subset ?_
  intro c hc
  have inv : (∀ t, t ∉ P.threads → c.1 t = St.mk (P.step t) []) ∧
      (∀ x, c.2 x = P.mem x ∨ Act.write x (c.2 x) ∈ A) := by
    induction hc with
    | refl => exact ⟨fun _ _ => rfl, fun _ => Or.inl rfl⟩
    | @tail c c' _ hs ih =>
      obtain ⟨t, a, hact, hc'⟩ := hs
      obtain ⟨i1, i2⟩ := ih
      have ht : t ∈ P.threads := by
        by_contra ht
        rw [i1 t ht, St.act_mk, P.step_none t ht] at hact
        cases hact
      cases a with
      | write x v =>
        have hc'' : c' = (Function.update c.1 t ((c.1 t).app none), Function.update c.2 x v) :=
          hc'
        subst hc''
        refine ⟨fun t' ht' => ?_, fun y => ?_⟩
        · have hne : t' ≠ t := fun h => ht' (h ▸ ht)
          change Function.update c.1 t ((c.1 t).app none) t' = _
          rw [Function.update_of_ne hne]
          exact i1 t' ht'
        · change Function.update c.2 x v y = P.mem y ∨ Act.write y (Function.update c.2 x v y) ∈ A
          by_cases hy : y = x
          · subst hy
            rw [Function.update_self]
            exact Or.inr ⟨t, ht, c.1 t, hact⟩
          · rw [Function.update_of_ne hy]
            exact i2 y
      | read x =>
        have hc'' : c' = (Function.update c.1 t ((c.1 t).app (some (c.2 x))), c.2) := hc'
        subst hc''
        refine ⟨fun t' ht' => ?_, i2⟩
        have hne : t' ≠ t := fun h => ht' (h ▸ ht)
        change Function.update c.1 t ((c.1 t).app (some (c.2 x))) t' = _
        rw [Function.update_of_ne hne]
        exact i1 t' ht'
  obtain ⟨i1, i2⟩ := inv
  have hmemV : ∀ x : ↥L, c.2 x ∈ V := by
    intro x
    rcases i2 x with h | hv
    · rw [h]
      exact Or.inr ⟨x, x.2, rfl⟩
    · exact Or.inl ⟨_, hv, rfl⟩
  refine ⟨(fun t => c.1 t, fun x => ⟨c.2 x, hmemV x⟩), ?_⟩
  refine Prod.ext (funext fun t => ?_) (funext fun x => ?_)
  · by_cases h : t ∈ P.threads
    · simp [F, h]
    · simp [F, h, i1 t h]
  · by_cases h : x ∈ L
    · simp [F, h]
    · have hx : c.2 x = P.mem x :=
        (i2 x).resolve_right (fun hv => h ⟨_, hv, rfl⟩)
      simp [F, h, hx]

/-! ### Instances -/

namespace Examples

/-- The configuration of the full graph `G3` of the checked run is reachable
in the interleaving semantics. -/
example : OpReach revProg (conf revProg G3) :=
  (conf_reach revProg _).mp
    ⟨G3, greach_iff.mpr ⟨G3_facts.1, G3_facts.2.1, G3_facts.2.2.1⟩, rfl⟩

end Examples

end Trust
