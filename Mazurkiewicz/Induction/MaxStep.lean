import Mazurkiewicz.Induction.Reach

/-!
# Maximal steps and schedule terms

`induction-popl`, `concepts.tex` sec:sc (def:mem, def:maxstep, lem:maxext,
prop:reachmax, cor:full) and sec:terms (def:signature, lem:terms), for plain
programs under SC.

How the text is read here.

* `comax_l(G)` is `G.maxWrite l` of the port; `mem_G` is `Graph.memOf`.
* def:maxstep: `MStep P t G G'` is a step under SC whose new event `e` belongs
  to thread `t`, reads from `comax_l(G)` if it is a read of `l`, and is
  `comax_l(G')` if it is a write to `l`. `MReach P` is `Reachmax(P)`.
* `mstep_iff`: a maximal step by `t` is the maximal extension `G.addMax e` of
  the port by the available event `e` of thread `t`.
* lem:maxext: a plain action is realised by exactly one label, so "for every
  label realising `a` there is exactly one `G'`" is: if thread `t` has a next
  action there is exactly one `G'` (`exists_mstep`, `MStep.unique`), and
  otherwise none (`not_mstep`). Uniqueness is among well-formed graphs, which
  `MStep` contains.
* prop:reachmax is proved by induction on the size, removing an event that is
  maximal for the SC order, instead of fixing a linear extension.
* cor:full: only its first sentence (every reachable graph of a bounded
  program is a prefix of a full reachable graph). The consequence for
  `Bad_err` needs error labels (plan, Section 2).
* def:signature, lem:terms: without choice actions `C_P = {∗}`, and a term
  `(t_n,∗)(…(t_1,∗)(ι))` is the list `[t_n, …, t_1]`. `valt` is its value in
  the graph algebra, `none` when undefined; `Valid_P` is `valt τ ≠ none`.
  The symbols are all of `Tid = ℕ`; a symbol outside `P.threads` has no
  value. `apT` is the unary operation of the algebra, undefined outside
  `Exec_SC(P)` as in def:signature; `MSteps` are the maximal steps along a
  list, and `greach_iff_msteps` says that a reachable graph is reached by
  exactly `|G| - 1` maximal steps.
-/

namespace Trust

open Program

variable {P : Program}

/-- The memory `mem_G` (def:mem): the value of the last write to each
location. -/
def Graph.memOf (G : Graph) (x : Loc) : Val := G.valAt x (G.maxWrite x)

/-- A maximal step `G →ᵗ G'` (def:maxstep). -/
def MStep (P : Program) (t : Tid) (G G' : Graph) : Prop :=
  G.Wf ∧ G'.Wf ∧ ∃ e, e.tid = t ∧ e ∉ G.events ∧ G'.events = insert e G.events ∧
    G = G'.restrict G.events ∧ P.Exec G' ∧ SC.cons G' ∧
    (∀ x, e.act = .read x → G'.rf e = some (G.maxWrite x)) ∧
    (e.IsWrite → G'.maxWrite e.loc = .th e)

/-- `Reachmax(P)` (def:maxstep). -/
def MReach (P : Program) (G : Graph) : Prop :=
  Relation.ReflTransGen (fun G G' => ∃ t, MStep P t G G') (Graph.init P.mem) G

/-- The operation `(t,∗)` of the graph algebra (def:signature): the maximal
step of thread `t` from a graph in `Exec_SC(P)`, undefined otherwise. -/
noncomputable def apT (P : Program) (t : Tid) (G : Graph) : Option Graph :=
  open Classical in
  if ExecSC P G ∧ t ∈ P.threads then (P.nextOf G t).map G.addMax else none

/-- The value of a schedule term in the graph algebra (def:signature): the
head of the list is the thread of the last step. -/
noncomputable def valt (P : Program) : List Tid → Option Graph
  | [] => some (Graph.init P.mem)
  | t :: τ => (valt P τ).bind (apT P t)

/-- `Valid_P` (def:signature): the terms with a value. -/
def Valid (P : Program) (τ : List Tid) : Prop := valt P τ ≠ none

/-- Maximal steps along a list of threads (head = last step). -/
def MSteps (P : Program) : List Tid → Graph → Graph → Prop
  | [], G, G' => G' = G
  | t :: τ, G, G' => ∃ G₁, MSteps P τ G G₁ ∧ MStep P t G₁ G'

/-! ### Auxiliary facts on the last write and on the SC order -/

namespace Graph

/-- A write to `x` other than the last one is coherence-before the last one. -/
theorem coRelAt_maxWrite_of_ne {G : Graph} (hG : G.Wf) {x : Loc} {w : Ev}
    (hw : G.IsWriteTo x w) (hne : w ≠ G.maxWrite x) :
    ∃ m, m ∈ G.co x ∧ G.coRelAt x w (.th m) := by
  revert hne
  unfold maxWrite
  cases h : (G.co x).getLast? with
  | none =>
    intro hne
    have h0 : G.co x = [] := List.getLast?_eq_none_iff.mp h
    cases w with
    | init => exact absurd rfl hne
    | th q =>
      have : q ∈ G.co x := (hG.co_mem x q).mpr hw
      rw [h0] at this
      cases this
  | some m =>
    intro hne
    have hm : m ∈ G.co x := List.mem_of_getLast? h
    refine ⟨m, hm, ?_⟩
    cases w with
    | init => exact hm
    | th q =>
      have hq : q ∈ G.co x := (hG.co_mem x q).mpr hw
      have hqm : q ≠ m := fun h' => hne (by subst h'; rfl)
      have hnel : G.co x ≠ [] := List.ne_nil_of_mem hm
      have hlast : (G.co x).getLast hnel = m := by
        have := List.getLast?_eq_some_getLast hnel
        rw [h] at this
        exact (Option.some.inj this).symm
      rcases List.Before.total hq hm hqm with h1 | h1
      · exact h1
      · have := List.not_before_getLast (hG.co_nodup x) hnel q
        rw [hlast] at this
        exact absurd h1 this

/-- A new write that is not placed after the last write of its location is
coherence-before some old write. -/
theorem addWrite_before_of_ne_max {G : Graph} (hG : G.Wf) {e : TEv} (he : e ∉ G.events)
    {wp : Ev} (hwp : G.IsWriteTo e.loc wp) (hne : wp ≠ G.maxWrite e.loc) :
    ∃ m, m ∈ G.co e.loc ∧ ((G.addWrite e wp).co e.loc).Before e m := by
  obtain ⟨m, hm, hco⟩ := coRelAt_maxWrite_of_ne hG hwp hne
  have hel : e ∉ G.co e.loc := fun h => he ((hG.co_mem _ _).mp h).1
  refine ⟨m, hm, ?_⟩
  rw [addWrite_co_self]
  cases wp with
  | init => exact List.before_cons_self hm (fun h => hel (h ▸ hm))
  | th p => exact (List.before_insertAfter_new_left hco.1 hel).mpr hco

/-- The target of a step of the SC order is a thread event of the graph. -/
theorem scStep_target_mem {G : Graph} (hG : G.Wf) {a b : Ev} (h : G.scStep a b) :
    ∃ q ∈ G.events, b = .th q := by
  rcases h with h | h | h | h
  · have := (hG.mem_of_porfStep (Or.inl h)).2
    cases b with
    | init => cases a <;> exact absurd h (by simp [po])
    | th q => exact ⟨q, this, rfl⟩
  · have := (hG.mem_of_porfStep (Or.inr h)).2
    obtain ⟨q, rfl, -, -⟩ := h
    exact ⟨q, this, rfl⟩
  · cases b with
    | init => cases a <;> exact absurd h (by simp [coRel])
    | th q =>
      refine ⟨q, ?_, rfl⟩
      cases a with
      | init =>
        obtain ⟨z, hz⟩ := h
        exact ((hG.co_mem z q).mp hz).1
      | th p =>
        obtain ⟨z, hz⟩ := h
        exact ((hG.co_mem z q).mp hz.2.1).1
  · obtain ⟨e, e', z, -, rfl, -, -, hco, -⟩ := h
    exact ⟨e', ((hG.co_mem z e').mp hco).1, rfl⟩

end Graph

/-! ### Maximal steps -/



/-- A maximal step is a step under SC. -/
theorem MStep.gstep {t : Tid} {G G' : Graph} (h : MStep P t G G') : GStep P SC G G' := by
  obtain ⟨hG, hG', e, -, he, hev, hres, hE, hc, -, -⟩ := h
  exact ⟨hG, hG', e, he, hev, hres, hE, hc⟩

/-- A maximal step by `t` is the maximal extension by the available event of
thread `t`. -/
theorem mstep_iff {t : Tid} {G G' : Graph} :
    MStep P t G G' ↔ ExecSC P G ∧ ∃ e ∈ P.avail G, e.tid = t ∧ G' = G.addMax e := by
  constructor
  · rintro ⟨hG, hG', e, ht, he, hev, hres, hE, hc, hr, hw⟩
    have hp := isPrefixOf_of_insert hG hG' he hev hres
    obtain ⟨hav, hcase⟩ := step_cases hG hG' he hev hres hE
    refine ⟨⟨hG, hE.of_isPrefixOf hG' hp, SC.prefix_closed G' G hG' hc hp⟩, e, hav, ht, ?_⟩
    rcases hcase with ⟨x, w, hact, -, rfl⟩ | ⟨wp, hew, hwp, rfl⟩
    · have := hr x hact
      rw [Graph.addRead_rf, Function.update_self] at this
      rw [Graph.addMax_read hact, Option.some.inj this]
    · have hwpeq : wp = G.maxWrite e.loc := by
        by_contra hne
        obtain ⟨m, hm, hbef⟩ := Graph.addWrite_before_of_ne_max hG he hwp hne
        have hmG := (hG.co_mem _ m).mp hm
        have := Graph.maxWrite_co_maximal hG' e.loc (w := .th m)
          ⟨Finset.mem_insert_of_mem hmG.1, hmG.2⟩
        rw [hw hew] at this
        exact this ⟨e.loc, hbef⟩
      rw [Graph.addMax_write hew, hwpeq]
  · rintro ⟨⟨hG, hE, hc⟩, e, hav, ht, rfl⟩
    have hidx := idx_eq_of_mem_avail hav
    have he := not_mem_of_mem_avail hG hav
    refine ⟨hG, hG.addMax hidx, e, ht, he, G.addMax_events e,
      (Graph.restrict_addMax hG he).symm, hE.addMax hG hav,
      SC.extensible.cons_addMax hG hc hidx, ?_, ?_⟩
    · intro x hact
      rw [Graph.addMax_read hact, Graph.addRead_rf, Function.update_self]
    · intro hew
      rw [Graph.addMax_write hew]
      exact Graph.maxWrite_addWrite_maxWrite hG e

/-- lem:maxext, uniqueness. -/
theorem MStep.unique {t : Tid} {G G₁ G₂ : Graph} (h₁ : MStep P t G G₁) (h₂ : MStep P t G G₂) :
    G₁ = G₂ := by
  obtain ⟨-, e₁, he₁, ht₁, rfl⟩ := mstep_iff.mp h₁
  obtain ⟨-, e₂, he₂, ht₂, rfl⟩ := mstep_iff.mp h₂
  rw [avail_tid_inj he₁ he₂ (ht₁.trans ht₂.symm)]

/-- lem:maxext, existence. -/
theorem exists_mstep {G : Graph} (hG : ExecSC P G) {t : Tid} (ht : t ∈ P.threads) {a : Act}
    (ha : P.step t (G.trace t) = some a) :
    ∃ G', MStep P t G G' ∧ G'.events = insert ⟨t, G.cnt t, a⟩ G.events := by
  have hav : (⟨t, G.cnt t, a⟩ : TEv) ∈ P.avail G := mem_avail_iff.mpr ⟨ht, rfl, ha⟩
  exact ⟨G.addMax ⟨t, G.cnt t, a⟩, mstep_iff.mpr ⟨hG, _, hav, rfl, rfl⟩, G.addMax_events _⟩

/-- lem:maxext, last sentence. -/
theorem not_mstep {G G' : Graph} {t : Tid} (ha : P.step t (G.trace t) = none) :
    ¬ MStep P t G G' := by
  intro h
  obtain ⟨-, e, he, ht, -⟩ := mstep_iff.mp h
  have := (mem_avail_iff.mp he).2.2
  rw [ht, ha] at this
  cases this

/-- The induction for prop:reachmax: remove an event that is maximal for the SC
order; the step that puts it back is a maximal step. -/
theorem mreach_of_execSC : ∀ (n : ℕ) (G : Graph), G.events.card = n → ExecSC P G →
    MReach P G := by
  classical
  intro n
  induction n with
  | zero =>
    rintro G hcard ⟨hG, hE, -⟩
    have h0 := hG.eq_init_of_events_eq_empty (Finset.card_eq_zero.mp hcard)
    rw [h0, hE.1]
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    rintro G hcard ⟨hG, hE, hc⟩
    have hne : (G.events.image Ev.th).Nonempty := by
      rw [Finset.image_nonempty]
      exact Finset.card_pos.mp (by omega)
    obtain ⟨a, ha, hmax⟩ := Maz.Acyclic.exists_maximal (r := G.scStep) hc _ hne
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    have hsink : ∀ b, ¬ G.scStep (.th e) b := by
      intro b hb
      obtain ⟨q, hq, rfl⟩ := Graph.scStep_target_mem hG hb
      exact hmax _ (Finset.mem_image_of_mem _ hq) hb
    have hp : (G.remove {e}).IsPrefixOf G := by
      refine Graph.remove_isPrefixOf hG (fun q hq b hb => ?_)
      rw [Finset.mem_singleton.mp hq] at hb
      exact absurd (hb.elim Or.inl (fun h => Or.inr (Or.inl h))) (hsink b)
    have hG0 := hG.of_isPrefixOf hp
    have hE0 := hE.of_isPrefixOf hG hp
    have hc0 : SC.cons (G.remove {e}) := SC.prefix_closed G _ hG hc hp
    have hev0 := Graph.remove_singleton_events G e
    have he0 : e ∉ (G.remove {e}).events := by
      rw [hev0]
      exact Finset.notMem_erase e _
    have hev : G.events = insert e (G.remove {e}).events := by
      rw [hev0, Finset.insert_erase he]
    have hres : G.remove {e} = G.restrict (G.remove {e}).events := by
      rw [hev0]
      unfold Graph.remove
      rw [Finset.sdiff_singleton_eq_erase]
    have hcard0 : (G.remove {e}).events.card = n := by
      rw [hev0, Finset.card_erase_of_mem he, hcard]
      rfl
    have hreach := ih _ hcard0 ⟨hG0, hE0, hc0⟩
    obtain ⟨hav, hcase⟩ := step_cases hG0 hG he0 hev hres hE
    refine hreach.tail ⟨e.tid, mstep_iff.mpr ⟨⟨hG0, hE0, hc0⟩, e, hav, rfl, ?_⟩⟩
    rcases hcase with ⟨x, w, hact, hwt, hGeq⟩ | ⟨wp, hew, hwp, hGeq⟩
    · have hco : G.co x = (G.remove {e}).co x := by
        have h := congrArg (fun H : Graph => H.co x) hGeq
        exact h
      have hrf : G.rf e = some w := by
        have := congrArg (fun H : Graph => H.rf e) hGeq
        simpa using this
      have hweq : w = (G.remove {e}).maxWrite x := by
        by_contra hne'
        obtain ⟨m, hm, hrel⟩ := Graph.coRelAt_maxWrite_of_ne hG0 hwt hne'
        refine hsink (.th m) (Or.inr (Or.inr (Or.inr
          ⟨e, m, x, rfl, rfl, he, hact, hco ▸ hm, ?_⟩)))
        cases w with
        | init => exact Or.inl hrf
        | th q => exact Or.inr ⟨q, hrf, hco ▸ hrel⟩
      rw [Graph.addMax_read hact, ← hweq]
      exact hGeq
    · have hco : G.co e.loc = ((G.remove {e}).addWrite e wp).co e.loc :=
        congrArg (fun H : Graph => H.co e.loc) hGeq
      have hwpeq : wp = (G.remove {e}).maxWrite e.loc := by
        by_contra hne'
        obtain ⟨m, -, hbef⟩ := Graph.addWrite_before_of_ne_max hG0 he0 hwp hne'
        exact hsink (.th m) (Or.inr (Or.inr (Or.inl ⟨e.loc, hco ▸ hbef⟩)))
      rw [Graph.addMax_write hew, ← hwpeq]
      exact hGeq

/-- prop:reachmax. -/
theorem mreach_iff {G : Graph} : MReach P G ↔ GReach P SC G := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih =>
      obtain ⟨t, hs⟩ := hs
      exact Relation.ReflTransGen.tail ih hs.gstep
  · intro h
    exact mreach_of_execSC _ G rfl (greach_iff.mp h)

/-- cor:full, first sentence: a reachable graph of a bounded program is a
prefix of a full reachable graph. -/
theorem exists_full_extension {n : ℕ} (hn : P.Bounded n) {G : Graph} (hG : GReach P SC G) :
    ∃ Gf, GReach P SC Gf ∧ P.Full Gf ∧ G.IsPrefixOf Gf := by
  have key : ∀ k (G : Graph), ExecSC P G → n * P.threads.length - G.events.card ≤ k →
      ∃ Gf, ExecSC P Gf ∧ P.Full Gf ∧ G.IsPrefixOf Gf := by
    intro k
    induction k with
    | zero =>
      rintro G ⟨hG, hE, hc⟩ hk
      by_cases hf : P.Full G
      · exact ⟨G, ⟨hG, hE, hc⟩, hf, hG.isPrefixOf_refl⟩
      · obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hf
        have hidx := idx_eq_of_mem_avail he
        have hcard : (G.addMax e).events.card = G.events.card + 1 := by
          rw [G.addMax_events, Finset.card_insert_of_notMem (not_mem_of_mem_avail hG he)]
        have h1 := (hE.addMax hG he).card_le (hG.addMax hidx) hn
        have h2 := hE.card_le hG hn
        omega
    | succ k ih =>
      rintro G ⟨hG, hE, hc⟩ hk
      by_cases hf : P.Full G
      · exact ⟨G, ⟨hG, hE, hc⟩, hf, hG.isPrefixOf_refl⟩
      · obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hf
        have hidx := idx_eq_of_mem_avail he
        have hne := not_mem_of_mem_avail hG he
        have hcard : (G.addMax e).events.card = G.events.card + 1 := by
          rw [G.addMax_events, Finset.card_insert_of_notMem hne]
        obtain ⟨Gf, hGf, hff, hp⟩ := ih (G.addMax e)
          ⟨hG.addMax hidx, hE.addMax hG he, SC.extensible.cons_addMax hG hc hidx⟩ (by omega)
        exact ⟨Gf, hGf, hff, Graph.IsPrefixOf.trans (isPrefixOf_of_insert hG (hG.addMax hidx)
          hne (G.addMax_events e) (Graph.restrict_addMax hG hne).symm) hp⟩
  obtain ⟨Gf, hGf, hff, hp⟩ := key _ G (greach_iff.mp hG) (Nat.le_refl _)
  exact ⟨Gf, greach_iff.mpr hGf, hff, hp⟩

theorem MStep.execSC_left {t : Tid} {G G' : Graph} (h : MStep P t G G') : ExecSC P G :=
  (mstep_iff.mp h).1

theorem MStep.execSC_right {t : Tid} {G G' : Graph} (h : MStep P t G G') : ExecSC P G' := by
  obtain ⟨-, hW, e, -, -, -, hE, hc⟩ := h.gstep
  exact ⟨hW, hE, hc⟩

/-- The new event of a maximal step of `t`: the next event of thread `t`. -/
theorem MStep.new_event {t : Tid} {G G' : Graph} (h : MStep P t G G') :
    ∃ a, t ∈ P.threads ∧ P.step t (G.trace t) = some a ∧ G' = G.addMax ⟨t, G.cnt t, a⟩ := by
  obtain ⟨-, ⟨t0, i0, a0⟩, he, ht, rfl⟩ := mstep_iff.mp h
  obtain ⟨h1, h2, h3⟩ := mem_avail_iff.mp he
  simp only at ht h1 h2 h3
  subst ht h2
  exact ⟨a0, h1, h3, rfl⟩

/-! ### Schedule terms -/

/-- One application of the graph algebra is a maximal step. -/
theorem apT_eq_some_iff {t : Tid} {G G' : Graph} : apT P t G = some G' ↔ MStep P t G G' := by
  classical
  unfold apT
  constructor
  · intro h
    by_cases hc : ExecSC P G ∧ t ∈ P.threads
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
      unfold Program.nextOf at he
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp he
      exact mstep_iff.mpr ⟨hc.1, _, mem_avail_iff.mpr ⟨hc.2, rfl, ha⟩, rfl, rfl⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h
      cases h
  · intro h
    obtain ⟨a, ht, ha, rfl⟩ := h.new_event
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h.execSC_left, ht⟩)]
    unfold Program.nextOf
    rw [ha]
    rfl

theorem valt_cons (P : Program) (t : Tid) (τ : List Tid) :
    valt P (t :: τ) = (valt P τ).bind (apT P t) := rfl

/-- A defined term is obtained from its subterm by a maximal step. -/
theorem valt_cons_eq_some {t : Tid} {τ : List Tid} {G' : Graph} :
    valt P (t :: τ) = some G' ↔ ∃ G, valt P τ = some G ∧ MStep P t G G' := by
  rw [valt_cons, Option.bind_eq_some_iff]
  exact exists_congr (fun G => and_congr Iff.rfl apT_eq_some_iff)

/-- The value of a term is reached by the maximal steps that the term lists. -/
theorem valt_eq_some_iff {τ : List Tid} {G : Graph} :
    valt P τ = some G ↔ MSteps P τ (Graph.init P.mem) G := by
  induction τ generalizing G with
  | nil =>
    change some (Graph.init P.mem) = some G ↔ G = Graph.init P.mem
    exact ⟨fun h => (Option.some.inj h).symm, fun h => h ▸ rfl⟩
  | cons t τ ih =>
    rw [valt_cons_eq_some]
    exact exists_congr (fun G₁ => and_congr ih Iff.rfl)

/-- The value of a term is a consistent execution. -/
theorem valt_execSC {τ : List Tid} {G : Graph} (h : valt P τ = some G) : ExecSC P G := by
  cases τ with
  | nil =>
    cases h
    exact ⟨Graph.init_wf _, exec_init P, SC.cons_init _⟩
  | cons t τ =>
    obtain ⟨G₀, -, hstep⟩ := valt_cons_eq_some.mp h
    exact hstep.execSC_right

/-- Maximal steps along a list are deterministic. -/
theorem MSteps.unique {τ : List Tid} {G G₁ G₂ : Graph} (h₁ : MSteps P τ G G₁)
    (h₂ : MSteps P τ G G₂) : G₁ = G₂ := by
  induction τ generalizing G₁ G₂ with
  | nil => exact h₁.trans h₂.symm
  | cons t τ ih =>
    obtain ⟨H₁, hH₁, hs₁⟩ := h₁
    obtain ⟨H₂, hH₂, hs₂⟩ := h₂
    rw [ih hH₁ hH₂] at hs₁
    exact hs₁.unique hs₂

/-- Each maximal step adds one event. -/
theorem MSteps.card {τ : List Tid} {G G' : Graph} (h : MSteps P τ G G') :
    G'.events.card = G.events.card + τ.length := by
  induction τ generalizing G' with
  | nil => rw [h]; rfl
  | cons t τ ih =>
    obtain ⟨H, hH, hs⟩ := h
    have := hs.gstep.size
    unfold Graph.size at this
    rw [List.length_cons, ← Nat.add_assoc, ← ih hH]
    omega

/-- lem:terms: the values of the valid terms are the reachable graphs. -/
theorem valt_range {G : Graph} : (∃ τ, valt P τ = some G) ↔ GReach P SC G := by
  constructor
  · rintro ⟨τ, h⟩
    exact greach_iff.mpr (valt_execSC h)
  · intro h
    have hm := mreach_iff.mpr h
    induction hm with
    | refl => exact ⟨[], rfl⟩
    | tail hr hs ih =>
      obtain ⟨t, hs⟩ := hs
      obtain ⟨τ, hτ⟩ := ih (mreach_iff.mp hr)
      exact ⟨t :: τ, valt_cons_eq_some.mpr ⟨_, hτ, hs⟩⟩

/-- A reachable graph is the value of a term with one symbol per thread
event: it is reached by `|G| - 1` maximal steps. -/
theorem greach_iff_msteps {G : Graph} :
    GReach P SC G ↔
      ∃ τ, τ.length = G.events.card ∧ MSteps P τ (Graph.init P.mem) G := by
  constructor
  · intro h
    obtain ⟨τ, hτ⟩ := valt_range.mpr h
    have hm := valt_eq_some_iff.mp hτ
    have := hm.card
    simp only [Graph.init, Finset.card_empty, Nat.zero_add] at this
    exact ⟨τ, this.symm, hm⟩
  · rintro ⟨τ, -, hm⟩
    exact valt_range.mp ⟨τ, valt_eq_some_iff.mpr hm⟩

/-! ### Instances -/

namespace Examples

/-- The full graph `G3` of the checked run is the value of a schedule term
with three symbols. -/
example : ∃ τ, τ.length = 3 ∧ valt revProg τ = some G3 := by
  obtain ⟨τ, hl, hm⟩ := greach_iff_msteps.mp
    (greach_iff.mpr ⟨G3_facts.1, G3_facts.2.1, G3_facts.2.2.1⟩)
  refine ⟨τ, hl.trans ?_, valt_eq_some_iff.mpr hm⟩
  rw [← C3_abs]
  rfl

end Examples

end Trust
