import Mazurkiewicz.Condpor.Explore
import Mazurkiewicz.Lib.ReachB

/-!
# Computable checks

The tests that Algorithm 1 performs, as functions to `Bool`, each proved
equal to the predicate of `Trust/Graph.lean`, `Models/Model.lean` and
`Trust/Alg.lean` that it decides:

* `Graph.porfB`: causality `porf` (`Graph.porfB_iff`);
* `Graph.consB`: SC-consistency of a well-formed graph (`Graph.consB_iff`);
* `Config.deletedB`, `Config.keepC`, `Config.revisitC`: the deleted events
  of a revisit, the kept events, the configuration after the revisit;
* `Config.previousB`, `Config.maxAddedB`: `Previous` and
  `IsMaximallyAdded`.

The events of a graph are given to these functions as a list (the order list
of a configuration). The functions are written for clarity of the proofs,
not for speed: reachability tries all paths up to the number of events.
-/

namespace Condpor

open Program

namespace Graph

variable (G : Graph)

/-! ### Causality -/

/-- One step of causality, as a test. -/
def porfStepB : Ev → Ev → Bool
  | .init, .th e => decide (e ∈ G.events)
  | .th e, .th e' =>
    decide (e ∈ G.events ∧ e' ∈ G.events ∧ e.tid = e'.tid ∧ e.idx < e'.idx) ||
      (decide (e' ∈ G.events) && decide (G.rf e' = some (.th e)))
  | _, .init => false

theorem porfStepB_iff (a b : Ev) : G.porfStepB a b = true ↔ G.porfStep a b := by
  cases a with
  | init =>
    cases b with
    | init => simp [porfStepB, porfStep, po, rfRel]
    | th e' =>
      simp only [porfStepB, porfStep, po, rfRel, decide_eq_true_eq]
      constructor
      · exact Or.inl
      · rintro (h | ⟨q, hq, hqm, -⟩)
        · exact h
        · exact (Ev.th.inj hq) ▸ hqm
  | th e =>
    cases b with
    | init => simp [porfStepB, porfStep, po, rfRel]
    | th e' =>
      simp only [porfStepB, porfStep, po, rfRel, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨e', rfl, h1, h2⟩
      · rintro (h | ⟨q, hq, hqm, hrf⟩)
        · exact Or.inl h
        · rw [← Ev.th.inj hq] at hqm hrf
          exact Or.inr ⟨hqm, hrf⟩

/-- Causality, as a test; `l` lists the events of the graph. -/
def porfB (l : List TEv) (a b : Ev) : Bool :=
  Maz.reachN G.porfStepB (l.map .th) (l.map Ev.th).length a b

theorem porfB_iff {l : List TEv} (hl : ∀ e, e ∈ G.events → e ∈ l) (a b : Ev) :
    G.porfB l a b = true ↔ G.porf a b := by
  have hrel : (fun x y => G.porfStepB x y = true) = G.porfStep := by
    funext x y
    exact propext (G.porfStepB_iff x y)
  unfold porfB porf
  rw [Maz.reachN_iff, hrel]
  intro x y hxy
  have hstep := (G.porfStepB_iff x y).mp hxy
  rcases hstep with hpo | ⟨q, rfl, hqm, -⟩
  · cases y with
    | init => cases x <;> exact absurd hpo (by simp [po])
    | th q =>
      refine List.mem_map_of_mem (hl q ?_)
      cases x with
      | init => exact hpo
      | th p => exact hpo.2.1
  · exact List.mem_map_of_mem (hl q hqm)

/-! ### Sequential consistency -/

/-- Coherence, as a test (on a well-formed graph the location of a pair is
the location of its events). -/
def coB : Ev → Ev → Bool
  | .init, .th e' => decide (e' ∈ G.co e'.loc)
  | .th e, .th e' => decide ((G.co e.loc).Before e e')
  | _, .init => false

/-- From-read, as a test. -/
def frB : Ev → Ev → Bool
  | .th e, .th e' =>
    match e.act with
    | .read x =>
      decide (e ∈ G.events) && decide (e' ∈ G.co x) &&
        (match G.rf e with
          | some .init => true
          | some (.th e'') => decide ((G.co x).Before e'' e')
          | none => false)
    | _ => false
  | _, _ => false

/-- One step of the SC order, as a test. -/
def scStepB (a b : Ev) : Bool := G.porfStepB a b || G.coB a b || G.frB a b

/-- SC-consistency, as a test; `l` lists the events of the graph. -/
def consB (l : List TEv) : Bool := Maz.acyclicB G.scStepB (l.map .th)

variable {G}

theorem Wf.loc_of_co_mem (hG : G.Wf) {x : Loc} {e : TEv} (h : e ∈ G.co x) : e.loc = x := by
  obtain ⟨-, v, hv⟩ := (hG.co_mem x e).mp h
  simp [TEv.loc, hv, Act.loc]

theorem coB_iff (hG : G.Wf) (a b : Ev) : G.coB a b = true ↔ G.coRel a b := by
  cases a with
  | init =>
    cases b with
    | init => simp [coB, coRel]
    | th e' =>
      simp only [coB, coRel, decide_eq_true_eq]
      constructor
      · exact fun h => ⟨_, h⟩
      · rintro ⟨x, hx⟩
        rw [hG.loc_of_co_mem hx]
        exact hx
  | th e =>
    cases b with
    | init => simp [coB, coRel]
    | th e' =>
      simp only [coB, coRel, decide_eq_true_eq]
      constructor
      · exact fun h => ⟨_, h⟩
      · rintro ⟨x, hx⟩
        rw [hG.loc_of_co_mem hx.1]
        exact hx

theorem frB_iff (a b : Ev) : G.frB a b = true ↔ G.frRel a b := by
  cases a with
  | init =>
    simp only [frB, frRel, Bool.false_eq_true, false_iff]
    rintro ⟨e, e', x, h, -⟩
    cases h
  | th e =>
    cases b with
    | init =>
      simp only [frB, frRel, Bool.false_eq_true, false_iff]
      rintro ⟨e0, e', x, -, h, -⟩
      cases h
    | th e' =>
      unfold frB frRel
      cases hact : e.act
      case read x =>
        simp only [hact, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨e, e', x, rfl, rfl, h1, hact, h2, ?_⟩
          cases hrf : G.rf e with
          | none => rw [hrf] at h3; cases h3
          | some s =>
            cases s with
            | init => exact Or.inl rfl
            | th e'' =>
              rw [hrf] at h3
              exact Or.inr ⟨e'', rfl, of_decide_eq_true h3⟩
        · rintro ⟨e0, e1, y, h0, h1, hm, hy, hco, hsrc⟩
          rw [← Ev.th.inj h0] at hm hy hsrc
          rw [← Ev.th.inj h1] at hco hsrc
          rw [hact] at hy
          have hxy : x = y := Act.read.inj hy
          subst hxy
          refine ⟨⟨hm, hco⟩, ?_⟩
          rcases hsrc with h | ⟨e'', h, hb⟩
          · rw [h]
          · rw [h]
            exact decide_eq_true hb
      all_goals
        simp only [hact, Bool.false_eq_true, false_iff]
        rintro ⟨e0, e1, y, h0, -, -, hy, -⟩
        rw [← Ev.th.inj h0, hact] at hy
        cases hy

theorem scStepB_iff (hG : G.Wf) (a b : Ev) : G.scStepB a b = true ↔ G.scStep a b := by
  unfold scStepB scStep
  rw [Bool.or_eq_true, Bool.or_eq_true, G.porfStepB_iff, coB_iff hG, frB_iff]
  unfold porfStep
  tauto

theorem consB_iff (hG : G.Wf) {l : List TEv} (hl : ∀ e, e ∈ G.events → e ∈ l) :
    G.consB l = true ↔ SC.cons G := by
  have hrel : (fun x y => G.scStepB x y = true) = G.scStep := by
    funext x y
    exact propext (scStepB_iff hG x y)
  unfold consB
  change _ ↔ Maz.Acyclic G.scStep
  rw [Maz.acyclicB_iff, hrel]
  intro x y hxy
  rcases (scStepB_iff hG x y).mp hxy with h | h | h | h
  · have := (hG.mem_of_porfStep (Or.inl h)).2
    cases y with
    | init => cases x <;> exact absurd h (by simp [po])
    | th q => exact List.mem_map_of_mem (hl q this)
  · have := (hG.mem_of_porfStep (Or.inr h)).2
    obtain ⟨q, rfl, -, -⟩ := h
    exact List.mem_map_of_mem (hl q this)
  · cases y with
    | init => cases x <;> exact absurd h (by simp [coRel])
    | th q =>
      refine List.mem_map_of_mem (hl q ?_)
      cases x with
      | init =>
        obtain ⟨z, hz⟩ := h
        exact ((hG.co_mem z q).mp hz).1
      | th p =>
        obtain ⟨z, hz⟩ := h
        exact ((hG.co_mem z q).mp hz.2.1).1
  · obtain ⟨e, e', z, -, rfl, -, -, hco, -⟩ := h
    exact List.mem_map_of_mem (hl e' ((hG.co_mem z e').mp hco).1)

end Graph

namespace Graph

instance (G : Graph) (x : Loc) (a b : Ev) : Decidable (G.coRelAt x a b) := by
  cases a <;> cases b <;> unfold coRelAt <;> infer_instance

/-- A coherence successor at `x` is a thread write in the list `co x`. -/
theorem mem_co_of_coRelAt {G : Graph} {x : Loc} {a : Ev} {w : TEv}
    (h : G.coRelAt x a (.th w)) : w ∈ G.co x := by
  cases a with
  | init => exact h
  | th s => exact h.2.1

end Graph

namespace Config

variable (c : Config)

/-! ### Tests on configurations -/

/-- SC-consistency of the graph of a configuration. -/
def consC : Bool := c.abs.consB c.order

theorem consC_iff (hc : c.abs.Wf) : c.consC = true ↔ SC.cons c.abs :=
  Graph.consB_iff hc (fun _ he => List.mem_toFinset.mp he)

/-- Causality in `c.plus w`. -/
def plusPorfB (w : TEv) (a b : Ev) : Bool := (c.plus w).porfB (w :: c.order) a b

theorem plusPorfB_iff (w : TEv) (a b : Ev) :
    c.plusPorfB w a b = true ↔ (c.plus w).porf a b := by
  refine Graph.porfB_iff _ (fun e he => ?_) a b
  have he' : e ∈ insert w c.order.toFinset := he
  rcases Finset.mem_insert.mp he' with rfl | h
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_toFinset.mp h)

/-- `Deleted`, as a test. -/
def deletedB (r w d : TEv) : Bool :=
  decide (d ∈ c.order) && decide (c.order.Before d r) && !c.plusPorfB w (.th d) (.th w)

theorem deletedB_iff (r w d : TEv) : c.deletedB r w d = true ↔ c.Deleted r w d := by
  unfold deletedB Deleted lt
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    Bool.not_eq_true', ← Bool.not_eq_true, plusPorfB_iff]
  tauto

/-- The kept events of a revisit, computed. -/
def keepC (r w : TEv) : Finset TEv := (c.order.filter (fun d => !c.deletedB r w d)).toFinset

theorem keepC_eq (r w : TEv) : c.keepC r w = c.keep r w := by
  ext d
  rw [mem_keep_iff, ← deletedB_iff]
  simp [keepC]

/-- The configuration after a revisit, computed. -/
def revisitC (r w : TEv) (wp : Ev) : Config :=
  let G' := ((c.abs.restrict (c.keepC r w)).addWrite w wp).setRF r (.th w)
  ⟨c.mem, w :: c.order.filter (fun d => decide (d ∈ c.keepC r w)), G'.rf, G'.co, G'.pol⟩

theorem revisitC_eq (r w : TEv) (wp : Ev) : c.revisitC r w wp = c.revisit r w wp := by
  unfold revisitC revisit
  rw [keepC_eq]

/-- `Previous`, as a test. -/
def previousB (p w : TEv) : Ev → Bool
  | .init => true
  | .th q =>
    decide (q ∈ c.order) &&
      (decide (q = p) || decide (c.order.Before p q) || c.plusPorfB w (.th q) (.th w))

theorem previousB_iff (p w : TEv) (x : Ev) : c.previousB p w x = true ↔ c.Previous p w x := by
  cases x with
  | init => simp [previousB, Previous]
  | th q =>
    unfold previousB Previous le lt
    rw [Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      decide_eq_true_eq, decide_eq_true_eq, plusPorfB_iff]

/-- The context of a revisit, computed. -/
def ctxC (r w : TEv) : Finset Lit := (c.abs.restrict (c.keepC r w)).F

theorem ctxC_eq (r w : TEv) : c.ctxC r w = c.ctx r w := by
  unfold ctxC ctx
  rw [keepC_eq]

/-- The literals of the events of `Previous` other than the event, computed. -/
def prevFC (p w : TEv) : Finset Lit :=
  (c.abs.restrict
    (c.order.filter (fun q => decide (q ≠ p) && c.previousB p w (.th q))).toFinset).F

theorem prevFC_eq (p w : TEv) : c.prevFC p w = c.prevF p w := by
  classical
  unfold prevFC prevF
  congr 2
  ext q
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq, previousB_iff]

/-- `IsMaximallyAdded`, as a test; `pb` is the choice of outcomes for the
context of the revisit. -/
def maxAddedB (pb : Finset Lit → SExpr → Bool) (p w : TEv) : Bool :=
  !(c.order.any (fun q => c.previousB p w (.th q) && decide (c.rf q = some (.th p)))) &&
    (match p.act with
      | .read _ =>
        (match c.rf p with
          | none => false
          | some e' =>
            c.previousB p w e' &&
              !((c.abs.co p.loc).any (fun w'' =>
                c.previousB p w (.th w'') && decide (c.abs.coRelAt p.loc e' (.th w'')))))
      | .write _ _ =>
        c.previousB p w (.th p) &&
          !((c.abs.co p.loc).any (fun w'' =>
            c.previousB p w (.th w'') && decide (c.abs.coRelAt p.loc (.th p) (.th w''))))
      | .cons φ => decide (c.pol p = some (pb (c.prevFC p w) φ))
      | _ => true)

theorem maxAddedB_iff {S : Solver} (τ : TieBreak S) (K : Finset Lit) (p w : TEv) :
    c.maxAddedB (τ.pref K) p w = true ↔ c.IsMaximallyAdded τ K p w := by
  have h1 : (!(c.order.any (fun q =>
        c.previousB p w (.th q) && decide (c.rf q = some (.th p))))) = true ↔
      ¬ ∃ q, c.Previous p w (.th q) ∧ c.rf q = some (.th p) := by
    rw [Bool.not_eq_true', ← Bool.not_eq_true, List.any_eq_true]
    refine not_congr ⟨?_, ?_⟩
    · rintro ⟨q, -, hq⟩
      rw [Bool.and_eq_true, previousB_iff, decide_eq_true_eq] at hq
      exact ⟨q, hq⟩
    · rintro ⟨q, hq1, hq2⟩
      exact ⟨q, hq1.1, by rw [Bool.and_eq_true, previousB_iff, decide_eq_true_eq]; exact ⟨hq1, hq2⟩⟩
  have h2 : ∀ e' : Ev, (c.previousB p w e' &&
        !((c.abs.co p.loc).any (fun w'' =>
          c.previousB p w (.th w'') && decide (c.abs.coRelAt p.loc e' (.th w''))))) = true ↔
      (c.Previous p w e' ∧ ¬ ∃ w', c.Previous p w w' ∧ c.abs.coRelAt p.loc e' w') := by
    intro e'
    rw [Bool.and_eq_true, previousB_iff, Bool.not_eq_true', ← Bool.not_eq_true,
      List.any_eq_true]
    refine and_congr Iff.rfl (not_congr ⟨?_, ?_⟩)
    · rintro ⟨w'', -, hw⟩
      rw [Bool.and_eq_true, previousB_iff, decide_eq_true_eq] at hw
      exact ⟨.th w'', hw⟩
    · rintro ⟨w', hw1, hw2⟩
      cases w' with
      | init => cases e' <;> exact absurd hw2 (by simp [Graph.coRelAt])
      | th w'' =>
        exact ⟨w'', Graph.mem_co_of_coRelAt hw2, by
          rw [Bool.and_eq_true, previousB_iff, decide_eq_true_eq]; exact ⟨hw1, hw2⟩⟩
  unfold maxAddedB IsMaximallyAdded MaxRW MaxCons
  rw [Bool.and_eq_true, h1]
  refine and_congr Iff.rfl ?_
  cases hact : p.act with
  | read x =>
    have hr : p.IsRead := by simp [TEv.IsRead, hact, Act.IsRead]
    have hnl : ¬ p.IsLocal := fun h => h.not_isRead hr
    simp only
    constructor
    · intro h
      refine ⟨fun _ => ?_, fun φ hφ => by cases hφ⟩
      cases hrf : c.rf p with
      | none => rw [hrf] at h; cases h
      | some s =>
        rw [hrf] at h
        exact ⟨s, fun _ => rfl, fun hn => absurd hr hn, (h2 s).mp h⟩
    · rintro ⟨h, -⟩
      obtain ⟨e', he', -, hp⟩ := h hnl
      rw [he' hr]
      exact (h2 e').mpr hp
  | write x v =>
    have hnr : ¬ p.IsRead := by simp [TEv.IsRead, hact, Act.IsRead]
    have hnl : ¬ p.IsLocal := by simp [TEv.IsLocal, hact, Act.IsLocal]
    simp only
    rw [h2]
    constructor
    · intro h
      exact ⟨fun _ => ⟨.th p, fun hr => absurd hr hnr, fun _ => rfl, h⟩,
        fun φ hφ => by cases hφ⟩
    · rintro ⟨h, -⟩
      obtain ⟨e', -, he', hp⟩ := h hnl
      rw [he' hnr] at hp
      exact hp
  | cons φ =>
    have hl : p.IsLocal := by simp [TEv.IsLocal, hact, Act.IsLocal]
    simp only
    rw [decide_eq_true_eq, prevFC_eq]
    constructor
    · intro h
      refine ⟨fun hn => absurd hl hn, fun φ' hφ' => ?_⟩
      have : φ = φ' := Act.cons.inj hφ'
      rw [← this]
      exact h
    · rintro ⟨-, h⟩
      exact h φ rfl
  | gen s =>
    have hl : p.IsLocal := by simp [TEv.IsLocal, hact, Act.IsLocal]
    simp only [true_iff]
    exact ⟨fun hn => absurd hl hn,
      fun φ hφ => by cases hφ⟩
  | block =>
    have hl : p.IsLocal := by simp [TEv.IsLocal, hact, Act.IsLocal]
    simp only [true_iff]
    exact ⟨fun hn => absurd hl hn,
      fun φ hφ => by cases hφ⟩
  | error =>
    have hl : p.IsLocal := by simp [TEv.IsLocal, hact, Act.IsLocal]
    simp only [true_iff]
    exact ⟨fun hn => absurd hl hn,
      fun φ hφ => by cases hφ⟩

/-- The tests of a revisit of `r` by `w`: `r` is not causally before `w`, and
the deleted events and `r` are maximally added. `prefB` computes the
tie-break. -/
def revisitOKB (prefB : Finset Lit → Finset Lit → SExpr → Bool) (r w : TEv) : Bool :=
  !c.plusPorfB w (.th r) (.th w) &&
    c.order.all (fun d => !(c.deletedB r w d || decide (d = r)) ||
      c.maxAddedB (prefB (c.ctxC r w)) d w)

theorem revisitOKB_iff {S : Solver} (τ : TieBreak S)
    {prefB : Finset Lit → Finset Lit → SExpr → Bool}
    (hpb : ∀ K F φ, prefB K F φ = τ.pref K F φ) {r : TEv} (hr : r ∈ c.order) (w : TEv) :
    c.revisitOKB prefB r w = true ↔
      (¬ (c.plus w).porf (.th r) (.th w) ∧
        ∀ d, (c.Deleted r w d ∨ d = r) → c.IsMaximallyAdded τ (c.ctx r w) d w) := by
  have hpe : prefB (c.ctxC r w) = τ.pref (c.ctx r w) := by
    funext F φ
    rw [hpb, ctxC_eq]
  unfold revisitOKB
  rw [hpe, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, plusPorfB_iff,
    List.all_eq_true]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · intro h d hd
    have hdo : d ∈ c.order := hd.elim (fun h' => h'.1) (fun h' => h' ▸ hr)
    have := h d hdo
    rw [Bool.or_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, Bool.or_eq_true, deletedB_iff,
      decide_eq_true_eq, maxAddedB_iff] at this
    exact this.resolve_left (fun h' => h' hd)
  · intro h d _
    rw [Bool.or_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, Bool.or_eq_true, deletedB_iff,
      decide_eq_true_eq, maxAddedB_iff]
    by_cases hd : c.Deleted r w d ∨ d = r
    · exact Or.inr (h d hd)
    · exact Or.inl hd

end Config

end Condpor
