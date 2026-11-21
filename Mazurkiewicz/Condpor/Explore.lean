import Mazurkiewicz.Condpor.Exit

/-!
# The explorer and its specification

`Trust/Explore.lean` for the symbolic algorithm. `explore P M τ n` is the list
of graphs that Algorithm 1 (without the exit at an error) reports for the
program `P`, bounded by `n` events per thread, under the model `M` and with
the tie-break `τ`.

`explore_spec`: for a bounded program, an extensible underlying model `M` and
any solver and tie-break, the list `explore P (M.sym S) τ n` has no repetition,
and its members are exactly the well-formed, `M_S`-consistent, full executions
of `P`. This is Theorems 4 and 5(a) of the paper in one statement; a graph in
which every thread is finished, blocked, or stopped by an error is full.

`cands` enumerates the choices of a call of `Visit`: a source for a read; a
coherence place for a write; a read to revisit, with a coherence place; the
two outcomes of a constraint evaluation; the one way to add a generation,
block or error event. `succs` keeps the choices that are steps. The recursion
of `Visit` is `exploreFrom`, with a counter in place of a termination
argument; `explore` starts it with a counter that no run exceeds
(`terminates_bound`). The definitions here are not computable; the computable
explorer for `SC` is in `ExploreC.lean`.
-/

namespace List

variable {α : Type*} [DecidableEq α]

/-- The place where `e` is inserted is determined by the result. -/
theorem insertAfter_inj {l : List α} {p1 p2 e : α} (h1 : p1 ∈ l) (h2 : p2 ∈ l) (he : e ∉ l)
    (h : l.insertAfter p1 e = l.insertAfter p2 e) : p1 = p2 := by
  have a1 := before_insertAfter_self h1 he
  have a2 := before_insertAfter_self h2 he
  rw [h] at a1
  rw [← h] at a2
  rcases (before_insertAfter_new_right h2 he).mp a1 with h' | h'
  · exact h'
  · rcases (before_insertAfter_new_right h1 he).mp a2 with h'' | h''
    · exact h''.symm
    · exact absurd h'' h'.asymm

theorem cons_ne_insertAfter {l : List α} {p e : α} (hp : p ∈ l) (he : e ∉ l) :
    e :: l ≠ l.insertAfter p e := by
  intro h
  have a := before_insertAfter_self hp he
  rw [← h] at a
  rcases before_cons_iff.mp a with ⟨h1, -, -⟩ | ⟨-, h1, -⟩
  · exact he (h1 ▸ hp)
  · exact h1 rfl

end List

namespace Condpor

open Program

variable {P : Program} {M : Model} {S : Solver} {τ : TieBreak S}

/-! ### Definitions -/

/-- The thread event `q` is a write to `x`. -/
def TEv.writesTo (q : TEv) (x : Loc) : Bool :=
  match q.act with
  | .write y _ => decide (y = x)
  | _ => false

/-- The thread event `q` is a read of `x`. -/
def TEv.readsLoc (q : TEv) (x : Loc) : Bool :=
  match q.act with
  | .read y => decide (y = x)
  | _ => false

/-- The writes to `x` among the events `l`, with `init`. -/
def writesOf (l : List TEv) (x : Loc) : List Ev :=
  .init :: (l.filter (fun q => q.writesTo x)).map .th

/-- The bound on the length of a run for a program with at most `n` events
per thread (the bound in the proof of Theorem A.27). -/
def Program.bound (P : Program) (n : ℕ) : ℕ :=
  (n * P.threads.length) * (n * P.threads.length + 1) + n * P.threads.length

/-- The choices of Algorithm 1 at the configuration `c` (lines 10-18, 21-22),
before the checks. -/
noncomputable def cands (P : Program) (c : Config) : List Config :=
  match P.nextC c with
  | none => []
  | some e =>
    match e.act with
    | .read x => (writesOf c.order x).map (c.addRead e)
    | .write x _ =>
      (writesOf c.order x).map (c.addWrite e) ++
        (c.order.filter (fun r => r.readsLoc x)).flatMap (fun r =>
          (writesOf (c.order.filter (fun d => decide (d ∈ c.keep r e))) x).map
            (c.revisit r e))
    | .cons _ => [c.addLoc e (some true), c.addLoc e (some false)]
    | _ => [c.addLoc e none]

/-- The configurations that `Visit` is called with from `c`: the choices that
pass the checks. -/
noncomputable def succs (P : Program) (M : Model) {S : Solver} (τ : TieBreak S)
    (c : Config) : List Config :=
  open Classical in (cands P c).filter (fun c' => decide (Step P M τ c c'))

/-- The graphs reported by `Visit` started at `c`, following the calls to
depth `f`. -/
noncomputable def exploreFrom (P : Program) (M : Model) {S : Solver} (τ : TieBreak S) :
    ℕ → Config → List Graph
  | 0, _ => []
  | f + 1, c =>
    open Classical in
    if M.cons c.abs then
      if P.nextC c = none then [c.abs] else (succs P M τ c).flatMap (exploreFrom P M τ f)
    else []

/-- The graphs that Algorithm 1 reports for `P` under `M`, where `n` bounds
the number of events of a thread. -/
noncomputable def explore (P : Program) (M : Model) {S : Solver} (τ : TieBreak S)
    (n : ℕ) : List Graph :=
  exploreFrom P M τ (P.bound n + 1) (Config.init P.mem)

/-! ### The choices -/

theorem TEv.writesTo_iff {q : TEv} {x : Loc} : q.writesTo x = true ↔ ∃ v, q.act = .write x v := by
  unfold TEv.writesTo
  cases q.act <;> simp

theorem TEv.readsLoc_iff {q : TEv} {x : Loc} : q.readsLoc x = true ↔ q.act = .read x := by
  unfold TEv.readsLoc
  cases q.act <;> simp

theorem mem_writesOf {l : List TEv} {x : Loc} {w : Ev} :
    w ∈ writesOf l x ↔
      (match w with
        | .init => True
        | .th q => q ∈ l ∧ ∃ v, q.act = .write x v) := by
  unfold writesOf
  cases w with
  | init => simp
  | th q => simp [List.mem_filter, TEv.writesTo_iff]

theorem writesOf_nodup {l : List TEv} (hl : l.Nodup) (x : Loc) : (writesOf l x).Nodup := by
  unfold writesOf
  refine List.nodup_cons.mpr ⟨by simp, ?_⟩
  exact (hl.filter _).map (fun a b h => Ev.th.inj h)

/-- The coherence predecessor is determined by the coherence list. -/
theorem coPos_inj {l : List TEv} {e : TEv} {wp1 wp2 : Ev} (he : e ∉ l)
    (h : (match wp1 with
          | .init => e :: l
          | .th p => l.insertAfter p e) =
        (match wp2 with
          | .init => e :: l
          | .th p => l.insertAfter p e))
    (h1 : ∀ p, wp1 = .th p → p ∈ l) (h2 : ∀ p, wp2 = .th p → p ∈ l) : wp1 = wp2 := by
  cases wp1 with
  | init =>
    cases wp2 with
    | init => rfl
    | th p2 => exact absurd h (List.cons_ne_insertAfter (h2 p2 rfl) he)
  | th p1 =>
    cases wp2 with
    | init => exact absurd h.symm (List.cons_ne_insertAfter (h1 p1 rfl) he)
    | th p2 => rw [List.insertAfter_inj (h1 p1 rfl) (h2 p2 rfl) he h]

/-- A step leads to one of the choices. -/
theorem mem_cands_of_step {c c' : Config} (hc : c.Wf) (h : Step P M τ c c') : c' ∈ cands P c := by
  obtain ⟨e, k, hs⟩ := h
  unfold cands
  cases k with
  | nr =>
    obtain ⟨-, hnext, hcase⟩ := hs.nr_inv
    rw [(nextC_eq_some_iff hc).mpr hnext]
    rcases hcase with ⟨x, w, hact, hw, rfl⟩ | ⟨wp, hw, hwp, rfl⟩ | ⟨b, hcs, rfl⟩ |
      ⟨hl, hnc, rfl⟩
    rotate_left 2
    · obtain ⟨φ, hφ⟩ := TEv.IsCons.exists_act hcs
      simp only [hφ]
      cases b <;> simp
    · cases hact : e.act with
      | read x => simp [TEv.IsLocal, hact, Act.IsLocal] at hl
      | write x v => simp [TEv.IsLocal, hact, Act.IsLocal] at hl
      | cons φ => simp [TEv.IsCons, hact, Act.IsCons] at hnc
      | gen s => simp only [hact, List.mem_singleton]
      | block => simp only [hact, List.mem_singleton]
      | error => simp only [hact, List.mem_singleton]
    · simp only [hact]
      refine List.mem_map_of_mem (mem_writesOf.mpr ?_)
      cases w with
      | init => trivial
      | th q => exact ⟨List.mem_toFinset.mp hw.1, hw.2⟩
    · obtain ⟨v, hv⟩ := hw.exists_act
      simp only [hv]
      refine List.mem_append_left _ (List.mem_map_of_mem (mem_writesOf.mpr ?_))
      cases wp with
      | init => trivial
      | th q => exact ⟨List.mem_toFinset.mp hwp.1, hwp.2⟩
  | rv r =>
    obtain ⟨wp, rfl, -, hnext, hw, hr, hract, -, -, hwp⟩ := hs.rv_inv
    rw [(nextC_eq_some_iff hc).mpr hnext]
    obtain ⟨v, hv⟩ := hw.exists_act
    simp only [hv]
    refine List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨r, List.mem_filter.mpr ⟨hr, TEv.readsLoc_iff.mpr hract⟩,
        List.mem_map_of_mem (mem_writesOf.mpr ?_)⟩)
    cases wp with
    | init => trivial
    | th q =>
      obtain ⟨hq, hq'⟩ := hwp
      have hq2 := Finset.mem_inter.mp hq
      exact ⟨List.mem_filter.mpr ⟨List.mem_toFinset.mp hq2.1, by simpa using hq2.2⟩, hq'⟩

/-- No choice is listed twice. -/
theorem cands_nodup {c : Config} (hc : c.Wf) : (cands P c).Nodup := by
  unfold cands
  cases hnx : P.nextC c with
  | none => exact List.nodup_nil
  | some e =>
    have hnext := (nextC_eq_some_iff hc).mp hnx
    have hidx := idx_eq_of_mem_avail hnext.1
    have heE : e ∉ c.abs.events := hc.1.not_mem_of_idx_eq_cnt hidx
    have heo : e ∉ c.order := fun h => heE (List.mem_toFinset.mpr h)
    -- no read of `c` reads from `e`
    have hnoe : ∀ q, c.abs.rf q ≠ some (.th e) := fun q h => heE (hc.1.rf_source_mem h).2
    cases hact : e.act with
    | read x =>
      simp only [hact]
      refine List.Nodup.map_on (fun w1 _ w2 _ h => ?_) (writesOf_nodup hc.2 x)
      have h' := congrFun (congrArg Config.rf h) e
      simp only [Config.addRead, Graph.addRead_rf, Function.update_self] at h'
      exact Option.some.inj h'
    | write x v =>
      simp only [hact]
      have hloc : e.loc = x := by simp [TEv.loc, hact, Act.loc]
      refine List.nodup_append.mpr ⟨?_, ?_, ?_⟩
      · refine List.Nodup.map_on (fun w1 hw1 w2 hw2 h => ?_) (writesOf_nodup hc.2 x)
        have h' := congrFun (congrArg Config.co h) e.loc
        simp only [Config.addWrite] at h'
        rw [Graph.addWrite_co_self, Graph.addWrite_co_self] at h'
        have hval : ∀ w, w ∈ writesOf c.order x → ∀ p, w = .th p → p ∈ c.abs.co e.loc := by
          rintro w hw p rfl
          obtain ⟨hp, hp'⟩ := mem_writesOf.mp hw
          rw [hloc]
          exact (hc.1.co_mem x p).mpr ⟨List.mem_toFinset.mpr hp, hp'⟩
        exact coPos_inj (fun h => heE ((hc.1.co_mem _ _).mp h).1) h' (hval w1 hw1) (hval w2 hw2)
      · refine List.nodup_flatMap.mpr ⟨fun r _ => ?_, ?_⟩
        · refine List.Nodup.map_on (fun w1 hw1 w2 hw2 h => ?_)
            (writesOf_nodup (hc.2.filter _) x)
          have h' := congrFun (congrArg Config.co h) e.loc
          simp only [Config.revisit, Graph.setRF_co] at h'
          rw [Graph.addWrite_co_self, Graph.addWrite_co_self] at h'
          have hval : ∀ w, w ∈ writesOf (c.order.filter (fun d => decide (d ∈ c.keep r e))) x →
              ∀ p, w = .th p → p ∈ (c.abs.restrict (c.keep r e)).co e.loc := by
            rintro w hw p rfl
            obtain ⟨hp, hp'⟩ := mem_writesOf.mp hw
            obtain ⟨hp1, hp2⟩ := List.mem_filter.mp hp
            rw [hloc]
            exact List.mem_filter.mpr
              ⟨(hc.1.co_mem x p).mpr ⟨List.mem_toFinset.mpr hp1, hp'⟩, hp2⟩
          refine coPos_inj (fun h => ?_) h' (hval w1 hw1) (hval w2 hw2)
          exact heE ((hc.1.co_mem _ _).mp (List.mem_filter.mp h).1).1
        · refine List.Pairwise.imp (fun {r r'} hne => ?_) (hc.2.filter _)
          intro c' h1 h2
          obtain ⟨wp, -, rfl⟩ := List.mem_map.mp h1
          obtain ⟨wp', -, h⟩ := List.mem_map.mp h2
          have h' := congrFun (congrArg Config.rf h) r
          simp only [Config.revisit, Graph.setRF_rf, Graph.addWrite_rf, Function.update_self,
            Function.update_of_ne hne] at h'
          exact hnoe r (c.abs.restrict_rf_eq_some h').1
      · intro c1 h1 c2 h2 h12
        obtain ⟨wp, -, rfl⟩ := List.mem_map.mp h1
        obtain ⟨r, -, h2'⟩ := List.mem_flatMap.mp h2
        obtain ⟨wp', -, h⟩ := List.mem_map.mp h2'
        rw [← h12] at h
        have h' := congrFun (congrArg Config.rf h) r
        simp only [Config.revisit, Config.addWrite, Graph.setRF_rf, Graph.addWrite_rf,
          Function.update_self] at h'
        exact hnoe r h'.symm
    | cons φ =>
      simp only [hact]
      refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
      intro h
      have h' := congrFun (congrArg Config.pol (List.mem_singleton.mp h)) e
      simp [Config.addLoc] at h'
    | gen s =>
      simp only [hact]
      exact List.nodup_singleton _
    | block =>
      simp only [hact]
      exact List.nodup_singleton _
    | error =>
      simp only [hact]
      exact List.nodup_singleton _

/-- A step needs a next event: a full configuration has no step. -/
theorem Step.not_full {c c' : Config} (h : Step P (M.sym S) τ c c') : ¬ P.Full c.abs := by
  obtain ⟨e, k, hs⟩ := h
  have hnext : P.IsNext c.abs e := by
    cases k with
    | nr => exact hs.nr_inv.2.1
    | rv r =>
      obtain ⟨wp, -, -, h, -⟩ := hs.rv_inv
      exact h
  intro hf
  rw [Full] at hf
  have := hnext.1
  rw [hf] at this
  cases this

/-! ### Statements -/

/-- Theorem A.27 with its bound. -/
theorem terminates_bound {n : ℕ} (hn : P.Bounded n) (p : List Config) (c : Config)
    (hp : Maz.Path (Step P (M.sym S) τ) (Config.init P.mem) p c) : p.length ≤ P.bound n := by
  unfold Program.bound
  obtain ⟨p', rw, hp', hl⟩ := lift_path hp ∅
  rw [← hl]
  refine Maz.Path.length_le_of_bounded_measure (measureRW (n * P.threads.length)) _ ?_ ?_ hp'
  · intro x y hx hs
    exact StepRW.measure_lt (K := n * P.threads.length) hx ((ReachRW.reach hx).card_le hn) hs
  · intro x hx
    have hD1 := (ReachRW.a21_aux hx).1
    have hcard := (ReachRW.reach hx).card_le hn
    have hrw : x.2.card ≤ x.1.abs.events.card := by
      apply Finset.card_le_card
      intro w hw
      exact List.mem_toFinset.mpr (hD1 w hw)
    unfold measureRW
    have := Nat.mul_le_mul_right (n * P.threads.length + 1) (le_trans hrw hcard)
    omega

/-- `succs` lists the steps from a well-formed configuration. -/
theorem mem_succs {c c' : Config} (hc : c.Wf) :
    c' ∈ succs P (M.sym S) τ c ↔ Step P (M.sym S) τ c c' := by
  classical
  unfold succs
  rw [List.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    exact of_decide_eq_true h
  · intro h
    exact ⟨mem_cands_of_step hc h, decide_eq_true h⟩

/-- Each step is listed once. -/
theorem succs_nodup {c : Config} (hc : c.Wf) : (succs P (M.sym S) τ c).Nodup :=
  (cands_nodup hc).filter _

/-- The graphs reported from a reached configuration `c` to depth `f`: the
graphs of the full configurations reached from `c` in fewer than `f` steps. -/
theorem mem_exploreFrom {c : Config} (hc : Reach P (M.sym S) τ c) (f : ℕ) (G : Graph) :
    G ∈ exploreFrom P (M.sym S) τ f c ↔
      ∃ p c', Maz.Path (Step P (M.sym S) τ) c p c' ∧ p.length < f ∧ P.Full c'.abs ∧ c'.abs = G := by
  induction f generalizing c with
  | zero =>
    simp only [exploreFrom, List.not_mem_nil, false_iff]
    rintro ⟨p, c', -, h, -⟩
    exact Nat.not_lt_zero _ h
  | succ f ih =>
    have hcw := hc.sound.1
    unfold exploreFrom
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc.sound.2.2.1)]
    by_cases hnx : P.nextC c = none
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hnx), List.mem_singleton]
      have hfull := (nextC_eq_none_iff hcw).mp hnx
      constructor
      · rintro rfl
        exact ⟨[], c, Maz.Path.nil c, Nat.succ_pos _, hfull, rfl⟩
      · rintro ⟨p, c', hp, -, -, rfl⟩
        cases hp with
        | nil => rfl
        | cons hstep _ => exact absurd hfull hstep.not_full
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hnx), List.mem_flatMap]
      constructor
      · rintro ⟨c1, hc1, hG⟩
        have hstep := (mem_succs hcw).mp hc1
        obtain ⟨p, c', hp, hl, hfull, rfl⟩ := (ih (hc.tail hstep)).mp hG
        exact ⟨c1 :: p, c', Maz.Path.cons hstep hp, Nat.succ_lt_succ hl, hfull, rfl⟩
      · rintro ⟨p, c', hp, hl, hfull, rfl⟩
        cases hp with
        | nil => exact absurd ((nextC_eq_none_iff hcw).mpr hfull) hnx
        | @cons _ c1 _ p' hstep hrest =>
          exact ⟨c1, (mem_succs hcw).mpr hstep,
            (ih (hc.tail hstep)).mpr ⟨p', c', hrest, Nat.lt_of_succ_lt_succ hl, hfull, rfl⟩⟩

theorem exploreFrom_nodup {c : Config} (hc : Reach P (M.sym S) τ c) (f : ℕ) :
    (exploreFrom P (M.sym S) τ f c).Nodup := by
  induction f generalizing c with
  | zero => exact List.nodup_nil
  | succ f ih =>
    have hcw := hc.sound.1
    unfold exploreFrom
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc.sound.2.2.1)]
    by_cases hnx : P.nextC c = none
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hnx)]
      exact List.nodup_singleton _
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hnx)]
      refine List.nodup_flatMap.mpr
        ⟨fun c1 hc1 => ih (hc.tail ((mem_succs hcw).mp hc1)), ?_⟩
      refine List.Pairwise.imp_of_mem (fun {c1 c2} h1 h2 hne => ?_) (succs_nodup hcw)
      intro G hG1 hG2
      have hs1 := (mem_succs hcw).mp h1
      have hs2 := (mem_succs hcw).mp h2
      obtain ⟨p1, c1', hp1, -, -, hG1'⟩ := (mem_exploreFrom (hc.tail hs1) f G).mp hG1
      obtain ⟨p2, c2', hp2, -, -, hG2'⟩ := (mem_exploreFrom (hc.tail hs2) f G).mp hG2
      obtain ⟨q0, hq0⟩ := Maz.Path.of_reflTransGen hc
      have hfull1 := hq0.append (Maz.Path.cons hs1 hp1)
      have hfull2 := hq0.append (Maz.Path.cons hs2 hp2)
      have heq := path_unique hfull1 hfull2 (hG1'.trans hG2'.symm)
      exact hne (List.cons.inj (List.append_cancel_left heq)).1

/-- Soundness of the explorer, for every program and model: a reported graph
is a well-formed, consistent, full execution. -/
theorem explore_sound {n : ℕ} {G : Graph} (h : G ∈ explore P (M.sym S) τ n) :
    G.Wf ∧ P.Exec G ∧ (M.sym S).cons G ∧ P.Full G := by
  unfold explore at h
  obtain ⟨p, c', hp, -, hfull, rfl⟩ := (mem_exploreFrom Relation.ReflTransGen.refl _ _).mp h
  exact Reach.sound_full hp.reflTransGen hfull

/-- The explorer reports no graph twice, for every program and model. -/
theorem explore_nodup (n : ℕ) : (explore P (M.sym S) τ n).Nodup :=
  exploreFrom_nodup Relation.ReflTransGen.refl _

/-- The specification of the explorer: for a bounded program and a maximally
extensible model, `explore` lists, without repetition, exactly the
well-formed, consistent, full executions of the program. -/
theorem explore_spec {n : ℕ} (hn : P.Bounded n) (hM : M.Extensible) :
    (explore P (M.sym S) τ n).Nodup ∧
      ∀ G, G ∈ explore P (M.sym S) τ n ↔ G.Wf ∧ P.Exec G ∧ (M.sym S).cons G ∧ P.Full G := by
  have h0 : Reach P (M.sym S) τ (Config.init P.mem) := Relation.ReflTransGen.refl
  refine ⟨explore_nodup n, fun G => ⟨explore_sound, ?_⟩⟩
  unfold explore
  rw [mem_exploreFrom h0]
  · rintro ⟨hW, hE, hc, hfull⟩
    obtain ⟨c, hreach, rfl⟩ := complete hn hM hW hE hc hfull
    obtain ⟨p, hp⟩ := Maz.Path.of_reflTransGen hreach
    exact ⟨p, c, hp, Nat.lt_succ_of_le (terminates_bound hn p c hp), hfull, rfl⟩

end Condpor
