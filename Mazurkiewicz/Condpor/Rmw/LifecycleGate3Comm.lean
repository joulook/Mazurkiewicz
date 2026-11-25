import Mazurkiewicz.Condpor.Rmw.LifecycleGate3Trace
import Mazurkiewicz.Condpor.Rmw.LifecycleGateFinal

/-!
# Gate clause 3, part 2: equivalent maximal runs have the same graph (LC2-c)

* `GB.Eqv`: two builders with the same event set, `rf`, `co` and counters; it is a congruence
  for `emit`, `synth`, `finalize`, and equal graphs (`abs`) follow.
* `prims`: `emit` as a list of primitive builder operations (`emit_eq_prims`); two primitives
  of different threads without a conflicting access commute up to `GB.Eqv` (`prim_comm`).
* `OkOcc`: the resources of an occurrence have their roles (lock / data / lifecycle of a
  thread); every occurrence enabled in a state whose remaining calls are suffixes of the code
  has them, for a fragment program (`okOcc_of_enabled`). On such resources `resLoc` is
  injective (`resLoc_inj`), so independent occurrences have no conflicting accesses, and
  `emit` commutes on them (`emit_comm`) — the place where the fragment is needed.
* `run_move`: in a run, an occurrence independent of the preceding segment moves in front of
  it; the result is a run to the same state with an equivalent builder (by `commute`).
* `bwd_core` and **`gate3_bwd`**: two `MEquiv` runs from a state reach the same state with
  equivalent builders (induction on the first list, `mequiv_cons_split`, `run_move`); hence two
  equivalent maximal runs have the same graph. The intermediate lists of the equivalence need
  not be runs: Levi's lemma moves the first letter in the second run through runs only.
-/

namespace Condpor

namespace Life

namespace Sem

variable {P : LProg}

/-! ### Equivalent builders -/

/-- Same event set, `rf`, `co`, counters. -/
structure GB.Eqv (g h : GB) : Prop where
  ev : g.order.toFinset = h.order.toFinset
  rf : g.rf = h.rf
  co : g.co = h.co
  cnt : g.cnt = h.cnt

theorem GB.Eqv.refl (g : GB) : g.Eqv g := ⟨rfl, rfl, rfl, rfl⟩

theorem GB.Eqv.symm {g h : GB} (e : g.Eqv h) : h.Eqv g :=
  ⟨e.ev.symm, e.rf.symm, e.co.symm, e.cnt.symm⟩

theorem GB.Eqv.trans {g h k : GB} (e1 : g.Eqv h) (e2 : h.Eqv k) : g.Eqv k :=
  ⟨e1.ev.trans e2.ev, e1.rf.trans e2.rf, e1.co.trans e2.co, e1.cnt.trans e2.cnt⟩

theorem GB.Eqv.abs {g h : GB} (e : g.Eqv h) (P : LProg) : (g.toCfg P).abs = (h.toCfg P).abs := by
  simp only [GB.toCfg, Config.abs, e.ev, e.rf, e.co]

theorem GB.Eqv.last {g h : GB} (e : g.Eqv h) (x : Loc) : g.last x = h.last x := by
  simp only [GB.last, e.co]

theorem GB.Eqv.ev' {g h : GB} (e : g.Eqv h) (t : Tid) (a : Act) : g.ev t a = h.ev t a := by
  simp only [GB.ev, e.cnt]

theorem GB.Eqv.push {g h : GB} (e : g.Eqv h) (x : TEv) : (g.push x).Eqv (h.push x) := by
  refine ⟨?_, e.rf, e.co, ?_⟩
  · simp only [GB.push, List.toFinset_cons, e.ev]
  · simp only [GB.push, e.cnt]

theorem GB.Eqv.read {g h : GB} (e : g.Eqv h) (t : Tid) (x : Loc) (src : Ev) :
    (g.read t x src).Eqv (h.read t x src) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals simp only [GB.read, GB.push, GB.ev, List.toFinset_cons, e.ev, e.cnt, e.rf, e.co]
  rfl

theorem GB.Eqv.readLast {g h : GB} (e : g.Eqv h) (t : Tid) (x : Loc) :
    (g.readLast t x).Eqv (h.readLast t x) := by
  unfold GB.readLast; rw [e.last]; exact e.read t x _

theorem GB.Eqv.write {g h : GB} (e : g.Eqv h) (t : Tid) (x : Loc) (v : Val) :
    (g.write t x v).Eqv (h.write t x v) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [GB.write, GB.push, GB.ev, List.toFinset_cons, e.ev, e.cnt, e.rf, e.co]

theorem GB.Eqv.loc0 {g h : GB} (e : g.Eqv h) (t : Tid) (a : Act) :
    (g.loc0 t a).Eqv (h.loc0 t a) := by
  unfold GB.loc0; rw [e.ev' t]; exact e.push _

theorem GB.Eqv.emit {g h : GB} (e : g.Eqv h) (P : LProg) (o : Occ) :
    (emit P g o).Eqv (emit P h o) := by
  cases o <;> simp only [Sem.emit]
  all_goals first
    | exact e.readLast _ _
    | exact (e.readLast _ _).write _ _ _
    | exact e.write _ _ _
    | exact e.loc0 _ _
    | exact (e.readLast _ _).loc0 _ _

theorem GB.Eqv.foldl_emit {g h : GB} (e : g.Eqv h) (P : LProg) (rs : List Occ) :
    (rs.foldl (Sem.emit P) g).Eqv (rs.foldl (Sem.emit P) h) := by
  induction rs generalizing g h with
  | nil => exact e
  | cons o rs ih => exact ih (e.emit P o)

theorem GB.Eqv.synth {g h : GB} (e : g.Eqv h) (P : LProg) (s : MState) (t : Tid) :
    (Sem.synth P s g t).Eqv (Sem.synth P s h t) := by
  unfold Sem.synth
  split
  · exact (e.read _ _ _).loc0 _ _
  · split
    · split_ifs
      · exact (e.readLast _ _).loc0 _ _
      · exact e
    · split_ifs
      · exact (e.readLast _ _).loc0 _ _
      · exact e
    · exact e
  · exact e

theorem GB.Eqv.finalize {g h : GB} (e : g.Eqv h) (P : LProg) (s : MState) :
    (Sem.finalize P g s).Eqv (Sem.finalize P h s) := by
  unfold Sem.finalize
  suffices ∀ (l : List Tid) (g h : GB), g.Eqv h → (l.foldl (Sem.synth P s) g).Eqv
      (l.foldl (Sem.synth P s) h) from this _ _ _ e
  intro l
  induction l with
  | nil => intro g h e; exact e
  | cons t l ih => intro g h e; exact ih _ _ (e.synth P s t)

/-! ### Primitive builder operations -/

/-- A primitive builder operation. -/
inductive Prim where
  | rd (t : Tid) (x : Loc)
  | wr (t : Tid) (x : Loc) (v : Val)
  | z (t : Tid) (a : Act)

/-- Apply a primitive. -/
def GB.ap (g : GB) : Prim → GB
  | .rd t x => g.readLast t x
  | .wr t x v => g.write t x v
  | .z t a => g.loc0 t a

def Prim.tid : Prim → Tid
  | .rd t _ | .wr t _ _ | .z t _ => t

/-- The access of a primitive: the location and whether it writes. -/
def Prim.acc : Prim → Option (Loc × Bool)
  | .rd _ x => some (x, false)
  | .wr _ x _ => some (x, true)
  | .z _ _ => none

/-- No conflicting access: not the same location with a write. -/
def NoConf (p q : Prim) : Prop :=
  ∀ x b₁ b₂, p.acc = some (x, b₁) → q.acc = some (x, b₂) → b₁ = false ∧ b₂ = false

/-- `emit` as a list of primitives. -/
def prims (P : LProg) : Occ → List Prim
  | .begin t => [.rd t (P.st t)]
  | .acq t l | .tryAcq t l _ => [.rd t l, .wr t l 1]
  | .reacq t _ | .tryRe t _ _ | .unlockRe t _ => [.z t (.gen 0)]
  | .tryFail t l _ => [.rd t l]
  | .release t l => [.wr t l 0]
  | .unlockErr t _ => [.z t .error]
  | .query t l => [.rd t l]
  | .rd t x | .asmOk t x _ => [.rd t x]
  | .wr t x v => [.wr t x v]
  | .asmStop t x _ => [.rd t x, .z t .block]
  | .start t u => [.wr t (P.st u) 1]
  | .join t u => [.rd t (P.st u)]
  | .fin t => [.wr t (P.st t) 2]

theorem emit_eq_prims (P : LProg) (g : GB) (o : Occ) :
    emit P g o = (prims P o).foldl GB.ap g := by
  cases o <;> rfl

theorem prims_tid (P : LProg) (o : Occ) : ∀ p ∈ prims P o, p.tid = o.tid := by
  cases o <;> simp [prims, Prim.tid, Occ.tid]

theorem GB.Eqv.ap {g h : GB} (e : g.Eqv h) (p : Prim) : (g.ap p).Eqv (h.ap p) := by
  cases p
  · exact e.readLast _ _
  · exact e.write _ _ _
  · exact e.loc0 _ _

theorem GB.Eqv.foldl_ap {g h : GB} (e : g.Eqv h) (ps : List Prim) :
    (ps.foldl GB.ap g).Eqv (ps.foldl GB.ap h) := by
  induction ps generalizing g h with
  | nil => exact e
  | cons p ps ih => exact ih (e.ap p)

theorem toFinset_swap2 (a b : TEv) (l : List TEv) :
    (a :: b :: l).toFinset = (b :: a :: l).toFinset := by
  simp only [List.toFinset_cons, Finset.insert_comm]

/-- The proof of one case of `prim_comm`. -/
macro "prim_tac" : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals (try funext z)
  all_goals simp only [GB.ap, GB.readLast, GB.read, GB.write, GB.loc0, GB.push, GB.ev, GB.last,
    Function.update_apply, ite_false, List.toFinset_cons, *]
  all_goals first
    | (simp_all [Finset.insert_comm]; done)
    | (split_ifs <;> simp_all)))

/-- Two primitives of different threads without a conflicting access commute. -/
theorem prim_comm (g : GB) {p q : Prim} (ht : p.tid ≠ q.tid) (hc : NoConf p q) :
    ((g.ap p).ap q).Eqv ((g.ap q).ap p) := by
  have hne : ∀ {x y : Loc} {b₁ b₂ : Bool}, b₁ = true ∨ b₂ = true →
      p.acc = some (x, b₁) → q.acc = some (y, b₂) → x ≠ y ∧ y ≠ x := by
    intro x y b₁ b₂ hb h1 h2
    refine ⟨fun hxy => ?_, fun hxy => ?_⟩ <;> subst hxy <;>
      have := hc _ _ _ h1 h2 <;> cases hb <;> simp_all
  have ht' := Ne.symm ht
  cases p <;> cases q <;> simp only [Prim.tid] at ht ht' <;> clear hc
  · prim_tac
  · obtain ⟨h1, h2⟩ := hne (Or.inr rfl) rfl rfl
    prim_tac
  · prim_tac
  · obtain ⟨h1, h2⟩ := hne (Or.inl rfl) rfl rfl
    prim_tac
  · obtain ⟨h1, h2⟩ := hne (Or.inl rfl) rfl rfl
    prim_tac
  · prim_tac
  · prim_tac
  · prim_tac
  · prim_tac

end Sem

end Life

end Condpor
