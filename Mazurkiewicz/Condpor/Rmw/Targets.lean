import Mazurkiewicz.Condpor.Rmw.LocksEx3
import Mazurkiewicz.Condpor.Rmw.LocksEx4

/-!
# Reference outputs for JMC: an executable copy of `exploreAt`, proved equal

`exploreAt P eqOracleSe n` (`Rmw/ExploreC.lean`) cannot be compiled: its
implicit tie-break `TieBreak.se EqSem.solver` is `noncomputable` (it decides
satisfiability classically). The explorer itself uses only the oracle's two
Boolean functions, which are computable.

* `seC`, `oracleC`: the tie-break `se` with the computable choice `eqSatB`, and
  the oracle with the same two functions as `eqOracleSe`.
* `exploreAt_congr`: two oracles with the same functions give the same
  explorer. Hence `exploreAt_oracleC`: `exploreAt P oracleC n = exploreAt P
  eqOracleSe n` for every lock program, as a theorem.
* `exploreCfgAt`: the same recursion, returning the configurations (graph and
  insertion order) instead of the graphs; `exploreCfgAt_abs`: their graphs are
  the list of `exploreAt`; `mem_exploreCfgAt`: each one is reached by the
  proved transition relation and full.
* `visitAt`: every configuration that the recursion visits and finds
  consistent (for witnesses); `mem_visitAt`: each one is reached.
* `classOf`: the class of a full graph of a lock program (MODEL §5).
* `revDiag`: the outcome of every revisit candidate of the next write, with the
  failing predicate; it is built from the tests of `revisitOKB` and
  `maxAddedB` (`revisitOKB_split`, `maxAddedB_split`).
-/

namespace Condpor

namespace Targets

open Program

/-! ### A computable tie-break equal to `se` -/

/-- `TieBreak.se EqSem.solver` with the computable choice. -/
def seC : TieBreak EqSem.solver where
  inv := fun _ F => EqSem.solver.sat F
  pref := fun _ F φ => eqSatB (insert (φ, true) F)
  inv_ctx := fun h => h
  inv_sat := fun h => h
  inv_step := by
    intro K F φ h
    cases hs : eqSatB (insert (φ, true) F) with
    | true => exact (eqSatB_iff _).mp hs
    | false =>
      have hn : ¬ EqSem.solver.sat (insert (φ, true) F) := fun h' => by
        rw [← eqSatB_iff] at h'
        rw [hs] at h'
        cases h'
      exact (EqSem.solver.sat_split φ h).resolve_left hn

/-- `seC` is `TieBreak.se EqSem.solver`. -/
theorem seC_eq : seC = TieBreak.se EqSem.solver := by
  have hp : seC.pref = (TieBreak.se EqSem.solver).pref := by
    funext K F φ
    rw [Bool.eq_iff_iff, TieBreak.se_pref_iff]
    exact eqSatB_iff _
  have hi : seC.inv = (TieBreak.se EqSem.solver).inv := rfl
  cases h1 : seC
  cases h2 : TieBreak.se EqSem.solver
  rw [h1, h2] at hp hi
  simp only at hp hi
  subst hp hi
  rfl

/-- The oracle with the functions of `eqOracleSe`, for the computable tie-break. -/
def oracleC : Oracle seC where
  satB := eqSatB
  satB_iff := eqSatB_iff
  prefB := fun _ F φ => eqSatB (insert (φ, true) F)
  prefB_eq := fun _ _ _ => rfl

/-! ### The explorer depends only on the functions of the oracle -/

section congr

variable {S₁ S₂ : Solver} {τ₁ : TieBreak S₁} {τ₂ : TieBreak S₂} (P : XProgram)
  (O₁ : Oracle τ₁) (O₂ : Oracle τ₂)

theorem consX_congr (hs : O₁.satB = O₂.satB) (c : Config) : c.consX P O₁ = c.consX P O₂ := by
  unfold Config.consX
  rw [hs]

theorem succsAt_congr (hs : O₁.satB = O₂.satB) (hp : O₁.prefB = O₂.prefB) (c : Config) :
    succsAt P O₁ c = succsAt P O₂ c := by
  unfold succsAt
  simp only [consX_congr P O₁ O₂ hs, hp]

theorem exploreFromAt_congr (hs : O₁.satB = O₂.satB) (hp : O₁.prefB = O₂.prefB) (f : ℕ)
    (c : Config) : exploreFromAt P O₁ f c = exploreFromAt P O₂ f c := by
  induction f generalizing c with
  | zero => rfl
  | succ f ih =>
    unfold exploreFromAt
    rw [consX_congr P O₁ O₂ hs, succsAt_congr P O₁ O₂ hs hp, funext ih]

theorem exploreAt_congr (hs : O₁.satB = O₂.satB) (hp : O₁.prefB = O₂.prefB) (n : ℕ) :
    exploreAt P O₁ n = exploreAt P O₂ n :=
  exploreFromAt_congr P O₁ O₂ hs hp _ _

theorem deadFromAt_congr (hs : O₁.satB = O₂.satB) (hp : O₁.prefB = O₂.prefB) (f : ℕ)
    (c : Config) : deadFromAt P O₁ f c = deadFromAt P O₂ f c := by
  induction f generalizing c with
  | zero => rfl
  | succ f ih =>
    unfold deadFromAt
    rw [consX_congr P O₁ O₂ hs, succsAt_congr P O₁ O₂ hs hp, funext ih]

end congr

/-- The executable explorer is the proved one. -/
theorem exploreAt_oracleC (P : XProgram) (n : ℕ) :
    exploreAt P oracleC n = exploreAt P eqOracleSe n :=
  exploreAt_congr P oracleC eqOracleSe rfl rfl n

theorem deadAt_oracleC (P : XProgram) (n : ℕ) :
    deadAt P oracleC n = deadAt P eqOracleSe n :=
  deadFromAt_congr P oracleC eqOracleSe rfl rfl _ _

theorem succsAt_oracleC (P : XProgram) (c : Config) :
    succsAt P oracleC c = succsAt P eqOracleSe c :=
  succsAt_congr P oracleC eqOracleSe rfl rfl c

/-! ### The explorer on configurations -/

variable {S : Solver} {τ : TieBreak S}

/-- `exploreFromAt`, returning the full configurations. -/
def exploreCfgFrom (P : XProgram) (O : Oracle τ) : ℕ → Config → List Config
  | 0, _ => []
  | f + 1, c =>
    if c.consX P O then
      if P.nextC c = none then [c] else (succsAt P O c).flatMap (exploreCfgFrom P O f)
    else []

/-- The full configurations of `exploreAt`, in its order. -/
def exploreCfgAt (P : XProgram) (O : Oracle τ) (n : ℕ) : List Config :=
  exploreCfgFrom P O (P.toProgram.bound n + 1) (Config.init P.mem)

theorem exploreCfgFrom_abs (P : XProgram) (O : Oracle τ) (f : ℕ) (c : Config) :
    (exploreCfgFrom P O f c).map Config.abs = exploreFromAt P O f c := by
  induction f generalizing c with
  | zero => rfl
  | succ f ih =>
    unfold exploreCfgFrom exploreFromAt
    split_ifs
    · rfl
    · rw [List.map_flatMap]
      simp only [ih]
    · rfl

/-- The graphs of the configurations are the list of the proved explorer. -/
theorem exploreCfgAt_abs (P : XProgram) (n : ℕ) :
    (exploreCfgAt P oracleC n).map Config.abs = exploreAt P eqOracleSe n := by
  rw [← exploreAt_oracleC]
  exact exploreCfgFrom_abs P oracleC _ _

theorem exploreCfgFrom_congr {S₁ S₂ : Solver} {τ₁ : TieBreak S₁} {τ₂ : TieBreak S₂}
    (P : XProgram) (O₁ : Oracle τ₁) (O₂ : Oracle τ₂) (hs : O₁.satB = O₂.satB)
    (hp : O₁.prefB = O₂.prefB) (f : ℕ) (c : Config) :
    exploreCfgFrom P O₁ f c = exploreCfgFrom P O₂ f c := by
  induction f generalizing c with
  | zero => rfl
  | succ f ih =>
    unfold exploreCfgFrom
    rw [consX_congr P O₁ O₂ hs, succsAt_congr P O₁ O₂ hs hp, funext ih]

/-- Every configuration of `exploreCfgFrom` is reached and full. -/
theorem mem_exploreCfgFrom (P : XProgram) (O : Oracle τ) {c : Config}
    (hc : Reach P.toProgram ((Model.atomic P SC).sym S) τ c) (f : ℕ) {d : Config}
    (h : d ∈ exploreCfgFrom P O f c) :
    Reach P.toProgram ((Model.atomic P SC).sym S) τ d ∧ P.toProgram.Full d.abs := by
  induction f generalizing c with
  | zero => simp [exploreCfgFrom] at h
  | succ f ih =>
    obtain ⟨hcw, hpo, hcons, -⟩ := hc.sound
    unfold exploreCfgFrom at h
    rw [ite_eq_left_of_eq_true _ _ (eq_true ((c.consX_iff P O hcw.1).mpr hcons))] at h
    by_cases hnx : P.nextC c = none
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hnx)] at h
      have hd : d = c := List.mem_singleton.mp h
      subst hd
      exact ⟨hc, (nextC_eq_none_iff hcw).mp hnx⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hnx)] at h
      obtain ⟨c1, hc1, hd⟩ := List.mem_flatMap.mp h
      rw [succsAt_eq O hcw hpo hcons] at hc1
      exact ih (hc.tail ((mem_succs hcw).mp hc1)) hd

/-- Every configuration of `exploreCfgAt` is reached by the proved transition
relation (with the tie-break `se`) and full. -/
theorem mem_exploreCfgAt (P : XProgram) (n : ℕ) {d : Config}
    (h : d ∈ exploreCfgAt P oracleC n) :
    Reach P.toProgram ((Model.atomic P SC).sym EqSem.solver) (TieBreak.se EqSem.solver) d ∧
      P.toProgram.Full d.abs := by
  unfold exploreCfgAt at h
  rw [exploreCfgFrom_congr P oracleC eqOracleSe rfl rfl] at h
  exact mem_exploreCfgFrom P eqOracleSe Relation.ReflTransGen.refl _ h

/-- Every configuration that the recursion visits and finds consistent, in
visiting order (pre-order). -/
def visitFrom (P : XProgram) (O : Oracle τ) : ℕ → Config → List Config
  | 0, _ => []
  | f + 1, c =>
    if c.consX P O then
      if P.nextC c = none then [c] else c :: (succsAt P O c).flatMap (visitFrom P O f)
    else []

def visitAt (P : XProgram) (O : Oracle τ) (n : ℕ) : List Config :=
  visitFrom P O (P.toProgram.bound n + 1) (Config.init P.mem)

theorem visitFrom_congr {S₁ S₂ : Solver} {τ₁ : TieBreak S₁} {τ₂ : TieBreak S₂}
    (P : XProgram) (O₁ : Oracle τ₁) (O₂ : Oracle τ₂) (hs : O₁.satB = O₂.satB)
    (hp : O₁.prefB = O₂.prefB) (f : ℕ) (c : Config) :
    visitFrom P O₁ f c = visitFrom P O₂ f c := by
  induction f generalizing c with
  | zero => rfl
  | succ f ih =>
    unfold visitFrom
    rw [consX_congr P O₁ O₂ hs, succsAt_congr P O₁ O₂ hs hp, funext ih]

theorem mem_visitFrom (P : XProgram) (O : Oracle τ) {c : Config}
    (hc : Reach P.toProgram ((Model.atomic P SC).sym S) τ c) (f : ℕ) {d : Config}
    (h : d ∈ visitFrom P O f c) :
    Reach P.toProgram ((Model.atomic P SC).sym S) τ d := by
  induction f generalizing c with
  | zero => simp [visitFrom] at h
  | succ f ih =>
    obtain ⟨hcw, hpo, hcons, -⟩ := hc.sound
    unfold visitFrom at h
    rw [ite_eq_left_of_eq_true _ _ (eq_true ((c.consX_iff P O hcw.1).mpr hcons))] at h
    by_cases hnx : P.nextC c = none
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hnx)] at h
      rw [List.mem_singleton.mp h]
      exact hc
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hnx)] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact hc
      obtain ⟨c1, hc1, hd⟩ := List.mem_flatMap.mp h
      rw [succsAt_eq O hcw hpo hcons] at hc1
      exact ih (hc.tail ((mem_succs hcw).mp hc1)) hd

/-- Every configuration of `visitAt` is reached by the proved transition
relation. Its successors are `succsAt`, which is `succs` there (`succsAt_eq`). -/
theorem mem_visitAt (P : XProgram) (n : ℕ) {d : Config} (h : d ∈ visitAt P oracleC n) :
    Reach P.toProgram ((Model.atomic P SC).sym EqSem.solver) (TieBreak.se EqSem.solver) d := by
  unfold visitAt at h
  rw [visitFrom_congr P oracleC eqOracleSe rfl rfl] at h
  exact mem_visitFrom P eqOracleSe Relation.ReflTransGen.refl _ h

/-! ### Classes of full graphs of lock programs (MODEL §5) -/

/-- The events of thread `t` of a configuration, by index. -/
def thEvents (c : Config) (t : Tid) : List TEv :=
  (List.range (c.cnt t)).filterMap (c.evAt t)

/-- The thread ends with a `block` event. -/
def blockedB (c : Config) (t : Tid) : Bool :=
  match (thEvents c t).getLast? with
  | some e => decide (e.act = .block)
  | none => false

/-- The read after which thread `t` blocks: its last read. -/
def blockingRead (c : Config) (t : Tid) : Option TEv :=
  ((thEvents c t).filter (fun e => match e.act with
    | .read _ => true
    | _ => false)).getLast?

/-- The co-maximal write of `x`. -/
def coMax (c : Config) (x : Loc) : Ev :=
  match (c.co x).getLast? with
  | some w => .th w
  | none => .init

/-- A blocked read is final: it reads the co-maximal write of its location. -/
def finalB (c : Config) (r : TEv) : Bool := decide (c.rf r = some (coMax c r.act.loc))

/-- Classes (MODEL §5). `dropped` and `bound` need timed waits; lock programs
have none. -/
inductive Cls
  | complete | dropped | bound | deadlock | exploration
  deriving DecidableEq, Repr

def Cls.name : Cls → String
  | .complete => "complete" | .dropped => "dropped" | .bound => "bound"
  | .deadlock => "deadlock" | .exploration => "exploration"

/-- The class of a full configuration of the threads `ts`: no blocked thread:
complete; every blocking read final: deadlock; otherwise exploration. -/
def classOf (ts : List Tid) (c : Config) : Cls :=
  let bl := ts.filter (blockedB c)
  if bl = [] then .complete
  else if bl.all (fun t => match blockingRead c t with
      | some r => finalB c r
      | none => false) then .deadlock
  else .exploration

/-- Counts per class: complete, dropped, bound, deadlock, exploration. -/
def classCounts (ts : List Tid) (l : List Config) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  let k := fun (x : Cls) => (l.filter (fun c => decide (classOf ts c = x))).length
  (k .complete, k .dropped, k .bound, k .deadlock, k .exploration)

/-- Assumption A6 on one full configuration: a thread that does not end
blocked has no next action in the code (it is not cut by `n`); a thread that
ends blocked has at least one `block` event. Checked on every listed graph. -/
def cutOkB (code : Tid → List LOp) (ts : List Tid) (c : Config) : Bool :=
  ts.all (fun t => blockedB c t || decide ((lockState (code t) (c.trace t)).act = none))

/-! ### Revisit candidates and the failing predicate -/

/-- Why a revisit candidate `r` of the next write `w` is rejected, or `ok`. -/
inductive Rej
  /-- `r` is `porf`-before `w` -/
  | porf
  /-- the event `d` (deleted, or `r` itself) fails condition (a), (b) or (c) of L5 -/
  | maxA (d : TEv) | maxB (d : TEv) | maxC (d : TEv)
  deriving DecidableEq, Repr

/-- L5 (a) as in `maxAddedB`: no read of `Previous(d, w)` reads from `d`. -/
def condA (c : Config) (d w : TEv) : Bool :=
  !(c.order.any (fun q => c.previousB d w (.th q) && decide (c.rf q = some (.th d))))

/-- L5 (b) as in `maxAddedB`. -/
def condB (c : Config) (d w : TEv) : Bool :=
  match d.act with
  | .read _ =>
    (match c.rf d with
      | none => false
      | some e' =>
        c.previousB d w e' &&
          !((c.abs.co d.loc).any (fun w'' =>
            c.previousB d w (.th w'') && decide (c.abs.coRelAt d.loc e' (.th w'')))))
  | .write _ _ =>
    c.previousB d w (.th d) &&
      !((c.abs.co d.loc).any (fun w'' =>
        c.previousB d w (.th w'') && decide (c.abs.coRelAt d.loc (.th d) (.th w''))))
  | _ => true

/-- L5 (c) as in `maxAddedB`. -/
def condC (pb : Finset Lit → SExpr → Bool) (c : Config) (d w : TEv) : Bool :=
  match d.act with
  | .cons φ => decide (c.pol d = some (pb (c.prevFC d w) φ))
  | _ => true

theorem maxAddedB_split (pb : Finset Lit → SExpr → Bool) (c : Config) (d w : TEv) :
    c.maxAddedB pb d w = (condA c d w && condB c d w && condC pb c d w) := by
  unfold Config.maxAddedB condA condB condC
  cases d.act <;> simp <;> rfl

/-- The events tested by `revisitOKB` (deleted ones and `r`), oldest first. -/
def testedEvents (c : Config) (r w : TEv) : List TEv :=
  c.order.reverse.filter (fun d => c.deletedB r w d || decide (d = r))

theorem revisitOKB_split (prefB : Finset Lit → Finset Lit → SExpr → Bool) (c : Config)
    (r w : TEv) :
    c.revisitOKB prefB r w =
      (!c.plusPorfB w (.th r) (.th w) &&
        (testedEvents c r w).all (fun d => c.maxAddedB (prefB (c.ctxC r w)) d w)) := by
  unfold Config.revisitOKB testedEvents
  congr 1
  rw [List.all_filter, List.all_reverse]

/-- All failures of the candidate `r` for the next write `w`, in the order:
`porf`; then for each tested event, oldest first, the failing conditions among
(a), (b), (c). Empty iff `revisitOKB` passes (`revDiag_nil_iff`). -/
def revDiag (O : Oracle τ) (c : Config) (r w : TEv) : List Rej :=
  (if c.plusPorfB w (.th r) (.th w) then [Rej.porf] else []) ++
    (testedEvents c r w).flatMap (fun d =>
      (if condA c d w then [] else [Rej.maxA d]) ++
      (if condB c d w then [] else [Rej.maxB d]) ++
      (if condC (O.prefB (c.ctxC r w)) c d w then [] else [Rej.maxC d]))

theorem revDiag_nil_iff (O : Oracle τ) (c : Config) (r w : TEv) :
    revDiag O c r w = [] ↔ c.revisitOKB O.prefB r w = true := by
  rw [revisitOKB_split]
  unfold revDiag
  simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff, Bool.and_eq_true,
    Bool.not_eq_true', List.all_eq_true, maxAddedB_split]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun d hd => ?_⟩
    · cases h : c.plusPorfB w (.th r) (.th w) <;> simp_all
    · obtain ⟨⟨ha, hb⟩, hc⟩ := h2 d hd
      revert ha hb hc
      cases condA c d w <;> cases condB c d w <;> cases condC (O.prefB (c.ctxC r w)) c d w <;>
        simp
  · rintro ⟨h1, h2⟩
    refine ⟨by simp [h1], fun d hd => ?_⟩
    have := h2 d hd
    revert this
    cases condA c d w <;> cases condB c d w <;> cases condC (O.prefB (c.ctxC r w)) c d w <;>
      simp


/-! ### Raw listings (plain data, for the JSON files and for kernel checks) -/

/-- An event of a listing. `kind`: 0 `R`, 1 `W`, 2 `RX`, 3 `WX`, 4 `C`, 5 `B`,
6 `E`, 7 `G`. `val`: the value read or written, `1`/`0` for the outcome of a
`C`, `0` otherwise. `rf`: for a read, `some none` for `init`, `some (some
(t, i))` for a thread write; `none` for other events. `phi`: the formula of a
`C`. -/
structure REv where
  t : ℕ
  i : ℕ
  kind : ℕ
  loc : ℕ
  val : ℕ
  rf : Option (Option (ℕ × ℕ))
  phi : ℕ
  deriving DecidableEq, Repr

/-- A listing: events by thread and index, insertion order (oldest first),
coherence per location, blocked threads, class. -/
structure RGraph where
  evs : List REv
  order : List (ℕ × ℕ)
  co : List (ℕ × List (ℕ × ℕ))
  blocked : List ℕ
  cls : Cls
  deriving DecidableEq, Repr

def evId (e : TEv) : ℕ × ℕ := (e.tid, e.idx)

def rawEv (P : XProgram) (c : Config) (e : TEv) : REv :=
  let ex := P.ex e.tid (c.traceBeforeC e.tid e.idx)
  match e.act with
  | .read x =>
    ⟨e.tid, e.idx, if ex then 2 else 0, x, (c.abs.ret e).getD 0,
      some ((c.rf e).bind (fun s => match s with
        | .init => none
        | .th q => some (evId q))), 0⟩
  | .write x v => ⟨e.tid, e.idx, if ex then 3 else 1, x, v, none, 0⟩
  | .cons φ => ⟨e.tid, e.idx, 4, 0, (c.abs.ret e).getD 0, none, φ⟩
  | .block => ⟨e.tid, e.idx, 5, 0, 0, none, 0⟩
  | .error => ⟨e.tid, e.idx, 6, 0, 0, none, 0⟩
  | .gen s => ⟨e.tid, e.idx, 7, 0, 0, none, s⟩

/-- The listing of a configuration of the threads `ts` with the locations
`locs`. -/
def rawOf (P : XProgram) (ts : List Tid) (locs : List Loc) (c : Config) : RGraph :=
  ⟨ts.flatMap (fun t => (thEvents c t).map (rawEv P c)), c.order.reverse.map evId,
    locs.map (fun x => (x, (c.co x).map evId)), ts.filter (blockedB c), classOf ts c⟩

end Targets

end Condpor
