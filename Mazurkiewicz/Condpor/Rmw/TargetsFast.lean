import Mazurkiewicz.Condpor.Rmw.Targets

/-!
# A faster executable copy of `exploreAt`, proved equal

The tests of `Compute.lean` decide causality and acyclicity with `Maz.reachN`,
which enumerates every path of at most `n` steps: exponential in the length of
a thread (the program order is transitive). `reachNF` computes the same
function by iterating the set of nodes from which the target is reached, with
an early stop at a fixed point (`reachNF_eq`, an equation, no hypothesis).

Every function on the way from `exploreAt` to `reachN` is copied with
`reachNF` in place of `reachN` and proved equal to the original
(`*_eqF` theorems). The final statements:

* `exploreCfgAtF_eq`: `exploreCfgAtF P n = exploreCfgAt P oracleC n`; with
  `exploreCfgAt_abs`, `(exploreCfgAtF P n).map Config.abs = exploreAt P
  eqOracleSe n`.
* `mem_exploreCfgAtF`, `mem_visitAtF`: the listed configurations are reached.
* `deadAtF_eq`, `succsAtF_eq`.
-/

namespace Condpor

namespace Targets

open Program

/-! ### Reachability by iterated sets -/

section reach

variable {α : Type*} [DecidableEq α]

/-- One step backwards: the nodes with an edge to `b` or to a node of `B`. -/
def bstep (r : α → α → Bool) (nodes : List α) (b : α) (B : List α) : List α :=
  nodes.filter (fun m => r m b || B.any (r m))

/-- `f` iterated `k` times, stopping at a fixed point. -/
def iterStop (f : List α → List α) : ℕ → List α → List α
  | 0, x => x
  | k + 1, x => if f x = x then x else iterStop f k (f x)

theorem iterStop_eq (f : List α → List α) (k : ℕ) (x : List α) :
    iterStop f k x = f^[k] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    unfold iterStop
    split_ifs with h
    · rw [Function.iterate_succ_apply, h, Function.iterate_fixed h]
    · rw [ih, Function.iterate_succ_apply]

theorem filter_reachN (r : α → α → Bool) (nodes : List α) (b : α) (n : ℕ) :
    nodes.filter (fun m => Maz.reachN r nodes n m b) = (bstep r nodes b)^[n] [] := by
  induction n with
  | zero => simp [Maz.reachN]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih]
    unfold bstep
    congr 1
    funext m
    simp only [Maz.reachN, List.any_filter]
    congr 1
    congr 1
    funext m'
    rw [Bool.and_comm]

/-- `Maz.reachN`, computed by iterated sets. -/
def reachNF (r : α → α → Bool) (nodes : List α) : ℕ → α → α → Bool
  | 0, _, _ => false
  | n + 1, a, b => r a b || (iterStop (bstep r nodes b) n []).any (r a)

theorem reachNF_eq (r : α → α → Bool) (nodes : List α) (n : ℕ) (a b : α) :
    reachNF r nodes n a b = Maz.reachN r nodes n a b := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [reachNF, Maz.reachN, iterStop_eq, ← filter_reachN, List.any_filter]
    congr 1
    congr 1
    funext m
    rw [Bool.and_comm]

/-- `Maz.acyclicB`, computed by iterated sets. -/
def acyclicBF (r : α → α → Bool) (nodes : List α) : Bool :=
  nodes.all (fun a => !reachNF r nodes nodes.length a a)

theorem acyclicBF_eq (r : α → α → Bool) (nodes : List α) :
    acyclicBF r nodes = Maz.acyclicB r nodes := by
  unfold acyclicBF Maz.acyclicB
  simp only [reachNF_eq]

end reach

/-! ### The tests, with `reachNF` -/

def porfBF (G : Graph) (l : List TEv) (a b : Ev) : Bool :=
  reachNF G.porfStepB (l.map .th) (l.map Ev.th).length a b

theorem porfBF_eq (G : Graph) (l : List TEv) (a b : Ev) : porfBF G l a b = G.porfB l a b := by
  unfold porfBF Graph.porfB
  exact reachNF_eq _ _ _ _ _

def consCF (c : Config) : Bool := acyclicBF c.abs.scStepB (c.order.map .th)

theorem consCF_eq (c : Config) : consCF c = c.consC := by
  unfold consCF Config.consC Graph.consB
  exact acyclicBF_eq _ _

def plusPorfBF (c : Config) (w : TEv) (a b : Ev) : Bool := porfBF (c.plus w) (w :: c.order) a b

theorem plusPorfBF_eq (c : Config) (w : TEv) (a b : Ev) :
    plusPorfBF c w a b = c.plusPorfB w a b := by
  unfold plusPorfBF Config.plusPorfB
  exact porfBF_eq _ _ _ _

def deletedBF (c : Config) (r w d : TEv) : Bool :=
  decide (d ∈ c.order) && decide (c.order.Before d r) && !plusPorfBF c w (.th d) (.th w)

theorem deletedBF_eq (c : Config) (r w d : TEv) : deletedBF c r w d = c.deletedB r w d := by
  unfold deletedBF Config.deletedB
  rw [plusPorfBF_eq]

def keepCF (c : Config) (r w : TEv) : Finset TEv :=
  (c.order.filter (fun d => !deletedBF c r w d)).toFinset

theorem keepCF_eq (c : Config) (r w : TEv) : keepCF c r w = c.keepC r w := by
  unfold keepCF Config.keepC
  simp only [deletedBF_eq]

def revisitCF (c : Config) (r w : TEv) (wp : Ev) : Config :=
  let G' := ((c.abs.restrict (keepCF c r w)).addWrite w wp).setRF r (.th w)
  ⟨c.mem, w :: c.order.filter (fun d => decide (d ∈ keepCF c r w)), G'.rf, G'.co, G'.pol⟩

theorem revisitCF_eq (c : Config) (r w : TEv) : revisitCF c r w = c.revisitC r w := by
  funext wp
  unfold revisitCF Config.revisitC
  rw [keepCF_eq]

def previousBF (c : Config) (p w : TEv) : Ev → Bool
  | .init => true
  | .th q =>
    decide (q ∈ c.order) &&
      (decide (q = p) || decide (c.order.Before p q) || plusPorfBF c w (.th q) (.th w))

theorem previousBF_eq (c : Config) (p w : TEv) (x : Ev) :
    previousBF c p w x = c.previousB p w x := by
  cases x with
  | init => rfl
  | th q =>
    simp only [previousBF, Config.previousB, plusPorfBF_eq]

def ctxCF (c : Config) (r w : TEv) : Finset Lit := (c.abs.restrict (keepCF c r w)).F

theorem ctxCF_eq (c : Config) (r w : TEv) : ctxCF c r w = c.ctxC r w := by
  unfold ctxCF Config.ctxC
  rw [keepCF_eq]

def prevFCF (c : Config) (p w : TEv) : Finset Lit :=
  (c.abs.restrict
    (c.order.filter (fun q => decide (q ≠ p) && previousBF c p w (.th q))).toFinset).F

theorem prevFCF_eq (c : Config) (p w : TEv) : prevFCF c p w = c.prevFC p w := by
  unfold prevFCF Config.prevFC
  simp only [previousBF_eq]

def maxAddedBF (c : Config) (pb : Finset Lit → SExpr → Bool) (p w : TEv) : Bool :=
  !(c.order.any (fun q => previousBF c p w (.th q) && decide (c.rf q = some (.th p)))) &&
    (match p.act with
      | .read _ =>
        (match c.rf p with
          | none => false
          | some e' =>
            previousBF c p w e' &&
              !((c.abs.co p.loc).any (fun w'' =>
                previousBF c p w (.th w'') && decide (c.abs.coRelAt p.loc e' (.th w'')))))
      | .write _ _ =>
        previousBF c p w (.th p) &&
          !((c.abs.co p.loc).any (fun w'' =>
            previousBF c p w (.th w'') && decide (c.abs.coRelAt p.loc (.th p) (.th w''))))
      | .cons φ => decide (c.pol p = some (pb (prevFCF c p w) φ))
      | _ => true)

theorem maxAddedBF_eq (c : Config) (pb : Finset Lit → SExpr → Bool) (p w : TEv) :
    maxAddedBF c pb p w = c.maxAddedB pb p w := by
  unfold maxAddedBF Config.maxAddedB
  simp only [previousBF_eq, prevFCF_eq]
  rfl

def revisitOKBF (c : Config) (prefB : Finset Lit → Finset Lit → SExpr → Bool) (r w : TEv) :
    Bool :=
  !plusPorfBF c w (.th r) (.th w) &&
    c.order.all (fun d => !(deletedBF c r w d || decide (d = r)) ||
      maxAddedBF c (prefB (ctxCF c r w)) d w)

theorem revisitOKBF_eq (c : Config) (prefB : Finset Lit → Finset Lit → SExpr → Bool)
    (r w : TEv) : revisitOKBF c prefB r w = c.revisitOKB prefB r w := by
  unfold revisitOKBF Config.revisitOKB
  simp only [plusPorfBF_eq, deletedBF_eq, maxAddedBF_eq, ctxCF_eq]

/-! ### The explorer, with the faster tests -/

variable {S : Solver} {τ : TieBreak S}

def consXF (P : XProgram) (O : Oracle τ) (c : Config) : Bool :=
  consCF c && c.atomicB P && O.satB c.abs.F

theorem consXF_eq (P : XProgram) (O : Oracle τ) (c : Config) : consXF P O c = c.consX P O := by
  unfold consXF Config.consX
  rw [consCF_eq]

def succsAtF (P : XProgram) (O : Oracle τ) (c : Config) : List Config :=
  match P.nextC c with
  | none => []
  | some e =>
    match e.act with
    | .read x =>
      ((writesOf c.order x).filter (fun w => consXF P O (c.addRead e w))).map (c.addRead e)
    | .write x _ =>
      ((writesOf c.order x).filter (fun wp => consXF P O (c.addWrite e wp))).map
          (c.addWrite e) ++
        (c.order.filter (fun r => r.readsLoc x)).flatMap (fun r =>
          if revisitOKBF c O.prefB r e then
            ((writesOf (c.order.filter (fun d => decide (d ∈ keepCF c r e))) x).filter
              (fun wp => consXF P O (revisitCF c r e wp))).map (revisitCF c r e)
          else [])
    | .cons _ =>
      ([true, false].filter (fun b => consXF P O (c.addLoc e (some b)))).map
        (fun b => c.addLoc e (some b))
    | _ => if consXF P O (c.addLoc e none) then [c.addLoc e none] else []

theorem succsAtF_eq (P : XProgram) (O : Oracle τ) (c : Config) :
    succsAtF P O c = succsAt P O c := by
  unfold succsAtF succsAt
  have h1 : ∀ r e wp, revisitCF c r e wp = c.revisitC r e wp := fun r e wp => by
    rw [revisitCF_eq]
  simp only [consXF_eq, revisitOKBF_eq, keepCF_eq, revisitCF_eq, h1]
  rfl

def exploreCfgFromF (P : XProgram) (O : Oracle τ) : ℕ → Config → List Config
  | 0, _ => []
  | f + 1, c =>
    if consXF P O c then
      if P.nextC c = none then [c] else (succsAtF P O c).flatMap (exploreCfgFromF P O f)
    else []

theorem exploreCfgFromF_eq (P : XProgram) (O : Oracle τ) (f : ℕ) (c : Config) :
    exploreCfgFromF P O f c = exploreCfgFrom P O f c := by
  induction f generalizing c with
  | zero => rfl
  | succ f ih =>
    unfold exploreCfgFromF exploreCfgFrom
    rw [consXF_eq, succsAtF_eq, funext ih]

/-- The fast explorer on configurations. -/
def exploreCfgAtF (P : XProgram) (n : ℕ) : List Config :=
  exploreCfgFromF P oracleC (P.toProgram.bound n + 1) (Config.init P.mem)

theorem exploreCfgAtF_eq (P : XProgram) (n : ℕ) :
    exploreCfgAtF P n = exploreCfgAt P oracleC n :=
  exploreCfgFromF_eq P oracleC _ _

/-- The graphs of the fast explorer are the list of the proved explorer. -/
theorem exploreCfgAtF_abs (P : XProgram) (n : ℕ) :
    (exploreCfgAtF P n).map Config.abs = exploreAt P eqOracleSe n := by
  rw [exploreCfgAtF_eq]
  exact exploreCfgAt_abs P n

theorem mem_exploreCfgAtF (P : XProgram) (n : ℕ) {d : Config} (h : d ∈ exploreCfgAtF P n) :
    Reach P.toProgram ((Model.atomic P SC).sym EqSem.solver) (TieBreak.se EqSem.solver) d ∧
      P.toProgram.Full d.abs := by
  rw [exploreCfgAtF_eq] at h
  exact mem_exploreCfgAt P n h

def visitFromF (P : XProgram) (O : Oracle τ) : ℕ → Config → List Config
  | 0, _ => []
  | f + 1, c =>
    if consXF P O c then
      if P.nextC c = none then [c] else c :: (succsAtF P O c).flatMap (visitFromF P O f)
    else []

theorem visitFromF_eq (P : XProgram) (O : Oracle τ) (f : ℕ) (c : Config) :
    visitFromF P O f c = visitFrom P O f c := by
  induction f generalizing c with
  | zero => rfl
  | succ f ih =>
    unfold visitFromF visitFrom
    rw [consXF_eq, succsAtF_eq, funext ih]

def visitAtF (P : XProgram) (n : ℕ) : List Config :=
  visitFromF P oracleC (P.toProgram.bound n + 1) (Config.init P.mem)

theorem mem_visitAtF (P : XProgram) (n : ℕ) {d : Config} (h : d ∈ visitAtF P n) :
    Reach P.toProgram ((Model.atomic P SC).sym EqSem.solver) (TieBreak.se EqSem.solver) d := by
  unfold visitAtF at h
  rw [visitFromF_eq] at h
  exact mem_visitAt P n h

def deadFromAtF (P : XProgram) (O : Oracle τ) : ℕ → Config → List Config
  | 0, _ => []
  | f + 1, c =>
    if consXF P O c then
      if P.nextC c = none then []
      else if (succsAtF P O c).isEmpty then [c]
      else (succsAtF P O c).flatMap (deadFromAtF P O f)
    else []

theorem deadFromAtF_eq (P : XProgram) (O : Oracle τ) (f : ℕ) (c : Config) :
    deadFromAtF P O f c = deadFromAt P O f c := by
  induction f generalizing c with
  | zero => rfl
  | succ f ih =>
    unfold deadFromAtF deadFromAt
    rw [consXF_eq, succsAtF_eq, funext ih]

/-- `deadAt` (configurations without a step that are not full), fast. -/
def deadAtF (P : XProgram) (n : ℕ) : List Config :=
  deadFromAtF P oracleC (P.toProgram.bound n + 1) (Config.init P.mem)

theorem deadAtF_eq (P : XProgram) (n : ℕ) : deadAtF P n = deadAt P eqOracleSe n := by
  unfold deadAtF
  rw [deadFromAtF_eq, ← deadAt_oracleC]
  rfl

/-! ### Diagnostics of revisit candidates, with the faster tests -/

def condAF (c : Config) (d w : TEv) : Bool :=
  !(c.order.any (fun q => previousBF c d w (.th q) && decide (c.rf q = some (.th d))))

theorem condAF_eq (c : Config) (d w : TEv) : condAF c d w = condA c d w := by
  unfold condAF condA
  simp only [previousBF_eq]

def condBF (c : Config) (d w : TEv) : Bool :=
  match d.act with
  | .read _ =>
    (match c.rf d with
      | none => false
      | some e' =>
        previousBF c d w e' &&
          !((c.abs.co d.loc).any (fun w'' =>
            previousBF c d w (.th w'') && decide (c.abs.coRelAt d.loc e' (.th w'')))))
  | .write _ _ =>
    previousBF c d w (.th d) &&
      !((c.abs.co d.loc).any (fun w'' =>
        previousBF c d w (.th w'') && decide (c.abs.coRelAt d.loc (.th d) (.th w''))))
  | _ => true

theorem condBF_eq (c : Config) (d w : TEv) : condBF c d w = condB c d w := by
  unfold condBF condB
  simp only [previousBF_eq]
  rfl

def condCF (pb : Finset Lit → SExpr → Bool) (c : Config) (d w : TEv) : Bool :=
  match d.act with
  | .cons φ => decide (c.pol d = some (pb (prevFCF c d w) φ))
  | _ => true

theorem condCF_eq (pb : Finset Lit → SExpr → Bool) (c : Config) (d w : TEv) :
    condCF pb c d w = condC pb c d w := by
  unfold condCF condC
  simp only [prevFCF_eq]
  rfl

def testedEventsF (c : Config) (r w : TEv) : List TEv :=
  c.order.reverse.filter (fun d => deletedBF c r w d || decide (d = r))

theorem testedEventsF_eq (c : Config) (r w : TEv) : testedEventsF c r w = testedEvents c r w := by
  unfold testedEventsF testedEvents
  simp only [deletedBF_eq]

def revDiagF (O : Oracle τ) (c : Config) (r w : TEv) : List Rej :=
  (if plusPorfBF c w (.th r) (.th w) then [Rej.porf] else []) ++
    (testedEventsF c r w).flatMap (fun d =>
      (if condAF c d w then [] else [Rej.maxA d]) ++
      (if condBF c d w then [] else [Rej.maxB d]) ++
      (if condCF (O.prefB (ctxCF c r w)) c d w then [] else [Rej.maxC d]))

theorem revDiagF_eq (O : Oracle τ) (c : Config) (r w : TEv) :
    revDiagF O c r w = revDiag O c r w := by
  unfold revDiagF revDiag
  simp only [plusPorfBF_eq, testedEventsF_eq, condAF_eq, condBF_eq, condCF_eq, ctxCF_eq]

end Targets

end Condpor
