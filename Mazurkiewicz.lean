import Mazurkiewicz.Lib.Rel
import Mazurkiewicz.Lib.ListOrder
import Mazurkiewicz.Lib.Path
import Mazurkiewicz.Lib.Finset
import Mazurkiewicz.Trust.Event
import Mazurkiewicz.Trust.Graph
import Mazurkiewicz.Trust.Ops
import Mazurkiewicz.Trust.Examples
import Mazurkiewicz.Trust.Program
import Mazurkiewicz.Models.Model
import Mazurkiewicz.Trust.Alg
import Mazurkiewicz.Trust.AlgExamples
import Mazurkiewicz.Trust.Invariants
import Mazurkiewicz.Trust.A22
import Mazurkiewicz.Trust.Terminate
import Mazurkiewicz.Trust.Prev
import Mazurkiewicz.Trust.PrevTerm
import Mazurkiewicz.Trust.Complete
import Mazurkiewicz.Trust.Optimal
import Mazurkiewicz.Trust.Explore
import Mazurkiewicz.Lib.ReachB
import Mazurkiewicz.Trust.Compute
import Mazurkiewicz.Trust.ExploreC
import Mazurkiewicz.Trust.Budget
import Mazurkiewicz.Trust.Oracle
import Mazurkiewicz.Induction.Reach
import Mazurkiewicz.Induction.MaxStep
import Mazurkiewicz.Induction.States
import Mazurkiewicz.Induction.Interleave
import Mazurkiewicz.Induction.Residual
import Mazurkiewicz.Induction.Compose
import Mazurkiewicz.Induction.Certificate
import Mazurkiewicz.Induction.KInductive
import Mazurkiewicz.Induction.Budgets
import Mazurkiewicz.Induction.FullObl
import Mazurkiewicz.Induction.Check
import Mazurkiewicz.Induction.MonoExample
import Mazurkiewicz.Induction.ErrGraph
import Mazurkiewicz.Induction.ErrEnc
import Mazurkiewicz.Induction.AssertExample
import Mazurkiewicz.Induction.Bars
import Mazurkiewicz.Induction.CutBar
import Mazurkiewicz.Induction.BarCheck
import Mazurkiewicz.Induction.ToggleExample
import Mazurkiewicz.Audit
import Mazurkiewicz.Condpor.Chain
import Mazurkiewicz.Condpor.GetNextEx
import Mazurkiewicz.Condpor.StackEx
import Mazurkiewicz.Condpor.Rf.Variant
import Mazurkiewicz.Condpor.Rmw.Sym
import Mazurkiewicz.Condpor.Rmw.Inv
import Mazurkiewicz.Condpor.Rmw.PrevTerm
import Mazurkiewicz.Condpor.Rmw.Complete
import Mazurkiewicz.Condpor.Rmw.Exit
import Mazurkiewicz.Condpor.Rmw.Instances
import Mazurkiewicz.Condpor.Rmw.LocksEx
import Mazurkiewicz.Condpor.Rmw.LocksEx3
import Mazurkiewicz.Condpor.Rmw.LockMutex
import Mazurkiewicz.Pct.Coverage
import Mazurkiewicz.Pct.Count
import Mazurkiewicz.Pct.Hitting
import Mazurkiewicz.Jmt.Stage
import Mazurkiewicz.Jmt.NoSo
import Mazurkiewicz.Jmt.Structure

/-!
# Mazurkiewicz

A Lean 4 formalization of TruSt: "Truly Stateless, Optimal Dynamic Partial Order
Reduction" (Kokologiannakis, Marmanis, Gladstein, Vafeiadis, POPL 2022).

Work in progress.
-/
