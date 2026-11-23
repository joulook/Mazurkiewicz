import Mazurkiewicz.Condpor.Rmw.TargetsEx

/-!
# Generation of the JMC reference data (no effect at build time)

Run from the root of the Lean project, one command per group:

    lake env lean --run Mazurkiewicz/Condpor/Rmw/TargetsGen.lean <group> <dataDir> <fragDir>

Groups: `a` (L1 L2 L3 L7 L4 T7 L9 L9b L10 and the witnesses), `b` (L5 L8 T8 T9 T10 T12
T13), `c1` (T11), `c2` (T14), `c3` (T15), and `merge` (writes `O1-counts.json` from
the fragments in `fragDir`; run it last).
-/

open Condpor Targets

def groups : List (String × List String × Bool) :=
  [("a", ["L1", "L2", "L3", "L7", "L4", "T7", "L9", "L9b", "L10"], true),
   ("b", ["L5", "L8", "T8", "T9", "T10", "T12", "T13"], false),
   ("c1", ["T11"], false), ("c2", ["T14"], false), ("c3", ["T15"], false)]

def main (args : List String) : IO UInt32 := do
  match args with
  | ["merge", dir, frag] => mergeO1 dir frag; return 0
  | [g, dir, frag] =>
    match groups.find? (·.1 == g) with
    | some (_, names, wits) => writeAll dir frag names wits; return 0
    | none => IO.eprintln s!"unknown group {g}"; return 1
  | _ => IO.eprintln "usage: <group|merge> <dataDir> <fragDir>"; return 1
