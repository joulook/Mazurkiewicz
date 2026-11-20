import Mazurkiewicz.Trust.Ops

/-!
# Checked examples for graphs and their operations

The tests of the plan (Section 7) for the points where the representation
differs from the Coq development: a trace of writes only, and a revisit that
deletes an event that depends on the revisited read; and the four graphs of
the paper's Fig. 4 (exit criterion of milestone M2). (Two locations with
different initial values, and a read from `init` while another location has a
write, are at the end of `Ops.lean`.)
-/

namespace Trust

namespace Examples

open Graph

/-- The memory that holds `0` everywhere. -/
def μ : Loc → Val := fun _ => 0

/-! ### A trace of writes only -/

/-- `W(x,1)` and `W(x,2)` by thread `0`. -/
def a : TEv := ⟨0, 0, .write 0 1⟩
/-- The second write of thread `0`. -/
def b : TEv := ⟨0, 1, .write 0 2⟩

/-- Thread `0` writes `1` and then `2` to location `0`. -/
def Gww : Graph := ((Graph.init μ).addWrite a .init).addWrite b (.th a)

theorem Gww_wf : Gww.Wf :=
  ((Graph.init_wf μ).addWrite (e := a) (wp := .init) (by decide) (by decide) trivial).addWrite
    (e := b) (wp := .th a) (by decide) (by decide) ⟨by decide, 1, rfl⟩

example : Gww.co 0 = [a, b] := by decide
example : Gww.maxWrite 0 = .th b := by decide

/-- Both events return no value. -/
example : Gww.trace 0 = [none, none] := by
  have h0 : (Graph.init μ).trace 0 = [] := by
    simp [trace, traceBefore, cnt, Graph.init]
  have h1 := trace_addWrite (Graph.init_wf μ) (e := a) (wp := .init) (by decide) (by decide)
    trivial 0
  have hG1 := (Graph.init_wf μ).addWrite (e := a) (wp := .init) (by decide) (by decide) trivial
  have h2 := trace_addWrite hG1 (e := b) (wp := .th a) (by decide) (by decide)
    ⟨by decide, 1, rfl⟩ 0
  rw [show Gww = ((Graph.init μ).addWrite a .init).addWrite b (.th a) from rfl, h2, h1, h0]
  rfl

/-! ### A revisit that deletes a dependent event

Thread `0` reads `x` (from `init`) and then writes `y`; thread `1` writes `2`
to `x`. With the order `<next` of the plan (thread, then index), Algorithm 1
adds `r`, then `d`, then `w`. The write `w` revisits `r`: the write `d` to `y`
was added after `r` and is not causally before `w`, so it is deleted
(Def. A.6); the read now reads `2`.

The step itself (the deleted set, `IsMaximallyAdded`, the rule) is defined with
the algorithm. Here we check the graph operations that the step uses, and the
two causality facts that make `d` deleted and `r` revisitable. -/

/-- The read of `x` by thread `0`. -/
def r : TEv := ⟨0, 0, .read 0⟩
/-- The write to `y` by thread `0`, after its read. -/
def d : TEv := ⟨0, 1, .write 1 1⟩
/-- The write of `2` to `x` by thread `1`. -/
def w : TEv := ⟨1, 0, .write 0 2⟩

/-- Before the revisit: `r` and `d` have been added, in this order. -/
def G1 : Graph := ((Graph.init μ).addRead r .init).addWrite d .init

/-- The configuration before the revisit; the order list is newest first. -/
def C1 : Config := ⟨G1.mem, [d, r], G1.rf, G1.co⟩

example : C1.abs.events = G1.events := by decide
-- `r` was added before `d`
example : C1.order.Before d r := by decide

theorem G1_wf : G1.Wf :=
  ((Graph.init_wf μ).addRead (e := r) (x := 0) (w := .init) (by decide) rfl trivial).addWrite
    (e := d) (wp := .init) (by decide) (by decide) trivial

/-- The paper's `G + w`: the graph with the new write, at any coherence place. -/
def G1w : Graph := G1.addWrite w .init

/-- Only `init` is causally before the new write. -/
theorem porf_w {a : Ev} (h : G1w.porf a (.th w)) : a = .init := by
  refine G1w.eq_init_of_porf ?_ h
  rintro c (hc | ⟨e, he, -, hrf⟩)
  · cases c with
    | init => rfl
    | th q =>
      have h3 : q.idx < w.idx := hc.2.2.2
      simp [w] at h3
  · cases he
    have h0 : G1w.rf w = none := by decide
    rw [h0] at hrf
    cases hrf

-- `r` is not causally before `w`, so it may be revisited (Algorithm 1, line 15)
example : ¬ G1w.porf (.th r) (.th w) := fun h => by cases porf_w h
-- `d` was added after `r` and is not causally before `w`: it is deleted (Def. A.6)
example : ¬ G1w.porf (.th d) (.th w) := fun h => by cases porf_w h

/-- After the revisit: restrict to the events that are not deleted, add the
write, give the read its new source. -/
def G2 : Graph := ((G1.restrict {r}).addWrite w .init).setRF r (.th w)

theorem G2_wf : G2.Wf := by
  have hE : (G1.restrict {r}).WfExcept r := by
    refine G1_wf.restrict_except ?_ ?_
    · intro x y h hy
      cases x with
      | init => trivial
      | th q =>
        cases y with
        | init => exact absurd h (by simp [po])
        | th q' =>
          have hy' : q' ∈ G1.events ∩ {r} := hy
          have hq' : q' = r := by
            have := (Finset.mem_inter.mp hy').2
            simpa using this
          subst hq'
          have := h.2.2.2
          simp [r] at this
    · intro q hq hne
      have := (Finset.mem_inter.mp hq).2
      exact absurd (by simpa using this) hne
  have hA := hE.addWrite (e := w) (wp := .init) (by decide) (by decide) trivial
  exact hA.setRF (x := 0) (by decide) rfl ⟨by decide, 2, rfl⟩

-- the dependent write is gone, and the read returns the new value
example : G2.events = {w, r} := by decide
example : d ∉ G2.events := by decide
example : G1.ret r = some 0 := by decide
example : G2.ret r = some 2 := by decide
example : G2.co 0 = [w] ∧ G2.co 1 = [] := by decide

/-! ### The four graphs of Fig. 4

The program `w+w+rr`: thread `0` writes `1` to `x`, thread `1` writes `1` to
`y`, thread `2` reads `x` and then `y`. Its four consistent graphs under SC
(paper, Fig. 4) differ in the sources of the two reads. Here they are built as
values and checked to be well-formed; consistency and the program come with
later milestones. Locations: `x = 0`, `y = 1`. -/

/-- `W(x,1)` by thread `0`. -/
def wx : TEv := ⟨0, 0, .write 0 1⟩
/-- `W(y,1)` by thread `1`. -/
def wy : TEv := ⟨1, 0, .write 1 1⟩
/-- `R(x)` by thread `2`. -/
def rx : TEv := ⟨2, 0, .read 0⟩
/-- `R(y)` by thread `2`. -/
def ry : TEv := ⟨2, 1, .read 1⟩

/-- The graph with the two writes and the two reads, with the given sources. -/
def fig4 (sx sy : Ev) : Graph :=
  ((((Graph.init μ).addWrite wx .init).addWrite wy .init).addRead rx sx).addRead ry sy

theorem fig4_writes_wf : (((Graph.init μ).addWrite wx .init).addWrite wy .init).Wf :=
  ((Graph.init_wf μ).addWrite (e := wx) (wp := .init) (by decide) (by decide) trivial).addWrite
    (e := wy) (wp := .init) (by decide) (by decide) trivial

/-- Graph 1 of Fig. 4: both reads read from `init`. -/
theorem fig4_1_wf : (fig4 .init .init).Wf :=
  (fig4_writes_wf.addRead (e := rx) (x := 0) (w := .init) (by decide) rfl trivial).addRead
    (e := ry) (x := 1) (w := .init) (by decide) rfl trivial

/-- Graph 2: `R(x)` reads from `init`, `R(y)` from `W(y,1)`. -/
theorem fig4_2_wf : (fig4 .init (.th wy)).Wf :=
  (fig4_writes_wf.addRead (e := rx) (x := 0) (w := .init) (by decide) rfl trivial).addRead
    (e := ry) (x := 1) (w := .th wy) (by decide) rfl ⟨by decide, 1, rfl⟩

/-- Graph 3: `R(x)` reads from `W(x,1)`, `R(y)` from `init`. -/
theorem fig4_3_wf : (fig4 (.th wx) .init).Wf :=
  (fig4_writes_wf.addRead (e := rx) (x := 0) (w := .th wx) (by decide) rfl
    ⟨by decide, 1, rfl⟩).addRead (e := ry) (x := 1) (w := .init) (by decide) rfl trivial

/-- Graph 4: both reads read from the writes. -/
theorem fig4_4_wf : (fig4 (.th wx) (.th wy)).Wf :=
  (fig4_writes_wf.addRead (e := rx) (x := 0) (w := .th wx) (by decide) rfl
    ⟨by decide, 1, rfl⟩).addRead (e := ry) (x := 1) (w := .th wy) (by decide) rfl
    ⟨by decide, 1, rfl⟩

-- the four graphs have the same events and coherence lists
example : (fig4 .init .init).events = {wx, wy, rx, ry} := by decide
example : (fig4 (.th wx) (.th wy)).events = {wx, wy, rx, ry} := by decide
example : (fig4 .init .init).co 0 = [wx] ∧ (fig4 .init .init).co 1 = [wy] := by decide
-- and differ in the values read: (0,0), (0,1), (1,0), (1,1)
example : (fig4 .init .init).ret rx = some 0 ∧ (fig4 .init .init).ret ry = some 0 := by decide
example : (fig4 .init (.th wy)).ret rx = some 0 ∧ (fig4 .init (.th wy)).ret ry = some 1 := by
  decide
example : (fig4 (.th wx) .init).ret rx = some 1 ∧ (fig4 (.th wx) .init).ret ry = some 0 := by
  decide
example : (fig4 (.th wx) (.th wy)).ret rx = some 1 ∧ (fig4 (.th wx) (.th wy)).ret ry = some 1 := by
  decide

end Examples

end Trust
