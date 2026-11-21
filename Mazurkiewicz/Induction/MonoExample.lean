import Mazurkiewicz.Induction.Check

/-!
# The worked example: monotone reads of the reader/writer program

`induction-popl`, ex:rw-fix, ex:mono (`bridge.tex`) and ex:mono-enum
(`dpor.tex`).

The program `P^rw`: one thread writes `1` to a location forever, one thread
reads it forever. It is unbounded, and it has infinitely many reachable
graphs. The property `Bad^mono`: a read that returns `1` is followed by a read
that returns `0`.

`mono_safe`: `P^rw` is safe for `Bad^mono` under SC, for executions of every
length. The proof is `check_sound` applied to the result of running `Check`
with the verified explorer of TruSt (`mono_check`: the verdict is `true`
after 12 evaluations of `f`, as in ex:mono-enum). `mono_check` is proved by
evaluation in the kernel (`decide +kernel`), not by `native_decide`.

How the text is read here.

* Threads `1`, `2` of the paper are `0`, `1`; the location `x` is `0`.
* `Bad^mono` and the abstraction are defined on the trace of the reader (the
  list of the values returned by its reads, def:trace) instead of on pairs
  of read events.
* `α(G) = (mem_G(x), seen(G), bad(G))` with values in `Val × Bool × Bool`.
* `f` is the formula of ex:mono for `b ⊙ H`, computed from the graph `H`
  (`fM`, with the computable `traceC`).
* The two negative examples of ex:mono are checked too: the set without
  `(1,1,0)` and the set with the unrealised `(0,1,0)` are rejected.
-/

namespace Trust

namespace Mono

/-- The reader/writer program `P^rw` (ex:rw-fix): thread `0` writes `1` to the
location `0` forever, thread `1` reads the location `0` forever. -/
def rw : Program where
  threads := [0, 1]
  threads_nodup := by decide
  step := fun t _ =>
    match t with
    | 0 => some (.write 0 1)
    | 1 => some (.read 0)
    | _ => none
  mem := fun _ => 0
  step_none := by
    intro t ht
    match t with
    | 0 | 1 => simp at ht
    | _ + 2 => rfl

/-- Some read returned `1`. -/
def seenL (l : List (Option Val)) : Bool := l.any (fun v => v == some 1)

/-- Some read returned `0`. -/
def zeroL (l : List (Option Val)) : Bool := l.any (fun v => v == some 0)

/-- A read that returned `1` is followed by a read that returned `0`. -/
def badL : List (Option Val) → Bool
  | [] => false
  | v :: l => (v == some 1 && zeroL l) || badL l

/-- The values returned by the reads of thread `1`, computed. -/
def traceC (H : Graph) : List (Option Val) :=
  (List.range (H.cnt 1)).map (fun i => H.ret ⟨1, i, .read 0⟩)

abbrev A := Val × Bool × Bool

def uM (_ : A) (_ : Tid) : List (Option Val) := []

def μM (b : A) : Loc → Val := fun x => if x = 0 then b.1 else 0

def fM (b : A) (H : Graph) : A :=
  (H.memOf 0, b.2.1 || seenL (traceC H),
    b.2.2 || badL (traceC H) || (b.2.1 && zeroL (traceC H)))

def abadM (b : A) : Bool := b.2.2

def BM : List A := [(0, false, false), (1, false, false), (1, true, false)]

/-! ### Lists of returned values -/

theorem seenL_append (l₁ l₂ : List (Option Val)) :
    seenL (l₁ ++ l₂) = (seenL l₁ || seenL l₂) := List.any_append

theorem zeroL_append (l₁ l₂ : List (Option Val)) :
    zeroL (l₁ ++ l₂) = (zeroL l₁ || zeroL l₂) := List.any_append

theorem badL_append (l₁ l₂ : List (Option Val)) :
    badL (l₁ ++ l₂) = (badL l₁ || badL l₂ || (seenL l₁ && zeroL l₂)) := by
  induction l₁ with
  | nil => simp [badL, seenL]
  | cons v l ih =>
    have h1 : seenL (v :: l) = ((v == some 1) || seenL l) := List.any_cons
    rw [List.cons_append, badL, badL, ih, zeroL_append, h1]
    generalize (v == some 1) = a
    generalize zeroL l = b
    generalize zeroL l₂ = c
    generalize badL l = d
    generalize badL l₂ = e
    generalize seenL l = s
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases s <;> rfl

/-! ### Executions of programs that step like `P^rw` -/

theorem rw_step_ge (t : Tid) (u : List (Option Val)) (ht : t ∉ rw.threads) :
    rw.step t u = none := by
  match t with
  | 0 | 1 => simp [rw] at ht
  | _ + 2 => rfl

/-- A residual program of `P^rw` steps like `P^rw`. -/
theorem residual_step (u : Tid → List (Option Val)) (μ : Loc → Val) (t : Tid)
    (x : List (Option Val)) : (rw.residual u μ).step t x = rw.step t x := by
  change (if t ∈ rw.threads then rw.step t (u t ++ x) else none) = rw.step t x
  by_cases ht : t ∈ rw.threads
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ht)]
    rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false ht), rw_step_ge t x ht]

/-- The events of an execution: writes of `1` to `0` by thread `0`, reads of
`0` by thread `1`. -/
theorem act_of_exec {Q : Program} (hQ : ∀ t u, Q.step t u = rw.step t u) {G : Graph}
    (hE : Q.Exec G) {e : TEv} (he : e ∈ G.events) :
    (e.tid = 0 ∧ e.act = .write 0 1) ∨ (e.tid = 1 ∧ e.act = .read 0) := by
  have h := hE.2 e he
  rw [hQ] at h
  obtain ⟨t, i, a⟩ := e
  match t with
  | 0 => exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
  | 1 => exact Or.inr ⟨rfl, (Option.some.inj h).symm⟩
  | _ + 2 => cases h

/-- Only the location `0` is written. -/
theorem memOf_of_ne {Q : Program} (hQ : ∀ t u, Q.step t u = rw.step t u) {G : Graph}
    (hG : G.Wf) (hE : Q.Exec G) {x : Loc} (hx : x ≠ 0) : G.memOf x = G.mem x := by
  have hco : G.co x = [] := by
    refine List.eq_nil_iff_forall_not_mem.mpr (fun e he => ?_)
    obtain ⟨hev, v, hv⟩ := (hG.co_mem x e).mp he
    rcases act_of_exec hQ hE hev with ⟨-, h⟩ | ⟨-, h⟩
    · rw [h] at hv
      exact hx (Act.write.inj hv).1.symm
    · rw [h] at hv
      cases hv
  unfold Graph.memOf Graph.maxWrite
  rw [hco]
  rfl

/-- The computed list of returned values is the trace of the reader. -/
theorem traceC_eq {Q : Program} (hQ : ∀ t u, Q.step t u = rw.step t u) {G : Graph}
    (hG : G.Wf) (hE : Q.Exec G) : traceC G = G.trace 1 := by
  unfold traceC Graph.trace Graph.traceBefore
  refine List.map_congr_left (fun i hi => ?_)
  obtain ⟨q, hq, ht, hidx⟩ := (hG.exists_idx_iff 1 i).mpr (List.mem_range.mp hi)
  have hev := hG.evAt_eq_some hq
  rw [ht, hidx] at hev
  rw [hev]
  rcases act_of_exec hQ hE hq with ⟨h, -⟩ | ⟨-, h⟩
  · rw [ht] at h
    cases h
  · obtain ⟨t, j, a⟩ := q
    simp only at ht hidx h
    subst ht hidx h
    rfl

/-- The trace of a thread in a prefix is an initial segment of its trace. -/
theorem trace_of_isPrefixOf {G G' : Graph} (hG' : G'.Wf) (hp : G.IsPrefixOf G') (t : Tid) :
    ∃ l, G'.trace t = G.trace t ++ l := by
  have hG := hG'.of_isPrefixOf hp
  obtain ⟨s, hcl, rfl⟩ := hp
  have hi : (G'.restrict s).cnt t ≤ G'.cnt t :=
    Finset.card_le_card (Finset.filter_subset_filter _ Finset.inter_subset_left)
  have hkeep : ∀ q ∈ G'.events, q.tid = t → q.idx < (G'.restrict s).cnt t →
      q ∈ G'.events ∩ s := by
    intro q hq ht hlt
    obtain ⟨q₀, hq₀, ht₀, hi₀⟩ := (hG.exists_idx_iff t q.idx).mpr hlt
    have hq₀' : q₀ ∈ G'.events ∩ s := hq₀
    have := hG'.idx_inj q₀ (Finset.mem_inter.mp hq₀').1 q hq (ht₀.trans ht.symm) hi₀
    exact this ▸ hq₀'
  have htr : (G'.restrict s).trace t = G'.traceBefore t ((G'.restrict s).cnt t) :=
    Graph.traceBefore_restrict_of_keep hG' hi
      (fun q hq ht hlt => (Finset.mem_inter.mp (hkeep q hq ht hlt)).2)
      (fun q hq ht hlt w hw => Graph.evSet_mono Finset.inter_subset_right
        (hcl (Or.inr ⟨q, rfl, hq, hw⟩) (hkeep q hq ht hlt)))
  rw [htr, Graph.traceBefore_eq_take G' t hi]
  exact ⟨(G'.trace t).drop ((G'.restrict s).cnt t), (List.take_append_drop _ _).symm⟩

/-! ### The property, the abstraction, the hypotheses of `check_sound` -/

/-- `Bad^mono` (ex:mono). -/
def BadMono : Set Graph := {G | badL (G.trace 1) = true}

/-- The abstraction `α(G) = (mem_G(x), seen(G), bad(G))` of ex:mono. -/
noncomputable def absM : Abstraction rw A where
  α := fun G => (G.memOf 0, seenL (G.trace 1), badL (G.trace 1))
  u := uM
  μ := μM
  hconf := by
    intro G hG
    refine ⟨fun t _ x => rfl, ?_⟩
    funext x
    by_cases hx : x = 0
    · subst hx
      rfl
    · rw [memOf_of_ne (fun _ _ => rfl) hG.1 hG.2.1 hx, hG.2.1.1]
      simp [μM, hx, rw]

/-- `Bad^mono` is `α`-determined by `Abad = {(m, σ, 1)}`. -/
theorem absM_determines : absM.Determines BadMono {a | abadM a = true} :=
  fun _ _ => Iff.rfl

/-- `Bad^mono` is extension-closed. -/
theorem badMono_extClosed : ExtClosed rw BadMono := by
  intro G G' _ hG' hbad hp
  obtain ⟨l, hl⟩ := trace_of_isPrefixOf hG'.1 hp 1
  change badL (G'.trace 1) = true
  have hb : badL (G.trace 1) = true := hbad
  rw [hl, badL_append, hb]
  rfl

/-- The formula of ex:mono for `b ⊙ H`. -/
theorem fM_eq {G H : Graph} (hG : ExecSC rw G)
    (hH : GReach (rw.residual G.trace G.memOf) SC H) :
    fM (absM.α G) H = absM.α (G.comp H) := by
  have hHE := greach_iff.mp hH
  obtain ⟨-, -, -, htr, -, hmem⟩ := Graph.comp_facts hG.1 hHE.1 hHE.2.2 hHE.2.1.1
  have htc := traceC_eq (residual_step G.trace G.memOf) hHE.1 hHE.2.1
  change (H.memOf 0, seenL (G.trace 1) || seenL (traceC H),
    badL (G.trace 1) || badL (traceC H) || (seenL (G.trace 1) && zeroL (traceC H))) =
    ((G.comp H).memOf 0, seenL ((G.comp H).trace 1), badL ((G.comp H).trace 1))
  rw [htc, htr, hmem, seenL_append, badL_append]

/-- The abstraction is compositional (ex:mono). -/
theorem absM_compositional : absM.Compositional := by
  intro G₁ G₂ hG₁ hG₂ h H hH
  have hres : rw.residual G₁.trace G₁.memOf = rw.residual G₂.trace G₂.memOf := by
    rw [← absM.res_eq hG₁, ← absM.res_eq hG₂, h]
  rw [← fM_eq hG₁ hH, ← fM_eq hG₂ (hres ▸ hH), h]

/-! ### Running `Check` -/

/-- `Check` with the explorer accepts `B` for `K = 2`, after 12 evaluations of
`f` (ex:mono-enum). Proved by evaluation in the kernel. -/
theorem mono_check : Check exploreC rw BM abadM uM μM fM 2 = (true, 12) := by
  decide +kernel

/-- `P^rw` is safe for `Bad^mono` under SC: no execution, of any length, has a
read that returns `1` followed by a read that returns `0`. -/
theorem mono_safe : Safe rw SC BadMono := by
  refine check_sound absM absM_determines badMono_extClosed (B := BM) (K := 2) ?_
    (by decide) (by decide) fM (fun G hG _ H hH _ => fM_eq hG hH) ?_
  · change (((Graph.init rw.mem).memOf 0, seenL ((Graph.init rw.mem).trace 1),
      badL ((Graph.init rw.mem).trace 1)) : A) ∈ BM
    rw [Graph.trace_init]
    decide
  · change (Check exploreC rw BM abadM uM μM fM 2).1 = true
    rw [mono_check]

/-- The same through the form with the paper's hypotheses. -/
theorem mono_safe_paper : Safe rw SC BadMono := by
  refine check_sound_paper absM absM_compositional absM_determines badMono_extClosed
    (B := BM) (K := 2) ?_ (by decide) (by decide) fM (fun G hG _ H hH _ => fM_eq hG hH) ?_
  · change (((Graph.init rw.mem).memOf 0, seenL ((Graph.init rw.mem).trace 1),
      badL ((Graph.init rw.mem).trace 1)) : A) ∈ BM
    rw [Graph.trace_init]
    decide
  · change (Check exploreC rw BM abadM uM μM fM 2).1 = true
    rw [mono_check]

/-- "A wrong set is rejected" (ex:mono): without `(1,1,0)` the check fails.
(That this set is not 2-inductive is the paper's remark; only the rejection
is proved here.) -/
theorem mono_reject_wrong :
    (Check exploreC rw [(0, false, false), (1, false, false)] abadM uM μM fM 2).1 = false := by
  decide +kernel

/-- "A spurious failure at an unrealised value" (ex:mono): with `(0,1,0)`
added, the check fails. (The paper notes that this set is 2-inductive; that
is not proved here.) -/
theorem mono_reject_unrealised :
    (Check exploreC rw ((0, true, false) :: BM) abadM uM μM fM 2).1 = false := by
  decide +kernel

/-- Both threads of `P^rw` have one local state; so it has finitely many
reachable configurations (cor:op (3), rem:forgets), although it has
infinitely many reachable graphs. -/
theorem rw_opReach_finite : {c | OpReach rw c}.Finite := by
  refine opReach_finite rw (fun t _ => ?_)
  have : Subsingleton (St (rw.step t)) := by
    refine ⟨fun s s' => ?_⟩
    refine Quotient.inductionOn₂ s s' (fun u u' => ?_)
    exact St.mk_eq_mk.mpr (fun _ => rfl)
  exact Finite.of_subsingleton

set_option linter.hashCommand false

-- the compiler agrees with the kernel
#guard Check exploreC rw BM abadM uM μM fM 2 == (true, 12)

end Mono

end Trust
