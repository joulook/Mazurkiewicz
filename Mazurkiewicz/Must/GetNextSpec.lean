import Mazurkiewicz.Must.GetNext

/-!
# The domain of `GetNext`, its specification, and the loop invariants of A.16 (milestone M7)

Paper: Lemma A.16 (pp. 31–33): the specification ⟨1⟩1 (P1–P3) and the loop invariants LI1–LI4
of ⟨3⟩2. Plan: Section 2b (`GetNext`), fate rows "Algorithm 2" and A.16, the addendum after the
M6 review (P1 strengthened, `next_P(G_s) ∈ G′.E`; the upper bound of the loop is the current
`MaxCompletion(G_p, A)`, not `G_t`).

* `CallDom M P c Gt e` (the strengthened domain): `c` has the configuration invariant,
  `c.G ⊑ Gt`, `e = next_P(c.G)` and `e ∈ Gt.E`. (Then `c.G ⊏ Gt`.) The printed domain
  `G_s ⊏ G_t` alone is false for the claim ⟨1⟩1 (plan fate row, `getNext_printed_domain_false`
  in `GetNextEx.lean`).
* `CallSpec M tie P c Gt e S c'`: P2 (`S` is a sequence of algorithmic steps from `c` to `c'`),
  P1 repaired (`c'.G ⊑ Gt`, `c.G ⊏ c'.G`, and `e ∈ c'.G.E`), P3 made precise (every
  configuration of `S` has `c.order ++ [e]` as a prefix of its insertion order and `c.G` as a
  causal prefix of its graph: no event of `G_s` is deleted, moved or given another source, and
  `e` is inserted first).
* `Ctx`: the situation of lines 10–14 (Case 2). `LoopInv` (LI1–LI4 repaired): with
  `X = MaxCompletion(G_p, A)`: `c.G ⊑ X` (LI1, LI2), `A` starts with `r₀`, is duplicate-free, its
  events are in `c.G` and not in `G_p`, `s₀ ∉ c.G`, the insertion order starts with
  `c₀.order ++ [r₀]` and lists the events of `A` in the order of `A`, `c₀.G` is a causal prefix
  of `c.G`.
* Loop facts: `LoopInv.thr_sub` (events of the thread of `s₀` are in `G_p`), `LoopInv.test_of`
  (the test of line 16 holds for `e ∈ G_p.E ∪ {s₀}`, so `s₀` is never deferred),
  `LoopInv.exists_next` (`next_P(G) ≠ ⊥`, LI1's first clause), `LoopInv.eq_of_brk` (at the break
  `G = MaxCompletion(G_p, A)`, A.16 ⟨3⟩3), `LoopInv.defer_facts` (A.16 ⟨7⟩1, ⟨6⟩2: a deferred
  event is not in `MaxCompletion(G_p, A)`, is available there, and the new `MaxCompletion` exists),
  `loopInv_of_call` (preservation by one iteration, LI4), `loop_exists` (the loop terminates at the
  break, by induction on the remaining capacity `N − |G.E|`).

Every result holds for every model `M`, every tie-break with `TieQ9 M tie`; `loop_exists` needs a
bounded program.
-/

namespace Must

open Graph Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q]
variable {M : Model Q} {P : Program Q} {tie : Tie Q}

/-- The strengthened domain of `GetNext(G_s, G_t)` at configuration level (plan Section 2b,
addendum after M6): `c` satisfies the configuration invariant, `c.G ⊑ Gt`, and the next event
`e = next_P(c.G)` is an event of `Gt`. -/
structure CallDom (M : Model Q) (P : Program Q) (c : Config Q) (Gt : Graph Q) (e : Ev Q) :
    Prop where
  /-- the configuration invariant -/
  inv : c.Inv M P
  /-- `G_s ⊑ G_t` -/
  pfx : Pfx M P c.G Gt
  /-- `e = next_P(G_s)` -/
  next : M.nextP P c.G = some e
  /-- `next_P(G_s) ∈ G_t.E` -/
  mem : e ∈ Gt.events

/-- The specification of `GetNext(G_s, G_t)` (Lemma A.16 ⟨1⟩1, repaired): P2, P1 with
`next_P(G_s) ∈ G'.E`, P3 as order and graph prefixes. -/
structure CallSpec (M : Model Q) (tie : Tie Q) (P : Program Q) (c : Config Q) (Gt : Graph Q)
    (e : Ev Q) (S : List (Config Q)) (c' : Config Q) : Prop where
  /-- P2: the steps of `S` lead from `c` to `c'` -/
  path : StepSeq M tie P c S c'
  /-- P1: `G' ⊑ G_t` -/
  pfx : Pfx M P c'.G Gt
  /-- P1: `G_s ⊏ G'` -/
  spfx : SPfx M P c.G c'.G
  /-- P1, strengthened: `next_P(G_s) ∈ G'.E` -/
  mem : e ∈ c'.G.events
  /-- P3: the order of `c'` starts with the order of `c` followed by `next_P(G_s)` -/
  ord : c.order ++ [e] <+: c'.order
  /-- P3: no step of `S` revisits or deletes an event of `G_s` -/
  keep : ∀ d ∈ S, c.order ++ [e] <+: d.order ∧ c.G.IsPrefixOf d.G

/-- Case 2 of `GetNext(c.G, Gt)` (lines 10–14): `r₀ = next_P(G_s)` reads `s₀ ∉ G_s` in `G_t`. -/
structure Ctx (M : Model Q) (P : Program Q) (c₀ : Config Q) (Gt : Graph Q) (r₀ s₀ : Ev Q) :
    Prop where
  /-- the domain of the call -/
  dom : CallDom M P c₀ Gt r₀
  /-- `s₀ = G_t.rf(r₀)` (repaired line 12) -/
  src : Gt.rf r₀ = some (.snd s₀)
  /-- `s₀ ∉ G_s` (the test of line 9 fails) -/
  nmem : s₀ ∉ c₀.G.events

namespace Ctx

variable {c₀ : Config Q} {Gt : Graph Q} {r₀ s₀ : Ev Q} (hx : Ctx M P c₀ Gt r₀ s₀)
include hx

theorem nextEv : P.nextEv c₀.G r₀.tid = some r₀ := nextEv_of_nextP hx.dom.next

theorem facts : s₀ ∈ Gt.events ∧ s₀.IsSend ∧ r₀.IsRecv ∧ s₀ ≠ r₀ :=
  case2_facts hx.dom.pfx hx.src

theorem smatch : s₀.Matches r₀ := hx.dom.pfx.wf'.rf_match _ _ hx.src

theorem gp_left : Pfx M P c₀.G (prefixExt c₀.G Gt s₀) := hx.dom.pfx.prefixExt_left s₀

theorem gp_right : Pfx M P (prefixExt c₀.G Gt s₀) Gt := hx.dom.pfx.prefixExt_right s₀

theorem nextEv_s₀ : P.nextEv (prefixExt c₀.G Gt s₀) s₀.tid = some s₀ :=
  case2_nextEv_s₀ hx.dom.pfx hx.src hx.nmem

theorem s₀_not_mem : s₀ ∉ (prefixExt c₀.G Gt s₀).events :=
  prefixExt_not_mem hx.dom.pfx.wf' hx.nmem

theorem r₀_not_mem_c₀ : r₀ ∉ c₀.G.events :=
  hx.dom.inv.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv hx.nextEv)

/-- `r₀ ∉ G_p`: `r₀` is not in `G_s` and not causally before its source `s₀`. -/
theorem r₀_not_mem : r₀ ∉ (prefixExt c₀.G Gt s₀).events := by
  rw [mem_prefixExt hx.dom.pfx.events_subset]
  rintro (h | ⟨-, h⟩)
  · exact hx.r₀_not_mem_c₀ h
  · exact hx.dom.pfx.wf'.porf_irrefl r₀ (TransGen.tail h (Or.inr ⟨hx.dom.mem, hx.src⟩))

/-- The test of line 9 fails. -/
theorem not_test : ¬ ∃ src out, OpAdd₀ M P c₀.G r₀ src out ∧ Pfx M P (c₀.G.add r₀ src out) Gt :=
  fun h => hx.nmem ((case1_iff hx.dom.pfx hx.nextEv hx.dom.mem).mp h s₀ hx.src)

end Ctx

/-- The loop invariant of A.16 ⟨3⟩2 (LI1–LI4, repaired), at the configuration `c` with the
deferred list `A` and `X = MaxCompletion(G_p, A)`, for Case 2 of `GetNext(c₀.G, Gt)`. -/
structure LoopInv (M : Model Q) (tie : Tie Q) (P : Program Q) (c₀ : Config Q) (Gt : Graph Q)
    (r₀ s₀ : Ev Q) (c : Config Q) (A : List (Ev Q)) (X : Graph Q) : Prop where
  /-- the configuration invariant -/
  inv : c.Inv M P
  /-- LI2: `MaxCompletion(G_p, A) = X ≠ ⊥` -/
  mc : maxCompletion tie P (prefixExt c₀.G Gt s₀) A = some X
  /-- LI1: `G ⊑ MaxCompletion(G_p, A)` -/
  pfx : Pfx M P c.G X
  /-- `A` starts with `r₀` (A.16 ⟨5⟩2) -/
  head : ∃ A', A = r₀ :: A'
  /-- `A` is duplicate-free -/
  nodup : A.Nodup
  /-- LI1: `A ⊆ G.E` -/
  sub : ∀ x ∈ A, x ∈ c.G.events
  /-- no deferred event is in `G_p` -/
  disj : ∀ x ∈ A, x ∉ (prefixExt c₀.G Gt s₀).events
  /-- `s₀` has not been added -/
  ns₀ : s₀ ∉ c.G.events
  /-- LI4 (no event of `G_s` revisited), as orders: `r₀` is inserted right after `G_s` -/
  ord : c₀.order ++ [r₀] <+: c.order
  /-- the events of `A` appear in the insertion order in the order of `A` (A.16 ⟨3⟩4) -/
  filt : c.order.filter (fun x => decide (x ∈ A)) = A
  /-- LI4 as graphs: `G_s` is a causal prefix of `G` -/
  base : c₀.G.IsPrefixOf c.G

namespace LoopInv

variable {c₀ c : Config Q} {Gt X : Graph Q} {r₀ s₀ : Ev Q} {A : List (Ev Q)}
variable (hx : Ctx M P c₀ Gt r₀ s₀) (hI : LoopInv M tie P c₀ Gt r₀ s₀ c A X)
include hx hI

omit hx in
theorem replay : Replay tie P (prefixExt c₀.G Gt s₀) A X := maxCompletion_replay hI.mc

/-- `G_p ⊑ X`. -/
theorem gp_pfx (hT : TieQ9 M tie) : Pfx M P (prefixExt c₀.G Gt s₀) X :=
  maxCompletion_pfx hT hx.gp_right.cons hx.gp_right.exec hI.mc

omit hx in
theorem mem_X {x : Ev Q} : x ∈ X.events ↔ x ∈ (prefixExt c₀.G Gt s₀).events ∨ x ∈ A := by
  rw [hI.replay.events, Finset.mem_union, List.mem_toFinset]

omit hx in
theorem r₀_mem : r₀ ∈ A := by
  obtain ⟨A', hA⟩ := hI.head
  rw [hA]
  exact List.mem_cons_self

/-- The graph grows strictly over the loop: `|G_s.E| < |G.E|`. -/
theorem card_lt : c₀.G.events.card < c.G.events.card := by
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hI.base.events_subset, ?_⟩)
  intro h
  exact hx.r₀_not_mem_c₀ (h ▸ hI.sub r₀ hI.r₀_mem)

/-- The events of the thread of `s₀` in `G` are in `G_p`. -/
theorem thr_sub (hT : TieQ9 M tie) {x : Ev Q} (hxc : x ∈ c.G.events) (hxt : x.tid = s₀.tid) :
    x ∈ (prefixExt c₀.G Gt s₀).events := by
  have hGpX := hI.gp_pfx hx hT
  have hcX := hI.pfx
  have hn := hx.nextEv_s₀
  have hidx : s₀.idx = (prefixExt c₀.G Gt s₀).cnt s₀.tid := Model.idx_of_nextEv hn
  by_cases hlt : x.idx < s₀.idx
  · obtain ⟨y, hy, hyt, hyi⟩ :=
      (hGpX.wf.exists_idx_iff s₀.tid x.idx).mpr (by rw [← hidx]; exact hlt)
    have := hcX.wf'.idx_inj y (hGpX.events_subset hy) x (hcX.events_subset hxc)
      (hyt.trans hxt.symm) hyi
    rwa [this] at hy
  · exfalso
    obtain ⟨z, hz, hzt, hzi⟩ : ∃ z ∈ c.G.events, z.tid = s₀.tid ∧ z.idx = s₀.idx := by
      rcases Nat.lt_or_eq_of_le (not_lt.mp hlt) with h | h
      · obtain ⟨z, hz, hzt, hzi⟩ := hI.inv.wf.idx_contig x hxc s₀.idx h
        exact ⟨z, hz, hzt.trans hxt, hzi⟩
      · exact ⟨x, hxc, hxt, h.symm⟩
    have := hGpX.eq_nextEv hn (hcX.events_subset hz) hzt (hzi.trans hidx)
    exact hI.ns₀ (this ▸ hz)

/-- The test of line 16 holds for the next event when it is in `G_p` or is `s₀` (A.16 ⟨8⟩2 for
`G_p`; for `s₀`, by `thr_sub`): `s₀` is never deferred. -/
theorem test_of (hT : TieQ9 M tie) {e : Ev Q} (hn : M.nextP P c.G = some e)
    (h : e ∈ (prefixExt c₀.G Gt s₀).events ∨ e = s₀) :
    LoopTest M P (prefixExt c₀.G Gt s₀) s₀ c.G e := by
  have hGpX := hI.gp_pfx hx hT
  refine ⟨(availPrefix_pfx_iff hI.pfx hGpX).mpr ?_, h⟩
  rcases h with h | rfl
  · exact availSet_subset_of_mem hI.pfx hGpX (nextEv_of_nextP hn) h
  · intro a ha
    obtain ⟨-, x, hx', hxt, hax⟩ := mem_availSet.mp ha
    have hxGp := hI.thr_sub hx hT hx' hxt
    rcases hax with rfl | hax
    · exact hxGp
    · have := (closed_iff_porf X _).mp hGpX.closed (hI.pfx.pre.porf_le hax)
        (Finset.mem_inter.mpr ⟨hGpX.events_subset hxGp, hxGp⟩)
      exact (Finset.mem_inter.mp this).2

/-- LI1, first clause: `next_P(G) ≠ ⊥`. If `G ≠ X`, a `porf`-minimal event of `X` not in `G` is
available; if `G = X`, then `s₀` is available (A.15 from `G_p`). -/
theorem exists_next (hT : TieQ9 M tie) : ∃ e, M.nextP P c.G = some e := by
  have hGpX := hI.gp_pfx hx hT
  by_cases hcX : c.G = X
  · have hs₀av : s₀ ∈ M.availM P (prefixExt c₀.G Gt s₀) :=
      M.mem_availM_iff'.mpr ⟨s₀.tid, tid_mem_of_nextEv hGpX.wf hGpX.exec hx.nextEv_s₀,
        hx.nextEv_s₀, Or.inl fun h => Lab.IsSend.not_isRecv hx.facts.2.1 (Lab.IsRecvB.isRecv h)⟩
    have hGpc : (prefixExt c₀.G Gt s₀).IsPrefixOf c.G := hcX ▸ hGpX.pre
    exact nextP_isSome_of_mem
      (availM_stable hGpX.cons hI.inv.cons hI.inv.exec hGpc hs₀av hI.ns₀)
  · obtain ⟨y, -, -, hy⟩ := exists_avail_of_sPfx (⟨hI.pfx, hcX⟩ : SPfx M P c.G X)
    exact nextP_isSome_of_mem hy

/-- A.16 ⟨3⟩3, repaired: at the break (`next_P(G) = s₀`), `G = MaxCompletion(G_p, A)`. The causal
predecessors of `s₀` in `G_t` are in `G`: `s₀` is the next event of its thread in `G`. -/
theorem eq_of_brk (hT : TieQ9 M tie) (hn : M.nextP P c.G = some s₀) : c.G = X := by
  have hGpX := hI.gp_pfx hx hT
  have hcX := hI.pfx
  have hGpGt := hx.gp_right
  have hGt := hx.dom.pfx.wf'
  have hidx : s₀.idx = c.G.cnt s₀.tid := Model.idx_of_nextEv (nextEv_of_nextP hn)
  refine hcX.eq_of_subset fun x hx' => ?_
  rcases (hI.mem_X).mp hx' with hxGp | hxA
  · rcases (mem_prefixExt hx.dom.pfx.events_subset).mp hxGp with h | ⟨-, hxs⟩
    · exact hI.base.events_subset h
    · obtain ⟨b, hxb, hbs⟩ := TransGen.tail'_iff.mp hxs
      have hbpo : Gt.po b s₀ := by
        rcases hbs with h | ⟨-, hrf⟩
        · exact h
        · rw [hGt.rf_none (Or.inr (Lab.IsSend.not_isRecv hx.facts.2.1))] at hrf
          cases hrf
      have hbGp : b ∈ (prefixExt c₀.G Gt s₀).events :=
        (mem_prefixExt hx.dom.pfx.events_subset).mpr
          (Or.inr ⟨hbpo.1, TransGen.single (Or.inl hbpo)⟩)
      have hbc : b ∈ c.G.events := by
        obtain ⟨y, hy, hyt, hyi⟩ :=
          (hI.inv.wf.exists_idx_iff s₀.tid b.idx).mpr (by rw [← hidx]; exact hbpo.2.2.2)
        have := hcX.wf'.idx_inj y (hcX.events_subset hy) b (hGpX.events_subset hbGp)
          (hyt.trans hbpo.2.2.1.symm) hyi
        rwa [this] at hy
      rcases reflTransGen_iff_eq_or_transGen.mp hxb with h | h
      · exact h ▸ hbc
      · have h1 := hGpX.pre.porf_le ((hGpGt.pre.porf_iff hbGp).mpr h)
        exact (Finset.mem_inter.mp ((closed_iff_porf X c.G.events).mp hcX.closed h1
          (Finset.mem_inter.mpr ⟨hGpX.events_subset hbGp, hbc⟩))).2
  · exact hI.sub x hxA

/-- A.16 ⟨6⟩2–⟨8⟩3: an event `e = next_P(G)` that fails the test of line 16 is not in `G_p`, is
not `s₀`, is not in `A`; it is available in `X = MaxCompletion(G_p, A)` (A.15), so
`MaxCompletion(G_p, A ++ [e])` exists, is above `X`, and contains `e`. -/
theorem defer_facts (hT : TieQ9 M tie) {e : Ev Q} (hn : M.nextP P c.G = some e)
    (hnt : ¬ LoopTest M P (prefixExt c₀.G Gt s₀) s₀ c.G e) :
    e ∉ (prefixExt c₀.G Gt s₀).events ∧ e ≠ s₀ ∧ e ∉ A ∧
      ∃ Y, maxCompletion tie P (prefixExt c₀.G Gt s₀) (A ++ [e]) = some Y ∧ Pfx M P X Y ∧
        e ∈ Y.events := by
  have heGp : e ∉ (prefixExt c₀.G Gt s₀).events :=
    fun h => hnt (hI.test_of hx hT hn (Or.inl h))
  have hes : e ≠ s₀ := fun h => hnt (hI.test_of hx hT hn (Or.inr h))
  have hec : e ∉ c.G.events :=
    hI.inv.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv (nextEv_of_nextP hn))
  have heA : e ∉ A := fun h => hec (hI.sub e h)
  have heX : e ∉ X.events := fun h => by
    rcases (hI.mem_X).mp h with h | h
    exacts [heGp h, heA h]
  have hav := availM_stable hI.inv.cons hI.pfx.cons' hI.pfx.exec' hI.pfx.pre
    (Model.mem_availM_of_nextP hn) heX
  obtain ⟨Y, hY, hs, hXY⟩ := maxCompletion_snoc hT hx.gp_right.cons hx.gp_right.exec hI.mc hav
  refine ⟨heGp, hes, heA, Y, hY, hXY, ?_⟩
  obtain ⟨-, src, out, -, rfl⟩ := hs
  exact Finset.mem_insert_self _ _

end LoopInv

/-- One iteration of the loop preserves the invariant (A.16 ⟨4⟩1, ⟨4⟩2): after
`GetNext(G, MaxCompletion(G_p, A'))` with `A' = A` (the test of line 16 holds, `e ∈ G_p`) or
`A' = A ++ [e]` (`e` deferred). The hypotheses on the old state hold for every state of the loop
and for the initial state `(c₀, [])`. -/
theorem loopInv_of_call {c₀ : Config Q} {Gt : Graph Q} {r₀ s₀ : Ev Q}
    (hx : Ctx M P c₀ Gt r₀ s₀) {c : Config Q} {A A' : List (Ev Q)}
    {e : Ev Q} {X' : Graph Q} {S : List (Config Q)} {c₁ : Config Q}
    (hinv : c.Inv M P) (hnd : A.Nodup) (hsub : ∀ x ∈ A, x ∈ c.G.events)
    (hdisj : ∀ x ∈ A, x ∉ (prefixExt c₀.G Gt s₀).events)
    (hfilt : c.order.filter (fun x => decide (x ∈ A)) = A) (hbase : c₀.G.IsPrefixOf c.G)
    (hpre : c₀.order ++ [r₀] <+: c.order ++ [e]) (hn : M.nextP P c.G = some e)
    (hA' : (A' = A ∧ e ∈ (prefixExt c₀.G Gt s₀).events) ∨
      (A' = A ++ [e] ∧ e ∉ (prefixExt c₀.G Gt s₀).events))
    (hhead : ∃ A'', A' = r₀ :: A'') (hs₀ : s₀ ∉ A')
    (hmc : maxCompletion tie P (prefixExt c₀.G Gt s₀) A' = some X')
    (hspec : CallSpec M tie P c X' e S c₁) : LoopInv M tie P c₀ Gt r₀ s₀ c₁ A' X' := by
  have hec : e ∉ c.G.events :=
    hinv.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv (nextEv_of_nextP hn))
  have heo : e ∉ c.order := fun h => hec ((hinv.mem e).mp h)
  have hinv₁ := (hspec.path.inv hinv).1
  have hsub₁ : c.G.events ⊆ c₁.G.events := hspec.spfx.1.events_subset
  have hA'mem : ∀ x, x ∈ A' → x ∈ A ∨ x = e := by
    intro x hx'
    rcases hA' with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl hx'
    · simpa using hx'
  have hX' : X'.events = (prefixExt c₀.G Gt s₀).events ∪ A'.toFinset :=
    (maxCompletion_replay hmc).events
  refine ⟨hinv₁, hmc, hspec.pfx, hhead, ?_, ?_, ?_, ?_, hpre.trans hspec.ord, ?_,
    hbase.trans hspec.spfx.1.pre⟩
  · rcases hA' with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hnd
    · refine List.nodup_append.mpr ⟨hnd, List.nodup_singleton e, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb
      subst hb
      exact fun h => hec (h ▸ hsub a ha)
  · intro x hx'
    rcases hA'mem x hx' with h | rfl
    · exact hsub₁ (hsub x h)
    · exact hspec.mem
  · intro x hx'
    rcases hA' with ⟨rfl, -⟩ | ⟨rfl, he⟩
    · exact hdisj x hx'
    · rcases List.mem_append.mp hx' with h | h
      · exact hdisj x h
      · rw [List.mem_singleton] at h
        exact h ▸ he
  · intro h
    have := hspec.pfx.events_subset h
    rw [hX', Finset.mem_union, List.mem_toFinset] at this
    rcases this with h | h
    · exact hx.s₀_not_mem h
    · exact hs₀ h
  · obtain ⟨L, hL⟩ := hspec.ord
    have hnd₁ := hinv₁.nodup
    rw [← hL] at hnd₁ ⊢
    have hLA : ∀ x ∈ L, x ∉ A' := by
      intro x hxL hxA
      have hd := (List.nodup_append.mp hnd₁).2.2
      rcases hA'mem x hxA with h | rfl
      · have hxo : x ∈ c.order := (hinv.mem x).mpr (hsub x h)
        exact hd x (List.mem_append_left _ hxo) x hxL rfl
      · exact hd x (List.mem_append_right _ (List.mem_singleton_self x)) x hxL rfl
    have hLnil : L.filter (fun x => decide (x ∈ A')) = [] :=
      List.filter_eq_nil_iff.mpr (fun x hx => by simpa using hLA x hx)
    rw [List.filter_append, List.filter_append, hLnil, List.append_nil]
    rcases hA' with ⟨rfl, heGp⟩ | ⟨rfl, -⟩
    · have heA : e ∉ A' := fun h => hdisj e h heGp
      rw [hfilt]
      simp [heA]
    · have : c.order.filter (fun x => decide (x ∈ A ++ [e])) =
          c.order.filter (fun x => decide (x ∈ A)) :=
        List.filter_congr fun x hx => by
          have hxe : x ≠ e := fun h => heo (h ▸ hx)
          simp [hxe]
      rw [this, hfilt]
      simp

/-- The loop of lines 15–21 reaches the break (A.16 ⟨3⟩3, by induction on the remaining capacity
`N − |G.E|`, `N = |threads| · n`), given `GetNext` with its specification on every call from a
configuration with more events than `G_s` (the outer induction). -/
theorem loop_exists (hT : TieQ9 M tie) {n : ℕ} (hb : P.Bounded n) {c₀ : Config Q}
    {Gt : Graph Q} {r₀ s₀ : Ev Q} (hx : Ctx M P c₀ Gt r₀ s₀)
    (IH : ∀ (c : Config Q) (X : Graph Q) (e : Ev Q), CallDom M P c X e →
      c₀.G.events.card < c.G.events.card →
      ∃ S c', GetNext M tie P (.call c X) S c' ∧ CallSpec M tie P c X e S c') :
    ∀ (k : ℕ) (c : Config Q) (A : List (Ev Q)) (X : Graph Q),
      P.threads.length * n - c.G.events.card = k → LoopInv M tie P c₀ Gt r₀ s₀ c A X →
      ∃ S cL AL XL, GetNext M tie P (.loop (prefixExt c₀.G Gt s₀) s₀ c A) S cL ∧
        StepSeq M tie P c S cL ∧ (∀ d ∈ S, c.order <+: d.order ∧ c.G.IsPrefixOf d.G) ∧
        M.nextP P cL.G = some s₀ ∧ LoopInv M tie P c₀ Gt r₀ s₀ cL AL XL := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro c A X hk hI
  obtain ⟨e, hn⟩ := hI.exists_next hx hT
  by_cases hes : e = s₀
  · subst hes
    exact ⟨[], c, A, X, .brk hn (hI.test_of hx hT hn (Or.inr rfl)), .nil c,
      fun _ h => absurd h List.not_mem_nil, hn, hI⟩
  have hcard := hI.card_lt hx
  have keep : ∀ {X' : Graph Q} {S₁ : List (Config Q)} {c₁ : Config Q} {S₂ : List (Config Q)},
      CallSpec M tie P c X' e S₁ c₁ →
      (∀ d ∈ S₂, c₁.order <+: d.order ∧ c₁.G.IsPrefixOf d.G) →
      ∀ d ∈ S₁ ++ S₂, c.order <+: d.order ∧ c.G.IsPrefixOf d.G := by
    intro X' S₁ c₁ S₂ hs₁ hk₂ d hd
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨h1, h2⟩ := hs₁.keep d hd
      exact ⟨(List.prefix_append _ _).trans h1, h2⟩
    · obtain ⟨h1, h2⟩ := hk₂ d hd
      exact ⟨((List.prefix_append _ _).trans hs₁.ord).trans h1, hs₁.spfx.1.pre.trans h2⟩
  have hlt : ∀ {X' : Graph Q} {S₁ : List (Config Q)} {c₁ : Config Q},
      CallSpec M tie P c X' e S₁ c₁ → P.threads.length * n - c₁.G.events.card < k := by
    intro X' S₁ c₁ hs₁
    have hinv₁ := (hs₁.path.inv hI.inv).1
    have h1 := hs₁.spfx.card_lt
    have h2 := card_le_of_bounded hinv₁.wf hinv₁.exec hb
    omega
  by_cases ht : LoopTest M P (prefixExt c₀.G Gt s₀) s₀ c.G e
  · have heGp : e ∈ (prefixExt c₀.G Gt s₀).events := ht.2.resolve_right hes
    obtain ⟨S₁, c₁, h₁, hs₁⟩ :=
      IH c X e ⟨hI.inv, hI.pfx, hn, (hI.gp_pfx hx hT).events_subset heGp⟩ hcard
    have hI₁ : LoopInv M tie P c₀ Gt r₀ s₀ c₁ A X :=
      loopInv_of_call hx hI.inv hI.nodup hI.sub hI.disj hI.filt hI.base
        (hI.ord.trans (List.prefix_append _ _)) hn (Or.inl ⟨rfl, heGp⟩) hI.head
        (fun h => hI.ns₀ (hI.sub _ h)) hI.mc hs₁
    obtain ⟨S₂, cL, AL, XL, h₂, hp₂, hk₂, hnL, hIL⟩ := ih _ (hlt hs₁) c₁ A X rfl hI₁
    exact ⟨S₁ ++ S₂, cL, AL, XL, .good hn hes ht hI.mc h₁ h₂, hs₁.path.append hp₂,
      keep hs₁ hk₂, hnL, hIL⟩
  · obtain ⟨heGp, -, -, Y, hY, hXY, heY⟩ := hI.defer_facts hx hT hn ht
    obtain ⟨S₁, c₁, h₁, hs₁⟩ := IH c Y e ⟨hI.inv, hI.pfx.trans hXY, hn, heY⟩ hcard
    obtain ⟨A'', hA''⟩ := hI.head
    have hs₀A : s₀ ∉ A ++ [e] := by
      rw [List.mem_append, List.mem_singleton, not_or]
      exact ⟨fun h => hI.ns₀ (hI.sub _ h), fun h => hes h.symm⟩
    have hI₁ : LoopInv M tie P c₀ Gt r₀ s₀ c₁ (A ++ [e]) Y :=
      loopInv_of_call hx hI.inv hI.nodup hI.sub hI.disj hI.filt hI.base
        (hI.ord.trans (List.prefix_append _ _)) hn (Or.inr ⟨rfl, heGp⟩)
        ⟨A'' ++ [e], by rw [hA'']; rfl⟩ hs₀A hY hs₁
    obtain ⟨S₂, cL, AL, XL, h₂, hp₂, hk₂, hnL, hIL⟩ := ih _ (hlt hs₁) c₁ _ Y rfl hI₁
    exact ⟨S₁ ++ S₂, cL, AL, XL, .defer hn ht hY h₁ h₂, hs₁.path.append hp₂,
      keep hs₁ hk₂, hnL, hIL⟩

end Must

#print axioms Must.Ctx.r₀_not_mem
#print axioms Must.Ctx.not_test
#print axioms Must.LoopInv.card_lt
#print axioms Must.LoopInv.thr_sub
#print axioms Must.LoopInv.test_of
#print axioms Must.LoopInv.exists_next
#print axioms Must.LoopInv.eq_of_brk
#print axioms Must.LoopInv.defer_facts
#print axioms Must.loopInv_of_call
#print axioms Must.loop_exists
