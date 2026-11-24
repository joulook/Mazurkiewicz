import Mazurkiewicz.Must.OptimalUnique
import Mazurkiewicz.Must.AlgCompute

/-!
# One step is one branch (milestone M9)

Paper: Algorithm 1 (lines 6–13). Plan: row M9; reviews of M8 (Opus N2, Astra item 2).

Relational branch injectivity, for a configuration `c` with `Inv`:

* `nrAdd_inj`: two non-revisit additions with the same successor add the same event with the
  same source and outcome (ND value, receive source).
* `nr_ne_revisit`: a non-revisit addition and a revisit never give the same successor (in the
  revisit the receive reads the fresh send; in an addition no receive reads it).
* `revisit_inj`: two revisits by the same send with the same successor revisit the same receive.
* `StepM.branch_inj`: the three together, for `StepM` edges described by their branch label.

Computed successor list: `stepM_nodup`: for a model with a decision procedure `consB` (on
graphs with `Supp`) and every selection `T`, the successor list of M2's `stepM` with the
repaired variant has no duplicates, on configurations with `Inv` (so for `asyn`, `p2p`, `cd`:
`stepM_nodup_asyn`, `stepM_nodup_p2p`, `stepM_nodup_cd`). Together with M4's `mem_stepM_iff`
the list is a duplicate-free enumeration of exactly the `StepM`-successors.
-/

namespace Must

open Graph Config

variable {Q : Type} [DecidableEq Q] [Membership Val Q]
variable {M : Model Q} {P : Program Q} {tie : Tie Q}

/-! ### Relational branch injectivity -/

omit [Membership Val Q] in
/-- Additions of the same event to the same configuration agree iff source and outcome do. -/
theorem add_inj {c : Config Q} {e e' : Ev Q} {src src' : Option (Src Q)} {out out' : Option Val}
    (he : e = e') (h : c.add e src out = c.add e' src' out') : src = src' ∧ out = out' := by
  subst he
  have h1 := congrArg (fun d : Config Q => d.G.rf e) h
  have h2 := congrArg (fun d : Config Q => d.G.nd e) h
  simp only [Config.add, add_rf, add_nd, Function.update_self] at h1 h2
  exact ⟨h1, h2⟩

/-- Two non-revisit additions with the same successor are the same branch (same event, same
receive source, same ND outcome). -/
theorem nrAdd_inj {c : Config Q} {e e' : Ev Q} {src src' : Option (Src Q)}
    {out out' : Option Val} (h₁ : NrAdd M P c.G e src out) (h₂ : NrAdd M P c.G e' src' out')
    (h : c.add e src out = c.add e' src' out') : e = e' ∧ src = src' ∧ out = out' := by
  have he : e = e' := Option.some.inj (h₁.1.symm.trans h₂.1)
  exact ⟨he, add_inj he h⟩

/-- The core of `nr_ne_revisit`: adding the fresh send `e` without revisit differs from every
revisit of an event `r` of the graph by `e`. -/
theorem add_ne_revisitCfg {c : Config Q} {t : Tid} {e r : Ev Q} (hc : c.Inv M P)
    (ht : P.nextEv c.G t = some e) (hr : r ∈ (c.add e none none).G.events) (hre : r ≠ e) :
    c.add e none none ≠ (c.add e none none).revisitCfg r e := by
  intro heq
  have heA := hc.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv ht)
  have hrd : r ∉ (c.add e none none).del r e := fun h => lt_irrefl _ (mem_del.mp h).2.2.1
  have h1 := revisitCfg_rf (r := r) (s := e) hr hrd
  simp only [↓reduceIte] at h1
  rw [← heq] at h1
  simp only [Config.add, add_rf, Function.update_of_ne hre] at h1
  exact heA (hc.wf.rf_mem _ _ h1)

/-- A non-revisit step and a revisit step never give the same successor. -/
theorem nr_ne_revisit {c : Config Q} {e e' r : Ev Q} {src : Option (Src Q)} {out : Option Val}
    (hc : c.Inv M P) (hn : M.nextP P c.G = some e) (hnr : NrAdd M P c.G e' src out)
    (hg : RevGuard tie (c.add e none none) r e)
    (heq : c.add e' src out = (c.add e none none).revisitCfg r e) : False := by
  have he' : e' = e := Option.some.inj (hnr.1.symm.trans hn)
  subst he'
  obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hn
  have hre : r ≠ e' := fun h => Lab.IsSend.not_isRecv hg.smatch.isSend (h ▸ hg.recv)
  rcases hnr.2 with ⟨S, v, hl, -⟩ | ⟨hR, -⟩ | ⟨-, rfl, rfl, -⟩ | ⟨hL, -⟩
  · have h := hg.smatch.isSend
    simp [Ev.IsSend, hl, Lab.IsSend] at h
  · exact Lab.IsSend.not_isRecv hg.smatch.isSend hR
  · exact add_ne_revisitCfg hc ht hg.mem hre heq
  · obtain ⟨m, d, w, h⟩ := (Lab.isSend_iff _).mp hg.smatch.isSend
    simp [Ev.IsLoc, h, Lab.IsLoc] at hL

/-- The core of `revisit_inj`: two revisits by the fresh send `e` with the same successor revisit
the same receive (only the first receive is assumed to be an event of the graph). -/
theorem revisitCfg_inj {c : Config Q} {t : Tid} {e r₁ r₂ : Ev Q} (hc : c.Inv M P)
    (ht : P.nextEv c.G t = some e) (hr₁ : r₁ ∈ (c.add e none none).G.events)
    (heq : (c.add e none none).revisitCfg r₁ e = (c.add e none none).revisitCfg r₂ e) :
    r₁ = r₂ := by
  by_contra hne
  obtain ⟨-, hread, -⟩ := addSend_facts hc ht
  have hrd₁ : r₁ ∉ (c.add e none none).del r₁ e := fun h => lt_irrefl _ (mem_del.mp h).2.2.1
  have h1 := revisitCfg_rf (r := r₁) (s := e) hr₁ hrd₁
  simp only [↓reduceIte] at h1
  rw [heq] at h1
  have hin : r₁ ∈ ((c.add e none none).revisitCfg r₂ e).G.events := by
    by_contra hno
    have : ((c.add e none none).revisitCfg r₂ e).G.rf r₁ = none := by
      simp only [revisitCfg, Graph.revisit, restrict_rf]
      split_ifs with hh
      · exact absurd (by
          simp only [revisitCfg, Graph.revisit, restrict_events, setRF_events, Finset.mem_inter]
          exact ⟨(Finset.mem_sdiff.mp hh).1, hh⟩) hno
      · rfl
    rw [this] at h1
    cases h1
  obtain ⟨hH, hd⟩ := mem_revisitCfg_events.mp hin
  rw [revisitCfg_rf hH hd] at h1
  simp only [hne, ↓reduceIte] at h1
  exact hread r₁ h1

/-- Two revisit branches by the same send with the same successor revisit the same receive. -/
theorem revisit_inj {c : Config Q} {e r₁ r₂ : Ev Q} (hc : c.Inv M P)
    (hn : M.nextP P c.G = some e) (hg₁ : RevGuard tie (c.add e none none) r₁ e)
    (heq : (c.add e none none).revisitCfg r₁ e = (c.add e none none).revisitCfg r₂ e) :
    r₁ = r₂ := by
  obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hn
  exact revisitCfg_inj hc ht hg₁.mem heq

/-- A branch of Algorithm 1 at a configuration: a non-revisit addition (event, source,
outcome; lines 6, 7, 9, 14), or the revisit of a receive by the added send (lines 10–13). -/
inductive Branch (Q : Type)
  /-- a non-revisit addition -/
  | nr (e : Ev Q) (src : Option (Src Q)) (out : Option Val)
  /-- the revisit of the receive `r` by the send `e` -/
  | rev (e r : Ev Q)

/-- The branch `b` is enabled at `c` and leads to `d`. -/
def BranchStep (M : Model Q) (tie : Tie Q) (P : Program Q) (c : Config Q) :
    Branch Q → Config Q → Prop
  | .nr e src out, d => NrAdd M P c.G e src out ∧ d = c.add e src out
  | .rev e r, d => M.nextP P c.G = some e ∧ e.IsSend ∧ RevGuard tie (c.add e none none) r e ∧
      M.cons ((c.add e none none).revisitCfg r e).G ∧ d = (c.add e none none).revisitCfg r e

/-- The `StepM` edges are exactly the enabled branches. -/
theorem stepM_iff_branch {c d : Config Q} : StepM M tie P c d ↔ ∃ b, BranchStep M tie P c b d := by
  constructor
  · rintro (⟨h⟩ | ⟨h1, h2, h3, h4⟩)
    · exact ⟨.nr _ _ _, h, rfl⟩
    · exact ⟨.rev _ _, h1, h2, h3, h4, rfl⟩
  · rintro ⟨_ | _, h⟩
    · obtain ⟨h, rfl⟩ := h
      exact .nr h
    · obtain ⟨h1, h2, h3, h4, rfl⟩ := h
      exact .revisit h1 h2 h3 h4

/-- **Branch injectivity**: on a configuration with `Inv`, two enabled branches with the same
successor are the same branch. So one `StepM` edge is one branch of Algorithm 1. -/
theorem StepM.branch_inj {c d : Config Q} {b₁ b₂ : Branch Q} (hc : c.Inv M P)
    (h₁ : BranchStep M tie P c b₁ d) (h₂ : BranchStep M tie P c b₂ d) : b₁ = b₂ := by
  rcases b₁ with ⟨e₁, s₁, o₁⟩ | ⟨e₁, r₁⟩ <;> rcases b₂ with ⟨e₂, s₂, o₂⟩ | ⟨e₂, r₂⟩
  · obtain ⟨h₁, rfl⟩ := h₁
    obtain ⟨h₂, h⟩ := h₂
    obtain ⟨rfl, rfl, rfl⟩ := nrAdd_inj h₁ h₂ h
    rfl
  · obtain ⟨h₁, rfl⟩ := h₁
    obtain ⟨n₂, -, g₂, -, h⟩ := h₂
    exact (nr_ne_revisit hc n₂ h₁ g₂ h).elim
  · obtain ⟨n₁, -, g₁, -, rfl⟩ := h₁
    obtain ⟨h₂, h⟩ := h₂
    exact (nr_ne_revisit hc n₁ h₂ g₁ h.symm).elim
  · obtain ⟨n₁, -, g₁, -, rfl⟩ := h₁
    obtain ⟨n₂, -, -, -, h⟩ := h₂
    obtain rfl : e₁ = e₂ := Option.some.inj (n₁.symm.trans n₂)
    rw [revisit_inj hc n₁ g₁ h]

/-! ### The computed successor list has no duplicates -/

variable [∀ (v : Val) (q : Q), Decidable (v ∈ q)] {consB : Graph Q → Bool}

omit [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
theorem nodup_ndList (S : Finset Val) : (ndList S).Nodup :=
  List.nodup_range.filter _

omit [Membership Val Q] [∀ (v : Val) (q : Q), Decidable (v ∈ q)] in
/-- `filterMap` of a duplicate-free list by a function injective on the list. -/
theorem nodup_filterMap_on {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, l.Nodup → (∀ a ∈ l, ∀ a' ∈ l, ∀ b, f a = some b → f a' = some b → a = a') →
      (l.filterMap f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hl, h => by
    obtain ⟨ha, hl'⟩ := List.nodup_cons.mp hl
    have ih := nodup_filterMap_on hl' (fun x hx y hy => h x (.tail _ hx) y (.tail _ hy))
    rw [List.filterMap_cons]
    cases hfa : f a with
    | none => exact ih
    | some b =>
      refine List.nodup_cons.mpr ⟨fun hb => ?_, ih⟩
      obtain ⟨a', ha', hfa'⟩ := List.mem_filterMap.mp hb
      exact ha ((h a (.head _) a' (.tail _ ha') b hfa hfa').symm ▸ ha')

/-- M2's revisit list (repaired variant) as a `filterMap` producing `revisitCfg`. -/
theorem revisitsOf_repaired (T : Sel Q) (H : Config Q) (s : Ev Q) :
    revisitsOf consB (Variant.repaired consB T) H s =
      (H.order.filter (fun r => decide (r.IsRecv ∧ s.Matches r ∧ ¬ H.G.porf r s))).filterMap
        fun r => if (decide (∀ d ∈ insert r (H.del r s), revCond (oracleQ9 consB T) H d s = true)
            && revCond (oracleQ9 consB T) H s s) = true
          then (if consB (H.revisitCfg r s).G = true then some (H.revisitCfg r s) else none)
          else none := by
  unfold revisitsOf
  rfl

/-- M2's revisit list by the fresh send `e` (repaired variant) has no duplicates and does not
contain the non-revisit successor. -/
theorem revisitsOf_nodup (T : Sel Q) {c : Config Q} {t : Tid} {e : Ev Q} (hc : c.Inv M P)
    (ht : P.nextEv c.G t = some e) (hS : e.IsSend) :
    (revisitsOf consB (Variant.repaired consB T) (c.add e none none) e).Nodup ∧
      c.add e none none ∉ revisitsOf consB (Variant.repaired consB T) (c.add e none none) e := by
  have hmem : ∀ x, x ∈ (c.add e none none).order ↔ x ∈ (c.add e none none).G.events := by
    intro x
    simp only [Config.add, List.mem_append, List.mem_singleton, add_events,
      Finset.mem_insert, hc.mem]
    exact or_comm
  have hnd : (c.add e none none).order.Nodup := by
    simp only [Config.add]
    refine List.nodup_append.mpr ⟨hc.nodup, List.nodup_singleton _, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton] at hb
    subst hab hb
    exact hc.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv ht) ((hc.mem _).mp ha)
  have hval : ∀ r b, (if (decide (∀ d ∈ insert r ((c.add e none none).del r e),
        revCond (oracleQ9 consB T) (c.add e none none) d e = true)
        && revCond (oracleQ9 consB T) (c.add e none none) e e) = true
      then (if consB ((c.add e none none).revisitCfg r e).G = true
        then some ((c.add e none none).revisitCfg r e) else none) else none) = some b →
      b = (c.add e none none).revisitCfg r e := by
    intro r b hb
    split_ifs at hb
    exact (Option.some.inj hb).symm
  rw [revisitsOf_repaired]
  constructor
  · refine nodup_filterMap_on (hnd.filter _) (fun r₁ h₁ r₂ _ b hb₁ hb₂ => ?_)
    have hr₁ := (hmem r₁).mp (List.mem_filter.mp h₁).1
    exact revisitCfg_inj hc ht hr₁ ((hval _ _ hb₁).symm.trans (hval _ _ hb₂))
  · intro h
    obtain ⟨r, hr, hb⟩ := List.mem_filterMap.mp h
    obtain ⟨hro, hp⟩ := List.mem_filter.mp hr
    have hR := (of_decide_eq_true hp).1
    have hre : r ≠ e := fun h => Lab.IsSend.not_isRecv hS (h ▸ hR)
    exact add_ne_revisitCfg hc ht ((hmem r).mp hro) hre (hval _ _ hb)

/-- **The computed successor list has no duplicates**: for a model `M` with a decision
procedure `consB` (agreeing with `M.cons` on graphs with `Supp`), every selection `T`, every
program and every configuration with `Inv`, M2's `stepM` with the repaired variant lists every
successor once. -/
theorem stepM_nodup (hc : ∀ H : Graph Q, H.Supp → (consB H = true ↔ M.cons H)) (T : Sel Q)
    (P : Program Q) {c : Config Q} (hi : c.Inv M P) :
    ((stepM consB (Variant.repaired consB T) P c).getD []).Nodup := by
  have hn : (Variant.repaired consB T).next P c.G = M.nextP P c.G :=
    Model.nextP_eq consB hc P hi.wf.supp
  unfold stepM
  rw [hn]
  rcases hne : M.nextP P c.G with _ | e
  · exact List.nodup_nil
  obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hne
  simp only [Option.getD_some]
  split
  next S hl =>
    refine (nodup_ndList S).map_on (fun v _ w _ h => ?_)
    exact Option.some.inj (add_inj rfl h).2
  next a vals hl =>
    refine nodup_filterMap_on ?_ (fun x _ y _ b hx hy => ?_)
    · refine List.nodup_append.mpr ⟨(hi.nodup.filter _).map (fun _ _ h => Src.snd.inj h),
        List.nodup_singleton _, ?_⟩
      intro a ha b hb hab
      rw [List.mem_singleton] at hb
      subst hb
      obtain ⟨d, -, rfl⟩ := List.mem_map.mp ha
      cases hab
    · split_ifs at hx hy
      have h := (Option.some.inj hx).trans (Option.some.inj hy).symm
      exact Option.some.inj (add_inj rfl h).1
  next m dst v hl =>
    have hS : e.IsSend := by simp [Ev.IsSend, hl, Lab.IsSend]
    obtain ⟨h1, h2⟩ := revisitsOf_nodup (consB := consB) T hi ht hS
    refine List.nodup_append.mpr ⟨?_, h1, ?_⟩
    · split_ifs
      · exact List.nodup_singleton _
      · exact List.nodup_nil
    · intro a ha b hb hab
      split_ifs at ha
      · rw [List.mem_singleton] at ha
        subst ha hab
        exact h2 hb
      · exact absurd ha List.not_mem_nil
  next => exact List.nodup_singleton _

/-- The computed successors of a configuration with `Inv`: a duplicate-free list of exactly
the `StepM`-successors (M4's `mem_stepM_iff` and `stepM_nodup`). -/
theorem stepM_spec (hc : ∀ H : Graph Q, H.Supp → (consB H = true ↔ M.cons H)) (T : Sel Q)
    (P : Program Q) {c : Config Q} (hi : c.Inv M P) :
    ((stepM consB (Variant.repaired consB T) P c).getD []).Nodup ∧
      ∀ c', c' ∈ (stepM consB (Variant.repaired consB T) P c).getD [] ↔
        StepM M (T.pick consB) P c c' :=
  ⟨stepM_nodup hc T P hi, mem_stepM_iff hc T P hi⟩

/-- `stepM_nodup` for `asyn` (`consAsynB`). -/
theorem stepM_nodup_asyn (T : Sel Q) (P : Program Q) {c : Config Q} (hi : c.Inv Model.asyn P) :
    ((stepM consAsynB (Variant.repaired consAsynB T) P c).getD []).Nodup :=
  stepM_nodup consAsynB_iff_asyn T P hi

/-- `stepM_nodup` for `p2p` (`consAPB`). -/
theorem stepM_nodup_p2p (T : Sel Q) (P : Program Q) {c : Config Q} (hi : c.Inv Model.p2p P) :
    ((stepM consAPB (Variant.repaired consAPB T) P c).getD []).Nodup :=
  stepM_nodup consAPB_iff_p2p T P hi

/-- `stepM_nodup` for `cd` (`consCDB`). -/
theorem stepM_nodup_cd (T : Sel Q) (P : Program Q) {c : Config Q} (hi : c.Inv Model.cd P) :
    ((stepM Model.consCDB (Variant.repaired Model.consCDB T) P c).getD []).Nodup :=
  stepM_nodup (fun _ hH => Model.consCDB_iff hH) T P hi

end Must

#print axioms Must.add_inj
#print axioms Must.nrAdd_inj
#print axioms Must.add_ne_revisitCfg
#print axioms Must.nr_ne_revisit
#print axioms Must.revisitCfg_inj
#print axioms Must.revisit_inj
#print axioms Must.stepM_iff_branch
#print axioms Must.StepM.branch_inj
#print axioms Must.nodup_filterMap_on
#print axioms Must.revisitsOf_repaired
#print axioms Must.revisitsOf_nodup
#print axioms Must.stepM_nodup
#print axioms Must.stepM_spec
#print axioms Must.stepM_nodup_asyn
#print axioms Must.stepM_nodup_p2p
#print axioms Must.stepM_nodup_cd
