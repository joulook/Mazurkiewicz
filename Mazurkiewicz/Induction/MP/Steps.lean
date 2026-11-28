import Mazurkiewicz.Induction.MP.Defs
import Mazurkiewicz.Must.AlgSound

/-!
# Message passing: steps, reachability, terminal executions (Track C, milestone C1a)

`induction-popl`, `prelim.tex` (def:step, prop:reach-exec, def:safety) and `mp.tex`
(lem:prefix-steps, def:terminal `Term`, lem:terminal (1)) for the graphs, programs and models
of the Must port, every `Must.Model` (plan `plan/ind/TRACK-C-PLAN.md`, milestone C1a).

* def:step: `PStep M P G G'` (`G'.E = G.E ⊎ {e}`, `G = G'|G.E`, `G'` a consistent execution of
  `P`); `pstep_iff`: from `G ∈ Exec_M(P)` it is the port's operational step `OpStepG`.
* prop:reach-exec: `MReach M P G` (operational reachability from the empty graph) iff
  `G ∈ Exec_M(P)` (`mreach_iff`).
* `StepsN M P n G G'`: `n` steps; `stepsN_iff`: from `G ∈ Exec_M(P)`, `n` steps reach exactly
  the consistent executions that have `G` as a prefix and `n` more events.
* lem:prefix-steps (`prefix_steps`): a prefix `G ⊑ G'` in `Exec_M(P)` reaches `G'` in
  `|G'| - |G|` steps, and every graph between them is a prefix of `G'`.
* def:safety: `Safe`. `Term M P G`: reachable without a step; `term_iff_sem`: `Term` is the
  port's repaired `⟦P⟧` (`Model.Sem`) (ass:must (c), the R-claim of the plan, Section 2.5).
* lem:terminal (1), for every `Must.Model`: `Stuck`, `term_iff_stuck`.
-/

namespace Must

namespace Ind

open Graph Relation

variable {Q : Type} [DecidableEq Q] [Membership Val Q]
variable {M : Model Q} {P : Program Q} {G G' : Graph Q}

/-! ### Steps -/

/-- A step `G →_{P,M} G'` (def:step). -/
def PStep (M : Model Q) (P : Program Q) (G G' : Graph Q) : Prop :=
  G.Wf ∧ ∃ e, e ∉ G.events ∧ G'.events = insert e G.events ∧ G = G'.restrict G.events ∧
    P.Exec G' ∧ M.cons G'

/-- def:step is the port's operational step, from a consistent execution. Counterexample with
only `M.cons G` (Astra, plan C1a): `G` with a well-formed send that disagrees with thread 1's
program, thread 2 enabled: `OpStepG` holds, `P.Exec G'` fails. -/
theorem pstep_iff (hG : ExecM M P G) : PStep M P G G' ↔ OpStepG M P G G' := by
  constructor
  · rintro ⟨hGw, e, he, hev, hres, hE', hc'⟩
    have hG'w := M.wf _ hc'
    have heG' : e ∈ G'.events := by rw [hev]; exact Finset.mem_insert_self _ _
    have hsub : ∀ x ∈ G.events, x ∈ G'.events := fun x hx => by
      rw [hev]; exact Finset.mem_insert_of_mem hx
    have hmax : ∀ b, ¬ G'.porfStep e b := by
      rintro b (⟨-, hb, ht, hi⟩ | ⟨hb, hrf⟩)
      · have hbe : b ≠ e := fun h => by rw [h] at hi; exact lt_irrefl _ hi
        have hbG : b ∈ G.events := by
          rw [hev, Finset.mem_insert] at hb
          exact hb.resolve_left hbe
        obtain ⟨e', he', ht', hi'⟩ := hGw.idx_contig b hbG e.idx hi
        have := hG'w.idx_inj e' (hsub e' he') e heG' (ht'.trans ht.symm) hi'
        exact he (this ▸ he')
      · have hm := hG'w.rf_match _ _ hrf
        have hbe : b ≠ e := fun h => Lab.IsSend.not_isRecv hm.isSend (h ▸ hm.isRecv)
        have hbG : b ∈ G.events := by
          rw [hev, Finset.mem_insert] at hb
          exact hb.resolve_left hbe
        have hrfG : G.rf b = some (.snd e) := by
          rw [hres]
          simpa [hbG] using hrf
        exact he (hGw.rf_mem _ _ hrfG)
    obtain ⟨hop, hback⟩ := Graph.Wf.opAdd_remove_max hc' hE' heG' hmax
    have hrem : G'.remove {e} = G := by
      rw [hres]
      unfold Graph.remove
      congr 1
      ext x
      rw [hev, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd h1 h2
        · exact h1
      · intro hx
        exact ⟨Or.inr hx, fun h => he (h ▸ hx)⟩
    rw [hrem] at hop hback
    exact ⟨e, _, _, hop, hback.symm⟩
  · rintro ⟨e, src, out, hop, rfl⟩
    have hGw := M.wf _ hG.2
    obtain ⟨t, ht⟩ := hop.nextEv
    have hidx := Model.idx_of_nextEv ht
    have he := hGw.not_mem_of_idx_eq_cnt hidx
    refine ⟨hGw, e, he, rfl, ?_, P.exec_add hG.1 hGw ht src out, hop.2.2⟩
    rw [restrict_add_of_not_mem he, hGw.restrict_self]

/-- Reachability `G ∈ Reach_M(P)`: operational steps from the empty graph. -/
def MReach (M : Model Q) (P : Program Q) (G : Graph Q) : Prop := OpLe M P Graph.empty G

/-- prop:reach-exec: the reachable graphs are the consistent executions. -/
theorem mreach_iff : MReach M P G ↔ ExecM M P G := by
  constructor
  · intro h
    exact ⟨OpLe.exec M.empty (fun e he => by simp [Graph.empty] at he) h,
      (OpLe.isPrefixOf M.empty h).2⟩
  · rintro ⟨hE, hc⟩
    exact isPrefixOf_opLe hc hE (empty_isPrefixOf G)

/-- `n` steps. -/
def StepsN (M : Model Q) (P : Program Q) : ℕ → Graph Q → Graph Q → Prop
  | 0, G, G' => G = G'
  | n + 1, G, G' => ∃ G'', StepsN M P n G G'' ∧ OpStepG M P G'' G'

/-- Operational reachability is reachability in some number of steps. -/
theorem stepsN_of_opLe (h : OpLe M P G G') : ∃ n, StepsN M P n G G' := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hs ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, _, hn, hs⟩

/-- One direction of `stepsN_iff`. -/
theorem StepsN.execM {n : ℕ} (hG : ExecM M P G) (h : StepsN M P n G G') :
    ExecM M P G' ∧ G.IsPrefixOf G' ∧ G'.events.card = G.events.card + n := by
  induction n generalizing G' with
  | zero =>
    cases h
    exact ⟨hG, (M.wf _ hG.2).isPrefixOf_refl, rfl⟩
  | succ n ih =>
    obtain ⟨G'', h'', e, src, out, hop, rfl⟩ := h
    obtain ⟨hE'', hp'', hc''⟩ := ih h''
    have hw'' := M.wf _ hE''.2
    obtain ⟨t, ht⟩ := hop.nextEv
    have hidx := Model.idx_of_nextEv ht
    have he := hw''.not_mem_of_idx_eq_cnt hidx
    refine ⟨⟨P.exec_add hE''.1 hw'' ht src out, hop.2.2⟩,
      hp''.trans (hw''.isPrefixOf_add hidx), ?_⟩
    rw [add_events, Finset.card_insert_of_notMem he, hc'']
    rfl

/-- `n` steps from a consistent execution reach exactly the consistent executions with `G` as a
prefix and `n` more events. -/
theorem stepsN_iff {n : ℕ} (hG : ExecM M P G) :
    StepsN M P n G G' ↔ ExecM M P G' ∧ G.IsPrefixOf G' ∧ G'.events.card = G.events.card + n := by
  refine ⟨StepsN.execM hG, fun ⟨hG', hp, hc⟩ => ?_⟩
  obtain ⟨k, hk⟩ := stepsN_of_opLe (isPrefixOf_opLe hG'.2 hG'.1 hp)
  have := (StepsN.execM hG hk).2.2
  have hkn : k = n := by omega
  exact hkn ▸ hk

/-- lem:prefix-steps: a prefix in `Exec_M(P)` reaches the larger graph in `|G'| - |G|` steps,
through graphs that are prefixes of `G'`. -/
theorem prefix_steps (hG : ExecM M P G) (hG' : ExecM M P G') (hp : G.IsPrefixOf G') :
    StepsN M P (G'.events.card - G.events.card) G G' ∧
    ∀ H, OpLe M P G H → OpLe M P H G' → H.IsPrefixOf G' := by
  refine ⟨(stepsN_iff hG).mpr ⟨hG', hp, ?_⟩, fun H h1 h2 => ?_⟩
  · have := Finset.card_le_card hp.events_subset
    omega
  · exact (OpLe.isPrefixOf (OpLe.isPrefixOf hG.2 h1).2 h2).1

/-- def:safety: no reachable graph is bad. -/
def Safe (M : Model Q) (P : Program Q) (Bad : Set (Graph Q)) : Prop :=
  ∀ G, MReach M P G → G ∉ Bad

/-- `Term_M(P)`: the reachable graphs without a step. -/
def Term (M : Model Q) (P : Program Q) (G : Graph Q) : Prop :=
  MReach M P G ∧ ∀ G', ¬ OpStepG M P G G'

/-- Every available event has a step. -/
theorem exists_opStepG_of_mem_availM (hc : M.cons G) {e : Ev Q} (he : e ∈ M.availM P G) :
    ∃ G', OpStepG M P G G' := by
  obtain ⟨t, -, ht, hu⟩ := M.mem_availM_iff'.mp he
  have hidx := Model.idx_of_nextEv ht
  have hlab : P.step t (G.trace t) = some e.lab := by
    unfold Program.nextEv at ht
    obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp ht
    exact hl
  rcases hu with hB | ⟨s, hs, hcs⟩
  · by_cases hR : e.IsRecv
    · have hNB : e.IsRecvNB := (Lab.IsRecv.recvB_or_recvNB hR).resolve_left hB
      exact ⟨_, e, _, _, ⟨he, Or.inl ⟨hR, rfl, Or.inl rfl⟩, M.ext_bot G e hc hidx hNB⟩, rfl⟩
    · by_cases hN : e.IsND
      · obtain ⟨S, hS⟩ := (Lab.isND_iff e.lab).mp hN
        obtain ⟨v, hv⟩ := P.nd_ne t _ S (hS ▸ hlab)
        have hv' : v ∈ e.ndSet := by simpa [Ev.ndSet, hS, Lab.ndSet] using hv
        exact ⟨_, e, _, _, ⟨he, Or.inr (Or.inl ⟨hN, rfl, v, hv', rfl⟩),
          M.ext_nd G e v hc hidx hN hv'⟩, rfl⟩
      · exact ⟨_, e, _, _, ⟨he, Or.inr (Or.inr ⟨hR, hN, rfl, rfl⟩),
          M.ext_plain G e hc hidx hR hN⟩, rfl⟩
  · have hR : e.IsRecv :=
      ((M.wf _ hcs).rf_match e s (by simp [Graph.addRecv])).isRecv
    exact ⟨_, e, _, _, ⟨he, Or.inl ⟨hR, rfl, Or.inr ⟨s, hs, rfl⟩⟩, hcs⟩, rfl⟩

/-- `Term` is the port's repaired `⟦P⟧` (`Model.Sem`): ass:must (c), part of the R-claim. -/
theorem term_iff_sem : Term M P G ↔ M.Sem P G := by
  constructor
  · rintro ⟨hr, hn⟩
    obtain ⟨hE, hc⟩ := mreach_iff.mp hr
    refine ⟨M.wf _ hc, hE, hc, ?_⟩
    unfold Model.FullM
    by_contra hne
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨G', hG'⟩ := exists_opStepG_of_mem_availM hc he
    exact hn G' hG'
  · rintro ⟨-, hE, hc, hf⟩
    refine ⟨mreach_iff.mpr ⟨hE, hc⟩, fun G' ⟨e, src, out, hop, _⟩ => ?_⟩
    have := hop.1
    unfold Model.FullM at hf
    rw [hf] at this
    exact List.not_mem_nil this

/-- Thread `t` is stuck in `G` (lem:terminal): its next label is a blocking receive that no
unread send matches. -/
def Stuck (P : Program Q) (G : Graph Q) (t : Tid) : Prop :=
  ∃ l, P.step t (G.trace t) = some l ∧ l.IsRecvB ∧ ∀ s ∈ G.US, ¬ s.Matches ⟨t, G.cnt t, l⟩

/-- lem:terminal (1), for every `Must.Model`: a consistent execution is terminal iff every
thread of the program with a next label is stuck. -/
theorem term_iff_stuck (hG : ExecM M P G) :
    Term M P G ↔ ∀ t ∈ P.threads, (P.step t (G.trace t)).isSome → Stuck P G t := by
  rw [term_iff_sem]
  have hS : M.Sem P G ↔ M.availM P G = [] :=
    ⟨fun h => h.2.2.2, fun h => ⟨M.wf _ hG.2, hG.1, hG.2, h⟩⟩
  rw [hS, List.eq_nil_iff_forall_not_mem]
  constructor
  · intro h t ht hs
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp hs
    have hn : P.nextEv G t = some ⟨t, G.cnt t, l⟩ := by simp [Program.nextEv, hl]
    have hna := h ⟨t, G.cnt t, l⟩
    rw [M.mem_availM_iff hG.2] at hna
    push Not at hna
    obtain ⟨hB, hU⟩ := hna t ht hn
    exact ⟨l, hl, hB, hU⟩
  · intro h e he
    obtain ⟨t, ht, hn, hu⟩ := (M.mem_availM_iff hG.2).mp he
    unfold Program.nextEv at hn
    obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp hn
    obtain ⟨l', hl', hB, hU⟩ := h t ht (by simp [hl])
    rw [hl] at hl'
    cases hl'
    rcases hu with hu | ⟨s, hs, hm⟩
    · exact hu hB
    · exact hU s hs hm

end Ind

end Must
