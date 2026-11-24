import Mazurkiewicz.Must.Optimal

/-!
# Optimality, part 2: Lemma A.18 (milestone M8)

Paper: Appendix A.9, Lemma A.18 (p. 34): "Let `S` be a production sequence that reaches a
consistent execution `G_t`, and `G` an execution in `S` such that `G ⊑ G_t`. Then there is no
algorithm step in `S` after `G` that revisits an event of `G`." Plan: rows A.18 and M8
(`no_revisit_of_prefix`); the fate table adds the case `rf r = ⊥`.

Statement proved (`no_revisit_of_prefix`): for a configuration `c` with the invariant and a
sequence of algorithmic steps `c → ⋯ → d` such that every event of `c` has in `d` its source in
`c` (in particular when `c.G ⊑ d.G`), every configuration of the sequence keeps `c`
**frozen**: `c`'s insertion order is a prefix of its order, and every event of `c` has its
source and outcome of `c` (`Frozen`). A revisit of an event of `c` would change its source, and
a deletion of an event of `c` would remove it from the order prefix, so neither happens. The
hypothesis is weaker than the printed `G ⊑ G_t` (no closure, no consistency) and the end need
not be a full execution; for every model and every tie-break with Q9.

Proof (not the printed one, which picks "the `<`-earliest revisited event"): induction on the
length `k` of the frozen prefix. If the first `k` events of `c` stay frozen along the sequence,
the `(k+1)`-th event `x` can change only by a revisit of `x` itself (a deletion of `x` would need
a revisit of an earlier event, which is frozen). After such a revisit (`PhaseB`) `x` reads a
send that was fresh when it revisited `x`, and the old source `s₀` of `x` stays in every later
graph: it is frozen if it precedes `x`; otherwise the revisit kept it (line 21: `x` reads it and
is in its `Previous`), so `s₀` is causally before the new send, which `x` reads backward, so
`s₀` is protected (`Config.Prot`, part 1) and is never deleted. Hence `x` never reads `s₀` again
(a revisit needs a fresh send), and the end contradicts the hypothesis. The case `rf x = ⊥`
needs no extra argument (a revisit installs a send).
-/

namespace Must

open Graph Relation Config

variable {Q : Type} [DecidableEq Q] [Membership Val Q]
variable {M : Model Q} {P : Program Q} {tie : Tie Q}

/-- `d` keeps the first `k` events of `c` frozen: they form a prefix of `d`'s insertion order
and have in `d` their sources and outcomes of `c`. -/
def Frozen (k : ℕ) (c d : Config Q) : Prop :=
  c.order.take k <+: d.order ∧
    ∀ y ∈ c.order.take k, d.G.rf y = c.G.rf y ∧ d.G.nd y = c.G.nd y

omit [DecidableEq Q] [Membership Val Q] in
theorem frozen_refl (k : ℕ) (c : Config Q) : Frozen k c c :=
  ⟨List.take_prefix _ _, fun _ _ => ⟨rfl, rfl⟩⟩

omit [Membership Val Q] in
/-- With a frozen prefix of length `k`, the events before position `k` are exactly those of the
prefix. -/
theorem pos_lt_iff_mem_take {c d : Config Q} {k : ℕ} (hk : k ≤ c.order.length)
    (hp : c.order.take k <+: d.order) {y : Ev Q} (hy : y ∈ d.order) :
    d.pos y < k ↔ y ∈ c.order.take k := by
  have hlen : (c.order.take k).length = k := List.length_take_of_le hk
  have ht : d.order.take k = c.order.take k := by
    have := List.prefix_iff_eq_take.mp hp
    rw [hlen] at this
    exact this.symm
  rw [← ht]
  exact (List.mem_take_iff_idxOf_lt hy).symm

omit [Membership Val Q] in
/-- A prefix of the order survives an addition. -/
theorem prefix_add {c : Config Q} {pre : List (Ev Q)} (h : pre <+: c.order) {e : Ev Q}
    {src : Option (Src Q)} {out : Option Val} : pre <+: (c.add e src out).order :=
  h.trans (List.prefix_append _ _)

omit [Membership Val Q] in
/-- A prefix of the order none of whose events is deleted survives a revisit. -/
theorem prefix_revisitCfg {H : Config Q} {r s : Ev Q} {pre : List (Ev Q)} (h : pre <+: H.order)
    (hk : ∀ y ∈ pre, y ∉ H.del r s ∧ y ≠ s) : pre <+: (H.revisitCfg r s).order := by
  obtain ⟨rest, hrest⟩ := h
  refine ⟨rest.filter (fun d => decide (d ∉ H.del r s ∧ d ≠ s)) ++ [s], ?_⟩
  rw [revisitCfg_order, ← hrest, List.filter_append, List.append_assoc]
  congr 1
  refine (List.filter_eq_self.mpr fun y hy => ?_).symm
  simp [hk y hy]

omit [Membership Val Q] in
/-- Outcomes of kept events are unchanged by a revisit. -/
theorem revisitCfg_nd {H : Config Q} {r s z : Ev Q} (hz : z ∈ H.G.events)
    (hzd : z ∉ H.del r s) : (H.revisitCfg r s).G.nd z = H.G.nd z := by
  simp [revisitCfg, Graph.revisit, hz, hzd]

/-! ### One step -/

section Step

variable {c : Config Q} {k : ℕ} (hk : k < c.order.length)

/-- The `(k+1)`-th event of `c` has been revisited and its old source is kept for good. -/
def PhaseB (c : Config Q) (k : ℕ) (hk : k < c.order.length) (a : Config Q) : Prop :=
  c.order.take (k + 1) <+: a.order ∧
    (∃ t, a.G.rf (c.order[k]) = some (.snd t) ∧ c.G.rf (c.order[k]) ≠ some (.snd t)) ∧
    ∀ s₀, c.G.rf (c.order[k]) = some (.snd s₀) →
      s₀ ∈ a.G.events ∧ (s₀ ∈ c.order.take k ∨ a.Prot s₀)

omit [DecidableEq Q] [Membership Val Q] in
theorem take_succ_eq : c.order.take (k + 1) = c.order.take k ++ [c.order[k]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  rfl

omit [DecidableEq Q] [Membership Val Q] in
theorem mem_take_succ {y : Ev Q} :
    y ∈ c.order.take (k + 1) ↔ y ∈ c.order.take k ∨ y = c.order[k] := by
  rw [take_succ_eq hk, List.mem_append, List.mem_singleton]

/-- The facts about a revisit step `a → (a + e).revisit(r', e)` between configurations that keep
the first `k` events of `c` frozen, when the `(k+1)`-th event is the next one in `a`'s order:
`r'` is not among the first `k` events, the first `k+1` events stay a prefix, and the source of
the `(k+1)`-th event is unchanged unless it is `r'`. -/
theorem revisit_facts {a : Config Q} {e r' : Ev Q} (ha : a.Inv M P)
    (hn : M.nextP P a.G = some e) (hS : e.IsSend) (hg : RevGuard tie (a.add e none none) r' e)
    (hfa : Frozen k c a) (hfb : Frozen k c ((a.add e none none).revisitCfg r' e))
    (hpre : c.order.take (k + 1) <+: a.order) :
    e ∉ a.G.events ∧ r' ∉ c.order.take k ∧
    c.order.take (k + 1) <+: ((a.add e none none).revisitCfg r' e).order ∧
    c.order[k] ∉ (a.add e none none).del r' e ∧
    ((a.add e none none).revisitCfg r' e).G.rf (c.order[k]) =
      if c.order[k] = r' then some (.snd e) else a.G.rf (c.order[k]) := by
  set H := a.add e none none with hH
  obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hn
  have heA := ha.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv ht)
  have hHi : H.Inv M P := ha.addSend ht hS
  have hrd : r' ∉ H.del r' e := fun h => lt_irrefl _ (mem_del.mp h).2.2.1
  have hr'k : r' ∉ c.order.take k := by
    intro hr
    have h1 := (hfb.2 r' hr).1
    rw [revisitCfg_rf hg.mem hrd] at h1
    simp only [↓reduceIte] at h1
    rw [← (hfa.2 r' hr).1] at h1
    exact heA (ha.wf.rf_mem _ _ h1.symm)
  have hlen : k + 1 ≤ c.order.length := hk
  have hpreH : c.order.take (k + 1) <+: H.order := prefix_add hpre
  have hpreHk : c.order.take k <+: H.order :=
    ((List.prefix_take_le_iff hk).mpr (Nat.le_succ k)).trans hpreH
  have hr'pos : k ≤ H.pos r' := by
    by_contra hlt
    exact hr'k ((pos_lt_iff_mem_take hk.le hpreHk ((hHi.mem r').mpr hg.mem)).mp (by omega))
  have hkeep : ∀ y ∈ c.order.take (k + 1), y ∉ H.del r' e ∧ y ≠ e := by
    intro y hy
    have hyo : y ∈ a.order := hpre.subset hy
    have hye : y ≠ e := fun h => heA (h ▸ (ha.mem y).mp hyo)
    refine ⟨fun hd => ?_, hye⟩
    have hyH : y ∈ H.order := List.mem_append_left _ hyo
    have h1 := (pos_lt_iff_mem_take hlen hpreH hyH).mpr hy
    have h2 := (mem_del.mp hd).2.2.1
    omega
  have hxk : c.order[k] ∈ c.order.take (k + 1) := (mem_take_succ hk).mpr (Or.inr rfl)
  have hxa : c.order[k] ∈ a.G.events := (ha.mem _).mp (hpre.subset hxk)
  have hxe : c.order[k] ≠ e := fun h => heA (h ▸ hxa)
  refine ⟨heA, hr'k, prefix_revisitCfg hpreH hkeep, (hkeep _ hxk).1, ?_⟩
  rw [revisitCfg_rf (Finset.mem_insert_of_mem hxa) (hkeep _ hxk).1]
  split_ifs with h
  · rfl
  · change Function.update a.G.rf e none (c.order[k]) = _
    rw [Function.update_of_ne hxe]


/-- One algorithmic step between configurations that keep the first `k` events of `c` frozen:
from `Frozen (k+1)` the successor is `Frozen (k+1)` or enters `PhaseB` (the step revisited the
`(k+1)`-th event); `PhaseB` is kept. -/
theorem step_phase (hT : TieQ9 M tie) {a b : Config Q} (h : StepM M tie P a b) (ha : a.Inv M P)
    (hfa : Frozen k c a) (hfb : Frozen k c b) :
    (Frozen (k + 1) c a → Frozen (k + 1) c b ∨ PhaseB c k hk b) ∧
    (PhaseB c k hk a → PhaseB c k hk b) := by
  have hb := h.inv ha
  have hxk : c.order[k] ∈ c.order.take (k + 1) := (mem_take_succ hk).mpr (Or.inr rfl)
  cases h with
  | nr hnr =>
    rename_i e src out
    obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hnr.1
    have heA := ha.wf.not_mem_of_idx_eq_cnt (Model.idx_of_nextEv ht)
    have hne : ∀ y ∈ a.order, y ≠ e := fun y hy h' => heA (h' ▸ (ha.mem y).mp hy)
    constructor
    · intro hA
      refine Or.inl ⟨prefix_add hA.1, fun y hy => ?_⟩
      have hye := hne y (hA.1.subset hy)
      simp only [Config.add, add_rf, add_nd, Function.update_of_ne hye]
      exact hA.2 y hy
    · rintro ⟨hpre, ⟨t', ht1, ht2⟩, hs₀⟩
      have hxe := hne _ (hpre.subset hxk)
      refine ⟨prefix_add hpre, ⟨t', ?_, ht2⟩, fun s₀ hs => ?_⟩
      · simp only [Config.add, add_rf, Function.update_of_ne hxe]
        exact ht1
      · obtain ⟨h1, h2⟩ := hs₀ s₀ hs
        refine ⟨Finset.mem_insert_of_mem h1, h2.imp id fun hp => hp.add ha heA⟩
  | revisit hn hS hg hcons =>
    rename_i e r'
    set H := a.add e none none with hHdef
    obtain ⟨t, ht⟩ := exists_nextEv_of_nextP hn
    have hHi : H.Inv M P := ha.addSend ht hS
    constructor
    · intro hA
      obtain ⟨heA, -, hpreb, hxd, hrfx⟩ := revisit_facts hk ha hn hS hg hfa hfb hA.1
      by_cases hxr : c.order[k] = r'
      · -- the `(k+1)`-th event is revisited: `PhaseB`
        right
        rw [ite_eq_left hxr] at hrfx
        refine ⟨hpreb, ⟨e, hrfx, fun h' => heA ?_⟩, fun s₀ hs => ?_⟩
        · rw [← (hA.2 _ hxk).1] at h'
          exact ha.wf.rf_mem _ _ h'
        · have hxs₀ : a.G.rf (c.order[k]) = some (.snd s₀) := (hA.2 _ hxk).1.trans hs
          have hs₀a : s₀ ∈ a.G.events := ha.wf.rf_mem _ _ hxs₀
          have hs₀H : s₀ ∈ H.G.events := Finset.mem_insert_of_mem hs₀a
          have hs₀e : s₀ ≠ e := fun h' => heA (h' ▸ hs₀a)
          by_cases hs₀k : s₀ ∈ c.order.take k
          · exact ⟨(hb.mem _).mp (hfb.1.subset hs₀k), Or.inl hs₀k⟩
          · -- `s₀` comes after `x`; it is kept, causally before `e`, hence protected
            have hxR : (c.order[k]).IsRecv := (ha.wf.rf_some hxs₀).2
            have hs₀S : s₀.IsSend := (ha.wf.rf_match _ _ hxs₀).isSend
            have hs₀x : s₀ ≠ c.order[k] := fun h' => Lab.IsSend.not_isRecv hs₀S (h' ▸ hxR)
            have hs₀k1 : s₀ ∉ c.order.take (k + 1) := fun h' =>
              ((mem_take_succ hk).mp h').elim hs₀k hs₀x
            have hpreH : c.order.take (k + 1) <+: H.order := prefix_add hA.1
            have hxpos : H.pos (c.order[k]) < k + 1 :=
              (pos_lt_iff_mem_take hk hpreH (List.mem_append_left _ (hA.1.subset hxk))).mpr hxk
            have hs₀pos : ¬ H.pos s₀ < k + 1 := fun h' => hs₀k1
              ((pos_lt_iff_mem_take hk hpreH ((hHi.mem s₀).mpr hs₀H)).mp h')
            have hxa : c.order[k] ∈ a.G.events := (ha.mem _).mp (hA.1.subset hxk)
            have hHx : H.G.rf (c.order[k]) = some (.snd s₀) := by
              change Function.update a.G.rf e none (c.order[k]) = _
              rw [Function.update_of_ne (fun (h' : c.order[k] = e) => heA (h' ▸ hxa))]
              exact hxs₀
            have hs₀d : s₀ ∉ H.del r' e := by
              intro hd
              have hc := RevCond.of_send (hg.cond s₀ (Finset.mem_insert_of_mem hd)) hs₀S
              refine hc (c.order[k]) (Finset.mem_filter.mpr ⟨?_, Or.inl (by omega)⟩) hxR hHx
              exact Finset.mem_insert_of_mem ((ha.mem _).mp (hA.1.subset hxk))
            have hporf : H.G.porf s₀ e := by
              by_contra hn'
              refine hs₀d (mem_del.mpr ⟨hs₀H, hs₀e, ?_, hn'⟩)
              rw [← hxr]
              omega
            have he : e ∈ H.G.events := Finset.mem_insert_self _ _
            have hre : r' ≠ e := fun h' => Lab.IsSend.not_isRecv hS (h' ▸ hg.recv)
            refine ⟨mem_revisitCfg_events.mpr ⟨hs₀H, hs₀d⟩, Or.inr ⟨e, r',
              (porf_revisit_to_s hHi hg he hporf).to_reflTransGen,
              revisitCfg_bwRead hHi hg hre⟩⟩
      · -- another receive is revisited: `x` keeps its source
        left
        rw [ite_eq_right hxr] at hrfx
        refine ⟨hpreb, fun y hy => ?_⟩
        rcases (mem_take_succ hk).mp hy with hy | rfl
        · exact hfb.2 y hy
        · refine ⟨hrfx.trans (hA.2 _ hxk).1, ?_⟩
          have hxa := (ha.mem _).mp (hA.1.subset hxk)
          rw [revisitCfg_nd (Finset.mem_insert_of_mem hxa) hxd]
          have hxe : c.order[k] ≠ e := fun h' => heA (h' ▸ hxa)
          change Function.update a.G.nd e none (c.order[k]) = _
          rw [Function.update_of_ne hxe]
          exact (hA.2 _ hxk).2
    · rintro ⟨hpre, ⟨t', ht1, ht2⟩, hs₀⟩
      obtain ⟨heA, -, hpreb, -, hrfx⟩ := revisit_facts hk ha hn hS hg hfa hfb hpre
      refine ⟨hpreb, ?_, fun s₀ hs => ?_⟩
      · split_ifs at hrfx with hxr
        · refine ⟨e, hrfx, fun h' => heA (hs₀ e h').1⟩
        · exact ⟨t', hrfx.trans ht1, ht2⟩
      · obtain ⟨h1, h2⟩ := hs₀ s₀ hs
        rcases h2 with h2 | h2
        · exact ⟨(hb.mem _).mp (hfb.1.subset h2), Or.inl h2⟩
        · obtain ⟨h3, h4⟩ := (StepM.revisit hn hS hg hcons).prot hT ha h2
          exact ⟨h3, Or.inr h4⟩

omit [Membership Val Q] in
/-- `Frozen (k+1)` and `PhaseB` exclude each other. -/
theorem not_phaseB_of_frozen {a : Config Q} (hA : Frozen (k + 1) c a) : ¬ PhaseB c k hk a := by
  rintro ⟨-, ⟨t, ht1, ht2⟩, -⟩
  have hxk : c.order[k] ∈ c.order.take (k + 1) := (mem_take_succ hk).mpr (Or.inr rfl)
  exact ht2 ((hA.2 _ hxk).1.symm.trans ht1)

/-- Along a sequence of algorithmic steps whose configurations keep the first `k` events of `c`
frozen: either every configuration keeps the first `k+1` frozen, or the last one is in
`PhaseB`. -/
theorem seq_phase (hT : TieQ9 M tie) {a d : Config Q} {S : List (Config Q)}
    (h : StepSeq M tie P a S d) (ha : a.Inv M P) (hfa : Frozen k c a)
    (hfS : ∀ d' ∈ S, Frozen k c d') (hph : Frozen (k + 1) c a ∨ PhaseB c k hk a) :
    (Frozen (k + 1) c a ∧ ∀ d' ∈ S, Frozen (k + 1) c d') ∨ PhaseB c k hk d := by
  induction h with
  | nil => exact hph.imp (fun h => ⟨h, fun _ h' => absurd h' List.not_mem_nil⟩) id
  | @cons a' b d' S' hs _ ih =>
    have hfb : Frozen k c b := hfS b (List.mem_cons_self ..)
    obtain ⟨hstA, hstB⟩ := step_phase hk hT hs ha hfa hfb
    have hphb : Frozen (k + 1) c b ∨ PhaseB c k hk b :=
      hph.elim hstA (fun hB => Or.inr (hstB hB))
    rcases ih (hs.inv ha) hfb (fun d'' hd'' => hfS d'' (List.mem_cons_of_mem _ hd'')) hphb with
      ⟨hb1, hb2⟩ | hd
    · rcases hph with hA | hB
      · refine Or.inl ⟨hA, fun d'' hd'' => ?_⟩
        rcases List.mem_cons.mp hd'' with rfl | hd''
        · exact hb1
        · exact hb2 d'' hd''
      · exact absurd (hstB hB) (not_phaseB_of_frozen hk hb1)
    · exact Or.inr hd

end Step

/-- **Lemma A.18** (`no_revisit_of_prefix`), repaired. Let `c` be a configuration with the
invariant (every reachable one) and `c → ⋯ → d` a sequence of algorithmic steps such that every
event of `c` has in `d` its source in `c` (true when `c.G ⊑ d.G`). Then every configuration of
the sequence keeps `c` frozen: no step revisits an event of `c` (its source would change), and
no step deletes one. For every model and every tie-break with Q9; `d` need not be full. -/
theorem no_revisit_of_prefix (hT : TieQ9 M tie) {c d : Config Q} {S : List (Config Q)}
    (hc : c.Inv M P) (h : StepSeq M tie P c S d)
    (hfin : ∀ x ∈ c.G.events, d.G.rf x = c.G.rf x) :
    ∀ d' ∈ S, Frozen c.order.length c d' := by
  suffices H : ∀ k ≤ c.order.length, ∀ d' ∈ S, Frozen k c d' from H _ le_rfl
  intro k
  induction k with
  | zero => exact fun _ d' _ => ⟨by simp, fun y hy => by simp at hy⟩
  | succ k ih =>
    intro hk1
    have hk : k < c.order.length := hk1
    have hfS := ih hk.le
    rcases seq_phase hk hT h hc (frozen_refl k c) hfS (Or.inl (frozen_refl (k + 1) c)) with
      ⟨-, h2⟩ | hB
    · exact h2
    · exfalso
      obtain ⟨-, ⟨t, ht1, ht2⟩, -⟩ := hB
      have hxc : c.order[k] ∈ c.G.events := (hc.mem _).mp (List.getElem_mem hk)
      exact ht2 ((hfin _ hxc).symm.trans ht1)

/-- A.18 in the printed form: no step of the sequence revisits an event of `c` or deletes one:
`c`'s order is a prefix of every later order, and the events of `c` keep their sources. -/
theorem no_revisit_of_prefix' (hT : TieQ9 M tie) {c d : Config Q} {S : List (Config Q)}
    (hc : c.Inv M P) (h : StepSeq M tie P c S d)
    (hfin : ∀ x ∈ c.G.events, d.G.rf x = c.G.rf x) :
    ∀ d' ∈ S, c.order <+: d'.order ∧ ∀ x ∈ c.G.events, d'.G.rf x = c.G.rf x ∧
      d'.G.nd x = c.G.nd x := by
  intro d' hd'
  obtain ⟨h1, h2⟩ := no_revisit_of_prefix hT hc h hfin d' hd'
  rw [List.take_length] at h1 h2
  exact ⟨h1, fun x hx => h2 x ((hc.mem x).mpr hx)⟩

end Must

#print axioms Must.no_revisit_of_prefix
#print axioms Must.no_revisit_of_prefix'
