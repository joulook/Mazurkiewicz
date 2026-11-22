import Mazurkiewicz.Condpor.Rmw.Inv

/-!
# Read-modify-write accesses: the completion and the backward step

`MaxCompletion` and `Prev` (Algorithm 5 of TruSt) are those of `Prev.lean`.
What changes is the consistency of the completion (Proposition A.23 (S3)):
with atomicity, "the completion of a consistent graph is consistent" is false
(a pending read whose source is not the last write: its mate, placed last,
breaks atomicity).

* `Towards P e G`: every prospective pair of `G` has the write `e`, or its
  read reads the last write of the location and its write is the next event.
  The completion towards `e` keeps it (`ComplStep.towards`), and under it
  every round of the completion keeps consistency (`Rmw.complChain`).
-/

namespace Condpor

open Program

variable {P : XProgram} {M : Model} {S : Solver} {τ : TieBreak S}
  {p : Finset Lit → SExpr → Bool}

/-- An available exclusive write has a mate: the last event of its thread. -/
theorem XProgram.exists_mate {G : Graph} (hG : G.Wf) (hE : P.toProgram.Exec G) {a : TEv}
    (ha : a ∈ P.toProgram.avail G) (hw : a.IsWrite) (hx : P.ex a.tid (G.trace a.tid) = true) :
    ∃ r, P.Mate G r a := by
  obtain ⟨-, hidx, hs⟩ := mem_avail_iff.mp ha
  obtain ⟨v, hv⟩ := hw.exists_act
  rw [hv] at hs
  obtain ⟨u₀, b, hu, hx0, hs0⟩ := P.ex_write a.tid _ a.loc v hx hs
  have hlen : G.cnt a.tid = u₀.length + 1 := by
    rw [← G.trace_length, hu]
    simp
  obtain ⟨r, hr, hrt, hri⟩ := (hG.exists_idx_iff a.tid u₀.length).mpr (by omega)
  have htb : G.traceBefore a.tid u₀.length = u₀ := by
    rw [G.traceBefore_eq_take _ (by omega), hu]
    simp
  have hract : r.act = .read a.loc := by
    have := hE.2 r hr
    rw [hrt, hri, htb, hs0] at this
    exact (Option.some.inj this).symm
  refine ⟨r, hr, by simp [TEv.IsRead, hract, Act.IsRead], ?_, ha, hrt.symm, by omega, hw, hx⟩
  unfold XProgram.IsEx
  rw [hrt, hri, htb]
  exact hx0

/-- The maximal extension by an available event with the outcomes of a
tie-break keeps `M`-consistency and the invariant of the tie-break, if the read
of an exclusive write reads the last write of the location. -/
theorem ExtensibleX.sym_cons_addMax (hM : ExtensibleX P M) (τ : TieBreak S) {K : Finset Lit}
    {G : Graph} (hG : G.Wf) (hE : P.toProgram.Exec G) (hc : M.cons G) (hinv : τ.inv K G.F)
    {a : TEv} (ha : a ∈ P.toProgram.avail G)
    (hx : ∀ r, P.Mate G r a → G.rf r = some (G.maxWrite a.loc)) :
    M.cons (G.addMax (τ.pref K) a) ∧ τ.inv K (G.addMax (τ.pref K) a).F := by
  have hidx := idx_eq_of_mem_avail ha
  constructor
  · rcases a.act.isRead_or_isWrite_or_isLocal with h | h | h
    · rw [Graph.addMax_read (TEv.IsRead.exists_act h)]
      exact hM.ext_read G a _ hG hE hc ha (TEv.IsRead.exists_act h)
    · rw [Graph.addMax_write h]
      by_cases hex : P.ex a.tid (G.trace a.tid) = true
      · obtain ⟨r, hr⟩ := XProgram.exists_mate hG hE ha h hex
        exact hM.ext_wex G r a hG hE hc hr (hx r hr)
      · exact hM.ext_write G a hG hE hc ha h (by simpa using hex)
    · obtain ⟨o, ho, heq⟩ := Graph.addMax_local (G := G) (p := τ.pref K) h
      rw [heq]
      exact hM.ext_loc G a o hG hE hc ha h ho
  · rw [Graph.F_addMax hG hidx]
    cases h : a.act with
    | cons φ => exact τ.inv_step φ hinv
    | read x => exact hinv
    | write x v => exact hinv
    | gen s => exact hinv
    | block => exact hinv
    | error => exact hinv

/-- The available events of the other threads after a maximal extension were
available before. -/
theorem Program.avail_of_addMax_ne {Q : Program} {G : Graph} (hG : G.Wf) {a y : TEv}
    (hidx : a.idx = G.cnt a.tid) (hy : y ∈ Q.avail (G.addMax p a)) (hne : y.tid ≠ a.tid) :
    y ∈ Q.avail G := by
  obtain ⟨ht, hi, hs⟩ := mem_avail_iff.mp hy
  have htr := Graph.trace_addMax_of_ne (p := p) hG hidx hne
  refine mem_avail_iff.mpr ⟨ht, ?_, ?_⟩
  · rw [← Graph.trace_length, ← htr, Graph.trace_length]
    exact hi
  · rw [← htr]
    exact hs

/-- The invariant of the completion towards `e`: every prospective pair has
the write `e`, or its read reads the last write of the location and its write
is the next event. -/
def Towards (P : XProgram) (e : TEv) (G : Graph) : Prop :=
  ∀ r m, P.Mate G r m → m = e ∨ (G.rf r = some (G.maxWrite m.loc) ∧ P.toProgram.IsNext G m)

/-- A round of the completion keeps the invariant. -/
theorem ComplStep.towards {e : TEv} {G G' : Graph} (hG : G.Wf) (hE : P.toProgram.Exec G)
    (h : ComplStep P.toProgram p e G G') (hK : Towards P e G) : Towards P e G' := by
  obtain ⟨a, hnext, hae, rfl⟩ := h
  have hidx := idx_eq_of_mem_avail hnext.1
  have hG' : (G.addMax p a).Wf := hG.addMax hidx
  have hE' : P.toProgram.Exec (G.addMax p a) := hE.addMax hG hnext.1 p
  have haG' : a ∈ (G.addMax p a).events := by
    rw [Graph.addMax_events]
    exact Finset.mem_insert_self _ _
  intro r' m' hm'
  have hm'' := hm'
  obtain ⟨hr'G, hr'R, -, hma, hmt, hmi, -, -⟩ := hm'
  by_cases hra : r' = a
  · subst hra
    right
    have hact := hr'R.exists_act
    have hloc : r'.loc = m'.loc := by
      have := hm''.read_act hE'
      rw [hact] at this
      injection this
    refine ⟨?_, hma, fun y hy hne => ?_⟩
    · rw [Graph.addMax_read hact, ← hloc]
      simp [Graph.addRead_rf, Graph.maxWrite]
    · have htne : y.tid ≠ r'.tid := fun h' => hne (avail_tid_inj hy hma (h'.trans hmt.symm))
      have hyG := Program.avail_of_addMax_ne hG hidx hy htne
      exact hm''.next_lt hy hne (hnext.2 y hyG (fun h' => htne (congrArg TEv.tid h')))
  · have hr'G0 : r' ∈ G.events := by
      rw [Graph.addMax_events] at hr'G
      exact (Finset.mem_insert.mp hr'G).resolve_left hra
    have htne : r'.tid ≠ a.tid := by
      intro h'
      have h1 := hG'.idx_lt_cnt haG'
      have h2 := idx_eq_of_mem_avail hma
      have h3 := hG.idx_lt_cnt hr'G0
      rw [← h', ← hmt, ← h2, hmi] at h1
      rw [h', ← hidx] at h3
      omega
    have hmG := Program.avail_of_addMax_ne hG hidx hma (fun h' => htne (hmt.symm.trans h'))
    have hMate := XProgram.Mate.of_trace_eq hG hG' hm'' hr'G0 hmG
      (Graph.trace_addMax_of_ne hG hidx htne)
    rcases hK r' m' hMate with h | ⟨-, h⟩
    · exact Or.inl h
    · exact absurd (hmt.symm.trans (congrArg TEv.tid (Program.isNext_unique h hnext))) htne

/-- Under the invariant, the rounds of the completion keep consistency, the
invariant of the tie-break and the invariant `Towards`. -/
theorem Rmw.complChain (hM : ExtensibleX P M) {K : Finset Lit} {e : TEv} {G G' : Graph}
    (hG : G.Wf) (hE : P.toProgram.Exec G) (he : e ∈ P.toProgram.avail G)
    (hc : M.cons G ∧ τ.inv K G.F) (hK : Towards P e G)
    (h : Relation.ReflTransGen (ComplStep P.toProgram (τ.pref K) e) G G') :
    (M.cons G' ∧ τ.inv K G'.F) ∧ Towards P e G' := by
  induction h with
  | refl => exact ⟨hc, hK⟩
  | tail hch hs ih =>
    obtain ⟨hW, hE1, -, -⟩ := ComplStep.chain hG hE he hch
    refine ⟨?_, hs.towards hW hE1 ih.2⟩
    obtain ⟨a, hnext, hae, rfl⟩ := hs
    exact hM.sym_cons_addMax τ hW hE1 ih.1.1 ih.1.2 hnext.1
      (fun r hr => ((ih.2 r a hr).resolve_left hae).1)

/-! ### Prospective pairs of a prefix -/

/-- The last event of a thread, if it is a read, has no causal successor. -/
theorem Graph.Wf.not_porf_of_last_read {G : Graph} (hG : G.Wf) {r : TEv} (hr : r.IsRead)
    (hlast : G.cnt r.tid = r.idx + 1) (b : Ev) : ¬ G.porf (.th r) b := by
  intro h
  obtain ⟨z, hz⟩ := Maz.exists_first_of_transGen h
  rcases hz with hpo | ⟨e, -, -, hrf⟩
  · cases z with
    | init => exact absurd hpo (by simp [Graph.po])
    | th z' =>
      obtain ⟨-, hz'm, htz, hiz⟩ := hpo
      have := hG.idx_lt_cnt hz'm
      rw [← htz, hlast] at this
      omega
  · exact hG.not_isRead_of_rf hrf hr

/-- A prospective pair of a prefix of an execution `X` is a prospective pair of
`X`, or its write is an event of `X` that is not in the prefix. -/
theorem XProgram.Mate.of_restrict {X : Graph} (hX : X.Wf) (hE : P.toProgram.Exec X)
    {s : Finset TEv} (hcl : Maz.PrefixClosed X.porfStep (Graph.evSet (X.events ∩ s)))
    {r m : TEv} (hm : P.Mate (X.restrict s) r m) :
    P.Mate X r m ∨ (m ∈ X.events ∧ m ∉ s) := by
  have hZ : (X.restrict s).Wf := hX.restrict hcl
  have hm' := hm
  obtain ⟨hrZ, -, -, hma, hmt, hmi, -, -⟩ := hm
  obtain ⟨hrX, hrs⟩ := Finset.mem_inter.mp hrZ
  obtain ⟨hmth, hmidx, hmstep⟩ := mem_avail_iff.mp hma
  -- the events of the thread up to `r` are kept, with their sources
  have hkeep : ∀ q ∈ X.events, q.tid = r.tid → q.idx < r.idx + 1 → q ∈ s := by
    intro q hq hqt hqi
    by_cases hqr : q = r
    · exact hqr ▸ hrs
    · have hne : q.idx ≠ r.idx := fun h' => hqr (hX.idx_inj q hq r hrX hqt h')
      have hpo : X.po (.th q) (.th r) := ⟨hq, hrX, hqt, by omega⟩
      exact (Finset.mem_inter.mp (hcl (Or.inl hpo) hrZ)).2
  have hsrc : ∀ q ∈ X.events, q ∈ s → ∀ w, X.rf q = some w → w ∈ Graph.evSet s := by
    intro q hq hqs w hw
    have hrf : X.rfRel w (.th q) := ⟨q, rfl, hq, hw⟩
    have := hcl (Or.inr hrf) (show Ev.th q ∈ Graph.evSet (X.events ∩ s) from
      Finset.mem_inter.mpr ⟨hq, hqs⟩)
    cases w with
    | init => trivial
    | th w' => exact (Finset.mem_inter.mp this).2
  by_cases hall : ∀ z ∈ X.events, z.tid = r.tid → z ∈ s
  · left
    have htr : (X.restrict s).trace r.tid = X.trace r.tid :=
      Graph.trace_restrict_of_thread hX hall (fun z hz hzt w hw => hsrc z hz (hall z hz hzt) w hw)
    have hcnt : (X.restrict s).cnt r.tid = X.cnt r.tid := Graph.cnt_restrict X hall
    have hav : m ∈ P.toProgram.avail X := by
      rw [hmt] at hmidx hmstep
      refine mem_avail_iff.mpr ⟨hmth, ?_, ?_⟩
      · rw [hmt, ← hcnt]
        exact hmidx
      · rw [hmt, ← htr]
        exact hmstep
    exact XProgram.Mate.of_trace_eq hX hZ hm' hrX hav htr
  · right
    push Not at hall
    obtain ⟨z, hz, hzt, hzs⟩ := hall
    have hzi : r.idx + 1 ≤ z.idx := by
      by_contra hlt
      exact hzs (hkeep z hz hzt (by omega))
    have hlt : r.idx + 1 < X.cnt r.tid := by
      have := hX.idx_lt_cnt hz
      rw [hzt] at this
      omega
    obtain ⟨d, hd, hdt, hdi⟩ := (hX.exists_idx_iff r.tid (r.idx + 1)).mpr hlt
    have hds : d ∉ s := by
      intro hds
      have := hZ.idx_lt_cnt (Finset.mem_inter.mpr ⟨hd, hds⟩)
      rw [hdt, ← hmt, ← hmidx, hmi] at this
      omega
    have hdav : d ∈ P.toProgram.avail (X.restrict s) :=
      Program.mem_avail_restrict hX hE hd hds
        (fun q hq hqt hqi => hkeep q hq (hqt.trans hdt) (by omega))
        (fun q hq hqt hqi w hw =>
          hsrc q hq (hkeep q hq (hqt.trans hdt) (by omega)) w hw) hZ
    have hmd : m = d := avail_tid_inj hma hdav (hmt.trans hdt.symm)
    exact ⟨hmd ▸ hd, hmd ▸ hds⟩

/-! ### Proposition A.23 (S2), (S3) -/

/-- Proposition A.23 (S2): the read of a prospective pair is `me`. -/
def S2 (P : XProgram) (G : Graph) : Prop := ∀ r m, P.Mate G r m → G.IsMe (.th r)

/-- (S2) after the removal of `me`: if a prospective pair appears, its write is
the removed event, and its read is the new `me`. -/
theorem Rmw.s2_nr {X : Graph} {a : TEv} (hX : X.Wf) (hE : P.toProgram.Exec X)
    (hme : X.IsMe (.th a)) (hS2 : S2 P X) : S2 P (X.remove {a}) := by
  have hamax : ∀ b, ¬ X.porfStep (.th a) b := fun b h => hme.2.1 b (Relation.TransGen.single h)
  have hcl : Maz.PrefixClosed X.porfStep (Graph.evSet (X.events ∩ (X.events \ {a}))) :=
    Graph.remove_prefixClosed hX (fun q hq b hb => by
      rw [Finset.mem_singleton.mp hq] at hb
      exact absurd hb (hamax b))
  have hZ : (X.remove {a}).Wf := hX.restrict hcl
  intro r m hm
  have hrZ : r ∈ X.events ∩ (X.events \ {a}) := hm.1
  have hrX : r ∈ X.events := (Finset.mem_inter.mp hrZ).1
  have hra : r ≠ a := fun h' => by
    have := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hrZ).2).2
    exact this (by simp [h'])
  rcases hm.of_restrict hX hE hcl with h | ⟨hmX, hms⟩
  · exact absurd (Ev.th.inj ((hS2 r m h).unique hme)) hra
  · have hma : m = a := by
      by_contra hne
      exact hms (Finset.mem_sdiff.mpr ⟨hmX, by simp [hne]⟩)
    subst hma
    obtain ⟨-, hrR, -, hmav, hmt, hmi, hmW, -⟩ := hm
    have hlast : (X.remove {m}).cnt r.tid = r.idx + 1 := by
      have := idx_eq_of_mem_avail hmav
      rw [hmt] at this
      omega
    refine ⟨hrZ, fun b => hZ.not_porf_of_last_read hrR hlast b, ?_⟩
    intro b hb hbmax hbr
    cases b with
    | init => trivial
    | th b' =>
      have hbZ : b' ∈ X.events ∩ (X.events \ {m}) := hb
      have hbX : b' ∈ X.events := (Finset.mem_inter.mp hbZ).1
      have hb'r : b' ≠ r := fun h' => hbr (congrArg Ev.th h')
      -- an event of the thread of `r` other than `r` is not maximal in the prefix
      have hthr : b'.tid = r.tid → False := by
        intro ht
        have hi : b'.idx < r.idx := by
          have h1 := hZ.idx_lt_cnt hbZ
          rw [ht, hlast] at h1
          have hne : b'.idx ≠ r.idx := fun h' => hb'r (hX.idx_inj b' hbX r hrX ht h')
          omega
        have hpo : X.po (.th b') (.th r) := ⟨hbX, hrX, ht, hi⟩
        exact hbmax (.th r) ((Graph.porf_restrict_iff hcl hrZ).mpr
          (Relation.TransGen.single (Or.inl hpo)))
      -- so `b'` is maximal in `X`
      have hmaxX : ∀ c, ¬ X.porf (.th b') c := by
        intro c hc
        obtain ⟨c', hc'⟩ := Maz.exists_first_of_transGen hc
        cases c' with
        | init =>
          rcases hc' with h | ⟨q, hq, -, -⟩
          · exact absurd h (by simp [Graph.po])
          · cases hq
        | th q =>
          by_cases hqm : q = m
          · subst hqm
            rcases hc' with h | ⟨q', hq', -, hrf⟩
            · exact hthr (h.2.2.1.trans hmt)
            · rw [← Ev.th.inj hq'] at hrf
              have := hX.isRead_of_rf hrf
              exact (Act.not_isRead_and_isWrite q.act) ⟨this, hmW⟩
          · have hqX : q ∈ X.events := (hX.mem_of_porfStep hc').2
            have hqZ : Ev.th q ∈ Graph.evSet (X.events ∩ (X.events \ {m})) :=
              Finset.mem_inter.mpr ⟨hqX, Finset.mem_sdiff.mpr ⟨hqX, by simp [hqm]⟩⟩
            exact hbmax (.th q) ((Graph.porf_restrict_iff hcl hqZ).mpr
              (Relation.TransGen.single hc'))
      have hbm : b' ≠ m := fun h' => by
        have := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hbZ).2).2
        exact this (by simp [h'])
      have hlt : nextLt b' m := hme.2.2 (.th b') hbX hmaxX (fun h' => hbm (Ev.th.inj h'))
      rcases hlt with h1 | ⟨h1, -⟩ | ⟨h1, -, -⟩
      · refine Or.inl ?_
        rw [← hmt]
        exact h1
      · exact absurd (h1.trans hmt) hthr
      · exact absurd (h1.trans hmt) hthr

/-- The start of the completion in a backward revisit step: a prospective pair
of `X \ {a, e}` has the write `e`. -/
theorem Rmw.towards_rv {X : Graph} {a e : TEv} (hX : X.Wf) (hE : P.toProgram.Exec X)
    (hme : X.IsMe (.th a)) (har : a.IsRead) (hpo : ∀ b, X.porf (.th e) b ↔ b = .th a)
    (hS2 : S2 P X) : Towards P e (X.remove {a, e}) := by
  have hamax : ∀ b, ¬ X.porfStep (.th a) b := fun b h => hme.2.1 b (Relation.TransGen.single h)
  have hcl : Maz.PrefixClosed X.porfStep (Graph.evSet (X.events ∩ (X.events \ {a, e}))) :=
    Graph.remove_prefixClosed hX (fun q hq b hb => by
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact absurd hb (hamax b)
      · rw [Finset.mem_singleton.mp hq] at hb
        exact ⟨a, by simp, (hpo b).mp (Relation.TransGen.single hb)⟩)
  intro r m hm
  have hrZ : r ∈ X.events ∩ (X.events \ {a, e}) := hm.1
  have hra : r ≠ a := fun h' => by
    have := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hrZ).2).2
    exact this (by simp [h'])
  rcases hm.of_restrict hX hE hcl with h | ⟨hmX, hms⟩
  · exact absurd (Ev.th.inj ((hS2 r m h).unique hme)) hra
  · left
    by_contra hne
    have hma : m = a := by
      by_contra hne'
      exact hms (Finset.mem_sdiff.mpr ⟨hmX, by simp [hne, hne']⟩)
    exact (Act.not_isRead_and_isWrite a.act) ⟨har, hma ▸ hm.2.2.2.2.2.2.1⟩

/-- (S2) for the graph that the completion towards `e` returns. -/
theorem Rmw.s2_of_towards {Y : Graph} {e : TEv} (hY : Y.Wf)
    (hac : Maz.Acyclic Y.porfStep) (hnext : P.toProgram.IsNext Y e) (hK : Towards P e Y)
    (hs1 : ∀ m', Y.IsMe (.th m') → ¬ nextLt e m') : S2 P Y := by
  intro r m hm
  have hme : m = e := (hK r m hm).elim id (fun h => Program.isNext_unique h.2 hnext)
  subst hme
  obtain ⟨hrY, hrR, -, hmav, hmt, hmi, -, -⟩ := hm
  have hlast : Y.cnt r.tid = r.idx + 1 := by
    have := idx_eq_of_mem_avail hmav
    rw [hmt] at this
    omega
  have hrmax := hY.not_porf_of_last_read hrR hlast
  obtain ⟨b, hb⟩ := Graph.exists_isMe hY hac
  suffices h : b = .th r from h ▸ hb
  by_contra hne
  have hlt := hb.2.2 (.th r) hrY hrmax (fun h' => hne h'.symm)
  cases b with
  | init => exact hlt
  | th b' =>
    have hlt' : nextLt r b' := hlt
    rcases hlt' with h1 | ⟨h1, h2⟩ | ⟨h1, h2, -⟩
    · refine hs1 b' hb (Or.inl ?_)
      rw [hmt]
      exact h1
    · have := hY.idx_lt_cnt (show b' ∈ Y.events from hb.1)
      rw [← h1, hlast] at this
      omega
    · exact hne (congrArg Ev.th (hY.idx_inj b' hb.1 r hrY h1.symm h2.symm))

/-- Proposition A.23 (S2), (S3) for one backward step: from a well-formed
consistent execution that satisfies (S1) and (S2), a backward step gives one
that satisfies (S2). -/
theorem PrevStep.invX (hM : ExtensibleX P M) {X Y : Graph} {e : TEv} {k : Kind} (hX : X.Wf)
    (hE : P.toProgram.Exec X) (hc : (M.sym S).cons X)
    (hS1 : ∀ y ∈ P.toProgram.avail X, ∀ m, X.IsMe m → ¬ nextLtEv (.th y) m) (hS2 : S2 P X)
    (hs : PrevStep P.toProgram τ X e k Y) :
    Y.Wf ∧ P.toProgram.Exec Y ∧ (M.sym S).cons Y ∧ S2 P Y := by
  cases k with
  | rv a =>
    obtain ⟨hme, har, hrf, -, hpo, hmc⟩ := hs.rv_inv
    obtain ⟨hp, hav⟩ := rv_remove hX hE hme hrf hpo
    obtain ⟨hW0, hc0⟩ := (M.sym S).cons_prefix hX hc hp
    have hE0 := hE.of_isPrefixOf hX hp
    obtain ⟨hW', hE', -⟩ := hmc.facts hW0 hE0 hav
    obtain ⟨hc1, hc2⟩ := Model.sym_cons_iff.mp hc0
    obtain ⟨⟨h1, h2⟩, hK⟩ := Rmw.complChain hM hW0 hE0 hav ⟨hc1, τ.inv_ctx hc2⟩
      (Rmw.towards_rv hX hE hme har hpo hS2) hmc.1
    have hcY : (M.sym S).cons Y := Model.sym_cons_of_inv τ h1 h2
    refine ⟨hW', hE', hcY,
      Rmw.s2_of_towards hW' ((M.sym S).porf_acyclic _ hW' hcY) hmc.2 hK ?_⟩
    intro m' hm'
    exact (hs.s1_step hX hE hS1).2 e hmc.2.1 (.th m') hm'
  | nr =>
    obtain ⟨hme, rfl, -⟩ := hs.nr_inv
    obtain ⟨hp, -, -⟩ := nr_remove (P := P.toProgram) hX hE hme
    obtain ⟨hW0, hc0⟩ := (M.sym S).cons_prefix hX hc hp
    exact ⟨hW0, hE.of_isPrefixOf hX hp, hc0, Rmw.s2_nr hX hE hme hS2⟩

/-- Proposition A.23 (S1), (S2), (S3) for the graphs obtained from a full
consistent execution by backward steps. -/
theorem PrevReach.invX (hM : ExtensibleX P M) {Gf G : Graph} (hGf : Gf.Wf)
    (hEf : P.toProgram.Exec Gf) (hcf : (M.sym S).cons Gf) (hff : P.toProgram.Full Gf)
    (h : PrevReach P.toProgram τ Gf G) :
    G.Wf ∧ P.toProgram.Exec G ∧ (M.sym S).cons G ∧ S2 P G ∧
      ∀ y ∈ P.toProgram.avail G, ∀ m, G.IsMe m → ¬ nextLtEv (.th y) m := by
  induction h with
  | refl =>
    rw [Program.Full] at hff
    refine ⟨hGf, hEf, hcf, fun r m hm => ?_, fun y hy => ?_⟩
    · have := hm.2.2.2.1
      rw [hff] at this
      exact absurd this (by simp)
    · rw [hff] at hy
      exact absurd hy (by simp)
  | tail _ hs ih =>
    obtain ⟨e, k, hs⟩ := hs
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    obtain ⟨h1', h2', h3', h4'⟩ := hs.invX hM h1 h2 h3 h5 h4
    exact ⟨h1', h2', h3', h4', (hs.s1_step h1 h2 h5).2⟩

/-- Lemma A.24: the event that a backward step removes is the next event of
the graph it returns. -/
theorem PrevReach.next_of_prevStepX (hM : ExtensibleX P M) {Gf G G' : Graph} {e : TEv}
    {k : Kind} (hGf : Gf.Wf) (hEf : P.toProgram.Exec Gf) (hcf : (M.sym S).cons Gf)
    (hff : P.toProgram.Full Gf) (h : PrevReach P.toProgram τ Gf G)
    (hs : PrevStep P.toProgram τ G e k G') : P.toProgram.IsNext G' e := by
  obtain ⟨hW, hE, -, -, hS1⟩ := PrevReach.invX hM hGf hEf hcf hff h
  exact (hs.s1_step hW hE hS1).1

end Condpor
