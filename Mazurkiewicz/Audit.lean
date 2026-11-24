import Mazurkiewicz.Lib.Rel
import Mazurkiewicz.Lib.ListOrder
import Mazurkiewicz.Lib.Path
import Mazurkiewicz.Lib.Finset
import Mazurkiewicz.Trust.Ops
import Mazurkiewicz.Trust.Examples
import Mazurkiewicz.Trust.Program
import Mazurkiewicz.Models.Model
import Mazurkiewicz.Trust.Alg
import Mazurkiewicz.Trust.AlgExamples
import Mazurkiewicz.Trust.Invariants
import Mazurkiewicz.Trust.A22
import Mazurkiewicz.Trust.Oracle
import Mazurkiewicz.Induction.AssertExample
import Mazurkiewicz.Induction.ToggleExample
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
import Mazurkiewicz.Jmt.Stage
import Mazurkiewicz.Jmt.Structure

/-!
# Axiom audit

`#print axioms` for the main results of each milestone. Allowed:
`propext`, `Classical.choice`, `Quot.sound`.
-/

-- M1
#print axioms Maz.Acyclic.of_sink
#print axioms Maz.transGen_restrict_iff
#print axioms Maz.restrict_eq_of_total
#print axioms Maz.exists_sink_of_bounded_measure
#print axioms List.before_filter_iff
#print axioms List.before_insertAfter_iff
#print axioms List.before_append_singleton_iff
#print axioms List.not_before_getLast
#print axioms List.Nodup.insertAfter
#print axioms Maz.Path.exists_snoc
#print axioms Maz.Path.exists_cross
#print axioms Maz.Path.reverse
#print axioms Maz.Path.length_le_of_bounded_measure
#print axioms List.insertAfter_getLast
#print axioms List.filter_insertAfter_of_neg
#print axioms Finset.eq_range_of_downClosed

-- M2
#print axioms Trust.Graph.init_wf
#print axioms Trust.Graph.Wf.exists_idx_iff
#print axioms Trust.Graph.Wf.addRead
#print axioms Trust.Graph.Wf.addWrite
#print axioms Trust.Graph.WfExcept.addWrite
#print axioms Trust.Graph.WfExcept.setRF
#print axioms Trust.Graph.Wf.restrict_except
#print axioms Trust.Graph.Wf.restrict
#print axioms Trust.Graph.ret_restrict
#print axioms Trust.Graph.traceBefore_restrict
#print axioms Trust.Graph.traceBefore_restrict_of_sources
#print axioms Trust.Graph.trace_addRead
#print axioms Trust.Graph.trace_addWrite
#print axioms Trust.Graph.porf_restrict_iff
#print axioms Trust.Graph.coRel_restrict_iff
#print axioms Trust.Graph.frRel_restrict_mono
#print axioms Trust.Graph.restrict_restrict
#print axioms Trust.Graph.Wf.isPrefixOf_refl
#print axioms Trust.Graph.init_isPrefixOf
#print axioms Trust.Graph.Wf.isPrefixOf_addRead
#print axioms Trust.Graph.Wf.isPrefixOf_addWrite
#print axioms Trust.Graph.maxWrite_co_maximal
#print axioms Trust.Graph.addWrite_maxWrite_co
#print axioms Trust.Examples.Gww_wf
#print axioms Trust.Examples.G2_wf
#print axioms Trust.Graph.porf_addWrite_wp
#print axioms Trust.Graph.eq_init_of_porf
#print axioms Trust.Examples.porf_w
#print axioms Trust.Examples.fig4_4_wf

-- M3
#print axioms Maz.Acyclic.exists_maximal
#print axioms Trust.Graph.traceBefore_restrict_of_keep
#print axioms Trust.Program.nextLt_trans
#print axioms Trust.Program.nextLt_total
#print axioms Trust.Program.mem_avail_iff
#print axioms Trust.Program.exists_unique_isNext
#print axioms Trust.Program.Exec.tid_mem
#print axioms Trust.Program.Exec.addRead
#print axioms Trust.Program.Exec.addWrite
#print axioms Trust.Program.Exec.of_isPrefixOf
#print axioms Trust.Program.Exec.full_iff
#print axioms Trust.Program.Exec.restrict_except
#print axioms Trust.Program.Exec.setRF
#print axioms Trust.Program.Exec.cnt_le
#print axioms Trust.Program.Exec.card_le
#print axioms Trust.Program.Built.exec
#print axioms Trust.Program.Built.acyclic
#print axioms Trust.Program.Exec.built
#print axioms Trust.Config.trace_eq
#print axioms Trust.Program.availC_eq
#print axioms Trust.Program.nextC_eq_some_iff
#print axioms Trust.Program.nextC_eq_none_iff
#print axioms Trust.Program.Built.fresh
#print axioms Trust.Program.avail_congr
#print axioms Trust.Program.avail_tid_inj
#print axioms Trust.Program.idx_eq_of_mem_avail
#print axioms Trust.Program.full_iff
#print axioms Trust.Program.exec_init
#print axioms Trust.Program.nextLt_irrefl
#print axioms Trust.Program.actLt_irrefl
#print axioms Trust.Program.actLt_trans
#print axioms Trust.Program.actLt_total
#print axioms Trust.Program.Exec.of_traceBefore_eq
#print axioms Trust.Config.evAt_eq
#print axioms Trust.Config.cnt_eq
#print axioms Trust.Program.rf_of_restrict_eq

-- M4
#print axioms Trust.Model.porf_irrefl
#print axioms Trust.Model.cons_prefix
#print axioms Trust.Graph.Wf.addMax
#print axioms Trust.Graph.porfStep_addRead
#print axioms Trust.Graph.not_porfStep_addRead_self
#print axioms Trust.Graph.porfStep_addWrite
#print axioms Trust.Graph.not_porfStep_addWrite_self
#print axioms Trust.Graph.scStep_addRead_maxWrite
#print axioms Trust.Graph.not_scStep_addRead_maxWrite_self
#print axioms Trust.Graph.scStep_addWrite_maxWrite
#print axioms Trust.Graph.not_scStep_addWrite_maxWrite_self
#print axioms Trust.Graph.scStep_restrict
#print axioms Trust.Model.Extensible.cons_addMax
#print axioms Trust.Program.Exec.addMax
#print axioms Trust.Free
#print axioms Trust.Free.extensible
#print axioms Trust.SC
#print axioms Trust.SC.extensible
#print axioms Trust.Graph.addMax_read
#print axioms Trust.Graph.addMax_write
#print axioms Trust.Graph.po_of_events_insert
#print axioms Trust.Graph.not_po_of_events_insert
#print axioms Trust.Graph.addWrite_maxWrite_co_eq
#print axioms Trust.Graph.not_scStep_init
#print axioms Trust.Examples.fig4_4_cons

-- M5a
#print axioms Trust.Config.revisit_abs
#print axioms Trust.Config.keep_po_closed
#print axioms Trust.Config.keep_sources
#print axioms Trust.Config.keep_last
#print axioms Trust.Config.keep_thread
#print axioms Trust.Config.restrict_keep_wf
#print axioms Trust.Config.revisit_wf
#print axioms Trust.Config.poLt_cons
#print axioms Trust.Config.revisit_exec
#print axioms Trust.StepL.order
#print axioms Trust.StepL.wf
#print axioms Trust.StepL.poLt
#print axioms Trust.StepL.cons
#print axioms Trust.StepL.exec
#print axioms Trust.StepL.rv_inv
#print axioms Trust.StepL.nr_inv
#print axioms Trust.Reach.sound
#print axioms Trust.Reach.sound_full
#print axioms Trust.Reach.sound_built_full
#print axioms Trust.Examples.C1_step
#print axioms Trust.Examples.revisit_reach
#print axioms Trust.Examples.C1_max_d
#print axioms Trust.Examples.C1_max_r
#print axioms Trust.Examples.C1_keep

-- M5b (Lemma A.20, `me`, Proposition A.22)
#print axioms Trust.A20_D1
#print axioms Trust.A20_D2
#print axioms Trust.A20_D3
#print axioms Trust.A20_step
#print axioms Trust.Graph.IsMe.unique
#print axioms Trust.Graph.exists_isMe
#print axioms Trust.Graph.isMe_init
#print axioms Trust.Program.exists_nextLt_max
#print axioms Trust.StepL.nrFacts
#print axioms Trust.NrFacts.bw_iff
#print axioms Trust.RvHyp.lt_iff
#print axioms Trust.RvHyp.bw_iff
#print axioms Trust.RvHyp.r_max
#print axioms Trust.RvHyp.w_out
#print axioms Trust.RvHyp.porf_kept
#print axioms Trust.RvHyp.porf_w_iff
#print axioms Trust.RvHyp.avail_cases
#print axioms Trust.LastStep.witness
#print axioms Trust.inv_nr
#print axioms Trust.inv_rv
#print axioms Trust.Reach.inv
#print axioms Trust.Reach.a22
#print axioms Trust.Examples.C1_reach
#print axioms Trust.Reach.lastStep
#print axioms Trust.Reach.me_eq
#print axioms Trust.A22.del_after_r
#print axioms Trust.RvHyp.deleted_iff
#print axioms Trust.Reach.bw_po_lt

-- M6
#print axioms Trust.ReachRW.reach
#print axioms Trust.Reach.exists_rw
#print axioms Trust.ReachRW.a21
#print axioms Trust.StepRW.measure_lt
#print axioms Trust.lift_path
#print axioms Trust.terminates
#print axioms Trust.step_wellFounded
#print axioms Trust.Examples.revProg_bounded

-- M7a
#print axioms Trust.MaxCompl.det
#print axioms Trust.MaxCompl.exists
#print axioms Trust.MaxCompl.facts
#print axioms Trust.MaxCompl.cons
#print axioms Trust.PrevStep.det
#print axioms Trust.exists_prevStep
#print axioms Trust.not_prevStep_init
#print axioms Trust.PrevStep.inv
#print axioms Trust.PrevReach.inv
#print axioms Trust.PrevReach.s1
#print axioms Trust.PrevReach.next_of_prevStep

-- M7b
#print axioms Trust.Graph.NoEarlierSucc.me_ge
#print axioms Trust.ComplStep.order
#print axioms Trust.PrevStep.noEarlierSucc
#print axioms Trust.PrevStep.not_noEarlierSucc
#print axioms Trust.PrevReach.rv_mem
#print axioms Trust.PrevReachRW.subset
#print axioms Trust.PrevReachRW.a25
#print axioms Trust.PrevReach.init
#print axioms Trust.PrevStep.rv_not_mem
#print axioms Trust.PrevStep.nr_events

-- M8
#print axioms Trust.ComplStep.co_order
#print axioms Trust.RvData.del_iff
#print axioms Trust.RvData.maxAdded
#print axioms Trust.RvData.step
#print axioms Trust.Reach.deleted_iff_of_prevStep
#print axioms Trust.Reach.step_of_prevStep
#print axioms Trust.PrevReach.reach
#print axioms Trust.complete

-- M9
#print axioms Trust.Reach.prevStep_of_step_nr
#print axioms Trust.Reach.prevStep_of_step_rv
#print axioms Trust.Reach.prevStep_of_step
#print axioms Trust.StepL.eq_of_abs_eq
#print axioms Trust.Reach.pred_unique
#print axioms Trust.StepL.label_unique
#print axioms Trust.path_unique
#print axioms Trust.Reach.eq_of_abs_eq

-- M10a
#print axioms Trust.terminates_bound
#print axioms Trust.mem_succs
#print axioms Trust.succs_nodup
#print axioms Trust.mem_exploreFrom
#print axioms Trust.exploreFrom_nodup
#print axioms Trust.explore_sound
#print axioms Trust.explore_nodup
#print axioms Trust.explore_spec

-- M10b
#print axioms Maz.reachN_iff
#print axioms Maz.acyclicB_iff
#print axioms Trust.Graph.porfB_iff
#print axioms Trust.Graph.consB_iff
#print axioms Trust.Config.keepC_eq
#print axioms Trust.Config.revisitC_eq
#print axioms Trust.Config.maxAddedB_iff
#print axioms Trust.Config.revisitOKB_iff
#print axioms Trust.step_revisit_iff
#print axioms Trust.succsC_eq
#print axioms Trust.exploreFromC_eq
#print axioms Trust.exploreC_eq
#print axioms Trust.exploreC_spec

-- M10c
#print axioms Trust.Program.exec_trunc_iff
#print axioms Trust.Program.full_trunc_iff
#print axioms Trust.Program.Exec.full_trunc_cnt
#print axioms Trust.Program.trunc_bounded
#print axioms Trust.exploreC_trunc_spec
#print axioms Trust.exploreCfgC_abs

-- Induction A1
#print axioms Trust.step_cases
#print axioms Trust.Graph.IsPrefixOf.trans
#print axioms Trust.greach_iff
#print axioms Trust.greach_iff_built
#print axioms Trust.post_singleton_finite
#print axioms Trust.stepF_iterate
#print axioms Trust.greach_eq_lfp
#print axioms Trust.stabilises_iff
#print axioms Trust.greach_finite_of_bounded
#print axioms Trust.safe_iff_invariant

-- Induction A2
#print axioms Trust.mstep_iff
#print axioms Trust.MStep.unique
#print axioms Trust.exists_mstep
#print axioms Trust.mreach_iff
#print axioms Trust.exists_full_extension
#print axioms Trust.apT_eq_some_iff
#print axioms Trust.valt_range
#print axioms Trust.greach_iff_msteps

-- Induction A3
#print axioms Trust.futEq_of_state
#print axioms Trust.conf_eq_iff_threads
#print axioms Trust.MStep.trace
#print axioms Trust.MStep.memOf
#print axioms Trust.MStep.opStep
#print axioms Trust.exists_mstep_of_opStep
#print axioms Trust.conf_reach
#print axioms Trust.opReach_finite

-- Induction A4
#print axioms Trust.Program.residual_eq_iff
#print axioms Trust.St.ofResid_injective
#print axioms Trust.Graph.sc_induction
#print axioms Trust.Graph.comp_init
#print axioms Trust.Graph.comp_addMax
#print axioms Trust.Graph.comp_facts
#print axioms Trust.MStep.comp
#print axioms Trust.mstep_comp_inv
#print axioms Trust.greach_comp
#print axioms Trust.msteps_decomp

-- Induction A5
#print axioms Trust.Certificate.run_valt
#print axioms Trust.Certificate.safe
#print axioms Trust.Abstraction.res_eq
#print axioms Trust.Abstraction.confAbs_eq
#print axioms Trust.Abstraction.ksound
#print axioms Trust.Abstraction.kinductive_iff_representatives
#print axioms Trust.Abstraction.stepOK_iff_obligation
#print axioms Trust.Abstraction.reduction
#print axioms Trust.Abstraction.safe_of_obligations_realised
#print axioms Trust.Abstraction.safe_of_obligations

-- Induction A6
#print axioms Trust.mem_budgets
#print axioms Trust.budgets_nodup
#print axioms Trust.ExecSC.sum_cnt
#print axioms Trust.cover_exists
#print axioms Trust.cover_prefix
#print axioms Trust.cover_full
#print axioms Trust.cover_unique
#print axioms Trust.Graph.comp_isPrefixOf_comp
#print axioms Trust.Abstraction.stepOK_iff_full_prefix
#print axioms Trust.Abstraction.stepOK_iff_full

-- Induction A7
#print axioms Trust.exploreC_complete
#print axioms Trust.exploreC_sound
#print axioms Trust.exploreC_optimal
#print axioms Trust.check_sound_of_complete
#print axioms Trust.check_sound
#print axioms Trust.check_accepts
#print axioms Trust.checkItems_nodup
#print axioms Trust.check_count_eq_sum_ncard
#print axioms Trust.exists_unique_budget
#print axioms Trust.Mono.mono_check
#print axioms Trust.Mono.mono_safe
#print axioms Trust.Mono.mono_reject_wrong
#print axioms Trust.Mono.mono_reject_unrealised
#print axioms Trust.Mono.rw_opReach_finite

-- Induction E1-E4 (error actions)
#print axioms Trust.EGraph.consE_iff
#print axioms Trust.SProgram.enc_bounded
#print axioms Trust.psi_dHatTail
#print axioms Trust.psiInv_dTail
#print axioms Trust.psiInv_psi
#print axioms Trust.psi_psiInv
#print axioms Trust.psi_cons
#print axioms Trust.psi_trace
#print axioms Trust.SProgram.ExecE.dTail
#print axioms Trust.exec_enc_dHatTail
#print axioms Trust.execE_iff
#print axioms Trust.execSC_enc
#print axioms Trust.fullESC_iff
#print axioms Trust.fullSC_enc
#print axioms Trust.encEnum_complete
#print axioms Trust.encEnum_sound
#print axioms Trust.encEnum_eq_map
#print axioms Trust.encEnum_optimal
#print axioms Trust.encEnum_exploreC
#print axioms Trust.safeE_iff
#print axioms Trust.safeE_badErr_iff
#print axioms Trust.badMark_extClosed
#print axioms Trust.check_sound_err
#print axioms Trust.Assert.assert_check
#print axioms Trust.Assert.assert_safe
#print axioms Trust.Assert.assert_reject

-- Induction B1-B5 (cuts)
#print axioms Trust.Abstraction.barsound_path
#print axioms Trust.Abstraction.barsound
#print axioms Trust.Abstraction.barInductive_iff_path
#print axioms Trust.Abstraction.barInductive_iff_representatives
#print axioms Trust.boundary_barK
#print axioms Trust.Abstraction.barInductive_barK_iff
#print axioms Trust.cutBar_extClosed
#print axioms Trust.cutBar_congr
#print axioms Trust.cutBar_depthLe
#print axioms Trust.mem_boundary_cutBar
#print axioms Trust.Abstraction.safe_of_bar_obligations
#print axioms Trust.visit_spec
#print axioms Trust.Abstraction.checkBar_path
#print axioms Trust.Abstraction.checkBar_sound
#print axioms Trust.Toggle.mem_cutBar_tg
#print axioms Trust.Toggle.segBound_even
#print axioms Trust.Toggle.segBound_odd
#print axioms Trust.Toggle.toggle_check
#print axioms Trust.Toggle.toggle_safe
#print axioms Trust.Toggle.toggle_reject_fuel
#print axioms Trust.Toggle.toggle_reject

/-! ### Condpor: the symbolic algorithm -/

#print axioms Condpor.Model.sym_cons_addMax
#print axioms Condpor.Reach.sound
#print axioms Condpor.ComplStep.pol_added
#print axioms Condpor.RvData.maxAdded
#print axioms Condpor.complete
#print axioms Condpor.Reach.prevStep_of_step
#print axioms Condpor.path_unique
#print axioms Condpor.Reach.eq_of_abs_eq
#print axioms Condpor.Reach.reaches_full
#print axioms Condpor.exists_full_extension
#print axioms Condpor.reachX_of_reach
#print axioms Condpor.exists_reachX_err
#print axioms Condpor.complete_exit
#print axioms Condpor.explore_spec
#print axioms Condpor.Config.maxAddedB_iff
#print axioms Condpor.exploreC_eq
#print axioms Condpor.exploreC_spec
#print axioms Condpor.eqSatB_iff
#print axioms Condpor.fig1_six
#print axioms Condpor.ex1_four
#print axioms Condpor.ex1_revisit_B
#print axioms Condpor.ex1_no_revisit_C
#print axioms Condpor.sb_forbidden
#print axioms Condpor.Model.sym_cons_addRead_iff
#print axioms Condpor.Sem.sat_insert_of_models
#print axioms Condpor.complete_byModel
#print axioms Condpor.eqSolve_models
#print axioms Condpor.fig1_count_byModel
#print axioms Condpor.ex1_count_byModel
#print axioms Condpor.mem_visitC
#print axioms Condpor.exploreX_err
#print axioms Condpor.exploreX_ok
#print axioms Condpor.exploreX_finds
#print axioms Condpor.ex1_revisit_only_B
#print axioms Condpor.ex1_revisit_from_B
#print axioms Condpor.fig1_graphs
#print axioms Condpor.mem_orderings
#print axioms Condpor.orderings_read_first
#print axioms Condpor.behaviours_total
#print axioms Condpor.fig1_perm
#print axioms Condpor.exploreV_std
#print axioms Condpor.printed_deleted_self
#print axioms Condpor.n0_lost
#print axioms Condpor.n1_duplicate
#print axioms Condpor.n2_lost_init
#print axioms Condpor.n2_lost_last
#print axioms Condpor.n3_duplicate
#print axioms Condpor.n3_lost
#print axioms Condpor.revisit_chain
#print axioms Condpor.fig1_exit
#print axioms Condpor.se_ne_byModel
#print axioms Condpor.Reach.prefix_pred
#print axioms Condpor.Reach.path_of_prefix
#print axioms Condpor.Reach.exists_seg
#print axioms Condpor.Seg.unique
#print axioms Condpor.Reach.segChain
#print axioms Condpor.SegChain.unique
#print axioms Condpor.getNext_fixpoint
#print axioms Condpor.opLe_iff_isPrefixOf
#print axioms Condpor.NrLe.opLe
#print axioms Condpor.nrLe_fails
#print axioms Condpor.tsSem_all_outcomes
#print axioms Condpor.ts_executions
#print axioms Condpor.ts_explore_length
#print axioms Condpor.ctr_executions
#print axioms Condpor.ctr_explore_length
#print axioms Condpor.length_interleavings_mul
#print axioms Condpor.length_interleavings_div
#print axioms Condpor.ct_count
#print axioms Condpor.ctr_executions_2_2
#print axioms Condpor.ctr_executions_2_3
#print axioms Condpor.ctr_executions_3_2
#print axioms Condpor.CoChoice.classical
#print axioms Condpor.StepR.lift
#print axioms Condpor.ReachR.sound
#print axioms Condpor.ReachR.a22
#print axioms Condpor.terminatesR
#print axioms Condpor.PrevStepR.lift
#print axioms Condpor.prevStep_of_rvHyp
#print axioms Condpor.ReachR.prevStepR_of_step
#print axioms Condpor.path_uniqueR
#print axioms Condpor.ReachR.eq_of_rfEq
#print axioms Condpor.PrevReachR.init
#print axioms Condpor.RvData'.co_eq
#print axioms Condpor.ReachR.step_of_prevStepR
#print axioms Condpor.completeR
#print axioms Condpor.ReachR.reaches_full
#print axioms Condpor.exploreR_spec
#print axioms Condpor.exploreR_classes
#print axioms Condpor.mem_exploreR_iff_canon
#print axioms Condpor.exploreR_length_le
#print axioms Condpor.exploreR_length_sc
#print axioms Condpor.rww_three
#print axioms Condpor.fig1_ex1_rf
#print axioms Condpor.rfx_six
#print axioms Condpor.rfx_repaired
#print axioms Condpor.rfx_printed
#print axioms Condpor.rfx_printed_classes

-- Read-modify-write accesses (`Condpor/Rmw`), milestone R1
#print axioms Condpor.Model.atomic
#print axioms Condpor.Rmw.sound
#print axioms Condpor.Rmw.path_unique
#print axioms Condpor.Rmw.eq_of_abs_eq
#print axioms Condpor.SC.extensibleX
#print axioms Maz.Acyclic.of_insert
#print axioms Condpor.Graph.scStep_addWrite_acyclic
#print axioms Condpor.XProgram.Mate.read_act
#print axioms Condpor.XProgram.RMW.read_act
#print axioms Condpor.SC.exclExtensible
#print axioms Condpor.ExtensibleX.sym_ext_read
#print axioms Condpor.ExtensibleX.sym_ext_write
#print axioms Condpor.ExtensibleX.sym_ext_wex
#print axioms Condpor.ExtensibleX.sym_ext_loc_none
#print axioms Condpor.ExtensibleX.sym_ext_cons
#print axioms Condpor.ExclExtensible.sym
#print axioms Condpor.SC.exclExtensible_sym

-- Read-modify-write accesses, milestone R2: (P7), (P8)
#print axioms Condpor.Graph.porf_of_read_succ
#print axioms Condpor.RvHyp.succ_not_deleted
#print axioms Condpor.XProgram.Mate.of_trace_eq
#print axioms Condpor.XProgram.Mate.next_lt
#print axioms Condpor.XProgram.pending_iff
#print axioms Condpor.Program.nextOf_setRF_of_ne
#print axioms Condpor.LastStep.isNext_mate
#print axioms Condpor.Rmw.pending

-- Read-modify-write accesses, milestone R3: completion and backward steps
#print axioms Condpor.XProgram.exists_mate
#print axioms Condpor.ExtensibleX.sym_cons_addMax
#print axioms Condpor.ComplStep.towards
#print axioms Condpor.Rmw.complChain
#print axioms Condpor.XProgram.Mate.of_restrict
#print axioms Condpor.Rmw.s2_nr
#print axioms Condpor.Rmw.towards_rv
#print axioms Condpor.Rmw.s2_of_towards
#print axioms Condpor.PrevStep.invX
#print axioms Condpor.PrevReach.invX
#print axioms Condpor.PrevReach.next_of_prevStepX
#print axioms Condpor.PrevReach.noEarlierSuccX
#print axioms Condpor.PrevReachRW.a25X
#print axioms Condpor.PrevReach.initX
#print axioms Condpor.PrevReach.card_leX

-- Read-modify-write accesses, milestone R4: completeness
#print axioms Condpor.Reach.step_of_prevStep_nrX
#print axioms Condpor.Reach.step_of_prevStep_rvX
#print axioms Condpor.Reach.step_of_prevStepX
#print axioms Condpor.PrevReach.reachX
#print axioms Condpor.Rmw.complete
#print axioms Condpor.Rmw.complete_sc

-- Read-modify-write accesses, milestone R5: Theorem A.33 and the exit
#print axioms Condpor.Reach.exists_stepX
#print axioms Condpor.Reach.step_after
#print axioms Condpor.Reach.exists_live_step
#print axioms Condpor.Rmw.reaches_full
#print axioms Condpor.Rmw.blocked_of_fruitless
#print axioms Condpor.Rmw.collision_of_blocked
#print axioms Condpor.Reach.exists_step_of_no_ex
#print axioms Condpor.Rmw.reaches_full_of_no_ex
#print axioms Condpor.Rmw.exists_reachX_err
#print axioms Condpor.Rmw.exists_reachX_err_full
#print axioms Condpor.Rmw.complete_exit

-- Read-modify-write accesses, milestone R6: explorer and instances
#print axioms Condpor.Rmw.explore_spec
#print axioms Condpor.Config.atomicB_iff
#print axioms Condpor.Config.consX_iff
#print axioms Condpor.succsAt_eq
#print axioms Condpor.exploreAt_eq
#print axioms Condpor.exploreAt_spec
#print axioms Condpor.mem_deadFromAt
#print axioms Condpor.exists_dead_of_deadAt
#print axioms Condpor.exists_dead_iff_deadAt
#print axioms Condpor.exploreAtV_std
#print axioms Condpor.faa2_two
#print axioms Condpor.rw2_four
#print axioms Condpor.faa3_six
#print axioms Condpor.lock_count
#print axioms Condpor.lock_seven
#print axioms Condpor.lock_variant
#print axioms Condpor.wfaa2_dead
#print axioms Condpor.faar_dead
#print axioms Condpor.faa3_dead
#print axioms Condpor.lock_dead
#print axioms Condpor.faa2_no_dead

-- Locks (`Condpor/Rmw/Locks`, `LocksEx`), milestone K1
#print axioms Condpor.lockSys_explore
#print axioms Condpor.lockSys_complete
#print axioms Condpor.lockSys_eq_of_abs_eq
#print axioms Condpor.lockSys_blocked_of_fruitless
#print axioms Condpor.lockT1
#print axioms Condpor.lockT2
#print axioms Condpor.lockT3
#print axioms Condpor.lockT4
#print axioms Condpor.lockT5
#print axioms Condpor.lockT6
#print axioms Condpor.lockT1_execs
#print axioms Condpor.lockT6_execs
#print axioms Condpor.lockT0
#print axioms Condpor.lockT_no_dead
#print axioms Condpor.LockLike.alternates
#print axioms Condpor.lockState_holds_pos
#print axioms Condpor.lockSys_lockLike
#print axioms Condpor.lockSys_mutex

-- Locks with three threads (`Condpor/Rmw/LocksEx3`), milestone K4
#print axioms Condpor.lockT7
#print axioms Condpor.lockT8
#print axioms Condpor.lockT9
#print axioms Condpor.lockT7_execs
#print axioms Condpor.lockT10
#print axioms Condpor.lockT11
#print axioms Condpor.lockT12
#print axioms Condpor.lockT13
#print axioms Condpor.lockT14
#print axioms Condpor.lockT15
#print axioms Condpor.lockT16
#print axioms Condpor.lockT17

-- Java memory model: justifications and stage states (`Jmt/Stage`)
#print axioms Jmt.forward

-- Stage states: reachable executions are valid; (F3) is redundant (`Jmt/Structure`)
#print axioms Jmt.Reach.valid
#print axioms Jmt.Reach'.valid
#print axioms Jmt.valid_iff_reach'
#print axioms Jmt.forward'
#print axioms Jmt.valid'_iff_valid
#print axioms Jmt.Justifies.stage_valid
#print axioms Jmt.Step.of_sameStepData
