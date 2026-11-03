/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution

/-!
# Axiom audit

`#print axioms` for the main declarations of both parts of the formalization, grouped by the
section of the paper.  Run `lake env lean Audit.lean`; `scripts/check_axioms.py` checks that every
declaration depends only on `propext`, `Classical.choice` and `Quot.sound`.
-/

open SubspaceConvolution
-- Lemma 3
#print axioms SubspaceConvolution.compatible_profile_iff
#print axioms SubspaceConvolution.profile_eq_map
#print axioms SubspaceConvolution.bilin_congr_left
-- Theorem 6
#print axioms SubspaceConvolution.MergeData.run_spec
#print axioms SubspaceConvolution.hists_union
#print axioms SubspaceConvolution.treeDP_eq_hists
#print axioms SubspaceConvolution.count_treeDP_root
#print axioms SubspaceConvolution.card_coloring_eq_sum
#print axioms SubspaceConvolution.eval_chromaticPolynomial
#print axioms SubspaceConvolution.eq_chromaticPolynomial_of_eval
#print axioms SubspaceConvolution.chromaticNumber_eq_sInf
#print axioms SubspaceConvolution.chromaticPolynomial_eq_treeDP
#print axioms SubspaceConvolution.chromaticNumber_eq_treeDP
#print axioms SubspaceConvolution.exists_optimal_of_treeDP
#print axioms SubspaceConvolution.treeCost_le
#print axioms SubspaceConvolution.treeCost_le_pow
-- Corollary 1
#print axioms SubspaceConvolution.hists_insert
#print axioms SubspaceConvolution.linDP_layout
#print axioms SubspaceConvolution.chromaticPolynomial_eq_linDP
#print axioms SubspaceConvolution.chromaticNumber_eq_linDP
#print axioms SubspaceConvolution.linCost_le
-- Proposition 1
#print axioms SubspaceConvolution.exists_cutLabels
#print axioms SubspaceConvolution.proper_iff_profiles
#print axioms SubspaceConvolution.card_coloring_eq_completionSum
#print axioms SubspaceConvolution.completionSum_eq_zetaOn
#print axioms SubspaceConvolution.zetaOn_univ_eq_foldr
#print axioms SubspaceConvolution.completion_cost_le
-- Appendix A counts
#print axioms SubspaceConvolution.numSubspaces_le
#print axioms SubspaceConvolution.le_numSubspaces
#print axioms SubspaceConvolution.card_finrank_eq_mul_prod
-- Appendix G
#print axioms SubspaceConvolution.Counter.colorable_iff
#print axioms SubspaceConvolution.Counter.layout_width
#print axioms SubspaceConvolution.Counter.card_Vtx_le_poly
#print axioms SubspaceConvolution.Counter.reduction_spec
#print axioms SubspaceConvolution.Counter.chromatic_lower_bound
-- Appendix H
#print axioms SubspaceConvolution.FixedPalette.card_coloring
#print axioms SubspaceConvolution.FixedPalette.layout_width
#print axioms SubspaceConvolution.FixedPalette.reduction_spec
#print axioms SubspaceConvolution.FixedPalette.fixed_palette_lower_bound
#print axioms SubspaceConvolution.FixedPalette.fixed_palette_counting_lower_bound
#print axioms SubspaceConvolution.FixedPalette.caterpillar_width
#print axioms SubspaceConvolution.Counter.caterpillar_width
-- ===== Part I: the transforms =====
-- Lemma 1, equations (8)/(12)
#print axioms SubspaceConvolution.HypData.existsUnique_lift
#print axioms SubspaceConvolution.HypData.lift_le_lift_iff
#print axioms SubspaceConvolution.HypData.finrank_lift
#print axioms SubspaceConvolution.HypData.lift_inf_H
#print axioms SubspaceConvolution.HypData.containT_split_inl
#print axioms SubspaceConvolution.HypData.containT_split_inr
-- Fourier, Lemma 2, equation (10), coefficient rings
#print axioms SubspaceConvolution.fourierQInv_fourierQ
#print axioms SubspaceConvolution.sum_freq_psi
#print axioms SubspaceConvolution.fourier_affineT
#print axioms SubspaceConvolution.affineT_eq
#print axioms SubspaceConvolution.FourierData.ext
#print axioms SubspaceConvolution.FourierData.complex_consts
-- Cost model
#print axioms SubspaceConvolution.Circuit.LinCost.comp
#print axioms SubspaceConvolution.Circuit.LinCost.sigma
#print axioms SubspaceConvolution.Circuit.LinCost.transpose
#print axioms SubspaceConvolution.Circuit.LinCost.baseChange
#print axioms SubspaceConvolution.Circuit.dft_cost
#print axioms SubspaceConvolution.Circuit.idft_cost
#print axioms SubspaceConvolution.Circuit.morgenstern
#print axioms SubspaceConvolution.Circuit.ArithCost.comp
-- Theorem 1
#print axioms SubspaceConvolution.containT_step
#print axioms SubspaceConvolution.zeta_linCost
#print axioms SubspaceConvolution.zetaInv_linCost
#print axioms SubspaceConvolution.fast_subspace_summation
#print axioms SubspaceConvolution.fast_subspace_summation_log
-- Theorem 2
#print axioms SubspaceConvolution.incid_linCost
#print axioms SubspaceConvolution.fast_incidence
#print axioms SubspaceConvolution.fast_incidence_complex
-- Appendices A, B; Section 3.3
#print axioms SubspaceConvolution.gr_mul_prod
#print axioms SubspaceConvolution.gr_succ_succ
#print axioms SubspaceConvolution.gr_symm
#print axioms SubspaceConvolution.pow_le_gr
#print axioms SubspaceConvolution.gr_le
#print axioms SubspaceConvolution.pow_le_numLE_self
#print axioms SubspaceConvolution.numLE_self_le
#print axioms SubspaceConvolution.numLE_le_two_mul_gr
#print axioms SubspaceConvolution.pow_le_coverPairs
#print axioms SubspaceConvolution.coverPairs_le
#print axioms SubspaceConvolution.numLE_count
#print axioms SubspaceConvolution.two_mul_numLE_le
#print axioms SubspaceConvolution.mul_le_log_numLE
#print axioms SubspaceConvolution.slack
#print axioms SubspaceConvolution.incid_budget_step
#print axioms SubspaceConvolution.incidBound_le
-- Introduction, footnote, Section 5.3 count
#print axioms SubspaceConvolution.coverPairs_theta
#print axioms SubspaceConvolution.coverPairs_theta_rpow
#print axioms SubspaceConvolution.sqDist_lineIndicator
#print axioms SubspaceConvolution.card_inclusions_theta
-- Section 5: convolution, Theorem 5
#print axioms SubspaceConvolution.zetaAll_spanConv
#print axioms SubspaceConvolution.fast_spanConv
#print axioms SubspaceConvolution.zetaAllT_interConv
#print axioms SubspaceConvolution.directConv_eq_coeff
#print axioms SubspaceConvolution.two_pow_card_eq_sum_spanCount
#print axioms SubspaceConvolution.spanCount_eq_zetaAllInv
#print axioms SubspaceConvolution.fast_span_count
-- Theorem 3 and Section 5.3
#print axioms SubspaceConvolution.moments
#print axioms SubspaceConvolution.kernelCoeff_spec
#print axioms SubspaceConvolution.kernelApply_eq_zeta
#print axioms SubspaceConvolution.kernelApply_dual
#print axioms SubspaceConvolution.fast_kernel
#print axioms SubspaceConvolution.fast_kernel_arith
#print axioms SubspaceConvolution.grassGraph_dist
#print axioms SubspaceConvolution.invariant_iff_exists_dist
-- Appendix C
#print axioms SubspaceConvolution.moment_profile
#print axioms SubspaceConvolution.fast_distance_sums
#print axioms SubspaceConvolution.isLeast_minDist
#print axioms SubspaceConvolution.rect_moments
#print axioms SubspaceConvolution.rectKernel_eq_sum_incid
#print axioms SubspaceConvolution.rectKernel_dual
#print axioms SubspaceConvolution.fast_rectKernel
#print axioms SubspaceConvolution.allKernel_eq_zetaAll
#print axioms SubspaceConvolution.fast_allKernel
#print axioms SubspaceConvolution.aeval_adjEnd_eq_zero
#print axioms SubspaceConvolution.sum_specProj
#print axioms SubspaceConvolution.specComponents_linCost
#print axioms SubspaceConvolution.bijective_kernelApply_iff
#print axioms SubspaceConvolution.kernelApply_inverse
#print axioms SubspaceConvolution.kernelInverse_linCost
-- Corollary 2
#print axioms SubspaceConvolution.zetaInv_eq_sum_mobius
#print axioms SubspaceConvolution.exact_integer_zeta
#print axioms SubspaceConvolution.exact_integer_zetaInv
#print axioms SubspaceConvolution.exact_integer_zetaT
#print axioms SubspaceConvolution.exact_integer_zetaTInv
#print axioms SubspaceConvolution.exact_integer_incid
#print axioms SubspaceConvolution.exact_integer_incidT
-- Theorem 7
#print axioms SubspaceConvolution.LowerBoundAux.abs_det_incMat_ge
#print axioms SubspaceConvolution.incidence_lower_bound
#print axioms SubspaceConvolution.incidence_lower_bound_attained
-- Proposition 1 with the cost of Theorem 1
#print axioms SubspaceConvolution.fast_completionSum
#print axioms SubspaceConvolution.fast_completion_count
