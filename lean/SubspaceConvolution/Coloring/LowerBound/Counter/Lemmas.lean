/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.Counter.Defs

/-!
# Appendix G: basic facts about the construction

Parameters, cardinalities, the entry test `(e_i, Tᵀ e_i)ᵀ t_{A,j} = T_{ij} + A_{ij}`, and
characterizations of the adjacency relation of `graph I`.
-/

open Finset Matrix

set_option linter.unusedSectionVars false

namespace SubspaceConvolution.Counter

variable {I : MinCSP}

/-! ## Parameters -/

theorem k_le_M (I : MinCSP) : I.k ≤ M I := Nat.find_spec (exists_sq_exponent I.k)

theorem d_pos (hI : I.Normalized) : 0 < d I := by
  by_contra h0
  have h0 : d I = 0 := by omega
  have := k_le_M I
  rw [M, h0] at this
  have := hI.two_le_k
  simp at *
  omega

theorem M_pos (I : MinCSP) : 0 < M I := by unfold M; positivity

theorem W_le_Q (hI : I.Normalized) : I.W ≤ Q I :=
  hI.W_le.trans (Nat.mul_le_mul_right _ (k_le_M I))

theorem n_le_Q (I : MinCSP) : I.n ≤ Q I := by
  unfold Q
  exact Nat.le_mul_of_pos_left _ (M_pos I)

theorem Q_le_eta (I : MinCSP) : Q I ≤ eta I := by unfold eta; omega

theorem n_le_eta (I : MinCSP) : I.n ≤ eta I := (n_le_Q I).trans (Q_le_eta I)

/-! ## Cardinalities -/

theorem card_Mat (I : MinCSP) : Fintype.card (Mat I) = M I := by
  simp only [Mat, Fintype.card_fun, Fintype.card_fin, ZMod.card, M]
  rw [← pow_mul]

theorem card_IIdx (I : MinCSP) : Fintype.card (IIdx I) = numI I := by
  rw [Fintype.card_congr (IIdx.equivSigma I)]
  simp only [Fintype.card_sigma, Fintype.card_fin, numI]
  refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun R _ => ?_
  exact Finset.sum_coe_sort (I.scope C) (fun x => I.n - I.thr C R x)

theorem card_AIdx (I : MinCSP) : Fintype.card (AIdx I) = ∑ C, (I.scope C).card := by
  simp [AIdx, Fintype.card_sigma]

/-- `η = Q + |D|`: the selectors and anchors are indexed by `Fin p ⊕ IIdx I`. -/
theorem eta_eq_Q_add_card_D (I : MinCSP) : eta I = Q I + Fintype.card (Fin I.p ⊕ IIdx I) := by
  simp [eta, card_IIdx]

/-! ## The entry test -/

theorem regLabel_dotProduct_testVec {m : ℕ} (i : Fin m) (a : Fin m → F2)
    (A : Fin m → Fin m → F2) (j : Fin m) : regLabel i a ⬝ᵥ testVec A j = A i j + a j := by
  simp [dotProduct, regLabel, testVec, Fintype.sum_sum_type, Pi.single_apply]

theorem F2_add_eq_one_iff (a b : F2) : a + b = 1 ↔ a ≠ b := by
  revert a b
  decide

/-! ## Adjacency -/

theorem adj_iff {v w : Vtx I} : (graph I).Adj v w ↔ v ≠ w ∧ (edge I v w ∨ edge I w v) :=
  SimpleGraph.fromRel_adj _ _ _

theorem adj_of_edge {v w : Vtx I} (hne : v ≠ w) (h : edge I v w) : (graph I).Adj v w :=
  adj_iff.2 ⟨hne, Or.inl h⟩

theorem edge_aV_row {C : Fin I.p} {x : Fin I.k} {hx : x ∈ I.scope C} {j : Fin (d I)}
    {t : Fin I.n} {i : Fin (d I)} {A : Mat I} {s : Fin I.n} :
    edge I (.aV C x hx j t) (.row i A s) ↔ A i j ≠ enc I x i j := by
  simp only [edge, regLabel_dotProduct_testVec, F2_add_eq_one_iff]
  exact ne_comm

/-- The adjacency of a test vertex and a register vertex: the label `(e_i, A i)` of `row i A s`
fails the test `t_{enc x, j}` exactly when `A i j ≠ (enc x) i j`. -/
theorem adj_aV_row {C : Fin I.p} {x : Fin I.k} {hx : x ∈ I.scope C} {j : Fin (d I)}
    {t : Fin I.n} {i : Fin (d I)} {A : Mat I} {s : Fin I.n} :
    (graph I).Adj (.aV C x hx j t) (.row i A s) ↔ A i j ≠ enc I x i j := by
  rw [adj_iff, edge_aV_row]
  simp [edge]

end SubspaceConvolution.Counter
