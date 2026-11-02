/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.Counter.Lemmas

/-!
# The size of the construction

* `card_row` / `card_row_label`: each row `B_i` is a `Q`-clique with exactly `Q/h` vertices of
  each label `(e_i, a)` (this documents that the indexing of the register vertices by pairs
  `(A, t)` gives exactly the register of the paper).
* `card_Vtx`: the exact number of vertices
  `N = d Q + (Q - W) + |D| + a d n + |I| + a (η - n)`, where `|D| = p + |I|`,
  `|I| = numI I = Σ_C Σ_R Σ_{x ∈ X_C} (n - c_{R,x})` and `a = Σ_C |X_C|` is the number of palette
  blocks; and the clean bound `N ≤ (d + 1) Q + p + 2 |I| + a (d n + η)`.
* `eta_eq`, `eta_le`: `η = Q + p + Σ_C Σ_R Σ_{x ∈ X_C} (n - c_{R,x})`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace SubspaceConvolution.Counter

variable {I : MinCSP}

/-- The number `a = Σ_C |X_C|` of palette blocks. -/
def numA (I : MinCSP) : ℕ := ∑ C, (I.scope C).card

/-- Each row `B_i` (indexed by the pairs `(A, t)`) has `Q` vertices. -/
theorem card_row (I : MinCSP) : Fintype.card (Mat I × Fin I.n) = Q I := by
  rw [Fintype.card_prod, card_Mat, Fintype.card_fin, Q]

/-- The matrices with a prescribed row `i`. -/
def matRowEquiv (i : Fin (d I)) (a : Fin (d I) → F2) :
    {A : Mat I // A i = a} ≃ ({j : Fin (d I) // j ≠ i} → Fin (d I) → F2) where
  toFun A j := A.1 j
  invFun f := ⟨fun j => if h : j = i then a else f ⟨j, h⟩, by simp⟩
  left_inv A := by
    ext j : 2
    by_cases h : j = i
    · subst h; simp [A.2]
    · simp [h]
  right_inv f := by
    ext j : 1
    simp [j.2]

/-- In the row `B_i`, exactly `Q/h` vertices have the label `(e_i, a)`: the vertex `row i A t`
has label `(e_i, A i)`. -/
theorem card_row_label (i : Fin (d I)) (a : Fin (d I) → F2) :
    Fintype.card {q : Mat I × Fin I.n // q.1 i = a} = Q I / h I := by
  have hd : 0 < d I := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  rw [Fintype.card_congr (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun A : Mat I => A i = a)),
    Fintype.card_prod, Fintype.card_congr (matRowEquiv i a), Fintype.card_fun,
    Fintype.card_subtype_compl, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ZMod.card]
  have h1 : Fintype.card {j : Fin (d I) // j = i} = 1 := Fintype.card_subtype_eq i
  rw [h1, Q, M, h, ← pow_mul]
  have h2 : d I * d I = d I + d I * (d I - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, d I = m + 1 := ⟨d I - 1, by omega⟩
    rw [hm]
    simp only [Nat.add_sub_cancel]
    ring
  rw [h2, pow_add, mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]

/-- The exact number of vertices: `d Q` register vertices, `Q - W` vertices of `B_*`,
`|D| = p + |I|` selectors and anchors, `a d n` vertices of test cliques, `|I|` `I`-vertices and
`a (η - n)` vertices of private cliques. -/
theorem card_Vtx (I : MinCSP) :
    Fintype.card (Vtx I) = d I * Q I + (Q I - I.W) + (I.p + numI I) + numA I * (d I * I.n) +
      numI I + numA I * (eta I - I.n) := by
  rw [Fintype.card_congr (Vtx.equivSum I)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_Mat, card_IIdx,
    card_AIdx]
  simp only [numA, Q]
  ring

/-- A clean upper bound on the number of vertices. -/
theorem card_Vtx_le (I : MinCSP) :
    Fintype.card (Vtx I) ≤ (d I + 1) * Q I + I.p + 2 * numI I + numA I * (d I * I.n + eta I) := by
  rw [card_Vtx]
  have h1 : Q I - I.W ≤ Q I := Nat.sub_le _ _
  have h2 : eta I - I.n ≤ eta I := Nat.sub_le _ _
  have h3 : numA I * (eta I - I.n) ≤ numA I * eta I := Nat.mul_le_mul_left _ h2
  nlinarith

/-- `η = Q + p + Σ_C Σ_R Σ_{x ∈ X_C} (n - c_{R,x})`. -/
theorem eta_eq (I : MinCSP) :
    eta I = Q I + I.p + ∑ C, ∑ R : Fin (I.numMini C), ∑ x ∈ I.scope C, (I.n - I.thr C R x) := by
  rw [eta, numI, add_assoc]

/-- The bound `η ≤ Q + p + Σ_C Σ_R Σ_{x ∈ X_C} (n - c_{R,x})` (with equality). -/
theorem eta_le (I : MinCSP) :
    eta I ≤ Q I + I.p + ∑ C, ∑ R : Fin (I.numMini C), ∑ x ∈ I.scope C, (I.n - I.thr C R x) :=
  (eta_eq I).le

end SubspaceConvolution.Counter
