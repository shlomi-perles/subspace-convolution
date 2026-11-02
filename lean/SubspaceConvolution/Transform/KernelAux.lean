/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Algorithm
import SubspaceConvolution.Transform.Incidence
import SubspaceConvolution.Transform.Count
import SubspaceConvolution.Circuit.Arith

/-!
# Auxiliary lemmas for intersection kernels (Theorem 1.4)

* `grassLeEquiv`, `card_grass_inside` — the `j`-dimensional subspaces of `V` inside `S` are
  the `j`-dimensional subspaces of `S`; there are `|Gr(dim S, j)|` of them.
* `sum_grass_le_sum_ge` — the double count behind equations (moments) and (rect-moments).
* `subLESigmaEquiv`, `sum_subLE_eq` — the subspaces of dimension at most `k`, grouped by
  dimension.
* Circuit helpers: `LinCost.scale` (one scaling gate per entry) and `LinCost.empty`
  (maps into an empty table are free).
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

open Circuit

universe u v w

section Counting

variable {K : Type w} [Field K] [Fintype K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {R : Type u} [CommRing R]

/-- The `j`-dimensional subspaces of `V` contained in `S` are the `j`-dimensional subspaces of
`S`. -/
noncomputable def grassLeEquiv (S : Submodule K V) (j : ℕ) :
    {L : Grass K V j // L.1 ≤ S} ≃ Grass K S j where
  toFun L := ⟨Submodule.comap S.subtype L.1.1, by
    rw [← Submodule.finrank_map_subtype_eq S, Submodule.map_comap_subtype, inf_of_le_right L.2]
    exact L.1.2⟩
  invFun L := ⟨⟨Submodule.map S.subtype L.1, by rw [Submodule.finrank_map_subtype_eq]; exact L.2⟩,
    Submodule.map_subtype_le S _⟩
  left_inv L := by
    apply Subtype.ext; apply Subtype.ext
    simp only
    rw [Submodule.map_comap_subtype, inf_of_le_right L.2]
  right_inv L := by
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective S.injective_subtype _

open Classical in
/-- The number of `j`-dimensional subspaces inside `S` is `|Gr(dim S, j)|`. -/
theorem card_grass_inside (S : Submodule K V) (j : ℕ) :
    #(univ.filter fun L : Grass K V j => L.1 ≤ S) = gr K (finrank K S) j := by
  rw [← card_grass (K := K) (V := S) rfl j, ← Fintype.card_subtype]
  exact Fintype.card_congr (grassLeEquiv S j)

open Classical in
/-- **The double count** behind equations (moments) and (rect-moments):
`∑_{L ≤ S, dim L = j} ∑_{W ≥ L} g(W) = ∑_W |Gr(dim(S ∩ W), j)| g(W)`. -/
theorem sum_grass_le_sum_ge {j k : ℕ} (S : Submodule K V) (g : Grass K V k → R) :
    ∑ L ∈ univ.filter (fun L : Grass K V j => L.1 ≤ S),
        ∑ W ∈ univ.filter (fun W : Grass K V k => L.1 ≤ W.1), g W =
      ∑ W : Grass K V k, (gr K (finrank K (S ⊓ W.1 : Submodule K V)) j : R) * g W := by
  rw [Finset.sum_comm' (t' := univ)
    (s' := fun W => univ.filter fun L : Grass K V j => L.1 ≤ S ⊓ W.1)]
  · refine sum_congr rfl fun W _ => ?_
    rw [sum_const, card_grass_inside, nsmul_eq_mul]
  · intro L W
    simp only [mem_filter, mem_univ, true_and, le_inf_iff, and_true]

/-- Subspaces of dimension at most `k`, grouped by their dimension. -/
noncomputable def subLESigmaEquiv (k : ℕ) : (Σ j : Fin (k + 1), Grass K V j) ≃ SubLE K V k where
  toFun p := ⟨p.2.1, p.2.2.le.trans (Nat.lt_succ_iff.mp p.1.2)⟩
  invFun L := ⟨⟨finrank K L.1, Nat.lt_succ_of_le L.2⟩, ⟨L.1, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨j, hj⟩, ⟨L, hL⟩⟩
    obtain rfl : finrank K L = j := hL
    rfl
  right_inv _ := rfl

/-- A sum over the subspaces of dimension at most `k`, grouped by dimension. -/
theorem sum_subLE_eq (k : ℕ) (F : SubLE K V k → R) :
    ∑ L, F L = ∑ j : Fin (k + 1), ∑ L : Grass K V j,
      F ⟨L.1, L.2.le.trans (Nat.lt_succ_iff.mp j.2)⟩ := by
  calc ∑ L, F L = ∑ p : (Σ j : Fin (k + 1), Grass K V j), F (subLESigmaEquiv k p) :=
        (Fintype.sum_equiv (subLESigmaEquiv k) _ _ fun _ => rfl).symm
    _ = _ := Fintype.sum_sigma _

end Counting

/-! ### Circuit helpers -/

namespace Circuit.LinCost

variable {R : Type u} [CommRing R]

/-- Scaling every entry of a table by its own constant: one gate per entry. -/
theorem scale {O : Type*} [Fintype O] (c : O → R) :
    LinCost (Set.univ : Set R) (fun (g : O → R) o => c o * g o) (Fintype.card O) := by
  have h1 : ∀ j : O,
      LinCost (Set.univ : Set R) (fun (g : Unit → R) (_ : Unit) => c j * g ()) 1 := by
    intro j
    have := LinCost.lincomb (C := (Set.univ : Set R)) (O := Unit) (LinCost.id (I := Unit))
      (LinCost.zero (I := Unit) (O := Unit)) (a := c j) (b := 0) trivial trivial
    refine (this.congr ?_).mono (by simp)
    funext g o
    cases o
    simp
  have h2 := LinCost.sigma (C := (Set.univ : Set R)) (ι := O) (I' := fun _ => Unit)
    (O' := fun _ => Unit) (fun j g _ => c j * g ()) (fun _ => 1) h1
  have h3 := h2.reindex (I' := O) (O' := O) (fun p => p.1) (fun o => ⟨o, ()⟩)
  refine (h3.congr ?_).mono (by simp)
  funext g o
  rfl

/-- A map into an empty table costs nothing. -/
theorem empty {C : Set R} {I O : Type*} [IsEmpty O] (M : (I → R) → O → R) (s : ℕ) :
    LinCost C M s := by
  refine (LinCost.zero (C := C) (I := I) (O := O)).congr ?_ |>.mono (Nat.zero_le s)
  funext f o
  exact isEmptyElim o

end Circuit.LinCost

end SubspaceConvolution
