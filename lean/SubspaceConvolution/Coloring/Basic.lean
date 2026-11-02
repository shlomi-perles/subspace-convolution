/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import Mathlib

/-!
# Basic definitions

Shared objects for the formalization of the graph-coloring results of
*A Fast Algorithm for Subspace Convolution* (Perles–Weinstein), Section 7 and Appendices C, D.

* `F2` — the field with two elements.
* `cutRow`, `cutSpace`, `matCutRank` — the rows, row space and rank of the cut submatrix
  `M[X, V \ X]` of an `F₂`-matrix `M`; rows are extended by zero to vectors in `F₂^V`.
* `cutRank G X` — the binary cut-rank `ρ_G(X) = rank_{F₂} A_G[X, V(G) \ X]`.
* A toolkit of upper bounds for `matCutRank`: subadditivity, counting rows, counting columns,
  and factorization through `F₂^d`.  These are used for all layout-width bounds.
* `LinearLayout` (vertex orderings) and `LinearLayout.width`.
* `DTree`, `RankDecomposition` (rooted: binary trees whose leaves are the vertices) and its width.
* `IsColorPartition` (partitions into nonempty independent sets) and `profile`.
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

/-- The field with two elements. -/
abbrev F2 : Type := ZMod 2

/-! ## Cut-rank of a matrix and of a graph -/

section CutRank

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Row `x` of the cut submatrix `M[X, V \ X]`, extended by zero on `X` to a vector in `F₂^V`. -/
def cutRow (M : Matrix V V F2) (X : Finset V) (x : V) : V → F2 :=
  fun y => if y ∈ X then 0 else M x y

/-- The row space of `M[X, V \ X]`, as a subspace of `F₂^V`. -/
def cutSpace (M : Matrix V V F2) (X : Finset V) : Submodule F2 (V → F2) :=
  Submodule.span F2 (cutRow M X '' (X : Set V))

/-- The `F₂`-rank of the cut submatrix `M[X, V \ X]`. -/
noncomputable def matCutRank (M : Matrix V V F2) (X : Finset V) : ℕ :=
  finrank F2 (cutSpace M X)

/-- The binary cut-rank `ρ_G(X) = rank_{F₂} A_G[X, V(G) \ X]`. -/
noncomputable def cutRank (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) : ℕ :=
  matCutRank (G.adjMatrix F2) X

variable {M M' : Matrix V V F2} {X : Finset V}

@[simp] theorem cutRow_apply (M : Matrix V V F2) (X : Finset V) (x y : V) :
    cutRow M X x y = if y ∈ X then 0 else M x y := rfl

theorem cutRow_congr (h : ∀ x ∈ X, ∀ y ∉ X, M x y = M' x y) {x : V} (hx : x ∈ X) :
    cutRow M X x = cutRow M' X x := by
  funext y
  simp only [cutRow_apply]
  split_ifs with hy
  · rfl
  · exact h x hx y hy

theorem cutSpace_congr (h : ∀ x ∈ X, ∀ y ∉ X, M x y = M' x y) :
    cutSpace M X = cutSpace M' X := by
  unfold cutSpace
  congr 1
  exact Set.image_congr fun x hx => cutRow_congr h hx

/-- The cut-rank only depends on the entries `M x y` with `x ∈ X`, `y ∉ X`. -/
theorem matCutRank_congr (h : ∀ x ∈ X, ∀ y ∉ X, M x y = M' x y) :
    matCutRank M X = matCutRank M' X := by
  unfold matCutRank
  rw [cutSpace_congr h]

theorem cutRow_mem_cutSpace {x : V} (hx : x ∈ X) : cutRow M X x ∈ cutSpace M X :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem cutSpace_le_iff {S : Submodule F2 (V → F2)} :
    cutSpace M X ≤ S ↔ ∀ x ∈ X, cutRow M X x ∈ S := by
  unfold cutSpace
  rw [Submodule.span_le]
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    exact h x hx

theorem matCutRank_le_of_cutSpace_le {S : Submodule F2 (V → F2)} (h : cutSpace M X ≤ S) :
    matCutRank M X ≤ finrank F2 S :=
  Submodule.finrank_mono h

@[simp] theorem matCutRank_zero (X : Finset V) : matCutRank (0 : Matrix V V F2) X = 0 := by
  have : cutSpace (0 : Matrix V V F2) X = ⊥ := by
    rw [eq_bot_iff, cutSpace_le_iff]
    intro x _
    rw [Submodule.mem_bot]
    funext y
    simp
  simp [matCutRank, this]

@[simp] theorem matCutRank_empty (M : Matrix V V F2) : matCutRank M ∅ = 0 := by
  have : cutSpace M ∅ = ⊥ := by
    rw [eq_bot_iff, cutSpace_le_iff]
    simp
  simp [matCutRank, this]

@[simp] theorem matCutRank_univ (M : Matrix V V F2) : matCutRank M univ = 0 := by
  have : cutSpace M univ = ⊥ := by
    rw [eq_bot_iff, cutSpace_le_iff]
    intro x _
    rw [Submodule.mem_bot]
    funext y
    simp
  simp [matCutRank, this]

theorem cutSpace_add_le : cutSpace (M + M') X ≤ cutSpace M X ⊔ cutSpace M' X := by
  rw [cutSpace_le_iff]
  intro x hx
  have : cutRow (M + M') X x = cutRow M X x + cutRow M' X x := by
    funext y
    simp only [cutRow_apply, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  rw [this]
  exact Submodule.add_mem_sup (cutRow_mem_cutSpace hx) (cutRow_mem_cutSpace hx)

/-- Subadditivity of the cut-rank. -/
theorem matCutRank_add_le : matCutRank (M + M') X ≤ matCutRank M X + matCutRank M' X :=
  (Submodule.finrank_mono cutSpace_add_le).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- Subadditivity of the cut-rank over a finite sum of matrices. -/
theorem matCutRank_sum_le {ι : Type*} (s : Finset ι) (M : ι → Matrix V V F2) (X : Finset V) :
    matCutRank (∑ i ∈ s, M i) X ≤ ∑ i ∈ s, matCutRank (M i) X := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact matCutRank_add_le.trans (by omega)

/-- If all rows of `M[X, V \ X]` lie in a finite set `S` of vectors, the rank is at most `|S|`. -/
theorem matCutRank_le_card_of_mem (S : Finset (V → F2)) (h : ∀ x ∈ X, cutRow M X x ∈ S) :
    matCutRank M X ≤ #S := by
  refine (matCutRank_le_of_cutSpace_le (S := Submodule.span F2 (S : Set (V → F2))) ?_).trans
    (finrank_span_finset_le_card S)
  rw [cutSpace_le_iff]
  intro x hx
  exact Submodule.subset_span (h x hx)

/-- Counting distinct rows: if every row of `M[X, V \ X]` is zero or lies in a finite set `S`,
the rank is at most `|S|`. -/
theorem matCutRank_le_card_of_mem_or_zero (S : Finset (V → F2))
    (h : ∀ x ∈ X, cutRow M X x = 0 ∨ cutRow M X x ∈ S) : matCutRank M X ≤ #S := by
  refine (matCutRank_le_of_cutSpace_le (S := Submodule.span F2 (S : Set (V → F2))) ?_).trans
    (finrank_span_finset_le_card S)
  rw [cutSpace_le_iff]
  intro x hx
  rcases h x hx with h0 | hS
  · rw [h0]
    exact Submodule.zero_mem _
  · exact Submodule.subset_span hS

/-- Counting rows: if every row of `M[X, V \ X]` outside `R` vanishes, the rank is at most `|R|`. -/
theorem matCutRank_le_card_rows (R : Finset V) (h : ∀ x ∈ X, x ∉ R → ∀ y ∉ X, M x y = 0) :
    matCutRank M X ≤ #R := by
  refine (matCutRank_le_of_cutSpace_le
    (S := Submodule.span F2 ((R.image (cutRow M X) : Finset (V → F2)) : Set (V → F2))) ?_).trans
    ((finrank_span_finset_le_card _).trans card_image_le)
  rw [cutSpace_le_iff]
  intro x hx
  by_cases hxR : x ∈ R
  · exact Submodule.subset_span (mem_coe.2 (mem_image_of_mem _ hxR))
  · have : cutRow M X x = 0 := by
      funext y
      simp only [cutRow_apply, Pi.zero_apply]
      split_ifs with hy
      · rfl
      · exact h x hx hxR y hy
    rw [this]
    exact Submodule.zero_mem _

/-- Counting columns: if `M[X, V \ X]` vanishes outside the columns `S`, the rank is at most
`|S|`. -/
theorem matCutRank_le_card_cols (S : Finset V) (h : ∀ x ∈ X, ∀ y ∉ X, y ∉ S → M x y = 0) :
    matCutRank M X ≤ #S := by
  let e : S → (V → F2) := fun y => Pi.single (y : V) 1
  refine (matCutRank_le_of_cutSpace_le (S := Submodule.span F2 (Set.range e)) ?_).trans
    ((finrank_range_le_card e).trans (by simp))
  rw [cutSpace_le_iff]
  intro x hx
  have hrow : cutRow M X x = ∑ y : S, cutRow M X x y • e y := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, e, smul_eq_mul]
    by_cases hz : z ∈ S
    · rw [Finset.sum_eq_single ⟨z, hz⟩]
      · simp
      · rintro ⟨w, hw⟩ _ hne
        have : w ≠ z := fun hwz => hne (Subtype.ext hwz)
        simp [Ne.symm this]
      · simp
    · rw [Finset.sum_eq_zero]
      · simp only [cutRow_apply]
        split_ifs with hzX
        · rfl
        · exact h x hx z hzX hz
      · rintro ⟨w, hw⟩ _
        have : z ≠ w := fun hzw => hz (hzw ▸ hw)
        simp [this]
  rw [hrow]
  exact Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)

/-- Factorization: if `M[X, V \ X] = P Qᵀ` with inner dimension `d`, the rank is at most `d`. -/
theorem matCutRank_le_of_factor {d : ℕ} (p q : V → Fin d → F2)
    (h : ∀ x ∈ X, ∀ y ∉ X, M x y = ∑ i, p x i * q y i) : matCutRank M X ≤ d := by
  let b : Fin d → (V → F2) := fun i y => if y ∈ X then 0 else q y i
  refine (matCutRank_le_of_cutSpace_le (S := Submodule.span F2 (Set.range b)) ?_).trans
    ((finrank_range_le_card b).trans (by simp))
  rw [cutSpace_le_iff]
  intro x hx
  have hrow : cutRow M X x = ∑ i, p x i • b i := by
    funext y
    simp only [cutRow_apply, Finset.sum_apply, Pi.smul_apply, b, smul_eq_mul]
    split_ifs with hy
    · simp
    · rw [h x hx y hy]
  rw [hrow]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The rank of a cut is at most the number of rows. -/
theorem matCutRank_le_card (M : Matrix V V F2) (X : Finset V) : matCutRank M X ≤ #X :=
  matCutRank_le_card_rows X fun _ hx hxX => absurd hx hxX

/-- The rank of a cut is at most the number of columns. -/
theorem matCutRank_le_card_compl (M : Matrix V V F2) (X : Finset V) : matCutRank M X ≤ #Xᶜ :=
  matCutRank_le_card_cols Xᶜ fun _ _ _ hy hyc => absurd (mem_compl.2 hy) hyc

end CutRank

/-! ## Linear layouts -/

/-- A linear layout: an ordering `v₁, …, vₙ` of all vertices. -/
structure LinearLayout (V : Type*) [Fintype V] where
  /-- The vertices, in layout order. -/
  order : List V
  nodup : order.Nodup
  mem_order : ∀ v, v ∈ order

namespace LinearLayout

variable {V : Type*} [Fintype V] [DecidableEq V] (π : LinearLayout V)

/-- The set `{v₁, …, vᵢ}` of the first `i` vertices of the layout. -/
def prefixSet (i : ℕ) : Finset V := (π.order.take i).toFinset

/-- The width `max_i ρ_G({v₁, …, vᵢ})` of a linear layout.  (The prefixes with `i = 0` and
`i = n` have cut-rank `0`, so including them does not change the maximum.) -/
noncomputable def width (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (range (π.order.length + 1)).sup fun i => cutRank G (π.prefixSet i)

theorem prefixSet_of_length_le {i : ℕ} (hi : π.order.length ≤ i) : π.prefixSet i = univ := by
  ext v
  simp [prefixSet, List.take_of_length_le hi, π.mem_order v]

theorem cutRank_prefixSet_le_width (G : SimpleGraph V) [DecidableRel G.Adj] (i : ℕ) :
    cutRank G (π.prefixSet i) ≤ π.width G := by
  by_cases hi : i ≤ π.order.length
  · exact le_sup (f := fun i => cutRank G (π.prefixSet i)) (mem_range.2 (by omega))
  · rw [π.prefixSet_of_length_le (by omega)]
    simp [cutRank]

theorem width_le_iff (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ} :
    π.width G ≤ r ↔ ∀ i, cutRank G (π.prefixSet i) ≤ r := by
  constructor
  · intro h i
    exact (π.cutRank_prefixSet_le_width G i).trans h
  · intro h
    exact Finset.sup_le fun i _ => h i

end LinearLayout

/-! ## Rooted rank-decompositions -/

/-- Rooted binary trees with vertex-labelled leaves. -/
inductive DTree (V : Type*) where
  | leaf : V → DTree V
  | node : DTree V → DTree V → DTree V
  deriving DecidableEq

namespace DTree

variable {V : Type*}

/-- The leaves of a tree, from left to right. -/
def leaves : DTree V → List V
  | leaf v => [v]
  | node l r => l.leaves ++ r.leaves

/-- All subtrees (including the tree itself). -/
def subtrees : DTree V → List (DTree V)
  | leaf v => [leaf v]
  | node l r => node l r :: (l.subtrees ++ r.subtrees)

/-- The set of leaves below a node. -/
def leafSet [DecidableEq V] (t : DTree V) : Finset V := t.leaves.toFinset

theorem self_mem_subtrees (t : DTree V) : t ∈ t.subtrees := by
  cases t <;> simp [subtrees]

end DTree

/-- A (rooted) rank-decomposition: a rooted binary tree whose leaves are in bijection with the
vertices.  Every tree edge corresponds to the subtree below it; the cut it induces is the leaf set
of that subtree.  (Rooting a subcubic tree at a subdivided edge and suppressing degree-two nodes
gives exactly such a tree with the same set of cuts, as in the proof of Theorem 7.1.) -/
structure RankDecomposition (V : Type*) [Fintype V] where
  /-- The underlying rooted binary tree. -/
  tree : DTree V
  nodup : tree.leaves.Nodup
  mem_leaves : ∀ v, v ∈ tree.leaves

namespace RankDecomposition

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The width of a rank-decomposition: the maximum cut-rank of a cut induced by a subtree. -/
noncomputable def width (D : RankDecomposition V) (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (D.tree.subtrees.toFinset).sup fun t => cutRank G t.leafSet

theorem width_le_iff (D : RankDecomposition V) (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ} :
    D.width G ≤ r ↔ ∀ t ∈ D.tree.subtrees, cutRank G t.leafSet ≤ r := by
  simp [width]

end RankDecomposition

/-! ## Color partitions and profiles -/

section ColorPartition

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A *color partition* of `G[X]`: a partition of `X` into nonempty independent sets (the classes
carry no names). -/
def IsColorPartition {X : Finset V} (P : Finpartition X) : Prop :=
  ∀ C ∈ P.parts, ∀ x ∈ C, ∀ y ∈ C, ¬ G.Adj x y

/-- The *profile* `U_X(C)` of a class `C ⊆ X`: the span of the neighborhood vectors
`A_G[x, V \ X]ᵀ`, `x ∈ C` (extended by zero to `F₂^V`). -/
def profile (X C : Finset V) : Submodule F2 (V → F2) :=
  Submodule.span F2 (cutRow (G.adjMatrix F2) X '' (C : Set V))

theorem profile_le_cutSpace {X C : Finset V} (h : C ⊆ X) :
    profile G X C ≤ cutSpace (G.adjMatrix F2) X :=
  Submodule.span_mono (Set.image_mono (by exact_mod_cast h))

/-- Proper colorings with colors in `α` are the same as functions `V → α` that differ on every
edge. -/
def coloringEquivFun (α : Type*) :
    G.Coloring α ≃ {f : V → α // ∀ ⦃x y⦄, G.Adj x y → f x ≠ f y} where
  toFun C := ⟨C, fun _ _ h => C.valid h⟩
  invFun f := SimpleGraph.Coloring.mk f.1 fun h => f.2 h
  left_inv _ := rfl
  right_inv _ := rfl

end ColorPartition

end SubspaceConvolution
