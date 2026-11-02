/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.TreeDP

/-!
# Chromatic polynomial and chromatic number from color-partition counts

Paper, Section 7 ("Initialization and output", eq. (chromatic-falling)): with `a_t` the number of
partitions of `V(G)` into `t` nonempty independent sets,

  `P_G(z) = ∑_t a_t (z)_t`,   `(z)_t = z (z - 1) ⋯ (z - t + 1)`,

and the chromatic number is the least `t` with `a_t > 0`.

* `card_coloring_eq_sum` — the number of proper colorings with `z` colors is `∑_t a_t (z)_t`.
* `chromaticPolynomial` — `∑_t a_t · descPochhammer t`; `eval_chromaticPolynomial` — it counts
  proper colorings at every natural number, and `eq_chromaticPolynomial_of_eval` — it is the unique
  integer polynomial doing so.
* `colorable_iff_exists_numColorPartitions_pos`, `chromaticNumber_eq_sInf`.
* `chromaticPolynomial_eq_treeDP`, `chromaticNumber_eq_treeDP` — Theorem 7.1: both are read off
  the output of the rank-decomposition dynamic program.
-/

open Finset

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The partition into color classes -/

/-- The partition of `V` into the nonempty fibers of `f`. -/
def classPartition {α : Type*} [DecidableEq α] (f : V → α) : Finpartition (univ : Finset V) :=
  Finpartition.ofExistsUnique (univ.image fun v => univ.filter fun w => f w = f v)
    (fun _ _ => subset_univ _)
    (fun a _ => ⟨univ.filter fun w => f w = f a, ⟨mem_image_of_mem _ (mem_univ a), by simp⟩,
      fun t ⟨ht, hat⟩ => by
        obtain ⟨v, -, rfl⟩ := mem_image.1 ht
        simp only [mem_filter, mem_univ, true_and] at hat
        ext w
        simp [hat]⟩)
    (by
      simp only [mem_image, mem_univ, true_and, not_exists]
      intro v h
      have : v ∈ univ.filter fun w => f w = f v := by simp
      rw [h] at this
      exact absurd this (notMem_empty v))

theorem classPartition_part {α : Type*} [DecidableEq α] (f : V → α) (v : V) :
    (classPartition f).part v = univ.filter fun w => f w = f v :=
  Finpartition.part_eq_of_mem _
    (by
      simp only [classPartition]
      exact mem_image_of_mem _ (mem_univ v))
    (by simp)

theorem parts_eq_image_part (P : Finpartition (univ : Finset V)) :
    P.parts = univ.image P.part := by
  ext C
  rw [mem_image]
  constructor
  · intro hC
    obtain ⟨v, hv⟩ := P.nonempty_of_mem_parts hC
    exact ⟨v, mem_univ v, P.part_eq_of_mem hC hv⟩
  · rintro ⟨v, -, rfl⟩
    exact P.part_mem.2 (mem_univ v)

theorem classPartition_eq_iff {α : Type*} [DecidableEq α] (f : V → α)
    (P : Finpartition (univ : Finset V)) :
    classPartition f = P ↔ ∀ v, P.part v = univ.filter fun w => f w = f v := by
  constructor
  · rintro rfl v
    exact classPartition_part f v
  · intro h
    apply Finpartition.ext
    rw [parts_eq_image_part (classPartition f), parts_eq_image_part P]
    congr 1
    funext v
    rw [classPartition_part, h]

/-! ### Counting colorings by their color partition -/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem isColorPartition_classPartition {α : Type*} [DecidableEq α] {f : V → α}
    (hf : ∀ ⦃x y⦄, G.Adj x y → f x ≠ f y) : IsColorPartition G (classPartition f) := by
  intro C hC x hx y hy hxy
  have hxC := Finpartition.part_eq_of_mem _ hC hx
  have hyC := Finpartition.part_eq_of_mem _ hC hy
  rw [classPartition_part] at hxC hyC
  have : y ∈ univ.filter fun w => f w = f x := by rw [hxC]; exact hy
  simp only [mem_filter, mem_univ, true_and] at this
  exact hf hxy this.symm

/-- The colorings with a prescribed color partition `P` correspond to injective maps from the
classes of `P` to the colors. -/
theorem card_fiber_classPartition (z : ℕ) {P : Finpartition (univ : Finset V)}
    (hP : IsColorPartition G P) :
    #((univ.filter fun f : V → Fin z => ∀ ⦃x y⦄, G.Adj x y → f x ≠ f y).filter
        fun f => classPartition f = P) = z.descFactorial #P.parts := by
  classical
  have hcard : Fintype.card (P.parts ↪ Fin z) = z.descFactorial #P.parts := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe]
  rw [← hcard, ← card_univ]
  -- representatives of the classes
  have hrep : ∀ C : P.parts, ∃ v, v ∈ (C : Finset V) := fun C =>
    P.nonempty_of_mem_parts C.2
  choose rep hrep using hrep
  have hpart : ∀ C : P.parts, P.part (rep C) = C := fun C => P.part_eq_of_mem C.2 (hrep C)
  refine card_bij' (fun f hf => ⟨fun C => f (rep C), ?_⟩)
    (fun e _ v => e ⟨P.part v, P.part_mem.2 (mem_univ v)⟩) ?_ ?_ ?_ ?_
  · -- injectivity of `C ↦ f (rep C)`
    intro C C' h
    obtain ⟨-, hfP⟩ := mem_filter.1 hf
    rw [classPartition_eq_iff] at hfP
    have : rep C' ∈ P.part (rep C) := by
      rw [hfP]
      simp only [mem_filter, mem_univ, true_and]
      exact h.symm
    rw [hpart C] at this
    exact Subtype.ext (P.eq_of_mem_parts C.2 C'.2 this (hrep C'))
  · intro f hf
    exact mem_univ _
  · intro e _
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨fun x y hxy h => ?_, ?_⟩
    · have := e.injective h
      simp only [Subtype.mk.injEq] at this
      have hy : y ∈ P.part x := by rw [this]; exact P.mem_part_self.2 (mem_univ y)
      exact hP _ (P.part_mem.2 (mem_univ x)) x (P.mem_part_self.2 (mem_univ x)) y hy hxy
    · rw [classPartition_eq_iff]
      intro v
      ext w
      simp only [mem_filter, mem_univ, true_and]
      rw [P.mem_part_iff_part_eq_part (mem_univ w) (mem_univ v)]
      constructor
      · intro h
        simp [h]
      · intro h
        have := e.injective h
        simpa using this
  · intro f hf
    obtain ⟨-, hfP⟩ := mem_filter.1 hf
    rw [classPartition_eq_iff] at hfP
    funext v
    have h1 : rep ⟨P.part v, P.part_mem.2 (mem_univ v)⟩ ∈ P.part v :=
      hrep ⟨P.part v, P.part_mem.2 (mem_univ v)⟩
    have h2 := (Finset.ext_iff.1 (hfP v) _).1 h1
    simp only [mem_filter, mem_univ, true_and] at h2
    exact h2
  · intro e _
    apply Function.Embedding.ext
    intro C
    have hC : (⟨P.part (rep C), P.part_mem.2 (mem_univ _)⟩ : P.parts) = C :=
      Subtype.ext (hpart C)
    show e ⟨P.part (rep C), _⟩ = e C
    rw [hC]

/-- The number of proper colorings with `z` colors, summed over color partitions:
`∑_{P} (z)_{|P|}`. -/
theorem card_coloring_eq_sum_colorParts (z : ℕ) :
    Fintype.card (G.Coloring (Fin z)) = ∑ P ∈ colorParts G univ, z.descFactorial #P.parts := by
  classical
  rw [Fintype.card_congr (coloringEquivFun G (Fin z)), Fintype.card_subtype]
  rw [card_eq_sum_card_fiberwise (f := fun f : V → Fin z => classPartition f)
    (t := colorParts G univ)]
  · refine sum_congr rfl fun P hP => ?_
    exact card_fiber_classPartition G z ((mem_colorParts G).1 hP)
  · intro f hf
    exact (mem_colorParts G).2 (isColorPartition_classPartition G (mem_filter.1 hf).2)

theorem card_parts_le (P : Finpartition (univ : Finset V)) : #P.parts ≤ Fintype.card V := by
  simpa using P.card_parts_le_card

/-- **Equation (chromatic-falling):** the number of proper colorings with `z` colors is
`∑_t a_t (z)_t`. -/
theorem card_coloring_eq_sum (z : ℕ) :
    Fintype.card (G.Coloring (Fin z)) =
      ∑ t ∈ range (Fintype.card V + 1), numColorPartitions G t * z.descFactorial t := by
  rw [card_coloring_eq_sum_colorParts,
    ← sum_fiberwise_of_maps_to (s := colorParts G univ) (t := range (Fintype.card V + 1))
      (g := fun P => #P.parts) (fun P _ => mem_range.2 (Nat.lt_succ_of_le (card_parts_le P)))]
  refine sum_congr rfl fun t _ => ?_
  rw [numColorPartitions, sum_congr rfl (g := fun _ => z.descFactorial t), sum_const, smul_eq_mul]
  intro P hP
  rw [(mem_filter.1 hP).2]

/-! ### The chromatic polynomial -/

/-- The chromatic polynomial `P_G(z) = ∑_t a_t (z)_t` (paper, eq. (chromatic-falling)). -/
noncomputable def chromaticPolynomial : Polynomial ℤ :=
  ∑ t ∈ range (Fintype.card V + 1), (numColorPartitions G t : ℤ) • descPochhammer ℤ t

/-- `P_G(z)` is the number of proper colorings of `G` with `z` colors, for every `z ∈ ℕ`. -/
theorem eval_chromaticPolynomial (z : ℕ) :
    (chromaticPolynomial G).eval (z : ℤ) = Fintype.card (G.Coloring (Fin z)) := by
  rw [chromaticPolynomial, Polynomial.eval_finsetSum, card_coloring_eq_sum]
  push_cast
  refine sum_congr rfl fun t _ => ?_
  rw [Polynomial.eval_smul, descPochhammer_eval_eq_descFactorial, smul_eq_mul]

/-- The chromatic polynomial is the unique integer polynomial counting proper colorings. -/
theorem eq_chromaticPolynomial_of_eval (p : Polynomial ℤ)
    (hp : ∀ z : ℕ, p.eval (z : ℤ) = Fintype.card (G.Coloring (Fin z))) :
    p = chromaticPolynomial G := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℤ)) Nat.cast_injective
  intro z
  simp [hp, eval_chromaticPolynomial]

/-! ### Chromatic number -/

theorem colorable_iff_exists_numColorPartitions_pos (z : ℕ) :
    G.Colorable z ↔ ∃ t ≤ z, 0 < numColorPartitions G t := by
  rw [SimpleGraph.Colorable, ← Fintype.card_pos_iff, card_coloring_eq_sum, sum_pos_iff]
  constructor
  · rintro ⟨t, -, ht⟩
    have h1 := Nat.pos_of_mul_pos_right ht
    have h2 := Nat.pos_of_mul_pos_left ht
    refine ⟨t, ?_, h1⟩
    by_contra h
    rw [Nat.pos_iff_ne_zero, Ne, Nat.descFactorial_eq_zero_iff_lt] at h2
    exact h2 (by omega)
  · rintro ⟨t, htz, ht⟩
    have htV : t ≤ Fintype.card V := by
      obtain ⟨P, hP⟩ := card_pos.1 ht
      rw [(mem_filter.1 hP).2.symm]
      exact card_parts_le P
    refine ⟨t, mem_range.2 (Nat.lt_succ_of_le htV), Nat.mul_pos ht ?_⟩
    rw [Nat.pos_iff_ne_zero, Ne, Nat.descFactorial_eq_zero_iff_lt]
    omega

/-- The discrete partition shows `a_{|V|} > 0`. -/
theorem exists_numColorPartitions_pos : ∃ t, 0 < numColorPartitions G t := by
  obtain ⟨t, -, ht⟩ := (colorable_iff_exists_numColorPartitions_pos G (Fintype.card V)).1
    (SimpleGraph.colorable_of_fintype G)
  exact ⟨t, ht⟩

/-- **The chromatic number is the least `t` with `a_t > 0`.** -/
theorem chromaticNumber_eq_sInf :
    G.chromaticNumber = ((sInf {t | 0 < numColorPartitions G t} : ℕ) : ℕ∞) := by
  rw [(SimpleGraph.colorable_of_fintype G).chromaticNumber_eq_sInf]
  congr 1
  obtain ⟨t₀, ht₀⟩ := exists_numColorPartitions_pos G
  apply le_antisymm
  · apply Nat.sInf_le
    exact (colorable_iff_exists_numColorPartitions_pos G _).2
      ⟨_, le_rfl, Nat.sInf_mem (s := {t | 0 < numColorPartitions G t}) ⟨t₀, ht₀⟩⟩
  · have hm := Nat.sInf_mem (s := {n | G.Colorable n}) ⟨_, SimpleGraph.colorable_of_fintype G⟩
    obtain ⟨t, ht, hpos⟩ := (colorable_iff_exists_numColorPartitions_pos G _).1 hm
    exact (Nat.sInf_le hpos).trans ht

/-! ### Reading the outputs off the dynamic program (Theorem 7.1) -/

/-- **Theorem 7.1 (chromatic polynomial).** The chromatic polynomial is obtained from the output
of the dynamic program on any rank-decomposition. -/
theorem chromaticPolynomial_eq_treeDP (D : RankDecomposition V) :
    chromaticPolynomial G = ∑ t ∈ range (Fintype.card V + 1),
      (((treeDP G D.tree).count (Multiset.replicate t ⊥) : ℕ) : ℤ) • descPochhammer ℤ t := by
  simp only [chromaticPolynomial, count_treeDP_root]

/-- **Theorem 7.1 (chromatic number).** The chromatic number is the least `t` such that the
dynamic program outputs the root histogram `t · δ_{0}` with positive count. -/
theorem chromaticNumber_eq_treeDP (D : RankDecomposition V) :
    G.chromaticNumber =
      ((sInf {t | 0 < (treeDP G D.tree).count (Multiset.replicate t ⊥)} : ℕ) : ℕ∞) := by
  simp only [count_treeDP_root, chromaticNumber_eq_sInf]

end SubspaceConvolution
