/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.SubspaceCount

/-!
# Proposition 7.3: coloring-completion queries across a cut

Across a cut `(X, V \ X)` of binary cut-rank at most `r`, vertices carry labels
`p_x, q_y ∈ F₂^r` with `xy ∈ E ⇔ p_xᵀ q_y = 1` (`exists_cutLabels`, a rank factorization).
For a named `c`-coloring of either side, the profile of color `i` is the span of the labels of the
vertices of color `i`; unused colors have profile `{0}`.

* `proper_iff_profiles` — two proper colorings of the sides combine into a proper coloring of `G`
  exactly when corresponding profiles are orthogonal ("Named colorings across a binary rank-r cut
  combine exactly when corresponding profiles in `F₂^r` are orthogonal").
* `card_coloring_eq_completionSum` — with `f, g` counting the colorings of the two sides by their ordered
  profile tuples, `∑_U f(U) B_g(U)` counts the proper `c`-colorings of `G`, where
  `B_g(U₁,…,U_c) = ∑_{V_i ≤ U_i^⊥} g(V₁,…,V_c)`.
* `Bg_eq_zetaTensor` — eq. (color-compatibility): `B_g(U) = (Z_r^{⊗c} g)(U₁^⊥, …, U_c^⊥)`.
* `zetaOn_eq_foldr` — `Z^{⊗c}` is obtained by applying the one-dimensional transform in each
  argument, holding the other arguments fixed.
* `completion_cost_le` — the arithmetic of the running time: `c · N^{c-1}` calls of a transform of
  cost `K · N log N` cost `K · S log S` with `S = N^c`.  (The cost bound for one call is the
  paper's Theorem 1.1, which is not part of the coloring results; it enters as the parameter `K`.)
-/

open Finset Module

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

/-! ### Orthogonal complements -/

/-- `U^⊥` for the standard dot product on `F₂^r`. -/
def perp {r : ℕ} (U : Submodule F2 (Fin r → F2)) : Submodule F2 (Fin r → F2) where
  carrier := {v | ∀ u ∈ U, u ⬝ᵥ v = 0}
  add_mem' {a b} ha hb u hu := by
    simp only [Set.mem_ofPred_eq] at ha hb
    rw [dotProduct_add, ha u hu, hb u hu, add_zero]
  zero_mem' u _ := dotProduct_zero u
  smul_mem' c v hv u hu := by
    simp only [Set.mem_ofPred_eq] at hv
    rw [dotProduct_smul, hv u hu, smul_zero]

theorem mem_perp {r : ℕ} {U : Submodule F2 (Fin r → F2)} {v : Fin r → F2} :
    v ∈ perp U ↔ ∀ u ∈ U, u ⬝ᵥ v = 0 := Iff.rfl

/-- Two spans are orthogonal iff their generators are. -/
theorem span_le_perp_span_iff {r : ℕ} {S T : Set (Fin r → F2)} :
    Submodule.span F2 T ≤ perp (Submodule.span F2 S) ↔ ∀ s ∈ S, ∀ t ∈ T, s ⬝ᵥ t = 0 := by
  constructor
  · intro h s hs t ht
    exact h (Submodule.subset_span ht) s (Submodule.subset_span hs)
  · intro h
    rw [Submodule.span_le]
    intro t ht u hu
    induction hu using Submodule.span_induction with
    | mem s hs => exact h s hs t ht
    | zero => exact zero_dotProduct t
    | add a b _ _ ha hb => rw [add_dotProduct, ha, hb, add_zero]
    | smul k a _ ha => rw [smul_dotProduct, ha, smul_zero]

/-! ### Labels from a rank factorization -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Labels across a cut `(X, V \ X)`: `p_x, q_y ∈ F₂^r` with `xy ∈ E ⇔ p_xᵀ q_y = 1`. -/
structure CutLabels (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (r : ℕ) where
  /-- labels of the left side -/
  p : V → Fin r → F2
  /-- labels of the right side -/
  q : V → Fin r → F2
  adj_iff : ∀ x ∈ X, ∀ y ∉ X, G.Adj x y ↔ p x ⬝ᵥ q y = 1

/-- Zero-padding `F₂^d → F₂^r` preserves dot products. -/
def padVec {d r : ℕ} (u : Fin d → F2) : Fin r → F2 :=
  fun i => if h : (i : ℕ) < d then u ⟨i, h⟩ else 0

theorem padVec_dotProduct {d r : ℕ} (hdr : d ≤ r) (u v : Fin d → F2) :
    padVec (r := r) u ⬝ᵥ padVec v = u ⬝ᵥ v := by
  set F : ℕ → F2 := fun n => if h : n < d then u ⟨n, h⟩ * v ⟨n, h⟩ else 0 with hF
  have h1 : padVec (r := r) u ⬝ᵥ padVec v = ∑ i : Fin r, F i := by
    unfold dotProduct padVec
    refine Fintype.sum_congr _ _ fun i => ?_
    by_cases h : (i : ℕ) < d <;> simp [hF, h]
  have h2 : u ⬝ᵥ v = ∑ i : Fin d, F i := by
    unfold dotProduct
    refine Fintype.sum_congr _ _ fun i => ?_
    simp [hF, i.2]
  rw [h1, h2, Fin.sum_univ_eq_sum_range F r, Fin.sum_univ_eq_sum_range F d,
    ← Finset.sum_range_add_sum_Ico F hdr, Finset.sum_eq_zero (s := Finset.Ico d r), add_zero]
  intro n hn
  simp [hF, not_lt.2 (Finset.mem_Ico.1 hn).1]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Labels exist across every cut of binary cut-rank at most `r`** (rank factorization of
`A_G[X, V \ X]`). -/
theorem exists_cutLabels {X : Finset V} {r : ℕ} (h : cutRank G X ≤ r) :
    Nonempty (CutLabels G X r) := by
  classical
  set W := cutSpace (G.adjMatrix F2) X
  set d := finrank F2 W
  have hd : d ≤ r := h
  let b : Basis (Fin d) F2 W := Module.finBasis F2 W
  -- coefficients of the rows in the basis
  let α : V → Fin d → F2 := fun x =>
    if hx : x ∈ X then b.repr ⟨cutRow (G.adjMatrix F2) X x, cutRow_mem_cutSpace hx⟩ else 0
  refine ⟨⟨fun x => padVec (α x), fun y => padVec (fun i => (b i : V → F2) y), ?_⟩⟩
  intro x hx y hy
  rw [padVec_dotProduct hd]
  have hrow : cutRow (G.adjMatrix F2) X x = ∑ i, α x i • (b i : V → F2) := by
    have := b.sum_repr ⟨cutRow (G.adjMatrix F2) X x, cutRow_mem_cutSpace hx⟩
    have := congrArg Subtype.val this
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    simp only [α, dite_eq_left hx]
    exact this.symm
  have hxy : cutRow (G.adjMatrix F2) X x y = ∑ i, α x i * (b i : V → F2) y := by
    rw [hrow, Finset.sum_apply]
    simp
  have hA : G.adjMatrix F2 x y = ∑ i, α x i * (b i : V → F2) y := by
    rw [← hxy, cutRow_apply, ite_eq_right hy]
  unfold dotProduct
  rw [← hA, SimpleGraph.adjMatrix_apply]
  by_cases hadj : G.Adj x y <;> simp [hadj]

/-! ### Combining colorings of the two sides -/

section Combine

variable {G} {X : Finset V} {r : ℕ} (L : CutLabels G X r) (c : ℕ)

/-- The profile of color `i` in a coloring `a` of the left side `X`. -/
def profL (a : {v // v ∈ X} → Fin c) (i : Fin c) : Submodule F2 (Fin r → F2) :=
  Submodule.span F2 ((fun x : {v // v ∈ X} => L.p x) '' {x | a x = i})

/-- The profile of color `i` in a coloring `b` of the right side `V \ X`. -/
def profR (b : {v // v ∉ X} → Fin c) (i : Fin c) : Submodule F2 (Fin r → F2) :=
  Submodule.span F2 ((fun y : {v // v ∉ X} => L.q y) '' {y | b y = i})

variable (G)

/-- Proper colorings of the left side. -/
def ProperL {c : ℕ} (a : {v // v ∈ X} → Fin c) : Prop :=
  ∀ x y : {v // v ∈ X}, G.Adj x y → a x ≠ a y

/-- Proper colorings of the right side. -/
def ProperR {c : ℕ} (b : {v // v ∉ X} → Fin c) : Prop :=
  ∀ x y : {v // v ∉ X}, G.Adj x y → b x ≠ b y

variable {G}

/-- **Colorings of the two sides combine iff corresponding profiles are orthogonal.** -/
theorem proper_iff_profiles (φ : V → Fin c) :
    (∀ ⦃x y⦄, G.Adj x y → φ x ≠ φ y) ↔
      ProperL G (fun x : {v // v ∈ X} => φ x) ∧ ProperR G (fun y : {v // v ∉ X} => φ y) ∧
        ∀ i, profR L c (fun y => φ y) i ≤ perp (profL L c (fun x => φ x) i) := by
  constructor
  · intro h
    refine ⟨fun x y hxy => h hxy, fun x y hxy => h hxy, fun i => ?_⟩
    rw [profR, profL, span_le_perp_span_iff]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [Set.mem_ofPred_eq] at hx hy
    have hnadj : ¬ G.Adj x y := fun hadj => h hadj (hx.trans hy.symm)
    rw [L.adj_iff x x.2 y y.2] at hnadj
    rcases (show ∀ t : F2, t = 0 ∨ t = 1 by decide) (L.p x ⬝ᵥ L.q y) with h0 | h1
    · exact h0
    · exact absurd h1 hnadj
  · rintro ⟨hL, hR, hLR⟩ x y hxy hφ
    by_cases hx : x ∈ X <;> by_cases hy : y ∈ X
    · exact hL ⟨x, hx⟩ ⟨y, hy⟩ hxy hφ
    · have hdot := (span_le_perp_span_iff.1 (hLR (φ x))) _ ⟨⟨x, hx⟩, rfl, rfl⟩ _
        ⟨⟨y, hy⟩, hφ.symm, rfl⟩
      rw [(L.adj_iff x hx y hy).1 hxy] at hdot
      exact one_ne_zero hdot
    · have hdot := (span_le_perp_span_iff.1 (hLR (φ y))) _ ⟨⟨y, hy⟩, rfl, rfl⟩ _
        ⟨⟨x, hx⟩, hφ, rfl⟩
      rw [(L.adj_iff y hy x hx).1 hxy.symm] at hdot
      exact one_ne_zero hdot
    · exact hR ⟨x, hx⟩ ⟨y, hy⟩ hxy hφ

end Combine

/-! ### Counting colorings through the completion sums -/

section Count

noncomputable instance instFintypeSubmoduleF2 (r : ℕ) : Fintype (Submodule F2 (Fin r → F2)) :=
  Fintype.ofFinite _

variable {G} {X : Finset V} {r : ℕ} (L : CutLabels G X r) (c : ℕ)

open Classical in
/-- `f(U)`: the number of proper colorings of the left side with profile tuple `U`. -/
noncomputable def leftCount (U : Fin c → Submodule F2 (Fin r → F2)) : ℕ :=
  #(univ.filter fun a : {v // v ∈ X} → Fin c => ProperL G a ∧ profL L c a = U)

open Classical in
/-- `g(V)`: the number of proper colorings of the right side with profile tuple `V`. -/
noncomputable def rightCount (W : Fin c → Submodule F2 (Fin r → F2)) : ℕ :=
  #(univ.filter fun b : {v // v ∉ X} → Fin c => ProperR G b ∧ profR L c b = W)

open Classical in
/-- The completion sums `B_g(U₁, …, U_c) = ∑_{V_i ≤ U_i^⊥} g(V₁, …, V_c)`. -/
noncomputable def completionSum {R : Type*} [AddCommMonoid R] {c r : ℕ}
    (g : (Fin c → Submodule F2 (Fin r → F2)) → R) (U : Fin c → Submodule F2 (Fin r → F2)) : R :=
  ∑ W ∈ univ.filter (fun W : Fin c → Submodule F2 (Fin r → F2) => ∀ i, W i ≤ perp (U i)), g W

/-- Counting pairs through their profiles: the number of pairs `(a, b)` with `P a`, `Q b` and
compatible profiles is `∑_u #{a | P a, pa a = u} · ∑_{w compatible with u} #{b | Q b, pb b = w}`. -/
theorem card_pairs_eq_sum {A B α β : Type*} [Fintype A] [Fintype B] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (P : A → Prop) (Q : B → Prop) [DecidablePred P]
    [DecidablePred Q] (pa : A → α) (pb : B → β) (C : α → β → Prop)
    [∀ u w, Decidable (C u w)] :
    #(univ.filter fun ab : A × B => P ab.1 ∧ Q ab.2 ∧ C (pa ab.1) (pb ab.2)) =
      ∑ u, #(univ.filter fun a => P a ∧ pa a = u) *
        ∑ w ∈ univ.filter (fun w => C u w), #(univ.filter fun b => Q b ∧ pb b = w) := by
  classical
  have key : ∀ u w, #((univ.filter fun ab : A × B => P ab.1 ∧ Q ab.2 ∧ C (pa ab.1) (pb ab.2)).filter
      fun ab => (pa ab.1, pb ab.2) = (u, w)) =
        if C u w then #(univ.filter fun a => P a ∧ pa a = u) *
          #(univ.filter fun b => Q b ∧ pb b = w) else 0 := by
    intro u w
    split_ifs with hC
    · rw [← card_product]
      congr 1
      ext ⟨a, b⟩
      simp only [mem_filter, mem_univ, true_and, mem_product, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hP, hQ, -⟩, rfl, rfl⟩
        exact ⟨⟨hP, rfl⟩, hQ, rfl⟩
      · rintro ⟨⟨hP, rfl⟩, hQ, rfl⟩
        exact ⟨⟨hP, hQ, hC⟩, rfl, rfl⟩
    · rw [card_eq_zero, filter_eq_empty_iff]
      rintro ⟨a, b⟩ hab hEq
      simp only [mem_filter, mem_univ, true_and] at hab
      simp only [Prod.mk.injEq] at hEq
      obtain ⟨rfl, rfl⟩ := hEq
      exact hC hab.2.2
  rw [card_eq_sum_card_fiberwise (f := fun ab : A × B => (pa ab.1, pb ab.2)) (t := univ)
    (fun _ _ => mem_univ _), ← univ_product_univ, sum_product]
  refine sum_congr rfl fun u _ => ?_
  rw [mul_sum, sum_filter]
  refine sum_congr rfl fun w _ => ?_
  rw [key u w]

open Classical in
/-- **The final sum of Proposition 7.3 counts the proper `c`-colorings of `G`:**
`|{proper c-colorings of G}| = ∑_U f(U) B_g(U)`. -/
theorem card_coloring_eq_completionSum :
    Fintype.card (G.Coloring (Fin c)) =
      ∑ U, leftCount L c U * completionSum (rightCount L c) U := by
  rw [Fintype.card_congr (coloringEquivFun G (Fin c)), Fintype.card_subtype]
  -- split colorings of `V` into colorings of the two sides
  let e := Equiv.piEquivPiSubtypeProd (fun v : V => v ∈ X) (fun _ => Fin c)
  have hcard : #(univ.filter fun φ : V → Fin c => ∀ ⦃x y⦄, G.Adj x y → φ x ≠ φ y) =
      #(univ.filter fun ab : ({v // v ∈ X} → Fin c) × ({v // v ∉ X} → Fin c) =>
        ProperL G ab.1 ∧ ProperR G ab.2 ∧ ∀ i, profR L c ab.2 i ≤ perp (profL L c ab.1 i)) := by
    refine card_bij' (fun φ _ => e φ) (fun ab _ => e.symm ab) ?_ ?_ ?_ ?_
    · intro φ hφ
      simp only [mem_filter, mem_univ, true_and] at hφ ⊢
      exact (proper_iff_profiles L c φ).1 hφ
    · intro ab hab
      simp only [mem_filter, mem_univ, true_and] at hab ⊢
      rw [proper_iff_profiles L c]
      have h1 : (fun x : {v // v ∈ X} => e.symm ab x) = ab.1 := by
        funext x
        simp [e, Equiv.piEquivPiSubtypeProd, x.2]
      have h2 : (fun y : {v // v ∉ X} => e.symm ab y) = ab.2 := by
        funext y
        simp [e, Equiv.piEquivPiSubtypeProd, y.2]
      rw [h1, h2]
      exact hab
    · intro φ _
      exact e.symm_apply_apply φ
    · intro ab _
      exact e.apply_symm_apply ab
  rw [hcard]
  exact card_pairs_eq_sum (ProperL G) (ProperR G) (profL L c) (profR L c)
    (fun U W => ∀ i, W i ≤ perp (U i))

end Count

/-! ### The tensor zeta transform and its coordinatewise evaluation -/

section Zeta

variable {ι S R : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [PartialOrder S]
  [AddCommMonoid R]

open Classical in
/-- The zeta transform in the coordinates `I`: sum over tuples below `W` in the coordinates of `I`
and equal to `W` in the other coordinates.  For `I = univ` this is `Z^{⊗ι}`. -/
noncomputable def zetaOn (I : Finset ι) (g : (ι → S) → R) (W : ι → S) : R :=
  ∑ V ∈ univ.filter (fun V : ι → S => (∀ i ∈ I, V i ≤ W i) ∧ ∀ i ∉ I, V i = W i), g V

open Classical in
/-- The one-dimensional zeta transform in the argument `i`, holding the other arguments fixed. -/
noncomputable def zetaCoord (i : ι) (g : (ι → S) → R) (W : ι → S) : R :=
  ∑ s ∈ univ.filter (· ≤ W i), g (Function.update W i s)

theorem zetaOn_empty (g : (ι → S) → R) : zetaOn ∅ g = g := by
  classical
  funext W
  rw [zetaOn, sum_eq_single W]
  · intro V hV hne
    simp only [mem_filter, mem_univ, true_and, notMem_empty, IsEmpty.forall_iff,
      implies_true, not_false_eq_true, forall_const] at hV
    exact absurd (funext hV) hne
  · intro h
    simp at h

theorem zetaOn_insert {i : ι} {I : Finset ι} (hi : i ∉ I) (g : (ι → S) → R) :
    zetaOn (insert i I) g = zetaCoord i (zetaOn I g) := by
  classical
  funext W
  simp only [zetaCoord, zetaOn]
  rw [← sum_fiberwise_of_maps_to (s := univ.filter fun V : ι → S =>
      (∀ j ∈ insert i I, V j ≤ W j) ∧ ∀ j ∉ insert i I, V j = W j)
    (t := univ.filter (· ≤ W i)) (g := fun V => V i)]
  · refine sum_congr rfl fun s hs => ?_
    apply sum_congr
    · ext V
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · rintro ⟨⟨hle, heq⟩, rfl⟩
        refine ⟨fun j hj => ?_, fun j hj => ?_⟩
        · have hji : j ≠ i := fun h => hi (h ▸ hj)
          rw [Function.update_of_ne hji]
          exact hle j (Or.inr hj)
        · by_cases hji : j = i
          · subst hji
            simp
          · rw [Function.update_of_ne hji]
            exact heq j (by tauto)
      · rintro ⟨hle, heq⟩
        have hVi : V i = s := by
          have := heq i hi
          rwa [Function.update_self] at this
        refine ⟨⟨fun j hj => ?_, fun j hj => ?_⟩, hVi⟩
        · rcases hj with rfl | hj
          · rw [hVi]
            exact (mem_filter.1 hs).2
          · have hji : j ≠ i := fun h => hi (h ▸ hj)
            have := hle j hj
            rwa [Function.update_of_ne hji] at this
        · have hji : j ≠ i := fun h => hj (Or.inl h)
          have := heq j (fun h => hj (Or.inr h))
          rwa [Function.update_of_ne hji] at this
    · intro V _
      rfl
  · intro V hV
    simp only [mem_filter, mem_univ, true_and] at hV ⊢
    exact hV.1 i (mem_insert_self i I)

/-- **`Z^{⊗c}` by coordinatewise transforms**: applying the one-dimensional zeta transform in each
argument in turn (holding the other arguments fixed) computes the transform in all arguments. -/
theorem zetaOn_eq_foldr (g : (ι → S) → R) :
    ∀ l : List ι, l.Nodup → zetaOn l.toFinset g = l.foldr zetaCoord g
  | [], _ => by simp [zetaOn_empty]
  | i :: l, h => by
    obtain ⟨hi, hl⟩ := List.nodup_cons.1 h
    rw [List.toFinset_cons, zetaOn_insert (by simpa using hi), zetaOn_eq_foldr g l hl,
      List.foldr_cons]

theorem zetaOn_univ_eq_foldr (g : (ι → S) → R) :
    zetaOn univ g = (univ : Finset ι).toList.foldr zetaCoord g := by
  rw [← zetaOn_eq_foldr g _ (Finset.nodup_toList _), Finset.toList_toFinset]

end Zeta

open Classical in
/-- **Equation (color-compatibility):** `B_g(U₁,…,U_c) = (Z_r^{⊗c} g)(U₁^⊥, …, U_c^⊥)`. -/
theorem completionSum_eq_zetaOn {R : Type*} [AddCommMonoid R] {c r : ℕ}
    (g : (Fin c → Submodule F2 (Fin r → F2)) → R) (U : Fin c → Submodule F2 (Fin r → F2)) :
    completionSum g U = zetaOn univ g (fun i => perp (U i)) := by
  unfold completionSum zetaOn
  apply sum_congr
  · ext W
    simp
  · intro _ _
    rfl

/-! ### The running-time arithmetic -/

/-- **Running time of Proposition 7.3.**  Applying a one-dimensional transform of cost at most
`K · N log N` along each of the `c` arguments uses `c · N^{c-1}` calls, of total cost at most
`K · S log S` with `S = N^c`; the final inner product `∑_U f(U) B_g(U)` adds `S` multiplications
and `S` additions. -/
theorem completion_cost_le (K : ℝ) (N c : ℕ) (hc : 1 ≤ c) :
    (c * N ^ (c - 1) : ℝ) * (K * N * Real.log N) = K * (N ^ c : ℝ) * Real.log ((N ^ c : ℕ) : ℝ) := by
  push_cast
  rw [Real.log_pow]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
  simp only [Nat.add_sub_cancel_left, pow_add, pow_one]
  push_cast
  ring

end SubspaceConvolution
