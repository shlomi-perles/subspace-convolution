/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Circuit.SLP

/-!
# Morgenstern's bound (Appendix F)

A linear straight-line program over `ℂ` whose constants have modulus at most one and which
computes a square linear map `M` has at least `log₂ |det M|` gates (main.tex, proof of the
bounded-coefficient lower bound in Appendix F).

Every wire `w` of a program `gs` carries a *coefficient row* `row gs w : I → ℂ`: its values on the
unit vectors.  A gate `z = a x + b y` has row `a • row x + b • row y`, and appending a gate leaves
the rows of all other wires unchanged.  For a choice `σ : I → Wire I` of `|I|` wires consider the
determinant of their rows.  With no gates every such determinant is `0` or `±1`; by
multilinearity a new gate with `|a|, |b| ≤ 1` at most doubles the largest absolute value of such
a determinant (`det_row_le`).  The matrix of `M` is the matrix of the rows of the output wires.
-/

open Finset

namespace SubspaceConvolution.Circuit

namespace MorgensternAux

variable {I : Type*}

section Run

variable {R : Type*} [CommRing R]

theorem run_nil (f : I → R) : run ([] : List (Gate R I)) f = [] := rfl

theorem run_append (gs : List (Gate R I)) (g : Gate R I) (f : I → R) :
    run (gs ++ [g]) f = run gs f ++ [g.eval f (run gs f)] := by
  simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem length_run (gs : List (Gate R I)) (f : I → R) : (run gs f).length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih => simp [run_append, ih]

theorem read_append_old (f : I → R) (vals : List R) (v : R) (w : Wire I)
    (hw : w ≠ .inr vals.length) : read f (vals ++ [v]) w = read f vals w := by
  rcases w with i | k
  · rfl
  · have hk : k ≠ vals.length := fun h => hw (h ▸ rfl)
    simp only [read]
    rcases lt_or_gt_of_ne hk with hk | hk
    · exact List.getD_append _ _ _ _ hk
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem read_append_new (f : I → R) (vals : List R) (v : R) :
    read f (vals ++ [v]) (.inr vals.length) = v := by
  simp only [read]
  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
  rfl

end Run

variable [DecidableEq I]

/-- The coefficient row of a wire: its values on the unit vectors. -/
def row (gs : List (Gate ℂ I)) (w : Wire I) : I → ℂ :=
  fun j => read (Pi.single j 1) (run gs (Pi.single j 1)) w

theorem row_append_new (gs : List (Gate ℂ I)) (g : Gate ℂ I) :
    row (gs ++ [g]) (.inr gs.length) = g.a • row gs g.x + g.b • row gs g.y := by
  funext j
  simp only [row, run_append]
  rw [← length_run gs (Pi.single j 1), read_append_new]
  rfl

theorem row_append_old (gs : List (Gate ℂ I)) (g : Gate ℂ I) (w : Wire I)
    (hw : w ≠ .inr gs.length) : row (gs ++ [g]) w = row gs w := by
  funext j
  simp only [row, run_append]
  exact read_append_old _ _ _ _ (by rwa [length_run])

theorem row_nil_inl (i : I) : row ([] : List (Gate ℂ I)) (.inl i) = Pi.single i 1 := by
  funext j
  simp only [row, read]
  by_cases h : i = j
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (Ne.symm h)]

theorem row_nil_inr (k : ℕ) : row ([] : List (Gate ℂ I)) (.inr k) = 0 := by
  funext j
  simp only [row, read, run_nil, List.getD_nil, Pi.zero_apply]

variable [Fintype I]

/-- With no gates, every determinant of wire rows is `0` or `±1`. -/
theorem det_row_nil_le (σ : I → Wire I) :
    ‖(Matrix.of fun i j => row ([] : List (Gate ℂ I)) (σ i) j).det‖ ≤ 1 := by
  by_cases h : ∃ i k, σ i = .inr k
  · obtain ⟨i, k, hik⟩ := h
    rw [Matrix.det_eq_zero_of_row_eq_zero i (fun j => by simp [hik, row_nil_inr])]
    simp
  · push Not at h
    have hl : ∀ i, ∃ k, σ i = .inl k := by
      intro i
      rcases hσ : σ i with k | k
      · exact ⟨k, rfl⟩
      · exact absurd hσ (h i k)
    choose τ hτ using hl
    have hA : (Matrix.of fun i j => row ([] : List (Gate ℂ I)) (σ i) j) =
        (1 : Matrix I I ℂ).submatrix τ id := by
      ext i j
      simp only [Matrix.of_apply, hτ, row_nil_inl, Matrix.submatrix_apply, id, Matrix.one_apply,
        Pi.single_apply]
      exact if_congr eq_comm rfl rfl
    by_cases hinj : Function.Injective τ
    · have hbij : Function.Bijective τ := hinj.bijective_of_finite
      have hp : (1 : Matrix I I ℂ).submatrix τ id =
          (1 : Matrix I I ℂ).submatrix (Equiv.ofBijective τ hbij) id := rfl
      rw [hA, hp, Matrix.det_permute, Matrix.det_one, mul_one]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.ofBijective τ hbij)) with h1 | h1 <;>
        simp [h1]
    · obtain ⟨i, i', heq, hne⟩ := Function.not_injective_iff.mp hinj
      have hσ : σ i = σ i' := by rw [hτ, hτ, heq]
      rw [Matrix.det_zero_of_row_eq hne (by ext j; simp [hσ])]
      simp

/-- **The doubling argument.**  After `t` gates with constants of modulus at most one, every
determinant formed from `|I|` wire rows has absolute value at most `2 ^ t`. -/
theorem det_row_le (gs : List (Gate ℂ I))
    (hC : ∀ g ∈ gs, g.a ∈ Metric.closedBall (0 : ℂ) 1 ∧ g.b ∈ Metric.closedBall (0 : ℂ) 1)
    (σ : I → Wire I) :
    ‖(Matrix.of fun i j => row gs (σ i) j).det‖ ≤ 2 ^ gs.length := by
  induction gs using List.reverseRecOn generalizing σ with
  | nil => simpa using det_row_nil_le σ
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hC g' (List.mem_append_left _ hg'))
    have hg := hC g (List.mem_append_right _ (List.mem_singleton_self g))
    rw [mem_closedBall_zero_iff, mem_closedBall_zero_iff] at hg
    have hpos : (0 : ℝ) ≤ 2 ^ gs.length := by positivity
    rw [List.length_append, List.length_singleton, pow_succ]
    by_cases h1 : ∃ i₀, σ i₀ = .inr gs.length
    · obtain ⟨i₀, hi₀⟩ := h1
      by_cases h2 : ∃ i₁, i₁ ≠ i₀ ∧ σ i₁ = .inr gs.length
      · obtain ⟨i₁, hne, hi₁⟩ := h2
        rw [Matrix.det_zero_of_row_eq hne (by ext j; simp [hi₀, hi₁])]
        simp only [norm_zero]
        positivity
      · push Not at h2
        set B : Matrix I I ℂ := Matrix.of fun i j => row gs (σ i) j with hB
        have hA : (Matrix.of fun i j => row (gs ++ [g]) (σ i) j) =
            B.updateRow i₀ (g.a • row gs g.x + g.b • row gs g.y) := by
          ext i j
          by_cases hi : i = i₀
          · subst hi
            simp [Matrix.updateRow_self, hi₀, row_append_new]
          · simp [hi, row_append_old _ _ _ (h2 i hi), hB]
        have hupd : ∀ w : Wire I, B.updateRow i₀ (row gs w) =
            Matrix.of fun i j => row gs (Function.update σ i₀ w i) j := by
          intro w
          ext i j
          by_cases hi : i = i₀
          · subst hi
            simp
          · simp [hi, hB]
        rw [hA, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.det_updateRow_smul,
          hupd, hupd]
        have hx := ih' (Function.update σ i₀ g.x)
        have hy := ih' (Function.update σ i₀ g.y)
        calc ‖g.a * (Matrix.of fun i j => row gs (Function.update σ i₀ g.x i) j).det +
              g.b * (Matrix.of fun i j => row gs (Function.update σ i₀ g.y i) j).det‖
            ≤ ‖g.a‖ * ‖(Matrix.of fun i j => row gs (Function.update σ i₀ g.x i) j).det‖ +
              ‖g.b‖ * ‖(Matrix.of fun i j => row gs (Function.update σ i₀ g.y i) j).det‖ := by
              rw [← norm_mul, ← norm_mul]
              exact norm_add_le _ _
          _ ≤ 1 * 2 ^ gs.length + 1 * 2 ^ gs.length := by
              gcongr
              · exact hg.1
              · exact hg.2
          _ = 2 ^ gs.length * 2 := by ring
    · push Not at h1
      have hA : (Matrix.of fun i j => row (gs ++ [g]) (σ i) j) =
          Matrix.of fun i j => row gs (σ i) j := by
        ext i j
        simp [row_append_old _ _ _ (h1 i)]
      rw [hA]
      calc _ ≤ 2 ^ gs.length := ih' σ
        _ ≤ 2 ^ gs.length * 2 := by linarith

end MorgensternAux

/-- **Morgenstern's bound** (Appendix F): a program over `ℂ` with constants of modulus at most one,
computing a square linear map, has at least `log₂ |det|` gates. -/
theorem morgenstern {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] (e : O ≃ I)
    {M : (I → ℂ) → O → ℂ} {s : ℕ} (h : LinCost (Metric.closedBall (0 : ℂ) 1) M s) :
    ‖(Matrix.of fun i j : I => M (Pi.single j 1) (e.symm i)).det‖ ≤ 2 ^ s := by
  obtain ⟨P, hs, hC, rfl⟩ := h
  exact (MorgensternAux.det_row_le P.gates hC (fun i => P.out (e.symm i))).trans
    (pow_le_pow_right₀ (by norm_num) hs)

end SubspaceConvolution.Circuit
