/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.FixedPalette.Core

/-!
# Counting the three-colorings of `G_φ`

The identity (cnt:identity) of the paper:
`#3-Color(G_φ) = 6 · 2^g · 16^m · #SAT(φ)` with `g = 2k + 3m` groups, for `k ≥ 1`.
-/

namespace SubspaceConvolution.FixedPalette

open Finset

variable {k : ℕ}

theorem card_grp (k m : ℕ) : Fintype.card (Grp k m) = 2 * k + 3 * m := by
  let e : Grp k m ≃ Fin k ⊕ Fin k ⊕ (Fin m × Fin 3) :=
    { toFun := fun γ => match γ with
        | .colB h => .inl h
        | .rowA j => .inr (.inl j)
        | .loc i t => .inr (.inr (i, t))
      invFun := fun x => match x with
        | .inl h => .colB h
        | .inr (.inl j) => .rowA j
        | .inr (.inr (i, t)) => .loc i t
      left_inv := fun γ => by cases γ <;> rfl
      right_inv := fun x => by rcases x with h | j | ⟨i, t⟩ <;> rfl }
  rw [Fintype.card_congr e]
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod]
  ring

/-- The number of vertices: `3 + g (2^{k+1} + 1) + 20 m` with `g = 2k + 3m` groups. -/
theorem card_vtx (k m : ℕ) :
    Fintype.card (Vtx k m) = 3 + (2 * k + 3 * m) * (2 ^ (k + 1) + 1) + 20 * m := by
  let e : Vtx k m ≃ Fin 3 ⊕ (Grp k m × Fin (2 ^ k)) ⊕ (Grp k m × Fin (2 ^ k + 1)) ⊕
      (Fin m × Fin 3 × Bool) ⊕ (Fin m × Bool) ⊕ (Fin m × Fin 4 × Fin 3) :=
    { toFun := fun v => match v with
        | .pal a => .inl a
        | .inp γ p => .inr (.inl (γ, p))
        | .cyc γ i => .inr (.inr (.inl (γ, i)))
        | .lit i t b => .inr (.inr (.inr (.inl (i, t, b))))
        | .sig i b => .inr (.inr (.inr (.inr (.inl (i, b)))))
        | .tri i q r => .inr (.inr (.inr (.inr (.inr (i, q, r)))))
      invFun := fun x => match x with
        | .inl a => .pal a
        | .inr (.inl (γ, p)) => .inp γ p
        | .inr (.inr (.inl (γ, i))) => .cyc γ i
        | .inr (.inr (.inr (.inl (i, t, b)))) => .lit i t b
        | .inr (.inr (.inr (.inr (.inl (i, b))))) => .sig i b
        | .inr (.inr (.inr (.inr (.inr (i, q, r))))) => .tri i q r
      left_inv := fun v => by cases v <;> rfl
      right_inv := fun x => by
        rcases x with a | ⟨γ, p⟩ | ⟨γ, i⟩ | ⟨i, t, b⟩ | ⟨i, b⟩ | ⟨i, q, r⟩ <;> rfl }
  rw [Fintype.card_congr e]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, card_grp]
  ring

theorem even_two_pow (hk : 1 ≤ k) : Even (2 ^ k) :=
  Nat.even_pow.2 ⟨even_two, by omega⟩

theorem falseCol_ne_zero {m : ℕ} (γ : Grp k m) : γ.falseCol ≠ 0 := by
  cases γ <;> simp [Grp.falseCol]

theorem eq_zero_or_falseCol {m : ℕ} (γ : Grp k m) (x : Fin 3) (hx : x ≠ γ.forbCol) :
    x = 0 ∨ x = γ.falseCol := by
  cases γ <;> fin_cases x <;> simp_all [Grp.forbCol, Grp.falseCol]

/-- Every cycle of a core coloring coming from an assignment has exactly two extensions. -/
theorem card_cyc_core (hk : 1 ≤ k) (φ : GridCNF k) (α : Fin k → Fin k → Bool)
    (σ : Fin φ.m → Bool) (γ : Grp k φ.m) :
    Nat.card {v // CycOK (core φ α σ) γ v} = 2 := by
  refine cycle_card_two (even_two_pow hk) Nat.one_le_two_pow γ.falseCol (falseCol_ne_zero γ)
    ((core φ α σ).1 γ) ((asg k).symm (selAsg φ α γ)) ?_ ?_
  · simp [core]
  · intro p hp
    have : asg k p ≠ selAsg φ α γ := fun h => hp (by rw [← h]; simp)
    simp [core, this]

/-! ### The clause gadget -/

/-- The color of a signal with truth value `b`: `T = 0` if true, `F_B = 2` if false. -/
def sc (b : Bool) : Fin 3 := if b then 0 else 2

/-- The terminal colors of the four NAE triangles of a clause whose literals have values
`a, b, c`, with clause signal `s`. -/
def termColors (a b c s : Bool) : Fin 4 → Fin 3 → Fin 3 :=
  ![![sc (!a), sc s, 2], ![sc (!b), sc s, 2], ![sc a, sc b, sc (!s)], ![sc s, sc c, 2]]

/-- The number of extensions of an NAE triangle with terminal colors `a`. -/
def naeV (a : Fin 3 → Fin 3) : ℕ := if a 0 = a 1 ∧ a 1 = a 2 then 0 else 2

/-- The clause gadget: summed over the signal `s`, the four NAE triangles have `16` extensions if
the clause is satisfied and none otherwise (`s = a ∨ b` is forced). -/
theorem clause_sum : ∀ a b c : Bool,
    ∑ s : Bool, ∏ q : Fin 4, naeV (termColors a b c s q) =
      if (a || b || c) = true then 16 else 0 := by
  decide

theorem coreVal_term (φ : GridCNF k) (α : Fin k → Fin k → Bool) (σ : Fin φ.m → Bool)
    (i : Fin φ.m) (q : Fin 4) (r : Fin 3) :
    coreVal (core φ α σ) (term i q r) =
      termColors ((φ.clause i 0).eval α) ((φ.clause i 1).eval α) ((φ.clause i 2).eval α) (σ i)
        q r := by
  fin_cases q <;> fin_cases r <;> simp [term, coreVal, core, termColors, sc]

theorem card_tri_core (φ : GridCNF k) (α : Fin k → Fin k → Bool) (σ : Fin φ.m → Bool)
    (iq : Fin φ.m × Fin 4) :
    Nat.card {z // TriOK (core φ α σ) iq z} =
      naeV (termColors ((φ.clause iq.1 0).eval α) ((φ.clause iq.1 1).eval α)
        ((φ.clause iq.1 2).eval α) (σ iq.1) iq.2) := by
  unfold TriOK naeV
  simp only [coreVal_term]
  exact nae_card _

theorem satisfies_iff (φ : GridCNF k) (α : Fin k → Fin k → Bool) :
    φ.Satisfies α ↔
      ∀ i, ((φ.clause i 0).eval α || (φ.clause i 1).eval α || (φ.clause i 2).eval α) = true := by
  unfold GridCNF.Satisfies
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨t, ht⟩
    fin_cases t <;> simp_all
  · intro h
    simp only [Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩

/-- The fiber over `core φ α σ`. -/
theorem card_fiber_core (hk : 1 ≤ k) (φ : GridCNF k) (α : Fin k → Fin k → Bool)
    (σ : Fin φ.m → Bool) :
    Nat.card (Fiber φ (core φ α σ)) =
      2 ^ (2 * k + 3 * φ.m) * ∏ i, ∏ q : Fin 4,
        naeV (termColors ((φ.clause i 0).eval α) ((φ.clause i 1).eval α)
          ((φ.clause i 2).eval α) (σ i) q) := by
  rw [card_fiber (core_ok φ α σ)]
  simp only [card_cyc_core hk, card_tri_core, prod_const, card_univ, card_grp]
  rw [Fintype.prod_prod_type]

/-- Normalized colorings: `2^g · 16^m · #SAT(φ)`. -/
theorem card_normCol_eq (hk : 1 ≤ k) (φ : GridCNF k) :
    Nat.card (NormCol φ) = 2 ^ (2 * k + 3 * φ.m) * 16 ^ φ.m * φ.numSat := by
  classical
  rw [card_normCol]
  -- only core colorings coming from assignments contribute
  have hsub : ∑ c, Nat.card (Fiber φ c) =
      ∑ c ∈ univ.image (fun x : (Fin k → Fin k → Bool) × (Fin φ.m → Bool) => core φ x.1 x.2),
        Nat.card (Fiber φ c) := by
    symm
    apply sum_subset (subset_univ _)
    intro c _ hc
    by_contra hne
    obtain ⟨⟨x, hcore, hcyc, -⟩⟩ := (Nat.card_ne_zero.1 hne).1
    obtain ⟨α, σ, rfl⟩ := exists_core hcore fun γ =>
      cycle_exists_sel (even_two_pow hk) γ.falseCol (c.1 γ)
        (fun p => eq_zero_or_falseCol γ _ (hcore.inp_forb γ p)) (x.1 γ) (hcyc γ)
    exact hc (mem_image_of_mem _ (mem_univ (α, σ)))
  rw [hsub, sum_image (fun x _ y _ h => core_injective φ h), Fintype.sum_prod_type]
  simp only [card_fiber_core hk]
  -- sum over the clause signals clause by clause
  have hσ : ∀ α : Fin k → Fin k → Bool,
      ∑ σ : Fin φ.m → Bool, ∏ i, ∏ q : Fin 4,
        naeV (termColors ((φ.clause i 0).eval α) ((φ.clause i 1).eval α)
          ((φ.clause i 2).eval α) (σ i) q) =
      if φ.Satisfies α then 16 ^ φ.m else 0 := by
    intro α
    rw [← Fintype.prod_sum (fun i (s : Bool) => ∏ q : Fin 4,
        naeV (termColors ((φ.clause i 0).eval α) ((φ.clause i 1).eval α)
          ((φ.clause i 2).eval α) s q))]
    simp only [clause_sum, Fintype.prod_ite_zero, prod_const, card_univ, Fintype.card_fin]
    simp only [satisfies_iff]
  simp only [← mul_sum, hσ]
  rw [sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul, GridCNF.numSat,
    Fintype.card_subtype]
  ring

/-- **Counting identity** (paper eq. (cnt:identity)). -/
theorem card_coloring (hk : 1 ≤ k) (φ : GridCNF k) :
    Fintype.card ((graph φ).Coloring (Fin 3)) =
      6 * 2 ^ (2 * k + 3 * φ.m) * 16 ^ φ.m * φ.numSat := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (coloringEquivFun (graph φ) (Fin 3))]
  have e : {f : Vtx k φ.m → Fin 3 // ∀ ⦃x y⦄, (graph φ).Adj x y → f x ≠ f y} ≃ ProperCol φ :=
    Equiv.subtypeEquivRight fun f => ⟨fun h x z => @h x z, fun h x z => h x z⟩
  rw [Nat.card_congr e, card_properCol, card_normCol_eq hk]
  ring

/-- **Decision**: `G_φ` is three-colorable iff `φ` is satisfiable. -/
theorem colorable_iff (hk : 1 ≤ k) (φ : GridCNF k) :
    (graph φ).Colorable 3 ↔ ∃ α, φ.Satisfies α := by
  have h1 : (graph φ).Colorable 3 ↔ 0 < Fintype.card ((graph φ).Coloring (Fin 3)) := by
    rw [Fintype.card_pos_iff]
    rfl
  have h2 : (∃ α, φ.Satisfies α) ↔ 0 < φ.numSat := by
    rw [GridCNF.numSat, Fintype.card_pos_iff]
    exact ⟨fun ⟨α, h⟩ => ⟨⟨α, h⟩⟩, fun ⟨⟨α, h⟩⟩ => ⟨α, h⟩⟩
  rw [h1, h2, card_coloring hk]
  constructor
  · intro h
    exact Nat.pos_of_ne_zero fun h0 => by simp [h0] at h
  · intro h
    positivity

end SubspaceConvolution.FixedPalette
