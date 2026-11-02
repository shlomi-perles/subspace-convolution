/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.FixedPalette.Defs

/-!
# Padding a general 3-CNF formula onto the grid

A 3-CNF formula on `n` variables (`CNF n`, each clause three literal occurrences
`(variable, sign)`) is placed on a `k × k` grid with `n ≤ k²` by sending variable `v` to
`(v / k, v % k)`.  The grid formula has the same clauses; the `k² - n` unused grid variables are
free, so the number of satisfying assignments is multiplied by `2^{k² - n}` (`numSat_toGrid`), and
satisfiability is preserved (`satisfiable_toGrid_iff`).
-/

namespace SubspaceConvolution.FixedPalette

variable {n : ℕ}

/-- A 3-CNF formula on the variables `Fin n`: each clause has three literal occurrences
`(variable, sign)` (`true` for a positive literal). -/
structure CNF (n : ℕ) where
  m : ℕ
  clause : Fin m → Fin 3 → Fin n × Bool

/-- The value of a literal `(v, s)` under an assignment `β`. -/
def evalLit (β : Fin n → Bool) (l : Fin n × Bool) : Bool :=
  if l.2 then β l.1 else !(β l.1)

def CNF.Satisfies (φ : CNF n) (β : Fin n → Bool) : Prop :=
  ∀ i, ∃ t, evalLit β (φ.clause i t) = true

instance (φ : CNF n) : DecidablePred φ.Satisfies := fun β => by
  unfold CNF.Satisfies
  infer_instance

/-- The number of satisfying assignments. -/
noncomputable def CNF.numSat (φ : CNF n) : ℕ :=
  Fintype.card {β : Fin n → Bool // φ.Satisfies β}

theorem pos_of_lt_mul {v k : ℕ} (h : v < k * k) : 0 < k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp at h
  · exact hk

/-- The grid position `(v / k, v % k)` of a variable `v < n ≤ k²`. -/
def gridPos (k : ℕ) (h : n ≤ k * k) (v : Fin n) : Fin k × Fin k :=
  (⟨v / k, (Nat.div_lt_iff_lt_mul (pos_of_lt_mul (lt_of_lt_of_le v.isLt h))).2
      (lt_of_lt_of_le v.isLt h)⟩,
   ⟨v % k, Nat.mod_lt _ (pos_of_lt_mul (lt_of_lt_of_le v.isLt h))⟩)

/-- The formula `φ` placed on the `k × k` grid. -/
def CNF.toGrid (φ : CNF n) (k : ℕ) (h : n ≤ k * k) : GridCNF k where
  m := φ.m
  clause i t := ⟨(gridPos k h (φ.clause i t).1).1, (gridPos k h (φ.clause i t).1).2,
    (φ.clause i t).2⟩

/-- The assignment of the original variables read off a grid assignment. -/
def restrictGrid (k : ℕ) (h : n ≤ k * k) (α : Fin k → Fin k → Bool) : Fin n → Bool :=
  fun v => α (gridPos k h v).1 (gridPos k h v).2

theorem satisfies_toGrid_iff (φ : CNF n) (k : ℕ) (h : n ≤ k * k) (α : Fin k → Fin k → Bool) :
    (φ.toGrid k h).Satisfies α ↔ φ.Satisfies (restrictGrid k h α) := Iff.rfl

theorem mul_add_lt_sq {a b k : ℕ} (ha : a < k) (hb : b < k) : a * k + b < k * k := by
  have : (a + 1) * k ≤ k * k := Nat.mul_le_mul_right k ha
  rw [Nat.add_mul, one_mul] at this
  omega

theorem grid_div {a b k : ℕ} (hb : b < k) : (a * k + b) / k = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < k), Nat.div_eq_of_lt hb, zero_add]

theorem grid_mod {a b k : ℕ} (hb : b < k) : (a * k + b) % k = b := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

/-- The grid position of the `j`-th padding variable (grid index `n + j`). -/
def padPos (k : ℕ) (h : n ≤ k * k) (j : Fin (k * k - n)) : Fin k × Fin k :=
  have hj : n + j.val < k * k := by have := j.isLt; omega
  (⟨(n + j) / k, (Nat.div_lt_iff_lt_mul (pos_of_lt_mul hj)).2 hj⟩,
   ⟨(n + j) % k, Nat.mod_lt _ (pos_of_lt_mul hj)⟩)

/-- The grid assignment with original part `x.1` and padding part `x.2`. -/
def joinAsg (k : ℕ) (x : (Fin n → Bool) × (Fin (k * k - n) → Bool)) (a b : Fin k) : Bool :=
  if hx : a.val * k + b.val < n then x.1 ⟨a.val * k + b.val, hx⟩
  else x.2 ⟨a.val * k + b.val - n, by have := mul_add_lt_sq a.isLt b.isLt; omega⟩

theorem joinAsg_gridPos (k : ℕ) (h : n ≤ k * k) (x : (Fin n → Bool) × (Fin (k * k - n) → Bool))
    (v : Fin n) : joinAsg k x (gridPos k h v).1 (gridPos k h v).2 = x.1 v := by
  have hv : (gridPos k h v).1.val * k + (gridPos k h v).2.val = v.val := Nat.div_add_mod' v k
  unfold joinAsg
  split_ifs with hx
  · exact congrArg x.1 (Fin.ext hv)
  · exact absurd (hv ▸ v.isLt) hx

theorem joinAsg_padPos (k : ℕ) (h : n ≤ k * k) (x : (Fin n → Bool) × (Fin (k * k - n) → Bool))
    (j : Fin (k * k - n)) : joinAsg k x (padPos k h j).1 (padPos k h j).2 = x.2 j := by
  have hv : (padPos k h j).1.val * k + (padPos k h j).2.val = n + j.val :=
    Nat.div_add_mod' (n + j.val) k
  unfold joinAsg
  split_ifs with hx
  · omega
  · exact congrArg x.2 (Fin.ext (by simp only; omega))

/-- Grid assignments split into an assignment of the original variables and of the `k² - n`
padding variables. -/
def gridSplit (k : ℕ) (h : n ≤ k * k) :
    (Fin k → Fin k → Bool) ≃ (Fin n → Bool) × (Fin (k * k - n) → Bool) where
  toFun α := (restrictGrid k h α, fun j => α (padPos k h j).1 (padPos k h j).2)
  invFun x := joinAsg k x
  left_inv α := by
    funext a b
    have hb := b.isLt
    show joinAsg k (restrictGrid k h α, fun j => α (padPos k h j).1 (padPos k h j).2) a b = α a b
    unfold joinAsg
    split_ifs with hx
    · simp only [restrictGrid, gridPos]
      congr 1
      · exact Fin.ext (grid_div hb)
      · exact Fin.ext (grid_mod hb)
    · simp only [padPos]
      have : n + (a * k + b - n) = a * k + b := by omega
      congr 1
      · exact Fin.ext (by simp only [this]; exact grid_div hb)
      · exact Fin.ext (by simp only [this]; exact grid_mod hb)
  right_inv x := by
    obtain ⟨β, γ⟩ := x
    ext v
    · exact joinAsg_gridPos k h (β, γ) v
    · exact joinAsg_padPos k h (β, γ) v

/-- **Padding**: the grid formula has `2^{k² - n}` times as many satisfying assignments. -/
theorem numSat_toGrid (φ : CNF n) (k : ℕ) (h : n ≤ k * k) :
    (φ.toGrid k h).numSat = 2 ^ (k * k - n) * φ.numSat := by
  unfold GridCNF.numSat CNF.numSat
  have e : {α : Fin k → Fin k → Bool // (φ.toGrid k h).Satisfies α} ≃
      {β : Fin n → Bool // φ.Satisfies β} × (Fin (k * k - n) → Bool) :=
    (Equiv.subtypeEquiv (gridSplit k h) fun α => satisfies_toGrid_iff φ k h α).trans
      Equiv.prodSubtypeFstEquivSubtypeProd
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, mul_comm]

/-- **Padding**: the grid formula is satisfiable iff the original formula is. -/
theorem satisfiable_toGrid_iff (φ : CNF n) (k : ℕ) (h : n ≤ k * k) :
    (∃ α, (φ.toGrid k h).Satisfies α) ↔ ∃ β, φ.Satisfies β := by
  constructor
  · rintro ⟨α, hα⟩
    exact ⟨_, (satisfies_toGrid_iff φ k h α).1 hα⟩
  · rintro ⟨β, hβ⟩
    refine ⟨(gridSplit k h).symm (β, fun _ => false), ?_⟩
    rw [satisfies_toGrid_iff]
    have : restrictGrid k h ((gridSplit k h).symm (β, fun _ => false)) = β :=
      congrArg Prod.fst ((gridSplit k h).apply_symm_apply (β, fun _ => false))
    rw [this]
    exact hβ

end SubspaceConvolution.FixedPalette
