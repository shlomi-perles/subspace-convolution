/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.Basic

/-!
# Gadget lemmas for the fixed-palette reduction

* Odd cycles with list constraints (`odd_cycle_avoid`, `cycle_exists_sel`, `cycle_card_two`):
  a cycle `w_0 w_1 ⋯ w_t w_0` of odd length `t + 1`, with `w_0` avoiding the false color `F`
  and `w_{p+1}` avoiding the color of the input `x_{p+1} ∈ {T, F}` (`T = 0`), has no proper
  3-coloring when no input is selected and exactly two when exactly one input is selected.
* NAE triangles (`nae_card`): a triangle whose vertices avoid the colors `a 0, a 1, a 2` of
  their terminals has no proper coloring if the terminals have equal colors and exactly two
  otherwise.
-/

namespace SubspaceConvolution.FixedPalette

/-! ## Three colors -/

/-- The third color. -/
def third (a b : Fin 3) : Fin 3 := -(a + b)

theorem third_ne_left : ∀ a b : Fin 3, a ≠ b → third a b ≠ a := by decide

theorem third_ne_right : ∀ a b : Fin 3, a ≠ b → third a b ≠ b := by decide

theorem eq_third : ∀ a b c : Fin 3, a ≠ b → c ≠ a → c ≠ b → c = third a b := by decide

theorem third_third : ∀ a b : Fin 3, a ≠ b → third (third a b) b = a := by decide

/-! ## Odd cycles -/

section Cycle

variable {t : ℕ}

theorem two_color_period' : ∀ a b c d : Fin 3, (a ≠ d ∧ b ≠ d ∧ c ≠ d ∧ a ≠ b ∧ b ≠ c) → c = a := by
  decide

theorem two_color_period (a b c d : Fin 3) (h1 : a ≠ d) (h2 : b ≠ d) (h3 : c ≠ d) (h4 : a ≠ b)
    (h5 : b ≠ c) : c = a :=
  two_color_period' a b c d ⟨h1, h2, h3, h4, h5⟩

theorem ofNat_succ_fin (j : ℕ) : Fin.ofNat (t + 1) (j + 1) = Fin.ofNat (t + 1) j + 1 := by
  ext
  simp [Fin.val_add, Nat.add_mod]

theorem ofNat_self_fin : Fin.ofNat (t + 1) (t + 1) = 0 := by
  ext
  simp

theorem ofNat_val_fin (i : Fin (t + 1)) : Fin.ofNat (t + 1) i.val = i := by
  ext
  simp

/-- An odd cycle has no proper coloring avoiding a color `F` everywhere. -/
theorem odd_cycle_avoid (ht : Even t) (w : Fin (t + 1) → Fin 3) (hw : ∀ i, w i ≠ w (i + 1))
    (F : Fin 3) (hF : ∀ i, w i ≠ F) : False := by
  set W : ℕ → Fin 3 := fun j => w (Fin.ofNat (t + 1) j) with hWdef
  have hstep : ∀ j, W j ≠ W (j + 1) := fun j => by
    have := hw (Fin.ofNat (t + 1) j)
    rw [← ofNat_succ_fin] at this
    exact this
  have h2 : ∀ j, W (j + 2) = W j := fun j =>
    two_color_period _ _ _ F (hF _) (hF _) (hF _) (hstep j) (hstep (j + 1))
  have heven : ∀ s, W (2 * s) = W 0 := by
    intro s
    induction s with
    | zero => rfl
    | succ s ih => rw [show 2 * (s + 1) = 2 * s + 2 by ring, h2, ih]
  obtain ⟨s, hs⟩ := ht
  have hlast := hstep t
  have hW0 : W (t + 1) = W 0 := by
    simp only [W]
    rw [ofNat_self_fin]
    rfl
  rw [hW0, show t = 2 * s by omega, heven] at hlast
  exact hlast rfl

/-- The two proper colorings of an odd cycle in which `w 0` avoids `0` and all other vertices
avoid `F ≠ 0`, parametrized by the color `b ≠ F` of `w 1`. -/
def cycCol (F b : Fin 3) (i : Fin (t + 1)) : Fin 3 :=
  if i = 0 then F else if i.val % 2 = 1 then b else third b F

theorem fin_one_val (ht1 : 1 ≤ t) : (1 : Fin (t + 1)).val = 1 := by
  show 1 % (t + 1) = 1
  exact Nat.mod_eq_of_lt (by omega)

theorem fin_one_ne_zero (ht1 : 1 ≤ t) : (1 : Fin (t + 1)) ≠ 0 := fun h => by
  have := congrArg Fin.val h
  rw [fin_one_val ht1] at this
  simp at this

theorem cycCol_ok (ht1 : 1 ≤ t) (F : Fin 3) (hF : F ≠ 0) (b : Fin 3) (hb : b ≠ F) :
    (∀ i : Fin (t + 1), cycCol F b i ≠ cycCol F b (i + 1)) ∧ cycCol (t := t) F b 0 ≠ 0 ∧
      ∀ i : Fin (t + 1), i ≠ 0 → cycCol F b i ≠ F := by
  refine ⟨fun i => ?_, by simpa [cycCol] using hF, fun i hi => ?_⟩
  · have hval := Fin.val_add_one i
    by_cases hi0 : i = 0
    · subst hi0
      rw [zero_add]
      simp only [cycCol, fin_one_ne_zero ht1, fin_one_val ht1, ↓reduceIte]
      simpa using Ne.symm hb
    · by_cases hil : i = Fin.last t
      · subst hil
        have : (Fin.last t + 1 : Fin (t + 1)) = 0 := by simp
        rw [this]
        simp only [cycCol, hi0, ↓reduceIte]
        split_ifs
        · exact hb
        · exact third_ne_right _ _ hb
      · simp only [hil, ↓reduceIte] at hval
        have hne : i + 1 ≠ 0 := by
          intro h
          have := congrArg Fin.val h
          rw [hval] at this
          simp at this
        simp only [cycCol, hi0, hne, hval, ↓reduceIte]
        have := Nat.mod_two_eq_zero_or_one i.val
        split_ifs with h1 h2 h2 <;> try omega
        · exact Ne.symm (third_ne_left _ _ hb)
        · exact third_ne_left _ _ hb
  · simp only [cycCol, hi, ↓reduceIte]
    split_ifs
    · exact hb
    · exact third_ne_right _ _ hb

theorem cycCol_one (ht1 : 1 ≤ t) (F b : Fin 3) : cycCol F b (1 : Fin (t + 1)) = b := by
  simp only [cycCol, fin_one_ne_zero ht1, fin_one_val ht1, ↓reduceIte]

/-- Uniqueness: a coloring of the rotated cycle is `cycCol F (w 1)`. -/
theorem eq_cycCol (ht : Even t) (ht1 : 1 ≤ t) (F : Fin 3)
    (w : Fin (t + 1) → Fin 3)
    (hw : (∀ i, w i ≠ w (i + 1)) ∧ w 0 ≠ 0 ∧ ∀ i : Fin (t + 1), i ≠ 0 → w i ≠ F) :
    w = cycCol F (w 1) := by
  obtain ⟨hcyc, h0, hF'⟩ := hw
  -- `w 0 = F`, otherwise `F` is avoided everywhere
  have hw0 : w 0 = F := by
    by_contra h
    exact odd_cycle_avoid ht w hcyc F fun i => by
      by_cases hi : i = 0
      · subst hi; exact h
      · exact hF' i hi
  set W : ℕ → Fin 3 := fun j => w (Fin.ofNat (t + 1) j) with hWdef
  have hstep : ∀ j, W j ≠ W (j + 1) := fun j => by
    have := hcyc (Fin.ofNat (t + 1) j)
    rw [← ofNat_succ_fin] at this
    exact this
  have hnz : ∀ j, 1 ≤ j → j ≤ t → Fin.ofNat (t + 1) j ≠ 0 := by
    intro j hj1 hjt h
    have := congrArg Fin.val h
    rw [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    simp at this
    omega
  have hWF : ∀ j, 1 ≤ j → j ≤ t → W j ≠ F := fun j hj1 hjt => hF' _ (hnz j hj1 hjt)
  have hW1 : W 1 = w 1 := rfl
  have key : ∀ j, 1 ≤ j → j ≤ t → W j = if j % 2 = 1 then W 1 else third (W 1) F := by
    intro j hj1 hjt
    induction j, hj1 using Nat.le_induction with
    | base => simp
    | succ j hj ih =>
      have ih := ih (by omega)
      have hnext : W (j + 1) = third (W j) F :=
        eq_third _ _ _ (hWF j hj (by omega)) (Ne.symm (hstep j)) (hWF (j + 1) (by omega) hjt)
      rw [hnext, ih]
      have := Nat.mod_two_eq_zero_or_one j
      split_ifs with h1 h2 h2 <;> try omega
      · exact third_third _ _ (hWF 1 le_rfl (by omega))
  funext i
  by_cases hi : i = 0
  · subst hi
    simp [cycCol, hw0]
  · have hiv : 1 ≤ i.val := by
      rcases Nat.eq_zero_or_pos i.val with h | h
      · exact absurd (Fin.ext h) hi
      · exact h
    have := key i.val hiv (by omega)
    have hWi : W i.val = w i := by simp only [W, ofNat_val_fin]
    rw [hWi, hW1] at this
    rw [this]
    simp only [cycCol, hi, ↓reduceIte]

/-- The rotated cycle (selected input at position `0`) has exactly two colorings. -/
theorem card_rot (ht : Even t) (ht1 : 1 ≤ t) (F : Fin 3) (hF : F ≠ 0) :
    Nat.card {w : Fin (t + 1) → Fin 3 //
      (∀ i, w i ≠ w (i + 1)) ∧ w 0 ≠ 0 ∧ ∀ i : Fin (t + 1), i ≠ 0 → w i ≠ F} = 2 := by
  have h1ne : (1 : Fin (t + 1)) ≠ 0 := fin_one_ne_zero ht1
  let e : {w : Fin (t + 1) → Fin 3 //
      (∀ i, w i ≠ w (i + 1)) ∧ w 0 ≠ 0 ∧ ∀ i : Fin (t + 1), i ≠ 0 → w i ≠ F} ≃
      {b : Fin 3 // b ≠ F} :=
    { toFun := fun w => ⟨w.1 1, w.2.2.2 1 h1ne⟩
      invFun := fun b => ⟨cycCol F b.1, cycCol_ok ht1 F hF b.1 b.2⟩
      left_inv := fun w => Subtype.ext (eq_cycCol ht ht1 F w.1 w.2).symm
      right_inv := fun b => Subtype.ext (cycCol_one ht1 F b.1) }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  revert F
  decide

/-- If every input avoids `T = 0` (no input is selected), the cycle has no proper coloring.
Equivalently, a colorable cycle has a selected input. -/
theorem cycle_exists_sel (ht : Even t) (F : Fin 3) (col : Fin t → Fin 3)
    (hcol : ∀ p, col p = 0 ∨ col p = F) (w : Fin (t + 1) → Fin 3)
    (hw : w 0 ≠ F ∧ (∀ i, w i ≠ w (i + 1)) ∧ ∀ p : Fin t, w p.succ ≠ col p) :
    ∃ p, col p = 0 := by
  by_contra hne'
  have hne : ∀ p, col p ≠ 0 := fun p hp => hne' ⟨p, hp⟩
  refine odd_cycle_avoid ht w hw.2.1 F fun i => ?_
  refine Fin.cases hw.1 (fun p => ?_) i
  have := hw.2.2 p
  rcases hcol p with h | h
  · exact absurd h (hne p)
  · rwa [h] at this

/-- If exactly one input is selected (color `0`) and the others have the false color `F`, the
cycle has exactly two proper colorings. -/
theorem cycle_card_two (ht : Even t) (ht1 : 1 ≤ t) (F : Fin 3) (hF : F ≠ 0) (col : Fin t → Fin 3)
    (p₀ : Fin t) (hp₀ : col p₀ = 0) (hother : ∀ p, p ≠ p₀ → col p = F) :
    Nat.card {w : Fin (t + 1) → Fin 3 //
      w 0 ≠ F ∧ (∀ i, w i ≠ w (i + 1)) ∧ ∀ p : Fin t, w p.succ ≠ col p} = 2 := by
  set s : Fin (t + 1) := p₀.succ with hs
  have hs0 : s ≠ 0 := Fin.succ_ne_zero p₀
  -- every vertex except `s` avoids `F`, and `s` avoids `0`
  have hforb : ∀ (w : Fin (t + 1) → Fin 3),
      (w 0 ≠ F ∧ ∀ p : Fin t, w p.succ ≠ col p) ↔
        (w s ≠ 0 ∧ ∀ j : Fin (t + 1), j ≠ s → w j ≠ F) := by
    intro w
    constructor
    · rintro ⟨h0, hp⟩
      refine ⟨by simpa [hp₀] using hp p₀, fun j hj => ?_⟩
      refine Fin.cases (fun _ => h0) (fun p hp' => ?_) j hj
      have hpp : p ≠ p₀ := fun h => hp' (by rw [h])
      simpa [hother p hpp] using hp p
    · rintro ⟨hs', hj⟩
      refine ⟨hj 0 (Ne.symm hs0), fun p => ?_⟩
      by_cases hpp : p = p₀
      · subst hpp; rw [hp₀]; exact hs'
      · rw [hother p hpp]
        exact hj _ fun h => hpp (Fin.succ_injective _ h)
  let e : {w : Fin (t + 1) → Fin 3 //
      w 0 ≠ F ∧ (∀ i, w i ≠ w (i + 1)) ∧ ∀ p : Fin t, w p.succ ≠ col p} ≃
      {w : Fin (t + 1) → Fin 3 //
      (∀ i, w i ≠ w (i + 1)) ∧ w 0 ≠ 0 ∧ ∀ i : Fin (t + 1), i ≠ 0 → w i ≠ F} :=
    { toFun := fun w => ⟨fun i => w.1 (i + s), by
        obtain ⟨h0, hc, hp⟩ := w.2
        obtain ⟨hs', hj⟩ := (hforb w.1).1 ⟨h0, hp⟩
        refine ⟨fun i => ?_, by simpa using hs', fun i hi => hj _ ?_⟩
        · simpa [add_right_comm] using hc (i + s)
        · intro h
          exact hi (by simpa using h)⟩
      invFun := fun w => ⟨fun i => w.1 (i - s), by
        obtain ⟨hc, h0, hj⟩ := w.2
        have := (hforb fun i => w.1 (i - s)).2 ⟨by simpa using h0, fun j hj' => hj _ ?_⟩
        · refine ⟨this.1, fun i => ?_, this.2⟩
          simpa [sub_add_eq_add_sub] using hc (i - s)
        · intro h
          exact hj' (sub_eq_zero.1 h)⟩
      left_inv := fun w => Subtype.ext (funext fun i => by simp)
      right_inv := fun w => Subtype.ext (funext fun i => by simp) }
  rw [Nat.card_congr e]
  exact card_rot ht ht1 F hF

end Cycle

/-! ## NAE triangles -/

theorem nae_card_fintype : ∀ a : Fin 3 → Fin 3,
    Fintype.card {z : Fin 3 → Fin 3 // (∀ r r', r < r' → z r ≠ z r') ∧ ∀ r, z r ≠ a r} =
      if a 0 = a 1 ∧ a 1 = a 2 then 0 else 2 := by
  decide

/-- A triangle whose vertices avoid the colors `a 0, a 1, a 2` of their terminals has exactly
two proper colorings if the terminal colors are not all equal, and none otherwise. -/
theorem nae_card (a : Fin 3 → Fin 3) :
    Nat.card {z : Fin 3 → Fin 3 // (∀ r r', r < r' → z r ≠ z r') ∧ ∀ r, z r ≠ a r} =
      if a 0 = a 1 ∧ a 1 = a 2 then 0 else 2 := by
  rw [Nat.card_eq_fintype_card]
  exact nae_card_fintype a

end SubspaceConvolution.FixedPalette
