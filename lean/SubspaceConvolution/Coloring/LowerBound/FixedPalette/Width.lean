/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.FixedPalette.WidthClasses

/-!
# Width of the supplied layout, part 2: local edges and the main bound

The remaining (local) edges lie inside one group (cycle edges and the edges `w_{p+1} x_{p+1}`) or
inside one clause test (the pairs `c c̄`, `s s̄`, the triangle edges and the edges from triangles to
their terminals).  For the prefix of vertices before `b`, only the group or clause test containing
`b` can straddle the cut.  In a group at most `w_0`, the last cycle vertex before `b` and the
current input have neighbors after the cut; in a clause test at most the eight signal vertices
and two vertices of the unfinished triangle.  Hence at most `10` rows (`locRows`).

Altogether every prefix cut has rank at most `3 + 2k + 6 + 10 = 2k + 19` (`layout_width`).
-/

namespace SubspaceConvolution.FixedPalette

open Finset

variable {k m : ℕ}

/-- `i - 1` (truncated) as a cycle index. -/
def prevC (i : Fin (2 ^ k + 1)) : Fin (2 ^ k + 1) := ⟨i.val - 1, by omega⟩

/-- `i - 1` (truncated) as an input index. -/
def prevI (i : Fin (2 ^ k + 1)) : Fin (2 ^ k) :=
  ⟨i.val - 1, by
    have := i.isLt
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega⟩

/-- The eight signal vertices of clause `i`. -/
def sigs (i : Fin m) : Finset (Vtx k m) := lits i ∪ {.sig i true, .sig i false}

theorem card_sigs (i : Fin m) : (sigs (k := k) i).card ≤ 8 := by
  have h1 := card_lits (k := k) i
  have h2 := card_le_two (a := (Vtx.sig i true : Vtx k m)) (b := .sig i false)
  exact (card_union_le _ _).trans (by omega)

theorem lit_mem_sigs (i : Fin m) (t : Fin 3) (bb : Bool) : (Vtx.lit i t bb : Vtx k m) ∈ sigs i :=
  mem_union_left _ (lit_mem_lits i t bb)

theorem sig_mem_sigs (i : Fin m) (bb : Bool) : (Vtx.sig i bb : Vtx k m) ∈ sigs i := by
  apply mem_union_right
  cases bb <;> simp

/-- The rows of local edges that can cross the cut before `b`. -/
def locRows : Vtx k m → Finset (Vtx k m)
  | .pal _ => ∅
  | .inp γ p => {.cyc γ 0, .cyc γ p.castSucc}
  | .cyc γ i => {.cyc γ 0, .cyc γ (prevC i), .inp γ (prevI i)}
  | .lit i _ _ => sigs i
  | .sig i _ => sigs i
  | .tri i q _ => sigs i ∪ {.tri i q 0, .tri i q 1}

theorem card_locRows (b : Vtx k m) : (locRows b).card ≤ 10 := by
  cases b with
  | pal a => simp [locRows]
  | inp γ p => exact card_le_two.trans (by norm_num)
  | cyc γ i => exact card_le_three.trans (by norm_num)
  | lit i t bb => exact (card_sigs i).trans (by norm_num)
  | sig i bb => exact (card_sigs i).trans (by norm_num)
  | tri i q r =>
    have h1 := card_sigs (k := k) i
    have h2 := card_le_two (a := (Vtx.tri i q 0 : Vtx k m)) (b := .tri i q 1)
    exact (card_union_le _ _).trans (by omega)

/-! ### Locating the first missing vertex -/

theorem between {x y b : Vtx k m} (hs : x.sid = y.sid) (h1 : Vtx.Before x b)
    (h2 : ¬ Vtx.Before y b) : b.sid = x.sid ∧ x.off < b.off ∧ b.off ≤ y.off := by
  unfold Vtx.Before at h1 h2
  omega

theorem sid_eq_grp {γ : Grp k m} {b : Vtx k m} (h : b.sid = γ.sid k) :
    (∃ p, b = .inp γ p) ∨ (∃ i, b = .cyc γ i) := by
  cases b with
  | pal a =>
    have := γ.one_le_sid
    simp at h
    omega
  | inp γ' p => exact Or.inl ⟨p, by rw [Grp.sid_injective h]⟩
  | cyc γ' i => exact Or.inr ⟨i, by rw [Grp.sid_injective h]⟩
  | lit i t bb => exact absurd h.symm (γ.sid_lt_test i)
  | sig i bb => exact absurd h.symm (γ.sid_lt_test i)
  | tri i q r => exact absurd h.symm (γ.sid_lt_test i)

theorem sid_eq_test {i : Fin m} {b : Vtx k m} (h : b.sid = 4 + 2 * k + 4 * (i : ℕ)) :
    sigs i ⊆ locRows b ∧ ((∃ q r, b = .tri i q r) ∨ b.off < 8) := by
  cases b with
  | pal a =>
    simp only [Vtx.sid_pal] at h
    omega
  | inp γ p => exact absurd h (γ.sid_lt_test i)
  | cyc γ p => exact absurd h (γ.sid_lt_test i)
  | lit i' t bb =>
    simp only [Vtx.sid_lit] at h
    have : i' = i := Fin.ext (by omega)
    subst this
    refine ⟨subset_refl _, Or.inr ?_⟩
    simp only [Vtx.off_lit]
    split_ifs <;> omega
  | sig i' bb =>
    simp only [Vtx.sid_sig] at h
    have : i' = i := Fin.ext (by omega)
    subst this
    refine ⟨subset_refl _, Or.inr ?_⟩
    simp only [Vtx.off_sig]
    split_ifs <;> omega
  | tri i' q r =>
    simp only [Vtx.sid_tri] at h
    have : i' = i := Fin.ext (by omega)
    subst this
    exact ⟨subset_union_left, Or.inl ⟨q, r, rfl⟩⟩

/-! ### The local edges -/

section Local

variable {γ : Grp k m} {b : Vtx k m}

theorem cyc_succ_val (i : Fin (2 ^ k + 1)) :
    ((i + 1 : Fin (2 ^ k + 1)) : ℕ) = i + 1 ∨ (i + 1 = 0 ∧ (i : ℕ) = 2 ^ k) := by
  have hv := Fin.val_add_one i
  split_ifs at hv with hl
  · right
    subst hl
    exact ⟨Fin.ext hv, rfl⟩
  · left
    exact hv

/-- The cycle edge `w_i w_{i+1}`, crossing forward. -/
theorem loc_cyc_fwd {i : Fin (2 ^ k + 1)} (h1 : Vtx.Before (.cyc γ i) b)
    (h2 : ¬ Vtx.Before (.cyc γ (i + 1)) b) : (Vtx.cyc γ i : Vtx k m) ∈ locRows b := by
  obtain ⟨hs, ho1, ho2⟩ := between (by simp) h1 h2
  simp only [Vtx.sid_cyc, Vtx.off_cyc] at hs ho1 ho2
  rcases sid_eq_grp hs with ⟨p, rfl⟩ | ⟨i', rfl⟩
  · simp only [Vtx.off_inp] at ho1 ho2
    simp only [locRows, mem_insert, mem_singleton, Vtx.cyc.injEq, true_and]
    right
    rcases cyc_succ_val i with h | ⟨_, h⟩
    · exact Fin.ext (by simp; omega)
    · rw [show (i + 1 : Fin (2 ^ k + 1)) = 0 by omega] at ho2
      simp at ho2
  · simp only [Vtx.off_cyc] at ho1 ho2
    simp only [locRows, mem_insert, mem_singleton, Vtx.cyc.injEq, true_and, reduceCtorEq,
      or_false]
    right
    rcases cyc_succ_val i with h | ⟨h, -⟩
    · exact Fin.ext (by simp [prevC]; omega)
    · exfalso
      rw [h] at ho2
      simp only [Fin.val_zero] at ho2
      omega

/-- The cycle edge `w_i w_{i+1}`, crossing backward (only the closing edge `w_t w_0`). -/
theorem loc_cyc_bwd {i : Fin (2 ^ k + 1)} (h1 : Vtx.Before (.cyc γ (i + 1)) b)
    (h2 : ¬ Vtx.Before (.cyc γ i) b) : (Vtx.cyc γ (i + 1) : Vtx k m) ∈ locRows b := by
  obtain ⟨hs, ho1, ho2⟩ := between (by simp) h1 h2
  simp only [Vtx.sid_cyc, Vtx.off_cyc] at hs ho1 ho2
  rcases cyc_succ_val i with h | ⟨h, -⟩
  · omega
  · rw [h]
    rcases sid_eq_grp hs with ⟨p, rfl⟩ | ⟨i', rfl⟩
    · simp [locRows]
    · simp [locRows]

/-- The edge `x_{p+1} w_{p+1}`. -/
theorem loc_inp_cyc {p : Fin (2 ^ k)} (h1 : Vtx.Before (.inp γ p) b)
    (h2 : ¬ Vtx.Before (.cyc γ p.succ) b) : (Vtx.inp γ p : Vtx k m) ∈ locRows b := by
  obtain ⟨hs, ho1, ho2⟩ := between (by simp) h1 h2
  simp only [Vtx.sid_inp, Vtx.off_inp, Vtx.off_cyc, Fin.val_succ] at hs ho1 ho2
  rcases sid_eq_grp hs with ⟨p', rfl⟩ | ⟨i', rfl⟩
  · simp only [Vtx.off_inp] at ho1 ho2
    omega
  · simp only [Vtx.off_cyc] at ho1 ho2
    simp only [locRows, mem_insert, mem_singleton, reduceCtorEq, false_or, Vtx.inp.injEq,
      true_and]
    exact Fin.ext (by simp [prevI]; omega)

theorem loc_cyc_inp {p : Fin (2 ^ k)} (h1 : Vtx.Before (.cyc γ p.succ) b)
    (h2 : ¬ Vtx.Before (.inp γ p) b) : False := by
  obtain ⟨-, ho1, ho2⟩ := between (by simp) h1 h2
  simp only [Vtx.off_inp, Vtx.off_cyc, Fin.val_succ] at ho1 ho2
  omega

/-- Edges at a signal vertex of a clause test. -/
theorem loc_sig {i : Fin m} {x y : Vtx k m} (hx : x ∈ sigs i) (hsx : x.sid = 4 + 2 * k + 4 * i)
    (hsy : y.sid = x.sid) (h1 : Vtx.Before x b) (h2 : ¬ Vtx.Before y b) : x ∈ locRows b := by
  obtain ⟨hs, -, -⟩ := between hsy.symm h1 h2
  exact (sid_eq_test (hs.trans hsx)).1 hx

/-- A triangle edge. -/
theorem loc_tri_tri {i : Fin m} {q : Fin 4} {r r' : Fin 3} (hr : r < r')
    (h1 : Vtx.Before (.tri i q r) b) (h2 : ¬ Vtx.Before (.tri i q r') b) :
    (Vtx.tri i q r : Vtx k m) ∈ locRows b := by
  obtain ⟨hs, ho1, ho2⟩ := between (by simp) h1 h2
  simp only [Vtx.sid_tri, Vtx.off_tri] at hs ho1 ho2
  rcases (sid_eq_test hs).2 with ⟨q', r'', rfl⟩ | hb
  · simp only [Vtx.off_tri] at ho1 ho2
    have hq : q' = q := Fin.ext (by omega)
    subst hq
    simp only [locRows]
    apply mem_union_right
    have : (r : ℕ) = 0 ∨ (r : ℕ) = 1 := by omega
    rcases this with h | h
    · have : r = 0 := Fin.ext h
      simp [this]
    · have : r = 1 := Fin.ext h
      simp [this]
  · omega

theorem loc_tri_tri_rev {i : Fin m} {q : Fin 4} {r r' : Fin 3} (hr : r < r')
    (h1 : Vtx.Before (.tri i q r') b) (h2 : ¬ Vtx.Before (.tri i q r) b) : False := by
  obtain ⟨-, ho1, ho2⟩ := between (by simp) h1 h2
  simp only [Vtx.off_tri] at ho1 ho2
  have : (r : ℕ) < r' := hr
  omega

theorem term_cases (i : Fin m) (q : Fin 4) (r : Fin 3) :
    (term i q r : Vtx k m) ∈ sigs i ∨ ∃ a, (term i q r : Vtx k m) = .pal a := by
  fin_cases q <;> fin_cases r <;> simp [term, lit_mem_sigs, sig_mem_sigs]

/-- The edge from a triangle vertex to its terminal. -/
theorem loc_tri_term {i : Fin m} {q : Fin 4} {r : Fin 3} {v : Vtx k m} (hv : v ∈ sigs i)
    (h1 : Vtx.Before (.tri i q r) b) (h2 : ¬ Vtx.Before v b) (hsv : v.sid = 4 + 2 * k + 4 * i) :
    False := by
  obtain ⟨-, ho1, ho2⟩ := between (by simp [hsv]) h1 h2
  simp only [Vtx.off_tri] at ho1 ho2
  have : v.off < 8 := by
    simp only [sigs, lits, mem_union, mem_image, mem_univ, true_and, mem_insert,
      mem_singleton] at hv
    rcases hv with ⟨⟨t, bb⟩, rfl⟩ | rfl | rfl
    · simp only [Vtx.off_lit]
      split_ifs <;> omega
    · simp
    · simp
  omega

theorem sid_of_mem_sigs {i : Fin m} {v : Vtx k m} (hv : v ∈ sigs i) :
    v.sid = 4 + 2 * k + 4 * i := by
  simp only [sigs, lits, mem_union, mem_image, mem_univ, true_and, mem_insert,
    mem_singleton] at hv
  rcases hv with ⟨⟨t, bb⟩, rfl⟩ | rfl | rfl <;> simp

end Local

/-- The local edges crossing the cut before `b` have their row in `locRows b`. -/
theorem loc_dir {φ : GridCNF k} {u v b : Vtx k φ.m} (h : edge φ u v = true)
    (hc : Vtx.cls u v = 3) :
    (Vtx.Before u b → ¬ Vtx.Before v b → u ∈ locRows b) ∧
      (Vtx.Before v b → ¬ Vtx.Before u b → v ∈ locRows b) := by
  cases u with
  | pal a => simp [Vtx.cls, Vtx.isPal] at hc
  | inp γ p =>
    cases v <;> simp [edge] at h <;> simp [Vtx.cls, Vtx.isPal, Vtx.isInp] at hc
  | cyc γ i =>
    cases v with
    | pal a => simp [Vtx.cls, Vtx.isPal] at hc
    | inp γ' p =>
      simp only [edge, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun h1 h2 => (loc_cyc_inp h1 h2).elim, fun h1 h2 => loc_inp_cyc h1 h2⟩
    | cyc γ' i' =>
      simp only [edge, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun h1 h2 => loc_cyc_fwd h1 h2, fun h1 h2 => loc_cyc_bwd h1 h2⟩
    | _ => simp [edge] at h
  | lit i t bb =>
    cases v with
    | pal a => simp [Vtx.cls, Vtx.isPal] at hc
    | inp γ p => simp [Vtx.cls, Vtx.isPal, Vtx.isInp, Vtx.isLit] at hc
    | lit i' t' bb' =>
      simp only [edge, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨fun h1 h2 => loc_sig (lit_mem_sigs _ _ _) (by simp) (by simp) h1 h2,
        fun h1 h2 => loc_sig (lit_mem_sigs _ _ _) (by simp) (by simp) h1 h2⟩
    | _ => simp [edge] at h
  | sig i bb =>
    cases v with
    | pal a => simp [Vtx.cls, Vtx.isPal] at hc
    | sig i' bb' =>
      simp only [edge, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨fun h1 h2 => loc_sig (sig_mem_sigs _ _) (by simp) (by simp) h1 h2,
        fun h1 h2 => loc_sig (sig_mem_sigs _ _) (by simp) (by simp) h1 h2⟩
    | _ => simp [edge] at h
  | tri i q r =>
    have hterm : ∀ v : Vtx k φ.m, term i q r = v → v.isPal = false →
        (Vtx.Before (.tri i q r) b → ¬ Vtx.Before v b → Vtx.tri i q r ∈ locRows b) ∧
          (Vtx.Before v b → ¬ Vtx.Before (.tri i q r) b → v ∈ locRows b) := by
      rintro v rfl hp
      rcases term_cases (k := k) i q r with hs | ⟨a, ha⟩
      · have hsv := sid_of_mem_sigs hs
        exact ⟨fun h1 h2 => (loc_tri_term hs h1 h2 hsv).elim,
          fun h1 h2 => loc_sig hs hsv (by simp [hsv]) h1 h2⟩
      · rw [ha] at hp
        simp [Vtx.isPal] at hp
    cases v with
    | pal a => simp [Vtx.cls, Vtx.isPal] at hc
    | lit i' t bb =>
      simp only [edge, decide_eq_true_eq] at h
      exact hterm _ h rfl
    | sig i' bb =>
      simp only [edge, decide_eq_true_eq] at h
      exact hterm _ h rfl
    | tri i' q' r' =>
      simp only [edge, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl, hr⟩ := h
      exact ⟨fun h1 h2 => loc_tri_tri hr h1 h2, fun h1 h2 => (loc_tri_tri_rev hr h1 h2).elim⟩
    | _ => simp [edge] at h

theorem rank_loc (φ : GridCNF k) (b : Vtx k φ.m) :
    matCutRank (clsMat φ 3) (beforeSet b) ≤ 10 := by
  refine (matCutRank_le_card_rows (locRows b) ?_).trans (card_locRows b)
  intro x hx hxR y hy
  rw [mem_beforeSet] at hx hy
  apply clsMat_eq_zero
  intro hadj hc
  rcases hadj with h | h
  · exact hxR ((loc_dir h hc).1 hx hy)
  · rw [Vtx.cls_comm] at hc
    exact hxR ((loc_dir h hc).2 hx hy)

/-! ### The width bound -/

theorem cutRank_beforeSet_le (φ : GridCNF k) (b : Vtx k φ.m) :
    cutRank (graph φ) (beforeSet b) ≤ 2 * k + 19 := by
  unfold cutRank
  rw [adjMatrix_eq_sum]
  refine (matCutRank_sum_le _ _ _).trans ?_
  rw [Fin.sum_univ_four]
  have h0 := rank_pal φ b
  have h1 := rank_ab φ b
  have h2 := rank_lit φ b
  have h3 := rank_loc φ b
  omega

/-- **Width of the supplied layout**: every prefix cut of the layout of `G_φ` has binary
cut-rank at most `2k + 19`. -/
theorem layout_width (φ : GridCNF k) : (layout φ).width (graph φ) ≤ 2 * k + 19 := by
  rw [LinearLayout.width_le_iff]
  intro n
  by_cases hn : n < (layout φ).order.length
  · rw [prefixSet_eq φ n hn]
    exact cutRank_beforeSet_le φ _
  · rw [(layout φ).prefixSet_of_length_le (by omega)]
    simp [cutRank]

end SubspaceConvolution.FixedPalette
