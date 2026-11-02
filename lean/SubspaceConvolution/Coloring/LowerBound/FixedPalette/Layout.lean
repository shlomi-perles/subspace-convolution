/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.FixedPalette.Defs

/-!
# The supplied layout of `G_φ`

The layout orders the vertices by `(sid, off)` lexicographically (`Vtx.sid`, `Vtx.off`): the
palette `T, F_A, F_B`; then the column groups; then the base row groups; then, for each clause, its
three local row groups followed by its clause test.  Inside a group the order is
`w_0, x_1, w_1, …, x_t, w_t`; inside a clause test it is `c₀, c̄₀, c₁, c̄₁, c₂, c̄₂, s, s̄`
followed by the four triangles, one at a time.  This is the order of the paper's paragraph
"The supplied layout and its size".  (The column groups are ordered by column and the base row
groups by row; the paper leaves the order inside these blocks unspecified.)

Every proper prefix of the layout is the set of vertices strictly before its first missing vertex
`b` (`prefixSet_eq`).
-/

namespace SubspaceConvolution.FixedPalette

open Finset

variable {k m : ℕ}

namespace Grp

@[simp] theorem sid_colB (h : Fin k) : (colB h : Grp k m).sid k = 1 + h := rfl
@[simp] theorem sid_rowA (j : Fin k) : (rowA j : Grp k m).sid k = 1 + k + j := rfl
@[simp] theorem sid_loc (i : Fin m) (t : Fin 3) :
    (loc i t : Grp k m).sid k = 1 + 2 * k + 4 * i + t := rfl

theorem one_le_sid (γ : Grp k m) : 1 ≤ γ.sid k := by
  cases γ <;> simp [sid] <;> omega

theorem sid_lt_test (γ : Grp k m) (i : Fin m) :
    γ.sid k ≠ 4 + 2 * k + 4 * (i : ℕ) := by
  cases γ <;> simp [sid] <;> omega

theorem sid_injective {γ γ' : Grp k m} (h : γ.sid k = γ'.sid k) : γ = γ' := by
  cases γ <;> cases γ' <;> simp only [sid] at h
  · rw [colB.injEq]; exact Fin.ext (by omega)
  · omega
  · omega
  · omega
  · rw [rowA.injEq]; exact Fin.ext (by omega)
  · omega
  · omega
  · omega
  · rw [loc.injEq]; exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

end Grp

namespace Vtx

@[simp] theorem sid_pal (a : Fin 3) : (pal a : Vtx k m).sid = 0 := rfl
@[simp] theorem sid_inp (γ : Grp k m) (p : Fin (2 ^ k)) : (inp γ p).sid = γ.sid k := rfl
@[simp] theorem sid_cyc (γ : Grp k m) (i : Fin (2 ^ k + 1)) : (cyc γ i).sid = γ.sid k := rfl
@[simp] theorem sid_lit (i : Fin m) (t : Fin 3) (b : Bool) :
    (lit i t b : Vtx k m).sid = 4 + 2 * k + 4 * i := rfl
@[simp] theorem sid_sig (i : Fin m) (b : Bool) : (sig i b : Vtx k m).sid = 4 + 2 * k + 4 * i := rfl
@[simp] theorem sid_tri (i : Fin m) (q : Fin 4) (r : Fin 3) :
    (tri i q r : Vtx k m).sid = 4 + 2 * k + 4 * i := rfl
@[simp] theorem off_pal (a : Fin 3) : (pal a : Vtx k m).off = a := rfl
@[simp] theorem off_inp (γ : Grp k m) (p : Fin (2 ^ k)) : (inp γ p).off = 2 * p + 1 := rfl
@[simp] theorem off_cyc (γ : Grp k m) (i : Fin (2 ^ k + 1)) : (cyc γ i).off = 2 * i := rfl
@[simp] theorem off_lit (i : Fin m) (t : Fin 3) (b : Bool) :
    (lit i t b : Vtx k m).off = 2 * t + (if b then 0 else 1) := rfl
@[simp] theorem off_sig (i : Fin m) (b : Bool) :
    (sig i b : Vtx k m).off = 6 + (if b then 0 else 1) := rfl
@[simp] theorem off_tri (i : Fin m) (q : Fin 4) (r : Fin 3) :
    (tri i q r : Vtx k m).off = 8 + 3 * q + r := rfl

theorem key_injective {v w : Vtx k m} (hs : v.sid = w.sid) (ho : v.off = w.off) : v = w := by
  cases v with
  | pal a =>
    cases w <;> simp only [sid, off] at hs ho
    · simp only [pal.injEq]; ext; omega
    all_goals first | omega | (have := Grp.one_le_sid (k := k) ‹_›; omega)
  | inp γ p =>
    cases w <;> simp only [sid, off] at hs ho
    · have := Grp.one_le_sid γ; omega
    · simp only [inp.injEq]
      exact ⟨Grp.sid_injective hs, Fin.ext (by omega)⟩
    · omega
    all_goals exact absurd hs (Grp.sid_lt_test γ _)
  | cyc γ i =>
    cases w <;> simp only [sid, off] at hs ho
    · have := Grp.one_le_sid γ; omega
    · omega
    · simp only [cyc.injEq]
      exact ⟨Grp.sid_injective hs, Fin.ext (by omega)⟩
    all_goals exact absurd hs (Grp.sid_lt_test γ _)
  | lit i t b =>
    cases w <;> simp only [sid, off] at hs ho
    · omega
    · exact absurd hs.symm (Grp.sid_lt_test _ i)
    · exact absurd hs.symm (Grp.sid_lt_test _ i)
    · simp only [lit.injEq]
      refine ⟨Fin.ext (by omega), Fin.ext (by split_ifs at ho <;> omega), ?_⟩
      cases b <;> cases ‹Bool› <;> simp at ho ⊢ <;> omega
    · split_ifs at ho <;> omega
    · split_ifs at ho <;> omega
  | sig i b =>
    cases w <;> simp only [sid, off] at hs ho
    · omega
    · exact absurd hs.symm (Grp.sid_lt_test _ i)
    · exact absurd hs.symm (Grp.sid_lt_test _ i)
    · split_ifs at ho <;> omega
    · simp only [sig.injEq]
      refine ⟨Fin.ext (by omega), ?_⟩
      cases b <;> cases ‹Bool› <;> simp at ho ⊢
    · split_ifs at ho <;> omega
  | tri i q r =>
    cases w <;> simp only [sid, off] at hs ho
    · omega
    · exact absurd hs.symm (Grp.sid_lt_test _ i)
    · exact absurd hs.symm (Grp.sid_lt_test _ i)
    · split_ifs at ho <;> omega
    · split_ifs at ho <;> omega
    · simp only [tri.injEq]
      exact ⟨Fin.ext (by omega), Fin.ext (by omega), Fin.ext (by omega)⟩

theorem before_irrefl (v : Vtx k m) : ¬ Before v v := by
  simp [Before]

theorem before_trans {u v w : Vtx k m} (h1 : Before u v) (h2 : Before v w) : Before u w := by
  unfold Before at *
  omega

theorem before_asymm {u v : Vtx k m} (h1 : Before u v) (h2 : Before v u) : False := by
  unfold Before at *
  omega

theorem before_of_layoutLE {v w : Vtx k m} (h : LayoutLE v w) (hne : v ≠ w) : Before v w := by
  unfold LayoutLE at h
  unfold Before
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · refine Or.inr ⟨h1, lt_of_le_of_ne h2 fun h3 => hne (key_injective h1 h3)⟩

instance : IsTrans (Vtx k m) LayoutLE :=
  ⟨fun a b c h1 h2 => by unfold LayoutLE at *; omega⟩

instance : Std.Antisymm (LayoutLE : Vtx k m → Vtx k m → Prop) :=
  ⟨fun a b h1 h2 => by
    unfold LayoutLE at h1 h2
    exact key_injective (by omega) (by omega)⟩

instance : Std.Total (LayoutLE : Vtx k m → Vtx k m → Prop) :=
  ⟨fun a b => by unfold LayoutLE; omega⟩

end Vtx

/-- The supplied layout of `G_φ`: the vertices sorted by `(sid, off)`. -/
def layout (φ : GridCNF k) : LinearLayout (Vtx k φ.m) where
  order := (univ : Finset (Vtx k φ.m)).sort Vtx.LayoutLE
  nodup := sort_nodup _ _
  mem_order v := (mem_sort _).2 (mem_univ v)

theorem layout_pairwise (φ : GridCNF k) : (layout φ).order.Pairwise Vtx.Before :=
  ((pairwise_sort _ _).and (layout φ).nodup).imp fun h => Vtx.before_of_layoutLE h.1 h.2

/-- A proper prefix of the layout is the set of vertices before its first missing vertex. -/
theorem prefixSet_eq (φ : GridCNF k) (n : ℕ) (hn : n < (layout φ).order.length) :
    (layout φ).prefixSet n = univ.filter fun v => Vtx.Before v ((layout φ).order[n]) := by
  have hpw := List.pairwise_iff_getElem.1 (layout_pairwise φ)
  ext v
  simp only [LinearLayout.prefixSet, List.mem_toFinset, mem_filter, mem_univ, true_and]
  constructor
  · intro hv
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.1 hv
    exact hpw j n (by omega) hn (by omega)
  · intro hv
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ((layout φ).mem_order v)
    refine List.mem_take_iff_getElem.2 ⟨j, ?_, rfl⟩
    rcases lt_trichotomy j n with h | h | h
    · omega
    · subst h
      exact absurd hv (Vtx.before_irrefl _)
    · exact absurd (hpw n j hn hj h) fun h' => Vtx.before_asymm h' hv

end SubspaceConvolution.FixedPalette
