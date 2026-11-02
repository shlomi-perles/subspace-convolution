/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.Basic

/-!
# A universal clique for palettes with more than three colors

For `c > 3` colors the paper adds a universal `(c-3)`-clique placed first in the layout.  Here,
for any graph `G`, `joinClique G t` is `G` together with a `t`-clique joined to every vertex.

* `card_coloring_joinClique`: the proper `(t + c)`-colorings of `joinClique G t` number
  `(t + c)!/c! · #c-colorings of G` (the clique takes `t` distinct colors in order, the rest of the
  graph is colored with the remaining `c` colors);
* `colorable_joinClique_iff`: `joinClique G t` is `(t + c)`-colorable iff `G` is `c`-colorable;
* `width_joinCliqueLayout`: placing the clique first adds at most `t` to the width of a layout.

We also prove a general comparison lemma for cut-ranks (`matCutRank_le_of_map`).
-/

namespace SubspaceConvolution.FixedPalette

open Finset Module

/-! ## Comparing cut-ranks through a linear map -/

section CutRankMap

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- If every row of the cut `M[X, V \ X]` is zero or the image under a fixed linear map of a row
of the cut `N[Y, W \ Y]`, then the cut-rank of `M` at `X` is at most that of `N` at `Y`. -/
theorem matCutRank_le_of_map (M : Matrix V V F2) (X : Finset V) (N : Matrix W W F2)
    (Y : Finset W) (L : (W → F2) →ₗ[F2] (V → F2))
    (h : ∀ x ∈ X, cutRow M X x = 0 ∨ ∃ y ∈ Y, cutRow M X x = L (cutRow N Y y)) :
    matCutRank M X ≤ matCutRank N Y := by
  have hle : cutSpace M X ≤ (cutSpace N Y).map L := by
    rw [cutSpace_le_iff]
    intro x hx
    rcases h x hx with h0 | ⟨y, hy, hxy⟩
    · rw [h0]
      exact Submodule.zero_mem _
    · rw [hxy]
      exact Submodule.mem_map_of_mem (cutRow_mem_cutSpace hy)
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_map_le _ _)

end CutRankMap

/-! ## The join with a clique -/

variable {V : Type*}

/-- Adjacency of a `t`-clique joined to every vertex of `G`. -/
def joinAdj (G : SimpleGraph V) (t : ℕ) : Fin t ⊕ V → Fin t ⊕ V → Prop
  | .inl a, .inl b => a ≠ b
  | .inl _, .inr _ => True
  | .inr _, .inl _ => True
  | .inr u, .inr v => G.Adj u v

/-- `G` together with a universal `t`-clique (a `t`-clique joined to every vertex of `G`). -/
def joinClique (G : SimpleGraph V) (t : ℕ) : SimpleGraph (Fin t ⊕ V) where
  Adj := joinAdj G t
  symm := ⟨fun x y h => by
    cases x with
    | inl a =>
      cases y with
      | inl b => exact Ne.symm h
      | inr v => trivial
    | inr u =>
      cases y with
      | inl b => trivial
      | inr v => exact G.symm.symm _ _ h⟩
  loopless := ⟨fun x h => by
    cases x <;> simp only [joinAdj] at h
    · exact h rfl
    · exact G.loopless.irrefl _ h⟩

section Join

variable (G : SimpleGraph V) (t : ℕ)

@[simp] theorem joinClique_adj_inl_inl (a b : Fin t) :
    (joinClique G t).Adj (.inl a) (.inl b) ↔ a ≠ b := Iff.rfl

@[simp] theorem joinClique_adj_inl_inr (a : Fin t) (v : V) :
    (joinClique G t).Adj (.inl a) (.inr v) := trivial

@[simp] theorem joinClique_adj_inr_inl (v : V) (a : Fin t) :
    (joinClique G t).Adj (.inr v) (.inl a) := trivial

@[simp] theorem joinClique_adj_inr_inr (u v : V) :
    (joinClique G t).Adj (.inr u) (.inr v) ↔ G.Adj u v := Iff.rfl

instance [DecidableRel G.Adj] : DecidableRel (joinClique G t).Adj
  | .inl a, .inl b => inferInstanceAs (Decidable (a ≠ b))
  | .inl _, .inr _ => isTrue trivial
  | .inr _, .inl _ => isTrue trivial
  | .inr u, .inr v => inferInstanceAs (Decidable (G.Adj u v))

end Join

/-! ### Colorings -/

section Colorings

variable (G : SimpleGraph V) (t c : ℕ)

/-- The colors not used by an embedding `g` of the clique. -/
abbrev freeColors (g : Fin t ↪ Fin (t + c)) : Type := {x : Fin (t + c) // ∀ a, g a ≠ x}

theorem card_freeColors (g : Fin t ↪ Fin (t + c)) : Fintype.card (freeColors t c g) = c := by
  classical
  have h1 : Fintype.card (freeColors t c g) =
      Fintype.card {x : Fin (t + c) // ¬ ∃ a, g a = x} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun x => by simp)
  have h2 : Fintype.card {x : Fin (t + c) // ∃ a, g a = x} = t := by
    have e : {x : Fin (t + c) // ∃ a, g a = x} ≃ Fin t := (Equiv.ofInjective g g.injective).symm
    rw [Fintype.card_congr e, Fintype.card_fin]
  rw [h1, Fintype.card_subtype_compl, h2, Fintype.card_fin]
  omega

/-- A bijection between the free colors and `Fin c`. -/
noncomputable def freeEquiv (g : Fin t ↪ Fin (t + c)) : freeColors t c g ≃ Fin c :=
  Fintype.equivFinOfCardEq (card_freeColors t c g)

/-- Colorings of the rest of the graph with the free colors are colorings with `c` colors. -/
noncomputable def fiberEquiv (g : Fin t ↪ Fin (t + c)) :
    {h : V → Fin (t + c) // (∀ a v, g a ≠ h v) ∧ ∀ ⦃u v⦄, G.Adj u v → h u ≠ h v} ≃
      {h : V → Fin c // ∀ ⦃u v⦄, G.Adj u v → h u ≠ h v} where
  toFun h := ⟨fun v => freeEquiv t c g ⟨h.1 v, fun a => h.2.1 a v⟩, fun u v huv heq =>
    h.2.2 huv (congrArg Subtype.val ((freeEquiv t c g).injective heq))⟩
  invFun h := ⟨fun v => ((freeEquiv t c g).symm (h.1 v)).1,
    fun a v => ((freeEquiv t c g).symm (h.1 v)).2 a,
    fun u v huv heq => h.2 huv ((freeEquiv t c g).symm.injective (Subtype.ext heq))⟩
  left_inv h := Subtype.ext (funext fun v => by simp)
  right_inv h := Subtype.ext (funext fun v => by simp)

/-- Colorings of the join: an injective coloring of the clique and a coloring of `G` avoiding its
colors. -/
def joinEquiv :
    {f : Fin t ⊕ V → Fin (t + c) // ∀ ⦃x y⦄, (joinClique G t).Adj x y → f x ≠ f y} ≃
      Σ g : Fin t ↪ Fin (t + c),
        {h : V → Fin (t + c) // (∀ a v, g a ≠ h v) ∧ ∀ ⦃u v⦄, G.Adj u v → h u ≠ h v} where
  toFun f := ⟨⟨fun a => f.1 (.inl a), fun a b hab => by
      by_contra hne
      exact f.2 (show (joinClique G t).Adj (.inl a) (.inl b) from hne) hab⟩,
    ⟨fun v => f.1 (.inr v), fun a v => f.2 (joinClique_adj_inl_inr G t a v),
      fun u v huv => f.2 (show (joinClique G t).Adj (.inr u) (.inr v) from huv)⟩⟩
  invFun x := ⟨Sum.elim x.1 x.2.1, fun p q hpq => by
    cases p with
    | inl a =>
      cases q with
      | inl b => exact fun h => hpq (x.1.injective h)
      | inr v => exact x.2.2.1 a v
    | inr u =>
      cases q with
      | inl b => exact fun h => x.2.2.1 b u h.symm
      | inr v => exact x.2.2.2 hpq⟩
  left_inv f := Subtype.ext (funext fun p => by cases p <;> rfl)
  right_inv x := rfl

/-- **Universal clique, counting**: the `(t + c)`-colorings of `joinClique G t` number
`(t + c)(t + c - 1)⋯(c + 1)` times the `c`-colorings of `G`. -/
theorem card_coloring_joinClique [Fintype V] :
    Fintype.card ((joinClique G t).Coloring (Fin (t + c))) =
      (t + c).descFactorial t * Fintype.card (G.Coloring (Fin c)) := by
  classical
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    Nat.card_congr (coloringEquivFun _ _), Nat.card_congr (coloringEquivFun G (Fin c)),
    Nat.card_congr (joinEquiv G t c), Nat.card_sigma]
  simp only [fun g => Nat.card_congr (fiberEquiv G t c g)]
  rw [sum_const, card_univ, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin,
    smul_eq_mul]

/-- **Universal clique, decision**: `joinClique G t` is `(t + c)`-colorable iff `G` is
`c`-colorable. -/
theorem colorable_joinClique_iff : (joinClique G t).Colorable (t + c) ↔ G.Colorable c := by
  constructor
  · rintro ⟨f⟩
    let g : Fin t ↪ Fin (t + c) := ⟨fun a => f (.inl a), fun a b hab => by
      by_contra hne
      exact f.valid (show (joinClique G t).Adj (.inl a) (.inl b) from hne) hab⟩
    exact ⟨SimpleGraph.Coloring.mk
      (fun v => freeEquiv t c g ⟨f (.inr v), fun a => f.valid (joinClique_adj_inl_inr G t a v)⟩)
      fun {u v} huv heq => f.valid (show (joinClique G t).Adj (.inr u) (.inr v) from huv)
        (congrArg Subtype.val ((freeEquiv t c g).injective heq))⟩
  · rintro ⟨C⟩
    refine ⟨SimpleGraph.Coloring.mk (Sum.elim (Fin.castAdd c) fun v => Fin.natAdd t (C v)) ?_⟩
    intro p q hpq
    cases p with
    | inl a =>
      cases q with
      | inl b => exact fun h => hpq (Fin.castAdd_injective _ _ h)
      | inr v =>
        intro h
        have h1 := congrArg Fin.val h
        simp only [Sum.elim_inl, Sum.elim_inr, Fin.val_castAdd, Fin.val_natAdd] at h1
        omega
    | inr u =>
      cases q with
      | inl b =>
        intro h
        have h1 := congrArg Fin.val h
        simp only [Sum.elim_inl, Sum.elim_inr, Fin.val_castAdd, Fin.val_natAdd] at h1
        omega
      | inr v =>
        intro h
        exact C.valid hpq (Fin.natAdd_injective _ _ h)

end Colorings

/-! ### The layout -/

section Layout

variable [Fintype V]

/-- The layout of `joinClique G t`: the clique first (in order), then the layout `π` of `G`. -/
def joinCliqueLayout (π : LinearLayout V) (t : ℕ) : LinearLayout (Fin t ⊕ V) where
  order := (List.finRange t).map Sum.inl ++ π.order.map Sum.inr
  nodup := by
    rw [List.nodup_append]
    refine ⟨(List.nodup_finRange t).map Sum.inl_injective, π.nodup.map Sum.inr_injective, ?_⟩
    intro a ha b hb
    simp only [List.mem_map] at ha hb
    obtain ⟨a', -, rfl⟩ := ha
    obtain ⟨b', -, rfl⟩ := hb
    simp
  mem_order x := by
    cases x with
    | inl a => simp
    | inr v => simp [π.mem_order v]

variable [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (π : LinearLayout V) (t : ℕ)

theorem joinCliqueLayout_prefixSet_of_le {n : ℕ} (hn : n ≤ t) :
    #((joinCliqueLayout π t).prefixSet n) ≤ t := by
  unfold LinearLayout.prefixSet joinCliqueLayout
  refine (List.toFinset_card_le _).trans ?_
  simp only [List.length_take]
  omega

theorem mem_joinCliqueLayout_prefixSet {n : ℕ} (hn : t ≤ n) (x : Fin t ⊕ V) :
    x ∈ (joinCliqueLayout π t).prefixSet n ↔
      Sum.elim (fun _ => True) (fun v => v ∈ π.prefixSet (n - t)) x := by
  have htake : (joinCliqueLayout π t).order.take n =
      (List.finRange t).map Sum.inl ++ (π.order.take (n - t)).map Sum.inr := by
    simp only [joinCliqueLayout, List.take_append, List.length_map, List.length_finRange]
    rw [List.take_of_length_le (by simp; omega), List.map_take]
  simp only [LinearLayout.prefixSet, List.mem_toFinset, htake, List.mem_append, List.mem_map]
  cases x with
  | inl a => simp
  | inr v => simp

/-- The edges of the join at the clique. -/
def cliqueMat : Matrix (Fin t ⊕ V) (Fin t ⊕ V) F2 :=
  Matrix.of fun x y => if x.isLeft ∨ y.isLeft then (joinClique G t).adjMatrix F2 x y else 0

/-- The edges of `G` inside the join. -/
def baseMat : Matrix (Fin t ⊕ V) (Fin t ⊕ V) F2
  | .inr u, .inr v => G.adjMatrix F2 u v
  | _, _ => 0

omit [Fintype V] [DecidableEq V] in
theorem adjMatrix_join : (joinClique G t).adjMatrix F2 = cliqueMat G t + baseMat G t := by
  ext x y
  cases x <;> cases y <;> simp [cliqueMat, baseMat, SimpleGraph.adjMatrix_apply]

/-- The extension of a vector on `V` by zero on the clique. -/
def extendZero : (V → F2) →ₗ[F2] (Fin t ⊕ V → F2) where
  toFun g := Sum.elim 0 g
  map_add' g g' := by
    funext x
    cases x <;> simp
  map_smul' a g := by
    funext x
    cases x <;> simp

/-- **Universal clique, width**: placing the clique first adds at most `t` to the width. -/
theorem width_joinCliqueLayout :
    (joinCliqueLayout π t).width (joinClique G t) ≤ π.width G + t := by
  rw [LinearLayout.width_le_iff]
  intro n
  by_cases hn : n ≤ t
  · exact (matCutRank_le_card _ _).trans
      ((joinCliqueLayout_prefixSet_of_le π t hn).trans (by omega))
  · have hn' : t ≤ n := by omega
    set X := (joinCliqueLayout π t).prefixSet n with hX
    set Y := π.prefixSet (n - t) with hY
    have hmem : ∀ x, x ∈ X ↔ Sum.elim (fun _ => True) (fun v => v ∈ Y) x :=
      mem_joinCliqueLayout_prefixSet π t hn'
    unfold cutRank
    rw [adjMatrix_join]
    refine matCutRank_add_le.trans ?_
    have hw := π.cutRank_prefixSet_le_width G (n - t)
    suffices h : matCutRank (cliqueMat G t) X ≤ t ∧ matCutRank (baseMat G t) X ≤ π.width G by
      omega
    refine ⟨?_, ?_⟩
    · -- the clique rows
      refine (matCutRank_le_card_rows (univ.map ⟨Sum.inl, Sum.inl_injective⟩) ?_).trans
        (by simp)
      intro x hx hxR y hy
      cases x with
      | inl a => simp at hxR
      | inr u =>
        cases y with
        | inl b => exact absurd ((hmem (.inl b)).2 trivial) hy
        | inr v => simp [cliqueMat]
    · -- the rows of `G`
      refine (matCutRank_le_of_map _ X _ Y (extendZero t) ?_).trans hw
      intro x hx
      cases x with
      | inl a =>
        left
        funext y
        cases y <;> simp [baseMat]
      | inr u =>
        right
        refine ⟨u, by simpa using (hmem (.inr u)).1 hx, ?_⟩
        funext y
        cases y with
        | inl b =>
          simp only [cutRow_apply, extendZero, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl,
            Pi.zero_apply]
          split_ifs <;> rfl
        | inr v =>
          have hv : (Sum.inr v : Fin t ⊕ V) ∈ X ↔ v ∈ Y := by simpa using hmem (.inr v)
          simp only [cutRow_apply, extendZero, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inr, hv]
          rfl

end Layout

end SubspaceConvolution.FixedPalette
