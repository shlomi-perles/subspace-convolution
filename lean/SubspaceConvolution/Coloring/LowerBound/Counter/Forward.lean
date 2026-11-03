/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.Counter.Lemmas

/-!
# Lemma 5, first direction: an `η`-coloring gives a satisfying assignment

Given an `η`-coloring `c` of `graph I`:

* `B_i ∪ D` is an `η`-clique, so every row `B_i` uses exactly the colors outside `c(D)` (the
  *register palette*); `B_*` uses `Q - W` of them, and the remaining (at most `W`) colors are
  *active*.
* Each register color `c₀` occurs once in each row; its labels `(e_i, Tᵢ)` define its type
  `regType c c₀ = T`.
* `A^{(j)}_{C,x} ∪ E_{C,x}` is an `η`-clique, so all `A^{(j)}_{C,x}` use the same palette; by
  the entry test, every register color on `A_{C,x}` has type `enc x`.
* At most one mini-constraint `R` of `C` uses the selector color; all other `I`-vertices use
  their anchor colors, which are then blocked on `A_{C,x}`.  Hence
  `n ≤ (n - c_{R,x}) + z_{enc x}`, i.e. `z_{enc x} ≥ c_{R,x}`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace SubspaceConvolution.Counter

variable {I : MinCSP}

/-! ## Some adjacencies -/

/-- The selectors and anchors (the clique `D`). -/
def dv : Fin I.p ⊕ IIdx I → Vtx I := Sum.elim Vtx.sel Vtx.anc

theorem dv_adj_dv {δ δ' : Fin I.p ⊕ IIdx I} (hne : δ ≠ δ') : (graph I).Adj (dv δ) (dv δ') := by
  rcases δ with C | b <;> rcases δ' with C' | b' <;> simp_all [dv, adj_iff, edge]

theorem dv_adj_row (δ : Fin I.p ⊕ IIdx I) (i : Fin (d I)) (A : Mat I) (t : Fin I.n) :
    (graph I).Adj (dv δ) (.row i A t) := by
  rcases δ with C | b <;> simp [dv, adj_iff, edge]

theorem dv_adj_star (δ : Fin I.p ⊕ IIdx I) (t : Fin (Q I - I.W)) :
    (graph I).Adj (dv δ) (.star t) := by
  rcases δ with C | b <;> simp [dv, adj_iff, edge]

theorem row_adj_row {i : Fin (d I)} {q q' : Mat I × Fin I.n} (hne : q ≠ q') :
    (graph I).Adj (.row i q.1 q.2) (.row i q'.1 q'.2) := by
  refine adj_of_edge ?_ (by simp [edge])
  intro h
  simp only [Vtx.row.injEq, true_and] at h
  exact hne (Prod.ext h.1 h.2)

theorem star_adj_star {t t' : Fin (Q I - I.W)} (hne : t ≠ t') :
    (graph I).Adj (.star t) (.star t') :=
  adj_of_edge (by simpa using hne) (by simp [edge])

theorem aV_adj_aV {C : Fin I.p} {x : Fin I.k} {hx : x ∈ I.scope C} {j : Fin (d I)}
    {t t' : Fin I.n} (hne : t ≠ t') : (graph I).Adj (.aV C x hx j t) (.aV C x hx j t') :=
  adj_of_edge (by simpa using hne) (by simp [edge])

theorem eV_adj_eV {C : Fin I.p} {x : Fin I.k} {hx : x ∈ I.scope C} {t t' : Fin (eta I - I.n)}
    (hne : t ≠ t') : (graph I).Adj (.eV C x hx t) (.eV C x hx t') :=
  adj_of_edge (by simpa using hne) (by simp [edge])

theorem eV_adj_aV {C : Fin I.p} {x : Fin I.k} {hx hx' : x ∈ I.scope C} (t : Fin (eta I - I.n))
    (j : Fin (d I)) (t' : Fin I.n) : (graph I).Adj (.eV C x hx t) (.aV C x hx' j t') :=
  adj_of_edge (by simp) (by simp [edge])

theorem iV_adj_row (b : IIdx I) (i : Fin (d I)) (A : Mat I) (t : Fin I.n) :
    (graph I).Adj (.iV b) (.row i A t) :=
  adj_of_edge (by simp) (by simp [edge])

theorem star_adj_aV (s : Fin (Q I - I.W)) {C : Fin I.p} {x : Fin I.k} (hx : x ∈ I.scope C)
    {j : Fin (d I)} (hj : (j : ℕ) = 0) (t : Fin I.n) : (graph I).Adj (.star s) (.aV C x hx j t) :=
  adj_of_edge (by simp) (by simp [edge, hj])

theorem sel_adj_aV (C' : Fin I.p) {C : Fin I.p} {x : Fin I.k} (hx : x ∈ I.scope C)
    {j : Fin (d I)} (hj : (j : ℕ) = 0) (t : Fin I.n) : (graph I).Adj (.sel C') (.aV C x hx j t) :=
  adj_of_edge (by simp) (by simp [edge, hj])

theorem anc_adj_aV {b : IIdx I} {C : Fin I.p} {x : Fin I.k} (hx : x ∈ I.scope C)
    {j : Fin (d I)} (hj : (j : ℕ) = 0) (hb : ¬ (C = b.C ∧ x = b.x)) (t : Fin I.n) :
    (graph I).Adj (.anc b) (.aV C x hx j t) :=
  adj_of_edge (by simp) (by simp only [edge]; exact ⟨hj, hb⟩)

theorem iV_adj_aV {b : IIdx I} {C : Fin I.p} {x : Fin I.k} (hx : x ∈ I.scope C)
    {j : Fin (d I)} (hj : (j : ℕ) = 0) (hC : b.C = C) (hxb : b.x = x) (t : Fin I.n) :
    (graph I).Adj (.iV b) (.aV C x hx j t) :=
  adj_of_edge (by simp) (by simp only [edge]; exact ⟨hj, hC, hxb⟩)

theorem sel_adj_iV {C : Fin I.p} {b : IIdx I} (h : b.C ≠ C) : (graph I).Adj (.sel C) (.iV b) :=
  adj_of_edge (by simp) (by simpa [edge] using h)

theorem anc_adj_iV {b b' : IIdx I} (h : b' ≠ b) : (graph I).Adj (.anc b) (.iV b') :=
  adj_of_edge (by simp) (by simpa [edge] using h)

theorem iV_adj_iV {b b' : IIdx I} (hC : b.C = b'.C) (hR : (b.R : ℕ) ≠ b'.R) :
    (graph I).Adj (.iV b) (.iV b') := by
  refine adj_of_edge ?_ (by simp only [edge]; exact ⟨hC, hR⟩)
  rintro ⟨⟩
  exact hR rfl

noncomputable section

namespace Forward

variable (c : (graph I).Coloring (Fin (eta I)))

theorem inj_of_clique {α : Type*} (f : α → Vtx I)
    (hf : ∀ a a', a ≠ a' → (graph I).Adj (f a) (f a')) : Function.Injective (fun a => c (f a)) := by
  intro a a' h
  by_contra hne
  exact c.valid (hf a a' hne) h

/-! ## The register palette -/

/-- The colors of `D`. -/
def DC : Finset (Fin (eta I)) := univ.image fun δ => c (dv δ)

/-- The colors of the row `B_i`. -/
def rowImg (i : Fin (d I)) : Finset (Fin (eta I)) :=
  univ.image fun q : Mat I × Fin I.n => c (.row i q.1 q.2)

/-- The colors of `B_*`. -/
def starImg : Finset (Fin (eta I)) := univ.image fun t => c (.star t)

/-- The colors of `A^{(j+1)}_{C,x}`. -/
def blockImg (C : Fin I.p) (x : Fin I.k) (hx : x ∈ I.scope C) (j : Fin (d I)) :
    Finset (Fin (eta I)) :=
  univ.image fun t => c (.aV C x hx j t)

/-- The colors of `E_{C,x}`. -/
def eImg (C : Fin I.p) (x : Fin I.k) (hx : x ∈ I.scope C) : Finset (Fin (eta I)) :=
  univ.image fun t => c (.eV C x hx t)

theorem card_DC : (DC c).card = I.p + numI I := by
  rw [DC, card_image_of_injective _ (inj_of_clique c dv fun _ _ h => dv_adj_dv h)]
  simp [card_IIdx]

theorem card_rowImg (i : Fin (d I)) : (rowImg c i).card = Q I := by
  rw [rowImg, card_image_of_injective _ (inj_of_clique c _ fun _ _ h => row_adj_row h),
    card_univ, Fintype.card_prod, card_Mat, Fintype.card_fin, Q]

theorem card_starImg : (starImg c).card = Q I - I.W := by
  rw [starImg, card_image_of_injective _ (inj_of_clique c _ fun _ _ h => star_adj_star h)]
  simp

theorem card_blockImg (C : Fin I.p) (x : Fin I.k) (hx : x ∈ I.scope C) (j : Fin (d I)) :
    (blockImg c C x hx j).card = I.n := by
  rw [blockImg, card_image_of_injective _ (inj_of_clique c _ fun _ _ h => aV_adj_aV h)]
  simp

theorem card_eImg (C : Fin I.p) (x : Fin I.k) (hx : x ∈ I.scope C) :
    (eImg c C x hx).card = eta I - I.n := by
  rw [eImg, card_image_of_injective _ (inj_of_clique c _ fun _ _ h => eV_adj_eV h)]
  simp

theorem disjoint_DC_rowImg (i : Fin (d I)) : Disjoint (DC c) (rowImg c i) := by
  rw [Finset.disjoint_left]
  intro c₀ h1 h2
  simp only [DC, rowImg, mem_image, mem_univ, true_and] at h1 h2
  obtain ⟨δ, rfl⟩ := h1
  obtain ⟨q, hq⟩ := h2
  exact c.valid (dv_adj_row δ i q.1 q.2) hq.symm

theorem starImg_subset : starImg c ⊆ (DC c)ᶜ := by
  intro c₀ h
  simp only [starImg, mem_image, mem_univ, true_and] at h
  obtain ⟨t, rfl⟩ := h
  simp only [DC, mem_compl, mem_image, mem_univ, true_and, not_exists]
  intro δ hδ
  exact c.valid (dv_adj_star δ t) hδ

/-- Every row uses exactly the colors outside `c(D)`. -/
theorem mem_rowImg {c₀ : Fin (eta I)} (h : c₀ ∉ DC c) (i : Fin (d I)) : c₀ ∈ rowImg c i := by
  have hu : DC c ∪ rowImg c i = univ := by
    apply eq_univ_of_card
    rw [card_union_of_disjoint (disjoint_DC_rowImg c i), card_DC, card_rowImg, Fintype.card_fin,
      eta]
    ring
  have : c₀ ∈ DC c ∪ rowImg c i := hu ▸ mem_univ c₀
  rcases mem_union.1 this with h' | h'
  · exact absurd h' h
  · exact h'

theorem exists_row {c₀ : Fin (eta I)} (h : c₀ ∉ DC c) (i : Fin (d I)) :
    ∃ q : Mat I × Fin I.n, c (.row i q.1 q.2) = c₀ := by
  simpa [rowImg] using mem_rowImg c h i

theorem disjoint_eImg_blockImg (C : Fin I.p) (x : Fin I.k) (hx : x ∈ I.scope C) (j : Fin (d I)) :
    Disjoint (eImg c C x hx) (blockImg c C x hx j) := by
  rw [Finset.disjoint_left]
  intro c₀ h1 h2
  simp only [eImg, blockImg, mem_image, mem_univ, true_and] at h1 h2
  obtain ⟨t, rfl⟩ := h1
  obtain ⟨t', ht'⟩ := h2
  exact c.valid (eV_adj_aV t j t') ht'.symm

/-- The private clique leaves exactly `n` colors: all `A^{(j)}_{C,x}` use the same palette. -/
theorem mem_blockImg (C : Fin I.p) (x : Fin I.k) (hx : x ∈ I.scope C) (t : Fin I.n)
    (hj : 0 < d I) (j : Fin (d I)) : c (.aV C x hx ⟨0, hj⟩ t) ∈ blockImg c C x hx j := by
  have hu : eImg c C x hx ∪ blockImg c C x hx j = univ := by
    apply eq_univ_of_card
    rw [card_union_of_disjoint (disjoint_eImg_blockImg c C x hx j), card_eImg, card_blockImg,
      Fintype.card_fin]
    have := n_le_eta I
    omega
  have hmem := hu ▸ mem_univ (c (.aV C x hx ⟨0, hj⟩ t))
  rcases mem_union.1 hmem with h' | h'
  · simp only [eImg, mem_image, mem_univ, true_and] at h'
    obtain ⟨s, hs⟩ := h'
    exact absurd hs (c.valid (eV_adj_aV s _ t))
  · exact h'

/-! ## Types of register colors -/

/-- The type of a register color `c₀`: row `i` of `regType c c₀` is the second half of the label
of the vertex of `B_i` with color `c₀`. -/
def regType (c₀ : Fin (eta I)) : Mat I := fun i =>
  if h : ∃ q : Mat I × Fin I.n, c (.row i q.1 q.2) = c₀ then h.choose.1 i else 0

/-- The test: a register color used on `A_{C,x}` has type `enc x`. -/
theorem regType_eq (C : Fin I.p) (x : Fin I.k) (hx : x ∈ I.scope C) (t : Fin I.n)
    (hj : 0 < d I) (h : c (.aV C x hx ⟨0, hj⟩ t) ∉ DC c) :
    regType c (c (.aV C x hx ⟨0, hj⟩ t)) = enc I x := by
  funext i j
  have hex := exists_row c h i
  simp only [regType, dite_eq_left hex]
  set q := hex.choose with hq
  have hqc : c (.row i q.1 q.2) = c (.aV C x hx ⟨0, hj⟩ t) := hex.choose_spec
  by_contra hne
  have hmem := mem_blockImg c C x hx t hj j
  simp only [blockImg, mem_image, mem_univ, true_and] at hmem
  obtain ⟨t', ht'⟩ := hmem
  exact c.valid (adj_aV_row.2 hne) (ht'.trans hqc.symm)

/-- The active colors: register colors not used on `B_*`. -/
def Act : Finset (Fin (eta I)) := (DC c)ᶜ \ starImg c

theorem card_Act_le (hI : I.Normalized) : (Act c).card ≤ I.W := by
  rw [Act, card_sdiff_of_subset (starImg_subset c), card_compl, card_DC, card_starImg,
    Fintype.card_fin, eta]
  have := W_le_Q hI
  omega

/-- `z_A`: the number of active colors of type `A`. -/
def z (A : Mat I) : ℕ := ((Act c).filter fun c₀ => regType c c₀ = A).card

theorem sum_z (hI : I.Normalized) : ∑ A, z c A ≤ I.W := by
  unfold z
  rw [← card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)]
  exact card_Act_le c hI

/-! ## The selectors -/

/-- The mini-constraint chosen for `C`: the one whose vertices use the selector color, if any. -/
def chosenR (hI : I.Normalized) (C : Fin I.p) : Fin (I.numMini C) :=
  if h : ∃ R : Fin (I.numMini C), ∃ x hx t, c (.iV ⟨C, R, x, hx, t⟩) = c (.sel C) then h.choose
  else ⟨0, hI.numMini_pos C⟩

/-- Every `I`-vertex uses a color of `D` (it is complete to the rows). -/
theorem iV_mem_DC (hI : I.Normalized) (b : IIdx I) : c (.iV b) ∈ DC c := by
  by_contra h
  obtain ⟨q, hq⟩ := exists_row c h ⟨0, d_pos hI⟩
  exact c.valid (iV_adj_row b _ q.1 q.2) hq.symm

/-- An `I`-vertex `b` uses the selector color of its constraint or its anchor color. -/
theorem iV_color (hI : I.Normalized) (b : IIdx I) :
    c (.iV b) = c (.sel b.C) ∨ c (.iV b) = c (.anc b) := by
  have := iV_mem_DC c hI b
  simp only [DC, mem_image, mem_univ, true_and] at this
  obtain ⟨δ, hδ⟩ := this
  rcases δ with C' | b'
  · left
    by_cases hC : b.C = C'
    · rw [hC]; exact hδ.symm
    · exact absurd hδ (c.valid (sel_adj_iV hC))
  · right
    by_cases hb : b = b'
    · subst hb; exact hδ.symm
    · exact absurd hδ (c.valid (anc_adj_iV hb))

/-- The `I`-vertices of the other mini-constraints use their anchor colors. -/
theorem iV_color_of_ne (hI : I.Normalized) (b : IIdx I) (hb : b.R ≠ chosenR c hI b.C) :
    c (.iV b) = c (.anc b) := by
  rcases iV_color c hI b with h | h
  · exfalso
    have hex : ∃ R : Fin (I.numMini b.C), ∃ x hx t, c (.iV ⟨b.C, R, x, hx, t⟩) = c (.sel b.C) :=
      ⟨b.R, b.x, b.hx, b.t, h⟩
    rw [chosenR, dite_eq_left hex] at hb
    obtain ⟨x₀, hx₀, t₀, h₀⟩ := hex.choose_spec
    have hR : (b.R : ℕ) ≠ (hex.choose : ℕ) := fun h' => hb (Fin.ext h')
    exact c.valid (iV_adj_iV (b := b) (b' := ⟨b.C, hex.choose, x₀, hx₀, t₀⟩) rfl hR)
      (h.trans h₀.symm)
  · exact h

/-- The colors available to `A_{C,x}`: active colors of type `enc x`, and the anchor colors of
`I_{C,R,x}` for the chosen `R`. -/
theorem aV_color_mem (hI : I.Normalized) (C : Fin I.p) (x : Fin I.k) (hx : x ∈ I.scope C)
    (t : Fin I.n) :
    c (.aV C x hx ⟨0, d_pos hI⟩ t) ∈ ((Act c).filter fun c₀ => regType c c₀ = enc I x) ∪
      univ.image (fun s => c (.anc ⟨C, chosenR c hI C, x, hx, s⟩)) := by
  set c₀ := c (.aV C x hx ⟨0, d_pos hI⟩ t) with hc₀
  by_cases hD : c₀ ∈ DC c
  · apply mem_union_right
    simp only [DC, mem_image, mem_univ, true_and] at hD
    obtain ⟨δ, hδ⟩ := hD
    rcases δ with C' | b'
    · exact absurd hδ (c.valid (sel_adj_aV C' hx rfl t))
    · obtain ⟨C₁, R₁, x₁, hx₁, t₁⟩ := b'
      by_cases hCx : C = C₁ ∧ x = x₁
      · obtain ⟨rfl, rfl⟩ := hCx
        by_cases hR : R₁ = chosenR c hI C
        · subst hR
          simp only [mem_image, mem_univ, true_and]
          exact ⟨t₁, hδ⟩
        · have h1 := iV_color_of_ne c hI ⟨C, R₁, x, hx₁, t₁⟩ hR
          exact absurd (h1.trans hδ) (c.valid (iV_adj_aV hx rfl rfl rfl t))
      · exact absurd hδ (c.valid (anc_adj_aV hx rfl hCx t))
  · apply mem_union_left
    simp only [Act, mem_filter, mem_sdiff, mem_compl]
    refine ⟨⟨hD, ?_⟩, regType_eq c C x hx t (d_pos hI) hD⟩
    simp only [starImg, mem_image, mem_univ, true_and, not_exists]
    intro s hs
    exact c.valid (star_adj_aV s hx rfl t) hs

/-- The counting step: `z_{enc x} ≥ c_{R,x}` for the chosen `R`. -/
theorem thr_le_z (hI : I.Normalized) (C : Fin I.p) (x : Fin I.k) (hx : x ∈ I.scope C) :
    I.thr C (chosenR c hI C) x ≤ z c (enc I x) := by
  have hsub : blockImg c C x hx ⟨0, d_pos hI⟩ ⊆ ((Act c).filter fun c₀ => regType c c₀ = enc I x) ∪
      univ.image (fun s => c (.anc ⟨C, chosenR c hI C, x, hx, s⟩)) := by
    intro c₀ h
    simp only [blockImg, mem_image, mem_univ, true_and] at h
    obtain ⟨t, rfl⟩ := h
    exact aV_color_mem c hI C x hx t
  have h1 := card_le_card hsub
  rw [card_blockImg] at h1
  have h2 := h1.trans (card_union_le _ _)
  have h3 : (univ.image (fun s => c (.anc ⟨C, chosenR c hI C, x, hx, s⟩))).card ≤
      I.n - I.thr C (chosenR c hI C) x :=
    card_image_le.trans (by simp)
  have h4 := hI.thr_le C (chosenR c hI C) x
  unfold z
  omega

end Forward

open Forward in
/-- **Lemma 5**, first direction: an `η`-coloring yields a satisfying assignment. -/
theorem satisfiable_of_colorable (hI : I.Normalized) (hcol : (graph I).Colorable (eta I)) :
    I.Satisfiable := by
  obtain ⟨c⟩ := hcol
  refine ⟨fun x => min I.n (z c (enc I x)), fun x => min_le_left _ _, ?_, fun C => ?_⟩
  · calc ∑ x, min I.n (z c (enc I x)) ≤ ∑ x, z c (enc I x) :=
          sum_le_sum fun x _ => min_le_right _ _
      _ = ∑ A ∈ univ.map (enc I), z c A := by rw [sum_map]
      _ ≤ ∑ A, z c A := sum_le_sum_of_subset (subset_univ _)
      _ ≤ I.W := sum_z c hI
  · exact ⟨chosenR c hI C, fun x hx =>
      le_min (hI.thr_le C _ x) (thr_le_z c hI C x hx)⟩

end

end SubspaceConvolution.Counter
