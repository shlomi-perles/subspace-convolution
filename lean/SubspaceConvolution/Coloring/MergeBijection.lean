/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.Profiles
import SubspaceConvolution.Coloring.MatchingDP

/-!
# The merge step of Theorem 6

For disjoint `X₁, X₂`, color partitions of `G[X₁ ∪ X₂]` correspond bijectively to triples
`(P₁, P₂, M)` of color partitions `P_i` of `G[X_i]` and compatible partial matchings `M` between
their classes (paper: "Classes sharing a color form a compatible partial matching … the
correspondence is a bijection").  The histogram of the parent partition is the parent histogram
of the matching, computed from the child profiles by Lemma 3.

Combined with `MergeData.run_spec`, this proves that the histogram recurrence of the paper
computes, for every parent histogram, the number of color partitions of `G[X₁ ∪ X₂]` realizing
it (`hists_union`).
-/

open Finset

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Histograms -/

section Hist

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The histogram of a partition of `X`: the multiset of profiles of its classes. -/
def hist {X : Finset V} (P : Finpartition X) : Multiset (Submodule F2 (V → F2)) :=
  P.parts.val.map (profile G X)

open Classical in
/-- The color partitions of `G[X]`. -/
noncomputable def colorParts (X : Finset V) : Finset (Finpartition X) :=
  univ.filter (IsColorPartition G)

theorem mem_colorParts {X : Finset V} {P : Finpartition X} :
    P ∈ colorParts G X ↔ IsColorPartition G P := by
  classical
  unfold colorParts
  rw [mem_filter]
  simp

/-- The histograms of all color partitions of `G[X]`, with multiplicity: the multiplicity of `h`
is the number of color partitions of `G[X]` with histogram `h`. -/
noncomputable def hists (X : Finset V) : Multiset (Multiset (Submodule F2 (V → F2))) :=
  (colorParts G X).val.map (hist G)

/-- The merge data for the children `X₁, X₂`: compatibility is the vanishing of `β`, and parent
profiles are obtained by restricting to `Y = V \ (X₁ ∪ X₂)` (Lemma 3). -/
noncomputable def mergeData (X₁ X₂ : Finset V) :
    MergeData (Submodule F2 (V → F2)) (Submodule F2 (V → F2)) (Submodule F2 (V → F2)) where
  compat := Compatible G X₁ X₂
  left U := U.map (restrictOut (X₁ ∪ X₂))
  right W := W.map (restrictOut (X₁ ∪ X₂))
  pair U W := U.map (restrictOut (X₁ ∪ X₂)) ⊔ W.map (restrictOut (X₁ ∪ X₂))

end Hist

/-! ### The combinatorial bijection -/

section Bijection

variable {X₁ X₂ : Finset V}

/-- The pairs `(C ∩ X₁, C ∩ X₂)` of classes `C ∈ S` meeting both sides. -/
def matchOf (X₁ X₂ : Finset V) (S : Finset (Finset V)) : Finset (Finset V × Finset V) :=
  (S.filter fun C => (C ∩ X₁).Nonempty ∧ (C ∩ X₂).Nonempty).image fun C => (C ∩ X₁, C ∩ X₂)

/-- The parent classes: unions of matched pairs, and unmatched classes on either side. -/
def parentParts (L R : Finset (Finset V)) (M : Finset (Finset V × Finset V)) :
    Finset (Finset V) :=
  M.image (fun e => e.1 ∪ e.2) ∪ L.filter (· ∉ M.image Prod.fst) ∪
    R.filter (· ∉ M.image Prod.snd)

/-- `M` is a partial matching between `L` and `R` (no compatibility requirement). -/
def IsPM (L R : Finset (Finset V)) (M : Finset (Finset V × Finset V)) : Prop :=
  M ⊆ L ×ˢ R ∧ (∀ e ∈ M, ∀ e' ∈ M, e.1 = e'.1 → e = e') ∧
    (∀ e ∈ M, ∀ e' ∈ M, e.2 = e'.2 → e = e')

theorem mem_parentParts {L R : Finset (Finset V)} {M : Finset (Finset V × Finset V)}
    {t : Finset V} :
    t ∈ parentParts L R M ↔ (∃ e ∈ M, e.1 ∪ e.2 = t) ∨ (t ∈ L ∧ t ∉ M.image Prod.fst) ∨
      (t ∈ R ∧ t ∉ M.image Prod.snd) := by
  simp only [parentParts, mem_union, mem_image, mem_filter, or_assoc]

theorem mem_restrict_parts {X Y : Finset V} (P : Finpartition X) (h : Y ⊆ X) {C : Finset V} :
    C ∈ (P.restrict h).parts ↔ C.Nonempty ∧ ∃ D ∈ P.parts, D ∩ Y = C := by
  rw [Finpartition.parts_restrict, mem_erase, mem_image, nonempty_iff_ne_empty]
  rfl

variable (hd : Disjoint X₁ X₂) (P₁ : Finpartition X₁) (P₂ : Finpartition X₂)
  {M : Finset (Finset V × Finset V)}

include hd in
theorem exists_mem_parentParts (_hM : IsPM P₁.parts P₂.parts M) {a : V} (ha : a ∈ X₁ ∪ X₂) :
    ∃ t ∈ parentParts P₁.parts P₂.parts M, a ∈ t := by
  rcases mem_union.1 ha with ha | ha
  · obtain ⟨C, hC, haC⟩ := P₁.exists_mem ha
    by_cases hm : C ∈ M.image Prod.fst
    · obtain ⟨e, he, rfl⟩ := mem_image.1 hm
      exact ⟨e.1 ∪ e.2, mem_parentParts.2 (Or.inl ⟨e, he, rfl⟩), mem_union_left _ haC⟩
    · exact ⟨C, mem_parentParts.2 (Or.inr (Or.inl ⟨hC, hm⟩)), haC⟩
  · obtain ⟨C, hC, haC⟩ := P₂.exists_mem ha
    by_cases hm : C ∈ M.image Prod.snd
    · obtain ⟨e, he, rfl⟩ := mem_image.1 hm
      exact ⟨e.1 ∪ e.2, mem_parentParts.2 (Or.inl ⟨e, he, rfl⟩), mem_union_right _ haC⟩
    · exact ⟨C, mem_parentParts.2 (Or.inr (Or.inr ⟨hC, hm⟩)), haC⟩

include hd in
theorem eq_of_mem_parentParts (hM : IsPM P₁.parts P₂.parts M) {a : V} {t t' : Finset V}
    (ht : t ∈ parentParts P₁.parts P₂.parts M) (ht' : t' ∈ parentParts P₁.parts P₂.parts M)
    (hat : a ∈ t) (hat' : a ∈ t') : t = t' := by
  obtain ⟨hsub, h1, h2⟩ := hM
  have hl : ∀ e ∈ M, e.1 ∈ P₁.parts := fun e he => (mem_product.1 (hsub he)).1
  have hr : ∀ e ∈ M, e.2 ∈ P₂.parts := fun e he => (mem_product.1 (hsub he)).2
  have hX₁ : ∀ e ∈ M, e.1 ⊆ X₁ := fun e he => P₁.subset (hl e he)
  have hX₂ : ∀ e ∈ M, e.2 ⊆ X₂ := fun e he => P₂.subset (hr e he)
  have n12 : ∀ {x}, x ∈ X₁ → x ∉ X₂ := fun hx => disjoint_left.1 hd hx
  -- in a matched pair, `a` lies on exactly one side
  rcases mem_parentParts.1 ht with ⟨e, he, rfl⟩ | ⟨htL, htm⟩ | ⟨htR, htm⟩ <;>
    rcases mem_parentParts.1 ht' with ⟨e', he', rfl⟩ | ⟨htL', htm'⟩ | ⟨htR', htm'⟩
  · -- pair / pair
    rcases mem_union.1 hat with h | h
    · have h' : a ∈ e'.1 := by
        rcases mem_union.1 hat' with h' | h'
        · exact h'
        · exact absurd (hX₂ e' he' h') (n12 (hX₁ e he h))
      rw [h1 e he e' he' (P₁.eq_of_mem_parts (hl e he) (hl e' he') h h')]
    · have h' : a ∈ e'.2 := by
        rcases mem_union.1 hat' with h' | h'
        · exact absurd (hX₂ e he h) (n12 (hX₁ e' he' h'))
        · exact h'
      rw [h2 e he e' he' (P₂.eq_of_mem_parts (hr e he) (hr e' he') h h')]
  · -- pair / unmatched left
    have haX : a ∈ X₁ := P₁.subset htL' hat'
    have h : a ∈ e.1 := by
      rcases mem_union.1 hat with h | h
      · exact h
      · exact absurd (hX₂ e he h) (n12 haX)
    exact absurd (mem_image.2 ⟨e, he, P₁.eq_of_mem_parts (hl e he) htL' h hat'⟩) htm'
  · -- pair / unmatched right
    have haX : a ∈ X₂ := P₂.subset htR' hat'
    have h : a ∈ e.2 := by
      rcases mem_union.1 hat with h | h
      · exact absurd haX (n12 (hX₁ e he h))
      · exact h
    exact absurd (mem_image.2 ⟨e, he, P₂.eq_of_mem_parts (hr e he) htR' h hat'⟩) htm'
  · -- unmatched left / pair
    have haX : a ∈ X₁ := P₁.subset htL hat
    have h : a ∈ e'.1 := by
      rcases mem_union.1 hat' with h | h
      · exact h
      · exact absurd (hX₂ e' he' h) (n12 haX)
    exact absurd (mem_image.2 ⟨e', he', P₁.eq_of_mem_parts (hl e' he') htL h hat⟩) htm
  · exact P₁.eq_of_mem_parts htL htL' hat hat'
  · exact absurd (P₂.subset htR' hat') (n12 (P₁.subset htL hat))
  · -- unmatched right / pair
    have haX : a ∈ X₂ := P₂.subset htR hat
    have h : a ∈ e'.2 := by
      rcases mem_union.1 hat' with h | h
      · exact absurd haX (n12 (hX₁ e' he' h))
      · exact h
    exact absurd (mem_image.2 ⟨e', he', P₂.eq_of_mem_parts (hr e' he') htR h hat⟩) htm
  · exact absurd (P₂.subset htR hat) (n12 (P₁.subset htL' hat'))
  · exact P₂.eq_of_mem_parts htR htR' hat hat'

theorem parentParts_subset (hM : IsPM P₁.parts P₂.parts M) {t : Finset V}
    (ht : t ∈ parentParts P₁.parts P₂.parts M) : t ⊆ X₁ ∪ X₂ := by
  obtain ⟨hsub, -⟩ := hM
  rcases mem_parentParts.1 ht with ⟨e, he, rfl⟩ | ⟨htL, -⟩ | ⟨htR, -⟩
  · obtain ⟨h1, h2⟩ := mem_product.1 (hsub he)
    exact union_subset_union (P₁.subset h1) (P₂.subset h2)
  · exact (P₁.subset htL).trans subset_union_left
  · exact (P₂.subset htR).trans subset_union_right

theorem empty_not_mem_parentParts (hM : IsPM P₁.parts P₂.parts M) :
    ∅ ∉ parentParts P₁.parts P₂.parts M := by
  obtain ⟨hsub, -⟩ := hM
  intro h
  rcases mem_parentParts.1 h with ⟨e, he, he'⟩ | ⟨htL, -⟩ | ⟨htR, -⟩
  · have := P₁.nonempty_of_mem_parts (mem_product.1 (hsub he)).1
    rw [← not_nonempty_iff_eq_empty] at he'
    exact he' (this.mono subset_union_left)
  · exact P₁.empty_notMem_parts htL
  · exact P₂.empty_notMem_parts htR

/-- The parent partition built from `P₁`, `P₂` and a partial matching `M`. -/
def ofTriple (hM : IsPM P₁.parts P₂.parts M) : Finpartition (X₁ ∪ X₂) :=
  Finpartition.ofExistsUnique (parentParts P₁.parts P₂.parts M)
    (fun _ ht => parentParts_subset P₁ P₂ hM ht)
    (fun _ ha => by
      obtain ⟨t, ht, hat⟩ := exists_mem_parentParts hd P₁ P₂ hM ha
      exact ⟨t, ⟨ht, hat⟩, fun t' ⟨ht', hat'⟩ =>
        eq_of_mem_parentParts hd P₁ P₂ hM ht' ht hat' hat⟩)
    (empty_not_mem_parentParts P₁ P₂ hM)

@[simp] theorem ofTriple_parts (hM : IsPM P₁.parts P₂.parts M) :
    (ofTriple hd P₁ P₂ hM).parts = parentParts P₁.parts P₂.parts M := rfl

end Bijection

/-! ### Round trips -/

section RoundTrip

variable {X₁ X₂ : Finset V} (hd : Disjoint X₁ X₂)

/-- Restriction of a parent partition to the left child. -/
def restrictL (P : Finpartition (X₁ ∪ X₂)) : Finpartition X₁ := P.restrict subset_union_left

/-- Restriction of a parent partition to the right child. -/
def restrictR (P : Finpartition (X₁ ∪ X₂)) : Finpartition X₂ := P.restrict subset_union_right

include hd in
theorem isPM_matchOf (P : Finpartition (X₁ ∪ X₂)) :
    IsPM (restrictL P).parts (restrictR P).parts (matchOf X₁ X₂ P.parts) := by
  refine ⟨fun e he => ?_, fun e he e' he' h => ?_, fun e he e' he' h => ?_⟩
  · obtain ⟨C, hC, rfl⟩ := mem_image.1 he
    obtain ⟨hCP, h1, h2⟩ := mem_filter.1 hC
    exact mem_product.2 ⟨(mem_restrict_parts P _).2 ⟨h1, C, hCP, rfl⟩,
      (mem_restrict_parts P _).2 ⟨h2, C, hCP, rfl⟩⟩
  · obtain ⟨C, hC, rfl⟩ := mem_image.1 he
    obtain ⟨C', hC', rfl⟩ := mem_image.1 he'
    obtain ⟨hCP, h1, -⟩ := mem_filter.1 hC
    obtain ⟨hCP', -, -⟩ := mem_filter.1 hC'
    obtain ⟨x, hx⟩ := h1
    have hx' : x ∈ C' ∩ X₁ := (show C ∩ X₁ = C' ∩ X₁ from h) ▸ hx
    rw [P.eq_of_mem_parts hCP hCP' (mem_inter.1 hx).1 (mem_inter.1 hx').1]
  · obtain ⟨C, hC, rfl⟩ := mem_image.1 he
    obtain ⟨C', hC', rfl⟩ := mem_image.1 he'
    obtain ⟨hCP, -, h2⟩ := mem_filter.1 hC
    obtain ⟨hCP', -, -⟩ := mem_filter.1 hC'
    obtain ⟨x, hx⟩ := h2
    have hx' : x ∈ C' ∩ X₂ := (show C ∩ X₂ = C' ∩ X₂ from h) ▸ hx
    rw [P.eq_of_mem_parts hCP hCP' (mem_inter.1 hx).1 (mem_inter.1 hx').1]

include hd in
/-- Round trip: rebuilding a parent partition from its restrictions and matching. -/
theorem parentParts_restrict (P : Finpartition (X₁ ∪ X₂)) :
    parentParts (restrictL P).parts (restrictR P).parts (matchOf X₁ X₂ P.parts) = P.parts := by
  have hsplit : ∀ C ∈ P.parts, C ∩ X₁ ∪ C ∩ X₂ = C := fun C hC => by
    rw [← inter_union_distrib_left, inter_eq_left.2 (P.subset hC)]
  ext t
  rw [mem_parentParts]
  constructor
  · rintro (⟨e, he, rfl⟩ | ⟨htL, htm⟩ | ⟨htR, htm⟩)
    · obtain ⟨C, hC, rfl⟩ := mem_image.1 he
      rw [hsplit C (mem_filter.1 hC).1]
      exact (mem_filter.1 hC).1
    · obtain ⟨hne, C, hC, rfl⟩ := (mem_restrict_parts P _).1 htL
      have h2 : C ∩ X₂ = ∅ := by
        by_contra h2
        exact htm (mem_image.2 ⟨(C ∩ X₁, C ∩ X₂), mem_image.2 ⟨C, mem_filter.2 ⟨hC, hne,
          nonempty_iff_ne_empty.2 h2⟩, rfl⟩, rfl⟩)
      have : C ∩ X₁ = C := by
        have := hsplit C hC
        rw [h2, union_empty] at this
        exact this
      rw [this]
      exact hC
    · obtain ⟨hne, C, hC, rfl⟩ := (mem_restrict_parts P _).1 htR
      have h1 : C ∩ X₁ = ∅ := by
        by_contra h1
        exact htm (mem_image.2 ⟨(C ∩ X₁, C ∩ X₂), mem_image.2 ⟨C, mem_filter.2 ⟨hC,
          nonempty_iff_ne_empty.2 h1, hne⟩, rfl⟩, rfl⟩)
      have : C ∩ X₂ = C := by
        have := hsplit C hC
        rw [h1, empty_union] at this
        exact this
      rw [this]
      exact hC
  · intro ht
    by_cases h1 : (t ∩ X₁).Nonempty <;> by_cases h2 : (t ∩ X₂).Nonempty
    · exact Or.inl ⟨(t ∩ X₁, t ∩ X₂), mem_image.2 ⟨t, mem_filter.2 ⟨ht, h1, h2⟩, rfl⟩,
        hsplit t ht⟩
    · have h2' : t ∩ X₂ = ∅ := not_nonempty_iff_eq_empty.1 h2
      have htX : t ∩ X₁ = t := by
        have := hsplit t ht
        rw [h2', union_empty] at this
        exact this
      refine Or.inr (Or.inl ⟨(mem_restrict_parts P _).2 ⟨htX ▸ h1, t, ht, htX⟩, ?_⟩)
      intro hm
      obtain ⟨e, he, hfe⟩ := mem_image.1 hm
      obtain ⟨C, hC, rfl⟩ := mem_image.1 he
      obtain ⟨hCP, ⟨x, hx⟩, hC2⟩ := mem_filter.1 hC
      have hfe' : C ∩ X₁ = t := hfe
      have hxt : x ∈ t := hfe' ▸ hx
      have := P.eq_of_mem_parts hCP ht (mem_inter.1 hx).1 hxt
      subst this
      exact h2 hC2
    · have h1' : t ∩ X₁ = ∅ := not_nonempty_iff_eq_empty.1 h1
      have htX : t ∩ X₂ = t := by
        have := hsplit t ht
        rw [h1', empty_union] at this
        exact this
      refine Or.inr (Or.inr ⟨(mem_restrict_parts P _).2 ⟨htX ▸ h2, t, ht, htX⟩, ?_⟩)
      intro hm
      obtain ⟨e, he, hfe⟩ := mem_image.1 hm
      obtain ⟨C, hC, rfl⟩ := mem_image.1 he
      obtain ⟨hCP, hC1, ⟨x, hx⟩⟩ := mem_filter.1 hC
      have hfe' : C ∩ X₂ = t := hfe
      have hxt : x ∈ t := hfe' ▸ hx
      have := P.eq_of_mem_parts hCP ht (mem_inter.1 hx).1 hxt
      subst this
      exact h1 hC1
    · exfalso
      obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts ht
      rcases mem_union.1 (P.subset ht hx) with hx1 | hx2
      · exact h1 ⟨x, mem_inter.2 ⟨hx, hx1⟩⟩
      · exact h2 ⟨x, mem_inter.2 ⟨hx, hx2⟩⟩

variable (P₁ : Finpartition X₁) (P₂ : Finpartition X₂) {M : Finset (Finset V × Finset V)}

include hd in
theorem parentParts_inter_left (hM : IsPM P₁.parts P₂.parts M) :
    ((parentParts P₁.parts P₂.parts M).image (· ∩ X₁)).erase ∅ = P₁.parts := by
  obtain ⟨hsub, h1, h2⟩ := hM
  have hl : ∀ e ∈ M, e.1 ∈ P₁.parts := fun e he => (mem_product.1 (hsub he)).1
  have hr : ∀ e ∈ M, e.2 ∈ P₂.parts := fun e he => (mem_product.1 (hsub he)).2
  have hpair : ∀ e ∈ M, (e.1 ∪ e.2) ∩ X₁ = e.1 := fun e he => by
    rw [union_inter_distrib_right, inter_eq_left.2 (P₁.subset (hl e he)),
      disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_left (P₂.subset (hr e he)) hd.symm),
      union_empty]
  ext C
  rw [mem_erase, mem_image]
  constructor
  · rintro ⟨hne, t, ht, rfl⟩
    rcases mem_parentParts.1 ht with ⟨e, he, rfl⟩ | ⟨htL, -⟩ | ⟨htR, -⟩
    · rw [hpair e he]; exact hl e he
    · rwa [inter_eq_left.2 (P₁.subset htL)]
    · exact absurd (disjoint_iff_inter_eq_empty.1
        (disjoint_of_subset_left (P₂.subset htR) hd.symm)) hne
  · intro hC
    refine ⟨P₁.ne_empty hC, ?_⟩
    by_cases hm : C ∈ M.image Prod.fst
    · obtain ⟨e, he, rfl⟩ := mem_image.1 hm
      exact ⟨e.1 ∪ e.2, mem_parentParts.2 (Or.inl ⟨e, he, rfl⟩), hpair e he⟩
    · exact ⟨C, mem_parentParts.2 (Or.inr (Or.inl ⟨hC, hm⟩)), inter_eq_left.2 (P₁.subset hC)⟩

include hd in
theorem parentParts_inter_right (hM : IsPM P₁.parts P₂.parts M) :
    ((parentParts P₁.parts P₂.parts M).image (· ∩ X₂)).erase ∅ = P₂.parts := by
  obtain ⟨hsub, h1, h2⟩ := hM
  have hl : ∀ e ∈ M, e.1 ∈ P₁.parts := fun e he => (mem_product.1 (hsub he)).1
  have hr : ∀ e ∈ M, e.2 ∈ P₂.parts := fun e he => (mem_product.1 (hsub he)).2
  have hpair : ∀ e ∈ M, (e.1 ∪ e.2) ∩ X₂ = e.2 := fun e he => by
    rw [union_inter_distrib_right, inter_eq_left.2 (P₂.subset (hr e he)),
      disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_left (P₁.subset (hl e he)) hd),
      empty_union]
  ext C
  rw [mem_erase, mem_image]
  constructor
  · rintro ⟨hne, t, ht, rfl⟩
    rcases mem_parentParts.1 ht with ⟨e, he, rfl⟩ | ⟨htL, -⟩ | ⟨htR, -⟩
    · rw [hpair e he]; exact hr e he
    · exact absurd (disjoint_iff_inter_eq_empty.1
        (disjoint_of_subset_left (P₁.subset htL) hd)) hne
    · rwa [inter_eq_left.2 (P₂.subset htR)]
  · intro hC
    refine ⟨P₂.ne_empty hC, ?_⟩
    by_cases hm : C ∈ M.image Prod.snd
    · obtain ⟨e, he, rfl⟩ := mem_image.1 hm
      exact ⟨e.1 ∪ e.2, mem_parentParts.2 (Or.inl ⟨e, he, rfl⟩), hpair e he⟩
    · exact ⟨C, mem_parentParts.2 (Or.inr (Or.inr ⟨hC, hm⟩)), inter_eq_left.2 (P₂.subset hC)⟩

include hd in
theorem restrictL_ofTriple (hM : IsPM P₁.parts P₂.parts M) :
    restrictL (ofTriple hd P₁ P₂ hM) = P₁ := by
  apply Finpartition.ext
  rw [restrictL, Finpartition.parts_restrict, ofTriple_parts]
  exact parentParts_inter_left hd P₁ P₂ hM

include hd in
theorem restrictR_ofTriple (hM : IsPM P₁.parts P₂.parts M) :
    restrictR (ofTriple hd P₁ P₂ hM) = P₂ := by
  apply Finpartition.ext
  rw [restrictR, Finpartition.parts_restrict, ofTriple_parts]
  exact parentParts_inter_right hd P₁ P₂ hM

include hd in
theorem matchOf_parentParts (hM : IsPM P₁.parts P₂.parts M) :
    matchOf X₁ X₂ (parentParts P₁.parts P₂.parts M) = M := by
  obtain ⟨hsub, h1, h2⟩ := hM
  have hl : ∀ e ∈ M, e.1 ∈ P₁.parts := fun e he => (mem_product.1 (hsub he)).1
  have hr : ∀ e ∈ M, e.2 ∈ P₂.parts := fun e he => (mem_product.1 (hsub he)).2
  have hp1 : ∀ e ∈ M, (e.1 ∪ e.2) ∩ X₁ = e.1 := fun e he => by
    rw [union_inter_distrib_right, inter_eq_left.2 (P₁.subset (hl e he)),
      disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_left (P₂.subset (hr e he)) hd.symm),
      union_empty]
  have hp2 : ∀ e ∈ M, (e.1 ∪ e.2) ∩ X₂ = e.2 := fun e he => by
    rw [union_inter_distrib_right, inter_eq_left.2 (P₂.subset (hr e he)),
      disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_left (P₁.subset (hl e he)) hd),
      empty_union]
  ext e
  simp only [matchOf, mem_image, mem_filter]
  constructor
  · rintro ⟨t, ⟨ht, hn1, hn2⟩, rfl⟩
    rcases mem_parentParts.1 ht with ⟨e', he', rfl⟩ | ⟨htL, -⟩ | ⟨htR, -⟩
    · rw [hp1 e' he', hp2 e' he']
      exact he'
    · exact absurd (disjoint_iff_inter_eq_empty.1
        (disjoint_of_subset_left (P₁.subset htL) hd)) (nonempty_iff_ne_empty.1 hn2)
    · exact absurd (disjoint_iff_inter_eq_empty.1
        (disjoint_of_subset_left (P₂.subset htR) hd.symm)) (nonempty_iff_ne_empty.1 hn1)
  · intro he
    refine ⟨e.1 ∪ e.2, ⟨mem_parentParts.2 (Or.inl ⟨e, he, rfl⟩), ?_, ?_⟩, ?_⟩
    · rw [hp1 e he]; exact P₁.nonempty_of_mem_parts (hl e he)
    · rw [hp2 e he]; exact P₂.nonempty_of_mem_parts (hr e he)
    · rw [hp1 e he, hp2 e he]

include hd in
theorem ofTriple_restrict (P : Finpartition (X₁ ∪ X₂)) :
    ofTriple hd (restrictL P) (restrictR P) (isPM_matchOf hd P) = P := by
  apply Finpartition.ext
  rw [ofTriple_parts]
  exact parentParts_restrict hd P

end RoundTrip

/-! ### Color partitions and histograms under the bijection -/

section Graph

variable (G : SimpleGraph V) [DecidableRel G.Adj] {X₁ X₂ : Finset V} (hd : Disjoint X₁ X₂)

theorem isColorPartition_restrict {X Y : Finset V} {P : Finpartition X} (h : Y ⊆ X)
    (hP : IsColorPartition G P) : IsColorPartition G (P.restrict h) := by
  intro C hC x hx y hy
  obtain ⟨-, D, hD, rfl⟩ := (mem_restrict_parts P h).1 hC
  exact hP D hD x (mem_inter.1 hx).1 y (mem_inter.1 hy).1

include hd in
theorem compat_matchOf {P : Finpartition (X₁ ∪ X₂)} (hP : IsColorPartition G P) :
    ∀ e ∈ matchOf X₁ X₂ P.parts, Compatible G X₁ X₂ (profile G X₁ e.1) (profile G X₂ e.2) := by
  intro e he
  obtain ⟨C, hC, rfl⟩ := mem_image.1 he
  have hCP := (mem_filter.1 hC).1
  rw [compatible_profile_iff G hd inter_subset_right inter_subset_right]
  intro x hx y hy
  exact hP C hCP x (mem_inter.1 hx).1 y (mem_inter.1 hy).1

include hd in
theorem isColorPartition_ofTriple {P₁ : Finpartition X₁} {P₂ : Finpartition X₂}
    {M : Finset (Finset V × Finset V)} (hM : IsPM P₁.parts P₂.parts M)
    (hP₁ : IsColorPartition G P₁) (hP₂ : IsColorPartition G P₂)
    (hc : ∀ e ∈ M, Compatible G X₁ X₂ (profile G X₁ e.1) (profile G X₂ e.2)) :
    IsColorPartition G (ofTriple hd P₁ P₂ hM) := by
  intro t ht
  rw [ofTriple_parts] at ht
  rcases mem_parentParts.1 ht with ⟨e, he, rfl⟩ | ⟨htL, -⟩ | ⟨htR, -⟩
  · obtain ⟨h1, h2⟩ := mem_product.1 (hM.1 he)
    have hno := (compatible_profile_iff G hd (P₁.subset h1) (P₂.subset h2)).1 (hc e he)
    intro x hx y hy
    rcases mem_union.1 hx with hx | hx <;> rcases mem_union.1 hy with hy | hy
    · exact hP₁ _ h1 x hx y hy
    · exact hno x hx y hy
    · exact fun h => hno y hy x hx h.symm
    · exact hP₂ _ h2 x hx y hy
  · exact hP₁ t htL
  · exact hP₂ t htR

include hd in
/-- The histogram of the parent partition is the parent histogram of the matching. -/
theorem hist_ofTriple {P₁ : Finpartition X₁} {P₂ : Finpartition X₂}
    {M : Finset (Finset V × Finset V)} (hM : IsPM P₁.parts P₂.parts M) :
    hist G (ofTriple hd P₁ P₂ hM) =
      (mergeData G X₁ X₂).parentHist (profile G X₁) (profile G X₂) P₁.parts P₂.parts M := by
  unfold hist
  rw [ofTriple_parts]
  obtain ⟨hsub, h1, h2⟩ := hM
  have hl : ∀ e ∈ M, e.1 ∈ P₁.parts := fun e he => (mem_product.1 (hsub he)).1
  have hr : ∀ e ∈ M, e.2 ∈ P₂.parts := fun e he => (mem_product.1 (hsub he)).2
  -- the three families of parent classes are pairwise disjoint
  have hA : ∀ e ∈ M, ¬ (e.1 ∪ e.2 ⊆ X₁) := fun e he hs => by
    obtain ⟨x, hx⟩ := P₂.nonempty_of_mem_parts (hr e he)
    exact disjoint_left.1 hd (hs (mem_union_right _ hx)) (P₂.subset (hr e he) hx)
  have hA' : ∀ e ∈ M, ¬ (e.1 ∪ e.2 ⊆ X₂) := fun e he hs => by
    obtain ⟨x, hx⟩ := P₁.nonempty_of_mem_parts (hl e he)
    exact disjoint_left.1 hd (P₁.subset (hl e he) hx) (hs (mem_union_left _ hx))
  have d1 : Disjoint (M.image fun e => e.1 ∪ e.2) (P₁.parts.filter (· ∉ M.image Prod.fst)) := by
    rw [disjoint_left]
    intro t ht ht'
    obtain ⟨e, he, rfl⟩ := mem_image.1 ht
    exact hA e he (P₁.subset (mem_filter.1 ht').1)
  have d2 : Disjoint ((M.image fun e => e.1 ∪ e.2) ∪ P₁.parts.filter (· ∉ M.image Prod.fst))
      (P₂.parts.filter (· ∉ M.image Prod.snd)) := by
    rw [disjoint_left]
    intro t ht ht'
    have htR := P₂.subset (mem_filter.1 ht').1
    rcases mem_union.1 ht with ht | ht
    · obtain ⟨e, he, rfl⟩ := mem_image.1 ht
      exact hA' e he htR
    · obtain ⟨x, hx⟩ := P₂.nonempty_of_mem_parts (mem_filter.1 ht').1
      exact disjoint_left.1 hd (P₁.subset (mem_filter.1 ht).1 hx) (htR hx)
  have hinj : Set.InjOn (fun e : Finset V × Finset V => e.1 ∪ e.2) M := by
    intro e he e' he' h
    have h1' : (e.1 ∪ e.2) ∩ X₁ = e.1 := by
      rw [union_inter_distrib_right, inter_eq_left.2 (P₁.subset (hl e he)),
        disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_left (P₂.subset (hr e he)) hd.symm),
        union_empty]
    have h1'' : (e'.1 ∪ e'.2) ∩ X₁ = e'.1 := by
      rw [union_inter_distrib_right, inter_eq_left.2 (P₁.subset (hl e' he')),
        disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_left (P₂.subset (hr e' he')) hd.symm),
        union_empty]
    have : e.1 = e'.1 := by
      rw [← h1', ← h1'']
      exact congrArg (· ∩ X₁) h
    exact h1 e he e' he' this
  unfold MergeData.parentHist
  rw [parentParts, ← disjUnion_eq_union _ _ d2, disjUnion_val,
    ← disjUnion_eq_union _ _ d1, disjUnion_val, image_val_of_injOn hinj, Multiset.map_add,
    Multiset.map_add, Multiset.map_map]
  congr 1
  congr 1
  · refine Multiset.map_congr rfl fun e he => ?_
    simp only [Function.comp_apply, mergeData]
    rw [profile_union, profile_eq_map G subset_union_left, profile_eq_map G subset_union_right]
  · refine Multiset.map_congr rfl fun C hC => ?_
    simp only [mergeData]
    exact profile_eq_map G subset_union_left
  · refine Multiset.map_congr rfl fun C hC => ?_
    simp only [mergeData]
    exact profile_eq_map G subset_union_right

end Graph

end SubspaceConvolution
