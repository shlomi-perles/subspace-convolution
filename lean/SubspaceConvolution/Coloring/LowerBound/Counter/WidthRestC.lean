/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.Counter.WidthRest

/-!
# Lemma C.4, part 3: the remaining edges at a cut in the constraint part

Let the cut `X` contain the selector `s_{C₀}` of the last constraint `C₀` it meets.  After
removing the register edges, the test-clique edges and the private edges, the remaining nonzero
rows have at most ten different future neighborhoods:

* `B_*`, the selectors of completed constraints and the anchors whose `I`-vertex is in the past
  see all future old vertices (`PAll`); `A`/`I`-vertices of completed constraints see exactly
  the future `D`-vertices (`PD`);
* the current selector `s_{C₀}` (`PSel`);
* the current `A`-vertices, one neighborhood for each `x ∈ X_{C₀}` (`PA`, at most four);
* the current `I`-vertices, according to whether their mini-constraint is current or finished
  (`PI`, `PI'`);
* a split pair `m_b, b` (`PAnc`).
-/

open Finset Matrix

set_option linter.unusedSectionVars false

namespace SubspaceConvolution.Counter

variable {I : MinCSP}

section CaseC

variable {X : Finset (Vtx I)} (hX : IsCut X) {C₀ : Fin I.p} (hsel : Vtx.sel C₀ ∈ X)
  (hmax : ∀ C, Vtx.sel C ∈ X → C ≤ C₀)

include hX hsel

/-! ### The past and the future of the cut -/

theorem caseC_row_mem (i : Fin (d I)) (A : Mat I) (t : Fin I.n) : Vtx.row i A t ∈ X :=
  hX.mem_of_lt hsel (by simp [key, List.cons_lt_cons_iff])

theorem caseC_star_mem (t : Fin (Q I - I.W)) : Vtx.star t ∈ X :=
  hX.mem_of_lt hsel (by simp [key, List.cons_lt_cons_iff])

theorem caseC_sel_gt {C : Fin I.p} (hy : Vtx.sel C ∉ X) : C₀ < C := by
  by_contra h
  rcases lt_or_eq_of_le (not_lt.1 h) with h' | h'
  · exact hy (hX.mem_of_lt hsel (by simpa [key, List.cons_lt_cons_iff] using h'))
  · exact hy (h' ▸ hsel)

theorem caseC_anc_ge {b : IIdx I} (hy : Vtx.anc b ∉ X) : C₀ ≤ b.C := by
  by_contra h
  exact hy (hX.mem_of_lt hsel (by simpa [key, List.cons_lt_cons_iff] using not_le.1 h))

theorem caseC_aV_ge {C : Fin I.p} {x : Fin I.k} {hx : x ∈ I.scope C} {j : Fin (d I)}
    {t : Fin I.n} (hy : Vtx.aV C x hx j t ∉ X) : C₀ ≤ C := by
  by_contra h
  exact hy (hX.mem_of_lt hsel (by simpa [key, List.cons_lt_cons_iff] using not_le.1 h))

theorem caseC_iV_ge {b : IIdx I} (hy : Vtx.iV b ∉ X) : C₀ ≤ b.C := by
  by_contra h
  exact hy (hX.mem_of_lt hsel (by simpa [key, List.cons_lt_cons_iff] using not_le.1 h))

omit hsel in
include hmax in
theorem caseC_anc_le {b : IIdx I} (hv : Vtx.anc b ∈ X) : b.C ≤ C₀ :=
  hmax _ (hX.mem_of_lt hv (by simp [key, List.cons_lt_cons_iff]))

omit hsel in
include hmax in
theorem caseC_aV_le {C : Fin I.p} {x : Fin I.k} {hx : x ∈ I.scope C} {j : Fin (d I)}
    {t : Fin I.n} (hv : Vtx.aV C x hx j t ∈ X) : C ≤ C₀ :=
  hmax _ (hX.mem_of_lt hv (by simp [key, List.cons_lt_cons_iff]))

omit hsel in
include hmax in
theorem caseC_iV_le {b : IIdx I} (hv : Vtx.iV b ∈ X) : b.C ≤ C₀ :=
  hmax _ (hX.mem_of_lt hv (by simp [key, List.cons_lt_cons_iff]))

/-! ### The remaining rows -/

theorem caseC_rest_row (i : Fin (d I)) (A : Mat I) (t : Fin I.n) :
    cutRow (Mpart I .rest) X (.row i A t) = 0 := by
  rw [rest_row_eq (caseC_row_mem hX hsel i A t)]
  apply nbVec_eq_zero
  intro y hy h
  cases y <;> simp only [PRow] at h
  exact hy (caseC_row_mem hX hsel _ _ _)

theorem caseC_rest_star (t : Fin (Q I - I.W)) :
    cutRow (Mpart I .rest) X (.star t) = nbVec X PAll := by
  apply cutRow_Mpart_eq
  intro y hy
  cases y
  case star t' => exact absurd (caseC_star_mem hX hsel t') hy
  all_goals simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PAll]

/-- The selectors of completed constraints see all future old vertices. -/
theorem caseC_rest_sel_lt {C : Fin I.p} (hC : C < C₀) :
    cutRow (Mpart I .rest) X (.sel C) = nbVec X PAll := by
  apply cutRow_Mpart_eq
  intro y hy
  cases y
  case star t' => exact absurd (caseC_star_mem hX hsel t') hy
  case row i A t => exact absurd (caseC_row_mem hX hsel i A t) hy
  case sel C' =>
    have := caseC_sel_gt hX hsel hy
    have hne : C ≠ C' := by rintro rfl; exact absurd (hC.trans this) (lt_irrefl _)
    simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PAll, hne]
  case iV b =>
    have := caseC_iV_ge hX hsel hy
    have hne : b.C ≠ C := by rintro h; rw [h] at this; exact absurd (hC.trans_le this) (lt_irrefl _)
    simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PAll, hne]
  all_goals simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PAll]

/-- The current selector. -/
theorem caseC_rest_sel_eq : cutRow (Mpart I .rest) X (.sel C₀) = nbVec X (PSel C₀) := by
  apply cutRow_Mpart_eq
  intro y hy
  cases y
  case star t' => exact absurd (caseC_star_mem hX hsel t') hy
  case row i A t => exact absurd (caseC_row_mem hX hsel i A t) hy
  case sel C' =>
    have := caseC_sel_gt hX hsel hy
    simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PSel, this.ne]
  all_goals simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PSel, eq_comm]

/-- Anchors whose `I`-vertex is in the past see all future old vertices. -/
theorem caseC_rest_anc_all {b : IIdx I} (hv : Vtx.anc b ∈ X) (hbv : Vtx.iV b ∈ X) :
    cutRow (Mpart I .rest) X (.anc b) = nbVec X PAll := by
  apply cutRow_Mpart_eq
  intro y hy
  cases y
  case star t' => exact absurd (caseC_star_mem hX hsel t') hy
  case row i A t => exact absurd (caseC_row_mem hX hsel i A t) hy
  case anc b' =>
    have hne : b ≠ b' := by rintro rfl; exact hy hv
    simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PAll, hne]
  case iV b' =>
    have hne : b' ≠ b := by rintro rfl; exact hy hbv
    simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PAll, hne]
  case aV C x hx j t =>
    -- the `A`-cliques of `b.C` precede `m_b`
    have hne : ¬ (C = b.C ∧ x = b.x) := by
      rintro ⟨rfl, rfl⟩
      exact hy (hX.mem_of_lt hv (by simp [key, List.cons_lt_cons_iff]))
    simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PAll, hne]
  all_goals simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PAll]

/-- The anchor of a split pair `m_b, b`. -/
theorem caseC_rest_anc_split {b : IIdx I} (hv : Vtx.anc b ∈ X) :
    cutRow (Mpart I .rest) X (.anc b) = nbVec X (PAnc b) := by
  apply cutRow_Mpart_eq
  intro y hy
  cases y
  case star t' => exact absurd (caseC_star_mem hX hsel t') hy
  case row i A t => exact absurd (caseC_row_mem hX hsel i A t) hy
  case anc b' =>
    have hne : b ≠ b' := by rintro rfl; exact hy hv
    simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PAnc, hne]
  case aV C x hx j t =>
    have hne : ¬ (C = b.C ∧ x = b.x) := by
      rintro ⟨rfl, rfl⟩
      exact hy (hX.mem_of_lt hv (by simp [key, List.cons_lt_cons_iff]))
    simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PAnc, hne]
  all_goals simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PAnc]

/-- `A`-vertices of completed constraints see exactly the future `D`-vertices. -/
theorem caseC_rest_aV_lt {C : Fin I.p} {x : Fin I.k} {hx : x ∈ I.scope C} {j : Fin (d I)}
    {t : Fin I.n} (hj : (j : ℕ) = 0) (hC : C < C₀) :
    cutRow (Mpart I .rest) X (.aV C x hx j t) = nbVec X PD := by
  apply cutRow_Mpart_eq
  intro y hy
  cases y
  case star t' => exact absurd (caseC_star_mem hX hsel t') hy
  case row i A t => exact absurd (caseC_row_mem hX hsel i A t) hy
  case anc b =>
    have := caseC_anc_ge hX hsel hy
    have hne : ¬ (C = b.C ∧ x = b.x) := by
      rintro ⟨rfl, -⟩; exact absurd (hC.trans_le this) (lt_irrefl _)
    simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PD, hj, hne]
  case iV b =>
    have := caseC_iV_ge hX hsel hy
    have hne : ¬ (b.C = C ∧ b.x = x) := by
      rintro ⟨h, -⟩; rw [h] at this; exact absurd (hC.trans_le this) (lt_irrefl _)
    simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PD, hj]
    exact fun h1 h2 => hne ⟨h1, h2⟩
  all_goals simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PD, hj]

/-- The current `A`-vertices of the block `x`. -/
theorem caseC_rest_aV_eq {x : Fin I.k} {hx : x ∈ I.scope C₀} {j : Fin (d I)} {t : Fin I.n}
    (hj : (j : ℕ) = 0) : cutRow (Mpart I .rest) X (.aV C₀ x hx j t) = nbVec X (PA C₀ x) := by
  apply cutRow_Mpart_eq
  intro y hy
  cases y
  case star t' => exact absurd (caseC_star_mem hX hsel t') hy
  case row i A t => exact absurd (caseC_row_mem hX hsel i A t) hy
  all_goals simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PA, hj, eq_comm]

/-- `I`-vertices of completed constraints see exactly the future `D`-vertices. -/
theorem caseC_rest_iV_lt {b : IIdx I} (hC : b.C < C₀) :
    cutRow (Mpart I .rest) X (.iV b) = nbVec X PD := by
  apply cutRow_Mpart_eq
  intro y hy
  cases y
  case star t' => exact absurd (caseC_star_mem hX hsel t') hy
  case row i A t => exact absurd (caseC_row_mem hX hsel i A t) hy
  case sel C' =>
    have := caseC_sel_gt hX hsel hy
    have hne : b.C ≠ C' := by rintro h; rw [← h] at this; exact absurd (hC.trans this) (lt_irrefl _)
    simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PD, hne]
  case anc b' =>
    have := caseC_anc_ge hX hsel hy
    have hne : b ≠ b' := by rintro rfl; exact absurd (hC.trans_le this) (lt_irrefl _)
    simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PD, hne]
  case iV b' =>
    have := caseC_iV_ge hX hsel hy
    have hne : b.C ≠ b'.C := by rintro h; rw [← h] at this; exact absurd (hC.trans_le this) (lt_irrefl _)
    simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PD, hne, Ne.symm hne]
  case aV C x hx j t =>
    have := caseC_aV_ge hX hsel hy
    have hne : b.C ≠ C := by rintro h; rw [← h] at this; exact absurd (hC.trans_le this) (lt_irrefl _)
    simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PD, hne]
  case eV => simp [ecls, Vtx.isEV, adj_iff, edge, PD]

/-- The current `I`-vertices. -/
theorem caseC_rest_iV_eq {b : IIdx I} (hv : Vtx.iV b ∈ X) (hC : b.C = C₀) :
    cutRow (Mpart I .rest) X (.iV b) = nbVec X (PI C₀ b.R) := by
  apply cutRow_Mpart_eq
  intro y hy
  cases y
  case star t' => exact absurd (caseC_star_mem hX hsel t') hy
  case row i A t => exact absurd (caseC_row_mem hX hsel i A t) hy
  case sel C' =>
    have := caseC_sel_gt hX hsel hy
    have hne : b.C ≠ C' := by rw [hC]; exact this.ne
    simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PI, hne]
  case anc b' =>
    have hne : b ≠ b' := by
      rintro rfl
      exact hy (hX.mem_of_lt hv (by simp [key, List.cons_lt_cons_iff]))
    simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PI, hne]
  case iV b' =>
    have hne : b ≠ b' := by rintro rfl; exact hy hv
    simp only [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PI, ne_eq, Vtx.iV.injEq, hne,
      not_false_eq_true, true_and, Bool.or_self, Bool.false_eq_true, ite_false, bne_self_eq_false,
      Bool.and_self, and_true, hC]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1.symm, Ne.symm h2⟩
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact Or.inr ⟨h1, h2⟩
  case aV C x hx j t =>
    have hne : ¬ ((j : ℕ) = 0 ∧ b.C = C ∧ b.x = x) := by
      rintro ⟨-, h1, -⟩
      subst h1
      exact hy (hX.mem_of_lt hv (by simp [key, List.cons_lt_cons_iff]))
    simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PI]
    exact fun h1 h2 h3 => hne ⟨h1, h2, h3⟩
  case eV => simp [ecls, Vtx.isEV, adj_iff, edge, PI]

/-- A finished mini-constraint of the current constraint. -/
theorem nbVec_PI_eq {R : ℕ} (hfin : ∀ b : IIdx I, b.C = C₀ → (b.R : ℕ) = R → Vtx.iV b ∈ X) :
    nbVec X (PI C₀ R) = nbVec X (PI' C₀) := by
  funext y
  simp only [nbVec]
  by_cases hy : y ∈ X
  · simp [hy]
  · cases y <;> simp [PI, PI', hy]
    rename_i b
    by_cases hb : b.C = C₀
    · have : ¬ (b.R : ℕ) = R := fun h => hy (hfin b hb h)
      simp [hb, this]
    · simp [hb]

/-! ### Counting the split mini-constraints and the split pairs -/

omit hsel in
/-- The split mini-constraints of `C₀`. -/
def splitR (X : Finset (Vtx I)) (C₀ : Fin I.p) : Finset ℕ :=
  (range (I.numMini C₀)).filter fun R => ∃ b b' : IIdx I, b.C = C₀ ∧ b'.C = C₀ ∧
    (b.R : ℕ) = R ∧ (b'.R : ℕ) = R ∧ Vtx.iV b ∈ X ∧ Vtx.iV b' ∉ X

omit hsel in
theorem card_splitR_le : (splitR X C₀).card ≤ 1 := by
  rw [card_le_one]
  intro R hR R' hR'
  simp only [splitR, mem_filter, mem_range] at hR hR'
  obtain ⟨-, b₁, b₂, hb₁, hb₂, hR₁, hR₂, hm₁, hm₂⟩ := hR
  obtain ⟨-, b₁', b₂', hb₁', hb₂', hR₁', hR₂', hm₁', hm₂'⟩ := hR'
  have h1 := hX _ hm₁' _ hm₂
  have h2 := hX _ hm₁ _ hm₂'
  simp only [key, List.cons_lt_cons_iff, lt_self_iff_false, true_and, false_or, not_or,
    not_and, not_lt, hb₁, hb₂, hb₁', hb₂'] at h1 h2
  omega

omit hsel in
/-- The split pairs `m_b, b`. -/
def splitB (X : Finset (Vtx I)) : Finset (IIdx I) :=
  univ.filter fun b => Vtx.anc b ∈ X ∧ Vtx.iV b ∉ X

omit hsel in
theorem card_splitB_le : (splitB X).card ≤ 1 := by
  rw [card_le_one]
  intro b hb b' hb'
  simp only [splitB, mem_filter, mem_univ, true_and] at hb hb'
  have h1 := hX _ hb.1 _ hb'.2
  have h2 := hX _ hb'.1 _ hb.2
  simp only [key, List.cons_lt_cons_iff, lt_self_iff_false, true_and, false_or, not_or,
    not_and, not_lt] at h1 h2
  exact IIdx.ext_val (Fin.ext (by omega)) (by omega) (Fin.ext (by omega)) (by omega)

/-! ### The bound -/

omit hsel in
/-- The (at most ten) future neighborhoods. -/
def nbSet (X : Finset (Vtx I)) (C₀ : Fin I.p) : Finset (Vtx I → F2) :=
  ({nbVec X PAll, nbVec X PD, nbVec X (PSel C₀), nbVec X (PI' C₀)} : Finset (Vtx I → F2)) ∪
    (I.scope C₀).image (fun x => nbVec X (PA C₀ x)) ∪
    (splitR X C₀).image (fun R => nbVec X (PI C₀ R)) ∪
    (splitB X).image (fun b => nbVec X (PAnc b))

omit hsel in
theorem card_nbSet_le (hI : I.Normalized) : (nbSet X C₀).card ≤ 10 := by
  unfold nbSet
  set A := ({nbVec X PAll, nbVec X PD, nbVec X (PSel C₀), nbVec X (PI' C₀)} :
    Finset (Vtx I → F2)) with hA
  set B := (I.scope C₀).image (fun x => nbVec X (PA C₀ x)) with hB
  set C := (splitR X C₀).image (fun R => nbVec X (PI C₀ R)) with hC
  set D := (splitB X).image (fun b => nbVec X (PAnc b)) with hD
  have h1 : A.card ≤ 4 := card_le_four
  have h2 : B.card ≤ 4 := card_image_le.trans (hI.scope_card C₀)
  have h3 : C.card ≤ 1 := card_image_le.trans (card_splitR_le hX)
  have h4 : D.card ≤ 1 := card_image_le.trans (card_splitB_le hX)
  have u1 : (A ∪ B ∪ C ∪ D).card ≤ (A ∪ B ∪ C).card + D.card := card_union_le _ _
  have u2 : (A ∪ B ∪ C).card ≤ (A ∪ B).card + C.card := card_union_le _ _
  have u3 : (A ∪ B).card ≤ A.card + B.card := card_union_le _ _
  omega

include hmax in
/-- **Case C: the remaining edges have cut-rank at most ten.** -/
theorem matCutRank_Mrest_le_caseC (hI : I.Normalized) : matCutRank (Mpart I .rest) X ≤ 10 := by
  refine (matCutRank_le_card_of_mem_or_zero (nbSet X C₀) fun v hv => ?_).trans
    (card_nbSet_le hX hI)
  have mem1 : ∀ f ∈ ({nbVec X PAll, nbVec X PD, nbVec X (PSel C₀), nbVec X (PI' C₀)} :
      Finset (Vtx I → F2)), f ∈ nbSet X C₀ := fun f hf =>
    mem_union_left _ (mem_union_left _ (mem_union_left _ hf))
  cases v with
  | row i A t => exact Or.inl (caseC_rest_row hX hsel i A t)
  | star t => exact Or.inr (mem1 _ (by simp [caseC_rest_star hX hsel t]))
  | sel C =>
    right
    rcases lt_or_eq_of_le (hmax C hv) with hC | rfl
    · exact mem1 _ (by simp [caseC_rest_sel_lt hX hsel hC])
    · exact mem1 _ (by simp [caseC_rest_sel_eq hX hsel])
  | anc b =>
    right
    by_cases hbv : Vtx.iV b ∈ X
    · exact mem1 _ (by simp [caseC_rest_anc_all hX hsel hv hbv])
    · rw [caseC_rest_anc_split hX hsel hv]
      exact mem_union_right _ (mem_image_of_mem _ (by simp [splitB, hv, hbv]))
  | aV C x hx j t =>
    by_cases hj : (j : ℕ) = 0
    · right
      rcases lt_or_eq_of_le (caseC_aV_le hX hmax hv) with hC | rfl
      · exact mem1 _ (by simp [caseC_rest_aV_lt hX hsel hj hC])
      · rw [caseC_rest_aV_eq hX hsel hj]
        exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_image_of_mem _ hx)))
    · exact Or.inl (rest_aV_eq_zero hj)
  | iV b =>
    right
    rcases lt_or_eq_of_le (caseC_iV_le hX hmax hv) with hC | hC
    · exact mem1 _ (by simp [caseC_rest_iV_lt hX hsel hC])
    · rw [caseC_rest_iV_eq hX hsel hv hC]
      by_cases hfin : ∀ b' : IIdx I, b'.C = C₀ → (b'.R : ℕ) = b.R → Vtx.iV b' ∈ X
      · rw [nbVec_PI_eq hX hsel hfin]
        exact mem1 _ (by simp)
      · push Not at hfin
        obtain ⟨b', hb'C, hb'R, hb'⟩ := hfin
        refine mem_union_left _ (mem_union_right _ (mem_image_of_mem _ ?_))
        simp only [splitR, mem_filter, mem_range]
        refine ⟨?_, b, b', hC, hb'C, rfl, hb'R, hv, hb'⟩
        calc (b.R : ℕ) < I.numMini b.C := b.R.isLt
          _ = I.numMini C₀ := by rw [hC]
  | eV C x hx t => exact Or.inl rest_eV_eq_zero

end CaseC

end SubspaceConvolution.Counter
