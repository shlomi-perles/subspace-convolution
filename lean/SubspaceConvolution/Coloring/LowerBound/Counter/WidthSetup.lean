/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.Counter.Lemmas

/-!
# Lemma C.4, part 1: cuts of the layout and the easy parts of the cut-rank bound

* Every prefix of `layout I` is a *cut*: a set `X` closed downwards under the sort key
  (`isCut_prefixSet`).
* The adjacency matrix splits as `M_reg + M_test + M_priv + M_rest` according to the class of
  the edge (`adjMatrix_eq`): register edges (incident to exactly one row vertex), edges inside
  test cliques, private edges (incident to a vertex of some `E_{C,x}`), and the rest.
* For every cut: `M_reg` has cut-rank at most `2d` (it factors through the register labels in
  `F₂^{2d}`; the universal columns to `D` and to the `I`-vertices are `(1,…,1,0,…,0)`, since the
  first `d` coordinates of a label `(e_i, a)` sum to one), and `M_test`, `M_priv` have cut-rank
  at most one (at most one test clique, resp. palette block, is split).
-/

open Finset Matrix

set_option linter.unusedSectionVars false

namespace SubspaceConvolution.Counter

variable {I : MinCSP}

/-! ## Cuts -/

/-- A *cut*: a set of vertices closed downwards under the layout key. -/
def IsCut (X : Finset (Vtx I)) : Prop := ∀ v ∈ X, ∀ w ∉ X, ¬ key I w < key I v

theorem IsCut.mem_of_lt {X : Finset (Vtx I)} (hX : IsCut X) {v w : Vtx I} (hv : v ∈ X)
    (h : key I w < key I v) : w ∈ X := by
  by_contra hw
  exact hX v hv w hw h

theorem IsCut.not_mem_of_lt {X : Finset (Vtx I)} (hX : IsCut X) {v w : Vtx I} (hw : w ∉ X)
    (h : key I w < key I v) : v ∉ X := fun hv => hw (hX.mem_of_lt hv h)

/-- Every prefix of the layout is a cut. -/
theorem isCut_prefixSet (i : ℕ) : IsCut ((layout I).prefixSet i) := by
  intro v hv w hw
  simp only [LinearLayout.prefixSet, List.mem_toFinset] at hv hw
  have hsort : (layout I).order.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  rw [← List.take_append_drop i (layout I).order, List.pairwise_append] at hsort
  have hw' : w ∈ (layout I).order.drop i := by
    have := (layout I).mem_order w
    rw [← List.take_append_drop i (layout I).order, List.mem_append] at this
    exact this.resolve_left hw
  have hvw : v ≤ w := hsort.2.2 v hv w hw'
  exact not_lt.2 hvw

/-! ## Kinds of vertices and classes of edges -/

/-- `v` is a register vertex. -/
def Vtx.isRow : Vtx I → Bool
  | .row .. => true
  | _ => false

/-- `v` is a vertex of a test clique `A^{(j)}_{C,x}` (including `A_{C,x}`). -/
def Vtx.isAV : Vtx I → Bool
  | .aV .. => true
  | _ => false

/-- `v` is a vertex of a private clique `E_{C,x}`. -/
def Vtx.isEV : Vtx I → Bool
  | .eV .. => true
  | _ => false

/-- The classes of edges. -/
inductive ECls
  | reg | test | priv | rest
  deriving DecidableEq

/-- The class of a pair: private (incident to `E`), register (incident to exactly one row
vertex), test (inside the test cliques), or the rest. -/
def ecls (v w : Vtx I) : ECls :=
  if v.isEV || w.isEV then .priv
  else if v.isRow != w.isRow then .reg
  else if v.isAV && w.isAV then .test
  else .rest

/-- The part of the adjacency matrix formed by the edges of class `c`. -/
def Mpart (I : MinCSP) (c : ECls) : Matrix (Vtx I) (Vtx I) F2 := fun v w =>
  if (graph I).Adj v w ∧ ecls v w = c then 1 else 0

theorem ite_split (P : Prop) [Decidable P] (c : ECls) :
    (if P then (1 : F2) else 0) = (if P ∧ c = .reg then 1 else 0) +
      (if P ∧ c = .test then 1 else 0) + (if P ∧ c = .priv then 1 else 0) +
      (if P ∧ c = .rest then 1 else 0) := by
  by_cases h : P <;> cases c <;> simp [h]

theorem adjMatrix_eq :
    (graph I).adjMatrix F2 = Mpart I .reg + Mpart I .test + Mpart I .priv + Mpart I .rest := by
  ext v w
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.add_apply, SimpleGraph.adjMatrix_apply]
  exact ite_split ((graph I).Adj v w) (ecls v w)

theorem cutRank_le_parts (X : Finset (Vtx I)) :
    cutRank (graph I) X ≤ matCutRank (Mpart I .reg) X + matCutRank (Mpart I .test) X +
      matCutRank (Mpart I .priv) X + matCutRank (Mpart I .rest) X := by
  rw [cutRank, adjMatrix_eq]
  have h1 := matCutRank_add_le (M := Mpart I .reg + Mpart I .test + Mpart I .priv)
    (M' := Mpart I .rest) (X := X)
  have h2 := matCutRank_add_le (M := Mpart I .reg + Mpart I .test) (M' := Mpart I .priv) (X := X)
  have h3 := matCutRank_add_le (M := Mpart I .reg) (M' := Mpart I .test) (X := X)
  omega

/-- A cut row equals the indicator of a future neighborhood. -/
def nbVec (X : Finset (Vtx I)) (P : Vtx I → Prop) [DecidablePred P] : Vtx I → F2 :=
  fun y => if y ∉ X ∧ P y then 1 else 0

theorem cutRow_Mpart_eq {X : Finset (Vtx I)} {c : ECls} {v : Vtx I} {P : Vtx I → Prop}
    [DecidablePred P] (h : ∀ y ∉ X, ((graph I).Adj v y ∧ ecls v y = c ↔ P y)) :
    cutRow (Mpart I c) X v = nbVec X P := by
  funext y
  simp only [cutRow_apply, nbVec, Mpart]
  by_cases hy : y ∈ X
  · simp [hy]
  · simp only [hy, ite_false, not_false_eq_true, true_and]
    exact if_congr (h y hy) rfl rfl

theorem nbVec_eq_zero {X : Finset (Vtx I)} {P : Vtx I → Prop} [DecidablePred P]
    (h : ∀ y ∉ X, ¬ P y) : nbVec X P = 0 := by
  funext y
  simp only [nbVec, Pi.zero_apply]
  by_cases hy : y ∈ X
  · simp [hy]
  · simp [hy, h y hy]

theorem cutRow_Mpart_eq_zero {X : Finset (Vtx I)} {c : ECls} {v : Vtx I}
    (h : ∀ y ∉ X, ¬ ((graph I).Adj v y ∧ ecls v y = c)) : cutRow (Mpart I c) X v = 0 := by
  funext y
  simp only [cutRow_apply, Mpart, Pi.zero_apply]
  split_ifs with hy h'
  · rfl
  · exact absurd h' (h y hy)
  · rfl

/-! ## Some key comparisons -/

theorem key_row_lt {i : Fin (d I)} {A : Mat I} {t : Fin I.n} {v : Vtx I} (hv : v.isRow = false) :
    key I (.row i A t) < key I v := by
  cases v <;> simp_all [Vtx.isRow, key, List.cons_lt_cons_iff]

/-! ## The register part -/

/-- The left factor: the label `(e_i, A i)` of a register vertex. -/
def regP : Vtx I → Fin (d I) ⊕ Fin (d I) → F2
  | .row i A _ => regLabel i (A i)
  | _ => 0

/-- The right factor: the test vector `t_{enc x, j}` of a test vertex, and `(1, …, 1, 0, …, 0)`
for the vertices of `D` and the `I`-vertices (which are complete to all rows). -/
def regQ : Vtx I → Fin (d I) ⊕ Fin (d I) → F2
  | .aV _ x _ j _ => testVec (enc I x) j
  | .sel _ => Sum.elim 1 0
  | .anc _ => Sum.elim 1 0
  | .iV _ => Sum.elim 1 0
  | _ => 0

theorem regLabel_dotProduct_ones {m : ℕ} (i : Fin m) (a : Fin m → F2) :
    regLabel i a ⬝ᵥ Sum.elim 1 0 = 1 := by
  simp [dotProduct, regLabel, Fintype.sum_sum_type, Pi.single_apply]

theorem F2_ite_eq_one (a : F2) : (if a = 1 then 1 else 0 : F2) = a := by
  revert a
  decide

theorem Mreg_eq {X : Finset (Vtx I)} (hX : IsCut X) {v w : Vtx I} (hv : v ∈ X) (hw : w ∉ X) :
    Mpart I .reg v w = regP v ⬝ᵥ regQ w := by
  cases hrow : v.isRow
  · -- `v` is not a register vertex: `w` is not one either
    have hw' : w.isRow = false := by
      cases hw'' : w.isRow
      · rfl
      · exfalso
        cases w <;> simp only [Vtx.isRow, reduceCtorEq] at hw''
        exact hX v hv _ hw (key_row_lt hrow)
    have : regP v = 0 := by cases v <;> simp_all [Vtx.isRow, regP]
    rw [this, zero_dotProduct]
    simp only [Mpart, ecls, hrow, hw', bne_self_eq_false]
    split_ifs with h1 h2 <;> simp_all
  · cases v <;> simp only [Vtx.isRow, Bool.false_eq_true] at hrow
    rename_i i A t
    cases w <;> simp [Mpart, ecls, Vtx.isRow, Vtx.isEV, Vtx.isAV, regP, regQ, adj_iff, edge,
      regLabel_dotProduct_ones, regLabel_dotProduct_testVec]
    exact F2_ite_eq_one _

/-- **The register edges have cut-rank at most `2d`.** -/
theorem matCutRank_Mreg_le {X : Finset (Vtx I)} (hX : IsCut X) :
    matCutRank (Mpart I .reg) X ≤ d I + d I := by
  refine matCutRank_le_of_factor (fun v r => regP v (finSumFinEquiv.symm r))
    (fun w r => regQ w (finSumFinEquiv.symm r)) fun v hv w hw => ?_
  rw [Mreg_eq hX hv hw, dotProduct]
  exact (Equiv.sum_comp finSumFinEquiv.symm (fun s => regP v s * regQ w s)).symm

/-! ## The test cliques -/

/-- The test clique `(C, x, j)` containing a vertex. -/
def testId : Vtx I → Option (Fin I.p × Fin I.k × Fin (d I))
  | .aV C x _ j _ => some (C, x, j)
  | _ => none

/-- The split test cliques. -/
def splitT (X : Finset (Vtx I)) : Finset (Fin I.p × Fin I.k × Fin (d I)) :=
  univ.filter fun c => (∃ v ∈ X, testId v = some c) ∧ (∃ w ∉ X, testId w = some c)

theorem card_splitT_le {X : Finset (Vtx I)} (hX : IsCut X) : (splitT X).card ≤ 1 := by
  rw [card_le_one]
  intro c hc c' hc'
  simp only [splitT, mem_filter, mem_univ, true_and] at hc hc'
  obtain ⟨⟨v, hv, hvc⟩, ⟨w, hw, hwc⟩⟩ := hc
  obtain ⟨⟨v', hv', hvc'⟩, ⟨w', hw', hwc'⟩⟩ := hc'
  have h1 := hX v' hv' w hw
  have h2 := hX v hv w' hw'
  obtain ⟨C, x, j⟩ := c
  obtain ⟨C', x', j'⟩ := c'
  cases v <;> simp only [testId, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hvc
  cases w <;> simp only [testId, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hwc
  cases v' <;> simp only [testId, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hvc'
  cases w' <;> simp only [testId, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hwc'
  obtain ⟨rfl, rfl, rfl⟩ := hvc
  obtain ⟨rfl, rfl, rfl⟩ := hwc
  obtain ⟨rfl, rfl, rfl⟩ := hvc'
  obtain ⟨rfl, rfl, rfl⟩ := hwc'
  simp only [key, List.cons_lt_cons_iff, lt_self_iff_false, true_and, false_or, not_or,
    not_and, not_lt] at h1 h2
  simp only [Prod.mk.injEq]
  refine ⟨Fin.ext (by omega), Fin.ext (by omega), Fin.ext (by omega)⟩

/-- **At most one test clique is split: the test-clique edges have cut-rank at most one.** -/
theorem matCutRank_Mtest_le {X : Finset (Vtx I)} (hX : IsCut X) :
    matCutRank (Mpart I .test) X ≤ 1 := by
  refine (matCutRank_le_card_of_mem_or_zero ((splitT X).image fun c =>
    nbVec X (fun y => testId y = some c)) fun v hv => ?_).trans
    (card_image_le.trans (card_splitT_le hX))
  cases hv' : testId v with
  | none =>
    left
    apply cutRow_Mpart_eq_zero
    intro y _ ⟨_, hc⟩
    cases v <;> simp only [testId, reduceCtorEq] at hv'
    all_goals cases y <;> simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV] at hc
  | some c =>
    have hrow : cutRow (Mpart I .test) X v = nbVec X (fun y => testId y = some c) := by
      apply cutRow_Mpart_eq
      intro y hy
      cases v <;> simp only [testId, reduceCtorEq, Option.some.injEq] at hv'
      subst hv'
      have hne : Vtx.aV _ _ _ _ _ ≠ y := fun h => hy (h ▸ hv)
      cases y <;> simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, testId, hne,
        eq_comm]
    rw [hrow]
    by_cases hsplit : ∃ w ∉ X, testId w = some c
    · right
      exact mem_image_of_mem _ (by simp [splitT]; exact ⟨⟨v, hv, hv'⟩, hsplit⟩)
    · left
      apply nbVec_eq_zero
      intro y hy h
      exact hsplit ⟨y, hy, h⟩

/-! ## The private cliques -/

/-- The palette block `(C, x)` containing a vertex. -/
def blockId : Vtx I → Option (Fin I.p × Fin I.k)
  | .aV C x _ _ _ => some (C, x)
  | .eV C x _ _ => some (C, x)
  | _ => none

/-- The private clique `E_{C,x}` containing a vertex. -/
def eId : Vtx I → Option (Fin I.p × Fin I.k)
  | .eV C x _ _ => some (C, x)
  | _ => none

/-- The split palette blocks (some vertex in the past, some private vertex in the future). -/
def splitP (X : Finset (Vtx I)) : Finset (Fin I.p × Fin I.k) :=
  univ.filter fun c => (∃ v ∈ X, blockId v = some c) ∧ (∃ w ∉ X, eId w = some c)

theorem card_splitP_le {X : Finset (Vtx I)} (hX : IsCut X) : (splitP X).card ≤ 1 := by
  rw [card_le_one]
  intro c hc c' hc'
  simp only [splitP, mem_filter, mem_univ, true_and] at hc hc'
  obtain ⟨⟨v, hv, hvc⟩, ⟨w, hw, hwc⟩⟩ := hc
  obtain ⟨⟨v', hv', hvc'⟩, ⟨w', hw', hwc'⟩⟩ := hc'
  have h1 := hX v' hv' w hw
  have h2 := hX v hv w' hw'
  obtain ⟨C, x⟩ := c
  obtain ⟨C', x'⟩ := c'
  cases w <;> simp only [eId, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hwc
  cases w' <;> simp only [eId, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hwc'
  obtain ⟨rfl, rfl⟩ := hwc
  obtain ⟨rfl, rfl⟩ := hwc'
  simp only [Prod.mk.injEq]
  cases v <;> simp only [blockId, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hvc <;>
    cases v' <;> simp only [blockId, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hvc' <;>
    obtain ⟨rfl, rfl⟩ := hvc <;> obtain ⟨rfl, rfl⟩ := hvc' <;>
    simp only [key, List.cons_lt_cons_iff, lt_self_iff_false, true_and, false_or, not_or,
      not_and, not_lt] at h1 h2 <;>
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

/-- **At most one palette block is split: the private edges have cut-rank at most one.** -/
theorem matCutRank_Mpriv_le {X : Finset (Vtx I)} (hX : IsCut X) :
    matCutRank (Mpart I .priv) X ≤ 1 := by
  refine (matCutRank_le_card_of_mem_or_zero ((splitP X).image fun c =>
    nbVec X (fun y => eId y = some c)) fun v hv => ?_).trans
    (card_image_le.trans (card_splitP_le hX))
  cases hv' : blockId v with
  | none =>
    left
    apply cutRow_Mpart_eq_zero
    intro y _ ⟨hadj, hc⟩
    cases v <;> simp only [blockId, reduceCtorEq] at hv'
    all_goals cases y <;> simp_all [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge]
  | some c =>
    have hrow : cutRow (Mpart I .priv) X v = nbVec X (fun y => eId y = some c) := by
      apply cutRow_Mpart_eq
      intro y hy
      cases v <;> simp only [blockId, reduceCtorEq, Option.some.injEq] at hv' <;> subst hv'
      · cases y <;> simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, eId, eq_comm]
      · rename_i C x hx t
        have hne : Vtx.eV C x hx t ≠ y := fun h => hy (h ▸ hv)
        cases y <;> simp [ecls, Vtx.isEV, adj_iff, edge, eId, hne, eq_comm]
        -- a test vertex of the same block precedes `E_{C,x}`
        rename_i C' x' hx' j' t'
        intro hC hx''
        subst hC hx''
        exact hy (hX.mem_of_lt hv (by simp [key, List.cons_lt_cons_iff]))
    rw [hrow]
    by_cases hsplit : ∃ w ∉ X, eId w = some c
    · right
      exact mem_image_of_mem _ (by simp [splitP]; exact ⟨⟨v, hv, hv'⟩, hsplit⟩)
    · left
      apply nbVec_eq_zero
      intro y hy h
      exact hsplit ⟨y, hy, h⟩

end SubspaceConvolution.Counter
