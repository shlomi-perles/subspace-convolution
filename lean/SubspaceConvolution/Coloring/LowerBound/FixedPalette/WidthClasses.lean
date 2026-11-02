/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.FixedPalette.Layout

/-!
# Width of the supplied layout, part 1: edge classes

We split the adjacency matrix of `G_φ` into four edge classes (`clsMat`): edges at the palette,
edges between inputs (the `AB` block), edges between inputs and literal pairs, and the remaining
local edges.  For a prefix `X` of the layout (the vertices before `b`) we bound the cut-rank of the
first three classes by `3`, `2k` and `6`:

* palette edges: all rows of the cut lie at the palette, which precedes every other vertex;
* `AB` edges: all `B` inputs precede all `A` inputs, so the cut factors through the labels
  `(v, e_h)` and `(e_j, u)` in `F₂^{2k}`;
* input–literal edges: their columns lie among the six literal-pair vertices of the clause whose
  segment contains `b`.
-/

namespace SubspaceConvolution.FixedPalette

open Finset

variable {k m : ℕ}

namespace Vtx

def isPal : Vtx k m → Bool
  | pal _ => true
  | inp _ _ => false
  | cyc _ _ => false
  | lit _ _ _ => false
  | sig _ _ => false
  | tri _ _ _ => false

def isInp : Vtx k m → Bool
  | pal _ => false
  | inp _ _ => true
  | cyc _ _ => false
  | lit _ _ _ => false
  | sig _ _ => false
  | tri _ _ _ => false

def isLit : Vtx k m → Bool
  | pal _ => false
  | inp _ _ => false
  | cyc _ _ => false
  | lit _ _ _ => true
  | sig _ _ => false
  | tri _ _ _ => false

/-- Edge classes: `0` palette, `1` between inputs, `2` between inputs and literal pairs,
`3` local. -/
def cls (x y : Vtx k m) : Fin 4 :=
  if x.isPal || y.isPal then 0
  else if x.isInp && y.isInp then 1
  else if (x.isInp && y.isLit) || (x.isLit && y.isInp) then 2
  else 3

theorem cls_comm (x y : Vtx k m) : cls x y = cls y x := by
  unfold cls
  cases x.isPal <;> cases y.isPal <;> cases x.isInp <;> cases y.isInp <;> cases x.isLit <;>
    cases y.isLit <;> rfl

theorem one_le_sid_of_not_pal {x : Vtx k m} (h : x.isPal = false) : 1 ≤ x.sid := by
  cases x with
  | pal a => simp [isPal] at h
  | inp γ p => exact γ.one_le_sid
  | cyc γ i => exact γ.one_le_sid
  | lit i t b => simp only [sid]; omega
  | sig i b => simp only [sid]; omega
  | tri i q r => simp only [sid]; omega

theorem cls_eq_zero {x y : Vtx k m} (h : cls x y = 0) : x.isPal = true ∨ y.isPal = true := by
  unfold cls at h
  split_ifs at h with h1 h2 h3
  · simpa using h1
  all_goals exact absurd h (by decide)

/-- The clause whose part of the layout (local groups and clause test) contains a vertex. -/
def clauseOf : Vtx k m → Option (Fin m)
  | pal _ => none
  | inp (.loc i _) _ => some i
  | inp _ _ => none
  | cyc (.loc i _) _ => some i
  | cyc _ _ => none
  | lit i _ _ => some i
  | sig i _ => some i
  | tri i _ _ => some i

theorem clauseOf_eq {b : Vtx k m} {i : Fin m} (h1 : 1 + 2 * k + 4 * (i : ℕ) ≤ b.sid)
    (h2 : b.sid ≤ 4 + 2 * k + 4 * (i : ℕ)) : b.clauseOf = some i := by
  cases b with
  | pal a => simp [sid] at h1
  | inp γ p =>
    cases γ with
    | colB h => simp [sid, Grp.sid] at h1 h2; omega
    | rowA j => simp [sid, Grp.sid] at h1 h2; omega
    | loc i' t =>
      simp only [sid, Grp.sid] at h1 h2
      simp only [clauseOf, Option.some.injEq]
      exact Fin.ext (by omega)
  | cyc γ p =>
    cases γ with
    | colB h => simp [sid, Grp.sid] at h1 h2; omega
    | rowA j => simp [sid, Grp.sid] at h1 h2; omega
    | loc i' t =>
      simp only [sid, Grp.sid] at h1 h2
      simp only [clauseOf, Option.some.injEq]
      exact Fin.ext (by omega)
  | lit i' t bb =>
    simp only [sid] at h1 h2
    simp only [clauseOf, Option.some.injEq]
    exact Fin.ext (by omega)
  | sig i' bb =>
    simp only [sid] at h1 h2
    simp only [clauseOf, Option.some.injEq]
    exact Fin.ext (by omega)
  | tri i' q r =>
    simp only [sid] at h1 h2
    simp only [clauseOf, Option.some.injEq]
    exact Fin.ext (by omega)

end Vtx

/-- The vertices strictly before `b`. -/
def beforeSet (b : Vtx k m) : Finset (Vtx k m) := univ.filter fun v => Vtx.Before v b

@[simp] theorem mem_beforeSet {b v : Vtx k m} : v ∈ beforeSet b ↔ Vtx.Before v b := by
  simp [beforeSet]

/-- The edges of class `c`. -/
def clsMat (φ : GridCNF k) (c : Fin 4) : Matrix (Vtx k φ.m) (Vtx k φ.m) F2 :=
  Matrix.of fun x y => if (graph φ).Adj x y ∧ Vtx.cls x y = c then 1 else 0

theorem adjMatrix_eq_sum (φ : GridCNF k) :
    (graph φ).adjMatrix F2 = ∑ c : Fin 4, clsMat φ c := by
  ext x y
  rw [SimpleGraph.adjMatrix_apply, Matrix.sum_apply]
  simp only [clsMat, Matrix.of_apply]
  by_cases h : (graph φ).Adj x y
  · simp [h]
  · simp [h]

theorem clsMat_eq_zero {φ : GridCNF k} {c : Fin 4} {x y : Vtx k φ.m}
    (h : (graph φ).Adj x y → Vtx.cls x y = c → False) : clsMat φ c x y = 0 := by
  simp only [clsMat, Matrix.of_apply]
  rw [ite_eq_right_iff]
  intro h'
  exact absurd h'.2 (h h'.1)

/-! ### Palette edges -/

theorem rank_pal (φ : GridCNF k) (b : Vtx k φ.m) :
    matCutRank (clsMat φ 0) (beforeSet b) ≤ 3 := by
  refine (matCutRank_le_card_rows {.pal 0, .pal 1, .pal 2} ?_).trans card_le_three
  intro x hx hxR y hy
  rw [mem_beforeSet] at hx
  rw [mem_beforeSet] at hy
  apply clsMat_eq_zero
  intro _ hc
  have hxp : x.isPal = false := by
    cases x with
    | pal a => fin_cases a <;> simp at hxR
    | _ => rfl
  have hyp : y.isPal = true := by
    rcases Vtx.cls_eq_zero hc with h | h
    · rw [hxp] at h
      exact absurd h (by decide)
    · exact h
  apply hy
  have h1 := Vtx.one_le_sid_of_not_pal hxp
  have hy0 : y.sid = 0 := by
    cases y <;> simp_all [Vtx.isPal, Vtx.sid]
  unfold Vtx.Before at hx ⊢
  omega

/-! ### Edges between inputs: the label factorization -/

/-- `F₂`-value of a Boolean. -/
def b2 (b : Bool) : F2 := if b then 1 else 0

theorem ite_ne_eq_b2 : ∀ a b : Bool, (if a ≠ b then (1 : F2) else 0) = b2 a + b2 b := by
  decide

/-- The label `(v, e_h)` of the `B` input of column `h` with assignment `v`. -/
def labB : Vtx k m → Fin (k + k) → F2
  | .inp γ q =>
    match γ with
    | .colB h => Fin.append (fun j => b2 (asg k q j)) (fun h' => if h' = h then 1 else 0)
    | .rowA _ => 0
    | .loc _ _ => 0
  | .pal _ => 0
  | .cyc _ _ => 0
  | .lit _ _ _ => 0
  | .sig _ _ => 0
  | .tri _ _ _ => 0

/-- The label `(e_j, u)` of an `A` input of row `j` with assignment `u`. -/
def labA (φ : GridCNF k) : Vtx k φ.m → Fin (k + k) → F2
  | .inp γ p =>
    match γ.row φ with
    | some j => Fin.append (fun j' => if j' = j then 1 else 0) (fun h => b2 (asg k p h))
    | none => 0
  | .pal _ => 0
  | .cyc _ _ => 0
  | .lit _ _ _ => 0
  | .sig _ _ => 0
  | .tri _ _ _ => 0

theorem lab_dot (φ : GridCNF k) (h : Fin k) (q : Fin (2 ^ k)) (γ : Grp k φ.m) (p : Fin (2 ^ k))
    (j : Fin k) (hj : γ.row φ = some j) :
    ∑ i, labB (.inp (.colB h) q : Vtx k φ.m) i * labA φ (.inp γ p) i =
      b2 (asg k q j) + b2 (asg k p h) := by
  simp only [labB, labA, hj, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  simp [Finset.sum_ite_eq']

theorem colB_row (φ : GridCNF k) (h : Fin k) : (Grp.colB h : Grp k φ.m).row φ = none := rfl

theorem before_B_A {h : Fin k} {q : Fin (2 ^ k)} {γ : Grp k m} {p : Fin (2 ^ k)}
    (hγ : ∀ h', γ ≠ .colB h') : Vtx.Before (.inp (.colB h) q) (.inp γ p) := by
  left
  cases γ with
  | colB h' => exact absurd rfl (hγ h')
  | rowA j => simp [Vtx.sid, Grp.sid]; omega
  | loc i t => simp [Vtx.sid, Grp.sid]; omega

theorem cls_ne_one_of_left {x y : Vtx k m} (hx : x.isInp = false) : Vtx.cls x y ≠ 1 := by
  unfold Vtx.cls
  rw [hx]
  split_ifs <;> simp_all

theorem cls_ne_one_of_right {x y : Vtx k m} (hy : y.isInp = false) : Vtx.cls x y ≠ 1 := by
  unfold Vtx.cls
  rw [hy]
  split_ifs <;> simp_all

theorem rank_ab_aux_left {φ : GridCNF k} {x y : Vtx k φ.m} (hx : x.isInp = false)
    (hl : labB x = 0) : clsMat φ 1 x y = ∑ i, labB x i * labA φ y i := by
  rw [hl]
  simp only [Pi.zero_apply, zero_mul, sum_const_zero]
  exact clsMat_eq_zero fun _ hc => cls_ne_one_of_left hx hc

theorem rank_ab_aux_right {φ : GridCNF k} {x y : Vtx k φ.m} (hy : y.isInp = false)
    (hl : labA φ y = 0) : clsMat φ 1 x y = ∑ i, labB x i * labA φ y i := by
  rw [hl]
  simp only [Pi.zero_apply, mul_zero, sum_const_zero]
  exact clsMat_eq_zero fun _ hc => cls_ne_one_of_right hy hc

theorem rank_ab (φ : GridCNF k) (b : Vtx k φ.m) :
    matCutRank (clsMat φ 1) (beforeSet b) ≤ k + k := by
  refine matCutRank_le_of_factor (labB) (labA φ) ?_
  intro x hx y hy
  rw [mem_beforeSet] at hx hy
  cases x with
  | inp γ q =>
    cases y with
    | inp γ' p =>
      cases γ with
      | colB h =>
        cases hr : γ'.row φ with
        | none =>
          rw [clsMat_eq_zero]
          · simp [labA, hr]
          · intro hadj _
            rcases hadj with h1 | h1
            · simp [edge, hr] at h1
            · cases γ' <;> simp [edge, Grp.row] at h1 hr
        | some j =>
          rw [lab_dot φ h q γ' p j hr, ← ite_ne_eq_b2]
          simp only [clsMat, Matrix.of_apply]
          have hadj : (graph φ).Adj (.inp (.colB h) q) (.inp γ' p) ↔ asg k q j ≠ asg k p h := by
            rw [graph_adj]
            constructor
            · rintro (h1 | h1)
              · simpa [edge, hr] using h1
              · simp [edge, Grp.row] at h1
            · intro h1
              left
              simpa [edge, hr] using h1
          have hcls : Vtx.cls (.inp (.colB h) q : Vtx k φ.m) (.inp γ' p) = 1 := rfl
          simp only [hadj, hcls, and_true]
      | rowA j =>
        have hl : labB (.inp (.rowA j) q : Vtx k φ.m) = 0 := rfl
        rw [hl]
        simp only [Pi.zero_apply, zero_mul, sum_const_zero]
        apply clsMat_eq_zero
        intro hadj _
        rcases hadj with h1 | h1
        · simp [edge] at h1
        · cases γ' with
          | colB h' =>
            exact hy (Vtx.before_trans (before_B_A (by simp)) hx)
          | rowA j' => simp [edge] at h1
          | loc i t => simp [edge] at h1
      | loc i t =>
        have hl : labB (.inp (.loc i t) q : Vtx k φ.m) = 0 := rfl
        rw [hl]
        simp only [Pi.zero_apply, zero_mul, sum_const_zero]
        apply clsMat_eq_zero
        intro hadj _
        rcases hadj with h1 | h1
        · simp [edge] at h1
        · cases γ' with
          | colB h' =>
            exact hy (Vtx.before_trans (before_B_A (by simp)) hx)
          | rowA j' => simp [edge] at h1
          | loc i t => simp [edge] at h1
    | pal a => exact rank_ab_aux_right (by rfl) (by rfl)
    | cyc γ' i => exact rank_ab_aux_right (by rfl) (by rfl)
    | lit i t bb => exact rank_ab_aux_right (by rfl) (by rfl)
    | sig i bb => exact rank_ab_aux_right (by rfl) (by rfl)
    | tri i q r => exact rank_ab_aux_right (by rfl) (by rfl)
  | pal a => exact rank_ab_aux_left (by rfl) (by rfl)
  | cyc γ i => exact rank_ab_aux_left (by rfl) (by rfl)
  | lit i t bb => exact rank_ab_aux_left (by rfl) (by rfl)
  | sig i bb => exact rank_ab_aux_left (by rfl) (by rfl)
  | tri i q r => exact rank_ab_aux_left (by rfl) (by rfl)

/-! ### Edges between inputs and literal pairs -/

/-- The six literal-pair vertices of clause `i`. -/
def lits (i : Fin m) : Finset (Vtx k m) := univ.image fun tb : Fin 3 × Bool => .lit i tb.1 tb.2

theorem card_lits (i : Fin m) : (lits (k := k) i).card ≤ 6 :=
  card_image_le.trans (by simp)

theorem lit_mem_lits (i : Fin m) (t : Fin 3) (bb : Bool) : (Vtx.lit i t bb : Vtx k m) ∈ lits i :=
  mem_image.2 ⟨(t, bb), mem_univ _, rfl⟩

/-- The literal-pair vertices of the clause whose part of the layout contains `b`. -/
def litCols (b : Vtx k m) : Finset (Vtx k m) :=
  match b.clauseOf with
  | some i => lits i
  | none => ∅

theorem card_litCols (b : Vtx k m) : (litCols b).card ≤ 6 := by
  unfold litCols
  split
  · exact card_lits _
  · simp

theorem rank_lit (φ : GridCNF k) (b : Vtx k φ.m) :
    matCutRank (clsMat φ 2) (beforeSet b) ≤ 6 := by
  refine (matCutRank_le_card_cols (litCols b) ?_).trans (card_litCols b)
  intro x hx y hy hyS
  rw [mem_beforeSet] at hx hy
  apply clsMat_eq_zero
  intro hadj hc
  rcases hadj with h1 | h1
  · -- edge from `x` to `y`: `x` is the literal vertex
    cases x <;> cases y <;> simp [edge] at h1 <;>
      simp [Vtx.cls, Vtx.isPal, Vtx.isInp, Vtx.isLit] at hc
    obtain ⟨rfl, -⟩ := h1
    apply hy
    unfold Vtx.Before at hx ⊢
    simp only [Vtx.sid_inp, Vtx.sid_lit, Grp.sid_loc] at hx ⊢
    omega
  · -- edge from `y` to `x`: `y` is the literal vertex
    cases x <;> cases y <;> simp [edge] at h1 <;>
      simp [Vtx.cls, Vtx.isPal, Vtx.isInp, Vtx.isLit] at hc
    rename_i γ p i t bb
    obtain ⟨rfl, -⟩ := h1
    apply hyS
    have hcl : b.clauseOf = some i := by
      unfold Vtx.Before at hx hy
      simp only [Vtx.sid_inp, Vtx.sid_lit, Grp.sid_loc] at hx hy
      exact Vtx.clauseOf_eq (by omega) (by omega)
    simp only [litCols, hcl]
    exact lit_mem_lits _ _ _

end SubspaceConvolution.FixedPalette
