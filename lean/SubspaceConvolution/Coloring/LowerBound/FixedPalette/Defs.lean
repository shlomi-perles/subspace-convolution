/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.Basic

/-!
# Fixed-palette lower bounds (Appendix D): the construction

This file defines the input formulas (3-CNF formulas over a `k × k` grid of Boolean variables),
the graph `G_φ` of Appendix D ("Fixed-palette decision and counting lower bounds") and its
supplied linear layout.

## The construction

* The palette triangle `T = pal 0`, `F_A = pal 1`, `F_B = pal 2`.
* Groups (`Grp k m`): a column group `colB h` for every column `h`, a base row group `rowA j` for
  every row `j`, and a clause-local row group `loc i t` for every literal occurrence `(i, t)`
  (clause `i`, position `t : Fin 3`), for the row of that literal.  This is the one allowed
  simplification of the paper, where the local groups are indexed by the rows `j ∈ J_i`
  occurring in clause `i`.  There are `g = 2k + 3m` groups.
* Every group has `t = 2^k` inputs `inp γ p` (`p : Fin (2^k)`, the input `x_{p+1}`), the input
  `p` carrying the assignment `asg k p : Fin k → Bool` (of the row, resp. of the column).
  `A` inputs (row groups) are adjacent to `F_B`, `B` inputs (column groups) to `F_A`.
  An `A` input of row `j` with assignment `u` is adjacent to the `B` input of column `h` with
  assignment `v` iff `u_h ≠ v_j`, i.e. iff the labels `(e_j, u)` and `(v, e_h)` have dot product
  one.
* Every group has an odd cycle `w_0 w_1 ⋯ w_t w_0` (`cyc γ i`, `i : Fin (2^k + 1)`); `w_0` is
  adjacent to the false color of the group (`F_A` for row groups, `F_B` for column groups) and
  `w_{p+1}` is adjacent to `x_{p+1}`.
* For every literal occurrence `(i, t)` an adjacent pair `c = lit i t true`,
  `c̄ = lit i t false`, both adjacent to `F_A`; `c` is adjacent to the inputs of the local group
  `loc i t` that falsify the literal and `c̄` to those that satisfy it.
* For every clause `i` an adjacent pair `s = sig i true`, `s̄ = sig i false`, both adjacent to
  `F_A`, and four private NAE triangles `tri i q r` (`q : Fin 4`, `r : Fin 3`) implementing
  `NAE(ā, s, F_B)`, `NAE(b̄, s, F_B)`, `NAE(a, b, s̄)`, `NAE(s, c, F_B)`, where `a, b, c` are the
  vertices `c` of the three literal pairs of the clause; triangle vertex `tri i q r` is adjacent
  to the terminal `term i q r`.
-/

namespace SubspaceConvolution.FixedPalette

/-! ## Formulas -/

structure Lit (k : ℕ) where
  row : Fin k
  col : Fin k
  pos : Bool
deriving DecidableEq

/-- 3-CNF over the k×k grid of variables; each clause has exactly three literal occurrences
(shorter nonempty clauses repeat a literal, as in the paper). -/
structure GridCNF (k : ℕ) where
  m : ℕ
  clause : Fin m → Fin 3 → Lit k

def Lit.eval {k : ℕ} (α : Fin k → Fin k → Bool) (l : Lit k) : Bool :=
  if l.pos then α l.row l.col else !(α l.row l.col)

def GridCNF.Satisfies {k : ℕ} (φ : GridCNF k) (α : Fin k → Fin k → Bool) : Prop :=
  ∀ i, ∃ t, (φ.clause i t).eval α = true

instance {k : ℕ} (φ : GridCNF k) : DecidablePred φ.Satisfies := fun α => by
  unfold GridCNF.Satisfies
  infer_instance

noncomputable def GridCNF.numSat {k : ℕ} (φ : GridCNF k) : ℕ :=
  Fintype.card {α : Fin k → Fin k → Bool // φ.Satisfies α}

/-- The value of a literal under an assignment `u` of its row. -/
def Lit.evalRow {k : ℕ} (l : Lit k) (u : Fin k → Bool) : Bool :=
  if l.pos then u l.col else !(u l.col)

theorem Lit.eval_eq_evalRow {k : ℕ} (α : Fin k → Fin k → Bool) (l : Lit k) :
    l.eval α = l.evalRow (α l.row) := rfl

/-! ## Assignments of a row or column -/

/-- The assignment carried by the `p`-th input of a group (binary encoding). -/
def asg (k : ℕ) : Fin (2 ^ k) ≃ (Fin k → Bool) :=
  finFunctionFinEquiv.symm.trans (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv)

/-! ## Groups and vertices -/

/-- The groups of inputs: column groups `colB h`, base row groups `rowA j`, and clause-local row
groups `loc i t` (one per literal occurrence). -/
inductive Grp (k m : ℕ) where
  | colB (h : Fin k)
  | rowA (j : Fin k)
  | loc (i : Fin m) (t : Fin 3)
  deriving DecidableEq, Fintype

variable {k m : ℕ}

namespace Grp

/-- The false color of a group: `F_B = 2` for column groups, `F_A = 1` for row groups. -/
def falseCol : Grp k m → Fin 3
  | colB _ => 2
  | rowA _ => 1
  | loc _ _ => 1

/-- The palette vertex the inputs of a group are joined to: `F_A = 1` for column groups,
`F_B = 2` for row groups. -/
def forbCol : Grp k m → Fin 3
  | colB _ => 1
  | rowA _ => 2
  | loc _ _ => 2

/-- The row of a row group (`none` for column groups). -/
def row (φ : GridCNF k) : Grp k φ.m → Option (Fin k)
  | colB _ => none
  | rowA j => some j
  | loc i t => some (φ.clause i t).row

/-- Segment index of a group in the layout. -/
def sid (k : ℕ) : Grp k m → ℕ
  | colB h => 1 + h
  | rowA j => 1 + k + j
  | loc i t => 1 + 2 * k + 4 * i + t

end Grp

/-- The vertices of `G_φ`. -/
inductive Vtx (k m : ℕ) where
  /-- palette: `T = pal 0`, `F_A = pal 1`, `F_B = pal 2` -/
  | pal (a : Fin 3)
  /-- the input `x_{p+1}` of a group -/
  | inp (γ : Grp k m) (p : Fin (2 ^ k))
  /-- the cycle vertex `w_i` of a group -/
  | cyc (γ : Grp k m) (i : Fin (2 ^ k + 1))
  /-- literal pair of occurrence `(i, t)`: `c` (`b = true`) and `c̄` (`b = false`) -/
  | lit (i : Fin m) (t : Fin 3) (b : Bool)
  /-- clause pair: `s` (`b = true`) and `s̄` (`b = false`) -/
  | sig (i : Fin m) (b : Bool)
  /-- vertex `r` of NAE triangle `q` of clause `i` -/
  | tri (i : Fin m) (q : Fin 4) (r : Fin 3)
  deriving DecidableEq, Fintype

/-- The terminals of the four NAE triangles of clause `i`:
`NAE(ā, s, F_B)`, `NAE(b̄, s, F_B)`, `NAE(a, b, s̄)`, `NAE(s, c, F_B)`. -/
def term (i : Fin m) : Fin 4 → Fin 3 → Vtx k m :=
  ![![.lit i 0 false, .sig i true, .pal 2],
    ![.lit i 1 false, .sig i true, .pal 2],
    ![.lit i 0 true, .lit i 1 true, .sig i false],
    ![.sig i true, .lit i 2 true, .pal 2]]

/-- The edges of `G_φ`, each listed in one direction. -/
def edge (φ : GridCNF k) : Vtx k φ.m → Vtx k φ.m → Bool
  | .pal a, .pal b => decide (a < b)
  | .inp γ _, .pal c => decide (c = γ.forbCol)
  | .inp γ q, .inp γ' p =>
      match γ, γ'.row φ with
      | .colB h, some j => decide (asg k q j ≠ asg k p h)
      | _, _ => false
  | .cyc γ i, .pal c => decide (i = 0 ∧ c = γ.falseCol)
  | .cyc γ i, .cyc γ' i' => decide (γ' = γ ∧ i' = i + 1)
  | .cyc γ i, .inp γ' p => decide (γ' = γ ∧ i = p.succ)
  | .lit _ _ _, .pal c => decide (c = 1)
  | .lit i t b, .lit i' t' b' => decide (i' = i ∧ t' = t ∧ b = true ∧ b' = false)
  | .lit i t b, .inp γ p => decide (γ = .loc i t ∧ (φ.clause i t).evalRow (asg k p) ≠ b)
  | .sig _ _, .pal c => decide (c = 1)
  | .sig i b, .sig i' b' => decide (i' = i ∧ b = true ∧ b' = false)
  | .tri i q r, .tri i' q' r' => decide (i' = i ∧ q' = q ∧ r < r')
  | .tri i q r, .pal c => decide ((term i q r : Vtx k φ.m) = .pal c)
  | .tri i q r, .lit i' t b => decide ((term i q r : Vtx k φ.m) = .lit i' t b)
  | .tri i q r, .sig i' b => decide ((term i q r : Vtx k φ.m) = .sig i' b)
  | _, _ => false

theorem fin_add_one_ne_self (i : Fin (2 ^ k + 1)) : i + 1 ≠ i := by
  intro h
  have h1 := congrArg Fin.val h
  rw [Fin.val_add_one] at h1
  have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  split_ifs at h1 with h2
  · subst h2
    simp at h1
    omega
  · omega

theorem edge_self (φ : GridCNF k) (x : Vtx k φ.m) : edge φ x x = false := by
  cases x with
  | pal a => simp [edge]
  | inp γ p => cases γ <;> simp [edge, Grp.row]
  | cyc γ i => simp [edge]
  | lit i t b => simp [edge]
  | sig i b => simp [edge]
  | tri i q r => simp [edge]

/-- The graph `G_φ`. -/
def graph (φ : GridCNF k) : SimpleGraph (Vtx k φ.m) where
  Adj x y := edge φ x y = true ∨ edge φ y x = true
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun x h => by simp [edge_self] at h⟩

instance (φ : GridCNF k) : DecidableRel (graph φ).Adj := fun x y =>
  inferInstanceAs (Decidable (edge φ x y = true ∨ edge φ y x = true))

theorem graph_adj (φ : GridCNF k) (x y : Vtx k φ.m) :
    (graph φ).Adj x y ↔ edge φ x y = true ∨ edge φ y x = true := Iff.rfl

/-! ## The layout -/

namespace Vtx

/-- Segment index in the layout: the palette, then the column groups, the base row groups, and
for each clause its three local groups followed by its clause test. -/
def sid : Vtx k m → ℕ
  | pal _ => 0
  | inp γ _ => γ.sid k
  | cyc γ _ => γ.sid k
  | lit i _ _ => 4 + 2 * k + 4 * i
  | sig i _ => 4 + 2 * k + 4 * i
  | tri i _ _ => 4 + 2 * k + 4 * i

/-- Offset inside a segment: `w_0, x_1, w_1, …, x_t, w_t` in a group; the four signal pairs
`c, c̄` (three times) and `s, s̄`, then the four triangles in a clause test. -/
def off : Vtx k m → ℕ
  | pal a => a
  | inp _ p => 2 * p + 1
  | cyc _ i => 2 * i
  | lit _ t b => 2 * t + (if b then 0 else 1)
  | sig _ b => 6 + (if b then 0 else 1)
  | tri _ q r => 8 + 3 * q + r

/-- `v` strictly precedes `w` in the layout. -/
def Before (v w : Vtx k m) : Prop := v.sid < w.sid ∨ (v.sid = w.sid ∧ v.off < w.off)

instance : DecidableRel (Before : Vtx k m → Vtx k m → Prop) := fun v w => by
  unfold Before
  infer_instance

/-- The layout order (non-strict). -/
def LayoutLE (v w : Vtx k m) : Prop := v.sid < w.sid ∨ (v.sid = w.sid ∧ v.off ≤ w.off)

instance : DecidableRel (LayoutLE : Vtx k m → Vtx k m → Prop) := fun v w => by
  unfold LayoutLE
  infer_instance

end Vtx

end SubspaceConvolution.FixedPalette
