/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.Basic

/-!
# Appendix G: the counter reduction — the construction

This file contains only the *construction* of Appendix G ("The counter reduction") of the paper:
the source problem **4-Monotone min-CSP**, the parameters `d, M, h, Q`, the graph `graph I`
with its vertex type `Vtx I`, the target number of colors `eta I`, and the linear layout
`layout I` of Lemma 6.  The theorems are proved in the other files of this directory.

## The source problem

An instance `I : MinCSP` has variables `Fin k` with values in `{0, …, n}`, a budget `W`, and
constraints `Fin p`.  A constraint `C` has a scope `X_C = scope C` and mini-constraints
`Fin (numMini C)`; the mini-constraint `R` requires `α x ≥ c_{R,x} = thr C R x` for `x ∈ X_C`.

## The graph (Section "Monotone counters and the register" and "Constraint gadgets")

Put `d = ⌈√(log₂ k)⌉` (the least `d` with `k ≤ 2^(d²)`), `M = 2^(d²)`, `h = 2^d`, `Q = M n`.
The variables are padded to the `M` matrices `A ∈ F₂^{d×d}` via the injection `enc I`.

* `row i A t` (`i < d`, `A ∈ F₂^{d×d}`, `t < n`): the register rows `B_i`, each a `Q`-clique.
  The vertex `row i A t` has label `(e_i, A i) ∈ F₂^{2d}` (`A i` is row `i` of `A`, i.e.
  `Aᵀ e_i`).  Thus the `Q/h` vertices of label `(e_i, a)` in `B_i` are indexed by the pairs
  `(A, t)` with `A i = a` (any indexing of these copies gives an isomorphic graph).
* `star t` (`t < Q - W`): the clique `B_*`.
* `sel C`: the selector `s_C`;  `anc b`: the anchor `m_b` of the `I`-vertex `b`.
  Selectors and anchors form the clique `D`.
* `aV C x _ j t` (`x ∈ X_C`, `j < d`, `t < n`): vertex `t` of the `n`-clique `A^{(j+1)}_{C,x}`.
  The clique with `j = 0` is the old clique `A_{C,x} = A^{(1)}`; only it carries the old
  edges.  (Indices are `0`-based: `A^{(j+1)}` of the paper is `j`.)
* `iV b` (`b = ⟨C, R, x, _, t⟩`, `t < n - c_{R,x}`): the vertices of the independent set
  `I_{C,R,x}`.
* `eV C x _ t` (`t < η - n`): the private clique `E_{C,x}`.

The target number of colors is `η = Q + |D| = Q + p + Σ_C Σ_R Σ_{x ∈ X_C} (n - c_{R,x})`.

## The layout (Lemma 6)

The layout sorts the vertices by the lexicographic key `key I v : List ℕ`: first the rows
`B_1, …, B_d`, then `B_*`, then for each `C` in turn: `s_C`, then the palette blocks
`[A^{(1)}_{C,x}, …, A^{(d)}_{C,x}, E_{C,x}]` (`x ∈ X_C` increasing; whole cliques
consecutively), then the mini-constraints `R` one at a time, each as the consecutive pairs
`m_b, b` for `b ∈ I_{C,R}`.
-/

open Finset Matrix

set_option linter.unusedSectionVars false

namespace SubspaceConvolution.Counter

/-! ## The source problem -/

/-- An instance of **4-Monotone min-CSP** (the scope bound `|X_C| ≤ 4` and the other
normalizations are recorded separately in `MinCSP.Normalized`). -/
structure MinCSP where
  /-- the number of variables; the variables are `Fin k` -/
  k : ℕ
  /-- the values are `0, …, n` -/
  n : ℕ
  /-- the budget -/
  W : ℕ
  /-- the number of constraints; the constraints are `Fin p` -/
  p : ℕ
  /-- the scope `X_C` of the constraint `C` -/
  scope : Fin p → Finset (Fin k)
  /-- the number of mini-constraints of `C`; they are `Fin (numMini C)` -/
  numMini : Fin p → ℕ
  /-- the thresholds `c_{R,x}` (only used for `x ∈ X_C`) -/
  thr : (C : Fin p) → Fin (numMini C) → Fin k → ℕ

namespace MinCSP

variable (I : MinCSP)

/-- `α` is a satisfying assignment: values in `{0, …, n}`, cost at most `W`, and every
constraint has a mini-constraint all of whose thresholds are met. -/
def Satisfies (α : Fin I.k → ℕ) : Prop :=
  (∀ x, α x ≤ I.n) ∧ ∑ x, α x ≤ I.W ∧
    ∀ C, ∃ R : Fin (I.numMini C), ∀ x ∈ I.scope C, I.thr C R x ≤ α x

/-- The instance has a satisfying assignment. -/
def Satisfiable : Prop := ∃ α, I.Satisfies α

/-- The normalizations the paper performs before the reduction. -/
structure Normalized : Prop where
  two_le_k : 2 ≤ I.k
  one_le_n : 1 ≤ I.n
  W_le : I.W ≤ I.k * I.n
  scope_card : ∀ C, (I.scope C).card ≤ 4
  numMini_pos : ∀ C, 0 < I.numMini C
  thr_le : ∀ C R x, I.thr C R x ≤ I.n

end MinCSP

/-! ## Parameters -/

theorem exists_sq_exponent (k : ℕ) : ∃ d : ℕ, k ≤ 2 ^ (d * d) :=
  ⟨k, Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_self k))⟩

/-- `d = ⌈√(log₂ k)⌉`: the least `d` with `k ≤ 2^(d²)`. -/
def d (I : MinCSP) : ℕ := Nat.find (exists_sq_exponent I.k)

/-- `M = 2^(d²)`, the number of matrix types. -/
def M (I : MinCSP) : ℕ := 2 ^ (d I * d I)

/-- `h = 2^d`, the number of labels in a row. -/
def h (I : MinCSP) : ℕ := 2 ^ d I

/-- `Q = M n`, the size of the register palette. -/
def Q (I : MinCSP) : ℕ := M I * I.n

/-- The matrices `A ∈ F₂^{d×d}` (the color types); `A i j` is the entry in row `i`, column `j`. -/
abbrev Mat (I : MinCSP) : Type := Fin (d I) → Fin (d I) → F2

/-- An explicit enumeration of the `2^(m²)` binary `m × m` matrices. -/
def matEquiv (m : ℕ) : (Fin m → Fin m → F2) ≃ Fin (2 ^ (m * m)) :=
  (Equiv.curry (Fin m) (Fin m) F2).symm.trans
    ((Equiv.arrowCongr finProdFinEquiv (Equiv.refl F2)).trans finFunctionFinEquiv)

/-- The padding: variable `x` is indexed by the matrix `enc I x` (the other matrices index the
unused padding variables). -/
def enc (I : MinCSP) : Fin I.k ↪ Mat I :=
  (Fin.castLEEmb (Nat.find_spec (exists_sq_exponent I.k))).trans
    (matEquiv (d I)).symm.toEmbedding

/-- The index of a matrix in the enumeration `matEquiv` (used to order the register rows). -/
def matIdx {I : MinCSP} (A : Mat I) : ℕ := (matEquiv (d I) A : ℕ)

/-- The label `(e_i, a) ∈ F₂^m × F₂^m` of a register vertex of row `i`. -/
def regLabel {m : ℕ} (i : Fin m) (a : Fin m → F2) : Fin m ⊕ Fin m → F2 :=
  Sum.elim (Pi.single i 1) a

/-- The test vector `t_{A,j} = (A e_j, e_j)`; these form a basis of `S_A^⊥`, where
`S_A = {(x, Aᵀ x)}`. -/
def testVec {m : ℕ} (A : Fin m → Fin m → F2) (j : Fin m) : Fin m ⊕ Fin m → F2 :=
  Sum.elim (fun i => A i j) (Pi.single j 1)

/-! ## The vertices -/

/-- The `I`-vertices: `⟨C, R, x, _, t⟩` is vertex `t` of the independent set `I_{C,R,x}`
(`x ∈ X_C`), which has `n - c_{R,x}` vertices. -/
structure IIdx (I : MinCSP) where
  /-- the constraint -/
  C : Fin I.p
  /-- the mini-constraint -/
  R : Fin (I.numMini C)
  /-- the variable -/
  x : Fin I.k
  hx : x ∈ I.scope C
  /-- the index inside `I_{C,R,x}` -/
  t : Fin (I.n - I.thr C R x)
  deriving DecidableEq

/-- `I`-vertices as a sigma type. -/
def IIdx.equivSigma (I : MinCSP) :
    IIdx I ≃ Σ C : Fin I.p, Σ R : Fin (I.numMini C), Σ x : I.scope C, Fin (I.n - I.thr C R x) where
  toFun b := ⟨b.C, b.R, ⟨b.x, b.hx⟩, b.t⟩
  invFun s := ⟨s.1, s.2.1, s.2.2.1.1, s.2.2.1.2, s.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (I : MinCSP) : Fintype (IIdx I) := Fintype.ofEquiv _ (IIdx.equivSigma I).symm

/-- The number of `I`-vertices, `Σ_C Σ_R Σ_{x ∈ X_C} (n - c_{R,x})`. -/
def numI (I : MinCSP) : ℕ :=
  ∑ C : Fin I.p, ∑ R : Fin (I.numMini C), ∑ x ∈ I.scope C, (I.n - I.thr C R x)

/-- The target number of colors `η = Q + |D|`, where `|D| = p + numI` (one selector per
constraint and one anchor per `I`-vertex). -/
def eta (I : MinCSP) : ℕ := Q I + (I.p + numI I)

/-- The vertices of the graph of Appendix G. -/
inductive Vtx (I : MinCSP) : Type
  /-- Register vertex of the row `B_i`, with label `(e_i, A i)`. -/
  | row (i : Fin (d I)) (A : Mat I) (t : Fin I.n)
  /-- Vertex of the clique `B_*` (of size `Q - W`). -/
  | star (t : Fin (Q I - I.W))
  /-- The selector `s_C`. -/
  | sel (C : Fin I.p)
  /-- The anchor `m_b` of the `I`-vertex `b`. -/
  | anc (b : IIdx I)
  /-- Vertex `t` of the `n`-clique `A^{(j+1)}_{C,x}`; `j = 0` is the old clique `A_{C,x}`. -/
  | aV (C : Fin I.p) (x : Fin I.k) (hx : x ∈ I.scope C) (j : Fin (d I)) (t : Fin I.n)
  /-- The `I`-vertex `b ∈ I_{C,R,x}`. -/
  | iV (b : IIdx I)
  /-- Vertex `t` of the private `(η - n)`-clique `E_{C,x}`. -/
  | eV (C : Fin I.p) (x : Fin I.k) (hx : x ∈ I.scope C) (t : Fin (eta I - I.n))
  deriving DecidableEq

/-- The pairs `(C, x)` with `x ∈ X_C` (the palette blocks). -/
abbrev AIdx (I : MinCSP) : Type := Σ C : Fin I.p, I.scope C

/-- The vertices as a sum type (used for the `Fintype` instance and for counting). -/
def Vtx.equivSum (I : MinCSP) :
    Vtx I ≃ (Fin (d I) × Mat I × Fin I.n) ⊕ Fin (Q I - I.W) ⊕ Fin I.p ⊕ IIdx I ⊕
      (AIdx I × Fin (d I) × Fin I.n) ⊕ IIdx I ⊕ (AIdx I × Fin (eta I - I.n)) where
  toFun
    | .row i A t => .inl (i, A, t)
    | .star t => .inr (.inl t)
    | .sel C => .inr (.inr (.inl C))
    | .anc b => .inr (.inr (.inr (.inl b)))
    | .aV C x hx j t => .inr (.inr (.inr (.inr (.inl (⟨C, x, hx⟩, j, t)))))
    | .iV b => .inr (.inr (.inr (.inr (.inr (.inl b)))))
    | .eV C x hx t => .inr (.inr (.inr (.inr (.inr (.inr (⟨C, x, hx⟩, t))))))
  invFun
    | .inl (i, A, t) => .row i A t
    | .inr (.inl t) => .star t
    | .inr (.inr (.inl C)) => .sel C
    | .inr (.inr (.inr (.inl b))) => .anc b
    | .inr (.inr (.inr (.inr (.inl (⟨C, x, hx⟩, j, t))))) => .aV C x hx j t
    | .inr (.inr (.inr (.inr (.inr (.inl b))))) => .iV b
    | .inr (.inr (.inr (.inr (.inr (.inr (⟨C, x, hx⟩, t)))))) => .eV C x hx t
  left_inv v := by cases v <;> rfl
  right_inv s := by
    rcases s with ⟨i, A, t⟩ | t | C | b | ⟨⟨C, x, hx⟩, j, t⟩ | b | ⟨⟨C, x, hx⟩, t⟩ <;> rfl

instance (I : MinCSP) : Fintype (Vtx I) := Fintype.ofEquiv _ (Vtx.equivSum I).symm

/-! ## The edges -/

/-- The edges of the graph, each listed once (in one orientation). -/
def edge (I : MinCSP) : Vtx I → Vtx I → Prop
  -- the rows `B_i` are cliques; there are no edges between different rows
  | .row i _ _, .row i' _ _ => i = i'
  -- `B_*` is a clique
  | .star _, .star _ => True
  -- the selectors and anchors form the clique `D` ...
  | .sel _, .sel _ => True
  | .sel _, .anc _ => True
  | .anc _, .anc _ => True
  -- ... completely joined to every `B_i` and to `B_*`
  | .sel _, .row _ _ _ => True
  | .anc _, .row _ _ _ => True
  | .sel _, .star _ => True
  | .anc _, .star _ => True
  -- distinct `I_{C,R}` are completely joined (for fixed `C`)
  | .iV b, .iV b' => b.C = b'.C ∧ (b.R : ℕ) ≠ b'.R
  -- `I_{C,R,x}` is completely joined to `A_{C,x}`
  | .iV b, .aV C x _ j _ => (j : ℕ) = 0 ∧ b.C = C ∧ b.x = x
  -- `s_C` is joined to every `A`-vertex and to every `I`-vertex outside `I_C`
  | .sel _, .aV _ _ _ j _ => (j : ℕ) = 0
  | .sel C, .iV b => b.C ≠ C
  -- `m_b` (`b ∈ I_{C,R,x}`) is joined to every `A`- and `I`-vertex outside `A_{C,x} ∪ {b}`
  | .anc b, .aV C x _ j _ => (j : ℕ) = 0 ∧ ¬ (C = b.C ∧ x = b.x)
  | .anc b, .iV b' => b' ≠ b
  -- all `A`- and `I`-vertices are joined to `B_*`
  | .star _, .aV _ _ _ j _ => (j : ℕ) = 0
  | .star _, .iV _ => True
  -- all `I`-vertices are joined to every `B_i`
  | .iV _, .row _ _ _ => True
  -- the cliques `A^{(1)}_{C,x}, …, A^{(d)}_{C,x}`
  | .aV C x _ j _, .aV C' x' _ j' _ => C = C' ∧ x = x' ∧ j = j'
  -- the test edges: `A^{(j+1)}_{C,x}` is joined to the register vertices of label `v` with
  -- `vᵀ t_{A,j} = 1`, where `A = enc x` is the matrix of the variable `x`
  | .aV _ x _ j _, .row i A _ => regLabel i (A i) ⬝ᵥ testVec (enc I x) j = 1
  -- the private clique `E_{C,x}`, complete to `A^{(1)}_{C,x}, …, A^{(d)}_{C,x}`
  | .eV C x _ _, .eV C' x' _ _ => C = C' ∧ x = x'
  | .eV C x _ _, .aV C' x' _ _ _ => C = C' ∧ x = x'
  | _, _ => False

instance (I : MinCSP) : DecidableRel (edge I) := fun v w => by
  cases v <;> cases w <;> unfold edge <;> infer_instance

/-- The graph of Appendix G. -/
def graph (I : MinCSP) : SimpleGraph (Vtx I) := SimpleGraph.fromRel (edge I)

instance (I : MinCSP) : DecidableRel (graph I).Adj := fun v w =>
  decidable_of_iff (v ≠ w ∧ (edge I v w ∨ edge I w v)) (SimpleGraph.fromRel_adj _ _ _).symm

/-! ## The linear layout -/

/-- The lexicographic sort key of the layout of Lemma 6. -/
def key (I : MinCSP) : Vtx I → List ℕ
  | .row i A t => [0, i, matIdx A, t]
  | .star t => [1, t]
  | .sel C => [2, C, 0]
  | .aV C x _ j t => [2, C, 1, x, j, t]
  | .eV C x _ t => [2, C, 1, x, d I, t]
  | .anc b => [2, b.C, 2, b.R, b.x, b.t, 0]
  | .iV b => [2, b.C, 2, b.R, b.x, b.t, 1]

theorem IIdx.ext_val {I : MinCSP} {b b' : IIdx I} (hC : b.C = b'.C) (hR : (b.R : ℕ) = b'.R)
    (hx : b.x = b'.x) (ht : (b.t : ℕ) = b'.t) : b = b' := by
  obtain ⟨C, R, x, hxC, t⟩ := b
  obtain ⟨C', R', x', hxC', t'⟩ := b'
  dsimp only at hC hR hx ht
  subst hC hx
  obtain rfl : R = R' := Fin.ext hR
  obtain rfl : t = t' := Fin.ext ht
  rfl

theorem matIdx_injective (I : MinCSP) : Function.Injective (matIdx (I := I)) := fun _ _ h =>
  (matEquiv (d I)).injective (Fin.ext h)

theorem key_injective (I : MinCSP) : Function.Injective (key I) := by
  intro v w hvw
  cases v <;> cases w <;> simp [key] at hvw ⊢
  · exact ⟨Fin.ext hvw.1, matIdx_injective I hvw.2.1, Fin.ext hvw.2.2⟩
  · exact Fin.ext hvw
  · exact Fin.ext hvw
  · exact IIdx.ext_val (Fin.ext hvw.1) hvw.2.1 (Fin.ext hvw.2.2.1) hvw.2.2.2
  · exact ⟨Fin.ext hvw.1, Fin.ext hvw.2.1, Fin.ext hvw.2.2.1, Fin.ext hvw.2.2.2⟩
  · exact absurd hvw.2.2.1 (ne_of_lt (Fin.is_lt _))
  · exact IIdx.ext_val (Fin.ext hvw.1) hvw.2.1 (Fin.ext hvw.2.2.1) hvw.2.2.2
  · exact absurd hvw.2.2.1 (ne_of_lt (Fin.is_lt _)).symm
  · exact ⟨Fin.ext hvw.1, Fin.ext hvw.2.1, Fin.ext hvw.2.2⟩

/-- The layout order: lexicographic by `key`. -/
instance (I : MinCSP) : LinearOrder (Vtx I) := LinearOrder.lift' (key I) (key_injective I)

/-- The linear layout of Lemma 6: the vertices sorted by `key`. -/
def layout (I : MinCSP) : LinearLayout (Vtx I) where
  order := (Finset.univ : Finset (Vtx I)).sort (· ≤ ·)
  nodup := Finset.sort_nodup _ _
  mem_order v := (Finset.mem_sort _).2 (Finset.mem_univ v)

end SubspaceConvolution.Counter
