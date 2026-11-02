/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Transform.Defs

/-!
# Linear straight-line programs: definitions

The definitions of `SubspaceConvolution.Circuit.SLP` (moved here verbatim so that the proofs of the
cost-model API can be split over several files; see `SubspaceConvolution/Circuit/SLP.lean` for the
documentation and the public statements).
-/

open Finset

namespace SubspaceConvolution.Circuit

/-- A wire of a straight-line program: an input, or the output of a gate (by position). -/
abbrev Wire (I : Type*) := I ⊕ ℕ

/-- A linear gate `z = a x + b y`. -/
structure Gate (R : Type*) (I : Type*) where
  a : R
  x : Wire I
  b : R
  y : Wire I

variable {R : Type*} [CommRing R] {I O : Type*}

/-- The value of a wire, given the inputs and the values of the gates computed so far. -/
def read (f : I → R) (vals : List R) : Wire I → R
  | .inl i => f i
  | .inr j => vals.getD j 0

/-- The value of a gate. -/
def Gate.eval (g : Gate R I) (f : I → R) (vals : List R) : R :=
  g.a * read f vals g.x + g.b * read f vals g.y

/-- The values of all gates, in order. -/
def run (gs : List (Gate R I)) (f : I → R) : List R :=
  gs.foldl (fun vals g => vals ++ [g.eval f vals]) []

/-- A linear straight-line program with inputs `I` and outputs `O`. -/
structure SLP (R I O : Type*) where
  gates : List (Gate R I)
  out : O → Wire I

/-- The map computed by a program. -/
def SLP.eval (P : SLP R I O) (f : I → R) : O → R :=
  fun o => read f (run P.gates f) (P.out o)

/-- The number of gates. -/
def SLP.size (P : SLP R I O) : ℕ := P.gates.length

/-- All constants of the program lie in `C`. -/
def SLP.ConstsIn (P : SLP R I O) (C : Set R) : Prop := ∀ g ∈ P.gates, g.a ∈ C ∧ g.b ∈ C

/-- **The cost model.** `M` is computed by a linear straight-line program with at most `s` gates
`z = a x + b y` whose constants `a, b` lie in `C`. -/
def LinCost (C : Set R) (M : (I → R) → O → R) (s : ℕ) : Prop :=
  ∃ P : SLP R I O, P.size ≤ s ∧ P.ConstsIn C ∧ P.eval = M

/-- The transpose of a linear map given as a function (its matrix is `M (Pi.single i 1) o`). -/
noncomputable def transposeMap [Fintype O] [DecidableEq I] (M : (I → R) → O → R) :
    (O → R) → I → R :=
  fun g i => ∑ o, M (Pi.single i 1) o * g o

/-! ### The fast Fourier transform on `K^e` -/

section DFT

variable {K : Type*} [Field K] [Fintype K] {S : Type*} [CommRing S]

/-- The `e`-dimensional Fourier transform over `K`:
`ĥ(ξ) = ∑_x h(x) ψ(∑_i ξ_i x_i)`. -/
noncomputable def dft (F : FourierData K S) (e : ℕ) (h : (Fin e → K) → S) (ξ : Fin e → K) : S :=
  ∑ x, h x * F.ψ (∑ i, ξ i * x i)

/-- Its inverse `h(x) = q^{-e} ∑_ξ ĥ(ξ) ψ(-∑_i ξ_i x_i)`. -/
noncomputable def idft (F : FourierData K S) (e : ℕ) (g : (Fin e → K) → S) (x : Fin e → K) : S :=
  F.qinv ^ e * ∑ ξ, g ξ * F.ψ (-(∑ i, ξ i * x i))

end DFT

end SubspaceConvolution.Circuit
