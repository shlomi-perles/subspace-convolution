/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Circuit.Transpose

/-!
# Linear straight-line programs: the cost model for arithmetic operations

The paper counts ring additions, subtractions and multiplications.  Every algorithm in the paper
for a transform is a *linear* computation, so we count operations with **linear straight-line
programs** (linear circuits): a program is a list of gates `z = a x + b y`, where `x, y` are inputs
or earlier gates and `a, b` are constants.  One gate costs at most three ring operations, so a bound
on gates is a bound on arithmetic operations up to a factor of three.  The same gates, with
`|a|, |b| ≤ 1` over `ℂ`, are the bounded-coefficient model of Appendix F.

* `SLP R I O` — a program with inputs `I` and outputs `O`; `SLP.eval`; `SLP.size` (number of gates).
* `LinCost C M s` — the map `M : (I → R) → (O → R)` is computed by a program with at most `s`
  gates whose constants lie in `C`.

A wire is `Sum.inl i` (input `i`) or `Sum.inr j` (gate number `j`, counted from `0`).  A reference
to a gate that has not been computed yet reads as `0`; in particular the constant `0` is free.

The definitions (`Wire`, `Gate`, `read`, `Gate.eval`, `run`, `SLP`, `SLP.eval`, `SLP.size`,
`SLP.ConstsIn`, `LinCost`, `transposeMap`, `dft`, `idft`) live in
`SubspaceConvolution.Circuit.Defs`; the program combinators used in the proofs below are in
`SubspaceConvolution.Circuit.Run`, and the transposed program in `SubspaceConvolution.Circuit.Transpose`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace SubspaceConvolution.Circuit

variable {R : Type*} [CommRing R] {I O : Type*}

namespace LinCost

variable {C : Set R}

theorem mono {M : (I → R) → O → R} {s t : ℕ} (h : LinCost C M s) (hst : s ≤ t) :
    LinCost C M t := by
  obtain ⟨P, hs, hC, hM⟩ := h
  exact ⟨P, hs.trans hst, hC, hM⟩

theorem mono_consts {C' : Set R} {M : (I → R) → O → R} {s : ℕ} (h : LinCost C M s)
    (hC : C ⊆ C') : LinCost C' M s := by
  obtain ⟨P, hs, hP, hM⟩ := h
  exact ⟨P, hs, fun g hg => ⟨hC (hP g hg).1, hC (hP g hg).2⟩, hM⟩

theorem congr {M M' : (I → R) → O → R} {s : ℕ} (h : LinCost C M s) (hM : M = M') :
    LinCost C M' s := hM ▸ h

/-- The identity costs nothing. -/
theorem id : LinCost C (fun f : I → R => f) 0 :=
  ⟨⟨[], Sum.inl⟩, le_rfl, fun _ hg => absurd hg List.not_mem_nil, rfl⟩

/-- Constant zero outputs cost nothing. -/
theorem zero : LinCost C (fun (_ : I → R) (_ : O) => (0 : R)) 0 := by
  refine ⟨⟨[], fun _ => Sum.inr 0⟩, le_rfl, fun _ hg => absurd hg List.not_mem_nil, ?_⟩
  funext f o
  simp [SLP.eval]

/-- Reindexing is free: inputs may be read several times or not at all, and outputs may be
duplicated or dropped. -/
theorem reindex {I' O' : Type*} {M : (I → R) → O → R} {s : ℕ} (h : LinCost C M s)
    (d : I → I') (e : O' → O) :
    LinCost C (fun (f : I' → R) (o : O') => M (fun i => f (d i)) (e o)) s := by
  obtain ⟨P, hs, hC, rfl⟩ := h
  exact ⟨P.reindex d e, by rwa [SLP.size_reindex], P.constsIn_reindex d e hC,
    SLP.eval_reindex P d e⟩

/-- Composition: the costs add. -/
theorem comp {J : Type*} {M₁ : (I → R) → J → R} {M₂ : (J → R) → O → R} {s₁ s₂ : ℕ}
    (h₁ : LinCost C M₁ s₁) (h₂ : LinCost C M₂ s₂) : LinCost C (fun f => M₂ (M₁ f)) (s₁ + s₂) := by
  obtain ⟨P₁, hs₁, hC₁, rfl⟩ := h₁
  obtain ⟨P₂, hs₂, hC₂, rfl⟩ := h₂
  refine ⟨P₁.comp P₂, ?_, P₁.constsIn_comp P₂ hC₁ hC₂, funext fun f => SLP.eval_comp P₁ P₂ f⟩
  rw [SLP.size_comp]
  omega

/-- Two maps of the same input, outputs side by side. -/
theorem sumElim {O₁ O₂ : Type*} {M₁ : (I → R) → O₁ → R} {M₂ : (I → R) → O₂ → R} {s₁ s₂ : ℕ}
    (h₁ : LinCost C M₁ s₁) (h₂ : LinCost C M₂ s₂) :
    LinCost C (fun f => Sum.elim (M₁ f) (M₂ f)) (s₁ + s₂) := by
  obtain ⟨P₁, hs₁, hC₁, rfl⟩ := h₁
  obtain ⟨P₂, hs₂, hC₂, rfl⟩ := h₂
  refine ⟨P₁.sumElim P₂, ?_, P₁.constsIn_sumElim P₂ hC₁ hC₂,
    funext fun f => SLP.eval_sumElim P₁ P₂ f⟩
  rw [SLP.size_sumElim]
  omega

/-- A block-diagonal family of maps: the costs add. -/
theorem sigma {ι : Type*} [Fintype ι] {I' O' : ι → Type*} (M : ∀ j, (I' j → R) → O' j → R)
    (s : ι → ℕ) (h : ∀ j, LinCost C (M j) (s j)) :
    LinCost C (fun (f : (Σ j, I' j) → R) (o : Σ j, O' j) => M o.1 (fun i => f ⟨o.1, i⟩) o.2)
      (∑ j, s j) := by
  classical
  -- the blocks indexed by a finset `T`, by induction on `T`
  have key : ∀ T : Finset ι, LinCost C (fun (f : (Σ j, I' j) → R)
      (o : {p : Σ j, O' j // p.1 ∈ T}) => M o.1.1 (fun i => f ⟨o.1.1, i⟩) o.1.2)
      (∑ j ∈ T, s j) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty]
      refine (zero (C := C)).congr ?_
      funext f o
      exact absurd o.2 (Finset.notMem_empty _)
    | insert a T ha ih =>
      rw [Finset.sum_insert ha]
      have hA : LinCost C (fun (f : (Σ j, I' j) → R) (o : O' a) => M a (fun i => f ⟨a, i⟩) o)
          (s a) := (h a).reindex (fun i => (⟨a, i⟩ : Σ j, I' j)) (fun o => o)
      have h2 := (hA.sumElim ih).reindex (fun p => p)
        (fun o : {p : Σ j, O' j // p.1 ∈ insert a T} =>
          if hj : o.1.1 = a then Sum.inl (cast (congrArg O' hj) o.1.2)
          else Sum.inr ⟨o.1, (Finset.mem_insert.1 o.2).resolve_left hj⟩)
      refine h2.congr ?_
      funext f o
      obtain ⟨⟨j, x⟩, hj⟩ := o
      by_cases hja : j = a
      · subst hja
        simp
      · simp [hja]
  exact (key Finset.univ).reindex (fun p => p) (fun o => ⟨o, Finset.mem_univ _⟩)

/-- One gate `a_o f(x_o) + b_o f(y_o)` per output, reading only inputs. -/
theorem inputGates [Fintype O] (a b : O → R) (x y : O → I) (ha : ∀ o, a o ∈ C)
    (hb : ∀ o, b o ∈ C) :
    LinCost C (fun f o => a o * f (x o) + b o * f (y o)) (Fintype.card O) :=
  ⟨SLP.inputGates a b x y, (SLP.size_inputGates a b x y).le,
    SLP.constsIn_inputGates a b x y ha hb, SLP.eval_inputGates a b x y⟩

/-- A linear combination of two maps: one more gate per output. -/
theorem lincomb [Fintype O] {M₁ M₂ : (I → R) → O → R} {s₁ s₂ : ℕ} (h₁ : LinCost C M₁ s₁)
    (h₂ : LinCost C M₂ s₂) {a b : R} (ha : a ∈ C) (hb : b ∈ C) :
    LinCost C (fun f o => a * M₁ f o + b * M₂ f o) (s₁ + s₂ + Fintype.card O) := by
  have h := comp (sumElim h₁ h₂)
    (inputGates (C := C) (fun _ : O => a) (fun _ => b) Sum.inl Sum.inr (fun _ => ha) (fun _ => hb))
  exact h

/-- A dense matrix with entries in `C`: at most `|O| |I|` gates. -/
theorem dense [Fintype I] [Fintype O] (A : O → I → R) (hA : ∀ o i, A o i ∈ C) (_h0 : (0 : R) ∈ C)
    (h1 : (1 : R) ∈ C) : LinCost C (fun f o => ∑ i, A o i * f i) (Fintype.card O * Fintype.card I) := by
  classical
  -- one row: a chain `w ← a_j f_j + 1 · w`
  have row : ∀ (a : I → R), (∀ i, a i ∈ C) → ∀ T : Finset I,
      LinCost C (fun (f : I → R) (_ : Unit) => ∑ i ∈ T, a i * f i) T.card := by
    intro a ha T
    induction T using Finset.induction_on with
    | empty =>
      rw [Finset.card_empty]
      exact (zero (C := C)).congr (by funext f u; simp)
    | insert j T hj ih =>
      have h₁ : LinCost C (fun (f : I → R) (_ : Unit) => f j) 0 :=
        (LinCost.id (C := C) (I := I)).reindex (fun i => i) (fun _ => j)
      have h₂ := lincomb h₁ ih (ha j) h1
      rw [Finset.card_insert_of_notMem hj]
      refine (h₂.congr ?_).mono (by simp)
      funext f u
      rw [Finset.sum_insert hj, one_mul]
  have hs := sigma (I' := fun _ : O => I) (O' := fun _ : O => Unit)
    (fun o f _ => ∑ i, A o i * f i) (fun _ => Fintype.card I)
    (fun o => row (A o) (hA o) Finset.univ)
  have h' := hs.reindex (fun p => p.2) (fun o => ⟨o, ()⟩)
  refine h'.mono ?_
  simp

/-- Every program computes a linear map. -/
theorem eq_sum [Fintype I] [DecidableEq I] {M : (I → R) → O → R} {s : ℕ} (h : LinCost C M s)
    (f : I → R) (o : O) : M f o = ∑ i, M (Pi.single i 1) o * f i := by
  obtain ⟨P, -, -, rfl⟩ := h
  rw [SLP.eval_eq_sum_rows]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SLP.eval_eq_sum_rows]
  congr 1
  simp [Pi.single_apply]

/-- **Transposition principle** (Section 3.3): reverse the gates and accumulate. -/
theorem transpose [Fintype I] [Fintype O] [DecidableEq I] {M : (I → R) → O → R} {s : ℕ}
    (h : LinCost C M s) (_h0 : (0 : R) ∈ C) (h1 : (1 : R) ∈ C) :
    LinCost C (transposeMap M) (2 * s + Fintype.card O) := by
  obtain ⟨P, hs, hC, rfl⟩ := h
  refine ⟨Transpose.prog P, ?_, Transpose.constsIn_prog h1 P hC, Transpose.eval_prog P⟩
  rw [Transpose.size_prog, SLP.size_def]
  rw [SLP.size_def] at hs
  omega

end LinCost

/-! ### Base change: simulating a program over a free `R`-algebra `S` -/

namespace BaseChange

variable {S : Type*} [CommRing S] [Algebra R S] {ι : Type*} [Fintype ι] (b : Module.Basis ι R S)

/-- The `S`-valued input with coordinates `v`. -/
noncomputable def toS (v : I × ι → R) : I → S := fun i => ∑ l, v (i, l) • b l

theorem repr_toS (v : I × ι → R) (i : I) (l : ι) : b.repr (toS b v i) l = v (i, l) := by
  simp only [toS, Module.Basis.repr_sum_self]

/-- Coordinates of a product: `b.repr (a * y) k = ∑ l, (leftMulMatrix b a) k l * b.repr y l`. -/
theorem repr_mul [DecidableEq ι] (a y : S) (k : ι) :
    b.repr (a * y) k = ∑ l, Algebra.leftMulMatrix b a k l * b.repr y l := by
  rw [← Algebra.leftMulMatrix_mulVec_repr]
  rfl

/-- The coordinates of all wires after the gates `pre`, as a function of the input coordinates:
`2 d²` gates per gate of `pre` (`d = |ι|`). -/
theorem sim (pre : List (Gate S I)) :
    LinCost (Set.univ : Set R) (fun (v : I × ι → R) (p : Wire I × ι) =>
      b.repr (read (toS b v) (run pre (toS b v)) p.1) p.2)
      (2 * Fintype.card ι ^ 2 * pre.length) := by
  classical
  induction pre using List.reverseRecOn with
  | nil =>
    have h := (LinCost.sumElim (LinCost.id (C := (Set.univ : Set R)) (I := I × ι))
      (LinCost.zero (C := (Set.univ : Set R)) (I := I × ι) (O := Unit))).reindex (fun x => x)
      (fun p : Wire I × ι => Sum.elim (fun i => Sum.inl (i, p.2)) (fun _ => Sum.inr ()) p.1)
    refine (h.congr ?_).mono (by simp)
    funext v p
    obtain ⟨w, l⟩ := p
    rcases w with i | m
    · simp [repr_toS]
    · simp
  | append_singleton pre gt ih =>
    set d := Fintype.card ι
    set A := Algebra.leftMulMatrix b gt.a
    set B := Algebra.leftMulMatrix b gt.b
    have hD := (LinCost.dense (C := (Set.univ : Set R))
      (fun k (q : ι ⊕ ι) => Sum.elim (A k) (B k) q) (fun _ _ => trivial) trivial trivial).reindex
      (fun q : ι ⊕ ι => Sum.elim (fun l => (gt.x, l)) (fun l => (gt.y, l)) q) (fun k : ι => k)
    have hG := (LinCost.sumElim (LinCost.id (C := (Set.univ : Set R)) (I := Wire I × ι)) hD).reindex
      (fun x => x)
      (fun p : Wire I × ι => if p.1 = Sum.inr pre.length then Sum.inr p.2 else Sum.inl p)
    have h := LinCost.comp ih hG
    refine (h.congr ?_).mono (le_of_eq ?_)
    · funext v p
      obtain ⟨w, k⟩ := p
      by_cases hw : w = Sum.inr pre.length
      · subst hw
        simp only [ite_true, Sum.elim_inr, Fintype.sum_sum_type, Sum.elim_inl]
        rw [read_run_append_single_self]
        simp only [Gate.eval, map_add, Finsupp.add_apply, repr_mul]
        rfl
      · simp only [hw, ite_false, Sum.elim_inl]
        rw [read_run_append_single_of_ne _ _ _ hw]
    · simp only [List.length_append, List.length_cons, List.length_nil, Fintype.card_sum]
      ring

/-- The coordinates of the scalar inputs:
`algebraMap R S (f i) = ∑ l, (f i * b.repr 1 l) • b l`. -/
theorem toS_input (f : I → R) :
    toS b (fun p : I × ι => b.repr 1 p.2 * f p.1 + 0 * f p.1) = fun i => algebraMap R S (f i) := by
  funext i
  simp only [toS, zero_mul, add_zero]
  calc ∑ l, (b.repr 1 l * f i) • b l = f i • ∑ l, b.repr 1 l • b l := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [mul_comm, mul_smul]
    _ = algebraMap R S (f i) := by rw [b.sum_repr, Algebra.algebraMap_eq_smul_one]

end BaseChange

namespace LinCost

/-- **Base change** (Section 3.4): a program over an `R`-algebra `S` that is free with basis `b`
is simulated over `R`, coordinate by coordinate. -/
theorem baseChange {S : Type*} [CommRing S] [Algebra R S] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R S) [Fintype I] {M : (I → S) → O → S} {s : ℕ}
    (h : LinCost (Set.univ : Set S) M s) (j : ι) :
    LinCost (Set.univ : Set R) (fun (f : I → R) (o : O) => b.repr (M (fun i => algebraMap R S (f i)) o) j)
      (2 * Fintype.card ι ^ 2 * s + Fintype.card ι * Fintype.card I) := by
  obtain ⟨P, hs, -, rfl⟩ := h
  have hE := LinCost.inputGates (C := (Set.univ : Set R)) (fun p : I × ι => b.repr 1 p.2)
    (fun _ => 0) Prod.fst Prod.fst (fun _ => trivial) (fun _ => trivial)
  have h := (LinCost.comp hE (BaseChange.sim b P.gates)).reindex (fun i => i)
    (fun o => (P.out o, j))
  refine (h.congr ?_).mono ?_
  · funext f o
    show b.repr (read (BaseChange.toS b _) (run P.gates (BaseChange.toS b _)) (P.out o)) j = _
    rw [BaseChange.toS_input]
    rfl
  · rw [SLP.size_def] at hs
    have := Nat.mul_le_mul_left (2 * Fintype.card ι ^ 2) hs
    rw [Fintype.card_prod]
    nlinarith

end LinCost

/-! ### The fast Fourier transform on `K^e` -/

section DFT

variable {K : Type*} [Field K] [Fintype K] {S : Type*} [CommRing S]

/-- Sums over `Fin (e + 1) → K`, splitting off the first coordinate. -/
theorem sum_pi_fin_succ {M : Type*} [AddCommMonoid M] (e : ℕ) (F : (Fin (e + 1) → K) → M) :
    ∑ x, F x = ∑ x₀ : K, ∑ x' : Fin e → K, F (Fin.cons x₀ x') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => K) _ _ (fun _ => rfl)).symm

/-- One row–column step: `q` copies of a transform on `K^e` (one for each value of the first
coordinate), then `q^e` dense `q × q` transforms along the first coordinate. -/
theorem LinCost.rowcol {C : Set S} (e : ℕ) (A : K → K → S) (hA : ∀ a b, A a b ∈ C)
    (h0 : (0 : S) ∈ C) (h1 : (1 : S) ∈ C) {T : ((Fin e → K) → S) → (Fin e → K) → S} {c : ℕ}
    (hT : LinCost C T c) :
    LinCost C (fun (h : (Fin (e + 1) → K) → S) (ξ : Fin (e + 1) → K) =>
        ∑ x₀, A (ξ 0) x₀ * T (fun x' => h (Fin.cons x₀ x')) (Fin.tail ξ))
      (Fintype.card K * c + Fintype.card K ^ e * (Fintype.card K * Fintype.card K)) := by
  have p1 := (LinCost.sigma (I' := fun _ : K => Fin e → K) (O' := fun _ : K => Fin e → K)
    (fun _ => T) (fun _ => c) (fun _ => hT)).reindex
    (fun p : (Σ _ : K, Fin e → K) => (Fin.cons p.1 p.2 : Fin (e + 1) → K)) (fun o => o)
  have p2 := (LinCost.sigma (I' := fun _ : (Fin e → K) => K) (O' := fun _ : (Fin e → K) => K)
    (fun _ g ξ₀ => ∑ x₀, A ξ₀ x₀ * g x₀) (fun _ => Fintype.card K * Fintype.card K)
    (fun _ => LinCost.dense A hA h0 h1)).reindex
    (fun p : (Σ _ : Fin e → K, K) => (⟨p.2, p.1⟩ : Σ _ : K, Fin e → K))
    (fun ξ : Fin (e + 1) → K => (⟨Fin.tail ξ, ξ 0⟩ : Σ _ : Fin e → K, K))
  refine (LinCost.comp p1 p2).mono (le_of_eq ?_)
  simp [Finset.sum_const, Finset.card_univ]

theorem dft_zero (F : FourierData K S) (h : (Fin 0 → K) → S) (ξ : Fin 0 → K) :
    dft F 0 h ξ = h ξ := by
  unfold dft
  rw [Fintype.sum_unique]
  simp [Subsingleton.elim (default : Fin 0 → K) ξ]

theorem dft_succ (F : FourierData K S) (e : ℕ) (h : (Fin (e + 1) → K) → S)
    (ξ : Fin (e + 1) → K) :
    dft F (e + 1) h ξ =
      ∑ x₀, F.ψ (ξ 0 * x₀) * dft F e (fun x' => h (Fin.cons x₀ x')) (Fin.tail ξ) := by
  unfold dft
  rw [sum_pi_fin_succ (M := S)]
  refine Finset.sum_congr rfl fun x₀ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [Fin.sum_univ_succ, Fin.cons_zero, AddChar.map_add_eq_mul]
  simp only [Fin.cons_succ, Fin.tail]
  ring

theorem idft_zero (F : FourierData K S) (g : (Fin 0 → K) → S) (x : Fin 0 → K) :
    idft F 0 g x = g x := by
  unfold idft
  rw [Fintype.sum_unique]
  simp [Subsingleton.elim (default : Fin 0 → K) x]

theorem idft_succ (F : FourierData K S) (e : ℕ) (g : (Fin (e + 1) → K) → S)
    (x : Fin (e + 1) → K) :
    idft F (e + 1) g x = ∑ ξ₀, F.qinv * F.ψ (-(ξ₀ * x 0)) *
      idft F e (fun ξ' => g (Fin.cons ξ₀ ξ')) (Fin.tail x) := by
  unfold idft
  rw [sum_pi_fin_succ (M := S)]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ξ₀ _ => Finset.sum_congr rfl fun ξ' _ => ?_
  rw [Fin.sum_univ_succ (M := K), Fin.cons_zero, neg_add, AddChar.map_add_eq_mul]
  simp only [Fin.cons_succ, Fin.tail]
  ring

/-- Row–column FFT: `e` passes of `q^{e-1}` length-`q` transforms, each a dense `q × q` matrix. -/
theorem dft_cost (F : FourierData K S) {C : Set S} (hC : F.consts ⊆ C) (e : ℕ) :
    LinCost C (dft F e) (e * Fintype.card K ^ (e + 1)) := by
  have h0 : (0 : S) ∈ C := hC (Or.inl rfl)
  have h1 : (1 : S) ∈ C := hC (Or.inr (Or.inl rfl))
  induction e with
  | zero =>
    refine (LinCost.id.congr ?_).mono (by simp)
    funext h ξ
    exact (dft_zero F h ξ).symm
  | succ e ih =>
    have := LinCost.rowcol e (fun a b => F.ψ (a * b))
      (fun a b => hC (Or.inr (Or.inr (Or.inr (Or.inl ⟨a * b, rfl⟩))))) h0 h1 ih
    refine (this.congr ?_).mono (le_of_eq ?_)
    · funext h ξ
      exact (dft_succ F e h ξ).symm
    · ring

theorem idft_cost (F : FourierData K S) {C : Set S} (hC : F.consts ⊆ C) (e : ℕ) :
    LinCost C (idft F e) (e * Fintype.card K ^ (e + 1)) := by
  have h0 : (0 : S) ∈ C := hC (Or.inl rfl)
  have h1 : (1 : S) ∈ C := hC (Or.inr (Or.inl rfl))
  induction e with
  | zero =>
    refine (LinCost.id.congr ?_).mono (by simp)
    funext g x
    exact (idft_zero F g x).symm
  | succ e ih =>
    have := LinCost.rowcol e (fun a b => F.qinv * F.ψ (-(b * a)))
      (fun a b => hC (Or.inr (Or.inr (Or.inr (Or.inr ⟨-(b * a), rfl⟩))))) h0 h1 ih
    refine (this.congr ?_).mono (le_of_eq ?_)
    · funext g x
      exact (idft_succ F e g x).symm
    · ring

end DFT

end SubspaceConvolution.Circuit
