/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Circuit.Run

/-!
# The transposition principle (Section 3.3)

From a linear program `P` with inputs `I`, outputs `O` and `T` gates we build a program for the
transposed map with `|O| + 2T` gates.  Every wire `w` of `P` gets an accumulator (initially the
always-zero wire).  First each new input `g o` is added to the accumulator of the output wire
`P.out o`; then the gates are traversed backwards, and a gate `z = a x + b y` triggers
`acc_x ← acc_x + a acc_z` and `acc_y ← acc_y + b acc_z`.  The accumulators of the input wires are
the outputs.

Correctness is the invariant `∑_w acc(w) · val_t(w) = ⟨g, M f⟩` (for every input `f` of `P`),
where `val_t` are the wire values of `P` after its first `t` gates; at `t = 0` only the input wires
carry values, which identifies the accumulators of the inputs with the transposed map.
-/

open Finset

set_option linter.unusedSectionVars false

namespace SubspaceConvolution.Circuit

namespace Transpose

variable {R : Type*} [CommRing R] {I O : Type*} [DecidableEq I]

/-- A construction state: the gates built so far, and for every wire of the original program the
gate number holding its current accumulator (an out-of-range number reads as zero). -/
abbrev State (R I O : Type*) := List (Gate R O) × (Wire I → ℕ)

/-- Add `c · src` to the accumulator of the wire `w`: one gate `1 · acc_w + c · src`. -/
def addTo (st : State R I O) (w : Wire I) (c : R) (src : Wire O) : State R I O :=
  (st.1 ++ [⟨1, Sum.inr (st.2 w), c, src⟩], Function.update st.2 w st.1.length)

/-- The first phase: add each input `g o` to the accumulator of the output wire `out o`. -/
def phase1 (out : O → Wire I) : List O → State R I O → State R I O
  | [], st => st
  | o :: os, st => phase1 out os (addTo st (out o) 1 (Sum.inl o))

/-- Transposing gate number `t`, `gt = (z = a x + b y)`: `acc_x += a acc_z`, `acc_y += b acc_z`. -/
def step (gt : Gate R I) (t : ℕ) (st : State R I O) : State R I O :=
  addTo (addTo st gt.x gt.a (Sum.inr (st.2 (Sum.inr t)))) gt.y gt.b (Sum.inr (st.2 (Sum.inr t)))

/-- The second phase, over the gates in reverse order (`gt :: rest` is gate number
`rest.length`). -/
def phase2 : List (Gate R I) → State R I O → State R I O
  | [], st => st
  | gt :: rest, st => phase2 rest (step gt rest.length st)

/-- The transposed program; `N = |O| + 2T` (its number of gates) serves as the zero wire. -/
noncomputable def prog [Fintype O] (P : SLP R I O) : SLP R O I :=
  ⟨(phase2 P.gates.reverse (phase1 P.out (Finset.univ : Finset O).toList
      ([], fun _ => Fintype.card O + 2 * P.gates.length))).1,
    fun i => Sum.inr ((phase2 P.gates.reverse (phase1 P.out (Finset.univ : Finset O).toList
      ([], fun _ => Fintype.card O + 2 * P.gates.length))).2 (Sum.inl i))⟩

/-- Every accumulator is an already computed gate, or the zero wire `N`. -/
def Valid (N : ℕ) (st : State R I O) : Prop := ∀ w, st.2 w < st.1.length ∨ st.2 w = N

/-- The current value of the accumulator of `w`, on the input `g` of the transposed program. -/
def acc (g : O → R) (st : State R I O) (w : Wire I) : R := (run st.1 g).getD (st.2 w) 0

/-! ### One update -/

theorem length_addTo (st : State R I O) (w : Wire I) (c : R) (src : Wire O) :
    (addTo st w c src).1.length = st.1.length + 1 := by
  simp [addTo]

theorem valid_addTo {N : ℕ} {st : State R I O} (hst : Valid N st) (w : Wire I) (c : R)
    (src : Wire O) : Valid N (addTo st w c src) := by
  intro w'
  rw [length_addTo]
  by_cases h : w' = w
  · left
    subst h
    simp [addTo]
  · have he : (addTo st w c src).2 w' = st.2 w' := by simp [addTo, h]
    rw [he]
    rcases hst w' with h' | h'
    · left
      omega
    · right
      exact h'

theorem consts_addTo {C : Set R} {st : State R I O} (hst : ∀ q ∈ st.1, q.a ∈ C ∧ q.b ∈ C)
    (h1 : (1 : R) ∈ C) (w : Wire I) {c : R} (hc : c ∈ C) (src : Wire O) :
    ∀ q ∈ (addTo st w c src).1, q.a ∈ C ∧ q.b ∈ C := by
  intro q hq
  simp only [addTo, List.mem_append, List.mem_singleton] at hq
  rcases hq with hq | rfl
  · exact hst q hq
  · exact ⟨h1, hc⟩

theorem getD_run_addTo {N : ℕ} (g : O → R) (st : State R I O) (w : Wire I) (c : R)
    (src : Wire O) (hN : st.1.length < N) {j : ℕ} (hj : j < st.1.length ∨ j = N) :
    (run (addTo st w c src).1 g).getD j 0 = (run st.1 g).getD j 0 := by
  simp only [addTo]
  rw [run_append_single]
  apply getD_append_single_of_ne
  rw [length_run]
  omega

theorem acc_addTo {N : ℕ} (g : O → R) {st : State R I O} (hst : Valid N st)
    (hN : st.1.length < N) (w : Wire I) (c : R) (src : Wire O) (w' : Wire I) :
    acc g (addTo st w c src) w' =
      if w' = w then acc g st w + c * read g (run st.1 g) src else acc g st w' := by
  by_cases h : w' = w
  · subst h
    rw [ite_eq_left rfl]
    have hl := length_run st.1 g
    simp only [acc, addTo, Function.update_self]
    rw [run_append_single, ← hl, getD_append_single_self]
    simp [Gate.eval]
  · rw [ite_eq_right h]
    have he : (addTo st w c src).2 w' = st.2 w' := by simp [addTo, h]
    unfold acc
    rw [he]
    exact getD_run_addTo g st w c src hN (hst w')

/-- The effect of one update on a weighted sum of the accumulators. -/
theorem sum_acc_addTo {N : ℕ} (g : O → R) {st : State R I O} (hst : Valid N st)
    (hN : st.1.length < N) (Ws : Finset (Wire I)) (φ : Wire I → R) (w : Wire I)
    (hφ : w ∉ Ws → φ w = 0) (c : R) (src : Wire O) :
    ∑ w' ∈ Ws, acc g (addTo st w c src) w' * φ w' =
      ∑ w' ∈ Ws, acc g st w' * φ w' + c * read g (run st.1 g) src * φ w := by
  have key : ∀ w', acc g (addTo st w c src) w' * φ w' =
      acc g st w' * φ w' + if w' = w then c * read g (run st.1 g) src * φ w' else 0 := by
    intro w'
    rw [acc_addTo g hst hN]
    split_ifs with h
    · subst h
      ring
    · ring
  rw [Finset.sum_congr rfl fun w' _ => key w', Finset.sum_add_distrib, Finset.sum_ite_eq']
  split_ifs with hw
  · rfl
  · rw [hφ hw, mul_zero, add_zero]

/-! ### The first phase -/

theorem length_phase1 (out : O → Wire I) (os : List O) (st : State R I O) :
    (phase1 out os st).1.length = st.1.length + os.length := by
  induction os generalizing st with
  | nil => simp [phase1]
  | cons o os ih =>
    simp only [phase1, ih, length_addTo, List.length_cons]
    omega

theorem valid_phase1 {N : ℕ} (out : O → Wire I) (os : List O) (st : State R I O)
    (hst : Valid N st) : Valid N (phase1 out os st) := by
  induction os generalizing st with
  | nil => exact hst
  | cons o os ih => exact ih _ (valid_addTo hst _ _ _)

theorem consts_phase1 {C : Set R} (h1 : (1 : R) ∈ C) (out : O → Wire I) (os : List O)
    (st : State R I O) (hst : ∀ q ∈ st.1, q.a ∈ C ∧ q.b ∈ C) :
    ∀ q ∈ (phase1 out os st).1, q.a ∈ C ∧ q.b ∈ C := by
  induction os generalizing st with
  | nil => exact hst
  | cons o os ih => exact ih _ (consts_addTo hst h1 _ h1 _)

theorem sum_phase1 {N : ℕ} (g : O → R) (out : O → Wire I) (Ws : Finset (Wire I))
    (φ : Wire I → R) (hφ : ∀ w, w ∉ Ws → φ w = 0) (os : List O) (st : State R I O)
    (hst : Valid N st) (hN : st.1.length + os.length ≤ N) :
    ∑ w ∈ Ws, acc g (phase1 out os st) w * φ w =
      ∑ w ∈ Ws, acc g st w * φ w + (os.map fun o => g o * φ (out o)).sum := by
  induction os generalizing st with
  | nil => simp [phase1]
  | cons o os ih =>
    simp only [List.length_cons] at hN
    simp only [phase1]
    rw [ih _ (valid_addTo hst _ _ _) (by rw [length_addTo]; omega),
      sum_acc_addTo g hst (by omega) Ws φ (out o) (hφ _) 1 (Sum.inl o)]
    simp only [List.map_cons, List.sum_cons, read_inl]
    ring

/-! ### The second phase -/

theorem length_step (gt : Gate R I) (t : ℕ) (st : State R I O) :
    (step gt t st).1.length = st.1.length + 2 := by
  simp only [step, length_addTo]

theorem valid_step {N : ℕ} (gt : Gate R I) (t : ℕ) {st : State R I O} (hst : Valid N st) :
    Valid N (step gt t st) :=
  valid_addTo (valid_addTo hst _ _ _) _ _ _

theorem length_phase2 (gs : List (Gate R I)) (st : State R I O) :
    (phase2 gs st).1.length = st.1.length + 2 * gs.length := by
  induction gs generalizing st with
  | nil => simp [phase2]
  | cons gt gs ih =>
    simp only [phase2, ih, length_step, List.length_cons]
    ring

theorem valid_phase2 {N : ℕ} (gs : List (Gate R I)) (st : State R I O) (hst : Valid N st) :
    Valid N (phase2 gs st) := by
  induction gs generalizing st with
  | nil => exact hst
  | cons gt gs ih => exact ih _ (valid_step _ _ hst)

theorem consts_phase2 {C : Set R} (h1 : (1 : R) ∈ C) (gs : List (Gate R I))
    (hgs : ∀ gt ∈ gs, gt.a ∈ C ∧ gt.b ∈ C) (st : State R I O)
    (hst : ∀ q ∈ st.1, q.a ∈ C ∧ q.b ∈ C) :
    ∀ q ∈ (phase2 gs st).1, q.a ∈ C ∧ q.b ∈ C := by
  induction gs generalizing st with
  | nil => exact hst
  | cons gt gs ih =>
    have hgt := hgs gt List.mem_cons_self
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _
      (consts_addTo (consts_addTo hst h1 _ hgt.1 _) h1 _ hgt.2 _)

variable [Fintype I]

/-- The wires that can carry nonzero values in a program with `T` gates. -/
def wires (T : ℕ) : Finset (Wire I) := (Finset.univ : Finset I).disjSum (Finset.range T)

theorem mem_wires_inr {T m : ℕ} : (Sum.inr m : Wire I) ∈ wires T ↔ m < T := by
  simp [wires]

theorem read_eq_zero_of_not_mem_wires {T : ℕ} (gs : List (Gate R I)) (hgs : gs.length ≤ T)
    (f : I → R) {w : Wire I} (hw : w ∉ wires T) : read f (run gs f) w = 0 := by
  rcases w with i | m
  · exact absurd (by simp [wires]) hw
  · rw [mem_wires_inr] at hw
    exact read_run_length gs f (by omega)

/-- One transposed gate preserves the invariant. -/
theorem sum_step {N T : ℕ} (g : O → R) (pre : List (Gate R I)) (gt : Gate R I)
    (hT : pre.length < T) {st : State R I O} (hst : Valid N st) (hN : st.1.length + 2 ≤ N)
    (f : I → R) :
    ∑ w ∈ wires T, acc g (step gt pre.length st) w * read f (run pre f) w =
      ∑ w ∈ wires T, acc g st w * read f (run (pre ++ [gt]) f) w := by
  have hφ : ∀ w, w ∉ wires T → read f (run pre f) w = 0 :=
    fun w hw => read_eq_zero_of_not_mem_wires pre hT.le f hw
  have hst' : Valid N (addTo st gt.x gt.a (Sum.inr (st.2 (Sum.inr pre.length)))) :=
    valid_addTo hst _ _ _
  have hz : read g (run (addTo st gt.x gt.a (Sum.inr (st.2 (Sum.inr pre.length)))).1 g)
      (Sum.inr (st.2 (Sum.inr pre.length))) = acc g st (Sum.inr pre.length) := by
    simp only [read_inr, acc]
    exact getD_run_addTo g st _ _ _ (by omega) (hst _)
  rw [step, sum_acc_addTo g hst' (by rw [length_addTo]; omega) _ _ gt.y (hφ _),
    sum_acc_addTo g hst (by omega) _ _ gt.x (hφ _), hz]
  have hnew : ∀ w, read f (run (pre ++ [gt]) f) w = read f (run pre f) w +
      if w = Sum.inr pre.length then
        gt.a * read f (run pre f) gt.x + gt.b * read f (run pre f) gt.y else 0 := by
    intro w
    by_cases hw : w = Sum.inr pre.length
    · subst hw
      rw [read_run_append_single_self, ite_eq_left rfl, read_run_length pre f le_rfl, zero_add]
      rfl
    · rw [read_run_append_single_of_ne pre gt f hw, ite_eq_right hw, add_zero]
  simp only [hnew, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq']
  rw [ite_eq_left (mem_wires_inr.2 hT)]
  simp only [read_inr, acc]
  ring

theorem sum_phase2 {N T : ℕ} (g : O → R) (Φ : (I → R) → R) (pre : List (Gate R I)) :
    ∀ st : State R I O, Valid N st → st.1.length + 2 * pre.length ≤ N → pre.length ≤ T →
      (∀ f, ∑ w ∈ wires T, acc g st w * read f (run pre f) w = Φ f) →
      ∀ f, ∑ w ∈ wires T, acc g (phase2 pre.reverse st) w * read f (run [] f) w = Φ f := by
  induction pre using List.reverseRecOn with
  | nil =>
    intro st _ _ _ h
    exact h
  | append_singleton pre gt ih =>
    intro st hst hN hT h
    simp only [List.length_append, List.length_cons, List.length_nil] at hN hT
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append, phase2,
      List.length_reverse]
    refine ih (step gt pre.length st) (valid_step _ _ hst) (by rw [length_step]; omega)
      (by omega) (fun f => ?_)
    rw [sum_step g pre gt (by omega) hst (by omega) f]
    exact h f

variable [Fintype O]

theorem size_prog (P : SLP R I O) : (prog P).size = Fintype.card O + 2 * P.size := by
  simp [prog, SLP.size, length_phase2, length_phase1]

theorem constsIn_prog {C : Set R} (h1 : (1 : R) ∈ C) (P : SLP R I O) (hP : P.ConstsIn C) :
    (prog P).ConstsIn C :=
  consts_phase2 h1 _ (fun gt hgt => hP gt (List.mem_reverse.1 hgt)) _
    (consts_phase1 h1 _ _ _ (fun _ hq => absurd hq List.not_mem_nil))

/-- **The transposition principle**: `prog P` computes the transpose of `P.eval`. -/
theorem eval_prog (P : SLP R I O) : (prog P).eval = transposeMap P.eval := by
  funext g i
  -- the states after the two phases
  set N := Fintype.card O + 2 * P.gates.length with hNdef
  set st₀ : State R I O := ([], fun _ => N) with hst₀
  set st₁ := phase1 P.out (Finset.univ : Finset O).toList st₀ with hst₁
  set st₂ := phase2 P.gates.reverse st₁ with hst₂
  have hv₀ : Valid N st₀ := fun _ => Or.inr rfl
  have hv₁ : Valid N st₁ := valid_phase1 _ _ _ hv₀
  have hl₁ : st₁.1.length = Fintype.card O := by
    rw [hst₁, length_phase1]
    simp [hst₀]
  -- the invariant after the first phase
  have h₁ : ∀ f, ∑ w ∈ wires P.gates.length, acc g st₁ w * read f (run P.gates f) w =
      ∑ o, g o * P.eval f o := by
    intro f
    rw [hst₁, sum_phase1 g P.out _ _ (fun w hw => read_eq_zero_of_not_mem_wires P.gates le_rfl f hw)
      _ st₀ hv₀ (by simp [hst₀, hNdef])]
    have h0 : ∀ w, acc g st₀ w = 0 := fun w => by simp [acc, hst₀]
    simp only [h0, zero_mul, Finset.sum_const_zero, zero_add, Finset.sum_map_toList]
    rfl
  -- the invariant after the second phase
  have h₂ : ∀ f, ∑ w ∈ wires P.gates.length, acc g st₂ w * read f (run [] f) w =
      ∑ o, g o * P.eval f o :=
    sum_phase2 g (fun f => ∑ o, g o * P.eval f o) P.gates st₁ hv₁ (by rw [hl₁]) le_rfl h₁
  have key : ∀ f, ∑ i', acc g st₂ (Sum.inl i') * f i' = ∑ o, g o * P.eval f o := by
    intro f
    rw [← h₂ f, wires, Finset.sum_disjSum]
    simp
  have := key (Pi.single i 1)
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at this
  show acc g st₂ (Sum.inl i) = _
  rw [this, transposeMap]
  exact Finset.sum_congr rfl fun o _ => mul_comm _ _

end Transpose

end SubspaceConvolution.Circuit
