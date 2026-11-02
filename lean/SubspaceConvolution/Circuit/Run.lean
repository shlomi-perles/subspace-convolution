/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Circuit.Defs

/-!
# Evaluating straight-line programs

Facts about the evaluation fold `gs.foldl (fun vals g => vals ++ [ev g vals]) init` (which is how
both linear programs, `run`, and general arithmetic programs are evaluated), relabelling of wires,
and the basic combinators on linear programs used to prove the cost-model API of
`SubspaceConvolution.Circuit.SLP`:

* `SLP.reindex` — relabel inputs and outputs;
* `SLP.comp` — run `P₂` on the outputs of `P₁`;
* `SLP.sumElim` — run two programs on the same input, outputs side by side;
* `SLP.inputGates` — one gate per output, reading only inputs;
* `rows` — the coefficient row of every gate, so that `P.eval f o = ∑ i, row i * f i`.

Concatenating programs must keep "zero wires" (references to gates that are not computed yet)
equal to zero: references past the end of the first program are normalized by `normW` to a wire
that is out of range for the whole combined program.
-/

open Finset

set_option linter.unusedSectionVars false

namespace SubspaceConvolution.Circuit

/-! ### The evaluation fold -/

section Fold

variable {G G' V W : Type*}

/-- The fold evaluating a straight-line program: append the value of each gate in turn. -/
def evalFold (ev : G → List V → V) (gs : List G) (init : List V) : List V :=
  gs.foldl (fun vals g => vals ++ [ev g vals]) init

@[simp] theorem evalFold_nil (ev : G → List V → V) (init : List V) :
    evalFold ev [] init = init := rfl

theorem evalFold_cons (ev : G → List V → V) (g : G) (gs : List G) (init : List V) :
    evalFold ev (g :: gs) init = evalFold ev gs (init ++ [ev g init]) := rfl

theorem evalFold_append (ev : G → List V → V) (gs hs : List G) (init : List V) :
    evalFold ev (gs ++ hs) init = evalFold ev hs (evalFold ev gs init) :=
  List.foldl_append

theorem length_evalFold (ev : G → List V → V) (gs : List G) (init : List V) :
    (evalFold ev gs init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    rw [evalFold_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- Gates relabelled by `φ` and evaluated after a fixed prefix `A` of values behave like the
original gates, provided `ev' (φ g) (A ++ B) = ev g B` for all short enough `B`. -/
theorem evalFold_map_append (ev : G → List V → V) (ev' : G' → List V → V) (φ : G → G')
    (A : List V) (L : ℕ) (gs : List G)
    (hφ : ∀ g ∈ gs, ∀ B : List V, B.length < L → ev' (φ g) (A ++ B) = ev g B)
    (B₀ : List V) (hB₀ : B₀.length + gs.length ≤ L) :
    evalFold ev' (gs.map φ) (A ++ B₀) = A ++ evalFold ev gs B₀ := by
  induction gs generalizing B₀ with
  | nil => simp
  | cons g gs ih =>
    simp only [List.length_cons] at hB₀
    rw [List.map_cons, evalFold_cons, evalFold_cons,
      hφ g List.mem_cons_self B₀ (by omega), List.append_assoc]
    exact ih (fun g' hg' B hB => hφ g' (List.mem_cons_of_mem _ hg') B hB) _
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)

/-- Evaluation commutes with a map of values that is compatible with the gates. -/
theorem evalFold_hom (ev : G → List V → V) (ev' : G → List W → W) (ψ : V → W)
    (h : ∀ g vs, ev' g (vs.map ψ) = ψ (ev g vs)) (gs : List G) (init : List V) :
    evalFold ev' gs (init.map ψ) = (evalFold ev gs init).map ψ := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    rw [evalFold_cons, evalFold_cons, h, ← ih]
    simp

/-- Gates whose values do not depend on earlier gates (e.g. gates reading only inputs). -/
theorem evalFold_const (ev : G → List V → V) (c : G → V) (gs : List G)
    (h : ∀ g ∈ gs, ∀ vs, ev g vs = c g) (init : List V) :
    evalFold ev gs init = init ++ gs.map c := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    rw [evalFold_cons, ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')),
      h g List.mem_cons_self]
    simp

end Fold

/-! ### Linear programs -/

section Linear

variable {R : Type*} [CommRing R] {I J O : Type*}

@[simp] theorem read_inl (f : I → R) (vals : List R) (i : I) :
    read f vals (Sum.inl i) = f i := rfl

@[simp] theorem read_inr (f : I → R) (vals : List R) (j : ℕ) :
    read f vals (Sum.inr j) = vals.getD j 0 := rfl

theorem run_eq_evalFold (gs : List (Gate R I)) (f : I → R) :
    run gs f = evalFold (fun g vals => g.eval f vals) gs [] := rfl

@[simp] theorem run_nil (f : I → R) : run ([] : List (Gate R I)) f = [] := rfl

@[simp] theorem length_run (gs : List (Gate R I)) (f : I → R) :
    (run gs f).length = gs.length := by
  rw [run_eq_evalFold, length_evalFold]
  simp

/-- Appending a gate does not change the earlier values. -/
theorem run_append_single (gs : List (Gate R I)) (g : Gate R I) (f : I → R) :
    run (gs ++ [g]) f = run gs f ++ [g.eval f (run gs f)] := by
  rw [run_eq_evalFold, evalFold_append]
  rfl

theorem getD_append_single_of_ne (vals : List R) (v : R) {j : ℕ} (hj : j ≠ vals.length) :
    (vals ++ [v]).getD j 0 = vals.getD j 0 := by
  rcases lt_or_gt_of_ne hj with h | h
  · exact List.getD_append _ _ _ _ h
  · have h' : (vals ++ [v]).length ≤ j := by simp; omega
    rw [List.getD_eq_default _ _ h', List.getD_eq_default _ _ (by omega)]

theorem getD_append_single_self (vals : List R) (v : R) :
    (vals ++ [v]).getD vals.length 0 = v := by
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

/-- The value of the new wire after one more gate `g`. -/
theorem read_run_append_single_self (gs : List (Gate R I)) (g : Gate R I) (f : I → R) :
    read f (run (gs ++ [g]) f) (Sum.inr gs.length) = g.eval f (run gs f) := by
  rw [run_append_single, read_inr]
  have := getD_append_single_self (run gs f) (g.eval f (run gs f))
  rw [length_run] at this
  exact this

/-- One more gate does not change the values of the other wires. -/
theorem read_run_append_single_of_ne (gs : List (Gate R I)) (g : Gate R I) (f : I → R)
    {w : Wire I} (hw : w ≠ Sum.inr gs.length) :
    read f (run (gs ++ [g]) f) w = read f (run gs f) w := by
  rw [run_append_single]
  rcases w with i | j
  · rfl
  · have hj' : j ≠ (run gs f).length := by
      rw [length_run]
      exact fun h => hw (by rw [h])
    exact getD_append_single_of_ne _ _ hj'

/-- The wire `inr t` reads as zero after `t` gates. -/
theorem read_run_length (gs : List (Gate R I)) (f : I → R) {m : ℕ} (hm : gs.length ≤ m) :
    read f (run gs f) (Sum.inr m) = 0 := by
  simp only [read_inr]
  exact List.getD_eq_default _ _ (by simpa using hm)

/-! #### Relabelling wires -/

/-- Relabel the wires of a gate. -/
def Gate.mapW (W : Wire J → Wire I) (g : Gate R J) : Gate R I := ⟨g.a, W g.x, g.b, W g.y⟩

theorem Gate.eval_mapW (W : Wire J → Wire I) (g : Gate R J) (f : I → R) (vals : List R) :
    (g.mapW W).eval f vals = g.a * read f vals (W g.x) + g.b * read f vals (W g.y) := rfl

/-- The wires of a program placed after `s` gates of another one: its input `j` becomes the wire
`μ j`, and its gate `m` becomes gate `m + s`. -/
def shiftW (μ : J → Wire I) (s : ℕ) : Wire J → Wire I :=
  Sum.elim μ (fun m => Sum.inr (m + s))

/-- References to gates numbered `≥ s` (which read as `0` in a program with `s` gates) are sent
to the gate number `N`, which still reads as `0` in every extension to at most `N` gates. -/
def normW (s N : ℕ) : Wire I → Wire I :=
  Sum.elim Sum.inl (fun m => if m < s then Sum.inr m else Sum.inr N)

theorem read_shiftW (μ : J → Wire I) (f : I → R) (g : J → R) (A B : List R) {s : ℕ}
    (hs : A.length = s) (hμ : ∀ j, read f (A ++ B) (μ j) = g j) (w : Wire J) :
    read f (A ++ B) (shiftW μ s w) = read g B w := by
  rcases w with j | m
  · exact hμ j
  · simp only [shiftW, Sum.elim_inr, read_inr]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega

theorem read_normW (f : I → R) (A B : List R) {s N : ℕ} (hs : A.length = s)
    (hN : (A ++ B).length ≤ N) (w : Wire I) :
    read f (A ++ B) (normW s N w) = read f A w := by
  rcases w with i | m
  · rfl
  · simp only [normW, Sum.elim_inr]
    split_ifs with h
    · simp only [read_inr]
      exact List.getD_append _ _ _ _ (by omega)
    · simp only [read_inr]
      rw [List.getD_eq_default _ _ hN, List.getD_eq_default _ _ (by omega)]

/-- Running a relabelled program `gs₂` after `gs₁`: the values of the combined run are those of
`gs₁` followed by those of `gs₂` on the inputs `g`, provided the wires `μ j` read `g j`. -/
theorem run_append_mapW (gs₁ : List (Gate R I)) (gs₂ : List (Gate R J)) (μ : J → Wire I)
    (f : I → R) (g : J → R)
    (hμ : ∀ j (B : List R), B.length ≤ gs₂.length → read f (run gs₁ f ++ B) (μ j) = g j) :
    run (gs₁ ++ gs₂.map (Gate.mapW (shiftW μ gs₁.length))) f = run gs₁ f ++ run gs₂ g := by
  have hl : (run gs₁ f).length = gs₁.length := length_run _ _
  have key := evalFold_map_append (fun g' vals => g'.eval g vals)
    (fun g' vals => g'.eval f vals) (Gate.mapW (shiftW μ gs₁.length)) (run gs₁ f)
    gs₂.length gs₂ ?_ [] (by simp)
  · rw [List.append_nil] at key
    rw [run_eq_evalFold, evalFold_append]
    exact key
  · intro g' _ B hB
    show g'.a * read f (run gs₁ f ++ B) (shiftW μ gs₁.length g'.x) +
        g'.b * read f (run gs₁ f ++ B) (shiftW μ gs₁.length g'.y) =
      g'.a * read g B g'.x + g'.b * read g B g'.y
    rw [read_shiftW μ f g _ B hl (fun j => hμ j B hB.le),
      read_shiftW μ f g _ B hl (fun j => hμ j B hB.le)]

/-! #### Combinators on programs -/

namespace SLP

variable {I' O' O₁ O₂ : Type*}

theorem size_def (P : SLP R I O) : P.size = P.gates.length := rfl

theorem constsIn_map {C : Set R} (W : Wire J → Wire I) {gs : List (Gate R J)}
    (h : ∀ g ∈ gs, g.a ∈ C ∧ g.b ∈ C) : ∀ g ∈ gs.map (Gate.mapW W), g.a ∈ C ∧ g.b ∈ C := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
  exact h g' hg'

/-- Relabelled inputs and outputs. -/
def reindex (P : SLP R I O) (d : I → I') (e : O' → O) : SLP R I' O' where
  gates := P.gates.map (Gate.mapW (shiftW (fun i => Sum.inl (d i)) 0))
  out o := shiftW (fun i => Sum.inl (d i)) 0 (P.out (e o))

theorem size_reindex (P : SLP R I O) (d : I → I') (e : O' → O) :
    (P.reindex d e).size = P.size := by
  simp [reindex, size_def]

theorem constsIn_reindex {C : Set R} (P : SLP R I O) (d : I → I') (e : O' → O)
    (h : P.ConstsIn C) : (P.reindex d e).ConstsIn C :=
  constsIn_map _ h

theorem run_reindex (P : SLP R I O) (d : I → I') (e : O' → O) (f : I' → R) :
    run (P.reindex d e).gates f = run P.gates (fun i => f (d i)) := by
  have := run_append_mapW ([] : List (Gate R I')) P.gates (fun i => Sum.inl (d i)) f
    (fun i => f (d i)) (fun _ _ _ => rfl)
  simp only [List.nil_append, List.length_nil, run_nil] at this
  exact this

theorem eval_reindex (P : SLP R I O) (d : I → I') (e : O' → O) :
    (P.reindex d e).eval = fun f o => P.eval (fun i => f (d i)) (e o) := by
  funext f o
  show read f (run (P.reindex d e).gates f) (shiftW _ 0 (P.out (e o))) = _
  rw [run_reindex]
  exact read_shiftW (fun i => Sum.inl (d i)) f (fun i => f (d i)) [] _ rfl (fun _ => rfl)
    (P.out (e o))

/-- Sequential composition: `P₂` runs on the outputs of `P₁`. -/
def comp (P₁ : SLP R I J) (P₂ : SLP R J O) : SLP R I O where
  gates := P₁.gates ++ P₂.gates.map (Gate.mapW (shiftW
    (fun j => normW P₁.gates.length (P₁.gates.length + P₂.gates.length) (P₁.out j))
    P₁.gates.length))
  out o := shiftW (fun j => normW P₁.gates.length (P₁.gates.length + P₂.gates.length) (P₁.out j))
    P₁.gates.length (P₂.out o)

theorem size_comp (P₁ : SLP R I J) (P₂ : SLP R J O) : (P₁.comp P₂).size = P₁.size + P₂.size := by
  simp [comp, size_def]

theorem constsIn_comp {C : Set R} (P₁ : SLP R I J) (P₂ : SLP R J O) (h₁ : P₁.ConstsIn C)
    (h₂ : P₂.ConstsIn C) : (P₁.comp P₂).ConstsIn C := by
  intro g hg
  rcases List.mem_append.1 hg with hg | hg
  · exact h₁ g hg
  · exact constsIn_map _ h₂ g hg

theorem eval_comp (P₁ : SLP R I J) (P₂ : SLP R J O) (f : I → R) :
    (P₁.comp P₂).eval f = P₂.eval (P₁.eval f) := by
  funext o
  have hl : (run P₁.gates f).length = P₁.gates.length := length_run _ _
  have hμ : ∀ j (B : List R), B.length ≤ P₂.gates.length →
      read f (run P₁.gates f ++ B)
        (normW P₁.gates.length (P₁.gates.length + P₂.gates.length) (P₁.out j)) = P₁.eval f j := by
    intro j B hB
    exact read_normW f _ B hl (by simp only [List.length_append, hl]; omega) (P₁.out j)
  show read f (run (P₁.comp P₂).gates f) (shiftW _ P₁.gates.length (P₂.out o)) = _
  have hrun : run (P₁.comp P₂).gates f = run P₁.gates f ++ run P₂.gates (P₁.eval f) :=
    run_append_mapW P₁.gates P₂.gates _ f (P₁.eval f) hμ
  rw [hrun]
  exact read_shiftW _ f (P₁.eval f) _ _ hl (fun j => hμ j _ (by simp)) (P₂.out o)

/-- Two programs on the same input, outputs side by side. -/
def sumElim (P₁ : SLP R I O₁) (P₂ : SLP R I O₂) : SLP R I (O₁ ⊕ O₂) where
  gates := P₁.gates ++ P₂.gates.map (Gate.mapW (shiftW Sum.inl P₁.gates.length))
  out := Sum.elim (fun o => normW P₁.gates.length (P₁.gates.length + P₂.gates.length) (P₁.out o))
    (fun o => shiftW Sum.inl P₁.gates.length (P₂.out o))

theorem size_sumElim (P₁ : SLP R I O₁) (P₂ : SLP R I O₂) :
    (P₁.sumElim P₂).size = P₁.size + P₂.size := by
  simp [sumElim, size_def]

theorem constsIn_sumElim {C : Set R} (P₁ : SLP R I O₁) (P₂ : SLP R I O₂) (h₁ : P₁.ConstsIn C)
    (h₂ : P₂.ConstsIn C) : (P₁.sumElim P₂).ConstsIn C := by
  intro g hg
  rcases List.mem_append.1 hg with hg | hg
  · exact h₁ g hg
  · exact constsIn_map _ h₂ g hg

theorem eval_sumElim (P₁ : SLP R I O₁) (P₂ : SLP R I O₂) (f : I → R) :
    (P₁.sumElim P₂).eval f = Sum.elim (P₁.eval f) (P₂.eval f) := by
  funext o
  have hl : (run P₁.gates f).length = P₁.gates.length := length_run _ _
  have hrun : run (P₁.sumElim P₂).gates f = run P₁.gates f ++ run P₂.gates f :=
    run_append_mapW P₁.gates P₂.gates Sum.inl f f (fun _ _ _ => rfl)
  rcases o with o | o
  · show read f (run (P₁.sumElim P₂).gates f) (normW _ _ (P₁.out o)) = _
    rw [hrun]
    exact read_normW f _ _ hl (by simp) (P₁.out o)
  · show read f (run (P₁.sumElim P₂).gates f) (shiftW Sum.inl _ (P₂.out o)) = _
    rw [hrun]
    exact read_shiftW Sum.inl f f _ _ hl (fun _ => rfl) (P₂.out o)

/-- One gate `a_o f(x_o) + b_o f(y_o)` per output `o`, reading only inputs. -/
noncomputable def inputGates [Fintype O] (a b : O → R) (x y : O → I) : SLP R I O where
  gates := List.ofFn fun k : Fin (Fintype.card O) =>
    (⟨a ((Fintype.equivFin O).symm k), Sum.inl (x ((Fintype.equivFin O).symm k)),
      b ((Fintype.equivFin O).symm k), Sum.inl (y ((Fintype.equivFin O).symm k))⟩ : Gate R I)
  out o := Sum.inr (Fintype.equivFin O o)

theorem size_inputGates [Fintype O] (a b : O → R) (x y : O → I) :
    (inputGates a b x y).size = Fintype.card O := by
  simp [inputGates, size_def]

theorem constsIn_inputGates {C : Set R} [Fintype O] (a b : O → R) (x y : O → I)
    (ha : ∀ o, a o ∈ C) (hb : ∀ o, b o ∈ C) : (inputGates a b x y).ConstsIn C := by
  intro g hg
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hg
  exact ⟨ha _, hb _⟩

theorem eval_inputGates [Fintype O] (a b : O → R) (x y : O → I) :
    (inputGates a b x y).eval = fun f o => a o * f (x o) + b o * f (y o) := by
  funext f o
  have hrun : run (inputGates a b x y).gates f =
      (inputGates a b x y).gates.map (fun g => g.eval f []) := by
    rw [run_eq_evalFold, evalFold_const _ (fun g => g.eval f []) _ ?_ [], List.nil_append]
    intro g hg vs
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hg
    rfl
  show read f (run (inputGates a b x y).gates f) (Sum.inr (Fintype.equivFin O o)) = _
  rw [hrun, read_inr, List.getD_eq_getElem _ _ (by simp [inputGates])]
  simp [inputGates, Gate.eval]

end SLP

/-! #### Coefficient rows: every program computes a linear map -/

section Rows

variable [DecidableEq I]

/-- The coefficient row of a wire, given the rows of the gates computed so far. -/
def rowRead (rs : List (I → R)) : Wire I → I → R
  | .inl i => Pi.single i 1
  | .inr j => rs.getD j 0

/-- The coefficient row of a gate. -/
def Gate.row (g : Gate R I) (rs : List (I → R)) : I → R :=
  g.a • rowRead rs g.x + g.b • rowRead rs g.y

/-- The coefficient rows of all gates, in order. -/
def rows (gs : List (Gate R I)) : List (I → R) := evalFold (fun g rs => g.row rs) gs []

variable [Fintype I]

theorem read_map_rows (rs : List (I → R)) (f : I → R) (w : Wire I) :
    read f (rs.map fun r => ∑ i, r i * f i) w = ∑ i, rowRead rs w i * f i := by
  rcases w with i | j
  · simp [rowRead, Pi.single_apply]
  · simp only [read_inr, rowRead]
    by_cases hj : j < rs.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj,
        List.getElem_map]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
      simp

theorem run_eq_map_rows (gs : List (Gate R I)) (f : I → R) :
    run gs f = (rows gs).map fun r => ∑ i, r i * f i := by
  have key := evalFold_hom (fun g rs => g.row rs) (fun g vals => g.eval f vals)
    (fun r : I → R => ∑ i, r i * f i) ?_ gs []
  · simp only [List.map_nil] at key
    exact key
  · intro g rs
    simp only [Gate.eval, read_map_rows, Gate.row, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem SLP.eval_eq_sum_rows (P : SLP R I O) (f : I → R) (o : O) :
    P.eval f o = ∑ i, rowRead (rows P.gates) (P.out o) i * f i := by
  simp only [SLP.eval, run_eq_map_rows, read_map_rows]

end Rows

end Linear

end SubspaceConvolution.Circuit
