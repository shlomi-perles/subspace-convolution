/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.Counter.WidthSetup

/-!
# Lemma 6, part 2: the remaining edges — neighborhoods and the initial cuts

After removing the register edges, the edges inside test cliques and the private edges, the
remaining rows of a cut matrix take only few distinct values ("future neighborhoods").  Here we
define these neighborhoods and treat the initial cuts:

* *Case A* — the cut lies in the register: only one row clique is split (rank `≤ 1`);
* *Case B* — the cut lies in `B_*`: the processed vertices of `B_*` have one common future
  neighborhood (rank `≤ 1`).

The cuts in the constraint part (Case C, rank `≤ 10`) are treated in `WidthRestC.lean`.
-/

open Finset Matrix

set_option linter.unusedSectionVars false

namespace SubspaceConvolution.Counter

variable {I : MinCSP}

/-! ## Future neighborhoods in the remaining graph -/

/-- All old vertices except `B_*` and the rows: `D`, the `A`-vertices and the `I`-vertices. -/
def PAll : Vtx I → Prop
  | .sel _ => True
  | .anc _ => True
  | .aV _ _ _ j _ => (j : ℕ) = 0
  | .iV _ => True
  | _ => False

/-- The vertices of `D`. -/
def PD : Vtx I → Prop
  | .sel _ => True
  | .anc _ => True
  | _ => False

/-- The neighborhood of the current selector `s_C`: `D`, the `A`-vertices and the `I`-vertices
outside `I_C`. -/
def PSel (C : Fin I.p) : Vtx I → Prop
  | .sel _ => True
  | .anc _ => True
  | .aV _ _ _ j _ => (j : ℕ) = 0
  | .iV b => b.C ≠ C
  | _ => False

/-- The neighborhood of `A_{C,x}`: `D` outside `M_{C,x}`, and `I_{C,x}`. -/
def PA (C : Fin I.p) (x : Fin I.k) : Vtx I → Prop
  | .sel _ => True
  | .anc b => ¬ (b.C = C ∧ b.x = x)
  | .iV b => b.C = C ∧ b.x = x
  | _ => False

/-- The neighborhood of the vertices of the current mini-constraint `R` of `C`: `D` and
`I_C \ I_{C,R}`. -/
def PI (C : Fin I.p) (R : ℕ) : Vtx I → Prop
  | .sel _ => True
  | .anc _ => True
  | .iV b => b.C = C ∧ (b.R : ℕ) ≠ R
  | _ => False

/-- The neighborhood of the vertices of the finished mini-constraints of `C`: `D` and `I_C`. -/
def PI' (C : Fin I.p) : Vtx I → Prop
  | .sel _ => True
  | .anc _ => True
  | .iV b => b.C = C
  | _ => False

/-- The neighborhood of an anchor `m_b` whose `b` is in the future: everything old except `b`. -/
def PAnc (b : IIdx I) : Vtx I → Prop
  | .sel _ => True
  | .anc _ => True
  | .aV _ _ _ j _ => (j : ℕ) = 0
  | .iV b' => b' ≠ b
  | _ => False

/-- The row `B_i`. -/
def PRow (i : Fin (d I)) : Vtx I → Prop
  | .row i' _ _ => i' = i
  | _ => False

/-- The neighborhood of `B_*`: `B_*` and all old vertices except the rows. -/
def PStar : Vtx I → Prop
  | .star _ => True
  | .sel _ => True
  | .anc _ => True
  | .aV _ _ _ j _ => (j : ℕ) = 0
  | .iV _ => True
  | _ => False

instance : DecidablePred (PAll (I := I)) := fun v => by cases v <;> unfold PAll <;> infer_instance
instance : DecidablePred (PD (I := I)) := fun v => by cases v <;> unfold PD <;> infer_instance
instance (C : Fin I.p) : DecidablePred (PSel C) := fun v => by
  cases v <;> unfold PSel <;> infer_instance
instance (C : Fin I.p) (x : Fin I.k) : DecidablePred (PA C x) := fun v => by
  cases v <;> unfold PA <;> infer_instance
instance (C : Fin I.p) (R : ℕ) : DecidablePred (PI C R) := fun v => by
  cases v <;> unfold PI <;> infer_instance
instance (C : Fin I.p) : DecidablePred (PI' C) := fun v => by
  cases v <;> unfold PI' <;> infer_instance
instance (b : IIdx I) : DecidablePred (PAnc b) := fun v => by
  cases v <;> unfold PAnc <;> infer_instance
instance (i : Fin (d I)) : DecidablePred (PRow i) := fun v => by
  cases v <;> unfold PRow <;> infer_instance
instance : DecidablePred (PStar (I := I)) := fun v => by
  cases v <;> unfold PStar <;> infer_instance

/-! ## Rows of the remaining graph that vanish -/

theorem rest_aV_eq_zero {X : Finset (Vtx I)} {C : Fin I.p} {x : Fin I.k} {hx : x ∈ I.scope C}
    {j : Fin (d I)} {t : Fin I.n} (hj : (j : ℕ) ≠ 0) :
    cutRow (Mpart I .rest) X (.aV C x hx j t) = 0 := by
  apply cutRow_Mpart_eq_zero
  intro y _ ⟨hadj, hc⟩
  cases y <;> simp_all [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge]

theorem rest_eV_eq_zero {X : Finset (Vtx I)} {C : Fin I.p} {x : Fin I.k} {hx : x ∈ I.scope C}
    {t : Fin (eta I - I.n)} : cutRow (Mpart I .rest) X (.eV C x hx t) = 0 := by
  apply cutRow_Mpart_eq_zero
  intro y _ ⟨_, hc⟩
  simp [ecls, Vtx.isEV] at hc

/-- The remaining row of a register vertex: the future part of its row clique. -/
theorem rest_row_eq {X : Finset (Vtx I)} {i : Fin (d I)} {A : Mat I} {t : Fin I.n}
    (hv : Vtx.row i A t ∈ X) : cutRow (Mpart I .rest) X (.row i A t) = nbVec X (PRow i) := by
  apply cutRow_Mpart_eq
  intro y hy
  have hne : Vtx.row i A t ≠ y := fun h => hy (h ▸ hv)
  cases y <;> simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PRow, hne, eq_comm]

/-! ## Case A: cuts inside the register -/

/-- The row containing a register vertex. -/
def rowId : Vtx I → Option (Fin (d I))
  | .row i _ _ => some i
  | _ => none

/-- The split rows. -/
def splitRow (X : Finset (Vtx I)) : Finset (Fin (d I)) :=
  univ.filter fun i => (∃ v ∈ X, rowId v = some i) ∧ (∃ w ∉ X, rowId w = some i)

theorem card_splitRow_le {X : Finset (Vtx I)} (hX : IsCut X) : (splitRow X).card ≤ 1 := by
  rw [card_le_one]
  intro i hi i' hi'
  simp only [splitRow, mem_filter, mem_univ, true_and] at hi hi'
  obtain ⟨⟨v, hv, hvc⟩, ⟨w, hw, hwc⟩⟩ := hi
  obtain ⟨⟨v', hv', hvc'⟩, ⟨w', hw', hwc'⟩⟩ := hi'
  have h1 := hX v' hv' w hw
  have h2 := hX v hv w' hw'
  cases v <;> simp only [rowId, reduceCtorEq, Option.some.injEq] at hvc
  cases w <;> simp only [rowId, reduceCtorEq, Option.some.injEq] at hwc
  cases v' <;> simp only [rowId, reduceCtorEq, Option.some.injEq] at hvc'
  cases w' <;> simp only [rowId, reduceCtorEq, Option.some.injEq] at hwc'
  subst hvc hwc hvc' hwc'
  simp only [key, List.cons_lt_cons_iff, lt_self_iff_false, true_and, false_or, not_or,
    not_and, not_lt] at h1 h2
  exact Fin.ext (by omega)

theorem matCutRank_Mrest_le_caseA {X : Finset (Vtx I)} (hX : IsCut X)
    (hA : ∀ v ∈ X, v.isRow = true) : matCutRank (Mpart I .rest) X ≤ 1 := by
  refine (matCutRank_le_card_of_mem_or_zero ((splitRow X).image fun i =>
    nbVec X (PRow i)) fun v hv => ?_).trans (card_image_le.trans (card_splitRow_le hX))
  have hrow := hA v hv
  cases v <;> simp only [Vtx.isRow, Bool.false_eq_true] at hrow
  rename_i i A t
  rw [rest_row_eq hv]
  by_cases hsplit : ∃ w ∉ X, rowId w = some i
  · right
    exact mem_image_of_mem _ (by simp [splitRow]; exact ⟨⟨_, hv, rfl⟩, hsplit⟩)
  · left
    apply nbVec_eq_zero
    intro y hy h
    cases y <;> simp only [PRow] at h
    exact hsplit ⟨_, hy, by simp [rowId, h]⟩

/-! ## Case B: cuts inside `B_*` -/

theorem matCutRank_Mrest_le_caseB {X : Finset (Vtx I)} (hX : IsCut X) {v₀ : Vtx I}
    (hv₀ : v₀ ∈ X) (hv₀r : v₀.isRow = false) (hB : ∀ C, Vtx.sel C ∉ X) :
    matCutRank (Mpart I .rest) X ≤ 1 := by
  have hrows : ∀ i A t, Vtx.row i A t ∈ X := fun i A t => hX.mem_of_lt hv₀ (key_row_lt hv₀r)
  refine (matCutRank_le_card_of_mem_or_zero {nbVec X PStar} fun v hv => ?_).trans
    (card_singleton _).le
  cases v with
  | row i A t =>
    left
    rw [rest_row_eq hv]
    apply nbVec_eq_zero
    intro y hy h
    cases y <;> simp only [PRow] at h
    exact hy (hrows _ _ _)
  | star t =>
    right
    rw [mem_singleton]
    apply cutRow_Mpart_eq
    intro y hy
    have hne : Vtx.star t ≠ y := fun h => hy (h ▸ hv)
    cases y <;> simp [ecls, Vtx.isEV, Vtx.isRow, Vtx.isAV, adj_iff, edge, PStar, hne]
  | sel C => exact absurd hv (hB C)
  | anc b =>
    exact absurd (hX.mem_of_lt hv (w := .sel b.C) (by simp [key, List.cons_lt_cons_iff]))
      (hB b.C)
  | aV C x hx j t =>
    exact absurd (hX.mem_of_lt hv (w := .sel C) (by simp [key, List.cons_lt_cons_iff])) (hB C)
  | iV b =>
    exact absurd (hX.mem_of_lt hv (w := .sel b.C) (by simp [key, List.cons_lt_cons_iff]))
      (hB b.C)
  | eV C x hx t =>
    exact absurd (hX.mem_of_lt hv (w := .sel C) (by simp [key, List.cons_lt_cons_iff])) (hB C)

end SubspaceConvolution.Counter
