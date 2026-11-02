/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.FixedPalette.Split

/-!
# Core colorings come from assignments

For a grid assignment `α` and clause signals `σ`, `core φ α σ` is the core coloring in which every
group selects (colors `T = 0`) exactly the input carrying the assignment of `α` to its row or
column, and in which the literal pairs and clause pairs carry the corresponding truth values
(`T = 0` for true, `F_B = 2` for false).

The main lemma `exists_core` is the consistency argument of the paper ("Making the row assignments
agree"): a proper core coloring in which every group selects at least one input is of this form.
-/

namespace SubspaceConvolution.FixedPalette

variable {k : ℕ}

/-- The assignment selected in group `γ` by the grid assignment `α`: the column `h` of `α` for
the column group `colB h`, and the row of `α` for a row group. -/
def selAsg (φ : GridCNF k) (α : Fin k → Fin k → Bool) : Grp k φ.m → (Fin k → Bool)
  | .colB h => fun j => α j h
  | .rowA j => α j
  | .loc i t => α (φ.clause i t).row

/-- The core coloring determined by the grid assignment `α` and the clause signals `σ`. -/
def core (φ : GridCNF k) (α : Fin k → Fin k → Bool) (σ : Fin φ.m → Bool) : CoreCol k φ.m :=
  (fun γ p => if asg k p = selAsg φ α γ then 0 else γ.falseCol,
   fun i t b => if (φ.clause i t).eval α = b then 0 else 2,
   fun i b => if σ i = b then 0 else 2)

theorem row_eq_some {φ : GridCNF k} {γ : Grp k φ.m} {j : Fin k} (h : γ.row φ = some j) :
    ∀ α, selAsg φ α γ = α j ∧ γ.falseCol = 1 ∧ γ.forbCol = 2 := by
  cases γ with
  | colB hh => simp [Grp.row] at h
  | rowA j' =>
    simp only [Grp.row, Option.some.injEq] at h
    subst h
    intro α
    exact ⟨rfl, rfl, rfl⟩
  | loc i t =>
    simp only [Grp.row, Option.some.injEq] at h
    subst h
    intro α
    exact ⟨rfl, rfl, rfl⟩

theorem fin3_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  fin_cases x <;> simp

theorem core_ok (φ : GridCNF k) (α : Fin k → Fin k → Bool) (σ : Fin φ.m → Bool) :
    CoreOK φ (core φ α σ) where
  inp_forb γ p := by
    cases γ <;> simp only [core, Grp.falseCol, Grp.forbCol] <;> split_ifs <;> decide
  ab hh q γ p j hj hne := by
    obtain ⟨hsel, hfalse, -⟩ := row_eq_some hj α
    show (if asg k q = selAsg φ α (.colB hh) then (0 : Fin 3) else 2) ≠
      (if asg k p = selAsg φ α γ then 0 else γ.falseCol)
    rw [hsel, hfalse]
    split_ifs with h1 h2 h2
    · exfalso
      apply hne
      have e1 := congrFun h1 j
      have e2 := congrFun h2 hh
      simp only [selAsg] at e1
      rw [e1, e2]
    all_goals decide
  lit_pal i t b := by
    simp only [core]
    split_ifs <;> decide
  lit_pair i t := by
    simp only [core]
    cases (φ.clause i t).eval α <;> decide
  lit_inp i t b p hne := by
    show (if (φ.clause i t).eval α = b then (0 : Fin 3) else 2) ≠
      (if asg k p = selAsg φ α (.loc i t) then 0 else (Grp.loc i t : Grp k φ.m).falseCol)
    split_ifs with h1 h2 h2
    · exfalso
      apply hne
      rw [show asg k p = α (φ.clause i t).row from h2, ← h1]
      rfl
    all_goals simp [Grp.falseCol]
  sig_pal i b := by
    simp only [core]
    split_ifs <;> decide
  sig_pair i := by
    simp only [core]
    cases σ i <;> decide

theorem core_injective (φ : GridCNF k) :
    Function.Injective fun x : (Fin k → Fin k → Bool) × (Fin φ.m → Bool) => core φ x.1 x.2 := by
  rintro ⟨α, σ⟩ ⟨α', σ'⟩ h
  simp only [core, Prod.mk.injEq] at h
  obtain ⟨hinp, -, hsig⟩ := h
  have hα : α = α' := by
    funext j
    have := congrFun (congrFun hinp (.rowA j)) ((asg k).symm (α j))
    simp only [Equiv.apply_symm_apply, selAsg, ↓reduceIte, Grp.falseCol] at this
    split_ifs at this with h'
    · exact h'
    · exact absurd this (by decide)
  have hσ : σ = σ' := by
    funext i
    have := congrFun (congrFun hsig i) true
    cases h1 : σ i <;> cases h2 : σ' i <;> simp_all
  rw [hα, hσ]

/-- **Consistency** (the paper's "Making the row assignments agree"): if every group selects at
least one input in a proper core coloring, the core coloring comes from an assignment. -/
theorem exists_core {φ : GridCNF k} {c : CoreCol k φ.m} (hc : CoreOK φ c)
    (hsel : ∀ γ, ∃ p, c.1 γ p = 0) : ∃ α σ, c = core φ α σ := by
  choose sel hsel using hsel
  set α : Fin k → Fin k → Bool := fun j h => asg k (sel (.colB h)) j with hαdef
  set σ : Fin φ.m → Bool := fun i => decide (c.2.2 i true = 0) with hσdef
  -- selected inputs of row groups carry the row of `α`
  have hA : ∀ γ j, γ.row φ = some j → ∀ p, c.1 γ p = 0 → asg k p = α j := by
    intro γ j hj p hp
    funext h
    by_contra hne
    exact hc.ab h (sel (.colB h)) γ p j hj (Ne.symm hne) (by rw [hsel, hp])
  have hA' : ∀ γ j, γ.row φ = some j → ∀ p, c.1 γ p = 0 ↔ asg k p = α j := by
    intro γ j hj p
    refine ⟨hA γ j hj p, fun hp => ?_⟩
    have h1 := hA γ j hj (sel γ) (hsel γ)
    have : sel γ = p := (asg k).injective (h1.trans hp.symm)
    rw [← this]
    exact hsel γ
  -- selected inputs of column groups carry the column of `α`
  have hB : ∀ h q, c.1 (.colB h) q = 0 ↔ asg k q = fun j => α j h := by
    intro h q
    constructor
    · intro hq
      funext j
      by_contra hne
      have hpj := hA (.rowA j) j rfl (sel (.rowA j)) (hsel _)
      refine hc.ab h q (.rowA j) (sel (.rowA j)) j rfl ?_ (by rw [hq, hsel])
      rw [hpj]
      exact hne
    · intro hq
      have : q = sel (.colB h) := (asg k).injective (by rw [hq])
      rw [this]
      exact hsel _
  refine ⟨α, σ, Prod.ext ?_ (Prod.ext ?_ ?_)⟩
  · funext γ p
    show c.1 γ p = if asg k p = selAsg φ α γ then 0 else γ.falseCol
    have hforb := hc.inp_forb γ p
    cases γ with
    | colB h =>
      show c.1 (.colB h) p = if asg k p = (fun j => α j h) then 0 else 2
      split_ifs with h1
      · exact (hB h p).2 h1
      · have h0 : c.1 (.colB h) p ≠ 0 := fun h0 => h1 ((hB h p).1 h0)
        rcases fin3_cases (c.1 (.colB h) p) with h' | h' | h'
        · exact absurd h' h0
        · exact absurd h' hforb
        · exact h'
    | rowA j =>
      show c.1 (.rowA j) p = if asg k p = α j then 0 else 1
      split_ifs with h1
      · exact (hA' (.rowA j) j rfl p).2 h1
      · have h0 : c.1 (.rowA j) p ≠ 0 := fun h0 => h1 ((hA' (.rowA j) j rfl p).1 h0)
        rcases fin3_cases (c.1 (.rowA j) p) with h' | h' | h'
        · exact absurd h' h0
        · exact h'
        · exact absurd h' hforb
    | loc i t =>
      show c.1 (.loc i t) p = if asg k p = α (φ.clause i t).row then 0 else 1
      split_ifs with h1
      · exact (hA' (.loc i t) _ rfl p).2 h1
      · have h0 : c.1 (.loc i t) p ≠ 0 := fun h0 => h1 ((hA' (.loc i t) _ rfl p).1 h0)
        rcases fin3_cases (c.1 (.loc i t) p) with h' | h' | h'
        · exact absurd h' h0
        · exact h'
        · exact absurd h' hforb
  · funext i t b
    show c.2.1 i t b = if (φ.clause i t).eval α = b then 0 else 2
    -- the selected input of the local group carries the row of `α`
    set p := sel (.loc i t) with hp
    have hp0 : c.1 (.loc i t) p = 0 := hsel _
    have hpα : asg k p = α (φ.clause i t).row := (hA' (.loc i t) _ rfl p).1 hp0
    have hval : (φ.clause i t).evalRow (asg k p) = (φ.clause i t).eval α := by
      rw [hpα]
      rfl
    have hlit : ∀ b', (φ.clause i t).eval α ≠ b' → c.2.1 i t b' = 2 := by
      intro b' hb'
      have h1 := hc.lit_inp i t b' p (by rw [hval]; exact hb')
      rw [hp0] at h1
      have h2 := hc.lit_pal i t b'
      rcases fin3_cases (c.2.1 i t b') with h' | h' | h'
      · exact absurd h' h1
      · exact absurd h' h2
      · exact h'
    split_ifs with hb
    · -- the other vertex of the pair has color `2`
      have h2 := hlit (!b) (by rw [hb]; cases b <;> decide)
      have hpair := hc.lit_pair i t
      have hpal := hc.lit_pal i t b
      have hne : c.2.1 i t b ≠ c.2.1 i t (!b) := by
        cases b
        · exact Ne.symm hpair
        · exact hpair
      rw [h2] at hne
      rcases fin3_cases (c.2.1 i t b) with h' | h' | h'
      · exact h'
      · exact absurd h' hpal
      · exact absurd h' hne
    · exact hlit b hb
  · funext i b
    show c.2.2 i b = if σ i = b then 0 else 2
    have h1 := hc.sig_pal i true
    have h2 := hc.sig_pal i false
    have h3 := hc.sig_pair i
    simp only [hσdef]
    rcases fin3_cases (c.2.2 i true) with h' | h' | h' <;>
      rcases fin3_cases (c.2.2 i false) with h'' | h'' | h'' <;>
      cases b <;> simp_all

end SubspaceConvolution.FixedPalette
