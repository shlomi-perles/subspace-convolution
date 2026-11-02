/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.Counter.Lemmas

/-!
# Lemma C.3, second direction: a satisfying assignment gives an `η`-coloring

Given a satisfying assignment `α`:

* increase it (on the padded variables, i.e. on all matrices) to a family `β A ≤ n` of cost
  exactly `W` (`exists_fill`);
* the colors are the selectors `Fin p`, the anchors `IIdx I` and the register *slots*
  `(A, t) ∈ F₂^{d×d} × Fin n`; there are exactly `η` of them.  The slot `(A, t)` is a color of
  type `A`; it is *active* if `t < β A` and *garbage* otherwise.  The register vertex
  `row i A t` (of label `(e_i, A i)`) gets the slot `(A, t)`, so each slot of type `A` sits on
  the label `(e_i, Aᵀ e_i)` in every row, and each label receives at most `Q/h` colors;
  `B_*` gets distinct garbage slots;
* choose a satisfied mini-constraint `R_C` for each `C`; color `I_{C,R_C}` with the selector
  color and every other `I`-vertex `b` with its anchor color; color `A_{C,x}` (and all its test
  copies `A^{(j)}_{C,x}`) with `c_{R_C,x}` active colors of type `enc x` and the
  `n - c_{R_C,x}` anchor colors of `I_{C,R_C,x}`; color `E_{C,x}` with the remaining colors.
-/

open Finset

set_option linter.unusedSectionVars false

namespace SubspaceConvolution.Counter

variable {I : MinCSP}

/-- Increasing a family of values in `{0, …, n}` to a prescribed total `W ≤ |ι| n`. -/
theorem exists_fill {ι : Type*} [Fintype ι] [DecidableEq ι] (n W : ℕ) (f₀ : ι → ℕ)
    (hf₀ : ∀ i, f₀ i ≤ n) (hsum : ∑ i, f₀ i ≤ W) (hW : W ≤ Fintype.card ι * n) :
    ∃ f : ι → ℕ, (∀ i, f₀ i ≤ f i) ∧ (∀ i, f i ≤ n) ∧ ∑ i, f i = W := by
  obtain ⟨m, hm⟩ : ∃ m, W - ∑ i, f₀ i = m := ⟨_, rfl⟩
  induction m generalizing f₀ with
  | zero => exact ⟨f₀, fun _ => le_rfl, hf₀, by omega⟩
  | succ m ih =>
    obtain ⟨i₀, hi₀⟩ : ∃ i, f₀ i < n := by
      by_contra hcon
      push Not at hcon
      have : Fintype.card ι * n ≤ ∑ i, f₀ i := by
        calc Fintype.card ι * n = ∑ _i : ι, n := by simp
          _ ≤ ∑ i, f₀ i := sum_le_sum fun i _ => hcon i
      omega
    set f₁ : ι → ℕ := fun i => f₀ i + if i = i₀ then 1 else 0 with hf₁
    have hs : ∑ i, f₁ i = ∑ i, f₀ i + 1 := by
      simp only [hf₁, sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
    obtain ⟨f, hf1, hf2, hf3⟩ := ih f₁ (fun i => by
      simp only [hf₁]
      split_ifs with h
      · subst h; omega
      · simpa using hf₀ i) (by omega) (by omega)
    exact ⟨f, fun i => (Nat.le_add_right _ _).trans (hf1 i), hf2, hf3⟩

namespace Backward

/-- The colors: the selectors `Fin p`, the anchors `IIdx I`, and the register slots. -/
abbrev Col (I : MinCSP) : Type := Fin I.p ⊕ IIdx I ⊕ (Mat I × Fin I.n)

theorem card_Col : Fintype.card (Col I) = eta I := by
  simp only [Col, Fintype.card_sum, Fintype.card_fin, card_IIdx, Fintype.card_prod, card_Mat,
    eta, Q]
  ring

/-- The colors of `A_{C,x}` (and of all test copies `A^{(j)}_{C,x}`): the first `c_{R_C,x}`
vertices get the active slots `(enc x, t)`, the others the anchor colors of `I_{C,R_C,x}`. -/
def colA (R : (C : Fin I.p) → Fin (I.numMini C)) (C : Fin I.p) (x : Fin I.k)
    (hx : x ∈ I.scope C) (t : Fin I.n) : Col I :=
  if h : (t : ℕ) < I.thr C (R C) x then .inr (.inr (enc I x, t))
  else .inr (.inl ⟨C, R C, x, hx, ⟨t - I.thr C (R C) x, by have := t.isLt; omega⟩⟩)

/-- The data determining the coloring. -/
structure Data (I : MinCSP) where
  /-- the active color counts -/
  β : Mat I → ℕ
  /-- the chosen mini-constraints -/
  R : (C : Fin I.p) → Fin (I.numMini C)
  /-- the garbage slots used on `B_*` -/
  gar : Fin (Q I - I.W) → Mat I × Fin I.n
  /-- the colors of `E_{C,x}` -/
  eCol : (C : Fin I.p) → (x : Fin I.k) → x ∈ I.scope C → Fin (eta I - I.n) → Col I

/-- The coloring. -/
def col (D : Data I) : Vtx I → Col I
  | .row _ A t => .inr (.inr (A, t))
  | .star t => .inr (.inr (D.gar t))
  | .sel C => .inl C
  | .anc b => .inr (.inl b)
  | .aV C x hx _ t => colA D.R C x hx t
  | .iV b => if b.R = D.R b.C then .inl b.C else .inr (.inl b)
  | .eV C x hx t => D.eCol C x hx t

/-- The conditions on the data making `col D` proper. -/
structure Data.Valid (D : Data I) : Prop where
  gar_inj : Function.Injective D.gar
  gar_garbage : ∀ t, D.β (D.gar t).1 ≤ (D.gar t).2
  thr_le : ∀ C, ∀ x ∈ I.scope C, I.thr C (D.R C) x ≤ D.β (enc I x)
  eCol_inj : ∀ C x hx, Function.Injective (D.eCol C x hx)
  eCol_avoid : ∀ C x hx t s, D.eCol C x hx t ≠ colA D.R C x hx s

theorem colA_injective (R : (C : Fin I.p) → Fin (I.numMini C)) (C : Fin I.p) (x : Fin I.k)
    (hx : x ∈ I.scope C) : Function.Injective (colA R C x hx) := by
  intro t t' h
  unfold colA at h
  split_ifs at h with h1 h2 h2
  · simp only [Sum.inr.injEq, Prod.mk.injEq] at h
    exact h.2
  · simp at h
  · simp at h
  · simp only [Sum.inr.injEq, Sum.inl.injEq, IIdx.mk.injEq, heq_eq_eq, true_and, Fin.mk.injEq]
      at h
    exact Fin.ext (by omega)

theorem colA_ne_inl (R : (C : Fin I.p) → Fin (I.numMini C)) (C : Fin I.p) (x : Fin I.k)
    (hx : x ∈ I.scope C) (t : Fin I.n) (C' : Fin I.p) : colA R C x hx t ≠ .inl C' := by
  unfold colA
  split_ifs <;> simp

theorem colA_eq_slot {R : (C : Fin I.p) → Fin (I.numMini C)} {C : Fin I.p} {x : Fin I.k}
    {hx : x ∈ I.scope C} {t : Fin I.n} {q : Mat I × Fin I.n}
    (h : colA R C x hx t = .inr (.inr q)) : q = (enc I x, t) ∧ (t : ℕ) < I.thr C (R C) x := by
  unfold colA at h
  split_ifs at h with h1
  · simp only [Sum.inr.injEq] at h
    exact ⟨h.symm, h1⟩
  · simp at h

theorem colA_eq_anc {R : (C : Fin I.p) → Fin (I.numMini C)} {C : Fin I.p} {x : Fin I.k}
    {hx : x ∈ I.scope C} {t : Fin I.n} {b : IIdx I}
    (h : colA R C x hx t = .inr (.inl b)) : ∃ s, b = ⟨C, R C, x, hx, s⟩ := by
  unfold colA at h
  split_ifs at h with h1
  · simp at h
  · simp only [Sum.inr.injEq, Sum.inl.injEq] at h
    exact ⟨_, h.symm⟩

theorem col_ne_of_edge {D : Data I} (hD : D.Valid) {v w : Vtx I} (hne : v ≠ w)
    (he : edge I v w) : col D v ≠ col D w := by
  cases v <;> cases w <;> simp only [edge] at he
  all_goals simp only [col, ne_eq]
  case row.row i A t i' A' t' =>
    intro h
    simp only [Sum.inr.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hne (by rw [he])
  case star.star t t' =>
    intro h
    simp only [Sum.inr.injEq] at h
    exact hne (by rw [hD.gar_inj h])
  case star.aV s C x hx j t =>
    intro h
    obtain ⟨h1, h2⟩ := colA_eq_slot h.symm
    have h3 := hD.gar_garbage s
    rw [h1] at h3
    have h4 := hD.thr_le C x hx
    simp only at h3
    omega
  case star.iV => split_ifs <;> simp
  case sel.row => simp
  case sel.star => simp
  case sel.sel => simpa using hne
  case sel.anc => simp
  case sel.aV C' C x hx j t => exact fun h => colA_ne_inl _ _ _ _ _ _ h.symm
  case sel.iV C b =>
    split_ifs
    · simpa [eq_comm] using he
    · simp
  case anc.row => simp
  case anc.star => simp
  case anc.anc => simpa using hne
  case anc.aV b C x hx j t =>
    intro h
    obtain ⟨s, rfl⟩ := colA_eq_anc h.symm
    exact he.2 ⟨rfl, rfl⟩
  case anc.iV b b' =>
    split_ifs
    · simp
    · simpa [eq_comm] using he
  case aV.row C x hx j t i A s =>
    rw [regLabel_dotProduct_testVec, F2_add_eq_one_iff] at he
    intro h
    obtain ⟨h1, -⟩ := colA_eq_slot h
    simp only [Prod.mk.injEq] at h1
    exact he (by rw [h1.1])
  case aV.aV C x hx j t C' x' hx' j' t' =>
    obtain ⟨rfl, rfl, rfl⟩ := he
    intro h
    have := colA_injective D.R C x hx h
    exact hne (by rw [this])
  case iV.row => split_ifs <;> simp
  case iV.aV b C x hx j t =>
    split_ifs with hR
    · exact fun h => colA_ne_inl _ _ _ _ _ _ h.symm
    · intro h
      obtain ⟨s, rfl⟩ := colA_eq_anc h.symm
      exact hR rfl
  case iV.iV b b' =>
    split_ifs with h1 h2 h2
    · intro _
      apply he.2
      rw [h1, h2]
      exact congrArg (fun C => ((D.R C : Fin _) : ℕ)) he.1
    · simp
    · simp
    · intro h
      simp only [Sum.inr.injEq, Sum.inl.injEq] at h
      exact he.2 (by rw [h])
  case eV.aV C x hx t C' x' hx' j s =>
    obtain ⟨rfl, rfl⟩ := he
    exact hD.eCol_avoid C x hx t s
  case eV.eV C x hx t C' x' hx' t' =>
    obtain ⟨rfl, rfl⟩ := he
    intro h
    exact hne (by rw [hD.eCol_inj C x hx h])

theorem col_valid {D : Data I} (hD : D.Valid) {v w : Vtx I} (hvw : (graph I).Adj v w) :
    col D v ≠ col D w := by
  rcases adj_iff.1 hvw with ⟨hne, he | he⟩
  · exact col_ne_of_edge hD hne he
  · exact (col_ne_of_edge hD (Ne.symm hne) he).symm

/-- The data exist: increase a satisfying assignment to cost exactly `W`, choose satisfied
mini-constraints, garbage slots for `B_*`, and the remaining colors for the private cliques. -/
theorem exists_data (hI : I.Normalized) (hsat : I.Satisfiable) : ∃ D : Data I, D.Valid := by
  classical
  obtain ⟨α, hα_le, hα_sum, hα_C⟩ := hsat
  choose R hR using hα_C
  -- the padded assignment, increased to cost exactly `W`
  set f₀ : Mat I → ℕ := Function.extend (enc I) α 0 with hf₀
  have hf₀_enc : ∀ x, f₀ (enc I x) = α x := fun x => (enc I).injective.extend_apply α 0 x
  have hf₀_out : ∀ A, (¬ ∃ x, enc I x = A) → f₀ A = 0 := fun A hA => by
    rw [hf₀, Function.extend_apply' _ _ _ hA]
    rfl
  have hf₀_le : ∀ A, f₀ A ≤ I.n := by
    intro A
    by_cases hA : ∃ x, enc I x = A
    · obtain ⟨x, rfl⟩ := hA
      rw [hf₀_enc]
      exact hα_le x
    · rw [hf₀_out A hA]
      exact Nat.zero_le _
  have hf₀_sum : ∑ A, f₀ A = ∑ x, α x := by
    rw [← sum_subset (subset_univ (univ.map (enc I))) (fun A _ hA => hf₀_out A (by simpa using hA)),
      sum_map]
    exact sum_congr rfl fun x _ => hf₀_enc x
  obtain ⟨β, hβ₀, hβn, hβW⟩ := exists_fill I.n I.W f₀ hf₀_le (hf₀_sum ▸ hα_sum)
    (by rw [card_Mat]; exact W_le_Q hI)
  -- the garbage slots
  have hcardG : Fintype.card (Σ A : Mat I, Fin (I.n - β A)) = Q I - I.W := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [sum_tsub_distrib _ (fun A _ => hβn A), hβW, sum_const, card_univ, card_Mat, smul_eq_mul, Q]
  set e := (Fintype.equivFinOfCardEq hcardG).symm with he
  let gar : Fin (Q I - I.W) → Mat I × Fin I.n := fun t =>
    ((e t).1, ⟨β (e t).1 + (e t).2, by have := (e t).2.isLt; omega⟩)
  -- the colors of the private cliques
  have hE : ∀ C x (hx : x ∈ I.scope C),
      Nonempty (Fin (eta I - I.n) ↪ {c : Col I // c ∉ univ.image (colA R C x hx)}) := by
    intro C x hx
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin, Fintype.card_subtype_compl, card_Col, Fintype.card_coe]
    have h1 : (univ.image (colA R C x hx)).card ≤ I.n :=
      card_image_le.trans (by simp)
    omega
  let eE := fun C x hx => Classical.choice (hE C x hx)
  refine ⟨⟨β, R, gar, fun C x hx t => (eE C x hx t).1⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro t t' h
    simp only [gar, Prod.mk.injEq, Fin.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    apply e.injective
    revert h1 h2
    generalize e t = u
    generalize e t' = u'
    intro h1 h2
    obtain ⟨A, s⟩ := u
    obtain ⟨A', s'⟩ := u'
    simp only at h1 h2
    subst h1
    have : s = s' := Fin.ext (by omega)
    rw [this]
  · intro t
    exact Nat.le_add_right _ _
  · intro C x hx
    exact (hR C x hx).trans ((hf₀_enc x).symm ▸ hβ₀ (enc I x))
  · intro C x hx
    exact Subtype.val_injective.comp (eE C x hx).injective
  · intro C x hx t s h
    exact (eE C x hx t).2 (mem_image.2 ⟨s, mem_univ _, h.symm⟩)

end Backward

open Backward in
/-- **Lemma C.3**, second direction: a satisfying assignment yields an `η`-coloring. -/
theorem colorable_of_satisfiable (hI : I.Normalized) (hsat : I.Satisfiable) :
    (graph I).Colorable (eta I) := by
  obtain ⟨D, hD⟩ := exists_data hI hsat
  have := (SimpleGraph.Coloring.mk (col D) (fun h => col_valid hD h)).colorable
  rwa [card_Col] at this

end SubspaceConvolution.Counter
