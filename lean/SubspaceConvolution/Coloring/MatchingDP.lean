/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.Basic

/-!
# Counting compatible partial matchings one left class at a time

This file isolates the purely combinatorial core of the merge step in Section 7
("Grouping partial colorings"), independently of graphs.

We have finitely many *left classes* `L` and *right classes* `R`, each carrying a profile
(`p : α → P₁`, `q : β → P₂`).  A compatible partial matching pairs some left classes with
distinct right classes, subject to a compatibility relation between their profiles.  Each
matching produces a *parent histogram*: the multiset of parent profiles of the paired classes,
the unpaired left classes and the unpaired right classes.

The paper computes the distribution of parent histograms by processing the left classes one at a
time, keeping only the histogram `b` of still available right classes and the histogram `H` of
parent classes already formed:

* leave the next left class (profile `U`) separate: `(b, H) ↦ (b, H + δ_{left U})`, weight `1`;
* pair it with an available compatible right class of profile `V`:
  `(b, H) ↦ (b - δ_V, H + δ_{pair U V})`, weight `b(V)`;

and finally adds the remaining right classes.  This is `MergeData.run`; multiplicities in the
returned multiset of parent histograms are the accumulated weights.  The main theorem
`MergeData.run_spec` says that `run` produces exactly the multiset of parent histograms of all
compatible partial matchings (paper: "Every partial matching has a unique sequence of these
choices").
-/

open Finset

set_option linter.unusedSectionVars false

namespace SubspaceConvolution

/-- The data of one merge step: compatibility of profiles, and the parent profiles of an unpaired
left class, an unpaired right class and a paired class. -/
structure MergeData (P₁ P₂ Q : Type*) where
  /-- a left class of profile `u` and a right class of profile `v` may share a color -/
  compat : P₁ → P₂ → Prop
  /-- the parent profile of an unpaired left class -/
  left : P₁ → Q
  /-- the parent profile of an unpaired right class -/
  right : P₂ → Q
  /-- the parent profile of a paired class -/
  pair : P₁ → P₂ → Q

namespace MergeData

variable {P₁ P₂ Q : Type*} (D : MergeData P₁ P₂ Q) [DecidableEq P₂] [DecidableRel D.compat]

/-- The merge recurrence of the paper (equations (hist-row) and (hist-weight)): process the
remaining left profiles `us`, with available right histogram `b` and formed parent histogram `H`.
The result is the multiset of final parent histograms, counted with the transition weights. -/
def run : List P₁ → Multiset P₂ → Multiset Q → Multiset (Multiset Q)
  | [], b, H => {H + b.map D.right}
  | u :: us, b, H =>
      run us b (D.left u ::ₘ H) +
        ∑ v ∈ b.toFinset.filter (D.compat u), b.count v • run us (b.erase v) (D.pair u v ::ₘ H)

@[simp] theorem run_nil (b : Multiset P₂) (H : Multiset Q) :
    D.run [] b H = {H + b.map D.right} := rfl

theorem run_cons (u : P₁) (us : List P₁) (b : Multiset P₂) (H : Multiset Q) :
    D.run (u :: us) b H = D.run us b (D.left u ::ₘ H) +
      ∑ v ∈ b.toFinset.filter (D.compat u), b.count v • D.run us (b.erase v) (D.pair u v ::ₘ H) :=
  rfl

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- `M` is a compatible partial matching between the left classes `L` and the right classes `R`:
a set of pairs, each left class and each right class in at most one pair, with compatible
profiles. -/
def IsMatching (p : α → P₁) (q : β → P₂) (L : Finset α) (R : Finset β)
    (M : Finset (α × β)) : Prop :=
  M ⊆ L ×ˢ R ∧ (∀ e ∈ M, ∀ e' ∈ M, e.1 = e'.1 → e = e') ∧
    (∀ e ∈ M, ∀ e' ∈ M, e.2 = e'.2 → e = e') ∧ ∀ e ∈ M, D.compat (p e.1) (q e.2)

open Classical in
/-- All compatible partial matchings between `L` and `R`. -/
noncomputable def matchings (p : α → P₁) (q : β → P₂) (L : Finset α) (R : Finset β) :
    Finset (Finset (α × β)) :=
  (L ×ˢ R).powerset.filter (D.IsMatching p q L R)

theorem mem_matchings {p : α → P₁} {q : β → P₂} {L : Finset α} {R : Finset β}
    {M : Finset (α × β)} : M ∈ D.matchings p q L R ↔ D.IsMatching p q L R M := by
  classical
  unfold matchings
  rw [mem_filter, mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- The parent histogram produced by the matching `M`. -/
def parentHist (p : α → P₁) (q : β → P₂) (L : Finset α) (R : Finset β)
    (M : Finset (α × β)) : Multiset Q :=
  M.val.map (fun e => D.pair (p e.1) (q e.2)) +
    (L.filter (· ∉ M.image Prod.fst)).val.map (fun a => D.left (p a)) +
    (R.filter (· ∉ M.image Prod.snd)).val.map (fun b => D.right (q b))

section Lemmas

variable {p : α → P₁} {q : β → P₂}

theorem matchings_empty_left (R : Finset β) :
    D.matchings p q ∅ R = {∅} := by
  ext M
  rw [mem_matchings, mem_singleton]
  constructor
  · rintro ⟨hM, -⟩
    simpa using hM
  · rintro rfl
    refine ⟨by simp, by simp, by simp, by simp⟩

/-- Matchings of `insert a L` in which `a` is unpaired are the matchings of `L`. -/
theorem filter_not_mem_fst {a : α} {L : Finset α} (ha : a ∉ L) (R : Finset β) :
    (D.matchings p q (insert a L) R).filter (fun M => a ∉ M.image Prod.fst) =
      D.matchings p q L R := by
  ext M
  rw [mem_filter, mem_matchings, mem_matchings]
  constructor
  · rintro ⟨⟨hsub, h1, h2, hc⟩, haM⟩
    refine ⟨fun e he => ?_, h1, h2, hc⟩
    have := hsub he
    rw [mem_product, mem_insert] at this
    rcases this with ⟨rfl | h, hr⟩
    · exact absurd (mem_image_of_mem Prod.fst he) haM
    · exact mem_product.2 ⟨h, hr⟩
  · rintro ⟨hsub, h1, h2, hc⟩
    refine ⟨⟨fun e he => ?_, h1, h2, hc⟩, ?_⟩
    · have := mem_product.1 (hsub he)
      exact mem_product.2 ⟨mem_insert_of_mem this.1, this.2⟩
    · intro h
      obtain ⟨e, he, rfl⟩ := mem_image.1 h
      exact ha (mem_product.1 (hsub he)).1

/-- Matchings of `insert a L` in which `a` is paired, grouped by the partner of `a`. -/
theorem filter_mem_fst {a : α} {L : Finset α} (ha : a ∉ L) (R : Finset β) :
    (D.matchings p q (insert a L) R).filter (fun M => a ∈ M.image Prod.fst) =
      (R.filter fun r => D.compat (p a) (q r)).biUnion
        fun r => (D.matchings p q L (R.erase r)).image (insert (a, r)) := by
  ext M
  rw [mem_filter, mem_matchings, mem_biUnion]
  constructor
  · rintro ⟨⟨hsub, h1, h2, hc⟩, haM⟩
    obtain ⟨⟨a', r⟩, hM, rfl⟩ := mem_image.1 haM
    dsimp only at hM ⊢
    have hr : r ∈ R := (mem_product.1 (hsub hM)).2
    refine ⟨r, mem_filter.2 ⟨hr, hc _ hM⟩, mem_image.2 ⟨M.erase (a', r), ?_, insert_erase hM⟩⟩
    rw [mem_matchings]
    refine ⟨fun e he => ?_, fun e he e' he' h => h1 e (mem_of_mem_erase he) e'
      (mem_of_mem_erase he') h, fun e he e' he' h => h2 e (mem_of_mem_erase he) e'
      (mem_of_mem_erase he') h, fun e he => hc e (mem_of_mem_erase he)⟩
    obtain ⟨hne, he⟩ := mem_erase.1 he
    obtain ⟨he1, he2⟩ := mem_product.1 (hsub he)
    refine mem_product.2 ⟨?_, mem_erase.2 ⟨fun h => hne (h2 e he _ hM h), he2⟩⟩
    rcases mem_insert.1 he1 with h | h
    · exact absurd (h1 e he _ hM h) hne
    · exact h
  · rintro ⟨r, hr, hM⟩
    obtain ⟨hrR, hcr⟩ := mem_filter.1 hr
    obtain ⟨M', hM', rfl⟩ := mem_image.1 hM
    obtain ⟨hsub, h1, h2, hc⟩ := (mem_matchings D).1 hM'
    have hfst : ∀ e ∈ M', e.1 ∈ L := fun e he => (mem_product.1 (hsub he)).1
    have hsnd : ∀ e ∈ M', e.2 ∈ R.erase r := fun e he => (mem_product.1 (hsub he)).2
    refine ⟨⟨fun e he => ?_, ?_, ?_, ?_⟩, mem_image.2 ⟨(a, r), mem_insert_self _ _, rfl⟩⟩
    · rcases mem_insert.1 he with rfl | he
      · exact mem_product.2 ⟨mem_insert_self _ _, hrR⟩
      · exact mem_product.2 ⟨mem_insert_of_mem (hfst e he), mem_of_mem_erase (hsnd e he)⟩
    · intro e he e' he' h
      rcases mem_insert.1 he with rfl | he <;> rcases mem_insert.1 he' with rfl | he'
      · rfl
      · exfalso
        have h' : a = e'.1 := h
        exact ha (h' ▸ hfst e' he')
      · exfalso
        have h' : e.1 = a := h
        exact ha (h' ▸ hfst e he)
      · exact h1 e he e' he' h
    · intro e he e' he' h
      rcases mem_insert.1 he with rfl | he <;> rcases mem_insert.1 he' with rfl | he'
      · rfl
      · exfalso
        have h' : r = e'.2 := h
        have := hsnd e' he'
        rw [← h'] at this
        simp at this
      · exfalso
        have h' : e.2 = r := h
        have := hsnd e he
        rw [h'] at this
        simp at this
      · exact h2 e he e' he' h
    · intro e he
      rcases mem_insert.1 he with rfl | he
      · exact hcr
      · exact hc e he

theorem parentHist_of_not_mem {a : α} {L : Finset α} (ha : a ∉ L) (R : Finset β)
    {M : Finset (α × β)} (hM : M ∈ D.matchings p q L R) :
    D.parentHist p q (insert a L) R M = D.left (p a) ::ₘ D.parentHist p q L R M := by
  obtain ⟨hsub, -⟩ := (mem_matchings D).1 hM
  have haM : a ∉ M.image Prod.fst := by
    intro h
    obtain ⟨e, he, rfl⟩ := mem_image.1 h
    exact ha (mem_product.1 (hsub he)).1
  unfold parentHist
  rw [filter_insert, ite_eq_left haM, insert_val_of_notMem (by simp [ha]), Multiset.map_cons]
  simp only [Multiset.add_cons, Multiset.cons_add]

theorem parentHist_insert {a : α} {L : Finset α} (ha : a ∉ L) {R : Finset β} {r : β}
    (_hr : r ∈ R) {M : Finset (α × β)} (hM : M ∈ D.matchings p q L (R.erase r)) :
    D.parentHist p q (insert a L) R (insert (a, r) M) =
      D.pair (p a) (q r) ::ₘ D.parentHist p q L (R.erase r) M := by
  obtain ⟨hsub, -⟩ := (mem_matchings D).1 hM
  have hfst : ∀ e ∈ M, e.1 ∈ L := fun e he => (mem_product.1 (hsub he)).1
  have hsnd : ∀ e ∈ M, e.2 ∈ R.erase r := fun e he => (mem_product.1 (hsub he)).2
  have har : (a, r) ∉ M := fun h => ha (hfst _ h)
  have hL : (insert a L).filter (· ∉ (insert (a, r) M).image Prod.fst) =
      L.filter (· ∉ M.image Prod.fst) := by
    ext x
    simp only [mem_filter, mem_insert, image_insert]
    constructor
    · rintro ⟨rfl | hx, h⟩
      · exact absurd (Or.inl rfl) h
      · exact ⟨hx, fun h' => h (Or.inr h')⟩
    · rintro ⟨hx, h⟩
      refine ⟨Or.inr hx, ?_⟩
      rintro (rfl | h')
      · exact ha hx
      · exact h h'
  have hR : R.filter (· ∉ (insert (a, r) M).image Prod.snd) =
      (R.erase r).filter (· ∉ M.image Prod.snd) := by
    ext y
    simp only [mem_filter, mem_erase, image_insert, mem_insert]
    constructor
    · rintro ⟨hy, h⟩
      exact ⟨⟨fun h' => h (Or.inl h'), hy⟩, fun h' => h (Or.inr h')⟩
    · rintro ⟨⟨hne, hy⟩, h⟩
      exact ⟨hy, by rintro (h' | h'); exacts [hne h', h h']⟩
  unfold parentHist
  rw [hL, hR, insert_val_of_notMem har, Multiset.map_cons]
  simp only [Multiset.cons_add]

end Lemmas

/-- **The merge recurrence counts matchings.** For left classes listed (without repetition) by
`l` and right classes `R`, the multiset of parent histograms of all compatible partial matchings
(each shifted by `H`) is exactly what the recurrence `run` produces from the left profiles
`l.map p`, the right histogram `R.val.map q` and the initial parent histogram `H`. -/
theorem run_spec (p : α → P₁) (q : β → P₂) :
    ∀ (l : List α), l.Nodup → ∀ (R : Finset β) (H : Multiset Q),
      ∑ M ∈ D.matchings p q l.toFinset R, ({H + D.parentHist p q l.toFinset R M} :
        Multiset (Multiset Q)) = D.run (l.map p) (R.val.map q) H := by
  intro l
  induction l with
  | nil =>
    intro _ R H
    simp only [List.toFinset_nil, matchings_empty_left, sum_singleton, List.map_nil, run_nil,
      Multiset.map_map]
    simp [parentHist]
  | cons a l ih =>
    intro hl R H
    obtain ⟨ha, hl⟩ := List.nodup_cons.1 hl
    have ha' : a ∉ l.toFinset := by simpa using ha
    rw [List.toFinset_cons, List.map_cons, run_cons,
      ← sum_filter_add_sum_filter_not _ (fun M => a ∉ M.image Prod.fst)]
    congr 1
    · -- `a` stays separate
      rw [filter_not_mem_fst D ha', ← ih hl R (D.left (p a) ::ₘ H)]
      refine sum_congr rfl fun M hM => ?_
      rw [parentHist_of_not_mem D ha' R hM, Multiset.add_cons, Multiset.cons_add]
    · -- `a` is paired with some compatible `r`
      simp only [not_not]
      rw [filter_mem_fst D ha', sum_biUnion]
      · -- evaluate the inner sums by induction, then group the partners by profile
        have hinner : ∀ r ∈ R.filter (fun r => D.compat (p a) (q r)),
            ∑ M ∈ (D.matchings p q l.toFinset (R.erase r)).image (insert (a, r)),
              ({H + D.parentHist p q (insert a l.toFinset) R M} : Multiset (Multiset Q)) =
            D.run (l.map p) ((R.val.map q).erase (q r)) (D.pair (p a) (q r) ::ₘ H) := by
          intro r hr
          have hrR := (mem_filter.1 hr).1
          rw [sum_image]
          · rw [← Multiset.map_erase_of_mem _ _ hrR, ← erase_val,
              ← ih hl (R.erase r) (D.pair (p a) (q r) ::ₘ H)]
            refine sum_congr rfl fun M hM => ?_
            rw [parentHist_insert D ha' hrR hM, Multiset.add_cons, Multiset.cons_add]
          · intro M hM M' hM' h
            have hnot : ∀ N ∈ D.matchings p q l.toFinset (R.erase r), (a, r) ∉ N := by
              intro N hN hN'
              exact ha' (mem_product.1 (((mem_matchings D).1 hN).1 hN')).1
            have := congrArg (fun N => N.erase (a, r)) h
            simpa [erase_insert (hnot M hM), erase_insert (hnot M' hM')] using this
        rw [sum_congr rfl hinner]
        rw [sum_comp (fun v => D.run (l.map p) ((R.val.map q).erase v) (D.pair (p a) v ::ₘ H))
          (fun r => q r)]
        apply sum_congr
        · ext v
          simp only [mem_image, mem_filter, Multiset.mem_toFinset, Multiset.mem_map, mem_val]
          constructor
          · rintro ⟨r, ⟨hr, hc⟩, rfl⟩
            exact ⟨⟨r, hr, rfl⟩, hc⟩
          · rintro ⟨⟨r, hr, rfl⟩, hc⟩
            exact ⟨r, ⟨hr, hc⟩, rfl⟩
        · intro v hv
          congr 1
          rw [Multiset.count_map, filter_filter, card_def, filter_val]
          congr 1
          apply Multiset.filter_congr
          intro r _
          obtain ⟨-, hc⟩ := mem_filter.1 hv
          constructor
          · rintro ⟨-, h⟩
            exact h.symm
          · intro h
            exact ⟨h ▸ hc, h.symm⟩
      · -- different partners give different matchings
        intro r hr r' hr' hne
        simp only [Function.onFun]
        rw [disjoint_left]
        intro M hM hM'
        obtain ⟨N, hN, rfl⟩ := mem_image.1 hM
        obtain ⟨N', hN', hNN'⟩ := mem_image.1 hM'
        have hmem : (a, r) ∈ insert (a, r') N' := hNN' ▸ mem_insert_self _ _
        rcases mem_insert.1 hmem with h | h
        · exact hne (Prod.ext_iff.1 h).2
        · exact ha' (mem_product.1 (((mem_matchings D).1 hN').1 h)).1

/-- The same statement, phrased with `Multiset.map`. -/
theorem run_spec' (p : α → P₁) (q : β → P₂) (l : List α) (hl : l.Nodup) (R : Finset β) :
    (D.matchings p q l.toFinset R).val.map (D.parentHist p q l.toFinset R) =
      D.run (l.map p) (R.val.map q) 0 := by
  rw [← run_spec D p q l hl R 0, sum_eq_multiset_sum]
  simp only [zero_add]
  have : (fun M => ({D.parentHist p q l.toFinset R M} : Multiset (Multiset Q))) =
      (fun y => {y}) ∘ D.parentHist p q l.toFinset R := rfl
  rw [this, ← Multiset.map_map, Multiset.sum_map_singleton]

end MergeData

end SubspaceConvolution
