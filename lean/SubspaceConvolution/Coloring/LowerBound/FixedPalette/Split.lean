/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Coloring.LowerBound.FixedPalette.Defs
import SubspaceConvolution.Coloring.LowerBound.FixedPalette.Gadgets

/-!
# Splitting the colorings of `G_φ`

We normalize the palette (`T = 0`, `F_A = 1`, `F_B = 2`; this accounts for the factor `6`) and
split a normalized coloring into its *core* part (inputs, literal pairs and clause pairs), its
cycle part (one cycle per group) and its triangle part (one triangle per NAE gadget).  A
normalized coloring is proper iff the core part satisfies `CoreOK`, every cycle satisfies
`CycOK` and every triangle satisfies `TriOK`; cycles and triangles only see the core.
-/

namespace SubspaceConvolution.FixedPalette

variable {k m : ℕ}

/-- Colors of the core vertices: inputs, literal pairs, clause pairs. -/
abbrev CoreCol (k m : ℕ) : Type :=
  (Grp k m → Fin (2 ^ k) → Fin 3) × (Fin m → Fin 3 → Bool → Fin 3) × (Fin m → Bool → Fin 3)

/-- Colors of the cycle vertices. -/
abbrev CycCol (k m : ℕ) : Type := Grp k m → Fin (2 ^ k + 1) → Fin 3

/-- Colors of the NAE triangle vertices. -/
abbrev TriCol (m : ℕ) : Type := Fin m × Fin 4 → Fin 3 → Fin 3

/-- The color of a core vertex (palette normalized; junk on cycle and triangle vertices). -/
def coreVal (c : CoreCol k m) : Vtx k m → Fin 3
  | .pal a => a
  | .inp γ p => c.1 γ p
  | .cyc _ _ => 0
  | .lit i t b => c.2.1 i t b
  | .sig i b => c.2.2 i b
  | .tri _ _ _ => 0

/-- The core coloring is proper on all edges between core vertices (palette normalized). -/
structure CoreOK (φ : GridCNF k) (c : CoreCol k φ.m) : Prop where
  inp_forb : ∀ γ p, c.1 γ p ≠ γ.forbCol
  ab : ∀ h q γ p j, γ.row φ = some j → asg k q j ≠ asg k p h → c.1 (.colB h) q ≠ c.1 γ p
  lit_pal : ∀ i t b, c.2.1 i t b ≠ 1
  lit_pair : ∀ i t, c.2.1 i t true ≠ c.2.1 i t false
  lit_inp : ∀ i t b p, (φ.clause i t).evalRow (asg k p) ≠ b → c.2.1 i t b ≠ c.1 (.loc i t) p
  sig_pal : ∀ i b, c.2.2 i b ≠ 1
  sig_pair : ∀ i, c.2.2 i true ≠ c.2.2 i false

/-- The cycle of group `γ` is properly colored by `w`. -/
def CycOK (c : CoreCol k m) (γ : Grp k m) (w : Fin (2 ^ k + 1) → Fin 3) : Prop :=
  w 0 ≠ γ.falseCol ∧ (∀ i, w i ≠ w (i + 1)) ∧ ∀ p : Fin (2 ^ k), w p.succ ≠ c.1 γ p

/-- The NAE triangle `iq` is properly colored by `z`. -/
def TriOK (c : CoreCol k m) (iq : Fin m × Fin 4) (z : Fin 3 → Fin 3) : Prop :=
  (∀ r r', r < r' → z r ≠ z r') ∧ ∀ r, z r ≠ coreVal c (term iq.1 iq.2 r)

/-- Assemble a normalized coloring from its parts. -/
def join (c : CoreCol k m) (w : CycCol k m) (y : TriCol m) : Vtx k m → Fin 3
  | .pal a => a
  | .inp γ p => c.1 γ p
  | .cyc γ i => w γ i
  | .lit i t b => c.2.1 i t b
  | .sig i b => c.2.2 i b
  | .tri i q r => y (i, q) r

theorem join_term (c : CoreCol k m) (w : CycCol k m) (y : TriCol m) (i : Fin m) (q : Fin 4)
    (r : Fin 3) : join c w y (term i q r) = coreVal c (term i q r) := by
  fin_cases q <;> fin_cases r <;> rfl

theorem edge_term (φ : GridCNF k) (i : Fin φ.m) (q : Fin 4) (r : Fin 3) :
    edge φ (.tri i q r) (term i q r) = true := by
  fin_cases q <;> fin_cases r <;> simp [edge, term]

section Proper

variable {φ : GridCNF k} {c : CoreCol k φ.m} {w : CycCol k φ.m} {y : TriCol φ.m}

theorem join_ne_of_edge (hc : CoreOK φ c) (hw : ∀ γ, CycOK c γ (w γ))
    (hy : ∀ iq, TriOK c iq (y iq)) {x z : Vtx k φ.m} (h : edge φ x z = true) :
    join c w y x ≠ join c w y z := by
  cases x with
  | pal a =>
    cases z <;> simp [edge] at h
    exact ne_of_lt h
  | inp γ q =>
    cases z with
    | pal a =>
      simp only [edge, decide_eq_true_eq] at h
      subst h
      exact hc.inp_forb γ q
    | inp γ' p =>
      cases γ with
      | colB hh =>
        cases hr : γ'.row φ with
        | none => simp [edge, hr] at h
        | some j =>
          simp only [edge, hr, decide_eq_true_eq] at h
          exact hc.ab hh q γ' p j hr h
      | rowA j => simp [edge] at h
      | loc i t => simp [edge] at h
    | _ => simp [edge] at h
  | cyc γ i =>
    cases z with
    | pal a =>
      simp only [edge, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact (hw γ).1
    | inp γ' p =>
      simp only [edge, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact (hw γ').2.2 p
    | cyc γ' i' =>
      simp only [edge, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact (hw γ').2.1 i
    | _ => simp [edge] at h
  | lit i t b =>
    cases z with
    | pal a =>
      simp only [edge, decide_eq_true_eq] at h
      subst h
      exact hc.lit_pal i t b
    | inp γ p =>
      simp only [edge, decide_eq_true_eq] at h
      obtain ⟨rfl, h⟩ := h
      exact hc.lit_inp i t b p h
    | lit i' t' b' =>
      simp only [edge, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact hc.lit_pair i' t'
    | _ => simp [edge] at h
  | sig i b =>
    cases z with
    | pal a =>
      simp only [edge, decide_eq_true_eq] at h
      subst h
      exact hc.sig_pal i b
    | sig i' b' =>
      simp only [edge, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact hc.sig_pair i'
    | _ => simp [edge] at h
  | tri i q r =>
    have hterm : ∀ v, term i q r = v → join c w y (.tri i q r) ≠ join c w y v := by
      rintro v rfl
      rw [join_term]
      exact (hy (i, q)).2 r
    cases z with
    | pal a =>
      simp only [edge, decide_eq_true_eq] at h
      exact hterm _ h
    | lit i' t b =>
      simp only [edge, decide_eq_true_eq] at h
      exact hterm _ h
    | sig i' b =>
      simp only [edge, decide_eq_true_eq] at h
      exact hterm _ h
    | tri i' q' r' =>
      simp only [edge, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl, h⟩ := h
      exact (hy (i', q')).1 r r' h
    | _ => simp [edge] at h

theorem ok_of_join_ne (hf : ∀ x z, edge φ x z = true → join c w y x ≠ join c w y z) :
    CoreOK φ c ∧ (∀ γ, CycOK c γ (w γ)) ∧ ∀ iq, TriOK c iq (y iq) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro γ p
    exact hf (.inp γ p) (.pal γ.forbCol) (by simp [edge])
  · intro hh q γ p j hj hne
    exact hf (.inp (.colB hh) q) (.inp γ p) (by simp [edge, hj, hne])
  · intro i t b
    exact hf (.lit i t b) (.pal 1) (by simp [edge])
  · intro i t
    exact hf (.lit i t true) (.lit i t false) (by simp [edge])
  · intro i t b p hne
    exact hf (.lit i t b) (.inp (.loc i t) p) (by simp [edge, hne])
  · intro i b
    exact hf (.sig i b) (.pal 1) (by simp [edge])
  · intro i
    exact hf (.sig i true) (.sig i false) (by simp [edge])
  · intro γ
    refine ⟨hf (.cyc γ 0) (.pal γ.falseCol) (by simp [edge]), fun i => ?_, fun p => ?_⟩
    · exact hf (.cyc γ i) (.cyc γ (i + 1)) (by simp [edge])
    · exact hf (.cyc γ p.succ) (.inp γ p) (by simp [edge])
  · rintro ⟨i, q⟩
    refine ⟨fun r r' hr => hf (.tri i q r) (.tri i q r') (by simp [edge, hr]), fun r => ?_⟩
    have := hf (.tri i q r) (term i q r) (edge_term φ i q r)
    rwa [join_term] at this

theorem proper_join_iff :
    (∀ x z, (graph φ).Adj x z → join c w y x ≠ join c w y z) ↔
      CoreOK φ c ∧ (∀ γ, CycOK c γ (w γ)) ∧ ∀ iq, TriOK c iq (y iq) := by
  constructor
  · intro hf
    exact ok_of_join_ne fun x z h => hf x z (Or.inl h)
  · rintro ⟨hc, hw, hy⟩ x z (h | h)
    · exact join_ne_of_edge hc hw hy h
    · exact (join_ne_of_edge hc hw hy h).symm

end Proper

/-! ## Normalized colorings and the fiber decomposition -/

/-- Proper colorings of `G_φ` as functions. -/
def ProperCol (φ : GridCNF k) : Type :=
  {f : Vtx k φ.m → Fin 3 // ∀ x z, (graph φ).Adj x z → f x ≠ f z}

/-- Proper colorings with the palette colored `T = 0`, `F_A = 1`, `F_B = 2`. -/
def NormCol (φ : GridCNF k) : Type :=
  {f : Vtx k φ.m → Fin 3 // (∀ x z, (graph φ).Adj x z → f x ≠ f z) ∧ ∀ a, f (.pal a) = a}

def coreOf (f : Vtx k m → Fin 3) : CoreCol k m :=
  (fun γ p => f (.inp γ p), fun i t b => f (.lit i t b), fun i b => f (.sig i b))

def cycOf (f : Vtx k m → Fin 3) : CycCol k m := fun γ i => f (.cyc γ i)

def triOf (f : Vtx k m → Fin 3) : TriCol m := fun iq r => f (.tri iq.1 iq.2 r)

theorem join_of (f : Vtx k m → Fin 3) (hf : ∀ a, f (.pal a) = a) :
    join (coreOf f) (cycOf f) (triOf f) = f := by
  funext v
  cases v <;> simp [join, coreOf, cycOf, triOf, hf]

/-- The fiber of the core coloring `c`: its cycle and triangle extensions. -/
def Fiber (φ : GridCNF k) (c : CoreCol k φ.m) : Type :=
  {x : CycCol k φ.m × TriCol φ.m //
    CoreOK φ c ∧ (∀ γ, CycOK c γ (x.1 γ)) ∧ ∀ iq, TriOK c iq (x.2 iq)}

instance (φ : GridCNF k) (c : CoreCol k φ.m) : Finite (Fiber φ c) := by
  unfold Fiber
  infer_instance

/-- Normalized proper colorings are pairs of a core coloring and an extension. -/
def normEquiv (φ : GridCNF k) : NormCol φ ≃ Σ c : CoreCol k φ.m, Fiber φ c where
  toFun f := ⟨coreOf f.1, ⟨(cycOf f.1, triOf f.1), by
    have h := f.2.1
    rw [← join_of f.1 f.2.2] at h
    exact proper_join_iff.1 h⟩⟩
  invFun x := ⟨join x.1 x.2.1.1 x.2.1.2, proper_join_iff.2 x.2.2, fun _ => rfl⟩
  left_inv f := Subtype.ext (join_of f.1 f.2.2)
  right_inv x := rfl

theorem card_normCol (φ : GridCNF k) :
    Nat.card (NormCol φ) = ∑ c : CoreCol k φ.m, Nat.card (Fiber φ c) := by
  rw [Nat.card_congr (normEquiv φ), Nat.card_sigma]

theorem card_fiber_of_not {φ : GridCNF k} {c : CoreCol k φ.m} (hc : ¬ CoreOK φ c) :
    Nat.card (Fiber φ c) = 0 := by
  have : IsEmpty (Fiber φ c) := ⟨fun x => hc x.2.1⟩
  exact Nat.card_of_isEmpty

theorem card_fiber {φ : GridCNF k} {c : CoreCol k φ.m} (hc : CoreOK φ c) :
    Nat.card (Fiber φ c) =
      (∏ γ, Nat.card {v // CycOK c γ v}) * ∏ iq, Nat.card {z // TriOK c iq z} := by
  let e : Fiber φ c ≃ (∀ γ, {v // CycOK c γ v}) × ∀ iq, {z // TriOK c iq z} :=
    { toFun := fun x => (fun γ => ⟨x.1.1 γ, x.2.2.1 γ⟩, fun iq => ⟨x.1.2 iq, x.2.2.2 iq⟩)
      invFun := fun x => ⟨(fun γ => (x.1 γ).1, fun iq => (x.2 iq).1),
        hc, fun γ => (x.1 γ).2, fun iq => (x.2 iq).2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_pi, Nat.card_pi]

/-! ## Normalizing the palette -/

/-- The palette coloring of a proper coloring, as a permutation of the colors. -/
noncomputable def palPerm {φ : GridCNF k} (f : ProperCol φ) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (fun a => f.1 (.pal a)) (by
    rw [← Finite.injective_iff_bijective]
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact f.2 (.pal a) (.pal b) (Or.inl (by simp [edge, h])) hab
    · exact f.2 (.pal a) (.pal b) (Or.inr (by simp [edge, h])) hab)

/-- Proper colorings are pairs of a palette permutation and a normalized coloring. -/
noncomputable def properEquiv (φ : GridCNF k) : ProperCol φ ≃ Equiv.Perm (Fin 3) × NormCol φ where
  toFun f := (palPerm f, ⟨fun v => (palPerm f).symm (f.1 v), fun x z h hxz =>
    f.2 x z h ((palPerm f).symm.injective hxz), fun a => by
      rw [Equiv.symm_apply_eq]
      rfl⟩)
  invFun x := ⟨fun v => x.1 (x.2.1 v), fun a b h hab => x.2.2.1 a b h (x.1.injective hab)⟩
  left_inv f := by
    apply Subtype.ext
    funext v
    simp
  right_inv x := by
    have hσ : palPerm ⟨fun v => x.1 (x.2.1 v), fun a b h hab => x.2.2.1 a b h (x.1.injective hab)⟩
        = x.1 := by
      ext a
      simp [palPerm, x.2.2.2 a]
    ext1
    · exact hσ
    · apply Subtype.ext
      funext v
      simp only
      rw [hσ]
      simp

theorem card_properCol (φ : GridCNF k) : Nat.card (ProperCol φ) = 6 * Nat.card (NormCol φ) := by
  rw [Nat.card_congr (properEquiv φ), Nat.card_prod, Nat.card_eq_fintype_card (α := Equiv.Perm _),
    Fintype.card_perm]
  rfl

end SubspaceConvolution.FixedPalette
