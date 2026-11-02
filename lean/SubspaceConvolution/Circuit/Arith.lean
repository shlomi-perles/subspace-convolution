/-
Copyright (c) 2026 Shlomo A. Perles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shlomo A. Perles
-/
import SubspaceConvolution.Circuit.SLP

/-!
# General arithmetic straight-line programs

For bilinear computations (span convolution, kernels whose coefficients are inputs) we also need
products of two computed values.  An arithmetic program has linear gates `z = a x + b y`
(constants free) and product gates `z = x y`; `ArithCost M s` says `M` is computed with at most
`s` gates.  A linear gate is at most three ring operations, so `ArithCost` counts arithmetic
operations up to a factor of three.
-/

open Finset

namespace SubspaceConvolution.Circuit

/-- A gate of an arithmetic program. -/
inductive AGate (R : Type*) (I : Type*) where
  | lin (a : R) (x : Wire I) (b : R) (y : Wire I)
  | mul (x y : Wire I)

variable {R : Type*} [CommRing R] {I O : Type*}

/-- The value of a gate. -/
def AGate.eval : AGate R I → (I → R) → List R → R
  | .lin a x b y, f, vals => a * read f vals x + b * read f vals y
  | .mul x y, f, vals => read f vals x * read f vals y

/-- The values of all gates, in order. -/
def arun (gs : List (AGate R I)) (f : I → R) : List R :=
  gs.foldl (fun vals g => vals ++ [g.eval f vals]) []

/-- An arithmetic straight-line program with inputs `I` and outputs `O`. -/
structure ASLP (R I O : Type*) where
  gates : List (AGate R I)
  out : O → Wire I

/-- The map computed by an arithmetic program. -/
def ASLP.eval (P : ASLP R I O) (f : I → R) : O → R :=
  fun o => read f (arun P.gates f) (P.out o)

/-- `M` is computed by an arithmetic straight-line program with at most `s` gates. -/
def ArithCost (M : (I → R) → O → R) (s : ℕ) : Prop :=
  ∃ P : ASLP R I O, P.gates.length ≤ s ∧ P.eval = M

/-! ### Simulation lemmas

Programs are combined by concatenating gate lists and renaming wires.  A wire `inr j` with `j` at
least the number of gates computed so far reads as `0`; when two programs are concatenated, such
references of the first program are redirected beyond the whole combined program (`fixW`), so
that they never start reading gates of the second one. -/

namespace ArithAux

omit [CommRing R] in
/-- **Generic simulation.**  If every mapped gate `φ g` reads, in the context `vals₁ ++ v`, the
value that `g` reads in the context `v`, then running the mapped gates after `vals₁` appends
exactly the values of the original gates. -/
theorem foldl_map_sim {G G' : Type*} (E : G → List R → R) (E' : G' → List R → R) (φ : G' → G)
    (vals₁ : List R) (N : ℕ) :
    ∀ (hs : List G') (acc : List R), acc.length + hs.length ≤ N →
      (∀ g ∈ hs, ∀ v : List R, v.length < N → E (φ g) (vals₁ ++ v) = E' g v) →
      (hs.map φ).foldl (fun vals g => vals ++ [E g vals]) (vals₁ ++ acc) =
        vals₁ ++ hs.foldl (fun vals g => vals ++ [E' g vals]) acc
  | [], acc, _, _ => by simp
  | g :: hs, acc, hlen, hE => by
    simp only [List.length_cons] at hlen
    simp only [List.map_cons, List.foldl_cons]
    have hlen' : (acc ++ [E' g acc]).length + hs.length ≤ N := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [hE g List.mem_cons_self acc (by omega), List.append_assoc]
    exact foldl_map_sim E E' φ vals₁ N hs _ hlen'
      (fun g' hg' v hv => hE g' (List.mem_cons_of_mem _ hg') v hv)

omit [CommRing R] in
theorem length_foldl {G : Type*} (E : G → List R → R) :
    ∀ (gs : List G) (acc : List R),
      (gs.foldl (fun vals g => vals ++ [E g vals]) acc).length = acc.length + gs.length
  | [], acc => by simp
  | g :: gs, acc => by
    simp only [List.foldl_cons]
    rw [length_foldl E gs]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem length_arun (gs : List (AGate R I)) (f : I → R) : (arun gs f).length = gs.length := by
  have := length_foldl (fun g vals => AGate.eval g f vals) gs []
  rw [List.length_nil, Nat.zero_add] at this
  exact this

theorem arun_append (gs hs : List (AGate R I)) (f : I → R) :
    arun (gs ++ hs) f = hs.foldl (fun vals g => vals ++ [g.eval f vals]) (arun gs f) := by
  simp only [arun, List.foldl_append]

/-- Rename the wires of a gate. -/
def rewire {I' : Type*} (ρ : Wire I' → Wire I) : AGate R I' → AGate R I
  | .lin a x b y => .lin a (ρ x) b (ρ y)
  | .mul x y => .mul (ρ x) (ρ y)

theorem eval_rewire {I' : Type*} (ρ : Wire I' → Wire I) (g : AGate R I') (f : I → R)
    (f' : I' → R) (vals vals' : List R) (h : ∀ w, read f vals (ρ w) = read f' vals' w) :
    (rewire ρ g).eval f vals = g.eval f' vals' := by
  cases g with
  | lin a x b y => simp only [rewire, AGate.eval, h]
  | mul x y => simp only [rewire, AGate.eval, h]

/-- Running renamed gates after a program `gs`: the values of `gs` followed by the values of the
original gates, provided the renaming reads correctly in every intermediate context. -/
theorem arun_append_map {I' : Type*} (gs : List (AGate R I)) (hs : List (AGate R I'))
    (ρ : Wire I' → Wire I) (f : I → R) (f' : I' → R)
    (h : ∀ v : List R, v.length < hs.length → ∀ w, read f (arun gs f ++ v) (ρ w) = read f' v w) :
    arun (gs ++ hs.map (rewire ρ)) f = arun gs f ++ arun hs f' := by
  rw [arun_append]
  have := foldl_map_sim (fun g vals => AGate.eval g f vals) (fun g vals => AGate.eval g f' vals)
    (rewire ρ) (arun gs f) hs.length hs [] (by simp)
    (fun g _ v hv => eval_rewire ρ g f f' _ _ (h v hv))
  rw [List.append_nil] at this
  exact this

/-- Redirect references of a program with `n` gates to gates it does not have to wire `N`. -/
def fixW (n N : ℕ) : Wire I → Wire I :=
  Sum.elim Sum.inl (fun k => if k < n then Sum.inr k else Sum.inr N)

theorem read_fixW (f : I → R) {vals v : List R} {n N : ℕ} (hn : vals.length = n)
    (hN : n + v.length ≤ N) (w : Wire I) : read f (vals ++ v) (fixW n N w) = read f vals w := by
  rcases w with i | k
  · rfl
  · by_cases hk : k < n
    · simp only [fixW, Sum.elim_inr, hk, ite_true, read]
      exact List.getD_append _ _ _ _ (by omega)
    · simp only [fixW, Sum.elim_inr, hk, ite_false, read]
      rw [List.getD_eq_default _ _ (by simp only [List.length_append]; omega),
        List.getD_eq_default _ _ (by omega)]

/-- Wires of a program run after `n` gates: gate `k` becomes gate `n + k`, input `i` becomes
`ι i`. -/
def shiftW {I' : Type*} (n : ℕ) (ι : I' → Wire I) : Wire I' → Wire I :=
  Sum.elim ι (fun k => Sum.inr (n + k))

theorem read_shiftW {I' : Type*} {ι : I' → Wire I} {f : I → R} {f' : I' → R} {vals v : List R}
    {n : ℕ} (hn : vals.length = n) (hι : ∀ i, read f (vals ++ v) (ι i) = f' i) (w : Wire I') :
    read f (vals ++ v) (shiftW n ι w) = read f' v w := by
  rcases w with i | k
  · exact hι i
  · simp only [shiftW, Sum.elim_inr, read]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega

theorem read_map {I' : Type*} (d : I → I') (f : I' → R) (vals : List R) (w : Wire I) :
    read f vals (Sum.map d id w) = read (fun i => f (d i)) vals w := by
  rcases w with i | k <;> rfl

omit [CommRing R] in
/-- A program whose gates do not read earlier gates. -/
theorem foldl_const {G : Type*} (E : G → List R → R) (c : G → R) :
    ∀ (gs : List G) (acc : List R), (∀ g ∈ gs, ∀ vals, E g vals = c g) →
      gs.foldl (fun vals g => vals ++ [E g vals]) acc = acc ++ gs.map c
  | [], acc, _ => by simp
  | g :: gs, acc, hc => by
    simp only [List.foldl_cons, List.map_cons]
    rw [hc g List.mem_cons_self acc,
      foldl_const E c gs _ (fun g' hg' => hc g' (List.mem_cons_of_mem _ hg'))]
    simp

end ArithAux

namespace ArithCost

theorem of_linCost {C : Set R} {M : (I → R) → O → R} {s : ℕ} (h : LinCost C M s) :
    ArithCost M s := by
  obtain ⟨P, hs, -, rfl⟩ := h
  refine ⟨⟨P.gates.map (fun g => AGate.lin g.a g.x g.b g.y), P.out⟩, ?_, ?_⟩
  · simpa [SLP.size] using hs
  · funext f o
    have key : arun (P.gates.map (fun g => AGate.lin g.a g.x g.b g.y)) f = run P.gates f :=
      ArithAux.foldl_map_sim (fun g vals => AGate.eval g f vals)
        (fun g vals => Gate.eval g f vals) (fun g => AGate.lin g.a g.x g.b g.y) []
        P.gates.length P.gates [] (by simp) (fun _ _ _ _ => rfl)
    simp only [ASLP.eval, SLP.eval, key]

theorem mono {M : (I → R) → O → R} {s t : ℕ} (h : ArithCost M s) (hst : s ≤ t) :
    ArithCost M t := by
  obtain ⟨P, hP, hM⟩ := h
  exact ⟨P, hP.trans hst, hM⟩

theorem congr {M M' : (I → R) → O → R} {s : ℕ} (h : ArithCost M s) (hM : M = M') :
    ArithCost M' s := hM ▸ h

theorem reindex {I' O' : Type*} {M : (I → R) → O → R} {s : ℕ} (h : ArithCost M s)
    (d : I → I') (e : O' → O) :
    ArithCost (fun (f : I' → R) (o : O') => M (fun i => f (d i)) (e o)) s := by
  obtain ⟨P, hP, rfl⟩ := h
  refine ⟨⟨P.gates.map (ArithAux.rewire (Sum.map d id)), fun o => Sum.map d id (P.out (e o))⟩,
    ?_, ?_⟩
  · simpa using hP
  · funext f o
    have key : arun (P.gates.map (ArithAux.rewire (Sum.map d id))) f =
        arun P.gates (fun i => f (d i)) := by
      have := ArithAux.arun_append_map [] P.gates (Sum.map d id) f (fun i => f (d i))
        (fun v _ w => ArithAux.read_map d f _ w)
      rw [List.nil_append] at this
      exact this
    simp only [ASLP.eval, key, ArithAux.read_map]

theorem comp {J : Type*} {M₁ : (I → R) → J → R} {M₂ : (J → R) → O → R} {s₁ s₂ : ℕ}
    (h₁ : ArithCost M₁ s₁) (h₂ : ArithCost M₂ s₂) : ArithCost (fun f => M₂ (M₁ f)) (s₁ + s₂) := by
  obtain ⟨P₁, hP₁, rfl⟩ := h₁
  obtain ⟨P₂, hP₂, rfl⟩ := h₂
  let n₁ := P₁.gates.length
  let N := P₁.gates.length + P₂.gates.length
  let ρ : Wire J → Wire I := ArithAux.shiftW n₁ (fun j => ArithAux.fixW n₁ N (P₁.out j))
  refine ⟨⟨P₁.gates ++ P₂.gates.map (ArithAux.rewire ρ), fun o => ρ (P₂.out o)⟩, ?_, ?_⟩
  · simp only [List.length_append, List.length_map]
    omega
  · funext f o
    have hρ : ∀ v : List R, v.length ≤ P₂.gates.length → ∀ w,
        read f (arun P₁.gates f ++ v) (ρ w) = read (P₁.eval f) v w := fun v hv w =>
      ArithAux.read_shiftW (ArithAux.length_arun _ _)
        (fun j => ArithAux.read_fixW f (ArithAux.length_arun _ _) (by omega) (P₁.out j)) w
    have key := ArithAux.arun_append_map P₁.gates P₂.gates ρ f (P₁.eval f)
      (fun v hv w => hρ v hv.le w)
    simp only [ASLP.eval, key]
    exact hρ _ (ArithAux.length_arun _ _).le _

theorem sumElim {O₁ O₂ : Type*} {M₁ : (I → R) → O₁ → R} {M₂ : (I → R) → O₂ → R} {s₁ s₂ : ℕ}
    (h₁ : ArithCost M₁ s₁) (h₂ : ArithCost M₂ s₂) :
    ArithCost (fun f => Sum.elim (M₁ f) (M₂ f)) (s₁ + s₂) := by
  obtain ⟨P₁, hP₁, rfl⟩ := h₁
  obtain ⟨P₂, hP₂, rfl⟩ := h₂
  let n₁ := P₁.gates.length
  let N := P₁.gates.length + P₂.gates.length
  let ρ : Wire I → Wire I := ArithAux.shiftW n₁ Sum.inl
  refine ⟨⟨P₁.gates ++ P₂.gates.map (ArithAux.rewire ρ),
    Sum.elim (fun o => ArithAux.fixW n₁ N (P₁.out o)) (fun o => ρ (P₂.out o))⟩, ?_, ?_⟩
  · simp only [List.length_append, List.length_map]
    omega
  · funext f o
    have hρ : ∀ v : List R, ∀ w, read f (arun P₁.gates f ++ v) (ρ w) = read f v w :=
      fun v w => ArithAux.read_shiftW (ArithAux.length_arun _ _) (fun _ => rfl) w
    have key := ArithAux.arun_append_map P₁.gates P₂.gates ρ f f (fun v _ w => hρ v w)
    rcases o with o | o
    · simp only [ASLP.eval, key, Sum.elim_inl]
      exact ArithAux.read_fixW f (ArithAux.length_arun _ _) (by rw [ArithAux.length_arun]) _
    · simp only [ASLP.eval, key, Sum.elim_inr]
      exact hρ _ _

/-- Pointwise products of two tables: one product gate per entry. -/
theorem mulPointwise {J : Type*} [Fintype J] :
    ArithCost (fun (f : J ⊕ J → R) (j : J) => f (Sum.inl j) * f (Sum.inr j)) (Fintype.card J) := by
  let e := Fintype.equivFin J
  let G : Fin (Fintype.card J) → AGate R (J ⊕ J) := fun k =>
    AGate.mul (Sum.inl (Sum.inl (e.symm k))) (Sum.inl (Sum.inr (e.symm k)))
  refine ⟨⟨List.ofFn G, fun j => Sum.inr (e j)⟩, by simp, ?_⟩
  funext f j
  have key : arun (List.ofFn G) f =
      List.ofFn (fun k => f (Sum.inl (e.symm k)) * f (Sum.inr (e.symm k))) := by
    have := ArithAux.foldl_const (fun g vals => AGate.eval g f vals)
      (fun g => AGate.eval g f []) (List.ofFn G) [] (fun g hg vals => by
        obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
        rfl)
    simp only [List.nil_append, List.map_ofFn] at this
    exact this
  simp only [ASLP.eval, key, read]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  simp

end ArithCost

end SubspaceConvolution.Circuit
