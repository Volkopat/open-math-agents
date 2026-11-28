import FormalConjectures.ErdosProblems.«1104»
import Mathlib

/-!
# Chromatic lower bound for triangle-free graphs

Theorem 1.3 of Hefty, Horn, King and Pfender supplies the graph construction.
Pedro Bessa formalized it for Erdős problem 1013 in PR #14897, commit
082a6ceef70c92998374257bbf202658d2353c75. The construction through
`Erdos1013Assembly.prove_alphaBound` below comes from its adaptation in
PR #22434, commit a32d6d50bab941785356f667511a8cf73b65b997.

For Erdős problem 1104, we count the fibers of an optimal coloring of
this graph and use the independence bound to obtain the chromatic lower bound.

https://arxiv.org/abs/2510.19718
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/14897
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/22434
-/

namespace Erdos1013Prob

open Finset BigOperators

section BasicProb

variable {Ω : Type*} [Fintype Ω]

/-- Finite expectation with respect to weight `P : Ω → ℝ`. -/
def E (P : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, P ω * f ω

/-- Finite probability of predicate `A` with respect to weight `P : Ω → ℝ`. -/
noncomputable def Pr (P : Ω → ℝ) (A : Ω → Prop) : ℝ :=
  by classical exact ∑ ω, if A ω then P ω else 0

/-- Weight `P` is a probability distribution on `Ω`. -/
structure IsProb (P : Ω → ℝ) : Prop where
  nonneg : ∀ ω, 0 ≤ P ω
  sum_eq_one : ∑ ω, P ω = 1

lemma Pr_eq_E (P : Ω → ℝ) (A : Ω → Prop) :
    Pr P A = E P (fun ω => by classical exact if A ω then 1 else 0) := by
  classical
  simp only [Pr, E]
  refine Finset.sum_congr rfl fun ω _ => ?_
  split_ifs <;> ring

lemma Pr_nonneg {P : Ω → ℝ} (hP : IsProb P) (A : Ω → Prop) : 0 ≤ Pr P A := by
  classical
  exact Finset.sum_nonneg fun ω _ => by split_ifs; exact hP.nonneg ω; exact le_rfl

lemma Pr_le_one {P : Ω → ℝ} (hP : IsProb P) (A : Ω → Prop) : Pr P A ≤ 1 := by
  classical
  calc Pr P A = ∑ ω, if A ω then P ω else 0 := rfl
    _ ≤ ∑ ω, P ω := Finset.sum_le_sum fun ω _ => by split_ifs; exact le_rfl; exact hP.nonneg ω
    _ = 1 := hP.sum_eq_one

lemma Pr_mono {P : Ω → ℝ} (hP : IsProb P) {A B : Ω → Prop} (h : ∀ ω, A ω → B ω) :
    Pr P A ≤ Pr P B := by
  classical
  refine Finset.sum_le_sum fun ω _ => ?_
  split_ifs with hA hB
  · exact le_rfl
  · exact absurd (h ω hA) hB
  · exact hP.nonneg ω
  · exact le_rfl

lemma Pr_congr {P : Ω → ℝ} {A B : Ω → Prop} (h : ∀ ω, A ω ↔ B ω) :
    Pr P A = Pr P B := by
  classical
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp only [h ω]

lemma Pr_false (P : Ω → ℝ) : Pr P (fun _ => False) = 0 := by
  classical simp [Pr]

lemma Pr_true {P : Ω → ℝ} (hP : IsProb P) : Pr P (fun _ => True) = 1 := by
  classical simp [Pr, hP.sum_eq_one]

lemma Pr_or_le {P : Ω → ℝ} (hP : IsProb P) (A B : Ω → Prop) :
    Pr P (fun ω => A ω ∨ B ω) ≤ Pr P A + Pr P B := by
  classical
  rw [Pr, Pr, Pr, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hA : A ω <;> by_cases hB : B ω <;> simp [hA, hB, hP.nonneg ω]

lemma Pr_exists_le {ι : Type*} {P : Ω → ℝ} (hP : IsProb P) (s : Finset ι) (A : ι → Ω → Prop) :
    Pr P (fun ω => ∃ i ∈ s, A i ω) ≤ ∑ i ∈ s, Pr P (A i) := by
  classical
  simp only [Pr]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun ω _ => ?_
  split_ifs with h
  · obtain ⟨i, hi, hAi⟩ := h
    have hle : (if A i ω then P ω else 0) ≤ ∑ j ∈ s, if A j ω then P ω else 0 :=
      Finset.single_le_sum (f := fun j => if A j ω then P ω else 0)
        (fun j _ => by split_ifs; exact hP.nonneg ω; exact le_rfl) hi
    simpa [hAi] using hle
  · exact Finset.sum_nonneg fun j _ => by split_ifs; exact hP.nonneg ω; exact le_rfl

lemma exists_of_Pr_lt_one {P : Ω → ℝ} (hP : IsProb P) {A : Ω → Prop} (h : Pr P A < 1) :
    ∃ ω, ¬ A ω := by
  by_contra hall
  push Not at hall
  have h1 : Pr P A = 1 := by
    rw [Pr_congr (B := fun _ => True) (fun ω => ⟨fun _ => trivial, fun _ => hall ω⟩)]
    exact Pr_true hP
  linarith

lemma E_const {P : Ω → ℝ} (hP : IsProb P) (c : ℝ) : E P (fun _ => c) = c := by
  simp only [E, ← Finset.sum_mul, hP.sum_eq_one, one_mul]

lemma E_add (P : Ω → ℝ) (f g : Ω → ℝ) : E P (fun ω => f ω + g ω) = E P f + E P g := by
  simp only [E, mul_add, Finset.sum_add_distrib]

lemma E_sub (P : Ω → ℝ) (f g : Ω → ℝ) : E P (fun ω => f ω - g ω) = E P f - E P g := by
  simp only [E, mul_sub, Finset.sum_sub_distrib]

lemma E_const_mul (P : Ω → ℝ) (c : ℝ) (f : Ω → ℝ) : E P (fun ω => c * f ω) = c * E P f := by
  simp only [E, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => by ring

lemma E_mono {P : Ω → ℝ} (hP : IsProb P) {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    E P f ≤ E P g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (hP.nonneg ω)

lemma E_nonneg {P : Ω → ℝ} (hP : IsProb P) {f : Ω → ℝ} (h : ∀ ω, 0 ≤ f ω) : 0 ≤ E P f :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (hP.nonneg ω) (h ω)

lemma E_sum {ι : Type*} (P : Ω → ℝ) (s : Finset ι) (f : ι → Ω → ℝ) :
    E P (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, E P (f i) := by
  simp only [E, Finset.mul_sum]
  exact Finset.sum_comm

lemma markov {P : Ω → ℝ} (hP : IsProb P) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) {t : ℝ} (ht : 0 < t) :
    Pr P (fun ω => t ≤ f ω) ≤ E P f / t := by
  classical
  rw [le_div_iff₀ ht, Pr, E, Finset.sum_mul]
  refine Finset.sum_le_sum fun ω _ => ?_
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left h (hP.nonneg ω)
  · simp only [zero_mul]
    exact mul_nonneg (hP.nonneg ω) (hf ω)

lemma exp_markov {P : Ω → ℝ} (hP : IsProb P) (f : Ω → ℝ) {s t : ℝ} (hs : 0 ≤ s) :
    Pr P (fun ω => t ≤ f ω) ≤ Real.exp (-s * t) * E P (fun ω => Real.exp (s * f ω)) := by
  have h1 : Pr P (fun ω => t ≤ f ω) ≤ Pr P (fun ω => Real.exp (s * t) ≤ Real.exp (s * f ω)) :=
    Pr_mono hP fun ω h => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h hs)
  have h2 := markov hP (fun ω => (Real.exp_pos (s * f ω)).le) (Real.exp_pos (s * t))
  calc Pr P (fun ω => t ≤ f ω)
      ≤ E P (fun ω => Real.exp (s * f ω)) / Real.exp (s * t) := h1.trans h2
    _ = Real.exp (-s * t) * E P (fun ω => Real.exp (s * f ω)) := by
        rw [div_eq_mul_inv, ← Real.exp_neg, neg_mul, mul_comm]

lemma E_equiv {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂] (e : Ω₁ ≃ Ω₂)
    (P : Ω₂ → ℝ) (f : Ω₂ → ℝ) :
    E (fun x => P (e x)) (fun x => f (e x)) = E P f :=
  Fintype.sum_equiv e _ _ (fun _ => rfl)

lemma Pr_equiv {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂] (e : Ω₁ ≃ Ω₂)
    (P : Ω₂ → ℝ) (A : Ω₂ → Prop) :
    Pr (fun x => P (e x)) (fun x => A (e x)) = Pr P A := by
  classical
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

end BasicProb

section ProductProb

/-- Product weight on `Ω₁ × Ω₂`. -/
def prodW {Ω₁ Ω₂ : Type*} (P : Ω₁ → ℝ) (Q : Ω₂ → ℝ) (x : Ω₁ × Ω₂) : ℝ :=
  P x.1 * Q x.2

lemma isProb_prodW {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂] {P : Ω₁ → ℝ} {Q : Ω₂ → ℝ}
    (hP : IsProb P) (hQ : IsProb Q) : IsProb (prodW P Q) where
  nonneg x := mul_nonneg (hP.nonneg x.1) (hQ.nonneg x.2)
  sum_eq_one := by
    simp only [prodW, Fintype.sum_prod_type, ← Finset.mul_sum, hQ.sum_eq_one, mul_one,
      hP.sum_eq_one]

lemma E_prodW {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂] (P : Ω₁ → ℝ) (Q : Ω₂ → ℝ)
    (f : Ω₁ × Ω₂ → ℝ) :
    E (prodW P Q) f = E P (fun x => E Q (fun y => f (x, y))) := by
  simp only [E, prodW, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

lemma Pr_prodW {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂] (P : Ω₁ → ℝ) (Q : Ω₂ → ℝ)
    (A : Ω₁ × Ω₂ → Prop) :
    Pr (prodW P Q) A = E P (fun x => Pr Q (fun y => A (x, y))) := by
  rw [Pr_eq_E, E_prodW]
  refine Finset.sum_congr rfl fun x _ => ?_
  dsimp only
  rw [Pr_eq_E]

lemma Pr_prodW_fst {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂] {P : Ω₁ → ℝ} {Q : Ω₂ → ℝ}
    (hQ : IsProb Q) (A : Ω₁ → Prop) :
    Pr (prodW P Q) (fun x => A x.1) = Pr P A := by
  classical
  rw [Pr_prodW]
  calc E P (fun x => Pr Q (fun _ => A x))
      = E P (fun x => if A x then 1 else 0) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          dsimp only
          congr 1
          by_cases h : A x
          · simp [Pr, h, hQ.sum_eq_one]
          · simp [Pr, h]
    _ = Pr P A := (Pr_eq_E P A).symm

lemma Pr_prodW_snd {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂] {P : Ω₁ → ℝ} {Q : Ω₂ → ℝ}
    (hP : IsProb P) (B : Ω₂ → Prop) :
    Pr (prodW P Q) (fun x => B x.2) = Pr Q B := by
  rw [Pr_prodW]
  simpa using E_const hP (Pr Q B)

lemma Pr_prodW_and {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂] (P : Ω₁ → ℝ) (Q : Ω₂ → ℝ)
    (A : Ω₁ → Prop) (B : Ω₂ → Prop) :
    Pr (prodW P Q) (fun x => A x.1 ∧ B x.2) = Pr P A * Pr Q B := by
  classical
  rw [Pr_prodW]
  calc E P (fun x => Pr Q (fun y => A x ∧ B y))
      = E P (fun x => (if A x then 1 else 0) * Pr Q B) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          dsimp only
          congr 1
          by_cases h : A x
          · simp [Pr, h]
          · simp [Pr, h]
    _ = E P (fun x => if A x then 1 else 0) * Pr Q B := by
          simp only [E, Finset.sum_mul]
          refine Finset.sum_congr rfl fun x _ => by ring
    _ = Pr P A * Pr Q B := by rw [← Pr_eq_E]

/-- Pi-product weight on `∀ i : ι, α i`. -/
def piW {ι : Type*} [Fintype ι] {α : ι → Type*} (w : ∀ i, α i → ℝ) (x : ∀ i, α i) : ℝ :=
  ∏ i, w i (x i)

lemma isProb_piW {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] {w : ∀ i, α i → ℝ} (hw : ∀ i, IsProb (w i)) :
    IsProb (piW w) where
  nonneg x := Finset.prod_nonneg fun i _ => (hw i).nonneg (x i)
  sum_eq_one := by
    simp only [piW]
    rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one fun i _ => (hw i).sum_eq_one

/-- Splitting a dependent function `∀ i : ι, α i` along a finset `S : Finset ι`. -/
def splitPiEquiv {ι : Type*} [DecidableEq ι] {α : ι → Type*} (S : Finset ι) :
    (∀ i : ι, α i) ≃ ((∀ i : {i // i ∈ S}, α i.1) × (∀ i : {i // i ∉ S}, α i.1)) where
  toFun x := (fun i => x i.1, fun i => x i.1)
  invFun p i := if h : i ∈ S then p.1 ⟨i, h⟩ else p.2 ⟨i, h⟩
  left_inv x := by
    funext i
    dsimp only
    split_ifs <;> rfl
  right_inv p := by
    rcases p with ⟨p₁, p₂⟩
    ext ⟨i, hi⟩
    · simp [hi]
    · simp [hi]

lemma piW_split {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    (w : ∀ i, α i → ℝ) (S : Finset ι) (x : ∀ i, α i) :
    piW w x = prodW (piW (fun i : {i // i ∈ S} => w i.1))
      (piW (fun i : {i // i ∉ S} => w i.1)) (splitPiEquiv S x) := by
  simp only [piW, prodW, splitPiEquiv, Equiv.coe_fn_mk]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => i ∈ S)]
  congr 1
  · refine Finset.prod_bij (fun i hi => ⟨i, (Finset.mem_filter.mp hi).2⟩) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro i₁ _ i₂ _ h; exact congr_arg Subtype.val h
    · intro ⟨i, hi⟩ _; exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩
    · intro _ _; rfl
  · refine Finset.prod_bij (fun i hi => ⟨i, (Finset.mem_filter.mp hi).2⟩) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro i₁ _ i₂ _ h; exact congr_arg Subtype.val h
    · intro ⟨i, hi⟩ _; exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩
    · intro _ _; rfl

lemma E_piW_split {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (w : ∀ i, α i → ℝ) (S : Finset ι) (f : (∀ i, α i) → ℝ) :
    E (piW w) f =
      E (piW (fun i : {i // i ∈ S} => w i.1)) fun x₁ =>
        E (piW (fun i : {i // i ∉ S} => w i.1)) fun x₂ =>
          f ((splitPiEquiv S).symm (x₁, x₂)) := by
  have hprod := E_prodW (piW (fun i : {i // i ∈ S} => w i.1))
    (piW (fun i : {i // i ∉ S} => w i.1)) (fun p => f ((splitPiEquiv S).symm p))
  rw [← hprod]
  have h := E_equiv (splitPiEquiv S)
    (prodW (piW (fun i : {i // i ∈ S} => w i.1)) (piW (fun i : {i // i ∉ S} => w i.1)))
    (fun p => f ((splitPiEquiv S).symm p))
  simp only [Equiv.symm_apply_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [piW_split w S x]

lemma Pr_piW_split {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (w : ∀ i, α i → ℝ) (S : Finset ι) (A : (∀ i, α i) → Prop) :
    Pr (piW w) A =
      E (piW (fun i : {i // i ∈ S} => w i.1)) fun x₁ =>
        Pr (piW (fun i : {i // i ∉ S} => w i.1)) fun x₂ =>
          A ((splitPiEquiv S).symm (x₁, x₂)) := by
  rw [Pr_eq_E, E_piW_split]
  refine Finset.sum_congr rfl fun x₁ _ => ?_
  dsimp only
  rw [Pr_eq_E]

lemma E_piW_depends_on {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] {w : ∀ i, α i → ℝ} (hw : ∀ i, IsProb (w i))
    (S : Finset ι) (f : (∀ i : {i // i ∈ S}, α i.1) → ℝ) :
    E (piW w) (fun x => f (fun i => x i.1)) =
      E (piW (fun i : {i // i ∈ S} => w i.1)) f := by
  rw [E_piW_split w S]
  have hQ : IsProb (piW (fun i : {i // i ∉ S} => w i.1)) := isProb_piW (fun i => hw i.1)
  refine Finset.sum_congr rfl fun x₁ _ => ?_
  dsimp only
  congr 1
  have hconst : (fun x₂ : ∀ i : {i // i ∉ S}, α i.1 =>
      f (fun i => (splitPiEquiv S).symm (x₁, x₂) i.1)) = fun _ => f x₁ := by
    funext x₂
    congr 1
    funext ⟨i, hi⟩
    simp [splitPiEquiv, hi]
  rw [hconst, E_const hQ]

lemma Pr_piW_depends_on {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] {w : ∀ i, α i → ℝ} (hw : ∀ i, IsProb (w i))
    (S : Finset ι) (A : (∀ i : {i // i ∈ S}, α i.1) → Prop) :
    Pr (piW w) (fun x => A (fun i => x i.1)) =
      Pr (piW (fun i : {i // i ∈ S} => w i.1)) A := by
  rw [Pr_eq_E, Pr_eq_E]
  exact E_piW_depends_on hw S (fun x₁ => by classical exact if A x₁ then 1 else 0)

lemma E_piW_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (w : ∀ i, α i → ℝ) (g : ∀ i, α i → ℝ) :
    E (piW w) (fun x => ∏ i, g i (x i)) = ∏ i, E (w i) (g i) := by
  simp only [E, piW]
  calc ∑ x : ∀ i, α i, (∏ i, w i (x i)) * (∏ i, g i (x i))
      = ∑ x : ∀ i, α i, ∏ i, (w i (x i) * g i (x i)) := by
          refine Finset.sum_congr rfl fun x _ => (Finset.prod_mul_distrib).symm
    _ = ∏ i, ∑ a : α i, w i a * g i a := (Fintype.prod_sum (fun i a => w i a * g i a)).symm

/-- Pushforward of a `piW` measure along coordinatewise maps `φ i : α i → β i`. -/
lemma E_piW_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α β : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (w : ∀ i, α i → ℝ) (φ : ∀ i, α i → β i) (v : ∀ i, β i → ℝ)
    (hv : ∀ i b, ∑ a ∈ Finset.univ.filter (fun a => φ i a = b), w i a = v i b)
    (f : (∀ i, β i) → ℝ) :
    E (piW w) (fun x => f (fun i => φ i (x i))) = E (piW v) f := by
  simp only [E, piW]
  have hfiber : ∀ y : ∀ i, β i,
      ∑ x ∈ Finset.univ.filter (fun x : ∀ i, α i => (fun i => φ i (x i)) = y),
        (∏ i, w i (x i)) = ∏ i, v i (y i) := by
    intro y
    have h1 : (∑ x ∈ Finset.univ.filter (fun x : ∀ i, α i => (fun i => φ i (x i)) = y),
        ∏ i, w i (x i)) =
        ∑ x : ∀ i, α i, ∏ i, (if φ i (x i) = y i then w i (x i) else 0) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hxy : (fun i => φ i (x i)) = y
      · rw [if_pos hxy]
        refine Finset.prod_congr rfl fun i _ => ?_
        have hi : φ i (x i) = y i := congr_fun hxy i
        rw [if_pos hi]
      · rw [if_neg hxy]
        have hex : ∃ i, φ i (x i) ≠ y i := by
          by_contra hall
          push Not at hall
          exact hxy (funext hall)
        obtain ⟨i, hi⟩ := hex
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
    rw [h1, ← Fintype.prod_sum (fun i a => if φ i a = y i then w i a else 0)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.sum_filter]
    exact hv i (y i)
  calc ∑ x : ∀ i, α i, (∏ i, w i (x i)) * f (fun i => φ i (x i))
      = ∑ y : ∀ i, β i,
          ∑ x ∈ Finset.univ.filter (fun x : ∀ i, α i => (fun i => φ i (x i)) = y),
            (∏ i, w i (x i)) * f (fun i => φ i (x i)) := by
          rw [← Finset.sum_fiberwise_of_maps_to (g := fun x i => φ i (x i))
            (fun _ _ => Finset.mem_univ _)]
    _ = ∑ y : ∀ i, β i, (∏ i, v i (y i)) * f y := by
          refine Finset.sum_congr rfl fun y _ => ?_
          have h2 : ∑ x ∈ Finset.univ.filter (fun x : ∀ i, α i => (fun i => φ i (x i)) = y),
              (∏ i, w i (x i)) * f (fun i => φ i (x i)) =
              (∑ x ∈ Finset.univ.filter (fun x : ∀ i, α i => (fun i => φ i (x i)) = y),
                ∏ i, w i (x i)) * f y := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun x hx => ?_
            rw [(Finset.mem_filter.mp hx).2]
          rw [h2, hfiber y]

lemma Pr_piW_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α β : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (w : ∀ i, α i → ℝ) (φ : ∀ i, α i → β i) (v : ∀ i, β i → ℝ)
    (hv : ∀ i b, ∑ a ∈ Finset.univ.filter (fun a => φ i a = b), w i a = v i b)
    (A : (∀ i, β i) → Prop) :
    Pr (piW w) (fun x => A (fun i => φ i (x i))) = Pr (piW v) A := by
  rw [Pr_eq_E, Pr_eq_E]
  exact E_piW_map w φ v hv (fun y => by classical exact if A y then 1 else 0)

end ProductProb

section BernoulliAndUniform

/-- Single Bernoulli(p) weight on Bool. -/
def bern1 (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

lemma isProb_bern1 {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : IsProb (bern1 p) where
  nonneg b := by cases b <;> simp [bern1] <;> linarith
  sum_eq_one := by simp [bern1]

/-- i.i.d. Bernoulli(p) weight on `ι → Bool`. -/
def bernW (ι : Type*) [Fintype ι] (p : ℝ) : (ι → Bool) → ℝ :=
  piW (fun _ : ι => bern1 p)

lemma isProb_bernW {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : IsProb (bernW ι p) :=
  isProb_piW (fun _ => isProb_bern1 hp0 hp1)

lemma Pr_bernW_all_true {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset ι) :
    Pr (bernW ι p) (fun x => ∀ i ∈ S, x i = true) = p ^ S.card := by
  have hdep := Pr_piW_depends_on (w := fun _ : ι => bern1 p) (fun _ => isProb_bern1 hp0 hp1) S
    (fun y => ∀ i : {i // i ∈ S}, y i = true)
  have heq : (fun x : ι → Bool => ∀ i ∈ S, x i = true) =
      (fun x : ι → Bool => ∀ i : {i // i ∈ S}, x i.1 = true) := by
    funext x
    exact propext ⟨fun h ⟨i, hi⟩ => h i hi, fun h i hi => h ⟨i, hi⟩⟩
  rw [heq]
  unfold bernW
  rw [hdep, Pr_eq_E]
  trans (E (piW (fun _ : {i // i ∈ S} => bern1 p))
      (fun y => ∏ i : {i // i ∈ S}, if y i = true then (1 : ℝ) else 0))
  · refine Finset.sum_congr rfl fun y _ => ?_
    dsimp only
    congr 1
    classical
    by_cases hy : ∀ i, y i = true
    · rw [if_pos hy]
      symm
      exact Finset.prod_eq_one fun i _ => if_pos (hy i)
    · rw [if_neg hy]
      push Not at hy
      obtain ⟨i, hi⟩ := hy
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  · rw [E_piW_prod (g := fun _ b => if b = true then (1 : ℝ) else 0)]
    have h1 : E (bern1 p) (fun b => if b = true then (1 : ℝ) else 0) = p := by
      simp [E, bern1]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe, h1]

/-- Elementary binomial upper tail via union bound over `t`-subsets. -/
lemma bernW_upper_tail {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset ι) (t : ℕ) :
    Pr (bernW ι p) (fun x => t ≤ (S.filter (fun i => x i = true)).card) ≤
      (S.card.choose t : ℝ) * p ^ t := by
  have hP := isProb_bernW (ι := ι) hp0 hp1
  have himp : ∀ x : ι → Bool, t ≤ (S.filter (fun i => x i = true)).card →
      ∃ T ∈ S.powersetCard t, ∀ i ∈ T, x i = true := by
    intro x hx
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hx
    refine ⟨T, Finset.mem_powersetCard.mpr ⟨hTsub.trans (Finset.filter_subset _ _), hTcard⟩, ?_⟩
    intro i hi
    exact (Finset.mem_filter.mp (hTsub hi)).2
  calc Pr (bernW ι p) (fun x => t ≤ (S.filter (fun i => x i = true)).card)
      ≤ Pr (bernW ι p) (fun x => ∃ T ∈ S.powersetCard t, ∀ i ∈ T, x i = true) :=
          Pr_mono hP himp
    _ ≤ ∑ T ∈ S.powersetCard t, Pr (bernW ι p) (fun x => ∀ i ∈ T, x i = true) :=
          Pr_exists_le hP _ _
    _ = ∑ T ∈ S.powersetCard t, p ^ t := by
          refine Finset.sum_congr rfl fun T hT => ?_
          rw [Pr_bernW_all_true hp0 hp1 T, (Finset.mem_powersetCard.mp hT).2]
    _ = (S.card.choose t : ℝ) * p ^ t := by
          simp [Finset.card_powersetCard]

/-- Elementary exponential upper bound: `exp x ≤ 1 + x + x^2` for `0 ≤ x ≤ 1`. -/
lemma exp_le_one_add_add_sq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.exp_bound (x := x) (n := 2) (by rw [abs_of_nonneg hx0]; exact hx1) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
    pow_zero, pow_one, div_one, zero_add] at h
  have habs := (abs_le.mp h).2
  have hx2 : |x| ^ 2 = x ^ 2 := by rw [abs_of_nonneg hx0]
  rw [hx2] at habs
  have hnum : (3 : ℝ) / (2 * 2) ≤ 1 := by norm_num
  have hsq : 0 ≤ x ^ 2 := sq_nonneg x
  nlinarith

/-- Elementary exponential upper bound for negative arguments: `exp (-x) ≤ 1 - x + x^2 / 2` for `x ≥ 0`. -/
lemma exp_neg_le_one_sub_add_half_sq {x : ℝ} (hx0 : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  let g : ℝ → ℝ := fun t => 1 - t + t ^ 2 / 2 - Real.exp (-t)
  have hmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact ((continuous_const.sub continuous_id).add ((continuous_pow 2).div_const 2)).sub
        (Real.continuous_exp.comp continuous_neg) |>.continuousOn
    · exact ((differentiable_const _).sub differentiable_id).add
        ((differentiable_pow 2).div_const 2) |>.sub
        (Real.differentiable_exp.comp differentiable_neg) |>.differentiableOn
    · intro t ht
      have ht0 : 0 ≤ t := le_of_lt (by simpa [interior_Ici] using ht)
      have hderiv : HasDerivAt g (-1 + t + Real.exp (-t)) t := by
        have ha : HasDerivAt (fun s : ℝ => (1 : ℝ) - s) (-1) t := by
          simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
        have hb : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
          have h := (hasDerivAt_pow 2 t).div_const (2 : ℝ)
          have hval : ((2 : ℕ) : ℝ) * t ^ (2 - 1) / 2 = t := by norm_num
          rwa [hval] at h
        have h1 : HasDerivAt (fun s : ℝ => 1 - s + s ^ 2 / 2) (-1 + t) t := ha.add hb
        have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
          have := (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
          simpa [Function.comp_def] using this
        have h3 := h1.sub h2
        have hval : -1 + t - -Real.exp (-t) = -1 + t + Real.exp (-t) := by ring
        rw [← hval]
        exact h3
      rw [hderiv.deriv]
      have hlin := Real.add_one_le_exp (-t)
      linarith
  have hg0 : g 0 ≤ g x := hmono (Set.mem_Ici.mpr le_rfl) hx0 hx0
  simp only [g, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    add_zero, neg_zero, Real.exp_zero, sub_self] at hg0
  linarith

/-- MGF of a binomial sum under `bernW`. -/
lemma E_bernW_exp_card {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset ι) (s : ℝ) :
    E (bernW ι p) (fun x => Real.exp (s * ((S.filter (fun i => x i = true)).card : ℝ))) =
      (1 + p * (Real.exp s - 1)) ^ S.card := by
  have hdep := E_piW_depends_on (w := fun _ : ι => bern1 p) (fun _ => isProb_bern1 hp0 hp1) S
    (fun y => Real.exp (s * ((Finset.univ.filter (fun i : {i // i ∈ S} => y i = true)).card : ℝ)))
  have hcard : ∀ x : ι → Bool,
      (S.filter (fun i => x i = true)).card =
        (Finset.univ.filter (fun i : {i // i ∈ S} => x i.1 = true)).card := by
    intro x
    refine Finset.card_bij (fun i hi => ⟨i, (Finset.mem_filter.mp hi).1⟩) ?_ ?_ ?_
    · intro i hi
      simp [(Finset.mem_filter.mp hi).2]
    · intro i₁ _ i₂ _ h
      exact congr_arg Subtype.val h
    · intro ⟨i, hi⟩ h
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, (Finset.mem_filter.mp h).2⟩, rfl⟩
  have hcongr : (fun x : ι → Bool => Real.exp (s * ((S.filter (fun i => x i = true)).card : ℝ))) =
      (fun x => Real.exp (s * ((Finset.univ.filter (fun i : {i // i ∈ S} => x i.1 = true)).card : ℝ))) := by
    funext x; rw [hcard x]
  rw [hcongr]
  unfold bernW
  rw [hdep]
  have hprod : (fun y : {i // i ∈ S} → Bool =>
      Real.exp (s * ((Finset.univ.filter (fun i : {i // i ∈ S} => y i = true)).card : ℝ))) =
      (fun y => ∏ i : {i // i ∈ S}, Real.exp (if y i = true then s else 0)) := by
    funext y
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hprod, E_piW_prod (g := fun _ b => Real.exp (if b = true then s else 0))]
  have h1 : E (bern1 p) (fun b => Real.exp (if b = true then s else 0)) = 1 + p * (Real.exp s - 1) := by
    simp [E, bern1]
    ring
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe, h1]

/-- Two-sided Chernoff bound for Binomial sums under `bernW` (`0 < δ ≤ 1`). -/
lemma bernW_chernoff_two_sided {ι : Type*} [Fintype ι] [DecidableEq ι] {p δ : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (S : Finset ι) :
    Pr (bernW ι p) (fun x =>
      |((S.filter (fun i => x i = true)).card : ℝ) - (S.card : ℝ) * p| ≥
        δ * ((S.card : ℝ) * p)) ≤
      2 * Real.exp (-δ ^ 2 * ((S.card : ℝ) * p) / 4) := by
  have hP := isProb_bernW (ι := ι) hp0 hp1
  set μ : ℝ := (S.card : ℝ) * p with hμ
  have hμ0 : 0 ≤ μ := mul_nonneg (Nat.cast_nonneg _) hp0
  have hsplit : ∀ x : ι → Bool,
      |((S.filter (fun i => x i = true)).card : ℝ) - μ| ≥ δ * μ →
      (1 + δ) * μ ≤ ((S.filter (fun i => x i = true)).card : ℝ) ∨
      -((1 - δ) * μ) ≤ -((S.filter (fun i => x i = true)).card : ℝ) := by
    intro x hx
    rcases le_abs.mp hx with h | h
    · left; linarith
    · right; linarith
  have hupper : Pr (bernW ι p) (fun x =>
      (1 + δ) * μ ≤ ((S.filter (fun i => x i = true)).card : ℝ)) ≤
      Real.exp (-δ ^ 2 * μ / 4) := by
    have hm := exp_markov hP (fun x => ((S.filter (fun i => x i = true)).card : ℝ))
      (s := δ / 2) (t := (1 + δ) * μ) (by linarith)
    rw [E_bernW_exp_card hp0 hp1 S (δ / 2)] at hm
    have hpow : (1 + p * (Real.exp (δ / 2) - 1)) ^ S.card ≤
        Real.exp (μ * (Real.exp (δ / 2) - 1)) := by
      calc (1 + p * (Real.exp (δ / 2) - 1)) ^ S.card
          ≤ (Real.exp (p * (Real.exp (δ / 2) - 1))) ^ S.card := by
              refine pow_le_pow_left₀ ?_ (by linarith [Real.add_one_le_exp (p * (Real.exp (δ / 2) - 1))]) _
              have hexp1 : 1 ≤ Real.exp (δ / 2) := Real.one_le_exp (by linarith)
              nlinarith
        _ = Real.exp (μ * (Real.exp (δ / 2) - 1)) := by
              rw [← Real.exp_nat_mul, hμ]; ring_nf
    have hlin : Real.exp (δ / 2) - 1 ≤ δ / 2 + (δ / 2) ^ 2 := by
      linarith [exp_le_one_add_add_sq (x := δ / 2) (by linarith) (by linarith)]
    calc Pr (bernW ι p) (fun x => (1 + δ) * μ ≤ ((S.filter (fun i => x i = true)).card : ℝ))
        ≤ Real.exp (-(δ / 2) * ((1 + δ) * μ)) * Real.exp (μ * (Real.exp (δ / 2) - 1)) :=
            hm.trans (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le)
      _ = Real.exp (-(δ / 2) * ((1 + δ) * μ) + μ * (Real.exp (δ / 2) - 1)) :=
            (Real.exp_add _ _).symm
      _ ≤ Real.exp (-δ ^ 2 * μ / 4) := by
            apply Real.exp_le_exp.mpr
            nlinarith
  have hlower : Pr (bernW ι p) (fun x =>
      -((1 - δ) * μ) ≤ -((S.filter (fun i => x i = true)).card : ℝ)) ≤
      Real.exp (-δ ^ 2 * μ / 4) := by
    have hm := exp_markov hP (fun x => -((S.filter (fun i => x i = true)).card : ℝ))
      (s := δ / 2) (t := -((1 - δ) * μ)) (by linarith)
    have hneg : (fun x : ι → Bool =>
        Real.exp (δ / 2 * -((S.filter (fun i => x i = true)).card : ℝ))) =
        (fun x => Real.exp (-(δ / 2) * ((S.filter (fun i => x i = true)).card : ℝ))) := by
      funext x; congr 1; ring
    rw [hneg, E_bernW_exp_card hp0 hp1 S (-(δ / 2))] at hm
    have hpow : (1 + p * (Real.exp (-(δ / 2)) - 1)) ^ S.card ≤
        Real.exp (μ * (Real.exp (-(δ / 2)) - 1)) := by
      calc (1 + p * (Real.exp (-(δ / 2)) - 1)) ^ S.card
          ≤ (Real.exp (p * (Real.exp (-(δ / 2)) - 1))) ^ S.card := by
              refine pow_le_pow_left₀ ?_ (by linarith [Real.add_one_le_exp (p * (Real.exp (-(δ / 2)) - 1))]) _
              have hexp0 : 0 < Real.exp (-(δ / 2)) := Real.exp_pos _
              nlinarith
        _ = Real.exp (μ * (Real.exp (-(δ / 2)) - 1)) := by
              rw [← Real.exp_nat_mul, hμ]; ring_nf
    have hlin : Real.exp (-(δ / 2)) - 1 ≤ -(δ / 2) + (δ / 2) ^ 2 / 2 := by
      linarith [exp_neg_le_one_sub_add_half_sq (x := δ / 2) (by linarith)]
    calc Pr (bernW ι p) (fun x => -((1 - δ) * μ) ≤ -((S.filter (fun i => x i = true)).card : ℝ))
        ≤ Real.exp (-(δ / 2) * -((1 - δ) * μ)) * Real.exp (μ * (Real.exp (-(δ / 2)) - 1)) :=
            hm.trans (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le)
      _ = Real.exp (-(δ / 2) * -((1 - δ) * μ) + μ * (Real.exp (-(δ / 2)) - 1)) :=
            (Real.exp_add _ _).symm
      _ ≤ Real.exp (-δ ^ 2 * μ / 4) := by
            apply Real.exp_le_exp.mpr
            nlinarith
  calc Pr (bernW ι p) (fun x => |((S.filter (fun i => x i = true)).card : ℝ) - μ| ≥ δ * μ)
      ≤ Pr (bernW ι p) (fun x =>
          (1 + δ) * μ ≤ ((S.filter (fun i => x i = true)).card : ℝ) ∨
          -((1 - δ) * μ) ≤ -((S.filter (fun i => x i = true)).card : ℝ)) :=
          Pr_mono hP hsplit
    _ ≤ Pr (bernW ι p) (fun x => (1 + δ) * μ ≤ ((S.filter (fun i => x i = true)).card : ℝ)) +
        Pr (bernW ι p) (fun x => -((1 - δ) * μ) ≤ -((S.filter (fun i => x i = true)).card : ℝ)) :=
          Pr_or_le hP _ _
    _ ≤ 2 * Real.exp (-δ ^ 2 * μ / 4) := by linarith

/-- Pushforward of `x (a j) && x (b j)` for pairwise disjoint pairs `(a j, b j)` to `bernW (Fin r) (p^2)`. -/
lemma Pr_bernW_disjoint_and {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (a b : Fin r → ι)
    (_hab : ∀ j, a j ≠ b j)
    (ha_inj : Function.Injective a) (hb_inj : Function.Injective b)
    (hdisj : ∀ j k, a j ≠ b k)
    (A : (Fin r → Bool) → Prop) :
    Pr (bernW ι p) (fun x => A (fun j => x (a j) && x (b j))) =
      Pr (bernW (Fin r) (p ^ 2)) A := by
  let S : Finset ι := Finset.univ.image a ∪ Finset.univ.image b
  have hmemA : ∀ j, a j ∈ S := fun j => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have hmemB : ∀ j, b j ∈ S := fun j => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  -- Build equivalence `Fin r × Bool ≃ {i // i ∈ S}` mapping `(j, false) ↦ a j`, `(j, true) ↦ b j`.
  let e : (Fin r × Bool) ≃ {i // i ∈ S} :=
    Equiv.ofBijective (fun q => if q.2 then ⟨b q.1, hmemB q.1⟩ else ⟨a q.1, hmemA q.1⟩)
      ⟨by
        rintro ⟨j₁, c₁⟩ ⟨j₂, c₂⟩ h
        cases c₁ <;> cases c₂ <;> simp only [Bool.false_eq_true, ↓reduceIte, Subtype.mk.injEq] at h
        · exact Prod.ext (ha_inj h) rfl
        · exact absurd h (hdisj j₁ j₂)
        · exact absurd h.symm (hdisj j₂ j₁)
        · exact Prod.ext (hb_inj h) rfl,
       by
        rintro ⟨i, hi⟩
        rcases Finset.mem_union.mp hi with ha | hb
        · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
          exact ⟨(j, false), rfl⟩
        · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
          exact ⟨(j, true), rfl⟩⟩
  have h1 := Pr_piW_depends_on (w := fun _ : ι => bern1 p) (fun _ => isProb_bern1 hp0 hp1) S
    (fun y => A (fun j => y ⟨a j, hmemA j⟩ && y ⟨b j, hmemB j⟩))
  change Pr (piW (fun _ : ι => bern1 p)) (fun x => A (fun j => x (a j) && x (b j))) = _
  rw [h1]
  -- Reindex `({i // i ∈ S} → Bool)` via `e` and then curry to `(Fin r → Bool × Bool)`.
  let e2 : (Fin r → Bool × Bool) ≃ ({i // i ∈ S} → Bool) :=
    { toFun := fun z i => let q := e.symm i; if q.2 then (z q.1).2 else (z q.1).1
      invFun := fun y j => (y ⟨a j, hmemA j⟩, y ⟨b j, hmemB j⟩)
      left_inv := fun z => by
        funext j
        have ha' : e.symm ⟨a j, hmemA j⟩ = (j, false) := e.symm_apply_eq.mpr rfl
        have hb' : e.symm ⟨b j, hmemB j⟩ = (j, true) := e.symm_apply_eq.mpr rfl
        simp [ha', hb']
      right_inv := fun y => by
        funext i
        dsimp only
        rw [show e.symm i = e.symm i from rfl]
        rcases hq : e.symm i with ⟨j, c⟩
        have hi : e (j, c) = i := (e.symm_apply_eq.mp hq).symm
        cases c
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have : e (j, false) = ⟨a j, hmemA j⟩ := rfl
          rw [← hi, this]
        · simp only [↓reduceIte]
          have : e (j, true) = ⟨b j, hmemB j⟩ := rfl
          rw [← hi, this] }
  rw [← Pr_equiv e2]
  have hwt : (fun z : Fin r → Bool × Bool =>
      piW (fun _ : {i // i ∈ S} => bern1 p) (e2 z)) =
      piW (fun _ : Fin r => fun q : Bool × Bool => bern1 p q.1 * bern1 p q.2) := by
    funext z
    simp only [piW]
    rw [← Fintype.prod_equiv e (fun q => bern1 p (e2 z (e q))) (fun i => bern1 p (e2 z i)) (fun _ => rfl)]
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun j _ => ?_
    have ha' : e.symm (e (j, false)) = (j, false) := e.symm_apply_apply _
    have hb' : e.symm (e (j, true)) = (j, true) := e.symm_apply_apply _
    simp [e2, mul_comm]
  have hpred : (fun z : Fin r → Bool × Bool =>
      A (fun j => e2 z ⟨a j, hmemA j⟩ && e2 z ⟨b j, hmemB j⟩)) =
      (fun z => A (fun j => (z j).1 && (z j).2)) := by
    funext z
    congr 1
    funext j
    have ha' : e.symm ⟨a j, hmemA j⟩ = (j, false) := e.symm_apply_eq.mpr rfl
    have hb' : e.symm ⟨b j, hmemB j⟩ = (j, true) := e.symm_apply_eq.mpr rfl
    simp [e2, ha', hb']
  rw [hwt, hpred]
  unfold bernW
  apply Pr_piW_map (w := fun _ : Fin r => fun q : Bool × Bool => bern1 p q.1 * bern1 p q.2)
    (φ := fun _ q => q.1 && q.2) (v := fun _ => bern1 (p ^ 2))
  intro _ c
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  cases c
  · simp [bern1]; ring
  · simp [bern1]; ring

/-- Uniform distribution on `Fin m`. -/
noncomputable def unif1 (m : ℕ) : Fin m → ℝ := fun _ => 1 / (m : ℝ)

lemma isProb_unif1 {m : ℕ} (hm : 0 < m) : IsProb (unif1 m) where
  nonneg _ := div_nonneg zero_le_one (Nat.cast_nonneg m)
  sum_eq_one := by
    simp only [unif1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    field_simp

/-- i.i.d. uniform weight on `ι → Fin m`. -/
noncomputable def unifW (ι : Type*) [Fintype ι] (m : ℕ) : (ι → Fin m) → ℝ :=
  piW (fun _ : ι => unif1 m)

lemma isProb_unifW {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (hm : 0 < m) :
    IsProb (unifW ι m) :=
  isProb_piW (fun _ => isProb_unif1 hm)

/-- Pushforward of `decide (f i ∈ T)` under `unifW ι m` is `bernW ι (|T| / m)`. -/
lemma Pr_unifW_mem {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (hm : 0 < m)
    (T : Finset (Fin m)) (A : (ι → Bool) → Prop) :
    Pr (unifW ι m) (fun f => A (fun i => decide (f i ∈ T))) =
      Pr (bernW ι ((T.card : ℝ) / (m : ℝ))) A := by
  apply Pr_piW_map (w := fun _ : ι => unif1 m) (φ := fun _ a => decide (a ∈ T))
    (v := fun _ => bern1 ((T.card : ℝ) / (m : ℝ)))
  intro _ b
  have hmR : (m : ℝ) ≠ 0 := by positivity
  cases b
  · have hcard : (Finset.univ.filter (fun a : Fin m => decide (a ∈ T) = false)).card = m - T.card := by
      have hsub : Finset.univ.filter (fun a : Fin m => decide (a ∈ T) = false) = Tᶜ := by
        ext a; simp
      rw [hsub, Finset.card_compl, Fintype.card_fin]
    have hle : T.card ≤ m := by simpa using T.card_le_univ
    simp only [unif1, bern1, Bool.false_eq_true, ↓reduceIte, Finset.sum_const, nsmul_eq_mul, hcard]
    rw [Nat.cast_sub hle]
    field_simp
  · have hcard : (Finset.univ.filter (fun a : Fin m => decide (a ∈ T) = true)).card = T.card := by
      have hsub : Finset.univ.filter (fun a : Fin m => decide (a ∈ T) = true) = T := by
        ext a; simp
      rw [hsub]
    simp only [unif1, bern1, ↓reduceIte, Finset.sum_const, nsmul_eq_mul, hcard]
    field_simp

/-- Pushforward of `decide (f i ∈ T₁ ∧ g i ∈ T₂)` under `prodW (unifW ι m) (unifW ι m)` is `bernW`. -/
lemma Pr_unifW_prod_mem {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (hm : 0 < m)
    (T₁ T₂ : Finset (Fin m)) (A : (ι → Bool) → Prop) :
    Pr (prodW (unifW ι m) (unifW ι m))
      (fun fg => A (fun i => decide (fg.1 i ∈ T₁ ∧ fg.2 i ∈ T₂))) =
      Pr (bernW ι (((T₁.card : ℝ) * (T₂.card : ℝ)) / ((m : ℝ) ^ 2))) A := by
  let e : (ι → Fin m × Fin m) ≃ ((ι → Fin m) × (ι → Fin m)) :=
    { toFun := fun h => (fun i => (h i).1, fun i => (h i).2)
      invFun := fun p i => (p.1 i, p.2 i)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Pr_equiv e]
  have hwt : (fun h : ι → Fin m × Fin m => prodW (unifW ι m) (unifW ι m) (e h)) =
      piW (fun _ : ι => fun p : Fin m × Fin m => unif1 m p.1 * unif1 m p.2) := by
    funext h
    simp [prodW, unifW, piW, e, Finset.prod_mul_distrib]
  have hpred : (fun h : ι → Fin m × Fin m =>
      A (fun i => decide ((e h).1 i ∈ T₁ ∧ (e h).2 i ∈ T₂))) =
      (fun h => A (fun i => decide ((h i).1 ∈ T₁ ∧ (h i).2 ∈ T₂))) := rfl
  rw [hwt, hpred]
  unfold bernW
  apply Pr_piW_map (w := fun _ : ι => fun p : Fin m × Fin m => unif1 m p.1 * unif1 m p.2)
    (φ := fun _ p => decide (p.1 ∈ T₁ ∧ p.2 ∈ T₂))
    (v := fun _ => bern1 (((T₁.card : ℝ) * (T₂.card : ℝ)) / ((m : ℝ) ^ 2)))
  intro _ b
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have hprod : (Finset.univ.filter (fun p : Fin m × Fin m => decide (p.1 ∈ T₁ ∧ p.2 ∈ T₂) = true)).card =
      T₁.card * T₂.card := by
    have heq : Finset.univ.filter (fun p : Fin m × Fin m => decide (p.1 ∈ T₁ ∧ p.2 ∈ T₂) = true) =
        T₁ ×ˢ T₂ := by
      ext ⟨a, c⟩; simp
    rw [heq, Finset.card_product]
  cases b
  · have hcomp : (Finset.univ.filter (fun p : Fin m × Fin m => decide (p.1 ∈ T₁ ∧ p.2 ∈ T₂) = false)).card =
        m * m - T₁.card * T₂.card := by
      have heq : Finset.univ.filter (fun p : Fin m × Fin m => decide (p.1 ∈ T₁ ∧ p.2 ∈ T₂) = false) =
          (T₁ ×ˢ T₂)ᶜ := by
        ext ⟨a, c⟩; simp
      rw [heq, Finset.card_compl, Fintype.card_prod, Fintype.card_fin, Finset.card_product]
    have hle : T₁.card * T₂.card ≤ m * m := by
      have h1 : T₁.card ≤ m := by simpa using T₁.card_le_univ
      have h2 : T₂.card ≤ m := by simpa using T₂.card_le_univ
      exact Nat.mul_le_mul h1 h2
    simp only [unif1, bern1, Bool.false_eq_true, ↓reduceIte, Finset.sum_const, nsmul_eq_mul, hcomp]
    rw [Nat.cast_sub hle, Nat.cast_mul, Nat.cast_mul]
    field_simp
  · simp only [unif1, bern1, ↓reduceIte, Finset.sum_const, nsmul_eq_mul, hprod]
    push_cast
    field_simp

/-- Projection size upper bound under `unifW`:
`Pr(|f(I)| ≤ ℓ) ≤ choose m ℓ * (ℓ / m)^|I|`. -/
lemma Pr_unifW_image_card_le {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (hm : 0 < m)
    (I : Finset ι) {ℓ : ℕ} (hℓm : ℓ ≤ m) :
    Pr (unifW ι m) (fun f => (I.image f).card ≤ ℓ) ≤
      (m.choose ℓ : ℝ) * ((ℓ : ℝ) / (m : ℝ)) ^ I.card := by
  have hP := isProb_unifW (ι := ι) hm
  have himp : ∀ f : ι → Fin m, (I.image f).card ≤ ℓ →
      ∃ S ∈ (Finset.univ : Finset (Fin m)).powersetCard ℓ, ∀ i ∈ I, f i ∈ S := by
    intro f hf
    obtain ⟨S, hsub, hScard⟩ := Finset.exists_superset_card_eq hf (by simpa using hℓm)
    exact ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hScard⟩,
      fun i hi => hsub (Finset.mem_image_of_mem f hi)⟩
  calc Pr (unifW ι m) (fun f => (I.image f).card ≤ ℓ)
      ≤ Pr (unifW ι m) (fun f => ∃ S ∈ (Finset.univ : Finset (Fin m)).powersetCard ℓ,
          ∀ i ∈ I, f i ∈ S) := Pr_mono hP himp
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard ℓ,
          Pr (unifW ι m) (fun f => ∀ i ∈ I, f i ∈ S) := Pr_exists_le hP _ _
    _ = ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard ℓ, ((ℓ : ℝ) / (m : ℝ)) ^ I.card := by
          refine Finset.sum_congr rfl fun S hS => ?_
          have hScard : S.card = ℓ := (Finset.mem_powersetCard.mp hS).2
          have h1 : Pr (unifW ι m) (fun f => ∀ i ∈ I, f i ∈ S) =
              Pr (unifW ι m) (fun f => ∀ i ∈ I, decide (f i ∈ S) = true) :=
            Pr_congr fun f => by simp
          rw [h1, Pr_unifW_mem hm S (fun x => ∀ i ∈ I, x i = true), hScard]
          exact Pr_bernW_all_true (by positivity) (by
            rw [div_le_one (by positivity)]; exact_mod_cast hℓm) I
    _ = (m.choose ℓ : ℝ) * ((ℓ : ℝ) / (m : ℝ)) ^ I.card := by
          simp [Finset.card_powersetCard]

end BernoulliAndUniform

section PredictableBernoulli

/-- Split expectation under `bernW ι p` on a single coordinate `hd : ι`. -/
lemma E_bernW_single_split {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hd : ι) (f : (ι → Bool) → ℝ) :
    E (bernW ι p) f =
      p * E (bernW ι p) (fun x => f (Function.update x hd true)) +
      (1 - p) * E (bernW ι p) (fun x => f (Function.update x hd false)) := by
  let eBool : Bool ≃ ({i // i ∈ ({hd} : Finset ι)} → Bool) :=
    { toFun := fun b _ => b
      invFun := fun g => g ⟨hd, Finset.mem_singleton_self hd⟩
      left_inv := fun _ => rfl
      right_inv := fun g => by
        funext ⟨i, hi⟩
        have hih : i = hd := Finset.mem_singleton.mp hi
        subst hih
        rfl }
  have hwt1 : (fun b : Bool => piW (fun _ : {i // i ∈ ({hd} : Finset ι)} => bern1 p) (eBool b)) =
      bern1 p := by funext b; simp [piW, eBool]
  have hinner : ∀ b : Bool,
      E (piW (fun _ : {i // i ∉ ({hd} : Finset ι)} => bern1 p))
        (fun x₂ => f ((splitPiEquiv (α := fun _ => Bool) {hd}).symm (eBool b, x₂))) =
      E (bernW ι p) (fun x => f (Function.update x hd b)) := by
    intro b
    symm
    unfold bernW
    rw [E_piW_split (fun _ : ι => bern1 p) {hd}]
    have hupd : ∀ (x₁ : {i // i ∈ ({hd} : Finset ι)} → Bool)
        (x₂ : {i // i ∉ ({hd} : Finset ι)} → Bool),
        Function.update ((splitPiEquiv (α := fun _ => Bool) {hd}).symm (x₁, x₂)) hd b =
          (splitPiEquiv (α := fun _ => Bool) {hd}).symm (eBool b, x₂) := by
      intro x₁ x₂
      funext i
      by_cases hi : i = hd
      · subst hi; simp [Function.update, splitPiEquiv, eBool]
      · simp [Function.update, hi, splitPiEquiv]
    simp_rw [hupd]
    exact E_const (isProb_piW (fun _ => isProb_bern1 hp0 hp1)) _
  unfold bernW
  rw [E_piW_split (fun _ : ι => bern1 p) {hd}, ← E_equiv eBool, hwt1]
  have hEbool : ∀ g : Bool → ℝ, E (bern1 p) g = p * g true + (1 - p) * g false := by
    intro g; simp [E, bern1]
  rw [hEbool, hinner true, hinner false]
  rfl

/-- Active count along a list `L` where bit equals `c`. -/
def actCount {ι : Type*} (L : List ι) (act : ℕ → (ι → Bool) → Bool) (c : Bool) (x : ι → Bool) : ℕ :=
  (Finset.univ.filter (fun k : Fin L.length => act k.1 x = true ∧ x (L[k.1]) = c)).card

/-- All active true bits along `L` belong to `A`. -/
def allActiveIn {ι : Type*} (L : List ι) (A : Finset ι) (act : ℕ → (ι → Bool) → Bool)
    (x : ι → Bool) : Prop :=
  ∀ k (hk : k < L.length), act k x = true → x (L[k]) = true → L[k] ∈ A

/-- Weighted score for predictable sequential binomial sampling. -/
noncomputable def predScore {ι : Type*} (L : List ι) (A : Finset ι)
    (act : ℕ → (ι → Bool) → Bool) (p : ℝ) (u M : ℕ) (x : ι → Bool) : ℝ :=
  by classical exact
    if allActiveIn L A act x ∧ actCount L act true x = u
    then (1 - p) ^ (M - actCount L act false x)
    else 0

/-- Weighted predictable sequential binomial sampling bound:
for any `Nodup` list `L` of coordinates in `ι`, fixed `A : Finset ι`, and predictable `act`,
`E[predScore L A act p u M] ≤ (|A ∩ L|.choose u) * p^u * (1 - p)^M`. -/
lemma predictable_bern_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ (L : List ι), L.Nodup →
    ∀ (A : Finset ι) (act : ℕ → (ι → Bool) → Bool),
      (∀ k (x y : ι → Bool), (∀ i ∈ L.take k, x i = y i) → act k x = act k y) →
      ∀ (u M : ℕ),
      E (bernW ι p) (predScore L A act p u M) ≤
        ((A.filter (· ∈ L)).card.choose u : ℝ) * p ^ u * (1 - p) ^ M := by
  intro L
  induction L with
  | nil =>
    intro _ A act _ u M
    have hP := isProb_bernW (ι := ι) hp0 hp1
    cases u with
    | zero =>
      have h : predScore ([] : List ι) A act p 0 M = fun _ => (1 - p) ^ M := by
        funext x; simp [predScore, allActiveIn, actCount]
      rw [h, E_const hP]; simp
    | succ u' =>
      have h : predScore ([] : List ι) A act p (u' + 1) M = fun _ => 0 := by
        funext x; simp [predScore, allActiveIn, actCount]
      rw [h, E_const hP]; positivity
  | cons hd tl ih =>
    intro hnodup A act hpred u M
    rw [List.nodup_cons] at hnodup
    obtain ⟨hd_not_mem, htl_nodup⟩ := hnodup
    rw [E_bernW_single_split hp0 hp1 hd]
    let x0 : ι → Bool := fun _ => false
    have hact0 : ∀ x : ι → Bool, act 0 x = act 0 x0 := fun x => hpred 0 x x0 (by simp)
    let act' (b : Bool) (k : ℕ) (x : ι → Bool) : Bool := act (k + 1) (Function.update x hd b)
    have hpred' : ∀ b k (x y : ι → Bool), (∀ i ∈ tl.take k, x i = y i) → act' b k x = act' b k y := by
      intro b k x y hxy
      apply hpred (k + 1)
      intro i hi
      simp only [List.take_succ_cons, List.mem_cons] at hi
      rcases hi with rfl | hi
      · simp
      · by_cases hih : i = hd
        · subst hih; simp
        · simp [Function.update, hih, hxy i hi]
    have htl_upd : ∀ (b : Bool) (x : ι → Bool) (k : ℕ) (hk : k < tl.length),
        Function.update x hd b (tl[k]) = x (tl[k]) := by
      intro b x k hk
      have hne : tl[k] ≠ hd := fun h => hd_not_mem (h ▸ List.getElem_mem hk)
      simp [Function.update, hne]
    have hcnt : ∀ (b c : Bool) (x : ι → Bool),
        actCount (hd :: tl) act c (Function.update x hd b) =
        (if act 0 x0 = true ∧ b = c then 1 else 0) + actCount tl (act' b) c x := by
      intro b c x
      simp only [actCount, Finset.card_filter]
      change (∑ k : Fin (tl.length + 1), _) = _
      rw [Fin.sum_univ_succ]
      congr 1
      · change (if act 0 (Function.update x hd b) = true ∧ Function.update x hd b hd = c then 1 else 0) = _
        simp [hact0]
      · refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Fin.val_succ, List.getElem_cons_succ, htl_upd b x k.1 k.2, act']
    have hall : ∀ (b : Bool) (x : ι → Bool),
        allActiveIn (hd :: tl) A act (Function.update x hd b) ↔
        ((act 0 x0 = true → b = true → hd ∈ A) ∧ allActiveIn tl A (act' b) x) := by
      intro b x
      constructor
      · intro h
        refine ⟨fun ha hb => ?_, fun k hk ha hx => ?_⟩
        · have := h 0 (Nat.zero_lt_succ _)
          simp only [hact0, List.getElem_cons_zero, Function.update_self] at this
          exact this ha hb
        · have := h (k + 1) (Nat.succ_lt_succ hk)
          simp only [List.getElem_cons_succ, htl_upd b x k hk] at this
          exact this ha hx
      · rintro ⟨hhead, htail⟩ k hk ha hx
        cases k with
        | zero =>
          simp only [hact0, List.getElem_cons_zero, Function.update_self] at ha hx ⊢
          exact hhead ha hx
        | succ k' =>
          have hk' : k' < tl.length := Nat.lt_of_succ_lt_succ hk
          simp only [List.getElem_cons_succ, htl_upd b x k' hk'] at ha hx ⊢
          exact htail k' hk' ha hx
    have hA_card : (A.filter (· ∈ hd :: tl)).card =
        (if hd ∈ A then 1 else 0) + (A.filter (· ∈ tl)).card := by
      by_cases hhd : hd ∈ A
      · have heq : A.filter (· ∈ hd :: tl) = insert hd (A.filter (· ∈ tl)) := by
          ext i
          simp only [Finset.mem_filter, List.mem_cons, Finset.mem_insert]
          exact ⟨fun ⟨hA, h⟩ => h.elim Or.inl (fun ht => Or.inr ⟨hA, ht⟩),
                 fun h => h.elim (fun he => ⟨he ▸ hhd, Or.inl he⟩) (fun ⟨hA, ht⟩ => ⟨hA, Or.inr ht⟩)⟩
        rw [heq, Finset.card_insert_of_notMem (by simp [hd_not_mem]), if_pos hhd, add_comm]
      · have heq : A.filter (· ∈ hd :: tl) = A.filter (· ∈ tl) := by
          ext i
          simp only [Finset.mem_filter, List.mem_cons]
          exact ⟨fun ⟨hA, h⟩ => ⟨hA, h.resolve_left (fun he => hhd (he ▸ hA))⟩,
                 fun ⟨hA, ht⟩ => ⟨hA, Or.inr ht⟩⟩
        rw [heq, if_neg hhd, zero_add]
    by_cases hact : act 0 x0 = true
    · -- Active at step 0
      have hF_eq : (fun x => predScore (hd :: tl) A act p u M (Function.update x hd false)) =
          predScore tl A (act' false) p u (M - 1) := by
        funext x
        classical
        simp only [predScore, hall false x, hcnt false true x, hcnt false false x,
          hact, Bool.false_eq_true, and_false, ↓reduceIte, zero_add, and_true,
          true_implies, IsEmpty.forall_iff, true_and]
        rw [Nat.sub_add_eq, Nat.sub_right_comm]
      have hF_le : (1 - p) * E (bernW ι p) (fun x => predScore (hd :: tl) A act p u M (Function.update x hd false)) ≤
          ((A.filter (· ∈ tl)).card.choose u : ℝ) * p ^ u * (1 - p) ^ M := by
        rw [hF_eq]
        have h1mp : (1 - p) * (1 - p) ^ (M - 1) ≤ (1 - p) ^ M := by
          cases M with
          | zero => simp; linarith
          | succ M' => rw [Nat.add_sub_cancel, pow_succ']
        calc (1 - p) * E (bernW ι p) (predScore tl A (act' false) p u (M - 1))
            ≤ (1 - p) * (((A.filter (· ∈ tl)).card.choose u : ℝ) * p ^ u * (1 - p) ^ (M - 1)) :=
              mul_le_mul_of_nonneg_left (ih htl_nodup A (act' false) (hpred' false) u (M - 1)) (by linarith)
          _ = ((A.filter (· ∈ tl)).card.choose u : ℝ) * p ^ u * ((1 - p) * (1 - p) ^ (M - 1)) := by ring
          _ ≤ ((A.filter (· ∈ tl)).card.choose u : ℝ) * p ^ u * (1 - p) ^ M :=
              mul_le_mul_of_nonneg_left h1mp (by positivity)
      by_cases hhd : hd ∈ A
      · have hA_succ : (A.filter (· ∈ hd :: tl)).card = (A.filter (· ∈ tl)).card + 1 := by
          rw [hA_card, if_pos hhd, add_comm]
        cases u with
        | zero =>
          have hT_eq : (fun x => predScore (hd :: tl) A act p 0 M (Function.update x hd true)) = fun _ => 0 := by
            funext x
            classical
            simp only [predScore, hcnt true true x, hact, and_self, ↓reduceIte]
            split_ifs with h
            · omega
            · rfl
          rw [hT_eq, E_const (isProb_bernW hp0 hp1), mul_zero, zero_add]
          simpa [hA_succ] using hF_le
        | succ u' =>
          have hT_eq : (fun x => predScore (hd :: tl) A act p (u' + 1) M (Function.update x hd true)) =
              predScore tl A (act' true) p u' M := by
            funext x
            classical
            simp only [predScore, hall true x, hcnt true true x, hcnt true false x,
              hact, and_self, ↓reduceIte, Bool.true_eq_false, and_false, zero_add,
              true_implies, hhd, true_and]
            have hadd : (1 + actCount tl (act' true) true x = u' + 1) ↔
                (actCount tl (act' true) true x = u') := by omega
            simp only [hadd]
          have hT_le : p * E (bernW ι p) (fun x => predScore (hd :: tl) A act p (u' + 1) M (Function.update x hd true)) ≤
              ((A.filter (· ∈ tl)).card.choose u' : ℝ) * p ^ (u' + 1) * (1 - p) ^ M := by
            rw [hT_eq]
            calc p * E (bernW ι p) (predScore tl A (act' true) p u' M)
                ≤ p * (((A.filter (· ∈ tl)).card.choose u' : ℝ) * p ^ u' * (1 - p) ^ M) :=
                  mul_le_mul_of_nonneg_left (ih htl_nodup A (act' true) (hpred' true) u' M) hp0
              _ = ((A.filter (· ∈ tl)).card.choose u' : ℝ) * p ^ (u' + 1) * (1 - p) ^ M := by
                  rw [pow_succ']; ring
          rw [hA_succ, Nat.choose_succ_succ]
          push_cast
          linarith
      · have hT_eq : (fun x => predScore (hd :: tl) A act p u M (Function.update x hd true)) = fun _ => 0 := by
          funext x
          classical
          simp only [predScore, hall true x, hact, true_implies, hhd, false_and, ↓reduceIte]
        have hA_eq : (A.filter (· ∈ hd :: tl)).card = (A.filter (· ∈ tl)).card := by
          rw [hA_card, if_neg hhd, zero_add]
        rw [hT_eq, E_const (isProb_bernW hp0 hp1), mul_zero, zero_add, hA_eq]
        exact hF_le
    · -- Inactive at step 0
      have hEq : ∀ b : Bool,
          (fun x => predScore (hd :: tl) A act p u M (Function.update x hd b)) =
            predScore tl A (act' b) p u M := by
        intro b
        funext x
        classical
        have hactF : act 0 x0 = false := Bool.eq_false_iff.mpr hact
        simp [predScore, hall b x, hcnt b true x, hcnt b false x, hactF]
      have hA_le : (A.filter (· ∈ tl)).card ≤ (A.filter (· ∈ hd :: tl)).card := by omega
      have hchoose_le : ((A.filter (· ∈ tl)).card.choose u : ℝ) ≤
          ((A.filter (· ∈ hd :: tl)).card.choose u : ℝ) := by
        exact_mod_cast Nat.choose_le_choose u hA_le
      rw [hEq true, hEq false]
      have ht := ih htl_nodup A (act' true) (hpred' true) u M
      have hf := ih htl_nodup A (act' false) (hpred' false) u M
      have hnn : 0 ≤ p ^ u * (1 - p) ^ M := mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
      have h1 : p * E (bernW ι p) (predScore tl A (act' true) p u M) +
          (1 - p) * E (bernW ι p) (predScore tl A (act' false) p u M) ≤
          ((A.filter (· ∈ tl)).card.choose u : ℝ) * p ^ u * (1 - p) ^ M := by
        have h1' := mul_le_mul_of_nonneg_left ht hp0
        have h2' := mul_le_mul_of_nonneg_left hf (by linarith : 0 ≤ 1 - p)
        nlinarith
      nlinarith

end PredictableBernoulli

section McDiarmid

/-- Hoeffding's scalar inequality: for `0 ≤ μ ≤ 1` and `h ∈ ℝ`,
`exp (-h * μ) * (1 - μ + μ * exp h) ≤ exp (h^2 / 8)`. -/
lemma hoeffding_scalar {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (h : ℝ) :
    Real.exp (-h * μ) * (1 - μ + μ * Real.exp h) ≤ Real.exp (h ^ 2 / 8) := by
  have hden_pos : ∀ t : ℝ, 0 < 1 - μ + μ * Real.exp t := by
    intro t
    by_cases h1 : μ = 1
    · subst h1; simpa using Real.exp_pos t
    · have : 0 < 1 - μ := by linarith [lt_of_le_of_ne hμ1 h1]
      have : 0 ≤ μ * Real.exp t := mul_nonneg hμ0 (Real.exp_pos t).le
      linarith
  -- Equivalent to `φ(t) := t^2 / 8 + t * μ - log (1 - μ + μ * exp t) ≥ 0`.
  let φ : ℝ → ℝ := fun t => t ^ 2 / 8 + t * μ - Real.log (1 - μ + μ * Real.exp t)
  let φ' : ℝ → ℝ := fun t => t / 4 + μ - μ * Real.exp t / (1 - μ + μ * Real.exp t)
  have hderiv_φ : ∀ t : ℝ, HasDerivAt φ (φ' t) t := by
    intro t
    have ha : HasDerivAt (fun s : ℝ => s ^ 2 / 8) (t / 4) t := by
      have h := (hasDerivAt_pow 2 t).div_const (8 : ℝ)
      have hval : ((2 : ℕ) : ℝ) * t ^ (2 - 1) / 8 = t / 4 := by norm_num; ring
      rwa [hval] at h
    have hb : HasDerivAt (fun s : ℝ => s * μ) μ t := by
      simpa using (hasDerivAt_id t).mul_const μ
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2 / 8 + s * μ) (t / 4 + μ) t := ha.add hb
    have h2 : HasDerivAt (fun s : ℝ => 1 - μ + μ * Real.exp s) (μ * Real.exp t) t :=
      ((Real.hasDerivAt_exp t).const_mul μ).const_add (1 - μ)
    have h3 : HasDerivAt (fun s : ℝ => Real.log (1 - μ + μ * Real.exp s))
        (μ * Real.exp t / (1 - μ + μ * Real.exp t)) t :=
      h2.log (hden_pos t).ne'
    exact h1.sub h3
  have hderiv_φ' : ∀ t : ℝ, HasDerivAt φ'
      (1 / 4 - (μ * Real.exp t / (1 - μ + μ * Real.exp t)) *
        (1 - μ * Real.exp t / (1 - μ + μ * Real.exp t))) t := by
    intro t
    have hpos := hden_pos t
    have h1 : HasDerivAt (fun s : ℝ => s / 4 + μ) (1 / 4) t := by
      simpa using ((hasDerivAt_id t).div_const (4 : ℝ)).add_const μ
    have hnum : HasDerivAt (fun s : ℝ => μ * Real.exp s) (μ * Real.exp t) t :=
      (Real.hasDerivAt_exp t).const_mul μ
    have hden : HasDerivAt (fun s : ℝ => 1 - μ + μ * Real.exp s) (μ * Real.exp t) t :=
      hnum.const_add (1 - μ)
    have hdiv := hnum.div hden hpos.ne'
    have hsub := h1.sub hdiv
    have hval : 1 / 4 - (μ * Real.exp t * (1 - μ + μ * Real.exp t) - μ * Real.exp t * (μ * Real.exp t)) /
        (1 - μ + μ * Real.exp t) ^ 2 =
        1 / 4 - (μ * Real.exp t / (1 - μ + μ * Real.exp t)) *
        (1 - μ * Real.exp t / (1 - μ + μ * Real.exp t)) := by
      field_simp [hpos.ne']
    rw [← hval]
    exact hsub
  have hφ'_mono : Monotone φ' := by
    apply monotone_of_deriv_nonneg (fun t => (hderiv_φ' t).differentiableAt)
    intro t
    rw [(hderiv_φ' t).deriv]
    set θ := μ * Real.exp t / (1 - μ + μ * Real.exp t)
    nlinarith [sq_nonneg (θ - 1 / 2)]
  have hφ'0 : φ' 0 = 0 := by simp [φ']
  have hφ0 : φ 0 = 0 := by simp [φ]
  have hφ_nonneg : 0 ≤ φ h := by
    have hφ_diff : Differentiable ℝ φ := fun t => (hderiv_φ t).differentiableAt
    by_cases hh : 0 ≤ h
    · have hmono : MonotoneOn φ (Set.Ici 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
        · exact hφ_diff.continuous.continuousOn
        · exact fun t _ => (hderiv_φ t).differentiableAt.differentiableWithinAt
        · intro t ht
          have ht0 : 0 ≤ t := le_of_lt (by simpa [interior_Ici] using ht)
          rw [(hderiv_φ t).deriv]
          simpa [hφ'0] using hφ'_mono ht0
      have := hmono (Set.mem_Ici.mpr le_rfl) hh hh
      linarith
    · have hh' : h ≤ 0 := le_of_not_ge hh
      have hanti : AntitoneOn φ (Set.Iic 0) := by
        apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
        · exact hφ_diff.continuous.continuousOn
        · exact fun t _ => (hderiv_φ t).differentiableAt.differentiableWithinAt
        · intro t ht
          have ht0 : t ≤ 0 := le_of_lt (by simpa [interior_Iic] using ht)
          rw [(hderiv_φ t).deriv]
          simpa [hφ'0] using hφ'_mono ht0
      have := hanti hh' (Set.mem_Iic.mpr le_rfl) hh'
      linarith
  have hlog : Real.log (1 - μ + μ * Real.exp h) ≤ h ^ 2 / 8 + h * μ := by
    dsimp only [φ] at hφ_nonneg
    linarith
  calc Real.exp (-h * μ) * (1 - μ + μ * Real.exp h)
      = Real.exp (-h * μ) * Real.exp (Real.log (1 - μ + μ * Real.exp h)) := by
          rw [Real.exp_log (hden_pos h)]
    _ = Real.exp (-h * μ + Real.log (1 - μ + μ * Real.exp h)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (h ^ 2 / 8) := by
          apply Real.exp_le_exp.mpr
          linarith

/-- Hoeffding's Lemma for a bounded finite random variable. -/
lemma hoeffding_mgf {α : Type*} [Fintype α] {w : α → ℝ} (hw : IsProb w)
    (Y : α → ℝ) {c : ℝ} (hc : 0 ≤ c) (hbdd : ∀ a b, Y a - Y b ≤ c) (s : ℝ) :
    E w (fun a => Real.exp (s * (Y a - E w Y))) ≤ Real.exp (s ^ 2 * c ^ 2 / 8) := by
  by_cases hc0 : c = 0
  · subst hc0
    have hconst : ∀ a, Y a = E w Y := by
      intro a
      have hsame : ∀ b, Y b = Y a := fun b => le_antisymm (by linarith [hbdd b a]) (by linarith [hbdd a b])
      have hE : E w Y = Y a := by
        calc E w Y = E w (fun _ => Y a) := by
              refine Finset.sum_congr rfl fun b _ => by rw [hsame b]
          _ = Y a := E_const hw _
      exact hE.symm
    have : (fun a => Real.exp (s * (Y a - E w Y))) = fun _ => 1 := by
      funext a; simp [hconst a]
    rw [this, E_const hw]
    simp
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  have hne : (Finset.univ : Finset α).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hsum := hw.sum_eq_one
    rw [hemp, Finset.sum_empty] at hsum
    linarith
  obtain ⟨a₀, _, hmin⟩ := Finset.exists_min_image Finset.univ Y hne
  let L := Y a₀
  have hY_ge : ∀ a, L ≤ Y a := fun a => hmin a (Finset.mem_univ a)
  have hY_le : ∀ a, Y a ≤ L + c := fun a => by linarith [hbdd a a₀]
  let X : α → ℝ := fun a => (Y a - L) / c
  have hX0 : ∀ a, 0 ≤ X a := fun a => div_nonneg (by linarith [hY_ge a]) hcpos.le
  have hX1 : ∀ a, X a ≤ 1 := fun a => (div_le_one hcpos).mpr (by linarith [hY_le a])
  set μ : ℝ := E w X
  have hμ0 : 0 ≤ μ := E_nonneg hw hX0
  have hμ1 : μ ≤ 1 := by
    calc μ = E w X := rfl
      _ ≤ E w (fun _ => 1) := E_mono hw hX1
      _ = 1 := E_const hw 1
  have hEY : E w Y = L + c * μ := by
    have hYeq : Y = fun a => L + c * X a := by
      funext a; simp only [X]; field_simp [hcpos.ne']; ring
    conv_lhs => rw [hYeq]
    rw [E_add, E_const hw, E_const_mul]
  let h := s * c
  have hconv : ∀ a, Real.exp (h * X a) ≤ 1 - X a + X a * Real.exp h := by
    intro a
    have h1 := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ h)
      (by linarith [hX1 a] : 0 ≤ 1 - X a) (hX0 a) (by ring : (1 - X a) + X a = 1)
    simpa [smul_eq_mul, mul_comm] using h1
  have hexp_eq : ∀ a, Real.exp (s * (Y a - E w Y)) = Real.exp (-h * μ) * Real.exp (h * X a) := by
    intro a
    rw [← Real.exp_add, hEY]
    congr 1
    simp only [h, X]
    field_simp [hcpos.ne']
    ring
  calc E w (fun a => Real.exp (s * (Y a - E w Y)))
      = E w (fun a => Real.exp (-h * μ) * Real.exp (h * X a)) := by
          refine Finset.sum_congr rfl fun a _ => by dsimp only; rw [hexp_eq a]
    _ = Real.exp (-h * μ) * E w (fun a => Real.exp (h * X a)) := E_const_mul _ _ _
    _ ≤ Real.exp (-h * μ) * E w (fun a => 1 - X a + X a * Real.exp h) :=
          mul_le_mul_of_nonneg_left (E_mono hw hconv) (Real.exp_pos _).le
    _ = Real.exp (-h * μ) * (1 - μ + μ * Real.exp h) := by
          congr 1
          rw [E_add, E_sub, E_const hw]
          have : E w (fun a => X a * Real.exp h) = μ * Real.exp h := by
            have h' : (fun a => X a * Real.exp h) = fun a => Real.exp h * X a := by
              funext a; ring
            rw [h', E_const_mul]; ring
          rw [this]
    _ ≤ Real.exp (h ^ 2 / 8) := hoeffding_scalar hμ0 hμ1 h
    _ = Real.exp (s ^ 2 * c ^ 2 / 8) := by congr 1; simp only [h]; ring

/-- McDiarmid MGF bound on homogeneous finite product space `Fin N → α`. -/
lemma mcdiarmid_mgf {α : Type*} [Fintype α] {w : α → ℝ} (hw : IsProb w) :
    ∀ (N : ℕ) (f : (Fin N → α) → ℝ) {c : ℝ}, 0 ≤ c →
    (∀ (x : Fin N → α) (i : Fin N) (a : α), |f x - f (Function.update x i a)| ≤ c) →
    ∀ s : ℝ,
      E (piW (fun _ : Fin N => w)) (fun x => Real.exp (s * (f x - E (piW (fun _ : Fin N => w)) f))) ≤
        Real.exp (s ^ 2 * (N : ℝ) * c ^ 2 / 8) := by
  intro N
  induction N with
  | zero =>
    intro f c _ _ s
    have hP : IsProb (piW (fun _ : Fin 0 => w)) := isProb_piW (fun _ => hw)
    have hconst : ∀ x : Fin 0 → α, f x = E (piW (fun _ : Fin 0 => w)) f := by
      intro x
      have hall : ∀ y : Fin 0 → α, f y = f x := fun y => by
        congr 1; funext i; exact Fin.elim0 i
      calc f x = E (piW (fun _ : Fin 0 => w)) (fun _ => f x) := (E_const hP _).symm
        _ = E (piW (fun _ : Fin 0 => w)) f := by
            refine Finset.sum_congr rfl fun y _ => by rw [hall y]
    have hfun : (fun x : Fin 0 → α =>
        Real.exp (s * (f x - E (piW (fun _ : Fin 0 => w)) f))) = fun _ => 1 := by
      funext x; simp [hconst x]
    rw [hfun, E_const hP]
    simp
  | succ N ih =>
    intro f c hc hdiff s
    -- Equiv `(α × (Fin N → α)) ≃ (Fin (N + 1) → α)` via `Fin.cons`.
    let e : (α × (Fin N → α)) ≃ (Fin (N + 1) → α) :=
      { toFun := fun p => Fin.cons p.1 p.2
        invFun := fun x => (x 0, fun j => x j.succ)
        left_inv := fun ⟨a, x'⟩ => by simp
        right_inv := fun x => by
          funext i
          refine Fin.cases ?_ ?_ i <;> simp }
    have he_wt : (fun p : α × (Fin N → α) => piW (fun _ : Fin (N + 1) => w) (e p)) =
        prodW w (piW (fun _ : Fin N => w)) := by
      funext ⟨a, x'⟩
      simp only [piW, prodW, Fin.prod_univ_succ, e, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ]
    let μ := E (piW (fun _ : Fin (N + 1) => w)) f
    let h : α → ℝ := fun a => E (piW (fun _ : Fin N => w)) (fun x' => f (e (a, x')))
    have hμ_eq : μ = E w h := by
      dsimp only [μ, h]
      rw [← E_equiv e, he_wt, E_prodW]
    -- `h` has bounded oscillation `≤ c`.
    have hh_bdd : ∀ a b : α, h a - h b ≤ c := by
      intro a b
      dsimp only [h]
      rw [← E_sub]
      have hPN : IsProb (piW (fun _ : Fin N => w)) := isProb_piW (fun _ => hw)
      calc E (piW (fun _ : Fin N => w)) (fun x' => f (e (a, x')) - f (e (b, x')))
          ≤ E (piW (fun _ : Fin N => w)) (fun _ => c) := by
            refine E_mono hPN fun x' => ?_
            have hupd : Function.update (e (a, x')) 0 b = e (b, x') := by
              funext i
              refine Fin.cases ?_ ?_ i
              · simp [e]
              · intro j; simp [e]
            have h1 := hdiff (e (a, x')) 0 b
            rw [hupd] at h1
            exact (le_abs_self _).trans h1
        _ = c := E_const hPN c
    -- For each fixed `a : α`, `x' ↦ f (e (a, x'))` has bounded difference `c` on `Fin N → α`.
    have hf_diff : ∀ a : α, ∀ (x' : Fin N → α) (j : Fin N) (b : α),
        |f (e (a, x')) - f (e (a, Function.update x' j b))| ≤ c := by
      intro a x' j b
      have hupd : Function.update (e (a, x')) j.succ b = e (a, Function.update x' j b) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · have hne : (0 : Fin (N + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
          simp [e, hne]
        · intro k
          by_cases hkj : k = j
          · subst hkj; simp [e]
          · simp [e, hkj, Fin.succ_inj]
      rw [← hupd]
      exact hdiff (e (a, x')) j.succ b
    -- Now combine using `E_prodW`!
    rw [← E_equiv e, he_wt, E_prodW]
    calc E w (fun a => E (piW (fun _ : Fin N => w)) (fun x' => Real.exp (s * (f (e (a, x')) - μ))))
        = E w (fun a => Real.exp (s * (h a - μ)) *
            E (piW (fun _ : Fin N => w)) (fun x' => Real.exp (s * (f (e (a, x')) - h a)))) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          dsimp only
          congr 1
          rw [← E_const_mul]
          refine Finset.sum_congr rfl fun x' _ => ?_
          dsimp only
          congr 1
          rw [← Real.exp_add]
          congr 1
          ring
      _ ≤ E w (fun a => Real.exp (s * (h a - μ)) * Real.exp (s ^ 2 * (N : ℝ) * c ^ 2 / 8)) := by
          refine E_mono hw fun a => ?_
          exact mul_le_mul_of_nonneg_left (ih (fun x' => f (e (a, x'))) hc (hf_diff a) s)
            (Real.exp_pos _).le
      _ = Real.exp (s ^ 2 * (N : ℝ) * c ^ 2 / 8) * E w (fun a => Real.exp (s * (h a - E w h))) := by
          rw [← hμ_eq, ← E_const_mul]
          refine Finset.sum_congr rfl fun a _ => by ring
      _ ≤ Real.exp (s ^ 2 * (N : ℝ) * c ^ 2 / 8) * Real.exp (s ^ 2 * c ^ 2 / 8) :=
          mul_le_mul_of_nonneg_left (hoeffding_mgf hw h hc hh_bdd s) (Real.exp_pos _).le
      _ = Real.exp (s ^ 2 * ((N + 1 : ℕ) : ℝ) * c ^ 2 / 8) := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring

/-- McDiarmid's Inequality on `Fin N → α`. -/
lemma mcdiarmid_upper {α : Type*} [Fintype α] {w : α → ℝ} (hw : IsProb w)
    {N : ℕ} (hN : 0 < N) (f : (Fin N → α) → ℝ) {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t)
    (hdiff : ∀ (x : Fin N → α) (i : Fin N) (a : α), |f x - f (Function.update x i a)| ≤ c) :
    Pr (piW (fun _ : Fin N => w))
      (fun x => E (piW (fun _ : Fin N => w)) f + t ≤ f x) ≤
      Real.exp (-2 * t ^ 2 / ((N : ℝ) * c ^ 2)) := by
  have hP : IsProb (piW (fun _ : Fin N => w)) := isProb_piW (fun _ => hw)
  have hNc : 0 < (N : ℝ) * c ^ 2 := by positivity
  let s : ℝ := 4 * t / ((N : ℝ) * c ^ 2)
  have hs0 : 0 ≤ s := by positivity
  have hcongr : Pr (piW (fun _ : Fin N => w))
      (fun x => E (piW (fun _ : Fin N => w)) f + t ≤ f x) =
      Pr (piW (fun _ : Fin N => w))
      (fun x => t ≤ f x - E (piW (fun _ : Fin N => w)) f) :=
    Pr_congr fun x => by constructor <;> intro h <;> linarith
  rw [hcongr]
  calc Pr (piW (fun _ : Fin N => w)) (fun x => t ≤ f x - E (piW (fun _ : Fin N => w)) f)
      ≤ Real.exp (-s * t) * E (piW (fun _ : Fin N => w))
          (fun x => Real.exp (s * (f x - E (piW (fun _ : Fin N => w)) f))) :=
          exp_markov hP _ hs0
    _ ≤ Real.exp (-s * t) * Real.exp (s ^ 2 * (N : ℝ) * c ^ 2 / 8) :=
          mul_le_mul_of_nonneg_left (mcdiarmid_mgf hw N f hc.le hdiff s) (Real.exp_pos _).le
    _ = Real.exp (-s * t + s ^ 2 * (N : ℝ) * c ^ 2 / 8) := (Real.exp_add _ _).symm
    _ = Real.exp (-2 * t ^ 2 / ((N : ℝ) * c ^ 2)) := by
          congr 1
          dsimp only [s]
          field_simp [hNc.ne']
          ring

end McDiarmid

section CombinatorialAlgebra

/-- Standard binomial upper bound: `(n.choose k : ℝ) ≤ (e * n / k)^k` for `1 ≤ k`. -/
lemma choose_le_exp_pow {n k : ℕ} (hk : 1 ≤ k) :
    (n.choose k : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h1 : (n.choose k : ℝ) * (k.factorial : ℝ) ≤ (n : ℝ) ^ k := by
    have hnat : n.choose k * k.factorial ≤ n ^ k := by
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow n k
    exact_mod_cast hnat
  -- `(k : ℝ)^k / k.factorial ≤ exp k = (exp 1)^k`!
  have h2 : (k : ℝ) ^ k / (k.factorial : ℝ) ≤ Real.exp (k : ℝ) := by
    have hterm := Real.sum_le_exp_of_nonneg (Nat.cast_nonneg k) (k + 1)
    have hsingle : (k : ℝ) ^ k / (k.factorial : ℝ) ≤
        ∑ i ∈ Finset.range (k + 1), (k : ℝ) ^ i / (i.factorial : ℝ) :=
      Finset.single_le_sum (f := fun i => (k : ℝ) ^ i / (i.factorial : ℝ))
        (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self k))
    exact hsingle.trans hterm
  have hfac_pos : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h3 : (k : ℝ) ^ k ≤ Real.exp (k : ℝ) * (k.factorial : ℝ) := (div_le_iff₀ hfac_pos).mp h2
  have h4 : Real.exp (k : ℝ) = (Real.exp 1) ^ k := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [h4] at h3
  rw [div_pow, mul_pow, le_div_iff₀ (pow_pos hkpos k)]
  have hmul : (n.choose k : ℝ) * (k.factorial : ℝ) * (Real.exp 1) ^ k ≤
      (n : ℝ) ^ k * (Real.exp 1) ^ k :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  have hmul2 : (n.choose k : ℝ) * (k : ℝ) ^ k ≤
      (n.choose k : ℝ) * ((Real.exp 1) ^ k * (k.factorial : ℝ)) :=
    mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
  nlinarith

/-- Piecewise-quadratic cap function `gCap M A`:
`A^2 / 2` if `A ≤ M`, and `M^2 / 2 + (A - M)^2 / 2` if `A > M`. -/
noncomputable def gCap (M A : ℝ) : ℝ :=
  if A ≤ M then A ^ 2 / 2 else (M ^ 2 + (A - M) ^ 2) / 2

lemma gCap_le_half_sq {M A : ℝ} (hM : 0 ≤ M) : gCap M A ≤ A ^ 2 / 2 := by
  unfold gCap
  split_ifs with h
  · exact le_rfl
  · push Not at h
    nlinarith

lemma gCap_add_le {M A δ : ℝ} (hM : 0 ≤ M) (_hA : 0 ≤ A) (hδ : 0 ≤ δ) :
    gCap M (A + δ) ≤ gCap M A + (A + δ) * δ := by
  unfold gCap
  split_ifs with h1 h2 h2
  · nlinarith
  · push Not at h2; linarith
  · push Not at h1
    have hM_le : M ≤ A + δ := h1.le
    nlinarith [sq_nonneg (M - A)]
  · push Not at h1 h2
    nlinarith

/-- 4-line Sum-of-Squares Cap Inequality:
if `0 ≤ x i ≤ M` for all `i ∈ s` and `A = ∑ i ∈ s, x i ≥ M`, then `∑ i ∈ s, (x i)^2 ≤ M^2 + (A - M)^2`. -/
lemma sum_sq_cap_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hxM : ∀ i ∈ s, x i ≤ M) (hAM : M ≤ ∑ i ∈ s, x i) :
    ∑ i ∈ s, (x i) ^ 2 ≤ M ^ 2 + (∑ i ∈ s, x i - M) ^ 2 := by
  set A := ∑ i ∈ s, x i with hA
  by_cases h2M : 2 * M ≤ A
  · have h1 : ∑ i ∈ s, (x i) ^ 2 ≤ M * A := by
      rw [hA, Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      have := hx0 i hi; have := hxM i hi
      nlinarith
    nlinarith
  · push Not at h2M
    by_cases hs : s.Nonempty
    · obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image s x hs
      set xm := x i₀
      have hxm0 : 0 ≤ xm := hx0 i₀ hi₀
      have hxmM : xm ≤ M := hxM i₀ hi₀
      by_cases hsmall : xm ≤ A - M
      · have h1 : ∑ i ∈ s, (x i) ^ 2 ≤ xm * A := by
          rw [hA, Finset.mul_sum]
          refine Finset.sum_le_sum fun i hi => ?_
          have := hx0 i hi; have := hmax i hi
          nlinarith
        have h2 : xm * A ≤ (A - M) * A := mul_le_mul_of_nonneg_right hsmall (by linarith)
        nlinarith
      · push Not at hsmall
        have hsplit : ∑ i ∈ s, (x i) ^ 2 = xm ^ 2 + ∑ i ∈ s.erase i₀, (x i) ^ 2 := by
          rw [← Finset.add_sum_erase s (fun i => (x i) ^ 2) hi₀]
        have hrest_sum : ∑ i ∈ s.erase i₀, x i = A - xm := by
          have := Finset.add_sum_erase s x hi₀
          linarith
        have hrest_sq : ∑ i ∈ s.erase i₀, (x i) ^ 2 ≤ (A - xm) ^ 2 := by
          rw [← hrest_sum]
          have hsub : ∀ i ∈ s.erase i₀, 0 ≤ x i := fun i hi => hx0 i (Finset.mem_of_mem_erase hi)
          have hle_sum : ∀ i ∈ s.erase i₀, x i ≤ ∑ j ∈ s.erase i₀, x j :=
            fun i hi => Finset.single_le_sum hsub hi
          calc ∑ i ∈ s.erase i₀, (x i) ^ 2
              ≤ ∑ i ∈ s.erase i₀, (x i * ∑ j ∈ s.erase i₀, x j) :=
                Finset.sum_le_sum fun i hi => by
                  have := hsub i hi; have := hle_sum i hi; nlinarith
            _ = (∑ i ∈ s.erase i₀, x i) ^ 2 := by rw [← Finset.sum_mul, sq]
        nlinarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hs
      subst hs
      simp only [Finset.sum_empty] at hA ⊢
      nlinarith

/-- Unified bound: for `0 ≤ x i ≤ (1 + ε₂) * M₀` and `∑ x i ≤ y₀`,
`∑ (x i)^2 / 2 ≤ (1 + ε₂)^2 * gCap M₀ y₀`. -/
lemma sum_half_sq_le_gCap {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℝ) {M₀ ε₂ y₀ : ℝ}
    (hM₀ : 0 ≤ M₀) (hε₂ : 0 ≤ ε₂) (hx0 : ∀ i ∈ s, 0 ≤ x i)
    (hxM : ∀ i ∈ s, x i ≤ (1 + ε₂) * M₀) (hsum : ∑ i ∈ s, x i ≤ y₀) :
    (∑ i ∈ s, (x i) ^ 2) / 2 ≤ (1 + ε₂) ^ 2 * gCap M₀ y₀ := by
  set M := (1 + ε₂) * M₀
  set A := ∑ i ∈ s, x i
  have hA0 : 0 ≤ A := Finset.sum_nonneg hx0
  have hM_nonneg : 0 ≤ M := by positivity
  have h1e_ge1 : 1 ≤ (1 + ε₂) ^ 2 := by nlinarith
  by_cases hAM : A ≤ M
  · have hsq : ∑ i ∈ s, (x i) ^ 2 ≤ A ^ 2 := by
      have hle_sum : ∀ i ∈ s, x i ≤ A := fun i hi => Finset.single_le_sum hx0 hi
      calc ∑ i ∈ s, (x i) ^ 2
          ≤ ∑ i ∈ s, (x i * A) := Finset.sum_le_sum fun i hi => by
              have := hx0 i hi; have := hle_sum i hi; nlinarith
        _ = A ^ 2 := by rw [← Finset.sum_mul, sq]
    unfold gCap
    split_ifs with hy
    · have hAy : A ^ 2 ≤ y₀ ^ 2 := by nlinarith
      nlinarith [sq_nonneg A]
    · push Not at hy
      have hAM2 : A ^ 2 ≤ M ^ 2 := by nlinarith
      have hM2 : M ^ 2 = (1 + ε₂) ^ 2 * M₀ ^ 2 := by dsimp only [M]; ring
      nlinarith [sq_nonneg (y₀ - M₀)]
  · push Not at hAM
    have hcap := sum_sq_cap_le s x hM_nonneg hx0 hxM hAM.le
    have hyM : M₀ < y₀ := by nlinarith
    have hy_not_le : ¬ y₀ ≤ M₀ := not_le.mpr hyM
    unfold gCap
    rw [if_neg hy_not_le]
    have hdiff_le : A - M ≤ y₀ - M₀ := by nlinarith
    have hdiff_sq : (A - M) ^ 2 ≤ (y₀ - M₀) ^ 2 := by nlinarith
    have hM2 : M ^ 2 = (1 + ε₂) ^ 2 * M₀ ^ 2 := by dsimp only [M]; ring
    nlinarith [sq_nonneg (y₀ - M₀)]

end CombinatorialAlgebra

end Erdos1013Prob


namespace Erdos1013Model

open Finset BigOperators SimpleGraph Erdos1013Prob

section GraphModel

/-- Unordered edges of `Fin m`, represented canonically as ordered pairs `(i, j)` with `i < j`. -/
abbrev Pair (m : ℕ) := {e : Fin m × Fin m // e.1 < e.2}

/-- Lexicographic rank of a pair `(i, j)` with `i < j`. -/
def pairRank {m : ℕ} (e : Pair m) : ℕ := e.1.1.val * m + e.1.2.val

lemma pairRank_inj {m : ℕ} {e₁ e₂ : Pair m} (h : pairRank e₁ = pairRank e₂) : e₁ = e₂ := by
  have h1 : e₁.1.2.val < m := e₁.1.2.isLt
  have h2 : e₂.1.2.val < m := e₂.1.2.isLt
  have hfst : e₁.1.1.val = e₂.1.1.val := by
    have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) h1
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : e₁.1.1.val * m + e₁.1.2.val < (e₁.1.1.val + 1) * m := by
        rw [Nat.add_mul, one_mul]; omega
      have : (e₁.1.1.val + 1) * m ≤ e₂.1.1.val * m := Nat.mul_le_mul_right m hlt
      dsimp only [pairRank] at h; omega
    · have : e₂.1.1.val * m + e₂.1.2.val < (e₂.1.1.val + 1) * m := by
        rw [Nat.add_mul, one_mul]; omega
      have : (e₂.1.1.val + 1) * m ≤ e₁.1.1.val * m := Nat.mul_le_mul_right m hgt
      dsimp only [pairRank] at h; omega
  have hsnd : e₁.1.2.val = e₂.1.2.val := by dsimp only [pairRank] at h; rw [hfst] at h; omega
  exact Subtype.ext (Prod.ext (Fin.ext hfst) (Fin.ext hsnd))

lemma pairRank_lt_of_fst_lt {m : ℕ} {e₁ e₂ : Pair m} (h : e₁.1.1 < e₂.1.1) :
    pairRank e₁ < pairRank e₂ := by
  have h1 : e₁.1.2.val < m := e₁.1.2.isLt
  have hlt : e₁.1.1.val + 1 ≤ e₂.1.1.val := h
  have hmul : (e₁.1.1.val + 1) * m ≤ e₂.1.1.val * m := Nat.mul_le_mul_right m hlt
  dsimp only [pairRank]
  rw [Nat.add_mul, one_mul] at hmul
  omega

/-- Canonical `Pair m` for any two distinct vertices `u ≠ v`. -/
def mkEdge {m : ℕ} (u v : Fin m) (h : u ≠ v) : Pair m :=
  if hlt : u < v then ⟨(u, v), hlt⟩
  else ⟨(v, u), lt_of_le_of_ne (not_lt.mp hlt) h.symm⟩

lemma mkEdge_symm {m : ℕ} (u v : Fin m) (h : u ≠ v) :
    mkEdge v u h.symm = mkEdge u v h := by
  unfold mkEdge
  by_cases hlt : u < v
  · have hnot : ¬ v < u := not_lt.mpr hlt.le
    simp [hlt, hnot]
  · have hgt : v < u := lt_of_le_of_ne (not_lt.mp hlt) h.symm
    simp [hlt, hgt]

lemma mkEdge_fst_eq_min {m : ℕ} (u v : Fin m) (h : u ≠ v) :
    (mkEdge u v h).1.1 = min u v := by
  unfold mkEdge
  split_ifs with hlt
  · exact (min_eq_left hlt.le).symm
  · exact (min_eq_right (not_lt.mp hlt)).symm

/-- Decidable adjacency from `g : Pair m → Bool`. -/
def gAdj {m : ℕ} (g : Pair m → Bool) (u v : Fin m) : Bool :=
  if h : u ≠ v then g (mkEdge u v h) else false

lemma gAdj_symm {m : ℕ} (g : Pair m → Bool) (u v : Fin m) : gAdj g u v = gAdj g v u := by
  unfold gAdj
  by_cases h : u ≠ v
  · rw [dif_pos h, dif_pos h.symm, mkEdge_symm]
  · have h' : ¬ v ≠ u := fun hv => h hv.symm
    rw [dif_neg h, dif_neg h']

lemma gAdj_ne_of_true {m : ℕ} {g : Pair m → Bool} {u v : Fin m} (h : gAdj g u v = true) :
    u ≠ v := by
  intro heq; subst heq; simp [gAdj] at h

/-- Red surviving edge predicate in the two-bites construction. -/
def redSurv {n m : ℕ} (πR πB : Fin n → Fin m) (gR gB : Pair m → Bool) (u v : Fin n) : Prop :=
  gAdj gR (πR u) (πR v) = true ∧
  (¬ ∃ r : Fin m, r < min (πR u) (πR v) ∧ gAdj gR r (πR u) = true ∧ gAdj gR r (πR v) = true) ∧
  (¬ ∃ b : Fin m, gAdj gB b (πB u) = true ∧ gAdj gB b (πB v) = true)

/-- Blue surviving edge predicate in the two-bites construction. -/
def blueSurv {n m : ℕ} (πR πB : Fin n → Fin m) (gR gB : Pair m → Bool) (u v : Fin n) : Prop :=
  redSurv πB πR gB gR u v

lemma redSurv_symm {n m : ℕ} (πR πB : Fin n → Fin m) (gR gB : Pair m → Bool) {u v : Fin n}
    (h : redSurv πR πB gR gB u v) : redSurv πR πB gR gB v u := by
  refine ⟨?_, ?_, ?_⟩
  · rw [gAdj_symm]; exact h.1
  · rintro ⟨r, hmin, hr1, hr2⟩
    exact h.2.1 ⟨r, by rwa [min_comm], hr2, hr1⟩
  · rintro ⟨b, hb1, hb2⟩
    exact h.2.2 ⟨b, hb2, hb1⟩

/-- The two-bites triangle-free graph on `Fin n`. -/
def twoBitesGraph {n m : ℕ} (πR πB : Fin n → Fin m) (gR gB : Pair m → Bool) :
    SimpleGraph (Fin n) where
  Adj u v := redSurv πR πB gR gB u v ∨ blueSurv πR πB gR gB u v
  symm := ⟨fun _ _ h => h.elim (fun h1 => Or.inl (redSurv_symm _ _ _ _ h1))
    (fun h2 => Or.inr (redSurv_symm _ _ _ _ h2))⟩
  loopless := ⟨fun _ h => h.elim (fun h1 => by simp [redSurv, gAdj] at h1)
    (fun h2 => by simp [blueSurv, redSurv, gAdj] at h2)⟩

/-- Deterministic triangle-freeness of `twoBitesGraph` (works for ANY `πR, πB`, no injectivity!). -/
lemma twoBitesGraph_cliqueFree_three {n m : ℕ} (πR πB : Fin n → Fin m) (gR gB : Pair m → Bool) :
    (twoBitesGraph πR πB gR gB).CliqueFree 3 := by
  intro s hs
  obtain ⟨hclique, hcard⟩ := hs
  obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := Finset.card_eq_three.mp hcard
  have h1 : (twoBitesGraph πR πB gR gB).Adj u v := hclique (by simp) (by simp) huv
  have h2 : (twoBitesGraph πR πB gR gB).Adj u w := hclique (by simp) (by simp) huw
  have h3 : (twoBitesGraph πR πB gR gB).Adj v w := hclique (by simp) (by simp) hvw
  -- Helper: three mutually red-surviving vertices cannot exist!
  have hmono : ∀ (π₁ π₂ : Fin n → Fin m) (g₁ g₂ : Pair m → Bool),
      redSurv π₁ π₂ g₁ g₂ u v → redSurv π₁ π₂ g₁ g₂ u w → redSurv π₁ π₂ g₁ g₂ v w → False := by
    intro π₁ π₂ g₁ g₂ huv' huw' hvw'
    have hne1 : π₁ u ≠ π₁ v := gAdj_ne_of_true huv'.1
    have hne2 : π₁ u ≠ π₁ w := gAdj_ne_of_true huw'.1
    have hne3 : π₁ v ≠ π₁ w := gAdj_ne_of_true hvw'.1
    rcases lt_or_gt_of_ne hne1 with h_uv | h_vu
    · rcases lt_or_gt_of_ne hne2 with h_uw | h_wu
      · -- `π₁ u < π₁ v` and `π₁ u < π₁ w`, so `π₁ u` deletes `vw`!
        exact hvw'.2.1 ⟨π₁ u, lt_min h_uv h_uw, huv'.1, huw'.1⟩
      · -- `π₁ w < π₁ u < π₁ v`, so `π₁ w` deletes `uv`!
        exact huv'.2.1 ⟨π₁ w, lt_min h_wu (lt_trans h_wu h_uv),
          by rw [gAdj_symm]; exact huw'.1, by rw [gAdj_symm]; exact hvw'.1⟩
    · rcases lt_or_gt_of_ne hne3 with h_vw | h_wv
      · -- `π₁ v < π₁ u` and `π₁ v < π₁ w`, so `π₁ v` deletes `uw`!
        exact huw'.2.1 ⟨π₁ v, lt_min h_vu h_vw, by rw [gAdj_symm]; exact huv'.1, hvw'.1⟩
      · -- `π₁ w < π₁ v < π₁ u`, so `π₁ w` deletes `uv`!
        exact huv'.2.1 ⟨π₁ w, lt_min (lt_trans h_wv h_vu) h_wv,
          by rw [gAdj_symm]; exact huw'.1, by rw [gAdj_symm]; exact hvw'.1⟩
  -- Helper: two edges of one color + one edge of the other color cannot exist!
  have hmix : ∀ (π₁ π₂ : Fin n → Fin m) (g₁ g₂ : Pair m → Bool) (a b c : Fin n),
      redSurv π₁ π₂ g₁ g₂ a b → redSurv π₁ π₂ g₁ g₂ a c → redSurv π₂ π₁ g₂ g₁ b c → False := by
    intro π₁ π₂ g₁ g₂ a b c hab hac hbc
    exact hbc.2.2 ⟨π₁ a, hab.1, hac.1⟩
  rcases h1 with h1r | h1b <;> rcases h2 with h2r | h2b <;> rcases h3 with h3r | h3b
  · exact hmono πR πB gR gB h1r h2r h3r
  · exact hmix πR πB gR gB u v w h1r h2r h3b
  · exact hmix πR πB gR gB v u w (redSurv_symm _ _ _ _ h1r) h3r h2b
  · exact hmix πB πR gB gR w u v (redSurv_symm _ _ _ _ h2b) (redSurv_symm _ _ _ _ h3b) h1r
  · exact hmix πR πB gR gB w u v (redSurv_symm _ _ _ _ h2r) (redSurv_symm _ _ _ _ h3r) h1b
  · exact hmix πB πR gB gR v u w (redSurv_symm _ _ _ _ h1b) h3b h2r
  · exact hmix πB πR gB gR u v w h1b h2b h3r
  · exact hmono πB πR gB gR h1b h2b h3b

end GraphModel

section NeighborhoodsAndWeights

/-- Fiber of `v : Fin m` under `π : Fin n → Fin m`. -/
def fiber {n m : ℕ} (π : Fin n → Fin m) (v : Fin m) : Finset (Fin n) :=
  Finset.univ.filter (fun x => π x = v)

/-- Neighborhood of `v : Fin m` inside `g : Pair m → Bool`. -/
def nbrG {m : ℕ} (g : Pair m → Bool) (v : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun u => gAdj g v u = true)

/-- Common neighborhood of `v, w : Fin m` inside `g : Pair m → Bool`. -/
def codegG {m : ℕ} (g : Pair m → Bool) (v w : Fin m) : Finset (Fin m) :=
  nbrG g v ∩ nbrG g w

/-- Blow-up neighborhood `N_v = {x : Fin n | π x ∈ N(v)}`. -/
def nbrV {n m : ℕ} (π : Fin n → Fin m) (g : Pair m → Bool) (v : Fin m) : Finset (Fin n) :=
  Finset.univ.filter (fun x => gAdj g v (π x) = true)

/-- Intersection `X_v(I) = I ∩ N_v`. -/
def XV {n m : ℕ} (π : Fin n → Fin m) (g : Pair m → Bool) (I : Finset (Fin n)) (v : Fin m) :
    Finset (Fin n) :=
  I.filter (fun x => gAdj g v (π x) = true)

/-- Projected neighborhood `π₂(N_v)` (for `v` of color 1). -/
def projNbr {n m : ℕ} (π₁ π₂ : Fin n → Fin m) (g : Pair m → Bool) (v : Fin m) : Finset (Fin m) :=
  (nbrV π₁ g v).image π₂

lemma nbrV_card_eq_sum_fibers {n m : ℕ} (π : Fin n → Fin m) (g : Pair m → Bool) (v : Fin m) :
    (nbrV π g v).card = ∑ u ∈ nbrG g v, (fiber π u).card := by
  have hdisj : (nbrV π g v) = (nbrG g v).biUnion (fiber π) := by
    ext x
    simp [nbrV, nbrG, fiber]
  rw [hdisj, Finset.card_biUnion]
  intro u₁ _ u₂ _ hne
  dsimp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
  exact hne (hx1.symm.trans hx2)

lemma nbrV_inter_card_eq_sum_fibers {n m : ℕ} (π : Fin n → Fin m) (g : Pair m → Bool)
    (v w : Fin m) :
    (nbrV π g v ∩ nbrV π g w).card = ∑ u ∈ codegG g v w, (fiber π u).card := by
  have hdisj : (nbrV π g v ∩ nbrV π g w) = (codegG g v w).biUnion (fiber π) := by
    ext x
    simp [nbrV, codegG, nbrG, fiber]
  rw [hdisj, Finset.card_biUnion]
  intro u₁ _ u₂ _ hne
  dsimp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
  exact hne (hx1.symm.trans hx2)

/-- Product probability space `((πR, πB), (gR, gB))`. -/
abbrev PiPair (n m : ℕ) := (Fin n → Fin m) × (Fin n → Fin m)
abbrev GPair (m : ℕ) := (Pair m → Bool) × (Pair m → Bool)
abbrev Omega (n m : ℕ) := PiPair n m × GPair m

noncomputable def piPairW (n m : ℕ) : PiPair n m → ℝ :=
  prodW (unifW (Fin n) m) (unifW (Fin n) m)

def gPairW (m : ℕ) (p : ℝ) : GPair m → ℝ :=
  prodW (bernW (Pair m) p) (bernW (Pair m) p)

noncomputable def fullW (n m : ℕ) (p : ℝ) : Omega n m → ℝ :=
  prodW (piPairW n m) (gPairW m p)

lemma isProb_piPairW {n m : ℕ} (hm : 0 < m) : IsProb (piPairW n m) :=
  isProb_prodW (isProb_unifW hm) (isProb_unifW hm)

lemma isProb_gPairW {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : IsProb (gPairW m p) :=
  isProb_prodW (isProb_bernW hp0 hp1) (isProb_bernW hp0 hp1)

lemma isProb_fullW {n m : ℕ} {p : ℝ} (hm : 0 < m) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProb (fullW n m p) :=
  isProb_prodW (isProb_piPairW hm) (isProb_gPairW hp0 hp1)

end NeighborhoodsAndWeights

section Lemma31Concentration

/-- Non-asymptotic fiber concentration under `unifW (Fin n) m`. -/
lemma Pr_not_fiberGood {n m : ℕ} (hm : 0 < m) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    Pr (unifW (Fin n) m) (fun π => ¬ ∀ v : Fin m,
      |((fiber π v).card : ℝ) - (n : ℝ) / (m : ℝ)| < δ * ((n : ℝ) / (m : ℝ))) ≤
      (m : ℝ) * (2 * Real.exp (-δ ^ 2 * ((n : ℝ) / (m : ℝ)) / 4)) := by
  have hP := isProb_unifW (ι := Fin n) hm
  have himp : ∀ π : Fin n → Fin m,
      (¬ ∀ v : Fin m, |((fiber π v).card : ℝ) - (n : ℝ) / (m : ℝ)| < δ * ((n : ℝ) / (m : ℝ))) →
      ∃ v ∈ (Finset.univ : Finset (Fin m)),
        |((fiber π v).card : ℝ) - (n : ℝ) / (m : ℝ)| ≥ δ * ((n : ℝ) / (m : ℝ)) := by
    intro π h
    push Not at h
    obtain ⟨v, hv⟩ := h
    exact ⟨v, Finset.mem_univ v, hv⟩
  have h1m0 : 0 ≤ (1 : ℝ) / (m : ℝ) := by positivity
  have h1m1 : (1 : ℝ) / (m : ℝ) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hm : (0 : ℝ) < m)]
    exact_mod_cast hm
  calc Pr (unifW (Fin n) m) _
      ≤ Pr (unifW (Fin n) m) (fun π => ∃ v ∈ (Finset.univ : Finset (Fin m)),
          |((fiber π v).card : ℝ) - (n : ℝ) / (m : ℝ)| ≥ δ * ((n : ℝ) / (m : ℝ))) :=
        Pr_mono hP himp
    _ ≤ ∑ v ∈ (Finset.univ : Finset (Fin m)),
          Pr (unifW (Fin n) m) (fun π =>
            |((fiber π v).card : ℝ) - (n : ℝ) / (m : ℝ)| ≥ δ * ((n : ℝ) / (m : ℝ))) :=
        Pr_exists_le hP _ _
    _ ≤ ∑ _v ∈ (Finset.univ : Finset (Fin m)),
          2 * Real.exp (-δ ^ 2 * ((n : ℝ) / (m : ℝ)) / 4) := by
        refine Finset.sum_le_sum fun v _ => ?_
        have hcongr : Pr (unifW (Fin n) m) (fun π =>
            |((fiber π v).card : ℝ) - (n : ℝ) / (m : ℝ)| ≥ δ * ((n : ℝ) / (m : ℝ))) =
          Pr (unifW (Fin n) m) (fun π =>
            |((Finset.univ.filter (fun x : Fin n => decide (π x ∈ ({v} : Finset (Fin m))) = true)).card : ℝ) -
              ((Finset.univ : Finset (Fin n)).card : ℝ) * ((({v} : Finset (Fin m)).card : ℝ) / (m : ℝ))| ≥
            δ * (((Finset.univ : Finset (Fin n)).card : ℝ) * ((({v} : Finset (Fin m)).card : ℝ) / (m : ℝ)))) := by
          refine Pr_congr fun π => ?_
          have hf : fiber π v = Finset.univ.filter (fun x : Fin n => decide (π x ∈ ({v} : Finset (Fin m))) = true) := by
            ext x; simp [fiber]
          rw [hf]
          simp [div_eq_mul_inv]
        rw [hcongr, Pr_unifW_mem hm {v} (A := fun x : Fin n → Bool =>
          |((Finset.univ.filter (fun i : Fin n => x i = true)).card : ℝ) -
            ((Finset.univ : Finset (Fin n)).card : ℝ) * ((({v} : Finset (Fin m)).card : ℝ) / (m : ℝ))| ≥
          δ * (((Finset.univ : Finset (Fin n)).card : ℝ) * ((({v} : Finset (Fin m)).card : ℝ) / (m : ℝ))))]
        simpa [div_eq_mul_inv] using bernW_chernoff_two_sided (ι := Fin n) (p := (({v} : Finset (Fin m)).card : ℝ) / (m : ℝ))
          (by simp) (by simpa using h1m1) hδ0 hδ1 Finset.univ
    _ = (m : ℝ) * (2 * Real.exp (-δ ^ 2 * ((n : ℝ) / (m : ℝ)) / 4)) := by simp

/-- Set of pairs incident to a vertex `v : Fin m`. -/
def incidentPairs {m : ℕ} (v : Fin m) : Finset (Pair m) :=
  Finset.univ.filter (fun e : Pair m => e.1.1 = v ∨ e.1.2 = v)

lemma incidentPairs_card {m : ℕ} (v : Fin m) : (incidentPairs v).card = m - 1 := by
  have hbij : (incidentPairs v).card = (Finset.univ.erase v).card := by
    refine Finset.card_bij (fun e he => if e.1.1 = v then e.1.2 else e.1.1) ?_ ?_ ?_
    · intro e he
      have hmem := (Finset.mem_filter.mp he).2
      rw [Finset.mem_erase]
      split_ifs with h1
      · refine ⟨?_, Finset.mem_univ _⟩
        have hlt := e.2
        rw [h1] at hlt
        exact hlt.ne'
      · have h2 : e.1.2 = v := hmem.resolve_left h1
        refine ⟨?_, Finset.mem_univ _⟩
        have hlt := e.2
        rw [h2] at hlt
        exact hlt.ne
    · intro e₁ he₁ e₂ he₂ heq
      have hm1 := (Finset.mem_filter.mp he₁).2
      have hm2 := (Finset.mem_filter.mp he₂).2
      split_ifs at heq with h1 h2 h2
      · exact Subtype.ext (Prod.ext (h1.trans h2.symm) heq)
      · have h2' : e₂.1.2 = v := hm2.resolve_left h2
        have hlt1 : v < e₁.1.2 := h1 ▸ e₁.2
        have hlt2 : e₂.1.1 < v := h2' ▸ e₂.2
        rw [heq] at hlt1
        exact absurd (lt_trans hlt1 hlt2) (lt_irrefl _)
      · have h1' : e₁.1.2 = v := hm1.resolve_left h1
        have hlt1 : e₁.1.1 < v := h1' ▸ e₁.2
        have hlt2 : v < e₂.1.2 := h2 ▸ e₂.2
        rw [heq] at hlt1
        exact absurd (lt_trans hlt1 hlt2) (lt_irrefl _)
      · have h1' : e₁.1.2 = v := hm1.resolve_left h1
        have h2' : e₂.1.2 = v := hm2.resolve_left h2
        exact Subtype.ext (Prod.ext heq (h1'.trans h2'.symm))
    · intro u hu
      have hne : u ≠ v := (Finset.mem_erase.mp hu).1
      refine ⟨mkEdge v u hne.symm, ?_, ?_⟩
      · unfold incidentPairs mkEdge
        split_ifs with hlt <;> simp
      · by_cases hlt : v < u
        · simp [mkEdge, hlt]
        · simp [mkEdge, hlt, hne]
  rw [hbij, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]

lemma nbrG_card_eq_incident_card {m : ℕ} (g : Pair m → Bool) (v : Fin m) :
    (nbrG g v).card = ((incidentPairs v).filter (fun e => g e = true)).card := by
  refine Finset.card_bij (fun u hu => mkEdge v u (gAdj_ne_of_true (Finset.mem_filter.mp hu).2)) ?_ ?_ ?_
  · intro u hu
    have hadj := (Finset.mem_filter.mp hu).2
    have hne : v ≠ u := gAdj_ne_of_true hadj
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · unfold incidentPairs mkEdge
      split_ifs <;> simp
    · simpa [gAdj, hne] using hadj
  · intro u₁ hu₁ u₂ hu₂ heq
    have hne1 : v ≠ u₁ := gAdj_ne_of_true (Finset.mem_filter.mp hu₁).2
    have hne2 : v ≠ u₂ := gAdj_ne_of_true (Finset.mem_filter.mp hu₂).2
    unfold mkEdge at heq
    split_ifs at heq with h1 h2 h2
    · exact congr_arg (fun e : Pair m => e.1.2) heq
    · have hv : v = u₂ := congr_arg (fun e : Pair m => e.1.1) heq
      exact absurd hv hne2
    · have hv : u₁ = v := congr_arg (fun e : Pair m => e.1.1) heq
      exact absurd hv.symm hne1
    · exact congr_arg (fun e : Pair m => e.1.1) heq
  · intro e he
    have hinc := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
    have hge := (Finset.mem_filter.mp he).2
    by_cases h1 : e.1.1 = v
    · have hne : v ≠ e.1.2 := by have := e.2; rw [h1] at this; exact this.ne
      have hmk : mkEdge v e.1.2 hne = e := by
        apply Subtype.ext
        have hlt : v < e.1.2 := h1 ▸ e.2
        simp only [mkEdge, dif_pos hlt]
        exact Prod.ext h1.symm rfl
      refine ⟨e.1.2, ?_, hmk⟩
      rw [nbrG, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      simp [gAdj, hne, hmk, hge]
    · have h2 : e.1.2 = v := hinc.resolve_left h1
      have hlt : e.1.1 < v := h2 ▸ e.2
      have hne : v ≠ e.1.1 := hlt.ne'
      have hmk : mkEdge v e.1.1 hne = e := by
        apply Subtype.ext
        have hnot : ¬ v < e.1.1 := not_lt.mpr hlt.le
        simp only [mkEdge, dif_neg hnot]
        exact Prod.ext rfl h2.symm
      refine ⟨e.1.1, ?_, hmk⟩
      rw [nbrG, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      simp [gAdj, hne, hmk, hge]

/-- Non-asymptotic degree concentration in `G(m, p)`. -/
lemma Pr_not_degGood {m : ℕ} {p δ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    Pr (bernW (Pair m) p) (fun g => ¬ ∀ v : Fin m,
      |((nbrG g v).card : ℝ) - ((m - 1 : ℕ) : ℝ) * p| < δ * (((m - 1 : ℕ) : ℝ) * p)) ≤
      (m : ℝ) * (2 * Real.exp (-δ ^ 2 * (((m - 1 : ℕ) : ℝ) * p) / 4)) := by
  have hP := isProb_bernW (ι := Pair m) hp0 hp1
  have himp : ∀ g : Pair m → Bool,
      (¬ ∀ v : Fin m, |((nbrG g v).card : ℝ) - ((m - 1 : ℕ) : ℝ) * p| < δ * (((m - 1 : ℕ) : ℝ) * p)) →
      ∃ v ∈ (Finset.univ : Finset (Fin m)),
        |((nbrG g v).card : ℝ) - ((m - 1 : ℕ) : ℝ) * p| ≥ δ * (((m - 1 : ℕ) : ℝ) * p) := by
    intro g h; push Not at h; obtain ⟨v, hv⟩ := h; exact ⟨v, Finset.mem_univ v, hv⟩
  calc Pr (bernW (Pair m) p) _
      ≤ Pr (bernW (Pair m) p) (fun g => ∃ v ∈ (Finset.univ : Finset (Fin m)),
          |((nbrG g v).card : ℝ) - ((m - 1 : ℕ) : ℝ) * p| ≥ δ * (((m - 1 : ℕ) : ℝ) * p)) :=
        Pr_mono hP himp
    _ ≤ ∑ v ∈ (Finset.univ : Finset (Fin m)),
          Pr (bernW (Pair m) p) (fun g =>
            |((nbrG g v).card : ℝ) - ((m - 1 : ℕ) : ℝ) * p| ≥ δ * (((m - 1 : ℕ) : ℝ) * p)) :=
        Pr_exists_le hP _ _
    _ ≤ ∑ _v ∈ (Finset.univ : Finset (Fin m)),
          2 * Real.exp (-δ ^ 2 * (((m - 1 : ℕ) : ℝ) * p) / 4) := by
        refine Finset.sum_le_sum fun v _ => ?_
        have hcongr : Pr (bernW (Pair m) p) (fun g =>
            |((nbrG g v).card : ℝ) - ((m - 1 : ℕ) : ℝ) * p| ≥ δ * (((m - 1 : ℕ) : ℝ) * p)) =
          Pr (bernW (Pair m) p) (fun g =>
            |(((incidentPairs v).filter (fun e => g e = true)).card : ℝ) - ((incidentPairs v).card : ℝ) * p| ≥
            δ * (((incidentPairs v).card : ℝ) * p)) := by
          refine Pr_congr fun g => ?_
          rw [nbrG_card_eq_incident_card, incidentPairs_card]
        rw [hcongr]
        simpa [incidentPairs_card] using bernW_chernoff_two_sided hp0 hp1 hδ0 hδ1 (incidentPairs v)
    _ = (m : ℝ) * (2 * Real.exp (-δ ^ 2 * (((m - 1 : ℕ) : ℝ) * p) / 4)) := by simp

/-- Non-asymptotic co-degree upper tail in `G(m, p)`. -/
lemma Pr_not_codegGood {m t : ℕ} (ht : 1 ≤ t) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Pr (bernW (Pair m) p) (fun g => ¬ ∀ v w : Fin m, v ≠ w → (codegG g v w).card < t) ≤
      (m : ℝ) ^ 2 * (Real.exp 1 * (m : ℝ) * p ^ 2 / (t : ℝ)) ^ t := by
  have hP := isProb_bernW (ι := Pair m) hp0 hp1
  have himp : ∀ g : Pair m → Bool,
      (¬ ∀ v w : Fin m, v ≠ w → (codegG g v w).card < t) →
      ∃ vw ∈ (Finset.univ : Finset (Fin m × Fin m)), vw.1 ≠ vw.2 ∧ t ≤ (codegG g vw.1 vw.2).card := by
    intro g h
    push Not at h
    obtain ⟨v, w, hne, hge⟩ := h
    exact ⟨(v, w), Finset.mem_univ _, hne, hge⟩
  have hsingle : ∀ v w : Fin m, v ≠ w →
      Pr (bernW (Pair m) p) (fun g => t ≤ (codegG g v w).card) ≤
        (Real.exp 1 * (m : ℝ) * p ^ 2 / (t : ℝ)) ^ t := by
    intro v w hvw
    let U : Finset (Fin m) := (Finset.univ.erase v).erase w
    let eU : Fin U.card ≃ {u // u ∈ U} := (Fintype.equivFinOfCardEq (Fintype.card_coe U)).symm
    have hne_v : ∀ j : Fin U.card, v ≠ (eU j).1 := fun j =>
      (Finset.mem_erase.mp (Finset.mem_erase.mp (eU j).2).2).1.symm
    have hne_w : ∀ j : Fin U.card, w ≠ (eU j).1 := fun j =>
      (Finset.mem_erase.mp (eU j).2).1.symm
    let a : Fin U.card → Pair m := fun j => mkEdge v (eU j).1 (hne_v j)
    let b : Fin U.card → Pair m := fun j => mkEdge w (eU j).1 (hne_w j)
    have hdisj : ∀ j k : Fin U.card, a j ≠ b k := by
      intro j k heq
      have h1 : v = w ∨ v = (eU k).1 := by
        unfold a b mkEdge at heq
        split_ifs at heq <;>
        · have hfst := congr_arg (fun e : Pair m => e.1.1) heq
          have hsnd := congr_arg (fun e : Pair m => e.1.2) heq
          tauto
      rcases h1 with h1 | h1
      · exact hvw h1
      · exact hne_v k h1
    have ha_inj : Function.Injective a := by
      intro j₁ j₂ heq
      have hu : (eU j₁).1 = (eU j₂).1 := by
        unfold a mkEdge at heq
        split_ifs at heq with h1 h2 h2
        · exact congr_arg (fun e : Pair m => e.1.2) heq
        · exact absurd (congr_arg (fun e : Pair m => e.1.1) heq) (hne_v j₂)
        · exact absurd (congr_arg (fun e : Pair m => e.1.1) heq).symm (hne_v j₁)
        · exact congr_arg (fun e : Pair m => e.1.1) heq
      exact eU.injective (Subtype.ext hu)
    have hb_inj : Function.Injective b := by
      intro j₁ j₂ heq
      have hu : (eU j₁).1 = (eU j₂).1 := by
        unfold b mkEdge at heq
        split_ifs at heq with h1 h2 h2
        · exact congr_arg (fun e : Pair m => e.1.2) heq
        · exact absurd (congr_arg (fun e : Pair m => e.1.1) heq) (hne_w j₂)
        · exact absurd (congr_arg (fun e : Pair m => e.1.1) heq).symm (hne_w j₁)
        · exact congr_arg (fun e : Pair m => e.1.1) heq
      exact eU.injective (Subtype.ext hu)
    have hcard_eq : ∀ g : Pair m → Bool,
        (codegG g v w).card = (Finset.univ.filter (fun j : Fin U.card => (g (a j) && g (b j)) = true)).card := by
      intro g
      refine Finset.card_bij (fun u hu => eU.symm ⟨u, ?_⟩) ?_ ?_ ?_
      · have hmem := Finset.mem_inter.mp hu
        have h1 : v ≠ u := gAdj_ne_of_true (Finset.mem_filter.mp hmem.1).2
        have h2 : w ≠ u := gAdj_ne_of_true (Finset.mem_filter.mp hmem.2).2
        exact Finset.mem_erase.mpr ⟨h2.symm, Finset.mem_erase.mpr ⟨h1.symm, Finset.mem_univ u⟩⟩
      · intro u hu
        have hmem := Finset.mem_inter.mp hu
        have h1 := (Finset.mem_filter.mp hmem.1).2
        have h2 := (Finset.mem_filter.mp hmem.2).2
        have hne1 : v ≠ u := gAdj_ne_of_true h1
        have hne2 : w ≠ u := gAdj_ne_of_true h2
        have huU : u ∈ U := Finset.mem_erase.mpr ⟨hne2.symm, Finset.mem_erase.mpr ⟨hne1.symm, Finset.mem_univ u⟩⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have heq_u : (eU (eU.symm ⟨u, huU⟩)).1 = u := by simp
        have h1' : g (mkEdge v u hne1) = true := by simpa [gAdj, hne1] using h1
        have h2' : g (mkEdge w u hne2) = true := by simpa [gAdj, hne2] using h2
        have hga : g (a (eU.symm ⟨u, huU⟩)) = true := by
          have ha_eq : a (eU.symm ⟨u, huU⟩) = mkEdge v u hne1 := by simp [a]
          rwa [ha_eq]
        have hgb : g (b (eU.symm ⟨u, huU⟩)) = true := by
          have hb_eq : b (eU.symm ⟨u, huU⟩) = mkEdge w u hne2 := by simp [b]
          rwa [hb_eq]
        simp [hga, hgb]
      · intro u₁ _ u₂ _ heq
        have := congr_arg (fun j => (eU j).1) heq
        simpa using this
      · intro j hj
        have hband := (Finset.mem_filter.mp hj).2
        rw [Bool.and_eq_true] at hband
        refine ⟨(eU j).1, ?_, by simp⟩
        rw [codegG, Finset.mem_inter, nbrG, nbrG, Finset.mem_filter, Finset.mem_filter]
        exact ⟨⟨Finset.mem_univ _, by simp [gAdj, hne_v j, a] at *; exact hband.1⟩,
               ⟨Finset.mem_univ _, by simp [gAdj, hne_w j, b] at *; exact hband.2⟩⟩
    have hcongr : Pr (bernW (Pair m) p) (fun g => t ≤ (codegG g v w).card) =
        Pr (bernW (Pair m) p) (fun g => t ≤ (Finset.univ.filter (fun j : Fin U.card => (g (a j) && g (b j)) = true)).card) :=
      Pr_congr fun g => by rw [hcard_eq g]
    rw [hcongr, Pr_bernW_disjoint_and hp0 hp1 a b (fun j => hdisj j j) ha_inj hb_inj hdisj
      (A := fun y : Fin U.card → Bool => t ≤ (Finset.univ.filter (fun j : Fin U.card => y j = true)).card)]
    have hp2_0 : 0 ≤ p ^ 2 := sq_nonneg p
    have hp2_1 : p ^ 2 ≤ 1 := by nlinarith
    have htail := bernW_upper_tail (ι := Fin U.card) hp2_0 hp2_1 Finset.univ t
    have hUle : U.card ≤ m := by simpa using U.card_le_univ
    have hch := choose_le_exp_pow (n := U.card) (k := t) ht
    have hUleR : (U.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast hUle
    have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    calc Pr (bernW (Fin U.card) (p ^ 2)) _
        ≤ (U.card.choose t : ℝ) * (p ^ 2) ^ t := by simpa using htail
      _ ≤ (Real.exp 1 * (U.card : ℝ) / (t : ℝ)) ^ t * (p ^ 2) ^ t :=
          mul_le_mul_of_nonneg_right hch (pow_nonneg hp2_0 t)
      _ = (Real.exp 1 * (U.card : ℝ) * p ^ 2 / (t : ℝ)) ^ t := by rw [← mul_pow]; congr 1; ring
      _ ≤ (Real.exp 1 * (m : ℝ) * p ^ 2 / (t : ℝ)) ^ t := by
          refine pow_le_pow_left₀ (by positivity) ?_ t
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hUleR (Real.exp_pos 1).le) hp2_0) htpos.le
  calc Pr (bernW (Pair m) p) _
      ≤ Pr (bernW (Pair m) p) (fun g => ∃ vw ∈ (Finset.univ : Finset (Fin m × Fin m)),
          vw.1 ≠ vw.2 ∧ t ≤ (codegG g vw.1 vw.2).card) := Pr_mono hP himp
    _ ≤ ∑ vw ∈ (Finset.univ : Finset (Fin m × Fin m)),
          Pr (bernW (Pair m) p) (fun g => vw.1 ≠ vw.2 ∧ t ≤ (codegG g vw.1 vw.2).card) :=
        Pr_exists_le hP _ _
    _ ≤ ∑ _vw ∈ (Finset.univ : Finset (Fin m × Fin m)),
          (Real.exp 1 * (m : ℝ) * p ^ 2 / (t : ℝ)) ^ t := by
        refine Finset.sum_le_sum fun vw _ => ?_
        by_cases hne : vw.1 ≠ vw.2
        · exact (Pr_mono hP fun g hg => hg.2).trans (hsingle vw.1 vw.2 hne)
        · have hfalse : Pr (bernW (Pair m) p) (fun g => vw.1 ≠ vw.2 ∧ t ≤ (codegG g vw.1 vw.2).card) = 0 := by
            rw [Pr_congr (B := fun _ => False) (fun _ => ⟨fun h => hne h.1, False.elim⟩), Pr_false]
          rw [hfalse]
          positivity
    _ = (m : ℝ) ^ 2 * (Real.exp 1 * (m : ℝ) * p ^ 2 / (t : ℝ)) ^ t := by
        simp [sq]

/-- Non-asymptotic cross-color co-degree bound for fixed `(gR, gB)` of max degree `≤ D`. -/
lemma Pr_not_crossGood {n m D t : ℕ} (hm : 0 < m) (ht : 1 ≤ t)
    (gR gB : Pair m → Bool)
    (hDR : ∀ v : Fin m, (nbrG gR v).card ≤ D)
    (hDB : ∀ w : Fin m, (nbrG gB w).card ≤ D) :
    Pr (piPairW n m) (fun π => ¬ ∀ v w : Fin m, (nbrV π.1 gR v ∩ nbrV π.2 gB w).card < t) ≤
      (m : ℝ) ^ 2 * (Real.exp 1 * (n : ℝ) * ((D : ℝ) / (m : ℝ)) ^ 2 / (t : ℝ)) ^ t := by
  have hP := isProb_piPairW (n := n) hm
  have himp : ∀ π : PiPair n m,
      (¬ ∀ v w : Fin m, (nbrV π.1 gR v ∩ nbrV π.2 gB w).card < t) →
      ∃ vw ∈ (Finset.univ : Finset (Fin m × Fin m)), t ≤ (nbrV π.1 gR vw.1 ∩ nbrV π.2 gB vw.2).card := by
    intro π h; push Not at h; obtain ⟨v, w, hge⟩ := h; exact ⟨(v, w), Finset.mem_univ _, hge⟩
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  calc Pr (piPairW n m) _
      ≤ Pr (piPairW n m) (fun π => ∃ vw ∈ (Finset.univ : Finset (Fin m × Fin m)),
          t ≤ (nbrV π.1 gR vw.1 ∩ nbrV π.2 gB vw.2).card) := Pr_mono hP himp
    _ ≤ ∑ vw ∈ (Finset.univ : Finset (Fin m × Fin m)),
          Pr (piPairW n m) (fun π => t ≤ (nbrV π.1 gR vw.1 ∩ nbrV π.2 gB vw.2).card) :=
        Pr_exists_le hP _ _
    _ ≤ ∑ _vw ∈ (Finset.univ : Finset (Fin m × Fin m)),
          (Real.exp 1 * (n : ℝ) * ((D : ℝ) / (m : ℝ)) ^ 2 / (t : ℝ)) ^ t := by
        refine Finset.sum_le_sum fun ⟨v, w⟩ _ => ?_
        have hcongr : Pr (piPairW n m) (fun π => t ≤ (nbrV π.1 gR v ∩ nbrV π.2 gB w).card) =
            Pr (piPairW n m) (fun π => t ≤ (Finset.univ.filter (fun x : Fin n =>
              decide (π.1 x ∈ nbrG gR v ∧ π.2 x ∈ nbrG gB w) = true)).card) := by
          refine Pr_congr fun π => ?_
          have hset : nbrV π.1 gR v ∩ nbrV π.2 gB w =
              Finset.univ.filter (fun x : Fin n => decide (π.1 x ∈ nbrG gR v ∧ π.2 x ∈ nbrG gB w) = true) := by
            ext x; simp [nbrV, nbrG]
          rw [hset]
        rw [hcongr, piPairW, Pr_unifW_prod_mem hm (nbrG gR v) (nbrG gB w)
          (A := fun y : Fin n → Bool => t ≤ (Finset.univ.filter (fun x : Fin n => y x = true)).card)]
        set q := ((nbrG gR v).card : ℝ) * ((nbrG gB w).card : ℝ) / ((m : ℝ) ^ 2)
        have hq0 : 0 ≤ q := by positivity
        have hq1 : q ≤ 1 := by
          rw [div_le_one (pow_pos hmpos 2)]
          have h1 : ((nbrG gR v).card : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by simpa using (nbrG gR v).card_le_univ)
          have h2 : ((nbrG gB w).card : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by simpa using (nbrG gB w).card_le_univ)
          nlinarith
        have hqD : q ≤ ((D : ℝ) / (m : ℝ)) ^ 2 := by
          rw [div_pow]
          refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
          have h1 : ((nbrG gR v).card : ℝ) ≤ (D : ℝ) := by exact_mod_cast hDR v
          have h2 : ((nbrG gB w).card : ℝ) ≤ (D : ℝ) := by exact_mod_cast hDB w
          nlinarith
        have htail := bernW_upper_tail (ι := Fin n) hq0 hq1 Finset.univ t
        have hch := choose_le_exp_pow (n := n) (k := t) ht
        calc Pr (bernW (Fin n) q) _
            ≤ (n.choose t : ℝ) * q ^ t := by simpa using htail
          _ ≤ (Real.exp 1 * (n : ℝ) / (t : ℝ)) ^ t * q ^ t :=
              mul_le_mul_of_nonneg_right hch (pow_nonneg hq0 t)
          _ = (Real.exp 1 * (n : ℝ) * q / (t : ℝ)) ^ t := by rw [← mul_pow]; congr 1; ring
          _ ≤ (Real.exp 1 * (n : ℝ) * ((D : ℝ) / (m : ℝ)) ^ 2 / (t : ℝ)) ^ t := by
              refine pow_le_pow_left₀ (by positivity) ?_ t
              exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hqD (by positivity)) htpos.le
    _ = (m : ℝ) ^ 2 * (Real.exp 1 * (n : ℝ) * ((D : ℝ) / (m : ℝ)) ^ 2 / (t : ℝ)) ^ t := by
        simp [sq]

/-- Non-asymptotic projected co-degree bound for fixed `gR, πR` with `|N_v| ≤ Nmax` and `|N_v ∩ N_w| ≤ Smax`. -/
lemma Pr_not_projCodegGood {n m Nmax Smax t : ℕ} (hm : 0 < m) (ht : 1 ≤ t)
    (gR : Pair m → Bool) (πR : Fin n → Fin m)
    (hN : ∀ v : Fin m, (nbrV πR gR v).card ≤ Nmax)
    (hS : ∀ v w : Fin m, v ≠ w → (nbrV πR gR v ∩ nbrV πR gR w).card ≤ Smax) :
    Pr (unifW (Fin n) m) (fun πB => ¬ ∀ v w : Fin m, v ≠ w →
      (projNbr πR πB gR v ∩ projNbr πR πB gR w).card < Smax + t) ≤
      (m : ℝ) ^ 2 * (Real.exp 1 * (Nmax : ℝ) ^ 2 / ((m : ℝ) * (t : ℝ))) ^ t := by
  have hP := isProb_unifW (ι := Fin n) hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have himp : ∀ πB : Fin n → Fin m,
      (¬ ∀ v w : Fin m, v ≠ w → (projNbr πR πB gR v ∩ projNbr πR πB gR w).card < Smax + t) →
      ∃ vw ∈ (Finset.univ : Finset (Fin m × Fin m)),
        vw.1 ≠ vw.2 ∧ Smax + t ≤ (projNbr πR πB gR vw.1 ∩ projNbr πR πB gR vw.2).card := by
    intro πB h; push Not at h; obtain ⟨v, w, hne, hge⟩ := h; exact ⟨(v, w), Finset.mem_univ _, hne, hge⟩
  have hsingle : ∀ v w : Fin m, v ≠ w →
      Pr (unifW (Fin n) m) (fun πB => Smax + t ≤ (projNbr πR πB gR v ∩ projNbr πR πB gR w).card) ≤
        (Real.exp 1 * (Nmax : ℝ) ^ 2 / ((m : ℝ) * (t : ℝ))) ^ t := by
    intro v w hvw
    let A₁ : Finset (Fin n) := nbrV πR gR v \ nbrV πR gR w
    let A₂ : Finset (Fin n) := nbrV πR gR w \ nbrV πR gR v
    have hcard_bound : ∀ πB : Fin n → Fin m,
        Smax + t ≤ (projNbr πR πB gR v ∩ projNbr πR πB gR w).card →
        t ≤ (A₂.filter (fun y => πB y ∈ A₁.image πB)).card := by
      intro πB hge
      have hsub : projNbr πR πB gR v ∩ projNbr πR πB gR w ⊆
          (nbrV πR gR v ∩ nbrV πR gR w).image πB ∪
          (A₂.filter (fun y => πB y ∈ A₁.image πB)).image πB := by
        intro b hb
        rcases Finset.mem_inter.mp hb with ⟨hbv, hbw⟩
        obtain ⟨x, hxv, rfl⟩ := Finset.mem_image.mp hbv
        obtain ⟨y, hyw, hyb⟩ := Finset.mem_image.mp hbw
        by_cases hxw : x ∈ nbrV πR gR w
        · exact Finset.mem_union_left _ (Finset.mem_image_of_mem πB (Finset.mem_inter.mpr ⟨hxv, hxw⟩))
        · by_cases hyv : y ∈ nbrV πR gR v
          · exact Finset.mem_union_left _
              (hyb ▸ Finset.mem_image_of_mem πB (Finset.mem_inter.mpr ⟨hyv, hyw⟩))
          · refine Finset.mem_union_right _ ?_
            rw [← hyb]
            refine Finset.mem_image_of_mem πB (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hyw, hyv⟩, ?_⟩)
            rw [hyb]
            exact Finset.mem_image_of_mem πB (Finset.mem_sdiff.mpr ⟨hxv, hxw⟩)
      have hc1 : (projNbr πR πB gR v ∩ projNbr πR πB gR w).card ≤
          ((nbrV πR gR v ∩ nbrV πR gR w).image πB).card +
          ((A₂.filter (fun y => πB y ∈ A₁.image πB)).image πB).card :=
        (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have hc2 : ((nbrV πR gR v ∩ nbrV πR gR w).image πB).card ≤ Smax :=
        Finset.card_image_le.trans (hS v w hvw)
      have hc3 : ((A₂.filter (fun y => πB y ∈ A₁.image πB)).image πB).card ≤
          (A₂.filter (fun y => πB y ∈ A₁.image πB)).card := Finset.card_image_le
      omega
    calc Pr (unifW (Fin n) m) (fun πB => Smax + t ≤ (projNbr πR πB gR v ∩ projNbr πR πB gR w).card)
        ≤ Pr (unifW (Fin n) m) (fun πB => t ≤ (A₂.filter (fun y => πB y ∈ A₁.image πB)).card) :=
          Pr_mono hP hcard_bound
      _ = E (piW (fun _ : {x // x ∈ A₁} => unif1 m)) fun π₁ =>
            Pr (piW (fun _ : {x // x ∉ A₁} => unif1 m)) fun π₂ =>
              t ≤ (A₂.filter (fun y =>
                (splitPiEquiv (α := fun _ => Fin m) A₁).symm (π₁, π₂) y ∈
                  A₁.image ((splitPiEquiv (α := fun _ => Fin m) A₁).symm (π₁, π₂)))).card := by
          unfold unifW
          exact Pr_piW_split (fun _ : Fin n => unif1 m) A₁ _
      _ ≤ E (piW (fun _ : {x // x ∈ A₁} => unif1 m)) fun _ =>
            (Real.exp 1 * (Nmax : ℝ) ^ 2 / ((m : ℝ) * (t : ℝ))) ^ t := by
          refine E_mono (isProb_piW (fun _ => isProb_unif1 hm)) fun π₁ => ?_
          let T : Finset (Fin m) := Finset.univ.image π₁
          let A₂' : Finset {x // x ∉ A₁} := Finset.univ.filter (fun y => y.1 ∈ A₂)
          have hT_eq : ∀ π₂ : {x // x ∉ A₁} → Fin m,
              A₁.image ((splitPiEquiv (α := fun _ => Fin m) A₁).symm (π₁, π₂)) = T := by
            intro π₂
            ext b
            simp only [T, Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists]
            constructor
            · rintro ⟨x, hx, rfl⟩
              exact ⟨x, hx, by simp [splitPiEquiv, hx]⟩
            · rintro ⟨x, hx, rfl⟩
              exact ⟨x, hx, by simp [splitPiEquiv, hx]⟩
          have hcard_eq : ∀ π₂ : {x // x ∉ A₁} → Fin m,
              (A₂.filter (fun y => (splitPiEquiv (α := fun _ => Fin m) A₁).symm (π₁, π₂) y ∈ T)).card =
              (A₂'.filter (fun y => decide (π₂ y ∈ T) = true)).card := by
            intro π₂
            refine Finset.card_bij (fun y hy => ⟨y, ?_⟩) ?_ ?_ ?_
            · intro hA1
              exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).2
                (Finset.mem_sdiff.mp hA1).1
            · intro y hy
              have hyA2 := (Finset.mem_filter.mp hy).1
              have hynotA1 : y ∉ A₁ := fun hA1 =>
                (Finset.mem_sdiff.mp hyA2).2 (Finset.mem_sdiff.mp hA1).1
              have hyT := (Finset.mem_filter.mp hy).2
              simp only [splitPiEquiv, Equiv.coe_fn_symm_mk, dif_neg hynotA1] at hyT
              simp [A₂', hyA2, hyT]
            · intro y₁ _ y₂ _ heq; exact congr_arg Subtype.val heq
            · intro ⟨y, hynot⟩ hy
              simp only [A₂', Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hy
              refine ⟨y, Finset.mem_filter.mpr ⟨hy.1, ?_⟩, rfl⟩
              simp [splitPiEquiv, hynot, hy.2]
          have hcongr : Pr (piW (fun _ : {x // x ∉ A₁} => unif1 m)) (fun π₂ =>
              t ≤ (A₂.filter (fun y =>
                (splitPiEquiv (α := fun _ => Fin m) A₁).symm (π₁, π₂) y ∈
                  A₁.image ((splitPiEquiv (α := fun _ => Fin m) A₁).symm (π₁, π₂)))).card) =
            Pr (unifW {x // x ∉ A₁} m) (fun π₂ =>
              t ≤ (A₂'.filter (fun y => decide (π₂ y ∈ T) = true)).card) := by
            refine Pr_congr fun π₂ => ?_
            rw [hT_eq π₂, hcard_eq π₂]
          rw [hcongr, Pr_unifW_mem hm T
            (A := fun y : {x // x ∉ A₁} → Bool => t ≤ (A₂'.filter (fun z => y z = true)).card)]
          have hTle_m : T.card ≤ m := by simpa using T.card_le_univ
          have hq0 : 0 ≤ (T.card : ℝ) / (m : ℝ) := by positivity
          have hq1 : (T.card : ℝ) / (m : ℝ) ≤ 1 := by
            rw [div_le_one hmpos]; exact_mod_cast hTle_m
          have htail := bernW_upper_tail hq0 hq1 A₂' t
          have hch := choose_le_exp_pow (n := A₂'.card) (k := t) ht
          have hTleN : T.card ≤ Nmax := by
            calc T.card ≤ (Finset.univ : Finset {x // x ∈ A₁}).card := Finset.card_image_le
              _ = A₁.card := by simp
              _ ≤ (nbrV πR gR v).card := Finset.card_le_card Finset.sdiff_subset
              _ ≤ Nmax := hN v
          have hA2leN : A₂'.card ≤ Nmax := by
            have hle : A₂'.card ≤ A₂.card := by
              have hcard_eq2 : A₂'.card = A₂.card := by
                refine Finset.card_bij (fun y _ => y.1) ?_ ?_ ?_
                · intro y hy; exact (Finset.mem_filter.mp hy).2
                · intro y₁ _ y₂ _ h; exact Subtype.ext h
                · intro y hy
                  have hnot : y ∉ A₁ := fun hA1 =>
                    (Finset.mem_sdiff.mp hy).2 (Finset.mem_sdiff.mp hA1).1
                  exact ⟨⟨y, hnot⟩, by simp [A₂', hy], rfl⟩
              exact hcard_eq2.le
            exact hle.trans ((Finset.card_le_card Finset.sdiff_subset).trans (hN w))
          have hTleNR : (T.card : ℝ) ≤ (Nmax : ℝ) := by exact_mod_cast hTleN
          have hA2leNR : (A₂'.card : ℝ) ≤ (Nmax : ℝ) := by exact_mod_cast hA2leN
          calc Pr (bernW {x // x ∉ A₁} ((T.card : ℝ) / (m : ℝ))) _
              ≤ (A₂'.card.choose t : ℝ) * ((T.card : ℝ) / (m : ℝ)) ^ t := htail
            _ ≤ (Real.exp 1 * (A₂'.card : ℝ) / (t : ℝ)) ^ t * ((T.card : ℝ) / (m : ℝ)) ^ t :=
                mul_le_mul_of_nonneg_right hch (pow_nonneg hq0 t)
            _ = (Real.exp 1 * ((A₂'.card : ℝ) * (T.card : ℝ)) / ((m : ℝ) * (t : ℝ))) ^ t := by
                rw [← mul_pow]; congr 1; ring
            _ ≤ (Real.exp 1 * (Nmax : ℝ) ^ 2 / ((m : ℝ) * (t : ℝ))) ^ t := by
                refine pow_le_pow_left₀ (by positivity) ?_ t
                refine div_le_div_of_nonneg_right ?_ (by positivity)
                have hmul : (A₂'.card : ℝ) * (T.card : ℝ) ≤ (Nmax : ℝ) ^ 2 := by nlinarith
                exact mul_le_mul_of_nonneg_left hmul (Real.exp_pos 1).le
      _ = (Real.exp 1 * (Nmax : ℝ) ^ 2 / ((m : ℝ) * (t : ℝ))) ^ t :=
          E_const (isProb_piW (fun _ => isProb_unif1 hm)) _
  calc Pr (unifW (Fin n) m) _
      ≤ Pr (unifW (Fin n) m) (fun πB => ∃ vw ∈ (Finset.univ : Finset (Fin m × Fin m)),
          vw.1 ≠ vw.2 ∧ Smax + t ≤ (projNbr πR πB gR vw.1 ∩ projNbr πR πB gR vw.2).card) :=
        Pr_mono hP himp
    _ ≤ ∑ vw ∈ (Finset.univ : Finset (Fin m × Fin m)),
          Pr (unifW (Fin n) m) (fun πB =>
            vw.1 ≠ vw.2 ∧ Smax + t ≤ (projNbr πR πB gR vw.1 ∩ projNbr πR πB gR vw.2).card) :=
        Pr_exists_le hP _ _
    _ ≤ ∑ _vw ∈ (Finset.univ : Finset (Fin m × Fin m)),
          (Real.exp 1 * (Nmax : ℝ) ^ 2 / ((m : ℝ) * (t : ℝ))) ^ t := by
        refine Finset.sum_le_sum fun vw _ => ?_
        by_cases hne : vw.1 ≠ vw.2
        · exact (Pr_mono hP fun πB h => h.2).trans (hsingle vw.1 vw.2 hne)
        · have hfalse : Pr (unifW (Fin n) m) (fun πB =>
              vw.1 ≠ vw.2 ∧ Smax + t ≤ (projNbr πR πB gR vw.1 ∩ projNbr πR πB gR vw.2).card) = 0 := by
            rw [Pr_congr (B := fun _ => False) (fun _ => ⟨fun h => hne h.1, False.elim⟩), Pr_false]
          rw [hfalse]
          positivity
    _ = (m : ℝ) ^ 2 * (Real.exp 1 * (Nmax : ℝ) ^ 2 / ((m : ℝ) * (t : ℝ))) ^ t := by simp [sq]

end Lemma31Concentration

end Erdos1013Model

namespace Erdos1013ClosedPairs

open Finset BigOperators Erdos1013Prob Erdos1013Model

section PairsAndInclusionExclusion

/-- All unordered pairs inside a vertex subset `S : Finset (Fin n)`. -/
def pairsOf {n : ℕ} (S : Finset (Fin n)) : Finset (Pair n) :=
  Finset.univ.filter (fun e : Pair n => e.1.1 ∈ S ∧ e.1.2 ∈ S)

/-- All projected unordered pairs in `Pair m` inside `S.image π`. -/
def projPairs {n m : ℕ} (π : Fin n → Fin m) (S : Finset (Fin n)) : Finset (Pair m) :=
  Finset.univ.filter (fun e : Pair m => e.1.1 ∈ S.image π ∧ e.1.2 ∈ S.image π)

lemma pairsOf_card {n : ℕ} (S : Finset (Fin n)) : (pairsOf S).card = S.card.choose 2 := by
  have h1 : (pairsOf S).card = (S.powersetCard 2).card := by
    refine Finset.card_bij (fun e _ => ({e.1.1, e.1.2} : Finset (Fin n))) ?_ ?_ ?_
    · intro e he
      have hm := (Finset.mem_filter.mp he).2
      rw [Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_pair e.2.ne⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hm.1
      · rw [Finset.mem_singleton.mp hx]; exact hm.2
    · intro e₁ _ e₂ _ heq
      have h1 : e₁.1.1 ∈ ({e₂.1.1, e₂.1.2} : Finset (Fin n)) := heq ▸ by simp
      have h2 : e₁.1.2 ∈ ({e₂.1.1, e₂.1.2} : Finset (Fin n)) := heq ▸ by simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
      have hlt1 := e₁.2; have hlt2 := e₂.2
      apply Subtype.ext; apply Prod.ext
      · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact absurd (h1.trans h2.symm) hlt1.ne
        · exact h1
        · rw [h1, h2] at hlt1; exact absurd (lt_trans hlt1 hlt2) (lt_irrefl _)
        · exact absurd (h1.trans h2.symm) hlt1.ne
      · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact absurd (h1.trans h2.symm) hlt1.ne
        · exact h2
        · rw [h1, h2] at hlt1; exact absurd (lt_trans hlt1 hlt2) (lt_irrefl _)
        · exact absurd (h1.trans h2.symm) hlt1.ne
    · intro t ht
      obtain ⟨htsub, htcard⟩ := Finset.mem_powersetCard.mp ht
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp htcard
      refine ⟨mkEdge x y hxy, ?_, ?_⟩
      · rw [pairsOf, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        unfold mkEdge
        split_ifs
        · exact ⟨htsub (by simp), htsub (by simp)⟩
        · exact ⟨htsub (by simp), htsub (by simp)⟩
      · unfold mkEdge
        split_ifs
        · rfl
        · exact Finset.pair_comm y x
  rw [h1, Finset.card_powersetCard]

lemma projPairs_card {n m : ℕ} (π : Fin n → Fin m) (S : Finset (Fin n)) :
    (projPairs π S).card = (S.image π).card.choose 2 := by
  simpa [projPairs, pairsOf] using pairsOf_card (S.image π)

lemma card_biUnion_projPairs_le_pairsOf {α : Type*} [DecidableEq α] {n m : ℕ}
    (π : Fin n → Fin m) (F : Finset α) (X : α → Finset (Fin n)) :
    (F.biUnion (fun v => projPairs π (X v))).card ≤ (F.biUnion (fun v => pairsOf (X v))).card := by
  classical
  have hex : ∀ e ∈ F.biUnion (fun v => projPairs π (X v)),
      ∃ f ∈ F.biUnion (fun v => pairsOf (X v)),
        ({π f.1.1, π f.1.2} : Finset (Fin m)) = {e.1.1, e.1.2} := by
    intro e he
    obtain ⟨v, hvF, hev⟩ := Finset.mem_biUnion.mp he
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hev).2
    obtain ⟨x, hx, hπx⟩ := Finset.mem_image.mp h1
    obtain ⟨y, hy, hπy⟩ := Finset.mem_image.mp h2
    have hxy : x ≠ y := fun h => e.2.ne (hπx.symm.trans (h ▸ hπy))
    refine ⟨mkEdge x y hxy, Finset.mem_biUnion.mpr ⟨v, hvF, ?_⟩, ?_⟩
    · rw [pairsOf, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      unfold mkEdge; split_ifs <;> exact ⟨‹_›, ‹_›⟩
    · unfold mkEdge
      split_ifs
      · simp [hπx, hπy]
      · simp [hπx, hπy, Finset.pair_comm]
  choose φ hφ_mem hφ_eq using hex
  let S := F.biUnion (fun v => projPairs π (X v))
  let T := F.biUnion (fun v => pairsOf (X v))
  have hinj : Function.Injective (fun e : {e // e ∈ S} => (⟨φ e.1 e.2, hφ_mem e.1 e.2⟩ : {f // f ∈ T})) := by
    intro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ h
    have hfeq : φ e₁ he₁ = φ e₂ he₂ := congr_arg Subtype.val h
    have hset : ({e₁.1.1, e₁.1.2} : Finset (Fin m)) = {e₂.1.1, e₂.1.2} :=
      (hφ_eq e₁ he₁).symm.trans (hfeq ▸ hφ_eq e₂ he₂)
    have h1 : e₁.1.1 ∈ ({e₂.1.1, e₂.1.2} : Finset (Fin m)) := hset ▸ by simp
    have h2 : e₁.1.2 ∈ ({e₂.1.1, e₂.1.2} : Finset (Fin m)) := hset ▸ by simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    have hlt1 := e₁.2; have hlt2 := e₂.2
    apply Subtype.ext; apply Subtype.ext; apply Prod.ext
    · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hlt1.ne
      · exact h1
      · rw [h1, h2] at hlt1; exact absurd (lt_trans hlt1 hlt2) (lt_irrefl _)
      · exact absurd (h1.trans h2.symm) hlt1.ne
    · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hlt1.ne
      · exact h2
      · rw [h1, h2] at hlt1; exact absurd (lt_trans hlt1 hlt2) (lt_irrefl _)
      · exact absurd (h1.trans h2.symm) hlt1.ne
  calc S.card = Fintype.card {e // e ∈ S} := (Fintype.card_coe S).symm
    _ ≤ Fintype.card {f // f ∈ T} := Fintype.card_le_of_injective _ hinj
    _ = T.card := Fintype.card_coe T

/-- Pure-`ℕ` inclusion-exclusion lower bound:
if pairwise intersections of `A v` (`v ∈ s`) have cardinality `≤ C`,
then `∑ v ∈ s, |A v| ≤ |⋃ v ∈ s, A v| + s.card.choose 2 * C`. -/
lemma sum_card_le_card_biUnion_add {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (A : α → Finset β) (C : ℕ)
    (hinter : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → (A u ∩ A v).card ≤ C) :
    ∑ v ∈ s, (A v).card ≤ (s.biUnion A).card + s.card.choose 2 * C := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hsub : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → (A u ∩ A v).card ≤ C := fun u hu v hv =>
      hinter u (Finset.mem_insert_of_mem hu) v (Finset.mem_insert_of_mem hv)
    have hih := ih hsub
    have hunion : (insert a s).biUnion A = A a ∪ s.biUnion A := Finset.biUnion_insert
    have hcap : (A a ∩ s.biUnion A).card ≤ s.card * C := by
      have heq : A a ∩ s.biUnion A = s.biUnion (fun v => A a ∩ A v) := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_biUnion]
        exact ⟨fun ⟨ha', v, hv, hxv⟩ => ⟨v, hv, ha', hxv⟩, fun ⟨v, hv, ha', hxv⟩ => ⟨ha', v, hv, hxv⟩⟩
      rw [heq]
      calc (s.biUnion (fun v => A a ∩ A v)).card
          ≤ ∑ v ∈ s, (A a ∩ A v).card := Finset.card_biUnion_le
        _ ≤ ∑ _v ∈ s, C := Finset.sum_le_sum fun v hv =>
            hinter a (Finset.mem_insert_self a s) v (Finset.mem_insert_of_mem hv) (fun h => ha (h ▸ hv))
        _ = s.card * C := by simp
    have hadd := Finset.card_union_add_card_inter (A a) (s.biUnion A)
    have hchoose : (s.card + 1).choose 2 = s.card.choose 2 + s.card := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
    rw [Finset.sum_insert ha, hunion, Finset.card_insert_of_notMem ha, hchoose, Nat.add_mul]
    omega

lemma choose_two_le_half_mul_bound {a : ℕ} {t : ℝ} (ha : (a : ℝ) ≤ t) :
    (a.choose 2 : ℝ) ≤ (a : ℝ) * t / 2 := by
  have h : (a.choose 2 : ℝ) = (a : ℝ) * ((a : ℝ) - 1) / 2 := by
    rw [Nat.choose_two_right]
    cases a with
    | zero => simp
    | succ a' =>
      have heven : 2 ∣ (a' + 1) * a' := Nat.even_mul_pred_self (a' + 1) |> Even.two_dvd
      have hcast : (((a' + 1) * a' / 2 : ℕ) : ℝ) = ((a' + 1 : ℕ) : ℝ) * (a' : ℝ) / 2 := by
        have hmul := Nat.div_mul_cancel heven
        have hR : (((a' + 1) * a' / 2 : ℕ) : ℝ) * 2 = ((a' + 1 : ℕ) : ℝ) * (a' : ℝ) := by
          exact_mod_cast hmul
        linarith
      simpa [Nat.add_sub_cancel] using hcast
  rw [h]
  nlinarith [Nat.cast_nonneg (α := ℝ) a]

lemma choose_two_le_half_sq (a : ℕ) : (a.choose 2 : ℝ) ≤ (a : ℝ) ^ 2 / 2 := by
  have h := choose_two_le_half_mul_bound (a := a) (t := (a : ℝ)) le_rfl
  simpa [sq] using h

end PairsAndInclusionExclusion

section VertexPartition

/-- Combined red + blue blow-up neighborhood `N_v` for `v : Fin m ⊕ Fin m`. -/
def nbrAll {n m : ℕ} (π : PiPair n m) (g : GPair m) : Fin m ⊕ Fin m → Finset (Fin n)
  | Sum.inl r => nbrV π.1 g.1 r
  | Sum.inr b => nbrV π.2 g.2 b

/-- Combined `X_v(I) = I ∩ N_v` for `v : Fin m ⊕ Fin m`. -/
def XAll {n m : ℕ} (π : PiPair n m) (g : GPair m) (I : Finset (Fin n)) (v : Fin m ⊕ Fin m) :
    Finset (Fin n) :=
  I ∩ nbrAll π g v

lemma XAll_inl {n m : ℕ} (π : PiPair n m) (g : GPair m) (I : Finset (Fin n)) (r : Fin m) :
    XAll π g I (Sum.inl r) = XV π.1 g.1 I r := by
  ext x; simp [XAll, nbrAll, nbrV, XV]

lemma XAll_inr {n m : ℕ} (π : PiPair n m) (g : GPair m) (I : Finset (Fin n)) (b : Fin m) :
    XAll π g I (Sum.inr b) = XV π.2 g.2 I b := by
  ext x; simp [XAll, nbrAll, nbrV, XV]

/-- Partition of `V_R ⊕ V_B` into Huge / Large / Medium / Small vertices for `I`. -/
noncomputable def Hset {n m : ℕ} (π : PiPair n m) (g : GPair m) (I : Finset (Fin n)) (t₁ : ℝ) :
    Finset (Fin m ⊕ Fin m) :=
  by classical exact Finset.univ.filter (fun v => t₁ < ((XAll π g I v).card : ℝ))

noncomputable def Lset {n m : ℕ} (π : PiPair n m) (g : GPair m) (I : Finset (Fin n)) (t₁ t₂ : ℝ) :
    Finset (Fin m ⊕ Fin m) :=
  by classical exact Finset.univ.filter (fun v =>
    t₂ < ((XAll π g I v).card : ℝ) ∧ ((XAll π g I v).card : ℝ) ≤ t₁)

noncomputable def Mset {n m : ℕ} (π : PiPair n m) (g : GPair m) (I : Finset (Fin n)) (t₂ t₃ : ℝ) :
    Finset (Fin m ⊕ Fin m) :=
  by classical exact Finset.univ.filter (fun v =>
    t₃ < ((XAll π g I v).card : ℝ) ∧ ((XAll π g I v).card : ℝ) ≤ t₂)

noncomputable def Sset {n m : ℕ} (π : PiPair n m) (g : GPair m) (I : Finset (Fin n)) (t₃ : ℝ) :
    Finset (Fin m ⊕ Fin m) :=
  by classical exact Finset.univ.filter (fun v => ((XAll π g I v).card : ℝ) ≤ t₃)

lemma mem_LMS_of_not_mem_H {n m : ℕ} (π : PiPair n m) (g : GPair m) (I : Finset (Fin n))
    (t₁ t₂ t₃ : ℝ) (v : Fin m ⊕ Fin m) (hv : v ∉ Hset π g I t₁) :
    v ∈ Lset π g I t₁ t₂ ∨ v ∈ Mset π g I t₂ t₃ ∨ v ∈ Sset π g I t₃ := by
  classical
  simp only [Hset, Lset, Mset, Sset, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hv ⊢
  by_cases h2 : t₂ < ((XAll π g I v).card : ℝ)
  · exact Or.inl ⟨h2, hv⟩
  · push Not at h2
    by_cases h3 : t₃ < ((XAll π g I v).card : ℝ)
    · exact Or.inr (Or.inl ⟨h3, h2⟩)
    · push Not at h3
      exact Or.inr (Or.inr h3)

end VertexPartition

section Lemma32Large

/-- Lemma 3.2 (`lem:large`, deterministic):
given pairwise neighborhood intersection cap `C_int`, if `L_cap * t₂ > k + L_cap.choose 2 * C_int`,
then `|Lset| < L_cap` and `|(⋃_{v ∈ Lset} pairsOf (X_v))| ≤ (t₁ / 2) * (k + L_cap.choose 2 * C_int)`. -/
lemma lem_large_bound {n m k C_int L_cap : ℕ} {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁)
    (π : PiPair n m) (g : GPair m) (I : Finset (Fin n)) (hI : I.card = k)
    (hinter : ∀ u v : Fin m ⊕ Fin m, u ≠ v → (nbrAll π g u ∩ nbrAll π g v).card ≤ C_int)
    (hLcap : (k : ℝ) + ((L_cap.choose 2 * C_int : ℕ) : ℝ) < (L_cap : ℝ) * t₂) :
    (Lset π g I t₁ t₂).card < L_cap ∧
    (((Lset π g I t₁ t₂).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ) ≤
      (t₁ / 2) * ((k : ℝ) + ((L_cap.choose 2 * C_int : ℕ) : ℝ)) := by
  classical
  have hinterX : ∀ u v : Fin m ⊕ Fin m, u ≠ v → (XAll π g I u ∩ XAll π g I v).card ≤ C_int := by
    intro u v huv
    have hsub : XAll π g I u ∩ XAll π g I v ⊆ nbrAll π g u ∩ nbrAll π g v := by
      intro x hx
      simp only [XAll, Finset.mem_inter] at hx ⊢
      exact ⟨hx.1.2, hx.2.2⟩
    exact (Finset.card_le_card hsub).trans (hinter u v huv)
  have hcard_lt : (Lset π g I t₁ t₂).card < L_cap := by
    by_contra hge
    push Not at hge
    obtain ⟨L, hLsub, hLcard⟩ := Finset.exists_subset_card_eq hge
    have hIE := sum_card_le_card_biUnion_add L (XAll π g I) C_int (fun u _ v _ h => hinterX u v h)
    have hbi_le : (L.biUnion (XAll π g I)).card ≤ k := by
      rw [← hI]
      refine Finset.card_le_card ?_
      intro x hx
      obtain ⟨v, _, hxv⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_inter.mp hxv).1
    have hsum_gt : (L_cap : ℝ) * t₂ ≤ ∑ v ∈ L, ((XAll π g I v).card : ℝ) := by
      calc (L_cap : ℝ) * t₂ = ∑ _v ∈ L, t₂ := by rw [Finset.sum_const, nsmul_eq_mul, hLcard]
        _ ≤ ∑ v ∈ L, ((XAll π g I v).card : ℝ) := by
            refine Finset.sum_le_sum fun v hv => ?_
            exact ((Finset.mem_filter.mp (hLsub hv)).2.1).le
    have hIE_R : ∑ v ∈ L, ((XAll π g I v).card : ℝ) ≤ (k : ℝ) + ((L_cap.choose 2 * C_int : ℕ) : ℝ) := by
      rw [hLcard] at hIE
      have h1 : (∑ v ∈ L, (XAll π g I v).card : ℕ) ≤ k + L_cap.choose 2 * C_int := by omega
      exact_mod_cast h1
    linarith
  refine ⟨hcard_lt, ?_⟩
  have hIE := sum_card_le_card_biUnion_add (Lset π g I t₁ t₂) (XAll π g I) C_int
    (fun u _ v _ h => hinterX u v h)
  have hbi_le : ((Lset π g I t₁ t₂).biUnion (XAll π g I)).card ≤ k := by
    rw [← hI]
    refine Finset.card_le_card ?_
    intro x hx
    obtain ⟨v, _, hxv⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp hxv).1
  have hch_le : (Lset π g I t₁ t₂).card.choose 2 ≤ L_cap.choose 2 :=
    Nat.choose_le_choose 2 hcard_lt.le
  have hsum_le : (∑ v ∈ Lset π g I t₁ t₂, ((XAll π g I v).card : ℝ)) ≤
      (k : ℝ) + ((L_cap.choose 2 * C_int : ℕ) : ℝ) := by
    have h1 : (∑ v ∈ Lset π g I t₁ t₂, (XAll π g I v).card : ℕ) ≤ k + L_cap.choose 2 * C_int := by
      have : (Lset π g I t₁ t₂).card.choose 2 * C_int ≤ L_cap.choose 2 * C_int :=
        Nat.mul_le_mul_right C_int hch_le
      omega
    exact_mod_cast h1
  calc (((Lset π g I t₁ t₂).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ)
      ≤ ∑ v ∈ Lset π g I t₁ t₂, ((pairsOf (XAll π g I v)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
    _ = ∑ v ∈ Lset π g I t₁ t₂, (((XAll π g I v).card.choose 2 : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl fun v _ => by rw [pairsOf_card]
    _ ≤ ∑ v ∈ Lset π g I t₁ t₂, (((XAll π g I v).card : ℝ) * t₁ / 2) := by
          refine Finset.sum_le_sum fun v hv => ?_
          exact choose_two_le_half_mul_bound (Finset.mem_filter.mp hv).2.2
    _ = (t₁ / 2) * ∑ v ∈ Lset π g I t₁ t₂, ((XAll π g I v).card : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun v _ => by ring
    _ ≤ (t₁ / 2) * ((k : ℝ) + ((L_cap.choose 2 * C_int : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hsum_le (by linarith)

end Lemma32Large

section Lemma35Huge

/-- Lemma 3.5 (`lem:huge`, deterministic):
bounds on `|Hset|` and all four projected closed-pair sums over `Hset ∩ V_R` and `Hset ∩ V_B`. -/
lemma lem_huge_bound {n m k C_int C_proj H_cap Dmax : ℕ} {t₁ M₀ ε₂ : ℝ}
    (hM₀ : 0 ≤ M₀) (hε₂ : 0 ≤ ε₂)
    (π : PiPair n m) (g : GPair m) (I : Finset (Fin n)) (hI : I.card = k)
    (hinter : ∀ u v : Fin m ⊕ Fin m, u ≠ v → (nbrAll π g u ∩ nbrAll π g v).card ≤ C_int)
    (hdegR : ∀ r : Fin m, (nbrG g.1 r).card ≤ Dmax)
    (hdegB : ∀ b : Fin m, (nbrG g.2 b).card ≤ Dmax)
    (hNV_R : ∀ r : Fin m, ((nbrV π.1 g.1 r).card : ℝ) ≤ (1 + ε₂) * M₀)
    (hNV_B : ∀ b : Fin m, ((nbrV π.2 g.2 b).card : ℝ) ≤ (1 + ε₂) * M₀)
    (hprojB : ∀ r₁ r₂ : Fin m, r₁ ≠ r₂ → (projNbr π.1 π.2 g.1 r₁ ∩ projNbr π.1 π.2 g.1 r₂).card ≤ C_proj)
    (hprojR : ∀ b₁ b₂ : Fin m, b₁ ≠ b₂ → (projNbr π.2 π.1 g.2 b₁ ∩ projNbr π.2 π.1 g.2 b₂).card ≤ C_proj)
    (hHcap : (k : ℝ) + ((H_cap.choose 2 * C_int : ℕ) : ℝ) < (H_cap : ℝ) * t₁) :
    let HR : Finset (Fin m) := by classical exact Finset.univ.filter (fun r => Sum.inl r ∈ Hset π g I t₁)
    let HB : Finset (Fin m) := by classical exact Finset.univ.filter (fun b => Sum.inr b ∈ Hset π g I t₁)
    (Hset π g I t₁).card < H_cap ∧
    (∑ r ∈ HR, ((projPairs π.1 (XV π.1 g.1 I r)).card : ℝ)) ≤ ((H_cap * Dmax : ℕ) : ℝ) ^ 2 / 2 ∧
    (∑ b ∈ HB, ((projPairs π.2 (XV π.2 g.2 I b)).card : ℝ)) ≤ ((H_cap * Dmax : ℕ) : ℝ) ^ 2 / 2 ∧
    (∑ r ∈ HR, ((projPairs π.2 (XV π.1 g.1 I r)).card : ℝ)) ≤
      (1 + ε₂) ^ 2 * gCap M₀ (((k - (I.image π.1).card : ℕ) : ℝ) +
        ((H_cap * Dmax + H_cap.choose 2 * C_proj : ℕ) : ℝ)) ∧
    (∑ b ∈ HB, ((projPairs π.1 (XV π.2 g.2 I b)).card : ℝ)) ≤
      (1 + ε₂) ^ 2 * gCap M₀ (((k - (I.image π.2).card : ℕ) : ℝ) +
        ((H_cap * Dmax + H_cap.choose 2 * C_proj : ℕ) : ℝ)) := by
  classical
  dsimp only
  set HR : Finset (Fin m) := Finset.univ.filter (fun r => Sum.inl r ∈ Hset π g I t₁)
  set HB : Finset (Fin m) := Finset.univ.filter (fun b => Sum.inr b ∈ Hset π g I t₁)
  have hinterX : ∀ u v : Fin m ⊕ Fin m, u ≠ v → (XAll π g I u ∩ XAll π g I v).card ≤ C_int := by
    intro u v huv
    have hsub : XAll π g I u ∩ XAll π g I v ⊆ nbrAll π g u ∩ nbrAll π g v := fun x hx =>
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).2,
        (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).2⟩
    exact (Finset.card_le_card hsub).trans (hinter u v huv)
  have hH_lt : (Hset π g I t₁).card < H_cap := by
    by_contra hge
    push Not at hge
    obtain ⟨H, hHsub, hHcard⟩ := Finset.exists_subset_card_eq hge
    have hIE := sum_card_le_card_biUnion_add H (XAll π g I) C_int (fun u _ v _ h => hinterX u v h)
    have hbi_le : (H.biUnion (XAll π g I)).card ≤ k := by
      rw [← hI]
      refine Finset.card_le_card ?_
      intro x hx
      obtain ⟨v, _, hxv⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_inter.mp hxv).1
    have hsum_gt : (H_cap : ℝ) * t₁ ≤ ∑ v ∈ H, ((XAll π g I v).card : ℝ) := by
      calc (H_cap : ℝ) * t₁ = ∑ _v ∈ H, t₁ := by rw [Finset.sum_const, nsmul_eq_mul, hHcard]
        _ ≤ ∑ v ∈ H, ((XAll π g I v).card : ℝ) := Finset.sum_le_sum fun v hv =>
            ((Finset.mem_filter.mp (hHsub hv)).2).le
    have hIE_R : ∑ v ∈ H, ((XAll π g I v).card : ℝ) ≤ (k : ℝ) + ((H_cap.choose 2 * C_int : ℕ) : ℝ) := by
      rw [hHcard] at hIE
      exact_mod_cast (by omega : (∑ v ∈ H, (XAll π g I v).card : ℕ) ≤ k + H_cap.choose 2 * C_int)
    linarith
  have hHR_le : HR.card ≤ H_cap := by
    have h1 : HR.card ≤ (Hset π g I t₁).card := by
      refine Finset.card_le_card_of_injOn Sum.inl (fun r hr => (Finset.mem_filter.mp hr).2)
        (fun _ _ _ _ h => Sum.inl.inj h)
    exact h1.trans hH_lt.le
  have hHB_le : HB.card ≤ H_cap := by
    have h1 : HB.card ≤ (Hset π g I t₁).card := by
      refine Finset.card_le_card_of_injOn Sum.inr (fun b hb => (Finset.mem_filter.mp hb).2)
        (fun _ _ _ _ h => Sum.inr.inj h)
    exact h1.trans hH_lt.le
  -- Symmetric helper for one color!
  have hone : ∀ (π₁ π₂ : Fin n → Fin m) (g₁ : Pair m → Bool) (H₁ : Finset (Fin m)),
      H₁.card ≤ H_cap →
      (∀ v : Fin m, (nbrG g₁ v).card ≤ Dmax) →
      (∀ v : Fin m, ((nbrV π₁ g₁ v).card : ℝ) ≤ (1 + ε₂) * M₀) →
      (∀ u v : Fin m, u ≠ v → (projNbr π₁ π₂ g₁ u ∩ projNbr π₁ π₂ g₁ v).card ≤ C_proj) →
      (∑ v ∈ H₁, ((projPairs π₁ (XV π₁ g₁ I v)).card : ℝ)) ≤ ((H_cap * Dmax : ℕ) : ℝ) ^ 2 / 2 ∧
      (∑ v ∈ H₁, ((projPairs π₂ (XV π₁ g₁ I v)).card : ℝ)) ≤
        (1 + ε₂) ^ 2 * gCap M₀ (((k - (I.image π₁).card : ℕ) : ℝ) +
          ((H_cap * Dmax + H_cap.choose 2 * C_proj : ℕ) : ℝ)) := by
    intro π₁ π₂ g₁ H₁ hH₁_le hdeg hNV hproj
    have himg1_le : ∀ v : Fin m, ((XV π₁ g₁ I v).image π₁).card ≤ Dmax := by
      intro v
      have hsub : (XV π₁ g₁ I v).image π₁ ⊆ nbrG g₁ v := by
        intro u hu
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
      exact (Finset.card_le_card hsub).trans (hdeg v)
    have hsum1 : (∑ v ∈ H₁, ((XV π₁ g₁ I v).image π₁).card) ≤ H_cap * Dmax := by
      calc ∑ v ∈ H₁, ((XV π₁ g₁ I v).image π₁).card
          ≤ ∑ _v ∈ H₁, Dmax := Finset.sum_le_sum fun v _ => himg1_le v
        _ = H₁.card * Dmax := by simp
        _ ≤ H_cap * Dmax := Nat.mul_le_mul_right Dmax hH₁_le
    constructor
    · calc ∑ v ∈ H₁, ((projPairs π₁ (XV π₁ g₁ I v)).card : ℝ)
          = ∑ v ∈ H₁, ((((XV π₁ g₁ I v).image π₁).card.choose 2 : ℕ) : ℝ) := by
              refine Finset.sum_congr rfl fun v _ => by rw [projPairs_card]
        _ ≤ ∑ v ∈ H₁, ((((XV π₁ g₁ I v).image π₁).card : ℝ) ^ 2 / 2) :=
              Finset.sum_le_sum fun v _ => choose_two_le_half_sq _
        _ = (∑ v ∈ H₁, (((XV π₁ g₁ I v).image π₁).card : ℝ) ^ 2) / 2 := by rw [Finset.sum_div]
        _ ≤ (∑ v ∈ H₁, (((XV π₁ g₁ I v).image π₁).card : ℝ)) ^ 2 / 2 := by
              apply div_le_div_of_nonneg_right _ (by norm_num)
              have hnonneg : ∀ v ∈ H₁, (0 : ℝ) ≤ (((XV π₁ g₁ I v).image π₁).card : ℝ) :=
                fun _ _ => Nat.cast_nonneg _
              calc ∑ v ∈ H₁, (((XV π₁ g₁ I v).image π₁).card : ℝ) ^ 2
                  ≤ ∑ v ∈ H₁, (((XV π₁ g₁ I v).image π₁).card : ℝ) *
                      (∑ w ∈ H₁, (((XV π₁ g₁ I w).image π₁).card : ℝ)) :=
                    Finset.sum_le_sum fun v hv => by
                      have h1 := hnonneg v hv
                      have h2 := Finset.single_le_sum hnonneg hv
                      nlinarith
                _ = (∑ v ∈ H₁, (((XV π₁ g₁ I v).image π₁).card : ℝ)) ^ 2 := by
                    rw [← Finset.sum_mul, sq]
        _ ≤ ((H_cap * Dmax : ℕ) : ℝ) ^ 2 / 2 := by
              apply div_le_div_of_nonneg_right _ (by norm_num)
              have hsum1R : (∑ v ∈ H₁, (((XV π₁ g₁ I v).image π₁).card : ℝ)) ≤ ((H_cap * Dmax : ℕ) : ℝ) := by
                exact_mod_cast hsum1
              have h0 : (0 : ℝ) ≤ ∑ v ∈ H₁, (((XV π₁ g₁ I v).image π₁).card : ℝ) :=
                Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
              nlinarith
    · -- Second bound: `∑ v ∈ H₁, choose |π₂(X_v)| 2` via `sum_half_sq_le_gCap`!
      set U : Finset (Fin n) := H₁.biUnion (fun v => XV π₁ g₁ I v)
      have hUsub : U ⊆ I := by
        intro x hx
        obtain ⟨v, _, hxv⟩ := Finset.mem_biUnion.mp hx
        exact (Finset.mem_filter.mp hxv).1
      -- Bound `|U| ≤ k - |I.image π₁| + H_cap * Dmax`!
      have hU_le : U.card ≤ (k - (I.image π₁).card) + H_cap * Dmax := by
        have hIeq : (I.image π₁) ⊆ U.image π₁ ∪ (I \ U).image π₁ := by
          intro u hu
          obtain ⟨x, hxI, rfl⟩ := Finset.mem_image.mp hu
          by_cases hxU : x ∈ U
          · exact Finset.mem_union_left _ (Finset.mem_image_of_mem π₁ hxU)
          · exact Finset.mem_union_right _ (Finset.mem_image_of_mem π₁ (Finset.mem_sdiff.mpr ⟨hxI, hxU⟩))
        have hc1 : (I.image π₁).card ≤ (U.image π₁).card + ((I \ U).image π₁).card :=
          (Finset.card_le_card hIeq).trans (Finset.card_union_le _ _)
        have hc2 : (U.image π₁).card ≤ H_cap * Dmax := by
          have heq : U.image π₁ = H₁.biUnion (fun v => (XV π₁ g₁ I v).image π₁) := by
            ext u
            simp only [U, Finset.mem_image, Finset.mem_biUnion]
            exact ⟨fun ⟨x, ⟨v, hv, hxv⟩, hπ⟩ => ⟨v, hv, x, hxv, hπ⟩,
                   fun ⟨v, hv, x, hxv, hπ⟩ => ⟨x, ⟨v, hv, hxv⟩, hπ⟩⟩
          rw [heq]
          exact Finset.card_biUnion_le.trans hsum1
        have hc3 : ((I \ U).image π₁).card ≤ k - U.card := by
          calc ((I \ U).image π₁).card ≤ (I \ U).card := Finset.card_image_le
            _ = I.card - U.card := Finset.card_sdiff_of_subset hUsub
            _ = k - U.card := by rw [hI]
        have hUle_k : U.card ≤ k := by rw [← hI]; exact Finset.card_le_card hUsub
        omega
      -- Bound `∑ v ∈ H₁, |π₂(X_v)| ≤ |U| + H_cap.choose 2 * C_proj`!
      have hsum2 : (∑ v ∈ H₁, ((XV π₁ g₁ I v).image π₂).card) ≤
          (k - (I.image π₁).card) + (H_cap * Dmax + H_cap.choose 2 * C_proj) := by
        have hIE := sum_card_le_card_biUnion_add H₁ (fun v => (XV π₁ g₁ I v).image π₂) C_proj (by
          intro u _ v _ huv
          have hsub : (XV π₁ g₁ I u).image π₂ ∩ (XV π₁ g₁ I v).image π₂ ⊆
              projNbr π₁ π₂ g₁ u ∩ projNbr π₁ π₂ g₁ v := by
            intro b hb
            rcases Finset.mem_inter.mp hb with ⟨hbu, hbv⟩
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hbu
            obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hbv
            refine Finset.mem_inter.mpr ⟨?_, ?_⟩
            · exact Finset.mem_image_of_mem π₂ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩)
            · rw [← hyx]
              exact Finset.mem_image_of_mem π₂ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩)
          exact (Finset.card_le_card hsub).trans (hproj u v huv))
        have hbi_eq : H₁.biUnion (fun v => (XV π₁ g₁ I v).image π₂) = U.image π₂ := by
          ext b
          simp only [U, Finset.mem_biUnion, Finset.mem_image]
          exact ⟨fun ⟨v, hv, x, hxv, hπ⟩ => ⟨x, ⟨v, hv, hxv⟩, hπ⟩,
                 fun ⟨x, ⟨v, hv, hxv⟩, hπ⟩ => ⟨v, hv, x, hxv, hπ⟩⟩
        have hbi_le : (U.image π₂).card ≤ U.card := Finset.card_image_le
        have hch_le : H₁.card.choose 2 * C_proj ≤ H_cap.choose 2 * C_proj :=
          Nat.mul_le_mul_right C_proj (Nat.choose_le_choose 2 hH₁_le)
        rw [hbi_eq] at hIE
        omega
      -- Apply `sum_half_sq_le_gCap`!
      calc ∑ v ∈ H₁, ((projPairs π₂ (XV π₁ g₁ I v)).card : ℝ)
          = ∑ v ∈ H₁, ((((XV π₁ g₁ I v).image π₂).card.choose 2 : ℕ) : ℝ) := by
              refine Finset.sum_congr rfl fun v _ => by rw [projPairs_card]
        _ ≤ ∑ v ∈ H₁, ((((XV π₁ g₁ I v).image π₂).card : ℝ) ^ 2 / 2) :=
              Finset.sum_le_sum fun v _ => choose_two_le_half_sq _
        _ = (∑ v ∈ H₁, (((XV π₁ g₁ I v).image π₂).card : ℝ) ^ 2) / 2 := by rw [Finset.sum_div]
        _ ≤ (1 + ε₂) ^ 2 * gCap M₀ (((k - (I.image π₁).card : ℕ) : ℝ) +
              ((H_cap * Dmax + H_cap.choose 2 * C_proj : ℕ) : ℝ)) := by
              apply sum_half_sq_le_gCap H₁ (fun v => (((XV π₁ g₁ I v).image π₂).card : ℝ)) hM₀ hε₂
              · intro _ _; exact Nat.cast_nonneg _
              · intro v _
                have hc : ((XV π₁ g₁ I v).image π₂).card ≤ (nbrV π₁ g₁ v).card := by
                  calc ((XV π₁ g₁ I v).image π₂).card ≤ (XV π₁ g₁ I v).card := Finset.card_image_le
                    _ ≤ (nbrV π₁ g₁ v).card := Finset.card_le_card fun x hx =>
                        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
                exact (Nat.cast_le.mpr hc).trans (hNV v)
              · exact_mod_cast hsum2
  obtain ⟨hR1, hR2⟩ := hone π.1 π.2 g.1 HR hHR_le hdegR hNV_R hprojB
  obtain ⟨hB1, hB2⟩ := hone π.2 π.1 g.2 HB hHB_le hdegB hNV_B hprojR
  exact ⟨hH_lt, hR1, hB1, hR2, hB2⟩

end Lemma35Huge

section Lemma33Medium

/-- Equivalence between `GPair m` and `(Pair m ⊕ Pair m → Bool)`. -/
def gPairEquiv (m : ℕ) : (Pair m ⊕ Pair m → Bool) ≃ GPair m where
  toFun f := (fun e => f (Sum.inl e), fun e => f (Sum.inr e))
  invFun g := Sum.elim g.1 g.2
  left_inv f := by funext x; cases x <;> rfl
  right_inv g := by cases g; rfl

lemma gPairW_eq_bernW {m : ℕ} (p : ℝ) (f : Pair m ⊕ Pair m → Bool) :
    gPairW m p (gPairEquiv m f) = bernW (Pair m ⊕ Pair m) p f := by
  simp [gPairW, prodW, bernW, piW, gPairEquiv, Fintype.prod_sum_type]

/-- Bipartite edge set in `Pair m ⊕ Pair m` between `B : Finset (Fin m ⊕ Fin m)` and `(πR(I), πB(I))`. -/
def bipEdges {n m : ℕ} (π : PiPair n m) (I : Finset (Fin n)) (B : Finset (Fin m ⊕ Fin m)) :
    Finset (Pair m ⊕ Pair m) :=
  let BR := Finset.univ.filter (fun r : Fin m => Sum.inl r ∈ B)
  let BB := Finset.univ.filter (fun b : Fin m => Sum.inr b ∈ B)
  let ER := Finset.univ.filter (fun e : Pair m =>
    (e.1.1 ∈ BR ∧ e.1.2 ∈ I.image π.1) ∨ (e.1.2 ∈ BR ∧ e.1.1 ∈ I.image π.1))
  let EB := Finset.univ.filter (fun e : Pair m =>
    (e.1.1 ∈ BB ∧ e.1.2 ∈ I.image π.2) ∨ (e.1.2 ∈ BB ∧ e.1.1 ∈ I.image π.2))
  ER.image Sum.inl ∪ EB.image Sum.inr

lemma bipEdges_card_le {n m : ℕ} (π : PiPair n m) (I : Finset (Fin n))
    (B : Finset (Fin m ⊕ Fin m)) :
    (bipEdges π I B).card ≤ B.card * I.card := by
  let BR := Finset.univ.filter (fun r : Fin m => Sum.inl r ∈ B)
  let BB := Finset.univ.filter (fun b : Fin m => Sum.inr b ∈ B)
  have hBsum : BR.card + BB.card = B.card := by
    have hdisj : Disjoint (BR.image Sum.inl) (BB.image Sum.inr) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hx1
      obtain ⟨_, _, h⟩ := Finset.mem_image.mp hx2
      cases h
    have hunion : BR.image Sum.inl ∪ BB.image Sum.inr = B := by
      ext x; cases x <;> simp [BR, BB]
    rw [← hunion, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective]
  have hone : ∀ (π₁ : Fin n → Fin m) (B₁ : Finset (Fin m)),
      (Finset.univ.filter (fun e : Pair m =>
        (e.1.1 ∈ B₁ ∧ e.1.2 ∈ I.image π₁) ∨ (e.1.2 ∈ B₁ ∧ e.1.1 ∈ I.image π₁))).card ≤
      B₁.card * I.card := by
    intro π₁ B₁
    let E₁ := Finset.univ.filter (fun e : Pair m =>
      (e.1.1 ∈ B₁ ∧ e.1.2 ∈ I.image π₁) ∨ (e.1.2 ∈ B₁ ∧ e.1.1 ∈ I.image π₁))
    have hinj : ∀ e : {e // e ∈ E₁}, ∃ p : Fin m × Fin m, p ∈ B₁ ×ˢ I.image π₁ ∧
        ({p.1, p.2} : Finset (Fin m)) = {e.1.1.1, e.1.1.2} := by
      intro ⟨e, he⟩
      rcases (Finset.mem_filter.mp he).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨(e.1.1, e.1.2), Finset.mem_product.mpr ⟨h1, h2⟩, rfl⟩
      · exact ⟨(e.1.2, e.1.1), Finset.mem_product.mpr ⟨h1, h2⟩, Finset.pair_comm _ _⟩
    choose ψ hψ_mem hψ_eq using hinj
    have hφ_inj : Function.Injective (fun e : {e // e ∈ E₁} =>
        (⟨ψ e, hψ_mem e⟩ : {p // p ∈ B₁ ×ˢ I.image π₁})) := by
      intro e₁ e₂ heq
      have hpeq : ψ e₁ = ψ e₂ := congr_arg Subtype.val heq
      have hset : ({e₁.1.1.1, e₁.1.1.2} : Finset (Fin m)) = {e₂.1.1.1, e₂.1.1.2} :=
        (hψ_eq e₁).symm.trans (hpeq ▸ hψ_eq e₂)
      have h1 : e₁.1.1.1 ∈ ({e₂.1.1.1, e₂.1.1.2} : Finset (Fin m)) := hset ▸ by simp
      have h2 : e₁.1.1.2 ∈ ({e₂.1.1.1, e₂.1.1.2} : Finset (Fin m)) := hset ▸ by simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
      have hlt1 := e₁.1.2; have hlt2 := e₂.1.2
      apply Subtype.ext; apply Subtype.ext; apply Prod.ext
      · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact absurd (h1.trans h2.symm) hlt1.ne
        · exact h1
        · rw [h1, h2] at hlt1; exact absurd (lt_trans hlt1 hlt2) (lt_irrefl _)
        · exact absurd (h1.trans h2.symm) hlt1.ne
      · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact absurd (h1.trans h2.symm) hlt1.ne
        · exact h2
        · rw [h1, h2] at hlt1; exact absurd (lt_trans hlt1 hlt2) (lt_irrefl _)
        · exact absurd (h1.trans h2.symm) hlt1.ne
    calc E₁.card = Fintype.card {e // e ∈ E₁} := (Fintype.card_coe E₁).symm
      _ ≤ Fintype.card {p // p ∈ B₁ ×ˢ I.image π₁} := Fintype.card_le_of_injective _ hφ_inj
      _ = (B₁ ×ˢ I.image π₁).card := Fintype.card_coe _
      _ = B₁.card * (I.image π₁).card := Finset.card_product _ _
      _ ≤ B₁.card * I.card := Nat.mul_le_mul_left _ Finset.card_image_le
  calc (bipEdges π I B).card
      ≤ _ + _ := Finset.card_union_le _ _
    _ ≤ _ + _ := add_le_add Finset.card_image_le Finset.card_image_le
    _ ≤ BR.card * I.card + BB.card * I.card := add_le_add (hone π.1 BR) (hone π.2 BB)
    _ = B.card * I.card := by rw [← Nat.add_mul, hBsum]

/-- Double-counting: `∑ v ∈ B, |X_v(I)| ≤ 2 * Fmax * |active edges in bipEdges π I Bt|` whenever `B ⊆ Bt`. -/
lemma sum_XAll_le_two_mul_Fmax_bipEdges {n m Fmax : ℕ}
    (π : PiPair n m) (g : GPair m) (I : Finset (Fin n)) (B Bt : Finset (Fin m ⊕ Fin m))
    (hsub : B ⊆ Bt)
    (hFR : ∀ r : Fin m, (fiber π.1 r).card ≤ Fmax)
    (hFB : ∀ b : Fin m, (fiber π.2 b).card ≤ Fmax) :
    ∑ v ∈ B, (XAll π g I v).card ≤
      2 * Fmax * ((bipEdges π I Bt).filter (fun e => (gPairEquiv m).symm g e = true)).card := by
  let BR := Finset.univ.filter (fun r : Fin m => Sum.inl r ∈ B)
  let BB := Finset.univ.filter (fun b : Fin m => Sum.inr b ∈ B)
  let BtR := Finset.univ.filter (fun r : Fin m => Sum.inl r ∈ Bt)
  let BtB := Finset.univ.filter (fun b : Fin m => Sum.inr b ∈ Bt)
  let ER := Finset.univ.filter (fun e : Pair m =>
    (e.1.1 ∈ BtR ∧ e.1.2 ∈ I.image π.1) ∨ (e.1.2 ∈ BtR ∧ e.1.1 ∈ I.image π.1))
  let EB := Finset.univ.filter (fun e : Pair m =>
    (e.1.1 ∈ BtB ∧ e.1.2 ∈ I.image π.2) ∨ (e.1.2 ∈ BtB ∧ e.1.1 ∈ I.image π.2))
  -- One-color double-counting helper:
  have hone : ∀ (π₁ : Fin n → Fin m) (g₁ : Pair m → Bool) (B₁ Bt₁ : Finset (Fin m))
      (E₁ : Finset (Pair m)),
      B₁ ⊆ Bt₁ →
      E₁ = Finset.univ.filter (fun e : Pair m =>
        (e.1.1 ∈ Bt₁ ∧ e.1.2 ∈ I.image π₁) ∨ (e.1.2 ∈ Bt₁ ∧ e.1.1 ∈ I.image π₁)) →
      (∀ u : Fin m, (fiber π₁ u).card ≤ Fmax) →
      ∑ v ∈ B₁, (XV π₁ g₁ I v).card ≤ 2 * Fmax * (E₁.filter (fun e => g₁ e = true)).card := by
    intro π₁ g₁ B₁ Bt₁ E₁ hBsub hE₁ hF
    let P := (B₁ ×ˢ I).filter (fun p => gAdj g₁ p.1 (π₁ p.2) = true)
    have hPcard : P.card = ∑ v ∈ B₁, (XV π₁ g₁ I v).card := by
      have h1 : P = B₁.biUnion (fun v => (XV π₁ g₁ I v).image (fun x => (v, x))) := by
        ext ⟨v, x⟩
        simp [P, XV, and_assoc]
      rw [h1, Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun v _ => ?_
        exact Finset.card_image_of_injective _ (fun x₁ x₂ h => (Prod.mk.inj h).2)
      · intro v₁ _ v₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro ⟨v, x⟩ h1 h2
        obtain ⟨_, _, hv1⟩ := Finset.mem_image.mp h1
        obtain ⟨_, _, hv2⟩ := Finset.mem_image.mp h2
        exact hne ((Prod.mk.inj hv1).1.trans (Prod.mk.inj hv2).1.symm)
    rw [← hPcard]
    let Eact := E₁.filter (fun e => g₁ e = true)
    have hsubP : P ⊆ Eact.biUnion (fun e =>
        ((fiber π₁ e.1.2).image (fun x => (e.1.1, x))) ∪
        ((fiber π₁ e.1.1).image (fun x => (e.1.2, x)))) := by
      intro ⟨v, x⟩ hp
      have hmem := Finset.mem_filter.mp hp
      have hvB : v ∈ B₁ := (Finset.mem_product.mp hmem.1).1
      have hxI : x ∈ I := (Finset.mem_product.mp hmem.1).2
      have hadj : gAdj g₁ v (π₁ x) = true := hmem.2
      have hne : v ≠ π₁ x := gAdj_ne_of_true hadj
      let e := mkEdge v (π₁ x) hne
      have he_act : e ∈ Eact := by
        rw [Finset.mem_filter, hE₁, Finset.mem_filter]
        refine ⟨⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · unfold e mkEdge
          split_ifs
          · exact Or.inl ⟨hBsub hvB, Finset.mem_image_of_mem π₁ hxI⟩
          · exact Or.inr ⟨hBsub hvB, Finset.mem_image_of_mem π₁ hxI⟩
        · simpa [e, gAdj, hne] using hadj
      refine Finset.mem_biUnion.mpr ⟨e, he_act, ?_⟩
      unfold e mkEdge
      split_ifs
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (by simp [fiber]))
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (by simp [fiber]))
    calc P.card
        ≤ (Eact.biUnion (fun e =>
            ((fiber π₁ e.1.2).image (fun x => (e.1.1, x))) ∪
            ((fiber π₁ e.1.1).image (fun x => (e.1.2, x))))).card := Finset.card_le_card hsubP
      _ ≤ ∑ e ∈ Eact, (((fiber π₁ e.1.2).image (fun x => (e.1.1, x))) ∪
            ((fiber π₁ e.1.1).image (fun x => (e.1.2, x)))).card := Finset.card_biUnion_le
      _ ≤ ∑ _e ∈ Eact, (2 * Fmax) := by
          refine Finset.sum_le_sum fun e _ => ?_
          have h1 := Finset.card_union_le ((fiber π₁ e.1.2).image (fun x => (e.1.1, x)))
            ((fiber π₁ e.1.1).image (fun x => (e.1.2, x)))
          have h2 : ((fiber π₁ e.1.2).image (fun x => (e.1.1, x))).card ≤ Fmax :=
            Finset.card_image_le.trans (hF e.1.2)
          have h3 : ((fiber π₁ e.1.1).image (fun x => (e.1.2, x))).card ≤ Fmax :=
            Finset.card_image_le.trans (hF e.1.1)
          omega
      _ = 2 * Fmax * Eact.card := by simp [mul_comm]
  have hsumB : ∑ v ∈ B, (XAll π g I v).card =
      ∑ r ∈ BR, (XV π.1 g.1 I r).card + ∑ b ∈ BB, (XV π.2 g.2 I b).card := by
    have hdisj : Disjoint (BR.image Sum.inl) (BB.image Sum.inr) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hx1
      obtain ⟨_, _, h⟩ := Finset.mem_image.mp hx2
      cases h
    have hunion : BR.image Sum.inl ∪ BB.image Sum.inr = B := by
      ext x; cases x <;> simp [BR, BB]
    rw [← hunion, Finset.sum_union hdisj,
      Finset.sum_image (fun _ _ _ _ h => Sum.inl.inj h),
      Finset.sum_image (fun _ _ _ _ h => Sum.inr.inj h)]
    congr 1
    · refine Finset.sum_congr rfl fun r _ => by rw [XAll_inl]
    · refine Finset.sum_congr rfl fun b _ => by rw [XAll_inr]
  have hact_split : ((bipEdges π I Bt).filter (fun e => (gPairEquiv m).symm g e = true)).card =
      (ER.filter (fun e => g.1 e = true)).card + (EB.filter (fun e => g.2 e = true)).card := by
    have hdisj : Disjoint ((ER.filter (fun e => g.1 e = true)).image Sum.inl)
        ((EB.filter (fun e => g.2 e = true)).image Sum.inr) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hx1
      obtain ⟨_, _, h⟩ := Finset.mem_image.mp hx2
      cases h
    have heq : (bipEdges π I Bt).filter (fun e => (gPairEquiv m).symm g e = true) =
        (ER.filter (fun e => g.1 e = true)).image Sum.inl ∪
        (EB.filter (fun e => g.2 e = true)).image Sum.inr := by
      ext x
      cases x <;> simp [bipEdges, ER, EB, BtR, BtB, gPairEquiv]
    rw [heq, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective]
  rw [hsumB, hact_split, Nat.mul_add]
  have h1 := hone π.1 g.1 BR BtR ER (fun r hr => by simp only [BR, BtR, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢; exact hsub hr) rfl hFR
  have h2 := hone π.2 g.2 BB BtB EB (fun b hb => by simp only [BB, BtB, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢; exact hsub hb) rfl hFB
  omega

/-- Lemma 3.3 (`lem:med`, non-asymptotic fixed-`π` bound):
for fixed `π` with max fiber size `≤ Fmax`, bounds the probability that SOME `k`-set `I`
has `∑_{v ∈ Mset} |X_v(I)| > Ylim`. -/
lemma Pr_not_medGood {n m k Fmax b₀ t_med : ℕ} {p t₂ t₃ Ylim : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ht₃ : 0 < t₃) (ht₂ : t₂ ≤ Ylim) (hb₀_ge : 2 * Ylim / t₃ ≤ (b₀ : ℝ)) (hb₀_le : b₀ ≤ 2 * m)
    (ht_med1 : 1 ≤ t_med) (ht_med_le : ((2 * Fmax * t_med : ℕ) : ℝ) ≤ Ylim)
    (π : PiPair n m)
    (hFR : ∀ r : Fin m, (fiber π.1 r).card ≤ Fmax)
    (hFB : ∀ b : Fin m, (fiber π.2 b).card ≤ Fmax) :
    Pr (gPairW m p) (fun g => ∃ I : Finset (Fin n), I.card = k ∧
      Ylim < ∑ v ∈ Mset π g I t₂ t₃, ((XAll π g I v).card : ℝ)) ≤
      (n.choose k : ℝ) * ((2 * m).choose b₀ : ℝ) *
        (Real.exp 1 * ((b₀ * k : ℕ) : ℝ) * p / (t_med : ℝ)) ^ t_med := by
  classical
  have hP := isProb_gPairW (m := m) hp0 hp1
  have himp : ∀ g : GPair m,
      (∃ I : Finset (Fin n), I.card = k ∧ Ylim < ∑ v ∈ Mset π g I t₂ t₃, ((XAll π g I v).card : ℝ)) →
      ∃ I ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      ∃ Bt ∈ (Finset.univ : Finset (Fin m ⊕ Fin m)).powersetCard b₀,
        t_med ≤ ((bipEdges π I Bt).filter (fun e => (gPairEquiv m).symm g e = true)).card := by
    intro g ⟨I, hIk, hYgt⟩
    -- Choose minimal `B ⊆ Mset` with `Ylim < ∑ v ∈ B, |X_v(I)|`!
    let S : Finset (Finset (Fin m ⊕ Fin m)) :=
      (Mset π g I t₂ t₃).powerset.filter (fun B => Ylim < ∑ v ∈ B, ((XAll π g I v).card : ℝ))
    have hSne : S.Nonempty := ⟨Mset π g I t₂ t₃, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr subset_rfl, hYgt⟩⟩
    obtain ⟨B, hBS, hBmin⟩ := Finset.exists_min_image S Finset.card hSne
    have hBsub : B ⊆ Mset π g I t₂ t₃ := Finset.mem_powerset.mp (Finset.mem_filter.mp hBS).1
    have hBgt : Ylim < ∑ v ∈ B, ((XAll π g I v).card : ℝ) := (Finset.mem_filter.mp hBS).2
    have hBne : B.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      subst hemp
      simp only [Finset.sum_empty] at hBgt
      have h0 : 0 ≤ Ylim := le_trans (Nat.cast_nonneg _) ht_med_le
      linarith
    obtain ⟨v₀, hv₀⟩ := hBne
    have herase_le : ∑ v ∈ B.erase v₀, ((XAll π g I v).card : ℝ) ≤ Ylim := by
      by_contra hgt
      push Not at hgt
      have hmem : B.erase v₀ ∈ S := Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr ((Finset.erase_subset v₀ B).trans hBsub), hgt⟩
      have hmin := hBmin (B.erase v₀) hmem
      have hlt : (B.erase v₀).card < B.card := Finset.card_erase_lt_of_mem hv₀
      omega
    have hv₀_le : ((XAll π g I v₀).card : ℝ) ≤ t₂ := (Finset.mem_filter.mp (hBsub hv₀)).2.2
    have hBle2Y : ∑ v ∈ B, ((XAll π g I v).card : ℝ) ≤ 2 * Ylim := by
      rw [← Finset.add_sum_erase B (fun v => ((XAll π g I v).card : ℝ)) hv₀]
      linarith
    have hBcard_le : B.card ≤ b₀ := by
      have hlow : (B.card : ℝ) * t₃ ≤ ∑ v ∈ B, ((XAll π g I v).card : ℝ) := by
        calc (B.card : ℝ) * t₃ = ∑ _v ∈ B, t₃ := by simp
          _ ≤ ∑ v ∈ B, ((XAll π g I v).card : ℝ) := Finset.sum_le_sum fun v hv =>
              ((Finset.mem_filter.mp (hBsub hv)).2.1).le
      have hdiv : (B.card : ℝ) ≤ 2 * Ylim / t₃ := (le_div_iff₀ ht₃).mpr (hlow.trans hBle2Y)
      exact_mod_cast (hdiv.trans hb₀_ge)
    have hb₀_card : b₀ ≤ Fintype.card (Fin m ⊕ Fin m) := by
      simpa [Fintype.card_sum, Fintype.card_fin, two_mul] using hb₀_le
    obtain ⟨Bt, hBBt, hBtcard⟩ := Finset.exists_superset_card_eq hBcard_le hb₀_card
    refine ⟨I, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ I, hIk⟩,
            Bt, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ Bt, hBtcard⟩, ?_⟩
    have hdc := sum_XAll_le_two_mul_Fmax_bipEdges π g I B Bt hBBt hFR hFB
    have hdcR : ∑ v ∈ B, ((XAll π g I v).card : ℝ) ≤
        ((2 * Fmax : ℕ) : ℝ) * (((bipEdges π I Bt).filter (fun e => (gPairEquiv m).symm g e = true)).card : ℝ) := by
      exact_mod_cast hdc
    have hgeR : ((2 * Fmax * t_med : ℕ) : ℝ) <
        ((2 * Fmax : ℕ) : ℝ) * (((bipEdges π I Bt).filter (fun e => (gPairEquiv m).symm g e = true)).card : ℝ) :=
      lt_of_le_of_lt ht_med_le (hBgt.trans_le hdcR)
    have hgeNat : 2 * Fmax * t_med < 2 * Fmax * ((bipEdges π I Bt).filter (fun e => (gPairEquiv m).symm g e = true)).card := by
      push_cast at hgeR
      exact_mod_cast hgeR
    have h2Fpos : 0 < 2 * Fmax := by
      by_contra h0
      have : 2 * Fmax = 0 := by omega
      rw [this, zero_mul, zero_mul] at hgeNat
      omega
    exact le_of_lt (Nat.lt_of_mul_lt_mul_left hgeNat)
  have htpos : (0 : ℝ) < (t_med : ℝ) := by exact_mod_cast ht_med1
  calc Pr (gPairW m p) _
      ≤ Pr (gPairW m p) (fun g =>
          ∃ pIB ∈ ((Finset.univ : Finset (Fin n)).powersetCard k) ×ˢ
                  ((Finset.univ : Finset (Fin m ⊕ Fin m)).powersetCard b₀),
            t_med ≤ ((bipEdges π pIB.1 pIB.2).filter (fun e => (gPairEquiv m).symm g e = true)).card) := by
        refine Pr_mono hP fun g hg => ?_
        obtain ⟨I, hI, Bt, hBt, ht⟩ := himp g hg
        exact ⟨(I, Bt), Finset.mem_product.mpr ⟨hI, hBt⟩, ht⟩
    _ ≤ ∑ pIB ∈ ((Finset.univ : Finset (Fin n)).powersetCard k) ×ˢ
                ((Finset.univ : Finset (Fin m ⊕ Fin m)).powersetCard b₀),
          Pr (gPairW m p) (fun g =>
            t_med ≤ ((bipEdges π pIB.1 pIB.2).filter (fun e => (gPairEquiv m).symm g e = true)).card) :=
        Pr_exists_le hP _ _
    _ ≤ ∑ _pIB ∈ ((Finset.univ : Finset (Fin n)).powersetCard k) ×ˢ
                ((Finset.univ : Finset (Fin m ⊕ Fin m)).powersetCard b₀),
          (Real.exp 1 * ((b₀ * k : ℕ) : ℝ) * p / (t_med : ℝ)) ^ t_med := by
        refine Finset.sum_le_sum fun ⟨I, Bt⟩ hp => ?_
        have hIcard : I.card = k := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp).1).2
        have hBtcard : Bt.card = b₀ := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp).2).2
        rw [← Pr_equiv (gPairEquiv m)]
        have hwt : (fun f : Pair m ⊕ Pair m → Bool => gPairW m p (gPairEquiv m f)) =
            bernW (Pair m ⊕ Pair m) p := funext (gPairW_eq_bernW p)
        have hpred : (fun f : Pair m ⊕ Pair m → Bool =>
            t_med ≤ ((bipEdges π I Bt).filter (fun e => (gPairEquiv m).symm (gPairEquiv m f) e = true)).card) =
            (fun f => t_med ≤ ((bipEdges π I Bt).filter (fun e => f e = true)).card) := by
          funext f; simp
        rw [hwt, hpred]
        have htail := bernW_upper_tail hp0 hp1 (bipEdges π I Bt) t_med
        have hch := choose_le_exp_pow (n := (bipEdges π I Bt).card) (k := t_med) ht_med1
        have hcard_le : ((bipEdges π I Bt).card : ℝ) ≤ ((b₀ * k : ℕ) : ℝ) := by
          have := bipEdges_card_le π I Bt
          rw [hIcard, hBtcard] at this
          exact_mod_cast this
        calc Pr (bernW (Pair m ⊕ Pair m) p) _
            ≤ ((bipEdges π I Bt).card.choose t_med : ℝ) * p ^ t_med := htail
          _ ≤ (Real.exp 1 * ((bipEdges π I Bt).card : ℝ) / (t_med : ℝ)) ^ t_med * p ^ t_med :=
              mul_le_mul_of_nonneg_right hch (pow_nonneg hp0 t_med)
          _ = (Real.exp 1 * ((bipEdges π I Bt).card : ℝ) * p / (t_med : ℝ)) ^ t_med := by
              rw [← mul_pow]; congr 1; ring
          _ ≤ (Real.exp 1 * ((b₀ * k : ℕ) : ℝ) * p / (t_med : ℝ)) ^ t_med := by
              refine pow_le_pow_left₀ (by positivity) ?_ t_med
              exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hcard_le (Real.exp_pos 1).le) hp0) htpos.le
    _ = (n.choose k : ℝ) * ((2 * m).choose b₀ : ℝ) *
          (Real.exp 1 * ((b₀ * k : ℕ) : ℝ) * p / (t_med : ℝ)) ^ t_med := by
        simp [Finset.card_product, Finset.card_powersetCard, Fintype.card_sum, Fintype.card_fin,
          two_mul, mul_assoc]

end Lemma33Medium

section Lemma34Small

/-- External small vertices for `I`: vertices `v ∈ Sset` outside `πR(I) ⊕ πB(I)`. -/
noncomputable def SsetExt {n m : ℕ} (π : PiPair n m) (g : GPair m) (I : Finset (Fin n)) (t₃ : ℝ) :
    Finset (Fin m ⊕ Fin m) :=
  by classical exact (Sset π g I t₃).filter (fun v => match v with
    | Sum.inl r => r ∉ I.image π.1
    | Sum.inr b => b ∉ I.image π.2)

/-- Internal small vertices for `I`: vertices `v ∈ Sset` inside `πR(I) ⊕ πB(I)`. -/
noncomputable def SsetInt {n m : ℕ} (π : PiPair n m) (g : GPair m) (I : Finset (Fin n)) (t₃ : ℝ) :
    Finset (Fin m ⊕ Fin m) :=
  by classical exact (Sset π g I t₃).filter (fun v => match v with
    | Sum.inl r => r ∈ I.image π.1
    | Sum.inr b => b ∈ I.image π.2)

/-- Deterministic bound on internal small pairs (`≤ k * t₃^2`). -/
lemma card_SsetInt_pairs_le {n m k : ℕ} {t₃ : ℝ} (ht₃ : 0 ≤ t₃)
    (π : PiPair n m) (g : GPair m) (I : Finset (Fin n)) (hI : I.card = k) :
    (((SsetInt π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ) ≤
      (k : ℝ) * t₃ ^ 2 := by
  classical
  have hInt_card : (SsetInt π g I t₃).card ≤ 2 * k := by
    have hsub : SsetInt π g I t₃ ⊆ (I.image π.1).image Sum.inl ∪ (I.image π.2).image Sum.inr := by
      intro v hv
      have hm := (Finset.mem_filter.mp hv).2
      cases v with
      | inl r => exact Finset.mem_union_left _ (Finset.mem_image_of_mem Sum.inl hm)
      | inr b => exact Finset.mem_union_right _ (Finset.mem_image_of_mem Sum.inr hm)
    calc (SsetInt π g I t₃).card
        ≤ ((I.image π.1).image Sum.inl ∪ (I.image π.2).image Sum.inr).card := Finset.card_le_card hsub
      _ ≤ ((I.image π.1).image Sum.inl).card + ((I.image π.2).image Sum.inr).card := Finset.card_union_le _ _
      _ ≤ (I.image π.1).card + (I.image π.2).card := add_le_add Finset.card_image_le Finset.card_image_le
      _ ≤ I.card + I.card := add_le_add Finset.card_image_le Finset.card_image_le
      _ = 2 * k := by omega
  calc (((SsetInt π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ)
      ≤ ∑ v ∈ SsetInt π g I t₃, ((pairsOf (XAll π g I v)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
    _ = ∑ v ∈ SsetInt π g I t₃, (((XAll π g I v).card.choose 2 : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl fun v _ => by rw [pairsOf_card]
    _ ≤ ∑ _v ∈ SsetInt π g I t₃, (t₃ ^ 2 / 2) := by
          refine Finset.sum_le_sum fun v hv => ?_
          have hle : ((XAll π g I v).card : ℝ) ≤ t₃ :=
            (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2
          have h1 := choose_two_le_half_sq (XAll π g I v).card
          have h0 : (0 : ℝ) ≤ ((XAll π g I v).card : ℝ) := Nat.cast_nonneg _
          nlinarith
    _ = ((SsetInt π g I t₃).card : ℝ) * (t₃ ^ 2 / 2) := by simp
    _ ≤ ((2 * k : ℕ) : ℝ) * (t₃ ^ 2 / 2) := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hInt_card) (by positivity)
    _ = (k : ℝ) * t₃ ^ 2 := by push_cast; ring

/-- Expectation upper bound for external small closed pairs (used in Lemma 3.4). -/
lemma E_SsetExt_le {n m k Fmax : ℕ} {p t₃ : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (π : PiPair n m) (I : Finset (Fin n)) (hI : I.card = k)
    (hFR : ∀ r : Fin m, (fiber π.1 r).card ≤ Fmax)
    (hFB : ∀ b : Fin m, (fiber π.2 b).card ≤ Fmax) :
    E (gPairW m p) (fun g => (((SsetExt π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ)) ≤
      (k : ℝ) * (Fmax : ℝ) + (k.choose 2 : ℝ) * (2 * (m : ℝ) * p ^ 2) := by
  classical
  have hP := isProb_gPairW (m := m) hp0 hp1
  let Vext : Finset (Fin m ⊕ Fin m) := Finset.univ.filter (fun v => match v with
    | Sum.inl r => r ∉ I.image π.1
    | Sum.inr b => b ∉ I.image π.2)
  set N := Vext.card
  have hNle2m : N ≤ 2 * m := by
    calc N ≤ (Finset.univ : Finset (Fin m ⊕ Fin m)).card := Finset.card_le_univ _
      _ = 2 * m := by simp [Fintype.card_sum, Fintype.card_fin, two_mul]
  -- Split `pairsOf I` into same-fiber pairs and different-fiber pairs!
  let sameF : Finset (Pair n) := (pairsOf I).filter (fun e => π.1 e.1.1 = π.1 e.1.2 ∨ π.2 e.1.1 = π.2 e.1.2)
  let diffF : Finset (Pair n) := (pairsOf I).filter (fun e => π.1 e.1.1 ≠ π.1 e.1.2 ∧ π.2 e.1.1 ≠ π.2 e.1.2)
  have hsame_card : (sameF.card : ℝ) ≤ (k : ℝ) * (Fmax : ℝ) := by
    have hsub : sameF ⊆ (Finset.univ.biUnion (fun r : Fin m => pairsOf (I ∩ fiber π.1 r))) ∪
        (Finset.univ.biUnion (fun b : Fin m => pairsOf (I ∩ fiber π.2 b))) := by
      intro e he
      have hm := Finset.mem_filter.mp he
      have heI := (Finset.mem_filter.mp hm.1).2
      rcases hm.2 with hr | hb
      · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨π.1 e.1.1, Finset.mem_univ _, ?_⟩)
        simp [pairsOf, fiber, heI.1, heI.2, hr.symm]
      · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨π.2 e.1.1, Finset.mem_univ _, ?_⟩)
        simp [pairsOf, fiber, heI.1, heI.2, hb.symm]
    have h1color : ∀ (π₁ : Fin n → Fin m), (∀ u : Fin m, (fiber π₁ u).card ≤ Fmax) →
        ((Finset.univ.biUnion (fun u : Fin m => pairsOf (I ∩ fiber π₁ u))).card : ℝ) ≤ (k : ℝ) * (Fmax : ℝ) / 2 := by
      intro π₁ hF
      have hsum_part : ∑ u : Fin m, (I ∩ fiber π₁ u).card = k := by
        rw [← hI]
        have hdisj : I = Finset.univ.biUnion (fun u : Fin m => I ∩ fiber π₁ u) := by
          ext x; simp [fiber]
        conv_rhs => rw [hdisj]
        rw [Finset.card_biUnion]
        intro u₁ _ u₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [Finset.mem_inter, fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
        exact hne (hx1.2.symm.trans hx2.2)
      calc ((Finset.univ.biUnion (fun u : Fin m => pairsOf (I ∩ fiber π₁ u))).card : ℝ)
          ≤ ∑ u : Fin m, ((pairsOf (I ∩ fiber π₁ u)).card : ℝ) := by
              exact_mod_cast Finset.card_biUnion_le
        _ = ∑ u : Fin m, (((I ∩ fiber π₁ u).card.choose 2 : ℕ) : ℝ) := by
              refine Finset.sum_congr rfl fun u _ => by rw [pairsOf_card]
        _ ≤ ∑ u : Fin m, (((I ∩ fiber π₁ u).card : ℝ) * (Fmax : ℝ) / 2) := by
              refine Finset.sum_le_sum fun u _ => choose_two_le_half_mul_bound ?_
              exact_mod_cast ((Finset.card_le_card Finset.inter_subset_right).trans (hF u))
        _ = (∑ u : Fin m, ((I ∩ fiber π₁ u).card : ℝ)) * (Fmax : ℝ) / 2 := by
              rw [← Finset.sum_div, ← Finset.sum_mul]
        _ = (k : ℝ) * (Fmax : ℝ) / 2 := by
              have : (∑ u : Fin m, ((I ∩ fiber π₁ u).card : ℝ)) = (k : ℝ) := by exact_mod_cast hsum_part
              rw [this]
    have hle_union : (sameF.card : ℝ) ≤
        ((Finset.univ.biUnion (fun r : Fin m => pairsOf (I ∩ fiber π.1 r))).card : ℝ) +
        ((Finset.univ.biUnion (fun b : Fin m => pairsOf (I ∩ fiber π.2 b))).card : ℝ) := by
      exact_mod_cast ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
    linarith [h1color π.1 hFR, h1color π.2 hFB]
  -- For each `e ∈ diffF`, `Pr_{gPairW}(∃ v ∈ Vext, e ∈ pairsOf (XAll v)) ≤ 2 * m * p^2`!
  have hdiff_prob : ∀ e ∈ diffF,
      Pr (gPairW m p) (fun g => ∃ v ∈ Vext, e ∈ pairsOf (XAll π g I v)) ≤ 2 * (m : ℝ) * p ^ 2 := by
    intro e he
    have hneR : π.1 e.1.1 ≠ π.1 e.1.2 := (Finset.mem_filter.mp he).2.1
    have hneB : π.2 e.1.1 ≠ π.2 e.1.2 := (Finset.mem_filter.mp he).2.2
    have heI : e.1.1 ∈ I ∧ e.1.2 ∈ I := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
    calc Pr (gPairW m p) (fun g => ∃ v ∈ Vext, e ∈ pairsOf (XAll π g I v))
        ≤ ∑ v ∈ Vext, Pr (gPairW m p) (fun g => e ∈ pairsOf (XAll π g I v)) := Pr_exists_le hP _ _
      _ ≤ ∑ _v ∈ Vext, p ^ 2 := by
          refine Finset.sum_le_sum fun v hv => ?_
          have hvext := (Finset.mem_filter.mp hv).2
          cases v with
          | inl r =>
            have hne1 : r ≠ π.1 e.1.1 := fun h => hvext (h ▸ Finset.mem_image_of_mem π.1 heI.1)
            have hne2 : r ≠ π.1 e.1.2 := fun h => hvext (h ▸ Finset.mem_image_of_mem π.1 heI.2)
            let p1 := mkEdge r (π.1 e.1.1) hne1
            let p2 := mkEdge r (π.1 e.1.2) hne2
            have hp12 : p1 ≠ p2 := by
              intro h
              unfold p1 p2 mkEdge at h
              split_ifs at h <;>
              · have hf := congr_arg (fun q : Pair m => q.1.1) h
                have hs := congr_arg (fun q : Pair m => q.1.2) h
                first | exact hneR hs | exact hne2 hf | exact hne1 hf.symm | exact hneR hf
            have hsub : ∀ g : GPair m, e ∈ pairsOf (XAll π g I (Sum.inl r)) →
                ∀ q ∈ ({p1, p2} : Finset (Pair m)), g.1 q = true := by
              intro g hmem q hq
              rw [XAll_inl] at hmem
              have h12 := (Finset.mem_filter.mp hmem).2
              have hadj1 := (Finset.mem_filter.mp h12.1).2
              have hadj2 := (Finset.mem_filter.mp h12.2).2
              rcases Finset.mem_insert.mp hq with rfl | hq
              · simpa [p1, gAdj, hne1] using hadj1
              · rw [Finset.mem_singleton.mp hq]; simpa [p2, gAdj, hne2] using hadj2
            calc Pr (gPairW m p) (fun g => e ∈ pairsOf (XAll π g I (Sum.inl r)))
                ≤ Pr (gPairW m p) (fun g => ∀ q ∈ ({p1, p2} : Finset (Pair m)), g.1 q = true) :=
                  Pr_mono hP hsub
              _ = Pr (bernW (Pair m) p) (fun g₁ => ∀ q ∈ ({p1, p2} : Finset (Pair m)), g₁ q = true) :=
                  Pr_prodW_fst (P := bernW (Pair m) p) (Q := bernW (Pair m) p) (isProb_bernW hp0 hp1)
                    (fun g₁ => ∀ q ∈ ({p1, p2} : Finset (Pair m)), g₁ q = true)
              _ = p ^ ({p1, p2} : Finset (Pair m)).card := Pr_bernW_all_true hp0 hp1 _
              _ = p ^ 2 := by rw [Finset.card_pair hp12]
          | inr b =>
            have hne1 : b ≠ π.2 e.1.1 := fun h => hvext (h ▸ Finset.mem_image_of_mem π.2 heI.1)
            have hne2 : b ≠ π.2 e.1.2 := fun h => hvext (h ▸ Finset.mem_image_of_mem π.2 heI.2)
            let p1 := mkEdge b (π.2 e.1.1) hne1
            let p2 := mkEdge b (π.2 e.1.2) hne2
            have hp12 : p1 ≠ p2 := by
              intro h
              unfold p1 p2 mkEdge at h
              split_ifs at h <;>
              · have hf := congr_arg (fun q : Pair m => q.1.1) h
                have hs := congr_arg (fun q : Pair m => q.1.2) h
                first | exact hneB hs | exact hne2 hf | exact hne1 hf.symm | exact hneB hf
            have hsub : ∀ g : GPair m, e ∈ pairsOf (XAll π g I (Sum.inr b)) →
                ∀ q ∈ ({p1, p2} : Finset (Pair m)), g.2 q = true := by
              intro g hmem q hq
              rw [XAll_inr] at hmem
              have h12 := (Finset.mem_filter.mp hmem).2
              have hadj1 := (Finset.mem_filter.mp h12.1).2
              have hadj2 := (Finset.mem_filter.mp h12.2).2
              rcases Finset.mem_insert.mp hq with rfl | hq
              · simpa [p1, gAdj, hne1] using hadj1
              · rw [Finset.mem_singleton.mp hq]; simpa [p2, gAdj, hne2] using hadj2
            calc Pr (gPairW m p) (fun g => e ∈ pairsOf (XAll π g I (Sum.inr b)))
                ≤ Pr (gPairW m p) (fun g => ∀ q ∈ ({p1, p2} : Finset (Pair m)), g.2 q = true) :=
                  Pr_mono hP hsub
              _ = Pr (bernW (Pair m) p) (fun g₂ => ∀ q ∈ ({p1, p2} : Finset (Pair m)), g₂ q = true) :=
                  Pr_prodW_snd (P := bernW (Pair m) p) (Q := bernW (Pair m) p) (isProb_bernW hp0 hp1)
                    (fun g₂ => ∀ q ∈ ({p1, p2} : Finset (Pair m)), g₂ q = true)
              _ = p ^ ({p1, p2} : Finset (Pair m)).card := Pr_bernW_all_true hp0 hp1 _
              _ = p ^ 2 := by rw [Finset.card_pair hp12]
      _ = (N : ℝ) * p ^ 2 := by simp [N]
      _ ≤ (2 * (m : ℝ)) * p ^ 2 := mul_le_mul_of_nonneg_right (by exact_mod_cast hNle2m) (sq_nonneg p)
      _ = 2 * (m : ℝ) * p ^ 2 := by ring
  -- Combine pointwise bound `Z(g) ≤ sameF.card + ∑ e ∈ diffF, 1[∃ v ∈ Vext, e ∈ pairsOf (XAll v)]`!
  have hpt : ∀ g : GPair m,
      (((SsetExt π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ) ≤
      (sameF.card : ℝ) + ∑ e ∈ diffF, (if ∃ v ∈ Vext, e ∈ pairsOf (XAll π g I v) then (1 : ℝ) else 0) := by
    intro g
    let U := (SsetExt π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))
    have hUsub : U ⊆ sameF ∪ diffF.filter (fun e => ∃ v ∈ Vext, e ∈ pairsOf (XAll π g I v)) := by
      intro e he
      obtain ⟨v, hv, hev⟩ := Finset.mem_biUnion.mp he
      have hvV : v ∈ Vext := Finset.mem_filter.mpr ⟨Finset.mem_univ v, (Finset.mem_filter.mp hv).2⟩
      have heI : e ∈ pairsOf I := by
        have hm := (Finset.mem_filter.mp hev).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ e,
          (Finset.mem_inter.mp hm.1).1, (Finset.mem_inter.mp hm.2).1⟩
      by_cases hsf : π.1 e.1.1 = π.1 e.1.2 ∨ π.2 e.1.1 = π.2 e.1.2
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heI, hsf⟩)
      · push Not at hsf
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨heI, hsf⟩, v, hvV, hev⟩)
    have hc := (Finset.card_le_card hUsub).trans (Finset.card_union_le _ _)
    have hcR : (U.card : ℝ) ≤ (sameF.card : ℝ) +
        ((diffF.filter (fun e => ∃ v ∈ Vext, e ∈ pairsOf (XAll π g I v))).card : ℝ) := by
      exact_mod_cast hc
    have hsum : ((diffF.filter (fun e => ∃ v ∈ Vext, e ∈ pairsOf (XAll π g I v))).card : ℝ) =
        ∑ e ∈ diffF, (if ∃ v ∈ Vext, e ∈ pairsOf (XAll π g I v) then (1 : ℝ) else 0) := by
      rw [Finset.card_filter]; push_cast; rfl
    rw [← hsum]
    exact hcR
  have hdiff_card : (diffF.card : ℝ) ≤ (k.choose 2 : ℝ) := by
    have h1 : diffF.card ≤ (pairsOf I).card := Finset.card_le_card (Finset.filter_subset _ _)
    rw [pairsOf_card, hI] at h1
    exact_mod_cast h1
  calc E (gPairW m p) (fun g => (((SsetExt π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ))
      ≤ E (gPairW m p) (fun g => (sameF.card : ℝ) +
          ∑ e ∈ diffF, (if ∃ v ∈ Vext, e ∈ pairsOf (XAll π g I v) then (1 : ℝ) else 0)) :=
        E_mono hP hpt
    _ = (sameF.card : ℝ) + ∑ e ∈ diffF, Pr (gPairW m p) (fun g => ∃ v ∈ Vext, e ∈ pairsOf (XAll π g I v)) := by
        rw [E_add, E_const hP, E_sum]
        refine congrArg ((sameF.card : ℝ) + ·) (Finset.sum_congr rfl fun e _ => ?_)
        rw [Pr_eq_E]
        refine Finset.sum_congr rfl fun g _ => ?_
        by_cases h : ∃ v ∈ Vext, e ∈ pairsOf (XAll π g I v) <;> simp [h]
    _ ≤ (k : ℝ) * (Fmax : ℝ) + ∑ _e ∈ diffF, (2 * (m : ℝ) * p ^ 2) :=
        add_le_add hsame_card (Finset.sum_le_sum hdiff_prob)
    _ = (k : ℝ) * (Fmax : ℝ) + (diffF.card : ℝ) * (2 * (m : ℝ) * p ^ 2) := by simp
    _ ≤ (k : ℝ) * (Fmax : ℝ) + (k.choose 2 : ℝ) * (2 * (m : ℝ) * p ^ 2) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hdiff_card (by positivity))

/-- Lemma 3.4 (`lem:small`, non-asymptotic fixed-`π`, fixed-`I` McDiarmid bound):
for fixed `π` with max fiber size `≤ Fmax`, fixed `I` of size `k`, `0 < t₃`, `0 ≤ t`, `0 < m`:
`Pr_{gPairW}(|(⋃_{v ∈ SsetExt} pairsOf (X_v))| ≥ k * Fmax + (k.choose 2) * (2 * m * p^2) + t)
  ≤ exp(-2 * t^2 / ((2 * m) * (t₃^2 / 2)^2))`. -/
lemma Pr_SsetExt_single_le {n m k Fmax : ℕ} {p t₃ t : ℝ}
    (hm : 0 < m) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht₃ : 0 < t₃) (ht : 0 ≤ t)
    (π : PiPair n m) (I : Finset (Fin n)) (hI : I.card = k)
    (hFR : ∀ r : Fin m, (fiber π.1 r).card ≤ Fmax)
    (hFB : ∀ b : Fin m, (fiber π.2 b).card ≤ Fmax) :
    Pr (gPairW m p) (fun g =>
      (k : ℝ) * (Fmax : ℝ) + (k.choose 2 : ℝ) * (2 * (m : ℝ) * p ^ 2) + t ≤
        (((SsetExt π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ)) ≤
      Real.exp (-2 * t ^ 2 / ((2 * (m : ℝ)) * (t₃ ^ 2 / 2) ^ 2)) := by
  classical
  have hP := isProb_gPairW (m := m) hp0 hp1
  let Vext : Finset (Fin m ⊕ Fin m) := Finset.univ.filter (fun v => match v with
    | Sum.inl r => r ∉ I.image π.1
    | Sum.inr b => b ∉ I.image π.2)
  set N := Vext.card
  -- Handle `N = 0` trivially (then `SsetExt = ∅`, card = 0).
  by_cases hN0 : N = 0
  · have hVemp : Vext = ∅ := Finset.card_eq_zero.mp hN0
    have hSemp : ∀ g, SsetExt π g I t₃ = ∅ := by
      intro g
      rw [Finset.eq_empty_iff_forall_notMem]
      intro v hv
      have hvV : v ∈ Vext := Finset.mem_filter.mpr ⟨Finset.mem_univ v, (Finset.mem_filter.mp hv).2⟩
      rw [hVemp] at hvV
      exact Finset.notMem_empty v hvV
    by_cases hzero : (k : ℝ) * (Fmax : ℝ) + (k.choose 2 : ℝ) * (2 * (m : ℝ) * p ^ 2) + t = 0
    · have ht0 : t = 0 := by
        have h1 : 0 ≤ (k : ℝ) * (Fmax : ℝ) := by positivity
        have h2 : 0 ≤ (k.choose 2 : ℝ) * (2 * (m : ℝ) * p ^ 2) := by positivity
        linarith
      subst ht0
      calc Pr (gPairW m p) _ ≤ 1 := Pr_le_one hP _
        _ = Real.exp (-2 * 0 ^ 2 / ((2 * (m : ℝ)) * (t₃ ^ 2 / 2) ^ 2)) := by simp
    · have hpos : 0 < (k : ℝ) * (Fmax : ℝ) + (k.choose 2 : ℝ) * (2 * (m : ℝ) * p ^ 2) + t :=
        lt_of_le_of_ne (by positivity) (Ne.symm hzero)
      have hfalse : Pr (gPairW m p) (fun g =>
          (k : ℝ) * (Fmax : ℝ) + (k.choose 2 : ℝ) * (2 * (m : ℝ) * p ^ 2) + t ≤
            (((SsetExt π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ)) = 0 := by
        rw [Pr_congr (B := fun _ => False) (fun g => by
          rw [hSemp g]; simp only [Finset.biUnion_empty, Finset.card_empty, Nat.cast_zero, iff_false, not_le]
          exact hpos), Pr_false]
      rw [hfalse]
      exact (Real.exp_pos _).le
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
  have hNle2m : N ≤ 2 * m := by
    calc N ≤ (Finset.univ : Finset (Fin m ⊕ Fin m)).card := Finset.card_le_univ _
      _ = 2 * m := by simp [Fintype.card_sum, Fintype.card_fin, two_mul]
  let eV : Fin N ≃ {v // v ∈ Vext} := (Fintype.equivFinOfCardEq (Fintype.card_coe Vext)).symm
  -- Define the McDiarmid function `fmc : (Fin N → (Fin m → Bool)) → ℝ` directly!
  let Xmc (W : Fin N → (Fin m → Bool)) (i : Fin N) : Finset (Fin n) :=
    match (eV i).1 with
    | Sum.inl _ => I.filter (fun x => W i (π.1 x) = true)
    | Sum.inr _ => I.filter (fun x => W i (π.2 x) = true)
  let Zmc (W : Fin N → (Fin m → Bool)) : Finset (Pair n) :=
    Finset.univ.biUnion (fun i : Fin N =>
      if ((Xmc W i).card : ℝ) ≤ t₃ then pairsOf (Xmc W i) else ∅)
  let fmc (W : Fin N → (Fin m → Bool)) : ℝ := ((Zmc W).card : ℝ)
  let wN : (Fin N → (Fin m → Bool)) → ℝ := piW (fun _ : Fin N => bernW (Fin m) p)
  have hw1 : IsProb (bernW (Fin m) p) := isProb_bernW hp0 hp1
  have hwN : IsProb wN := isProb_piW (fun _ => hw1)
  -- Step 1: Identify `E wN fmc` and `Pr wN (B ≤ fmc)` with `gPairW m p` via edge-coordinate embedding!
  -- Map `g : GPair m` to its restriction on edges incident to `Vext` and `π(I)`:
  -- Embed `(i, u) ∈ Q_W` into `Pair m ⊕ Pair m`!
  let Q_W : Finset (Fin N × Fin m) := Finset.univ.filter (fun iu =>
    match (eV iu.1).1 with
    | Sum.inl _ => iu.2 ∈ I.image π.1
    | Sum.inr _ => iu.2 ∈ I.image π.2)
  have hne_Q : ∀ iu : {iu // iu ∈ Q_W}, match (eV iu.1.1).1 with
      | Sum.inl r => r ≠ iu.1.2
      | Sum.inr b => b ≠ iu.1.2 := by
    intro ⟨⟨i, u⟩, hiu⟩
    have hmem := (Finset.mem_filter.mp hiu).2
    have hvext := (Finset.mem_filter.mp (eV i).2).2
    cases hv : (eV i).1 with
    | inl r =>
      simp only [hv] at hmem hvext ⊢
      intro h; exact hvext (h ▸ hmem)
    | inr b =>
      simp only [hv] at hmem hvext ⊢
      intro h; exact hvext (h ▸ hmem)
  let emb : {iu // iu ∈ Q_W} → Pair m ⊕ Pair m := fun iu =>
    match hv : (eV iu.1.1).1 with
    | Sum.inl r => Sum.inl (mkEdge r iu.1.2 (by have h := hne_Q iu; simp [hv] at h; exact h))
    | Sum.inr b => Sum.inr (mkEdge b iu.1.2 (by have h := hne_Q iu; simp [hv] at h; exact h))
  have hemb_inj : Function.Injective emb := by
    intro ⟨⟨i₁, u₁⟩, h1⟩ ⟨⟨i₂, u₂⟩, h2⟩ heq
    have hm1 := (Finset.mem_filter.mp h1).2
    have hm2 := (Finset.mem_filter.mp h2).2
    have hv1 := (Finset.mem_filter.mp (eV i₁).2).2
    have hv2 := (Finset.mem_filter.mp (eV i₂).2).2
    dsimp only [emb] at heq
    split at heq <;> split at heq
    · rename_i r₁ hr₁ r₂ hr₂
      simp only [hr₁] at hm1 hv1; simp only [hr₂] at hm2 hv2
      have hmk := Sum.inl.inj heq
      unfold mkEdge at hmk
      have hr_u : r₁ = r₂ ∧ u₁ = u₂ := by
        split_ifs at hmk <;>
        · simp only [Subtype.mk.injEq, Prod.mk.injEq] at hmk
          rcases hmk with ⟨hf, hs⟩
          first | exact ⟨hf, hs⟩
                | (rw [hf] at hv1; exact absurd hm2 hv1)
                | (rw [hs] at hv1; exact absurd hm2 hv1)
                | exact ⟨hs, hf⟩
      have hi : i₁ = i₂ := eV.injective (Subtype.ext (hr₁.trans (hr_u.1 ▸ hr₂.symm)))
      exact Subtype.ext (Prod.ext hi hr_u.2)
    · cases heq
    · cases heq
    · rename_i b₁ hb₁ b₂ hb₂
      simp only [hb₁] at hm1 hv1; simp only [hb₂] at hm2 hv2
      have hmk := Sum.inr.inj heq
      unfold mkEdge at hmk
      have hb_u : b₁ = b₂ ∧ u₁ = u₂ := by
        split_ifs at hmk <;>
        · simp only [Subtype.mk.injEq, Prod.mk.injEq] at hmk
          rcases hmk with ⟨hf, hs⟩
          first | exact ⟨hf, hs⟩
                | (rw [hf] at hv1; exact absurd hm2 hv1)
                | (rw [hs] at hv1; exact absurd hm2 hv1)
                | exact ⟨hs, hf⟩
      have hi : i₁ = i₂ := eV.injective (Subtype.ext (hb₁.trans (hb_u.1 ▸ hb₂.symm)))
      exact Subtype.ext (Prod.ext hi hb_u.2)
  let Q_G : Finset (Pair m ⊕ Pair m) := Finset.univ.image emb
  let eQ : {iu // iu ∈ Q_W} ≃ {e // e ∈ Q_G} :=
    Equiv.ofBijective (fun iu => ⟨emb iu, Finset.mem_image_of_mem emb (Finset.mem_univ iu)⟩)
      ⟨fun a b h => hemb_inj (congr_arg Subtype.val h),
       fun ⟨e, he⟩ => by obtain ⟨iu, _, rfl⟩ := Finset.mem_image.mp he; exact ⟨iu, rfl⟩⟩
  -- For any `f : Pair m ⊕ Pair m → Bool` and `W : Fin N → (Fin m → Bool)` agreeing on `eQ`,
  -- `Zmc W = (SsetExt π (gPairEquiv m f) I t₃).biUnion (fun v => pairsOf (XAll π (gPairEquiv m f) I v))`!
  -- Therefore the law of `(SsetExt.biUnion pairsOf).card` under `gPairW m p` equals the law of `fmc` under `wN`!
  have hlaw_E : ∀ Φ : ℝ → ℝ,
      E (gPairW m p) (fun g => Φ (((SsetExt π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ)) =
      E wN (fun W => Φ (fmc W)) := by
    intro Φ
    -- Define the common function on `y : {iu // iu ∈ Q_W} → Bool`!
    let Xy (y : {iu // iu ∈ Q_W} → Bool) (i : Fin N) : Finset (Fin n) :=
      match hv : (eV i).1 with
      | Sum.inl _ => I.filter (fun x =>
          if hx : x ∈ I then y ⟨(i, π.1 x), Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hv, Finset.mem_image_of_mem π.1 hx]⟩⟩ = true
          else False)
      | Sum.inr _ => I.filter (fun x =>
          if hx : x ∈ I then y ⟨(i, π.2 x), Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hv, Finset.mem_image_of_mem π.2 hx]⟩⟩ = true
          else False)
    let Zy (y : {iu // iu ∈ Q_W} → Bool) : ℝ :=
      ((Finset.univ.biUnion (fun i : Fin N =>
        if ((Xy y i).card : ℝ) ≤ t₃ then pairsOf (Xy y i) else ∅)).card : ℝ)
    -- Step A: `E (gPairW m p) (Φ ∘ Z_g) = E (bernW {iu // iu ∈ Q_W} p) (Φ ∘ Zy)`
    have hA : E (gPairW m p) (fun g => Φ (((SsetExt π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ)) =
        E (piW (fun _ : {iu // iu ∈ Q_W} => bern1 p)) (fun y => Φ (Zy y)) := by
      rw [← E_equiv (gPairEquiv m)]
      have hwt : (fun f : Pair m ⊕ Pair m → Bool => gPairW m p (gPairEquiv m f)) =
          piW (fun _ : Pair m ⊕ Pair m => bern1 p) := funext (gPairW_eq_bernW p)
      rw [hwt]
      have hdep_g : ∀ f : Pair m ⊕ Pair m → Bool,
          (((SsetExt π (gPairEquiv m f) I t₃).biUnion (fun v => pairsOf (XAll π (gPairEquiv m f) I v))).card : ℝ) =
          Zy (fun iu => f (eQ iu).1) := by
        intro f
        congr 1; congr 1
        have hXeq : ∀ i : Fin N, XAll π (gPairEquiv m f) I (eV i).1 = Xy (fun iu => f (eQ iu).1) i := by
          intro i
          have hvext := (Finset.mem_filter.mp (eV i).2).2
          dsimp only [Xy]
          split
          · rename_i r hr
            simp only [hr] at hvext
            conv_lhs => rw [hr, XAll_inl]
            refine Finset.ext fun x => ?_
            rw [XV, Finset.mem_filter, Finset.mem_filter]
            dsimp only [gPairEquiv, Equiv.coe_fn_mk]
            constructor
            · rintro ⟨hxI, hadj⟩
              refine ⟨hxI, ?_⟩
              rw [dif_pos hxI]
              have hne : r ≠ π.1 x := fun h => hvext (h ▸ Finset.mem_image_of_mem π.1 hxI)
              have hadj' : f (Sum.inl (mkEdge r (π.1 x) hne)) = true := by simpa [gAdj, hne] using hadj
              have hmemQ : (i, π.1 x) ∈ Q_W :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hr, Finset.mem_image_of_mem π.1 hxI]⟩
              have heQval : (eQ ⟨(i, π.1 x), hmemQ⟩).1 = Sum.inl (mkEdge r (π.1 x) hne) := by
                change emb ⟨(i, π.1 x), hmemQ⟩ = _; dsimp only [emb]; split
                · rename_i r' hr'; have : r' = r := Sum.inl.inj (hr'.symm.trans hr); subst this; rfl
                · rename_i b' hb'; exact absurd (hb'.symm.trans hr) (by simp)
              rwa [heQval]
            · rintro ⟨hxI, hy⟩
              rw [dif_pos hxI] at hy
              refine ⟨hxI, ?_⟩
              have hne : r ≠ π.1 x := fun h => hvext (h ▸ Finset.mem_image_of_mem π.1 hxI)
              have hmemQ : (i, π.1 x) ∈ Q_W :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hr, Finset.mem_image_of_mem π.1 hxI]⟩
              have heQval : (eQ ⟨(i, π.1 x), hmemQ⟩).1 = Sum.inl (mkEdge r (π.1 x) hne) := by
                change emb ⟨(i, π.1 x), hmemQ⟩ = _; dsimp only [emb]; split
                · rename_i r' hr'; have : r' = r := Sum.inl.inj (hr'.symm.trans hr); subst this; rfl
                · rename_i b' hb'; exact absurd (hb'.symm.trans hr) (by simp)
              rw [heQval] at hy
              simpa [gAdj, hne] using hy
          · rename_i b hb
            simp only [hb] at hvext
            conv_lhs => rw [hb, XAll_inr]
            refine Finset.ext fun x => ?_
            rw [XV, Finset.mem_filter, Finset.mem_filter]
            dsimp only [gPairEquiv, Equiv.coe_fn_mk]
            constructor
            · rintro ⟨hxI, hadj⟩
              refine ⟨hxI, ?_⟩
              rw [dif_pos hxI]
              have hne : b ≠ π.2 x := fun h => hvext (h ▸ Finset.mem_image_of_mem π.2 hxI)
              have hadj' : f (Sum.inr (mkEdge b (π.2 x) hne)) = true := by simpa [gAdj, hne] using hadj
              have hmemQ : (i, π.2 x) ∈ Q_W :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hb, Finset.mem_image_of_mem π.2 hxI]⟩
              have heQval : (eQ ⟨(i, π.2 x), hmemQ⟩).1 = Sum.inr (mkEdge b (π.2 x) hne) := by
                change emb ⟨(i, π.2 x), hmemQ⟩ = _; dsimp only [emb]; split
                · rename_i r' hr'; exact absurd (hr'.symm.trans hb) (by simp)
                · rename_i b' hb'; have : b' = b := Sum.inr.inj (hb'.symm.trans hb); subst this; rfl
              rwa [heQval]
            · rintro ⟨hxI, hy⟩
              rw [dif_pos hxI] at hy
              refine ⟨hxI, ?_⟩
              have hne : b ≠ π.2 x := fun h => hvext (h ▸ Finset.mem_image_of_mem π.2 hxI)
              have hmemQ : (i, π.2 x) ∈ Q_W :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hb, Finset.mem_image_of_mem π.2 hxI]⟩
              have heQval : (eQ ⟨(i, π.2 x), hmemQ⟩).1 = Sum.inr (mkEdge b (π.2 x) hne) := by
                change emb ⟨(i, π.2 x), hmemQ⟩ = _; dsimp only [emb]; split
                · rename_i r' hr'; exact absurd (hr'.symm.trans hb) (by simp)
                · rename_i b' hb'; have : b' = b := Sum.inr.inj (hb'.symm.trans hb); subst this; rfl
              rw [heQval] at hy
              simpa [gAdj, hne] using hy
        ext e
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, SsetExt, Sset, Finset.mem_filter]
        constructor
        · rintro ⟨v, ⟨hle, hvext⟩, hev⟩
          let i := eV.symm ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvext⟩⟩
          have hi : (eV i).1 = v := by simp [i]
          refine ⟨i, ?_⟩
          rw [← hXeq i, hi, if_pos hle]
          exact hev
        · rintro ⟨i, hei⟩
          split_ifs at hei with hle
          · refine ⟨(eV i).1, ⟨?_, (Finset.mem_filter.mp (eV i).2).2⟩, ?_⟩
            · rwa [hXeq i]
            · rwa [hXeq i]
          · exact absurd hei (Finset.notMem_empty e)
      simp_rw [hdep_g]
      rw [E_piW_depends_on (fun _ => isProb_bern1 hp0 hp1) Q_G (fun yG => Φ (Zy (fun iu => yG (eQ iu))))]
      let eFun : ({iu // iu ∈ Q_W} → Bool) ≃ ({e // e ∈ Q_G} → Bool) :=
        { toFun := fun y e => y (eQ.symm e)
          invFun := fun yG iu => yG (eQ iu)
          left_inv := fun y => by funext iu; simp
          right_inv := fun yG => by funext e; simp }
      rw [← E_equiv eFun]
      have hwt_e : (fun y : {iu // iu ∈ Q_W} → Bool =>
          piW (fun _ : {e // e ∈ Q_G} => bern1 p) (eFun y)) =
          piW (fun _ : {iu // iu ∈ Q_W} => bern1 p) := by
        funext y
        simp only [piW, eFun, Equiv.coe_fn_mk]
        exact Fintype.prod_equiv eQ.symm _ _ (fun _ => rfl)
      have hfn_e : (fun y : {iu // iu ∈ Q_W} → Bool => Φ (Zy (fun iu => eFun y (eQ iu)))) =
          fun y => Φ (Zy y) := by funext y; simp [eFun]
      rw [hwt_e, hfn_e]
    -- Step B: `E wN (Φ ∘ fmc) = E (bernW {iu // iu ∈ Q_W} p) (Φ ∘ Zy)`
    have hB : E wN (fun W => Φ (fmc W)) =
        E (piW (fun _ : {iu // iu ∈ Q_W} => bern1 p)) (fun y => Φ (Zy y)) := by
      let eCurry : (Fin N × Fin m → Bool) ≃ (Fin N → (Fin m → Bool)) := Equiv.curry _ _ _
      rw [← E_equiv eCurry]
      have hwt_c : (fun W : Fin N × Fin m → Bool => wN (eCurry W)) =
          piW (fun _ : Fin N × Fin m => bern1 p) := by
        funext W
        simp [wN, bernW, piW, eCurry, Fintype.prod_prod_type]
      rw [hwt_c]
      have hdep_W : ∀ W : Fin N × Fin m → Bool, fmc (eCurry W) = Zy (fun iu => W iu.1) := by
        intro W
        dsimp only [fmc, Zmc, Zy]
        congr 1; congr 1
        refine Finset.biUnion_congr rfl fun i _ => ?_
        have hX : Xmc (eCurry W) i = Xy (fun iu => W iu.1) i := by
          dsimp only [Xmc, Xy, eCurry]
          split
          · rename_i r hr
            simp only [hr]
            refine Finset.ext fun x => ?_
            simp only [Finset.mem_filter, Equiv.curry_apply]
            constructor
            · rintro ⟨hxI, hW⟩; exact ⟨hxI, by rw [dif_pos hxI]; exact hW⟩
            · rintro ⟨hxI, hW⟩; rw [dif_pos hxI] at hW; exact ⟨hxI, hW⟩
          · rename_i b hb
            simp only [hb]
            refine Finset.ext fun x => ?_
            simp only [Finset.mem_filter, Equiv.curry_apply]
            constructor
            · rintro ⟨hxI, hW⟩; exact ⟨hxI, by rw [dif_pos hxI]; exact hW⟩
            · rintro ⟨hxI, hW⟩; rw [dif_pos hxI] at hW; exact ⟨hxI, hW⟩
        rw [hX]
      simp_rw [hdep_W]
      exact E_piW_depends_on (fun _ => isProb_bern1 hp0 hp1) Q_W (fun y => Φ (Zy y))
    exact hA.trans hB.symm
  -- Step 2: Bounded differences of `fmc` (`c = t₃^2 / 2`)!
  have hdiff : ∀ (W : Fin N → (Fin m → Bool)) (i : Fin N) (a : Fin m → Bool),
      |fmc W - fmc (Function.update W i a)| ≤ t₃ ^ 2 / 2 := by
    intro W i a
    let term (W' : Fin N → (Fin m → Bool)) (j : Fin N) : Finset (Pair n) :=
      if ((Xmc W' j).card : ℝ) ≤ t₃ then pairsOf (Xmc W' j) else ∅
    have hterm_card : ∀ W' j, ((term W' j).card : ℝ) ≤ t₃ ^ 2 / 2 := by
      intro W' j
      dsimp only [term]
      split_ifs with hle
      · rw [pairsOf_card]
        have h1 := choose_two_le_half_sq (Xmc W' j).card
        have h0 : (0 : ℝ) ≤ ((Xmc W' j).card : ℝ) := Nat.cast_nonneg _
        nlinarith
      · simp; positivity
    have hsame : ∀ j : Fin N, j ≠ i → term (Function.update W i a) j = term W j := by
      intro j hji
      have hX : Xmc (Function.update W i a) j = Xmc W j := by
        dsimp only [Xmc]
        split <;> simp [Function.update, hji]
      simp [term, hX]
    have hbound1 : ∀ W₁ W₂ : Fin N → (Fin m → Bool),
        (∀ j, j ≠ i → term W₁ j = term W₂ j) →
        ((Zmc W₁).card : ℝ) - ((Zmc W₂).card : ℝ) ≤ t₃ ^ 2 / 2 := by
      intro W₁ W₂ heq
      let rest : Finset (Pair n) := (Finset.univ.erase i).biUnion (term W₁)
      have h1 : Zmc W₁ = term W₁ i ∪ rest := by
        dsimp only [Zmc, rest]
        conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ i)]
        rw [Finset.biUnion_insert]
      have h2 : rest ⊆ Zmc W₂ := by
        intro e he
        obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp he
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        rw [heq j hji] at hej
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hej⟩
      have hc1 : (Zmc W₁).card ≤ (term W₁ i).card + rest.card := by
        rw [h1]; exact Finset.card_union_le _ _
      have hc2 : rest.card ≤ (Zmc W₂).card := Finset.card_le_card h2
      have hleR : ((Zmc W₁).card : ℝ) ≤ ((term W₁ i).card : ℝ) + ((Zmc W₂).card : ℝ) := by
        exact_mod_cast (hc1.trans (Nat.add_le_add_left hc2 _))
      linarith [hterm_card W₁ i]
    rw [abs_le]
    constructor
    · linarith [hbound1 (Function.update W i a) W hsame]
    · linarith [hbound1 W (Function.update W i a) (fun j hj => (hsame j hj).symm)]
  -- Step 3: Upper bound `E wN fmc = E (gPairW m p) Z ≤ k * Fmax + (k.choose 2) * (2 * m * p^2)`!
  have hE_le : E wN fmc ≤ (k : ℝ) * (Fmax : ℝ) + (k.choose 2 : ℝ) * (2 * (m : ℝ) * p ^ 2) := by
    have hlaw_id := hlaw_E id
    dsimp only [id] at hlaw_id
    rw [← hlaw_id]
    exact E_SsetExt_le hp0 hp1 π I hI hFR hFB
  -- Step 4: Apply `mcdiarmid_upper` to `fmc`!
  have hPr_eq : Pr (gPairW m p) (fun g =>
        (k : ℝ) * (Fmax : ℝ) + (k.choose 2 : ℝ) * (2 * (m : ℝ) * p ^ 2) + t ≤
          (((SsetExt π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ)) =
      Pr wN (fun W => (k : ℝ) * (Fmax : ℝ) + (k.choose 2 : ℝ) * (2 * (m : ℝ) * p ^ 2) + t ≤ fmc W) := by
    rw [Pr_eq_E, Pr_eq_E]
    exact hlaw_E (fun r => by classical exact if (k : ℝ) * (Fmax : ℝ) + (k.choose 2 : ℝ) * (2 * (m : ℝ) * p ^ 2) + t ≤ r then 1 else 0)
  rw [hPr_eq]
  have hc_pos : 0 < t₃ ^ 2 / 2 := by positivity
  have hmcd := mcdiarmid_upper hw1 hNpos fmc hc_pos ht hdiff
  calc Pr wN (fun W => (k : ℝ) * (Fmax : ℝ) + (k.choose 2 : ℝ) * (2 * (m : ℝ) * p ^ 2) + t ≤ fmc W)
      ≤ Pr wN (fun W => E wN fmc + t ≤ fmc W) := Pr_mono hwN fun W hW => by linarith
    _ ≤ Real.exp (-2 * t ^ 2 / ((N : ℝ) * (t₃ ^ 2 / 2) ^ 2)) := hmcd
    _ ≤ Real.exp (-2 * t ^ 2 / ((2 * (m : ℝ)) * (t₃ ^ 2 / 2) ^ 2)) := by
        apply Real.exp_le_exp.mpr
        have hNleR : (N : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hNle2m
        have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
        have hden1 : 0 < (N : ℝ) * (t₃ ^ 2 / 2) ^ 2 := by positivity
        have hden2 : 0 < (2 * (m : ℝ)) * (t₃ ^ 2 / 2) ^ 2 := by positivity
        have hdiv : 2 * t ^ 2 / ((2 * (m : ℝ)) * (t₃ ^ 2 / 2) ^ 2) ≤
            2 * t ^ 2 / ((N : ℝ) * (t₃ ^ 2 / 2) ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) hden1 (by nlinarith [sq_pos_of_pos hc_pos])
        have heq1 : -2 * t ^ 2 / ((N : ℝ) * (t₃ ^ 2 / 2) ^ 2) = -(2 * t ^ 2 / ((N : ℝ) * (t₃ ^ 2 / 2) ^ 2)) := by ring
        have heq2 : -2 * t ^ 2 / ((2 * (m : ℝ)) * (t₃ ^ 2 / 2) ^ 2) = -(2 * t ^ 2 / ((2 * (m : ℝ)) * (t₃ ^ 2 / 2) ^ 2)) := by ring
        linarith

/-- Union bound over all `k`-subsets `I` for Lemma 3.4 (`lem:small`). -/
lemma Pr_not_smallGood {n m k Fmax : ℕ} {p t₃ t : ℝ}
    (hm : 0 < m) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht₃ : 0 < t₃) (ht : 0 ≤ t)
    (π : PiPair n m)
    (hFR : ∀ r : Fin m, (fiber π.1 r).card ≤ Fmax)
    (hFB : ∀ b : Fin m, (fiber π.2 b).card ≤ Fmax) :
    Pr (gPairW m p) (fun g => ∃ I : Finset (Fin n), I.card = k ∧
      (k : ℝ) * t₃ ^ 2 + (k : ℝ) * (Fmax : ℝ) + (k.choose 2 : ℝ) * (2 * (m : ℝ) * p ^ 2) + t <
        (((Sset π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ)) ≤
      (n.choose k : ℝ) * Real.exp (-2 * t ^ 2 / ((2 * (m : ℝ)) * (t₃ ^ 2 / 2) ^ 2)) := by
  classical
  have hP := isProb_gPairW (m := m) hp0 hp1
  have himp : ∀ g : GPair m,
      (∃ I : Finset (Fin n), I.card = k ∧
        (k : ℝ) * t₃ ^ 2 + (k : ℝ) * (Fmax : ℝ) + (k.choose 2 : ℝ) * (2 * (m : ℝ) * p ^ 2) + t <
          (((Sset π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ)) →
      ∃ I ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (k : ℝ) * (Fmax : ℝ) + (k.choose 2 : ℝ) * (2 * (m : ℝ) * p ^ 2) + t ≤
          (((SsetExt π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ) := by
    intro g ⟨I, hIk, hgt⟩
    refine ⟨I, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ I, hIk⟩, ?_⟩
    have hsplit : Sset π g I t₃ ⊆ SsetInt π g I t₃ ∪ SsetExt π g I t₃ := by
      intro v hv
      cases v with
      | inl r =>
        by_cases hr : r ∈ I.image π.1
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv, hr⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv, hr⟩)
      | inr b =>
        by_cases hb : b ∈ I.image π.2
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv, hb⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv, hb⟩)
    have hcard_le : ((Sset π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card ≤
        ((SsetInt π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card +
        ((SsetExt π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card := by
      calc ((Sset π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card
          ≤ ((SsetInt π g I t₃ ∪ SsetExt π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card :=
            Finset.card_le_card (Finset.biUnion_subset_biUnion_of_subset_left _ hsplit)
        _ = ((SsetInt π g I t₃).biUnion (fun v => pairsOf (XAll π g I v)) ∪
             (SsetExt π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card := by
            rw [Finset.union_biUnion]
        _ ≤ _ := Finset.card_union_le _ _
    have hcard_leR : (((Sset π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ) ≤
        (((SsetInt π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ) +
        (((SsetExt π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ) := by
      exact_mod_cast hcard_le
    have hint := card_SsetInt_pairs_le ht₃.le π g I hIk
    linarith
  calc Pr (gPairW m p) _
      ≤ Pr (gPairW m p) (fun g => ∃ I ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          (k : ℝ) * (Fmax : ℝ) + (k.choose 2 : ℝ) * (2 * (m : ℝ) * p ^ 2) + t ≤
            (((SsetExt π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ)) :=
        Pr_mono hP himp
    _ ≤ ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          Pr (gPairW m p) (fun g =>
            (k : ℝ) * (Fmax : ℝ) + (k.choose 2 : ℝ) * (2 * (m : ℝ) * p ^ 2) + t ≤
              (((SsetExt π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ)) :=
        Pr_exists_le hP _ _
    _ ≤ ∑ _I ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          Real.exp (-2 * t ^ 2 / ((2 * (m : ℝ)) * (t₃ ^ 2 / 2) ^ 2)) :=
        Finset.sum_le_sum fun I hI =>
          Pr_SsetExt_single_le hm hp0 hp1 ht₃ ht π I (Finset.mem_powersetCard.mp hI).2 hFR hFB
    _ = (n.choose k : ℝ) * Real.exp (-2 * t ^ 2 / ((2 * (m : ℝ)) * (t₃ ^ 2 / 2) ^ 2)) := by
        simp [Finset.card_powersetCard]

end Lemma34Small

end Erdos1013ClosedPairs


namespace Erdos1013RISI

open Finset BigOperators Erdos1013Prob Erdos1013Model Erdos1013ClosedPairs

section AdaptiveConditioning

/-- Coordinatewise merge: take `x₀` on `S` and `y` outside `S`. -/
def mergeOn {ι : Type*} [DecidableEq ι] (S : Finset ι) (x₀ y : ι → Bool) (i : ι) : Bool :=
  if i ∈ S then x₀ i else y i

lemma mergeOn_mem {ι : Type*} [DecidableEq ι] (S : Finset ι) (x₀ y : ι → Bool) {i : ι} (hi : i ∈ S) :
    mergeOn S x₀ y i = x₀ i := if_pos hi

lemma mergeOn_notMem {ι : Type*} [DecidableEq ι] (S : Finset ι) (x₀ y : ι → Bool) {i : ι} (hi : i ∉ S) :
    mergeOn S x₀ y i = y i := if_neg hi

/-- Single-stage conditioning identity under `bernW ι p` using `mergeOn`. -/
lemma Pr_bernW_mergeOn {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset ι) (A : (ι → Bool) → Prop) :
    Pr (bernW ι p) A =
      E (bernW ι p) (fun x₀ => Pr (bernW ι p) (fun y => A (mergeOn S x₀ y))) := by
  have hP1 : IsProb (piW (fun _ : {i // i ∈ S} => bern1 p)) := isProb_piW (fun _ => isProb_bern1 hp0 hp1)
  have hP2 : IsProb (piW (fun _ : {i // i ∉ S} => bern1 p)) := isProb_piW (fun _ => isProb_bern1 hp0 hp1)
  have hmerge_split : ∀ (x₁ : {i // i ∈ S} → Bool) (x₂ : {i // i ∉ S} → Bool)
      (y₁ : {i // i ∈ S} → Bool) (y₂ : {i // i ∉ S} → Bool),
      mergeOn S ((splitPiEquiv (α := fun _ => Bool) S).symm (x₁, x₂))
                ((splitPiEquiv (α := fun _ => Bool) S).symm (y₁, y₂)) =
      (splitPiEquiv (α := fun _ => Bool) S).symm (x₁, y₂) := by
    intro x₁ x₂ y₁ y₂
    funext i
    by_cases hi : i ∈ S
    · simp [mergeOn, splitPiEquiv, hi]
    · simp [mergeOn, splitPiEquiv, hi]
  unfold bernW
  rw [Pr_piW_split (fun _ : ι => bern1 p) S, E_piW_split (fun _ : ι => bern1 p) S]
  refine Finset.sum_congr rfl fun x₁ _ => ?_
  dsimp only
  congr 1
  have hinner : ∀ x₂ : {i // i ∉ S} → Bool,
      Pr (piW (fun _ : ι => bern1 p)) (fun y =>
        A (mergeOn S ((splitPiEquiv (α := fun _ => Bool) S).symm (x₁, x₂)) y)) =
      Pr (piW (fun _ : {i // i ∉ S} => bern1 p)) (fun y₂ =>
        A ((splitPiEquiv (α := fun _ => Bool) S).symm (x₁, y₂))) := by
    intro x₂
    rw [Pr_piW_split (fun _ : ι => bern1 p) S]
    have hconst : ∀ y₁ : {i // i ∈ S} → Bool,
        Pr (piW (fun _ : {i // i ∉ S} => bern1 p)) (fun y₂ =>
          A (mergeOn S ((splitPiEquiv (α := fun _ => Bool) S).symm (x₁, x₂))
                       ((splitPiEquiv (α := fun _ => Bool) S).symm (y₁, y₂)))) =
        Pr (piW (fun _ : {i // i ∉ S} => bern1 p)) (fun y₂ =>
          A ((splitPiEquiv (α := fun _ => Bool) S).symm (x₁, y₂))) := by
      intro y₁
      refine Pr_congr fun y₂ => by rw [hmerge_split]
    simp_rw [hconst]
    exact E_const hP1 _
  simp_rw [hinner]
  exact (E_const hP2 _).symm

/-- 3-stage adaptive conditioning upper bound under `bernW ι p`. -/
lemma Pr_bernW_adaptive3_le {ι : Type*} [Fintype ι] [DecidableEq ι] {p B : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Q₁ : Finset ι)
    (Q₂ : (ι → Bool) → Finset ι)
    (Q₃ : (ι → Bool) → Finset ι)
    (hQ₂ : ∀ x y, (∀ i ∈ Q₁, x i = y i) → Q₂ x = Q₂ y)
    (hQ₃ : ∀ x y, (∀ i ∈ Q₁ ∪ Q₂ x, x i = y i) → Q₃ x = Q₃ y)
    (A : (ι → Bool) → Prop)
    (hbound : ∀ x₀ : ι → Bool,
      Pr (bernW ι p) (fun y => A (mergeOn (Q₁ ∪ Q₂ x₀ ∪ Q₃ x₀) x₀ y)) ≤ B) :
    Pr (bernW ι p) A ≤ B := by
  have hP := isProb_bernW (ι := ι) hp0 hp1
  rw [Pr_bernW_mergeOn hp0 hp1 Q₁]
  calc E (bernW ι p) (fun x₁ => Pr (bernW ι p) (fun y₁ => A (mergeOn Q₁ x₁ y₁)))
      ≤ E (bernW ι p) (fun _ => B) := by
        refine E_mono hP fun x₁ => ?_
        set S₂ := Q₂ x₁
        rw [Pr_bernW_mergeOn hp0 hp1 (Q₁ ∪ S₂)]
        calc E (bernW ι p) (fun x₂ => Pr (bernW ι p) (fun y₂ => A (mergeOn Q₁ x₁ (mergeOn (Q₁ ∪ S₂) x₂ y₂))))
            ≤ E (bernW ι p) (fun _ => B) := by
              refine E_mono hP fun x₂ => ?_
              let w₂ : ι → Bool := mergeOn Q₁ x₁ x₂
              have hw₂_eq : ∀ y₂, mergeOn Q₁ x₁ (mergeOn (Q₁ ∪ S₂) x₂ y₂) = mergeOn (Q₁ ∪ S₂) w₂ y₂ := by
                intro y₂; funext i
                by_cases h1 : i ∈ Q₁
                · simp [mergeOn, w₂, h1]
                · by_cases h2 : i ∈ S₂
                  · simp [mergeOn, w₂, h1, h2]
                  · simp [mergeOn, w₂, h1, h2]
              have hQ₂_w₂ : Q₂ w₂ = S₂ := hQ₂ w₂ x₁ (fun i hi => mergeOn_mem Q₁ x₁ x₂ hi)
              set S₃ := Q₃ w₂
              rw [Pr_congr (fun y₂ => by rw [hw₂_eq y₂]), Pr_bernW_mergeOn hp0 hp1 (Q₁ ∪ S₂ ∪ S₃)]
              calc E (bernW ι p) (fun x₃ => Pr (bernW ι p) (fun y₃ =>
                    A (mergeOn (Q₁ ∪ S₂) w₂ (mergeOn (Q₁ ∪ S₂ ∪ S₃) x₃ y₃))))
                  ≤ E (bernW ι p) (fun _ => B) := by
                    refine E_mono hP fun x₃ => ?_
                    let x₀ : ι → Bool := mergeOn (Q₁ ∪ S₂) w₂ x₃
                    have hx₀_eq : ∀ y₃, mergeOn (Q₁ ∪ S₂) w₂ (mergeOn (Q₁ ∪ S₂ ∪ S₃) x₃ y₃) =
                        mergeOn (Q₁ ∪ S₂ ∪ S₃) x₀ y₃ := by
                      intro y₃; funext i
                      by_cases h12 : i ∈ Q₁ ∪ S₂
                      · have h123 : i ∈ Q₁ ∪ S₂ ∪ S₃ := Finset.mem_union_left S₃ h12
                        simp only [mergeOn, x₀, if_pos h12, if_pos h123]
                      · by_cases h3 : i ∈ S₃
                        · have h123 : i ∈ Q₁ ∪ S₂ ∪ S₃ := Finset.mem_union_right _ h3
                          simp only [mergeOn, x₀, if_neg h12, if_pos h123]
                        · have h123 : i ∉ Q₁ ∪ S₂ ∪ S₃ := fun h =>
                            (Finset.mem_union.mp h).elim h12 h3
                          simp only [mergeOn, x₀, if_neg h12, if_neg h123]
                    have hQ₂_x₀ : Q₂ x₀ = S₂ := by
                      rw [← hQ₂_w₂]
                      exact hQ₂ x₀ w₂ (fun i hi => mergeOn_mem (Q₁ ∪ S₂) w₂ x₃ (Finset.mem_union_left S₂ hi))
                    have hQ₃_x₀ : Q₃ x₀ = S₃ := by
                      apply hQ₃ x₀ w₂
                      intro i hi
                      rw [hQ₂_x₀] at hi
                      exact mergeOn_mem (Q₁ ∪ S₂) w₂ x₃ hi
                    have hQ_eq : Q₁ ∪ S₂ ∪ S₃ = Q₁ ∪ Q₂ x₀ ∪ Q₃ x₀ := by rw [hQ₂_x₀, hQ₃_x₀]
                    rw [Pr_congr (fun y₃ => by rw [hx₀_eq y₃, hQ_eq])]
                    exact hbound x₀
                _ = B := E_const hP B
          _ = B := E_const hP B
    _ = B := E_const hP B

/-- Binomial-theorem sum over ordered pairs `u₂ ≤ u₁`:
`∑_{u₁ ≤ M₁} ∑_{u₂ ≤ min u₁ M₂} C(M₁, u₁) p^{u₁} C(M₂, u₂) p^{u₂} (1 - p)^Z
  ≤ exp((M₁ / r + r * M₂) * p - p * Z)` for `0 ≤ p ≤ 1`, `0 < r ≤ 1`. -/
lemma binom_sum_ordered_le {p r : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (M₁ M₂ Z : ℕ) :
    ∑ u₁ ∈ Finset.range (M₁ + 1), ∑ u₂ ∈ Finset.range (min u₁ M₂ + 1),
      (M₁.choose u₁ : ℝ) * p ^ u₁ * ((M₂.choose u₂ : ℝ) * p ^ u₂) * (1 - p) ^ Z ≤
      Real.exp (((M₁ : ℝ) / r + r * (M₂ : ℝ)) * p - p * (Z : ℝ)) := by
  have h1mp0 : 0 ≤ 1 - p := by linarith
  have hterm : ∀ u₁ ∈ Finset.range (M₁ + 1), ∀ u₂ ∈ Finset.range (min u₁ M₂ + 1),
      (M₁.choose u₁ : ℝ) * p ^ u₁ * ((M₂.choose u₂ : ℝ) * p ^ u₂) * (1 - p) ^ Z ≤
      ((M₁.choose u₁ : ℝ) * (p / r) ^ u₁) * ((M₂.choose u₂ : ℝ) * (r * p) ^ u₂) * (1 - p) ^ Z := by
    intro u₁ _ u₂ hu₂
    have hu₂_le : u₂ ≤ u₁ := by
      have := Finset.mem_range.mp hu₂
      omega
    have hrpow : r ^ (u₁ - u₂) ≤ 1 := pow_le_one₀ hr0.le hr1
    have hscale : p ^ u₁ * p ^ u₂ ≤ (p / r) ^ u₁ * (r * p) ^ u₂ := by
      have hru₁ : r ^ u₁ ≠ 0 := pow_ne_zero u₁ hr0.ne'
      have hru_eq : r ^ u₁ = r ^ (u₁ - u₂) * r ^ u₂ := by
        rw [← pow_add, Nat.sub_add_cancel hu₂_le]
      rw [div_pow, mul_pow]
      have hlhs : (p ^ u₁ / r ^ u₁) * (r ^ u₂ * p ^ u₂) = (p ^ u₁ * p ^ u₂) / r ^ (u₁ - u₂) := by
        rw [hru_eq]; field_simp [pow_ne_zero _ hr0.ne']
      rw [hlhs, le_div_iff₀ (pow_pos hr0 _)]
      have hnn : 0 ≤ p ^ u₁ * p ^ u₂ := by positivity
      nlinarith
    have hcoeff : 0 ≤ (M₁.choose u₁ : ℝ) * (M₂.choose u₂ : ℝ) * (1 - p) ^ Z := by positivity
    calc (M₁.choose u₁ : ℝ) * p ^ u₁ * ((M₂.choose u₂ : ℝ) * p ^ u₂) * (1 - p) ^ Z
        = ((M₁.choose u₁ : ℝ) * (M₂.choose u₂ : ℝ) * (1 - p) ^ Z) * (p ^ u₁ * p ^ u₂) := by ring
      _ ≤ ((M₁.choose u₁ : ℝ) * (M₂.choose u₂ : ℝ) * (1 - p) ^ Z) * ((p / r) ^ u₁ * (r * p) ^ u₂) :=
          mul_le_mul_of_nonneg_left hscale hcoeff
      _ = ((M₁.choose u₁ : ℝ) * (p / r) ^ u₁) * ((M₂.choose u₂ : ℝ) * (r * p) ^ u₂) * (1 - p) ^ Z := by ring
  have hsum_le : ∑ u₁ ∈ Finset.range (M₁ + 1), ∑ u₂ ∈ Finset.range (min u₁ M₂ + 1),
      (M₁.choose u₁ : ℝ) * p ^ u₁ * ((M₂.choose u₂ : ℝ) * p ^ u₂) * (1 - p) ^ Z ≤
      (∑ u₁ ∈ Finset.range (M₁ + 1), (M₁.choose u₁ : ℝ) * (p / r) ^ u₁) *
      (∑ u₂ ∈ Finset.range (M₂ + 1), (M₂.choose u₂ : ℝ) * (r * p) ^ u₂) * (1 - p) ^ Z := by
    calc ∑ u₁ ∈ Finset.range (M₁ + 1), ∑ u₂ ∈ Finset.range (min u₁ M₂ + 1),
          (M₁.choose u₁ : ℝ) * p ^ u₁ * ((M₂.choose u₂ : ℝ) * p ^ u₂) * (1 - p) ^ Z
        ≤ ∑ u₁ ∈ Finset.range (M₁ + 1), ∑ u₂ ∈ Finset.range (min u₁ M₂ + 1),
            ((M₁.choose u₁ : ℝ) * (p / r) ^ u₁) * ((M₂.choose u₂ : ℝ) * (r * p) ^ u₂) * (1 - p) ^ Z :=
          Finset.sum_le_sum fun u₁ hu₁ => Finset.sum_le_sum fun u₂ hu₂ => hterm u₁ hu₁ u₂ hu₂
      _ ≤ ∑ u₁ ∈ Finset.range (M₁ + 1), ∑ u₂ ∈ Finset.range (M₂ + 1),
            ((M₁.choose u₁ : ℝ) * (p / r) ^ u₁) * ((M₂.choose u₂ : ℝ) * (r * p) ^ u₂) * (1 - p) ^ Z := by
          refine Finset.sum_le_sum fun u₁ _ => Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          exact Finset.range_mono (Nat.add_le_add_right (min_le_right u₁ M₂) 1)
      _ = (∑ u₁ ∈ Finset.range (M₁ + 1), (M₁.choose u₁ : ℝ) * (p / r) ^ u₁) *
          (∑ u₂ ∈ Finset.range (M₂ + 1), (M₂.choose u₂ : ℝ) * (r * p) ^ u₂) * (1 - p) ^ Z := by
          rw [Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun u₁ _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
  have hbin1 : ∑ u₁ ∈ Finset.range (M₁ + 1), (M₁.choose u₁ : ℝ) * (p / r) ^ u₁ = (1 + p / r) ^ M₁ := by
    have h := add_pow (p / r) (1 : ℝ) M₁
    rw [add_comm] at h
    rw [h]
    refine Finset.sum_congr rfl fun u _ => by simp [mul_comm]
  have hbin2 : ∑ u₂ ∈ Finset.range (M₂ + 1), (M₂.choose u₂ : ℝ) * (r * p) ^ u₂ = (1 + r * p) ^ M₂ := by
    have h := add_pow (r * p) (1 : ℝ) M₂
    rw [add_comm] at h
    rw [h]
    refine Finset.sum_congr rfl fun u _ => by simp [mul_comm]
  have he1 : (1 + p / r) ^ M₁ ≤ Real.exp ((M₁ : ℝ) * (p / r)) := by
    calc (1 + p / r) ^ M₁ ≤ (Real.exp (p / r)) ^ M₁ :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (p / r)]) M₁
      _ = Real.exp ((M₁ : ℝ) * (p / r)) := (Real.exp_nat_mul _ _).symm
  have he2 : (1 + r * p) ^ M₂ ≤ Real.exp ((M₂ : ℝ) * (r * p)) := by
    calc (1 + r * p) ^ M₂ ≤ (Real.exp (r * p)) ^ M₂ :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (r * p)]) M₂
      _ = Real.exp ((M₂ : ℝ) * (r * p)) := (Real.exp_nat_mul _ _).symm
  have he3 : (1 - p) ^ Z ≤ Real.exp (-p * (Z : ℝ)) := by
    calc (1 - p) ^ Z ≤ (Real.exp (-p)) ^ Z :=
          pow_le_pow_left₀ h1mp0 (by linarith [Real.add_one_le_exp (-p)]) Z
      _ = Real.exp ((Z : ℝ) * (-p)) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp (-p * (Z : ℝ)) := by congr 1; ring
  calc ∑ u₁ ∈ Finset.range (M₁ + 1), ∑ u₂ ∈ Finset.range (min u₁ M₂ + 1),
        (M₁.choose u₁ : ℝ) * p ^ u₁ * ((M₂.choose u₂ : ℝ) * p ^ u₂) * (1 - p) ^ Z
      ≤ (1 + p / r) ^ M₁ * (1 + r * p) ^ M₂ * (1 - p) ^ Z := by rw [← hbin1, ← hbin2]; exact hsum_le
    _ ≤ Real.exp ((M₁ : ℝ) * (p / r)) * Real.exp ((M₂ : ℝ) * (r * p)) * Real.exp (-p * (Z : ℝ)) := by
        exact mul_le_mul (mul_le_mul he1 he2 (by positivity) (Real.exp_pos _).le)
          he3 (pow_nonneg h1mp0 Z) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = Real.exp (((M₁ : ℝ) / r + r * (M₂ : ℝ)) * p - p * (Z : ℝ)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1; ring

end AdaptiveConditioning

section Lemma41RISI

/-- Lexicographic sorted list of a finset `E : Finset (Pair m)` by `pairRank`. -/
def sortPairs {m : ℕ} (E : Finset (Pair m)) : List (Pair m) :=
  haveI : IsTrans (Pair m) (fun a b => pairRank a ≤ pairRank b) := ⟨fun _ _ _ h1 h2 => le_trans h1 h2⟩
  haveI : Std.Antisymm (fun a b : Pair m => pairRank a ≤ pairRank b) := ⟨fun _ _ h1 h2 => pairRank_inj (le_antisymm h1 h2)⟩
  haveI : Std.Total (fun a b : Pair m => pairRank a ≤ pairRank b) := ⟨fun a b => le_total (pairRank a) (pairRank b)⟩
  E.sort (fun a b => pairRank a ≤ pairRank b)

lemma sortPairs_nodup {m : ℕ} (E : Finset (Pair m)) : (sortPairs E).Nodup := by
  have : IsTrans (Pair m) (fun a b => pairRank a ≤ pairRank b) := ⟨fun _ _ _ h1 h2 => le_trans h1 h2⟩
  have : Std.Antisymm (fun a b : Pair m => pairRank a ≤ pairRank b) := ⟨fun _ _ h1 h2 => pairRank_inj (le_antisymm h1 h2)⟩
  have : Std.Total (fun a b : Pair m => pairRank a ≤ pairRank b) := ⟨fun a b => le_total (pairRank a) (pairRank b)⟩
  exact Finset.sort_nodup E _

lemma mem_sortPairs {m : ℕ} (E : Finset (Pair m)) (e : Pair m) : e ∈ sortPairs E ↔ e ∈ E := by
  have : IsTrans (Pair m) (fun a b => pairRank a ≤ pairRank b) := ⟨fun _ _ _ h1 h2 => le_trans h1 h2⟩
  have : Std.Antisymm (fun a b : Pair m => pairRank a ≤ pairRank b) := ⟨fun _ _ h1 h2 => pairRank_inj (le_antisymm h1 h2)⟩
  have : Std.Total (fun a b : Pair m => pairRank a ≤ pairRank b) := ⟨fun a b => le_total (pairRank a) (pairRank b)⟩
  exact Finset.mem_sort _

lemma sortPairs_length {m : ℕ} (E : Finset (Pair m)) : (sortPairs E).length = E.card := by
  have : IsTrans (Pair m) (fun a b => pairRank a ≤ pairRank b) := ⟨fun _ _ _ h1 h2 => le_trans h1 h2⟩
  have : Std.Antisymm (fun a b : Pair m => pairRank a ≤ pairRank b) := ⟨fun _ _ h1 h2 => pairRank_inj (le_antisymm h1 h2)⟩
  have : Std.Total (fun a b : Pair m => pairRank a ≤ pairRank b) := ⟨fun a b => le_total (pairRank a) (pairRank b)⟩
  exact Finset.length_sort _

/-- If `e' ∈ E` has strictly smaller `pairRank` than `(sortPairs E)[k]`, then `e' ∈ (sortPairs E).take k`. -/
lemma mem_take_sortPairs_of_rank_lt {m : ℕ} (E : Finset (Pair m)) {k : ℕ}
    (hk : k < (sortPairs E).length) {e' : Pair m} (he' : e' ∈ E)
    (hlt : pairRank e' < pairRank ((sortPairs E)[k])) :
    e' ∈ (sortPairs E).take k := by
  have : IsTrans (Pair m) (fun a b => pairRank a ≤ pairRank b) := ⟨fun _ _ _ h1 h2 => le_trans h1 h2⟩
  have : Std.Antisymm (fun a b : Pair m => pairRank a ≤ pairRank b) := ⟨fun _ _ h1 h2 => pairRank_inj (le_antisymm h1 h2)⟩
  have : Std.Total (fun a b : Pair m => pairRank a ≤ pairRank b) := ⟨fun a b => le_total (pairRank a) (pairRank b)⟩
  have hsorted : (sortPairs E).Pairwise (fun a b => pairRank a ≤ pairRank b) :=
    Finset.pairwise_sort E (fun a b => pairRank a ≤ pairRank b)
  have hmem : e' ∈ sortPairs E := (mem_sortPairs E e').mpr he'
  obtain ⟨j, hj, hj_eq⟩ := List.getElem_of_mem hmem
  have hjk : j < k := by
    by_contra hge
    push Not at hge
    rcases eq_or_lt_of_le hge with rfl | hlt_kj
    · rw [hj_eq] at hlt; exact lt_irrefl _ hlt
    · have hle := List.pairwise_iff_getElem.mp hsorted k j hk hj hlt_kj
      rw [hj_eq] at hle
      omega
  have htake : (sortPairs E)[j] ∈ (sortPairs E).take k := by
    have hj_take : j < ((sortPairs E).take k).length := by rw [List.length_take]; omega
    have hget : ((sortPairs E).take k)[j] = (sortPairs E)[j] := List.getElem_take
    rw [← hget]
    exact List.getElem_mem hj_take
  rwa [hj_eq] at htake

/-- Predictable active indicator for `e = (sortPairs E)[k]`:
`true` iff NO `i < e.1.1` is adjacent to both `e.1.1` and `e.1.2` in `mergeOn Eᶜ g₀ y`. -/
def triAct {m : ℕ} (E : Finset (Pair m)) (g₀ : Pair m → Bool) (k : ℕ) (y : Pair m → Bool) : Bool :=
  if hk : k < (sortPairs E).length then
    let e := (sortPairs E)[k]
    let g := mergeOn Eᶜ g₀ y
    decide (¬ ∃ i : Fin m, i < e.1.1 ∧ gAdj g i e.1.1 = true ∧ gAdj g i e.1.2 = true)
  else false

lemma triAct_predictable {m : ℕ} (E : Finset (Pair m)) (g₀ : Pair m → Bool) :
    ∀ k (y₁ y₂ : Pair m → Bool),
      (∀ e ∈ (sortPairs E).take k, y₁ e = y₂ e) → triAct E g₀ k y₁ = triAct E g₀ k y₂ := by
  intro k y₁ y₂ htake
  unfold triAct
  split_ifs with hk
  · dsimp only
    rw [decide_eq_decide]
    have hagree : ∀ (i : Fin m), i < ((sortPairs E)[k]).1.1 →
        (gAdj (mergeOn Eᶜ g₀ y₁) i ((sortPairs E)[k]).1.1 = gAdj (mergeOn Eᶜ g₀ y₂) i ((sortPairs E)[k]).1.1 ∧
         gAdj (mergeOn Eᶜ g₀ y₁) i ((sortPairs E)[k]).1.2 = gAdj (mergeOn Eᶜ g₀ y₂) i ((sortPairs E)[k]).1.2) := by
      intro i hilt
      have h1 : i ≠ ((sortPairs E)[k]).1.1 := hilt.ne
      have h2 : i ≠ ((sortPairs E)[k]).1.2 := (lt_trans hilt ((sortPairs E)[k]).2).ne
      have hfst1 : (mkEdge i ((sortPairs E)[k]).1.1 h1).1.1 < ((sortPairs E)[k]).1.1 := by
        rw [mkEdge_fst_eq_min, min_eq_left hilt.le]; exact hilt
      have hfst2 : (mkEdge i ((sortPairs E)[k]).1.2 h2).1.1 < ((sortPairs E)[k]).1.1 := by
        rw [mkEdge_fst_eq_min, min_eq_left (lt_trans hilt ((sortPairs E)[k]).2).le]; exact hilt
      have heq_edge : ∀ (e' : Pair m), e'.1.1 < ((sortPairs E)[k]).1.1 →
          mergeOn Eᶜ g₀ y₁ e' = mergeOn Eᶜ g₀ y₂ e' := by
        intro e' he'lt
        by_cases he'E : e' ∈ E
        · have he'not : e' ∉ Eᶜ := by simp [he'E]
          rw [mergeOn_notMem _ _ _ he'not, mergeOn_notMem _ _ _ he'not]
          exact htake e' (mem_take_sortPairs_of_rank_lt E hk he'E (pairRank_lt_of_fst_lt he'lt))
        · have he'mem : e' ∈ Eᶜ := by simp [he'E]
          rw [mergeOn_mem _ _ _ he'mem, mergeOn_mem _ _ _ he'mem]
      constructor
      · simp only [gAdj, dif_pos h1]; exact heq_edge _ hfst1
      · simp only [gAdj, dif_pos h2]; exact heq_edge _ hfst2
    constructor <;> intro h <;> rintro ⟨i, hilt, ha, hb⟩
    · exact h ⟨i, hilt, (hagree i hilt).1 ▸ ha, (hagree i hilt).2 ▸ hb⟩
    · exact h ⟨i, hilt, (hagree i hilt).1.symm ▸ ha, (hagree i hilt).2.symm ▸ hb⟩
  · rfl

/-- One-sided inner bound for fixed `g₀` and fixed unrevealed sets `E_1, E_2`
(covers BOTH `U_B ≤ U_R` and symmetrically `U_R ≤ U_B`!). -/
lemma inner_half_bound {m M₁ M₂ Z_min : ℕ} {p r : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (E₁ E₂ : Finset (Pair m)) (hE₂_le : E₂.card ≤ M₂)
    (g₀₁ g₀₂ : Pair m → Bool)
    (C_allowed : (Pair m → Bool) → Finset (Pair m))
    (Ev : (Pair m → Bool) → (Pair m → Bool) → Prop)
    (hEv_imp : ∀ y₁ y₂ : Pair m → Bool, Ev y₁ y₂ →
      allActiveIn (sortPairs E₁) (C_allowed y₂) (triAct E₁ g₀₁) y₁ ∧
      (C_allowed y₂).card ≤ M₁ ∧
      actCount (sortPairs E₂) (triAct E₂ g₀₂) true y₂ ≤ actCount (sortPairs E₁) (triAct E₁ g₀₁) true y₁ ∧
      Z_min ≤ actCount (sortPairs E₁) (triAct E₁ g₀₁) false y₁ + actCount (sortPairs E₂) (triAct E₂ g₀₂) false y₂) :
    Pr (prodW (bernW (Pair m) p) (bernW (Pair m) p)) (fun y => Ev y.1 y.2) ≤
      Real.exp (((M₁ : ℝ) / r + r * (M₂ : ℝ)) * p - p * (Z_min : ℝ)) := by
  have hP1 := isProb_bernW (ι := Pair m) hp0 hp1
  have hP := isProb_prodW hP1 hP1
  -- Swap coordinates so outer sum is `y₂`, inner is `y₁`!
  set L₁ := sortPairs E₁
  set L₂ := sortPairs E₂
  have hL₁_nd : L₁.Nodup := sortPairs_nodup E₁
  have hL₂_nd : L₂.Nodup := sortPairs_nodup E₂
  have hU₁_le : ∀ y₁ y₂, Ev y₁ y₂ → actCount L₁ (triAct E₁ g₀₁) true y₁ ≤ M₁ := by
    intro y₁ y₂ hEv
    obtain ⟨hall, hC_le, _, _⟩ := hEv_imp y₁ y₂ hEv
    have hinj : (Finset.univ.filter (fun k : Fin L₁.length => triAct E₁ g₀₁ k.1 y₁ = true ∧ y₁ (L₁[k.1]) = true)).card ≤
        (C_allowed y₂).card := by
      refine Finset.card_le_card_of_injOn (fun k : Fin L₁.length => L₁[k.1]) ?_ ?_
      · intro k hk
        have hm := (Finset.mem_filter.mp hk).2
        exact hall k.1 k.2 hm.1 hm.2
      · intro k₁ _ k₂ _ heq
        exact Fin.ext ((List.Nodup.getElem_inj_iff hL₁_nd).mp heq)
    exact hinj.trans hC_le
  have hU₂_le : ∀ y₂, actCount L₂ (triAct E₂ g₀₂) true y₂ ≤ M₂ := by
    intro y₂
    calc actCount L₂ (triAct E₂ g₀₂) true y₂
        ≤ (Finset.univ : Finset (Fin L₂.length)).card := Finset.card_le_univ _
      _ = L₂.length := by simp
      _ = E₂.card := sortPairs_length E₂
      _ ≤ M₂ := hE₂_le
  -- Bound `Pr(Ev)` by summing over `(u₁, u₂)` with `u₁ ≤ M₁` and `u₂ ≤ min u₁ M₂`!
  have himp_sum : ∀ y : (Pair m → Bool) × (Pair m → Bool), Ev y.1 y.2 →
      ∃ u₁ ∈ Finset.range (M₁ + 1), ∃ u₂ ∈ Finset.range (min u₁ M₂ + 1),
        Ev y.1 y.2 ∧
        actCount L₁ (triAct E₁ g₀₁) true y.1 = u₁ ∧
        actCount L₂ (triAct E₂ g₀₂) true y.2 = u₂ := by
    intro y hEv
    set u₁ := actCount L₁ (triAct E₁ g₀₁) true y.1
    set u₂ := actCount L₂ (triAct E₂ g₀₂) true y.2
    have h1 : u₁ ≤ M₁ := hU₁_le y.1 y.2 hEv
    have h2 : u₂ ≤ M₂ := hU₂_le y.2
    have h21 : u₂ ≤ u₁ := (hEv_imp y.1 y.2 hEv).2.2.1
    refine ⟨u₁, Finset.mem_range.mpr (by omega), u₂, Finset.mem_range.mpr (by omega), hEv, rfl, rfl⟩
  -- For fixed `(u₁, u₂)`, bound `Pr(Ev ∧ U₁ = u₁ ∧ U₂ = u₂)` via `predictable_bern_bound` twice!
  have hfixed : ∀ u₁ u₂ : ℕ,
      Pr (prodW (bernW (Pair m) p) (bernW (Pair m) p)) (fun y =>
        Ev y.1 y.2 ∧ actCount L₁ (triAct E₁ g₀₁) true y.1 = u₁ ∧ actCount L₂ (triAct E₂ g₀₂) true y.2 = u₂) ≤
      (M₁.choose u₁ : ℝ) * p ^ u₁ * ((M₂.choose u₂ : ℝ) * p ^ u₂) * (1 - p) ^ Z_min := by
    intro u₁ u₂
    let eSwap : ((Pair m → Bool) × (Pair m → Bool)) ≃ ((Pair m → Bool) × (Pair m → Bool)) :=
      Equiv.prodComm _ _
    rw [← Pr_equiv eSwap]
    have hwt_swap : (fun y : (Pair m → Bool) × (Pair m → Bool) =>
        prodW (bernW (Pair m) p) (bernW (Pair m) p) (eSwap y)) =
        prodW (bernW (Pair m) p) (bernW (Pair m) p) := by
      funext ⟨y₂, y₁⟩; simp [prodW, eSwap, mul_comm]
    rw [hwt_swap, Pr_prodW]
    have hinner : ∀ y₂ : Pair m → Bool,
        Pr (bernW (Pair m) p) (fun y₁ =>
          Ev y₁ y₂ ∧ actCount L₁ (triAct E₁ g₀₁) true y₁ = u₁ ∧ actCount L₂ (triAct E₂ g₀₂) true y₂ = u₂) ≤
        ((M₁.choose u₁ : ℝ) * p ^ u₁) *
          predScore L₂ Finset.univ (triAct E₂ g₀₂) p u₂ Z_min y₂ := by
      intro y₂
      by_cases hcond : actCount L₂ (triAct E₂ g₀₂) true y₂ = u₂ ∧ (C_allowed y₂).card ≤ M₁
      · -- Inner `y₁` probability ≤ `E_{y₁}[predScore L₁ (C_allowed y₂) (triAct E₁ g₀₁) p u₁ (Z_min - Z₂)]`!
        set Z₂ := actCount L₂ (triAct E₂ g₀₂) false y₂
        have hstep1 : Pr (bernW (Pair m) p) (fun y₁ =>
              Ev y₁ y₂ ∧ actCount L₁ (triAct E₁ g₀₁) true y₁ = u₁ ∧ actCount L₂ (triAct E₂ g₀₂) true y₂ = u₂) ≤
            E (bernW (Pair m) p) (predScore L₁ (C_allowed y₂) (triAct E₁ g₀₁) p u₁ (Z_min - Z₂)) := by
          rw [Pr_eq_E]
          refine E_mono hP1 fun y₁ => ?_
          split_ifs with h
          · obtain ⟨hEv, hU1, _⟩ := h
            obtain ⟨hall, _, _, hZ⟩ := hEv_imp y₁ y₂ hEv
            have hsub0 : (Z_min - Z₂) - actCount L₁ (triAct E₁ g₀₁) false y₁ = 0 := by omega
            simp [predScore, hall, hU1, hsub0]
          · simp only [predScore]
            split_ifs
            · exact pow_nonneg (by linarith) _
            · exact le_rfl
        have hpred1' : E (bernW (Pair m) p) (predScore L₁ (C_allowed y₂) (triAct E₁ g₀₁) p u₁ (Z_min - Z₂)) ≤
            (M₁.choose u₁ : ℝ) * p ^ u₁ * (1 - p) ^ (Z_min - Z₂) := by
          refine (predictable_bern_bound hp0 hp1 L₁ hL₁_nd (C_allowed y₂) (triAct E₁ g₀₁)
            (triAct_predictable E₁ g₀₁) u₁ (Z_min - Z₂)).trans ?_
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hp0 _))
            (pow_nonneg (by linarith) _)
          have hfil : ∀ (P : Pair m → Prop) (inst : DecidablePred P),
              (@Finset.filter (Pair m) P inst (C_allowed y₂)).card ≤ M₁ := fun P inst =>
            (Finset.card_le_card (@Finset.filter_subset (Pair m) P inst (C_allowed y₂))).trans hcond.2
          exact Nat.cast_le.mpr (Nat.choose_le_choose u₁ (hfil _ _))
        have hscore2 : predScore L₂ Finset.univ (triAct E₂ g₀₂) p u₂ Z_min y₂ = (1 - p) ^ (Z_min - Z₂) := by
          simp [predScore, allActiveIn, hcond.1, Z₂]
        rw [hscore2]
        exact hstep1.trans hpred1'
      · -- Either `U₂ ≠ u₂` or `|C_allowed y₂| > M₁`: `Ev` cannot hold!
        have hzero : Pr (bernW (Pair m) p) (fun y₁ =>
            Ev y₁ y₂ ∧ actCount L₁ (triAct E₁ g₀₁) true y₁ = u₁ ∧ actCount L₂ (triAct E₂ g₀₂) true y₂ = u₂) = 0 := by
          rw [Pr_congr (B := fun _ => False) (fun y₁ => by
            constructor
            · rintro ⟨hEv, _, hU2⟩
              exact hcond ⟨hU2, (hEv_imp y₁ y₂ hEv).2.1⟩
            · exact False.elim), Pr_false]
        rw [hzero]
        have hsc0 : 0 ≤ predScore L₂ Finset.univ (triAct E₂ g₀₂) p u₂ Z_min y₂ := by
          simp only [predScore]
          split_ifs
          · exact pow_nonneg (by linarith) _
          · exact le_rfl
        exact mul_nonneg (by positivity) hsc0
    have hpred2' : E (bernW (Pair m) p) (predScore L₂ Finset.univ (triAct E₂ g₀₂) p u₂ Z_min) ≤
        (M₂.choose u₂ : ℝ) * p ^ u₂ * (1 - p) ^ Z_min := by
      refine (predictable_bern_bound hp0 hp1 L₂ hL₂_nd Finset.univ (triAct E₂ g₀₂)
        (triAct_predictable E₂ g₀₂) u₂ Z_min).trans ?_
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hp0 _))
        (pow_nonneg (by linarith) _)
      have hL2_card : ∀ (P : Pair m → Prop) (inst : DecidablePred P), (∀ e, P e ↔ e ∈ E₂) →
          (@Finset.filter (Pair m) P inst Finset.univ).card ≤ M₂ := by
        intro P inst hPiff
        have heq : @Finset.filter (Pair m) P inst Finset.univ = E₂ := by ext e; simp [hPiff]
        rw [heq]; exact hE₂_le
      exact Nat.cast_le.mpr (Nat.choose_le_choose u₂ (hL2_card _ _ (fun e => mem_sortPairs E₂ e)))
    calc E (bernW (Pair m) p) (fun y₂ => Pr (bernW (Pair m) p) (fun y₁ =>
          Ev (eSwap (y₂, y₁)).1 (eSwap (y₂, y₁)).2 ∧
          actCount L₁ (triAct E₁ g₀₁) true (eSwap (y₂, y₁)).1 = u₁ ∧
          actCount L₂ (triAct E₂ g₀₂) true (eSwap (y₂, y₁)).2 = u₂))
        ≤ E (bernW (Pair m) p) (fun y₂ => ((M₁.choose u₁ : ℝ) * p ^ u₁) *
            predScore L₂ Finset.univ (triAct E₂ g₀₂) p u₂ Z_min y₂) :=
          E_mono hP1 fun y₂ => hinner y₂
      _ = ((M₁.choose u₁ : ℝ) * p ^ u₁) *
            E (bernW (Pair m) p) (predScore L₂ Finset.univ (triAct E₂ g₀₂) p u₂ Z_min) := E_const_mul _ _ _
      _ ≤ ((M₁.choose u₁ : ℝ) * p ^ u₁) * ((M₂.choose u₂ : ℝ) * p ^ u₂ * (1 - p) ^ Z_min) :=
          mul_le_mul_of_nonneg_left hpred2' (by positivity)
      _ = (M₁.choose u₁ : ℝ) * p ^ u₁ * ((M₂.choose u₂ : ℝ) * p ^ u₂) * (1 - p) ^ Z_min := by ring
  -- Combine via union bound over `u₁, u₂` and `binom_sum_ordered_le`!
  calc Pr (prodW (bernW (Pair m) p) (bernW (Pair m) p)) (fun y => Ev y.1 y.2)
      ≤ Pr (prodW (bernW (Pair m) p) (bernW (Pair m) p)) (fun y =>
          ∃ u₁ ∈ Finset.range (M₁ + 1), ∃ u₂ ∈ Finset.range (min u₁ M₂ + 1),
            Ev y.1 y.2 ∧ actCount L₁ (triAct E₁ g₀₁) true y.1 = u₁ ∧ actCount L₂ (triAct E₂ g₀₂) true y.2 = u₂) :=
        Pr_mono hP himp_sum
    _ ≤ ∑ u₁ ∈ Finset.range (M₁ + 1), Pr (prodW (bernW (Pair m) p) (bernW (Pair m) p)) (fun y =>
          ∃ u₂ ∈ Finset.range (min u₁ M₂ + 1),
            Ev y.1 y.2 ∧ actCount L₁ (triAct E₁ g₀₁) true y.1 = u₁ ∧ actCount L₂ (triAct E₂ g₀₂) true y.2 = u₂) :=
        Pr_exists_le hP _ _
    _ ≤ ∑ u₁ ∈ Finset.range (M₁ + 1), ∑ u₂ ∈ Finset.range (min u₁ M₂ + 1),
          Pr (prodW (bernW (Pair m) p) (bernW (Pair m) p)) (fun y =>
            Ev y.1 y.2 ∧ actCount L₁ (triAct E₁ g₀₁) true y.1 = u₁ ∧ actCount L₂ (triAct E₂ g₀₂) true y.2 = u₂) :=
        Finset.sum_le_sum fun u₁ _ => Pr_exists_le hP _ _
    _ ≤ ∑ u₁ ∈ Finset.range (M₁ + 1), ∑ u₂ ∈ Finset.range (min u₁ M₂ + 1),
          (M₁.choose u₁ : ℝ) * p ^ u₁ * ((M₂.choose u₂ : ℝ) * p ^ u₂) * (1 - p) ^ Z_min :=
        Finset.sum_le_sum fun u₁ _ => Finset.sum_le_sum fun u₂ _ => hfixed u₁ u₂
    _ ≤ Real.exp (((M₁ : ℝ) / r + r * (M₂ : ℝ)) * p - p * (Z_min : ℝ)) :=
        binom_sum_ordered_le hp0 hp1 hr0 hr1 M₁ M₂ Z_min

/-- Independence predicate for `I` in `twoBitesGraph π.1 π.2 g.1 g.2`. -/
def IndepI {n m : ℕ} (π : PiPair n m) (g : GPair m) (I : Finset (Fin n)) : Prop :=
  (twoBitesGraph π.1 π.2 g.1 g.2).IsIndepSet (↑I : Set (Fin n))

/-- The 4-step exposure sets for fixed `π` and `I`:
- `F1R`, `F1B`: heavy-fiber vertices inside `πR(I)`, `πB(I)` (depend only on `π, I`).
- `F2R`, `F2B`: vertices in `R_I \ F1R` (resp. `B_I \ F1B`) with `> Nthr` neighbors in `F1`. -/
noncomputable def F1set {n m : ℕ} (π₁ : Fin n → Fin m) (I : Finset (Fin n)) (Fthr : ℝ) : Finset (Fin m) :=
  by classical exact (I.image π₁).filter (fun r => Fthr < ((I ∩ fiber π₁ r).card : ℝ))

noncomputable def F2set {n m : ℕ} (π₁ : Fin n → Fin m) (g₁ : Pair m → Bool)
    (I : Finset (Fin n)) (Fthr Nthr : ℝ) : Finset (Fin m) :=
  by classical exact ((I.image π₁) \ F1set π₁ I Fthr).filter (fun r =>
    Nthr < ((nbrG g₁ r ∩ F1set π₁ I Fthr).card : ℝ))

/-- Pairs revealed in Stage 1+2 (fixed given `π, I`): all pairs NOT inside `R_I \ F1R` (resp. `B_I \ F1B`). -/
noncomputable def Q12one {n m : ℕ} (π₁ : Fin n → Fin m) (I : Finset (Fin n)) (Fthr : ℝ) :
    Finset (Pair m) :=
  let keep := I.image π₁ \ F1set π₁ I Fthr
  Finset.univ.filter (fun e : Pair m => ¬ (e.1.1 ∈ keep ∧ e.1.2 ∈ keep))

/-- Pairs revealed in Stage 3 (depends only on `Q12`): pairs incident to `F2`. -/
noncomputable def Q3one {n m : ℕ} (π₁ : Fin n → Fin m) (g₁ : Pair m → Bool)
    (I : Finset (Fin n)) (Fthr Nthr : ℝ) : Finset (Pair m) :=
  let F2 := F2set π₁ g₁ I Fthr Nthr
  Finset.univ.filter (fun e : Pair m => e.1.1 ∈ F2 ∨ e.1.2 ∈ F2)

/-- Full revealed vertex set `F = F0 ∪ F1 ∪ F2 = (R_I \ (F1 ∪ F2))ᶜ`. -/
noncomputable def Ffull {n m : ℕ} (π₁ : Fin n → Fin m) (g₁ : Pair m → Bool)
    (I : Finset (Fin n)) (Fthr Nthr : ℝ) : Finset (Fin m) :=
  ((I.image π₁) \ (F1set π₁ I Fthr ∪ F2set π₁ g₁ I Fthr Nthr))ᶜ

/-- Pairs revealed in Stage 4 (depends only on `Q12 ∪ Q3`):
all projected pairs in `projPairs π₁ (X_v(I))` for `v ∈ FR ∪ FB`. -/
noncomputable def Q4one {n m : ℕ} (π₁ π₂ : Fin n → Fin m) (g₁ g₂ : Pair m → Bool)
    (I : Finset (Fin n)) (Fthr Nthr : ℝ) : Finset (Pair m) :=
  (Ffull π₁ g₁ I Fthr Nthr).biUnion (fun r => projPairs π₁ (XV π₁ g₁ I r)) ∪
  (Ffull π₂ g₂ I Fthr Nthr).biUnion (fun b => projPairs π₁ (XV π₂ g₂ I b))

/-- One-color helper: open pairs in `projPairs π₁ I` outside `Q12 ∪ Q3` are active false bits in `E₁`. -/
lemma open_unrev_le_actCount {n m : ℕ} {Fthr Nthr : ℝ}
    (π₁ π₂ : Fin n → Fin m) (g₀₁ g₀₂ y₁ _y₂ : Pair m → Bool)
    (I : Finset (Fin n))
    (E₁ : Finset (Pair m))
    (hE₁ : E₁ = (Q12one π₁ I Fthr ∪ Q3one π₁ g₀₁ I Fthr Nthr ∪ Q4one π₁ π₂ g₀₁ g₀₂ I Fthr Nthr)ᶜ)
    (g₁ g₂ : Pair m → Bool)
    (hg₁ : g₁ = mergeOn E₁ᶜ g₀₁ y₁)
    (hF2eq : F2set π₁ g₁ I Fthr Nthr = F2set π₁ g₀₁ I Fthr Nthr)
    (hXV1 : ∀ v ∈ Ffull π₁ g₀₁ I Fthr Nthr, XV π₁ g₁ I v = XV π₁ g₀₁ I v)
    (hXV2 : ∀ v ∈ Ffull π₂ g₀₂ I Fthr Nthr, XV π₂ g₂ I v = XV π₂ g₀₂ I v)
    (hnoSurv : ∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ redSurv π₁ π₂ g₁ g₂ u v) :
    ((projPairs π₁ I \ (Finset.univ.biUnion (fun v : Fin m ⊕ Fin m =>
        projPairs π₁ (XAll (π₁, π₂) (g₁, g₂) I v)))) \ (Q12one π₁ I Fthr ∪ Q3one π₁ g₁ I Fthr Nthr)).card ≤
      actCount (sortPairs E₁) (triAct E₁ g₀₁) false y₁ := by
  let O_unrev := (projPairs π₁ I \ (Finset.univ.biUnion (fun v : Fin m ⊕ Fin m =>
      projPairs π₁ (XAll (π₁, π₂) (g₁, g₂) I v)))) \ (Q12one π₁ I Fthr ∪ Q3one π₁ g₁ I Fthr Nthr)
  have hO_sub_E₁ : ∀ e ∈ O_unrev, e ∈ E₁ := by
    intro e he
    have h1 := Finset.mem_sdiff.mp he
    have hopen := Finset.mem_sdiff.mp h1.1
    have hnot123' : e ∉ Q12one π₁ I Fthr ∪ Q3one π₁ g₀₁ I Fthr Nthr := by
      simpa [Q3one, hF2eq] using h1.2
    have hnotQ4 : e ∉ Q4one π₁ π₂ g₀₁ g₀₂ I Fthr Nthr := by
      intro hq4
      apply hopen.2
      rcases Finset.mem_union.mp hq4 with hR4 | hB4
      · obtain ⟨r, hrF, her⟩ := Finset.mem_biUnion.mp hR4
        refine Finset.mem_biUnion.mpr ⟨Sum.inl r, Finset.mem_univ _, ?_⟩
        rw [XAll_inl, hXV1 r hrF]; exact her
      · obtain ⟨b, hbF, heb⟩ := Finset.mem_biUnion.mp hB4
        refine Finset.mem_biUnion.mpr ⟨Sum.inr b, Finset.mem_univ _, ?_⟩
        rw [XAll_inr, hXV2 b hbF]; exact heb
    rw [hE₁, Finset.mem_compl, Finset.mem_union, not_or]
    exact ⟨hnot123', hnotQ4⟩
  have hO_actF : ∀ (k' : Fin (sortPairs E₁).length), (sortPairs E₁)[k'.1] ∈ O_unrev →
      triAct E₁ g₀₁ k'.1 y₁ = true ∧ y₁ ((sortPairs E₁)[k'.1]) = false := by
    intro k' hk'
    set e := (sortPairs E₁)[k'.1]
    have hopen := Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hk').1
    have heI := (Finset.mem_filter.mp hopen.1).2
    obtain ⟨u, huI, hπu⟩ := Finset.mem_image.mp heI.1
    obtain ⟨v, hvI, hπv⟩ := Finset.mem_image.mp heI.2
    have huv : u ≠ v := fun h => e.2.ne (hπu.symm.trans (h ▸ hπv))
    have hno_r : ¬ ∃ r : Fin m, r < e.1.1 ∧ gAdj g₁ r e.1.1 = true ∧ gAdj g₁ r e.1.2 = true := by
      rintro ⟨r, _, h1, h2⟩
      apply hopen.2
      refine Finset.mem_biUnion.mpr ⟨Sum.inl r, Finset.mem_univ _, ?_⟩
      rw [XAll_inl]
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ e, ?_, ?_⟩
      · rw [← hπu]; exact Finset.mem_image_of_mem π₁ (Finset.mem_filter.mpr ⟨huI, by dsimp only; rwa [hπu]⟩)
      · rw [← hπv]; exact Finset.mem_image_of_mem π₁ (Finset.mem_filter.mpr ⟨hvI, by dsimp only; rwa [hπv]⟩)
    have hact : triAct E₁ g₀₁ k'.1 y₁ = true := by
      simp only [triAct, dif_pos k'.2, decide_eq_true_eq]
      rwa [← hg₁]
    have hfalse : y₁ e = false := by
      by_contra hneF
      have hyT : y₁ e = true := Bool.eq_true_of_not_eq_false hneF
      have heE₁ : e ∈ E₁ := hO_sub_E₁ e hk'
      have hge : gAdj g₁ (π₁ u) (π₁ v) = true := by
        have hne : π₁ u ≠ π₁ v := by rw [hπu, hπv]; exact e.2.ne
        have hmk : mkEdge (π₁ u) (π₁ v) hne = e := by
          apply Subtype.ext; simp only [mkEdge, hπu, hπv, dif_pos e.2]
        have hnotc : e ∉ E₁ᶜ := by simp [heE₁]
        simp [gAdj, hne, hmk, hg₁, mergeOn_notMem _ _ _ hnotc, hyT]
      have hno_b : ¬ ∃ b : Fin m, gAdj g₂ b (π₂ u) = true ∧ gAdj g₂ b (π₂ v) = true := by
        rintro ⟨b, hbu, hbv⟩
        apply hopen.2
        refine Finset.mem_biUnion.mpr ⟨Sum.inr b, Finset.mem_univ _, ?_⟩
        rw [XAll_inr]
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ e, ?_, ?_⟩
        · rw [← hπu]; exact Finset.mem_image_of_mem π₁ (Finset.mem_filter.mpr ⟨huI, hbu⟩)
        · rw [← hπv]; exact Finset.mem_image_of_mem π₁ (Finset.mem_filter.mpr ⟨hvI, hbv⟩)
      have hno_r' : ¬ ∃ r : Fin m, r < min (π₁ u) (π₁ v) ∧ gAdj g₁ r (π₁ u) = true ∧ gAdj g₁ r (π₁ v) = true := by
        rintro ⟨r, hlt, h1, h2⟩
        rw [hπu, hπv, min_eq_left e.2.le] at hlt
        rw [hπu] at h1; rw [hπv] at h2
        exact hno_r ⟨r, hlt, h1, h2⟩
      exact hnoSurv u huI v hvI huv ⟨hge, hno_r', hno_b⟩
    exact ⟨hact, hfalse⟩
  have hcard_le : O_unrev.card ≤
      (Finset.univ.filter (fun k' : Fin (sortPairs E₁).length => (sortPairs E₁)[k'.1] ∈ O_unrev)).card := by
    have hsurj : ∀ e ∈ O_unrev, ∃ k' ∈ Finset.univ.filter (fun k' : Fin (sortPairs E₁).length =>
        (sortPairs E₁)[k'.1] ∈ O_unrev), (sortPairs E₁)[k'.1] = e := by
      intro e he
      have hmem : e ∈ sortPairs E₁ := (mem_sortPairs E₁ e).mpr (hO_sub_E₁ e he)
      obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hmem
      exact ⟨⟨j, hj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjeq.symm ▸ he⟩, hjeq⟩
    exact Finset.card_le_card_of_surjOn (fun k' : Fin (sortPairs E₁).length => (sortPairs E₁)[k'.1]) hsurj
  exact hcard_le.trans (Finset.card_le_card fun k' hk' =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ k', hO_actF k' (Finset.mem_filter.mp hk').2⟩)

/-- Lemma 4.1 (`lem:RISI`, non-asymptotic fixed-`π` bound):
for fixed `π`, `I` of size `k`, and ANY regularity predicate `Reg : GPair m → Prop` such that
whenever `IndepI π g I ∧ Reg g`:
1. Both cross-closed sets outside `Ffull` have size `≤ M₁`:
   `|((B_I \ (F1B ∪ F2B)).biUnion (projPairs π.1 ∘ XV_B))| ≤ M₁` and symmetrically for red.
2. Total open unrevealed pairs (equivalently `|O_R ∩ E_IR| + |O_B ∩ E_IB|`) is `≥ Z_min`:
   more concretely, `|O_R \ (Q12R ∪ Q3R)| + |O_B \ (Q12B ∪ Q3B)| ≥ Z_min` where
   `O_R = projPairs π.1 I \ ⋃_{v : Fin m ⊕ Fin m} projPairs π.1 (XAll π g I v)` and similarly `O_B`.
Then `Pr (gPairW m p) (fun g => IndepI π g I ∧ Reg g) ≤ 2 * exp(((M₁ / r + r * k^2) * p - p * Z_min))`. -/
lemma lem_RISI_fixed_pi {n m k M₁ Z_min : ℕ} {p r Fthr Nthr : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (π : PiPair n m) (I : Finset (Fin n)) (hI : I.card = k)
    (Reg : GPair m → Prop)
    (hReg_C1 : ∀ g : GPair m, IndepI π g I → Reg g →
      (((I.image π.2) \ (F1set π.2 I Fthr ∪ F2set π.2 g.2 I Fthr Nthr)).biUnion
        (fun b => projPairs π.1 (XV π.2 g.2 I b))).card ≤ M₁)
    (hReg_C2 : ∀ g : GPair m, IndepI π g I → Reg g →
      (((I.image π.1) \ (F1set π.1 I Fthr ∪ F2set π.1 g.1 I Fthr Nthr)).biUnion
        (fun r => projPairs π.2 (XV π.1 g.1 I r))).card ≤ M₁)
    (hReg_Z : ∀ g : GPair m, IndepI π g I → Reg g →
      Z_min ≤
        ((projPairs π.1 I \ (Finset.univ.biUnion (fun v : Fin m ⊕ Fin m => projPairs π.1 (XAll π g I v)))) \
          (Q12one π.1 I Fthr ∪ Q3one π.1 g.1 I Fthr Nthr)).card +
        ((projPairs π.2 I \ (Finset.univ.biUnion (fun v : Fin m ⊕ Fin m => projPairs π.2 (XAll π g I v)))) \
          (Q12one π.2 I Fthr ∪ Q3one π.2 g.2 I Fthr Nthr)).card) :
    Pr (gPairW m p) (fun g => IndepI π g I ∧ Reg g) ≤
      2 * Real.exp (((M₁ : ℝ) / r + r * ((k ^ 2 : ℕ) : ℝ)) * p - p * (Z_min : ℝ)) := by
  -- Move to `bernW (Pair m ⊕ Pair m) p` via `gPairEquiv m`, apply `Pr_bernW_adaptive3_le`!
  rw [← Pr_equiv (gPairEquiv m)]
  have hwt : (fun f : Pair m ⊕ Pair m → Bool => gPairW m p (gPairEquiv m f)) =
      bernW (Pair m ⊕ Pair m) p := funext (gPairW_eq_bernW p)
  rw [hwt]
  let Q₁ : Finset (Pair m ⊕ Pair m) :=
    (Q12one π.1 I Fthr).image Sum.inl ∪ (Q12one π.2 I Fthr).image Sum.inr
  let Q₂ (f : Pair m ⊕ Pair m → Bool) : Finset (Pair m ⊕ Pair m) :=
    (Q3one π.1 (gPairEquiv m f).1 I Fthr Nthr).image Sum.inl ∪
    (Q3one π.2 (gPairEquiv m f).2 I Fthr Nthr).image Sum.inr
  let Q₃ (f : Pair m ⊕ Pair m → Bool) : Finset (Pair m ⊕ Pair m) :=
    (Q4one π.1 π.2 (gPairEquiv m f).1 (gPairEquiv m f).2 I Fthr Nthr).image Sum.inl ∪
    (Q4one π.2 π.1 (gPairEquiv m f).2 (gPairEquiv m f).1 I Fthr Nthr).image Sum.inr
  -- Helper: `F2set` depends only on `Q12one`!
  have hF2_dep : ∀ (π₁ : Fin n → Fin m) (g₁ g₁' : Pair m → Bool),
      (∀ e ∈ Q12one π₁ I Fthr, g₁ e = g₁' e) →
      F2set π₁ g₁ I Fthr Nthr = F2set π₁ g₁' I Fthr Nthr := by
    intro π₁ g₁ g₁' hag
    refine Finset.filter_congr fun u _ => ?_
    have hne_inter : nbrG g₁ u ∩ F1set π₁ I Fthr = nbrG g₁' u ∩ F1set π₁ I Fthr := by
      ext w
      simp only [Finset.mem_inter, nbrG, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> rintro ⟨hadj, hwF1⟩ <;> refine ⟨?_, hwF1⟩
      · have hne : u ≠ w := gAdj_ne_of_true hadj
        have heQ : mkEdge u w hne ∈ Q12one π₁ I Fthr := by
          simp only [Q12one, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
          unfold mkEdge; split_ifs <;> tauto
        simpa [gAdj, hne, hag _ heQ] using hadj
      · have hne : u ≠ w := gAdj_ne_of_true hadj
        have heQ : mkEdge u w hne ∈ Q12one π₁ I Fthr := by
          simp only [Q12one, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
          unfold mkEdge; split_ifs <;> tauto
        simpa [gAdj, hne, ← hag _ heQ] using hadj
    rw [hne_inter]
  -- Helper: for `v ∈ Ffull`, `XV π₁ g₁ I v` depends only on `Q12one ∪ Q3one`!
  have hXV_dep : ∀ (π₁ : Fin n → Fin m) (g₁ g₁' : Pair m → Bool),
      (∀ e ∈ Q12one π₁ I Fthr ∪ Q3one π₁ g₁ I Fthr Nthr, g₁ e = g₁' e) →
      ∀ v ∈ Ffull π₁ g₁ I Fthr Nthr, XV π₁ g₁ I v = XV π₁ g₁' I v := by
    intro π₁ g₁ g₁' hag v hv
    have hvnot : v ∉ (I.image π₁) \ (F1set π₁ I Fthr ∪ F2set π₁ g₁ I Fthr Nthr) :=
      Finset.mem_compl.mp hv
    refine Finset.filter_congr fun x hxI => ?_
    by_cases hne : v = π₁ x
    · simp [gAdj, hne]
    · have heQ : mkEdge v (π₁ x) hne ∈ Q12one π₁ I Fthr ∪ Q3one π₁ g₁ I Fthr Nthr := by
        by_cases hvF2 : v ∈ F2set π₁ g₁ I Fthr Nthr
        · refine Finset.mem_union_right _ ?_
          simp only [Q3one, Finset.mem_filter, Finset.mem_univ, true_and]
          unfold mkEdge; split_ifs <;> simp [hvF2]
        · refine Finset.mem_union_left _ ?_
          simp only [Q12one, Finset.mem_filter, Finset.mem_univ, true_and]
          have hvnotk : v ∉ I.image π₁ \ F1set π₁ I Fthr := by
            intro hmem
            have h1 := (Finset.mem_sdiff.mp hmem).1
            have h2 := (Finset.mem_sdiff.mp hmem).2
            exact hvnot (Finset.mem_sdiff.mpr ⟨h1, by simp [h2, hvF2]⟩)
          unfold mkEdge
          split_ifs
          · intro ⟨h1, _⟩; exact hvnotk h1
          · intro ⟨_, h2⟩; exact hvnotk h2
      simp [gAdj, hne, hag _ heQ]
  -- Verify `hQ₂` and `hQ₃` for `Pr_bernW_adaptive3_le`!
  have hQ₂_dep : ∀ f₁ f₂, (∀ e ∈ Q₁, f₁ e = f₂ e) → Q₂ f₁ = Q₂ f₂ := by
    intro f₁ f₂ hag
    have hR : F2set π.1 (gPairEquiv m f₁).1 I Fthr Nthr = F2set π.1 (gPairEquiv m f₂).1 I Fthr Nthr :=
      hF2_dep π.1 _ _ (fun e he => hag (Sum.inl e) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ he)))
    have hB : F2set π.2 (gPairEquiv m f₁).2 I Fthr Nthr = F2set π.2 (gPairEquiv m f₂).2 I Fthr Nthr :=
      hF2_dep π.2 _ _ (fun e he => hag (Sum.inr e) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)))
    simp only [Q₂, Q3one, hR, hB]
  have hQ₃_dep : ∀ f₁ f₂, (∀ e ∈ Q₁ ∪ Q₂ f₁, f₁ e = f₂ e) → Q₃ f₁ = Q₃ f₂ := by
    intro f₁ f₂ hag
    have hagR : ∀ e ∈ Q12one π.1 I Fthr ∪ Q3one π.1 (gPairEquiv m f₁).1 I Fthr Nthr,
        (gPairEquiv m f₁).1 e = (gPairEquiv m f₂).1 e := by
      intro e he
      rcases Finset.mem_union.mp he with h1 | h2
      · exact hag (Sum.inl e) (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h1)))
      · exact hag (Sum.inl e) (Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h2)))
    have hagB : ∀ e ∈ Q12one π.2 I Fthr ∪ Q3one π.2 (gPairEquiv m f₁).2 I Fthr Nthr,
        (gPairEquiv m f₁).2 e = (gPairEquiv m f₂).2 e := by
      intro e he
      rcases Finset.mem_union.mp he with h1 | h2
      · exact hag (Sum.inr e) (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ h1)))
      · exact hag (Sum.inr e) (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ h2)))
    have hF2R : F2set π.1 (gPairEquiv m f₁).1 I Fthr Nthr = F2set π.1 (gPairEquiv m f₂).1 I Fthr Nthr :=
      hF2_dep π.1 _ _ (fun e he => hagR e (Finset.mem_union_left _ he))
    have hF2B : F2set π.2 (gPairEquiv m f₁).2 I Fthr Nthr = F2set π.2 (gPairEquiv m f₂).2 I Fthr Nthr :=
      hF2_dep π.2 _ _ (fun e he => hagB e (Finset.mem_union_left _ he))
    have hFR_eq : Ffull π.1 (gPairEquiv m f₁).1 I Fthr Nthr = Ffull π.1 (gPairEquiv m f₂).1 I Fthr Nthr := by
      simp [Ffull, hF2R]
    have hFB_eq : Ffull π.2 (gPairEquiv m f₁).2 I Fthr Nthr = Ffull π.2 (gPairEquiv m f₂).2 I Fthr Nthr := by
      simp [Ffull, hF2B]
    have hQ4R : Q4one π.1 π.2 (gPairEquiv m f₁).1 (gPairEquiv m f₁).2 I Fthr Nthr =
        Q4one π.1 π.2 (gPairEquiv m f₂).1 (gPairEquiv m f₂).2 I Fthr Nthr := by
      simp only [Q4one]
      congr 1
      · rw [← hFR_eq]; exact Finset.biUnion_congr rfl fun r hr => by rw [hXV_dep π.1 _ _ hagR r hr]
      · rw [← hFB_eq]; exact Finset.biUnion_congr rfl fun b hb => by rw [hXV_dep π.2 _ _ hagB b hb]
    have hQ4B : Q4one π.2 π.1 (gPairEquiv m f₁).2 (gPairEquiv m f₁).1 I Fthr Nthr =
        Q4one π.2 π.1 (gPairEquiv m f₂).2 (gPairEquiv m f₂).1 I Fthr Nthr := by
      simp only [Q4one]
      congr 1
      · rw [← hFB_eq]; exact Finset.biUnion_congr rfl fun b hb => by rw [hXV_dep π.2 _ _ hagB b hb]
      · rw [← hFR_eq]; exact Finset.biUnion_congr rfl fun r hr => by rw [hXV_dep π.1 _ _ hagR r hr]
    simp only [Q₃, hQ4R, hQ4B]
  -- Apply `Pr_bernW_adaptive3_le`!
  apply Pr_bernW_adaptive3_le hp0 hp1 Q₁ Q₂ Q₃ hQ₂_dep hQ₃_dep
  intro f₀
  let g₀ := gPairEquiv m f₀
  let QR : Finset (Pair m) :=
    Q12one π.1 I Fthr ∪ Q3one π.1 g₀.1 I Fthr Nthr ∪ Q4one π.1 π.2 g₀.1 g₀.2 I Fthr Nthr
  let QB : Finset (Pair m) :=
    Q12one π.2 I Fthr ∪ Q3one π.2 g₀.2 I Fthr Nthr ∪ Q4one π.2 π.1 g₀.2 g₀.1 I Fthr Nthr
  let ER : Finset (Pair m) := QRᶜ
  let EB : Finset (Pair m) := QBᶜ
  have hQ_eq : Q₁ ∪ Q₂ f₀ ∪ Q₃ f₀ = QR.image Sum.inl ∪ QB.image Sum.inr := by
    ext x; cases x <;> simp [Q₁, Q₂, Q₃, QR, QB, g₀]
  -- Rewrite back to `prodW (bernW (Pair m) p) (bernW (Pair m) p)`!
  have hmerge_pair : ∀ y : Pair m ⊕ Pair m → Bool,
      gPairEquiv m (mergeOn (Q₁ ∪ Q₂ f₀ ∪ Q₃ f₀) f₀ y) =
      (mergeOn ERᶜ g₀.1 (gPairEquiv m y).1, mergeOn EBᶜ g₀.2 (gPairEquiv m y).2) := by
    intro y
    rw [hQ_eq]
    apply Prod.ext <;> funext e
    · by_cases he : e ∈ QR
      · simp [gPairEquiv, mergeOn, ER, he, g₀]
      · simp [gPairEquiv, mergeOn, ER, he]
    · by_cases he : e ∈ QB
      · simp [gPairEquiv, mergeOn, EB, he, g₀]
      · simp [gPairEquiv, mergeOn, EB, he]
  have hPr_eq : Pr (bernW (Pair m ⊕ Pair m) p) (fun y =>
        IndepI π (gPairEquiv m (mergeOn (Q₁ ∪ Q₂ f₀ ∪ Q₃ f₀) f₀ y)) I ∧
        Reg (gPairEquiv m (mergeOn (Q₁ ∪ Q₂ f₀ ∪ Q₃ f₀) f₀ y))) =
      Pr (prodW (bernW (Pair m) p) (bernW (Pair m) p)) (fun y =>
        IndepI π (mergeOn ERᶜ g₀.1 y.1, mergeOn EBᶜ g₀.2 y.2) I ∧
        Reg (mergeOn ERᶜ g₀.1 y.1, mergeOn EBᶜ g₀.2 y.2)) := by
    rw [← Pr_equiv (gPairEquiv m)]
    have hwt2 : (fun y => prodW (bernW (Pair m) p) (bernW (Pair m) p) (gPairEquiv m y)) =
        bernW (Pair m ⊕ Pair m) p := funext (gPairW_eq_bernW p)
    rw [hwt2]
    exact Pr_congr fun y => by rw [hmerge_pair y]
  rw [hPr_eq]
  -- Check `ER.card ≤ k^2` and `EB.card ≤ k^2`!
  have hER_sub : ER ⊆ projPairs π.1 I := by
    intro e he
    have hnotQ12 : e ∉ Q12one π.1 I Fthr := fun h =>
      (Finset.mem_compl.mp he) (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    simp only [Q12one, Finset.mem_filter, Finset.mem_univ, true_and, not_not, Finset.mem_sdiff] at hnotQ12
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, hnotQ12.1.1, hnotQ12.2.1⟩
  have hEB_sub : EB ⊆ projPairs π.2 I := by
    intro e he
    have hnotQ12 : e ∉ Q12one π.2 I Fthr := fun h =>
      (Finset.mem_compl.mp he) (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    simp only [Q12one, Finset.mem_filter, Finset.mem_univ, true_and, not_not, Finset.mem_sdiff] at hnotQ12
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, hnotQ12.1.1, hnotQ12.2.1⟩
  have hER_le : ER.card ≤ k ^ 2 := by
    calc ER.card ≤ (projPairs π.1 I).card := Finset.card_le_card hER_sub
      _ = (I.image π.1).card.choose 2 := projPairs_card _ _
      _ ≤ (I.image π.1).card * (I.image π.1).card := by
          rw [Nat.choose_two_right]; exact Nat.div_le_self _ 2 |>.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
      _ ≤ I.card * I.card := Nat.mul_le_mul Finset.card_image_le Finset.card_image_le
      _ = k ^ 2 := by rw [hI, sq]
  have hEB_le : EB.card ≤ k ^ 2 := by
    calc EB.card ≤ (projPairs π.2 I).card := Finset.card_le_card hEB_sub
      _ = (I.image π.2).card.choose 2 := projPairs_card _ _
      _ ≤ (I.image π.2).card * (I.image π.2).card := by
          rw [Nat.choose_two_right]; exact Nat.div_le_self _ 2 |>.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
      _ ≤ I.card * I.card := Nat.mul_le_mul Finset.card_image_le Finset.card_image_le
      _ = k ^ 2 := by rw [hI, sq]
  -- Helper: key deterministic properties of `g = (mergeOn ERᶜ g₀.1 y.1, mergeOn EBᶜ g₀.2 y.2)`!
  have hF2_same : ∀ y₁ y₂,
      F2set π.1 (mergeOn ERᶜ g₀.1 y₁) I Fthr Nthr = F2set π.1 g₀.1 I Fthr Nthr ∧
      F2set π.2 (mergeOn EBᶜ g₀.2 y₂) I Fthr Nthr = F2set π.2 g₀.2 I Fthr Nthr := by
    intro y₁ y₂
    constructor
    · exact hF2_dep π.1 _ _ (fun e he => mergeOn_mem ERᶜ g₀.1 y₁
        (by simp [ER, QR, he]))
    · exact hF2_dep π.2 _ _ (fun e he => mergeOn_mem EBᶜ g₀.2 y₂
        (by simp [EB, QB, he]))
  have hXV_same : ∀ y₁ y₂,
      (∀ v ∈ Ffull π.1 g₀.1 I Fthr Nthr, XV π.1 (mergeOn ERᶜ g₀.1 y₁) I v = XV π.1 g₀.1 I v) ∧
      (∀ v ∈ Ffull π.2 g₀.2 I Fthr Nthr, XV π.2 (mergeOn EBᶜ g₀.2 y₂) I v = XV π.2 g₀.2 I v) := by
    intro y₁ y₂
    constructor
    · intro v hv
      exact (hXV_dep π.1 g₀.1 (mergeOn ERᶜ g₀.1 y₁)
        (fun e he => (mergeOn_mem ERᶜ g₀.1 y₁ (by
          simp only [ER, Finset.mem_compl, not_not, QR]
          rcases Finset.mem_union.mp he with h1 | h2
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ h1)
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ h2))).symm) v hv).symm
    · intro v hv
      exact (hXV_dep π.2 g₀.2 (mergeOn EBᶜ g₀.2 y₂)
        (fun e he => (mergeOn_mem EBᶜ g₀.2 y₂ (by
          simp only [EB, Finset.mem_compl, not_not, QB]
          rcases Finset.mem_union.mp he with h1 | h2
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ h1)
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ h2))).symm) v hv).symm
  -- Helper: active red true edge in `ER` must lie in `C_BtoR(gB)`!
  have hall_R : ∀ y₁ y₂,
      IndepI π (mergeOn ERᶜ g₀.1 y₁, mergeOn EBᶜ g₀.2 y₂) I →
      allActiveIn (sortPairs ER)
        (((I.image π.2) \ (F1set π.2 I Fthr ∪ F2set π.2 g₀.2 I Fthr Nthr)).biUnion
          (fun b => projPairs π.1 (XV π.2 (mergeOn EBᶜ g₀.2 y₂) I b)))
        (triAct ER g₀.1) y₁ := by
    intro y₁ y₂ hInd k' hk' hact hy1
    set e := (sortPairs ER)[k']
    have heER : e ∈ ER := (mem_sortPairs ER e).mp (List.getElem_mem hk')
    have heI : e.1.1 ∈ I.image π.1 ∧ e.1.2 ∈ I.image π.1 := (Finset.mem_filter.mp (hER_sub heER)).2
    obtain ⟨u, huI, hπu⟩ := Finset.mem_image.mp heI.1
    obtain ⟨v, hvI, hπv⟩ := Finset.mem_image.mp heI.2
    have huv : u ≠ v := fun h => e.2.ne (hπu.symm.trans (h ▸ hπv))
    set gR := mergeOn ERᶜ g₀.1 y₁
    set gB := mergeOn EBᶜ g₀.2 y₂
    have hnot_adj : ¬ (twoBitesGraph π.1 π.2 gR gB).Adj u v := hInd huI hvI huv
    have hnot_red : ¬ redSurv π.1 π.2 gR gB u v := fun h => hnot_adj (Or.inl h)
    have hge : gAdj gR (π.1 u) (π.1 v) = true := by
      have hne : π.1 u ≠ π.1 v := by rw [hπu, hπv]; exact e.2.ne
      have hmk : mkEdge (π.1 u) (π.1 v) hne = e := by
        apply Subtype.ext; simp only [mkEdge, hπu, hπv, dif_pos e.2]
      have hnotc : e ∉ ERᶜ := by simp [heER]
      simp [gAdj, hne, hmk, gR, mergeOn_notMem _ _ _ hnotc, hy1]
    have hno_r : ¬ ∃ r : Fin m, r < min (π.1 u) (π.1 v) ∧ gAdj gR r (π.1 u) = true ∧ gAdj gR r (π.1 v) = true := by
      simp only [triAct, dif_pos hk', decide_eq_true_eq] at hact
      rintro ⟨r, hlt, ha, hb⟩
      rw [hπu, hπv, min_eq_left e.2.le] at hlt
      rw [hπu] at ha; rw [hπv] at hb
      exact hact ⟨r, hlt, ha, hb⟩
    have hex_b : ∃ b : Fin m, gAdj gB b (π.2 u) = true ∧ gAdj gB b (π.2 v) = true := by
      by_contra hno_b
      exact hnot_red ⟨hge, hno_r, hno_b⟩
    obtain ⟨b, hbu, hbv⟩ := hex_b
    have he_b : e ∈ projPairs π.1 (XV π.2 gB I b) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ e, ?_, ?_⟩
      · rw [← hπu]; exact Finset.mem_image_of_mem π.1 (Finset.mem_filter.mpr ⟨huI, hbu⟩)
      · rw [← hπv]; exact Finset.mem_image_of_mem π.1 (Finset.mem_filter.mpr ⟨hvI, hbv⟩)
    have hb_not_F : b ∉ Ffull π.2 g₀.2 I Fthr Nthr := by
      intro hbF
      have heQ4 : e ∈ Q4one π.1 π.2 g₀.1 g₀.2 I Fthr Nthr := by
        refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b, hbF, ?_⟩)
        rw [← (hXV_same y₁ y₂).2 b hbF]
        exact he_b
      exact (Finset.mem_compl.mp heER) (Finset.mem_union_right _ heQ4)
    have hb_keep : b ∈ (I.image π.2) \ (F1set π.2 I Fthr ∪ F2set π.2 g₀.2 I Fthr Nthr) := by
      simpa only [Ffull, Finset.mem_compl, not_not] using hb_not_F
    exact Finset.mem_biUnion.mpr ⟨b, hb_keep, he_b⟩
  -- Symmetric helper for blue!
  have hall_B : ∀ y₁ y₂,
      IndepI π (mergeOn ERᶜ g₀.1 y₁, mergeOn EBᶜ g₀.2 y₂) I →
      allActiveIn (sortPairs EB)
        (((I.image π.1) \ (F1set π.1 I Fthr ∪ F2set π.1 g₀.1 I Fthr Nthr)).biUnion
          (fun r => projPairs π.2 (XV π.1 (mergeOn ERᶜ g₀.1 y₁) I r)))
        (triAct EB g₀.2) y₂ := by
    intro y₁ y₂ hInd k' hk' hact hy2
    set e := (sortPairs EB)[k']
    have heEB : e ∈ EB := (mem_sortPairs EB e).mp (List.getElem_mem hk')
    have heI : e.1.1 ∈ I.image π.2 ∧ e.1.2 ∈ I.image π.2 := (Finset.mem_filter.mp (hEB_sub heEB)).2
    obtain ⟨u, huI, hπu⟩ := Finset.mem_image.mp heI.1
    obtain ⟨v, hvI, hπv⟩ := Finset.mem_image.mp heI.2
    have huv : u ≠ v := fun h => e.2.ne (hπu.symm.trans (h ▸ hπv))
    set gR := mergeOn ERᶜ g₀.1 y₁
    set gB := mergeOn EBᶜ g₀.2 y₂
    have hnot_adj : ¬ (twoBitesGraph π.1 π.2 gR gB).Adj u v := hInd huI hvI huv
    have hnot_blue : ¬ blueSurv π.1 π.2 gR gB u v := fun h => hnot_adj (Or.inr h)
    have hge : gAdj gB (π.2 u) (π.2 v) = true := by
      have hne : π.2 u ≠ π.2 v := by rw [hπu, hπv]; exact e.2.ne
      have hmk : mkEdge (π.2 u) (π.2 v) hne = e := by
        apply Subtype.ext; simp only [mkEdge, hπu, hπv, dif_pos e.2]
      have hnotc : e ∉ EBᶜ := by simp [heEB]
      simp [gAdj, hne, hmk, gB, mergeOn_notMem _ _ _ hnotc, hy2]
    have hno_b : ¬ ∃ b : Fin m, b < min (π.2 u) (π.2 v) ∧ gAdj gB b (π.2 u) = true ∧ gAdj gB b (π.2 v) = true := by
      simp only [triAct, dif_pos hk', decide_eq_true_eq] at hact
      rintro ⟨b, hlt, ha, hb⟩
      rw [hπu, hπv, min_eq_left e.2.le] at hlt
      rw [hπu] at ha; rw [hπv] at hb
      exact hact ⟨b, hlt, ha, hb⟩
    have hex_r : ∃ r : Fin m, gAdj gR r (π.1 u) = true ∧ gAdj gR r (π.1 v) = true := by
      by_contra hno_r
      exact hnot_blue ⟨hge, hno_b, hno_r⟩
    obtain ⟨r, hru, hrv⟩ := hex_r
    have he_r : e ∈ projPairs π.2 (XV π.1 gR I r) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ e, ?_, ?_⟩
      · rw [← hπu]; exact Finset.mem_image_of_mem π.2 (Finset.mem_filter.mpr ⟨huI, hru⟩)
      · rw [← hπv]; exact Finset.mem_image_of_mem π.2 (Finset.mem_filter.mpr ⟨hvI, hrv⟩)
    have hr_not_F : r ∉ Ffull π.1 g₀.1 I Fthr Nthr := by
      intro hrF
      have heQ4 : e ∈ Q4one π.2 π.1 g₀.2 g₀.1 I Fthr Nthr := by
        refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, hrF, ?_⟩)
        rw [← (hXV_same y₁ y₂).1 r hrF]
        exact he_r
      exact (Finset.mem_compl.mp heEB) (Finset.mem_union_right _ heQ4)
    have hr_keep : r ∈ (I.image π.1) \ (F1set π.1 I Fthr ∪ F2set π.1 g₀.1 I Fthr Nthr) := by
      simpa only [Ffull, Finset.mem_compl, not_not] using hr_not_F
    exact Finset.mem_biUnion.mpr ⟨r, hr_keep, he_r⟩
  -- Helper: every open pair outside `Q12 ∪ Q3` is an active false bit in `ER` (resp. `EB`)!
  have hZ_lower : ∀ y₁ y₂,
      IndepI π (mergeOn ERᶜ g₀.1 y₁, mergeOn EBᶜ g₀.2 y₂) I →
      Reg (mergeOn ERᶜ g₀.1 y₁, mergeOn EBᶜ g₀.2 y₂) →
      Z_min ≤ actCount (sortPairs ER) (triAct ER g₀.1) false y₁ +
              actCount (sortPairs EB) (triAct EB g₀.2) false y₂ := by
    intro y₁ y₂ hInd hReg
    have hZ0 := hReg_Z (mergeOn ERᶜ g₀.1 y₁, mergeOn EBᶜ g₀.2 y₂) hInd hReg
    have hZR := open_unrev_le_actCount π.1 π.2 g₀.1 g₀.2 y₁ y₂ I ER rfl
      (mergeOn ERᶜ g₀.1 y₁) (mergeOn EBᶜ g₀.2 y₂) rfl
      (hF2_same y₁ y₂).1 (hXV_same y₁ y₂).1 (hXV_same y₁ y₂).2
      (fun u hu v hv huv h => hInd hu hv huv (Or.inl h))
    have hZB_raw := open_unrev_le_actCount π.2 π.1 g₀.2 g₀.1 y₂ y₁ I EB rfl
      (mergeOn EBᶜ g₀.2 y₂) (mergeOn ERᶜ g₀.1 y₁) rfl
      (hF2_same y₁ y₂).2 (hXV_same y₁ y₂).2 (hXV_same y₁ y₂).1
      (fun u hu v hv huv h => hInd hu hv huv (Or.inr h))
    have hswapU : Finset.univ.biUnion (fun v : Fin m ⊕ Fin m =>
        projPairs π.2 (XAll (π.2, π.1) (mergeOn EBᶜ g₀.2 y₂, mergeOn ERᶜ g₀.1 y₁) I v)) =
        Finset.univ.biUnion (fun v : Fin m ⊕ Fin m =>
        projPairs π.2 (XAll π (mergeOn ERᶜ g₀.1 y₁, mergeOn EBᶜ g₀.2 y₂) I v)) := by
      ext e
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨v, hv⟩
        cases v with
        | inl b => exact ⟨Sum.inr b, by rw [XAll_inr]; rw [XAll_inl] at hv; exact hv⟩
        | inr r => exact ⟨Sum.inl r, by rw [XAll_inl]; rw [XAll_inr] at hv; exact hv⟩
      · rintro ⟨v, hv⟩
        cases v with
        | inl r => exact ⟨Sum.inr r, by rw [XAll_inr]; rw [XAll_inl] at hv; exact hv⟩
        | inr b => exact ⟨Sum.inl b, by rw [XAll_inl]; rw [XAll_inr] at hv; exact hv⟩
    rw [hswapU] at hZB_raw
    exact hZ0.trans (Nat.add_le_add hZR hZB_raw)
  -- Split into `U_B ≤ U_R` and `U_R ≤ U_B` and apply `inner_half_bound` to BOTH halves!
  have hP := isProb_prodW (isProb_bernW (ι := Pair m) hp0 hp1) (isProb_bernW (ι := Pair m) hp0 hp1)
  have hhalf1 : Pr (prodW (bernW (Pair m) p) (bernW (Pair m) p)) (fun y =>
        IndepI π (mergeOn ERᶜ g₀.1 y.1, mergeOn EBᶜ g₀.2 y.2) I ∧
        Reg (mergeOn ERᶜ g₀.1 y.1, mergeOn EBᶜ g₀.2 y.2) ∧
        actCount (sortPairs EB) (triAct EB g₀.2) true y.2 ≤
          actCount (sortPairs ER) (triAct ER g₀.1) true y.1) ≤
      Real.exp (((M₁ : ℝ) / r + r * ((k ^ 2 : ℕ) : ℝ)) * p - p * (Z_min : ℝ)) := by
    exact inner_half_bound (M₁ := M₁) (M₂ := k ^ 2) (Z_min := Z_min)
      hp0 hp1 hr0 hr1 ER EB hEB_le g₀.1 g₀.2
      (fun y₂ => ((I.image π.2) \ (F1set π.2 I Fthr ∪ F2set π.2 g₀.2 I Fthr Nthr)).biUnion
        (fun b => projPairs π.1 (XV π.2 (mergeOn EBᶜ g₀.2 y₂) I b)))
      (fun y₁ y₂ => IndepI π (mergeOn ERᶜ g₀.1 y₁, mergeOn EBᶜ g₀.2 y₂) I ∧
        Reg (mergeOn ERᶜ g₀.1 y₁, mergeOn EBᶜ g₀.2 y₂) ∧
        actCount (sortPairs EB) (triAct EB g₀.2) true y₂ ≤ actCount (sortPairs ER) (triAct ER g₀.1) true y₁)
      (fun y₁ y₂ ⟨hInd, hReg, hle⟩ => by
        refine ⟨hall_R y₁ y₂ hInd, ?_, hle, hZ_lower y₁ y₂ hInd hReg⟩
        have hC := hReg_C1 (mergeOn ERᶜ g₀.1 y₁, mergeOn EBᶜ g₀.2 y₂) hInd hReg
        rwa [(hF2_same y₁ y₂).2] at hC)
  have hhalf2 : Pr (prodW (bernW (Pair m) p) (bernW (Pair m) p)) (fun y =>
        IndepI π (mergeOn ERᶜ g₀.1 y.1, mergeOn EBᶜ g₀.2 y.2) I ∧
        Reg (mergeOn ERᶜ g₀.1 y.1, mergeOn EBᶜ g₀.2 y.2) ∧
        actCount (sortPairs ER) (triAct ER g₀.1) true y.1 ≤
          actCount (sortPairs EB) (triAct EB g₀.2) true y.2) ≤
      Real.exp (((M₁ : ℝ) / r + r * ((k ^ 2 : ℕ) : ℝ)) * p - p * (Z_min : ℝ)) := by
    let eSwap : ((Pair m → Bool) × (Pair m → Bool)) ≃ ((Pair m → Bool) × (Pair m → Bool)) :=
      Equiv.prodComm _ _
    rw [← Pr_equiv eSwap]
    have hwt_s : (fun y => prodW (bernW (Pair m) p) (bernW (Pair m) p) (eSwap y)) =
        prodW (bernW (Pair m) p) (bernW (Pair m) p) := by
      funext ⟨a, b⟩; simp [prodW, eSwap, mul_comm]
    rw [hwt_s]
    exact inner_half_bound (M₁ := M₁) (M₂ := k ^ 2) (Z_min := Z_min)
      hp0 hp1 hr0 hr1 EB ER hER_le g₀.2 g₀.1
      (fun y₁ => ((I.image π.1) \ (F1set π.1 I Fthr ∪ F2set π.1 g₀.1 I Fthr Nthr)).biUnion
        (fun r => projPairs π.2 (XV π.1 (mergeOn ERᶜ g₀.1 y₁) I r)))
      (fun y₂ y₁ => IndepI π (mergeOn ERᶜ g₀.1 y₁, mergeOn EBᶜ g₀.2 y₂) I ∧
        Reg (mergeOn ERᶜ g₀.1 y₁, mergeOn EBᶜ g₀.2 y₂) ∧
        actCount (sortPairs ER) (triAct ER g₀.1) true y₁ ≤ actCount (sortPairs EB) (triAct EB g₀.2) true y₂)
      (fun y₂ y₁ ⟨hInd, hReg, hle⟩ => by
        refine ⟨hall_B y₁ y₂ hInd, ?_, hle, ?_⟩
        · have hC := hReg_C2 (mergeOn ERᶜ g₀.1 y₁, mergeOn EBᶜ g₀.2 y₂) hInd hReg
          rwa [(hF2_same y₁ y₂).1] at hC
        · have := hZ_lower y₁ y₂ hInd hReg; omega)
  have hsplit : ∀ y : (Pair m → Bool) × (Pair m → Bool),
      (IndepI π (mergeOn ERᶜ g₀.1 y.1, mergeOn EBᶜ g₀.2 y.2) I ∧
       Reg (mergeOn ERᶜ g₀.1 y.1, mergeOn EBᶜ g₀.2 y.2)) →
      (IndepI π (mergeOn ERᶜ g₀.1 y.1, mergeOn EBᶜ g₀.2 y.2) I ∧
       Reg (mergeOn ERᶜ g₀.1 y.1, mergeOn EBᶜ g₀.2 y.2) ∧
       actCount (sortPairs EB) (triAct EB g₀.2) true y.2 ≤ actCount (sortPairs ER) (triAct ER g₀.1) true y.1) ∨
      (IndepI π (mergeOn ERᶜ g₀.1 y.1, mergeOn EBᶜ g₀.2 y.2) I ∧
       Reg (mergeOn ERᶜ g₀.1 y.1, mergeOn EBᶜ g₀.2 y.2) ∧
       actCount (sortPairs ER) (triAct ER g₀.1) true y.1 ≤ actCount (sortPairs EB) (triAct EB g₀.2) true y.2) := by
    intro y ⟨h1, h2⟩
    rcases le_total (actCount (sortPairs EB) (triAct EB g₀.2) true y.2)
      (actCount (sortPairs ER) (triAct ER g₀.1) true y.1) with hle | hle
    · exact Or.inl ⟨h1, h2, hle⟩
    · exact Or.inr ⟨h1, h2, hle⟩
  calc Pr (prodW (bernW (Pair m) p) (bernW (Pair m) p)) _
      ≤ Pr (prodW (bernW (Pair m) p) (bernW (Pair m) p)) (fun y =>
          (IndepI π (mergeOn ERᶜ g₀.1 y.1, mergeOn EBᶜ g₀.2 y.2) I ∧
           Reg (mergeOn ERᶜ g₀.1 y.1, mergeOn EBᶜ g₀.2 y.2) ∧
           actCount (sortPairs EB) (triAct EB g₀.2) true y.2 ≤ actCount (sortPairs ER) (triAct ER g₀.1) true y.1) ∨
          (IndepI π (mergeOn ERᶜ g₀.1 y.1, mergeOn EBᶜ g₀.2 y.2) I ∧
           Reg (mergeOn ERᶜ g₀.1 y.1, mergeOn EBᶜ g₀.2 y.2) ∧
           actCount (sortPairs ER) (triAct ER g₀.1) true y.1 ≤ actCount (sortPairs EB) (triAct EB g₀.2) true y.2)) :=
        Pr_mono hP hsplit
    _ ≤ _ + _ := Pr_or_le hP _ _
    _ ≤ 2 * Real.exp (((M₁ : ℝ) / r + r * ((k ^ 2 : ℕ) : ℝ)) * p - p * (Z_min : ℝ)) := by linarith

end Lemma41RISI

end Erdos1013RISI
namespace Erdos1013Assembly

open Finset BigOperators SimpleGraph Filter Erdos1013Prob Erdos1013Model Erdos1013ClosedPairs Erdos1013RISI

section ConfigAndGoodEvent

/-- Scaling invariance of `gCap`: `gCap (c * M) (c * y) = c^2 * gCap M y` for `c > 0`. -/
lemma gCap_scale {c M y : ℝ} (hc : 0 < c) :
    gCap (c * M) (c * y) = c ^ 2 * gCap M y := by
  unfold gCap
  have hiff : c * y ≤ c * M ↔ y ≤ M := mul_le_mul_iff_right₀ hc
  by_cases h : y ≤ M
  · rw [if_pos (hiff.mpr h), if_pos h]; ring
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]; ring

/-- Concrete non-asymptotic parameter bundle for the two-bites construction. -/
structure Cfg where
  n : ℕ
  m : ℕ
  k : ℕ
  Fmax : ℕ
  Dmax : ℕ
  Nmax : ℕ
  t_codeg : ℕ
  t_cross : ℕ
  t_proj : ℕ
  L_cap : ℕ
  H_cap : ℕ
  b₀ : ℕ
  t_med : ℕ
  M₁ : ℕ
  ε : ℝ
  r : ℝ
  ε₁ : ℝ
  ε₂ : ℝ
  p : ℝ
  t₁ : ℝ
  t₂ : ℝ
  t₃ : ℝ
  Ylim : ℝ
  t_small : ℝ
  Fthr : ℝ
  Nthr : ℝ

def Cfg.Smax (c : Cfg) : ℕ := c.t_codeg * c.Fmax
def Cfg.C_int (c : Cfg) : ℕ := max c.Smax c.t_cross
def Cfg.C_proj (c : Cfg) : ℕ := c.Smax + c.t_proj
noncomputable def Cfg.L (c : Cfg) : ℝ := Real.log (c.n : ℝ)

/-- Target open-pair quadratic functional `f(ℓR, ℓB)`. -/
noncomputable def Cfg.fVal (c : Cfg) (ℓR ℓB : ℕ) : ℝ :=
  (ℓR : ℝ) ^ 2 / 2 + (ℓB : ℝ) ^ 2 / 2 -
    gCap (c.p * (c.n : ℝ)) ((c.k - ℓR : ℕ) : ℝ) -
    gCap (c.p * (c.n : ℝ)) ((c.k - ℓB : ℕ) : ℝ)

/-- Exact finite set of non-asymptotic inequalities needed by the proof. -/
structure ValidCfg (c : Cfg) : Prop where
  hn : 3 ≤ c.n
  hm : 1 ≤ c.m
  hk1 : 1 ≤ c.k
  hkm : c.k ≤ c.m
  hε0 : 0 < c.ε
  hε32 : c.ε ≤ 1 / 32
  hr_eq : c.r = c.ε ^ 3 / 100
  hε₁_eq : c.ε₁ = c.r ^ 2
  hε₂_eq : c.ε₂ = c.ε₁ / 100
  hp0 : 0 ≤ c.p
  hp1 : c.p ≤ 1
  ht₁0 : 0 ≤ c.t₁
  ht₂0 : 0 < c.t₂
  ht₃0 : 0 < c.t₃
  ht_small0 : 0 ≤ c.t_small
  hFthr0 : 0 < c.Fthr
  hNthr_eq : c.Nthr = c.t₂ / c.Fthr
  ht_codeg1 : 1 ≤ c.t_codeg
  ht_cross1 : 1 ≤ c.t_cross
  ht_proj1 : 1 ≤ c.t_proj
  ht_med1 : 1 ≤ c.t_med
  hFmax_ge : (1 + c.ε₂ / 3) * ((c.n : ℝ) / (c.m : ℝ)) ≤ (c.Fmax : ℝ)
  hDmax_ge : (1 + c.ε₂ / 3) * (((c.m - 1 : ℕ) : ℝ) * c.p) ≤ (c.Dmax : ℝ)
  hNmax_ge : (1 + c.ε₂) * (c.p * (c.n : ℝ)) ≤ (c.Nmax : ℝ)
  hM₁_eq : c.M₁ = ⌊3 * c.ε₁ * (c.k : ℝ) ^ 2⌋₊
  hPr_fiber : (c.m : ℝ) * (2 * Real.exp (-(c.ε₂ / 3) ^ 2 * ((c.n : ℝ) / (c.m : ℝ)) / 4)) ≤ 1 / 40
  hPr_deg : (c.m : ℝ) * (2 * Real.exp (-(c.ε₂ / 3) ^ 2 * (((c.m - 1 : ℕ) : ℝ) * c.p) / 4)) ≤ 1 / 40
  hPr_codeg : (c.m : ℝ) ^ 2 * (Real.exp 1 * (c.m : ℝ) * c.p ^ 2 / (c.t_codeg : ℝ)) ^ c.t_codeg ≤ 1 / 40
  hPr_cross : (c.m : ℝ) ^ 2 * (Real.exp 1 * (c.n : ℝ) * ((c.Dmax : ℝ) / (c.m : ℝ)) ^ 2 / (c.t_cross : ℝ)) ^ c.t_cross ≤ 1 / 40
  hPr_proj : (c.m : ℝ) ^ 2 * (Real.exp 1 * (c.Nmax : ℝ) ^ 2 / ((c.m : ℝ) * (c.t_proj : ℝ))) ^ c.t_proj ≤ 1 / 40
  hMed_ht₂ : c.t₂ ≤ c.Ylim
  hMed_b₀_ge : 2 * c.Ylim / c.t₃ ≤ (c.b₀ : ℝ)
  hMed_b₀_le : c.b₀ ≤ 2 * c.m
  hMed_tmed_le : ((2 * c.Fmax * c.t_med : ℕ) : ℝ) ≤ c.Ylim
  hPr_med : (c.n.choose c.k : ℝ) * ((2 * c.m).choose c.b₀ : ℝ) *
    (Real.exp 1 * ((c.b₀ * c.k : ℕ) : ℝ) * c.p / (c.t_med : ℝ)) ^ c.t_med ≤ 1 / 40
  hPr_small : (c.n.choose c.k : ℝ) * Real.exp (-2 * c.t_small ^ 2 / ((2 * (c.m : ℝ)) * (c.t₃ ^ 2 / 2) ^ 2)) ≤ 1 / 40
  hLcap : (c.k : ℝ) + ((c.L_cap.choose 2 * c.C_int : ℕ) : ℝ) < (c.L_cap : ℝ) * c.t₂
  hHcap : (c.k : ℝ) + ((c.H_cap.choose 2 * c.C_int : ℕ) : ℝ) < (c.H_cap : ℝ) * c.t₁
  hF2_sep : c.Nthr * (c.Fmax : ℝ) + (c.Dmax : ℝ) * c.Fthr ≤ c.t₁
  hL_loss : (c.t₁ / 2) * ((c.k : ℝ) + ((c.L_cap.choose 2 * c.C_int : ℕ) : ℝ)) ≤ c.ε₁ * (c.k : ℝ) ^ 2
  hM_loss : (c.t₂ / 2) * c.Ylim ≤ c.ε₁ * (c.k : ℝ) ^ 2
  hS_loss : (c.k : ℝ) * c.t₃ ^ 2 + (c.k : ℝ) * (c.Fmax : ℝ) +
    (c.k.choose 2 : ℝ) * (2 * (c.m : ℝ) * c.p ^ 2) + c.t_small ≤ c.ε₁ * (c.k : ℝ) ^ 2
  hH_same_loss : ((c.H_cap * c.Dmax : ℕ) : ℝ) ^ 2 / 2 ≤ c.ε₁ * (c.k : ℝ) ^ 2
  hH_cross_delta : ((c.H_cap * c.Dmax + c.H_cap.choose 2 * c.C_proj : ℕ) : ℝ) ≤ (c.ε₁ / 4) * (c.k : ℝ)
  hQ_loss : ((c.k : ℝ) / c.Fthr + (c.L_cap : ℝ) + (c.H_cap : ℝ)) * (c.k : ℝ) ≤ c.ε₁ * (c.k : ℝ) ^ 2
  hHalf_k : (c.k : ℝ) / 2 ≤ c.ε₁ * (c.k : ℝ) ^ 2
  hOne_le : 1 ≤ c.ε₁ * (c.k : ℝ) ^ 2
  hp_sq : c.p ^ 2 * (c.n : ℝ) = c.L / 4
  hpk_low : (1 + 7 * c.ε / 8) * (c.L / 2) ≤ c.p * (c.k : ℝ)
  hpk_high : c.p * (c.k : ℝ) ≤ (1 + c.ε) * (c.L / 2)
  h_n_div_k : (c.n : ℝ) / (c.k : ℝ) ≤ Real.exp (c.L / 2)
  h_k_div_m : (c.k : ℝ) / (c.m : ℝ) ≤ Real.exp (-(1 / 2 - c.ε ^ 3 / 40) * c.L)
  h_e3_le : Real.exp 3 ≤ Real.exp ((c.ε ^ 3 / 40) * c.L)
  h_final_sum : 2 * (c.k : ℝ) ^ 2 * Real.exp (-(c.ε ^ 2 / 8) * (c.k : ℝ) * c.L) < 1 / 4

/-- Individual regularity events in `GoodR`. -/
def GoodFiber (n m : ℕ) (δ : ℝ) (π₁ : Fin n → Fin m) : Prop :=
  ∀ v : Fin m, |((fiber π₁ v).card : ℝ) - (n : ℝ) / (m : ℝ)| < δ * ((n : ℝ) / (m : ℝ))

def GoodDeg (m : ℕ) (p δ : ℝ) (g₁ : Pair m → Bool) : Prop :=
  ∀ v : Fin m, |((nbrG g₁ v).card : ℝ) - ((m - 1 : ℕ) : ℝ) * p| < δ * (((m - 1 : ℕ) : ℝ) * p)

def GoodCodeg (m t_codeg : ℕ) (g₁ : Pair m → Bool) : Prop :=
  ∀ v w : Fin m, v ≠ w → (codegG g₁ v w).card < t_codeg

def GoodCross (n m t_cross : ℕ) (π : PiPair n m) (g : GPair m) : Prop :=
  ∀ v w : Fin m, (nbrV π.1 g.1 v ∩ nbrV π.2 g.2 w).card < t_cross

def GoodProj (n m Smax t_proj : ℕ) (π₁ π₂ : Fin n → Fin m) (g₁ : Pair m → Bool) : Prop :=
  ∀ v w : Fin m, v ≠ w → (projNbr π₁ π₂ g₁ v ∩ projNbr π₁ π₂ g₁ w).card < Smax + t_proj

def GoodMed (n m k : ℕ) (t₂ t₃ Ylim : ℝ) (π : PiPair n m) (g : GPair m) : Prop :=
  ∀ I : Finset (Fin n), I.card = k → ∑ v ∈ Mset π g I t₂ t₃, ((XAll π g I v).card : ℝ) ≤ Ylim

def GoodSmall (n m k Fmax : ℕ) (p t₃ t_small : ℝ) (π : PiPair n m) (g : GPair m) : Prop :=
  ∀ I : Finset (Fin n), I.card = k →
    (((Sset π g I t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ) ≤
      (k : ℝ) * t₃ ^ 2 + (k : ℝ) * (Fmax : ℝ) + (k.choose 2 : ℝ) * (2 * (m : ℝ) * p ^ 2) + t_small

/-- Combined high-probability regularity event `GoodR` on `Omega c.n c.m`. -/
def GoodR (c : Cfg) (ω : Omega c.n c.m) : Prop :=
  GoodFiber c.n c.m (c.ε₂ / 3) ω.1.1 ∧
  GoodFiber c.n c.m (c.ε₂ / 3) ω.1.2 ∧
  GoodDeg c.m c.p (c.ε₂ / 3) ω.2.1 ∧
  GoodDeg c.m c.p (c.ε₂ / 3) ω.2.2 ∧
  GoodCodeg c.m c.t_codeg ω.2.1 ∧
  GoodCodeg c.m c.t_codeg ω.2.2 ∧
  GoodCross c.n c.m c.t_cross ω.1 ω.2 ∧
  GoodProj c.n c.m c.Smax c.t_proj ω.1.1 ω.1.2 ω.2.1 ∧
  GoodProj c.n c.m c.Smax c.t_proj ω.1.2 ω.1.1 ω.2.2 ∧
  GoodMed c.n c.m c.k c.t₂ c.t₃ c.Ylim ω.1 ω.2 ∧
  GoodSmall c.n c.m c.k c.Fmax c.p c.t₃ c.t_small ω.1 ω.2

/-- Derived parameter positivity/bounds from `ValidCfg`. -/
lemma ValidCfg.hr_pos {c : Cfg} (hc : ValidCfg c) : 0 < c.r := by
  rw [hc.hr_eq]; have := hc.hε0; positivity

lemma ValidCfg.hr_le_one {c : Cfg} (hc : ValidCfg c) : c.r ≤ 1 := by
  rw [hc.hr_eq]
  have h1 : c.ε ^ 3 ≤ 1 := pow_le_one₀ hc.hε0.le (by linarith [hc.hε32])
  linarith

lemma ValidCfg.hε₁_pos {c : Cfg} (hc : ValidCfg c) : 0 < c.ε₁ := by
  rw [hc.hε₁_eq]; exact sq_pos_of_pos hc.hr_pos

lemma ValidCfg.hε₁_le_one {c : Cfg} (hc : ValidCfg c) : c.ε₁ ≤ 1 := by
  rw [hc.hε₁_eq]; nlinarith [hc.hr_pos, hc.hr_le_one]

lemma ValidCfg.hε₂_pos {c : Cfg} (hc : ValidCfg c) : 0 < c.ε₂ := by
  rw [hc.hε₂_eq]; linarith [hc.hε₁_pos]

lemma ValidCfg.hε₂_le_one {c : Cfg} (hc : ValidCfg c) : c.ε₂ ≤ 1 := by
  rw [hc.hε₂_eq]; linarith [hc.hε₁_le_one]

lemma ValidCfg.hL_pos {c : Cfg} (hc : ValidCfg c) : 0 < c.L := by
  unfold Cfg.L
  exact Real.log_pos (by exact_mod_cast (by have := hc.hn; omega : 1 < c.n))

/-- Deterministic consequences of `GoodFiber`, `GoodDeg`, `GoodCodeg`. -/
lemma fiber_le_Fmax {c : Cfg} (hc : ValidCfg c) {π₁ : Fin c.n → Fin c.m}
    (hf : GoodFiber c.n c.m (c.ε₂ / 3) π₁) (v : Fin c.m) :
    (fiber π₁ v).card ≤ c.Fmax := by
  have h1 := (abs_lt.mp (hf v)).2
  have h2 : ((fiber π₁ v).card : ℝ) ≤ (c.Fmax : ℝ) := by linarith [hc.hFmax_ge]
  exact_mod_cast h2

lemma deg_le_Dmax {c : Cfg} (hc : ValidCfg c) {g₁ : Pair c.m → Bool}
    (hd : GoodDeg c.m c.p (c.ε₂ / 3) g₁) (v : Fin c.m) :
    (nbrG g₁ v).card ≤ c.Dmax := by
  have h1 := (abs_lt.mp (hd v)).2
  have h2 : ((nbrG g₁ v).card : ℝ) ≤ (c.Dmax : ℝ) := by linarith [hc.hDmax_ge]
  exact_mod_cast h2

lemma nbrV_le_pn {c : Cfg} (hc : ValidCfg c) {π₁ : Fin c.n → Fin c.m} {g₁ : Pair c.m → Bool}
    (hf : GoodFiber c.n c.m (c.ε₂ / 3) π₁) (hd : GoodDeg c.m c.p (c.ε₂ / 3) g₁) (v : Fin c.m) :
    ((nbrV π₁ g₁ v).card : ℝ) ≤ (1 + c.ε₂) * (c.p * (c.n : ℝ)) := by
  rw [nbrV_card_eq_sum_fibers, Nat.cast_sum]
  have hmpos : (0 : ℝ) < (c.m : ℝ) := by exact_mod_cast (by have := hc.hm; omega : 0 < c.m)
  have hfib_le : ∀ u ∈ nbrG g₁ v, ((fiber π₁ u).card : ℝ) ≤ (1 + c.ε₂ / 3) * ((c.n : ℝ) / (c.m : ℝ)) := by
    intro u _; linarith [(abs_lt.mp (hf u)).2]
  have hdeg_le : ((nbrG g₁ v).card : ℝ) ≤ (1 + c.ε₂ / 3) * (((c.m - 1 : ℕ) : ℝ) * c.p) := by
    linarith [(abs_lt.mp (hd v)).2]
  have hm1_le : ((c.m - 1 : ℕ) : ℝ) ≤ (c.m : ℝ) := by exact_mod_cast Nat.sub_le c.m 1
  have hdiv_le : ((c.m - 1 : ℕ) : ℝ) / (c.m : ℝ) ≤ 1 := (div_le_one hmpos).mpr hm1_le
  have hε₂_sq : (1 + c.ε₂ / 3) ^ 2 ≤ 1 + c.ε₂ := by nlinarith [hc.hε₂_pos, hc.hε₂_le_one]
  have hpn0 : 0 ≤ c.p * (c.n : ℝ) := mul_nonneg hc.hp0 (Nat.cast_nonneg _)
  have hprod : ((1 + c.ε₂ / 3) * (((c.m - 1 : ℕ) : ℝ) * c.p)) * ((1 + c.ε₂ / 3) * ((c.n : ℝ) / (c.m : ℝ))) =
      (1 + c.ε₂ / 3) ^ 2 * ((((c.m - 1 : ℕ) : ℝ) / (c.m : ℝ)) * (c.p * (c.n : ℝ))) := by ring
  calc ∑ u ∈ nbrG g₁ v, ((fiber π₁ u).card : ℝ)
      ≤ ∑ _u ∈ nbrG g₁ v, ((1 + c.ε₂ / 3) * ((c.n : ℝ) / (c.m : ℝ))) := Finset.sum_le_sum hfib_le
    _ = ((nbrG g₁ v).card : ℝ) * ((1 + c.ε₂ / 3) * ((c.n : ℝ) / (c.m : ℝ))) := by simp
    _ ≤ ((1 + c.ε₂ / 3) * (((c.m - 1 : ℕ) : ℝ) * c.p)) * ((1 + c.ε₂ / 3) * ((c.n : ℝ) / (c.m : ℝ))) := by
        refine mul_le_mul_of_nonneg_right hdeg_le ?_
        have := hc.hε₂_pos; positivity
    _ = (1 + c.ε₂ / 3) ^ 2 * ((((c.m - 1 : ℕ) : ℝ) / (c.m : ℝ)) * (c.p * (c.n : ℝ))) := hprod
    _ ≤ (1 + c.ε₂ / 3) ^ 2 * (c.p * (c.n : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        nlinarith
    _ ≤ (1 + c.ε₂) * (c.p * (c.n : ℝ)) := by nlinarith

lemma nbrV_le_Nmax {c : Cfg} (hc : ValidCfg c) {π₁ : Fin c.n → Fin c.m} {g₁ : Pair c.m → Bool}
    (hf : GoodFiber c.n c.m (c.ε₂ / 3) π₁) (hd : GoodDeg c.m c.p (c.ε₂ / 3) g₁) (v : Fin c.m) :
    (nbrV π₁ g₁ v).card ≤ c.Nmax := by
  exact_mod_cast (nbrV_le_pn hc hf hd v).trans hc.hNmax_ge

lemma nbrV_inter_le_Smax {c : Cfg} (hc : ValidCfg c) {π₁ : Fin c.n → Fin c.m} {g₁ : Pair c.m → Bool}
    (hf : GoodFiber c.n c.m (c.ε₂ / 3) π₁) (hcd : GoodCodeg c.m c.t_codeg g₁)
    {v w : Fin c.m} (hvw : v ≠ w) :
    (nbrV π₁ g₁ v ∩ nbrV π₁ g₁ w).card ≤ c.Smax := by
  rw [nbrV_inter_card_eq_sum_fibers]
  calc ∑ u ∈ codegG g₁ v w, (fiber π₁ u).card
      ≤ ∑ _u ∈ codegG g₁ v w, c.Fmax := Finset.sum_le_sum fun u _ => fiber_le_Fmax hc hf u
    _ = (codegG g₁ v w).card * c.Fmax := by simp
    _ ≤ c.t_codeg * c.Fmax := Nat.mul_le_mul_right c.Fmax (hcd v w hvw).le

/-- Conditioned product probability helper. -/
lemma Pr_prodW_cond_le {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    {w₁ : Ω₁ → ℝ} {w₂ : Ω₂ → ℝ} (hw₁ : IsProb w₁)
    (P : Ω₁ → Prop) (Q : Ω₁ → Ω₂ → Prop) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ x : Ω₁, P x → Pr w₂ (fun y => Q x y) ≤ B) :
    Pr (prodW w₁ w₂) (fun xy => P xy.1 ∧ Q xy.1 xy.2) ≤ B := by
  rw [Pr_prodW]
  calc E w₁ (fun x => Pr w₂ (fun y => P x ∧ Q x y))
      ≤ E w₁ (fun _ => B) := by
        refine E_mono hw₁ fun x => ?_
        by_cases hx : P x
        · rw [Pr_congr (fun y => ⟨fun hy => hy.2, fun hy => ⟨hx, hy⟩⟩)]
          exact h x hx
        · rw [Pr_congr (B := fun _ => False) (fun y => ⟨fun hy => hx hy.1, False.elim⟩), Pr_false]
          exact hB
    _ = B := E_const hw₁ B

/-- High-probability regularity theorem: `Pr (fullW c.n c.m c.p) (¬ GoodR c) < 1 / 2`. -/
lemma Pr_not_goodR_lt_half {c : Cfg} (hc : ValidCfg c) :
    Pr (fullW c.n c.m c.p) (fun ω => ¬ GoodR c ω) < 1 / 2 := by
  have hmpos : 0 < c.m := by have := hc.hm; omega
  have hPpi1 : IsProb (unifW (Fin c.n) c.m) := isProb_unifW hmpos
  have hPpi : IsProb (piPairW c.n c.m) := isProb_piPairW hmpos
  have hPg1 : IsProb (bernW (Pair c.m) c.p) := isProb_bernW hc.hp0 hc.hp1
  have hPg : IsProb (gPairW c.m c.p) := isProb_gPairW hc.hp0 hc.hp1
  have hP : IsProb (fullW c.n c.m c.p) := isProb_fullW hmpos hc.hp0 hc.hp1
  have hδ0 : 0 ≤ c.ε₂ / 3 := by linarith [hc.hε₂_pos]
  have hδ1 : c.ε₂ / 3 ≤ 1 := by linarith [hc.hε₂_le_one]
  -- 1 & 2: Fiber bounds
  have hF1 : Pr (fullW c.n c.m c.p) (fun ω => ¬ GoodFiber c.n c.m (c.ε₂ / 3) ω.1.1) ≤ 1 / 40 := by
    rw [fullW, Pr_prodW_fst hPg (A := fun π : PiPair c.n c.m => ¬ GoodFiber c.n c.m (c.ε₂ / 3) π.1)]
    rw [piPairW, Pr_prodW_fst hPpi1 (A := fun π₁ : Fin c.n → Fin c.m => ¬ GoodFiber c.n c.m (c.ε₂ / 3) π₁)]
    exact (Pr_not_fiberGood hmpos hδ0 hδ1).trans hc.hPr_fiber
  have hF2 : Pr (fullW c.n c.m c.p) (fun ω => ¬ GoodFiber c.n c.m (c.ε₂ / 3) ω.1.2) ≤ 1 / 40 := by
    rw [fullW, Pr_prodW_fst hPg (A := fun π : PiPair c.n c.m => ¬ GoodFiber c.n c.m (c.ε₂ / 3) π.2)]
    rw [piPairW, Pr_prodW_snd hPpi1 (B := fun π₂ : Fin c.n → Fin c.m => ¬ GoodFiber c.n c.m (c.ε₂ / 3) π₂)]
    exact (Pr_not_fiberGood hmpos hδ0 hδ1).trans hc.hPr_fiber
  -- 3 & 4: Degree bounds
  have hD1 : Pr (fullW c.n c.m c.p) (fun ω => ¬ GoodDeg c.m c.p (c.ε₂ / 3) ω.2.1) ≤ 1 / 40 := by
    rw [fullW, Pr_prodW_snd hPpi (B := fun g : GPair c.m => ¬ GoodDeg c.m c.p (c.ε₂ / 3) g.1)]
    rw [gPairW, Pr_prodW_fst hPg1 (A := fun g₁ : Pair c.m → Bool => ¬ GoodDeg c.m c.p (c.ε₂ / 3) g₁)]
    exact (Pr_not_degGood hc.hp0 hc.hp1 hδ0 hδ1).trans hc.hPr_deg
  have hD2 : Pr (fullW c.n c.m c.p) (fun ω => ¬ GoodDeg c.m c.p (c.ε₂ / 3) ω.2.2) ≤ 1 / 40 := by
    rw [fullW, Pr_prodW_snd hPpi (B := fun g : GPair c.m => ¬ GoodDeg c.m c.p (c.ε₂ / 3) g.2)]
    rw [gPairW, Pr_prodW_snd hPg1 (B := fun g₂ : Pair c.m → Bool => ¬ GoodDeg c.m c.p (c.ε₂ / 3) g₂)]
    exact (Pr_not_degGood hc.hp0 hc.hp1 hδ0 hδ1).trans hc.hPr_deg
  -- 5 & 6: Co-degree bounds
  have hC1 : Pr (fullW c.n c.m c.p) (fun ω => ¬ GoodCodeg c.m c.t_codeg ω.2.1) ≤ 1 / 40 := by
    rw [fullW, Pr_prodW_snd hPpi (B := fun g : GPair c.m => ¬ GoodCodeg c.m c.t_codeg g.1)]
    rw [gPairW, Pr_prodW_fst hPg1 (A := fun g₁ : Pair c.m → Bool => ¬ GoodCodeg c.m c.t_codeg g₁)]
    exact (Pr_not_codegGood hc.ht_codeg1 hc.hp0 hc.hp1).trans hc.hPr_codeg
  have hC2 : Pr (fullW c.n c.m c.p) (fun ω => ¬ GoodCodeg c.m c.t_codeg ω.2.2) ≤ 1 / 40 := by
    rw [fullW, Pr_prodW_snd hPpi (B := fun g : GPair c.m => ¬ GoodCodeg c.m c.t_codeg g.2)]
    rw [gPairW, Pr_prodW_snd hPg1 (B := fun g₂ : Pair c.m → Bool => ¬ GoodCodeg c.m c.t_codeg g₂)]
    exact (Pr_not_codegGood hc.ht_codeg1 hc.hp0 hc.hp1).trans hc.hPr_codeg
  -- 7: Cross-color co-degree conditioned on `GoodDeg`
  have hCross : Pr (fullW c.n c.m c.p) (fun ω =>
      (GoodDeg c.m c.p (c.ε₂ / 3) ω.2.1 ∧ GoodDeg c.m c.p (c.ε₂ / 3) ω.2.2) ∧
      ¬ GoodCross c.n c.m c.t_cross ω.1 ω.2) ≤ 1 / 40 := by
    let eSwap : (GPair c.m × PiPair c.n c.m) ≃ Omega c.n c.m := Equiv.prodComm _ _
    rw [← Pr_equiv eSwap]
    have hwt : (fun x : GPair c.m × PiPair c.n c.m => fullW c.n c.m c.p (eSwap x)) =
        prodW (gPairW c.m c.p) (piPairW c.n c.m) := by
      funext ⟨g, π⟩; simp [fullW, prodW, eSwap, mul_comm]
    rw [hwt]
    refine Pr_prodW_cond_le hPg
      (fun g => GoodDeg c.m c.p (c.ε₂ / 3) g.1 ∧ GoodDeg c.m c.p (c.ε₂ / 3) g.2)
      (fun g π => ¬ GoodCross c.n c.m c.t_cross π g) (by norm_num) ?_
    intro g ⟨hd1, hd2⟩
    exact (Pr_not_crossGood hmpos hc.ht_cross1 g.1 g.2
      (deg_le_Dmax hc hd1) (deg_le_Dmax hc hd2)).trans hc.hPr_cross
  -- 8: Projected co-degree (Red -> Blue) conditioned on `GoodFiber π.1 ∧ GoodDeg g.1 ∧ GoodCodeg g.1`
  have hProj1 : Pr (fullW c.n c.m c.p) (fun ω =>
      (GoodFiber c.n c.m (c.ε₂ / 3) ω.1.1 ∧ GoodDeg c.m c.p (c.ε₂ / 3) ω.2.1 ∧ GoodCodeg c.m c.t_codeg ω.2.1) ∧
      ¬ GoodProj c.n c.m c.Smax c.t_proj ω.1.1 ω.1.2 ω.2.1) ≤ 1 / 40 := by
    let eR : (((Fin c.n → Fin c.m) × GPair c.m) × (Fin c.n → Fin c.m)) ≃ Omega c.n c.m :=
      { toFun := fun x => ((x.1.1, x.2), x.1.2)
        invFun := fun ω => ((ω.1.1, ω.2), ω.1.2)
        left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
        right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    rw [← Pr_equiv eR]
    have hwt : (fun x => fullW c.n c.m c.p (eR x)) =
        prodW (prodW (unifW (Fin c.n) c.m) (gPairW c.m c.p)) (unifW (Fin c.n) c.m) := by
      funext ⟨⟨π₁, g⟩, π₂⟩; simp [fullW, piPairW, prodW, eR]; ring
    rw [hwt]
    refine Pr_prodW_cond_le (isProb_prodW hPpi1 hPg)
      (fun x => GoodFiber c.n c.m (c.ε₂ / 3) x.1 ∧ GoodDeg c.m c.p (c.ε₂ / 3) x.2.1 ∧ GoodCodeg c.m c.t_codeg x.2.1)
      (fun x π₂ => ¬ GoodProj c.n c.m c.Smax c.t_proj x.1 π₂ x.2.1) (by norm_num) ?_
    intro ⟨π₁, g⟩ ⟨hf1, hd1, hcd1⟩
    exact (Pr_not_projCodegGood hmpos hc.ht_proj1 g.1 π₁
      (nbrV_le_Nmax hc hf1 hd1) (fun v w h => nbrV_inter_le_Smax hc hf1 hcd1 h)).trans hc.hPr_proj
  -- 9: Projected co-degree (Blue -> Red) conditioned on `GoodFiber π.2 ∧ GoodDeg g.2 ∧ GoodCodeg g.2`
  have hProj2 : Pr (fullW c.n c.m c.p) (fun ω =>
      (GoodFiber c.n c.m (c.ε₂ / 3) ω.1.2 ∧ GoodDeg c.m c.p (c.ε₂ / 3) ω.2.2 ∧ GoodCodeg c.m c.t_codeg ω.2.2) ∧
      ¬ GoodProj c.n c.m c.Smax c.t_proj ω.1.2 ω.1.1 ω.2.2) ≤ 1 / 40 := by
    let eB : (((Fin c.n → Fin c.m) × GPair c.m) × (Fin c.n → Fin c.m)) ≃ Omega c.n c.m :=
      { toFun := fun x => ((x.2, x.1.1), x.1.2)
        invFun := fun ω => ((ω.1.2, ω.2), ω.1.1)
        left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
        right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    rw [← Pr_equiv eB]
    have hwt : (fun x => fullW c.n c.m c.p (eB x)) =
        prodW (prodW (unifW (Fin c.n) c.m) (gPairW c.m c.p)) (unifW (Fin c.n) c.m) := by
      funext ⟨⟨π₂, g⟩, π₁⟩; simp [fullW, piPairW, prodW, eB]; ring
    rw [hwt]
    refine Pr_prodW_cond_le (isProb_prodW hPpi1 hPg)
      (fun x => GoodFiber c.n c.m (c.ε₂ / 3) x.1 ∧ GoodDeg c.m c.p (c.ε₂ / 3) x.2.2 ∧ GoodCodeg c.m c.t_codeg x.2.2)
      (fun x π₁ => ¬ GoodProj c.n c.m c.Smax c.t_proj x.1 π₁ x.2.2) (by norm_num) ?_
    intro ⟨π₂, g⟩ ⟨hf2, hd2, hcd2⟩
    exact (Pr_not_projCodegGood hmpos hc.ht_proj1 g.2 π₂
      (nbrV_le_Nmax hc hf2 hd2) (fun v w h => nbrV_inter_le_Smax hc hf2 hcd2 h)).trans hc.hPr_proj
  -- 10: Medium vertices conditioned on `GoodFiber π.1 ∧ GoodFiber π.2`
  have hMed : Pr (fullW c.n c.m c.p) (fun ω =>
      (GoodFiber c.n c.m (c.ε₂ / 3) ω.1.1 ∧ GoodFiber c.n c.m (c.ε₂ / 3) ω.1.2) ∧
      ¬ GoodMed c.n c.m c.k c.t₂ c.t₃ c.Ylim ω.1 ω.2) ≤ 1 / 40 := by
    rw [fullW]
    refine Pr_prodW_cond_le hPpi
      (fun π => GoodFiber c.n c.m (c.ε₂ / 3) π.1 ∧ GoodFiber c.n c.m (c.ε₂ / 3) π.2)
      (fun π g => ¬ GoodMed c.n c.m c.k c.t₂ c.t₃ c.Ylim π g) (by norm_num) ?_
    intro π ⟨hf1, hf2⟩
    have hcongr : Pr (gPairW c.m c.p) (fun g => ¬ GoodMed c.n c.m c.k c.t₂ c.t₃ c.Ylim π g) =
        Pr (gPairW c.m c.p) (fun g => ∃ I : Finset (Fin c.n), I.card = c.k ∧
          c.Ylim < ∑ v ∈ Mset π g I c.t₂ c.t₃, ((XAll π g I v).card : ℝ)) := by
      refine Pr_congr fun g => ?_
      simp [GoodMed]
    rw [hcongr]
    exact (Pr_not_medGood hc.hp0 hc.hp1 hc.ht₃0 hc.hMed_ht₂ hc.hMed_b₀_ge hc.hMed_b₀_le
      hc.ht_med1 hc.hMed_tmed_le π (fiber_le_Fmax hc hf1) (fiber_le_Fmax hc hf2)).trans hc.hPr_med
  -- 11: Small vertices conditioned on `GoodFiber π.1 ∧ GoodFiber π.2`
  have hSmall : Pr (fullW c.n c.m c.p) (fun ω =>
      (GoodFiber c.n c.m (c.ε₂ / 3) ω.1.1 ∧ GoodFiber c.n c.m (c.ε₂ / 3) ω.1.2) ∧
      ¬ GoodSmall c.n c.m c.k c.Fmax c.p c.t₃ c.t_small ω.1 ω.2) ≤ 1 / 40 := by
    rw [fullW]
    refine Pr_prodW_cond_le hPpi
      (fun π => GoodFiber c.n c.m (c.ε₂ / 3) π.1 ∧ GoodFiber c.n c.m (c.ε₂ / 3) π.2)
      (fun π g => ¬ GoodSmall c.n c.m c.k c.Fmax c.p c.t₃ c.t_small π g) (by norm_num) ?_
    intro π ⟨hf1, hf2⟩
    have hcongr : Pr (gPairW c.m c.p) (fun g => ¬ GoodSmall c.n c.m c.k c.Fmax c.p c.t₃ c.t_small π g) =
        Pr (gPairW c.m c.p) (fun g => ∃ I : Finset (Fin c.n), I.card = c.k ∧
          (c.k : ℝ) * c.t₃ ^ 2 + (c.k : ℝ) * (c.Fmax : ℝ) +
            (c.k.choose 2 : ℝ) * (2 * (c.m : ℝ) * c.p ^ 2) + c.t_small <
            (((Sset π g I c.t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ)) := by
      refine Pr_congr fun g => ?_
      simp [GoodSmall]
    rw [hcongr]
    exact (Pr_not_smallGood hmpos hc.hp0 hc.hp1 hc.ht₃0 hc.ht_small0 π
      (fiber_le_Fmax hc hf1) (fiber_le_Fmax hc hf2)).trans hc.hPr_small
  -- Combine all 11 events by union bound (`11 / 40 < 1 / 2`)!
  let E1 (ω : Omega c.n c.m) := ¬ GoodFiber c.n c.m (c.ε₂ / 3) ω.1.1
  let E2 (ω : Omega c.n c.m) := ¬ GoodFiber c.n c.m (c.ε₂ / 3) ω.1.2
  let E3 (ω : Omega c.n c.m) := ¬ GoodDeg c.m c.p (c.ε₂ / 3) ω.2.1
  let E4 (ω : Omega c.n c.m) := ¬ GoodDeg c.m c.p (c.ε₂ / 3) ω.2.2
  let E5 (ω : Omega c.n c.m) := ¬ GoodCodeg c.m c.t_codeg ω.2.1
  let E6 (ω : Omega c.n c.m) := ¬ GoodCodeg c.m c.t_codeg ω.2.2
  let E7 (ω : Omega c.n c.m) := (GoodDeg c.m c.p (c.ε₂ / 3) ω.2.1 ∧ GoodDeg c.m c.p (c.ε₂ / 3) ω.2.2) ∧
      ¬ GoodCross c.n c.m c.t_cross ω.1 ω.2
  let E8 (ω : Omega c.n c.m) := (GoodFiber c.n c.m (c.ε₂ / 3) ω.1.1 ∧ GoodDeg c.m c.p (c.ε₂ / 3) ω.2.1 ∧
      GoodCodeg c.m c.t_codeg ω.2.1) ∧ ¬ GoodProj c.n c.m c.Smax c.t_proj ω.1.1 ω.1.2 ω.2.1
  let E9 (ω : Omega c.n c.m) := (GoodFiber c.n c.m (c.ε₂ / 3) ω.1.2 ∧ GoodDeg c.m c.p (c.ε₂ / 3) ω.2.2 ∧
      GoodCodeg c.m c.t_codeg ω.2.2) ∧ ¬ GoodProj c.n c.m c.Smax c.t_proj ω.1.2 ω.1.1 ω.2.2
  let E10 (ω : Omega c.n c.m) := (GoodFiber c.n c.m (c.ε₂ / 3) ω.1.1 ∧ GoodFiber c.n c.m (c.ε₂ / 3) ω.1.2) ∧
      ¬ GoodMed c.n c.m c.k c.t₂ c.t₃ c.Ylim ω.1 ω.2
  let E11 (ω : Omega c.n c.m) := (GoodFiber c.n c.m (c.ε₂ / 3) ω.1.1 ∧ GoodFiber c.n c.m (c.ε₂ / 3) ω.1.2) ∧
      ¬ GoodSmall c.n c.m c.k c.Fmax c.p c.t₃ c.t_small ω.1 ω.2
  have himp : ∀ ω : Omega c.n c.m, ¬ GoodR c ω →
      E1 ω ∨ E2 ω ∨ E3 ω ∨ E4 ω ∨ E5 ω ∨ E6 ω ∨ E7 ω ∨ E8 ω ∨ E9 ω ∨ E10 ω ∨ E11 ω := by
    intro ω hnot
    by_contra hor
    apply hnot
    simp only [not_or, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, not_not] at hor
    rcases hor with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    have h7' : GoodCross c.n c.m c.t_cross ω.1 ω.2 := Classical.byContradiction fun h => h7 ⟨⟨h3, h4⟩, h⟩
    have h8' : GoodProj c.n c.m c.Smax c.t_proj ω.1.1 ω.1.2 ω.2.1 := Classical.byContradiction fun h => h8 ⟨⟨h1, h3, h5⟩, h⟩
    have h9' : GoodProj c.n c.m c.Smax c.t_proj ω.1.2 ω.1.1 ω.2.2 := Classical.byContradiction fun h => h9 ⟨⟨h2, h4, h6⟩, h⟩
    have h10' : GoodMed c.n c.m c.k c.t₂ c.t₃ c.Ylim ω.1 ω.2 := Classical.byContradiction fun h => h10 ⟨⟨h1, h2⟩, h⟩
    have h11' : GoodSmall c.n c.m c.k c.Fmax c.p c.t₃ c.t_small ω.1 ω.2 := Classical.byContradiction fun h => h11 ⟨⟨h1, h2⟩, h⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7', h8', h9', h10', h11'⟩
  have htot : Pr (fullW c.n c.m c.p) (fun ω => ¬ GoodR c ω) ≤
      Pr (fullW c.n c.m c.p) E1 + Pr (fullW c.n c.m c.p) E2 + Pr (fullW c.n c.m c.p) E3 +
      Pr (fullW c.n c.m c.p) E4 + Pr (fullW c.n c.m c.p) E5 + Pr (fullW c.n c.m c.p) E6 +
      Pr (fullW c.n c.m c.p) E7 + Pr (fullW c.n c.m c.p) E8 + Pr (fullW c.n c.m c.p) E9 +
      Pr (fullW c.n c.m c.p) E10 + Pr (fullW c.n c.m c.p) E11 := by
    have h0 := Pr_mono hP himp
    have ha1 := Pr_or_le hP E1 (fun ω => E2 ω ∨ E3 ω ∨ E4 ω ∨ E5 ω ∨ E6 ω ∨ E7 ω ∨ E8 ω ∨ E9 ω ∨ E10 ω ∨ E11 ω)
    have ha2 := Pr_or_le hP E2 (fun ω => E3 ω ∨ E4 ω ∨ E5 ω ∨ E6 ω ∨ E7 ω ∨ E8 ω ∨ E9 ω ∨ E10 ω ∨ E11 ω)
    have ha3 := Pr_or_le hP E3 (fun ω => E4 ω ∨ E5 ω ∨ E6 ω ∨ E7 ω ∨ E8 ω ∨ E9 ω ∨ E10 ω ∨ E11 ω)
    have ha4 := Pr_or_le hP E4 (fun ω => E5 ω ∨ E6 ω ∨ E7 ω ∨ E8 ω ∨ E9 ω ∨ E10 ω ∨ E11 ω)
    have ha5 := Pr_or_le hP E5 (fun ω => E6 ω ∨ E7 ω ∨ E8 ω ∨ E9 ω ∨ E10 ω ∨ E11 ω)
    have ha6 := Pr_or_le hP E6 (fun ω => E7 ω ∨ E8 ω ∨ E9 ω ∨ E10 ω ∨ E11 ω)
    have ha7 := Pr_or_le hP E7 (fun ω => E8 ω ∨ E9 ω ∨ E10 ω ∨ E11 ω)
    have ha8 := Pr_or_le hP E8 (fun ω => E9 ω ∨ E10 ω ∨ E11 ω)
    have ha9 := Pr_or_le hP E9 (fun ω => E10 ω ∨ E11 ω)
    have ha10 := Pr_or_le hP E10 E11
    linarith
  linarith only [htot, hF1, hF2, hD1, hD2, hC1, hC2, hCross, hProj1, hProj2, hMed, hSmall]

end ConfigAndGoodEvent

section GoodRImpliesRISI

/-- Fiber decomposition of `XV π₁ g₁ I v`. -/
lemma XV_card_eq_sum_inter_fibers {n m : ℕ} (π₁ : Fin n → Fin m) (g₁ : Pair m → Bool)
    (I : Finset (Fin n)) (v : Fin m) :
    (XV π₁ g₁ I v).card = ∑ u ∈ nbrG g₁ v, (I ∩ fiber π₁ u).card := by
  have hbi : XV π₁ g₁ I v = (nbrG g₁ v).biUnion (fun u => I ∩ fiber π₁ u) := by
    ext x
    simp only [XV, nbrG, fiber, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_inter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hxI, hadj⟩
      exact ⟨π₁ x, hadj, hxI, rfl⟩
    · rintro ⟨u, hadj, hxI, rfl⟩
      exact ⟨hxI, hadj⟩
  rw [hbi, Finset.card_biUnion]
  intro u₁ _ u₂ _ hne
  dsimp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  have h1 : π₁ x = u₁ := (Finset.mem_filter.mp (Finset.mem_inter.mp hx1).2).2
  have h2 : π₁ x = u₂ := (Finset.mem_filter.mp (Finset.mem_inter.mp hx2).2).2
  exact hne (h1.symm.trans h2)

/-- Counting pairs in `projPairs π₁ I ∩ (Q12one ∪ Q3one)` via an injective map into `(F1 ∪ F2) ×ˢ π₁(I)`. -/
lemma card_projPairs_inter_Q123_le {n m : ℕ} (π₁ : Fin n → Fin m) (g₁ : Pair m → Bool)
    (I : Finset (Fin n)) (Fthr Nthr : ℝ) :
    (projPairs π₁ I ∩ (Q12one π₁ I Fthr ∪ Q3one π₁ g₁ I Fthr Nthr)).card ≤
      ((F1set π₁ I Fthr).card + (F2set π₁ g₁ I Fthr Nthr).card) * (I.image π₁).card := by
  classical
  let F12 := F1set π₁ I Fthr ∪ F2set π₁ g₁ I Fthr Nthr
  let φ : Pair m → Fin m × Fin m := fun e =>
    if e.1.1 ∈ F12 then (e.1.1, e.1.2) else (e.1.2, e.1.1)
  have hcard : (projPairs π₁ I ∩ (Q12one π₁ I Fthr ∪ Q3one π₁ g₁ I Fthr Nthr)).card ≤
      (F12 ×ˢ I.image π₁).card := by
    refine Finset.card_le_card_of_injOn φ ?_ ?_
    · intro e he
      have h1 := (Finset.mem_filter.mp (Finset.mem_inter.mp he).1).2
      have h2 := (Finset.mem_inter.mp he).2
      have hor : e.1.1 ∈ F12 ∨ e.1.2 ∈ F12 := by
        rcases Finset.mem_union.mp h2 with hq12 | hq3
        · have hn := (Finset.mem_filter.mp hq12).2
          simp only [Finset.mem_sdiff, h1.1, h1.2, true_and, not_and, not_not] at hn
          by_cases ha : e.1.1 ∈ F1set π₁ I Fthr
          · exact Or.inl (Finset.mem_union_left _ ha)
          · exact Or.inr (Finset.mem_union_left _ (hn ha))
        · rcases (Finset.mem_filter.mp hq3).2 with ha | hb
          · exact Or.inl (Finset.mem_union_right _ ha)
          · exact Or.inr (Finset.mem_union_right _ hb)
      dsimp only [φ]
      split_ifs with ha
      · exact Finset.mem_product.mpr ⟨ha, h1.2⟩
      · exact Finset.mem_product.mpr ⟨hor.resolve_left ha, h1.1⟩
    · intro e₁ _ e₂ _ heq
      dsimp only [φ] at heq
      split_ifs at heq with h1 h2 h2
      · exact Subtype.ext heq
      · have hfst : e₁.1.1 = e₂.1.2 := congr_arg Prod.fst heq
        have hsnd : e₁.1.2 = e₂.1.1 := congr_arg Prod.snd heq
        have h1 := e₁.2; rw [hfst, hsnd] at h1
        exact absurd (lt_trans h1 e₂.2) (lt_irrefl _)
      · have hfst : e₁.1.2 = e₂.1.1 := congr_arg Prod.fst heq
        have hsnd : e₁.1.1 = e₂.1.2 := congr_arg Prod.snd heq
        have h1 := e₁.2; rw [hfst, hsnd] at h1
        exact absurd (lt_trans h1 e₂.2) (lt_irrefl _)
      · exact Subtype.ext (Prod.ext (congr_arg Prod.snd heq) (congr_arg Prod.fst heq))
  calc (projPairs π₁ I ∩ (Q12one π₁ I Fthr ∪ Q3one π₁ g₁ I Fthr Nthr)).card
      ≤ (F12 ×ˢ I.image π₁).card := hcard
    _ = F12.card * (I.image π₁).card := Finset.card_product _ _
    _ ≤ ((F1set π₁ I Fthr).card + (F2set π₁ g₁ I Fthr Nthr).card) * (I.image π₁).card :=
        Nat.mul_le_mul_right _ (Finset.card_union_le _ _)

/-- Perturbation bound for `gCap`: `(1 + ε₂)^2 * gCap M₀ (y + δ) ≤ gCap M₀ y + 2 * ε₁ * k^2`. -/
lemma gCap_excess_le {M₀ k ε₁ ε₂ y δ : ℝ}
    (hM₀ : 0 ≤ M₀) (hk0 : 0 ≤ k) (hε₁0 : 0 < ε₁) (hε₁1 : ε₁ ≤ 1)
    (hε₂_eq : ε₂ = ε₁ / 100) (hy0 : 0 ≤ y) (hyk : y ≤ k) (hδ0 : 0 ≤ δ) (hδk : δ ≤ (ε₁ / 4) * k) :
    (1 + ε₂) ^ 2 * gCap M₀ (y + δ) ≤ gCap M₀ y + 2 * ε₁ * k ^ 2 := by
  have hε₂0 : 0 < ε₂ := by rw [hε₂_eq]; linarith
  have hε₂1 : ε₂ ≤ 1 := by rw [hε₂_eq]; linarith
  have hadd : gCap M₀ (y + δ) ≤ gCap M₀ y + (y + δ) * δ := gCap_add_le hM₀ hy0 hδ0
  have hgy_le : gCap M₀ y ≤ k ^ 2 / 2 := by
    have h1 : gCap M₀ y ≤ y ^ 2 / 2 := gCap_le_half_sq hM₀
    nlinarith only [h1, hy0, hyk]
  have hgy0 : 0 ≤ gCap M₀ y := by unfold gCap; split_ifs <;> positivity
  have hrem : (y + δ) * δ ≤ (ε₁ / 2) * k ^ 2 := by
    have h1 : y * δ ≤ (ε₁ / 4) * k ^ 2 := by nlinarith only [hy0, hyk, hδ0, hδk]
    have h2 : δ ^ 2 ≤ (ε₁ / 4) * k ^ 2 := by
      have h3 : δ ≤ k := by nlinarith only [hk0, hε₁0, hε₁1, hδk]
      nlinarith only [hδ0, hδk, h3]
    nlinarith only [h1, h2]
  have hε₂_small : ε₂ ≤ 1 / 100 := by rw [hε₂_eq]; linarith only [hε₁1]
  have h12 : (1 + ε₂) ^ 2 ≤ 1 + 3 * ε₂ := by nlinarith only [hε₂0, hε₂1]
  have h12_2 : (1 + ε₂) ^ 2 ≤ 2 := by nlinarith only [hε₂0, hε₂_small]
  have h3ε₂ : 3 * ε₂ * (k ^ 2 / 2) ≤ ε₁ * k ^ 2 := by
    rw [hε₂_eq]; nlinarith only [sq_nonneg k, hε₁0]
  have hrem0 : 0 ≤ (y + δ) * δ := by positivity
  calc (1 + ε₂) ^ 2 * gCap M₀ (y + δ)
      ≤ (1 + ε₂) ^ 2 * (gCap M₀ y + (y + δ) * δ) := mul_le_mul_of_nonneg_left hadd (sq_nonneg _)
    _ = (1 + ε₂) ^ 2 * gCap M₀ y + (1 + ε₂) ^ 2 * ((y + δ) * δ) := by ring
    _ ≤ (1 + 3 * ε₂) * gCap M₀ y + 2 * ((ε₁ / 2) * k ^ 2) := by
        nlinarith only [h12, h12_2, hgy0, hrem, hrem0]
    _ ≤ gCap M₀ y + 3 * ε₂ * (k ^ 2 / 2) + ε₁ * k ^ 2 := by nlinarith only [hε₂0, hgy_le]
    _ ≤ gCap M₀ y + 2 * ε₁ * k ^ 2 := by linarith only [h3ε₂]

/-- Deterministic bridge: under `ValidCfg c` and `GoodR c (π, g)`, all 3 hypotheses of
`lem_RISI_fixed_pi` hold for `I` of size `c.k` with `M₁ = c.M₁` and
`Z_min = ⌊c.fVal |π.1(I)| |π.2(I)| - 16 * c.ε₁ * c.k^2⌋₊`. -/
lemma goodR_imp_RISI_hyps {c : Cfg} (hc : ValidCfg c)
    (π : PiPair c.n c.m) (g : GPair c.m) (hG : GoodR c (π, g))
    (I : Finset (Fin c.n)) (hI : I.card = c.k) :
    (((I.image π.2) \ (F1set π.2 I c.Fthr ∪ F2set π.2 g.2 I c.Fthr c.Nthr)).biUnion
      (fun b => projPairs π.1 (XV π.2 g.2 I b))).card ≤ c.M₁ ∧
    (((I.image π.1) \ (F1set π.1 I c.Fthr ∪ F2set π.1 g.1 I c.Fthr c.Nthr)).biUnion
      (fun r => projPairs π.2 (XV π.1 g.1 I r))).card ≤ c.M₁ ∧
    ⌊c.fVal (I.image π.1).card (I.image π.2).card - 16 * c.ε₁ * (c.k : ℝ) ^ 2⌋₊ ≤
      ((projPairs π.1 I \ (Finset.univ.biUnion (fun v : Fin c.m ⊕ Fin c.m => projPairs π.1 (XAll π g I v)))) \
        (Q12one π.1 I c.Fthr ∪ Q3one π.1 g.1 I c.Fthr c.Nthr)).card +
      ((projPairs π.2 I \ (Finset.univ.biUnion (fun v : Fin c.m ⊕ Fin c.m => projPairs π.2 (XAll π g I v)))) \
        (Q12one π.2 I c.Fthr ∪ Q3one π.2 g.2 I c.Fthr c.Nthr)).card := by
  classical
  obtain ⟨hf1, hf2, hd1, hd2, hcd1, hcd2, hcross, hproj1, hproj2, hmed, hsmall⟩ := hG
  have hFR : ∀ r, (fiber π.1 r).card ≤ c.Fmax := fiber_le_Fmax hc hf1
  have hFB : ∀ b, (fiber π.2 b).card ≤ c.Fmax := fiber_le_Fmax hc hf2
  have hDR : ∀ r, (nbrG g.1 r).card ≤ c.Dmax := deg_le_Dmax hc hd1
  have hDB : ∀ b, (nbrG g.2 b).card ≤ c.Dmax := deg_le_Dmax hc hd2
  have hNV_R : ∀ r, ((nbrV π.1 g.1 r).card : ℝ) ≤ (1 + c.ε₂) * (c.p * (c.n : ℝ)) := nbrV_le_pn hc hf1 hd1
  have hNV_B : ∀ b, ((nbrV π.2 g.2 b).card : ℝ) ≤ (1 + c.ε₂) * (c.p * (c.n : ℝ)) := nbrV_le_pn hc hf2 hd2
  have hinter : ∀ u v : Fin c.m ⊕ Fin c.m, u ≠ v → (nbrAll π g u ∩ nbrAll π g v).card ≤ c.C_int := by
    intro u v huv
    cases u with
    | inl r₁ =>
      cases v with
      | inl r₂ =>
        have hne : r₁ ≠ r₂ := fun h => huv (congr_arg Sum.inl h)
        exact (nbrV_inter_le_Smax hc hf1 hcd1 hne).trans (le_max_left _ _)
      | inr b₂ =>
        exact (hcross r₁ b₂).le.trans (le_max_right _ _)
    | inr b₁ =>
      cases v with
      | inl r₂ =>
        rw [Finset.inter_comm]
        exact (hcross r₂ b₁).le.trans (le_max_right _ _)
      | inr b₂ =>
        have hne : b₁ ≠ b₂ := fun h => huv (congr_arg Sum.inr h)
        exact (nbrV_inter_le_Smax hc hf2 hcd2 hne).trans (le_max_left _ _)
  have hprojB : ∀ r₁ r₂ : Fin c.m, r₁ ≠ r₂ → (projNbr π.1 π.2 g.1 r₁ ∩ projNbr π.1 π.2 g.1 r₂).card ≤ c.C_proj :=
    fun r₁ r₂ h => (hproj1 r₁ r₂ h).le
  have hprojR : ∀ b₁ b₂ : Fin c.m, b₁ ≠ b₂ → (projNbr π.2 π.1 g.2 b₁ ∩ projNbr π.2 π.1 g.2 b₂).card ≤ c.C_proj :=
    fun b₁ b₂ h => (hproj2 b₁ b₂ h).le
  -- Apply Lemma 3.2 (`lem_large_bound`) and Lemma 3.5 (`lem_huge_bound`)!
  obtain ⟨hL_lt, hL_pairs⟩ := lem_large_bound hc.ht₁0 π g I hI hinter hc.hLcap
  have hM₀_nn : 0 ≤ c.p * (c.n : ℝ) := mul_nonneg hc.hp0 (Nat.cast_nonneg _)
  have hHuge := lem_huge_bound hM₀_nn hc.hε₂_pos.le π g I hI hinter hDR hDB hNV_R hNV_B hprojB hprojR hc.hHcap
  set HR : Finset (Fin c.m) := Finset.univ.filter (fun r => Sum.inl r ∈ Hset π g I c.t₁)
  set HB : Finset (Fin c.m) := Finset.univ.filter (fun b => Sum.inr b ∈ Hset π g I c.t₁)
  obtain ⟨hH_lt, hHR_same, hHB_same, hHR_cross, hHB_cross⟩ := hHuge
  -- Combined `Lset ∪ Mset ∪ Sset` pairsOf bound `≤ 3 * c.ε₁ * c.k^2`!
  set LMS : Finset (Fin c.m ⊕ Fin c.m) :=
    Lset π g I c.t₁ c.t₂ ∪ Mset π g I c.t₂ c.t₃ ∪ Sset π g I c.t₃
  have hM_pairs : (((Mset π g I c.t₂ c.t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ) ≤
      c.ε₁ * (c.k : ℝ) ^ 2 := by
    calc (((Mset π g I c.t₂ c.t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ)
        ≤ ∑ v ∈ Mset π g I c.t₂ c.t₃, ((pairsOf (XAll π g I v)).card : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
      _ = ∑ v ∈ Mset π g I c.t₂ c.t₃, (((XAll π g I v).card.choose 2 : ℕ) : ℝ) := by
            refine Finset.sum_congr rfl fun v _ => by rw [pairsOf_card]
      _ ≤ ∑ v ∈ Mset π g I c.t₂ c.t₃, (((XAll π g I v).card : ℝ) * c.t₂ / 2) := by
            refine Finset.sum_le_sum fun v hv =>
              choose_two_le_half_mul_bound (Finset.mem_filter.mp hv).2.2
      _ = (c.t₂ / 2) * ∑ v ∈ Mset π g I c.t₂ c.t₃, ((XAll π g I v).card : ℝ) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun v _ => by ring
      _ ≤ (c.t₂ / 2) * c.Ylim := mul_le_mul_of_nonneg_left (hmed I hI) (by linarith [hc.ht₂0])
      _ ≤ c.ε₁ * (c.k : ℝ) ^ 2 := hc.hM_loss
  have hS_pairs : (((Sset π g I c.t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ) ≤
      c.ε₁ * (c.k : ℝ) ^ 2 := (hsmall I hI).trans hc.hS_loss
  have hLMS_pairs : ((LMS.biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ) ≤ 3 * c.ε₁ * (c.k : ℝ) ^ 2 := by
    have hcard : (LMS.biUnion (fun v => pairsOf (XAll π g I v))).card ≤
        ((Lset π g I c.t₁ c.t₂).biUnion (fun v => pairsOf (XAll π g I v))).card +
        ((Mset π g I c.t₂ c.t₃).biUnion (fun v => pairsOf (XAll π g I v))).card +
        ((Sset π g I c.t₃).biUnion (fun v => pairsOf (XAll π g I v))).card := by
      dsimp only [LMS]
      rw [Finset.union_biUnion, Finset.union_biUnion]
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    have hcardR : ((LMS.biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ) ≤
        (((Lset π g I c.t₁ c.t₂).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ) +
        (((Mset π g I c.t₂ c.t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ) +
        (((Sset π g I c.t₃).biUnion (fun v => pairsOf (XAll π g I v))).card : ℝ) := by
      exact_mod_cast hcard
    linarith [hL_pairs.trans hc.hL_loss]
  -- Helper for one color: `|F1| ≤ k / Fthr`, `|F2| ≤ L_cap + H_cap`, and `v ∉ F1 ∪ F2 → |XV v| ≤ t₁`!
  have hF12_props : ∀ (π₁ : Fin c.n → Fin c.m) (g₁ : Pair c.m → Bool),
      (∀ u, (fiber π₁ u).card ≤ c.Fmax) → (∀ u, (nbrG g₁ u).card ≤ c.Dmax) →
      ((F1set π₁ I c.Fthr).card : ℝ) ≤ (c.k : ℝ) / c.Fthr ∧
      (∀ v ∈ F2set π₁ g₁ I c.Fthr c.Nthr, c.t₂ < ((XV π₁ g₁ I v).card : ℝ)) ∧
      (∀ v ∈ (I.image π₁) \ (F1set π₁ I c.Fthr ∪ F2set π₁ g₁ I c.Fthr c.Nthr),
        ((XV π₁ g₁ I v).card : ℝ) ≤ c.t₁) := by
    intro π₁ g₁ hF hD
    refine ⟨?_, ?_, ?_⟩
    · -- `|F1| * Fthr ≤ ∑_{u ∈ F1} |I ∩ fiber u| ≤ |I| = k`
      have hdisj : ((F1set π₁ I c.Fthr).biUnion (fun u => I ∩ fiber π₁ u)).card =
          ∑ u ∈ F1set π₁ I c.Fthr, (I ∩ fiber π₁ u).card := by
        rw [Finset.card_biUnion]
        intro u₁ _ u₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro x h1 h2
        have e1 : π₁ x = u₁ := (Finset.mem_filter.mp (Finset.mem_inter.mp h1).2).2
        have e2 : π₁ x = u₂ := (Finset.mem_filter.mp (Finset.mem_inter.mp h2).2).2
        exact hne (e1.symm.trans e2)
      have hsubI : (F1set π₁ I c.Fthr).biUnion (fun u => I ∩ fiber π₁ u) ⊆ I := by
        intro x hx
        obtain ⟨_, _, hxu⟩ := Finset.mem_biUnion.mp hx
        exact (Finset.mem_inter.mp hxu).1
      have hsum_le : (∑ u ∈ F1set π₁ I c.Fthr, ((I ∩ fiber π₁ u).card : ℝ)) ≤ (c.k : ℝ) := by
        have hnat : (∑ u ∈ F1set π₁ I c.Fthr, (I ∩ fiber π₁ u).card) ≤ c.k := by
          rw [← hdisj, ← hI]; exact Finset.card_le_card hsubI
        exact_mod_cast hnat
      have hsum_ge : ((F1set π₁ I c.Fthr).card : ℝ) * c.Fthr ≤
          ∑ u ∈ F1set π₁ I c.Fthr, ((I ∩ fiber π₁ u).card : ℝ) := by
        calc ((F1set π₁ I c.Fthr).card : ℝ) * c.Fthr = ∑ _u ∈ F1set π₁ I c.Fthr, c.Fthr := by simp
          _ ≤ ∑ u ∈ F1set π₁ I c.Fthr, ((I ∩ fiber π₁ u).card : ℝ) :=
              Finset.sum_le_sum fun u hu => ((Finset.mem_filter.mp hu).2).le
      exact (le_div_iff₀ hc.hFthr0).mpr (hsum_ge.trans hsum_le)
    · -- `v ∈ F2set → t₂ < |XV v|`
      intro v hv
      have hNgt : c.Nthr < ((nbrG g₁ v ∩ F1set π₁ I c.Fthr).card : ℝ) := (Finset.mem_filter.mp hv).2
      rw [XV_card_eq_sum_inter_fibers, Nat.cast_sum]
      have hge1 : ∑ u ∈ nbrG g₁ v ∩ F1set π₁ I c.Fthr, ((I ∩ fiber π₁ u).card : ℝ) ≤
          ∑ u ∈ nbrG g₁ v, ((I ∩ fiber π₁ u).card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (fun _ _ _ => Nat.cast_nonneg _)
      have hge2 : ((nbrG g₁ v ∩ F1set π₁ I c.Fthr).card : ℝ) * c.Fthr ≤
          ∑ u ∈ nbrG g₁ v ∩ F1set π₁ I c.Fthr, ((I ∩ fiber π₁ u).card : ℝ) := by
        calc ((nbrG g₁ v ∩ F1set π₁ I c.Fthr).card : ℝ) * c.Fthr
            = ∑ _u ∈ nbrG g₁ v ∩ F1set π₁ I c.Fthr, c.Fthr := by simp
          _ ≤ ∑ u ∈ nbrG g₁ v ∩ F1set π₁ I c.Fthr, ((I ∩ fiber π₁ u).card : ℝ) :=
              Finset.sum_le_sum fun u hu => ((Finset.mem_filter.mp (Finset.mem_inter.mp hu).2).2).le
      have hprod : c.t₂ = c.Nthr * c.Fthr := by rw [hc.hNthr_eq]; field_simp [hc.hFthr0.ne']
      have hlt : c.Nthr * c.Fthr < ((nbrG g₁ v ∩ F1set π₁ I c.Fthr).card : ℝ) * c.Fthr :=
        mul_lt_mul_of_pos_right hNgt hc.hFthr0
      linarith
    · -- `v ∈ I.image π₁ \ (F1 ∪ F2) → |XV v| ≤ t₁`
      intro v hv
      have hvI : v ∈ I.image π₁ := (Finset.mem_sdiff.mp hv).1
      have hvnot1 : v ∉ F1set π₁ I c.Fthr := fun h => (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_left _ h)
      have hvnot2 : v ∉ F2set π₁ g₁ I c.Fthr c.Nthr := fun h => (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_right _ h)
      have hNle : ((nbrG g₁ v ∩ F1set π₁ I c.Fthr).card : ℝ) ≤ c.Nthr := by
        by_contra hgt
        push Not at hgt
        exact hvnot2 (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hvI, hvnot1⟩, hgt⟩)
      rw [XV_card_eq_sum_inter_fibers, Nat.cast_sum]
      have hpart : nbrG g₁ v = (nbrG g₁ v ∩ F1set π₁ I c.Fthr) ∪ (nbrG g₁ v \ F1set π₁ I c.Fthr) := by
        ext u; simp [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
      have hdisj : Disjoint (nbrG g₁ v ∩ F1set π₁ I c.Fthr) (nbrG g₁ v \ F1set π₁ I c.Fthr) := by
        rw [Finset.disjoint_left]; intro u h1 h2
        exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).2
      rw [hpart, Finset.sum_union hdisj]
      have hsumA : ∑ u ∈ nbrG g₁ v ∩ F1set π₁ I c.Fthr, ((I ∩ fiber π₁ u).card : ℝ) ≤ c.Nthr * (c.Fmax : ℝ) := by
        calc ∑ u ∈ nbrG g₁ v ∩ F1set π₁ I c.Fthr, ((I ∩ fiber π₁ u).card : ℝ)
            ≤ ∑ _u ∈ nbrG g₁ v ∩ F1set π₁ I c.Fthr, (c.Fmax : ℝ) := by
                refine Finset.sum_le_sum fun u _ => ?_
                exact_mod_cast (Finset.card_le_card Finset.inter_subset_right).trans (hF u)
          _ = ((nbrG g₁ v ∩ F1set π₁ I c.Fthr).card : ℝ) * (c.Fmax : ℝ) := by simp
          _ ≤ c.Nthr * (c.Fmax : ℝ) := mul_le_mul_of_nonneg_right hNle (Nat.cast_nonneg _)
      have hsumB : ∑ u ∈ nbrG g₁ v \ F1set π₁ I c.Fthr, ((I ∩ fiber π₁ u).card : ℝ) ≤ (c.Dmax : ℝ) * c.Fthr := by
        have hpt : ∀ u ∈ nbrG g₁ v \ F1set π₁ I c.Fthr, ((I ∩ fiber π₁ u).card : ℝ) ≤ c.Fthr := by
          intro u hu
          have hunot : u ∉ F1set π₁ I c.Fthr := (Finset.mem_sdiff.mp hu).2
          by_cases huI : u ∈ I.image π₁
          · by_contra hgt; push Not at hgt
            exact hunot (Finset.mem_filter.mpr ⟨huI, hgt⟩)
          · have hemp : I ∩ fiber π₁ u = ∅ := by
              rw [Finset.eq_empty_iff_forall_notMem]
              intro x hx
              have hxI := (Finset.mem_inter.mp hx).1
              have hπx := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).2).2
              exact huI (hπx ▸ Finset.mem_image_of_mem π₁ hxI)
            rw [hemp]; simp [hc.hFthr0.le]
        calc ∑ u ∈ nbrG g₁ v \ F1set π₁ I c.Fthr, ((I ∩ fiber π₁ u).card : ℝ)
            ≤ ∑ _u ∈ nbrG g₁ v \ F1set π₁ I c.Fthr, c.Fthr := Finset.sum_le_sum hpt
          _ = ((nbrG g₁ v \ F1set π₁ I c.Fthr).card : ℝ) * c.Fthr := by simp
          _ ≤ (c.Dmax : ℝ) * c.Fthr := by
              refine mul_le_mul_of_nonneg_right ?_ hc.hFthr0.le
              exact_mod_cast (Finset.card_le_card Finset.sdiff_subset).trans (hD v)
      linarith [hc.hF2_sep]
  obtain ⟨hF1R_le, hF2R_gt, hKeepR_le⟩ := hF12_props π.1 g.1 hFR hDR
  obtain ⟨hF1B_le, hF2B_gt, hKeepB_le⟩ := hF12_props π.2 g.2 hFB hDB
  -- Bound `|F2R|` and `|F2B|` by `c.L_cap + c.H_cap`!
  have hF2R_card : (F2set π.1 g.1 I c.Fthr c.Nthr).card ≤ c.L_cap + c.H_cap := by
    have h1 : (F2set π.1 g.1 I c.Fthr c.Nthr).card ≤ (Lset π g I c.t₁ c.t₂ ∪ Hset π g I c.t₁).card := by
      refine Finset.card_le_card_of_injOn Sum.inl ?_ (fun _ _ _ _ h => Sum.inl.inj h)
      intro r hr
      have hgt : c.t₂ < ((XAll π g I (Sum.inl r)).card : ℝ) := by rw [XAll_inl]; exact hF2R_gt r hr
      by_cases h1 : c.t₁ < ((XAll π g I (Sum.inl r)).card : ℝ)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
      · push Not at h1
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt, h1⟩)
    exact (h1.trans (Finset.card_union_le _ _)).trans (Nat.add_le_add hL_lt.le hH_lt.le)
  have hF2B_card : (F2set π.2 g.2 I c.Fthr c.Nthr).card ≤ c.L_cap + c.H_cap := by
    have h1 : (F2set π.2 g.2 I c.Fthr c.Nthr).card ≤ (Lset π g I c.t₁ c.t₂ ∪ Hset π g I c.t₁).card := by
      refine Finset.card_le_card_of_injOn Sum.inr ?_ (fun _ _ _ _ h => Sum.inr.inj h)
      intro b hb
      have hgt : c.t₂ < ((XAll π g I (Sum.inr b)).card : ℝ) := by rw [XAll_inr]; exact hF2B_gt b hb
      by_cases h1 : c.t₁ < ((XAll π g I (Sum.inr b)).card : ℝ)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
      · push Not at h1
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt, h1⟩)
    exact (h1.trans (Finset.card_union_le _ _)).trans (Nat.add_le_add hL_lt.le hH_lt.le)
  -- Goal 1 (`hReg_C1`) & Goal 2 (`hReg_C2`):
  have hC1 : (((I.image π.2) \ (F1set π.2 I c.Fthr ∪ F2set π.2 g.2 I c.Fthr c.Nthr)).biUnion
      (fun b => projPairs π.1 (XV π.2 g.2 I b))).card ≤ c.M₁ := by
    have hsub : ((I.image π.2) \ (F1set π.2 I c.Fthr ∪ F2set π.2 g.2 I c.Fthr c.Nthr)).biUnion
        (fun b => projPairs π.1 (XV π.2 g.2 I b)) ⊆ LMS.biUnion (fun v => projPairs π.1 (XAll π g I v)) := by
      intro e he
      obtain ⟨b, hb, heb⟩ := Finset.mem_biUnion.mp he
      have hb_notH : Sum.inr b ∉ Hset π g I c.t₁ := by
        simp only [Hset, Finset.mem_filter, Finset.mem_univ, true_and, not_lt, XAll_inr]
        exact hKeepB_le b hb
      have hb_LMS : Sum.inr b ∈ LMS := by
        rcases mem_LMS_of_not_mem_H π g I c.t₁ c.t₂ c.t₃ (Sum.inr b) hb_notH with hL | hM | hS
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hL)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hM)
        · exact Finset.mem_union_right _ hS
      exact Finset.mem_biUnion.mpr ⟨Sum.inr b, hb_LMS, by rw [XAll_inr]; exact heb⟩
    have hleR : ((((I.image π.2) \ (F1set π.2 I c.Fthr ∪ F2set π.2 g.2 I c.Fthr c.Nthr)).biUnion
        (fun b => projPairs π.1 (XV π.2 g.2 I b))).card : ℝ) ≤ 3 * c.ε₁ * (c.k : ℝ) ^ 2 := by
      have h1 : (((I.image π.2) \ (F1set π.2 I c.Fthr ∪ F2set π.2 g.2 I c.Fthr c.Nthr)).biUnion
          (fun b => projPairs π.1 (XV π.2 g.2 I b))).card ≤
          (LMS.biUnion (fun v => pairsOf (XAll π g I v))).card :=
        (Finset.card_le_card hsub).trans (card_biUnion_projPairs_le_pairsOf π.1 LMS (XAll π g I))
      exact (Nat.cast_le.mpr h1).trans hLMS_pairs
    rw [hc.hM₁_eq]
    exact Nat.le_floor hleR
  have hC2 : (((I.image π.1) \ (F1set π.1 I c.Fthr ∪ F2set π.1 g.1 I c.Fthr c.Nthr)).biUnion
      (fun r => projPairs π.2 (XV π.1 g.1 I r))).card ≤ c.M₁ := by
    have hsub : ((I.image π.1) \ (F1set π.1 I c.Fthr ∪ F2set π.1 g.1 I c.Fthr c.Nthr)).biUnion
        (fun r => projPairs π.2 (XV π.1 g.1 I r)) ⊆ LMS.biUnion (fun v => projPairs π.2 (XAll π g I v)) := by
      intro e he
      obtain ⟨r, hr, her⟩ := Finset.mem_biUnion.mp he
      have hr_notH : Sum.inl r ∉ Hset π g I c.t₁ := by
        simp only [Hset, Finset.mem_filter, Finset.mem_univ, true_and, not_lt, XAll_inl]
        exact hKeepR_le r hr
      have hr_LMS : Sum.inl r ∈ LMS := by
        rcases mem_LMS_of_not_mem_H π g I c.t₁ c.t₂ c.t₃ (Sum.inl r) hr_notH with hL | hM | hS
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hL)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hM)
        · exact Finset.mem_union_right _ hS
      exact Finset.mem_biUnion.mpr ⟨Sum.inl r, hr_LMS, by rw [XAll_inl]; exact her⟩
    have hleR : ((((I.image π.1) \ (F1set π.1 I c.Fthr ∪ F2set π.1 g.1 I c.Fthr c.Nthr)).biUnion
        (fun r => projPairs π.2 (XV π.1 g.1 I r))).card : ℝ) ≤ 3 * c.ε₁ * (c.k : ℝ) ^ 2 := by
      have h1 : (((I.image π.1) \ (F1set π.1 I c.Fthr ∪ F2set π.1 g.1 I c.Fthr c.Nthr)).biUnion
          (fun r => projPairs π.2 (XV π.1 g.1 I r))).card ≤
          (LMS.biUnion (fun v => pairsOf (XAll π g I v))).card :=
        (Finset.card_le_card hsub).trans (card_biUnion_projPairs_le_pairsOf π.2 LMS (XAll π g I))
      exact (Nat.cast_le.mpr h1).trans hLMS_pairs
    rw [hc.hM₁_eq]
    exact Nat.le_floor hleR
  -- Helper: `(1 + c.ε₂)^2 * gCap (p*n) (y + δ) ≤ gCap (p*n) y + 2 * c.ε₁ * k^2` via `gCap_excess_le`!
  have hgCap_excess : ∀ (y δ : ℝ), 0 ≤ y → y ≤ (c.k : ℝ) → 0 ≤ δ → δ ≤ (c.ε₁ / 4) * (c.k : ℝ) →
      (1 + c.ε₂) ^ 2 * gCap (c.p * (c.n : ℝ)) (y + δ) ≤
        gCap (c.p * (c.n : ℝ)) y + 2 * c.ε₁ * (c.k : ℝ) ^ 2 :=
    fun _ _ hy0 hyk hδ0 hδk =>
      gCap_excess_le hM₀_nn (Nat.cast_nonneg _) hc.hε₁_pos hc.hε₁_le_one hc.hε₂_eq hy0 hyk hδ0 hδk
  -- Lower bound on red open unrevealed pairs:
  have hOpenR : ((I.image π.1).card : ℝ) ^ 2 / 2 -
      gCap (c.p * (c.n : ℝ)) ((c.k - (I.image π.2).card : ℕ) : ℝ) - 8 * c.ε₁ * (c.k : ℝ) ^ 2 ≤
      (((projPairs π.1 I \ (Finset.univ.biUnion (fun v : Fin c.m ⊕ Fin c.m => projPairs π.1 (XAll π g I v)))) \
        (Q12one π.1 I c.Fthr ∪ Q3one π.1 g.1 I c.Fthr c.Nthr)).card : ℝ) := by
    let O := (projPairs π.1 I \ (Finset.univ.biUnion (fun v : Fin c.m ⊕ Fin c.m => projPairs π.1 (XAll π g I v)))) \
        (Q12one π.1 I c.Fthr ∪ Q3one π.1 g.1 I c.Fthr c.Nthr)
    have hcov : projPairs π.1 I ⊆
        O ∪ LMS.biUnion (fun v => projPairs π.1 (XAll π g I v)) ∪
        HR.biUnion (fun r => projPairs π.1 (XV π.1 g.1 I r)) ∪
        HB.biUnion (fun b => projPairs π.1 (XV π.2 g.2 I b)) ∪
        (projPairs π.1 I ∩ (Q12one π.1 I c.Fthr ∪ Q3one π.1 g.1 I c.Fthr c.Nthr)) := by
      intro e he
      by_cases hq : e ∈ Q12one π.1 I c.Fthr ∪ Q3one π.1 g.1 I c.Fthr c.Nthr
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨he, hq⟩)
      · refine Finset.mem_union_left _ ?_
        by_cases hcl : e ∈ Finset.univ.biUnion (fun v : Fin c.m ⊕ Fin c.m => projPairs π.1 (XAll π g I v))
        · obtain ⟨v, _, hev⟩ := Finset.mem_biUnion.mp hcl
          by_cases hvH : v ∈ Hset π g I c.t₁
          · cases v with
            | inl r =>
              refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
              refine Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvH⟩, ?_⟩
              rwa [XAll_inl] at hev
            | inr b =>
              refine Finset.mem_union_right _ ?_
              refine Finset.mem_biUnion.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvH⟩, ?_⟩
              rwa [XAll_inr] at hev
          · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
            have hvLMS : v ∈ LMS := by
              rcases mem_LMS_of_not_mem_H π g I c.t₁ c.t₂ c.t₃ v hvH with hL | hM | hS
              · exact Finset.mem_union_left _ (Finset.mem_union_left _ hL)
              · exact Finset.mem_union_left _ (Finset.mem_union_right _ hM)
              · exact Finset.mem_union_right _ hS
            exact Finset.mem_biUnion.mpr ⟨v, hvLMS, hev⟩
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨he, hcl⟩, hq⟩)))
    have hcard_cov : (projPairs π.1 I).card ≤
        O.card + (LMS.biUnion (fun v => projPairs π.1 (XAll π g I v))).card +
        (HR.biUnion (fun r => projPairs π.1 (XV π.1 g.1 I r))).card +
        (HB.biUnion (fun b => projPairs π.1 (XV π.2 g.2 I b))).card +
        (projPairs π.1 I ∩ (Q12one π.1 I c.Fthr ∪ Q3one π.1 g.1 I c.Fthr c.Nthr)).card := by
      have h1 := Finset.card_le_card hcov
      have h2 := Finset.card_union_le
        (O ∪ LMS.biUnion (fun v => projPairs π.1 (XAll π g I v)) ∪
          HR.biUnion (fun r => projPairs π.1 (XV π.1 g.1 I r)) ∪
          HB.biUnion (fun b => projPairs π.1 (XV π.2 g.2 I b)))
        (projPairs π.1 I ∩ (Q12one π.1 I c.Fthr ∪ Q3one π.1 g.1 I c.Fthr c.Nthr))
      have h3 := Finset.card_union_le
        (O ∪ LMS.biUnion (fun v => projPairs π.1 (XAll π g I v)) ∪
          HR.biUnion (fun r => projPairs π.1 (XV π.1 g.1 I r)))
        (HB.biUnion (fun b => projPairs π.1 (XV π.2 g.2 I b)))
      have h4 := Finset.card_union_le
        (O ∪ LMS.biUnion (fun v => projPairs π.1 (XAll π g I v)))
        (HR.biUnion (fun r => projPairs π.1 (XV π.1 g.1 I r)))
      have h5 := Finset.card_union_le O (LMS.biUnion (fun v => projPairs π.1 (XAll π g I v)))
      omega
    have hcard_covR : ((projPairs π.1 I).card : ℝ) ≤
        (O.card : ℝ) + ((LMS.biUnion (fun v => projPairs π.1 (XAll π g I v))).card : ℝ) +
        ((HR.biUnion (fun r => projPairs π.1 (XV π.1 g.1 I r))).card : ℝ) +
        ((HB.biUnion (fun b => projPairs π.1 (XV π.2 g.2 I b))).card : ℝ) +
        ((projPairs π.1 I ∩ (Q12one π.1 I c.Fthr ∪ Q3one π.1 g.1 I c.Fthr c.Nthr)).card : ℝ) := by
      exact_mod_cast hcard_cov
    have hch_low : ((I.image π.1).card : ℝ) ^ 2 / 2 - (c.k : ℝ) / 2 ≤ ((projPairs π.1 I).card : ℝ) := by
      rw [projPairs_card]
      set ℓ := (I.image π.1).card
      have hℓ_le : (ℓ : ℝ) ≤ (c.k : ℝ) := by exact_mod_cast (Finset.card_image_le.trans hI.le)
      have h2 : (ℓ.choose 2 : ℝ) = (ℓ : ℝ) * ((ℓ : ℝ) - 1) / 2 := by
        cases ℓ with
        | zero => simp
        | succ a =>
          rw [Nat.choose_two_right]
          have heven : 2 ∣ (a + 1) * a := by
            rcases Nat.even_or_odd a with ⟨j, rfl⟩ | ⟨j, rfl⟩
            · exact ⟨(j + j + 1) * j, by ring⟩
            · exact ⟨(j + 1) * (2 * j + 1), by ring⟩
          have hcast : (((a + 1) * a / 2 : ℕ) : ℝ) = (((a + 1) * a : ℕ) : ℝ) / 2 :=
            Nat.cast_div heven (by norm_num)
          rw [Nat.add_sub_cancel, hcast]
          push_cast; ring
      rw [h2]; linarith
    have h1_LMS : ((LMS.biUnion (fun v => projPairs π.1 (XAll π g I v))).card : ℝ) ≤ 3 * c.ε₁ * (c.k : ℝ) ^ 2 :=
      (Nat.cast_le.mpr (card_biUnion_projPairs_le_pairsOf π.1 LMS (XAll π g I))).trans hLMS_pairs
    have h2_HR : ((HR.biUnion (fun r => projPairs π.1 (XV π.1 g.1 I r))).card : ℝ) ≤ c.ε₁ * (c.k : ℝ) ^ 2 := by
      have hle : ((HR.biUnion (fun r => projPairs π.1 (XV π.1 g.1 I r))).card : ℝ) ≤
          ∑ r ∈ HR, ((projPairs π.1 (XV π.1 g.1 I r)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      exact hle.trans (hHR_same.trans hc.hH_same_loss)
    have h3_HB : ((HB.biUnion (fun b => projPairs π.1 (XV π.2 g.2 I b))).card : ℝ) ≤
        gCap (c.p * (c.n : ℝ)) ((c.k - (I.image π.2).card : ℕ) : ℝ) + 2 * c.ε₁ * (c.k : ℝ) ^ 2 := by
      have hle : ((HB.biUnion (fun b => projPairs π.1 (XV π.2 g.2 I b))).card : ℝ) ≤
          ∑ b ∈ HB, ((projPairs π.1 (XV π.2 g.2 I b)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      have hyk : ((c.k - (I.image π.2).card : ℕ) : ℝ) ≤ (c.k : ℝ) := by
        exact_mod_cast Nat.sub_le c.k _
      exact hle.trans (hHB_cross.trans (hgCap_excess _ _ (Nat.cast_nonneg _) hyk (Nat.cast_nonneg _) hc.hH_cross_delta))
    have h4_Q : ((projPairs π.1 I ∩ (Q12one π.1 I c.Fthr ∪ Q3one π.1 g.1 I c.Fthr c.Nthr)).card : ℝ) ≤
        c.ε₁ * (c.k : ℝ) ^ 2 := by
      have hq1 : ((projPairs π.1 I ∩ (Q12one π.1 I c.Fthr ∪ Q3one π.1 g.1 I c.Fthr c.Nthr)).card : ℝ) ≤
          (((F1set π.1 I c.Fthr).card : ℝ) + ((F2set π.1 g.1 I c.Fthr c.Nthr).card : ℝ)) *
            ((I.image π.1).card : ℝ) := by
        exact_mod_cast card_projPairs_inter_Q123_le π.1 g.1 I c.Fthr c.Nthr
      have hF2R_R : ((F2set π.1 g.1 I c.Fthr c.Nthr).card : ℝ) ≤ (c.L_cap : ℝ) + (c.H_cap : ℝ) := by
        exact_mod_cast hF2R_card
      have hI1_le : ((I.image π.1).card : ℝ) ≤ (c.k : ℝ) := by
        exact_mod_cast Finset.card_image_le.trans hI.le
      calc ((projPairs π.1 I ∩ (Q12one π.1 I c.Fthr ∪ Q3one π.1 g.1 I c.Fthr c.Nthr)).card : ℝ)
          ≤ (((F1set π.1 I c.Fthr).card : ℝ) + ((F2set π.1 g.1 I c.Fthr c.Nthr).card : ℝ)) * (c.k : ℝ) :=
            hq1.trans (mul_le_mul_of_nonneg_left hI1_le (by positivity))
        _ ≤ ((c.k : ℝ) / c.Fthr + (c.L_cap : ℝ) + (c.H_cap : ℝ)) * (c.k : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
        _ ≤ c.ε₁ * (c.k : ℝ) ^ 2 := hc.hQ_loss
    linarith [hc.hHalf_k]
  -- Symmetric lower bound on blue open unrevealed pairs:
  have hOpenB : ((I.image π.2).card : ℝ) ^ 2 / 2 -
      gCap (c.p * (c.n : ℝ)) ((c.k - (I.image π.1).card : ℕ) : ℝ) - 8 * c.ε₁ * (c.k : ℝ) ^ 2 ≤
      (((projPairs π.2 I \ (Finset.univ.biUnion (fun v : Fin c.m ⊕ Fin c.m => projPairs π.2 (XAll π g I v)))) \
        (Q12one π.2 I c.Fthr ∪ Q3one π.2 g.2 I c.Fthr c.Nthr)).card : ℝ) := by
    let O := (projPairs π.2 I \ (Finset.univ.biUnion (fun v : Fin c.m ⊕ Fin c.m => projPairs π.2 (XAll π g I v)))) \
        (Q12one π.2 I c.Fthr ∪ Q3one π.2 g.2 I c.Fthr c.Nthr)
    have hcov : projPairs π.2 I ⊆
        O ∪ LMS.biUnion (fun v => projPairs π.2 (XAll π g I v)) ∪
        HB.biUnion (fun b => projPairs π.2 (XV π.2 g.2 I b)) ∪
        HR.biUnion (fun r => projPairs π.2 (XV π.1 g.1 I r)) ∪
        (projPairs π.2 I ∩ (Q12one π.2 I c.Fthr ∪ Q3one π.2 g.2 I c.Fthr c.Nthr)) := by
      intro e he
      by_cases hq : e ∈ Q12one π.2 I c.Fthr ∪ Q3one π.2 g.2 I c.Fthr c.Nthr
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨he, hq⟩)
      · refine Finset.mem_union_left _ ?_
        by_cases hcl : e ∈ Finset.univ.biUnion (fun v : Fin c.m ⊕ Fin c.m => projPairs π.2 (XAll π g I v))
        · obtain ⟨v, _, hev⟩ := Finset.mem_biUnion.mp hcl
          by_cases hvH : v ∈ Hset π g I c.t₁
          · cases v with
            | inr b =>
              refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
              refine Finset.mem_biUnion.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvH⟩, ?_⟩
              rwa [XAll_inr] at hev
            | inl r =>
              refine Finset.mem_union_right _ ?_
              refine Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvH⟩, ?_⟩
              rwa [XAll_inl] at hev
          · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
            have hvLMS : v ∈ LMS := by
              rcases mem_LMS_of_not_mem_H π g I c.t₁ c.t₂ c.t₃ v hvH with hL | hM | hS
              · exact Finset.mem_union_left _ (Finset.mem_union_left _ hL)
              · exact Finset.mem_union_left _ (Finset.mem_union_right _ hM)
              · exact Finset.mem_union_right _ hS
            exact Finset.mem_biUnion.mpr ⟨v, hvLMS, hev⟩
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨he, hcl⟩, hq⟩)))
    have hcard_cov : (projPairs π.2 I).card ≤
        O.card + (LMS.biUnion (fun v => projPairs π.2 (XAll π g I v))).card +
        (HB.biUnion (fun b => projPairs π.2 (XV π.2 g.2 I b))).card +
        (HR.biUnion (fun r => projPairs π.2 (XV π.1 g.1 I r))).card +
        (projPairs π.2 I ∩ (Q12one π.2 I c.Fthr ∪ Q3one π.2 g.2 I c.Fthr c.Nthr)).card := by
      have h1 := Finset.card_le_card hcov
      have h2 := Finset.card_union_le
        (O ∪ LMS.biUnion (fun v => projPairs π.2 (XAll π g I v)) ∪
          HB.biUnion (fun b => projPairs π.2 (XV π.2 g.2 I b)) ∪
          HR.biUnion (fun r => projPairs π.2 (XV π.1 g.1 I r)))
        (projPairs π.2 I ∩ (Q12one π.2 I c.Fthr ∪ Q3one π.2 g.2 I c.Fthr c.Nthr))
      have h3 := Finset.card_union_le
        (O ∪ LMS.biUnion (fun v => projPairs π.2 (XAll π g I v)) ∪
          HB.biUnion (fun b => projPairs π.2 (XV π.2 g.2 I b)))
        (HR.biUnion (fun r => projPairs π.2 (XV π.1 g.1 I r)))
      have h4 := Finset.card_union_le
        (O ∪ LMS.biUnion (fun v => projPairs π.2 (XAll π g I v)))
        (HB.biUnion (fun b => projPairs π.2 (XV π.2 g.2 I b)))
      have h5 := Finset.card_union_le O (LMS.biUnion (fun v => projPairs π.2 (XAll π g I v)))
      omega
    have hcard_covR : ((projPairs π.2 I).card : ℝ) ≤
        (O.card : ℝ) + ((LMS.biUnion (fun v => projPairs π.2 (XAll π g I v))).card : ℝ) +
        ((HB.biUnion (fun b => projPairs π.2 (XV π.2 g.2 I b))).card : ℝ) +
        ((HR.biUnion (fun r => projPairs π.2 (XV π.1 g.1 I r))).card : ℝ) +
        ((projPairs π.2 I ∩ (Q12one π.2 I c.Fthr ∪ Q3one π.2 g.2 I c.Fthr c.Nthr)).card : ℝ) := by
      exact_mod_cast hcard_cov
    have hch_low : ((I.image π.2).card : ℝ) ^ 2 / 2 - (c.k : ℝ) / 2 ≤ ((projPairs π.2 I).card : ℝ) := by
      rw [projPairs_card]
      set ℓ := (I.image π.2).card
      have hℓ_le : (ℓ : ℝ) ≤ (c.k : ℝ) := by exact_mod_cast (Finset.card_image_le.trans hI.le)
      have h2 : (ℓ.choose 2 : ℝ) = (ℓ : ℝ) * ((ℓ : ℝ) - 1) / 2 := by
        cases ℓ with
        | zero => simp
        | succ a =>
          rw [Nat.choose_two_right]
          have heven : 2 ∣ (a + 1) * a := by
            rcases Nat.even_or_odd a with ⟨j, rfl⟩ | ⟨j, rfl⟩
            · exact ⟨(j + j + 1) * j, by ring⟩
            · exact ⟨(j + 1) * (2 * j + 1), by ring⟩
          have hcast : (((a + 1) * a / 2 : ℕ) : ℝ) = (((a + 1) * a : ℕ) : ℝ) / 2 :=
            Nat.cast_div heven (by norm_num)
          rw [Nat.add_sub_cancel, hcast]
          push_cast; ring
      rw [h2]; linarith
    have h1_LMS : ((LMS.biUnion (fun v => projPairs π.2 (XAll π g I v))).card : ℝ) ≤ 3 * c.ε₁ * (c.k : ℝ) ^ 2 :=
      (Nat.cast_le.mpr (card_biUnion_projPairs_le_pairsOf π.2 LMS (XAll π g I))).trans hLMS_pairs
    have h2_HB : ((HB.biUnion (fun b => projPairs π.2 (XV π.2 g.2 I b))).card : ℝ) ≤ c.ε₁ * (c.k : ℝ) ^ 2 := by
      have hle : ((HB.biUnion (fun b => projPairs π.2 (XV π.2 g.2 I b))).card : ℝ) ≤
          ∑ b ∈ HB, ((projPairs π.2 (XV π.2 g.2 I b)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      exact hle.trans (hHB_same.trans hc.hH_same_loss)
    have h3_HR : ((HR.biUnion (fun r => projPairs π.2 (XV π.1 g.1 I r))).card : ℝ) ≤
        gCap (c.p * (c.n : ℝ)) ((c.k - (I.image π.1).card : ℕ) : ℝ) + 2 * c.ε₁ * (c.k : ℝ) ^ 2 := by
      have hle : ((HR.biUnion (fun r => projPairs π.2 (XV π.1 g.1 I r))).card : ℝ) ≤
          ∑ r ∈ HR, ((projPairs π.2 (XV π.1 g.1 I r)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      have hyk : ((c.k - (I.image π.1).card : ℕ) : ℝ) ≤ (c.k : ℝ) := by
        exact_mod_cast Nat.sub_le c.k _
      exact hle.trans (hHR_cross.trans (hgCap_excess _ _ (Nat.cast_nonneg _) hyk (Nat.cast_nonneg _) hc.hH_cross_delta))
    have h4_Q : ((projPairs π.2 I ∩ (Q12one π.2 I c.Fthr ∪ Q3one π.2 g.2 I c.Fthr c.Nthr)).card : ℝ) ≤
        c.ε₁ * (c.k : ℝ) ^ 2 := by
      have hq1 : ((projPairs π.2 I ∩ (Q12one π.2 I c.Fthr ∪ Q3one π.2 g.2 I c.Fthr c.Nthr)).card : ℝ) ≤
          (((F1set π.2 I c.Fthr).card : ℝ) + ((F2set π.2 g.2 I c.Fthr c.Nthr).card : ℝ)) *
            ((I.image π.2).card : ℝ) := by
        exact_mod_cast card_projPairs_inter_Q123_le π.2 g.2 I c.Fthr c.Nthr
      have hF2B_R : ((F2set π.2 g.2 I c.Fthr c.Nthr).card : ℝ) ≤ (c.L_cap : ℝ) + (c.H_cap : ℝ) := by
        exact_mod_cast hF2B_card
      have hI2_le : ((I.image π.2).card : ℝ) ≤ (c.k : ℝ) := by
        exact_mod_cast Finset.card_image_le.trans hI.le
      calc ((projPairs π.2 I ∩ (Q12one π.2 I c.Fthr ∪ Q3one π.2 g.2 I c.Fthr c.Nthr)).card : ℝ)
          ≤ (((F1set π.2 I c.Fthr).card : ℝ) + ((F2set π.2 g.2 I c.Fthr c.Nthr).card : ℝ)) * (c.k : ℝ) :=
            hq1.trans (mul_le_mul_of_nonneg_left hI2_le (by positivity))
        _ ≤ ((c.k : ℝ) / c.Fthr + (c.L_cap : ℝ) + (c.H_cap : ℝ)) * (c.k : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
        _ ≤ c.ε₁ * (c.k : ℝ) ^ 2 := hc.hQ_loss
    linarith [hc.hHalf_k]
  -- Combine red + blue open bounds into `Nat.floor`!
  have hZ_sum : c.fVal (I.image π.1).card (I.image π.2).card - 16 * c.ε₁ * (c.k : ℝ) ^ 2 ≤
      (((projPairs π.1 I \ (Finset.univ.biUnion (fun v : Fin c.m ⊕ Fin c.m => projPairs π.1 (XAll π g I v)))) \
        (Q12one π.1 I c.Fthr ∪ Q3one π.1 g.1 I c.Fthr c.Nthr)).card +
       ((projPairs π.2 I \ (Finset.univ.biUnion (fun v : Fin c.m ⊕ Fin c.m => projPairs π.2 (XAll π g I v)))) \
        (Q12one π.2 I c.Fthr ∪ Q3one π.2 g.2 I c.Fthr c.Nthr)).card : ℕ) := by
    unfold Cfg.fVal
    push_cast
    linarith
  have hZ_nat : ⌊c.fVal (I.image π.1).card (I.image π.2).card - 16 * c.ε₁ * (c.k : ℝ) ^ 2⌋₊ ≤
      ((projPairs π.1 I \ (Finset.univ.biUnion (fun v : Fin c.m ⊕ Fin c.m => projPairs π.1 (XAll π g I v)))) \
        (Q12one π.1 I c.Fthr ∪ Q3one π.1 g.1 I c.Fthr c.Nthr)).card +
      ((projPairs π.2 I \ (Finset.univ.biUnion (fun v : Fin c.m ⊕ Fin c.m => projPairs π.2 (XAll π g I v)))) \
        (Q12one π.2 I c.Fthr ∪ Q3one π.2 g.2 I c.Fthr c.Nthr)).card := by
    by_cases hneg : c.fVal (I.image π.1).card (I.image π.2).card - 16 * c.ε₁ * (c.k : ℝ) ^ 2 ≤ 0
    · rw [Nat.floor_eq_zero.mpr (by linarith)]; exact Nat.zero_le _
    · push Not at hneg
      exact_mod_cast (Nat.floor_le hneg.le).trans hZ_sum
  exact ⟨hC1, hC2, hZ_nat⟩

end GoodRImpliesRISI

section Lemma42AndMainProb

/-- Pure algebraic 3-case exponent bound for Lemma 4.2 (`lem:RI`). -/
lemma three_case_exponent_bound {ε κ a xR xB : ℝ}
    (hε0 : 0 < ε) (hε32 : ε ≤ 1 / 32)
    (hκ_low : 1 + 7 * ε / 8 ≤ κ) (hκ_high : κ ≤ 1 + ε)
    (hκa : κ * a = 1 / 2)
    (_hxR0 : 0 ≤ xR) (_hxR1 : xR ≤ 1) (_hxB0 : 0 ≤ xB) (_hxB1 : xB ≤ 1) :
    let F := xR ^ 2 / 2 + xB ^ 2 / 2 - gCap a (1 - xR) - gCap a (1 - xB)
    let E1 := (xR + xB - 1) / 2 + 3 * ε ^ 3 / 40
    let E2 := (xR + xB - 1) / 2 + 3 * ε ^ 3 / 40 + (κ / 2) * (ε ^ 3 / 20 - F)
    min E1 E2 ≤ -(ε ^ 2 / 8) := by
  dsimp only
  set s := xR + xB
  set F := xR ^ 2 / 2 + xB ^ 2 / 2 - gCap a (1 - xR) - gCap a (1 - xB)
  have hκ_pos : 0 < κ := by linarith only [hε0, hκ_low]
  have ha_pos : 0 < a := by nlinarith only [hκ_pos, hκa]
  have hκ_le2 : κ ≤ 2 := by linarith only [hε32, hκ_high]
  have hε_sq_le : ε ^ 2 ≤ ε / 32 := by nlinarith only [hε0, hε32]
  have hε3_le_sq : ε ^ 3 ≤ ε ^ 2 / 32 := by
    have : ε ^ 3 = ε * ε ^ 2 := by ring
    nlinarith only [this, hε0, hε32, sq_nonneg ε]
  -- Case 1: `s ≤ 1 - ε / 2` (use `E1`)
  by_cases hs1 : s ≤ 1 - ε / 2
  · refine (min_le_left _ _).trans ?_
    linarith only [hs1, hε0, hε_sq_le, hε3_le_sq]
  push Not at hs1
  -- In Cases 2 and 3, use `E2`!
  refine (min_le_right _ _).trans ?_
  -- Universal bound: `F ≥ s - 1`
  have hF_ge_s : s - 1 ≤ F := by
    have h1 : gCap a (1 - xR) ≤ (1 - xR) ^ 2 / 2 := gCap_le_half_sq ha_pos.le
    have h2 : gCap a (1 - xB) ≤ (1 - xB) ^ 2 / 2 := gCap_le_half_sq ha_pos.le
    dsimp only [F, s]
    linarith only [h1, h2]
  -- Case 2: `s ≥ 1 + ε / 2`
  by_cases hs2 : 1 + ε / 2 ≤ s
  · have hstep1 : (s - 1) / 2 + 3 * ε ^ 3 / 40 + (κ / 2) * (ε ^ 3 / 20 - F) ≤
        -((κ - 1) / 2) * (s - 1) + ((3 + κ) / 40) * ε ^ 3 := by
      have hmul : (κ / 2) * (s - 1) ≤ (κ / 2) * F := mul_le_mul_of_nonneg_left hF_ge_s (by linarith only [hκ_pos])
      linarith only [hmul]
    have hstep2 : -((κ - 1) / 2) * (s - 1) ≤ -(7 * ε / 16) * (ε / 2) := by
      nlinarith only [hκ_low, hs2, hε0]
    have hstep3 : ((3 + κ) / 40) * ε ^ 3 ≤ ε ^ 3 / 8 := by
      have hε3_0 : 0 ≤ ε ^ 3 := pow_nonneg hε0.le 3
      nlinarith only [hκ_le2, hε3_0]
    linarith only [hstep1, hstep2, hstep3, hε3_le_sq, sq_nonneg ε]
  -- Case 3: `1 - ε / 2 < s < 1 + ε / 2`
  push Not at hs2
  have ha_le : a ≤ 1 / 2 - 3 * ε / 8 := by
    have h1 : 1 ≤ (1 / 2 - 3 * ε / 8) * (2 * (1 + 7 * ε / 8)) := by nlinarith only [hε0, hε32, sq_nonneg ε]
    have h2 : 1 ≤ (1 / 2 - 3 * ε / 8) * (2 * κ) := by nlinarith only [h1, hκ_low, hε32]
    nlinarith only [h2, hκa, hκ_pos]
  have hF_case3 : ∀ u v : ℝ, u ≤ v → u + v = s →
      (s - 1) + a * (1 - u - a) ≤ u ^ 2 / 2 + v ^ 2 / 2 - gCap a (1 - u) - gCap a (1 - v) := by
    intro u v huv huvs
    have hu_lt : u < 1 / 2 + ε / 4 := by linarith only [huv, huvs, hs2]
    have hdiff_gt : ε / 8 < 1 - u - a := by linarith only [hu_lt, ha_le]
    have hnotle : ¬ (1 - u ≤ a) := by linarith only [hdiff_gt, hε0]
    have hg_u : gCap a (1 - u) = a ^ 2 / 2 + (1 - u - a) ^ 2 / 2 := by
      unfold gCap; rw [if_neg hnotle]; ring
    have hg_v : gCap a (1 - v) ≤ (1 - v) ^ 2 / 2 := gCap_le_half_sq ha_pos.le
    rw [hg_u]
    have hid : u ^ 2 / 2 + v ^ 2 / 2 - (a ^ 2 / 2 + (1 - u - a) ^ 2 / 2) - (1 - v) ^ 2 / 2 =
        (u + v - 1) + a * (1 - u - a) := by ring
    linarith only [hg_v, hid, huvs]
  have hF_extra : ∃ u : ℝ, u < 1 / 2 + ε / 4 ∧ (s - 1) + a * (1 - u - a) ≤ F := by
    rcases le_total xR xB with hle | hle
    · refine ⟨xR, by linarith only [hle, hs2], ?_⟩
      simpa [F] using hF_case3 xR xB hle rfl
    · refine ⟨xB, by linarith only [hle, hs2], ?_⟩
      have h3 := hF_case3 xB xR hle (add_comm xB xR)
      dsimp only [F]; linarith only [h3]
  obtain ⟨u, hu_lt, hFu⟩ := hF_extra
  have hdiff_gt : ε / 8 < 1 - u - a := by linarith only [hu_lt, ha_le]
  have hterm1 : -((κ - 1) / 2) * (s - 1) ≤ ε ^ 2 / 4 := by
    by_cases hs0 : 0 ≤ s - 1
    · nlinarith only [hκ_low, hε0, hs0, sq_nonneg ε]
    · push Not at hs0
      nlinarith only [hκ_low, hκ_high, hs1, hs0, hε0]
  have hterm2 : (κ / 2) * (a * (1 - u - a)) = (1 / 4) * (1 - u - a) := by
    have : κ / 2 * (a * (1 - u - a)) = (κ * a) / 2 * (1 - u - a) := by ring
    rw [this, hκa]; ring
  have hterm3 : ((3 + κ) / 40) * ε ^ 3 ≤ ε ^ 3 / 8 := by
    have hε3_0 : 0 ≤ ε ^ 3 := pow_nonneg hε0.le 3
    nlinarith only [hκ_le2, hε3_0]
  have hF_plug : (s - 1) / 2 + 3 * ε ^ 3 / 40 + (κ / 2) * (ε ^ 3 / 20 - F) ≤
      -((κ - 1) / 2) * (s - 1) - (1 / 4) * (1 - u - a) + ((3 + κ) / 40) * ε ^ 3 := by
    have hmul : (κ / 2) * ((s - 1) + a * (1 - u - a)) ≤ (κ / 2) * F :=
      mul_le_mul_of_nonneg_left hFu (by linarith only [hκ_pos])
    linarith only [hmul, hterm2]
  linarith only [hF_plug, hterm1, hdiff_gt, hterm3, hε_sq_le, hε3_le_sq, hε0]

/-- Uniform combinatorial bound on `Pr(S_{I, ℓR, ℓB})`:
for any `1 ≤ ℓ ≤ k ≤ m`, `(m.choose ℓ) * (ℓ / m)^k ≤ exp k * (k / m)^(k - ℓ)`. -/
lemma choose_mul_pow_le_exp_pow {m k ℓ : ℕ} (hm : 0 < m) (hℓ1 : 1 ≤ ℓ) (hℓk : ℓ ≤ k) :
    (m.choose ℓ : ℝ) * ((ℓ : ℝ) / (m : ℝ)) ^ k ≤
      Real.exp (k : ℝ) * ((k : ℝ) / (m : ℝ)) ^ (k - ℓ) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ1
  have hch := choose_le_exp_pow (n := m) (k := ℓ) hℓ1
  have hsplit : ((ℓ : ℝ) / (m : ℝ)) ^ k = ((ℓ : ℝ) / (m : ℝ)) ^ ℓ * ((ℓ : ℝ) / (m : ℝ)) ^ (k - ℓ) := by
    rw [← pow_add, Nat.add_sub_of_le hℓk]
  have hcancel : (Real.exp 1 * (m : ℝ) / (ℓ : ℝ)) ^ ℓ * ((ℓ : ℝ) / (m : ℝ)) ^ ℓ = Real.exp (ℓ : ℝ) := by
    rw [← mul_pow]
    have h1 : Real.exp 1 * (m : ℝ) / (ℓ : ℝ) * ((ℓ : ℝ) / (m : ℝ)) = Real.exp 1 := by
      field_simp [hmpos.ne', hℓpos.ne']
    rw [h1, ← Real.exp_nat_mul, mul_one]
  have hexp_le : Real.exp (ℓ : ℝ) ≤ Real.exp (k : ℝ) :=
    Real.exp_le_exp.mpr (by exact_mod_cast hℓk)
  have hbase_le : ((ℓ : ℝ) / (m : ℝ)) ^ (k - ℓ) ≤ ((k : ℝ) / (m : ℝ)) ^ (k - ℓ) := by
    refine pow_le_pow_left₀ (by positivity) ?_ (k - ℓ)
    exact div_le_div_of_nonneg_right (by exact_mod_cast hℓk) hmpos.le
  calc (m.choose ℓ : ℝ) * ((ℓ : ℝ) / (m : ℝ)) ^ k
      ≤ (Real.exp 1 * (m : ℝ) / (ℓ : ℝ)) ^ ℓ * ((ℓ : ℝ) / (m : ℝ)) ^ k :=
        mul_le_mul_of_nonneg_right hch (by positivity)
    _ = ((Real.exp 1 * (m : ℝ) / (ℓ : ℝ)) ^ ℓ * ((ℓ : ℝ) / (m : ℝ)) ^ ℓ) *
          ((ℓ : ℝ) / (m : ℝ)) ^ (k - ℓ) := by rw [hsplit]; ring
    _ = Real.exp (ℓ : ℝ) * ((ℓ : ℝ) / (m : ℝ)) ^ (k - ℓ) := by rw [hcancel]
    _ ≤ Real.exp (k : ℝ) * ((k : ℝ) / (m : ℝ)) ^ (k - ℓ) :=
        mul_le_mul hexp_le hbase_le (by positivity) (Real.exp_pos _).le

/-- Lemma 4.2 (`lem:RI`): for any fixed `k`-subset `I`,
`(n.choose k) * Pr (fullW) (IndepI ∧ GoodR) < 1 / 4`. -/
lemma lem_RI_bound {c : Cfg} (hc : ValidCfg c) (I : Finset (Fin c.n)) (hI : I.card = c.k) :
    (c.n.choose c.k : ℝ) * Pr (fullW c.n c.m c.p) (fun ω => IndepI ω.1 ω.2 I ∧ GoodR c ω) < 1 / 4 := by
  have hmpos : 0 < c.m := by have := hc.hm; omega
  have hkpos : (0 : ℝ) < (c.k : ℝ) := by exact_mod_cast hc.hk1
  have hmposR : (0 : ℝ) < (c.m : ℝ) := by exact_mod_cast hmpos
  have hnposR : (0 : ℝ) < (c.n : ℝ) := by exact_mod_cast (by have := hc.hn; omega : 0 < c.n)
  have hPpi1 : IsProb (unifW (Fin c.n) c.m) := isProb_unifW hmpos
  have hPpi : IsProb (piPairW c.n c.m) := isProb_piPairW hmpos
  have hPg : IsProb (gPairW c.m c.p) := isProb_gPairW hc.hp0 hc.hp1
  have hP : IsProb (fullW c.n c.m c.p) := isProb_fullW hmpos hc.hp0 hc.hp1
  have hIne : I.Nonempty := Finset.card_pos.mp (by rw [hI]; exact hc.hk1)
  let pairs : Finset (ℕ × ℕ) := (Finset.Icc 1 c.k) ×ˢ (Finset.Icc 1 c.k)
  have himp : ∀ ω : Omega c.n c.m, (IndepI ω.1 ω.2 I ∧ GoodR c ω) →
      ∃ ℓ ∈ pairs, IndepI ω.1 ω.2 I ∧ GoodR c ω ∧
        (I.image ω.1.1).card = ℓ.1 ∧ (I.image ω.1.2).card = ℓ.2 := by
    intro ω h
    have h1 : 1 ≤ (I.image ω.1.1).card := Finset.card_pos.mpr (hIne.image _)
    have h2 : (I.image ω.1.1).card ≤ c.k := Finset.card_image_le.trans hI.le
    have h3 : 1 ≤ (I.image ω.1.2).card := Finset.card_pos.mpr (hIne.image _)
    have h4 : (I.image ω.1.2).card ≤ c.k := Finset.card_image_le.trans hI.le
    refine ⟨((I.image ω.1.1).card, (I.image ω.1.2).card),
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, Finset.mem_Icc.mpr ⟨h3, h4⟩⟩,
      h.1, h.2, rfl, rfl⟩
  -- Bound each `(ℓR, ℓB) ∈ pairs` by `2 * exp(-(ε^2 / 8) * k * L)`!
  have hterm : ∀ ℓ ∈ pairs,
      (c.n.choose c.k : ℝ) * Pr (fullW c.n c.m c.p) (fun ω =>
        IndepI ω.1 ω.2 I ∧ GoodR c ω ∧ (I.image ω.1.1).card = ℓ.1 ∧ (I.image ω.1.2).card = ℓ.2) ≤
      2 * Real.exp (-(c.ε ^ 2 / 8) * (c.k : ℝ) * c.L) := by
    intro ⟨ℓR, ℓB⟩ hℓ
    obtain ⟨hℓR_mem, hℓB_mem⟩ := Finset.mem_product.mp hℓ
    obtain ⟨hℓR1, hℓRk⟩ := Finset.mem_Icc.mp hℓR_mem
    obtain ⟨hℓB1, hℓBk⟩ := Finset.mem_Icc.mp hℓB_mem
    set xR : ℝ := (ℓR : ℝ) / (c.k : ℝ)
    set xB : ℝ := (ℓB : ℝ) / (c.k : ℝ)
    set κ : ℝ := 2 * c.p * (c.k : ℝ) / c.L
    set a : ℝ := c.p * (c.n : ℝ) / (c.k : ℝ)
    set F : ℝ := xR ^ 2 / 2 + xB ^ 2 / 2 - gCap a (1 - xR) - gCap a (1 - xB)
    have hκ_low : 1 + 7 * c.ε / 8 ≤ κ := by
      dsimp only [κ]; rw [le_div_iff₀ hc.hL_pos]; linarith [hc.hpk_low]
    have hκ_high : κ ≤ 1 + c.ε := by
      dsimp only [κ]; rw [div_le_iff₀ hc.hL_pos]; linarith [hc.hpk_high]
    have hκa : κ * a = 1 / 2 := by
      dsimp only [κ, a]
      have hLne : c.L ≠ 0 := hc.hL_pos.ne'
      have hkne : (c.k : ℝ) ≠ 0 := hkpos.ne'
      have h1 : 2 * c.p * (c.k : ℝ) / c.L * (c.p * (c.n : ℝ) / (c.k : ℝ)) =
          2 * (c.p ^ 2 * (c.n : ℝ)) / c.L := by field_simp [hLne, hkne]
      rw [h1, hc.hp_sq]; field_simp [hLne]; ring
    have hfVal_eq : c.fVal ℓR ℓB = (c.k : ℝ) ^ 2 * F := by
      unfold Cfg.fVal
      have h1 : c.p * (c.n : ℝ) = (c.k : ℝ) * a := by dsimp only [a]; field_simp [hkpos.ne']
      have h2 : ((c.k - ℓR : ℕ) : ℝ) = (c.k : ℝ) * (1 - xR) := by
        rw [Nat.cast_sub hℓRk]; dsimp only [xR]; field_simp [hkpos.ne']
      have h3 : ((c.k - ℓB : ℕ) : ℝ) = (c.k : ℝ) * (1 - xB) := by
        rw [Nat.cast_sub hℓBk]; dsimp only [xB]; field_simp [hkpos.ne']
      rw [h1, h2, h3, gCap_scale hkpos, gCap_scale hkpos]
      have h4 : (ℓR : ℝ) = (c.k : ℝ) * xR := by dsimp only [xR]; field_simp [hkpos.ne']
      have h5 : (ℓB : ℝ) = (c.k : ℝ) * xB := by dsimp only [xB]; field_simp [hkpos.ne']
      rw [h4, h5]; dsimp only [F]; ring
    -- Step 1: Bound `Pr(fullW)(...) ≤ Pr(piPairW)(|π1(I)| ≤ ℓR ∧ |π2(I)| ≤ ℓB) * B_RISI`
    let B_RISI : ℝ := min 1 (2 * Real.exp ((c.ε ^ 3 / 20) * c.p * (c.k : ℝ) ^ 2 - c.p * c.fVal ℓR ℓB))
    have hBR_nn : 0 ≤ B_RISI := le_min (by norm_num) (by positivity)
    have hPr_split : Pr (fullW c.n c.m c.p) (fun ω =>
        IndepI ω.1 ω.2 I ∧ GoodR c ω ∧ (I.image ω.1.1).card = ℓR ∧ (I.image ω.1.2).card = ℓB) ≤
      Pr (piPairW c.n c.m) (fun π => (I.image π.1).card ≤ ℓR ∧ (I.image π.2).card ≤ ℓB) * B_RISI := by
      rw [fullW, Pr_prodW]
      have hinner : ∀ π : PiPair c.n c.m,
          Pr (gPairW c.m c.p) (fun g => IndepI π g I ∧ GoodR c (π, g) ∧
            (I.image π.1).card = ℓR ∧ (I.image π.2).card = ℓB) ≤
          (by classical exact if (I.image π.1).card ≤ ℓR ∧ (I.image π.2).card ≤ ℓB then (1 : ℝ) else 0) * B_RISI := by
        intro π
        by_cases hmatch : (I.image π.1).card = ℓR ∧ (I.image π.2).card = ℓB
        · have hle : (I.image π.1).card ≤ ℓR ∧ (I.image π.2).card ≤ ℓB := ⟨hmatch.1.le, hmatch.2.le⟩
          rw [if_pos hle, one_mul]
          refine le_min (Pr_le_one hPg _) ?_
          rw [Pr_congr (fun g => show (IndepI π g I ∧ GoodR c (π, g) ∧ (I.image π.1).card = ℓR ∧ (I.image π.2).card = ℓB) ↔
              (IndepI π g I ∧ GoodR c (π, g)) by tauto)]
          set Z_min := ⌊c.fVal ℓR ℓB - 16 * c.ε₁ * (c.k : ℝ) ^ 2⌋₊
          have hRISI := lem_RISI_fixed_pi (M₁ := c.M₁) (Z_min := Z_min) (Fthr := c.Fthr) (Nthr := c.Nthr)
            hc.hp0 hc.hp1 hc.hr_pos hc.hr_le_one π I hI (fun g => GoodR c (π, g))
            (fun g _ hG => (goodR_imp_RISI_hyps hc π g hG I hI).1)
            (fun g _ hG => (goodR_imp_RISI_hyps hc π g hG I hI).2.1)
            (fun g _ hG => by
              have hZ := (goodR_imp_RISI_hyps hc π g hG I hI).2.2
              rwa [hmatch.1, hmatch.2] at hZ)
          refine hRISI.trans ?_
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
          have hM1_le : (c.M₁ : ℝ) ≤ 3 * c.ε₁ * (c.k : ℝ) ^ 2 := by
            rw [hc.hM₁_eq]; exact Nat.floor_le (by have := hc.hε₁_pos; positivity)
          have hZ_ge : c.fVal ℓR ℓB - 17 * c.ε₁ * (c.k : ℝ) ^ 2 ≤ (Z_min : ℝ) := by
            have h1 := Nat.sub_one_lt_floor (c.fVal ℓR ℓB - 16 * c.ε₁ * (c.k : ℝ) ^ 2)
            linarith [hc.hOne_le]
          have hM1_div : (c.M₁ : ℝ) / c.r ≤ 3 * c.r * (c.k : ℝ) ^ 2 := by
            rw [div_le_iff₀ hc.hr_pos]
            have : 3 * c.r * (c.k : ℝ) ^ 2 * c.r = 3 * c.r ^ 2 * (c.k : ℝ) ^ 2 := by ring
            rw [this, ← hc.hε₁_eq]; exact hM1_le
          have hcoeff : 4 * c.r + 17 * c.ε₁ ≤ c.ε ^ 3 / 20 := by
            rw [hc.hε₁_eq, hc.hr_eq]
            have h1 : c.ε ^ 3 ≤ 1 / 32 := by
              have hsq : c.ε ^ 2 ≤ 1 := by nlinarith only [hc.hε0, hc.hε32]
              have hcub : c.ε ^ 3 = c.ε * c.ε ^ 2 := by ring
              nlinarith only [hcub, hsq, hc.hε0, hc.hε32, sq_nonneg c.ε]
            have hpos3 : 0 < c.ε ^ 3 := pow_pos hc.hε0 3
            nlinarith only [h1, hpos3]
          have hcast_k2 : ((c.k ^ 2 : ℕ) : ℝ) = (c.k : ℝ) ^ 2 := by push_cast; rfl
          rw [hcast_k2]
          have hcomb : ((c.M₁ : ℝ) / c.r + c.r * (c.k : ℝ) ^ 2) * c.p - c.p * (Z_min : ℝ) ≤
              (4 * c.r + 17 * c.ε₁) * c.p * (c.k : ℝ) ^ 2 - c.p * c.fVal ℓR ℓB := by
            have h1 : ((c.M₁ : ℝ) / c.r + c.r * (c.k : ℝ) ^ 2) * c.p ≤ (4 * c.r * (c.k : ℝ) ^ 2) * c.p :=
              mul_le_mul_of_nonneg_right (by linarith) hc.hp0
            have h2 : c.p * (c.fVal ℓR ℓB - 17 * c.ε₁ * (c.k : ℝ) ^ 2) ≤ c.p * (Z_min : ℝ) :=
              mul_le_mul_of_nonneg_left hZ_ge hc.hp0
            linarith
          have hcomb2 : (4 * c.r + 17 * c.ε₁) * c.p * (c.k : ℝ) ^ 2 ≤ (c.ε ^ 3 / 20) * c.p * (c.k : ℝ) ^ 2 := by
            have hnn : 0 ≤ c.p * (c.k : ℝ) ^ 2 := mul_nonneg hc.hp0 (sq_nonneg _)
            nlinarith
          linarith
        · have hzero : Pr (gPairW c.m c.p) (fun g => IndepI π g I ∧ GoodR c (π, g) ∧
              (I.image π.1).card = ℓR ∧ (I.image π.2).card = ℓB) = 0 := by
            rw [Pr_congr (B := fun _ => False) (fun _ => ⟨fun h => hmatch ⟨h.2.2.1, h.2.2.2⟩, False.elim⟩), Pr_false]
          rw [hzero]
          refine mul_nonneg ?_ hBR_nn
          split_ifs <;> norm_num
      calc E (piPairW c.n c.m) _
          ≤ E (piPairW c.n c.m) (fun π =>
              (by classical exact if (I.image π.1).card ≤ ℓR ∧ (I.image π.2).card ≤ ℓB then (1 : ℝ) else 0) * B_RISI) :=
            E_mono hPpi hinner
        _ = Pr (piPairW c.n c.m) (fun π => (I.image π.1).card ≤ ℓR ∧ (I.image π.2).card ≤ ℓB) * B_RISI := by
            rw [Pr_eq_E]
            unfold E
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun π _ => ?_
            dsimp only; split_ifs <;> ring
    -- Step 2: Bound `(n.choose k) * Pr(piPairW)(...) ≤ exp(k * L * ((xR + xB - 1)/2 + 3*ε^3/40))`!
    have hPr_pi : (c.n.choose c.k : ℝ) *
        Pr (piPairW c.n c.m) (fun π => (I.image π.1).card ≤ ℓR ∧ (I.image π.2).card ≤ ℓB) ≤
        Real.exp ((c.k : ℝ) * c.L * ((xR + xB - 1) / 2 + 3 * c.ε ^ 3 / 40)) := by
      have hprod : Pr (piPairW c.n c.m) (fun π => (I.image π.1).card ≤ ℓR ∧ (I.image π.2).card ≤ ℓB) =
          Pr (unifW (Fin c.n) c.m) (fun π₁ => (I.image π₁).card ≤ ℓR) *
          Pr (unifW (Fin c.n) c.m) (fun π₂ => (I.image π₂).card ≤ ℓB) :=
        Pr_prodW_and (P := unifW (Fin c.n) c.m) (Q := unifW (Fin c.n) c.m)
          (fun π₁ => (I.image π₁).card ≤ ℓR) (fun π₂ => (I.image π₂).card ≤ ℓB)
      rw [hprod]
      have h1 := Pr_unifW_image_card_le hmpos I (hℓRk.trans hc.hkm)
      have h2 := Pr_unifW_image_card_le hmpos I (hℓBk.trans hc.hkm)
      rw [hI] at h1 h2
      have h1' := h1.trans (choose_mul_pow_le_exp_pow hmpos hℓR1 hℓRk)
      have h2' := h2.trans (choose_mul_pow_le_exp_pow hmpos hℓB1 hℓBk)
      have hch_n := choose_le_exp_pow (n := c.n) (k := c.k) hc.hk1
      have hcomb_ch : (Real.exp 1 * (c.n : ℝ) / (c.k : ℝ)) ^ c.k *
          (Real.exp (c.k : ℝ) * ((c.k : ℝ) / (c.m : ℝ)) ^ (c.k - ℓR)) *
          (Real.exp (c.k : ℝ) * ((c.k : ℝ) / (c.m : ℝ)) ^ (c.k - ℓB)) =
          (Real.exp 3) ^ c.k * ((c.n : ℝ) / (c.k : ℝ)) ^ c.k *
          ((c.k : ℝ) / (c.m : ℝ)) ^ ((c.k - ℓR) + (c.k - ℓB)) := by
        have h1e : (Real.exp 1 * (c.n : ℝ) / (c.k : ℝ)) ^ c.k =
            Real.exp (c.k : ℝ) * ((c.n : ℝ) / (c.k : ℝ)) ^ c.k := by
          rw [mul_div_assoc, mul_pow, ← Real.exp_nat_mul, mul_one]
        have h3e : (Real.exp 3) ^ c.k = Real.exp (c.k : ℝ) * Real.exp (c.k : ℝ) * Real.exp (c.k : ℝ) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
        rw [h1e, h3e, pow_add]; ring
      have he3_pow : (Real.exp 3) ^ c.k ≤ Real.exp ((c.ε ^ 3 / 40) * (c.k : ℝ) * c.L) := by
        calc (Real.exp 3) ^ c.k ≤ (Real.exp ((c.ε ^ 3 / 40) * c.L)) ^ c.k :=
              pow_le_pow_left₀ (Real.exp_pos _).le hc.h_e3_le c.k
          _ = Real.exp ((c.ε ^ 3 / 40) * (c.k : ℝ) * c.L) := by rw [← Real.exp_nat_mul]; congr 1; ring
      have hnk_pow : ((c.n : ℝ) / (c.k : ℝ)) ^ c.k ≤ Real.exp ((c.k : ℝ) * (c.L / 2)) := by
        calc ((c.n : ℝ) / (c.k : ℝ)) ^ c.k ≤ (Real.exp (c.L / 2)) ^ c.k :=
              pow_le_pow_left₀ (by positivity) hc.h_n_div_k c.k
          _ = Real.exp ((c.k : ℝ) * (c.L / 2)) := by rw [← Real.exp_nat_mul]
      set d : ℕ := (c.k - ℓR) + (c.k - ℓB)
      have hd_eq : (d : ℝ) = (2 - xR - xB) * (c.k : ℝ) := by
        dsimp only [d]
        rw [Nat.cast_add, Nat.cast_sub hℓRk, Nat.cast_sub hℓBk]
        dsimp only [xR, xB]; field_simp [hkpos.ne']; ring
      have hkm_pow : ((c.k : ℝ) / (c.m : ℝ)) ^ d ≤
          Real.exp (-(1 / 2 - c.ε ^ 3 / 40) * (2 - xR - xB) * (c.k : ℝ) * c.L) := by
        calc ((c.k : ℝ) / (c.m : ℝ)) ^ d ≤ (Real.exp (-(1 / 2 - c.ε ^ 3 / 40) * c.L)) ^ d :=
              pow_le_pow_left₀ (by positivity) hc.h_k_div_m d
          _ = Real.exp ((d : ℝ) * (-(1 / 2 - c.ε ^ 3 / 40) * c.L)) := by rw [← Real.exp_nat_mul]
          _ = Real.exp (-(1 / 2 - c.ε ^ 3 / 40) * (2 - xR - xB) * (c.k : ℝ) * c.L) := by
              rw [hd_eq]; congr 1; ring
      have hexp_sum : (c.ε ^ 3 / 40) * (c.k : ℝ) * c.L + (c.k : ℝ) * (c.L / 2) +
          (-(1 / 2 - c.ε ^ 3 / 40) * (2 - xR - xB) * (c.k : ℝ) * c.L) ≤
          (c.k : ℝ) * c.L * ((xR + xB - 1) / 2 + 3 * c.ε ^ 3 / 40) := by
        have hxR0 : 0 ≤ xR := by positivity
        have hxB0 : 0 ≤ xB := by positivity
        have hkL0 : 0 ≤ (c.k : ℝ) * c.L := mul_nonneg hkpos.le hc.hL_pos.le
        have hε3_0 : 0 ≤ c.ε ^ 3 / 40 := by have := hc.hε0; positivity
        have hfac : (c.ε ^ 3 / 40) * (c.k : ℝ) * c.L + (c.k : ℝ) * (c.L / 2) +
            (-(1 / 2 - c.ε ^ 3 / 40) * (2 - xR - xB) * (c.k : ℝ) * c.L) =
            (c.k : ℝ) * c.L * ((xR + xB - 1) / 2 + (3 - xR - xB) * (c.ε ^ 3 / 40)) := by ring
        rw [hfac]
        refine mul_le_mul_of_nonneg_left ?_ hkL0
        nlinarith only [hxR0, hxB0, hε3_0]
      calc (c.n.choose c.k : ℝ) *
            (Pr (unifW (Fin c.n) c.m) (fun π₁ => (I.image π₁).card ≤ ℓR) *
             Pr (unifW (Fin c.n) c.m) (fun π₂ => (I.image π₂).card ≤ ℓB))
          ≤ (Real.exp 1 * (c.n : ℝ) / (c.k : ℝ)) ^ c.k *
            ((Real.exp (c.k : ℝ) * ((c.k : ℝ) / (c.m : ℝ)) ^ (c.k - ℓR)) *
             (Real.exp (c.k : ℝ) * ((c.k : ℝ) / (c.m : ℝ)) ^ (c.k - ℓB))) := by
              refine mul_le_mul hch_n (mul_le_mul h1' h2' (Pr_nonneg hPpi1 _) (by positivity))
                (mul_nonneg (Pr_nonneg hPpi1 _) (Pr_nonneg hPpi1 _)) (by positivity)
        _ = (Real.exp 3) ^ c.k * ((c.n : ℝ) / (c.k : ℝ)) ^ c.k * ((c.k : ℝ) / (c.m : ℝ)) ^ d := by
              rw [← mul_assoc]; exact hcomb_ch
        _ ≤ Real.exp ((c.ε ^ 3 / 40) * (c.k : ℝ) * c.L) *
            Real.exp ((c.k : ℝ) * (c.L / 2)) *
            Real.exp (-(1 / 2 - c.ε ^ 3 / 40) * (2 - xR - xB) * (c.k : ℝ) * c.L) := by
              refine mul_le_mul (mul_le_mul he3_pow hnk_pow (by positivity) (Real.exp_pos _).le)
                hkm_pow (by positivity) (by positivity)
        _ = Real.exp ((c.ε ^ 3 / 40) * (c.k : ℝ) * c.L + (c.k : ℝ) * (c.L / 2) +
              (-(1 / 2 - c.ε ^ 3 / 40) * (2 - xR - xB) * (c.k : ℝ) * c.L)) := by
              rw [← Real.exp_add, ← Real.exp_add]
        _ ≤ Real.exp ((c.k : ℝ) * c.L * ((xR + xB - 1) / 2 + 3 * c.ε ^ 3 / 40)) :=
              Real.exp_le_exp.mpr hexp_sum
    -- Step 3: Combine via `three_case_exponent_bound`!
    have hxR0 : 0 ≤ xR := by positivity
    have hxB0 : 0 ≤ xB := by positivity
    have hxR1 : xR ≤ 1 := by dsimp only [xR]; rw [div_le_one hkpos]; exact_mod_cast hℓRk
    have hxB1 : xB ≤ 1 := by dsimp only [xB]; rw [div_le_one hkpos]; exact_mod_cast hℓBk
    have h3case := three_case_exponent_bound hc.hε0 hc.hε32 hκ_low hκ_high hκa hxR0 hxR1 hxB0 hxB1
    have hpk_eq : c.p * (c.k : ℝ) = (κ / 2) * c.L := by
      dsimp only [κ]; field_simp [hc.hL_pos.ne']
    have hRISI_exp : (c.ε ^ 3 / 20) * c.p * (c.k : ℝ) ^ 2 - c.p * c.fVal ℓR ℓB =
        (c.k : ℝ) * c.L * ((κ / 2) * (c.ε ^ 3 / 20 - F)) := by
      rw [hfVal_eq]
      have h1 : c.p * ((c.k : ℝ) ^ 2 * F) = (c.p * (c.k : ℝ)) * (c.k : ℝ) * F := by ring
      have h2 : (c.ε ^ 3 / 20) * c.p * (c.k : ℝ) ^ 2 = (c.p * (c.k : ℝ)) * (c.k : ℝ) * (c.ε ^ 3 / 20) := by ring
      rw [h1, h2, hpk_eq]; ring
    set E1 := (xR + xB - 1) / 2 + 3 * c.ε ^ 3 / 40
    set E2 := E1 + (κ / 2) * (c.ε ^ 3 / 20 - F)
    have hcomb_min : Real.exp ((c.k : ℝ) * c.L * E1) * B_RISI ≤ 2 * Real.exp ((c.k : ℝ) * c.L * min E1 E2) := by
      by_cases h12 : E1 ≤ E2
      · rw [min_eq_left h12]
        have hB1 : B_RISI ≤ 1 := min_le_left _ _
        have he0 : 0 < Real.exp ((c.k : ℝ) * c.L * E1) := Real.exp_pos _
        nlinarith only [hB1, he0]
      · push Not at h12
        rw [min_eq_right h12.le]
        have hB2 : B_RISI ≤ 2 * Real.exp ((c.k : ℝ) * c.L * ((κ / 2) * (c.ε ^ 3 / 20 - F))) := by
          rw [← hRISI_exp]; exact min_le_right _ _
        calc Real.exp ((c.k : ℝ) * c.L * E1) * B_RISI
            ≤ Real.exp ((c.k : ℝ) * c.L * E1) * (2 * Real.exp ((c.k : ℝ) * c.L * ((κ / 2) * (c.ε ^ 3 / 20 - F)))) :=
              mul_le_mul_of_nonneg_left hB2 (Real.exp_pos _).le
          _ = 2 * (Real.exp ((c.k : ℝ) * c.L * E1) * Real.exp ((c.k : ℝ) * c.L * ((κ / 2) * (c.ε ^ 3 / 20 - F)))) := by ring
          _ = 2 * Real.exp ((c.k : ℝ) * c.L * E2) := by rw [← Real.exp_add]; congr 2; dsimp only [E2]; ring
    calc (c.n.choose c.k : ℝ) * Pr (fullW c.n c.m c.p) (fun ω =>
            IndepI ω.1 ω.2 I ∧ GoodR c ω ∧ (I.image ω.1.1).card = ℓR ∧ (I.image ω.1.2).card = ℓB)
        ≤ (c.n.choose c.k : ℝ) *
            (Pr (piPairW c.n c.m) (fun π => (I.image π.1).card ≤ ℓR ∧ (I.image π.2).card ≤ ℓB) * B_RISI) :=
          mul_le_mul_of_nonneg_left hPr_split (Nat.cast_nonneg _)
      _ = ((c.n.choose c.k : ℝ) *
            Pr (piPairW c.n c.m) (fun π => (I.image π.1).card ≤ ℓR ∧ (I.image π.2).card ≤ ℓB)) * B_RISI := by ring
      _ ≤ Real.exp ((c.k : ℝ) * c.L * E1) * B_RISI := mul_le_mul_of_nonneg_right hPr_pi hBR_nn
      _ ≤ 2 * Real.exp ((c.k : ℝ) * c.L * min E1 E2) := hcomb_min
      _ ≤ 2 * Real.exp (-(c.ε ^ 2 / 8) * (c.k : ℝ) * c.L) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
          have hkL0 : 0 ≤ (c.k : ℝ) * c.L := mul_nonneg hkpos.le hc.hL_pos.le
          have : (c.k : ℝ) * c.L * min E1 E2 ≤ (c.k : ℝ) * c.L * (-(c.ε ^ 2 / 8)) :=
            mul_le_mul_of_nonneg_left h3case hkL0
          linarith
  -- Sum over all `ℓ ∈ pairs` (`pairs.card = k^2`)!
  have hpairs_card : (pairs.card : ℝ) = (c.k : ℝ) ^ 2 := by
    have h1 : pairs.card = c.k * c.k := by
      simp [pairs, Finset.card_product, Nat.card_Icc]
    rw [h1]; push_cast; ring
  calc (c.n.choose c.k : ℝ) * Pr (fullW c.n c.m c.p) (fun ω => IndepI ω.1 ω.2 I ∧ GoodR c ω)
      ≤ (c.n.choose c.k : ℝ) * Pr (fullW c.n c.m c.p) (fun ω => ∃ ℓ ∈ pairs,
          IndepI ω.1 ω.2 I ∧ GoodR c ω ∧ (I.image ω.1.1).card = ℓ.1 ∧ (I.image ω.1.2).card = ℓ.2) :=
        mul_le_mul_of_nonneg_left (Pr_mono hP himp) (Nat.cast_nonneg _)
    _ ≤ (c.n.choose c.k : ℝ) * ∑ ℓ ∈ pairs, Pr (fullW c.n c.m c.p) (fun ω =>
          IndepI ω.1 ω.2 I ∧ GoodR c ω ∧ (I.image ω.1.1).card = ℓ.1 ∧ (I.image ω.1.2).card = ℓ.2) :=
        mul_le_mul_of_nonneg_left (Pr_exists_le hP pairs _) (Nat.cast_nonneg _)
    _ = ∑ ℓ ∈ pairs, ((c.n.choose c.k : ℝ) * Pr (fullW c.n c.m c.p) (fun ω =>
          IndepI ω.1 ω.2 I ∧ GoodR c ω ∧ (I.image ω.1.1).card = ℓ.1 ∧ (I.image ω.1.2).card = ℓ.2)) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ _ℓ ∈ pairs, (2 * Real.exp (-(c.ε ^ 2 / 8) * (c.k : ℝ) * c.L)) := Finset.sum_le_sum hterm
    _ = 2 * (c.k : ℝ) ^ 2 * Real.exp (-(c.ε ^ 2 / 8) * (c.k : ℝ) * c.L) := by
        rw [Finset.sum_const, nsmul_eq_mul, hpairs_card]; ring
    _ < 1 / 4 := hc.h_final_sum

/-- Main probabilistic existence theorem: any `ValidCfg c` produces a triangle-free graph on `Fin c.n`
with no independent set of size `c.k` (hence every independent set has card `< c.k`). -/
lemma exists_good_graph_of_validCfg {c : Cfg} (hc : ValidCfg c) :
    ∃ G : SimpleGraph (Fin c.n), G.CliqueFree 3 ∧
      ∀ I : Finset (Fin c.n), G.IsIndepSet (↑I : Set (Fin c.n)) → I.card < c.k := by
  have hmpos : 0 < c.m := by have := hc.hm; omega
  have hP : IsProb (fullW c.n c.m c.p) := isProb_fullW hmpos hc.hp0 hc.hp1
  let badInd (ω : Omega c.n c.m) : Prop :=
    ∃ I ∈ (Finset.univ : Finset (Fin c.n)).powersetCard c.k, IndepI ω.1 ω.2 I
  have hbad_lt : Pr (fullW c.n c.m c.p) badInd < 1 := by
    have hsplit : Pr (fullW c.n c.m c.p) badInd ≤
        Pr (fullW c.n c.m c.p) (fun ω => ¬ GoodR c ω) +
        Pr (fullW c.n c.m c.p) (fun ω => ∃ I ∈ (Finset.univ : Finset (Fin c.n)).powersetCard c.k,
          IndepI ω.1 ω.2 I ∧ GoodR c ω) := by
      calc Pr (fullW c.n c.m c.p) badInd
          ≤ Pr (fullW c.n c.m c.p) (fun ω => (¬ GoodR c ω) ∨
              ∃ I ∈ (Finset.univ : Finset (Fin c.n)).powersetCard c.k, IndepI ω.1 ω.2 I ∧ GoodR c ω) := by
              refine Pr_mono hP fun ω ⟨I, hI, hInd⟩ => ?_
              by_cases hG : GoodR c ω
              · exact Or.inr ⟨I, hI, hInd, hG⟩
              · exact Or.inl hG
        _ ≤ _ := Pr_or_le hP _ _
    have hsum_ind : Pr (fullW c.n c.m c.p) (fun ω => ∃ I ∈ (Finset.univ : Finset (Fin c.n)).powersetCard c.k,
          IndepI ω.1 ω.2 I ∧ GoodR c ω) < 1 / 4 := by
      by_cases hne : ((Finset.univ : Finset (Fin c.n)).powersetCard c.k).Nonempty
      · have hch_pos : (0 : ℝ) < (c.n.choose c.k : ℝ) := by
          have : 0 < ((Finset.univ : Finset (Fin c.n)).powersetCard c.k).card := Finset.card_pos.mpr hne
          simpa [Finset.card_powersetCard] using (Nat.cast_pos.mpr this : (0 : ℝ) < _)
        have hle1 : Pr (fullW c.n c.m c.p) (fun ω => ∃ I ∈ (Finset.univ : Finset (Fin c.n)).powersetCard c.k,
              IndepI ω.1 ω.2 I ∧ GoodR c ω) ≤
            ∑ I ∈ (Finset.univ : Finset (Fin c.n)).powersetCard c.k,
              Pr (fullW c.n c.m c.p) (fun ω => IndepI ω.1 ω.2 I ∧ GoodR c ω) := Pr_exists_le hP _ _
        have hlt2 : ∑ I ∈ (Finset.univ : Finset (Fin c.n)).powersetCard c.k,
              Pr (fullW c.n c.m c.p) (fun ω => IndepI ω.1 ω.2 I ∧ GoodR c ω) <
            ∑ _I ∈ (Finset.univ : Finset (Fin c.n)).powersetCard c.k, ((1 / 4 : ℝ) / (c.n.choose c.k : ℝ)) := by
          refine Finset.sum_lt_sum_of_nonempty hne fun I hI => ?_
          rw [lt_div_iff₀ hch_pos, mul_comm]
          exact lem_RI_bound hc I (Finset.mem_powersetCard.mp hI).2
        have hsum_eq : ∑ _I ∈ (Finset.univ : Finset (Fin c.n)).powersetCard c.k,
            ((1 / 4 : ℝ) / (c.n.choose c.k : ℝ)) = 1 / 4 := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
          field_simp [hch_pos.ne']
        linarith
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne]
        have hzero : Pr (fullW c.n c.m c.p) (fun ω => ∃ I ∈ (∅ : Finset (Finset (Fin c.n))),
            IndepI ω.1 ω.2 I ∧ GoodR c ω) = 0 := by
          rw [Pr_congr (B := fun _ => False) (fun _ => by simp), Pr_false]
        rw [hzero]; norm_num
    linarith [Pr_not_goodR_lt_half hc]
  obtain ⟨ω, hnot_bad⟩ := exists_of_Pr_lt_one hP hbad_lt
  refine ⟨twoBitesGraph ω.1.1 ω.1.2 ω.2.1 ω.2.2, twoBitesGraph_cliqueFree_three _ _ _ _, ?_⟩
  intro I hInd
  by_contra hge
  push Not at hge
  obtain ⟨J, hJI, hJcard⟩ := Finset.exists_subset_card_eq hge
  apply hnot_bad
  refine ⟨J, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ J, hJcard⟩, ?_⟩
  intro u hu v hv huv hadj
  exact hInd (hJI hu) (hJI hv) huv hadj

end Lemma42AndMainProb

section AsymptoticInstantiation

/-- `exp (-4) ≤ 1 / 40`. -/
lemma exp_neg_four_le : Real.exp (-4 : ℝ) ≤ 1 / 40 := by
  have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he4 : (40 : ℝ) ≤ Real.exp 4 := by
    have h4 : Real.exp (4 : ℝ) = (Real.exp 1) ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h4]
    have h1 : (2.7 : ℝ) ^ 4 ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) he.le 4
    norm_num at h1 ⊢
    linarith
  rw [Real.exp_neg]
  exact (inv_le_comm₀ (Real.exp_pos 4) (by norm_num)).mpr (by linarith)

/-- Universal asymptotic domination: for any `b : ℕ`, `a > 0`, `C : ℝ`,
eventually `C * (Real.log n)^b ≤ n^a`. -/
lemma eventually_log_pow_le_rpow (b : ℕ) {a : ℝ} (ha : 0 < a) (C : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, C * (Real.log (n : ℝ)) ^ b ≤ (n : ℝ) ^ a := by
  cases b with
  | zero =>
    have hC1 : ∀ᶠ n : ℕ in Filter.atTop, C ≤ (n : ℝ) ^ a :=
      ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop C
    filter_upwards [hC1] with n hn
    simpa [pow_zero] using hn
  | succ b' =>
    set b := b' + 1
    have hbpos : (0 : ℝ) < (b : ℝ) := by positivity
    set α : ℝ := a / (2 * (b : ℝ))
    have hα : 0 < α := by positivity
    have hC1 : ∀ᶠ n : ℕ in Filter.atTop, max C 0 * (1 / α) ^ b ≤ (n : ℝ) ^ (a / 2) :=
      ((tendsto_rpow_atTop (by linarith : 0 < a / 2)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
    filter_upwards [hC1, Filter.eventually_ge_atTop 3] with n hCn hn3
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hL0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have hlog_le : Real.log (n : ℝ) ≤ (1 / α) * (n : ℝ) ^ α := by
      have h1 : α * Real.log (n : ℝ) ≤ Real.exp (α * Real.log (n : ℝ)) := by
        linarith [Real.add_one_le_exp (α * Real.log (n : ℝ))]
      have h2 : Real.exp (α * Real.log (n : ℝ)) = (n : ℝ) ^ α := by
        rw [Real.rpow_def_of_pos hnpos, mul_comm]
      rw [h2] at h1
      calc Real.log (n : ℝ) = (1 / α) * (α * Real.log (n : ℝ)) := by field_simp [hα.ne']
        _ ≤ (1 / α) * (n : ℝ) ^ α := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hpow_le : (Real.log (n : ℝ)) ^ b ≤ (1 / α) ^ b * (n : ℝ) ^ (a / 2) := by
      calc (Real.log (n : ℝ)) ^ b ≤ ((1 / α) * (n : ℝ) ^ α) ^ b := pow_le_pow_left₀ hL0 hlog_le b
        _ = (1 / α) ^ b * ((n : ℝ) ^ α) ^ b := mul_pow _ _ b
        _ = (1 / α) ^ b * (n : ℝ) ^ (α * (b : ℝ)) := by
            rw [← Real.rpow_natCast ((n : ℝ) ^ α) b, ← Real.rpow_mul hnpos.le]
        _ = (1 / α) ^ b * (n : ℝ) ^ (a / 2) := by congr 2; dsimp only [α]; field_simp [hbpos.ne']
    have hmul : C * (Real.log (n : ℝ)) ^ b ≤ (max C 0 * (1 / α) ^ b) * (n : ℝ) ^ (a / 2) := by
      calc C * (Real.log (n : ℝ)) ^ b ≤ max C 0 * (Real.log (n : ℝ)) ^ b :=
            mul_le_mul_of_nonneg_right (le_max_left C 0) (pow_nonneg hL0 b)
        _ ≤ max C 0 * ((1 / α) ^ b * (n : ℝ) ^ (a / 2)) := mul_le_mul_of_nonneg_left hpow_le (le_max_right C 0)
        _ = (max C 0 * (1 / α) ^ b) * (n : ℝ) ^ (a / 2) := by ring
    have hadd : (n : ℝ) ^ (a / 2) * (n : ℝ) ^ (a / 2) = (n : ℝ) ^ a := by
      rw [← Real.rpow_add hnpos]; congr 1; ring
    have hstep2 : (max C 0 * (1 / α) ^ b) * (n : ℝ) ^ (a / 2) ≤ (n : ℝ) ^ (a / 2) * (n : ℝ) ^ (a / 2) :=
      mul_le_mul_of_nonneg_right hCn (Real.rpow_nonneg hnpos.le _)
    linarith

/-- Concrete `Cfg` constructor for `ε > 0` and `n : ℕ`. -/
noncomputable def mkCfg (ε : ℝ) (n : ℕ) : Cfg :=
  let L := Real.log (n : ℝ)
  let r := ε ^ 3 / 100
  let ε₁ := r ^ 2
  let ε₂ := ε₁ / 100
  let m := ⌊(n : ℝ) / L ^ 2⌋₊
  let p := (1 / 2) * Real.sqrt (L / (n : ℝ))
  let S := Real.sqrt ((n : ℝ) * L)
  let k := ⌊(1 + ε) * S⌋₊
  let Fmax := ⌈(1 + ε₂ / 3) * ((n : ℝ) / (m : ℝ))⌉₊
  let Dmax := ⌈(1 + ε₂ / 3) * (((m - 1 : ℕ) : ℝ) * p)⌉₊
  let Nmax := ⌈(1 + ε₂) * (p * (n : ℝ))⌉₊
  let t_codeg := ⌈10 * L⌉₊
  let t_cross := ⌈10 * L⌉₊
  let t_proj := ⌈20 * L ^ 3⌉₊
  let t₁ := Real.sqrt (n : ℝ)
  let t₂ := (n : ℝ) ^ ((1 : ℝ) / 4 + ε)
  let t₃ := (n : ℝ) ^ (2 * ε)
  let L_cap := ⌈2 * (k : ℝ) / t₂⌉₊
  let H_cap := ⌈3 * Real.sqrt L⌉₊
  let Ylim := (k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε)
  let b₀ := ⌈2 * Ylim / t₃⌉₊
  let t_med := ⌊Ylim / (2 * (Fmax : ℝ))⌋₊
  let t_small := (ε₁ / 2) * (k : ℝ) ^ 2
  let Fthr := L
  let Nthr := t₂ / L
  let M₁ := ⌊3 * ε₁ * (k : ℝ) ^ 2⌋₊
  { n, m, k, Fmax, Dmax, Nmax, t_codeg, t_cross, t_proj, L_cap, H_cap, b₀, t_med, M₁,
    ε, r, ε₁, ε₂, p, t₁, t₂, t₃, Ylim, t_small, Fthr, Nthr }

-- Fast modular split of `eventually_validCfg` (0 bare `nlinarith`, default 200k heartbeats!).

/-- The 15 asymptotic inequalities holding eventually for `n` given `0 < ε ≤ 1 / 32`. -/
structure AsymptoticEnv (ε : ℝ) (n : ℕ) : Prop where
  hn : 100 ≤ n
  hL_big :
    let r := ε ^ 3 / 100
    let ε₁ := r ^ 2
    let ε₂ := ε₁ / 100
    max (max (max 100 (1000 / ε₂ ^ 2)) (max (100 / ε₁ ^ 2) (200 / ε ^ 3))) (100 / ε ^ 2) ≤ Real.log (n : ℝ)
  hm_big : 100 * (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) ^ (1 : ℝ)
  hkm_big : 10 * (Real.log (n : ℝ)) ^ 3 ≤ (n : ℝ) ^ ((1 : ℝ) / 2)
  hdeg_big : (3000 / ((ε ^ 3 / 100) ^ 2 / 100) ^ 2) * (Real.log (n : ℝ)) ^ 3 ≤ (n : ℝ) ^ ((1 : ℝ) / 2)
  hS1_big : (100 / (ε ^ 2 * (ε ^ 3 / 100) ^ 2)) * (Real.log (n : ℝ)) ^ 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 2)
  hLcap_big : 2000 * (Real.log (n : ℝ)) ^ 4 ≤ (n : ℝ) ^ (2 * ε)
  hHcap_big : (10000 / (ε ^ 3 / 100) ^ 2) * (Real.log (n : ℝ)) ^ 4 ≤ (n : ℝ) ^ ((1 : ℝ) / 2)
  hF2_big : (200 / (ε ^ 3 / 100) ^ 2) * (Real.log (n : ℝ)) ^ 3 ≤ (n : ℝ) ^ ((1 : ℝ) / 4 - ε)
  hmed1_big : 400 * (Real.log (n : ℝ)) ^ 3 ≤ (n : ℝ) ^ (2 * ε)
  hmed2_big : 20 * (Real.log (n : ℝ)) ^ 3 ≤ (n : ℝ) ^ ((1 : ℝ) / 4 + 3 * ε)
  hsm1_big : (20 / (ε ^ 3 / 100) ^ 2) * (Real.log (n : ℝ)) ^ 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 2 - 4 * ε)
  hsm2_big : (20 / ((ε ^ 3 / 100) ^ 2) ^ 2) * (Real.log (n : ℝ)) ^ 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 2 - 8 * ε)
  hkm_exp_big : 4 * (Real.log (n : ℝ)) ^ 3 ≤ (n : ℝ) ^ (ε ^ 3 / 40)
  hq1_big : (30 / (ε ^ 3 / 100) ^ 2) * (Real.log (n : ℝ)) ^ 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 4 + ε)

lemma eventually_asymptoticEnv {ε : ℝ} (hε0 : 0 < ε) (hε32 : ε ≤ 1 / 32) :
    ∀ᶠ n : ℕ in Filter.atTop, AsymptoticEnv ε n := by
  set r : ℝ := ε ^ 3 / 100
  set ε₁ : ℝ := r ^ 2
  set ε₂ : ℝ := ε₁ / 100
  have htlog : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [Filter.eventually_ge_atTop 100,
     htlog.eventually_ge_atTop (max (max (max 100 (1000 / ε₂ ^ 2)) (max (100 / ε₁ ^ 2) (200 / ε ^ 3))) (100 / ε ^ 2)),
     eventually_log_pow_le_rpow 2 (a := (1 : ℝ)) (by norm_num) 100,
     eventually_log_pow_le_rpow 3 (a := (1 : ℝ) / 2) (by norm_num) 10,
     eventually_log_pow_le_rpow 3 (a := (1 : ℝ) / 2) (by norm_num) (3000 / ε₂ ^ 2),
     eventually_log_pow_le_rpow 0 (a := (1 : ℝ) / 2) (by norm_num) (100 / (ε ^ 2 * ε₁)),
     eventually_log_pow_le_rpow 4 (a := 2 * ε) (by positivity) 2000,
     eventually_log_pow_le_rpow 4 (a := (1 : ℝ) / 2) (by norm_num) (10000 / ε₁),
     eventually_log_pow_le_rpow 3 (a := (1 : ℝ) / 4 - ε) (by linarith) (200 / ε₁),
     eventually_log_pow_le_rpow 3 (a := 2 * ε) (by positivity) 400,
     eventually_log_pow_le_rpow 3 (a := (1 : ℝ) / 4 + 3 * ε) (by positivity) 20,
     eventually_log_pow_le_rpow 0 (a := (1 : ℝ) / 2 - 4 * ε) (by linarith) (20 / ε₁),
     eventually_log_pow_le_rpow 0 (a := (1 : ℝ) / 2 - 8 * ε) (by linarith) (20 / ε₁ ^ 2),
     eventually_log_pow_le_rpow 3 (a := ε ^ 3 / 40) (by positivity) 4,
     eventually_log_pow_le_rpow 1 (a := (1 : ℝ) / 4 + ε) (by positivity) (30 / ε₁)] with n
    hn hL_big hm_big hkm_big hdeg_big hS1_big hLcap_big hHcap_big hF2_big hmed1_big hmed2_big
    hsm1_big hsm2_big hkm_exp_big hq1_big
  exact ⟨hn, hL_big, hm_big, hkm_big, hdeg_big, hS1_big, hLcap_big, hHcap_big, hF2_big,
    hmed1_big, hmed2_big, hsm1_big, hsm2_big, hkm_exp_big, hq1_big⟩

/-- Derived basic bounds for `c = mkCfg ε n` (kept inside a structure so tactics never scan all 40 at once!). -/
structure MkCfgBase (ε : ℝ) (n : ℕ) : Prop where
  hr_pos : 0 < (mkCfg ε n).r
  hr_le : (mkCfg ε n).r ≤ 1
  hε₁_pos : 0 < (mkCfg ε n).ε₁
  hε₁_le : (mkCfg ε n).ε₁ ≤ 1
  hε₂_pos : 0 < (mkCfg ε n).ε₂
  hε₂_le : (mkCfg ε n).ε₂ ≤ 1
  hnpos : (0 : ℝ) < (n : ℝ)
  hn100 : (100 : ℝ) ≤ (n : ℝ)
  hL100 : 100 ≤ Real.log (n : ℝ)
  hL_ε₂ : 1000 / (mkCfg ε n).ε₂ ^ 2 ≤ Real.log (n : ℝ)
  hL_ε₁ : 100 / (mkCfg ε n).ε₁ ^ 2 ≤ Real.log (n : ℝ)
  hL_ε3 : 200 / ε ^ 3 ≤ Real.log (n : ℝ)
  hL_ε2 : 100 / ε ^ 2 ≤ Real.log (n : ℝ)
  hLpos : 0 < Real.log (n : ℝ)
  hsqrtL_ge1 : 1 ≤ Real.sqrt (Real.log (n : ℝ))
  hsqrtL_leL : Real.sqrt (Real.log (n : ℝ)) ≤ Real.log (n : ℝ)
  hsqrtn_pos : 0 < (n : ℝ) ^ ((1 : ℝ) / 2)
  hS_eq : Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) = (n : ℝ) ^ ((1 : ℝ) / 2) * Real.sqrt (Real.log (n : ℝ))
  hS_ge_sqrtn : (n : ℝ) ^ ((1 : ℝ) / 2) ≤ Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
  hS_pos : 0 < Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
  hsqrtn_big : 100 / (ε ^ 2 * (mkCfg ε n).ε₁) ≤ (n : ℝ) ^ ((1 : ℝ) / 2)
  hm_le : ((mkCfg ε n).m : ℝ) ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 2
  hm_ge : (1 / 2) * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) ≤ ((mkCfg ε n).m : ℝ)
  hm_nat : 50 ≤ (mkCfg ε n).m
  hm_posR : (0 : ℝ) < ((mkCfg ε n).m : ℝ)
  hm1_ge : (1 / 4) * ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) ≤ (((mkCfg ε n).m - 1 : ℕ) : ℝ)
  hnm_ge : (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) / ((mkCfg ε n).m : ℝ)
  hnm_le : (n : ℝ) / ((mkCfg ε n).m : ℝ) ≤ 2 * (Real.log (n : ℝ)) ^ 2
  hp0 : 0 ≤ (mkCfg ε n).p
  hp_sq : (mkCfg ε n).p ^ 2 * (n : ℝ) = Real.log (n : ℝ) / 4
  hp_le1 : (mkCfg ε n).p ≤ 1
  hpS_eq : (mkCfg ε n).p * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) = Real.log (n : ℝ) / 2
  hpn_eq : (mkCfg ε n).p * (n : ℝ) = Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 2
  hk_le : ((mkCfg ε n).k : ℝ) ≤ (1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
  hk_low : (1 + 7 * ε / 8) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ ((mkCfg ε n).k : ℝ)
  hk_ge_S : Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ ((mkCfg ε n).k : ℝ)
  hk_le_2S : ((mkCfg ε n).k : ℝ) ≤ 2 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
  hk_ge_sqrtn : (n : ℝ) ^ ((1 : ℝ) / 2) ≤ ((mkCfg ε n).k : ℝ)
  hk_ge100 : (100 : ℝ) ≤ ((mkCfg ε n).k : ℝ)
  hk_posR : (0 : ℝ) < ((mkCfg ε n).k : ℝ)
  hk1 : 1 ≤ (mkCfg ε n).k
  hkm : (mkCfg ε n).k ≤ (mkCfg ε n).m
  hFmax_ge : (1 + (mkCfg ε n).ε₂ / 3) * ((n : ℝ) / ((mkCfg ε n).m : ℝ)) ≤ ((mkCfg ε n).Fmax : ℝ)
  hFmax_le : ((mkCfg ε n).Fmax : ℝ) ≤ 3 * (Real.log (n : ℝ)) ^ 2
  hm1p_le : (((mkCfg ε n).m - 1 : ℕ) : ℝ) * (mkCfg ε n).p ≤
    (n : ℝ) ^ ((1 : ℝ) / 2) / (2 * Real.log (n : ℝ) * Real.sqrt (Real.log (n : ℝ)))
  hm1p_ge : (n : ℝ) ^ ((1 : ℝ) / 2) / (8 * (Real.log (n : ℝ)) ^ 2) ≤
    (((mkCfg ε n).m - 1 : ℕ) : ℝ) * (mkCfg ε n).p
  hDmax_ge : (1 + (mkCfg ε n).ε₂ / 3) * ((((mkCfg ε n).m - 1 : ℕ) : ℝ) * (mkCfg ε n).p) ≤ ((mkCfg ε n).Dmax : ℝ)
  hDmax_le : ((mkCfg ε n).Dmax : ℝ) ≤
    (n : ℝ) ^ ((1 : ℝ) / 2) / (Real.log (n : ℝ) * Real.sqrt (Real.log (n : ℝ)))
  hNmax_ge : (1 + (mkCfg ε n).ε₂) * ((mkCfg ε n).p * (n : ℝ)) ≤ ((mkCfg ε n).Nmax : ℝ)
  hNmax_le : ((mkCfg ε n).Nmax : ℝ) ≤ Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
  ht_codeg_ge : 10 * Real.log (n : ℝ) ≤ ((mkCfg ε n).t_codeg : ℝ)
  ht_codeg_le : ((mkCfg ε n).t_codeg : ℝ) ≤ 11 * Real.log (n : ℝ)
  ht_codeg1 : 1 ≤ (mkCfg ε n).t_codeg
  ht_cross_ge : 10 * Real.log (n : ℝ) ≤ ((mkCfg ε n).t_cross : ℝ)
  ht_cross1 : 1 ≤ (mkCfg ε n).t_cross
  ht_proj_ge : 20 * (Real.log (n : ℝ)) ^ 3 ≤ ((mkCfg ε n).t_proj : ℝ)
  ht_proj_le : ((mkCfg ε n).t_proj : ℝ) ≤ 21 * (Real.log (n : ℝ)) ^ 3
  ht_proj1 : 1 ≤ (mkCfg ε n).t_proj
  hSmax_le : ((mkCfg ε n).Smax : ℝ) ≤ 33 * (Real.log (n : ℝ)) ^ 3
  hCint_le : ((mkCfg ε n).C_int : ℝ) ≤ 33 * (Real.log (n : ℝ)) ^ 3
  hCproj_le : ((mkCfg ε n).C_proj : ℝ) ≤ 54 * (Real.log (n : ℝ)) ^ 3
  he_lt3 : Real.exp 1 < 3
  hexpL : Real.exp (Real.log (n : ℝ)) = (n : ℝ)
  hm_le_n : ((mkCfg ε n).m : ℝ) ≤ (n : ℝ)
  h2m_exp : ((mkCfg ε n).m : ℝ) * (2 * Real.exp (-10 * Real.log (n : ℝ))) ≤ 1 / 40
  hm2_exp : ((mkCfg ε n).m : ℝ) ^ 2 * Real.exp (-10 * Real.log (n : ℝ)) ≤ 1 / 40

lemma mkCfgBase_of_env {ε : ℝ} {n : ℕ} (hε0 : 0 < ε) (hε32 : ε ≤ 1 / 32)
    (he : AsymptoticEnv ε n) : MkCfgBase ε n := by
  set c := mkCfg ε n
  set L := Real.log (n : ℝ)
  set S := Real.sqrt ((n : ℝ) * L)
  have hr_pos : 0 < c.r := by dsimp only [c, mkCfg]; positivity
  have hr_le : c.r ≤ 1 := by
    have h1 : ε ^ 3 ≤ 1 := pow_le_one₀ hε0.le (by linarith only [hε32])
    dsimp only [c, mkCfg]; linarith only [h1]
  have hε₁_pos : 0 < c.ε₁ := sq_pos_of_pos hr_pos
  have hε₁_le : c.ε₁ ≤ 1 := by dsimp only [c, mkCfg] at hr_pos hr_le ⊢; nlinarith only [hr_pos, hr_le]
  have hε₂_pos : 0 < c.ε₂ := by dsimp only [c, mkCfg] at hε₁_pos ⊢; linarith only [hε₁_pos]
  have hε₂_le : c.ε₂ ≤ 1 := by dsimp only [c, mkCfg] at hε₁_le ⊢; linarith only [hε₁_le]
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by have := he.hn; omega : 0 < n)
  have hn100 : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast he.hn
  have hL_big' : max (max (max 100 (1000 / c.ε₂ ^ 2)) (max (100 / c.ε₁ ^ 2) (200 / ε ^ 3))) (100 / ε ^ 2) ≤ L :=
    he.hL_big
  have hL100 : 100 ≤ L := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hL_big'
  have hL_ε₂ : 1000 / c.ε₂ ^ 2 ≤ L := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hL_big'
  have hL_ε₁ : 100 / c.ε₁ ^ 2 ≤ L := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hL_big'
  have hL_ε3 : 200 / ε ^ 3 ≤ L := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hL_big'
  have hL_ε2 : 100 / ε ^ 2 ≤ L := le_trans (le_max_right _ _) hL_big'
  have hLpos : 0 < L := by linarith only [hL100]
  have hsqrtL_ge1 : 1 ≤ Real.sqrt L := by rw [Real.le_sqrt (by norm_num) hLpos.le]; linarith only [hL100]
  have hsqrtL_leL : Real.sqrt L ≤ L := by rw [Real.sqrt_le_iff]; exact ⟨hLpos.le, by nlinarith only [hL100]⟩
  have hsqrtn_eq : Real.sqrt (n : ℝ) = (n : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (n : ℝ)
  have hS_eq : S = (n : ℝ) ^ ((1 : ℝ) / 2) * Real.sqrt L := by
    dsimp only [S]; rw [Real.sqrt_mul hnpos.le, hsqrtn_eq]
  have hsqrtn_pos : 0 < (n : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hnpos _
  have hS_ge_sqrtn : (n : ℝ) ^ ((1 : ℝ) / 2) ≤ S := by rw [hS_eq]; nlinarith only [hsqrtn_pos, hsqrtL_ge1]
  have hS_pos : 0 < S := lt_of_lt_of_le hsqrtn_pos hS_ge_sqrtn
  have hsqrtn_big : 100 / (ε ^ 2 * c.ε₁) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := by
    have h0 : 100 / (ε ^ 2 * c.ε₁) * L ^ 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := he.hS1_big
    simpa [pow_zero] using h0
  have hm_100 : 100 * L ^ 2 ≤ (n : ℝ) := by simpa [Real.rpow_one] using he.hm_big
  have hm_div_ge : 100 ≤ (n : ℝ) / L ^ 2 := (le_div_iff₀ (sq_pos_of_pos hLpos)).mpr hm_100
  have hm_le : (c.m : ℝ) ≤ (n : ℝ) / L ^ 2 := Nat.floor_le (by positivity)
  have hm_ge : (1 / 2) * ((n : ℝ) / L ^ 2) ≤ (c.m : ℝ) := by
    have h1 : (n : ℝ) / L ^ 2 - 1 < (c.m : ℝ) := Nat.sub_one_lt_floor _
    linarith only [h1, hm_div_ge]
  have hm_ge50 : (50 : ℝ) ≤ (c.m : ℝ) := by linarith only [hm_ge, hm_div_ge]
  have hm_nat : 50 ≤ c.m := by exact_mod_cast hm_ge50
  have hm_posR : (0 : ℝ) < (c.m : ℝ) := by linarith only [hm_ge50]
  have hm1_ge : (1 / 4) * ((n : ℝ) / L ^ 2) ≤ ((c.m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ c.m)]; push_cast; linarith only [hm_ge, hm_div_ge]
  have hnm_ge : L ^ 2 ≤ (n : ℝ) / (c.m : ℝ) := by
    rw [le_div_iff₀ hm_posR]
    have h1 : (c.m : ℝ) * L ^ 2 ≤ (n : ℝ) / L ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_right hm_le (sq_nonneg L)
    rw [div_mul_cancel₀ _ (sq_pos_of_pos hLpos).ne'] at h1
    linarith only [h1]
  have hnm_le : (n : ℝ) / (c.m : ℝ) ≤ 2 * L ^ 2 := by
    rw [div_le_iff₀ hm_posR]
    have h2 : (1 / 2) * ((n : ℝ) / L ^ 2) * (2 * L ^ 2) ≤ (c.m : ℝ) * (2 * L ^ 2) :=
      mul_le_mul_of_nonneg_right hm_ge (by positivity)
    linarith only [h2, show (1 / 2) * ((n : ℝ) / L ^ 2) * (2 * L ^ 2) = (n : ℝ) by field_simp [hLpos.ne']]
  have hp0 : 0 ≤ c.p := by dsimp only [c, mkCfg]; positivity
  have hp_sq : c.p ^ 2 * (n : ℝ) = L / 4 := by
    dsimp only [c, mkCfg]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp [hnpos.ne']; ring
  have hp_le1 : c.p ≤ 1 := by
    have h1 : c.p ^ 2 ≤ 1 := by
      have hLn : L ≤ (n : ℝ) := by nlinarith only [hm_100, hL100]
      have hp2 : c.p ^ 2 = L / (4 * (n : ℝ)) := by
        have := hp_sq; field_simp [hnpos.ne'] at this ⊢; linarith only [this]
      rw [hp2, div_le_one (by positivity)]; linarith only [hLn, hnpos]
    nlinarith only [h1, hp0]
  have hpS_eq : c.p * S = L / 2 := by
    dsimp only [c, mkCfg, S]
    have h1 : Real.sqrt (L / (n : ℝ)) * Real.sqrt ((n : ℝ) * L) = L := by
      rw [← Real.sqrt_mul (by positivity)]
      have h2 : L / (n : ℝ) * ((n : ℝ) * L) = L ^ 2 := by field_simp [hnpos.ne']
      rw [h2, Real.sqrt_sq hLpos.le]
    linarith only [h1, show (1 / 2) * Real.sqrt (L / (n : ℝ)) * Real.sqrt ((n : ℝ) * L) =
      (1 / 2) * (Real.sqrt (L / (n : ℝ)) * Real.sqrt ((n : ℝ) * L)) by ring]
  have hpn_eq : c.p * (n : ℝ) = S / 2 := by
    dsimp only [c, mkCfg, S]
    have h1 : Real.sqrt (L / (n : ℝ)) * (n : ℝ) = Real.sqrt ((n : ℝ) * L) := by
      have h2 : (n : ℝ) = Real.sqrt ((n : ℝ) ^ 2) := (Real.sqrt_sq hnpos.le).symm
      conv_lhs => arg 2; rw [h2]
      rw [← Real.sqrt_mul (by positivity)]
      congr 1; field_simp [hnpos.ne']
    linarith only [h1, show (1 / 2) * Real.sqrt (L / (n : ℝ)) * (n : ℝ) =
      (1 / 2) * (Real.sqrt (L / (n : ℝ)) * (n : ℝ)) by ring]
  have hk_le : (c.k : ℝ) ≤ (1 + ε) * S := Nat.floor_le (by positivity)
  have hk_low : (1 + 7 * ε / 8) * S ≤ (c.k : ℝ) := by
    have h1 : (1 + ε) * S - 1 < (c.k : ℝ) := Nat.sub_one_lt_floor _
    have hS_ge_eps : 8 / ε ≤ S := by
      have h2 : 8 / ε ≤ 100 / (ε ^ 2 * c.ε₁) := by
        rw [div_le_div_iff₀ hε0 (by positivity)]
        have h3 : ε * c.ε₁ ≤ 1 := by nlinarith only [hε0, hε32, hε₁_pos, hε₁_le]
        nlinarith only [h3, hε0]
      linarith only [h2, hsqrtn_big, hS_ge_sqrtn]
    have h1_le : 1 ≤ (ε / 8) * S := by have := (div_le_iff₀ hε0).mp hS_ge_eps; linarith only [this]
    linarith only [h1, h1_le]
  have hk_ge_S : S ≤ (c.k : ℝ) := by nlinarith only [hk_low, hε0, hS_pos]
  have hk_le_2S : (c.k : ℝ) ≤ 2 * S := by nlinarith only [hk_le, hε32, hS_pos]
  have hk_ge_sqrtn : (n : ℝ) ^ ((1 : ℝ) / 2) ≤ (c.k : ℝ) := hS_ge_sqrtn.trans hk_ge_S
  have hk_ge100 : (100 : ℝ) ≤ (c.k : ℝ) := by
    have h1 : ε ^ 2 * c.ε₁ ≤ 1 := by
      have : ε ^ 2 ≤ 1 := by nlinarith only [hε0, hε32]
      nlinarith only [this, hε₁_pos, hε₁_le]
    have h2 : 100 ≤ 100 / (ε ^ 2 * c.ε₁) := (le_div_iff₀ (by positivity)).mpr (by linarith only [h1])
    linarith only [h2, hsqrtn_big, hk_ge_sqrtn]
  have hk_posR : (0 : ℝ) < (c.k : ℝ) := by linarith only [hk_ge100]
  have hk1 : 1 ≤ c.k := by exact_mod_cast (by linarith only [hk_ge100] : (1 : ℝ) ≤ (c.k : ℝ))
  have hkm : c.k ≤ c.m := by
    have h1 : (c.k : ℝ) ≤ (c.m : ℝ) := by
      have hsqn : (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) = (n : ℝ) := by
        rw [← Real.rpow_add hnpos]; norm_num
      have h2 : 2 * (n : ℝ) ^ ((1 : ℝ) / 2) * L ^ 3 ≤ (n : ℝ) / 2 := by
        have h3 := mul_le_mul_of_nonneg_left he.hkm_big hsqrtn_pos.le
        linarith only [h3, hsqn, show (n : ℝ) ^ ((1 : ℝ) / 2) * (10 * L ^ 3) =
          10 * (n : ℝ) ^ ((1 : ℝ) / 2) * L ^ 3 by ring,
          show 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) * L ^ 3 by positivity]
      have h4 : (c.k : ℝ) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 2) * L := by
        rw [hS_eq] at hk_le_2S; nlinarith only [hk_le_2S, hsqrtL_leL, hsqrtn_pos]
      have h5 : (c.k : ℝ) * L ^ 2 ≤ (n : ℝ) / 2 := by
        have := mul_le_mul_of_nonneg_right h4 (sq_nonneg L)
        linarith only [this, h2, show 2 * (n : ℝ) ^ ((1 : ℝ) / 2) * L * L ^ 2 = 2 * (n : ℝ) ^ ((1 : ℝ) / 2) * L ^ 3 by ring]
      have h6 : (c.k : ℝ) ≤ (1 / 2) * ((n : ℝ) / L ^ 2) := by
        rw [show (1 / 2) * ((n : ℝ) / L ^ 2) = ((n : ℝ) / 2) / L ^ 2 by ring, le_div_iff₀ (sq_pos_of_pos hLpos)]
        exact h5
      linarith only [h6, hm_ge]
    exact_mod_cast h1
  have hFmax_ge : (1 + c.ε₂ / 3) * ((n : ℝ) / (c.m : ℝ)) ≤ (c.Fmax : ℝ) := Nat.le_ceil _
  have hFmax_le : (c.Fmax : ℝ) ≤ 3 * L ^ 2 := by
    have h1 : (c.Fmax : ℝ) < (1 + c.ε₂ / 3) * ((n : ℝ) / (c.m : ℝ)) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h2 : (1 + c.ε₂ / 3) * ((n : ℝ) / (c.m : ℝ)) ≤ (4 / 3) * (2 * L ^ 2) :=
      mul_le_mul (by linarith only [hε₂_le]) hnm_le (by positivity) (by norm_num)
    nlinarith only [h1, h2, hL100]
  have hm1p_le : ((c.m - 1 : ℕ) : ℝ) * c.p ≤ (n : ℝ) ^ ((1 : ℝ) / 2) / (2 * L * Real.sqrt L) := by
    have hm1 : ((c.m - 1 : ℕ) : ℝ) ≤ (c.m : ℝ) := by exact_mod_cast Nat.sub_le c.m 1
    calc ((c.m - 1 : ℕ) : ℝ) * c.p ≤ (c.m : ℝ) * c.p := mul_le_mul_of_nonneg_right hm1 hp0
      _ ≤ ((n : ℝ) / L ^ 2) * c.p := mul_le_mul_of_nonneg_right hm_le hp0
      _ = (c.p * (n : ℝ)) / L ^ 2 := by ring
      _ = S / (2 * L ^ 2) := by rw [hpn_eq]; ring
      _ = (n : ℝ) ^ ((1 : ℝ) / 2) / (2 * L * Real.sqrt L) := by
          rw [hS_eq]
          have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLpos.le
          field_simp [hLpos.ne', (Real.sqrt_pos.mpr hLpos).ne']
          nlinarith only [hsq]
  have hm1p_ge : (n : ℝ) ^ ((1 : ℝ) / 2) / (8 * L ^ 2) ≤ ((c.m - 1 : ℕ) : ℝ) * c.p := by
    calc (n : ℝ) ^ ((1 : ℝ) / 2) / (8 * L ^ 2)
        ≤ S / (8 * L ^ 2) := div_le_div_of_nonneg_right hS_ge_sqrtn (by positivity)
      _ = (1 / 4) * ((n : ℝ) / L ^ 2) * c.p := by
          have : (1 / 4) * ((n : ℝ) / L ^ 2) * c.p = (c.p * (n : ℝ)) / (4 * L ^ 2) := by ring
          rw [this, hpn_eq]; ring
      _ ≤ ((c.m - 1 : ℕ) : ℝ) * c.p := mul_le_mul_of_nonneg_right hm1_ge hp0
  have hDmax_ge : (1 + c.ε₂ / 3) * (((c.m - 1 : ℕ) : ℝ) * c.p) ≤ (c.Dmax : ℝ) := Nat.le_ceil _
  have hDmax_le : (c.Dmax : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) / (L * Real.sqrt L) := by
    have h1 : (c.Dmax : ℝ) < (1 + c.ε₂ / 3) * (((c.m - 1 : ℕ) : ℝ) * c.p) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h2 : (1 + c.ε₂ / 3) * (((c.m - 1 : ℕ) : ℝ) * c.p) ≤ (2 / 3) * ((n : ℝ) ^ ((1 : ℝ) / 2) / (L * Real.sqrt L)) := by
      have h3 := mul_le_mul (by linarith only [hε₂_le] : 1 + c.ε₂ / 3 ≤ 4 / 3) hm1p_le (by positivity) (by norm_num)
      linarith only [h3, show (4 / 3) * ((n : ℝ) ^ ((1 : ℝ) / 2) / (2 * L * Real.sqrt L)) =
        (2 / 3) * ((n : ℝ) ^ ((1 : ℝ) / 2) / (L * Real.sqrt L)) by ring]
    have h3 : 1 ≤ (1 / 3) * ((n : ℝ) ^ ((1 : ℝ) / 2) / (L * Real.sqrt L)) := by
      rw [show (1 / 3) * ((n : ℝ) ^ ((1 : ℝ) / 2) / (L * Real.sqrt L)) =
        (n : ℝ) ^ ((1 : ℝ) / 2) / (3 * L * Real.sqrt L) by ring, one_le_div (by positivity)]
      have h4 : 3 * L * Real.sqrt L ≤ 10 * L ^ 3 := by
        have : L * Real.sqrt L ≤ L ^ 2 := by nlinarith only [hLpos, hsqrtL_leL]
        nlinarith only [this, hL100]
      linarith only [h4, he.hkm_big]
    linarith only [h1, h2, h3]
  have hNmax_ge : (1 + c.ε₂) * (c.p * (n : ℝ)) ≤ (c.Nmax : ℝ) := Nat.le_ceil _
  have hNmax_le : (c.Nmax : ℝ) ≤ S := by
    have h1 : (c.Nmax : ℝ) < (1 + c.ε₂) * (c.p * (n : ℝ)) + 1 := Nat.ceil_lt_add_one (by positivity)
    rw [hpn_eq] at h1
    have hε₂_small : c.ε₂ ≤ 1 / 100 := by dsimp only [c, mkCfg] at hε₁_le ⊢; linarith only [hε₁_le]
    have hS4 : 4 ≤ S := by linarith only [hk_ge100, hk_le_2S]
    nlinarith only [h1, hε₂_small, hS4]
  have ht_codeg_ge : 10 * L ≤ (c.t_codeg : ℝ) := Nat.le_ceil _
  have ht_codeg_le : (c.t_codeg : ℝ) ≤ 11 * L := by
    have h1 : (c.t_codeg : ℝ) < 10 * L + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith only [h1, hL100]
  have ht_codeg1 : 1 ≤ c.t_codeg := by exact_mod_cast (by linarith only [ht_codeg_ge, hL100] : (1 : ℝ) ≤ (c.t_codeg : ℝ))
  have ht_cross_ge : 10 * L ≤ (c.t_cross : ℝ) := Nat.le_ceil _
  have ht_cross1 : 1 ≤ c.t_cross := by exact_mod_cast (by linarith only [ht_cross_ge, hL100] : (1 : ℝ) ≤ (c.t_cross : ℝ))
  have ht_proj_ge : 20 * L ^ 3 ≤ (c.t_proj : ℝ) := Nat.le_ceil _
  have hL3_ge_L : L ≤ L ^ 3 := by
    have hL2 : L ≤ L ^ 2 := by nlinarith only [hL100]
    nlinarith only [hL2, hL100]
  have ht_proj_le : (c.t_proj : ℝ) ≤ 21 * L ^ 3 := by
    have h1 : (c.t_proj : ℝ) < 20 * L ^ 3 + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith only [h1, hL3_ge_L, hL100]
  have ht_proj1 : 1 ≤ c.t_proj := by
    exact_mod_cast (by linarith only [ht_proj_ge, hL3_ge_L, hL100] : (1 : ℝ) ≤ (c.t_proj : ℝ))
  have hSmax_le : (c.Smax : ℝ) ≤ 33 * L ^ 3 := by
    unfold Cfg.Smax; push_cast
    have := mul_le_mul ht_codeg_le hFmax_le (Nat.cast_nonneg _) (by positivity)
    linarith only [this, show 11 * L * (3 * L ^ 2) = 33 * L ^ 3 by ring]
  have hCint_le : (c.C_int : ℝ) ≤ 33 * L ^ 3 := by
    unfold Cfg.C_int; push_cast
    have ht_cross_le : (c.t_cross : ℝ) ≤ 11 * L := ht_codeg_le
    exact max_le hSmax_le (by linarith only [ht_cross_le, hL3_ge_L])
  have hCproj_le : (c.C_proj : ℝ) ≤ 54 * L ^ 3 := by
    unfold Cfg.C_proj; push_cast; linarith only [hSmax_le, ht_proj_le]
  have he_lt3 : Real.exp 1 < 3 := by linarith only [Real.exp_one_lt_d9]
  have hexpL : Real.exp L = (n : ℝ) := Real.exp_log hnpos
  have hm_le_n : (c.m : ℝ) ≤ (n : ℝ) := by
    have : (n : ℝ) / L ^ 2 ≤ (n : ℝ) := div_le_self hnpos.le (by nlinarith only [hL100])
    linarith only [hm_le, this]
  have hexp2L : Real.exp (2 * L) = (n : ℝ) ^ 2 := by
    rw [show (2 : ℝ) * L = L + L by ring, Real.exp_add, hexpL, sq]
  have h2m_exp : (c.m : ℝ) * (2 * Real.exp (-10 * L)) ≤ 1 / 40 := by
    have h2n : 2 * (c.m : ℝ) ≤ Real.exp (2 * L) := by rw [hexp2L]; nlinarith only [hm_le_n, hn100]
    calc (c.m : ℝ) * (2 * Real.exp (-10 * L)) = (2 * (c.m : ℝ)) * Real.exp (-10 * L) := by ring
      _ ≤ Real.exp (2 * L) * Real.exp (-10 * L) := mul_le_mul_of_nonneg_right h2n (Real.exp_pos _).le
      _ = Real.exp (-8 * L) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-4 : ℝ) := Real.exp_le_exp.mpr (by linarith only [hL100])
      _ ≤ 1 / 40 := exp_neg_four_le
  have hm2_exp : (c.m : ℝ) ^ 2 * Real.exp (-10 * L) ≤ 1 / 40 := by
    have hsq : (c.m : ℝ) ^ 2 ≤ Real.exp (2 * L) := by rw [hexp2L]; nlinarith only [hm_le_n, hm_posR]
    calc (c.m : ℝ) ^ 2 * Real.exp (-10 * L)
        ≤ Real.exp (2 * L) * Real.exp (-10 * L) := mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
      _ = Real.exp (-8 * L) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-4 : ℝ) := Real.exp_le_exp.mpr (by linarith only [hL100])
      _ ≤ 1 / 40 := exp_neg_four_le
  exact ⟨hr_pos, hr_le, hε₁_pos, hε₁_le, hε₂_pos, hε₂_le, hnpos, hn100, hL100, hL_ε₂, hL_ε₁, hL_ε3, hL_ε2,
    hLpos, hsqrtL_ge1, hsqrtL_leL, hsqrtn_pos, hS_eq, hS_ge_sqrtn, hS_pos, hsqrtn_big, hm_le, hm_ge, hm_nat,
    hm_posR, hm1_ge, hnm_ge, hnm_le, hp0, hp_sq, hp_le1, hpS_eq, hpn_eq, hk_le, hk_low, hk_ge_S, hk_le_2S,
    hk_ge_sqrtn, hk_ge100, hk_posR, hk1, hkm, hFmax_ge, hFmax_le, hm1p_le, hm1p_ge, hDmax_ge, hDmax_le,
    hNmax_ge, hNmax_le, ht_codeg_ge, ht_codeg_le, ht_codeg1, ht_cross_ge, ht_cross1, ht_proj_ge, ht_proj_le,
    ht_proj1, hSmax_le, hCint_le, hCproj_le, he_lt3, hexpL, hm_le_n, h2m_exp, hm2_exp⟩

lemma mkCfg_prob1 {ε : ℝ} {n : ℕ} (_hε0 : 0 < ε) (_hε32 : ε ≤ 1 / 32)
    (he : AsymptoticEnv ε n) (hb : MkCfgBase ε n) :
    let c := mkCfg ε n
    (c.m : ℝ) * (2 * Real.exp (-(c.ε₂ / 3) ^ 2 * ((c.n : ℝ) / (c.m : ℝ)) / 4)) ≤ 1 / 40 ∧
    (c.m : ℝ) * (2 * Real.exp (-(c.ε₂ / 3) ^ 2 * (((c.m - 1 : ℕ) : ℝ) * c.p) / 4)) ≤ 1 / 40 ∧
    (c.m : ℝ) ^ 2 * (Real.exp 1 * (c.m : ℝ) * c.p ^ 2 / (c.t_codeg : ℝ)) ^ c.t_codeg ≤ 1 / 40 ∧
    (c.m : ℝ) ^ 2 * (Real.exp 1 * (c.n : ℝ) * ((c.Dmax : ℝ) / (c.m : ℝ)) ^ 2 / (c.t_cross : ℝ)) ^ c.t_cross ≤ 1 / 40 ∧
    (c.m : ℝ) ^ 2 * (Real.exp 1 * (c.Nmax : ℝ) ^ 2 / ((c.m : ℝ) * (c.t_proj : ℝ))) ^ c.t_proj ≤ 1 / 40 := by
  dsimp only
  set c := mkCfg ε n
  set L := Real.log (n : ℝ)
  have h1 : (c.m : ℝ) * (2 * Real.exp (-(c.ε₂ / 3) ^ 2 * ((n : ℝ) / (c.m : ℝ)) / 4)) ≤ 1 / 40 := by
    have hexp : -(c.ε₂ / 3) ^ 2 * ((n : ℝ) / (c.m : ℝ)) / 4 ≤ -10 * L := by
      have h1a : 1000 ≤ c.ε₂ ^ 2 * L := (div_le_iff₀ (sq_pos_of_pos hb.hε₂_pos)).mp hb.hL_ε₂ |>.trans_eq (mul_comm _ _)
      have h1b : 360 * L ≤ c.ε₂ ^ 2 * L ^ 2 := by nlinarith only [h1a, hb.hLpos]
      have h1c : c.ε₂ ^ 2 * L ^ 2 ≤ c.ε₂ ^ 2 * ((n : ℝ) / (c.m : ℝ)) :=
        mul_le_mul_of_nonneg_left hb.hnm_ge (sq_nonneg _)
      linarith only [h1b, h1c]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num))
      hb.hm_posR.le).trans hb.h2m_exp
  have h2 : (c.m : ℝ) * (2 * Real.exp (-(c.ε₂ / 3) ^ 2 * (((c.m - 1 : ℕ) : ℝ) * c.p) / 4)) ≤ 1 / 40 := by
    have hexp : -(c.ε₂ / 3) ^ 2 * (((c.m - 1 : ℕ) : ℝ) * c.p) / 4 ≤ -10 * L := by
      have hdeg' : (3000 / c.ε₂ ^ 2) * L ^ 3 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := he.hdeg_big
      have hε₂_ne : c.ε₂ ≠ 0 := hb.hε₂_pos.ne'
      have h2a : 3000 * L ^ 3 ≤ c.ε₂ ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 2) := by
        have hmul := mul_le_mul_of_nonneg_right hdeg' (sq_nonneg c.ε₂)
        have hcancel : (3000 / c.ε₂ ^ 2) * L ^ 3 * c.ε₂ ^ 2 = 3000 * L ^ 3 := by field_simp [hε₂_ne]
        linarith only [hmul, hcancel]
      have h2b : 360 * L ≤ c.ε₂ ^ 2 * ((n : ℝ) ^ ((1 : ℝ) / 2) / (8 * L ^ 2)) := by
        rw [← mul_div_assoc, le_div_iff₀ (by have := hb.hLpos; positivity : 0 < 8 * L ^ 2)]
        have hL3 : 0 ≤ L ^ 3 := pow_nonneg hb.hLpos.le 3
        linarith only [h2a, hL3, show 360 * L * (8 * L ^ 2) = 2880 * L ^ 3 by ring]
      have h2c : c.ε₂ ^ 2 * ((n : ℝ) ^ ((1 : ℝ) / 2) / (8 * L ^ 2)) ≤ c.ε₂ ^ 2 * (((c.m - 1 : ℕ) : ℝ) * c.p) :=
        mul_le_mul_of_nonneg_left hb.hm1p_ge (sq_nonneg _)
      linarith only [h2b, h2c]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num))
      hb.hm_posR.le).trans hb.h2m_exp
  have h3 : (c.m : ℝ) ^ 2 * (Real.exp 1 * (c.m : ℝ) * c.p ^ 2 / (c.t_codeg : ℝ)) ^ c.t_codeg ≤ 1 / 40 := by
    have hbase : Real.exp 1 * (c.m : ℝ) * c.p ^ 2 / (c.t_codeg : ℝ) ≤ Real.exp (-1) := by
      have htpos : (0 : ℝ) < (c.t_codeg : ℝ) := by exact_mod_cast hb.ht_codeg1
      rw [div_le_iff₀ htpos, Real.exp_neg]
      have hmp2 : (c.m : ℝ) * c.p ^ 2 ≤ 1 / (4 * L) := by
        calc (c.m : ℝ) * c.p ^ 2 ≤ ((n : ℝ) / L ^ 2) * c.p ^ 2 := mul_le_mul_of_nonneg_right hb.hm_le (sq_nonneg _)
          _ = (c.p ^ 2 * (n : ℝ)) / L ^ 2 := by ring
          _ = (L / 4) / L ^ 2 := by rw [hb.hp_sq]
          _ = 1 / (4 * L) := by field_simp [hb.hLpos.ne']
      have he2 : Real.exp 1 * Real.exp 1 ≤ 9 := by nlinarith only [hb.he_lt3, Real.exp_pos 1]
      have h3a : Real.exp 1 * (c.m : ℝ) * c.p ^ 2 * Real.exp 1 ≤ 9 / (4 * L) := by
        have hrew : Real.exp 1 * (c.m : ℝ) * c.p ^ 2 * Real.exp 1 = (Real.exp 1 * Real.exp 1) * ((c.m : ℝ) * c.p ^ 2) := by ring
        rw [hrew]
        exact (mul_le_mul he2 hmp2 (by positivity) (by norm_num)).trans (by ring_nf; exact le_rfl)
      have h3b : 9 / (4 * L) ≤ 10 * L := by
        rw [div_le_iff₀ (by linarith only [hb.hLpos] : 0 < 4 * L)]
        nlinarith only [hb.hL100]
      have h3c : Real.exp 1 * (c.m : ℝ) * c.p ^ 2 * Real.exp 1 ≤ (c.t_codeg : ℝ) := by
        linarith only [h3a, h3b, hb.ht_codeg_ge]
      calc Real.exp 1 * (c.m : ℝ) * c.p ^ 2
          = (Real.exp 1 * (c.m : ℝ) * c.p ^ 2 * Real.exp 1) * (Real.exp 1)⁻¹ := by
              field_simp [(Real.exp_pos 1).ne']
        _ ≤ (c.t_codeg : ℝ) * (Real.exp 1)⁻¹ := mul_le_mul_of_nonneg_right h3c (by positivity)
        _ = (Real.exp 1)⁻¹ * (c.t_codeg : ℝ) := mul_comm _ _
    have hpow : (Real.exp 1 * (c.m : ℝ) * c.p ^ 2 / (c.t_codeg : ℝ)) ^ c.t_codeg ≤ Real.exp (-10 * L) := by
      calc _ ≤ (Real.exp (-1)) ^ c.t_codeg := pow_le_pow_left₀ (by positivity) hbase _
        _ = Real.exp (-(c.t_codeg : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
        _ ≤ Real.exp (-10 * L) := Real.exp_le_exp.mpr (by linarith only [hb.ht_codeg_ge])
    exact (mul_le_mul_of_nonneg_left hpow (sq_nonneg _)).trans hb.hm2_exp
  have h4 : (c.m : ℝ) ^ 2 * (Real.exp 1 * (n : ℝ) * ((c.Dmax : ℝ) / (c.m : ℝ)) ^ 2 / (c.t_cross : ℝ)) ^ c.t_cross ≤ 1 / 40 := by
    have hbase : Real.exp 1 * (n : ℝ) * ((c.Dmax : ℝ) / (c.m : ℝ)) ^ 2 / (c.t_cross : ℝ) ≤ Real.exp (-1) := by
      have hDmax_sharp : (c.Dmax : ℝ) ≤ (3 / 2) * ((c.m : ℝ) * c.p) := by
        have h4a : (c.Dmax : ℝ) < (1 + c.ε₂ / 3) * (((c.m - 1 : ℕ) : ℝ) * c.p) + 1 :=
          Nat.ceil_lt_add_one (by have := hb.hε₂_pos; have := hb.hp0; positivity)
        have hm1 : ((c.m - 1 : ℕ) : ℝ) ≤ (c.m : ℝ) := by exact_mod_cast Nat.sub_le c.m 1
        have hm1_mp : ((c.m - 1 : ℕ) : ℝ) * c.p ≤ (c.m : ℝ) * c.p := mul_le_mul_of_nonneg_right hm1 hb.hp0
        have hmp_ge6 : 6 ≤ (c.m : ℝ) * c.p := by
          have h4b : 6 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) / (8 * L ^ 2) := by
            rw [le_div_iff₀ (by have := hb.hLpos; positivity : 0 < 8 * L ^ 2)]
            have : 48 * L ^ 2 ≤ 10 * L ^ 3 := by nlinarith only [hb.hL100]
            linarith only [this, he.hkm_big]
          linarith only [h4b, hb.hm1p_ge, hm1_mp]
        nlinarith only [h4a, hm1_mp, hmp_ge6, hb.hε₂_le, hb.hε₂_pos]
      have hDm_sharp : (c.Dmax : ℝ) / (c.m : ℝ) ≤ (3 / 2) * c.p := (div_le_iff₀ hb.hm_posR).mpr (by linarith only [hDmax_sharp])
      have hD2_sharp : (n : ℝ) * ((c.Dmax : ℝ) / (c.m : ℝ)) ^ 2 ≤ (9 / 16) * L := by
        have h4c : ((c.Dmax : ℝ) / (c.m : ℝ)) ^ 2 ≤ ((3 / 2) * c.p) ^ 2 := pow_le_pow_left₀ (by positivity) hDm_sharp 2
        calc (n : ℝ) * ((c.Dmax : ℝ) / (c.m : ℝ)) ^ 2
            ≤ (n : ℝ) * ((3 / 2) * c.p) ^ 2 := mul_le_mul_of_nonneg_left h4c hb.hnpos.le
          _ = (9 / 4) * (c.p ^ 2 * (n : ℝ)) := by ring
          _ = (9 / 16) * L := by rw [hb.hp_sq]; ring
      have htpos : (0 : ℝ) < (c.t_cross : ℝ) := by exact_mod_cast hb.ht_cross1
      rw [div_le_iff₀ htpos, Real.exp_neg]
      have he2 : Real.exp 1 * Real.exp 1 ≤ 9 := by nlinarith only [hb.he_lt3, Real.exp_pos 1]
      have h4d : Real.exp 1 * (n : ℝ) * ((c.Dmax : ℝ) / (c.m : ℝ)) ^ 2 * Real.exp 1 ≤ (c.t_cross : ℝ) := by
        have hrew : Real.exp 1 * (n : ℝ) * ((c.Dmax : ℝ) / (c.m : ℝ)) ^ 2 * Real.exp 1 =
            (Real.exp 1 * Real.exp 1) * ((n : ℝ) * ((c.Dmax : ℝ) / (c.m : ℝ)) ^ 2) := by ring
        rw [hrew]
        have hmul := mul_le_mul he2 hD2_sharp (by positivity) (by norm_num)
        linarith only [hmul, hb.ht_cross_ge, hb.hLpos]
      calc Real.exp 1 * (n : ℝ) * ((c.Dmax : ℝ) / (c.m : ℝ)) ^ 2
          = (Real.exp 1 * (n : ℝ) * ((c.Dmax : ℝ) / (c.m : ℝ)) ^ 2 * Real.exp 1) * (Real.exp 1)⁻¹ := by
              field_simp [(Real.exp_pos 1).ne']
        _ ≤ (c.t_cross : ℝ) * (Real.exp 1)⁻¹ := mul_le_mul_of_nonneg_right h4d (by positivity)
        _ = (Real.exp 1)⁻¹ * (c.t_cross : ℝ) := mul_comm _ _
    have hpow : (Real.exp 1 * (n : ℝ) * ((c.Dmax : ℝ) / (c.m : ℝ)) ^ 2 / (c.t_cross : ℝ)) ^ c.t_cross ≤
        Real.exp (-10 * L) := by
      calc _ ≤ (Real.exp (-1)) ^ c.t_cross := pow_le_pow_left₀ (by positivity) hbase _
        _ = Real.exp (-(c.t_cross : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
        _ ≤ Real.exp (-10 * L) := Real.exp_le_exp.mpr (by linarith only [hb.ht_cross_ge])
    exact (mul_le_mul_of_nonneg_left hpow (sq_nonneg _)).trans hb.hm2_exp
  have h5 : (c.m : ℝ) ^ 2 * (Real.exp 1 * (c.Nmax : ℝ) ^ 2 / ((c.m : ℝ) * (c.t_proj : ℝ))) ^ c.t_proj ≤ 1 / 40 := by
    have hN2 : (c.Nmax : ℝ) ^ 2 ≤ (n : ℝ) * L := by
      have h5a := pow_le_pow_left₀ (Nat.cast_nonneg _) hb.hNmax_le 2
      rwa [Real.sq_sqrt (by have := hb.hnpos; have := hb.hLpos; positivity)] at h5a
    have hbase : Real.exp 1 * (c.Nmax : ℝ) ^ 2 / ((c.m : ℝ) * (c.t_proj : ℝ)) ≤ Real.exp (-1) := by
      have htpos : (0 : ℝ) < (c.t_proj : ℝ) := by exact_mod_cast hb.ht_proj1
      rw [div_le_iff₀ (mul_pos hb.hm_posR htpos), Real.exp_neg]
      have he2 : Real.exp 1 * Real.exp 1 ≤ 9 := by nlinarith only [hb.he_lt3, Real.exp_pos 1]
      have h5b : Real.exp 1 * (c.Nmax : ℝ) ^ 2 * Real.exp 1 ≤ 9 * ((n : ℝ) * L) := by
        have hrew : Real.exp 1 * (c.Nmax : ℝ) ^ 2 * Real.exp 1 = (Real.exp 1 * Real.exp 1) * (c.Nmax : ℝ) ^ 2 := by ring
        rw [hrew]; exact mul_le_mul he2 hN2 (sq_nonneg _) (by norm_num)
      have h5c : 9 * ((n : ℝ) * L) ≤ (c.m : ℝ) * (c.t_proj : ℝ) := by
        calc 9 * ((n : ℝ) * L) ≤ 10 * ((n : ℝ) * L) := by nlinarith only [hb.hnpos, hb.hLpos]
          _ = ((1 / 2) * ((n : ℝ) / L ^ 2)) * (20 * L ^ 3) := by field_simp [hb.hLpos.ne']; ring
          _ ≤ (c.m : ℝ) * (c.t_proj : ℝ) := mul_le_mul hb.hm_ge hb.ht_proj_ge (by have := hb.hLpos; positivity) hb.hm_posR.le
      have h5d := h5b.trans h5c
      calc Real.exp 1 * (c.Nmax : ℝ) ^ 2
          = (Real.exp 1 * (c.Nmax : ℝ) ^ 2 * Real.exp 1) * (Real.exp 1)⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ (Real.exp_pos _).ne', mul_one]
        _ ≤ ((c.m : ℝ) * (c.t_proj : ℝ)) * (Real.exp 1)⁻¹ := mul_le_mul_of_nonneg_right h5d (by positivity)
        _ = (Real.exp 1)⁻¹ * ((c.m : ℝ) * (c.t_proj : ℝ)) := mul_comm _ _
    have hpow : (Real.exp 1 * (c.Nmax : ℝ) ^ 2 / ((c.m : ℝ) * (c.t_proj : ℝ))) ^ c.t_proj ≤ Real.exp (-10 * L) := by
      have h10L : 10 * L ≤ (c.t_proj : ℝ) := by
        have hL2 : L ≤ L ^ 2 := by nlinarith only [hb.hL100]
        have hL3 : L ≤ L ^ 3 := by nlinarith only [hL2, hb.hL100]
        linarith only [hb.ht_proj_ge, hL3]
      calc _ ≤ (Real.exp (-1)) ^ c.t_proj := pow_le_pow_left₀ (by positivity) hbase _
        _ = Real.exp (-(c.t_proj : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
        _ ≤ Real.exp (-10 * L) := Real.exp_le_exp.mpr (by linarith only [h10L])
    exact (mul_le_mul_of_nonneg_left hpow (sq_nonneg _)).trans hb.hm2_exp
  exact ⟨h1, h2, h3, h4, h5⟩

lemma mkCfg_prob2 {ε : ℝ} {n : ℕ} (hε0 : 0 < ε) (hε32 : ε ≤ 1 / 32)
    (he : AsymptoticEnv ε n) (hb : MkCfgBase ε n) :
    let c := mkCfg ε n
    1 ≤ c.t_med ∧ c.t₂ ≤ c.Ylim ∧ 2 * c.Ylim / c.t₃ ≤ (c.b₀ : ℝ) ∧ c.b₀ ≤ 2 * c.m ∧
    ((2 * c.Fmax * c.t_med : ℕ) : ℝ) ≤ c.Ylim ∧
    (c.n.choose c.k : ℝ) * ((2 * c.m).choose c.b₀ : ℝ) *
      (Real.exp 1 * ((c.b₀ * c.k : ℕ) : ℝ) * c.p / (c.t_med : ℝ)) ^ c.t_med ≤ 1 / 40 ∧
    (c.n.choose c.k : ℝ) * Real.exp (-2 * c.t_small ^ 2 / ((2 * (c.m : ℝ)) * (c.t₃ ^ 2 / 2) ^ 2)) ≤ 1 / 40 := by
  dsimp only
  set c := mkCfg ε n
  set L := Real.log (n : ℝ)
  have hF2' : (200 / c.ε₁) * L ^ 3 ≤ (n : ℝ) ^ ((1 : ℝ) / 4 - ε) := he.hF2_big
  have h1_div_ε₁ : 1 ≤ 1 / c.ε₁ := (one_le_div hb.hε₁_pos).mpr hb.hε₁_le
  have h200L3 : 200 * L ^ 3 ≤ (n : ℝ) ^ ((1 : ℝ) / 4 - ε) := by
    have : 200 * L ^ 3 ≤ (200 / c.ε₁) * L ^ 3 := by
      have hL3 : 0 ≤ L ^ 3 := pow_nonneg hb.hLpos.le 3
      have h200 : 200 ≤ 200 / c.ε₁ := by linarith only [show 200 / c.ε₁ = 200 * (1 / c.ε₁) by ring, h1_div_ε₁]
      exact mul_le_mul_of_nonneg_right h200 hL3
    linarith only [this, hF2']
  have hL2_le_L3 : L ^ 2 ≤ L ^ 3 := by nlinarith only [hb.hL100]
  have hMed_ht₂ : c.t₂ ≤ c.Ylim := by
    have h1 : (n : ℝ) ^ (2 * ε) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith only [hb.hn100]) (by linarith only [hε32])
    have h2 : (n : ℝ) ^ ((1 : ℝ) / 4 + ε) = (n : ℝ) ^ (2 * ε) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) := by
      rw [← Real.rpow_add hb.hnpos]; congr 1; ring
    dsimp only [c, mkCfg]; rw [h2]
    exact mul_le_mul_of_nonneg_right (h1.trans hb.hk_ge_sqrtn) (Real.rpow_nonneg hb.hnpos.le _)
  have hMed_b₀_ge : 2 * c.Ylim / c.t₃ ≤ (c.b₀ : ℝ) := Nat.le_ceil _
  have h2Y_t3 : 2 * c.Ylim / c.t₃ = 2 * (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε) := by
    have hY : c.Ylim = (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) := rfl
    have ht3 : c.t₃ = (n : ℝ) ^ (2 * ε) := rfl
    rw [hY, ht3, mul_div_assoc, mul_div_assoc, ← Real.rpow_sub hb.hnpos, ← mul_assoc]
    congr 2; ring
  have hb₀_ge_2 : 2 * (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε) ≤ (c.b₀ : ℝ) := h2Y_t3 ▸ hMed_b₀_ge
  have hpow_ge1 : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε) :=
    Real.one_le_rpow (by linarith only [hb.hn100]) (by linarith only [hε32])
  have hb₀_le_3 : (c.b₀ : ℝ) ≤ 3 * (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε) := by
    have h1 : (c.b₀ : ℝ) < 2 * c.Ylim / c.t₃ + 1 := Nat.ceil_lt_add_one (by
      have := hb.hnpos; positivity)
    rw [h2Y_t3] at h1
    have hge1 : 1 ≤ (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε) := by nlinarith only [hb.hk_ge100, hpow_ge1]
    linarith only [h1, hge1]
  have hMed_b₀_le : c.b₀ ≤ 2 * c.m := by
    have h1 : (c.b₀ : ℝ) ≤ (2 * c.m : ℕ) := by
      push_cast
      have hk_2nL : (c.k : ℝ) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 2) * L := by
        have := hb.hk_le_2S; rw [hb.hS_eq] at this; nlinarith only [this, hb.hsqrtL_leL, hb.hsqrtn_pos]
      have h2 : (c.b₀ : ℝ) ≤ 6 * (n : ℝ) ^ ((3 : ℝ) / 4 - 3 * ε) * L := by
        have h3 := mul_le_mul_of_nonneg_right hk_2nL (Real.rpow_nonneg hb.hnpos.le ((1 : ℝ) / 4 - 3 * ε))
        have h4 : (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε) =
            (n : ℝ) ^ ((3 : ℝ) / 4 - 3 * ε) := by rw [← Real.rpow_add hb.hnpos]; congr 1; ring
        have h5 : 2 * (n : ℝ) ^ ((1 : ℝ) / 2) * L * (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε) =
            2 * (n : ℝ) ^ ((3 : ℝ) / 4 - 3 * ε) * L := by
          rw [← h4]; ring
        linarith only [hb₀_le_3, h3, h5]
      have h3 : 6 * (n : ℝ) ^ ((3 : ℝ) / 4 - 3 * ε) * L ≤ (n : ℝ) / L ^ 2 := by
        rw [le_div_iff₀ (sq_pos_of_pos hb.hLpos)]
        have h4 : (n : ℝ) ^ ((3 : ℝ) / 4 - 3 * ε) * (n : ℝ) ^ ((1 : ℝ) / 4 + 3 * ε) = (n : ℝ) := by
          rw [← Real.rpow_add hb.hnpos]; norm_num
        have h5 : 6 * L ^ 3 ≤ (n : ℝ) ^ ((1 : ℝ) / 4 + 3 * ε) := by
          have hL3 : 0 ≤ L ^ 3 := pow_nonneg hb.hLpos.le 3
          linarith only [he.hmed2_big, hL3]
        have h6 := mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hb.hnpos.le ((3 : ℝ) / 4 - 3 * ε))
        linarith only [h4, h6, show 6 * (n : ℝ) ^ ((3 : ℝ) / 4 - 3 * ε) * L * L ^ 2 =
          (n : ℝ) ^ ((3 : ℝ) / 4 - 3 * ε) * (6 * L ^ 3) by ring]
      linarith only [h2, h3, hb.hm_ge]
    exact_mod_cast h1
  have hMed_tmed_le : ((2 * c.Fmax * c.t_med : ℕ) : ℝ) ≤ c.Ylim := by
    push_cast
    have hFpos : (0 : ℝ) < 2 * (c.Fmax : ℝ) := by
      have : L ^ 2 ≤ (c.Fmax : ℝ) := by nlinarith only [hb.hFmax_ge, hb.hnm_ge, hb.hε₂_pos, hb.hL100]
      nlinarith only [this, hb.hL100]
    have hYnn : 0 ≤ c.Ylim := by
      have hY : c.Ylim = (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) := rfl
      rw [hY]; have := hb.hk_posR; have := hb.hnpos; positivity
    have hfl : (c.t_med : ℝ) ≤ c.Ylim / (2 * (c.Fmax : ℝ)) := Nat.floor_le (div_nonneg hYnn hFpos.le)
    linarith only [(le_div_iff₀ hFpos).mp hfl]
  have ht_med_ge : (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) / (12 * L ^ 2) ≤ (c.t_med : ℝ) := by
    have hfl : c.Ylim / (2 * (c.Fmax : ℝ)) - 1 < (c.t_med : ℝ) := Nat.sub_one_lt_floor _
    have hFpos : (0 : ℝ) < 2 * (c.Fmax : ℝ) := by
      have : L ^ 2 ≤ (c.Fmax : ℝ) := by nlinarith only [hb.hFmax_ge, hb.hnm_ge, hb.hε₂_pos, hb.hL100]
      nlinarith only [this, hb.hL100]
    have hYeq : c.Ylim = (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) := rfl
    have hdiv : (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) / (6 * L ^ 2) ≤ c.Ylim / (2 * (c.Fmax : ℝ)) := by
      rw [hYeq]
      exact div_le_div_of_nonneg_left (by have := hb.hk_posR; have := hb.hnpos; positivity) hFpos (by linarith only [hb.hFmax_le])
    have hge1 : 1 ≤ (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) / (12 * L ^ 2) := by
      rw [one_le_div (by have := hb.hLpos; positivity : 0 < 12 * L ^ 2)]
      nlinarith only [hb.hk_ge100, h200L3, hL2_le_L3, hb.hL100]
    have h2eq : (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) / (6 * L ^ 2) =
        2 * ((c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) / (12 * L ^ 2)) := by ring
    linarith only [hfl, hdiv, hge1, h2eq]
  have ht_med1 : 1 ≤ c.t_med := by
    have hge1 : (1 : ℝ) ≤ (c.t_med : ℝ) := by
      have h1 : 1 ≤ (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) / (12 * L ^ 2) := by
        rw [one_le_div (by have := hb.hLpos; positivity : 0 < 12 * L ^ 2)]
        nlinarith only [hb.hk_ge100, h200L3, hL2_le_L3, hb.hL100]
      linarith only [h1, ht_med_ge]
    exact_mod_cast hge1
  have hch1 : (n.choose c.k : ℝ) ≤ Real.exp ((c.k : ℝ) * L) := by
    calc (n.choose c.k : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (c.k : ℝ)) ^ c.k := choose_le_exp_pow hb.hk1
      _ ≤ (n : ℝ) ^ c.k := by
          refine pow_le_pow_left₀ (by positivity) ?_ c.k
          rw [div_le_iff₀ hb.hk_posR]; nlinarith only [hb.he_lt3, hb.hk_ge100, hb.hnpos]
      _ = Real.exp ((c.k : ℝ) * L) := by rw [← hb.hexpL, ← Real.exp_nat_mul]
  have hPr_med : (n.choose c.k : ℝ) * ((2 * c.m).choose c.b₀ : ℝ) *
      (Real.exp 1 * ((c.b₀ * c.k : ℕ) : ℝ) * c.p / (c.t_med : ℝ)) ^ c.t_med ≤ 1 / 40 := by
    have hb₀_ge3 : (3 : ℝ) ≤ (c.b₀ : ℝ) := by nlinarith only [hb₀_ge_2, hb.hk_ge100, hpow_ge1]
    have hb₀1 : 1 ≤ c.b₀ := by exact_mod_cast (by linarith only [hb₀_ge3] : (1 : ℝ) ≤ (c.b₀ : ℝ))
    have hch2 : ((2 * c.m).choose c.b₀ : ℝ) ≤ Real.exp ((c.b₀ : ℝ) * (L + 1)) := by
      have h2m_le : (2 * c.m : ℝ) ≤ Real.exp (L + 1) := by
        rw [Real.exp_add, hb.hexpL]
        have : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
        nlinarith only [hb.hm_le_n, this, hb.hnpos]
      calc ((2 * c.m).choose c.b₀ : ℝ)
          ≤ (Real.exp 1 * ((2 * c.m : ℕ) : ℝ) / (c.b₀ : ℝ)) ^ c.b₀ := choose_le_exp_pow hb₀1
        _ ≤ (Real.exp (L + 1)) ^ c.b₀ := by
            refine pow_le_pow_left₀ (by positivity) ?_ c.b₀
            push_cast
            rw [div_le_iff₀ (by linarith only [hb₀_ge3] : (0 : ℝ) < (c.b₀ : ℝ))]
            have h3m : Real.exp 1 * (2 * (c.m : ℝ)) ≤ 3 * (2 * (c.m : ℝ)) := by nlinarith only [hb.he_lt3, hb.hm_posR]
            nlinarith only [h3m, h2m_le, hb₀_ge3, Real.exp_pos (L + 1)]
        _ = Real.exp ((c.b₀ : ℝ) * (L + 1)) := by rw [← Real.exp_nat_mul]
    have hbase : Real.exp 1 * ((c.b₀ * c.k : ℕ) : ℝ) * c.p / (c.t_med : ℝ) ≤ Real.exp (-1) := by
      have htpos : (0 : ℝ) < (c.t_med : ℝ) := by exact_mod_cast ht_med1
      rw [div_le_iff₀ htpos, Real.exp_neg]
      have hpk_le : (c.k : ℝ) * c.p ≤ L := by
        have h1 : c.p * (c.k : ℝ) ≤ (1 + ε) * (L / 2) := by
          calc c.p * (c.k : ℝ) ≤ c.p * ((1 + ε) * Real.sqrt ((n : ℝ) * L)) := mul_le_mul_of_nonneg_left hb.hk_le hb.hp0
            _ = (1 + ε) * (c.p * Real.sqrt ((n : ℝ) * L)) := by ring
            _ = (1 + ε) * (L / 2) := by rw [hb.hpS_eq]
        nlinarith only [h1, hε32, hb.hLpos]
      have he2 : Real.exp 1 * Real.exp 1 ≤ 9 := by nlinarith only [hb.he_lt3, Real.exp_pos 1]
      have hnum : Real.exp 1 * ((c.b₀ * c.k : ℕ) : ℝ) * c.p * Real.exp 1 ≤
          27 * (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε) * L := by
        push_cast
        have h1 : (c.b₀ : ℝ) * ((c.k : ℝ) * c.p) ≤ (3 * (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε)) * L :=
          mul_le_mul hb₀_le_3 hpk_le (by have := hb.hk_posR; have := hb.hp0; positivity)
            (by have := hb.hk_posR; have := hb.hnpos; positivity)
        have hrew : Real.exp 1 * ((c.b₀ : ℝ) * (c.k : ℝ)) * c.p * Real.exp 1 =
            (Real.exp 1 * Real.exp 1) * ((c.b₀ : ℝ) * ((c.k : ℝ) * c.p)) := by ring
        rw [hrew]
        have hmul := mul_le_mul he2 h1 (by have := hb.hk_posR; have := hb.hp0; positivity) (by norm_num)
        linarith only [hmul]
      have hcmp : 27 * (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε) * L ≤ (c.t_med : ℝ) := by
        have h1 : 324 * L ^ 3 ≤ (n : ℝ) ^ (2 * ε) := by
          have hL3 : 0 ≤ L ^ 3 := pow_nonneg hb.hLpos.le 3
          linarith only [he.hmed1_big, hL3]
        have h2 : (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε) * (n : ℝ) ^ (2 * ε) = (n : ℝ) ^ ((1 : ℝ) / 4 - ε) := by
          rw [← Real.rpow_add hb.hnpos]; congr 1; ring
        have h3 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε) by
          have := hb.hk_posR; have := hb.hnpos; positivity)
        have h4 : 27 * (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε) * L * (12 * L ^ 2) ≤
            (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) := by
          linarith only [h3, show 27 * (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε) * L * (12 * L ^ 2) =
            (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε) * (324 * L ^ 3) by ring,
            show (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε) * (n : ℝ) ^ (2 * ε) =
            (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) by rw [mul_assoc, h2]]
        exact ((le_div_iff₀ (by have := hb.hLpos; positivity : 0 < 12 * L ^ 2)).mpr h4).trans ht_med_ge
      have htot := hnum.trans hcmp
      calc Real.exp 1 * ((c.b₀ * c.k : ℕ) : ℝ) * c.p
          = (Real.exp 1 * ((c.b₀ * c.k : ℕ) : ℝ) * c.p * Real.exp 1) * (Real.exp 1)⁻¹ := by
              field_simp [(Real.exp_pos 1).ne']
        _ ≤ (c.t_med : ℝ) * (Real.exp 1)⁻¹ := mul_le_mul_of_nonneg_right htot (by positivity)
        _ = (Real.exp 1)⁻¹ * (c.t_med : ℝ) := mul_comm _ _
    have hexp_dom : (c.k : ℝ) * L + (c.b₀ : ℝ) * (L + 1) + 4 ≤ (c.t_med : ℝ) := by
      have h1 : (c.k : ℝ) * L ≤ (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) / (36 * L ^ 2) := by
        rw [le_div_iff₀ (by have := hb.hLpos; positivity : 0 < 36 * L ^ 2)]
        have h1a : 36 * L ^ 3 ≤ (n : ℝ) ^ ((1 : ℝ) / 4 - ε) := by
          have hL3 : 0 ≤ L ^ 3 := pow_nonneg hb.hLpos.le 3
          linarith only [h200L3, hL3]
        have h1b := mul_le_mul_of_nonneg_left h1a hb.hk_posR.le
        linarith only [h1b, show (c.k : ℝ) * L * (36 * L ^ 2) = (c.k : ℝ) * (36 * L ^ 3) by ring]
      have h2 : (c.b₀ : ℝ) * (L + 1) ≤ (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) / (36 * L ^ 2) := by
        have hbL : (c.b₀ : ℝ) * (L + 1) ≤ 6 * (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε) * L := by
          have hL1 : L + 1 ≤ 2 * L := by linarith only [hb.hL100]
          have hmul := mul_le_mul hb₀_le_3 hL1 (by linarith only [hb.hLpos]) (by have := hb.hk_posR; have := hb.hnpos; positivity)
          linarith only [hmul]
        have h2a : 216 * L ^ 3 ≤ (n : ℝ) ^ (2 * ε) := by
          have hL3 : 0 ≤ L ^ 3 := pow_nonneg hb.hLpos.le 3
          linarith only [he.hmed1_big, hL3]
        have h2b : (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε) * (n : ℝ) ^ (2 * ε) = (n : ℝ) ^ ((1 : ℝ) / 4 - ε) := by
          rw [← Real.rpow_add hb.hnpos]; congr 1; ring
        have h2c := mul_le_mul_of_nonneg_left h2a (show 0 ≤ (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε) by
          have := hb.hk_posR; have := hb.hnpos; positivity)
        have h2d : 6 * (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε) * L * (36 * L ^ 2) ≤
            (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) := by
          linarith only [h2c, show 6 * (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε) * L * (36 * L ^ 2) =
            (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε) * (216 * L ^ 3) by ring,
            show (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - 3 * ε) * (n : ℝ) ^ (2 * ε) =
            (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) by rw [mul_assoc, h2b]]
        exact hbL.trans ((le_div_iff₀ (by have := hb.hLpos; positivity : 0 < 36 * L ^ 2)).mpr h2d)
      have h3 : 4 ≤ (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) / (36 * L ^ 2) := by
        rw [le_div_iff₀ (by have := hb.hLpos; positivity : 0 < 36 * L ^ 2)]
        nlinarith only [hb.hk_ge100, h200L3, hL2_le_L3, hb.hL100]
      linarith only [h1, h2, h3, ht_med_ge,
        show (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) / (12 * L ^ 2) =
          3 * ((c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) / (36 * L ^ 2)) by ring]
    calc (n.choose c.k : ℝ) * ((2 * c.m).choose c.b₀ : ℝ) *
          (Real.exp 1 * ((c.b₀ * c.k : ℕ) : ℝ) * c.p / (c.t_med : ℝ)) ^ c.t_med
        ≤ Real.exp ((c.k : ℝ) * L) * Real.exp ((c.b₀ : ℝ) * (L + 1)) * (Real.exp (-1)) ^ c.t_med := by
            refine mul_le_mul (mul_le_mul hch1 hch2 (Nat.cast_nonneg _) (Real.exp_pos _).le)
              (pow_le_pow_left₀ (by have := hb.hp0; positivity) hbase _) (by have := hb.hp0; positivity) (by positivity)
      _ = Real.exp ((c.k : ℝ) * L + (c.b₀ : ℝ) * (L + 1) - (c.t_med : ℝ)) := by
            rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-4 : ℝ) := Real.exp_le_exp.mpr (by linarith only [hexp_dom])
      _ ≤ 1 / 40 := exp_neg_four_le
  have hPr_small : (n.choose c.k : ℝ) * Real.exp (-2 * c.t_small ^ 2 / ((2 * (c.m : ℝ)) * (c.t₃ ^ 2 / 2) ^ 2)) ≤ 1 / 40 := by
    have hden_le : (2 * (c.m : ℝ)) * (c.t₃ ^ 2 / 2) ^ 2 ≤ (n : ℝ) ^ (1 + 8 * ε) / (2 * L ^ 2) := by
      have ht3_4 : (c.t₃ ^ 2 / 2) ^ 2 = (n : ℝ) ^ (8 * ε) / 4 := by
        have ht3 : c.t₃ = (n : ℝ) ^ (2 * ε) := rfl
        rw [ht3, div_pow, ← pow_mul, ← Real.rpow_natCast ((n : ℝ) ^ (2 * ε)) (2 * 2), ← Real.rpow_mul hb.hnpos.le]
        congr 1
        · congr 1; push_cast; ring
        · norm_num
      rw [ht3_4]
      have hprod : (n : ℝ) * (n : ℝ) ^ (8 * ε) = (n : ℝ) ^ (1 + 8 * ε) := by
        conv_lhs => arg 1; rw [← Real.rpow_one (n : ℝ)]
        rw [← Real.rpow_add hb.hnpos]
      have h1 := mul_le_mul_of_nonneg_right (by linarith only [hb.hm_le] : 2 * (c.m : ℝ) ≤ 2 * ((n : ℝ) / L ^ 2))
        (show 0 ≤ (n : ℝ) ^ (8 * ε) / 4 by have := hb.hnpos; positivity)
      linarith only [h1, show (2 * ((n : ℝ) / L ^ 2)) * ((n : ℝ) ^ (8 * ε) / 4) =
        (n : ℝ) ^ (1 + 8 * ε) / (2 * L ^ 2) by rw [← hprod]; ring]
    have hnum_ge : (c.ε₁ ^ 2 / 2) * (n : ℝ) ^ 2 * L ^ 2 ≤ 2 * c.t_small ^ 2 := by
      have hk4 : (n : ℝ) ^ 2 * L ^ 2 ≤ (c.k : ℝ) ^ 4 := by
        have hS2 : (Real.sqrt ((n : ℝ) * L)) ^ 2 = (n : ℝ) * L := Real.sq_sqrt (by have := hb.hnpos; have := hb.hLpos; positivity)
        have h1 := pow_le_pow_left₀ hb.hS_pos.le hb.hk_ge_S 4
        have h2 : (Real.sqrt ((n : ℝ) * L)) ^ 4 = ((Real.sqrt ((n : ℝ) * L)) ^ 2) ^ 2 := by ring
        rw [h2, hS2, mul_pow] at h1; exact h1
      have hrew : 2 * c.t_small ^ 2 = (c.ε₁ ^ 2 / 2) * (c.k : ℝ) ^ 4 := by dsimp only [c, mkCfg]; ring
      rw [hrew]
      have hmul := mul_le_mul_of_nonneg_left hk4 (show 0 ≤ c.ε₁ ^ 2 / 2 by positivity)
      linarith only [hmul]
    have hratio : (c.k : ℝ) * L + 4 ≤ 2 * c.t_small ^ 2 / ((2 * (c.m : ℝ)) * (c.t₃ ^ 2 / 2) ^ 2) := by
      have h1 : c.ε₁ ^ 2 * (n : ℝ) ^ (1 - 8 * ε) * L ^ 4 ≤
          ((c.ε₁ ^ 2 / 2) * (n : ℝ) ^ 2 * L ^ 2) / ((n : ℝ) ^ (1 + 8 * ε) / (2 * L ^ 2)) := by
        have hpow_sub : (n : ℝ) ^ 2 / (n : ℝ) ^ (1 + 8 * ε) = (n : ℝ) ^ (1 - 8 * ε) := by
          rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_sub hb.hnpos]; congr 1; norm_num; ring
        have heq : ((c.ε₁ ^ 2 / 2) * (n : ℝ) ^ 2 * L ^ 2) / ((n : ℝ) ^ (1 + 8 * ε) / (2 * L ^ 2)) =
            c.ε₁ ^ 2 * ((n : ℝ) ^ 2 / (n : ℝ) ^ (1 + 8 * ε)) * L ^ 4 := by
          field_simp [hb.hLpos.ne', (Real.rpow_pos_of_pos hb.hnpos _).ne']
        rw [heq, hpow_sub]
      have h2 : ((c.ε₁ ^ 2 / 2) * (n : ℝ) ^ 2 * L ^ 2) / ((n : ℝ) ^ (1 + 8 * ε) / (2 * L ^ 2)) ≤
          2 * c.t_small ^ 2 / ((2 * (c.m : ℝ)) * (c.t₃ ^ 2 / 2) ^ 2) := by
        have hdenpos : 0 < (2 * (c.m : ℝ)) * (c.t₃ ^ 2 / 2) ^ 2 := by
          have := hb.hm_posR; have := hb.hnpos; dsimp only [c, mkCfg]; positivity
        exact div_le_div₀ (by positivity) hnum_ge hdenpos hden_le
      have h3 : (c.k : ℝ) * L + 4 ≤ c.ε₁ ^ 2 * (n : ℝ) ^ (1 - 8 * ε) * L ^ 4 := by
        have hk_2nL : (c.k : ℝ) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 2) * L := by
          have := hb.hk_le_2S; rw [hb.hS_eq] at this; nlinarith only [this, hb.hsqrtL_leL, hb.hsqrtn_pos]
        have hkL : (c.k : ℝ) * L + 4 ≤ 3 * (n : ℝ) ^ ((1 : ℝ) / 2) * L ^ 2 := by
          have hmul := mul_le_mul_of_nonneg_right hk_2nL hb.hLpos.le
          have hge4 : 4 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) * L ^ 2 := by
            have h1 : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow (by linarith only [hb.hn100]) (by norm_num)
            nlinarith only [h1, hb.hL100]
          linarith only [hmul, hge4, show 2 * (n : ℝ) ^ ((1 : ℝ) / 2) * L * L = 2 * (n : ℝ) ^ ((1 : ℝ) / 2) * L ^ 2 by ring]
        have hsm2' : 20 / c.ε₁ ^ 2 ≤ (n : ℝ) ^ ((1 : ℝ) / 2 - 8 * ε) := by
          have h0 : 20 / c.ε₁ ^ 2 * L ^ 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 2 - 8 * ε) := he.hsm2_big
          simpa [pow_zero] using h0
        have hε₁_ne : c.ε₁ ≠ 0 := hb.hε₁_pos.ne'
        have h4 : 20 ≤ c.ε₁ ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 2 - 8 * ε) := by
          have hmul := mul_le_mul_of_nonneg_right hsm2' (sq_nonneg c.ε₁)
          have hcancel : (20 / c.ε₁ ^ 2) * c.ε₁ ^ 2 = 20 := by field_simp [hε₁_ne]
          linarith only [hmul, hcancel]
        have h5 : (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2 - 8 * ε) = (n : ℝ) ^ (1 - 8 * ε) := by
          rw [← Real.rpow_add hb.hnpos]; congr 1; ring
        have h6 : 20 * (n : ℝ) ^ ((1 : ℝ) / 2) ≤ c.ε₁ ^ 2 * (n : ℝ) ^ (1 - 8 * ε) := by
          have hmul := mul_le_mul_of_nonneg_right h4 hb.hsqrtn_pos.le
          linarith only [hmul, show c.ε₁ ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 2 - 8 * ε) * (n : ℝ) ^ ((1 : ℝ) / 2) =
            c.ε₁ ^ 2 * (n : ℝ) ^ (1 - 8 * ε) by rw [mul_assoc, mul_comm ((n : ℝ) ^ _), h5]]
        have hL24 : L ^ 2 ≤ L ^ 4 := by
          have hL2 : 1 ≤ L ^ 2 := by nlinarith only [hb.hL100]
          nlinarith only [hL2]
        have hmul := mul_le_mul h6 hL24 (sq_nonneg L) (by have := hb.hnpos; positivity)
        have hpos : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) * L ^ 2 := by have := hb.hsqrtn_pos; positivity
        linarith only [hkL, hmul, hpos]
      linarith only [h1, h2, h3]
    have hneg_eq : -2 * c.t_small ^ 2 / ((2 * (c.m : ℝ)) * (c.t₃ ^ 2 / 2) ^ 2) =
        -(2 * c.t_small ^ 2 / ((2 * (c.m : ℝ)) * (c.t₃ ^ 2 / 2) ^ 2)) := by ring
    calc (n.choose c.k : ℝ) * Real.exp (-2 * c.t_small ^ 2 / ((2 * (c.m : ℝ)) * (c.t₃ ^ 2 / 2) ^ 2))
        ≤ Real.exp ((c.k : ℝ) * L) * Real.exp (-(2 * c.t_small ^ 2 / ((2 * (c.m : ℝ)) * (c.t₃ ^ 2 / 2) ^ 2))) := by
            rw [hneg_eq]; exact mul_le_mul_of_nonneg_right hch1 (Real.exp_pos _).le
      _ = Real.exp ((c.k : ℝ) * L - 2 * c.t_small ^ 2 / ((2 * (c.m : ℝ)) * (c.t₃ ^ 2 / 2) ^ 2)) := by
            rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-4 : ℝ) := Real.exp_le_exp.mpr (by linarith only [hratio])
      _ ≤ 1 / 40 := exp_neg_four_le
  exact ⟨ht_med1, hMed_ht₂, hMed_b₀_ge, hMed_b₀_le, hMed_tmed_le, hPr_med, hPr_small⟩

lemma mkCfg_det_and_RI {ε : ℝ} {n : ℕ} (hε0 : 0 < ε) (hε32 : ε ≤ 1 / 32)
    (he : AsymptoticEnv ε n) (hb : MkCfgBase ε n) :
    let c := mkCfg ε n
    (c.k : ℝ) + ((c.L_cap.choose 2 * c.C_int : ℕ) : ℝ) < (c.L_cap : ℝ) * c.t₂ ∧
    (c.k : ℝ) + ((c.H_cap.choose 2 * c.C_int : ℕ) : ℝ) < (c.H_cap : ℝ) * c.t₁ ∧
    c.Nthr * (c.Fmax : ℝ) + (c.Dmax : ℝ) * c.Fthr ≤ c.t₁ ∧
    (c.t₁ / 2) * ((c.k : ℝ) + ((c.L_cap.choose 2 * c.C_int : ℕ) : ℝ)) ≤ c.ε₁ * (c.k : ℝ) ^ 2 ∧
    (c.t₂ / 2) * c.Ylim ≤ c.ε₁ * (c.k : ℝ) ^ 2 ∧
    (c.k : ℝ) * c.t₃ ^ 2 + (c.k : ℝ) * (c.Fmax : ℝ) +
      (c.k.choose 2 : ℝ) * (2 * (c.m : ℝ) * c.p ^ 2) + c.t_small ≤ c.ε₁ * (c.k : ℝ) ^ 2 ∧
    ((c.H_cap * c.Dmax : ℕ) : ℝ) ^ 2 / 2 ≤ c.ε₁ * (c.k : ℝ) ^ 2 ∧
    ((c.H_cap * c.Dmax + c.H_cap.choose 2 * c.C_proj : ℕ) : ℝ) ≤ (c.ε₁ / 4) * (c.k : ℝ) ∧
    ((c.k : ℝ) / c.Fthr + (c.L_cap : ℝ) + (c.H_cap : ℝ)) * (c.k : ℝ) ≤ c.ε₁ * (c.k : ℝ) ^ 2 ∧
    (c.k : ℝ) / 2 ≤ c.ε₁ * (c.k : ℝ) ^ 2 ∧
    1 ≤ c.ε₁ * (c.k : ℝ) ^ 2 ∧
    (1 + 7 * ε / 8) * (Real.log (n : ℝ) / 2) ≤ c.p * (c.k : ℝ) ∧
    c.p * (c.k : ℝ) ≤ (1 + ε) * (Real.log (n : ℝ) / 2) ∧
    (n : ℝ) / (c.k : ℝ) ≤ Real.exp (Real.log (n : ℝ) / 2) ∧
    (c.k : ℝ) / (c.m : ℝ) ≤ Real.exp (-(1 / 2 - ε ^ 3 / 40) * Real.log (n : ℝ)) ∧
    Real.exp 3 ≤ Real.exp ((ε ^ 3 / 40) * Real.log (n : ℝ)) ∧
    2 * (c.k : ℝ) ^ 2 * Real.exp (-(ε ^ 2 / 8) * (c.k : ℝ) * Real.log (n : ℝ)) < 1 / 4 := by
  dsimp only
  set c := mkCfg ε n
  set L := Real.log (n : ℝ)
  have hsqrtn_eq : Real.sqrt (n : ℝ) = (n : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (n : ℝ)
  have ht₂_pos : 0 < c.t₂ := Real.rpow_pos_of_pos hb.hnpos _
  have h100_div_ε₁ : 100 / c.ε₁ ≤ L := by
    have h1 : 100 / c.ε₁ ≤ 100 / c.ε₁ ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hb.hε₁_pos) (by nlinarith only [hb.hε₁_pos, hb.hε₁_le])
    linarith only [h1, hb.hL_ε₁]
  have h100_le_ε₁L : 100 ≤ c.ε₁ * L := (div_le_iff₀ hb.hε₁_pos).mp h100_div_ε₁ |>.trans_eq (mul_comm _ _)
  have h1_div_sqrtL : 1 / Real.sqrt L ≤ c.ε₁ := by
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hb.hLpos)]
    have h1 : 100 ≤ c.ε₁ ^ 2 * L := (div_le_iff₀ (sq_pos_of_pos hb.hε₁_pos)).mp hb.hL_ε₁ |>.trans_eq (mul_comm _ _)
    have h2 : (1 : ℝ) ≤ (c.ε₁ * Real.sqrt L) ^ 2 := by rw [mul_pow, Real.sq_sqrt hb.hLpos.le]; linarith only [h1]
    have hpos : 0 < c.ε₁ * Real.sqrt L := mul_pos hb.hε₁_pos (Real.sqrt_pos.mpr hb.hLpos)
    nlinarith only [h2, hpos]
  have hε₁_ne : c.ε₁ ≠ 0 := hb.hε₁_pos.ne'
  have hL_ne : L ≠ 0 := hb.hLpos.ne'
  have hsqrtL_ne : Real.sqrt L ≠ 0 := (Real.sqrt_pos.mpr hb.hLpos).ne'
  have hHcap_big' : (10000 / c.ε₁) * L ^ 4 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := he.hHcap_big
  have h10000L4 : 10000 * L ^ 4 ≤ c.ε₁ * (n : ℝ) ^ ((1 : ℝ) / 2) := by
    have hmul := mul_le_mul_of_nonneg_right hHcap_big' hb.hε₁_pos.le
    have hcancel : (10000 / c.ε₁) * L ^ 4 * c.ε₁ = 10000 * L ^ 4 := by field_simp [hε₁_ne]
    linarith only [hmul, hcancel]
  -- `L_cap` and `H_cap` bounds
  have hLcap_ge : 2 * (c.k : ℝ) / c.t₂ ≤ (c.L_cap : ℝ) := Nat.le_ceil _
  have hLcap_le : (c.L_cap : ℝ) ≤ 6 * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) * Real.sqrt L := by
    have h1 : (c.L_cap : ℝ) < 2 * (c.k : ℝ) / c.t₂ + 1 := Nat.ceil_lt_add_one (by have := hb.hk_posR; positivity)
    have hdiv : 2 * (c.k : ℝ) / c.t₂ ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) * Real.sqrt L := by
      have h2 : (c.k : ℝ) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 2) * Real.sqrt L := by
        have h2a := hb.hk_le_2S; rw [hb.hS_eq] at h2a; linarith only [h2a]
      have h3 : (n : ℝ) ^ ((1 : ℝ) / 2) / (n : ℝ) ^ ((1 : ℝ) / 4 + ε) = (n : ℝ) ^ ((1 : ℝ) / 4 - ε) := by
        rw [← Real.rpow_sub hb.hnpos]; congr 1; ring
      have ht2_eq : c.t₂ = (n : ℝ) ^ ((1 : ℝ) / 4 + ε) := rfl
      rw [ht2_eq]
      calc 2 * (c.k : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 4 + ε)
          ≤ 2 * (2 * (n : ℝ) ^ ((1 : ℝ) / 2) * Real.sqrt L) / (n : ℝ) ^ ((1 : ℝ) / 4 + ε) :=
            div_le_div_of_nonneg_right (by linarith only [h2]) (Real.rpow_pos_of_pos hb.hnpos _).le
        _ = 4 * ((n : ℝ) ^ ((1 : ℝ) / 2) / (n : ℝ) ^ ((1 : ℝ) / 4 + ε)) * Real.sqrt L := by ring
        _ = 4 * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) * Real.sqrt L := by rw [h3]
    have hge1 : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 4 - ε) * Real.sqrt L := by
      have hpow : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4 - ε) :=
        Real.one_le_rpow (by linarith only [hb.hn100]) (by linarith only [hε32])
      nlinarith only [hpow, hb.hsqrtL_ge1]
    linarith only [h1, hdiv, hge1]
  have hLcap_ch : ((c.L_cap.choose 2 * c.C_int : ℕ) : ℝ) < (c.k : ℝ) := by
    push_cast
    have hch : (c.L_cap.choose 2 : ℝ) ≤ (c.L_cap : ℝ) ^ 2 / 2 := choose_two_le_half_sq _
    have hL2 : (c.L_cap : ℝ) ^ 2 ≤ 36 * (n : ℝ) ^ ((1 : ℝ) / 2 - 2 * ε) * L := by
      have h1 := pow_le_pow_left₀ (Nat.cast_nonneg _) hLcap_le 2
      have h2 : (6 * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) * Real.sqrt L) ^ 2 =
          36 * (n : ℝ) ^ ((1 : ℝ) / 2 - 2 * ε) * L := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hb.hLpos.le,
          ← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / 4 - ε)) 2, ← Real.rpow_mul hb.hnpos.le]
        norm_num; congr 2; ring
      linarith only [h1, h2]
    have hprod : (c.L_cap.choose 2 : ℝ) * (c.C_int : ℝ) ≤ 600 * (n : ℝ) ^ ((1 : ℝ) / 2 - 2 * ε) * L ^ 4 := by
      have h1 := mul_le_mul hch hb.hCint_le (Nat.cast_nonneg _) (by positivity)
      have h2 := mul_le_mul_of_nonneg_right (by linarith only [hL2] : (c.L_cap : ℝ) ^ 2 / 2 ≤ 18 * (n : ℝ) ^ ((1 : ℝ) / 2 - 2 * ε) * L)
        (show 0 ≤ 33 * L ^ 3 by have := hb.hLpos; positivity)
      have hpos : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 2 - 2 * ε) * L ^ 4 := by have := hb.hnpos; have := hb.hLpos; positivity
      linarith only [h1, h2, hpos, show (18 * (n : ℝ) ^ ((1 : ℝ) / 2 - 2 * ε) * L) * (33 * L ^ 3) =
        594 * (n : ℝ) ^ ((1 : ℝ) / 2 - 2 * ε) * L ^ 4 by ring]
    have hlt : 600 * (n : ℝ) ^ ((1 : ℝ) / 2 - 2 * ε) * L ^ 4 < (n : ℝ) ^ ((1 : ℝ) / 2) := by
      have hL4 : 0 < L ^ 4 := pow_pos hb.hLpos 4
      have h1 : 600 * L ^ 4 < (n : ℝ) ^ (2 * ε) := by linarith only [he.hLcap_big, hL4]
      have h2 : (n : ℝ) ^ ((1 : ℝ) / 2 - 2 * ε) * (n : ℝ) ^ (2 * ε) = (n : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_add hb.hnpos]; congr 1; ring
      have h3 := mul_lt_mul_of_pos_left h1 (Real.rpow_pos_of_pos hb.hnpos ((1 : ℝ) / 2 - 2 * ε))
      linarith only [h2, h3, show (n : ℝ) ^ ((1 : ℝ) / 2 - 2 * ε) * (600 * L ^ 4) =
        600 * (n : ℝ) ^ ((1 : ℝ) / 2 - 2 * ε) * L ^ 4 by ring]
    linarith only [hprod, hlt, hb.hk_ge_sqrtn]
  have hLcap : (c.k : ℝ) + ((c.L_cap.choose 2 * c.C_int : ℕ) : ℝ) < (c.L_cap : ℝ) * c.t₂ := by
    have h1 : 2 * (c.k : ℝ) ≤ (c.L_cap : ℝ) * c.t₂ := (div_le_iff₀ ht₂_pos).mp hLcap_ge
    linarith only [h1, hLcap_ch]
  have hHcap_ge : 3 * Real.sqrt L ≤ (c.H_cap : ℝ) := Nat.le_ceil _
  have hHcap_le : (c.H_cap : ℝ) ≤ 4 * Real.sqrt L := by
    have h1 : (c.H_cap : ℝ) < 3 * Real.sqrt L + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith only [h1, hb.hsqrtL_ge1]
  have hHcap_ch2 : (c.H_cap.choose 2 : ℝ) ≤ 8 * L := by
    have h1 := choose_two_le_half_sq c.H_cap
    have h2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hHcap_le 2
    rw [mul_pow, Real.sq_sqrt hb.hLpos.le] at h2
    linarith only [h1, h2]
  have ht1_eq : c.t₁ = (n : ℝ) ^ ((1 : ℝ) / 2) := hsqrtn_eq
  have hFthr_eq : c.Fthr = L := rfl
  have hNthr_eq : c.Nthr = (n : ℝ) ^ ((1 : ℝ) / 4 + ε) / L := rfl
  have hHcap : (c.k : ℝ) + ((c.H_cap.choose 2 * c.C_int : ℕ) : ℝ) < (c.H_cap : ℝ) * c.t₁ := by
    have h1 : 3 * Real.sqrt ((n : ℝ) * L) ≤ (c.H_cap : ℝ) * c.t₁ := by
      rw [hb.hS_eq, ht1_eq]
      have hmul := mul_le_mul_of_nonneg_right hHcap_ge hb.hsqrtn_pos.le
      linarith only [hmul]
    have h2 : ((c.H_cap.choose 2 * c.C_int : ℕ) : ℝ) < Real.sqrt ((n : ℝ) * L) := by
      push_cast
      have hprod := mul_le_mul hHcap_ch2 hb.hCint_le (Nat.cast_nonneg _) (by linarith only [hb.hLpos])
      have hL4 : 0 < L ^ 4 := pow_pos hb.hLpos 4
      have hlt : 264 * L ^ 4 < (n : ℝ) ^ ((1 : ℝ) / 2) := by
        have h3 : c.ε₁ * (n : ℝ) ^ ((1 : ℝ) / 2) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := by nlinarith only [hb.hε₁_le, hb.hsqrtn_pos]
        linarith only [h10000L4, h3, hL4]
      linarith only [hprod, hlt, hb.hS_ge_sqrtn, show 8 * L * (33 * L ^ 3) = 264 * L ^ 4 by ring]
    linarith only [h1, h2, hb.hk_le_2S]
  have hF2_sep : c.Nthr * (c.Fmax : ℝ) + (c.Dmax : ℝ) * c.Fthr ≤ c.t₁ := by
    have h1 : c.Nthr * (c.Fmax : ℝ) ≤ (1 / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
      have hN : c.Nthr * (c.Fmax : ℝ) ≤ 3 * (n : ℝ) ^ ((1 : ℝ) / 4 + ε) * L := by
        rw [hNthr_eq]
        calc (n : ℝ) ^ ((1 : ℝ) / 4 + ε) / L * (c.Fmax : ℝ)
            ≤ (n : ℝ) ^ ((1 : ℝ) / 4 + ε) / L * (3 * L ^ 2) :=
              mul_le_mul_of_nonneg_left hb.hFmax_le (by have := hb.hnpos; have := hb.hLpos; positivity)
          _ = 3 * (n : ℝ) ^ ((1 : ℝ) / 4 + ε) * L := by field_simp [hL_ne]
      have h2 : 6 * L ≤ (n : ℝ) ^ ((1 : ℝ) / 4 - ε) := by
        have hF2' : (200 / c.ε₁) * L ^ 3 ≤ (n : ℝ) ^ ((1 : ℝ) / 4 - ε) := he.hF2_big
        have hL12 : L ≤ L ^ 2 := by nlinarith only [hb.hL100]
        have hL13 : L ≤ L ^ 3 := by nlinarith only [hL12, hb.hL100]
        have h200 : 200 ≤ 200 / c.ε₁ := by
          have : 1 ≤ 1 / c.ε₁ := (one_le_div hb.hε₁_pos).mpr hb.hε₁_le
          linarith only [this, show 200 / c.ε₁ = 200 * (1 / c.ε₁) by ring]
        have hmul := mul_le_mul h200 hL13 hb.hLpos.le (by positivity)
        linarith only [hF2', hmul, hb.hLpos]
      have h3 : (n : ℝ) ^ ((1 : ℝ) / 4 + ε) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) = (n : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_add hb.hnpos]; congr 1; ring
      have h4 := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hb.hnpos.le ((1 : ℝ) / 4 + ε))
      linarith only [hN, h3, h4, show (n : ℝ) ^ ((1 : ℝ) / 4 + ε) * (6 * L) = 6 * (n : ℝ) ^ ((1 : ℝ) / 4 + ε) * L by ring]
    have h2 : (c.Dmax : ℝ) * c.Fthr ≤ (1 / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [hFthr_eq]
      have h3 : (c.Dmax : ℝ) * L ≤ (n : ℝ) ^ ((1 : ℝ) / 2) / Real.sqrt L := by
        calc (c.Dmax : ℝ) * L ≤ ((n : ℝ) ^ ((1 : ℝ) / 2) / (L * Real.sqrt L)) * L :=
              mul_le_mul_of_nonneg_right hb.hDmax_le hb.hLpos.le
          _ = (n : ℝ) ^ ((1 : ℝ) / 2) / Real.sqrt L := by field_simp [hL_ne, hsqrtL_ne]
      have h4 : (2 : ℝ) ≤ Real.sqrt L := by rw [Real.le_sqrt (by norm_num) hb.hLpos.le]; linarith only [hb.hL100]
      have h5 : (n : ℝ) ^ ((1 : ℝ) / 2) / Real.sqrt L ≤ (n : ℝ) ^ ((1 : ℝ) / 2) / 2 :=
        div_le_div_of_nonneg_left hb.hsqrtn_pos.le (by norm_num) h4
      linarith only [h3, h5]
    rw [ht1_eq]; linarith only [h1, h2]
  have hsqrtn_le_ε₁k : (n : ℝ) ^ ((1 : ℝ) / 2) ≤ c.ε₁ * (c.k : ℝ) := by
    have h1 : (n : ℝ) ^ ((1 : ℝ) / 2) ≤ (c.k : ℝ) / Real.sqrt L := by
      rw [le_div_iff₀ (Real.sqrt_pos.mpr hb.hLpos), ← hb.hS_eq]; exact hb.hk_ge_S
    calc (n : ℝ) ^ ((1 : ℝ) / 2) ≤ (c.k : ℝ) * (1 / Real.sqrt L) := by
          linarith only [h1, show (c.k : ℝ) / Real.sqrt L = (c.k : ℝ) * (1 / Real.sqrt L) by ring]
      _ ≤ (c.k : ℝ) * c.ε₁ := mul_le_mul_of_nonneg_left h1_div_sqrtL hb.hk_posR.le
      _ = c.ε₁ * (c.k : ℝ) := mul_comm _ _
  have hL_loss : (c.t₁ / 2) * ((c.k : ℝ) + ((c.L_cap.choose 2 * c.C_int : ℕ) : ℝ)) ≤ c.ε₁ * (c.k : ℝ) ^ 2 := by
    rw [ht1_eq]
    have h1 : ((n : ℝ) ^ ((1 : ℝ) / 2) / 2) * ((c.k : ℝ) + ((c.L_cap.choose 2 * c.C_int : ℕ) : ℝ)) ≤
        (n : ℝ) ^ ((1 : ℝ) / 2) * (c.k : ℝ) := by
      nlinarith only [hb.hsqrtn_pos, hLcap_ch]
    nlinarith only [h1, hsqrtn_le_ε₁k, hb.hk_posR]
  have hM_loss : (c.t₂ / 2) * c.Ylim ≤ c.ε₁ * (c.k : ℝ) ^ 2 := by
    have hprod : c.t₂ * c.Ylim = (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
      have ht2_eq : c.t₂ = (n : ℝ) ^ ((1 : ℝ) / 4 + ε) := rfl
      have hY_eq : c.Ylim = (c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) := rfl
      rw [ht2_eq, hY_eq]
      have h1 : (n : ℝ) ^ ((1 : ℝ) / 4 + ε) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) = (n : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_add hb.hnpos]; congr 1; ring
      rw [show (n : ℝ) ^ ((1 : ℝ) / 4 + ε) * ((c.k : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε)) =
        (c.k : ℝ) * ((n : ℝ) ^ ((1 : ℝ) / 4 + ε) * (n : ℝ) ^ ((1 : ℝ) / 4 - ε)) by ring, h1]
    have hrew : (c.t₂ / 2) * c.Ylim = (1 / 2) * (c.t₂ * c.Ylim) := by ring
    rw [hrew, hprod]
    nlinarith only [hsqrtn_le_ε₁k, hb.hk_posR, hb.hsqrtn_pos]
  have hS_loss : (c.k : ℝ) * c.t₃ ^ 2 + (c.k : ℝ) * (c.Fmax : ℝ) +
      (c.k.choose 2 : ℝ) * (2 * (c.m : ℝ) * c.p ^ 2) + c.t_small ≤ c.ε₁ * (c.k : ℝ) ^ 2 := by
    have h1 : (c.k : ℝ) * c.t₃ ^ 2 ≤ (c.ε₁ / 6) * (c.k : ℝ) ^ 2 := by
      have ht3_2 : c.t₃ ^ 2 = (n : ℝ) ^ (4 * ε) := by
        have ht3 : c.t₃ = (n : ℝ) ^ (2 * ε) := rfl
        rw [ht3, ← Real.rpow_natCast ((n : ℝ) ^ (2 * ε)) 2, ← Real.rpow_mul hb.hnpos.le]; congr 1; norm_num; ring
      have hsm1' : 20 / c.ε₁ ≤ (n : ℝ) ^ ((1 : ℝ) / 2 - 4 * ε) := by
        have h0 : 20 / c.ε₁ * L ^ 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 2 - 4 * ε) := he.hsm1_big
        simpa [pow_zero] using h0
      have h2 : 20 ≤ c.ε₁ * (n : ℝ) ^ ((1 : ℝ) / 2 - 4 * ε) := by
        have hmul := mul_le_mul_of_nonneg_right hsm1' hb.hε₁_pos.le
        have hcancel : (20 / c.ε₁) * c.ε₁ = 20 := by field_simp [hε₁_ne]
        linarith only [hmul, hcancel]
      have h3 : (n : ℝ) ^ (4 * ε) * (n : ℝ) ^ ((1 : ℝ) / 2 - 4 * ε) = (n : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_add hb.hnpos]; congr 1; ring
      have h4 : c.t₃ ^ 2 ≤ (c.ε₁ / 6) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [ht3_2]
        have hmul := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hb.hnpos.le (4 * ε))
        have hpos : 0 ≤ (n : ℝ) ^ (4 * ε) := Real.rpow_nonneg hb.hnpos.le _
        linarith only [hmul, hpos, show (n : ℝ) ^ (4 * ε) * (c.ε₁ * (n : ℝ) ^ ((1 : ℝ) / 2 - 4 * ε)) =
          c.ε₁ * (n : ℝ) ^ ((1 : ℝ) / 2) by rw [mul_comm c.ε₁, ← mul_assoc, h3, mul_comm]]
      have h5 := h4.trans (mul_le_mul_of_nonneg_left hb.hk_ge_sqrtn (by linarith only [hb.hε₁_pos]))
      nlinarith only [h5, hb.hk_posR]
    have h2 : (c.k : ℝ) * (c.Fmax : ℝ) ≤ (c.ε₁ / 6) * (c.k : ℝ) ^ 2 := by
      have hL2_ge1 : 1 ≤ L ^ 2 := by nlinarith only [hb.hL100]
      have hL24 : L ^ 2 ≤ L ^ 4 := by nlinarith only [hL2_ge1]
      have h3 : (c.Fmax : ℝ) ≤ (c.ε₁ / 6) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
        linarith only [hb.hFmax_le, hL24, h10000L4, show 0 ≤ L ^ 4 by positivity]
      have h4 := h3.trans (mul_le_mul_of_nonneg_left hb.hk_ge_sqrtn (by linarith only [hb.hε₁_pos]))
      nlinarith only [h4, hb.hk_posR]
    have h3 : (c.k.choose 2 : ℝ) * (2 * (c.m : ℝ) * c.p ^ 2) ≤ (c.ε₁ / 6) * (c.k : ℝ) ^ 2 := by
      have hmp2 : 2 * (c.m : ℝ) * c.p ^ 2 ≤ 1 / (2 * L) := by
        calc 2 * (c.m : ℝ) * c.p ^ 2 ≤ 2 * ((n : ℝ) / L ^ 2) * c.p ^ 2 := by
              have := mul_le_mul_of_nonneg_right hb.hm_le (sq_nonneg c.p); linarith only [this]
          _ = 2 * (c.p ^ 2 * (n : ℝ)) / L ^ 2 := by ring
          _ = 2 * (L / 4) / L ^ 2 := by rw [hb.hp_sq]
          _ = 1 / (2 * L) := by field_simp [hL_ne]; ring
      have hch := choose_two_le_half_sq c.k
      have hL_ge : 1 / (4 * L) ≤ c.ε₁ / 6 := by
        rw [div_le_div_iff₀ (by linarith only [hb.hLpos] : 0 < 4 * L) (by norm_num)]
        linarith only [h100_le_ε₁L]
      calc (c.k.choose 2 : ℝ) * (2 * (c.m : ℝ) * c.p ^ 2)
          ≤ ((c.k : ℝ) ^ 2 / 2) * (1 / (2 * L)) := mul_le_mul hch hmp2 (by positivity) (by positivity)
        _ = (1 / (4 * L)) * (c.k : ℝ) ^ 2 := by ring
        _ ≤ (c.ε₁ / 6) * (c.k : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hL_ge (sq_nonneg _)
    have h4 : c.t_small = (c.ε₁ / 2) * (c.k : ℝ) ^ 2 := rfl
    linarith only [h1, h2, h3, h4]
  have hHD_le : ((c.H_cap * c.Dmax : ℕ) : ℝ) ≤ (4 / L) * (c.k : ℝ) := by
    push_cast
    calc (c.H_cap : ℝ) * (c.Dmax : ℝ)
        ≤ (4 * Real.sqrt L) * ((n : ℝ) ^ ((1 : ℝ) / 2) / (L * Real.sqrt L)) :=
          mul_le_mul hHcap_le hb.hDmax_le (Nat.cast_nonneg _) (by positivity)
      _ = (4 / L) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
          field_simp [hL_ne, hsqrtL_ne]
      _ ≤ (4 / L) * (c.k : ℝ) := mul_le_mul_of_nonneg_left hb.hk_ge_sqrtn (by have := hb.hLpos; positivity)
  have hH_same_loss : ((c.H_cap * c.Dmax : ℕ) : ℝ) ^ 2 / 2 ≤ c.ε₁ * (c.k : ℝ) ^ 2 := by
    have h1 := pow_le_pow_left₀ (Nat.cast_nonneg _) hHD_le 2
    have h2 : 8 / L ^ 2 ≤ c.ε₁ := by
      rw [div_le_iff₀ (sq_pos_of_pos hb.hLpos)]
      nlinarith only [h100_le_ε₁L, hb.hL100]
    calc ((c.H_cap * c.Dmax : ℕ) : ℝ) ^ 2 / 2
        ≤ ((4 / L) * (c.k : ℝ)) ^ 2 / 2 := by linarith only [h1]
      _ = (8 / L ^ 2) * (c.k : ℝ) ^ 2 := by ring
      _ ≤ c.ε₁ * (c.k : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have hH_cross_delta : ((c.H_cap * c.Dmax + c.H_cap.choose 2 * c.C_proj : ℕ) : ℝ) ≤ (c.ε₁ / 4) * (c.k : ℝ) := by
    push_cast
    have h1 : (c.H_cap : ℝ) * (c.Dmax : ℝ) ≤ (c.ε₁ / 8) * (c.k : ℝ) := by
      have h4L : 4 / L ≤ c.ε₁ / 8 := by
        rw [div_le_div_iff₀ hb.hLpos (by norm_num)]; linarith only [h100_le_ε₁L]
      have hHD' : (c.H_cap : ℝ) * (c.Dmax : ℝ) ≤ (4 / L) * (c.k : ℝ) := by simpa using hHD_le
      exact hHD'.trans (mul_le_mul_of_nonneg_right h4L hb.hk_posR.le)
    have h2 : (c.H_cap.choose 2 : ℝ) * (c.C_proj : ℝ) ≤ (c.ε₁ / 8) * (c.k : ℝ) := by
      have hprod := mul_le_mul hHcap_ch2 hb.hCproj_le (Nat.cast_nonneg _) (by linarith only [hb.hLpos])
      have hL4 : 0 ≤ L ^ 4 := pow_nonneg hb.hLpos.le 4
      have h3 : (c.H_cap.choose 2 : ℝ) * (c.C_proj : ℝ) ≤ (c.ε₁ / 8) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
        linarith only [hprod, h10000L4, hL4, show 8 * L * (54 * L ^ 3) = 432 * L ^ 4 by ring]
      exact h3.trans (mul_le_mul_of_nonneg_left hb.hk_ge_sqrtn (by linarith only [hb.hε₁_pos]))
    linarith only [h1, h2]
  have hQ_loss : ((c.k : ℝ) / c.Fthr + (c.L_cap : ℝ) + (c.H_cap : ℝ)) * (c.k : ℝ) ≤ c.ε₁ * (c.k : ℝ) ^ 2 := by
    have h1 : (c.k : ℝ) / c.Fthr ≤ (c.ε₁ / 3) * (c.k : ℝ) := by
      rw [hFthr_eq, div_le_iff₀ hb.hLpos]
      nlinarith only [h100_le_ε₁L, hb.hk_posR]
    have h2 : (c.L_cap : ℝ) ≤ (c.ε₁ / 3) * (c.k : ℝ) := by
      have hq1' : (30 / c.ε₁) * L ≤ (n : ℝ) ^ ((1 : ℝ) / 4 + ε) := by
        have h0 : (30 / c.ε₁) * L ^ 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 4 + ε) := he.hq1_big
        simpa [pow_one] using h0
      have h3 : 30 * L ≤ c.ε₁ * (n : ℝ) ^ ((1 : ℝ) / 4 + ε) := by
        have hmul := mul_le_mul_of_nonneg_right hq1' hb.hε₁_pos.le
        have hcancel : (30 / c.ε₁) * L * c.ε₁ = 30 * L := by field_simp [hε₁_ne]
        linarith only [hmul, hcancel]
      have h4 : (n : ℝ) ^ ((1 : ℝ) / 4 - ε) * (n : ℝ) ^ ((1 : ℝ) / 4 + ε) = (n : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_add hb.hnpos]; congr 1; ring
      have h5 : 6 * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) * L ≤ (c.ε₁ / 3) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
        have hmul := mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hb.hnpos.le ((1 : ℝ) / 4 - ε))
        have hpos : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 4 - ε) * L := by have := hb.hnpos; have := hb.hLpos; positivity
        linarith only [hmul, hpos, show (n : ℝ) ^ ((1 : ℝ) / 4 - ε) * (30 * L) = 30 * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) * L by ring,
          show (n : ℝ) ^ ((1 : ℝ) / 4 - ε) * (c.ε₁ * (n : ℝ) ^ ((1 : ℝ) / 4 + ε)) = c.ε₁ * (n : ℝ) ^ ((1 : ℝ) / 2) by
            rw [mul_comm c.ε₁, ← mul_assoc, h4, mul_comm]]
      have hLcap' : (c.L_cap : ℝ) ≤ 6 * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) * L := by
        have hpos : 0 ≤ 6 * (n : ℝ) ^ ((1 : ℝ) / 4 - ε) := by have := hb.hnpos; positivity
        nlinarith only [hLcap_le, hb.hsqrtL_leL, hpos]
      exact hLcap'.trans (h5.trans (mul_le_mul_of_nonneg_left hb.hk_ge_sqrtn (by linarith only [hb.hε₁_pos])))
    have h3 : (c.H_cap : ℝ) ≤ (c.ε₁ / 3) * (c.k : ℝ) := by
      have hL2 : L ≤ L ^ 2 := by nlinarith only [hb.hL100]
      have hL2_ge1 : 1 ≤ L ^ 2 := by nlinarith only [hb.hL100]
      have hL3 : L ^ 2 ≤ L ^ 4 := by nlinarith only [hL2_ge1]
      have hL14 : L ≤ L ^ 4 := by linarith only [hL2, hL3]
      have h4 : (c.H_cap : ℝ) ≤ (c.ε₁ / 3) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
        linarith only [hHcap_le, hb.hsqrtL_leL, hL14, h10000L4, show 0 ≤ L ^ 4 by positivity]
      exact h4.trans (mul_le_mul_of_nonneg_left hb.hk_ge_sqrtn (by linarith only [hb.hε₁_pos]))
    have hsum : (c.k : ℝ) / c.Fthr + (c.L_cap : ℝ) + (c.H_cap : ℝ) ≤ c.ε₁ * (c.k : ℝ) := by linarith only [h1, h2, h3]
    nlinarith only [hsum, hb.hk_posR]
  have h1_le_ε₁k : 1 ≤ c.ε₁ * (c.k : ℝ) := by
    have h1 : 1 / c.ε₁ ≤ 100 / (ε ^ 2 * c.ε₁) := by
      rw [div_le_div_iff₀ hb.hε₁_pos (by have := hb.hε₁_pos; positivity)]
      have hε2 : ε ^ 2 ≤ 1 := by nlinarith only [hε0, hε32]
      nlinarith only [hε2, hb.hε₁_pos]
    have h2 : 1 / c.ε₁ ≤ (c.k : ℝ) := by linarith only [h1, hb.hsqrtn_big, hb.hk_ge_sqrtn]
    exact (div_le_iff₀ hb.hε₁_pos).mp h2 |>.trans_eq (mul_comm _ _)
  have hHalf_k : (c.k : ℝ) / 2 ≤ c.ε₁ * (c.k : ℝ) ^ 2 := by nlinarith only [h1_le_ε₁k, hb.hk_posR]
  have hOne_le : 1 ≤ c.ε₁ * (c.k : ℝ) ^ 2 := by nlinarith only [hHalf_k, hb.hk_ge100]
  -- Lemma 4.2 bounds
  have hpk_low : (1 + 7 * ε / 8) * (L / 2) ≤ c.p * (c.k : ℝ) := by
    calc (1 + 7 * ε / 8) * (L / 2) = c.p * ((1 + 7 * ε / 8) * Real.sqrt ((n : ℝ) * L)) := by rw [← hb.hpS_eq]; ring
      _ ≤ c.p * (c.k : ℝ) := mul_le_mul_of_nonneg_left hb.hk_low hb.hp0
  have hpk_high : c.p * (c.k : ℝ) ≤ (1 + ε) * (L / 2) := by
    calc c.p * (c.k : ℝ) ≤ c.p * ((1 + ε) * Real.sqrt ((n : ℝ) * L)) := mul_le_mul_of_nonneg_left hb.hk_le hb.hp0
      _ = (1 + ε) * (L / 2) := by rw [← hb.hpS_eq]; ring
  have h_n_div_k : (n : ℝ) / (c.k : ℝ) ≤ Real.exp (L / 2) := by
    have hexp_half : Real.exp (L / 2) = (n : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [Real.rpow_def_of_pos hb.hnpos]; congr 1; ring
    rw [hexp_half, div_le_iff₀ hb.hk_posR]
    have hsq : (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) = (n : ℝ) := by
      rw [← Real.rpow_add hb.hnpos]; norm_num
    nlinarith only [hsq, hb.hk_ge_sqrtn, hb.hsqrtn_pos]
  have h_k_div_m : (c.k : ℝ) / (c.m : ℝ) ≤ Real.exp (-(1 / 2 - ε ^ 3 / 40) * L) := by
    have hexp_eq : Real.exp (-(1 / 2 - ε ^ 3 / 40) * L) = (n : ℝ) ^ (ε ^ 3 / 40) / (n : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_sub hb.hnpos, Real.rpow_def_of_pos hb.hnpos]; congr 1; ring
    rw [hexp_eq]
    have hk_2nL : (c.k : ℝ) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 2) * L := by
      have := hb.hk_le_2S; rw [hb.hS_eq] at this; nlinarith only [this, hb.hsqrtL_leL, hb.hsqrtn_pos]
    have h1 : (c.k : ℝ) / (c.m : ℝ) ≤ (2 * (n : ℝ) ^ ((1 : ℝ) / 2) * L) / ((1 / 2) * ((n : ℝ) / L ^ 2)) :=
      div_le_div₀ (by have := hb.hsqrtn_pos; have := hb.hLpos; positivity) hk_2nL
        (by have := hb.hnpos; have := hb.hLpos; positivity) hb.hm_ge
    have h2 : (2 * (n : ℝ) ^ ((1 : ℝ) / 2) * L) / ((1 / 2) * ((n : ℝ) / L ^ 2)) =
        4 * L ^ 3 / (n : ℝ) ^ ((1 : ℝ) / 2) := by
      have hsq : (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) = (n : ℝ) := by
        rw [← Real.rpow_add hb.hnpos]; norm_num
      field_simp [hb.hLpos.ne', hb.hnpos.ne', hb.hsqrtn_pos.ne']
      nlinarith only [hsq, show 0 ≤ L ^ 3 by positivity]
    exact h1.trans (h2.le.trans (div_le_div_of_nonneg_right he.hkm_exp_big hb.hsqrtn_pos.le))
  have h_e3_le : Real.exp 3 ≤ Real.exp ((ε ^ 3 / 40) * L) := by
    apply Real.exp_le_exp.mpr
    have h1 := (div_le_iff₀ (pow_pos hε0 3)).mp hb.hL_ε3
    linarith only [h1]
  have h_final_sum : 2 * (c.k : ℝ) ^ 2 * Real.exp (-(ε ^ 2 / 8) * (c.k : ℝ) * L) < 1 / 4 := by
    have h8k2 : 8 * (c.k : ℝ) ^ 2 ≤ Real.exp (2 * L) := by
      have hsq : Real.exp (2 * L) = (n : ℝ) ^ 2 := by
        rw [show (2 : ℝ) * L = L + L by ring, Real.exp_add, hb.hexpL, sq]
      rw [hsq]
      have h1 : (c.k : ℝ) ^ 2 ≤ 4 * (n : ℝ) * L := by
        have h2 := pow_le_pow_left₀ hb.hk_posR.le hb.hk_le_2S 2
        rw [mul_pow, Real.sq_sqrt (by have := hb.hnpos; have := hb.hLpos; positivity)] at h2
        linarith only [h2]
      have h100 : 100 * L ^ 2 ≤ (n : ℝ) := by simpa [Real.rpow_one] using he.hm_big
      have h2 : 32 * L ≤ (n : ℝ) := by nlinarith only [h100, hb.hL100]
      nlinarith only [h1, h2, hb.hnpos]
    have hexp_lt : 2 * L < (ε ^ 2 / 8) * (c.k : ℝ) * L := by
      have h1 : 16 / ε ^ 2 < (c.k : ℝ) := by
        have h2 : 16 / ε ^ 2 < 100 / (ε ^ 2 * c.ε₁) := by
          rw [div_lt_div_iff₀ (sq_pos_of_pos hε0) (by have := hb.hε₁_pos; positivity)]
          have hε2_pos : 0 < ε ^ 2 := sq_pos_of_pos hε0
          nlinarith only [hε2_pos, hb.hε₁_le]
        linarith only [h2, hb.hsqrtn_big, hb.hk_ge_sqrtn]
      have h2 : 16 < ε ^ 2 * (c.k : ℝ) := by
        have := (div_lt_iff₀ (sq_pos_of_pos hε0)).mp h1; linarith only [this]
      nlinarith only [h2, hb.hLpos]
    have hprod : 8 * (c.k : ℝ) ^ 2 * Real.exp (-(ε ^ 2 / 8) * (c.k : ℝ) * L) < 1 := by
      calc 8 * (c.k : ℝ) ^ 2 * Real.exp (-(ε ^ 2 / 8) * (c.k : ℝ) * L)
          ≤ Real.exp (2 * L) * Real.exp (-(ε ^ 2 / 8) * (c.k : ℝ) * L) :=
            mul_le_mul_of_nonneg_right h8k2 (Real.exp_pos _).le
        _ = Real.exp (2 * L - (ε ^ 2 / 8) * (c.k : ℝ) * L) := by rw [← Real.exp_add]; congr 1; ring
        _ < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith only [hexp_lt])
        _ = 1 := Real.exp_zero
    linarith only [hprod]
  exact ⟨hLcap, hHcap, hF2_sep, hL_loss, hM_loss, hS_loss, hH_same_loss, hH_cross_delta,
    hQ_loss, hHalf_k, hOne_le, hpk_low, hpk_high, h_n_div_k, h_k_div_m, h_e3_le, h_final_sum⟩

/-- For any `0 < ε ≤ 1 / 32`, `mkCfg ε n` is valid for all sufficiently large `n`. -/
lemma eventually_validCfg {ε : ℝ} (hε0 : 0 < ε) (hε32 : ε ≤ 1 / 32) :
    ∀ᶠ n : ℕ in Filter.atTop, ValidCfg (mkCfg ε n) := by
  filter_upwards [eventually_asymptoticEnv hε0 hε32] with n he
  have hb := mkCfgBase_of_env hε0 hε32 he
  obtain ⟨hPr_fiber, hPr_deg, hPr_codeg, hPr_cross, hPr_proj⟩ := mkCfg_prob1 hε0 hε32 he hb
  obtain ⟨ht_med1, hMed_ht₂, hMed_b₀_ge, hMed_b₀_le, hMed_tmed_le, hPr_med, hPr_small⟩ := mkCfg_prob2 hε0 hε32 he hb
  obtain ⟨hLcap, hHcap, hF2_sep, hL_loss, hM_loss, hS_loss, hH_same_loss, hH_cross_delta,
    hQ_loss, hHalf_k, hOne_le, hpk_low, hpk_high, h_n_div_k, h_k_div_m, h_e3_le, h_final_sum⟩ :=
    mkCfg_det_and_RI hε0 hε32 he hb
  exact
    { hn := by have := he.hn; change 3 ≤ n; omega
      hm := by have := hb.hm_nat; omega
      hk1 := hb.hk1
      hkm := hb.hkm
      hε0 := hε0
      hε32 := hε32
      hr_eq := rfl
      hε₁_eq := rfl
      hε₂_eq := rfl
      hp0 := hb.hp0
      hp1 := hb.hp_le1
      ht₁0 := Real.sqrt_nonneg _
      ht₂0 := Real.rpow_pos_of_pos hb.hnpos _
      ht₃0 := Real.rpow_pos_of_pos hb.hnpos _
      ht_small0 := by dsimp only [mkCfg]; have := hb.hε₁_pos; positivity
      hFthr0 := hb.hLpos
      hNthr_eq := rfl
      ht_codeg1 := hb.ht_codeg1
      ht_cross1 := hb.ht_cross1
      ht_proj1 := hb.ht_proj1
      ht_med1 := ht_med1
      hFmax_ge := hb.hFmax_ge
      hDmax_ge := hb.hDmax_ge
      hNmax_ge := hb.hNmax_ge
      hM₁_eq := rfl
      hPr_fiber := hPr_fiber
      hPr_deg := hPr_deg
      hPr_codeg := hPr_codeg
      hPr_cross := hPr_cross
      hPr_proj := hPr_proj
      hMed_ht₂ := hMed_ht₂
      hMed_b₀_ge := hMed_b₀_ge
      hMed_b₀_le := hMed_b₀_le
      hMed_tmed_le := hMed_tmed_le
      hPr_med := hPr_med
      hPr_small := hPr_small
      hLcap := hLcap
      hHcap := hHcap
      hF2_sep := hF2_sep
      hL_loss := hL_loss
      hM_loss := hM_loss
      hS_loss := hS_loss
      hH_same_loss := hH_same_loss
      hH_cross_delta := hH_cross_delta
      hQ_loss := hQ_loss
      hHalf_k := hHalf_k
      hOne_le := hOne_le
      hp_sq := hb.hp_sq
      hpk_low := hpk_low
      hpk_high := hpk_high
      h_n_div_k := h_n_div_k
      h_k_div_m := h_k_div_m
      h_e3_le := h_e3_le
      h_final_sum := h_final_sum }

/-- Theorem 1.3 (`AlphaBound`) of Hefty–Horn–King–Pfender:
for every `ε > 0` and all sufficiently large `n`, there exists a triangle-free graph on `Fin n`
whose every independent set has size strictly less than `(1 + ε) * √(n * log n)`. -/
theorem prove_alphaBound :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧
        ∀ I : Finset (Fin n), G.IsIndepSet (↑I : Set (Fin n)) →
          (I.card : ℝ) < (1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
  intro ε hε
  set ε' : ℝ := min ε (1 / 32)
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'32 : ε' ≤ 1 / 32 := min_le_right _ _
  have hε'le : ε' ≤ ε := min_le_left _ _
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp (eventually_validCfg hε'0 hε'32)
  refine ⟨n₀, fun n hn => ?_⟩
  have hvalid : ValidCfg (mkCfg ε' n) := hn₀ n hn
  obtain ⟨G, htri, hind⟩ := exists_good_graph_of_validCfg hvalid
  refine ⟨G, htri, fun I hI => ?_⟩
  have hlt_k : (I.card : ℝ) < ((mkCfg ε' n).k : ℝ) := by exact_mod_cast hind I hI
  have hk_le : ((mkCfg ε' n).k : ℝ) ≤ (1 + ε') * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
    Nat.floor_le (by positivity)
  have hle_ε : (1 + ε') * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
      (1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  linarith

end AsymptoticInstantiation

end Erdos1013Assembly

open Filter SimpleGraph
open scoped Real
namespace Erdos1104

theorem card_le_indepNum_mul_maxChromatic {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 3) : n ≤ G.indepNum * triangleFreeMaxChromatic n := by
  classical
  let k := G.chromaticNumber.toNat
  obtain ⟨C⟩ := G.colorable_chromaticNumber_of_fintype
  have hk : (k : ℕ∞) = G.chromaticNumber :=
    ENat.natCast_toNat (ne_top_of_le_ne_top (by simp) G.chromaticNumber_le_card)
  have hmax : k ≤ triangleFreeMaxChromatic n := by
    apply le_csSup (a := k)
    · refine ⟨n, ?_⟩
      rintro m ⟨H, -, he⟩
      have h := H.chromaticNumber_le_card
      simpa [he] using h
    · exact ⟨G, hG, hk.symm⟩
  have hf (b : Fin k) : (Finset.univ.filter (fun a => C a = b)).card ≤ G.indepNum := by
    apply IsIndepSet.card_le_indepNum
    simpa [Coloring.colorClass] using C.isIndepSet_colorClass b
  calc
    n = ∑ b : Fin k, (Finset.univ.filter (fun a => C a = b)).card := by
      simpa using (Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
        (f := fun a => C a) (by simp))
    _ ≤ ∑ _b : Fin k, G.indepNum := Finset.sum_le_sum fun b _ => hf b
    _ = G.indepNum * k := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ hmax

theorem lower_of_independent_sets
    (witness : ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n),
      G.CliqueFree 3 ∧ (G.indepNum : ℝ) ≤
        (1 + δ) * Real.sqrt (n : ℝ) * Real.sqrt (Real.log (n : ℝ))) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (1 - ε) * Real.sqrt (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) ≤
        (triangleFreeMaxChromatic n : ℝ) := by
  intro ε hε
  filter_upwards [witness ε hε, eventually_ge_atTop 2] with n ⟨G, hG, hα⟩ hn
  have hn' : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hx : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hy := Real.sqrt_pos.2 (Real.log_pos hn')
  have hc : (n : ℝ) ≤ (G.indepNum : ℝ) * (triangleFreeMaxChromatic n : ℝ) := by
    exact_mod_cast card_le_indepNum_mul_maxChromatic G hG
  have hprod := hc.trans (mul_le_mul_of_nonneg_right hα (by positivity))
  have hsq := Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ n)
  have hdivide : Real.sqrt (n : ℝ) ≤ (1+ε) * Real.sqrt (Real.log (n : ℝ)) *
      (triangleFreeMaxChromatic n : ℝ) := by
    apply (le_of_mul_le_mul_left ?_ hx)
    calc
      _ = (n : ℝ) := hsq
      _ ≤ _ := hprod.trans_eq (by ring)
  apply (div_le_iff₀ hy).2
  by_cases he : ε ≤ 1
  · have h := mul_le_mul_of_nonneg_left hdivide (sub_nonneg.2 he)
    nlinarith [mul_nonneg (sq_nonneg ε)
      (mul_nonneg hy.le (Nat.cast_nonneg (triangleFreeMaxChromatic n) : (0 : ℝ) ≤ _))]
  · exact le_trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) hx.le) (by positivity)

end Erdos1104


theorem OMA.solution : type_of% @Erdos1104.erdos_1104.variants.lower := by
  apply Erdos1104.lower_of_independent_sets
  intro δ hδ
  obtain ⟨N, hN⟩ := Erdos1013Assembly.prove_alphaBound δ hδ
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  obtain ⟨G, htri, hind⟩ := hN n hn
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  refine ⟨G, htri, ?_⟩
  have hb := (hind I hI.isIndepSet).le
  simpa [hI.card_eq, Real.sqrt_mul (Nat.cast_nonneg n), mul_assoc] using hb
