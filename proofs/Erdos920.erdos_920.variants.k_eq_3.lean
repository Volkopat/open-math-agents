import FormalConjectures.ErdosProblems.«920»
import Mathlib

-- Problem: Erdős Problem 920 — k eq 3
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/920.lean:78 (declaration Erdos920.erdos_920.variants.k_eq_3)
-- Credit: @gdyan2022

/-!
Proof of `Erdos920.erdos_920.variants.k_eq_3`:
`f 3 n = Θ(√(n / log n))`, combining:
1. A self-contained, nibble-free proof of Kim's lower bound (`H1`: for large `n`, there exists a
   triangle-free graph on `Fin n` with independence number `≤ C √(n log n)`), using two independent
   random blow-ups of `G(m, p)` with `m ≈ n / (α log n)` and `p = √(log n / n)`, vertex-order
   triangle pruning, minority-color deletion, a convexity/random-bipartition codegree-sum bound,
   and a sequential-exposure supermartingale.
2. Shearer's upper bound (`H2`: every triangle-free graph on `m` vertices has an independent set
   of size `≥ √(m log m) / 15`) and greedy colouring (`H1 → H2 → f 3 n = Θ(√(n / log n))`).
-/

namespace Erdos920Full

open Real Filter Finset
open scoped Classical

/- ### Section 1: Finite Bernoulli Product & Uniform Map Probability Toolkit -/

section FiniteBernoulli

/-- Product Bernoulli(`p`) weight on `X → Bool`. -/
noncomputable def bernW {X : Type*} [Fintype X] (p : ℝ) (ω : X → Bool) : ℝ :=
  ∏ x : X, if ω x then p else 1 - p

/-- Product Bernoulli(`p`) probability of a predicate `P` on `X → Bool`. -/
noncomputable def bernProb {X : Type*} [Fintype X] [DecidableEq X] (p : ℝ) (P : (X → Bool) → Prop) : ℝ :=
  ∑ ω : X → Bool, if P ω then bernW p ω else 0

/-- Product Bernoulli(`p`) expectation of `f : (X → Bool) → ℝ`. -/
noncomputable def bernExp {X : Type*} [Fintype X] [DecidableEq X] (p : ℝ) (f : (X → Bool) → ℝ) : ℝ :=
  ∑ ω : X → Bool, bernW p ω * f ω

lemma bernW_nonneg {X : Type*} [Fintype X] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ω : X → Bool) :
    0 ≤ bernW p ω := by
  refine Finset.prod_nonneg fun x _ => ?_
  cases ω x <;> simp <;> linarith

lemma sum_bernW_eq_one {X : Type*} [Fintype X] [DecidableEq X] (p : ℝ) :
    ∑ ω : X → Bool, bernW p ω = 1 := by
  have h := Fintype.prod_sum (fun (_ : X) (b : Bool) => if b then p else 1 - p)
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false] at h
  change ∑ ω : X → Bool, ∏ x : X, (if ω x then p else 1 - p) = 1
  rw [← h]
  simp

lemma bernProb_nonneg {X : Type*} [Fintype X] [DecidableEq X] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : (X → Bool) → Prop) : 0 ≤ bernProb p P :=
  Finset.sum_nonneg fun ω _ => by split_ifs; exact bernW_nonneg hp0 hp1 ω; exact le_rfl

lemma bernProb_mono {X : Type*} [Fintype X] [DecidableEq X] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {P Q : (X → Bool) → Prop} (h : ∀ ω, P ω → Q ω) :
    bernProb p P ≤ bernProb p Q := by
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hP : P ω
  · rw [if_pos hP, if_pos (h ω hP)]
  · rw [if_neg hP]
    split_ifs
    · exact bernW_nonneg hp0 hp1 ω
    · exact le_rfl

lemma bernProb_or_le {X : Type*} [Fintype X] [DecidableEq X] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P Q : (X → Bool) → Prop) :
    bernProb p (fun ω => P ω ∨ Q ω) ≤ bernProb p P + bernProb p Q := by
  rw [bernProb, bernProb, bernProb, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  have hw := bernW_nonneg hp0 hp1 ω
  by_cases hP : P ω <;> by_cases hQ : Q ω <;> simp [hP, hQ]
  exact hw

lemma bernProb_exists_le {X ι : Type*} [Fintype X] [DecidableEq X] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (s : Finset ι) (P : ι → (X → Bool) → Prop) :
    bernProb p (fun ω => ∃ i ∈ s, P i ω) ≤ ∑ i ∈ s, bernProb p (P i) := by
  simp only [bernProb]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hex : ∃ i ∈ s, P i ω
  · rw [if_pos hex]
    rcases hex with ⟨i₀, hi₀, hPi₀⟩
    calc bernW p ω = (if P i₀ ω then bernW p ω else 0) := by rw [if_pos hPi₀]
      _ ≤ ∑ i ∈ s, if P i ω then bernW p ω else 0 :=
          Finset.single_le_sum (f := fun i => if P i ω then bernW p ω else 0)
            (fun i _ => by split_ifs; exact bernW_nonneg hp0 hp1 ω; exact le_rfl) hi₀
  · rw [if_neg hex]
    exact Finset.sum_nonneg fun i _ => by split_ifs; exact bernW_nonneg hp0 hp1 ω; exact le_rfl

lemma bernProb_markov {X : Type*} [Fintype X] [DecidableEq X] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f : (X → Bool) → ℝ} (hf : ∀ ω, 0 ≤ f ω) {t : ℝ} (ht : 0 < t) :
    bernProb p (fun ω => t ≤ f ω) ≤ bernExp p f / t := by
  rw [le_div_iff₀ ht, bernProb, bernExp, Finset.sum_mul]
  refine Finset.sum_le_sum fun ω _ => ?_
  have hw := bernW_nonneg hp0 hp1 ω
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left h hw
  · rw [zero_mul]; exact mul_nonneg hw (hf ω)

lemma bernW_equiv_comp {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) (p : ℝ) (ω : Y → Bool) :
    bernW p (ω ∘ e) = bernW p ω := by
  simp only [bernW, Function.comp]
  exact Equiv.prod_comp e (fun y => if ω y then p else 1 - p)

lemma bernW_sum_split {A B : Type*} [Fintype A] [Fintype B] (p : ℝ) (ω : A ⊕ B → Bool) :
    bernW p ω = bernW p (fun a => ω (Sum.inl a)) * bernW p (fun b => ω (Sum.inr b)) := by
  simp only [bernW, Fintype.prod_sum_type]

/-- Reindexing `bernProb` along an equivalence `e : X ≃ Y`. -/
lemma bernProb_equiv {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) (p : ℝ) (P : (Y → Bool) → Prop) :
    bernProb p P = bernProb p (fun ω : X → Bool => P (ω ∘ e.symm)) := by
  let eF : (X → Bool) ≃ (Y → Bool) :=
    { toFun := fun ω y => ω (e.symm y)
      invFun := fun ω x => ω (e x)
      left_inv := fun ω => by funext x; simp
      right_inv := fun ω => by funext y; simp }
  rw [bernProb, bernProb, ← Equiv.sum_comp eF (fun ω : Y → Bool => if P ω then bernW p ω else 0)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hw : bernW p (eF ω) = bernW p ω := by
    have h1 := bernW_equiv_comp e p (eF ω)
    have h2 : (eF ω) ∘ e = ω := by funext x; simp [eF]
    rw [h2] at h1; exact h1.symm
  simp only [eF, Equiv.coe_fn_mk] at hw ⊢
  rw [hw]; rfl

/-- Marginalizing `bernProb` on `A ⊕ B` when the event depends only on `A`. -/
lemma bernProb_inl {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (p : ℝ) (P : (A → Bool) → Prop) :
    bernProb p (fun ω : A ⊕ B → Bool => P (fun a => ω (Sum.inl a))) = bernProb p P := by
  let e : ((A → Bool) × (B → Bool)) ≃ (A ⊕ B → Bool) :=
    { toFun := fun q x => Sum.casesOn x q.1 q.2
      invFun := fun ω => (fun a => ω (Sum.inl a), fun b => ω (Sum.inr b))
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ω => by funext x; cases x <;> rfl }
  rw [bernProb, bernProb]
  refine (Fintype.sum_equiv e (fun q => if P q.1 then bernW p (e q) else 0)
    (fun ω => if P (fun a => ω (Sum.inl a)) then bernW p ω else 0) (fun _ => rfl)).symm.trans ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ωA _ => ?_
  have h1 : ∀ ωB : B → Bool, bernW p (e (ωA, ωB)) = bernW p ωA * bernW p ωB := fun ωB =>
    bernW_sum_split p (e (ωA, ωB))
  simp only [e, Equiv.coe_fn_mk] at h1 ⊢
  by_cases hP : P ωA
  · simp only [if_pos hP, h1, ← Finset.mul_sum, sum_bernW_eq_one, mul_one]
  · simp [hP]

/-- Factorization of product expectations over a partition `X ≃ A ⊕ B`. -/
lemma bernExp_sum_split {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (p : ℝ) (f : (A → Bool) → ℝ) (g : (B → Bool) → ℝ) :
    bernExp p (fun ω : A ⊕ B → Bool => f (fun a => ω (Sum.inl a)) * g (fun b => ω (Sum.inr b))) =
      bernExp p f * bernExp p g := by
  let e : ((A → Bool) × (B → Bool)) ≃ (A ⊕ B → Bool) :=
    { toFun := fun q x => Sum.casesOn x q.1 q.2
      invFun := fun ω => (fun a => ω (Sum.inl a), fun b => ω (Sum.inr b))
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ω => by funext x; cases x <;> rfl }
  rw [bernExp]
  refine (Fintype.sum_equiv e (fun q => bernW p (e q) * (f q.1 * g q.2))
    (fun ω => bernW p ω * (f (fun a => ω (Sum.inl a)) * g (fun b => ω (Sum.inr b))))
    (fun _ => rfl)).symm.trans ?_
  rw [Fintype.sum_prod_type]
  rw [bernExp, bernExp, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ωA _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ωB _ => ?_
  have hw : bernW p (e (ωA, ωB)) = bernW p ωA * bernW p ωB := bernW_sum_split p (e (ωA, ωB))
  simp only [e, Equiv.coe_fn_mk] at hw ⊢
  rw [hw]; ring

/-- Expectation of a product of coordinate functions on `X → Bool`. -/
lemma bernExp_prod {X : Type*} [Fintype X] [DecidableEq X] (p : ℝ) (g : X → Bool → ℝ) :
    bernExp p (fun ω => ∏ x : X, g x (ω x)) = ∏ x : X, (p * g x true + (1 - p) * g x false) := by
  simp only [bernExp, bernW]
  have h1 : ∀ ω : X → Bool,
      (∏ x : X, if ω x then p else 1 - p) * (∏ x : X, g x (ω x)) =
      ∏ x : X, (if ω x then p else 1 - p) * g x (ω x) := fun ω => (Finset.prod_mul_distrib).symm
  simp_rw [h1]
  have h2 := Fintype.prod_sum (fun (x : X) (b : Bool) => (if b then p else 1 - p) * g x b)
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false] at h2
  exact h2.symm

/-- Factorization over an indexed family of disjoint blocks `(i : ι) → (B i → Bool)`. -/
lemma bernExp_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ι → Type*}
    [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)] (p : ℝ)
    (f : ∀ i : ι, (B i → Bool) → ℝ) :
    bernExp p (fun ω : (Σ i : ι, B i) → Bool => ∏ i : ι, f i (fun b => ω ⟨i, b⟩)) =
      ∏ i : ι, bernExp p (f i) := by
  let e : (∀ i : ι, B i → Bool) ≃ ((Σ i : ι, B i) → Bool) :=
    { toFun := fun g q => g q.1 q.2
      invFun := fun ω i b => ω ⟨i, b⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [bernExp]
  refine (Fintype.sum_equiv e (fun g => bernW p (e g) * ∏ i : ι, f i (fun b => e g ⟨i, b⟩))
    (fun ω => bernW p ω * ∏ i : ι, f i (fun b => ω ⟨i, b⟩)) (fun _ => rfl)).symm.trans ?_
  have hw : ∀ g : ∀ i : ι, B i → Bool, bernW p (e g) = ∏ i : ι, bernW p (g i) := by
    intro g; simp only [bernW, e, Equiv.coe_fn_mk, Fintype.prod_sigma]
  have hmul : ∀ g : ∀ i : ι, B i → Bool,
      bernW p (e g) * (∏ i : ι, f i (fun b => e g ⟨i, b⟩)) =
      ∏ i : ι, (bernW p (g i) * f i (g i)) := by
    intro g; rw [hw g, ← Finset.prod_mul_distrib]; rfl
  simp_rw [hmul]
  exact (Fintype.prod_sum (fun (i : ι) (ωi : B i → Bool) => bernW p ωi * f i ωi)).symm

/-- Probability of a conjunction of independent block events on `(Σ i, B i) → Bool`. -/
lemma bernProb_pi_forall {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ι → Type*}
    [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)] (p : ℝ)
    (P : ∀ i : ι, (B i → Bool) → Prop) :
    bernProb p (fun ω : (Σ i : ι, B i) → Bool => ∀ i : ι, P i (fun b => ω ⟨i, b⟩)) =
      ∏ i : ι, bernProb p (P i) := by
  let f : ∀ i : ι, (B i → Bool) → ℝ := fun i ωi => if P i ωi then 1 else 0
  have hprod : ∀ ω : (Σ i : ι, B i) → Bool,
      (if ∀ i : ι, P i (fun b => ω ⟨i, b⟩) then (1 : ℝ) else 0) =
      ∏ i : ι, f i (fun b => ω ⟨i, b⟩) := by
    intro ω
    by_cases hall : ∀ i : ι, P i (fun b => ω ⟨i, b⟩)
    · rw [if_pos hall]; symm; exact Finset.prod_eq_one fun i _ => by simp [f, hall i]
    · rw [if_neg hall]; push Not at hall; rcases hall with ⟨i₀, hi₀⟩
      symm; exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [f, hi₀])
  have h1 : bernProb p (fun ω : (Σ i : ι, B i) → Bool => ∀ i : ι, P i (fun b => ω ⟨i, b⟩)) =
      bernExp p (fun ω : (Σ i : ι, B i) → Bool => ∏ i : ι, f i (fun b => ω ⟨i, b⟩)) := by
    simp only [bernProb, bernExp]
    refine Finset.sum_congr rfl fun ω _ => by rw [← hprod ω]; split_ifs <;> ring
  rw [h1, bernExp_pi_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [bernProb, bernExp, f]
  refine Finset.sum_congr rfl fun ωi _ => by split_ifs <;> ring

/-- Elementary exponential inequality on `[0, 1]`: `exp u ≤ 1 + 2 u`. -/
lemma exp_le_one_add_two_mul {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp u ≤ 1 + 2 * u := by
  have hconv : Real.exp u ≤ (1 - u) * Real.exp 0 + u * Real.exp 1 := by
    have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
      (by linarith : 0 ≤ 1 - u) hu0 (by ring : (1 - u) + u = 1)
    simpa [smul_eq_mul] using h
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  rw [Real.exp_zero] at hconv
  nlinarith only [hconv, he, hu0]

/-- Elementary exponential upper tail for a sum of independent `[0, M]`-bounded block functions. -/
lemma bernProb_sum_bounded_le {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ι → Type*}
    [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    {p M A : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hM : 0 < M)
    (Y : ∀ i : ι, (B i → Bool) → ℝ)
    (hY0 : ∀ i ωi, 0 ≤ Y i ωi) (hYM : ∀ i ωi, Y i ωi ≤ M) :
    bernProb p (fun ω : (Σ i : ι, B i) → Bool => A ≤ ∑ i : ι, Y i (fun b => ω ⟨i, b⟩)) ≤
      Real.exp ((2 * (∑ i : ι, bernExp p (Y i)) - A) / M) := by
  have hmono : bernProb p (fun ω : (Σ i : ι, B i) → Bool => A ≤ ∑ i : ι, Y i (fun b => ω ⟨i, b⟩)) ≤
      bernProb p (fun ω : (Σ i : ι, B i) → Bool =>
        Real.exp (A / M) ≤ Real.exp ((∑ i : ι, Y i (fun b => ω ⟨i, b⟩)) / M)) :=
    bernProb_mono hp0 hp1 fun ω hω => Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hω hM.le)
  have hmk := bernProb_markov hp0 hp1 (f := fun ω : (Σ i : ι, B i) → Bool =>
    Real.exp ((∑ i : ι, Y i (fun b => ω ⟨i, b⟩)) / M)) (fun _ => (Real.exp_pos _).le) (Real.exp_pos (A / M))
  have hprod_eq : ∀ ω : (Σ i : ι, B i) → Bool,
      Real.exp ((∑ i : ι, Y i (fun b => ω ⟨i, b⟩)) / M) =
      ∏ i : ι, Real.exp (Y i (fun b => ω ⟨i, b⟩) / M) := by
    intro ω; rw [Finset.sum_div, Real.exp_sum]
  simp_rw [hprod_eq] at hmono hmk
  rw [bernExp_pi_prod p (fun i ωi => Real.exp (Y i ωi / M))] at hmk
  have hfac : ∀ i : ι, bernExp p (fun ωi => Real.exp (Y i ωi / M)) ≤
      Real.exp (2 * bernExp p (Y i) / M) := by
    intro i
    have h1 : bernExp p (fun ωi => Real.exp (Y i ωi / M)) ≤
        bernExp p (fun ωi => 1 + 2 * (Y i ωi / M)) := by
      refine Finset.sum_le_sum fun ωi _ => mul_le_mul_of_nonneg_left ?_ (bernW_nonneg hp0 hp1 ωi)
      exact exp_le_one_add_two_mul (div_nonneg (hY0 i ωi) hM.le) ((div_le_one hM).mpr (hYM i ωi))
    have h2 : bernExp p (fun ωi => 1 + 2 * (Y i ωi / M)) = 1 + 2 * bernExp p (Y i) / M := by
      simp only [bernExp, mul_add, Finset.sum_add_distrib, mul_one, sum_bernW_eq_one]
      congr 1
      rw [mul_div_assoc, Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ωi _ => by ring
    rw [h2] at h1
    linarith only [h1, Real.add_one_le_exp (2 * bernExp p (Y i) / M)]
  have hprod_le : ∏ i : ι, bernExp p (fun ωi => Real.exp (Y i ωi / M)) ≤
      Real.exp (2 * (∑ i : ι, bernExp p (Y i)) / M) := by
    calc ∏ i : ι, bernExp p (fun ωi => Real.exp (Y i ωi / M))
        ≤ ∏ i : ι, Real.exp (2 * bernExp p (Y i) / M) :=
          Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun ωi _ =>
            mul_nonneg (bernW_nonneg hp0 hp1 ωi) (Real.exp_pos _).le) fun i _ => hfac i
      _ = Real.exp (∑ i : ι, 2 * bernExp p (Y i) / M) := (Real.exp_sum _ _).symm
      _ = Real.exp (2 * (∑ i : ι, bernExp p (Y i)) / M) := by
          congr 1; rw [← Finset.sum_div, ← Finset.mul_sum]
  have hdiv : Real.exp (2 * (∑ i : ι, bernExp p (Y i)) / M) / Real.exp (A / M) =
      Real.exp ((2 * (∑ i : ι, bernExp p (Y i)) - A) / M) := by
    rw [← Real.exp_sub]; congr 1; ring
  calc _ ≤ _ := hmono.trans hmk
    _ ≤ Real.exp (2 * (∑ i : ι, bernExp p (Y i)) / M) / Real.exp (A / M) :=
        div_le_div_of_nonneg_right hprod_le (Real.exp_pos _).le
    _ = _ := hdiv

/-- Exact first moment of a Binomial sum `∑_{x ∈ S} 1_{ω x}` under `bernExp p`. -/
lemma bernExp_indicator_sum {X : Type*} [Fintype X] [DecidableEq X] (p : ℝ) (S : Finset X) :
    bernExp p (fun ω => ((S.filter (fun x => ω x = true)).card : ℝ)) = (S.card : ℝ) * p := by
  have hcard : ∀ ω : X → Bool,
      ((S.filter (fun x => ω x = true)).card : ℝ) = ∑ x ∈ S, if ω x then (1 : ℝ) else 0 := by
    intro ω; simp [Finset.sum_boole]
  simp_rw [hcard, bernExp, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hsingle : ∀ x : X, ∑ ω : X → Bool, bernW p ω * (if ω x then (1 : ℝ) else 0) = p := by
    intro x
    let g : X → Bool → ℝ := fun y b => if y = x then (if b then 1 else 0) else 1
    have hprod : ∀ ω : X → Bool, (if ω x then (1 : ℝ) else 0) = ∏ y : X, g y (ω y) := by
      intro ω
      rw [Finset.prod_eq_single x]
      · simp [g]
      · intro y _ hyx; simp [g, hyx]
      · intro h; exact absurd (Finset.mem_univ x) h
    have h1 : ∑ ω : X → Bool, bernW p ω * (if ω x then (1 : ℝ) else 0) =
        bernExp p (fun ω => ∏ y : X, g y (ω y)) := by
      simp only [bernExp]; refine Finset.sum_congr rfl fun ω _ => by rw [hprod ω]
    rw [h1, bernExp_prod]
    rw [Finset.prod_eq_single x]
    · simp [g]
    · intro y _ hyx; simp [g, hyx]
    · intro h; exact absurd (Finset.mem_univ x) h
  calc ∑ x ∈ S, ∑ ω : X → Bool, bernW p ω * (if ω x then (1 : ℝ) else 0)
      = ∑ _x ∈ S, p := Finset.sum_congr rfl fun x _ => hsingle x
    _ = (S.card : ℝ) * p := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Exact second moment upper bound `E[(∑_{x ∈ S} 1_{ω x})^2] ≤ |S| p + (|S| p)^2`. -/
lemma bernExp_indicator_sum_sq_le {X : Type*} [Fintype X] [DecidableEq X] {p : ℝ} (_hp0 : 0 ≤ p) (_hp1 : p ≤ 1)
    (S : Finset X) :
    bernExp p (fun ω => ((S.filter (fun x => ω x = true)).card : ℝ) ^ 2) ≤
      (S.card : ℝ) * p + ((S.card : ℝ) * p) ^ 2 := by
  have hsq : ∀ ω : X → Bool,
      ((S.filter (fun x => ω x = true)).card : ℝ) ^ 2 =
      ∑ x ∈ S, ∑ y ∈ S, (if ω x then (1 : ℝ) else 0) * (if ω y then (1 : ℝ) else 0) := by
    intro ω
    have h1 : ((S.filter (fun x => ω x = true)).card : ℝ) = ∑ x ∈ S, if ω x then (1 : ℝ) else 0 := by
      simp [Finset.sum_boole]
    rw [h1, sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => Finset.mul_sum _ _ _
  simp_rw [hsq, bernExp, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hswap : ∀ x ∈ S,
      ∑ ω : X → Bool, ∑ y ∈ S, bernW p ω * ((if ω x then (1 : ℝ) else 0) * (if ω y then (1 : ℝ) else 0)) =
      ∑ y ∈ S, ∑ ω : X → Bool, bernW p ω * ((if ω x then (1 : ℝ) else 0) * (if ω y then (1 : ℝ) else 0)) :=
    fun _ _ => Finset.sum_comm
  rw [Finset.sum_congr rfl hswap]
  have hpair : ∀ x y : X,
      ∑ ω : X → Bool, bernW p ω * ((if ω x then (1 : ℝ) else 0) * (if ω y then (1 : ℝ) else 0)) =
      if x = y then p else p ^ 2 := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl]
      let g : X → Bool → ℝ := fun z b => if z = x then (if b then 1 else 0) else 1
      have hp' : ∀ ω : X → Bool, (if ω x then (1 : ℝ) else 0) * (if ω x then (1 : ℝ) else 0) =
          ∏ z : X, g z (ω z) := by
        intro ω
        rw [Finset.prod_eq_single x]
        · cases ω x <;> simp [g]
        · intro z _ hzx; simp [g, hzx]
        · intro h; exact absurd (Finset.mem_univ x) h
      have h1 : ∑ ω : X → Bool, bernW p ω * ((if ω x then (1 : ℝ) else 0) * (if ω x then (1 : ℝ) else 0)) =
          bernExp p (fun ω => ∏ z : X, g z (ω z)) := by
        simp only [bernExp]; refine Finset.sum_congr rfl fun ω _ => by rw [hp' ω]
      rw [h1, bernExp_prod, Finset.prod_eq_single x]
      · simp [g]
      · intro z _ hzx; simp [g, hzx]
      · intro h; exact absurd (Finset.mem_univ x) h
    · rw [if_neg hxy]
      let g : X → Bool → ℝ := fun z b => if z = x ∨ z = y then (if b then 1 else 0) else 1
      have hp' : ∀ ω : X → Bool, (if ω x then (1 : ℝ) else 0) * (if ω y then (1 : ℝ) else 0) =
          ∏ z : X, g z (ω z) := by
        intro ω
        have hsub : ({x, y} : Finset X) ⊆ Finset.univ := Finset.subset_univ _
        rw [← Finset.prod_subset hsub]
        · rw [Finset.prod_pair hxy]; simp [g]
        · intro z _ hz; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
          simp [g, hz.1, hz.2]
      have h1 : ∑ ω : X → Bool, bernW p ω * ((if ω x then (1 : ℝ) else 0) * (if ω y then (1 : ℝ) else 0)) =
          bernExp p (fun ω => ∏ z : X, g z (ω z)) := by
        simp only [bernExp]; refine Finset.sum_congr rfl fun ω _ => by rw [hp' ω]
      rw [h1, bernExp_prod]
      have hsub : ({x, y} : Finset X) ⊆ Finset.univ := Finset.subset_univ _
      rw [← Finset.prod_subset hsub]
      · rw [Finset.prod_pair hxy]; simp [g, sq]
      · intro z _ hz; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
        simp [g, hz.1, hz.2]
  have hsum_eq : ∑ x ∈ S, ∑ y ∈ S,
      ∑ ω : X → Bool, bernW p ω * ((if ω x then (1 : ℝ) else 0) * (if ω y then (1 : ℝ) else 0)) =
      ∑ x ∈ S, ∑ y ∈ S, (if x = y then p else p ^ 2) :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hpair x y
  rw [hsum_eq]
  have hle : ∀ x ∈ S, ∑ y ∈ S, (if x = y then p else p ^ 2) ≤ p + (S.card : ℝ) * p ^ 2 := by
    intro x hx
    calc ∑ y ∈ S, (if x = y then p else p ^ 2)
        ≤ ∑ y ∈ S, ((if x = y then p else 0) + p ^ 2) := Finset.sum_le_sum fun y _ => by
          split_ifs <;> nlinarith only [_hp0, _hp1]
      _ = (∑ y ∈ S, if x = y then p else 0) + ∑ _y ∈ S, p ^ 2 := Finset.sum_add_distrib
      _ = p + (S.card : ℝ) * p ^ 2 := by simp [hx]
  calc ∑ x ∈ S, ∑ y ∈ S, (if x = y then p else p ^ 2)
      ≤ ∑ _x ∈ S, (p + (S.card : ℝ) * p ^ 2) := Finset.sum_le_sum hle
    _ = (S.card : ℝ) * p + ((S.card : ℝ) * p) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- Standard binomial upper tail via union bound over `r`-subsets:
`P(Bin(|S|, p) ≥ r) ≤ (|S|.choose r) * p ^ r`. -/
lemma bernProb_binom_ge_choose {X : Type*} [Fintype X] [DecidableEq X] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset X) (r : ℕ) :
    bernProb p (fun ω => r ≤ (S.filter (fun x => ω x = true)).card) ≤
      (S.card.choose r : ℝ) * p ^ r := by
  have himp : ∀ ω : X → Bool, r ≤ (S.filter (fun x => ω x = true)).card →
      ∃ T ∈ S.powersetCard r, ∀ x ∈ T, ω x = true := by
    intro ω hω
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hω
    refine ⟨T, Finset.mem_powersetCard.mpr ⟨hTsub.trans (Finset.filter_subset _ _), hTcard⟩,
      fun x hx => (Finset.mem_filter.mp (hTsub hx)).2⟩
  have h1 := (bernProb_mono hp0 hp1 himp).trans (bernProb_exists_le hp0 hp1 (S.powersetCard r)
    (fun T ω => ∀ x ∈ T, ω x = true))
  have hT_prob : ∀ T ∈ S.powersetCard r, bernProb p (fun ω => ∀ x ∈ T, ω x = true) = p ^ r := by
    intro T hT
    have hTc : T.card = r := (Finset.mem_powersetCard.mp hT).2
    let g : X → Bool → ℝ := fun x b => if x ∈ T then (if b then 1 else 0) else 1
    have hprod : ∀ ω : X → Bool, (if ∀ x ∈ T, ω x = true then (1 : ℝ) else 0) = ∏ x : X, g x (ω x) := by
      intro ω
      by_cases hall : ∀ x ∈ T, ω x = true
      · rw [if_pos hall]
        symm; exact Finset.prod_eq_one fun x _ => by
          by_cases hx : x ∈ T
          · simp [g, hx, hall x hx]
          · simp [g, hx]
      · rw [if_neg hall]
        push Not at hall
        rcases hall with ⟨x₀, hx₀T, hx₀f⟩
        symm; exact Finset.prod_eq_zero (Finset.mem_univ x₀) (by simp [g, hx₀T, hx₀f])
    have heq : bernProb p (fun ω => ∀ x ∈ T, ω x = true) =
        bernExp p (fun ω => ∏ x : X, g x (ω x)) := by
      simp only [bernProb, bernExp]
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [← hprod ω]; split_ifs <;> ring
    rw [heq, bernExp_prod]
    rw [← Finset.prod_subset (Finset.subset_univ T)]
    · calc ∏ x ∈ T, (p * g x true + (1 - p) * g x false)
          = ∏ _x ∈ T, p := Finset.prod_congr rfl fun x hx => by simp [g, hx]
        _ = p ^ T.card := Finset.prod_const p
        _ = p ^ r := by rw [hTc]
    · intro x _ hxT; simp [g, hxT]
  calc _ ≤ ∑ T ∈ S.powersetCard r, bernProb p (fun ω => ∀ x ∈ T, ω x = true) := h1
    _ = ∑ _T ∈ S.powersetCard r, p ^ r := Finset.sum_congr rfl hT_prob
    _ = (S.card.choose r : ℝ) * p ^ r := by
        rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

/-- Elementary factorial lower bound `(r / e)^r ≤ r!` (from `r^r / r! ≤ exp r`). -/
lemma pow_div_factorial_le_exp (r : ℕ) : (r : ℝ) ^ r / (r.factorial : ℝ) ≤ Real.exp (r : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (Nat.cast_nonneg r) (r + 1)
  have hterm : (r : ℝ) ^ r / (r.factorial : ℝ) ≤ ∑ i ∈ Finset.range (r + 1), (r : ℝ) ^ i / (i.factorial : ℝ) :=
    Finset.single_le_sum (f := fun i => (r : ℝ) ^ i / (i.factorial : ℝ))
      (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self r))
  exact hterm.trans h

/-- Elementary binomial upper bound `(N.choose r : ℝ) ≤ (e * N / r)^r` for `1 ≤ r`. -/
lemma choose_le_exp_pow {N r : ℕ} (hr : 1 ≤ r) :
    (N.choose r : ℝ) ≤ (Real.exp 1 * (N : ℝ) / (r : ℝ)) ^ r := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
  have hfac_pos : (0 : ℝ) < (r.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos r)
  have h1 : (N.choose r : ℝ) * (r.factorial : ℝ) ≤ (N : ℝ) ^ r := by
    have hnat : N.choose r * r.factorial ≤ N ^ r := by
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow N r
    exact_mod_cast hnat
  have h2 : (N.choose r : ℝ) ≤ (N : ℝ) ^ r / (r.factorial : ℝ) := (le_div_iff₀ hfac_pos).mpr h1
  have h3 := pow_div_factorial_le_exp r
  have h4 : Real.exp (r : ℝ) = (Real.exp 1) ^ r := by rw [← Real.exp_nat_mul, mul_one]
  rw [h4] at h3
  have h5 : (1 : ℝ) / (r.factorial : ℝ) ≤ (Real.exp 1 / (r : ℝ)) ^ r := by
    rw [div_pow, div_le_div_iff₀ hfac_pos (pow_pos hr_pos r)]
    rw [div_le_iff₀ hfac_pos] at h3
    linarith only [h3]
  calc (N.choose r : ℝ) ≤ (N : ℝ) ^ r / (r.factorial : ℝ) := h2
    _ = (N : ℝ) ^ r * (1 / (r.factorial : ℝ)) := by ring
    _ ≤ (N : ℝ) ^ r * (Real.exp 1 / (r : ℝ)) ^ r := mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = (Real.exp 1 * (N : ℝ) / (r : ℝ)) ^ r := by rw [← mul_pow]; congr 1; ring

/-- Binomial upper tail `(e * |S| * p / r)^r` for `1 ≤ r`. -/
lemma bernProb_binom_ge_pow {X : Type*} [Fintype X] [DecidableEq X] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset X) {r : ℕ} (hr : 1 ≤ r) :
    bernProb p (fun ω => r ≤ (S.filter (fun x => ω x = true)).card) ≤
      (Real.exp 1 * (S.card : ℝ) * p / (r : ℝ)) ^ r := by
  calc bernProb p (fun ω => r ≤ (S.filter (fun x => ω x = true)).card)
      ≤ (S.card.choose r : ℝ) * p ^ r := bernProb_binom_ge_choose hp0 hp1 S r
    _ ≤ (Real.exp 1 * (S.card : ℝ) / (r : ℝ)) ^ r * p ^ r :=
        mul_le_mul_of_nonneg_right (choose_le_exp_pow hr) (pow_nonneg hp0 r)
    _ = (Real.exp 1 * (S.card : ℝ) * p / (r : ℝ)) ^ r := by rw [← mul_pow]; congr 1; ring

/-- Upper Chernoff bound for Binomial: `P(Bin(|S|, p) ≥ 2 |S| p) ≤ exp(-|S| p / 6)`. -/
lemma bernProb_binom_ge_two_mul {X : Type*} [Fintype X] [DecidableEq X] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset X) :
    bernProb p (fun ω => 2 * ((S.card : ℝ) * p) ≤ ((S.filter (fun x => ω x = true)).card : ℝ)) ≤
      Real.exp (-((S.card : ℝ) * p) / 6) := by
  have h1 : bernProb p (fun ω => 2 * ((S.card : ℝ) * p) ≤ ((S.filter (fun x => ω x = true)).card : ℝ)) ≤
      bernProb p (fun ω => Real.exp ((S.card : ℝ) * p) ≤
        Real.exp (((S.filter (fun x => ω x = true)).card : ℝ) / 2)) :=
    bernProb_mono hp0 hp1 fun ω hω => Real.exp_le_exp.mpr (by linarith only [hω])
  have hmk := bernProb_markov hp0 hp1 (f := fun ω =>
    Real.exp (((S.filter (fun x => ω x = true)).card : ℝ) / 2))
    (fun _ => (Real.exp_pos _).le) (Real.exp_pos ((S.card : ℝ) * p))
  let g : X → Bool → ℝ := fun x b => if x ∈ S then (if b then Real.exp (1 / 2) else 1) else 1
  have hprod : ∀ ω : X → Bool,
      Real.exp (((S.filter (fun x => ω x = true)).card : ℝ) / 2) = ∏ x : X, g x (ω x) := by
    intro ω
    have hcard : ((S.filter (fun x => ω x = true)).card : ℝ) / 2 =
        ∑ x : X, if x ∈ S then (if ω x then (1 / 2 : ℝ) else 0) else 0 := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; ring
    rw [hcard, Real.exp_sum]
    refine Finset.prod_congr rfl fun x _ => by
      by_cases hx : x ∈ S
      · cases ω x <;> simp [g, hx]
      · simp [g, hx]
  simp_rw [hprod] at h1 hmk
  rw [bernExp_prod] at hmk
  have hexp_half : Real.exp (1 / 2 : ℝ) ≤ 11 / 6 := by
    have hsq : Real.exp (1 / 2 : ℝ) ^ 2 ≤ (11 / 6 : ℝ) ^ 2 := by
      rw [← Real.exp_nat_mul]
      have h : (2 : ℕ) * (1 / 2 : ℝ) = 1 := by norm_num
      rw [h]
      exact Real.exp_one_lt_d9.le.trans (by norm_num)
    nlinarith only [hsq, Real.exp_pos (1 / 2 : ℝ)]
  have hfac_le : ∀ x ∈ S, p * g x true + (1 - p) * g x false ≤ Real.exp ((5 / 6 : ℝ) * p) := by
    intro x hx
    simp only [g, hx, ite_true, Bool.false_eq_true, ite_false]
    have hle : p * Real.exp (1 / 2 : ℝ) + (1 - p) * 1 ≤ 1 + (5 / 6 : ℝ) * p := by
      nlinarith only [hexp_half, hp0]
    linarith only [hle, Real.add_one_le_exp ((5 / 6 : ℝ) * p)]
  have hprod_le : ∏ x : X, (p * g x true + (1 - p) * g x false) ≤ Real.exp ((5 / 6 : ℝ) * ((S.card : ℝ) * p)) := by
    rw [← Finset.prod_subset (Finset.subset_univ S)]
    · calc ∏ x ∈ S, (p * g x true + (1 - p) * g x false)
          ≤ ∏ _x ∈ S, Real.exp ((5 / 6 : ℝ) * p) :=
            Finset.prod_le_prod (fun x _ => by
              have : 0 ≤ g x true := by simp only [g]; split_ifs; all_goals positivity
              have : 0 ≤ g x false := by simp only [g]; split_ifs; all_goals positivity
              nlinarith only [hp0, hp1, ‹0 ≤ g x true›, ‹0 ≤ g x false›]) hfac_le
        _ = Real.exp ((5 / 6 : ℝ) * ((S.card : ℝ) * p)) := by
            rw [Finset.prod_const, ← Real.exp_nat_mul]; congr 1; ring
    · intro x _ hxS; simp [g, hxS]
  calc _ ≤ _ := h1.trans hmk
    _ ≤ Real.exp ((5 / 6 : ℝ) * ((S.card : ℝ) * p)) / Real.exp ((S.card : ℝ) * p) :=
        div_le_div_of_nonneg_right hprod_le (Real.exp_pos _).le
    _ = Real.exp (-((S.card : ℝ) * p) / 6) := by rw [← Real.exp_sub]; congr 1; ring

/-- Uniform-map fiber upper bound: for fixed `x : Fin m`, the fraction of maps `φ : Fin n → Fin m`
with `r ≤ |φ⁻¹(x)|` is at most `(n.choose r) * (1 / m)^r`. -/
lemma card_maps_fiber_ge_le {n m : ℕ} (hm : 1 ≤ m) (x : Fin m) (r : ℕ) :
    ((Finset.univ.filter (fun φ : Fin n → Fin m =>
      r ≤ (Finset.univ.filter (fun v : Fin n => φ v = x)).card)).card : ℝ) ≤
      (n.choose r : ℝ) * ((1 / (m : ℝ)) ^ r) * (m : ℝ) ^ n := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  let Good := Finset.univ.filter (fun φ : Fin n → Fin m =>
    r ≤ (Finset.univ.filter (fun v : Fin n => φ v = x)).card)
  have hcov : Good ⊆ ((Finset.univ : Finset (Fin n)).powersetCard r).biUnion
      (fun T => Finset.univ.filter (fun φ : Fin n → Fin m => ∀ v ∈ T, φ v = x)) := by
    intro φ hφ
    have hge := (Finset.mem_filter.mp hφ).2
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hge
    refine Finset.mem_biUnion.mpr ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hTcard⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v hv => (Finset.mem_filter.mp (hTsub hv)).2⟩⟩
  have hT_card : ∀ T ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
      ((Finset.univ.filter (fun φ : Fin n → Fin m => ∀ v ∈ T, φ v = x)).card : ℝ) =
      (1 / (m : ℝ)) ^ r * (m : ℝ) ^ n := by
    intro T hT
    have hTc : T.card = r := (Finset.mem_powersetCard.mp hT).2
    have hle : r ≤ n := by rw [← hTc]; exact (Finset.card_le_univ T).trans (by simp)
    let e : { φ : Fin n → Fin m // ∀ v ∈ T, φ v = x } ≃ ({ v : Fin n // v ∉ T } → Fin m) :=
      { toFun := fun f u => f.1 u.1
        invFun := fun g => ⟨fun v => if hv : v ∈ T then x else g ⟨v, hv⟩,
          fun v hv => by simp [hv]⟩
        left_inv := fun ⟨φ, hφ⟩ => by
          apply Subtype.ext; funext v
          by_cases hv : v ∈ T
          · simp [hv, hφ v hv]
          · simp [hv]
        right_inv := fun g => by funext ⟨v, hv⟩; simp [hv] }
    have hcard_nat : (Finset.univ.filter (fun φ : Fin n → Fin m => ∀ v ∈ T, φ v = x)).card =
        m ^ (n - r) := by
      have h1 : (Finset.univ.filter (fun φ : Fin n → Fin m => ∀ v ∈ T, φ v = x)).card =
          Fintype.card { φ : Fin n → Fin m // ∀ v ∈ T, φ v = x } := (Fintype.card_subtype _).symm
      rw [h1, Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin]
      congr 1
      have h2 : Fintype.card { v : Fin n // v ∉ T } = (Finset.univ \ T).card := by
        rw [Fintype.card_subtype]; congr 1; ext v; simp
      rw [h2, Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ, Fintype.card_fin, hTc]
    rw [hcard_nat, Nat.cast_pow]
    have hpow : (m : ℝ) ^ n = (m : ℝ) ^ r * (m : ℝ) ^ (n - r) := by
      rw [← pow_add, Nat.add_sub_of_le hle]
    rw [hpow, one_div_pow]
    field_simp
  have hbi : (Good.card : ℝ) ≤ ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
      ((Finset.univ.filter (fun φ : Fin n → Fin m => ∀ v ∈ T, φ v = x)).card : ℝ) := by
    have hnat : Good.card ≤ ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        (Finset.univ.filter (fun φ : Fin n → Fin m => ∀ v ∈ T, φ v = x)).card :=
      (Finset.card_le_card hcov).trans Finset.card_biUnion_le
    exact_mod_cast hnat
  calc (Good.card : ℝ)
      ≤ ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
          ((Finset.univ.filter (fun φ : Fin n → Fin m => ∀ v ∈ T, φ v = x)).card : ℝ) := hbi
    _ = ∑ _T ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
          ((1 / (m : ℝ)) ^ r * (m : ℝ) ^ n) := Finset.sum_congr rfl hT_card
    _ = (n.choose r : ℝ) * ((1 / (m : ℝ)) ^ r) * (m : ℝ) ^ n := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_assoc]

/-- Uniform-map compression bound: for a fixed `k`-set `I` and fixed `r`-set `A ⊆ Fin m`,
the number of maps `φ : Fin n → Fin m` sending `I` into `A` is `|A|^k * m^(n - k)`. -/
lemma card_maps_image_subset {n m : ℕ} (hm : 1 ≤ m) (I : Finset (Fin n)) (A : Finset (Fin m)) :
    ((Finset.univ.filter (fun φ : Fin n → Fin m => ∀ v ∈ I, φ v ∈ A)).card : ℝ) =
      ((A.card : ℝ) / (m : ℝ)) ^ I.card * (m : ℝ) ^ n := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hle : I.card ≤ n := (Finset.card_le_univ I).trans (by simp)
  let e : { φ : Fin n → Fin m // ∀ v ∈ I, φ v ∈ A } ≃
      (({ v : Fin n // v ∈ I } → { x : Fin m // x ∈ A }) × ({ v : Fin n // v ∉ I } → Fin m)) :=
    { toFun := fun f => (fun v => ⟨f.1 v.1, f.2 v.1 v.2⟩, fun v => f.1 v.1)
      invFun := fun p => ⟨fun v => if hv : v ∈ I then (p.1 ⟨v, hv⟩).1 else p.2 ⟨v, hv⟩,
        fun v hv => by simp [hv]⟩
      left_inv := fun ⟨φ, hφ⟩ => by
        apply Subtype.ext; funext v
        by_cases hv : v ∈ I <;> simp [hv]
      right_inv := fun ⟨g1, g2⟩ => by
        apply Prod.ext
        · funext ⟨v, hv⟩; apply Subtype.ext; simp [hv]
        · funext ⟨v, hv⟩; simp [hv] }
  have hcard_nat : (Finset.univ.filter (fun φ : Fin n → Fin m => ∀ v ∈ I, φ v ∈ A)).card =
      A.card ^ I.card * m ^ (n - I.card) := by
    have h1 : (Finset.univ.filter (fun φ : Fin n → Fin m => ∀ v ∈ I, φ v ∈ A)).card =
        Fintype.card { φ : Fin n → Fin m // ∀ v ∈ I, φ v ∈ A } := (Fintype.card_subtype _).symm
    rw [h1, Fintype.card_congr e, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
      Fintype.card_fin]
    have hI : Fintype.card { v : Fin n // v ∈ I } = I.card := by simp
    have hA : Fintype.card { x : Fin m // x ∈ A } = A.card := by simp
    have hIc : Fintype.card { v : Fin n // v ∉ I } = n - I.card := by
      have h2 : Fintype.card { v : Fin n // v ∉ I } = (Finset.univ \ I).card := by
        rw [Fintype.card_subtype]; congr 1; ext v; simp
      rw [h2, Finset.card_sdiff_of_subset (Finset.subset_univ I), Finset.card_univ, Fintype.card_fin]
    rw [hI, hA, hIc]
  rw [hcard_nat, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, div_pow]
  have hpow : (m : ℝ) ^ n = (m : ℝ) ^ I.card * (m : ℝ) ^ (n - I.card) := by
    rw [← pow_add, Nat.add_sub_of_le hle]
  rw [hpow]
  field_simp

end FiniteBernoulli

/- ### Section 2: Two-Blowup Triangle-Free Construction & Deterministic Reductions -/

section DeterministicConstruction

/-- Undirected edge index set on `Fin m`: ordered pairs `(u, v)` with `u < v`. -/
abbrev EdgeIdx (m : ℕ) : Type := { p : Fin m × Fin m // p.1 < p.2 }

/-- Simple graph on `Fin m` determined by an edge indicator `ω : EdgeIdx m → Bool`. -/
def graphOf {m : ℕ} (ω : EdgeIdx m → Bool) : SimpleGraph (Fin m) where
  Adj u v :=
    if h : u < v then ω ⟨(u, v), h⟩ = true
    else if h' : v < u then ω ⟨(v, u), h'⟩ = true
    else False
  symm := ⟨fun u v h => by
    rcases lt_trichotomy u v with hlt | rfl | hgt
    · have hnot : ¬ v < u := lt_asymm hlt
      simp only [dif_pos hlt] at h
      simp only [dif_neg hnot, dif_pos hlt, h]
    · simp at h
    · have hnot : ¬ u < v := lt_asymm hgt
      simp only [dif_neg hnot, dif_pos hgt] at h
      simp only [dif_pos hgt, h]⟩
  loopless := ⟨fun u => by simp⟩

/-- Vertex-order triangle pruning: retain edge `{u, v}` of `G` iff `u, v` have no common neighbor
strictly smaller than `min u v`. -/
def pruneTri {m : ℕ} (G : SimpleGraph (Fin m)) : SimpleGraph (Fin m) where
  Adj u v := G.Adj u v ∧ ¬ ∃ z : Fin m, z < min u v ∧ G.Adj z u ∧ G.Adj z v
  symm := ⟨fun u v ⟨hadj, hno⟩ =>
    ⟨hadj.symm, fun ⟨z, hz, hzv, hzu⟩ => hno ⟨z, by rwa [min_comm] at hz, hzu, hzv⟩⟩⟩
  loopless := ⟨fun u ⟨h, _⟩ => G.loopless.irrefl u h⟩

lemma pruneTri_cliqueFree {m : ℕ} (G : SimpleGraph (Fin m)) : (pruneTri G).CliqueFree 3 := by
  intro t ht
  rw [SimpleGraph.is3Clique_iff] at ht
  rcases ht with ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hne_ab : a ≠ b := (pruneTri G).ne_of_adj hab
  have hne_ac : a ≠ c := (pruneTri G).ne_of_adj hac
  have hne_bc : b ≠ c := (pruneTri G).ne_of_adj hbc
  rcases lt_or_gt_of_ne hne_ab with h1 | h1
  · rcases lt_or_gt_of_ne hne_ac with h2 | h2
    · exact hbc.2 ⟨a, lt_min h1 h2, hab.1, hac.1⟩
    · exact hab.2 ⟨c, lt_min h2 (lt_trans h2 h1), hac.1.symm, hbc.1.symm⟩
  · rcases lt_or_gt_of_ne hne_bc with h2 | h2
    · exact hac.2 ⟨b, lt_min h1 h2, hab.1.symm, hbc.1⟩
    · exact hab.2 ⟨c, lt_min (lt_trans h2 h1) h2, hac.1.symm, hbc.1.symm⟩

/-- A pair `(u, v)` in `Fin n` is blocked by `(G, φ)` if `φ u = φ v` or `φ u, φ v` share a neighbor in `G`. -/
def pairBad {n m : ℕ} (G : SimpleGraph (Fin m)) (φ : Fin n → Fin m) (u v : Fin n) : Prop :=
  φ u = φ v ∨ ∃ z : Fin m, G.Adj (φ u) z ∧ G.Adj (φ v) z

lemma pairBad_symm {n m : ℕ} (G : SimpleGraph (Fin m)) (φ : Fin n → Fin m) {u v : Fin n}
    (h : pairBad G φ u v) : pairBad G φ v u := by
  rcases h with heq | ⟨z, h1, h2⟩
  · exact Or.inl heq.symm
  · exact Or.inr ⟨z, h2, h1⟩

/-- Surviving red edge between `u, v ∈ Fin n`. -/
def red2Adj {n m : ℕ} (G_R G_B : SimpleGraph (Fin m)) (φ_R φ_B : Fin n → Fin m) (u v : Fin n) : Prop :=
  (pruneTri G_R).Adj (φ_R u) (φ_R v) ∧ ¬ pairBad G_B φ_B u v

/-- Surviving blue edge between `u, v ∈ Fin n`. -/
def blue2Adj {n m : ℕ} (G_R G_B : SimpleGraph (Fin m)) (φ_R φ_B : Fin n → Fin m) (u v : Fin n) : Prop :=
  (pruneTri G_B).Adj (φ_B u) (φ_B v) ∧ ¬ pairBad G_R φ_R u v

/-- The two-blowup triangle-free simple graph on `Fin n`. -/
def buildGraph {n m : ℕ} (G_R G_B : SimpleGraph (Fin m)) (φ_R φ_B : Fin n → Fin m) :
    SimpleGraph (Fin n) where
  Adj u v := red2Adj G_R G_B φ_R φ_B u v ∨ blue2Adj G_R G_B φ_R φ_B u v
  symm := ⟨fun u v h => by
    rcases h with ⟨hR, hnb⟩ | ⟨hB, hnr⟩
    · exact Or.inl ⟨hR.symm, fun h => hnb (pairBad_symm G_B φ_B h)⟩
    · exact Or.inr ⟨hB.symm, fun h => hnr (pairBad_symm G_R φ_R h)⟩⟩
  loopless := ⟨fun u h => by
    rcases h with ⟨hR, _⟩ | ⟨hB, _⟩
    · exact (pruneTri G_R).loopless.irrefl (φ_R u) hR
    · exact (pruneTri G_B).loopless.irrefl (φ_B u) hB⟩

/-- `buildGraph` is unconditionally triangle-free for ANY `(G_R, G_B, φ_R, φ_B)`. -/
theorem buildGraph_cliqueFree {n m : ℕ} (G_R G_B : SimpleGraph (Fin m)) (φ_R φ_B : Fin n → Fin m) :
    (buildGraph G_R G_B φ_R φ_B).CliqueFree 3 := by
  intro t ht
  rw [SimpleGraph.is3Clique_iff] at ht
  rcases ht with ⟨a, b, c, hab, hac, hbc, rfl⟩
  rcases hab with hR_ab | hB_ab
  · rcases hac with hR_ac | hB_ac
    · rcases hbc with hR_bc | hB_bc
      · exact pruneTri_cliqueFree G_R {φ_R a, φ_R b, φ_R c}
          (SimpleGraph.is3Clique_triple_iff.mpr ⟨hR_ab.1, hR_ac.1, hR_bc.1⟩)
      · exact hB_bc.2 (Or.inr ⟨φ_R a, hR_ab.1.1.symm, hR_ac.1.1.symm⟩)
    · rcases hbc with hR_bc | hB_bc
      · exact hB_ac.2 (Or.inr ⟨φ_R b, hR_ab.1.1, hR_bc.1.1.symm⟩)
      · exact hR_ab.2 (Or.inr ⟨φ_B c, hB_ac.1.1, hB_bc.1.1⟩)
  · rcases hac with hR_ac | hB_ac
    · rcases hbc with hR_bc | hB_bc
      · exact hB_ab.2 (Or.inr ⟨φ_R c, hR_ac.1.1, hR_bc.1.1⟩)
      · exact hR_ac.2 (Or.inr ⟨φ_B b, hB_ab.1.1, hB_bc.1.1.symm⟩)
    · rcases hbc with hR_bc | hB_bc
      · exact hR_bc.2 (Or.inr ⟨φ_B a, hB_ab.1.1.symm, hB_ac.1.1.symm⟩)
      · exact pruneTri_cliqueFree G_B {φ_B a, φ_B b, φ_B c}
          (SimpleGraph.is3Clique_triple_iff.mpr ⟨hB_ab.1, hB_ac.1, hB_bc.1⟩)

/-- Number of neighbors of `z` in `S` under `G`. -/
noncomputable def degIn {m : ℕ} (G : SimpleGraph (Fin m)) (S : Finset (Fin m)) (z : Fin m) : ℕ :=
  (S.filter (fun x => G.Adj z x)).card

/-- Random-bipartition lemma: for any graph `G` and `S : Finset (Fin m)`, there exists `A ⊆ S`
such that `∑_{z ∈ S} degIn G S z ^ 2 ≤ 8 * ∑_{z ∈ S \ A} degIn G A z ^ 2`. -/
lemma exists_bipartition_sum_sq {m : ℕ} (G : SimpleGraph (Fin m)) (S : Finset (Fin m)) :
    ∃ A ⊆ S, ∑ z ∈ S, (degIn G S z : ℝ) ^ 2 ≤ 8 * ∑ z ∈ S \ A, (degIn G A z : ℝ) ^ 2 := by
  let sub : (S → Bool) → Finset (Fin m) := fun f => S.filter (fun x => ∃ hx : x ∈ S, f ⟨x, hx⟩ = true)
  have hsub_sub : ∀ f : S → Bool, sub f ⊆ S := fun f => Finset.filter_subset _ _
  have havg : ∑ f : S → Bool, (8 * ∑ z ∈ S \ sub f, (degIn G (sub f) z : ℝ) ^ 2) ≥
      ∑ _f : S → Bool, ∑ z ∈ S, (degIn G S z : ℝ) ^ 2 := by
    have hLHS : ∑ f : S → Bool, (8 * ∑ z ∈ S \ sub f, (degIn G (sub f) z : ℝ) ^ 2) =
        ∑ z ∈ S, 8 * ∑ f : S → Bool, if z ∉ sub f then (degIn G (sub f) z : ℝ) ^ 2 else 0 := by
      rw [← Finset.mul_sum]
      have h1 : ∀ f : S → Bool, ∑ z ∈ S \ sub f, (degIn G (sub f) z : ℝ) ^ 2 =
          ∑ z ∈ S, if z ∉ sub f then (degIn G (sub f) z : ℝ) ^ 2 else 0 := by
        intro f
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext z; simp [Finset.mem_sdiff]
      simp_rw [h1]
      rw [Finset.sum_comm, Finset.mul_sum]
    have hRHS : ∑ _f : S → Bool, ∑ z ∈ S, (degIn G S z : ℝ) ^ 2 =
        ∑ z ∈ S, (Fintype.card (S → Bool) : ℝ) * (degIn G S z : ℝ) ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hLHS, hRHS]
    refine Finset.sum_le_sum fun z hz => ?_
    let Nz := S.filter (fun x => G.Adj z x)
    have hz_not_Nz : z ∉ Nz := fun h => G.loopless.irrefl z (Finset.mem_filter.mp h).2
    have hdeg_eq : ∀ f : S → Bool, (degIn G (sub f) z : ℝ) =
        ∑ x ∈ Nz, if ∃ hx : x ∈ S, f ⟨x, hx⟩ = true then (1 : ℝ) else 0 := by
      intro f
      simp only [degIn, sub, Nz, Finset.sum_boole]
      congr 2; ext x; simp only [Finset.mem_filter]; tauto
    have hexpand : ∀ f : S → Bool,
        (if z ∉ sub f then (degIn G (sub f) z : ℝ) ^ 2 else 0) =
        ∑ x ∈ Nz, ∑ y ∈ Nz,
          (if f ⟨z, hz⟩ = false ∧ (∃ hx : x ∈ S, f ⟨x, hx⟩ = true) ∧ (∃ hy : y ∈ S, f ⟨y, hy⟩ = true)
            then (1 : ℝ) else 0) := by
      intro f
      have hz_iff : z ∉ sub f ↔ f ⟨z, hz⟩ = false := by
        simp only [sub, Finset.mem_filter, hz, true_and, not_exists, Bool.not_eq_true]
        exact ⟨fun h => h trivial, fun h _ => h⟩
      by_cases hzf : f ⟨z, hz⟩ = false
      · rw [if_pos (hz_iff.mpr hzf), hdeg_eq f, sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => by
          by_cases hx : ∃ hx : x ∈ S, f ⟨x, hx⟩ = true <;>
          by_cases hy : ∃ hy : y ∈ S, f ⟨y, hy⟩ = true <;>
          simp [hzf, hx, hy]
      · rw [if_neg (fun h => hzf (hz_iff.mp h))]
        symm; exact Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => by simp [hzf]
    simp_rw [hexpand]
    rw [Finset.sum_comm]
    have hswap2 : ∀ x ∈ Nz,
        ∑ f : S → Bool, ∑ y ∈ Nz,
          (if f ⟨z, hz⟩ = false ∧ (∃ hx : x ∈ S, f ⟨x, hx⟩ = true) ∧ (∃ hy : y ∈ S, f ⟨y, hy⟩ = true)
            then (1 : ℝ) else 0) =
        ∑ y ∈ Nz, ∑ f : S → Bool,
          (if f ⟨z, hz⟩ = false ∧ (∃ hx : x ∈ S, f ⟨x, hx⟩ = true) ∧ (∃ hy : y ∈ S, f ⟨y, hy⟩ = true)
            then (1 : ℝ) else 0) := fun _ _ => Finset.sum_comm
    rw [Finset.sum_congr rfl hswap2]
    have hpair_ge : ∀ x ∈ Nz, ∀ y ∈ Nz,
        (Fintype.card (S → Bool) : ℝ) / 8 ≤
        ∑ f : S → Bool,
          (if f ⟨z, hz⟩ = false ∧ (∃ hx : x ∈ S, f ⟨x, hx⟩ = true) ∧ (∃ hy : y ∈ S, f ⟨y, hy⟩ = true)
            then (1 : ℝ) else 0) := by
      intro x hx y hy
      have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
      have hyS : y ∈ S := (Finset.mem_filter.mp hy).1
      have hxz : (⟨x, hxS⟩ : {u // u ∈ S}) ≠ ⟨z, hz⟩ := fun h => hz_not_Nz (by
        have : x = z := congrArg Subtype.val h; rwa [← this])
      have hyz : (⟨y, hyS⟩ : {u // u ∈ S}) ≠ ⟨z, hz⟩ := fun h => hz_not_Nz (by
        have : y = z := congrArg Subtype.val h; rwa [← this])
      have hsimp : ∀ f : S → Bool,
          (if f ⟨z, hz⟩ = false ∧ (∃ hx' : x ∈ S, f ⟨x, hx'⟩ = true) ∧ (∃ hy' : y ∈ S, f ⟨y, hy'⟩ = true)
            then (1 : ℝ) else 0) =
          (if f ⟨z, hz⟩ = false ∧ f ⟨x, hxS⟩ = true ∧ f ⟨y, hyS⟩ = true then (1 : ℝ) else 0) := by
        intro f; congr 1; exact propext ⟨fun ⟨h1, ⟨_, h2⟩, ⟨_, h3⟩⟩ => ⟨h1, h2, h3⟩,
          fun ⟨h1, h2, h3⟩ => ⟨h1, ⟨hxS, h2⟩, ⟨hyS, h3⟩⟩⟩
      simp_rw [hsimp]
      let g : {u // u ∈ S} → Bool → ℝ := fun u b =>
        if u = ⟨z, hz⟩ then (if b = false then 1 else 0)
        else if u = ⟨x, hxS⟩ ∨ u = ⟨y, hyS⟩ then (if b = true then 1 else 0)
        else 1
      have hprod : ∀ f : S → Bool,
          (if f ⟨z, hz⟩ = false ∧ f ⟨x, hxS⟩ = true ∧ f ⟨y, hyS⟩ = true then (1 : ℝ) else 0) =
          ∏ u : {u // u ∈ S}, g u (f u) := by
        intro f
        by_cases hall : f ⟨z, hz⟩ = false ∧ f ⟨x, hxS⟩ = true ∧ f ⟨y, hyS⟩ = true
        · rw [if_pos hall]; symm
          exact Finset.prod_eq_one fun u _ => by
            by_cases h1 : u = ⟨z, hz⟩
            · subst h1; simp [g, hall.1]
            · by_cases h2 : u = ⟨x, hxS⟩
              · subst h2; simp [g, h1, hall.2.1]
              · by_cases h3 : u = ⟨y, hyS⟩
                · subst h3; simp [g, h1, hall.2.2]
                · simp [g, h1, h2, h3]
        · rw [if_neg hall]; symm
          by_cases h1 : f ⟨z, hz⟩ = false
          · by_cases h2 : f ⟨x, hxS⟩ = true
            · have h3 : f ⟨y, hyS⟩ ≠ true := fun h => hall ⟨h1, h2, h⟩
              exact Finset.prod_eq_zero (Finset.mem_univ ⟨y, hyS⟩) (by simp [g, hyz, h3])
            · exact Finset.prod_eq_zero (Finset.mem_univ ⟨x, hxS⟩) (by simp [g, hxz, h2])
          · exact Finset.prod_eq_zero (Finset.mem_univ ⟨z, hz⟩) (by simp [g, h1])
      simp_rw [hprod]
      have hps := (Fintype.prod_sum (fun (u : {u // u ∈ S}) (b : Bool) => g u b)).symm
      rw [hps]
      have hterm : ∀ u : {u // u ∈ S}, ∑ b : Bool, g u b =
          if u = ⟨z, hz⟩ ∨ u = ⟨x, hxS⟩ ∨ u = ⟨y, hyS⟩ then (1 : ℝ) else 2 := by
        intro u
        by_cases h1 : u = ⟨z, hz⟩
        · subst h1; simp [g]
        · by_cases h2 : u = ⟨x, hxS⟩ ∨ u = ⟨y, hyS⟩
          · simp [g, h1, h2]
          · simp [g, h1, h2]
      simp_rw [hterm]
      let T : Finset {u // u ∈ S} := {⟨z, hz⟩, ⟨x, hxS⟩, ⟨y, hyS⟩}
      have hTcard : T.card ≤ 3 := by
        have h1 : T.card ≤ ({⟨x, hxS⟩, ⟨y, hyS⟩} : Finset {u // u ∈ S}).card + 1 := Finset.card_insert_le _ _
        have h2 : ({⟨x, hxS⟩, ⟨y, hyS⟩} : Finset {u // u ∈ S}).card ≤ 2 :=
          (Finset.card_insert_le _ _).trans (by simp)
        omega
      have hprod_eq : ∏ u : {u // u ∈ S}, (if u = ⟨z, hz⟩ ∨ u = ⟨x, hxS⟩ ∨ u = ⟨y, hyS⟩ then (1 : ℝ) else 2) =
          (2 : ℝ) ^ (Fintype.card {u // u ∈ S} - T.card) := by
        have h1 : ∀ u : {u // u ∈ S}, (u = ⟨z, hz⟩ ∨ u = ⟨x, hxS⟩ ∨ u = ⟨y, hyS⟩) ↔ u ∈ T := by
          intro u; simp [T]
        simp_rw [h1]
        rw [← Finset.prod_sdiff (Finset.subset_univ T)]
        have hT1 : ∏ u ∈ T, (if u ∈ T then (1 : ℝ) else 2) = 1 :=
          Finset.prod_eq_one fun u hu => by simp [hu]
        have hT2 : ∏ u ∈ Finset.univ \ T, (if u ∈ T then (1 : ℝ) else 2) =
            (2 : ℝ) ^ (Finset.univ \ T).card := by
          calc ∏ u ∈ Finset.univ \ T, (if u ∈ T then (1 : ℝ) else 2)
              = ∏ _u ∈ Finset.univ \ T, (2 : ℝ) := Finset.prod_congr rfl fun u hu => by
                  simp [(Finset.mem_sdiff.mp hu).2]
            _ = (2 : ℝ) ^ (Finset.univ \ T).card := Finset.prod_const 2
        rw [hT1, hT2, mul_one, Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ]
      rw [hprod_eq]
      have hcard_fun : (Fintype.card (S → Bool) : ℝ) = (2 : ℝ) ^ Fintype.card {u // u ∈ S} := by
        rw [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
      rw [hcard_fun, div_le_iff₀ (by norm_num : (0 : ℝ) < 8)]
      have hTle : T.card ≤ Fintype.card {u // u ∈ S} := Finset.card_le_univ T
      have h2T : (2 : ℝ) ^ T.card ≤ 8 := by
        calc (2 : ℝ) ^ T.card ≤ (2 : ℝ) ^ 3 := pow_le_pow_right₀ (by norm_num) hTcard
          _ = 8 := by norm_num
      calc (2 : ℝ) ^ Fintype.card {u // u ∈ S}
          = (2 : ℝ) ^ (Fintype.card {u // u ∈ S} - T.card) * (2 : ℝ) ^ T.card := by
              rw [← pow_add, Nat.sub_add_cancel hTle]
        _ ≤ (2 : ℝ) ^ (Fintype.card {u // u ∈ S} - T.card) * 8 :=
              mul_le_mul_of_nonneg_left h2T (by positivity)
    have hsum_ge : (degIn G S z : ℝ) ^ 2 * ((Fintype.card (S → Bool) : ℝ) / 8) ≤
        ∑ x ∈ Nz, ∑ y ∈ Nz, ∑ f : S → Bool,
          (if f ⟨z, hz⟩ = false ∧ (∃ hx : x ∈ S, f ⟨x, hx⟩ = true) ∧ (∃ hy : y ∈ S, f ⟨y, hy⟩ = true)
            then (1 : ℝ) else 0) := by
      calc (degIn G S z : ℝ) ^ 2 * ((Fintype.card (S → Bool) : ℝ) / 8)
          = ∑ _x ∈ Nz, ∑ _y ∈ Nz, ((Fintype.card (S → Bool) : ℝ) / 8) := by
              simp only [Finset.sum_const, nsmul_eq_mul, Nz, degIn]; ring
        _ ≤ _ := Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hpair_ge x hx y hy
    linarith only [hsum_ge]
  by_contra hall
  push Not at hall
  have hlt : ∑ f : S → Bool, (8 * ∑ z ∈ S \ sub f, (degIn G (sub f) z : ℝ) ^ 2) <
      ∑ _f : S → Bool, ∑ z ∈ S, (degIn G S z : ℝ) ^ 2 :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun f _ => hall (sub f) (hsub_sub f)
  linarith only [havg, hlt]

/-- Convexity maximization on `[0, 1]^m` with `∑ w ≤ B`: for any `G` and `w : Fin m → ℝ` with
`0 ≤ w x ≤ 1` and `∑ w x ≤ B`, there exists `S : Finset (Fin m)` with `(S.card : ℝ) ≤ B + 1`
such that `∑ z, (∑ x ∈ univ.filter (G.Adj z), w x)^2 ≤ ∑ z, (degIn G S z)^2`. -/
lemma exists_indicator_quad_ge {m : ℕ} (G : SimpleGraph (Fin m)) (w : Fin m → ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) :
    ∃ S : Finset (Fin m), (S.card : ℝ) ≤ (∑ x : Fin m, w x) + 1 ∧
      ∑ z : Fin m, (∑ x ∈ Finset.univ.filter (fun x => G.Adj z x), w x) ^ 2 ≤
        ∑ z : Fin m, (degIn G S z : ℝ) ^ 2 := by
  let Q : (Fin m → ℝ) → ℝ := fun v =>
    ∑ z : Fin m, (∑ x ∈ Finset.univ.filter (fun x => G.Adj z x), v x) ^ 2
  let fracCnt : (Fin m → ℝ) → ℕ := fun v =>
    (Finset.univ.filter (fun x : Fin m => 0 < v x ∧ v x < 1)).card
  have hstep : ∀ k : ℕ, ∀ v : Fin m → ℝ,
      (∀ x, 0 ≤ v x) → (∀ x, v x ≤ 1) → fracCnt v ≤ k →
      ∃ v' : Fin m → ℝ, (∀ x, 0 ≤ v' x) ∧ (∀ x, v' x ≤ 1) ∧
        (∑ x : Fin m, v' x = ∑ x : Fin m, v x) ∧ Q v ≤ Q v' ∧ fracCnt v' ≤ 1 := by
    intro k
    induction k with
    | zero =>
      intro v hv0 hv1 hfc
      exact ⟨v, hv0, hv1, rfl, le_rfl, by omega⟩
    | succ k ih =>
      intro v hv0 hv1 hfc
      by_cases h1 : fracCnt v ≤ 1
      · exact ⟨v, hv0, hv1, rfl, le_rfl, h1⟩
      · have h2 : 1 < (Finset.univ.filter (fun x : Fin m => 0 < v x ∧ v x < 1)).card := by
          dsimp only [fracCnt] at h1; omega
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
        have ha' := (Finset.mem_filter.mp ha).2
        have hb' := (Finset.mem_filter.mp hb).2
        -- Shift mass `δ` from `b` to `a`: `v_δ = v + δ (e_a - e_b)` stays in `[0, 1]^m` on `[-δ₁, δ₂]`.
        let δ₁ : ℝ := min (v a) (1 - v b)
        let δ₂ : ℝ := min (1 - v a) (v b)
        have hδ₁_pos : 0 < δ₁ := lt_min ha'.1 (by linarith only [hb'.2])
        have hδ₂_pos : 0 < δ₂ := lt_min (by linarith only [ha'.2]) hb'.1
        let shift : ℝ → Fin m → ℝ := fun δ x =>
          if x = a then v a + δ else if x = b then v b - δ else v x
        have hQ_convex : Q v ≤ max (Q (shift (-δ₁))) (Q (shift δ₂)) := by
          have hlin : ∀ z : Fin m, ∃ c₀ c₁ : ℝ, ∀ δ : ℝ,
              ∑ x ∈ Finset.univ.filter (fun x => G.Adj z x), shift δ x = c₀ + c₁ * δ := by
            intro z
            refine ⟨∑ x ∈ Finset.univ.filter (fun x => G.Adj z x), v x,
              (if G.Adj z a then (1 : ℝ) else 0) - (if G.Adj z b then (1 : ℝ) else 0), fun δ => ?_⟩
            have hpw : ∀ x : Fin m, shift δ x = v x + ((if x = a then (1 : ℝ) else 0) -
                (if x = b then (1 : ℝ) else 0)) * δ := by
              intro x; simp only [shift]
              by_cases hxa : x = a
              · subst hxa; simp [hab]
              · by_cases hxb : x = b
                · subst hxb; simp [hxa]; ring
                · simp [hxa, hxb]
            simp_rw [hpw, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib]
            have hfa : ∑ x ∈ Finset.univ.filter (fun x => G.Adj z x), (if x = a then (1 : ℝ) else 0) =
                if G.Adj z a then 1 else 0 := by rw [Finset.sum_ite_eq']; simp
            have hfb : ∑ x ∈ Finset.univ.filter (fun x => G.Adj z x), (if x = b then (1 : ℝ) else 0) =
                if G.Adj z b then 1 else 0 := by rw [Finset.sum_ite_eq']; simp
            rw [hfa, hfb]
          choose c₀ c₁ hc using hlin
          have hQ_eq : ∀ δ : ℝ, Q (shift δ) =
              (∑ z : Fin m, c₀ z ^ 2) + 2 * (∑ z : Fin m, c₀ z * c₁ z) * δ +
              (∑ z : Fin m, c₁ z ^ 2) * δ ^ 2 := by
            intro δ
            simp only [Q]
            simp_rw [hc]
            have hexp : ∀ z : Fin m, (c₀ z + c₁ z * δ) ^ 2 =
                c₀ z ^ 2 + (2 * (c₀ z * c₁ z) * δ + c₁ z ^ 2 * δ ^ 2) := fun z => by ring
            simp_rw [hexp, Finset.sum_add_distrib, ← Finset.sum_mul]
            rw [← Finset.mul_sum]; ring
          have hQ0 : Q v = ∑ z : Fin m, c₀ z ^ 2 := by
            have h0 : shift 0 = v := by
              funext x; simp only [shift]; split_ifs with hxa hxb
              · subst hxa; ring
              · subst hxb; ring
              · rfl
            have := hQ_eq 0
            rw [h0] at this; linarith only [this]
          have hA_nn : 0 ≤ ∑ z : Fin m, c₁ z ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
          have hcomb : (δ₂ / (δ₁ + δ₂)) * Q (shift (-δ₁)) + (δ₁ / (δ₁ + δ₂)) * Q (shift δ₂) =
              Q v + (∑ z : Fin m, c₁ z ^ 2) * (δ₁ * δ₂) := by
            rw [hQ_eq (-δ₁), hQ_eq δ₂, hQ0]
            have hne : δ₁ + δ₂ ≠ 0 := (add_pos hδ₁_pos hδ₂_pos).ne'
            field_simp [hne]; ring
          have hge : Q v ≤ (δ₂ / (δ₁ + δ₂)) * Q (shift (-δ₁)) + (δ₁ / (δ₁ + δ₂)) * Q (shift δ₂) := by
            rw [hcomb]; linarith only [mul_nonneg hA_nn (mul_pos hδ₁_pos hδ₂_pos).le]
          have hle_max : (δ₂ / (δ₁ + δ₂)) * Q (shift (-δ₁)) + (δ₁ / (δ₁ + δ₂)) * Q (shift δ₂) ≤
              max (Q (shift (-δ₁))) (Q (shift δ₂)) := by
            have h1 : (δ₂ / (δ₁ + δ₂)) * Q (shift (-δ₁)) ≤
                (δ₂ / (δ₁ + δ₂)) * max (Q (shift (-δ₁))) (Q (shift δ₂)) :=
              mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
            have h2 : (δ₁ / (δ₁ + δ₂)) * Q (shift δ₂) ≤
                (δ₁ / (δ₁ + δ₂)) * max (Q (shift (-δ₁))) (Q (shift δ₂)) :=
              mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
            have hsum1 : δ₂ / (δ₁ + δ₂) + δ₁ / (δ₁ + δ₂) = 1 := by
              have hne : δ₁ + δ₂ ≠ 0 := (add_pos hδ₁_pos hδ₂_pos).ne'
              field_simp [hne]; ring
            calc _ ≤ (δ₂ / (δ₁ + δ₂) + δ₁ / (δ₁ + δ₂)) * max (Q (shift (-δ₁))) (Q (shift δ₂)) := by
                    linarith only [h1, h2]
              _ = max (Q (shift (-δ₁))) (Q (shift δ₂)) := by rw [hsum1, one_mul]
          exact hge.trans hle_max
        have hsum_shift : ∀ δ : ℝ, ∑ x : Fin m, shift δ x = ∑ x : Fin m, v x := by
          intro δ
          have hpw : ∀ x : Fin m, shift δ x = v x + ((if x = a then δ else 0) - (if x = b then δ else 0)) := by
            intro x; simp only [shift]
            by_cases hxa : x = a
            · subst hxa; simp [hab]
            · by_cases hxb : x = b
              · subst hxb; simp [hxa]; ring
              · simp [hxa, hxb]
          simp_rw [hpw, Finset.sum_add_distrib, Finset.sum_sub_distrib]
          simp
        -- Pick whichever endpoint `-δ₁` or `δ₂` achieves the max; both strictly decrease `fracCnt`.
        rcases le_total (Q (shift (-δ₁))) (Q (shift δ₂)) with hle | hge
        · have hQv : Q v ≤ Q (shift δ₂) := hQ_convex.trans (by rw [max_eq_right hle])
          have hv'0 : ∀ x, 0 ≤ shift δ₂ x := fun x => by
            simp only [shift]; split_ifs with hxa hxb
            · linarith only [ha'.1, hδ₂_pos]
            · have : δ₂ ≤ v b := min_le_right _ _; linarith only [this]
            · exact hv0 x
          have hv'1 : ∀ x, shift δ₂ x ≤ 1 := fun x => by
            simp only [shift]; split_ifs with hxa hxb
            · have : δ₂ ≤ 1 - v a := min_le_left _ _; linarith only [this]
            · linarith only [hb'.2, hδ₂_pos]
            · exact hv1 x
          have hfc_lt : fracCnt (shift δ₂) < fracCnt v := by
            refine Finset.card_lt_card ⟨fun x hx => ?_, ?_⟩
            · have hx' := (Finset.mem_filter.mp hx).2
              by_cases hxa : x = a
              · subst hxa; exact ha
              · by_cases hxb : x = b
                · subst hxb; exact hb
                · simp only [shift, if_neg hxa, if_neg hxb] at hx'
                  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'⟩
            · intro hsub
              rcases min_cases (1 - v a) (v b) with ⟨hmin, _⟩ | ⟨hmin, _⟩
              · have ha_in := hsub ha
                have ha_lt := (Finset.mem_filter.mp ha_in).2.2
                simp only [shift, ite_true, δ₂, hmin] at ha_lt; linarith
              · have hb_in := hsub hb
                have hb_gt := (Finset.mem_filter.mp hb_in).2.1
                simp only [shift, if_neg hab.symm, ite_true, δ₂, hmin] at hb_gt; linarith
          obtain ⟨v', hv0', hv1', hsum', hQ', hfc'⟩ := ih (shift δ₂) hv'0 hv'1 (by omega)
          exact ⟨v', hv0', hv1', hsum'.trans (hsum_shift δ₂), hQv.trans hQ', hfc'⟩
        · have hQv : Q v ≤ Q (shift (-δ₁)) := hQ_convex.trans (by rw [max_eq_left hge])
          have hv'0 : ∀ x, 0 ≤ shift (-δ₁) x := fun x => by
            simp only [shift]; split_ifs with hxa hxb
            · have : δ₁ ≤ v a := min_le_left _ _; linarith only [this]
            · linarith only [hb'.1, hδ₁_pos]
            · exact hv0 x
          have hv'1 : ∀ x, shift (-δ₁) x ≤ 1 := fun x => by
            simp only [shift]; split_ifs with hxa hxb
            · linarith only [ha'.2, hδ₁_pos]
            · have : δ₁ ≤ 1 - v b := min_le_right _ _; linarith only [this]
            · exact hv1 x
          have hfc_lt : fracCnt (shift (-δ₁)) < fracCnt v := by
            refine Finset.card_lt_card ⟨fun x hx => ?_, ?_⟩
            · have hx' := (Finset.mem_filter.mp hx).2
              by_cases hxa : x = a
              · subst hxa; exact ha
              · by_cases hxb : x = b
                · subst hxb; exact hb
                · simp only [shift, if_neg hxa, if_neg hxb] at hx'
                  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'⟩
            · intro hsub
              rcases min_cases (v a) (1 - v b) with ⟨hmin, _⟩ | ⟨hmin, _⟩
              · have ha_in := hsub ha
                have ha_gt := (Finset.mem_filter.mp ha_in).2.1
                simp only [shift, ite_true, δ₁, hmin] at ha_gt; linarith
              · have hb_in := hsub hb
                have hb_lt := (Finset.mem_filter.mp hb_in).2.2
                simp only [shift, if_neg hab.symm, ite_true, δ₁, hmin] at hb_lt; linarith
          obtain ⟨v', hv0', hv1', hsum', hQ', hfc'⟩ := ih (shift (-δ₁)) hv'0 hv'1 (by omega)
          exact ⟨v', hv0', hv1', hsum'.trans (hsum_shift (-δ₁)), hQv.trans hQ', hfc'⟩
  obtain ⟨v', hv0', hv1', hsum', hQ', hfc'⟩ := hstep (fracCnt w) w hw0 hw1 le_rfl
  let S : Finset (Fin m) := Finset.univ.filter (fun x => 0 < v' x)
  let Ones : Finset (Fin m) := Finset.univ.filter (fun x => v' x = 1)
  let Frac : Finset (Fin m) := Finset.univ.filter (fun x => 0 < v' x ∧ v' x < 1)
  have hS_eq : S = Ones ∪ Frac := by
    ext x; simp only [S, Ones, Frac, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hpos
      rcases eq_or_lt_of_le (hv1' x) with h1 | hlt
      · exact Or.inl h1
      · exact Or.inr ⟨hpos, hlt⟩
    · rintro (h1 | ⟨hpos, _⟩)
      · linarith
      · exact hpos
  have hS_card : (S.card : ℝ) ≤ (∑ x : Fin m, w x) + 1 := by
    have h1 : S.card ≤ Ones.card + Frac.card := by rw [hS_eq]; exact Finset.card_union_le _ _
    have h2 : (Ones.card : ℝ) ≤ ∑ x : Fin m, v' x := by
      calc (Ones.card : ℝ) = ∑ _x ∈ Ones, (1 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ = ∑ x ∈ Ones, v' x := Finset.sum_congr rfl fun x hx => (Finset.mem_filter.mp hx).2.symm
        _ ≤ ∑ x : Fin m, v' x := Finset.sum_le_univ_sum_of_nonneg hv0'
    have h3 : (Frac.card : ℝ) ≤ 1 := by exact_mod_cast hfc'
    have h1R : (S.card : ℝ) ≤ (Ones.card : ℝ) + (Frac.card : ℝ) := by exact_mod_cast h1
    linarith only [h1R, h2, h3, hsum']
  refine ⟨S, hS_card, hQ'.trans ?_⟩
  refine Finset.sum_le_sum fun z _ => ?_
  have hinner : ∑ x ∈ Finset.univ.filter (fun x => G.Adj z x), v' x ≤ (degIn G S z : ℝ) := by
    have hdeg_eq : (degIn G S z : ℝ) =
        ∑ x ∈ Finset.univ.filter (fun x => G.Adj z x), if 0 < v' x then (1 : ℝ) else 0 := by
      simp only [degIn, S, Finset.sum_boole]
      congr 2; ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
    rw [hdeg_eq]
    refine Finset.sum_le_sum fun x _ => ?_
    split_ifs with hpos
    · exact hv1' x
    · linarith only [hv0' x, hpos]
  have hnn : 0 ≤ ∑ x ∈ Finset.univ.filter (fun x => G.Adj z x), v' x :=
    Finset.sum_nonneg fun x _ => hv0' x
  exact pow_le_pow_left₀ hnn hinner 2

/-- Greedy pruning lemma: if `U` has every term in `[L, D]` and `0 ≤ E₀ ≤ ∑_{z ∈ U} Y z`,
then there exists `U' ⊆ U` with `E₀ ≤ ∑_{z ∈ U'} Y z ≤ E₀ + D` and `|U'| * L ≤ E₀ + D`. -/
lemma exists_pruned_subset {ι : Type*} [DecidableEq ι] (U : Finset ι) (Y : ι → ℝ)
    {L D E₀ : ℝ} (_hL : 0 ≤ L) (hD : 0 ≤ D) (hE0 : 0 ≤ E₀)
    (hbounds : ∀ z ∈ U, L ≤ Y z ∧ Y z ≤ D) (hsum : E₀ ≤ ∑ z ∈ U, Y z) :
    ∃ U' ⊆ U, E₀ ≤ ∑ z ∈ U', Y z ∧ ∑ z ∈ U', Y z ≤ E₀ + D ∧ (U'.card : ℝ) * L ≤ E₀ + D := by
  induction U using Finset.strongInduction with
  | H U ih =>
  by_cases hle : ∑ z ∈ U, Y z ≤ E₀ + D
  · refine ⟨U, subset_rfl, hsum, hle, ?_⟩
    have hlow : (U.card : ℝ) * L ≤ ∑ z ∈ U, Y z := by
      calc (U.card : ℝ) * L = ∑ _z ∈ U, L := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ z ∈ U, Y z := Finset.sum_le_sum fun z hz => (hbounds z hz).1
    exact hlow.trans hle
  · push Not at hle
    have hne : U.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      subst hempty; simp at hsum hle; linarith only [hsum, hle, hD, hE0]
    obtain ⟨z₀, hz₀⟩ := hne
    have hsum_erase : E₀ ≤ ∑ z ∈ U.erase z₀, Y z := by
      have h1 := Finset.add_sum_erase U Y hz₀
      have h2 := (hbounds z₀ hz₀).2
      linarith only [h1, h2, hle]
    obtain ⟨U', hU'sub, h1, h2, h3⟩ := ih (U.erase z₀) (Finset.erase_ssubset hz₀)
      (fun z hz => hbounds z (Finset.erase_subset _ _ hz)) hsum_erase
    exact ⟨U', hU'sub.trans (Finset.erase_subset _ _), h1, h2, h3⟩

/-- Counting red-good pairs inside an `s`-subset `I' ⊆ Fin n` on which `φ_B` is injective:
given fiber bound `F_max`, codegree-sum bound `∑_z degIn G_R A z ^ 2 ≤ (1/1000) t^2` for all `|A| ≤ t`
(where `t ≥ s / F_max + 1`), at least `s^2 / 4` unordered pairs in `B = φ_B(I')` are red-good. -/
lemma card_redGood_pairs_ge {n m t : ℕ} {F_max : ℝ} (hF : 0 < F_max)
    (G_R : SimpleGraph (Fin m)) (φ_R φ_B : Fin n → Fin m)
    (hfiber : ∀ x : Fin m, ((Finset.univ.filter (fun v : Fin n => φ_R v = x)).card : ℝ) ≤ F_max)
    (hcodeg : ∀ A : Finset (Fin m), A.card ≤ t →
      ∑ z ∈ Finset.univ \ A, (degIn G_R A z : ℝ) ^ 2 ≤ (1 / 1000 : ℝ) * (t : ℝ) ^ 2)
    (I' : Finset (Fin n)) (hinj : Set.InjOn φ_B (I' : Set (Fin n)))
    (hs_t : (I'.card : ℝ) / F_max + 1 ≤ (t : ℝ))
    (ht_le : (t : ℝ) ≤ 2 * ((I'.card : ℝ) / F_max))
    (hF_small : F_max ≤ (1 / 10 : ℝ) * (I'.card : ℝ))
    (hs_ge : 16 ≤ I'.card) :
    let RedGood : Finset (EdgeIdx m) := Finset.univ.filter (fun e =>
      ∃ u ∈ I', ∃ v ∈ I', φ_B u = e.1.1 ∧ φ_B v = e.1.2 ∧ ¬ pairBad G_R φ_R u v)
    (1 / 4 : ℝ) * (I'.card : ℝ) ^ 2 ≤ (RedGood.card : ℝ) := by
  intro RedGood
  let B : Finset (Fin m) := I'.image φ_B
  set s := I'.card
  have hs_pos : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr (by omega)
  have hI'ne : I'.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨u₀, _⟩ := hI'ne
  let AllPairs : Finset (EdgeIdx m) := Finset.univ.filter (fun e =>
    ∃ u ∈ I', ∃ v ∈ I', φ_B u = e.1.1 ∧ φ_B v = e.1.2)
  let BadPairs : Finset (EdgeIdx m) := Finset.univ.filter (fun e =>
    ∃ u ∈ I', ∃ v ∈ I', φ_B u = e.1.1 ∧ φ_B v = e.1.2 ∧ pairBad G_R φ_R u v)
  have hBcard : B.card = s := Finset.card_image_of_injOn hinj
  have hAll_card : (AllPairs.card : ℝ) = (s : ℝ) * ((s : ℝ) - 1) / 2 := by
    have hEq : AllPairs = Finset.univ.filter (fun e : EdgeIdx m => e.1.1 ∈ B ∧ e.1.2 ∈ B) := by
      ext e; simp only [AllPairs, B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨u, hu, v, hv, h1, h2⟩; exact ⟨⟨u, hu, h1⟩, ⟨v, hv, h2⟩⟩
      · rintro ⟨⟨u, hu, h1⟩, ⟨v, hv, h2⟩⟩; exact ⟨u, hu, v, hv, h1, h2⟩
    rw [hEq]
    have h2 : 2 * (Finset.univ.filter (fun e : EdgeIdx m => e.1.1 ∈ B ∧ e.1.2 ∈ B)).card =
        B.card * (B.card - 1) := by
      have hoff : B.offDiag.card = B.card * (B.card - 1) := by
        rw [Finset.offDiag_card, Nat.mul_sub_one]
      let L1 := B.offDiag.filter (fun p => p.1 < p.2)
      let L2 := B.offDiag.filter (fun p => p.2 < p.1)
      have hdisj : Disjoint L1 L2 := by
        rw [Finset.disjoint_left]; intro p h1 h2
        exact lt_asymm (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
      have hunion : L1 ∪ L2 = B.offDiag := by
        ext p; simp only [L1, L2, Finset.mem_union, Finset.mem_filter, Finset.mem_offDiag]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro ⟨h1, h2, hne⟩
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact Or.inl ⟨⟨h1, h2, hne⟩, hlt⟩
          · exact Or.inr ⟨⟨h1, h2, hne⟩, hgt⟩
      have hL12 : L1.card = L2.card := by
        refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
        · intro p hp
          simp only [L1, L2, Finset.mem_filter, Finset.mem_offDiag] at hp ⊢
          exact ⟨⟨hp.1.2.1, hp.1.1, hp.1.2.2.symm⟩, hp.2⟩
        · intro p _ q _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
        · intro q hq
          simp only [L1, L2, Finset.mem_filter, Finset.mem_offDiag] at hq ⊢
          exact ⟨(q.2, q.1), ⟨⟨hq.1.2.1, hq.1.1, hq.1.2.2.symm⟩, hq.2⟩, rfl⟩
      have hL1_eq : L1.card = (Finset.univ.filter (fun e : EdgeIdx m => e.1.1 ∈ B ∧ e.1.2 ∈ B)).card := by
        refine Finset.card_bij (fun p hp => ⟨p, (Finset.mem_filter.mp hp).2⟩) ?_ ?_ ?_
        · intro p hp
          simp only [L1, Finset.mem_filter, Finset.mem_offDiag] at hp
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.1.1, hp.1.2.1⟩
        · intro p _ q _ h; exact congrArg Subtype.val h
        · intro e he
          have he' := (Finset.mem_filter.mp he).2
          refine ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨he'.1, he'.2, e.2.ne⟩, e.2⟩,
            Subtype.ext rfl⟩
      rw [← hL1_eq, ← hoff, ← hunion, Finset.card_union_of_disjoint hdisj, hL12]; omega
    rw [hBcard] at h2
    have h2R : 2 * ((Finset.univ.filter (fun e : EdgeIdx m => e.1.1 ∈ B ∧ e.1.2 ∈ B)).card : ℝ) =
        (s : ℝ) * ((s : ℝ) - 1) := by
      have hsub1 : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ s)]; simp
      have hcast : (2 * (Finset.univ.filter (fun e : EdgeIdx m => e.1.1 ∈ B ∧ e.1.2 ∈ B)).card : ℝ) =
          ((s * (s - 1) : ℕ) : ℝ) := by exact_mod_cast h2
      simpa [Nat.cast_mul, hsub1] using hcast
    linarith only [h2R]
  have hcov : AllPairs ⊆ RedGood ∪ BadPairs := by
    intro e he
    rcases (Finset.mem_filter.mp he).2 with ⟨u, hu, v, hv, h1, h2⟩
    by_cases hbad : pairBad G_R φ_R u v
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, hu, v, hv, h1, h2, hbad⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, hu, v, hv, h1, h2, hbad⟩)
  let w : Fin m → ℝ := fun x => ((I'.filter (fun u => φ_R u = x)).card : ℝ)
  have hw0 : ∀ x, 0 ≤ w x := fun _ => Nat.cast_nonneg _
  have hwF : ∀ x, w x ≤ F_max := fun x => by
    have hsub : I'.filter (fun u => φ_R u = x) ⊆ Finset.univ.filter (fun u => φ_R u = x) :=
      fun u hu => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hfiber x)
  have hw_sum : ∑ x : Fin m, w x = (s : ℝ) := by
    have h1 := Finset.card_eq_sum_card_fiberwise (f := φ_R) (s := I') (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    have h1R : (I'.card : ℝ) = ∑ x : Fin m, ((I'.filter (fun u => φ_R u = x)).card : ℝ) := by exact_mod_cast h1
    exact h1R.symm
  have hBad_le : 2 * (BadPairs.card : ℝ) ≤
      (∑ x : Fin m, (w x) ^ 2) + ∑ z : Fin m, (∑ x ∈ Finset.univ.filter (fun x => G_R.Adj z x), w x) ^ 2 := by
    let OrdBad := (I' ×ˢ I').filter (fun p => p.1 ≠ p.2 ∧ pairBad G_R φ_R p.1 p.2)
    have h2bad : 2 * BadPairs.card ≤ OrdBad.card := by
      let B1 := OrdBad.filter (fun p => φ_B p.1 < φ_B p.2)
      let B2 := OrdBad.filter (fun p => φ_B p.2 < φ_B p.1)
      have hdisj : Disjoint B1 B2 := by
        rw [Finset.disjoint_left]; intro p h1 h2
        exact lt_asymm (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
      have hB12 : B1.card = B2.card := by
        refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
        · intro p hp
          simp only [B1, B2, OrdBad, Finset.mem_filter, Finset.mem_product] at hp ⊢
          exact ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, hp.1.2.1.symm, pairBad_symm G_R φ_R hp.1.2.2⟩, hp.2⟩
        · intro p _ q _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
        · intro q hq
          simp only [B1, B2, OrdBad, Finset.mem_filter, Finset.mem_product] at hq ⊢
          exact ⟨(q.2, q.1), ⟨⟨⟨hq.1.1.2, hq.1.1.1⟩, hq.1.2.1.symm, pairBad_symm G_R φ_R hq.1.2.2⟩, hq.2⟩, rfl⟩
      have hBad_le_B1 : BadPairs.card ≤ B1.card := by
        have hmap : ∀ e ∈ BadPairs, ∃ p ∈ B1, φ_B p.1 = e.1.1 ∧ φ_B p.2 = e.1.2 := by
          intro e he
          rcases (Finset.mem_filter.mp he).2 with ⟨u, hu, v, hv, h1, h2, hbad⟩
          have hne : u ≠ v := fun h => by subst h; exact e.2.ne (h1.symm.trans h2)
          have hlt : φ_B u < φ_B v := by rw [h1, h2]; exact e.2
          exact ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hne, hbad⟩, hlt⟩, h1, h2⟩
        choose f hf_mem hf1 hf2 using hmap
        refine Finset.card_le_card_of_injOn (fun e => if h : e ∈ BadPairs then f e h else (u₀, u₀))
          (fun e he => by
            have he' : e ∈ BadPairs := Finset.mem_coe.mp he
            dsimp only; rw [dif_pos he']; exact Finset.mem_coe.mpr (hf_mem e he')) ?_
        intro e₁ he₁ e₂ he₂ heq
        have he₁' : e₁ ∈ BadPairs := Finset.mem_coe.mp he₁
        have he₂' : e₂ ∈ BadPairs := Finset.mem_coe.mp he₂
        dsimp only at heq
        rw [dif_pos he₁', dif_pos he₂'] at heq
        apply Subtype.ext; apply Prod.ext
        · rw [← hf1 e₁ he₁', ← hf1 e₂ he₂', heq]
        · rw [← hf2 e₁ he₁', ← hf2 e₂ he₂', heq]
      have hsub : B1 ∪ B2 ⊆ OrdBad := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      have hu := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj, ← hB12] at hu
      omega
    have hOrd_le : (OrdBad.card : ℝ) ≤
        (∑ x : Fin m, (w x) ^ 2) + ∑ z : Fin m, (∑ x ∈ Finset.univ.filter (fun x => G_R.Adj z x), w x) ^ 2 := by
      have h1 : (OrdBad.card : ℝ) ≤
          ∑ p ∈ I' ×ˢ I', ((if φ_R p.1 = φ_R p.2 then (1 : ℝ) else 0) +
            ∑ z : Fin m, if G_R.Adj (φ_R p.1) z ∧ G_R.Adj (φ_R p.2) z then (1 : ℝ) else 0) := by
        rw [Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_le_sum fun p _ => ?_
        by_cases hp : p.1 ≠ p.2 ∧ pairBad G_R φ_R p.1 p.2
        · rw [if_pos hp]; simp only [Nat.cast_one]
          rcases hp.2 with heq | ⟨z₀, hz1, hz2⟩
          · rw [if_pos heq]
            have hnn : 0 ≤ ∑ z : Fin m, if G_R.Adj (φ_R p.1) z ∧ G_R.Adj (φ_R p.2) z then (1 : ℝ) else 0 :=
              Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
            linarith only [hnn]
          · have h1le : (1 : ℝ) ≤ ∑ z : Fin m, if G_R.Adj (φ_R p.1) z ∧ G_R.Adj (φ_R p.2) z then (1 : ℝ) else 0 := by
              calc (1 : ℝ) = (if G_R.Adj (φ_R p.1) z₀ ∧ G_R.Adj (φ_R p.2) z₀ then (1 : ℝ) else 0) := by
                    rw [if_pos ⟨hz1, hz2⟩]
                _ ≤ _ := Finset.single_le_sum (f := fun z => if G_R.Adj (φ_R p.1) z ∧ G_R.Adj (φ_R p.2) z then (1 : ℝ) else 0)
                    (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ z₀)
            have hnn : 0 ≤ (if φ_R p.1 = φ_R p.2 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
            linarith only [h1le, hnn]
        · rw [if_neg hp]; simp only [Nat.cast_zero]
          refine add_nonneg (by split_ifs <;> norm_num) (Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
      rw [Finset.sum_add_distrib] at h1
      have hdiag : ∑ p ∈ I' ×ˢ I', (if φ_R p.1 = φ_R p.2 then (1 : ℝ) else 0) = ∑ x : Fin m, (w x) ^ 2 := by
        have hrew : ∀ p : Fin n × Fin n, (if φ_R p.1 = φ_R p.2 then (1 : ℝ) else 0) =
            ∑ x : Fin m, (if φ_R p.1 = x then (1 : ℝ) else 0) * (if φ_R p.2 = x then (1 : ℝ) else 0) := by
          intro p
          rw [Finset.sum_eq_single (φ_R p.1)]
          · by_cases heq : φ_R p.1 = φ_R p.2
            · simp [heq]
            · simp [heq, Ne.symm heq]
          · intro x _ hx; simp [Ne.symm hx]
          · intro h; exact absurd (Finset.mem_univ _) h
        simp_rw [hrew]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_product, sq]
        have hw_eq : w x = ∑ u ∈ I', if φ_R u = x then (1 : ℝ) else 0 := by
          simp [w, Finset.sum_boole]
        rw [hw_eq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => by dsimp only; rw [Finset.mul_sum]
      have hoff : ∑ p ∈ I' ×ˢ I', ∑ z : Fin m, (if G_R.Adj (φ_R p.1) z ∧ G_R.Adj (φ_R p.2) z then (1 : ℝ) else 0) =
          ∑ z : Fin m, (∑ x ∈ Finset.univ.filter (fun x => G_R.Adj z x), w x) ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_product]
        have hinner : ∑ x ∈ Finset.univ.filter (fun x => G_R.Adj z x), w x =
            ∑ u ∈ I', if G_R.Adj (φ_R u) z then (1 : ℝ) else 0 := by
          have hw_eq : ∀ x, w x = ∑ u ∈ I', if φ_R u = x then (1 : ℝ) else 0 := fun x => by
            simp [w, Finset.sum_boole]
          simp_rw [hw_eq]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun u _ => ?_
          by_cases hadj : G_R.Adj (φ_R u) z
          · rw [if_pos hadj, Finset.sum_eq_single (φ_R u)]
            · simp
            · intro x _ hx; simp [Ne.symm hx]
            · intro h; exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj.symm⟩) h
          · rw [if_neg hadj]
            exact Finset.sum_eq_zero fun x hx => by
              have hzx := (Finset.mem_filter.mp hx).2
              have hne : φ_R u ≠ x := fun h => hadj (by rw [h]; exact hzx.symm)
              simp [hne]
        rw [hinner, sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => by
          by_cases h1 : G_R.Adj (φ_R u) z <;> by_cases h2 : G_R.Adj (φ_R v) z <;> simp [h1, h2]
      rw [hdiag, hoff] at h1
      exact h1
    exact (by exact_mod_cast h2bad : 2 * (BadPairs.card : ℝ) ≤ (OrdBad.card : ℝ)).trans hOrd_le
  -- Bound `∑ x, w x ^ 2 ≤ F_max * s` and `∑ z, (∑_{x ~ z} w x)^2 ≤ F_max^2 * (9 / 1000) * t^2`.
  have hdiag_bd : ∑ x : Fin m, (w x) ^ 2 ≤ F_max * (s : ℝ) := by
    calc ∑ x : Fin m, (w x) ^ 2 ≤ ∑ x : Fin m, F_max * w x :=
          Finset.sum_le_sum fun x _ => by nlinarith only [hw0 x, hwF x]
      _ = F_max * ∑ x : Fin m, w x := (Finset.mul_sum _ _ _).symm
      _ = F_max * (s : ℝ) := by rw [hw_sum]
  have hoff_bd : ∑ z : Fin m, (∑ x ∈ Finset.univ.filter (fun x => G_R.Adj z x), w x) ^ 2 ≤
      F_max ^ 2 * ((9 / 1000 : ℝ) * (t : ℝ) ^ 2) := by
    let w' : Fin m → ℝ := fun x => w x / F_max
    have hw'0 : ∀ x, 0 ≤ w' x := fun x => div_nonneg (hw0 x) hF.le
    have hw'1 : ∀ x, w' x ≤ 1 := fun x => (div_le_one hF).mpr (hwF x)
    obtain ⟨S, hScard, hSge⟩ := exists_indicator_quad_ge G_R w' hw'0 hw'1
    have hS_le_t : S.card ≤ t := by
      have h1 : (S.card : ℝ) ≤ (t : ℝ) := by
        have hsum' : ∑ x : Fin m, w' x = (s : ℝ) / F_max := by
          simp only [w', ← Finset.sum_div, hw_sum]
        rw [hsum'] at hScard; exact hScard.trans hs_t
      exact_mod_cast h1
    obtain ⟨A, hAsub, hAbip⟩ := exists_bipartition_sum_sq G_R S
    have hA_le_t : A.card ≤ t := (Finset.card_le_card hAsub).trans hS_le_t
    have hS_tot : ∑ z : Fin m, (degIn G_R S z : ℝ) ^ 2 ≤ (9 / 1000 : ℝ) * (t : ℝ) ^ 2 := by
      have hsplit : ∑ z : Fin m, (degIn G_R S z : ℝ) ^ 2 =
          (∑ z ∈ Finset.univ \ S, (degIn G_R S z : ℝ) ^ 2) + ∑ z ∈ S, (degIn G_R S z : ℝ) ^ 2 := by
        rw [← Finset.sum_union Finset.sdiff_disjoint, Finset.sdiff_union_of_subset (Finset.subset_univ S)]
      have h1 := hcodeg S hS_le_t
      have h2 : ∑ z ∈ S, (degIn G_R S z : ℝ) ^ 2 ≤ 8 * ((1 / 1000 : ℝ) * (t : ℝ) ^ 2) := by
        have hsub' : S \ A ⊆ Finset.univ \ A := Finset.sdiff_subset_sdiff (Finset.subset_univ S) subset_rfl
        have hle' : ∑ z ∈ S \ A, (degIn G_R A z : ℝ) ^ 2 ≤ ∑ z ∈ Finset.univ \ A, (degIn G_R A z : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub' fun _ _ _ => sq_nonneg _
        exact hAbip.trans (mul_le_mul_of_nonneg_left (hle'.trans (hcodeg A hA_le_t)) (by norm_num))
      linarith only [hsplit, h1, h2]
    have hscale : ∑ z : Fin m, (∑ x ∈ Finset.univ.filter (fun x => G_R.Adj z x), w x) ^ 2 =
        F_max ^ 2 * ∑ z : Fin m, (∑ x ∈ Finset.univ.filter (fun x => G_R.Adj z x), w' x) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [w', ← Finset.sum_div, div_pow]
      field_simp
    rw [hscale]
    exact mul_le_mul_of_nonneg_left (hSge.trans hS_tot) (sq_nonneg F_max)
  have hFt : F_max * (t : ℝ) ≤ 2 * (s : ℝ) := by
    have := mul_le_mul_of_nonneg_left ht_le hF.le
    have heq : F_max * (2 * ((s : ℝ) / F_max)) = 2 * (s : ℝ) := by field_simp
    linarith only [this, heq]
  have hFt_sq : F_max ^ 2 * (t : ℝ) ^ 2 ≤ 4 * (s : ℝ) ^ 2 := by
    have h1 : (F_max * (t : ℝ)) ^ 2 ≤ (2 * (s : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hFt 2
    nlinarith only [h1]
  have hBad_final : (BadPairs.card : ℝ) ≤ (1 / 10 : ℝ) * (s : ℝ) ^ 2 := by
    have h1 : F_max * (s : ℝ) ≤ (1 / 10 : ℝ) * (s : ℝ) ^ 2 := by nlinarith only [hF_small, hs_pos]
    have h2 : F_max ^ 2 * ((9 / 1000 : ℝ) * (t : ℝ) ^ 2) ≤ (36 / 1000 : ℝ) * (s : ℝ) ^ 2 := by
      nlinarith only [hFt_sq]
    linarith only [hBad_le, hdiag_bd, hoff_bd, h1, h2]
  have hcov_card : (AllPairs.card : ℝ) ≤ (RedGood.card : ℝ) + (BadPairs.card : ℝ) := by
    have hnat : AllPairs.card ≤ RedGood.card + BadPairs.card :=
      (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
    exact_mod_cast hnat
  have hs16 : (16 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_ge
  nlinarith only [hAll_card, hcov_card, hBad_final, hs16]

end DeterministicConstruction

/- ### Section 3: Typicality Bounds for `(φ_R, φ_B)` and `G(m, p)` -/

section TypicalityBounds

/-- Bad event on the pair of blow-up maps `(φ_R, φ_B)`: either some fiber exceeds `F_max`,
or some `k`-subset `I` has both `|φ_R(I)| < s` and `|φ_B(I)| < s`. -/
def BadPi (n m k s : ℕ) (F_max : ℝ) (φ_R φ_B : Fin n → Fin m) : Prop :=
  (∃ x : Fin m, F_max < ((Finset.univ.filter (fun v : Fin n => φ_R v = x)).card : ℝ)) ∨
  (∃ x : Fin m, F_max < ((Finset.univ.filter (fun v : Fin n => φ_B v = x)).card : ℝ)) ∨
  (∃ I : Finset (Fin n), I.card = k ∧ (I.image φ_R).card < s ∧ (I.image φ_B).card < s)

/-- Counting bound on `BadPi`: under clean fiber and double-compression inequalities,
strictly fewer than `1/10` of all map pairs `(φ_R, φ_B)` satisfy `BadPi`. -/
lemma card_badPi_lt {n m k s : ℕ} {F_max : ℝ} (hm : 1 ≤ m) (hk : 1 ≤ k) (hs : 2 ≤ s)
    (hs_m : s - 1 ≤ m) (h4s : 4 * (s - 1) ≤ k) (hF0 : 0 < F_max)
    (h_fib : 2 * (m : ℝ) * (Real.exp 1 * (n : ℝ) / (((Nat.floor F_max + 1 : ℕ) : ℝ) * (m : ℝ))) ^
      (Nat.floor F_max + 1) < 1 / 20)
    (h_comp : (Real.exp 4 * ((n : ℝ) / (k : ℝ)) ^ 2 *
      (((s - 1 : ℕ) : ℝ) / (m : ℝ)) ^ 3) ^ k < (1 / 20 : ℝ) ^ 2) :
    ((Finset.univ.filter (fun q : (Fin n → Fin m) × (Fin n → Fin m) =>
      BadPi n m k s F_max q.1 q.2)).card : ℝ) <
      (1 / 10 : ℝ) * ((Fintype.card ((Fin n → Fin m) × (Fin n → Fin m))) : ℝ) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  set r_f : ℕ := Nat.floor F_max + 1
  have hrf_pos : 1 ≤ r_f := Nat.succ_le_succ (Nat.zero_le _)
  set r_s : ℕ := s - 1
  have hrs_pos : 1 ≤ r_s := by omega
  set M : ℝ := (m : ℝ) ^ n
  have hM_pos : 0 < M := pow_pos hm_pos n
  have hcard_tot : (Fintype.card ((Fin n → Fin m) × (Fin n → Fin m)) : ℝ) = M ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow, M, sq]
  rw [hcard_tot]
  let E1 : Finset ((Fin n → Fin m) × (Fin n → Fin m)) := Finset.univ.filter fun q =>
    ∃ x : Fin m, F_max < ((Finset.univ.filter (fun v : Fin n => q.1 v = x)).card : ℝ)
  let E2 : Finset ((Fin n → Fin m) × (Fin n → Fin m)) := Finset.univ.filter fun q =>
    ∃ x : Fin m, F_max < ((Finset.univ.filter (fun v : Fin n => q.2 v = x)).card : ℝ)
  let E3 : Finset ((Fin n → Fin m) × (Fin n → Fin m)) := Finset.univ.filter fun q =>
    ∃ I : Finset (Fin n), I.card = k ∧ (I.image q.1).card < s ∧ (I.image q.2).card < s
  have hsub_all : Finset.univ.filter (fun q : (Fin n → Fin m) × (Fin n → Fin m) =>
      BadPi n m k s F_max q.1 q.2) ⊆ E1 ∪ E2 ∪ E3 := by
    intro q hq
    rcases (Finset.mem_filter.mp hq).2 with h1 | h2 | h3
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3⟩)
  -- Fiber bound for a single map `φ : Fin n → Fin m`.
  have hfib_single : ((Finset.univ.filter (fun φ : Fin n → Fin m =>
      ∃ x : Fin m, F_max < ((Finset.univ.filter (fun v : Fin n => φ v = x)).card : ℝ))).card : ℝ) ≤
      (m : ℝ) * (Real.exp 1 * (n : ℝ) / ((r_f : ℝ) * (m : ℝ))) ^ r_f * M := by
    let Fset := Finset.univ.filter (fun φ : Fin n → Fin m =>
      ∃ x : Fin m, F_max < ((Finset.univ.filter (fun v : Fin n => φ v = x)).card : ℝ))
    have hcov : Fset ⊆ Finset.univ.biUnion fun x : Fin m =>
        Finset.univ.filter (fun φ : Fin n → Fin m =>
          r_f ≤ (Finset.univ.filter (fun v : Fin n => φ v = x)).card) := by
      intro φ hφ
      rcases (Finset.mem_filter.mp hφ).2 with ⟨x, hx⟩
      refine Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      have h1 : Nat.floor F_max < (Finset.univ.filter (fun v : Fin n => φ v = x)).card :=
        (Nat.floor_lt hF0.le).mpr hx
      omega
    have hbi : (Fset.card : ℝ) ≤ ∑ x : Fin m,
        ((Finset.univ.filter (fun φ : Fin n → Fin m =>
          r_f ≤ (Finset.univ.filter (fun v : Fin n => φ v = x)).card)).card : ℝ) := by
      have hnat : Fset.card ≤ ∑ x : Fin m,
          (Finset.univ.filter (fun φ : Fin n → Fin m =>
            r_f ≤ (Finset.univ.filter (fun v : Fin n => φ v = x)).card)).card :=
        (Finset.card_le_card hcov).trans Finset.card_biUnion_le
      exact_mod_cast hnat
    have hterm : ∀ x : Fin m,
        ((Finset.univ.filter (fun φ : Fin n → Fin m =>
          r_f ≤ (Finset.univ.filter (fun v : Fin n => φ v = x)).card)).card : ℝ) ≤
        (Real.exp 1 * (n : ℝ) / ((r_f : ℝ) * (m : ℝ))) ^ r_f * M := by
      intro x
      have h1 := card_maps_fiber_ge_le (n := n) hm x r_f
      have h2 := choose_le_exp_pow (N := n) hrf_pos
      have h3 : (n.choose r_f : ℝ) * (1 / (m : ℝ)) ^ r_f ≤
          (Real.exp 1 * (n : ℝ) / ((r_f : ℝ) * (m : ℝ))) ^ r_f := by
        calc (n.choose r_f : ℝ) * (1 / (m : ℝ)) ^ r_f
            ≤ (Real.exp 1 * (n : ℝ) / (r_f : ℝ)) ^ r_f * (1 / (m : ℝ)) ^ r_f :=
              mul_le_mul_of_nonneg_right h2 (by positivity)
          _ = (Real.exp 1 * (n : ℝ) / ((r_f : ℝ) * (m : ℝ))) ^ r_f := by
              rw [← mul_pow]; congr 1; ring
      exact h1.trans (mul_le_mul_of_nonneg_right h3 hM_pos.le)
    calc (Fset.card : ℝ)
        ≤ ∑ _x : Fin m, ((Real.exp 1 * (n : ℝ) / ((r_f : ℝ) * (m : ℝ))) ^ r_f * M) :=
          hbi.trans (Finset.sum_le_sum fun x _ => hterm x)
      _ = (m : ℝ) * (Real.exp 1 * (n : ℝ) / ((r_f : ℝ) * (m : ℝ))) ^ r_f * M := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
  have hE1 : (E1.card : ℝ) ≤ (m : ℝ) * (Real.exp 1 * (n : ℝ) / ((r_f : ℝ) * (m : ℝ))) ^ r_f * M ^ 2 := by
    have heq : E1 = (Finset.univ.filter (fun φ : Fin n → Fin m =>
        ∃ x : Fin m, F_max < ((Finset.univ.filter (fun v : Fin n => φ v = x)).card : ℝ))) ×ˢ
        (Finset.univ : Finset (Fin n → Fin m)) := by
      ext ⟨φ1, φ2⟩; simp [E1]
    rw [heq, Finset.card_product, Finset.card_univ]
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
    calc _ ≤ ((m : ℝ) * (Real.exp 1 * (n : ℝ) / ((r_f : ℝ) * (m : ℝ))) ^ r_f * M) * M :=
          mul_le_mul_of_nonneg_right hfib_single hM_pos.le
      _ = (m : ℝ) * (Real.exp 1 * (n : ℝ) / ((r_f : ℝ) * (m : ℝ))) ^ r_f * M ^ 2 := by ring
  have hE2 : (E2.card : ℝ) ≤ (m : ℝ) * (Real.exp 1 * (n : ℝ) / ((r_f : ℝ) * (m : ℝ))) ^ r_f * M ^ 2 := by
    have hbij : E2.card = E1.card := by
      refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
      · intro q hq; simp only [E1, E2, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢; exact hq
      · intro p _ q _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro q hq; refine ⟨(q.2, q.1), ?_, rfl⟩
        simp only [E1, E2, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢; exact hq
    rw [hbij]; exact hE1
  -- Double-compression bound for `E3`.
  have hE3 : (E3.card : ℝ) < (1 / 20 : ℝ) * M ^ 2 := by
    let Triples := (Finset.univ : Finset (Fin n)).powersetCard k ×ˢ
      ((Finset.univ : Finset (Fin m)).powersetCard r_s ×ˢ (Finset.univ : Finset (Fin m)).powersetCard r_s)
    have hcov3 : E3 ⊆ Triples.biUnion fun tr =>
        (Finset.univ.filter (fun φ : Fin n → Fin m => ∀ v ∈ tr.1, φ v ∈ tr.2.1)) ×ˢ
        (Finset.univ.filter (fun φ : Fin n → Fin m => ∀ v ∈ tr.1, φ v ∈ tr.2.2)) := by
      intro ⟨φ1, φ2⟩ hq
      rcases (Finset.mem_filter.mp hq).2 with ⟨I, hIk, hI1, hI2⟩
      dsimp only at hI1 hI2
      have h1le : (I.image φ1).card ≤ r_s := by omega
      have h2le : (I.image φ2).card ≤ r_s := by omega
      have hrs_m : r_s ≤ m := hs_m
      have h1diff : r_s - (I.image φ1).card ≤ (Finset.univ \ I.image φ1).card := by
        have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (I.image φ1))
        simp only [Finset.card_univ, Fintype.card_fin] at h; omega
      have h2diff : r_s - (I.image φ2).card ≤ (Finset.univ \ I.image φ2).card := by
        have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (I.image φ2))
        simp only [Finset.card_univ, Fintype.card_fin] at h; omega
      obtain ⟨D1, hD1sub, hD1c⟩ := Finset.exists_subset_card_eq h1diff
      obtain ⟨D2, hD2sub, hD2c⟩ := Finset.exists_subset_card_eq h2diff
      let A := I.image φ1 ∪ D1
      let B := I.image φ2 ∪ D2
      have hdisj1 : Disjoint (I.image φ1) D1 := Finset.disjoint_left.mpr fun x hx1 hx2 =>
        (Finset.mem_sdiff.mp (hD1sub hx2)).2 hx1
      have hdisj2 : Disjoint (I.image φ2) D2 := Finset.disjoint_left.mpr fun x hx1 hx2 =>
        (Finset.mem_sdiff.mp (hD2sub hx2)).2 hx1
      have hAc : A.card = r_s := by rw [Finset.card_union_of_disjoint hdisj1, hD1c]; omega
      have hBc : B.card = r_s := by rw [Finset.card_union_of_disjoint hdisj2, hD2c]; omega
      refine Finset.mem_biUnion.mpr ⟨(I, (A, B)), ?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hIk⟩,
          Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hAc⟩,
            Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hBc⟩⟩⟩
      · exact Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v hv => Finset.mem_union_left _ (Finset.mem_image_of_mem φ1 hv)⟩,
           Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v hv => Finset.mem_union_left _ (Finset.mem_image_of_mem φ2 hv)⟩⟩
    have hbi3 : (E3.card : ℝ) ≤ ∑ tr ∈ Triples,
        (((Finset.univ.filter (fun φ : Fin n → Fin m => ∀ v ∈ tr.1, φ v ∈ tr.2.1)) ×ˢ
          (Finset.univ.filter (fun φ : Fin n → Fin m => ∀ v ∈ tr.1, φ v ∈ tr.2.2))).card : ℝ) := by
      have hnat : E3.card ≤ ∑ tr ∈ Triples,
          ((Finset.univ.filter (fun φ : Fin n → Fin m => ∀ v ∈ tr.1, φ v ∈ tr.2.1)) ×ˢ
           (Finset.univ.filter (fun φ : Fin n → Fin m => ∀ v ∈ tr.1, φ v ∈ tr.2.2))).card :=
        (Finset.card_le_card hcov3).trans Finset.card_biUnion_le
      exact_mod_cast hnat
    have htr_eq : ∀ tr ∈ Triples,
        (((Finset.univ.filter (fun φ : Fin n → Fin m => ∀ v ∈ tr.1, φ v ∈ tr.2.1)) ×ˢ
          (Finset.univ.filter (fun φ : Fin n → Fin m => ∀ v ∈ tr.1, φ v ∈ tr.2.2))).card : ℝ) =
        ((r_s : ℝ) / (m : ℝ)) ^ (2 * k) * M ^ 2 := by
      intro tr htr
      have h1 : tr.1.card = k := (Finset.mem_powersetCard.mp (Finset.mem_product.mp htr).1).2
      have h2 : tr.2.1.card = r_s := (Finset.mem_powersetCard.mp (Finset.mem_product.mp (Finset.mem_product.mp htr).2).1).2
      have h3 : tr.2.2.card = r_s := (Finset.mem_powersetCard.mp (Finset.mem_product.mp (Finset.mem_product.mp htr).2).2).2
      rw [Finset.card_product, Nat.cast_mul, card_maps_image_subset hm tr.1 tr.2.1,
        card_maps_image_subset hm tr.1 tr.2.2, h1, h2, h3]
      rw [two_mul, pow_add]; ring
    have hTriples_card : (Triples.card : ℝ) = (n.choose k : ℝ) * (m.choose r_s : ℝ) ^ 2 := by
      simp only [Triples, Finset.card_product, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin, Nat.cast_mul, sq]
    have hsum3 : (E3.card : ℝ) ≤ (n.choose k : ℝ) * (m.choose r_s : ℝ) ^ 2 *
        ((r_s : ℝ) / (m : ℝ)) ^ (2 * k) * M ^ 2 := by
      calc (E3.card : ℝ)
          ≤ ∑ _tr ∈ Triples, (((r_s : ℝ) / (m : ℝ)) ^ (2 * k) * M ^ 2) :=
            hbi3.trans (le_of_eq (Finset.sum_congr rfl htr_eq))
        _ = (Triples.card : ℝ) * (((r_s : ℝ) / (m : ℝ)) ^ (2 * k) * M ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = _ := by rw [hTriples_card]; ring
    -- Bound the combinatorial coefficient `C3 := (n.choose k) * (m.choose r_s)^2 * (r_s / m)^(2*k)` via `C3^2 < (1/20)^2`.
    set C3 : ℝ := (n.choose k : ℝ) * (m.choose r_s : ℝ) ^ 2 * ((r_s : ℝ) / (m : ℝ)) ^ (2 * k)
    have hC3_le : C3 ≤ (Real.exp 2 * ((n : ℝ) / (k : ℝ))) ^ k * ((r_s : ℝ) / (m : ℝ)) ^ (2 * k - 2 * r_s) := by
      have hck := choose_le_exp_pow (N := n) hk
      have hcm := choose_le_exp_pow (N := m) hrs_pos
      have hcm2 : (m.choose r_s : ℝ) ^ 2 ≤ (Real.exp 1 * (m : ℝ) / (r_s : ℝ)) ^ (2 * r_s) := by
        rw [two_mul, pow_add, ← sq]
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) hcm 2
      have hrs_posR : (0 : ℝ) < (r_s : ℝ) := Nat.cast_pos.mpr (by omega)
      have hcancel : (Real.exp 1 * (m : ℝ) / (r_s : ℝ)) ^ (2 * r_s) * ((r_s : ℝ) / (m : ℝ)) ^ (2 * k) =
          (Real.exp 1) ^ (2 * r_s) * ((r_s : ℝ) / (m : ℝ)) ^ (2 * k - 2 * r_s) := by
        have hsplit : ((r_s : ℝ) / (m : ℝ)) ^ (2 * k) =
            ((r_s : ℝ) / (m : ℝ)) ^ (2 * r_s) * ((r_s : ℝ) / (m : ℝ)) ^ (2 * k - 2 * r_s) := by
          rw [← pow_add, Nat.add_sub_of_le (by omega : 2 * r_s ≤ 2 * k)]
        rw [hsplit, ← mul_assoc, ← mul_pow]
        congr 2; field_simp
      have he2rs : (Real.exp 1) ^ (2 * r_s) ≤ (Real.exp 1) ^ k :=
        pow_le_pow_right₀ (by linarith only [Real.add_one_le_exp (1 : ℝ)]) (by omega : 2 * r_s ≤ k)
      have he2 : (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k * (Real.exp 1) ^ k =
          (Real.exp 2 * ((n : ℝ) / (k : ℝ))) ^ k := by
        rw [← mul_pow]; congr 1
        have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        rw [this]; ring
      calc C3 ≤ (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k *
              ((Real.exp 1 * (m : ℝ) / (r_s : ℝ)) ^ (2 * r_s) * ((r_s : ℝ) / (m : ℝ)) ^ (2 * k)) := by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul hck hcm2 (by positivity) (by positivity)) (by positivity)
        _ = (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k *
              ((Real.exp 1) ^ (2 * r_s) * ((r_s : ℝ) / (m : ℝ)) ^ (2 * k - 2 * r_s)) := by rw [hcancel]
        _ ≤ (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k *
              ((Real.exp 1) ^ k * ((r_s : ℝ) / (m : ℝ)) ^ (2 * k - 2 * r_s)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he2rs (by positivity)) (by positivity)
        _ = (Real.exp 2 * ((n : ℝ) / (k : ℝ))) ^ k * ((r_s : ℝ) / (m : ℝ)) ^ (2 * k - 2 * r_s) := by
            rw [← mul_assoc, he2]
    have hC3_sq : C3 ^ 2 < (1 / 20 : ℝ) ^ 2 := by
      have h1 : C3 ^ 2 ≤ ((Real.exp 2 * ((n : ℝ) / (k : ℝ))) ^ k *
          ((r_s : ℝ) / (m : ℝ)) ^ (2 * k - 2 * r_s)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hC3_le 2
      have hrm_le : (r_s : ℝ) / (m : ℝ) ≤ 1 := (div_le_one hm_pos).mpr (by exact_mod_cast hs_m)
      have hpow_le : (((r_s : ℝ) / (m : ℝ)) ^ (2 * k - 2 * r_s)) ^ 2 ≤
          (((r_s : ℝ) / (m : ℝ)) ^ 3) ^ k := by
        rw [← pow_mul, ← pow_mul]
        exact pow_le_pow_of_le_one (by positivity) hrm_le (by omega : 3 * k ≤ (2 * k - 2 * r_s) * 2)
      have hexp4 : (Real.exp 2) ^ 2 = Real.exp 4 := by rw [sq, ← Real.exp_add]; norm_num
      have h2 : ((Real.exp 2 * ((n : ℝ) / (k : ℝ))) ^ k *
          ((r_s : ℝ) / (m : ℝ)) ^ (2 * k - 2 * r_s)) ^ 2 ≤
          (Real.exp 4 * ((n : ℝ) / (k : ℝ)) ^ 2 * ((r_s : ℝ) / (m : ℝ)) ^ 3) ^ k := by
        rw [mul_pow]
        calc ((Real.exp 2 * ((n : ℝ) / (k : ℝ))) ^ k) ^ 2 * (((r_s : ℝ) / (m : ℝ)) ^ (2 * k - 2 * r_s)) ^ 2
            ≤ ((Real.exp 2 * ((n : ℝ) / (k : ℝ))) ^ k) ^ 2 * (((r_s : ℝ) / (m : ℝ)) ^ 3) ^ k :=
              mul_le_mul_of_nonneg_left hpow_le (by positivity)
          _ = (Real.exp 4 * ((n : ℝ) / (k : ℝ)) ^ 2 * ((r_s : ℝ) / (m : ℝ)) ^ 3) ^ k := by
              rw [← pow_mul, mul_comm k 2, pow_mul, mul_pow, hexp4, ← mul_pow]
      exact (h1.trans h2).trans_lt h_comp
    have hC3_lt : C3 < 1 / 20 := by nlinarith only [hC3_sq, show 0 ≤ C3 by positivity]
    exact hsum3.trans_lt (mul_lt_mul_of_pos_right hC3_lt (pow_pos hM_pos 2))
  have hu : ((Finset.univ.filter (fun q : (Fin n → Fin m) × (Fin n → Fin m) =>
      BadPi n m k s F_max q.1 q.2)).card : ℝ) ≤ (E1.card : ℝ) + (E2.card : ℝ) + (E3.card : ℝ) := by
    have hnat : (Finset.univ.filter (fun q : (Fin n → Fin m) × (Fin n → Fin m) =>
        BadPi n m k s F_max q.1 q.2)).card ≤ E1.card + E2.card + E3.card := by
      calc _ ≤ (E1 ∪ E2 ∪ E3).card := Finset.card_le_card hsub_all
        _ ≤ (E1 ∪ E2).card + E3.card := Finset.card_union_le _ _
        _ ≤ E1.card + E2.card + E3.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    exact_mod_cast hnat
  have h12 : (E1.card : ℝ) + (E2.card : ℝ) < (1 / 20 : ℝ) * M ^ 2 := by
    have hsum12 : (E1.card : ℝ) + (E2.card : ℝ) ≤
        (2 * (m : ℝ) * (Real.exp 1 * (n : ℝ) / ((r_f : ℝ) * (m : ℝ))) ^ r_f) * M ^ 2 := by
      linarith only [hE1, hE2]
    exact hsum12.trans_lt (mul_lt_mul_of_pos_right h_fib (pow_pos hM_pos 2))
  linarith only [hu, h12, hE3]

/-- Helper equivalence splitting `EdgeIdx m` into edges between `Finset.univ \ A` and `A`
(grouped by `z ∉ A`) plus all remaining edges. -/
def edgeSplitOut {m : ℕ} (A : Finset (Fin m)) :
    EdgeIdx m ≃
      (Σ _ : {z : Fin m // z ∉ A}, {a : Fin m // a ∈ A}) ⊕
      {e : EdgeIdx m // ¬ ((e.1.1 ∉ A ∧ e.1.2 ∈ A) ∨ (e.1.2 ∉ A ∧ e.1.1 ∈ A))} where
  toFun e :=
    if h1 : e.1.1 ∉ A ∧ e.1.2 ∈ A then Sum.inl ⟨⟨e.1.1, h1.1⟩, ⟨e.1.2, h1.2⟩⟩
    else if h2 : e.1.2 ∉ A ∧ e.1.1 ∈ A then Sum.inl ⟨⟨e.1.2, h2.1⟩, ⟨e.1.1, h2.2⟩⟩
    else Sum.inr ⟨e, fun h => h.elim h1 h2⟩
  invFun s :=
    match s with
    | Sum.inl ⟨⟨z, hz⟩, ⟨a, ha⟩⟩ =>
        if hlt : z < a then ⟨(z, a), hlt⟩
        else ⟨(a, z), lt_of_le_of_ne (not_lt.mp hlt) (fun heq : a = z => hz (heq ▸ ha))⟩
    | Sum.inr ⟨e, _⟩ => e
  left_inv e := by
    dsimp only
    split_ifs with h1 h2
    · simp [e.2]
    · have hnot : ¬ e.1.2 < e.1.1 := lt_asymm e.2
      simp [hnot]
    · rfl
  right_inv s := by
    rcases s with ⟨⟨z, hz⟩, ⟨a, ha⟩⟩ | ⟨e, he⟩
    · dsimp only
      by_cases hlt : z < a
      · simp [hlt, hz, ha]
      · simp [hlt, hz, ha]
    · dsimp only
      have h1 : ¬ (e.1.1 ∉ A ∧ e.1.2 ∈ A) := fun h => he (Or.inl h)
      have h2 : ¬ (e.1.2 ∉ A ∧ e.1.1 ∈ A) := fun h => he (Or.inr h)
      simp [h1, h2]

/-- Under `edgeSplitOut A`, the degree of `z ∉ A` into `A` in `graphOf (ω ∘ edgeSplitOut A)`
is exactly the number of true coordinates in block `z`. -/
lemma degIn_edgeSplitOut {m : ℕ} (A : Finset (Fin m))
    (ω : ((Σ _ : {z : Fin m // z ∉ A}, {a : Fin m // a ∈ A}) ⊕
          {e : EdgeIdx m // ¬ ((e.1.1 ∉ A ∧ e.1.2 ∈ A) ∨ (e.1.2 ∉ A ∧ e.1.1 ∈ A))}) → Bool)
    (z : {z : Fin m // z ∉ A}) :
    degIn (graphOf (ω ∘ edgeSplitOut A)) A z.1 =
      (Finset.univ.filter (fun a : {a : Fin m // a ∈ A} => ω (Sum.inl ⟨z, a⟩) = true)).card := by
  unfold degIn
  refine Finset.card_bij (fun x hx => ⟨x, (Finset.mem_filter.mp hx).1⟩) ?_ ?_ ?_
  · intro x hx
    have hxA : x ∈ A := (Finset.mem_filter.mp hx).1
    have hadj : (graphOf (ω ∘ edgeSplitOut A)).Adj z.1 x := (Finset.mem_filter.mp hx).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simp only [graphOf, Function.comp] at hadj
    by_cases hlt : z.1 < x
    · rw [dif_pos hlt] at hadj
      have he : edgeSplitOut A ⟨(z.1, x), hlt⟩ = Sum.inl ⟨z, ⟨x, hxA⟩⟩ := by
        simp [edgeSplitOut, z.2, hxA]
      rwa [he] at hadj
    · have hgt : x < z.1 := lt_of_le_of_ne (not_lt.mp hlt) (fun h => z.2 (h ▸ hxA))
      rw [dif_neg hlt, dif_pos hgt] at hadj
      have he : edgeSplitOut A ⟨(x, z.1), hgt⟩ = Sum.inl ⟨z, ⟨x, hxA⟩⟩ := by
        simp [edgeSplitOut, z.2, hxA]
      rwa [he] at hadj
  · intro x _ y _ h; exact congrArg Subtype.val h
  · intro a ha
    have htrue : ω (Sum.inl ⟨z, a⟩) = true := (Finset.mem_filter.mp ha).2
    refine ⟨a.1, Finset.mem_filter.mpr ⟨a.2, ?_⟩, Subtype.ext rfl⟩
    simp only [graphOf, Function.comp]
    by_cases hlt : z.1 < a.1
    · rw [dif_pos hlt]
      have he : edgeSplitOut A ⟨(z.1, a.1), hlt⟩ = Sum.inl ⟨z, a⟩ := by
        simp [edgeSplitOut, z.2, a.2]
      rw [he]; exact htrue
    · have hgt : a.1 < z.1 := lt_of_le_of_ne (not_lt.mp hlt) (fun h => z.2 (h ▸ a.2))
      rw [dif_neg hlt, dif_pos hgt]
      have he : edgeSplitOut A ⟨(a.1, z.1), hgt⟩ = Sum.inl ⟨z, a⟩ := by
        simp [edgeSplitOut, z.2, a.2]
      rw [he]; exact htrue

/-- Max-degree tail bound in `G(m, p)`:
`P(∃ x, 2 m p < deg x) ≤ m * exp(-((m - 1) p) / 6)`. -/
lemma bernProb_maxDeg_le {m : ℕ} (_hm : 1 ≤ m) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bernProb p (fun ω : EdgeIdx m → Bool =>
      ∃ x : Fin m, 2 * ((m : ℝ) * p) < (degIn (graphOf ω) Finset.univ x : ℝ)) ≤
      (m : ℝ) * Real.exp (-(((m - 1 : ℕ) : ℝ) * p) / 6) := by
  have h1 : bernProb p (fun ω : EdgeIdx m → Bool =>
      ∃ x : Fin m, 2 * ((m : ℝ) * p) < (degIn (graphOf ω) Finset.univ x : ℝ)) ≤
      ∑ x : Fin m, bernProb p (fun ω : EdgeIdx m → Bool =>
        2 * ((m : ℝ) * p) < (degIn (graphOf ω) Finset.univ x : ℝ)) := by
    have heq : (fun ω : EdgeIdx m → Bool =>
        ∃ x : Fin m, 2 * ((m : ℝ) * p) < (degIn (graphOf ω) Finset.univ x : ℝ)) =
        (fun ω : EdgeIdx m → Bool =>
        ∃ x ∈ (Finset.univ : Finset (Fin m)), 2 * ((m : ℝ) * p) < (degIn (graphOf ω) Finset.univ x : ℝ)) := by
      funext ω; simp
    rw [heq]; exact bernProb_exists_le hp0 hp1 Finset.univ _
  have hper : ∀ x : Fin m,
      bernProb p (fun ω : EdgeIdx m → Bool =>
        2 * ((m : ℝ) * p) < (degIn (graphOf ω) Finset.univ x : ℝ)) ≤
      Real.exp (-(((m - 1 : ℕ) : ℝ) * p) / 6) := by
    intro x
    let Sx : Finset (EdgeIdx m) := Finset.univ.filter (fun e => e.1.1 = x ∨ e.1.2 = x)
    have hSx_card : Sx.card = m - 1 := by
      have hbij : Sx.card = (Finset.univ.erase x).card := by
        refine Finset.card_bij (fun e _ => if e.1.1 = x then e.1.2 else e.1.1) ?_ ?_ ?_
        · intro e he
          rcases (Finset.mem_filter.mp he).2 with h1 | h2
          · rw [if_pos h1]; exact Finset.mem_erase.mpr ⟨by rw [← h1]; exact e.2.ne', Finset.mem_univ _⟩
          · have hne : e.1.1 ≠ x := by rw [← h2]; exact e.2.ne
            rw [if_neg hne]; exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
        · intro e₁ he₁ e₂ he₂ heq
          rcases (Finset.mem_filter.mp he₁).2 with h1a | h1b <;>
          rcases (Finset.mem_filter.mp he₂).2 with h2a | h2b
          · simp only [if_pos h1a, if_pos h2a] at heq
            exact Subtype.ext (Prod.ext (h1a.trans h2a.symm) heq)
          · have hne2 : e₂.1.1 ≠ x := by rw [← h2b]; exact e₂.2.ne
            simp only [if_pos h1a, if_neg hne2] at heq
            have hlt1 : x < e₁.1.2 := h1a ▸ e₁.2
            have hlt2 : e₁.1.2 < x := heq ▸ h2b ▸ e₂.2
            exact absurd (lt_trans hlt1 hlt2) (lt_irrefl x)
          · have hne1 : e₁.1.1 ≠ x := by rw [← h1b]; exact e₁.2.ne
            simp only [if_neg hne1, if_pos h2a] at heq
            have hlt1 : x < e₂.1.2 := h2a ▸ e₂.2
            have hlt2 : e₂.1.2 < x := heq.symm ▸ h1b ▸ e₁.2
            exact absurd (lt_trans hlt1 hlt2) (lt_irrefl x)
          · have hne1 : e₁.1.1 ≠ x := by rw [← h1b]; exact e₁.2.ne
            have hne2 : e₂.1.1 ≠ x := by rw [← h2b]; exact e₂.2.ne
            simp only [if_neg hne1, if_neg hne2] at heq
            exact Subtype.ext (Prod.ext heq (h1b.trans h2b.symm))
        · intro y hy
          have hne : y ≠ x := (Finset.mem_erase.mp hy).1
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · refine ⟨⟨(y, x), hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr rfl⟩, by simp [hne]⟩
          · refine ⟨⟨(x, y), hgt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩, by simp⟩
      rw [hbij, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, Fintype.card_fin]
    have hdeg_eq : ∀ ω : EdgeIdx m → Bool,
        degIn (graphOf ω) Finset.univ x = (Sx.filter (fun e => ω e = true)).card := by
      intro ω
      unfold degIn
      refine Finset.card_bij (fun y hy =>
        if hlt : x < y then ⟨(x, y), hlt⟩
        else ⟨(y, x), lt_of_le_of_ne (not_lt.mp hlt) (fun h : y = x => by
          have hadj := (Finset.mem_filter.mp hy).2
          subst h; exact (graphOf ω).loopless.irrefl y hadj)⟩) ?_ ?_ ?_
      · intro y hy
        have hadj := (Finset.mem_filter.mp hy).2
        simp only [graphOf] at hadj
        by_cases hlt : x < y
        · rw [dif_pos hlt] at hadj
          simp [dif_pos hlt, Sx, hadj]
        · have hne : y ≠ x := fun h => by subst h; simp at hadj
          have hgt : y < x := lt_of_le_of_ne (not_lt.mp hlt) hne
          rw [dif_neg hlt, dif_pos hgt] at hadj
          simp [dif_neg hlt, Sx, hadj]
      · intro y₁ hy₁ y₂ hy₂ heq
        have h1 : y₁ ≠ x := fun h => by subst h; exact (graphOf ω).loopless.irrefl y₁ (Finset.mem_filter.mp hy₁).2
        have h2 : y₂ ≠ x := fun h => by subst h; exact (graphOf ω).loopless.irrefl y₂ (Finset.mem_filter.mp hy₂).2
        by_cases hlt1 : x < y₁ <;> by_cases hlt2 : x < y₂
        · simp only [dif_pos hlt1, dif_pos hlt2] at heq
          exact congrArg (fun e : EdgeIdx m => e.1.2) heq
        · simp only [dif_pos hlt1, dif_neg hlt2] at heq
          have h : x = y₂ := congrArg (fun e : EdgeIdx m => e.1.1) heq
          exact absurd h.symm h2
        · simp only [dif_neg hlt1, dif_pos hlt2] at heq
          have h : y₁ = x := congrArg (fun e : EdgeIdx m => e.1.1) heq
          exact absurd h h1
        · simp only [dif_neg hlt1, dif_neg hlt2] at heq
          exact congrArg (fun e : EdgeIdx m => e.1.1) heq
      · intro e he
        rcases (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2 with h1 | h2
        · have htrue := (Finset.mem_filter.mp he).2
          have hlt : x < e.1.2 := h1 ▸ e.2
          refine ⟨e.1.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · simp only [graphOf, dif_pos hlt]
            have : (⟨(x, e.1.2), hlt⟩ : EdgeIdx m) = e := Subtype.ext (Prod.ext h1.symm rfl)
            rwa [this]
          · simp only [dif_pos hlt]; exact Subtype.ext (Prod.ext h1.symm rfl)
        · have htrue := (Finset.mem_filter.mp he).2
          have hgt : e.1.1 < x := h2 ▸ e.2
          have hnot : ¬ x < e.1.1 := lt_asymm hgt
          refine ⟨e.1.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · simp only [graphOf, dif_neg hnot, dif_pos hgt]
            have : (⟨(e.1.1, x), hgt⟩ : EdgeIdx m) = e := Subtype.ext (Prod.ext rfl h2.symm)
            rwa [this]
          · simp only [dif_neg hnot]; exact Subtype.ext (Prod.ext rfl h2.symm)
    have hmono : bernProb p (fun ω : EdgeIdx m → Bool =>
        2 * ((m : ℝ) * p) < (degIn (graphOf ω) Finset.univ x : ℝ)) ≤
        bernProb p (fun ω : EdgeIdx m → Bool =>
        2 * ((Sx.card : ℝ) * p) ≤ ((Sx.filter (fun e => ω e = true)).card : ℝ)) := by
      refine bernProb_mono hp0 hp1 fun ω hω => ?_
      rw [hdeg_eq ω] at hω
      have hle : (Sx.card : ℝ) ≤ (m : ℝ) := by rw [hSx_card]; exact_mod_cast Nat.sub_le m 1
      have hmul : 2 * ((Sx.card : ℝ) * p) ≤ 2 * ((m : ℝ) * p) := by nlinarith only [hle, hp0]
      exact hmul.trans hω.le
    have hch := bernProb_binom_ge_two_mul hp0 hp1 Sx
    rw [hSx_card] at hmono hch
    exact hmono.trans hch
  calc _ ≤ ∑ _x : Fin m, Real.exp (-(((m - 1 : ℕ) : ℝ) * p) / 6) :=
        h1.trans (Finset.sum_le_sum fun x _ => hper x)
    _ = (m : ℝ) * Real.exp (-(((m - 1 : ℕ) : ℝ) * p) / 6) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Piece 1 (truncated small-degree squares): for fixed `A : Finset (Fin m)` and `L₁ > 0`,
`P(T₁ ≤ ∑_{z ∉ A, X_z ≤ L₁} X_z^2) ≤ exp((2 m (|A| p + (|A| p)^2) - T₁) / L₁^2)`. -/
lemma bernProb_degOut_sq_small {m : ℕ} {p L₁ T₁ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hL₁ : 0 < L₁)
    (A : Finset (Fin m)) :
    bernProb p (fun ω : EdgeIdx m → Bool =>
      T₁ ≤ ∑ z ∈ Finset.univ \ A,
        if (degIn (graphOf ω) A z : ℝ) ≤ L₁ then (degIn (graphOf ω) A z : ℝ) ^ 2 else 0) ≤
      Real.exp ((2 * (m : ℝ) * ((A.card : ℝ) * p + ((A.card : ℝ) * p) ^ 2) - T₁) / L₁ ^ 2) := by
  let e := (edgeSplitOut A).symm
  rw [bernProb_equiv e p]
  have hsymm : e.symm = edgeSplitOut A := Equiv.symm_symm (edgeSplitOut A)
  simp_rw [hsymm]
  let Y : ∀ z : {z : Fin m // z ∉ A}, ({a : Fin m // a ∈ A} → Bool) → ℝ := fun _ ωz =>
    let cnt : ℝ := ((Finset.univ.filter (fun a : {a : Fin m // a ∈ A} => ωz a = true)).card : ℝ)
    if cnt ≤ L₁ then cnt ^ 2 else 0
  have hrew : ∀ ω : ((Σ z : {z : Fin m // z ∉ A}, {a : Fin m // a ∈ A}) ⊕
      {e : EdgeIdx m // ¬ ((e.1.1 ∉ A ∧ e.1.2 ∈ A) ∨ (e.1.2 ∉ A ∧ e.1.1 ∈ A))}) → Bool,
      (∑ z ∈ Finset.univ \ A,
        if (degIn (graphOf (ω ∘ edgeSplitOut A)) A z : ℝ) ≤ L₁
        then (degIn (graphOf (ω ∘ edgeSplitOut A)) A z : ℝ) ^ 2 else 0) =
      ∑ z : {z : Fin m // z ∉ A}, Y z (fun a => ω (Sum.inl ⟨z, a⟩)) := by
    intro ω
    have h1 : ∑ z ∈ Finset.univ \ A,
        (if (degIn (graphOf (ω ∘ edgeSplitOut A)) A z : ℝ) ≤ L₁
          then (degIn (graphOf (ω ∘ edgeSplitOut A)) A z : ℝ) ^ 2 else 0) =
        ∑ z : {z : Fin m // z ∉ A},
          if (degIn (graphOf (ω ∘ edgeSplitOut A)) A z.1 : ℝ) ≤ L₁
          then (degIn (graphOf (ω ∘ edgeSplitOut A)) A z.1 : ℝ) ^ 2 else 0 := by
      refine Finset.sum_bij (fun z hz => ⟨z, (Finset.mem_sdiff.mp hz).2⟩) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro _ _ _ _ h; exact congrArg Subtype.val h
      · intro z _; exact ⟨z.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, z.2⟩, Subtype.ext rfl⟩
      · intro _ _; rfl
    rw [h1]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [Y, degIn_edgeSplitOut A ω z]
  simp_rw [hrew]
  refine (bernProb_inl p (fun ωL : (Σ _ : {z : Fin m // z ∉ A}, {a : Fin m // a ∈ A}) → Bool =>
    T₁ ≤ ∑ z : {z : Fin m // z ∉ A}, Y z (fun a => ωL ⟨z, a⟩))).trans_le ?_
  have hY0 : ∀ z ωz, 0 ≤ Y z ωz := fun z ωz => by
    simp only [Y]; split_ifs <;> positivity
  have hYM : ∀ z ωz, Y z ωz ≤ L₁ ^ 2 := fun z ωz => by
    simp only [Y]; split_ifs with hle
    · exact pow_le_pow_left₀ (Nat.cast_nonneg _) hle 2
    · positivity
  have hbd := bernProb_sum_bounded_le hp0 hp1 (sq_pos_of_pos hL₁) Y hY0 hYM (A := T₁)
  have hExp_le : ∑ z : {z : Fin m // z ∉ A}, bernExp p (Y z) ≤
      (m : ℝ) * ((A.card : ℝ) * p + ((A.card : ℝ) * p) ^ 2) := by
    have hper : ∀ z : {z : Fin m // z ∉ A},
        bernExp p (Y z) ≤ (A.card : ℝ) * p + ((A.card : ℝ) * p) ^ 2 := by
      intro z
      have hle_sq : bernExp p (Y z) ≤
          bernExp p (fun ωz : {a : Fin m // a ∈ A} → Bool =>
            ((Finset.univ.filter (fun a : {a : Fin m // a ∈ A} => ωz a = true)).card : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun ωz _ => mul_le_mul_of_nonneg_left ?_ (bernW_nonneg hp0 hp1 ωz)
        simp only [Y]; split_ifs
        · exact le_rfl
        · positivity
      have hsq := bernExp_indicator_sum_sq_le hp0 hp1 (Finset.univ : Finset {a : Fin m // a ∈ A})
      have hcardA : ((Finset.univ : Finset {a : Fin m // a ∈ A}).card : ℝ) = (A.card : ℝ) := by simp
      rw [hcardA] at hsq
      exact hle_sq.trans hsq
    have hcard_le : (Fintype.card {z : Fin m // z ∉ A} : ℝ) ≤ (m : ℝ) := by
      have h1 : Fintype.card {z : Fin m // z ∉ A} ≤ Fintype.card (Fin m) :=
        Fintype.card_subtype_le _
      rw [Fintype.card_fin] at h1
      exact_mod_cast h1
    calc ∑ z : {z : Fin m // z ∉ A}, bernExp p (Y z)
        ≤ ∑ _z : {z : Fin m // z ∉ A}, ((A.card : ℝ) * p + ((A.card : ℝ) * p) ^ 2) :=
          Finset.sum_le_sum fun z _ => hper z
      _ = (Fintype.card {z : Fin m // z ∉ A} : ℝ) * ((A.card : ℝ) * p + ((A.card : ℝ) * p) ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (m : ℝ) * ((A.card : ℝ) * p + ((A.card : ℝ) * p) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard_le (by positivity)
  refine hbd.trans (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right ?_ (sq_nonneg L₁)))
  linarith only [hExp_le]

/-- Piece 2 (middle dyadic range `L₁ < X_z < L₂`): for fixed `A`, `r₀ := Nat.floor L₁ + 1`,
and `J ≥ 1` with `L₂ ≤ r₀ * 2^J`, we bound the sum of squares in `(L₁, L₂)` by dyadic buckets. -/
lemma bernProb_degOut_sq_mid {m J : ℕ} {p L₁ L₂ T₂ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hL₁ : 0 < L₁) (hJ : 1 ≤ J) (hT₂ : 0 < T₂)
    (hcover : L₂ ≤ ((Nat.floor L₁ + 1 : ℕ) : ℝ) * (2 : ℝ) ^ J)
    (A : Finset (Fin m)) :
    let r₀ : ℕ := Nat.floor L₁ + 1
    bernProb p (fun ω : EdgeIdx m → Bool =>
      T₂ ≤ ∑ z ∈ Finset.univ \ A,
        if L₁ < (degIn (graphOf ω) A z : ℝ) ∧ (degIn (graphOf ω) A z : ℝ) < L₂
        then (degIn (graphOf ω) A z : ℝ) ^ 2 else 0) ≤
      ∑ j ∈ Finset.range J,
        if ((r₀ * 2 ^ j : ℕ) : ℝ) < L₂ then
          let rj : ℕ := r₀ * 2 ^ j
          let bj : ℕ := Nat.ceil (T₂ / (4 * (J : ℝ) * (rj : ℝ) ^ 2))
          ((m : ℝ) * (Real.exp 1 * (A.card : ℝ) * p / (rj : ℝ)) ^ rj) ^ bj
        else 0 := by
  intro r₀
  have hr₀_pos : 1 ≤ r₀ := Nat.succ_le_succ (Nat.zero_le _)
  have hJ_pos : (0 : ℝ) < (J : ℝ) := Nat.cast_pos.mpr (by omega)
  let r : ℕ → ℕ := fun j => r₀ * 2 ^ j
  let b : ℕ → ℕ := fun j => Nat.ceil (T₂ / (4 * (J : ℝ) * ((r j : ℕ) : ℝ) ^ 2))
  let ActiveJ : Finset ℕ := (Finset.range J).filter (fun j => ((r j : ℕ) : ℝ) < L₂)
  -- Deterministic implication: if the middle sum is `≥ T₂`, some active dyadic bucket `j` has `≥ b j` vertices.
  have himp : ∀ ω : EdgeIdx m → Bool,
      T₂ ≤ ∑ z ∈ Finset.univ \ A,
        (if L₁ < (degIn (graphOf ω) A z : ℝ) ∧ (degIn (graphOf ω) A z : ℝ) < L₂
          then (degIn (graphOf ω) A z : ℝ) ^ 2 else 0) →
      ∃ j ∈ ActiveJ, b j ≤ ((Finset.univ \ A).filter (fun z => r j ≤ degIn (graphOf ω) A z)).card := by
    intro ω hω
    by_contra hall
    push Not at hall
    have hlt_j : ∀ j ∈ ActiveJ,
        ((Finset.univ \ A).filter (fun z => r j ≤ degIn (graphOf ω) A z)).card * (4 * ((r j : ℕ) : ℝ) ^ 2) <
        T₂ / (J : ℝ) := by
      intro j hj
      have hcard_lt : (((Finset.univ \ A).filter (fun z => r j ≤ degIn (graphOf ω) A z)).card : ℝ) <
          T₂ / (4 * (J : ℝ) * ((r j : ℕ) : ℝ) ^ 2) := by
        have hnat : ((Finset.univ \ A).filter (fun z => r j ≤ degIn (graphOf ω) A z)).card < b j := hall j hj
        exact Nat.lt_ceil.mp hnat
      have hrj_pos : (0 : ℝ) < ((r j : ℕ) : ℝ) := Nat.cast_pos.mpr (by positivity)
      have h1 : (((Finset.univ \ A).filter (fun z => r j ≤ degIn (graphOf ω) A z)).card : ℝ) *
          (4 * (J : ℝ) * ((r j : ℕ) : ℝ) ^ 2) < T₂ :=
        (lt_div_iff₀ (by positivity)).mp hcard_lt
      rw [lt_div_iff₀ hJ_pos]
      linarith only [h1]
    have hpw : ∀ z ∈ Finset.univ \ A,
        (if L₁ < (degIn (graphOf ω) A z : ℝ) ∧ (degIn (graphOf ω) A z : ℝ) < L₂
          then (degIn (graphOf ω) A z : ℝ) ^ 2 else 0) ≤
        ∑ j ∈ ActiveJ,
          if r j ≤ degIn (graphOf ω) A z then 4 * ((r j : ℕ) : ℝ) ^ 2 else 0 := by
      intro z _
      split_ifs with hz
      · have hr0_le : r₀ ≤ degIn (graphOf ω) A z := by
          have := (Nat.floor_lt hL₁.le).mpr hz.1; omega
        have hlt_J : degIn (graphOf ω) A z < r₀ * 2 ^ J := by
          have h1 : (degIn (graphOf ω) A z : ℝ) < ((r₀ * 2 ^ J : ℕ) : ℝ) := by
            push_cast; exact hz.2.trans_le hcover
          exact_mod_cast h1
        -- Pick the largest `j < J` with `r₀ * 2^j ≤ deg`.
        let ValidJ := (Finset.range J).filter (fun j => r j ≤ degIn (graphOf ω) A z)
        have h0mem : 0 ∈ ValidJ := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), by simpa [r] using hr0_le⟩
        let j₀ := ValidJ.max' ⟨0, h0mem⟩
        have hj₀_mem : j₀ ∈ ValidJ := Finset.max'_mem ValidJ ⟨0, h0mem⟩
        have hj₀_lt : j₀ < J := Finset.mem_range.mp (Finset.mem_filter.mp hj₀_mem).1
        have hj₀_le : r j₀ ≤ degIn (graphOf ω) A z := (Finset.mem_filter.mp hj₀_mem).2
        have hj₀_act : j₀ ∈ ActiveJ := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hj₀_lt, lt_of_le_of_lt (by exact_mod_cast hj₀_le) hz.2⟩
        have hdeg_lt : degIn (graphOf ω) A z < 2 * r j₀ := by
          by_cases hsucc : j₀ + 1 < J
          · by_contra hge
            push Not at hge
            have hmem' : j₀ + 1 ∈ ValidJ := Finset.mem_filter.mpr
              ⟨Finset.mem_range.mpr hsucc, by
                have hr_eq : r (j₀ + 1) = 2 * r j₀ := by simp only [r, pow_succ]; ring
                omega⟩
            have := Finset.le_max' ValidJ (j₀ + 1) hmem'
            omega
          · have heqJ : j₀ + 1 = J := by omega
            have : 2 * r j₀ = r₀ * 2 ^ J := by
              rw [← heqJ]; simp only [r, pow_succ]; ring
            omega
        have hsq_le : (degIn (graphOf ω) A z : ℝ) ^ 2 ≤ 4 * ((r j₀ : ℕ) : ℝ) ^ 2 := by
          have hR : (degIn (graphOf ω) A z : ℝ) ≤ 2 * ((r j₀ : ℕ) : ℝ) := by exact_mod_cast hdeg_lt.le
          have h2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hR 2
          linarith only [h2]
        calc (degIn (graphOf ω) A z : ℝ) ^ 2
            ≤ 4 * ((r j₀ : ℕ) : ℝ) ^ 2 := hsq_le
          _ = (if r j₀ ≤ degIn (graphOf ω) A z then 4 * ((r j₀ : ℕ) : ℝ) ^ 2 else 0) := by
              rw [if_pos hj₀_le]
          _ ≤ ∑ j ∈ ActiveJ, if r j ≤ degIn (graphOf ω) A z then 4 * ((r j : ℕ) : ℝ) ^ 2 else 0 :=
              Finset.single_le_sum (f := fun j => if r j ≤ degIn (graphOf ω) A z then 4 * ((r j : ℕ) : ℝ) ^ 2 else 0)
                (fun _ _ => by split_ifs <;> positivity) hj₀_act
      · exact Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
    have hsum_lt : ∑ z ∈ Finset.univ \ A,
        (if L₁ < (degIn (graphOf ω) A z : ℝ) ∧ (degIn (graphOf ω) A z : ℝ) < L₂
          then (degIn (graphOf ω) A z : ℝ) ^ 2 else 0) < T₂ := by
      have h1 := Finset.sum_le_sum hpw
      rw [Finset.sum_comm] at h1
      have hinner : ∀ j ∈ ActiveJ,
          ∑ z ∈ Finset.univ \ A, (if r j ≤ degIn (graphOf ω) A z then 4 * ((r j : ℕ) : ℝ) ^ 2 else 0) =
          (((Finset.univ \ A).filter (fun z => r j ≤ degIn (graphOf ω) A z)).card : ℝ) *
            (4 * ((r j : ℕ) : ℝ) ^ 2) := by
        intro j _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      rw [Finset.sum_congr rfl hinner] at h1
      by_cases hne : ActiveJ.Nonempty
      · have hlt_sum : ∑ j ∈ ActiveJ,
            (((Finset.univ \ A).filter (fun z => r j ≤ degIn (graphOf ω) A z)).card : ℝ) *
              (4 * ((r j : ℕ) : ℝ) ^ 2) < ∑ _j ∈ ActiveJ, (T₂ / (J : ℝ)) :=
          Finset.sum_lt_sum_of_nonempty hne hlt_j
        have hcard_le : (ActiveJ.card : ℝ) ≤ (J : ℝ) := by
          have : ActiveJ.card ≤ J := (Finset.card_filter_le _ _).trans (by simp)
          exact_mod_cast this
        have htot : ∑ _j ∈ ActiveJ, (T₂ / (J : ℝ)) ≤ T₂ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          calc (ActiveJ.card : ℝ) * (T₂ / (J : ℝ)) ≤ (J : ℝ) * (T₂ / (J : ℝ)) :=
                mul_le_mul_of_nonneg_right hcard_le (by positivity)
            _ = T₂ := mul_div_cancel₀ T₂ hJ_pos.ne'
        linarith only [h1, hlt_sum, htot]
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne, Finset.sum_empty] at h1
        linarith only [h1, hT₂]
    linarith only [hω, hsum_lt]
  have h1 := (bernProb_mono hp0 hp1 himp).trans (bernProb_exists_le hp0 hp1 ActiveJ
    (fun j ω => b j ≤ ((Finset.univ \ A).filter (fun z => r j ≤ degIn (graphOf ω) A z)).card))
  -- For each `j ∈ ActiveJ`, union bound over `T ∈ (univ \ A).powersetCard (b j)` using independence across `z ∈ T`.
  have hper_j : ∀ j ∈ ActiveJ,
      bernProb p (fun ω : EdgeIdx m → Bool =>
        b j ≤ ((Finset.univ \ A).filter (fun z => r j ≤ degIn (graphOf ω) A z)).card) ≤
      ((m : ℝ) * (Real.exp 1 * (A.card : ℝ) * p / ((r j : ℕ) : ℝ)) ^ (r j)) ^ (b j) := by
    intro j _
    have hrj_pos : 1 ≤ r j := by
      have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      exact Nat.mul_pos hr₀_pos this
    have himpT : ∀ ω : EdgeIdx m → Bool,
        b j ≤ ((Finset.univ \ A).filter (fun z => r j ≤ degIn (graphOf ω) A z)).card →
        ∃ T ∈ (Finset.univ \ A).powersetCard (b j), ∀ z ∈ T, r j ≤ degIn (graphOf ω) A z := by
      intro ω hω
      obtain ⟨T, hTsub, hTc⟩ := Finset.exists_subset_card_eq hω
      exact ⟨T, Finset.mem_powersetCard.mpr ⟨hTsub.trans (Finset.filter_subset _ _), hTc⟩,
        fun z hz => (Finset.mem_filter.mp (hTsub hz)).2⟩
    have h2 := (bernProb_mono hp0 hp1 himpT).trans
      (bernProb_exists_le hp0 hp1 ((Finset.univ \ A).powersetCard (b j))
        (fun T ω => ∀ z ∈ T, r j ≤ degIn (graphOf ω) A z))
    have hT_bd : ∀ T ∈ (Finset.univ \ A).powersetCard (b j),
        bernProb p (fun ω : EdgeIdx m → Bool => ∀ z ∈ T, r j ≤ degIn (graphOf ω) A z) ≤
        ((Real.exp 1 * (A.card : ℝ) * p / ((r j : ℕ) : ℝ)) ^ (r j)) ^ (b j) := by
      intro T hT
      have hTsub : T ⊆ Finset.univ \ A := (Finset.mem_powersetCard.mp hT).1
      have hTc : T.card = b j := (Finset.mem_powersetCard.mp hT).2
      -- Reindex through `edgeSplitOut A` and apply `bernProb_pi_forall`!
      let e := (edgeSplitOut A).symm
      rw [bernProb_equiv e p]
      have hsymm : e.symm = edgeSplitOut A := Equiv.symm_symm (edgeSplitOut A)
      simp_rw [hsymm]
      have hrew : ∀ ω : ((Σ z : {z : Fin m // z ∉ A}, {a : Fin m // a ∈ A}) ⊕
          {e : EdgeIdx m // ¬ ((e.1.1 ∉ A ∧ e.1.2 ∈ A) ∨ (e.1.2 ∉ A ∧ e.1.1 ∈ A))}) → Bool,
          (∀ z ∈ T, r j ≤ degIn (graphOf (ω ∘ edgeSplitOut A)) A z) ↔
          (∀ z : {z : Fin m // z ∉ A},
            z.1 ∈ T → r j ≤ (Finset.univ.filter (fun a : {a : Fin m // a ∈ A} =>
              ω (Sum.inl ⟨z, a⟩) = true)).card) := by
        intro ω; constructor
        · intro hall z hzT
          rw [← degIn_edgeSplitOut A ω z]; exact hall z.1 hzT
        · intro hall z hzT
          have hznotA : z ∉ A := (Finset.mem_sdiff.mp (hTsub hzT)).2
          rw [degIn_edgeSplitOut A ω ⟨z, hznotA⟩]; exact hall ⟨z, hznotA⟩ hzT
      simp_rw [hrew]
      refine (bernProb_inl p (fun ωL : (Σ _ : {z : Fin m // z ∉ A}, {a : Fin m // a ∈ A}) → Bool =>
        ∀ z : {z : Fin m // z ∉ A},
          z.1 ∈ T → r j ≤ (Finset.univ.filter (fun a : {a : Fin m // a ∈ A} =>
            ωL ⟨z, a⟩ = true)).card)).trans_le ?_
      rw [bernProb_pi_forall p (fun (z : {z : Fin m // z ∉ A}) (ωz : {a : Fin m // a ∈ A} → Bool) =>
        z.1 ∈ T → r j ≤ (Finset.univ.filter (fun a => ωz a = true)).card)]
      have hfac : ∀ z : {z : Fin m // z ∉ A},
          bernProb p (fun ωz : {a : Fin m // a ∈ A} → Bool =>
            z.1 ∈ T → r j ≤ (Finset.univ.filter (fun a => ωz a = true)).card) ≤
          if z.1 ∈ T then (Real.exp 1 * (A.card : ℝ) * p / ((r j : ℕ) : ℝ)) ^ (r j) else 1 := by
        intro z
        by_cases hzT : z.1 ∈ T
        · rw [if_pos hzT]
          have hsimp : (fun ωz : {a : Fin m // a ∈ A} → Bool =>
              z.1 ∈ T → r j ≤ (Finset.univ.filter (fun a => ωz a = true)).card) =
              (fun ωz : {a : Fin m // a ∈ A} → Bool =>
                r j ≤ (Finset.univ.filter (fun a => ωz a = true)).card) := by
            funext ωz; simp [hzT]
          rw [hsimp]
          have hb := bernProb_binom_ge_pow hp0 hp1 (Finset.univ : Finset {a : Fin m // a ∈ A}) hrj_pos
          have hcardA : ((Finset.univ : Finset {a : Fin m // a ∈ A}).card : ℝ) = (A.card : ℝ) := by simp
          rwa [hcardA] at hb
        · rw [if_neg hzT]
          have h1 : bernProb p (fun ωz : {a : Fin m // a ∈ A} → Bool =>
              z.1 ∈ T → r j ≤ (Finset.univ.filter (fun a => ωz a = true)).card) =
              ∑ ωz : {a : Fin m // a ∈ A} → Bool, bernW p ωz := by
            simp only [bernProb, hzT, false_implies, ite_true]
          rw [h1, sum_bernW_eq_one]
      have hprod_le : ∏ z : {z : Fin m // z ∉ A},
          bernProb p (fun ωz : {a : Fin m // a ∈ A} → Bool =>
            z.1 ∈ T → r j ≤ (Finset.univ.filter (fun a => ωz a = true)).card) ≤
          ∏ z : {z : Fin m // z ∉ A},
            if z.1 ∈ T then (Real.exp 1 * (A.card : ℝ) * p / ((r j : ℕ) : ℝ)) ^ (r j) else 1 :=
        Finset.prod_le_prod (fun z _ => bernProb_nonneg hp0 hp1 _) fun z _ => hfac z
      refine hprod_le.trans (le_of_eq ?_)
      rw [← Finset.prod_filter]
      have hcard_filt : (Finset.univ.filter (fun z : {z : Fin m // z ∉ A} => z.1 ∈ T)).card = b j := by
        rw [← hTc]
        refine Finset.card_bij (fun z _ => z.1) ?_ ?_ ?_
        · intro z hz; exact (Finset.mem_filter.mp hz).2
        · intro z₁ _ z₂ _ h; exact Subtype.ext h
        · intro z hz; exact ⟨⟨z, (Finset.mem_sdiff.mp (hTsub hz)).2⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩, rfl⟩
      rw [Finset.prod_const, hcard_filt]
    have hcard_pow : (((Finset.univ \ A).powersetCard (b j)).card : ℝ) ≤ (m : ℝ) ^ (b j) := by
      rw [Finset.card_powersetCard]
      have h1 : (Finset.univ \ A).card.choose (b j) ≤ (Finset.univ \ A).card ^ (b j) := by
        have h2 : (Finset.univ \ A).card.choose (b j) * (b j).factorial ≤ (Finset.univ \ A).card ^ (b j) := by
          rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]; exact Nat.descFactorial_le_pow _ _
        exact le_trans (Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)) h2
      have h2 : (Finset.univ \ A).card ≤ m := by
        calc (Finset.univ \ A).card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card Finset.sdiff_subset
          _ = m := by simp
      exact_mod_cast h1.trans (Nat.pow_le_pow_left h2 (b j))
    calc _ ≤ ∑ _T ∈ (Finset.univ \ A).powersetCard (b j),
            ((Real.exp 1 * (A.card : ℝ) * p / ((r j : ℕ) : ℝ)) ^ (r j)) ^ (b j) :=
          h2.trans (Finset.sum_le_sum hT_bd)
      _ = (((Finset.univ \ A).powersetCard (b j)).card : ℝ) *
            ((Real.exp 1 * (A.card : ℝ) * p / ((r j : ℕ) : ℝ)) ^ (r j)) ^ (b j) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (m : ℝ) ^ (b j) * ((Real.exp 1 * (A.card : ℝ) * p / ((r j : ℕ) : ℝ)) ^ (r j)) ^ (b j) :=
          mul_le_mul_of_nonneg_right hcard_pow (by positivity)
      _ = ((m : ℝ) * (Real.exp 1 * (A.card : ℝ) * p / ((r j : ℕ) : ℝ)) ^ (r j)) ^ (b j) :=
          (mul_pow _ _ _).symm
  calc _ ≤ ∑ j ∈ ActiveJ, ((m : ℝ) * (Real.exp 1 * (A.card : ℝ) * p / ((r j : ℕ) : ℝ)) ^ (r j)) ^ (b j) :=
        h1.trans (Finset.sum_le_sum hper_j)
    _ = ∑ j ∈ Finset.range J,
          if ((r j : ℕ) : ℝ) < L₂ then
            ((m : ℝ) * (Real.exp 1 * (A.card : ℝ) * p / ((r j : ℕ) : ℝ)) ^ (r j)) ^ (b j)
          else 0 := by rw [Finset.sum_filter]

/-- Piece 3 (large-degree tail `L₂ ≤ X_z ≤ D`): greedy pruning reduces `∑_{z ∉ A, L₂ ≤ X_z} X_z^2 ≥ T₃`
to the existence of a small subset `U' ⊆ univ \ A` of size `1 ≤ u ≤ ⌊(E₀ + D) / L₂⌋` with
`⌈T₃ / D⌉ ≤ e(A, U')`. -/
lemma bernProb_degOut_sq_large {m : ℕ} {p L₂ D T₃ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hL₂ : 0 < L₂) (hD : 0 < D) (hT₃ : 0 < T₃) (A : Finset (Fin m)) :
    let E₀ : ℝ := T₃ / D
    let e₀ : ℕ := Nat.ceil E₀
    let u_max : ℕ := Nat.floor ((E₀ + D) / L₂)
    bernProb p (fun ω : EdgeIdx m → Bool =>
      (∀ z ∈ Finset.univ \ A, (degIn (graphOf ω) A z : ℝ) ≤ D) ∧
      T₃ ≤ ∑ z ∈ Finset.univ \ A,
        if L₂ ≤ (degIn (graphOf ω) A z : ℝ) then (degIn (graphOf ω) A z : ℝ) ^ 2 else 0) ≤
      ∑ u ∈ Finset.Icc 1 u_max,
        (m : ℝ) ^ u * (Real.exp 1 * ((A.card : ℝ) * (u : ℝ)) * p / (e₀ : ℝ)) ^ e₀ := by
  intro E₀ e₀ u_max
  have hE₀_pos : 0 < E₀ := div_pos hT₃ hD
  have he₀_pos : 1 ≤ e₀ := Nat.one_le_iff_ne_zero.mpr (by
    intro h0; have := (Nat.ceil_eq_zero.mp h0); linarith only [this, hE₀_pos])
  -- Deterministic pruning: extract `U' ⊆ univ \ A` with `1 ≤ U'.card ≤ u_max` and `e₀ ≤ ∑_{z ∈ U'} degIn A z`.
  have himp : ∀ ω : EdgeIdx m → Bool,
      ((∀ z ∈ Finset.univ \ A, (degIn (graphOf ω) A z : ℝ) ≤ D) ∧
        T₃ ≤ ∑ z ∈ Finset.univ \ A,
          if L₂ ≤ (degIn (graphOf ω) A z : ℝ) then (degIn (graphOf ω) A z : ℝ) ^ 2 else 0) →
      ∃ u ∈ Finset.Icc 1 u_max, ∃ U' ∈ (Finset.univ \ A).powersetCard u,
        e₀ ≤ ∑ z ∈ U', degIn (graphOf ω) A z := by
    intro ω ⟨hdeg_le, hsum_sq⟩
    let U := (Finset.univ \ A).filter (fun z => L₂ ≤ (degIn (graphOf ω) A z : ℝ))
    have hsum_U : E₀ ≤ ∑ z ∈ U, (degIn (graphOf ω) A z : ℝ) := by
      have h1 : T₃ ≤ D * ∑ z ∈ U, (degIn (graphOf ω) A z : ℝ) := by
        rw [Finset.mul_sum]
        calc T₃ ≤ ∑ z ∈ Finset.univ \ A,
                if L₂ ≤ (degIn (graphOf ω) A z : ℝ) then (degIn (graphOf ω) A z : ℝ) ^ 2 else 0 := hsum_sq
          _ = ∑ z ∈ U, (degIn (graphOf ω) A z : ℝ) ^ 2 := by rw [← Finset.sum_filter]
          _ ≤ ∑ z ∈ U, D * (degIn (graphOf ω) A z : ℝ) := Finset.sum_le_sum fun z hz => by
                have hd := hdeg_le z (Finset.mem_filter.mp hz).1
                nlinarith only [hd, Nat.cast_nonneg (α := ℝ) (degIn (graphOf ω) A z)]
      exact (div_le_iff₀ hD).mpr (by linarith only [h1])
    obtain ⟨U', hU'sub, hU'ge, _, hU'card⟩ := exists_pruned_subset U (fun z => (degIn (graphOf ω) A z : ℝ))
      hL₂.le hD.le hE₀_pos.le
      (fun z hz => ⟨(Finset.mem_filter.mp hz).2, hdeg_le z (Finset.mem_filter.mp hz).1⟩) hsum_U
    have hU'pos : 1 ≤ U'.card := by
      by_contra h0
      have hemp : U' = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hemp; simp at hU'ge; linarith only [hU'ge, hE₀_pos]
    have hU'le : U'.card ≤ u_max := by
      refine Nat.le_floor ?_
      rw [le_div_iff₀ hL₂]; exact hU'card
    have hsum_nat : e₀ ≤ ∑ z ∈ U', degIn (graphOf ω) A z := by
      refine Nat.ceil_le.mpr ?_
      simpa [Nat.cast_sum] using hU'ge
    exact ⟨U'.card, Finset.mem_Icc.mpr ⟨hU'pos, hU'le⟩, U',
      Finset.mem_powersetCard.mpr ⟨hU'sub.trans (Finset.filter_subset _ _), rfl⟩, hsum_nat⟩
  have h1 := (bernProb_mono hp0 hp1 himp).trans
    (bernProb_exists_le hp0 hp1 (Finset.Icc 1 u_max)
      (fun u ω => ∃ U' ∈ (Finset.univ \ A).powersetCard u, e₀ ≤ ∑ z ∈ U', degIn (graphOf ω) A z))
  refine h1.trans (Finset.sum_le_sum fun u _ => ?_)
  have h2 := bernProb_exists_le hp0 hp1 ((Finset.univ \ A).powersetCard u)
    (fun U' ω => e₀ ≤ ∑ z ∈ U', degIn (graphOf ω) A z)
  have hU'_bd : ∀ U' ∈ (Finset.univ \ A).powersetCard u,
      bernProb p (fun ω : EdgeIdx m → Bool => e₀ ≤ ∑ z ∈ U', degIn (graphOf ω) A z) ≤
      (Real.exp 1 * ((A.card : ℝ) * (u : ℝ)) * p / (e₀ : ℝ)) ^ e₀ := by
    intro U' hU'
    have hU'sub : U' ⊆ Finset.univ \ A := (Finset.mem_powersetCard.mp hU').1
    have hU'c : U'.card = u := (Finset.mem_powersetCard.mp hU').2
    -- Edges between `U'` and `A` form a subset `S_UA ⊆ EdgeIdx m` of cardinality `A.card * u`.
    let S_UA : Finset (EdgeIdx m) := Finset.univ.filter fun e =>
      (e.1.1 ∈ U' ∧ e.1.2 ∈ A) ∨ (e.1.2 ∈ U' ∧ e.1.1 ∈ A)
    have hdisj : Disjoint U' A := Finset.disjoint_left.mpr fun z hz => (Finset.mem_sdiff.mp (hU'sub hz)).2
    have hSUA_card : S_UA.card = A.card * u := by
      have hbij : S_UA.card = (A ×ˢ U').card := by
        refine Finset.card_bij (fun e _ => if e.1.1 ∈ A then (e.1.1, e.1.2) else (e.1.2, e.1.1)) ?_ ?_ ?_
        · intro e he
          rcases (Finset.mem_filter.mp he).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have hnot : e.1.1 ∉ A := (Finset.mem_sdiff.mp (hU'sub h1)).2
            rw [if_neg hnot]; exact Finset.mem_product.mpr ⟨h2, h1⟩
          · rw [if_pos h2]; exact Finset.mem_product.mpr ⟨h2, h1⟩
        · intro e₁ he₁ e₂ he₂ heq
          rcases (Finset.mem_filter.mp he₁).2 with ⟨h1u, h1a⟩ | ⟨h1u, h1a⟩ <;>
          rcases (Finset.mem_filter.mp he₂).2 with ⟨h2u, h2a⟩ | ⟨h2u, h2a⟩
          · have hnot1 : e₁.1.1 ∉ A := (Finset.mem_sdiff.mp (hU'sub h1u)).2
            have hnot2 : e₂.1.1 ∉ A := (Finset.mem_sdiff.mp (hU'sub h2u)).2
            simp only [if_neg hnot1, if_neg hnot2] at heq
            exact Subtype.ext (Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq))
          · have hnot1 : e₁.1.1 ∉ A := (Finset.mem_sdiff.mp (hU'sub h1u)).2
            simp only [if_neg hnot1, if_pos h2a] at heq
            have ha : e₁.1.2 = e₂.1.1 := congrArg Prod.fst heq
            have hu : e₁.1.1 = e₂.1.2 := congrArg Prod.snd heq
            exact absurd (lt_trans e₁.2 (by rw [ha]; exact e₂.2)) (by rw [hu]; exact lt_irrefl _)
          · have hnot2 : e₂.1.1 ∉ A := (Finset.mem_sdiff.mp (hU'sub h2u)).2
            simp only [if_pos h1a, if_neg hnot2] at heq
            have ha : e₁.1.1 = e₂.1.2 := congrArg Prod.fst heq
            have hu : e₁.1.2 = e₂.1.1 := congrArg Prod.snd heq
            exact absurd (lt_trans e₁.2 (by rw [hu]; exact e₂.2)) (by rw [ha]; exact lt_irrefl _)
          · simp only [if_pos h1a, if_pos h2a] at heq
            exact Subtype.ext heq
        · intro q hq
          have ha : q.1 ∈ A := (Finset.mem_product.mp hq).1
          have hu : q.2 ∈ U' := (Finset.mem_product.mp hq).2
          have hne : q.1 ≠ q.2 := fun h => (Finset.mem_sdiff.mp (hU'sub hu)).2 (h ▸ ha)
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact ⟨⟨(q.1, q.2), hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨hu, ha⟩⟩,
              by simp [ha]⟩
          · have hnot : q.2 ∉ A := (Finset.mem_sdiff.mp (hU'sub hu)).2
            exact ⟨⟨(q.2, q.1), hgt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨hu, ha⟩⟩,
              by simp [hnot]⟩
      rw [hbij, Finset.card_product, hU'c]
    have hsum_eq : ∀ ω : EdgeIdx m → Bool,
        ∑ z ∈ U', degIn (graphOf ω) A z = (S_UA.filter (fun e => ω e = true)).card := by
      intro ω
      have hprod : ∑ z ∈ U', degIn (graphOf ω) A z =
          ((U' ×ˢ A).filter (fun q => (graphOf ω).Adj q.1 q.2)).card := by
        simp only [degIn, Finset.card_filter, Finset.sum_product]
      rw [hprod]
      refine Finset.card_bij (fun q hq =>
        if hlt : q.1 < q.2 then ⟨(q.1, q.2), hlt⟩
        else ⟨(q.2, q.1), lt_of_le_of_ne (not_lt.mp hlt) (fun h : q.2 = q.1 =>
          (Finset.mem_sdiff.mp (hU'sub (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1)).2
            (h ▸ (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).2))⟩) ?_ ?_ ?_
      · intro q hq
        have hqU : q.1 ∈ U' := (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1
        have hqA : q.2 ∈ A := (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).2
        have hadj := (Finset.mem_filter.mp hq).2
        simp only [graphOf] at hadj
        by_cases hlt : q.1 < q.2
        · rw [dif_pos hlt] at hadj
          simp only [dif_pos hlt, S_UA, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨Or.inl ⟨hqU, hqA⟩, hadj⟩
        · have hne : q.2 ≠ q.1 := fun h => (Finset.mem_sdiff.mp (hU'sub hqU)).2 (h ▸ hqA)
          have hgt : q.2 < q.1 := lt_of_le_of_ne (not_lt.mp hlt) hne
          rw [dif_neg hlt, dif_pos hgt] at hadj
          simp only [dif_neg hlt, S_UA, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨Or.inr ⟨hqU, hqA⟩, hadj⟩
      · intro q₁ hq₁ q₂ hq₂ heq
        have h1U : q₁.1 ∈ U' := (Finset.mem_product.mp (Finset.mem_filter.mp hq₁).1).1
        have h1A : q₁.2 ∈ A := (Finset.mem_product.mp (Finset.mem_filter.mp hq₁).1).2
        have h2U : q₂.1 ∈ U' := (Finset.mem_product.mp (Finset.mem_filter.mp hq₂).1).1
        have h2A : q₂.2 ∈ A := (Finset.mem_product.mp (Finset.mem_filter.mp hq₂).1).2
        by_cases hlt1 : q₁.1 < q₁.2 <;> by_cases hlt2 : q₂.1 < q₂.2
        · simp only [dif_pos hlt1, dif_pos hlt2] at heq
          exact Prod.ext (congrArg (fun e : EdgeIdx m => e.1.1) heq) (congrArg (fun e : EdgeIdx m => e.1.2) heq)
        · simp only [dif_pos hlt1, dif_neg hlt2] at heq
          have h : q₁.1 = q₂.2 := congrArg (fun e : EdgeIdx m => e.1.1) heq
          exact absurd (h ▸ h2A) (Finset.mem_sdiff.mp (hU'sub h1U)).2
        · simp only [dif_neg hlt1, dif_pos hlt2] at heq
          have h : q₁.2 = q₂.1 := congrArg (fun e : EdgeIdx m => e.1.1) heq
          exact absurd (h ▸ h1A) (Finset.mem_sdiff.mp (hU'sub h2U)).2
        · simp only [dif_neg hlt1, dif_neg hlt2] at heq
          exact Prod.ext (congrArg (fun e : EdgeIdx m => e.1.2) heq) (congrArg (fun e : EdgeIdx m => e.1.1) heq)
      · intro e he
        have htrue := (Finset.mem_filter.mp he).2
        rcases (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2 with ⟨hU, hA⟩ | ⟨hU, hA⟩
        · refine ⟨(e.1.1, e.1.2), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hU, hA⟩, ?_⟩, ?_⟩
          · simp only [graphOf, dif_pos e.2]; exact htrue
          · simp only [dif_pos e.2]
        · have hnot : ¬ e.1.2 < e.1.1 := lt_asymm e.2
          refine ⟨(e.1.2, e.1.1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hU, hA⟩, ?_⟩, ?_⟩
          · simp only [graphOf, dif_neg hnot, dif_pos e.2]; exact htrue
          · simp only [dif_neg hnot]
    simp_rw [hsum_eq]
    have hb := bernProb_binom_ge_pow hp0 hp1 S_UA he₀_pos
    rw [hSUA_card, Nat.cast_mul] at hb
    exact hb
  have hcard_pow : (((Finset.univ \ A).powersetCard u).card : ℝ) ≤ (m : ℝ) ^ u := by
    rw [Finset.card_powersetCard]
    have h1 : (Finset.univ \ A).card.choose u ≤ (Finset.univ \ A).card ^ u := by
      have h2 : (Finset.univ \ A).card.choose u * u.factorial ≤ (Finset.univ \ A).card ^ u := by
        rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]; exact Nat.descFactorial_le_pow _ _
      exact le_trans (Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)) h2
    have h2 : (Finset.univ \ A).card ≤ m :=
      (Finset.card_le_card Finset.sdiff_subset).trans (by simp)
    exact_mod_cast h1.trans (Nat.pow_le_pow_left h2 u)
  calc _ ≤ ∑ _U' ∈ (Finset.univ \ A).powersetCard u,
          (Real.exp 1 * ((A.card : ℝ) * (u : ℝ)) * p / (e₀ : ℝ)) ^ e₀ :=
        h2.trans (Finset.sum_le_sum hU'_bd)
    _ = (((Finset.univ \ A).powersetCard u).card : ℝ) *
          (Real.exp 1 * ((A.card : ℝ) * (u : ℝ)) * p / (e₀ : ℝ)) ^ e₀ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (m : ℝ) ^ u * (Real.exp 1 * ((A.card : ℝ) * (u : ℝ)) * p / (e₀ : ℝ)) ^ e₀ :=
        mul_le_mul_of_nonneg_right hcard_pow (by positivity)

/-- Bad event on a single graph `ω : EdgeIdx m → Bool`: either max degree exceeds `2 m p`,
or some `A` of size `≤ t` has `∑_{z ∉ A} degIn A z ^ 2 > (1 / 1000) t^2`. -/
def BadGraph (m t : ℕ) (p : ℝ) (ω : EdgeIdx m → Bool) : Prop :=
  (∃ x : Fin m, 2 * ((m : ℝ) * p) < (degIn (graphOf ω) Finset.univ x : ℝ)) ∨
  (∃ A : Finset (Fin m), A.card ≤ t ∧
    (1 / 1000 : ℝ) * (t : ℝ) ^ 2 < ∑ z ∈ Finset.univ \ A, (degIn (graphOf ω) A z : ℝ) ^ 2)

/-- Master union bound for `BadGraph`: splits into max-degree + 3-piece sum over `A` (`|A| ≤ t`). -/
lemma bernProb_badGraph_le {m t J : ℕ} {p L₁ L₂ : ℝ} (hm : 1 ≤ m) (ht : 1 ≤ t) (hJ : 1 ≤ J)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hL₁ : 0 < L₁) (hL₂ : L₁ < L₂)
    (hcover : L₂ ≤ ((Nat.floor L₁ + 1 : ℕ) : ℝ) * (2 : ℝ) ^ J) :
    let r₀ : ℕ := Nat.floor L₁ + 1
    let T_p : ℝ := (1 / 4000 : ℝ) * (t : ℝ) ^ 2
    let D : ℝ := 2 * ((m : ℝ) * p)
    let E₀ : ℝ := T_p / D
    let e₀ : ℕ := Nat.ceil E₀
    let u_max : ℕ := Nat.floor ((E₀ + D) / L₂)
    let P_per_A : ℝ :=
      Real.exp ((2 * (m : ℝ) * ((t : ℝ) * p + ((t : ℝ) * p) ^ 2) - T_p) / L₁ ^ 2) +
      (∑ j ∈ Finset.range J,
        if ((r₀ * 2 ^ j : ℕ) : ℝ) < L₂ then
          let rj : ℕ := r₀ * 2 ^ j
          let bj : ℕ := Nat.ceil (T_p / (4 * (J : ℝ) * (rj : ℝ) ^ 2))
          ((m : ℝ) * (Real.exp 1 * (t : ℝ) * p / (rj : ℝ)) ^ rj) ^ bj
        else 0) +
      ∑ u ∈ Finset.Icc 1 u_max,
        (m : ℝ) ^ u * (Real.exp 1 * ((t : ℝ) * (u : ℝ)) * p / (e₀ : ℝ)) ^ e₀
    bernProb p (BadGraph m t p) ≤
      (m : ℝ) * Real.exp (-(((m - 1 : ℕ) : ℝ) * p) / 6) +
      ((t : ℝ) + 1) * (m : ℝ) ^ t * P_per_A := by
  intro r₀ T_p D E₀ e₀ u_max P_per_A
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have ht_pos : (0 : ℝ) < (t : ℝ) := Nat.cast_pos.mpr (by omega)
  have hTp_pos : 0 < T_p := by positivity
  have hD_pos : 0 < D := by positivity
  have hL₂_pos : 0 < L₂ := lt_trans hL₁ hL₂
  let MaxDegBad : (EdgeIdx m → Bool) → Prop := fun ω =>
    ∃ x : Fin m, D < (degIn (graphOf ω) Finset.univ x : ℝ)
  let AllSmallA : Finset (Finset (Fin m)) := Finset.univ.filter (fun A => A.card ≤ t)
  have hsplit : ∀ ω : EdgeIdx m → Bool, BadGraph m t p ω →
      MaxDegBad ω ∨ ∃ A ∈ AllSmallA,
        (∀ z ∈ Finset.univ \ A, (degIn (graphOf ω) A z : ℝ) ≤ D) ∧
        (1 / 1000 : ℝ) * (t : ℝ) ^ 2 < ∑ z ∈ Finset.univ \ A, (degIn (graphOf ω) A z : ℝ) ^ 2 := by
    intro ω hω
    by_cases hmd : MaxDegBad ω
    · exact Or.inl hmd
    · rcases hω with h1 | ⟨A, hAt, hsum⟩
      · exact Or.inl h1
      · refine Or.inr ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAt⟩, ?_, hsum⟩
        intro z _
        simp only [MaxDegBad, not_exists, not_lt] at hmd
        have hle : degIn (graphOf ω) A z ≤ degIn (graphOf ω) Finset.univ z :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ A))
        exact (Nat.cast_le.mpr hle).trans (hmd z)
  have h1 := (bernProb_mono hp0.le hp1 hsplit).trans (bernProb_or_le hp0.le hp1 _ _)
  have hmd_bd := bernProb_maxDeg_le hm hp0.le hp1
  have hA_exists := bernProb_exists_le hp0.le hp1 AllSmallA
    (fun A ω => (∀ z ∈ Finset.univ \ A, (degIn (graphOf ω) A z : ℝ) ≤ D) ∧
      (1 / 1000 : ℝ) * (t : ℝ) ^ 2 < ∑ z ∈ Finset.univ \ A, (degIn (graphOf ω) A z : ℝ) ^ 2)
  -- For each `A` with `A.card ≤ t`, bound the 3 pieces by `P_per_A`.
  have hperA : ∀ A ∈ AllSmallA,
      bernProb p (fun ω : EdgeIdx m → Bool =>
        (∀ z ∈ Finset.univ \ A, (degIn (graphOf ω) A z : ℝ) ≤ D) ∧
        (1 / 1000 : ℝ) * (t : ℝ) ^ 2 < ∑ z ∈ Finset.univ \ A, (degIn (graphOf ω) A z : ℝ) ^ 2) ≤
      P_per_A := by
    intro A hA
    have hAt : (A.card : ℝ) ≤ (t : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hA).2
    have h3split : ∀ ω : EdgeIdx m → Bool,
        ((∀ z ∈ Finset.univ \ A, (degIn (graphOf ω) A z : ℝ) ≤ D) ∧
         (1 / 1000 : ℝ) * (t : ℝ) ^ 2 < ∑ z ∈ Finset.univ \ A, (degIn (graphOf ω) A z : ℝ) ^ 2) →
        (T_p ≤ ∑ z ∈ Finset.univ \ A, if (degIn (graphOf ω) A z : ℝ) ≤ L₁ then (degIn (graphOf ω) A z : ℝ) ^ 2 else 0) ∨
        (T_p ≤ ∑ z ∈ Finset.univ \ A, if L₁ < (degIn (graphOf ω) A z : ℝ) ∧ (degIn (graphOf ω) A z : ℝ) < L₂ then (degIn (graphOf ω) A z : ℝ) ^ 2 else 0) ∨
        ((∀ z ∈ Finset.univ \ A, (degIn (graphOf ω) A z : ℝ) ≤ D) ∧
          T_p ≤ ∑ z ∈ Finset.univ \ A, if L₂ ≤ (degIn (graphOf ω) A z : ℝ) then (degIn (graphOf ω) A z : ℝ) ^ 2 else 0) := by
      intro ω ⟨hdeg, hgt⟩
      have htot : ∑ z ∈ Finset.univ \ A, (degIn (graphOf ω) A z : ℝ) ^ 2 =
          (∑ z ∈ Finset.univ \ A, if (degIn (graphOf ω) A z : ℝ) ≤ L₁ then (degIn (graphOf ω) A z : ℝ) ^ 2 else 0) +
          (∑ z ∈ Finset.univ \ A, if L₁ < (degIn (graphOf ω) A z : ℝ) ∧ (degIn (graphOf ω) A z : ℝ) < L₂ then (degIn (graphOf ω) A z : ℝ) ^ 2 else 0) +
          (∑ z ∈ Finset.univ \ A, if L₂ ≤ (degIn (graphOf ω) A z : ℝ) then (degIn (graphOf ω) A z : ℝ) ^ 2 else 0) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun z _ => ?_
        set x : ℝ := (degIn (graphOf ω) A z : ℝ)
        by_cases h1 : x ≤ L₁
        · have h2 : ¬ (L₁ < x ∧ x < L₂) := fun h => not_lt.mpr h1 h.1
          have h3 : ¬ L₂ ≤ x := fun h => not_lt.mpr (h.trans h1) hL₂
          simp [h1, h2, h3]
        · by_cases h3 : L₂ ≤ x
          · have h2 : ¬ (L₁ < x ∧ x < L₂) := fun h => not_lt.mpr h3 h.2
            simp [h1, h2, h3]
          · have h2 : L₁ < x ∧ x < L₂ := ⟨lt_of_not_ge h1, lt_of_not_ge h3⟩
            simp [h1, h2, h3]
      by_contra hnone
      push Not at hnone
      have h3 : ∑ z ∈ Finset.univ \ A,
          (if L₂ ≤ (degIn (graphOf ω) A z : ℝ) then (degIn (graphOf ω) A z : ℝ) ^ 2 else 0) < T_p :=
        hnone.2.2 hdeg
      have h4Tp : 4 * T_p = (1 / 1000 : ℝ) * (t : ℝ) ^ 2 := by simp only [T_p]; ring
      linarith only [htot, hgt, hnone.1, hnone.2.1, h3, hTp_pos, h4Tp]
    have hprob3 := (bernProb_mono hp0.le hp1 h3split).trans
      ((bernProb_or_le hp0.le hp1 _ _).trans (add_le_add le_rfl (bernProb_or_le hp0.le hp1 _ _)))
    have hp1_bd : bernProb p (fun ω =>
        T_p ≤ ∑ z ∈ Finset.univ \ A, if (degIn (graphOf ω) A z : ℝ) ≤ L₁ then (degIn (graphOf ω) A z : ℝ) ^ 2 else 0) ≤
        Real.exp ((2 * (m : ℝ) * ((t : ℝ) * p + ((t : ℝ) * p) ^ 2) - T_p) / L₁ ^ 2) := by
      refine (bernProb_degOut_sq_small hp0.le hp1 hL₁ A).trans (Real.exp_le_exp.mpr
        (div_le_div_of_nonneg_right ?_ (sq_nonneg L₁)))
      have hsq : ((A.card : ℝ) * p) ^ 2 ≤ ((t : ℝ) * p) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hAt hp0.le) 2
      have hlin : (A.card : ℝ) * p ≤ (t : ℝ) * p := mul_le_mul_of_nonneg_right hAt hp0.le
      nlinarith only [hsq, hlin, hm_pos]
    have hp2_bd : bernProb p (fun ω =>
        T_p ≤ ∑ z ∈ Finset.univ \ A, if L₁ < (degIn (graphOf ω) A z : ℝ) ∧ (degIn (graphOf ω) A z : ℝ) < L₂
          then (degIn (graphOf ω) A z : ℝ) ^ 2 else 0) ≤
        ∑ j ∈ Finset.range J,
          if ((r₀ * 2 ^ j : ℕ) : ℝ) < L₂ then
            let rj : ℕ := r₀ * 2 ^ j
            let bj : ℕ := Nat.ceil (T_p / (4 * (J : ℝ) * (rj : ℝ) ^ 2))
            ((m : ℝ) * (Real.exp 1 * (t : ℝ) * p / (rj : ℝ)) ^ rj) ^ bj
          else 0 := by
      refine (bernProb_degOut_sq_mid hp0.le hp1 hL₁ hJ hTp_pos hcover A).trans (Finset.sum_le_sum fun j _ => ?_)
      split_ifs
      · refine pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)) _) hm_pos.le) _
        have : Real.exp 1 * (A.card : ℝ) * p ≤ Real.exp 1 * (t : ℝ) * p := by
          gcongr
        exact this
      · exact le_rfl
    have hp3_bd : bernProb p (fun ω =>
        (∀ z ∈ Finset.univ \ A, (degIn (graphOf ω) A z : ℝ) ≤ D) ∧
        T_p ≤ ∑ z ∈ Finset.univ \ A, if L₂ ≤ (degIn (graphOf ω) A z : ℝ) then (degIn (graphOf ω) A z : ℝ) ^ 2 else 0) ≤
        ∑ u ∈ Finset.Icc 1 u_max,
          (m : ℝ) ^ u * (Real.exp 1 * ((t : ℝ) * (u : ℝ)) * p / (e₀ : ℝ)) ^ e₀ := by
      refine (bernProb_degOut_sq_large hp0.le hp1 hL₂_pos hD_pos hTp_pos A).trans (Finset.sum_le_sum fun u _ => ?_)
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
        (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)) _) (by positivity)
      gcongr
    linarith only [hprob3, hp1_bd, hp2_bd, hp3_bd]
  -- Bound `AllSmallA.card ≤ (t + 1) * m^t`.
  have hAllA_card : (AllSmallA.card : ℝ) ≤ ((t : ℝ) + 1) * (m : ℝ) ^ t := by
    have hcovA : AllSmallA ⊆ (Finset.range (t + 1)).biUnion fun a =>
        (Finset.univ : Finset (Fin m)).powersetCard a := by
      intro A hA
      have hAt := (Finset.mem_filter.mp hA).2
      exact Finset.mem_biUnion.mpr ⟨A.card, Finset.mem_range.mpr (by omega),
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩
    have hnat : AllSmallA.card ≤ ∑ a ∈ Finset.range (t + 1), m.choose a := by
      calc AllSmallA.card ≤ ∑ a ∈ Finset.range (t + 1),
              ((Finset.univ : Finset (Fin m)).powersetCard a).card :=
            (Finset.card_le_card hcovA).trans Finset.card_biUnion_le
        _ = ∑ a ∈ Finset.range (t + 1), m.choose a := by simp
    have hpow : ∀ a ∈ Finset.range (t + 1), m.choose a ≤ m ^ t := by
      intro a ha
      have hat : a ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      have h1 : m.choose a ≤ m ^ a := by
        have h2 : m.choose a * a.factorial ≤ m ^ a := by
          rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]; exact Nat.descFactorial_le_pow _ _
        exact le_trans (Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)) h2
      exact h1.trans (Nat.pow_le_pow_right (by omega) hat)
    have hnat2 : AllSmallA.card ≤ (t + 1) * m ^ t := by
      calc AllSmallA.card ≤ ∑ _a ∈ Finset.range (t + 1), m ^ t :=
            hnat.trans (Finset.sum_le_sum hpow)
        _ = (t + 1) * m ^ t := by simp
    exact_mod_cast hnat2
  have hP_nn : 0 ≤ P_per_A := by
    refine add_nonneg (add_nonneg (Real.exp_pos _).le ?_) ?_
    · exact Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
    · exact Finset.sum_nonneg fun _ _ => by positivity
  have hsumA : ∑ A ∈ AllSmallA, bernProb p (fun ω =>
      (∀ z ∈ Finset.univ \ A, (degIn (graphOf ω) A z : ℝ) ≤ D) ∧
      (1 / 1000 : ℝ) * (t : ℝ) ^ 2 < ∑ z ∈ Finset.univ \ A, (degIn (graphOf ω) A z : ℝ) ^ 2) ≤
      ((t : ℝ) + 1) * (m : ℝ) ^ t * P_per_A := by
    calc _ ≤ ∑ _A ∈ AllSmallA, P_per_A := Finset.sum_le_sum hperA
      _ = (AllSmallA.card : ℝ) * P_per_A := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((t : ℝ) + 1) * (m : ℝ) ^ t * P_per_A := mul_le_mul_of_nonneg_right hAllA_card hP_nn
  linarith only [h1, hmd_bd, hA_exists, hsumA]

end TypicalityBounds

/- ### Section 4A: Sequential-Exposure Supermartingale and Blue/Red Independent-Set Bound -/

section IndepSetBound

/-- Conditioning bound on `A ⊕ B → Bool`: if for every `ωB` the conditional probability over `ωA`
is at most `c`, then the joint probability is at most `c`. -/
lemma bernProb_sum_cond_le {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] {p c : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : (A → Bool) → (B → Bool) → Prop)
    (hbound : ∀ ωB : B → Bool, bernProb p (fun ωA => P ωA ωB) ≤ c) :
    bernProb p (fun ω : A ⊕ B → Bool => P (fun a => ω (Sum.inl a)) (fun b => ω (Sum.inr b))) ≤ c := by
  let e : ((A → Bool) × (B → Bool)) ≃ (A ⊕ B → Bool) :=
    { toFun := fun q x => Sum.casesOn x q.1 q.2
      invFun := fun ω => (fun a => ω (Sum.inl a), fun b => ω (Sum.inr b))
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ω => by funext x; cases x <;> rfl }
  rw [bernProb]
  refine (Fintype.sum_equiv e (fun q => if P q.1 q.2 then bernW p (e q) else 0)
    (fun ω => if P (fun a => ω (Sum.inl a)) (fun b => ω (Sum.inr b)) then bernW p ω else 0)
    (fun _ => rfl)).symm.trans_le ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hinner : ∀ ωB : B → Bool,
      (∑ ωA : A → Bool, if P ωA ωB then bernW p (e (ωA, ωB)) else 0) =
      bernW p ωB * bernProb p (fun ωA => P ωA ωB) := by
    intro ωB
    rw [bernProb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ωA _ => ?_
    have hw : bernW p (e (ωA, ωB)) = bernW p ωA * bernW p ωB := bernW_sum_split p (e (ωA, ωB))
    simp only [e, Equiv.coe_fn_mk] at hw ⊢
    split_ifs <;> linarith only [hw]
  calc ∑ ωB : B → Bool, ∑ ωA : A → Bool, (if P ωA ωB then bernW p (e (ωA, ωB)) else 0)
      = ∑ ωB : B → Bool, bernW p ωB * bernProb p (fun ωA => P ωA ωB) :=
        Finset.sum_congr rfl fun ωB _ => hinner ωB
    _ ≤ ∑ ωB : B → Bool, bernW p ωB * c :=
        Finset.sum_le_sum fun ωB _ => mul_le_mul_of_nonneg_left (hbound ωB) (bernW_nonneg hp0 hp1 ωB)
    _ = (∑ ωB : B → Bool, bernW p ωB) * c := (Finset.sum_mul _ _ _).symm
    _ = c := by rw [sum_bernW_eq_one, one_mul]

/-- Probability that every coordinate in `T : Finset X` is `false` is `(1 - p)^|T|`. -/
lemma bernProb_all_false {X : Type*} [Fintype X] [DecidableEq X] (p : ℝ) (T : Finset X) :
    bernProb p (fun ω : X → Bool => ∀ x ∈ T, ω x = false) = (1 - p) ^ T.card := by
  let g : X → Bool → ℝ := fun x b => if x ∈ T then (if b then 0 else 1) else 1
  have hprod : ∀ ω : X → Bool,
      (if ∀ x ∈ T, ω x = false then (1 : ℝ) else 0) = ∏ x : X, g x (ω x) := by
    intro ω
    by_cases hall : ∀ x ∈ T, ω x = false
    · rw [if_pos hall]; symm
      exact Finset.prod_eq_one fun x _ => by
        by_cases hx : x ∈ T
        · simp [g, hx, hall x hx]
        · simp [g, hx]
    · rw [if_neg hall]; push Not at hall
      rcases hall with ⟨x₀, hx₀T, hx₀f⟩
      have hx₀t : ω x₀ = true := by cases h : ω x₀ <;> simp_all
      symm; exact Finset.prod_eq_zero (Finset.mem_univ x₀) (by simp [g, hx₀T, hx₀t])
  have heq : bernProb p (fun ω : X → Bool => ∀ x ∈ T, ω x = false) =
      bernExp p (fun ω => ∏ x : X, g x (ω x)) := by
    simp only [bernProb, bernExp]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [← hprod ω]; split_ifs <;> ring
  rw [heq, bernExp_prod, ← Finset.prod_subset (Finset.subset_univ T)]
  · calc ∏ x ∈ T, (p * g x true + (1 - p) * g x false)
        = ∏ _x ∈ T, (1 - p) := Finset.prod_congr rfl fun x hx => by simp [g, hx]
      _ = (1 - p) ^ T.card := Finset.prod_const (1 - p)
  · intro x _ hxT; simp [g, hxT]

/-- Safe forward targets at stage `i : Fin s`: vertices `j > i` with `(i, j) ∈ F'` that share no
earlier common neighbor `r < i` in `ω`. Depends only on edges with left endpoint `< i`. -/
def safeSet {s : ℕ} (F' : Finset (EdgeIdx s)) (ω : EdgeIdx s → Bool) (i : Fin s) : Finset (Fin s) :=
  Finset.univ.filter fun j =>
    ∃ h : i < j, ⟨(i, j), h⟩ ∈ F' ∧
      ¬ ∃ r : Fin s, ∃ hri : r < i, ∃ hrj : r < j,
        ω ⟨(r, i), hri⟩ = true ∧ ω ⟨(r, j), hrj⟩ = true

lemma safeSet_congr {s : ℕ} (F' : Finset (EdgeIdx s)) {ω₁ ω₂ : EdgeIdx s → Bool} {i : Fin s}
    (h : ∀ e : EdgeIdx s, e.1.1 < i → ω₁ e = ω₂ e) :
    safeSet F' ω₁ i = safeSet F' ω₂ i := by
  ext j; simp only [safeSet, Finset.mem_filter, Finset.mem_univ, true_and]
  refine exists_congr fun hij => and_congr_right fun _ => not_congr ?_
  refine exists_congr fun r => exists_congr fun hri => exists_congr fun hrj => ?_
  rw [h ⟨(r, i), hri⟩ hri, h ⟨(r, j), hrj⟩ hri]

/-- Stage `i` fails to create a safe forward edge if every safe target `j ∈ safeSet F' ω i`
has `ω (i, j) = false`. -/
def stageFail {s : ℕ} (F' : Finset (EdgeIdx s)) (ω : EdgeIdx s → Bool) (i : Fin s) : Prop :=
  ∀ j ∈ safeSet F' ω i, ∀ h : i < j, ω ⟨(i, j), h⟩ = false

lemma stageFail_congr {s : ℕ} (F' : Finset (EdgeIdx s)) {ω₁ ω₂ : EdgeIdx s → Bool} {i : Fin s}
    (h : ∀ e : EdgeIdx s, e.1.1 ≤ i → ω₁ e = ω₂ e) :
    stageFail F' ω₁ i ↔ stageFail F' ω₂ i := by
  have hs : safeSet F' ω₁ i = safeSet F' ω₂ i :=
    safeSet_congr F' fun e he => h e (le_of_lt he)
  simp only [stageFail, hs]
  refine forall_congr' fun j => forall_congr' fun _ => forall_congr' fun hij => ?_
  rw [h ⟨(i, j), hij⟩ le_rfl]

/-- Normalized martingale factor at stage `i`: `((1 - p)^|safeSet i|)⁻¹` if stage `i` fails, else `0`. -/
noncomputable def stageFac {s : ℕ} (F' : Finset (EdgeIdx s)) (p : ℝ) (ω : EdgeIdx s → Bool) (i : Fin s) : ℝ :=
  if stageFail F' ω i then ((1 - p) ^ (safeSet F' ω i).card)⁻¹ else 0

lemma stageFac_congr {s : ℕ} (F' : Finset (EdgeIdx s)) (p : ℝ) {ω₁ ω₂ : EdgeIdx s → Bool} {i : Fin s}
    (h : ∀ e : EdgeIdx s, e.1.1 ≤ i → ω₁ e = ω₂ e) :
    stageFac F' p ω₁ i = stageFac F' p ω₂ i := by
  have hs := safeSet_congr F' (i := i) fun e he => h e (le_of_lt he)
  have hf := stageFail_congr F' (i := i) h
  simp only [stageFac, hs, hf]

lemma stageFac_nonneg {s : ℕ} (F' : Finset (EdgeIdx s)) {p : ℝ} (hp1 : p < 1)
    (ω : EdgeIdx s → Bool) (i : Fin s) : 0 ≤ stageFac F' p ω i := by
  simp only [stageFac]
  split_ifs
  · exact inv_nonneg.mpr (pow_nonneg (by linarith only [hp1]) _)
  · exact le_rfl

/-- Exact martingale expectation identity: exposing stages `i = 0, ..., s - 1` sequentially,
`E[∏_{i : Fin s} stageFac F' p ω i] = 1`. -/
lemma bernExp_stageFac_prod_eq_one {s : ℕ} (F' : Finset (EdgeIdx s)) {p : ℝ} (hp1 : p < 1) :
    bernExp p (fun ω : EdgeIdx s → Bool => ∏ i : Fin s, stageFac F' p ω i) = 1 := by
  have h1mp_pos : 0 < 1 - p := by linarith only [hp1]
  have hind : ∀ k : ℕ, k ≤ s →
      bernExp p (fun ω : EdgeIdx s → Bool => ∏ i : Fin s, if i.val < k then stageFac F' p ω i else 1) = 1 := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [Nat.not_lt_zero, ite_false, Finset.prod_const_one, bernExp, mul_one, sum_bernW_eq_one]
    | succ k ih =>
      intro hk
      let i₀ : Fin s := ⟨k, by omega⟩
      let L := {e : EdgeIdx s // e.1.1.val ≠ k}
      let R := {e : EdgeIdx s // e.1.1.val = k}
      let eSplit : EdgeIdx s ≃ L ⊕ R :=
        { toFun := fun e => if h : e.1.1.val = k then Sum.inr ⟨e, h⟩ else Sum.inl ⟨e, h⟩
          invFun := fun x => Sum.casesOn x Subtype.val Subtype.val
          left_inv := fun e => by dsimp only; split_ifs <;> rfl
          right_inv := fun x => by
            rcases x with ⟨e, he⟩ | ⟨e, he⟩ <;> simp [he] }
      let eProd : ((L → Bool) × (R → Bool)) ≃ (EdgeIdx s → Bool) :=
        { toFun := fun q e => if h : e.1.1.val = k then q.2 ⟨e, h⟩ else q.1 ⟨e, h⟩
          invFun := fun ω => (fun x => ω x.1, fun y => ω y.1)
          left_inv := fun ⟨ωL, ωR⟩ => by
            apply Prod.ext
            · funext ⟨e, he⟩; simp [he]
            · funext ⟨e, he⟩; simp [he]
          right_inv := fun ω => by funext e; dsimp only; split_ifs <;> rfl }
      have hw_split : ∀ (ωL : L → Bool) (ωR : R → Bool),
          bernW p (eProd (ωL, ωR)) = bernW p ωL * bernW p ωR := by
        intro ωL ωR
        simp only [bernW]
        have h1 : (∏ e : EdgeIdx s, if eProd (ωL, ωR) e then p else 1 - p) =
            ∏ x : L ⊕ R, if eProd (ωL, ωR) (eSplit.symm x) then p else 1 - p :=
          (Fintype.prod_equiv eSplit.symm _ _ fun _ => rfl).symm
        rw [h1, Fintype.prod_sum_type]
        congr 1
        · refine Finset.prod_congr rfl fun ⟨e, he⟩ _ => by simp [eSplit, eProd, he]
        · refine Finset.prod_congr rfl fun ⟨e, he⟩ _ => by simp [eSplit, eProd, he]
      -- Factor out the stage-`k` multiplier.
      have hprod_step : ∀ ω : EdgeIdx s → Bool,
          (∏ i : Fin s, if i.val < k + 1 then stageFac F' p ω i else 1) =
          (∏ i : Fin s, if i.val < k then stageFac F' p ω i else 1) * stageFac F' p ω i₀ := by
        intro ω
        have h1 : stageFac F' p ω i₀ =
            ∏ i : Fin s, if i = i₀ then stageFac F' p ω i else 1 := by
          rw [Finset.prod_ite_eq']; simp
        rw [h1, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        by_cases hlt : i.val < k
        · have hne : i ≠ i₀ := fun h => by subst h; simp [i₀] at hlt
          have hlt' : i.val < k + 1 := by omega
          simp [hlt, hlt', hne]
        · by_cases heq : i = i₀
          · subst heq; simp [i₀]
          · have hneq : i.val ≠ k := fun h => heq (Fin.ext h)
            have hnot : ¬ i.val < k + 1 := by omega
            simp [hlt, heq, hnot]
      let ωR₀ : R → Bool := fun _ => false
      have hPk_indep : ∀ (ωL : L → Bool) (ωR : R → Bool),
          (∏ i : Fin s, if i.val < k then stageFac F' p (eProd (ωL, ωR)) i else 1) =
          (∏ i : Fin s, if i.val < k then stageFac F' p (eProd (ωL, ωR₀)) i else 1) := by
        intro ωL ωR
        refine Finset.prod_congr rfl fun i _ => ?_
        split_ifs with hlt
        · refine stageFac_congr F' p fun e he => ?_
          have hne : e.1.1.val ≠ k := by
            have : e.1.1.val ≤ i.val := he
            omega
          simp [eProd, hne]
        · rfl
      have hsafe_indep : ∀ (ωL : L → Bool) (ωR : R → Bool),
          safeSet F' (eProd (ωL, ωR)) i₀ = safeSet F' (eProd (ωL, ωR₀)) i₀ := by
        intro ωL ωR
        refine safeSet_congr F' fun e he => ?_
        have hne : e.1.1.val ≠ k := by
          have : e.1.1.val < k := he
          omega
        simp [eProd, hne]
      have hinner_one : ∀ ωL : L → Bool,
          (∑ ωR : R → Bool, bernW p ωR * stageFac F' p (eProd (ωL, ωR)) i₀) = 1 := by
        intro ωL
        let S_L : Finset (Fin s) := safeSet F' (eProd (ωL, ωR₀)) i₀
        let T_R : Finset R := Finset.univ.filter fun e => e.1.1.2 ∈ S_L
        have hcard_eq : T_R.card = S_L.card := by
          refine Finset.card_bij (fun e _ => e.1.1.2) ?_ ?_ ?_
          · intro e he; exact (Finset.mem_filter.mp he).2
          · intro e₁ _ e₂ _ heq
            apply Subtype.ext; apply Subtype.ext; apply Prod.ext
            · exact Fin.ext (e₁.2.trans e₂.2.symm)
            · exact heq
          · intro j hj
            rcases (Finset.mem_filter.mp hj).2 with ⟨hij, _, _⟩
            exact ⟨⟨⟨(i₀, j), hij⟩, rfl⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩
        have hfail_iff : ∀ ωR : R → Bool,
            stageFail F' (eProd (ωL, ωR)) i₀ ↔ ∀ e ∈ T_R, ωR e = false := by
          intro ωR
          simp only [stageFail, hsafe_indep ωL ωR]
          constructor
          · intro h e he
            have hj : e.1.1.2 ∈ S_L := (Finset.mem_filter.mp he).2
            have he1 : e.1.1.1 = i₀ := Fin.ext e.2
            have hij : i₀ < e.1.1.2 := he1 ▸ e.1.2
            have hval := h e.1.1.2 hj hij
            have heq : (⟨(i₀, e.1.1.2), hij⟩ : EdgeIdx s) = e.1 := Subtype.ext (Prod.ext he1.symm rfl)
            have hstep : eProd (ωL, ωR) e.1 = ωR e := by
              simp only [eProd, Equiv.coe_fn_mk, dif_pos e.2]; rfl
            rw [heq, hstep] at hval; exact hval
          · intro h j hj hij
            have hmem : (⟨⟨(i₀, j), hij⟩, rfl⟩ : R) ∈ T_R :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
            have hval := h ⟨⟨(i₀, j), hij⟩, rfl⟩ hmem
            simpa [eProd, i₀] using hval
        have hsum_eq : (∑ ωR : R → Bool, bernW p ωR * stageFac F' p (eProd (ωL, ωR)) i₀) =
            ((1 - p) ^ S_L.card)⁻¹ * bernProb p (fun ωR : R → Bool => ∀ e ∈ T_R, ωR e = false) := by
          rw [bernProb, Finset.mul_sum]
          refine Finset.sum_congr rfl fun ωR _ => ?_
          simp only [stageFac, hsafe_indep ωL ωR, hfail_iff ωR]
          split_ifs <;> ring
        rw [hsum_eq, bernProb_all_false, hcard_eq, inv_mul_cancel₀ (pow_pos h1mp_pos _).ne']
      -- Evaluate `bernExp p P_{k+1}` via `eProd` and match to `bernExp p P_k = 1`.
      have hre1 : bernExp p (fun ω => ∏ i : Fin s, if i.val < k + 1 then stageFac F' p ω i else 1) =
          ∑ ωL : L → Bool, bernW p ωL *
            (∏ i : Fin s, if i.val < k then stageFac F' p (eProd (ωL, ωR₀)) i else 1) := by
        rw [bernExp]
        refine (Fintype.sum_equiv eProd
          (fun q => bernW p (eProd q) * ∏ i : Fin s, if i.val < k + 1 then stageFac F' p (eProd q) i else 1)
          (fun ω => bernW p ω * ∏ i : Fin s, if i.val < k + 1 then stageFac F' p ω i else 1)
          (fun _ => rfl)).symm.trans ?_
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun ωL _ => ?_
        calc ∑ ωR : R → Bool, bernW p (eProd (ωL, ωR)) *
                (∏ i : Fin s, if i.val < k + 1 then stageFac F' p (eProd (ωL, ωR)) i else 1)
            = ∑ ωR : R → Bool,
                (bernW p ωL * (∏ i : Fin s, if i.val < k then stageFac F' p (eProd (ωL, ωR₀)) i else 1)) *
                (bernW p ωR * stageFac F' p (eProd (ωL, ωR)) i₀) := by
              refine Finset.sum_congr rfl fun ωR _ => ?_
              rw [hw_split ωL ωR, hprod_step, hPk_indep ωL ωR]; ring
          _ = (bernW p ωL * (∏ i : Fin s, if i.val < k then stageFac F' p (eProd (ωL, ωR₀)) i else 1)) *
              (∑ ωR : R → Bool, bernW p ωR * stageFac F' p (eProd (ωL, ωR)) i₀) :=
              (Finset.mul_sum _ _ _).symm
          _ = bernW p ωL * (∏ i : Fin s, if i.val < k then stageFac F' p (eProd (ωL, ωR₀)) i else 1) := by
              rw [hinner_one ωL, mul_one]
      have hre0 : bernExp p (fun ω => ∏ i : Fin s, if i.val < k then stageFac F' p ω i else 1) =
          ∑ ωL : L → Bool, bernW p ωL *
            (∏ i : Fin s, if i.val < k then stageFac F' p (eProd (ωL, ωR₀)) i else 1) := by
        rw [bernExp]
        refine (Fintype.sum_equiv eProd
          (fun q => bernW p (eProd q) * ∏ i : Fin s, if i.val < k then stageFac F' p (eProd q) i else 1)
          (fun ω => bernW p ω * ∏ i : Fin s, if i.val < k then stageFac F' p ω i else 1)
          (fun _ => rfl)).symm.trans ?_
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun ωL _ => ?_
        calc ∑ ωR : R → Bool, bernW p (eProd (ωL, ωR)) *
                (∏ i : Fin s, if i.val < k then stageFac F' p (eProd (ωL, ωR)) i else 1)
            = ∑ ωR : R → Bool,
                (bernW p ωL * (∏ i : Fin s, if i.val < k then stageFac F' p (eProd (ωL, ωR₀)) i else 1)) *
                bernW p ωR := by
              refine Finset.sum_congr rfl fun ωR _ => ?_
              rw [hw_split ωL ωR, hPk_indep ωL ωR]; ring
          _ = (bernW p ωL * (∏ i : Fin s, if i.val < k then stageFac F' p (eProd (ωL, ωR₀)) i else 1)) *
              (∑ ωR : R → Bool, bernW p ωR) := (Finset.mul_sum _ _ _).symm
          _ = bernW p ωL * (∏ i : Fin s, if i.val < k then stageFac F' p (eProd (ωL, ωR₀)) i else 1) := by
              rw [sum_bernW_eq_one, mul_one]
      rw [hre1, ← hre0]
      exact ih (by omega)
  have hfull := hind s le_rfl
  simpa [Fin.isLt] using hfull

/-- Sequential-exposure survival bound: if no edge of `F'` survives `pruneTri (graphOf ω)` AND
the total number of safe forward targets is at least `M_safe`, that event has probability
at most `exp(-p * M_safe)`. -/
lemma seq_survival_bound {s : ℕ} (F' : Finset (EdgeIdx s)) {p M_safe : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    bernProb p (fun ω : EdgeIdx s → Bool =>
      (∀ e ∈ F', ¬ (pruneTri (graphOf ω)).Adj e.1.1 e.1.2) ∧
      M_safe ≤ (∑ i : Fin s, (safeSet F' ω i).card : ℝ)) ≤
      Real.exp (-p * M_safe) := by
  let Z : (EdgeIdx s → Bool) → ℝ := fun ω => ∏ i : Fin s, stageFac F' p ω i
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => Finset.prod_nonneg fun i _ => stageFac_nonneg F' hp1 ω i
  have himp : ∀ ω : EdgeIdx s → Bool,
      ((∀ e ∈ F', ¬ (pruneTri (graphOf ω)).Adj e.1.1 e.1.2) ∧
        M_safe ≤ (∑ i : Fin s, (safeSet F' ω i).card : ℝ)) →
      Real.exp (p * M_safe) ≤ Z ω := by
    intro ω ⟨hno_edge, hM_le⟩
    have hall_fail : ∀ i : Fin s, stageFail F' ω i := by
      intro i j hj hij
      rcases (Finset.mem_filter.mp hj).2 with ⟨hij', heF', hno_r⟩
      by_contra hnotf
      have htrue : ω ⟨(i, j), hij⟩ = true := by cases h : ω ⟨(i, j), hij⟩ <;> simp_all
      have hadj : (graphOf ω).Adj i j := by simp only [graphOf, dif_pos hij]; exact htrue
      have hprune : (pruneTri (graphOf ω)).Adj i j := by
        refine ⟨hadj, fun ⟨z, hz, hzi, hzj⟩ => hno_r ⟨z, ?_, ?_, ?_, ?_⟩⟩
        · have hmin : min i j = i := min_eq_left hij.le
          rw [hmin] at hz; exact hz
        · have hmin : min i j = i := min_eq_left hij.le
          rw [hmin] at hz; exact lt_trans hz hij
        · have hmin : min i j = i := min_eq_left hij.le
          have hzi' : z < i := by rwa [hmin] at hz
          simpa only [graphOf, dif_pos hzi'] using hzi
        · have hmin : min i j = i := min_eq_left hij.le
          have hzj' : z < j := lt_trans (by rwa [hmin] at hz) hij
          simpa only [graphOf, dif_pos hzj'] using hzj
      exact hno_edge ⟨(i, j), hij'⟩ heF' hprune
    have hZ_eq : Z ω = ((1 - p) ^ (∑ i : Fin s, (safeSet F' ω i).card))⁻¹ := by
      simp only [Z, stageFac]
      calc ∏ i : Fin s, (if stageFail F' ω i then ((1 - p) ^ (safeSet F' ω i).card)⁻¹ else 0)
          = ∏ i : Fin s, ((1 - p) ^ (safeSet F' ω i).card)⁻¹ :=
            Finset.prod_congr rfl fun i _ => if_pos (hall_fail i)
        _ = (∏ i : Fin s, (1 - p) ^ (safeSet F' ω i).card)⁻¹ := by rw [Finset.prod_inv_distrib]
        _ = ((1 - p) ^ (∑ i : Fin s, (safeSet F' ω i).card))⁻¹ := by rw [Finset.prod_pow_eq_pow_sum]
    rw [hZ_eq]
    have h1mp_pos : 0 < 1 - p := by linarith only [hp1]
    set N : ℕ := ∑ i : Fin s, (safeSet F' ω i).card
    have hM_N : M_safe ≤ (N : ℝ) := by simpa [N] using hM_le
    have h1 : (1 - p) ^ N ≤ Real.exp (-p * M_safe) := by
      have hbase : 1 - p ≤ Real.exp (-p) := by linarith only [Real.add_one_le_exp (-p)]
      calc (1 - p) ^ N ≤ (Real.exp (-p)) ^ N := pow_le_pow_left₀ h1mp_pos.le hbase N
        _ = Real.exp ((N : ℝ) * (-p)) := (Real.exp_nat_mul (-p) N).symm
        _ ≤ Real.exp (-p * M_safe) := Real.exp_le_exp.mpr (by nlinarith only [hp0, hM_N])
    have h2 : (Real.exp (-p * M_safe))⁻¹ ≤ ((1 - p) ^ N)⁻¹ :=
      inv_anti₀ (pow_pos h1mp_pos N) h1
    have h3 : Real.exp (p * M_safe) = (Real.exp (-p * M_safe))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rwa [h3]
  have h1 := bernProb_mono hp0.le hp1.le himp
  have hmk := bernProb_markov hp0.le hp1.le hZ0 (Real.exp_pos (p * M_safe))
  rw [bernExp_stageFac_prod_eq_one F' hp1] at hmk
  calc _ ≤ 1 / Real.exp (p * M_safe) := h1.trans hmk
    _ = Real.exp (-p * M_safe) := by rw [one_div, ← Real.exp_neg]; congr 1; ring

/-- Handshaking identity on `graphOf ω`: `∑ x, degIn (graphOf ω) univ x = 2 * |{e | ω e = true}|`. -/
lemma sum_degIn_graphOf {s : ℕ} (ω : EdgeIdx s → Bool) :
    ∑ x : Fin s, degIn (graphOf ω) Finset.univ x =
      2 * (Finset.univ.filter (fun e : EdgeIdx s => ω e = true)).card := by
  have hsum : ∑ x : Fin s, degIn (graphOf ω) Finset.univ x =
      ((Finset.univ ×ˢ Finset.univ : Finset (Fin s × Fin s)).filter
        (fun q => (graphOf ω).Adj q.1 q.2)).card := by
    simp only [degIn, Finset.card_filter, Finset.sum_product]
  rw [hsum]
  set P := (Finset.univ ×ˢ Finset.univ : Finset (Fin s × Fin s)).filter (fun q => (graphOf ω).Adj q.1 q.2)
  let P1 := P.filter (fun q => q.1 < q.2)
  let P2 := P.filter (fun q => q.2 < q.1)
  have hdisj : Disjoint P1 P2 := Finset.disjoint_left.mpr fun q h1 h2 =>
    lt_asymm (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
  have hunion : P1 ∪ P2 = P := by
    ext q; simp only [P1, P2, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hq
      have hne : q.1 ≠ q.2 := fun heq => (graphOf ω).loopless.irrefl q.1 (heq ▸ (Finset.mem_filter.mp hq).2)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨hq, hlt⟩
      · exact Or.inr ⟨hq, hgt⟩
  have h12 : P1.card = P2.card := by
    refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
    · intro q hq
      simp only [P1, P2, P, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hq ⊢
      exact ⟨(graphOf ω).symm.symm _ _ hq.1, hq.2⟩
    · intro p _ q _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro q hq
      simp only [P1, P2, P, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hq ⊢
      exact ⟨(q.2, q.1), ⟨(graphOf ω).symm.symm _ _ hq.1, hq.2⟩, rfl⟩
  have hP1 : P1.card = (Finset.univ.filter (fun e : EdgeIdx s => ω e = true)).card := by
    refine Finset.card_bij (fun q hq => ⟨q, (Finset.mem_filter.mp hq).2⟩) ?_ ?_ ?_
    · intro q hq
      have hlt : q.1 < q.2 := (Finset.mem_filter.mp hq).2
      have hadj : (graphOf ω).Adj q.1 q.2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
      simp only [graphOf, dif_pos hlt] at hadj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩
    · intro p _ q _ h; exact congrArg Subtype.val h
    · intro e he
      have htrue := (Finset.mem_filter.mp he).2
      refine ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩, e.2⟩, Subtype.ext rfl⟩
      simp only [graphOf, dif_pos e.2]; exact htrue
  rw [← hunion, Finset.card_union_of_disjoint hdisj, ← h12, hP1]; omega

/-- Deterministic lower bound on total safe targets:
`∑ i, |safeSet F' ω i| ≥ |F'| - 2 * D_max * E_max` when max degree `≤ D_max` and edges `≤ E_max`. -/
lemma sum_safeSet_ge {s : ℕ} (F' : Finset (EdgeIdx s)) (ω : EdgeIdx s → Bool)
    {D_max E_max : ℝ} (hD : 0 ≤ D_max)
    (hdeg : ∀ x : Fin s, (degIn (graphOf ω) Finset.univ x : ℝ) ≤ D_max)
    (hedges : ((Finset.univ.filter (fun e : EdgeIdx s => ω e = true)).card : ℝ) ≤ E_max) :
    (F'.card : ℝ) - 2 * D_max * E_max ≤ (∑ i : Fin s, (safeSet F' ω i).card : ℝ) := by
  let Safe := F'.filter (fun e => e.1.2 ∈ safeSet F' ω e.1.1)
  let Blocked := F'.filter (fun e => ¬ e.1.2 ∈ safeSet F' ω e.1.1)
  have hpart : F'.card = Safe.card + Blocked.card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
    congr 1; ext e; simp only [Finset.mem_union, Finset.mem_filter]; tauto
  have hSafe_eq : Safe.card = ∑ i : Fin s, (safeSet F' ω i).card := by
    have hfib := Finset.card_eq_sum_card_fiberwise (f := fun e : EdgeIdx s => e.1.1)
      (s := Safe) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    rw [hfib]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.card_bij (fun e _ => e.1.2) ?_ ?_ ?_
    · intro e he
      have h1 : e.1.2 ∈ safeSet F' ω e.1.1 := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
      have h2 : e.1.1 = i := (Finset.mem_filter.mp he).2
      rwa [h2] at h1
    · intro e₁ he₁ e₂ he₂ h2
      have h1 : e₁.1.1 = i := (Finset.mem_filter.mp he₁).2
      have h1' : e₂.1.1 = i := (Finset.mem_filter.mp he₂).2
      exact Subtype.ext (Prod.ext (h1.trans h1'.symm) h2)
    · intro j hj
      rcases (Finset.mem_filter.mp hj).2 with ⟨hij, heF', _⟩
      exact ⟨⟨(i, j), hij⟩, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨heF', hj⟩, rfl⟩, rfl⟩
  have hcov : Blocked ⊆ Finset.univ.biUnion (fun r : Fin s =>
      F'.filter (fun e => (graphOf ω).Adj r e.1.1 ∧ (graphOf ω).Adj r e.1.2)) := by
    intro e he
    have heF' : e ∈ F' := (Finset.mem_filter.mp he).1
    have hnot : e.1.2 ∉ safeSet F' ω e.1.1 := (Finset.mem_filter.mp he).2
    simp only [safeSet, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and] at hnot
    have hex := hnot e.2 heF'
    push Not at hex
    rcases hex with ⟨r, hri, hrj, h1, h2⟩
    refine Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, Finset.mem_filter.mpr ⟨heF', ?_, ?_⟩⟩
    · simp only [graphOf, dif_pos hri]; exact h1
    · simp only [graphOf, dif_pos hrj]; exact h2
  have hper_r : ∀ r : Fin s,
      (F'.filter (fun e => (graphOf ω).Adj r e.1.1 ∧ (graphOf ω).Adj r e.1.2)).card ≤
      (degIn (graphOf ω) Finset.univ r) ^ 2 := by
    intro r
    let Nbr := Finset.univ.filter (fun x : Fin s => (graphOf ω).Adj r x)
    have hle : (F'.filter (fun e => (graphOf ω).Adj r e.1.1 ∧ (graphOf ω).Adj r e.1.2)).card ≤
        (Nbr ×ˢ Nbr).card := by
      refine Finset.card_le_card_of_injOn (fun e : EdgeIdx s => e.1)
        (fun e he => by
          have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
          exact Finset.mem_coe.mpr (Finset.mem_product.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2.1⟩,
             Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2.2⟩⟩))
        (fun e₁ _ e₂ _ h => Subtype.ext h)
    simpa [Nbr, degIn, sq] using hle
  have hBlk_nat : Blocked.card ≤ ∑ r : Fin s, (degIn (graphOf ω) Finset.univ r) ^ 2 :=
    ((Finset.card_le_card hcov).trans Finset.card_biUnion_le).trans (Finset.sum_le_sum fun r _ => hper_r r)
  have hBlk_le : (Blocked.card : ℝ) ≤ 2 * D_max * E_max := by
    have h1 : (Blocked.card : ℝ) ≤ ∑ r : Fin s, (degIn (graphOf ω) Finset.univ r : ℝ) ^ 2 := by
      exact_mod_cast hBlk_nat
    have h2 : ∑ r : Fin s, (degIn (graphOf ω) Finset.univ r : ℝ) ^ 2 ≤
        D_max * ∑ r : Fin s, (degIn (graphOf ω) Finset.univ r : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun r _ => by
        have := hdeg r
        nlinarith only [this, Nat.cast_nonneg (α := ℝ) (degIn (graphOf ω) Finset.univ r)]
    have h3 : ∑ r : Fin s, (degIn (graphOf ω) Finset.univ r : ℝ) =
        2 * ((Finset.univ.filter (fun e : EdgeIdx s => ω e = true)).card : ℝ) := by
      exact_mod_cast sum_degIn_graphOf ω
    rw [h3] at h2
    have h4 : D_max * (2 * ((Finset.univ.filter (fun e : EdgeIdx s => ω e = true)).card : ℝ)) ≤
        2 * D_max * E_max := by nlinarith only [hD, hedges]
    linarith only [h1, h2, h4]
  have hpartR : (F'.card : ℝ) = (∑ i : Fin s, (safeSet F' ω i).card : ℝ) + (Blocked.card : ℝ) := by
    rw [hSafe_eq] at hpart; exact_mod_cast hpart
  linarith only [hpartR, hBlk_le]

/-- Equivalence splitting `EdgeIdx m` into internal edges inside `B` (indexed by `EdgeIdx s`
via the order isomorphism `B.orderIsoOfFin hB`) and all external edges. -/
def edgeSplitInt {m s : ℕ} (B : Finset (Fin m)) (hB : B.card = s) :
    EdgeIdx m ≃ EdgeIdx s ⊕ {e : EdgeIdx m // ¬ (e.1.1 ∈ B ∧ e.1.2 ∈ B)} :=
  let iso : Fin s ≃o {x : Fin m // x ∈ B} := B.orderIsoOfFin hB
  { toFun := fun e =>
      if h : e.1.1 ∈ B ∧ e.1.2 ∈ B then
        Sum.inl ⟨(iso.symm ⟨e.1.1, h.1⟩, iso.symm ⟨e.1.2, h.2⟩),
          iso.symm.strictMono (show (⟨e.1.1, h.1⟩ : {x // x ∈ B}) < ⟨e.1.2, h.2⟩ from e.2)⟩
      else Sum.inr ⟨e, h⟩
    invFun := fun x =>
      match x with
      | Sum.inl e => ⟨((iso e.1.1).1, (iso e.1.2).1), iso.strictMono e.2⟩
      | Sum.inr e => e.1
    left_inv := fun e => by
      dsimp only
      split_ifs with h
      · apply Subtype.ext; apply Prod.ext
        · exact congrArg Subtype.val (iso.apply_symm_apply ⟨e.1.1, h.1⟩)
        · exact congrArg Subtype.val (iso.apply_symm_apply ⟨e.1.2, h.2⟩)
      · rfl
    right_inv := fun x => by
      rcases x with e | ⟨e, he⟩
      · dsimp only
        have h1 : (iso e.1.1).1 ∈ B := (iso e.1.1).2
        have h2 : (iso e.1.2).1 ∈ B := (iso e.1.2).2
        rw [dif_pos ⟨h1, h2⟩]
        congr 1; apply Subtype.ext; apply Prod.ext
        · exact iso.symm_apply_apply e.1.1
        · exact iso.symm_apply_apply e.1.2
      · dsimp only; rw [dif_neg he] }

/-- Order-preservation transfer for triangle pruning: if `e : EdgeIdx s` survives `pruneTri`
inside `B`, and its endpoints in `B` share no common neighbor outside `B`, then the corresponding
edge survives `pruneTri` in the full graph on `Fin m`. -/
lemma pruneTri_of_int_and_no_ext {m s : ℕ} (B : Finset (Fin m)) (hB : B.card = s)
    (ω : EdgeIdx s ⊕ {e : EdgeIdx m // ¬ (e.1.1 ∈ B ∧ e.1.2 ∈ B)} → Bool)
    (e : EdgeIdx s) :
    let iso := B.orderIsoOfFin hB
    let ω_full : EdgeIdx m → Bool := ω ∘ edgeSplitInt B hB
    let ω_int : EdgeIdx s → Bool := fun e' => ω (Sum.inl e')
    (pruneTri (graphOf ω_int)).Adj e.1.1 e.1.2 →
    (¬ ∃ z ∈ Finset.univ \ B, (graphOf ω_full).Adj z (iso e.1.1).1 ∧ (graphOf ω_full).Adj z (iso e.1.2).1) →
    (pruneTri (graphOf ω_full)).Adj (iso e.1.1).1 (iso e.1.2).1 := by
  intro iso ω_full ω_int hprune hno_ext
  have hxy : (iso e.1.1).1 < (iso e.1.2).1 := iso.strictMono e.2
  have h1 : (graphOf ω_full).Adj (iso e.1.1).1 (iso e.1.2).1 := by
    have hint : ω_int e = true := by
      have hadj := hprune.1
      simpa only [graphOf, dif_pos e.2] using hadj
    have hsp : edgeSplitInt B hB ⟨((iso e.1.1).1, (iso e.1.2).1), hxy⟩ = Sum.inl e := by
      exact (edgeSplitInt B hB).right_inv (Sum.inl e)
    simp only [graphOf, dif_pos hxy, ω_full, Function.comp, hsp]
    exact hint
  refine ⟨h1, fun ⟨z, hz, hzx, hzy⟩ => ?_⟩
  have hzx_lt : z < (iso e.1.1).1 := by rwa [min_eq_left hxy.le] at hz
  have hzy_lt : z < (iso e.1.2).1 := lt_trans hzx_lt hxy
  by_cases hzB : z ∈ B
  · let r : Fin s := iso.symm ⟨z, hzB⟩
    have hr_val : (iso r).1 = z := congrArg Subtype.val (iso.apply_symm_apply ⟨z, hzB⟩)
    have hri : r < e.1.1 := by
      have : iso r < iso e.1.1 := by
        show (iso r).1 < (iso e.1.1).1; rw [hr_val]; exact hzx_lt
      exact iso.strictMono.lt_iff_lt.mp this
    have hrj : r < e.1.2 := lt_trans hri e.2
    have hri_adj : (graphOf ω_int).Adj r e.1.1 := by
      have hri' : (iso r).1 < (iso e.1.1).1 := iso.strictMono hri
      have hsp : edgeSplitInt B hB ⟨((iso r).1, (iso e.1.1).1), hri'⟩ = Sum.inl ⟨(r, e.1.1), hri⟩ :=
        (edgeSplitInt B hB).right_inv (Sum.inl ⟨(r, e.1.1), hri⟩)
      have hfull_eq : ω_full ⟨((iso r).1, (iso e.1.1).1), hri'⟩ = true := by
        have hzx' : (graphOf ω_full).Adj (iso r).1 (iso e.1.1).1 := by rwa [hr_val]
        simpa only [graphOf, dif_pos hri'] using hzx'
      simp only [graphOf, dif_pos hri, ω_int]
      simpa only [ω_full, Function.comp, hsp] using hfull_eq
    have hrj_adj : (graphOf ω_int).Adj r e.1.2 := by
      have hrj' : (iso r).1 < (iso e.1.2).1 := iso.strictMono hrj
      have hsp : edgeSplitInt B hB ⟨((iso r).1, (iso e.1.2).1), hrj'⟩ = Sum.inl ⟨(r, e.1.2), hrj⟩ :=
        (edgeSplitInt B hB).right_inv (Sum.inl ⟨(r, e.1.2), hrj⟩)
      have hfull_eq : ω_full ⟨((iso r).1, (iso e.1.2).1), hrj'⟩ = true := by
        have hzy' : (graphOf ω_full).Adj (iso r).1 (iso e.1.2).1 := by rwa [hr_val]
        simpa only [graphOf, dif_pos hrj'] using hzy'
      simp only [graphOf, dif_pos hrj, ω_int]
      simpa only [ω_full, Function.comp, hsp] using hfull_eq
    have hmin_r : r < min e.1.1 e.1.2 := by rwa [min_eq_left e.2.le]
    exact hprune.2 ⟨r, hmin_r, hri_adj, hrj_adj⟩
  · exact hno_ext ⟨z, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzB⟩, hzx, hzy⟩

/-- Cardinality of `EdgeIdx s` is `s * (s - 1) / 2` (equivalently `2 * |EdgeIdx s| = s * (s - 1)`). -/
lemma two_mul_card_edgeIdx (s : ℕ) : 2 * Fintype.card (EdgeIdx s) = s * (s - 1) := by
  have hoff : (Finset.univ : Finset (Fin s)).offDiag.card = s * (s - 1) := by
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin, Nat.mul_sub_one]
  let L1 := (Finset.univ : Finset (Fin s)).offDiag.filter (fun p => p.1 < p.2)
  let L2 := (Finset.univ : Finset (Fin s)).offDiag.filter (fun p => p.2 < p.1)
  have hdisj : Disjoint L1 L2 := Finset.disjoint_left.mpr fun p h1 h2 =>
    lt_asymm (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
  have hunion : L1 ∪ L2 = (Finset.univ : Finset (Fin s)).offDiag := by
    ext p; simp only [L1, L2, Finset.mem_union, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨hne, hlt⟩
      · exact Or.inr ⟨hne, hgt⟩
  have h12 : L1.card = L2.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      simp only [L1, L2, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and] at hp ⊢
      exact ⟨hp.1.symm, hp.2⟩
    · intro p _ q _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro q hq
      simp only [L1, L2, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and] at hq ⊢
      exact ⟨(q.2, q.1), ⟨hq.1.symm, hq.2⟩, rfl⟩
  have hL1 : L1.card = Fintype.card (EdgeIdx s) := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun p hp => ⟨p, (Finset.mem_filter.mp hp).2⟩) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro _ _ _ _ h; exact congrArg Subtype.val h
    · intro e _; exact ⟨e.1, Finset.mem_filter.mpr
        ⟨Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, e.2.ne⟩, e.2⟩, Subtype.ext rfl⟩
  rw [← hL1, ← hoff, ← hunion, Finset.card_union_of_disjoint hdisj, h12]; omega

/-- Blue independent-set bad event (intersected with the global max-degree bound on `ω_B`):
there exists an `s`-subset `I' ⊆ Fin n` on which `φ_B` is injective and which carries no `blue2Adj` edge. -/
def BadIndepBlue (n m s : ℕ) (p : ℝ) (ω_R ω_B : EdgeIdx m → Bool) (φ_R φ_B : Fin n → Fin m) : Prop :=
  (∀ x : Fin m, (degIn (graphOf ω_B) Finset.univ x : ℝ) ≤ 2 * ((m : ℝ) * p)) ∧
  ∃ I' ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
    Set.InjOn φ_B (I' : Set (Fin n)) ∧
    ∀ u ∈ I', ∀ v ∈ I', ¬ blue2Adj (graphOf ω_R) (graphOf ω_B) φ_R φ_B u v

/-- Master conditional bound on `BadIndepBlue` for a fixed good triple `(ω_R, φ_R, φ_B)`. -/
lemma bernProb_badIndepBlue_le {n m s t : ℕ} {p F_max : ℝ}
    (hm : 1 ≤ m) (hs : 16 ≤ s) (hp0 : 0 < p) (hp1 : p < 1) (hF : 0 < F_max)
    (hs_t : (s : ℝ) / F_max + 1 ≤ (t : ℝ))
    (ht_le : (t : ℝ) ≤ 2 * ((s : ℝ) / F_max))
    (hF_small : F_max ≤ (1 / 10 : ℝ) * (s : ℝ))
    (hmp2 : 4 * (m : ℝ) * p ^ 2 ≤ 1 / 20)
    (ω_R : EdgeIdx m → Bool) (φ_R φ_B : Fin n → Fin m)
    (hfiber : ∀ x : Fin m, ((Finset.univ.filter (fun v : Fin n => φ_R v = x)).card : ℝ) ≤ F_max)
    (hcodeg : ∀ A : Finset (Fin m), A.card ≤ t →
      ∑ z ∈ Finset.univ \ A, (degIn (graphOf ω_R) A z : ℝ) ^ 2 ≤ (1 / 1000 : ℝ) * (t : ℝ) ^ 2) :
    let L_B : ℝ := 20 * ((s : ℝ) * p)
    let D : ℝ := 2 * ((m : ℝ) * p)
    let T_B : ℝ := (1 / 20 : ℝ) * (s : ℝ) ^ 2
    let E₀ : ℝ := T_B / D
    let e₀ : ℕ := Nat.ceil E₀
    let u_max : ℕ := Nat.floor ((E₀ + D) / L_B)
    bernProb p (fun ω_B => BadIndepBlue n m s p ω_R ω_B φ_R φ_B) ≤
      (n.choose s : ℝ) *
        (Real.exp ((2 * (m : ℝ) * ((s : ℝ) * p + ((s : ℝ) * p) ^ 2) - T_B) / L_B ^ 2) +
         (∑ u ∈ Finset.Icc 1 u_max, (m : ℝ) ^ u * (Real.exp 1 * ((s : ℝ) * (u : ℝ)) * p / (e₀ : ℝ)) ^ e₀) +
         Real.exp (-((s : ℝ) ^ 2 * p) / 24) +
         Real.exp (-p * ((1 / 10 : ℝ) * (s : ℝ) ^ 2))) := by
  intro L_B D T_B E₀ e₀ u_max
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hs_pos : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr (by omega)
  have hLB_pos : 0 < L_B := by positivity
  have hD_pos : 0 < D := by positivity
  have hTB_pos : 0 < T_B := by positivity
  let Ssets := (Finset.univ : Finset (Fin n)).powersetCard s
  have hcov : ∀ ω_B : EdgeIdx m → Bool, BadIndepBlue n m s p ω_R ω_B φ_R φ_B →
      ∃ I' ∈ Ssets,
        (∀ x : Fin m, (degIn (graphOf ω_B) Finset.univ x : ℝ) ≤ D) ∧
        Set.InjOn φ_B (I' : Set (Fin n)) ∧
        ∀ u ∈ I', ∀ v ∈ I', ¬ blue2Adj (graphOf ω_R) (graphOf ω_B) φ_R φ_B u v := by
    intro ω_B ⟨hdeg, I', hI', hinj, hno⟩
    exact ⟨I', hI', hdeg, hinj, hno⟩
  have h1 := (bernProb_mono hp0.le hp1.le hcov).trans (bernProb_exists_le hp0.le hp1.le Ssets
    (fun I' ω_B => (∀ x : Fin m, (degIn (graphOf ω_B) Finset.univ x : ℝ) ≤ D) ∧
      Set.InjOn φ_B (I' : Set (Fin n)) ∧
      ∀ u ∈ I', ∀ v ∈ I', ¬ blue2Adj (graphOf ω_R) (graphOf ω_B) φ_R φ_B u v))
  set P_per : ℝ :=
    Real.exp ((2 * (m : ℝ) * ((s : ℝ) * p + ((s : ℝ) * p) ^ 2) - T_B) / L_B ^ 2) +
    (∑ u ∈ Finset.Icc 1 u_max, (m : ℝ) ^ u * (Real.exp 1 * ((s : ℝ) * (u : ℝ)) * p / (e₀ : ℝ)) ^ e₀) +
    Real.exp (-((s : ℝ) ^ 2 * p) / 24) +
    Real.exp (-p * ((1 / 10 : ℝ) * (s : ℝ) ^ 2))
  have hP_nn : 0 ≤ P_per := by
    refine add_nonneg (add_nonneg (add_nonneg (Real.exp_pos _).le ?_) (Real.exp_pos _).le) (Real.exp_pos _).le
    exact Finset.sum_nonneg fun _ _ => by positivity
  have hper : ∀ I' ∈ Ssets,
      bernProb p (fun ω_B : EdgeIdx m → Bool =>
        (∀ x : Fin m, (degIn (graphOf ω_B) Finset.univ x : ℝ) ≤ D) ∧
        Set.InjOn φ_B (I' : Set (Fin n)) ∧
        ∀ u ∈ I', ∀ v ∈ I', ¬ blue2Adj (graphOf ω_R) (graphOf ω_B) φ_R φ_B u v) ≤ P_per := by
    intro I' hI'
    have hI'c : I'.card = s := (Finset.mem_powersetCard.mp hI').2
    by_cases hinj : Set.InjOn φ_B (I' : Set (Fin n))
    · let B : Finset (Fin m) := I'.image φ_B
      have hB : B.card = s := by rw [Finset.card_image_of_injOn hinj, hI'c]
      let iso := B.orderIsoOfFin hB
      let RedGood : Finset (EdgeIdx m) := Finset.univ.filter (fun e =>
        ∃ u ∈ I', ∃ v ∈ I', φ_B u = e.1.1 ∧ φ_B v = e.1.2 ∧ ¬ pairBad (graphOf ω_R) φ_R u v)
      have hRG_card : (1 / 4 : ℝ) * (s : ℝ) ^ 2 ≤ (RedGood.card : ℝ) := by
        have h := card_redGood_pairs_ge hF (graphOf ω_R) φ_R φ_B hfiber hcodeg I' hinj
          (by rwa [hI'c]) (by rwa [hI'c]) (by rwa [hI'c]) (by omega)
        rwa [hI'c] at h
      let F_all : Finset (EdgeIdx s) := Finset.univ.filter (fun e =>
        (⟨((iso e.1.1).1, (iso e.1.2).1), iso.strictMono e.2⟩ : EdgeIdx m) ∈ RedGood)
      have hFall_card : F_all.card = RedGood.card := by
        refine Finset.card_bij (fun e _ => ⟨((iso e.1.1).1, (iso e.1.2).1), iso.strictMono e.2⟩) ?_ ?_ ?_
        · intro e he; exact (Finset.mem_filter.mp he).2
        · intro e₁ _ e₂ _ heq
          have h1 : iso e₁.1.1 = iso e₂.1.1 := Subtype.ext (congrArg (fun x : EdgeIdx m => x.1.1) heq)
          have h2 : iso e₁.1.2 = iso e₂.1.2 := Subtype.ext (congrArg (fun x : EdgeIdx m => x.1.2) heq)
          exact Subtype.ext (Prod.ext (iso.injective h1) (iso.injective h2))
        · intro e he
          rcases (Finset.mem_filter.mp he).2 with ⟨u, hu, v, hv, h1, h2, _⟩
          have he1B : e.1.1 ∈ B := Finset.mem_image.mpr ⟨u, hu, h1⟩
          have he2B : e.1.2 ∈ B := Finset.mem_image.mpr ⟨v, hv, h2⟩
          let i₁ := iso.symm ⟨e.1.1, he1B⟩
          let i₂ := iso.symm ⟨e.1.2, he2B⟩
          have hlt : i₁ < i₂ := iso.symm.strictMono (show (⟨e.1.1, he1B⟩ : {x // x ∈ B}) < ⟨e.1.2, he2B⟩ from e.2)
          have heq : (⟨((iso i₁).1, (iso i₂).1), iso.strictMono hlt⟩ : EdgeIdx m) = e := by
            apply Subtype.ext; apply Prod.ext
            · exact congrArg Subtype.val (iso.apply_symm_apply ⟨e.1.1, he1B⟩)
            · exact congrArg Subtype.val (iso.apply_symm_apply ⟨e.1.2, he2B⟩)
          refine ⟨⟨(i₁, i₂), hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, heq⟩
          rwa [heq]
      -- Split failure into: (1) ExtSmall, (2) ExtLarge, (3) ManyIntEdges, (4) GoodExt ∧ LowIntEdges ∧ NoBlue.
      let E_ext1 : (EdgeIdx m → Bool) → Prop := fun ω_B =>
        T_B ≤ ∑ z ∈ Finset.univ \ B,
          if (degIn (graphOf ω_B) B z : ℝ) ≤ L_B then (degIn (graphOf ω_B) B z : ℝ) ^ 2 else 0
      let E_ext2 : (EdgeIdx m → Bool) → Prop := fun ω_B =>
        (∀ z ∈ Finset.univ \ B, (degIn (graphOf ω_B) B z : ℝ) ≤ D) ∧
        T_B ≤ ∑ z ∈ Finset.univ \ B,
          if L_B ≤ (degIn (graphOf ω_B) B z : ℝ) then (degIn (graphOf ω_B) B z : ℝ) ^ 2 else 0
      let E_intE : (EdgeIdx m → Bool) → Prop := fun ω_B =>
        (s : ℝ) ^ 2 * p < ((Finset.univ.filter (fun e : EdgeIdx s =>
          ω_B ⟨((iso e.1.1).1, (iso e.1.2).1), iso.strictMono e.2⟩ = true)).card : ℝ)
      let E_seq : (EdgeIdx m → Bool) → Prop := fun ω_B =>
        (∀ x : Fin m, (degIn (graphOf ω_B) Finset.univ x : ℝ) ≤ D) ∧
        (∑ z ∈ Finset.univ \ B, (degIn (graphOf ω_B) B z : ℝ) ^ 2 ≤ (1 / 10 : ℝ) * (s : ℝ) ^ 2) ∧
        (((Finset.univ.filter (fun e : EdgeIdx s =>
          ω_B ⟨((iso e.1.1).1, (iso e.1.2).1), iso.strictMono e.2⟩ = true)).card : ℝ) ≤ (s : ℝ) ^ 2 * p) ∧
        (∀ e ∈ F_all, ¬ (pruneTri (graphOf ω_B)).Adj (iso e.1.1).1 (iso e.1.2).1)
      have hsplit4 : ∀ ω_B : EdgeIdx m → Bool,
          ((∀ x : Fin m, (degIn (graphOf ω_B) Finset.univ x : ℝ) ≤ D) ∧
           Set.InjOn φ_B (I' : Set (Fin n)) ∧
           ∀ u ∈ I', ∀ v ∈ I', ¬ blue2Adj (graphOf ω_R) (graphOf ω_B) φ_R φ_B u v) →
          E_ext1 ω_B ∨ E_ext2 ω_B ∨ E_intE ω_B ∨ E_seq ω_B := by
        intro ω_B ⟨hdeg, _, hno⟩
        have hdegB : ∀ z ∈ Finset.univ \ B, (degIn (graphOf ω_B) B z : ℝ) ≤ D := fun z _ => by
          have hle : degIn (graphOf ω_B) B z ≤ degIn (graphOf ω_B) Finset.univ z :=
            Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ B))
          exact (Nat.cast_le.mpr hle).trans (hdeg z)
        by_cases hsum_ext : (1 / 10 : ℝ) * (s : ℝ) ^ 2 < ∑ z ∈ Finset.univ \ B, (degIn (graphOf ω_B) B z : ℝ) ^ 2
        · have hdecomp : ∑ z ∈ Finset.univ \ B, (degIn (graphOf ω_B) B z : ℝ) ^ 2 ≤
              (∑ z ∈ Finset.univ \ B, if (degIn (graphOf ω_B) B z : ℝ) ≤ L_B then (degIn (graphOf ω_B) B z : ℝ) ^ 2 else 0) +
              (∑ z ∈ Finset.univ \ B, if L_B ≤ (degIn (graphOf ω_B) B z : ℝ) then (degIn (graphOf ω_B) B z : ℝ) ^ 2 else 0) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_le_sum fun z _ => ?_
            by_cases hle : (degIn (graphOf ω_B) B z : ℝ) ≤ L_B
            · rw [if_pos hle]
              have hnn : 0 ≤ (if L_B ≤ (degIn (graphOf ω_B) B z : ℝ) then (degIn (graphOf ω_B) B z : ℝ) ^ 2 else 0) := by
                split_ifs <;> positivity
              linarith only [hnn]
            · have hge : L_B ≤ (degIn (graphOf ω_B) B z : ℝ) := le_of_not_ge hle
              rw [if_neg hle, if_pos hge, zero_add]
          by_cases h1 : E_ext1 ω_B
          · exact Or.inl h1
          · refine Or.inr (Or.inl ⟨hdegB, ?_⟩)
            simp only [E_ext1, not_le] at h1
            have h2TB : 2 * T_B = (1 / 10 : ℝ) * (s : ℝ) ^ 2 := by simp only [T_B]; ring
            linarith only [hsum_ext, hdecomp, h1, h2TB]
        · push Not at hsum_ext
          by_cases h3 : E_intE ω_B
          · exact Or.inr (Or.inr (Or.inl h3))
          · simp only [E_intE, not_lt] at h3
            refine Or.inr (Or.inr (Or.inr ⟨hdeg, hsum_ext, h3, ?_⟩))
            intro e he hadj
            have heRG : (⟨((iso e.1.1).1, (iso e.1.2).1), iso.strictMono e.2⟩ : EdgeIdx m) ∈ RedGood :=
              (Finset.mem_filter.mp he).2
            rcases (Finset.mem_filter.mp heRG).2 with ⟨u, hu, v, hv, h1, h2, hnotbad⟩
            have hblue : blue2Adj (graphOf ω_R) (graphOf ω_B) φ_R φ_B u v := by
              refine ⟨?_, hnotbad⟩
              rw [h1, h2]; exact hadj
            exact hno u hu v hv hblue
      have hprob4 := (bernProb_mono hp0.le hp1.le hsplit4).trans
        ((bernProb_or_le hp0.le hp1.le _ _).trans (add_le_add le_rfl
          ((bernProb_or_le hp0.le hp1.le _ _).trans (add_le_add le_rfl
            (bernProb_or_le hp0.le hp1.le _ _)))))
      -- Bound 1: `E_ext1`
      have hb1 : bernProb p E_ext1 ≤
          Real.exp ((2 * (m : ℝ) * ((s : ℝ) * p + ((s : ℝ) * p) ^ 2) - T_B) / L_B ^ 2) := by
        have h := bernProb_degOut_sq_small hp0.le hp1.le hLB_pos (T₁ := T_B) B
        rwa [hB] at h
      -- Bound 2: `E_ext2`
      have hb2 : bernProb p E_ext2 ≤
          ∑ u ∈ Finset.Icc 1 u_max, (m : ℝ) ^ u * (Real.exp 1 * ((s : ℝ) * (u : ℝ)) * p / (e₀ : ℝ)) ^ e₀ := by
        have h := bernProb_degOut_sq_large hp0.le hp1.le hLB_pos hD_pos hTB_pos B
        rwa [hB] at h
      -- Bound 3: `E_intE` via `edgeSplitInt B hB` and `bernProb_binom_ge_two_mul`
      have hb3 : bernProb p E_intE ≤ Real.exp (-((s : ℝ) ^ 2 * p) / 24) := by
        let eS := (edgeSplitInt B hB).symm
        rw [bernProb_equiv eS p]
        have hsymm : eS.symm = edgeSplitInt B hB := Equiv.symm_symm _
        simp_rw [hsymm]
        have hrew : ∀ ω : (EdgeIdx s ⊕ {e : EdgeIdx m // ¬ (e.1.1 ∈ B ∧ e.1.2 ∈ B)}) → Bool,
            E_intE (ω ∘ edgeSplitInt B hB) ↔
            (s : ℝ) ^ 2 * p < ((Finset.univ.filter (fun e : EdgeIdx s => ω (Sum.inl e) = true)).card : ℝ) := by
          intro ω
          simp only [E_intE, Function.comp]
          have hpt : ∀ e : EdgeIdx s,
              edgeSplitInt B hB ⟨((iso e.1.1).1, (iso e.1.2).1), iso.strictMono e.2⟩ = Sum.inl e :=
            fun e => (edgeSplitInt B hB).right_inv (Sum.inl e)
          simp_rw [hpt]
        simp_rw [hrew]
        refine (bernProb_inl p (fun ω_int : EdgeIdx s → Bool =>
          (s : ℝ) ^ 2 * p < ((Finset.univ.filter (fun e : EdgeIdx s => ω_int e = true)).card : ℝ))).trans_le ?_
        have hcard_e : 2 * ((Finset.univ : Finset (EdgeIdx s)).card : ℝ) = (s : ℝ) * ((s : ℝ) - 1) := by
          have h2 := two_mul_card_edgeIdx s
          have hsub1 : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ s)]; simp
          have hcast : (2 * Fintype.card (EdgeIdx s) : ℝ) = ((s * (s - 1) : ℕ) : ℝ) := by exact_mod_cast h2
          simpa [Finset.card_univ, Nat.cast_mul, hsub1] using hcast
        have hmono : bernProb p (fun ω_int : EdgeIdx s → Bool =>
            (s : ℝ) ^ 2 * p < ((Finset.univ.filter (fun e : EdgeIdx s => ω_int e = true)).card : ℝ)) ≤
            bernProb p (fun ω_int : EdgeIdx s → Bool =>
              2 * (((Finset.univ : Finset (EdgeIdx s)).card : ℝ) * p) ≤
              ((Finset.univ.filter (fun e : EdgeIdx s => ω_int e = true)).card : ℝ)) := by
          refine bernProb_mono hp0.le hp1.le fun ω_int hω => ?_
          have hle : 2 * (((Finset.univ : Finset (EdgeIdx s)).card : ℝ) * p) ≤ (s : ℝ) ^ 2 * p := by
            have h1 : 2 * ((Finset.univ : Finset (EdgeIdx s)).card : ℝ) ≤ (s : ℝ) ^ 2 := by
              nlinarith only [hcard_e, hs_pos]
            nlinarith only [h1, hp0]
          exact hle.trans hω.le
        have hch := bernProb_binom_ge_two_mul hp0.le hp1.le (Finset.univ : Finset (EdgeIdx s))
        have hexp_le : Real.exp (-(((Finset.univ : Finset (EdgeIdx s)).card : ℝ) * p) / 6) ≤
            Real.exp (-((s : ℝ) ^ 2 * p) / 24) := by
          refine Real.exp_le_exp.mpr ?_
          have hs16 : (16 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
          have hcard_ge : (1 / 4 : ℝ) * (s : ℝ) ^ 2 ≤ ((Finset.univ : Finset (EdgeIdx s)).card : ℝ) := by
            nlinarith only [hcard_e, hs16]
          nlinarith only [hcard_ge, hp0]
        exact (hmono.trans hch).trans hexp_le
      -- Bound 4: `E_seq` by conditioning on `ω_ext` via `edgeSplitInt B hB` + `seq_survival_bound`!
      have hb4 : bernProb p E_seq ≤ Real.exp (-p * ((1 / 10 : ℝ) * (s : ℝ) ^ 2)) := by
        let eS := (edgeSplitInt B hB).symm
        rw [bernProb_equiv eS p]
        have hsymm : eS.symm = edgeSplitInt B hB := Equiv.symm_symm _
        simp_rw [hsymm]
        let Ext := {e : EdgeIdx m // ¬ (e.1.1 ∈ B ∧ e.1.2 ∈ B)}
        -- Reconstruct `ω_full` from `(ω_int, ω_ext)` via `Sum.casesOn`.
        let mkFull : (EdgeIdx s → Bool) → (Ext → Bool) → (EdgeIdx m → Bool) :=
          fun ω_int ω_ext e => Sum.casesOn (edgeSplitInt B hB e) ω_int ω_ext
        have hmk_eq : ∀ ω : EdgeIdx s ⊕ Ext → Bool,
            ω ∘ edgeSplitInt B hB = mkFull (fun a => ω (Sum.inl a)) (fun b => ω (Sum.inr b)) := by
          intro ω; funext e; simp only [Function.comp, mkFull]
          cases edgeSplitInt B hB e <;> rfl
        simp_rw [hmk_eq]
        refine bernProb_sum_cond_le hp0.le hp1.le (fun ω_int ω_ext => E_seq (mkFull ω_int ω_ext)) fun ω_ext => ?_
        -- Notice `degIn (graphOf (mkFull ω_int ω_ext)) B z` for `z ∉ B` depends ONLY on `ω_ext`!
        let ω_int0 : EdgeIdx s → Bool := fun _ => false
        let ω_ref : EdgeIdx m → Bool := mkFull ω_int0 ω_ext
        have hfull_ext : ∀ (ω_int : EdgeIdx s → Bool) (z : Fin m) (x : Fin m),
            z ∉ B → ((graphOf (mkFull ω_int ω_ext)).Adj z x ↔ (graphOf ω_ref).Adj z x) := by
          intro ω_int z x hzB
          simp only [graphOf]
          have hval : ∀ e : EdgeIdx m, (e.1.1 ∉ B ∨ e.1.2 ∉ B) → mkFull ω_int ω_ext e = ω_ref e := by
            intro e he
            have hnot : ¬ (e.1.1 ∈ B ∧ e.1.2 ∈ B) := by tauto
            have hsp : edgeSplitInt B hB e = Sum.inr ⟨e, hnot⟩ := by
              simp only [edgeSplitInt, Equiv.coe_fn_mk, dif_neg hnot]
            simp only [ω_ref, mkFull, hsp]
          split_ifs with h1 h2
          · rw [hval ⟨(z, x), h1⟩ (Or.inl hzB)]
          · rw [hval ⟨(x, z), h2⟩ (Or.inr hzB)]
          · rfl
        have hdeg_ext_eq : ∀ (ω_int : EdgeIdx s → Bool) (z : Fin m), z ∉ B →
            degIn (graphOf (mkFull ω_int ω_ext)) B z = degIn (graphOf ω_ref) B z := by
          intro ω_int z hzB
          unfold degIn; congr 1; ext x
          simp only [Finset.mem_filter, hfull_ext ω_int z x hzB]
        by_cases hext_ok : ∑ z ∈ Finset.univ \ B, (degIn (graphOf ω_ref) B z : ℝ) ^ 2 ≤ (1 / 10 : ℝ) * (s : ℝ) ^ 2
        · -- Filter `F_all` to pairs `F'` with NO external common neighbor in `ω_ref`.
          let F' : Finset (EdgeIdx s) := F_all.filter fun e =>
            ¬ ∃ z ∈ Finset.univ \ B, (graphOf ω_ref).Adj z (iso e.1.1).1 ∧ (graphOf ω_ref).Adj z (iso e.1.2).1
          let ExtBlk : Finset (EdgeIdx s) := F_all.filter fun e =>
            ∃ z ∈ Finset.univ \ B, (graphOf ω_ref).Adj z (iso e.1.1).1 ∧ (graphOf ω_ref).Adj z (iso e.1.2).1
          have hpart_ext : F_all.card = F'.card + ExtBlk.card := by
            rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h1 h2)]
            congr 1; ext e; simp only [Finset.mem_union, Finset.mem_filter]; tauto
          have hExtBlk_le : (ExtBlk.card : ℝ) ≤ (1 / 10 : ℝ) * (s : ℝ) ^ 2 := by
            have hcov_ext : ExtBlk ⊆ (Finset.univ \ B).biUnion fun z =>
                F_all.filter (fun e => (graphOf ω_ref).Adj z (iso e.1.1).1 ∧ (graphOf ω_ref).Adj z (iso e.1.2).1) := by
              intro e he
              have heF : e ∈ F_all := (Finset.mem_filter.mp he).1
              rcases (Finset.mem_filter.mp he).2 with ⟨z, hz, h1, h2⟩
              exact Finset.mem_biUnion.mpr ⟨z, hz, Finset.mem_filter.mpr ⟨heF, h1, h2⟩⟩
            have hper_z : ∀ z ∈ Finset.univ \ B,
                (F_all.filter (fun e => (graphOf ω_ref).Adj z (iso e.1.1).1 ∧ (graphOf ω_ref).Adj z (iso e.1.2).1)).card ≤
                (degIn (graphOf ω_ref) B z) ^ 2 := by
              intro z _
              let Nbr := B.filter (fun x => (graphOf ω_ref).Adj z x)
              have hle : (F_all.filter (fun e =>
                  (graphOf ω_ref).Adj z (iso e.1.1).1 ∧ (graphOf ω_ref).Adj z (iso e.1.2).1)).card ≤
                  (Nbr ×ˢ Nbr).card := by
                refine Finset.card_le_card_of_injOn (fun e : EdgeIdx s => ((iso e.1.1).1, (iso e.1.2).1))
                  (fun e he => by
                    have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
                    exact Finset.mem_coe.mpr (Finset.mem_product.mpr
                      ⟨Finset.mem_filter.mpr ⟨(iso e.1.1).2, h2.1⟩,
                       Finset.mem_filter.mpr ⟨(iso e.1.2).2, h2.2⟩⟩))
                  (fun e₁ _ e₂ _ h => by
                    have h1 : iso e₁.1.1 = iso e₂.1.1 := Subtype.ext (congrArg Prod.fst h)
                    have h2 : iso e₁.1.2 = iso e₂.1.2 := Subtype.ext (congrArg Prod.snd h)
                    exact Subtype.ext (Prod.ext (iso.injective h1) (iso.injective h2)))
              simpa [Nbr, degIn, sq] using hle
            have hnat : ExtBlk.card ≤ ∑ z ∈ Finset.univ \ B, (degIn (graphOf ω_ref) B z) ^ 2 :=
              ((Finset.card_le_card hcov_ext).trans Finset.card_biUnion_le).trans (Finset.sum_le_sum hper_z)
            have hR : (ExtBlk.card : ℝ) ≤ ∑ z ∈ Finset.univ \ B, (degIn (graphOf ω_ref) B z : ℝ) ^ 2 := by
              exact_mod_cast hnat
            exact hR.trans hext_ok
          have hF'_ge : (3 / 20 : ℝ) * (s : ℝ) ^ 2 ≤ (F'.card : ℝ) := by
            have hpartR : (F_all.card : ℝ) = (F'.card : ℝ) + (ExtBlk.card : ℝ) := by exact_mod_cast hpart_ext
            have hFall_ge : (1 / 4 : ℝ) * (s : ℝ) ^ 2 ≤ (F_all.card : ℝ) := by rw [hFall_card]; exact hRG_card
            linarith only [hpartR, hFall_ge, hExtBlk_le]
          -- Show `E_seq (mkFull ω_int ω_ext)` implies the sequential survival event on `F'`!
          have himp_seq : ∀ ω_int : EdgeIdx s → Bool, E_seq (mkFull ω_int ω_ext) →
              (∀ e ∈ F', ¬ (pruneTri (graphOf ω_int)).Adj e.1.1 e.1.2) ∧
              (1 / 10 : ℝ) * (s : ℝ) ^ 2 ≤ (∑ i : Fin s, (safeSet F' ω_int i).card : ℝ) := by
            intro ω_int ⟨hdeg_all, _, hedges_all, hno_prune⟩
            constructor
            · intro e he hpr
              have heF : e ∈ F_all := (Finset.mem_filter.mp he).1
              have hno_ext_ref := (Finset.mem_filter.mp he).2
              let ω_sum : EdgeIdx s ⊕ Ext → Bool := fun x => Sum.casesOn x ω_int ω_ext
              have hmk_sum : ω_sum ∘ edgeSplitInt B hB = mkFull ω_int ω_ext := rfl
              have hno_ext_full : ¬ ∃ z ∈ Finset.univ \ B,
                  (graphOf (ω_sum ∘ edgeSplitInt B hB)).Adj z (iso e.1.1).1 ∧
                  (graphOf (ω_sum ∘ edgeSplitInt B hB)).Adj z (iso e.1.2).1 := by
                rintro ⟨z, hz, h1, h2⟩
                have hzB : z ∉ B := (Finset.mem_sdiff.mp hz).2
                rw [hmk_sum, hfull_ext ω_int z (iso e.1.1).1 hzB] at h1
                rw [hmk_sum, hfull_ext ω_int z (iso e.1.2).1 hzB] at h2
                exact hno_ext_ref ⟨z, hz, h1, h2⟩
              have hfull_pr := pruneTri_of_int_and_no_ext B hB ω_sum e hpr hno_ext_full
              exact hno_prune e heF hfull_pr
            · have hdeg_int : ∀ i : Fin s, (degIn (graphOf ω_int) Finset.univ i : ℝ) ≤ D := by
                intro i
                have hle : degIn (graphOf ω_int) Finset.univ i ≤ degIn (graphOf (mkFull ω_int ω_ext)) Finset.univ (iso i).1 := by
                  unfold degIn
                  refine Finset.card_le_card_of_injOn (fun j : Fin s => (iso j).1)
                    (fun j hj => by
                      have hadj : (graphOf ω_int).Adj i j := (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
                      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
                      simp only [graphOf] at hadj ⊢
                      by_cases hlt : i < j
                      · rw [dif_pos hlt] at hadj
                        have hlt' : (iso i).1 < (iso j).1 := iso.strictMono hlt
                        rw [dif_pos hlt']
                        have hsp : edgeSplitInt B hB ⟨((iso i).1, (iso j).1), hlt'⟩ = Sum.inl ⟨(i, j), hlt⟩ :=
                          (edgeSplitInt B hB).right_inv (Sum.inl ⟨(i, j), hlt⟩)
                        simpa only [mkFull, hsp] using hadj
                      · by_cases hgt : j < i
                        · rw [dif_neg hlt, dif_pos hgt] at hadj
                          have hgt' : (iso j).1 < (iso i).1 := iso.strictMono hgt
                          have hnot' : ¬ (iso i).1 < (iso j).1 := lt_asymm hgt'
                          rw [dif_neg hnot', dif_pos hgt']
                          have hsp : edgeSplitInt B hB ⟨((iso j).1, (iso i).1), hgt'⟩ = Sum.inl ⟨(j, i), hgt⟩ :=
                            (edgeSplitInt B hB).right_inv (Sum.inl ⟨(j, i), hgt⟩)
                          simpa only [mkFull, hsp] using hadj
                        · rw [dif_neg hlt, dif_neg hgt] at hadj; exact False.elim hadj)
                    (fun j₁ _ j₂ _ h => iso.injective (Subtype.ext h))
                exact (Nat.cast_le.mpr hle).trans (hdeg_all (iso i).1)
              have hedges_int : ((Finset.univ.filter (fun e : EdgeIdx s => ω_int e = true)).card : ℝ) ≤ (s : ℝ) ^ 2 * p := by
                have hpt : ∀ e : EdgeIdx s,
                    mkFull ω_int ω_ext ⟨((iso e.1.1).1, (iso e.1.2).1), iso.strictMono e.2⟩ = ω_int e := fun e => by
                  have hsp : edgeSplitInt B hB ⟨((iso e.1.1).1, (iso e.1.2).1), iso.strictMono e.2⟩ = Sum.inl e :=
                    (edgeSplitInt B hB).right_inv (Sum.inl e)
                  simp only [mkFull, hsp]
                simp_rw [hpt] at hedges_all
                exact hedges_all
              have hsafe_ge := sum_safeSet_ge F' ω_int hD_pos.le hdeg_int hedges_int
              have hloss : 2 * D * ((s : ℝ) ^ 2 * p) ≤ (1 / 20 : ℝ) * (s : ℝ) ^ 2 := by
                have heq : 2 * D * ((s : ℝ) ^ 2 * p) = (4 * (m : ℝ) * p ^ 2) * (s : ℝ) ^ 2 := by
                  simp only [D]; ring
                rw [heq]
                exact mul_le_mul_of_nonneg_right hmp2 (sq_nonneg _)
              linarith only [hF'_ge, hsafe_ge, hloss]
          exact (bernProb_mono hp0.le hp1.le himp_seq).trans (seq_survival_bound F' hp0 hp1)
        · -- If `ω_ext` fails the external degree-square bound, then `E_seq (mkFull ω_int ω_ext)` is FALSE!
          have hfalse : ∀ ω_int : EdgeIdx s → Bool, ¬ E_seq (mkFull ω_int ω_ext) := by
            intro ω_int ⟨_, hsum, _, _⟩
            have heq : ∑ z ∈ Finset.univ \ B, (degIn (graphOf (mkFull ω_int ω_ext)) B z : ℝ) ^ 2 =
                ∑ z ∈ Finset.univ \ B, (degIn (graphOf ω_ref) B z : ℝ) ^ 2 :=
              Finset.sum_congr rfl fun z hz => by
                rw [hdeg_ext_eq ω_int z (Finset.mem_sdiff.mp hz).2]
            rw [heq] at hsum; exact hext_ok hsum
          have hzero : bernProb p (fun ω_int => E_seq (mkFull ω_int ω_ext)) = 0 := by
            simp only [bernProb, hfalse, ite_false, Finset.sum_const_zero]
          rw [hzero]; exact (Real.exp_pos _).le
      linarith only [hprob4, hb1, hb2, hb3, hb4]
    · -- If `φ_B` is not injective on `I'`, the event is empty (probability `0 ≤ P_per`).
      have hzero : bernProb p (fun ω_B : EdgeIdx m → Bool =>
          (∀ x : Fin m, (degIn (graphOf ω_B) Finset.univ x : ℝ) ≤ D) ∧
          Set.InjOn φ_B (I' : Set (Fin n)) ∧
          ∀ u ∈ I', ∀ v ∈ I', ¬ blue2Adj (graphOf ω_R) (graphOf ω_B) φ_R φ_B u v) = 0 := by
        simp only [bernProb]
        exact Finset.sum_eq_zero fun ω_B _ => if_neg fun h => hinj h.2.1
      rw [hzero]; exact hP_nn
  calc _ ≤ ∑ _I' ∈ Ssets, P_per := h1.trans (Finset.sum_le_sum hper)
    _ = (Ssets.card : ℝ) * P_per := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = (n.choose s : ℝ) * P_per := by
        simp only [Ssets, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

end IndepSetBound

/- ### Section 5: Shearer's Upper Bound and Greedy Colouring Reduction -/

section ShearerUpper

namespace Shearer

open Real intervalIntegral MeasureTheory Set

noncomputable def f (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, (1 - t) / (1 + (x - 1) * t)
noncomputable def g (x : ℝ) : ℝ := -∫ t in (0 : ℝ)..1, t * (1 - t) / (1 + (x - 1) * t) ^ 2

lemma den_pos {x t : ℝ} (hx : 0 < x) (ht : t ∈ uIcc (0 : ℝ) 1) : 0 < 1 + (x - 1) * t := by
  rw [Set.uIcc_of_le zero_le_one] at ht
  obtain ⟨h0, h1⟩ := ht
  rcases eq_or_lt_of_le h0 with rfl | h
  · norm_num
  · nlinarith [mul_pos hx h]

lemma int_A {x : ℝ} (hx : 0 < x) :
    IntervalIntegrable (fun t : ℝ => (1 - t) / (1 + (x - 1) * t)) volume 0 1 :=
  ContinuousOn.intervalIntegrable (ContinuousOn.div (by fun_prop) (by fun_prop)
    (fun t ht => (den_pos hx ht).ne'))

lemma int_B {x : ℝ} (hx : 0 < x) :
    IntervalIntegrable (fun t : ℝ => t * (1 - t) / (1 + (x - 1) * t) ^ 2) volume 0 1 :=
  ContinuousOn.intervalIntegrable (ContinuousOn.div (by fun_prop) (by fun_prop)
    (fun t ht => (pow_pos (den_pos hx ht) 2).ne'))

lemma g_nonpos {x : ℝ} (hx : 0 < x) : g x ≤ 0 := by
  unfold g
  rw [neg_nonpos]
  apply intervalIntegral.integral_nonneg zero_le_one
  intro t ht
  have := den_pos hx (by rwa [Set.uIcc_of_le zero_le_one])
  apply div_nonneg _ (by positivity)
  exact mul_nonneg ht.1 (by linarith [ht.2])

lemma tangent {x d : ℝ} (hx : 0 < x) (hd : 0 < d) : f d + g d * (x - d) ≤ f x := by
  have e : f d + g d * (x - d) = ∫ t in (0 : ℝ)..1,
      ((1 - t) / (1 + (d - 1) * t) - (x - d) * (t * (1 - t) / (1 + (d - 1) * t) ^ 2)) := by
    rw [intervalIntegral.integral_sub (int_A hd) ((int_B hd).const_mul _),
      intervalIntegral.integral_const_mul]
    unfold f g; ring
  rw [e]
  apply intervalIntegral.integral_mono_on zero_le_one
    ((int_A hd).sub ((int_B hd).const_mul _)) (int_A hx)
  intro t ht
  have ha := den_pos hd (by rwa [Set.uIcc_of_le zero_le_one])
  have hb := den_pos hx (by rwa [Set.uIcc_of_le zero_le_one])
  set a := 1 + (d - 1) * t
  set b := 1 + (x - 1) * t
  have hc : 0 ≤ 1 - t := by linarith [ht.2]
  have hba : (x - d) * t = b - a := by simp only [a, b]; ring
  have key : (1 - t) / b - ((1 - t) / a - (x - d) * (t * (1 - t) / a ^ 2)) =
      (1 - t) * (b - a) ^ 2 / (a ^ 2 * b) := by
    rw [← hba]; field_simp; simp only [a, b]; ring
  have : 0 ≤ (1 - t) * (b - a) ^ 2 / (a ^ 2 * b) := by positivity
  linarith

lemma ode {d : ℝ} (hd : 0 < d) : (1 + d) * f d - g d * (d - d ^ 2) = 1 := by
  have e : (1 + d) * f d - g d * (d - d ^ 2) = ∫ t in (0 : ℝ)..1,
      ((1 + d) * ((1 - t) / (1 + (d - 1) * t)) +
        (d - d ^ 2) * (t * (1 - t) / (1 + (d - 1) * t) ^ 2)) := by
    rw [intervalIntegral.integral_add ((int_A hd).const_mul _) ((int_B hd).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    unfold f g; ring
  rw [e]
  have hF : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t => t * (d + 1 - t) / (1 + (d - 1) * t))
      ((1 + d) * ((1 - t) / (1 + (d - 1) * t)) +
        (d - d ^ 2) * (t * (1 - t) / (1 + (d - 1) * t) ^ 2)) t := by
    intro t ht
    have hv := den_pos hd ht
    have h1 : HasDerivAt (fun t : ℝ => t * (d + 1 - t)) (1 * (d + 1 - t) + t * (0 - 1)) t :=
      (hasDerivAt_id t).mul ((hasDerivAt_const t (d + 1)).sub (hasDerivAt_id t))
    have h2 : HasDerivAt (fun t : ℝ => 1 + (d - 1) * t) (0 + (d - 1) * 1) t :=
      (hasDerivAt_const t 1).add ((hasDerivAt_id t).const_mul (d - 1))
    have hv' := hv.ne'
    refine (h1.div h2 hv').congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (((int_A hd).const_mul _).add ((int_B hd).const_mul _))]
  have : (1 : ℝ) + (d - 1) * 1 = d := by ring
  rw [this]; field_simp; ring

lemma at_zero {d : ℝ} (hd : 0 < d) : f d - d * g d ≤ 1 := by
  have e : f d - d * g d = ∫ t in (0 : ℝ)..1,
      ((1 - t) / (1 + (d - 1) * t) + d * (t * (1 - t) / (1 + (d - 1) * t) ^ 2)) := by
    rw [intervalIntegral.integral_add (int_A hd) ((int_B hd).const_mul _),
      intervalIntegral.integral_const_mul]
    unfold f g; ring
  rw [e]
  refine le_trans (intervalIntegral.integral_mono_on (g := fun _ => (1 : ℝ)) zero_le_one
    ((int_A hd).add ((int_B hd).const_mul _)) intervalIntegrable_const ?_) (by simp)
  intro t ht
  have hy := den_pos hd (by rwa [Set.uIcc_of_le zero_le_one])
  set y := 1 + (d - 1) * t with hydef
  have : (1 - t) / y + d * (t * (1 - t) / y ^ 2) = ((1 - t) * y + d * t * (1 - t)) / y ^ 2 := by
    field_simp
  rw [this, div_le_one (by positivity)]
  have : y ^ 2 - ((1 - t) * y + d * t * (1 - t)) = (d * t) ^ 2 := by rw [hydef]; ring
  nlinarith [sq_nonneg (d * t)]

lemma lower {D : ℝ} (hD : 1 ≤ D) : (Real.log D - 1) / D ≤ f D := by
  have hD0 : 0 < D := by linarith
  have hint : IntervalIntegrable (fun t : ℝ => (1 - t) / (1 + D * t)) volume 0 1 :=
    ContinuousOn.intervalIntegrable (ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun t ht => by
        rw [Set.uIcc_of_le zero_le_one] at ht
        nlinarith [ht.1]))
  have hmono : ∫ t in (0 : ℝ)..1, (1 - t) / (1 + D * t) ≤ f D := by
    apply intervalIntegral.integral_mono_on zero_le_one hint (int_A hD0)
    intro t ht
    have h1 := den_pos hD0 (by rwa [Set.uIcc_of_le zero_le_one])
    apply div_le_div_of_nonneg_left (by linarith [ht.2]) h1
    linarith [ht.1]
  have hG : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun t => (1 + D) / D ^ 2 * Real.log (1 + D * t) - t / D) ((1 - t) / (1 + D * t)) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hp : 0 < 1 + D * t := by nlinarith [ht.1]
    have h1 : HasDerivAt (fun t : ℝ => 1 + D * t) (0 + D * 1) t :=
      (hasDerivAt_const t 1).add ((hasDerivAt_id t).const_mul D)
    have h2 := ((h1.log hp.ne').const_mul ((1 + D) / D ^ 2)).sub ((hasDerivAt_id t).div_const D)
    have hp' := hp.ne'
    have hD' := hD0.ne'
    refine h2.congr_deriv ?_
    field_simp
    ring
  have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt hG hint
  simp only [mul_one, mul_zero, add_zero, Real.log_one, zero_div, sub_zero] at hval
  have hlog : Real.log D ≤ Real.log (1 + D) := Real.log_le_log hD0 (by linarith)
  have hl0 : 0 ≤ Real.log D := Real.log_nonneg hD
  have hcoef : 1 / D ≤ (1 + D) / D ^ 2 := by
    rw [div_le_div_iff₀ hD0 (by positivity)]; nlinarith
  have : (Real.log D - 1) / D ≤ (1 + D) / D ^ 2 * Real.log (1 + D) - 1 / D := by
    have h3 : Real.log D / D ≤ (1 + D) / D ^ 2 * Real.log (1 + D) := by
      calc Real.log D / D = 1 / D * Real.log D := by ring
        _ ≤ (1 + D) / D ^ 2 * Real.log D := mul_le_mul_of_nonneg_right hcoef hl0
        _ ≤ (1 + D) / D ^ 2 * Real.log (1 + D) :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
    have : (Real.log D - 1) / D = Real.log D / D - 1 / D := by ring
    linarith
  linarith

section ShearerGraph

open Finset

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def P (S : Finset V) : ℕ := ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2)).card

def deg (S : Finset V) (u : V) : ℕ := (S.filter (G.Adj u)).card

omit [DecidableEq V] in
lemma P_eq_sum (S : Finset V) : P G S = ∑ u ∈ S, deg G S u := by
  unfold P deg
  rw [card_filter, sum_product]
  apply sum_congr rfl; intro u _
  rw [card_filter]

omit [DecidableRel G.Adj] in
lemma no_tri (hG : G.CliqueFree 3) {v a b : V} (ha : G.Adj v a) (hb : G.Adj v b) : ¬ G.Adj a b := by
  intro hab
  exact hG {v, a, b} (SimpleGraph.is3Clique_triple_iff.mpr ⟨ha, hb, hab⟩)

lemma pairs_drop (hG : G.CliqueFree 3) (S : Finset V) (v : V) :
    P G (S \ insert v (S.filter (G.Adj v))) + 2 * ∑ u ∈ S.filter (G.Adj v), deg G S u ≤ P G S := by
  set N := S.filter (G.Adj v) with hN
  set S' := S \ insert v N with hS'
  set A := (S' ×ˢ S').filter (fun p => G.Adj p.1 p.2)
  set B1 := (N ×ˢ S).filter (fun p => G.Adj p.1 p.2)
  set B2 := (S ×ˢ N).filter (fun p => G.Adj p.1 p.2)
  have hB1 : B1.card = ∑ u ∈ N, deg G S u := by
    simp only [B1, deg]; rw [card_filter, sum_product]
    apply sum_congr rfl; intro u _; rw [card_filter]
  have hB2 : B2.card = B1.card := by
    apply card_bij (fun p _ => (p.2, p.1))
    · intro p hp; simp only [B1, B2, mem_filter, mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.symm⟩
    · intro p _ q _ h; simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1
    · intro q hq; refine ⟨(q.2, q.1), ?_, rfl⟩
      simp only [B1, B2, mem_filter, mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, hq.2.symm⟩
  have hNS : N ⊆ S := filter_subset _ _
  have hS'S : S' ⊆ S := sdiff_subset
  have notN : ∀ x ∈ S', x ∉ N := fun x hx hxN => (mem_sdiff.mp hx).2 (mem_insert_of_mem hxN)
  have d1 : Disjoint A B1 := by
    rw [Finset.disjoint_left]; intro p hpA hpB
    simp only [A, B1, mem_filter, mem_product] at hpA hpB
    exact notN _ hpA.1.1 hpB.1.1
  have d2 : Disjoint (A ∪ B1) B2 := by
    rw [Finset.disjoint_left]; intro p hp hpB
    simp only [B2, mem_filter, mem_product] at hpB
    rcases Finset.mem_union.mp hp with hpA | hpB1
    · simp only [A, mem_filter, mem_product] at hpA
      exact notN _ hpA.1.2 hpB.1.2
    · simp only [B1, mem_filter, mem_product] at hpB1
      have h1 := (mem_filter.mp hpB1.1.1).2
      have h2 := (mem_filter.mp hpB.1.2).2
      exact no_tri G hG h1 h2 hpB1.2
  have hsub : A ∪ B1 ∪ B2 ⊆ (S ×ˢ S).filter (fun p => G.Adj p.1 p.2) := by
    intro p hp
    simp only [A, B1, B2, Finset.mem_union, mem_filter, mem_product] at hp ⊢
    rcases hp with (h | h) | h
    · exact ⟨⟨hS'S h.1.1, hS'S h.1.2⟩, h.2⟩
    · exact ⟨⟨hNS h.1.1, h.1.2⟩, h.2⟩
    · exact ⟨⟨h.1.1, hNS h.1.2⟩, h.2⟩
  have := Finset.card_le_card hsub
  rw [card_union_of_disjoint d2, card_union_of_disjoint d1, hB2, hB1] at this
  unfold P
  linarith

omit [DecidableEq V] in
lemma sum_nbr_deg (S : Finset V) :
    ∑ v ∈ S, ∑ u ∈ S.filter (G.Adj v), (deg G S u : ℝ) = ∑ u ∈ S, (deg G S u : ℝ) ^ 2 := by
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl; intro u _
  rw [← sum_filter, sum_const, nsmul_eq_mul, sq]
  congr 1
  unfold deg
  congr 2
  ext w; simp only [mem_filter]
  exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩

theorem shearer (f g : ℝ → ℝ)
    (hT : ∀ x d : ℝ, 0 < x → 0 < d → f d + g d * (x - d) ≤ f x)
    (hN : ∀ d : ℝ, 0 < d → g d ≤ 0)
    (hO : ∀ d : ℝ, 0 < d → (1 + d) * f d - g d * (d - d ^ 2) = 1)
    (hZ : ∀ d : ℝ, 0 < d → f d - d * g d ≤ 1)
    (hG : G.CliqueFree 3) (S : Finset V) :
    ∃ I ⊆ S, G.IsIndepSet (I : Set V) ∧
      ∀ d : ℝ, 0 < d → (S.card : ℝ) * f d + g d * (P G S - S.card * d) ≤ I.card := by
  induction S using Finset.strongInduction with
  | H S ih =>
  by_cases hP : P G S = 0
  · refine ⟨S, subset_rfl, ?_, ?_⟩
    · intro a ha b hb _ hab
      have : (a, b) ∈ (S ×ˢ S).filter (fun p => G.Adj p.1 p.2) :=
        mem_filter.mpr ⟨mem_product.mpr ⟨ha, hb⟩, hab⟩
      unfold P at hP
      rw [card_eq_zero] at hP
      rw [hP] at this; simp at this
    · intro d hd
      rw [hP]; push_cast
      have := hZ d hd
      have hn : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
      nlinarith
  · have hSne : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; rintro rfl; exact hP (by simp [P])
    set n : ℝ := (S.card : ℝ) with hn
    have hn0 : 0 < n := by rw [hn]; exact_mod_cast hSne.card_pos
    set Pr : ℝ := (P G S : ℝ) with hPr
    have hP0 : 0 < Pr := by rw [hPr]; exact_mod_cast Nat.pos_of_ne_zero hP
    set d0 : ℝ := Pr / n with hd0
    have hd0pos : 0 < d0 := div_pos hP0 hn0
    have hnd : n * d0 = Pr := by rw [hd0]; field_simp
    set F := f d0
    set Gs := g d0
    have hGs : Gs ≤ 0 := hN d0 hd0pos
    have hode := hO d0 hd0pos
    set term : V → ℝ := fun v => 1 - (1 + (deg G S v : ℝ)) * F +
      Gs * (d0 + d0 * deg G S v - 2 * ∑ u ∈ S.filter (G.Adj v), (deg G S u : ℝ)) with hterm
    have hsumdeg : ∑ v ∈ S, (deg G S v : ℝ) = Pr := by rw [hPr, P_eq_sum]; push_cast; rfl
    have hCS : Pr ^ 2 ≤ n * ∑ u ∈ S, (deg G S u : ℝ) ^ 2 := by
      rw [← hsumdeg, hn]; exact sq_sum_le_card_mul_sum_sq
    have hsum : 0 ≤ ∑ v ∈ S, term v := by
      have e : ∑ v ∈ S, term v = n - (n + Pr) * F + Gs * (n * d0 + d0 * Pr -
          2 * ∑ u ∈ S, (deg G S u : ℝ) ^ 2) := by
        simp only [hterm, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul, sum_const,
          nsmul_eq_mul, mul_one, ← hn, hsumdeg, sum_nbr_deg]
      rw [e]
      have hsq : d0 * Pr ≤ ∑ u ∈ S, (deg G S u : ℝ) ^ 2 := by
        have : d0 * Pr * n = Pr ^ 2 := by rw [← hnd]; ring
        nlinarith
      have h1 : Gs * (n * d0 + d0 * Pr - 2 * ∑ u ∈ S, (deg G S u : ℝ) ^ 2) ≥
          Gs * (n * d0 + d0 * Pr - 2 * (d0 * Pr)) :=
        mul_le_mul_of_nonpos_left (by linarith) hGs
      have h2 : n - (n + Pr) * F + Gs * (n * d0 + d0 * Pr - 2 * (d0 * Pr)) =
          n * ((1 + d0) * F - Gs * (d0 - d0 ^ 2) - 1) * (-1) := by
        rw [← hnd]; ring
      rw [hode] at h2
      linarith
    obtain ⟨v, hvS, hv⟩ : ∃ v ∈ S, 0 ≤ term v := by
      by_contra hcon
      push Not at hcon
      have := sum_lt_sum_of_nonempty hSne (g := fun _ => (0 : ℝ)) hcon
      simp at this; linarith
    set Nv := S.filter (G.Adj v) with hNv
    set S' := S \ insert v Nv with hS'
    have hvN : v ∉ Nv := fun h => G.irrefl (mem_filter.mp h).2
    have hins : insert v Nv ⊆ S := insert_subset hvS (filter_subset _ _)
    have hcard : S'.card + (1 + deg G S v) = S.card := by
      rw [hS', card_sdiff, Finset.inter_eq_left.mpr hins, card_insert_of_notMem hvN]
      have := Finset.card_le_card hins
      rw [card_insert_of_notMem hvN] at this
      unfold deg; rw [← hNv]; omega
    obtain ⟨I', hI'S, hI'ind, hI'⟩ := ih S' (by rw [hS']; exact sdiff_ssubset hins ⟨v, mem_insert_self _ _⟩)
    have hdrop := pairs_drop G hG S v
    rw [← hNv, ← hS'] at hdrop
    have hvI' : v ∉ I' := fun h => (mem_sdiff.mp (hI'S h)).2 (mem_insert_self _ _)
    refine ⟨insert v I', insert_subset hvS (hI'S.trans sdiff_subset), ?_, ?_⟩
    · rw [coe_insert]
      refine Set.Pairwise.insert hI'ind (fun u hu _ => ?_)
      have huS' := hI'S (mem_coe.mp hu)
      have hnot : ¬ G.Adj v u := fun h =>
        (mem_sdiff.mp huS').2 (mem_insert_of_mem (mem_filter.mpr ⟨(mem_sdiff.mp huS').1, h⟩))
      exact ⟨hnot, fun h => hnot h.symm⟩
    · have hId0 := hI' d0 hd0pos
      rw [card_insert_of_notMem hvI']
      have hcardR : (S'.card : ℝ) + (1 + deg G S v) = n := by rw [hn]; exact_mod_cast hcard
      have hdropR : (P G S' : ℝ) + 2 * ∑ u ∈ Nv, (deg G S u : ℝ) ≤ Pr := by
        rw [hPr]; exact_mod_cast hdrop
      have hstep : n * F ≤ (I'.card : ℝ) + 1 := by
        have hA : Gs * ((P G S' : ℝ) - S'.card * d0) ≥
            Gs * (Pr - 2 * ∑ u ∈ Nv, (deg G S u : ℝ) - S'.card * d0) :=
          mul_le_mul_of_nonpos_left (by linarith) hGs
        have hv' : 0 ≤ term v := hv
        simp only [hterm] at hv'
        rw [← hNv] at hv'
        have e : n = S'.card + 1 + deg G S v := by linarith
        have e2 : Pr = n * d0 := hnd.symm
        rw [e2] at hA
        rw [e] at hA ⊢
        nlinarith
      intro d hd
      have htan := hT d0 d hd0pos hd
      have : n * f d + g d * (Pr - n * d) = n * (f d + g d * (d0 - d)) := by rw [← hnd]; ring
      rw [this]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left htan hn0.le]

end ShearerGraph

end Shearer

/-- Kim (1995) hypothesis: triangle-free graphs on `n` vertices with independence number `O(√(n log n))`. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop, ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧
    ∀ s : Finset (Fin n), G.IsIndepSet (s : Set (Fin n)) → (s.card : ℝ) ≤ C * √((n : ℝ) * Real.log n)

/-- Ajtai–Komlós–Szemerédi (1980) / Shearer (1983): every triangle-free graph on `m` vertices
has an independent set of size `≫ √(m log m)`. -/
def H2 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
    ∃ s : Finset V, G.IsIndepSet (s : Set V) ∧
      c * √((Fintype.card V : ℝ) * Real.log (Fintype.card V)) ≤ s.card

lemma exp4_lt : Real.exp (4 : ℝ) < 55 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp (4 : ℝ) = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have h0 : 0 < Real.exp (1 : ℝ) := Real.exp_pos 1
  calc Real.exp (1 : ℝ) ^ 4 < (2.7182818286 : ℝ) ^ 4 := by gcongr
    _ < 55 := by norm_num

lemma H2_proof : H2 := by
  refine ⟨1 / 15, by norm_num, ?_⟩
  intro V _ G hG
  classical
  set m : ℕ := Fintype.card V with hmdef
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · refine ⟨∅, by simp, ?_⟩
    rw [hm0]; simp
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  have hlog0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  by_cases hsmall : Real.log (m : ℝ) < 4
  · have hV : Nonempty V := Fintype.card_pos_iff.mp hmpos
    obtain ⟨v⟩ := hV
    refine ⟨{v}, by simp, ?_⟩
    have hm55 : (m : ℝ) < 55 := by
      have := (Real.log_lt_iff_lt_exp (by linarith)).mp hsmall
      linarith [exp4_lt]
    have hprod : (m : ℝ) * Real.log m ≤ 225 := by nlinarith
    have : √((m : ℝ) * Real.log m) ≤ 15 := by
      rw [show (15 : ℝ) = √(15 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num; linarith)
    simp only [Finset.card_singleton, Nat.cast_one]
    linarith
  push Not at hsmall
  set s : ℝ := √((m : ℝ) * Real.log m) with hsdef
  have hml : (m : ℝ) ≤ m * Real.log m := by nlinarith
  have hs1 : 1 ≤ s := by
    rw [hsdef, show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hs0 : 0 < s := by linarith
  have hss : s * s = m * Real.log m := Real.mul_self_sqrt (by positivity)
  set Pval : ℝ := (Shearer.P G Finset.univ : ℝ) with hPdef
  have hsumdeg : ∑ v : V, (Shearer.deg G Finset.univ v : ℝ) = Pval := by
    rw [hPdef, Shearer.P_eq_sum]; push_cast; rfl
  by_cases hd : (m : ℝ) * s ≤ Pval
  · have hne : (Finset.univ : Finset V).Nonempty := Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hmpos)
    obtain ⟨v, -, hv⟩ : ∃ v ∈ (Finset.univ : Finset V), s ≤ (Shearer.deg G Finset.univ v : ℝ) := by
      apply Finset.exists_le_of_sum_le hne
      rw [Finset.sum_const, Finset.card_univ, ← hmdef, nsmul_eq_mul, hsumdeg]; exact hd
    refine ⟨Finset.univ.filter (G.Adj v), ?_, ?_⟩
    · intro a ha b hb _ hab
      have ha' : G.Adj v a := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
      have hb' : G.Adj v b := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
      exact Shearer.no_tri G hG ha' hb' hab
    · have : (Shearer.deg G Finset.univ v : ℝ) = ((Finset.univ.filter (G.Adj v)).card : ℝ) := rfl
      rw [← this]; linarith
  · push Not at hd
    obtain ⟨I, -, hI, hbound⟩ := Shearer.shearer G Shearer.f Shearer.g
      (fun _ _ hx hd => Shearer.tangent hx hd)
      (fun _ hd => Shearer.g_nonpos hd) (fun _ hd => Shearer.ode hd)
      (fun _ hd => Shearer.at_zero hd) hG Finset.univ
    refine ⟨I, hI, ?_⟩
    have hb := hbound s hs0
    rw [Finset.card_univ, ← hmdef] at hb
    have hgs : Shearer.g s ≤ 0 := Shearer.g_nonpos hs0
    have h1 : 0 ≤ Shearer.g s * (Pval - m * s) := mul_nonneg_of_nonpos_of_nonpos hgs (by linarith)
    have hf := Shearer.lower hs1
    have hlogs : Real.log (m : ℝ) / 2 ≤ Real.log s := by
      have : Real.log s = Real.log ((m : ℝ) * Real.log m) / 2 := by rw [hsdef, Real.log_sqrt (by positivity)]
      rw [this]
      have := Real.log_le_log (by linarith) hml
      linarith
    have hfs : (m : ℝ) * ((Real.log s - 1) / s) ≤ I.card := by
      have := mul_le_mul_of_nonneg_left hf hmR
      linarith
    have key : 1 / 15 * s ≤ (m : ℝ) * ((Real.log s - 1) / s) := by
      rw [mul_div_assoc', le_div_iff₀ hs0]
      have : (m : ℝ) * (Real.log m / 4) ≤ m * (Real.log s - 1) := by
        apply mul_le_mul_of_nonneg_left _ hmR; linarith
      nlinarith
    linarith

lemma H2_finset (c : ℝ) (hH : ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
      ∃ s : Finset V, G.IsIndepSet (s : Set V) ∧
        c * √((Fintype.card V : ℝ) * Real.log (Fintype.card V)) ≤ s.card)
    {V : Type} (G : SimpleGraph V) (hG : G.CliqueFree 3) (S : Finset V) :
    ∃ I ⊆ S, G.IsIndepSet (I : Set V) ∧ c * √((S.card : ℝ) * Real.log S.card) ≤ I.card := by
  classical
  have hG' : (G.induce (S : Set V)).CliqueFree 3 := hG.comap (SimpleGraph.Embedding.induce _).isContained
  obtain ⟨s, hs, hcard⟩ := hH (S : Set V) (G.induce (S : Set V)) hG'
  refine ⟨s.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  · intro x hx y hy hxy
    simp only [Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact hs hx' hy' (fun h => hxy (congrArg Subtype.val h))
  · rw [Finset.card_map]
    have : Fintype.card (S : Set V) = S.card := by simp
    rw [this] at hcard
    exact hcard

lemma sqrt_step {a m i : ℝ} (ha : 0 < a) (hm0 : 0 < m) (hi : i ≤ m) (hai : a * √m ≤ i) :
    2 * √(m - i) / a + 1 ≤ 2 * √m / a := by
  have hm : 0 ≤ m := le_trans (le_trans (mul_nonneg ha.le (Real.sqrt_nonneg m)) hai) hi
  have hsm : √m * √m = m := Real.mul_self_sqrt hm
  have hle : a ≤ √m := by
    have h := Real.sqrt_pos.mpr hm0
    nlinarith
  have hkey : √(m - i) ≤ √m - a / 2 := by
    calc √(m - i) ≤ √((√m - a / 2) ^ 2) := by
          apply Real.sqrt_le_sqrt; nlinarith
      _ = √m - a / 2 := Real.sqrt_sq (by linarith)
  rw [div_add_one ha.ne', div_le_div_iff_of_pos_right ha]
  linarith

lemma color {V : Type} [DecidableEq V] (G : SimpleGraph V) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (M : ℕ)
    (hA : ∀ S : Finset V, M < S.card → ∃ I ⊆ S, G.IsIndepSet (I : Set V) ∧ a * √(S.card : ℝ) ≤ I.card)
    (hB : ∀ S : Finset V, S.Nonempty → ∃ I ⊆ S, G.IsIndepSet (I : Set V) ∧ b * √(S.card : ℝ) ≤ I.card) :
    ∀ S : Finset V, ∃ (c : V → ℕ) (t : ℕ), (∀ v ∈ S, c v < t) ∧
      (∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v) ∧
      (t : ℝ) ≤ 2 * √(S.card : ℝ) / a + 2 * √(min (S.card : ℝ) M) / b := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => 0, 0, by simp, by simp, by simp⟩
  have hm : (0 : ℝ) < S.card := by exact_mod_cast hne.card_pos
  have step : ∀ I ⊆ S, I.Nonempty → G.IsIndepSet (I : Set V) →
      ∃ (c : V → ℕ) (t : ℕ), (∀ v ∈ S, c v < t) ∧ (∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v) ∧
      (t : ℝ) ≤ 2 * √((S.card : ℝ) - I.card) / a + 2 * √(min ((S.card : ℝ) - I.card) M) / b + 1 := by
    intro I hIS hIne hI
    obtain ⟨c, t, h1, h2, h3⟩ := ih (S \ I) (Finset.sdiff_ssubset hIS hIne)
    have hcard : ((S \ I).card : ℝ) = (S.card : ℝ) - I.card := by
      rw [Finset.card_sdiff_of_subset hIS, Nat.cast_sub (Finset.card_le_card hIS)]
    refine ⟨fun v => if v ∈ I then t else c v, t + 1, ?_, ?_, ?_⟩
    · intro v hv
      by_cases hvI : v ∈ I
      · simp [hvI]
      · simp only [hvI, if_false]; exact Nat.lt_succ_of_lt (h1 v (Finset.mem_sdiff.mpr ⟨hv, hvI⟩))
    · intro u hu v hv huv
      by_cases huI : u ∈ I <;> by_cases hvI : v ∈ I
      · exact absurd huv (hI (Finset.mem_coe.mpr huI) (Finset.mem_coe.mpr hvI) (G.ne_of_adj huv))
      · simp only [huI, hvI, if_true, if_false]; exact (h1 v (Finset.mem_sdiff.mpr ⟨hv, hvI⟩)).ne'
      · simp only [huI, hvI, if_true, if_false]; exact (h1 u (Finset.mem_sdiff.mpr ⟨hu, huI⟩)).ne
      · simp only [huI, hvI, if_false]
        exact h2 u (Finset.mem_sdiff.mpr ⟨hu, huI⟩) v (Finset.mem_sdiff.mpr ⟨hv, hvI⟩) huv
    · rw [hcard] at h3; push_cast; linarith
  have hpos : ∀ e : ℝ, 0 < e → e * √(S.card : ℝ) ≤ 0 → False := fun e he h =>
    by nlinarith [mul_pos he (Real.sqrt_pos.mpr hm)]
  rcases Nat.lt_or_ge M S.card with hbig | hsmall
  · obtain ⟨I, hIS, hI, hai⟩ := hA S hbig
    have hIne : I.Nonempty := by
      rw [← Finset.card_pos]; by_contra h0; push Not at h0
      exact hpos a ha (by have : (I.card : ℝ) = 0 := by exact_mod_cast Nat.le_zero.mp h0
                          linarith)
    obtain ⟨c, t, h1, h2, h3⟩ := step I hIS hIne hI
    refine ⟨c, t, h1, h2, ?_⟩
    have him : (I.card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card hIS
    have hs := sqrt_step ha hm him hai
    have hmin : min ((S.card : ℝ) - I.card) M ≤ min (S.card : ℝ) M :=
      min_le_min_right _ (by linarith [(Nat.cast_nonneg I.card : (0 : ℝ) ≤ I.card)])
    have hsq : 2 * √(min ((S.card : ℝ) - I.card) M) / b ≤ 2 * √(min (S.card : ℝ) M) / b := by
      apply div_le_div_of_nonneg_right _ hb.le
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmin) (by norm_num)
    linarith
  · obtain ⟨I, hIS, hI, hbi⟩ := hB S hne
    have hIne : I.Nonempty := by
      rw [← Finset.card_pos]; by_contra h0; push Not at h0
      exact hpos b hb (by have : (I.card : ℝ) = 0 := by exact_mod_cast Nat.le_zero.mp h0
                          linarith)
    obtain ⟨c, t, h1, h2, h3⟩ := step I hIS hIne hI
    refine ⟨c, t, h1, h2, ?_⟩
    have him : (I.card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card hIS
    have hMR : (S.card : ℝ) ≤ M := by exact_mod_cast hsmall
    have hI0 : (0 : ℝ) ≤ I.card := Nat.cast_nonneg _
    rw [min_eq_left hMR, min_eq_left (by linarith)] at *
    have hs := sqrt_step hb hm him hbi
    have hfirst : 2 * √((S.card : ℝ) - I.card) / a ≤ 2 * √(S.card : ℝ) / a := by
      apply div_le_div_of_nonneg_right _ ha.le
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by norm_num)
    linarith

lemma chrom_le {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℕ) (h : G.Colorable t)
    (x : ℕ) (hx : G.chromaticNumber = (x : ℕ∞)) : x ≤ t := by
  have h1 : G.chromaticNumber ≤ t := h.chromaticNumber_le
  rw [hx] at h1
  exact_mod_cast h1

lemma upper (h2 : H2) : ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
    (Erdos920.f 3 n : ℝ) ≤ K * √((n : ℝ) / Real.log n) := by
  classical
  obtain ⟨c, hc, hH⟩ := h2
  set b : ℝ := min c (1 / 2) with hbdef
  have hb : 0 < b := lt_min hc (by norm_num)
  refine ⟨4 / c + 2 * √2 / b, by positivity, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨16, fun n hn => ?_⟩
  set s := Nat.sqrt n with hsdef
  have hs2 : 2 ≤ s := by rw [hsdef, Nat.le_sqrt]; omega
  have hs4 : n ≤ s ^ 4 := by
    have := Nat.lt_succ_sqrt n
    rw [← hsdef] at this
    have h4 : 4 ≤ s ^ 2 := by nlinarith
    have : (s + 1) * (s + 1) ≤ s ^ 4 := by nlinarith
    rw [Nat.succ_eq_add_one] at *
    omega
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hlogS : ∀ m : ℕ, s < m → Real.log (n : ℝ) / 4 ≤ Real.log (m : ℝ) := by
    intro m hm
    have h1 : (n : ℝ) ≤ (m : ℝ) ^ 4 := by
      have : n ≤ m ^ 4 := le_trans hs4 (Nat.pow_le_pow_left hm.le 4)
      exact_mod_cast this
    have h2 := Real.log_le_log hnpos h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  set a : ℝ := c / 2 * √(Real.log (n : ℝ)) with hadef
  have ha : 0 < a := by positivity
  have hfn : Erdos920.f 3 n ≤ ⌊(4 / c + 2 * √2 / b) * √((n : ℝ) / Real.log n)⌋₊ := by
    unfold Erdos920.f
    apply csSup_le
    · have hne : (⊥ : SimpleGraph (Fin n)).chromaticNumber ≠ ⊤ :=
        SimpleGraph.chromaticNumber_ne_top_iff_exists.mpr ⟨_, SimpleGraph.colorable_of_fintype _⟩
      exact ⟨_, ⊥, SimpleGraph.cliqueFree_bot (by omega), (ENat.natCast_toNat hne).symm⟩
    rintro x ⟨G, hG, hx⟩
    have hA : ∀ S : Finset (Fin n), s < S.card →
        ∃ I ⊆ S, G.IsIndepSet (I : Set (Fin n)) ∧ a * √(S.card : ℝ) ≤ I.card := by
      intro S hS
      obtain ⟨I, hIS, hI, hc'⟩ := H2_finset c hH G hG S
      refine ⟨I, hIS, hI, le_trans ?_ hc'⟩
      have hl := hlogS S.card hS
      rw [hadef, Real.sqrt_mul' _ (by linarith [hlogn] : (0 : ℝ) ≤ Real.log S.card)]
      have : √(Real.log (n : ℝ)) / 2 ≤ √(Real.log (S.card : ℝ)) := by
        rw [show √(Real.log (n : ℝ)) / 2 = √(Real.log (n : ℝ) / 4) by
          rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4)]
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt hl
      have hsS := Real.sqrt_nonneg (S.card : ℝ)
      calc c / 2 * √(Real.log (n : ℝ)) * √(S.card : ℝ) = c * (√(Real.log (n : ℝ)) / 2) * √(S.card : ℝ) := by
            ring
        _ ≤ c * √(Real.log (S.card : ℝ)) * √(S.card : ℝ) := by gcongr
        _ = c * (√(S.card : ℝ) * √(Real.log (S.card : ℝ))) := by ring
    have hB : ∀ S : Finset (Fin n), S.Nonempty →
        ∃ I ⊆ S, G.IsIndepSet (I : Set (Fin n)) ∧ b * √(S.card : ℝ) ≤ I.card := by
      intro S hS
      rcases Nat.lt_or_ge S.card 3 with hlt | hge
      · obtain ⟨v, hv⟩ := hS
        refine ⟨{v}, Finset.singleton_subset_iff.mpr hv, by simp, ?_⟩
        have hle : (S.card : ℝ) ≤ 2 := by exact_mod_cast (by omega : S.card ≤ 2)
        have h1 : √(S.card : ℝ) ≤ 2 := by
          rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
          exact Real.sqrt_le_sqrt (by linarith)
        have hb2 : b ≤ 1 / 2 := min_le_right _ _
        simp only [Finset.card_singleton, Nat.cast_one]
        nlinarith [Real.sqrt_nonneg (S.card : ℝ)]
      · obtain ⟨I, hIS, hI, hc'⟩ := H2_finset c hH G hG S
        refine ⟨I, hIS, hI, le_trans ?_ hc'⟩
        have h3 : (3 : ℝ) ≤ S.card := by exact_mod_cast hge
        have hl1 : 1 ≤ Real.log (S.card : ℝ) := by
          rw [Real.le_log_iff_exp_le (by linarith)]
          have := Real.exp_one_lt_d9
          linarith
        have hbc : b ≤ c := min_le_left _ _
        have : √(S.card : ℝ) ≤ √((S.card : ℝ) * Real.log S.card) :=
          Real.sqrt_le_sqrt (by nlinarith)
        nlinarith [Real.sqrt_nonneg (S.card : ℝ)]
    obtain ⟨col, t, h1, h2, h3⟩ := color G a b ha hb s hA hB Finset.univ
    have hcol : G.Colorable t :=
      ⟨SimpleGraph.Coloring.mk (fun v => ⟨col v, h1 v (Finset.mem_univ v)⟩)
        (fun {u v} huv h => h2 u (Finset.mem_univ u) v (Finset.mem_univ v) huv (congrArg Fin.val h))⟩
    have hxt := chrom_le G t hcol x hx
    refine hxt.trans (Nat.le_floor (h3.trans ?_))
    rw [Finset.card_univ, Fintype.card_fin]
    have hmin : min (n : ℝ) (s : ℝ) ≤ s := min_le_right _ _
    have hsR : (s : ℝ) ≤ √(n : ℝ) := by
      rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      exact_mod_cast Nat.sqrt_le' n
    have hsqrt_n : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hnpos
    have hQ : √((n : ℝ) / Real.log n) = √(n : ℝ) / √(Real.log (n : ℝ)) := Real.sqrt_div' _ hlogn.le
    have e1 : 2 * √(n : ℝ) / a = 4 / c * √((n : ℝ) / Real.log n) := by
      rw [hQ, hadef]; field_simp; ring
    have hlog2 : Real.log (n : ℝ) ≤ 2 * √(n : ℝ) := by
      have := Real.log_le_sub_one_of_pos hsqrt_n
      rw [Real.log_sqrt hnpos.le] at this
      linarith
    have hss : √(min (n : ℝ) (s : ℝ)) ≤ √2 * √((n : ℝ) / Real.log n) := by
      have hA1 : √(min (n : ℝ) (s : ℝ)) ≤ √(√(n : ℝ)) := Real.sqrt_le_sqrt (hmin.trans hsR)
      have hA2 : √(√(n : ℝ)) ≤ √2 * √((n : ℝ) / Real.log n) := by
        rw [← Real.sqrt_mul (by norm_num)]
        apply Real.sqrt_le_sqrt
        rw [mul_div_assoc', le_div_iff₀ hlogn]
        have hsq : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hnpos.le
        nlinarith
      exact hA1.trans hA2
    have e2 : 2 * √(min (n : ℝ) (s : ℝ)) / b ≤ 2 * √2 / b * √((n : ℝ) / Real.log n) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hb]
      nlinarith
    rw [e1, add_mul]
    linarith
  calc (Erdos920.f 3 n : ℝ) ≤ (⌊(4 / c + 2 * √2 / b) * √((n : ℝ) / Real.log n)⌋₊ : ℝ) := by
        exact_mod_cast hfn
    _ ≤ _ := Nat.floor_le (by positivity)

lemma lower (h1 : H1) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop,
    √((n : ℝ) / Real.log n) ≤ C * Erdos920.f 3 n := by
  classical
  obtain ⟨C, hC, hev⟩ := h1
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev, Filter.eventually_ge_atTop 2] with n ⟨G, hG, hα⟩ hn2
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < n := by linarith
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  set t := G.chromaticNumber.toNat with htdef
  have hne : G.chromaticNumber ≠ ⊤ :=
    SimpleGraph.chromaticNumber_ne_top_iff_exists.mpr ⟨_, SimpleGraph.colorable_of_fintype _⟩
  have hcol : G.Colorable t := by
    rw [htdef]; exact SimpleGraph.colorable_chromaticNumber_of_fintype G
  have htf : t ≤ Erdos920.f 3 n := by
    unfold Erdos920.f
    apply le_csSup
    · refine ⟨n, ?_⟩
      rintro x ⟨H, -, hx⟩
      have : H.chromaticNumber ≤ Fintype.card (Fin n) := SimpleGraph.chromaticNumber_le_card
      rw [hx, Fintype.card_fin] at this
      exact_mod_cast this
    · exact ⟨G, hG, (ENat.natCast_toNat hne).symm⟩
  obtain ⟨col⟩ := hcol
  have hsum : (n : ℝ) ≤ t * (C * √((n : ℝ) * Real.log n)) := by
    have hcard := Finset.card_eq_sum_card_fiberwise (f := fun v : Fin n => col v) (s := Finset.univ)
      (t := (Finset.univ : Finset (Fin t))) (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    have hb : ∀ i ∈ (Finset.univ : Finset (Fin t)),
        (((Finset.univ : Finset (Fin n)).filter (fun v => col v = i)).card : ℝ) ≤ C * √((n : ℝ) * Real.log n) := by
      intro i _
      apply hα
      intro u hu v hv _ hadj
      have hu' : col u = i := (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2
      have hv' : col v = i := (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).2
      exact col.valid hadj (hu'.trans hv'.symm)
    have := Finset.sum_le_sum hb
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    calc (n : ℝ) = ∑ i : Fin t, (((Finset.univ : Finset (Fin n)).filter (fun v => col v = i)).card : ℝ) := by
          exact_mod_cast hcard
      _ ≤ _ := this
  have hR : 0 < √((n : ℝ) * Real.log n) := Real.sqrt_pos.mpr (mul_pos hnpos hlogn)
  have hprod : √((n : ℝ) / Real.log n) * √((n : ℝ) * Real.log n) = n := by
    rw [← Real.sqrt_mul (div_nonneg hnpos.le hlogn.le)]
    rw [show (n : ℝ) / Real.log n * (n * Real.log n) = n ^ 2 by field_simp]
    exact Real.sqrt_sq hnpos.le
  have htR : (t : ℝ) ≤ Erdos920.f 3 n := by exact_mod_cast htf
  have key : √((n : ℝ) / Real.log n) ≤ C * t := by
    by_contra hcon
    push Not at hcon
    have : C * t * √((n : ℝ) * Real.log n) < √((n : ℝ) / Real.log n) * √((n : ℝ) * Real.log n) :=
      mul_lt_mul_of_pos_right hcon hR
    rw [hprod] at this
    nlinarith
  calc √((n : ℝ) / Real.log n) ≤ C * t := key
    _ ≤ C * Erdos920.f 3 n := mul_le_mul_of_nonneg_left htR hC.le

lemma main_reduction : H1 → H2 → type_of% @Erdos920.erdos_920.variants.k_eq_3 := by
  intro h1 h2
  obtain ⟨K, _, hup⟩ := upper h2
  obtain ⟨C, _, hlo⟩ := lower h1
  have e : ∀ n : ℕ, ((n : ℝ) / Real.log n) ^ (1 / 2 : ℝ) = √((n : ℝ) / Real.log n) := fun n =>
    (Real.sqrt_eq_rpow _).symm
  simp_rw [e]
  refine ⟨Asymptotics.IsBigO.of_bound K ?_, Asymptotics.IsBigO.of_bound C ?_⟩
  · filter_upwards [hup] with n hn
    rw [Real.norm_natCast, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact hn
  · filter_upwards [hlo] with n hn
    rw [Real.norm_natCast, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact hn

end ShearerUpper

/- ### Section 4B: Five-Event Existence Argument and Asymptotic Parameter Verification (`kim_1995_H1`) -/

section KimAsymptotics

/-- Helper: extract an `s`-subset `I' ⊆ I` on which `φ` is injective, whenever `s ≤ (I.image φ).card`. -/
lemma exists_injOn_subset_of_card_image_ge {n m s : ℕ} (φ : Fin n → Fin m) (I : Finset (Fin n))
    (hge : s ≤ (I.image φ).card) :
    ∃ I' ⊆ I, I'.card = s ∧ Set.InjOn φ (I' : Set (Fin n)) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs_pos
  · exact ⟨∅, Finset.empty_subset _, rfl, by simp⟩
  have hIne : I.Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty] at he
    subst he; simp at hge; omega
  obtain ⟨u₀, _⟩ := hIne
  obtain ⟨B₀, hB₀sub, hB₀c⟩ := Finset.exists_subset_card_eq hge
  have hpre : ∀ x : Fin m, x ∈ B₀ → ∃ u ∈ I, φ u = x := fun x hx =>
    Finset.mem_image.mp (hB₀sub hx)
  let pick : Fin m → Fin n := fun x =>
    if h : x ∈ B₀ then Classical.choose (hpre x h) else u₀
  have hpick_mem : ∀ x ∈ B₀, pick x ∈ I := fun x hx => by
    simp only [pick, dif_pos hx]; exact (Classical.choose_spec (hpre x hx)).1
  have hpick_eq : ∀ x ∈ B₀, φ (pick x) = x := fun x hx => by
    simp only [pick, dif_pos hx]; exact (Classical.choose_spec (hpre x hx)).2
  let I' : Finset (Fin n) := B₀.image pick
  refine ⟨I', ?_, ?_, ?_⟩
  · intro u hu
    rcases Finset.mem_image.mp hu with ⟨x, hx, rfl⟩
    exact hpick_mem x hx
  · rw [Finset.card_image_of_injOn, hB₀c]
    intro x hx y hy heq
    have hx' : x ∈ B₀ := Finset.mem_coe.mp hx
    have hy' : y ∈ B₀ := Finset.mem_coe.mp hy
    rw [← hpick_eq x hx', ← hpick_eq y hy', heq]
  · intro u hu v hv heq
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hu) with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hv) with ⟨y, hy, rfl⟩
    rw [hpick_eq x hx, hpick_eq y hy] at heq
    rw [heq]

/-- Master finite existence lemma: if the 5 explicit probabilistic upper bounds are each `≤ 1/10`
(with `BadPi` strictly `< 1/10`), there exists a triangle-free graph on `Fin n` with every
independent set of size `< k`. -/
lemma exists_good_graph_of_bounds {n m k s t J : ℕ} {p F_max L₁ L₂ : ℝ}
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hs : 16 ≤ s) (hs_m : s - 1 ≤ m) (h4s : 4 * (s - 1) ≤ k)
    (ht : 1 ≤ t) (hJ : 1 ≤ J) (hp0 : 0 < p) (hp1 : p < 1) (hF : 0 < F_max)
    (hL₁ : 0 < L₁) (hL₂ : L₁ < L₂)
    (hcover : L₂ ≤ ((Nat.floor L₁ + 1 : ℕ) : ℝ) * (2 : ℝ) ^ J)
    (hs_t : (s : ℝ) / F_max + 1 ≤ (t : ℝ))
    (ht_le : (t : ℝ) ≤ 2 * ((s : ℝ) / F_max))
    (hF_small : F_max ≤ (1 / 10 : ℝ) * (s : ℝ))
    (hmp2 : 4 * (m : ℝ) * p ^ 2 ≤ 1 / 20)
    (h_fib : 2 * (m : ℝ) * (Real.exp 1 * (n : ℝ) / (((Nat.floor F_max + 1 : ℕ) : ℝ) * (m : ℝ))) ^
      (Nat.floor F_max + 1) < 1 / 20)
    (h_comp : (Real.exp 4 * ((n : ℝ) / (k : ℝ)) ^ 2 *
      (((s - 1 : ℕ) : ℝ) / (m : ℝ)) ^ 3) ^ k < (1 / 20 : ℝ) ^ 2)
    (h_badG :
      let r₀ : ℕ := Nat.floor L₁ + 1
      let T_p : ℝ := (1 / 4000 : ℝ) * (t : ℝ) ^ 2
      let D : ℝ := 2 * ((m : ℝ) * p)
      let E₀ : ℝ := T_p / D
      let e₀ : ℕ := Nat.ceil E₀
      let u_max : ℕ := Nat.floor ((E₀ + D) / L₂)
      let P_per_A : ℝ :=
        Real.exp ((2 * (m : ℝ) * ((t : ℝ) * p + ((t : ℝ) * p) ^ 2) - T_p) / L₁ ^ 2) +
        (∑ j ∈ Finset.range J,
          if ((r₀ * 2 ^ j : ℕ) : ℝ) < L₂ then
            let rj : ℕ := r₀ * 2 ^ j
            let bj : ℕ := Nat.ceil (T_p / (4 * (J : ℝ) * (rj : ℝ) ^ 2))
            ((m : ℝ) * (Real.exp 1 * (t : ℝ) * p / (rj : ℝ)) ^ rj) ^ bj
          else 0) +
        ∑ u ∈ Finset.Icc 1 u_max,
          (m : ℝ) ^ u * (Real.exp 1 * ((t : ℝ) * (u : ℝ)) * p / (e₀ : ℝ)) ^ e₀
      (m : ℝ) * Real.exp (-(((m - 1 : ℕ) : ℝ) * p) / 6) +
        ((t : ℝ) + 1) * (m : ℝ) ^ t * P_per_A ≤ 1 / 10)
    (h_badIndep :
      let L_B : ℝ := 20 * ((s : ℝ) * p)
      let D : ℝ := 2 * ((m : ℝ) * p)
      let T_B : ℝ := (1 / 20 : ℝ) * (s : ℝ) ^ 2
      let E₀ : ℝ := T_B / D
      let e₀ : ℕ := Nat.ceil E₀
      let u_max : ℕ := Nat.floor ((E₀ + D) / L_B)
      (n.choose s : ℝ) *
        (Real.exp ((2 * (m : ℝ) * ((s : ℝ) * p + ((s : ℝ) * p) ^ 2) - T_B) / L_B ^ 2) +
         (∑ u ∈ Finset.Icc 1 u_max, (m : ℝ) ^ u * (Real.exp 1 * ((s : ℝ) * (u : ℝ)) * p / (e₀ : ℝ)) ^ e₀) +
         Real.exp (-((s : ℝ) ^ 2 * p) / 24) +
         Real.exp (-p * ((1 / 10 : ℝ) * (s : ℝ) ^ 2))) ≤ 1 / 10) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧
      ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) → S.card < k := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  set M : ℝ := (m : ℝ) ^ n
  have hM_pos : 0 < M := pow_pos hm_pos n
  have hM2_pos : 0 < M ^ 2 := pow_pos hM_pos 2
  have hsum_maps : ∀ c : ℝ, (∑ _φ : Fin n → Fin m, c) = M * c := fun c => by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow]
  have hcard_maps : (Fintype.card ((Fin n → Fin m) × (Fin n → Fin m)) : ℝ) = M ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow, M, sq]
  let Ω := (EdgeIdx m → Bool) × (EdgeIdx m → Bool) × (Fin n → Fin m) × (Fin n → Fin m)
  let W : Ω → ℝ := fun q => bernW p q.1 * bernW p q.2.1
  have hW_nn : ∀ q : Ω, 0 ≤ W q := fun q =>
    mul_nonneg (bernW_nonneg hp0.le hp1.le q.1) (bernW_nonneg hp0.le hp1.le q.2.1)
  have hW_tot : ∑ q : Ω, W q = M ^ 2 := by
    simp only [Ω, W, Fintype.sum_prod_type]
    have h1 : ∀ ω_R : EdgeIdx m → Bool,
        (∑ ω_B : EdgeIdx m → Bool, ∑ _φ_R : Fin n → Fin m, ∑ _φ_B : Fin n → Fin m, bernW p ω_R * bernW p ω_B) =
        bernW p ω_R * M ^ 2 := by
      intro ω_R
      have hinner : ∀ ω_B : EdgeIdx m → Bool,
          (∑ _φ_R : Fin n → Fin m, ∑ _φ_B : Fin n → Fin m, bernW p ω_R * bernW p ω_B) =
          (bernW p ω_R * bernW p ω_B) * M ^ 2 := fun ω_B => by
        rw [hsum_maps, hsum_maps]; ring
      simp_rw [hinner, ← Finset.sum_mul, ← Finset.mul_sum, sum_bernW_eq_one, mul_one]
    simp_rw [h1, ← Finset.sum_mul, sum_bernW_eq_one, one_mul]
  let B1 : Ω → Prop := fun q => BadPi n m k s F_max q.2.2.1 q.2.2.2
  let B2 : Ω → Prop := fun q => BadGraph m t p q.1
  let B3 : Ω → Prop := fun q => BadGraph m t p q.2.1
  let B4 : Ω → Prop := fun q => ¬ B1 q ∧ ¬ B2 q ∧ BadIndepBlue n m s p q.1 q.2.1 q.2.2.1 q.2.2.2
  let B5 : Ω → Prop := fun q => ¬ B1 q ∧ ¬ B3 q ∧ BadIndepBlue n m s p q.2.1 q.1 q.2.2.2 q.2.2.1
  -- Bound 1: `B1` strictly `< (1/10) M^2`
  have hB1 : (∑ q : Ω, if B1 q then W q else 0) < (1 / 10 : ℝ) * M ^ 2 := by
    have heq : (∑ q : Ω, if B1 q then W q else 0) =
        ((Finset.univ.filter (fun pφ : (Fin n → Fin m) × (Fin n → Fin m) =>
          BadPi n m k s F_max pφ.1 pφ.2)).card : ℝ) := by
      simp only [Ω, W, B1, Fintype.sum_prod_type]
      have h1 : ∀ ω_R ω_B : EdgeIdx m → Bool,
          (∑ φ_R : Fin n → Fin m, ∑ φ_B : Fin n → Fin m,
            if BadPi n m k s F_max φ_R φ_B then bernW p ω_R * bernW p ω_B else 0) =
          (bernW p ω_R * bernW p ω_B) *
            ((Finset.univ.filter (fun pφ : (Fin n → Fin m) × (Fin n → Fin m) =>
              BadPi n m k s F_max pφ.1 pφ.2)).card : ℝ) := by
        intro ω_R ω_B
        rw [← Fintype.sum_prod_type', Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun pφ _ => by split_ifs <;> simp
      simp_rw [h1, ← Finset.sum_mul, ← Finset.mul_sum, sum_bernW_eq_one, mul_one]
      rw [sum_bernW_eq_one, one_mul]
    rw [heq]
    have hlt := card_badPi_lt hm hk (by omega : 2 ≤ s) hs_m h4s hF h_fib h_comp
    rwa [hcard_maps] at hlt
  -- Bound 2: `B2 ≤ (1/10) M^2`
  have hBadG_prob : bernProb p (BadGraph m t p) ≤ 1 / 10 :=
    (bernProb_badGraph_le hm ht hJ hp0 hp1.le hL₁ hL₂ hcover).trans h_badG
  have hB2 : (∑ q : Ω, if B2 q then W q else 0) ≤ (1 / 10 : ℝ) * M ^ 2 := by
    have heq : (∑ q : Ω, if B2 q then W q else 0) = bernProb p (BadGraph m t p) * M ^ 2 := by
      simp only [Ω, W, B2, Fintype.sum_prod_type, bernProb]
      have h1 : ∀ ω_R : EdgeIdx m → Bool,
          (∑ ω_B : EdgeIdx m → Bool, ∑ _φ_R : Fin n → Fin m, ∑ _φ_B : Fin n → Fin m,
            if BadGraph m t p ω_R then bernW p ω_R * bernW p ω_B else 0) =
          (if BadGraph m t p ω_R then bernW p ω_R else 0) * M ^ 2 := by
        intro ω_R
        by_cases hG : BadGraph m t p ω_R
        · simp only [if_pos hG]
          have h2 : ∀ ω_B : EdgeIdx m → Bool,
              (∑ _φ_R : Fin n → Fin m, ∑ _φ_B : Fin n → Fin m, bernW p ω_R * bernW p ω_B) =
              (bernW p ω_R * bernW p ω_B) * M ^ 2 := fun ω_B => by
            rw [hsum_maps, hsum_maps]; ring
          simp_rw [h2, ← Finset.sum_mul, ← Finset.mul_sum, sum_bernW_eq_one, mul_one]
        · simp [hG]
      simp_rw [h1, ← Finset.sum_mul]
    rw [heq]
    exact mul_le_mul_of_nonneg_right hBadG_prob hM2_pos.le
  -- Bound 3: `B3 ≤ (1/10) M^2`
  have hB3 : (∑ q : Ω, if B3 q then W q else 0) ≤ (1 / 10 : ℝ) * M ^ 2 := by
    let sw : Ω ≃ Ω :=
      { toFun := fun q => (q.2.1, q.1, q.2.2.1, q.2.2.2)
        invFun := fun q => (q.2.1, q.1, q.2.2.1, q.2.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have heq : (∑ q : Ω, if B3 q then W q else 0) = ∑ q : Ω, if B2 q then W q else 0 :=
      Fintype.sum_equiv sw _ _ fun q => by simp only [sw, B2, B3, W, Equiv.coe_fn_mk, mul_comm]
    rw [heq]; exact hB2
  -- Bound 4: `B4 ≤ (1/10) M^2`
  have hB4 : (∑ q : Ω, if B4 q then W q else 0) ≤ (1 / 10 : ℝ) * M ^ 2 := by
    simp only [Ω, W, B4, Fintype.sum_prod_type]
    have hswap : ∀ ω_R : EdgeIdx m → Bool,
        (∑ ω_B : EdgeIdx m → Bool, ∑ φ_R : Fin n → Fin m, ∑ φ_B : Fin n → Fin m,
          if ¬ B1 (ω_R, ω_B, φ_R, φ_B) ∧ ¬ B2 (ω_R, ω_B, φ_R, φ_B) ∧ BadIndepBlue n m s p ω_R ω_B φ_R φ_B
          then bernW p ω_R * bernW p ω_B else 0) ≤
        bernW p ω_R * ((1 / 10 : ℝ) * M ^ 2) := by
      intro ω_R
      rw [Finset.sum_comm]
      have hinner1 : ∀ φ_R : Fin n → Fin m,
          (∑ ω_B : EdgeIdx m → Bool, ∑ φ_B : Fin n → Fin m,
            if ¬ B1 (ω_R, ω_B, φ_R, φ_B) ∧ ¬ B2 (ω_R, ω_B, φ_R, φ_B) ∧ BadIndepBlue n m s p ω_R ω_B φ_R φ_B
            then bernW p ω_R * bernW p ω_B else 0) ≤
          bernW p ω_R * ((1 / 10 : ℝ) * M) := by
        intro φ_R
        rw [Finset.sum_comm]
        have hinner2 : ∀ φ_B : Fin n → Fin m,
            (∑ ω_B : EdgeIdx m → Bool,
              if ¬ B1 (ω_R, ω_B, φ_R, φ_B) ∧ ¬ B2 (ω_R, ω_B, φ_R, φ_B) ∧ BadIndepBlue n m s p ω_R ω_B φ_R φ_B
              then bernW p ω_R * bernW p ω_B else 0) ≤
            bernW p ω_R * (1 / 10 : ℝ) := by
          intro φ_B
          by_cases hgood : ¬ BadPi n m k s F_max φ_R φ_B ∧ ¬ BadGraph m t p ω_R
          · have hfiber : ∀ x : Fin m, ((Finset.univ.filter (fun v : Fin n => φ_R v = x)).card : ℝ) ≤ F_max := by
              intro x; by_contra hgt; push Not at hgt
              exact hgood.1 (Or.inl ⟨x, hgt⟩)
            have hcodeg : ∀ A : Finset (Fin m), A.card ≤ t →
                ∑ z ∈ Finset.univ \ A, (degIn (graphOf ω_R) A z : ℝ) ^ 2 ≤ (1 / 1000 : ℝ) * (t : ℝ) ^ 2 := by
              intro A hAt; by_contra hgt; push Not at hgt
              exact hgood.2 (Or.inr ⟨A, hAt, hgt⟩)
            have hprob_le : bernProb p (fun ω_B => BadIndepBlue n m s p ω_R ω_B φ_R φ_B) ≤ 1 / 10 :=
              (bernProb_badIndepBlue_le hm hs hp0 hp1 hF hs_t ht_le hF_small hmp2 ω_R φ_R φ_B hfiber hcodeg).trans h_badIndep
            have hsum_eq : (∑ ω_B : EdgeIdx m → Bool,
                if ¬ B1 (ω_R, ω_B, φ_R, φ_B) ∧ ¬ B2 (ω_R, ω_B, φ_R, φ_B) ∧ BadIndepBlue n m s p ω_R ω_B φ_R φ_B
                then bernW p ω_R * bernW p ω_B else 0) =
                bernW p ω_R * bernProb p (fun ω_B => BadIndepBlue n m s p ω_R ω_B φ_R φ_B) := by
              rw [bernProb, Finset.mul_sum]
              refine Finset.sum_congr rfl fun ω_B _ => ?_
              simp only [B1, B2, hgood.1, hgood.2, not_false_eq_true, true_and]
              split_ifs <;> ring
            rw [hsum_eq]
            exact mul_le_mul_of_nonneg_left hprob_le (bernW_nonneg hp0.le hp1.le ω_R)
          · have hzero : (∑ ω_B : EdgeIdx m → Bool,
                if ¬ B1 (ω_R, ω_B, φ_R, φ_B) ∧ ¬ B2 (ω_R, ω_B, φ_R, φ_B) ∧ BadIndepBlue n m s p ω_R ω_B φ_R φ_B
                then bernW p ω_R * bernW p ω_B else 0) = 0 :=
              Finset.sum_eq_zero fun ω_B _ => if_neg fun h => hgood ⟨h.1, h.2.1⟩
            rw [hzero]
            exact mul_nonneg (bernW_nonneg hp0.le hp1.le ω_R) (by norm_num)
        calc _ ≤ ∑ _φ_B : Fin n → Fin m, (bernW p ω_R * (1 / 10 : ℝ)) := Finset.sum_le_sum fun φ_B _ => hinner2 φ_B
          _ = bernW p ω_R * ((1 / 10 : ℝ) * M) := by rw [hsum_maps]; ring
      calc _ ≤ ∑ _φ_R : Fin n → Fin m, (bernW p ω_R * ((1 / 10 : ℝ) * M)) := Finset.sum_le_sum fun φ_R _ => hinner1 φ_R
        _ = bernW p ω_R * ((1 / 10 : ℝ) * M ^ 2) := by rw [hsum_maps]; ring
    calc _ ≤ ∑ ω_R : EdgeIdx m → Bool, bernW p ω_R * ((1 / 10 : ℝ) * M ^ 2) :=
          Finset.sum_le_sum fun ω_R _ => hswap ω_R
      _ = (1 / 10 : ℝ) * M ^ 2 := by rw [← Finset.sum_mul, sum_bernW_eq_one, one_mul]
  -- Bound 5: `B5 ≤ (1/10) M^2`
  have hB5 : (∑ q : Ω, if B5 q then W q else 0) ≤ (1 / 10 : ℝ) * M ^ 2 := by
    let sw : Ω ≃ Ω :=
      { toFun := fun q => (q.2.1, q.1, q.2.2.2, q.2.2.1)
        invFun := fun q => (q.2.1, q.1, q.2.2.2, q.2.2.1)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hBadPi_symm : ∀ φ₁ φ₂ : Fin n → Fin m, BadPi n m k s F_max φ₁ φ₂ ↔ BadPi n m k s F_max φ₂ φ₁ := by
      intro φ₁ φ₂; simp only [BadPi]
      constructor <;> rintro (h | h | ⟨I, h1, h2, h3⟩)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨I, h1, h3, h2⟩)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨I, h1, h3, h2⟩)
    have heq : (∑ q : Ω, if B5 q then W q else 0) = ∑ q : Ω, if B4 q then W q else 0 :=
      Fintype.sum_equiv sw _ _ fun q => by
        simp only [sw, B4, B5, B1, B2, B3, W, Equiv.coe_fn_mk, mul_comm, hBadPi_symm]
    rw [heq]; exact hB4
  have hgood_exists : ∃ q : Ω, ¬ (B1 q ∨ B2 q ∨ B3 q ∨ B4 q ∨ B5 q) := by
    by_contra hall
    push Not at hall
    have hsum_le : ∑ q : Ω, W q ≤
        (∑ q : Ω, if B1 q then W q else 0) + (∑ q : Ω, if B2 q then W q else 0) +
        (∑ q : Ω, if B3 q then W q else 0) + (∑ q : Ω, if B4 q then W q else 0) +
        (∑ q : Ω, if B5 q then W q else 0) := by
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun q _ => ?_
      have hw := hW_nn q
      have hq := hall q
      rcases hq with h | h | h | h | h <;> simp only [h, ite_true] <;>
        (repeat (split_ifs)) <;> linarith only [hw]
    linarith only [hW_tot, hsum_le, hB1, hB2, hB3, hB4, hB5, hM2_pos]
  rcases hgood_exists with ⟨⟨ω_R, ω_B, φ_R, φ_B⟩, hgood⟩
  simp only [not_or] at hgood
  rcases hgood with ⟨hnB1, hnB2, hnB3, hnB4, hnB5⟩
  have hnBlue : ¬ BadIndepBlue n m s p ω_R ω_B φ_R φ_B := fun h => hnB4 ⟨hnB1, hnB2, h⟩
  have hnRed : ¬ BadIndepBlue n m s p ω_B ω_R φ_B φ_R := fun h => hnB5 ⟨hnB1, hnB3, h⟩
  have hdegB : ∀ x : Fin m, (degIn (graphOf ω_B) Finset.univ x : ℝ) ≤ 2 * ((m : ℝ) * p) := by
    intro x; by_contra hgt; push Not at hgt; exact hnB3 (Or.inl ⟨x, hgt⟩)
  have hdegR : ∀ x : Fin m, (degIn (graphOf ω_R) Finset.univ x : ℝ) ≤ 2 * ((m : ℝ) * p) := by
    intro x; by_contra hgt; push Not at hgt; exact hnB2 (Or.inl ⟨x, hgt⟩)
  let G := buildGraph (graphOf ω_R) (graphOf ω_B) φ_R φ_B
  refine ⟨G, buildGraph_cliqueFree _ _ _ _, fun S hSind => ?_⟩
  by_contra hge
  push Not at hge
  obtain ⟨I, hIS, hIk⟩ := Finset.exists_subset_card_eq hge
  have hnot_both : ¬ ((I.image φ_R).card < s ∧ (I.image φ_B).card < s) := fun h =>
    hnB1 (Or.inr (Or.inr ⟨I, hIk, h.1, h.2⟩))
  by_cases hBbig : s ≤ (I.image φ_B).card
  · obtain ⟨I', hI'I, hI'c, hinj⟩ := exists_injOn_subset_of_card_image_ge φ_B I hBbig
    refine hnBlue ⟨hdegB, I', Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hI'c⟩, hinj, ?_⟩
    intro u hu v hv hblue
    have hne : u ≠ v := fun h => by
      subst h; exact (pruneTri (graphOf ω_B)).loopless.irrefl (φ_B u) hblue.1
    exact hSind (Finset.mem_coe.mpr (hIS (hI'I hu))) (Finset.mem_coe.mpr (hIS (hI'I hv))) hne (Or.inr hblue)
  · have hRbig : s ≤ (I.image φ_R).card := by omega
    obtain ⟨I', hI'I, hI'c, hinj⟩ := exists_injOn_subset_of_card_image_ge φ_R I hRbig
    refine hnRed ⟨hdegR, I', Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hI'c⟩, hinj, ?_⟩
    intro u hu v hv hred
    have hne : u ≠ v := fun h => by
      subst h; exact (pruneTri (graphOf ω_R)).loopless.irrefl (φ_R u) hred.1
    exact hSind (Finset.mem_coe.mpr (hIS (hI'I hu))) (Finset.mem_coe.mpr (hIS (hI'I hv))) hne (Or.inl hred)

/-- Elementary logarithmic growth bound: for every `a > 0`, `b : ℕ`, and `K : ℝ`,
`K * (log n)^b < n^a` eventually as `n → ∞`. -/
lemma eventually_log_pow_lt_rpow {a : ℝ} (ha : 0 < a) (b : ℕ) (K : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, K * (Real.log (n : ℝ)) ^ b < (n : ℝ) ^ a := by
  let ε : ℝ := a / (2 * ((b : ℝ) + 1))
  have hε : 0 < ε := by positivity
  let M : ℝ := (max K 0) / ε ^ b + 1
  have hM : 0 < M := by positivity
  let N₀ : ℕ := max 2 (Nat.ceil (M ^ (2 / a)) + 1)
  rw [Filter.eventually_atTop]
  refine ⟨N₀, fun n hn => ?_⟩
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_trans (le_max_left _ _) hn)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hlog_le : Real.log (n : ℝ) ≤ (n : ℝ) ^ ε / ε := by
    have h1 : Real.log ((n : ℝ) ^ ε) ≤ (n : ℝ) ^ ε - 1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hn_pos ε)
    rw [Real.log_rpow hn_pos] at h1
    rw [le_div_iff₀ hε]; linarith
  have hpow_le : (Real.log (n : ℝ)) ^ b ≤ (n : ℝ) ^ ((b : ℝ) * ε) / ε ^ b := by
    calc (Real.log (n : ℝ)) ^ b ≤ ((n : ℝ) ^ ε / ε) ^ b := pow_le_pow_left₀ hlog_nn hlog_le b
      _ = ((n : ℝ) ^ ε) ^ b / ε ^ b := div_pow _ _ _
      _ = (n : ℝ) ^ ((b : ℝ) * ε) / ε ^ b := by
          congr 1; rw [← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le, mul_comm]
  have hbe_le : (b : ℝ) * ε ≤ a / 2 := by
    simp only [ε]
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Nat.cast_nonneg (α := ℝ) b]
  have hn_pow_le : (n : ℝ) ^ ((b : ℝ) * ε) ≤ (n : ℝ) ^ (a / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hbe_le
  have hM_lt : M < (n : ℝ) ^ (a / 2) := by
    have hn_gt : M ^ (2 / a) < (n : ℝ) := by
      have hceil : Nat.ceil (M ^ (2 / a)) + 1 ≤ n := le_trans (le_max_right _ _) hn
      have h1 : M ^ (2 / a) ≤ (Nat.ceil (M ^ (2 / a)) : ℝ) := Nat.le_ceil _
      have h2 : (Nat.ceil (M ^ (2 / a)) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hceil
      linarith
    have h3 : (M ^ (2 / a)) ^ (a / 2) < (n : ℝ) ^ (a / 2) :=
      Real.rpow_lt_rpow (Real.rpow_nonneg hM.le _) hn_gt (by positivity)
    have h4 : (M ^ (2 / a)) ^ (a / 2) = M := by
      rw [← Real.rpow_mul hM.le]
      have : (2 / a) * (a / 2) = 1 := by field_simp
      rw [this, Real.rpow_one]
    rwa [h4] at h3
  have hsplit : (n : ℝ) ^ a = (n : ℝ) ^ (a / 2) * (n : ℝ) ^ (a / 2) := by
    rw [← Real.rpow_add hn_pos]; congr 1; ring
  calc K * (Real.log (n : ℝ)) ^ b
      ≤ max K 0 * (Real.log (n : ℝ)) ^ b := mul_le_mul_of_nonneg_right (le_max_left K 0) (pow_nonneg hlog_nn b)
    _ ≤ max K 0 * ((n : ℝ) ^ ((b : ℝ) * ε) / ε ^ b) := mul_le_mul_of_nonneg_left hpow_le (le_max_right K 0)
    _ ≤ max K 0 * ((n : ℝ) ^ (a / 2) / ε ^ b) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hn_pow_le (pow_nonneg hε.le b)) (le_max_right K 0)
    _ = (max K 0 / ε ^ b) * (n : ℝ) ^ (a / 2) := by ring
    _ ≤ M * (n : ℝ) ^ (a / 2) := mul_le_mul_of_nonneg_right (by simp only [M]; linarith) (Real.rpow_pos_of_pos hn_pos _).le
    _ < (n : ℝ) ^ (a / 2) * (n : ℝ) ^ (a / 2) := mul_lt_mul_of_pos_right hM_lt (Real.rpow_pos_of_pos hn_pos _)
    _ = (n : ℝ) ^ a := hsplit.symm

/-- Elementary `log n > c` eventually as `n → ∞`. -/
lemma eventually_lt_log (c : ℝ) : ∀ᶠ n : ℕ in Filter.atTop, c < Real.log (n : ℝ) := by
  rw [Filter.eventually_atTop]
  refine ⟨Nat.ceil (Real.exp c) + 1, fun n hn => ?_⟩
  have h1 : Real.exp c < (n : ℝ) := by
    have h2 : Real.exp c ≤ (Nat.ceil (Real.exp c) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil (Real.exp c) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  exact (Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos c) h1)).mpr h1

lemma exp_neg_ten_lt : Real.exp (-10 : ℝ) < 1 / 40 := by
  have h1 : (40 : ℝ) < Real.exp 10 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    have h3 : (2 : ℝ) ^ 10 ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) h2 10
    have h4 : (Real.exp 1) ^ 10 = Real.exp 10 := by rw [← Real.exp_nat_mul]; norm_num
    linarith only [h3, h4, show (40 : ℝ) < (2 : ℝ) ^ 10 by norm_num]
  rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 10) (by norm_num)]
  linarith only [h1]

/-- Helper 1 for `kim_1995_H1`: verify the `BadPi` fiber and double-compression inequalities. -/
lemma asymp_badPi_bounds {n m k s : ℕ} {C_val α : ℝ}
    (hC : 0 < C_val) (hα : 1 ≤ α) (hn10k : (10000 : ℝ) ≤ (n : ℝ)) (hk1 : 1 ≤ k)
    (hL100 : 100 < Real.log (n : ℝ))
    (hm_ge : (n : ℝ) / (2 * α * Real.log (n : ℝ)) ≤ (m : ℝ))
    (hm_le_n : (m : ℝ) ≤ (n : ℝ))
    (hk_ge : C_val * (√(n : ℝ) * √(Real.log (n : ℝ))) ≤ (k : ℝ))
    (hs_le : (s : ℝ) ≤ C_val * (√(n : ℝ) * √(Real.log (n : ℝ))))
    (h_q_L4 : Real.exp 4 * C_val * α ^ 3 * 4000 * (Real.log (n : ℝ)) ^ 4 < √(n : ℝ)) :
    let F_max : ℝ := 12 * α * Real.log (n : ℝ)
    2 * (m : ℝ) * (Real.exp 1 * (n : ℝ) / (((Nat.floor F_max + 1 : ℕ) : ℝ) * (m : ℝ))) ^
      (Nat.floor F_max + 1) < 1 / 20 ∧
    (Real.exp 4 * ((n : ℝ) / (k : ℝ)) ^ 2 * (((s - 1 : ℕ) : ℝ) / (m : ℝ)) ^ 3) ^ k < (1 / 20 : ℝ) ^ 2 := by
  intro F_max
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith only [hn10k]
  set L : ℝ := Real.log (n : ℝ)
  have hL_pos : 0 < L := by linarith only [hL100]
  set q : ℝ := √(n : ℝ)
  have hq_pos : 0 < q := Real.sqrt_pos.mpr hn_pos
  have hq_sq : q ^ 2 = (n : ℝ) := Real.sq_sqrt hn_pos.le
  have hsqL_pos : 0 < √L := Real.sqrt_pos.mpr hL_pos
  have hsqL_sq : (√L) ^ 2 = L := Real.sq_sqrt hL_pos.le
  have hsqL_le : √L ≤ L := by nlinarith only [hsqL_sq, hsqL_pos, hL100]
  have he_lt3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have hm_pos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by positivity) hm_ge
  constructor
  · set rf : ℕ := Nat.floor F_max + 1
    have hrf_ge : F_max ≤ (rf : ℝ) := by
      have := Nat.lt_floor_add_one F_max
      push_cast [rf]; linarith only [this]
    have hrfm : 6 * (n : ℝ) ≤ (rf : ℝ) * (m : ℝ) := by
      have h1 : F_max * ((n : ℝ) / (2 * α * L)) = 6 * (n : ℝ) := by
        simp only [F_max]; field_simp [hL_pos.ne', (show (0 : ℝ) < α by linarith).ne']; ring
      have h2 := mul_le_mul hrf_ge hm_ge (by positivity) (by positivity)
      linarith only [h1, h2]
    have hbase : Real.exp 1 * (n : ℝ) / ((rf : ℝ) * (m : ℝ)) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith only [hrfm, he_lt3, hn_pos]
    have hhalf : (1 / 2 : ℝ) ≤ Real.exp (-1 / 2) := by
      have hsq : Real.exp (1 / 2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ 2 := by
        rw [← Real.exp_nat_mul]
        have : (2 : ℕ) * (1 / 2 : ℝ) = 1 := by norm_num
        rw [this]; linarith only [he_lt3]
      have hle2 : Real.exp (1 / 2 : ℝ) ≤ 2 := by nlinarith only [hsq, Real.exp_pos (1 / 2 : ℝ)]
      rw [one_div, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.exp_neg]
      exact inv_anti₀ (Real.exp_pos _) hle2
    have hrf_4L : 4 * L ≤ (rf : ℝ) := by
      have : 4 * L ≤ F_max := by simp only [F_max]; nlinarith only [hα, hL_pos]
      linarith only [this, hrf_ge]
    have hpow : (Real.exp 1 * (n : ℝ) / ((rf : ℝ) * (m : ℝ))) ^ rf ≤ Real.exp (-2 * L) := by
      calc _ ≤ (1 / 2 : ℝ) ^ rf := pow_le_pow_left₀ (by positivity) hbase rf
        _ ≤ (Real.exp (-1 / 2)) ^ rf := pow_le_pow_left₀ (by norm_num) hhalf rf
        _ = Real.exp ((rf : ℝ) * (-1 / 2)) := (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp (-2 * L) := Real.exp_le_exp.mpr (by linarith only [hrf_4L])
    have hexp2L : Real.exp (-2 * L) = 1 / (n : ℝ) ^ 2 := by
      rw [show (-2 * L : ℝ) = -(((2 : ℕ) : ℝ) * Real.log (n : ℝ)) by norm_num [L],
        Real.exp_neg, Real.exp_nat_mul, Real.exp_log hn_pos, one_div]
    calc 2 * (m : ℝ) * (Real.exp 1 * (n : ℝ) / ((rf : ℝ) * (m : ℝ))) ^ rf
        ≤ 2 * (n : ℝ) * Real.exp (-2 * L) := mul_le_mul (by linarith only [hm_le_n]) hpow (by positivity) (by positivity)
      _ = 2 / (n : ℝ) := by rw [hexp2L]; field_simp [hn_pos.ne']
      _ < 1 / 20 := by rw [div_lt_iff₀ hn_pos]; linarith only [hn10k]
  · have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hnk : (n : ℝ) / (k : ℝ) ≤ q / (C_val * √L) := by
      rw [div_le_div_iff₀ hk_pos (by positivity)]
      have : (n : ℝ) * (C_val * √L) = q * (C_val * (q * √L)) := by rw [← hq_sq]; ring
      rw [this]; exact mul_le_mul_of_nonneg_left hk_ge hq_pos.le
    have hsm : ((s - 1 : ℕ) : ℝ) / (m : ℝ) ≤ 2 * C_val * α * L * √L / q := by
      have h1 : ((s - 1 : ℕ) : ℝ) ≤ C_val * (q * √L) := (Nat.cast_le.mpr (Nat.sub_le s 1)).trans hs_le
      calc ((s - 1 : ℕ) : ℝ) / (m : ℝ)
          ≤ (C_val * (q * √L)) / ((n : ℝ) / (2 * α * L)) :=
            div_le_div₀ (by positivity) h1 (by positivity) hm_ge
        _ = 2 * C_val * α * L * √L / q := by
            field_simp [hn_pos.ne', hq_pos.ne', hL_pos.ne']
            rw [← hq_sq]
    have hbase_lt : Real.exp 4 * ((n : ℝ) / (k : ℝ)) ^ 2 * (((s - 1 : ℕ) : ℝ) / (m : ℝ)) ^ 3 < (1 / 20 : ℝ) ^ 2 := by
      have h1 : ((n : ℝ) / (k : ℝ)) ^ 2 ≤ q ^ 2 / (C_val ^ 2 * L) := by
        calc _ ≤ (q / (C_val * √L)) ^ 2 := pow_le_pow_left₀ (by positivity) hnk 2
          _ = q ^ 2 / (C_val ^ 2 * L) := by rw [div_pow, mul_pow, hsqL_sq]
      have h2 : (((s - 1 : ℕ) : ℝ) / (m : ℝ)) ^ 3 ≤ 8 * C_val ^ 3 * α ^ 3 * L ^ 4 * √L / q ^ 3 := by
        calc _ ≤ (2 * C_val * α * L * √L / q) ^ 3 := pow_le_pow_left₀ (by positivity) hsm 3
          _ = 8 * C_val ^ 3 * α ^ 3 * L ^ 3 * (√L ^ 2 * √L) / q ^ 3 := by ring
          _ = 8 * C_val ^ 3 * α ^ 3 * L ^ 4 * √L / q ^ 3 := by rw [hsqL_sq]; ring
      have h3 : Real.exp 4 * ((n : ℝ) / (k : ℝ)) ^ 2 * (((s - 1 : ℕ) : ℝ) / (m : ℝ)) ^ 3 ≤
          8 * Real.exp 4 * C_val * α ^ 3 * L ^ 4 / q := by
        have ha : Real.exp 4 * ((n : ℝ) / (k : ℝ)) ^ 2 * (((s - 1 : ℕ) : ℝ) / (m : ℝ)) ^ 3 ≤
            Real.exp 4 * (q ^ 2 / (C_val ^ 2 * L)) * (8 * C_val ^ 3 * α ^ 3 * L ^ 4 * √L / q ^ 3) := by
          gcongr
        have hb : Real.exp 4 * (q ^ 2 / (C_val ^ 2 * L)) * (8 * C_val ^ 3 * α ^ 3 * L ^ 4 * √L / q ^ 3) =
            (8 * Real.exp 4 * C_val * α ^ 3) * (L ^ 3 * √L) / q := by
          field_simp [hq_pos.ne', hL_pos.ne', hC.ne']
        have hL4 : L ^ 3 * √L ≤ L ^ 4 := by nlinarith only [hsqL_le, pow_pos hL_pos 3]
        have hc : (8 * Real.exp 4 * C_val * α ^ 3) * (L ^ 3 * √L) / q ≤
            8 * Real.exp 4 * C_val * α ^ 3 * L ^ 4 / q := by
          refine div_le_div_of_nonneg_right ?_ hq_pos.le
          have := mul_le_mul_of_nonneg_left hL4 (by positivity : 0 ≤ 8 * Real.exp 4 * C_val * α ^ 3)
          linarith only [this]
        exact (ha.trans_eq hb).trans hc
      have h4 : 8 * Real.exp 4 * C_val * α ^ 3 * L ^ 4 / q < (1 / 20 : ℝ) ^ 2 := by
        rw [div_lt_iff₀ hq_pos]
        have hpos : 0 < Real.exp 4 * C_val * α ^ 3 * L ^ 4 := by positivity
        nlinarith only [h_q_L4, hpos]
      exact h3.trans_lt h4
    have hpow_le : (Real.exp 4 * ((n : ℝ) / (k : ℝ)) ^ 2 * (((s - 1 : ℕ) : ℝ) / (m : ℝ)) ^ 3) ^ k ≤
        (Real.exp 4 * ((n : ℝ) / (k : ℝ)) ^ 2 * (((s - 1 : ℕ) : ℝ) / (m : ℝ)) ^ 3) ^ 1 :=
      pow_le_pow_of_le_one (by positivity) (hbase_lt.le.trans (by norm_num)) hk1
    rw [pow_one] at hpow_le
    exact hpow_le.trans_lt hbase_lt

/-- Helper 2 for `kim_1995_H1`: verify the `BadGraph` upper bound `≤ 1 / 10`. -/
lemma asymp_badGraph_bound {n m t J : ℕ} {p : ℝ}
    (hm1 : 1 ≤ m) (ht1 : 1 ≤ t) (hJ1 : 1 ≤ J) (hp_pos : 0 < p)
    (hn10k : (10000 : ℝ) ≤ (n : ℝ)) (hL100 : 100 < Real.log (n : ℝ))
    (hu100 : 100 < √(√(n : ℝ)))
    (h_n_L1 : 4 * (20000000 : ℝ) * Real.log (n : ℝ) < (n : ℝ))
    (h_q_L2 : 100 * (20000000 : ℝ) * (Real.log (n : ℝ)) ^ 2 < √(n : ℝ))
    (h_q_L4b : (100000000 : ℝ) * (Real.log (n : ℝ)) ^ 4 < √(n : ℝ))
    (h_u_L3 : (1000000000 : ℝ) * (Real.log (n : ℝ)) ^ 3 < √(√(n : ℝ)))
    (hm_ge : (n : ℝ) / (2 * 20000000 * Real.log (n : ℝ)) ≤ (m : ℝ))
    (hm_le : (m : ℝ) ≤ (n : ℝ) / (20000000 * Real.log (n : ℝ)))
    (hm_le_n : (m : ℝ) ≤ (n : ℝ))
    (ht_ge : (1 / 50 : ℝ) * (√(n : ℝ) / √(Real.log (n : ℝ))) ≤ (t : ℝ))
    (ht_le : (t : ℝ) ≤ (1 / 30 : ℝ) * (√(n : ℝ) / √(Real.log (n : ℝ))))
    (hJ_le : (J : ℝ) ≤ 2 * Real.log (n : ℝ))
    (htp_le : (t : ℝ) * p ≤ 1 / 30)
    (hmp_le : (m : ℝ) * p ≤ (1 / 20000000 : ℝ) * (√(n : ℝ) / √(Real.log (n : ℝ))))
    (hmp_ge : (1 / (2 * 20000000) : ℝ) * (√(n : ℝ) / √(Real.log (n : ℝ))) ≤ (m : ℝ) * p) :
    let L : ℝ := Real.log (n : ℝ)
    let u : ℝ := √(√(n : ℝ))
    let r₀ : ℕ := Nat.floor L + 1
    let T_p : ℝ := (1 / 4000 : ℝ) * (t : ℝ) ^ 2
    let D : ℝ := 2 * ((m : ℝ) * p)
    let E₀ : ℝ := T_p / D
    let e₀ : ℕ := Nat.ceil E₀
    let u_max : ℕ := Nat.floor ((E₀ + D) / u)
    let P_per_A : ℝ :=
      Real.exp ((2 * (m : ℝ) * ((t : ℝ) * p + ((t : ℝ) * p) ^ 2) - T_p) / L ^ 2) +
      (∑ j ∈ Finset.range J,
        if ((r₀ * 2 ^ j : ℕ) : ℝ) < u then
          let rj : ℕ := r₀ * 2 ^ j
          let bj : ℕ := Nat.ceil (T_p / (4 * (J : ℝ) * (rj : ℝ) ^ 2))
          ((m : ℝ) * (Real.exp 1 * (t : ℝ) * p / (rj : ℝ)) ^ rj) ^ bj
        else 0) +
      ∑ u_i ∈ Finset.Icc 1 u_max,
        (m : ℝ) ^ u_i * (Real.exp 1 * ((t : ℝ) * (u_i : ℝ)) * p / (e₀ : ℝ)) ^ e₀
    (m : ℝ) * Real.exp (-(((m - 1 : ℕ) : ℝ) * p) / 6) +
      ((t : ℝ) + 1) * (m : ℝ) ^ t * P_per_A ≤ 1 / 10 := by
  intro L u r₀ T_p D E₀ e₀ u_max P_per_A
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith only [hn10k]
  have hL_pos : 0 < L := by linarith only [hL100]
  set q : ℝ := √(n : ℝ)
  have hq_pos : 0 < q := Real.sqrt_pos.mpr hn_pos
  have hq_sq : q ^ 2 = (n : ℝ) := Real.sq_sqrt hn_pos.le
  have hu_pos : 0 < u := Real.sqrt_pos.mpr hq_pos
  have hu_sq : u ^ 2 = q := Real.sq_sqrt hq_pos.le
  have hu4 : u ^ 4 = (n : ℝ) := by nlinarith only [hu_sq, hq_sq]
  have h_q_L2' : 100 * (20000000 : ℝ) * L ^ 2 < q := h_q_L2
  have h_n_L1' : 4 * (20000000 : ℝ) * L < (n : ℝ) := h_n_L1
  have h_q_L4b' : (100000000 : ℝ) * L ^ 4 < q := h_q_L4b
  have h_u_L3' : (1000000000 : ℝ) * L ^ 3 < u := h_u_L3
  have hsqL_pos : 0 < √L := Real.sqrt_pos.mpr hL_pos
  have hsqL_sq : (√L) ^ 2 = L := Real.sq_sqrt hL_pos.le
  have hsqL_le : √L ≤ L := by nlinarith only [hsqL_sq, hsqL_pos, hL100]
  have hsqL_ge10 : 10 ≤ √L := by nlinarith only [hsqL_sq, hsqL_pos, hL100]
  have he_lt3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have hq_le_n : q ≤ (n : ℝ) := by nlinarith only [hq_sq, hq_pos, hn10k]
  have hTp_ge : (1 / 10000000 : ℝ) * ((n : ℝ) / L) ≤ T_p := by
    have ht_sq : (1 / 2500 : ℝ) * ((n : ℝ) / L) ≤ (t : ℝ) ^ 2 := by
      have h1 : ((1 / 50 : ℝ) * (q / √L)) ^ 2 ≤ (t : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) ht_ge 2
      have h2 : ((1 / 50 : ℝ) * (q / √L)) ^ 2 = (1 / 2500 : ℝ) * ((n : ℝ) / L) := by
        rw [mul_pow, div_pow, div_pow, hq_sq, hsqL_sq]; ring
      linarith only [h1, h2]
    simp only [T_p]; linarith only [ht_sq]
  have hPref_t : ((t : ℝ) + 1) * (m : ℝ) ^ t ≤ Real.exp (((t : ℝ) + 1) * L) := by
    have ht1_le : (t : ℝ) + 1 ≤ (n : ℝ) := by
      have h1 : q / √L ≤ (n : ℝ) := by
        rw [div_le_iff₀ hsqL_pos]; nlinarith only [hq_le_n, hsqL_ge10, hn_pos]
      linarith only [ht_le, h1, hn10k]
    have hpow : ((t : ℝ) + 1) * (m : ℝ) ^ t ≤ (n : ℝ) ^ (t + 1) := by
      rw [pow_succ (n : ℝ) t, mul_comm ((n : ℝ) ^ t)]
      exact mul_le_mul ht1_le (pow_le_pow_left₀ (Nat.cast_nonneg _) hm_le_n t) (by positivity) hn_pos.le
    have hlog_eq : (n : ℝ) ^ (t + 1) = Real.exp (((t : ℝ) + 1) * L) := by
      have hcast : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by push_cast; rfl
      rw [← hcast, Real.exp_nat_mul, Real.exp_log hn_pos]
    rwa [hlog_eq] at hpow
  have hPref_le : ((t : ℝ) + 1) * (m : ℝ) ^ t ≤ Real.exp (q * √L) := by
    refine hPref_t.trans (Real.exp_le_exp.mpr ?_)
    have h1 : ((t : ℝ) + 1) * L ≤ ((1 / 30 : ℝ) * (q / √L) + 1) * L :=
      mul_le_mul_of_nonneg_right (by linarith only [ht_le]) hL_pos.le
    have h2 : (q / √L) * L = q * √L := by field_simp [hsqL_pos.ne']; rw [hsqL_sq]
    have h3 : L ≤ (1 / 2 : ℝ) * (q * √L) := by
      have : L ≤ q := by nlinarith only [h_q_L2', hL100]
      nlinarith only [this, hsqL_ge10, hq_pos]
    have h1' : ((t : ℝ) + 1) * L ≤ (1 / 30 : ℝ) * ((q / √L) * L) + L := by linarith only [h1]
    rw [h2] at h1'
    have hqsqL_nn : 0 ≤ q * √L := by positivity
    linarith only [h1', h3, hqsqL_nn]
  -- Piece 0: Max-degree `< 1 / 40`
  have hP0 : (m : ℝ) * Real.exp (-(((m - 1 : ℕ) : ℝ) * p) / 6) < 1 / 40 := by
    have hm_sub : (m : ℝ) / 2 ≤ ((m - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hm1]; simp only [Nat.cast_one]
      have hm2 : (2 : ℝ) ≤ (m : ℝ) := by
        have : (2 : ℝ) ≤ (n : ℝ) / (2 * 20000000 * L) := by
          rw [le_div_iff₀ (by positivity)]; linarith only [h_n_L1']
        linarith only [this, hm_ge]
      linarith only [hm2]
    have hmp_big : 2 * L + 10 ≤ (((m - 1 : ℕ) : ℝ) * p) / 6 := by
      have h1 : (1 / (24 * 20000000 : ℝ)) * (q / √L) ≤ (((m - 1 : ℕ) : ℝ) * p) / 6 := by
        have := mul_le_mul_of_nonneg_right hm_sub hp_pos.le
        linarith only [this, hmp_ge]
      have h2 : 2 * L + 10 ≤ (1 / (24 * 20000000 : ℝ)) * (q / √L) := by
        rw [mul_div_assoc', le_div_iff₀ hsqL_pos]
        have ha : (2 * L + 10) * √L ≤ 3 * L ^ 2 := by nlinarith only [hsqL_le, hL100]
        have hb : (24 * 20000000 : ℝ) * ((2 * L + 10) * √L) ≤ q := by linarith only [ha, h_q_L2', sq_nonneg L]
        linarith only [hb]
      exact h2.trans h1
    calc (m : ℝ) * Real.exp (-(((m - 1 : ℕ) : ℝ) * p) / 6)
        ≤ (n : ℝ) * Real.exp (-(2 * L + 10)) :=
          mul_le_mul hm_le_n (Real.exp_le_exp.mpr (by linarith only [hmp_big])) (Real.exp_pos _).le hn_pos.le
      _ = Real.exp (L - (2 * L + 10)) := by
          rw [show (n : ℝ) = Real.exp L from (Real.exp_log hn_pos).symm, ← Real.exp_add, sub_eq_add_neg]
      _ ≤ Real.exp (-10 : ℝ) := Real.exp_le_exp.mpr (by linarith only [hL_pos])
      _ < 1 / 40 := exp_neg_ten_lt
  -- Piece 1: Small-degree squares `< 1 / 40`
  have hP1 : ((t : ℝ) + 1) * (m : ℝ) ^ t *
      Real.exp ((2 * (m : ℝ) * ((t : ℝ) * p + ((t : ℝ) * p) ^ 2) - T_p) / L ^ 2) < 1 / 40 := by
    have hmean_small : 2 * (m : ℝ) * ((t : ℝ) * p + ((t : ℝ) * p) ^ 2) ≤ (1 / 2 : ℝ) * T_p := by
      have htp_nn : 0 ≤ (t : ℝ) * p := by positivity
      have htp_sum : (t : ℝ) * p + ((t : ℝ) * p) ^ 2 ≤ 1 / 25 := by nlinarith only [htp_le, htp_nn]
      have h1 : 2 * (m : ℝ) * ((t : ℝ) * p + ((t : ℝ) * p) ^ 2) ≤ (2 / 25) * ((n : ℝ) / (20000000 * L)) := by
        have := mul_le_mul hm_le htp_sum (by positivity) (by positivity)
        linarith only [this]
      have h2 : (2 / 25 : ℝ) * ((n : ℝ) / (20000000 * L)) = (2 / (25 * 20000000) : ℝ) * ((n : ℝ) / L) := by ring
      have h3 : (2 / (25 * 20000000) : ℝ) * ((n : ℝ) / L) ≤ (1 / 2 : ℝ) * ((1 / 10000000 : ℝ) * ((n : ℝ) / L)) := by
        nlinarith only [div_pos hn_pos hL_pos]
      linarith only [h1, h2, h3, hTp_ge]
    have hexp_bd : (2 * (m : ℝ) * ((t : ℝ) * p + ((t : ℝ) * p) ^ 2) - T_p) / L ^ 2 ≤ -(q * √L + 10) := by
      have hnum : (2 * (m : ℝ) * ((t : ℝ) * p + ((t : ℝ) * p) ^ 2) - T_p) / L ^ 2 ≤
          -(1 / 20000000 : ℝ) * ((n : ℝ) / L ^ 3) := by
        have h1 : 2 * (m : ℝ) * ((t : ℝ) * p + ((t : ℝ) * p) ^ 2) - T_p ≤ -(1 / 20000000 : ℝ) * ((n : ℝ) / L) := by
          linarith only [hmean_small, hTp_ge]
        have h2 := div_le_div_of_nonneg_right h1 (sq_nonneg L)
        have h3 : -(1 / 20000000 : ℝ) * ((n : ℝ) / L) / L ^ 2 = -(1 / 20000000 : ℝ) * ((n : ℝ) / L ^ 3) := by
          field_simp [hL_pos.ne']
        linarith only [h2, h3]
      have hbig : q * √L + 10 ≤ (1 / 20000000 : ℝ) * ((n : ℝ) / L ^ 3) := by
        rw [mul_div_assoc', le_div_iff₀ (pow_pos hL_pos 3)]
        have h0 : q * √L + 10 ≤ 2 * q * L := by
          have : 10 ≤ q * √L := by nlinarith only [hq_pos, hsqL_ge10, hq_sq, hn10k]
          nlinarith only [this, hsqL_le, hq_pos]
        have h1 : (q * √L + 10) * L ^ 3 ≤ 2 * q * L ^ 4 :=
          (mul_le_mul_of_nonneg_right h0 (pow_pos hL_pos 3).le).trans_eq (by ring)
        have h2 : 2 * q * L ^ 4 * 20000000 ≤ q * q := by nlinarith only [h_q_L4b', hq_pos, pow_pos hL_pos 4]
        have h3 : (n : ℝ) = q * q := by nlinarith only [hq_sq]
        linarith only [h1, h2, h3]
      linarith only [hnum, hbig]
    calc _ ≤ Real.exp (q * √L) * Real.exp (-(q * √L + 10)) :=
          mul_le_mul hPref_le (Real.exp_le_exp.mpr hexp_bd) (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (-10 : ℝ) := by rw [← Real.exp_add]; congr 1; ring
      _ < 1 / 40 := exp_neg_ten_lt
  -- Piece 2: Middle dyadic range `< 1 / 40`
  have hP2 : ((t : ℝ) + 1) * (m : ℝ) ^ t *
      (∑ j ∈ Finset.range J,
        if ((r₀ * 2 ^ j : ℕ) : ℝ) < u then
          let rj : ℕ := r₀ * 2 ^ j
          let bj : ℕ := Nat.ceil (T_p / (4 * (J : ℝ) * (rj : ℝ) ^ 2))
          ((m : ℝ) * (Real.exp 1 * (t : ℝ) * p / (rj : ℝ)) ^ rj) ^ bj
        else 0) < 1 / 40 := by
    have hterm : ∀ j ∈ Finset.range J,
        (if ((r₀ * 2 ^ j : ℕ) : ℝ) < u then
          let rj : ℕ := r₀ * 2 ^ j
          let bj : ℕ := Nat.ceil (T_p / (4 * (J : ℝ) * (rj : ℝ) ^ 2))
          ((m : ℝ) * (Real.exp 1 * (t : ℝ) * p / (rj : ℝ)) ^ rj) ^ bj
        else 0) ≤ Real.exp (-(q * √L + L + 10)) := by
      intro j _
      split_ifs with hlt
      · set rj : ℕ := r₀ * 2 ^ j
        set bj : ℕ := Nat.ceil (T_p / (4 * (J : ℝ) * (rj : ℝ) ^ 2))
        have hrj_geL : L ≤ (rj : ℝ) := by
          have hr0_ge : L ≤ (r₀ : ℝ) := by
            have := Nat.lt_floor_add_one L
            push_cast [r₀]; linarith only [this]
          have h2j : (1 : ℝ) ≤ (2 ^ j : ℕ) := by exact_mod_cast Nat.one_le_two_pow
          have hcast : (rj : ℝ) = (r₀ : ℝ) * ((2 ^ j : ℕ) : ℝ) := by push_cast [rj]; rfl
          rw [hcast]; nlinarith only [hr0_ge, h2j, hL_pos]
        have hrj_pos : (0 : ℝ) < (rj : ℝ) := by linarith only [hrj_geL, hL_pos]
        have hbase_le : Real.exp 1 * (t : ℝ) * p / (rj : ℝ) ≤ Real.exp (-2 : ℝ) := by
          have hnum : Real.exp 1 * (t : ℝ) * p ≤ 1 / 10 := by
            have h1 := mul_le_mul he_lt3.le htp_le (by positivity) (by norm_num)
            linarith only [h1]
          have hden : (1 / 10 : ℝ) / L ≤ Real.exp (-2 : ℝ) := by
            have he2 : Real.exp (2 : ℝ) ≤ 9 := by
              have : Real.exp (2 : ℝ) = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
              rw [this]; nlinarith only [he_lt3, Real.exp_pos 1]
            rw [Real.exp_neg, div_le_iff₀ hL_pos, mul_comm, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos 2)]
            nlinarith only [he2, hL100]
          calc Real.exp 1 * (t : ℝ) * p / (rj : ℝ)
              ≤ (1 / 10 : ℝ) / L := div_le_div₀ (by norm_num) hnum hL_pos hrj_geL
            _ ≤ Real.exp (-2 : ℝ) := hden
        have hm_pow : (m : ℝ) * (Real.exp 1 * (t : ℝ) * p / (rj : ℝ)) ^ rj ≤ Real.exp (-(rj : ℝ)) := by
          calc _ ≤ (n : ℝ) * (Real.exp (-2 : ℝ)) ^ rj :=
                mul_le_mul hm_le_n (pow_le_pow_left₀ (by positivity) hbase_le rj) (by positivity) hn_pos.le
            _ = Real.exp (L - 2 * (rj : ℝ)) := by
                rw [← Real.exp_nat_mul, show (n : ℝ) = Real.exp L from (Real.exp_log hn_pos).symm,
                  ← Real.exp_add]; congr 1; ring
            _ ≤ Real.exp (-(rj : ℝ)) := Real.exp_le_exp.mpr (by linarith only [hrj_geL])
        have hrb : T_p / (8 * L * u) ≤ (rj : ℝ) * (bj : ℝ) := by
          have hbj_ge : T_p / (4 * (J : ℝ) * (rj : ℝ) ^ 2) ≤ (bj : ℝ) := Nat.le_ceil _
          have h1 : T_p / (4 * (J : ℝ) * (rj : ℝ)) ≤ (rj : ℝ) * (bj : ℝ) := by
            have hmul := mul_le_mul_of_nonneg_left hbj_ge hrj_pos.le
            have heq : (rj : ℝ) * (T_p / (4 * (J : ℝ) * (rj : ℝ) ^ 2)) = T_p / (4 * (J : ℝ) * (rj : ℝ)) := by
              field_simp [hrj_pos.ne']
            linarith only [hmul, heq]
          have hden : 4 * (J : ℝ) * (rj : ℝ) ≤ 8 * L * u := by
            have hJpos : (0 : ℝ) < (J : ℝ) := by exact_mod_cast (by omega : 0 < J)
            nlinarith only [hJ_le, hlt, hL_pos, hu_pos, hrj_pos]
          exact (div_le_div_of_nonneg_left (by positivity : 0 ≤ T_p) (by positivity) hden).trans h1
        have hbig : q * √L + L + 10 ≤ T_p / (8 * L * u) := by
          have h1 : (1 / 80000000 : ℝ) * (u ^ 3 / L ^ 2) ≤ T_p / (8 * L * u) := by
            have h2 := div_le_div_of_nonneg_right hTp_ge (by positivity : 0 ≤ 8 * L * u)
            have h3 : (1 / 10000000 : ℝ) * ((n : ℝ) / L) / (8 * L * u) = (1 / 80000000 : ℝ) * (u ^ 3 / L ^ 2) := by
              rw [← hu4]; field_simp [hL_pos.ne', hu_pos.ne']; ring
            linarith only [h2, h3]
          have h2 : q * √L + L + 10 ≤ (1 / 80000000 : ℝ) * (u ^ 3 / L ^ 2) := by
            rw [mul_div_assoc', le_div_iff₀ (sq_pos_of_pos hL_pos)]
            have h0 : q * √L + L + 10 ≤ 2 * q * L := by
              have hLq : L ≤ q := by nlinarith only [h_q_L2, hL100]
              have hL10 : L + 10 ≤ q * √L := by nlinarith only [hLq, hsqL_ge10, hL100, hq_pos]
              nlinarith only [hL10, hsqL_le, hq_pos]
            have ha : (q * √L + L + 10) * L ^ 2 ≤ 2 * q * L ^ 3 :=
              (mul_le_mul_of_nonneg_right h0 (sq_nonneg L)).trans_eq (by ring)
            have hb : 2 * q * L ^ 3 * 80000000 ≤ q * u := by nlinarith only [h_u_L3', hq_pos, pow_pos hL_pos 3]
            have hc : u ^ 3 = q * u := by rw [show u ^ 3 = u ^ 2 * u by ring, hu_sq]
            linarith only [ha, hb, hc]
          exact h2.trans h1
        calc ((m : ℝ) * (Real.exp 1 * (t : ℝ) * p / (rj : ℝ)) ^ rj) ^ bj
            ≤ (Real.exp (-(rj : ℝ))) ^ bj := pow_le_pow_left₀ (by positivity) hm_pow bj
          _ = Real.exp ((bj : ℝ) * (-(rj : ℝ))) := (Real.exp_nat_mul _ _).symm
          _ ≤ Real.exp (-(q * √L + L + 10)) := Real.exp_le_exp.mpr (by linarith only [hrb, hbig])
      · exact (Real.exp_pos _).le
    have hsum_le : (∑ j ∈ Finset.range J,
        if ((r₀ * 2 ^ j : ℕ) : ℝ) < u then
          let rj : ℕ := r₀ * 2 ^ j
          let bj : ℕ := Nat.ceil (T_p / (4 * (J : ℝ) * (rj : ℝ) ^ 2))
          ((m : ℝ) * (Real.exp 1 * (t : ℝ) * p / (rj : ℝ)) ^ rj) ^ bj
        else 0) ≤ Real.exp L * Real.exp (-(q * √L + L + 10)) := by
      have h1 : _ ≤ ∑ _j ∈ Finset.range J, Real.exp (-(q * √L + L + 10)) := Finset.sum_le_sum hterm
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
      have hJ_exp : (J : ℝ) ≤ Real.exp L := by
        rw [Real.exp_log hn_pos]
        have : 2 * L ≤ (n : ℝ) := by nlinarith only [h_n_L1, hL_pos]
        linarith only [hJ_le, this]
      exact h1.trans (mul_le_mul_of_nonneg_right hJ_exp (Real.exp_pos _).le)
    calc _ ≤ Real.exp (q * √L) * (Real.exp L * Real.exp (-(q * √L + L + 10))) :=
          mul_le_mul hPref_le hsum_le (Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity) (Real.exp_pos _).le
      _ = Real.exp (-10 : ℝ) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ < 1 / 40 := exp_neg_ten_lt
  -- Piece 3: Large-degree tail `< 1 / 40`
  have hP3 : ((t : ℝ) + 1) * (m : ℝ) ^ t *
      (∑ u_i ∈ Finset.Icc 1 u_max,
        (m : ℝ) ^ u_i * (Real.exp 1 * ((t : ℝ) * (u_i : ℝ)) * p / (e₀ : ℝ)) ^ e₀) < 1 / 40 := by
    have hD_pos : 0 < D := by positivity
    have hE₀_ge : 50 * (t : ℝ) ≤ E₀ := by
      simp only [E₀, T_p, D]
      rw [le_div_iff₀ hD_pos]
      have h1 : 50 * (2 * ((m : ℝ) * p)) ≤ (1 / 4000 : ℝ) * (t : ℝ) := by
        have h2 : 400000 * ((m : ℝ) * p) ≤ (t : ℝ) := by
          have := mul_le_mul_of_nonneg_left hmp_le (by norm_num : (0 : ℝ) ≤ 400000)
          linarith only [this, ht_ge]
        linarith only [h2]
      nlinarith only [h1, Nat.cast_nonneg (α := ℝ) t]
    have hD_le_E₀ : D ≤ E₀ := by
      have hD_le_t : D ≤ (t : ℝ) := by
        have h2 := mul_le_mul_of_nonneg_left hmp_le (by norm_num : (0 : ℝ) ≤ 2)
        have h3 : (2 / 20000000 : ℝ) * (q / √L) ≤ (1 / 50 : ℝ) * (q / √L) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        linarith only [h2, h3, ht_ge]
      linarith only [hD_le_t, hE₀_ge, Nat.cast_nonneg (α := ℝ) t]
    have he₀_ge : E₀ ≤ (e₀ : ℝ) := Nat.le_ceil E₀
    have hE₀_pos : 0 < E₀ := by positivity
    have hE₀_le_n : E₀ ≤ (n : ℝ) := by
      simp only [E₀, T_p, D]
      rw [div_le_iff₀ hD_pos]
      have ht_sq : (t : ℝ) ^ 2 ≤ (n : ℝ) / L := by
        have h1 : (t : ℝ) ^ 2 ≤ ((1 / 30 : ℝ) * (q / √L)) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) ht_le 2
        have h2 : ((1 / 30 : ℝ) * (q / √L)) ^ 2 = (1 / 900 : ℝ) * ((n : ℝ) / L) := by
          rw [mul_pow, div_pow, div_pow, hq_sq, hsqL_sq]; ring
        nlinarith only [h1, h2, div_pos hn_pos hL_pos]
      have h2 : (1 / 4000 : ℝ) * ((n : ℝ) / L) ≤ (n : ℝ) * ((1 / 20000000 : ℝ) * (q / √L)) := by
        have h3 : (1 / 4000 : ℝ) / L ≤ (1 / 20000000 : ℝ) * (q / √L) := by
          rw [div_le_iff₀ hL_pos]
          have hqL : (20000000 : ℝ) ≤ q * √L := by nlinarith only [h_q_L2, hsqL_ge10, hL100]
          have h4 : (1 / 20000000 : ℝ) * (q / √L) * L = q * √L / 20000000 := by
            field_simp [hsqL_pos.ne']; rw [hsqL_sq]
          rw [h4, le_div_iff₀ (by norm_num : (0 : ℝ) < 20000000)]
          linarith only [hqL]
        have := mul_le_mul_of_nonneg_left h3 hn_pos.le
        linarith only [this, show (n : ℝ) * ((1 / 4000 : ℝ) / L) = (1 / 4000 : ℝ) * ((n : ℝ) / L) by ring]
      have hD_ge2 : (1 / 20000000 : ℝ) * (q / √L) ≤ D := by linarith only [hmp_ge]
      nlinarith only [ht_sq, h2, hD_ge2, hn_pos]
    have humax_le : (u_max : ℝ) ≤ 2 * E₀ / u := by
      have h1 : (u_max : ℝ) ≤ (E₀ + D) / u := Nat.floor_le (by positivity)
      have h2 : (E₀ + D) / u ≤ 2 * E₀ / u := div_le_div_of_nonneg_right (by linarith only [hD_le_E₀]) hu_pos.le
      exact h1.trans h2
    have hterm : ∀ u_i ∈ Finset.Icc 1 u_max,
        (m : ℝ) ^ u_i * (Real.exp 1 * ((t : ℝ) * (u_i : ℝ)) * p / (e₀ : ℝ)) ^ e₀ ≤
        Real.exp (-((3 / 16 : ℝ) * (50 * (t : ℝ)) * L)) := by
      intro u_i hu_i
      have hui_le : (u_i : ℝ) ≤ 2 * E₀ / u :=
        (Nat.cast_le.mpr (Finset.mem_Icc.mp hu_i).2).trans humax_le
      have hbase_le : Real.exp 1 * ((t : ℝ) * (u_i : ℝ)) * p / (e₀ : ℝ) ≤ Real.exp (-L / 4) := by
        have h1 : Real.exp 1 * ((t : ℝ) * (u_i : ℝ)) * p ≤ (1 / 10 : ℝ) * (2 * E₀ / u) := by
          have htp : Real.exp 1 * (t : ℝ) * p ≤ 1 / 10 := by
            have := mul_le_mul he_lt3.le htp_le (by positivity) (by norm_num)
            linarith only [this]
          have h2 := mul_le_mul htp hui_le (Nat.cast_nonneg _) (by norm_num)
          linarith only [h2]
        have h2 : Real.exp 1 * ((t : ℝ) * (u_i : ℝ)) * p / (e₀ : ℝ) ≤ 1 / u := by
          calc _ ≤ ((1 / 10 : ℝ) * (2 * E₀ / u)) / E₀ := div_le_div₀ (by positivity) h1 hE₀_pos he₀_ge
            _ = 1 / (5 * u) := by field_simp [hE₀_pos.ne', hu_pos.ne']; ring
            _ ≤ 1 / u := div_le_div_of_nonneg_left (by norm_num) hu_pos (by linarith only [hu_pos])
        have hu_exp : 1 / u = Real.exp (-L / 4) := by
          have hlu : Real.log u = L / 4 := by
            rw [show u = √q from rfl, Real.log_sqrt hq_pos.le, show q = √(n : ℝ) from rfl,
              Real.log_sqrt hn_pos.le]; ring
          rw [show (-L / 4 : ℝ) = -Real.log u by linarith only [hlu], Real.exp_neg, Real.exp_log hu_pos, one_div]
        rwa [← hu_exp]
      have hui_small : (u_i : ℝ) ≤ (e₀ : ℝ) / 16 := by
        have h1 : 2 * E₀ / u ≤ E₀ / 16 := by
          rw [div_le_div_iff₀ hu_pos (by norm_num : (0 : ℝ) < 16)]
          nlinarith only [hu100, hE₀_pos]
        linarith only [hui_le, h1, he₀_ge]
      have hm_pow : (m : ℝ) ^ u_i ≤ Real.exp ((e₀ : ℝ) * L / 16) := by
        calc (m : ℝ) ^ u_i ≤ (n : ℝ) ^ u_i := pow_le_pow_left₀ (Nat.cast_nonneg _) hm_le_n u_i
          _ = Real.exp ((u_i : ℝ) * L) := by rw [Real.exp_nat_mul, Real.exp_log hn_pos]
          _ ≤ Real.exp ((e₀ : ℝ) * L / 16) := Real.exp_le_exp.mpr (by nlinarith only [hui_small, hL_pos])
      have hpow_le : (Real.exp 1 * ((t : ℝ) * (u_i : ℝ)) * p / (e₀ : ℝ)) ^ e₀ ≤ Real.exp (-(e₀ : ℝ) * L / 4) := by
        calc _ ≤ (Real.exp (-L / 4)) ^ e₀ := pow_le_pow_left₀ (by positivity) hbase_le e₀
          _ = Real.exp ((e₀ : ℝ) * (-L / 4)) := (Real.exp_nat_mul _ _).symm
          _ = Real.exp (-(e₀ : ℝ) * L / 4) := by congr 1; ring
      calc _ ≤ Real.exp ((e₀ : ℝ) * L / 16) * Real.exp (-(e₀ : ℝ) * L / 4) :=
            mul_le_mul hm_pow hpow_le (by positivity) (Real.exp_pos _).le
        _ = Real.exp (-((3 / 16 : ℝ) * (e₀ : ℝ) * L)) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ Real.exp (-((3 / 16 : ℝ) * (50 * (t : ℝ)) * L)) :=
            Real.exp_le_exp.mpr (by nlinarith only [hE₀_ge, he₀_ge, hL_pos])
    have hsum_le : (∑ u_i ∈ Finset.Icc 1 u_max,
        (m : ℝ) ^ u_i * (Real.exp 1 * ((t : ℝ) * (u_i : ℝ)) * p / (e₀ : ℝ)) ^ e₀) ≤
        Real.exp L * Real.exp (-((3 / 16 : ℝ) * (50 * (t : ℝ)) * L)) := by
      have h1 := Finset.sum_le_sum hterm
      rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at h1
      have hcard : (u_max : ℝ) ≤ Real.exp L := by
        rw [Real.exp_log hn_pos]
        have h2 : 2 * E₀ / u ≤ E₀ := by rw [div_le_iff₀ hu_pos]; nlinarith only [hu100, hE₀_pos]
        exact humax_le.trans (h2.trans hE₀_le_n)
      exact h1.trans (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le)
    have ht_ge1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
    calc _ ≤ Real.exp (((t : ℝ) + 1) * L) * (Real.exp L * Real.exp (-((3 / 16 : ℝ) * (50 * (t : ℝ)) * L))) :=
          mul_le_mul hPref_t hsum_le (Finset.sum_nonneg fun _ _ => by positivity) (Real.exp_pos _).le
      _ = Real.exp (((t : ℝ) + 2 - (150 / 16 : ℝ) * (t : ℝ)) * L) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-10 : ℝ) := Real.exp_le_exp.mpr (by nlinarith only [ht_ge1, hL100])
      _ < 1 / 40 := exp_neg_ten_lt
  have hdist : ((t : ℝ) + 1) * (m : ℝ) ^ t * P_per_A =
      ((t : ℝ) + 1) * (m : ℝ) ^ t * Real.exp ((2 * (m : ℝ) * ((t : ℝ) * p + ((t : ℝ) * p) ^ 2) - T_p) / L ^ 2) +
      ((t : ℝ) + 1) * (m : ℝ) ^ t * (∑ j ∈ Finset.range J,
        if ((r₀ * 2 ^ j : ℕ) : ℝ) < u then
          let rj : ℕ := r₀ * 2 ^ j
          let bj : ℕ := Nat.ceil (T_p / (4 * (J : ℝ) * (rj : ℝ) ^ 2))
          ((m : ℝ) * (Real.exp 1 * (t : ℝ) * p / (rj : ℝ)) ^ rj) ^ bj
        else 0) +
      ((t : ℝ) + 1) * (m : ℝ) ^ t * (∑ u_i ∈ Finset.Icc 1 u_max,
        (m : ℝ) ^ u_i * (Real.exp 1 * ((t : ℝ) * (u_i : ℝ)) * p / (e₀ : ℝ)) ^ e₀) := by
    simp only [P_per_A]; ring
  linarith only [hdist, hP0, hP1, hP2, hP3]

/-- Helper 3 for `kim_1995_H1`: verify the `BadIndepBlue` upper bound `≤ 1 / 10`. -/
lemma asymp_badIndep_bound {n m s : ℕ} {p : ℝ}
    (hs16 : 16 ≤ s) (hp_pos : 0 < p) (hp_eq : p = √(Real.log (n : ℝ)) / √(n : ℝ))
    (hp_sq : p ^ 2 = Real.log (n : ℝ) / (n : ℝ))
    (hn10k : (10000 : ℝ) ≤ (n : ℝ)) (hL100 : 100 < Real.log (n : ℝ))
    (h_q_L2 : 100 * (20000000 : ℝ) * (Real.log (n : ℝ)) ^ 2 < √(n : ℝ))
    (h_q_L3 : 32000 * (20000000 : ℝ) * (Real.log (n : ℝ)) ^ 3 < √(n : ℝ))
    (hm_le : (m : ℝ) ≤ (n : ℝ) / (20000000 * Real.log (n : ℝ)))
    (hm_le_n : (m : ℝ) ≤ (n : ℝ))
    (hs_ge : (20000000 / 4 : ℝ) * (√(n : ℝ) * √(Real.log (n : ℝ))) ≤ (s : ℝ))
    (hs_le : (s : ℝ) ≤ (20000000 : ℝ) * (√(n : ℝ) * √(Real.log (n : ℝ))))
    (hs_le_n : (s : ℝ) ≤ (n : ℝ))
    (hmp_le : (m : ℝ) * p ≤ (1 / 20000000 : ℝ) * (√(n : ℝ) / √(Real.log (n : ℝ))))
    (hmp_ge : (1 / (2 * 20000000) : ℝ) * (√(n : ℝ) / √(Real.log (n : ℝ))) ≤ (m : ℝ) * p) :
    let L_B : ℝ := 20 * ((s : ℝ) * p)
    let D : ℝ := 2 * ((m : ℝ) * p)
    let T_B : ℝ := (1 / 20 : ℝ) * (s : ℝ) ^ 2
    let E₀ : ℝ := T_B / D
    let e₀ : ℕ := Nat.ceil E₀
    let u_max : ℕ := Nat.floor ((E₀ + D) / L_B)
    (n.choose s : ℝ) *
      (Real.exp ((2 * (m : ℝ) * ((s : ℝ) * p + ((s : ℝ) * p) ^ 2) - T_B) / L_B ^ 2) +
       (∑ u_i ∈ Finset.Icc 1 u_max, (m : ℝ) ^ u_i * (Real.exp 1 * ((s : ℝ) * (u_i : ℝ)) * p / (e₀ : ℝ)) ^ e₀) +
       Real.exp (-((s : ℝ) ^ 2 * p) / 24) +
       Real.exp (-p * ((1 / 10 : ℝ) * (s : ℝ) ^ 2))) ≤ 1 / 10 := by
  intro L_B D T_B E₀ e₀ u_max
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith only [hn10k]
  set L : ℝ := Real.log (n : ℝ)
  have hL_pos : 0 < L := by linarith only [hL100]
  set q : ℝ := √(n : ℝ)
  have hq_pos : 0 < q := Real.sqrt_pos.mpr hn_pos
  have hq_sq : q ^ 2 = (n : ℝ) := Real.sq_sqrt hn_pos.le
  have hsqL_pos : 0 < √L := Real.sqrt_pos.mpr hL_pos
  have hsqL_sq : (√L) ^ 2 = L := Real.sq_sqrt hL_pos.le
  have hsqL_le : √L ≤ L := by nlinarith only [hsqL_sq, hsqL_pos, hL100]
  have hsqL_ge10 : 10 ≤ √L := by nlinarith only [hsqL_sq, hsqL_pos, hL100]
  have he_lt3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
  have hs16R : (16 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs16
  have hns_le : (n.choose s : ℝ) ≤ Real.exp ((s : ℝ) * L) := by
    have h1 : n.choose s ≤ n ^ s := by
      have h2 : n.choose s * s.factorial ≤ n ^ s := by
        rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]; exact Nat.descFactorial_le_pow n s
      exact le_trans (Nat.le_mul_of_pos_right _ (Nat.factorial_pos s)) h2
    have hR : (n.choose s : ℝ) ≤ (n : ℝ) ^ s := by exact_mod_cast h1
    rwa [show (n : ℝ) ^ s = Real.exp ((s : ℝ) * L) by rw [Real.exp_nat_mul, Real.exp_log hn_pos]] at hR
  have hsp_ge : (20000000 / 4 : ℝ) * L ≤ (s : ℝ) * p := by
    rw [hp_eq]
    calc (20000000 / 4 : ℝ) * L = ((20000000 / 4 : ℝ) * (q * √L)) * (√L / q) := by
          field_simp [hq_pos.ne']; rw [hsqL_sq]
      _ ≤ (s : ℝ) * (√L / q) := mul_le_mul_of_nonneg_right hs_ge (by positivity)
  have hsp_ge1 : 1 ≤ (s : ℝ) * p := by nlinarith only [hsp_ge, hL100]
  -- Term 1: External small squares
  have hI1 : (n.choose s : ℝ) *
      Real.exp ((2 * (m : ℝ) * ((s : ℝ) * p + ((s : ℝ) * p) ^ 2) - T_B) / L_B ^ 2) < 1 / 40 := by
    have hnum : 2 * (m : ℝ) * ((s : ℝ) * p + ((s : ℝ) * p) ^ 2) - T_B ≤ -(1 / 40 : ℝ) * (s : ℝ) ^ 2 := by
      have h1 : (s : ℝ) * p + ((s : ℝ) * p) ^ 2 ≤ 2 * ((s : ℝ) * p) ^ 2 := by nlinarith only [hsp_ge1]
      have h2 : 2 * (m : ℝ) * ((s : ℝ) * p + ((s : ℝ) * p) ^ 2) ≤ (4 * (m : ℝ) * p ^ 2) * (s : ℝ) ^ 2 := by
        have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * (m : ℝ))
        linarith only [this, show 2 * (m : ℝ) * (2 * ((s : ℝ) * p) ^ 2) = (4 * (m : ℝ) * p ^ 2) * (s : ℝ) ^ 2 by ring]
      have h3 : 4 * (m : ℝ) * p ^ 2 ≤ 1 / 40 := by
        have : (m : ℝ) * p ^ 2 ≤ 1 / 20000000 := by
          rw [hp_sq]
          calc (m : ℝ) * (L / (n : ℝ)) ≤ ((n : ℝ) / (20000000 * L)) * (L / (n : ℝ)) :=
                mul_le_mul_of_nonneg_right hm_le (by positivity)
            _ = 1 / 20000000 := by field_simp [hn_pos.ne', hL_pos.ne']
        linarith only [this]
      have h4 : (4 * (m : ℝ) * p ^ 2) * (s : ℝ) ^ 2 ≤ (1 / 40 : ℝ) * (s : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
      simp only [T_B]; linarith only [h2, h4]
    have hdiv : (2 * (m : ℝ) * ((s : ℝ) * p + ((s : ℝ) * p) ^ 2) - T_B) / L_B ^ 2 ≤
        -((n : ℝ) / (16000 * L)) := by
      have h1 := div_le_div_of_nonneg_right hnum (sq_nonneg L_B)
      have h2 : (-(1 / 40 : ℝ) * (s : ℝ) ^ 2) / L_B ^ 2 = -((n : ℝ) / (16000 * L)) := by
        simp only [L_B]
        have hsq : (20 * ((s : ℝ) * p)) ^ 2 = 400 * (s : ℝ) ^ 2 * (L / (n : ℝ)) := by
          rw [mul_pow, mul_pow, hp_sq]; ring
        rw [hsq]; field_simp [hs_pos.ne', hL_pos.ne', hn_pos.ne']; ring
      linarith only [h1, h2]
    have hbig : (s : ℝ) * L + 10 ≤ (n : ℝ) / (16000 * L) := by
      rw [le_div_iff₀ (by positivity : 0 < 16000 * L)]
      have h1 : ((s : ℝ) * L + 10) * (16000 * L) ≤ 32000 * 20000000 * q * L ^ 3 := by
        have h10 : 10 ≤ (s : ℝ) * L := by nlinarith only [hs16R, hL100]
        have hsL : (s : ℝ) * L ≤ 20000000 * q * L ^ 2 := by
          have : q * √L ≤ q * L := mul_le_mul_of_nonneg_left hsqL_le hq_pos.le
          have hs' : (s : ℝ) ≤ 20000000 * q * L := by linarith only [hs_le, this]
          exact (mul_le_mul_of_nonneg_right hs' hL_pos.le).trans_eq (by ring)
        have hsum : (s : ℝ) * L + 10 ≤ 2 * (20000000 * q * L ^ 2) := by linarith only [h10, hsL]
        exact (mul_le_mul_of_nonneg_right hsum (by positivity : 0 ≤ 16000 * L)).trans_eq (by ring)
      have h2 : 32000 * 20000000 * q * L ^ 3 ≤ q * q := by nlinarith only [h_q_L3, hq_pos, pow_pos hL_pos 3]
      have h3 : (n : ℝ) = q * q := by nlinarith only [hq_sq]
      linarith only [h1, h2, h3]
    calc _ ≤ Real.exp ((s : ℝ) * L) * Real.exp (-((s : ℝ) * L + 10)) :=
          mul_le_mul hns_le (Real.exp_le_exp.mpr (by linarith only [hdiv, hbig])) (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (-10 : ℝ) := by rw [← Real.exp_add]; congr 1; ring
      _ < 1 / 40 := exp_neg_ten_lt
  -- Term 2: External large squares
  have hI2 : (n.choose s : ℝ) *
      (∑ u_i ∈ Finset.Icc 1 u_max,
        (m : ℝ) ^ u_i * (Real.exp 1 * ((s : ℝ) * (u_i : ℝ)) * p / (e₀ : ℝ)) ^ e₀) < 1 / 40 := by
    have hmp_pos : 0 < (m : ℝ) * p := lt_of_lt_of_le (by positivity) hmp_ge
    have hD_pos : 0 < D := by simp only [D]; linarith only [hmp_pos]
    have hE₀_ge : 100 * (s : ℝ) * L ≤ E₀ := by
      simp only [E₀, T_B, D]
      rw [le_div_iff₀ hD_pos]
      have h1 : 100 * L * (2 * ((m : ℝ) * p)) ≤ (1 / 20 : ℝ) * (s : ℝ) := by
        have h2 : 200 * L * ((m : ℝ) * p) ≤ (200 / 20000000 : ℝ) * (q * √L) := by
          have := mul_le_mul_of_nonneg_left hmp_le (by positivity : 0 ≤ 200 * L)
          have heq : 200 * L * ((1 / 20000000 : ℝ) * (q / √L)) = (200 / 20000000 : ℝ) * (q * √L) := by
            field_simp [hsqL_pos.ne']; rw [hsqL_sq]
          linarith only [this, heq]
        have h4 : (200 / 20000000 : ℝ) * (q * √L) ≤ (1 / 20 : ℝ) * ((20000000 / 4 : ℝ) * (q * √L)) := by
          have hcoef : (200 / 20000000 : ℝ) ≤ (1 / 20 : ℝ) * (20000000 / 4 : ℝ) := by norm_num
          have := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ q * √L)
          linarith only [this]
        linarith only [h2, h4, hs_ge]
      nlinarith only [h1, hs_pos]
    have hD_le_E₀ : D ≤ E₀ := by
      have hD_le_s : D ≤ (s : ℝ) := by
        have h3 : q / √L ≤ q * √L := by
          rw [div_le_iff₀ hsqL_pos]; nlinarith only [hsqL_sq, hL100, hq_pos]
        have h1 : 2 * ((1 / 20000000 : ℝ) * (q / √L)) ≤ (20000000 / 4 : ℝ) * (q * √L) := by
          nlinarith only [h3, div_pos hq_pos hsqL_pos]
        linarith only [hmp_le, h1, hs_ge]
      nlinarith only [hD_le_s, hE₀_ge, hL100, hs_pos]
    have he₀_ge : E₀ ≤ (e₀ : ℝ) := Nat.le_ceil E₀
    have hE₀_pos : 0 < E₀ := by positivity
    have humax_le : (u_max : ℝ) ≤ E₀ / (10 * ((s : ℝ) * p)) := by
      have h1 : (u_max : ℝ) ≤ (E₀ + D) / L_B := Nat.floor_le (by positivity)
      have h2 : (E₀ + D) / L_B ≤ 2 * E₀ / (20 * ((s : ℝ) * p)) :=
        div_le_div_of_nonneg_right (by linarith only [hD_le_E₀]) (by positivity)
      have h3 : 2 * E₀ / (20 * ((s : ℝ) * p)) = E₀ / (10 * ((s : ℝ) * p)) := by ring
      linarith only [h1, h2, h3]
    have hterm : ∀ u_i ∈ Finset.Icc 1 u_max,
        (m : ℝ) ^ u_i * (Real.exp 1 * ((s : ℝ) * (u_i : ℝ)) * p / (e₀ : ℝ)) ^ e₀ ≤
        Real.exp (-(50 * (s : ℝ) * L)) := by
      intro u_i hu_i
      have hui_le : (u_i : ℝ) ≤ E₀ / (10 * ((s : ℝ) * p)) :=
        (Nat.cast_le.mpr (Finset.mem_Icc.mp hu_i).2).trans humax_le
      have hbase_le : Real.exp 1 * ((s : ℝ) * (u_i : ℝ)) * p / (e₀ : ℝ) ≤ Real.exp (-1 : ℝ) := by
        have h1 : Real.exp 1 * ((s : ℝ) * (u_i : ℝ)) * p ≤ (Real.exp 1 / 10) * E₀ := by
          have := mul_le_mul_of_nonneg_left hui_le (by positivity : 0 ≤ Real.exp 1 * (s : ℝ) * p)
          have heq : Real.exp 1 * (s : ℝ) * p * (E₀ / (10 * ((s : ℝ) * p))) = (Real.exp 1 / 10) * E₀ := by
            field_simp [hs_pos.ne', hp_pos.ne']
          linarith only [this, heq]
        have h2 : Real.exp 1 * ((s : ℝ) * (u_i : ℝ)) * p / (e₀ : ℝ) ≤ Real.exp 1 / 10 := by
          calc _ ≤ ((Real.exp 1 / 10) * E₀) / E₀ := div_le_div₀ (by positivity) h1 hE₀_pos he₀_ge
            _ = Real.exp 1 / 10 := mul_div_cancel_right₀ _ hE₀_pos.ne'
        have h3 : Real.exp 1 / 10 ≤ Real.exp (-1 : ℝ) := by
          rw [Real.exp_neg, div_le_iff₀ (by norm_num : (0 : ℝ) < 10), mul_comm, ← div_eq_mul_inv,
            le_div_iff₀ (Real.exp_pos 1)]
          nlinarith only [he_lt3, Real.exp_pos 1]
        exact h2.trans h3
      have hui_L : (u_i : ℝ) * L ≤ (e₀ : ℝ) / 2 := by
        have h1 : (u_i : ℝ) * L ≤ E₀ * (L / (10 * ((s : ℝ) * p))) := by
          have := mul_le_mul_of_nonneg_right hui_le hL_pos.le
          linarith only [this, show E₀ / (10 * ((s : ℝ) * p)) * L = E₀ * (L / (10 * ((s : ℝ) * p))) by ring]
        have h2 : L / (10 * ((s : ℝ) * p)) ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]; nlinarith only [hsp_ge, hL_pos]
        nlinarith only [h1, h2, hE₀_pos, he₀_ge]
      have hm_pow : (m : ℝ) ^ u_i ≤ Real.exp ((e₀ : ℝ) / 2) := by
        calc (m : ℝ) ^ u_i ≤ (n : ℝ) ^ u_i := pow_le_pow_left₀ (Nat.cast_nonneg _) hm_le_n u_i
          _ = Real.exp ((u_i : ℝ) * L) := by rw [Real.exp_nat_mul, Real.exp_log hn_pos]
          _ ≤ Real.exp ((e₀ : ℝ) / 2) := Real.exp_le_exp.mpr hui_L
      have hpow_le : (Real.exp 1 * ((s : ℝ) * (u_i : ℝ)) * p / (e₀ : ℝ)) ^ e₀ ≤ Real.exp (-(e₀ : ℝ)) := by
        calc _ ≤ (Real.exp (-1 : ℝ)) ^ e₀ := pow_le_pow_left₀ (by positivity) hbase_le e₀
          _ = Real.exp (-(e₀ : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
      calc _ ≤ Real.exp ((e₀ : ℝ) / 2) * Real.exp (-(e₀ : ℝ)) :=
            mul_le_mul hm_pow hpow_le (by positivity) (Real.exp_pos _).le
        _ = Real.exp (-(e₀ : ℝ) / 2) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ Real.exp (-(50 * (s : ℝ) * L)) := Real.exp_le_exp.mpr (by linarith only [hE₀_ge, he₀_ge])
    have humax_exp : (u_max : ℝ) ≤ Real.exp (2 * L) := by
      have hD_ge1 : (1 : ℝ) ≤ D := by
        have h3 : 2 * (20000000 : ℝ) ≤ q / √L := by
          rw [le_div_iff₀ hsqL_pos]
          have : 2 * (20000000 : ℝ) * √L ≤ 100 * 20000000 * L ^ 2 := by nlinarith only [hsqL_le, hL100]
          linarith only [this, h_q_L2]
        have h4 : 2 ≤ D := by
          have := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ (1 / 20000000 : ℝ))
          linarith only [this, hmp_ge]
        linarith only [h4]
      have hE_le : E₀ ≤ (s : ℝ) ^ 2 := by
        simp only [E₀, T_B]; rw [div_le_iff₀ hD_pos]; nlinarith only [hD_ge1, sq_nonneg (s : ℝ)]
      have h1 : E₀ / (10 * ((s : ℝ) * p)) ≤ (s : ℝ) ^ 2 :=
        (div_le_self hE₀_pos.le (by linarith only [hsp_ge1])).trans hE_le
      have hn2 : (s : ℝ) ^ 2 ≤ Real.exp (2 * L) := by
        rw [show (2 * L : ℝ) = ((2 : ℕ) : ℝ) * Real.log (n : ℝ) by norm_num [L],
          Real.exp_nat_mul, Real.exp_log hn_pos]
        exact pow_le_pow_left₀ hs_pos.le hs_le_n 2
      exact humax_le.trans (h1.trans hn2)
    have hsum_le : (∑ u_i ∈ Finset.Icc 1 u_max,
        (m : ℝ) ^ u_i * (Real.exp 1 * ((s : ℝ) * (u_i : ℝ)) * p / (e₀ : ℝ)) ^ e₀) ≤
        Real.exp (2 * L) * Real.exp (-(50 * (s : ℝ) * L)) := by
      have h1 := Finset.sum_le_sum hterm
      rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right humax_exp (Real.exp_pos _).le)
    calc _ ≤ Real.exp ((s : ℝ) * L) * (Real.exp (2 * L) * Real.exp (-(50 * (s : ℝ) * L))) :=
          mul_le_mul hns_le hsum_le (Finset.sum_nonneg fun _ _ => by positivity) (Real.exp_pos _).le
      _ = Real.exp ((2 - 49 * (s : ℝ)) * L) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-10 : ℝ) := Real.exp_le_exp.mpr (by nlinarith only [hs16R, hL100])
      _ < 1 / 40 := exp_neg_ten_lt
  -- Term 3: Internal edges
  have hI3 : (n.choose s : ℝ) * Real.exp (-((s : ℝ) ^ 2 * p) / 24) < 1 / 40 := by
    have h1 : (s : ℝ) * L + 10 ≤ (s : ℝ) ^ 2 * p / 24 := by
      have h2 : 100 * (s : ℝ) * L ≤ (s : ℝ) ^ 2 * p / 24 := by
        have : (s : ℝ) ^ 2 * p / 24 = (s : ℝ) * ((s : ℝ) * p / 24) := by ring
        rw [this]
        have h3 : 100 * L ≤ (s : ℝ) * p / 24 := by linarith only [hsp_ge, hL_pos]
        nlinarith only [h3, hs_pos]
      nlinarith only [h2, hs16R, hL100]
    calc _ ≤ Real.exp ((s : ℝ) * L) * Real.exp (-((s : ℝ) * L + 10)) :=
          mul_le_mul hns_le (Real.exp_le_exp.mpr (by linarith only [h1])) (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (-10 : ℝ) := by rw [← Real.exp_add]; congr 1; ring
      _ < 1 / 40 := exp_neg_ten_lt
  -- Term 4: Sequential survival
  have hI4 : (n.choose s : ℝ) * Real.exp (-p * ((1 / 10 : ℝ) * (s : ℝ) ^ 2)) < 1 / 40 := by
    have h1 : (s : ℝ) * L + 10 ≤ p * ((1 / 10 : ℝ) * (s : ℝ) ^ 2) := by
      have h2 : 100 * (s : ℝ) * L ≤ p * ((1 / 10 : ℝ) * (s : ℝ) ^ 2) := by
        have : p * ((1 / 10 : ℝ) * (s : ℝ) ^ 2) = (s : ℝ) * ((s : ℝ) * p / 10) := by ring
        rw [this]
        have h3 : 100 * L ≤ (s : ℝ) * p / 10 := by linarith only [hsp_ge, hL_pos]
        nlinarith only [h3, hs_pos]
      nlinarith only [h2, hs16R, hL100]
    calc _ ≤ Real.exp ((s : ℝ) * L) * Real.exp (-((s : ℝ) * L + 10)) :=
          mul_le_mul hns_le (Real.exp_le_exp.mpr (by linarith only [h1])) (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (-10 : ℝ) := by rw [← Real.exp_add]; congr 1; ring
      _ < 1 / 40 := exp_neg_ten_lt
  linarith only [hI1, hI2, hI3, hI4]

/-- Proof of Kim's (1995) Ramsey lower bound `H1`:
there exists `C > 0` such that for all sufficiently large `n`, there is a triangle-free graph
on `Fin n` with every independent set of cardinality at most `C * √(n * log n)`. -/
lemma kim_1995_H1 : H1 := by
  refine ⟨2 * (20000000 : ℝ), by positivity, ?_⟩
  filter_upwards
    [Filter.eventually_ge_atTop 10000,
     eventually_lt_log 100,
     eventually_log_pow_lt_rpow (a := 1) (by norm_num) 1 (4 * (20000000 : ℝ)),
     eventually_log_pow_lt_rpow (a := 1 / 2) (by norm_num) 4 (Real.exp 4 * (20000000 : ℝ) * (20000000 : ℝ) ^ 3 * 4000),
     eventually_log_pow_lt_rpow (a := 1 / 2) (by norm_num) 2 (100 * (20000000 : ℝ)),
     eventually_log_pow_lt_rpow (a := 1 / 2) (by norm_num) 4 (100000000 : ℝ),
     eventually_log_pow_lt_rpow (a := 1 / 4) (by norm_num) 3 (1000000000 : ℝ),
     eventually_log_pow_lt_rpow (a := 1 / 2) (by norm_num) 3 (32000 * (20000000 : ℝ)),
     eventually_log_pow_lt_rpow (a := 1 / 4) (by norm_num) 0 (100 : ℝ)] with
    n hn10k hL100 h_n_L1 h_q_L4 h_q_L2 h_q_L4b h_u_L3 h_q_L3 h_u100
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h10k : (10000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn10k
  set L : ℝ := Real.log (n : ℝ)
  have hL_pos : 0 < L := by linarith only [hL100]
  set q : ℝ := √(n : ℝ)
  have hq_pos : 0 < q := Real.sqrt_pos.mpr hn_pos
  have hq_sq : q ^ 2 = (n : ℝ) := Real.sq_sqrt hn_pos.le
  set u : ℝ := √q
  have hu_pos : 0 < u := Real.sqrt_pos.mpr hq_pos
  have hu_sq : u ^ 2 = q := Real.sq_sqrt hq_pos.le
  have hnr1 : (n : ℝ) ^ (1 : ℝ) = (n : ℝ) := Real.rpow_one _
  have hnr_half : (n : ℝ) ^ (1 / 2 : ℝ) = q := (Real.sqrt_eq_rpow (n : ℝ)).symm
  have hnr_qtr : (n : ℝ) ^ (1 / 4 : ℝ) = u := by
    rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) * (1 / 2 : ℝ) by norm_num, Real.rpow_mul hn_pos.le,
      ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  rw [hnr1, pow_one] at h_n_L1
  rw [hnr_half] at h_q_L4 h_q_L2 h_q_L4b h_q_L3
  rw [hnr_qtr] at h_u_L3 h_u100
  simp only [pow_zero, mul_one] at h_u100
  have hsqL_pos : 0 < √L := Real.sqrt_pos.mpr hL_pos
  have hsqL_sq : (√L) ^ 2 = L := Real.sq_sqrt hL_pos.le
  have hsqL_le : √L ≤ L := by nlinarith only [hsqL_sq, hsqL_pos, hL100]
  have hsqL_ge10 : 10 ≤ √L := by nlinarith only [hsqL_sq, hsqL_pos, hL100]
  have he_lt3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  -- Explicit parameters
  set p : ℝ := √(L / (n : ℝ))
  have hp_eq : p = √L / q := Real.sqrt_div hL_pos.le (n : ℝ)
  have hp_pos : 0 < p := by rw [hp_eq]; positivity
  have hp_sq : p ^ 2 = L / (n : ℝ) := Real.sq_sqrt (div_nonneg hL_pos.le hn_pos.le)
  have hp_lt1 : p < 1 := by
    rw [hp_eq, div_lt_one hq_pos]
    exact Real.sqrt_lt_sqrt hL_pos.le (by nlinarith only [h_n_L1, hL_pos])
  set m : ℕ := Nat.floor ((n : ℝ) / (20000000 * L))
  have hm_div_ge2 : 2 ≤ (n : ℝ) / (20000000 * L) := by
    rw [le_div_iff₀ (by positivity : 0 < 20000000 * L)]; linarith only [h_n_L1]
  have hm_ge : (n : ℝ) / (2 * 20000000 * L) ≤ (m : ℝ) := by
    have h1 := Nat.sub_one_lt_floor ((n : ℝ) / (20000000 * L))
    have h2 : (n : ℝ) / (2 * 20000000 * L) = (n : ℝ) / (20000000 * L) / 2 := by ring
    linarith only [h1, h2, hm_div_ge2]
  have hm_le : (m : ℝ) ≤ (n : ℝ) / (20000000 * L) := Nat.floor_le (by positivity)
  have hm_le_n : (m : ℝ) ≤ (n : ℝ) := hm_le.trans (div_le_self hn_pos.le (by nlinarith only [hL100]))
  have hm1 : 1 ≤ m := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) / (2 * 20000000 * L) := by
        rw [one_le_div (by positivity : 0 < 2 * 20000000 * L)]; linarith only [h_n_L1]
      linarith only [this, hm_ge]
    exact_mod_cast h1
  set F_max : ℝ := 12 * 20000000 * L
  have hF_pos : 0 < F_max := by positivity
  set k : ℕ := Nat.ceil (20000000 * √((n : ℝ) * L))
  have hsqrt_nL : √((n : ℝ) * L) = q * √L := Real.sqrt_mul hn_pos.le L
  have hk_ge : 20000000 * (q * √L) ≤ (k : ℝ) := by rw [← hsqrt_nL]; exact Nat.le_ceil _
  have hk_le : (k : ℝ) ≤ 2 * 20000000 * (q * √L) := by
    have h1 : (k : ℝ) < 20000000 * √((n : ℝ) * L) + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (1 : ℝ) ≤ 20000000 * (q * √L) := by nlinarith only [hq_pos, hsqL_ge10, hq_sq, h10k]
    rw [hsqrt_nL] at h1; linarith only [h1, h2]
  have hk100 : 100 ≤ k := by
    have : (100 : ℝ) ≤ (k : ℝ) := by nlinarith only [hk_ge, hq_pos, hsqL_ge10, hq_sq, h10k]
    exact_mod_cast this
  set s : ℕ := k / 4 + 1
  have hs16 : 16 ≤ s := by omega
  have h4s : 4 * (s - 1) ≤ k := by omega
  have hs_ge : (20000000 / 4 : ℝ) * (q * √L) ≤ (s : ℝ) := by
    have hR : (k : ℝ) ≤ 4 * (s : ℝ) := by exact_mod_cast (by omega : k ≤ 4 * s)
    linarith only [hk_ge, hR]
  have hs_le_tight : (s : ℝ) ≤ (20000000 / 3 : ℝ) * (q * √L) := by
    have hsub : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ s)]; simp
    have hR : 4 * ((s : ℝ) - 1) ≤ (k : ℝ) := by
      have hcast : (4 * ((s - 1 : ℕ) : ℝ)) ≤ (k : ℝ) := by exact_mod_cast h4s
      rwa [hsub] at hcast
    have hk_tight : (k : ℝ) ≤ 20000000 * (q * √L) + 1 := by
      rw [← hsqrt_nL]; exact (Nat.ceil_lt_add_one (by positivity)).le
    have hbig : (5 : ℝ) ≤ (20000000 / 3 : ℝ) * (q * √L) := by nlinarith only [hq_pos, hsqL_ge10, hq_sq, h10k]
    linarith only [hR, hk_tight, hbig]
  have hs_le' : (s : ℝ) ≤ 20000000 * (q * √L) := by nlinarith only [hs_le_tight, hq_pos, hsqL_pos]
  have hs_m : s - 1 ≤ m := by
    have hR : ((s - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
      have h1 : ((s - 1 : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast Nat.sub_le s 1
      have h2 : 20000000 * (q * √L) ≤ (n : ℝ) / (2 * 20000000 * L) := by
        rw [le_div_iff₀ (by positivity : 0 < 2 * 20000000 * L)]
        have he4 : (1 : ℝ) ≤ Real.exp 4 := by linarith only [Real.add_one_le_exp (4 : ℝ)]
        have hL2 : L ^ 2 ≤ L ^ 4 := by
          have : 1 ≤ L ^ 2 := by nlinarith only [hL100]
          nlinarith only [this, sq_pos_of_pos hL_pos]
        have hbig : 2 * 20000000 * 20000000 * L ^ 2 ≤ q := by
          have hcoef : (2 : ℝ) * 20000000 * 20000000 ≤ Real.exp 4 * 20000000 * 20000000 ^ 3 * 4000 := by
            nlinarith only [he4]
          have := mul_le_mul hcoef hL2 (sq_nonneg L) (by positivity)
          exact this.trans h_q_L4.le
        have hstep : 20000000 * (q * √L) * (2 * 20000000 * L) ≤ (2 * 20000000 * 20000000 * L ^ 2) * q := by
          have : L * √L ≤ L ^ 2 := by nlinarith only [hsqL_le, hL_pos]
          have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 2 * 20000000 * 20000000 * q)
          linarith only [this]
        have hqq : (2 * 20000000 * 20000000 * L ^ 2) * q ≤ q * q := mul_le_mul_of_nonneg_right hbig hq_pos.le
        nlinarith only [hstep, hqq, hq_sq]
      exact h1.trans (hs_le'.trans (h2.trans hm_ge))
    exact_mod_cast hR
  have hs_le_n : (s : ℝ) ≤ (n : ℝ) := by
    have h1 : ((s - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hs_m
    have hsub : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ s)]; simp
    have hm_lt_n : (m : ℝ) + 1 ≤ (n : ℝ) := by
      have : (n : ℝ) / (20000000 * L) ≤ (n : ℝ) / 2 :=
        div_le_div_of_nonneg_left hn_pos.le (by norm_num) (by nlinarith only [hL100])
      linarith only [hm_le, this, h10k]
    linarith only [h1, hsub, hm_lt_n]
  set t : ℕ := Nat.ceil ((s : ℝ) / F_max) + 1
  have ht1 : 1 ≤ t := by omega
  have hs_t : (s : ℝ) / F_max + 1 ≤ (t : ℝ) := by
    have h1 : (s : ℝ) / F_max ≤ (Nat.ceil ((s : ℝ) / F_max) : ℝ) := Nat.le_ceil _
    push_cast [t]; linarith only [h1]
  have hsf_ge : (1 / 48 : ℝ) * (q / √L) ≤ (s : ℝ) / F_max := by
    rw [le_div_iff₀ hF_pos]
    have : (1 / 48 : ℝ) * (q / √L) * F_max = (20000000 / 4 : ℝ) * (q * √L) := by
      simp only [F_max]; field_simp [hsqL_pos.ne']; rw [hsqL_sq]; ring
    linarith only [this, hs_ge]
  have hsf_le_tight : (s : ℝ) / F_max ≤ (1 / 36 : ℝ) * (q / √L) := by
    rw [div_le_iff₀ hF_pos]
    have : (1 / 36 : ℝ) * (q / √L) * F_max = (20000000 / 3 : ℝ) * (q * √L) := by
      simp only [F_max]; field_simp [hsqL_pos.ne']; rw [hsqL_sq]; ring
    linarith only [this, hs_le_tight]
  have hq_div_sqL_big : 1000 ≤ q / √L := by
    rw [le_div_iff₀ hsqL_pos]
    have : 1000 * √L ≤ 100 * 20000000 * L ^ 2 := by nlinarith only [hsqL_le, hL100]
    linarith only [this, h_q_L2]
  have ht_ge : (1 / 50 : ℝ) * (q / √L) ≤ (t : ℝ) := by linarith only [hs_t, hsf_ge, hq_div_sqL_big]
  have ht_le_tight : (t : ℝ) ≤ (1 / 30 : ℝ) * (q / √L) := by
    have h1 : (Nat.ceil ((s : ℝ) / F_max) : ℝ) < (s : ℝ) / F_max + 1 := Nat.ceil_lt_add_one (by positivity)
    push_cast [t]; linarith only [h1, hsf_le_tight, hq_div_sqL_big]
  have ht_le : (t : ℝ) ≤ 2 * ((s : ℝ) / F_max) := by
    have h1 : (Nat.ceil ((s : ℝ) / F_max) : ℝ) < (s : ℝ) / F_max + 1 := Nat.ceil_lt_add_one (by positivity)
    push_cast [t]; linarith only [h1, hsf_ge, hq_div_sqL_big]
  have hF_small : F_max ≤ (1 / 10 : ℝ) * (s : ℝ) := by
    have h1 : 10 ≤ (s : ℝ) / F_max := by linarith only [hsf_ge, hq_div_sqL_big]
    rw [le_div_iff₀ hF_pos] at h1; linarith only [h1]
  have hmp2 : 4 * (m : ℝ) * p ^ 2 ≤ 1 / 20 := by
    have h1 : (m : ℝ) * p ^ 2 ≤ 1 / 20000000 := by
      rw [hp_sq]
      calc (m : ℝ) * (L / (n : ℝ)) ≤ ((n : ℝ) / (20000000 * L)) * (L / (n : ℝ)) :=
            mul_le_mul_of_nonneg_right hm_le (by positivity)
        _ = 1 / 20000000 := by field_simp [hn_pos.ne', hL_pos.ne']
    linarith only [h1]
  have htp_le : (t : ℝ) * p ≤ 1 / 30 := by
    rw [hp_eq]
    calc (t : ℝ) * (√L / q) ≤ ((1 / 30 : ℝ) * (q / √L)) * (√L / q) :=
          mul_le_mul_of_nonneg_right ht_le_tight (by positivity)
      _ = 1 / 30 := by field_simp [hq_pos.ne', hsqL_pos.ne']
  have hmp_le : (m : ℝ) * p ≤ (1 / 20000000 : ℝ) * (q / √L) := by
    rw [hp_eq]
    calc (m : ℝ) * (√L / q) ≤ ((n : ℝ) / (20000000 * L)) * (√L / q) :=
          mul_le_mul_of_nonneg_right hm_le (by positivity)
      _ = (1 / 20000000 : ℝ) * (q / √L) := by
          field_simp [hq_pos.ne', hsqL_pos.ne', hL_pos.ne']; rw [← hq_sq, hsqL_sq]; ring
  have hmp_ge : (1 / (2 * 20000000) : ℝ) * (q / √L) ≤ (m : ℝ) * p := by
    rw [hp_eq]
    calc (1 / (2 * 20000000) : ℝ) * (q / √L) = ((n : ℝ) / (2 * 20000000 * L)) * (√L / q) := by
          field_simp [hq_pos.ne', hsqL_pos.ne', hL_pos.ne']; rw [← hq_sq, hsqL_sq]; ring
      _ ≤ (m : ℝ) * (√L / q) := mul_le_mul_of_nonneg_right hm_ge (by positivity)
  set J : ℕ := Nat.ceil L
  have hJ1 : 1 ≤ J := by
    have : (1 : ℝ) ≤ (J : ℝ) := le_trans (by linarith only [hL100]) (Nat.le_ceil L)
    exact_mod_cast this
  have hJ_le : (J : ℝ) ≤ 2 * L := by
    have h1 : (J : ℝ) < L + 1 := Nat.ceil_lt_add_one hL_pos.le
    linarith only [h1, hL100]
  have hL_lt_u : L < u := by
    have hL2 : L ≤ L ^ 2 := by nlinarith only [hL100]
    have hL3 : L ≤ L ^ 3 := by nlinarith only [hL2, hL100]
    have hu3 : L ^ 3 < u := by nlinarith only [h_u_L3, pow_pos hL_pos 3]
    linarith only [hL3, hu3]
  have hcover : u ≤ ((Nat.floor L + 1 : ℕ) : ℝ) * (2 : ℝ) ^ J := by
    have h2_ge : Real.exp (1 / 2 : ℝ) ≤ 2 := by
      have hsq : Real.exp (1 / 2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ 2 := by
        rw [← Real.exp_nat_mul]; norm_num; linarith only [he_lt3]
      nlinarith only [hsq, Real.exp_pos (1 / 2 : ℝ)]
    have h2J : q ≤ (2 : ℝ) ^ J := by
      calc q = Real.exp (L / 2) := by
              rw [show L / 2 = Real.log q by rw [Real.log_sqrt hn_pos.le], Real.exp_log hq_pos]
        _ ≤ Real.exp ((J : ℝ) * (1 / 2)) := Real.exp_le_exp.mpr (by linarith only [Nat.le_ceil L])
        _ = (Real.exp (1 / 2 : ℝ)) ^ J := Real.exp_nat_mul _ _
        _ ≤ (2 : ℝ) ^ J := pow_le_pow_left₀ (Real.exp_pos _).le h2_ge J
    have hr0_ge1 : (1 : ℝ) ≤ ((Nat.floor L + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hu_le_q : u ≤ q := by nlinarith only [hu_sq, hu_pos, h_u100]
    nlinarith only [hr0_ge1, h2J, hu_le_q, hq_pos]
  -- Call the 3 modular asymptotic helpers and `exists_good_graph_of_bounds`!
  obtain ⟨h_fib, h_comp⟩ := asymp_badPi_bounds (by norm_num : (0 : ℝ) < 20000000) (by norm_num : (1 : ℝ) ≤ 20000000)
    h10k (by omega) hL100 hm_ge hm_le_n hk_ge hs_le' h_q_L4
  have h_badG := asymp_badGraph_bound hm1 ht1 hJ1 hp_pos h10k hL100 h_u100 h_n_L1 h_q_L2 h_q_L4b h_u_L3
    hm_ge hm_le hm_le_n ht_ge ht_le_tight hJ_le htp_le hmp_le hmp_ge
  have h_badIndep := asymp_badIndep_bound hs16 hp_pos hp_eq hp_sq h10k hL100 h_q_L2 h_q_L3
    hm_le hm_le_n hs_ge hs_le' hs_le_n hmp_le hmp_ge
  obtain ⟨G, hG_cf, hG_indep⟩ := exists_good_graph_of_bounds hm1 (by omega : 1 ≤ k) hs16 hs_m h4s ht1 hJ1
    hp_pos hp_lt1 hF_pos hL_pos hL_lt_u hcover hs_t ht_le hF_small hmp2 h_fib h_comp h_badG h_badIndep
  refine ⟨G, hG_cf, fun S hS => ?_⟩
  have hlt : S.card < k := hG_indep S hS
  have hleR : (S.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hlt.le
  rw [← hsqrt_nL] at hk_le
  linarith only [hleR, hk_le]

end KimAsymptotics

end Erdos920Full

theorem OMA.solution : type_of% @Erdos920.erdos_920.variants.k_eq_3 :=
  Erdos920Full.main_reduction Erdos920Full.kim_1995_H1 Erdos920Full.H2_proof
