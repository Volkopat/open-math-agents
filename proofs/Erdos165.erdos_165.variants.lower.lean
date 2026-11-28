import FormalConjectures.ErdosProblems.«165»
import Mathlib

/-!
# Proof of Erdős Problem 165 (Sharp Lower Bound `R(3, k) ≥ (1/2 - ε) k² / log k`)

We formalize the two-bites random-blowup construction of Hefty, Horn, King, and Pfender
(*Improving R(3, k) in just two bites*, 2025), proving that for every `ε > 0` and all
sufficiently large `n`, there exists a triangle-free graph on `n` vertices with independence
number `< (1 + ε) √(n log n)`, which inverts to `R(3, k) ≥ (1/2 - ε) k² / log k`.
-/

-- Problem: Erdős Problem 165 — lower
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/165.lean:87 (declaration Erdos165.erdos_165.variants.lower)
-- Credit: @gdyan2022 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Erdos165LowerProof

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

lemma bernProb_exists_univ_le {X ι : Type*} [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P : ι → (X → Bool) → Prop) :
    bernProb p (fun ω => ∃ i : ι, P i ω) ≤ ∑ i : ι, bernProb p (P i) :=
  (bernProb_mono hp0 hp1 fun _ ⟨i, hi⟩ => ⟨i, Finset.mem_univ i, hi⟩).trans
    (bernProb_exists_le hp0 hp1 Finset.univ P)

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

end DeterministicConstruction

section ExtraProbTools

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

/-- Independence factorization of `bernProb` on `A ⊕ B → Bool`. -/
lemma bernProb_sum_and {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (p : ℝ) (P : (A → Bool) → Prop) (Q : (B → Bool) → Prop) :
    bernProb p (fun ω : A ⊕ B → Bool =>
      P (fun a => ω (Sum.inl a)) ∧ Q (fun b => ω (Sum.inr b))) =
      bernProb p P * bernProb p Q := by
  let e : ((A → Bool) × (B → Bool)) ≃ (A ⊕ B → Bool) :=
    { toFun := fun q x => Sum.casesOn x q.1 q.2
      invFun := fun ω => (fun a => ω (Sum.inl a), fun b => ω (Sum.inr b))
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ω => by funext x; cases x <;> rfl }
  rw [bernProb]
  calc _ = ∑ q : (A → Bool) × (B → Bool), (if P q.1 ∧ Q q.2 then bernW p (e q) else 0) :=
        (Fintype.sum_equiv e _ _ fun q => by
          dsimp only [e, Equiv.coe_fn_mk]
          by_cases hA : P q.1 <;> by_cases hB : Q q.2 <;> simp [hA, hB]).symm
    _ = bernProb p P * bernProb p Q := by
        rw [Fintype.sum_prod_type, bernProb, bernProb, Finset.sum_mul]
        refine Finset.sum_congr rfl fun ωA _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ωB _ => ?_
        have hw : bernW p (e (ωA, ωB)) = bernW p ωA * bernW p ωB := bernW_sum_split p (e (ωA, ωB))
        simp only [e, Equiv.coe_fn_mk] at hw ⊢
        by_cases hA : P ωA <;> by_cases hB : Q ωB <;> simp [hA, hB, hw]

/-- Elementary Chernoff exponent bound: `(1 + η) * log (1 + η) - η ≥ η^2 / 3` for `0 ≤ η ≤ 1/2`. -/
lemma one_add_mul_log_sub_ge {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1 / 2) :
    η ^ 2 / 3 ≤ (1 + η) * Real.log (1 + η) - η := by
  let f : ℝ → ℝ := fun x => (1 + x) * Real.log (1 + x) - x - x ^ 2 / 3
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2),
      HasDerivAt f (Real.log (1 + x) - 2 * x / 3) x := by
    intro x hx
    have hpos : (0 : ℝ) < 1 + x := by linarith [hx.1]
    have h1x : HasDerivAt (fun t : ℝ => 1 + t) 1 x := (hasDerivAt_id x).const_add 1
    have hlog : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + x)) x := by
      simpa using h1x.log hpos.ne'
    have hmul : HasDerivAt (fun t : ℝ => (1 + t) * Real.log (1 + t))
        (1 * Real.log (1 + x) + (1 + x) * (1 / (1 + x))) x := h1x.mul hlog
    have hsq : HasDerivAt (fun t : ℝ => t ^ 2 / 3) (2 * x / 3) x := by
      have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
        simpa [pow_one] using hasDerivAt_pow 2 x
      exact hpow.div_const 3
    have hall : HasDerivAt f (1 * Real.log (1 + x) + (1 + x) * (1 / (1 + x)) - 1 - 2 * x / 3) x :=
      (hmul.sub (hasDerivAt_id x)).sub hsq
    convert hall using 1
    rw [one_mul, mul_one_div_cancel hpos.ne']
    ring
  have hmono : MonotoneOn f (Set.Icc (0 : ℝ) (1 / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2)) ?_ ?_ ?_
    · exact fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Set.Icc (0 : ℝ) (1 / 2) := interior_subset hx
      rw [(hderiv x hx').deriv]
      have hpos : (0 : ℝ) < 1 + x := by linarith [hx'.1]
      have hlog_inv := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
      rw [Real.log_inv] at hlog_inv
      have hlog_ge : x / (1 + x) ≤ Real.log (1 + x) := by
        have hrew : (1 + x)⁻¹ - 1 = -(x / (1 + x)) := by field_simp [hpos.ne']; ring
        linarith
      have hfrac : 2 * x / 3 ≤ x / (1 + x) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hpos]
        nlinarith [hx'.1, hx'.2]
      linarith
  have hf0 : f 0 = 0 := by simp [f]
  have hle := hmono (Set.left_mem_Icc.mpr (by norm_num)) ⟨h0, h1⟩ h0
  rw [hf0] at hle
  dsimp only [f] at hle
  linarith

/-- Multiplicative Chernoff upper tail for `bernProb`:
`P(|{x ∈ S : ω x}| ≥ (1 + η) * (|S| * p)) ≤ exp(-η^2 / 3 * (|S| * p))` for `0 < η ≤ 1/2`. -/
lemma bernProb_binom_ge_chernoff {X : Type*} [Fintype X] [DecidableEq X] {p η : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hη0 : 0 < η) (hη1 : η ≤ 1 / 2) (S : Finset X) :
    bernProb p (fun ω : X → Bool =>
      (1 + η) * ((S.card : ℝ) * p) ≤ ((S.filter (fun x => ω x = true)).card : ℝ)) ≤
      Real.exp (-(η ^ 2 / 3) * ((S.card : ℝ) * p)) := by
  set μ : ℝ := (S.card : ℝ) * p
  have hμ0 : 0 ≤ μ := mul_nonneg (Nat.cast_nonneg _) hp0
  have h1η_pos : 0 < 1 + η := by linarith
  let g : X → Bool → ℝ := fun x b => if x ∈ S then (if b then 1 + η else 1) else 1
  let Z : (X → Bool) → ℝ := fun ω => ∏ x : X, g x (ω x)
  have hZ_eq : ∀ ω : X → Bool, Z ω = (1 + η) ^ (S.filter (fun x => ω x = true)).card := by
    intro ω
    dsimp only [Z]
    rw [← Finset.prod_subset (Finset.subset_univ S)]
    · rw [← Finset.prod_filter_mul_prod_filter_not S (fun x => ω x = true)]
      have h1 : (∏ x ∈ S.filter (fun x => ω x = true), g x (ω x)) =
          (1 + η) ^ (S.filter (fun x => ω x = true)).card := by
        calc ∏ x ∈ S.filter (fun x => ω x = true), g x (ω x)
            = ∏ _x ∈ S.filter (fun x => ω x = true), (1 + η) :=
              Finset.prod_congr rfl fun x hx => by
                rcases Finset.mem_filter.mp hx with ⟨hxS, hxt⟩
                simp [g, hxS, hxt]
          _ = (1 + η) ^ (S.filter (fun x => ω x = true)).card := Finset.prod_const _
      have h2 : (∏ x ∈ S.filter (fun x => ¬ ω x = true), g x (ω x)) = 1 :=
        Finset.prod_eq_one fun x hx => by
          rcases Finset.mem_filter.mp hx with ⟨hxS, hxf⟩
          simp [g, hxS, hxf]
      rw [h1, h2, mul_one]
    · intro x _ hxS; simp [g, hxS]
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => by rw [hZ_eq]; positivity
  have hEZ : bernExp p Z ≤ Real.exp (η * μ) := by
    rw [show bernExp p Z = ∏ x : X, (p * g x true + (1 - p) * g x false) from bernExp_prod p g]
    rw [← Finset.prod_subset (Finset.subset_univ S)]
    · calc ∏ x ∈ S, (p * g x true + (1 - p) * g x false)
          = ∏ _x ∈ S, (1 + p * η) := Finset.prod_congr rfl fun x hx => by simp [g, hx]; ring
        _ = (1 + p * η) ^ S.card := Finset.prod_const _
        _ ≤ (Real.exp (p * η)) ^ S.card := by
            refine pow_le_pow_left₀ (by nlinarith) ?_ S.card
            linarith [Real.add_one_le_exp (p * η)]
        _ = Real.exp ((S.card : ℝ) * (p * η)) := (Real.exp_nat_mul _ _).symm
        _ = Real.exp (η * μ) := by congr 1; dsimp only [μ]; ring
    · intro x _ hxS; simp [g, hxS]
  set thr : ℝ := Real.exp ((1 + η) * μ * Real.log (1 + η))
  have himp : ∀ ω : X → Bool,
      (1 + η) * μ ≤ ((S.filter (fun x => ω x = true)).card : ℝ) → thr ≤ Z ω := by
    intro ω hge
    rw [hZ_eq, ← Real.rpow_natCast, Real.rpow_def_of_pos h1η_pos]
    dsimp only [thr]
    refine Real.exp_le_exp.mpr ?_
    have hlog0 : 0 ≤ Real.log (1 + η) := Real.log_nonneg (by linarith)
    nlinarith
  have h1 := bernProb_mono hp0 hp1 himp
  have hmk := bernProb_markov hp0 hp1 hZ0 (Real.exp_pos ((1 + η) * μ * Real.log (1 + η)))
  calc bernProb p (fun ω => (1 + η) * μ ≤ ((S.filter (fun x => ω x = true)).card : ℝ))
      ≤ bernExp p Z / thr := h1.trans hmk
    _ ≤ Real.exp (η * μ) / thr := div_le_div_of_nonneg_right hEZ (Real.exp_pos _).le
    _ = Real.exp (η * μ - (1 + η) * μ * Real.log (1 + η)) := by rw [← Real.exp_sub]
    _ ≤ Real.exp (-(η ^ 2 / 3) * μ) := by
        refine Real.exp_le_exp.mpr ?_
        have hkl := one_add_mul_log_sub_ge hη0.le hη1
        nlinarith

/-- Multiplicative Chernoff upper tail for uniform random maps `φ : Fin n → Fin m`:
for `x : Fin m` and `0 < η ≤ 1/2`, the number of maps with `|φ⁻¹(x)| ≥ (1 + η) * (n / m)`
is at most `exp(-η^2 / 3 * (n / m)) * m^n`. -/
lemma card_maps_fiber_ge_chernoff {n m : ℕ} (hm : 1 ≤ m) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (x : Fin m) :
    ((Finset.univ.filter (fun φ : Fin n → Fin m =>
      (1 + η) * ((n : ℝ) / (m : ℝ)) ≤ ((Finset.univ.filter (fun v : Fin n => φ v = x)).card : ℝ))).card : ℝ) ≤
      Real.exp (-(η ^ 2 / 3) * ((n : ℝ) / (m : ℝ))) * (m : ℝ) ^ n := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  set μ : ℝ := (n : ℝ) / (m : ℝ)
  have hμ0 : 0 ≤ μ := div_nonneg (Nat.cast_nonneg _) hm_pos.le
  have h1η_pos : 0 < 1 + η := by linarith
  let Z : (Fin n → Fin m) → ℝ := fun φ =>
    ∏ v : Fin n, (if φ v = x then 1 + η else 1)
  have hZ_eq : ∀ φ : Fin n → Fin m,
      Z φ = (1 + η) ^ (Finset.univ.filter (fun v : Fin n => φ v = x)).card := by
    intro φ
    dsimp only [Z]
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun v : Fin n => φ v = x)]
    have h1 : (∏ v ∈ Finset.univ.filter (fun v : Fin n => φ v = x), if φ v = x then 1 + η else 1) =
        (1 + η) ^ (Finset.univ.filter (fun v : Fin n => φ v = x)).card := by
      calc _ = ∏ _v ∈ Finset.univ.filter (fun v : Fin n => φ v = x), (1 + η) :=
              Finset.prod_congr rfl fun v hv => by simp [(Finset.mem_filter.mp hv).2]
        _ = _ := Finset.prod_const _
    have h2 : (∏ v ∈ Finset.univ.filter (fun v : Fin n => ¬ φ v = x), if φ v = x then 1 + η else 1) = 1 :=
      Finset.prod_eq_one fun v hv => by simp [(Finset.mem_filter.mp hv).2]
    rw [h1, h2, mul_one]
  have hsumZ : (∑ φ : Fin n → Fin m, Z φ) = ((m : ℝ) + η) ^ n := by
    have h := Fintype.prod_sum (fun (_ : Fin n) (y : Fin m) => if y = x then (1 + η : ℝ) else 1)
    change (∑ φ : Fin n → Fin m, ∏ v : Fin n, if φ v = x then 1 + η else 1) = ((m : ℝ) + η) ^ n
    rw [← h]
    have hinner : ∀ _v : Fin n, (∑ y : Fin m, if y = x then (1 + η : ℝ) else 1) = (m : ℝ) + η := by
      intro _
      have hsplit : (∑ y : Fin m, if y = x then (1 + η : ℝ) else 1) =
          (∑ y : Fin m, (1 : ℝ)) + ∑ y : Fin m, (if y = x then η else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun y _ => by split_ifs <;> ring
      rw [hsplit, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
        Finset.sum_ite_eq']
      simp
    calc ∏ v : Fin n, ∑ y : Fin m, (if y = x then (1 + η : ℝ) else 1)
        = ∏ _v : Fin n, ((m : ℝ) + η) := Finset.prod_congr rfl fun v _ => hinner v
      _ = ((m : ℝ) + η) ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsumZ_le : (∑ φ : Fin n → Fin m, Z φ) ≤ Real.exp (η * μ) * (m : ℝ) ^ n := by
    rw [hsumZ]
    have hfac : (m : ℝ) + η = (m : ℝ) * (1 + η / (m : ℝ)) := by field_simp [hm_pos.ne']
    rw [hfac, mul_pow, mul_comm ((m : ℝ) ^ n)]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hm_pos.le n)
    calc (1 + η / (m : ℝ)) ^ n
        ≤ (Real.exp (η / (m : ℝ))) ^ n := by
          refine pow_le_pow_left₀ (by positivity) ?_ n
          linarith [Real.add_one_le_exp (η / (m : ℝ))]
      _ = Real.exp ((n : ℝ) * (η / (m : ℝ))) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp (η * μ) := by congr 1; dsimp only [μ]; ring
  set thr : ℝ := Real.exp ((1 + η) * μ * Real.log (1 + η))
  set Good := Finset.univ.filter (fun φ : Fin n → Fin m =>
    (1 + η) * μ ≤ ((Finset.univ.filter (fun v : Fin n => φ v = x)).card : ℝ))
  have hmarkov : (Good.card : ℝ) * thr ≤ ∑ φ : Fin n → Fin m, Z φ := by
    calc (Good.card : ℝ) * thr
        = ∑ _φ ∈ Good, thr := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ φ ∈ Good, Z φ := by
          refine Finset.sum_le_sum fun φ hφ => ?_
          have hge := (Finset.mem_filter.mp hφ).2
          rw [hZ_eq, ← Real.rpow_natCast, Real.rpow_def_of_pos h1η_pos]
          dsimp only [thr]
          refine Real.exp_le_exp.mpr ?_
          have hlog0 : 0 ≤ Real.log (1 + η) := Real.log_nonneg (by linarith)
          nlinarith
      _ ≤ ∑ φ : Fin n → Fin m, Z φ :=
          Finset.sum_le_univ_sum_of_nonneg fun φ => by rw [hZ_eq]; positivity
  have hle_div : (Good.card : ℝ) ≤ (Real.exp (η * μ) / thr) * (m : ℝ) ^ n := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (Real.exp_pos _)]
    exact hmarkov.trans hsumZ_le
  calc (Good.card : ℝ)
      ≤ (Real.exp (η * μ) / thr) * (m : ℝ) ^ n := hle_div
    _ = Real.exp (η * μ - (1 + η) * μ * Real.log (1 + η)) * (m : ℝ) ^ n := by
        rw [← Real.exp_sub]
    _ ≤ Real.exp (-(η ^ 2 / 3) * μ) * (m : ℝ) ^ n := by
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (pow_nonneg hm_pos.le n)
        have hkl := one_add_mul_log_sub_ge hη0.le hη1
        nlinarith

/-- Lower-tail MGF bound for `bernProb`: for any `λ > 0`, `S : Finset X`, and `T : ℝ`,
`P(|{x ∈ S : ω x}| ≤ T) ≤ exp(λ * T - p * (1 - exp(-λ)) * |S|)`. -/
lemma bernProb_binom_le_mgf {X : Type*} [Fintype X] [DecidableEq X] {p lam T : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hlam : 0 < lam) (S : Finset X) :
    bernProb p (fun ω : X → Bool =>
      ((S.filter (fun x => ω x = true)).card : ℝ) ≤ T) ≤
      Real.exp (lam * T - p * (1 - Real.exp (-lam)) * (S.card : ℝ)) := by
  let g : X → Bool → ℝ := fun x b => if x ∈ S then (if b then Real.exp (-lam) else 1) else 1
  let Z : (X → Bool) → ℝ := fun ω => ∏ x : X, g x (ω x)
  have hZ_eq : ∀ ω : X → Bool,
      Z ω = Real.exp (-lam * ((S.filter (fun x => ω x = true)).card : ℝ)) := by
    intro ω
    dsimp only [Z]
    rw [← Finset.prod_subset (Finset.subset_univ S)]
    · rw [← Finset.prod_filter_mul_prod_filter_not S (fun x => ω x = true)]
      have h1 : (∏ x ∈ S.filter (fun x => ω x = true), g x (ω x)) =
          Real.exp (-lam * ((S.filter (fun x => ω x = true)).card : ℝ)) := by
        calc ∏ x ∈ S.filter (fun x => ω x = true), g x (ω x)
            = ∏ _x ∈ S.filter (fun x => ω x = true), Real.exp (-lam) :=
              Finset.prod_congr rfl fun x hx => by
                rcases Finset.mem_filter.mp hx with ⟨hxS, hxt⟩
                simp [g, hxS, hxt]
          _ = (Real.exp (-lam)) ^ (S.filter (fun x => ω x = true)).card := Finset.prod_const _
          _ = Real.exp (((S.filter (fun x => ω x = true)).card : ℝ) * (-lam)) :=
              (Real.exp_nat_mul _ _).symm
          _ = Real.exp (-lam * ((S.filter (fun x => ω x = true)).card : ℝ)) := by congr 1; ring
      have h2 : (∏ x ∈ S.filter (fun x => ¬ ω x = true), g x (ω x)) = 1 :=
        Finset.prod_eq_one fun x hx => by
          rcases Finset.mem_filter.mp hx with ⟨hxS, hxf⟩
          simp [g, hxS, hxf]
      rw [h1, h2, mul_one]
    · intro x _ hxS; simp [g, hxS]
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => by rw [hZ_eq]; exact (Real.exp_pos _).le
  have hEZ : bernExp p Z ≤ Real.exp (-p * (1 - Real.exp (-lam)) * (S.card : ℝ)) := by
    rw [show bernExp p Z = ∏ x : X, (p * g x true + (1 - p) * g x false) from bernExp_prod p g]
    rw [← Finset.prod_subset (Finset.subset_univ S)]
    · have hbase_nonneg : 0 ≤ 1 - p * (1 - Real.exp (-lam)) := by
        have he0 : 0 ≤ Real.exp (-lam) := (Real.exp_pos _).le
        nlinarith
      calc ∏ x ∈ S, (p * g x true + (1 - p) * g x false)
          = ∏ _x ∈ S, (1 - p * (1 - Real.exp (-lam))) :=
            Finset.prod_congr rfl fun x hx => by simp [g, hx]; ring
        _ = (1 - p * (1 - Real.exp (-lam))) ^ S.card := Finset.prod_const _
        _ ≤ (Real.exp (-p * (1 - Real.exp (-lam)))) ^ S.card := by
            refine pow_le_pow_left₀ hbase_nonneg ?_ S.card
            linarith [Real.add_one_le_exp (-p * (1 - Real.exp (-lam)))]
        _ = Real.exp ((S.card : ℝ) * (-p * (1 - Real.exp (-lam)))) := (Real.exp_nat_mul _ _).symm
        _ = Real.exp (-p * (1 - Real.exp (-lam)) * (S.card : ℝ)) := by congr 1; ring
    · intro x _ hxS; simp [g, hxS]
  have himp : ∀ ω : X → Bool,
      ((S.filter (fun x => ω x = true)).card : ℝ) ≤ T → Real.exp (-lam * T) ≤ Z ω := by
    intro ω hle
    rw [hZ_eq]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have h1 := bernProb_mono hp0 hp1 himp
  have hmk := bernProb_markov hp0 hp1 hZ0 (Real.exp_pos (-lam * T))
  calc _ ≤ bernExp p Z / Real.exp (-lam * T) := h1.trans hmk
    _ ≤ Real.exp (-p * (1 - Real.exp (-lam)) * (S.card : ℝ)) / Real.exp (-lam * T) :=
        div_le_div_of_nonneg_right hEZ (Real.exp_pos _).le
    _ = Real.exp (lam * T - p * (1 - Real.exp (-lam)) * (S.card : ℝ)) := by
        rw [← Real.exp_sub]; congr 1; ring

/-- Forward pairs `(i, j)` with `i < j` that already share a common earlier neighbor `r < i`
in `ω : EdgeIdx s → Bool`. Depends strictly on edges with left endpoint `< i`. -/
def triCand {s : ℕ} (ω : EdgeIdx s → Bool) (i : Fin s) : Finset (Fin s) :=
  Finset.univ.filter fun j =>
    ∃ _h : i < j, ∃ r : Fin s, ∃ hri : r < i, ∃ hrj : r < j,
      ω ⟨(r, i), hri⟩ = true ∧ ω ⟨(r, j), hrj⟩ = true

lemma triCand_congr {s : ℕ} {ω₁ ω₂ : EdgeIdx s → Bool} {i : Fin s}
    (h : ∀ e : EdgeIdx s, e.1.1 < i → ω₁ e = ω₂ e) :
    triCand ω₁ i = triCand ω₂ i := by
  ext j; simp only [triCand, Finset.mem_filter, Finset.mem_univ, true_and]
  refine exists_congr fun _ => exists_congr fun r => exists_congr fun hri => exists_congr fun hrj => ?_
  rw [h ⟨(r, i), hri⟩ hri, h ⟨(r, j), hrj⟩ hri]

/-- Forward edges `(i, j)` in `triCand ω i` that are actually present in `ω`. -/
def triHits {s : ℕ} (ω : EdgeIdx s → Bool) (i : Fin s) : Finset (Fin s) :=
  (triCand ω i).filter fun j => ∃ h : i < j, ω ⟨(i, j), h⟩ = true

lemma triHits_congr {s : ℕ} {ω₁ ω₂ : EdgeIdx s → Bool} {i : Fin s}
    (h : ∀ e : EdgeIdx s, e.1.1 ≤ i → ω₁ e = ω₂ e) :
    triHits ω₁ i = triHits ω₂ i := by
  have hc : triCand ω₁ i = triCand ω₂ i := triCand_congr fun e he => h e (le_of_lt he)
  simp only [triHits, hc]
  ext j; simp only [Finset.mem_filter]
  refine and_congr_right fun _ => exists_congr fun hij => ?_
  rw [h ⟨(i, j), hij⟩ le_rfl]

/-- Stopping condition at stage `i`: total `triCand` count up to and including `i` is `≤ M₀`.
Depends strictly on edges with left endpoint `< i`. -/
def stopOk {s : ℕ} (M₀ : ℕ) (ω : EdgeIdx s → Bool) (i : Fin s) : Prop :=
  (∑ r : Fin s, if r ≤ i then (triCand ω r).card else 0) ≤ M₀

lemma stopOk_congr {s : ℕ} (M₀ : ℕ) {ω₁ ω₂ : EdgeIdx s → Bool} {i : Fin s}
    (h : ∀ e : EdgeIdx s, e.1.1 < i → ω₁ e = ω₂ e) :
    stopOk M₀ ω₁ i ↔ stopOk M₀ ω₂ i := by
  simp only [stopOk]
  have hsum : (∑ r : Fin s, if r ≤ i then (triCand ω₁ r).card else 0) =
      ∑ r : Fin s, if r ≤ i then (triCand ω₂ r).card else 0 := by
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs with hri
    · rw [triCand_congr fun e her => h e (lt_of_lt_of_le her hri)]
    · rfl
  rw [hsum]

/-- Stopped exponential martingale factor at stage `i`. -/
noncomputable def triFac {s : ℕ} (M₀ : ℕ) (p lam : ℝ) (ω : EdgeIdx s → Bool) (i : Fin s) : ℝ :=
  if stopOk M₀ ω i then
    Real.exp (lam * ((triHits ω i).card : ℝ)) / (1 - p + p * Real.exp lam) ^ (triCand ω i).card
  else 1

lemma triFac_congr {s : ℕ} (M₀ : ℕ) (p lam : ℝ) {ω₁ ω₂ : EdgeIdx s → Bool} {i : Fin s}
    (h : ∀ e : EdgeIdx s, e.1.1 ≤ i → ω₁ e = ω₂ e) :
    triFac M₀ p lam ω₁ i = triFac M₀ p lam ω₂ i := by
  have hs := stopOk_congr M₀ (i := i) fun e he => h e (le_of_lt he)
  have hc := triCand_congr (i := i) fun e he => h e (le_of_lt he)
  have hh := triHits_congr (i := i) h
  simp only [triFac, hs, hc, hh]

lemma triFac_nonneg {s : ℕ} (M₀ : ℕ) {p lam : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ω : EdgeIdx s → Bool) (i : Fin s) : 0 ≤ triFac M₀ p lam ω i := by
  simp only [triFac]
  split_ifs
  · refine div_nonneg (Real.exp_pos _).le (pow_nonneg ?_ _)
    have : 0 ≤ p * Real.exp lam := mul_nonneg hp0 (Real.exp_pos _).le
    linarith
  · exact zero_le_one

/-- Exact stopped exponential martingale identity: `E[∏ i, triFac M₀ p lam ω i] = 1`. -/
lemma bernExp_triFac_prod_eq_one {s : ℕ} (M₀ : ℕ) {p lam : ℝ} (hp0 : 0 ≤ p) (_hp1 : p ≤ 1)
    (hlam : 0 ≤ lam) :
    bernExp p (fun ω : EdgeIdx s → Bool => ∏ i : Fin s, triFac M₀ p lam ω i) = 1 := by
  have hden_pos : 0 < 1 - p + p * Real.exp lam := by
    have : 1 ≤ Real.exp lam := Real.one_le_exp hlam
    nlinarith
  have hind : ∀ k : ℕ, k ≤ s →
      bernExp p (fun ω : EdgeIdx s → Bool => ∏ i : Fin s, if i.val < k then triFac M₀ p lam ω i else 1) = 1 := by
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
          right_inv := fun x => by rcases x with ⟨e, he⟩ | ⟨e, he⟩ <;> simp [he] }
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
      have hprod_step : ∀ ω : EdgeIdx s → Bool,
          (∏ i : Fin s, if i.val < k + 1 then triFac M₀ p lam ω i else 1) =
          (∏ i : Fin s, if i.val < k then triFac M₀ p lam ω i else 1) * triFac M₀ p lam ω i₀ := by
        intro ω
        have h1 : triFac M₀ p lam ω i₀ =
            ∏ i : Fin s, if i = i₀ then triFac M₀ p lam ω i else 1 := by
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
          (∏ i : Fin s, if i.val < k then triFac M₀ p lam (eProd (ωL, ωR)) i else 1) =
          (∏ i : Fin s, if i.val < k then triFac M₀ p lam (eProd (ωL, ωR₀)) i else 1) := by
        intro ωL ωR
        refine Finset.prod_congr rfl fun i _ => ?_
        split_ifs with hlt
        · refine triFac_congr M₀ p lam fun e he => ?_
          have hne : e.1.1.val ≠ k := by have : e.1.1.val ≤ i.val := he; omega
          simp [eProd, hne]
        · rfl
      have hcand_indep : ∀ (ωL : L → Bool) (ωR : R → Bool),
          triCand (eProd (ωL, ωR)) i₀ = triCand (eProd (ωL, ωR₀)) i₀ := by
        intro ωL ωR
        refine triCand_congr fun e he => ?_
        have hne : e.1.1.val ≠ k := by have : e.1.1.val < k := he; omega
        simp [eProd, hne]
      have hstop_indep : ∀ (ωL : L → Bool) (ωR : R → Bool),
          stopOk M₀ (eProd (ωL, ωR)) i₀ ↔ stopOk M₀ (eProd (ωL, ωR₀)) i₀ := by
        intro ωL ωR
        refine stopOk_congr M₀ fun e he => ?_
        have hne : e.1.1.val ≠ k := by have : e.1.1.val < k := he; omega
        simp [eProd, hne]
      have hinner_one : ∀ ωL : L → Bool,
          (∑ ωR : R → Bool, bernW p ωR * triFac M₀ p lam (eProd (ωL, ωR)) i₀) = 1 := by
        intro ωL
        by_cases hst : stopOk M₀ (eProd (ωL, ωR₀)) i₀
        · let S_L : Finset (Fin s) := triCand (eProd (ωL, ωR₀)) i₀
          let T_R : Finset R := Finset.univ.filter fun e => e.1.1.2 ∈ S_L
          have hcard_eq : T_R.card = S_L.card := by
            refine Finset.card_bij (fun e _ => e.1.1.2) ?_ ?_ ?_
            · intro e he; exact (Finset.mem_filter.mp he).2
            · intro e₁ _ e₂ _ heq
              apply Subtype.ext; apply Subtype.ext; apply Prod.ext
              · exact Fin.ext (e₁.2.trans e₂.2.symm)
              · exact heq
            · intro j hj
              rcases (Finset.mem_filter.mp hj).2 with ⟨hij, _⟩
              exact ⟨⟨⟨(i₀, j), hij⟩, rfl⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩
          have hhits_eq : ∀ ωR : R → Bool,
              (triHits (eProd (ωL, ωR)) i₀).card = (T_R.filter fun e => ωR e = true).card := by
            intro ωR
            refine Finset.card_bij (fun j hj => ?_) ?_ ?_ ?_
            · have hjm : j ∈ S_L := by
                dsimp only [S_L]; rw [← hcand_indep ωL ωR]; exact (Finset.mem_filter.mp hj).1
              have hij : i₀ < j := (Finset.mem_filter.mp hjm).2.choose
              exact ⟨⟨(i₀, j), hij⟩, rfl⟩
            · intro j hj
              rcases Finset.mem_filter.mp hj with ⟨hjc, hij, htrue⟩
              have hjm : j ∈ S_L := by dsimp only [S_L]; rwa [← hcand_indep ωL ωR]
              refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjm⟩, ?_⟩
              simpa [eProd, i₀] using htrue
            · intro j₁ _ j₂ _ heq
              exact congrArg (fun x : R => x.1.1.2) heq
            · intro e he
              rcases Finset.mem_filter.mp he with ⟨heT, htrue⟩
              have hjS : e.1.1.2 ∈ S_L := (Finset.mem_filter.mp heT).2
              have he1 : e.1.1.1 = i₀ := Fin.ext e.2
              have hij : i₀ < e.1.1.2 := he1 ▸ e.1.2
              refine ⟨e.1.1.2, Finset.mem_filter.mpr ⟨by rwa [hcand_indep ωL ωR], hij, ?_⟩, ?_⟩
              · have heq : (⟨(i₀, e.1.1.2), hij⟩ : EdgeIdx s) = e.1 :=
                  Subtype.ext (Prod.ext he1.symm rfl)
                rw [heq]; simp only [eProd, Equiv.coe_fn_mk, dif_pos e.2]; exact htrue
              · apply Subtype.ext; apply Subtype.ext; exact Prod.ext he1.symm rfl
          let gR : R → Bool → ℝ := fun e b => if e ∈ T_R then (if b then Real.exp lam else 1) else 1
          have hprod_eq : ∀ ωR : R → Bool,
              Real.exp (lam * ((triHits (eProd (ωL, ωR)) i₀).card : ℝ)) = ∏ e : R, gR e (ωR e) := by
            intro ωR
            rw [hhits_eq ωR, ← Finset.prod_subset (Finset.subset_univ T_R)]
            · rw [← Finset.prod_filter_mul_prod_filter_not T_R (fun e => ωR e = true)]
              have h1 : (∏ e ∈ T_R.filter (fun e => ωR e = true), gR e (ωR e)) =
                  Real.exp (lam * ((T_R.filter (fun e => ωR e = true)).card : ℝ)) := by
                calc _ = ∏ _e ∈ T_R.filter (fun e => ωR e = true), Real.exp lam :=
                        Finset.prod_congr rfl fun e he => by
                          rcases Finset.mem_filter.mp he with ⟨heT, htrue⟩
                          simp [gR, heT, htrue]
                  _ = (Real.exp lam) ^ (T_R.filter (fun e => ωR e = true)).card := Finset.prod_const _
                  _ = Real.exp (((T_R.filter (fun e => ωR e = true)).card : ℝ) * lam) :=
                      (Real.exp_nat_mul _ _).symm
                  _ = _ := by congr 1; ring
              have h2 : (∏ e ∈ T_R.filter (fun e => ¬ ωR e = true), gR e (ωR e)) = 1 :=
                Finset.prod_eq_one fun e he => by
                  rcases Finset.mem_filter.mp he with ⟨heT, hfalse⟩
                  simp [gR, heT, hfalse]
              rw [h1, h2, mul_one]
            · intro e _ heT; simp [gR, heT]
          have hsum_exp : (∑ ωR : R → Bool, bernW p ωR *
              Real.exp (lam * ((triHits (eProd (ωL, ωR)) i₀).card : ℝ))) =
              (1 - p + p * Real.exp lam) ^ S_L.card := by
            have h1 : (∑ ωR : R → Bool, bernW p ωR *
                Real.exp (lam * ((triHits (eProd (ωL, ωR)) i₀).card : ℝ))) =
                bernExp p (fun ωR => ∏ e : R, gR e (ωR e)) := by
              rw [bernExp]; exact Finset.sum_congr rfl fun ωR _ => by rw [hprod_eq ωR]
            rw [h1, bernExp_prod, ← Finset.prod_subset (Finset.subset_univ T_R)]
            · calc ∏ e ∈ T_R, (p * gR e true + (1 - p) * gR e false)
                  = ∏ _e ∈ T_R, (1 - p + p * Real.exp lam) :=
                    Finset.prod_congr rfl fun e he => by simp [gR, he]; ring
                _ = (1 - p + p * Real.exp lam) ^ T_R.card := Finset.prod_const _
                _ = (1 - p + p * Real.exp lam) ^ S_L.card := by rw [hcard_eq]
            · intro e _ heT; simp [gR, heT]
          calc ∑ ωR : R → Bool, bernW p ωR * triFac M₀ p lam (eProd (ωL, ωR)) i₀
              = (∑ ωR : R → Bool, bernW p ωR *
                  Real.exp (lam * ((triHits (eProd (ωL, ωR)) i₀).card : ℝ))) /
                  (1 - p + p * Real.exp lam) ^ S_L.card := by
                rw [Finset.sum_div]
                refine Finset.sum_congr rfl fun ωR _ => ?_
                have hst' : stopOk M₀ (eProd (ωL, ωR)) i₀ := (hstop_indep ωL ωR).mpr hst
                simp only [triFac, if_pos hst', hcand_indep ωL ωR, S_L]
                ring
            _ = 1 := by rw [hsum_exp, div_self (pow_pos hden_pos _).ne']
        · calc ∑ ωR : R → Bool, bernW p ωR * triFac M₀ p lam (eProd (ωL, ωR)) i₀
              = ∑ ωR : R → Bool, bernW p ωR * 1 := by
                refine Finset.sum_congr rfl fun ωR _ => ?_
                have hst' : ¬ stopOk M₀ (eProd (ωL, ωR)) i₀ := fun h => hst ((hstop_indep ωL ωR).mp h)
                simp [triFac, hst']
            _ = 1 := by simp [sum_bernW_eq_one]
      have hre1 : bernExp p (fun ω => ∏ i : Fin s, if i.val < k + 1 then triFac M₀ p lam ω i else 1) =
          ∑ ωL : L → Bool, bernW p ωL *
            (∏ i : Fin s, if i.val < k then triFac M₀ p lam (eProd (ωL, ωR₀)) i else 1) := by
        rw [bernExp]
        refine (Fintype.sum_equiv eProd
          (fun q => bernW p (eProd q) * ∏ i : Fin s, if i.val < k + 1 then triFac M₀ p lam (eProd q) i else 1)
          (fun ω => bernW p ω * ∏ i : Fin s, if i.val < k + 1 then triFac M₀ p lam ω i else 1)
          (fun _ => rfl)).symm.trans ?_
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun ωL _ => ?_
        calc ∑ ωR : R → Bool, bernW p (eProd (ωL, ωR)) *
                (∏ i : Fin s, if i.val < k + 1 then triFac M₀ p lam (eProd (ωL, ωR)) i else 1)
            = ∑ ωR : R → Bool,
                (bernW p ωL * (∏ i : Fin s, if i.val < k then triFac M₀ p lam (eProd (ωL, ωR₀)) i else 1)) *
                (bernW p ωR * triFac M₀ p lam (eProd (ωL, ωR)) i₀) := by
              refine Finset.sum_congr rfl fun ωR _ => ?_
              rw [hw_split ωL ωR, hprod_step, hPk_indep ωL ωR]; ring
          _ = (bernW p ωL * (∏ i : Fin s, if i.val < k then triFac M₀ p lam (eProd (ωL, ωR₀)) i else 1)) *
              (∑ ωR : R → Bool, bernW p ωR * triFac M₀ p lam (eProd (ωL, ωR)) i₀) :=
              (Finset.mul_sum _ _ _).symm
          _ = bernW p ωL * (∏ i : Fin s, if i.val < k then triFac M₀ p lam (eProd (ωL, ωR₀)) i else 1) := by
              rw [hinner_one ωL, mul_one]
      have hre0 : bernExp p (fun ω => ∏ i : Fin s, if i.val < k then triFac M₀ p lam ω i else 1) =
          ∑ ωL : L → Bool, bernW p ωL *
            (∏ i : Fin s, if i.val < k then triFac M₀ p lam (eProd (ωL, ωR₀)) i else 1) := by
        rw [bernExp]
        refine (Fintype.sum_equiv eProd
          (fun q => bernW p (eProd q) * ∏ i : Fin s, if i.val < k then triFac M₀ p lam (eProd q) i else 1)
          (fun ω => bernW p ω * ∏ i : Fin s, if i.val < k then triFac M₀ p lam ω i else 1)
          (fun _ => rfl)).symm.trans ?_
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun ωL _ => ?_
        calc ∑ ωR : R → Bool, bernW p (eProd (ωL, ωR)) *
                (∏ i : Fin s, if i.val < k then triFac M₀ p lam (eProd (ωL, ωR)) i else 1)
            = ∑ ωR : R → Bool,
                (bernW p ωL * (∏ i : Fin s, if i.val < k then triFac M₀ p lam (eProd (ωL, ωR₀)) i else 1)) *
                bernW p ωR := by
              refine Finset.sum_congr rfl fun ωR _ => ?_
              rw [hw_split ωL ωR, hPk_indep ωL ωR]; ring
          _ = (bernW p ωL * (∏ i : Fin s, if i.val < k then triFac M₀ p lam (eProd (ωL, ωR₀)) i else 1)) *
              (∑ ωR : R → Bool, bernW p ωR) := (Finset.mul_sum _ _ _).symm
          _ = bernW p ωL * (∏ i : Fin s, if i.val < k then triFac M₀ p lam (eProd (ωL, ωR₀)) i else 1) := by
              rw [sum_bernW_eq_one, mul_one]
      rw [hre1, ← hre0]
      exact ih (by omega)
  have hfull := hind s le_rfl
  simpa [Fin.isLt] using hfull

/-- Stopped martingale upper tail on the number of `pruneTri`-deleted edges in `G(s, p)`. -/
lemma bernProb_triKill_le {s : ℕ} (M₀ : ℕ) {p lam T : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hlam : 0 < lam) :
    bernProb p (fun ω : EdgeIdx s → Bool =>
      (∑ i : Fin s, (triCand ω i).card ≤ M₀) ∧
      T ≤ ((∑ i : Fin s, (triHits ω i).card : ℕ) : ℝ)) ≤
      Real.exp ((Real.exp lam - 1) * p * (M₀ : ℝ) - lam * T) := by
  let Z : (EdgeIdx s → Bool) → ℝ := fun ω => ∏ i : Fin s, triFac M₀ p lam ω i
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => Finset.prod_nonneg fun i _ => triFac_nonneg M₀ hp0 hp1 ω i
  have hbase_ge1 : 1 ≤ 1 - p + p * Real.exp lam := by
    have : 1 ≤ Real.exp lam := Real.one_le_exp hlam.le
    nlinarith
  have hbase_le_exp : 1 - p + p * Real.exp lam ≤ Real.exp ((Real.exp lam - 1) * p) := by
    have h := Real.add_one_le_exp ((Real.exp lam - 1) * p)
    linarith
  have himp : ∀ ω : EdgeIdx s → Bool,
      ((∑ i : Fin s, (triCand ω i).card ≤ M₀) ∧
        T ≤ ((∑ i : Fin s, (triHits ω i).card : ℕ) : ℝ)) →
      Real.exp (lam * T - (Real.exp lam - 1) * p * (M₀ : ℝ)) ≤ Z ω := by
    intro ω ⟨hM, hT⟩
    have hall_ok : ∀ i : Fin s, stopOk M₀ ω i := fun i => by
      dsimp only [stopOk]
      refine le_trans (Finset.sum_le_sum fun r _ => ?_) hM
      split_ifs <;> omega
    have hZ_eq : Z ω = Real.exp (lam * ((∑ i : Fin s, (triHits ω i).card : ℕ) : ℝ)) /
        (1 - p + p * Real.exp lam) ^ (∑ i : Fin s, (triCand ω i).card) := by
      dsimp only [Z]
      calc ∏ i : Fin s, triFac M₀ p lam ω i
          = ∏ i : Fin s, (Real.exp (lam * ((triHits ω i).card : ℝ)) /
              (1 - p + p * Real.exp lam) ^ (triCand ω i).card) :=
            Finset.prod_congr rfl fun i _ => if_pos (hall_ok i)
        _ = (∏ i : Fin s, Real.exp (lam * ((triHits ω i).card : ℝ))) /
            (∏ i : Fin s, (1 - p + p * Real.exp lam) ^ (triCand ω i).card) := by
            rw [Finset.prod_div_distrib]
        _ = Real.exp (∑ i : Fin s, lam * ((triHits ω i).card : ℝ)) /
            (1 - p + p * Real.exp lam) ^ (∑ i : Fin s, (triCand ω i).card) := by
            rw [Real.exp_sum, Finset.prod_pow_eq_pow_sum]
        _ = Real.exp (lam * ((∑ i : Fin s, (triHits ω i).card : ℕ) : ℝ)) /
            (1 - p + p * Real.exp lam) ^ (∑ i : Fin s, (triCand ω i).card) := by
            rw [← Finset.mul_sum, Nat.cast_sum]
    rw [hZ_eq]
    have hnum : Real.exp (lam * T) ≤
        Real.exp (lam * ((∑ i : Fin s, (triHits ω i).card : ℕ) : ℝ)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hden_pos : 0 < (1 - p + p * Real.exp lam) ^ (∑ i : Fin s, (triCand ω i).card) :=
      pow_pos (by linarith) _
    have hden_le : (1 - p + p * Real.exp lam) ^ (∑ i : Fin s, (triCand ω i).card) ≤
        Real.exp ((Real.exp lam - 1) * p * (M₀ : ℝ)) := by
      calc (1 - p + p * Real.exp lam) ^ (∑ i : Fin s, (triCand ω i).card)
          ≤ (1 - p + p * Real.exp lam) ^ M₀ := pow_le_pow_right₀ hbase_ge1 hM
        _ ≤ (Real.exp ((Real.exp lam - 1) * p)) ^ M₀ :=
            pow_le_pow_left₀ (by linarith) hbase_le_exp M₀
        _ = Real.exp ((M₀ : ℝ) * ((Real.exp lam - 1) * p)) := (Real.exp_nat_mul _ _).symm
        _ = Real.exp ((Real.exp lam - 1) * p * (M₀ : ℝ)) := by congr 1; ring
    rw [Real.exp_sub]
    calc Real.exp (lam * T) / Real.exp ((Real.exp lam - 1) * p * (M₀ : ℝ))
        ≤ Real.exp (lam * ((∑ i : Fin s, (triHits ω i).card : ℕ) : ℝ)) /
          Real.exp ((Real.exp lam - 1) * p * (M₀ : ℝ)) :=
          div_le_div_of_nonneg_right hnum (Real.exp_pos _).le
      _ ≤ Real.exp (lam * ((∑ i : Fin s, (triHits ω i).card : ℕ) : ℝ)) /
          (1 - p + p * Real.exp lam) ^ (∑ i : Fin s, (triCand ω i).card) :=
          div_le_div_of_nonneg_left (Real.exp_pos _).le hden_pos hden_le
  have h1 := bernProb_mono hp0 hp1 himp
  have hmk := bernProb_markov hp0 hp1 hZ0 (Real.exp_pos (lam * T - (Real.exp lam - 1) * p * (M₀ : ℝ)))
  rw [bernExp_triFac_prod_eq_one M₀ hp0 hp1 hlam.le] at hmk
  calc _ ≤ 1 / Real.exp (lam * T - (Real.exp lam - 1) * p * (M₀ : ℝ)) := h1.trans hmk
    _ = Real.exp ((Real.exp lam - 1) * p * (M₀ : ℝ) - lam * T) := by
        rw [one_div, ← Real.exp_neg]; congr 1; ring

/-- Every `triCand` pair `(i, j)` has a common earlier neighbor `r < i < j`, so
`2 * ∑ i, |triCand ω i| ≤ ∑ r, degIn (graphOf ω) univ r ^ 2`. -/
lemma two_mul_sum_triCand_le {s : ℕ} (ω : EdgeIdx s → Bool) :
    2 * ∑ i : Fin s, (triCand ω i).card ≤
      ∑ r : Fin s, (degIn (graphOf ω) Finset.univ r) ^ 2 := by
  let pairs := (Finset.univ : Finset (Fin s)).sigma (fun i => triCand ω i)
  have hp_card : pairs.card = ∑ i : Fin s, (triCand ω i).card := Finset.card_sigma _ _
  let triples := (Finset.univ : Finset (Fin s)).sigma fun r =>
    ((Finset.univ.filter fun u => (graphOf ω).Adj r u) ×ˢ
      (Finset.univ.filter fun v => (graphOf ω).Adj r v)).filter fun q => q.1 < q.2
  have hinj : pairs.card ≤ triples.card := by
    have hex : ∀ x ∈ pairs, ∃ r : Fin s, ⟨r, (x.1, x.2)⟩ ∈ triples := by
      intro ⟨i, j⟩ hx
      have hj := (Finset.mem_sigma.mp hx).2
      rcases (Finset.mem_filter.mp hj).2 with ⟨hij, r, hri, hrj, h1, h2⟩
      refine ⟨r, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩, hij⟩⟩⟩
      · simp only [graphOf, dif_pos hri]; exact h1
      · simp only [graphOf, dif_pos hrj]; exact h2
    choose f hf using hex
    refine Finset.card_le_card_of_injOn (fun x => if hx : x ∈ pairs then ⟨f x hx, (x.1, x.2)⟩ else
        ⟨x.1, (x.1, x.2)⟩) ?_ ?_
    · intro x hx
      have hx' : x ∈ pairs := hx
      change (if hx : x ∈ pairs then ⟨f x hx, (x.1, x.2)⟩ else ⟨x.1, (x.1, x.2)⟩) ∈ triples
      rw [dif_pos hx']; exact hf x hx'
    · intro x hx y hy hxy
      have hx' : x ∈ pairs := hx
      have hy' : y ∈ pairs := hy
      dsimp only at hxy
      rw [dif_pos hx', dif_pos hy'] at hxy
      have h12 : (x.1, x.2) = (y.1, y.2) := by
        have := congrArg Sigma.snd hxy; simpa using this
      exact Sigma.ext (congrArg Prod.fst h12) (heq_of_eq (congrArg Prod.snd h12))
  have htri_bound : 2 * triples.card ≤ ∑ r : Fin s, (degIn (graphOf ω) Finset.univ r) ^ 2 := by
    rw [Finset.card_sigma, Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    set N := Finset.univ.filter fun u => (graphOf ω).Adj r u
    have hcard_lt : 2 * ((N ×ˢ N).filter fun q => q.1 < q.2).card ≤ (N ×ˢ N).card := by
      let A := (N ×ˢ N).filter fun q => q.1 < q.2
      let B := (N ×ˢ N).filter fun q => q.2 < q.1
      have hdisj : Disjoint A B := Finset.disjoint_left.mpr fun q hqA hqB =>
        lt_asymm (Finset.mem_filter.mp hqA).2 (Finset.mem_filter.mp hqB).2
      have hsub : A ∪ B ⊆ N ×ˢ N := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      have hcardAB : A.card = B.card := by
        refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
        · intro q hq
          rcases Finset.mem_filter.mp hq with ⟨hqN, hlt⟩
          rcases Finset.mem_product.mp hqN with ⟨h1, h2⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2, h1⟩, hlt⟩
        · intro q₁ _ q₂ _ h
          exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
        · intro q hq
          rcases Finset.mem_filter.mp hq with ⟨hqN, hlt⟩
          rcases Finset.mem_product.mp hqN with ⟨h1, h2⟩
          exact ⟨(q.2, q.1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2, h1⟩, hlt⟩, rfl⟩
      have hle := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj, ← hcardAB] at hle
      change 2 * A.card ≤ (N ×ˢ N).card
      omega
    simpa [degIn, N, Finset.card_product, sq] using hcard_lt
  omega

/-- Every edge `e : EdgeIdx s` present in `ω` that is deleted by `pruneTri (graphOf ω)` is
counted in `∑ i, (triHits ω i).card`. -/
lemma card_triPruned_edges_le_sum_triHits {s : ℕ} (ω : EdgeIdx s → Bool) :
    (Finset.univ.filter fun e : EdgeIdx s =>
      ω e = true ∧ ¬ (pruneTri (graphOf ω)).Adj e.1.1 e.1.2).card ≤
      ∑ i : Fin s, (triHits ω i).card := by
  let E := Finset.univ.filter fun e : EdgeIdx s =>
    ω e = true ∧ ¬ (pruneTri (graphOf ω)).Adj e.1.1 e.1.2
  let H := (Finset.univ : Finset (Fin s)).sigma fun i => triHits ω i
  have hH_card : H.card = ∑ i : Fin s, (triHits ω i).card := Finset.card_sigma _ _
  rw [← hH_card]
  refine Finset.card_le_card_of_injOn (fun e => ⟨e.1.1, e.1.2⟩) ?_ ?_
  · intro e he
    rcases (Finset.mem_filter.mp he).2 with ⟨htrue, hnot⟩
    have hadj : (graphOf ω).Adj e.1.1 e.1.2 := by simp only [graphOf, dif_pos e.2]; exact htrue
    have hex : ∃ z : Fin s, z < min e.1.1 e.1.2 ∧ (graphOf ω).Adj z e.1.1 ∧ (graphOf ω).Adj z e.1.2 := by
      by_contra hno; exact hnot ⟨hadj, hno⟩
    rcases hex with ⟨z, hz, hz1, hz2⟩
    have hmin : min e.1.1 e.1.2 = e.1.1 := min_eq_left e.2.le
    have hz1_lt : z < e.1.1 := by rwa [hmin] at hz
    have hz2_lt : z < e.1.2 := lt_trans hz1_lt e.2
    have h1 : ω ⟨(z, e.1.1), hz1_lt⟩ = true := by simpa only [graphOf, dif_pos hz1_lt] using hz1
    have h2 : ω ⟨(z, e.1.2), hz2_lt⟩ = true := by simpa only [graphOf, dif_pos hz2_lt] using hz2
    refine Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2, z, hz1_lt, hz2_lt, h1, h2⟩, e.2, htrue⟩⟩
  · intro e₁ _ e₂ _ h
    apply Subtype.ext; apply Prod.ext
    · exact congrArg Sigma.fst h
    · exact eq_of_heq (Sigma.ext_iff.mp h).2

end ExtraProbTools

/- ### Section 2: Graph Regularity Event `GoodGraph` and Weighted 2-Path Bounds -/

section GraphRegularity

/-- Probability that every coordinate in `T : Finset X` is `true` is `p^|T|`. -/
lemma bernProb_all_true {X : Type*} [Fintype X] [DecidableEq X] (p : ℝ) (T : Finset X) :
    bernProb p (fun ω : X → Bool => ∀ x ∈ T, ω x = true) = p ^ T.card := by
  let g : X → Bool → ℝ := fun x b => if x ∈ T then (if b then 1 else 0) else 1
  have hprod : ∀ ω : X → Bool,
      (if ∀ x ∈ T, ω x = true then (1 : ℝ) else 0) = ∏ x : X, g x (ω x) := by
    intro ω
    by_cases hall : ∀ x ∈ T, ω x = true
    · rw [if_pos hall]; symm
      exact Finset.prod_eq_one fun x _ => by
        by_cases hx : x ∈ T
        · simp [g, hx, hall x hx]
        · simp [g, hx]
    · rw [if_neg hall]; push Not at hall
      rcases hall with ⟨x₀, hx₀T, hx₀f⟩
      have hx₀b : ω x₀ = false := by cases h : ω x₀ <;> simp_all
      symm; exact Finset.prod_eq_zero (Finset.mem_univ x₀) (by simp [g, hx₀T, hx₀b])
  have heq : bernProb p (fun ω : X → Bool => ∀ x ∈ T, ω x = true) =
      bernExp p (fun ω => ∏ x : X, g x (ω x)) := by
    simp only [bernProb, bernExp]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [← hprod ω]; split_ifs <;> ring
  rw [heq, bernExp_prod, ← Finset.prod_subset (Finset.subset_univ T)]
  · calc ∏ x ∈ T, (p * g x true + (1 - p) * g x false)
        = ∏ _x ∈ T, p := Finset.prod_congr rfl fun x hx => by simp [g, hx]
      _ = p ^ T.card := Finset.prod_const p
  · intro x _ hxT; simp [g, hxT]

/-- Parameters governing the global regularity event `GoodGraph` on `G(m, p)`. -/
structure RegParams where
  m : ℕ
  k : ℕ
  p : ℝ
  η₀ : ℝ
  C_codeg : ℕ
  L : ℕ
  J : ℕ
  T_lo : ℝ
  T_cut : ℝ
  T_mid : ℝ
  T_big : ℝ
  B_mid : ℝ
  B_cross : ℝ

/-- Target subset size for weight class `i : ℕ` (`w = 2^i`). -/
def RegParams.clsSize (P : RegParams) (i : ℕ) : ℕ :=
  min P.m (P.k / 2 ^ i)

/-- Exterior degree-tail count threshold in Range B (`T_lo ≤ 2^i * 2^j ≤ T_mid`). -/
noncomputable def RegParams.rMid (P : RegParams) (i j : ℕ) : ℕ :=
  ⌈(P.k : ℝ) ^ 2 / (((2 ^ i : ℕ) : ℝ) ^ 2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * P.B_mid)⌉₊

/-- Exterior degree-tail count threshold in Range A (`T_mid < 2^i * 2^j`). -/
noncomputable def RegParams.rLargeOut (P : RegParams) (i j : ℕ) : ℕ :=
  ⌈40 * (P.clsSize i : ℝ) / ((2 ^ j : ℕ) : ℝ)⌉₊ + 1

/-- Interior degree-tail count threshold in Range A (`T_mid < 2^i * 2^j`). -/
noncomputable def RegParams.rLargeIn (P : RegParams) (i j : ℕ) : ℕ :=
  ⌈80 * (P.clsSize i : ℝ) / ((2 ^ j : ℕ) : ℝ)⌉₊ + 1

/-- Off-diagonal (`d₁ ≥ 1 ∧ d₂ ≥ 1`) common-neighbor count threshold for classes `i < i'`. -/
noncomputable def RegParams.rCross (P : RegParams) (i i' : ℕ) : ℕ :=
  ⌈(P.k : ℝ) ^ 2 / (((2 ^ i : ℕ) : ℝ) * ((2 ^ i' : ℕ) : ℝ) * P.B_cross)⌉₊

/-- Helper: unordered edge corresponding to distinct vertices `u ≠ v` in `Fin m`. -/
def mkEdgeIdx {m : ℕ} {u v : Fin m} (h : u ≠ v) : EdgeIdx m :=
  if hlt : u < v then ⟨(u, v), hlt⟩
  else ⟨(v, u), lt_of_le_of_ne (le_of_not_gt hlt) h.symm⟩

lemma graphOf_adj_iff_mkEdgeIdx {m : ℕ} (ω : EdgeIdx m → Bool) {u v : Fin m} (h : u ≠ v) :
    (graphOf ω).Adj u v ↔ ω (mkEdgeIdx h) = true := by
  by_cases hlt : u < v
  · simp [graphOf, mkEdgeIdx, hlt]
  · have hgt : v < u := lt_of_le_of_ne (le_of_not_gt hlt) h.symm
    simp [graphOf, mkEdgeIdx, hlt, hgt]

lemma choose_le_pow (n k : ℕ) : n.choose k ≤ n ^ k := by
  cases n with
  | zero => cases k <;> simp
  | succ n =>
    have hcard : ((Finset.univ : Finset (Fin (n + 1))).powersetCard k).card = (n + 1).choose k := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    have hfn : (Finset.univ : Finset (Fin k → Fin (n + 1))).card = (n + 1) ^ k := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    rw [← hcard, ← hfn]
    refine Finset.card_le_card_of_injOn
      (fun S => if h : S.card = k then (fun i : Fin k => (S.orderIsoOfFin h i).1) else fun _ => ⟨0, by omega⟩)
      (fun _ _ => Finset.mem_univ _) ?_
    intro S₁ hS1 S₂ hS2 heq
    have hc1 : S₁.card = k := (Finset.mem_powersetCard.mp hS1).2
    have hc2 : S₂.card = k := (Finset.mem_powersetCard.mp hS2).2
    simp only [dif_pos hc1, dif_pos hc2] at heq
    ext x
    constructor
    · intro hx
      let i := (S₁.orderIsoOfFin hc1).symm ⟨x, hx⟩
      have h1 : (S₁.orderIsoOfFin hc1 i).1 = x := congrArg Subtype.val ((S₁.orderIsoOfFin hc1).apply_symm_apply ⟨x, hx⟩)
      have h2 := congrFun heq i
      rw [h1] at h2; rw [h2]; exact (S₂.orderIsoOfFin hc2 i).2
    · intro hx
      let i := (S₂.orderIsoOfFin hc2).symm ⟨x, hx⟩
      have h2 : (S₂.orderIsoOfFin hc2 i).1 = x := congrArg Subtype.val ((S₂.orderIsoOfFin hc2).apply_symm_apply ⟨x, hx⟩)
      have h1 := congrFun heq i
      rw [h2] at h1; rw [← h1]; exact (S₁.orderIsoOfFin hc1 i).2

lemma mkEdgeIdx_eq_iff {m : ℕ} {u₁ v₁ u₂ v₂ : Fin m} (h₁ : u₁ ≠ v₁) (h₂ : u₂ ≠ v₂) :
    mkEdgeIdx h₁ = mkEdgeIdx h₂ ↔ (u₁ = u₂ ∧ v₁ = v₂) ∨ (u₁ = v₂ ∧ v₁ = u₂) := by
  constructor
  · intro heq
    have hval := congrArg Subtype.val heq
    by_cases hlt₁ : u₁ < v₁ <;> by_cases hlt₂ : u₂ < v₂
    · simp only [mkEdgeIdx, dif_pos hlt₁, dif_pos hlt₂, Prod.mk.injEq] at hval
      exact Or.inl hval
    · simp only [mkEdgeIdx, dif_pos hlt₁, dif_neg hlt₂, Prod.mk.injEq] at hval
      exact Or.inr hval
    · simp only [mkEdgeIdx, dif_neg hlt₁, dif_pos hlt₂, Prod.mk.injEq] at hval
      exact Or.inr ⟨hval.2, hval.1⟩
    · simp only [mkEdgeIdx, dif_neg hlt₁, dif_neg hlt₂, Prod.mk.injEq] at hval
      exact Or.inl ⟨hval.2, hval.1⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · by_cases hlt : u₁ < v₁
      · have hnot : ¬ v₁ < u₁ := lt_asymm hlt
        simp [mkEdgeIdx, hlt, hnot]
      · have hgt : v₁ < u₁ := lt_of_le_of_ne (le_of_not_gt hlt) h₁.symm
        simp [mkEdgeIdx, hlt, hgt]

/-- Property 1: maximum degree in `G` is at most `(1 + η₀) * m * p`. -/
def GoodMaxDeg (P : RegParams) (ω : EdgeIdx P.m → Bool) : Prop :=
  ∀ z : Fin P.m, (degIn (graphOf ω) Finset.univ z : ℝ) ≤ (1 + P.η₀) * ((P.m : ℝ) * P.p)

/-- Property 2: pairwise codegree of distinct vertices is `< C_codeg`. -/
def GoodMaxCodeg (P : RegParams) (ω : EdgeIdx P.m → Bool) : Prop :=
  ∀ z₁ z₂ : Fin P.m, z₁ ≠ z₂ →
    (Finset.univ.filter fun u : Fin P.m => (graphOf ω).Adj z₁ u ∧ (graphOf ω).Adj z₂ u).card < P.C_codeg

/-- Property 3: exterior degree tail in Range B (`T_lo ≤ 2^i * 2^j ≤ T_mid`, `1 ≤ j < J`). -/
def GoodExtDegMid (P : RegParams) (ω : EdgeIdx P.m → Bool) : Prop :=
  ∀ i : Fin P.L, ∀ j : Fin P.J, 1 ≤ j.val →
    P.T_lo ≤ ((2 ^ i.val : ℕ) : ℝ) * ((2 ^ j.val : ℕ) : ℝ) →
    ((2 ^ i.val : ℕ) : ℝ) * ((2 ^ j.val : ℕ) : ℝ) ≤ P.T_mid →
    ∀ S ∈ (Finset.univ : Finset (Fin P.m)).powersetCard (P.clsSize i.val),
      ((Finset.univ \ S).filter fun z => 2 ^ j.val ≤ degIn (graphOf ω) S z).card < P.rMid i.val j.val

/-- Property 4: exterior and interior degree tails in Range A (`T_mid < 2^i * 2^j`). -/
def GoodDegLarge (P : RegParams) (ω : EdgeIdx P.m → Bool) : Prop :=
  ∀ i : Fin P.L, ∀ j : Fin P.J,
    P.T_mid < ((2 ^ i.val : ℕ) : ℝ) * ((2 ^ j.val : ℕ) : ℝ) →
    ∀ S ∈ (Finset.univ : Finset (Fin P.m)).powersetCard (P.clsSize i.val),
      ((Finset.univ \ S).filter fun z => 2 ^ j.val ≤ degIn (graphOf ω) S z).card < P.rLargeOut i.val j.val ∧
      (S.filter fun z => 2 ^ j.val ≤ degIn (graphOf ω) S z).card < P.rLargeIn i.val j.val

/-- Property 5: cross-class common neighbors (`d(z, S₁) ≥ 1 ∧ d(z, S₂) ≥ 1`) for `i < i'`. -/
def GoodCrossPair (P : RegParams) (ω : EdgeIdx P.m → Bool) : Prop :=
  ∀ i i' : Fin P.L, i.val < i'.val →
    ∀ S₁ ∈ (Finset.univ : Finset (Fin P.m)).powersetCard (P.clsSize i.val),
    ∀ S₂ ∈ (Finset.univ : Finset (Fin P.m)).powersetCard (P.clsSize i'.val),
      Disjoint S₁ S₂ →
      ((Finset.univ \ (S₁ ∪ S₂)).filter fun z =>
        1 ≤ degIn (graphOf ω) S₁ z ∧ 1 ≤ degIn (graphOf ω) S₂ z).card < P.rCross i.val i'.val

/-- Complete global regularity event on `G(m, p)`. -/
def GoodGraph (P : RegParams) (ω : EdgeIdx P.m → Bool) : Prop :=
  GoodMaxDeg P ω ∧ GoodMaxCodeg P ω ∧ GoodExtDegMid P ω ∧ GoodDegLarge P ω ∧ GoodCrossPair P ω

/-- Bound on `P(¬ GoodMaxDeg P ω)`. -/
lemma bernProb_not_goodMaxDeg_le (P : RegParams)
    (hp0 : 0 ≤ P.p) (hp1 : P.p ≤ 1) (hη0 : 0 < P.η₀) (hη1 : P.η₀ ≤ 1 / 2) :
    bernProb P.p (fun ω => ¬ GoodMaxDeg P ω) ≤
      (P.m : ℝ) * Real.exp (-(P.η₀ ^ 2 / 3) * (((P.m - 1 : ℕ) : ℝ) * P.p)) := by
  have himp : ∀ ω : EdgeIdx P.m → Bool, ¬ GoodMaxDeg P ω →
      ∃ z : Fin P.m, (1 + P.η₀) * ((P.m : ℝ) * P.p) < (degIn (graphOf ω) Finset.univ z : ℝ) := by
    intro ω hnot; simp only [GoodMaxDeg, not_forall, not_le] at hnot; exact hnot
  refine (bernProb_mono hp0 hp1 himp).trans ?_
  refine (bernProb_exists_univ_le hp0 hp1 _).trans ?_
  have hsingle : ∀ z : Fin P.m,
      bernProb P.p (fun ω => (1 + P.η₀) * ((P.m : ℝ) * P.p) < (degIn (graphOf ω) Finset.univ z : ℝ)) ≤
        Real.exp (-(P.η₀ ^ 2 / 3) * (((P.m - 1 : ℕ) : ℝ) * P.p)) := by
    intro z
    let Sz : Finset (EdgeIdx P.m) := Finset.univ.filter fun e => e.1.1 = z ∨ e.1.2 = z
    have hSz_card : Sz.card = P.m - 1 := by
      have hbij : Sz.card = (Finset.univ.erase z).card := by
        refine Finset.card_bij (fun e _ => if e.1.1 = z then e.1.2 else e.1.1) ?_ ?_ ?_
        · intro e he
          rcases (Finset.mem_filter.mp he).2 with h1 | h2
          · rw [if_pos h1]; exact Finset.mem_erase.mpr ⟨(h1 ▸ e.2).ne', Finset.mem_univ _⟩
          · have hne : e.1.1 ≠ z := (h2 ▸ e.2).ne
            rw [if_neg hne]; exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
        · intro e₁ he₁ e₂ he₂ heq
          rcases (Finset.mem_filter.mp he₁).2 with h1 | h1 <;>
          rcases (Finset.mem_filter.mp he₂).2 with h2 | h2
          · simp only [if_pos h1, if_pos h2] at heq
            exact Subtype.ext (Prod.ext (h1.trans h2.symm) heq)
          · have hne₂ : e₂.1.1 ≠ z := (h2 ▸ e₂.2).ne
            simp only [if_pos h1, if_neg hne₂] at heq
            have hlt1 : z < e₁.1.2 := h1 ▸ e₁.2
            have hlt2 : e₁.1.2 < z := by rw [heq]; exact h2 ▸ e₂.2
            exact False.elim (lt_asymm hlt1 hlt2)
          · have hne₁ : e₁.1.1 ≠ z := (h1 ▸ e₁.2).ne
            simp only [if_neg hne₁, if_pos h2] at heq
            have hlt1 : e₁.1.1 < z := h1 ▸ e₁.2
            have hlt2 : z < e₁.1.1 := by rw [heq]; exact h2 ▸ e₂.2
            exact False.elim (lt_asymm hlt1 hlt2)
          · have hne₁ : e₁.1.1 ≠ z := (h1 ▸ e₁.2).ne
            have hne₂ : e₂.1.1 ≠ z := (h2 ▸ e₂.2).ne
            simp only [if_neg hne₁, if_neg hne₂] at heq
            exact Subtype.ext (Prod.ext heq (h1.trans h2.symm))
        · intro u hu
          have hne : u ≠ z := (Finset.mem_erase.mp hu).1
          refine ⟨mkEdgeIdx hne.symm, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · by_cases hlt : z < u <;> simp [mkEdgeIdx, hlt]
          · by_cases hlt : z < u
            · simp [mkEdgeIdx, hlt]
            · have hgt : u < z := lt_of_le_of_ne (le_of_not_gt hlt) hne
              simp [mkEdgeIdx, hlt, hne]
      rw [hbij, Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ, Fintype.card_fin]
    have hdeg_eq : ∀ ω : EdgeIdx P.m → Bool,
        degIn (graphOf ω) Finset.univ z = (Sz.filter fun e => ω e = true).card := by
      intro ω
      dsimp only [degIn]
      refine Finset.card_bij (fun u hu => mkEdgeIdx (show z ≠ u from
          (graphOf ω).ne_of_adj (Finset.mem_filter.mp hu).2)) ?_ ?_ ?_
      · intro u hu
        have hadj := (Finset.mem_filter.mp hu).2
        have hne : z ≠ u := (graphOf ω).ne_of_adj hadj
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
          (graphOf_adj_iff_mkEdgeIdx ω hne).mp hadj⟩
        by_cases hlt : z < u <;> simp [mkEdgeIdx, hlt]
      · intro u₁ hu₁ u₂ hu₂ heq
        have hne₁ : z ≠ u₁ := (graphOf ω).ne_of_adj (Finset.mem_filter.mp hu₁).2
        have hne₂ : z ≠ u₂ := (graphOf ω).ne_of_adj (Finset.mem_filter.mp hu₂).2
        rcases (mkEdgeIdx_eq_iff hne₁ hne₂).mp heq with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact False.elim (hne₂ h)
      · intro e he
        rcases Finset.mem_filter.mp he with ⟨heSz, htrue⟩
        rcases (Finset.mem_filter.mp heSz).2 with h1 | h2
        · refine ⟨e.1.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · have hlt : z < e.1.2 := h1 ▸ e.2
            simp only [graphOf, dif_pos hlt]
            have heq : (⟨(z, e.1.2), hlt⟩ : EdgeIdx P.m) = e := Subtype.ext (Prod.ext h1.symm rfl)
            rw [heq]; exact htrue
          · have hlt : z < e.1.2 := h1 ▸ e.2
            simp only [mkEdgeIdx, dif_pos hlt]
            exact Subtype.ext (Prod.ext h1.symm rfl)
        · refine ⟨e.1.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · have hlt : e.1.1 < z := h2 ▸ e.2
            have hnot : ¬ z < e.1.1 := lt_asymm hlt
            simp only [graphOf, dif_neg hnot, dif_pos hlt]
            have heq : (⟨(e.1.1, z), hlt⟩ : EdgeIdx P.m) = e := Subtype.ext (Prod.ext rfl h2.symm)
            rw [heq]; exact htrue
          · have hlt : e.1.1 < z := h2 ▸ e.2
            have hnot : ¬ z < e.1.1 := lt_asymm hlt
            simp only [mkEdgeIdx, dif_neg hnot]
            exact Subtype.ext (Prod.ext rfl h2.symm)
    have hm1_le : ((P.m - 1 : ℕ) : ℝ) ≤ (P.m : ℝ) := by exact_mod_cast Nat.sub_le P.m 1
    have hch := bernProb_binom_ge_chernoff hp0 hp1 hη0 hη1 Sz
    rw [hSz_card] at hch
    refine (bernProb_mono hp0 hp1 fun ω hlt => ?_).trans hch
    rw [← hdeg_eq ω]
    have h1 : (1 + P.η₀) * (((P.m - 1 : ℕ) : ℝ) * P.p) ≤ (1 + P.η₀) * ((P.m : ℝ) * P.p) := by
      have : 0 ≤ (1 + P.η₀) * P.p := by nlinarith
      nlinarith
    exact h1.trans hlt.le
  calc ∑ z : Fin P.m, bernProb P.p (fun ω => (1 + P.η₀) * ((P.m : ℝ) * P.p) <
        (degIn (graphOf ω) Finset.univ z : ℝ))
      ≤ ∑ _z : Fin P.m, Real.exp (-(P.η₀ ^ 2 / 3) * (((P.m - 1 : ℕ) : ℝ) * P.p)) :=
        Finset.sum_le_sum fun z _ => hsingle z
    _ = (P.m : ℝ) * Real.exp (-(P.η₀ ^ 2 / 3) * (((P.m - 1 : ℕ) : ℝ) * P.p)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Bound on `P(¬ GoodMaxCodeg P ω)`. -/
lemma bernProb_not_goodMaxCodeg_le (P : RegParams)
    (hp0 : 0 ≤ P.p) (hp1 : P.p ≤ 1) (hC : 1 ≤ P.C_codeg) :
    bernProb P.p (fun ω => ¬ GoodMaxCodeg P ω) ≤
      (P.m : ℝ) ^ 2 * (Real.exp 1 * (P.m : ℝ) * P.p ^ 2 / (P.C_codeg : ℝ)) ^ P.C_codeg := by
  have himp : ∀ ω : EdgeIdx P.m → Bool, ¬ GoodMaxCodeg P ω →
      ∃ q : Fin P.m × Fin P.m, q.1 ≠ q.2 ∧
        P.C_codeg ≤ (Finset.univ.filter fun u : Fin P.m =>
          (graphOf ω).Adj q.1 u ∧ (graphOf ω).Adj q.2 u).card := by
    intro ω hnot
    simp only [GoodMaxCodeg, not_forall, not_lt] at hnot
    rcases hnot with ⟨z₁, z₂, hne, hge⟩
    exact ⟨(z₁, z₂), hne, hge⟩
  refine (bernProb_mono hp0 hp1 himp).trans ?_
  refine (bernProb_exists_univ_le hp0 hp1 _).trans ?_
  have hpair : ∀ q : Fin P.m × Fin P.m,
      bernProb P.p (fun ω => q.1 ≠ q.2 ∧
        P.C_codeg ≤ (Finset.univ.filter fun u : Fin P.m =>
          (graphOf ω).Adj q.1 u ∧ (graphOf ω).Adj q.2 u).card) ≤
        (Real.exp 1 * (P.m : ℝ) * P.p ^ 2 / (P.C_codeg : ℝ)) ^ P.C_codeg := by
    intro ⟨z₁, z₂⟩
    by_cases hne : z₁ = z₂
    · subst hne
      have h0 : bernProb P.p (fun ω : EdgeIdx P.m → Bool => z₁ ≠ z₁ ∧
          P.C_codeg ≤ (Finset.univ.filter fun u : Fin P.m =>
            (graphOf ω).Adj z₁ u ∧ (graphOf ω).Adj z₁ u).card) = 0 := by
        simp [bernProb]
      rw [h0]; positivity
    · let cands := (Finset.univ : Finset (Fin P.m)).powersetCard P.C_codeg
      have hcov : ∀ ω : EdgeIdx P.m → Bool,
          (z₁ ≠ z₂ ∧ P.C_codeg ≤ (Finset.univ.filter fun u : Fin P.m =>
            (graphOf ω).Adj z₁ u ∧ (graphOf ω).Adj z₂ u).card) →
          ∃ U : { U : Finset (Fin P.m) // U ∈ cands },
            z₁ ∉ U.1 ∧ z₂ ∉ U.1 ∧ ∀ u ∈ U.1, (graphOf ω).Adj z₁ u ∧ (graphOf ω).Adj z₂ u := by
        intro ω ⟨_, hge⟩
        obtain ⟨U, hUsub, hUcard⟩ := Finset.exists_subset_card_eq hge
        have hmem : U ∈ cands := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hUcard⟩
        have hz1 : z₁ ∉ U := fun hz => (graphOf ω).loopless.irrefl z₁ (Finset.mem_filter.mp (hUsub hz)).2.1
        have hz2 : z₂ ∉ U := fun hz => (graphOf ω).loopless.irrefl z₂ (Finset.mem_filter.mp (hUsub hz)).2.2
        exact ⟨⟨U, hmem⟩, hz1, hz2, fun u hu => (Finset.mem_filter.mp (hUsub hu)).2⟩
      refine (bernProb_mono hp0 hp1 hcov).trans ?_
      refine (bernProb_exists_univ_le hp0 hp1 _).trans ?_
      have hU_bound : ∀ U : { U : Finset (Fin P.m) // U ∈ cands },
          bernProb P.p (fun ω => z₁ ∉ U.1 ∧ z₂ ∉ U.1 ∧
            ∀ u ∈ U.1, (graphOf ω).Adj z₁ u ∧ (graphOf ω).Adj z₂ u) ≤ P.p ^ (2 * P.C_codeg) := by
        intro ⟨U, hU⟩
        by_cases hnot : z₁ ∉ U ∧ z₂ ∉ U
        · rcases hnot with ⟨hz1, hz2⟩
          have hUcard : U.card = P.C_codeg := (Finset.mem_powersetCard.mp hU).2
          let E₁ : Finset (EdgeIdx P.m) := U.attach.image fun u =>
            mkEdgeIdx (show z₁ ≠ u.1 from fun h => hz1 (h ▸ u.2))
          let E₂ : Finset (EdgeIdx P.m) := U.attach.image fun u =>
            mkEdgeIdx (show z₂ ≠ u.1 from fun h => hz2 (h ▸ u.2))
          have hE1_card : E₁.card = U.card := by
            rw [Finset.card_image_of_injective]
            · exact Finset.card_attach
            · intro u₁ u₂ heq
              rcases (mkEdgeIdx_eq_iff _ _).mp heq with ⟨_, h⟩ | ⟨h, _⟩
              · exact Subtype.ext h
              · exact False.elim (hz1 (h ▸ u₂.2))
          have hE2_card : E₂.card = U.card := by
            rw [Finset.card_image_of_injective]
            · exact Finset.card_attach
            · intro u₁ u₂ heq
              rcases (mkEdgeIdx_eq_iff _ _).mp heq with ⟨_, h⟩ | ⟨h, _⟩
              · exact Subtype.ext h
              · exact False.elim (hz2 (h ▸ u₂.2))
          have hdisj : Disjoint E₁ E₂ := by
            refine Finset.disjoint_left.mpr fun e he1 he2 => ?_
            rcases Finset.mem_image.mp he1 with ⟨u₁, _, rfl⟩
            rcases Finset.mem_image.mp he2 with ⟨u₂, _, heq⟩
            rcases (mkEdgeIdx_eq_iff _ _).mp heq with ⟨h, _⟩ | ⟨h, _⟩
            · exact hne h.symm
            · exact hz2 (h ▸ u₁.2)
          have hall : ∀ ω : EdgeIdx P.m → Bool,
              (z₁ ∉ U ∧ z₂ ∉ U ∧ ∀ u ∈ U, (graphOf ω).Adj z₁ u ∧ (graphOf ω).Adj z₂ u) →
              ∀ e ∈ E₁ ∪ E₂, ω e = true := by
            intro ω ⟨_, _, hadj⟩ e he
            rcases Finset.mem_union.mp he with he1 | he2
            · rcases Finset.mem_image.mp he1 with ⟨u, _, rfl⟩
              exact (graphOf_adj_iff_mkEdgeIdx ω _).mp (hadj u.1 u.2).1
            · rcases Finset.mem_image.mp he2 with ⟨u, _, rfl⟩
              exact (graphOf_adj_iff_mkEdgeIdx ω _).mp (hadj u.1 u.2).2
          refine (bernProb_mono hp0 hp1 hall).trans ?_
          rw [bernProb_all_true, Finset.card_union_of_disjoint hdisj, hE1_card, hE2_card, hUcard,
            two_mul]
        · have h0 : bernProb P.p (fun ω => z₁ ∉ U ∧ z₂ ∉ U ∧
              ∀ u ∈ U, (graphOf ω).Adj z₁ u ∧ (graphOf ω).Adj z₂ u) = 0 := by
            simp only [bernProb]
            exact Finset.sum_eq_zero fun ω _ => if_neg (fun h => hnot ⟨h.1, h.2.1⟩)
          rw [h0]; positivity
      calc ∑ U : { U : Finset (Fin P.m) // U ∈ cands },
            bernProb P.p (fun ω => z₁ ∉ U.1 ∧ z₂ ∉ U.1 ∧
              ∀ u ∈ U.1, (graphOf ω).Adj z₁ u ∧ (graphOf ω).Adj z₂ u)
          ≤ ∑ _U : { U : Finset (Fin P.m) // U ∈ cands }, P.p ^ (2 * P.C_codeg) :=
            Finset.sum_le_sum fun U _ => hU_bound U
        _ = (P.m.choose P.C_codeg : ℝ) * P.p ^ (2 * P.C_codeg) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, Finset.card_powersetCard,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ (Real.exp 1 * (P.m : ℝ) / (P.C_codeg : ℝ)) ^ P.C_codeg * (P.p ^ 2) ^ P.C_codeg := by
            rw [← pow_mul]
            exact mul_le_mul_of_nonneg_right (choose_le_exp_pow hC) (by positivity)
        _ = (Real.exp 1 * (P.m : ℝ) * P.p ^ 2 / (P.C_codeg : ℝ)) ^ P.C_codeg := by
            rw [← mul_pow]; congr 1; ring
  calc ∑ q : Fin P.m × Fin P.m, _
      ≤ ∑ _q : Fin P.m × Fin P.m,
          (Real.exp 1 * (P.m : ℝ) * P.p ^ 2 / (P.C_codeg : ℝ)) ^ P.C_codeg :=
        Finset.sum_le_sum fun q _ => hpair q
    _ = (P.m : ℝ) ^ 2 * (Real.exp 1 * (P.m : ℝ) * P.p ^ 2 / (P.C_codeg : ℝ)) ^ P.C_codeg := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_mul]; ring

/-- Reusable exterior bipartite edge-count bound: for disjoint `T, S ⊆ Fin m` with `|T| = r`,
`|S| = a`, and `1 ≤ r * t`, `P(∀ z ∈ T, deg(z, S) ≥ t) ≤ (e * a * p / t)^(r * t)`. -/
lemma bernProb_forall_degIn_disj_le {m r a t : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 1 ≤ r) (ht : 1 ≤ t)
    {T S : Finset (Fin m)} (hdisj : Disjoint T S) (hT : T.card = r) (hS : S.card = a) :
    bernProb p (fun ω : EdgeIdx m → Bool => ∀ z ∈ T, t ≤ degIn (graphOf ω) S z) ≤
      (Real.exp 1 * (a : ℝ) * p / (t : ℝ)) ^ (r * t) := by
  let E_TS : Finset (EdgeIdx m) := (T ×ˢ S).attach.image fun q =>
    mkEdgeIdx (show q.1.1 ≠ q.1.2 from fun h =>
      Finset.disjoint_left.mp hdisj (Finset.mem_product.mp q.2).1 (h ▸ (Finset.mem_product.mp q.2).2))
  have hE_card : E_TS.card = r * a := by
    rw [Finset.card_image_of_injective]
    · rw [Finset.card_attach, Finset.card_product, hT, hS]
    · intro q₁ q₂ heq
      rcases (mkEdgeIdx_eq_iff _ _).mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Subtype.ext (Prod.ext h1 h2)
      · exact False.elim (Finset.disjoint_left.mp hdisj
          (Finset.mem_product.mp q₁.2).1 (h1 ▸ (Finset.mem_product.mp q₂.2).2))
  have himp : ∀ ω : EdgeIdx m → Bool, (∀ z ∈ T, t ≤ degIn (graphOf ω) S z) →
      r * t ≤ (E_TS.filter fun e => ω e = true).card := by
    intro ω hdeg
    have hsum : r * t ≤ ∑ z ∈ T, degIn (graphOf ω) S z := by
      calc r * t = ∑ _z ∈ T, t := by rw [Finset.sum_const, hT, smul_eq_mul]
        _ ≤ ∑ z ∈ T, degIn (graphOf ω) S z := Finset.sum_le_sum fun z hz => hdeg z hz
    have hbij : ∑ z ∈ T, degIn (graphOf ω) S z = (E_TS.filter fun e => ω e = true).card := by
      dsimp only [degIn]
      rw [← Finset.card_sigma]
      refine Finset.card_bij
        (fun x hx => mkEdgeIdx (show x.1 ≠ x.2 from fun h =>
          Finset.disjoint_left.mp hdisj (Finset.mem_sigma.mp hx).1
            (h ▸ (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).1)))
        ?_ ?_ ?_
      · intro x hx
        rcases Finset.mem_sigma.mp hx with ⟨hzT, hxu⟩
        rcases Finset.mem_filter.mp hxu with ⟨huS, hadj⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
          ⟨⟨(x.1, x.2), Finset.mem_product.mpr ⟨hzT, huS⟩⟩, Finset.mem_attach _ _, rfl⟩,
          (graphOf_adj_iff_mkEdgeIdx ω _).mp hadj⟩
      · intro x₁ hx₁ x₂ hx₂ heq
        rcases (mkEdgeIdx_eq_iff _ _).mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Sigma.ext h1 (heq_of_eq h2)
        · exact False.elim (Finset.disjoint_left.mp hdisj (Finset.mem_sigma.mp hx₁).1
            (h1 ▸ (Finset.mem_filter.mp (Finset.mem_sigma.mp hx₂).2).1))
      · intro e he
        rcases Finset.mem_filter.mp he with ⟨heE, htrue⟩
        rcases Finset.mem_image.mp heE with ⟨⟨⟨z, u⟩, hzu⟩, _, rfl⟩
        rcases Finset.mem_product.mp hzu with ⟨hzT, huS⟩
        refine ⟨⟨z, u⟩, Finset.mem_sigma.mpr ⟨hzT, Finset.mem_filter.mpr ⟨huS,
          (graphOf_adj_iff_mkEdgeIdx ω _).mpr htrue⟩⟩, rfl⟩
    omega
  have hrt : 1 ≤ r * t := Nat.mul_pos (by omega) (by omega)
  refine (bernProb_mono hp0 hp1 himp).trans ?_
  have hbp := bernProb_binom_ge_pow hp0 hp1 E_TS hrt
  rw [hE_card] at hbp
  refine hbp.trans (le_of_eq ?_)
  have hr0 : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  congr 1; push_cast; field_simp [hr0]

/-- Reusable interior edge-count bound: for `T ⊆ S ⊆ Fin m` with `|T| = r`, `|S| = a`,
`P(∀ z ∈ T, deg(z, S) ≥ t) ≤ (2 * e * a * p / t)^((r * t + 1) / 2)`. -/
lemma bernProb_forall_degIn_subset_le {m r a t : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 1 ≤ r) (ht : 1 ≤ t)
    {T S : Finset (Fin m)} (_hTS : T ⊆ S) (hT : T.card = r) (hS : S.card = a) :
    bernProb p (fun ω : EdgeIdx m → Bool => ∀ z ∈ T, t ≤ degIn (graphOf ω) S z) ≤
      (2 * Real.exp 1 * (a : ℝ) * p / (t : ℝ)) ^ ((r * t + 1) / 2) := by
  let E_TS : Finset (EdgeIdx m) := Finset.univ.filter fun e =>
    (e.1.1 ∈ T ∧ e.1.2 ∈ S) ∨ (e.1.2 ∈ T ∧ e.1.1 ∈ S)
  have hE_le : E_TS.card ≤ r * a := by
    let Q := (T ×ˢ S).filter fun q : Fin m × Fin m => q.1 ≠ q.2
    have hsub : E_TS ⊆ Q.attach.image (fun q =>
        mkEdgeIdx (Finset.mem_filter.mp (show q.1 ∈ (T ×ˢ S).filter (fun q : Fin m × Fin m => q.1 ≠ q.2) from q.2)).2) := by
      intro e he
      rcases (Finset.mem_filter.mp he).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine Finset.mem_image.mpr ⟨⟨(e.1.1, e.1.2), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨h1, h2⟩, e.2.ne⟩⟩, Finset.mem_attach _ _, ?_⟩
        simp [mkEdgeIdx, e.2]
      · refine Finset.mem_image.mpr ⟨⟨(e.1.2, e.1.1), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨h1, h2⟩, e.2.ne'⟩⟩, Finset.mem_attach _ _, ?_⟩
        have hnot : ¬ e.1.2 < e.1.1 := lt_asymm e.2
        simp [mkEdgeIdx, hnot]
    calc E_TS.card
        ≤ (Q.attach.image _).card := Finset.card_le_card hsub
      _ ≤ Q.attach.card := Finset.card_image_le
      _ = Q.card := Finset.card_attach
      _ ≤ (T ×ˢ S).card := Finset.card_filter_le _ _
      _ = r * a := by rw [Finset.card_product, hT, hS]
  let h : ℕ := (r * t + 1) / 2
  have hh_ge1 : 1 ≤ h := by
    have hrt : 1 ≤ r * t := Nat.mul_pos (by omega) (by omega)
    omega
  have himp : ∀ ω : EdgeIdx m → Bool, (∀ z ∈ T, t ≤ degIn (graphOf ω) S z) →
      h ≤ (E_TS.filter fun e => ω e = true).card := by
    intro ω hdeg
    have hsum : r * t ≤ ∑ z ∈ T, degIn (graphOf ω) S z := by
      calc r * t = ∑ _z ∈ T, t := by rw [Finset.sum_const, hT, smul_eq_mul]
        _ ≤ ∑ z ∈ T, degIn (graphOf ω) S z := Finset.sum_le_sum fun z hz => hdeg z hz
    let pairs := T.sigma fun z => S.filter fun u => (graphOf ω).Adj z u
    have hpairs_eq : pairs.card = ∑ z ∈ T, degIn (graphOf ω) S z := Finset.card_sigma _ _
    let E_true := E_TS.filter fun e => ω e = true
    have h2 : pairs.card ≤ 2 * E_true.card := by
      let P1 := pairs.filter fun x => x.1 < x.2
      let P2 := pairs.filter fun x => x.2 < x.1
      have hcov : pairs ⊆ P1 ∪ P2 := by
        intro x hx
        have hadj := (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).2
        rcases lt_or_gt_of_ne ((graphOf ω).ne_of_adj hadj) with hlt | hgt
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hlt⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, hgt⟩)
      have hP1 : P1.card ≤ E_true.card := by
        rw [← Finset.card_attach (s := P1)]
        refine Finset.card_le_card_of_injOn (fun x => ⟨(x.1.1, x.1.2), (Finset.mem_filter.mp x.2).2⟩) ?_ ?_
        · intro x _
          rcases Finset.mem_filter.mp x.2 with ⟨hxp, hlt⟩
          rcases Finset.mem_sigma.mp hxp with ⟨hzT, hxu⟩
          rcases Finset.mem_filter.mp hxu with ⟨huS, hadj⟩
          change (⟨(x.1.1, x.1.2), hlt⟩ : EdgeIdx m) ∈ E_true
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨hzT, huS⟩⟩, ?_⟩
          simpa only [graphOf, dif_pos hlt] using hadj
        · intro x₁ _ x₂ _ heq
          have hv := congrArg Subtype.val heq
          exact Subtype.ext (Sigma.ext (congrArg Prod.fst hv) (heq_of_eq (congrArg Prod.snd hv)))
      have hP2 : P2.card ≤ E_true.card := by
        rw [← Finset.card_attach (s := P2)]
        refine Finset.card_le_card_of_injOn (fun x => ⟨(x.1.2, x.1.1), (Finset.mem_filter.mp x.2).2⟩) ?_ ?_
        · intro x _
          rcases Finset.mem_filter.mp x.2 with ⟨hxp, hgt⟩
          rcases Finset.mem_sigma.mp hxp with ⟨hzT, hxu⟩
          rcases Finset.mem_filter.mp hxu with ⟨huS, hadj⟩
          change (⟨(x.1.2, x.1.1), hgt⟩ : EdgeIdx m) ∈ E_true
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨hzT, huS⟩⟩, ?_⟩
          have hnot : ¬ x.1.1 < x.1.2 := lt_asymm hgt
          simpa only [graphOf, dif_neg hnot, dif_pos hgt] using hadj
        · intro x₁ _ x₂ _ heq
          have hv := congrArg Subtype.val heq
          exact Subtype.ext (Sigma.ext (congrArg Prod.snd hv) (heq_of_eq (congrArg Prod.fst hv)))
      calc pairs.card ≤ (P1 ∪ P2).card := Finset.card_le_card hcov
        _ ≤ P1.card + P2.card := Finset.card_union_le P1 P2
        _ ≤ E_true.card + E_true.card := add_le_add hP1 hP2
        _ = 2 * E_true.card := by ring
    change h ≤ E_true.card
    omega
  refine (bernProb_mono hp0 hp1 himp).trans ?_
  refine (bernProb_binom_ge_pow hp0 hp1 E_TS hh_ge1).trans ?_
  refine pow_le_pow_left₀ (by positivity) ?_ h
  have hh_pos : (0 : ℝ) < (h : ℝ) := Nat.cast_pos.mpr (by omega)
  have ht_pos : (0 : ℝ) < (t : ℝ) := Nat.cast_pos.mpr (by omega)
  have h2h : (r : ℝ) * (t : ℝ) ≤ 2 * (h : ℝ) := by
    have : r * t ≤ 2 * h := by omega
    exact_mod_cast this
  have hE_real : (E_TS.card : ℝ) ≤ (r : ℝ) * (a : ℝ) := by exact_mod_cast hE_le
  rw [div_le_div_iff₀ hh_pos ht_pos]
  calc Real.exp 1 * (E_TS.card : ℝ) * p * (t : ℝ)
      ≤ Real.exp 1 * ((r : ℝ) * (a : ℝ)) * p * (t : ℝ) := by gcongr
    _ = Real.exp 1 * (a : ℝ) * p * ((r : ℝ) * (t : ℝ)) := by ring
    _ ≤ Real.exp 1 * (a : ℝ) * p * (2 * (h : ℝ)) := by gcongr
    _ = 2 * Real.exp 1 * (a : ℝ) * p * (h : ℝ) := by ring

/-- Bound on `P(¬ GoodExtDegMid P ω)`. -/
lemma bernProb_not_goodExtDegMid_le (P : RegParams)
    (hp0 : 0 ≤ P.p) (hp1 : P.p ≤ 1)
    (hrmid_pos : ∀ i : Fin P.L, ∀ j : Fin P.J, 1 ≤ j.val →
      P.T_lo ≤ ((2 ^ i.val : ℕ) : ℝ) * ((2 ^ j.val : ℕ) : ℝ) →
      ((2 ^ i.val : ℕ) : ℝ) * ((2 ^ j.val : ℕ) : ℝ) ≤ P.T_mid → 1 ≤ P.rMid i.val j.val) :
    bernProb P.p (fun ω => ¬ GoodExtDegMid P ω) ≤
      ∑ i : Fin P.L, ∑ j : Fin P.J,
        if 1 ≤ j.val ∧ P.T_lo ≤ ((2 ^ i.val : ℕ) : ℝ) * ((2 ^ j.val : ℕ) : ℝ) ∧
            ((2 ^ i.val : ℕ) : ℝ) * ((2 ^ j.val : ℕ) : ℝ) ≤ P.T_mid then
          (P.m : ℝ) ^ P.clsSize i.val *
            (Real.exp 1 * (P.m : ℝ) / (P.rMid i.val j.val : ℝ) *
              (Real.exp 1 * (P.clsSize i.val : ℝ) * P.p / ((2 ^ j.val : ℕ) : ℝ)) ^ (2 ^ j.val)) ^
              P.rMid i.val j.val
        else 0 := by
  have himp : ∀ ω : EdgeIdx P.m → Bool, ¬ GoodExtDegMid P ω →
      ∃ ij : Fin P.L × Fin P.J,
        (1 ≤ ij.2.val ∧ P.T_lo ≤ ((2 ^ ij.1.val : ℕ) : ℝ) * ((2 ^ ij.2.val : ℕ) : ℝ) ∧
          ((2 ^ ij.1.val : ℕ) : ℝ) * ((2 ^ ij.2.val : ℕ) : ℝ) ≤ P.T_mid) ∧
        ∃ S ∈ (Finset.univ : Finset (Fin P.m)).powersetCard (P.clsSize ij.1.val),
          P.rMid ij.1.val ij.2.val ≤
            ((Finset.univ \ S).filter fun z => 2 ^ ij.2.val ≤ degIn (graphOf ω) S z).card := by
    intro ω hnot
    simp only [GoodExtDegMid, not_forall, not_lt] at hnot
    rcases hnot with ⟨i, j, hj1, hlo, hmid, S, hS, hge⟩
    exact ⟨(i, j), ⟨hj1, hlo, hmid⟩, S, hS, hge⟩
  refine (bernProb_mono hp0 hp1 himp).trans ?_
  refine (bernProb_exists_univ_le hp0 hp1 _).trans ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases hcond : 1 ≤ j.val ∧ P.T_lo ≤ ((2 ^ i.val : ℕ) : ℝ) * ((2 ^ j.val : ℕ) : ℝ) ∧
      ((2 ^ i.val : ℕ) : ℝ) * ((2 ^ j.val : ℕ) : ℝ) ≤ P.T_mid
  · rw [if_pos hcond]
    set a := P.clsSize i.val
    set t := 2 ^ j.val
    set r := P.rMid i.val j.val
    have hr1 : 1 ≤ r := hrmid_pos i j hcond.1 hcond.2.1 hcond.2.2
    have ht1 : 1 ≤ t := Nat.one_le_pow _ _ (by omega)
    let candsS := (Finset.univ : Finset (Fin P.m)).powersetCard a
    let candsT := (Finset.univ : Finset (Fin P.m)).powersetCard r
    have hcov : ∀ ω : EdgeIdx P.m → Bool,
        ((1 ≤ j.val ∧ P.T_lo ≤ ((2 ^ i.val : ℕ) : ℝ) * ((2 ^ j.val : ℕ) : ℝ) ∧
            ((2 ^ i.val : ℕ) : ℝ) * ((2 ^ j.val : ℕ) : ℝ) ≤ P.T_mid) ∧
          ∃ S ∈ candsS, r ≤ ((Finset.univ \ S).filter fun z => t ≤ degIn (graphOf ω) S z).card) →
        ∃ ST : { S // S ∈ candsS } × { T // T ∈ candsT },
          Disjoint ST.2.1 ST.1.1 ∧ ∀ z ∈ ST.2.1, t ≤ degIn (graphOf ω) ST.1.1 z := by
      intro ω ⟨_, S, hS, hge⟩
      obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hge
      have hTmem : T ∈ candsT := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hTcard⟩
      have hdisj : Disjoint T S := Finset.disjoint_left.mpr fun z hzT hzS =>
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hTsub hzT)).1).2 hzS
      exact ⟨(⟨S, hS⟩, ⟨T, hTmem⟩), hdisj, fun z hz => (Finset.mem_filter.mp (hTsub hz)).2⟩
    refine (bernProb_mono hp0 hp1 hcov).trans ?_
    refine (bernProb_exists_univ_le hp0 hp1 _).trans ?_
    have hterm : ∀ ST : { S // S ∈ candsS } × { T // T ∈ candsT },
        bernProb P.p (fun ω => Disjoint ST.2.1 ST.1.1 ∧ ∀ z ∈ ST.2.1, t ≤ degIn (graphOf ω) ST.1.1 z) ≤
          (Real.exp 1 * (a : ℝ) * P.p / (t : ℝ)) ^ (r * t) := by
      intro ⟨⟨S, hS⟩, ⟨T, hT⟩⟩
      by_cases hdisj : Disjoint T S
      · refine (bernProb_mono hp0 hp1 fun ω h => h.2).trans ?_
        exact bernProb_forall_degIn_disj_le hp0 hp1 hr1 ht1 hdisj
          (Finset.mem_powersetCard.mp hT).2 (Finset.mem_powersetCard.mp hS).2
      · have h0 : bernProb P.p (fun ω => Disjoint T S ∧ ∀ z ∈ T, t ≤ degIn (graphOf ω) S z) = 0 := by
          simp only [bernProb]; exact Finset.sum_eq_zero fun _ _ => if_neg (fun h => hdisj h.1)
        rw [h0]; positivity
    calc ∑ ST : { S // S ∈ candsS } × { T // T ∈ candsT }, _
        ≤ ∑ _ST : { S // S ∈ candsS } × { T // T ∈ candsT },
            (Real.exp 1 * (a : ℝ) * P.p / (t : ℝ)) ^ (r * t) :=
          Finset.sum_le_sum fun ST _ => hterm ST
      _ = (P.m.choose a : ℝ) * (P.m.choose r : ℝ) *
            (Real.exp 1 * (a : ℝ) * P.p / (t : ℝ)) ^ (r * t) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_coe, Fintype.card_coe,
            Finset.card_powersetCard, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_mul]
      _ ≤ (P.m : ℝ) ^ a * (Real.exp 1 * (P.m : ℝ) / (r : ℝ)) ^ r *
            ((Real.exp 1 * (a : ℝ) * P.p / (t : ℝ)) ^ t) ^ r := by
          have hma : (P.m.choose a : ℝ) ≤ (P.m : ℝ) ^ a := by exact_mod_cast choose_le_pow P.m a
          have hmr : (P.m.choose r : ℝ) ≤ (Real.exp 1 * (P.m : ℝ) / (r : ℝ)) ^ r := choose_le_exp_pow hr1
          rw [mul_comm r t, pow_mul]
          have h1 : (P.m.choose a : ℝ) * (P.m.choose r : ℝ) ≤
              (P.m : ℝ) ^ a * (Real.exp 1 * (P.m : ℝ) / (r : ℝ)) ^ r :=
            mul_le_mul hma hmr (Nat.cast_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (P.m : ℝ) ^ a *
            (Real.exp 1 * (P.m : ℝ) / (r : ℝ) * (Real.exp 1 * (a : ℝ) * P.p / (t : ℝ)) ^ t) ^ r := by
          rw [mul_assoc, ← mul_pow]
  · rw [if_neg hcond]
    have h0 : bernProb P.p (fun ω =>
        (1 ≤ j.val ∧ P.T_lo ≤ ((2 ^ i.val : ℕ) : ℝ) * ((2 ^ j.val : ℕ) : ℝ) ∧
            ((2 ^ i.val : ℕ) : ℝ) * ((2 ^ j.val : ℕ) : ℝ) ≤ P.T_mid) ∧
          ∃ S ∈ (Finset.univ : Finset (Fin P.m)).powersetCard (P.clsSize i.val),
            P.rMid i.val j.val ≤
              ((Finset.univ \ S).filter fun z => 2 ^ j.val ≤ degIn (graphOf ω) S z).card) = 0 := by
      simp only [bernProb]; exact Finset.sum_eq_zero fun _ _ => if_neg (fun h => hcond h.1)
    rw [h0]

/-- Bound on `P(¬ GoodDegLarge P ω)`. -/
lemma bernProb_not_goodDegLarge_le (P : RegParams)
    (hp0 : 0 ≤ P.p) (hp1 : P.p ≤ 1) :
    bernProb P.p (fun ω => ¬ GoodDegLarge P ω) ≤
      ∑ i : Fin P.L, ∑ j : Fin P.J,
        if P.T_mid < ((2 ^ i.val : ℕ) : ℝ) * ((2 ^ j.val : ℕ) : ℝ) then
          (P.m : ℝ) ^ (P.clsSize i.val + P.rLargeOut i.val j.val) *
            (Real.exp 1 * (P.clsSize i.val : ℝ) * P.p / ((2 ^ j.val : ℕ) : ℝ)) ^
              (P.rLargeOut i.val j.val * 2 ^ j.val) +
          (2 * (P.m : ℝ)) ^ P.clsSize i.val *
            (2 * Real.exp 1 * (P.clsSize i.val : ℝ) * P.p / ((2 ^ j.val : ℕ) : ℝ)) ^
              ((P.rLargeIn i.val j.val * 2 ^ j.val + 1) / 2)
        else 0 := by
  have himp : ∀ ω : EdgeIdx P.m → Bool, ¬ GoodDegLarge P ω →
      ∃ ij : Fin P.L × Fin P.J,
        P.T_mid < ((2 ^ ij.1.val : ℕ) : ℝ) * ((2 ^ ij.2.val : ℕ) : ℝ) ∧
        ((∃ S ∈ (Finset.univ : Finset (Fin P.m)).powersetCard (P.clsSize ij.1.val),
            P.rLargeOut ij.1.val ij.2.val ≤
              ((Finset.univ \ S).filter fun z => 2 ^ ij.2.val ≤ degIn (graphOf ω) S z).card) ∨
         (∃ S ∈ (Finset.univ : Finset (Fin P.m)).powersetCard (P.clsSize ij.1.val),
            P.rLargeIn ij.1.val ij.2.val ≤
              (S.filter fun z => 2 ^ ij.2.val ≤ degIn (graphOf ω) S z).card)) := by
    intro ω hnot
    simp only [GoodDegLarge, not_forall, not_and_or, not_lt] at hnot
    rcases hnot with ⟨i, j, hgt, S, hS, h1 | h2⟩
    · exact ⟨(i, j), hgt, Or.inl ⟨S, hS, h1⟩⟩
    · exact ⟨(i, j), hgt, Or.inr ⟨S, hS, h2⟩⟩
  refine (bernProb_mono hp0 hp1 himp).trans ?_
  refine (bernProb_exists_univ_le hp0 hp1 _).trans ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases hgt : P.T_mid < ((2 ^ i.val : ℕ) : ℝ) * ((2 ^ j.val : ℕ) : ℝ)
  · rw [if_pos hgt]
    set a := P.clsSize i.val
    set t := 2 ^ j.val
    set ro := P.rLargeOut i.val j.val
    set ri := P.rLargeIn i.val j.val
    have hro1 : 1 ≤ ro := by dsimp only [ro, RegParams.rLargeOut]; omega
    have hri1 : 1 ≤ ri := by dsimp only [ri, RegParams.rLargeIn]; omega
    have ht1 : 1 ≤ t := Nat.one_le_pow _ _ (by omega)
    let candsS := (Finset.univ : Finset (Fin P.m)).powersetCard a
    refine (bernProb_mono hp0 hp1 fun ω h => h.2).trans ?_
    refine (bernProb_or_le hp0 hp1 _ _).trans ?_
    refine add_le_add ?_ ?_
    · -- Exterior part
      let candsT := (Finset.univ : Finset (Fin P.m)).powersetCard ro
      have hcov : ∀ ω : EdgeIdx P.m → Bool,
          (∃ S ∈ candsS, ro ≤ ((Finset.univ \ S).filter fun z => t ≤ degIn (graphOf ω) S z).card) →
          ∃ ST : { S // S ∈ candsS } × { T // T ∈ candsT },
            Disjoint ST.2.1 ST.1.1 ∧ ∀ z ∈ ST.2.1, t ≤ degIn (graphOf ω) ST.1.1 z := by
        intro ω ⟨S, hS, hge⟩
        obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hge
        exact ⟨(⟨S, hS⟩, ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hTcard⟩⟩),
          Finset.disjoint_left.mpr fun z hzT hzS =>
            (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hTsub hzT)).1).2 hzS,
          fun z hz => (Finset.mem_filter.mp (hTsub hz)).2⟩
      refine (bernProb_mono hp0 hp1 hcov).trans ((bernProb_exists_univ_le hp0 hp1 _).trans ?_)
      have hterm : ∀ ST : { S // S ∈ candsS } × { T // T ∈ candsT },
          bernProb P.p (fun ω => Disjoint ST.2.1 ST.1.1 ∧ ∀ z ∈ ST.2.1, t ≤ degIn (graphOf ω) ST.1.1 z) ≤
            (Real.exp 1 * (a : ℝ) * P.p / (t : ℝ)) ^ (ro * t) := by
        intro ⟨⟨S, hS⟩, ⟨T, hT⟩⟩
        by_cases hdisj : Disjoint T S
        · exact (bernProb_mono hp0 hp1 fun _ h => h.2).trans
            (bernProb_forall_degIn_disj_le hp0 hp1 hro1 ht1 hdisj
              (Finset.mem_powersetCard.mp hT).2 (Finset.mem_powersetCard.mp hS).2)
        · have h0 : bernProb P.p (fun ω => Disjoint T S ∧ ∀ z ∈ T, t ≤ degIn (graphOf ω) S z) = 0 := by
            simp only [bernProb]; exact Finset.sum_eq_zero fun _ _ => if_neg (fun h => hdisj h.1)
          rw [h0]; positivity
      calc ∑ ST : { S // S ∈ candsS } × { T // T ∈ candsT }, _
          ≤ ∑ _ST : { S // S ∈ candsS } × { T // T ∈ candsT },
              (Real.exp 1 * (a : ℝ) * P.p / (t : ℝ)) ^ (ro * t) :=
            Finset.sum_le_sum fun ST _ => hterm ST
        _ = (P.m.choose a : ℝ) * (P.m.choose ro : ℝ) *
              (Real.exp 1 * (a : ℝ) * P.p / (t : ℝ)) ^ (ro * t) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_coe, Fintype.card_coe,
              Finset.card_powersetCard, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul, Nat.cast_mul]
        _ ≤ (P.m : ℝ) ^ (a + ro) * (Real.exp 1 * (a : ℝ) * P.p / (t : ℝ)) ^ (ro * t) := by
            rw [pow_add]
            have h1 : (P.m.choose a : ℝ) ≤ (P.m : ℝ) ^ a := by exact_mod_cast choose_le_pow P.m a
            have h2 : (P.m.choose ro : ℝ) ≤ (P.m : ℝ) ^ ro := by exact_mod_cast choose_le_pow P.m ro
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)) (by positivity)
    · -- Interior part
      have hcov : ∀ ω : EdgeIdx P.m → Bool,
          (∃ S ∈ candsS, ri ≤ (S.filter fun z => t ≤ degIn (graphOf ω) S z).card) →
          ∃ ST : Sigma (fun S : { S // S ∈ candsS } => { T : Finset (Fin P.m) // T ∈ S.1.powersetCard ri }),
            ∀ z ∈ ST.2.1, t ≤ degIn (graphOf ω) ST.1.1 z := by
        intro ω ⟨S, hS, hge⟩
        obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hge
        have hTS : T ⊆ S := hTsub.trans (Finset.filter_subset _ _)
        exact ⟨⟨⟨S, hS⟩, ⟨T, Finset.mem_powersetCard.mpr ⟨hTS, hTcard⟩⟩⟩,
          fun z hz => (Finset.mem_filter.mp (hTsub hz)).2⟩
      refine (bernProb_mono hp0 hp1 hcov).trans ((bernProb_exists_univ_le hp0 hp1 _).trans ?_)
      have hterm : ∀ ST : Sigma (fun S : { S // S ∈ candsS } => { T // T ∈ S.1.powersetCard ri }),
          bernProb P.p (fun ω => ∀ z ∈ ST.2.1, t ≤ degIn (graphOf ω) ST.1.1 z) ≤
            (2 * Real.exp 1 * (a : ℝ) * P.p / (t : ℝ)) ^ ((ri * t + 1) / 2) := by
        intro ⟨⟨S, hS⟩, ⟨T, hT⟩⟩
        exact bernProb_forall_degIn_subset_le hp0 hp1 hri1 ht1
          (Finset.mem_powersetCard.mp hT).1 (Finset.mem_powersetCard.mp hT).2
          (Finset.mem_powersetCard.mp hS).2
      calc ∑ ST : Sigma (fun S : { S // S ∈ candsS } => { T // T ∈ S.1.powersetCard ri }), _
          ≤ ∑ _ST : Sigma (fun S : { S // S ∈ candsS } => { T // T ∈ S.1.powersetCard ri }),
              (2 * Real.exp 1 * (a : ℝ) * P.p / (t : ℝ)) ^ ((ri * t + 1) / 2) :=
            Finset.sum_le_sum fun ST _ => hterm ST
        _ = (P.m.choose a : ℝ) * (a.choose ri : ℝ) *
              (2 * Real.exp 1 * (a : ℝ) * P.p / (t : ℝ)) ^ ((ri * t + 1) / 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_sigma, nsmul_eq_mul]
            have hcard : ∑ S : { S // S ∈ candsS }, Fintype.card { T // T ∈ S.1.powersetCard ri } =
                P.m.choose a * a.choose ri := by
              calc ∑ S : { S // S ∈ candsS }, Fintype.card { T // T ∈ S.1.powersetCard ri }
                  = ∑ S : { S // S ∈ candsS }, a.choose ri := by
                    refine Finset.sum_congr rfl fun ⟨S, hS⟩ _ => ?_
                    rw [Fintype.card_coe, Finset.card_powersetCard, (Finset.mem_powersetCard.mp hS).2]
                _ = P.m.choose a * a.choose ri := by
                    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
                      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
            rw [hcard, Nat.cast_mul]
        _ ≤ (2 * (P.m : ℝ)) ^ a *
              (2 * Real.exp 1 * (a : ℝ) * P.p / (t : ℝ)) ^ ((ri * t + 1) / 2) := by
            rw [mul_pow, mul_comm ((2 : ℝ) ^ a)]
            have h1 : (P.m.choose a : ℝ) ≤ (P.m : ℝ) ^ a := by exact_mod_cast choose_le_pow P.m a
            have h2 : (a.choose ri : ℝ) ≤ (2 : ℝ) ^ a := by
              have : a.choose ri ≤ 2 ^ a := by
                have hsum := Nat.sum_range_choose a
                by_cases hle : ri ≤ a
                · exact (Finset.single_le_sum (f := fun k => a.choose k) (fun _ _ => Nat.zero_le _)
                    (Finset.mem_range.mpr (by omega))).trans hsum.le
                · rw [Nat.choose_eq_zero_of_lt (by omega)]; exact Nat.zero_le _
              exact_mod_cast this
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)) (by positivity)
  · rw [if_neg hgt]
    simp only [bernProb]
    exact (Finset.sum_eq_zero fun _ _ => if_neg (fun h => hgt h.1)).le

/-- Bound on `P(¬ GoodCrossPair P ω)`. -/
lemma bernProb_not_goodCrossPair_le (P : RegParams)
    (hp0 : 0 ≤ P.p) (hp1 : P.p ≤ 1)
    (hrcross_pos : ∀ i i' : Fin P.L, i.val < i'.val → 1 ≤ P.rCross i.val i'.val) :
    bernProb P.p (fun ω => ¬ GoodCrossPair P ω) ≤
      ∑ i : Fin P.L, ∑ i' : Fin P.L,
        if i.val < i'.val then
          (P.m : ℝ) ^ (P.clsSize i.val + P.clsSize i'.val) *
            (Real.exp 1 * (P.m : ℝ) * (P.clsSize i.val : ℝ) * (P.clsSize i'.val : ℝ) * P.p ^ 2 /
              (P.rCross i.val i'.val : ℝ)) ^ P.rCross i.val i'.val
        else 0 := by
  have himp : ∀ ω : EdgeIdx P.m → Bool, ¬ GoodCrossPair P ω →
      ∃ ii : Fin P.L × Fin P.L, ii.1.val < ii.2.val ∧
        ∃ S₁ ∈ (Finset.univ : Finset (Fin P.m)).powersetCard (P.clsSize ii.1.val),
        ∃ S₂ ∈ (Finset.univ : Finset (Fin P.m)).powersetCard (P.clsSize ii.2.val),
          Disjoint S₁ S₂ ∧ P.rCross ii.1.val ii.2.val ≤
            ((Finset.univ \ (S₁ ∪ S₂)).filter fun z =>
              1 ≤ degIn (graphOf ω) S₁ z ∧ 1 ≤ degIn (graphOf ω) S₂ z).card := by
    intro ω hnot
    simp only [GoodCrossPair, not_forall, not_lt] at hnot
    rcases hnot with ⟨i, i', hlt, S₁, hS1, S₂, hS2, hdisj, hge⟩
    exact ⟨(i, i'), hlt, S₁, hS1, S₂, hS2, hdisj, hge⟩
  refine (bernProb_mono hp0 hp1 himp).trans ((bernProb_exists_univ_le hp0 hp1 _).trans ?_)
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun i' _ => ?_
  by_cases hlt : i.val < i'.val
  · rw [if_pos hlt]
    set a₁ := P.clsSize i.val
    set a₂ := P.clsSize i'.val
    set r := P.rCross i.val i'.val
    have hr1 : 1 ≤ r := hrcross_pos i i' hlt
    let cands1 := (Finset.univ : Finset (Fin P.m)).powersetCard a₁
    let cands2 := (Finset.univ : Finset (Fin P.m)).powersetCard a₂
    let candsT := (Finset.univ : Finset (Fin P.m)).powersetCard r
    have hcov : ∀ ω : EdgeIdx P.m → Bool,
        (i.val < i'.val ∧ ∃ S₁ ∈ cands1, ∃ S₂ ∈ cands2, Disjoint S₁ S₂ ∧
          r ≤ ((Finset.univ \ (S₁ ∪ S₂)).filter fun z =>
            1 ≤ degIn (graphOf ω) S₁ z ∧ 1 ≤ degIn (graphOf ω) S₂ z).card) →
        ∃ q : { S₁ // S₁ ∈ cands1 } × { S₂ // S₂ ∈ cands2 } × { T // T ∈ candsT },
          Disjoint q.1.1 q.2.1.1 ∧ Disjoint q.2.2.1 (q.1.1 ∪ q.2.1.1) ∧
          ∀ z ∈ q.2.2.1, 1 ≤ degIn (graphOf ω) q.1.1 z ∧ 1 ≤ degIn (graphOf ω) q.2.1.1 z := by
      intro ω ⟨_, S₁, hS1, S₂, hS2, hdisj12, hge⟩
      obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hge
      have hdisjT : Disjoint T (S₁ ∪ S₂) := Finset.disjoint_left.mpr fun z hzT hz12 =>
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hTsub hzT)).1).2 hz12
      exact ⟨(⟨S₁, hS1⟩, ⟨S₂, hS2⟩, ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hTcard⟩⟩),
        hdisj12, hdisjT, fun z hz => (Finset.mem_filter.mp (hTsub hz)).2⟩
    refine (bernProb_mono hp0 hp1 hcov).trans ((bernProb_exists_univ_le hp0 hp1 _).trans ?_)
    have hsingle : ∀ q : { S₁ // S₁ ∈ cands1 } × { S₂ // S₂ ∈ cands2 } × { T // T ∈ candsT },
        bernProb P.p (fun ω => Disjoint q.1.1 q.2.1.1 ∧ Disjoint q.2.2.1 (q.1.1 ∪ q.2.1.1) ∧
          ∀ z ∈ q.2.2.1, 1 ≤ degIn (graphOf ω) q.1.1 z ∧ 1 ≤ degIn (graphOf ω) q.2.1.1 z) ≤
          ((a₁ : ℝ) * (a₂ : ℝ) * P.p ^ 2) ^ r := by
      intro ⟨⟨S₁, hS1⟩, ⟨S₂, hS2⟩, ⟨T, hT⟩⟩
      by_cases hgood : Disjoint S₁ S₂ ∧ Disjoint T (S₁ ∪ S₂)
      · rcases hgood with ⟨hdisj12, hdisjT⟩
        have hS1c : S₁.card = a₁ := (Finset.mem_powersetCard.mp hS1).2
        have hS2c : S₂.card = a₂ := (Finset.mem_powersetCard.mp hS2).2
        have hTc : T.card = r := (Finset.mem_powersetCard.mp hT).2
        let B : T → Type := fun z => { x : Fin P.m // x ∈ S₁ } ⊕ { y : Fin P.m // y ∈ S₂ }
        let inj : (z : T) → B z → EdgeIdx P.m := fun z b =>
          Sum.casesOn b
            (fun x => mkEdgeIdx (show z.1 ≠ x.1 from fun h =>
              Finset.disjoint_left.mp hdisjT z.2 (h ▸ Finset.mem_union_left _ x.2)))
            (fun y => mkEdgeIdx (show z.1 ≠ y.1 from fun h =>
              Finset.disjoint_left.mp hdisjT z.2 (h ▸ Finset.mem_union_right _ y.2)))
        have hinj : Function.Injective (fun p : Sigma B => inj p.1 p.2) := by
          intro ⟨z₁, b₁⟩ ⟨z₂, b₂⟩ heq
          rcases b₁ with ⟨x₁, hx1⟩ | ⟨y₁, hy1⟩ <;> rcases b₂ with ⟨x₂, hx2⟩ | ⟨y₂, hy2⟩
          · rcases (mkEdgeIdx_eq_iff _ _).mp heq with ⟨hz, hx⟩ | ⟨hz, _⟩
            · exact Sigma.ext (Subtype.ext hz) (heq_of_eq (congrArg Sum.inl (Subtype.ext hx)))
            · exact False.elim (Finset.disjoint_left.mp hdisjT z₁.2 (hz ▸ Finset.mem_union_left _ hx2))
          · rcases (mkEdgeIdx_eq_iff _ _).mp heq with ⟨_, hxy⟩ | ⟨hz, _⟩
            · dsimp only at hxy
              exact False.elim (Finset.disjoint_left.mp hdisj12 hx1 (hxy ▸ hy2))
            · exact False.elim (Finset.disjoint_left.mp hdisjT z₁.2 (hz ▸ Finset.mem_union_right _ hy2))
          · rcases (mkEdgeIdx_eq_iff _ _).mp heq with ⟨_, hyx⟩ | ⟨hz, _⟩
            · dsimp only at hyx
              exact False.elim (Finset.disjoint_left.mp hdisj12 hx2 (hyx ▸ hy1))
            · exact False.elim (Finset.disjoint_left.mp hdisjT z₁.2 (hz ▸ Finset.mem_union_left _ hx2))
          · rcases (mkEdgeIdx_eq_iff _ _).mp heq with ⟨hz, hy⟩ | ⟨hz, _⟩
            · exact Sigma.ext (Subtype.ext hz) (heq_of_eq (congrArg Sum.inr (Subtype.ext hy)))
            · exact False.elim (Finset.disjoint_left.mp hdisjT z₁.2 (hz ▸ Finset.mem_union_right _ hy2))
        let imgE : Finset (EdgeIdx P.m) := Finset.univ.image fun p : Sigma B => inj p.1 p.2
        let Rest := { e : EdgeIdx P.m // e ∉ imgE }
        have : DecidablePred (fun e : EdgeIdx P.m => ∃ p : Sigma B, inj p.1 p.2 = e) := Classical.decPred _
        let eSplit : EdgeIdx P.m ≃ Sigma B ⊕ Rest :=
          { toFun := fun e =>
              if h : ∃ p : Sigma B, inj p.1 p.2 = e then Sum.inl h.choose
              else Sum.inr ⟨e, fun hm => by
                rcases Finset.mem_image.mp hm with ⟨p, _, hp⟩; exact h ⟨p, hp⟩⟩
            invFun := fun s => Sum.casesOn s (fun p => inj p.1 p.2) Subtype.val
            left_inv := fun e => by
              dsimp only; split_ifs with h
              · exact h.choose_spec
              · rfl
            right_inv := fun s => by
              rcases s with p | ⟨e, he⟩
              · dsimp only
                have hex : ∃ p' : Sigma B, inj p'.1 p'.2 = inj p.1 p.2 := ⟨p, rfl⟩
                rw [dif_pos hex]
                exact congrArg Sum.inl (hinj hex.choose_spec)
              · dsimp only
                have hno : ¬ ∃ p : Sigma B, inj p.1 p.2 = e := fun ⟨p, hp⟩ =>
                  he (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, hp⟩)
                rw [dif_neg hno] }
        let Pz : (z : T) → (B z → Bool) → Prop := fun z ωz =>
          (∃ x : { x : Fin P.m // x ∈ S₁ }, ωz (Sum.inl x) = true) ∧
          (∃ y : { y : Fin P.m // y ∈ S₂ }, ωz (Sum.inr y) = true)
        have hstep : ∀ ω : EdgeIdx P.m → Bool,
            (Disjoint S₁ S₂ ∧ Disjoint T (S₁ ∪ S₂) ∧
              ∀ z ∈ T, 1 ≤ degIn (graphOf ω) S₁ z ∧ 1 ≤ degIn (graphOf ω) S₂ z) →
            ∀ z : T, Pz z (fun b => ω (eSplit.symm (Sum.inl ⟨z, b⟩))) := by
          intro ω ⟨_, _, hdeg⟩ z
          rcases hdeg z.1 z.2 with ⟨hd1, hd2⟩
          dsimp only [degIn] at hd1 hd2
          obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < (S₁.filter fun u => (graphOf ω).Adj z.1 u).card)
          obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < (S₂.filter fun u => (graphOf ω).Adj z.1 u).card)
          rcases Finset.mem_filter.mp hx with ⟨hxS1, hadj1⟩
          rcases Finset.mem_filter.mp hy with ⟨hyS2, hadj2⟩
          refine ⟨⟨⟨x, hxS1⟩, ?_⟩, ⟨⟨y, hyS2⟩, ?_⟩⟩
          · dsimp only [eSplit, Equiv.coe_fn_symm_mk, inj]
            exact (graphOf_adj_iff_mkEdgeIdx ω _).mp hadj1
          · dsimp only [eSplit, Equiv.coe_fn_symm_mk, inj]
            exact (graphOf_adj_iff_mkEdgeIdx ω _).mp hadj2
        refine (bernProb_mono hp0 hp1 hstep).trans ?_
        rw [bernProb_equiv eSplit.symm P.p]
        simp only [Function.comp_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
        refine (bernProb_inl P.p (fun ωL : Sigma B → Bool => ∀ z : T, Pz z (fun b => ωL ⟨z, b⟩))).trans_le ?_
        rw [bernProb_pi_forall P.p Pz]
        have hPz_le : ∀ z : T, bernProb P.p (Pz z) ≤ (a₁ : ℝ) * (a₂ : ℝ) * P.p ^ 2 := by
          intro z
          rw [bernProb_sum_and P.p (fun ω1 : { x // x ∈ S₁ } → Bool => ∃ x, ω1 x = true)
            (fun ω2 : { y // y ∈ S₂ } → Bool => ∃ y, ω2 y = true)]
          have h1 : bernProb P.p (fun ω1 : { x // x ∈ S₁ } → Bool => ∃ x, ω1 x = true) ≤ (a₁ : ℝ) * P.p := by
            refine (bernProb_exists_univ_le hp0 hp1 _).trans ?_
            have hpt : ∀ x : { x // x ∈ S₁ }, bernProb P.p (fun ω1 : { x // x ∈ S₁ } → Bool => ω1 x = true) = P.p := by
              intro x
              have := bernProb_all_true P.p ({x} : Finset { x // x ∈ S₁ })
              simpa using this
            refine le_of_eq ?_
            calc ∑ x : { x // x ∈ S₁ }, bernProb P.p (fun ω1 => ω1 x = true)
                = ∑ _x : { x // x ∈ S₁ }, P.p := Finset.sum_congr rfl fun x _ => hpt x
              _ = (a₁ : ℝ) * P.p := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, hS1c, nsmul_eq_mul]
          have h2 : bernProb P.p (fun ω2 : { y // y ∈ S₂ } → Bool => ∃ y, ω2 y = true) ≤ (a₂ : ℝ) * P.p := by
            refine (bernProb_exists_univ_le hp0 hp1 _).trans ?_
            have hpt : ∀ y : { y // y ∈ S₂ }, bernProb P.p (fun ω2 : { y // y ∈ S₂ } → Bool => ω2 y = true) = P.p := by
              intro y
              have := bernProb_all_true P.p ({y} : Finset { y // y ∈ S₂ })
              simpa using this
            refine le_of_eq ?_
            calc ∑ y : { y // y ∈ S₂ }, bernProb P.p (fun ω2 => ω2 y = true)
                = ∑ _y : { y // y ∈ S₂ }, P.p := Finset.sum_congr rfl fun y _ => hpt y
              _ = (a₂ : ℝ) * P.p := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, hS2c, nsmul_eq_mul]
          calc _ ≤ ((a₁ : ℝ) * P.p) * ((a₂ : ℝ) * P.p) :=
                mul_le_mul h1 h2 (bernProb_nonneg hp0 hp1 _) (by positivity)
            _ = (a₁ : ℝ) * (a₂ : ℝ) * P.p ^ 2 := by ring
        calc ∏ z : T, bernProb P.p (Pz z)
            ≤ ∏ _z : T, ((a₁ : ℝ) * (a₂ : ℝ) * P.p ^ 2) :=
              Finset.prod_le_prod (fun z _ => bernProb_nonneg hp0 hp1 _) fun z _ => hPz_le z
          _ = ((a₁ : ℝ) * (a₂ : ℝ) * P.p ^ 2) ^ r := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, hTc]
      · have h0 : bernProb P.p (fun ω => Disjoint S₁ S₂ ∧ Disjoint T (S₁ ∪ S₂) ∧
            ∀ z ∈ T, 1 ≤ degIn (graphOf ω) S₁ z ∧ 1 ≤ degIn (graphOf ω) S₂ z) = 0 := by
          simp only [bernProb]; exact Finset.sum_eq_zero fun _ _ => if_neg (fun h => hgood ⟨h.1, h.2.1⟩)
        rw [h0]; positivity
    calc ∑ q : { S₁ // S₁ ∈ cands1 } × { S₂ // S₂ ∈ cands2 } × { T // T ∈ candsT }, _
        ≤ ∑ _q : { S₁ // S₁ ∈ cands1 } × { S₂ // S₂ ∈ cands2 } × { T // T ∈ candsT },
            ((a₁ : ℝ) * (a₂ : ℝ) * P.p ^ 2) ^ r := Finset.sum_le_sum fun q _ => hsingle q
      _ = (P.m.choose a₁ : ℝ) * (P.m.choose a₂ : ℝ) * (P.m.choose r : ℝ) *
            ((a₁ : ℝ) * (a₂ : ℝ) * P.p ^ 2) ^ r := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
            Fintype.card_coe, Fintype.card_coe, Fintype.card_coe,
            Finset.card_powersetCard, Finset.card_powersetCard, Finset.card_powersetCard,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_mul]; ring
      _ ≤ (P.m : ℝ) ^ (a₁ + a₂) *
            (Real.exp 1 * (P.m : ℝ) * (a₁ : ℝ) * (a₂ : ℝ) * P.p ^ 2 / (r : ℝ)) ^ r := by
          have h1 : (P.m.choose a₁ : ℝ) ≤ (P.m : ℝ) ^ a₁ := by exact_mod_cast choose_le_pow P.m a₁
          have h2 : (P.m.choose a₂ : ℝ) ≤ (P.m : ℝ) ^ a₂ := by exact_mod_cast choose_le_pow P.m a₂
          have h3 : (P.m.choose r : ℝ) ≤ (Real.exp 1 * (P.m : ℝ) / (r : ℝ)) ^ r := choose_le_exp_pow hr1
          have h12 : (P.m.choose a₁ : ℝ) * (P.m.choose a₂ : ℝ) ≤ (P.m : ℝ) ^ (a₁ + a₂) := by
            rw [pow_add]; exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
          calc (P.m.choose a₁ : ℝ) * (P.m.choose a₂ : ℝ) * (P.m.choose r : ℝ) *
                ((a₁ : ℝ) * (a₂ : ℝ) * P.p ^ 2) ^ r
              ≤ (P.m : ℝ) ^ (a₁ + a₂) * (Real.exp 1 * (P.m : ℝ) / (r : ℝ)) ^ r *
                ((a₁ : ℝ) * (a₂ : ℝ) * P.p ^ 2) ^ r := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul h12 h3 (Nat.cast_nonneg _) (by positivity)) (by positivity)
            _ = (P.m : ℝ) ^ (a₁ + a₂) *
                  (Real.exp 1 * (P.m : ℝ) * (a₁ : ℝ) * (a₂ : ℝ) * P.p ^ 2 / (r : ℝ)) ^ r := by
                rw [mul_assoc, ← mul_pow]; congr 1; ring
  · rw [if_neg hlt]
    simp only [bernProb]
    exact (Finset.sum_eq_zero fun _ _ => if_neg (fun h => hlt h.1)).le

end GraphRegularity

/- ### Section 2B: Deterministic Weighted 2-Path Bounds from `GoodGraph` -/

section WeightedTwoPaths

lemma sum_biUnion_le_of_nonneg {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s : Finset α} {t : α → Finset β} {f : β → ℝ} (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ s.biUnion t, f b ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hle : ∑ b ∈ t a ∪ s.biUnion t, f b ≤ (∑ b ∈ t a, f b) + ∑ b ∈ s.biUnion t, f b := by
      have h := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
      have hinter : 0 ≤ ∑ b ∈ t a ∩ s.biUnion t, f b := Finset.sum_nonneg fun b _ => hf b
      linarith
    linarith

/-- Pad any `S : Finset (Fin m)` of size `≤ a ≤ m` to a superset of exact size `a`. -/
lemma exists_superset_card_eq {m a : ℕ} {S : Finset (Fin m)} (hSa : S.card ≤ a) (ham : a ≤ m) :
    ∃ S' : Finset (Fin m), S ⊆ S' ∧ S'.card = a := by
  have hcomp : a - S.card ≤ (Finset.univ \ S).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcomp
  have hdisj : Disjoint S T := Finset.disjoint_right.mpr fun x hxT hxS =>
    (Finset.mem_sdiff.mp (hTsub hxT)).2 hxS
  refine ⟨S ∪ T, Finset.subset_union_left, ?_⟩
  rw [Finset.card_union_of_disjoint hdisj, hTcard]
  omega

/-- Pad disjoint `S₁, S₂ : Finset (Fin m)` to disjoint supersets of exact sizes `a₁, a₂`
when `a₁ + a₂ ≤ m`. -/
lemma exists_disjoint_supersets_card_eq {m a₁ a₂ : ℕ} {S₁ S₂ : Finset (Fin m)}
    (hdisj : Disjoint S₁ S₂) (h1 : S₁.card ≤ a₁) (h2 : S₂.card ≤ a₂) (hsum : a₁ + a₂ ≤ m) :
    ∃ S₁' S₂' : Finset (Fin m), S₁ ⊆ S₁' ∧ S₂ ⊆ S₂' ∧ S₁'.card = a₁ ∧ S₂'.card = a₂ ∧
      Disjoint S₁' S₂' := by
  have hcomp1 : a₁ - S₁.card ≤ (Finset.univ \ (S₁ ∪ S₂)).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_union_of_disjoint hdisj]
    omega
  obtain ⟨T₁, hT1sub, hT1card⟩ := Finset.exists_subset_card_eq hcomp1
  have hdisj_S1_T1 : Disjoint S₁ T₁ := Finset.disjoint_right.mpr fun x hxT hx1 =>
    (Finset.mem_sdiff.mp (hT1sub hxT)).2 (Finset.mem_union_left _ hx1)
  have hdisj_S2_T1 : Disjoint S₂ T₁ := Finset.disjoint_right.mpr fun x hxT hx2 =>
    (Finset.mem_sdiff.mp (hT1sub hxT)).2 (Finset.mem_union_right _ hx2)
  let S₁' := S₁ ∪ T₁
  have hS1'_card : S₁'.card = a₁ := by
    rw [Finset.card_union_of_disjoint hdisj_S1_T1, hT1card]; omega
  have hdisj_1'_2 : Disjoint S₁' S₂ := Finset.disjoint_union_left.mpr ⟨hdisj, hdisj_S2_T1.symm⟩
  have hcomp2 : a₂ - S₂.card ≤ (Finset.univ \ (S₁' ∪ S₂)).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_union_of_disjoint hdisj_1'_2, hS1'_card]
    omega
  obtain ⟨T₂, hT2sub, hT2card⟩ := Finset.exists_subset_card_eq hcomp2
  have hdisj_S2_T2 : Disjoint S₂ T₂ := Finset.disjoint_right.mpr fun x hxT hx2 =>
    (Finset.mem_sdiff.mp (hT2sub hxT)).2 (Finset.mem_union_right _ hx2)
  have hdisj_1'_T2 : Disjoint S₁' T₂ := Finset.disjoint_right.mpr fun x hxT hx1 =>
    (Finset.mem_sdiff.mp (hT2sub hxT)).2 (Finset.mem_union_left _ hx1)
  refine ⟨S₁', S₂ ∪ T₂, Finset.subset_union_left, Finset.subset_union_left, hS1'_card, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj_S2_T2, hT2card]; omega
  · exact Finset.disjoint_union_right.mpr ⟨hdisj_1'_2, hdisj_1'_T2⟩

lemma degIn_mono {m : ℕ} (G : SimpleGraph (Fin m)) {S S' : Finset (Fin m)} (h : S ⊆ S') (z : Fin m) :
    degIn G S z ≤ degIn G S' z :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- Dyadic weight class `i` of `(A, c)`: `{r ∈ A | 2^i ≤ c r < 2^(i+1)}`. -/
def wtClass {m : ℕ} (A : Finset (Fin m)) (c : Fin m → ℕ) (i : ℕ) : Finset (Fin m) :=
  A.filter fun r => 2 ^ i ≤ c r ∧ c r < 2 ^ (i + 1)

lemma wtClass_disjoint {m : ℕ} (A : Finset (Fin m)) (c : Fin m → ℕ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (wtClass A c i) (wtClass A c j) := by
  refine Finset.disjoint_left.mpr fun r hri hrj => ?_
  have hi := (Finset.mem_filter.mp hri).2
  have hj := (Finset.mem_filter.mp hrj).2
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have : 2 ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hlt
    omega
  · have : 2 ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hgt
    omega

lemma wtClass_card_le {P : RegParams} {A : Finset (Fin P.m)} {c : Fin P.m → ℕ}
    (hsum : ∑ r ∈ A, c r ≤ P.k) (i : ℕ) :
    (wtClass A c i).card ≤ P.clsSize i := by
  refine le_min ((Finset.card_le_univ _).trans (by simp)) ?_
  rw [Nat.le_div_iff_mul_le (Nat.pow_pos (by omega : 0 < 2))]
  calc (wtClass A c i).card * 2 ^ i
      = ∑ _r ∈ wtClass A c i, 2 ^ i := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ r ∈ wtClass A c i, c r :=
        Finset.sum_le_sum fun r hr => (Finset.mem_filter.mp hr).2.1
    _ ≤ ∑ r ∈ A, c r := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ ≤ P.k := hsum

lemma mem_wtClass_of_pos {m L : ℕ} {A : Finset (Fin m)} {c : Fin m → ℕ}
    {r : Fin m} (hrA : r ∈ A) (hpos : 1 ≤ c r) (hlt : c r < 2 ^ L) :
    ∃ i : Fin L, r ∈ wtClass A c i.val := by
  let i := Nat.log 2 (c r)
  have hi_lt : i < L := (Nat.log_lt_iff_lt_pow (by omega : 1 < 2) (by omega)).mpr hlt
  refine ⟨⟨i, hi_lt⟩, Finset.mem_filter.mpr ⟨hrA, ?_, ?_⟩⟩
  · exact Nat.pow_log_le_self 2 (by omega)
  · exact Nat.lt_pow_succ_log_self (by omega : 1 < 2) (c r)

/-- Heavy vertices `Zbig` for `(A, c)` in `G = graphOf ω`: vertices `z` where some class `i` has
`2^i * deg(z, wtClass A c i) > T_big`. -/
noncomputable def Zbig (P : RegParams) (ω : EdgeIdx P.m → Bool)
    (A : Finset (Fin P.m)) (c : Fin P.m → ℕ) : Finset (Fin P.m) :=
  Finset.univ.filter fun z =>
    ∃ i : Fin P.L, P.T_big < ((2 ^ i.val : ℕ) : ℝ) * (degIn (graphOf ω) (wtClass A c i.val) z : ℝ)

/-- Bound on `|Zbig P ω A c|` under `GoodDegLarge`. -/
lemma card_Zbig_le (P : RegParams) (ω : EdgeIdx P.m → Bool)
    (hLarge : GoodDegLarge P ω)
    {A : Finset (Fin P.m)} {c : Fin P.m → ℕ} (hsum : ∑ r ∈ A, c r ≤ P.k)
    (hTbig_pos : 0 < P.T_big) (hTmid_lt : P.T_mid < P.T_big / 2)
    (hTbig_lt_J : P.T_big < ((2 ^ P.J : ℕ) : ℝ))
    (hL_le_Tbig : ∀ i : Fin P.L, ((2 ^ i.val : ℕ) : ℝ) ≤ P.T_big) :
    ((Zbig P ω A c).card : ℝ) ≤ (P.L : ℝ) * (240 * (P.k : ℝ) / P.T_big + 4) := by
  let cls (i : Fin P.L) := Finset.univ.filter fun z : Fin P.m =>
    P.T_big < ((2 ^ i.val : ℕ) : ℝ) * (degIn (graphOf ω) (wtClass A c i.val) z : ℝ)
  have hcov : Zbig P ω A c ⊆ Finset.univ.biUnion cls := by
    intro z hz
    rcases (Finset.mem_filter.mp hz).2 with ⟨i, hi⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have hbi : ((Zbig P ω A c).card : ℝ) ≤ ∑ i : Fin P.L, ((cls i).card : ℝ) := by
    have hnat : (Zbig P ω A c).card ≤ ∑ i : Fin P.L, (cls i).card :=
      (Finset.card_le_card hcov).trans Finset.card_biUnion_le
    exact_mod_cast hnat
  refine hbi.trans ?_
  have hsingle : ∀ i : Fin P.L, ((cls i).card : ℝ) ≤ 240 * (P.k : ℝ) / P.T_big + 4 := by
    intro i
    set w : ℝ := ((2 ^ i.val : ℕ) : ℝ)
    have hw_pos : 0 < w := by positivity
    have hq_ge1 : 1 ≤ P.T_big / w := (one_le_div hw_pos).mpr (hL_le_Tbig i)
    set q : ℕ := ⌊P.T_big / w⌋₊
    have hq_pos : 1 ≤ q := Nat.floor_pos.mpr hq_ge1
    set j₀ : ℕ := Nat.log 2 q
    have hj0_le : 2 ^ j₀ ≤ q := Nat.pow_log_le_self 2 (by omega)
    have hq_lt : q < 2 ^ (j₀ + 1) := Nat.lt_pow_succ_log_self (by omega : 1 < 2) q
    have h2j_le_div : ((2 ^ j₀ : ℕ) : ℝ) ≤ P.T_big / w :=
      le_trans (by exact_mod_cast hj0_le) (Nat.floor_le (by positivity))
    have hdiv_lt : P.T_big / w < ((2 ^ (j₀ + 1) : ℕ) : ℝ) :=
      lt_of_lt_of_le (Nat.lt_floor_add_one _) (by exact_mod_cast (by omega : q + 1 ≤ 2 ^ (j₀ + 1)))
    have hprod_le : w * ((2 ^ j₀ : ℕ) : ℝ) ≤ P.T_big := (le_div_iff₀' hw_pos).mp h2j_le_div
    have hprod_gt : P.T_big / 2 < w * ((2 ^ j₀ : ℕ) : ℝ) := by
      have hpow : ((2 ^ (j₀ + 1) : ℕ) : ℝ) = 2 * ((2 ^ j₀ : ℕ) : ℝ) := by push_cast; ring
      rw [hpow, div_lt_iff₀ hw_pos] at hdiv_lt
      linarith
    have hj0_lt_J : j₀ < P.J := by
      have h1 : ((2 ^ j₀ : ℕ) : ℝ) < ((2 ^ P.J : ℕ) : ℝ) := by
        have hw1 : (1 : ℝ) ≤ w := by dsimp only [w]; exact_mod_cast Nat.one_le_pow i.val 2 (by omega)
        calc ((2 ^ j₀ : ℕ) : ℝ) ≤ w * ((2 ^ j₀ : ℕ) : ℝ) := le_mul_of_one_le_left (by positivity) hw1
          _ ≤ P.T_big := hprod_le
          _ < ((2 ^ P.J : ℕ) : ℝ) := hTbig_lt_J
      have hnat : 2 ^ j₀ < 2 ^ P.J := by exact_mod_cast h1
      exact (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hnat
    have hcls_le : (wtClass A c i.val).card ≤ P.clsSize i.val := wtClass_card_le hsum i.val
    obtain ⟨S', hSsub, hS'card⟩ := exists_superset_card_eq hcls_le (min_le_left _ _)
    have hS'mem : S' ∈ (Finset.univ : Finset (Fin P.m)).powersetCard (P.clsSize i.val) :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS'card⟩
    have hgl := hLarge i ⟨j₀, hj0_lt_J⟩ (hTmid_lt.trans hprod_gt) S' hS'mem
    simp only at hgl
    have hsub_union : cls i ⊆
        ((Finset.univ \ S').filter fun z => 2 ^ j₀ ≤ degIn (graphOf ω) S' z) ∪
        (S'.filter fun z => 2 ^ j₀ ≤ degIn (graphOf ω) S' z) := by
      intro z hz
      have hlt := (Finset.mem_filter.mp hz).2
      have hd_ge : 2 ^ j₀ ≤ degIn (graphOf ω) (wtClass A c i.val) z := by
        by_contra hnot
        have hlt_d : (degIn (graphOf ω) (wtClass A c i.val) z : ℝ) < ((2 ^ j₀ : ℕ) : ℝ) := by
          exact_mod_cast (by omega : degIn (graphOf ω) (wtClass A c i.val) z < 2 ^ j₀)
        have hmul := mul_lt_mul_of_pos_left hlt_d hw_pos
        linarith
      have hd' : 2 ^ j₀ ≤ degIn (graphOf ω) S' z := hd_ge.trans (degIn_mono (graphOf ω) hSsub z)
      by_cases hzS : z ∈ S'
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hzS, hd'⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzS⟩, hd'⟩)
    have hcard_lt : (cls i).card ≤ P.rLargeOut i.val j₀ + P.rLargeIn i.val j₀ := by
      calc (cls i).card
          ≤ (((Finset.univ \ S').filter fun z => 2 ^ j₀ ≤ degIn (graphOf ω) S' z) ∪
              (S'.filter fun z => 2 ^ j₀ ≤ degIn (graphOf ω) S' z)).card := Finset.card_le_card hsub_union
        _ ≤ _ + _ := Finset.card_union_le _ _
        _ ≤ P.rLargeOut i.val j₀ + P.rLargeIn i.val j₀ := by omega
    have hcard_real : ((cls i).card : ℝ) ≤ (P.rLargeOut i.val j₀ : ℝ) + (P.rLargeIn i.val j₀ : ℝ) := by
      exact_mod_cast hcard_lt
    have ha_le : (P.clsSize i.val : ℝ) ≤ (P.k : ℝ) / w := by
      have hnat : P.clsSize i.val * 2 ^ i.val ≤ P.k :=
        (Nat.mul_le_mul_right _ (min_le_right _ _)).trans (Nat.div_mul_le_self _ _)
      have hreal : (P.clsSize i.val : ℝ) * w ≤ (P.k : ℝ) := by dsimp only [w]; exact_mod_cast hnat
      exact (le_div_iff₀ hw_pos).mpr hreal
    have hro : (P.rLargeOut i.val j₀ : ℝ) ≤ 40 * (P.clsSize i.val : ℝ) / ((2 ^ j₀ : ℕ) : ℝ) + 2 := by
      dsimp only [RegParams.rLargeOut]
      rw [Nat.cast_add, Nat.cast_one]
      have hcl := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 40 * (P.clsSize i.val : ℝ) / ((2 ^ j₀ : ℕ) : ℝ) by positivity)
      linarith
    have hri : (P.rLargeIn i.val j₀ : ℝ) ≤ 80 * (P.clsSize i.val : ℝ) / ((2 ^ j₀ : ℕ) : ℝ) + 2 := by
      dsimp only [RegParams.rLargeIn]
      rw [Nat.cast_add, Nat.cast_one]
      have hcl := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 80 * (P.clsSize i.val : ℝ) / ((2 ^ j₀ : ℕ) : ℝ) by positivity)
      linarith
    have hfrac : (P.clsSize i.val : ℝ) / ((2 ^ j₀ : ℕ) : ℝ) ≤ 2 * (P.k : ℝ) / P.T_big := by
      have h2j_pos : (0 : ℝ) < ((2 ^ j₀ : ℕ) : ℝ) := by positivity
      calc (P.clsSize i.val : ℝ) / ((2 ^ j₀ : ℕ) : ℝ)
          ≤ ((P.k : ℝ) / w) / ((2 ^ j₀ : ℕ) : ℝ) := div_le_div_of_nonneg_right ha_le h2j_pos.le
        _ = (P.k : ℝ) / (w * ((2 ^ j₀ : ℕ) : ℝ)) := by rw [div_div]
        _ ≤ (P.k : ℝ) / (P.T_big / 2) :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hprod_gt.le
        _ = 2 * (P.k : ℝ) / P.T_big := by ring
    have h120 : 40 * (P.clsSize i.val : ℝ) / ((2 ^ j₀ : ℕ) : ℝ) +
        80 * (P.clsSize i.val : ℝ) / ((2 ^ j₀ : ℕ) : ℝ) =
        120 * ((P.clsSize i.val : ℝ) / ((2 ^ j₀ : ℕ) : ℝ)) := by ring
    have h240 : 120 * (2 * (P.k : ℝ) / P.T_big) = 240 * (P.k : ℝ) / P.T_big := by ring
    linarith only [hcard_real, hro, hri, hfrac, h120, h240]
  calc ∑ i : Fin P.L, ((cls i).card : ℝ)
      ≤ ∑ _i : Fin P.L, (240 * (P.k : ℝ) / P.T_big + 4) := Finset.sum_le_sum fun i _ => hsingle i
    _ = (P.L : ℝ) * (240 * (P.k : ℝ) / P.T_big + 4) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Total weighted degree of a single class `i`: `∑ z, (2^i * deg(z, S_i)) ≤ k * ((1 + η₀) * m * p)`. -/
lemma sum_wtClass_deg_le (P : RegParams) (ω : EdgeIdx P.m → Bool)
    (hDeg : GoodMaxDeg P ω) {A : Finset (Fin P.m)} {c : Fin P.m → ℕ}
    (hsum : ∑ r ∈ A, c r ≤ P.k) (i : ℕ) :
    ∑ z : Fin P.m, ((2 ^ i : ℕ) : ℝ) * (degIn (graphOf ω) (wtClass A c i) z : ℝ) ≤
      (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) := by
  have hswap : ∑ z : Fin P.m, degIn (graphOf ω) (wtClass A c i) z =
      ∑ r ∈ wtClass A c i, degIn (graphOf ω) Finset.univ r := by
    simp only [degIn]
    have h1 : ∀ z : Fin P.m, ((wtClass A c i).filter fun r => (graphOf ω).Adj z r).card =
        ∑ r ∈ wtClass A c i, if (graphOf ω).Adj z r then 1 else 0 := fun z => by simp
    have h2 : ∀ r : Fin P.m, (Finset.univ.filter fun z => (graphOf ω).Adj r z).card =
        ∑ z : Fin P.m, if (graphOf ω).Adj z r then 1 else 0 := fun r => by
      simp only [Finset.card_filter]; refine Finset.sum_congr rfl fun z _ => ?_
      by_cases hadj : (graphOf ω).Adj r z
      · simp [hadj, hadj.symm]
      · have hnot : ¬ (graphOf ω).Adj z r := fun h => hadj h.symm
        simp [hadj, hnot]
    simp_rw [h1, h2]
    exact Finset.sum_comm
  have hsum_deg : (∑ z : Fin P.m, (degIn (graphOf ω) (wtClass A c i) z : ℝ)) ≤
      ((wtClass A c i).card : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) := by
    rw [← Nat.cast_sum, hswap, Nat.cast_sum]
    calc ∑ r ∈ wtClass A c i, (degIn (graphOf ω) Finset.univ r : ℝ)
        ≤ ∑ _r ∈ wtClass A c i, ((1 + P.η₀) * ((P.m : ℝ) * P.p)) :=
          Finset.sum_le_sum fun r _ => hDeg r
      _ = ((wtClass A c i).card : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hwa : ((2 ^ i : ℕ) : ℝ) * ((wtClass A c i).card : ℝ) ≤ (P.k : ℝ) := by
    have hnat : 2 ^ i * (wtClass A c i).card ≤ P.k := by
      calc 2 ^ i * (wtClass A c i).card
          = ∑ _r ∈ wtClass A c i, 2 ^ i := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ r ∈ wtClass A c i, c r := Finset.sum_le_sum fun r hr => (Finset.mem_filter.mp hr).2.1
        _ ≤ ∑ r ∈ A, c r := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ ≤ P.k := hsum
    exact_mod_cast hnat
  have hdeg_nonneg : 0 ≤ (1 + P.η₀) * ((P.m : ℝ) * P.p) := by
    by_cases hm : 0 < P.m
    · exact le_trans (Nat.cast_nonneg _) (hDeg ⟨0, hm⟩)
    · have hm0 : P.m = 0 := by omega
      simp [hm0]
  rw [← Finset.mul_sum]
  calc ((2 ^ i : ℕ) : ℝ) * ∑ z : Fin P.m, (degIn (graphOf ω) (wtClass A c i) z : ℝ)
      ≤ ((2 ^ i : ℕ) : ℝ) * (((wtClass A c i).card : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p))) :=
        mul_le_mul_of_nonneg_left hsum_deg (by positivity)
    _ = (((2 ^ i : ℕ) : ℝ) * ((wtClass A c i).card : ℝ)) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) := by ring
    _ ≤ (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) :=
        mul_le_mul_of_nonneg_right hwa hdeg_nonneg

/-- Single-class diagonal squared-degree bound for `z ∉ Zbig` with `2 ≤ deg(z, S_i)`. -/
lemma sum_diag_class_outside_Zbig_le (P : RegParams) (ω : EdgeIdx P.m → Bool)
    (hG : GoodGraph P ω) {A : Finset (Fin P.m)} {c : Fin P.m → ℕ}
    (hsum : ∑ r ∈ A, c r ≤ P.k)
    (hTlo : 0 < P.T_lo) (hTmid : 0 < P.T_mid) (hTbig : 0 < P.T_big)
    (hBmid : 0 < P.B_mid) (hm_lt_J : P.m < 2 ^ P.J) (i : Fin P.L) :
    ∑ z ∈ Finset.univ.filter (fun z => z ∉ Zbig P ω A c ∧ 2 ≤ degIn (graphOf ω) (wtClass A c i.val) z),
        (((2 ^ i.val : ℕ) : ℝ) * (degIn (graphOf ω) (wtClass A c i.val) z : ℝ)) ^ 2 ≤
      2 * P.T_lo * (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) +
      4 * (P.k : ℝ) * P.T_mid ^ 2 +
      (P.J : ℝ) * (4 * (P.k : ℝ) ^ 2 / P.B_mid + 4 * P.T_mid ^ 2 +
        480 * (P.k : ℝ) * P.T_big + 16 * P.T_big ^ 2) := by
  set S := wtClass A c i.val
  set w : ℝ := ((2 ^ i.val : ℕ) : ℝ)
  set d : Fin P.m → ℕ := fun z => degIn (graphOf ω) S z
  have hw_pos : 0 < w := by positivity
  have hS_le : S.card ≤ P.clsSize i.val := wtClass_card_le hsum i.val
  obtain ⟨S', hSsub, hS'card⟩ := exists_superset_card_eq hS_le (min_le_left _ _)
  have hS'mem : S' ∈ (Finset.univ : Finset (Fin P.m)).powersetCard (P.clsSize i.val) :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS'card⟩
  set U := Finset.univ.filter (fun z => z ∉ Zbig P ω A c ∧ 2 ≤ d z)
  set U_lo := U.filter (fun z => w * (d z : ℝ) ≤ 2 * P.T_lo)
  set U_hi := U.filter (fun z => ¬ w * (d z : ℝ) ≤ 2 * P.T_lo)
  have hsplit : ∑ z ∈ U, (w * (d z : ℝ)) ^ 2 =
      (∑ z ∈ U_lo, (w * (d z : ℝ)) ^ 2) + ∑ z ∈ U_hi, (w * (d z : ℝ)) ^ 2 :=
    (Finset.sum_filter_add_sum_filter_not U _ _).symm
  -- 1. Low bucket: w * d z ≤ 2 * T_lo
  have hlow : ∑ z ∈ U_lo, (w * (d z : ℝ)) ^ 2 ≤
      2 * P.T_lo * (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) := by
    calc ∑ z ∈ U_lo, (w * (d z : ℝ)) ^ 2
        ≤ ∑ z ∈ U_lo, (2 * P.T_lo) * (w * (d z : ℝ)) := by
          refine Finset.sum_le_sum fun z hz => ?_
          have hle := (Finset.mem_filter.mp hz).2
          have hnn : 0 ≤ w * (d z : ℝ) := by positivity
          nlinarith
      _ = 2 * P.T_lo * ∑ z ∈ U_lo, (w * (d z : ℝ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * P.T_lo * ∑ z : Fin P.m, (w * (d z : ℝ)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_univ_sum_of_nonneg fun z => by positivity) (by positivity)
      _ ≤ 2 * P.T_lo * ((P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p))) :=
          mul_le_mul_of_nonneg_left (sum_wtClass_deg_le P ω hG.1 hsum i.val) (by positivity)
      _ = 2 * P.T_lo * (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) := by ring
  -- 2. High bucket: 2 * T_lo < w * d z ≤ T_big, partitioned by j = Nat.log 2 (d z)
  set U_in_mid := U_hi.filter (fun z => z ∈ S' ∧ w * ((2 ^ (Nat.log 2 (d z)) : ℕ) : ℝ) ≤ P.T_mid)
  set U_rest := U_hi.filter (fun z => ¬ (z ∈ S' ∧ w * ((2 ^ (Nat.log 2 (d z)) : ℕ) : ℝ) ≤ P.T_mid))
  have hsplit2 : ∑ z ∈ U_hi, (w * (d z : ℝ)) ^ 2 =
      (∑ z ∈ U_in_mid, (w * (d z : ℝ)) ^ 2) + ∑ z ∈ U_rest, (w * (d z : ℝ)) ^ 2 :=
    (Finset.sum_filter_add_sum_filter_not U_hi _ _).symm
  have hin_mid : ∑ z ∈ U_in_mid, (w * (d z : ℝ)) ^ 2 ≤ 4 * (P.k : ℝ) * P.T_mid ^ 2 := by
    have hcard_le : (U_in_mid.card : ℝ) ≤ (P.k : ℝ) := by
      have hsub : U_in_mid ⊆ S' := fun z hz => (Finset.mem_filter.mp hz).2.1
      have h1 : U_in_mid.card ≤ P.clsSize i.val := by rw [← hS'card]; exact Finset.card_le_card hsub
      have h2 : P.clsSize i.val ≤ P.k := (min_le_right _ _).trans (Nat.div_le_self _ _)
      exact_mod_cast h1.trans h2
    calc ∑ z ∈ U_in_mid, (w * (d z : ℝ)) ^ 2
        ≤ ∑ _z ∈ U_in_mid, (2 * P.T_mid) ^ 2 := by
          refine Finset.sum_le_sum fun z hz => ?_
          have hmid := (Finset.mem_filter.mp hz).2.2
          have hd_lt : (d z : ℝ) < 2 * ((2 ^ (Nat.log 2 (d z)) : ℕ) : ℝ) := by
            have hnat := Nat.lt_pow_succ_log_self (by omega : 1 < 2) (d z)
            have hreal : (d z : ℝ) < ((2 ^ (Nat.log 2 (d z) + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
            have hpow : ((2 ^ (Nat.log 2 (d z) + 1) : ℕ) : ℝ) = 2 * ((2 ^ (Nat.log 2 (d z)) : ℕ) : ℝ) := by
              push_cast; ring
            linarith
          have hwd_le : w * (d z : ℝ) ≤ 2 * P.T_mid := by nlinarith
          nlinarith [show (0 : ℝ) ≤ w * (d z : ℝ) by positivity]
      _ = (U_in_mid.card : ℝ) * (4 * P.T_mid ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ (P.k : ℝ) * (4 * P.T_mid ^ 2) := mul_le_mul_of_nonneg_right hcard_le (by positivity)
      _ = 4 * (P.k : ℝ) * P.T_mid ^ 2 := by ring
  -- 3. Dyadic buckets for U_rest
  let B (j : Fin P.J) := U_rest.filter fun z => Nat.log 2 (d z) = j.val
  have hUrest_cov : U_rest ⊆ Finset.univ.biUnion B := by
    intro z hz
    have hd_le_m : d z ≤ P.m := (Finset.card_le_univ _).trans (by simp)
    have hlog_lt : Nat.log 2 (d z) < P.J := by
      by_cases hd0 : d z = 0
      · have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).2.2
        omega
      · exact (Nat.log_lt_iff_lt_pow (by omega : 1 < 2) hd0).mpr (lt_of_le_of_lt hd_le_m hm_lt_J)
    exact Finset.mem_biUnion.mpr ⟨⟨Nat.log 2 (d z), hlog_lt⟩, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨hz, rfl⟩⟩
  have hsum_B : ∑ z ∈ U_rest, (w * (d z : ℝ)) ^ 2 ≤ ∑ j : Fin P.J, ∑ z ∈ B j, (w * (d z : ℝ)) ^ 2 := by
    calc ∑ z ∈ U_rest, (w * (d z : ℝ)) ^ 2
        ≤ ∑ z ∈ Finset.univ.biUnion B, (w * (d z : ℝ)) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hUrest_cov fun _ _ _ => sq_nonneg _
      _ ≤ ∑ j : Fin P.J, ∑ z ∈ B j, (w * (d z : ℝ)) ^ 2 :=
          sum_biUnion_le_of_nonneg fun _ => sq_nonneg _
  have hBj_bound : ∀ j : Fin P.J, ∑ z ∈ B j, (w * (d z : ℝ)) ^ 2 ≤
      4 * (P.k : ℝ) ^ 2 / P.B_mid + 4 * P.T_mid ^ 2 +
        480 * (P.k : ℝ) * P.T_big + 16 * P.T_big ^ 2 := by
    intro j
    by_cases hne : (B j).Nonempty
    · obtain ⟨z₀, hz₀⟩ := hne
      have hlog0 : Nat.log 2 (d z₀) = j.val := (Finset.mem_filter.mp hz₀).2
      have hz₀_hi := (Finset.mem_filter.mp (Finset.mem_filter.mp hz₀).1).1
      have hz₀_U := (Finset.mem_filter.mp hz₀_hi).1
      have hgt0 : 2 * P.T_lo < w * (d z₀ : ℝ) := not_le.mp (Finset.mem_filter.mp hz₀_hi).2
      have hnotZ0 : z₀ ∉ Zbig P ω A c := (Finset.mem_filter.mp hz₀_U).2.1
      have hd0_ge2 : 2 ≤ d z₀ := (Finset.mem_filter.mp hz₀_U).2.2
      have hj1 : 1 ≤ j.val := by
        rw [← hlog0]; exact Nat.le_log_of_pow_le (by omega : 1 < 2) (by simpa using hd0_ge2)
      have hwt_le_big : w * ((2 ^ j.val : ℕ) : ℝ) ≤ P.T_big := by
        have hnotgt : ¬ P.T_big < w * (d z₀ : ℝ) := fun h => hnotZ0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i, h⟩⟩)
        have h2j_le_d : ((2 ^ j.val : ℕ) : ℝ) ≤ (d z₀ : ℝ) := by
          rw [← hlog0]; exact_mod_cast Nat.pow_log_le_self 2 (by omega)
        nlinarith
      have hwt_gt_lo : P.T_lo < w * ((2 ^ j.val : ℕ) : ℝ) := by
        have hd_lt : (d z₀ : ℝ) < 2 * ((2 ^ j.val : ℕ) : ℝ) := by
          rw [← hlog0]
          have hnat := Nat.lt_pow_succ_log_self (by omega : 1 < 2) (d z₀)
          have hreal : (d z₀ : ℝ) < ((2 ^ (Nat.log 2 (d z₀) + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
          have hpow : ((2 ^ (Nat.log 2 (d z₀) + 1) : ℕ) : ℝ) = 2 * ((2 ^ (Nat.log 2 (d z₀)) : ℕ) : ℝ) := by
            push_cast; ring
          linarith
        nlinarith
      have hterm_le : ∀ z ∈ B j, (w * (d z : ℝ)) ^ 2 ≤ 4 * (w * ((2 ^ j.val : ℕ) : ℝ)) ^ 2 := by
        intro z hz
        have hlogz : Nat.log 2 (d z) = j.val := (Finset.mem_filter.mp hz).2
        have hd_lt : (d z : ℝ) < 2 * ((2 ^ j.val : ℕ) : ℝ) := by
          rw [← hlogz]
          have hnat := Nat.lt_pow_succ_log_self (by omega : 1 < 2) (d z)
          have hreal : (d z : ℝ) < ((2 ^ (Nat.log 2 (d z) + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
          have hpow : ((2 ^ (Nat.log 2 (d z) + 1) : ℕ) : ℝ) = 2 * ((2 ^ (Nat.log 2 (d z)) : ℕ) : ℝ) := by
            push_cast; ring
          linarith
        have hwd_le : w * (d z : ℝ) ≤ 2 * (w * ((2 ^ j.val : ℕ) : ℝ)) := by nlinarith
        nlinarith [show (0 : ℝ) ≤ w * (d z : ℝ) by positivity]
      have hsum_card : ∑ z ∈ B j, (w * (d z : ℝ)) ^ 2 ≤
          ((B j).card : ℝ) * (4 * (w * ((2 ^ j.val : ℕ) : ℝ)) ^ 2) := by
        calc ∑ z ∈ B j, (w * (d z : ℝ)) ^ 2
            ≤ ∑ _z ∈ B j, (4 * (w * ((2 ^ j.val : ℕ) : ℝ)) ^ 2) := Finset.sum_le_sum hterm_le
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
      by_cases hmid : w * ((2 ^ j.val : ℕ) : ℝ) ≤ P.T_mid
      · -- Range B: every z ∈ B j has z ∉ S'
        have hBsub : B j ⊆ (Finset.univ \ S').filter fun z => 2 ^ j.val ≤ degIn (graphOf ω) S' z := by
          intro z hz
          have hlogz : Nat.log 2 (d z) = j.val := (Finset.mem_filter.mp hz).2
          have hz_rest := (Finset.mem_filter.mp hz).1
          have hnot_in := (Finset.mem_filter.mp hz_rest).2
          have hz_notS' : z ∉ S' := fun hzS' => hnot_in ⟨hzS', by rwa [hlogz]⟩
          have hd_ge2 : 2 ≤ d z := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz_rest).1).1).2.2
          have h2j_le : 2 ^ j.val ≤ d z := by rw [← hlogz]; exact Nat.pow_log_le_self 2 (by omega)
          exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hz_notS'⟩,
            h2j_le.trans (degIn_mono (graphOf ω) hSsub z)⟩
        have hcard_lt : (B j).card < P.rMid i.val j.val :=
          lt_of_le_of_lt (Finset.card_le_card hBsub) (hG.2.2.1 i j hj1 hwt_gt_lo.le hmid S' hS'mem)
        have hcard_real : ((B j).card : ℝ) ≤
            (P.k : ℝ) ^ 2 / ((w * ((2 ^ j.val : ℕ) : ℝ)) ^ 2 * P.B_mid) + 1 := by
          have hle_r : ((B j).card : ℝ) ≤ (P.rMid i.val j.val : ℝ) := by exact_mod_cast hcard_lt.le
          have hceil := Nat.ceil_lt_add_one (show (0 : ℝ) ≤
            (P.k : ℝ) ^ 2 / (w ^ 2 * ((2 ^ j.val : ℕ) : ℝ) ^ 2 * P.B_mid) by positivity)
          have heq : w ^ 2 * ((2 ^ j.val : ℕ) : ℝ) ^ 2 * P.B_mid =
              (w * ((2 ^ j.val : ℕ) : ℝ)) ^ 2 * P.B_mid := by ring
          dsimp only [RegParams.rMid] at hle_r
          change ((B j).card : ℝ) ≤ (⌈(P.k : ℝ) ^ 2 / (w ^ 2 * ((2 ^ j.val : ℕ) : ℝ) ^ 2 * P.B_mid)⌉₊ : ℝ) at hle_r
          rw [heq] at hceil hle_r
          linarith only [hle_r, hceil]
        have hwt_pos : 0 < (w * ((2 ^ j.val : ℕ) : ℝ)) ^ 2 := by positivity
        have h1 : ((B j).card : ℝ) * (4 * (w * ((2 ^ j.val : ℕ) : ℝ)) ^ 2) ≤
            4 * (P.k : ℝ) ^ 2 / P.B_mid + 4 * P.T_mid ^ 2 := by
          have hmul := mul_le_mul_of_nonneg_right hcard_real (show 0 ≤ 4 * (w * ((2 ^ j.val : ℕ) : ℝ)) ^ 2 by positivity)
          have hsimp : ((P.k : ℝ) ^ 2 / ((w * ((2 ^ j.val : ℕ) : ℝ)) ^ 2 * P.B_mid) + 1) *
              (4 * (w * ((2 ^ j.val : ℕ) : ℝ)) ^ 2) =
              4 * (P.k : ℝ) ^ 2 / P.B_mid + 4 * (w * ((2 ^ j.val : ℕ) : ℝ)) ^ 2 := by
            field_simp [hwt_pos.ne', hBmid.ne']
          have hsq : (w * ((2 ^ j.val : ℕ) : ℝ)) ^ 2 ≤ P.T_mid ^ 2 := by
            nlinarith only [hmid, show 0 ≤ w * ((2 ^ j.val : ℕ) : ℝ) by positivity]
          linarith only [hmul, hsimp, hsq]
        have hpos_tail : 0 ≤ 480 * (P.k : ℝ) * P.T_big + 16 * P.T_big ^ 2 := by positivity
        linarith only [hsum_card, h1, hpos_tail]
      · -- Range A: T_mid < w * 2^j ≤ T_big
        have hgt_mid : P.T_mid < w * ((2 ^ j.val : ℕ) : ℝ) := not_le.mp hmid
        have hgl := hG.2.2.2.1 i j hgt_mid S' hS'mem
        have hBsub : B j ⊆
            ((Finset.univ \ S').filter fun z => 2 ^ j.val ≤ degIn (graphOf ω) S' z) ∪
            (S'.filter fun z => 2 ^ j.val ≤ degIn (graphOf ω) S' z) := by
          intro z hz
          have hlogz : Nat.log 2 (d z) = j.val := (Finset.mem_filter.mp hz).2
          have hd_ge2 : 2 ≤ d z :=
            (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).1).2.2
          have h2j_le : 2 ^ j.val ≤ d z := by rw [← hlogz]; exact Nat.pow_log_le_self 2 (by omega)
          have hd' := h2j_le.trans (degIn_mono (graphOf ω) hSsub z)
          by_cases hzS : z ∈ S'
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hzS, hd'⟩)
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzS⟩, hd'⟩)
        have hcard_le : (B j).card ≤ P.rLargeOut i.val j.val + P.rLargeIn i.val j.val := by
          calc (B j).card
              ≤ (((Finset.univ \ S').filter fun z => 2 ^ j.val ≤ degIn (graphOf ω) S' z) ∪
                  (S'.filter fun z => 2 ^ j.val ≤ degIn (graphOf ω) S' z)).card := Finset.card_le_card hBsub
            _ ≤ _ + _ := Finset.card_union_le _ _
            _ ≤ _ := by omega
        have hcard_real : ((B j).card : ℝ) ≤ 120 * (P.clsSize i.val : ℝ) / ((2 ^ j.val : ℕ) : ℝ) + 4 := by
          have hle : ((B j).card : ℝ) ≤ (P.rLargeOut i.val j.val : ℝ) + (P.rLargeIn i.val j.val : ℝ) := by
            exact_mod_cast hcard_le
          dsimp only [RegParams.rLargeOut, RegParams.rLargeIn] at hle
          simp only [Nat.cast_add, Nat.cast_one] at hle
          have h1 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 40 * (P.clsSize i.val : ℝ) / ((2 ^ j.val : ℕ) : ℝ) by positivity)
          have h2 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 80 * (P.clsSize i.val : ℝ) / ((2 ^ j.val : ℕ) : ℝ) by positivity)
          have h120 : 40 * (P.clsSize i.val : ℝ) / ((2 ^ j.val : ℕ) : ℝ) +
              80 * (P.clsSize i.val : ℝ) / ((2 ^ j.val : ℕ) : ℝ) =
              120 * (P.clsSize i.val : ℝ) / ((2 ^ j.val : ℕ) : ℝ) := by ring
          linarith only [hle, h1, h2, h120]
        have hwa_le : w * (P.clsSize i.val : ℝ) ≤ (P.k : ℝ) := by
          have hnat : 2 ^ i.val * P.clsSize i.val ≤ P.k := by
            rw [mul_comm]; exact (Nat.mul_le_mul_right _ (min_le_right _ _)).trans (Nat.div_mul_le_self _ _)
          dsimp only [w]; exact_mod_cast hnat
        have h2j_pos : (0 : ℝ) < ((2 ^ j.val : ℕ) : ℝ) := by positivity
        have h1 : ((B j).card : ℝ) * (4 * (w * ((2 ^ j.val : ℕ) : ℝ)) ^ 2) ≤
            480 * (P.k : ℝ) * P.T_big + 16 * P.T_big ^ 2 := by
          have hmul := mul_le_mul_of_nonneg_right hcard_real (show 0 ≤ 4 * (w * ((2 ^ j.val : ℕ) : ℝ)) ^ 2 by positivity)
          have hsimp : (120 * (P.clsSize i.val : ℝ) / ((2 ^ j.val : ℕ) : ℝ) + 4) *
              (4 * (w * ((2 ^ j.val : ℕ) : ℝ)) ^ 2) =
              480 * (w * (P.clsSize i.val : ℝ)) * (w * ((2 ^ j.val : ℕ) : ℝ)) +
              16 * (w * ((2 ^ j.val : ℕ) : ℝ)) ^ 2 := by
            field_simp [h2j_pos.ne']; ring
          have hterm1 : (w * (P.clsSize i.val : ℝ)) * (w * ((2 ^ j.val : ℕ) : ℝ)) ≤ (P.k : ℝ) * P.T_big :=
            mul_le_mul hwa_le hwt_le_big (by positivity) (by positivity)
          have hterm2 : (w * ((2 ^ j.val : ℕ) : ℝ)) ^ 2 ≤ P.T_big ^ 2 := by
            nlinarith only [hwt_le_big, show 0 ≤ w * ((2 ^ j.val : ℕ) : ℝ) by positivity]
          linarith only [hmul, hsimp, hterm1, hterm2]
        have hpos_head : 0 ≤ 4 * (P.k : ℝ) ^ 2 / P.B_mid + 4 * P.T_mid ^ 2 := by positivity
        linarith only [hsum_card, h1, hpos_head]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
      positivity
  have hrest_le : ∑ z ∈ U_rest, (w * (d z : ℝ)) ^ 2 ≤
      (P.J : ℝ) * (4 * (P.k : ℝ) ^ 2 / P.B_mid + 4 * P.T_mid ^ 2 +
        480 * (P.k : ℝ) * P.T_big + 16 * P.T_big ^ 2) := by
    refine hsum_B.trans ?_
    calc ∑ j : Fin P.J, ∑ z ∈ B j, (w * (d z : ℝ)) ^ 2
        ≤ ∑ _j : Fin P.J, (4 * (P.k : ℝ) ^ 2 / P.B_mid + 4 * P.T_mid ^ 2 +
            480 * (P.k : ℝ) * P.T_big + 16 * P.T_big ^ 2) := Finset.sum_le_sum fun j _ => hBj_bound j
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith only [hsplit, hsplit2, hlow, hin_mid, hrest_le]

/-- Off-diagonal `(d_a = 1, d_b ≥ 2)` bound for `z ∉ Zbig`. -/
lemma sum_one_ge2_outside_Zbig_le (P : RegParams) (ω : EdgeIdx P.m → Bool)
    (hG : GoodGraph P ω) {A : Finset (Fin P.m)} {c : Fin P.m → ℕ} {F_max : ℝ}
    (hsum : ∑ r ∈ A, c r ≤ P.k)
    (hTlo : 0 < P.T_lo) (hTcut : P.T_lo ≤ P.T_cut) (hF_le_mid : F_max ≤ P.T_mid)
    (hTbig : 0 < P.T_big) (hBmid : 0 < P.B_mid) (hm_lt_J : P.m < 2 ^ P.J)
    (hL_le_F : ∀ i : Fin P.L, ((2 ^ i.val : ℕ) : ℝ) ≤ F_max) (a b : Fin P.L) :
    ∑ z ∈ Finset.univ.filter (fun z => z ∉ Zbig P ω A c ∧
        degIn (graphOf ω) (wtClass A c a.val) z = 1 ∧
        2 ≤ degIn (graphOf ω) (wtClass A c b.val) z),
        (((2 ^ a.val : ℕ) : ℝ) * (degIn (graphOf ω) (wtClass A c a.val) z : ℝ)) *
        (((2 ^ b.val : ℕ) : ℝ) * (degIn (graphOf ω) (wtClass A c b.val) z : ℝ)) ≤
      2 * P.T_cut * (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) +
      (P.k : ℝ) * F_max ^ 2 +
      (P.J : ℝ) * (2 * (P.k : ℝ) ^ 2 * F_max / (P.T_cut * P.B_mid) + 2 * F_max ^ 2) +
      (2 * P.T_lo * (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) +
        4 * (P.k : ℝ) * P.T_mid ^ 2 +
        (P.J : ℝ) * (4 * (P.k : ℝ) ^ 2 / P.B_mid + 4 * P.T_mid ^ 2 +
          480 * (P.k : ℝ) * P.T_big + 16 * P.T_big ^ 2)) := by
  set Sa := wtClass A c a.val
  set Sb := wtClass A c b.val
  set wa : ℝ := ((2 ^ a.val : ℕ) : ℝ)
  set wb : ℝ := ((2 ^ b.val : ℕ) : ℝ)
  set da : Fin P.m → ℕ := fun z => degIn (graphOf ω) Sa z
  set db : Fin P.m → ℕ := fun z => degIn (graphOf ω) Sb z
  have hwa_le : wa ≤ F_max := hL_le_F a
  have hF_pos : 0 < F_max := lt_of_lt_of_le (by positivity : (0 : ℝ) < wa) hwa_le
  have hTcut_pos : 0 < P.T_cut := lt_of_lt_of_le hTlo hTcut
  have hTmid_pos : 0 < P.T_mid := lt_of_lt_of_le hF_pos hF_le_mid
  set U := Finset.univ.filter (fun z => z ∉ Zbig P ω A c ∧ da z = 1 ∧ 2 ≤ db z)
  set U1 := U.filter (fun z => wb * (db z : ℝ) ≤ 2 * P.T_cut)
  set U23 := U.filter (fun z => ¬ wb * (db z : ℝ) ≤ 2 * P.T_cut)
  set U2 := U23.filter (fun z => wb * (db z : ℝ) ≤ F_max)
  set U3 := U23.filter (fun z => ¬ wb * (db z : ℝ) ≤ F_max)
  have hsplit : ∑ z ∈ U, (wa * (da z : ℝ)) * (wb * (db z : ℝ)) =
      (∑ z ∈ U1, (wa * (da z : ℝ)) * (wb * (db z : ℝ))) +
      (∑ z ∈ U2, (wa * (da z : ℝ)) * (wb * (db z : ℝ))) +
      (∑ z ∈ U3, (wa * (da z : ℝ)) * (wb * (db z : ℝ))) := by
    have h1 := (Finset.sum_filter_add_sum_filter_not U (fun z => wb * (db z : ℝ) ≤ 2 * P.T_cut)
      (fun z => (wa * (da z : ℝ)) * (wb * (db z : ℝ)))).symm
    have h2 := (Finset.sum_filter_add_sum_filter_not U23 (fun z => wb * (db z : ℝ) ≤ F_max)
      (fun z => (wa * (da z : ℝ)) * (wb * (db z : ℝ)))).symm
    linarith
  -- Part 1: wb * db z ≤ 2 * T_cut
  have h1 : ∑ z ∈ U1, (wa * (da z : ℝ)) * (wb * (db z : ℝ)) ≤
      2 * P.T_cut * (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) := by
    calc ∑ z ∈ U1, (wa * (da z : ℝ)) * (wb * (db z : ℝ))
        ≤ ∑ z ∈ U1, (2 * P.T_cut) * (wa * (da z : ℝ)) := by
          refine Finset.sum_le_sum fun z hz => ?_
          have hle := (Finset.mem_filter.mp hz).2
          have hnn : 0 ≤ wa * (da z : ℝ) := by positivity
          nlinarith
      _ = 2 * P.T_cut * ∑ z ∈ U1, (wa * (da z : ℝ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * P.T_cut * ∑ z : Fin P.m, (wa * (da z : ℝ)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_univ_sum_of_nonneg fun z => by positivity) (by positivity)
      _ ≤ 2 * P.T_cut * ((P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p))) :=
          mul_le_mul_of_nonneg_left (sum_wtClass_deg_le P ω hG.1 hsum a.val) (by positivity)
      _ = _ := by ring
  -- Part 3: F_max < wb * db z ⇒ wa * da z = wa ≤ F_max < wb * db z, bounded by diagonal b
  have h3 : ∑ z ∈ U3, (wa * (da z : ℝ)) * (wb * (db z : ℝ)) ≤
      2 * P.T_lo * (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) +
      4 * (P.k : ℝ) * P.T_mid ^ 2 +
      (P.J : ℝ) * (4 * (P.k : ℝ) ^ 2 / P.B_mid + 4 * P.T_mid ^ 2 +
        480 * (P.k : ℝ) * P.T_big + 16 * P.T_big ^ 2) := by
    have hsub : U3 ⊆ Finset.univ.filter (fun z => z ∉ Zbig P ω A c ∧ 2 ≤ db z) := by
      intro z hz
      have hU := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
      have hm := (Finset.mem_filter.mp hU).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm.1, hm.2.2⟩
    calc ∑ z ∈ U3, (wa * (da z : ℝ)) * (wb * (db z : ℝ))
        ≤ ∑ z ∈ U3, (wb * (db z : ℝ)) ^ 2 := by
          refine Finset.sum_le_sum fun z hz => ?_
          have hgt : F_max < wb * (db z : ℝ) := not_le.mp (Finset.mem_filter.mp hz).2
          have hU := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
          have hda1 : da z = 1 := (Finset.mem_filter.mp hU).2.2.1
          have hua : wa * (da z : ℝ) ≤ wb * (db z : ℝ) := by rw [hda1]; simp only [Nat.cast_one, mul_one]; linarith
          nlinarith [show 0 ≤ wb * (db z : ℝ) by positivity]
      _ ≤ ∑ z ∈ Finset.univ.filter (fun z => z ∉ Zbig P ω A c ∧ 2 ≤ db z), (wb * (db z : ℝ)) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
      _ ≤ _ := sum_diag_class_outside_Zbig_le P ω hG hsum hTlo hTmid_pos hTbig hBmid hm_lt_J b
  -- Part 2: 2 * T_cut < wb * db z ≤ F_max
  have hSb_le : Sb.card ≤ P.clsSize b.val := wtClass_card_le hsum b.val
  obtain ⟨Sb', hSbsub, hSb'card⟩ := exists_superset_card_eq hSb_le (min_le_left _ _)
  have hSb'mem : Sb' ∈ (Finset.univ : Finset (Fin P.m)).powersetCard (P.clsSize b.val) :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hSb'card⟩
  set U2_in := U2.filter (fun z => z ∈ Sb')
  set U2_out := U2.filter (fun z => z ∉ Sb')
  have h2_split : ∑ z ∈ U2, (wa * (da z : ℝ)) * (wb * (db z : ℝ)) =
      (∑ z ∈ U2_in, (wa * (da z : ℝ)) * (wb * (db z : ℝ))) +
      ∑ z ∈ U2_out, (wa * (da z : ℝ)) * (wb * (db z : ℝ)) :=
    (Finset.sum_filter_add_sum_filter_not U2 _ _).symm
  have h2_in : ∑ z ∈ U2_in, (wa * (da z : ℝ)) * (wb * (db z : ℝ)) ≤ (P.k : ℝ) * F_max ^ 2 := by
    have hcard_le : (U2_in.card : ℝ) ≤ (P.k : ℝ) := by
      have hsub : U2_in ⊆ Sb' := fun z hz => (Finset.mem_filter.mp hz).2
      have h1' : U2_in.card ≤ P.clsSize b.val := by rw [← hSb'card]; exact Finset.card_le_card hsub
      exact_mod_cast h1'.trans ((min_le_right _ _).trans (Nat.div_le_self _ _))
    calc ∑ z ∈ U2_in, (wa * (da z : ℝ)) * (wb * (db z : ℝ))
        ≤ ∑ _z ∈ U2_in, F_max ^ 2 := by
          refine Finset.sum_le_sum fun z hz => ?_
          have hz2 := (Finset.mem_filter.mp hz).1
          have hleF := (Finset.mem_filter.mp hz2).2
          have hda1 : da z = 1 :=
            (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz2).1).1).2.2.1
          rw [hda1, Nat.cast_one, mul_one, sq]
          exact mul_le_mul hwa_le hleF (by positivity) hF_pos.le
      _ = (U2_in.card : ℝ) * F_max ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (P.k : ℝ) * F_max ^ 2 := mul_le_mul_of_nonneg_right hcard_le (sq_nonneg _)
  -- Dyadic buckets for U2_out
  let B (j : Fin P.J) := U2_out.filter fun z => Nat.log 2 (db z) = j.val
  have hcov2 : U2_out ⊆ Finset.univ.biUnion B := by
    intro z hz
    have hdb_le : db z ≤ P.m := (Finset.card_le_univ _).trans (by simp)
    have hdb_ge2 : 2 ≤ db z :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).1).2.2.2
    have hlog_lt : Nat.log 2 (db z) < P.J :=
      (Nat.log_lt_iff_lt_pow (by omega : 1 < 2) (by omega)).mpr (lt_of_le_of_lt hdb_le hm_lt_J)
    exact Finset.mem_biUnion.mpr ⟨⟨Nat.log 2 (db z), hlog_lt⟩, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨hz, rfl⟩⟩
  have h2_out : ∑ z ∈ U2_out, (wa * (da z : ℝ)) * (wb * (db z : ℝ)) ≤
      (P.J : ℝ) * (2 * (P.k : ℝ) ^ 2 * F_max / (P.T_cut * P.B_mid) + 2 * F_max ^ 2) := by
    have hsum_le : ∑ z ∈ U2_out, (wa * (da z : ℝ)) * (wb * (db z : ℝ)) ≤
        ∑ j : Fin P.J, ∑ z ∈ B j, (wa * (da z : ℝ)) * (wb * (db z : ℝ)) := by
      calc _ ≤ ∑ z ∈ Finset.univ.biUnion B, (wa * (da z : ℝ)) * (wb * (db z : ℝ)) :=
              Finset.sum_le_sum_of_subset_of_nonneg hcov2 fun _ _ _ => by positivity
        _ ≤ _ := sum_biUnion_le_of_nonneg fun _ => by positivity
    refine hsum_le.trans ?_
    have hBj : ∀ j : Fin P.J, ∑ z ∈ B j, (wa * (da z : ℝ)) * (wb * (db z : ℝ)) ≤
        2 * (P.k : ℝ) ^ 2 * F_max / (P.T_cut * P.B_mid) + 2 * F_max ^ 2 := by
      intro j
      by_cases hne : (B j).Nonempty
      · obtain ⟨z₀, hz₀⟩ := hne
        have hlog0 : Nat.log 2 (db z₀) = j.val := (Finset.mem_filter.mp hz₀).2
        have hz₀_2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hz₀).1).1
        have hleF0 : wb * (db z₀ : ℝ) ≤ F_max := (Finset.mem_filter.mp hz₀_2).2
        have hgt0 : 2 * P.T_cut < wb * (db z₀ : ℝ) :=
          not_le.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz₀_2).1).2
        have hdb0_ge2 : 2 ≤ db z₀ :=
          (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz₀_2).1).1).2.2.2
        have hj1 : 1 ≤ j.val := by
          rw [← hlog0]; exact Nat.le_log_of_pow_le (by omega : 1 < 2) (by simpa using hdb0_ge2)
        have hwt_le_F : wb * ((2 ^ j.val : ℕ) : ℝ) ≤ F_max := by
          have h2j_le : ((2 ^ j.val : ℕ) : ℝ) ≤ (db z₀ : ℝ) := by
            rw [← hlog0]; exact_mod_cast Nat.pow_log_le_self 2 (by omega)
          have hwb_pos : 0 < wb := by positivity
          nlinarith only [hleF0, h2j_le, hwb_pos]
        have hwt_gt_cut : P.T_cut < wb * ((2 ^ j.val : ℕ) : ℝ) := by
          have hd_lt : (db z₀ : ℝ) < 2 * ((2 ^ j.val : ℕ) : ℝ) := by
            rw [← hlog0]
            have hnat := Nat.lt_pow_succ_log_self (by omega : 1 < 2) (db z₀)
            have hreal : (db z₀ : ℝ) < ((2 ^ (Nat.log 2 (db z₀) + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
            have hpow : ((2 ^ (Nat.log 2 (db z₀) + 1) : ℕ) : ℝ) = 2 * ((2 ^ (Nat.log 2 (db z₀)) : ℕ) : ℝ) := by
              push_cast; ring
            linarith only [hreal, hpow]
          have hwb_pos : 0 < wb := by positivity
          nlinarith only [hgt0, hd_lt, hwb_pos]
        have hBsub : B j ⊆ (Finset.univ \ Sb').filter fun z => 2 ^ j.val ≤ degIn (graphOf ω) Sb' z := by
          intro z hz
          have hlogz : Nat.log 2 (db z) = j.val := (Finset.mem_filter.mp hz).2
          have hz_out := (Finset.mem_filter.mp hz).1
          have hz_notSb' : z ∉ Sb' := (Finset.mem_filter.mp hz_out).2
          have hdbz_ge2 : 2 ≤ db z :=
            (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz_out).1).1).1).2.2.2
          have h2j_le : 2 ^ j.val ≤ db z := by rw [← hlogz]; exact Nat.pow_log_le_self 2 (by omega)
          exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hz_notSb'⟩,
            h2j_le.trans (degIn_mono (graphOf ω) hSbsub z)⟩
        have hcard_lt : (B j).card < P.rMid b.val j.val :=
          lt_of_le_of_lt (Finset.card_le_card hBsub)
            (hG.2.2.1 b j hj1 (hTcut.trans hwt_gt_cut.le) (hwt_le_F.trans hF_le_mid) Sb' hSb'mem)
        have hcard_real : ((B j).card : ℝ) ≤
            (P.k : ℝ) ^ 2 / ((wb * ((2 ^ j.val : ℕ) : ℝ)) ^ 2 * P.B_mid) + 1 := by
          have hle_r : ((B j).card : ℝ) ≤ (P.rMid b.val j.val : ℝ) := by exact_mod_cast hcard_lt.le
          have hceil := Nat.ceil_lt_add_one (show (0 : ℝ) ≤
            (P.k : ℝ) ^ 2 / (wb ^ 2 * ((2 ^ j.val : ℕ) : ℝ) ^ 2 * P.B_mid) by positivity)
          have heq : wb ^ 2 * ((2 ^ j.val : ℕ) : ℝ) ^ 2 * P.B_mid =
              (wb * ((2 ^ j.val : ℕ) : ℝ)) ^ 2 * P.B_mid := by ring
          dsimp only [RegParams.rMid] at hle_r
          change ((B j).card : ℝ) ≤ (⌈(P.k : ℝ) ^ 2 / (wb ^ 2 * ((2 ^ j.val : ℕ) : ℝ) ^ 2 * P.B_mid)⌉₊ : ℝ) at hle_r
          rw [heq] at hceil hle_r
          linarith only [hle_r, hceil]
        have hwt_pos : 0 < wb * ((2 ^ j.val : ℕ) : ℝ) := by positivity
        calc ∑ z ∈ B j, (wa * (da z : ℝ)) * (wb * (db z : ℝ))
            ≤ ∑ _z ∈ B j, (2 * F_max * (wb * ((2 ^ j.val : ℕ) : ℝ))) := by
              refine Finset.sum_le_sum fun z hz => ?_
              have hlogz : Nat.log 2 (db z) = j.val := (Finset.mem_filter.mp hz).2
              have hda1 : da z = 1 :=
                (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp
                  (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).1).1).2.2.1
              have hd_lt : (db z : ℝ) < 2 * ((2 ^ j.val : ℕ) : ℝ) := by
                rw [← hlogz]
                have hnat := Nat.lt_pow_succ_log_self (by omega : 1 < 2) (db z)
                have hreal : (db z : ℝ) < ((2 ^ (Nat.log 2 (db z) + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
                have hpow : ((2 ^ (Nat.log 2 (db z) + 1) : ℕ) : ℝ) = 2 * ((2 ^ (Nat.log 2 (db z)) : ℕ) : ℝ) := by
                  push_cast; ring
                linarith only [hreal, hpow]
              rw [hda1, Nat.cast_one, mul_one]
              have hwb_pos : 0 < wb := by positivity
              have hle2 : wb * (db z : ℝ) ≤ 2 * (wb * ((2 ^ j.val : ℕ) : ℝ)) := by nlinarith only [hd_lt, hwb_pos]
              have h1' := mul_le_mul hwa_le hle2 (by positivity) hF_pos.le
              linarith only [h1']
          _ = ((B j).card : ℝ) * (2 * F_max * (wb * ((2 ^ j.val : ℕ) : ℝ))) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ((P.k : ℝ) ^ 2 / ((wb * ((2 ^ j.val : ℕ) : ℝ)) ^ 2 * P.B_mid) + 1) *
              (2 * F_max * (wb * ((2 ^ j.val : ℕ) : ℝ))) :=
              mul_le_mul_of_nonneg_right hcard_real (by positivity)
          _ = 2 * (P.k : ℝ) ^ 2 * F_max / ((wb * ((2 ^ j.val : ℕ) : ℝ)) * P.B_mid) +
              2 * F_max * (wb * ((2 ^ j.val : ℕ) : ℝ)) := by
              have hwb_ne : wb ≠ 0 := by positivity
              have h2j_ne : ((2 ^ j.val : ℕ) : ℝ) ≠ 0 := by positivity
              field_simp [hwb_ne, h2j_ne, hBmid.ne']
          _ ≤ 2 * (P.k : ℝ) ^ 2 * F_max / (P.T_cut * P.B_mid) + 2 * F_max ^ 2 := by
              refine add_le_add ?_ ?_
              · refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
                exact mul_le_mul_of_nonneg_right hwt_gt_cut.le hBmid.le
              · nlinarith only [hwt_le_F, hF_pos]
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
        positivity
    calc ∑ j : Fin P.J, _
        ≤ ∑ _j : Fin P.J, (2 * (P.k : ℝ) ^ 2 * F_max / (P.T_cut * P.B_mid) + 2 * F_max ^ 2) :=
          Finset.sum_le_sum fun j _ => hBj j
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith only [hsplit, h1, h3, h2_split, h2_in, h2_out]

/-- Off-diagonal `(d_a = 1, d_b = 1)` bound for `a < b`. -/
lemma sum_one_one_le (P : RegParams) (ω : EdgeIdx P.m → Bool)
    (hCross : GoodCrossPair P ω) {A : Finset (Fin P.m)} {c : Fin P.m → ℕ} {F_max : ℝ}
    (hsum : ∑ r ∈ A, c r ≤ P.k) (h2k : 2 * P.k ≤ P.m) (hBcross : 0 < P.B_cross)
    (hL_le_F : ∀ i : Fin P.L, ((2 ^ i.val : ℕ) : ℝ) ≤ F_max) {a b : Fin P.L} (hab : a.val < b.val) :
    ∑ z ∈ Finset.univ.filter (fun z =>
        degIn (graphOf ω) (wtClass A c a.val) z = 1 ∧
        degIn (graphOf ω) (wtClass A c b.val) z = 1),
        (((2 ^ a.val : ℕ) : ℝ) * (degIn (graphOf ω) (wtClass A c a.val) z : ℝ)) *
        (((2 ^ b.val : ℕ) : ℝ) * (degIn (graphOf ω) (wtClass A c b.val) z : ℝ)) ≤
      2 * (P.k : ℝ) * F_max ^ 2 + (P.k : ℝ) ^ 2 / P.B_cross + F_max ^ 2 := by
  set Sa := wtClass A c a.val
  set Sb := wtClass A c b.val
  set wa : ℝ := ((2 ^ a.val : ℕ) : ℝ)
  set wb : ℝ := ((2 ^ b.val : ℕ) : ℝ)
  have hwa_le : wa ≤ F_max := hL_le_F a
  have hwb_le : wb ≤ F_max := hL_le_F b
  have hF_pos : 0 < F_max := lt_of_lt_of_le (by positivity : (0 : ℝ) < wa) hwa_le
  have hdisj : Disjoint Sa Sb := wtClass_disjoint A c (by omega)
  have hSa_le : Sa.card ≤ P.clsSize a.val := wtClass_card_le hsum a.val
  have hSb_le : Sb.card ≤ P.clsSize b.val := wtClass_card_le hsum b.val
  have hsum_cls : P.clsSize a.val + P.clsSize b.val ≤ P.m := by
    have h1 : P.clsSize a.val ≤ P.k := (min_le_right _ _).trans (Nat.div_le_self _ _)
    have h2 : P.clsSize b.val ≤ P.k := (min_le_right _ _).trans (Nat.div_le_self _ _)
    omega
  obtain ⟨Sa', Sb', hSa_sub, hSb_sub, hSa'c, hSb'c, hdisj'⟩ :=
    exists_disjoint_supersets_card_eq hdisj hSa_le hSb_le hsum_cls
  have hSa'mem : Sa' ∈ (Finset.univ : Finset (Fin P.m)).powersetCard (P.clsSize a.val) :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hSa'c⟩
  have hSb'mem : Sb' ∈ (Finset.univ : Finset (Fin P.m)).powersetCard (P.clsSize b.val) :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hSb'c⟩
  set U := Finset.univ.filter (fun z => degIn (graphOf ω) Sa z = 1 ∧ degIn (graphOf ω) Sb z = 1)
  set U_in := U.filter (fun z => z ∈ Sa' ∪ Sb')
  set U_out := U.filter (fun z => z ∉ Sa' ∪ Sb')
  have hsplit : ∑ z ∈ U, (wa * (degIn (graphOf ω) Sa z : ℝ)) * (wb * (degIn (graphOf ω) Sb z : ℝ)) =
      (∑ z ∈ U_in, (wa * (degIn (graphOf ω) Sa z : ℝ)) * (wb * (degIn (graphOf ω) Sb z : ℝ))) +
      ∑ z ∈ U_out, (wa * (degIn (graphOf ω) Sa z : ℝ)) * (wb * (degIn (graphOf ω) Sb z : ℝ)) :=
    (Finset.sum_filter_add_sum_filter_not U _ _).symm
  have hin : ∑ z ∈ U_in, (wa * (degIn (graphOf ω) Sa z : ℝ)) * (wb * (degIn (graphOf ω) Sb z : ℝ)) ≤
      2 * (P.k : ℝ) * F_max ^ 2 := by
    have hcard_le : (U_in.card : ℝ) ≤ 2 * (P.k : ℝ) := by
      have hsub : U_in ⊆ Sa' ∪ Sb' := fun z hz => (Finset.mem_filter.mp hz).2
      have h1 : (Sa' ∪ Sb').card ≤ 2 * P.k := by
        rw [Finset.card_union_of_disjoint hdisj', hSa'c, hSb'c]
        have ha : P.clsSize a.val ≤ P.k := (min_le_right _ _).trans (Nat.div_le_self _ _)
        have hb : P.clsSize b.val ≤ P.k := (min_le_right _ _).trans (Nat.div_le_self _ _)
        omega
      exact_mod_cast (Finset.card_le_card hsub).trans h1
    calc ∑ z ∈ U_in, (wa * (degIn (graphOf ω) Sa z : ℝ)) * (wb * (degIn (graphOf ω) Sb z : ℝ))
        ≤ ∑ _z ∈ U_in, F_max ^ 2 := by
          refine Finset.sum_le_sum fun z hz => ?_
          rcases (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2 with ⟨hd1, hd2⟩
          rw [hd1, hd2]; simp only [Nat.cast_one, mul_one, sq]
          exact mul_le_mul hwa_le hwb_le (by positivity) hF_pos.le
      _ = (U_in.card : ℝ) * F_max ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (P.k : ℝ) * F_max ^ 2 := mul_le_mul_of_nonneg_right hcard_le (sq_nonneg _)
  have hout : ∑ z ∈ U_out, (wa * (degIn (graphOf ω) Sa z : ℝ)) * (wb * (degIn (graphOf ω) Sb z : ℝ)) ≤
      (P.k : ℝ) ^ 2 / P.B_cross + F_max ^ 2 := by
    have hsub : U_out ⊆ (Finset.univ \ (Sa' ∪ Sb')).filter fun z =>
        1 ≤ degIn (graphOf ω) Sa' z ∧ 1 ≤ degIn (graphOf ω) Sb' z := by
      intro z hz
      have hnot := (Finset.mem_filter.mp hz).2
      rcases (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2 with ⟨hd1, hd2⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩,
        (by omega : 1 ≤ degIn (graphOf ω) Sa z).trans (degIn_mono (graphOf ω) hSa_sub z),
        (by omega : 1 ≤ degIn (graphOf ω) Sb z).trans (degIn_mono (graphOf ω) hSb_sub z)⟩
    have hcard_lt : U_out.card < P.rCross a.val b.val :=
      lt_of_le_of_lt (Finset.card_le_card hsub) (hCross a b hab Sa' hSa'mem Sb' hSb'mem hdisj')
    have hcard_real : (U_out.card : ℝ) ≤ (P.k : ℝ) ^ 2 / (wa * wb * P.B_cross) + 1 := by
      have hle : (U_out.card : ℝ) ≤ (P.rCross a.val b.val : ℝ) := by exact_mod_cast hcard_lt.le
      have hceil := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (P.k : ℝ) ^ 2 / (wa * wb * P.B_cross) by positivity)
      dsimp only [RegParams.rCross] at hle
      linarith
    have hwab_pos : 0 < wa * wb := by positivity
    calc ∑ z ∈ U_out, (wa * (degIn (graphOf ω) Sa z : ℝ)) * (wb * (degIn (graphOf ω) Sb z : ℝ))
        = ∑ _z ∈ U_out, (wa * wb) := by
          refine Finset.sum_congr rfl fun z hz => ?_
          rcases (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2 with ⟨hd1, hd2⟩
          rw [hd1, hd2]; simp
      _ = (U_out.card : ℝ) * (wa * wb) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((P.k : ℝ) ^ 2 / (wa * wb * P.B_cross) + 1) * (wa * wb) :=
          mul_le_mul_of_nonneg_right hcard_real hwab_pos.le
      _ = (P.k : ℝ) ^ 2 / P.B_cross + wa * wb := by
          have hwa_ne : wa ≠ 0 := by positivity
          have hwb_ne : wb ≠ 0 := by positivity
          field_simp [hwa_ne, hwb_ne, hBcross.ne']
      _ ≤ (P.k : ℝ) ^ 2 / P.B_cross + F_max ^ 2 := by
          refine add_le_add le_rfl ?_
          rw [sq]; exact mul_le_mul hwa_le hwb_le (by positivity) hF_pos.le
  linarith

/-- Total weighted distinct-fiber 2-path sum OUTSIDE `Zbig`:
`∑_{z ∉ Zbig} ∑_{r₁, r₂ ∈ A ∩ N(z), r₁ ≠ r₂} c(r₁) c(r₂) ≤ errOut`. -/
noncomputable def errOut (P : RegParams) (F_max : ℝ) : ℝ :=
  4 * ((P.L : ℝ) ^ 2) * (
    4 * (2 * P.T_lo * (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) +
      4 * (P.k : ℝ) * P.T_mid ^ 2 +
      (P.J : ℝ) * (4 * (P.k : ℝ) ^ 2 / P.B_mid + 4 * P.T_mid ^ 2 +
        480 * (P.k : ℝ) * P.T_big + 16 * P.T_big ^ 2)) +
    2 * (2 * P.T_cut * (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) +
      (P.k : ℝ) * F_max ^ 2 +
      (P.J : ℝ) * (2 * (P.k : ℝ) ^ 2 * F_max / (P.T_cut * P.B_mid) + 2 * F_max ^ 2)) +
    (2 * (P.k : ℝ) * F_max ^ 2 + (P.k : ℝ) ^ 2 / P.B_cross + F_max ^ 2))

lemma sum_weighted_pairs_outside_Zbig_le (P : RegParams) (ω : EdgeIdx P.m → Bool)
    (hG : GoodGraph P ω) {A : Finset (Fin P.m)} {c : Fin P.m → ℕ} {F_max : ℝ}
    (hsum : ∑ r ∈ A, c r ≤ P.k) (h2k : 2 * P.k ≤ P.m)
    (hc_lt : ∀ r ∈ A, c r < 2 ^ P.L)
    (hTlo : 0 < P.T_lo) (hTcut : P.T_lo ≤ P.T_cut) (hF_le_mid : F_max ≤ P.T_mid)
    (hTbig : 0 < P.T_big) (hBmid : 0 < P.B_mid) (hBcross : 0 < P.B_cross)
    (hm_lt_J : P.m < 2 ^ P.J)
    (hL_le_F : ∀ i : Fin P.L, ((2 ^ i.val : ℕ) : ℝ) ≤ F_max) :
    ∑ z ∈ Finset.univ.filter (fun z => z ∉ Zbig P ω A c),
        ∑ r₁ ∈ A.filter (fun r => (graphOf ω).Adj z r),
        ∑ r₂ ∈ (A.filter (fun r => (graphOf ω).Adj z r)).erase r₁,
          ((c r₁ : ℝ) * (c r₂ : ℝ)) ≤ errOut P F_max := by
  let u : Fin P.L → Fin P.m → ℝ := fun i z =>
    ((2 ^ i.val : ℕ) : ℝ) * (degIn (graphOf ω) (wtClass A c i.val) z : ℝ)
  let d : Fin P.L → Fin P.m → ℕ := fun i z => degIn (graphOf ω) (wtClass A c i.val) z
  -- Pointwise bound at each z: decompose r₁, r₂ into their dyadic classes a, b : Fin P.L
  have hpt : ∀ z : Fin P.m,
      ∑ r₁ ∈ A.filter (fun r => (graphOf ω).Adj z r),
      ∑ r₂ ∈ (A.filter (fun r => (graphOf ω).Adj z r)).erase r₁, ((c r₁ : ℝ) * (c r₂ : ℝ)) ≤
      4 * ∑ a : Fin P.L, ∑ b : Fin P.L,
        if a = b then (if 2 ≤ d a z then (u a z) ^ 2 else 0)
        else u a z * u b z := by
    intro z
    let N := A.filter fun r => (graphOf ω).Adj z r
    let Ni (i : Fin P.L) := (wtClass A c i.val).filter fun r => (graphOf ω).Adj z r
    have hNi_card : ∀ i : Fin P.L, (Ni i).card = d i z := fun _ => rfl
    have hpair_le : ∀ r₁ ∈ N, ∀ r₂ ∈ N.erase r₁,
        (c r₁ : ℝ) * (c r₂ : ℝ) ≤
        4 * ∑ a : Fin P.L, ∑ b : Fin P.L,
          if r₁ ∈ Ni a ∧ r₂ ∈ Ni b then ((2 ^ a.val : ℕ) : ℝ) * ((2 ^ b.val : ℕ) : ℝ) else 0 := by
      intro r₁ hr1 r₂ hr2
      by_cases h1 : c r₁ = 0
      · rw [h1]; simp only [Nat.cast_zero, zero_mul]
        exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity)
      · by_cases h2 : c r₂ = 0
        · rw [h2]; simp only [Nat.cast_zero, mul_zero]
          exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity)
        · have hr1A := (Finset.mem_filter.mp hr1).1
          have hr1adj := (Finset.mem_filter.mp hr1).2
          have hr2N := (Finset.mem_erase.mp hr2).2
          have hr2A := (Finset.mem_filter.mp hr2N).1
          have hr2adj := (Finset.mem_filter.mp hr2N).2
          obtain ⟨a, ha⟩ := mem_wtClass_of_pos hr1A (by omega) (hc_lt r₁ hr1A)
          obtain ⟨b, hb⟩ := mem_wtClass_of_pos hr2A (by omega) (hc_lt r₂ hr2A)
          have h1lt : (c r₁ : ℝ) ≤ 2 * ((2 ^ a.val : ℕ) : ℝ) := by
            have hlt := (Finset.mem_filter.mp ha).2.2
            have hreal : (c r₁ : ℝ) < ((2 ^ (a.val + 1) : ℕ) : ℝ) := by exact_mod_cast hlt
            have hpow : ((2 ^ (a.val + 1) : ℕ) : ℝ) = 2 * ((2 ^ a.val : ℕ) : ℝ) := by push_cast; ring
            linarith
          have h2lt : (c r₂ : ℝ) ≤ 2 * ((2 ^ b.val : ℕ) : ℝ) := by
            have hlt := (Finset.mem_filter.mp hb).2.2
            have hreal : (c r₂ : ℝ) < ((2 ^ (b.val + 1) : ℕ) : ℝ) := by exact_mod_cast hlt
            have hpow : ((2 ^ (b.val + 1) : ℕ) : ℝ) = 2 * ((2 ^ b.val : ℕ) : ℝ) := by push_cast; ring
            linarith
          have hmem_a : r₁ ∈ Ni a := Finset.mem_filter.mpr ⟨ha, hr1adj⟩
          have hmem_b : r₂ ∈ Ni b := Finset.mem_filter.mpr ⟨hb, hr2adj⟩
          have hsingle : ((2 ^ a.val : ℕ) : ℝ) * ((2 ^ b.val : ℕ) : ℝ) ≤
              ∑ a' : Fin P.L, ∑ b' : Fin P.L,
                if r₁ ∈ Ni a' ∧ r₂ ∈ Ni b' then ((2 ^ a'.val : ℕ) : ℝ) * ((2 ^ b'.val : ℕ) : ℝ) else 0 := by
            have hinner : ((2 ^ a.val : ℕ) : ℝ) * ((2 ^ b.val : ℕ) : ℝ) ≤
                ∑ b' : Fin P.L,
                  if r₁ ∈ Ni a ∧ r₂ ∈ Ni b' then ((2 ^ a.val : ℕ) : ℝ) * ((2 ^ b'.val : ℕ) : ℝ) else 0 := by
              have hval : (if r₁ ∈ Ni a ∧ r₂ ∈ Ni b then ((2 ^ a.val : ℕ) : ℝ) * ((2 ^ b.val : ℕ) : ℝ) else 0) =
                  ((2 ^ a.val : ℕ) : ℝ) * ((2 ^ b.val : ℕ) : ℝ) := if_pos ⟨hmem_a, hmem_b⟩
              rw [← hval]
              exact Finset.single_le_sum
                (f := fun b' : Fin P.L => if r₁ ∈ Ni a ∧ r₂ ∈ Ni b' then ((2 ^ a.val : ℕ) : ℝ) * ((2 ^ b'.val : ℕ) : ℝ) else 0)
                (fun _ _ => by split_ifs <;> positivity) (Finset.mem_univ b)
            exact hinner.trans (Finset.single_le_sum
              (f := fun a' : Fin P.L => ∑ b' : Fin P.L,
                if r₁ ∈ Ni a' ∧ r₂ ∈ Ni b' then ((2 ^ a'.val : ℕ) : ℝ) * ((2 ^ b'.val : ℕ) : ℝ) else 0)
              (fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity) (Finset.mem_univ a))
          have hprod : (c r₁ : ℝ) * (c r₂ : ℝ) ≤ 4 * (((2 ^ a.val : ℕ) : ℝ) * ((2 ^ b.val : ℕ) : ℝ)) := by
            have hmul := mul_le_mul h1lt h2lt (Nat.cast_nonneg _) (by positivity)
            linarith
          linarith
    calc ∑ r₁ ∈ N, ∑ r₂ ∈ N.erase r₁, ((c r₁ : ℝ) * (c r₂ : ℝ))
        ≤ ∑ r₁ ∈ N, ∑ r₂ ∈ N.erase r₁,
            4 * ∑ a : Fin P.L, ∑ b : Fin P.L,
              if r₁ ∈ Ni a ∧ r₂ ∈ Ni b then ((2 ^ a.val : ℕ) : ℝ) * ((2 ^ b.val : ℕ) : ℝ) else 0 :=
          Finset.sum_le_sum fun r₁ hr1 => Finset.sum_le_sum fun r₂ hr2 => hpair_le r₁ hr1 r₂ hr2
      _ = 4 * ∑ a : Fin P.L, ∑ b : Fin P.L,
            ∑ r₁ ∈ N, ∑ r₂ ∈ N.erase r₁,
              if r₁ ∈ Ni a ∧ r₂ ∈ Ni b then ((2 ^ a.val : ℕ) : ℝ) * ((2 ^ b.val : ℕ) : ℝ) else 0 := by
          simp_rw [← Finset.mul_sum]; congr 1
          have hstep1 : ∀ r₁ ∈ N,
              (∑ r₂ ∈ N.erase r₁, ∑ a : Fin P.L, ∑ b : Fin P.L,
                if r₁ ∈ Ni a ∧ r₂ ∈ Ni b then ((2 ^ a.val : ℕ) : ℝ) * ((2 ^ b.val : ℕ) : ℝ) else 0) =
              ∑ a : Fin P.L, ∑ b : Fin P.L, ∑ r₂ ∈ N.erase r₁,
                if r₁ ∈ Ni a ∧ r₂ ∈ Ni b then ((2 ^ a.val : ℕ) : ℝ) * ((2 ^ b.val : ℕ) : ℝ) else 0 := by
            intro r₁ _
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
          rw [Finset.sum_congr rfl hstep1, Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ ≤ 4 * ∑ a : Fin P.L, ∑ b : Fin P.L,
            if a = b then (if 2 ≤ d a z then (u a z) ^ 2 else 0) else u a z * u b z := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_) (by norm_num)
          have hNi_sub : ∀ i : Fin P.L, Ni i ⊆ N := fun i =>
            Finset.filter_subset_filter _ (Finset.filter_subset _ _)
          have hcount : (∑ r₁ ∈ N, ∑ r₂ ∈ N.erase r₁,
              if r₁ ∈ Ni a ∧ r₂ ∈ Ni b then ((2 ^ a.val : ℕ) : ℝ) * ((2 ^ b.val : ℕ) : ℝ) else 0) ≤
              u a z * u b z := by
            have hle1 : (∑ r₁ ∈ N, ∑ r₂ ∈ N.erase r₁,
                if r₁ ∈ Ni a ∧ r₂ ∈ Ni b then ((2 ^ a.val : ℕ) : ℝ) * ((2 ^ b.val : ℕ) : ℝ) else 0) ≤
                ∑ r₁ ∈ N, ∑ r₂ ∈ N,
                  if r₁ ∈ Ni a ∧ r₂ ∈ Ni b then ((2 ^ a.val : ℕ) : ℝ) * ((2 ^ b.val : ℕ) : ℝ) else 0 :=
              Finset.sum_le_sum fun r₁ _ =>
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun _ _ _ => by split_ifs <;> positivity
            refine hle1.trans (le_of_eq ?_)
            have hinner : ∀ r₁ ∈ N, (∑ r₂ ∈ N,
                if r₁ ∈ Ni a ∧ r₂ ∈ Ni b then ((2 ^ a.val : ℕ) : ℝ) * ((2 ^ b.val : ℕ) : ℝ) else 0) =
                if r₁ ∈ Ni a then ((2 ^ a.val : ℕ) : ℝ) * u b z else 0 := by
              intro r₁ _
              by_cases hr1 : r₁ ∈ Ni a
              · simp only [hr1, true_and, if_true]
                rw [← Finset.sum_filter, show N.filter (fun r₂ => r₂ ∈ Ni b) = Ni b from
                  Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr (hNi_sub b))]
                rw [Finset.sum_const, hNi_card b, nsmul_eq_mul]
                dsimp only [u]; ring
              · simp [hr1]
            rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter,
              show N.filter (fun r₁ => r₁ ∈ Ni a) = Ni a from
                Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr (hNi_sub a)),
              Finset.sum_const, hNi_card a, nsmul_eq_mul]
            dsimp only [u]; ring
          by_cases hab : a = b
          · subst hab; simp only [if_true]
            by_cases hd2 : 2 ≤ d a z
            · rw [if_pos hd2, sq]; exact hcount
            · rw [if_neg hd2]
              have hzero : ∀ r₁ ∈ N, ∀ r₂ ∈ N.erase r₁, ¬ (r₁ ∈ Ni a ∧ r₂ ∈ Ni a) := by
                intro r₁ _ r₂ hr2 ⟨h1, h2⟩
                have hne : r₂ ≠ r₁ := (Finset.mem_erase.mp hr2).1
                have hcard2 : 2 ≤ (Ni a).card := by
                  have hsub : ({r₁, r₂} : Finset (Fin P.m)) ⊆ Ni a :=
                    Finset.insert_subset h1 (Finset.singleton_subset_iff.mpr h2)
                  have := Finset.card_le_card hsub
                  rw [Finset.card_pair hne.symm] at this; exact this
                rw [hNi_card a] at hcard2; omega
              have hsum0 : (∑ r₁ ∈ N, ∑ r₂ ∈ N.erase r₁,
                  if r₁ ∈ Ni a ∧ r₂ ∈ Ni a then ((2 ^ a.val : ℕ) : ℝ) * ((2 ^ a.val : ℕ) : ℝ) else 0) = 0 :=
                Finset.sum_eq_zero fun r₁ hr1 => Finset.sum_eq_zero fun r₂ hr2 => if_neg (hzero r₁ hr1 r₂ hr2)
              rw [hsum0]
          · simp only [if_neg hab]; exact hcount
  -- Sum over z ∉ Zbig and swap sums over (a, b)
  set Zc := Finset.univ.filter (fun z : Fin P.m => z ∉ Zbig P ω A c)
  by_cases hL0 : P.L = 0
  · have h0 : ∀ z ∈ Zc, (∑ r₁ ∈ A.filter (fun r => (graphOf ω).Adj z r),
        ∑ r₂ ∈ (A.filter (fun r => (graphOf ω).Adj z r)).erase r₁, ((c r₁ : ℝ) * (c r₂ : ℝ))) = 0 := by
      intro z _
      refine Finset.sum_eq_zero fun r₁ hr1 => Finset.sum_eq_zero fun r₂ _ => ?_
      have hlt := hc_lt r₁ (Finset.mem_filter.mp hr1).1
      rw [hL0, pow_zero] at hlt
      have : c r₁ = 0 := by omega
      simp [this]
    rw [Finset.sum_eq_zero h0]
    simp [errOut, hL0]
  have hLpos : 0 < P.L := Nat.pos_of_ne_zero hL0
  have hF_ge1 : (1 : ℝ) ≤ F_max := by simpa using hL_le_F ⟨0, hLpos⟩
  have hTmid_pos' : 0 < P.T_mid := lt_of_lt_of_le (by linarith : (0 : ℝ) < 1) (hF_ge1.trans hF_le_mid)
  set D_bound : ℝ := 2 * P.T_lo * (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) +
      4 * (P.k : ℝ) * P.T_mid ^ 2 +
      (P.J : ℝ) * (4 * (P.k : ℝ) ^ 2 / P.B_mid + 4 * P.T_mid ^ 2 +
        480 * (P.k : ℝ) * P.T_big + 16 * P.T_big ^ 2)
  set O12_bound : ℝ := 2 * P.T_cut * (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) +
      (P.k : ℝ) * F_max ^ 2 +
      (P.J : ℝ) * (2 * (P.k : ℝ) ^ 2 * F_max / (P.T_cut * P.B_mid) + 2 * F_max ^ 2)
  set O11_bound : ℝ := 2 * (P.k : ℝ) * F_max ^ 2 + (P.k : ℝ) ^ 2 / P.B_cross + F_max ^ 2
  have hD_nn : 0 ≤ D_bound := by
    have hdeg_nn : 0 ≤ (1 + P.η₀) * ((P.m : ℝ) * P.p) := by
      by_cases hm : 0 < P.m
      · exact le_trans (Nat.cast_nonneg _) (hG.1 ⟨0, hm⟩)
      · have hm0 : P.m = 0 := by omega
        simp [hm0]
    dsimp only [D_bound]; positivity
  have hO12_nn : 0 ≤ O12_bound := by
    have hdeg_nn : 0 ≤ (1 + P.η₀) * ((P.m : ℝ) * P.p) := by
      by_cases hm : 0 < P.m
      · exact le_trans (Nat.cast_nonneg _) (hG.1 ⟨0, hm⟩)
      · have hm0 : P.m = 0 := by omega
        simp [hm0]
    have hTcut_pos : 0 < P.T_cut := lt_of_lt_of_le hTlo hTcut
    dsimp only [O12_bound]; positivity
  have hO11_nn : 0 ≤ O11_bound := by dsimp only [O11_bound]; positivity
  have hpair_ab : ∀ a b : Fin P.L,
      ∑ z ∈ Zc, (if a = b then (if 2 ≤ d a z then (u a z) ^ 2 else 0) else u a z * u b z) ≤
        4 * D_bound + 2 * O12_bound + O11_bound := by
    intro a b
    by_cases hab : a = b
    · subst hab; simp only [if_true]
      rw [← Finset.sum_filter]
      have heq : Zc.filter (fun z => 2 ≤ d a z) =
          Finset.univ.filter (fun z => z ∉ Zbig P ω A c ∧ 2 ≤ d a z) := by
        ext z; simp [Zc]
      rw [heq]
      have hdiag := sum_diag_class_outside_Zbig_le P ω hG hsum hTlo hTmid_pos' hTbig hBmid hm_lt_J a
      linarith
    · simp only [if_neg hab]
      have hpoint : ∀ z ∈ Zc, u a z * u b z ≤
          (if 2 ≤ d a z then (u a z) ^ 2 else 0) +
          (if 2 ≤ d b z then (u b z) ^ 2 else 0) +
          (if d a z = 1 ∧ 2 ≤ d b z then u a z * u b z else 0) +
          (if d b z = 1 ∧ 2 ≤ d a z then u b z * u a z else 0) +
          (if d a z = 1 ∧ d b z = 1 then u a z * u b z else 0) := by
        intro z _
        have hnn1 : 0 ≤ (if 2 ≤ d a z then (u a z) ^ 2 else 0) := by split_ifs <;> positivity
        have hnn2 : 0 ≤ (if 2 ≤ d b z then (u b z) ^ 2 else 0) := by split_ifs <;> positivity
        have hnn3 : 0 ≤ (if d a z = 1 ∧ 2 ≤ d b z then u a z * u b z else 0) := by split_ifs <;> positivity
        have hnn4 : 0 ≤ (if d b z = 1 ∧ 2 ≤ d a z then u b z * u a z else 0) := by split_ifs <;> positivity
        have hnn5 : 0 ≤ (if d a z = 1 ∧ d b z = 1 then u a z * u b z else 0) := by split_ifs <;> positivity
        by_cases ha0 : d a z = 0
        · have hu0 : u a z = 0 := by
            dsimp only [u]; change ((2 ^ a.val : ℕ) : ℝ) * (d a z : ℝ) = 0; rw [ha0]; simp
          linarith only [hu0, hnn1, hnn2, hnn3, hnn4, hnn5, show u a z * u b z = 0 by rw [hu0, zero_mul]]
        · by_cases hb0 : d b z = 0
          · have hu0 : u b z = 0 := by
              dsimp only [u]; change ((2 ^ b.val : ℕ) : ℝ) * (d b z : ℝ) = 0; rw [hb0]; simp
            linarith only [hu0, hnn1, hnn2, hnn3, hnn4, hnn5, show u a z * u b z = 0 by rw [hu0, mul_zero]]
          · by_cases ha1 : d a z = 1
            · by_cases hb1 : d b z = 1
              · have h5 : (if d a z = 1 ∧ d b z = 1 then u a z * u b z else 0) = u a z * u b z :=
                  if_pos ⟨ha1, hb1⟩
                linarith only [hnn1, hnn2, hnn3, hnn4, h5]
              · have hb2 : 2 ≤ d b z := by omega
                have h3 : (if d a z = 1 ∧ 2 ≤ d b z then u a z * u b z else 0) = u a z * u b z :=
                  if_pos ⟨ha1, hb2⟩
                linarith only [hnn1, hnn2, h3, hnn4, hnn5]
            · have ha2 : 2 ≤ d a z := by omega
              by_cases hb1 : d b z = 1
              · have h4 : (if d b z = 1 ∧ 2 ≤ d a z then u b z * u a z else 0) = u b z * u a z :=
                  if_pos ⟨hb1, ha2⟩
                linarith only [hnn1, hnn2, hnn3, h4, hnn5, mul_comm (u a z) (u b z)]
              · have hb2 : 2 ≤ d b z := by omega
                have h1 : (if 2 ≤ d a z then (u a z) ^ 2 else 0) = (u a z) ^ 2 := if_pos ha2
                have h2 : (if 2 ≤ d b z then (u b z) ^ 2 else 0) = (u b z) ^ 2 := if_pos hb2
                have hamgm : u a z * u b z ≤ (u a z) ^ 2 + (u b z) ^ 2 := by
                  nlinarith only [sq_nonneg (u a z - u b z)]
                linarith only [h1, h2, hnn3, hnn4, hnn5, hamgm]
      refine (Finset.sum_le_sum hpoint).trans ?_
      simp only [Finset.sum_add_distrib]
      have hT1 : (∑ z ∈ Zc, if 2 ≤ d a z then (u a z) ^ 2 else 0) ≤ D_bound := by
        rw [← Finset.sum_filter]
        have heq : Zc.filter (fun z => 2 ≤ d a z) =
            Finset.univ.filter (fun z => z ∉ Zbig P ω A c ∧ 2 ≤ d a z) := by ext z; simp [Zc]
        rw [heq]; exact sum_diag_class_outside_Zbig_le P ω hG hsum hTlo hTmid_pos' hTbig hBmid hm_lt_J a
      have hT2 : (∑ z ∈ Zc, if 2 ≤ d b z then (u b z) ^ 2 else 0) ≤ D_bound := by
        rw [← Finset.sum_filter]
        have heq : Zc.filter (fun z => 2 ≤ d b z) =
            Finset.univ.filter (fun z => z ∉ Zbig P ω A c ∧ 2 ≤ d b z) := by ext z; simp [Zc]
        rw [heq]; exact sum_diag_class_outside_Zbig_le P ω hG hsum hTlo hTmid_pos' hTbig hBmid hm_lt_J b
      have hT3 : (∑ z ∈ Zc, if d a z = 1 ∧ 2 ≤ d b z then u a z * u b z else 0) ≤ O12_bound + D_bound := by
        rw [← Finset.sum_filter]
        have heq : Zc.filter (fun z => d a z = 1 ∧ 2 ≤ d b z) =
            Finset.univ.filter (fun z => z ∉ Zbig P ω A c ∧ d a z = 1 ∧ 2 ≤ d b z) := by ext z; simp [Zc]
        rw [heq]
        exact sum_one_ge2_outside_Zbig_le P ω hG hsum hTlo hTcut hF_le_mid hTbig hBmid hm_lt_J hL_le_F a b
      have hT4 : (∑ z ∈ Zc, if d b z = 1 ∧ 2 ≤ d a z then u b z * u a z else 0) ≤ O12_bound + D_bound := by
        rw [← Finset.sum_filter]
        have heq : Zc.filter (fun z => d b z = 1 ∧ 2 ≤ d a z) =
            Finset.univ.filter (fun z => z ∉ Zbig P ω A c ∧ d b z = 1 ∧ 2 ≤ d a z) := by ext z; simp [Zc]
        rw [heq]
        exact sum_one_ge2_outside_Zbig_le P ω hG hsum hTlo hTcut hF_le_mid hTbig hBmid hm_lt_J hL_le_F b a
      have hT5 : (∑ z ∈ Zc, if d a z = 1 ∧ d b z = 1 then u a z * u b z else 0) ≤ O11_bound := by
        rw [← Finset.sum_filter]
        have hsub : Zc.filter (fun z => d a z = 1 ∧ d b z = 1) ⊆
            Finset.univ.filter (fun z => d a z = 1 ∧ d b z = 1) := by
          intro z hz; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩
        refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hgt
        · exact sum_one_one_le P ω hG.2.2.2.2 hsum h2k hBcross hL_le_F hlt
        · have heq : Finset.univ.filter (fun z => d a z = 1 ∧ d b z = 1) =
              Finset.univ.filter (fun z => d b z = 1 ∧ d a z = 1) := by ext z; simp [and_comm]
          rw [heq]
          calc ∑ z ∈ Finset.univ.filter (fun z => d b z = 1 ∧ d a z = 1), u a z * u b z
              = ∑ z ∈ Finset.univ.filter (fun z => d b z = 1 ∧ d a z = 1), u b z * u a z :=
                Finset.sum_congr rfl fun _ _ => mul_comm _ _
            _ ≤ O11_bound := sum_one_one_le P ω hG.2.2.2.2 hsum h2k hBcross hL_le_F hgt
      linarith
  calc ∑ z ∈ Zc, ∑ r₁ ∈ A.filter (fun r => (graphOf ω).Adj z r),
        ∑ r₂ ∈ (A.filter (fun r => (graphOf ω).Adj z r)).erase r₁, ((c r₁ : ℝ) * (c r₂ : ℝ))
      ≤ ∑ z ∈ Zc, 4 * ∑ a : Fin P.L, ∑ b : Fin P.L,
          if a = b then (if 2 ≤ d a z then (u a z) ^ 2 else 0) else u a z * u b z :=
        Finset.sum_le_sum fun z _ => hpt z
    _ = 4 * ∑ a : Fin P.L, ∑ b : Fin P.L, ∑ z ∈ Zc,
          if a = b then (if 2 ≤ d a z then (u a z) ^ 2 else 0) else u a z * u b z := by
        rw [← Finset.mul_sum]; congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ ≤ 4 * ∑ _a : Fin P.L, ∑ _b : Fin P.L, (4 * D_bound + 2 * O12_bound + O11_bound) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpair_ab a b) (by norm_num)
    _ = errOut P F_max := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, errOut,
          D_bound, O12_bound, O11_bound]
        ring

/-- Weighted sum over any subset `Z : Finset (Fin P.m)` using `GoodMaxCodeg`:
`∑_{z ∈ Z} W_z ≤ (∑_{r ∈ A} c r) + F_max * |Z|^2 * C_codeg`. -/
lemma sum_weight_over_Z_le (P : RegParams) (ω : EdgeIdx P.m → Bool)
    (hCodeg : GoodMaxCodeg P ω) {A Z : Finset (Fin P.m)} {c : Fin P.m → ℕ} {F_max : ℝ}
    (hc_le : ∀ r ∈ A, (c r : ℝ) ≤ F_max) (hF0 : 0 ≤ F_max) :
    ∑ z ∈ Z, (∑ r ∈ A.filter (fun r => (graphOf ω).Adj z r), (c r : ℝ)) ≤
      (∑ r ∈ A, (c r : ℝ)) + F_max * ((Z.card : ℝ) ^ 2) * (P.C_codeg : ℝ) := by
  have hswap : ∑ z ∈ Z, (∑ r ∈ A.filter (fun r => (graphOf ω).Adj z r), (c r : ℝ)) =
      ∑ r ∈ A, (c r : ℝ) * (degIn (graphOf ω) Z r : ℝ) := by
    have h1 : ∀ z ∈ Z, ∑ r ∈ A.filter (fun r => (graphOf ω).Adj z r), (c r : ℝ) =
        ∑ r ∈ A, if (graphOf ω).Adj z r then (c r : ℝ) else 0 := fun _ _ => Finset.sum_filter _ _
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    have h2 : ∑ z ∈ Z, (if (graphOf ω).Adj z r then (c r : ℝ) else 0) =
        ∑ z ∈ Z.filter (fun z => (graphOf ω).Adj r z), (c r : ℝ) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun z _ => ?_
      by_cases hadj : (graphOf ω).Adj z r
      · simp [hadj, hadj.symm]
      · have hnot : ¬ (graphOf ω).Adj r z := fun h => hadj h.symm
        simp [hadj, hnot]
    rw [h2, Finset.sum_const, nsmul_eq_mul, mul_comm]; rfl
  rw [hswap]
  -- Split r ∈ A by deg(r, Z) ≤ 1 vs deg(r, Z) ≥ 2: for d ≥ 2, d ≤ d * (d - 1)
  have hpt : ∀ r ∈ A, (c r : ℝ) * (degIn (graphOf ω) Z r : ℝ) ≤
      (c r : ℝ) + F_max * ((degIn (graphOf ω) Z r * (degIn (graphOf ω) Z r - 1) : ℕ) : ℝ) := by
    intro r hr
    set d := degIn (graphOf ω) Z r
    by_cases hd : d ≤ 1
    · have hd_le1 : (d : ℝ) ≤ 1 := by exact_mod_cast hd
      have h1 : (c r : ℝ) * (d : ℝ) ≤ (c r : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) (c r)]
      have h2 : 0 ≤ F_max * ((d * (d - 1) : ℕ) : ℝ) := by positivity
      linarith
    · have hdd : d ≤ d * (d - 1) := by
        have hd2 : 2 ≤ d := by omega
        calc d = d * 1 := (mul_one d).symm
          _ ≤ d * (d - 1) := Nat.mul_le_mul_left d (by omega)
      have hdd_real : (d : ℝ) ≤ ((d * (d - 1) : ℕ) : ℝ) := by exact_mod_cast hdd
      have hmul : (c r : ℝ) * (d : ℝ) ≤ F_max * ((d * (d - 1) : ℕ) : ℝ) :=
        mul_le_mul (hc_le r hr) hdd_real (Nat.cast_nonneg _) hF0
      linarith [Nat.cast_nonneg (α := ℝ) (c r)]
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc F_max]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hF0)
  -- ∑_{r ∈ A} deg(r, Z) * (deg(r, Z) - 1) = ∑_{z₁ ∈ Z} ∑_{z₂ ∈ Z.erase z₁} |{r ∈ A | z₁ ~ r ∧ z₂ ~ r}| ≤ |Z|^2 * C_codeg
  have hcount : ∑ r ∈ A, degIn (graphOf ω) Z r * (degIn (graphOf ω) Z r - 1) =
      ∑ z₁ ∈ Z, ∑ z₂ ∈ Z.erase z₁, (A.filter fun r => (graphOf ω).Adj z₁ r ∧ (graphOf ω).Adj z₂ r).card := by
    have hL : ∀ r ∈ A, degIn (graphOf ω) Z r * (degIn (graphOf ω) Z r - 1) =
        ∑ z₁ ∈ Z, ∑ z₂ ∈ Z.erase z₁, if (graphOf ω).Adj z₁ r ∧ (graphOf ω).Adj z₂ r then 1 else 0 := by
      intro r _
      set Nz := Z.filter fun z => (graphOf ω).Adj r z
      have h1 : ∑ z₁ ∈ Z, ∑ z₂ ∈ Z.erase z₁,
          (if (graphOf ω).Adj z₁ r ∧ (graphOf ω).Adj z₂ r then 1 else 0) =
          ∑ z₁ ∈ Nz, (Nz.erase z₁).card := by
        have hstep : ∀ z₁ ∈ Z,
            (∑ z₂ ∈ Z.erase z₁, if (graphOf ω).Adj z₁ r ∧ (graphOf ω).Adj z₂ r then 1 else 0) =
            if (graphOf ω).Adj r z₁ then (Nz.erase z₁).card else 0 := by
          intro z₁ _
          by_cases h1 : (graphOf ω).Adj r z₁
          · rw [if_pos h1]
            have hsym : (graphOf ω).Adj z₁ r := h1.symm
            have heq : (Z.erase z₁).filter (fun z₂ => (graphOf ω).Adj z₁ r ∧ (graphOf ω).Adj z₂ r) =
                Nz.erase z₁ := by
              ext z₂; simp only [Finset.mem_filter, Finset.mem_erase, Nz, hsym, true_and]
              exact ⟨fun ⟨⟨hne, hzZ⟩, hadj⟩ => ⟨hne, hzZ, hadj.symm⟩,
                fun ⟨hne, hzZ, hadj⟩ => ⟨⟨hne, hzZ⟩, hadj.symm⟩⟩
            rw [← Finset.card_filter, heq]
          · rw [if_neg h1]
            have hsym : ¬ (graphOf ω).Adj z₁ r := fun h => h1 h.symm
            exact Finset.sum_eq_zero fun _ _ => if_neg (fun h => hsym h.1)
        calc ∑ z₁ ∈ Z, ∑ z₂ ∈ Z.erase z₁, (if (graphOf ω).Adj z₁ r ∧ (graphOf ω).Adj z₂ r then 1 else 0)
            = ∑ z₁ ∈ Z, (if (graphOf ω).Adj r z₁ then (Nz.erase z₁).card else 0) :=
              Finset.sum_congr rfl hstep
          _ = ∑ z₁ ∈ Nz, (Nz.erase z₁).card := (Finset.sum_filter _ _).symm
      rw [h1]
      calc degIn (graphOf ω) Z r * (degIn (graphOf ω) Z r - 1)
          = ∑ _z₁ ∈ Nz, (Nz.card - 1) := by rw [Finset.sum_const, smul_eq_mul]; rfl
        _ = ∑ z₁ ∈ Nz, (Nz.erase z₁).card :=
            Finset.sum_congr rfl fun z₁ hz1 => (Finset.card_erase_of_mem hz1).symm
    rw [Finset.sum_congr rfl hL, Finset.sum_comm]
    refine Finset.sum_congr rfl fun z₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z₂ _ => ?_
    simp
  have hle_nat : ∑ r ∈ A, degIn (graphOf ω) Z r * (degIn (graphOf ω) Z r - 1) ≤
      Z.card ^ 2 * P.C_codeg := by
    rw [hcount]
    calc ∑ z₁ ∈ Z, ∑ z₂ ∈ Z.erase z₁, (A.filter fun r => (graphOf ω).Adj z₁ r ∧ (graphOf ω).Adj z₂ r).card
        ≤ ∑ z₁ ∈ Z, ∑ _z₂ ∈ Z.erase z₁, P.C_codeg := by
          refine Finset.sum_le_sum fun z₁ _ => Finset.sum_le_sum fun z₂ hz2 => ?_
          have hne : z₁ ≠ z₂ := (Finset.mem_erase.mp hz2).1.symm
          have hsub : A.filter (fun r => (graphOf ω).Adj z₁ r ∧ (graphOf ω).Adj z₂ r) ⊆
              Finset.univ.filter (fun r => (graphOf ω).Adj z₁ r ∧ (graphOf ω).Adj z₂ r) :=
            Finset.filter_subset_filter _ (Finset.subset_univ _)
          exact (Finset.card_le_card hsub).trans (hCodeg z₁ z₂ hne).le
      _ ≤ ∑ _z₁ ∈ Z, (Z.card * P.C_codeg) := by
          refine Finset.sum_le_sum fun z₁ _ => ?_
          rw [Finset.sum_const, smul_eq_mul]
          exact Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.erase_subset _ _))
      _ = Z.card ^ 2 * P.C_codeg := by
          rw [Finset.sum_const, smul_eq_mul, ← mul_assoc, sq]
  rw [← Nat.cast_sum]
  exact_mod_cast hle_nat

/-- Convexity squared-sum bound on `Z`: if `0 ≤ W z ≤ D` for all `z ∈ Z` and `∑_{z ∈ Z} W z ≤ S`,
then `∑_{z ∈ Z} W z ^ 2 ≤ min (S ^ 2) (D * S)`. -/
lemma sum_sq_le_min_sq_mul {ι : Type*} (Z : Finset ι) (W : ι → ℝ) {D S : ℝ}
    (hW0 : ∀ z ∈ Z, 0 ≤ W z) (hWD : ∀ z ∈ Z, W z ≤ D) (hsum : ∑ z ∈ Z, W z ≤ S) (hD0 : 0 ≤ D) :
    ∑ z ∈ Z, W z ^ 2 ≤ min (S ^ 2) (D * S) := by
  have hsum0 : 0 ≤ ∑ z ∈ Z, W z := Finset.sum_nonneg hW0
  refine le_min ?_ ?_
  · calc ∑ z ∈ Z, W z ^ 2
        ≤ ∑ z ∈ Z, W z * (∑ y ∈ Z, W y) := by
          refine Finset.sum_le_sum fun z hz => ?_
          rw [sq]
          exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hW0 hz) (hW0 z hz)
      _ = (∑ z ∈ Z, W z) ^ 2 := by rw [← Finset.sum_mul, sq]
      _ ≤ S ^ 2 := by nlinarith
  · calc ∑ z ∈ Z, W z ^ 2
        ≤ ∑ z ∈ Z, D * W z := by
          refine Finset.sum_le_sum fun z hz => ?_
          rw [sq]; exact mul_le_mul_of_nonneg_right (hWD z hz) (hW0 z hz)
      _ = D * ∑ z ∈ Z, W z := (Finset.mul_sum _ _ _).symm
      _ ≤ D * S := mul_le_mul_of_nonneg_left hsum hD0

/-- Unweighted degree-square bound for `A : Finset (Fin P.m)` with `A.card ≤ P.k`:
`∑ z, degIn (graphOf ω) A z * (degIn (graphOf ω) A z - 1) ≤ errOut P F_max + ((1 + η₀) * m * p) * (k + |Zbig(A,1)|^2 * C_codeg)`. -/
lemma sum_degIn_choose2_le (P : RegParams) (ω : EdgeIdx P.m → Bool)
    (hG : GoodGraph P ω) {A : Finset (Fin P.m)} {F_max : ℝ}
    (hAcard : A.card ≤ P.k) (h2k : 2 * P.k ≤ P.m) (hL1 : 1 ≤ P.L)
    (hTlo : 0 < P.T_lo) (hTcut : P.T_lo ≤ P.T_cut) (hF_le_mid : F_max ≤ P.T_mid)
    (hTbig : 0 < P.T_big) (hTmid_lt : P.T_mid < P.T_big / 2)
    (hTbig_lt_J : P.T_big < ((2 ^ P.J : ℕ) : ℝ))
    (hBmid : 0 < P.B_mid) (hBcross : 0 < P.B_cross)
    (hm_lt_J : P.m < 2 ^ P.J)
    (hL_le_F : ∀ i : Fin P.L, ((2 ^ i.val : ℕ) : ℝ) ≤ F_max)
    (hL_le_Tbig : ∀ i : Fin P.L, ((2 ^ i.val : ℕ) : ℝ) ≤ P.T_big) :
    ∑ z : Fin P.m, ((degIn (graphOf ω) A z * (degIn (graphOf ω) A z - 1) : ℕ) : ℝ) ≤
      errOut P F_max +
      ((1 + P.η₀) * ((P.m : ℝ) * P.p)) *
        ((P.k : ℝ) + ((P.L : ℝ) * (240 * (P.k : ℝ) / P.T_big + 4)) ^ 2 * (P.C_codeg : ℝ)) := by
  let c1 : Fin P.m → ℕ := fun r => if r ∈ A then 1 else 0
  have hsum1 : ∑ r ∈ A, c1 r ≤ P.k := by
    have : ∑ r ∈ A, c1 r = A.card := by simp [c1]
    omega
  have hc1_lt : ∀ r ∈ A, c1 r < 2 ^ P.L := fun r hr => by
    have : 2 ≤ 2 ^ P.L := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ P.L := Nat.pow_le_pow_right (by omega) hL1
    simp [c1, hr]; omega
  set Z := Zbig P ω A c1
  have hdeg_eq : ∀ z : Fin P.m,
      ((degIn (graphOf ω) A z * (degIn (graphOf ω) A z - 1) : ℕ) : ℝ) =
      ∑ r₁ ∈ A.filter (fun r => (graphOf ω).Adj z r),
      ∑ r₂ ∈ (A.filter (fun r => (graphOf ω).Adj z r)).erase r₁, ((c1 r₁ : ℝ) * (c1 r₂ : ℝ)) := by
    intro z
    set N := A.filter fun r => (graphOf ω).Adj z r
    have h1 : ∀ r₁ ∈ N, ∑ r₂ ∈ N.erase r₁, ((c1 r₁ : ℝ) * (c1 r₂ : ℝ)) = ((N.card - 1 : ℕ) : ℝ) := by
      intro r₁ hr1
      have hr1A : r₁ ∈ A := (Finset.mem_filter.mp hr1).1
      calc ∑ r₂ ∈ N.erase r₁, ((c1 r₁ : ℝ) * (c1 r₂ : ℝ))
          = ∑ _r₂ ∈ N.erase r₁, (1 : ℝ) := by
            refine Finset.sum_congr rfl fun r₂ hr2 => ?_
            have hr2A : r₂ ∈ A := (Finset.mem_filter.mp (Finset.mem_erase.mp hr2).2).1
            simp [c1, hr1A, hr2A]
        _ = ((N.erase r₁).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ = ((N.card - 1 : ℕ) : ℝ) := by rw [Finset.card_erase_of_mem hr1]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, Nat.cast_mul]; rfl
  have hsplit : ∑ z : Fin P.m, ((degIn (graphOf ω) A z * (degIn (graphOf ω) A z - 1) : ℕ) : ℝ) =
      (∑ z ∈ Finset.univ.filter (fun z => z ∉ Z),
        ((degIn (graphOf ω) A z * (degIn (graphOf ω) A z - 1) : ℕ) : ℝ)) +
      (∑ z ∈ Finset.univ.filter (fun z => z ∈ Z),
        ((degIn (graphOf ω) A z * (degIn (graphOf ω) A z - 1) : ℕ) : ℝ)) := by
    have := (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin P.m))
      (fun z => z ∈ Z) (fun z => ((degIn (graphOf ω) A z * (degIn (graphOf ω) A z - 1) : ℕ) : ℝ))).symm
    linarith
  have hout : ∑ z ∈ Finset.univ.filter (fun z => z ∉ Z),
      ((degIn (graphOf ω) A z * (degIn (graphOf ω) A z - 1) : ℕ) : ℝ) ≤ errOut P F_max := by
    simp_rw [hdeg_eq]
    exact sum_weighted_pairs_outside_Zbig_le P ω hG hsum1 h2k hc1_lt hTlo hTcut hF_le_mid hTbig
      hBmid hBcross hm_lt_J hL_le_F
  have hin : ∑ z ∈ Finset.univ.filter (fun z => z ∈ Z),
      ((degIn (graphOf ω) A z * (degIn (graphOf ω) A z - 1) : ℕ) : ℝ) ≤
      ((1 + P.η₀) * ((P.m : ℝ) * P.p)) *
        ((P.k : ℝ) + ((P.L : ℝ) * (240 * (P.k : ℝ) / P.T_big + 4)) ^ 2 * (P.C_codeg : ℝ)) := by
    have hZeq : Finset.univ.filter (fun z : Fin P.m => z ∈ Z) = Z := by ext z; simp
    rw [hZeq]
    have hdeg_nn : 0 ≤ (1 + P.η₀) * ((P.m : ℝ) * P.p) := by
      by_cases hm : 0 < P.m
      · exact le_trans (Nat.cast_nonneg _) (hG.1 ⟨0, hm⟩)
      · have hm0 : P.m = 0 := by omega
        simp [hm0]
    have hle1 : ∑ z ∈ Z, ((degIn (graphOf ω) A z * (degIn (graphOf ω) A z - 1) : ℕ) : ℝ) ≤
        ((1 + P.η₀) * ((P.m : ℝ) * P.p)) * ∑ z ∈ Z, (degIn (graphOf ω) A z : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun z _ => ?_
      have hd_le_all : (degIn (graphOf ω) A z : ℝ) ≤ (1 + P.η₀) * ((P.m : ℝ) * P.p) :=
        le_trans (by exact_mod_cast degIn_mono (graphOf ω) (Finset.subset_univ A) z) (hG.1 z)
      have hdsub : ((degIn (graphOf ω) A z - 1 : ℕ) : ℝ) ≤ (degIn (graphOf ω) A z : ℝ) := by
        exact_mod_cast Nat.sub_le _ 1
      rw [Nat.cast_mul]
      calc (degIn (graphOf ω) A z : ℝ) * ((degIn (graphOf ω) A z - 1 : ℕ) : ℝ)
          ≤ (degIn (graphOf ω) A z : ℝ) * (degIn (graphOf ω) A z : ℝ) :=
            mul_le_mul_of_nonneg_left hdsub (Nat.cast_nonneg _)
        _ ≤ ((1 + P.η₀) * ((P.m : ℝ) * P.p)) * (degIn (graphOf ω) A z : ℝ) :=
            mul_le_mul_of_nonneg_right hd_le_all (Nat.cast_nonneg _)
    have hZcard := card_Zbig_le P ω hG.2.2.2.1 hsum1 hTbig hTmid_lt hTbig_lt_J hL_le_Tbig
    have hsumZ := sum_weight_over_Z_le P ω hG.2.1 (A := A) (Z := Z) (c := c1) (F_max := 1)
      (fun r hr => by simp [c1, hr]) (by norm_num)
    have hW_eq : ∀ z ∈ Z, (∑ r ∈ A.filter (fun r => (graphOf ω).Adj z r), (c1 r : ℝ)) =
        (degIn (graphOf ω) A z : ℝ) := fun z _ => by
      calc ∑ r ∈ A.filter (fun r => (graphOf ω).Adj z r), (c1 r : ℝ)
          = ∑ _r ∈ A.filter (fun r => (graphOf ω).Adj z r), (1 : ℝ) :=
            Finset.sum_congr rfl fun r hr => by simp [c1, (Finset.mem_filter.mp hr).1]
        _ = (degIn (graphOf ω) A z : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]; rfl
    rw [Finset.sum_congr rfl hW_eq] at hsumZ
    have hc1_sum : (∑ r ∈ A, (c1 r : ℝ)) ≤ (P.k : ℝ) := by exact_mod_cast hsum1
    have hZsq : (Z.card : ℝ) ^ 2 ≤ ((P.L : ℝ) * (240 * (P.k : ℝ) / P.T_big + 4)) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) Z.card]
    have hsumZ' : ∑ z ∈ Z, (degIn (graphOf ω) A z : ℝ) ≤
        (P.k : ℝ) + ((P.L : ℝ) * (240 * (P.k : ℝ) / P.T_big + 4)) ^ 2 * (P.C_codeg : ℝ) := by
      have h1 : (1 : ℝ) * (Z.card : ℝ) ^ 2 * (P.C_codeg : ℝ) ≤
          ((P.L : ℝ) * (240 * (P.k : ℝ) / P.T_big + 4)) ^ 2 * (P.C_codeg : ℝ) := by
        rw [one_mul]; exact mul_le_mul_of_nonneg_right hZsq (Nat.cast_nonneg _)
      linarith
    exact hle1.trans (mul_le_mul_of_nonneg_left hsumZ' hdeg_nn)
  linarith

end WeightedTwoPaths

/- ### Section 3: Stage-1 / Stage-2 Joint Red-Blue Survival Bound -/

section JointIndepBound

/-- Coordinate split of `EdgeIdx m` into interior pairs on `S : Finset (Fin m)` (preserving
the `Fin m` vertex order via `S.orderIsoOfFin rfl`) and exterior pairs touching `Sᶜ`. -/
noncomputable def edgeSplitSub {m : ℕ} (S : Finset (Fin m)) :
    EdgeIdx m ≃ EdgeIdx S.card ⊕ { e : EdgeIdx m // ¬ (e.1.1 ∈ S ∧ e.1.2 ∈ S) } :=
  let eS : Fin S.card ≃o S := S.orderIsoOfFin rfl
  { toFun := fun e =>
      if h : e.1.1 ∈ S ∧ e.1.2 ∈ S then
        Sum.inl ⟨(eS.symm ⟨e.1.1, h.1⟩, eS.symm ⟨e.1.2, h.2⟩), by
          have hlt : (⟨e.1.1, h.1⟩ : S) < ⟨e.1.2, h.2⟩ := e.2
          exact eS.symm.strictMono hlt⟩
      else Sum.inr ⟨e, h⟩
    invFun := fun x =>
      Sum.casesOn x
        (fun e => ⟨((eS e.1.1).1, (eS e.1.2).1), eS.strictMono e.2⟩)
        Subtype.val
    left_inv := fun e => by
      dsimp only
      split_ifs with h
      · apply Subtype.ext; apply Prod.ext
        · exact congrArg Subtype.val (eS.apply_symm_apply ⟨e.1.1, h.1⟩)
        · exact congrArg Subtype.val (eS.apply_symm_apply ⟨e.1.2, h.2⟩)
      · rfl
    right_inv := fun x => by
      rcases x with e | ⟨e, he⟩
      · dsimp only
        have hmem : (eS e.1.1).1 ∈ S ∧ (eS e.1.2).1 ∈ S := ⟨(eS e.1.1).2, (eS e.1.2).2⟩
        rw [dif_pos hmem]
        apply congrArg Sum.inl; apply Subtype.ext; apply Prod.ext
        · exact eS.symm_apply_apply e.1.1
        · exact eS.symm_apply_apply e.1.2
      · dsimp only; rw [dif_neg he] }

lemma graphOf_edgeSplitSub_int {m : ℕ} (S : Finset (Fin m))
    (ω : EdgeIdx m → Bool) (i j : Fin S.card) :
    let eS := S.orderIsoOfFin rfl
    let ωIn : EdgeIdx S.card → Bool := fun e => ω ((edgeSplitSub S).symm (Sum.inl e))
    (graphOf ω).Adj (eS i).1 (eS j).1 ↔ (graphOf ωIn).Adj i j := by
  intro eS ωIn
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · have hlt' : (eS i).1 < (eS j).1 := eS.strictMono hlt
    simp only [graphOf, dif_pos hlt, dif_pos hlt', ωIn, edgeSplitSub, Equiv.coe_fn_symm_mk, eS]
  · simp [graphOf]
  · have hgt' : (eS j).1 < (eS i).1 := eS.strictMono hgt
    have hnot : ¬ i < j := lt_asymm hgt
    have hnot' : ¬ (eS i).1 < (eS j).1 := lt_asymm hgt'
    simp only [graphOf, dif_neg hnot, dif_pos hgt, dif_neg hnot', dif_pos hgt',
      ωIn, edgeSplitSub, Equiv.coe_fn_symm_mk, eS]

lemma graphOf_edgeSplitSub_ext {m : ℕ} (S : Finset (Fin m))
    (ω₁ ω₂ : EdgeIdx m → Bool)
    (hext : ∀ x : { e : EdgeIdx m // ¬ (e.1.1 ∈ S ∧ e.1.2 ∈ S) },
      ω₁ x.1 = ω₂ x.1)
    {u v : Fin m} (hnot : ¬ (u ∈ S ∧ v ∈ S)) :
    (graphOf ω₁).Adj u v ↔ (graphOf ω₂).Adj u v := by
  rcases lt_trichotomy u v with hlt | rfl | hgt
  · simp only [graphOf, dif_pos hlt]
    rw [hext ⟨⟨(u, v), hlt⟩, hnot⟩]
  · simp [graphOf]
  · have hnot' : ¬ (v ∈ S ∧ u ∈ S) := fun h => hnot ⟨h.2, h.1⟩
    have hnotlt : ¬ u < v := lt_asymm hgt
    simp only [graphOf, dif_neg hnotlt, dif_pos hgt]
    rw [hext ⟨⟨(v, u), hgt⟩, hnot'⟩]

/-- If `e = (i, j) : EdgeIdx S.card` has no common neighbor outside `S` in `graphOf ω` and
survives interior `pruneTri` in `ωIn`, then `(eS i, eS j)` survives `pruneTri (graphOf ω)`. -/
lemma pruneTri_of_int_no_ext {m : ℕ} (S : Finset (Fin m)) (ω : EdgeIdx m → Bool)
    {i j : Fin S.card} (hij : i < j)
    (hno_ext : ¬ ∃ z : Fin m, z ∉ S ∧ (graphOf ω).Adj z (S.orderIsoOfFin rfl i).1 ∧
        (graphOf ω).Adj z (S.orderIsoOfFin rfl j).1)
    (hprune_in : (pruneTri (graphOf (fun e => ω ((edgeSplitSub S).symm (Sum.inl e))))).Adj i j) :
    (pruneTri (graphOf ω)).Adj (S.orderIsoOfFin rfl i).1 (S.orderIsoOfFin rfl j).1 := by
  set eS := S.orderIsoOfFin rfl
  refine ⟨(graphOf_edgeSplitSub_int S ω i j).mpr hprune_in.1, ?_⟩
  rintro ⟨z, hz, hzi, hzj⟩
  by_cases hzS : z ∈ S
  · let r : Fin S.card := eS.symm ⟨z, hzS⟩
    have hrz : (eS r).1 = z := congrArg Subtype.val (eS.apply_symm_apply ⟨z, hzS⟩)
    have hri : r < i := by
      have hmin : min (eS i).1 (eS j).1 = (eS i).1 := min_eq_left (eS.strictMono hij).le
      rw [hmin] at hz
      have hltS : (⟨z, hzS⟩ : S) < eS i := hz
      have := eS.symm.strictMono hltS
      simpa [r] using this
    have hrj : r < j := lt_trans hri hij
    have h1 : (graphOf (fun e => ω ((edgeSplitSub S).symm (Sum.inl e)))).Adj r i :=
      (graphOf_edgeSplitSub_int S ω r i).mp (by rwa [hrz])
    have h2 : (graphOf (fun e => ω ((edgeSplitSub S).symm (Sum.inl e)))).Adj r j :=
      (graphOf_edgeSplitSub_int S ω r j).mp (by rwa [hrz])
    exact hprune_in.2 ⟨r, lt_min hri hrj, h1, h2⟩
  · exact hno_ext ⟨z, hzS, hzi, hzj⟩

/-- Pure Stage-2 five-event survival bound on `(EdgeIdx sR ⊕ EdgeIdx sB) → Bool`. -/
lemma bernProb_stage2_five_events {sR sB : ℕ} {p M_target T_small M_mix lam₁ lam₂ : ℝ} {M_tri : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hlam1 : 0 < lam₁) (hlam2 : 0 < lam₂) (hTsmall : 0 < T_small)
    (hMmix : 0 ≤ M_mix)
    (openR : Finset (EdgeIdx sR)) (openB : Finset (EdgeIdx sB))
    (hopen : M_target ≤ (openR.card : ℝ) + (openB.card : ℝ))
    (KR : (EdgeIdx sB → Bool) → Finset (EdgeIdx sR))
    (KB : (EdgeIdx sR → Bool) → Finset (EdgeIdx sB)) :
    bernProb p (fun ω : EdgeIdx sR ⊕ EdgeIdx sB → Bool =>
      let ωR := fun e => ω (Sum.inl e)
      let ωB := fun e => ω (Sum.inr e)
      (∀ e ∈ openR, ωR e = true → ¬ (pruneTri (graphOf ωR)).Adj e.1.1 e.1.2 ∨ e ∈ KR ωB) ∧
      (∀ e ∈ openB, ωB e = true → ¬ (pruneTri (graphOf ωB)).Adj e.1.1 e.1.2 ∨ e ∈ KB ωR) ∧
      ((KR ωB).card : ℝ) ≤ M_mix ∧ ((KB ωR).card : ℝ) ≤ M_mix ∧
      (∑ i : Fin sR, (triCand ωR i).card ≤ M_tri) ∧
      (∑ i : Fin sB, (triCand ωB i).card ≤ M_tri)) ≤
    Real.exp (2 * lam₁ * T_small - p * (1 - Real.exp (-lam₁)) * M_target) +
    2 * (Real.exp 1 * M_mix * p / (⌈T_small / 2⌉₊ : ℝ)) ^ ⌈T_small / 2⌉₊ +
    2 * Real.exp ((Real.exp lam₂ - 1) * p * (M_tri : ℝ) - lam₂ * (T_small / 2)) := by
  set h : ℕ := ⌈T_small / 2⌉₊
  have hh1 : 1 ≤ h := Nat.ceil_pos.mpr (by linarith)
  have hh_ge : T_small / 2 ≤ (h : ℝ) := Nat.le_ceil _
  let E1 : (EdgeIdx sR ⊕ EdgeIdx sB → Bool) → Prop := fun ω =>
    ((openR.filter fun e => ω (Sum.inl e) = true).card : ℝ) ≤ T_small ∧
    ((openB.filter fun e => ω (Sum.inr e) = true).card : ℝ) ≤ T_small
  let E2 : (EdgeIdx sR ⊕ EdgeIdx sB → Bool) → Prop := fun ω =>
    let ωR := fun e => ω (Sum.inl e)
    let ωB := fun e => ω (Sum.inr e)
    ((KR ωB).card : ℝ) ≤ M_mix ∧ h ≤ ((KR ωB).filter fun e => ωR e = true).card
  let E3 : (EdgeIdx sR ⊕ EdgeIdx sB → Bool) → Prop := fun ω =>
    let ωR := fun e => ω (Sum.inl e)
    let ωB := fun e => ω (Sum.inr e)
    ((KB ωR).card : ℝ) ≤ M_mix ∧ h ≤ ((KB ωR).filter fun e => ωB e = true).card
  let E4 : (EdgeIdx sR ⊕ EdgeIdx sB → Bool) → Prop := fun ω =>
    let ωR := fun e => ω (Sum.inl e)
    (∑ i : Fin sR, (triCand ωR i).card ≤ M_tri) ∧
    T_small / 2 ≤ ((∑ i : Fin sR, (triHits ωR i).card : ℕ) : ℝ)
  let E5 : (EdgeIdx sR ⊕ EdgeIdx sB → Bool) → Prop := fun ω =>
    let ωB := fun e => ω (Sum.inr e)
    (∑ i : Fin sB, (triCand ωB i).card ≤ M_tri) ∧
    T_small / 2 ≤ ((∑ i : Fin sB, (triHits ωB i).card : ℕ) : ℝ)
  have hcov : ∀ ω : EdgeIdx sR ⊕ EdgeIdx sB → Bool,
      ((∀ e ∈ openR, ω (Sum.inl e) = true →
          ¬ (pruneTri (graphOf (fun e => ω (Sum.inl e)))).Adj e.1.1 e.1.2 ∨ e ∈ KR (fun e => ω (Sum.inr e))) ∧
       (∀ e ∈ openB, ω (Sum.inr e) = true →
          ¬ (pruneTri (graphOf (fun e => ω (Sum.inr e)))).Adj e.1.1 e.1.2 ∨ e ∈ KB (fun e => ω (Sum.inl e))) ∧
       ((KR (fun e => ω (Sum.inr e))).card : ℝ) ≤ M_mix ∧
       ((KB (fun e => ω (Sum.inl e))).card : ℝ) ≤ M_mix ∧
       (∑ i : Fin sR, (triCand (fun e => ω (Sum.inl e)) i).card ≤ M_tri) ∧
       (∑ i : Fin sB, (triCand (fun e => ω (Sum.inr e)) i).card ≤ M_tri)) →
      E1 ω ∨ (E2 ω ∨ (E3 ω ∨ (E4 ω ∨ E5 ω))) := by
    intro ω ⟨hR, hB, hKRm, hKBm, htriR, htriB⟩
    set ωR := fun e => ω (Sum.inl e)
    set ωB := fun e => ω (Sum.inr e)
    by_cases h1 : E1 ω
    · exact Or.inl h1
    · right
      have hgt : T_small < ((openR.filter fun e => ωR e = true).card : ℝ) ∨
          T_small < ((openB.filter fun e => ωB e = true).card : ℝ) := by
        dsimp only [E1] at h1
        rw [not_and_or, not_le, not_le] at h1
        exact h1
      rcases hgt with hgtR | hgtB
      · have hsub : openR.filter (fun e => ωR e = true) ⊆
            (Finset.univ.filter fun e : EdgeIdx sR =>
              ωR e = true ∧ ¬ (pruneTri (graphOf ωR)).Adj e.1.1 e.1.2) ∪
            ((KR ωB).filter fun e => ωR e = true) := by
          intro e he
          rcases Finset.mem_filter.mp he with ⟨heO, ht⟩
          rcases hR e heO ht with hkill | hmix
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, hkill⟩)
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hmix, ht⟩)
        have hsum_le : ((openR.filter fun e => ωR e = true).card : ℝ) ≤
            ((∑ i : Fin sR, (triHits ωR i).card : ℕ) : ℝ) +
            (((KR ωB).filter fun e => ωR e = true).card : ℝ) := by
          have h1' := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
          have h2' := card_triPruned_edges_le_sum_triHits ωR
          have hnat : (openR.filter fun e => ωR e = true).card ≤
              (∑ i : Fin sR, (triHits ωR i).card) + ((KR ωB).filter fun e => ωR e = true).card := by omega
          exact_mod_cast hnat
        by_cases htri : T_small / 2 ≤ ((∑ i : Fin sR, (triHits ωR i).card : ℕ) : ℝ)
        · exact Or.inr (Or.inr (Or.inl ⟨htriR, htri⟩))
        · have hmix_ge : T_small / 2 ≤ (((KR ωB).filter fun e => ωR e = true).card : ℝ) := by linarith
          have hmix_h : h ≤ ((KR ωB).filter fun e => ωR e = true).card := Nat.ceil_le.mpr hmix_ge
          exact Or.inl ⟨hKRm, hmix_h⟩
      · have hsub : openB.filter (fun e => ωB e = true) ⊆
            (Finset.univ.filter fun e : EdgeIdx sB =>
              ωB e = true ∧ ¬ (pruneTri (graphOf ωB)).Adj e.1.1 e.1.2) ∪
            ((KB ωR).filter fun e => ωB e = true) := by
          intro e he
          rcases Finset.mem_filter.mp he with ⟨heO, ht⟩
          rcases hB e heO ht with hkill | hmix
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, hkill⟩)
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hmix, ht⟩)
        have hsum_le : ((openB.filter fun e => ωB e = true).card : ℝ) ≤
            ((∑ i : Fin sB, (triHits ωB i).card : ℕ) : ℝ) +
            (((KB ωR).filter fun e => ωB e = true).card : ℝ) := by
          have h1' := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
          have h2' := card_triPruned_edges_le_sum_triHits ωB
          have hnat : (openB.filter fun e => ωB e = true).card ≤
              (∑ i : Fin sB, (triHits ωB i).card) + ((KB ωR).filter fun e => ωB e = true).card := by omega
          exact_mod_cast hnat
        by_cases htri : T_small / 2 ≤ ((∑ i : Fin sB, (triHits ωB i).card : ℕ) : ℝ)
        · exact Or.inr (Or.inr (Or.inr ⟨htriB, htri⟩))
        · have hmix_ge : T_small / 2 ≤ (((KB ωR).filter fun e => ωB e = true).card : ℝ) := by linarith
          have hmix_h : h ≤ ((KB ωR).filter fun e => ωB e = true).card := Nat.ceil_le.mpr hmix_ge
          exact Or.inr (Or.inl ⟨hKBm, hmix_h⟩)
  -- Bound each of the 5 events!
  have hP1 : bernProb p E1 ≤ Real.exp (2 * lam₁ * T_small - p * (1 - Real.exp (-lam₁)) * M_target) := by
    dsimp only [E1]
    rw [bernProb_sum_and p
      (fun ωR : EdgeIdx sR → Bool => ((openR.filter fun e => ωR e = true).card : ℝ) ≤ T_small)
      (fun ωB : EdgeIdx sB → Bool => ((openB.filter fun e => ωB e = true).card : ℝ) ≤ T_small)]
    have hR := bernProb_binom_le_mgf (lam := lam₁) (T := T_small) hp0 hp1 hlam1 openR
    have hB := bernProb_binom_le_mgf (lam := lam₁) (T := T_small) hp0 hp1 hlam1 openB
    calc _ ≤ Real.exp (lam₁ * T_small - p * (1 - Real.exp (-lam₁)) * (openR.card : ℝ)) *
            Real.exp (lam₁ * T_small - p * (1 - Real.exp (-lam₁)) * (openB.card : ℝ)) :=
          mul_le_mul hR hB (bernProb_nonneg hp0 hp1 _) (Real.exp_pos _).le
      _ = Real.exp (2 * lam₁ * T_small - p * (1 - Real.exp (-lam₁)) * ((openR.card : ℝ) + (openB.card : ℝ))) := by
          rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (2 * lam₁ * T_small - p * (1 - Real.exp (-lam₁)) * M_target) := by
          refine Real.exp_le_exp.mpr ?_
          have h1me : 0 ≤ 1 - Real.exp (-lam₁) := by
            have : Real.exp (-lam₁) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
            linarith
          have hp_fac : 0 ≤ p * (1 - Real.exp (-lam₁)) := mul_nonneg hp0 h1me
          nlinarith
  have hP2 : bernProb p E2 ≤ (Real.exp 1 * M_mix * p / (h : ℝ)) ^ h := by
    refine bernProb_sum_cond_le hp0 hp1 (fun ωR ωB =>
      ((KR ωB).card : ℝ) ≤ M_mix ∧ h ≤ ((KR ωB).filter fun e => ωR e = true).card) fun ωB => ?_
    by_cases hM : ((KR ωB).card : ℝ) ≤ M_mix
    · refine (bernProb_mono hp0 hp1 fun _ h' => h'.2).trans ?_
      refine (bernProb_binom_ge_pow hp0 hp1 (KR ωB) hh1).trans ?_
      refine pow_le_pow_left₀ (by positivity) ?_ h
      have hhpos : (0 : ℝ) < (h : ℝ) := Nat.cast_pos.mpr (by omega)
      have hnum : Real.exp 1 * ((KR ωB).card : ℝ) * p ≤ Real.exp 1 * M_mix * p := by
        have : 0 ≤ Real.exp 1 * p := by positivity
        nlinarith
      exact div_le_div_of_nonneg_right hnum hhpos.le
    · have h0 : bernProb p (fun ωR => ((KR ωB).card : ℝ) ≤ M_mix ∧
          h ≤ ((KR ωB).filter fun e => ωR e = true).card) = 0 := by
        simp only [bernProb]; exact Finset.sum_eq_zero fun _ _ => if_neg (fun h' => hM h'.1)
      rw [h0]
      exact pow_nonneg (div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos 1).le hMmix) hp0) (Nat.cast_nonneg _)) h
  have hP3 : bernProb p E3 ≤ (Real.exp 1 * M_mix * p / (h : ℝ)) ^ h := by
    -- Swap the sum to condition on ωR!
    let eSwap : EdgeIdx sB ⊕ EdgeIdx sR ≃ EdgeIdx sR ⊕ EdgeIdx sB := Equiv.sumComm _ _
    rw [bernProb_equiv eSwap p]
    refine bernProb_sum_cond_le hp0 hp1 (fun ωB ωR =>
      ((KB ωR).card : ℝ) ≤ M_mix ∧ h ≤ ((KB ωR).filter fun e => ωB e = true).card) fun ωR => ?_
    by_cases hM : ((KB ωR).card : ℝ) ≤ M_mix
    · refine (bernProb_mono hp0 hp1 fun _ h' => h'.2).trans ?_
      refine (bernProb_binom_ge_pow hp0 hp1 (KB ωR) hh1).trans ?_
      refine pow_le_pow_left₀ (by positivity) ?_ h
      have hhpos : (0 : ℝ) < (h : ℝ) := Nat.cast_pos.mpr (by omega)
      have hnum : Real.exp 1 * ((KB ωR).card : ℝ) * p ≤ Real.exp 1 * M_mix * p := by
        have : 0 ≤ Real.exp 1 * p := by positivity
        nlinarith
      exact div_le_div_of_nonneg_right hnum hhpos.le
    · have h0 : bernProb p (fun ωB => ((KB ωR).card : ℝ) ≤ M_mix ∧
          h ≤ ((KB ωR).filter fun e => ωB e = true).card) = 0 := by
        simp only [bernProb]; exact Finset.sum_eq_zero fun _ _ => if_neg (fun h' => hM h'.1)
      rw [h0]
      exact pow_nonneg (div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos 1).le hMmix) hp0) (Nat.cast_nonneg _)) h
  have hP4 : bernProb p E4 ≤ Real.exp ((Real.exp lam₂ - 1) * p * (M_tri : ℝ) - lam₂ * (T_small / 2)) := by
    refine (bernProb_inl p (fun ωR : EdgeIdx sR → Bool =>
      (∑ i : Fin sR, (triCand ωR i).card ≤ M_tri) ∧
      T_small / 2 ≤ ((∑ i : Fin sR, (triHits ωR i).card : ℕ) : ℝ))).trans_le ?_
    exact bernProb_triKill_le M_tri hp0 hp1 hlam2
  have hP5 : bernProb p E5 ≤ Real.exp ((Real.exp lam₂ - 1) * p * (M_tri : ℝ) - lam₂ * (T_small / 2)) := by
    let eSwap : EdgeIdx sB ⊕ EdgeIdx sR ≃ EdgeIdx sR ⊕ EdgeIdx sB := Equiv.sumComm _ _
    rw [bernProb_equiv eSwap p]
    refine (bernProb_inl p (fun ωB : EdgeIdx sB → Bool =>
      (∑ i : Fin sB, (triCand ωB i).card ≤ M_tri) ∧
      T_small / 2 ≤ ((∑ i : Fin sB, (triHits ωB i).card : ℕ) : ℝ))).trans_le ?_
    exact bernProb_triKill_le M_tri hp0 hp1 hlam2
  -- Combine all 5 events by union bound
  refine (bernProb_mono hp0 hp1 hcov).trans ?_
  have hu1 := bernProb_or_le hp0 hp1 E1 (fun ω => E2 ω ∨ (E3 ω ∨ (E4 ω ∨ E5 ω)))
  have hu2 := bernProb_or_le hp0 hp1 E2 (fun ω => E3 ω ∨ (E4 ω ∨ E5 ω))
  have hu3 := bernProb_or_le hp0 hp1 E3 (fun ω => E4 ω ∨ E5 ω)
  have hu4 := bernProb_or_le hp0 hp1 E4 E5
  linarith

/-- Excess fiber-weight sum bound: picking one representative `repR r ∈ I ∩ φ_R⁻¹(r)` for each
`r ∈ A = φ_R(I)`, the weights `cB j = |{r ∈ A | φ_B (repR r) = j}|` satisfy
`∑ j ∈ B, cB j = a`, `cB j ≤ F_max`, and `∑ j ∈ B, (cB j - 1) ≤ k - b`. -/
lemma rep_weight_bounds {n m : ℕ} {I : Finset (Fin n)} {φ_R φ_B : Fin n → Fin m} {F_max : ℝ}
    (hfibB : ∀ j : Fin m, ((Finset.univ.filter fun v : Fin n => φ_B v = j).card : ℝ) ≤ F_max)
    (repR : Fin m → Fin n) (hrepI : ∀ r ∈ I.image φ_R, repR r ∈ I)
    (hrepEq : ∀ r ∈ I.image φ_R, φ_R (repR r) = r) :
    let A := I.image φ_R
    let B := I.image φ_B
    let cB : Fin m → ℕ := fun j => (A.filter fun r => φ_B (repR r) = j).card
    (∑ j ∈ B, cB j = A.card) ∧
    (∀ j ∈ B, (cB j : ℝ) ≤ F_max) ∧
    (∑ j ∈ B, (cB j - 1) ≤ I.card - B.card) := by
  intro A B cB
  have hmaps : ∀ r ∈ A, φ_B (repR r) ∈ B := fun r hr => Finset.mem_image.mpr ⟨repR r, hrepI r hr, rfl⟩
  have hsum_cB : ∑ j ∈ B, cB j = A.card := by
    have := Finset.card_eq_sum_card_fiberwise (f := fun r => φ_B (repR r)) (s := A) (t := B) hmaps
    exact this.symm
  have hrep_inj : Set.InjOn repR (A : Set (Fin m)) := by
    intro r₁ hr1 r₂ hr2 heq
    have h1 := hrepEq r₁ hr1
    have h2 := hrepEq r₂ hr2
    rw [heq] at h1; exact h1.symm.trans h2
  have hcB_le : ∀ j ∈ B, (cB j : ℝ) ≤ F_max := by
    intro j _
    have hcard_le : cB j ≤ (Finset.univ.filter fun v : Fin n => φ_B v = j).card := by
      refine Finset.card_le_card_of_injOn repR ?_ ?_
      · intro r hr
        rcases Finset.mem_filter.mp hr with ⟨_, heq⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
      · intro r₁ hr1 r₂ hr2 heq
        exact hrep_inj (Finset.mem_filter.mp hr1).1 (Finset.mem_filter.mp hr2).1 heq
    exact le_trans (by exact_mod_cast hcard_le) (hfibB j)
  have hexcess : ∑ j ∈ B, (cB j - 1) ≤ I.card - B.card := by
    let I_R := A.image repR
    have hIR_sub : I_R ⊆ I := Finset.image_subset_iff.mpr hrepI
    have hIR_card : I_R.card = A.card := Finset.card_image_of_injOn hrep_inj
    let B_R := A.image fun r => φ_B (repR r)
    have hBR_sub : B_R ⊆ B := Finset.image_subset_iff.mpr hmaps
    have hBR_eq : B_R = I_R.image φ_B := by
      ext j; simp only [B_R, I_R, Finset.mem_image]
      constructor
      · rintro ⟨r, hr, rfl⟩; exact ⟨repR r, ⟨r, hr, rfl⟩, rfl⟩
      · rintro ⟨v, ⟨r, hr, rfl⟩, rfl⟩; exact ⟨r, hr, rfl⟩
    have hdiff_sub : B \ B_R ⊆ (I \ I_R).image φ_B := by
      intro j hj
      rcases Finset.mem_sdiff.mp hj with ⟨hjB, hjBR⟩
      rcases Finset.mem_image.mp hjB with ⟨v, hvI, rfl⟩
      refine Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hvI, fun hvIR => ?_⟩, rfl⟩
      rw [hBR_eq] at hjBR
      exact hjBR (Finset.mem_image.mpr ⟨v, hvIR, rfl⟩)
    have hdiff_le : B.card - B_R.card ≤ I.card - A.card := by
      calc B.card - B_R.card
          = (B \ B_R).card := (Finset.card_sdiff_of_subset hBR_sub).symm
        _ ≤ ((I \ I_R).image φ_B).card := Finset.card_le_card hdiff_sub
        _ ≤ (I \ I_R).card := Finset.card_image_le
        _ = I.card - I_R.card := Finset.card_sdiff_of_subset hIR_sub
        _ = I.card - A.card := by rw [hIR_card]
    have hBR_ge : ∀ j ∈ B_R, 1 ≤ cB j := by
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨r, hrA, rfl⟩
      exact Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨hrA, rfl⟩⟩
    have hnotBR : ∀ j ∈ B, j ∉ B_R → cB j = 0 := by
      intro j _ hjnot
      exact Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun r hrA heq =>
        hjnot (Finset.mem_image.mpr ⟨r, hrA, heq⟩))
    have hsum_eq : ∑ j ∈ B, (cB j - 1) = A.card - B_R.card := by
      have h1 : ∑ j ∈ B, (cB j - 1) = ∑ j ∈ B_R, (cB j - 1) := by
        symm; refine Finset.sum_subset hBR_sub fun j hjB hjnot => ?_
        rw [hnotBR j hjB hjnot]; rfl
      have h2 : ∑ j ∈ B_R, (cB j - 1) + B_R.card = ∑ j ∈ B_R, cB j := by
        calc ∑ j ∈ B_R, (cB j - 1) + B_R.card
            = ∑ j ∈ B_R, (cB j - 1) + ∑ _j ∈ B_R, 1 := by simp
          _ = ∑ j ∈ B_R, ((cB j - 1) + 1) := (Finset.sum_add_distrib).symm
          _ = ∑ j ∈ B_R, cB j := Finset.sum_congr rfl fun j hj => Nat.sub_add_cancel (hBR_ge j hj)
      have h3 : ∑ j ∈ B_R, cB j = A.card := by
        rw [← hsum_cB]; exact Finset.sum_subset hBR_sub fun j hjB hjnot => hnotBR j hjB hjnot
      omega
    have hB_le_I : B.card ≤ I.card := Finset.card_image_le
    have hA_le_I : A.card ≤ I.card := Finset.card_image_le
    have hBR_le_B : B_R.card ≤ B.card := Finset.card_le_card hBR_sub
    omega
  exact ⟨hsum_cB, hcB_le, hexcess⟩

/-- Algebraic count of closed red pairs in `A` under `GoodGraph P ω_R` and `GoodGraph P ω_B`:
the Stage-1 open pairs `openR` in `EdgeIdx (A \ Z_R).card` satisfy
`|openR| ≥ 1/2 * max 0 (a^2 - min((k - b)^2, D * (k - b))) - errOpen`. -/
noncomputable def Qmax (P : RegParams) : ℕ :=
  ⌈(P.L : ℝ) * (240 * (P.k : ℝ) / P.T_big + 4)⌉₊

noncomputable def errOpen (P : RegParams) (F_max : ℝ) : ℝ :=
  (P.k : ℝ) / 2 +
  (1 + F_max) * (Qmax P : ℝ) * (P.k : ℝ) +
  F_max * (P.k : ℝ) +
  errOut P F_max +
  2 * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) *
    ((P.k : ℝ) + F_max * (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ)) +
  (2 * (P.k : ℝ) + F_max * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) +
    F_max * (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ)) *
    (F_max * (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ))

/-- Deterministic lower bound on `|openR|` given `GoodGraph P ω_R` and `GoodGraph P ω_B`. -/
lemma card_openR_ge {n : ℕ} (P : RegParams) {F_max : ℝ}
    (ω_R ω_B : EdgeIdx P.m → Bool) (hGR : GoodGraph P ω_R) (hGB : GoodGraph P ω_B)
    {I : Finset (Fin n)} (hIk : I.card = P.k) {φ_R φ_B : Fin n → Fin P.m}
    (hfibB : ∀ j : Fin P.m, ((Finset.univ.filter fun v : Fin n => φ_B v = j).card : ℝ) ≤ F_max)
    (repR : Fin P.m → Fin n) (hrepI : ∀ r ∈ I.image φ_R, repR r ∈ I)
    (hrepEq : ∀ r ∈ I.image φ_R, φ_R (repR r) = r)
    (Z_R Z_B : Finset (Fin P.m))
    (hZR_card : Z_R.card ≤ Qmax P) (hZB_card : Z_B.card ≤ Qmax P)
    (h2k : 2 * P.k ≤ P.m) (hL1 : 1 ≤ P.L)
    (hF1 : 1 ≤ F_max) (hF_lt_L : ∀ x : ℕ, (x : ℝ) ≤ F_max → x < 2 ^ P.L)
    (hTlo : 0 < P.T_lo) (hTcut : P.T_lo ≤ P.T_cut) (hF_le_mid : F_max ≤ P.T_mid)
    (hTbig : 0 < P.T_big) (hTmid_lt : P.T_mid < P.T_big / 2)
    (hTbig_lt_J : P.T_big < ((2 ^ P.J : ℕ) : ℝ))
    (hBmid : 0 < P.B_mid) (hBcross : 0 < P.B_cross) (hm_lt_J : P.m < 2 ^ P.J)
    (hL_le_F : ∀ i : Fin P.L, ((2 ^ i.val : ℕ) : ℝ) ≤ F_max)
    (hL_le_Tbig : ∀ i : Fin P.L, ((2 ^ i.val : ℕ) : ℝ) ≤ P.T_big) :
    let A := I.image φ_R
    let B := I.image φ_B
    let A₂ := A \ Z_R
    let B₂ := B \ Z_B
    let eA := A₂.orderIsoOfFin rfl
    let openR : Finset (EdgeIdx A₂.card) := Finset.univ.filter fun e =>
      let r₁ := (eA e.1.1).1
      let r₂ := (eA e.1.2).1
      φ_B (repR r₁) ∉ Z_B ∧ φ_B (repR r₂) ∉ Z_B ∧
      φ_B (repR r₁) ≠ φ_B (repR r₂) ∧
      (¬ ∃ z : Fin P.m, z ∉ A₂ ∧ (graphOf ω_R).Adj z r₁ ∧ (graphOf ω_R).Adj z r₂) ∧
      (¬ ∃ w : Fin P.m, w ∉ B₂ ∧ (graphOf ω_B).Adj w (φ_B (repR r₁)) ∧ (graphOf ω_B).Adj w (φ_B (repR r₂)))
    let D := F_max * ((1 + P.η₀) * ((P.m : ℝ) * P.p))
    (1 / 2 : ℝ) * max 0 ((A.card : ℝ) ^ 2 -
        min (((P.k - B.card : ℕ) : ℝ) ^ 2) (D * ((P.k - B.card : ℕ) : ℝ))) - errOpen P F_max ≤
      (openR.card : ℝ) := by
  intro A B A₂ B₂ eA openR D
  have hdeg_nn : 0 ≤ (1 + P.η₀) * ((P.m : ℝ) * P.p) := by
    by_cases hm : 0 < P.m
    · exact le_trans (Nat.cast_nonneg _) (hGR.1 ⟨0, hm⟩)
    · have hm0 : P.m = 0 := by omega
      simp [hm0]
  have hD_nn : 0 ≤ D := mul_nonneg (by linarith) hdeg_nn
  have herr_nn : 0 ≤ errOpen P F_max := by
    have hQ : 0 ≤ (Qmax P : ℝ) := Nat.cast_nonneg _
    have hLpos : 0 < P.L := by omega
    have hTmid_pos : 0 < P.T_mid := lt_of_lt_of_le (by linarith : (0 : ℝ) < 1) (hF1.trans hF_le_mid)
    have hTcut_pos : 0 < P.T_cut := lt_of_lt_of_le hTlo hTcut
    have heo_nn : 0 ≤ errOut P F_max := by dsimp only [errOut]; positivity
    dsimp only [errOpen]; positivity
  -- If max 0 (...) = 0, then LHS = -errOpen ≤ 0 ≤ openR.card!
  by_cases hzero : (A.card : ℝ) ^ 2 -
      min (((P.k - B.card : ℕ) : ℝ) ^ 2) (D * ((P.k - B.card : ℕ) : ℝ)) ≤ 0
  · rw [max_eq_left hzero, mul_zero, zero_sub]
    linarith [Nat.cast_nonneg (α := ℝ) openR.card]
  push Not at hzero
  rw [max_eq_right hzero.le]
  -- Count ordered distinct pairs (r₁, r₂) in A × A that do NOT correspond to openR!
  let allOrd := (A ×ˢ A).filter fun q => q.1 ≠ q.2
  have hall_card : (allOrd.card : ℝ) = (A.card : ℝ) ^ 2 - (A.card : ℝ) := by
    have h1 : allOrd.card = A.card * (A.card - 1) := by
      have : allOrd.card = ∑ r₁ ∈ A, (A.erase r₁).card := by
        rw [← Finset.card_sigma]
        refine Finset.card_bij (fun q _ => ⟨q.1, q.2⟩) ?_ ?_ ?_
        · intro q hq
          rcases Finset.mem_filter.mp hq with ⟨hqA, hne⟩
          rcases Finset.mem_product.mp hqA with ⟨h1, h2⟩
          exact Finset.mem_sigma.mpr ⟨h1, Finset.mem_erase.mpr ⟨hne.symm, h2⟩⟩
        · intro q₁ _ q₂ _ h
          exact Prod.ext (congrArg Sigma.fst h) (eq_of_heq (Sigma.ext_iff.mp h).2)
        · intro x hx
          rcases Finset.mem_sigma.mp hx with ⟨h1, h2⟩
          rcases Finset.mem_erase.mp h2 with ⟨hne, h2A⟩
          exact ⟨(x.1, x.2), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1, h2A⟩, hne.symm⟩, rfl⟩
      rw [this]
      calc ∑ r₁ ∈ A, (A.erase r₁).card
          = ∑ _r₁ ∈ A, (A.card - 1) := Finset.sum_congr rfl fun r₁ hr1 => Finset.card_erase_of_mem hr1
        _ = A.card * (A.card - 1) := by rw [Finset.sum_const, smul_eq_mul]
    rw [h1]
    by_cases hA0 : A.card = 0
    · simp [hA0]
    · rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ A.card), Nat.cast_one]; ring
  let goodOrd := allOrd.filter fun q =>
    q.1 ∈ A₂ ∧ q.2 ∈ A₂ ∧
    φ_B (repR q.1) ∉ Z_B ∧ φ_B (repR q.2) ∉ Z_B ∧
    φ_B (repR q.1) ≠ φ_B (repR q.2) ∧
    (¬ ∃ z : Fin P.m, z ∉ A₂ ∧ (graphOf ω_R).Adj z q.1 ∧ (graphOf ω_R).Adj z q.2) ∧
    (¬ ∃ w : Fin P.m, w ∉ B₂ ∧ (graphOf ω_B).Adj w (φ_B (repR q.1)) ∧ (graphOf ω_B).Adj w (φ_B (repR q.2)))
  have h2open : 2 * openR.card = goodOrd.card := by
    let G1 := goodOrd.filter fun q => q.1 < q.2
    let G2 := goodOrd.filter fun q => q.2 < q.1
    have hdisj : Disjoint G1 G2 := Finset.disjoint_left.mpr fun q h1 h2 =>
      lt_asymm (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    have hunion : goodOrd = G1 ∪ G2 := by
      ext q; simp only [G1, G2, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hq
        have hne := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
        rcases lt_or_gt_of_ne hne with h | h
        · exact Or.inl ⟨hq, h⟩
        · exact Or.inr ⟨hq, h⟩
      · rintro (⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq
    have hG12 : G1.card = G2.card := by
      refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
      · intro q hq
        rcases Finset.mem_filter.mp hq with ⟨hqg, hlt⟩
        rcases Finset.mem_filter.mp hqg with ⟨hqa, h1, h2, h3, h4, h5, h6, h7⟩
        rcases Finset.mem_filter.mp hqa with ⟨hqp, hne⟩
        rcases Finset.mem_product.mp hqp with ⟨ha1, ha2⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨ha2, ha1⟩, hne.symm⟩,
          h2, h1, h4, h3, h5.symm,
          fun ⟨z, hz, ha, hb⟩ => h6 ⟨z, hz, hb, ha⟩,
          fun ⟨w, hw, ha, hb⟩ => h7 ⟨w, hw, hb, ha⟩⟩, hlt⟩
      · intro q₁ _ q₂ _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro q hq
        rcases Finset.mem_filter.mp hq with ⟨hqg, hlt⟩
        rcases Finset.mem_filter.mp hqg with ⟨hqa, h1, h2, h3, h4, h5, h6, h7⟩
        rcases Finset.mem_filter.mp hqa with ⟨hqp, hne⟩
        rcases Finset.mem_product.mp hqp with ⟨ha1, ha2⟩
        exact ⟨(q.2, q.1), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨ha2, ha1⟩, hne.symm⟩,
          h2, h1, h4, h3, h5.symm,
          fun ⟨z, hz, ha, hb⟩ => h6 ⟨z, hz, hb, ha⟩,
          fun ⟨w, hw, ha, hb⟩ => h7 ⟨w, hw, hb, ha⟩⟩, hlt⟩, rfl⟩
    have hopen_G1 : openR.card = G1.card := by
      refine Finset.card_bij (fun e _ => ((eA e.1.1).1, (eA e.1.2).1)) ?_ ?_ ?_
      · intro e he
        rcases (Finset.mem_filter.mp he).2 with ⟨h1, h2, h3, h4, h5⟩
        have hlt : (eA e.1.1).1 < (eA e.1.2).1 := eA.strictMono e.2
        have hA1 : (eA e.1.1).1 ∈ A := (Finset.mem_sdiff.mp (eA e.1.1).2).1
        have hA2 : (eA e.1.2).1 ∈ A := (Finset.mem_sdiff.mp (eA e.1.2).2).1
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hA1, hA2⟩, hlt.ne⟩,
          (eA e.1.1).2, (eA e.1.2).2, h1, h2, h3, h4, h5⟩, hlt⟩
      · intro e₁ _ e₂ _ h
        apply Subtype.ext; apply Prod.ext
        · exact eA.injective (Subtype.ext (congrArg Prod.fst h))
        · exact eA.injective (Subtype.ext (congrArg Prod.snd h))
      · intro q hq
        rcases Finset.mem_filter.mp hq with ⟨hqg, hlt⟩
        rcases Finset.mem_filter.mp hqg with ⟨_, h1, h2, h3, h4, h5, h6, h7⟩
        let i := eA.symm ⟨q.1, h1⟩
        let j := eA.symm ⟨q.2, h2⟩
        have hij : i < j := eA.symm.strictMono (show (⟨q.1, h1⟩ : A₂) < ⟨q.2, h2⟩ from hlt)
        have hi_eq : (eA i).1 = q.1 := congrArg Subtype.val (eA.apply_symm_apply ⟨q.1, h1⟩)
        have hj_eq : (eA j).1 = q.2 := congrArg Subtype.val (eA.apply_symm_apply ⟨q.2, h2⟩)
        refine ⟨⟨(i, j), hij⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Prod.ext hi_eq hj_eq⟩
        simpa only [hi_eq, hj_eq] using ⟨h3, h4, h5, h6, h7⟩
    rw [hunion, Finset.card_union_of_disjoint hdisj, ← hG12, hopen_G1]; ring
  -- Now bound |(allOrd \ goodOrd)| by 5 clean buckets!
  let bad1 := allOrd.filter fun q => q.1 ∈ Z_R ∨ q.2 ∈ Z_R
  let bad2 := allOrd.filter fun q => φ_B (repR q.1) ∈ Z_B ∨ φ_B (repR q.2) ∈ Z_B
  let bad3 := allOrd.filter fun q => φ_B (repR q.1) = φ_B (repR q.2)
  let bad4 := allOrd.filter fun q => ∃ z : Fin P.m, (graphOf ω_R).Adj z q.1 ∧ (graphOf ω_R).Adj z q.2
  let bad5 := allOrd.filter fun q =>
    φ_B (repR q.1) ≠ φ_B (repR q.2) ∧
    ∃ w : Fin P.m, (graphOf ω_B).Adj w (φ_B (repR q.1)) ∧ (graphOf ω_B).Adj w (φ_B (repR q.2))
  have hcov_bad : allOrd \ goodOrd ⊆ bad1 ∪ (bad2 ∪ (bad3 ∪ (bad4 ∪ bad5))) := by
    intro q hq
    rcases Finset.mem_sdiff.mp hq with ⟨hqa, hnotg⟩
    have hq1A : q.1 ∈ A := (Finset.mem_product.mp (Finset.mem_filter.mp hqa).1).1
    have hq2A : q.2 ∈ A := (Finset.mem_product.mp (Finset.mem_filter.mp hqa).1).2
    by_cases h1 : q.1 ∈ Z_R ∨ q.2 ∈ Z_R
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hqa, h1⟩)
    · push Not at h1
      have h1A₂ : q.1 ∈ A₂ := Finset.mem_sdiff.mpr ⟨hq1A, h1.1⟩
      have h2A₂ : q.2 ∈ A₂ := Finset.mem_sdiff.mpr ⟨hq2A, h1.2⟩
      by_cases h2 : φ_B (repR q.1) ∈ Z_B ∨ φ_B (repR q.2) ∈ Z_B
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hqa, h2⟩))
      · push Not at h2
        by_cases h3 : φ_B (repR q.1) = φ_B (repR q.2)
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨hqa, h3⟩)))
        · by_cases h4 : ∃ z : Fin P.m, (graphOf ω_R).Adj z q.1 ∧ (graphOf ω_R).Adj z q.2
          · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
              (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hqa, h4⟩))))
          · refine Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
              (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hqa, h3, ?_⟩))))
            by_contra h5
            exact hnotg (Finset.mem_filter.mpr ⟨hqa, h1A₂, h2A₂, h2.1, h2.2, h3,
              fun ⟨z, _, ha, hb⟩ => h4 ⟨z, ha, hb⟩, fun ⟨w, _, ha, hb⟩ => h5 ⟨w, ha, hb⟩⟩)
  have hA_le_k : A.card ≤ P.k := by rw [← hIk]; exact Finset.card_image_le
  -- Bound |bad1| ≤ 2 * Qmax * k
  have hbad1 : (bad1.card : ℝ) ≤ 2 * (Qmax P : ℝ) * (P.k : ℝ) := by
    have hsub : bad1 ⊆ (Z_R ×ˢ A) ∪ (A ×ˢ Z_R) := by
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqa, h1 | h2⟩
      · exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨h1, (Finset.mem_product.mp (Finset.mem_filter.mp hqa).1).2⟩)
      · exact Finset.mem_union_right _ (Finset.mem_product.mpr ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hqa).1).1, h2⟩)
    have hnat : bad1.card ≤ 2 * Qmax P * P.k := by
      calc bad1.card ≤ ((Z_R ×ˢ A) ∪ (A ×ˢ Z_R)).card := Finset.card_le_card hsub
        _ ≤ (Z_R ×ˢ A).card + (A ×ˢ Z_R).card := Finset.card_union_le _ _
        _ = Z_R.card * A.card + A.card * Z_R.card := by simp [Finset.card_product]
        _ ≤ Qmax P * P.k + P.k * Qmax P := add_le_add (Nat.mul_le_mul hZR_card hA_le_k) (Nat.mul_le_mul hA_le_k hZR_card)
        _ = 2 * Qmax P * P.k := by ring
    exact_mod_cast hnat
  -- Bound |bad2| ≤ 2 * F_max * Qmax * k
  let cB : Fin P.m → ℕ := fun j => (A.filter fun r => φ_B (repR r) = j).card
  obtain ⟨hsum_cB, hcB_le_F, hexcess_cB⟩ := rep_weight_bounds hfibB repR hrepI hrepEq
  rw [hIk] at hexcess_cB
  have hbad2 : (bad2.card : ℝ) ≤ 2 * F_max * (Qmax P : ℝ) * (P.k : ℝ) := by
    let A_ZB := A.filter fun r => φ_B (repR r) ∈ Z_B
    have hAZB_card : (A_ZB.card : ℝ) ≤ F_max * (Qmax P : ℝ) := by
      have hcov : A_ZB ⊆ Z_B.biUnion fun j => A.filter fun r => φ_B (repR r) = j := by
        intro r hr
        rcases Finset.mem_filter.mp hr with ⟨hrA, hrZB⟩
        exact Finset.mem_biUnion.mpr ⟨φ_B (repR r), hrZB, Finset.mem_filter.mpr ⟨hrA, rfl⟩⟩
      have hle : (A_ZB.card : ℝ) ≤ ∑ j ∈ Z_B, (cB j : ℝ) := by
        have hnat : A_ZB.card ≤ ∑ j ∈ Z_B, cB j := (Finset.card_le_card hcov).trans Finset.card_biUnion_le
        exact_mod_cast hnat
      have hcB_all : ∀ j : Fin P.m, (cB j : ℝ) ≤ F_max := by
        intro j
        by_cases hjB : j ∈ B
        · exact hcB_le_F j hjB
        · have h0 : cB j = 0 := Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun r hrA heq =>
            hjB (Finset.mem_image.mpr ⟨repR r, hrepI r hrA, heq⟩))
          rw [h0, Nat.cast_zero]; linarith
      calc (A_ZB.card : ℝ) ≤ ∑ j ∈ Z_B, (cB j : ℝ) := hle
        _ ≤ ∑ _j ∈ Z_B, F_max := Finset.sum_le_sum fun j _ => hcB_all j
        _ = (Z_B.card : ℝ) * F_max := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (Qmax P : ℝ) * F_max := mul_le_mul_of_nonneg_right (by exact_mod_cast hZB_card) (by linarith)
        _ = F_max * (Qmax P : ℝ) := by ring
    have hsub : bad2 ⊆ (A_ZB ×ˢ A) ∪ (A ×ˢ A_ZB) := by
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqa, h1 | h2⟩
      · rcases Finset.mem_product.mp (Finset.mem_filter.mp hqa).1 with ⟨ha1, ha2⟩
        exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨ha1, h1⟩, ha2⟩)
      · rcases Finset.mem_product.mp (Finset.mem_filter.mp hqa).1 with ⟨ha1, ha2⟩
        exact Finset.mem_union_right _ (Finset.mem_product.mpr ⟨ha1, Finset.mem_filter.mpr ⟨ha2, h2⟩⟩)
    have hle_nat : bad2.card ≤ 2 * A_ZB.card * A.card := by
      calc bad2.card ≤ ((A_ZB ×ˢ A) ∪ (A ×ˢ A_ZB)).card := Finset.card_le_card hsub
        _ ≤ (A_ZB ×ˢ A).card + (A ×ˢ A_ZB).card := Finset.card_union_le _ _
        _ = 2 * A_ZB.card * A.card := by simp [Finset.card_product]; ring
    have hle_real : (bad2.card : ℝ) ≤ 2 * (A_ZB.card : ℝ) * (A.card : ℝ) := by exact_mod_cast hle_nat
    have hAk_real : (A.card : ℝ) ≤ (P.k : ℝ) := by exact_mod_cast hA_le_k
    have h1 := mul_le_mul hAZB_card hAk_real (Nat.cast_nonneg _) (by positivity)
    linarith
  -- Bound |bad3| ≤ F_max * k
  have hbad3 : (bad3.card : ℝ) ≤ F_max * (P.k : ℝ) := by
    have hle_nat : bad3.card ≤ ∑ r₁ ∈ A, cB (φ_B (repR r₁)) := by
      rw [← Finset.card_sigma]
      refine Finset.card_le_card_of_injOn (fun q => ⟨q.1, q.2⟩) ?_ ?_
      · intro q hq
        rcases Finset.mem_filter.mp hq with ⟨hqa, heq⟩
        rcases Finset.mem_product.mp (Finset.mem_filter.mp hqa).1 with ⟨ha1, ha2⟩
        exact Finset.mem_sigma.mpr ⟨ha1, Finset.mem_filter.mpr ⟨ha2, heq.symm⟩⟩
      · intro q₁ _ q₂ _ h
        exact Prod.ext (congrArg Sigma.fst h) (eq_of_heq (Sigma.ext_iff.mp h).2)
    have hle_real : (bad3.card : ℝ) ≤ ∑ r₁ ∈ A, (cB (φ_B (repR r₁)) : ℝ) := by
      rw [← Nat.cast_sum]; exact_mod_cast hle_nat
    calc (bad3.card : ℝ) ≤ ∑ r₁ ∈ A, (cB (φ_B (repR r₁)) : ℝ) := hle_real
      _ ≤ ∑ _r₁ ∈ A, F_max := Finset.sum_le_sum fun r₁ hr1 =>
          hcB_le_F _ (Finset.mem_image.mpr ⟨repR r₁, hrepI r₁ hr1, rfl⟩)
      _ = (A.card : ℝ) * F_max := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (P.k : ℝ) * F_max := mul_le_mul_of_nonneg_right (by exact_mod_cast hA_le_k) (by linarith)
      _ = F_max * (P.k : ℝ) := by ring
  -- Bound |bad4| ≤ ∑ z, deg_R(z, A) * (deg_R(z, A) - 1)
  have hbad4 : (bad4.card : ℝ) ≤ errOut P F_max +
      ((1 + P.η₀) * ((P.m : ℝ) * P.p)) * ((P.k : ℝ) + (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ)) := by
    have hle_nat : bad4.card ≤ ∑ z : Fin P.m, degIn (graphOf ω_R) A z * (degIn (graphOf ω_R) A z - 1) := by
      have hcov : bad4 ⊆ Finset.univ.biUnion fun z : Fin P.m =>
          ((A.filter fun r => (graphOf ω_R).Adj z r) ×ˢ (A.filter fun r => (graphOf ω_R).Adj z r)).filter
            fun q => q.1 ≠ q.2 := by
        intro q hq
        rcases Finset.mem_filter.mp hq with ⟨hqa, z, h1, h2⟩
        rcases Finset.mem_filter.mp hqa with ⟨hqp, hne⟩
        rcases Finset.mem_product.mp hqp with ⟨ha1, ha2⟩
        exact Finset.mem_biUnion.mpr ⟨z, Finset.mem_univ _, Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨ha1, h1⟩, Finset.mem_filter.mpr ⟨ha2, h2⟩⟩, hne⟩⟩
      refine (Finset.card_le_card hcov).trans (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun z _ => ?_))
      set N := A.filter fun r => (graphOf ω_R).Adj z r
      have hcard_eq : ((N ×ˢ N).filter fun q => q.1 ≠ q.2).card = N.card * (N.card - 1) := by
        have : ((N ×ˢ N).filter fun q => q.1 ≠ q.2).card = ∑ r₁ ∈ N, (N.erase r₁).card := by
          rw [← Finset.card_sigma]
          refine Finset.card_bij (fun q _ => ⟨q.1, q.2⟩) ?_ ?_ ?_
          · intro q hq
            rcases Finset.mem_filter.mp hq with ⟨hqN, hne⟩
            rcases Finset.mem_product.mp hqN with ⟨h1, h2⟩
            exact Finset.mem_sigma.mpr ⟨h1, Finset.mem_erase.mpr ⟨hne.symm, h2⟩⟩
          · intro q₁ _ q₂ _ h
            exact Prod.ext (congrArg Sigma.fst h) (eq_of_heq (Sigma.ext_iff.mp h).2)
          · intro x hx
            rcases Finset.mem_sigma.mp hx with ⟨h1, h2⟩
            rcases Finset.mem_erase.mp h2 with ⟨hne, h2N⟩
            exact ⟨(x.1, x.2), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1, h2N⟩, hne.symm⟩, rfl⟩
        rw [this]
        calc ∑ r₁ ∈ N, (N.erase r₁).card
            = ∑ _r₁ ∈ N, (N.card - 1) := Finset.sum_congr rfl fun r₁ hr1 => Finset.card_erase_of_mem hr1
          _ = N.card * (N.card - 1) := by rw [Finset.sum_const, smul_eq_mul]
      exact le_of_eq hcard_eq
    have hle_real : (bad4.card : ℝ) ≤
        ∑ z : Fin P.m, ((degIn (graphOf ω_R) A z * (degIn (graphOf ω_R) A z - 1) : ℕ) : ℝ) := by
      rw [← Nat.cast_sum]; exact_mod_cast hle_nat
    refine hle_real.trans ?_
    refine (sum_degIn_choose2_le P ω_R hGR hA_le_k h2k hL1 hTlo hTcut hF_le_mid hTbig hTmid_lt
      hTbig_lt_J hBmid hBcross hm_lt_J hL_le_F hL_le_Tbig).trans ?_
    refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hdeg_nn)
    have hQ : (P.L : ℝ) * (240 * (P.k : ℝ) / P.T_big + 4) ≤ (Qmax P : ℝ) := Nat.le_ceil _
    have hsq : ((P.L : ℝ) * (240 * (P.k : ℝ) / P.T_big + 4)) ^ 2 ≤ (Qmax P : ℝ) ^ 2 := by
      nlinarith [show 0 ≤ (P.L : ℝ) * (240 * (P.k : ℝ) / P.T_big + 4) by positivity]
    exact mul_le_mul_of_nonneg_right hsq (Nat.cast_nonneg _)
  -- Bound |bad5| via Zbig P ω_B B cB: outside Zbig + inside Zbig!
  have hbad5 : (bad5.card : ℝ) ≤
      min (((P.k - B.card : ℕ) : ℝ) ^ 2) (D * ((P.k - B.card : ℕ) : ℝ)) +
      errOut P F_max +
      3 * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) *
        ((P.k : ℝ) + F_max * (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ)) +
      2 * (2 * (P.k : ℝ) + D + F_max * (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ)) *
        (F_max * (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ)) := by
    have hle_sum : (bad5.card : ℝ) ≤
        ∑ w : Fin P.m, ∑ j₁ ∈ B.filter (fun j => (graphOf ω_B).Adj w j),
        ∑ j₂ ∈ (B.filter (fun j => (graphOf ω_B).Adj w j)).erase j₁, ((cB j₁ : ℝ) * (cB j₂ : ℝ)) := by
      have hcov : bad5 ⊆ Finset.univ.biUnion fun w : Fin P.m =>
          allOrd.filter fun q =>
            φ_B (repR q.1) ≠ φ_B (repR q.2) ∧
            (graphOf ω_B).Adj w (φ_B (repR q.1)) ∧ (graphOf ω_B).Adj w (φ_B (repR q.2)) := by
        intro q hq
        rcases Finset.mem_filter.mp hq with ⟨hqa, hne, w, h1, h2⟩
        exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hqa, hne, h1, h2⟩⟩
      have hnat : bad5.card ≤ ∑ w : Fin P.m,
          ∑ j₁ ∈ B.filter (fun j => (graphOf ω_B).Adj w j),
          ∑ j₂ ∈ (B.filter (fun j => (graphOf ω_B).Adj w j)).erase j₁, (cB j₁ * cB j₂) := by
        refine (Finset.card_le_card hcov).trans (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun w _ => ?_))
        set Nw := B.filter fun j => (graphOf ω_B).Adj w j
        let S := Nw.sigma fun j₁ => (Nw.erase j₁).sigma fun j₂ =>
          (A.filter fun r => φ_B (repR r) = j₁) ×ˢ (A.filter fun r => φ_B (repR r) = j₂)
        have hS_card : S.card = ∑ j₁ ∈ Nw, ∑ j₂ ∈ Nw.erase j₁, (cB j₁ * cB j₂) := by
          simp only [S, Finset.card_sigma, Finset.card_product, cB]
        rw [← hS_card]
        refine Finset.card_le_card_of_injOn (fun q => ⟨φ_B (repR q.1), ⟨φ_B (repR q.2), (q.1, q.2)⟩⟩) ?_ ?_
        · intro q hq
          rcases Finset.mem_filter.mp hq with ⟨hqa, hne, h1, h2⟩
          rcases Finset.mem_product.mp (Finset.mem_filter.mp hqa).1 with ⟨ha1, ha2⟩
          have hj1 : φ_B (repR q.1) ∈ Nw :=
            Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨repR q.1, hrepI q.1 ha1, rfl⟩, h1⟩
          have hj2 : φ_B (repR q.2) ∈ Nw :=
            Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨repR q.2, hrepI q.2 ha2, rfl⟩, h2⟩
          exact Finset.mem_sigma.mpr ⟨hj1, Finset.mem_sigma.mpr ⟨Finset.mem_erase.mpr ⟨hne.symm, hj2⟩,
            Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨ha1, rfl⟩, Finset.mem_filter.mpr ⟨ha2, rfl⟩⟩⟩⟩
        · intro q₁ _ q₂ _ h
          have h2 : (q₁.1, q₁.2) = (q₂.1, q₂.2) := by
            have hs1 := (Sigma.ext_iff.mp h).2
            have hfst : φ_B (repR q₁.1) = φ_B (repR q₂.1) := congrArg Sigma.fst h
            have h_inner : (⟨φ_B (repR q₁.2), (q₁.1, q₁.2)⟩ : Sigma fun _ : Fin P.m => Fin P.m × Fin P.m) =
                ⟨φ_B (repR q₂.2), (q₂.1, q₂.2)⟩ := eq_of_heq hs1
            exact eq_of_heq (Sigma.ext_iff.mp h_inner).2
          exact Prod.ext (congrArg Prod.fst h2) (congrArg Prod.snd h2)
      have hcast : (bad5.card : ℝ) ≤
          ((∑ w : Fin P.m, ∑ j₁ ∈ B.filter (fun j => (graphOf ω_B).Adj w j),
            ∑ j₂ ∈ (B.filter (fun j => (graphOf ω_B).Adj w j)).erase j₁, (cB j₁ * cB j₂) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      simpa only [Nat.cast_sum, Nat.cast_mul] using hcast
    refine hle_sum.trans ?_
    set Z := Zbig P ω_B B cB
    have hsplit : (∑ w : Fin P.m, ∑ j₁ ∈ B.filter (fun j => (graphOf ω_B).Adj w j),
          ∑ j₂ ∈ (B.filter (fun j => (graphOf ω_B).Adj w j)).erase j₁, ((cB j₁ : ℝ) * (cB j₂ : ℝ))) =
        (∑ w ∈ Finset.univ.filter (fun w => w ∉ Z),
          ∑ j₁ ∈ B.filter (fun j => (graphOf ω_B).Adj w j),
          ∑ j₂ ∈ (B.filter (fun j => (graphOf ω_B).Adj w j)).erase j₁, ((cB j₁ : ℝ) * (cB j₂ : ℝ))) +
        (∑ w ∈ Z,
          ∑ j₁ ∈ B.filter (fun j => (graphOf ω_B).Adj w j),
          ∑ j₂ ∈ (B.filter (fun j => (graphOf ω_B).Adj w j)).erase j₁, ((cB j₁ : ℝ) * (cB j₂ : ℝ))) := by
      have h1 := (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin P.m))
        (fun w => w ∈ Z) (fun w => ∑ j₁ ∈ B.filter (fun j => (graphOf ω_B).Adj w j),
          ∑ j₂ ∈ (B.filter (fun j => (graphOf ω_B).Adj w j)).erase j₁, ((cB j₁ : ℝ) * (cB j₂ : ℝ)))).symm
      have hZeq : Finset.univ.filter (fun w : Fin P.m => w ∈ Z) = Z := by ext w; simp
      rw [hZeq] at h1; linarith
    rw [hsplit]
    have hsum_cB_le : ∑ j ∈ B, cB j ≤ P.k := by rw [hsum_cB]; exact hA_le_k
    have hcB_lt : ∀ j ∈ B, cB j < 2 ^ P.L := fun j hj => hF_lt_L (cB j) (hcB_le_F j hj)
    have hout : (∑ w ∈ Finset.univ.filter (fun w => w ∉ Z),
        ∑ j₁ ∈ B.filter (fun j => (graphOf ω_B).Adj w j),
        ∑ j₂ ∈ (B.filter (fun j => (graphOf ω_B).Adj w j)).erase j₁, ((cB j₁ : ℝ) * (cB j₂ : ℝ))) ≤
        errOut P F_max :=
      sum_weighted_pairs_outside_Zbig_le P ω_B hGB hsum_cB_le h2k hcB_lt hTlo hTcut hF_le_mid hTbig
        hBmid hBcross hm_lt_J hL_le_F
    -- Inside Z: bound by ∑_{w ∈ Z} W_w(cB)^2 where W_w(cB) ≤ deg(w, B) + W_w(cB')
    let cB' : Fin P.m → ℕ := fun j => cB j - 1
    let W : Fin P.m → ℝ := fun w => ∑ j ∈ B.filter (fun j => (graphOf ω_B).Adj w j), (cB j : ℝ)
    let W' : Fin P.m → ℝ := fun w => ∑ j ∈ B.filter (fun j => (graphOf ω_B).Adj w j), (cB' j : ℝ)
    have hZ_card : (Z.card : ℝ) ≤ (Qmax P : ℝ) :=
      (card_Zbig_le P ω_B hGB.2.2.2.1 hsum_cB_le hTbig hTmid_lt hTbig_lt_J hL_le_Tbig).trans (Nat.le_ceil _)
    have hZ_sq : (Z.card : ℝ) ^ 2 ≤ (Qmax P : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) Z.card]
    set Ez : ℝ := F_max * (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ)
    have hEz_nn : 0 ≤ Ez := by positivity
    have hpair_W : ∀ w ∈ Z,
        (∑ j₁ ∈ B.filter (fun j => (graphOf ω_B).Adj w j),
         ∑ j₂ ∈ (B.filter (fun j => (graphOf ω_B).Adj w j)).erase j₁, ((cB j₁ : ℝ) * (cB j₂ : ℝ))) ≤
        W w ^ 2 := by
      intro w _
      set Nw := B.filter fun j => (graphOf ω_B).Adj w j
      calc ∑ j₁ ∈ Nw, ∑ j₂ ∈ Nw.erase j₁, ((cB j₁ : ℝ) * (cB j₂ : ℝ))
          ≤ ∑ j₁ ∈ Nw, ∑ j₂ ∈ Nw, ((cB j₁ : ℝ) * (cB j₂ : ℝ)) :=
            Finset.sum_le_sum fun j₁ _ =>
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
                fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        _ = W w ^ 2 := by
            dsimp only [W, Nw]
            rw [sq, Finset.sum_mul]
            refine Finset.sum_congr rfl fun j₁ _ => (Finset.mul_sum _ _ _).symm
    have hW_split : ∀ w ∈ Z, W w ^ 2 ≤
        ((1 + P.η₀) * ((P.m : ℝ) * P.p)) * ((degIn (graphOf ω_B) B w : ℝ) + 2 * W' w) + W' w ^ 2 := by
      intro w _
      have hle_sum' : W w ≤ (degIn (graphOf ω_B) B w : ℝ) + W' w := by
        dsimp only [W, W', degIn]
        have hcard : ((B.filter fun j => (graphOf ω_B).Adj w j).card : ℝ) =
            ∑ _j ∈ B.filter (fun j => (graphOf ω_B).Adj w j), (1 : ℝ) := by simp
        rw [hcard, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun j _ => ?_
        have : cB j ≤ 1 + cB' j := by dsimp only [cB']; omega
        exact_mod_cast this
      have hd_le : (degIn (graphOf ω_B) B w : ℝ) ≤ (1 + P.η₀) * ((P.m : ℝ) * P.p) :=
        le_trans (by exact_mod_cast degIn_mono (graphOf ω_B) (Finset.subset_univ B) w) (hGB.1 w)
      have hW0 : 0 ≤ W w := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      have hW'0 : 0 ≤ W' w := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      have hd0 : 0 ≤ (degIn (graphOf ω_B) B w : ℝ) := Nat.cast_nonneg _
      nlinarith only [hle_sum', hd_le, hW0, hW'0, hd0]
    have hsum_deg_Z : ∑ w ∈ Z, (degIn (graphOf ω_B) B w : ℝ) ≤ (P.k : ℝ) + Ez := by
      let c1 : Fin P.m → ℕ := fun _ => 1
      have h1 := sum_weight_over_Z_le P ω_B hGB.2.1 (A := B) (Z := Z) (c := c1) (F_max := 1)
        (fun _ _ => by simp [c1]) (by norm_num)
      have hWeq : ∀ w ∈ Z, (∑ j ∈ B.filter (fun j => (graphOf ω_B).Adj w j), (c1 j : ℝ)) =
          (degIn (graphOf ω_B) B w : ℝ) := fun w _ => by simp [c1, degIn]
      rw [Finset.sum_congr rfl hWeq] at h1
      have hB_le_k : (B.card : ℝ) ≤ (P.k : ℝ) := by
        rw [← hIk]; exact_mod_cast (Finset.card_image_le : B.card ≤ I.card)
      have hc1_sum : ∑ j ∈ B, (c1 j : ℝ) = (B.card : ℝ) := by simp [c1]
      have hE1 : (1 : ℝ) * (Z.card : ℝ) ^ 2 * (P.C_codeg : ℝ) ≤ Ez := by
        dsimp only [Ez]
        have hF1_le : (Z.card : ℝ) ^ 2 ≤ F_max * (Qmax P : ℝ) ^ 2 := by
          nlinarith only [hZ_sq, hF1, sq_nonneg (Qmax P : ℝ)]
        nlinarith only [hF1_le, Nat.cast_nonneg (α := ℝ) P.C_codeg]
      linarith only [h1, hB_le_k, hc1_sum, hE1]
    have hcB'_le : ∀ j ∈ B, (cB' j : ℝ) ≤ F_max := fun j hj =>
      le_trans (by exact_mod_cast Nat.sub_le (cB j) 1) (hcB_le_F j hj)
    have hsum_W'_Z : ∑ w ∈ Z, W' w ≤ ((P.k - B.card : ℕ) : ℝ) + Ez := by
      have h1 := sum_weight_over_Z_le P ω_B hGB.2.1 (A := B) (Z := Z) (c := cB') (F_max := F_max)
        hcB'_le (by linarith only [hF1])
      have hsum_cB' : ∑ j ∈ B, (cB' j : ℝ) ≤ ((P.k - B.card : ℕ) : ℝ) := by
        rw [← Nat.cast_sum]; exact_mod_cast hexcess_cB
      have hE1 : F_max * (Z.card : ℝ) ^ 2 * (P.C_codeg : ℝ) ≤ Ez := by
        dsimp only [Ez]
        have hFC : 0 ≤ F_max * (P.C_codeg : ℝ) := mul_nonneg (by linarith only [hF1]) (Nat.cast_nonneg _)
        nlinarith only [hZ_sq, hFC]
      linarith only [h1, hsum_cB', hE1]
    have hW'_le_D : ∀ w ∈ Z, W' w ≤ D := fun w _ => by
      calc W' w ≤ ∑ _j ∈ B.filter (fun j => (graphOf ω_B).Adj w j), F_max :=
              Finset.sum_le_sum fun j hj => hcB'_le j (Finset.mem_filter.mp hj).1
        _ = (degIn (graphOf ω_B) B w : ℝ) * F_max := by rw [Finset.sum_const, nsmul_eq_mul]; rfl
        _ ≤ ((1 + P.η₀) * ((P.m : ℝ) * P.p)) * F_max :=
            mul_le_mul_of_nonneg_right
              (le_trans (by exact_mod_cast degIn_mono (graphOf ω_B) (Finset.subset_univ B) w) (hGB.1 w))
              (by linarith only [hF1])
        _ = D := by dsimp only [D]; ring
    have hW'_sq : ∑ w ∈ Z, W' w ^ 2 ≤
        min (((P.k - B.card : ℕ) : ℝ) ^ 2) (D * ((P.k - B.card : ℕ) : ℝ)) +
        (2 * (P.k : ℝ) + D + Ez) * Ez := by
      have hconv := sum_sq_le_min_sq_mul Z W'
        (fun w _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hW'_le_D hsum_W'_Z hD_nn
      set s : ℝ := ((P.k - B.card : ℕ) : ℝ)
      have hs_le : s ≤ (P.k : ℝ) := by dsimp only [s]; exact_mod_cast Nat.sub_le P.k B.card
      have hs0 : 0 ≤ s := Nat.cast_nonneg _
      have hmin_le : min ((s + Ez) ^ 2) (D * (s + Ez)) ≤ min (s ^ 2) (D * s) + (2 * (P.k : ℝ) + D + Ez) * Ez := by
        rw [min_add, le_min_iff]
        refine ⟨?_, ?_⟩
        · have h1 : min ((s + Ez) ^ 2) (D * (s + Ez)) ≤ (s + Ez) ^ 2 := min_le_left _ _
          nlinarith only [h1, hs_le, hs0, hEz_nn, hD_nn]
        · have h2 : min ((s + Ez) ^ 2) (D * (s + Ez)) ≤ D * (s + Ez) := min_le_right _ _
          nlinarith only [h2, hs_le, hs0, hEz_nn, hD_nn, Nat.cast_nonneg (α := ℝ) P.k]
      exact hconv.trans hmin_le
    have hW'_le_k : ∑ w ∈ Z, W' w ≤ (P.k : ℝ) + Ez := by
      have hs_le : ((P.k - B.card : ℕ) : ℝ) ≤ (P.k : ℝ) := by exact_mod_cast Nat.sub_le P.k B.card
      linarith only [hsum_W'_Z, hs_le]
    have hin : (∑ w ∈ Z, ∑ j₁ ∈ B.filter (fun j => (graphOf ω_B).Adj w j),
        ∑ j₂ ∈ (B.filter (fun j => (graphOf ω_B).Adj w j)).erase j₁, ((cB j₁ : ℝ) * (cB j₂ : ℝ))) ≤
        min (((P.k - B.card : ℕ) : ℝ) ^ 2) (D * ((P.k - B.card : ℕ) : ℝ)) +
        3 * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) * ((P.k : ℝ) + Ez) +
        (2 * (P.k : ℝ) + D + Ez) * Ez := by
      calc _ ≤ ∑ w ∈ Z, W w ^ 2 := Finset.sum_le_sum hpair_W
        _ ≤ ∑ w ∈ Z, (((1 + P.η₀) * ((P.m : ℝ) * P.p)) *
              ((degIn (graphOf ω_B) B w : ℝ) + 2 * W' w) + W' w ^ 2) := Finset.sum_le_sum hW_split
        _ = ((1 + P.η₀) * ((P.m : ℝ) * P.p)) *
              ((∑ w ∈ Z, (degIn (graphOf ω_B) B w : ℝ)) + 2 * ∑ w ∈ Z, W' w) +
            ∑ w ∈ Z, W' w ^ 2 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
        _ ≤ ((1 + P.η₀) * ((P.m : ℝ) * P.p)) * (3 * ((P.k : ℝ) + Ez)) +
            (min (((P.k - B.card : ℕ) : ℝ) ^ 2) (D * ((P.k - B.card : ℕ) : ℝ)) +
              (2 * (P.k : ℝ) + D + Ez) * Ez) := by
            refine add_le_add (mul_le_mul_of_nonneg_left (by linarith only [hsum_deg_Z, hW'_le_k]) hdeg_nn) hW'_sq
        _ = _ := by ring
    have hpos_extra : 0 ≤ (2 * (P.k : ℝ) + D + Ez) * Ez :=
      mul_nonneg (add_nonneg (add_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hD_nn) hEz_nn) hEz_nn
    linarith only [hout, hin, hpos_extra]
  -- Combine: 2 * openR.card = goodOrd.card ≥ allOrd.card - (bad1 + bad2 + bad3 + bad4 + bad5)
  have hgood_sub : goodOrd ⊆ allOrd := Finset.filter_subset _ _
  have hdiff_card : allOrd.card - goodOrd.card ≤ bad1.card + bad2.card + bad3.card + bad4.card + bad5.card := by
    rw [← Finset.card_sdiff_of_subset hgood_sub]
    calc (allOrd \ goodOrd).card
        ≤ (bad1 ∪ (bad2 ∪ (bad3 ∪ (bad4 ∪ bad5)))).card := Finset.card_le_card hcov_bad
      _ ≤ bad1.card + (bad2 ∪ (bad3 ∪ (bad4 ∪ bad5))).card := Finset.card_union_le _ _
      _ ≤ bad1.card + (bad2.card + (bad3 ∪ (bad4 ∪ bad5)).card) := add_le_add le_rfl (Finset.card_union_le _ _)
      _ ≤ bad1.card + (bad2.card + (bad3.card + (bad4 ∪ bad5).card)) :=
          add_le_add le_rfl (add_le_add le_rfl (Finset.card_union_le _ _))
      _ ≤ bad1.card + (bad2.card + (bad3.card + (bad4.card + bad5.card))) :=
          add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl (Finset.card_union_le _ _)))
      _ = _ := by ring
  have hall_le_good : (allOrd.card : ℝ) ≤
      (goodOrd.card : ℝ) + (bad1.card : ℝ) + (bad2.card : ℝ) + (bad3.card : ℝ) +
      (bad4.card : ℝ) + (bad5.card : ℝ) := by
    have hnat : allOrd.card ≤ goodOrd.card + bad1.card + bad2.card + bad3.card + bad4.card + bad5.card := by
      have := Finset.card_le_card hgood_sub; omega
    exact_mod_cast hnat
  have h2open_real : 2 * (openR.card : ℝ) = (goodOrd.card : ℝ) := by exact_mod_cast h2open
  have hA_le_k_real : (A.card : ℝ) ≤ (P.k : ℝ) := by exact_mod_cast hA_le_k
  have hQ_sq_F : (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ) ≤ F_max * (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ) := by
    have hq : 0 ≤ (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ) := mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
    nlinarith only [hF1, hq]
  have hbad4_le : (bad4.card : ℝ) ≤ errOut P F_max +
      ((1 + P.η₀) * ((P.m : ℝ) * P.p)) * ((P.k : ℝ) + F_max * (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ)) := by
    refine hbad4.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl hQ_sq_F) hdeg_nn))
  -- Check: 2 * errOpen P F_max ≥ k + 2*(1+F_max)*Qmax*k + 2*F_max*k + 2*errOut + 4*deg*(k+Ez) + 2*(2k+D+Ez)*Ez
  have hsum_bads : (A.card : ℝ) + (bad1.card : ℝ) + (bad2.card : ℝ) + (bad3.card : ℝ) +
      (bad4.card : ℝ) + (bad5.card : ℝ) ≤
      min (((P.k - B.card : ℕ) : ℝ) ^ 2) (D * ((P.k - B.card : ℕ) : ℝ)) + 2 * errOpen P F_max := by
    dsimp only [errOpen]
    have hFk_nn : 0 ≤ F_max * (P.k : ℝ) := mul_nonneg (by linarith only [hF1]) (Nat.cast_nonneg _)
    linarith only [hA_le_k_real, hbad1, hbad2, hbad3, hbad4_le, hbad5, hFk_nn]
  linarith only [hall_card, hall_le_good, h2open_real, hsum_bads]

end JointIndepBound

/- ### Section 3B: Stage-1/Stage-2 Conditioning Assembly (`bernProb_indep_good_le`) -/

section JointIndepAssembly

/-- Number of subsets of a set of size `≤ k` having cardinality `≤ Q` is at most `(Q + 1) * (A.card + 1)^Q`. -/
lemma card_powerset_card_le {α : Type*} [DecidableEq α] (A : Finset α) (Q : ℕ) :
    ((A.powerset.filter fun Z => Z.card ≤ Q).card : ℝ) ≤
      ((Q + 1 : ℕ) : ℝ) * ((A.card + 1 : ℕ) : ℝ) ^ Q := by
  have hcov : A.powerset.filter (fun Z => Z.card ≤ Q) ⊆
      (Finset.range (Q + 1)).biUnion fun q => A.powersetCard q := by
    intro Z hZ
    rcases Finset.mem_filter.mp hZ with ⟨hZp, hZq⟩
    exact Finset.mem_biUnion.mpr ⟨Z.card, Finset.mem_range.mpr (by omega),
      Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hZp, rfl⟩⟩
  have hnat : (A.powerset.filter fun Z => Z.card ≤ Q).card ≤ (Q + 1) * (A.card + 1) ^ Q := by
    calc (A.powerset.filter fun Z => Z.card ≤ Q).card
        ≤ ((Finset.range (Q + 1)).biUnion fun q => A.powersetCard q).card := Finset.card_le_card hcov
      _ ≤ ∑ q ∈ Finset.range (Q + 1), (A.powersetCard q).card := Finset.card_biUnion_le
      _ = ∑ q ∈ Finset.range (Q + 1), A.card.choose q := by
          refine Finset.sum_congr rfl fun q _ => Finset.card_powersetCard q A
      _ ≤ ∑ _q ∈ Finset.range (Q + 1), (A.card + 1) ^ Q := by
          refine Finset.sum_le_sum fun q hq => ?_
          have hqle : q ≤ Q := by have := Finset.mem_range.mp hq; omega
          calc A.card.choose q ≤ A.card ^ q := choose_le_pow A.card q
            _ ≤ (A.card + 1) ^ q := Nat.pow_le_pow_left (by omega) q
            _ ≤ (A.card + 1) ^ Q := Nat.pow_le_pow_right (by omega) hqle
      _ = (Q + 1) * (A.card + 1) ^ Q := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  exact_mod_cast hnat

/-- Exact Stage-2 `triCand` upper bound for `G_R[A₂]` under `GoodGraph P ω_R`. -/
noncomputable def MtriBound (P : RegParams) (F_max : ℝ) : ℕ :=
  ⌈((P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) + errOut P F_max +
    ((1 + P.η₀) * ((P.m : ℝ) * P.p)) *
      ((P.k : ℝ) + ((P.L : ℝ) * (240 * (P.k : ℝ) / P.T_big + 4)) ^ 2 * (P.C_codeg : ℝ))) / 2⌉₊

lemma sum_triCand_sub_le (P : RegParams) {F_max : ℝ}
    (ω : EdgeIdx P.m → Bool) (hG : GoodGraph P ω)
    {A A₂ : Finset (Fin P.m)} (hA₂ : A₂ ⊆ A) (hAcard : A.card ≤ P.k)
    (h2k : 2 * P.k ≤ P.m) (hL1 : 1 ≤ P.L)
    (hTlo : 0 < P.T_lo) (hTcut : P.T_lo ≤ P.T_cut) (hF_le_mid : F_max ≤ P.T_mid)
    (hTbig : 0 < P.T_big) (hTmid_lt : P.T_mid < P.T_big / 2)
    (hTbig_lt_J : P.T_big < ((2 ^ P.J : ℕ) : ℝ))
    (hBmid : 0 < P.B_mid) (hBcross : 0 < P.B_cross) (hm_lt_J : P.m < 2 ^ P.J)
    (hL_le_F : ∀ i : Fin P.L, ((2 ^ i.val : ℕ) : ℝ) ≤ F_max)
    (hL_le_Tbig : ∀ i : Fin P.L, ((2 ^ i.val : ℕ) : ℝ) ≤ P.T_big) :
    let ωIn : EdgeIdx A₂.card → Bool := fun e => ω ((edgeSplitSub A₂).symm (Sum.inl e))
    ∑ i : Fin A₂.card, (triCand ωIn i).card ≤ MtriBound P F_max := by
  intro ωIn
  set eA := A₂.orderIsoOfFin rfl
  have h2tri := two_mul_sum_triCand_le ωIn
  have hdeg_le : ∀ r : Fin A₂.card,
      degIn (graphOf ωIn) Finset.univ r ≤ degIn (graphOf ω) A (eA r).1 := by
    intro r
    dsimp only [degIn]
    refine Finset.card_le_card_of_injOn (fun j => (eA j).1) ?_ ?_
    · intro j hj
      have hadj := (Finset.mem_filter.mp hj).2
      exact Finset.mem_filter.mpr ⟨hA₂ (eA j).2, (graphOf_edgeSplitSub_int A₂ ω r j).mpr hadj⟩
    · intro j₁ _ j₂ _ h; exact eA.injective (Subtype.ext h)
  have hsq_sum : ∑ r : Fin A₂.card, (degIn (graphOf ωIn) Finset.univ r) ^ 2 ≤
      ∑ z : Fin P.m, (degIn (graphOf ω) A z) ^ 2 := by
    calc ∑ r : Fin A₂.card, (degIn (graphOf ωIn) Finset.univ r) ^ 2
        ≤ ∑ r : Fin A₂.card, (degIn (graphOf ω) A (eA r).1) ^ 2 :=
          Finset.sum_le_sum fun r _ => Nat.pow_le_pow_left (hdeg_le r) 2
      _ = ∑ z ∈ A₂, (degIn (graphOf ω) A z) ^ 2 := by
          refine Finset.sum_bij (fun r _ => (eA r).1) (fun r _ => (eA r).2)
            (fun r₁ _ r₂ _ h => eA.injective (Subtype.ext h)) ?_ (fun _ _ => rfl)
          intro z hz
          exact ⟨eA.symm ⟨z, hz⟩, Finset.mem_univ _, congrArg Subtype.val (eA.apply_symm_apply ⟨z, hz⟩)⟩
      _ ≤ ∑ z : Fin P.m, (degIn (graphOf ω) A z) ^ 2 :=
          Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
  have hdeg_split : ∀ z : Fin P.m,
      ((degIn (graphOf ω) A z : ℝ) ^ 2) =
      (degIn (graphOf ω) A z : ℝ) + ((degIn (graphOf ω) A z * (degIn (graphOf ω) A z - 1) : ℕ) : ℝ) := by
    intro z
    set d := degIn (graphOf ω) A z
    by_cases hd : d = 0
    · simp [hd]
    · rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]; ring
  have hsum_deg1 : ∑ z : Fin P.m, (degIn (graphOf ω) A z : ℝ) ≤
      (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) := by
    have hswap : ∑ z : Fin P.m, degIn (graphOf ω) A z = ∑ r ∈ A, degIn (graphOf ω) Finset.univ r := by
      simp only [degIn]
      have h1 : ∀ z : Fin P.m, (A.filter fun r => (graphOf ω).Adj z r).card =
          ∑ r ∈ A, if (graphOf ω).Adj z r then 1 else 0 := fun _ => by simp
      have h2 : ∀ r : Fin P.m, (Finset.univ.filter fun z => (graphOf ω).Adj r z).card =
          ∑ z : Fin P.m, if (graphOf ω).Adj z r then 1 else 0 := fun r => by
        simp only [Finset.card_filter]; refine Finset.sum_congr rfl fun z _ => ?_
        by_cases hadj : (graphOf ω).Adj r z
        · simp [hadj, hadj.symm]
        · have hnot : ¬ (graphOf ω).Adj z r := fun h => hadj h.symm
          simp [hadj, hnot]
      simp_rw [h1, h2]; exact Finset.sum_comm
    rw [← Nat.cast_sum, hswap, Nat.cast_sum]
    have hdeg_nn : 0 ≤ (1 + P.η₀) * ((P.m : ℝ) * P.p) := by
      by_cases hm : 0 < P.m
      · exact le_trans (Nat.cast_nonneg _) (hG.1 ⟨0, hm⟩)
      · have hm0 : P.m = 0 := by omega
        simp [hm0]
    calc ∑ r ∈ A, (degIn (graphOf ω) Finset.univ r : ℝ)
        ≤ ∑ _r ∈ A, ((1 + P.η₀) * ((P.m : ℝ) * P.p)) := Finset.sum_le_sum fun r _ => hG.1 r
      _ = (A.card : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hAcard) hdeg_nn
  have hsum_deg2 := sum_degIn_choose2_le P ω hG hAcard h2k hL1 hTlo hTcut hF_le_mid hTbig
    hTmid_lt hTbig_lt_J hBmid hBcross hm_lt_J hL_le_F hL_le_Tbig
  have htot : (2 : ℝ) * ((∑ i : Fin A₂.card, (triCand ωIn i).card : ℕ) : ℝ) ≤
      (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) + errOut P F_max +
      ((1 + P.η₀) * ((P.m : ℝ) * P.p)) *
        ((P.k : ℝ) + ((P.L : ℝ) * (240 * (P.k : ℝ) / P.T_big + 4)) ^ 2 * (P.C_codeg : ℝ)) := by
    have h1 : (2 : ℝ) * ((∑ i : Fin A₂.card, (triCand ωIn i).card : ℕ) : ℝ) ≤
        ∑ z : Fin P.m, ((degIn (graphOf ω) A z : ℝ) ^ 2) := by
      have hnat := h2tri.trans hsq_sum
      have hreal : ((2 * ∑ i : Fin A₂.card, (triCand ωIn i).card : ℕ) : ℝ) ≤
          ((∑ z : Fin P.m, (degIn (graphOf ω) A z) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnat
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum, Nat.cast_pow] using hreal
    refine h1.trans ?_
    simp_rw [hdeg_split]
    rw [Finset.sum_add_distrib]
    linarith
  have hle_div : ((∑ i : Fin A₂.card, (triCand ωIn i).card : ℕ) : ℝ) ≤
      ((P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) + errOut P F_max +
        ((1 + P.η₀) * ((P.m : ℝ) * P.p)) *
          ((P.k : ℝ) + ((P.L : ℝ) * (240 * (P.k : ℝ) / P.T_big + 4)) ^ 2 * (P.C_codeg : ℝ))) / 2 := by
    linarith
  dsimp only [MtriBound]
  exact Nat.cast_le (α := ℝ).mp (hle_div.trans (Nat.le_ceil _))

/-- Stage-2 mixed-killer set bound: when `GoodGraph P ω_B` and `Z_B = Zbig P ω_B B cB ∩ B`,
the number of pairs in `openR` killed by an interior blue 2-path through `B₂ = B \ Z_B`
is at most `(1 / 2) * errOut P F_max`. -/
lemma card_KR_le {n : ℕ} (P : RegParams) {F_max : ℝ}
    (ω_B : EdgeIdx P.m → Bool) (hGB : GoodGraph P ω_B)
    {I : Finset (Fin n)} (hIk : I.card = P.k) {φ_R φ_B : Fin n → Fin P.m}
    (hfibB : ∀ j : Fin P.m, ((Finset.univ.filter fun v : Fin n => φ_B v = j).card : ℝ) ≤ F_max)
    (repR : Fin P.m → Fin n) (hrepI : ∀ r ∈ I.image φ_R, repR r ∈ I)
    (hrepEq : ∀ r ∈ I.image φ_R, φ_R (repR r) = r)
    (Z_R Z_B : Finset (Fin P.m))
    (hZB_eq : Z_B = Zbig P ω_B (I.image φ_B)
        (fun j => ((I.image φ_R).filter fun r => φ_B (repR r) = j).card) ∩ (I.image φ_B))
    (h2k : 2 * P.k ≤ P.m) (hF_lt_L : ∀ x : ℕ, (x : ℝ) ≤ F_max → x < 2 ^ P.L)
    (hTlo : 0 < P.T_lo) (hTcut : P.T_lo ≤ P.T_cut) (hF_le_mid : F_max ≤ P.T_mid)
    (hTbig : 0 < P.T_big) (hBmid : 0 < P.B_mid) (hBcross : 0 < P.B_cross)
    (hm_lt_J : P.m < 2 ^ P.J) (hL_le_F : ∀ i : Fin P.L, ((2 ^ i.val : ℕ) : ℝ) ≤ F_max) :
    let A := I.image φ_R
    let B := I.image φ_B
    let A₂ := A \ Z_R
    let B₂ := B \ Z_B
    let eA := A₂.orderIsoOfFin rfl
    let eB := B₂.orderIsoOfFin rfl
    let ωInB : EdgeIdx B₂.card → Bool := fun e => ω_B ((edgeSplitSub B₂).symm (Sum.inl e))
    let KR : Finset (EdgeIdx A₂.card) := Finset.univ.filter fun e =>
      let r₁ := (eA e.1.1).1
      let r₂ := (eA e.1.2).1
      ∃ h1 : φ_B (repR r₁) ∈ B₂, ∃ h2 : φ_B (repR r₂) ∈ B₂,
        φ_B (repR r₁) ≠ φ_B (repR r₂) ∧
        ∃ w : Fin B₂.card,
          (graphOf ωInB).Adj w (eB.symm ⟨φ_B (repR r₁), h1⟩) ∧
          (graphOf ωInB).Adj w (eB.symm ⟨φ_B (repR r₂), h2⟩)
    (KR.card : ℝ) ≤ errOut P F_max / 2 := by
  intro A B A₂ B₂ eA eB ωInB KR
  let cB : Fin P.m → ℕ := fun j => (A.filter fun r => φ_B (repR r) = j).card
  obtain ⟨hsum_cB, hcB_le_F, _⟩ := rep_weight_bounds hfibB repR hrepI hrepEq
  have hA_le_k : A.card ≤ P.k := by rw [← hIk]; exact Finset.card_image_le
  have hsum_le : ∑ j ∈ B, cB j ≤ P.k := by rw [hsum_cB]; exact hA_le_k
  have hcB_lt : ∀ j ∈ B, cB j < 2 ^ P.L := fun j hj => hF_lt_L (cB j) (hcB_le_F j hj)
  -- Double-count ordered pairs (r₁, r₂) from KR: 2 * KR.card ≤ ∑_{w ∈ B₂} ∑_{j₁ ≠ j₂ ∈ B ∩ N(w)} cB j₁ * cB j₂
  let ordKR := (A ×ˢ A).filter fun q =>
    q.1 ≠ q.2 ∧ φ_B (repR q.1) ≠ φ_B (repR q.2) ∧
    ∃ w ∈ B₂, (graphOf ω_B).Adj w (φ_B (repR q.1)) ∧ (graphOf ω_B).Adj w (φ_B (repR q.2))
  have h2KR : 2 * KR.card ≤ ordKR.card := by
    let O1 := ordKR.filter fun q => q.1 < q.2
    let O2 := ordKR.filter fun q => q.2 < q.1
    have hdisj : Disjoint O1 O2 := Finset.disjoint_left.mpr fun q h1 h2 =>
      lt_asymm (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    have hO12 : O1.card = O2.card := by
      refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
      · intro q hq
        rcases Finset.mem_filter.mp hq with ⟨hqo, hlt⟩
        rcases Finset.mem_filter.mp hqo with ⟨hqp, hne, hneB, w, hw, h1, h2⟩
        rcases Finset.mem_product.mp hqp with ⟨ha1, ha2⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha2, ha1⟩,
          hne.symm, hneB.symm, w, hw, h2, h1⟩, hlt⟩
      · intro q₁ _ q₂ _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro q hq
        rcases Finset.mem_filter.mp hq with ⟨hqo, hlt⟩
        rcases Finset.mem_filter.mp hqo with ⟨hqp, hne, hneB, w, hw, h1, h2⟩
        rcases Finset.mem_product.mp hqp with ⟨ha1, ha2⟩
        exact ⟨(q.2, q.1), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha2, ha1⟩,
          hne.symm, hneB.symm, w, hw, h2, h1⟩, hlt⟩, rfl⟩
    have hKR_O1 : KR.card ≤ O1.card := by
      refine Finset.card_le_card_of_injOn (fun e => ((eA e.1.1).1, (eA e.1.2).1)) ?_ ?_
      · intro e he
        rcases (Finset.mem_filter.mp he).2 with ⟨h1, h2, hneB, w, hw1, hw2⟩
        have hlt : (eA e.1.1).1 < (eA e.1.2).1 := eA.strictMono e.2
        have hA1 : (eA e.1.1).1 ∈ A := (Finset.mem_sdiff.mp (eA e.1.1).2).1
        have hA2 : (eA e.1.2).1 ∈ A := (Finset.mem_sdiff.mp (eA e.1.2).2).1
        have hadj1 : (graphOf ω_B).Adj (eB w).1 (φ_B (repR (eA e.1.1).1)) := by
          have h1' := (graphOf_edgeSplitSub_int B₂ ω_B w (eB.symm ⟨φ_B (repR (eA e.1.1).1), h1⟩)).mpr hw1
          change (graphOf ω_B).Adj (eB w).1 (eB (eB.symm ⟨φ_B (repR (eA e.1.1).1), h1⟩)).1 at h1'
          rwa [eB.apply_symm_apply] at h1'
        have hadj2 : (graphOf ω_B).Adj (eB w).1 (φ_B (repR (eA e.1.2).1)) := by
          have h2' := (graphOf_edgeSplitSub_int B₂ ω_B w (eB.symm ⟨φ_B (repR (eA e.1.2).1), h2⟩)).mpr hw2
          change (graphOf ω_B).Adj (eB w).1 (eB (eB.symm ⟨φ_B (repR (eA e.1.2).1), h2⟩)).1 at h2'
          rwa [eB.apply_symm_apply] at h2'
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hA1, hA2⟩,
          hlt.ne, hneB, (eB w).1, (eB w).2, hadj1, hadj2⟩, hlt⟩
      · intro e₁ _ e₂ _ h
        apply Subtype.ext; apply Prod.ext
        · exact eA.injective (Subtype.ext (congrArg Prod.fst h))
        · exact eA.injective (Subtype.ext (congrArg Prod.snd h))
    have hsub : O1 ∪ O2 ⊆ ordKR := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hle := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, ← hO12] at hle
    omega
  have hord_le : (ordKR.card : ℝ) ≤
      ∑ w ∈ Finset.univ.filter (fun w => w ∉ Zbig P ω_B B cB),
        ∑ j₁ ∈ B.filter (fun j => (graphOf ω_B).Adj w j),
        ∑ j₂ ∈ (B.filter (fun j => (graphOf ω_B).Adj w j)).erase j₁, ((cB j₁ : ℝ) * (cB j₂ : ℝ)) := by
    have hB₂_sub : B₂ ⊆ Finset.univ.filter (fun w => w ∉ Zbig P ω_B B cB) := by
      intro w hw
      rcases Finset.mem_sdiff.mp hw with ⟨hwB, hwZB⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hZ => hwZB ?_⟩
      rw [hZB_eq]; exact Finset.mem_inter.mpr ⟨hZ, hwB⟩
    have hcov : ordKR ⊆ B₂.biUnion fun w =>
        (A ×ˢ A).filter fun q =>
          φ_B (repR q.1) ≠ φ_B (repR q.2) ∧
          (graphOf ω_B).Adj w (φ_B (repR q.1)) ∧ (graphOf ω_B).Adj w (φ_B (repR q.2)) := by
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqp, _, hneB, w, hw, h1, h2⟩
      exact Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_filter.mpr ⟨hqp, hneB, h1, h2⟩⟩
    have hnat : ordKR.card ≤ ∑ w ∈ B₂,
        ∑ j₁ ∈ B.filter (fun j => (graphOf ω_B).Adj w j),
        ∑ j₂ ∈ (B.filter (fun j => (graphOf ω_B).Adj w j)).erase j₁, (cB j₁ * cB j₂) := by
      refine (Finset.card_le_card hcov).trans (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun w _ => ?_))
      set Nw := B.filter fun j => (graphOf ω_B).Adj w j
      let S := Nw.sigma fun j₁ => (Nw.erase j₁).sigma fun j₂ =>
        (A.filter fun r => φ_B (repR r) = j₁) ×ˢ (A.filter fun r => φ_B (repR r) = j₂)
      have hS_card : S.card = ∑ j₁ ∈ Nw, ∑ j₂ ∈ Nw.erase j₁, (cB j₁ * cB j₂) := by
        simp only [S, Finset.card_sigma, Finset.card_product, cB]
      rw [← hS_card]
      refine Finset.card_le_card_of_injOn (fun q => ⟨φ_B (repR q.1), ⟨φ_B (repR q.2), (q.1, q.2)⟩⟩) ?_ ?_
      · intro q hq
        rcases Finset.mem_filter.mp hq with ⟨hqp, hneB, h1, h2⟩
        rcases Finset.mem_product.mp hqp with ⟨ha1, ha2⟩
        have hj1 : φ_B (repR q.1) ∈ Nw :=
          Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨repR q.1, hrepI q.1 ha1, rfl⟩, h1⟩
        have hj2 : φ_B (repR q.2) ∈ Nw :=
          Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨repR q.2, hrepI q.2 ha2, rfl⟩, h2⟩
        exact Finset.mem_sigma.mpr ⟨hj1, Finset.mem_sigma.mpr ⟨Finset.mem_erase.mpr ⟨hneB.symm, hj2⟩,
          Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨ha1, rfl⟩, Finset.mem_filter.mpr ⟨ha2, rfl⟩⟩⟩⟩
      · intro q₁ _ q₂ _ h
        have h_inner : (⟨φ_B (repR q₁.2), (q₁.1, q₁.2)⟩ : Sigma fun _ : Fin P.m => Fin P.m × Fin P.m) =
            ⟨φ_B (repR q₂.2), (q₂.1, q₂.2)⟩ := eq_of_heq (Sigma.ext_iff.mp h).2
        have h2 := eq_of_heq (Sigma.ext_iff.mp h_inner).2
        exact Prod.ext (congrArg Prod.fst h2) (congrArg Prod.snd h2)
    have hreal : (ordKR.card : ℝ) ≤ ∑ w ∈ B₂,
        ∑ j₁ ∈ B.filter (fun j => (graphOf ω_B).Adj w j),
        ∑ j₂ ∈ (B.filter (fun j => (graphOf ω_B).Adj w j)).erase j₁, ((cB j₁ : ℝ) * (cB j₂ : ℝ)) := by
      have hcast : (ordKR.card : ℝ) ≤
          ((∑ w ∈ B₂, ∑ j₁ ∈ B.filter (fun j => (graphOf ω_B).Adj w j),
            ∑ j₂ ∈ (B.filter (fun j => (graphOf ω_B).Adj w j)).erase j₁, (cB j₁ * cB j₂) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      simpa only [Nat.cast_sum, Nat.cast_mul] using hcast
    exact hreal.trans (Finset.sum_le_sum_of_subset_of_nonneg hB₂_sub fun _ _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
  have hout := sum_weighted_pairs_outside_Zbig_le P ω_B hGB hsum_le h2k hcB_lt hTlo hTcut hF_le_mid
    hTbig hBmid hBcross hm_lt_J hL_le_F
  have h2KR_real : 2 * (KR.card : ℝ) ≤ (ordKR.card : ℝ) := by exact_mod_cast h2KR
  linarith

/-- Bundled parameter validity hypotheses for `RegParams` + `F_max`. -/
structure ValidRegParams (P : RegParams) (F_max : ℝ) : Prop where
  hp0 : 0 ≤ P.p
  hp1 : P.p ≤ 1
  hη0 : 0 < P.η₀
  hk1 : 1 ≤ P.k
  h2k : 2 * P.k ≤ P.m
  hL1 : 1 ≤ P.L
  hF1 : 1 ≤ F_max
  hF_lt_L : ∀ x : ℕ, (x : ℝ) ≤ F_max → x < 2 ^ P.L
  hTlo : 0 < P.T_lo
  hTcut : P.T_lo ≤ P.T_cut
  hF_le_mid : F_max ≤ P.T_mid
  hTbig : 0 < P.T_big
  hTmid_lt : P.T_mid < P.T_big / 2
  hTbig_lt_J : P.T_big < ((2 ^ P.J : ℕ) : ℝ)
  hBmid : 0 < P.B_mid
  hBcross : 0 < P.B_cross
  hm_lt_J : P.m < 2 ^ P.J
  hL_le_F : ∀ i : Fin P.L, ((2 ^ i.val : ℕ) : ℝ) ≤ F_max
  hL_le_Tbig : ∀ i : Fin P.L, ((2 ^ i.val : ℕ) : ℝ) ≤ P.T_big

lemma errOut_nonneg (P : RegParams) {F_max : ℝ} (hV : ValidRegParams P F_max) :
    0 ≤ errOut P F_max := by
  have hdeg_nn : 0 ≤ (1 + P.η₀) * ((P.m : ℝ) * P.p) :=
    mul_nonneg (by linarith [hV.hη0]) (mul_nonneg (Nat.cast_nonneg _) hV.hp0)
  have hTmid_pos : 0 < P.T_mid := lt_of_lt_of_le (by linarith [hV.hF1]) hV.hF_le_mid
  have hTcut_pos : 0 < P.T_cut := lt_of_lt_of_le hV.hTlo hV.hTcut
  have hBmid_pos := hV.hBmid
  have hBcross_pos := hV.hBcross
  have hTlo_pos := hV.hTlo
  have hTbig_pos := hV.hTbig
  have hF1 := hV.hF1
  dsimp only [errOut]
  positivity

/-- Auxiliary equivalence reordering `(A₁ ⊕ B₁) ⊕ (A₂ ⊕ B₂) ≃ (A₁ ⊕ A₂) ⊕ (B₁ ⊕ B₂)`. -/
def sumSwapMid {A₁ B₁ A₂ B₂ : Type*} :
    (A₁ ⊕ B₁) ⊕ (A₂ ⊕ B₂) ≃ (A₁ ⊕ A₂) ⊕ (B₁ ⊕ B₂) where
  toFun
    | Sum.inl (Sum.inl a₁) => Sum.inl (Sum.inl a₁)
    | Sum.inl (Sum.inr b₁) => Sum.inr (Sum.inl b₁)
    | Sum.inr (Sum.inl a₂) => Sum.inl (Sum.inr a₂)
    | Sum.inr (Sum.inr b₂) => Sum.inr (Sum.inr b₂)
  invFun
    | Sum.inl (Sum.inl a₁) => Sum.inl (Sum.inl a₁)
    | Sum.inl (Sum.inr a₂) => Sum.inr (Sum.inl a₂)
    | Sum.inr (Sum.inl b₁) => Sum.inl (Sum.inr b₁)
    | Sum.inr (Sum.inr b₂) => Sum.inr (Sum.inr b₂)
  left_inv x := by rcases x with (a₁ | b₁) | (a₂ | b₂) <;> rfl
  right_inv x := by rcases x with (a₁ | a₂) | (b₁ | b₂) <;> rfl

/-- Fixed-`(Z_R, Z_B)` conditional Stage-1 / Stage-2 bound. -/
lemma bernProb_indep_good_fixedZ_le {n : ℕ} (P : RegParams) {F_max T_small lam₁ lam₂ : ℝ}
    (hV : ValidRegParams P F_max) (hTsmall : 0 < T_small) (hlam1 : 0 < lam₁) (hlam2 : 0 < lam₂)
    {I : Finset (Fin n)} (hIk : I.card = P.k) {φ_R φ_B : Fin n → Fin P.m}
    (hfibR : ∀ r : Fin P.m, ((Finset.univ.filter fun v : Fin n => φ_R v = r).card : ℝ) ≤ F_max)
    (hfibB : ∀ j : Fin P.m, ((Finset.univ.filter fun v : Fin n => φ_B v = j).card : ℝ) ≤ F_max)
    (repR repB : Fin P.m → Fin n)
    (hrepRI : ∀ r ∈ I.image φ_R, repR r ∈ I) (hrepREq : ∀ r ∈ I.image φ_R, φ_R (repR r) = r)
    (hrepBI : ∀ j ∈ I.image φ_B, repB j ∈ I) (hrepBEq : ∀ j ∈ I.image φ_B, φ_B (repB j) = j)
    (Z_R Z_B : Finset (Fin P.m)) (hZR_card : Z_R.card ≤ Qmax P) (hZB_card : Z_B.card ≤ Qmax P) :
    let A := I.image φ_R
    let B := I.image φ_B
    let cB : Fin P.m → ℕ := fun j => (A.filter fun r => φ_B (repR r) = j).card
    let cR : Fin P.m → ℕ := fun r => (B.filter fun j => φ_R (repB j) = r).card
    let D := F_max * ((1 + P.η₀) * ((P.m : ℝ) * P.p))
    let M_open :=
      (1 / 2 : ℝ) * max 0 ((A.card : ℝ) ^ 2 - min (((P.k - B.card : ℕ) : ℝ) ^ 2) (D * ((P.k - B.card : ℕ) : ℝ))) +
      (1 / 2 : ℝ) * max 0 ((B.card : ℝ) ^ 2 - min (((P.k - A.card : ℕ) : ℝ) ^ 2) (D * ((P.k - A.card : ℕ) : ℝ))) -
      2 * errOpen P F_max
    bernProb P.p (fun ω : EdgeIdx P.m ⊕ EdgeIdx P.m → Bool =>
      let ω_R := fun e => ω (Sum.inl e)
      let ω_B := fun e => ω (Sum.inr e)
      GoodGraph P ω_R ∧ GoodGraph P ω_B ∧
      (buildGraph (graphOf ω_R) (graphOf ω_B) φ_R φ_B).IsIndepSet (I : Set (Fin n)) ∧
      Z_R = Zbig P ω_R A cR ∩ A ∧ Z_B = Zbig P ω_B B cB ∩ B) ≤
    Real.exp (2 * lam₁ * T_small - P.p * (1 - Real.exp (-lam₁)) * M_open) +
    2 * (Real.exp 1 * (errOut P F_max / 2) * P.p / (⌈T_small / 2⌉₊ : ℝ)) ^ ⌈T_small / 2⌉₊ +
    2 * Real.exp ((Real.exp lam₂ - 1) * P.p * (MtriBound P F_max : ℝ) - lam₂ * (T_small / 2)) := by
  intro A B cB cR D M_open
  set A₂ := A \ Z_R
  set B₂ := B \ Z_B
  set eA := A₂.orderIsoOfFin rfl
  set eB := B₂.orderIsoOfFin rfl
  let ExtR := { e : EdgeIdx P.m // ¬ (e.1.1 ∈ A₂ ∧ e.1.2 ∈ A₂) }
  let ExtB := { e : EdgeIdx P.m // ¬ (e.1.1 ∈ B₂ ∧ e.1.2 ∈ B₂) }
  let eAll : EdgeIdx P.m ⊕ EdgeIdx P.m ≃ (EdgeIdx A₂.card ⊕ EdgeIdx B₂.card) ⊕ (ExtR ⊕ ExtB) :=
    (Equiv.sumCongr (edgeSplitSub A₂) (edgeSplitSub B₂)).trans sumSwapMid
  rw [bernProb_equiv eAll.symm P.p]
  -- Unpack ωL = (ω2_R, ω2_B), ωR = (ω1_R, ω1_B)
  let mkR : (EdgeIdx A₂.card → Bool) → (ExtR → Bool) → (EdgeIdx P.m → Bool) :=
    fun ω2 ω1 e => Sum.casesOn (edgeSplitSub A₂ e) ω2 ω1
  let mkB : (EdgeIdx B₂.card → Bool) → (ExtB → Bool) → (EdgeIdx P.m → Bool) :=
    fun ω2 ω1 e => Sum.casesOn (edgeSplitSub B₂ e) ω2 ω1
  have hmkR_int : ∀ ω2 ω1 (e : EdgeIdx A₂.card), mkR ω2 ω1 ((edgeSplitSub A₂).symm (Sum.inl e)) = ω2 e := by
    intro ω2 ω1 e; simp [mkR]
  have hmkB_int : ∀ ω2 ω1 (e : EdgeIdx B₂.card), mkB ω2 ω1 ((edgeSplitSub B₂).symm (Sum.inl e)) = ω2 e := by
    intro ω2 ω1 e; simp [mkB]
  have hmkR_ext : ∀ ω2 ω1 (x : ExtR), mkR ω2 ω1 x.1 = ω1 x := by
    intro ω2 ω1 x
    dsimp only [mkR]
    have hx : edgeSplitSub A₂ x.1 = Sum.inr x := by simp [edgeSplitSub, x.2]
    rw [hx]
  have hmkB_ext : ∀ ω2 ω1 (x : ExtB), mkB ω2 ω1 x.1 = ω1 x := by
    intro ω2 ω1 x
    dsimp only [mkB]
    have hx : edgeSplitSub B₂ x.1 = Sum.inr x := by simp [edgeSplitSub, x.2]
    rw [hx]
  have hcomp_eq : ∀ (ω : (EdgeIdx A₂.card ⊕ EdgeIdx B₂.card) ⊕ (ExtR ⊕ ExtB) → Bool),
      (fun e => ω (eAll (Sum.inl e))) = mkR (fun e => ω (Sum.inl (Sum.inl e))) (fun x => ω (Sum.inr (Sum.inl x))) ∧
      (fun e => ω (eAll (Sum.inr e))) = mkB (fun e => ω (Sum.inl (Sum.inr e))) (fun x => ω (Sum.inr (Sum.inr x))) := by
    intro ω; constructor
    · funext e; dsimp only [eAll, mkR, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl]
      cases h : edgeSplitSub A₂ e with
      | inl v => simp [sumSwapMid, h]
      | inr v => simp [sumSwapMid, h]
    · funext e; dsimp only [eAll, mkB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr]
      cases h : edgeSplitSub B₂ e with
      | inl v => simp [sumSwapMid, h]
      | inr v => simp [sumSwapMid, h]
  have hrewrite : ∀ ω : (EdgeIdx A₂.card ⊕ EdgeIdx B₂.card) ⊕ (ExtR ⊕ ExtB) → Bool,
      let ωL := fun a => ω (Sum.inl a)
      let ω1 := fun b => ω (Sum.inr b)
      let ω_R := mkR (fun e => ωL (Sum.inl e)) (fun x => ω1 (Sum.inl x))
      let ω_B := mkB (fun e => ωL (Sum.inr e)) (fun x => ω1 (Sum.inr x))
      ((GoodGraph P (fun e => (ω ∘ eAll) (Sum.inl e)) ∧ GoodGraph P (fun e => (ω ∘ eAll) (Sum.inr e)) ∧
        (buildGraph (graphOf (fun e => (ω ∘ eAll) (Sum.inl e)))
          (graphOf (fun e => (ω ∘ eAll) (Sum.inr e))) φ_R φ_B).IsIndepSet (I : Set (Fin n)) ∧
        Z_R = Zbig P (fun e => (ω ∘ eAll) (Sum.inl e)) A cR ∩ A ∧
        Z_B = Zbig P (fun e => (ω ∘ eAll) (Sum.inr e)) B cB ∩ B) →
      (GoodGraph P ω_R ∧ GoodGraph P ω_B ∧
        (buildGraph (graphOf ω_R) (graphOf ω_B) φ_R φ_B).IsIndepSet (I : Set (Fin n)) ∧
        Z_R = Zbig P ω_R A cR ∩ A ∧ Z_B = Zbig P ω_B B cB ∩ B)) := by
    intro ω
    rcases hcomp_eq ω with ⟨hR, hB⟩
    simp only [Function.comp, hR, hB]
    exact id
  refine (bernProb_mono hV.hp0 hV.hp1 hrewrite).trans ?_
  refine bernProb_sum_cond_le hV.hp0 hV.hp1 (fun ωL ω1 =>
    let ω_R := mkR (fun e => ωL (Sum.inl e)) (fun x => ω1 (Sum.inl x))
    let ω_B := mkB (fun e => ωL (Sum.inr e)) (fun x => ω1 (Sum.inr x))
    GoodGraph P ω_R ∧ GoodGraph P ω_B ∧
    (buildGraph (graphOf ω_R) (graphOf ω_B) φ_R φ_B).IsIndepSet (I : Set (Fin n)) ∧
    Z_R = Zbig P ω_R A cR ∩ A ∧ Z_B = Zbig P ω_B B cB ∩ B) fun ω1 => ?_
  let ω1_R : ExtR → Bool := fun x => ω1 (Sum.inl x)
  let ω1_B : ExtB → Bool := fun x => ω1 (Sum.inr x)
  let ωR₀ := mkR (fun _ => false) ω1_R
  let ωB₀ := mkB (fun _ => false) ω1_B
  -- Define Stage-1 open sets purely from (ωR₀, ωB₀)
  let openR : Finset (EdgeIdx A₂.card) := Finset.univ.filter fun e =>
    let r₁ := (eA e.1.1).1
    let r₂ := (eA e.1.2).1
    φ_B (repR r₁) ∉ Z_B ∧ φ_B (repR r₂) ∉ Z_B ∧ φ_B (repR r₁) ≠ φ_B (repR r₂) ∧
    (¬ ∃ z : Fin P.m, z ∉ A₂ ∧ (graphOf ωR₀).Adj z r₁ ∧ (graphOf ωR₀).Adj z r₂) ∧
    (¬ ∃ w : Fin P.m, w ∉ B₂ ∧ (graphOf ωB₀).Adj w (φ_B (repR r₁)) ∧ (graphOf ωB₀).Adj w (φ_B (repR r₂)))
  let openB : Finset (EdgeIdx B₂.card) := Finset.univ.filter fun e =>
    let j₁ := (eB e.1.1).1
    let j₂ := (eB e.1.2).1
    φ_R (repB j₁) ∉ Z_R ∧ φ_R (repB j₂) ∉ Z_R ∧ φ_R (repB j₁) ≠ φ_R (repB j₂) ∧
    (¬ ∃ w : Fin P.m, w ∉ B₂ ∧ (graphOf ωB₀).Adj w j₁ ∧ (graphOf ωB₀).Adj w j₂) ∧
    (¬ ∃ z : Fin P.m, z ∉ A₂ ∧ (graphOf ωR₀).Adj z (φ_R (repB j₁)) ∧ (graphOf ωR₀).Adj z (φ_R (repB j₂)))
  -- Exterior edges of (mkR ω2_R ω1_R, mkB ω2_B ω1_B) match (ωR₀, ωB₀)
  have hopenR_eq : ∀ ω2_R ω2_B,
      (Finset.univ.filter fun e : EdgeIdx A₂.card =>
        let r₁ := (eA e.1.1).1
        let r₂ := (eA e.1.2).1
        φ_B (repR r₁) ∉ Z_B ∧ φ_B (repR r₂) ∉ Z_B ∧ φ_B (repR r₁) ≠ φ_B (repR r₂) ∧
        (¬ ∃ z : Fin P.m, z ∉ A₂ ∧ (graphOf (mkR ω2_R ω1_R)).Adj z r₁ ∧ (graphOf (mkR ω2_R ω1_R)).Adj z r₂) ∧
        (¬ ∃ w : Fin P.m, w ∉ B₂ ∧ (graphOf (mkB ω2_B ω1_B)).Adj w (φ_B (repR r₁)) ∧
          (graphOf (mkB ω2_B ω1_B)).Adj w (φ_B (repR r₂)))) = openR := by
    intro ω2_R ω2_B
    ext e; simp only [openR, Finset.mem_filter, Finset.mem_univ, true_and]
    refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => and_congr ?_ ?_
    · refine not_congr (exists_congr fun z => and_congr_right fun hz => and_congr ?_ ?_)
      · exact graphOf_edgeSplitSub_ext A₂ _ _ (fun x => by dsimp only [ωR₀]; rw [hmkR_ext, hmkR_ext]) (fun h => hz h.1)
      · exact graphOf_edgeSplitSub_ext A₂ _ _ (fun x => by dsimp only [ωR₀]; rw [hmkR_ext, hmkR_ext]) (fun h => hz h.1)
    · refine not_congr (exists_congr fun w => and_congr_right fun hw => and_congr ?_ ?_)
      · exact graphOf_edgeSplitSub_ext B₂ _ _ (fun x => by dsimp only [ωB₀]; rw [hmkB_ext, hmkB_ext]) (fun h => hw h.1)
      · exact graphOf_edgeSplitSub_ext B₂ _ _ (fun x => by dsimp only [ωB₀]; rw [hmkB_ext, hmkB_ext]) (fun h => hw h.1)
  have hopenB_eq : ∀ ω2_R ω2_B,
      (Finset.univ.filter fun e : EdgeIdx B₂.card =>
        let j₁ := (eB e.1.1).1
        let j₂ := (eB e.1.2).1
        φ_R (repB j₁) ∉ Z_R ∧ φ_R (repB j₂) ∉ Z_R ∧ φ_R (repB j₁) ≠ φ_R (repB j₂) ∧
        (¬ ∃ w : Fin P.m, w ∉ B₂ ∧ (graphOf (mkB ω2_B ω1_B)).Adj w j₁ ∧ (graphOf (mkB ω2_B ω1_B)).Adj w j₂) ∧
        (¬ ∃ z : Fin P.m, z ∉ A₂ ∧ (graphOf (mkR ω2_R ω1_R)).Adj z (φ_R (repB j₁)) ∧
          (graphOf (mkR ω2_R ω1_R)).Adj z (φ_R (repB j₂)))) = openB := by
    intro ω2_R ω2_B
    ext e; simp only [openB, Finset.mem_filter, Finset.mem_univ, true_and]
    refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => and_congr ?_ ?_
    · refine not_congr (exists_congr fun w => and_congr_right fun hw => and_congr ?_ ?_)
      · exact graphOf_edgeSplitSub_ext B₂ _ _ (fun x => by dsimp only [ωB₀]; rw [hmkB_ext, hmkB_ext]) (fun h => hw h.1)
      · exact graphOf_edgeSplitSub_ext B₂ _ _ (fun x => by dsimp only [ωB₀]; rw [hmkB_ext, hmkB_ext]) (fun h => hw h.1)
    · refine not_congr (exists_congr fun z => and_congr_right fun hz => and_congr ?_ ?_)
      · exact graphOf_edgeSplitSub_ext A₂ _ _ (fun x => by dsimp only [ωR₀]; rw [hmkR_ext, hmkR_ext]) (fun h => hz h.1)
      · exact graphOf_edgeSplitSub_ext A₂ _ _ (fun x => by dsimp only [ωR₀]; rw [hmkR_ext, hmkR_ext]) (fun h => hz h.1)
  by_cases hopen_ok : M_open ≤ (openR.card : ℝ) + (openB.card : ℝ)
  · -- Define Stage-2 killer sets KR(ω2_B) and KB(ω2_R)
    let KR : (EdgeIdx B₂.card → Bool) → Finset (EdgeIdx A₂.card) := fun ω2_B =>
      Finset.univ.filter fun e =>
        let r₁ := (eA e.1.1).1
        let r₂ := (eA e.1.2).1
        ∃ h1 : φ_B (repR r₁) ∈ B₂, ∃ h2 : φ_B (repR r₂) ∈ B₂,
          φ_B (repR r₁) ≠ φ_B (repR r₂) ∧
          ∃ w : Fin B₂.card,
            (graphOf ω2_B).Adj w (eB.symm ⟨φ_B (repR r₁), h1⟩) ∧
            (graphOf ω2_B).Adj w (eB.symm ⟨φ_B (repR r₂), h2⟩)
    let KB : (EdgeIdx A₂.card → Bool) → Finset (EdgeIdx B₂.card) := fun ω2_R =>
      Finset.univ.filter fun e =>
        let j₁ := (eB e.1.1).1
        let j₂ := (eB e.1.2).1
        ∃ h1 : φ_R (repB j₁) ∈ A₂, ∃ h2 : φ_R (repB j₂) ∈ A₂,
          φ_R (repB j₁) ≠ φ_R (repB j₂) ∧
          ∃ z : Fin A₂.card,
            (graphOf ω2_R).Adj z (eA.symm ⟨φ_R (repB j₁), h1⟩) ∧
            (graphOf ω2_R).Adj z (eA.symm ⟨φ_R (repB j₂), h2⟩)
    have himp_stage2 : ∀ ωL : EdgeIdx A₂.card ⊕ EdgeIdx B₂.card → Bool,
        let ω2_R := fun e => ωL (Sum.inl e)
        let ω2_B := fun e => ωL (Sum.inr e)
        let ω_R := mkR ω2_R ω1_R
        let ω_B := mkB ω2_B ω1_B
        (GoodGraph P ω_R ∧ GoodGraph P ω_B ∧
          (buildGraph (graphOf ω_R) (graphOf ω_B) φ_R φ_B).IsIndepSet (I : Set (Fin n)) ∧
          Z_R = Zbig P ω_R A cR ∩ A ∧ Z_B = Zbig P ω_B B cB ∩ B) →
        ((∀ e ∈ openR, ω2_R e = true → ¬ (pruneTri (graphOf ω2_R)).Adj e.1.1 e.1.2 ∨ e ∈ KR ω2_B) ∧
         (∀ e ∈ openB, ω2_B e = true → ¬ (pruneTri (graphOf ω2_B)).Adj e.1.1 e.1.2 ∨ e ∈ KB ω2_R) ∧
         ((KR ω2_B).card : ℝ) ≤ errOut P F_max / 2 ∧
         ((KB ω2_R).card : ℝ) ≤ errOut P F_max / 2 ∧
         (∑ i : Fin A₂.card, (triCand ω2_R i).card ≤ MtriBound P F_max) ∧
         (∑ i : Fin B₂.card, (triCand ω2_B i).card ≤ MtriBound P F_max)) := by
      intro ωL; dsimp only; rintro ⟨hGR, hGB, hindep, hZR_eq, hZB_eq⟩
      set ω2_R := fun e => ωL (Sum.inl e)
      set ω2_B := fun e => ωL (Sum.inr e)
      set ω_R := mkR ω2_R ω1_R
      set ω_B := mkB ω2_B ω1_B
      have hA_le_k : A.card ≤ P.k := by rw [← hIk]; exact Finset.card_image_le
      have hB_le_k : B.card ≤ P.k := by rw [← hIk]; exact Finset.card_image_le
      have hωInR : (fun e => ω_R ((edgeSplitSub A₂).symm (Sum.inl e))) = ω2_R := funext (hmkR_int ω2_R ω1_R)
      have hωInB : (fun e => ω_B ((edgeSplitSub B₂).symm (Sum.inl e))) = ω2_B := funext (hmkB_int ω2_B ω1_B)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- Red open edges killed by TriKill_R or KR
        intro e he htrue
        rw [← hopenR_eq ω2_R ω2_B] at he
        rcases (Finset.mem_filter.mp he).2 with ⟨hb1, hb2, hneB, hnoExtR, hnoExtB⟩
        by_cases hpr : (pruneTri (graphOf ω2_R)).Adj e.1.1 e.1.2
        · right
          set r₁ := (eA e.1.1).1
          set r₂ := (eA e.1.2).1
          have hr1A : r₁ ∈ A := (Finset.mem_sdiff.mp (eA e.1.1).2).1
          have hr2A : r₂ ∈ A := (Finset.mem_sdiff.mp (eA e.1.2).2).1
          have hpruneR : (pruneTri (graphOf ω_R)).Adj r₁ r₂ := by
            have hpr' : (pruneTri (graphOf (fun e' => ω_R ((edgeSplitSub A₂).symm (Sum.inl e'))))).Adj e.1.1 e.1.2 := by
              rwa [hωInR]
            exact pruneTri_of_int_no_ext A₂ ω_R e.2 hnoExtR hpr'
          have hne_u : repR r₁ ≠ repR r₂ := fun heq => by
            have h1 := hrepREq r₁ hr1A; have h2 := hrepREq r₂ hr2A
            rw [heq] at h1
            exact (eA.strictMono e.2).ne (Subtype.ext (h1.symm.trans h2))
          have hnot_adj : ¬ (buildGraph (graphOf ω_R) (graphOf ω_B) φ_R φ_B).Adj (repR r₁) (repR r₂) :=
            hindep (hrepRI r₁ hr1A) (hrepRI r₂ hr2A) hne_u
          have hpb : pairBad (graphOf ω_B) φ_B (repR r₁) (repR r₂) := by
            by_contra hnotpb
            exact hnot_adj (Or.inl ⟨by rwa [hrepREq r₁ hr1A, hrepREq r₂ hr2A], hnotpb⟩)
          rcases hpb with heqB | ⟨w, hw1, hw2⟩
          · exact False.elim (hneB heqB)
          · have hwB₂ : w ∈ B₂ := by
              by_contra hwNot
              exact hnoExtB ⟨w, hwNot, hw1.symm, hw2.symm⟩
            have h1B₂ : φ_B (repR r₁) ∈ B₂ :=
              Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨repR r₁, hrepRI r₁ hr1A, rfl⟩, hb1⟩
            have h2B₂ : φ_B (repR r₂) ∈ B₂ :=
              Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨repR r₂, hrepRI r₂ hr2A, rfl⟩, hb2⟩
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1B₂, h2B₂, hneB, eB.symm ⟨w, hwB₂⟩, ?_, ?_⟩
            · have h1 := (graphOf_edgeSplitSub_int B₂ ω_B (eB.symm ⟨w, hwB₂⟩) (eB.symm ⟨φ_B (repR r₁), h1B₂⟩)).mp
              rw [hωInB] at h1
              refine h1 ?_
              change (graphOf ω_B).Adj (eB (eB.symm ⟨w, hwB₂⟩)).1 (eB (eB.symm ⟨φ_B (repR r₁), h1B₂⟩)).1
              rw [eB.apply_symm_apply, eB.apply_symm_apply]
              exact hw1.symm
            · have h2 := (graphOf_edgeSplitSub_int B₂ ω_B (eB.symm ⟨w, hwB₂⟩) (eB.symm ⟨φ_B (repR r₂), h2B₂⟩)).mp
              rw [hωInB] at h2
              refine h2 ?_
              change (graphOf ω_B).Adj (eB (eB.symm ⟨w, hwB₂⟩)).1 (eB (eB.symm ⟨φ_B (repR r₂), h2B₂⟩)).1
              rw [eB.apply_symm_apply, eB.apply_symm_apply]
              exact hw2.symm
        · exact Or.inl hpr
      · -- Blue open edges killed by TriKill_B or KB
        intro e he htrue
        rw [← hopenB_eq ω2_R ω2_B] at he
        rcases (Finset.mem_filter.mp he).2 with ⟨hr1, hr2, hneR, hnoExtB, hnoExtR⟩
        by_cases hpr : (pruneTri (graphOf ω2_B)).Adj e.1.1 e.1.2
        · right
          set j₁ := (eB e.1.1).1
          set j₂ := (eB e.1.2).1
          have hj1B : j₁ ∈ B := (Finset.mem_sdiff.mp (eB e.1.1).2).1
          have hj2B : j₂ ∈ B := (Finset.mem_sdiff.mp (eB e.1.2).2).1
          have hpruneB : (pruneTri (graphOf ω_B)).Adj j₁ j₂ := by
            have hpr' : (pruneTri (graphOf (fun e' => ω_B ((edgeSplitSub B₂).symm (Sum.inl e'))))).Adj e.1.1 e.1.2 := by
              rwa [hωInB]
            exact pruneTri_of_int_no_ext B₂ ω_B e.2 hnoExtB hpr'
          have hne_u : repB j₁ ≠ repB j₂ := fun heq => by
            have h1 := hrepBEq j₁ hj1B; have h2 := hrepBEq j₂ hj2B
            rw [heq] at h1
            exact (eB.strictMono e.2).ne (Subtype.ext (h1.symm.trans h2))
          have hnot_adj : ¬ (buildGraph (graphOf ω_R) (graphOf ω_B) φ_R φ_B).Adj (repB j₁) (repB j₂) :=
            hindep (hrepBI j₁ hj1B) (hrepBI j₂ hj2B) hne_u
          have hpb : pairBad (graphOf ω_R) φ_R (repB j₁) (repB j₂) := by
            by_contra hnotpb
            exact hnot_adj (Or.inr ⟨by rwa [hrepBEq j₁ hj1B, hrepBEq j₂ hj2B], hnotpb⟩)
          rcases hpb with heqR | ⟨z, hz1, hz2⟩
          · exact False.elim (hneR heqR)
          · have hzA₂ : z ∈ A₂ := by
              by_contra hzNot
              exact hnoExtR ⟨z, hzNot, hz1.symm, hz2.symm⟩
            have h1A₂ : φ_R (repB j₁) ∈ A₂ :=
              Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨repB j₁, hrepBI j₁ hj1B, rfl⟩, hr1⟩
            have h2A₂ : φ_R (repB j₂) ∈ A₂ :=
              Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨repB j₂, hrepBI j₂ hj2B, rfl⟩, hr2⟩
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1A₂, h2A₂, hneR, eA.symm ⟨z, hzA₂⟩, ?_, ?_⟩
            · have h1 := (graphOf_edgeSplitSub_int A₂ ω_R (eA.symm ⟨z, hzA₂⟩) (eA.symm ⟨φ_R (repB j₁), h1A₂⟩)).mp
              rw [hωInR] at h1
              refine h1 ?_
              change (graphOf ω_R).Adj (eA (eA.symm ⟨z, hzA₂⟩)).1 (eA (eA.symm ⟨φ_R (repB j₁), h1A₂⟩)).1
              rw [eA.apply_symm_apply, eA.apply_symm_apply]
              exact hz1.symm
            · have h2 := (graphOf_edgeSplitSub_int A₂ ω_R (eA.symm ⟨z, hzA₂⟩) (eA.symm ⟨φ_R (repB j₂), h2A₂⟩)).mp
              rw [hωInR] at h2
              refine h2 ?_
              change (graphOf ω_R).Adj (eA (eA.symm ⟨z, hzA₂⟩)).1 (eA (eA.symm ⟨φ_R (repB j₂), h2A₂⟩)).1
              rw [eA.apply_symm_apply, eA.apply_symm_apply]
              exact hz2.symm
        · exact Or.inl hpr
      · -- |KR ω2_B| ≤ errOut / 2
        have hK := card_KR_le P ω_B hGB hIk hfibB repR hrepRI hrepREq Z_R Z_B hZB_eq
          hV.h2k hV.hF_lt_L hV.hTlo hV.hTcut hV.hF_le_mid hV.hTbig hV.hBmid hV.hBcross hV.hm_lt_J hV.hL_le_F
        dsimp only at hK
        rw [hωInB] at hK
        exact hK
      · -- |KB ω2_R| ≤ errOut / 2
        have hK := card_KR_le P ω_R hGR hIk hfibR repB hrepBI hrepBEq Z_B Z_R hZR_eq
          hV.h2k hV.hF_lt_L hV.hTlo hV.hTcut hV.hF_le_mid hV.hTbig hV.hBmid hV.hBcross hV.hm_lt_J hV.hL_le_F
        dsimp only at hK
        rw [hωInR] at hK
        exact hK
      · -- triCand R ≤ MtriBound
        have htri := sum_triCand_sub_le P ω_R hGR (A₂ := A₂) Finset.sdiff_subset hA_le_k hV.h2k hV.hL1
          hV.hTlo hV.hTcut hV.hF_le_mid hV.hTbig hV.hTmid_lt hV.hTbig_lt_J hV.hBmid hV.hBcross
          hV.hm_lt_J hV.hL_le_F hV.hL_le_Tbig
        simpa only [hωInR] using htri
      · -- triCand B ≤ MtriBound
        have htri := sum_triCand_sub_le P ω_B hGB (A₂ := B₂) Finset.sdiff_subset hB_le_k hV.h2k hV.hL1
          hV.hTlo hV.hTcut hV.hF_le_mid hV.hTbig hV.hTmid_lt hV.hTbig_lt_J hV.hBmid hV.hBcross
          hV.hm_lt_J hV.hL_le_F hV.hL_le_Tbig
        simpa only [hωInB] using htri
    have heo_nn : 0 ≤ errOut P F_max / 2 := div_nonneg (errOut_nonneg P hV) (by norm_num)
    exact (bernProb_mono hV.hp0 hV.hp1 himp_stage2).trans
      (bernProb_stage2_five_events hV.hp0 hV.hp1 hlam1 hlam2 hTsmall heo_nn openR openB hopen_ok KR KB)
  · -- Impossible branch: M_open > |openR| + |openB| contradicts GoodGraph R ∧ GoodGraph B!
    have h0 : bernProb P.p (fun ωL : EdgeIdx A₂.card ⊕ EdgeIdx B₂.card → Bool =>
        let ω_R := mkR (fun e => ωL (Sum.inl e)) ω1_R
        let ω_B := mkB (fun e => ωL (Sum.inr e)) ω1_B
        GoodGraph P ω_R ∧ GoodGraph P ω_B ∧
        (buildGraph (graphOf ω_R) (graphOf ω_B) φ_R φ_B).IsIndepSet (I : Set (Fin n)) ∧
        Z_R = Zbig P ω_R A cR ∩ A ∧ Z_B = Zbig P ω_B B cB ∩ B) = 0 := by
      simp only [bernProb]
      refine Finset.sum_eq_zero fun ωL _ => if_neg fun ⟨hGR, hGB, _, _, _⟩ => hopen_ok ?_
      have hoR := card_openR_ge P (mkR (fun e => ωL (Sum.inl e)) ω1_R) (mkB (fun e => ωL (Sum.inr e)) ω1_B)
        hGR hGB hIk hfibB repR hrepRI hrepREq Z_R Z_B hZR_card hZB_card hV.h2k hV.hL1 hV.hF1 hV.hF_lt_L
        hV.hTlo hV.hTcut hV.hF_le_mid hV.hTbig hV.hTmid_lt hV.hTbig_lt_J hV.hBmid hV.hBcross hV.hm_lt_J
        hV.hL_le_F hV.hL_le_Tbig
      have hoB := card_openR_ge P (mkB (fun e => ωL (Sum.inr e)) ω1_B) (mkR (fun e => ωL (Sum.inl e)) ω1_R)
        hGB hGR hIk hfibR repB hrepBI hrepBEq Z_B Z_R hZB_card hZR_card hV.h2k hV.hL1 hV.hF1 hV.hF_lt_L
        hV.hTlo hV.hTcut hV.hF_le_mid hV.hTbig hV.hTmid_lt hV.hTbig_lt_J hV.hBmid hV.hBcross hV.hm_lt_J
        hV.hL_le_F hV.hL_le_Tbig
      dsimp only at hoR hoB
      rw [hopenR_eq] at hoR
      rw [hopenB_eq] at hoB
      dsimp only [M_open, D] at *
      linarith only [hoR, hoB]
    rw [h0]
    have heo_nn : 0 ≤ errOut P F_max := errOut_nonneg P hV
    exact add_nonneg
      (add_nonneg (Real.exp_pos _).le
        (mul_nonneg (by norm_num)
          (pow_nonneg (div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le
            (div_nonneg heo_nn (by norm_num))) hV.hp0) (Nat.cast_nonneg _)) _)))
      (mul_nonneg (by norm_num) (Real.exp_pos _).le)

/-- Master Section-3 theorem: for fixed `I` of size `k` and fiber-good `(φ_R, φ_B)`, bound
`P_{G_R, G_B}(GoodGraph R ∧ GoodGraph B ∧ IsIndepSet I)` by summing over `(Z_R, Z_B)`. -/
lemma bernProb_indep_good_le {n : ℕ} (P : RegParams) {F_max T_small lam₁ lam₂ : ℝ}
    (hV : ValidRegParams P F_max) (hTsmall : 0 < T_small) (hlam1 : 0 < lam₁) (hlam2 : 0 < lam₂)
    {I : Finset (Fin n)} (hIk : I.card = P.k) {φ_R φ_B : Fin n → Fin P.m}
    (hfibR : ∀ r : Fin P.m, ((Finset.univ.filter fun v : Fin n => φ_R v = r).card : ℝ) ≤ F_max)
    (hfibB : ∀ j : Fin P.m, ((Finset.univ.filter fun v : Fin n => φ_B v = j).card : ℝ) ≤ F_max) :
    let A := I.image φ_R
    let B := I.image φ_B
    let D := F_max * ((1 + P.η₀) * ((P.m : ℝ) * P.p))
    let M_open :=
      (1 / 2 : ℝ) * max 0 ((A.card : ℝ) ^ 2 - min (((P.k - B.card : ℕ) : ℝ) ^ 2) (D * ((P.k - B.card : ℕ) : ℝ))) +
      (1 / 2 : ℝ) * max 0 ((B.card : ℝ) ^ 2 - min (((P.k - A.card : ℕ) : ℝ) ^ 2) (D * ((P.k - A.card : ℕ) : ℝ))) -
      2 * errOpen P F_max
    bernProb P.p (fun ω : EdgeIdx P.m ⊕ EdgeIdx P.m → Bool =>
      let ω_R := fun e => ω (Sum.inl e)
      let ω_B := fun e => ω (Sum.inr e)
      GoodGraph P ω_R ∧ GoodGraph P ω_B ∧
      (buildGraph (graphOf ω_R) (graphOf ω_B) φ_R φ_B).IsIndepSet (I : Set (Fin n))) ≤
    (((Qmax P + 1 : ℕ) : ℝ) * ((P.k + 1 : ℕ) : ℝ) ^ Qmax P) ^ 2 * (
      Real.exp (2 * lam₁ * T_small - P.p * (1 - Real.exp (-lam₁)) * M_open) +
      2 * (Real.exp 1 * (errOut P F_max / 2) * P.p / (⌈T_small / 2⌉₊ : ℝ)) ^ ⌈T_small / 2⌉₊ +
      2 * Real.exp ((Real.exp lam₂ - 1) * P.p * (MtriBound P F_max : ℝ) - lam₂ * (T_small / 2))) := by
  intro A B D M_open
  obtain ⟨v₀, hv₀⟩ := Finset.card_pos.mp (show 0 < I.card by have := hV.hk1; omega)
  have hexR : ∀ r : Fin P.m, r ∈ A → ∃ v ∈ I, φ_R v = r := fun r hr => Finset.mem_image.mp hr
  have hexB : ∀ j : Fin P.m, j ∈ B → ∃ v ∈ I, φ_B v = j := fun j hj => Finset.mem_image.mp hj
  let repR : Fin P.m → Fin n := fun r => if h : r ∈ A then (hexR r h).choose else v₀
  let repB : Fin P.m → Fin n := fun j => if h : j ∈ B then (hexB j h).choose else v₀
  have hrepRI : ∀ r ∈ A, repR r ∈ I := fun r hr => by simp only [repR, dif_pos hr]; exact (hexR r hr).choose_spec.1
  have hrepREq : ∀ r ∈ A, φ_R (repR r) = r := fun r hr => by simp only [repR, dif_pos hr]; exact (hexR r hr).choose_spec.2
  have hrepBI : ∀ j ∈ B, repB j ∈ I := fun j hj => by simp only [repB, dif_pos hj]; exact (hexB j hj).choose_spec.1
  have hrepBEq : ∀ j ∈ B, φ_B (repB j) = j := fun j hj => by simp only [repB, dif_pos hj]; exact (hexB j hj).choose_spec.2
  let cB : Fin P.m → ℕ := fun j => (A.filter fun r => φ_B (repR r) = j).card
  let cR : Fin P.m → ℕ := fun r => (B.filter fun j => φ_R (repB j) = r).card
  have hA_le_k : A.card ≤ P.k := by rw [← hIk]; exact Finset.card_image_le
  have hB_le_k : B.card ≤ P.k := by rw [← hIk]; exact Finset.card_image_le
  obtain ⟨hsum_cB, _, _⟩ := rep_weight_bounds hfibB repR hrepRI hrepREq
  obtain ⟨hsum_cR, _, _⟩ := rep_weight_bounds hfibR repB hrepBI hrepBEq
  have hsum_cB_le : ∑ j ∈ B, cB j ≤ P.k := by rw [hsum_cB]; exact hA_le_k
  have hsum_cR_le : ∑ r ∈ A, cR r ≤ P.k := by rw [hsum_cR]; exact hB_le_k
  let candsR := A.powerset.filter fun Z => Z.card ≤ Qmax P
  let candsB := B.powerset.filter fun Z => Z.card ≤ Qmax P
  have hcov : ∀ ω : EdgeIdx P.m ⊕ EdgeIdx P.m → Bool,
      let ω_R := fun e => ω (Sum.inl e)
      let ω_B := fun e => ω (Sum.inr e)
      (GoodGraph P ω_R ∧ GoodGraph P ω_B ∧
        (buildGraph (graphOf ω_R) (graphOf ω_B) φ_R φ_B).IsIndepSet (I : Set (Fin n))) →
      ∃ q : { Z // Z ∈ candsR } × { Z // Z ∈ candsB },
        GoodGraph P ω_R ∧ GoodGraph P ω_B ∧
        (buildGraph (graphOf ω_R) (graphOf ω_B) φ_R φ_B).IsIndepSet (I : Set (Fin n)) ∧
        q.1.1 = Zbig P ω_R A cR ∩ A ∧ q.2.1 = Zbig P ω_B B cB ∩ B := by
    intro ω; dsimp only; rintro ⟨hGR, hGB, hindep⟩
    set ω_R := fun e => ω (Sum.inl e)
    set ω_B := fun e => ω (Sum.inr e)
    have hZR_le : (Zbig P ω_R A cR ∩ A).card ≤ Qmax P := by
      have h1 : ((Zbig P ω_R A cR ∩ A).card : ℝ) ≤ ((Zbig P ω_R A cR).card : ℝ) := by
        exact_mod_cast Finset.card_le_card Finset.inter_subset_left
      have h2 := card_Zbig_le P ω_R hGR.2.2.2.1 hsum_cR_le hV.hTbig hV.hTmid_lt hV.hTbig_lt_J hV.hL_le_Tbig
      dsimp only [Qmax]
      exact Nat.cast_le (α := ℝ).mp ((h1.trans h2).trans (Nat.le_ceil _))
    have hZB_le : (Zbig P ω_B B cB ∩ B).card ≤ Qmax P := by
      have h1 : ((Zbig P ω_B B cB ∩ B).card : ℝ) ≤ ((Zbig P ω_B B cB).card : ℝ) := by
        exact_mod_cast Finset.card_le_card Finset.inter_subset_left
      have h2 := card_Zbig_le P ω_B hGB.2.2.2.1 hsum_cB_le hV.hTbig hV.hTmid_lt hV.hTbig_lt_J hV.hL_le_Tbig
      dsimp only [Qmax]
      exact Nat.cast_le (α := ℝ).mp ((h1.trans h2).trans (Nat.le_ceil _))
    have hZR_mem : Zbig P ω_R A cR ∩ A ∈ candsR :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, hZR_le⟩
    have hZB_mem : Zbig P ω_B B cB ∩ B ∈ candsB :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, hZB_le⟩
    exact ⟨(⟨Zbig P ω_R A cR ∩ A, hZR_mem⟩, ⟨Zbig P ω_B B cB ∩ B, hZB_mem⟩), hGR, hGB, hindep, rfl, rfl⟩
  refine (bernProb_mono hV.hp0 hV.hp1 hcov).trans ?_
  refine (bernProb_exists_univ_le hV.hp0 hV.hp1 _).trans ?_
  set rhs :=
    Real.exp (2 * lam₁ * T_small - P.p * (1 - Real.exp (-lam₁)) * M_open) +
    2 * (Real.exp 1 * (errOut P F_max / 2) * P.p / (⌈T_small / 2⌉₊ : ℝ)) ^ ⌈T_small / 2⌉₊ +
    2 * Real.exp ((Real.exp lam₂ - 1) * P.p * (MtriBound P F_max : ℝ) - lam₂ * (T_small / 2))
  have hrhs_nn : 0 ≤ rhs := by
    have heo_nn : 0 ≤ errOut P F_max := errOut_nonneg P hV
    dsimp only [rhs]
    exact add_nonneg
      (add_nonneg (Real.exp_pos _).le
        (mul_nonneg (by norm_num)
          (pow_nonneg (div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le
            (div_nonneg heo_nn (by norm_num))) hV.hp0) (Nat.cast_nonneg _)) _)))
      (mul_nonneg (by norm_num) (Real.exp_pos _).le)
  have hsingle : ∀ q : { Z // Z ∈ candsR } × { Z // Z ∈ candsB },
      bernProb P.p (fun ω : EdgeIdx P.m ⊕ EdgeIdx P.m → Bool =>
        let ω_R := fun e => ω (Sum.inl e)
        let ω_B := fun e => ω (Sum.inr e)
        GoodGraph P ω_R ∧ GoodGraph P ω_B ∧
        (buildGraph (graphOf ω_R) (graphOf ω_B) φ_R φ_B).IsIndepSet (I : Set (Fin n)) ∧
        q.1.1 = Zbig P ω_R A cR ∩ A ∧ q.2.1 = Zbig P ω_B B cB ∩ B) ≤ rhs := by
    intro ⟨⟨Z_R, hZR⟩, ⟨Z_B, hZB⟩⟩
    exact bernProb_indep_good_fixedZ_le P hV hTsmall hlam1 hlam2 hIk hfibR hfibB repR repB
      hrepRI hrepREq hrepBI hrepBEq Z_R Z_B (Finset.mem_filter.mp hZR).2 (Finset.mem_filter.mp hZB).2
  have hcR_le : (candsR.card : ℝ) ≤ ((Qmax P + 1 : ℕ) : ℝ) * ((P.k + 1 : ℕ) : ℝ) ^ Qmax P := by
    refine (card_powerset_card_le A (Qmax P)).trans ?_
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _) (Nat.cast_nonneg _)
    exact_mod_cast (by omega : A.card + 1 ≤ P.k + 1)
  have hcB_le : (candsB.card : ℝ) ≤ ((Qmax P + 1 : ℕ) : ℝ) * ((P.k + 1 : ℕ) : ℝ) ^ Qmax P := by
    refine (card_powerset_card_le B (Qmax P)).trans ?_
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _) (Nat.cast_nonneg _)
    exact_mod_cast (by omega : B.card + 1 ≤ P.k + 1)
  calc ∑ q : { Z // Z ∈ candsR } × { Z // Z ∈ candsB }, _
      ≤ ∑ _q : { Z // Z ∈ candsR } × { Z // Z ∈ candsB }, rhs := Finset.sum_le_sum fun q _ => hsingle q
    _ = ((candsR.card : ℝ) * (candsB.card : ℝ)) * rhs := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_coe, Fintype.card_coe,
          nsmul_eq_mul, Nat.cast_mul]
    _ ≤ (((Qmax P + 1 : ℕ) : ℝ) * ((P.k + 1 : ℕ) : ℝ) ^ Qmax P) ^ 2 * rhs := by
        rw [sq]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hcR_le hcB_le (Nat.cast_nonneg _) (by positivity)) hrhs_nn

end JointIndepAssembly

/- ### Section 4A: Algebraic Master Inequality, Finite Probabilistic Existence, and Ramsey Transfer -/

section MasterAlgAndExistence

/-- Two-color open-pair fraction `h_ρ(x, y)` on `[0, 1]^2`. -/
noncomputable def hRho (ρ x y : ℝ) : ℝ :=
  (1 / 2 : ℝ) * max 0 (y ^ 2 - min ((1 - x) ^ 2) (ρ * (1 - x))) +
  (1 / 2 : ℝ) * max 0 (x ^ 2 - min ((1 - y) ^ 2) (ρ * (1 - y)))

/-- Algebraic Master Inequality on `[0, 1]^2`:
for `0 < ε ≤ 1/4` and `1 / (2 * (1 + ε)) ≤ ρ ≤ 1/2 - ε/4`,
`((1 + ε) / 2) * hRho ρ x y - (1 / 2) * (x + y - 1) ≥ ε^2 / 32` for ALL `x, y ∈ [0, 1]`. -/
lemma alg_master_ineq {ε ρ x y : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hρ_lo : 1 / (2 * (1 + ε)) ≤ ρ) (hρ_hi : ρ ≤ 1 / 2 - ε / 4)
    (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) (_hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ε ^ 2 / 32 ≤ ((1 + ε) / 2) * hRho ρ x y - (1 / 2) * (x + y - 1) := by
  have hρ_ge : (2 / 5 : ℝ) ≤ ρ := by
    have : (2 / 5 : ℝ) ≤ 1 / (2 * (1 + ε)) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      linarith
    linarith
  have hρ_prod : 2 * ε ≤ (1 + ε) * ρ := by
    have h1 : 1 / 2 ≤ (1 + ε) * ρ := by
      have := (div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (1 + ε))).mp hρ_lo
      linarith
    linarith
  have hh0 : 0 ≤ hRho ρ x y := by
    dsimp only [hRho]
    exact add_nonneg (mul_nonneg (by norm_num) (le_max_left _ _))
      (mul_nonneg (by norm_num) (le_max_left _ _))
  by_cases hlow : x + y ≤ 1 - ε ^ 2 / 16
  · nlinarith only [hε0, hh0, hlow]
  push Not at hlow
  by_cases h1x : 1 - x ≤ ρ
  · by_cases h1y : 1 - y ≤ ρ
    · -- Case 1: 1 - x ≤ ρ and 1 - y ≤ ρ
      have hminx : min ((1 - x) ^ 2) (ρ * (1 - x)) = (1 - x) ^ 2 :=
        min_eq_left (by nlinarith only [hx1, h1x])
      have hminy : min ((1 - y) ^ 2) (ρ * (1 - y)) = (1 - y) ^ 2 :=
        min_eq_left (by nlinarith only [hy1, h1y])
      have hh_ge : x + y - 1 ≤ hRho ρ x y := by
        dsimp only [hRho]
        rw [hminx, hminy]
        have hmx : y ^ 2 - (1 - x) ^ 2 ≤ max 0 (y ^ 2 - (1 - x) ^ 2) := le_max_right _ _
        have hmy : x ^ 2 - (1 - y) ^ 2 ≤ max 0 (x ^ 2 - (1 - y) ^ 2) := le_max_right _ _
        linarith only [hmx, hmy]
      have hsum_ge : ε / 2 ≤ x + y - 1 := by linarith only [h1x, h1y, hρ_hi]
      nlinarith only [hε0, hh_ge, hsum_ge]
    · -- Case 3: 1 - x ≤ ρ and ρ < 1 - y
      push Not at h1y
      have hminx : min ((1 - x) ^ 2) (ρ * (1 - x)) = (1 - x) ^ 2 :=
        min_eq_left (by nlinarith only [hx1, h1x])
      have hminy : min ((1 - y) ^ 2) (ρ * (1 - y)) = ρ * (1 - y) :=
        min_eq_right (by nlinarith only [hy1, h1y, hρ_ge])
      have hh_ge : (x + y - 1) + (1 / 2) * (1 - y) * (1 - y - ρ) ≤ hRho ρ x y := by
        dsimp only [hRho]
        rw [hminx, hminy]
        have hmx : y ^ 2 - (1 - x) ^ 2 ≤ max 0 (y ^ 2 - (1 - x) ^ 2) := le_max_right _ _
        have hmy : x ^ 2 - ρ * (1 - y) ≤ max 0 (x ^ 2 - ρ * (1 - y)) := le_max_right _ _
        linarith only [hmx, hmy]
      have hrem : ((1 + ε) / 2) * hRho ρ x y - (1 / 2) * (x + y - 1) ≥
          (ε / 2) * (x + y - 1) + ((1 + ε) / 4) * (1 - y) * (1 - y - ρ) := by
        nlinarith only [hε0, hh_ge]
      have hsum_comb : ε / 2 ≤ (x + y - 1) + (1 - y - ρ) := by linarith only [h1x, hρ_hi]
      by_cases hneg : x + y - 1 < 0
      · have h2 : ε / 2 ≤ 1 - y - ρ := by linarith only [hsum_comb, hneg]
        have hterm1 : -(ε ^ 3 / 32) ≤ (ε / 2) * (x + y - 1) := by nlinarith only [hε0, hlow]
        have hterm2 : ε / 20 ≤ ((1 + ε) / 4) * (1 - y) * (1 - y - ρ) := by
          have h1 : (2 / 5 : ℝ) ≤ 1 - y := by linarith only [h1y, hρ_ge]
          have h3 : (1 / 4 : ℝ) ≤ (1 + ε) / 4 := by linarith only [hε0]
          have hprod : (1 / 4 : ℝ) * (2 / 5 : ℝ) ≤ ((1 + ε) / 4) * (1 - y) := by nlinarith only [h1, h3]
          nlinarith only [hprod, h2, hε0]
        nlinarith only [hrem, hterm1, hterm2, hε0, hε1]
      · push Not at hneg
        by_cases hbig1 : ε / 4 ≤ x + y - 1
        · have hterm2 : 0 ≤ ((1 + ε) / 4) * (1 - y) * (1 - y - ρ) := by
            have : 0 ≤ 1 - y := by linarith only [hy1]
            have : 0 ≤ 1 - y - ρ := by linarith only [h1y]
            positivity
          nlinarith only [hrem, hbig1, hterm2, hε0]
        · have hbig2 : ε / 4 ≤ 1 - y - ρ := by linarith only [hsum_comb, hbig1]
          have hterm1 : 0 ≤ (ε / 2) * (x + y - 1) := by nlinarith only [hε0, hneg]
          have hterm2 : ε / 40 ≤ ((1 + ε) / 4) * (1 - y) * (1 - y - ρ) := by
            have h1 : (2 / 5 : ℝ) ≤ 1 - y := by linarith only [h1y, hρ_ge]
            have h3 : (1 / 4 : ℝ) ≤ (1 + ε) / 4 := by linarith only [hε0]
            have hprod : (1 / 4 : ℝ) * (2 / 5 : ℝ) ≤ ((1 + ε) / 4) * (1 - y) := by nlinarith only [h1, h3]
            nlinarith only [hprod, hbig2, hε0]
          nlinarith only [hrem, hterm1, hterm2, hε0, hε1]
  · push Not at h1x
    by_cases h1y : 1 - y ≤ ρ
    · -- Case 4: symmetric to Case 3 (swap x and y)
      have hminx : min ((1 - x) ^ 2) (ρ * (1 - x)) = ρ * (1 - x) :=
        min_eq_right (by nlinarith only [hx1, h1x, hρ_ge])
      have hminy : min ((1 - y) ^ 2) (ρ * (1 - y)) = (1 - y) ^ 2 :=
        min_eq_left (by nlinarith only [hy1, h1y])
      have hh_ge : (x + y - 1) + (1 / 2) * (1 - x) * (1 - x - ρ) ≤ hRho ρ x y := by
        dsimp only [hRho]
        rw [hminx, hminy]
        have hmx : y ^ 2 - ρ * (1 - x) ≤ max 0 (y ^ 2 - ρ * (1 - x)) := le_max_right _ _
        have hmy : x ^ 2 - (1 - y) ^ 2 ≤ max 0 (x ^ 2 - (1 - y) ^ 2) := le_max_right _ _
        linarith only [hmx, hmy]
      have hrem : ((1 + ε) / 2) * hRho ρ x y - (1 / 2) * (x + y - 1) ≥
          (ε / 2) * (x + y - 1) + ((1 + ε) / 4) * (1 - x) * (1 - x - ρ) := by
        nlinarith only [hε0, hh_ge]
      have hsum_comb : ε / 2 ≤ (x + y - 1) + (1 - x - ρ) := by linarith only [h1y, hρ_hi]
      by_cases hneg : x + y - 1 < 0
      · have h2 : ε / 2 ≤ 1 - x - ρ := by linarith only [hsum_comb, hneg]
        have hterm1 : -(ε ^ 3 / 32) ≤ (ε / 2) * (x + y - 1) := by nlinarith only [hε0, hlow]
        have hterm2 : ε / 20 ≤ ((1 + ε) / 4) * (1 - x) * (1 - x - ρ) := by
          have h1 : (2 / 5 : ℝ) ≤ 1 - x := by linarith only [h1x, hρ_ge]
          have h3 : (1 / 4 : ℝ) ≤ (1 + ε) / 4 := by linarith only [hε0]
          have hprod : (1 / 4 : ℝ) * (2 / 5 : ℝ) ≤ ((1 + ε) / 4) * (1 - x) := by nlinarith only [h1, h3]
          nlinarith only [hprod, h2, hε0]
        nlinarith only [hrem, hterm1, hterm2, hε0, hε1]
      · push Not at hneg
        by_cases hbig1 : ε / 4 ≤ x + y - 1
        · have hterm2 : 0 ≤ ((1 + ε) / 4) * (1 - x) * (1 - x - ρ) := by
            have : 0 ≤ 1 - x := by linarith only [hx1]
            have : 0 ≤ 1 - x - ρ := by linarith only [h1x]
            positivity
          nlinarith only [hrem, hbig1, hterm2, hε0]
        · have hbig2 : ε / 4 ≤ 1 - x - ρ := by linarith only [hsum_comb, hbig1]
          have hterm1 : 0 ≤ (ε / 2) * (x + y - 1) := by nlinarith only [hε0, hneg]
          have hterm2 : ε / 40 ≤ ((1 + ε) / 4) * (1 - x) * (1 - x - ρ) := by
            have h1 : (2 / 5 : ℝ) ≤ 1 - x := by linarith only [h1x, hρ_ge]
            have h3 : (1 / 4 : ℝ) ≤ (1 + ε) / 4 := by linarith only [hε0]
            have hprod : (1 / 4 : ℝ) * (2 / 5 : ℝ) ≤ ((1 + ε) / 4) * (1 - x) := by nlinarith only [h1, h3]
            nlinarith only [hprod, hbig2, hε0]
          nlinarith only [hrem, hterm1, hterm2, hε0, hε1]
    · -- Case 2: ρ < 1 - x and ρ < 1 - y
      push Not at h1y
      have hminx : min ((1 - x) ^ 2) (ρ * (1 - x)) = ρ * (1 - x) :=
        min_eq_right (by nlinarith only [hx1, h1x, hρ_ge])
      have hminy : min ((1 - y) ^ 2) (ρ * (1 - y)) = ρ * (1 - y) :=
        min_eq_right (by nlinarith only [hy1, h1y, hρ_ge])
      set S : ℝ := x + y
      have hsq : S ^ 2 / 2 ≤ x ^ 2 + y ^ 2 := by nlinarith only [sq_nonneg (x - y)]
      have hh_ge : S ^ 2 / 4 - ρ * (2 - S) / 2 ≤ hRho ρ x y := by
        dsimp only [hRho]
        rw [hminx, hminy]
        have hmx : y ^ 2 - ρ * (1 - x) ≤ max 0 (y ^ 2 - ρ * (1 - x)) := le_max_right _ _
        have hmy : x ^ 2 - ρ * (1 - y) ≤ max 0 (x ^ 2 - ρ * (1 - y)) := le_max_right _ _
        linarith only [hmx, hmy, hsq]
      set u : ℝ := (2 - 2 * ρ) - S
      have hu0 : 0 ≤ u := by dsimp only [u, S]; linarith only [h1x, h1y]
      have hquad_id : ((1 + ε) / 2) * (S ^ 2 / 4 - ρ * (2 - S) / 2) - (1 / 2) * (S - 1) =
          (ε / 2) * (1 - 2 * ρ) + ((1 + ε) / 8) * u ^ 2 + (((1 + ε) * ρ - 2 * ε) / 4) * u := by
        dsimp only [u]; ring
      have hval_ge : ε ^ 2 / 4 ≤ (ε / 2) * (1 - 2 * ρ) := by nlinarith only [hε0, hρ_hi]
      have hu1 : 0 ≤ ((1 + ε) / 8) * u ^ 2 := by positivity
      have hu2 : 0 ≤ (((1 + ε) * ρ - 2 * ε) / 4) * u := by nlinarith only [hρ_prod, hu0]
      nlinarith only [hε0, hh_ge, hquad_id, hval_ge, hu1, hu2]

/-- Map fiber-goodness predicate: every fiber of `φ : Fin n → Fin m` has size `≤ F_max`. -/
def FibGood (n m : ℕ) (F_max : ℝ) (φ : Fin n → Fin m) : Prop :=
  ∀ x : Fin m, ((Finset.univ.filter fun v : Fin n => φ v = x).card : ℝ) ≤ F_max

/-- Fraction of maps failing `FibGood` is bounded via Chernoff when `F_max = (1 + η₀) * (n / m)`. -/
lemma card_not_fibGood_le {n m : ℕ} (hm : 1 ≤ m) {η₀ : ℝ} (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 2) :
    ((Finset.univ.filter fun φ : Fin n → Fin m =>
      ¬ FibGood n m ((1 + η₀) * ((n : ℝ) / (m : ℝ))) φ).card : ℝ) ≤
      (m : ℝ) * Real.exp (-(η₀ ^ 2 / 3) * ((n : ℝ) / (m : ℝ))) * (m : ℝ) ^ n := by
  let bad := Finset.univ.filter fun φ : Fin n → Fin m =>
    ¬ FibGood n m ((1 + η₀) * ((n : ℝ) / (m : ℝ))) φ
  have hcov : bad ⊆ Finset.univ.biUnion fun x : Fin m =>
      Finset.univ.filter fun φ : Fin n → Fin m =>
        (1 + η₀) * ((n : ℝ) / (m : ℝ)) ≤ ((Finset.univ.filter fun v : Fin n => φ v = x).card : ℝ) := by
    intro φ hφ
    have hnot := (Finset.mem_filter.mp hφ).2
    simp only [FibGood, not_forall, not_le] at hnot
    rcases hnot with ⟨x, hx⟩
    exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.le⟩⟩
  have hle : (bad.card : ℝ) ≤ ∑ x : Fin m,
      ((Finset.univ.filter fun φ : Fin n → Fin m =>
        (1 + η₀) * ((n : ℝ) / (m : ℝ)) ≤ ((Finset.univ.filter fun v : Fin n => φ v = x).card : ℝ)).card : ℝ) := by
    have hnat : bad.card ≤ ∑ x : Fin m,
        (Finset.univ.filter fun φ : Fin n → Fin m =>
          (1 + η₀) * ((n : ℝ) / (m : ℝ)) ≤ ((Finset.univ.filter fun v : Fin n => φ v = x).card : ℝ)).card :=
      (Finset.card_le_card hcov).trans Finset.card_biUnion_le
    exact_mod_cast hnat
  calc (bad.card : ℝ)
      ≤ ∑ x : Fin m, _ := hle
    _ ≤ ∑ _x : Fin m, (Real.exp (-(η₀ ^ 2 / 3) * ((n : ℝ) / (m : ℝ))) * (m : ℝ) ^ n) :=
        Finset.sum_le_sum fun x _ => card_maps_fiber_ge_chernoff hm hη0 hη1 x
    _ = (m : ℝ) * Real.exp (-(η₀ ^ 2 / 3) * ((n : ℝ) / (m : ℝ))) * (m : ℝ) ^ n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

/-- Number of maps `φ : Fin n → Fin m` sending `I` onto an image of exact cardinality `a`:
at most `m.choose a * (a / m)^|I| * m^n`. -/
lemma card_maps_card_image_eq_le {n m : ℕ} (hm : 1 ≤ m) (I : Finset (Fin n)) (a : ℕ) :
    ((Finset.univ.filter fun φ : Fin n → Fin m => (I.image φ).card = a).card : ℝ) ≤
      (m.choose a : ℝ) * ((a : ℝ) / (m : ℝ)) ^ I.card * (m : ℝ) ^ n := by
  let S := Finset.univ.filter fun φ : Fin n → Fin m => (I.image φ).card = a
  have hcov : S ⊆ ((Finset.univ : Finset (Fin m)).powersetCard a).biUnion fun A =>
      Finset.univ.filter fun φ : Fin n → Fin m => ∀ v ∈ I, φ v ∈ A := by
    intro φ hφ
    have heq := (Finset.mem_filter.mp hφ).2
    refine Finset.mem_biUnion.mpr ⟨I.image φ, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, heq⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v hv => Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩⟩
  have hle : (S.card : ℝ) ≤ ∑ A ∈ (Finset.univ : Finset (Fin m)).powersetCard a,
      ((Finset.univ.filter fun φ : Fin n → Fin m => ∀ v ∈ I, φ v ∈ A).card : ℝ) := by
    have hnat := (Finset.card_le_card hcov).trans Finset.card_biUnion_le
    exact_mod_cast hnat
  calc (S.card : ℝ)
      ≤ ∑ A ∈ (Finset.univ : Finset (Fin m)).powersetCard a,
          ((Finset.univ.filter fun φ : Fin n → Fin m => ∀ v ∈ I, φ v ∈ A).card : ℝ) := hle
    _ = ∑ A ∈ (Finset.univ : Finset (Fin m)).powersetCard a,
          (((A.card : ℝ) / (m : ℝ)) ^ I.card * (m : ℝ) ^ n) :=
        Finset.sum_congr rfl fun A _ => card_maps_image_subset hm I A
    _ = ∑ _A ∈ (Finset.univ : Finset (Fin m)).powersetCard a,
          (((a : ℝ) / (m : ℝ)) ^ I.card * (m : ℝ) ^ n) :=
        Finset.sum_congr rfl fun A hA => by rw [(Finset.mem_powersetCard.mp hA).2]
    _ = (m.choose a : ℝ) * ((a : ℝ) / (m : ℝ)) ^ I.card * (m : ℝ) ^ n := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_assoc]

/-- Finite probabilistic existence theorem: if the sum of the fiber-failure, regularity-failure,
and independent-set union bounds is `< 1`, then there exists a triangle-free graph `G` on `Fin n`
whose independent sets all have cardinality `< P.k`. -/
lemma exists_triangleFree_indep_lt {n : ℕ} (P : RegParams) {F_max T_small lam₁ lam₂ B_good B_ind : ℝ}
    (hV : ValidRegParams P F_max) (hη1 : P.η₀ ≤ 1 / 2)
    (hF_def : F_max = (1 + P.η₀) * ((n : ℝ) / (P.m : ℝ)))
    (hTsmall : 0 < T_small) (hlam1 : 0 < lam₁) (hlam2 : 0 < lam₂)
    (hBgood : bernProb P.p (fun ω => ¬ GoodGraph P ω) ≤ B_good)
    (hBind : ∀ a ∈ Finset.Icc 1 P.k, ∀ b ∈ Finset.Icc 1 P.k,
      let D := F_max * ((1 + P.η₀) * ((P.m : ℝ) * P.p))
      let M_open :=
        (1 / 2 : ℝ) * max 0 ((a : ℝ) ^ 2 - min (((P.k - b : ℕ) : ℝ) ^ 2) (D * ((P.k - b : ℕ) : ℝ))) +
        (1 / 2 : ℝ) * max 0 ((b : ℝ) ^ 2 - min (((P.k - a : ℕ) : ℝ) ^ 2) (D * ((P.k - a : ℕ) : ℝ))) -
        2 * errOpen P F_max
      (n.choose P.k : ℝ) *
        ((P.m.choose a : ℝ) * ((a : ℝ) / (P.m : ℝ)) ^ P.k) *
        ((P.m.choose b : ℝ) * ((b : ℝ) / (P.m : ℝ)) ^ P.k) *
        (((Qmax P + 1 : ℕ) : ℝ) * ((P.k + 1 : ℕ) : ℝ) ^ Qmax P) ^ 2 * (
          Real.exp (2 * lam₁ * T_small - P.p * (1 - Real.exp (-lam₁)) * M_open) +
          2 * (Real.exp 1 * (errOut P F_max / 2) * P.p / (⌈T_small / 2⌉₊ : ℝ)) ^ ⌈T_small / 2⌉₊ +
          2 * Real.exp ((Real.exp lam₂ - 1) * P.p * (MtriBound P F_max : ℝ) - lam₂ * (T_small / 2))) ≤ B_ind)
    (htot : 2 * (P.m : ℝ) * Real.exp (-(P.η₀ ^ 2 / 3) * ((n : ℝ) / (P.m : ℝ))) +
        2 * B_good + ((P.k : ℝ) ^ 2) * B_ind < 1) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧
      ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) → I.card < P.k := by
  have hm1 : 1 ≤ P.m := by have := hV.hk1; have := hV.h2k; omega
  have hm_pos : (0 : ℝ) < (P.m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm2n_pos : (0 : ℝ) < ((P.m : ℝ) ^ n) ^ 2 := by positivity
  -- Average over all (φ_R, φ_B) : (Fin n → Fin P.m) × (Fin n → Fin P.m) of the bad Bernoulli prob!
  let badEv : (Fin n → Fin P.m) × (Fin n → Fin P.m) → (EdgeIdx P.m ⊕ EdgeIdx P.m → Bool) → Prop :=
    fun φ ω =>
      let ω_R := fun e => ω (Sum.inl e)
      let ω_B := fun e => ω (Sum.inr e)
      ¬ FibGood n P.m F_max φ.1 ∨ ¬ FibGood n P.m F_max φ.2 ∨
      ¬ GoodGraph P ω_R ∨ ¬ GoodGraph P ω_B ∨
      ∃ I ∈ (Finset.univ : Finset (Fin n)).powersetCard P.k,
        FibGood n P.m F_max φ.1 ∧ FibGood n P.m F_max φ.2 ∧
        GoodGraph P ω_R ∧ GoodGraph P ω_B ∧
        (buildGraph (graphOf ω_R) (graphOf ω_B) φ.1 φ.2).IsIndepSet (I : Set (Fin n))
  let badProb : (Fin n → Fin P.m) × (Fin n → Fin P.m) → ℝ := fun φ => bernProb P.p (badEv φ)
  have hsum_bad : ∑ φ : (Fin n → Fin P.m) × (Fin n → Fin P.m), badProb φ < ((P.m : ℝ) ^ n) ^ 2 := by
    have hsplit : ∀ φ : (Fin n → Fin P.m) × (Fin n → Fin P.m),
        badProb φ ≤
          (if ¬ FibGood n P.m F_max φ.1 then (1 : ℝ) else 0) +
          (if ¬ FibGood n P.m F_max φ.2 then (1 : ℝ) else 0) +
          2 * B_good +
          ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard P.k,
            if FibGood n P.m F_max φ.1 ∧ FibGood n P.m F_max φ.2 then
              bernProb P.p (fun ω : EdgeIdx P.m ⊕ EdgeIdx P.m → Bool =>
                GoodGraph P (fun e => ω (Sum.inl e)) ∧ GoodGraph P (fun e => ω (Sum.inr e)) ∧
                (buildGraph (graphOf (fun e => ω (Sum.inl e)))
                  (graphOf (fun e => ω (Sum.inr e))) φ.1 φ.2).IsIndepSet (I : Set (Fin n)))
            else 0 := by
      intro φ
      let Q1 : (EdgeIdx P.m ⊕ EdgeIdx P.m → Bool) → Prop := fun _ => ¬ FibGood n P.m F_max φ.1
      let Q2 : (EdgeIdx P.m ⊕ EdgeIdx P.m → Bool) → Prop := fun _ => ¬ FibGood n P.m F_max φ.2
      let Q3 : (EdgeIdx P.m ⊕ EdgeIdx P.m → Bool) → Prop := fun ω => ¬ GoodGraph P (fun e => ω (Sum.inl e))
      let Q4 : (EdgeIdx P.m ⊕ EdgeIdx P.m → Bool) → Prop := fun ω => ¬ GoodGraph P (fun e => ω (Sum.inr e))
      let Q5 : (EdgeIdx P.m ⊕ EdgeIdx P.m → Bool) → Prop := fun ω =>
        ∃ I ∈ (Finset.univ : Finset (Fin n)).powersetCard P.k,
          FibGood n P.m F_max φ.1 ∧ FibGood n P.m F_max φ.2 ∧
          GoodGraph P (fun e => ω (Sum.inl e)) ∧ GoodGraph P (fun e => ω (Sum.inr e)) ∧
          (buildGraph (graphOf (fun e => ω (Sum.inl e)))
            (graphOf (fun e => ω (Sum.inr e))) φ.1 φ.2).IsIndepSet (I : Set (Fin n))
      have h1 := bernProb_or_le hV.hp0 hV.hp1 Q1 (fun ω => Q2 ω ∨ Q3 ω ∨ Q4 ω ∨ Q5 ω)
      have h2 := bernProb_or_le hV.hp0 hV.hp1 Q2 (fun ω => Q3 ω ∨ Q4 ω ∨ Q5 ω)
      have h3 := bernProb_or_le hV.hp0 hV.hp1 Q3 (fun ω => Q4 ω ∨ Q5 ω)
      have h4 := bernProb_or_le hV.hp0 hV.hp1 Q4 Q5
      have hQ1 : bernProb P.p Q1 = if ¬ FibGood n P.m F_max φ.1 then 1 else 0 := by
        by_cases hq : ¬ FibGood n P.m F_max φ.1 <;> simp [Q1, bernProb, hq, sum_bernW_eq_one]
      have hQ2 : bernProb P.p Q2 = if ¬ FibGood n P.m F_max φ.2 then 1 else 0 := by
        by_cases hq : ¬ FibGood n P.m F_max φ.2 <;> simp [Q2, bernProb, hq, sum_bernW_eq_one]
      have hGR_le : bernProb P.p Q3 ≤ B_good :=
        (bernProb_inl P.p (fun ωR => ¬ GoodGraph P ωR)).trans_le hBgood
      have hGB_le : bernProb P.p Q4 ≤ B_good := by
        let eSwap : EdgeIdx P.m ⊕ EdgeIdx P.m ≃ EdgeIdx P.m ⊕ EdgeIdx P.m := Equiv.sumComm _ _
        dsimp only [Q4]
        rw [bernProb_equiv eSwap P.p]
        exact (bernProb_inl P.p (fun ωB => ¬ GoodGraph P ωB)).trans_le hBgood
      have h5 : bernProb P.p Q5 ≤ ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard P.k,
          bernProb P.p (fun ω : EdgeIdx P.m ⊕ EdgeIdx P.m → Bool =>
            FibGood n P.m F_max φ.1 ∧ FibGood n P.m F_max φ.2 ∧
            GoodGraph P (fun e => ω (Sum.inl e)) ∧ GoodGraph P (fun e => ω (Sum.inr e)) ∧
            (buildGraph (graphOf (fun e => ω (Sum.inl e)))
              (graphOf (fun e => ω (Sum.inr e))) φ.1 φ.2).IsIndepSet (I : Set (Fin n))) :=
        bernProb_exists_le hV.hp0 hV.hp1 ((Finset.univ : Finset (Fin n)).powersetCard P.k) _
      have h5_eq : ∀ I ∈ (Finset.univ : Finset (Fin n)).powersetCard P.k,
          bernProb P.p (fun ω : EdgeIdx P.m ⊕ EdgeIdx P.m → Bool =>
            FibGood n P.m F_max φ.1 ∧ FibGood n P.m F_max φ.2 ∧
            GoodGraph P (fun e => ω (Sum.inl e)) ∧ GoodGraph P (fun e => ω (Sum.inr e)) ∧
            (buildGraph (graphOf (fun e => ω (Sum.inl e))) (graphOf (fun e => ω (Sum.inr e))) φ.1 φ.2).IsIndepSet (I : Set (Fin n))) =
          if FibGood n P.m F_max φ.1 ∧ FibGood n P.m F_max φ.2 then
            bernProb P.p (fun ω : EdgeIdx P.m ⊕ EdgeIdx P.m → Bool =>
              GoodGraph P (fun e => ω (Sum.inl e)) ∧ GoodGraph P (fun e => ω (Sum.inr e)) ∧
              (buildGraph (graphOf (fun e => ω (Sum.inl e))) (graphOf (fun e => ω (Sum.inr e))) φ.1 φ.2).IsIndepSet (I : Set (Fin n)))
          else 0 := fun I _ => by
        by_cases hf : FibGood n P.m F_max φ.1 ∧ FibGood n P.m F_max φ.2
        · simp [hf]
        · simp only [if_neg hf, bernProb]
          exact Finset.sum_eq_zero fun _ _ => if_neg (fun h => hf ⟨h.1, h.2.1⟩)
      rw [Finset.sum_congr rfl h5_eq] at h5
      have hbad_eq : badProb φ = bernProb P.p (fun ω => Q1 ω ∨ Q2 ω ∨ Q3 ω ∨ Q4 ω ∨ Q5 ω) := rfl
      linarith only [hbad_eq, h1, h2, h3, h4, hQ1, hQ2, hGR_le, hGB_le, h5]
    refine (Finset.sum_le_sum fun φ _ => hsplit φ).trans_lt ?_
    simp only [Finset.sum_add_distrib]
    have hcard_maps : (Fintype.card (Fin n → Fin P.m) : ℝ) = (P.m : ℝ) ^ n := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
    -- Sum 1 + Sum 2: fiber Chernoff
    have hS1 : (∑ φ : (Fin n → Fin P.m) × (Fin n → Fin P.m), if ¬ FibGood n P.m F_max φ.1 then (1 : ℝ) else 0) ≤
        (P.m : ℝ) * Real.exp (-(P.η₀ ^ 2 / 3) * ((n : ℝ) / (P.m : ℝ))) * ((P.m : ℝ) ^ n) ^ 2 := by
      have hprod_eq : (∑ φ : (Fin n → Fin P.m) × (Fin n → Fin P.m), if ¬ FibGood n P.m F_max φ.1 then (1 : ℝ) else 0) =
          (∑ φ₁ : Fin n → Fin P.m, if ¬ FibGood n P.m F_max φ₁ then (1 : ℝ) else 0) * (P.m : ℝ) ^ n := by
        rw [Fintype.sum_prod_type, Finset.sum_mul]
        refine Finset.sum_congr rfl fun φ₁ _ => ?_
        change (∑ _y : Fin n → Fin P.m, if ¬ FibGood n P.m F_max φ₁ then (1 : ℝ) else 0) = _
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard_maps, mul_comm]
      rw [hprod_eq]
      have h1 : (∑ φ₁ : Fin n → Fin P.m, if ¬ FibGood n P.m F_max φ₁ then (1 : ℝ) else 0) =
          ((Finset.univ.filter fun φ₁ : Fin n → Fin P.m => ¬ FibGood n P.m F_max φ₁).card : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [h1, hF_def]
      have hch := card_not_fibGood_le (n := n) hm1 hV.hη0 hη1
      have hmul := mul_le_mul_of_nonneg_right hch (pow_nonneg hm_pos.le n)
      linarith only [hmul, show (P.m : ℝ) * Real.exp (-(P.η₀ ^ 2 / 3) * ((n : ℝ) / (P.m : ℝ))) *
          (P.m : ℝ) ^ n * (P.m : ℝ) ^ n =
          (P.m : ℝ) * Real.exp (-(P.η₀ ^ 2 / 3) * ((n : ℝ) / (P.m : ℝ))) * ((P.m : ℝ) ^ n) ^ 2 by ring]
    have hS2 : (∑ φ : (Fin n → Fin P.m) × (Fin n → Fin P.m), if ¬ FibGood n P.m F_max φ.2 then (1 : ℝ) else 0) ≤
        (P.m : ℝ) * Real.exp (-(P.η₀ ^ 2 / 3) * ((n : ℝ) / (P.m : ℝ))) * ((P.m : ℝ) ^ n) ^ 2 := by
      have hprod_eq : (∑ φ : (Fin n → Fin P.m) × (Fin n → Fin P.m), if ¬ FibGood n P.m F_max φ.2 then (1 : ℝ) else 0) =
          (∑ φ₂ : Fin n → Fin P.m, if ¬ FibGood n P.m F_max φ₂ then (1 : ℝ) else 0) * (P.m : ℝ) ^ n := by
        rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_mul]
        refine Finset.sum_congr rfl fun φ₂ _ => ?_
        change (∑ _x : Fin n → Fin P.m, if ¬ FibGood n P.m F_max φ₂ then (1 : ℝ) else 0) = _
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard_maps, mul_comm]
      rw [hprod_eq]
      have h1 : (∑ φ₂ : Fin n → Fin P.m, if ¬ FibGood n P.m F_max φ₂ then (1 : ℝ) else 0) =
          ((Finset.univ.filter fun φ₂ : Fin n → Fin P.m => ¬ FibGood n P.m F_max φ₂).card : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [h1, hF_def]
      have hch := card_not_fibGood_le (n := n) hm1 hV.hη0 hη1
      have hmul := mul_le_mul_of_nonneg_right hch (pow_nonneg hm_pos.le n)
      linarith only [hmul, show (P.m : ℝ) * Real.exp (-(P.η₀ ^ 2 / 3) * ((n : ℝ) / (P.m : ℝ))) *
          (P.m : ℝ) ^ n * (P.m : ℝ) ^ n =
          (P.m : ℝ) * Real.exp (-(P.η₀ ^ 2 / 3) * ((n : ℝ) / (P.m : ℝ))) * ((P.m : ℝ) ^ n) ^ 2 by ring]
    -- Sum 3: 2 * B_good
    have hS3 : (∑ _φ : (Fin n → Fin P.m) × (Fin n → Fin P.m), (2 * B_good)) =
        2 * B_good * ((P.m : ℝ) ^ n) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul, hcard_maps]
      ring
    -- Sum 4: swap I outside, group φ = (φ_R, φ_B) by (|I.image φ_R|, |I.image φ_B|) ∈ Icc 1 k × Icc 1 k!
    have hS4 : (∑ φ : (Fin n → Fin P.m) × (Fin n → Fin P.m),
        ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard P.k,
          if FibGood n P.m F_max φ.1 ∧ FibGood n P.m F_max φ.2 then
            bernProb P.p (fun ω : EdgeIdx P.m ⊕ EdgeIdx P.m → Bool =>
              GoodGraph P (fun e => ω (Sum.inl e)) ∧ GoodGraph P (fun e => ω (Sum.inr e)) ∧
              (buildGraph (graphOf (fun e => ω (Sum.inl e)))
                (graphOf (fun e => ω (Sum.inr e))) φ.1 φ.2).IsIndepSet (I : Set (Fin n)))
          else 0) ≤ ((P.k : ℝ) ^ 2) * B_ind * ((P.m : ℝ) ^ n) ^ 2 := by
      rw [Finset.sum_comm]
      -- Define the bound term f(a, b)
      let fAB : ℕ → ℕ → ℝ := fun a b =>
        let D := F_max * ((1 + P.η₀) * ((P.m : ℝ) * P.p))
        let M_open :=
          (1 / 2 : ℝ) * max 0 ((a : ℝ) ^ 2 - min (((P.k - b : ℕ) : ℝ) ^ 2) (D * ((P.k - b : ℕ) : ℝ))) +
          (1 / 2 : ℝ) * max 0 ((b : ℝ) ^ 2 - min (((P.k - a : ℕ) : ℝ) ^ 2) (D * ((P.k - a : ℕ) : ℝ))) -
          2 * errOpen P F_max
        (((Qmax P + 1 : ℕ) : ℝ) * ((P.k + 1 : ℕ) : ℝ) ^ Qmax P) ^ 2 * (
          Real.exp (2 * lam₁ * T_small - P.p * (1 - Real.exp (-lam₁)) * M_open) +
          2 * (Real.exp 1 * (errOut P F_max / 2) * P.p / (⌈T_small / 2⌉₊ : ℝ)) ^ ⌈T_small / 2⌉₊ +
          2 * Real.exp ((Real.exp lam₂ - 1) * P.p * (MtriBound P F_max : ℝ) - lam₂ * (T_small / 2)))
      have hfAB_nn : ∀ a b, 0 ≤ fAB a b := fun a b => by
        have heo_nn : 0 ≤ errOut P F_max := errOut_nonneg P hV
        dsimp only [fAB]
        exact mul_nonneg (sq_nonneg _)
          (add_nonneg
            (add_nonneg (Real.exp_pos _).le
              (mul_nonneg (by norm_num)
                (pow_nonneg (div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le
                  (div_nonneg heo_nn (by norm_num))) hV.hp0) (Nat.cast_nonneg _)) _)))
            (mul_nonneg (by norm_num) (Real.exp_pos _).le))
      have hsingle_I : ∀ I ∈ (Finset.univ : Finset (Fin n)).powersetCard P.k,
          (∑ φ : (Fin n → Fin P.m) × (Fin n → Fin P.m),
            if FibGood n P.m F_max φ.1 ∧ FibGood n P.m F_max φ.2 then
              bernProb P.p (fun ω : EdgeIdx P.m ⊕ EdgeIdx P.m → Bool =>
                GoodGraph P (fun e => ω (Sum.inl e)) ∧ GoodGraph P (fun e => ω (Sum.inr e)) ∧
                (buildGraph (graphOf (fun e => ω (Sum.inl e)))
                  (graphOf (fun e => ω (Sum.inr e))) φ.1 φ.2).IsIndepSet (I : Set (Fin n)))
            else 0) ≤
          ∑ a ∈ Finset.Icc 1 P.k, ∑ b ∈ Finset.Icc 1 P.k,
            ((P.m.choose a : ℝ) * ((a : ℝ) / (P.m : ℝ)) ^ P.k) *
            ((P.m.choose b : ℝ) * ((b : ℝ) / (P.m : ℝ)) ^ P.k) *
            fAB a b * ((P.m : ℝ) ^ n) ^ 2 := by
        intro I hI
        have hIk : I.card = P.k := (Finset.mem_powersetCard.mp hI).2
        have hIne : I.Nonempty := Finset.card_pos.mp (by have := hV.hk1; omega)
        have hpt : ∀ φ : (Fin n → Fin P.m) × (Fin n → Fin P.m),
            (if FibGood n P.m F_max φ.1 ∧ FibGood n P.m F_max φ.2 then
              bernProb P.p (fun ω : EdgeIdx P.m ⊕ EdgeIdx P.m → Bool =>
                GoodGraph P (fun e => ω (Sum.inl e)) ∧ GoodGraph P (fun e => ω (Sum.inr e)) ∧
                (buildGraph (graphOf (fun e => ω (Sum.inl e)))
                  (graphOf (fun e => ω (Sum.inr e))) φ.1 φ.2).IsIndepSet (I : Set (Fin n)))
            else 0) ≤ fAB (I.image φ.1).card (I.image φ.2).card := by
          intro φ
          split_ifs with hf
          · exact bernProb_indep_good_le P hV hTsmall hlam1 hlam2 hIk hf.1 hf.2
          · exact hfAB_nn _ _
        refine (Finset.sum_le_sum fun φ _ => hpt φ).trans ?_
        -- Partition univ over (a, b) ∈ Icc 1 k × Icc 1 k
        have hmaps_ab : ∀ φ : (Fin n → Fin P.m) × (Fin n → Fin P.m),
            ((I.image φ.1).card, (I.image φ.2).card) ∈ Finset.Icc 1 P.k ×ˢ Finset.Icc 1 P.k := by
          intro φ
          have h1 : 1 ≤ (I.image φ.1).card := Finset.card_pos.mpr (hIne.image φ.1)
          have h2 : (I.image φ.1).card ≤ P.k := by rw [← hIk]; exact Finset.card_image_le
          have h3 : 1 ≤ (I.image φ.2).card := Finset.card_pos.mpr (hIne.image φ.2)
          have h4 : (I.image φ.2).card ≤ P.k := by rw [← hIk]; exact Finset.card_image_le
          exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, Finset.mem_Icc.mpr ⟨h3, h4⟩⟩
        rw [← Finset.sum_fiberwise_of_maps_to (g := fun φ : (Fin n → Fin P.m) × (Fin n → Fin P.m) =>
            ((I.image φ.1).card, (I.image φ.2).card)) (fun φ _ => hmaps_ab φ), Finset.sum_product]
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        have hconst : ∑ φ ∈ Finset.univ.filter (fun φ : (Fin n → Fin P.m) × (Fin n → Fin P.m) =>
            ((I.image φ.1).card, (I.image φ.2).card) = (a, b)), fAB (I.image φ.1).card (I.image φ.2).card =
            ((Finset.univ.filter fun φ₁ : Fin n → Fin P.m => (I.image φ₁).card = a).card : ℝ) *
            ((Finset.univ.filter fun φ₂ : Fin n → Fin P.m => (I.image φ₂).card = b).card : ℝ) * fAB a b := by
          have heq_f : Finset.univ.filter (fun φ : (Fin n → Fin P.m) × (Fin n → Fin P.m) =>
              ((I.image φ.1).card, (I.image φ.2).card) = (a, b)) =
              (Finset.univ.filter fun φ₁ : Fin n → Fin P.m => (I.image φ₁).card = a) ×ˢ
              (Finset.univ.filter fun φ₂ : Fin n → Fin P.m => (I.image φ₂).card = b) := by
            ext ⟨φ₁, φ₂⟩; simp [Prod.mk.injEq]
          calc ∑ φ ∈ Finset.univ.filter (fun φ : (Fin n → Fin P.m) × (Fin n → Fin P.m) =>
                ((I.image φ.1).card, (I.image φ.2).card) = (a, b)), fAB (I.image φ.1).card (I.image φ.2).card
              = ∑ _φ ∈ Finset.univ.filter (fun φ : (Fin n → Fin P.m) × (Fin n → Fin P.m) =>
                  ((I.image φ.1).card, (I.image φ.2).card) = (a, b)), fAB a b :=
                Finset.sum_congr rfl fun φ hφ => by
                  have h := Prod.mk.inj (Finset.mem_filter.mp hφ).2
                  rw [h.1, h.2]
            _ = _ := by rw [heq_f, Finset.sum_const, Finset.card_product, nsmul_eq_mul, Nat.cast_mul]
        rw [hconst]
        have hca := card_maps_card_image_eq_le hm1 I a
        have hcb := card_maps_card_image_eq_le hm1 I b
        rw [hIk] at hca hcb
        have hprod := mul_le_mul hca hcb (Nat.cast_nonneg _) (by positivity)
        have hmul := mul_le_mul_of_nonneg_right hprod (hfAB_nn a b)
        linarith only [hmul, show ((P.m.choose a : ℝ) * ((a : ℝ) / (P.m : ℝ)) ^ P.k * (P.m : ℝ) ^ n) *
            ((P.m.choose b : ℝ) * ((b : ℝ) / (P.m : ℝ)) ^ P.k * (P.m : ℝ) ^ n) * fAB a b =
            ((P.m.choose a : ℝ) * ((a : ℝ) / (P.m : ℝ)) ^ P.k) *
            ((P.m.choose b : ℝ) * ((b : ℝ) / (P.m : ℝ)) ^ P.k) *
            fAB a b * ((P.m : ℝ) ^ n) ^ 2 by ring]
      calc ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard P.k, _
          ≤ ∑ _I ∈ (Finset.univ : Finset (Fin n)).powersetCard P.k,
              ∑ a ∈ Finset.Icc 1 P.k, ∑ b ∈ Finset.Icc 1 P.k,
                ((P.m.choose a : ℝ) * ((a : ℝ) / (P.m : ℝ)) ^ P.k) *
                ((P.m.choose b : ℝ) * ((b : ℝ) / (P.m : ℝ)) ^ P.k) *
                fAB a b * ((P.m : ℝ) ^ n) ^ 2 := Finset.sum_le_sum hsingle_I
        _ = ∑ a ∈ Finset.Icc 1 P.k, ∑ b ∈ Finset.Icc 1 P.k,
              ((n.choose P.k : ℝ) *
                ((P.m.choose a : ℝ) * ((a : ℝ) / (P.m : ℝ)) ^ P.k) *
                ((P.m.choose b : ℝ) * ((b : ℝ) / (P.m : ℝ)) ^ P.k) *
                fAB a b) * ((P.m : ℝ) ^ n) ^ 2 := by
            rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => by ring
        _ ≤ ∑ _a ∈ Finset.Icc 1 P.k, ∑ _b ∈ Finset.Icc 1 P.k, (B_ind * ((P.m : ℝ) ^ n) ^ 2) :=
            Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => by
              dsimp only [fAB]
              rw [← mul_assoc]
              exact mul_le_mul_of_nonneg_right (hBind a ha b hb) hm2n_pos.le
        _ = ((P.k : ℝ) ^ 2) * B_ind * ((P.m : ℝ) ^ n) ^ 2 := by
            simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
            ring
    calc _ ≤ (P.m : ℝ) * Real.exp (-(P.η₀ ^ 2 / 3) * ((n : ℝ) / (P.m : ℝ))) * ((P.m : ℝ) ^ n) ^ 2 +
            (P.m : ℝ) * Real.exp (-(P.η₀ ^ 2 / 3) * ((n : ℝ) / (P.m : ℝ))) * ((P.m : ℝ) ^ n) ^ 2 +
            2 * B_good * ((P.m : ℝ) ^ n) ^ 2 + ((P.k : ℝ) ^ 2) * B_ind * ((P.m : ℝ) ^ n) ^ 2 := by
          linarith only [hS1, hS2, hS3, hS4]
      _ = (2 * (P.m : ℝ) * Real.exp (-(P.η₀ ^ 2 / 3) * ((n : ℝ) / (P.m : ℝ))) +
            2 * B_good + ((P.k : ℝ) ^ 2) * B_ind) * ((P.m : ℝ) ^ n) ^ 2 := by ring
      _ < 1 * ((P.m : ℝ) ^ n) ^ 2 := mul_lt_mul_of_pos_right htot hm2n_pos
      _ = ((P.m : ℝ) ^ n) ^ 2 := one_mul _
  -- Extract a witness φ = (φ_R, φ_B) with badProb φ < 1!
  have hex_φ : ∃ φ : (Fin n → Fin P.m) × (Fin n → Fin P.m), badProb φ < 1 := by
    by_contra hall; push Not at hall
    have hge : ((P.m : ℝ) ^ n) ^ 2 ≤ ∑ φ : (Fin n → Fin P.m) × (Fin n → Fin P.m), badProb φ := by
      calc ((P.m : ℝ) ^ n) ^ 2
          = ∑ _φ : (Fin n → Fin P.m) × (Fin n → Fin P.m), (1 : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fun,
              Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_mul, Nat.cast_pow, sq]
        _ ≤ ∑ φ : (Fin n → Fin P.m) × (Fin n → Fin P.m), badProb φ := Finset.sum_le_sum fun φ _ => hall φ
    linarith only [hge, hsum_bad]
  rcases hex_φ with ⟨⟨φ_R, φ_B⟩, hφlt⟩
  -- Extract ω = (ω_R, ω_B) avoiding the bad event!
  have hex_ω : ∃ ω : EdgeIdx P.m ⊕ EdgeIdx P.m → Bool, ¬ badEv (φ_R, φ_B) ω := by
    by_contra hall; push Not at hall
    have heq1 : badProb (φ_R, φ_B) = 1 := by
      dsimp only [badProb, bernProb]
      calc _ = ∑ ω : EdgeIdx P.m ⊕ EdgeIdx P.m → Bool, bernW P.p ω :=
            Finset.sum_congr rfl fun ω _ => if_pos (hall ω)
        _ = 1 := sum_bernW_eq_one P.p
    linarith only [heq1, hφlt]
  rcases hex_ω with ⟨ω, hω⟩
  dsimp only [badEv] at hω
  push Not at hω
  rcases hω with ⟨hfR, hfB, hGR, hGB, hnoI⟩
  refine ⟨buildGraph (graphOf (fun e => ω (Sum.inl e))) (graphOf (fun e => ω (Sum.inr e))) φ_R φ_B,
    buildGraph_cliqueFree _ _ _ _, ?_⟩
  intro I hI
  by_contra hge; push Not at hge
  obtain ⟨J, hJsub, hJcard⟩ := Finset.exists_subset_card_eq hge
  have hJind : (buildGraph (graphOf (fun e => ω (Sum.inl e)))
      (graphOf (fun e => ω (Sum.inr e))) φ_R φ_B).IsIndepSet (J : Set (Fin n)) :=
    hI.mono (Finset.coe_subset.mpr hJsub)
  exact hnoI J (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hJcard⟩) hfR hfB hGR hGB hJind

/-- Finite Ramsey lower bound transfer: a triangle-free graph on `Fin N` with no independent
set of size `k` witnesses `N < SimpleGraph.classicalRamsey 3 k`. -/
lemma witness_lt_classicalRamsey {N k : ℕ} (G : SimpleGraph (Fin N))
    (htri : G.CliqueFree 3) (hind : ∀ I : Finset (Fin N), G.IsIndepSet (I : Set (Fin N)) → I.card < k) :
    N < SimpleGraph.classicalRamsey 3 k := by
  have hindFree : G.IndepSetFree k := fun I hI => by
    have := hind I hI.1; rw [hI.2] at this; omega
  let P (v : ℕ) : Prop := ∀ H : SimpleGraph (Fin v),
    (SimpleGraph.completeGraph (Fin 3)).IsContained H ∨
    (SimpleGraph.completeGraph (Fin k)).IsContained Hᶜ
  have hne : {v : ℕ | P v}.Nonempty := by
    refine ⟨(k + 3).choose k, fun H => ?_⟩
    let c : Finset (Fin ((k + 3).choose k)) → Bool := fun e => decide (H.IsClique (e : Set _))
    obtain ⟨S, _, hcard, hS⟩ | ⟨S, _, hcard, hS⟩ :=
      Combinatorics.Diagonal.hasRamseyProperty_choose k 3 c Finset.univ (by simp)
    · right
      rw [← SimpleGraph.not_cliqueFree_iff_top_isContained]
      intro hcf
      refine hcf S ⟨?_, hcard⟩
      intro x hx y hy hxy
      have hfalse := hS {x, y} (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))
        (Finset.card_pair hxy)
      have hnot : ¬ H.IsClique (({x, y} : Finset _) : Set _) := by
        simpa [c] using hfalse
      rw [SimpleGraph.compl_adj]
      refine ⟨hxy, fun hadj => hnot ?_⟩
      intro a ha b hb hab
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact False.elim (hab rfl)
      · exact hadj
      · exact hadj.symm
      · exact False.elim (hab rfl)
    · left
      rw [← SimpleGraph.not_cliqueFree_iff_top_isContained]
      intro hcf
      refine hcf S ⟨?_, hcard⟩
      intro x hx y hy hxy
      have htrue := hS {x, y} (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))
        (Finset.card_pair hxy)
      have hcl : H.IsClique (({x, y} : Finset _) : Set _) := of_decide_eq_true htrue
      exact hcl (by simp) (by simp) hxy
  have hmono : ∀ {v w : ℕ}, v ≤ w → P v → P w := by
    intro v w hvw hv H
    let e : Fin v ↪ Fin w := Fin.castLEEmb hvw
    let emb : H.comap e ↪g H := SimpleGraph.Embedding.comap e H
    let embc : (H.comap e)ᶜ ↪g Hᶜ := SimpleGraph.Embedding.complEquiv emb
    rcases hv (H.comap e) with h1 | h2
    · exact Or.inl (h1.trans emb.isContained)
    · exact Or.inr (h2.trans embc.isContained)
  by_contra hle; push Not at hle
  have hPR : P (SimpleGraph.classicalRamsey 3 k) := Nat.sInf_mem hne
  have hPN : P N := hmono hle hPR
  rcases hPN G with h3 | hk
  · exact ((SimpleGraph.not_cliqueFree_iff_top_isContained 3).mpr h3) htri
  · exact ((SimpleGraph.not_cliqueFree_iff_top_isContained k).mpr hk) (G.cliqueFree_compl.mpr hindFree)

/-- Analytic inversion: if for every `ε > 0` and all sufficiently large `n` there is a triangle-free
graph on `Fin n` with independence number `< (1 + ε) √(n log n)`, then
`Erdos165.erdos_165.variants.lower` holds. -/
lemma lower_of_indep_bound
    (hIndep : ∀ ε > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧
        ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) →
          (I.card : ℝ) < (1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) :
    ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in Filter.atTop,
      (1 / 2 - ε) * (k : ℝ) ^ 2 / Real.log k ≤ (SimpleGraph.classicalRamsey 3 k : ℝ) := by
  intro ε hε
  by_cases hbig : 1 / 2 ≤ ε
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with k hk
    have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
    have hlog : 0 < Real.log (k : ℝ) := Real.log_pos hk1
    have hneg : (1 / 2 - ε) * (k : ℝ) ^ 2 / Real.log (k : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)) hlog.le
    exact hneg.trans (Nat.cast_nonneg _)
  push Not at hbig
  obtain ⟨n₀, hn₀⟩ := hIndep (ε / 4) (by linarith)
  let k₀ : ℕ := max 3 (max ⌈(n₀ : ℝ) / (1 / 2 - ε)⌉₊ ⌈2 / ε⌉₊)
  rw [Filter.eventually_atTop]
  refine ⟨k₀, fun k hk => ?_⟩
  have hk3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans (le_max_left 3 _) hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hlog_ge1 : (1 : ℝ) ≤ Real.log (k : ℝ) := by
    have hexp : Real.exp 1 ≤ (k : ℝ) := by linarith [Real.exp_one_lt_d9]
    have h1 := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at h1
  have hlog_pos : 0 < Real.log (k : ℝ) := by linarith
  have hk_le_div : (k : ℝ) ≤ (k : ℝ) ^ 2 / Real.log (k : ℝ) := by
    rw [le_div_iff₀ hlog_pos]
    have := Real.log_le_sub_one_of_pos hk_pos
    nlinarith
  set x : ℝ := (1 / 2 - ε) * (k : ℝ) ^ 2 / Real.log (k : ℝ)
  have hx_pos : 0 < x := by dsimp only [x]; positivity
  let N : ℕ := ⌈x⌉₊
  have hN_ge : x ≤ (N : ℝ) := Nat.le_ceil x
  have hN_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le hx_pos hN_ge
  have hn0_le : n₀ ≤ N := by
    have h1 : (n₀ : ℝ) / (1 / 2 - ε) ≤ (k : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_right 3 _)) hk)
    have h2 : (n₀ : ℝ) ≤ (1 / 2 - ε) * (k : ℝ) := by
      have := (div_le_iff₀ (show (0 : ℝ) < 1 / 2 - ε by linarith)).mp h1; linarith
    have h3 : (1 / 2 - ε) * (k : ℝ) ≤ x := by
      have := mul_le_mul_of_nonneg_left hk_le_div (show (0 : ℝ) ≤ 1 / 2 - ε by linarith)
      dsimp only [x]; linarith [mul_div_assoc (1 / 2 - ε) ((k : ℝ) ^ 2) (Real.log (k : ℝ))]
    exact_mod_cast h2.trans (h3.trans hN_ge)
  obtain ⟨G, htri, hind⟩ := hn₀ N hn0_le
  have hN_lt : (N : ℝ) < x + 1 := Nat.ceil_lt_add_one hx_pos.le
  have h1_le : (1 : ℝ) ≤ (ε / 2) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) := by
    have h1 : 2 / ε ≤ (k : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right 3 _)) hk)
    have h2 : 2 ≤ ε * (k : ℝ) := by have := (div_le_iff₀ hε).mp h1; linarith
    have h3 := mul_le_mul_of_nonneg_left hk_le_div (show (0 : ℝ) ≤ ε / 2 by linarith)
    linarith
  have hN_up : (N : ℝ) ≤ ((1 - ε) / 2) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) := by
    have : x + (ε / 2) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) =
        ((1 - ε) / 2) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) := by dsimp only [x]; ring
    linarith
  have hN_le_sq : (N : ℝ) ≤ (k : ℝ) ^ 2 := by
    have hdiv : (k : ℝ) ^ 2 / Real.log (k : ℝ) ≤ (k : ℝ) ^ 2 := div_le_self (by positivity) hlog_ge1
    nlinarith
  have hlogN_le : Real.log (N : ℝ) ≤ 2 * Real.log (k : ℝ) := by
    have h1 := Real.log_le_log hN_pos hN_le_sq
    rw [Real.log_pow] at h1; simpa using h1
  have hthr : (1 + ε / 4) * Real.sqrt ((N : ℝ) * Real.log (N : ℝ)) < (k : ℝ) := by
    by_cases hln : 0 ≤ Real.log (N : ℝ)
    · have hprod : (N : ℝ) * Real.log (N : ℝ) ≤ (1 - ε) * (k : ℝ) ^ 2 := by
        have h1me : 0 ≤ (1 - ε) / 2 := by linarith
        calc (N : ℝ) * Real.log (N : ℝ)
            ≤ (((1 - ε) / 2) * ((k : ℝ) ^ 2 / Real.log (k : ℝ))) * (2 * Real.log (k : ℝ)) :=
              mul_le_mul hN_up hlogN_le hln (by positivity)
          _ = (1 - ε) * (k : ℝ) ^ 2 := by field_simp [hlog_pos.ne']
      have hcoeff : (1 + ε / 4) ^ 2 * (1 - ε) < 1 := by
        have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
        have hε3 : 0 < ε ^ 3 := pow_pos hε 3
        nlinarith
      have hsq : ((1 + ε / 4) * Real.sqrt ((N : ℝ) * Real.log (N : ℝ))) ^ 2 < (k : ℝ) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (mul_nonneg hN_pos.le hln)]
        have hk2 : 0 < (k : ℝ) ^ 2 := sq_pos_of_pos hk_pos
        nlinarith [mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ (1 + ε / 4) ^ 2)]
      nlinarith [show 0 ≤ (1 + ε / 4) * Real.sqrt ((N : ℝ) * Real.log (N : ℝ)) by positivity]
    · rw [Real.sqrt_eq_zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hN_pos.le (le_of_not_ge hln)), mul_zero]
      exact hk_pos
  have hind_nat : ∀ I : Finset (Fin N), G.IsIndepSet (I : Set (Fin N)) → I.card < k := fun I hI => by
    exact_mod_cast (hind I hI).trans hthr
  have hram : (N : ℝ) ≤ (SimpleGraph.classicalRamsey 3 k : ℝ) := by
    exact_mod_cast (witness_lt_classicalRamsey G htri hind_nat).le
  exact hN_ge.trans hram

end MasterAlgAndExistence

/- ### Section 4B: Asymptotic Parameter Verification and Proof of `Erdos165.erdos_165.variants.lower` -/

section AsymptoticsAndMain

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
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith only [hn2]
  have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith only [hn2])
  have hlog_le : Real.log (n : ℝ) ≤ (n : ℝ) ^ ε / ε := by
    have h1 : Real.log ((n : ℝ) ^ ε) ≤ (n : ℝ) ^ ε - 1 :=
      Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hn_pos ε)
    rw [Real.log_rpow hn_pos] at h1
    rw [le_div_iff₀ hε]; linarith only [h1]
  have hpow_le : (Real.log (n : ℝ)) ^ b ≤ (n : ℝ) ^ ((b : ℝ) * ε) / ε ^ b := by
    calc (Real.log (n : ℝ)) ^ b ≤ ((n : ℝ) ^ ε / ε) ^ b := pow_le_pow_left₀ hlog_nn hlog_le b
      _ = ((n : ℝ) ^ ε) ^ b / ε ^ b := div_pow _ _ _
      _ = (n : ℝ) ^ ((b : ℝ) * ε) / ε ^ b := by
          congr 1; rw [← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le, mul_comm]
  have hbe_le : (b : ℝ) * ε ≤ a / 2 := by
    simp only [ε]
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
    nlinarith only [ha, Nat.cast_nonneg (α := ℝ) b]
  have hn_pow_le : (n : ℝ) ^ ((b : ℝ) * ε) ≤ (n : ℝ) ^ (a / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith only [hn2]) hbe_le
  have hM_lt : M < (n : ℝ) ^ (a / 2) := by
    have hn_gt : M ^ (2 / a) < (n : ℝ) := by
      have hceil : Nat.ceil (M ^ (2 / a)) + 1 ≤ n := le_trans (le_max_right _ _) hn
      have h1 : M ^ (2 / a) ≤ (Nat.ceil (M ^ (2 / a)) : ℝ) := Nat.le_ceil _
      have h2 : (Nat.ceil (M ^ (2 / a)) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hceil
      linarith only [h1, h2]
    have h3 : (M ^ (2 / a)) ^ (a / 2) < (n : ℝ) ^ (a / 2) :=
      Real.rpow_lt_rpow (Real.rpow_nonneg hM.le _) hn_gt (by positivity)
    have h4 : (M ^ (2 / a)) ^ (a / 2) = M := by
      rw [← Real.rpow_mul hM.le]
      have : (2 / a) * (a / 2) = 1 := by field_simp [ha.ne']
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
    linarith only [h2, h3]
  exact (Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos c) h1)).mpr h1

/-- Concrete construction parameters for `n : ℕ` and `ε' ∈ (0, 1/4]`. -/
noncomputable def mkParams (ε' : ℝ) (n : ℕ) : RegParams :=
  let L_log : ℝ := Real.log (n : ℝ)
  let m : ℕ := ⌈(n : ℝ) / L_log ^ 5⌉₊
  let p : ℝ := Real.sqrt (L_log / (n : ℝ)) / 2
  let k : ℕ := ⌈(1 + ε') * Real.sqrt ((n : ℝ) * L_log)⌉₊
  let η₀ : ℝ := ε' / 16
  let F_max : ℝ := (1 + η₀) * ((n : ℝ) / (m : ℝ))
  { m := m
    k := k
    p := p
    η₀ := η₀
    C_codeg := ⌈L_log⌉₊
    L := Nat.log 2 ⌊F_max⌋₊ + 1
    J := Nat.log 2 m + 1
    T_lo := L_log ^ 2
    T_cut := L_log ^ 4
    T_mid := (n : ℝ) ^ (1 / 10 : ℝ)
    T_big := (k : ℝ) / L_log ^ 3
    B_mid := L_log ^ 3
    B_cross := L_log ^ 3 }

/-- Elementary `log x ≤ 4 * x ^ (1/4)` for `x > 0`. -/
lemma log_le_four_rpow_quarter {x : ℝ} (hx : 0 < x) : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
  have h1 : Real.log (x ^ (1 / 4 : ℝ)) ≤ x ^ (1 / 4 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx (1 / 4 : ℝ))
  rw [Real.log_rpow hx] at h1
  linarith only [h1]

/-- Elementary `log_2 N ≤ 2 * log N` for `N ≥ 1`. -/
lemma nat_log2_le_two_mul_log {N : ℕ} (hN : 1 ≤ N) : (Nat.log 2 N : ℝ) ≤ 2 * Real.log (N : ℝ) := by
  have h1 : ((2 ^ Nat.log 2 N : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hpow : ((2 ^ Nat.log 2 N : ℕ) : ℝ) = (2 : ℝ) ^ Nat.log 2 N := by push_cast; rfl
  rw [hpow] at h1
  have hlog := Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at hlog
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h2 : Real.exp (1 / 2 : ℝ) ≤ 2 := by
      have hsq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; norm_num
      have he : Real.exp 1 < 4 := by linarith only [Real.exp_one_lt_d9]
      nlinarith only [hsq, he, Real.exp_pos (1 / 2 : ℝ)]
    have := Real.log_le_log (Real.exp_pos (1 / 2 : ℝ)) h2
    rwa [Real.log_exp] at this
  nlinarith only [hlog, hlog2, Nat.cast_nonneg (α := ℝ) (Nat.log 2 N)]

/-- Tiny helper: `C ≤ 10^12 / ε'^2` for `C ≤ 10^12` and `0 < ε' ≤ 1/4`. -/
lemma const_le_big_div_sq {C ε' : ℝ} (hC : C ≤ 10 ^ 12) (hε0 : 0 < ε') (hε1 : ε' ≤ 1 / 4) :
    C ≤ 10 ^ 12 / ε' ^ 2 := by
  rw [le_div_iff₀ (sq_pos_of_pos hε0)]
  have hsq : ε' ^ 2 ≤ 1 := by nlinarith only [hε0, hε1]
  nlinarith only [hC, hsq, sq_pos_of_pos hε0]

/-- Tiny helper: from `(10^12 / ε'^2) * L^20 < n^(1/20)` deduce `C * L^b < n^(1/20)` for `C ≤ 10^12, b ≤ 20`. -/
lemma log_pow_lt_rpow_of_big {n : ℕ} {ε' C : ℝ} {b : ℕ} (hb : b ≤ 20) (hC : C ≤ 10 ^ 12)
    (hε0 : 0 < ε') (hε1 : ε' ≤ 1 / 4) (hL1 : 1 ≤ Real.log (n : ℝ))
    (hrp : (10 ^ 12 / ε' ^ 2) * Real.log (n : ℝ) ^ 20 < (n : ℝ) ^ (1 / 20 : ℝ)) :
    C * Real.log (n : ℝ) ^ b < (n : ℝ) ^ (1 / 20 : ℝ) := by
  have hLb : Real.log (n : ℝ) ^ b ≤ Real.log (n : ℝ) ^ 20 := pow_le_pow_right₀ hL1 hb
  have h1 : C ≤ 10 ^ 12 / ε' ^ 2 := const_le_big_div_sq hC hε0 hε1
  have hLnn : 0 ≤ Real.log (n : ℝ) ^ b := pow_nonneg (by linarith only [hL1]) b
  have h2 : C * Real.log (n : ℝ) ^ b ≤ (10 ^ 12 / ε' ^ 2) * Real.log (n : ℝ) ^ 20 :=
    (mul_le_mul_of_nonneg_right h1 hLnn).trans (mul_le_mul_of_nonneg_left hLb (by positivity))
  linarith only [h2, hrp]

/-- Tiny helper: `n * (√(L / n) / 2) = √(n * L) / 2` for `n > 0, L > 0`. -/
lemma mul_sqrt_div_two {n_r L : ℝ} (hn : 0 < n_r) (hL : 0 < L) :
    n_r * (Real.sqrt (L / n_r) / 2) = Real.sqrt (n_r * L) / 2 := by
  rw [Real.sqrt_div hL.le, Real.sqrt_mul hn.le]
  have hsq : Real.sqrt n_r * Real.sqrt n_r = n_r := Real.mul_self_sqrt hn.le
  have hne : Real.sqrt n_r ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  calc n_r * (Real.sqrt L / Real.sqrt n_r / 2)
      = (Real.sqrt n_r * Real.sqrt n_r) * (Real.sqrt L / Real.sqrt n_r / 2) := by rw [hsq]
    _ = Real.sqrt n_r * Real.sqrt L / 2 := by field_simp [hne]

/-- Helper 1A: Basic scale bounds and `ValidRegParams` for `mkParams ε' n`. -/
lemma asymp_basic_scales {ε' : ℝ} (hε0 : 0 < ε') (hε1 : ε' ≤ 1 / 4) :
    ∀ᶠ n : ℕ in Filter.atTop,
      let P := mkParams ε' n
      let L_log := Real.log (n : ℝ)
      let F_max := (1 + P.η₀) * ((n : ℝ) / (P.m : ℝ))
      let D := F_max * ((1 + P.η₀) * ((P.m : ℝ) * P.p))
      ValidRegParams P F_max ∧
      (100 < L_log) ∧
      ((n : ℝ) / L_log ^ 5 ≤ (P.m : ℝ) ∧ (P.m : ℝ) ≤ 2 * (n : ℝ) / L_log ^ 5) ∧
      (L_log ^ 5 / 2 ≤ (n : ℝ) / (P.m : ℝ) ∧ (n : ℝ) / (P.m : ℝ) ≤ L_log ^ 5) ∧
      (1 ≤ F_max ∧ F_max ≤ 2 * L_log ^ 5) ∧
      ((1 + ε') * Real.sqrt ((n : ℝ) * L_log) ≤ (P.k : ℝ) ∧
        (P.k : ℝ) ≤ (1 + 2 * ε') * Real.sqrt ((n : ℝ) * L_log)) ∧
      ((P.L : ℝ) ≤ 50 * L_log ^ (1 / 4 : ℝ) ∧ (P.J : ℝ) ≤ 3 * L_log) ∧
      (1 / (2 * (1 + ε')) ≤ D / (P.k : ℝ) ∧ D / (P.k : ℝ) ≤ 1 / 2 - ε' / 4) := by
  have h1 := eventually_lt_log (max 100 (1000 / ε' ^ 2))
  have h2 := eventually_log_pow_lt_rpow (a := (1 / 20 : ℝ)) (by norm_num) 20 (10 ^ 12 / ε' ^ 2)
  filter_upwards [h1, h2, Filter.eventually_ge_atTop (1000 : ℕ)] with n hlog_big hrpow1 hn_ge
  set P := mkParams ε' n
  set L_log := Real.log (n : ℝ)
  set F_max := (1 + P.η₀) * ((n : ℝ) / (P.m : ℝ))
  set D := F_max * ((1 + P.η₀) * ((P.m : ℝ) * P.p))
  have hL100 : 100 < L_log := lt_of_le_of_lt (le_max_left _ _) hlog_big
  have hL1 : (1 : ℝ) ≤ L_log := by linarith only [hL100]
  have hLpos : 0 < L_log := by linarith only [hL100]
  have hn_ge1000 : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith only [hn_ge1000]
  have hn120_pos : 0 < (n : ℝ) ^ (1 / 20 : ℝ) := Real.rpow_pos_of_pos hn_pos _
  have hn120_ge1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 20 : ℝ) := Real.one_le_rpow (by linarith only [hn_ge1000]) (by norm_num)
  have hn120_le_n : (n : ℝ) ^ (1 / 20 : ℝ) ≤ (n : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith only [hn_ge1000] : (1 : ℝ) ≤ (n : ℝ)) (by norm_num : (1 / 20 : ℝ) ≤ 1)
  have hn110_eq : (n : ℝ) ^ (1 / 10 : ℝ) = ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; congr 1; norm_num
  have hn12_eq : Real.sqrt (n : ℝ) = ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 10 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; congr 1; norm_num
  have hL5_lt_n : L_log ^ 5 < (n : ℝ) / 2 := by
    have hlt := log_pow_lt_rpow_of_big (C := 2) (b := 5) (by omega) (by norm_num) hε0 hε1 hL1 hrpow1
    linarith only [hlt, hn120_le_n]
  -- Bounds on m = ⌈n / L_log^5⌉₊
  have hm_lo : (n : ℝ) / L_log ^ 5 ≤ (P.m : ℝ) := Nat.le_ceil _
  have hm_hi : (P.m : ℝ) ≤ 2 * (n : ℝ) / L_log ^ 5 := by
    have hcl := Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) / L_log ^ 5 by positivity)
    have h1 : (1 : ℝ) ≤ (n : ℝ) / L_log ^ 5 := (one_le_div (by positivity)).mpr (by linarith only [hL5_lt_n])
    have hmeq : (P.m : ℝ) = (⌈(n : ℝ) / L_log ^ 5⌉₊ : ℝ) := rfl
    linarith only [hcl, h1, hmeq, show 2 * (n : ℝ) / L_log ^ 5 = (n : ℝ) / L_log ^ 5 + (n : ℝ) / L_log ^ 5 by ring]
  have hm_pos : (0 : ℝ) < (P.m : ℝ) := lt_of_lt_of_le (by positivity) hm_lo
  have hnm_lo : L_log ^ 5 / 2 ≤ (n : ℝ) / (P.m : ℝ) := by
    rw [div_le_div_iff₀ (by norm_num) hm_pos]
    have h1 : (P.m : ℝ) * L_log ^ 5 ≤ 2 * (n : ℝ) := (le_div_iff₀ (show (0 : ℝ) < L_log ^ 5 by positivity)).mp hm_hi
    linarith only [h1]
  have hnm_hi : (n : ℝ) / (P.m : ℝ) ≤ L_log ^ 5 := by
    rw [div_le_iff₀ hm_pos]
    have h1 := (div_le_iff₀ (show (0 : ℝ) < L_log ^ 5 by positivity)).mp hm_lo
    linarith only [h1]
  -- Bounds on F_max = (1 + η₀) * (n / m)
  have hη0_pos : 0 < P.η₀ := by dsimp only [P, mkParams]; linarith only [hε0]
  have hη0_le : P.η₀ ≤ 1 / 64 := by dsimp only [P, mkParams]; linarith only [hε1]
  have hF_lo : L_log ^ 5 / 2 ≤ F_max := by
    dsimp only [F_max]; nlinarith only [hη0_pos, hnm_lo, show (0 : ℝ) ≤ L_log ^ 5 by positivity]
  have hF1 : 1 ≤ F_max := by
    have h100 : (100 : ℝ) ^ 5 ≤ L_log ^ 5 := pow_le_pow_left₀ (by norm_num) hL100.le 5
    linarith only [hF_lo, h100]
  have hF_hi : F_max ≤ 2 * L_log ^ 5 := by
    dsimp only [F_max]; nlinarith only [hη0_pos, hη0_le, hnm_hi, show (0 : ℝ) ≤ (n : ℝ) / (P.m : ℝ) by positivity]
  -- Bounds on k
  have hk_lo : (1 + ε') * Real.sqrt ((n : ℝ) * L_log) ≤ (P.k : ℝ) := Nat.le_ceil _
  have hsqrt_big : 16 / ε' < Real.sqrt ((n : ℝ) * L_log) := by
    have h1 : (16 / ε') ^ 2 < (n : ℝ) * L_log := by
      have hL20 : (1 : ℝ) ≤ L_log ^ 20 := one_le_pow₀ hL1
      have h256 : (16 / ε') ^ 2 ≤ (10 ^ 12 / ε' ^ 2) * L_log ^ 20 := by
        have hrew : (16 / ε') ^ 2 = 256 / ε' ^ 2 := by ring
        rw [hrew]
        have hdiv : 256 / ε' ^ 2 ≤ 10 ^ 12 / ε' ^ 2 := div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)
        have hnn : (0 : ℝ) ≤ 10 ^ 12 / ε' ^ 2 := by positivity
        nlinarith only [hdiv, hL20, hnn]
      nlinarith only [h256, hrpow1, hn120_le_n, hL100, hn_pos]
    exact Real.lt_sqrt_of_sq_lt h1
  have hk_hi : (P.k : ℝ) ≤ (1 + 2 * ε') * Real.sqrt ((n : ℝ) * L_log) := by
    have hcl := Nat.ceil_lt_add_one (show 0 ≤ (1 + ε') * Real.sqrt ((n : ℝ) * L_log) by positivity)
    have h1 : (1 : ℝ) ≤ ε' * Real.sqrt ((n : ℝ) * L_log) := by
      have h2 := (div_lt_iff₀ hε0).mp hsqrt_big; linarith only [h2]
    have hkeq : (P.k : ℝ) = (⌈(1 + ε') * Real.sqrt ((n : ℝ) * L_log)⌉₊ : ℝ) := rfl
    linarith only [hcl, h1, hkeq]
  have hk_hi2 : (P.k : ℝ) ≤ 2 * Real.sqrt ((n : ℝ) * L_log) := by
    nlinarith only [hk_hi, hε1, Real.sqrt_nonneg ((n : ℝ) * L_log)]
  have hk_pos : (0 : ℝ) < (P.k : ℝ) := lt_of_lt_of_le (by positivity) hk_lo
  -- Bounds on p and D / k
  have hp0 : 0 ≤ P.p := by dsimp only [P, mkParams]; positivity
  have hp1 : P.p ≤ 1 := by
    dsimp only [P, mkParams]
    have h1 : L_log / (n : ℝ) ≤ 1 := (div_le_one hn_pos).mpr (by linarith only [Real.log_le_sub_one_of_pos hn_pos])
    have h2 : Real.sqrt (L_log / (n : ℝ)) ≤ 1 := Real.sqrt_le_one.mpr h1
    linarith only [h2]
  have hnp_eq : (n : ℝ) * P.p = Real.sqrt ((n : ℝ) * L_log) / 2 := mul_sqrt_div_two hn_pos hLpos
  have hD_eq : D = (1 + P.η₀) ^ 2 * (Real.sqrt ((n : ℝ) * L_log) / 2) := by
    dsimp only [D, F_max]; rw [← hnp_eq]; field_simp [hm_pos.ne']
  have hρ_hi : D / (P.k : ℝ) ≤ 1 / 2 - ε' / 4 := by
    rw [div_le_iff₀ hk_pos, hD_eq]
    have hcoef : (1 + P.η₀) ^ 2 / 2 ≤ (1 / 2 - ε' / 4) * (1 + ε') := by
      have hηdef : P.η₀ = ε' / 16 := rfl
      rw [hηdef]; nlinarith only [hε0, hε1]
    have hsr : 0 ≤ Real.sqrt ((n : ℝ) * L_log) := Real.sqrt_nonneg _
    have hmul1 : (1 / 2 - ε' / 4) * ((1 + ε') * Real.sqrt ((n : ℝ) * L_log)) ≤ (1 / 2 - ε' / 4) * (P.k : ℝ) :=
      mul_le_mul_of_nonneg_left hk_lo (by linarith only [hε1])
    nlinarith only [hcoef, hsr, hmul1]
  have hρ_lo : 1 / (2 * (1 + ε')) ≤ D / (P.k : ℝ) := by
    rw [div_le_div_iff₀ (by linarith only [hε0]) hk_pos, one_mul, hD_eq]
    have hcl : (P.k : ℝ) ≤ (1 + ε') * Real.sqrt ((n : ℝ) * L_log) + 1 :=
      (Nat.ceil_lt_add_one (show 0 ≤ (1 + ε') * Real.sqrt ((n : ℝ) * L_log) by positivity)).le
    have h1 : (1 : ℝ) ≤ (ε' / 16) * Real.sqrt ((n : ℝ) * L_log) := by
      have h2 := (div_lt_iff₀ hε0).mp hsqrt_big; linarith only [h2]
    have hk_tight : (P.k : ℝ) ≤ (1 + ε') * (1 + P.η₀) ^ 2 * Real.sqrt ((n : ℝ) * L_log) := by
      have hηdef : P.η₀ = ε' / 16 := rfl
      have hsr : 0 ≤ Real.sqrt ((n : ℝ) * L_log) := Real.sqrt_nonneg _
      have hsq : 0 ≤ ε' ^ 2 := sq_nonneg ε'
      have hcu : 0 ≤ ε' ^ 3 := pow_nonneg hε0.le 3
      have hcoef : (1 + ε') + ε' / 16 ≤ (1 + ε') * (1 + ε' / 16) ^ 2 := by
        linarith only [hε0, hsq, hcu,
          show (1 + ε') * (1 + ε' / 16) ^ 2 = (1 + ε') + ε' / 16 + (ε' / 16 + 33 / 256 * ε' ^ 2 + 1 / 256 * ε' ^ 3) by ring]
      have hmul := mul_le_mul_of_nonneg_right hcoef hsr
      rw [hηdef]
      linarith only [hcl, h1, hmul,
        show ((1 + ε') + ε' / 16) * Real.sqrt ((n : ℝ) * L_log) =
          (1 + ε') * Real.sqrt ((n : ℝ) * L_log) + (ε' / 16) * Real.sqrt ((n : ℝ) * L_log) by ring]
    linarith only [hk_tight]
  -- Bounds on P.L and P.J
  have hL_bound : (P.L : ℝ) ≤ 50 * L_log ^ (1 / 4 : ℝ) := by
    have hLdef : P.L = Nat.log 2 ⌊F_max⌋₊ + 1 := rfl
    have hfl_ge1 : 1 ≤ ⌊F_max⌋₊ := Nat.floor_pos.mpr hF1
    have hlog2 := nat_log2_le_two_mul_log hfl_ge1
    have hfl_le : (⌊F_max⌋₊ : ℝ) ≤ 2 * L_log ^ 5 := (Nat.floor_le (by linarith only [hF1])).trans hF_hi
    have hlog_fl : Real.log (⌊F_max⌋₊ : ℝ) ≤ Real.log (2 * L_log ^ 5) :=
      Real.log_le_log (by exact_mod_cast hfl_ge1) hfl_le
    have hlog_2L5 : Real.log (2 * L_log ^ 5) ≤ 6 * Real.log L_log := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      have hlog2_lt : Real.log 2 ≤ Real.log L_log := Real.log_le_log (by norm_num) (by linarith only [hL100])
      push_cast; linarith only [hlog2_lt]
    have hlogL := log_le_four_rpow_quarter hLpos
    have h1le : (1 : ℝ) ≤ L_log ^ (1 / 4 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    rw [hLdef, Nat.cast_add, Nat.cast_one]
    linarith only [hlog2, hlog_fl, hlog_2L5, hlogL, h1le]
  have hJ_bound : (P.J : ℝ) ≤ 3 * L_log := by
    have hJdef : P.J = Nat.log 2 P.m + 1 := rfl
    have hdiv1 : (1 : ℝ) ≤ (n : ℝ) / L_log ^ 5 := (one_le_div (by positivity)).mpr (by linarith only [hL5_lt_n])
    have hm1 : 1 ≤ P.m := by exact_mod_cast (by linarith only [hm_lo, hdiv1] : (1 : ℝ) ≤ (P.m : ℝ))
    have hlog2 := nat_log2_le_two_mul_log hm1
    have hm_le_n : (P.m : ℝ) ≤ (n : ℝ) := by
      have h2L5 : 2 / L_log ^ 5 ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : (100 : ℝ) ^ 5 ≤ L_log ^ 5 := pow_le_pow_left₀ (by norm_num) hL100.le 5
        linarith only [this]
      calc (P.m : ℝ) ≤ 2 * (n : ℝ) / L_log ^ 5 := hm_hi
        _ = (2 / L_log ^ 5) * (n : ℝ) := by ring
        _ ≤ 1 * (n : ℝ) := mul_le_mul_of_nonneg_right h2L5 hn_pos.le
        _ = (n : ℝ) := one_mul _
    have hlog_m : Real.log (P.m : ℝ) ≤ L_log := Real.log_le_log hm_pos hm_le_n
    rw [hJdef, Nat.cast_add, Nat.cast_one]; linarith only [hlog2, hlog_m, hL100]
  -- ValidRegParams P F_max
  have h2k_le_m : 2 * P.k ≤ P.m := by
    have hreal : (2 * P.k : ℝ) ≤ (P.m : ℝ) := by
      have hsr : Real.sqrt ((n : ℝ) * L_log) ≤ (n : ℝ) / (4 * L_log ^ 5) := by
        have h1 : (n : ℝ) * L_log ≤ ((n : ℝ) / (4 * L_log ^ 5)) ^ 2 := by
          rw [div_pow, le_div_iff₀ (by positivity)]
          have hL11 := log_pow_lt_rpow_of_big (C := 16) (b := 11) (by omega) (by norm_num) hε0 hε1 hL1 hrpow1
          have h16_lt_n : 16 * L_log ^ 11 < (n : ℝ) := lt_of_lt_of_le hL11 hn120_le_n
          have hrew : (n : ℝ) * L_log * (4 * L_log ^ 5) ^ 2 = (n : ℝ) * (16 * L_log ^ 11) := by ring
          rw [hrew]; nlinarith only [h16_lt_n, hn_pos]
        exact Real.sqrt_le_iff.mpr ⟨by positivity, h1⟩
      have h4 : 4 * Real.sqrt ((n : ℝ) * L_log) ≤ (n : ℝ) / L_log ^ 5 := by
        have := mul_le_mul_of_nonneg_left hsr (by norm_num : (0 : ℝ) ≤ 4)
        linarith only [this, show 4 * ((n : ℝ) / (4 * L_log ^ 5)) = (n : ℝ) / L_log ^ 5 by ring]
      linarith only [hk_hi2, h4, hm_lo]
    exact_mod_cast hreal
  have hsr_n_le_k : Real.sqrt (n : ℝ) ≤ (P.k : ℝ) := by
    have h1 : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) * L_log) :=
      Real.sqrt_le_sqrt (by nlinarith only [hn_pos, hL100])
    nlinarith only [h1, hk_lo, hε0, Real.sqrt_nonneg ((n : ℝ) * L_log)]
  have hTmid_lt_big : P.T_mid < P.T_big / 2 := by
    dsimp only [P, mkParams]
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2), lt_div_iff₀ (by positivity)]
    have hL3 := log_pow_lt_rpow_of_big (C := 2) (b := 3) (by omega) (by norm_num) hε0 hε1 hL1 hrpow1
    have hpow3 : ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 3 ≤ ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 10 :=
      pow_le_pow_right₀ hn120_ge1 (by omega)
    have h1 : 2 * (n : ℝ) ^ (1 / 10 : ℝ) * L_log ^ 3 < Real.sqrt (n : ℝ) := by
      rw [hn110_eq, hn12_eq]
      have hmul := mul_lt_mul_of_pos_left hL3 (pow_pos hn120_pos 2)
      nlinarith only [hmul, hpow3]
    have hkeq : (⌈(1 + ε') * Real.sqrt ((n : ℝ) * L_log)⌉₊ : ℝ) = (P.k : ℝ) := rfl
    rw [hkeq]; linarith only [h1, hsr_n_le_k]
  have hTbig_lt_J : P.T_big < ((2 ^ P.J : ℕ) : ℝ) := by
    have hm_lt : P.m < 2 ^ P.J := Nat.lt_pow_succ_log_self (by omega : 1 < 2) P.m
    have hTbig_le_k : P.T_big ≤ (P.k : ℝ) := by
      dsimp only [P, mkParams]
      exact div_le_self (Nat.cast_nonneg _) (one_le_pow₀ hL1)
    have hk_le_m : (P.k : ℝ) ≤ (P.m : ℝ) := by exact_mod_cast (by omega : P.k ≤ P.m)
    have hm_lt_r : (P.m : ℝ) < ((2 ^ P.J : ℕ) : ℝ) := by exact_mod_cast hm_lt
    linarith only [hTbig_le_k, hk_le_m, hm_lt_r]
  have hF_le_mid : F_max ≤ P.T_mid := by
    have hL5 := log_pow_lt_rpow_of_big (C := 2) (b := 5) (by omega) (by norm_num) hε0 hε1 hL1 hrpow1
    have hsq : (n : ℝ) ^ (1 / 20 : ℝ) ≤ ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 2 := by nlinarith only [hn120_ge1]
    have hTm : P.T_mid = ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 2 := hn110_eq
    linarith only [hF_hi, hL5, hsq, hTm]
  have hL_le_F : ∀ i : Fin P.L, ((2 ^ i.val : ℕ) : ℝ) ≤ F_max := by
    intro i
    have hile : i.val ≤ Nat.log 2 ⌊F_max⌋₊ := by
      have hLdef : P.L = Nat.log 2 ⌊F_max⌋₊ + 1 := rfl
      have := i.isLt; omega
    have hnat : 2 ^ i.val ≤ ⌊F_max⌋₊ :=
      (Nat.pow_le_pow_right (by omega) hile).trans (Nat.pow_log_le_self 2 (by
        have : 1 ≤ ⌊F_max⌋₊ := Nat.floor_pos.mpr hF1; omega))
    exact le_trans (by exact_mod_cast hnat) (Nat.floor_le (by linarith only [hF1]))
  have hsr1 : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) * L_log) :=
    Real.one_le_sqrt.mpr (by nlinarith only [hn_ge1000, hL100])
  have hk1_nat : 1 ≤ P.k := by
    have h1 : (1 : ℝ) ≤ (P.k : ℝ) := by nlinarith only [hk_lo, hsr1, hε0]
    exact_mod_cast h1
  have hV : ValidRegParams P F_max :=
    { hp0 := hp0
      hp1 := hp1
      hη0 := hη0_pos
      hk1 := hk1_nat
      h2k := h2k_le_m
      hL1 := by dsimp only [P, mkParams]; omega
      hF1 := hF1
      hF_lt_L := fun x hx => by
        have hxfl : x ≤ ⌊F_max⌋₊ := Nat.le_floor hx
        exact lt_of_le_of_lt hxfl (Nat.lt_pow_succ_log_self (by omega : 1 < 2) ⌊F_max⌋₊)
      hTlo := by dsimp only [P, mkParams]; positivity
      hTcut := by dsimp only [P, mkParams]; exact pow_le_pow_right₀ hL1 (by omega)
      hF_le_mid := hF_le_mid
      hTbig := by dsimp only [P, mkParams]; positivity
      hTmid_lt := hTmid_lt_big
      hTbig_lt_J := hTbig_lt_J
      hBmid := by dsimp only [P, mkParams]; positivity
      hBcross := by dsimp only [P, mkParams]; positivity
      hm_lt_J := Nat.lt_pow_succ_log_self (by omega : 1 < 2) P.m
      hL_le_F := hL_le_F
      hL_le_Tbig := fun i => (hL_le_F i).trans (hF_le_mid.trans (by linarith only [hTmid_lt_big, hF_le_mid, hF1])) }
  exact ⟨hV, hL100, ⟨hm_lo, hm_hi⟩, ⟨hnm_lo, hnm_hi⟩, ⟨hF1, hF_hi⟩, ⟨hk_lo, hk_hi⟩,
    ⟨hL_bound, hJ_bound⟩, ⟨hρ_lo, hρ_hi⟩⟩

/-- Helper 1B-i: Asymptotic `Qmax`, `errOut`, degree, and `L_log ≤ k` bounds. -/
lemma asymp_errOut_Qmax {ε' : ℝ} (hε0 : 0 < ε') (hε1 : ε' ≤ 1 / 4) :
    ∀ᶠ n : ℕ in Filter.atTop,
      let P := mkParams ε' n
      let L_log := Real.log (n : ℝ)
      let F_max := (1 + P.η₀) * ((n : ℝ) / (P.m : ℝ))
      ((Qmax P : ℝ) ≤ (10 ^ 5 : ℝ) * L_log ^ 4) ∧
      (errOut P F_max ≤ (10 ^ 9 : ℝ) * (P.k : ℝ) ^ 2 / L_log ^ (1 / 2 : ℝ)) ∧
      ((1 + P.η₀) * ((P.m : ℝ) * P.p) ≤ 2 * (P.k : ℝ) / L_log ^ 5) ∧
      (L_log ≤ (P.k : ℝ)) := by
  have hB := asymp_basic_scales hε0 hε1
  have h2 := eventually_log_pow_lt_rpow (a := (1 / 20 : ℝ)) (by norm_num) 20 (10 ^ 12 / ε' ^ 2)
  filter_upwards [hB, h2, Filter.eventually_ge_atTop (1000 : ℕ)] with n hBas hrpow1 hn_ge
  rcases hBas with ⟨hV, hL100, ⟨_, hm_hi⟩, _, ⟨hF1, hF_hi⟩, ⟨hk_lo, _⟩, ⟨hL_bound, hJ_bound⟩, _⟩
  set P := mkParams ε' n
  set L_log := Real.log (n : ℝ)
  set F_max := (1 + P.η₀) * ((n : ℝ) / (P.m : ℝ))
  have hL1 : (1 : ℝ) ≤ L_log := by linarith only [hL100]
  have hLpos : 0 < L_log := by linarith only [hL100]
  have hn_ge1000 : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith only [hn_ge1000]
  have hn120_pos : 0 < (n : ℝ) ^ (1 / 20 : ℝ) := Real.rpow_pos_of_pos hn_pos _
  have hn120_ge1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 20 : ℝ) := Real.one_le_rpow (by linarith only [hn_ge1000]) (by norm_num)
  have hn12_eq : Real.sqrt (n : ℝ) = ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 10 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; congr 1; norm_num
  have hk_pos : (0 : ℝ) < (P.k : ℝ) := by have hk1 : 1 ≤ P.k := hV.hk1; exact Nat.cast_pos.mpr (by omega)
  have hsr_n_le_k : Real.sqrt (n : ℝ) ≤ (P.k : ℝ) := by
    have h1 : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) * L_log) :=
      Real.sqrt_le_sqrt (by nlinarith only [hn_pos, hL100])
    nlinarith only [h1, hk_lo, hε0, Real.sqrt_nonneg ((n : ℝ) * L_log)]
  have hQ_le : (Qmax P : ℝ) ≤ (10 ^ 5 : ℝ) * L_log ^ 4 := by
    have hcl := Nat.ceil_lt_add_one (show 0 ≤ (P.L : ℝ) * (240 * (P.k : ℝ) / P.T_big + 4) by
      have := hV.hTbig; positivity)
    have hdiv : (P.k : ℝ) / P.T_big = L_log ^ 3 := by
      have hTdef : P.T_big = (P.k : ℝ) / L_log ^ 3 := rfl
      rw [hTdef]; field_simp [hk_pos.ne', hLpos.ne']
    have hL_le_L : (P.L : ℝ) ≤ 50 * L_log := by
      have : L_log ^ (1 / 4 : ℝ) ≤ L_log := by
        simpa using Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 / 4 : ℝ) ≤ 1)
      linarith only [hL_bound, this]
    have hL3_ge : (1 : ℝ) ≤ L_log ^ 3 := one_le_pow₀ hL1
    have hL4_ge : (1 : ℝ) ≤ L_log ^ 4 := one_le_pow₀ hL1
    dsimp only [Qmax]; rw [show 240 * (P.k : ℝ) / P.T_big = 240 * ((P.k : ℝ) / P.T_big) by ring, hdiv] at hcl ⊢
    have hprod : (P.L : ℝ) * (240 * L_log ^ 3 + 4) ≤ (50 * L_log) * (244 * L_log ^ 3) :=
      mul_le_mul hL_le_L (by linarith only [hL3_ge]) (by positivity) (by positivity)
    linarith only [hcl, hprod, hL4_ge, show (50 * L_log) * (244 * L_log ^ 3) = 12200 * L_log ^ 4 by ring]
  have hLsq_le : (P.L : ℝ) ^ 2 ≤ 2500 * L_log ^ (1 / 2 : ℝ) := by
    have h1 : (P.L : ℝ) ^ 2 ≤ (50 * L_log ^ (1 / 4 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hL_bound 2
    have h2 : (L_log ^ (1 / 4 : ℝ)) ^ 2 = L_log ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]; congr 1; norm_num
    nlinarith only [h1, h2]
  have hLhalf_pos : 0 < L_log ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hLpos _
  have hLhalf_sq : L_log ^ (1 / 2 : ℝ) * L_log ^ (1 / 2 : ℝ) = L_log := by
    rw [← Real.rpow_add hLpos]; norm_num
  have hLhalf_le : L_log ^ (1 / 2 : ℝ) ≤ L_log := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hnp_eq : (n : ℝ) * P.p = Real.sqrt ((n : ℝ) * L_log) / 2 := mul_sqrt_div_two hn_pos hLpos
  have hmp_le : (P.m : ℝ) * P.p ≤ Real.sqrt ((n : ℝ) * L_log) / L_log ^ 5 := by
    calc (P.m : ℝ) * P.p ≤ (2 * (n : ℝ) / L_log ^ 5) * P.p := mul_le_mul_of_nonneg_right hm_hi hV.hp0
      _ = 2 * ((n : ℝ) * P.p) / L_log ^ 5 := by ring
      _ = Real.sqrt ((n : ℝ) * L_log) / L_log ^ 5 := by rw [hnp_eq]; ring
  have hdeg_le_k : (1 + P.η₀) * ((P.m : ℝ) * P.p) ≤ 2 * (P.k : ℝ) / L_log ^ 5 := by
    have h1 : Real.sqrt ((n : ℝ) * L_log) ≤ (P.k : ℝ) := by
      nlinarith only [hk_lo, hε0, Real.sqrt_nonneg ((n : ℝ) * L_log)]
    have h2 : (P.m : ℝ) * P.p ≤ (P.k : ℝ) / L_log ^ 5 :=
      hmp_le.trans (div_le_div_of_nonneg_right h1 (by positivity))
    have hη_le1 : 1 + P.η₀ ≤ 2 := by dsimp only [P, mkParams]; linarith only [hε1]
    have hmp_nn : 0 ≤ (P.m : ℝ) * P.p := mul_nonneg (Nat.cast_nonneg _) hV.hp0
    have hmul := mul_le_mul hη_le1 h2 hmp_nn (by norm_num)
    linarith only [hmul, show 2 * ((P.k : ℝ) / L_log ^ 5) = 2 * (P.k : ℝ) / L_log ^ 5 by ring]
  have hTmid2_le : P.T_mid ^ 2 * L_log ^ 4 ≤ (P.k : ℝ) := by
    have hT2 : P.T_mid ^ 2 = ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 4 := by
      dsimp only [P, mkParams]; rw [← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le,
        ← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; congr 1; norm_num
    rw [hT2]
    have hL4 := log_pow_lt_rpow_of_big (C := 1) (b := 4) (by omega) (by norm_num) hε0 hε1 hL1 hrpow1
    have hpow5 : ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 5 ≤ ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 10 :=
      pow_le_pow_right₀ hn120_ge1 (by omega)
    have h1 : ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 4 * L_log ^ 4 ≤ Real.sqrt (n : ℝ) := by
      rw [hn12_eq]
      have hmul := mul_le_mul_of_nonneg_left (by linarith only [hL4] : L_log ^ 4 ≤ (n : ℝ) ^ (1 / 20 : ℝ))
        (pow_nonneg hn120_pos.le 4)
      have hrew : ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 4 * (n : ℝ) ^ (1 / 20 : ℝ) = ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 5 := by ring
      linarith only [hmul, hrew, hpow5]
    linarith only [h1, hsr_n_le_k]
  have hL_le_k : L_log ≤ (P.k : ℝ) := by
    have hL1_lt := log_pow_lt_rpow_of_big (C := 1) (b := 1) (by omega) (by norm_num) hε0 hε1 hL1 hrpow1
    have hpow10 : (n : ℝ) ^ (1 / 20 : ℝ) ≤ ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 10 := by
      simpa using pow_le_pow_right₀ hn120_ge1 (by omega : 1 ≤ 10)
    rw [hn12_eq] at hsr_n_le_k
    linarith only [hL1_lt, hpow10, hsr_n_le_k, pow_one L_log]
  -- Bound errOut P F_max ≤ 10^9 * k^2 / L_log^(1/2)
  have herrOut_le : errOut P F_max ≤ (10 ^ 9 : ℝ) * (P.k : ℝ) ^ 2 / L_log ^ (1 / 2 : ℝ) := by
    have hTlo_deg : 2 * P.T_lo * (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) ≤ 4 * (P.k : ℝ) ^ 2 / L_log ^ 3 := by
      have h1 := mul_le_mul_of_nonneg_left hdeg_le_k (show 0 ≤ 2 * P.T_lo * (P.k : ℝ) by have := hV.hTlo; positivity)
      have hsimp : 2 * P.T_lo * (P.k : ℝ) * (2 * (P.k : ℝ) / L_log ^ 5) = 4 * (P.k : ℝ) ^ 2 / L_log ^ 3 := by
        dsimp only [P, mkParams]; field_simp [hLpos.ne']; ring
      linarith only [h1, hsimp]
    have hTcut_deg : 2 * P.T_cut * (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) ≤ 4 * (P.k : ℝ) ^ 2 / L_log := by
      have h1 := mul_le_mul_of_nonneg_left hdeg_le_k (show 0 ≤ 2 * P.T_cut * (P.k : ℝ) by
        have := lt_of_lt_of_le hV.hTlo hV.hTcut; positivity)
      have hsimp : 2 * P.T_cut * (P.k : ℝ) * (2 * (P.k : ℝ) / L_log ^ 5) = 4 * (P.k : ℝ) ^ 2 / L_log := by
        dsimp only [P, mkParams]; field_simp [hLpos.ne']; ring
      linarith only [h1, hsimp]
    have hk_Tmid2 : (P.k : ℝ) * P.T_mid ^ 2 ≤ (P.k : ℝ) ^ 2 / L_log ^ 4 := by
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hTmid2_le hk_pos.le
      linarith only [this, show (P.k : ℝ) * (P.T_mid ^ 2 * L_log ^ 4) = (P.k : ℝ) * P.T_mid ^ 2 * L_log ^ 4 by ring]
    have hTmid2_only : P.T_mid ^ 2 ≤ (P.k : ℝ) ^ 2 / L_log ^ 4 := by
      have hk1 : (1 : ℝ) ≤ (P.k : ℝ) := by have := hV.hk1; exact_mod_cast this
      nlinarith only [hk_Tmid2, hk1, sq_nonneg P.T_mid]
    have hF2_le : F_max ^ 2 ≤ P.T_mid ^ 2 :=
      pow_le_pow_left₀ (by linarith only [hF1]) hV.hF_le_mid 2
    have hTbig_term : (P.k : ℝ) * P.T_big = (P.k : ℝ) ^ 2 / L_log ^ 3 := by dsimp only [P, mkParams]; ring
    have hTbig2_le : P.T_big ^ 2 ≤ (P.k : ℝ) ^ 2 / L_log ^ 3 := by
      dsimp only [P, mkParams]; rw [div_pow]
      refine div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) ?_
      rw [show (L_log ^ 3) ^ 2 = L_log ^ 6 by ring]
      exact pow_le_pow_right₀ hL1 (by omega)
    have hL34 : (P.k : ℝ) ^ 2 / L_log ^ 4 ≤ (P.k : ℝ) ^ 2 / L_log ^ 3 :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_right₀ hL1 (by omega))
    have hL24 : (P.k : ℝ) ^ 2 / L_log ^ 4 ≤ (P.k : ℝ) ^ 2 / L_log ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_right₀ hL1 (by omega))
    have hL12 : (P.k : ℝ) ^ 2 / L_log ^ 2 ≤ (P.k : ℝ) ^ 2 / L_log :=
      div_le_div_of_nonneg_left (sq_nonneg _) hLpos (by simpa using pow_le_pow_right₀ hL1 (by omega : 1 ≤ 2))
    have hL13 : (P.k : ℝ) ^ 2 / L_log ^ 3 ≤ (P.k : ℝ) ^ 2 / L_log :=
      div_le_div_of_nonneg_left (sq_nonneg _) hLpos (by simpa using pow_le_pow_right₀ hL1 (by omega : 1 ≤ 3))
    have hL14 : (P.k : ℝ) ^ 2 / L_log ^ 4 ≤ (P.k : ℝ) ^ 2 / L_log :=
      div_le_div_of_nonneg_left (sq_nonneg _) hLpos (by simpa using pow_le_pow_right₀ hL1 (by omega : 1 ≤ 4))
    have hJ_mid : (P.J : ℝ) * (4 * (P.k : ℝ) ^ 2 / P.B_mid + 4 * P.T_mid ^ 2 +
        480 * (P.k : ℝ) * P.T_big + 16 * P.T_big ^ 2) ≤ 2000 * (P.k : ℝ) ^ 2 / L_log ^ 2 := by
      have hB : P.B_mid = L_log ^ 3 := rfl
      have hsum : 4 * (P.k : ℝ) ^ 2 / P.B_mid + 4 * P.T_mid ^ 2 +
          480 * (P.k : ℝ) * P.T_big + 16 * P.T_big ^ 2 ≤ 504 * (P.k : ℝ) ^ 2 / L_log ^ 3 := by
        rw [hB, show 480 * (P.k : ℝ) * P.T_big = 480 * ((P.k : ℝ) * P.T_big) by ring, hTbig_term]
        simp only [mul_div_assoc]
        linarith only [hTmid2_only, hTbig2_le, hL34]
      have hBpos := hV.hBmid; have hTbpos := hV.hTbig
      calc (P.J : ℝ) * _ ≤ (3 * L_log) * (504 * (P.k : ℝ) ^ 2 / L_log ^ 3) :=
            mul_le_mul hJ_bound hsum (by positivity) (by positivity)
        _ = 1512 * (P.k : ℝ) ^ 2 / L_log ^ 2 := by field_simp [hLpos.ne']; ring
        _ ≤ 2000 * (P.k : ℝ) ^ 2 / L_log ^ 2 := div_le_div_of_nonneg_right (by nlinarith only [sq_nonneg (P.k : ℝ)]) (by positivity)
    have hJ_o12 : (P.J : ℝ) * (2 * (P.k : ℝ) ^ 2 * F_max / (P.T_cut * P.B_mid) + 2 * F_max ^ 2) ≤
        20 * (P.k : ℝ) ^ 2 / L_log := by
      have h1 : 2 * (P.k : ℝ) ^ 2 * F_max / (P.T_cut * P.B_mid) ≤ 4 * (P.k : ℝ) ^ 2 / L_log ^ 2 := by
        have hTB : P.T_cut * P.B_mid = L_log ^ 4 * L_log ^ 3 := rfl
        rw [hTB]
        calc 2 * (P.k : ℝ) ^ 2 * F_max / (L_log ^ 4 * L_log ^ 3)
            ≤ 2 * (P.k : ℝ) ^ 2 * (2 * L_log ^ 5) / (L_log ^ 4 * L_log ^ 3) :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hF_hi (by positivity)) (by positivity)
          _ = 4 * (P.k : ℝ) ^ 2 / L_log ^ 2 := by field_simp [hLpos.ne']; ring
      have h2 : 2 * F_max ^ 2 ≤ 2 * (P.k : ℝ) ^ 2 / L_log ^ 2 := by
        rw [mul_div_assoc]; linarith only [hF2_le, hTmid2_only, hL24]
      have hTcpos : 0 < P.T_cut := lt_of_lt_of_le hV.hTlo hV.hTcut; have hBpos := hV.hBmid
      calc (P.J : ℝ) * _ ≤ (3 * L_log) * (6 * (P.k : ℝ) ^ 2 / L_log ^ 2) :=
            mul_le_mul hJ_bound (by simp only [mul_div_assoc] at h1 h2 ⊢; linarith only [h1, h2]) (by positivity) (by positivity)
        _ = 18 * (P.k : ℝ) ^ 2 / L_log := by field_simp [hLpos.ne']; ring
        _ ≤ 20 * (P.k : ℝ) ^ 2 / L_log := div_le_div_of_nonneg_right (by nlinarith only [sq_nonneg (P.k : ℝ)]) hLpos.le
    have hkF2 : (P.k : ℝ) * F_max ^ 2 ≤ (P.k : ℝ) ^ 2 / L_log ^ 4 :=
      (mul_le_mul_of_nonneg_left hF2_le hk_pos.le).trans hk_Tmid2
    have hinner_le :
        4 * (2 * P.T_lo * (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) +
          4 * (P.k : ℝ) * P.T_mid ^ 2 +
          (P.J : ℝ) * (4 * (P.k : ℝ) ^ 2 / P.B_mid + 4 * P.T_mid ^ 2 +
            480 * (P.k : ℝ) * P.T_big + 16 * P.T_big ^ 2)) +
        2 * (2 * P.T_cut * (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) +
          (P.k : ℝ) * F_max ^ 2 +
          (P.J : ℝ) * (2 * (P.k : ℝ) ^ 2 * F_max / (P.T_cut * P.B_mid) + 2 * F_max ^ 2)) +
        (2 * (P.k : ℝ) * F_max ^ 2 + (P.k : ℝ) ^ 2 / P.B_cross + F_max ^ 2) ≤
        10000 * (P.k : ℝ) ^ 2 / L_log := by
      have hBc : P.B_cross = L_log ^ 3 := rfl
      rw [hBc]
      simp only [mul_div_assoc] at hTlo_deg hJ_mid hTcut_deg hJ_o12 ⊢
      linarith only [hTlo_deg, hk_Tmid2, hJ_mid, hTcut_deg, hkF2, hJ_o12, hF2_le, hTmid2_only, hL12, hL13, hL14,
        show 0 ≤ (P.k : ℝ) ^ 2 / L_log by positivity]
    have hinner_nn : 0 ≤
        4 * (2 * P.T_lo * (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) +
          4 * (P.k : ℝ) * P.T_mid ^ 2 +
          (P.J : ℝ) * (4 * (P.k : ℝ) ^ 2 / P.B_mid + 4 * P.T_mid ^ 2 +
            480 * (P.k : ℝ) * P.T_big + 16 * P.T_big ^ 2)) +
        2 * (2 * P.T_cut * (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) +
          (P.k : ℝ) * F_max ^ 2 +
          (P.J : ℝ) * (2 * (P.k : ℝ) ^ 2 * F_max / (P.T_cut * P.B_mid) + 2 * F_max ^ 2)) +
        (2 * (P.k : ℝ) * F_max ^ 2 + (P.k : ℝ) ^ 2 / P.B_cross + F_max ^ 2) := by
      have hdeg_nn : 0 ≤ (1 + P.η₀) * ((P.m : ℝ) * P.p) :=
        mul_nonneg (by linarith only [hV.hη0]) (mul_nonneg (Nat.cast_nonneg _) hV.hp0)
      have hTc := lt_of_lt_of_le hV.hTlo hV.hTcut; have hBm := hV.hBmid; have hBc := hV.hBcross
      have hTl := hV.hTlo; have hTb := hV.hTbig
      positivity
    dsimp only [errOut]
    calc 4 * (P.L : ℝ) ^ 2 * _
        ≤ 4 * (2500 * L_log ^ (1 / 2 : ℝ)) * (10000 * (P.k : ℝ) ^ 2 / L_log) :=
          mul_le_mul (by linarith only [hLsq_le]) hinner_le hinner_nn (by positivity)
      _ = (10 ^ 8 : ℝ) * (P.k : ℝ) ^ 2 / L_log ^ (1 / 2 : ℝ) := by
          field_simp [hLpos.ne', hLhalf_pos.ne']
          rw [sq, hLhalf_sq]; ring
      _ ≤ (10 ^ 9 : ℝ) * (P.k : ℝ) ^ 2 / L_log ^ (1 / 2 : ℝ) :=
          div_le_div_of_nonneg_right (by nlinarith only [sq_nonneg (P.k : ℝ)]) hLhalf_pos.le
  exact ⟨hQ_le, herrOut_le, hdeg_le_k, hL_le_k⟩

/-- Helper 1B: Full asymptotic parameter validity + error bounds (`errOut`, `errOpen`, `MtriBound`, `Qmax`). -/
lemma asymp_valid_and_scales {ε' : ℝ} (hε0 : 0 < ε') (hε1 : ε' ≤ 1 / 4) :
    ∀ᶠ n : ℕ in Filter.atTop,
      let P := mkParams ε' n
      let L_log := Real.log (n : ℝ)
      let F_max := (1 + P.η₀) * ((n : ℝ) / (P.m : ℝ))
      let D := F_max * ((1 + P.η₀) * ((P.m : ℝ) * P.p))
      ValidRegParams P F_max ∧
      (100 < L_log) ∧
      ((n : ℝ) / L_log ^ 5 ≤ (P.m : ℝ) ∧ (P.m : ℝ) ≤ 2 * (n : ℝ) / L_log ^ 5) ∧
      (L_log ^ 5 / 2 ≤ (n : ℝ) / (P.m : ℝ) ∧ (n : ℝ) / (P.m : ℝ) ≤ L_log ^ 5) ∧
      (1 ≤ F_max ∧ F_max ≤ 2 * L_log ^ 5) ∧
      ((1 + ε') * Real.sqrt ((n : ℝ) * L_log) ≤ (P.k : ℝ) ∧
        (P.k : ℝ) ≤ (1 + 2 * ε') * Real.sqrt ((n : ℝ) * L_log)) ∧
      ((P.L : ℝ) ≤ 50 * L_log ^ (1 / 4 : ℝ) ∧ (P.J : ℝ) ≤ 3 * L_log) ∧
      (1 / (2 * (1 + ε')) ≤ D / (P.k : ℝ) ∧ D / (P.k : ℝ) ≤ 1 / 2 - ε' / 4) ∧
      (errOut P F_max ≤ (10 ^ 9 : ℝ) * (P.k : ℝ) ^ 2 / L_log ^ (1 / 2 : ℝ)) ∧
      (errOpen P F_max ≤ (10 ^ 10 : ℝ) * (P.k : ℝ) ^ 2 / L_log ^ (1 / 2 : ℝ)) ∧
      ((MtriBound P F_max : ℝ) ≤ (10 ^ 9 : ℝ) * (P.k : ℝ) ^ 2 / L_log ^ (1 / 2 : ℝ)) ∧
      ((Qmax P : ℝ) ≤ (10 ^ 5 : ℝ) * L_log ^ 4) := by
  have hB := asymp_basic_scales hε0 hε1
  have hE := asymp_errOut_Qmax hε0 hε1
  have h2 := eventually_log_pow_lt_rpow (a := (1 / 20 : ℝ)) (by norm_num) 20 (10 ^ 12 / ε' ^ 2)
  filter_upwards [hB, hE, h2, Filter.eventually_ge_atTop (1000 : ℕ)] with n hBas hErr hrpow1 hn_ge
  rcases hBas with ⟨hV, hL100, ⟨hm_lo, hm_hi⟩, ⟨hnm_lo, hnm_hi⟩, ⟨hF1, hF_hi⟩, ⟨hk_lo, hk_hi⟩,
    ⟨hL_bound, hJ_bound⟩, ⟨hρ_lo, hρ_hi⟩⟩
  rcases hErr with ⟨hQ_le, herrOut_le, hdeg_le_k, hL_le_k⟩
  set P := mkParams ε' n
  set L_log := Real.log (n : ℝ)
  set F_max := (1 + P.η₀) * ((n : ℝ) / (P.m : ℝ))
  set D := F_max * ((1 + P.η₀) * ((P.m : ℝ) * P.p))
  have hL1 : (1 : ℝ) ≤ L_log := by linarith only [hL100]
  have hLpos : 0 < L_log := by linarith only [hL100]
  have hn_ge1000 : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith only [hn_ge1000]
  have hn120_ge1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 20 : ℝ) := Real.one_le_rpow (by linarith only [hn_ge1000]) (by norm_num)
  have hn12_eq : Real.sqrt (n : ℝ) = ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 10 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; congr 1; norm_num
  have hk_pos : (0 : ℝ) < (P.k : ℝ) := by have hk1 : 1 ≤ P.k := hV.hk1; exact Nat.cast_pos.mpr (by omega)
  have hsr_n_le_k : Real.sqrt (n : ℝ) ≤ (P.k : ℝ) := by
    have h1 : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) * L_log) :=
      Real.sqrt_le_sqrt (by nlinarith only [hn_pos, hL100])
    nlinarith only [h1, hk_lo, hε0, Real.sqrt_nonneg ((n : ℝ) * L_log)]
  have hLhalf_pos : 0 < L_log ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hLpos _
  have hLhalf_le : L_log ^ (1 / 2 : ℝ) ≤ L_log := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 / 2 : ℝ) ≤ 1)
  -- Bound Ez and (1 + F_max) * Qmax
  have hEz_le : F_max * (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ) ≤ (P.k : ℝ) / L_log ^ 4 := by
    have hC_le : (P.C_codeg : ℝ) ≤ 2 * L_log := by
      have hcl := Nat.ceil_lt_add_one hLpos.le
      have hCeq : (P.C_codeg : ℝ) = (⌈L_log⌉₊ : ℝ) := rfl
      linarith only [hcl, hCeq, hL100]
    have hprod_L : F_max * (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ) ≤ 4 * (10 ^ 10 : ℝ) * L_log ^ 14 := by
      have hQ2 : (Qmax P : ℝ) ^ 2 ≤ (10 ^ 5 * L_log ^ 4) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hQ_le 2
      have h1 := mul_le_mul hF_hi hQ2 (sq_nonneg _) (by positivity)
      have h2 := mul_le_mul h1 hC_le (Nat.cast_nonneg _) (by positivity)
      linarith only [h2, show (2 * L_log ^ 5) * (10 ^ 5 * L_log ^ 4) ^ 2 * (2 * L_log) = 4 * (10 ^ 10 : ℝ) * L_log ^ 14 by ring]
    rw [le_div_iff₀ (by positivity)]
    have hL18 := log_pow_lt_rpow_of_big (C := 4 * 10 ^ 10) (b := 18) (by omega) (by norm_num) hε0 hε1 hL1 hrpow1
    have hpow10 : (n : ℝ) ^ (1 / 20 : ℝ) ≤ ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 10 := by
      simpa using pow_le_pow_right₀ hn120_ge1 (by omega : 1 ≤ 10)
    have hmul := mul_le_mul_of_nonneg_right hprod_L (show (0 : ℝ) ≤ L_log ^ 4 by positivity)
    rw [hn12_eq] at hsr_n_le_k
    linarith only [hmul, hL18, hpow10, hsr_n_le_k,
      show (4 * (10 ^ 10 : ℝ) * L_log ^ 14) * L_log ^ 4 = 4 * (10 ^ 10 : ℝ) * L_log ^ 18 by ring]
  have hQ_F_le : (1 + F_max) * (Qmax P : ℝ) ≤ (P.k : ℝ) / L_log ^ 4 := by
    have h1 : (1 + F_max) * (Qmax P : ℝ) ≤ 3 * (10 ^ 5 : ℝ) * L_log ^ 9 := by
      have hF3 : 1 + F_max ≤ 3 * L_log ^ 5 := by linarith only [hF_hi, one_le_pow₀ hL1 (n := 5)]
      have hmul := mul_le_mul hF3 hQ_le (Nat.cast_nonneg _) (by positivity)
      linarith only [hmul, show (3 * L_log ^ 5) * (10 ^ 5 * L_log ^ 4) = 3 * (10 ^ 5 : ℝ) * L_log ^ 9 by ring]
    rw [le_div_iff₀ (by positivity)]
    have hL13 := log_pow_lt_rpow_of_big (C := 3 * 10 ^ 5) (b := 13) (by omega) (by norm_num) hε0 hε1 hL1 hrpow1
    have hpow10 : (n : ℝ) ^ (1 / 20 : ℝ) ≤ ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 10 := by
      simpa using pow_le_pow_right₀ hn120_ge1 (by omega : 1 ≤ 10)
    have hmul := mul_le_mul_of_nonneg_right h1 (show (0 : ℝ) ≤ L_log ^ 4 by positivity)
    rw [hn12_eq] at hsr_n_le_k
    linarith only [hmul, hL13, hpow10, hsr_n_le_k,
      show (3 * (10 ^ 5 : ℝ) * L_log ^ 9) * L_log ^ 4 = 3 * (10 ^ 5 : ℝ) * L_log ^ 13 by ring]
  have hL4_half : (P.k : ℝ) ^ 2 / L_log ^ 4 ≤ (P.k : ℝ) ^ 2 / L_log ^ (1 / 2 : ℝ) := by
    refine div_le_div_of_nonneg_left (sq_nonneg _) hLhalf_pos ?_
    have : L_log ≤ L_log ^ 4 := by simpa using pow_le_pow_right₀ hL1 (by omega : 1 ≤ 4)
    linarith only [hLhalf_le, this]
  have hL5_half : (P.k : ℝ) ^ 2 / L_log ^ 5 ≤ (P.k : ℝ) ^ 2 / L_log ^ (1 / 2 : ℝ) := by
    refine div_le_div_of_nonneg_left (sq_nonneg _) hLhalf_pos ?_
    have : L_log ≤ L_log ^ 5 := by simpa using pow_le_pow_right₀ hL1 (by omega : 1 ≤ 5)
    linarith only [hLhalf_le, this]
  have hEz_le_k : F_max * (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ) ≤ (P.k : ℝ) :=
    hEz_le.trans (div_le_self hk_pos.le (one_le_pow₀ hL1))
  have herrOpen_le : errOpen P F_max ≤ (10 ^ 10 : ℝ) * (P.k : ℝ) ^ 2 / L_log ^ (1 / 2 : ℝ) := by
    have h1 : (P.k : ℝ) / 2 ≤ (P.k : ℝ) ^ 2 / L_log ^ (1 / 2 : ℝ) := by
      rw [le_div_iff₀ hLhalf_pos]; nlinarith only [hLhalf_le, hL_le_k, hk_pos]
    have h2 : (1 + F_max) * (Qmax P : ℝ) * (P.k : ℝ) ≤ (P.k : ℝ) ^ 2 / L_log ^ 4 := by
      have := mul_le_mul_of_nonneg_right hQ_F_le hk_pos.le
      linarith only [this, show (P.k : ℝ) / L_log ^ 4 * (P.k : ℝ) = (P.k : ℝ) ^ 2 / L_log ^ 4 by ring]
    have h3 : F_max * (P.k : ℝ) ≤ (P.k : ℝ) ^ 2 / L_log ^ 4 := by
      have hQ1 : (1 : ℝ) ≤ (Qmax P : ℝ) := by
        have hL1' : (0 : ℝ) < (P.L : ℝ) := Nat.cast_pos.mpr (by have := hV.hL1; omega)
        have hTb := hV.hTbig
        have hpos : 0 < Qmax P := by dsimp only [Qmax]; exact Nat.ceil_pos.mpr (by positivity)
        exact_mod_cast (Nat.succ_le_of_lt hpos : 1 ≤ Qmax P)
      have h3a : F_max ≤ (1 + F_max) * (Qmax P : ℝ) := by nlinarith only [hQ1, hF1]
      have h3b := mul_le_mul_of_nonneg_right h3a hk_pos.le
      linarith only [h3b, h2]
    have h4 : 2 * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) *
        ((P.k : ℝ) + F_max * (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ)) ≤ 8 * (P.k : ℝ) ^ 2 / L_log ^ 5 := by
      have hmul := mul_le_mul hdeg_le_k (show (P.k : ℝ) + F_max * (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ) ≤ 2 * (P.k : ℝ) by linarith only [hEz_le_k])
        (by positivity) (by positivity)
      linarith only [hmul, show 2 * ((2 * (P.k : ℝ) / L_log ^ 5) * (2 * (P.k : ℝ))) = 8 * (P.k : ℝ) ^ 2 / L_log ^ 5 by ring]
    have hD_le_k : F_max * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) ≤ (P.k : ℝ) := by
      have hD : D ≤ (1 / 2 - ε' / 4) * (P.k : ℝ) := (div_le_iff₀ hk_pos).mp hρ_hi
      nlinarith only [hD, hε0, hk_pos]
    have h5 : (2 * (P.k : ℝ) + F_max * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) +
        F_max * (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ)) *
        (F_max * (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ)) ≤ 4 * (P.k : ℝ) ^ 2 / L_log ^ 4 := by
      have hsum : 2 * (P.k : ℝ) + F_max * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) +
          F_max * (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ) ≤ 4 * (P.k : ℝ) := by linarith only [hD_le_k, hEz_le_k]
      have hmul := mul_le_mul hsum hEz_le (by positivity) (by positivity)
      linarith only [hmul, show 4 * (P.k : ℝ) * ((P.k : ℝ) / L_log ^ 4) = 4 * (P.k : ℝ) ^ 2 / L_log ^ 4 by ring]
    dsimp only [errOpen]
    simp only [mul_div_assoc] at herrOut_le h4 h5 ⊢
    linarith only [h1, h2, h3, herrOut_le, h4, h5, hL4_half, hL5_half,
      show 0 ≤ (P.k : ℝ) ^ 2 / L_log ^ (1 / 2 : ℝ) by positivity]
  have hMtri_le : (MtriBound P F_max : ℝ) ≤ (10 ^ 9 : ℝ) * (P.k : ℝ) ^ 2 / L_log ^ (1 / 2 : ℝ) := by
    have hdeg_nn : 0 ≤ (1 + P.η₀) * ((P.m : ℝ) * P.p) :=
      mul_nonneg (by linarith only [hV.hη0]) (mul_nonneg (Nat.cast_nonneg _) hV.hp0)
    have heo_nn : 0 ≤ errOut P F_max := errOut_nonneg P hV
    have hTb := hV.hTbig
    have hcl := Nat.ceil_lt_add_one (show 0 ≤ ((P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) + errOut P F_max +
      ((1 + P.η₀) * ((P.m : ℝ) * P.p)) *
        ((P.k : ℝ) + ((P.L : ℝ) * (240 * (P.k : ℝ) / P.T_big + 4)) ^ 2 * (P.C_codeg : ℝ))) / 2 by positivity)
    have h1 : (P.k : ℝ) * ((1 + P.η₀) * ((P.m : ℝ) * P.p)) ≤ 2 * (P.k : ℝ) ^ 2 / L_log ^ 5 := by
      have := mul_le_mul_of_nonneg_left hdeg_le_k hk_pos.le
      linarith only [this, show (P.k : ℝ) * (2 * (P.k : ℝ) / L_log ^ 5) = 2 * (P.k : ℝ) ^ 2 / L_log ^ 5 by ring]
    have hQ_le_ce : (P.L : ℝ) * (240 * (P.k : ℝ) / P.T_big + 4) ≤ (Qmax P : ℝ) := Nat.le_ceil _
    have h2 : ((P.L : ℝ) * (240 * (P.k : ℝ) / P.T_big + 4)) ^ 2 * (P.C_codeg : ℝ) ≤ (P.k : ℝ) := by
      have hsq : ((P.L : ℝ) * (240 * (P.k : ℝ) / P.T_big + 4)) ^ 2 ≤ (Qmax P : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hQ_le_ce 2
      have hle_Ez : (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ) ≤ F_max * (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ) := by
        have hnn : 0 ≤ (Qmax P : ℝ) ^ 2 * (P.C_codeg : ℝ) := by positivity
        nlinarith only [hF1, hnn]
      have hmul := mul_le_mul_of_nonneg_right hsq (Nat.cast_nonneg (α := ℝ) P.C_codeg)
      linarith only [hmul, hle_Ez, hEz_le_k]
    have h3 : ((1 + P.η₀) * ((P.m : ℝ) * P.p)) *
        ((P.k : ℝ) + ((P.L : ℝ) * (240 * (P.k : ℝ) / P.T_big + 4)) ^ 2 * (P.C_codeg : ℝ)) ≤
        4 * (P.k : ℝ) ^ 2 / L_log ^ 5 := by
      have hmul := mul_le_mul hdeg_le_k
        (show (P.k : ℝ) + ((P.L : ℝ) * (240 * (P.k : ℝ) / P.T_big + 4)) ^ 2 * (P.C_codeg : ℝ) ≤ 2 * (P.k : ℝ) by linarith only [h2])
        (by positivity) (by positivity)
      linarith only [hmul, show (2 * (P.k : ℝ) / L_log ^ 5) * (2 * (P.k : ℝ)) = 4 * (P.k : ℝ) ^ 2 / L_log ^ 5 by ring]
    have h1le : (1 : ℝ) ≤ (P.k : ℝ) ^ 2 / L_log ^ (1 / 2 : ℝ) := by
      rw [one_le_div hLhalf_pos]
      have hk1 : (1 : ℝ) ≤ (P.k : ℝ) := by have := hV.hk1; exact_mod_cast this
      nlinarith only [hLhalf_le, hL_le_k, hk1]
    dsimp only [MtriBound]
    simp only [mul_div_assoc] at hcl h1 herrOut_le h3 ⊢
    linarith only [hcl, h1, herrOut_le, h3, hL5_half, h1le,
      show 0 ≤ (P.k : ℝ) ^ 2 / L_log ^ (1 / 2 : ℝ) by positivity]
  exact ⟨hV, hL100, ⟨hm_lo, hm_hi⟩, ⟨hnm_lo, hnm_hi⟩, ⟨hF1, hF_hi⟩, ⟨hk_lo, hk_hi⟩,
    ⟨hL_bound, hJ_bound⟩, ⟨hρ_lo, hρ_hi⟩, herrOut_le, herrOpen_le, hMtri_le, hQ_le⟩

/-- Helper 2A: Asymptotic bounds for `¬ GoodMaxDeg` and `¬ GoodMaxCodeg` (each `≤ 1 / 50`). -/
lemma asymp_good_deg_codeg {ε' : ℝ} (hε0 : 0 < ε') (hε1 : ε' ≤ 1 / 4) :
    ∀ᶠ n : ℕ in Filter.atTop,
      bernProb (mkParams ε' n).p (fun ω => ¬ GoodMaxDeg (mkParams ε' n) ω) ≤ 1 / 50 ∧
      bernProb (mkParams ε' n).p (fun ω => ¬ GoodMaxCodeg (mkParams ε' n) ω) ≤ 1 / 50 := by
  have hS := asymp_basic_scales hε0 hε1
  have hlog := eventually_lt_log (max 1000 (1000 / ε' ^ 2))
  have hrp1 := eventually_log_pow_lt_rpow (a := (1 / 20 : ℝ)) (by norm_num) 20 (10 ^ 12 / ε' ^ 2)
  filter_upwards [hS, hlog, hrp1, Filter.eventually_ge_atTop (1000 : ℕ)] with n hSc hlog_big hrp1 hn_ge
  rcases hSc with ⟨hV, _, ⟨hm_lo, hm_hi⟩, _, _, _, _, _⟩
  set P := mkParams ε' n
  set L_log := Real.log (n : ℝ)
  have hL1000 : 1000 < L_log := lt_of_le_of_lt (le_max_left _ _) hlog_big
  have hL1 : (1 : ℝ) ≤ L_log := by linarith only [hL1000]
  have hLpos : 0 < L_log := by linarith only [hL1000]
  have hn_ge1000 : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith only [hn_ge1000]
  have hn_exp : (n : ℝ) = Real.exp L_log := (Real.exp_log hn_pos).symm
  have he_lt3 : Real.exp 1 < 3 := by linarith only [Real.exp_one_lt_d9]
  have hη1 : P.η₀ ≤ 1 / 2 := by dsimp only [P, mkParams]; linarith only [hε1]
  have hn120_ge1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 20 : ℝ) := Real.one_le_rpow (by linarith only [hn_ge1000]) (by norm_num)
  have hn120_le_n : (n : ℝ) ^ (1 / 20 : ℝ) ≤ (n : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith only [hn_ge1000] : (1 : ℝ) ≤ (n : ℝ)) (by norm_num : (1 / 20 : ℝ) ≤ 1)
  have hn12_eq : Real.sqrt (n : ℝ) = ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 10 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; congr 1; norm_num
  have hm_le_n : (P.m : ℝ) ≤ (n : ℝ) := by
    have hL5 : (2 : ℝ) ≤ L_log ^ 5 := by
      have : (1000 : ℝ) ^ 5 ≤ L_log ^ 5 := pow_le_pow_left₀ (by norm_num) hL1000.le 5
      linarith only [this]
    have hdiv : 2 / L_log ^ 5 ≤ 1 := (div_le_one (by positivity)).mpr hL5
    calc (P.m : ℝ) ≤ 2 * (n : ℝ) / L_log ^ 5 := hm_hi
      _ = (2 / L_log ^ 5) * (n : ℝ) := by ring
      _ ≤ 1 * (n : ℝ) := mul_le_mul_of_nonneg_right hdiv hn_pos.le
      _ = (n : ℝ) := one_mul _
  have h1n_le : 1 / (n : ℝ) ≤ 1 / 50 := by
    rw [div_le_div_iff₀ hn_pos (by norm_num : (0 : ℝ) < 50)]; linarith only [hn_ge1000]
  constructor
  · refine (bernProb_not_goodMaxDeg_le P hV.hp0 hV.hp1 hV.hη0 hη1).trans ?_
    have hm_ge2 : (2 : ℝ) ≤ (P.m : ℝ) := by
      have hL5 := log_pow_lt_rpow_of_big (C := 2) (b := 5) (by omega) (by norm_num) hε0 hε1 hL1 hrp1
      have h1 : (2 : ℝ) ≤ (n : ℝ) / L_log ^ 5 := (le_div_iff₀ (by positivity)).mpr (by linarith only [hL5, hn120_le_n])
      linarith only [hm_lo, h1]
    have hm1_ge : (n : ℝ) / (2 * L_log ^ 5) ≤ ((P.m - 1 : ℕ) : ℝ) := by
      have hm1_nat : 1 ≤ P.m := by exact_mod_cast (by linarith only [hm_ge2] : (1 : ℝ) ≤ (P.m : ℝ))
      rw [Nat.cast_sub hm1_nat, Nat.cast_one]
      linarith only [hm_ge2, hm_lo, show (n : ℝ) / (2 * L_log ^ 5) = ((n : ℝ) / L_log ^ 5) / 2 by ring]
    have hnp_eq : (n : ℝ) * P.p = Real.sqrt ((n : ℝ) * L_log) / 2 := mul_sqrt_div_two hn_pos hLpos
    have hm1p_ge : Real.sqrt (n : ℝ) / (4 * L_log ^ 5) ≤ ((P.m - 1 : ℕ) : ℝ) * P.p := by
      have h1 := mul_le_mul_of_nonneg_right hm1_ge hV.hp0
      have h2 : ((n : ℝ) / (2 * L_log ^ 5)) * P.p = Real.sqrt ((n : ℝ) * L_log) / (4 * L_log ^ 5) := by
        rw [show ((n : ℝ) / (2 * L_log ^ 5)) * P.p = ((n : ℝ) * P.p) / (2 * L_log ^ 5) by ring, hnp_eq]; ring
      have h3 : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) * L_log) := Real.sqrt_le_sqrt (by nlinarith only [hn_pos, hL1000])
      have h4 := div_le_div_of_nonneg_right h3 (show (0 : ℝ) ≤ 4 * L_log ^ 5 by positivity)
      linarith only [h1, h2, h4]
    have hexp_ge : 2 * L_log ≤ (P.η₀ ^ 2 / 3) * (((P.m - 1 : ℕ) : ℝ) * P.p) := by
      have hηsq : P.η₀ ^ 2 / 3 = ε' ^ 2 / 768 := by dsimp only [P, mkParams]; ring
      rw [hηsq]
      have hpow10 : (n : ℝ) ^ (1 / 20 : ℝ) ≤ ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 10 := by
        simpa using pow_le_pow_right₀ hn120_ge1 (by omega : 1 ≤ 10)
      have hsr_ge : (10 ^ 12 / ε' ^ 2) * L_log ^ 20 ≤ Real.sqrt (n : ℝ) := by
        rw [hn12_eq]; linarith only [hrp1, hpow10]
      have hmul := mul_le_mul_of_nonneg_left
        ((div_le_div_of_nonneg_right hsr_ge (by positivity)).trans hm1p_ge) (show (0 : ℝ) ≤ ε' ^ 2 / 768 by positivity)
      have hsimp : (ε' ^ 2 / 768) * (((10 ^ 12 / ε' ^ 2) * L_log ^ 20) / (4 * L_log ^ 5)) =
          (10 ^ 12 / 3072 : ℝ) * L_log ^ 15 := by field_simp [hε0.ne', hLpos.ne']; ring
      have hL15 : L_log ≤ L_log ^ 15 := by simpa using pow_le_pow_right₀ hL1 (by omega : 1 ≤ 15)
      linarith only [hmul, hsimp, hL15, hLpos]
    calc (P.m : ℝ) * Real.exp (-(P.η₀ ^ 2 / 3) * (((P.m - 1 : ℕ) : ℝ) * P.p))
        ≤ (n : ℝ) * Real.exp (-(2 * L_log)) :=
          mul_le_mul hm_le_n (Real.exp_le_exp.mpr (by linarith only [hexp_ge])) (Real.exp_pos _).le hn_pos.le
      _ = 1 / (n : ℝ) := by
          rw [show -(2 * L_log) = -L_log + -L_log by ring, Real.exp_add, Real.exp_neg, ← hn_exp]
          field_simp [hn_pos.ne']
      _ ≤ 1 / 50 := h1n_le
  · have hC1 : 1 ≤ P.C_codeg := Nat.ceil_pos.mpr hLpos
    refine (bernProb_not_goodMaxCodeg_le P hV.hp0 hV.hp1 hC1).trans ?_
    have hC_ge : L_log ≤ (P.C_codeg : ℝ) := Nat.le_ceil _
    have hp2 : P.p ^ 2 = L_log / (4 * (n : ℝ)) := by
      dsimp only [P, mkParams]; rw [div_pow, Real.sq_sqrt (by positivity)]; ring
    have hmp2 : (P.m : ℝ) * P.p ^ 2 ≤ 1 / (2 * L_log ^ 4) := by
      rw [hp2]
      calc (P.m : ℝ) * (L_log / (4 * (n : ℝ)))
          ≤ (2 * (n : ℝ) / L_log ^ 5) * (L_log / (4 * (n : ℝ))) :=
            mul_le_mul_of_nonneg_right hm_hi (by positivity)
        _ = 1 / (2 * L_log ^ 4) := by field_simp [hn_pos.ne', hLpos.ne']; ring
    have hbase : Real.exp 1 * (P.m : ℝ) * P.p ^ 2 / (P.C_codeg : ℝ) ≤ Real.exp (-3) := by
      have h1 : Real.exp 1 * (P.m : ℝ) * P.p ^ 2 / (P.C_codeg : ℝ) ≤ 3 / (2 * L_log ^ 5) := by
        have hnum := mul_le_mul he_lt3.le hmp2 (by positivity) (by norm_num)
        calc Real.exp 1 * (P.m : ℝ) * P.p ^ 2 / (P.C_codeg : ℝ)
            = (Real.exp 1 * ((P.m : ℝ) * P.p ^ 2)) / (P.C_codeg : ℝ) := by ring
          _ ≤ (3 * (1 / (2 * L_log ^ 4))) / L_log := div_le_div₀ (by positivity) hnum hLpos hC_ge
          _ = 3 / (2 * L_log ^ 5) := by field_simp [hLpos.ne']
      have he3 : Real.exp 3 < 27 := by
        have hsq : Real.exp 1 * Real.exp 1 < 9 := by nlinarith only [he_lt3, Real.exp_pos 1]
        have h3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add, ← Real.exp_add]; norm_num
        nlinarith only [h3, hsq, he_lt3, Real.exp_pos 1]
      have h2 : 3 / (2 * L_log ^ 5) ≤ Real.exp (-3) := by
        rw [Real.exp_neg, le_inv_comm₀ (by positivity) (Real.exp_pos 3), inv_div]
        have : (1000 : ℝ) ^ 5 ≤ L_log ^ 5 := pow_le_pow_left₀ (by norm_num) hL1000.le 5
        linarith only [he3, this]
      exact h1.trans h2
    have hpow : (Real.exp 1 * (P.m : ℝ) * P.p ^ 2 / (P.C_codeg : ℝ)) ^ P.C_codeg ≤ Real.exp (-(3 * L_log)) := by
      calc _ ≤ (Real.exp (-3)) ^ P.C_codeg := pow_le_pow_left₀ (by positivity) hbase _
        _ = Real.exp ((P.C_codeg : ℝ) * (-3)) := (Real.exp_nat_mul (-3) P.C_codeg).symm
        _ ≤ Real.exp (-(3 * L_log)) := Real.exp_le_exp.mpr (by linarith only [hC_ge])
    calc (P.m : ℝ) ^ 2 * (Real.exp 1 * (P.m : ℝ) * P.p ^ 2 / (P.C_codeg : ℝ)) ^ P.C_codeg
        ≤ (n : ℝ) ^ 2 * Real.exp (-(3 * L_log)) :=
          mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hm_le_n 2) hpow (by positivity) (sq_nonneg _)
      _ = 1 / (n : ℝ) := by
          rw [show -(3 * L_log) = -L_log + (-L_log + -L_log) by ring, Real.exp_add, Real.exp_add,
            Real.exp_neg, ← hn_exp]
          field_simp [hn_pos.ne']
      _ ≤ 1 / 50 := h1n_le

/-- Helper 2B: Asymptotic bound for `¬ GoodExtDegMid` (`≤ 1 / 50`). -/
lemma asymp_good_extDegMid {ε' : ℝ} (hε0 : 0 < ε') (hε1 : ε' ≤ 1 / 4) :
    ∀ᶠ n : ℕ in Filter.atTop,
      bernProb (mkParams ε' n).p (fun ω => ¬ GoodExtDegMid (mkParams ε' n) ω) ≤ 1 / 50 := by
  have hS := asymp_basic_scales hε0 hε1
  have hlog := eventually_lt_log (max 1000 (1000 / ε' ^ 2))
  have hrp1 := eventually_log_pow_lt_rpow (a := (1 / 20 : ℝ)) (by norm_num) 20 (10 ^ 12 / ε' ^ 2)
  filter_upwards [hS, hlog, hrp1, Filter.eventually_ge_atTop (1000 : ℕ)] with n hSc hlog_big hrp1 hn_ge
  rcases hSc with ⟨hV, _, ⟨_, hm_hi⟩, _, _, ⟨hk_lo, hk_hi⟩, ⟨hL_bd, hJ_bd⟩, _⟩
  set P := mkParams ε' n
  set L_log := Real.log (n : ℝ)
  have hL1000 : 1000 < L_log := lt_of_le_of_lt (le_max_left _ _) hlog_big
  have hL1 : (1 : ℝ) ≤ L_log := by linarith only [hL1000]
  have hLpos : 0 < L_log := by linarith only [hL1000]
  have hn_ge1000 : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith only [hn_ge1000]
  have hp0 : 0 ≤ P.p := hV.hp0
  have hn_exp : (n : ℝ) = Real.exp L_log := (Real.exp_log hn_pos).symm
  have he_lt3 : Real.exp 1 < 3 := by linarith only [Real.exp_one_lt_d9]
  have hn120_pos : 0 < (n : ℝ) ^ (1 / 20 : ℝ) := Real.rpow_pos_of_pos hn_pos _
  have hn120_ge1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 20 : ℝ) := Real.one_le_rpow (by linarith only [hn_ge1000]) (by norm_num)
  have hn120_le_n : (n : ℝ) ^ (1 / 20 : ℝ) ≤ (n : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith only [hn_ge1000] : (1 : ℝ) ≤ (n : ℝ)) (by norm_num : (1 / 20 : ℝ) ≤ 1)
  have hn12_eq : Real.sqrt (n : ℝ) = ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 10 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; congr 1; norm_num
  have hm_le_n : (P.m : ℝ) ≤ (n : ℝ) := by
    have hL5 : (2 : ℝ) ≤ L_log ^ 5 := by
      have : (1000 : ℝ) ^ 5 ≤ L_log ^ 5 := pow_le_pow_left₀ (by norm_num) hL1000.le 5
      linarith only [this]
    calc (P.m : ℝ) ≤ 2 * (n : ℝ) / L_log ^ 5 := hm_hi
      _ = (2 / L_log ^ 5) * (n : ℝ) := by ring
      _ ≤ 1 * (n : ℝ) := mul_le_mul_of_nonneg_right ((div_le_one (by positivity)).mpr hL5) hn_pos.le
      _ = (n : ℝ) := one_mul _
  have hk_hi2 : (P.k : ℝ) ≤ 2 * Real.sqrt ((n : ℝ) * L_log) := by
    nlinarith only [hk_hi, hε1, Real.sqrt_nonneg ((n : ℝ) * L_log)]
  have hkp_le : (P.k : ℝ) * P.p ≤ L_log := by
    have hprod : Real.sqrt ((n : ℝ) * L_log) * Real.sqrt (L_log / (n : ℝ)) = L_log := by
      rw [← Real.sqrt_mul (by positivity),
        show (n : ℝ) * L_log * (L_log / (n : ℝ)) = L_log ^ 2 by field_simp [hn_pos.ne'],
        Real.sqrt_sq hLpos.le]
    have h1 := mul_le_mul_of_nonneg_right hk_hi2 hV.hp0
    have hpdef : P.p = Real.sqrt (L_log / (n : ℝ)) / 2 := rfl
    rw [hpdef] at h1 ⊢
    linarith only [h1, hprod, show (2 * Real.sqrt ((n : ℝ) * L_log)) * (Real.sqrt (L_log / (n : ℝ)) / 2) =
      Real.sqrt ((n : ℝ) * L_log) * Real.sqrt (L_log / (n : ℝ)) by ring]
  have hap_le : ∀ i : ℕ, (P.clsSize i : ℝ) * P.p ≤ L_log / ((2 ^ i : ℕ) : ℝ) := by
    intro i
    have h2i_pos : (0 : ℝ) < ((2 ^ i : ℕ) : ℝ) := by positivity
    have hnat : P.clsSize i * 2 ^ i ≤ P.k :=
      (Nat.mul_le_mul_right _ (min_le_right _ _)).trans (Nat.div_mul_le_self _ _)
    have ha_le : (P.clsSize i : ℝ) ≤ (P.k : ℝ) / ((2 ^ i : ℕ) : ℝ) :=
      (le_div_iff₀ h2i_pos).mpr (by exact_mod_cast hnat)
    calc (P.clsSize i : ℝ) * P.p ≤ ((P.k : ℝ) / ((2 ^ i : ℕ) : ℝ)) * P.p := mul_le_mul_of_nonneg_right ha_le hV.hp0
      _ = (P.k : ℝ) * P.p / ((2 ^ i : ℕ) : ℝ) := by ring
      _ ≤ L_log / ((2 ^ i : ℕ) : ℝ) := div_le_div_of_nonneg_right hkp_le h2i_pos.le
  have hinv_e2 : (60 : ℝ) / L_log ≤ Real.exp (-2) := by
    rw [Real.exp_neg, le_inv_comm₀ (by positivity) (Real.exp_pos 2), inv_div]
    have he2 : Real.exp 2 < 9 := by
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith only [this, he_lt3, Real.exp_pos 1]
    have h1 : (9 : ℝ) ≤ L_log / 60 := by rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 60)]; linarith only [hL1000]
    linarith only [he2, h1]
  have hrmid_pos : ∀ i : Fin P.L, ∀ j : Fin P.J, 1 ≤ j.val →
      P.T_lo ≤ ((2 ^ i.val : ℕ) : ℝ) * ((2 ^ j.val : ℕ) : ℝ) →
      ((2 ^ i.val : ℕ) : ℝ) * ((2 ^ j.val : ℕ) : ℝ) ≤ P.T_mid → 1 ≤ P.rMid i.val j.val := by
    intro i j _ _ _
    dsimp only [RegParams.rMid]
    have hkpos : (0 : ℝ) < (P.k : ℝ) := by have hk1 : 1 ≤ P.k := hV.hk1; exact Nat.cast_pos.mpr (by omega)
    have hBpos := hV.hBmid
    exact Nat.ceil_pos.mpr (by positivity)
  refine (bernProb_not_goodExtDegMid_le P hV.hp0 hV.hp1 hrmid_pos).trans ?_
  have hterm : ∀ i : Fin P.L, ∀ j : Fin P.J,
      (if 1 ≤ j.val ∧ P.T_lo ≤ ((2 ^ i.val : ℕ) : ℝ) * ((2 ^ j.val : ℕ) : ℝ) ∧
          ((2 ^ i.val : ℕ) : ℝ) * ((2 ^ j.val : ℕ) : ℝ) ≤ P.T_mid then
        (P.m : ℝ) ^ P.clsSize i.val *
          (Real.exp 1 * (P.m : ℝ) / (P.rMid i.val j.val : ℝ) *
            (Real.exp 1 * (P.clsSize i.val : ℝ) * P.p / ((2 ^ j.val : ℕ) : ℝ)) ^ (2 ^ j.val)) ^
            P.rMid i.val j.val
      else 0) ≤ 1 / (n : ℝ) := by
    intro i j
    split_ifs with hcond
    · rcases hcond with ⟨hj1, hlo, hhi⟩
      set w : ℝ := ((2 ^ i.val : ℕ) : ℝ)
      set t_nat : ℕ := 2 ^ j.val
      set t : ℝ := (t_nat : ℝ)
      set a : ℕ := P.clsSize i.val
      set r : ℕ := P.rMid i.val j.val
      have hw_pos : 0 < w := by positivity
      have ht_pos : 0 < t := by positivity
      have ht2 : 2 ≤ t_nat := by simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hj1
      have hk2_ge : (n : ℝ) * L_log ≤ (P.k : ℝ) ^ 2 := by
        have h1 : Real.sqrt ((n : ℝ) * L_log) ≤ (P.k : ℝ) := by
          nlinarith only [hk_lo, hε0, Real.sqrt_nonneg ((n : ℝ) * L_log)]
        have := mul_le_mul h1 h1 (Real.sqrt_nonneg _) (by positivity)
        rwa [Real.mul_self_sqrt (by positivity), ← sq] at this
      have hr_ge : (n : ℝ) / ((w * t) ^ 2 * L_log ^ 2) ≤ (r : ℝ) := by
        have hcl : (P.k : ℝ) ^ 2 / (w ^ 2 * t ^ 2 * L_log ^ 3) ≤ (r : ℝ) := Nat.le_ceil _
        calc (n : ℝ) / ((w * t) ^ 2 * L_log ^ 2)
            = ((n : ℝ) * L_log) / (w ^ 2 * t ^ 2 * L_log ^ 3) := by
              field_simp [hw_pos.ne', ht_pos.ne', hLpos.ne']
          _ ≤ (P.k : ℝ) ^ 2 / (w ^ 2 * t ^ 2 * L_log ^ 3) :=
              div_le_div_of_nonneg_right hk2_ge (by positivity)
          _ ≤ (r : ℝ) := hcl
      have hq_le : Real.exp 1 * (a : ℝ) * P.p / t ≤ Real.exp 1 * L_log / (w * t) := by
        have h2 := mul_le_mul_of_nonneg_left (hap_le i.val) (Real.exp_pos 1).le
        calc Real.exp 1 * (a : ℝ) * P.p / t = (Real.exp 1 * ((a : ℝ) * P.p)) / t := by ring
          _ ≤ (Real.exp 1 * (L_log / w)) / t := div_le_div_of_nonneg_right h2 ht_pos.le
          _ = Real.exp 1 * L_log / (w * t) := by field_simp [hw_pos.ne', ht_pos.ne']
      have hq_le1 : Real.exp 1 * L_log / (w * t) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have hTlo : L_log ^ 2 ≤ w * t := hlo
        nlinarith only [he_lt3, hL1000, hTlo]
      have hq_pow : (Real.exp 1 * (a : ℝ) * P.p / t) ^ t_nat ≤ (Real.exp 1 * L_log / (w * t)) ^ 2 :=
        (pow_le_pow_left₀ (by positivity) hq_le t_nat).trans (pow_le_pow_of_le_one (by positivity) hq_le1 ht2)
      have hmr_le : Real.exp 1 * (P.m : ℝ) / (r : ℝ) ≤ 2 * Real.exp 1 * (w * t) ^ 2 / L_log ^ 3 := by
        calc Real.exp 1 * (P.m : ℝ) / (r : ℝ)
            ≤ Real.exp 1 * (2 * (n : ℝ) / L_log ^ 5) / ((n : ℝ) / ((w * t) ^ 2 * L_log ^ 2)) :=
              div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hm_hi (Real.exp_pos 1).le) (by positivity) hr_ge
          _ = 2 * Real.exp 1 * (w * t) ^ 2 / L_log ^ 3 := by
              field_simp [hn_pos.ne', hw_pos.ne', ht_pos.ne', hLpos.ne']
      have hbase_le : Real.exp 1 * (P.m : ℝ) / (r : ℝ) *
          (Real.exp 1 * (a : ℝ) * P.p / t) ^ t_nat ≤ Real.exp (-2) := by
        have he3 : Real.exp 1 ^ 3 ≤ 27 := by
          have hsq : Real.exp 1 ^ 2 ≤ 9 := by nlinarith only [he_lt3, Real.exp_pos 1]
          nlinarith only [hsq, he_lt3, Real.exp_pos 1]
        calc _ ≤ (2 * Real.exp 1 * (w * t) ^ 2 / L_log ^ 3) * (Real.exp 1 * L_log / (w * t)) ^ 2 :=
              mul_le_mul hmr_le hq_pow (by positivity) (by positivity)
          _ = 2 * Real.exp 1 ^ 3 / L_log := by field_simp [hw_pos.ne', ht_pos.ne', hLpos.ne']
          _ ≤ 60 / L_log := div_le_div_of_nonneg_right (by linarith only [he3]) hLpos.le
          _ ≤ Real.exp (-2) := hinv_e2
      have hr_big : (a : ℝ) * L_log + L_log ≤ (r : ℝ) := by
        have ha_le_k : (a : ℝ) ≤ (P.k : ℝ) := by
          exact_mod_cast ((min_le_right _ _).trans (Nat.div_le_self _ _) : P.clsSize i.val ≤ P.k)
        have hwt_sq : (w * t) ^ 2 ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
          have h1 : (w * t) ^ 2 ≤ ((n : ℝ) ^ (1 / 10 : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hhi 2
          have h2 : ((n : ℝ) ^ (1 / 10 : ℝ)) ^ 2 = (n : ℝ) ^ (1 / 5 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; congr 1; norm_num
          linarith only [h1, h2]
        have hr_ge2 : (n : ℝ) ^ (4 / 5 : ℝ) / L_log ^ 2 ≤ (r : ℝ) := by
          have hdiv : (n : ℝ) / ((n : ℝ) ^ (1 / 5 : ℝ) * L_log ^ 2) = (n : ℝ) ^ (4 / 5 : ℝ) / L_log ^ 2 := by
            have hsplit : (n : ℝ) = (n : ℝ) ^ (1 / 5 : ℝ) * (n : ℝ) ^ (4 / 5 : ℝ) := by
              rw [← Real.rpow_add hn_pos]; norm_num
            have hne : (n : ℝ) ^ (1 / 5 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hn_pos _).ne'
            calc (n : ℝ) / ((n : ℝ) ^ (1 / 5 : ℝ) * L_log ^ 2)
                = ((n : ℝ) ^ (1 / 5 : ℝ) * (n : ℝ) ^ (4 / 5 : ℝ)) / ((n : ℝ) ^ (1 / 5 : ℝ) * L_log ^ 2) := by
                  rw [← hsplit]
              _ = (n : ℝ) ^ (4 / 5 : ℝ) / L_log ^ 2 := by field_simp [hne, hLpos.ne']
          rw [← hdiv]
          exact (div_le_div_of_nonneg_left hn_pos.le (by positivity)
            (mul_le_mul_of_nonneg_right hwt_sq (sq_nonneg _))).trans hr_ge
        have hkL_le : (P.k : ℝ) * L_log + L_log ≤ (n : ℝ) ^ (4 / 5 : ℝ) / L_log ^ 2 := by
          rw [le_div_iff₀ (by positivity)]
          have hsr : Real.sqrt ((n : ℝ) * L_log) ≤ Real.sqrt (n : ℝ) * L_log := by
            rw [Real.sqrt_mul hn_pos.le]
            exact mul_le_mul_of_nonneg_left (Real.sqrt_le_iff.mpr ⟨hLpos.le, by nlinarith only [hL1000]⟩) (Real.sqrt_nonneg _)
          have h1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr (by linarith only [hn_ge1000])
          have hk_le : (P.k : ℝ) * L_log + L_log ≤ 3 * Real.sqrt (n : ℝ) * L_log ^ 2 := by
            nlinarith only [hk_hi2, hsr, h1, hL1000]
          have hL4 := log_pow_lt_rpow_of_big (C := 3) (b := 4) (by omega) (by norm_num) hε0 hε1 hL1 hrp1
          have hpow6 : (n : ℝ) ^ (1 / 20 : ℝ) ≤ ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 6 := by
            simpa using pow_le_pow_right₀ hn120_ge1 (by omega : 1 ≤ 6)
          have hn45 : (n : ℝ) ^ (4 / 5 : ℝ) = ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 16 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; congr 1; norm_num
          rw [hn45]
          have hmul1 := mul_le_mul_of_nonneg_right hk_le (sq_nonneg L_log)
          have hmul2 : (3 * Real.sqrt (n : ℝ) * L_log ^ 2) * L_log ^ 2 ≤ ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 16 := by
            rw [hn12_eq]
            have h3 : 3 * L_log ^ 4 ≤ ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 6 := by linarith only [hL4, hpow6]
            have h4 := mul_le_mul_of_nonneg_left h3 (pow_nonneg hn120_pos.le 10)
            linarith only [h4, show (3 * ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 10 * L_log ^ 2) * L_log ^ 2 =
              ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 10 * (3 * L_log ^ 4) by ring,
              show ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 10 * ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 6 = ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 16 by ring]
          linarith only [hmul1, hmul2]
        nlinarith only [ha_le_k, hLpos, hr_ge2, hkL_le]
      calc (P.m : ℝ) ^ a * (Real.exp 1 * (P.m : ℝ) / (r : ℝ) * (Real.exp 1 * (a : ℝ) * P.p / t) ^ t_nat) ^ r
          ≤ (n : ℝ) ^ a * (Real.exp (-2)) ^ r :=
            mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hm_le_n a)
              (pow_le_pow_left₀ (by positivity) hbase_le r) (by positivity) (by positivity)
        _ = Real.exp ((a : ℝ) * L_log - 2 * (r : ℝ)) := by
            rw [hn_exp, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
        _ ≤ Real.exp (-L_log) := Real.exp_le_exp.mpr (by linarith only [hr_big])
        _ = 1 / (n : ℝ) := by rw [Real.exp_neg, ← hn_exp, one_div]
    · positivity
  have hLJ_n : (P.L : ℝ) * (P.J : ℝ) * (1 / (n : ℝ)) ≤ 1 / 50 := by
    have hL_le_50L : (P.L : ℝ) ≤ 50 * L_log := by
      have : L_log ^ (1 / 4 : ℝ) ≤ L_log := by simpa using Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 / 4 : ℝ) ≤ 1)
      linarith only [hL_bd, this]
    have hprod : (P.L : ℝ) * (P.J : ℝ) ≤ 150 * L_log ^ 2 := by
      have := mul_le_mul hL_le_50L hJ_bd (Nat.cast_nonneg _) (by positivity)
      linarith only [this, show (50 * L_log) * (3 * L_log) = 150 * L_log ^ 2 by ring]
    have hL2 := log_pow_lt_rpow_of_big (C := 7500) (b := 2) (by omega) (by norm_num) hε0 hε1 hL1 hrp1
    rw [mul_one_div, div_le_div_iff₀ hn_pos (by norm_num : (0 : ℝ) < 50)]
    linarith only [hprod, hL2, hn120_le_n]
  calc ∑ i : Fin P.L, ∑ j : Fin P.J, _
      ≤ ∑ _i : Fin P.L, ∑ _j : Fin P.J, (1 / (n : ℝ)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = (P.L : ℝ) * (P.J : ℝ) * (1 / (n : ℝ)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ 1 / 50 := hLJ_n

/-- Helper 2C: Asymptotic bounds for `¬ GoodDegLarge` and `¬ GoodCrossPair` (each `≤ 1 / 50`). -/
lemma asymp_good_large_cross {ε' : ℝ} (hε0 : 0 < ε') (hε1 : ε' ≤ 1 / 4) :
    ∀ᶠ n : ℕ in Filter.atTop,
      bernProb (mkParams ε' n).p (fun ω => ¬ GoodDegLarge (mkParams ε' n) ω) ≤ 1 / 50 ∧
      bernProb (mkParams ε' n).p (fun ω => ¬ GoodCrossPair (mkParams ε' n) ω) ≤ 1 / 50 := by
  have hS := asymp_basic_scales hε0 hε1
  have hlog := eventually_lt_log (max 1000 (1000 / ε' ^ 2))
  have hrp1 := eventually_log_pow_lt_rpow (a := (1 / 20 : ℝ)) (by norm_num) 20 (10 ^ 12 / ε' ^ 2)
  filter_upwards [hS, hlog, hrp1, Filter.eventually_ge_atTop (1000 : ℕ)] with n hSc hlog_big hrp1 hn_ge
  rcases hSc with ⟨hV, _, ⟨_, hm_hi⟩, _, ⟨_, hF_hi⟩, ⟨hk_lo, hk_hi⟩, ⟨hL_bd, hJ_bd⟩, _⟩
  set P := mkParams ε' n
  set L_log := Real.log (n : ℝ)
  have hL1000 : 1000 < L_log := lt_of_le_of_lt (le_max_left _ _) hlog_big
  have hL1 : (1 : ℝ) ≤ L_log := by linarith only [hL1000]
  have hLpos : 0 < L_log := by linarith only [hL1000]
  have hn_ge1000 : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith only [hn_ge1000]
  have hp0 : 0 ≤ P.p := hV.hp0
  have hn_exp : (n : ℝ) = Real.exp L_log := (Real.exp_log hn_pos).symm
  have he_lt3 : Real.exp 1 < 3 := by linarith only [Real.exp_one_lt_d9]
  have hn120_pos : 0 < (n : ℝ) ^ (1 / 20 : ℝ) := Real.rpow_pos_of_pos hn_pos _
  have hn120_ge1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 20 : ℝ) := Real.one_le_rpow (by linarith only [hn_ge1000]) (by norm_num)
  have hn120_le_n : (n : ℝ) ^ (1 / 20 : ℝ) ≤ (n : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith only [hn_ge1000] : (1 : ℝ) ≤ (n : ℝ)) (by norm_num : (1 / 20 : ℝ) ≤ 1)
  have hn110_eq : (n : ℝ) ^ (1 / 10 : ℝ) = ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; congr 1; norm_num
  have hn12_eq : Real.sqrt (n : ℝ) = ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 10 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; congr 1; norm_num
  have h2m_le_n : 2 * (P.m : ℝ) ≤ (n : ℝ) := by
    have hL5 : (4 : ℝ) ≤ L_log ^ 5 := by
      have : (1000 : ℝ) ^ 5 ≤ L_log ^ 5 := pow_le_pow_left₀ (by norm_num) hL1000.le 5
      linarith only [this]
    calc 2 * (P.m : ℝ) ≤ 2 * (2 * (n : ℝ) / L_log ^ 5) := by linarith only [hm_hi]
      _ = (4 / L_log ^ 5) * (n : ℝ) := by ring
      _ ≤ 1 * (n : ℝ) := mul_le_mul_of_nonneg_right ((div_le_one (by positivity)).mpr hL5) hn_pos.le
      _ = (n : ℝ) := one_mul _
  have hm_le_n : (P.m : ℝ) ≤ (n : ℝ) := by linarith only [h2m_le_n, Nat.cast_nonneg (α := ℝ) P.m]
  have hk_hi2 : (P.k : ℝ) ≤ 2 * Real.sqrt ((n : ℝ) * L_log) := by
    nlinarith only [hk_hi, hε1, Real.sqrt_nonneg ((n : ℝ) * L_log)]
  have hkp_le : (P.k : ℝ) * P.p ≤ L_log := by
    have hprod : Real.sqrt ((n : ℝ) * L_log) * Real.sqrt (L_log / (n : ℝ)) = L_log := by
      rw [← Real.sqrt_mul (by positivity),
        show (n : ℝ) * L_log * (L_log / (n : ℝ)) = L_log ^ 2 by field_simp [hn_pos.ne'],
        Real.sqrt_sq hLpos.le]
    have h1 := mul_le_mul_of_nonneg_right hk_hi2 hV.hp0
    have hpdef : P.p = Real.sqrt (L_log / (n : ℝ)) / 2 := rfl
    rw [hpdef] at h1 ⊢
    linarith only [h1, hprod, show (2 * Real.sqrt ((n : ℝ) * L_log)) * (Real.sqrt (L_log / (n : ℝ)) / 2) =
      Real.sqrt ((n : ℝ) * L_log) * Real.sqrt (L_log / (n : ℝ)) by ring]
  have hap_le : ∀ i : ℕ, (P.clsSize i : ℝ) * P.p ≤ L_log / ((2 ^ i : ℕ) : ℝ) := by
    intro i
    have h2i_pos : (0 : ℝ) < ((2 ^ i : ℕ) : ℝ) := by positivity
    have hnat : P.clsSize i * 2 ^ i ≤ P.k :=
      (Nat.mul_le_mul_right _ (min_le_right _ _)).trans (Nat.div_mul_le_self _ _)
    have ha_le : (P.clsSize i : ℝ) ≤ (P.k : ℝ) / ((2 ^ i : ℕ) : ℝ) :=
      (le_div_iff₀ h2i_pos).mpr (by exact_mod_cast hnat)
    calc (P.clsSize i : ℝ) * P.p ≤ ((P.k : ℝ) / ((2 ^ i : ℕ) : ℝ)) * P.p := mul_le_mul_of_nonneg_right ha_le hV.hp0
      _ = (P.k : ℝ) * P.p / ((2 ^ i : ℕ) : ℝ) := by ring
      _ ≤ L_log / ((2 ^ i : ℕ) : ℝ) := div_le_div_of_nonneg_right hkp_le h2i_pos.le
  have hL_le_50L : (P.L : ℝ) ≤ 50 * L_log := by
    have : L_log ^ (1 / 4 : ℝ) ≤ L_log := by simpa using Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 / 4 : ℝ) ≤ 1)
    linarith only [hL_bd, this]
  constructor
  · -- GoodDegLarge
    refine (bernProb_not_goodDegLarge_le P hV.hp0 hV.hp1).trans ?_
    have hterm : ∀ i : Fin P.L, ∀ j : Fin P.J,
        (if P.T_mid < ((2 ^ i.val : ℕ) : ℝ) * ((2 ^ j.val : ℕ) : ℝ) then
          (P.m : ℝ) ^ (P.clsSize i.val + P.rLargeOut i.val j.val) *
            (Real.exp 1 * (P.clsSize i.val : ℝ) * P.p / ((2 ^ j.val : ℕ) : ℝ)) ^
              (P.rLargeOut i.val j.val * 2 ^ j.val) +
          (2 * (P.m : ℝ)) ^ P.clsSize i.val *
            (2 * Real.exp 1 * (P.clsSize i.val : ℝ) * P.p / ((2 ^ j.val : ℕ) : ℝ)) ^
              ((P.rLargeIn i.val j.val * 2 ^ j.val + 1) / 2)
        else 0) ≤ 2 * (1 / (n : ℝ)) := by
      intro i j
      split_ifs with hgt
      · set w : ℝ := ((2 ^ i.val : ℕ) : ℝ)
        set t_nat : ℕ := 2 ^ j.val
        set t : ℝ := (t_nat : ℝ)
        set a : ℕ := P.clsSize i.val
        set ro : ℕ := P.rLargeOut i.val j.val
        set ri : ℕ := P.rLargeIn i.val j.val
        have hw_pos : 0 < w := by positivity
        have ht_pos : 0 < t := by positivity
        have hw_le : w ≤ 2 * L_log ^ 5 := (hV.hL_le_F i).trans hF_hi
        have ht_ge80 : (80 : ℝ) ≤ t := by
          have h1 : (n : ℝ) ^ (1 / 10 : ℝ) < (2 * L_log ^ 5) * t := by
            have hT : P.T_mid = (n : ℝ) ^ (1 / 10 : ℝ) := rfl
            rw [hT] at hgt
            have := mul_le_mul_of_nonneg_right hw_le ht_pos.le
            linarith only [hgt, this]
          have hL5 := log_pow_lt_rpow_of_big (C := 160) (b := 5) (by omega) (by norm_num) hε0 hε1 hL1 hrp1
          have hsq : (n : ℝ) ^ (1 / 20 : ℝ) ≤ ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 2 := by nlinarith only [hn120_ge1]
          rw [hn110_eq] at h1
          have h2 : 80 * (2 * L_log ^ 5) < ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 2 := by linarith only [hL5, hsq]
          nlinarith only [h1, h2, show (0 : ℝ) < 2 * L_log ^ 5 by positivity]
        have hbase2 : 2 * Real.exp 1 * (a : ℝ) * P.p / t ≤ Real.exp (-(1 / 20 : ℝ) * L_log) := by
          have h1 : 2 * Real.exp 1 * (a : ℝ) * P.p / t ≤ 6 * L_log / (w * t) := by
            have hnum := mul_le_mul (by linarith only [he_lt3] : 2 * Real.exp 1 ≤ 6) (hap_le i.val) (by positivity) (by norm_num)
            calc 2 * Real.exp 1 * (a : ℝ) * P.p / t = (2 * Real.exp 1 * ((a : ℝ) * P.p)) / t := by ring
              _ ≤ (6 * (L_log / w)) / t := div_le_div_of_nonneg_right hnum ht_pos.le
              _ = 6 * L_log / (w * t) := by field_simp [hw_pos.ne', ht_pos.ne']
          have h2 : 6 * L_log / (w * t) ≤ 6 * L_log / (n : ℝ) ^ (1 / 10 : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hn_pos _) hgt.le
          have h3 : 6 * L_log / (n : ℝ) ^ (1 / 10 : ℝ) ≤ 1 / (n : ℝ) ^ (1 / 20 : ℝ) := by
            rw [hn110_eq, div_le_div_iff₀ (pow_pos hn120_pos 2) hn120_pos]
            have h6L := log_pow_lt_rpow_of_big (C := 6) (b := 1) (by omega) (by norm_num) hε0 hε1 hL1 hrp1
            rw [pow_one] at h6L
            nlinarith only [h6L, hn120_pos]
          have h4 : 1 / (n : ℝ) ^ (1 / 20 : ℝ) = Real.exp (-(1 / 20 : ℝ) * L_log) := by
            rw [one_div, Real.rpow_def_of_pos hn_pos, ← Real.exp_neg]; congr 1; ring
          linarith only [h1, h2, h3, h4]
        have hbase1 : Real.exp 1 * (a : ℝ) * P.p / t ≤ Real.exp (-(1 / 20 : ℝ) * L_log) := by
          have hnn : 0 ≤ Real.exp 1 * (a : ℝ) * P.p / t := by positivity
          linarith only [hbase2, hnn, show 2 * Real.exp 1 * (a : ℝ) * P.p / t = 2 * (Real.exp 1 * (a : ℝ) * P.p / t) by ring]
        have hT4a : (P.m : ℝ) ^ (a + ro) * (Real.exp 1 * (a : ℝ) * P.p / t) ^ (ro * t_nat) ≤ 1 / (n : ℝ) := by
          have hro_ge : 40 * (a : ℝ) / t + 1 ≤ (ro : ℝ) := by
            dsimp only [ro, RegParams.rLargeOut]; rw [Nat.cast_add, Nat.cast_one]
            linarith only [Nat.le_ceil (40 * (a : ℝ) / t)]
          have hrot1 : 40 * (a : ℝ) + t ≤ (ro : ℝ) * t := by
            have := mul_le_mul_of_nonneg_right hro_ge ht_pos.le
            have hsimp : (40 * (a : ℝ) / t + 1) * t = 40 * (a : ℝ) + t := by field_simp [ht_pos.ne']
            linarith only [this, hsimp]
          have hrot2 : 80 * (ro : ℝ) ≤ (ro : ℝ) * t := by
            have := mul_le_mul_of_nonneg_left ht_ge80 (Nat.cast_nonneg (α := ℝ) ro)
            linarith only [this]
          have hexp_ok : 20 * ((a : ℝ) + (ro : ℝ) + 1) ≤ ((ro * t_nat : ℕ) : ℝ) := by
            rw [Nat.cast_mul]; linarith only [hrot1, hrot2, ht_ge80]
          calc (P.m : ℝ) ^ (a + ro) * (Real.exp 1 * (a : ℝ) * P.p / t) ^ (ro * t_nat)
              ≤ (n : ℝ) ^ (a + ro) * (Real.exp (-(1 / 20 : ℝ) * L_log)) ^ (ro * t_nat) :=
                mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hm_le_n _)
                  (pow_le_pow_left₀ (by positivity) hbase1 _) (by positivity) (by positivity)
            _ = Real.exp (((a + ro : ℕ) : ℝ) * L_log - ((ro * t_nat : ℕ) : ℝ) / 20 * L_log) := by
                rw [hn_exp, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
            _ ≤ Real.exp (-L_log) := by
                refine Real.exp_le_exp.mpr ?_
                rw [Nat.cast_add]; nlinarith only [hexp_ok, hLpos]
            _ = 1 / (n : ℝ) := by rw [Real.exp_neg, ← hn_exp, one_div]
        have hT4b : (2 * (P.m : ℝ)) ^ a *
            (2 * Real.exp 1 * (a : ℝ) * P.p / t) ^ ((ri * t_nat + 1) / 2) ≤ 1 / (n : ℝ) := by
          have hri_ge : 80 * (a : ℝ) / t + 1 ≤ (ri : ℝ) := by
            dsimp only [ri, RegParams.rLargeIn]; rw [Nat.cast_add, Nat.cast_one]
            linarith only [Nat.le_ceil (80 * (a : ℝ) / t)]
          have hrit : 80 * (a : ℝ) + t ≤ (ri : ℝ) * t := by
            have := mul_le_mul_of_nonneg_right hri_ge ht_pos.le
            have hsimp : (80 * (a : ℝ) / t + 1) * t = 80 * (a : ℝ) + t := by field_simp [ht_pos.ne']
            linarith only [this, hsimp]
          have hdiv2 : 20 * ((a : ℝ) + 1) ≤ (((ri * t_nat + 1) / 2 : ℕ) : ℝ) := by
            have hnat : ri * t_nat ≤ 2 * ((ri * t_nat + 1) / 2) := by omega
            have hreal : ((ri * t_nat : ℕ) : ℝ) ≤ 2 * (((ri * t_nat + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hnat
            rw [Nat.cast_mul] at hreal; linarith only [hreal, hrit, ht_ge80]
          calc (2 * (P.m : ℝ)) ^ a * (2 * Real.exp 1 * (a : ℝ) * P.p / t) ^ ((ri * t_nat + 1) / 2)
              ≤ (n : ℝ) ^ a * (Real.exp (-(1 / 20 : ℝ) * L_log)) ^ ((ri * t_nat + 1) / 2) :=
                mul_le_mul (pow_le_pow_left₀ (by positivity) h2m_le_n _)
                  (pow_le_pow_left₀ (by positivity) hbase2 _) (by positivity) (by positivity)
            _ = Real.exp ((a : ℝ) * L_log - (((ri * t_nat + 1) / 2 : ℕ) : ℝ) / 20 * L_log) := by
                rw [hn_exp, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
            _ ≤ Real.exp (-L_log) := Real.exp_le_exp.mpr (by nlinarith only [hdiv2, hLpos])
            _ = 1 / (n : ℝ) := by rw [Real.exp_neg, ← hn_exp, one_div]
        linarith only [hT4a, hT4b]
      · positivity
    have hLJ_n : 2 * ((P.L : ℝ) * (P.J : ℝ) * (1 / (n : ℝ))) ≤ 1 / 50 := by
      have hprod : (P.L : ℝ) * (P.J : ℝ) ≤ 150 * L_log ^ 2 := by
        have := mul_le_mul hL_le_50L hJ_bd (Nat.cast_nonneg _) (by positivity)
        linarith only [this, show (50 * L_log) * (3 * L_log) = 150 * L_log ^ 2 by ring]
      have hL2 := log_pow_lt_rpow_of_big (C := 15000) (b := 2) (by omega) (by norm_num) hε0 hε1 hL1 hrp1
      have hdiv : (P.L : ℝ) * (P.J : ℝ) * (1 / (n : ℝ)) ≤ 1 / 100 := by
        rw [mul_one_div, div_le_div_iff₀ hn_pos (by norm_num : (0 : ℝ) < 100)]
        linarith only [hprod, hL2, hn120_le_n]
      linarith only [hdiv]
    calc ∑ i : Fin P.L, ∑ j : Fin P.J, _
        ≤ ∑ _i : Fin P.L, ∑ _j : Fin P.J, (2 * (1 / (n : ℝ))) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = 2 * ((P.L : ℝ) * (P.J : ℝ) * (1 / (n : ℝ))) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ 1 / 50 := hLJ_n
  · -- GoodCrossPair
    have hinv_e2 : (60 : ℝ) / L_log ≤ Real.exp (-2) := by
      rw [Real.exp_neg, le_inv_comm₀ (by positivity) (Real.exp_pos 2), inv_div]
      have he2 : Real.exp 2 < 9 := by
        have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith only [this, he_lt3, Real.exp_pos 1]
      have h1 : (9 : ℝ) ≤ L_log / 60 := by rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 60)]; linarith only [hL1000]
      linarith only [he2, h1]
    have hrcross_pos : ∀ i i' : Fin P.L, i.val < i'.val → 1 ≤ P.rCross i.val i'.val := by
      intro i i' _
      dsimp only [RegParams.rCross]
      have hkpos : (0 : ℝ) < (P.k : ℝ) := by have hk1 : 1 ≤ P.k := hV.hk1; exact Nat.cast_pos.mpr (by omega)
      have hBpos := hV.hBcross
      exact Nat.ceil_pos.mpr (by positivity)
    refine (bernProb_not_goodCrossPair_le P hV.hp0 hV.hp1 hrcross_pos).trans ?_
    have hterm : ∀ i i' : Fin P.L,
        (if i.val < i'.val then
          (P.m : ℝ) ^ (P.clsSize i.val + P.clsSize i'.val) *
            (Real.exp 1 * (P.m : ℝ) * (P.clsSize i.val : ℝ) * (P.clsSize i'.val : ℝ) * P.p ^ 2 /
              (P.rCross i.val i'.val : ℝ)) ^ P.rCross i.val i'.val
        else 0) ≤ 1 / (n : ℝ) := by
      intro i i'
      split_ifs with hlt
      · set w₁ : ℝ := ((2 ^ i.val : ℕ) : ℝ)
        set w₂ : ℝ := ((2 ^ i'.val : ℕ) : ℝ)
        set a₁ : ℕ := P.clsSize i.val
        set a₂ : ℕ := P.clsSize i'.val
        set r : ℕ := P.rCross i.val i'.val
        have hw1_pos : 0 < w₁ := by positivity
        have hw2_pos : 0 < w₂ := by positivity
        have hw1_le : w₁ ≤ 2 * L_log ^ 5 := (hV.hL_le_F i).trans hF_hi
        have hw2_le : w₂ ≤ 2 * L_log ^ 5 := (hV.hL_le_F i').trans hF_hi
        have hk2_ge : (n : ℝ) * L_log ≤ (P.k : ℝ) ^ 2 := by
          have h1 : Real.sqrt ((n : ℝ) * L_log) ≤ (P.k : ℝ) := by
            nlinarith only [hk_lo, hε0, Real.sqrt_nonneg ((n : ℝ) * L_log)]
          have := mul_le_mul h1 h1 (Real.sqrt_nonneg _) (by positivity)
          rwa [Real.mul_self_sqrt (by positivity), ← sq] at this
        have hr_ge : (n : ℝ) / (w₁ * w₂ * L_log ^ 2) ≤ (r : ℝ) := by
          have hcl : (P.k : ℝ) ^ 2 / (w₁ * w₂ * L_log ^ 3) ≤ (r : ℝ) := Nat.le_ceil _
          calc (n : ℝ) / (w₁ * w₂ * L_log ^ 2)
              = ((n : ℝ) * L_log) / (w₁ * w₂ * L_log ^ 3) := by
                field_simp [hw1_pos.ne', hw2_pos.ne', hLpos.ne']
            _ ≤ (P.k : ℝ) ^ 2 / (w₁ * w₂ * L_log ^ 3) := div_le_div_of_nonneg_right hk2_ge (by positivity)
            _ ≤ (r : ℝ) := hcl
        have hbase_le : Real.exp 1 * (P.m : ℝ) * (a₁ : ℝ) * (a₂ : ℝ) * P.p ^ 2 / (r : ℝ) ≤ Real.exp (-2) := by
          have haap := mul_le_mul (hap_le i.val) (hap_le i'.val) (by positivity) (by positivity)
          have hnum := mul_le_mul (mul_le_mul_of_nonneg_left hm_hi (Real.exp_pos 1).le) haap (by positivity) (by positivity)
          calc Real.exp 1 * (P.m : ℝ) * (a₁ : ℝ) * (a₂ : ℝ) * P.p ^ 2 / (r : ℝ)
              = (Real.exp 1 * (P.m : ℝ) * (((a₁ : ℝ) * P.p) * ((a₂ : ℝ) * P.p))) / (r : ℝ) := by ring
            _ ≤ (Real.exp 1 * (2 * (n : ℝ) / L_log ^ 5) * ((L_log / w₁) * (L_log / w₂))) /
                ((n : ℝ) / (w₁ * w₂ * L_log ^ 2)) := div_le_div₀ (by positivity) hnum (by positivity) hr_ge
            _ = 2 * Real.exp 1 / L_log := by field_simp [hn_pos.ne', hw1_pos.ne', hw2_pos.ne', hLpos.ne']
            _ ≤ 60 / L_log := div_le_div_of_nonneg_right (by linarith only [he_lt3]) hLpos.le
            _ ≤ Real.exp (-2) := hinv_e2
        have hr_big : ((a₁ + a₂ : ℕ) : ℝ) * L_log + L_log ≤ (r : ℝ) := by
          have ha1_le : (a₁ : ℝ) ≤ (P.k : ℝ) := by
            exact_mod_cast ((min_le_right _ _).trans (Nat.div_le_self _ _) : P.clsSize i.val ≤ P.k)
          have ha2_le : (a₂ : ℝ) ≤ (P.k : ℝ) := by
            exact_mod_cast ((min_le_right _ _).trans (Nat.div_le_self _ _) : P.clsSize i'.val ≤ P.k)
          have hw12 : w₁ * w₂ ≤ 4 * L_log ^ 10 := by
            have := mul_le_mul hw1_le hw2_le hw2_pos.le (by positivity)
            linarith only [this, show (2 * L_log ^ 5) * (2 * L_log ^ 5) = 4 * L_log ^ 10 by ring]
          have hr_ge2 : (n : ℝ) / (4 * L_log ^ 12) ≤ (r : ℝ) := by
            have h1 : w₁ * w₂ * L_log ^ 2 ≤ 4 * L_log ^ 12 := by
              have := mul_le_mul_of_nonneg_right hw12 (sq_nonneg L_log)
              linarith only [this, show 4 * L_log ^ 10 * L_log ^ 2 = 4 * L_log ^ 12 by ring]
            exact (div_le_div_of_nonneg_left hn_pos.le (by positivity) h1).trans hr_ge
          have h2kL_le : (2 * (P.k : ℝ) + 1) * L_log ≤ (n : ℝ) / (4 * L_log ^ 12) := by
            rw [le_div_iff₀ (by positivity)]
            have hsr : Real.sqrt ((n : ℝ) * L_log) ≤ Real.sqrt (n : ℝ) * L_log := by
              rw [Real.sqrt_mul hn_pos.le]
              exact mul_le_mul_of_nonneg_left (Real.sqrt_le_iff.mpr ⟨hLpos.le, by nlinarith only [hL1000]⟩) (Real.sqrt_nonneg _)
            have h1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr (by linarith only [hn_ge1000])
            have hlhs : (2 * (P.k : ℝ) + 1) * L_log ≤ 5 * Real.sqrt (n : ℝ) * L_log ^ 2 := by
              nlinarith only [hk_hi2, hsr, h1, hL1000]
            have hL14 := log_pow_lt_rpow_of_big (C := 20) (b := 14) (by omega) (by norm_num) hε0 hε1 hL1 hrp1
            have hpow10 : (n : ℝ) ^ (1 / 20 : ℝ) ≤ ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 10 := by
              simpa using pow_le_pow_right₀ hn120_ge1 (by omega : 1 ≤ 10)
            have h20L : 20 * L_log ^ 14 ≤ Real.sqrt (n : ℝ) := by rw [hn12_eq]; linarith only [hL14, hpow10]
            have hsr_sq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
            have hmul1 := mul_le_mul_of_nonneg_right hlhs (show (0 : ℝ) ≤ 4 * L_log ^ 12 by positivity)
            have hmul2 := mul_le_mul_of_nonneg_left h20L (Real.sqrt_nonneg (n : ℝ))
            linarith only [hmul1, hmul2, hsr_sq,
              show (5 * Real.sqrt (n : ℝ) * L_log ^ 2) * (4 * L_log ^ 12) = Real.sqrt (n : ℝ) * (20 * L_log ^ 14) by ring]
          rw [Nat.cast_add]; nlinarith only [ha1_le, ha2_le, hLpos, h2kL_le, hr_ge2]
        calc (P.m : ℝ) ^ (a₁ + a₂) *
              (Real.exp 1 * (P.m : ℝ) * (a₁ : ℝ) * (a₂ : ℝ) * P.p ^ 2 / (r : ℝ)) ^ r
            ≤ (n : ℝ) ^ (a₁ + a₂) * (Real.exp (-2)) ^ r :=
              mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hm_le_n _)
                (pow_le_pow_left₀ (by positivity) hbase_le _) (by positivity) (by positivity)
          _ = Real.exp (((a₁ + a₂ : ℕ) : ℝ) * L_log - 2 * (r : ℝ)) := by
              rw [hn_exp, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
          _ ≤ Real.exp (-L_log) := Real.exp_le_exp.mpr (by linarith only [hr_big])
          _ = 1 / (n : ℝ) := by rw [Real.exp_neg, ← hn_exp, one_div]
      · positivity
    have hL2_n : (P.L : ℝ) ^ 2 * (1 / (n : ℝ)) ≤ 1 / 50 := by
      have hL2 : (P.L : ℝ) ^ 2 ≤ 2500 * L_log ^ 2 := by
        have := pow_le_pow_left₀ (Nat.cast_nonneg _) hL_le_50L 2
        linarith only [this, show (50 * L_log) ^ 2 = 2500 * L_log ^ 2 by ring]
      have hbig := log_pow_lt_rpow_of_big (C := 125000) (b := 2) (by omega) (by norm_num) hε0 hε1 hL1 hrp1
      rw [mul_one_div, div_le_div_iff₀ hn_pos (by norm_num : (0 : ℝ) < 50)]
      linarith only [hL2, hbig, hn120_le_n]
    calc ∑ i : Fin P.L, ∑ i' : Fin P.L, _
        ≤ ∑ _i : Fin P.L, ∑ _i' : Fin P.L, (1 / (n : ℝ)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun i' _ => hterm i i'
      _ = (P.L : ℝ) ^ 2 * (1 / (n : ℝ)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ 1 / 50 := hL2_n

/-- Helper 2: Asymptotic regularity probability bound `P(¬ GoodGraph P ω) ≤ 1 / 10`. -/
lemma asymp_goodGraph_bound {ε' : ℝ} (hε0 : 0 < ε') (hε1 : ε' ≤ 1 / 4) :
    ∀ᶠ n : ℕ in Filter.atTop,
      bernProb (mkParams ε' n).p (fun ω => ¬ GoodGraph (mkParams ε' n) ω) ≤ 1 / 10 := by
  filter_upwards [asymp_basic_scales hε0 hε1, asymp_good_deg_codeg hε0 hε1,
    asymp_good_extDegMid hε0 hε1, asymp_good_large_cross hε0 hε1] with n hBas h12 h3 h45
  rcases hBas with ⟨hV, _, _, _, _, _, _, _⟩
  set P := mkParams ε' n
  have himp : ∀ ω : EdgeIdx P.m → Bool, ¬ GoodGraph P ω →
      ¬ GoodMaxDeg P ω ∨ ¬ GoodMaxCodeg P ω ∨ ¬ GoodExtDegMid P ω ∨
      ¬ GoodDegLarge P ω ∨ ¬ GoodCrossPair P ω := fun _ h => by dsimp only [GoodGraph] at h; tauto
  have h0 := bernProb_mono hV.hp0 hV.hp1 himp
  have u1 := bernProb_or_le hV.hp0 hV.hp1 (fun ω => ¬ GoodMaxDeg P ω)
    (fun ω => ¬ GoodMaxCodeg P ω ∨ ¬ GoodExtDegMid P ω ∨ ¬ GoodDegLarge P ω ∨ ¬ GoodCrossPair P ω)
  have u2 := bernProb_or_le hV.hp0 hV.hp1 (fun ω => ¬ GoodMaxCodeg P ω)
    (fun ω => ¬ GoodExtDegMid P ω ∨ ¬ GoodDegLarge P ω ∨ ¬ GoodCrossPair P ω)
  have u3 := bernProb_or_le hV.hp0 hV.hp1 (fun ω => ¬ GoodExtDegMid P ω)
    (fun ω => ¬ GoodDegLarge P ω ∨ ¬ GoodCrossPair P ω)
  have u4 := bernProb_or_le hV.hp0 hV.hp1 (fun ω => ¬ GoodDegLarge P ω)
    (fun ω => ¬ GoodCrossPair P ω)
  linarith only [h0, u1, u2, u3, u4, h12.1, h12.2, h3, h45.1, h45.2]

/-- Helper 3A: Entropy + compression + `Qmax` prefactor bound for `(a, b) ∈ [1, k]^2`. -/
lemma asymp_indep_pref_bound {ε' : ℝ} (hε0 : 0 < ε') (hε1 : ε' ≤ 1 / 4) :
    ∀ᶠ n : ℕ in Filter.atTop,
      let P := mkParams ε' n
      let L_log := Real.log (n : ℝ)
      ∀ a ∈ Finset.Icc 1 P.k, ∀ b ∈ Finset.Icc 1 P.k,
        let Pref := (n.choose P.k : ℝ) *
          ((P.m.choose a : ℝ) * ((a : ℝ) / (P.m : ℝ)) ^ P.k) *
          ((P.m.choose b : ℝ) * ((b : ℝ) / (P.m : ℝ)) ^ P.k) *
          (((Qmax P + 1 : ℕ) : ℝ) * ((P.k + 1 : ℕ) : ℝ) ^ Qmax P) ^ 2
        Pref ≤ Real.exp ((1 / 2 : ℝ) * ((a : ℝ) / (P.k : ℝ) + (b : ℝ) / (P.k : ℝ) - 1) * (P.k : ℝ) * L_log +
            (3 + 14 * Real.log L_log) * (P.k : ℝ)) ∧
        Pref ≤ Real.exp ((P.k : ℝ) * L_log) := by
  have hS := asymp_valid_and_scales hε0 hε1
  have hlog := eventually_lt_log (max 1000 ((10 ^ 14 / ε' ^ 2) ^ 2))
  have hrp1 := eventually_log_pow_lt_rpow (a := (1 / 20 : ℝ)) (by norm_num) 20 (10 ^ 12 / ε' ^ 2)
  filter_upwards [hS, hlog, hrp1, Filter.eventually_ge_atTop (1000 : ℕ)] with n hSc hlog_big hrp1 hn_ge
  rcases hSc with ⟨hV, _, ⟨hm_lo, _⟩, _, _, ⟨hk_lo, hk_hi⟩, _, _, _, _, _, hQ_le⟩
  intro P L_log a ha b hb Pref
  have hL1000 : 1000 < L_log := lt_of_le_of_lt (le_max_left _ _) hlog_big
  have hL1 : (1 : ℝ) ≤ L_log := by linarith only [hL1000]
  have hLpos : 0 < L_log := by linarith only [hL1000]
  have hn_ge1000 : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith only [hn_ge1000]
  have hn_exp : (n : ℝ) = Real.exp L_log := (Real.exp_log hn_pos).symm
  have he_lt3 : Real.exp 1 < 3 := by linarith only [Real.exp_one_lt_d9]
  have hm_pos : (0 : ℝ) < (P.m : ℝ) := lt_of_lt_of_le (by positivity) hm_lo
  have hk1 : 1 ≤ P.k := hV.hk1
  have hk_pos : (0 : ℝ) < (P.k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hk_hi2 : (P.k : ℝ) ≤ 2 * Real.sqrt ((n : ℝ) * L_log) := by
    nlinarith only [hk_hi, hε1, Real.sqrt_nonneg ((n : ℝ) * L_log)]
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
  have hak : a ≤ P.k := (Finset.mem_Icc.mp ha).2
  have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
  have hbk : b ≤ P.k := (Finset.mem_Icc.mp hb).2
  have hn120_ge1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 20 : ℝ) := Real.one_le_rpow (by linarith only [hn_ge1000]) (by norm_num)
  have hn12_eq : Real.sqrt (n : ℝ) = ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 10 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; congr 1; norm_num
  have hpow10 : (n : ℝ) ^ (1 / 20 : ℝ) ≤ ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 10 := by
    simpa using pow_le_pow_right₀ hn120_ge1 (by omega : 1 ≤ 10)
  have hk_ge_sr : Real.sqrt (n : ℝ) ≤ (P.k : ℝ) := by
    have h1 := Real.sqrt_le_sqrt (by nlinarith only [hn_pos, hL1000] : (n : ℝ) ≤ (n : ℝ) * L_log)
    nlinarith only [h1, hk_lo, hε0, Real.sqrt_nonneg ((n : ℝ) * L_log)]
  have hsr_nL : Real.sqrt ((n : ℝ) * L_log) ≤ Real.sqrt (n : ℝ) * L_log := by
    rw [Real.sqrt_mul hn_pos.le]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_iff.mpr ⟨hLpos.le, by nlinarith only [hL1000]⟩) (Real.sqrt_nonneg _)
  have hchoose_nk : (n.choose P.k : ℝ) ≤ Real.exp ((1 / 2 : ℝ) * (P.k : ℝ) * L_log) := by
    have h1 : (n.choose P.k : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (P.k : ℝ)) ^ P.k := choose_le_exp_pow hk1
    have hbase : Real.exp 1 * (n : ℝ) / (P.k : ℝ) ≤ Real.exp ((1 / 2 : ℝ) * L_log) := by
      have hsr_eq : Real.sqrt (n : ℝ) = Real.exp ((1 / 2 : ℝ) * L_log) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn_pos]; congr 1; ring
      rw [← hsr_eq, div_le_iff₀ hk_pos]
      have hsr_L : Real.exp 1 ≤ Real.sqrt L_log :=
        Real.le_sqrt_of_sq_le (by nlinarith only [he_lt3, Real.exp_pos 1, hL1000])
      have hmul : Real.exp 1 * (n : ℝ) ≤ Real.sqrt (n : ℝ) * Real.sqrt ((n : ℝ) * L_log) := by
        rw [Real.sqrt_mul hn_pos.le, ← mul_assoc, Real.mul_self_sqrt hn_pos.le, mul_comm (Real.exp 1) (n : ℝ)]
        exact mul_le_mul_of_nonneg_left hsr_L hn_pos.le
      have h2 := mul_le_mul_of_nonneg_left
        (by nlinarith only [hk_lo, hε0, Real.sqrt_nonneg ((n : ℝ) * L_log)] : Real.sqrt ((n : ℝ) * L_log) ≤ (P.k : ℝ))
        (Real.sqrt_nonneg (n : ℝ))
      linarith only [hmul, h2]
    calc (n.choose P.k : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (P.k : ℝ)) ^ P.k := h1
      _ ≤ (Real.exp ((1 / 2 : ℝ) * L_log)) ^ P.k := pow_le_pow_left₀ (by positivity) hbase _
      _ = Real.exp ((1 / 2 : ℝ) * (P.k : ℝ) * L_log) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hcomp_bound : ∀ c : ℕ, 1 ≤ c → c ≤ P.k →
      (P.m.choose c : ℝ) * ((c : ℝ) / (P.m : ℝ)) ^ P.k ≤
        Real.exp (-(1 / 2 : ℝ) * ((P.k - c : ℕ) : ℝ) * L_log + (1 + 7 * Real.log L_log) * (P.k : ℝ)) := by
    intro c hc1 hck
    have hc_pos : (0 : ℝ) < (c : ℝ) := Nat.cast_pos.mpr (by omega)
    have h1 : (P.m.choose c : ℝ) * ((c : ℝ) / (P.m : ℝ)) ^ P.k ≤
        Real.exp (P.k : ℝ) * ((P.k : ℝ) / (P.m : ℝ)) ^ (P.k - c) := by
      have hch := choose_le_exp_pow (N := P.m) hc1
      have hsplit : ((c : ℝ) / (P.m : ℝ)) ^ P.k =
          ((c : ℝ) / (P.m : ℝ)) ^ c * ((c : ℝ) / (P.m : ℝ)) ^ (P.k - c) := by
        rw [← pow_add, Nat.add_sub_of_le hck]
      have hcancel : (Real.exp 1 * (P.m : ℝ) / (c : ℝ)) ^ c * ((c : ℝ) / (P.m : ℝ)) ^ c = Real.exp (c : ℝ) := by
        rw [← mul_pow, show Real.exp 1 * (P.m : ℝ) / (c : ℝ) * ((c : ℝ) / (P.m : ℝ)) = Real.exp 1 by
          field_simp [hc_pos.ne', hm_pos.ne'], ← Real.exp_nat_mul, mul_one]
      have he_le : Real.exp (c : ℝ) ≤ Real.exp (P.k : ℝ) := Real.exp_le_exp.mpr (by exact_mod_cast hck)
      have hcm_le := pow_le_pow_left₀ (show (0 : ℝ) ≤ (c : ℝ) / (P.m : ℝ) by positivity)
        (div_le_div_of_nonneg_right (by exact_mod_cast hck : (c : ℝ) ≤ (P.k : ℝ)) hm_pos.le) (P.k - c)
      calc (P.m.choose c : ℝ) * ((c : ℝ) / (P.m : ℝ)) ^ P.k
          ≤ (Real.exp 1 * (P.m : ℝ) / (c : ℝ)) ^ c * (((c : ℝ) / (P.m : ℝ)) ^ c * ((c : ℝ) / (P.m : ℝ)) ^ (P.k - c)) := by
            rw [hsplit]; exact mul_le_mul_of_nonneg_right hch (by positivity)
        _ = Real.exp (c : ℝ) * ((c : ℝ) / (P.m : ℝ)) ^ (P.k - c) := by rw [← mul_assoc, hcancel]
        _ ≤ Real.exp (P.k : ℝ) * ((P.k : ℝ) / (P.m : ℝ)) ^ (P.k - c) :=
            mul_le_mul he_le hcm_le (by positivity) (Real.exp_pos _).le
    have hkm_le : (P.k : ℝ) / (P.m : ℝ) ≤ Real.exp (7 * Real.log L_log - (1 / 2 : ℝ) * L_log) := by
      have h2L6 : (P.k : ℝ) / (P.m : ℝ) ≤ 2 * L_log ^ 6 / Real.sqrt (n : ℝ) := by
        have hsr_sq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
        have hsr_ne : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn_pos).ne'
        calc (P.k : ℝ) / (P.m : ℝ) ≤ (2 * Real.sqrt (n : ℝ) * L_log) / ((n : ℝ) / L_log ^ 5) :=
              div_le_div₀ (by positivity) (by linarith only [hk_hi2, hsr_nL]) (by positivity) hm_lo
          _ = (2 * Real.sqrt (n : ℝ) * L_log) / ((Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) / L_log ^ 5) := by
              rw [hsr_sq]
          _ = 2 * L_log ^ 6 / Real.sqrt (n : ℝ) := by
              field_simp [hsr_ne, hLpos.ne']
      have hlog_2L6 : 2 * L_log ^ 6 ≤ Real.exp (7 * Real.log L_log) := by
        have h1' : Real.log (2 * L_log ^ 6) ≤ 7 * Real.log L_log := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
          have : Real.log 2 ≤ Real.log L_log := Real.log_le_log (by norm_num) (by linarith only [hL1000])
          push_cast; linarith only [this]
        have := Real.exp_le_exp.mpr h1'; rwa [Real.exp_log (by positivity)] at this
      have hsr_exp : Real.sqrt (n : ℝ) = Real.exp ((1 / 2 : ℝ) * L_log) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn_pos]; congr 1; ring
      calc (P.k : ℝ) / (P.m : ℝ) ≤ 2 * L_log ^ 6 / Real.sqrt (n : ℝ) := h2L6
        _ ≤ Real.exp (7 * Real.log L_log) / Real.exp ((1 / 2 : ℝ) * L_log) := by
            rw [hsr_exp]; exact div_le_div_of_nonneg_right hlog_2L6 (Real.exp_pos _).le
        _ = Real.exp (7 * Real.log L_log - (1 / 2 : ℝ) * L_log) := (Real.exp_sub _ _).symm
    have hlogL_nn : 0 ≤ Real.log L_log := Real.log_nonneg hL1
    have hkc_le : ((P.k - c : ℕ) : ℝ) ≤ (P.k : ℝ) := by exact_mod_cast Nat.sub_le P.k c
    calc (P.m.choose c : ℝ) * ((c : ℝ) / (P.m : ℝ)) ^ P.k
        ≤ Real.exp (P.k : ℝ) * (Real.exp (7 * Real.log L_log - (1 / 2 : ℝ) * L_log)) ^ (P.k - c) :=
          h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hkm_le _) (Real.exp_pos _).le)
      _ = Real.exp ((P.k : ℝ) + ((P.k - c : ℕ) : ℝ) * (7 * Real.log L_log - (1 / 2 : ℝ) * L_log)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
      _ ≤ Real.exp (-(1 / 2 : ℝ) * ((P.k - c : ℕ) : ℝ) * L_log + (1 + 7 * Real.log L_log) * (P.k : ℝ)) := by
          refine Real.exp_le_exp.mpr ?_; nlinarith only [hlogL_nn, hkc_le]
  have hQ_fac : (((Qmax P + 1 : ℕ) : ℝ) * ((P.k + 1 : ℕ) : ℝ) ^ Qmax P) ^ 2 ≤ Real.exp (P.k : ℝ) := by
    have hQ1_le : ((Qmax P + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one]
      have hL4 := log_pow_lt_rpow_of_big (C := 2 * 10 ^ 5) (b := 4) (by omega) (by norm_num) hε0 hε1 hL1 hrp1
      have hsr_le_n : Real.sqrt (n : ℝ) ≤ (n : ℝ) := Real.sqrt_le_iff.mpr ⟨hn_pos.le, by nlinarith only [hn_ge1000]⟩
      have hL4_ge1 : (1 : ℝ) ≤ L_log ^ 4 := one_le_pow₀ hL1
      rw [hn12_eq] at hsr_le_n
      linarith only [hQ_le, hL4_ge1, hL4, hpow10, hsr_le_n]
    have hk1_le : ((P.k + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one]
      have h1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr (by linarith only [hn_ge1000])
      have hk1' : (P.k : ℝ) + 1 ≤ 3 * Real.sqrt (n : ℝ) * L_log := by nlinarith only [hk_hi2, hsr_nL, h1, hL1000]
      have h3L := log_pow_lt_rpow_of_big (C := 3) (b := 1) (by omega) (by norm_num) hε0 hε1 hL1 hrp1
      rw [pow_one] at h3L
      have h3L_sr : 3 * L_log ≤ Real.sqrt (n : ℝ) := by rw [hn12_eq]; linarith only [h3L, hpow10]
      have hsr_sq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
      have hmul := mul_le_mul_of_nonneg_left h3L_sr (Real.sqrt_nonneg (n : ℝ))
      linarith only [hk1', hmul, hsr_sq, show 3 * Real.sqrt (n : ℝ) * L_log = Real.sqrt (n : ℝ) * (3 * L_log) by ring]
    have hpow : (((Qmax P + 1 : ℕ) : ℝ) * ((P.k + 1 : ℕ) : ℝ) ^ Qmax P) ^ 2 ≤
        Real.exp (2 * ((Qmax P : ℝ) + 1) * L_log) := by
      have h1 := mul_le_mul hQ1_le (pow_le_pow_left₀ (Nat.cast_nonneg _) hk1_le (Qmax P)) (by positivity) hn_pos.le
      calc (((Qmax P + 1 : ℕ) : ℝ) * ((P.k + 1 : ℕ) : ℝ) ^ Qmax P) ^ 2
          ≤ ((n : ℝ) * (n : ℝ) ^ Qmax P) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
        _ = ((Real.exp L_log) * (Real.exp L_log) ^ Qmax P) ^ 2 := by rw [← hn_exp]
        _ = Real.exp (2 * ((Qmax P : ℝ) + 1) * L_log) := by
            rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hexp_le : 2 * ((Qmax P : ℝ) + 1) * L_log ≤ (P.k : ℝ) := by
      have hL5 := log_pow_lt_rpow_of_big (C := 4 * 10 ^ 5) (b := 5) (by omega) (by norm_num) hε0 hε1 hL1 hrp1
      have hL4_ge1 : (1 : ℝ) ≤ L_log ^ 4 := one_le_pow₀ hL1
      have h1 : 2 * ((Qmax P : ℝ) + 1) * L_log ≤ 4 * (10 ^ 5 : ℝ) * L_log ^ 5 := by
        have hq : (Qmax P : ℝ) + 1 ≤ 2 * (10 ^ 5 : ℝ) * L_log ^ 4 := by linarith only [hQ_le, hL4_ge1]
        have hmul := mul_le_mul_of_nonneg_right hq (by linarith only [hLpos] : 0 ≤ 2 * L_log)
        linarith only [hmul, show ((Qmax P : ℝ) + 1) * (2 * L_log) = 2 * ((Qmax P : ℝ) + 1) * L_log by ring,
          show (2 * (10 ^ 5 : ℝ) * L_log ^ 4) * (2 * L_log) = 4 * (10 ^ 5 : ℝ) * L_log ^ 5 by ring]
      rw [hn12_eq] at hk_ge_sr
      linarith only [h1, hL5, hpow10, hk_ge_sr]
    exact hpow.trans (Real.exp_le_exp.mpr hexp_le)
  have hPref_le : Pref ≤ Real.exp ((1 / 2 : ℝ) * ((a : ℝ) / (P.k : ℝ) + (b : ℝ) / (P.k : ℝ) - 1) * (P.k : ℝ) * L_log +
      (3 + 14 * Real.log L_log) * (P.k : ℝ)) := by
    have hmul1 := mul_le_mul hchoose_nk (hcomp_bound a ha1 hak) (by positivity) (Real.exp_pos _).le
    have hmul2 := mul_le_mul hmul1 (hcomp_bound b hb1 hbk) (by positivity) (by positivity)
    have hmul3 := mul_le_mul hmul2 hQ_fac (by positivity) (by positivity)
    refine hmul3.trans (le_of_eq ?_)
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [Nat.cast_sub hak, Nat.cast_sub hbk]
    have hxk : (a : ℝ) / (P.k : ℝ) * (P.k : ℝ) = (a : ℝ) := div_mul_cancel₀ _ hk_pos.ne'
    have hyk : (b : ℝ) / (P.k : ℝ) * (P.k : ℝ) = (b : ℝ) := div_mul_cancel₀ _ hk_pos.ne'
    rw [show (1 / 2 : ℝ) * ((a : ℝ) / (P.k : ℝ) + (b : ℝ) / (P.k : ℝ) - 1) * (P.k : ℝ) * L_log =
      (1 / 2 : ℝ) * ((a : ℝ) / (P.k : ℝ) * (P.k : ℝ) + (b : ℝ) / (P.k : ℝ) * (P.k : ℝ) - (P.k : ℝ)) * L_log by ring,
      hxk, hyk]
    ring
  have hPref_simple : Pref ≤ Real.exp ((P.k : ℝ) * L_log) := by
    refine hPref_le.trans (Real.exp_le_exp.mpr ?_)
    have hlogL_le : Real.log L_log ≤ 4 * L_log ^ (1 / 4 : ℝ) := log_le_four_rpow_quarter hLpos
    have hL14_le : L_log ^ (1 / 4 : ℝ) ≤ L_log / 1000 := by
      have h2 : (1000 : ℝ) ≤ L_log ^ (3 / 4 : ℝ) := by
        have h34 : (L_log ^ (3 / 4 : ℝ)) ^ 4 = L_log ^ 3 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le,
            show (3 / 4 : ℝ) * (4 : ℕ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
        have hLbig : (10 ^ 14 / ε' ^ 2) ^ 2 < L_log := lt_of_le_of_lt (le_max_right _ _) hlog_big
        have h1014 : (10 ^ 14 : ℝ) ≤ 10 ^ 14 / ε' ^ 2 := by
          rw [le_div_iff₀ (sq_pos_of_pos hε0)]
          have hsq : ε' ^ 2 ≤ 1 := by nlinarith only [hε0, hε1]
          nlinarith only [hsq]
        have h1028 : (10 ^ 28 : ℝ) ≤ L_log := by nlinarith only [hLbig, h1014]
        have hL3 : L_log ≤ L_log ^ 3 := by simpa using pow_le_pow_right₀ hL1 (by omega : 1 ≤ 3)
        have hpos34 : 0 ≤ L_log ^ (3 / 4 : ℝ) := Real.rpow_nonneg hLpos.le _
        by_contra hlt; push Not at hlt
        have hlt4 : (L_log ^ (3 / 4 : ℝ)) ^ 4 < (1000 : ℝ) ^ 4 := pow_lt_pow_left₀ hlt hpos34 (by omega)
        linarith only [h34, hlt4, h1028, hL3]
      have hprod : L_log ^ (1 / 4 : ℝ) * L_log ^ (3 / 4 : ℝ) = L_log := by rw [← Real.rpow_add hLpos]; norm_num
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1000)]
      nlinarith only [h2, hprod, Real.rpow_nonneg hLpos.le (1 / 4 : ℝ)]
    have hx1 : (a : ℝ) / (P.k : ℝ) ≤ 1 := (div_le_one hk_pos).mpr (by exact_mod_cast hak)
    have hy1 : (b : ℝ) / (P.k : ℝ) ≤ 1 := (div_le_one hk_pos).mpr (by exact_mod_cast hbk)
    have hcoeff : 3 + 14 * Real.log L_log ≤ (1 / 2 : ℝ) * L_log := by linarith only [hlogL_le, hL14_le, hL1000]
    have hxy : (1 / 2 : ℝ) * ((a : ℝ) / (P.k : ℝ) + (b : ℝ) / (P.k : ℝ) - 1) * ((P.k : ℝ) * L_log) ≤
        (1 / 2 : ℝ) * ((P.k : ℝ) * L_log) :=
      mul_le_mul_of_nonneg_right (by linarith only [hx1, hy1]) (mul_pos hk_pos hLpos).le
    have h2 := mul_le_mul_of_nonneg_right hcoeff hk_pos.le
    linarith only [hxy, h2,
      show (1 / 2 : ℝ) * ((a : ℝ) / (P.k : ℝ) + (b : ℝ) / (P.k : ℝ) - 1) * (P.k : ℝ) * L_log =
        (1 / 2 : ℝ) * ((a : ℝ) / (P.k : ℝ) + (b : ℝ) / (P.k : ℝ) - 1) * ((P.k : ℝ) * L_log) by ring]
  exact ⟨hPref_le, hPref_simple⟩

/-- Helper 3: Asymptotic independent-set union bound per `(a, b) ∈ [1, k]^2`. -/
lemma asymp_indep_bound {ε' : ℝ} (hε0 : 0 < ε') (hε1 : ε' ≤ 1 / 4) :
    let lam₁ : ℝ := Real.log (1024 / ε' ^ 2)
    let η_s : ℝ := ε' ^ 2 / (1024 * lam₁)
    let lam₂ : ℝ := 20 / η_s
    ∀ᶠ n : ℕ in Filter.atTop,
      let P := mkParams ε' n
      let F_max := (1 + P.η₀) * ((n : ℝ) / (P.m : ℝ))
      let T_small := η_s * P.p * (P.k : ℝ) ^ 2
      ∀ a ∈ Finset.Icc 1 P.k, ∀ b ∈ Finset.Icc 1 P.k,
        let D := F_max * ((1 + P.η₀) * ((P.m : ℝ) * P.p))
        let M_open :=
          (1 / 2 : ℝ) * max 0 ((a : ℝ) ^ 2 - min (((P.k - b : ℕ) : ℝ) ^ 2) (D * ((P.k - b : ℕ) : ℝ))) +
          (1 / 2 : ℝ) * max 0 ((b : ℝ) ^ 2 - min (((P.k - a : ℕ) : ℝ) ^ 2) (D * ((P.k - a : ℕ) : ℝ))) -
          2 * errOpen P F_max
        (n.choose P.k : ℝ) *
          ((P.m.choose a : ℝ) * ((a : ℝ) / (P.m : ℝ)) ^ P.k) *
          ((P.m.choose b : ℝ) * ((b : ℝ) / (P.m : ℝ)) ^ P.k) *
          (((Qmax P + 1 : ℕ) : ℝ) * ((P.k + 1 : ℕ) : ℝ) ^ Qmax P) ^ 2 * (
            Real.exp (2 * lam₁ * T_small - P.p * (1 - Real.exp (-lam₁)) * M_open) +
            2 * (Real.exp 1 * (errOut P F_max / 2) * P.p / (⌈T_small / 2⌉₊ : ℝ)) ^ ⌈T_small / 2⌉₊ +
            2 * Real.exp ((Real.exp lam₂ - 1) * P.p * (MtriBound P F_max : ℝ) - lam₂ * (T_small / 2))) ≤
          1 / (10 * (P.k : ℝ) ^ 2) := by
  intro lam₁ η_s lam₂
  have h1024_gt : Real.exp 1 < 1024 / ε' ^ 2 := by
    have h1 : (1024 : ℝ) ≤ 1024 / ε' ^ 2 := by
      rw [le_div_iff₀ (sq_pos_of_pos hε0)]
      have hsq : ε' ^ 2 ≤ 1 := by nlinarith only [hε0, hε1]
      nlinarith only [hsq]
    linarith only [h1, Real.exp_one_lt_d9]
  have hlam1_gt1 : 1 < lam₁ := (Real.lt_log_iff_exp_lt (by positivity)).mpr h1024_gt
  have hlam1_pos : 0 < lam₁ := by linarith only [hlam1_gt1]
  have hηs_pos : 0 < η_s := by dsimp only [η_s]; positivity
  have hlam2_pos : 0 < lam₂ := by dsimp only [lam₂]; positivity
  have hexp_neg_lam1 : Real.exp (-lam₁) = ε' ^ 2 / 1024 := by
    dsimp only [lam₁]; rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  let C_log : ℝ := max 1000 (max ((10 ^ 14 / ε' ^ 2) ^ 2)
    (max ((3 * 10 ^ 9 * Real.exp (8 / η_s) / η_s) ^ 2) ((Real.exp lam₂ * 10 ^ 9) ^ 2)))
  have hS := asymp_valid_and_scales hε0 hε1
  have hP := asymp_indep_pref_bound hε0 hε1
  have hlog := eventually_lt_log C_log
  have hrp1 := eventually_log_pow_lt_rpow (a := (1 / 20 : ℝ)) (by norm_num) 20 (10 ^ 12 / ε' ^ 2)
  filter_upwards [hS, hP, hlog, hrp1, Filter.eventually_ge_atTop (1000 : ℕ)] with n hSc hPr hlog_big hrp1 hn_ge
  rcases hSc with ⟨hV, _, _, _, _, ⟨hk_lo, hk_hi⟩, _, ⟨hρ_lo, hρ_hi⟩, herrOut_le, herrOpen_le, hMtri_le, _⟩
  intro P F_max T_small a ha b hb D M_open
  rcases hPr a ha b hb with ⟨hPref_le, hPref_simple⟩
  set L_log := Real.log (n : ℝ)
  have hL1000 : 1000 < L_log := lt_of_le_of_lt (le_max_left _ _) hlog_big
  have hL1 : (1 : ℝ) ≤ L_log := by linarith only [hL1000]
  have hLpos : 0 < L_log := by linarith only [hL1000]
  have hn_ge1000 : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith only [hn_ge1000]
  have hn_exp : (n : ℝ) = Real.exp L_log := (Real.exp_log hn_pos).symm
  have he_lt3 : Real.exp 1 < 3 := by linarith only [Real.exp_one_lt_d9]
  have hk1 : 1 ≤ P.k := hV.hk1
  have hk_pos : (0 : ℝ) < (P.k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hk_hi2 : (P.k : ℝ) ≤ 2 * Real.sqrt ((n : ℝ) * L_log) := by
    nlinarith only [hk_hi, hε1, Real.sqrt_nonneg ((n : ℝ) * L_log)]
  have hak : a ≤ P.k := (Finset.mem_Icc.mp ha).2
  have hbk : b ≤ P.k := (Finset.mem_Icc.mp hb).2
  have hLhalf_pos : 0 < L_log ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hLpos _
  have hLhalf_sq : L_log ^ (1 / 2 : ℝ) * L_log ^ (1 / 2 : ℝ) = L_log := by rw [← Real.rpow_add hLpos]; norm_num
  have hLhalf_eq : L_log ^ (1 / 2 : ℝ) = Real.sqrt L_log := (Real.sqrt_eq_rpow L_log).symm
  have hsr_prod : Real.sqrt ((n : ℝ) * L_log) * Real.sqrt (L_log / (n : ℝ)) = L_log := by
    rw [← Real.sqrt_mul (by positivity),
      show (n : ℝ) * L_log * (L_log / (n : ℝ)) = L_log ^ 2 by field_simp [hn_pos.ne'],
      Real.sqrt_sq hLpos.le]
  have hpdef : P.p = Real.sqrt (L_log / (n : ℝ)) / 2 := rfl
  have hpk_lo : ((1 + ε') / 2) * L_log ≤ P.p * (P.k : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hk_lo hV.hp0
    have h2 : P.p * ((1 + ε') * Real.sqrt ((n : ℝ) * L_log)) = ((1 + ε') / 2) * L_log := by
      rw [hpdef, show Real.sqrt (L_log / (n : ℝ)) / 2 * ((1 + ε') * Real.sqrt ((n : ℝ) * L_log)) =
        ((1 + ε') / 2) * (Real.sqrt ((n : ℝ) * L_log) * Real.sqrt (L_log / (n : ℝ))) by ring, hsr_prod]
    linarith only [h1, h2]
  have hpk_hi : P.p * (P.k : ℝ) ≤ L_log := by
    have h1 := mul_le_mul_of_nonneg_left hk_hi2 hV.hp0
    have h2 : P.p * (2 * Real.sqrt ((n : ℝ) * L_log)) = L_log := by
      rw [hpdef, show Real.sqrt (L_log / (n : ℝ)) / 2 * (2 * Real.sqrt ((n : ℝ) * L_log)) =
        Real.sqrt ((n : ℝ) * L_log) * Real.sqrt (L_log / (n : ℝ)) by ring, hsr_prod]
    linarith only [h1, h2]
  have hp_pos : 0 < P.p := by dsimp only [P, mkParams]; positivity
  have hn120_ge1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 20 : ℝ) := Real.one_le_rpow (by linarith only [hn_ge1000]) (by norm_num)
  have hn12_eq : Real.sqrt (n : ℝ) = ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 10 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; congr 1; norm_num
  have hpow10 : (n : ℝ) ^ (1 / 20 : ℝ) ≤ ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 10 := by
    simpa using pow_le_pow_right₀ hn120_ge1 (by omega : 1 ≤ 10)
  have hsr_n_ge : (10 ^ 12 / ε' ^ 2) * L_log ^ 20 < Real.sqrt (n : ℝ) := by
    rw [hn12_eq]; linarith only [hrp1, hpow10]
  have hk_ge_sr : Real.sqrt (n : ℝ) ≤ (P.k : ℝ) := by
    have h1 := Real.sqrt_le_sqrt (by nlinarith only [hn_pos, hL1000] : (n : ℝ) ≤ (n : ℝ) * L_log)
    nlinarith only [h1, hk_lo, hε0, Real.sqrt_nonneg ((n : ℝ) * L_log)]
  set x : ℝ := (a : ℝ) / (P.k : ℝ)
  set y : ℝ := (b : ℝ) / (P.k : ℝ)
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := (div_le_one hk_pos).mpr (by exact_mod_cast hak)
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 := (div_le_one hk_pos).mpr (by exact_mod_cast hbk)
  set Pref : ℝ := (n.choose P.k : ℝ) *
    ((P.m.choose a : ℝ) * ((a : ℝ) / (P.m : ℝ)) ^ P.k) *
    ((P.m.choose b : ℝ) * ((b : ℝ) / (P.m : ℝ)) ^ P.k) *
    (((Qmax P + 1 : ℕ) : ℝ) * ((P.k + 1 : ℕ) : ℝ) ^ Qmax P) ^ 2
  have hexp_neg3 : Real.exp (-(3 * L_log)) ≤ 1 / (30 * (P.k : ℝ) ^ 2) := by
    have heq : Real.exp (-(3 * L_log)) = 1 / (n : ℝ) ^ 3 := by
      rw [show -(3 * L_log) = -L_log + (-L_log + -L_log) by ring, Real.exp_add, Real.exp_add,
        Real.exp_neg, ← hn_exp]; ring
    rw [heq]
    refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
    have hk2 : (P.k : ℝ) ^ 2 ≤ 4 * (n : ℝ) * L_log := by
      have h1 := pow_le_pow_left₀ hk_pos.le hk_hi2 2
      rw [mul_pow, Real.sq_sqrt (by positivity)] at h1; linarith only [h1]
    have h120L := log_pow_lt_rpow_of_big (C := 120) (b := 1) (by omega) (by norm_num) hε0 hε1 hL1 hrp1
    rw [pow_one] at h120L
    have hsr_le_n : Real.sqrt (n : ℝ) ≤ (n : ℝ) := Real.sqrt_le_iff.mpr ⟨hn_pos.le, by nlinarith only [hn_ge1000]⟩
    have h120_le : 120 * L_log ≤ (n : ℝ) ^ 2 := by
      rw [hn12_eq] at hsr_le_n
      nlinarith only [h120L, hpow10, hsr_le_n, hn_ge1000]
    nlinarith only [hk2, h120_le, hn_pos]
  have h2exp : (2 : ℝ) * Real.exp (-(P.k : ℝ) * L_log) ≤ Real.exp (-(3 * L_log)) := by
    have h2_le : (2 : ℝ) ≤ Real.exp L_log := by rw [← hn_exp]; linarith only [hn_ge1000]
    calc (2 : ℝ) * Real.exp (-(P.k : ℝ) * L_log)
        ≤ Real.exp L_log * Real.exp (-(P.k : ℝ) * L_log) :=
          mul_le_mul_of_nonneg_right h2_le (Real.exp_pos _).le
      _ = Real.exp (L_log - (P.k : ℝ) * L_log) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-(3 * L_log)) := by
          refine Real.exp_le_exp.mpr ?_
          have hk4 : (4 : ℝ) ≤ (P.k : ℝ) := by
            have : (4 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.le_sqrt_of_sq_le (by linarith only [hn_ge1000])
            linarith only [this, hk_ge_sr]
          nlinarith only [hk4, hLpos]
  -- Term 1
  have hT1 : Pref * Real.exp (2 * lam₁ * T_small - P.p * (1 - Real.exp (-lam₁)) * M_open) ≤
      1 / (30 * (P.k : ℝ) ^ 2) := by
    have hM_eq : M_open = hRho (D / (P.k : ℝ)) x y * (P.k : ℝ) ^ 2 - 2 * errOpen P F_max := by
      have hk2_nn : (0 : ℝ) ≤ (P.k : ℝ) ^ 2 := sq_nonneg _
      have h1a : max 0 ((a : ℝ) ^ 2 - min (((P.k - b : ℕ) : ℝ) ^ 2) (D * ((P.k - b : ℕ) : ℝ))) =
          (P.k : ℝ) ^ 2 * max 0 (x ^ 2 - min ((1 - y) ^ 2) ((D / (P.k : ℝ)) * (1 - y))) := by
        rw [mul_max_of_nonneg _ _ hk2_nn, mul_zero, mul_sub, mul_min_of_nonneg _ _ hk2_nn]
        congr 1; congr 1
        · dsimp only [x]; field_simp [hk_pos.ne']
        · congr 1
          · rw [Nat.cast_sub hbk]; dsimp only [y]; field_simp [hk_pos.ne']
          · rw [Nat.cast_sub hbk]; dsimp only [y]; field_simp [hk_pos.ne']
      have h1b : max 0 ((b : ℝ) ^ 2 - min (((P.k - a : ℕ) : ℝ) ^ 2) (D * ((P.k - a : ℕ) : ℝ))) =
          (P.k : ℝ) ^ 2 * max 0 (y ^ 2 - min ((1 - x) ^ 2) ((D / (P.k : ℝ)) * (1 - x))) := by
        rw [mul_max_of_nonneg _ _ hk2_nn, mul_zero, mul_sub, mul_min_of_nonneg _ _ hk2_nn]
        congr 1; congr 1
        · dsimp only [y]; field_simp [hk_pos.ne']
        · congr 1
          · rw [Nat.cast_sub hak]; dsimp only [x]; field_simp [hk_pos.ne']
          · rw [Nat.cast_sub hak]; dsimp only [x]; field_simp [hk_pos.ne']
      dsimp only [M_open, hRho]; rw [h1a, h1b]; ring
    have hh_nn : 0 ≤ hRho (D / (P.k : ℝ)) x y := by
      dsimp only [hRho]
      exact add_nonneg (mul_nonneg (by norm_num) (le_max_left _ _)) (mul_nonneg (by norm_num) (le_max_left _ _))
    have hh_le1 : hRho (D / (P.k : ℝ)) x y ≤ 1 := by
      have hDnn : 0 ≤ D := by
        have hF1 := hV.hF1; have hη0 := hV.hη0; have hp0 := hV.hp0
        dsimp only [D]; positivity
      have hmin1 : 0 ≤ min ((1 - x) ^ 2) (D / (P.k : ℝ) * (1 - x)) :=
        le_min (sq_nonneg _) (mul_nonneg (div_nonneg hDnn hk_pos.le) (by linarith only [hx1]))
      have hmin2 : 0 ≤ min ((1 - y) ^ 2) (D / (P.k : ℝ) * (1 - y)) :=
        le_min (sq_nonneg _) (mul_nonneg (div_nonneg hDnn hk_pos.le) (by linarith only [hy1]))
      have hm1 : max 0 (y ^ 2 - min ((1 - x) ^ 2) (D / (P.k : ℝ) * (1 - x))) ≤ 1 :=
        max_le (by norm_num) (by nlinarith only [hy0, hy1, hmin1])
      have hm2 : max 0 (x ^ 2 - min ((1 - y) ^ 2) (D / (P.k : ℝ) * (1 - y))) ≤ 1 :=
        max_le (by norm_num) (by nlinarith only [hx0, hx1, hmin2])
      dsimp only [hRho]; linarith only [hm1, hm2]
    have herrOpen_nn : 0 ≤ errOpen P F_max := by
      have heo := errOut_nonneg P hV
      have hdeg_nn : 0 ≤ (1 + P.η₀) * ((P.m : ℝ) * P.p) :=
        mul_nonneg (by linarith only [hV.hη0]) (mul_nonneg (Nat.cast_nonneg _) hV.hp0)
      have hF1 := hV.hF1
      dsimp only [errOpen]; positivity
    have hM_le_k2 : M_open ≤ (P.k : ℝ) ^ 2 := by rw [hM_eq]; nlinarith only [hh_le1, herrOpen_nn, sq_nonneg (P.k : ℝ)]
    have halg := alg_master_ineq hε0 hε1 hρ_lo hρ_hi hx0 hx1 hy0 hy1
    have hlamT : 2 * lam₁ * T_small = (ε' ^ 2 / 512) * (P.p * (P.k : ℝ)) * (P.k : ℝ) := by
      dsimp only [T_small, η_s]; field_simp [hlam1_pos.ne']; ring
    have hp_err : 2 * P.p * errOpen P F_max ≤ 2 * (10 ^ 10 : ℝ) * (P.k : ℝ) * L_log ^ (1 / 2 : ℝ) := by
      calc 2 * P.p * errOpen P F_max
          ≤ 2 * P.p * ((10 ^ 10 : ℝ) * (P.k : ℝ) ^ 2 / L_log ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left herrOpen_le (by positivity)
        _ = 2 * (10 ^ 10 : ℝ) * (P.p * (P.k : ℝ)) * (P.k : ℝ) / L_log ^ (1 / 2 : ℝ) := by ring
        _ ≤ 2 * (10 ^ 10 : ℝ) * L_log * (P.k : ℝ) / L_log ^ (1 / 2 : ℝ) :=
            div_le_div_of_nonneg_right (by nlinarith only [hpk_hi, hk_pos]) hLhalf_pos.le
        _ = 2 * (10 ^ 10 : ℝ) * (P.k : ℝ) * L_log ^ (1 / 2 : ℝ) := by
            field_simp [hLhalf_pos.ne']
            rw [sq, hLhalf_sq]
    have hLhalf_big : 10 ^ 14 / ε' ^ 2 < L_log ^ (1 / 2 : ℝ) := by
      have hsq : (10 ^ 14 / ε' ^ 2) ^ 2 < L_log :=
        lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hlog_big
      rw [hLhalf_eq]; exact Real.lt_sqrt_of_sq_lt hsq
    have herr_absorb : (3 + 14 * Real.log L_log) + 2 * (10 ^ 10 : ℝ) * L_log ^ (1 / 2 : ℝ) ≤
        (ε' ^ 2 / 128) * L_log := by
      have h1le : (1 : ℝ) ≤ L_log ^ (1 / 2 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
      have hlogL_le : Real.log L_log ≤ 2 * L_log ^ (1 / 2 : ℝ) := by
        have h1 : Real.log (L_log ^ (1 / 2 : ℝ)) ≤ L_log ^ (1 / 2 : ℝ) - 1 := Real.log_le_sub_one_of_pos hLhalf_pos
        rw [Real.log_rpow hLpos] at h1; linarith only [h1]
      have hsum_le : (3 + 14 * Real.log L_log) + 2 * (10 ^ 10 : ℝ) * L_log ^ (1 / 2 : ℝ) ≤
          3 * (10 ^ 10 : ℝ) * L_log ^ (1 / 2 : ℝ) := by linarith only [h1le, hlogL_le]
      have hcmp : 3 * (10 ^ 10 : ℝ) ≤ (ε' ^ 2 / 128) * L_log ^ (1 / 2 : ℝ) := by
        have h1 := (div_lt_iff₀ (sq_pos_of_pos hε0)).mp hLhalf_big; linarith only [h1]
      have hmul := mul_le_mul_of_nonneg_right hcmp hLhalf_pos.le
      nlinarith only [hsum_le, hmul, hLhalf_sq]
    have hexp1_le : (1 / 2 : ℝ) * (x + y - 1) * (P.k : ℝ) * L_log + (3 + 14 * Real.log L_log) * (P.k : ℝ) +
        (2 * lam₁ * T_small - P.p * (1 - Real.exp (-lam₁)) * M_open) ≤ -(3 * L_log) := by
      have hterm_M : 2 * lam₁ * T_small - P.p * (1 - Real.exp (-lam₁)) * M_open ≤
          (3 * ε' ^ 2 / 1024) * (P.k : ℝ) * L_log - ((1 + ε') / 2) * hRho (D / (P.k : ℝ)) x y * (P.k : ℝ) * L_log +
          2 * (10 ^ 10 : ℝ) * (P.k : ℝ) * L_log ^ (1 / 2 : ℝ) := by
        rw [hlamT, hexp_neg_lam1]
        have h1 : (ε' ^ 2 / 512) * (P.p * (P.k : ℝ)) * (P.k : ℝ) ≤ (ε' ^ 2 / 512) * (P.k : ℝ) * L_log := by
          have hm := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpk_hi (show 0 ≤ ε' ^ 2 / 512 by positivity)) hk_pos.le
          linarith only [hm,
            show (ε' ^ 2 / 512) * L_log * (P.k : ℝ) = (ε' ^ 2 / 512) * (P.k : ℝ) * L_log by ring]
        have h2 : P.p * (ε' ^ 2 / 1024) * M_open ≤ (ε' ^ 2 / 1024) * (P.k : ℝ) * L_log := by
          have ha' := mul_le_mul_of_nonneg_left hM_le_k2 hV.hp0
          have hb' : P.p * (P.k : ℝ) ^ 2 ≤ (P.k : ℝ) * L_log := by nlinarith only [hpk_hi, hk_pos]
          nlinarith only [ha', hb', sq_pos_of_pos hε0]
        have h3 : ((1 + ε') / 2) * hRho (D / (P.k : ℝ)) x y * (P.k : ℝ) * L_log ≤
            P.p * (hRho (D / (P.k : ℝ)) x y * (P.k : ℝ) ^ 2) := by
          have hmul := mul_le_mul_of_nonneg_right hpk_lo (mul_nonneg hh_nn hk_pos.le)
          linarith only [hmul,
            show ((1 + ε') / 2) * L_log * (hRho (D / (P.k : ℝ)) x y * (P.k : ℝ)) =
              ((1 + ε') / 2) * hRho (D / (P.k : ℝ)) x y * (P.k : ℝ) * L_log by ring,
            show P.p * (P.k : ℝ) * (hRho (D / (P.k : ℝ)) x y * (P.k : ℝ)) =
              P.p * (hRho (D / (P.k : ℝ)) x y * (P.k : ℝ) ^ 2) by ring]
        have hsplit_M : P.p * (1 - ε' ^ 2 / 1024) * M_open =
            P.p * (hRho (D / (P.k : ℝ)) x y * (P.k : ℝ) ^ 2) - 2 * P.p * errOpen P F_max -
            P.p * (ε' ^ 2 / 1024) * M_open := by
          calc P.p * (1 - ε' ^ 2 / 1024) * M_open
              = P.p * M_open - P.p * (ε' ^ 2 / 1024) * M_open := by ring
            _ = P.p * (hRho (D / (P.k : ℝ)) x y * (P.k : ℝ) ^ 2) - 2 * P.p * errOpen P F_max -
                P.p * (ε' ^ 2 / 1024) * M_open := by rw [hM_eq]; ring
        linarith only [h1, h2, h3, hsplit_M, hp_err]
      have halg_kL : ((1 / 2 : ℝ) * (x + y - 1) - ((1 + ε') / 2) * hRho (D / (P.k : ℝ)) x y) * ((P.k : ℝ) * L_log) ≤
          -(ε' ^ 2 / 32) * ((P.k : ℝ) * L_log) := by
        nlinarith only [halg, mul_pos hk_pos hLpos]
      have habs_k := mul_le_mul_of_nonneg_right herr_absorb hk_pos.le
      have hcomb : (1 / 2 : ℝ) * (x + y - 1) * (P.k : ℝ) * L_log + (3 + 14 * Real.log L_log) * (P.k : ℝ) +
          (2 * lam₁ * T_small - P.p * (1 - Real.exp (-lam₁)) * M_open) ≤ -(ε' ^ 2 / 128) * (P.k : ℝ) * L_log := by
        have hεkL : 0 ≤ ε' ^ 2 * ((P.k : ℝ) * L_log) := by positivity
        linarith only [hterm_M, halg_kL, habs_k, hεkL,
          show ((1 / 2 : ℝ) * (x + y - 1) - ((1 + ε') / 2) * hRho (D / (P.k : ℝ)) x y) * ((P.k : ℝ) * L_log) =
            (1 / 2 : ℝ) * (x + y - 1) * (P.k : ℝ) * L_log - ((1 + ε') / 2) * hRho (D / (P.k : ℝ)) x y * (P.k : ℝ) * L_log by ring,
          show ((3 + 14 * Real.log L_log) + 2 * (10 ^ 10 : ℝ) * L_log ^ (1 / 2 : ℝ)) * (P.k : ℝ) =
            (3 + 14 * Real.log L_log) * (P.k : ℝ) + 2 * (10 ^ 10 : ℝ) * (P.k : ℝ) * L_log ^ (1 / 2 : ℝ) by ring,
          show (3 * ε' ^ 2 / 1024) * (P.k : ℝ) * L_log + -(ε' ^ 2 / 32) * ((P.k : ℝ) * L_log) + (ε' ^ 2 / 128) * L_log * (P.k : ℝ) =
            -(ε' ^ 2 / 128) * (P.k : ℝ) * L_log - (13 / 1024 : ℝ) * (ε' ^ 2 * ((P.k : ℝ) * L_log)) by ring]
      have h3_le : 3 ≤ (ε' ^ 2 / 128) * (P.k : ℝ) := by
        have hL20 : (1 : ℝ) ≤ L_log ^ 20 := one_le_pow₀ hL1
        have h1 : 10 ^ 12 / ε' ^ 2 ≤ (P.k : ℝ) := by
          have hnn : (0 : ℝ) ≤ 10 ^ 12 / ε' ^ 2 := by positivity
          nlinarith only [hsr_n_ge, hk_ge_sr, hL20, hnn]
        have h2 := (div_le_iff₀ (sq_pos_of_pos hε0)).mp h1
        linarith only [h2]
      nlinarith only [hcomb, h3_le, hLpos]
    calc Pref * Real.exp (2 * lam₁ * T_small - P.p * (1 - Real.exp (-lam₁)) * M_open)
        ≤ Real.exp ((1 / 2 : ℝ) * (x + y - 1) * (P.k : ℝ) * L_log + (3 + 14 * Real.log L_log) * (P.k : ℝ)) *
          Real.exp (2 * lam₁ * T_small - P.p * (1 - Real.exp (-lam₁)) * M_open) :=
          mul_le_mul_of_nonneg_right hPref_le (Real.exp_pos _).le
      _ = Real.exp ((1 / 2 : ℝ) * (x + y - 1) * (P.k : ℝ) * L_log + (3 + 14 * Real.log L_log) * (P.k : ℝ) +
            (2 * lam₁ * T_small - P.p * (1 - Real.exp (-lam₁)) * M_open)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-(3 * L_log)) := Real.exp_le_exp.mpr hexp1_le
      _ ≤ 1 / (30 * (P.k : ℝ) ^ 2) := hexp_neg3
  -- Term 2
  have hT2 : Pref * (2 * (Real.exp 1 * (errOut P F_max / 2) * P.p / (⌈T_small / 2⌉₊ : ℝ)) ^ ⌈T_small / 2⌉₊) ≤
      1 / (30 * (P.k : ℝ) ^ 2) := by
    have hTsmall_pos : 0 < T_small := by dsimp only [T_small]; positivity
    have hceil_ge : T_small / 2 ≤ (⌈T_small / 2⌉₊ : ℝ) := Nat.le_ceil _
    have hheo := errOut_nonneg P hV
    have hLhalf_T2 : 3 * 10 ^ 9 * Real.exp (8 / η_s) / η_s < L_log ^ (1 / 2 : ℝ) := by
      have hsq : (3 * 10 ^ 9 * Real.exp (8 / η_s) / η_s) ^ 2 < L_log :=
        lt_of_le_of_lt ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) hlog_big
      rw [hLhalf_eq]; exact Real.lt_sqrt_of_sq_lt hsq
    have hbase : Real.exp 1 * (errOut P F_max / 2) * P.p / (⌈T_small / 2⌉₊ : ℝ) ≤ Real.exp (-(8 / η_s)) := by
      have h1 : Real.exp 1 * (errOut P F_max / 2) * P.p / (⌈T_small / 2⌉₊ : ℝ) ≤
          3 * (10 ^ 9 : ℝ) / (η_s * L_log ^ (1 / 2 : ℝ)) := by
        have hnum := mul_le_mul_of_nonneg_right
          (mul_le_mul he_lt3.le (div_le_div_of_nonneg_right herrOut_le (by norm_num : (0 : ℝ) ≤ 2))
            (div_nonneg hheo (by norm_num)) (by norm_num)) hV.hp0
        calc Real.exp 1 * (errOut P F_max / 2) * P.p / (⌈T_small / 2⌉₊ : ℝ)
            ≤ (3 * ((10 ^ 9 : ℝ) * (P.k : ℝ) ^ 2 / L_log ^ (1 / 2 : ℝ) / 2) * P.p) / (T_small / 2) :=
              div_le_div₀ (by positivity) hnum (by positivity) hceil_ge
          _ = 3 * (10 ^ 9 : ℝ) / (η_s * L_log ^ (1 / 2 : ℝ)) := by
              dsimp only [T_small]; field_simp [hηs_pos.ne', hp_pos.ne', hk_pos.ne', hLhalf_pos.ne']
      have h2 : 3 * (10 ^ 9 : ℝ) / (η_s * L_log ^ (1 / 2 : ℝ)) ≤ Real.exp (-(8 / η_s)) := by
        rw [Real.exp_neg, le_inv_comm₀ (by positivity) (Real.exp_pos _), inv_div, le_div_iff₀ (by positivity)]
        have h3 := (div_lt_iff₀ hηs_pos).mp hLhalf_T2
        linarith only [h3]
      exact h1.trans h2
    have hpow : (Real.exp 1 * (errOut P F_max / 2) * P.p / (⌈T_small / 2⌉₊ : ℝ)) ^ ⌈T_small / 2⌉₊ ≤
        Real.exp (-(2 * (P.k : ℝ) * L_log)) := by
      calc _ ≤ (Real.exp (-(8 / η_s))) ^ ⌈T_small / 2⌉₊ := pow_le_pow_left₀ (by positivity) hbase _
        _ = Real.exp ((⌈T_small / 2⌉₊ : ℝ) * (-(8 / η_s))) := (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp (-(2 * (P.k : ℝ) * L_log)) := by
            refine Real.exp_le_exp.mpr ?_
            have h1 := mul_le_mul_of_nonneg_left hceil_ge (show (0 : ℝ) ≤ 8 / η_s by positivity)
            have h2 : (8 / η_s) * (T_small / 2) = 4 * (P.p * (P.k : ℝ)) * (P.k : ℝ) := by
              dsimp only [T_small]; field_simp [hηs_pos.ne']; ring
            have h3 : (1 / 2 : ℝ) * L_log ≤ P.p * (P.k : ℝ) := by nlinarith only [hpk_lo, hε0, hLpos]
            nlinarith only [h1, h2, h3, hk_pos]
    calc Pref * (2 * (Real.exp 1 * (errOut P F_max / 2) * P.p / (⌈T_small / 2⌉₊ : ℝ)) ^ ⌈T_small / 2⌉₊)
        ≤ Real.exp ((P.k : ℝ) * L_log) * (2 * Real.exp (-(2 * (P.k : ℝ) * L_log))) :=
          mul_le_mul hPref_simple (mul_le_mul_of_nonneg_left hpow (by norm_num)) (by positivity) (Real.exp_pos _).le
      _ = 2 * Real.exp (-(P.k : ℝ) * L_log) := by
          rw [show Real.exp ((P.k : ℝ) * L_log) * (2 * Real.exp (-(2 * (P.k : ℝ) * L_log))) =
            2 * (Real.exp ((P.k : ℝ) * L_log) * Real.exp (-(2 * (P.k : ℝ) * L_log))) by ring,
            ← Real.exp_add]; congr 2; ring
      _ ≤ Real.exp (-(3 * L_log)) := h2exp
      _ ≤ 1 / (30 * (P.k : ℝ) ^ 2) := hexp_neg3
  -- Term 3
  have hT3 : Pref * (2 * Real.exp ((Real.exp lam₂ - 1) * P.p * (MtriBound P F_max : ℝ) - lam₂ * (T_small / 2))) ≤
      1 / (30 * (P.k : ℝ) ^ 2) := by
    have hLhalf_T3 : Real.exp lam₂ * 10 ^ 9 < L_log ^ (1 / 2 : ℝ) := by
      have hsq : (Real.exp lam₂ * 10 ^ 9) ^ 2 < L_log :=
        lt_of_le_of_lt ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) hlog_big
      rw [hLhalf_eq]; exact Real.lt_sqrt_of_sq_lt hsq
    have hexp3 : (Real.exp lam₂ - 1) * P.p * (MtriBound P F_max : ℝ) - lam₂ * (T_small / 2) ≤
        -(2 * (P.k : ℝ) * L_log) := by
      have hlam2T : lam₂ * (T_small / 2) = 10 * (P.p * (P.k : ℝ)) * (P.k : ℝ) := by
        dsimp only [lam₂, T_small]; field_simp [hηs_pos.ne']; ring
      have hle1 : Real.exp lam₂ - 1 ≤ Real.exp lam₂ := by linarith
      have h1 : (Real.exp lam₂ - 1) * P.p * (MtriBound P F_max : ℝ) ≤
          Real.exp lam₂ * P.p * ((10 ^ 9 : ℝ) * (P.k : ℝ) ^ 2 / L_log ^ (1 / 2 : ℝ)) :=
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle1 hV.hp0) (Nat.cast_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hMtri_le (by positivity))
      have h2 : Real.exp lam₂ * P.p * ((10 ^ 9 : ℝ) * (P.k : ℝ) ^ 2 / L_log ^ (1 / 2 : ℝ)) ≤
          (P.p * (P.k : ℝ)) * (P.k : ℝ) := by
        have hfrac : Real.exp lam₂ * 10 ^ 9 / L_log ^ (1 / 2 : ℝ) ≤ 1 := (div_le_one hLhalf_pos).mpr hLhalf_T3.le
        have hrew : Real.exp lam₂ * P.p * ((10 ^ 9 : ℝ) * (P.k : ℝ) ^ 2 / L_log ^ (1 / 2 : ℝ)) =
            (Real.exp lam₂ * 10 ^ 9 / L_log ^ (1 / 2 : ℝ)) * ((P.p * (P.k : ℝ)) * (P.k : ℝ)) := by ring
        rw [hrew]; nlinarith only [hfrac, mul_nonneg (mul_nonneg hV.hp0 hk_pos.le) hk_pos.le]
      have h3 : (1 / 2 : ℝ) * L_log ≤ P.p * (P.k : ℝ) := by nlinarith only [hpk_lo, hε0, hLpos]
      have h4 : 2 * (P.k : ℝ) * L_log ≤ 9 * (P.p * (P.k : ℝ)) * (P.k : ℝ) := by nlinarith only [h3, hk_pos, hLpos]
      linarith only [hlam2T, h1, h2, h4]
    calc Pref * (2 * Real.exp ((Real.exp lam₂ - 1) * P.p * (MtriBound P F_max : ℝ) - lam₂ * (T_small / 2)))
        ≤ Real.exp ((P.k : ℝ) * L_log) * (2 * Real.exp (-(2 * (P.k : ℝ) * L_log))) :=
          mul_le_mul hPref_simple (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp3) (by norm_num))
            (by positivity) (Real.exp_pos _).le
      _ = 2 * Real.exp (-(P.k : ℝ) * L_log) := by
          rw [show Real.exp ((P.k : ℝ) * L_log) * (2 * Real.exp (-(2 * (P.k : ℝ) * L_log))) =
            2 * (Real.exp ((P.k : ℝ) * L_log) * Real.exp (-(2 * (P.k : ℝ) * L_log))) by ring,
            ← Real.exp_add]; congr 2; ring
      _ ≤ Real.exp (-(3 * L_log)) := h2exp
      _ ≤ 1 / (30 * (P.k : ℝ) ^ 2) := hexp_neg3
  have hdist : Pref * (Real.exp (2 * lam₁ * T_small - P.p * (1 - Real.exp (-lam₁)) * M_open) +
      2 * (Real.exp 1 * (errOut P F_max / 2) * P.p / (⌈T_small / 2⌉₊ : ℝ)) ^ ⌈T_small / 2⌉₊ +
      2 * Real.exp ((Real.exp lam₂ - 1) * P.p * (MtriBound P F_max : ℝ) - lam₂ * (T_small / 2))) =
      Pref * Real.exp (2 * lam₁ * T_small - P.p * (1 - Real.exp (-lam₁)) * M_open) +
      Pref * (2 * (Real.exp 1 * (errOut P F_max / 2) * P.p / (⌈T_small / 2⌉₊ : ℝ)) ^ ⌈T_small / 2⌉₊) +
      Pref * (2 * Real.exp ((Real.exp lam₂ - 1) * P.p * (MtriBound P F_max : ℝ) - lam₂ * (T_small / 2))) := by ring
  rw [show (n.choose P.k : ℝ) * ((P.m.choose a : ℝ) * ((a : ℝ) / (P.m : ℝ)) ^ P.k) *
      ((P.m.choose b : ℝ) * ((b : ℝ) / (P.m : ℝ)) ^ P.k) *
      (((Qmax P + 1 : ℕ) : ℝ) * ((P.k + 1 : ℕ) : ℝ) ^ Qmax P) ^ 2 * _ = Pref * _ from rfl, hdist]
  have h30 : 1 / (30 * (P.k : ℝ) ^ 2) + 1 / (30 * (P.k : ℝ) ^ 2) + 1 / (30 * (P.k : ℝ) ^ 2) =
      1 / (10 * (P.k : ℝ) ^ 2) := by field_simp [hk_pos.ne']; ring
  linarith only [hT1, hT2, hT3, h30]

/-- Sharp triangle-free independence number bound (Hefty–Horn–King–Pfender 2025):
for every `ε > 0`, for all sufficiently large `n`, there exists a triangle-free graph on `Fin n`
with independence number `< (1 + ε) * √(n * log n)`. -/
lemma hhkp_indep_bound :
    ∀ ε > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧
        ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) →
          (I.card : ℝ) < (1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
  intro ε hε
  set ε' : ℝ := min (ε / 2) (1 / 4)
  have hε0 : 0 < ε' := lt_min (by linarith only [hε]) (by norm_num)
  have hε1 : ε' ≤ 1 / 4 := min_le_right _ _
  have hε_half : 2 * ε' ≤ ε := by have := min_le_left (ε / 2) (1 / 4 : ℝ); linarith only [this]
  set lam₁ : ℝ := Real.log (1024 / ε' ^ 2)
  set η_s : ℝ := ε' ^ 2 / (1024 * lam₁)
  set lam₂ : ℝ := 20 / η_s
  have hlam1_pos : 0 < lam₁ := by
    have h1 : (1 : ℝ) < 1024 / ε' ^ 2 := by
      rw [one_lt_div (sq_pos_of_pos hε0)]
      have hsq : ε' ^ 2 ≤ 1 := by nlinarith only [hε0, hε1]
      linarith only [hsq]
    exact Real.log_pos h1
  have hηs_pos : 0 < η_s := by dsimp only [η_s]; positivity
  have hlam2_pos : 0 < lam₂ := by dsimp only [lam₂]; positivity
  have hEv : ∀ᶠ n : ℕ in Filter.atTop,
      ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧
        ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) →
          (I.card : ℝ) < (1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
    have hS := asymp_valid_and_scales hε0 hε1
    have hG := asymp_goodGraph_bound hε0 hε1
    have hI := asymp_indep_bound hε0 hε1
    have hlog := eventually_lt_log (max 1000 (1000 / ε' ^ 2))
    filter_upwards [hS, hG, hI, hlog, Filter.eventually_ge_atTop (1000 : ℕ)] with n hSc hGg hIn hlog_big hn_ge
    rcases hSc with ⟨hV, _, ⟨_, hm_hi⟩, ⟨hnm_lo, _⟩, _, ⟨_, hk_hi⟩, _, _, _, _, _, _⟩
    set P := mkParams ε' n
    set L_log := Real.log (n : ℝ)
    set F_max := (1 + P.η₀) * ((n : ℝ) / (P.m : ℝ))
    set T_small := η_s * P.p * (P.k : ℝ) ^ 2
    have hL1000 : 1000 < L_log := lt_of_le_of_lt (le_max_left _ _) hlog_big
    have hLpos : 0 < L_log := by linarith only [hL1000]
    have hn_ge1000 : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
    have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith only [hn_ge1000]
    have hn_exp : (n : ℝ) = Real.exp L_log := (Real.exp_log hn_pos).symm
    have hη1 : P.η₀ ≤ 1 / 2 := by dsimp only [P, mkParams]; linarith only [hε1]
    have hk1 : 1 ≤ P.k := hV.hk1
    have hk_pos : (0 : ℝ) < (P.k : ℝ) := Nat.cast_pos.mpr (by omega)
    have hp_pos : 0 < P.p := by dsimp only [P, mkParams]; positivity
    have hTsmall_pos : 0 < T_small := by dsimp only [T_small]; positivity
    have hfib_tail : 2 * (P.m : ℝ) * Real.exp (-(P.η₀ ^ 2 / 3) * ((n : ℝ) / (P.m : ℝ))) ≤ 1 / 10 := by
      have hm_le_n : (P.m : ℝ) ≤ (n : ℝ) := by
        have hL5 : (2 : ℝ) ≤ L_log ^ 5 := by
          have : (1000 : ℝ) ^ 5 ≤ L_log ^ 5 := pow_le_pow_left₀ (by norm_num) hL1000.le 5
          linarith only [this]
        calc (P.m : ℝ) ≤ 2 * (n : ℝ) / L_log ^ 5 := hm_hi
          _ = (2 / L_log ^ 5) * (n : ℝ) := by ring
          _ ≤ 1 * (n : ℝ) := mul_le_mul_of_nonneg_right ((div_le_one (by positivity)).mpr hL5) hn_pos.le
          _ = (n : ℝ) := one_mul _
      have hexp_ge : 2 * L_log ≤ (P.η₀ ^ 2 / 3) * ((n : ℝ) / (P.m : ℝ)) := by
        have hηsq : P.η₀ ^ 2 / 3 = ε' ^ 2 / 768 := by dsimp only [P, mkParams]; ring
        rw [hηsq]
        have hL_eps : 1000 / ε' ^ 2 < L_log := lt_of_le_of_lt (le_max_right _ _) hlog_big
        have hε2L : 1000 ≤ ε' ^ 2 * L_log := by
          have := (div_lt_iff₀ (sq_pos_of_pos hε0)).mp hL_eps; linarith only [this]
        have hL3 : (1000 : ℝ) ^ 3 ≤ L_log ^ 3 := pow_le_pow_left₀ (by norm_num) hL1000.le 3
        have hprod : 2 * L_log ≤ (ε' ^ 2 / 768) * (L_log ^ 5 / 2) := by
          have hrew : (ε' ^ 2 / 768) * (L_log ^ 5 / 2) = (ε' ^ 2 * L_log) * L_log ^ 3 * L_log / 1536 := by ring
          rw [hrew]
          have h1 := mul_le_mul hε2L hL3 (by positivity) (by positivity)
          nlinarith only [h1, hLpos]
        exact hprod.trans (mul_le_mul_of_nonneg_left hnm_lo (by positivity))
      calc 2 * (P.m : ℝ) * Real.exp (-(P.η₀ ^ 2 / 3) * ((n : ℝ) / (P.m : ℝ)))
          ≤ 2 * (n : ℝ) * Real.exp (-(2 * L_log)) :=
            mul_le_mul (by linarith only [hm_le_n]) (Real.exp_le_exp.mpr (by linarith only [hexp_ge]))
              (Real.exp_pos _).le (by positivity)
        _ = 2 / (n : ℝ) := by
            rw [show -(2 * L_log) = -L_log + -L_log by ring, Real.exp_add, Real.exp_neg, ← hn_exp]
            field_simp [hn_pos.ne']
        _ ≤ 1 / 10 := by
            rw [div_le_div_iff₀ hn_pos (by norm_num : (0 : ℝ) < 10)]; linarith only [hn_ge1000]
    have htot : 2 * (P.m : ℝ) * Real.exp (-(P.η₀ ^ 2 / 3) * ((n : ℝ) / (P.m : ℝ))) +
        2 * (1 / 10 : ℝ) + ((P.k : ℝ) ^ 2) * (1 / (10 * (P.k : ℝ) ^ 2)) < 1 := by
      have hcancel : (P.k : ℝ) ^ 2 * (1 / (10 * (P.k : ℝ) ^ 2)) = 1 / 10 := by field_simp [hk_pos.ne']
      linarith only [hfib_tail, hcancel]
    obtain ⟨G, htri, hind⟩ := exists_triangleFree_indep_lt P hV hη1 rfl hTsmall_pos hlam1_pos hlam2_pos
      hGg hIn htot
    refine ⟨G, htri, fun I hI => ?_⟩
    have hlt_k : (I.card : ℝ) < (P.k : ℝ) := by exact_mod_cast hind I hI
    have hk_le_eps : (P.k : ℝ) ≤ (1 + ε) * Real.sqrt ((n : ℝ) * L_log) :=
      hk_hi.trans (mul_le_mul_of_nonneg_right (by linarith only [hε_half]) (Real.sqrt_nonneg _))
    exact lt_of_lt_of_le hlt_k hk_le_eps
  exact Filter.eventually_atTop.mp hEv

end AsymptoticsAndMain
end Erdos165LowerProof

theorem OMA.solution : type_of% @Erdos165.erdos_165.variants.lower :=
  Erdos165LowerProof.lower_of_indep_bound Erdos165LowerProof.hhkp_indep_bound
