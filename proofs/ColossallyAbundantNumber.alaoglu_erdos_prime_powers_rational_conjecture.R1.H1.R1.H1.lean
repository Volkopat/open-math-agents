import OMAReductions.R_ColossallyAbundantNumber_alaoglu_erdos_prime_powers_rational_conjecture_R1_H1_R1
import Mathlib

-- Step ColossallyAbundantNumber.alaoglu_erdos_prime_powers_rational_conjecture.R1.H1.R1.H1: hypothesis H1 of reduction ColossallyAbundantNumber.alaoglu_erdos_prime_powers_rational_conjecture.R1.H1.R1
-- Credit: @Mapika
-- H1 := ∀ a z : ℂ, z ≠ 0 → IsAlgebraic ℚ a → (∀ q : ℚ, a ≠ (q : ℂ)) →     IsAlgebraic ℚ (Complex.exp z) → Transcendental ℚ (Complex.exp (a * z))

/-!
The Gelfond-Schneider theorem (exponential form).

Target (step `ColossallyAbundantNumber.alaoglu_erdos_prime_powers_rational_conjecture.R1.H1.R1.H1`):
for all complex `a z`, `z ≠ 0`, `a` algebraic and not rational, `exp z` algebraic imply
`exp (a * z)` transcendental. With `α = exp z`, `β = a`, `γ = exp (a z)` this is
Gelfond-Schneider (Gelfond 1934, Schneider 1934) for an arbitrary determination `z` of the
logarithm of `α`.

Prior formalization: Karatarakis and Wiedijk, A formalization of the Gelfond-Schneider theorem,
arXiv:2603.24823, on a public mathlib branch that is not part of the Mathlib used here. This
file is an independent development: it follows Gelfond's method as outlined in sections 2 and 3
of that paper's prose (their Lean code was not consulted), with the bookkeeping redone so that
every bound is a natural power of one free parameter `t`.

Parameters. `K` a number field containing `α β γ`, `h = [K : ℚ]`, `m = 2h + 2`, a free natural
number `t`, `q = 2mt`, `n = 2mt^2` (so `q^2 = 2mn` and `q ≤ n`).

Chain (the constants `C₁ C₄ C₅` are at least one and do not depend on `t`):
* `aux_coeffs` (Siegel's lemma): integral `η`, not all zero, house at most `C₁^n q^(n+1)`,
  with `S r a = 0` for `r < n`, `1 ≤ a ≤ m`.
* `exists_S_ne_zero` (Vandermonde): some `S r 1 ≠ 0` with `r < q^2`. Take `r` minimal with
  `S r a₀ ≠ 0` for some `1 ≤ a₀ ≤ m`; then `n ≤ r < q^2`.
* `lower_bound` (norm of a nonzero algebraic integer): `1 / (C₄^r t^((2r+3)(h-1))) ≤ ‖σ (S r a₀)‖`.
* `upper_bound` (maximum principle, through `exists_factor`, `schwarz_multi`,
  `iteratedDeriv_R`): `‖σ (S r a₀)‖ t^(mr) ≤ C₅^r t^(3r+3)`.
* `no_large_t`: with `m = 2h+2` and `r ≥ 2mt^2` these two are incompatible for large `t`.

Written by a team of agents from one blueprint: the lemmas between the comment lines naming
them were proved separately against fixed statements and assembled mechanically.
-/

namespace OMA.GelfondSchneider

open NumberField

/-- The algebraic number `S(r, a) = ∑ η(k,l) ((k+1) + (l+1) β)^r α^((k+1) a) γ^((l+1) a)`,
the sum over `k l < q`. It equals `z^(-r)` times the `r`-th derivative at `a` of the
auxiliary function `R` below. -/
noncomputable def S {K : Type} [Field K] (α β γ : K) (q : ℕ) (η : Fin q → Fin q → K)
    (r a : ℕ) : K :=
  ∑ k : Fin q, ∑ l : Fin q,
    η k l * ((((k : ℕ) : K) + 1) + (((l : ℕ) : K) + 1) * β) ^ r
      * α ^ (((k : ℕ) + 1) * a) * γ ^ (((l : ℕ) + 1) * a)

/-- The auxiliary function `R(x) = ∑ σ(η(k,l)) exp(((k+1) + (l+1) σβ) z x)`. -/
noncomputable def R {K : Type} [Field K] (σ : K →+* ℂ) (β : K) (z : ℂ) (q : ℕ)
    (η : Fin q → Fin q → K) (x : ℂ) : ℂ :=
  ∑ k : Fin q, ∑ l : Fin q,
    σ (η k l) * Complex.exp (((((k : ℕ) : ℂ) + 1) + (((l : ℕ) : ℂ) + 1) * σ β) * z * x)

/-- Three algebraic complex numbers lie in the image of one number
field: `K = ℚ(α, β, γ)` inside `ℂ`, `σ` the inclusion. -/
lemma exists_numberField (α β γ : ℂ) (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β)
    (hγ : IsAlgebraic ℚ γ) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (σ : K →+* ℂ) (α' β' γ' : K),
      σ α' = α ∧ σ β' = β ∧ σ γ' = γ := by
  have hfd : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({α, β, γ} : Set ℂ)) := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    rcases hx with rfl | rfl | rfl
    exacts [hα.isIntegral, hβ.isIntegral, hγ.isIntegral]
  have hnf : NumberField (IntermediateField.adjoin ℚ ({α, β, γ} : Set ℂ)) :=
    { to_charZero := inferInstance, to_finiteDimensional := hfd }
  refine ⟨IntermediateField.adjoin ℚ ({α, β, γ} : Set ℂ), inferInstance, hnf,
    algebraMap _ ℂ, ⟨α, IntermediateField.subset_adjoin ℚ _ (by simp)⟩,
    ⟨β, IntermediateField.subset_adjoin ℚ _ (by simp)⟩,
    ⟨γ, IntermediateField.subset_adjoin ℚ _ (by simp)⟩, rfl, rfl, rfl⟩

/-- A positive natural number `c` with `c α`, `c β`, `c γ` algebraic
integers. Shared black box for `aux_coeffs` and `lower_bound`. -/
lemma exists_common_denominator (K : Type) [Field K] [NumberField K] (α β γ : K) :
    ∃ c : ℕ, 0 < c ∧ IsIntegral ℤ ((c : K) * α) ∧ IsIntegral ℤ ((c : K) * β) ∧
      IsIntegral ℤ ((c : K) * γ) := by
  classical
  have key : ∀ x : K, ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : K) * x) := by
    intro x
    have hx : IsAlgebraic ℤ x :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic x)
    obtain ⟨y, hy0, hy⟩ := hx.exists_integral_multiple
    refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩
    rw [zsmul_eq_mul] at hy
    rcases Int.natAbs_eq y with h | h
    · have e := congrArg (Int.cast (R := K)) h
      rw [Int.cast_natCast] at e
      rw [← e]; exact hy
    · have e := congrArg (Int.cast (R := K)) h
      rw [Int.cast_neg, Int.cast_natCast] at e
      have e' : ((y.natAbs : ℕ) : K) = -(y : K) := by rw [e, neg_neg]
      rw [e', neg_mul]; exact hy.neg
  obtain ⟨d₁, h1, i1⟩ := key α
  obtain ⟨d₂, h2, i2⟩ := key β
  obtain ⟨d₃, h3, i3⟩ := key γ
  refine ⟨d₁ * d₂ * d₃, by positivity, ?_, ?_, ?_⟩
  · have e : ((d₁ * d₂ * d₃ : ℕ) : K) * α = ((d₂ * d₃ : ℕ) : K) * ((d₁ : K) * α) := by
      push_cast; ring
    rw [e]; exact (isIntegral_natCast (R := ℤ) (B := K) (d₂ * d₃)).mul i1
  · have e : ((d₁ * d₂ * d₃ : ℕ) : K) * β = ((d₁ * d₃ : ℕ) : K) * ((d₂ : K) * β) := by
      push_cast; ring
    rw [e]; exact (isIntegral_natCast (R := ℤ) (B := K) (d₁ * d₃)).mul i2
  · have e : ((d₁ * d₂ * d₃ : ℕ) : K) * γ = ((d₁ * d₂ : ℕ) : K) * ((d₃ : K) * γ) := by
      push_cast; ring
    rw [e]; exact (isIntegral_natCast (R := ℤ) (B := K) (d₁ * d₂)).mul i3

/-- Siegel's lemma over a number field with a constant that depends
only on `K`: Mathlib states `NumberField.house.exists_ne_zero_int_vec_house_le` with a private
constant, which cannot be named; here it is captured by unification so that it can be chosen
before the parameter `t`. Nothing is known about the sign or size of `c` (in Mathlib it is
nonnegative, but that fact is private too): use `c * (c * x) ≤ (c ^ 2 + 1) * x` for `x ≥ 0`. -/
lemma siegel_uniform (K : Type) [Field K] [NumberField K] :
    ∃ c : ℝ, ∀ (p q : ℕ) (a : Matrix (Fin p) (Fin q) (𝓞 K)) (A : ℝ), 0 < p → p < q → a ≠ 0 →
      (∀ k l, house ((algebraMap (𝓞 K) K) (a k l)) ≤ A) →
      ∃ ξ : Fin q → 𝓞 K, ξ ≠ 0 ∧ a.mulVec ξ = 0 ∧
        ∀ l, house (ξ l).1 ≤ c * ((c * q * A) ^ ((p : ℝ) / (q - p))) := by
  classical
  refine ⟨?c, fun p q a A h0p hpq ha habs => ?main⟩
  case main =>
    exact NumberField.house.exists_ne_zero_int_vec_house_le K a ha h0p hpq (Fintype.card_fin q)
      habs (Fintype.card_fin p)

-- term_integral
section TI

lemma term_integral (K : Type) [Field K] [NumberField K] (α β γ : K) (c : ℕ)
    (hα : IsIntegral ℤ ((c : K) * α)) (hβ : IsIntegral ℤ ((c : K) * β))
    (hγ : IsIntegral ℤ ((c : K) * γ)) (u v r e₁ e₂ N : ℕ) (h1 : e₁ ≤ N) (h2 : e₂ ≤ N) :
    IsIntegral ℤ ((c : K) ^ (r + 2 * N) * ((((u : K) + (v : K) * β) ^ r) * α ^ e₁ * γ ^ e₂)) := by
  have hN : r + 2 * N = r + ((N - e₁) + e₁) + ((N - e₂) + e₂) := by omega
  have e : (c : K) ^ (r + 2 * N) * ((((u : K) + (v : K) * β) ^ r) * α ^ e₁ * γ ^ e₂) =
      (((c : K) * (u : K) + (v : K) * ((c : K) * β)) ^ r) *
        ((c : K) ^ (N - e₁) * ((c : K) * α) ^ e₁) *
        ((c : K) ^ (N - e₂) * ((c : K) * γ) ^ e₂) := by
    have hx : (c : K) * (u : K) + (v : K) * ((c : K) * β) = (c : K) * ((u : K) + (v : K) * β) := by
      ring
    rw [hx, hN, pow_add, pow_add, pow_add, pow_add, mul_pow, mul_pow, mul_pow]
    ring
  rw [e]
  have hc : IsIntegral ℤ (c : K) := isIntegral_natCast (R := ℤ) (B := K) c
  have hu : IsIntegral ℤ (u : K) := isIntegral_natCast (R := ℤ) (B := K) u
  have hv : IsIntegral ℤ (v : K) := isIntegral_natCast (R := ℤ) (B := K) v
  exact (((hc.mul hu).add (hv.mul hβ)).pow r).mul ((hc.pow _).mul (hα.pow _)) |>.mul
    ((hc.pow _).mul (hγ.pow _))

end TI

-- term_house
section TH

lemma TH_house_natCast (K : Type) [Field K] [NumberField K] (u : ℕ) :
    house (u : K) = (u : ℝ) := by
  have h := house_nat_mul (1 : K) u
  rw [mul_one] at h
  rw [h]
  have h1 : house (1 : K) = 1 := by
    have := house_intCast (K := K) 1
    simpa using this
  rw [h1, mul_one]

lemma TH_house_pow_le_max (K : Type) [Field K] [NumberField K] (x : K) (e : ℕ) :
    house (x ^ e) ≤ (max 1 (house x)) ^ e :=
  (house_pow_le x e).trans
    (pow_le_pow_left₀ (house_nonneg x) (le_max_right _ _) e)

lemma term_house (K : Type) [Field K] [NumberField K] (α β γ : K) (u v r e₁ e₂ : ℕ) :
    house ((((u : K) + (v : K) * β) ^ r) * α ^ e₁ * γ ^ e₂) ≤
      ((u : ℝ) + (v : ℝ) * house β) ^ r * (max 1 (house α)) ^ e₁ * (max 1 (house γ)) ^ e₂ := by
  have hb : house ((u : K) + (v : K) * β) ≤ (u : ℝ) + (v : ℝ) * house β := by
    calc house ((u : K) + (v : K) * β) ≤ house (u : K) + house ((v : K) * β) :=
          house_add_le _ _
      _ = (u : ℝ) + (v : ℝ) * house β := by
          rw [TH_house_natCast, house_nat_mul]
  have h0 : house (((u : K) + (v : K) * β) ^ r) ≤ ((u : ℝ) + (v : ℝ) * house β) ^ r :=
    (house_pow_le _ r).trans (pow_le_pow_left₀ (house_nonneg _) hb r)
  have hα := TH_house_pow_le_max K α e₁
  have hγ := TH_house_pow_le_max K γ e₂
  calc house ((((u : K) + (v : K) * β) ^ r) * α ^ e₁ * γ ^ e₂)
      ≤ house ((((u : K) + (v : K) * β) ^ r) * α ^ e₁) * house (γ ^ e₂) := house_mul_le _ _
    _ ≤ (house (((u : K) + (v : K) * β) ^ r) * house (α ^ e₁)) * house (γ ^ e₂) :=
        mul_le_mul_of_nonneg_right (house_mul_le _ _) (house_nonneg _)
    _ ≤ (((u : ℝ) + (v : ℝ) * house β) ^ r * (max 1 (house α)) ^ e₁) *
          (max 1 (house γ)) ^ e₂ := by
        have hu0 : 0 ≤ ((u : ℝ) + (v : ℝ) * house β) ^ r :=
          (house_nonneg _).trans h0
        have hab := mul_le_mul h0 hα (house_nonneg _) hu0
        have hab0 : 0 ≤ ((u : ℝ) + (v : ℝ) * house β) ^ r * (max 1 (house α)) ^ e₁ :=
          mul_nonneg hu0 (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
        exact mul_le_mul hab hγ (house_nonneg _) hab0

end TH

-- aux_coeffs
section AC

/-- The coefficient of the unknown `η k l` in the equation `S r a = 0`. -/
noncomputable def AC_coef {K : Type} [Field K] (α β γ : K) (k l r a : ℕ) : K :=
  ((((k : K) + 1) + ((l : K) + 1) * β) ^ r) * α ^ ((k + 1) * a) * γ ^ ((l + 1) * a)

lemma AC_S_eq {K : Type} [Field K] (α β γ : K) (q : ℕ) (η : Fin q → Fin q → K) (r a : ℕ) :
    S α β γ q η r a =
      ∑ k : Fin q, ∑ l : Fin q, η k l * AC_coef α β γ (k : ℕ) (l : ℕ) r a := by
  unfold S AC_coef
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

lemma AC_coef_eq {K : Type} [Field K] (α β γ : K) (k l r a : ℕ) :
    AC_coef α β γ k l r a =
      ((((k + 1 : ℕ) : K) + ((l + 1 : ℕ) : K) * β) ^ r) * α ^ ((k + 1) * a)
        * γ ^ ((l + 1) * a) := by
  unfold AC_coef
  push_cast
  rfl

/-- The cleared coefficient is an algebraic integer. -/
lemma AC_coef_integral (K : Type) [Field K] [NumberField K] (α β γ : K) (c : ℕ)
    (hα : IsIntegral ℤ ((c : K) * α)) (hβ : IsIntegral ℤ ((c : K) * β))
    (hγ : IsIntegral ℤ ((c : K) * γ)) (q n m k l r a : ℕ) (hk : k < q) (hl : l < q)
    (hr : r < n) (ha : a ≤ m) :
    IsIntegral ℤ (((c ^ (n + 2 * (m * q)) : ℕ) : K) * AC_coef α β γ k l r a) := by
  have h1 : (k + 1) * a ≤ m * q := by
    calc (k + 1) * a ≤ q * m := Nat.mul_le_mul hk ha
      _ = m * q := Nat.mul_comm _ _
  have h2 : (l + 1) * a ≤ m * q := by
    calc (l + 1) * a ≤ q * m := Nat.mul_le_mul hl ha
      _ = m * q := Nat.mul_comm _ _
  have key := term_integral K α β γ c hα hβ hγ (k + 1) (l + 1) r ((k + 1) * a) ((l + 1) * a)
    (m * q) h1 h2
  have e : ((c ^ (n + 2 * (m * q)) : ℕ) : K) * AC_coef α β γ k l r a =
      ((c ^ (n - r) : ℕ) : K) * ((c : K) ^ (r + 2 * (m * q)) *
        (((((k + 1 : ℕ) : K) + ((l + 1 : ℕ) : K) * β) ^ r) * α ^ ((k + 1) * a)
          * γ ^ ((l + 1) * a))) := by
    have hpow : (c : K) ^ (n + 2 * (m * q)) = (c : K) ^ (n - r) * (c : K) ^ (r + 2 * (m * q)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [AC_coef_eq, Nat.cast_pow, Nat.cast_pow, hpow]
    ring
  rw [e]
  exact (isIntegral_natCast (R := ℤ) (B := K) (c ^ (n - r))).mul key

/-- The house of the cleared coefficient. -/
lemma AC_coef_house (K : Type) [Field K] [NumberField K] (α β γ : K) (c q n m k l r a : ℕ)
    (hk : k < q) (hl : l < q) (hr : r < n) (ha : a ≤ m) :
    house (((c ^ (n + 2 * (m * q)) : ℕ) : K) * AC_coef α β γ k l r a) ≤
      (c : ℝ) ^ (n + 2 * (m * q)) * (((q : ℝ) * (1 + house β)) ^ (n - 1) *
        (max 1 (house α) * max 1 (house γ)) ^ (q * m)) := by
  have hb : 0 ≤ house β := house_nonneg β
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have : 1 ≤ q := by omega
    exact_mod_cast this
  have hk' : ((k + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hk
  have hl' : ((l + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hl
  rw [house_nat_mul, AC_coef_eq, Nat.cast_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (term_house K α β γ (k + 1) (l + 1) r _ _).trans ?_
  rw [mul_pow (max 1 (house α)), mul_assoc]
  have hbase0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + ((l + 1 : ℕ) : ℝ) * house β := by positivity
  have hbase : ((k + 1 : ℕ) : ℝ) + ((l + 1 : ℕ) : ℝ) * house β ≤ (q : ℝ) * (1 + house β) := by
    have := mul_le_mul_of_nonneg_right hl' hb
    linarith
  have hone : (1 : ℝ) ≤ (q : ℝ) * (1 + house β) := by
    have : (1 : ℝ) * 1 ≤ (q : ℝ) * (1 + house β) :=
      mul_le_mul hq1 (by linarith) zero_le_one (by linarith)
    linarith
  have e1 : (((k + 1 : ℕ) : ℝ) + ((l + 1 : ℕ) : ℝ) * house β) ^ r ≤
      ((q : ℝ) * (1 + house β)) ^ (n - 1) :=
    (pow_le_pow_left₀ hbase0 hbase r).trans (pow_le_pow_right₀ hone (by omega))
  have e2 : (max 1 (house α)) ^ ((k + 1) * a) ≤ (max 1 (house α)) ^ (q * m) :=
    pow_le_pow_right₀ (le_max_left _ _) (Nat.mul_le_mul hk ha)
  have e3 : (max 1 (house γ)) ^ ((l + 1) * a) ≤ (max 1 (house γ)) ^ (q * m) :=
    pow_le_pow_right₀ (le_max_left _ _) (Nat.mul_le_mul hl ha)
  have p1 : (0 : ℝ) ≤ max 1 (house α) := le_trans zero_le_one (le_max_left _ _)
  have p2 : (0 : ℝ) ≤ max 1 (house γ) := le_trans zero_le_one (le_max_left _ _)
  exact mul_le_mul e1 (mul_le_mul e2 e3 (by positivity) (by positivity)) (by positivity)
    (by positivity)

/-- The size bookkeeping: the bound given by Siegel's lemma is at most `C₁ ^ n * q ^ (n + 1)`. -/
lemma AC_arith (c₁ b G : ℝ) (c m q n : ℕ) (hc : 0 < c) (hb : 0 ≤ b) (hG : 1 ≤ G)
    (hq : 0 < q) (hn : 0 < n) (hqn : q ≤ n) :
    (c₁ ^ 2 + 1) * (((q * q : ℕ) : ℝ) * ((c : ℝ) ^ (n + 2 * (m * q)) *
      (((q : ℝ) * (1 + b)) ^ (n - 1) * G ^ (q * m)))) ≤
      ((c₁ ^ 2 + 1) * (c : ℝ) ^ (2 * m + 1) * (1 + b) * G ^ m) ^ n * (q : ℝ) ^ (n + 1) := by
  have hD : (1 : ℝ) ≤ c₁ ^ 2 + 1 := by nlinarith [sq_nonneg c₁]
  have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hB : (1 : ℝ) ≤ 1 + b := by linarith
  have hqR : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have s1 : c₁ ^ 2 + 1 ≤ (c₁ ^ 2 + 1) ^ n := le_self_pow₀ hD (by omega)
  have s2 : (c : ℝ) ^ (n + 2 * (m * q)) ≤ ((c : ℝ) ^ (2 * m + 1)) ^ n := by
    rw [← pow_mul]
    refine pow_le_pow_right₀ hcR ?_
    have : m * q ≤ m * n := Nat.mul_le_mul_left m hqn
    calc n + 2 * (m * q) ≤ n + 2 * (m * n) := by omega
      _ = (2 * m + 1) * n := by ring
  have s3 : (1 + b) ^ (n - 1) ≤ (1 + b) ^ n := pow_le_pow_right₀ hB (by omega)
  have s4 : G ^ (q * m) ≤ (G ^ m) ^ n := by
    rw [← pow_mul]
    refine pow_le_pow_right₀ hG ?_
    calc q * m ≤ n * m := Nat.mul_le_mul_right m hqn
      _ = m * n := Nat.mul_comm _ _
  have s5 : ((q * q : ℕ) : ℝ) * (q : ℝ) ^ (n - 1) = (q : ℝ) ^ (n + 1) := by
    have : n + 1 = (n - 1) + 2 := by omega
    rw [this, pow_add]
    push_cast
    ring
  have lhs : (c₁ ^ 2 + 1) * (((q * q : ℕ) : ℝ) * ((c : ℝ) ^ (n + 2 * (m * q)) *
      (((q : ℝ) * (1 + b)) ^ (n - 1) * G ^ (q * m)))) =
      ((c₁ ^ 2 + 1) * (c : ℝ) ^ (n + 2 * (m * q)) * (1 + b) ^ (n - 1) * G ^ (q * m)) *
        (((q * q : ℕ) : ℝ) * (q : ℝ) ^ (n - 1)) := by
    rw [mul_pow]
    ring
  rw [lhs, s5, mul_pow, mul_pow, mul_pow]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have p1 : (0 : ℝ) ≤ c₁ ^ 2 + 1 := by linarith
  have p2 : (0 : ℝ) ≤ (c : ℝ) := by linarith
  have p3 : (0 : ℝ) ≤ 1 + b := by linarith
  have p4 : (0 : ℝ) ≤ G := by linarith
  exact mul_le_mul (mul_le_mul (mul_le_mul s1 s2 (by positivity) (by positivity)) s3
    (by positivity) (by positivity)) s4 (by positivity) (by positivity)

/-- The general form: `q` and `n` are any positive naturals with `q ≤ n` and `q ^ 2 = 2 m n`. -/
lemma AC_main (K : Type) [Field K] [NumberField K] (α β γ : K) (hα0 : α ≠ 0) (hγ0 : γ ≠ 0)
    (c : ℕ) (hc : 0 < c) (hα : IsIntegral ℤ ((c : K) * α)) (hβ : IsIntegral ℤ ((c : K) * β))
    (hγ : IsIntegral ℤ ((c : K) * γ)) (c₁ : ℝ)
    (hsieg : ∀ (p q : ℕ) (a : Matrix (Fin p) (Fin q) (𝓞 K)) (A : ℝ), 0 < p → p < q → a ≠ 0 →
      (∀ k l, house ((algebraMap (𝓞 K) K) (a k l)) ≤ A) →
      ∃ ξ : Fin q → 𝓞 K, ξ ≠ 0 ∧ a.mulVec ξ = 0 ∧
        ∀ l, house (ξ l).1 ≤ c₁ * ((c₁ * q * A) ^ ((p : ℝ) / (q - p))))
    (m q n : ℕ) (hm : 0 < m) (hq : 0 < q) (hn : 0 < n) (hqn : q ≤ n)
    (hQ : q * q = 2 * (n * m)) :
    ∃ η : Fin q → Fin q → K,
      (∀ k l, IsIntegral ℤ (η k l)) ∧ (∃ k l, η k l ≠ 0) ∧
      (∀ k l, house (η k l) ≤
        ((c₁ ^ 2 + 1) * (c : ℝ) ^ (2 * m + 1) * (1 + house β) *
          (max 1 (house α) * max 1 (house γ)) ^ m) ^ n * (q : ℝ) ^ (n + 1)) ∧
      ∀ r < n, ∀ a, 1 ≤ a → a ≤ m → S α β γ q η r a = 0 := by
  classical
  -- the matrix: rows are the equations `(r, a - 1)`, columns are the unknowns `(k, l)`
  let M : Matrix (Fin (n * m)) (Fin (q * q)) (𝓞 K) := fun i j =>
    ⟨((c ^ (n + 2 * (m * q)) : ℕ) : K) *
        AC_coef α β γ ((finProdFinEquiv.symm j).1 : ℕ) ((finProdFinEquiv.symm j).2 : ℕ)
          ((finProdFinEquiv.symm i).1 : ℕ) (((finProdFinEquiv.symm i).2 : ℕ) + 1),
      AC_coef_integral K α β γ c hα hβ hγ q n m _ _ _ _ (finProdFinEquiv.symm j).1.2
        (finProdFinEquiv.symm j).2.2 (finProdFinEquiv.symm i).1.2
        (finProdFinEquiv.symm i).2.2⟩
  have hMval : ∀ i j, algebraMap (𝓞 K) K (M i j) = ((c ^ (n + 2 * (m * q)) : ℕ) : K) *
        AC_coef α β γ ((finProdFinEquiv.symm j).1 : ℕ) ((finProdFinEquiv.symm j).2 : ℕ)
          ((finProdFinEquiv.symm i).1 : ℕ) (((finProdFinEquiv.symm i).2 : ℕ) + 1) :=
    fun i j => rfl
  have hcK : ((c ^ (n + 2 * (m * q)) : ℕ) : K) ≠ 0 := by
    have : c ^ (n + 2 * (m * q)) ≠ 0 := pow_ne_zero _ (by omega)
    exact_mod_cast this
  have hp : 0 < n * m := Nat.mul_pos hn hm
  have hpq : n * m < q * q := by omega
  have hM : M ≠ 0 := by
    intro h
    have h1 : algebraMap (𝓞 K) K (M (finProdFinEquiv (⟨0, hn⟩, ⟨0, hm⟩))
        (finProdFinEquiv (⟨0, hq⟩, ⟨0, hq⟩))) = 0 := by
      rw [h]; simp
    rw [hMval] at h1
    simp only [Equiv.symm_apply_apply, AC_coef] at h1
    have h2 : (((0 : ℕ) : K) + 1 + (((0 : ℕ) : K) + 1) * β) ^ 0 * α ^ ((0 + 1) * (0 + 1)) *
        γ ^ ((0 + 1) * (0 + 1)) ≠ 0 := by
      simp [hα0, hγ0]
    exact mul_ne_zero hcK h2 h1
  have hA : ∀ i j, house (algebraMap (𝓞 K) K (M i j)) ≤
      (c : ℝ) ^ (n + 2 * (m * q)) * (((q : ℝ) * (1 + house β)) ^ (n - 1) *
        (max 1 (house α) * max 1 (house γ)) ^ (q * m)) := by
    intro i j
    rw [hMval]
    exact AC_coef_house K α β γ c q n m _ _ _ _ (finProdFinEquiv.symm j).1.2
      (finProdFinEquiv.symm j).2.2 (finProdFinEquiv.symm i).1.2 (finProdFinEquiv.symm i).2.2
  obtain ⟨ξ, hξ0, hξ, hξh⟩ := hsieg (n * m) (q * q) M _ hp hpq hM hA
  refine ⟨fun k l => algebraMap (𝓞 K) K (ξ (finProdFinEquiv (k, l))), ?_, ?_, ?_, ?_⟩
  · intro k l
    exact RingOfIntegers.isIntegral_coe _
  · have : ∃ j, ξ j ≠ 0 := by
      by_contra hcon
      exact hξ0 (funext fun j => not_not.mp fun h => hcon ⟨j, h⟩)
    obtain ⟨j, hj⟩ := this
    refine ⟨(finProdFinEquiv.symm j).1, (finProdFinEquiv.symm j).2, ?_⟩
    intro h0
    apply hj
    apply RingOfIntegers.ext
    have h0' : algebraMap (𝓞 K) K (ξ (finProdFinEquiv
        ((finProdFinEquiv.symm j).1, (finProdFinEquiv.symm j).2))) = 0 := h0
    rw [Prod.mk.eta, Equiv.apply_symm_apply] at h0'
    exact h0'.trans (map_zero _).symm
  · intro k l
    refine (hξh (finProdFinEquiv (k, l))).trans ?_
    have hexp : ((n * m : ℕ) : ℝ) / (((q * q : ℕ) : ℝ) - ((n * m : ℕ) : ℝ)) = 1 := by
      have h0 : ((n * m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
      have h2 : ((q * q : ℕ) : ℝ) = 2 * ((n * m : ℕ) : ℝ) := by exact_mod_cast hQ
      rw [h2]
      field_simp
      ring
    rw [hexp, Real.rpow_one]
    have hApos : 0 ≤ (c : ℝ) ^ (n + 2 * (m * q)) * (((q : ℝ) * (1 + house β)) ^ (n - 1) *
        (max 1 (house α) * max 1 (house γ)) ^ (q * m)) := by
      have := house_nonneg β
      positivity
    have hG : (1 : ℝ) ≤ max 1 (house α) * max 1 (house γ) := by
      have a1 : (1 : ℝ) ≤ max 1 (house α) := le_max_left _ _
      have a2 : (1 : ℝ) ≤ max 1 (house γ) := le_max_left _ _
      nlinarith
    refine le_trans ?_ (AC_arith c₁ (house β) _ c m q n hc (house_nonneg β) hG hq hn hqn)
    have hX : 0 ≤ ((q * q : ℕ) : ℝ) * ((c : ℝ) ^ (n + 2 * (m * q)) *
        (((q : ℝ) * (1 + house β)) ^ (n - 1) *
          (max 1 (house α) * max 1 (house γ)) ^ (q * m))) :=
      mul_nonneg (Nat.cast_nonneg _) hApos
    nlinarith [sq_nonneg c₁, hX]
  · intro r hr a ha1 ham
    have hrow := congrFun hξ (finProdFinEquiv (⟨r, hr⟩, ⟨a - 1, by omega⟩))
    have hrow' := congrArg (algebraMap (𝓞 K) K) hrow
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hMval, Equiv.symm_apply_apply,
      Pi.zero_apply, map_zero] at hrow'
    have ha' : a - 1 + 1 = a := by omega
    rw [ha'] at hrow'
    rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type] at hrow'
    simp only [Equiv.symm_apply_apply] at hrow'
    have hsum : ((c ^ (n + 2 * (m * q)) : ℕ) : K) * S α β γ q
        (fun k l => algebraMap (𝓞 K) K (ξ (finProdFinEquiv (k, l)))) r a = 0 := by
      rw [AC_S_eq, Finset.mul_sum]
      rw [← hrow']
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    exact (mul_eq_zero.mp hsum).resolve_left hcK

/-- LEMMA 1 (auxiliary coefficients, Siegel). -/
lemma aux_coeffs (K : Type) [Field K] [NumberField K] (α β γ : K) (m : ℕ) (hm : 0 < m)
    (hα0 : α ≠ 0) (hγ0 : γ ≠ 0) :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ t : ℕ, 1 ≤ t →
      ∃ η : Fin (2 * m * t) → Fin (2 * m * t) → K,
        (∀ k l, IsIntegral ℤ (η k l)) ∧ (∃ k l, η k l ≠ 0) ∧
        (∀ k l, house (η k l) ≤
          C₁ ^ (2 * m * t ^ 2) * ((2 * m * t : ℕ) : ℝ) ^ (2 * m * t ^ 2 + 1)) ∧
        ∀ r < 2 * m * t ^ 2, ∀ a, 1 ≤ a → a ≤ m → S α β γ (2 * m * t) η r a = 0 := by
  obtain ⟨c, hc, hα, hβ, hγ⟩ := exists_common_denominator K α β γ
  obtain ⟨c₁, hsieg⟩ := siegel_uniform K
  refine ⟨(c₁ ^ 2 + 1) * (c : ℝ) ^ (2 * m + 1) * (1 + house β) *
    (max 1 (house α) * max 1 (house γ)) ^ m, ?_, ?_⟩
  · have hD : (1 : ℝ) ≤ c₁ ^ 2 + 1 := by nlinarith [sq_nonneg c₁]
    have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
    have hB : (1 : ℝ) ≤ 1 + house β := by linarith [house_nonneg β]
    have a1 : (1 : ℝ) ≤ max 1 (house α) := le_max_left _ _
    have a2 : (1 : ℝ) ≤ max 1 (house γ) := le_max_left _ _
    have hG : (1 : ℝ) ≤ max 1 (house α) * max 1 (house γ) := by nlinarith
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hD (one_le_pow₀ hcR)) hB) (one_le_pow₀ hG)
  · intro t ht
    have hq : 0 < 2 * m * t := by positivity
    have hn : 0 < 2 * m * t ^ 2 := by positivity
    have hqn : 2 * m * t ≤ 2 * m * t ^ 2 := by
      refine Nat.mul_le_mul_left _ ?_
      calc t = t * 1 := (Nat.mul_one t).symm
        _ ≤ t * t := Nat.mul_le_mul_left t ht
        _ = t ^ 2 := (sq t).symm
    have hQ : 2 * m * t * (2 * m * t) = 2 * (2 * m * t ^ 2 * m) := by ring
    exact AC_main K α β γ hα0 hγ0 c hc hα hβ hγ c₁ hsieg m (2 * m * t) (2 * m * t ^ 2) hm hq hn
      hqn hQ

end AC

-- exists_S_ne_zero
section NZ

/-- The nodes `(k+1) + (l+1) β` are pairwise distinct when `β` is irrational. -/
lemma NZ_nodes_injective (K : Type) [Field K] [CharZero K] (β : K)
    (hirr : ∀ x : ℚ, β ≠ (x : K)) (q : ℕ) :
    Function.Injective (fun p : Fin q × Fin q =>
      (((p.1 : ℕ) : K) + 1) + (((p.2 : ℕ) : K) + 1) * β) := by
  rintro ⟨k, l⟩ ⟨k', l'⟩ h
  simp only at h
  by_cases hl : (l : ℕ) = (l' : ℕ)
  · rw [hl] at h
    have hk : ((k : ℕ) : K) = ((k' : ℕ) : K) := by linear_combination h
    have hk' : (k : ℕ) = (k' : ℕ) := Nat.cast_injective hk
    exact Prod.ext (Fin.ext hk') (Fin.ext hl)
  · exfalso
    have hne : ((l' : ℕ) : K) - ((l : ℕ) : K) ≠ 0 := by
      intro h0
      apply hl
      exact (Nat.cast_injective (R := K) (sub_eq_zero.mp h0)).symm
    apply hirr ((((k : ℕ) : ℚ) - ((k' : ℕ) : ℚ)) / (((l' : ℕ) : ℚ) - ((l : ℕ) : ℚ)))
    push_cast
    field_simp
    linear_combination -h

lemma exists_S_ne_zero (K : Type) [Field K] [NumberField K] (α β γ : K) (hα0 : α ≠ 0)
    (hγ0 : γ ≠ 0) (hirr : ∀ x : ℚ, β ≠ (x : K)) (q : ℕ) (η : Fin q → Fin q → K)
    (hη : ∃ k l, η k l ≠ 0) :
    ∃ r < q ^ 2, S α β γ q η r 1 ≠ 0 := by
  by_contra H
  push Not at H
  obtain ⟨k₀, l₀, h₀⟩ := hη
  let e : Fin q × Fin q ≃ Fin (q * q) := finProdFinEquiv
  let x : Fin q × Fin q → K := fun p =>
    (((p.1 : ℕ) : K) + 1) + (((p.2 : ℕ) : K) + 1) * β
  let w : Fin q × Fin q → K := fun p =>
    η p.1 p.2 * α ^ ((p.1 : ℕ) + 1) * γ ^ ((p.2 : ℕ) + 1)
  have hx : Function.Injective x := NZ_nodes_injective K β hirr q
  have hf : Function.Injective (x ∘ e.symm) := hx.comp e.symm.injective
  have hv : (w ∘ e.symm) = 0 := by
    refine Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf ?_
    intro i
    have hi : (i : ℕ) < q ^ 2 := by rw [sq]; exact i.isLt
    rw [← H i hi, S]
    rw [show (∑ j : Fin (q * q), (w ∘ e.symm) j * (x ∘ e.symm) j ^ (i : ℕ))
        = ∑ p : Fin q × Fin q, w p * x p ^ (i : ℕ) from
      (e.symm.sum_comp (fun p => w p * x p ^ (i : ℕ)))]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    simp only [w, x, mul_one]
    ring
  have h1 : w (k₀, l₀) = 0 := by
    have := congrFun hv (e (k₀, l₀))
    simpa using this
  simp only [w] at h1
  exact h₀ (by
    rcases mul_eq_zero.mp h1 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd (pow_eq_zero_iff (by omega) |>.mp h) hα0
    · exact absurd (pow_eq_zero_iff (by omega) |>.mp h) hγ0)

end NZ

-- lower_bound
section LB

/-- The norm of a nonzero algebraic integer has absolute value at least one. -/
lemma LB_one_le_norm (K : Type) [Field K] [NumberField K] (x : K) (hx : IsIntegral ℤ x)
    (hx0 : x ≠ 0) : 1 ≤ ‖Algebra.norm ℚ x‖ := by
  have hint : IsIntegral ℤ (Algebra.norm ℚ x) := Algebra.isIntegral_norm ℚ hx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact hx0 (Algebra.norm_eq_zero_iff.mp hy.symm)
  rw [← hy, eq_intCast, ← Rat.norm_cast_real, Rat.cast_intCast, Real.norm_eq_abs,
    ← Int.cast_abs]
  exact_mod_cast Int.one_le_abs hy0

/-- Integrality of `c^(r + 2 q m) S(r, a)` for integral `η` and `a ≤ m`. -/
lemma LB_integral (K : Type) [Field K] [NumberField K] (α β γ : K) (c : ℕ)
    (hα : IsIntegral ℤ ((c : K) * α)) (hβ : IsIntegral ℤ ((c : K) * β))
    (hγ : IsIntegral ℤ ((c : K) * γ)) (q m : ℕ) (η : Fin q → Fin q → K)
    (hη : ∀ k l, IsIntegral ℤ (η k l)) (r a : ℕ) (ham : a ≤ m) :
    IsIntegral ℤ ((c : K) ^ (r + 2 * (q * m)) * S α β γ q η r a) := by
  unfold S
  rw [Finset.mul_sum]
  refine IsIntegral.sum _ fun k _ => ?_
  rw [Finset.mul_sum]
  refine IsIntegral.sum _ fun l _ => ?_
  have h1 : ((k : ℕ) + 1) * a ≤ q * m := Nat.mul_le_mul k.2 ham
  have h2 : ((l : ℕ) + 1) * a ≤ q * m := Nat.mul_le_mul l.2 ham
  have key := term_integral K α β γ c hα hβ hγ ((k : ℕ) + 1) ((l : ℕ) + 1) r
    (((k : ℕ) + 1) * a) (((l : ℕ) + 1) * a) (q * m) h1 h2
  have e : (c : K) ^ (r + 2 * (q * m)) *
      (η k l * ((((k : ℕ) : K) + 1) + (((l : ℕ) : K) + 1) * β) ^ r
        * α ^ (((k : ℕ) + 1) * a) * γ ^ (((l : ℕ) + 1) * a)) =
      η k l * ((c : K) ^ (r + 2 * (q * m)) *
        ((((((k : ℕ) + 1 : ℕ) : K) + ((((l : ℕ) + 1 : ℕ) : K)) * β) ^ r)
          * α ^ (((k : ℕ) + 1) * a) * γ ^ (((l : ℕ) + 1) * a))) := by
    push_cast
    ring
  rw [e]
  exact (hη k l).mul key

/-- House of `S(r, a)` when every `η k l` has house at most `H` and `a ≤ m`. -/
lemma LB_house_S (K : Type) [Field K] [NumberField K] (α β γ : K) (q m : ℕ)
    (η : Fin q → Fin q → K) (H : ℝ) (hH : ∀ k l, house (η k l) ≤ H) (r a : ℕ) (ham : a ≤ m) :
    house (S α β γ q η r a) ≤
      (q : ℝ) ^ 2 * (H * (((q : ℝ) * (1 + house β)) ^ r * (max 1 (house α)) ^ (q * m)
        * (max 1 (house γ)) ^ (q * m))) := by
  have hterm : ∀ k l : Fin q,
      house (η k l * ((((k : ℕ) : K) + 1) + (((l : ℕ) : K) + 1) * β) ^ r
        * α ^ (((k : ℕ) + 1) * a) * γ ^ (((l : ℕ) + 1) * a)) ≤
      H * (((q : ℝ) * (1 + house β)) ^ r * (max 1 (house α)) ^ (q * m)
        * (max 1 (house γ)) ^ (q * m)) := by
    intro k l
    have h1 : ((k : ℕ) + 1) * a ≤ q * m := Nat.mul_le_mul k.2 ham
    have h2 : ((l : ℕ) + 1) * a ≤ q * m := Nat.mul_le_mul l.2 ham
    have hk : (((k : ℕ) + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast k.2
    have hl : (((l : ℕ) + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast l.2
    have hb : 0 ≤ house β := house_nonneg β
    have key := term_house K α β γ ((k : ℕ) + 1) ((l : ℕ) + 1) r
      (((k : ℕ) + 1) * a) (((l : ℕ) + 1) * a)
    have e : η k l * ((((k : ℕ) : K) + 1) + (((l : ℕ) : K) + 1) * β) ^ r
        * α ^ (((k : ℕ) + 1) * a) * γ ^ (((l : ℕ) + 1) * a) =
      η k l * (((((((k : ℕ) + 1 : ℕ) : K) + ((((l : ℕ) + 1 : ℕ) : K)) * β) ^ r)
          * α ^ (((k : ℕ) + 1) * a) * γ ^ (((l : ℕ) + 1) * a))) := by
      push_cast
      ring
    rw [e]
    have hbase : ((((k : ℕ) + 1 : ℕ) : ℝ) + (((l : ℕ) + 1 : ℕ) : ℝ) * house β) ≤
        (q : ℝ) * (1 + house β) := by
      have : (((l : ℕ) + 1 : ℕ) : ℝ) * house β ≤ (q : ℝ) * house β :=
        mul_le_mul_of_nonneg_right hl hb
      linarith
    have hbase0 : 0 ≤ ((((k : ℕ) + 1 : ℕ) : ℝ) + (((l : ℕ) + 1 : ℕ) : ℝ) * house β) := by
      positivity
    have hA : (max 1 (house α)) ^ (((k : ℕ) + 1) * a) ≤ (max 1 (house α)) ^ (q * m) :=
      pow_le_pow_right₀ (le_max_left _ _) h1
    have hB : (max 1 (house γ)) ^ (((l : ℕ) + 1) * a) ≤ (max 1 (house γ)) ^ (q * m) :=
      pow_le_pow_right₀ (le_max_left _ _) h2
    have hrest : ((((k : ℕ) + 1 : ℕ) : ℝ) + (((l : ℕ) + 1 : ℕ) : ℝ) * house β) ^ r
        * (max 1 (house α)) ^ (((k : ℕ) + 1) * a) * (max 1 (house γ)) ^ (((l : ℕ) + 1) * a) ≤
        ((q : ℝ) * (1 + house β)) ^ r * (max 1 (house α)) ^ (q * m)
          * (max 1 (house γ)) ^ (q * m) := by
      gcongr
    calc house (η k l * (((((((k : ℕ) + 1 : ℕ) : K) + ((((l : ℕ) + 1 : ℕ) : K)) * β) ^ r)
          * α ^ (((k : ℕ) + 1) * a) * γ ^ (((l : ℕ) + 1) * a))))
        ≤ house (η k l) * house (((((((k : ℕ) + 1 : ℕ) : K) + ((((l : ℕ) + 1 : ℕ) : K)) * β) ^ r)
          * α ^ (((k : ℕ) + 1) * a) * γ ^ (((l : ℕ) + 1) * a))) := house_mul_le _ _
      _ ≤ H * (((q : ℝ) * (1 + house β)) ^ r * (max 1 (house α)) ^ (q * m)
          * (max 1 (house γ)) ^ (q * m)) :=
        mul_le_mul (hH k l) (key.trans hrest) (house_nonneg _)
          ((house_nonneg _).trans (hH k l))
  unfold S
  calc house (∑ k : Fin q, ∑ l : Fin q,
        η k l * ((((k : ℕ) : K) + 1) + (((l : ℕ) : K) + 1) * β) ^ r
          * α ^ (((k : ℕ) + 1) * a) * γ ^ (((l : ℕ) + 1) * a))
      ≤ ∑ k : Fin q, house (∑ l : Fin q,
        η k l * ((((k : ℕ) : K) + 1) + (((l : ℕ) : K) + 1) * β) ^ r
          * α ^ (((k : ℕ) + 1) * a) * γ ^ (((l : ℕ) + 1) * a)) :=
        house_sum_le_sum_house _ _
    _ ≤ ∑ _k : Fin q, ∑ _l : Fin q, H * (((q : ℝ) * (1 + house β)) ^ r
          * (max 1 (house α)) ^ (q * m) * (max 1 (house γ)) ^ (q * m)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine (house_sum_le_sum_house _ _).trans ?_
        exact Finset.sum_le_sum fun l _ => hterm k l
    _ = (q : ℝ) ^ 2 * (H * (((q : ℝ) * (1 + house β)) ^ r * (max 1 (house α)) ^ (q * m)
        * (max 1 (house γ)) ^ (q * m))) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The real arithmetic: the house bound is at most `D^r t^(2r+3)`. -/
lemma LB_arith (C₁ P A B : ℝ) (hC₁ : 1 ≤ C₁) (hP : 1 ≤ P) (hA : 1 ≤ A) (hB : 1 ≤ B)
    (m t r : ℕ) (hm : 0 < m) (ht : 1 ≤ t) (hr : 2 * m * t ^ 2 ≤ r) :
    ((2 * m * t : ℕ) : ℝ) ^ 2 * ((C₁ ^ (2 * m * t ^ 2) *
        ((2 * m * t : ℕ) : ℝ) ^ (2 * m * t ^ 2 + 1)) *
        ((((2 * m * t : ℕ) : ℝ) * P) ^ r * A ^ (2 * m * t * m) * B ^ (2 * m * t * m))) ≤
      (((2 * m : ℕ) : ℝ) ^ 5 * C₁ * P * (A * B) ^ m) ^ r * (t : ℝ) ^ (2 * r + 3) := by
  have htt : t ≤ t ^ 2 := by nlinarith
  have hqn : 2 * m * t ≤ 2 * m * t ^ 2 := Nat.mul_le_mul_left _ htt
  have hqr : 2 * m * t ≤ r := hqn.trans hr
  have hr1 : 1 ≤ r := by
    have : 1 ≤ 2 * m * t := by
      have := Nat.mul_le_mul (Nat.mul_le_mul (le_refl 2) hm) ht
      omega
    omega
  have hQ : (1 : ℝ) ≤ ((2 * m * t : ℕ) : ℝ) := by
    have : 1 ≤ 2 * m * t := by
      have := Nat.mul_le_mul (Nat.mul_le_mul (le_refl 2) hm) ht
      omega
    exact_mod_cast this
  have hM : (1 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by
    have : 1 ≤ 2 * m := by omega
    exact_mod_cast this
  have hT : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hexp : 2 * m * t * m ≤ m * r := by
    calc 2 * m * t * m = m * (2 * m * t) := by ring
      _ ≤ m * r := Nat.mul_le_mul_left _ hqr
  have e1 : C₁ ^ (2 * m * t ^ 2) ≤ C₁ ^ r := pow_le_pow_right₀ hC₁ hr
  have e2 : ((2 * m * t : ℕ) : ℝ) ^ (2 * m * t ^ 2 + 1) ≤ ((2 * m * t : ℕ) : ℝ) ^ (r + 1) :=
    pow_le_pow_right₀ hQ (by omega)
  have e3 : A ^ (2 * m * t * m) ≤ A ^ (m * r) := pow_le_pow_right₀ hA hexp
  have e4 : B ^ (2 * m * t * m) ≤ B ^ (m * r) := pow_le_pow_right₀ hB hexp
  have e5 : ((2 * m : ℕ) : ℝ) ^ (2 * r + 3) ≤ ((2 * m : ℕ) : ℝ) ^ (5 * r) :=
    pow_le_pow_right₀ hM (by omega)
  have hQ0 : (0 : ℝ) ≤ ((2 * m * t : ℕ) : ℝ) := by positivity
  have hP0 : (0 : ℝ) ≤ P := by linarith
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hB0 : (0 : ℝ) ≤ B := by linarith
  have hC0 : (0 : ℝ) ≤ C₁ := by linarith
  calc ((2 * m * t : ℕ) : ℝ) ^ 2 * ((C₁ ^ (2 * m * t ^ 2) *
        ((2 * m * t : ℕ) : ℝ) ^ (2 * m * t ^ 2 + 1)) *
        ((((2 * m * t : ℕ) : ℝ) * P) ^ r * A ^ (2 * m * t * m) * B ^ (2 * m * t * m)))
      ≤ ((2 * m * t : ℕ) : ℝ) ^ 2 * ((C₁ ^ r * ((2 * m * t : ℕ) : ℝ) ^ (r + 1)) *
        ((((2 * m * t : ℕ) : ℝ) * P) ^ r * A ^ (m * r) * B ^ (m * r))) := by
        gcongr
    _ = ((2 * m : ℕ) : ℝ) ^ (2 * r + 3) *
        (C₁ ^ r * P ^ r * (A ^ (m * r) * B ^ (m * r)) * (t : ℝ) ^ (2 * r + 3)) := by
        push_cast
        ring
    _ ≤ ((2 * m : ℕ) : ℝ) ^ (5 * r) *
        (C₁ ^ r * P ^ r * (A ^ (m * r) * B ^ (m * r)) * (t : ℝ) ^ (2 * r + 3)) := by
        gcongr
    _ = (((2 * m : ℕ) : ℝ) ^ 5 * C₁ * P * (A * B) ^ m) ^ r * (t : ℝ) ^ (2 * r + 3) := by
        ring

lemma lower_bound (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (α β γ : K) (m : ℕ)
    (hm : 0 < m) (C₁ : ℝ) (hC₁ : 1 ≤ C₁) :
    ∃ C₄ : ℝ, 1 ≤ C₄ ∧ ∀ t : ℕ, 1 ≤ t → ∀ η : Fin (2 * m * t) → Fin (2 * m * t) → K,
      (∀ k l, IsIntegral ℤ (η k l)) →
      (∀ k l, house (η k l) ≤
        C₁ ^ (2 * m * t ^ 2) * ((2 * m * t : ℕ) : ℝ) ^ (2 * m * t ^ 2 + 1)) →
      ∀ r a, 2 * m * t ^ 2 ≤ r → 1 ≤ a → a ≤ m → S α β γ (2 * m * t) η r a ≠ 0 →
        (C₄ ^ r * (t : ℝ) ^ ((2 * r + 3) * (Module.finrank ℚ K - 1)))⁻¹ ≤
          ‖σ (S α β γ (2 * m * t) η r a)‖ := by
  obtain ⟨c, hc0, hcα, hcβ, hcγ⟩ := exists_common_denominator K α β γ
  have hpos : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
  obtain ⟨h', hh'⟩ : ∃ h', Module.finrank ℚ K = h' + 1 := ⟨Module.finrank ℚ K - 1, by omega⟩
  have hc1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc0
  have hP : (1 : ℝ) ≤ 1 + house β := by linarith [house_nonneg β]
  have hA : (1 : ℝ) ≤ max 1 (house α) := le_max_left _ _
  have hB : (1 : ℝ) ≤ max 1 (house γ) := le_max_left _ _
  have hM : (1 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by
    have : 1 ≤ 2 * m := by omega
    exact_mod_cast this
  have hD : (1 : ℝ) ≤ ((2 * m : ℕ) : ℝ) ^ 5 * C₁ * (1 + house β) *
      (max 1 (house α) * max 1 (house γ)) ^ m :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM) hC₁) hP)
      (one_le_pow₀ (one_le_mul_of_one_le_of_one_le hA hB))
  refine ⟨(c : ℝ) ^ ((h' + 1) * (2 * m + 1)) *
    (((2 * m : ℕ) : ℝ) ^ 5 * C₁ * (1 + house β) *
      (max 1 (house α) * max 1 (house γ)) ^ m) ^ h',
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hc1) (one_le_pow₀ hD), ?_⟩
  intro t ht η hint hhouse r a hr ha1 ham hS
  rw [hh', Nat.add_sub_cancel]
  -- natural number bookkeeping
  have htt : t ≤ t ^ 2 := by nlinarith
  have hk : r + 2 * (2 * m * t * m) ≤ (2 * m + 1) * r := by
    have h1 : 2 * m * t ≤ 2 * m * t ^ 2 := Nat.mul_le_mul_left _ htt
    have h2 : 2 * m * (2 * m * t) ≤ 2 * m * r := Nat.mul_le_mul_left _ (h1.trans hr)
    calc r + 2 * (2 * m * t * m) = r + 2 * m * (2 * m * t) := by ring
      _ ≤ r + 2 * m * r := by omega
      _ = (2 * m + 1) * r := by ring
  -- the algebraic integer
  have hcK : (c : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hx_int := LB_integral K α β γ c hcα hcβ hcγ (2 * m * t) m η hint r a ham
  have hx0 : (c : K) ^ (r + 2 * (2 * m * t * m)) * S α β γ (2 * m * t) η r a ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hcK) hS
  have hnorm := (LB_one_le_norm K _ hx_int hx0).trans
    (norm_norm_le_norm_mul_house_pow _ σ)
  rw [hh', Nat.add_sub_cancel] at hnorm
  have hcast : (c : K) ^ (r + 2 * (2 * m * t * m)) * S α β γ (2 * m * t) η r a =
      ((c ^ (r + 2 * (2 * m * t * m)) : ℕ) : K) * S α β γ (2 * m * t) η r a := by
    push_cast
    ring
  have hσx : ‖σ ((c : K) ^ (r + 2 * (2 * m * t * m)) * S α β γ (2 * m * t) η r a)‖ =
      (c : ℝ) ^ (r + 2 * (2 * m * t * m)) * ‖σ (S α β γ (2 * m * t) η r a)‖ := by
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast]
  have hhx : house ((c : K) ^ (r + 2 * (2 * m * t * m)) * S α β γ (2 * m * t) η r a) =
      (c : ℝ) ^ (r + 2 * (2 * m * t * m)) * house (S α β γ (2 * m * t) η r a) := by
    rw [hcast, house_nat_mul]
    push_cast
    ring
  rw [hσx, hhx] at hnorm
  -- house of `S r a`
  have hρ : house (S α β γ (2 * m * t) η r a) ≤
      (((2 * m : ℕ) : ℝ) ^ 5 * C₁ * (1 + house β) *
        (max 1 (house α) * max 1 (house γ)) ^ m) ^ r * (t : ℝ) ^ (2 * r + 3) :=
    (LB_house_S K α β γ (2 * m * t) m η _ hhouse r a ham).trans
      (LB_arith C₁ _ _ _ hC₁ hP hA hB m t r hm ht hr)
  have hck : (c : ℝ) ^ (r + 2 * (2 * m * t * m)) ≤ (c : ℝ) ^ ((2 * m + 1) * r) :=
    pow_le_pow_right₀ hc1 hk
  have hy : 0 ≤ ‖σ (S α β γ (2 * m * t) η r a)‖ := norm_nonneg _
  have hc0' : (0 : ℝ) ≤ (c : ℝ) := by positivity
  have hfin : (1 : ℝ) ≤ (c : ℝ) ^ ((2 * m + 1) * r) * ‖σ (S α β γ (2 * m * t) η r a)‖ *
      ((c : ℝ) ^ ((2 * m + 1) * r) * ((((2 * m : ℕ) : ℝ) ^ 5 * C₁ * (1 + house β) *
        (max 1 (house α) * max 1 (house γ)) ^ m) ^ r * (t : ℝ) ^ (2 * r + 3))) ^ h' := by
    refine hnorm.trans ?_
    have hho : 0 ≤ house (S α β γ (2 * m * t) η r a) := house_nonneg _
    gcongr
  have hX : 0 < ((c : ℝ) ^ ((h' + 1) * (2 * m + 1)) *
      (((2 * m : ℕ) : ℝ) ^ 5 * C₁ * (1 + house β) *
        (max 1 (house α) * max 1 (house γ)) ^ m) ^ h') ^ r *
      (t : ℝ) ^ ((2 * r + 3) * h') := by
    have : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    have : (0 : ℝ) < (c : ℝ) := by linarith
    have hD0 : (0 : ℝ) < ((2 * m : ℕ) : ℝ) ^ 5 * C₁ * (1 + house β) *
        (max 1 (house α) * max 1 (house γ)) ^ m := by linarith
    positivity
  rw [inv_le_iff_one_le_mul₀ hX]
  refine hfin.trans (le_of_eq ?_)
  ring

end LB

-- iteratedDeriv_R
section ID

lemma ID_term_contDiff (c w : ℂ) {n : ℕ} :
    ContDiff ℂ n (fun x : ℂ => c * Complex.exp (w * x)) :=
  contDiff_const.mul (Complex.contDiff_exp.comp (contDiff_const.mul contDiff_id))

lemma ID_inner_contDiff (q : ℕ) (c w : Fin q → ℂ) {n : ℕ} :
    ContDiff ℂ n (fun x : ℂ => ∑ l : Fin q, c l * Complex.exp (w l * x)) :=
  ContDiff.sum (fun l _ => ID_term_contDiff (c l) (w l))

lemma ID_term_iteratedDeriv (c w : ℂ) (j : ℕ) (x : ℂ) :
    iteratedDeriv j (fun x : ℂ => c * Complex.exp (w * x)) x
      = c * (w ^ j * Complex.exp (w * x)) := by
  have h : ContDiffAt ℂ j (fun x : ℂ => Complex.exp (w * x)) x :=
    (Complex.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffAt
  rw [iteratedDeriv_const_mul c h, iteratedDeriv_cexp_const_mul]

lemma iteratedDeriv_R (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (α β γ : K) (z : ℂ)
    (hα : σ α = Complex.exp z) (hγ : σ γ = Complex.exp (σ β * z)) (q : ℕ)
    (η : Fin q → Fin q → K) :
    Differentiable ℂ (R σ β z q η) ∧
      ∀ j a : ℕ, iteratedDeriv j (R σ β z q η) (a : ℂ) = z ^ j * σ (S α β γ q η j a) := by
  have hRfun : R σ β z q η = fun x => ∑ k : Fin q, ∑ l : Fin q,
      σ (η k l) * Complex.exp ((((((k : ℕ) : ℂ) + 1) + (((l : ℕ) : ℂ) + 1) * σ β) * z) * x) := by
    funext x; rfl
  refine ⟨?_, ?_⟩
  · rw [hRfun]
    exact (ContDiff.sum (fun k _ => ID_inner_contDiff q _ _ (n := 1))).differentiable
      one_ne_zero
  · intro j a
    rw [hRfun, iteratedDeriv_fun_sum (fun k _ => (ID_inner_contDiff q _ _).contDiffAt)]
    simp only [S, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [iteratedDeriv_fun_sum (fun l _ => (ID_term_contDiff _ _).contDiffAt)]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [ID_term_iteratedDeriv]
    simp only [map_mul, map_pow, map_add, map_natCast, map_one, hα, hγ]
    have he : Complex.exp ((((k : ℕ) : ℂ) + 1 + (((l : ℕ) : ℂ) + 1) * σ β) * z * (a : ℂ))
        = Complex.exp z ^ (((k : ℕ) + 1) * a)
          * Complex.exp (σ β * z) ^ (((l : ℕ) + 1) * a) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [he, mul_pow]
    ring

end ID

-- exists_factor
section EF

/-- One point: an entire function vanishing to order at least `r` at `c` is `(x - c)^r` times
an entire function. -/
lemma EF_one (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ) (r : ℕ)
    (hord : (r : ℕ∞) ≤ analyticOrderAt f c) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ x : ℂ, f x = (x - c) ^ r * g x := by
  obtain ⟨g₀, hg₀, hev⟩ := (natCast_le_analyticOrderAt (hf.analyticAt c)).1 hord
  simp only [smul_eq_mul] at hev
  refine ⟨fun x => if x = c then g₀ c else f x / (x - c) ^ r, ?_, ?_⟩
  · intro x
    by_cases hx : x = c
    · subst hx
      have heq : (fun y => if y = x then g₀ x else f y / (y - x) ^ r) =ᶠ[nhds x] g₀ := by
        filter_upwards [hev] with y hy
        by_cases hyx : y = x
        · simp [hyx]
        · have hne : (y - x) ^ r ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hyx)
          simp only [hyx, if_false]
          rw [hy]
          field_simp
      exact (hg₀.differentiableAt).congr_of_eventuallyEq heq
    · have heq : (fun y => if y = c then g₀ c else f y / (y - c) ^ r) =ᶠ[nhds x]
          fun y => f y / (y - c) ^ r := by
        filter_upwards [isOpen_ne.mem_nhds hx] with y hy
        have hy' : y ≠ c := hy
        simp [hy']
      have hne : (x - c) ^ r ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hx)
      have hd : DifferentiableAt ℂ (fun y => f y / (y - c) ^ r) x :=
        (hf x).div (((differentiableAt_id).sub_const c).pow r) hne
      exact hd.congr_of_eventuallyEq heq
  · intro x
    by_cases hx : x = c
    · subst hx
      simpa using hev.self_of_nhds
    · have hne : (x - c) ^ r ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hx)
      simp only [hx, if_false]
      field_simp

/-- The several point version, phrased with the order of vanishing. -/
lemma EF_order (r : ℕ) : ∀ (m : ℕ) (f : ℂ → ℂ), Differentiable ℂ f →
    (∀ a : ℕ, 1 ≤ a → a ≤ m → (r : ℕ∞) ≤ analyticOrderAt f (a : ℂ)) →
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ x : ℂ, f x = (∏ a ∈ Finset.Icc 1 m, (x - (a : ℂ)) ^ r) * g x := by
  intro m
  induction m with
  | zero =>
    intro f hf _
    exact ⟨f, hf, fun x => by simp⟩
  | succ m ih =>
    intro f hf hord
    obtain ⟨g, hg, hfg⟩ := ih f hf (fun a h1 h2 => hord a h1 (Nat.le_succ_of_le h2))
    have hP : Differentiable ℂ (fun x : ℂ => ∏ a ∈ Finset.Icc 1 m, (x - (a : ℂ)) ^ r) := by
      fun_prop
    have hPne : (∏ a ∈ Finset.Icc 1 m, ((((m + 1 : ℕ) : ℂ)) - (a : ℂ)) ^ r) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 (fun a ha => pow_ne_zero _ (sub_ne_zero.2 ?_))
      have ha' : a ≤ m := (Finset.mem_Icc.1 ha).2
      intro h
      have : m + 1 = a := by exact_mod_cast h
      omega
    have hfeq : f = (fun x : ℂ => ∏ a ∈ Finset.Icc 1 m, (x - (a : ℂ)) ^ r) * g := by
      funext x
      simpa using hfg x
    have hordP : analyticOrderAt (fun x : ℂ => ∏ a ∈ Finset.Icc 1 m, (x - (a : ℂ)) ^ r)
        (((m + 1 : ℕ) : ℂ)) = 0 :=
      ((hP.analyticAt _).analyticOrderAt_eq_zero).2 hPne
    have hordg : (r : ℕ∞) ≤ analyticOrderAt g (((m + 1 : ℕ) : ℂ)) := by
      have h1 := hord (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) le_rfl
      rw [hfeq, analyticOrderAt_mul (hP.analyticAt _) (hg.analyticAt _), hordP, zero_add] at h1
      exact h1
    obtain ⟨g', hg', hgg'⟩ := EF_one g hg _ r hordg
    refine ⟨g', hg', fun x => ?_⟩
    rw [Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le m)), hfg x, hgg' x]
    ring

/-- LEMMA 5a (dividing out the zeros). An entire `f` whose derivatives of order `< r` vanish at
`1, …, m` is `(∏_{a=1}^{m} (x - a)^r) * g x` with `g` entire. -/
lemma exists_factor (f : ℂ → ℂ) (hf : Differentiable ℂ f) (m r : ℕ)
    (hvan : ∀ j < r, ∀ a : ℕ, 1 ≤ a → a ≤ m → iteratedDeriv j f (a : ℂ) = 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ x : ℂ, f x = (∏ a ∈ Finset.Icc 1 m, (x - (a : ℂ)) ^ r) * g x := by
  refine EF_order r m f hf (fun a h1 h2 => ?_)
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf.analyticAt _)).2
    (fun j hj => hvan j hj a h1 h2)

end EF

-- schwarz_multi
section SM

/-- The `r`-th derivative of `(x - c)^r * G x` at `c` is `r! * G c`, for entire `G`. -/
lemma SM_iteratedDeriv_pow_mul (c : ℂ) : ∀ (r : ℕ) (G : ℂ → ℂ), Differentiable ℂ G →
    iteratedDeriv r (fun x => (x - c) ^ r * G x) c = (r.factorial : ℂ) * G c := by
  intro r
  induction r with
  | zero => intro G _; simp
  | succ n ih =>
    intro G hG
    have hd : deriv (fun x => (x - c) ^ (n + 1) * G x) =
        fun x => (x - c) ^ n * (((n : ℂ) + 1) * G x + (x - c) * deriv G x) := by
      funext x
      have h1 : HasDerivAt (fun x : ℂ => (x - c) ^ (n + 1))
          (((n + 1 : ℕ) : ℂ) * (x - c) ^ n * 1) x := by
        simpa using ((hasDerivAt_id x).sub_const c).fun_pow (n + 1)
      have h2 := h1.fun_mul (hG x).hasDerivAt
      rw [h2.deriv]
      push_cast
      ring
    have hG' : Differentiable ℂ (deriv G) := hG.deriv
    have hG1 : Differentiable ℂ (fun x => ((n : ℂ) + 1) * G x + (x - c) * deriv G x) := by
      fun_prop
    rw [iteratedDeriv_succ', hd, ih _ hG1]
    simp only [sub_self, zero_mul, add_zero]
    rw [Nat.factorial_succ]
    push_cast
    ring

/-- On the circle of radius `R₀ > m` the polynomial `∏ (x - a)^r` is at least
`(R₀ - m)^(m r)` in norm. -/
lemma SM_norm_prod_ge (m r : ℕ) (R₀ : ℝ) (hR : (m : ℝ) < R₀) (x : ℂ) (hx : ‖x‖ = R₀) :
    (R₀ - m) ^ (m * r) ≤ ‖∏ a ∈ Finset.Icc 1 m, (x - (a : ℂ)) ^ r‖ := by
  have hRm : 0 < R₀ - m := by linarith
  rw [norm_prod]
  have hc : (R₀ - m) ^ (m * r) = ∏ _a ∈ Finset.Icc 1 m, (R₀ - m) ^ r := by
    rw [Finset.prod_const, Nat.card_Icc, ← pow_mul, Nat.add_sub_cancel, mul_comm]
  rw [hc]
  apply Finset.prod_le_prod
  · intro a _
    exact (pow_pos hRm r).le
  · intro a ha
    rw [norm_pow]
    apply pow_le_pow_left₀ hRm.le
    have ha2 := (Finset.mem_Icc.mp ha).2
    have h3 : ‖x‖ - ‖(a : ℂ)‖ ≤ ‖x - (a : ℂ)‖ := norm_sub_norm_le _ _
    rw [Complex.norm_natCast, hx] at h3
    have h4 : (a : ℝ) ≤ m := by exact_mod_cast ha2
    linarith

lemma schwarz_multi (f : ℂ → ℂ) (hf : Differentiable ℂ f) (m r a₀ : ℕ) (h1 : 1 ≤ a₀)
    (h2 : a₀ ≤ m)
    (hvan : ∀ j < r, ∀ a : ℕ, 1 ≤ a → a ≤ m → iteratedDeriv j f (a : ℂ) = 0)
    (R₀ M : ℝ) (hR : (m : ℝ) < R₀) (hM : ∀ x : ℂ, ‖x‖ = R₀ → ‖f x‖ ≤ M) :
    ‖iteratedDeriv r f (a₀ : ℂ)‖ * (R₀ - m) ^ (m * r) ≤
      (r.factorial : ℝ) * (m : ℝ) ^ (m * r) * M := by
  classical
  obtain ⟨g, hg, hfg⟩ := exists_factor f hf m r hvan
  have hRm : 0 < R₀ - m := by linarith
  have hR0 : 0 < R₀ := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have ha₀m : (a₀ : ℝ) ≤ m := by exact_mod_cast h2
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h1.trans h2
  -- maximum modulus for `g` on the disc of radius `R₀`
  have hgb : ‖g (a₀ : ℂ)‖ ≤ M / (R₀ - m) ^ (m * r) := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := Metric.ball (0 : ℂ) R₀)
      Metric.isBounded_ball hg.diffContOnCl
    · intro x hx
      rw [frontier_ball (0 : ℂ) hR0.ne', mem_sphere_zero_iff_norm] at hx
      rw [le_div_iff₀ (pow_pos hRm _)]
      have h3 := hM x hx
      rw [hfg x, norm_mul] at h3
      have h4 := SM_norm_prod_ge m r R₀ hR x hx
      calc ‖g x‖ * (R₀ - m) ^ (m * r)
          ≤ ‖g x‖ * ‖∏ a ∈ Finset.Icc 1 m, (x - (a : ℂ)) ^ r‖ :=
            mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
        _ = ‖∏ a ∈ Finset.Icc 1 m, (x - (a : ℂ)) ^ r‖ * ‖g x‖ := mul_comm _ _
        _ ≤ M := h3
    · apply subset_closure
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_natCast]
      linarith
  have hgb' : ‖g (a₀ : ℂ)‖ * (R₀ - m) ^ (m * r) ≤ M := (le_div_iff₀ (pow_pos hRm _)).mp hgb
  -- the derivative of order `r` at `a₀`
  have ha₀ : a₀ ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨h1, h2⟩
  have hGd : Differentiable ℂ
      (fun x : ℂ => (∏ a ∈ (Finset.Icc 1 m).erase a₀, (x - (a : ℂ)) ^ r) * g x) := by
    apply Differentiable.mul _ hg
    apply Differentiable.fun_finsetProd
    intro a _
    fun_prop
  have hfG : f = fun x : ℂ => (x - (a₀ : ℂ)) ^ r *
      ((∏ a ∈ (Finset.Icc 1 m).erase a₀, (x - (a : ℂ)) ^ r) * g x) := by
    funext x
    rw [hfg x, ← Finset.mul_prod_erase _ _ ha₀]
    ring
  have hder : iteratedDeriv r f (a₀ : ℂ) = (r.factorial : ℂ) *
      ((∏ a ∈ (Finset.Icc 1 m).erase a₀, ((a₀ : ℂ) - (a : ℂ)) ^ r) * g (a₀ : ℂ)) := by
    rw [hfG]
    exact SM_iteratedDeriv_pow_mul (a₀ : ℂ) r _ hGd
  have hprod : ‖∏ a ∈ (Finset.Icc 1 m).erase a₀, ((a₀ : ℂ) - (a : ℂ)) ^ r‖ ≤
      (m : ℝ) ^ (m * r) := by
    rw [norm_prod]
    calc ∏ a ∈ (Finset.Icc 1 m).erase a₀, ‖((a₀ : ℂ) - (a : ℂ)) ^ r‖
        ≤ ∏ _a ∈ (Finset.Icc 1 m).erase a₀, (m : ℝ) ^ r := by
          apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          intro a ha
          rw [norm_pow]
          apply pow_le_pow_left₀ (norm_nonneg _)
          have ha' := Finset.mem_Icc.mp (Finset.mem_of_mem_erase ha)
          have e1 : (1 : ℝ) ≤ a := by exact_mod_cast ha'.1
          have e2 : (a : ℝ) ≤ m := by exact_mod_cast ha'.2
          have e3 : (1 : ℝ) ≤ a₀ := by exact_mod_cast h1
          have e4 : ((a₀ : ℂ) - (a : ℂ)) = (((a₀ : ℝ) - (a : ℝ) : ℝ) : ℂ) := by push_cast; ring
          rw [e4, Complex.norm_real, Real.norm_eq_abs, abs_le]
          constructor <;> linarith
      _ = (m : ℝ) ^ ((m - 1) * r) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem ha₀, Nat.card_Icc, ← pow_mul,
            Nat.add_sub_cancel, mul_comm]
      _ ≤ (m : ℝ) ^ (m * r) :=
          pow_le_pow_right₀ hm1 (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
  have hX0 : 0 ≤ ‖g (a₀ : ℂ)‖ * (R₀ - m) ^ (m * r) :=
    mul_nonneg (norm_nonneg _) (pow_pos hRm _).le
  have hfac : (0 : ℝ) ≤ (r.factorial : ℝ) := Nat.cast_nonneg _
  rw [hder, norm_mul, norm_mul, Complex.norm_natCast]
  calc (r.factorial : ℝ) *
        (‖∏ a ∈ (Finset.Icc 1 m).erase a₀, ((a₀ : ℂ) - (a : ℂ)) ^ r‖ * ‖g (a₀ : ℂ)‖) *
        (R₀ - m) ^ (m * r)
      = (r.factorial : ℝ) *
        (‖∏ a ∈ (Finset.Icc 1 m).erase a₀, ((a₀ : ℂ) - (a : ℂ)) ^ r‖ *
          (‖g (a₀ : ℂ)‖ * (R₀ - m) ^ (m * r))) := by ring
    _ ≤ (r.factorial : ℝ) * ((m : ℝ) ^ (m * r) * (‖g (a₀ : ℂ)‖ * (R₀ - m) ^ (m * r))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod hX0) hfac
    _ ≤ (r.factorial : ℝ) * ((m : ℝ) ^ (m * r) * M) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hgb' (pow_nonneg (Nat.cast_nonneg m) _)) hfac
    _ = (r.factorial : ℝ) * (m : ℝ) ^ (m * r) * M := by ring

end SM

-- upper_bound
section UB

/-- Termwise bound of the auxiliary function. -/
lemma UB_norm_R_le {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (β : K) (z : ℂ) (q : ℕ)
    (η : Fin q → Fin q → K) (H : ℝ) (hH : ∀ k l, house (η k l) ≤ H) (x : ℂ) :
    ‖R σ β z q η x‖ ≤ (q : ℝ) ^ 2 * H * Real.exp ((q : ℝ) * (1 + ‖σ β‖) * ‖z‖ * ‖x‖) := by
  have hterm : ∀ k l : Fin q,
      ‖σ (η k l) * Complex.exp (((((k : ℕ) : ℂ) + 1) + (((l : ℕ) : ℂ) + 1) * σ β) * z * x)‖ ≤
        H * Real.exp ((q : ℝ) * (1 + ‖σ β‖) * ‖z‖ * ‖x‖) := by
    intro k l
    rw [norm_mul]
    have h1 : ‖σ (η k l)‖ ≤ H := (norm_embedding_le_house _ σ).trans (hH k l)
    have h2 := Complex.norm_exp_le_exp_norm
      (((((k : ℕ) : ℂ) + 1) + (((l : ℕ) : ℂ) + 1) * σ β) * z * x)
    have hk : ‖((k : ℕ) : ℂ) + 1‖ ≤ (q : ℝ) := by
      have e : ((k : ℕ) : ℂ) + 1 = (((k : ℕ) + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [e, Complex.norm_natCast]
      exact_mod_cast k.2
    have hl : ‖((l : ℕ) : ℂ) + 1‖ ≤ (q : ℝ) := by
      have e : ((l : ℕ) : ℂ) + 1 = (((l : ℕ) + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [e, Complex.norm_natCast]
      exact_mod_cast l.2
    have h3 : ‖((((k : ℕ) : ℂ) + 1) + (((l : ℕ) : ℂ) + 1) * σ β) * z * x‖ ≤
        (q : ℝ) * (1 + ‖σ β‖) * ‖z‖ * ‖x‖ := by
      rw [norm_mul, norm_mul]
      have h4 : ‖(((k : ℕ) : ℂ) + 1) + (((l : ℕ) : ℂ) + 1) * σ β‖ ≤ (q : ℝ) * (1 + ‖σ β‖) := by
        calc ‖(((k : ℕ) : ℂ) + 1) + (((l : ℕ) : ℂ) + 1) * σ β‖
            ≤ ‖((k : ℕ) : ℂ) + 1‖ + ‖(((l : ℕ) : ℂ) + 1) * σ β‖ := norm_add_le _ _
          _ = ‖((k : ℕ) : ℂ) + 1‖ + ‖((l : ℕ) : ℂ) + 1‖ * ‖σ β‖ := by rw [norm_mul]
          _ ≤ (q : ℝ) + (q : ℝ) * ‖σ β‖ := by gcongr
          _ = (q : ℝ) * (1 + ‖σ β‖) := by ring
      gcongr
    have hH0 : 0 ≤ H := (norm_nonneg _).trans h1
    have h5 := h2.trans (Real.exp_le_exp.mpr h3)
    exact mul_le_mul h1 h5 (norm_nonneg _) hH0
  unfold R
  calc ‖∑ k : Fin q, ∑ l : Fin q,
          σ (η k l) * Complex.exp (((((k : ℕ) : ℂ) + 1) + (((l : ℕ) : ℂ) + 1) * σ β) * z * x)‖
      ≤ ∑ _k : Fin q, ∑ _l : Fin q, H * Real.exp ((q : ℝ) * (1 + ‖σ β‖) * ‖z‖ * ‖x‖) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => hterm k l)
    _ = (q : ℝ) ^ 2 * H * Real.exp ((q : ℝ) * (1 + ‖σ β‖) * ‖z‖ * ‖x‖) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The real-number bookkeeping: from the Schwarz inequality to the final bound. -/
lemma UB_arith (m t r : ℕ) (hm : 0 < m) (ht : 1 ≤ t) (hnr : 2 * m * t ^ 2 ≤ r)
    (hrq : r < (2 * m * t) ^ 2) (X Z b C₁ : ℝ) (hX : 0 ≤ X) (hZ : 0 < Z) (hb : 0 ≤ b)
    (hC₁ : 1 ≤ C₁)
    (hS : Z ^ r * X * ((m : ℝ) * (r : ℝ) / ((2 * m * t : ℕ) : ℝ)) ^ (m * r) ≤
      (r.factorial : ℝ) * (m : ℝ) ^ (m * r) *
        (((2 * m * t : ℕ) : ℝ) ^ 2 *
          (C₁ ^ (2 * m * t ^ 2) * ((2 * m * t : ℕ) : ℝ) ^ (2 * m * t ^ 2 + 1)) *
          Real.exp (((2 * m * t : ℕ) : ℝ) * (1 + b) * Z *
            ((m : ℝ) + (m : ℝ) * (r : ℝ) / ((2 * m * t : ℕ) : ℝ))))) :
    X * (t : ℝ) ^ (m * r) ≤
      (max 1 (Z⁻¹ * C₁ * Real.exp (2 * (m : ℝ) * (1 + b) * Z) * (2 * (m : ℝ)) ^ 6)) ^ r *
        (t : ℝ) ^ (3 * r + 3) := by
  set q : ℝ := ((2 * m * t : ℕ) : ℝ) with hqdef
  set E : ℝ := Real.exp (2 * (m : ℝ) * (1 + b) * Z) with hEdef
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have htR : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < (t : ℝ) := by linarith
  have hq : q = 2 * (m : ℝ) * (t : ℝ) := by rw [hqdef]; push_cast; ring
  have hq0 : 0 < q := by rw [hq]; positivity
  have h2m1 : (1 : ℝ) ≤ 2 * (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hq1 : 1 ≤ q := by rw [hq]; nlinarith
  -- natural-number facts
  have hqn : 2 * m * t ≤ 2 * m * t ^ 2 := by
    have : t ≤ t ^ 2 := by nlinarith
    exact Nat.mul_le_mul_left _ this
  have hqr : 2 * m * t ≤ r := hqn.trans hnr
  have hr1 : 1 ≤ r :=
    le_trans (Nat.mul_pos (Nat.mul_pos (by norm_num) hm) ht) hqr
  have hrR : (2 : ℝ) * (m : ℝ) * (t : ℝ) ^ 2 ≤ (r : ℝ) := by exact_mod_cast hnr
  have hqrR : q ≤ (r : ℝ) := by rw [hqdef]; exact_mod_cast hqr
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
  -- step 1: lower bound for the left factor
  have h1 : (m : ℝ) * (t : ℝ) ≤ (m : ℝ) * (r : ℝ) / q := by
    rw [le_div_iff₀ hq0, hq]
    nlinarith
  have h1' : (m : ℝ) ^ (m * r) * (t : ℝ) ^ (m * r) ≤ ((m : ℝ) * (r : ℝ) / q) ^ (m * r) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 _
  -- step 2: the exponential
  have h2 : Real.exp (q * (1 + b) * Z * ((m : ℝ) + (m : ℝ) * (r : ℝ) / q)) ≤ E ^ r := by
    rw [hEdef, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have e : q * (1 + b) * Z * ((m : ℝ) + (m : ℝ) * (r : ℝ) / q) =
        (1 + b) * Z * ((m : ℝ) * (q + (r : ℝ))) := by
      field_simp
    rw [e]
    have h3 : (m : ℝ) * (q + (r : ℝ)) ≤ 2 * (m : ℝ) * (r : ℝ) := by nlinarith
    have h4 : 0 ≤ (1 + b) * Z := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 h4]
  -- step 3: the factorial
  have h3 : (r.factorial : ℝ) ≤ q ^ (2 * r) := by
    have ha : (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by exact_mod_cast Nat.factorial_le_pow r
    have hb' : (r : ℝ) ≤ q ^ 2 := by
      rw [hqdef]; exact_mod_cast hrq.le
    calc (r.factorial : ℝ) ≤ (r : ℝ) ^ r := ha
      _ ≤ (q ^ 2) ^ r := pow_le_pow_left₀ hr0.le hb' _
      _ = q ^ (2 * r) := by rw [← pow_mul]
  -- step 4: the house bound
  have h4 : C₁ ^ (2 * m * t ^ 2) ≤ C₁ ^ r := pow_le_pow_right₀ hC₁ hnr
  have h5 : q ^ (2 * m * t ^ 2 + 1) ≤ q ^ (r + 1) := pow_le_pow_right₀ hq1 (by omega)
  have hE0 : 0 < E := Real.exp_pos _
  have hC0 : 0 < C₁ := by linarith
  -- combine
  have hmpow : (0 : ℝ) < (m : ℝ) ^ (m * r) := by positivity
  have hL : (m : ℝ) ^ (m * r) * (Z ^ r * X * (t : ℝ) ^ (m * r)) ≤
      (m : ℝ) ^ (m * r) * ((C₁ * E) ^ r * q ^ (3 * r + 3)) := by
    calc (m : ℝ) ^ (m * r) * (Z ^ r * X * (t : ℝ) ^ (m * r))
        = Z ^ r * X * ((m : ℝ) ^ (m * r) * (t : ℝ) ^ (m * r)) := by ring
      _ ≤ Z ^ r * X * ((m : ℝ) * (r : ℝ) / q) ^ (m * r) := by
          apply mul_le_mul_of_nonneg_left h1'
          positivity
      _ ≤ (r.factorial : ℝ) * (m : ℝ) ^ (m * r) *
            (q ^ 2 * (C₁ ^ (2 * m * t ^ 2) * q ^ (2 * m * t ^ 2 + 1)) *
              Real.exp (q * (1 + b) * Z * ((m : ℝ) + (m : ℝ) * (r : ℝ) / q))) := hS
      _ ≤ q ^ (2 * r) * (m : ℝ) ^ (m * r) * (q ^ 2 * (C₁ ^ r * q ^ (r + 1)) * E ^ r) := by
          gcongr
      _ = (m : ℝ) ^ (m * r) * ((C₁ * E) ^ r * q ^ (3 * r + 3)) := by
          rw [mul_pow]; ring
  have hL' : Z ^ r * X * (t : ℝ) ^ (m * r) ≤ (C₁ * E) ^ r * q ^ (3 * r + 3) :=
    le_of_mul_le_mul_left hL hmpow
  have hqpow : q ^ (3 * r + 3) ≤ ((2 * (m : ℝ)) ^ 6) ^ r * (t : ℝ) ^ (3 * r + 3) := by
    rw [hq, mul_pow, ← pow_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact pow_le_pow_right₀ h2m1 (by omega)
  have hZr : 0 < Z ^ r := by positivity
  have hfin : X * (t : ℝ) ^ (m * r) ≤
      (Z⁻¹ * C₁ * E * (2 * (m : ℝ)) ^ 6) ^ r * (t : ℝ) ^ (3 * r + 3) := by
    have hCE : 0 ≤ (C₁ * E) ^ r := by positivity
    have h6 : Z ^ r * (X * (t : ℝ) ^ (m * r)) ≤
        Z ^ r * ((Z⁻¹ * C₁ * E * (2 * (m : ℝ)) ^ 6) ^ r * (t : ℝ) ^ (3 * r + 3)) := by
      calc Z ^ r * (X * (t : ℝ) ^ (m * r)) = Z ^ r * X * (t : ℝ) ^ (m * r) := by ring
        _ ≤ (C₁ * E) ^ r * q ^ (3 * r + 3) := hL'
        _ ≤ (C₁ * E) ^ r * (((2 * (m : ℝ)) ^ 6) ^ r * (t : ℝ) ^ (3 * r + 3)) :=
            mul_le_mul_of_nonneg_left hqpow hCE
        _ = Z ^ r * ((Z⁻¹ * C₁ * E * (2 * (m : ℝ)) ^ 6) ^ r * (t : ℝ) ^ (3 * r + 3)) := by
            have : Z ^ r * (Z⁻¹) ^ r = 1 := by
              rw [← mul_pow, mul_inv_cancel₀ hZ.ne', one_pow]
            rw [mul_pow, mul_pow, mul_pow, mul_pow]
            linear_combination (-(C₁ ^ r * E ^ r * ((2 * (m : ℝ)) ^ 6) ^ r *
              (t : ℝ) ^ (3 * r + 3))) * this
    exact le_of_mul_le_mul_left h6 hZr
  refine hfin.trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact pow_le_pow_left₀ (by positivity) (le_max_right _ _) _

/-- LEMMA 4 (analytic upper bound). Uses `iteratedDeriv_R` and `schwarz_multi` as black boxes.
For `η` with the house bound of `aux_coeffs`, `n = 2mt^2 ≤ r < q^2 = (2mt)^2`, `1 ≤ a₀ ≤ m`
and `S j a = 0` for all `j < r`, `1 ≤ a ≤ m`:
`‖σ (S r a₀)‖ * t^(m r) ≤ C₅^r * t^(3r+3)`.

Sketch. `f := R σ β z q η`, `q = 2mt`. By `iteratedDeriv_R`, `f^(j)(a) = z^j σ (S j a)`, so `f`
vanishes to order `r` at `1..m` and `f^(r)(a₀) = z^r σ(ρ)`, `ρ = S r a₀`. Take
`R₀ = m (1 + r / q)`, so `R₀ - m = m r / q > 0`. On `‖x‖ = R₀`:
`‖f x‖ ≤ q^2 * H * exp (q (1 + ‖σ β‖) ‖z‖ R₀)` with `H = C₁^n q^(n+1)`
(`NumberField.norm_embedding_le_house`, `Complex.norm_exp_le_exp_norm`, and
`‖(k+1) + (l+1) σβ‖ ≤ q (1 + ‖σβ‖)`); `q R₀ = m (q + r) ≤ 2 m r` because `q ≤ n ≤ r`.
`schwarz_multi` gives `‖z‖^r ‖σρ‖ (m r / q)^(m r) ≤ r! m^(m r) M`, that is
`‖σρ‖ ≤ ‖z‖^(-r) r! M (q / r)^(m r)`. Now `r! ≤ r^r ≤ q^(2r)` (as `r < q^2`),
`C₁^n q^(n+1) ≤ C₁^r q^(r+1)`, and `q / r ≤ q / n = 1 / t`, so `(q/r)^(m r) ≤ t^(-m r)`.
Hence `‖σρ‖ t^(m r) ≤ (‖z‖⁻¹ C₁ exp (2 m (1 + ‖σβ‖) ‖z‖))^r q^(3r+3)` and
`q^(3r+3) = (2m)^(3r+3) t^(3r+3) ≤ ((2m)^6)^r t^(3r+3)`. Take
`C₅ = max 1 (‖z‖⁻¹ C₁ exp (2 m (1 + ‖σβ‖) ‖z‖) (2m)^6)`.

Depends on: `iteratedDeriv_R`, `schwarz_multi` (black boxes).
Estimate: 250 to 350 lines. Tested in `tests.py` with the explicit `C₅` above on instances
where the hypotheses really hold (K = ℚ, β rational: α = 4, β = 1/2, γ = 2, z = log 4; the
non-principal z = log 4 + 2πi with γ = -2; α = 128, β = 1/7, γ = 2), `(m,t)` up to `q = 6`,
`η` an exact integer solution, `r` the true minimal order: the Schwarz inequality for `R` and
the final inequality hold for all 46 values. The bound has a lot of room (`C₅` is large), so
this confirms the direction and the hypotheses, not sharpness. Exponent bookkeeping
(`q ≤ n`, `r / q ≥ t`, `r! ≤ q^(2r)`, `3r + 3 ≤ 6r`) by script. -/
lemma upper_bound (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (α β γ : K) (z : ℂ)
    (hz : z ≠ 0) (hα : σ α = Complex.exp z) (hγ : σ γ = Complex.exp (σ β * z)) (m : ℕ)
    (hm : 0 < m) (C₁ : ℝ) (hC₁ : 1 ≤ C₁) :
    ∃ C₅ : ℝ, 1 ≤ C₅ ∧ ∀ t : ℕ, 1 ≤ t → ∀ η : Fin (2 * m * t) → Fin (2 * m * t) → K,
      (∀ k l, house (η k l) ≤
        C₁ ^ (2 * m * t ^ 2) * ((2 * m * t : ℕ) : ℝ) ^ (2 * m * t ^ 2 + 1)) →
      ∀ r a₀, 2 * m * t ^ 2 ≤ r → r < (2 * m * t) ^ 2 → 1 ≤ a₀ → a₀ ≤ m →
        (∀ j < r, ∀ a, 1 ≤ a → a ≤ m → S α β γ (2 * m * t) η j a = 0) →
        ‖σ (S α β γ (2 * m * t) η r a₀)‖ * (t : ℝ) ^ (m * r) ≤
          C₅ ^ r * (t : ℝ) ^ (3 * r + 3) := by
  refine ⟨max 1 (‖z‖⁻¹ * C₁ * Real.exp (2 * (m : ℝ) * (1 + ‖σ β‖) * ‖z‖) * (2 * (m : ℝ)) ^ 6),
    le_max_left _ _, ?_⟩
  intro t ht η hη r a₀ hnr hrq h1 h2 hvan
  obtain ⟨hdiff, hder⟩ := iteratedDeriv_R K σ α β γ z hα hγ (2 * m * t) η
  have hvan' : ∀ j < r, ∀ a : ℕ, 1 ≤ a → a ≤ m →
      iteratedDeriv j (R σ β z (2 * m * t) η) (a : ℂ) = 0 := by
    intro j hj a ha1 ha2
    rw [hder, hvan j hj a ha1 ha2, map_zero, mul_zero]
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hq0 : (0 : ℝ) < ((2 * m * t : ℕ) : ℝ) := by
    have : 0 < 2 * m * t := by positivity
    exact_mod_cast this
  have hr0 : (0 : ℝ) < (r : ℝ) := by
    have : 0 < 2 * m * t ^ 2 := by positivity
    have : 0 < r := by omega
    exact_mod_cast this
  have hR : (m : ℝ) < (m : ℝ) + (m : ℝ) * (r : ℝ) / ((2 * m * t : ℕ) : ℝ) := by
    have : 0 < (m : ℝ) * (r : ℝ) / ((2 * m * t : ℕ) : ℝ) := by positivity
    linarith
  have hM : ∀ x : ℂ, ‖x‖ = (m : ℝ) + (m : ℝ) * (r : ℝ) / ((2 * m * t : ℕ) : ℝ) →
      ‖R σ β z (2 * m * t) η x‖ ≤
        ((2 * m * t : ℕ) : ℝ) ^ 2 *
          (C₁ ^ (2 * m * t ^ 2) * ((2 * m * t : ℕ) : ℝ) ^ (2 * m * t ^ 2 + 1)) *
          Real.exp (((2 * m * t : ℕ) : ℝ) * (1 + ‖σ β‖) * ‖z‖ *
            ((m : ℝ) + (m : ℝ) * (r : ℝ) / ((2 * m * t : ℕ) : ℝ))) := by
    intro x hx
    have := UB_norm_R_le σ β z (2 * m * t) η _ hη x
    rwa [hx] at this
  have hsch := schwarz_multi (R σ β z (2 * m * t) η) hdiff m r a₀ h1 h2 hvan' _ _ hR hM
  rw [hder, norm_mul, norm_pow, add_sub_cancel_left] at hsch
  exact UB_arith m t r hm ht hnr hrq _ ‖z‖ ‖σ β‖ C₁ (norm_nonneg _) (norm_pos_iff.mpr hz)
    (norm_nonneg _) hC₁ hsch

end UB

-- no_large_t
section NL

/-- Exponent bookkeeping: with `r = 3 (h' + 1) + s` and `m = 2 (h' + 1) + 2`,
`m r = (3 r + 3 + (2 r + 3) h') + s`. -/
lemma NL_exp_identity (h' s r m : ℕ) (hr : r = 3 * (h' + 1) + s)
    (hm : m = 2 * (h' + 1) + 2) :
    m * r = (3 * r + 3 + (2 * r + 3) * h') + s := by
  subst hr hm
  ring

lemma no_large_t (h m : ℕ) (hm : m = 2 * h + 2) (hh : 1 ≤ h) (C₄ C₅ : ℝ) (h4 : 1 ≤ C₄)
    (h5 : 1 ≤ C₅) :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t → ∀ r : ℕ, 2 * m * t ^ 2 ≤ r → ∀ x : ℝ, 0 ≤ x →
      (C₄ ^ r * (t : ℝ) ^ ((2 * r + 3) * (h - 1)))⁻¹ ≤ x →
      x * (t : ℝ) ^ (m * r) ≤ C₅ ^ r * (t : ℝ) ^ (3 * r + 3) → False := by
  refine ⟨⌈(C₄ * C₅) ^ 4⌉₊ + 2, ?_⟩
  intro t hT r hr x hx hlow hup
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  have hsub : h' + 1 - 1 = h' := by omega
  rw [hsub] at hlow
  have ht2 : 2 ≤ t := by omega
  -- r is large compared with h
  have hmt : 8 * (h' + 1) ≤ 2 * m * t ^ 2 := by
    have : 4 ≤ t ^ 2 := by nlinarith
    rw [hm]; nlinarith
  obtain ⟨s, hs⟩ : ∃ s, r = 3 * (h' + 1) + s := ⟨r - 3 * (h' + 1), by omega⟩
  have hsh : r ≤ 4 * s := by omega
  have hr0 : r ≠ 0 := by omega
  have hexp := NL_exp_identity h' s r m hs hm
  set C : ℝ := C₄ * C₅ with hC
  have hC1 : 1 ≤ C := by rw [hC]; nlinarith
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast (by omega : 1 ≤ t)
  have htpos : (0 : ℝ) < t := by linarith
  set E : ℕ := (2 * r + 3) * h' with hE
  set A : ℕ := 3 * r + 3 + E with hA
  have hD : 0 < C₄ ^ r * (t : ℝ) ^ E := by positivity
  -- 1 ≤ x C₄^r t^E
  have h1 : 1 ≤ x * (C₄ ^ r * (t : ℝ) ^ E) := by
    have := mul_le_mul_of_nonneg_right hlow hD.le
    rwa [inv_mul_cancel₀ hD.ne'] at this
  -- t^(m r) ≤ C^r t^A
  have h2 : (t : ℝ) ^ (m * r) ≤ C ^ r * (t : ℝ) ^ A := by
    have htm : (0 : ℝ) ≤ (t : ℝ) ^ (m * r) := by positivity
    calc (t : ℝ) ^ (m * r) ≤ x * (C₄ ^ r * (t : ℝ) ^ E) * (t : ℝ) ^ (m * r) := by
          nlinarith
      _ = (x * (t : ℝ) ^ (m * r)) * (C₄ ^ r * (t : ℝ) ^ E) := by ring
      _ ≤ (C₅ ^ r * (t : ℝ) ^ (3 * r + 3)) * (C₄ ^ r * (t : ℝ) ^ E) :=
          mul_le_mul_of_nonneg_right hup hD.le
      _ = C ^ r * (t : ℝ) ^ A := by
          rw [hC, hA, mul_pow, pow_add (t : ℝ) (3 * r + 3) E]; ring
  -- t^s ≤ C^r
  have h3 : (t : ℝ) ^ s ≤ C ^ r := by
    rw [hexp, pow_add] at h2
    have hAp : (0 : ℝ) < (t : ℝ) ^ A := by positivity
    have : (t : ℝ) ^ A * (t : ℝ) ^ s ≤ (t : ℝ) ^ A * C ^ r := by linarith
    exact le_of_mul_le_mul_left this hAp
  -- t^r ≤ (C^4)^r
  have h4' : (t : ℝ) ^ r ≤ (C ^ 4) ^ r := by
    calc (t : ℝ) ^ r ≤ (t : ℝ) ^ (4 * s) := pow_le_pow_right₀ htR hsh
      _ = ((t : ℝ) ^ s) ^ 4 := by rw [← pow_mul, mul_comm]
      _ ≤ (C ^ r) ^ 4 := pow_le_pow_left₀ (by positivity) h3 4
      _ = (C ^ 4) ^ r := by rw [← pow_mul, ← pow_mul, mul_comm]
  have h5' : (t : ℝ) ≤ C ^ 4 :=
    (pow_le_pow_iff_left₀ htpos.le (by positivity) hr0).mp h4'
  have hceil : C ^ 4 ≤ (⌈C ^ 4⌉₊ : ℝ) := Nat.le_ceil _
  have hTt : ((⌈C ^ 4⌉₊ + 2 : ℕ) : ℝ) ≤ t := by exact_mod_cast hT
  push_cast at hTt
  linarith

end NL

/-- The core: in a number field `K ⊆ ℂ` (via `σ`), `σ α = exp z` with `z ≠ 0` and
`σ γ = exp (σ β * z)` force `β` rational. Proved from Lemmas 1, 2, 3, 4, 6. -/
theorem core (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (α β γ : K) (z : ℂ)
    (hz : z ≠ 0) (hα : σ α = Complex.exp z) (hγ : σ γ = Complex.exp (σ β * z))
    (hirr : ∀ x : ℚ, β ≠ (x : K)) : False := by
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [map_zero] at hα
    exact Complex.exp_ne_zero z hα.symm
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hγ
    exact Complex.exp_ne_zero _ hγ.symm
  have hpos : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
  have hm0 : 0 < 2 * Module.finrank ℚ K + 2 := by omega
  obtain ⟨C₁, hC₁, H1⟩ := aux_coeffs K α β γ (2 * Module.finrank ℚ K + 2) hm0 hα0 hγ0
  obtain ⟨C₄, hC₄, H3⟩ := lower_bound K σ α β γ (2 * Module.finrank ℚ K + 2) hm0 C₁ hC₁
  obtain ⟨C₅, hC₅, H4⟩ :=
    upper_bound K σ α β γ z hz hα hγ (2 * Module.finrank ℚ K + 2) hm0 C₁ hC₁
  obtain ⟨T, HT⟩ := no_large_t (Module.finrank ℚ K) (2 * Module.finrank ℚ K + 2) rfl hpos
    C₄ C₅ hC₄ hC₅
  have ht1 : 1 ≤ max T 1 := le_max_right _ _
  obtain ⟨η, hint, hne, hhouse, hvan⟩ := H1 (max T 1) ht1
  obtain ⟨rs, hrs, hSrs⟩ := exists_S_ne_zero K α β γ hα0 hγ0 hirr _ η hne
  classical
  have hP : ∃ r, ∃ a, 1 ≤ a ∧ a ≤ 2 * Module.finrank ℚ K + 2 ∧
      S α β γ (2 * (2 * Module.finrank ℚ K + 2) * max T 1) η r a ≠ 0 :=
    ⟨rs, 1, le_refl 1, by omega, hSrs⟩
  obtain ⟨a₀, ha1, ham, hS⟩ := Nat.find_spec hP
  have hr_lt : Nat.find hP < (2 * (2 * Module.finrank ℚ K + 2) * max T 1) ^ 2 :=
    lt_of_le_of_lt (Nat.find_min' hP ⟨1, le_refl 1, by omega, hSrs⟩) hrs
  have hr_ge : 2 * (2 * Module.finrank ℚ K + 2) * max T 1 ^ 2 ≤ Nat.find hP := by
    by_contra hlt
    exact hS (hvan _ (not_le.mp hlt) a₀ ha1 ham)
  have hmin : ∀ j < Nat.find hP, ∀ a, 1 ≤ a → a ≤ 2 * Module.finrank ℚ K + 2 →
      S α β γ (2 * (2 * Module.finrank ℚ K + 2) * max T 1) η j a = 0 := by
    intro j hj a h1 h2
    by_contra hne'
    exact Nat.find_min hP hj ⟨a, h1, h2, hne'⟩
  have low := H3 (max T 1) ht1 η hint hhouse (Nat.find hP) a₀ hr_ge ha1 ham hS
  have up := H4 (max T 1) ht1 η hhouse (Nat.find hP) a₀ hr_ge hr_lt ha1 ham hmin
  exact HT (max T 1) (le_max_left _ _) (Nat.find hP) hr_ge _ (norm_nonneg _) low up

/-- The step, from Lemma A and the core. -/
theorem main :
    OMA.R_ColossallyAbundantNumber_alaoglu_erdos_prime_powers_rational_conjecture_R1_H1_R1.H1 := by
  intro a z hz ha hirr hexp halg
  obtain ⟨K, _, _, σ, α', β', γ', hα', hβ', hγ'⟩ :=
    exists_numberField (Complex.exp z) a (Complex.exp (a * z)) hexp ha halg
  refine core K σ α' β' γ' z hz hα' (by rw [hγ', hβ']) ?_
  intro x hx
  apply hirr x
  rw [← hβ', hx, map_ratCast]

end OMA.GelfondSchneider

theorem OMA.solution :
    OMA.R_ColossallyAbundantNumber_alaoglu_erdos_prime_powers_rational_conjecture_R1_H1_R1.H1 :=
  OMA.GelfondSchneider.main
