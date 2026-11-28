import FormalConjectures.OEIS.«87455»

-- Conditional research reduction, not a proof of Benford's law.
-- The arithmetic independence condition is a genuine unresolved obstacle.
-- Analytic route: Berger--Eshun, A characterization of Benford's Law in discrete-time
-- linear systems, Lemma 2.6 and Theorem 3.16.

namespace OMA.R_OeisA87455_conjecture_R1

open OeisA87455

-- Arithmetic task: only relations mixing both irrational quantities remain open.
-- The unmixed cases are discharged by the logarithm/phase irrationality lemmas below.
def H1 : Prop :=
  ∀ q₀ q₁ q₂ : ℚ, q₁ ≠ 0 → q₂ ≠ 0 →
    (q₀ : ℝ) + (q₁ : ℝ) * Real.logb 10 (Real.sqrt 3) +
      (q₂ : ℝ) * (Real.arctan (Real.sqrt 2) / Real.pi) ≠ 0

-- Analytic task: equidistribution on the two-torus implies Benford behavior for
-- integer-valued exponentially scaled cosines. The criterion is reusable for any radius/angle.
def H2 : Prop :=
  ∀ (r θ : ℝ) (s : ℕ → ℤ), 0 < r →
    (∀ q₀ q₁ q₂ : ℚ,
      (q₀ : ℝ) + (q₁ : ℝ) * Real.logb 10 r +
        (q₂ : ℝ) * (θ / Real.pi) = 0 →
        q₀ = 0 ∧ q₁ = 0 ∧ q₂ = 0) →
    (∀ n : ℕ, (s n : ℝ) = r ^ n * Real.cos ((n : ℝ) * θ)) →
    OeisA87455.SatisfiesBenford s

-- Exact algebraic representation, discharged here rather than left as an open step.
lemma scaled_cos_add_two (r θ : ℝ) (hr : r * Real.cos θ = 1) (hr2 : r ^ 2 = 3)
    (n : ℕ) :
    r ^ (n + 2) * Real.cos (((n + 2 : ℕ) : ℝ) * θ) =
      2 * r ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * θ) -
        3 * r ^ n * Real.cos ((n : ℝ) * θ) := by
  have hc := Real.cos_add_cos (x := (((n + 2 : ℕ) : ℝ) * θ)) (y := (n : ℝ) * θ)
  have hmean : ((((n + 2 : ℕ) : ℝ) * θ + (n : ℝ) * θ) / 2) =
      (((n + 1 : ℕ) : ℝ) * θ) := by
    simp only [Nat.cast_add, Nat.cast_ofNat]
    ring
  have hdiff : ((((n + 2 : ℕ) : ℝ) * θ - (n : ℝ) * θ) / 2) = θ := by
    simp only [Nat.cast_add, Nat.cast_ofNat]
    ring
  rw [hmean, hdiff] at hc
  calc
    _ = r ^ (n + 2) *
          (Real.cos (((n + 2 : ℕ) : ℝ) * θ) + Real.cos ((n : ℝ) * θ)) -
        r ^ (n + 2) * Real.cos ((n : ℝ) * θ) := by ring
    _ = r ^ (n + 2) *
          (2 * Real.cos (((n + 1 : ℕ) : ℝ) * θ) * Real.cos θ) -
        r ^ (n + 2) * Real.cos ((n : ℝ) * θ) := by rw [hc]
    _ = 2 * r ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * θ) * (r * Real.cos θ) -
        r ^ n * r ^ 2 * Real.cos ((n : ℝ) * θ) := by
      simp only [pow_add, pow_one]
      ring
    _ = 2 * r ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * θ) -
        3 * r ^ n * Real.cos ((n : ℝ) * θ) := by rw [hr, hr2]; ring

lemma a_cosine (n : ℕ) :
    (a n : ℝ) =
      (Real.sqrt 3) ^ n * Real.cos ((n : ℝ) * Real.arctan (Real.sqrt 2)) := by
  have hs2 : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs3 : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr : Real.sqrt 3 * Real.cos (Real.arctan (Real.sqrt 2)) = 1 := by
    rw [Real.cos_arctan, hs2]
    simp only [show (1 : ℝ) + 2 = 3 by norm_num, one_div]
    exact mul_inv_cancel₀ ((Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)).ne')
  induction n using Nat.twoStepInduction with
  | zero => simp [a]
  | one => simpa [a] using hr.symm
  | more n ih0 ih1 =>
      change (((2 : ℤ) * a (n + 1) - 3 * a n : ℤ) : ℝ) = _
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
      rw [ih0, ih1]
      simpa [mul_assoc] using
        (scaled_cos_add_two (Real.sqrt 3) (Real.arctan (Real.sqrt 2)) hr hs3 n).symm

lemma a_mod_three (n : ℕ) : a (n + 1) % 3 = 1 ∨ a (n + 1) % 3 = 2 := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
      change (2 * a (n + 1) - 3 * a n) % 3 = 1 ∨
        (2 * a (n + 1) - 3 * a n) % 3 = 2
      omega


lemma phase_not_rat (q : ℚ) :
    Real.arctan (Real.sqrt 2) / Real.pi ≠ (q : ℝ) := by
  intro hq
  let θ : ℝ := Real.arctan (Real.sqrt 2)
  have hθ : θ = (q : ℝ) * Real.pi := (div_eq_iff Real.pi_ne_zero).mp hq
  have hdenR : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hqden : (q : ℝ) * (q.den : ℝ) = (q.num : ℝ) := by
    rw [Rat.cast_def]
    exact div_mul_cancel₀ _ hdenR
  have hθmul : (((2 * q.den : ℕ) : ℝ) * θ) = (q.num : ℝ) * (2 * Real.pi) := by
    calc
      _ = ((q : ℝ) * (q.den : ℝ)) * (2 * Real.pi) := by
        rw [hθ]
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        ring
      _ = (q.num : ℝ) * (2 * Real.pi) := by rw [hqden]
  have hcos : Real.cos (((2 * q.den : ℕ) : ℝ) * θ) = 1 := by
    rw [hθmul]
    exact Real.cos_int_mul_two_pi q.num
  have hpow : (Real.sqrt (3 : ℝ)) ^ (2 * q.den) = (3 : ℝ) ^ q.den := by
    rw [pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have haR : (a (2 * q.den) : ℝ) = (3 : ℝ) ^ q.den := by
    rw [a_cosine]
    change (Real.sqrt (3 : ℝ)) ^ (2 * q.den) *
      Real.cos (((2 * q.den : ℕ) : ℝ) * θ) = (3 : ℝ) ^ q.den
    rw [hcos, hpow, mul_one]
  have ha : a (2 * q.den) = (3 : ℤ) ^ q.den := by
    apply Int.cast_injective (α := ℝ)
    simpa only [Int.cast_pow, Int.cast_ofNat] using haR
  have hpmod : (3 : ℤ) ^ q.den % 3 = 0 := by
    obtain ⟨d, hd⟩ : ∃ d : ℕ, q.den = d + 1 := ⟨q.den - 1, by have := q.den_pos; omega⟩
    rw [hd, pow_succ]
    omega
  have hindex : 2 * q.den - 1 + 1 = 2 * q.den := by
    have := q.den_pos
    omega
  have hm := a_mod_three (2 * q.den - 1)
  rw [hindex, ha, hpmod] at hm
  omega

lemma logb_three_not_rat (q : ℚ) : Real.logb 10 3 ≠ (q : ℝ) := by
  intro hq
  have hqposR : (0 : ℝ) < q := by
    rw [← hq]
    exact Real.logb_pos (by norm_num : (1 : ℝ) < 10) (by norm_num : (1 : ℝ) < 3)
  have hqpos : (0 : ℚ) < q := Rat.cast_pos.mp hqposR
  have hnumpos : (0 : ℤ) < q.num := Rat.num_pos.mpr hqpos
  have hmpos : 0 < q.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt hnumpos)
  have hnum : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg hnumpos.le
  have hnumR : (q.num : ℝ) = (q.num.natAbs : ℝ) := by
    have hcast := congrArg (Int.cast : ℤ → ℝ) hnum
    simpa only [Int.cast_natCast] using hcast.symm
  have hdenR : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hqden : (q : ℝ) * (q.den : ℝ) = (q.num : ℝ) := by
    rw [Rat.cast_def]
    exact div_mul_cancel₀ _ hdenR
  have hlog10 : Real.log (10 : ℝ) ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 10)).ne'
  have hlogq : Real.log (3 : ℝ) = (q : ℝ) * Real.log 10 :=
    (div_eq_iff hlog10).mp hq
  have hlogs : Real.log ((3 : ℝ) ^ q.den) = Real.log ((10 : ℝ) ^ q.num.natAbs) := by
    rw [Real.log_pow, Real.log_pow, hlogq]
    calc
      _ = ((q : ℝ) * (q.den : ℝ)) * Real.log 10 := by ring
      _ = (q.num.natAbs : ℝ) * Real.log 10 := by rw [hqden, hnumR]
  have hpR : (3 : ℝ) ^ q.den = (10 : ℝ) ^ q.num.natAbs :=
    Real.log_injOn_pos (pow_pos (by norm_num : (0 : ℝ) < 3) _)
      (pow_pos (by norm_num : (0 : ℝ) < 10) _) hlogs
  have hpN : (3 : ℕ) ^ q.den = (10 : ℕ) ^ q.num.natAbs := by
    apply Nat.cast_injective (R := ℝ)
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hpR
  have h3 : (3 : ℕ) ^ q.den % 2 = 1 := by simp [Nat.pow_mod]
  have h10 : (10 : ℕ) ^ q.num.natAbs % 2 = 0 := by
    rw [Nat.pow_mod]
    simp [Nat.ne_of_gt hmpos]
  have hmod := congrArg (fun n : ℕ => n % 2) hpN
  rw [h3, h10] at hmod
  omega

lemma logb_sqrt_three_not_rat (q : ℚ) : Real.logb 10 (Real.sqrt 3) ≠ (q : ℝ) := by
  intro hq
  have hs : Real.logb 10 3 = 2 * Real.logb 10 (Real.sqrt 3) := by
    have h := Real.logb_pow 10 (Real.sqrt 3) 2
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at h
    simpa using h
  apply logb_three_not_rat (2 * q)
  rw [hs, hq]
  simp only [Rat.cast_mul, Rat.cast_ofNat]

lemma independent_of_mixed (x y : ℝ)
    (hx : ∀ q : ℚ, x ≠ (q : ℝ)) (hy : ∀ q : ℚ, y ≠ (q : ℝ))
    (hmixed : ∀ q₀ q₁ q₂ : ℚ, q₁ ≠ 0 → q₂ ≠ 0 →
      (q₀ : ℝ) + (q₁ : ℝ) * x + (q₂ : ℝ) * y ≠ 0) :
    ∀ q₀ q₁ q₂ : ℚ,
      (q₀ : ℝ) + (q₁ : ℝ) * x + (q₂ : ℝ) * y = 0 →
        q₀ = 0 ∧ q₁ = 0 ∧ q₂ = 0 := by
  intro q₀ q₁ q₂ h
  by_cases hq₁ : q₁ = 0
  · subst q₁
    by_cases hq₂ : q₂ = 0
    · subst q₂
      have hq₀ : (q₀ : ℝ) = 0 := by simpa using h
      exact ⟨by exact_mod_cast hq₀, rfl, rfl⟩
    · exfalso
      apply hy (-q₀ / q₂)
      have hq₂R : (q₂ : ℝ) ≠ 0 := by exact_mod_cast hq₂
      simp only [Rat.cast_div, Rat.cast_neg]
      apply (eq_div_iff hq₂R).2
      simp only [Rat.cast_zero, zero_mul, add_zero] at h
      nlinarith
  · by_cases hq₂ : q₂ = 0
    · subst q₂
      exfalso
      apply hx (-q₀ / q₁)
      have hq₁R : (q₁ : ℝ) ≠ 0 := by exact_mod_cast hq₁
      simp only [Rat.cast_div, Rat.cast_neg]
      apply (eq_div_iff hq₁R).2
      simp only [Rat.cast_zero, zero_mul, add_zero] at h
      nlinarith
    · exact False.elim (hmixed q₀ q₁ q₂ hq₁ hq₂ h)

lemma arithmetic_independence (hmixed : H1) :
    ∀ q₀ q₁ q₂ : ℚ,
      (q₀ : ℝ) + (q₁ : ℝ) * Real.logb 10 (Real.sqrt 3) +
        (q₂ : ℝ) * (Real.arctan (Real.sqrt 2) / Real.pi) = 0 →
        q₀ = 0 ∧ q₁ = 0 ∧ q₂ = 0 := by
  exact independent_of_mixed (Real.logb 10 (Real.sqrt 3))
    (Real.arctan (Real.sqrt 2) / Real.pi) logb_sqrt_three_not_rat phase_not_rat hmixed

theorem main : H1 → H2 → type_of% @OeisA87455.conjecture := by
  intro h₁ h₂
  exact h₂ (Real.sqrt 3) (Real.arctan (Real.sqrt 2)) OeisA87455.a
    (Real.sqrt_pos.2 (by norm_num)) (arithmetic_independence h₁) a_cosine

end OMA.R_OeisA87455_conjecture_R1
