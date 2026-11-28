import OMAStatements.S_oeis_a259459

-- Problem: A259459: From higher-order arithmetic progressions.
-- Upstream: formal-conjectures statements/oeis-a259459.lean:0 (declaration OMA.S_oeis_a259459.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: write rV(i) = C(t(i) a) + C(s(i)) d with t(i) = i(i+1)/2, s(i) = (i-1)i(i+1)/6. For a
-- product P of m factors, (P * rV)'s d^0 and d^1 coefficients are P_0 * t a and P_1 * t a + P_0 * s,
-- so P_0 = alpha(m) a^m and a * P_1 = beta(m) a^m with alpha(m+1) = alpha(m) t(m+1),
-- beta(m+1) = beta(m) t(m+1) + alpha(m) s(m+1); hence a(n) = beta(n+2). By induction
-- beta(m) = alpha(m) m(m-1)/6, which gives 2(n+1) beta(n+3) = (n+4)(n+3)^2 beta(n+2), and then
-- beta(n+2) n! 2^n = (4)_n (3)_n (3)_n by induction (ascPochhammer_succ_eval).

namespace P1A259459

open OMA.S_oeis_a259459 Polynomial

/-- t(i) = i(i+1)/2. -/
def tB (i : ℕ) : ℚ := (i : ℚ) * ((i : ℚ) + 1) / 2

/-- s(i) = (i-1)i(i+1)/6. -/
def sB (i : ℕ) : ℚ := ((i : ℚ) - 1) * (i : ℚ) * ((i : ℚ) + 1) / 6

/-- alpha(m) = t(1) t(2) ... t(m). -/
def al : ℕ → ℚ
  | 0 => 1
  | m + 1 => al m * tB (m + 1)

/-- beta(m), the coefficient of d^1 a^(m-1) in rV(1) ... rV(m). -/
def be : ℕ → ℚ
  | 0 => 0
  | m + 1 => be m * tB (m + 1) + al m * sB (m + 1)

theorem rV_eq (i : ℕ) : rV i = C (C (tB i) * X) + C (C (sB i)) * X := rfl

theorem stepAB (p : Polynomial (Polynomial ℚ)) (u w : Polynomial ℚ) :
    (p * (C u + C w * X)).coeff 0 = p.coeff 0 * u ∧
      (p * (C u + C w * X)).coeff 1 = p.coeff 1 * u + p.coeff 0 * w := by
  have e : p * (C u + C w * X) = p * C u + (p * C w) * X := by ring
  rw [e]
  constructor
  · rw [Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_mul_X_zero, add_zero]
  · have h1 : ((p * C w) * X).coeff 1 = (p * C w).coeff 0 := Polynomial.coeff_mul_X (p * C w) 0
    rw [Polynomial.coeff_add, Polynomial.coeff_mul_C, h1, Polynomial.coeff_mul_C]

theorem invAB (m : ℕ) : (∏ i ∈ Finset.Icc 1 m, rV i).coeff 0 = C (al m) * X ^ m ∧
    X * (∏ i ∈ Finset.Icc 1 m, rV i).coeff 1 = C (be m) * X ^ m := by
  induction m with
  | zero =>
    rw [Finset.Icc_eq_empty_of_lt (show (0 : ℕ) < 1 by norm_num), Finset.prod_empty]
    refine ⟨?_, ?_⟩
    · simp [al]
    · simp [be, Polynomial.coeff_one]
  | succ m ih =>
    obtain ⟨h0, h1⟩ := ih
    obtain ⟨s0, s1⟩ := stepAB (∏ i ∈ Finset.Icc 1 m, rV i) (C (tB (m + 1)) * X) (C (sB (m + 1)))
    rw [Finset.prod_Icc_succ_top (show 1 ≤ m + 1 by omega), rV_eq (m + 1), s0, s1, h0]
    refine ⟨?_, ?_⟩
    · show C (al m) * X ^ m * (C (tB (m + 1)) * X) = C (al m * tB (m + 1)) * X ^ (m + 1)
      rw [map_mul]
      ring
    · show X * ((∏ i ∈ Finset.Icc 1 m, rV i).coeff 1 * (C (tB (m + 1)) * X) +
          C (al m) * X ^ m * C (sB (m + 1))) =
        C (be m * tB (m + 1) + al m * sB (m + 1)) * X ^ (m + 1)
      rw [map_add, map_mul, map_mul]
      linear_combination (C (tB (m + 1)) * X) * h1

theorem a_eq (n : ℕ) : a n = be (n + 2) := by
  have h := (invAB (n + 2)).2
  have h2 : (X * (∏ i ∈ Finset.Icc 1 (n + 2), rV i).coeff 1).coeff (n + 1 + 1) =
      (C (be (n + 2)) * X ^ (n + 2)).coeff (n + 1 + 1) := by
    rw [h]
  rw [Polynomial.coeff_X_mul, Polynomial.coeff_C_mul_X_pow, if_pos (show n + 1 + 1 = n + 2 by omega)] at h2
  exact h2

theorem hbe (m : ℕ) : be m = al m * ((m : ℚ) * ((m : ℚ) - 1) / 6) := by
  induction m with
  | zero =>
    show (0 : ℚ) = 1 * (((0 : ℕ) : ℚ) * (((0 : ℕ) : ℚ) - 1) / 6)
    norm_num
  | succ m ih =>
    show be m * tB (m + 1) + al m * sB (m + 1) =
      al m * tB (m + 1) * (((m + 1 : ℕ) : ℚ) * (((m + 1 : ℕ) : ℚ) - 1) / 6)
    rw [ih]
    unfold tB sB
    push_cast
    ring

theorem hb3 (n : ℕ) :
    be (n + 3) * (2 * ((n : ℚ) + 1)) = be (n + 2) * (((n : ℚ) + 4) * ((n : ℚ) + 3) ^ 2) := by
  rw [hbe (n + 3), hbe (n + 2), show al (n + 3) = al (n + 2) * tB (n + 3) from rfl]
  unfold tB
  push_cast
  ring

theorem hb2 : be 2 = 1 := by
  show (0 * tB 1 + 1 * sB 1) * tB 2 + 1 * tB 1 * sB 2 = 1
  unfold tB sB
  norm_num

theorem keyAB (n : ℕ) : be (n + 2) * ((n.factorial : ℚ) * 2 ^ n) =
    (ascPochhammer ℚ n).eval 4 * (ascPochhammer ℚ n).eval 3 * (ascPochhammer ℚ n).eval 3 := by
  induction n with
  | zero =>
    show be 2 * (((0 : ℕ).factorial : ℚ) * 2 ^ 0) =
      (ascPochhammer ℚ 0).eval 4 * (ascPochhammer ℚ 0).eval 3 * (ascPochhammer ℚ 0).eval 3
    rw [hb2]
    simp
  | succ n ih =>
    have h3 := hb3 n
    rw [show n + 1 + 2 = n + 3 from rfl, ascPochhammer_succ_eval, ascPochhammer_succ_eval,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one, pow_succ]
    linear_combination ((n.factorial : ℚ) * 2 ^ n) * h3 + (((n : ℚ) + 4) * ((n : ℚ) + 3) ^ 2) * ih

theorem hR (n : ℕ) : (ascPochhammer ℚ n).eval 4 * (ascPochhammer ℚ n).eval 3 *
    (ascPochhammer ℚ n).eval 3 / (n.factorial : ℚ) * (1 / 2 : ℚ) ^ n = be (n + 2) := by
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h2 : ((1 : ℚ) / 2) ^ n * 2 ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  rw [← keyAB n]
  calc be (n + 2) * ((n.factorial : ℚ) * 2 ^ n) / (n.factorial : ℚ) * (1 / 2 : ℚ) ^ n
      = be (n + 2) * ((n.factorial : ℚ) / (n.factorial : ℚ)) * (((1 : ℚ) / 2) ^ n * 2 ^ n) := by
        ring
    _ = be (n + 2) := by
        rw [div_self hf, h2]
        ring

end P1A259459

open OMA.S_oeis_a259459 P1A259459 in
theorem OMA.solution : type_of% @OMA.S_oeis_a259459.main := by
  congr 1
  funext n
  exact (a_eq n).trans (hR n).symm
