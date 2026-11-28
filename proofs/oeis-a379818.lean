import OMAStatements.S_oeis_a379818

-- Problem: A379818: a(2n+1) = a(n) for n >= 0, a(2n) = a(n) + a(n - 2^f(n)) + a(2n - 2^f(n)) + a(A025480(n-1)) for n > 0 with a(0) = 1 where f(n) = A007814(n).
-- Upstream: formal-conjectures statements/oeis-a379818.lean:0 (declaration OMA.S_oeis_a379818.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: induction on m for all k at once. For m = p + 1 put N = 2^p(2k+1); then f(N) = p,
-- N - 2^p = 2^(p+1) k, 2N - 2^p = 2^p(2(2k)+1) and A025480(N-1) = k, so the recursion gives
-- a(2^(p+1)(2k+1)) = a(2^p(2k+1)) + a(2^(p+1)k) + a(2^p(2(2k)+1)) + a(k). With
-- c(p,j) = binomial(p+2,j+1) - binomial(p,j) Pascal's rule gives c(p+1,j+1) = c(p,j) + c(p,j+1),
-- c(p+1,0) = c(p,0) + 1 and c(p,p+1) = 1, which is exactly the induction step.

namespace K07A379818

open OMA.S_oeis_a379818

theorem a_eq (n : ℕ) : a n = if _h0 : n = 0 then 1
    else if _h1 : n % 2 = 1 then a (n / 2)
    else a (n / 2) + a (n / 2 - 2 ^ A007814 (n / 2)) + a (n - 2 ^ A007814 (n / 2)) +
      a (A025480 (n / 2 - 1)) := by
  rw [a]

theorem a_odd (n : ℕ) : a (2 * n + 1) = a n := by
  rw [a_eq (2 * n + 1), dif_neg (show ¬ (2 * n + 1 = 0) by omega),
    dif_pos (show (2 * n + 1) % 2 = 1 by omega), show (2 * n + 1) / 2 = n by omega]

theorem a_even (n : ℕ) (hn : 0 < n) : a (2 * n) = a n + a (n - 2 ^ A007814 n) +
    a (2 * n - 2 ^ A007814 n) + a (A025480 (n - 1)) := by
  rw [a_eq (2 * n), dif_neg (show ¬ (2 * n = 0) by omega),
    dif_neg (show ¬ (2 * n % 2 = 1) by omega), show 2 * n / 2 = n by omega]

theorem v_odd_mul (e k : ℕ) : A007814 (2 ^ e * (2 * k + 1)) = e := by
  have h1 : (2 : ℕ) ^ e ≠ 0 := by positivity
  have h2 : 2 * k + 1 ≠ 0 := by omega
  have h3 : ¬ 2 ∣ 2 * k + 1 := by omega
  rw [A007814, padicValNat.mul (p := 2) h1 h2, padicValNat.prime_pow (p := 2) e,
    padicValNat.eq_zero_of_not_dvd h3, add_zero]

theorem A025480_val (e k : ℕ) : A025480 (2 ^ e * (2 * k + 1) - 1) = k := by
  have hq : 0 < 2 ^ e := Nat.two_pow_pos e
  have hpos : 0 < 2 ^ e * (2 * k + 1) := by positivity
  have hs : 2 ^ e * (2 * k + 1) - 1 + 1 = 2 ^ e * (2 * k + 1) := by omega
  have h5 : 2 ^ e * (2 * k + 1) = k * (2 ^ e * 2) + 2 ^ e := by ring
  have h6 : (k + 1) * (2 ^ e * 2) = k * (2 ^ e * 2) + 2 ^ e * 2 := by ring
  rw [A025480, hs, v_odd_mul, pow_succ]
  apply Nat.div_eq_of_lt_le
  · omega
  · omega

/-- The coefficient binomial(p+2, j+1) - binomial(p, j). -/
def c (p j : ℕ) : ℤ := (((Nat.choose (p + 2) (j + 1) : ℕ) : ℤ) - ((Nat.choose p j : ℕ) : ℤ))

theorem c_base : c 0 0 = 1 := by decide

theorem c_zero (p : ℕ) : c (p + 1) 0 = c p 0 + 1 := by
  rw [c, c, zero_add, Nat.choose_one_right, Nat.choose_one_right, Nat.choose_zero_right,
    Nat.choose_zero_right]
  push_cast
  ring

theorem c_succ (p j : ℕ) : c (p + 1) (j + 1) = c p j + c p (j + 1) := by
  rw [c, c, c, show p + 1 + 2 = p + 2 + 1 by ring, Nat.choose_succ_succ' (p + 2) (j + 1),
    Nat.choose_succ_succ' p j]
  push_cast
  ring

theorem c_top (p : ℕ) : c p (p + 1) = 1 := by
  rw [c, show p + 1 + 1 = p + 2 by ring, Nat.choose_self,
    Nat.choose_eq_zero_of_lt (show p < p + 1 by omega), Nat.cast_one, Nat.cast_zero, sub_zero]

theorem comb_step (p : ℕ) (X : ℕ → ℤ) :
    ∑ j ∈ Finset.range (p + 1 + 1), c (p + 1) j * X j =
      ∑ j ∈ Finset.range (p + 1), c p j * X j + X (p + 1) +
        ∑ j ∈ Finset.range (p + 1), c p j * X (j + 1) + X 0 := by
  rw [Finset.sum_range_succ' (fun j => c (p + 1) j * X j) (p + 1)]
  simp only [c_succ, c_zero, add_mul, Finset.sum_add_distrib]
  have h2 : ∑ j ∈ Finset.range (p + 1), c p (j + 1) * X (j + 1) + c p 0 * X 0 =
      ∑ j ∈ Finset.range (p + 1), c p j * X j + X (p + 1) := by
    rw [← Finset.sum_range_succ' (fun j => c p j * X j) (p + 1), Finset.sum_range_succ, c_top,
      one_mul]
  linear_combination h2

theorem key (m : ℕ) : ∀ k : ℕ, (a (2 ^ m * (2 * k + 1)) : ℤ) =
    ∑ j ∈ Finset.range (m + 1), c m j * (a (2 ^ j * k) : ℤ) := by
  induction m with
  | zero =>
    intro k
    simp [a_odd, c_base]
  | succ p ih =>
    intro k
    have hpos : 0 < 2 ^ p * (2 * k + 1) := by positivity
    have hN : 2 ^ (p + 1) * (2 * k + 1) = 2 * (2 ^ p * (2 * k + 1)) := by ring
    have e2 : 2 ^ p * (2 * k + 1) - 2 ^ p = 2 ^ (p + 1) * k := Nat.sub_eq_of_eq_add (by ring)
    have e3 : 2 * (2 ^ p * (2 * k + 1)) - 2 ^ p = 2 ^ p * (2 * (2 * k) + 1) :=
      Nat.sub_eq_of_eq_add (by ring)
    have h4 : ∑ j ∈ Finset.range (p + 1), c p j * (a (2 ^ j * (2 * k)) : ℤ) =
        ∑ j ∈ Finset.range (p + 1), c p j * (a (2 ^ (j + 1) * k) : ℤ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show 2 ^ j * (2 * k) = 2 ^ (j + 1) * k by ring]
    have h5 : (a (2 ^ 0 * k) : ℤ) = a k := by
      rw [pow_zero, one_mul]
    rw [hN, a_even _ hpos, v_odd_mul, A025480_val, e2, e3, Nat.cast_add, Nat.cast_add,
      Nat.cast_add, ih k, ih (2 * k), comb_step p (fun j => (a (2 ^ j * k) : ℤ)), h4]
    linear_combination -h5

end K07A379818

open OMA.S_oeis_a379818 in
theorem OMA.solution : type_of% @OMA.S_oeis_a379818.main := by
  intro m k
  exact K07A379818.key m k
