import OMAStatements.S_oeis_a000918

-- Credit: @oh-meh
open Nat

private theorem valuation (m : ℕ) :
    (catalan m).factorization 2 + 1 = (digits 2 (m+1)).sum := by
  have hc : catalan m ≠ 0 := by
    intro h
    have := succ_mul_catalan_eq_centralBinom m
    exact centralBinom_ne_zero m (by simpa [h] using this.symm)
  have hprod : catalan m * (m+1).factorial * m.factorial = (2*m).factorial := by
    rw [factorial_succ, ← mul_assoc (catalan m), mul_comm (catalan m) (m+1),
      succ_mul_catalan_eq_centralBinom, centralBinom_eq_two_mul_choose]
    simpa [show 2*m - m = m by omega] using
      choose_mul_factorial_mul_factorial (show m ≤ 2*m by omega)
  have hv := congrArg (fun z : ℕ => z.factorization 2) hprod
  simp only [Nat.factorization_mul (mul_ne_zero hc (factorial_ne_zero _)) (factorial_ne_zero _),
    Nat.factorization_mul hc (factorial_ne_zero _), Finsupp.add_apply,
    factorization_factorial_mul prime_two] at hv
  have legendre := sub_one_mul_factorization_factorial (n := m+1) prime_two
  have digitBound := sum_le_ofDigits (digits 2 (m+1)) (by decide : 1 ≤ 2)
  rw [ofDigits_digits] at digitBound
  simp only [Nat.reduceSub, one_mul] at legendre
  omega

private theorem digitBound (k : ℕ) : 2 ^ (digits 2 k).sum ≤ k + 1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases h : k = 0
    · simp [h]
    have lower := ih (k/2) (Nat.div_lt_self (by omega) (by decide))
    rw [digits_def' (by decide : 1 < 2) (by omega : 0 < k), List.sum_cons]
    rcases (show k % 2 = 0 ∨ k % 2 = 1 by omega) with even | odd
    · rw [even, zero_add]
      omega
    · rw [odd, pow_add, pow_one]
      omega

private theorem allOnes (n : ℕ) : (digits 2 (2^n-1)).sum = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 0 < 2^n := by positivity
    rw [pow_succ, show 2^n * 2 - 1 = 1 + 2*(2^n-1) by omega,
      digits_add 2 (by decide) 1 _ (by decide) (Or.inl (by decide)),
      List.sum_cons, ih]
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a000918.main := by
  intro n hn
  have hpow : 2 ≤ 2^n := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hn
  apply Eq.symm
  apply IsLeast.csInf_eq
  constructor
  · change (catalan (2^n-2)).factorization 2 = n-1
    have h := valuation (2^n-2)
    rw [show 2^n-2+1 = 2^n-1 by omega, allOnes] at h
    omega
  · intro m hm
    change (catalan m).factorization 2 = n-1 at hm
    have h := valuation m
    have heq : (digits 2 (m+1)).sum = n := by omega
    have bound := digitBound (m+1)
    rw [heq] at bound
    omega
