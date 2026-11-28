import OMAStatements.S_oeis_a262965

namespace OMA.P_oeis_a262965

lemma pf_two_pow_mul (p j : ℕ) (hp : p.Prime) (hj : j ≠ 0) :
    (p * 2 ^ j).primeFactors = {p, 2} := by
  rw [Nat.primeFactors_mul hp.ne_zero (by positivity), hp.primeFactors,
    Nat.primeFactors_prime_pow hj Nat.prime_two]
  rfl

end OMA.P_oeis_a262965

/-- Witnesses: `k = 2 * 3^4 = 162` for `p = 2`, and `k = p * 2^φ(p+2)` for odd primes `p`. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a262965.main := by
  intro n _
  set p := Nat.nth Nat.Prime (n - 1) with hpdef
  have hp : p.Prime := Nat.prime_nth_prime _
  rcases hp.eq_two_or_odd' with h2 | hodd
  · refine ⟨2 * 3 ^ 4, by norm_num, ?_⟩
    rw [h2]
    have : (2 * 3 ^ 4).primeFactors = {2, 3} := by
      rw [Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.prime_two.primeFactors,
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
      rfl
    unfold OMA.S_oeis_a262965.sopf
    rw [this]
    decide
  · have hne : p ≠ 2 := by rintro h; rw [h] at hodd; exact absurd hodd (by decide)
    have hφ : (p + 2).totient ≠ 0 := by
      rw [Ne, Nat.totient_eq_zero]; omega
    refine ⟨p * 2 ^ (p + 2).totient, by have := hp.pos; positivity, ?_⟩
    unfold OMA.S_oeis_a262965.sopf
    rw [OMA.P_oeis_a262965.pf_two_pow_mul p _ hp hφ, Finset.sum_pair hne]
    have hcop : Nat.Coprime 2 (p + 2) := by
      rw [Nat.coprime_two_left]
      exact hodd.add_even even_two
    have h1 : 2 ^ (p + 2).totient ≡ 1 [MOD p + 2] := Nat.ModEq.pow_totient hcop
    have h2 : p * 2 ^ (p + 2).totient ≡ p * 1 [MOD p + 2] := h1.mul_left p
    rw [mul_one] at h2
    rw [h2]
    exact Nat.mod_eq_of_lt (by omega)
