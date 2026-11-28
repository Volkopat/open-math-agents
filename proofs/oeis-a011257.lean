import OMAStatements.S_oeis_a011257

/-!
Counterexample to Labos Elemer's 2001 conjecture in A011257. The integer
below is twice a square, so its divisor sum is odd. Its totient times its
divisor sum is nevertheless a square. The factorization was found by
matching the parities of the prime exponents in the products
phi(p^e) * sigma(p^e) = p^(e-1) * (p^(e+1)-1).
Santos Cruz and Luca used the same parity method for cubes in their 2015
paper (https://doi.org/10.2140/involve.2015.8.745).
-/

namespace OddDivisorSum

open OMA.S_oeis_a011257

private def k : ℕ := 2^3 * 29^2 * 37^2 * 59^2 * 313^2 * 3541^2

private def Values (n t s : ℕ) : Prop :=
  n.totient = t ∧ ArithmeticFunction.sigma 1 n = s

private theorem combine {a b t u s v : ℕ} (ha : Values a t s) (hb : Values b u v)
    (hc : a.Coprime b) : Values (a*b) (t*u) (s*v) := by
  exact ⟨by rw [Nat.totient_mul hc, ha.1, hb.1],
    by rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc, ha.2, hb.2]⟩

private theorem square_values (p : ℕ) (hp : p.Prime) :
    Values (p^2) (p*(p-1)) (1+p+p^2) := by
  constructor
  · rw [Nat.totient_prime_pow hp (by decide)]
    simp
  · rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
    simp [Finset.sum_range_succ]

private theorem values : Values k 18122928246178169057280 80238418648671308738895 := by
  have h₂ : Values (2^3) 4 15 := by
    constructor
    · rw [Nat.totient_prime_pow Nat.prime_two (by decide)]
      norm_num
    · rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
      norm_num [Finset.sum_range_succ]
  have h₂₉ := combine h₂ (square_values 29 (by norm_num)) (by decide)
  have h₃₇ := combine h₂₉ (square_values 37 (by norm_num)) (by decide)
  have h₅₉ := combine h₃₇ (square_values 59 (by norm_num)) (by decide)
  have h₃₁₃ := combine h₅₉ (square_values 313 (by norm_num)) (by decide)
  exact combine h₃₁₃ (square_values 3541 (by norm_num)) (by decide)

theorem counterexample : ¬ (type_of% @OMA.S_oeis_a011257.main) := by
  intro h
  have sigma_value : sigma k = 80238418648671308738895 := by
    rw [sigma, ← ArithmeticFunction.sigma_one_apply]
    exact values.2
  have hsq : IsSquare (k.totient * sigma k) := by
    refine ⟨38133385684419294884160, ?_⟩
    rw [values.1, sigma_value]
  have he := h k (by norm_num [k]) hsq
  rw [sigma_value] at he
  norm_num at he

end OddDivisorSum

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a011257.main) := OddDivisorSum.counterexample
