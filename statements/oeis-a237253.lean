import Mathlib

/-!
# A237253: Number of ordered ways to write n = k + m with k > 0 and m > 0 such that phi(k) - 1, phi(k) + 1 and prime(prime(prime(m))) - 2 are all prime, where phi(.) is Euler's totient function.

Source: https://oeis.org/A237253
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A237253 (Zhi-Wei Sun, Feb 05 2014),
part (i): a(n) > 0 for all n > 7.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 0, 1, 0, 2, 1, 2, 2, 1, ...). `a n` is the number
  of natural numbers k with 0 < k < n (so that m = n - k > 0) such that phi(k) - 1,
  phi(k) + 1 and prime(prime(prime(n - k))) - 2 are all prime.
* phi is `Nat.totient`.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed
  (`Nat.nth Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1.
  The helper `pr k` below is prime(k).
* The natural subtractions are exact: phi(k) >= 1 for k > 0, and prime(prime(prime(m))) >= 5
  for m >= 1.
* Only part (i) of the conjecture is formalized; part (ii) is a different statement.
-/

namespace OMA.S_oeis_a237253

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- A237253: number of k with 0 < k < n such that phi(k) - 1, phi(k) + 1 and
prime(prime(prime(n - k))) - 2 are all prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {k : ℕ | 0 < k ∧ k < n ∧ (Nat.totient k - 1).Prime ∧ (Nat.totient k + 1).Prime ∧
    (pr (pr (pr (n - k))) - 2).Prime}

/-- The conjecture of Sun, part (i): a(n) > 0 for all n > 7. -/
theorem main : ∀ n : ℕ, 7 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a237253
