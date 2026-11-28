import Mathlib

/-!
# A236548: Number of ways to write n = k^2 + m with k > 0 and m > 0 such that phi(k^2) + prime(m) is prime, where phi(.) is Euler's totient function.

Source: https://oeis.org/A236548
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A236548 (Zhi-Wei Sun, Jan 28 2014),
part (i): a(n) > 0 for all n > 100.

Conventions:
* The sequence has offset 1 (data 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 2, ...). `a n` is the
  number of natural numbers k > 0 with k^2 < n (so that m = n - k^2 > 0) such that
  phi(k^2) + prime(n - k^2) is prime.
* phi is `Nat.totient`.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed
  (`Nat.nth Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1.
* Only part (i) of the conjecture is formalized; part (ii) is a different statement.
-/

namespace OMA.S_oeis_a236548

/-- A236548: number of k > 0 with k^2 < n and phi(k^2) + prime(n - k^2) prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {k : ℕ | 0 < k ∧ k ^ 2 < n ∧
    (Nat.totient (k ^ 2) + Nat.nth Nat.Prime (n - k ^ 2 - 1)).Prime}

/-- The conjecture of Sun, part (i): a(n) > 0 for all n > 100. -/
theorem main : ∀ n : ℕ, 100 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a236548
