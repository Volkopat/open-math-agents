import Mathlib

/-!
# A237817: Number of primes p < n such that r = |{q <= n-p: q and q + 2 are both prime}| and r + 2 are both prime.

Source: https://oeis.org/A237817
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A237817 (Zhi-Wei Sun, Feb 13 2014),
part (i): a(n) > 0 for all n > 12.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 3, ...).
* `r m` is the number of natural numbers q <= m such that q and q + 2 are both prime
  (r(11) = 3, counting 3, 5, 11).
* `a n` is the number of primes p < n such that r(n - p) and r(n - p) + 2 are both prime.
* Only part (i) of the conjecture is formalized; part (ii) is a different statement.
-/

namespace OMA.S_oeis_a237817

/-- r(m) = number of q <= m with q and q + 2 both prime. -/
noncomputable def r (m : ℕ) : ℕ := Set.ncard {q : ℕ | q ≤ m ∧ q.Prime ∧ (q + 2).Prime}

/-- A237817: number of primes p < n such that r(n - p) and r(n - p) + 2 are both prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ | p.Prime ∧ p < n ∧ (r (n - p)).Prime ∧ (r (n - p) + 2).Prime}

/-- The conjecture of Sun, part (i): a(n) > 0 for all n > 12. -/
theorem main : ∀ n : ℕ, 12 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a237817
