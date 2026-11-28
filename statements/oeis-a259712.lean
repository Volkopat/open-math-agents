import Mathlib

/-!
# A259712: Least positive integer k such that prime(k) + prime(k*n) is a square

Source: https://oeis.org/A259712
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A259712): a(n) exists for any n > 0.

(The comment states it as part of a more general conjecture on positive rationals m/n; only the
existence of a(n) for every n > 0 is formalized here.)

Conventions:
* prime(k) is the k-th prime with prime(1) = 2 (`Nat.nth Nat.Prime (k - 1)`).
* a(n) exists when some positive k has prime(k) + prime(k*n) a perfect square (`IsSquare`).
-/

namespace OMA.S_oeis_a259712

/-- The `k`-th prime, `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- Sun's conjecture on A259712: for every `n > 0` there is `k > 0` such that
`prime(k) + prime(k * n)` is a square. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ k : ℕ, 0 < k ∧ IsSquare (prime k + prime (k * n)) := by
  sorry

end OMA.S_oeis_a259712
