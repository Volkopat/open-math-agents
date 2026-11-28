import Mathlib

/-!
# A238289: Least positive integer k such that prime(k*n), prime((k+1)*n) and prime((k+2)*n) form an arithmetic progression, or 0 if such a number k does not exist.

Source: https://oeis.org/A238289
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A238289 (Zhi-Wei Sun, Feb 22 2014), part (i): We always
have 0 < a(n) < 3*prime(n) + 9.

Conventions:
* The sequence has offset 1 (data 2, 2, 17, 4, 1, 1, 59, 3, 56, 1, 39, 10, ...).
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* `a n` is the least positive integer k such that prime(k*n), prime((k+1)*n), prime((k+2)*n) form
  an arithmetic progression, as an infimum (`sInf`) over the natural numbers. In `ℕ` the infimum
  of the empty set is 0, which is exactly the OEIS convention `0 if such a number k does not
  exist`.
* Three numbers x, y, z form an arithmetic progression when x + z = 2*y.
* The claim is stated for every n >= 1 (the offset).
* Only part (i) of the conjecture is formalized; the other parts are different statements.
-/

namespace OMA.S_oeis_a238289

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- A238289: least k > 0 with prime(k*n), prime((k+1)*n), prime((k+2)*n) in arithmetic
progression (0 if there is none). -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ pr (k * n) + pr ((k + 2) * n) = 2 * pr ((k + 1) * n)}

/-- The conjecture recorded in A238289, part (i). -/
theorem main : ∀ n : ℕ, 1 ≤ n → (0 < a n ∧ a n < 3 * pr n + 9) := by
  sorry

end OMA.S_oeis_a238289
