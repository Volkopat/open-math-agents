import Mathlib

/-!
# A394666: a(n) = n! mod (2*n - 1).

Source: https://oeis.org/A394666
Credit: @agchua

Comment of A394666 (unsigned; the entry is by Sabuhi A. Amirov, Apr 29 2026):
  Conjecturally, a(n) = 0 iff n > 5 and 2*n - 1 is not a prime.
The sequence has offset 1. The claim is stated for n ≥ 2: at n = 1 the modulus 2n - 1 is 1, so
a(1) = 0 (as in the data and in the entry's example) while n > 5 fails; the entry's own
cross-reference (zero points are A104275 except 5, and A104275 begins with 1) also counts n = 1
among the zeros. For n ≥ 1 the subtraction 2n - 1 is exact; mod is the remainder Nat.mod.
-/

namespace OMA.S_oeis_a394666

/-- A394666(n) = n! mod (2n - 1). -/
def a (n : ℕ) : ℕ := Nat.factorial n % (2 * n - 1)

/-- The comment's conjecture, for n ≥ 2: a(n) = 0 iff n > 5 and 2n - 1 is not a prime. -/
theorem main : ∀ n : ℕ, 2 ≤ n → (a n = 0 ↔ 5 < n ∧ ¬ Nat.Prime (2 * n - 1)) := by
  sorry

end OMA.S_oeis_a394666