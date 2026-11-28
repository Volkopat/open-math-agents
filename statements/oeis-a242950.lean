import Mathlib

/-!
# A242950: Number of ordered ways to write n = k + m with k > 1 and m > 1 such that the least nonnegative residue of prime(k) modulo k is a square and the least nonnegative residue of prime(m) modulo m is a prime.

Source: https://oeis.org/A242950
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A242950 (Zhi-Wei Sun, May 27 2014), part (i): a(n) > 0
for all n > 7.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 1, 1, 0, 1, 3, 2, 1, 1, ...). `a n` is the number of
  pairs (k, m) of natural numbers with n = k + m, k > 1, m > 1, such that the least nonnegative
  residue of prime(k) modulo k is a square and the least nonnegative residue of prime(m) modulo m
  is a prime, exactly as in the OEIS name.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* The least nonnegative residue of x modulo k is `x % k`; `a square` is `IsSquare` on natural
  numbers (0 and 1 included).
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a242950

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- The condition in the name of A242950 on a tuple, for a given n. -/
def P (n : ℕ) (k m : ℕ) : Prop :=
  k + m = n ∧ 1 < k ∧ 1 < m ∧ IsSquare (pr k % k) ∧ (pr m % m).Prime

/-- A242950: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A242950. -/
theorem main : ∀ n : ℕ, 7 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a242950
