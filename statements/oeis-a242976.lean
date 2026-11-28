import Mathlib

/-!
# A242976: Number of ways to write n = i + j + k with 0 < i <= j <= k such that prime(i) mod i, prime(j) mod j and prime(k) mod k are all triangular numbers, where prime(m) mod m denotes the least nonnegative residue of prime(m) modulo m.

Source: https://oeis.org/A242976
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A242976 (Zhi-Wei Sun, May 28 2014),
part (i): a(n) > 0 for all n > 2.

Conventions:
* The sequence has offset 1 (data 0, 0, 1, 1, 1, 2, 2, 3, 4, 5, 5, 6, ...). `a n` is the number
  of triples (i, j, k) of natural numbers with 0 < i <= j <= k, i + j + k = n, such that
  prime(i) mod i, prime(j) mod j and prime(k) mod k are all triangular numbers.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed
  (`Nat.nth Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1.
* Triangular numbers are the numbers t*(t+1)/2 with t >= 0 (0 is triangular, as in the
  example of the entry for prime(1) mod 1 = 0); the condition is written 2*x = t*(t+1) to
  avoid division.
* Only part (i) of the conjecture is formalized; part (ii) is a different statement.
-/

namespace OMA.S_oeis_a242976

/-- T(m): prime(m) mod m is a triangular number t*(t+1)/2, t >= 0. -/
def T (m : ℕ) : Prop := ∃ t : ℕ, 2 * (Nat.nth Nat.Prime (m - 1) % m) = t * (t + 1)

/-- A242976: number of triples 0 < i <= j <= k with i + j + k = n and T(i), T(j), T(k). -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ × ℕ × ℕ | 0 < x.1 ∧ x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2 ∧
    x.1 + x.2.1 + x.2.2 = n ∧ T x.1 ∧ T x.2.1 ∧ T x.2.2}

/-- The conjecture of Sun, part (i): a(n) > 0 for all n > 2. -/
theorem main : ∀ n : ℕ, 2 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a242976
