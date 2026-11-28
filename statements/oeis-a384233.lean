import Mathlib

/-!
# A384233: column 2 of the array of numbers whose largest odd noncomposite divisor is the k-th

Source: https://oeis.org/A384233
Credit: @xor2k
Paired with OEIS A293452 as a sibling by text similarity; that entry is about a different
object, so this statement is modelled independently.

OEIS A384233 (offset 1): Square array read by upward antidiagonals: T(n,k) is the n-th number
whose largest odd noncomposite divisor is its k-th divisor, n >= 1, k >= 1.
Conjecture: T(n,2) = A061345(n).
OEIS A061345 (offset 0): Powers of odd primes. Alternatively, 1 and the odd prime powers
(p^k, p an odd prime, k >= 1).

Conventions:
* Noncomposite means 1 or a prime (OEIS A008578). Every positive m has the odd noncomposite
  divisor 1, so its largest odd noncomposite divisor exists.
* The divisors of m are listed in increasing order starting with the 1st; d is the k-th divisor
  of m iff exactly k - 1 divisors of m are smaller than d.
* T(n,k) is the n-th (1-based) positive number with this property; with the 0-based `Nat.nth`
  this is `Nat.nth (hasProperty k) (n - 1)` for n >= 1.
* A061345(n) is the n-th (0-based, as the offset is 0) power p^j (j >= 0) of an odd prime p,
  in increasing order, so A061345(0) = 1, A061345(1) = 3.
* The conjecture is stated for all n >= 1.
-/

namespace OMA.S_oeis_a384233

/-- Noncomposite: 1 or a prime. -/
def Noncomposite (d : ℕ) : Prop := d = 1 ∨ d.Prime

/-- `d` is the largest odd noncomposite divisor of `m`. -/
def IsLargestOddNoncompositeDivisor (m d : ℕ) : Prop :=
  d ∈ m.divisors ∧ Odd d ∧ Noncomposite d ∧
    ∀ e ∈ m.divisors, Odd e → Noncomposite e → e ≤ d

/-- The largest odd noncomposite divisor of `m > 0` is its `k`-th divisor. -/
def hasProperty (k m : ℕ) : Prop :=
  0 < m ∧ ∃ d, IsLargestOddNoncompositeDivisor m d ∧ (m.divisors.filter (· < d)).card + 1 = k

/-- T(n,k) for n, k >= 1: the n-th number with the property for k. -/
noncomputable def T (n k : ℕ) : ℕ := Nat.nth (hasProperty k) (n - 1)

/-- Powers of odd primes (including 1). -/
def IsOddPrimePower (m : ℕ) : Prop := ∃ p j : ℕ, p.Prime ∧ Odd p ∧ m = p ^ j

/-- A061345(n), offset 0. -/
noncomputable def A061345 (n : ℕ) : ℕ := Nat.nth IsOddPrimePower n

/-- T(n,2) = A061345(n) for every n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → T n 2 = A061345 n := by
  sorry

end OMA.S_oeis_a384233
