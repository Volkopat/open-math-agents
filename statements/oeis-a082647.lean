import Mathlib

/-!
# A082647: Number of ways n can be expressed as the sum of d consecutive positive integers where d>0 is a divisor of n.

Source: https://oeis.org/A082647
Credit: @surrenderyourfreedom

Formalizes the two formula conjectures of Omar E. Pol recorded in A082647:
* `a(n) = A067742(n) + A131576(n)` (Feb 22 2017),
* `a(n) = A001227(n) - A131576(n)` (Apr 18 2017).
The third comment of the entry (subparts of the symmetric representation of sigma(n)) is a
separate geometric conjecture and is not formalized here.

Conventions:
* Offset 1, so the conjecture is stated for every `n ≥ 1`.
* `a n` counts the divisors `d > 0` of `n` such that `n = s + (s+1) + ... + (s+d-1)` for some
  integer `s ≥ 1`, i.e. the definition of the entry read literally.
* A067742 (middle divisors): divisors `d` of `n` in `[sqrt(n/2), sqrt(2n))`, i.e.
  `n ≤ 2 d^2` and `d^2 < 2 n`.
* A131576: the number of ways to write `n` as a sum of an even number `2k` of consecutive
  positive integers. Each length gives at most one representation, so this counts the `k ≥ 1`
  for which such a representation exists (such a `k` satisfies `k ≤ n`).
* A001227: the number of odd divisors of `n`.
* The second formula is stated in `ℤ`, so the subtraction is not truncated.
-/

namespace OMA.S_oeis_a082647

open Classical

/-- `n` is the sum of `d` consecutive positive integers. -/
def IsConsecSum (n d : ℕ) : Prop :=
  ∃ s : ℕ, 0 < s ∧ ∑ i ∈ Finset.range d, (s + i) = n

/-- A082647: the number of divisors `d > 0` of `n` such that `n` is the sum of `d` consecutive
positive integers. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Nat.divisors n).filter (fun d => IsConsecSum n d)).card

/-- A067742: the number of middle divisors of `n`, i.e. divisors in `[sqrt(n/2), sqrt(2n))`. -/
def A067742 (n : ℕ) : ℕ :=
  ((Nat.divisors n).filter (fun d => n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n)).card

/-- A131576: the number of ways to write `n` as a sum of an even number of consecutive positive
integers, counted by the half-length `k ≥ 1`. -/
noncomputable def A131576 (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k => IsConsecSum n (2 * k))).card

/-- A001227: the number of odd divisors of `n`. -/
def A001227 (n : ℕ) : ℕ :=
  ((Nat.divisors n).filter (fun d => Odd d)).card

/-- Omar E. Pol's conjectures: `a(n) = A067742(n) + A131576(n)` and
`a(n) = A001227(n) - A131576(n)` for every `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = A067742 n + A131576 n ∧ (a n : ℤ) = (A001227 n : ℤ) - (A131576 n : ℤ) := by
  sorry

end OMA.S_oeis_a082647
