import Mathlib

/-!
# A400195: Maximum number of odd terms in a 2-dense sublist of divisors of n.

Source: https://oeis.org/A400195
Credit: @agchua

Comment and formula lines of A400195 (the entry is by Omar E. Pol, Sep 28 2026):
  Conjecture: a(n) is the ratio between the maximum number of terms in a 2-dense sublist of
  divisors of n and the ruler function of n.
  Conjecture: a(n) = A400194(n) / A001511(n).
The two conjectures say the same thing, since A400194(n) is the maximum number of terms in a
2-dense sublist of divisors of n and A001511 is the ruler function; `main` states them for
every n ≥ 1 (A400195 has offset 1), in ℚ, where the division is exact.

The 2-dense sublists of divisors of n are the pieces of the increasing list of divisors of n
when it is cut between consecutive divisors d < d' with d' > 2*d (as the entries' Mathematica
programs do with Split). Such a piece is determined by its first term a and last term b,
and its terms are the divisors d of n with a ≤ d ≤ b (`terms n a b`). `IsDense n a b` says that
a and b are divisors of n with a ≤ b, that the divisor following each divisor d with a ≤ d < b
is at most 2*d (some divisor e has d < e ≤ 2*d), that the divisor before a, if any, is less
than a/2, and that the divisor after b, if any, is greater than 2*b. `denseLists n` is the set
of pairs (a, b) of the 2-dense sublists of divisors of n.

The referenced sequences, by their own entries' definitions:
* A400194(n) (offset 1) is the maximum number of terms in a 2-dense sublist of divisors of n.
* A001511(n) (offset 1), the ruler function, is the exponent of the highest power of 2 dividing
  2n, equivalently the 2-adic valuation of 2n: `padicValNat 2 (2 * n)`.
-/

namespace OMA.S_oeis_a400195

/-- The terms of the sublist of divisors of n from a to b: the divisors d of n with a ≤ d ≤ b. -/
def terms (n a b : ℕ) : Finset ℕ := (Nat.divisors n).filter (fun d => a ≤ d ∧ d ≤ b)

/-- The divisors of n from a to b form a 2-dense sublist of divisors of n. -/
abbrev IsDense (n a b : ℕ) : Prop :=
  a ∈ Nat.divisors n ∧ b ∈ Nat.divisors n ∧ a ≤ b ∧
    (∀ d ∈ Nat.divisors n, a ≤ d → d < b → ∃ e ∈ Nat.divisors n, d < e ∧ e ≤ 2 * d) ∧
    (∀ p ∈ Nat.divisors n, p < a → 2 * p < a) ∧
    (∀ q ∈ Nat.divisors n, b < q → 2 * b < q)

/-- The 2-dense sublists of divisors of n, as pairs (first term, last term). -/
def denseLists (n : ℕ) : Finset (ℕ × ℕ) :=
  (Nat.divisors n ×ˢ Nat.divisors n).filter (fun p => IsDense n p.1 p.2)

/-- A400195(n): the maximum number of odd terms in a 2-dense sublist of divisors of n. -/
def a (n : ℕ) : ℕ := (denseLists n).sup (fun p => ((terms n p.1 p.2).filter Odd).card)

/-- A400194(n): the maximum number of terms in a 2-dense sublist of divisors of n. -/
def a400194 (n : ℕ) : ℕ := (denseLists n).sup (fun p => (terms n p.1 p.2).card)

/-- A001511(n), the ruler function: the 2-adic valuation of 2n. -/
def a001511 (n : ℕ) : ℕ := padicValNat 2 (2 * n)

/-- The conjecture: a(n) = A400194(n) / A001511(n) for n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (a400194 n : ℚ) / (a001511 n : ℚ) := by
  sorry

end OMA.S_oeis_a400195
