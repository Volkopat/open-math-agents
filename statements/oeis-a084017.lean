import Mathlib

/-!
# OEIS A084017: n-digit palindromic multiples of n with digit sum a multiple of n

The sequence a(n) is the smallest n-digit palindromic multiple of n whose
digit sum is also a multiple of n. For n = 10k it is sufficient that the
multiple is palindromic with leading zeros ignored; the entry is 0 if no
such number exists. The conjecture of Murthy and Srikanth: no entry is
zero, i.e. for every nonzero n such a multiple exists (nonvanishing needs
only existence, not smallest-ness).

Encoding: a candidate is N = P * 10 ^ z where P is a strict palindrome
(Nat.digits never has a leading zero), z is the count of ignored trailing
zeros, and the exact OEIS-generator clause is z = tz n, the decimal
10-adic valuation of n (count of trailing zeros of the index n itself).
P is nonzero (Nat.digits 10 0 = [] would give a degenerate empty
palindrome), the digit length of P plus z equals n, n divides N, and n
divides the digit sum of P (the appended zeros add nothing to the sum).

Source: https://oeis.org/A084017
-/

namespace OMA.S_oeis_a084017

/-- Number of ignored trailing zeros: the exact OEIS clause z = v_{10}(n),
    the length of the leading run of zeros of Nat.digits 10 n (little-endian
    order, so leading zeros of the digit list are trailing zeros of n). -/
def tz (x : ℕ) : ℕ := ((Nat.digits 10 x).takeWhile (· = 0)).length

/-- Per-index predicate: a qualifying n-digit palindromic multiple exists.
    Body identical to the frozen spec SpecPropA084017N and the proof goal
    finGoal (exact clause z = tz n). -/
abbrev qualifies (n : ℕ) : Prop :=
  ∃ P z : ℕ, P ≠ 0
    ∧ z = tz n
    ∧ (Nat.digits 10 P).Palindrome
    ∧ (Nat.digits 10 P).length + z = n
    ∧ n ∣ P * 10 ^ z
    ∧ n ∣ (Nat.digits 10 P).sum

/-- Conjecture: no entry of A084017 is zero. -/
theorem main : ∀ n : ℕ, n ≠ 0 → qualifies n := by
  sorry

end OMA.S_oeis_a084017
