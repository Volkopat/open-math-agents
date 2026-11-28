import Mathlib

/-!
# A192993: Numbers that are in more than one way the concatenation of the decimal representation of two nonzero squares.

Source: https://oeis.org/A192993
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A192993 (Klaus Brockhaus and Zak Seidov, Jul 14 2011):
a(n) = A038670(n) for all n >= 1.

Conventions:
* The sequence has offset 1 (data 164, 1441, 1625, 1961, 2564, 4841, 12116, 14449, 16400, 25625,
  46241, 48464, ...).
* A way to write N as the concatenation of the decimal representations of two nonzero squares is a
  pair of nonzero squares (u, v) with N = u*10^L + v, where L is the number of decimal digits of
  v. Since the positive squares correspond bijectively to their positive roots, `ways N` counts
  the pairs (r, s) of positive integers with N = r^2 * 10^L + s^2, L the length of `Nat.digits 10
  (s^2)`; the set is finite and `Set.ncard` is its number of elements.
* The terms of this sequence are the N with more than one way (predicate `1 < ways N`), and
  A038670 is the sequence of N with exactly two ways. a(n) and A038670(n) are `Nat.nth` of these
  predicates at n - 1 (`Nat.nth` is 0-indexed; both sequences have offset 1).
-/

namespace OMA.S_oeis_a192993

/-- The number of ways to write N as the concatenation of two nonzero squares. -/
noncomputable def ways (N : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | 0 < t.1 ∧ 0 < t.2 ∧
    t.1 ^ 2 * 10 ^ (Nat.digits 10 (t.2 ^ 2)).length + t.2 ^ 2 = N}

/-- The conjecture recorded in A192993. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    Nat.nth (fun N => 1 < ways N) (n - 1) = Nat.nth (fun N => ways N = 2) (n - 1) := by
  sorry

end OMA.S_oeis_a192993
