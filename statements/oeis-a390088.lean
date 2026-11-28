import Mathlib

/-!
# A390088: a(n) is the least integer base b > 1 in which the representation of n uses only prime digits; or 0 if no such base exists.

Source: https://oeis.org/A390088
Credit: @agchua

Comment of A390088 (unsigned; the entry is by Felix Huber, Oct 29 2025):
  Conjecture: Exactly the values k = 0, 1, 4, 6, 9 satisfy a(k) = 0.
The sequence has offset 0. As in the entry's Maple and PARI programs, the bases b = 2, ..., n + 1
are searched, and the digits of n in base b are Nat.digits b n. For n ≥ 1 the bound b ≤ n + 1
changes nothing, since in every base b > n the number n is the single digit n. For n = 0 the
search range is empty, so a(0) = 0, as in the data (Nat.digits b 0 is the empty list, which
would otherwise count as a representation with only prime digits).
-/

namespace OMA.S_oeis_a390088

/-- All digits of n in base b are prime. -/
def PrimeDigits (b n : ℕ) : Prop := ∀ d ∈ Nat.digits b n, d.Prime

open scoped Classical in
/-- A390088(n): the least base b with 2 ≤ b ≤ n + 1 in which all digits of n are prime, or 0
if there is no such base. -/
noncomputable def a (n : ℕ) : ℕ :=
  if h : ∃ b, 2 ≤ b ∧ b ≤ n + 1 ∧ PrimeDigits b n then Nat.find h else 0

/-- The comment's conjecture: a(k) = 0 exactly for k = 0, 1, 4, 6, 9. -/
theorem main : ∀ k : ℕ, a k = 0 ↔ k = 0 ∨ k = 1 ∨ k = 4 ∨ k = 6 ∨ k = 9 := by
  sorry

end OMA.S_oeis_a390088
