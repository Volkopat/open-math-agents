import Mathlib

/-!
# A345680: integers whose trajectory under A257588 includes zero

Source: https://oeis.org/A345680
Credit: @rpabani

A257588: if n = abcd... in decimal, f(n) = |a^2 - b^2 + c^2 - d^2 + ...|.
A345680: nonnegative integers whose trajectory under iteration of f includes zero.

Conjecture (OEIS A345680): there are strings of consecutive terms of arbitrary length.

`Nat.digits` lists the digits from the least significant end, while the source starts from the
most significant digit. The two alternating sums differ at most by a sign, so the absolute value
is the same. The trajectory of n starts at n itself, so 0 is a term, as in the source.
-/

namespace OMA.S_oeis_a345680

/-- OEIS A257588: the absolute value of the alternating sum of the squares of the digits. -/
def f (n : ℕ) : ℕ :=
  (((Nat.digits 10 n).map fun d => (d : ℤ) ^ 2).alternatingSum).natAbs

/-- `n` is a term of OEIS A345680: its trajectory under `f` reaches zero. -/
def IsTerm (n : ℕ) : Prop := ∃ j : ℕ, f^[j] n = 0

theorem main : ∀ L : ℕ, ∃ m : ℕ, ∀ i : ℕ, i < L → IsTerm (m + i) := by
  sorry

end OMA.S_oeis_a345680
