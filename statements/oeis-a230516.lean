import Mathlib

/-!
# A230516: n = a + b + c with {x^2+x-1, x^2+x+1} a twin prime pair for x = a, b, c

Source: https://oeis.org/A230516

A230516 (offset 1): `a(n)` is the number of ways to write `n = a + b + c` with `0 < a ≤ b ≤ c`
such that `{a^2+a-1, a^2+a+1}`, `{b^2+b-1, b^2+b+1}`, `{c^2+c-1, c^2+c+1}` are twin prime pairs.
For example `a(8) = 1` since `8 = 2 + 3 + 3`, and `{5, 7}` and `{11, 13}` are twin prime pairs.

Conjecture (Zhi-Wei Sun, Oct 22 2013): `a(n) > 0` for all `n > 5`. The entry notes that this has
been verified for `n` up to `10^9` (Mauro Fiorentini, Sep 22 2023).

Since `a(n)` counts the triples `0 < a ≤ b ≤ c` with `a + b + c = n` and the three pairs twin
prime pairs, `a(n) > 0` says exactly that such a triple exists, and the conjecture is stated in
that form.

Conventions:
- `{x^2+x-1, x^2+x+1}` is a twin prime pair when both numbers are prime (they differ by 2).
- Everything is in `ℕ`; `x^2 + x - 1` is an exact subtraction for `x > 0`.
-/

namespace OMA.S_oeis_a230516

/-- `{x^2+x-1, x^2+x+1}` is a twin prime pair. -/
def IsTwinPair (x : ℕ) : Prop := Nat.Prime (x ^ 2 + x - 1) ∧ Nat.Prime (x ^ 2 + x + 1)

theorem main :
    ∀ n : ℕ, 5 < n →
      ∃ a b c : ℕ, 0 < a ∧ a ≤ b ∧ b ≤ c ∧ a + b + c = n ∧
        IsTwinPair a ∧ IsTwinPair b ∧ IsTwinPair c := by
  sorry

end OMA.S_oeis_a230516
