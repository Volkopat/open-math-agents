import Mathlib

/-!
# A249280: Repeatedly apply 'Reverse and add' to n. a(n) gives the number of steps needed to reach a sum containing each digit from 0 to 9 at least once.

Source: https://oeis.org/A249280
Credit: @eltociear

The "reverse and add" map sends `m` to `m + R(m)`, where `R(m)` is the number whose decimal digits
are those of `m` in reverse order (leading zeros dropped, so `R(10) = 1`). `a(n)` (offset 1) is
the least number of steps `k` such that the `k`-th iterate of this map on `n` contains every
decimal digit `0, …, 9` at least once (`a(1) = 38`, `a(2) = 37`). The entry states two
conjectures:

1. a(n) exists for all n;
2. there exists an upper bound c such that a(n) < c for all n.

`main` is their conjunction, over the entry's range `n ≥ 1`. In conjecture 2, `a(n) < c` for the
least such `k` is equivalent to some step `k < c` reaching a pandigital number, which is how it is
stated.

`Nat.digits 10 m` lists the digits of `m` least significant first, so
`Nat.ofDigits 10 (Nat.digits 10 m).reverse` is the digit reversal of `m`.
-/

namespace OMA.S_oeis_a249280

/-- One "reverse and add" step: `m + reverse(m)` in base 10. -/
def revAdd (m : ℕ) : ℕ := m + Nat.ofDigits 10 (Nat.digits 10 m).reverse

/-- `m` contains each decimal digit `0, …, 9` at least once. -/
def IsPandigital (m : ℕ) : Prop := ∀ d < 10, d ∈ Nat.digits 10 m

/-- Conjectures 1 and 2 of OEIS A249280. -/
theorem main : (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, IsPandigital (revAdd^[k] n)) ∧
    (∃ c : ℕ, ∀ n : ℕ, 1 ≤ n → ∃ k < c, IsPandigital (revAdd^[k] n)) := by
  sorry

end OMA.S_oeis_a249280
-- ci: re-run check-proof
