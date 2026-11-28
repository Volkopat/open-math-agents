import Mathlib

/-!
# A367175: a(n) = Sum_{d | n} (-1)^[d is prime] * d divides sigma(n) only for seven n

Source: https://oeis.org/A367175

A367175 (offset 1): `a(n) = Sum_{d|n} (-1)^[d is prime] * d`, where `[]` denotes the Iverson
bracket: 1, -1, -2, 3, -4, 2, -6, 11, 7, 4, -10, 18, …  That is, the divisors of `n` are added,
with the prime divisors counted negatively.

Conjecture (Peter Luschny, Nov 08 2023): `{k : a(k) divides sigma(k)} = {1, 2, 3, 6, 14, 15, 35}`.

Conventions:
- `a n` is an integer: `∑ d ∈ n.divisors, if d is prime then -d else d`.
- `sigma(k)` is the sum of the divisors of `k`, written as `∑ d ∈ k.divisors, d` and cast to
  `ℤ`; divisibility is divisibility in `ℤ`.
- `k` ranges over the positive integers (offset 1), and the set equality is stated as an
  equivalence for every `k ≥ 1`.
-/

namespace OMA.S_oeis_a367175

/-- A367175: the sum of the divisors of `n`, with prime divisors counted negatively. -/
def a (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, if Nat.Prime d then -(d : ℤ) else (d : ℤ)

theorem main :
    ∀ k : ℕ, 0 < k →
      (a k ∣ ((∑ d ∈ k.divisors, d : ℕ) : ℤ) ↔ k ∈ ({1, 2, 3, 6, 14, 15, 35} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a367175
