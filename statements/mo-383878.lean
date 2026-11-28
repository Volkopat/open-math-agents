import Mathlib

/-!
# Number of divisors of `2^k + 1`

Source: https://mathoverflow.net/questions/383878
Credit: @JeremyDevs

Question (MathOverflow 383878, 2021). Let `p₁, p₂, ..., pₙ` be distinct primes greater than `3`
and `k = p₁ p₂ ⋯ pₙ`. It is known that `2^k + 1` has at least `4^n` divisors (IMO Shortlist
2002, N3). Is it true that `2^k + 1` has at least `(n + 1) · 2^(2^n - n)` divisors?

`main` states the affirmative answer, which is the one indicated at the source (a comment there
says that the bound holds and can even be improved to `2^(2^n)` using the theorem of Zsigmondy).
The second, open-ended part of the question ("Can this bound be improved?") is not formalized.

Conventions:
* The primes are a family `p : Fin n → ℕ`, "distinct" is injectivity of `p`, and `n ≥ 1`.
* "Divisors" are the positive divisors, counted by `(Nat.divisors _).card`.
* The exponent `2^n - n` is a natural-number subtraction; it is exact because `n ≤ 2^n`.
-/

namespace OMA.S_mo_383878

/-- If `k` is a product of `n ≥ 1` distinct primes greater than `3`, then `2^k + 1` has at
least `(n + 1) * 2^(2^n - n)` divisors. -/
theorem main :
    ∀ (n : ℕ) (p : Fin n → ℕ), 1 ≤ n → Function.Injective p →
      (∀ i, (p i).Prime ∧ 3 < p i) →
      (n + 1) * 2 ^ (2 ^ n - n) ≤ (Nat.divisors (2 ^ (∏ i, p i) + 1)).card := by
  sorry

end OMA.S_mo_383878
