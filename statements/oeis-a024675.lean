import Mathlib

/-!
# A024675: Average of two consecutive odd primes

Source: https://oeis.org/A024675
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(k) = (p + q)/2` for consecutive odd primes `p < q`: `4, 6, 9, 12, …` (offset `1`).
A028334 (offset `2`) lists the differences between consecutive odd primes divided by `2`.
Conjecture (Thomas Ordowski, OEIS, 2022): `∏_{k=1}^{n} a(k) / A028334(k+1)` is an integer for
every `n ≥ 1`.

## Encoding

* With `prime i = Nat.nth Nat.Prime i` (`prime 0 = 2`), `a(k) = (prime k + prime (k+1)) / 2` and
  `A028334(k+1) = (prime (k+1) - prime k) / 2` for `k ≥ 1`.
* "The product of the quotients is an integer" is stated as divisibility of the product of the
  numerators by the product of the denominators.
-/

namespace OMA.S_oeis_a024675

/-- `a(k)`: average of the `k`-th and `(k+1)`-th odd primes. -/
noncomputable def a (k : ℕ) : ℕ := (Nat.nth Nat.Prime k + Nat.nth Nat.Prime (k + 1)) / 2

/-- `A028334(k+1)`: half the gap between the `k`-th and `(k+1)`-th odd primes. -/
noncomputable def d (k : ℕ) : ℕ := (Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k) / 2

theorem main :
    ∀ n : ℕ, 1 ≤ n → (∏ k ∈ Finset.Icc 1 n, d k) ∣ ∏ k ∈ Finset.Icc 1 n, a k := by
  sorry

end OMA.S_oeis_a024675
