import Mathlib

/-!
# A235728: a(n) = |{0 < k < n - 2: 2*m + 1, m*(m+1) - prime(m) and m*(m+1) + prime(m) are all prime with m = phi(k) + phi(n-k)/2}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A235728
Credit: @luciusacarr

Data: 0, 0, 0, 0, 0, 2, 3, 2, 4, 4, 4, 4, 4, 5, 3, 6, 4, 7, 4, 3, ... (offset 1).

The entry's comment (Zhi-Wei Sun) states a three-part conjecture. `main` states parts (i) and
(ii), as a conjunction, in the order the source gives them. Part (iii) is NOT stated: read
literally (m = sigma(k) + phi(n-k), 0 < k < n), it fails numerically at n = 448 and n = 496 (no
k < n works; checked with SymPy), so the entry's wording of (iii) most likely contains a typo, and
stating it as written would hand provers a statement that is false for a trivial reason.

Conjecture: (i) a(n) > 0 for all n > 5, and a(n) = 1 only for n = 191.
(ii) If n > 8 is not equal to 32, then there is a positive integer k < n - 2 such that 2*m + 1,
m*(m+1) - prime(m) and m*(m+1) + prime(m) are all prime, where m = sigma(k) + phi(n-k)/2, and
sigma(k) is the sum of all positive divisors of k.
(iii) If n > 444, then there is a positive integer k < n such that 2*m + 1, m^2 - prime(m) and
m^2 + prime(m) are all prime, where m = sigma(k) + phi(n-k).

Reading of the source:
* `prime(m)` is the m-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (m - 1)`; `phi` is
  `Nat.totient` and `sigma` is `ArithmeticFunction.sigma 1`.
* `k < n - 2` makes `n - k > 2`, so `phi(n-k)` is even and `phi(n-k)/2` is exact.
* The difference `m(m+1) - prime(m)` is taken in ℕ: when the true difference is negative the
  ℕ value is 0, which is not prime, just as a negative integer is not.
* a(n) counts the `k` with `0 < k < n - 2` satisfying the conditions of (i); the first 30 data
  values were recomputed from this definition. "a(n) = 1 only for n = 191" is stated, for every
  `n ≥ 1`, as: a(n) = 1 if and only if n = 191.
-/

namespace OMA.S_oeis_a235728

/-- The m-th prime, 1-indexed: `prime 1 = 2`. -/
noncomputable def prime (m : ℕ) : ℕ := Nat.nth Nat.Prime (m - 1)

/-- The condition of part (i) for a given `m`. -/
def Good (m : ℕ) : Prop :=
  (2 * m + 1).Prime ∧ (m * (m + 1) - prime m).Prime ∧ (m * (m + 1) + prime m).Prime

/-- A235728(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  open Classical in
  ((Finset.Ioo 0 (n - 2)).filter (fun k => Good (Nat.totient k + Nat.totient (n - k) / 2))).card

theorem main :
    -- (i) a(n) > 0 for all n > 5,
    (∀ n : ℕ, 5 < n → 0 < a n) ∧
    -- and a(n) = 1 only for n = 191.
    (∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ n = 191)) ∧
    -- (ii) n > 8, n ≠ 32: some 0 < k < n - 2 works with m = sigma(k) + phi(n-k)/2.
    (∀ n : ℕ, 8 < n → n ≠ 32 → ∃ k : ℕ, 0 < k ∧ k + 2 < n ∧
      Good (ArithmeticFunction.sigma 1 k + Nat.totient (n - k) / 2)) := by
  sorry

end OMA.S_oeis_a235728
