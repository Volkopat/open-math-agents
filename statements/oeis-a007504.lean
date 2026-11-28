import Mathlib

/-!
# A007504: sum of the first n primes

Source: https://oeis.org/A007504
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A007/A007504.seq
Credit: @Bondyboy2001

`a(n)` is the sum of the first `n` primes, with offset `0`: `a(0) = 0`, `a(1) = 2`,
`a(2) = 5`, and so on. The OEIS entry records Zhi-Wei Sun's conjectures that:

* every integer `n ≥ 5340` is `a(i) + a(j) + 2*a(k)` for positive `i,j,k`;
* every integer `n > 16866` is `p + a(k)` with `p` prime and `k` positive;
* every integer `n > 13392` is `q + a(k)` with `q` practical and `k` positive.
-/

namespace OMA.S_oeis_a007504

/-- The sum of the first `n` primes. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 n, Nat.nth Nat.Prime (i - 1)

/-- A positive practical number: every positive integer up to `n` is a sum of distinct
positive divisors of `n`. -/
def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m ≤ n →
    ∃ D : Finset ℕ, D ⊆ n.divisors ∧ m = ∑ d ∈ D, d

theorem main :
    (∀ n : ℕ, 5340 ≤ n →
      ∃ i j k : ℕ, 0 < i ∧ 0 < j ∧ 0 < k ∧ n = a i + a j + 2 * a k) ∧
    (∀ n : ℕ, 16866 < n →
      ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ n = p + a k) ∧
    (∀ n : ℕ, 13392 < n →
      ∃ q k : ℕ, IsPractical q ∧ 0 < k ∧ n = q + a k) := by
  sorry

end OMA.S_oeis_a007504
