import Mathlib

/-!
# A392775: Least modulus separating 2*3^(k*(k-1)/2), k = 1..n

`a(n)` is the least positive integer `m` such that the numbers `2*3^(k*(k-1)/2)` (k = 1..n)
are pairwise incongruent modulo `m`.

Conjecture (Zhi-Wei Sun, OEIS A392775): Let `c` be any integer congruent to 3 or -3 modulo 8.
For any positive integer `n`, let `m(c,n)` be the least positive integer `m` such that the `n`
numbers `2*c^(k(k-1)/2)` (k = 1..n) are pairwise incongruent modulo `m`.
(i) `m(c,n)` is prime for any integer `n ≥ |c|`. In particular, `a(n)` is prime for any
integer `n > 1`.
(ii) `lim m(c,n)/n = 4` as `n` tends to infinity.

Source: https://oeis.org/A392775
Credit: @gblacher2
-/

namespace OMA.S_oeis_a392775

/-- `m(c,n)`: the least positive integer `m` such that the `n` numbers `2*c^(k(k-1)/2)`
(`k = 1, …, n`) are pairwise incongruent modulo `m`. For `|c| > 1` these numbers are distinct,
so such an `m` exists. -/
noncomputable def leastModulus (c : ℤ) (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ∀ j ∈ Finset.Icc 1 n, ∀ k ∈ Finset.Icc 1 n,
    2 * c ^ (j * (j - 1) / 2) ≡ 2 * c ^ (k * (k - 1) / 2) [ZMOD (m : ℤ)] → j = k}

/-- The sequence A392775 itself: `a(n) = m(3,n)`. -/
noncomputable def a (n : ℕ) : ℕ := leastModulus 3 n

/-- Sun's conjecture: parts (i) and (ii), together with the stated special case for `a`. -/
theorem main :
    (∀ c : ℤ, (c ≡ 3 [ZMOD 8] ∨ c ≡ -3 [ZMOD 8]) →
      (∀ n : ℕ, 0 < n → (c.natAbs : ℕ) ≤ n → (leastModulus c n).Prime) ∧
      Filter.Tendsto (fun n : ℕ => (leastModulus c n : ℝ) / n) Filter.atTop (nhds 4)) ∧
    (∀ n : ℕ, 1 < n → (a n).Prime) := by
  sorry

end OMA.S_oeis_a392775
