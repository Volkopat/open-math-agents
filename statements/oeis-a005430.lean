import Mathlib

/-!
# A005430: Apéry numbers: n*C(2*n,n).

Source: https://oeis.org/A005430
Credit: @thatoneguy006

The conjecture stated here, from the entry:

  Conjecture: the terms of the inverse binomial transform are 2*A132894(n).
  - R. J. Mathar, Oct 21 2012

Definitions.
* A005430(n) = n * C(2n, n), the name of the entry, with offset 0.
* The inverse binomial transform of a sequence `a` is
  `b(n) = Sum_{k=0..n} (-1)^(n-k) * C(n, k) * a(k)` (the OEIS convention). It is taken in ℤ.
* A132894(n) (the number of H steps in all length-n left factors of Motzkin paths) is given by the
  formula of that entry, also its PARI program:
  `a(n) = Sum_{k=0..n} k*C(n,k)*C(n-k, floor((n-k)/2))`, offset 0. With it the terms are
  0, 1, 4, 15, 52, 175, 576, ..., the data of A132894.
-/

namespace OMA.S_oeis_a005430

/-- A005430: the Apéry numbers `n * C(2n, n)`. -/
def a (n : ℕ) : ℤ := (n : ℤ) * ((2 * n).choose n : ℤ)

/-- A132894, by its formula `Sum_{k=0..n} k*C(n,k)*C(n-k, floor((n-k)/2))`. -/
def A132894 (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (k : ℤ) * (n.choose k : ℤ) * ((n - k).choose ((n - k) / 2) : ℤ)

/-- Mathar's conjecture: the inverse binomial transform of A005430 is twice A132894. -/
theorem main : ∀ n : ℕ,
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * (n.choose k : ℤ) * a k = 2 * A132894 n := by
  sorry

end OMA.S_oeis_a005430
