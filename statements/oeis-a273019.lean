import Mathlib

/-!
# A273019: a(n) = hypergeom([-2*n-1, 1/2], [2], 4) + (2*n+1)*hypergeom([-n+1/2, -n], [2], 4).

Source: https://oeis.org/A273019
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A273019 (R. J. Mathar, May 16 2016):
Conjecture: +(241*n+56) *(2*n+1) *(n+1)*a(n) +(482*n^3-25561*n^2+13831*n-56) *a(n-1)
+(-48682*n^3+225897*n^2-300131*n+125310) *a(n-2) +9*(n-2) *(2651*n-3183) *(2*n-3) *a(n-3)=0.

Conventions:
* The sequence has offset 0 (data 1, 5, 39, 321, 2675, 22483, 190345, ...).
* hypergeom([a, b], [c], z) is the Gauss hypergeometric series
  Sum_{k>=0} (a)_k*(b)_k/((c)_k*k!) * z^k, where (t)_k = t*(t+1)*...*(t+k-1) is the rising
  factorial, rendered by `(ascPochhammer ℚ k).eval t`. Everything is computed in `ℚ`.
* Both series terminate, because one upper parameter is a nonpositive integer: in the first
  one (-2*n-1)_k = 0 for every k >= 2*n+2, in the second one (-n)_k = 0 for every k >= n+1.
  The two hypergeometric values are therefore the finite sums over k < 2*n+2 and over k < n+1
  (`Finset.range (2 * n + 2)` and `Finset.range (n + 1)`), which contain every nonzero term.
* a(n) is an integer for every n; here it is a rational number, because it is defined from
  the rational terms of the two series. The recurrence is an identity in `ℚ`, with the natural
  number `n` cast to `ℚ`.
* The source gives no range for n. The recurrence is asserted for every `n ≥ 3`, which is
  exactly the range in which all the indices n, n-1, n-2, n-3 are at least the offset 0.
-/

namespace OMA.S_oeis_a273019

/-- The term number `k` of the hypergeometric series hypergeom([a, b], [c], z), that is
(a)_k*(b)_k/((c)_k*k!) * z^k with rising factorials (t)_k. -/
noncomputable def hterm (a b c z : ℚ) (k : ℕ) : ℚ :=
  (ascPochhammer ℚ k).eval a * (ascPochhammer ℚ k).eval b
    / ((ascPochhammer ℚ k).eval c * (k.factorial : ℚ)) * z ^ k

/-- A273019 (offset 0): a(n) = hypergeom([-2*n-1, 1/2], [2], 4)
+ (2*n+1)*hypergeom([-n+1/2, -n], [2], 4), both series being terminating. -/
noncomputable def a (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (2 * n + 2), hterm (-2 * (n : ℚ) - 1) (1 / 2) 2 4 k
    + (2 * (n : ℚ) + 1) * ∑ k ∈ Finset.range (n + 1), hterm (-(n : ℚ) + 1 / 2) (-(n : ℚ)) 2 4 k

/-- For every `n ≥ 3`, (241*n+56)*(2*n+1)*(n+1)*a(n) + (482*n^3-25561*n^2+13831*n-56)*a(n-1)
+ (-48682*n^3+225897*n^2-300131*n+125310)*a(n-2) + 9*(n-2)*(2651*n-3183)*(2*n-3)*a(n-3) = 0. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (241 * (n : ℚ) + 56) * (2 * (n : ℚ) + 1) * ((n : ℚ) + 1) * a n
      + (482 * (n : ℚ) ^ 3 - 25561 * (n : ℚ) ^ 2 + 13831 * (n : ℚ) - 56) * a (n - 1)
      + (-48682 * (n : ℚ) ^ 3 + 225897 * (n : ℚ) ^ 2 - 300131 * (n : ℚ) + 125310) * a (n - 2)
      + 9 * ((n : ℚ) - 2) * (2651 * (n : ℚ) - 3183) * (2 * (n : ℚ) - 3) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a273019
