import Mathlib

/-!
# A050189: T(n,4), array T as in A050186; a count of aperiodic binary words.

Source: https://oeis.org/A050189
Credit: @rtflynn

A050186 (https://oeis.org/A050186): T(h,k) = number of binary words of k 1's and h-k 0's which
are not a juxtaposition of 2 or more identical subwords. A050189 is the column k = 4, offset 4.

Chai Wah Wu (Jun 11 2016), in the formula section of A050189:
  a(n) = 2*a(n-1) + 2*a(n-2) - 6*a(n-3) + 6*a(n-5) - 2*a(n-6) - 2*a(n-7) + a(n-8) for n > 11
  (conjectured). G.f.: x^5*(5 + 2*x + x^2)/((1 - x)^5*(1 + x)^3) (conjectured).

Conventions:
* A binary word of length n is a `List.Vector Bool n` (`true` = 1). It has k = 4 ones when
  `true` occurs 4 times, and then h - k = n - 4 zeros.
* *A juxtaposition of 2 or more identical subwords*: the word equals `u ++ u ++ ... ++ u`
  (j copies, j ≥ 2) for some word u, written `(List.replicate j u).flatten`.
* `a n` is defined for every n. For n < 4 there is no such word, so `a n = 0`: the power series
  ∑ a(n) X^n over all n ≥ 0 is the g.f. of the entry (offset 4), and the g.f. is stated as an
  identity of formal power series over ℚ, (∑ a(n) X^n) * (1 - X)^5 * (1 + X)^3 = X^5 (5 + 2X + X^2).
* The recurrence is stated in ℤ for every n ≥ 12 (n > 11), where all indices are ≥ 4.

Numerical check: a Python copy of the definition gives 0, 0, 0, 0, 0, 5, 12, 35, 64, 126, 200,
330, 480, 715, 980 for n = 0..14, the DATA of the entry from n = 4.
-/

namespace OMA.S_oeis_a050189

/-- A050189: the number of binary words of length n with four 1's (and n - 4 0's) that are not
a juxtaposition of 2 or more identical subwords. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {w : List.Vector Bool n // w.toList.count true = 4 ∧
    ¬ ∃ (u : List Bool) (j : ℕ), 2 ≤ j ∧ w.toList = (List.replicate j u).flatten}

/-- Wu's conjectures: the recurrence for n > 11 and the rational g.f. -/
theorem main : (∀ n : ℕ, 12 ≤ n → (a n : ℤ) = 2 * a (n - 1) + 2 * a (n - 2) - 6 * a (n - 3) +
      6 * a (n - 5) - 2 * a (n - 6) - 2 * a (n - 7) + a (n - 8)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - PowerSeries.X) ^ 5 * (1 + PowerSeries.X) ^ 3) =
      PowerSeries.X ^ 5 * (5 + 2 * PowerSeries.X + PowerSeries.X ^ 2) := by
  sorry

end OMA.S_oeis_a050189
