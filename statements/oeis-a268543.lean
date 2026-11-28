import Mathlib

/-!
# A268543: Mathar's recurrence

Source: https://oeis.org/A268543
Credit: @ivillar

Status: known result. The entry records (Peter Bala, Jan 27 2018): a(n) = binomial(2*n,n)*Sum_{k = 0..n}
binomial(n,k)*binomial(2*n+k,k), and 'using this binomial sum, Maple confirms the above recurrence of
Mathar'.

A268543 (offset 0): the diagonal of 1/(1 - (y + z + x z + x w + x y w));
data 1, 8, 156, 3800, 102340, 2919168, 86427264, 2626557648, 81380484900, ...

Conjecture (R. J. Mathar, Mar 11 2016):
2*n^2*(17*n-23)*a(n) +(-1207*n^3+2840*n^2-1897*n+360)*a(n-1) + 4*(17*n-6)*(-3+2*n)^2*a(n-2) = 0.

Formalization: the entry gives the formula a(n) = binomial(2*n,n)*Sum_{k = 0..n} binomial(n,k)*
binomial(2*n+k,k) (Peter Bala, Jan 27 2018, from a theorem of Eger), and this formula is used as the
definition here (it reproduces the listed data, a(0) = 1, a(1) = 2*(1 + 3) = 8,
a(2) = 6*(1 + 10 + 15) = 156). The recurrence involves a(n-2), so it is stated for n ≥ 2; it is
checked by the data, for example at n = 2: (88)*(156) + (-1730)*(8) + (112)*(1) = 0.
-/

namespace OMA.S_oeis_a268543

/-- A268543 through the formula a(n) = binomial(2n,n) * Sum_{k=0..n} binomial(n,k)*binomial(2n+k,k). -/
def a (n : ℕ) : ℤ :=
  ((2 * n).choose n : ℤ) * ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℤ) * ((2 * n + k).choose k : ℤ))

/-- Mathar's recurrence for A268543, for n ≥ 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    2 * (n : ℤ) ^ 2 * (17 * (n : ℤ) - 23) * a n +
      (-1207 * (n : ℤ) ^ 3 + 2840 * (n : ℤ) ^ 2 - 1897 * (n : ℤ) + 360) * a (n - 1) +
      4 * (17 * (n : ℤ) - 6) * (2 * (n : ℤ) - 3) ^ 2 * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a268543
