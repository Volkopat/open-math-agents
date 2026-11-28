import Mathlib

/-!
# OEIS A156894: Mathar's three recurrences for Sum_k C(n,k)*C(2n+k-1,k)

Source: https://oeis.org/A156894
Credit: @sntntHb

A156894 (offset 0): `a(n) = Sum_{k=0..n} binomial(n,k)*binomial(2*n+k-1,k)`
(data: 1, 3, 19, 138, 1059, 8378, ...). For `n = 0` the only term is
`binomial(0,0)*binomial(-1,0) = 1`.

Conjectures (R. J. Mathar, Feb 05 2015, as listed in the entry):
1) `64*n*(2*n-1)*a(n) - 16*(89*n^2 - 134*n + 63)*a(n-1) + 4*(661*n^2 - 2619*n + 2576)*a(n-2)
   - 3*(119*n^2 - 713*n + 1092)*a(n-3) + 6*(2*n-7)*(n-4)*a(n-4) = 0`;
2) `16*n*(782*n + 5365)*(2*n-1)*a(n) + 8*(3128*n^3 - 362053*n^2 + 593930*n - 290328)*a(n-1)
   - 3*(726869*n^3 - 5105981*n^2 + 11667946*n - 8715544)*a(n-2)
   + 158*(2*n-5)*(n-3)*(391*n-764)*a(n-3) = 0`;
3) `4*n*(2*n-1)*(17*n^2 - 52*n + 39)*a(n) - (1207*n^4 - 4899*n^3 + 6692*n^2 - 3504*n + 576)*a(n-1)
   + 2*(n-2)*(2*n-3)*(17*n^2 - 18*n + 4)*a(n-2) = 0`.

Formalized: in `a n` the natural-number subtraction `2*n + k - 1` only truncates when
`n = k = 0`, where `binomial(0,0) = 1 = binomial(-1,0)`, so `a` agrees with the entry. The
recurrences are stated over `ℤ` for every `n` at which all indices are nonnegative
(`n >= 4`, `n >= 3`, `n >= 2` respectively); they were checked numerically for `n < 60`.
-/

namespace OMA.S_oeis_a156894

/-- `a(n) = Sum_{k=0..n} binomial(n,k)*binomial(2*n+k-1,k)`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose k * (2 * n + k - 1).choose k

theorem main :
    (∀ n : ℕ, 4 ≤ n →
      64 * (n : ℤ) * (2 * n - 1) * a n - 16 * (89 * (n : ℤ) ^ 2 - 134 * n + 63) * a (n - 1) +
        4 * (661 * (n : ℤ) ^ 2 - 2619 * n + 2576) * a (n - 2) -
        3 * (119 * (n : ℤ) ^ 2 - 713 * n + 1092) * a (n - 3) +
        6 * (2 * (n : ℤ) - 7) * ((n : ℤ) - 4) * a (n - 4) = 0) ∧
    (∀ n : ℕ, 3 ≤ n →
      16 * (n : ℤ) * (782 * n + 5365) * (2 * n - 1) * a n +
        8 * (3128 * (n : ℤ) ^ 3 - 362053 * n ^ 2 + 593930 * n - 290328) * a (n - 1) -
        3 * (726869 * (n : ℤ) ^ 3 - 5105981 * n ^ 2 + 11667946 * n - 8715544) * a (n - 2) +
        158 * (2 * (n : ℤ) - 5) * ((n : ℤ) - 3) * (391 * n - 764) * a (n - 3) = 0) ∧
    (∀ n : ℕ, 2 ≤ n →
      4 * (n : ℤ) * (2 * n - 1) * (17 * n ^ 2 - 52 * n + 39) * a n -
        (1207 * (n : ℤ) ^ 4 - 4899 * n ^ 3 + 6692 * n ^ 2 - 3504 * n + 576) * a (n - 1) +
        2 * ((n : ℤ) - 2) * (2 * n - 3) * (17 * n ^ 2 - 18 * n + 4) * a (n - 2) = 0) := by
  sorry

end OMA.S_oeis_a156894
