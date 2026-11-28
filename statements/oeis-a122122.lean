import Mathlib

/-!
# A122122: a(0) = 1; for n>0, a(n) = 2*(n+2)*4^(n-2)-(n/4)*((3-4*n)/(1-2*n))*binomial(2*n,n).

Source: https://oeis.org/A122122
Credit: @jagong-cmu

Formalizes the two recurrences conjectured in OEIS A122122 (R. J. Mathar, Jan 04 2017):
n*(4*n^2-21*n+19)*a(n) +2*(-16*n^3+80*n^2-77*n+3)*a(n-1) +8*(2*n-3)*(4*n^2-13*n+2)*a(n-2)=0;
n*a(n) +2*(-4*n-1)*a(n-1) +72*a(n-2) +32*(4*n-15)*a(n-3) +128*(-2*n+7)*a(n-4)=0.

Conventions:
* The sequence follows the name literally, in `ℚ`: `a 0 = 1` and, for `n > 0`,
  a(n) = 2*(n+2)*4^(n-2) - (n/4)*((3-4*n)/(1-2*n))*binomial(2*n,n). The power 4^(n-2) is the
  rational power with integer exponent `n - 2` (so 4^(-1) = 1/4 at n = 1, as in the PARI
  program of the entry), and the divisions are rational divisions (1-2*n is never 0).
  The data 1, 1, 3, 13, 62, 301, ... are all integers.
* Index shift: the term a(0) = 1 was inserted on Jun 13 2022 (EXTENSIONS section), after the
  recurrences were found in 2017. Before that, the terms 1, 3, 13, 62, ... were numbered from 0,
  so the term that the recurrences call a(m) is the present a(m+1). With the present numbering
  both recurrences fail (for instance the first one gives -24 at n = 2, the second one -74 at
  n = 4); with the 2017 numbering both hold. So they are asserted with every index raised by 1:
  the first for every `n ≥ 2` and the second for every `n ≥ 4`, which are the ranges where all
  their indices are at least 0 in the 2017 numbering. (At n = 1, resp. n = 3, the recurrences
  would involve the inserted term a(0) and they fail there.)
* All terms and coefficients are compared in `ℚ`, with `n` cast to `ℚ`.
-/

namespace OMA.S_oeis_a122122

/-- a(0) = 1; for n>0, a(n) = 2*(n+2)*4^(n-2)-(n/4)*((3-4*n)/(1-2*n))*binomial(2*n,n). -/
noncomputable def a (n : ℕ) : ℚ :=
  if n = 0 then 1
  else 2 * ((n : ℚ) + 2) * (4 : ℚ) ^ ((n : ℤ) - 2)
    - ((n : ℚ) / 4) * ((3 - 4 * (n : ℚ)) / (1 - 2 * (n : ℚ))) * ((2 * n).choose n : ℚ)

/-- Both recurrences of R. J. Mathar, in the numbering of 2017 (the term a(m) there is
`a (m + 1)` here). -/
theorem main :
    (∀ n : ℕ, 2 ≤ n →
      (n : ℚ) * (4 * (n : ℚ) ^ 2 - 21 * n + 19) * a (n + 1)
        + 2 * (-16 * (n : ℚ) ^ 3 + 80 * (n : ℚ) ^ 2 - 77 * n + 3) * a n
        + 8 * (2 * (n : ℚ) - 3) * (4 * (n : ℚ) ^ 2 - 13 * n + 2) * a (n - 1) = 0) ∧
    (∀ n : ℕ, 4 ≤ n →
      (n : ℚ) * a (n + 1) + 2 * (-4 * (n : ℚ) - 1) * a n + 72 * a (n - 1)
        + 32 * (4 * (n : ℚ) - 15) * a (n - 2) + 128 * (-2 * (n : ℚ) + 7) * a (n - 3) = 0) := by
  sorry

end OMA.S_oeis_a122122
