import Mathlib

/-!
# A192826: Mathar's recurrence

Source: https://oeis.org/A192826
Credit: @ivillar

Status: false as stated at n = 9: with the data a(2) = 4, a(3) = 72, ..., a(9) = 1949184 the left
side equals -1494421831680 instead of 0. The recurrence fits the closed form recorded in the entry,
which is stated for n > 2 only (at n = 2 it gives 12, not a(2) = 4), and n = 9 is the one index
where the recurrence involves a(2). `main` is the corrected recurrence (n ≥ 10). For it the entry
records the conjecture only; no proof or verification is noted there. It follows from the closed
form, which is used as the definition here.

A192826 (offset 2): molecular topological indices of the folded cube graphs;
data 4, 72, 448, 2400, 13824, 72128, 389120, 1949184, 9932800, 47950848, 234160128, ...

Conjecture (R. J. Mathar, Feb 21 2020): D-finite with recurrence:
+(n-1)*(3171347*n-9561097)*a(n) +2*(-22257061*n^2+113080920*n-124259984)*a(n-1)
+8*(25480326*n^2-186826067*n+302663821)*a(n-2) +16*(-2142117*n^2+189489004*n-548366652)*a(n-3)
+64*(-46156212*n^2+185594099*n-75953597)*a(n-4) +1024*(11001336*n^2-74317052*n+114909451)*a(n-5)
+1024*(-17489828*n^2+145166555*n-279390145)*a(n-6) +20480*(530179*n-1731202)*(n-6)*a(n-7)=0.

Formalization: the entry records a(n) = 2^(n-2)*n^2*(2 + 2^(n-1) - binomial(n-1,floor((n-1)/2))) for
n > 2 (Andrew Howroyd, May 11 2017), and the data give a(2) = 4; this is the definition of a(n) used
here. The values of `a` at n < 2 lie outside the offset and are not used.
-/

namespace OMA.S_oeis_a192826

/-- a(2) = 4 and a(n) = 2^(n-2) n^2 (2 + 2^(n-1) - C(n-1, floor((n-1)/2))) for n > 2. -/
def a (n : ℕ) : ℤ :=
  if n = 2 then 4
  else 2 ^ (n - 2) * (n : ℤ) ^ 2 * (2 + 2 ^ (n - 1) - ((n - 1).choose ((n - 1) / 2) : ℤ))

/-- Mathar's conjectured recurrence for A192826, for n ≥ 10 (it fails at n = 9). -/
theorem main : ∀ n : ℕ, 10 ≤ n →
    ((n : ℤ) - 1) * (3171347 * (n : ℤ) - 9561097) * a n +
      2 * (-22257061 * (n : ℤ) ^ 2 + 113080920 * (n : ℤ) - 124259984) * a (n - 1) +
      8 * (25480326 * (n : ℤ) ^ 2 - 186826067 * (n : ℤ) + 302663821) * a (n - 2) +
      16 * (-2142117 * (n : ℤ) ^ 2 + 189489004 * (n : ℤ) - 548366652) * a (n - 3) +
      64 * (-46156212 * (n : ℤ) ^ 2 + 185594099 * (n : ℤ) - 75953597) * a (n - 4) +
      1024 * (11001336 * (n : ℤ) ^ 2 - 74317052 * (n : ℤ) + 114909451) * a (n - 5) +
      1024 * (-17489828 * (n : ℤ) ^ 2 + 145166555 * (n : ℤ) - 279390145) * a (n - 6) +
      20480 * (530179 * (n : ℤ) - 1731202) * ((n : ℤ) - 6) * a (n - 7) = 0 := by
  sorry

end OMA.S_oeis_a192826
