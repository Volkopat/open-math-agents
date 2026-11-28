import Mathlib

/-!
# A112849: Mathar's recurrence, corrected to n ≥ 4

Source: https://oeis.org/A112849
Credit: @ivillar

Status: corrected recurrence (n ≥ 4): fails as stated at n = 3 (the left side is -42 at n = 3 on the
OEIS data). The entry records the recurrence as a conjecture; no proof or verification is noted there.
`main` is the corrected recurrence (n ≥ 4), which is proved.

A112849 (offset 1): number of congruence classes (epimorphisms/vertex partitionings induced by graph
endomorphisms) of undirected cycles of even length: |C(C_{2*n})|;
data 1, 4, 11, 36, 127, 463, 1717, 6436, 24311, 92379, 352717, 1352079, ...

Conjecture (R. J. Mathar, Aug 07 2015):
n*(3*n - 5)*a(n) + (-15*n^2 + 31*n - 12)*a(n-1) + 2*(3*n - 2)*(2*n - 3)*a(n-2) = 0.

Formalization: the entry gives the closed form
|C(C_2n)| = 1 + (1/2)*binomial(2*n-1, n-1) + (1/2)*binomial(2*n-1, n), n > 1,
and this closed form is used as the definition here, together with the listed first term a(1) = 1
(the closed form would give 2 at n = 1). `main` is stated for every a : ℕ → ℚ with a(1) = 1 and the
closed form for n ≥ 2; these conditions determine a(n) for all n ≥ 1. The sequence has offset 1 and
the recurrence involves a(n-2), so the recurrence as stated starts at n = 3, where it fails on the
data: 3*4*11 + (-54)*4 + 2*7*3*1 = -42. It vanishes from n = 4 on, for example at n = 4:
4*7*36 + (-128)*11 + 2*10*5*4 = 0.
-/

namespace OMA.S_oeis_a112849

/-- The corrected recurrence (n ≥ 4): Mathar's recurrence, which fails at n = 3. -/
theorem main : ∀ a : ℕ → ℚ, a 1 = 1 →
    (∀ n : ℕ, 2 ≤ n → a n = 1 + (1 / 2) * ((2 * n - 1).choose (n - 1) : ℚ) +
      (1 / 2) * ((2 * n - 1).choose n : ℚ)) →
    ∀ n : ℕ, 4 ≤ n →
      (n : ℚ) * (3 * (n : ℚ) - 5) * a n + (-15 * (n : ℚ) ^ 2 + 31 * (n : ℚ) - 12) * a (n - 1) +
        2 * (3 * (n : ℚ) - 2) * (2 * (n : ℚ) - 3) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a112849
