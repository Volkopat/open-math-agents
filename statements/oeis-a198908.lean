import Mathlib

/-!
# A198908, proper two-column arrays with at most 8 colors

R. H. Hardin's arrays introduce their colors in order of first appearance,
reading the rows from left to right. The first row is forced to be (0,1).
The finite sums below enumerate the possible actual next rows. Equal neighbors
horizontally and vertically are excluded. Index zero has generating coefficient
zero because the sequence starts at height one.

The two conclusions give Colin Barker's closed form with denominators cleared
and the coefficient identity obtained by multiplying his generating function
by (1-z)(1-3z)(1-7z)(1-13z)(1-21z)(1-43z).

Source: https://oeis.org/A198908
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a198908

open Finset

/-- Extend a proper two-column array by its remaining rows. There are t+2
already introduced colors. The last row is (a,b), with a different from b.
An old first entry either equals b or avoids a and b. Other branches introduce
one new color in either position, or two new colors in their forced order. -/
def extensions (limit : ℕ) : ℕ → ℕ → ℕ → ℕ → ℤ
  | 0, _, _, _ => 1
  | n+1, t, a, b =>
    let old := range (t+2)
    (∑ y ∈ old.erase b, extensions limit n t b y) +
    (∑ x ∈ (old.erase a).erase b, ∑ y ∈ (old.erase b).erase x, extensions limit n t x y) +
    (if t+2 < limit then
       (∑ y ∈ old.erase b, extensions limit n (t+1) (t+2) y) +
       (∑ x ∈ old.erase a, extensions limit n (t+1) x (t+2)) else 0) +
    (if t+3 < limit then extensions limit n (t+2) (t+2) (t+3) else 0)

def sequence : ℕ → ℤ
  | 0 => 0
  | m+1 => extensions 8 m 0 0 1

def delayed (d n : ℕ) : ℤ := if d ≤ n then sequence (n-d) else 0

def numerator (n : ℕ) : ℤ := if n = 1 then 1 else if n = 2 then -84 else if n = 3 then 2295 else if n = 4 then -25272 else if n = 5 then 107312 else if n = 6 then -128772 else 0

theorem main :
    (∀ m : ℕ, 2817360 * sequence (m+1) = 1036945 + 344344*3^(m+1) + 75465*7^(m+1) + 12040*13^(m+1) + 2795*21^(m+1) + 91*43^(m+1)) ∧
    (∀ n : ℕ, delayed 0 n - 88*delayed 1 n + 2613*delayed 2 n - 33232*delayed 3 n + 184531*delayed 4 n - 400344*delayed 5 n + 246519*delayed 6 n = numerator n) := by
  sorry

end OMA.S_oeis_a198908
