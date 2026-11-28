import Mathlib

/-!
# Factorials in Pascal's triangle

Source: https://mathoverflow.net/questions/17058/factorials-in-pascals-triangle
Credit: @shc261392

Question. The only instances of factorials in the interior of Pascal's triangle appear to be
`C(4, 2) = 3!` and `C(10, 3) = C(16, 2) = 5!`. Are these the only ones?

Reading used here (the affirmative answer):
* The interior of Pascal's triangle is the set of entries `C(n, k)` with `2 ≤ k ≤ n - 2`; the
  entries `C(n, 1) = C(n, n - 1) = n` are excluded, as every factorial occurs there.
* By symmetry the listed solutions are `(n, k) = (4, 2), (10, 3), (10, 7), (16, 2), (16, 14)`.
  Nair and Shorey (2016) settle the question only conditionally.
-/

namespace OMA.S_mo_17058

theorem main :
    ∀ n k m : ℕ, 2 ≤ k → k + 2 ≤ n → n.choose k = m.factorial →
      (n, k) ∈ ({(4, 2), (10, 3), (10, 7), (16, 2), (16, 14)} : Set (ℕ × ℕ)) := by
  sorry

end OMA.S_mo_17058
