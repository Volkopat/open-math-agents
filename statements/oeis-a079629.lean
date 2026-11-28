import Mathlib

/-!
# A079629: Number of twin prime pairs between p^2 and q^2 where (p,q) is the n-th twin prime pair.

Source: https://oeis.org/A079629
Credit: @azmiozgen

Conjecture (from the entry): a(n) is always positive. (The remark that a(n) might tend to infinity
is not stated here.)

Formalization notes:
* A twin prime pair is (r, r + 2) with both prime; "between p^2 and q^2" means p^2 < r and
  r + 2 < q^2 (with q = p + 2).
* Stated as: for every twin prime pair (p, p + 2) there is a twin prime pair (r, r + 2) between p^2 and
  (p + 2)^2.
* Controls (computed): for every twin pair with p < 6000 such (r, r + 2) exists; for (3, 5) the pairs
  are (11, 13) and (17, 19), matching a(1) = 2.
-/

namespace OMA.S_oeis_a079629

/-- Between the squares of the members of a twin prime pair there is always another twin pair. -/
theorem main :
    ∀ p : ℕ, p.Prime → (p + 2).Prime →
      ∃ r : ℕ, r.Prime ∧ (r + 2).Prime ∧ p ^ 2 < r ∧ r + 2 < (p + 2) ^ 2 := by
  sorry

end OMA.S_oeis_a079629
