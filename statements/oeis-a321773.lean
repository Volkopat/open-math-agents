import Mathlib

/-!
# A321773: compositions into exactly three parts with distinct multiplicities

Source: https://oeis.org/A321773 (conjectures by Colin Barker, Dec 11 2018, and by
Bill McEachen, Aug 12 2025)

`a(n)` (offset 3) is the number of compositions of `n` into exactly three parts whose distinct
part values occur with pairwise distinct multiplicities. A composition with three parts is an
ordered triple `(x, y, z)` of positive integers with `x + y + z = n`; the multiplicity condition
says the list of multiplicities `[x, y, z].count v`, over the distinct values `v`, has no
repetition. The same definition gives `a(0) = a(1) = a(2) = 0`, consistent with the offset.

The conjectures:
* G.f. `x^3 (1 + 3x + 5x^2) / ((1 - x)^2 (1 + x) (1 + x + x^2))`, stated here without division
  as an identity of power series over `ℤ`;
* `a(n) = a(n-2) + a(n-3) - a(n-5)` for `n > 7` (written without subtraction);
* `a(n) = (3n - k)/2` where `k` runs through the cycle `(7, 6, 3, 10, 3, 6)` starting at `n = 3`,
  stated as `2 a(n) = 3n - k`.
-/

namespace OMA.S_oeis_a321773

open PowerSeries

/-- OEIS A321773. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun t : ℕ × ℕ × ℕ => 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧ t.1 + t.2.1 + t.2.2 = n ∧
      (([t.1, t.2.1, t.2.2].dedup.map (fun v => [t.1, t.2.1, t.2.2].count v)).Nodup))).card

/-- The 6-periodic correction `k` of the third conjecture, indexed from `n = 3`. -/
def kk (r : ℕ) : ℤ := [7, 6, 3, 10, 3, 6].getD r 0

theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X) * (1 + X + X ^ 2)) =
      X ^ 3 * (1 + 3 * X + 5 * X ^ 2) ∧
    (∀ n : ℕ, 7 < n → a n + a (n - 5) = a (n - 2) + a (n - 3)) ∧
    (∀ n : ℕ, 3 ≤ n → 2 * (a n : ℤ) = 3 * n - kk ((n - 3) % 6)) := by
  sorry

end OMA.S_oeis_a321773
