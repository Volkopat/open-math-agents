import Mathlib

/-!
# OEIS A208598: 4-bead zero-sum necklaces on -n..n

Source: https://oeis.org/A208598
Credit: Sudharsan Rajendiran

A208598(n) is the number of 4-bead necklaces labeled with numbers `-n..n`, not allowing reversal,
with sum zero. Colin Barker conjectured (Mar 2018) the g.f. `x(6 - x + 4x^2 - x^3)/(1 - x)^4` and the
recurrence `a(n) = 4a(n-1) - 6a(n-2) + 4a(n-3) - a(n-4)` for `n > 4`; the entry also records the
empirical formula `a(n) = (4/3)n^3 + 2n^2 + (5/3)n + 1`. We state the closed form for `n ≥ 1`
(equivalent to the g.f.) together with the recurrence.

Conventions: offset `1`; a labeling is `v : Fin 4 → ℤ` (beads in cyclic order), and two labelings
are the same necklace iff one is a rotation of the other (indices mod 4). Identities are in `ℤ`.
-/

namespace OMA.S_oeis_a208598

/-- `{-n, …, 0, …, n}` as a finite set of integers. -/
noncomputable def B (n : ℕ) : Finset ℤ := Finset.Icc (-(n : ℤ)) n

/-- Labelings `v 0, v 1, v 2, v 3` of the 4 beads with numbers in `{-n, …, n}` and sum zero. -/
noncomputable def L (n : ℕ) : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun _ => B n).filter (fun v => ∑ i, v i = 0)

open Classical in
/-- A208598(n): the number of necklaces, i.e. classes of labelings in `L n` under rotation
(`w ~ v` iff `w i = v (i + k)` for some `k`, indices mod 4; reversal not allowed). -/
noncomputable def a (n : ℕ) : ℕ :=
  ((L n).image (fun v => (L n).filter (fun w => ∃ k : Fin 4, w = fun i => v (i + k)))).card

theorem main :
    (∀ n : ℕ, 1 ≤ n → 3 * (a n : ℤ) = 4 * n ^ 3 + 6 * n ^ 2 + 5 * n + 3) ∧
    (∀ n : ℕ, 4 < n →
      (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4)) := by
  sorry

end OMA.S_oeis_a208598
