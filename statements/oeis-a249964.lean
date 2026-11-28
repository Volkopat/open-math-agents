import Mathlib

/-!
# A249964: length 9 0..n arrays, no window of six with max of two = min of other four

A249964(n) is the number of arrays `x 0, ..., x 8` (length 4+5 = 9) with entries in 0..n
such that no six consecutive terms have the maximum of some two of them equal to the
minimum of the remaining four. That is, for each window `x s, ..., x (s + 5)`
(`s = 0, 1, 2, 3`) and each pair of distinct positions `i, j` in the window,
`max (w i) (w j)` differs from the minimum of the other four entries `w k`.
A brute-force count of this reading gives 15, 1593, 37584 for n = 1..3, matching the
listed terms.

The problem: the conjectures of Colin Barker (Aug 21 2017):
  G.f.: (15 + 1443*x + 22329*x^2 + 96055*x^3 + 145209*x^4 + 81921*x^5 + 15359*x^6
        + 549*x^7) / (1 - x)^10,
  a(n) = 10*a(n-1) - 45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) - 210*a(n-6)
         + 120*a(n-7) - 45*a(n-8) + 10*a(n-9) - a(n-10) for n > 10.
The offset is 1 and this g.f. starts with a(1): the coefficient of x^k is a(k + 1)
(checked against all 210 terms of the b-file). It is stated after multiplying both sides
by (1 - x)^10.

Source: https://oeis.org/A249964
Credit: @VashaTS
-/

namespace OMA.S_oeis_a249964

open PowerSeries

/-- The window of six consecutive terms starting at position `s`. -/
def window {n : ℕ} (x : Fin 9 → Fin (n + 1)) (s : Fin 4) (k : Fin 6) : ℕ :=
  (x ⟨s.val + k.val, by have := s.isLt; have := k.isLt; omega⟩).val

/-- Some two terms of `w` have maximum equal to the minimum of the remaining four. -/
def MaxPairEqMinRest (w : Fin 6 → ℕ) : Prop :=
  ∃ i j : Fin 6, i ≠ j ∧
    ((max (w i) (w j) : ℕ) : WithTop ℕ) = ({i, j}ᶜ : Finset (Fin 6)).inf fun k => (w k : WithTop ℕ)

instance (w : Fin 6 → ℕ) : Decidable (MaxPairEqMinRest w) := by
  unfold MaxPairEqMinRest; infer_instance

/-- A249964(n). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin 9 → Fin (n + 1) =>
    ∀ s : Fin 4, ¬ MaxPairEqMinRest (window x s)).card

theorem main :
    PowerSeries.mk (fun k => (a (k + 1) : ℚ)) * (1 - X) ^ 10 =
      15 + 1443 * X + 22329 * X ^ 2 + 96055 * X ^ 3 + 145209 * X ^ 4 + 81921 * X ^ 5
        + 15359 * X ^ 6 + 549 * X ^ 7 ∧
    ∀ n : ℕ, 10 < n →
      (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4)
        + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8)
        + 10 * a (n - 9) - a (n - 10) := by
  sorry

end OMA.S_oeis_a249964
