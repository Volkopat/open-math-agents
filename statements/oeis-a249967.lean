import Mathlib

/-!
# A249967: length 12 0..n arrays, no window of six with max of two = min of other four

A249967(n) is the number of arrays `x 0, ..., x 11` (length 7+5 = 12) with entries in
0..n such that no six consecutive terms have the maximum of some two of them equal to the
minimum of the remaining four. That is, for each window `x s, ..., x (s + 5)`
(`s = 0, ..., 6`) and each pair of distinct positions `i, j` in the window,
`max (w i) (w j)` differs from the minimum of the other four entries `w k`.
A brute-force count of this reading gives 15, 8823 for n = 1, 2, matching the listed
terms.

The offset is 1; `a 0` is not a term of the sequence and is set to 0 in the generating
function, which has no constant term.

The problem: the conjectures of Colin Barker (Aug 21 2017):
  G.f.: x*(15 + 8628*x + 596285*x^2 + 10163642*x^3 + 60659998*x^4 + 149218290*x^5
        + 162389570*x^6 + 78777198*x^7 + 16029715*x^8 + 1141682*x^9 + 16577*x^10)
        / (1 - x)^13,
  a(n) = 13*a(n-1) - 78*a(n-2) + 286*a(n-3) - 715*a(n-4) + 1287*a(n-5) - 1716*a(n-6)
         + 1716*a(n-7) - 1287*a(n-8) + 715*a(n-9) - 286*a(n-10) + 78*a(n-11)
         - 13*a(n-12) + a(n-13) for n > 13.
The g.f. is stated after multiplying both sides by (1 - x)^13. (R. H. Hardin's empirical
polynomial follows from the g.f.)

Source: https://oeis.org/A249967
Credit: @VashaTS
-/

namespace OMA.S_oeis_a249967

open PowerSeries

/-- The window of six consecutive terms starting at position `s`. -/
def window {n : ℕ} (x : Fin 12 → Fin (n + 1)) (s : Fin 7) (k : Fin 6) : ℕ :=
  (x ⟨s.val + k.val, by have := s.isLt; have := k.isLt; omega⟩).val

/-- Some two terms of `w` have maximum equal to the minimum of the remaining four. -/
def MaxPairEqMinRest (w : Fin 6 → ℕ) : Prop :=
  ∃ i j : Fin 6, i ≠ j ∧
    ((max (w i) (w j) : ℕ) : WithTop ℕ) = ({i, j}ᶜ : Finset (Fin 6)).inf fun k => (w k : WithTop ℕ)

instance (w : Fin 6 → ℕ) : Decidable (MaxPairEqMinRest w) := by
  unfold MaxPairEqMinRest; infer_instance

/-- A249967(n). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin 12 → Fin (n + 1) =>
    ∀ s : Fin 7, ¬ MaxPairEqMinRest (window x s)).card

theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 13 =
      X * (15 + 8628 * X + 596285 * X ^ 2 + 10163642 * X ^ 3 + 60659998 * X ^ 4
        + 149218290 * X ^ 5 + 162389570 * X ^ 6 + 78777198 * X ^ 7 + 16029715 * X ^ 8
        + 1141682 * X ^ 9 + 16577 * X ^ 10) ∧
    ∀ n : ℕ, 13 < n →
      (a n : ℤ) = 13 * a (n - 1) - 78 * a (n - 2) + 286 * a (n - 3) - 715 * a (n - 4)
        + 1287 * a (n - 5) - 1716 * a (n - 6) + 1716 * a (n - 7) - 1287 * a (n - 8)
        + 715 * a (n - 9) - 286 * a (n - 10) + 78 * a (n - 11) - 13 * a (n - 12)
        + a (n - 13) := by
  sorry

end OMA.S_oeis_a249967
