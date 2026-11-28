import Mathlib

/-!
# A250065: length 12 0..n arrays, no window of seven with max of two = min of other five

A250065(n) is the number of arrays `x 0, ..., x 11` (length 6+6 = 12) with entries in
0..n such that no seven consecutive terms have the maximum of some two of them equal to the
minimum of the remaining five. That is, for each window `x s, ..., x (s + 6)`
(`s = 0, ..., 5`) and each pair of distinct positions `i, j` in the window,
`max (w i) (w j)` differs from the minimum of the other five entries `w k`.
A brute-force count of this reading gives 21, 12284 for n = 1, 2, matching the listed
terms.

The offset is 1; `a 0` is not a term of the sequence and is set to 0 in the generating
function, which has no constant term.

The problem: the conjectures of Colin Barker (Aug 22 2017):
  G.f.: x*(21 + 12011*x + 757010*x^2 + 11894854*x^3 + 66128388*x^4 + 153231228*x^5
        + 158628614*x^6 + 73421530*x^7 + 14037031*x^8 + 882297*x^9 + 8616*x^10)
        / (1 - x)^13,
  a(n) = 13*a(n-1) - 78*a(n-2) + 286*a(n-3) - 715*a(n-4) + 1287*a(n-5) - 1716*a(n-6)
         + 1716*a(n-7) - 1287*a(n-8) + 715*a(n-9) - 286*a(n-10) + 78*a(n-11)
         - 13*a(n-12) + a(n-13) for n > 13.
The g.f. is stated after multiplying both sides by (1 - x)^13. (R. H. Hardin's empirical
polynomial follows from the g.f.)

Source: https://oeis.org/A250065
Credit: @VashaTS
-/

namespace OMA.S_oeis_a250065

open PowerSeries

/-- The window of seven consecutive terms starting at position `s`. -/
def window {n : ℕ} (x : Fin 12 → Fin (n + 1)) (s : Fin 6) (k : Fin 7) : ℕ :=
  (x ⟨s.val + k.val, by have := s.isLt; have := k.isLt; omega⟩).val

/-- Some two terms of `w` have maximum equal to the minimum of the remaining five. -/
def MaxPairEqMinRest (w : Fin 7 → ℕ) : Prop :=
  ∃ i j : Fin 7, i ≠ j ∧
    ((max (w i) (w j) : ℕ) : WithTop ℕ) = ({i, j}ᶜ : Finset (Fin 7)).inf fun k => (w k : WithTop ℕ)

instance (w : Fin 7 → ℕ) : Decidable (MaxPairEqMinRest w) := by
  unfold MaxPairEqMinRest; infer_instance

/-- A250065(n). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin 12 → Fin (n + 1) =>
    ∀ s : Fin 6, ¬ MaxPairEqMinRest (window x s)).card

theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 13 =
      X * (21 + 12011 * X + 757010 * X ^ 2 + 11894854 * X ^ 3 + 66128388 * X ^ 4
        + 153231228 * X ^ 5 + 158628614 * X ^ 6 + 73421530 * X ^ 7 + 14037031 * X ^ 8
        + 882297 * X ^ 9 + 8616 * X ^ 10) ∧
    ∀ n : ℕ, 13 < n →
      (a n : ℤ) = 13 * a (n - 1) - 78 * a (n - 2) + 286 * a (n - 3) - 715 * a (n - 4)
        + 1287 * a (n - 5) - 1716 * a (n - 6) + 1716 * a (n - 7) - 1287 * a (n - 8)
        + 715 * a (n - 9) - 286 * a (n - 10) + 78 * a (n - 11) - 13 * a (n - 12)
        + a (n - 13) := by
  sorry

end OMA.S_oeis_a250065
