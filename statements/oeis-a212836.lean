import Mathlib

/-!
# OEIS A212836: closed form, g.f. and recurrence for 0..n arrays of length 3 with 0 never adjacent to n

Source: https://oeis.org/A212836 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

Entry (R. H. Hardin, May 28 2012), offset 1: Number of 0..n arrays of length 3 with 0 never
adjacent to n. Data: 2, 17, 50, 107, 194, 317, 482, ... The formula section states:
* Empirical: a(n) = n^3 + 3*n^2 - n - 1.
* Conjectures from Colin Barker, Jul 21 2018:
  G.f.: x*(2 + 9*x - 6*x^2 + x^3) / (1 - x)^4.
  a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>4.

Formalization notes:
* An array is a function `Fin 3 → Fin (n + 1)` (entries in 0..n). "0 never adjacent to n" means
  that no two consecutive entries are 0 and n in either order: neither (entry i, entry i+1) =
  (0, n) nor = (n, 0), for i = 0, 1.
* The entry has offset 1; `a` is defined for every n, and the statements only use n ≥ 1.
* `main` is the conjunction of the three conjectured formulas: the empirical closed form for every
  n ≥ 1 (the offset), Barker's g.f., and Barker's recurrence for n > 4. The closed form and the
  recurrence have negative coefficients and are stated in ℤ.
* The g.f. is the series Sum_{n >= 1} a(n) x^n (the term at x^0 is set to 0, matching offset 1);
  the identity A(x) = N(x)/(1 - x)^4 is stated as A(x)*(1 - x)^4 = N(x) in ℚ[[x]], which is
  equivalent because (1 - x)^4 has constant term 1.
* Controls: the definition gives a(1..7) = 2, 17, 50, 107, 194, 317, 482, as in the entry.
-/

namespace OMA.S_oeis_a212836

/-- Entries `x`, `y` (in this order) are 0 and n, or n and 0. -/
def adj (n x y : ℕ) : Prop := (x = 0 ∧ y = n) ∨ (x = n ∧ y = 0)

instance (n x y : ℕ) : Decidable (adj n x y) := by unfold adj; infer_instance

/-- A 0..n array of length 3 in which 0 is never adjacent to n. -/
def good (n : ℕ) (f : Fin 3 → Fin (n + 1)) : Prop :=
  ¬ adj n (f 0) (f 1) ∧ ¬ adj n (f 1) (f 2)

instance (n : ℕ) : DecidablePred (good n) := fun f => by unfold good; infer_instance

/-- A212836: the number of 0..n arrays of length 3 with 0 never adjacent to n. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter (good n)).card

open PowerSeries in
/-- The empirical closed form, Barker's g.f., and Barker's recurrence for n > 4. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℤ) = (n : ℤ) ^ 3 + 3 * (n : ℤ) ^ 2 - n - 1) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 4 =
      X * (2 + 9 * X - 6 * X ^ 2 + X ^ 3) ∧
    ∀ n : ℕ, 4 < n →
      (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a212836
