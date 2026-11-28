import Mathlib

/-!
# A183897: Number of nondecreasing arrangements of n+3 numbers in 0..2 with each number being the sum mod 3 of three others.

Source: https://oeis.org/A183897
Credit: @Salofe

Conjectures from Colin Barker, Apr 05 2018, quoted verbatim from the entry:
* "G.f.: x*(1 + x - x^2)*(1 + 3*x - 3*x^2) / (1 - x)^3."
* "a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>5."

Formalization notes:
* Offset 1, as in the entry (data: 1, 7, 17, 25, 34, 44, 55, ...). The value of `a 0` is never
  used.
* An arrangement of n+3 numbers in 0..2 is a sequence `x 0, x 1, ..., x (n+2)` of values in
  `Fin 3`, i.e. a function `x : Fin (n + 3) → Fin 3`; nondecreasing means `Monotone x`.
* "Each number being the sum mod 3 of three others": for every position `i` there are three
  positions `j₁, j₂, j₃`, pairwise distinct and all different from `i`, such that
  `(x j₁ + x j₂ + x j₃) mod 3 = x i`, computed in `ℕ`. The three others are three other entries
  of the arrangement, so they sit at three distinct positions (equal values at different
  positions may be used). This reading reproduces the data: a brute-force count gives
  1, 7, 17, 25, 34, 44, ..., whereas letting one position be used twice gives 9, 15, 22, ...
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, written as `PowerSeries.mk` of the function
  that is 0 at n = 0 and a(n) for n ≥ 1. The identity is stated over `ℤ⟦X⟧`, cross-multiplied by
  the denominator `(1 - x)^3`, whose constant coefficient is 1.
* The recurrence is stated in `ℤ` for every n > 5, as in the entry.
-/

namespace OMA.S_oeis_a183897

open PowerSeries

/-- A nondecreasing arrangement `x 0 ≤ x 1 ≤ ... ≤ x (N - 1)` of numbers in `0..2` in which each
number is the sum mod 3 of three others: the entries at three pairwise distinct positions, all
different from its own position. -/
def Good {N : ℕ} (x : Fin N → Fin 3) : Prop :=
  Monotone x ∧
    ∀ i : Fin N, ∃ j₁ j₂ j₃ : Fin N, j₁ ≠ i ∧ j₂ ≠ i ∧ j₃ ≠ i ∧ j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃ ∧
      ((x j₁ : ℕ) + (x j₂ : ℕ) + (x j₃ : ℕ)) % 3 = (x i : ℕ)

/-- A183897(n): the number of nondecreasing arrangements of `n + 3` numbers in `0..2` with each
number being the sum mod 3 of three others. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {x : Fin (n + 3) → Fin 3 // Good x}

/-- Barker's conjectures: the generating function `x(1 + x - x^2)(1 + 3x - 3x^2)/(1 - x)^3`, and
the recurrence `a(n) = 3a(n-1) - 3a(n-2) + a(n-3)` for `n > 5`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) *
        ((1 - X) ^ 3 : PowerSeries ℤ) =
      X * (1 + X - X ^ 2) * (1 + 3 * X - 3 * X ^ 2) ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) = 3 * (a (n - 1) : ℤ) - 3 * (a (n - 2) : ℤ) + (a (n - 3) : ℤ) := by
  sorry

end OMA.S_oeis_a183897
