import Mathlib

/-!
# OEIS A228213: Barker's generating function and closed form

Source: https://oeis.org/A228213 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Aug 16 2013), offset 1: Number of second differences of arrays of length
n + 2 of numbers in 0..3. Data: 13, 103, 625, 3151, 14053, 58975, 242461, ...
Formula lines: Conjectures from Colin Barker, Sep 09 2018:
G.f.: x*(13 + 12*x + 60*x^2 + 12*x^3 - 504*x^4 - 1584*x^5 - 1728*x^6) / ((1 - 3*x)*(1 - 4*x)).
a(n) = 4^(2+n) - 3^(2+n) for n>5.

Formalization notes:
* An array of length n + 2 of numbers in 0..3 is a function `Fin (n + 2) → Fin 4`; its second
  differences are the n integers x(i+2) - 2 x(i+1) + x(i). a(n) is the number of distinct
  second-difference sequences, `(Finset.univ.image (d2 n)).card`.
* The offset is 1, so the generating function is sum_{n >= 1} a(n) x^n, as a formal power
  series over the rationals; the identity is A = num * den^(-1) in Q[[x]].
* Natural-number subtraction in 4^(2+n) - 3^(2+n) is exact.
* Controls proved in the proof file: a(1..5) = 13, 103, 625, 3151, 14053 (kernel computation).
-/

namespace OMA.S_oeis_a228213

open Finset PowerSeries

/-- Second differences of an array of length n + 2. -/
def d2 (n : ℕ) (x : Fin (n + 2) → Fin 4) : Fin n → ℤ :=
  fun i => ((x ⟨i.1 + 2, by omega⟩ : ℕ) : ℤ) - 2 * ((x ⟨i.1 + 1, by omega⟩ : ℕ) : ℤ) +
    ((x ⟨i.1, by omega⟩ : ℕ) : ℤ)

/-- A228213(n): the number of distinct second-difference sequences. -/
def a (n : ℕ) : ℕ := (Finset.univ.image (d2 n)).card

/-- The generating function sum_{n >= 1} a(n) x^n (offset 1). -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

/-- Barker's numerator and denominator. -/
noncomputable def num : ℚ⟦X⟧ :=
  X * (13 + 12 * X + 60 * X ^ 2 + 12 * X ^ 3 - 504 * X ^ 4 - 1584 * X ^ 5 - 1728 * X ^ 6)

noncomputable def den : ℚ⟦X⟧ := (1 - 3 * X) * (1 - 4 * X)

/-- Barker's conjectures: the generating function, and a(n) = 4^(2+n) - 3^(2+n) for n > 5. -/
theorem main : A = num * den⁻¹ ∧ ∀ n : ℕ, 5 < n → a n = 4 ^ (2 + n) - 3 ^ (2 + n) := by
  sorry

end OMA.S_oeis_a228213
