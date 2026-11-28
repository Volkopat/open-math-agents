import Mathlib

/-!
# OEIS A228254: the number of third difference sequences of arrays of length n+3 over 0..2

Source: https://oeis.org/A228254 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Aug 19 2013), offset 1: Number of third differences of arrays of length n+3
of numbers in 0..2. Data: 17, 143, 621, 2059, 6305, 19171, 58025, ... Formula: Empirical:
a(n) = 5*a(n-1) - 6*a(n-2) for n>5. Conjectures from Colin Barker, Sep 10 2018: G.f.:
x*(17 + 58*x + 8*x^2 - 188*x^3 - 264*x^4) / ((1 - 2*x)*(1 - 3*x)). a(n) = 3^(3+n) - 2^(3+n) for
n>3.

Formalization notes:
* An array of length n + 3 of numbers in 0..2 is x : Fin (n + 3) -> Fin 3; its third difference
  sequence is the integer sequence x(i+3) - 3 x(i+2) + 3 x(i+1) - x(i), i < n. a(n) is the number
  of distinct third difference sequences, the size of the image of this map.
* The g.f. is Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x)*D(x) = N(x) in Q[[x]], which is
  equivalent to A = N/D because D has constant term 1.
* The closed form is stated in N for every n > 3, as in the entry (3^(3+n) > 2^(3+n), so the
  subtraction is exact).
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..11) = 17, 143, 621, 2059, 6305, 19171, 58025, 175099,
  527345, 1586131, 4766585, the entry's data.
-/

namespace OMA.S_oeis_a228254

open Finset PowerSeries

/-- The third difference sequence of an array x of length n + 3 with entries 0..2:
x(i+3) - 3 x(i+2) + 3 x(i+1) - x(i) for i < n. -/
def D {n : ℕ} (x : Fin (n + 3) → Fin 3) (i : Fin n) : ℤ :=
  ((x ⟨i.val + 3, by omega⟩).val : ℤ) - 3 * ((x ⟨i.val + 2, by omega⟩).val : ℤ) +
    3 * ((x ⟨i.val + 1, by omega⟩).val : ℤ) - ((x ⟨i.val, by omega⟩).val : ℤ)

/-- A228254(n): the number of distinct third difference sequences of arrays of length n + 3 of
numbers in 0..2. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin (n + 3) → Fin 3)).image D).card

/-- Barker's conjectures: the g.f. and the closed form for n > 3. -/
theorem main : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - 2 * X) * (1 - 3 * X)) = X * (17 + 58 * X + 8 * X ^ 2 - 188 * X ^ 3 - 264 * X ^ 4) ∧
    ∀ n : ℕ, 3 < n → a n = 3 ^ (3 + n) - 2 ^ (3 + n) := by
  sorry

end OMA.S_oeis_a228254
