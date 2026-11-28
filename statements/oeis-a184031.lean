import Mathlib

/-!
# OEIS A184031: Barker's g.f. and closed forms for (n+1) X 2 arrays with equal 2 X 2 subblocks

Source: https://oeis.org/A184031 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A184031 (R. H. Hardin, Jan 08 2011), offset 1: 1/16 the number of (n+1) X 2 0..3 arrays with
all 2 X 2 subblocks having the same four values. Column 1 of A184039.
Formula section:
Empirical: a(n) = 3*a(n-1) - 6*a(n-3) + 4*a(n-4).
Conjectures from Colin Barker, Apr 10 2018: (Start)
G.f.: x*(16 - 20*x - 35*x^2 + 40*x^3) / ((1 - x)*(1 - 2*x)*(1 - 2*x^2)).
a(n) = 9*2^(n/2-1) + 9*2^(n-1) + 1 for n even.
a(n) = 9*2^(n-1) + 3*2^((n+1)/2) + 1 for n odd.
(End)

Formalization notes:
* An array is a function f : Fin (n + 1) -> Fin 2 -> Fin 4, f i j the entry in row i and column j,
  so the arrays are (n+1) X 2 with entries 0..3. Its 2 X 2 subblocks are those with upper left
  corner (i, j), i < n, j < 1; `blk f i j` is the multiset of their four values.
* Having the same four values is read as carrying the same multiset of four values (values with
  their multiplicities); every two subblocks are compared. The entry's data agree with this reading,
  and the proof file proves the first twelve terms.
* a(n) is the count divided by 16 in the natural numbers; the proof shows the count is 16 times the
  closed form, so the division is exact.
* The g.f. is the identity A(x) (1 - x)(1 - 2x)(1 - 2x^2) = x(16 - 20x - 35x^2 + 40x^3) in the
  formal power series ring over the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the
  constant term is 0).
* The closed forms are identities of natural numbers: for n even means every even n >= 2 (the offset
  is 1) and for n odd every odd n >= 1; all exponents are exact for these n. The statement is the
  conjunction of the g.f. and both closed forms.
* Controls proved in the proof file: the definition gives 16, 28, 49, 91, 169, 325, 625, 1225, 2401,
  4753, 9409, 18721 for n = 1..12, the entry's data.
-/

namespace OMA.S_oeis_a184031

open PowerSeries Finset

/-- The multiset of the four values of the 2 X 2 subblock with upper left corner (i, j). -/
def blk {n : ℕ} (f : Fin (n + 1) → Fin 2 → Fin 4) (i : Fin n) (j : Fin 1) : Multiset (Fin 4) :=
  {f i.castSucc j.castSucc, f i.castSucc j.succ, f i.succ j.castSucc, f i.succ j.succ}

/-- A184031: 1/16 the number of (n+1) X 2 arrays of 0..3 (row i, column j) with all 2 X 2
subblocks having the same four values. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 2 → Fin 4)).filter
    (fun f => ∀ i i' : Fin n, ∀ j j' : Fin 1, blk f i j = blk f i' j')).card / 16

/-- Barker's conjectures: the g.f. and the closed forms for even and odd n. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 2 * X) * (1 - 2 * X ^ 2)) =
      X * (16 - 20 * X - 35 * X ^ 2 + 40 * X ^ 3) ∧
    (∀ n : ℕ, 1 ≤ n → n % 2 = 0 → a n = 9 * 2 ^ (n / 2 - 1) + 9 * 2 ^ (n - 1) + 1) ∧
    (∀ n : ℕ, n % 2 = 1 → a n = 9 * 2 ^ (n - 1) + 3 * 2 ^ ((n + 1) / 2) + 1) := by
  sorry

end OMA.S_oeis_a184031
