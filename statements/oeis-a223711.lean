import Mathlib

/-!
# OEIS A223711: Barker's g.f. and closed form for n X 2 binary arrays with unimodal row and column sums

Source: https://oeis.org/A223711 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A223711 (R. H. Hardin, Mar 26 2013), offset 1: Number of n X 2 0..1 arrays with row sums and
column sums unimodal.
Formula section:
Empirical: a(n) = 7*a(n-1) - 19*a(n-2) + 25*a(n-3) - 16*a(n-4) + 4*a(n-5).
Conjectures from Colin Barker, Mar 16 2018: (Start)
G.f.: x*(2 - 3*x + 2*x^2)^2 / ((1 - x)^3*(1 - 2*x)^2).
a(n) = (-2*(2^(3+n)-9) + (5+2^(3+n))*n + n^2) / 2.
(End)

Formalization notes:
* An array is a function f : Fin n -> Fin 2 -> Fin 2, f i j the entry in row i and column j; the
  row sums are f i 0 + f i 1 (i < n) and the column sums are the sums of f i j over the rows
  (j = 0, 1), as natural numbers.
* A sequence s of length m is unimodal when there is an index k < m with s nondecreasing up to k
  (s i <= s j for i <= j <= k) and nonincreasing from k on (s j <= s i for k <= i <= j): weakly
  increasing, then weakly decreasing. This reading reproduces the entry's data (4, 16, 53, 155,
  418, 1066, 2611, 6205 for n = 1..8 by direct enumeration); a sequence of length 0 has no index k,
  which only concerns n = 0, outside the offset.
* The statement is the conjunction of the two parts of the site's problem: the g.f. as the identity
  A(x) (1 - x)^3 (1 - 2x)^2 = x(2 - 3x + 2x^2)^2 in the formal power series ring over the
  rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the
  closed form for every n >= 1 as an identity of rationals.
* Controls proved in the proof file: the definition gives 4, 16, 53, 155, 418 for n = 1..5.
-/

namespace OMA.S_oeis_a223711

open PowerSeries Finset

/-- A unimodal sequence: nondecreasing up to some index k and nonincreasing from k on. -/
def unimodal {m : ℕ} (s : Fin m → ℕ) : Prop :=
  ∃ k : Fin m, (∀ i j : Fin m, i ≤ j → j ≤ k → s i ≤ s j) ∧ (∀ i j : Fin m, k ≤ i → i ≤ j → s j ≤ s i)

instance {m : ℕ} (s : Fin m → ℕ) : Decidable (unimodal s) := by unfold unimodal; infer_instance

/-- Row sums and column sums unimodal (f i j: row i, column j). -/
def good {n : ℕ} (f : Fin n → Fin 2 → Fin 2) : Prop :=
  unimodal (fun i => (f i 0).val + (f i 1).val) ∧ unimodal (fun j => ∑ i, (f i j).val)

instance : ∀ {n : ℕ}, DecidablePred (@good n) := fun f => by unfold good; infer_instance

/-- A223711: the number of n X 2 0..1 arrays with row sums and column sums unimodal. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin n → Fin 2 → Fin 2)).filter good).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 3 * (1 - 2 * X) ^ 2) = X * (2 - 3 * X + 2 * X ^ 2) ^ 2 ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (-2 * (2 ^ (3 + n) - 9) + (5 + 2 ^ (3 + n)) * n + n ^ 2) / 2 := by
  sorry

end OMA.S_oeis_a223711
