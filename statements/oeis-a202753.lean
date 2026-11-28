import Mathlib

/-!
# OEIS A202753: Barker's g.f. and recurrence for n X 5 arrays rising from zero by steps 0 or 1

Source: https://oeis.org/A202753 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A202753 (R. H. Hardin, Dec 23 2011), offset 1: Number of n X 5 nonnegative integer arrays with each row and column increasing from zero by 0 or 1.
Formula section:
Empirical: a(n) = (1/302400)*n^10 + (1/10080)*n^9 + (1/1008)*n^8 + (1/336)*n^7 - (67/14400)*n^6 + (7/480)*n^5 + (1021/6048)*n^4 - (145/1008)*n^3 + (10519/12600)*n^2 - (367/420)*n + 1.
Conjectures from Colin Barker, Jun 01 2018: (Start)
G.f.: x*(1 - 6*x + 31*x^2 - 47*x^3 + 110*x^4 - 162*x^5 + 140*x^6 - 79*x^7 + 31*x^8 - 8*x^9 + x^10) / (1 - x)^11.
a(n) = 11*a(n-1) - 55*a(n-2) + 165*a(n-3) - 330*a(n-4) + 462*a(n-5) - 462*a(n-6) + 330*a(n-7) - 165*a(n-8) + 55*a(n-9) - 11*a(n-10) + a(n-11) for n>11.
(End)

Formalization notes:
* An array is a function f : Fin n -> Fin 5 -> ℕ, f i j the entry in row i and column j. Each row
  increasing from zero by 0 or 1 means f i 0 = 0 and f i (j + 1) - f i j is 0 or 1; each column
  increasing from zero by 0 or 1 means f 0 j = 0 and f (i + 1) j - f i j is 0 or 1. The steps are
  stated as f i j' = f i j or f i j' = f i j + 1 for consecutive indices, and the starts as f i j = 0
  when the index is 0, so the definition is the same for every n, including n = 0.
* a(n) is the cardinality (Set.ncard) of the set of such arrays; the set is finite since every
  entry is at most its column index.
* The statement is the conjunction of the two parts of the site's problem: the g.f. as the identity
  A(x) (1 - x)^11 = x(1 - 6x + 31x^2 - 47x^3 + 110x^4 - 162x^5 + 140x^6 - 79x^7 + 31x^8 - 8x^9 + x^10) in the formal
  power series ring over the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the
  constant term is 0), and the recurrence for every n > 11 as an identity of integers.
* Controls proved in the proof file: the definition gives 1, 5, 31, 184, 924, 3809, 13197, 39675, 106357, 259669, 586829
  for n = 1..11, the entry's data.
-/

namespace OMA.S_oeis_a202753

open PowerSeries Finset

/-- Each row and each column starts at zero and steps by 0 or 1 (f i j: row i, column j). -/
def good {n : ℕ} (f : Fin n → Fin 5 → ℕ) : Prop :=
  (∀ i j, j.val = 0 → f i j = 0) ∧ (∀ i j, i.val = 0 → f i j = 0) ∧
    (∀ i j j', j'.val = j.val + 1 → f i j' = f i j ∨ f i j' = f i j + 1) ∧
    (∀ i i' j, i'.val = i.val + 1 → f i' j = f i j ∨ f i' j = f i j + 1)

/-- A202753: the number of n X 5 nonnegative integer arrays with each row and column increasing from
zero by 0 or 1. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {f : Fin n → Fin 5 → ℕ | good f}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 11 = X * (1 - 6 * X + 31 * X ^ 2 - 47 * X ^ 3 + 110 * X ^ 4 - 162 * X ^ 5 + 140 * X ^ 6 - 79 * X ^ 7 + 31 * X ^ 8 - 8 * X ^ 9 + X ^ 10) ∧
    ∀ n : ℕ, 11 < n → (a n : ℤ) = 11 * a (n - 1) - 55 * a (n - 2) + 165 * a (n - 3) - 330 * a (n - 4) + 462 * a (n - 5) - 462 * a (n - 6) + 330 * a (n - 7) - 165 * a (n - 8) + 55 * a (n - 9) - 11 * a (n - 10) + a (n - 11) := by
  sorry

end OMA.S_oeis_a202753
