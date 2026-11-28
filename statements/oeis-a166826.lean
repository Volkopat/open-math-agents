import Mathlib

/-!
# OEIS A166826: Connected 4-valued `n × 2` arrays with sorted rows and columns

Source: https://oeis.org/A166826 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated (Antigravity / gemini-4-neon-high), submitted by @Solfanbtc.

OEIS Name:
Number of `n × 2` `1..4` arrays containing at least one of each value, all equal values
connected, rows considered as a single number in nondecreasing order, and columns considered
as a single number in nonincreasing order.

Offset: `1, 2`.
First terms (for `n = 1, 2, 3, ...`):
`0, 4, 49, 219, 666, 1636, 3499, 6783, 12212, 20748, 33637, 52459, 79182, 116220, ...`

Conjectures and empirical formulas from the OEIS entry:
1. Empirical formula (for `n ≥ 1`):
   `a(n) = (n^6 + 18*n^5 + 100*n^4 - 731*n^2 + 792*n - 180) / 180`.
2. Conjectures from Colin Barker (Mar 26 2018):
   - Generating function:
     `G.f.: x^2 * (4 + 21*x - 40*x^2 + 22*x^3 - 2*x^4 - x^5) / (1 - x)^7`.
   - Linear recurrence:
     `a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7)`
     for `n > 7`.

Reading conventions:
* Entries in `{1, 2, 3, 4}` are represented order-isomorphically by `Fin 4`.
* Connectivity of equal values is orthogonal (4-neighbor) connectivity on the `n × 2` grid.
* Rows are read left-to-right as 2-digit numbers in `{1, 2, 3, 4}`, so nondecreasing order is
  standard lexicographic order on `Fin 2 → Fin 4`.
* Columns are read top-to-bottom as `n`-digit numbers in `{1, 2, 3, 4}`, so nonincreasing order
  means column `0` is lexicographically `≥` column `1`.
* For `n = 0`, no `0 × 2` array contains all four values, so `a 0 = 0`, aligning the formal
  power series `∑ n, a(n) X^n` with the offset-1 generating function.
-/

namespace OMA.S_oeis_a166826

/-- Two cells in an `n × 2` grid are orthogonally (4-)adjacent. -/
def GridAdj {n : ℕ} (p q : Fin n × Fin 2) : Prop :=
  (p.1 = q.1 ∧ p.2 ≠ q.2) ∨
  (p.2 = q.2 ∧ (p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val))

/-- Orthogonal adjacency restricted to cells of `A` carrying value `v`. -/
def ValueAdj {n : ℕ} (A : Fin n → Fin 2 → Fin 4) (v : Fin 4) (p q : Fin n × Fin 2) : Prop :=
  GridAdj p q ∧ A p.1 p.2 = v ∧ A q.1 q.2 = v

/-- All cells of `A` with value `v` form a single 4-connected component. -/
def ValueConnected {n : ℕ} (A : Fin n → Fin 2 → Fin 4) (v : Fin 4) : Prop :=
  ∀ p q : Fin n × Fin 2, A p.1 p.2 = v → A q.1 q.2 = v →
    Relation.ReflTransGen (ValueAdj A v) p q

/-- Lexicographic order on rows of length 2 (equivalently, 2-digit numbers in `1..4`). -/
def RowLe (r₁ r₂ : Fin 2 → Fin 4) : Prop :=
  r₁ 0 < r₂ 0 ∨ (r₁ 0 = r₂ 0 ∧ r₁ 1 ≤ r₂ 1)

/-- Rows considered as single 2-digit numbers are in nondecreasing order. -/
def RowsNondecreasing {n : ℕ} (A : Fin n → Fin 2 → Fin 4) : Prop :=
  ∀ i j : Fin n, i ≤ j → RowLe (A i) (A j)

/-- Columns considered as `n`-digit numbers (read top-to-bottom) are in nonincreasing order,
i.e., column `0` is lexicographically greater than or equal to column `1`. -/
def ColsNonincreasing {n : ℕ} (A : Fin n → Fin 2 → Fin 4) : Prop :=
  (∀ i : Fin n, A i 0 = A i 1) ∨
  ∃ i : Fin n, (∀ k : Fin n, k < i → A k 0 = A k 1) ∧ A i 1 < A i 0

/-- An `n × 2` array over `Fin 4` satisfies all conditions of OEIS A166826. -/
def IsValid {n : ℕ} (A : Fin n → Fin 2 → Fin 4) : Prop :=
  (∀ v : Fin 4, ∃ i : Fin n, ∃ j : Fin 2, A i j = v) ∧
  (∀ v : Fin 4, ValueConnected A v) ∧
  RowsNondecreasing A ∧
  ColsNonincreasing A

/-- `a n` is the `n`-th term of OEIS A166826 (offset 1, with `a 0 = 0`). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {A : Fin n → Fin 2 → Fin 4 // IsValid A}

/-- Conjunction of the empirical closed-form formula and Colin Barker's generating function and
linear recurrence conjectures for OEIS A166826. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) =
        ((n : ℚ) ^ 6 + 18 * (n : ℚ) ^ 5 + 100 * (n : ℚ) ^ 4 -
          731 * (n : ℚ) ^ 2 + 792 * (n : ℚ) - 180) / 180) ∧
    (PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 7 =
      PowerSeries.X ^ 2 *
        (4 + 21 * PowerSeries.X - 40 * PowerSeries.X ^ 2 + 22 * PowerSeries.X ^ 3 -
          2 * PowerSeries.X ^ 4 - PowerSeries.X ^ 5)) ∧
    (∀ n : ℕ, 7 < n →
      (a n : ℤ) =
        7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) +
        21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a166826
