import Mathlib

/-!
# A223756: Number of n X 2 0..3 arrays with rows, antidiagonals and columns unimodal.

Source: https://oeis.org/A223756
Credit: @agchua

Colin Barker (Feb 19 2018), in the formula section of A223756:
  Conjectures from Colin Barker, Feb 19 2018: (Start)
  G.f.: x*(16 + 48*x + 420*x^2 - 208*x^3 + 1140*x^4 - 1260*x^5 + 1401*x^6 - 1044*x^7 + 597*x^8 - 244*x^9 + 69*x^10 - 12*x^11 + x^12) / (1 - x)^13.
  a(n) = 13*a(n-1) - 78*a(n-2) + 286*a(n-3) - 715*a(n-4) + 1287*a(n-5) - 1716*a(n-6) + 1716*a(n-7) - 1287*a(n-8) + 715*a(n-9) - 286*a(n-10) + 78*a(n-11) - 13*a(n-12) + a(n-13) for n>13.
  (End)
This file states both. The sequence has offset 1 (data 16, 256, 2500, 16900, 87616, 372100, ...).

An n X 2 array with entries in 0..3 is a function x : Fin n → Fin 2 → Fin 4, where x i j is the
entry in row i and column j. A finite list L is unimodal if there exists a peak index p such that
L is nondecreasing up to p and nonincreasing from p onwards (equivalently, L has no strict valley
L[i] > L[j] < L[l] for i < j < l). Rows have length 2, columns have length n, and the d-th
antidiagonal (for d in 0..n) consists of the entries x i j with i + j = d ordered by increasing i.
This reading reproduces the listed terms (a(n) = U(n)^2 where U(n) counts unimodal length-n
sequences over 0..3, matching the examples for n = 3 and all listed terms).

The g.f. is stated as a cleared-denominator identity of formal power series over ℚ with
coefficient 0 at X^0 (offset 1):
(sum of a(n) X^n over n ≥ 1) * (1 - X)^13 = X * (16 + 48 X + 420 X^2 - 208 X^3 + 1140 X^4 - 1260 X^5 + 1401 X^6 - 1044 X^7 + 597 X^8 - 244 X^9 + 69 X^10 - 12 X^11 + X^12).
The recurrence is stated over ℤ for n > 13 (i.e. 14 ≤ n), where every index n - 13 ≥ 1 is within
the offset 1 range.
-/

namespace OMA.S_oeis_a223756

/-- A list of entries in 0..3 is unimodal if there is a peak index p such that it is
nondecreasing up to p and nonincreasing from p onwards. -/
def IsUnimodal (L : List (Fin 4)) : Prop :=
  ∃ p : Fin (L.length + 1),
    (∀ i j : Fin L.length, i ≤ j → j.val ≤ p.val → L[i] ≤ L[j]) ∧
    (∀ i j : Fin L.length, p.val ≤ i.val → i ≤ j → L[j] ≤ L[i])

instance (L : List (Fin 4)) : Decidable (IsUnimodal L) := by
  unfold IsUnimodal
  infer_instance

/-- The i-th row of an n X 2 array. -/
def row (n : ℕ) (x : Fin n → Fin 2 → Fin 4) (i : Fin n) : List (Fin 4) :=
  List.ofFn (fun j : Fin 2 => x i j)

/-- The j-th column of an n X 2 array. -/
def col (n : ℕ) (x : Fin n → Fin 2 → Fin 4) (j : Fin 2) : List (Fin 4) :=
  List.ofFn (fun i : Fin n => x i j)

/-- The d-th antidiagonal of an n X 2 array (entries x i j with i + j = d, ordered by i). -/
def antidiag (n : ℕ) (x : Fin n → Fin 2 → Fin 4) (d : Fin (n + 1)) : List (Fin 4) :=
  (List.finRange n).filterMap (fun i =>
    if h : i.val ≤ d.val ∧ d.val - i.val < 2 then some (x i ⟨d.val - i.val, h.2⟩) else none)

/-- All rows, antidiagonals, and columns of x are unimodal. -/
def valid (n : ℕ) (x : Fin n → Fin 2 → Fin 4) : Prop :=
  (∀ i : Fin n, IsUnimodal (row n x i)) ∧
  (∀ d : Fin (n + 1), IsUnimodal (antidiag n x d)) ∧
  (∀ j : Fin 2, IsUnimodal (col n x j))

instance (n : ℕ) (x : Fin n → Fin 2 → Fin 4) : Decidable (valid n x) := by
  unfold valid
  infer_instance

/-- A223756(n): number of n X 2 0..3 arrays with rows, antidiagonals and columns unimodal. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 2 → Fin 4)).filter (valid n)).card

/-- Barker's conjectures: the g.f. x(16 + 48x + 420x^2 - 208x^3 + 1140x^4 - 1260x^5 + 1401x^6 -
1044x^7 + 597x^8 - 244x^9 + 69x^10 - 12x^11 + x^12)/(1 - x)^13 and the order-13 linear recurrence
for n > 13. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - PowerSeries.X) ^ 13 =
      PowerSeries.X * (16 + 48 * PowerSeries.X + 420 * PowerSeries.X ^ 2 -
        208 * PowerSeries.X ^ 3 + 1140 * PowerSeries.X ^ 4 - 1260 * PowerSeries.X ^ 5 +
        1401 * PowerSeries.X ^ 6 - 1044 * PowerSeries.X ^ 7 + 597 * PowerSeries.X ^ 8 -
        244 * PowerSeries.X ^ 9 + 69 * PowerSeries.X ^ 10 - 12 * PowerSeries.X ^ 11 +
        PowerSeries.X ^ 12) ∧
    ∀ n : ℕ, 13 < n →
      (a n : ℤ) = 13 * (a (n - 1) : ℤ) - 78 * (a (n - 2) : ℤ) + 286 * (a (n - 3) : ℤ) -
        715 * (a (n - 4) : ℤ) + 1287 * (a (n - 5) : ℤ) - 1716 * (a (n - 6) : ℤ) +
        1716 * (a (n - 7) : ℤ) - 1287 * (a (n - 8) : ℤ) + 715 * (a (n - 9) : ℤ) -
        286 * (a (n - 10) : ℤ) + 78 * (a (n - 11) : ℤ) - 13 * (a (n - 12) : ℤ) +
        (a (n - 13) : ℤ) := by
  sorry

end OMA.S_oeis_a223756
