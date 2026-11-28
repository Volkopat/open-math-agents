import Mathlib

/-!
# A222955: Number of n X 1 0..1 arrays with every row and column least squares fitting to a zero slope straight line, with a single point array taken as having zero slope.

Source: https://oeis.org/A222955
Credit: @agchua

Comment of A222955 (Gus Wiseman, Jan 07 2023):
  Conjecture: A binary word is counted iff it has the same sum of positions of 1's as its reverse, or, equivalently, the same sum of partial sums as its reverse.
The sequence has offset 1, so the claim is stated for words of length n ≥ 1. An n X 1 array with
entries 0 or 1 is a binary word w of length n (its only column); each of its n rows is a single
point. The least squares straight line through the points (x_i, y_i), i = 1..m, has slope
(m * Sum x_i*y_i - Sum x_i * Sum y_i) / (m * Sum x_i^2 - (Sum x_i)^2); the entries of a row or a
column of length m are the points (1, y_1), ..., (m, y_m). As in the name, a single point (m = 1)
counts as having zero slope. Positions are counted from 1, the reverse of w is i -> w(n+1-i),
and the partial sums of w are w(1) + ... + w(j) for j = 1..n.
-/

namespace OMA.S_oeis_a222955

/-- The slope of the least squares straight line through the points (i + 1, y i), i < m. -/
def lsSlope {m : ℕ} (y : Fin m → ℚ) : ℚ :=
  ((m : ℚ) * ∑ i : Fin m, (((i : ℕ) : ℚ) + 1) * y i -
      (∑ i : Fin m, (((i : ℕ) : ℚ) + 1)) * ∑ i : Fin m, y i) /
    ((m : ℚ) * ∑ i : Fin m, (((i : ℕ) : ℚ) + 1) ^ 2 - (∑ i : Fin m, (((i : ℕ) : ℚ) + 1)) ^ 2)

/-- A row or column of m points fits a zero slope straight line: it is a single point (the
entry's convention) or its least squares slope is 0. -/
def ZeroSlope {m : ℕ} (y : Fin m → ℚ) : Prop := m = 1 ∨ lsSlope y = 0

/-- An n X k array with entries 0 or 1 in which every row and every column fits a zero slope
straight line. -/
def Good {n k : ℕ} (A : Fin n → Fin k → Fin 2) : Prop :=
  (∀ i : Fin n, ZeroSlope (fun j => ((A i j : ℕ) : ℚ))) ∧
    ∀ j : Fin k, ZeroSlope (fun i => ((A i j : ℕ) : ℚ))

/-- The sum of the positions (counted from 1) of the 1's of a binary word. -/
def posSum {n : ℕ} (w : Fin n → Fin 2) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i => w i = 1), ((i : ℕ) + 1)

/-- The sum of the partial sums w(1), w(1) + w(2), ..., w(1) + ... + w(n) of a binary word. -/
def psSum {n : ℕ} (w : Fin n → Fin 2) : ℕ :=
  ∑ j : Fin n, ∑ i ∈ Finset.univ.filter (fun i => i ≤ j), (w i : ℕ)

/-- The reverse of a binary word. -/
def reverse {n : ℕ} (w : Fin n → Fin 2) : Fin n → Fin 2 := fun i => w (Fin.rev i)

/-- The comment's conjecture, for n ≥ 1: the n X 1 array of a binary word w is counted iff w has
the same sum of positions of 1's as its reverse, and this holds iff w has the same sum of partial
sums as its reverse. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∀ w : Fin n → Fin 2,
    (Good (fun i (_ : Fin 1) => w i) ↔ posSum w = posSum (reverse w)) ∧
      (posSum w = posSum (reverse w) ↔ psSum w = psSum (reverse w)) := by
  sorry

end OMA.S_oeis_a222955
