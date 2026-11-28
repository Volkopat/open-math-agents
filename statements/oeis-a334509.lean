import Mathlib

/-!
# The eventual period of elementary cellular automaton Rule 41

OEIS A334509 concerns the entire cyclic configuration, started from a single
occupied site. Colin Barker conjectured its recurrence and ordinary generating
function in 2020. Stefano Spezia conjectured its pointwise formula in 2021.
The factor A176895(n) in that formula is 4 / gcd(n, 4).

Sources: https://oeis.org/A334509 and https://oeis.org/A176895
Formalization: @saientropy
-/

namespace OMA.S_oeis_a334509

/-- In left-to-right order, the three neighborhoods giving output one are
000, 011, and 101. -/
def localRule (left center right : Prop) : Prop :=
  (¬ left ∧ ¬ center ∧ ¬ right) ∨
  (¬ left ∧ center ∧ right) ∨
  (left ∧ ¬ center ∧ right)

/-- The row at time `t`, lifted periodically from the ring of width `n`
to integer coordinates. Its initial occupied sites are precisely the
representatives of the residue class zero. -/
def row (n : ℕ) : ℕ → ℤ → Prop
  | 0, x => -x % (n : ℤ) = 0
  | t + 1, x => localRule (row n t (x - 1)) (row n t x) (row n t (x + 1))

/-- A time shift preserves the whole row at every sufficiently late time. -/
def EventualPeriod (n p : ℕ) : Prop :=
  ∃ T : ℕ, ∀ t ≥ T, row n (t + p) = row n t

/-- A334509 starts at width one. A zero coefficient at degree zero gives its
ordinary generating function the OEIS offset. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else sInf {p : ℕ | 0 < p ∧ EventualPeriod n p}

/-- Coefficients of Barker's numerator, in increasing order of degree,
including the leading factor of `X`. -/
def numeratorCoeffs : List ℤ :=
  [0, 2, 2, 2, 2, 11, -2, 24, 4, 8, 18, -10, -2, -5, -10]

/-- Spezia's pointwise formula and Barker's recurrence and generating
function. Clearing the denominator gives an equality of formal power series
over the integers. The denominator has constant coefficient one. -/
theorem main :
    (∀ n : ℕ, 6 < n → a n = n * (4 / Nat.gcd n 4)) ∧
    (∀ n : ℕ, 14 < n → (a n : ℤ) = 2 * (a (n - 4) : ℤ) - (a (n - 8) : ℤ)) ∧
    (let X : PowerSeries ℤ := PowerSeries.X
     PowerSeries.mk (fun n => (a n : ℤ)) *
        ((1 - X)^2 * (1 + X)^2 * (1 + X^2)^2) =
       PowerSeries.mk (fun n => numeratorCoeffs.getD n 0)) := by
  sorry

end OMA.S_oeis_a334509
