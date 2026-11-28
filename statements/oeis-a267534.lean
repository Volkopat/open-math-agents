import Mathlib.Data.Nat.Nth
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# OEIS A267534, indices of Lucas numbers that are not sums of three integer squares

Source: https://oeis.org/A267534 (Altug Alkan; two formulas conjectured by Colin Barker, 2016).
Credit: @jiyongparkphysics

The sequence is indexed by increasing Lucas index. Our term k is OEIS a(k+1),
so X times the series with coefficients term k has coefficient a(1) at X.
The displayed formal-power-series identity clears a denominator with constant
coefficient one. The recurrence uses integer subtraction as in the source.
Neville Robbins, The Fibonacci Quarterly 21 (1983), Theorem 1, gives the residue
classification underlying these corollaries: https://www.fq.math.ca/Scanned/21-1/robbins.pdf
-/

namespace OMA.S_oeis_a267534

open PowerSeries

def lucasPair : ℕ → ℕ × ℕ
  | 0 => (2, 1)
  | k+1 => let p := lucasPair k; (p.2, p.1 + p.2)

def badIndex (n : ℕ) : Prop :=
  ¬ ∃ x y z : ℤ, x^2 + y^2 + z^2 = ((lucasPair n).1 : ℤ)

/-- Zero-based indexing: term 0 is OEIS a(1). -/
noncomputable def term (k : ℕ) : ℕ := Nat.nth badIndex k

theorem main :
    (X * PowerSeries.mk (fun k => (term k : ℤ))) *
      ((1-X)^2*(1+X+X^2+X^3+X^4+X^5+X^6)) =
      X*(2+X)*(2+X+X^2+2*X^3+X^4+X^6) ∧
    (∀ n : ℕ, 8 < n → (term (n-1) : ℤ) =
      (term (n-2):ℤ) + (term (n-8):ℤ) - (term (n-9):ℤ)) := by
  sorry

end OMA.S_oeis_a267534
