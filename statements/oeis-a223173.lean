import Mathlib

/-!
# A223173: Barker's closed form and g.f. for the poly-Cauchy numbers c_3^(-n)

Source: https://oeis.org/A223173
Credit: @ivillar

Status: known result (the conjecture was verified by Robert Israel, Jun 21 2018).

A223173 (offset 1) is the sequence of poly-Cauchy numbers c_3^(-n),
a(n) = Sum_{k=0..3} Stirling1(3,k)*(k+1)^n, where Stirling1 is the signed Stirling number of
the first kind; data -1, -3, -1, 45, 359, 2037, ...
Conjecture (Colin Barker, Mar 31 2013): a(n) = 2^(1+n) - 3^(1+n) + 4^n, and the g.f. is
-x*(6*x-1) / ((2*x-1)*(3*x-1)*(4*x-1)). Robert Israel (Jun 21 2018) verified the conjecture.

Formalization notes.
* The signed Stirling number of the first kind is Stirling1(n,k) = (-1)^(n-k) * [n, k], where
  [n, k] is Mathlib's unsigned `Nat.stirlingFirst n k`. Terms are computed in ℤ.
* The closed form is claimed for every n ≥ 1 (the offset).
* The g.f. of the offset-1 sequence is Sum_{n >= 1} a(n) x^n, written as `PowerSeries.mk` of the
  function that is 0 at n = 0 and a(n) for n ≥ 1; the identity is stated over ℤ⟦X⟧,
  cross-multiplied by the denominator (2*x-1)*(3*x-1)*(4*x-1), which is a unit there.
-/

namespace OMA.S_oeis_a223173

open PowerSeries

/-- The signed Stirling number of the first kind, Stirling1(n,k) = (-1)^(n-k) * [n, k]. -/
def stirling1 (n k : ℕ) : ℤ := (-1) ^ (n - k) * (Nat.stirlingFirst n k : ℤ)

/-- A223173: a(n) = Sum_{k=0..3} Stirling1(3,k)*(k+1)^n. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range 4, stirling1 3 k * ((k : ℤ) + 1) ^ n

/-- Barker's conjecture: the closed form, and the g.f. cross-multiplied by its denominator. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → a n = 2 ^ (1 + n) - 3 ^ (1 + n) + 4 ^ n) ∧
      PowerSeries.mk (fun n => if n = 0 then 0 else a n) *
          ((2 * X - 1) * (3 * X - 1) * (4 * X - 1) : PowerSeries ℤ) =
        -X * (6 * X - 1) := by
  sorry

end OMA.S_oeis_a223173
