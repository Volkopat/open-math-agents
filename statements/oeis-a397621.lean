import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.ZMod.Basic

/-!
# Linear complexity of binary Pascal rows

Source: https://oeis.org/A397621 (Darío Clavijo, August 2026), conjectured
identity with https://oeis.org/A001317 and https://oeis.org/A080079.
A001317(n) reads row n of Pascal's triangle modulo 2 as binary digits.
Its digit word is symmetric and has length n+1. Its coefficients over the
binary field are therefore precisely those of (1+X)^n in increasing order.

A finite binary word has a linear recurrence of order L if a connection
polynomial Q of degree at most L and constant coefficient 1 makes the
convolution vanish in positions L through the end of the word. The least
such L is the finite-word linear complexity used by Berlekamp--Massey.
A080079(n) equals 2^(floor(log2 n)+1)-n for n ≥ 1 (Benoit Cloitre, 2003).
Credit: @Aryan-Poonacha
-/

namespace OMA.S_oeis_a397621

open Polynomial

/-- Orders of binary recurrences satisfied by the n-th finite Pascal row. -/
def RecurrenceOrder (n L : ℕ) : Prop :=
  ∃ Q : Polynomial (ZMod 2), Q.coeff 0 = 1 ∧ Q.natDegree ≤ L ∧
    ∀ j : ℕ, L ≤ j → j ≤ n → (Q * (1+X)^n).coeff j = 0

theorem main : ∀ n : ℕ, 0 < n →
    IsLeast {L : ℕ | RecurrenceOrder n L} (2^(n.log2+1)-n) := by
  sorry

end OMA.S_oeis_a397621
