import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Congruence for factorial-scaled exponential coefficients

Source: https://oeis.org/A361281 (Peter Bala, March 12, 2023, OEIS Foundation,
CC BY-SA 4.0). In the defining finite sum put j = n-k, so n!/k! becomes the
falling factorial n.descFactorial j. Expanding the exponential in the general
conjecture, its k-th term is x^k G(x)^(nk)/k!. Thus scaledCoeff is exactly
n! times the coefficient of x^n in F(x) exp(x G(x)^n), computed over the
integers without division. ZMod k expresses congruence modulo k.
-/

namespace OMA.S_oeis_a361281

open Finset PowerSeries

def a (n : ℕ) : ℕ :=
  ∑ j ∈ range (n+1), n.descFactorial j * (n*(n-j)).choose j

noncomputable def scaledCoeff {R : Type*} [CommRing R] (F G : PowerSeries R) (n : ℕ) : R :=
  ∑ j ∈ range (n+1), (n.descFactorial j : R) * coeff j (F * G^(n*(n-j)))

theorem main :
    (∀ (F G : PowerSeries ℤ), constantCoeff G = 1 → ∀ n k : ℕ,
      ((scaledCoeff F G (n+k) : ℤ) : ZMod k) = ((scaledCoeff F G n : ℤ) : ZMod k)) ∧
    (∀ n k : ℕ, (a (n+k) : ZMod k) = (a n : ZMod k)) ∧
    (∀ n : ℕ, (a n : ZMod 4) = 1) ∧
    (∀ n : ℕ, (a (5*n+2) : ZMod 5) = 0) := by
  sorry

end OMA.S_oeis_a361281
