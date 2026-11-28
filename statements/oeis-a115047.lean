import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Defs

/-!
# Divisibility at prime indices of A115047

Michael Somos asks whether every prime in the sequence's domain divides
the corresponding term. The published offset is 3 and the initial term
is a(3)=1. Below b(k)=a(k+3). In the recurrence for a(m+4), write the
source summation index as j+1 and put k=m-j.

Source: https://oeis.org/A115047 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Solitude1312
-/

namespace OMA.S_oeis_a115047

/-- The numerator of the original recurrence for a(m+4). -/
def numerator (m : ℕ) (f : ℕ → ℕ) : ℕ :=
  ∑ ij ∈ Finset.antidiagonal m, m.choose ij.1 * (m + 4).choose (ij.1 + 2) *
    f ij.1 * f ij.2 * (ij.1 + 1) * (ij.2 + 1)

/-- b(k) is the source term a(k+3). -/
def b (n : ℕ) : ℕ :=
  if n = 0 then 1 else
    let m := n - 1
    numerator m (fun i => if _h : i < n then b i else 0) / (2 * (m + 3))
termination_by n

theorem main : ∀ p : ℕ, 3 ≤ p → p.Prime → p ∣ b (p - 3) := by
  sorry

end OMA.S_oeis_a115047
