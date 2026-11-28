import OMAStatements.S_oeis_a046932
import Mathlib

/-! Separate a period produced by Frobenius linearization from the assertion
that no proper divisor of that period is a period. -/
namespace OMA.R_oeis_a046932_R1
open OMA.S_oeis_a046932
def H1 : Prop := ∀ k m : ℕ, 2 ≤ k → 1 ≤ m →
    a ((2^(k*m)-1)/(2^m-1)) ∣ (2^(a k*m)-1)/(2^m-1)
def H2 : Prop := ∀ k m : ℕ, 2 ≤ k → 1 ≤ m →
    (2^(a k*m)-1)/(2^m-1) ∣ a ((2^(k*m)-1)/(2^m-1))
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a046932.main := by
  intro up low
  have both (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m) :=
    Nat.dvd_antisymm (up k m hk hm) (low k m hk hm)
  exact ⟨fun k hk => by simpa using both k 1 hk (by decide),both⟩
end OMA.R_oeis_a046932_R1
