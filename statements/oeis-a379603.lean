import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Largest decimal numbers whose squares use only 6, 7, 8 and 9

Source: https://oeis.org/A379603
-/
namespace OMA.S_oeis_a379603

def good (x : ℕ) : Prop := ∀ i : ℕ, 10^i ≤ x → 6 ≤ x/10^i%10

def eligible (d x : ℕ) : Prop := 10^(d-1) ≤ x ∧ x < 10^d ∧ good (x^2)

def largest (d x : ℕ) : Prop := eligible d x ∧ ∀ y, eligible d y → y ≤ x

def evenValue (n : ℕ) : ℕ := 100^n-(5*10^n+1)/3

theorem main : ∀ n : ℕ, 5≤n →
    largest (2*n) (evenValue n) ∧ largest (2*n+1) (10*evenValue n+6) := by
  sorry

end OMA.S_oeis_a379603
