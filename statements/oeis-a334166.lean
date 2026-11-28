import Mathlib.NumberTheory.Divisors

/-!
# Gaps between integers with a Zumkeller multiple obtained from a divisor

Source: OEIS A334166, https://oeis.org/A334166, OEIS Foundation, CC BY-SA 4.0.
A083207 defines a Zumkeller number by a partition of its positive divisors
into two sets with equal sums. Choosing one side specifies its complement.
-/

namespace OMA.S_oeis_a334166

open Finset

def Zumkeller (n : ℕ) : Prop :=
  0 < n ∧ ∃ s ⊆ n.divisors, (∑ i ∈ s, i) = ∑ i ∈ n.divisors \ s, i

def member (k : ℕ) : Prop := ∃ d ∈ k.divisors, Zumkeller (d*k)

theorem main : ∀ x y : ℕ, member x → member y → x < y →
    (∀ z : ℕ, x < z → z < y → ¬ member z) → y ≤ x+6 := by
  sorry

end OMA.S_oeis_a334166
