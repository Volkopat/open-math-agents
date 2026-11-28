import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic
open scoped BigOperators

namespace OMA.S_mo_298012

theorem main : ∀ (n : ℕ) (hn : 2 ≤ n) (x : Fin n → ℝ) (m : ℝ)
    (hx : ∀ i, 0 ≤ x i) (hs : ∑ i, x i = n) (hsq : ∑ i, (x i)^2 = m),
    let a := 1 + Real.sqrt ((m - n) * (1 - 1 / (n : ℝ)))
    let y := fun i : ℕ => min a (max 0 ((n : ℝ) - i * a))
    1 ≤ a ∧ a ≤ n ∧
    Antitone y ∧ (∀ i, 0 ≤ y i) ∧
    (∑ i ∈ Finset.range n, y i) = n ∧
    (∀ k : ℕ, (∑ i ∈ Finset.range k, y i) = min ((k : ℝ) * a) n) ∧
    (∀ s : Finset (Fin n), (∑ i ∈ s, x i) ≤ ∑ i ∈ Finset.range s.card, y i) ∧
    (∀ i : Fin n, ∃ z : Fin n → ℝ, (∀ j, 0 ≤ z j) ∧
      (∑ j, z j = n) ∧ (∑ j, (z j)^2 = m) ∧ z i = a) := by
  sorry

end OMA.S_mo_298012
