import Mathlib

/-!
# Growth of a minimum recurrence
Source: https://mathoverflow.net/questions/143865/asymptotic-growth-of-recurrence-relation-x-n-min-limits-n-1n-2-nax-n-1

Both children are positive integers. The base value is x₁=0, and x₀ is
irrelevant. The minimum is specified by its lower-bound and attainment
properties. The strict two-sided estimate is the one in the original question
after multiplying through by the positive comparison function.
-/
namespace OMA.S_mo_143865

def cost (a : ℝ) (x : ℕ → ℝ) (i j : ℕ) : ℝ := a*(x i+x j)+2*(i:ℝ)*j

def Recurs (a : ℝ) (x : ℕ → ℝ) : Prop :=
  x 1=0 ∧ ∀ n : ℕ, 2 ≤ n →
    (∀ i j : ℕ, 0 < i → 0 < j → i+j=n → x n ≤ cost a x i j) ∧
    ∃ i j : ℕ, 0 < i ∧ 0 < j ∧ i+j=n ∧ x n=cost a x i j

def OrderOf (x g : ℕ → ℝ) : Prop := ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c*g n < x n ∧ x n < C*g n

theorem main : ∀ a : ℝ, 0 < a → (∃ x, Recurs a x) ∧ ∀ x, Recurs a x →
    (∀ r : ℝ, 0 < r → (OrderOf x (fun n => (n:ℝ)^r) ↔
      (a < 1 ∧ r=1) ∨ (1 ≤ a ∧ a < 2 ∧ r=2) ∨
        (2 < a ∧ r=1+Real.log a/Real.log 2))) ∧
    (a=2 → OrderOf x (fun n => (n:ℝ)^2*Real.log n)) ∧
    (∀ i j : ℕ, 0 < i → 0 < j →
      (x (i+j)=cost a x i j ↔
        (a < 1 ∧ (i=1 ∨ j=1)) ∨ a=1 ∨ (1 < a ∧ i ≤ j+1 ∧ j ≤ i+1))) := by
  sorry

end OMA.S_mo_143865
