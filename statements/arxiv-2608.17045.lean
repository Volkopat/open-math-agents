import Mathlib

/-!
# Prime-exponent transition geometry between consecutive highly composite numbers

Source: https://arxiv.org/html/2608.17045v1, Sections 2 and 9.
Credit: @pmaster
-/

namespace HCN

def tau (n : ℕ) : ℕ := n.divisors.card

def IsRecord (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m < n → tau m < tau n

def Consecutive (h k : ℕ) : Prop :=
  IsRecord h ∧ IsRecord k ∧ h < k ∧ ∀ m : ℕ, h < m → m < k → ¬ IsRecord m

/-- The gcd and lcm give the two coordinatewise endpoints of the closed exponent box. -/
def InBox (h k z : ℕ) : Prop := h.gcd k ∣ z ∧ z ∣ h.lcm k

/-- One prime exponent changes by one unit toward its exponent at the target. -/
def Move (k x y : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧
    ((y = p * x ∧ x.factorization p < k.factorization p) ∨
     (x = p * y ∧ k.factorization p < x.factorization p))

/-- A finite path from h staying below the ceiling k and retaining at least t divisors. -/
inductive Reach (h k t : ℕ) : ℕ → Prop
  | start (pos : 0 < h) (ceiling : h ≤ k) (floor : t ≤ tau h) : Reach h k t h
  | step {x y : ℕ} (prev : Reach h k t x) (move : Move k x y)
      (pos : 0 < y) (box : InBox h k y) (ceiling : y ≤ k) (floor : t ≤ tau y) :
      Reach h k t y

/-- Maximizing reachable integer thresholds is equivalent to maximizing path minima. -/
noncomputable def bottleneck (h k : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun t => Reach h k t k) (tau h)

noncomputable def capacity (h k : ℕ) : ℚ := (bottleneck h k : ℚ) / tau h

end HCN
namespace OMA.S_arxiv_2608_17045

open HCN

/-- Conjectures 9.1 and 9.2. -/
theorem main :
    (∀ h k : ℕ, Consecutive h k → 1 / 2 ≤ capacity h k) ∧
    (∀ h k : ℕ, Consecutive h k →
      (capacity h k = 1 / 2 ↔ k.primeFactors.card < h.primeFactors.card)) := by
  sorry

end OMA.S_arxiv_2608_17045
