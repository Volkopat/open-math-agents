import Mathlib

/-!
# Shift-invariant submultiplicative seminorms of bounded sequences

Source: https://mathoverflow.net/questions/133105 (Siddharth, CC BY-SA 3.0).
Credit: @connoranderson

Use the algebra of bounded real sequences with pointwise operations and the left shift.
Increasing is taken in the strict sense for the counterexample; it consequently also
rules out the nondecreasing convention. The zero seminorm is allowed by the literal
wording. The second question already fails for positive scalar multiples of one sequence.
-/

namespace OMA.S_mo_133105
abbrev Seq := BoundedContinuousFunction ℕ ℝ
noncomputable def shift (x : Seq) : Seq :=
  x.compContinuous ⟨fun n : ℕ => n+1,continuous_of_discreteTopology⟩
def admissible (p : Seminorm ℝ Seq) : Prop :=
  (∀ x, p (shift x) = p x) ∧ ∀ x y, p (x*y) ≤ p x * p y
noncomputable def ratio (f : ℕ → ℕ) (hf : Monotone f) : Seq :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n => (f n : ℝ)/(f (n+1) : ℝ)) 1 (by
      intro n
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      by_cases h : f (n+1) = 0
      · simp [h]
      · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h)).mpr
        exact_mod_cast hf (Nat.le_succ n))

theorem main :
    (∃ (f : ℕ → ℕ) (hf : StrictMono f), (∀ n, 2^n ≤ f n) ∧
      ∀ p : Seminorm ℝ Seq, admissible p → p ≠ 0 → 1 ≤ p (ratio f hf.monotone)) ∧
    (∀ p : Seminorm ℝ Seq, admissible p →
      ((∀ (f : ℕ → ℕ) (hf : StrictMono f), (∀ n, 0 < f n) →
        (∃ c r : ℝ, 0 < c ∧ 1 < r ∧ ∀ n, c*r^n ≤ f n) →
        p (ratio f hf.monotone) < 1) ↔ p = 0)) ∧
    (∃ (f g : ℕ → ℕ) (hf : StrictMono f) (hg : StrictMono g),
      (∀ n, 0 < g n ∧ g n < f n) ∧ ratio f hf.monotone = ratio g hg.monotone) := by
  sorry
end OMA.S_mo_133105
