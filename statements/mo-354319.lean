import Mathlib

/-!
# Minimizing weights while preserving maximum independent sets

Source: https://mathoverflow.net/questions/354319 (Bart Jansen, March 2020).
Credit: @Mapika

We use positive integer input weights. This agrees with the author's range
starting at 1 and the stated positive result for forests. If zero input weights
were allowed, a single isolated vertex of weight zero would already refute the
claim, since both the empty and the singleton set would be optimal.

For a positive bound B, the condition that B(n)^k ≤ 2^n eventually for every
positive integer k is equivalent to log₂ B(n) = o(n).
-/

namespace OMA.S_mo_354319

/-- The collection of all maximum-weight independent sets of a finite graph. -/
def optima {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℕ) :
    Set (Finset (Fin n)) :=
  {S | G.IsIndepSet (S : Set (Fin n)) ∧
    ∀ T : Finset (Fin n), G.IsIndepSet (T : Set (Fin n)) →
      (∑ v ∈ T, w v) ≤ ∑ v ∈ S, w v}

/-- Does a subexponential bound suffice uniformly over all graphs and weights? -/
theorem main :
    ∃ B : ℕ → ℕ, (∀ n, 0 < B n) ∧
      (∀ k : ℕ, 0 < k → ∃ N : ℕ, ∀ n ≥ N, B n ^ k ≤ 2 ^ n) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : Fin n → ℕ),
        (∀ v, 0 < w v) →
        ∃ w' : Fin n → ℕ, (∀ v, 0 < w' v ∧ w' v ≤ B n) ∧
          optima G w' = optima G w := by
  sorry

end OMA.S_mo_354319
