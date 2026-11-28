import Mathlib

/-!
# Finite-horizon reachability for convex mixtures of stochastic matrices

Source: jonem, MathOverflow question 385518, March 4, 2021 (CC BY-SA 4.0),
https://mathoverflow.net/questions/385518.
Credit: @connoranderson.

Reachability is equivalent to a polynomial feasibility test on the known endpoints
of words in the original matrices. The word weights are products of independent
stage probabilities. Allowing arbitrary convex weights gives exactly the convex hull
of the reachable set. A three-state, two-step example shows that this relaxation
can strictly enlarge the set.
-/

namespace OMA.S_mo_385518

open Matrix

abbrev Row (n : ℕ) := Fin n → ℝ
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def Distribution {n : ℕ} (x : Row n) : Prop := (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

def Stochastic {n : ℕ} (P : Mat n) : Prop := ∀ i, Distribution (P i)

noncomputable def endpoint {n z : ℕ} (x : Row n) (Q : Fin z → Mat n) : Row n :=
  x ᵥ* (List.ofFn Q).prod

def reachable {n m : ℕ} (z : ℕ) (x : Row n) (P : Fin m → Mat n) : Set (Row n) :=
  {y | ∃ Q : Fin z → Mat n, (∀ t, Q t ∈ convexHull ℝ (Set.range P)) ∧ y = endpoint x Q}

noncomputable def wordEnd {n m z : ℕ} (x : Row n) (P : Fin m → Mat n)
    (w : Fin z → Fin m) : Row n := endpoint x (P ∘ w)

theorem main :
    (∀ {n m z : ℕ}, 0 < z → ∀ (x : Row n) (P : Fin m → Mat n),
      Distribution x → (∀ a, Stochastic (P a)) →
      (∀ y, y ∈ reachable z x P ↔ ∃ p : Fin z → Row m, (∀ t, Distribution (p t)) ∧
        y = ∑ w : Fin z → Fin m, (∏ t, p t (w t)) • wordEnd x P w) ∧
      convexHull ℝ (reachable z x P) = convexHull ℝ (Set.range (wordEnd (z := z) x P))) ∧
    (∃ (x : Row 3) (P : Fin 2 → Mat 3), Distribution x ∧ (∀ a, Stochastic (P a)) ∧
      ¬ Convex ℝ (reachable 2 x P)) := by
  sorry

end OMA.S_mo_385518
