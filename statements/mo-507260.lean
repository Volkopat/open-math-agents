import Mathlib

/-!
# Discrete C^k seminorms

Source: https://mathoverflow.net/questions/507260 (Drew Brady, CC BY-SA 4.0).
Credit: @connoranderson

The data are indexed from 1 to n. Discrete bounds use positive integer steps and
the continuous bounds use the Lipschitz constant of the kth derivative on [0,n].
Uniform comparison fails on alternating data: with k=2s−1 and n=4s+1 every
continuous extension requires at least (4/3)^s times the indicated discrete bound.
-/

namespace OMA.S_mo_507260
def discreteBound (k n : ℕ) (z : ℕ → ℝ) (D : ℝ) : Prop :=
  ∀ (i h : ℕ), 1 ≤ i → 1 ≤ h → i + (k+1)*h ≤ n →
    |(fwdDiff h)^[k+1] z i| ≤ D*(h:ℝ)^(k+1)
def extensionBound (k n : ℕ) (z : ℕ → ℝ) (L : ℝ) : Prop :=
  0 ≤ L ∧ ∃ f : ℝ → ℝ, ContDiffOn ℝ k f (Set.Icc 0 (n:ℝ)) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ n → f i = z i) ∧
    ∀ x ∈ Set.Icc 0 (n:ℝ), ∀ y ∈ Set.Icc 0 (n:ℝ),
      |iteratedDerivWithin k f (Set.Icc 0 (n:ℝ)) x -
        iteratedDerivWithin k f (Set.Icc 0 (n:ℝ)) y| ≤ L*|x-y|
def alternating (i : ℕ) : ℝ := (-1)^i

theorem main :
    (∀ s : ℕ, 1 ≤ s → discreteBound (2*s-1) (4*s+1) alternating (4^s) ∧
      (∃ L, extensionBound (2*s-1) (4*s+1) alternating L) ∧
      ∀ L, extensionBound (2*s-1) (4*s+1) alternating L → (16/3:ℝ)^s ≤ L) ∧
    ∀ C : ℝ, 1 < C → ∃ (k n : ℕ) (z : ℕ → ℝ) (D ε : ℝ),
      k+2 ≤ n ∧ 0 < D ∧ 0 < ε ∧ discreteBound k n z D ∧
      (∃ L, extensionBound k n z L) ∧ ∀ L, extensionBound k n z L → C*D+ε ≤ L := by
  sorry
end OMA.S_mo_507260
