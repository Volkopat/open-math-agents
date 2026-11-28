import Mathlib

/-!
# Pointwise lower bounds for nearly stationary probability vectors

For a finite reversible chain, a bound on the total-variation mixing time gives
a pointwise lower bound for every probability vector dominating its discounted
one-step evolution. A uniform spectral gap alone does not give any such bound,
even for lazy reversible birth-death chains with strictly positive invariant law.

Original question by M.Burtke, https://mathoverflow.net/questions/188072 (CC BY-SA 3.0).
The comparison between separation and variation for reversible chains is classical,
see Aldous and Fill, Reversible Markov Chains and Random Walks on Graphs, §4.3.
Credit: @connoranderson (agent: Codex)
-/
namespace OMA.S_mo_188072
open Matrix
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
def prob {n : ℕ} (u : Fin n → ℝ) : Prop := (∀ i, 0 ≤ u i) ∧ ∑ i,u i=1
def reversible {n : ℕ} (P : Mat n) (π : Fin n → ℝ) : Prop :=
  P ∈ rowStochastic ℝ (Fin n) ∧ prob π ∧ (∀ i,0 < π i) ∧
    ∀ i j,π i*P i j=π j*P j i
def admissible {n : ℕ} (P : Mat n) (ε : ℝ) (u : Fin n → ℝ) : Prop :=
  prob u ∧ ∀ j,(1-ε)*(u ᵥ* P) j ≤ u j
/-- For probability rows, the sum of the positive deficits equals their
total-variation distance from the stationary law. -/
def mixed {n : ℕ} (P : Mat n) (π : Fin n → ℝ) (t : ℕ) : Prop :=
  ∀ i, (∑ j,max (π j-(P^t) i j) 0) ≤ 1/4
/-- The eigenvalues on nonconstant real eigenfunctions, including possible
additional eigenvectors at one, are uniformly separated from one. -/
def gap {n : ℕ} (P : Mat n) (g : ℝ) : Prop :=
  ∀ (θ : ℝ) (f : Fin n → ℝ), (∃ i j,f i ≠ f j) → P *ᵥ f=θ • f → |θ| ≤ 1-g

/-- The discounted occupation kernel for a walk restarted with probability ε. -/
noncomputable def resolvent {n} (P : Mat n) (ε : ℝ) : Mat n := ε • (1-(1-ε) • P)⁻¹

theorem main :
    (∀ {n : ℕ} (P : Mat n) (π : Fin n → ℝ) (ε C : ℝ), P ∈ rowStochastic ℝ (Fin n) →
      0 < ε → ε ≤ 1 → ((∀ u, admissible P ε u → ∀ j,C*π j ≤ u j) ↔
        ∀ i j,C*π j ≤ resolvent P ε i j)) ∧
    (∀ {n : ℕ} (P : Mat n) (π u : Fin n → ℝ) (t : ℕ) (ε : ℝ),
      reversible P π → admissible P ε u → 0 ≤ ε → ε ≤ 1 → mixed P π t →
      ∀ j, (1-ε)^(2*t)*π j/2 ≤ u j ∧ ((t:ℝ)*ε ≤ 1/10 → 2*π j/5 ≤ u j)) ∧
    (∀ (ε C : ℝ), 0 < ε → ε < 1 → 0 < C →
      ∃ (n : ℕ) (P : Mat n) (π u : Fin n → ℝ), reversible P π ∧
        (∀ i,1/2 ≤ P i i) ∧ gap P (1/8) ∧ admissible P ε u ∧ ∃ j,u j < C*π j) := by
  sorry
end OMA.S_mo_188072
