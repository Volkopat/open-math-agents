import Mathlib

/-!
# Prime labelings of grid graphs

Conjecture of Sundaram, Ponraj and Somasundaram (2006): every planar grid graph P_m × P_n has a prime labeling,
a bijection from its m·n vertices onto {1, …, m·n} that gives coprime labels to adjacent vertices.
Known cases: ladders m = 2 (Dean; Ghorbani–Kamali), P_p × P_n for a prime p and n ≤ p (Sundaram et al.), and
p < n ≤ p² for an odd prime p (S. Curran, Prime labelings on planar grid graphs, Theory and Applications of Graphs,
2022). Open in general; labelings have been found by computer search up to 115 × 115.
Lean statement by the Left to Solve team.
-/

namespace OMA.S_grid_prime_labeling

/-- Two cells of the m × n grid are adjacent when they share a row and their columns differ by one, or share a
column and their rows differ by one. -/
def gridAdj (m n : ℕ) (p q : Fin m × Fin n) : Prop :=
  (p.1 = q.1 ∧ ((p.2 : ℕ) + 1 = (q.2 : ℕ) ∨ (q.2 : ℕ) + 1 = (p.2 : ℕ))) ∨
    (p.2 = q.2 ∧ ((p.1 : ℕ) + 1 = (q.1 : ℕ) ∨ (q.1 : ℕ) + 1 = (p.1 : ℕ)))

/-- Every m × n grid graph has a prime labeling: the labels are f p + 1 ∈ {1, …, m·n}, each used once. -/
theorem main :
    ∀ m n : ℕ, ∃ f : Fin m × Fin n ≃ Fin (m * n),
      ∀ p q : Fin m × Fin n, gridAdj m n p q → Nat.Coprime ((f p : ℕ) + 1) ((f q : ℕ) + 1) := by
  sorry

end OMA.S_grid_prime_labeling
