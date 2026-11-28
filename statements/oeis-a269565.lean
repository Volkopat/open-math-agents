import Mathlib

/-!
# A269565: Array read by antidiagonals: T(n,m) is the number of (directed) Hamiltonian paths in K_n X K_m.

Source: https://oeis.org/A269565

K_n X K_m is the n X m rook graph, the Cartesian (box) product of the complete
graphs on n and m vertices. A directed Hamiltonian path is a sequence of
vertices in which consecutive vertices are adjacent and every vertex of the
graph appears exactly once; a path and its reversal are counted separately.
The array has offset 1, so n, m >= 1 (T(1,1) = 1, T(n,1) = n!, T(2,2) = 8).

The entry's conjecture (comment by Mikhail Kurkov, confirmed in the next
comment by Andrew Howroyd): T(n,m) mod n!*m! = 0.
-/

namespace OMA.S_oeis_a269565

/-- The n X m rook graph K_n □ K_m (Cartesian product of complete graphs). -/
abbrev rook (n m : ℕ) : SimpleGraph (Fin n × Fin m) :=
  (⊤ : SimpleGraph (Fin n)) □ (⊤ : SimpleGraph (Fin m))

/-- Directed Hamiltonian paths of the rook graph, as vertex sequences: consecutive
vertices are adjacent and every vertex is visited exactly once. -/
def HamPath (n m : ℕ) : Type :=
  {l : List (Fin n × Fin m) // l.IsChain (rook n m).Adj ∧ l.Nodup ∧ ∀ v, v ∈ l}

/-- T(n,m): the number of directed Hamiltonian paths in K_n □ K_m. -/
noncomputable def T (n m : ℕ) : ℕ := Nat.card (HamPath n m)

theorem main : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → (n.factorial * m.factorial) ∣ T n m := by
  sorry

end OMA.S_oeis_a269565
