import Mathlib

/-!
# A354568: Hamiltonian cycles in Kneser graphs

Source: https://oeis.org/A354568
Credit: @Lenqth

A354568 is the triangle `T(n, k)`, `1 ≤ k < n/2`, giving the number of Hamiltonian cycles in the
Kneser graph `K(n, k)`: its vertices are the `k`-element subsets of an `n`-element set, and two
vertices are adjacent when the subsets are disjoint.

Formalizes the conjecture in the comments of A354568 (going back to Lovász 1970): `T(n, k) > 0`,
i.e. `K(n, k)` is Hamiltonian, for all `1 ≤ k < n/2` except `(n, k) = (5, 2)`, the Petersen
graph. The entry lists partial results (Chen 2003; Shields–Savage 2004 for `n ≤ 27`;
Mütze–Nummenpalo–Walczak 2018). The full statement was proved by Merino, Mütze and Namrata,
"Kneser graphs are Hamiltonian" (STOC 2023, arXiv:2212.03918).

We use Mathlib's `SimpleGraph.IsHamiltonian`. For `1 ≤ k` and `2k < n` the graph has at least
`3` vertices, so Mathlib's convention that a one-vertex graph counts as Hamiltonian plays no role.
-/

namespace OMA.S_oeis_a354568

/-- The Kneser graph `K(n, k)`: `k`-subsets of `Fin n`, adjacent when disjoint. -/
def kneser (n k : ℕ) : SimpleGraph {s : Finset (Fin n) // s.card = k} :=
  SimpleGraph.fromRel fun s t => Disjoint s.1 t.1

/-- `K(n, k)` is Hamiltonian for all `1 ≤ k < n / 2` except `(n, k) = (5, 2)`. -/
theorem main : ∀ n k : ℕ, 1 ≤ k → 2 * k < n → (n, k) ≠ (5, 2) → (kneser n k).IsHamiltonian := by
  sorry

end OMA.S_oeis_a354568
