import Mathlib

/-!
# Are the Cayley digraphs `A'G_n` Hamiltonian?

Source: https://mathoverflow.net/questions/161445 (CC BY-SA 4.0).

Let `A'G_n` be the Cayley digraph on the alternating group `A_n` with generating set
`S = {(1 i 2) : 3 ≤ i ≤ n}`, `n ≥ 4`. The asker suspects that `A'G_n` is not Hamiltonian for all
`n ≥ 4` (true for `n = 4`, checked by hand), and asks whether `A'G_n` is Hamiltonian.

We state the asker's suspicion: for every `n ≥ 4`, `A'G_n` has no directed Hamiltonian cycle.

Formalization notes:
* Points are `Fin n`, with `1, 2, i` becoming `0, 1, i - 1`; the 3-cycle `(0 i 1)` (`0 ↦ i ↦ 1 ↦ 0`) is
  `swap 0 1 * swap 0 i`, with `(σ * τ) x = σ (τ x)`.
* A directed Hamiltonian cycle is an injective `f : ZMod (n!/2) → Perm (Fin n)` with every value even
  (so `f` is a bijection onto `A_n`, which has `n!/2` elements) and `f (k+1) = f k * s` with `s ∈ S`.
  Right multiplication is used; left multiplication gives an isomorphic digraph (`g ↦ g⁻¹` maps it to
  the left Cayley digraph of `S⁻¹`, and reversing a cycle turns `S⁻¹` back into `S`).
* Numerical check (exhaustive search): no Hamiltonian cycle for `n = 4`, matching the asker; but for
  `n = 5` a directed Hamiltonian cycle exists (found and verified by computer, under left and right
  multiplication alike). So this statement appears to be false, and its disproof should be at `n = 5`.
-/

namespace OMA.S_mo_161445

/-- For every `n ≥ 4`, the Cayley digraph of `A_n` with generators `(1 i 2)` is not Hamiltonian. -/
theorem main : ∀ n : ℕ, (hn : 4 ≤ n) → ¬ ∃ f : ZMod (n.factorial / 2) → Equiv.Perm (Fin n),
    Function.Injective f ∧ (∀ k, Equiv.Perm.sign (f k) = 1) ∧
      ∀ k, ∃ i : Fin n, 2 ≤ i.val ∧
        f (k + 1) = f k * (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ * Equiv.swap ⟨0, by omega⟩ i) := by
  sorry

end OMA.S_mo_161445
