import Mathlib

/-!
# Eventual periodicity of the extended partition rows in OEIS A365383

A partition represents a number when a multiset of its part sizes, each
available with unrestricted multiplicity, sums to that number.

Source: https://oeis.org/A365383
Credit: @CubeJerry
-/

namespace OMA.S_oeis_a365383

def Represents {n : ℕ} (p : Nat.Partition n) (k : ℕ) : Prop :=
  ∃ xs : Multiset ℕ, (∀ x ∈ xs, x ∈ p.parts) ∧ xs.sum = k

noncomputable def row (n k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : Nat.Partition n => Represents p k)).card

theorem main : (∀ n : ℕ, ∃ K : ℕ, ∀ k ≥ K, row n (k+n) = row n k) ∧
    (∀ n t : ℕ, 0 < n → (∃ K : ℕ, ∀ k ≥ K, row n (k+t) = row n k) → n ∣ t) := by
  sorry

end OMA.S_oeis_a365383
