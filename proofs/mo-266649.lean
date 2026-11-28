import OMAStatements.S_mo_266649
import Mathlib

-- Problem: mo-266649, does every finite group of non-prime order without elements of order
-- p^2 have an automorphism of order 2 moving some subgroup?
-- Original formalization by @ivillar, PR #24080.
-- Squarefreeness and finite subgroup cardinality simplify the same order-six witness.
--
-- No. In the cyclic group of order 6 every automorphism is a power map
-- x -> x^m, so it sends each subgroup into itself. Cardinality gives equality.
-- Its element orders divide the squarefree number 6, so none is
-- p^2, and 6 is not a prime.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_266649.main) := by
  intro h
  have hcard : Nat.card (Multiplicative (ZMod 6)) = 6 := by
    first
      | simp
      | (rw [Nat.card_eq_fintype_card]; rfl)
  have hA : ∀ p : ℕ, p.Prime → ∀ g : Multiplicative (ZMod 6), orderOf g ≠ p ^ 2 := by
    intro p hp g hg
    have h1 := orderOf_dvd_natCard g
    rw [hcard, hg] at h1
    exact (Nat.squarefree_iff_prime_squarefree.mp (by decide +kernel : Squarefree 6) p hp)
      (by simpa [pow_two] using h1)
  have hB : ∀ p : ℕ, p.Prime → Nat.card (Multiplicative (ZMod 6)) ≠ p := by
    intro p hp hpc
    rw [hcard] at hpc
    rw [← hpc] at hp
    exact absurd hp (by norm_num)
  obtain ⟨φ, -, H, hH⟩ := h (Multiplicative (ZMod 6)) hA hB
  apply hH
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic
    (φ : Multiplicative (ZMod 6) ≃* Multiplicative (ZMod 6)).toMonoidHom
  apply Subgroup.eq_of_le_of_card_ge
  · rintro x ⟨y, hy, rfl⟩
    change φ.toMonoidHom y ∈ H
    rw [hm y]
    exact H.zpow_mem hy m
  · exact (Subgroup.card_map_of_injective φ.injective).ge
