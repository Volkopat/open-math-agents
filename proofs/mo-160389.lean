import OMAStatements.S_mo_160389
import Mathlib

open Finset

open OMA.S_mo_160389



theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_160389.main) := by
  intro h
  let a : Fin 3 → ℕ := ![1, 1, 3]
  obtain ⟨k, _, hk⟩ := h a (by intro i; fin_cases i <;> decide)
    (by decide) (by refine ⟨2, ?_⟩; decide)
  have hsum : (∑ i, a i) = 5 := by decide
  have hmultiple (j : ℕ) (hj : Representable a j) : 5 ∣ j := by
    obtain ⟨w, hw⟩ := hj
    have htotal : ∑ i : Fin 3, ∑ σ : Equiv.Perm (Fin 3), w σ * a (σ i) = 3 * j := by
      simp [hw]
    rw [Finset.sum_comm] at htotal
    simp_rw [← Finset.mul_sum, Equiv.sum_comp, hsum, ← Finset.sum_mul] at htotal
    exact ⟨(∑ σ, w σ) / 3, by omega⟩
  have hn : ¬ Representable a (5 * k + 1) := fun hj => by
    obtain ⟨r, hr⟩ := hmultiple _ hj
    omega
  have := hk _ hn
  omega
