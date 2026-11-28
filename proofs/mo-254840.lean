import OMAStatements.S_mo_254840
import Mathlib

open OMA.S_mo_254840
open scoped InnerProductSpace

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_254840.main) := by
  rintro ⟨n, hn, S, hpm, horth, hcard⟩
  let v : S → EuclideanSpace ℝ (Fin n) := fun a => WithLp.toLp 2 (fun i => ((a.1 i : ℤ) : ℝ))
  have hinner : ∀ a b : S, ⟪v a, v b⟫_ℝ = ((∑ i, a.1 i * b.1 i : ℤ) : ℝ) := by
    intro a b
    simp only [v, PiLp.inner_apply, RCLike.inner_apply,
      conj_trivial]
    push_cast
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hz : ∀ a : S, v a ≠ 0 := by
    intro a h
    have h1 := hinner a a
    rw [h, inner_zero_left] at h1
    have h2 : (∑ i, a.1 i * a.1 i : ℤ) = n := by
      have : ∀ i, a.1 i * a.1 i = 1 := by
        intro i; rcases hpm a.1 a.2 i with h | h <;> rw [h] <;> norm_num
      simp [this]
    rw [h2] at h1
    have : (n : ℝ) = 0 := by exact_mod_cast h1.symm
    have : n = 0 := by exact_mod_cast this
    omega
  have ho : Pairwise fun a b : S => ⟪v a, v b⟫_ℝ = 0 := by
    intro a b hab
    rw [hinner, horth a.1 a.2 b.1 b.2 (fun h => hab (Subtype.ext h))]
    simp
  have hli : LinearIndependent ℝ v := linearIndependent_of_ne_zero_of_inner_eq_zero hz ho
  have := hli.fintype_card_le_finrank
  rw [finrank_euclideanSpace_fin, Fintype.card_coe] at this
  omega
