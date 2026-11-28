import OMAStatements.S_mo_471006
import Mathlib

open Polynomial OMA.S_mo_471006 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_471006.main) := by
  intro h
  let f (n : ℕ) : ℤ[X] := (X - C 1) ^ (n + 1)
  have degree (n : ℕ) : (f n).natDegree = n + 1 := by
    change ((X - C (1 : ℤ)) ^ (n + 1)).natDegree = n + 1
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, Nat.mul_one]
  have hf : Function.Injective f := by
    intro m n he
    have := congrArg Polynomial.natDegree he
    rw [degree, degree] at this
    omega
  apply Set.infinite_range_of_injective hf
  apply (h 2 1 (by norm_num) (by norm_num)).subset
  rintro _ ⟨n, rfl⟩
  change admissible 2 1 (f n)
  have hmap : (f n).map (Int.castRingHom ℝ) = (X - C (1 : ℝ)) ^ (n + 1) := by
    simp [f, Polynomial.map_sub, Polynomial.map_pow]
  have hroots : ((f n).map (Int.castRingHom ℝ)).roots =
      (n + 1) • ({1} : Multiset ℝ) := by
    rw [hmap, Polynomial.roots_pow, Polynomial.roots_X_sub_C]
  refine ⟨(Polynomial.monic_X_sub_C (1 : ℤ)).pow _, by rw [degree]; omega, ?_, ?_, ?_⟩
  · rw [hmap]
    exact (Polynomial.Splits.X_sub_C (1 : ℝ)).pow _
  · intro y hy
    rw [hroots] at hy
    have he : y = 1 := by simpa using Multiset.mem_of_mem_nsmul hy
    norm_num [he]
  · rw [hroots, degree]
    have hne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    simp only [Multiset.nsmul_singleton, Multiset.sum_replicate, nsmul_eq_mul, mul_one]
    exact div_self hne