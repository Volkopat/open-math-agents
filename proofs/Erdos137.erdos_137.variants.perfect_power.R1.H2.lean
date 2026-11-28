import OMAReductions.R_Erdos137_erdos_137_variants_perfect_power_R1
import Mathlib.NumberTheory.Bertrand

open Finset

theorem OMA.solution : OMA.R_Erdos137_erdos_137_variants_perfect_power_R1.H2 := by
  intro k n hk h
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.bertrand ((n + k) / 2) (by omega)
  have hpk : p < k := lt_of_not_ge fun h' => h ⟨p, h', by omega, hp⟩
  have h2 : n + k < 2 * p := by omega
  refine ⟨p, hp, ?_⟩
  rw [Nat.factorization_prod_apply fun m hm => by simp at hm; omega,
    sum_eq_single_of_mem p (by simp; omega)]
  · simp [hp.factorization]
  intro m hm hne
  refine Nat.factorization_eq_zero_of_not_dvd ?_
  rintro ⟨_ | _ | t, rfl⟩ <;> simp at hm hne
  nlinarith [hm.2]
