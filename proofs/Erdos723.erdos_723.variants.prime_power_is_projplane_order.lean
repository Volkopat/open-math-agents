import FormalConjectures.ErdosProblems.«723»

/-! Count the points of the projective plane over the finite field of the prescribed size. -/

open Configuration
open scoped LinearAlgebra.Projectivization

theorem OMA.solution : type_of% @Erdos723.erdos_723.variants.prime_power_is_projplane_order := by
  classical
  intro n hn
  obtain ⟨p,k,hp,hk,rfl⟩ := (isPrimePow_nat_iff n).mp hn
  haveI : Fact p.Prime := ⟨hp⟩
  let K := GaloisField p k
  let P := ℙ K (Fin 3 → K)
  letI : Fintype P := Fintype.ofFinite P
  refine ⟨P,P,inferInstance,inferInstance,inferInstance,inferInstance,?_⟩
  have hq : Nat.card K = p^k := GaloisField.card p k hk.ne'
  have points := Projectivization.card_of_finrank K (Fin 3 → K)
    (show Module.finrank K (Fin 3 → K) = 3 by simp)
  change Nat.card P = _ at points
  rw [Nat.card_eq_fintype_card, ProjectivePlane.card_points P P, hq] at points
  simp [Finset.sum_range_succ] at points
  let q := ProjectivePlane.order P P
  change q = p ^ k
  change q ^ 2 + q + 1 = _ at points
  rcases lt_trichotomy q (p^k) with h | h | h
  · nlinarith [Nat.pow_le_pow_left h.le 2]
  · exact h
  · nlinarith [Nat.pow_le_pow_left h.le 2]
