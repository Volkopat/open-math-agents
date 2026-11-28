import OMAReductions.R_mse_2615963_R1
import Mathlib.FieldTheory.Finite.Basic

-- Step mse-2615963.R1.H1: hypothesis H1 of reduction mse-2615963.R1
-- Credit: @luciusacarr
-- H1 := ∀ p : ℕ, p.Prime →   Int.ModEq (p : ℤ)     (∑ k ∈ Finset.range p, (Polynomial.Chebyshev.C ℤ ((p : ℤ) - 1)).eval (k : ℤ)) (-1)

/-!
`C_n` is monic of degree `n` for `n ≥ 1`. Reduce mod `p`: the sum over `k < p` becomes the sum
over all of `ZMod p`, and `∑ x, x ^ j` vanishes for `j < p - 1`, while `∑ x, x ^ (p - 1) = -1`.
So only the leading coefficient survives and the sum is `-1`.
-/

namespace OMA.MSE2615963H1

open Polynomial Finset

variable {R : Type*} [CommRing R]

lemma chebC_natDegree_le : ∀ n : ℕ, (Chebyshev.C R n).natDegree ≤ n
  | 0 => by simp [Chebyshev.C_zero]
  | 1 => by simpa [Chebyshev.C_one] using natDegree_X_le
  | n + 2 => by
    have h1 := chebC_natDegree_le (n + 1)
    have h0 := chebC_natDegree_le n
    have e : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
    rw [e, Chebyshev.C_add_two]
    have e1 : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e1]
    refine (natDegree_sub_le _ _).trans (max_le ?_ (h0.trans (by omega)))
    refine (natDegree_mul_le).trans ?_
    have := natDegree_X_le (R := R)
    omega

lemma chebC_coeff_self : ∀ n : ℕ, (Chebyshev.C R (n + 1 : ℕ)).coeff (n + 1) = 1
  | 0 => by simp [Chebyshev.C_one]
  | n + 1 => by
    have ih := chebC_coeff_self n
    have e : ((n + 1 + 1 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
    rw [e, Chebyshev.C_add_two]
    have e1 : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e1, coeff_sub, coeff_X_mul, ih,
      coeff_eq_zero_of_natDegree_lt ((chebC_natDegree_le n).trans_lt (by omega)), sub_zero]

lemma sum_pow_card_sub_one (p : ℕ) [Fact p.Prime] :
    ∑ x : ZMod p, x ^ (p - 1) = -1 := by
  have hp := (Fact.out : p.Prime).two_le
  have h : ∀ x : ZMod p, x ^ (p - 1) = 1 - (if x = 0 then 1 else 0) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      rw [zero_pow (by omega)]
      simp
    · rw [ZMod.pow_card_sub_one_eq_one hx]
      simp [hx]
  simp only [h, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, CharP.cast_eq_zero, mul_one]
  ring

end OMA.MSE2615963H1

open Polynomial Finset OMA.MSE2615963H1 in
theorem OMA.solution : OMA.R_mse_2615963_R1.H1 := by
  intro p hp
  have := Fact.mk hp
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 + 1 := ⟨p - 2, by have := hp.two_le; omega⟩
  rw [← ZMod.intCast_eq_intCast_iff]
  have eidx : ((n + 1 + 1 : ℕ) : ℤ) - 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [eidx]
  set F := ZMod (n + 1 + 1)
  push_cast
  have hmap : ∀ k : ℕ, (((Chebyshev.C ℤ ((n + 1 : ℕ) : ℤ)).eval (k : ℤ) : ℤ) : F) =
      (Chebyshev.C F ((n + 1 : ℕ) : ℤ)).eval (k : F) := by
    intro k
    have := eval_intCast_map (Int.castRingHom F) (Chebyshev.C ℤ ((n + 1 : ℕ) : ℤ)) (k : ℤ)
    rw [Chebyshev.map_C] at this
    simpa using this.symm
  simp only [Nat.cast_add, Nat.cast_one] at hmap
  rw [Finset.sum_congr rfl (fun k _ => hmap k)]
  have hsum : ∑ k ∈ range (n + 1 + 1), (Chebyshev.C F ((n : ℤ) + 1)).eval (k : F) =
      ∑ x : F, (Chebyshev.C F ((n : ℤ) + 1)).eval x := by
    refine Finset.sum_bij' (fun k _ => (k : F)) (fun x _ => x.val) (by simp)
      (fun x _ => Finset.mem_range.2 (ZMod.val_lt x)) ?_ ?_ (fun _ _ => rfl)
    · intro k hk
      exact ZMod.val_cast_of_lt (Finset.mem_range.1 hk)
    · intro x _
      exact ZMod.natCast_zmod_val x
  rw [hsum]
  have hdeg : (Chebyshev.C F ((n : ℤ) + 1)).natDegree < n + 1 + 1 := by
    have := chebC_natDegree_le (R := F) (n + 1)
    push_cast at this
    omega
  simp_rw [eval_eq_sum_range' hdeg]
  rw [Finset.sum_comm, Finset.sum_range_succ]
  have hlow : ∀ j ∈ range (n + 1),
      ∑ x : F, (Chebyshev.C F ((n : ℤ) + 1)).coeff j * x ^ j = 0 := by
    intro j hj
    rw [← Finset.mul_sum, FiniteField.sum_pow_lt_card_sub_one, mul_zero]
    rw [ZMod.card]
    have := Finset.mem_range.1 hj
    omega
  rw [Finset.sum_eq_zero hlow, zero_add, ← Finset.mul_sum]
  have hc : (Chebyshev.C F ((n : ℤ) + 1)).coeff (n + 1) = 1 := by
    have := chebC_coeff_self (R := F) n
    push_cast at this
    exact this
  rw [hc, one_mul]
  have := sum_pow_card_sub_one (n + 1 + 1)
  simpa using this
