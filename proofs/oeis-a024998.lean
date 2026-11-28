import OMAStatements.S_oeis_a024998

/-!
David Callan gave a generating function for these walks in OEIS A024998 (2004).
We prove R. J. Mathar's recurrence (2013) by reflecting walks and comparing
coefficients in a polynomial derivative.
-/

namespace A024998Proof

open OMA.S_oeis_a024998 Polynomial

noncomputable def B : ℤ[X] := 1 + X^2
noncomputable def P : ℤ[X] := 1 + X + X^2

private def permitted {n : ℕ} (w : Fin n → Fin 3) : Prop :=
  ∀ i, i.val < 2 → w i ≠ 1

private instance {n : ℕ} (w : Fin n → Fin 3) : Decidable (permitted w) := by
  unfold permitted
  infer_instance

private def weight {n : ℕ} (w : Fin n → Fin 3) : ℕ := ∑ i, (w i).val

private def ways (n t : ℕ) : ℤ :=
  ∑ w : Fin n → Fin 3, if permitted w ∧ t = weight w then 1 else 0

private theorem pos_end (n : ℕ) : (a n : ℤ) = ways n (n+1) := by
  rw [a, ← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro w _
  have h : (∑ i, ((w i : ℤ) - 1)) = (weight w : ℤ) - n := by
    simp [weight, Finset.sum_sub_distrib]
  have ht : (weight w : ℤ) - n = 1 ↔ n + 1 = weight w := by omega
  simp only [h, ht, permitted]
  by_cases good : (∀ i : Fin n, i.val < 2 → w i ≠ 1) ∧ n + 1 = weight w <;> simp [good]

private theorem reflection (m : ℕ) : ways (m+2) (m+1) = ways (m+2) (m+3) := by
  let e := Equiv.piCongrRight fun _ : Fin (m+2) => (Fin.revPerm : Equiv.Perm (Fin 3))
  unfold ways
  rw [← e.sum_comp (fun w => if permitted w ∧ m+1 = weight w then (1:ℤ) else 0)]
  apply Finset.sum_congr rfl
  intro w _
  have hfix : ∀ x : Fin 3, x.rev ≠ 1 ↔ x ≠ 1 := by decide
  have hperm : permitted (e w) ↔ permitted w := by
    change (∀ i, i.val < 2 → (w i).rev ≠ 1) ↔ _
    simp only [permitted, hfix]
  have hval : ∀ x : Fin 3, x.rev.val + x.val = 2 := by decide
  have hw : weight (e w) + weight w = 2 * (m+2) := by
    change (∑ i, (w i).rev.val) + (∑ i, (w i).val) = _
    simp only [← Finset.sum_add_distrib, hval, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, Nat.mul_comm]
  simp only [hperm, show m+1 = weight (e w) ↔ m+3 = weight w by omega]

private noncomputable def factor (i : ℕ) (d : Fin 3) : ℤ[X] :=
  if (i < 2 → d ≠ 1) then X^d.val else 0

private theorem factors (i : ℕ) : (∑ d : Fin 3, factor i d) = if i < 2 then B else P := by
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  by_cases h : i < 2 <;> norm_num [factor, h, B, P, Fin.sum_univ_succ, h21, add_assoc]

private theorem product_formula (m : ℕ) :
    (∏ i : Fin (m+2), ∑ d : Fin 3, factor i.val d) = B^2 * P^m := by
  simp only [factors]
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp [pow_two, mul_assoc]

private theorem ways_coeff (m t : ℕ) : ways (m+2) t = (B^2 * P^m).coeff t := by
  rw [← product_formula, Fintype.prod_sum, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro w _
  simp only [factor, Finset.prod_ite_zero, Finset.mem_univ, forall_const,
    Finset.prod_pow_eq_pow_sum]
  change (if permitted w ∧ t = weight w then (1:ℤ) else 0) =
    (if permitted w then (X:ℤ[X])^(weight w) else 0).coeff t
  by_cases h : permitted w <;> simp [h, coeff_X_pow]

/-- Reflecting every step exchanges walks ending at 1 and at -1. A third
nonlevel step combines the two counts in one central coefficient. -/
theorem twice_count (m : ℕ) : 2 * (a (m+2) : ℤ) = (B^3 * P^m).coeff (m+3) := by
  rw [show B^3*P^m = B^2*P^m + X^2*(B^2*P^m) by unfold B; ring,
    coeff_add, show m+3=m+1+2 by omega, coeff_X_pow_mul, ← ways_coeff, ← ways_coeff,
    reflection, pos_end]
  ring

private theorem differentiated (k : ℕ) :
    let T := (X^2-1)*B^4*P^(k+1)
    X * derivative T - C ((k:ℤ)+6) * T =
      C ((k:ℤ)+6) * (B^3*P^(k+3)) - C (3*(k:ℤ)+13) * ((B^3*P^(k+2))*X^1) -
      C ((k:ℤ)+12) * ((B^3*P^(k+1))*X^2) + C (3*(k:ℤ)+3) * ((B^3*P^k)*X^3) := by
  have dB : derivative B = 2*X := by simp [B]
  have dP : derivative P = 1+2*X := by simp [P]
  have dPk : derivative (P^(k+1)) = C ((k:ℤ)+1)*P^k*(1+2*X) := by
    rw [derivative_pow, dP]
    simp
  have dB4 : derivative (B^4) = 4*B^3*(2*X) := by rw [derivative_pow, dB]; norm_num
  have dX2 : derivative ((X:ℤ[X])^2-1) = 2*X := by simp
  dsimp only
  simp only [derivative_mul, dPk, dB4, dX2]
  simp only [pow_add, map_add, map_mul, map_one, map_ofNat, C_eq_natCast, B, P]
  ring

end A024998Proof

open Polynomial OMA.S_oeis_a024998 A024998Proof in
theorem OMA.solution :
    type_of% @OMA.S_oeis_a024998.main := by
  intro n hn
  by_cases hn4 : n=4
  · subst n
    decide +kernel
  obtain ⟨k,rfl⟩ : ∃ k, n=k+5 := ⟨n-5, by omega⟩
  have h := congrArg (fun f : ℤ[X] => f.coeff (k+6)) (differentiated k)
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_mul,
    coeff_derivative] at h
  simp (disch := omega) only [if_pos, Nat.cast_add, Nat.cast_ofNat] at h
  change ((k:ℤ)+5+1)*a (k+5) + (-3*((k:ℤ)+5)+2)*a (k+4) +
    (-((k:ℤ)+5)-7)*a (k+3) + 3*((k:ℤ)+5-4)*a (k+2) = 0
  rw [show k+6-1=k+2+3 by omega, show k+6-2=k+1+3 by omega, show k+6-3=k+3 by omega] at h
  rw [← twice_count (k+3), ← twice_count (k+2), ← twice_count (k+1), ← twice_count k] at h
  linarith only [h]
