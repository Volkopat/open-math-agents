import OMAStatements.S_oeis_a242145

namespace A242145Proof

open OMA.S_oeis_a242145 PowerSeries

noncomputable def box (n : ℕ) : ℚ⟦X⟧ :=
  ∑ i ∈ Finset.range (n+1), X^i

def geom : ℚ⟦X⟧ := PowerSeries.mk fun _ => 1

private theorem good_iff_sum {n : ℕ} (x : Fin 6 → Fin (n+1)) :
    good x ↔ (∑ j : Fin 6, (x j : ℕ)) ≤ 3*n := by
  simp only [good, decide_eq_true_eq, Nat.lt_one_iff, forall_eq, zero_add]
  exact (Finset.sum_fin_eq_sum_range (fun j => (x j : ℕ))).symm ▸ Iff.rfl

/-- Expanding the six factors chooses the six entries independently. -/
private theorem box_pow_six (n : ℕ) :
    (box n)^6 = ∑ x : Fin 6 → Fin (n+1), (X : ℚ⟦X⟧)^(∑ j, (x j : ℕ)) := by
  have h := Fintype.prod_sum (fun (_ : Fin 6) (d : Fin (n+1)) => (X : ℚ⟦X⟧)^d.val)
  simpa only [Fin.sum_univ_eq_sum_range, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.prod_pow_eq_pow_sum, box] using h

theorem count_coeff (n : ℕ) :
    (a n : ℚ) = coeff (3*n) (geom * (box n)^6) := by
  rw [box_pow_six, Finset.mul_sum, map_sum]
  simp only [coeff_mul_X_pow', geom, coeff_mk, Finset.sum_boole]
  unfold a
  push_cast
  congr 2
  ext x
  simp [good_iff_sum]

private theorem box_as_difference (n : ℕ) : box n = geom * (1-X^(n+1)) := by
  have h : geom * (1-X) = 1 := mk_one_mul_one_sub_eq_one ℚ
  have hbox : box n * (1-X) = 1-X^(n+1) := geom_sum_mul_neg _ _
  rw [← hbox, mul_left_comm, h, mul_one]

private theorem coeff_geom_seven (k : ℕ) :
    coeff k (geom^7) = ((k+6).choose 6 : ℚ) := by
  have h : geom^7 = (mk fun j => ((6+j).choose 6 : ℚ)) := mk_one_pow_eq_mk_choose_add ℚ 6
  rw [h,coeff_mk,Nat.add_comm]

/-- Inclusion-exclusion over the six entries. At degree 3*n, at most two shifts can contribute. -/
theorem coefficient_formula (n : ℕ) : coeff (3*n) (geom*(box n)^6) =
    (Nat.choose (3*n+6) 6:ℚ) - 6*(Nat.choose (2*n+5) 6:ℚ) + 15*(Nat.choose (n+4) 6:ℚ) := by
  let K := n+1
  let B := geom^7
  have expand : geom * (box n)^6 =
      B - 6 • (B * X^K) + 15 • (B * X^(K*2)) - 20 • (B * X^(K*3)) +
        15 • (B * X^(K*4)) - 6 • (B * X^(K*5)) + B * X^(K*6) := by
    rw [box_as_difference n]
    simp only [B,K,pow_mul,nsmul_eq_mul]
    ring
  rw [expand]
  simp only [map_add,map_sub,map_nsmul]
  simp only [nsmul_eq_mul,coeff_mul_X_pow',B,coeff_geom_seven,K]
  by_cases hn : n < 2
  · interval_cases n <;> norm_num [Nat.choose]
  · simp (disch := omega) only [if_pos,if_neg,mul_zero,sub_zero,add_zero]
    rw [show 3*n-(n+1)+6 = 2*n+5 by omega,
        show 3*n-(n+1)*2+6 = n+4 by omega]
    norm_num

end A242145Proof

namespace A242145Proof

open OMA.S_oeis_a242145 PowerSeries

private def bin6 (x : ℚ) : ℚ := x*(x-1)*(x-2)*(x-3)*(x-4)*(x-5)/720

private theorem choose_six (k : ℕ) : (k.choose 6 : ℚ) = bin6 k := by
  by_cases small : k < 5
  · interval_cases k <;> norm_num [bin6, Nat.choose]
  have eq := congrArg (fun t : ℕ => (t : ℚ)) (Nat.descFactorial_eq_factorial_mul_choose k 6)
  norm_num [Nat.descFactorial_succ, Nat.factorial, Nat.cast_sub (show 5≤k by omega),
    Nat.cast_sub (show 4≤k by omega), Nat.cast_sub (show 3≤k by omega),
    Nat.cast_sub (show 2≤k by omega), Nat.cast_sub (show 1≤k by omega)] at eq
  unfold bin6
  linarith only [eq]

private def total (x : ℚ) : ℚ := bin6 (3*x+6)-6*bin6 (2*x+5)+15*bin6 (x+4)

private theorem recurrenceFromTotal (count : ∀ n : ℕ, (a n : ℚ) = total n) (n : ℕ) (hn : 8≤n) :
    (a n : ℚ) = 7*a (n-1)-21*a (n-2)+35*a (n-3)-35*a (n-4)+21*a (n-5)-7*a (n-6)+a (n-7) := by
  simp (disch := omega) only [count, Nat.cast_sub, Nat.cast_ofNat, Nat.cast_one, total, bin6]
  ring

private theorem solutionOfCount (h : ∀ n : ℕ, (a n : ℚ) = ((3*n+6).choose 6 : ℚ) -
    6*((2*n+5).choose 6 : ℚ) + 15*((n+4).choose 6 : ℚ)) : type_of% @OMA.S_oeis_a242145.main := by
  have count (n : ℕ) : (a n : ℚ) = total n := by
    rw [h]
    simp [choose_six, total]
  refine ⟨?_, recurrenceFromTotal count⟩
  let A : ℚ⟦X⟧ := mk fun n => if n<1 then 0 else (a n:ℚ)
  change A*(1-X)^7 = _
  have den : A*(1-X)^7 = A-C 7*(A*X^1)+C 21*(A*X^2)-C 35*(A*X^3)+C 35*(A*X^4)
      -C 21*(A*X^5)+C 7*(A*X^6)-A*X^7 := by simp only [map_ofNat]; ring
  have num : (X : ℚ⟦X⟧)*(42+141*X+175*X^2-13*X^3+21*X^4-7*X^5+X^6) =
      C 42*X^1+C 141*X^2+C 175*X^3-C 13*X^4+C 21*X^5-C 7*X^6+C 1*X^7 := by
    simp only [map_ofNat, map_one]; ring
  rw [den,num]
  ext n
  simp only [map_add, map_sub, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', A, coeff_mk]
  by_cases small : n ≤ 7
  · interval_cases n <;> norm_num [count,total,bin6]
  · simp (disch := omega) only [if_pos, if_neg]
    linarith [recurrenceFromTotal count n (by omega)]

end A242145Proof

open A242145Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a242145.main :=
  solutionOfCount fun n => (count_coeff n).trans (coefficient_formula n)
