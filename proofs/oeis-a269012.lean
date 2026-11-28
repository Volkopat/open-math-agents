import OMAStatements.S_oeis_a269012

namespace A269012Proof

open OMA.S_oeis_a269012

abbrev Col := Fin 2 → Fin 2

def w (c : Col) : ℕ := c 0 + (c 1 : ℕ)

def score : (n : ℕ) → ℕ → (Fin n → Col) → ℕ
  | 0, _, _ => 0
  | n+1, b, x => b * w (x 0) + score n (w (x 0)) (fun i => x i.succ)

lemma score_sum (m b : ℕ) (x : Fin (m+1) → Col) :
    score (m+1) b x = b * w (x 0) + ∑ j : Fin m, w (x j.castSucc) * w (x j.succ) := by
  induction m generalizing b with
  | zero => simp [score]
  | succ m ih =>
    rw [score, ih, Fin.sum_univ_succ]
    simp

lemma bit (a b : Fin 2) :
    (if (a : ℕ) + (b : ℕ) = 2 then 1 else 0) = (a : ℕ) * (b : ℕ) := by
  fin_cases a <;> fin_cases b <;> decide

lemma pair_score (m : ℕ) (x : Fin (m+1) → Col) :
    pairsTotallingTwo m (fun i j => x j i) = score (m+1) 0 x := by
  simp only [pairsTotallingTwo, Finset.card_filter, Fintype.sum_prod_type,
    Fin.sum_univ_two, bit, score_sum, Nat.zero_mul, Nat.zero_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold w
  ring

def cnt : ℕ → ℕ → ℤ → ℤ
  | 0, _, k => if k = 0 then 1 else 0
  | n+1, b, k => cnt n 0 k + 2 * cnt n 1 (k-b) + cnt n 2 (k-2*b)

lemma cnt_neg (n b : ℕ) (k : ℤ) (hk : k < 0) : cnt n b k = 0 := by
  induction n generalizing b k with
  | zero => simp [cnt, ne_of_lt hk]
  | succ n ih =>
    rw [cnt, ih _ _ hk, ih _ _ (by omega), ih _ _ (by omega)]
    norm_num

lemma count_sum (n b : ℕ) (k : ℤ) :
    (∑ x : Fin n → Col, if (score n b x : ℤ) = k then (1 : ℤ) else 0) = cnt n b k := by
  induction n generalizing b k with
  | zero => simp [score, cnt, eq_comm]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Col)).sum_comp, Fintype.sum_prod_type]
    change (∑ c : Col, ∑ x : Fin n → Col, if ((b * w c + score n (w c) x : ℕ) : ℤ) = k
      then (1 : ℤ) else 0) = _
    simp only [Nat.cast_add, Nat.cast_mul, ← eq_sub_iff_add_eq', ih]
    rw [← (finTwoArrowEquiv (Fin 2)).symm.sum_comp, Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two]
    change cnt n 0 (k - b * (0 : ℤ)) + cnt n 1 (k - b * (1 : ℤ)) +
      (cnt n 1 (k - b * (1 : ℤ)) + cnt n 2 (k - b * (2 : ℤ))) = _
    simp [cnt, mul_comm (b : ℤ) 2]
    ring

lemma a_cnt (n : ℕ) : (a n : ℤ) = cnt n 0 1 := by
  cases n with
  | zero => decide
  | succ m =>
    rw [a, Finset.card_filter, Nat.cast_sum, ← count_sum,
      ← (Equiv.piComm (fun (_ : Fin (m+1)) (_ : Fin 2) => Fin 2)).sum_comp]
    apply Finset.sum_congr rfl
    intro x _
    change ((if pairsTotallingTwo m (fun i j => x j i) = 1 then 1 else 0 : ℕ) : ℤ) = _
    rw [pair_score]
    split_ifs <;> simp_all

lemma rec_seq (k : ℕ) : (a (k+5) : ℤ) = 2*a (k+4) + 5*a (k+3) - 6*a (k+2) - 9*a (k+1) := by
  simp only [a_cnt]
  norm_num [cnt, cnt_neg]
  ring

lemma initial : a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 4 ∧ a 3 = 8 ∧ a 4 = 36 := by
  have h : (a 0 : ℤ) = 0 ∧ (a 1 : ℤ) = 0 ∧ (a 2 : ℤ) = 4 ∧
      (a 3 : ℤ) = 8 ∧ (a 4 : ℤ) = 36 := by
    simp only [a_cnt]
    decide
  exact_mod_cast h

open PowerSeries

lemma gf : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X - 3 * X ^ 2) ^ 2 = 4 * X ^ 2 := by
  let p := PowerSeries.mk (fun n => (a n : ℚ))
  change p * _ = _
  rw [show p * (1 - X - 3 * X ^ 2) ^ 2 =
    p - (p * X ^ 1 + p * X ^ 1) - 5 • (p * X ^ 2) + 6 • (p * X ^ 3) + 9 • (p * X ^ 4) by
      simp only [nsmul_eq_mul]
      ring, show (4 : PowerSeries ℚ) * X ^ 2 = 4 • (X ^ 2) by simp]
  ext n
  simp only [map_add, map_sub, map_nsmul, coeff_mul_X_pow', coeff_X_pow, p, coeff_mk]
  simp only [nsmul_eq_mul]
  obtain ⟨h0,h1,h2,h3,h4⟩ := initial
  by_cases h : n < 5
  · interval_cases n <;> norm_num [h0,h1,h2,h3,h4]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 5 ≤ n by omega)
    have hrec : (a (k+5) : ℚ) = 2*a (k+4) + 5*a (k+3) - 6*a (k+2) - 9*a (k+1) := by
      exact_mod_cast rec_seq k
    simp [Nat.add_comm 5 k, show k+5 ≠ 2 by omega]
    linarith

noncomputable def rhs (n : ℕ) : ℝ := 4 * (-((1 / 2) * (1 + Real.sqrt 13)) ^ n * (Real.sqrt 13 - 13 * n) +
        ((1 / 2) * (1 - Real.sqrt 13)) ^ n * (Real.sqrt 13 + 13 * n)) / 169

lemma rhs_rec (k : ℕ) : rhs (k+5) = 2*rhs (k+4) + 5*rhs (k+3) - 6*rhs (k+2) - 9*rhs (k+1) := by
  have hs : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  simp only [rhs, pow_add, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  generalize ((1/2 : ℝ) * (1 + Real.sqrt 13)) ^ k = u
  generalize ((1/2 : ℝ) * (1 - Real.sqrt 13)) ^ k = v
  grind +ring

lemma closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℝ) = rhs n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hb : n < 5
    · obtain ⟨h0,h1,h2,h3,h4⟩ := initial
      have hs : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
      interval_cases n <;> simp only [rhs,h1,h2,h3,h4] <;> push_cast <;> grind +ring only
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le' (show 5 ≤ n by omega)
      have hr : (a (k+5) : ℝ) = 2*a (k+4) + 5*a (k+3) - 6*a (k+2) - 9*a (k+1) := by
        exact_mod_cast rec_seq k
      rw [hr, rhs_rec, ih _ (by omega) (by omega), ih _ (by omega) (by omega),
        ih _ (by omega) (by omega), ih _ (by omega) (by omega)]

end A269012Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a269012.main := by
  refine ⟨?_, A269012Proof.gf, A269012Proof.closed⟩
  intro n hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le' hn
  simpa using A269012Proof.rec_seq k
