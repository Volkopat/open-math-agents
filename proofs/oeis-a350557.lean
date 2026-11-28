import OMAStatements.S_oeis_a350557
import Mathlib

open OMA.S_oeis_a350557

private lemma df_succ (n : ℕ) : df (n + 1) = (2 * (n : ℚ) + 1) * df n := by
  unfold df
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  have : ((2 * n).factorial : ℚ) ≠ 0 := by positivity
  have : (n.factorial : ℚ) ≠ 0 := by positivity
  have : ((n : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

private def cc (k i : ℕ) : ℚ := ((i - 1).choose (k - 1) : ℚ) * 2 ^ i * (i.factorial : ℚ) / ((2 * i).factorial : ℚ)

private lemma cc_df (k n : ℕ) : cc k (n + 1) * df (n + 1) = (n.choose (k - 1) : ℚ) := by
  unfold cc df
  rw [show n + 1 - 1 = n by omega]
  have : ((2 * (n + 1)).factorial : ℚ) ≠ 0 := by positivity
  have : ((n + 1).factorial : ℚ) ≠ 0 := by positivity
  field_simp

private lemma T_pos (n k : ℕ) (hk : k ≠ 0) : T n k = (∑ i ∈ Finset.Icc k n, cc k i) * df n := by
  unfold T cc; rw [if_neg hk]

private lemma T_zero_lt (n k : ℕ) (hk : n < k) : T n k = 0 := by
  rw [T_pos n k (by omega), Finset.Icc_eq_empty (by omega)]; simp

private lemma T_rec (n k : ℕ) (hk : k ≠ 0) :
    T (n + 1) k = (n.choose (k - 1) : ℚ) + (2 * (n : ℚ) + 1) * T n k := by
  rcases Nat.lt_or_ge (n + 1) k with h | h
  · rw [T_zero_lt _ _ h, T_zero_lt _ _ (by omega), Nat.choose_eq_zero_of_lt (by omega)]; simp
  · rw [T_pos _ _ hk, T_pos _ _ hk, Finset.sum_Icc_succ_top h, add_mul, cc_df, df_succ]
    ring

private lemma T_rec0 (n : ℕ) : T (n + 1) 0 = (2 * (n : ℚ) + 1) * T n 0 := by
  unfold T; simp only [if_pos]; exact df_succ n

private lemma T_diag (n : ℕ) : T n n = 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [T, df]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [T_rec m (m + 1) (by omega), T_zero_lt m (m + 1) (by omega), show m + 1 - 1 = m by omega,
      Nat.choose_self]
    simp

private lemma Mrec (j k : ℕ) (hk : k ≠ 0) :
    M (j + 1) k + (2 * (j : ℚ) + 1) * M j k =
      (if k ≤ j + 1 then (-1) ^ (j + 1 - k) * (j.choose (k - 1) : ℚ) else 0) := by
  unfold M
  rcases Nat.lt_or_ge (j + 1) k with h | h
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; ring
  · rcases Nat.eq_or_lt_of_le h with h2 | h2
    · subst h2
      rw [if_pos le_rfl, if_neg (by omega), if_pos le_rfl, Nat.sub_self, T_diag,
        show j + 1 - 1 = j by omega, Nat.choose_self]
      ring
    · rw [if_pos h, if_pos (by omega), if_pos h, T_rec j k hk,
        show j + 1 - k = (j - k) + 1 by omega, pow_succ]
      ring

private lemma Mrec0 (j : ℕ) : M (j + 1) 0 + (2 * (j : ℚ) + 1) * M j 0 = 0 := by
  unfold M
  rw [if_pos (by omega), if_pos (by omega), T_rec0, Nat.sub_zero, Nat.sub_zero, pow_succ]
  ring

private lemma Ldec (N j : ℕ) (hj : j ≤ N + 1) :
    L (N + 1) j = (if j = 0 then 0 else (N.choose (j - 1) : ℚ)) + (2 * (j : ℚ) + 1) * (N.choose j : ℚ) := by
  unfold L
  rw [if_pos hj]
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0; simp
  · rw [if_neg (by omega), if_neg (by omega), show N + 1 - 1 = N by omega]
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [show i + 1 - 1 = i by omega]
    have hc := Nat.choose_succ_right_eq N i
    have hc' : ((N.choose (i + 1) : ℕ) : ℚ) * ((i : ℚ) + 1) = (N.choose i : ℚ) * ((N : ℚ) - i) := by
      rcases Nat.lt_or_ge N i with hh | hh
      · rw [Nat.choose_eq_zero_of_lt hh, Nat.choose_eq_zero_of_lt (by omega)]; simp
      · have := congrArg (fun x : ℕ => (x : ℚ)) hc
        push_cast [Nat.cast_sub hh] at this
        linarith
    have : ((i : ℚ) + 1) ≠ 0 := by positivity
    have hq : ((N.choose (i + 1) : ℕ) : ℚ) = (N.choose i : ℚ) * ((N : ℚ) - i) / ((i : ℚ) + 1) := by
      rw [eq_div_iff this]; exact hc'
    rw [hq]
    push_cast
    field_simp
    ring

private lemma BI (N m : ℕ) :
    ∑ j ∈ Finset.range (N + 1), (N.choose j : ℚ) *
      (if m ≤ j then (-1) ^ (j - m) * (j.choose m : ℚ) else 0) = (if N = m then 1 else 0) := by
  rcases Nat.lt_or_ge N m with h | h
  · rw [if_neg (by omega)]
    apply Finset.sum_eq_zero
    intro j hj; simp at hj
    rw [if_neg (by omega)]; ring
  · obtain ⟨r, rfl⟩ : ∃ r, N = m + r := ⟨N - m, by omega⟩
    rw [show m + r + 1 = m + (r + 1) by ring, Finset.sum_range_add]
    rw [Finset.sum_eq_zero (fun j hj => by simp at hj; rw [if_neg (by omega)]; ring), zero_add]
    have key : ∀ t ∈ Finset.range (r + 1), ((m + r).choose (m + t) : ℚ) *
        (if m ≤ m + t then (-1) ^ (m + t - m) * ((m + t).choose m : ℚ) else 0) =
        ((m + r).choose m : ℚ) * ((-1) ^ t * (r.choose t : ℚ)) := by
      intro t ht
      simp at ht
      rw [if_pos (by omega), show m + t - m = t by omega]
      have hm := @Nat.choose_mul (m + r) (m + t) m (by omega)
      rw [show m + r - m = r by omega, show m + t - m = t by omega] at hm
      have hm' := congrArg (fun x : ℕ => (x : ℚ)) hm
      push_cast at hm'
      linear_combination (-1 : ℚ) ^ t * hm'
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
    have ha := @Int.alternating_sum_range_choose r
    have ha' := congrArg (fun z : ℤ => (z : ℚ)) ha
    push_cast at ha'
    rw [ha']
    by_cases hr : r = 0
    · subst hr; simp
    · rw [if_neg hr, if_neg (by omega)]; ring

private lemma prod1 (n k : ℕ) : (∑ j ∈ Finset.range (n + 1), L n j * M j k) = (if n = k then 1 else 0) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp [L, M]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp [T, df]
    · rw [if_neg (by omega), if_neg (by omega)]
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have e0 : ∑ j ∈ Finset.range (N + 1 + 1), L (N + 1) j * M j k =
      ∑ j ∈ Finset.range (N + 1 + 1), ((if j = 0 then 0 else (N.choose (j - 1) : ℚ)) * M j k +
        (2 * (j : ℚ) + 1) * (N.choose j : ℚ) * M j k) :=
    Finset.sum_congr rfl (fun j hj => by simp at hj; rw [Ldec N j (by omega)]; ring)
  have e1 : ∑ j ∈ Finset.range (N + 1 + 1), (if j = 0 then 0 else (N.choose (j - 1) : ℚ)) * M j k =
      ∑ j ∈ Finset.range (N + 1), (N.choose j : ℚ) * M (j + 1) k := by
    rw [Finset.sum_range_succ']
    simp
  have e2 : ∑ j ∈ Finset.range (N + 1 + 1), (2 * (j : ℚ) + 1) * (N.choose j : ℚ) * M j k =
      ∑ j ∈ Finset.range (N + 1), (2 * (j : ℚ) + 1) * (N.choose j : ℚ) * M j k := by
    rw [Finset.sum_range_succ, Nat.choose_succ_self]; simp
  rw [e0, Finset.sum_add_distrib, e1, e2, ← Finset.sum_add_distrib]
  have hterm : ∀ j ∈ Finset.range (N + 1), (N.choose j : ℚ) * M (j + 1) k +
      (2 * (j : ℚ) + 1) * (N.choose j : ℚ) * M j k = (N.choose j : ℚ) * (M (j + 1) k + (2 * (j : ℚ) + 1) * M j k) := by
    intro j _; ring
  rw [Finset.sum_congr rfl hterm]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [if_neg (by omega)]
    apply Finset.sum_eq_zero; intro j _; rw [Mrec0]; ring
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Finset.sum_congr rfl (fun j _ => by rw [Mrec j (m + 1) (by omega)])]
    have := BI N m
    have hiff : (if N + 1 = m + 1 then (1 : ℚ) else 0) = (if N = m then 1 else 0) := by
      by_cases h : N = m <;> simp [h]
    rw [hiff]
    rw [← this]
    apply Finset.sum_congr rfl
    intro j _
    rw [show m + 1 - 1 = m by omega]
    by_cases hj : m ≤ j
    · rw [if_pos (by omega), if_pos hj, show j + 1 - (m + 1) = j - m by omega]
    · rw [if_neg (by omega), if_neg hj]

private lemma Lzero (j k : ℕ) (h : j < k) : L j k = 0 := by unfold L; rw [if_neg (by omega)]
private lemma Mzero (j k : ℕ) (h : j < k) : M j k = 0 := by unfold M; rw [if_neg (by omega)]

private lemma prod2 (n k : ℕ) : (∑ j ∈ Finset.range (n + 1), M n j * L j k) = (if n = k then 1 else 0) := by
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ := fun i j => L i j
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ := fun i j => M i j
  have hAB : A * B = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h1 : ∑ l : Fin (n + 1), A i l * B l j = ∑ l ∈ Finset.range (n + 1), L i l * M l j :=
      Fin.sum_univ_eq_sum_range (fun l => L i l * M l j) (n + 1)
    rw [h1]
    have h2 : ∑ l ∈ Finset.range (n + 1), L i l * M l j = ∑ l ∈ Finset.range (i + 1), L i l * M l j := by
      have hi : (i : ℕ) + 1 ≤ n + 1 := by omega
      rw [← Finset.sum_range_add_sum_Ico _ hi]
      rw [Finset.sum_eq_zero (s := Finset.Ico _ _) (fun l hl => by
        simp at hl; rw [Lzero i l (by omega)]; ring), add_zero]
    rw [h2, prod1]
    simp [Fin.ext_iff]
  have hBA : B * A = 1 := (Matrix.mul_eq_one_comm_of_card_eq (Fin (n + 1)) (Fin (n + 1)) ℚ rfl).mp hAB
  rcases Nat.lt_or_ge n k with h | h
  · rw [if_neg (by omega)]
    apply Finset.sum_eq_zero
    intro j hj; simp at hj
    rw [Lzero j k (by omega)]; ring
  · have := congrFun (congrFun hBA ⟨n, by omega⟩) ⟨k, by omega⟩
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    have h1 : ∑ l : Fin (n + 1), B ⟨n, by omega⟩ l * A l ⟨k, by omega⟩ =
        ∑ l ∈ Finset.range (n + 1), M n l * L l k :=
      Fin.sum_univ_eq_sum_range (fun l => M n l * L l k) (n + 1)
    rw [h1] at this
    rw [this]
    simp [Fin.ext_iff]

theorem OMA.solution : type_of% @OMA.S_oeis_a350557.main := fun n k => ⟨prod1 n k, prod2 n k⟩
