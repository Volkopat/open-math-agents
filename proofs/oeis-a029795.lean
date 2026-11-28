import OMAStatements.S_oeis_a029795

/-!
# OEIS A029795: the sequence does not eventually contain every integer

Every power `10 ^ j` with `j ≥ 1` lies in the sequence (`10 ^ j` and `10 ^ (3 j)` both have digit
set `{0, 1}`), so the defining predicate holds infinitely often and every term `a n` satisfies it.
If `a n = m + n` held for all large `n`, every large integer would satisfy the predicate, but
`2 · 10 ^ j` does not: its cube `8 · 10 ^ (3 j)` contains the digit `8`.
-/

namespace OMA.OeisA029795

open OMA.S_oeis_a029795

private lemma digits_pow_mul (j d : ℕ) (hd : 0 < d) (hd10 : d < 10) :
    Nat.digits 10 (10 ^ j * d) = List.replicate j 0 ++ [d] := by
  rw [Nat.digits_base_pow_mul (by norm_num) hd, Nat.digits_of_lt 10 d (by omega) hd10]

private lemma P_pow (j : ℕ) (hj : 0 < j) : P (10 ^ j) := by
  unfold P
  have h1 : (10 : ℕ) ^ j = 10 ^ j * 1 := (mul_one _).symm
  have h3 : ((10 : ℕ) ^ j) ^ 3 = 10 ^ (3 * j) * 1 := by rw [mul_one, ← pow_mul, mul_comm]
  rw [h3, h1, digits_pow_mul _ _ (by norm_num) (by norm_num),
    digits_pow_mul _ _ (by norm_num) (by norm_num)]
  ext x
  simp only [List.mem_toFinset, List.mem_append, List.mem_replicate, List.mem_singleton]
  constructor
  · rintro (⟨_, hx⟩ | hx)
    · exact Or.inl ⟨by omega, hx⟩
    · exact Or.inr hx
  · rintro (⟨_, hx⟩ | hx)
    · exact Or.inl ⟨by omega, hx⟩
    · exact Or.inr hx

private lemma not_P_two (j : ℕ) : ¬ P (10 ^ j * 2) := by
  unfold P
  intro h
  have h3 : ((10 : ℕ) ^ j * 2) ^ 3 = 10 ^ (3 * j) * 8 := by rw [mul_pow, ← pow_mul, mul_comm j 3]; norm_num
  rw [h3, digits_pow_mul _ _ (by norm_num) (by norm_num),
    digits_pow_mul _ _ (by norm_num) (by norm_num)] at h
  have h8 : 8 ∈ (List.replicate (3 * j) 0 ++ [8]).toFinset := by simp
  rw [← h] at h8
  simp [List.mem_replicate] at h8

private lemma P_infinite : (setOf P).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro x
  refine ⟨10 ^ (x + 1), P_pow (x + 1) (by omega), ?_⟩
  have := Nat.lt_pow_self (show 1 < 10 by norm_num) (n := x + 1)
  omega

end OMA.OeisA029795

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a029795.main) := by
  rintro ⟨m, N, h⟩
  set j := m + N + 1 with hj
  have hjk : j < 10 ^ j := Nat.lt_pow_self (show 1 < 10 by norm_num) (n := j)
  set k := 10 ^ j * 2 with hk
  have hkm : m + N ≤ k := by omega
  have hn := h (k - m) (by omega)
  have hmem : OMA.S_oeis_a029795.P (OMA.S_oeis_a029795.a (k - m)) := by
    unfold OMA.S_oeis_a029795.a
    exact Nat.nth_mem_of_infinite OMA.OeisA029795.P_infinite _
  rw [hn, show m + (k - m) = k by omega] at hmem
  exact OMA.OeisA029795.not_P_two j hmem
