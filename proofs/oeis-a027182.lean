import OMAStatements.S_oeis_a027182
import Mathlib

namespace OMA.S_oeis_a027182

/- Ratio lemmas for creative-telescoping term proofs (paste inside the helper namespace; needs `import Mathlib`).
   All in ℚ.  Atoms: x = C(N,k).  Typical use: express every binomial of the sum as (rational function)*x, then field_simp; ring. -/
lemma ch_succ (N k : ℕ) (hk : k ≤ N + 1) :   -- C(N,k)*(N+1) = C(N+1,k)*(N+1-k)
    (Nat.choose N k : ℚ) * ((N : ℚ) + 1) = Nat.choose (N + 1) k * (((N : ℚ) + 1) - k) := by
  have h := Nat.choose_mul_succ_eq N k
  have h' : ((Nat.choose N k * (N + 1) : ℕ) : ℚ) = ((Nat.choose (N + 1) k * (N + 1 - k) : ℕ) : ℚ) := by rw [h]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hk] at h'
  push_cast at h'
  exact h'

lemma ch_up (N k : ℕ) :                      -- C(N+1,k+1)*(k+1) = (N+1)*C(N,k)
    ((Nat.choose (N + 1) (k + 1) : ℚ)) * ((k : ℚ) + 1) = ((N : ℚ) + 1) * Nat.choose N k := by
  have h := Nat.add_one_mul_choose_eq N k
  have h' : (((N + 1) * Nat.choose N k : ℕ) : ℚ) = ((Nat.choose (N + 1) (k + 1) * (k + 1) : ℕ) : ℚ) := by rw [h]
  push_cast at h'
  linarith

lemma ch_right (N k : ℕ) (hk : k ≤ N) :      -- C(N,k+1)*(k+1) = (N-k)*C(N,k)
    (Nat.choose N (k + 1) : ℚ) * ((k : ℚ) + 1) = ((N : ℚ) - k) * (Nat.choose N k : ℚ) := by
  have h := Nat.choose_succ_right_eq N k
  have h' : ((Nat.choose N (k + 1) * (k + 1) : ℕ) : ℚ) = ((Nat.choose N k * (N - k) : ℕ) : ℚ) := by rw [h]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hk] at h'
  push_cast at h'
  linarith

/-- C(N,k) = C(N+1,k)*(N+1-k)/(N+1), for all k (both sides vanish for k > N+1). -/
lemma ch_down (N k : ℕ) :
    (Nat.choose N k : ℚ) = (Nat.choose (N + 1) k : ℚ) * (((N : ℚ) + 1) - k) / ((N : ℚ) + 1) := by
  rw [eq_div_iff (by positivity)]
  rcases Nat.lt_or_ge (N + 1) k with h | h
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]; simp
  · have := ch_succ N k h
    linarith

/-- C(N,k+1) = (N-k)*C(N,k)/(k+1), for all k. -/
lemma ch_next (N k : ℕ) :
    (Nat.choose N (k + 1) : ℚ) = ((N : ℚ) - k) * (Nat.choose N k : ℚ) / ((k : ℚ) + 1) := by
  rw [eq_div_iff (by positivity)]
  rcases Nat.lt_or_ge N k with h | h
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]; simp
  · exact ch_right N k h

/-- C(N+1,k) = C(N,k)*(N+1)/(N+1-k) for k ≤ N. -/
lemma ch_upN (N k : ℕ) (hk : k ≤ N) :
    (Nat.choose (N + 1) k : ℚ) = (Nat.choose N k : ℚ) * ((N : ℚ) + 1) / (((N : ℚ) + 1) - k) := by
  have : ((N : ℚ) + 1) - k ≠ 0 := by
    have : (k : ℚ) ≤ N := by exact_mod_cast hk
    linarith
  rw [eq_div_iff this]
  have := ch_succ N k (by omega)
  linarith

/-- support extension: sum over range N of a term that vanishes for k > n equals the sum over range (n+1). -/
lemma sum_ext {f : ℕ → ℚ} (n N : ℕ) (hN : n + 1 ≤ N) (hf : ∀ k, n < k → f k = 0) :
    ∑ k ∈ Finset.range N, f k = ∑ k ∈ Finset.range (n + 1), f k := by
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hN)
  intro k _ hk
  exact hf k (by simpa using hk)

lemma cb_succ (k : ℕ) : (Nat.choose (2 * (k + 1)) (k + 1) : ℚ) = 2 * (2 * (k : ℚ) + 1) * (Nat.choose (2 * k) k : ℚ) / ((k : ℚ) + 1) := by
  have := Nat.succ_mul_centralBinom_succ k
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at this
  have h' : (((k + 1) * Nat.choose (2 * (k + 1)) (k + 1) : ℕ) : ℚ) = ((2 * (2 * k + 1) * Nat.choose (2 * k) k : ℕ) : ℚ) := by
    rw [this]
  push_cast at h'
  rw [eq_div_iff (by positivity)]; linarith


lemma vdm (a b M : ℕ) : ∑ k ∈ Finset.range (M + 1), Nat.choose a k * Nat.choose b (M - k) = Nat.choose (a + b) M := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

lemma T_eq (n k : ℕ) : T n k = 2 * (Nat.choose (n + 2) (k + 1) : ℤ) + (Nat.choose n k : ℤ) - 4 := by
  have t00 : t 0 0 = 5 := by decide
  have h := Nat.choose_succ_succ' (n + 1) k
  unfold T
  rw [t00]
  unfold t
  have h' : ((Nat.choose (n + 2) (k + 1) : ℕ) : ℤ) = (Nat.choose (n + 1) k : ℤ) + (Nat.choose (n + 1) (k + 1) : ℤ) := by exact_mod_cast h
  linarith

lemma T_sym (n k : ℕ) (hk : k ≤ n) : T n (n - k) = T n k := by
  rw [T_eq, T_eq, show n - k + 1 = n + 2 - (k + 1) by omega, Nat.choose_symm (by omega), Nat.choose_symm hk]

lemma s_uu (n : ℕ) : ∑ k ∈ Finset.range (n + 1), (Nat.choose (n + 2) (k + 1) : ℚ) ^ 2 = (Nat.choose (2 * (n + 2)) (n + 2) : ℚ) - 2 := by
  have h := Nat.sum_range_choose_sq (n + 2)
  have h' : ∑ i ∈ Finset.range (n + 2 + 1), (Nat.choose (n + 2) i : ℚ) ^ 2 = (Nat.choose (2 * (n + 2)) (n + 2) : ℚ) := by exact_mod_cast h
  rw [Finset.sum_range_succ', Finset.sum_range_succ] at h'
  simp at h'
  linarith

lemma s_u (n : ℕ) : ∑ k ∈ Finset.range (n + 1), (Nat.choose (n + 2) (k + 1) : ℚ) = 2 ^ (n + 2) - 2 := by
  have h := Nat.sum_range_choose (n + 2)
  have h' : ∑ i ∈ Finset.range (n + 2 + 1), (Nat.choose (n + 2) i : ℚ) = 2 ^ (n + 2) := by exact_mod_cast h
  rw [Finset.sum_range_succ', Finset.sum_range_succ] at h'
  simp at h'
  linarith

lemma s_uv (n : ℕ) : ∑ k ∈ Finset.range (n + 1), (Nat.choose (n + 2) (k + 1) : ℚ) * (Nat.choose n k : ℚ) = (Nat.choose (2 * (n + 1)) (n + 1) : ℚ) := by
  have h := vdm (n + 2) n (n + 1)
  rw [show n + 2 + n = 2 * (n + 1) by ring] at h
  have h' : ∑ i ∈ Finset.range (n + 1 + 1), (Nat.choose (n + 2) i : ℚ) * (Nat.choose n (n + 1 - i) : ℚ) = (Nat.choose (2 * (n + 1)) (n + 1) : ℚ) := by exact_mod_cast h
  rw [Finset.sum_range_succ'] at h'
  have hz : (Nat.choose n (n + 1) : ℚ) = 0 := by simp
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero] at h'
  rw [hz, mul_zero, add_zero] at h'
  rw [← h']
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [show n + 1 - (k + 1) = n - k by omega, Nat.choose_symm (by omega)]

noncomputable def cbq (j : ℕ) : ℚ := (Nat.choose (2 * j) j : ℚ)

lemma cbq_succ (j : ℕ) : cbq (j + 1) = 2 * (2 * (j : ℚ) + 1) * cbq j / ((j : ℚ) + 1) := cb_succ j

lemma a_closed (n : ℕ) : (a n : ℚ) = 4 * cbq (n + 2) + 4 * cbq (n + 1) + cbq n - 72 * 2 ^ n + 16 * (n : ℚ) + 40 := by
  unfold cbq
  have h1 : (a n : ℚ) = ∑ k ∈ Finset.range (n + 1), ((T n k : ℤ) : ℚ) * ((T n k : ℤ) : ℚ) := by
    unfold a
    push_cast
    apply Finset.sum_congr rfl
    intro k hk
    rw [T_sym n k (by have := Finset.mem_range.mp hk; omega)]
  have h2 : ∀ k : ℕ, ((T n k : ℤ) : ℚ) * ((T n k : ℤ) : ℚ)
      = 4 * (Nat.choose (n + 2) (k + 1) : ℚ) ^ 2 + (Nat.choose n k : ℚ) ^ 2 + 16
        + 4 * ((Nat.choose (n + 2) (k + 1) : ℚ) * (Nat.choose n k : ℚ))
        - 16 * (Nat.choose (n + 2) (k + 1) : ℚ) - 8 * (Nat.choose n k : ℚ) := by
    intro k
    rw [T_eq]; push_cast; ring
  rw [h1]
  simp only [h2]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, s_uu, s_uv, s_u]
  have sv := Nat.sum_range_choose_sq n
  have sv' : ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℚ) ^ 2 = (Nat.choose (2 * n) n : ℚ) := by exact_mod_cast sv
  have sv2 := Nat.sum_range_choose n
  have sv2' : ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℚ) = 2 ^ n := by exact_mod_cast sv2
  rw [sv', sv2']
  simp
  ring

end OMA.S_oeis_a027182

theorem OMA.solution : type_of% @OMA.S_oeis_a027182.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega,
    show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega]
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [OMA.S_oeis_a027182.a_closed (m + 6), OMA.S_oeis_a027182.a_closed (m + 5), OMA.S_oeis_a027182.a_closed (m + 4), OMA.S_oeis_a027182.a_closed (m + 3),
    OMA.S_oeis_a027182.a_closed (m + 2), OMA.S_oeis_a027182.a_closed (m + 1)]
  simp only [OMA.S_oeis_a027182.cbq_succ]
  push_cast
  have h1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  have h2 : ((m : ℚ) + 2) ≠ 0 := by positivity
  have h3 : ((m : ℚ) + 3) ≠ 0 := by positivity
  have h4 : ((m : ℚ) + 4) ≠ 0 := by positivity
  have h5 : ((m : ℚ) + 5) ≠ 0 := by positivity
  have h6 : ((m : ℚ) + 6) ≠ 0 := by positivity
  have h7 : ((m : ℚ) + 7) ≠ 0 := by positivity
  have h8 : ((m : ℚ) + 8) ≠ 0 := by positivity
  field_simp
  ring
