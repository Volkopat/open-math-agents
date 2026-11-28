import OMAStatements.S_oeis_a096164

namespace OMA.P096164

open OMA.S_oeis_a096164

/-- Ballot differences: d(N,0) = 1 and d(N,j+1) = C(N,j+1) - C(N,j). -/
def d : ℕ → ℕ → ℚ
  | _, 0 => 1
  | N, j + 1 => (N.choose (j + 1) : ℚ) - (N.choose j : ℚ)

lemma d_pascal (N j : ℕ) : d (N + 1) (j + 1) = d N (j + 1) + d N j := by
  cases j with
  | zero =>
    simp only [d, zero_add, Nat.choose_one_right, Nat.choose_zero_right]
    push_cast
    ring
  | succ i =>
    simp only [d, Nat.choose_succ_succ' N]
    push_cast
    ring

lemma c_zero_of (n k : ℕ) (h : n < k ∨ (n - k) % 2 = 1) : c n k = 0 := by
  unfold c
  rw [if_pos h]

lemma c_big (n k : ℕ) (h : n < k) : c n k = 0 := c_zero_of n k (Or.inl h)

/-- The nonzero entries of the Catalan triangle are ballot differences. -/
lemma c_even (k j : ℕ) : c (k + 2 * j) k = d (k + 2 * j) j := by
  have hne : ¬ (k + 2 * j < k ∨ (k + 2 * j - k) % 2 = 1) := by omega
  have hj : (k + 2 * j - k) / 2 = j := by omega
  unfold c
  rw [if_neg hne, hj]
  cases j with
  | zero =>
    simp only [d, Nat.choose_zero_right]
    have h0 : ((k : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  | succ i =>
    simp only [d]
    have h1 := Nat.add_one_mul_choose_eq (k + 2 * (i + 1)) i
    have h2 := Nat.choose_succ_right_eq (k + 2 * (i + 1)) i
    have hsub : k + 2 * (i + 1) - i = k + i + 2 := by omega
    rw [hsub] at h2
    have h1' : (((k + 2 * (i + 1) : ℕ) : ℚ) + 1) * ((k + 2 * (i + 1)).choose i : ℚ)
        = ((k + 2 * (i + 1) + 1).choose (i + 1) : ℚ) * ((i : ℚ) + 1) := by
      exact_mod_cast h1
    have h2' : ((k + 2 * (i + 1)).choose (i + 1) : ℚ) * ((i : ℚ) + 1)
        = ((k + 2 * (i + 1)).choose i : ℚ) * ((k : ℚ) + i + 2) := by
      exact_mod_cast h2
    have hi : ((i : ℚ) + 1) ≠ 0 := by positivity
    have hN : (((k + 2 * (i + 1) : ℕ) : ℚ) + 1) ≠ 0 := by positivity
    have hM : (((k + 2 * (i + 1) : ℕ) : ℚ)) = (k : ℚ) + 2 * ((i : ℚ) + 1) := by
      push_cast
      ring
    rw [div_eq_iff hN]
    apply mul_right_cancel₀ hi
    rw [hM] at h1' ⊢
    linear_combination (-((k : ℚ) + 1)) * h1' - ((k : ℚ) + 2 * ((i : ℚ) + 1) + 1) * h2'

lemma c_succ (n k : ℕ) : c (n + 1) (k + 1) = c n k + c n (k + 1 + 1) := by
  by_cases h : n < k ∨ (n - k) % 2 = 1
  · rw [c_zero_of _ _ h, c_zero_of (n + 1) (k + 1) (by omega),
      c_zero_of n (k + 1 + 1) (by omega)]
    ring
  · obtain ⟨j, rfl⟩ : ∃ j, n = k + 2 * j := ⟨(n - k) / 2, by omega⟩
    have e1 : k + 2 * j + 1 = (k + 1) + 2 * j := by ring
    rw [e1, c_even (k + 1) j, c_even k j]
    cases j with
    | zero =>
      rw [c_zero_of _ _ (by omega)]
      simp [d]
    | succ i =>
      have e2 : k + 2 * (i + 1) = (k + 1 + 1) + 2 * i := by ring
      have e3 : k + 1 + 2 * (i + 1) = (k + 1 + 1 + 2 * i) + 1 := by ring
      rw [e3, d_pascal, e2, c_even (k + 1 + 1) i]

lemma c_zero (n : ℕ) : c (n + 1) 0 = c n 1 := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [c_zero_of _ _ (by omega), c_zero_of _ _ (by omega)]
  · have e1 : 2 * m + 1 + 1 = 0 + 2 * (m + 1) := by ring
    have e2 : 2 * m + 1 = 1 + 2 * m := by ring
    rw [e1, c_even 0 (m + 1), e2, c_even 1 m]
    have e3 : 0 + 2 * (m + 1) = (1 + 2 * m) + 1 := by ring
    rw [e3, d_pascal]
    have hz : d (1 + 2 * m) (m + 1) = 0 := by
      simp only [d]
      have e4 : 1 + 2 * m = 2 * m + 1 := by ring
      rw [e4, Nat.choose_symm_half]
      ring
    rw [hz, zero_add]

lemma p_sum (n k : ℕ) (hk : k ≤ n) : ∑ m ∈ Finset.range (n + 1), p k m = 3 ^ k := by
  have h : ∑ m ∈ Finset.range (k + 1), p k m = ∑ m ∈ Finset.range (n + 1), p k m := by
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    · intro x _ hx
      simp only [Finset.mem_range] at hx
      unfold p
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
  rw [← h]
  have e : (3 : ℚ) = 1 + 2 := by norm_num
  rw [e, add_pow]
  apply Finset.sum_congr rfl
  intro m _
  unfold p
  rw [one_pow, one_mul, mul_comm]

/-- The row sums as the values at 3 of the row polynomials of the Catalan triangle. -/
def P (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), c n k * 3 ^ k

def U (n : ℕ) : ℚ := ∑ k ∈ Finset.range n, c n (k + 1) * 3 ^ k

lemma row_sum (n : ℕ) : ∑ m ∈ Finset.range (n + 1), T n m = P n := by
  unfold T P
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by
    have := Finset.mem_range.mp hk
    omega
  rw [← Finset.mul_sum, p_sum n k hk']

lemma P_eq (n : ℕ) : P n = 3 * U n + c n 0 := by
  unfold P U
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_succ]
  ring

lemma P_succ (n : ℕ) : P (n + 1) = 3 * P n + U n := by
  have hU : U n = ∑ k ∈ Finset.range (n + 1), c n (k + 1 + 1) * (3 : ℚ) ^ (k + 1) + c n 1 := by
    have e1 := Finset.sum_range_succ' (fun k => c n (k + 1) * (3 : ℚ) ^ k) (n + 1)
    have e2 := Finset.sum_range_succ (fun k => c n (k + 1) * (3 : ℚ) ^ k) (n + 1)
    have e3 := Finset.sum_range_succ (fun k => c n (k + 1) * (3 : ℚ) ^ k) n
    rw [c_big n (n + 1 + 1) (by omega)] at e2
    rw [c_big n (n + 1) (by omega)] at e3
    simp only [zero_mul, add_zero, pow_zero, mul_one, zero_add] at e1 e2 e3
    unfold U
    linarith
  have hA : ∑ k ∈ Finset.range (n + 1), (c n k + c n (k + 1 + 1)) * (3 : ℚ) ^ (k + 1)
      = 3 * ∑ k ∈ Finset.range (n + 1), c n k * (3 : ℚ) ^ k
        + ∑ k ∈ Finset.range (n + 1), c n (k + 1 + 1) * (3 : ℚ) ^ (k + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ]
    ring
  unfold P
  rw [Finset.sum_range_succ' _ (n + 1)]
  simp only [c_succ, c_zero, pow_zero, mul_one]
  rw [hA, hU]
  ring

lemma s_cast (n : ℕ) :
    (s n : ℚ) = ∑ k ∈ Finset.range (n + 1), (n.choose (k / 2) : ℚ) * (3 : ℚ) ^ (n - k) := by
  unfold s
  push_cast
  rfl

def W (n : ℕ) : ℚ := ∑ i ∈ Finset.range n, (n.choose (i / 2) : ℚ) * (3 : ℚ) ^ (n - 1 - i)

def V (n : ℕ) : ℚ := ∑ i ∈ Finset.range n, (n.choose (i / 2 + 1) : ℚ) * (3 : ℚ) ^ (n - 1 - i)

lemma sW (n : ℕ) : (s n : ℚ) = 3 * W n + (n.choose (n / 2) : ℚ) := by
  rw [s_cast, Finset.sum_range_succ]
  unfold W
  rw [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have e : n - i = (n - 1 - i) + 1 := by omega
    rw [e, pow_succ]
    ring
  · simp

lemma sV (n : ℕ) :
    3 * (s n : ℚ) + (n.choose ((n + 1) / 2) : ℚ) = V n + (3 : ℚ) ^ n + (3 : ℚ) ^ (n + 1) := by
  have e1 := Finset.sum_range_succ
    (fun i => (n.choose (i / 2) : ℚ) * (3 : ℚ) ^ (n + 1 - i)) (n + 1)
  have e2 := Finset.sum_range_succ'
    (fun i => (n.choose (i / 2) : ℚ) * (3 : ℚ) ^ (n + 1 - i)) (n + 1)
  have e3 := Finset.sum_range_succ'
    (fun i => (n.choose ((i + 1) / 2) : ℚ) * (3 : ℚ) ^ (n + 1 - (i + 1))) n
  have h1 : ∑ i ∈ Finset.range (n + 1), (n.choose (i / 2) : ℚ) * (3 : ℚ) ^ (n + 1 - i)
      = 3 * (s n : ℚ) := by
    rw [s_cast, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have e : n + 1 - i = (n - i) + 1 := by omega
    rw [e, pow_succ]
    ring
  have h2 : ∑ i ∈ Finset.range n,
      (n.choose ((i + 1 + 1) / 2) : ℚ) * (3 : ℚ) ^ (n + 1 - (i + 1 + 1)) = V n := by
    unfold V
    apply Finset.sum_congr rfl
    intro i hi
    have a : (i + 1 + 1) / 2 = i / 2 + 1 := by omega
    have b : n + 1 - (i + 1 + 1) = n - 1 - i := by omega
    rw [a, b]
  have f1 : (n.choose ((n + 1) / 2) : ℚ) * (3 : ℚ) ^ (n + 1 - (n + 1))
      = (n.choose ((n + 1) / 2) : ℚ) := by simp
  have f2 : (n.choose (0 / 2) : ℚ) * (3 : ℚ) ^ (n + 1 - 0) = (3 : ℚ) ^ (n + 1) := by simp
  have f3 : (n.choose ((0 + 1) / 2) : ℚ) * (3 : ℚ) ^ (n + 1 - (0 + 1)) = (3 : ℚ) ^ n := by simp
  rw [f1] at e1
  rw [f2] at e2
  rw [f3] at e3
  rw [h1] at e1
  rw [h2] at e3
  linarith

lemma s_succ (n : ℕ) : (s (n + 1) : ℚ) = W n + V n + (3 : ℚ) ^ n + (3 : ℚ) ^ (n + 1) := by
  have e2 := Finset.sum_range_succ'
    (fun i => ((n + 1).choose (i / 2) : ℚ) * (3 : ℚ) ^ (n + 1 - i)) (n + 1)
  have e3 := Finset.sum_range_succ'
    (fun i => ((n + 1).choose ((i + 1) / 2) : ℚ) * (3 : ℚ) ^ (n + 1 - (i + 1))) n
  have h2 : ∑ i ∈ Finset.range n,
      ((n + 1).choose ((i + 1 + 1) / 2) : ℚ) * (3 : ℚ) ^ (n + 1 - (i + 1 + 1)) = W n + V n := by
    unfold W V
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have a : (i + 1 + 1) / 2 = i / 2 + 1 := by omega
    have b : n + 1 - (i + 1 + 1) = n - 1 - i := by omega
    rw [a, b, Nat.choose_succ_succ']
    push_cast
    ring
  have f2 : ((n + 1).choose (0 / 2) : ℚ) * (3 : ℚ) ^ (n + 1 - 0) = (3 : ℚ) ^ (n + 1) := by simp
  have f3 : ((n + 1).choose ((0 + 1) / 2) : ℚ) * (3 : ℚ) ^ (n + 1 - (0 + 1)) = (3 : ℚ) ^ n := by
    simp
  rw [f2] at e2
  rw [f3] at e3
  rw [h2] at e3
  rw [s_cast (n + 1)]
  linarith

lemma s_rec (n : ℕ) : 3 * (s (n + 1) : ℚ)
    = 10 * (s n : ℚ) + 3 * (n.choose ((n + 1) / 2) : ℚ) - (n.choose (n / 2) : ℚ) := by
  have h1 := sW n
  have h2 := sV n
  have h3 := s_succ n
  linarith

lemma key (n : ℕ) : 3 * A126931 (n + 1) = 10 * A126931 n - c n 0 := by
  unfold A126931
  have r1 := s_rec (n + 1)
  have r0 := s_rec n
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have a1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have a2 : (2 * m + 1) / 2 = m := by omega
    have a3 : (2 * m) / 2 = m := by omega
    rw [a1, a2] at r1
    rw [a2, a3] at r0
    have hs : ((2 * m + 1).choose (m + 1) : ℚ) = ((2 * m + 1).choose m : ℚ) := by
      rw [Nat.choose_symm_half]
    have e0 : 2 * m = 0 + 2 * m := by ring
    have hc : c (2 * m) 0 = d (0 + 2 * m) m := by
      rw [← c_even 0 m, ← e0]
    cases m with
    | zero =>
      simp only [d] at hc
      rw [hc]
      norm_num at r1 r0 ⊢
      linarith
    | succ i =>
      simp only [d] at hc
      rw [← e0] at hc
      have hp : ((2 * (i + 1) + 1).choose (i + 1) : ℚ)
          = ((2 * (i + 1)).choose i : ℚ) + ((2 * (i + 1)).choose (i + 1) : ℚ) := by
        rw [Nat.choose_succ_succ']
        push_cast
        ring
      rw [hc]
      linarith
  · have a1 : (2 * m + 1 + 1 + 1) / 2 = m + 1 := by omega
    have a2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have a3 : (2 * m + 1) / 2 = m := by omega
    rw [a1, a2] at r1
    rw [a2, a3] at r0
    have hs : ((2 * m + 1).choose (m + 1) : ℚ) = ((2 * m + 1).choose m : ℚ) := by
      rw [Nat.choose_symm_half]
    have hp : ((2 * m + 1 + 1).choose (m + 1) : ℚ)
        = ((2 * m + 1).choose m : ℚ) + ((2 * m + 1).choose (m + 1) : ℚ) := by
      rw [Nat.choose_succ_succ']
      push_cast
      ring
    have hc : c (2 * m + 1) 0 = 0 := c_zero_of _ _ (by omega)
    rw [hc]
    linarith

lemma P_eq_A (n : ℕ) : P n = A126931 n := by
  induction n with
  | zero =>
    simp [P, A126931, s, c, Finset.sum_range_succ]
    norm_num
  | succ n ih =>
    have h1 := P_succ n
    have h2 := P_eq n
    have h3 := key n
    linarith

end OMA.P096164

open OMA.S_oeis_a096164 OMA.P096164 in
theorem OMA.solution : type_of% @OMA.S_oeis_a096164.main := by
  intro n
  rw [row_sum, P_eq_A]
