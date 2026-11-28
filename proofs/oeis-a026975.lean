import OMAStatements.S_oeis_a026975

namespace OMA.P026975

open OMA.S_oeis_a026975 Finset

lemma T_zero (n : ℕ) : T n 0 = 1 := by
  cases n with
  | zero => rfl
  | succ m => cases m <;> rfl

lemma T_gt : ∀ n k : ℕ, n < k → T n k = 0
  | 0, 0, h => by omega
  | 0, k + 1, _ => by rw [T]
  | 1, 0, h => by omega
  | 1, k + 1, h => by
    rw [T]
    rw [if_neg (by omega)]
  | n + 2, 0, h => by omega
  | n + 2, k + 1, h => by
    rw [T]
    rw [if_neg (by omega), if_neg (by omega)]

lemma T_diag : ∀ n : ℕ, T n n = 1
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    rw [T]
    rw [if_pos rfl]

lemma T_rec (n k : ℕ) : T (n + 2) (k + 1)
    = T (n + 1) k + T (n + 1) (k + 1) + (if n % 2 = 0 ∧ k % 2 = 0 then T n k else 0) := by
  conv_lhs => rw [T]
  by_cases h1 : k + 1 = n + 2
  · have hk : k = n + 1 := by omega
    subst hk
    rw [if_pos h1, T_diag (n + 1), T_gt (n + 1) (n + 1 + 1) (by omega), if_neg (by omega)]
    norm_num
  · by_cases h2 : k + 1 < n + 2
    · rw [if_neg h1, if_pos h2]
      by_cases hc : (n + 2) % 2 = 0 ∧ (k + 1) % 2 = 1
      · rw [if_pos hc, if_pos (by omega)]
        ring
      · rw [if_neg hc, if_neg (by omega)]
        ring
    · rw [if_neg h1, if_neg h2, T_gt (n + 1) k (by omega), T_gt (n + 1) (k + 1) (by omega),
        T_gt n k (by omega)]
      simp

/-- Weighted row sums. -/
def W (n : ℕ) (g : ℕ → ℤ) : ℤ := ∑ k ∈ range (n + 1), g k * T n k

/-- Weighted row sums over the even columns. -/
def Fe (n : ℕ) (h : ℕ → ℤ) : ℤ := ∑ k ∈ range (n + 1), (if k % 2 = 0 then h k * T n k else 0)

lemma W_congr (n : ℕ) (g g2 : ℕ → ℤ) (h : ∀ k, g k = g2 k) : W n g = W n g2 := by
  unfold W
  exact sum_congr rfl (fun k _ => by rw [h k])

lemma W_add (n : ℕ) (g h : ℕ → ℤ) : W n (fun k => g k + h k) = W n g + W n h := by
  unfold W
  rw [← sum_add_distrib]
  exact sum_congr rfl (fun k _ => by ring)

lemma W_neg (n : ℕ) (g : ℕ → ℤ) : W n (fun k => - g k) = - W n g := by
  unfold W
  rw [← sum_neg_distrib]
  exact sum_congr rfl (fun k _ => by ring)

lemma W_succ2 (n : ℕ) (g : ℕ → ℤ) :
    W (n + 2) g = W (n + 1) g + W (n + 1) (fun k => g (k + 1))
      + (if n % 2 = 0 then Fe n (fun k => g (k + 1)) else 0) := by
  have h1 : W (n + 2) g = ∑ k ∈ range (n + 2), g (k + 1) * T (n + 2) (k + 1)
      + g 0 * T (n + 2) 0 := sum_range_succ' _ _
  have h2 : ∑ k ∈ range (n + 2), g (k + 1) * T (n + 2) (k + 1)
      = ∑ k ∈ range (n + 2), g (k + 1) * T (n + 1) k
        + ∑ k ∈ range (n + 2), g (k + 1) * T (n + 1) (k + 1)
        + ∑ k ∈ range (n + 2), g (k + 1) * (if n % 2 = 0 ∧ k % 2 = 0 then T n k else 0) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl (fun k _ => ?_)
    rw [T_rec]
    ring
  have h3 : W (n + 1) g = ∑ k ∈ range (n + 1), g (k + 1) * T (n + 1) (k + 1)
      + g 0 * T (n + 1) 0 := sum_range_succ' _ _
  have h4 : ∑ k ∈ range (n + 2), g (k + 1) * T (n + 1) (k + 1)
      = ∑ k ∈ range (n + 1), g (k + 1) * T (n + 1) (k + 1)
        + g (n + 1 + 1) * T (n + 1) (n + 1 + 1) := sum_range_succ _ _
  have h5 : W (n + 1) (fun k => g (k + 1)) = ∑ k ∈ range (n + 2), g (k + 1) * T (n + 1) k := rfl
  have h6 : ∑ k ∈ range (n + 2), g (k + 1) * (if n % 2 = 0 ∧ k % 2 = 0 then T n k else 0)
      = ∑ k ∈ range (n + 1), g (k + 1) * (if n % 2 = 0 ∧ k % 2 = 0 then T n k else 0)
        + g (n + 1 + 1) * (if n % 2 = 0 ∧ (n + 1) % 2 = 0 then T n (n + 1) else 0) :=
    sum_range_succ _ _
  have h7 : ∑ k ∈ range (n + 1), g (k + 1) * (if n % 2 = 0 ∧ k % 2 = 0 then T n k else 0)
      = (if n % 2 = 0 then Fe n (fun k => g (k + 1)) else 0) := by
    by_cases hn : n % 2 = 0
    · rw [if_pos hn]
      unfold Fe
      refine sum_congr rfl (fun k _ => ?_)
      by_cases hk : k % 2 = 0
      · rw [if_pos ⟨hn, hk⟩, if_pos hk]
      · rw [if_neg (fun h => hk h.2), if_neg hk, mul_zero]
    · rw [if_neg hn]
      refine sum_eq_zero (fun k _ => ?_)
      rw [if_neg (fun h => hn h.1), mul_zero]
  have z1 : T (n + 1) (n + 1 + 1) = 0 := T_gt _ _ (by omega)
  have z2 : (if n % 2 = 0 ∧ (n + 1) % 2 = 0 then T n (n + 1) else 0) = 0 := by
    rw [if_neg (by omega)]
  rw [h1, h2, h4, h6, h7, z1, z2, T_zero, h3, T_zero, h5]
  ring

/-- The sign (-1)^k. -/
def s (k : ℕ) : ℤ := (-1) ^ k

lemma s_succ (k : ℕ) : s (k + 1) = - s k := by
  unfold s
  rw [pow_succ]
  ring

lemma s_sq (k : ℕ) : s k * s k = 1 := by
  unfold s
  rw [← mul_pow]
  norm_num

lemma Fe_two (n : ℕ) (h : ℕ → ℤ) : 2 * Fe n h = W n h + W n (fun k => s k * h k) := by
  unfold Fe W
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl (fun k _ => ?_)
  by_cases hk : k % 2 = 0
  · have hs : s k = 1 := Even.neg_one_pow (Nat.even_iff.mpr hk)
    rw [if_pos hk]
    show 2 * (h k * T n k) = h k * T n k + s k * h k * T n k
    rw [hs]
    ring
  · have hs : s k = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))
    rw [if_neg hk]
    show 2 * 0 = h k * T n k + s k * h k * T n k
    rw [hs]
    ring

/-- Row sums. -/
def u (n : ℕ) : ℤ := W n (fun _ => 1)

/-- Row sums weighted by the column index. -/
def d (n : ℕ) : ℤ := W n (fun k => (k : ℤ))

/-- Alternating row sums. -/
def v (n : ℕ) : ℤ := W n s

/-- Alternating row sums weighted by the column index. -/
def e (n : ℕ) : ℤ := W n (fun k => s k * (k : ℤ))

lemma a_eq (n : ℕ) : a n = u n + d n := by
  unfold a u d W
  rw [← sum_add_distrib]
  exact sum_congr rfl (fun k _ => by ring)

lemma sh_d (n : ℕ) : W n (fun k => ((k + 1 : ℕ) : ℤ)) = d n + u n := by
  unfold d u
  rw [← W_add]
  exact W_congr _ _ _ (fun k => by push_cast; ring)

lemma sh_v (n : ℕ) : W n (fun k => s (k + 1)) = - v n := by
  unfold v
  rw [← W_neg]
  exact W_congr _ _ _ (fun k => s_succ k)

lemma sh_e (n : ℕ) : W n (fun k => s (k + 1) * ((k + 1 : ℕ) : ℤ)) = -(e n + v n) := by
  unfold e v
  rw [← W_add, ← W_neg]
  exact W_congr _ _ _ (fun k => by rw [s_succ]; push_cast; ring)

lemma al_u (n : ℕ) : W n (fun k => s k * 1) = v n := by
  unfold v
  exact W_congr _ _ _ (fun k => by ring)

lemma al_d (n : ℕ) : W n (fun k => s k * ((k + 1 : ℕ) : ℤ)) = e n + v n := by
  unfold e v
  rw [← W_add]
  exact W_congr _ _ _ (fun k => by push_cast; ring)

lemma al_v (n : ℕ) : W n (fun k => s k * s (k + 1)) = - u n := by
  unfold u
  rw [← W_neg]
  exact W_congr _ _ _ (fun k => by
    rw [s_succ]
    have h := s_sq k
    linear_combination (-1 : ℤ) * h)

lemma al_e (n : ℕ) :
    W n (fun k => s k * (s (k + 1) * ((k + 1 : ℕ) : ℤ))) = -(d n + u n) := by
  rw [← sh_d, ← W_neg]
  exact W_congr _ _ _ (fun k => by
    rw [s_succ]
    have h := s_sq k
    linear_combination (-((k + 1 : ℕ) : ℤ)) * h)

lemma step_odd (n : ℕ) (hn : ¬ n % 2 = 0) :
    u (n + 2) = 2 * u (n + 1) ∧ d (n + 2) = 2 * d (n + 1) + u (n + 1)
    ∧ v (n + 2) = v (n + 1) - v (n + 1) ∧ e (n + 2) = - v (n + 1) := by
  have hu := W_succ2 n (fun _ => (1 : ℤ))
  have hd := W_succ2 n (fun k => (k : ℤ))
  have hv := W_succ2 n s
  have he := W_succ2 n (fun k => s k * (k : ℤ))
  rw [if_neg hn] at hu hd hv he
  beta_reduce at hu hd hv he
  rw [sh_d] at hd
  rw [sh_v] at hv
  rw [sh_e] at he
  have cu1 : W (n + 1) (fun _ => (1 : ℤ)) = u (n + 1) := rfl
  have cu2 : W (n + 2) (fun _ => (1 : ℤ)) = u (n + 2) := rfl
  have cd1 : W (n + 1) (fun k => (k : ℤ)) = d (n + 1) := rfl
  have cd2 : W (n + 2) (fun k => (k : ℤ)) = d (n + 2) := rfl
  have cv1 : W (n + 1) s = v (n + 1) := rfl
  have cv2 : W (n + 2) s = v (n + 2) := rfl
  have ce1 : W (n + 1) (fun k => s k * (k : ℤ)) = e (n + 1) := rfl
  have ce2 : W (n + 2) (fun k => s k * (k : ℤ)) = e (n + 2) := rfl
  rw [cu2, cu1] at hu
  rw [cd2, cd1] at hd
  rw [cv2, cv1] at hv
  rw [ce2, ce1] at he
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith

lemma step_even (n : ℕ) (hn : n % 2 = 0) :
    2 * u (n + 2) = 4 * u (n + 1) + u n + v n
    ∧ 2 * d (n + 2) = 4 * d (n + 1) + 2 * u (n + 1) + d n + u n + e n + v n
    ∧ 2 * v (n + 2) = -(v n + u n)
    ∧ 2 * e (n + 2) = - 2 * v (n + 1) - (e n + v n + d n + u n) := by
  have hu := W_succ2 n (fun _ => (1 : ℤ))
  have hd := W_succ2 n (fun k => (k : ℤ))
  have hv := W_succ2 n s
  have he := W_succ2 n (fun k => s k * (k : ℤ))
  rw [if_pos hn] at hu hd hv he
  beta_reduce at hu hd hv he
  rw [sh_d] at hd
  rw [sh_v] at hv
  rw [sh_e] at he
  have fu := Fe_two n (fun _ => (1 : ℤ))
  have fd := Fe_two n (fun k => ((k + 1 : ℕ) : ℤ))
  have fv := Fe_two n (fun k => s (k + 1))
  have fe := Fe_two n (fun k => s (k + 1) * ((k + 1 : ℕ) : ℤ))
  beta_reduce at fu fd fv fe
  rw [al_u] at fu
  rw [sh_d, al_d] at fd
  rw [sh_v, al_v] at fv
  rw [sh_e, al_e] at fe
  have cu : W n (fun _ => (1 : ℤ)) = u n := rfl
  have cu1 : W (n + 1) (fun _ => (1 : ℤ)) = u (n + 1) := rfl
  have cu2 : W (n + 2) (fun _ => (1 : ℤ)) = u (n + 2) := rfl
  have cd1 : W (n + 1) (fun k => (k : ℤ)) = d (n + 1) := rfl
  have cd2 : W (n + 2) (fun k => (k : ℤ)) = d (n + 2) := rfl
  have cv1 : W (n + 1) s = v (n + 1) := rfl
  have cv2 : W (n + 2) s = v (n + 2) := rfl
  have ce1 : W (n + 1) (fun k => s k * (k : ℤ)) = e (n + 1) := rfl
  have ce2 : W (n + 2) (fun k => s k * (k : ℤ)) = e (n + 2) := rfl
  rw [cu] at fu
  rw [cu2, cu1] at hu
  rw [cd2, cd1] at hd
  rw [cv2, cv1] at hv
  rw [ce2, ce1] at he
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith

/-- The recurrence at an even base: indices b+10 and b+11. -/
lemma core (b : ℕ) (hb : b % 2 = 0) :
    a (b + 10) = 8 * a (b + 8) - 12 * a (b + 6) - 16 * a (b + 4) - 4 * a (b + 2)
    ∧ a (b + 11) = 8 * a (b + 9) - 12 * a (b + 7) - 16 * a (b + 5) - 4 * a (b + 3) := by
  obtain ⟨p0, q0, r0, t0⟩ := step_even b hb
  obtain ⟨p1, q1, r1, t1⟩ := step_odd (b + 1) (by omega)
  obtain ⟨p2, q2, r2, t2⟩ := step_even (b + 2) (by omega)
  obtain ⟨p3, q3, r3, t3⟩ := step_odd (b + 3) (by omega)
  obtain ⟨p4, q4, r4, t4⟩ := step_even (b + 4) (by omega)
  obtain ⟨p5, q5, r5, t5⟩ := step_odd (b + 5) (by omega)
  obtain ⟨p6, q6, r6, t6⟩ := step_even (b + 6) (by omega)
  obtain ⟨p7, q7, r7, t7⟩ := step_odd (b + 7) (by omega)
  obtain ⟨p8, q8, r8, t8⟩ := step_even (b + 8) (by omega)
  obtain ⟨p9, q9, r9, t9⟩ := step_odd (b + 9) (by omega)
  simp only [a_eq]
  constructor
  · linarith
  · linarith

lemma a8 : a 8 = 8 * a 6 - 12 * a 4 - 16 * a 2 - 4 * a 0 := by decide
lemma a9 : a 9 = 8 * a 7 - 12 * a 5 - 16 * a 3 - 4 * a 1 := by decide

end OMA.P026975

open OMA.S_oeis_a026975 OMA.P026975 in
theorem OMA.solution : type_of% @OMA.S_oeis_a026975.main := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 8 := ⟨n - 8, by omega⟩
  have e2 : j + 8 - 2 = j + 6 := by omega
  have e4 : j + 8 - 4 = j + 4 := by omega
  have e6 : j + 8 - 6 = j + 2 := by omega
  have e8 : j + 8 - 8 = j := by omega
  rw [e2, e4, e6, e8]
  rcases j with _ | _ | i
  · exact a8
  · exact a9
  · rcases Nat.even_or_odd i with ⟨m, hm⟩ | ⟨m, hm⟩
    · have h := (core i (by omega)).1
      exact h
    · obtain ⟨c, rfl⟩ : ∃ c, i = c + 1 := ⟨i - 1, by omega⟩
      have h := (core c (by omega)).2
      exact h
