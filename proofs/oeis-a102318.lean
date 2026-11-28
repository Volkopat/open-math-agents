import OMAStatements.S_oeis_a102318
import Mathlib

-- Problem: A102318, two recurrences for the mean binomial transform of the Catalan numbers.
-- Credit: @Uynet
--
-- For e with e^2 = 1 put T n = sum_k e^(n-k) * C(n,k) * Cat k. A telescoping sum with
-- G k = k (k+1) C(n+2,k) e^k Cat k gives the second-order recurrence
--   (n+3) T(n+2) = ((2n+4) e + 4n+6) T(n+1) - (1+4e) (n+1) T(n).
-- Both operators of the statement vanish on every solution of this recurrence for e = 1 and
-- for e = -1 (a rational-function identity), hence on the mean of the two transforms.

namespace OMA.A102318Proof

open OMA.S_oeis_a102318 Finset

theorem cat_step (k : ℕ) :
    ((k : ℚ) + 2) * (catalan (k + 1) : ℚ) = (4 * (k : ℚ) + 2) * (catalan k : ℚ) := by
  have h1 := succ_mul_catalan_eq_centralBinom (k + 1)
  have h2 := succ_mul_catalan_eq_centralBinom k
  have h3 := Nat.succ_mul_centralBinom_succ k
  have e1 : ((k : ℚ) + 1 + 1) * (catalan (k + 1) : ℚ) = (Nat.centralBinom (k + 1) : ℚ) := by
    exact_mod_cast h1
  have e2 : ((k : ℚ) + 1) * (catalan k : ℚ) = (Nat.centralBinom k : ℚ) := by
    exact_mod_cast h2
  have e3 : ((k : ℚ) + 1) * (Nat.centralBinom (k + 1) : ℚ) =
      2 * (2 * (k : ℚ) + 1) * (Nat.centralBinom k : ℚ) := by
    exact_mod_cast h3
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hk
  linear_combination ((k : ℚ) + 1) * e1 + e3 - 2 * (2 * (k : ℚ) + 1) * e2

theorem choose_step (N k : ℕ) :
    ((k : ℚ) + 1) * (N.choose (k + 1) : ℚ) = ((N : ℚ) - k) * (N.choose k : ℚ) := by
  rcases le_or_gt k N with h | h
  · have h1 := Nat.choose_succ_right_eq N k
    have h2 : ((N.choose (k + 1) * (k + 1) : ℕ) : ℚ) = ((N.choose k * (N - k) : ℕ) : ℚ) := by
      rw [h1]
    push_cast [Nat.cast_sub h] at h2
    linarith
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (Nat.lt_succ_of_lt h)]
    simp

theorem choose_up (n m k : ℕ) (hm : m = n + 1) :
    (n.choose k : ℚ) * (m : ℚ) = (m.choose k : ℚ) * ((m : ℚ) - k) := by
  subst hm
  rcases le_or_gt k (n + 1) with h | h
  · have h1 := Nat.choose_mul_succ_eq n k
    have h2 : ((n.choose k * (n + 1) : ℕ) : ℚ) = (((n + 1).choose k * (n + 1 - k) : ℕ) : ℚ) := by
      rw [h1]
    push_cast [Nat.cast_sub h] at h2 ⊢
    linarith
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (Nat.lt_of_succ_lt h)]
    simp

/-- The sum with a free upper bound. -/
def W (e : ℚ) (n N : ℕ) : ℚ := ∑ k ∈ range N, e ^ k * (n.choose k : ℚ) * (catalan k : ℚ)

theorem W_ext (e : ℚ) (n N : ℕ) (h : n + 1 ≤ N) : W e n N = W e n (n + 1) := by
  unfold W
  symm
  apply sum_subset (range_mono h)
  intro k _ hk
  have hk2 : n < k := by
    rw [mem_range] at hk; omega
  rw [Nat.choose_eq_zero_of_lt hk2]
  simp

theorem transform_eq (e : ℚ) (he : e ^ 2 = 1) (n : ℕ) :
    transform e n = e ^ n * W e n (n + 1) := by
  unfold transform W
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have hk2 : k ≤ n := by
    rw [mem_range] at hk; omega
  have h1 : e ^ (n - k) * e ^ k = e ^ n := by rw [← pow_add, Nat.sub_add_cancel hk2]
  have h2 : e ^ k * e ^ k = 1 := by rw [← pow_add, ← two_mul, pow_mul, he, one_pow]
  have h3 : e ^ n * e ^ k = e ^ (n - k) := by
    rw [← h1, mul_assoc, h2, mul_one]
  rw [← h3]; ring

/-- The telescoping identity, termwise. -/
theorem term (e : ℚ) (n k : ℕ) :
    ((n : ℚ) + 2) * (-(1 + 4 * e) * ((n : ℚ) + 1) * (n.choose k : ℚ)
        + ((2 * (n : ℚ) + 4) + e * (4 * (n : ℚ) + 6)) * ((n + 1).choose k : ℚ)
        - ((n : ℚ) + 3) * ((n + 2).choose k : ℚ)) * (e ^ k * (catalan k : ℚ))
      = ((k : ℚ) + 1) * ((k : ℚ) + 2) * ((n + 2).choose (k + 1) : ℚ)
          * (e ^ (k + 1) * (catalan (k + 1) : ℚ))
        - (k : ℚ) * ((k : ℚ) + 1) * ((n + 2).choose k : ℚ) * (e ^ k * (catalan k : ℚ)) := by
  have r1 : (n.choose k : ℚ) * ((n : ℚ) + 1) = ((n + 1).choose k : ℚ) * ((n : ℚ) + 1 - k) := by
    have h := choose_up n (n + 1) k rfl
    push_cast at h
    linarith
  have r2 : ((n + 1).choose k : ℚ) * ((n : ℚ) + 2)
      = ((n + 2).choose k : ℚ) * ((n : ℚ) + 2 - k) := by
    have h := choose_up (n + 1) (n + 2) k rfl
    push_cast at h
    linarith
  have r3 : ((k : ℚ) + 1) * ((n + 2).choose (k + 1) : ℚ)
      = ((n : ℚ) + 2 - k) * ((n + 2).choose k : ℚ) := by
    have h := choose_step (n + 2) k
    push_cast at h
    linarith
  have r4 := cat_step k
  rw [pow_succ]
  linear_combination
    (-(1 + 4 * e) * ((n : ℚ) + 2) * (e ^ k * (catalan k : ℚ))) * r1
    + ((-(1 + 4 * e) * ((n : ℚ) + 1 - k) + ((2 * (n : ℚ) + 4) + e * (4 * (n : ℚ) + 6)))
        * (e ^ k * (catalan k : ℚ))) * r2
    - (e ^ k * e * ((k : ℚ) + 2) * (catalan (k + 1) : ℚ)) * r3
    - (e ^ k * e * ((n : ℚ) + 2 - k) * ((n + 2).choose k : ℚ)) * r4

theorem W_rec (e : ℚ) (n : ℕ) :
    -(1 + 4 * e) * ((n : ℚ) + 1) * W e n (n + 3)
      + ((2 * (n : ℚ) + 4) + e * (4 * (n : ℚ) + 6)) * W e (n + 1) (n + 3)
      - ((n : ℚ) + 3) * W e (n + 2) (n + 3) = 0 := by
  have hn : ((n : ℚ) + 2) ≠ 0 := by positivity
  apply mul_left_cancel₀ hn
  rw [mul_zero]
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℚ, G = fun j : ℕ =>
      (j : ℚ) * ((j : ℚ) + 1) * ((n + 2).choose j : ℚ) * (e ^ j * (catalan j : ℚ)) := ⟨_, rfl⟩
  have hsum : ((n : ℚ) + 2) * (-(1 + 4 * e) * ((n : ℚ) + 1) * W e n (n + 3)
      + ((2 * (n : ℚ) + 4) + e * (4 * (n : ℚ) + 6)) * W e (n + 1) (n + 3)
      - ((n : ℚ) + 3) * W e (n + 2) (n + 3))
      = ∑ k ∈ range (n + 3), (G (k + 1) - G k) := by
    unfold W
    simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    have h := term e n k
    rw [hG]
    push_cast
    linear_combination h
  rw [hsum, sum_range_sub, hG]
  simp only []
  rw [Nat.choose_eq_zero_of_lt (by omega : n + 2 < n + 3)]
  simp

theorem T_rec (e : ℚ) (he : e ^ 2 = 1) (n : ℕ) :
    ((n : ℚ) + 3) * transform e (n + 2)
      = ((2 * (n : ℚ) + 4) * e + (4 * (n : ℚ) + 6)) * transform e (n + 1)
        - (1 + 4 * e) * ((n : ℚ) + 1) * transform e n := by
  have t0 := transform_eq e he n
  have t1 : transform e (n + 1) = e ^ (n + 1) * W e (n + 1) (n + 2) := transform_eq e he (n + 1)
  have t2 : transform e (n + 2) = e ^ (n + 2) * W e (n + 2) (n + 3) := transform_eq e he (n + 2)
  have w0 := W_ext e n (n + 3) (by omega)
  have w1 : W e (n + 1) (n + 3) = W e (n + 1) (n + 2) := W_ext e (n + 1) (n + 3) (by omega)
  have h := W_rec e n
  rw [w0, w1] at h
  have p1 : e ^ (n + 1) = e ^ n * e := pow_succ e n
  have p2 : e ^ (n + 2) = e ^ n := by
    rw [pow_add, he, mul_one]
  rw [t0, t1, t2, p1, p2]
  have he2 : e * e = 1 := by rw [← sq]; exact he
  linear_combination (-(e ^ n)) * h
    - (e ^ n * (2 * (n : ℚ) + 4) * W e (n + 1) (n + 2)) * he2

theorem P_rec (n : ℕ) :
    ((n : ℚ) + 3) * transform 1 (n + 2)
      = (6 * (n : ℚ) + 10) * transform 1 (n + 1) + (-5 * ((n : ℚ) + 1)) * transform 1 n := by
  have h := T_rec 1 (by norm_num) n
  linear_combination h

theorem R_rec (n : ℕ) :
    ((n : ℚ) + 3) * transform (-1) (n + 2)
      = (2 * (n : ℚ) + 2) * transform (-1) (n + 1) + (3 * ((n : ℚ) + 1)) * transform (-1) n := by
  have h := T_rec (-1) (by norm_num) n
  linear_combination h

/-- Solving a second-order recurrence for the next four terms. -/
theorem solve (a : ℕ → ℚ) (p q : ℚ → ℚ)
    (h : ∀ n : ℕ, ((n : ℚ) + 3) * a (n + 2) = p n * a (n + 1) + q n * a n) (m : ℕ) :
    a (m + 2) = (p m * a (m + 1) + q m * a m) / ((m : ℚ) + 3) ∧
    a (m + 3) = (p ((m : ℚ) + 1) * a (m + 2) + q ((m : ℚ) + 1) * a (m + 1)) / ((m : ℚ) + 4) ∧
    a (m + 4) = (p ((m : ℚ) + 2) * a (m + 3) + q ((m : ℚ) + 2) * a (m + 2)) / ((m : ℚ) + 5) ∧
    a (m + 5) = (p ((m : ℚ) + 3) * a (m + 4) + q ((m : ℚ) + 3) * a (m + 3)) / ((m : ℚ) + 6) := by
  have h0 := h m
  have h1 : (((m + 1 : ℕ) : ℚ) + 3) * a (m + 3)
      = p ((m + 1 : ℕ) : ℚ) * a (m + 2) + q ((m + 1 : ℕ) : ℚ) * a (m + 1) := h (m + 1)
  have h2 : (((m + 2 : ℕ) : ℚ) + 3) * a (m + 4)
      = p ((m + 2 : ℕ) : ℚ) * a (m + 3) + q ((m + 2 : ℕ) : ℚ) * a (m + 2) := h (m + 2)
  have h3 : (((m + 3 : ℕ) : ℚ) + 3) * a (m + 5)
      = p ((m + 3 : ℕ) : ℚ) * a (m + 4) + q ((m + 3 : ℕ) : ℚ) * a (m + 3) := h (m + 3)
  push_cast at h1 h2 h3
  have d3 : ((m : ℚ) + 3) ≠ 0 := by positivity
  have d4 : ((m : ℚ) + 4) ≠ 0 := by positivity
  have d5 : ((m : ℚ) + 5) ≠ 0 := by positivity
  have d6 : ((m : ℚ) + 6) ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eq_div_iff d3]; linarith
  · rw [eq_div_iff d4]; linarith
  · rw [eq_div_iff d5]; linarith
  · rw [eq_div_iff d6]; linarith

theorem five_P (a : ℕ → ℚ)
    (h : ∀ n : ℕ, ((n : ℚ) + 3) * a (n + 2)
      = (6 * (n : ℚ) + 10) * a (n + 1) + (-5 * ((n : ℚ) + 1)) * a n)
    (m : ℕ) : orderFive a m = 0 := by
  obtain ⟨e2, e3, e4, e5⟩ := solve a (fun x => 6 * x + 10) (fun x => -5 * (x + 1)) h m
  have d3 : ((m : ℚ) + 3) ≠ 0 := by positivity
  have d4 : ((m : ℚ) + 4) ≠ 0 := by positivity
  have d5 : ((m : ℚ) + 5) ≠ 0 := by positivity
  have d6 : ((m : ℚ) + 6) ≠ 0 := by positivity
  simp only [orderFive]
  rw [e5, e4, e3, e2]
  field_simp
  ring

theorem four_P (a : ℕ → ℚ)
    (h : ∀ n : ℕ, ((n : ℚ) + 3) * a (n + 2)
      = (6 * (n : ℚ) + 10) * a (n + 1) + (-5 * ((n : ℚ) + 1)) * a n)
    (m : ℕ) : orderFour a m = 0 := by
  obtain ⟨e2, e3, e4, _⟩ := solve a (fun x => 6 * x + 10) (fun x => -5 * (x + 1)) h m
  have d3 : ((m : ℚ) + 3) ≠ 0 := by positivity
  have d4 : ((m : ℚ) + 4) ≠ 0 := by positivity
  have d5 : ((m : ℚ) + 5) ≠ 0 := by positivity
  simp only [orderFour]
  rw [e4, e3, e2]
  field_simp
  ring

theorem five_R (a : ℕ → ℚ)
    (h : ∀ n : ℕ, ((n : ℚ) + 3) * a (n + 2)
      = (2 * (n : ℚ) + 2) * a (n + 1) + (3 * ((n : ℚ) + 1)) * a n)
    (m : ℕ) : orderFive a m = 0 := by
  obtain ⟨e2, e3, e4, e5⟩ := solve a (fun x => 2 * x + 2) (fun x => 3 * (x + 1)) h m
  have d3 : ((m : ℚ) + 3) ≠ 0 := by positivity
  have d4 : ((m : ℚ) + 4) ≠ 0 := by positivity
  have d5 : ((m : ℚ) + 5) ≠ 0 := by positivity
  have d6 : ((m : ℚ) + 6) ≠ 0 := by positivity
  simp only [orderFive]
  rw [e5, e4, e3, e2]
  field_simp
  ring

theorem four_R (a : ℕ → ℚ)
    (h : ∀ n : ℕ, ((n : ℚ) + 3) * a (n + 2)
      = (2 * (n : ℚ) + 2) * a (n + 1) + (3 * ((n : ℚ) + 1)) * a n)
    (m : ℕ) : orderFour a m = 0 := by
  obtain ⟨e2, e3, e4, _⟩ := solve a (fun x => 2 * x + 2) (fun x => 3 * (x + 1)) h m
  have d3 : ((m : ℚ) + 3) ≠ 0 := by positivity
  have d4 : ((m : ℚ) + 4) ≠ 0 := by positivity
  have d5 : ((m : ℚ) + 5) ≠ 0 := by positivity
  simp only [orderFour]
  rw [e4, e3, e2]
  field_simp
  ring

theorem five_lin (m : ℕ) :
    orderFive sequence m = (orderFive (transform 1) m + orderFive (transform (-1)) m) / 2 := by
  simp only [orderFive, OMA.S_oeis_a102318.sequence]; ring

theorem four_lin (m : ℕ) :
    orderFour sequence m = (orderFour (transform 1) m + orderFour (transform (-1)) m) / 2 := by
  simp only [orderFour, OMA.S_oeis_a102318.sequence]; ring

end OMA.A102318Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a102318.main := by
  intro m
  constructor
  · rw [OMA.A102318Proof.five_lin, OMA.A102318Proof.five_P _ OMA.A102318Proof.P_rec,
      OMA.A102318Proof.five_R _ OMA.A102318Proof.R_rec]
    norm_num
  · rw [OMA.A102318Proof.four_lin, OMA.A102318Proof.four_P _ OMA.A102318Proof.P_rec,
      OMA.A102318Proof.four_R _ OMA.A102318Proof.R_rec]
    norm_num
