import OMAStatements.S_oeis_a267035
import Mathlib

open OMA.S_oeis_a267035

private def live (t : ℕ) (i : ℤ) : Prop :=
    (t = 0 ∧ (i = 0)) ∨
    (1 ≤ t ∧ t % 2 = 0 ∧ (-(t : ℤ) ≤ i ∧ i ≤ t ∧ (i = -(t : ℤ)))) ∨
    (1 ≤ t ∧ t % 2 = 1 ∧ ((-(t : ℤ) ≤ i ∧ i ≤ t ∧ ¬(i = -(t : ℤ))) ∨ ((i < -(t : ℤ) ∨ (t : ℤ) < i))))

private lemma table (l c r : Bool) :
    eca 85 l c r = true ↔ r = false := by
  cases l <;> cases c <;> cases r <;> decide

set_option maxHeartbeats 4000000 in
private lemma state_iff (t : ℕ) (i : ℤ) : state t i = true ↔ live t i := by
  induction t generalizing i with
  | zero => simp [state, live]
  | succ t ih =>
    rw [state, table]
    simp only [Bool.eq_false_iff, ne_eq, ih]
    rcases Nat.lt_or_ge t 1 with h | h
    · simp only [live]
      interval_cases t <;> omega
    · simp only [live, eq_false (show ¬ t = 0 by omega), eq_false (show ¬ t + 1 = 0 by omega), eq_true (show 1 ≤ t by omega), eq_true (show 1 ≤ t + 1 by omega), false_and, false_or, or_false, true_and]
      omega

private lemma wsum (n : ℕ) (f : ℕ → ℤ) (c : ℤ) (w : ℕ → ℤ) (E : Finset ℕ)
    (hE : E ⊆ Finset.range n) (h : ∀ k < n, k ∉ E → f k = c * w k) :
    ∑ k ∈ Finset.range n, f k = c * ∑ k ∈ Finset.range n, w k + ∑ k ∈ E, (f k - c * w k) := by
  rw [Finset.sum_subset hE (fun k hk hkE => by rw [h k (Finset.mem_range.mp hk) hkE]; ring),
    Finset.sum_sub_distrib, Finset.mul_sum]
  ring

private lemma geo (t : ℕ) : ((10 : ℤ) - 1) * ∑ k ∈ Finset.range (2 * t + 1), (10 : ℤ) ^ (2 * t - k) =
    (10 : ℤ) ^ (2 * t + 1) - 1 := by
  have := Finset.sum_range_reflect (fun j => (10 : ℤ) ^ j) (2 * t + 1)
  simp only [show 2 * t + 1 - 1 = 2 * t by omega] at this
  rw [this, mul_comm, geom_sum_mul]

private lemma aval (t : ℕ) : (a t : ℤ) =
    ∑ k ∈ Finset.range (2 * t + 1), (if state t ((k : ℤ) - t) then (10 : ℤ) ^ (2 * t - k) else 0) := by
  unfold a; push_cast; rfl

private lemma row0 (t : ℕ) (ht : 1 ≤ t) (hp : t % 2 = 0) :
    ((9 : ℤ) * (10 : ℤ) ^ 0) * (a t : ℤ) = (9 : ℤ) * (10 : ℤ) ^ (2 * t) := by
  have key := wsum (2 * t + 1)
    (fun k => if state t ((k : ℤ) - t) then (10 : ℤ) ^ (2 * t - k) else 0) (0 : ℤ)
    (fun k => (10 : ℤ) ^ (2 * t - k)) ({0} : Finset ℕ)
    (by intro k hk; simp at hk ⊢; omega)
    (by
      intro k hk hkE
      have hs : state t ((k : ℤ) - t) = false := by
        rw [Bool.eq_false_iff]; intro hh; rw [state_iff] at hh; simp only [live] at hh; simp at hkE; push_cast at hh; omega
      simp [hs])

  rw [Finset.sum_singleton] at key
  have h0 : state t (((0 : ℕ) : ℤ) - t) = true := by
    rw [state_iff]; simp only [live]; push_cast; omega
  simp only [h0, if_true, if_false, Bool.false_eq_true, ↓reduceIte] at key
  have q0 : (10 : ℤ) ^ 0 * (10 : ℤ) ^ (2 * t - (0)) = (10 : ℤ) ^ (2 * t) := by
    rw [← pow_add]; congr 1; omega
  have g := geo t
  rw [aval]
  linear_combination (9 : ℤ) * (10 : ℤ) ^ 0 * key + (0 : ℤ) * (10 : ℤ) ^ 0 * g + (9 : ℤ) * q0

private lemma row1 (t : ℕ) (ht : 1 ≤ t) (hp : t % 2 = 1) :
    ((9 : ℤ) * (10 : ℤ) ^ 0) * (a t : ℤ) = ((10 : ℤ) ^ (2 * t + 1 + 0) - (10 : ℤ) ^ 0) - (9 : ℤ) * (10 : ℤ) ^ (2 * t) := by
  have key := wsum (2 * t + 1)
    (fun k => if state t ((k : ℤ) - t) then (10 : ℤ) ^ (2 * t - k) else 0) (1 : ℤ)
    (fun k => (10 : ℤ) ^ (2 * t - k)) ({0} : Finset ℕ)
    (by intro k hk; simp at hk ⊢; omega)
    (by
      intro k hk hkE
      have hs : state t ((k : ℤ) - t) = true := by
        rw [state_iff]; simp only [live]; simp at hkE; push_cast; omega
      simp [hs])

  rw [Finset.sum_singleton] at key
  have h0 : state t (((0 : ℕ) : ℤ) - t) = false := by
    rw [Bool.eq_false_iff]; intro hh; rw [state_iff] at hh; simp only [live] at hh; push_cast at hh; omega
  simp only [h0, if_true, if_false, Bool.false_eq_true, ↓reduceIte] at key
  have q0 : (10 : ℤ) ^ 0 * (10 : ℤ) ^ (2 * t - (0)) = (10 : ℤ) ^ (2 * t) := by
    rw [← pow_add]; congr 1; omega
  have g := geo t
  rw [aval]
  linear_combination (9 : ℤ) * (10 : ℤ) ^ 0 * key + (1 : ℤ) * (10 : ℤ) ^ 0 * g + (-9 : ℤ) * q0

private lemma ev (m : ℕ) : (-1 : ℤ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
private lemma od (m : ℕ) : (-1 : ℤ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num

private lemma cc (t : ℕ) (ht : 1 ≤ t) :
    2 * ((9 : ℤ) * (10 : ℤ) ^ 0) * (a t : ℤ) = (1 + (-1) ^ t) * ((9 : ℤ) * (10 : ℤ) ^ (2 * t)) + (1 - (-1) ^ t) * (((10 : ℤ) ^ (2 * t + 1 + 0) - (10 : ℤ) ^ 0) - (9 : ℤ) * (10 : ℤ) ^ (2 * t)) := by
  rcases Nat.even_or_odd' t with ⟨m, rfl | rfl⟩
  · have h := row0 (2 * m) ht (by omega); rw [ev]; linear_combination 2 * h
  · have h := row1 (2 * m + 1) ht (by omega); rw [od]; linear_combination 2 * h

private lemma v0 : a 0 = 1 := by decide

private lemma v1 : a 1 = 11 := by
  have h := cc 1 (by norm_num)
  norm_num at h
  omega

private lemma v2 : a 2 = 10000 := by
  have h := cc 2 (by norm_num)
  norm_num at h
  omega

private lemma v3 : a 3 = 111111 := by
  have h := cc 3 (by norm_num)
  norm_num at h
  omega

private lemma v4 : a 4 = 100000000 := by
  have h := cc 4 (by norm_num)
  norm_num at h
  omega

private lemma v5 : a 5 = 1111111111 := by
  have h := cc 5 (by norm_num)
  norm_num at h
  omega

private lemma v6 : a 6 = 1000000000000 := by
  have h := cc 6 (by norm_num)
  norm_num at h
  omega

private lemma v7 : a 7 = 11111111111111 := by
  have h := cc 7 (by norm_num)
  norm_num at h
  omega

private lemma v8 : a 8 = 10000000000000000 := by
  have h := cc 8 (by norm_num)
  norm_num at h
  omega

private lemma recur (n : ℕ) (hn : 3 < n) : (a n : ℤ) = (10001 : ℤ) * a (n - 2) + (-10000 : ℤ) * a (n - 4) := by
  by_cases h : 4 < n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
    have h0 := cc (m + 5) (by omega)
    have h1 := cc (m + 4) (by omega)
    have h2 := cc (m + 3) (by omega)
    have h3 := cc (m + 2) (by omega)
    have h4 := cc (m + 1) (by omega)
    simp only [pow_add] at h0 h1 h2 h3 h4
    have : (2 * ((9 : ℤ) * (10 : ℤ) ^ 0)) * (a (m + 5) - ((10001 : ℤ) * a (m + 3) + (-10000 : ℤ) * a (m + 1))) = 0 := by
      linear_combination h0 - (10001) * h2 - (-10000) * h4
    have := (mul_eq_zero.mp this).resolve_left (by norm_num)
    linarith
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8]

open PowerSeries in
private lemma gf : mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X)) = (1 + 11 * X - X ^ 2 + 1100 * X ^ 3 : PowerSeries ℤ) := by
  set F : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hF
  have product : F * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X)) = F + (-10001 : ℤ) • (F * X ^ 2) + (10000 : ℤ) • (F * X ^ 4) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have rhs : (1 + 11 * X - X ^ 2 + 1100 * X ^ 3 : PowerSeries ℤ) = (1 : ℤ) • X ^ 0 + (11 : ℤ) • X ^ 1 + (-1 : ℤ) • X ^ 2 + (1100 : ℤ) • X ^ 3 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [product, rhs]
  ext n
  simp only [map_add, map_sub, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow, smul_eq_mul]
  by_cases h : 4 < n
  · have hr := recur n (by omega)
    simp only [show 2 ≤ n by omega, show 4 ≤ n by omega, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, if_true, if_false]
    linarith
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8]

theorem OMA.solution : type_of% @OMA.S_oeis_a267035.main := by
  exact ⟨fun n hn => by have := recur n hn; linarith, gf⟩
