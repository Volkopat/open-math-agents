import OMAStatements.S_oeis_a267457
import Mathlib

open OMA.S_oeis_a267457

private def live (t : ℕ) (i : ℤ) : Prop :=
    (t = 0 ∧ (i = 0)) ∨
    (t = 1 ∧ (i ≠ -1 ∧ i ≠ 1)) ∨
    (2 ≤ t ∧ t % 2 = 0 ∧ ((-(t : ℤ) ≤ i ∧ i ≤ t ∧ (((i + (t : ℤ)) % 2 = 0 ∧ ¬(i = -(t : ℤ) ∨ i = (t : ℤ))) ∨ (¬((i + (t : ℤ)) % 2 = 0) ∧ (i = -(t : ℤ) ∨ i = (t : ℤ))))) ∨ ((i < -(t : ℤ) ∨ (t : ℤ) < i)))) ∨
    (2 ≤ t ∧ t % 2 = 1 ∧ ((-(t : ℤ) ≤ i ∧ i ≤ t ∧ (((i + (t : ℤ)) % 2 = 1 ∧ ¬(i = -(t : ℤ) + 1 ∨ i = (t : ℤ) - 1)) ∨ (¬((i + (t : ℤ)) % 2 = 1) ∧ (i = -(t : ℤ) + 1 ∨ i = (t : ℤ) - 1)))) ∨ ((i < -(t : ℤ) ∨ (t : ℤ) < i))))

private lemma table (l c r : Bool) :
    eca 133 l c r = true ↔ (l = false ∧ r = false) ∨ (l = true ∧ c = true ∧ r = true) := by
  cases l <;> cases c <;> cases r <;> decide

set_option maxHeartbeats 4000000 in
private lemma state_iff (t : ℕ) (i : ℤ) : state t i = true ↔ live t i := by
  induction t generalizing i with
  | zero => simp [state, live]
  | succ t ih =>
    rw [state, table]
    simp only [Bool.eq_false_iff, ne_eq, ih]
    rcases Nat.lt_or_ge t 2 with h | h
    · simp only [live]
      interval_cases t <;> omega
    · simp only [live, eq_false (show ¬ t = 0 by omega), eq_false (show ¬ t = 1 by omega), eq_false (show ¬ t + 1 = 0 by omega), eq_false (show ¬ t + 1 = 1 by omega), eq_true (show 2 ≤ t by omega), eq_true (show 2 ≤ t + 1 by omega), false_and, false_or, or_false, true_and]
      omega

private lemma aval (t : ℕ) : (a t : ℤ) =
    ∑ k ∈ Finset.range (2 * t + 1), (if state t ((k : ℤ) - t) then (2 : ℤ) ^ (2 * t - k) else 0) := by
  unfold a; push_cast; rfl

private lemma geometricParity (b : ℤ) (t p : ℕ) (hp : p ≤ 1) :
    (b ^ 2 - 1) * ∑ k ∈ Finset.range (2*t+1),
      (if k % 2 = p then b ^ (2*t-k) else 0) =
    b ^ (2*t+2-p) - b ^ p := by
  induction t with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, Finset.sum_range_one]
    interval_cases p <;> norm_num
  | succ t ih =>
    have shift : (∑ k ∈ Finset.range (2*t+1), if k % 2 = p then b^(2*(t+1)-k) else 0) =
        b^2 * ∑ k ∈ Finset.range (2*t+1), if k % 2 = p then b^(2*t-k) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have ht := Finset.mem_range.mp hk
      rw [show 2*(t+1)-k = 2*t-k+2 by omega, pow_add]
      split_ifs <;> ring
    rw [show 2*(t+1)+1 = 2*t+1+1+1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, shift, show (2*t+1)%2=1 by omega,
      show (2*t+1+1)%2=0 by omega, show 2*(t+1)-(2*t+1)=1 by omega,
      show 2*(t+1)-(2*t+1+1)=0 by omega,
      show 2*(t+1)+2-p = (2*t+2-p)+2 by omega, pow_add]
    interval_cases p <;> norm_num at * <;> linear_combination b^2 * ih

private lemma geo2_0 (t : ℕ) : ((2 : ℤ) ^ 2 - 1) * ∑ k ∈ Finset.range (2 * t + 1),
    (if k % 2 = 0 then (2 : ℤ) ^ (2 * t - k) else 0) = (2 : ℤ) ^ (2 * t + 2) - 1 := by
  simpa using geometricParity 2 t 0 (by decide)

private lemma geo2_1 (t : ℕ) : ((2 : ℤ) ^ 2 - 1) * ∑ k ∈ Finset.range (2 * t + 1),
    (if k % 2 = 1 then (2 : ℤ) ^ (2 * t - k) else 0) = (2 : ℤ) ^ (2 * t + 1) - (2 : ℤ) := by
  simpa only [show 2*t+2-1=2*t+1 by omega, pow_one] using geometricParity 2 t 1 (by decide)

private lemma wsumg (n : ℕ) (f g : ℕ → ℤ) (E : Finset ℕ)
    (hE : E ⊆ Finset.range n) (h : ∀ k < n, k ∉ E → f k = g k) :
    ∑ k ∈ Finset.range n, f k = ∑ k ∈ Finset.range n, g k + ∑ k ∈ E, (f k - g k) := by
  rw [Finset.sum_subset hE (fun k hk hkE => by rw [h k (Finset.mem_range.mp hk) hkE]; ring),
    Finset.sum_sub_distrib]
  ring

private lemma row0 (t : ℕ) (ht : 2 ≤ t) (hp : t % 2 = 0) :
    ((3 : ℤ) * (2 : ℤ) ^ 1) * (a t : ℤ) = ((2 : ℤ) ^ (2 * t + 2 + 1) - (2 : ℤ) ^ 1) - (3 : ℤ) * (2 : ℤ) ^ (2 * t + 1) - (3 : ℤ) * (2 : ℤ) ^ 1 := by
  have key := wsumg (2 * t + 1) (fun k => if state t ((k : ℤ) - t) then (2 : ℤ) ^ (2 * t - k) else 0)
    (fun k => if k % 2 = 0 then (2 : ℤ) ^ (2 * t - k) else 0) ({0, 2 * t + 0} : Finset ℕ)
    (by intro k hk; simp at hk ⊢ <;> omega)
    (by
      intro k hk hkE
      have hs : state t ((k : ℤ) - t) = true ↔ k % 2 = 0 := by
        rw [state_iff]; unfold live; simp at hkE; push_cast <;> omega
      by_cases hk2 : k % 2 = 0
      · simp [hs.mpr hk2, hk2]
      · have hf : state t ((k : ℤ) - t) = false := by
          rw [Bool.eq_false_iff]; intro hh; exact hk2 (hs.mp hh)
        simp [hf, hk2])
  rw [Finset.sum_insert (by simp <;> omega), Finset.sum_singleton] at key
  have h0 : state t (((0 : ℕ) : ℤ) - t) = false := by
    rw [Bool.eq_false_iff]; intro hh; rw [state_iff] at hh; unfold live at hh; push_cast at hh <;> omega
  have p0 : (0) % 2 = 0 := by omega
  have h1 : state t (((2 * t + 0 : ℕ) : ℤ) - t) = false := by
    rw [Bool.eq_false_iff]; intro hh; rw [state_iff] at hh; unfold live at hh; push_cast at hh <;> omega
  have p1 : (2 * t + 0) % 2 = 0 := by omega
  simp only [h0, p0, h1, p1, if_true, if_false, Bool.false_eq_true, ↓reduceIte, Nat.reduceEqDiff] at key
  have q0 : (2 : ℤ) ^ 1 * (2 : ℤ) ^ (2 * t - (0)) = (2 : ℤ) ^ (2 * t + 1) := by
    rw [← pow_add]; congr 1; omega
  have q1 : (2 : ℤ) ^ 1 * (2 : ℤ) ^ (2 * t - (2 * t + 0)) = (2 : ℤ) ^ 1 := by
    rw [← pow_add]; congr 1; omega
  have g := geo2_0 t
  rw [aval]
  linear_combination ((3 : ℤ) * (2 : ℤ) ^ 1) * key + (2 : ℤ) ^ 1 * g + (-3 : ℤ) * q0 + (-3 : ℤ) * q1

private lemma row1 (t : ℕ) (ht : 2 ≤ t) (hp : t % 2 = 1) :
    ((3 : ℤ) * (2 : ℤ) ^ 1) * (a t : ℤ) = ((2 : ℤ) ^ (2 * t + 1 + 1) - (2 : ℤ) ^ (1 + 1)) - (3 : ℤ) * (2 : ℤ) ^ (2 * t) - (3 : ℤ) * (2 : ℤ) ^ 2 := by
  have key := wsumg (2 * t + 1) (fun k => if state t ((k : ℤ) - t) then (2 : ℤ) ^ (2 * t - k) else 0)
    (fun k => if k % 2 = 1 then (2 : ℤ) ^ (2 * t - k) else 0) ({1, 2 * t - 1} : Finset ℕ)
    (by intro k hk; simp at hk ⊢ <;> omega)
    (by
      intro k hk hkE
      have hs : state t ((k : ℤ) - t) = true ↔ k % 2 = 1 := by
        rw [state_iff]; unfold live; simp at hkE; push_cast <;> omega
      by_cases hk2 : k % 2 = 1
      · simp [hs.mpr hk2, hk2]
      · have hf : state t ((k : ℤ) - t) = false := by
          rw [Bool.eq_false_iff]; intro hh; exact hk2 (hs.mp hh)
        simp [hf, hk2])
  rw [Finset.sum_insert (by simp <;> omega), Finset.sum_singleton] at key
  have h0 : state t (((1 : ℕ) : ℤ) - t) = false := by
    rw [Bool.eq_false_iff]; intro hh; rw [state_iff] at hh; unfold live at hh; push_cast at hh <;> omega
  have p0 : (1) % 2 = 1 := by omega
  have h1 : state t (((2 * t - 1 : ℕ) : ℤ) - t) = false := by
    rw [Bool.eq_false_iff]; intro hh; rw [state_iff] at hh; unfold live at hh; push_cast at hh <;> omega
  have p1 : (2 * t - 1) % 2 = 1 := by omega
  simp only [h0, p0, h1, p1, if_true, if_false, Bool.false_eq_true, ↓reduceIte, Nat.reduceEqDiff] at key
  have q0 : (2 : ℤ) ^ 1 * (2 : ℤ) ^ (2 * t - (1)) = (2 : ℤ) ^ (2 * t) := by
    rw [← pow_add]; congr 1; omega
  have q1 : (2 : ℤ) ^ 1 * (2 : ℤ) ^ (2 * t - (2 * t - 1)) = (2 : ℤ) ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have g := geo2_1 t
  rw [aval]
  linear_combination ((3 : ℤ) * (2 : ℤ) ^ 1) * key + (2 : ℤ) ^ 1 * g + (-3 : ℤ) * q0 + (-3 : ℤ) * q1

private lemma ev (m : ℕ) : (-1 : ℤ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
private lemma od (m : ℕ) : (-1 : ℤ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num

private lemma cc (t : ℕ) (ht : 2 ≤ t) :
    2 * ((3 : ℤ) * (2 : ℤ) ^ 1) * (a t : ℤ) = (1 + (-1) ^ t) * (((2 : ℤ) ^ (2 * t + 2 + 1) - (2 : ℤ) ^ 1) - (3 : ℤ) * (2 : ℤ) ^ (2 * t + 1) - (3 : ℤ) * (2 : ℤ) ^ 1) + (1 - (-1) ^ t) * (((2 : ℤ) ^ (2 * t + 1 + 1) - (2 : ℤ) ^ (1 + 1)) - (3 : ℤ) * (2 : ℤ) ^ (2 * t) - (3 : ℤ) * (2 : ℤ) ^ 2) := by
  rcases Nat.even_or_odd' t with ⟨m, rfl | rfl⟩
  · have h := row0 (2 * m) ht (by omega); rw [ev]; linear_combination 2 * h
  · have h := row1 (2 * m + 1) ht (by omega); rw [od]; linear_combination 2 * h

private lemma v0 : a 0 = 1 := by decide

private lemma v1 : a 1 = 2 := by decide

set_option maxRecDepth 100000 in
private lemma v2 : a 2 = 4 := by
  have h := cc 2 (by norm_num)
  norm_num at h
  omega

set_option maxRecDepth 100000 in
private lemma v3 : a 3 = 8 := by
  have h := cc 3 (by norm_num)
  norm_num at h
  omega

set_option maxRecDepth 100000 in
private lemma v4 : a 4 = 84 := by
  have h := cc 4 (by norm_num)
  norm_num at h
  omega

set_option maxRecDepth 100000 in
private lemma v5 : a 5 = 168 := by
  have h := cc 5 (by norm_num)
  norm_num at h
  omega

private lemma recur (n : ℕ) (hn : 5 < n) : (a n : ℤ) = (17 : ℤ) * a (n - 2) + (-16 : ℤ) * a (n - 4) := by
  by_cases h : 5 < n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega]
    have h0 := cc (m + 6) (by omega)
    have h1 := cc (m + 5) (by omega)
    have h2 := cc (m + 4) (by omega)
    have h3 := cc (m + 3) (by omega)
    have h4 := cc (m + 2) (by omega)
    simp only [pow_add] at h0 h1 h2 h3 h4
    have : (2 * ((3 : ℤ) * (2 : ℤ) ^ 1)) * (a (m + 6) - ((17 : ℤ) * a (m + 4) + (-16 : ℤ) * a (m + 2))) = 0 := by
      linear_combination h0 - (17) * h2 - (-16) * h4
    have := (mul_eq_zero.mp this).resolve_left (by norm_num)
    linarith
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5]

open PowerSeries in
private lemma gf : mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X)) = ((1 + 2 * X) * (1 - 13 * X ^ 2 + 32 * X ^ 4) : PowerSeries ℤ) := by
  set F : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hF
  have product : F * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X)) = F + (-17 : ℤ) • (F * X ^ 2) + (16 : ℤ) • (F * X ^ 4) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have rhs : ((1 + 2 * X) * (1 - 13 * X ^ 2 + 32 * X ^ 4) : PowerSeries ℤ) = (1 : ℤ) • X ^ 0 + (2 : ℤ) • X ^ 1 + (-13 : ℤ) • X ^ 2 + (-26 : ℤ) • X ^ 3 + (32 : ℤ) • X ^ 4 + (64 : ℤ) • X ^ 5 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [product, rhs]
  ext n
  simp only [map_add, map_sub, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow, smul_eq_mul]
  by_cases h : 5 < n
  · have hr := recur n (by omega)
    simp only [show 2 ≤ n by omega, show 4 ≤ n by omega, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, if_true, if_false]
    linarith
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5]

theorem OMA.solution : type_of% @OMA.S_oeis_a267457.main := by
  exact ⟨fun n hn => by have := recur n hn; linarith, gf⟩
