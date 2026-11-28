import OMAStatements.S_oeis_a267599
import Mathlib

open OMA.S_oeis_a267599

private def live (t : ℕ) (i : ℤ) : Prop :=
    (t = 0 ∧ (i = 0)) ∨
    (1 ≤ t ∧ t % 2 = 0 ∧ ((-(t : ℤ) ≤ i ∧ i ≤ t ∧ (((i + (t : ℤ)) % 2 = 1 ∧ ¬(i = (t : ℤ) - 1 ∨ i = (t : ℤ))) ∨ (¬((i + (t : ℤ)) % 2 = 1) ∧ (i = (t : ℤ) - 1 ∨ i = (t : ℤ))))) ∨ ((i < -(t : ℤ) ∨ (t : ℤ) < i)))) ∨
    (1 ≤ t ∧ t % 2 = 1 ∧ ((-(t : ℤ) ≤ i ∧ i ≤ t ∧ (((i + (t : ℤ)) % 2 = 1 ∧ ¬(i = (t : ℤ) - 1 ∨ i = (t : ℤ))) ∨ (¬((i + (t : ℤ)) % 2 = 1) ∧ (i = (t : ℤ) - 1 ∨ i = (t : ℤ))))) ∨ ((i < -(t : ℤ) ∨ (t : ℤ) < i))))

private lemma table (l c r : Bool) :
    eca 177 l c r = true ↔ (c = false ∧ r = false) ∨ (l = true ∧ r = true) := by
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

private lemma geo2_0 (t : ℕ) : ((10 : ℤ) ^ 2 - 1) * ∑ k ∈ Finset.range (2 * t + 1),
    (if k % 2 = 0 then (10 : ℤ) ^ (2 * t - k) else 0) = (10 : ℤ) ^ (2 * t + 2) - 1 := by
  simpa using geometricParity 10 t 0 (by decide)

private lemma geo2_1 (t : ℕ) : ((10 : ℤ) ^ 2 - 1) * ∑ k ∈ Finset.range (2 * t + 1),
    (if k % 2 = 1 then (10 : ℤ) ^ (2 * t - k) else 0) = (10 : ℤ) ^ (2 * t + 1) - (10 : ℤ) := by
  simpa only [show 2*t+2-1=2*t+1 by omega, pow_one] using geometricParity 10 t 1 (by decide)

private lemma wsumg (n : ℕ) (f g : ℕ → ℤ) (E : Finset ℕ)
    (hE : E ⊆ Finset.range n) (h : ∀ k < n, k ∉ E → f k = g k) :
    ∑ k ∈ Finset.range n, f k = ∑ k ∈ Finset.range n, g k + ∑ k ∈ E, (f k - g k) := by
  rw [Finset.sum_subset hE (fun k hk hkE => by rw [h k (Finset.mem_range.mp hk) hkE]; ring),
    Finset.sum_sub_distrib]
  ring

private lemma cc (t : ℕ) (ht : 1 ≤ t) :
    ((99 : ℤ) * (10 : ℤ) ^ 0) * (a t : ℤ) = ((10 : ℤ) ^ (2 * t + 1 + 0) - (10 : ℤ) ^ (1 + 0)) - (99 : ℤ) * (10 : ℤ) ^ 1 + (99 : ℤ) * (10 : ℤ) ^ 0 := by
  have key := wsumg (2 * t + 1) (fun k => if state t ((k : ℤ) - t) then (10 : ℤ) ^ (2 * t - k) else 0)
    (fun k => if k % 2 = 1 then (10 : ℤ) ^ (2 * t - k) else 0) ({2 * t - 1, 2 * t + 0} : Finset ℕ)
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
  have h0 : state t (((2 * t - 1 : ℕ) : ℤ) - t) = false := by
    rw [Bool.eq_false_iff]; intro hh; rw [state_iff] at hh; unfold live at hh; push_cast at hh <;> omega
  have p0 : (2 * t - 1) % 2 = 1 := by omega
  have h1 : state t (((2 * t + 0 : ℕ) : ℤ) - t) = true := by
    rw [state_iff]; unfold live; push_cast <;> omega
  have p1 : (2 * t + 0) % 2 = 0 := by omega
  simp only [h0, p0, h1, p1, if_true, if_false, Bool.false_eq_true, ↓reduceIte, Nat.reduceEqDiff] at key
  have q0 : (10 : ℤ) ^ 0 * (10 : ℤ) ^ (2 * t - (2 * t - 1)) = (10 : ℤ) ^ 1 := by
    rw [← pow_add]; congr 1; omega
  have q1 : (10 : ℤ) ^ 0 * (10 : ℤ) ^ (2 * t - (2 * t + 0)) = (10 : ℤ) ^ 0 := by
    rw [← pow_add]; congr 1; omega
  have g := geo2_1 t
  rw [aval]
  linear_combination ((99 : ℤ) * (10 : ℤ) ^ 0) * key + (10 : ℤ) ^ 0 * g + (-99 : ℤ) * q0 + (99 : ℤ) * q1

private lemma v0 : a 0 = 1 := by decide

set_option maxRecDepth 100000 in
private lemma v1 : a 1 = 1 := by
  have h := cc 1 (by norm_num)
  norm_num at h
  omega

set_option maxRecDepth 100000 in
private lemma v2 : a 2 = 1001 := by
  have h := cc 2 (by norm_num)
  norm_num at h
  omega

private lemma recur (n : ℕ) (hn : 2 < n) : (a n : ℤ) = (101 : ℤ) * a (n - 1) + (-100 : ℤ) * a (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
  have h0 := cc (m + 3) (by omega)
  have h1 := cc (m + 2) (by omega)
  have h2 := cc (m + 1) (by omega)
  simp only [pow_add] at h0 h1 h2
  apply mul_left_cancel₀ (a := (99 : ℤ)) (by decide)
  linear_combination h0 - 101 * h1 + 100 * h2

open PowerSeries in
private lemma gf : mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 100 * X)) = (1 - 100 * X + 1000 * X ^ 2 : PowerSeries ℤ) := by
  set F : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hF
  have product : F * ((1 - X) * (1 - 100 * X)) = F + (-101 : ℤ) • (F * X ^ 1) + (100 : ℤ) • (F * X ^ 2) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have rhs : (1 - 100 * X + 1000 * X ^ 2 : PowerSeries ℤ) = (1 : ℤ) • X ^ 0 + (-100 : ℤ) • X ^ 1 + (1000 : ℤ) • X ^ 2 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [product, rhs]
  ext n
  simp only [map_add, map_sub, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow, smul_eq_mul]
  by_cases h : 2 < n
  · have hr := recur n (by omega)
    split_ifs <;> first | omega | linarith
  · interval_cases n <;> simp [v0, v1, v2]

theorem OMA.solution : type_of% @OMA.S_oeis_a267599.main := by
  exact ⟨fun n hn => by have := recur n hn; linarith, gf⟩
