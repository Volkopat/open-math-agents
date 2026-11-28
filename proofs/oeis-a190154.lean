import OMAStatements.S_oeis_a190154

namespace OMA.P190154

open OMA.S_oeis_a190154 Finset

/-- Even-index sums along a line of the Pascal triangle, with an explicit cutoff. -/
def Em (M N : ℕ) : ℤ := ∑ k ∈ range M, (Nat.choose (N - 4 * k) (2 * k) : ℤ)

/-- Odd-index sums along a line of the Pascal triangle, with an explicit cutoff. -/
def Om (M N : ℕ) : ℤ := ∑ k ∈ range M, (Nat.choose (N - 4 * k - 2) (2 * k + 1) : ℤ)

lemma Em_ext (N M : ℕ) (h : N < 6 * M) : ∀ d : ℕ, Em (M + d) N = Em M N := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    have hs : Em (M + d + 1) N = Em (M + d) N
        + (Nat.choose (N - 4 * (M + d)) (2 * (M + d)) : ℤ) := sum_range_succ _ _
    have z : Nat.choose (N - 4 * (M + d)) (2 * (M + d)) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    show Em (M + d + 1) N = Em M N
    rw [hs, z, ih]
    simp

lemma Om_ext (N M : ℕ) (h : N < 6 * M) : ∀ d : ℕ, Om (M + d) N = Om M N := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    have hs : Om (M + d + 1) N = Om (M + d) N
        + (Nat.choose (N - 4 * (M + d) - 2) (2 * (M + d) + 1) : ℤ) := sum_range_succ _ _
    have z : Nat.choose (N - 4 * (M + d) - 2) (2 * (M + d) + 1) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    show Om (M + d + 1) N = Om M N
    rw [hs, z, ih]
    simp

lemma Em_step (M N : ℕ) : Em (M + 1) (N + 3) = Em (M + 1) (N + 2) + Om M N := by
  have h1 : Em (M + 1) (N + 3) = ∑ k ∈ range M,
      (Nat.choose (N + 3 - 4 * (k + 1)) (2 * (k + 1)) : ℤ)
      + (Nat.choose (N + 3 - 4 * 0) (2 * 0) : ℤ) := sum_range_succ' _ _
  have h2 : Em (M + 1) (N + 2) = ∑ k ∈ range M,
      (Nat.choose (N + 2 - 4 * (k + 1)) (2 * (k + 1)) : ℤ)
      + (Nat.choose (N + 2 - 4 * 0) (2 * 0) : ℤ) := sum_range_succ' _ _
  have hc : ∑ k ∈ range M, (Nat.choose (N + 3 - 4 * (k + 1)) (2 * (k + 1)) : ℤ)
      = ∑ k ∈ range M, ((Nat.choose (N + 2 - 4 * (k + 1)) (2 * (k + 1)) : ℤ)
        + (Nat.choose (N - 4 * k - 2) (2 * k + 1) : ℤ)) := by
    refine sum_congr rfl (fun k _ => ?_)
    by_cases hk : 4 * k + 2 ≤ N
    · have e1 : N + 3 - 4 * (k + 1) = (N - 4 * k - 2) + 1 := by omega
      have e2 : N + 2 - 4 * (k + 1) = N - 4 * k - 2 := by omega
      have e3 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      rw [e1, e2, e3, Nat.choose_succ_succ]
      push_cast
      ring
    · have e1 : N + 3 - 4 * (k + 1) = 0 := by omega
      have e2 : N + 2 - 4 * (k + 1) = 0 := by omega
      have e3 : N - 4 * k - 2 = 0 := by omega
      have e4 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      rw [e1, e2, e3, e4]
      simp
  rw [h1, h2, hc, sum_add_distrib]
  unfold Om
  simp
  ring

lemma Om_step (M N : ℕ) : Om M (N + 3) = Om M (N + 2) + Em M N := by
  unfold Om Em
  rw [← sum_add_distrib]
  refine sum_congr rfl (fun k _ => ?_)
  by_cases hk : 4 * k ≤ N
  · have e1 : N + 3 - 4 * k - 2 = (N - 4 * k) + 1 := by omega
    have e2 : N + 2 - 4 * k - 2 = N - 4 * k := by omega
    rw [e1, e2, Nat.choose_succ_succ]
    push_cast
    ring
  · have e1 : N + 3 - 4 * k - 2 = 0 := by omega
    have e2 : N + 2 - 4 * k - 2 = 0 := by omega
    have e3 : N - 4 * k = 0 := by omega
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have e4 : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
    rw [e1, e2, e3, e4]
    simp

/-- The full even sum. -/
def E (N : ℕ) : ℤ := Em (N + 1) N

/-- The full odd sum. -/
def O (N : ℕ) : ℤ := Om (N + 1) N

lemma E_rec (N : ℕ) : E (N + 3) = E (N + 2) + O N := by
  have h := Em_step (N + 3) N
  have h1 : Em (N + 3 + 1) (N + 2) = Em (N + 2 + 1) (N + 2) :=
    Em_ext (N + 2) (N + 2 + 1) (by omega) 1
  have h2 : Om (N + 3) N = Om (N + 1) N := Om_ext N (N + 1) (by omega) 2
  unfold E O
  rw [h, h1, h2]

lemma O_rec (N : ℕ) : O (N + 3) = O (N + 2) + E N := by
  have h := Om_step (N + 3 + 1) N
  have h1 : Om (N + 3 + 1) (N + 2) = Om (N + 2 + 1) (N + 2) :=
    Om_ext (N + 2) (N + 2 + 1) (by omega) 1
  have h2 : Em (N + 3 + 1) N = Em (N + 1) N := Em_ext N (N + 1) (by omega) 3
  unfold E O
  rw [h, h1, h2]

lemma a_eq (n : ℕ) : a n = E (3 * n) := by
  have h1 : a n = Em (n / 2 + 1) (3 * n) := by
    unfold a Em T
    refine sum_congr rfl (fun k hk => ?_)
    have hk2 := mem_range.mp hk
    have e1 : 3 * (n - k) - k = 3 * n - 4 * k := by omega
    have e2 : 3 * (n - k) - 3 * k = 3 * n - 4 * k - 2 * k := by omega
    rw [e1, e2, Nat.choose_symm (by omega)]
  have h2 : Em (n / 2 + 1 + (3 * n - n / 2)) (3 * n) = Em (n / 2 + 1) (3 * n) :=
    Em_ext (3 * n) (n / 2 + 1) (by omega) _
  have e : n / 2 + 1 + (3 * n - n / 2) = 3 * n + 1 := by omega
  rw [e] at h2
  rw [h1, ← h2]
  rfl

lemma E_tri (N : ℕ) : E (N + 18) = 2 * E (N + 15) + 2 * E (N + 12) + 6 * E (N + 9)
    - 3 * E (N + 6) + E N := by
  have p0 := E_rec N
  have p1 := E_rec (N + 1)
  have p2 := E_rec (N + 2)
  have p3 := E_rec (N + 3)
  have p4 := E_rec (N + 4)
  have p5 := E_rec (N + 5)
  have p6 := E_rec (N + 6)
  have p7 := E_rec (N + 7)
  have p8 := E_rec (N + 8)
  have p9 := E_rec (N + 9)
  have p10 := E_rec (N + 10)
  have p11 := E_rec (N + 11)
  have p12 := E_rec (N + 12)
  have p13 := E_rec (N + 13)
  have p14 := E_rec (N + 14)
  have p15 := E_rec (N + 15)
  have q0 := O_rec N
  have q1 := O_rec (N + 1)
  have q2 := O_rec (N + 2)
  have q3 := O_rec (N + 3)
  have q4 := O_rec (N + 4)
  have q5 := O_rec (N + 5)
  have q6 := O_rec (N + 6)
  have q7 := O_rec (N + 7)
  have q8 := O_rec (N + 8)
  have q9 := O_rec (N + 9)
  have q10 := O_rec (N + 10)
  have q11 := O_rec (N + 11)
  have q12 := O_rec (N + 12)
  linarith

lemma arec (n : ℕ) : a (n + 6) = 2 * a (n + 5) + 2 * a (n + 4) + 6 * a (n + 3)
    - 3 * a (n + 2) + a n := by
  simp only [a_eq]
  have h := E_tri (3 * n)
  have e6 : 3 * (n + 6) = 3 * n + 18 := by ring
  have e5 : 3 * (n + 5) = 3 * n + 15 := by ring
  have e4 : 3 * (n + 4) = 3 * n + 12 := by ring
  have e3 : 3 * (n + 3) = 3 * n + 9 := by ring
  have e2 : 3 * (n + 2) = 3 * n + 6 := by ring
  rw [e6, e5, e4, e3, e2]
  exact h

lemma a0 : a 0 = 1 := by decide
lemma a1 : a 1 = 1 := by decide
lemma a2 : a 2 = 2 := by decide
lemma a3 : a 3 = 11 := by decide
lemma a4 : a 4 = 30 := by decide
lemma a5 : a 5 = 91 := by decide

end OMA.P190154

open OMA.S_oeis_a190154 OMA.P190154 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a190154.main := by
  have hD : ∀ f : ℤ⟦X⟧, f * ((X ^ 3 - 3 * X ^ 2 + 4 * X - 1) * (X ^ 3 + 3 * X ^ 2 + 2 * X + 1))
      = f * X ^ 6 - (f * X ^ 4 + f * X ^ 4 + f * X ^ 4)
        + (f * X ^ 3 + f * X ^ 3 + f * X ^ 3 + f * X ^ 3 + f * X ^ 3 + f * X ^ 3)
        + (f * X ^ 2 + f * X ^ 2) + (f * X + f * X) - f := by
    intro f; ring
  have hN : (-1 + X + X ^ 3 - X ^ 4 + 2 * X ^ 2 : ℤ⟦X⟧)
      = -1 + X + X ^ 3 - X ^ 4 + (X ^ 2 + X ^ 2) := by ring
  rw [hD, hN]
  ext n
  have hx : ∀ f : ℤ⟦X⟧,
      PowerSeries.coeff n (f * X) = if 1 ≤ n then PowerSeries.coeff (n - 1) f else 0 := by
    intro f
    have := PowerSeries.coeff_mul_X_pow' (p := f) (n := 1) (d := n)
    simpa using this
  simp only [map_sub, map_add, map_neg, PowerSeries.coeff_mul_X_pow', hx, PowerSeries.coeff_mk,
    PowerSeries.coeff_X, PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
  rcases n with _ | _ | _ | _ | _ | _ | k
  · simp [a0]
  · simp [a0, a1]
  · simp [a0, a1, a2]
  · simp [a0, a1, a2, a3]
  · simp [a0, a1, a2, a3, a4]
  · simp [a1, a2, a3, a4, a5]
  · have h := arec k
    have e6 : k + 1 + 1 + 1 + 1 + 1 + 1 = k + 6 := rfl
    simp only [e6]
    have c6 : 6 ≤ k + 6 := by omega
    have c4 : 4 ≤ k + 6 := by omega
    have c3 : 3 ≤ k + 6 := by omega
    have c2 : 2 ≤ k + 6 := by omega
    have c1 : 1 ≤ k + 6 := by omega
    have n0 : ¬ (k + 6 = 0) := by omega
    have n1 : ¬ (k + 6 = 1) := by omega
    have n2 : ¬ (k + 6 = 2) := by omega
    have n3 : ¬ (k + 6 = 3) := by omega
    have n4 : ¬ (k + 6 = 4) := by omega
    have s6 : k + 6 - 6 = k := by omega
    have s4 : k + 6 - 4 = k + 2 := by omega
    have s3 : k + 6 - 3 = k + 3 := by omega
    have s2 : k + 6 - 2 = k + 4 := by omega
    have s1 : k + 6 - 1 = k + 5 := by omega
    simp only [c6, c4, c3, c2, c1, n0, n1, n2, n3, n4, s6, s4, s3, s2, s1, if_true, if_false]
    linarith
