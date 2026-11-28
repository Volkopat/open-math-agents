import OMAStatements.S_oeis_a392664

-- Problem: A392664: Triangle read by rows: T(n,k) (1 <= k <= n) given by T(n,1) = T(n,n) = 1, otherwise T(n,k) = (m*n-m*k+1)*T(n-1,k-1) + (m*k-m+1)*T(n-1,k), where m = -3.
-- Upstream: formal-conjectures statements/oeis-a392664.lean:0 (declaration OMA.S_oeis_a392664.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: both coefficients 1-3(n-k) and 4-3k are negative for 1 < k < n. So, by induction,
-- every row with n even is nonnegative and every row with n odd is nonpositive inside
-- (2 <= k <= n-1): an odd row is a negative combination of a nonnegative row, and an inner entry
-- 3 <= k <= n-2 of an even row is a negative combination of two inner entries of an odd row. The
-- two remaining entries of an even row are given exactly: 3*T(n,2) = 3*T(n,n-1) = (-2)^n + 5 - 3n
-- (induction from the recurrence), which is 2^n + 5 - 3n >= 0 for even n.

open OMA.S_oeis_a392664 in
theorem OMA.solution : type_of% @OMA.S_oeis_a392664.main := by
  have hb1 : ∀ n : ℕ, T (n + 1) 1 = 1 := by
    intro n
    simp [T]
  have hbn : ∀ n : ℕ, T (n + 1) (n + 1) = 1 := by
    intro n
    simp [T]
  have hrec : ∀ n k : ℕ, 1 < k → k < n + 1 →
      T (n + 1) k = (-3 * ((n : ℤ) + 1) + 3 * (k : ℤ) + 1) * T n (k - 1) +
        (-3 * (k : ℤ) + 3 + 1) * T n k := by
    intro n k h1 h2
    rw [T, if_neg (show ¬(k = 1 ∨ k = n + 1) by omega), if_pos (show 1 < k ∧ k < n + 1 from ⟨h1, h2⟩)]
  have hpowN : ∀ m : ℕ, 3 * m ≤ 2 ^ m + 5 := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [pow_succ]
      by_cases hm : m ≤ 1
      · interval_cases m <;> norm_num
      · have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
  have hpowZ : ∀ m : ℕ, 3 * (m : ℤ) ≤ 2 ^ m + 5 := by
    intro m
    exact_mod_cast hpowN m
  have hu : ∀ n : ℕ, 2 ≤ n → 3 * T n 2 = (-2 : ℤ) ^ n + 5 - 3 * (n : ℤ) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      have h : T 2 2 = 1 := by decide
      rw [h]
      norm_num
    | succ n hn ih =>
      have hr := hrec n 2 (by norm_num) (by omega)
      have h1 : T n 1 = 1 := by
        obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [hm]
        exact hb1 m
      rw [hr, show (2 : ℕ) - 1 = 1 by norm_num, h1]
      push_cast
      linear_combination (-2 : ℤ) * ih
  have hv : ∀ n : ℕ, 2 ≤ n → 3 * T n (n - 1) = (-2 : ℤ) ^ n + 5 - 3 * (n : ℤ) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      have h : T 2 (2 - 1) = 1 := by decide
      rw [h]
      norm_num
    | succ n hn ih =>
      rw [show n + 1 - 1 = n by omega]
      have hr := hrec n n (by omega) (by omega)
      have h1 : T n n = 1 := by
        obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [hm]
        exact hbn m
      rw [hr, h1]
      push_cast
      linear_combination (-2 : ℤ) * ih
  have key : ∀ n : ℕ, (Even n → ∀ k : ℕ, 1 ≤ k → k ≤ n → 0 ≤ T n k) ∧
      (¬ Even n → ∀ k : ℕ, 2 ≤ k → k + 1 ≤ n → T n k ≤ 0) := by
    intro n
    induction n with
    | zero =>
      constructor
      · intro _ k h1 h2
        omega
      · intro h
        exact (h ⟨0, rfl⟩).elim
    | succ n ih =>
      obtain ⟨ihE, ihO⟩ := ih
      constructor
      · intro he k h1 h2
        have hno : ¬ Even n := fun hn => (Nat.even_add_one.mp he) hn
        rcases (show k = 1 ∨ k = n + 1 ∨ k = 2 ∨ k = n ∨ (3 ≤ k ∧ k + 1 ≤ n) by omega) with
          hk | hk | hk | hk | hk
        · rw [hk, hb1]
          norm_num
        · rw [hk, hbn]
          norm_num
        · rw [hk]
          have h3 := hu (n + 1) (by omega)
          have hp : (-2 : ℤ) ^ (n + 1) = 2 ^ (n + 1) := Even.neg_pow he 2
          have hq := hpowZ (n + 1)
          rw [hp] at h3
          push_cast at h3 hq
          linarith
        · rw [hk]
          have h3 := hv (n + 1) (by omega)
          rw [show n + 1 - 1 = n by omega] at h3
          have hp : (-2 : ℤ) ^ (n + 1) = 2 ^ (n + 1) := Even.neg_pow he 2
          have hq := hpowZ (n + 1)
          rw [hp] at h3
          push_cast at h3 hq
          linarith
        · rw [hrec n k (by omega) (by omega)]
          have a1 := ihO hno (k - 1) (by omega) (by omega)
          have a2 := ihO hno k (by omega) (by omega)
          have c1 : -3 * ((n : ℤ) + 1) + 3 * (k : ℤ) + 1 ≤ 0 := by omega
          have c2 : -3 * (k : ℤ) + 3 + 1 ≤ 0 := by omega
          have p1 := mul_nonneg (neg_nonneg.mpr c1) (neg_nonneg.mpr a1)
          have p2 := mul_nonneg (neg_nonneg.mpr c2) (neg_nonneg.mpr a2)
          nlinarith [p1, p2]
      · intro ho k h1 h2
        have hev : Even n := by
          by_contra hn
          exact ho (Nat.even_add_one.mpr hn)
        rw [hrec n k (by omega) (by omega)]
        have a1 := ihE hev (k - 1) (by omega) (by omega)
        have a2 := ihE hev k (by omega) (by omega)
        have c1 : -3 * ((n : ℤ) + 1) + 3 * (k : ℤ) + 1 ≤ 0 := by omega
        have c2 : -3 * (k : ℤ) + 3 + 1 ≤ 0 := by omega
        have p1 := mul_nonneg (neg_nonneg.mpr c1) a1
        have p2 := mul_nonneg (neg_nonneg.mpr c2) a2
        nlinarith [p1, p2]
  intro n k he h1 h2
  exact (key n).1 he k h1 h2
