import OMAStatements.S_oeis_a278616

-- Problem: A278616: Sum of terms in level n of TRIP -  Stern sequence associated with permutation triple (e,13,132).
-- Upstream: formal-conjectures statements/oeis-a278616.lean:0 (declaration OMA.S_oeis_a278616.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: level n+1 consists of F0(T(m)) and F1(T(m)) for T(m) in level n, and F0, F1 are linear.
-- So the column sums X, Y, Z of level n obey X' = X + Y + Z, Y' = X + 2Z, Z' = X + Y, a matrix with
-- characteristic polynomial t^3 - t^2 - 4t - 1. Hence a(n+3) = a(n+2) + 4a(n+1) + a(n), with
-- a(0), a(1), a(2) = 3, 8, 21, and the g.f. follows by comparing coefficients (as for A278613).

namespace N10A278616

open OMA.S_oeis_a278616

theorem T_eq (n : ℕ) : T n = if _h : n ≤ 1 then (1, 1, 1)
    else if n % 2 = 0 then F0 (T (n / 2)) else F1 (T (n / 2)) := by
  rw [T]

theorem T_one : T 1 = (1, 1, 1) := by
  rw [T_eq 1, dif_pos (le_refl 1)]

theorem T_even (m : ℕ) (hm : 1 ≤ m) : T (2 * m) = F0 (T m) := by
  rw [T_eq (2 * m), dif_neg (show ¬ (2 * m ≤ 1) by omega), if_pos (show 2 * m % 2 = 0 by omega),
    show 2 * m / 2 = m by omega]

theorem T_odd (m : ℕ) (hm : 1 ≤ m) : T (2 * m + 1) = F1 (T m) := by
  rw [T_eq (2 * m + 1), dif_neg (show ¬ (2 * m + 1 ≤ 1) by omega),
    if_neg (show ¬ ((2 * m + 1) % 2 = 0) by omega), show (2 * m + 1) / 2 = m by omega]

theorem lvl_split_gen (f : ℕ → ℕ) (p : ℕ) : ∀ b, p ≤ b →
    ∑ l ∈ Finset.Ico (2 * p) (2 * b), f l = ∑ m ∈ Finset.Ico p b, (f (2 * m) + f (2 * m + 1)) := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
      Finset.sum_Ico_succ_top (by omega : 2 * p ≤ 2 * k + 1),
      Finset.sum_Ico_succ_top (by omega : 2 * p ≤ 2 * k), Finset.sum_Ico_succ_top hk, ih]
    ring

theorem lvl_split (f : ℕ → ℕ) (n : ℕ) :
    ∑ l ∈ Finset.Ico (2 ^ (n + 1)) (2 ^ (n + 1 + 1)), f l =
      ∑ m ∈ Finset.Ico (2 ^ n) (2 ^ (n + 1)), (f (2 * m) + f (2 * m + 1)) := by
  have h := lvl_split_gen f (2 ^ n) (2 ^ (n + 1)) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have e1 : 2 * 2 ^ n = 2 ^ (n + 1) := by ring
  have e2 : 2 * 2 ^ (n + 1) = 2 ^ (n + 1 + 1) := by ring
  rw [e1, e2] at h
  exact h

theorem mem_pos (n m : ℕ) (hm : m ∈ Finset.Ico (2 ^ n) (2 ^ (n + 1))) : 1 ≤ m := by
  rw [Finset.mem_Ico] at hm
  have h1 : 0 < 2 ^ n := pow_pos (by norm_num) n
  exact lt_of_lt_of_le h1 hm.1

def Xs (n : ℕ) : ℕ := ∑ l ∈ Finset.Ico (2 ^ n) (2 ^ (n + 1)), (T l).1

def Ys (n : ℕ) : ℕ := ∑ l ∈ Finset.Ico (2 ^ n) (2 ^ (n + 1)), (T l).2.1

def Zs (n : ℕ) : ℕ := ∑ l ∈ Finset.Ico (2 ^ n) (2 ^ (n + 1)), (T l).2.2

theorem X_succ (n : ℕ) : Xs (n + 1) = Xs n + Ys n + Zs n := by
  unfold Xs Ys Zs
  rw [lvl_split (fun l => (T l).1) n, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  show (T (2 * m)).1 + (T (2 * m + 1)).1 = (T m).1 + (T m).2.1 + (T m).2.2
  rw [T_even m (mem_pos n m hm), T_odd m (mem_pos n m hm)]
  show ((T m).1 + (T m).2.2) + (T m).2.1 = (T m).1 + (T m).2.1 + (T m).2.2
  ring

theorem Y_succ (n : ℕ) : Ys (n + 1) = Xs n + 2 * Zs n := by
  unfold Xs Ys Zs
  rw [lvl_split (fun l => (T l).2.1) n, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  show (T (2 * m)).2.1 + (T (2 * m + 1)).2.1 = (T m).1 + 2 * (T m).2.2
  rw [T_even m (mem_pos n m hm), T_odd m (mem_pos n m hm)]
  show (T m).2.2 + ((T m).1 + (T m).2.2) = (T m).1 + 2 * (T m).2.2
  ring

theorem Z_succ (n : ℕ) : Zs (n + 1) = Xs n + Ys n := by
  unfold Xs Ys Zs
  rw [lvl_split (fun l => (T l).2.2) n, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  show (T (2 * m)).2.2 + (T (2 * m + 1)).2.2 = (T m).1 + (T m).2.1
  rw [T_even m (mem_pos n m hm), T_odd m (mem_pos n m hm)]
  show (T m).2.1 + (T m).1 = (T m).1 + (T m).2.1
  ring

theorem a_eq (n : ℕ) : a n = Xs n + Ys n + Zs n := by
  unfold a Xs Ys Zs
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

theorem X0 : Xs 0 = 1 := by
  show ∑ l ∈ Finset.Ico 1 (1 + 1), (T l).1 = 1
  rw [Finset.sum_Ico_succ_top (le_refl 1), Finset.Ico_self, Finset.sum_empty, zero_add, T_one]

theorem Y0 : Ys 0 = 1 := by
  show ∑ l ∈ Finset.Ico 1 (1 + 1), (T l).2.1 = 1
  rw [Finset.sum_Ico_succ_top (le_refl 1), Finset.Ico_self, Finset.sum_empty, zero_add, T_one]

theorem Z0 : Zs 0 = 1 := by
  show ∑ l ∈ Finset.Ico 1 (1 + 1), (T l).2.2 = 1
  rw [Finset.sum_Ico_succ_top (le_refl 1), Finset.Ico_self, Finset.sum_empty, zero_add, T_one]

theorem a_rec (k : ℕ) : a (k + 1 + 1 + 1) = a (k + 1 + 1) + 4 * a (k + 1) + a k := by
  rw [a_eq (k + 1 + 1 + 1), a_eq (k + 1 + 1), a_eq (k + 1), a_eq k,
    X_succ (k + 1 + 1), Y_succ (k + 1 + 1), Z_succ (k + 1 + 1),
    X_succ (k + 1), Y_succ (k + 1), Z_succ (k + 1), X_succ k, Y_succ k, Z_succ k]
  ring

theorem a_zero : a 0 = 3 := by
  rw [a_eq 0, X0, Y0, Z0]

theorem a_one : a 1 = 8 := by
  have x1 : Xs 1 = 3 := by simpa [X0, Y0, Z0] using X_succ 0
  have y1 : Ys 1 = 3 := by simpa [X0, Z0] using Y_succ 0
  have z1 : Zs 1 = 2 := by simpa [X0, Y0] using Z_succ 0
  rw [a_eq 1, x1, y1, z1]

theorem a_two : a 2 = 21 := by
  have x1 : Xs 1 = 3 := by simpa [X0, Y0, Z0] using X_succ 0
  have y1 : Ys 1 = 3 := by simpa [X0, Z0] using Y_succ 0
  have z1 : Zs 1 = 2 := by simpa [X0, Y0] using Z_succ 0
  have x2 : Xs 2 = 8 := by simpa [x1, y1, z1] using X_succ 1
  have y2 : Ys 2 = 7 := by simpa [x1, z1] using Y_succ 1
  have z2 : Zs 2 = 6 := by simpa [x1, y1] using Z_succ 1
  rw [a_eq 2, x2, y2, z2]

end N10A278616

open OMA.S_oeis_a278616 N10A278616 in
theorem OMA.solution : type_of% @OMA.S_oeis_a278616.main := by
  have hrec : ∀ k, (a (k + 3) : ℚ) = (a (k + 2) : ℚ) + 4 * (a (k + 1) : ℚ) + (a k : ℚ) := by
    intro k
    have h := a_rec k
    rw [show k + 1 + 1 + 1 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega] at h
    exact_mod_cast h
  have a0 : (a 0 : ℚ) = 3 := by exact_mod_cast a_zero
  have a1 : (a 1 : ℚ) = 8 := by exact_mod_cast a_one
  have a2 : (a 2 : ℚ) = 21 := by exact_mod_cast a_two
  obtain ⟨A, hA⟩ : ∃ A : PowerSeries ℚ, A = PowerSeries.mk (fun n => (a n : ℚ)) := ⟨_, rfl⟩
  rw [← hA]
  have cA : ∀ m, PowerSeries.coeff m A = (a m : ℚ) := by
    intro m
    rw [hA, PowerSeries.coeff_mk]
  have h3 : (PowerSeries.C (3 : ℚ) : PowerSeries ℚ) = 3 := map_ofNat _ 3
  have h4 : (PowerSeries.C (4 : ℚ) : PowerSeries ℚ) = 4 := map_ofNat _ 4
  have h5 : (PowerSeries.C (5 : ℚ) : PowerSeries ℚ) = 5 := map_ofNat _ 5
  have e : A * (-1 + PowerSeries.X + 4 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3) =
      -A + A * PowerSeries.X ^ 1 + PowerSeries.C (4 : ℚ) * (A * PowerSeries.X ^ 2) +
        A * PowerSeries.X ^ 3 := by
    rw [h4]
    ring
  have e2 : (-3 - 5 * PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries ℚ) =
      -PowerSeries.C (3 : ℚ) - PowerSeries.C (5 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.X ^ 2 := by
    rw [h3, h5]
    ring
  refine e.trans (Eq.trans ?_ e2.symm)
  ext m
  simp only [map_add, map_sub, map_neg, PowerSeries.coeff_C_mul]
  rcases Nat.lt_or_ge m 3 with hm | hm
  · interval_cases m <;>
      simp only [PowerSeries.coeff_mul_X_pow', cA, PowerSeries.coeff_X_pow, PowerSeries.coeff_C] <;>
      norm_num [a0, a1, a2]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
    have t1 : PowerSeries.coeff (k + 3) (A * PowerSeries.X ^ 1) = (a (k + 2) : ℚ) := by
      rw [show k + 3 = k + 2 + 1 by omega, PowerSeries.coeff_mul_X_pow, cA]
    have t2 : PowerSeries.coeff (k + 3) (A * PowerSeries.X ^ 2) = (a (k + 1) : ℚ) := by
      rw [show k + 3 = k + 1 + 2 by omega, PowerSeries.coeff_mul_X_pow, cA]
    have t3 : PowerSeries.coeff (k + 3) (A * PowerSeries.X ^ 3) = (a k : ℚ) := by
      rw [PowerSeries.coeff_mul_X_pow, cA]
    have u0 : PowerSeries.coeff (k + 3) (PowerSeries.C (3 : ℚ)) = 0 := by
      rw [PowerSeries.coeff_C, if_neg (show ¬(k + 3 = 0) by omega)]
    have u1 : PowerSeries.coeff (k + 3) (PowerSeries.X ^ 1 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 3 = 1) by omega)]
    have u2 : PowerSeries.coeff (k + 3) (PowerSeries.X ^ 2 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 3 = 2) by omega)]
    rw [cA (k + 3), t1, t2, t3, u0, u1, u2, hrec k]
    ring
