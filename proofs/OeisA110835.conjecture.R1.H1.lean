import OMAReductions.R_OeisA110835_conjecture_R1
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Small multipliers in Sierpinski's prime-interval conjecture

For the H1 split by @TheLittleOne1234, Nagura's classical interval theorem
is mathematically sufficient. Here the large-input estimate is proved directly:
a periodic 0/1 floor weight bounds the von Mangoldt sum from below. A signed
combination of nine dilates bounds it from above, apart from a tail with
coefficient two at scale 1/1500. Its main coefficient is strictly below 6/5.

The cutoff is effective. Below it, 101 overlapping intervals are certified
by the Lucas primality criterion with small prime divisors of each p-1.
The numerical checks use ordinary kernel reduction.
-/

namespace A110835PrimeWindow

open Finset Nat Real ArithmeticFunction

def weight (t : ℕ) : ℤ :=
  (t : ℤ) - (t / 2 : ℕ) - (t / 3 : ℕ) - (t / 5 : ℕ) + (t / 30 : ℕ)

theorem weight_period (t : ℕ) : weight (t + 30) = weight t := by
  unfold weight
  omega

theorem weight_bounds (t : ℕ) : 0 ≤ weight t ∧ weight t ≤ 1 := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases ht : t < 30
    · exact (by decide : ∀ i : Fin 30, 0 ≤ weight i ∧ weight i ≤ 1) ⟨t, ht⟩
    · have h := weight_period (t - 30)
      rw [show t - 30 + 30 = t by omega] at h
      rw [h]
      exact ih (t - 30) (by omega)

/-- Signed dilates covering all positive quotients below the tail. -/
def major (t : ℕ) : ℤ :=
  weight t + weight (t / 6) - weight (t / 7) + weight (t / 10) +
    weight (t / 36) + weight (t / 60) + weight (t / 220) +
    weight (t / 900) + weight (t / 1320)

theorem major_lower (t : ℕ) (ht : 0 < t) :
    1 ≤ major t + (if 1500 ≤ t then 2 else 0) := by
  by_cases h : 1500 ≤ t
  · rw [if_pos h]
    unfold major
    linarith only [(weight_bounds t).1, (weight_bounds (t / 6)).1,
      (weight_bounds (t / 7)).2, (weight_bounds (t / 10)).1,
      (weight_bounds (t / 36)).1, (weight_bounds (t / 60)).1,
      (weight_bounds (t / 220)).1, (weight_bounds (t / 900)).1,
      (weight_bounds (t / 1320)).1]
  · rw [if_neg h, add_zero]
    have hs : ∀ i : Fin 50, ∀ j : Fin 30,
        1 ≤ major (30 * i.val + j.val + 1) + (if 1500 ≤ 30 * i.val + j.val + 1 then 2 else 0) := by
      decide
    have he : 30 * ((t - 1) / 30) + (t - 1) % 30 + 1 = t := by omega
    simpa only [he, if_neg h, add_zero] using
      hs ⟨(t - 1) / 30, by omega⟩ ⟨(t - 1) % 30, by omega⟩

noncomputable def L (n : ℕ) : ℝ := Real.log (n.factorial : ℝ)

theorem L_succ (n : ℕ) : L (n + 1) = L n + Real.log (n + 1 : ℝ) := by
  simp only [L, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  rw [Real.log_mul (by positivity) (by positivity), add_comm]

theorem factorial_convolution (n N : ℕ) (hn : n ≤ N) :
    L n = ∑ q ∈ Icc 1 N, ((n / q : ℕ) : ℝ) * vonMangoldt q := by
  induction n with
  | zero => simp [L]
  | succ n ih =>
    rw [L_succ, ih (by omega)]
    have hs : (Icc 1 N).filter (· ∣ n + 1) = (n + 1).divisors := by
      ext q
      simp only [mem_filter, mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨_, hq⟩
        exact ⟨hq, by omega⟩
      · rintro ⟨hq, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hq (by omega), (Nat.le_of_dvd (by omega) hq).trans hn⟩, hq⟩
    have hsum : (∑ q ∈ Icc 1 N, if q ∣ n + 1 then vonMangoldt q else 0) =
        Real.log (n + 1 : ℝ) := by
      rw [← sum_filter, hs, vonMangoldt_sum, Nat.cast_add, Nat.cast_one]
    rw [← hsum, ← sum_add_distrib]
    apply sum_congr rfl
    intro q hq
    rw [Nat.succ_div]
    by_cases hd : q ∣ n + 1 <;> simp [hd, add_mul]

noncomputable def T (n : ℕ) : ℝ :=
  L n - L (n / 2) - L (n / 3) - L (n / 5) + L (n / 30)

theorem T_sum (n d : ℕ) :
    T (n / d) = ∑ q ∈ Icc 1 n, (weight (n / q / d) : ℝ) * vonMangoldt q := by
  have hf (j : ℕ) : L (n / j) =
      ∑ q ∈ Icc 1 n, ((n / q / j : ℕ) : ℝ) * vonMangoldt q := by
    rw [factorial_convolution (n / j) n (Nat.div_le_self _ _)]
    simp only [Nat.div_right_comm n j]
  unfold T
  simp only [Nat.div_div_eq_div_mul, hf, weight, Int.cast_add, Int.cast_sub, Int.cast_natCast,
    sub_mul, add_mul, sum_sub_distrib, sum_add_distrib, Nat.div_div_eq_div_mul, Nat.mul_assoc]

noncomputable def psiN (n : ℕ) : ℝ := ∑ q ∈ Icc 1 n, vonMangoldt q

theorem T_le_psiN (n : ℕ) : T n ≤ psiN n := by
  have ht := T_sum n 1
  simp only [Nat.div_one] at ht
  rw [ht, psiN]
  apply sum_le_sum
  intro q _
  exact mul_le_of_le_one_left vonMangoldt_nonneg (by exact_mod_cast (weight_bounds (n / q)).2)

theorem psiN_le_L (n : ℕ) : psiN n ≤ L n := by
  rw [factorial_convolution n n le_rfl, psiN]
  apply sum_le_sum
  intro q hq
  obtain ⟨hq0, hqn⟩ := mem_Icc.mp hq
  exact le_mul_of_one_le_left vonMangoldt_nonneg (by exact_mod_cast Nat.div_pos hqn hq0)

theorem psiN_tail (n d : ℕ) (hd : 0 < d) :
    psiN (n / d) = ∑ q ∈ Icc 1 n, if d ≤ n / q then vonMangoldt q else 0 := by
  rw [psiN, ← sum_filter]
  congr 1
  ext q
  simp only [mem_Icc, mem_filter]
  by_cases hq : 1 ≤ q
  · rw [Nat.le_div_iff_mul_le hd, Nat.le_div_iff_mul_le hq, Nat.mul_comm q d]
    constructor
    · rintro ⟨_, h⟩
      exact ⟨⟨hq, (Nat.le_mul_of_pos_left q hd).trans h⟩, h⟩
    · exact fun h => ⟨hq, h.2⟩
  · simp [hq]

noncomputable def U (n : ℕ) : ℝ :=
  T n + T (n / 6) - T (n / 7) + T (n / 10) + T (n / 36) + T (n / 60) +
    T (n / 220) + T (n / 900) + T (n / 1320)

theorem psiN_le_U (n : ℕ) : psiN n ≤ U n + 2 * psiN (n / 1500) := by
  have hu : U n = ∑ q ∈ Icc 1 n, (major (n / q) : ℝ) * vonMangoldt q := by
    have ho := T_sum n 1
    simp only [Nat.div_one] at ho
    simp only [U, ho, T_sum, major, Int.cast_add, Int.cast_sub, add_mul, sub_mul,
      sum_add_distrib, sum_sub_distrib]
  rw [hu, psiN_tail n 1500 (by decide), Finset.mul_sum, ← sum_add_distrib, psiN]
  apply sum_le_sum
  intro q hq
  have hh := major_lower (n / q) (Nat.div_pos (mem_Icc.mp hq).2 (mem_Icc.mp hq).1)
  have hv : 0 ≤ vonMangoldt q := vonMangoldt_nonneg
  by_cases h : 1500 ≤ n / q
  · rw [if_pos h] at hh ⊢
    have hc : (1 : ℝ) ≤ (major (n / q) : ℝ) + 2 := by exact_mod_cast hh
    simpa only [one_mul, add_mul] using mul_le_mul_of_nonneg_right hc hv
  · rw [if_neg h] at hh ⊢
    simp only [add_zero] at hh
    simpa only [mul_zero, add_zero] using
      (le_mul_of_one_le_left hv (by exact_mod_cast hh) :
        vonMangoldt q ≤ (major (n / q) : ℝ) * vonMangoldt q)

end A110835PrimeWindow

namespace A110835PrimeWindow

open Real

noncomputable def g (x : ℝ) : ℝ := x * Real.log x - x

theorem tangent {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    g x + (y - x) * Real.log x ≤ g y := by
  rcases hy.eq_or_lt with he | hy'
  · subst y
    simp only [g, zero_mul, sub_zero, zero_sub, neg_mul]
    linarith
  · have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hx hy')) hy
    simp only [Real.log_div hx.ne' hy'.ne', mul_sub, mul_div_cancel₀ _ hy'.ne', mul_one] at h
    unfold g
    linarith only [h]

theorem L_bounds (n : ℕ) :
    g n ≤ L n ∧ L n ≤ g ((n : ℝ) + 1) + 1 := by
  induction n with
  | zero => norm_num [g, L]
  | succ n ih =>
    rw [L_succ]
    push_cast
    have hlo := tangent (x := (n : ℝ) + 1) (y := n) (by positivity) (by positivity)
    have hhi := tangent (x := (n : ℝ) + 1) (y := n + 1 + 1) (by positivity) (by positivity)
    constructor <;> linarith

theorem L_approx {y X : ℝ} (hy : 0 ≤ y) (hyX : y ≤ X) :
    |L ⌊y⌋₊ - g y| ≤ 1 + Real.log (X + 1) := by
  let k := ⌊y⌋₊
  have hk : (k : ℝ) ≤ y := Nat.floor_le hy
  have hk' : y < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hX : 0 ≤ Real.log (X + 1) := Real.log_nonneg (by linarith)
  obtain ⟨h₁, h₂⟩ := L_bounds k
  have hlogk : Real.log ((k : ℝ) + 1) ≤ Real.log (X + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hdec := tangent (x := (k : ℝ) + 1) (y := y) (by positivity) hy
  have hstep := mul_le_mul_of_nonneg_right (show (k : ℝ) + 1 - y ≤ 1 by linarith)
    (Real.log_nonneg (show 1 ≤ (k : ℝ) + 1 by linarith only [Nat.cast_nonneg (α := ℝ) k]))
  change |L k - g y| ≤ _
  rw [abs_le]
  constructor
  · rcases hy.eq_or_lt with hzero | hy'
    · subst y; simp [k, L, g]; linarith
    have ht := tangent (x := y) (y := k) hy' (Nat.cast_nonneg _)
    have hLy := Real.log_le_log hy' (show y ≤ X + 1 by linarith)
    have hterm : (y - k) * Real.log y ≤ Real.log (X + 1) := calc
      _ ≤ (y - k) * Real.log (X + 1) := mul_le_mul_of_nonneg_left hLy (by linarith)
      _ ≤ 1 * Real.log (X + 1) := mul_le_mul_of_nonneg_right (by linarith) hX
      _ = _ := one_mul _
    linarith
  · linarith

noncomputable def A : ℝ :=
  Real.log 2 / 2 + Real.log 3 / 3 + Real.log 5 / 5 - Real.log 30 / 30

theorem A_bounds : 1 / 2 ≤ A ∧ A ≤ 2 := by
  have he : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  have hlog2 := Real.log_le_sub_one_of_pos (x := (2 : ℝ)⁻¹) (by norm_num)
  rw [Real.log_inv] at hlog2
  have h3 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 3)
  have h5 := Real.log_le_log (by norm_num : (0 : ℝ) < 2 ^ 2) (by norm_num : (2 : ℝ) ^ 2 ≤ 5)
  rw [Real.log_pow] at h5
  unfold A
  constructor
  · norm_num at hlog2 h5
    linarith
  · have h30 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 30)
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3),
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)]

theorem g_balance (x : ℝ) :
    g x - g (x / 2) - g (x / 3) - g (x / 5) + g (x / 30) = A * x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [g]
  · simp only [g, A, Real.log_div hx (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_div hx (by norm_num : (3 : ℝ) ≠ 0), Real.log_div hx (by norm_num : (5 : ℝ) ≠ 0),
      Real.log_div hx (by norm_num : (30 : ℝ) ≠ 0)]
    ring

theorem T_approx (n : ℕ) :
    |T n - A * n| ≤ 5 * (1 + Real.log ((n : ℝ) + 1)) := by
  have h (d : ℕ) (hd : 1 ≤ d) : |L (n / d) - g ((n : ℝ) / d)| ≤
      1 + Real.log ((n : ℝ) + 1) := by
    simpa only [Nat.floor_div_eq_div] using
      (L_approx (y := (n : ℝ) / d) (X := n) (by positivity)
        (div_le_self (by positivity) (by exact_mod_cast hd)))
  have h1 := abs_le.mp (h 1 (by decide))
  simp only [Nat.div_one, Nat.cast_one, div_one] at h1
  have h2 := abs_le.mp (h 2 (by decide))
  have h3 := abs_le.mp (h 3 (by decide))
  have h5 := abs_le.mp (h 5 (by decide))
  have h30 := abs_le.mp (h 30 (by decide))
  norm_num only [Nat.cast_ofNat] at h2 h3 h5 h30
  rw [← g_balance, T, abs_le]
  constructor <;> linarith

end A110835PrimeWindow

namespace A110835PrimeWindow

open Finset Real

theorem psiN_eq (n : ℕ) : psiN n = Chebyshev.psi n := by
  have he : Icc 1 n = Ioc 0 n := by ext q; simp only [mem_Icc, mem_Ioc]; omega
  simp only [psiN, Chebyshev.psi, Nat.floor_natCast, he]

theorem psi_lower (n : ℕ) : A * n - 5 * (1 + log ((n : ℝ) + 1)) ≤ psiN n := by
  linarith only [(abs_le.mp (T_approx n)).1, T_le_psiN n]

theorem log_two_pow_le (k : ℕ) : log ((2 : ℝ) ^ k) ≤ k := by
  rw [Real.log_pow]
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) (by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)])

theorem psi_upper (n : ℕ) :
    psiN n ≤ (47 / 40 : ℝ) * (A * n) + 12 / 1500 * n + 45 * (1 + log ((n : ℝ) + 1)) + 2 := by
  let B := 5 * (1 + log ((n : ℝ) + 1))
  have hA : 0 ≤ A := le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) A_bounds.1
  have he (d : ℕ) : |T (n / d) - A * (n / d : ℕ)| ≤ B := by
    apply (T_approx _).trans
    have hdn : ((n / d : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.div_le_self n d
    have hl := Real.log_le_log (x := ((n / d : ℕ) : ℝ) + 1) (y := (n : ℝ) + 1)
      (by positivity) (by linarith)
    dsimp [B]
    linarith
  have hup (d : ℕ) (hd : 0 < d) : T (n / d) ≤ A * ((n : ℝ) / d) + B := by
    have hcast : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d :=
      (le_div_iff₀ (by exact_mod_cast hd)).mpr (by exact_mod_cast Nat.div_mul_le_self n d)
    linarith only [(abs_le.mp (he d)).2, mul_le_mul_of_nonneg_left hcast hA]
  have hbelow : (n : ℝ) / 7 ≤ ((n / 7 : ℕ) : ℝ) + 1 :=
    (div_le_iff₀ (by norm_num)).mpr (by exact_mod_cast (show n ≤ (n / 7 + 1) * 7 by omega))
  have h7 : A * ((n : ℝ) / 7) - A - B ≤ T (n / 7) := by
    linarith only [(abs_le.mp (he 7)).1, mul_le_mul_of_nonneg_left hbelow hA]
  have hu : U n ≤ (162809 / 138600 : ℝ) * (A * n) + 9 * B + A := by
    have h1 := hup 1 (by decide)
    simp only [Nat.div_one, Nat.cast_one, div_one] at h1
    unfold U
    linarith only [h1, hup 6 (by decide), h7, hup 10 (by decide), hup 36 (by decide),
      hup 60 (by decide), hup 220 (by decide), hup 900 (by decide), hup 1320 (by decide)]
  have hc := mul_le_mul_of_nonneg_right (by norm_num : (162809 / 138600 : ℝ) ≤ 47 / 40)
    (mul_nonneg hA (Nat.cast_nonneg n))
  have h4 : log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact log_two_pow_le 2
  have htail := Chebyshev.psi_le_const_mul_self (x := ((n / 1500 : ℕ) : ℝ)) (by positivity)
  rw [← psiN_eq] at htail
  have hdiv : ((n / 1500 : ℕ) : ℝ) * 1500 ≤ n := by exact_mod_cast Nat.div_mul_le_self n 1500
  have h6 := mul_le_mul_of_nonneg_right (show log 4 + 4 ≤ 6 by linarith) (Nat.cast_nonneg (n / 1500))
  dsimp [B] at hu
  linarith only [psiN_le_U n, hu, hc, htail, h6, hdiv, A_bounds.2]

end A110835PrimeWindow

namespace A110835PrimeWindow

open Real

theorem log_cost {t : ℝ} (ht : 1073741824 ≤ t) :
    1 + log (t + 1) ≤ 32 * t / 1073741824 := by
  have hpos : 0 < t + 1 := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hpos (by norm_num : (0 : ℝ) < 1073741824))
  rw [Real.log_div hpos.ne' (by norm_num)] at h
  have hK := log_two_pow_le 30
  rw [show (2 : ℝ) ^ 30 = 1073741824 by norm_num] at hK
  norm_num only [Nat.cast_ofNat] at hK
  linarith

theorem log_large {t : ℝ} (ht : 1073741824 ≤ t) : log t ≤ (32 / 32768 : ℝ) * √t := by
  have ht0 : 0 ≤ t := by linarith
  have hs : (32768 : ℝ) ≤ √t := calc
    _ = √(32768 ^ 2 : ℝ) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by norm_num; exact ht)
  have hp : 0 < √t := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hp (by norm_num : (0 : ℝ) < 32768))
  rw [Real.log_div hp.ne' (by norm_num), Real.log_sqrt ht0] at h
  have hK := log_two_pow_le 15
  rw [show (2 : ℝ) ^ 15 = 32768 by norm_num] at hK
  norm_num only [Nat.cast_ofNat] at hK
  linarith

theorem theta_increase {x y : ℕ} (hx : 2 ^ 30 ≤ x) (hlo : 6 * x ≤ 5 * y) (hhi : y ≤ 2 * x) :
    Chebyshev.theta x < Chebyshev.theta y := by
  have hx' : (1073741824 : ℝ) ≤ x := by exact_mod_cast (show 1073741824 ≤ x from hx)
  have hl : 6 * (x : ℝ) ≤ 5 * y := by exact_mod_cast hlo
  have hh : (y : ℝ) ≤ 2 * x := by exact_mod_cast hhi
  have hy : (1073741824 : ℝ) ≤ y := by linarith
  have hA : 0 ≤ A := le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) A_bounds.1
  have herr := Chebyshev.psi_sub_theta_le (x := (y : ℝ)) (by linarith)
  rw [← psiN_eq] at herr
  have hbound : 2 * √(y : ℝ) * log (y : ℝ) ≤ (64 / 32768 : ℝ) * y := calc
    _ ≤ 2 * √(y : ℝ) * ((32 / 32768 : ℝ) * √(y : ℝ)) :=
      mul_le_mul_of_nonneg_left (log_large hy) (by positivity)
    _ = _ := by nlinarith only [Real.sq_sqrt (Nat.cast_nonneg y)]
  have htheta := Chebyshev.theta_le_psi (x := (x : ℝ))
  rw [← psiN_eq] at htheta
  linarith only [hx', hh, mul_le_mul_of_nonneg_left hl hA,
    mul_le_mul_of_nonneg_right A_bounds.1 (Nat.cast_nonneg x), htheta,
    psi_upper x, psi_lower y, herr, hbound, log_cost hx', log_cost hy]

theorem large_window (n m : ℕ) (hm : 1 ≤ m) (hm5 : m ≤ 5) (hx : 2 ^ 30 ≤ n * m) :
    ∃ p : ℕ, p.Prime ∧ n * m ≤ p ∧ p ≤ n * (m + 1) := by
  have h6 : 6 * (n * m) ≤ 5 * (n * (m + 1)) := by
    rw [Nat.mul_succ]
    have := Nat.mul_le_mul_left n hm5
    omega
  have h2 : n * (m + 1) ≤ 2 * (n * m) := by
    rw [Nat.mul_succ]
    have := Nat.le_mul_of_pos_right n hm
    omega
  have ht := theta_increase hx h6 h2
  by_contra hn
  have he : (n * m).primesLE = (n * (m + 1)).primesLE := by
    ext p
    simp only [Nat.mem_primesLE]
    constructor
    · rintro ⟨hl, hp⟩
      exact ⟨hl.trans (Nat.mul_le_mul_left _ (Nat.le_succ _)), hp⟩
    · rintro ⟨hu, hp⟩
      refine ⟨?_, hp⟩
      by_contra! hlt
      exact hn ⟨p, hp, hlt.le, hu⟩
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log, he] at ht
  exact ht.false

end A110835PrimeWindow

namespace A110835PrimeWindow

def powC (p a : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | h + 1, e => (powC p a h (e / 2) ^ 2 * (if e % 2 = 0 then 1 else a)) % p

theorem powC_cast (p a h e : ℕ) (he : e < 2 ^ h) :
    (powC p a h e : ZMod p) = (a : ZMod p) ^ e := by
  induction h generalizing e with
  | zero =>
    have : e = 0 := by simp only [pow_zero] at he; omega
    simp [powC, this]
  | succ h ih =>
    rw [pow_succ] at he
    rw [powC, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow, ih (e / 2) (by omega), ← pow_mul]
    by_cases hpar : e % 2 = 0
    · rw [if_pos hpar, Nat.cast_one, mul_one, show e / 2 * 2 = e by omega]
    · rw [if_neg hpar, ← pow_succ, show e / 2 * 2 + 1 = e by omega]

/-- Divisibility by a power of 97! bounds the prime factors that Lucas must test. -/
def lucasOK (p a : ℕ) : Bool := decide (1 < p ∧ p < 2 ^ 32 ∧
  (p - 1) ∣ (Nat.factorial 97) ^ 32 ∧ powC p a 32 (p - 1) % p = 1 ∧
  ∀ q : Fin 98, q.val.Prime → q.val ∣ p - 1 → powC p a 32 ((p - 1) / q.val) % p ≠ 1)

theorem lucasOK_prime {p a : ℕ} (ok : lucasOK p a = true) : Nat.Prime p := by
  obtain ⟨hp, hbound, hfac, ha, htest⟩ := of_decide_eq_true ok
  have iff_one (e : ℕ) (he : e < 2 ^ 32) :
      (a : ZMod p) ^ e = 1 ↔ powC p a 32 e % p = 1 := by
    rw [← powC_cast p a 32 e he]
    simpa only [Nat.cast_one, Nat.mod_eq_of_lt hp] using
      ZMod.natCast_eq_natCast_iff' (powC p a 32 e) 1 p
  apply lucas_primality p (a : ZMod p) ((iff_one _ (by omega)).mpr ha)
  intro q hq hqd
  have hqf : q ∣ Nat.factorial 97 := hq.dvd_of_dvd_pow (hqd.trans hfac)
  have hq97 : q ≤ 97 := hq.dvd_factorial.mp hqf
  exact fun hh => htest ⟨q, by omega⟩ hq hqd ((iff_one _ ((Nat.div_le_self _ _).trans_lt
    (show p - 1 < 2 ^ 32 by omega))).mp hh)

def chain (last : ℕ) : List (ℕ × ℕ) → ℕ → Bool
  | [], lo => decide (last < lo)
  | (p, a) :: ps, lo =>
    decide (5 * p ≤ 6 * lo) && (lucasOK p a && chain last ps (p + 1))

theorem chain_sound {last x : ℕ} (ps : List (ℕ × ℕ)) (lo : ℕ)
    (ok : chain last ps lo = true) (hl : lo ≤ x) (hu : x ≤ last) :
    ∃ p : ℕ, Nat.Prime p ∧ x ≤ p ∧ 5 * p ≤ 6 * x := by
  induction ps generalizing lo with
  | nil => simp [chain] at ok; omega
  | cons ph ps ih =>
    obtain ⟨p, a⟩ := ph
    simp only [chain, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨hratio, ht, hnext⟩ := ok
    by_cases hxp : x ≤ p
    · exact ⟨p, lucasOK_prime ht, hxp, by omega⟩
    · exact ih (p + 1) hnext (by omega)

def primeData : List (ℕ × ℕ) :=
  [(29,2), (31,3), (37,2), (43,3), (47,5), (53,2), (61,2), (73,5),
   (83,2), (97,5), (113,3), (131,2), (157,5), (181,2), (211,2), (251,6),
   (293,2), (349,2), (419,2), (499,7), (599,7), (709,2), (829,2), (991,6),
   (1181,7), (1409,3), (1667,2), (1999,3), (2393,3), (2861,2), (3433,5), (4093,2),
   (4903,3), (5881,31), (7057,5), (8467,2), (10151,7), (12161,3), (14593,5), (17497,5),
   (20939,2), (25117,5), (30133,5), (36109,2), (43321,13), (51977,3), (62351,7), (74821,6),
   (89783,5), (107713,10), (129229,2), (154981,2), (185833,13), (222977,6), (267541,11),
   (321031,3), (385153,7), (461971,2), (554269,6), (665039,7), (797917,2), (957181,19),
   (1148437,2), (1378081,7), (1653697,7), (1984139,2), (2380951,11), (2856961,11),
   (3428353,7), (4113883,2), (4936121,3), (5922533,2), (7106959,3), (8527741,2),
   (10233287,5), (12279877,5), (14735771,2), (17681743,3), (21217681,43), (25460731,7),
   (30552877,2), (36662221,10), (43994539,7), (52789969,13), (63347257,5), (76015969,17),
   (91217449,13), (109460801,3), (131351851,2), (157621927,6), (189144001,11),
   (226972747,7), (272365633,5), (326838643,12), (392205601,11), (470646721,7),
   (564769999,3), (677718091,2), (813261151,6), (975912961,23), (1171086281,3)]

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 8192 in
theorem certified_chain : chain (2 ^ 30) primeData 25 = true := by rfl

theorem finite_window (n m : ℕ) (hm : 1 ≤ m) (hm5 : m ≤ 5) (hmn : m < n)
    (hsmall : n * m ≤ 2 ^ 30) : ∃ p : ℕ, p.Prime ∧ n * m ≤ p ∧ p ≤ n * (m + 1) := by
  by_cases h : 25 ≤ n * m
  · obtain ⟨p, hp, hl, hu⟩ := chain_sound primeData 25 certified_chain h hsmall
    have hmul := Nat.mul_le_mul_left n hm5
    refine ⟨p, hp, hl, ?_⟩
    rw [Nat.mul_succ]
    omega
  · have hn : n < 25 := lt_of_le_of_lt (Nat.le_mul_of_pos_right n hm) (by omega)
    have hs : ∀ i : Fin 25, ∀ j : Fin 6, 1 ≤ j.val → j.val < i.val → i.val * j.val < 25 →
        ∃ p : Fin 50, p.val.Prime ∧ i.val * j.val ≤ p.val ∧ p.val ≤ i.val * (j.val + 1) := by decide
    obtain ⟨p, hp⟩ := hs ⟨n, hn⟩ ⟨m, by omega⟩ hm hmn (show n * m < 25 from Nat.lt_of_not_ge h)
    exact ⟨p.val, hp⟩

end A110835PrimeWindow

theorem OMA.solution : OMA.R_OeisA110835_conjecture_R1.H1 := by
  intro n m hm h5 hn
  rcases le_total (n * m) (2 ^ 30) with h | h
  · exact A110835PrimeWindow.finite_window n m hm h5 hn h
  · exact A110835PrimeWindow.large_window n m hm h5 h
