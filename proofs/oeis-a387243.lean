import OMAStatements.S_oeis_a387243
import Mathlib

/-!
Proof of the A387243 conjecture `a(n) = A382131(n) - n`.

Write `c = A381767`. For `m ≥ 2`, `N < c m ↔ N^(m-1) < m^m`, so `(k+n)^k < (k+1)^(k+1) ↔ k + n < c (k+1)`.
The analytic step is `c m < c (m+1)`: with `X_j = exp((j+1) log(j+1) / j)` (so `X_j^j = (j+1)^(j+1)`), the map
`t ↦ exp((t+1) log(t+1) / t) - t` is monotone on `t > 0` (its derivative is `≥ 0` because
`(t+1) log(t+1)^2 ≤ t^2`, which is `v ≤ sinh v` at `v = log(t+1)/2`), so `X_j + 1 ≤ X_(j+1)`.
Then the positive integers missing from `c` below `c m + 1` number `c m - m`, and with `K = A387243 n` one gets
`c K < K + n < c (K+1)`, so `K + n` is the `n`-th missing integer.
-/

namespace OMA.A387243Proof

open OMA.S_oeis_a387243

/-! ## The integer form of A381767 -/

theorem c_one : A381767 1 = 1 := by
  simp [A381767]

theorem c_of_two_le {m : ℕ} (hm : 2 ≤ m) :
    A381767 m = sInf {N : ℕ | m ^ m ≤ N ^ (m - 1)} := by
  rw [A381767, if_neg (show m ≠ 1 by omega)]

theorem c_nonempty {m : ℕ} (hm : 2 ≤ m) : ({N : ℕ | m ^ m ≤ N ^ (m - 1)} : Set ℕ).Nonempty :=
  ⟨m ^ m, show m ^ m ≤ (m ^ m) ^ (m - 1) from Nat.le_self_pow (by omega) (m ^ m)⟩

theorem c_mem {m : ℕ} (hm : 2 ≤ m) : m ^ m ≤ A381767 m ^ (m - 1) := by
  rw [c_of_two_le hm]
  exact Nat.sInf_mem (c_nonempty hm)

theorem c_le {m N : ℕ} (hm : 2 ≤ m) (h : m ^ m ≤ N ^ (m - 1)) : A381767 m ≤ N := by
  rw [c_of_two_le hm]
  exact Nat.sInf_le (show N ∈ {N : ℕ | m ^ m ≤ N ^ (m - 1)} from h)

theorem lt_c_iff {m N : ℕ} (hm : 2 ≤ m) : N < A381767 m ↔ N ^ (m - 1) < m ^ m := by
  constructor
  · intro h
    by_contra hc
    exact absurd h (not_lt.mpr (c_le hm (not_lt.mp hc)))
  · intro h
    by_contra hc
    have h1 : A381767 m ^ (m - 1) ≤ N ^ (m - 1) := Nat.pow_le_pow_left (not_lt.mp hc) (m - 1)
    exact absurd h (not_lt.mpr ((c_mem hm).trans h1))

theorem c_pos {m : ℕ} (hm : 2 ≤ m) : 0 < A381767 m := by
  rw [lt_c_iff hm, zero_pow (show m - 1 ≠ 0 by omega)]
  exact pow_pos (by omega) m

/-! ## The real inequality `X_j + 1 ≤ X_(j+1)` -/

theorem key_log {t : ℝ} (ht : 0 < t) : (t + 1) * Real.log (t + 1) ^ 2 ≤ t ^ 2 := by
  have ht1 : 0 < t + 1 := by linarith
  have hL0 : 0 ≤ Real.log (t + 1) := Real.log_nonneg (by linarith)
  have hs : Real.log (t + 1) / 2 ≤ Real.sinh (Real.log (t + 1) / 2) :=
    Real.self_le_sinh_iff.mpr (div_nonneg hL0 (by norm_num))
  rw [Real.sinh_eq, Real.exp_neg] at hs
  have hw0 : 0 < Real.exp (Real.log (t + 1) / 2) := Real.exp_pos _
  have hw2 : Real.exp (Real.log (t + 1) / 2) ^ 2 = t + 1 := by
    rw [sq, ← Real.exp_add, add_halves, Real.exp_log ht1]
  generalize Real.exp (Real.log (t + 1) / 2) = w at hs hw0 hw2
  generalize Real.log (t + 1) = L at hs hL0 ⊢
  have h1 : L * w ≤ t := by
    have h2 : L / 2 * w ≤ (w - w⁻¹) / 2 * w := mul_le_mul_of_nonneg_right hs (le_of_lt hw0)
    have h3 : (w - w⁻¹) / 2 * w = (w * w - w⁻¹ * w) / 2 := by ring
    rw [inv_mul_cancel₀ (ne_of_gt hw0)] at h3
    rw [h3, ← sq, hw2] at h2
    linarith
  have h4 : 0 ≤ L * w := mul_nonneg hL0 (le_of_lt hw0)
  have h5 : (L * w) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ h4 h1 2
  calc (t + 1) * L ^ 2 = (L * w) ^ 2 := by rw [mul_pow, hw2]; ring
    _ ≤ t ^ 2 := h5

theorem phi_hasDeriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Real.exp ((s + 1) * Real.log (s + 1) / s) - s)
      (Real.exp ((t + 1) * Real.log (t + 1) / t) * ((t - Real.log (t + 1)) / t ^ 2) - 1) t := by
  have ht1 : t + 1 ≠ 0 := ne_of_gt (by linarith)
  have h1 : HasDerivAt (fun s : ℝ => s + 1) 1 t := (hasDerivAt_id' t).add_const 1
  have h2 : HasDerivAt (fun s : ℝ => Real.log (s + 1)) (1 / (t + 1)) t := h1.log ht1
  have h3 : HasDerivAt (fun s : ℝ => (s + 1) * Real.log (s + 1))
      (1 * Real.log (t + 1) + (t + 1) * (1 / (t + 1))) t := h1.mul h2
  have h4 : HasDerivAt (fun s : ℝ => (s + 1) * Real.log (s + 1) / s)
      (((1 * Real.log (t + 1) + (t + 1) * (1 / (t + 1))) * t - (t + 1) * Real.log (t + 1) * 1) / t ^ 2) t :=
    h3.div (hasDerivAt_id' t) (ne_of_gt ht)
  have h5 : HasDerivAt (fun s : ℝ => Real.exp ((s + 1) * Real.log (s + 1) / s))
      (Real.exp ((t + 1) * Real.log (t + 1) / t) *
        (((1 * Real.log (t + 1) + (t + 1) * (1 / (t + 1))) * t - (t + 1) * Real.log (t + 1) * 1) / t ^ 2)) t :=
    h4.exp
  have h6 : HasDerivAt (fun s : ℝ => Real.exp ((s + 1) * Real.log (s + 1) / s) - s)
      (Real.exp ((t + 1) * Real.log (t + 1) / t) *
        (((1 * Real.log (t + 1) + (t + 1) * (1 / (t + 1))) * t - (t + 1) * Real.log (t + 1) * 1) / t ^ 2)
        - 1) t :=
    h5.sub (hasDerivAt_id' t)
  refine h6.congr_deriv ?_
  rw [mul_one_div_cancel ht1]
  ring

theorem phi_deriv_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ Real.exp ((x + 1) * Real.log (x + 1) / x) * ((x - Real.log (x + 1)) / x ^ 2) - 1 := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hx1 : 0 < x + 1 := by linarith
  have hL0 : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
  have hLx : Real.log (x + 1) ≤ x := by
    have := Real.log_le_sub_one_of_pos hx1
    linarith
  have hkey := key_log hx
  have hsplit : (x + 1) * Real.log (x + 1) / x = Real.log (x + 1) + Real.log (x + 1) / x := by
    rw [add_mul, one_mul, add_div, mul_div_cancel_left₀ _ hx0]
  have hE : Real.exp ((x + 1) * Real.log (x + 1) / x) =
      (x + 1) * Real.exp (Real.log (x + 1) / x) := by
    rw [hsplit, Real.exp_add, Real.exp_log hx1]
  have hexp := Real.add_one_le_exp (Real.log (x + 1) / x)
  have hqx : Real.log (x + 1) / x * x = Real.log (x + 1) := div_mul_cancel₀ _ hx0
  rw [hE]
  generalize Real.log (x + 1) / x = q at hexp hqx ⊢
  generalize Real.log (x + 1) = L at hL0 hLx hkey hqx ⊢
  have hxL : 0 ≤ x - L := by linarith
  have hx2 : 0 < x ^ 2 := pow_pos hx 2
  have hq2 : (x + 1) * q ^ 2 ≤ 1 := by
    have h1 : (x + 1) * q ^ 2 * x ^ 2 ≤ 1 * x ^ 2 := by
      have e : (x + 1) * q ^ 2 * x ^ 2 = (x + 1) * (q * x) ^ 2 := by ring
      rw [e, hqx, one_mul]
      exact hkey
    exact le_of_mul_le_mul_right h1 hx2
  have hB : x ^ 2 ≤ (x + 1) * (q + 1) * (x - L) := by
    rw [← hqx]
    nlinarith [mul_nonneg (le_of_lt hx) (sub_nonneg.mpr hq2)]
  have hA : (x + 1) * (q + 1) * (x - L) ≤ (x + 1) * Real.exp q * (x - L) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (le_of_lt hx1)) hxL
  have hC : x ^ 2 ≤ (x + 1) * Real.exp q * (x - L) := le_trans hB hA
  have hD : x ^ 2 * (x ^ 2)⁻¹ ≤ (x + 1) * Real.exp q * (x - L) * (x ^ 2)⁻¹ :=
    mul_le_mul_of_nonneg_right hC (le_of_lt (inv_pos.mpr hx2))
  rw [mul_inv_cancel₀ (ne_of_gt hx2)] at hD
  have hF : (x + 1) * Real.exp q * ((x - L) / x ^ 2) =
      (x + 1) * Real.exp q * (x - L) * (x ^ 2)⁻¹ := by
    rw [div_eq_mul_inv]
    ring
  rw [hF]
  linarith

theorem phi_mono :
    MonotoneOn (fun s : ℝ => Real.exp ((s + 1) * Real.log (s + 1) / s) - s) (Set.Ioi 0) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := fun t : ℝ => Real.exp ((t + 1) * Real.log (t + 1) / t) * ((t - Real.log (t + 1)) / t ^ 2) - 1)
    (convex_Ioi 0) ?_ ?_ ?_
  · intro x hx
    exact (phi_hasDeriv (Set.mem_Ioi.mp hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx ⊢
    exact (phi_hasDeriv (Set.mem_Ioi.mp hx)).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact phi_deriv_nonneg (Set.mem_Ioi.mp hx)

theorem X_pow (j : ℕ) (hj : 1 ≤ j) :
    Real.exp (((j : ℝ) + 1) * Real.log ((j : ℝ) + 1) / (j : ℝ)) ^ j = ((j : ℝ) + 1) ^ (j + 1) := by
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  rw [← Real.exp_nat_mul]
  have h : (j : ℝ) * (((j : ℝ) + 1) * Real.log ((j : ℝ) + 1) / (j : ℝ)) =
      ((j + 1 : ℕ) : ℝ) * Real.log ((j : ℝ) + 1) := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ hj0, Nat.cast_succ]
  rw [h, Real.exp_nat_mul, Real.exp_log (show (0 : ℝ) < (j : ℝ) + 1 by positivity)]

/-- The core step: `N^j < (j+1)^(j+1)` implies `(N+1)^(j+1) < (j+2)^(j+2)`. -/
theorem core (j N : ℕ) (hj : 1 ≤ j) (h : N ^ j < (j + 1) ^ (j + 1)) :
    (N + 1) ^ (j + 1) < (j + 1 + 1) ^ (j + 1 + 1) := by
  have hX := X_pow j hj
  have hY : Real.exp (((j : ℝ) + 1 + 1) * Real.log ((j : ℝ) + 1 + 1) / ((j : ℝ) + 1)) ^ (j + 1) =
      ((j : ℝ) + 1 + 1) ^ (j + 1 + 1) := by
    have := X_pow (j + 1) (by omega)
    rw [Nat.cast_succ] at this
    exact this
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hm := phi_mono (Set.mem_Ioi.mpr hj0) (Set.mem_Ioi.mpr (by linarith : (0 : ℝ) < (j : ℝ) + 1))
    (by linarith : (j : ℝ) ≤ (j : ℝ) + 1)
  have hm' : Real.exp (((j : ℝ) + 1) * Real.log ((j : ℝ) + 1) / (j : ℝ)) - (j : ℝ) ≤
      Real.exp (((j : ℝ) + 1 + 1) * Real.log ((j : ℝ) + 1 + 1) / ((j : ℝ) + 1)) - ((j : ℝ) + 1) := hm
  have hX0 : 0 ≤ Real.exp (((j : ℝ) + 1) * Real.log ((j : ℝ) + 1) / (j : ℝ)) :=
    le_of_lt (Real.exp_pos _)
  have hNX : (N : ℝ) < Real.exp (((j : ℝ) + 1) * Real.log ((j : ℝ) + 1) / (j : ℝ)) := by
    by_contra hc
    have h1 := pow_le_pow_left₀ hX0 (not_lt.mp hc) j
    rw [hX] at h1
    have h2 : (N : ℝ) ^ j < ((j : ℝ) + 1) ^ (j + 1) := by exact_mod_cast h
    linarith
  have h3 : ((N : ℝ) + 1) ^ (j + 1) <
      Real.exp (((j : ℝ) + 1 + 1) * Real.log ((j : ℝ) + 1 + 1) / ((j : ℝ) + 1)) ^ (j + 1) :=
    pow_lt_pow_left₀ (by linarith) (by positivity) (by omega)
  rw [hY] at h3
  exact_mod_cast h3

/-! ## Monotonicity of A381767 -/

theorem c_lt_succ (i : ℕ) : A381767 (i + 1) < A381767 (i + 1 + 1) := by
  rcases Nat.eq_zero_or_pos i with h0 | hi
  · subst h0
    show A381767 1 < A381767 2
    rw [c_one, lt_c_iff (le_refl 2)]
    norm_num
  · have h2 : 2 ≤ i + 1 := by omega
    have hc : 1 ≤ A381767 (i + 1) := c_pos h2
    have h1 : A381767 (i + 1) - 1 < A381767 (i + 1) := by omega
    rw [lt_c_iff h2, Nat.add_sub_cancel] at h1
    have h3 := core i (A381767 (i + 1) - 1) hi h1
    rw [Nat.sub_add_cancel hc] at h3
    rw [lt_c_iff (m := i + 1 + 1) (by omega), show i + 1 + 1 - 1 = i + 1 by omega]
    exact h3

theorem c_strictMono : StrictMono (fun i : ℕ => A381767 (i + 1)) :=
  strictMono_nat_of_lt_succ (fun i => c_lt_succ i)

theorem c_lt_c {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) : A381767 a < A381767 b := by
  have h : A381767 (a - 1 + 1) < A381767 (b - 1 + 1) := c_strictMono (show a - 1 < b - 1 by omega)
  rwa [Nat.sub_add_cancel ha, Nat.sub_add_cancel (by omega : 1 ≤ b)] at h

theorem c_le_c {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : A381767 a ≤ A381767 b := by
  rcases Nat.lt_or_eq_of_le hab with h | h
  · exact le_of_lt (c_lt_c ha h)
  · rw [h]

theorem c_ge {m : ℕ} (hm : 1 ≤ m) : m ≤ A381767 m := by
  induction m, hm using Nat.le_induction with
  | base => exact le_of_eq c_one.symm
  | succ m hm ih =>
    have := c_lt_c hm (show m < m + 1 by omega)
    omega

/-! ## Counting the complement -/

/-- The complement predicate of the statement. -/
def Pr (x : ℕ) : Prop := 0 < x ∧ ∀ m : ℕ, 1 ≤ m → A381767 m ≠ x

theorem A382131_eq (n : ℕ) : A382131 n = Nat.nth Pr (n - 1) := rfl

theorem not_Pr_c {m : ℕ} (hm : 1 ≤ m) : ¬ Pr (A381767 m) := by
  intro h
  unfold Pr at h
  exact h.2 m hm rfl

theorem Pr_between {m y : ℕ} (hm : 1 ≤ m) (h1 : A381767 m < y) (h2 : y < A381767 (m + 1)) :
    Pr y := by
  unfold Pr
  refine ⟨by omega, fun m' hm' he => ?_⟩
  rcases Nat.lt_or_ge m m' with h | h
  · have := c_le_c (by omega : 1 ≤ m + 1) (show m + 1 ≤ m' by omega)
    omega
  · have := c_le_c hm' h
    omega

theorem count_between_of [DecidablePred Pr] {m : ℕ} (hm : 1 ≤ m)
    (hA : Nat.count Pr (A381767 m + 1) = A381767 m - m) :
    ∀ j : ℕ, A381767 m + j < A381767 (m + 1) →
      Nat.count Pr (A381767 m + 1 + j) = A381767 m - m + j := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Nat.add_zero]
    exact hA
  | succ j ihj =>
    intro hj
    have hj' : A381767 m + j < A381767 (m + 1) := by omega
    have hP : Pr (A381767 m + 1 + j) := Pr_between hm (by omega) (by omega)
    rw [show A381767 m + 1 + (j + 1) = A381767 m + 1 + j + 1 by omega, Nat.count_succ, ihj hj',
      if_pos hP]
    omega

theorem count_c_succ [DecidablePred Pr] {m : ℕ} (hm : 1 ≤ m) :
    Nat.count Pr (A381767 m + 1) = A381767 m - m := by
  induction m, hm using Nat.le_induction with
  | base =>
    have hP0 : ¬ Pr 0 := by
      intro h
      unfold Pr at h
      exact lt_irrefl 0 h.1
    have hP1 : ¬ Pr 1 := by
      have := not_Pr_c (le_refl 1)
      rwa [c_one] at this
    rw [c_one, Nat.count_succ, if_neg hP1]
    have e1 := Nat.count_succ Pr 0
    rw [Nat.count_zero, if_neg hP0] at e1
    simpa using e1
  | succ m hm ih =>
    have hlt : A381767 m < A381767 (m + 1) := c_lt_c hm (show m < m + 1 by omega)
    have hge : m ≤ A381767 m := c_ge hm
    have h1 := count_between_of hm ih (A381767 (m + 1) - A381767 m - 1) (by omega)
    rw [show A381767 m + 1 + (A381767 (m + 1) - A381767 m - 1) = A381767 (m + 1) by omega] at h1
    rw [Nat.count_succ, h1, if_neg (not_Pr_c (m := m + 1) (by omega))]
    omega

theorem count_between [DecidablePred Pr] {m : ℕ} (hm : 1 ≤ m) (j : ℕ)
    (h : A381767 m + j < A381767 (m + 1)) :
    Nat.count Pr (A381767 m + 1 + j) = A381767 m - m + j :=
  count_between_of hm (count_c_succ hm) j h

/-! ## Existence of a positive `k` -/

theorem pow_lt_of_exp (k n : ℕ) (h : Real.exp ((n : ℝ) - 1) < (k : ℝ) + n) :
    (k + n) ^ k < (k + 1) ^ (k + 1) := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hkn : (0 : ℝ) < (k : ℝ) + n := lt_trans (Real.exp_pos _) h
  have hq : ((n : ℝ) - 1) / ((k : ℝ) + 1) + 1 = ((k : ℝ) + n) / ((k : ℝ) + 1) := by
    rw [div_add_one (ne_of_gt hk1)]
    ring
  have hexp := Real.add_one_le_exp (((n : ℝ) - 1) / ((k : ℝ) + 1))
  rw [hq] at hexp
  have hpow : (((k : ℝ) + n) / ((k : ℝ) + 1)) ^ (k + 1) ≤ Real.exp ((n : ℝ) - 1) := by
    have h1 := pow_le_pow_left₀ (le_of_lt (div_pos hkn hk1)) hexp (k + 1)
    rw [← Real.exp_nat_mul] at h1
    have h2 : ((k + 1 : ℕ) : ℝ) * (((n : ℝ) - 1) / ((k : ℝ) + 1)) = (n : ℝ) - 1 := by
      rw [Nat.cast_succ, mul_div_assoc', mul_div_cancel_left₀ _ (ne_of_gt hk1)]
    rw [h2] at h1
    exact h1
  have e : ((k : ℝ) + n) = ((k : ℝ) + 1) * (((k : ℝ) + n) / ((k : ℝ) + 1)) := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ (ne_of_gt hk1)]
  have h3 : ((k : ℝ) + n) ^ (k + 1) ≤ ((k : ℝ) + 1) ^ (k + 1) * Real.exp ((n : ℝ) - 1) := by
    calc ((k : ℝ) + n) ^ (k + 1)
        = ((k : ℝ) + 1) ^ (k + 1) * (((k : ℝ) + n) / ((k : ℝ) + 1)) ^ (k + 1) := by
          rw [← mul_pow, ← e]
      _ ≤ ((k : ℝ) + 1) ^ (k + 1) * Real.exp ((n : ℝ) - 1) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  have h4 : ((k : ℝ) + n) ^ k * ((k : ℝ) + n) < ((k : ℝ) + 1) ^ (k + 1) * ((k : ℝ) + n) := by
    rw [← pow_succ]
    calc ((k : ℝ) + n) ^ (k + 1) ≤ ((k : ℝ) + 1) ^ (k + 1) * Real.exp ((n : ℝ) - 1) := h3
      _ < ((k : ℝ) + 1) ^ (k + 1) * ((k : ℝ) + n) :=
          mul_lt_mul_of_pos_left h (by positivity)
  have h5 := lt_of_mul_lt_mul_right h4 (le_of_lt hkn)
  exact_mod_cast h5

theorem unbounded (n : ℕ) : ∃ k : ℕ, 0 < k ∧ (k + n) ^ k < (k + 1) ^ (k + 1) := by
  refine ⟨3 ^ n, by positivity, pow_lt_of_exp _ _ ?_⟩
  have h1 : Real.exp ((n : ℝ) - 1) < Real.exp (n : ℝ) := Real.exp_lt_exp.mpr (by linarith)
  have h2 : Real.exp (n : ℝ) = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul, mul_one]
  have h3 : Real.exp 1 ^ n ≤ (3 : ℝ) ^ n :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt Real.exp_one_lt_three) n
  have h4 : (((3 ^ n : ℕ) : ℝ)) = (3 : ℝ) ^ n := by norm_num
  rw [h4]
  have h5 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-! ## Assembly -/

/-- The set whose least element is `A387243 n`. -/
def Sset (n : ℕ) : Set ℕ := {k : ℕ | 0 < k ∧ (k + n) ^ k < (k + 1) ^ (k + 1)}

theorem A387243_eq (n : ℕ) : A387243 n = sInf (Sset n) := rfl

theorem mem_Sset {n k : ℕ} : k ∈ Sset n ↔ 0 < k ∧ (k + n) ^ k < (k + 1) ^ (k + 1) := Iff.rfl

theorem solve (n : ℕ) (hn : 1 ≤ n) : A387243 n = A382131 n - n := by
  classical
  have hne : (Sset n).Nonempty := by
    obtain ⟨k, hk⟩ := unbounded n
    exact ⟨k, mem_Sset.mpr hk⟩
  obtain ⟨K, hKdef⟩ : ∃ K, sInf (Sset n) = K := ⟨_, rfl⟩
  have hK : K ∈ Sset n := by
    rw [← hKdef]
    exact Nat.sInf_mem hne
  have hle : ∀ k, k ∈ Sset n → K ≤ k := by
    intro k hk
    rw [← hKdef]
    exact Nat.sInf_le hk
  obtain ⟨hK0, hK1⟩ := mem_Sset.mp hK
  have hup : K + n < A381767 (K + 1) := by
    rw [lt_c_iff (m := K + 1) (by omega), Nat.add_sub_cancel]
    exact hK1
  have hlow : A381767 K ≤ K + n - 1 := by
    rcases Nat.lt_or_ge K 2 with h | h
    · have hK1' : K = 1 := by omega
      rw [hK1', c_one]
      omega
    · by_contra hc
      have h1 : K - 1 + n < A381767 K := by omega
      rw [lt_c_iff h] at h1
      have hmem : K - 1 ∈ Sset n := by
        rw [mem_Sset]
        refine ⟨by omega, ?_⟩
        rw [show K - 1 + 1 = K by omega]
        exact h1
      have := hle (K - 1) hmem
      omega
  have hcK : K ≤ A381767 K := c_ge hK0
  have hP : Pr (K + n) := Pr_between hK0 (by omega) hup
  have hcount : Nat.count Pr (K + n) = n - 1 := by
    have h1 := count_between hK0 (K + n - 1 - A381767 K) (by omega)
    rw [show A381767 K + 1 + (K + n - 1 - A381767 K) = K + n by omega] at h1
    rw [h1]
    omega
  have hnth : Nat.nth Pr (n - 1) = K + n := by
    rw [← hcount]
    exact Nat.nth_count hP
  rw [A387243_eq, hKdef, A382131_eq, hnth]
  omega

end OMA.A387243Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a387243.main := by
  intro n hn
  exact OMA.A387243Proof.solve n hn
