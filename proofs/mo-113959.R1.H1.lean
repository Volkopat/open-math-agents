import OMAReductions.R_mo_113959_R1
import Mathlib

/-! Write `n - 2 = 2^k u` with `u` odd. On an even `m = 2 + 2^(i+1) 3^j u` the least prime factor
is 2, so `f m = m + m/2 - 1 = 2 + 2^i 3^(j+1) u`; iterating `k` times gives the closed form, the
iterates before step `k` are even, and `2 + 3^k u` is odd. -/

open OMA.S_mo_113959

theorem OMA.solution : OMA.R_mo_113959_R1.H1 := by
  intro n hn
  obtain ⟨k, u, hu, hku⟩ := Nat.exists_eq_two_pow_mul_odd (n := n - 2) (by omega)
  have step : ∀ i j, f (2 + 2 ^ (i + 1) * 3 ^ j * u) = 2 + 2 ^ i * 3 ^ (j + 1) * u := by
    intro i j
    have e1 : 2 + 2 ^ (i + 1) * 3 ^ j * u = 2 * (1 + 2 ^ i * 3 ^ j * u) := by ring
    have e2 : 2 ^ i * 3 ^ (j + 1) * u = 3 * (2 ^ i * 3 ^ j * u) := by ring
    unfold f
    rw [e1, (Nat.minFac_eq_two_iff _).mpr (dvd_mul_right 2 _), Nat.mul_div_cancel_left _ two_pos, e2]
    omega
  have form : ∀ j ≤ k, f^[j] n = 2 + 2 ^ (k - j) * 3 ^ j * u := by
    intro j
    induction j with
    | zero => intro _; simp; omega
    | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply', ih (by omega),
        show k - j = (k - (j + 1)) + 1 by omega, step]
  refine ⟨k, u, hu, by omega, form, fun j hj => ?_, ?_⟩
  · rw [form j hj.le]
    have : k - j ≠ 0 := by omega
    simp [Nat.even_add, Nat.even_mul, Nat.even_pow, this]
  · rw [form k le_rfl, Nat.sub_self, pow_zero, one_mul]
    have h3 : Odd (3 ^ k) := Odd.pow (by decide)
    exact Even.add_odd even_two (h3.mul hu)
