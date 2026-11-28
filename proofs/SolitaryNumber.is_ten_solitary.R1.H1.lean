import OMAReductions.R_SolitaryNumber_is_ten_solitary_R1
import Mathlib

-- Step SolitaryNumber.is_ten_solitary.R1.H1: hypothesis H1 of reduction SolitaryNumber.is_ten_solitary.R1
-- Credit: @ivillar. 10 sigma(m) = 18 m forces 5 | m, so an even friend is m = 10 c; for c >= 2 the divisors d c (d | 10) together with 1 give sigma(10 c) > 18 c, contradicting sigma(m) = 18 c.

/-! Step SolitaryNumber.is_ten_solitary.R1.H1. -/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace P8Solitary

/-- A proper multiple has strictly larger abundancy: `σ(a) c < σ(a c)` for `c ≥ 2`. -/
lemma sigma_mul_lt (a c : ℕ) (ha : 0 < a) (hc : 2 ≤ c) : σ 1 a * c < σ 1 (a * c) := by
  rw [sigma_one_apply, sigma_one_apply, Finset.sum_mul]
  have hac : a * c ≠ 0 := by positivity
  have hinj : Set.InjOn (fun d => d * c) (a.divisors : Set ℕ) := by
    intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_right (by omega) hxy
  rw [← Finset.sum_image (f := fun x => x) hinj]
  apply Finset.sum_lt_sum_of_subset (i := 1)
  · exact Nat.one_mem_divisors.mpr hac
  · intro h1
    obtain ⟨d, _, hd1⟩ := Finset.mem_image.mp h1
    have := Nat.eq_one_of_mul_eq_one_left hd1
    omega
  · norm_num
  · intro j _ _
    exact Nat.zero_le j
  · intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hda, _⟩ := Nat.mem_divisors.mp hd
    exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_right hda c, hac⟩

lemma sigma_ten : σ 1 10 = 18 := by
  rw [sigma_one_apply]
  decide

theorem even_friend : ∀ m : ℕ, 0 < m → Even m → σ 1 m * 10 = 18 * m → m = 10 := by
  intro m hm hev h
  obtain ⟨k, hk⟩ := hev
  obtain ⟨c, rfl⟩ : ∃ c, m = 10 * c := ⟨m / 10, by omega⟩
  have hc : 1 ≤ c := by omega
  by_contra hne
  have hc2 : 2 ≤ c := by omega
  have := sigma_mul_lt 10 c (by norm_num) hc2
  rw [sigma_ten] at this
  omega

end P8Solitary

theorem OMA.solution : OMA.R_SolitaryNumber_is_ten_solitary_R1.H1 :=
  P8Solitary.even_friend
