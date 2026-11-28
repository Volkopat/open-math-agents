import OMAStatements.S_oeis_a034444
import Mathlib.Data.Nat.Factorization.Basic

-- Problem: A034444 (Ianakiev's conjecture): the odd unitary divisor power sum divides the full one.
-- Credit: @alan-phobos-claude (#10386); shorter proof by @PandaWill (#29856).
-- Replace the remaining strong induction for the odd-part decomposition with Mathlib's API.
-- Proof: write n = 2^a * m with m odd. The odd unitary divisors of n are exactly the unitary divisors
--   of m, and (for a > 0) the even ones are exactly 2^a times those. So the full sum is
--   (1 + 2^(a*k)) times the odd one.

open OMA.S_oeis_a034444 Finset

lemma U {N d : ℕ} (h : N ≠ 0) : d ∈ unitary N ↔ ∃ c, N = d * c ∧ d.Coprime c := by
  simp only [unitary, mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨⟨c, rfl⟩, -⟩, h'⟩
    exact ⟨c, rfl, by rwa [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (left_ne_zero_of_mul h))] at h'⟩
  · rintro ⟨c, rfl, h'⟩
    exact ⟨⟨dvd_mul_right _ _, h⟩, by rwa [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (left_ne_zero_of_mul h))]⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a034444.main := by
  intro n hn k
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hN := hn.ne'
  have hM : m ≠ 0 := by rintro rfl; simp at hN
  have O {d c} (h : m = d * c) : Odd d := (Nat.odd_mul.1 (h ▸ hm)).1
  have C {x} : Odd x → Nat.Coprime 2 x := Nat.coprime_two_left.2
  -- the odd unitary divisors of `2^a * m` are the unitary divisors of `m`
  have E : (unitary (2 ^ a * m)).filter Odd = unitary m := by
    ext d; rw [mem_filter, U hN, U hM]; constructor
    · rintro ⟨⟨c, hc, h⟩, hd⟩
      obtain ⟨c, rfl⟩ := ((C hd).pow_left a).dvd_of_dvd_mul_left ⟨m, hc.symm⟩
      exact ⟨c, Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos a) (by rw [hc, mul_left_comm]),
        h.coprime_dvd_right (dvd_mul_left _ _)⟩
    · rintro ⟨c, rfl, h⟩
      exact ⟨⟨2 ^ a * c, by rw [mul_left_comm], Nat.coprime_mul_iff_right.2 ⟨((C (O rfl)).pow_left a).symm, h⟩⟩, O rfl⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [E]; simp
  -- for `a > 0` the even ones are `2^a` times those, so the full sum is `(1 + 2^(a*k))` times the odd one
  have F : (unitary (2 ^ a * m)).filter (¬ Odd ·) = (unitary m).image (2 ^ a * ·) := by
    ext d; rw [mem_filter, mem_image, U hN]; constructor
    · rintro ⟨⟨c, hc, h⟩, hd⟩
      have : Odd c := Nat.coprime_two_left.1 (h.coprime_dvd_left (even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hd)))
      obtain ⟨e, rfl⟩ := ((C this).pow_left a).dvd_of_dvd_mul_right ⟨m, hc.symm⟩
      have hmc : m = e * c := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos a) (by rw [hc, mul_assoc])
      exact ⟨e, (U hM).2 ⟨c, hmc, h.coprime_dvd_left (dvd_mul_left _ _)⟩, rfl⟩
    · rintro ⟨e, he, rfl⟩
      obtain ⟨c, rfl, h⟩ := (U hM).1 he
      exact ⟨⟨c, by rw [mul_assoc], Nat.coprime_mul_iff_left.2 ⟨(C (O (mul_comm _ _))).pow_left a, h⟩⟩,
        Nat.not_odd_iff_even.2 ((Nat.even_pow.2 ⟨even_two, ha.ne'⟩).mul_right _)⟩
  rw [← sum_filter_add_sum_filter_not (unitary (2 ^ a * m)) Odd, E, F, sum_image (mul_right_injective₀ (by simp)).injOn]
  simp only [mul_pow]
  exact dvd_add dvd_rfl (Dvd.intro_left _ (map_sum (AddMonoidHom.mulLeft ((2 ^ a) ^ k)) (· ^ k) _))
