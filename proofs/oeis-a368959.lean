import OMAStatements.S_oeis_a368959
import Mathlib

-- Problem: OEIS A368959, Conjecture 1 of Kotesovec: if Sum_{k=0..m-1} exp(2 Pi i k^s / m) is
-- not zero for each s >= 2, then m is a powerful number (p | m implies p^2 | m).
-- Statement: statements/oeis-a368959.lean (declaration OMA.S_oeis_a368959.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Assume that a prime p divides m = p n but p^2 does not, so p does not divide n.
-- Take s = p. In Z/m, (x + n)^p = x^p + n^p, because each middle term of the binomial
-- expansion has a factor binomial(p, j) n^(p-j) with 0 < j < p, which is a multiple of p n.
-- Let e be the standard additive character of Z/m and S = Sum_x e(x^p). The shift x -> x + n
-- gives S = e(n^p) S. But n^p is not zero in Z/m (else p | n^(p-1), so p | n), and e is
-- injective, so e(n^p) is not 1. Thus S = 0, a contradiction.

namespace OMA.A368959

open OMA.S_oeis_a368959

/-- The exponential sum is a sum of the standard additive character over ZMod m. -/
lemma sum_eq (m : ℕ) [NeZero m] (s : ℕ) :
    ∑ k ∈ Finset.range m, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) ^ s / (m : ℂ))
    = ∑ x : ZMod m, ZMod.stdAddChar (x ^ s) := by
  have h1 : ∀ k : ℕ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) ^ s / (m : ℂ))
      = ZMod.stdAddChar (((k : ZMod m)) ^ s) := by
    intro k
    have := ZMod.stdAddChar_coe (N := m) ((k : ℤ) ^ s)
    push_cast at this
    rw [this]
  simp_rw [h1]
  refine Finset.sum_nbij' (fun k => (k : ZMod m)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intro k _; exact Finset.mem_univ _
  · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro k hk; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hk)
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro k _; rfl

/-- In ZMod (p n), (x + n)^p = x^p + n^p. -/
lemma add_pow_eq (q n : ℕ) (hp : (q + 1).Prime) (x : ZMod ((q + 1) * n)) :
    (x + (n : ZMod ((q + 1) * n))) ^ (q + 1) = x ^ (q + 1) + (n : ZMod ((q + 1) * n)) ^ (q + 1) := by
  rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
  have hz : ∑ j ∈ Finset.range q, x ^ (j + 1) * (n : ZMod ((q + 1) * n)) ^ (q + 1 - (j + 1))
      * (((q + 1).choose (j + 1) : ℕ) : ZMod ((q + 1) * n)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hd : (q + 1) * n ∣ n ^ (q + 1 - (j + 1)) * (q + 1).choose (j + 1) := by
      rw [mul_comm (q + 1) n]
      exact mul_dvd_mul (dvd_pow_self n (by omega)) (hp.dvd_choose_self (by omega) (by omega))
    have : ((n : ZMod ((q + 1) * n)) ^ (q + 1 - (j + 1))
        * (((q + 1).choose (j + 1) : ℕ) : ZMod ((q + 1) * n))) = 0 := by
      have := (ZMod.natCast_eq_zero_iff _ _).mpr hd
      push_cast at this
      rw [show q + 1 - (j + 1) = q - j by omega]
      exact this
    rw [mul_assoc, this, mul_zero]
  rw [hz]
  simp
  ring

theorem main' (m : ℕ) (hm : 1 ≤ m)
    (h : ∀ s : ℕ, 2 ≤ s →
      ∑ k ∈ Finset.range m,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) ^ s / (m : ℂ)) ≠ 0) :
    ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m := by
  intro p hp hpm
  by_contra hnot
  obtain ⟨n, rfl⟩ := hpm
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · omega
    · exact h0
  have hpn : ¬ (q + 1) ∣ n := by
    intro hd
    apply hnot
    rw [pow_two]
    exact mul_dvd_mul_left _ hd
  have : NeZero ((q + 1) * n) := ⟨by positivity⟩
  apply h (q + 1) hp.two_le
  rw [sum_eq]
  set S := ∑ x : ZMod ((q + 1) * n), ZMod.stdAddChar (x ^ (q + 1)) with hS
  have hshift : S = ZMod.stdAddChar ((n : ZMod ((q + 1) * n)) ^ (q + 1)) * S := by
    rw [hS, Finset.mul_sum]
    rw [← Fintype.sum_equiv (Equiv.addRight (n : ZMod ((q + 1) * n)))
      (fun x => ZMod.stdAddChar ((x + (n : ZMod ((q + 1) * n))) ^ (q + 1)))
      (fun x => ZMod.stdAddChar (x ^ (q + 1))) (fun x => rfl)]
    apply Finset.sum_congr rfl
    intro x _
    rw [add_pow_eq q n hp, AddChar.map_add_eq_mul, mul_comm]
  have hne : ZMod.stdAddChar ((n : ZMod ((q + 1) * n)) ^ (q + 1)) ≠ 1 := by
    intro h1
    rw [← (ZMod.stdAddChar (N := (q + 1) * n)).map_zero_eq_one,
      ZMod.injective_stdAddChar.eq_iff] at h1
    have h2 : (((n ^ (q + 1) : ℕ)) : ZMod ((q + 1) * n)) = 0 := by push_cast; exact h1
    rw [ZMod.natCast_eq_zero_iff, pow_succ, mul_comm (q + 1) n] at h2
    have h3 : (q + 1) ∣ n ^ q := (Nat.mul_dvd_mul_iff_left hn).mp (by rwa [mul_comm (n ^ q) n] at h2)
    exact hpn (hp.dvd_of_dvd_pow h3)
  have : (1 - ZMod.stdAddChar ((n : ZMod ((q + 1) * n)) ^ (q + 1))) * S = 0 := by
    rw [sub_mul, one_mul, ← hshift, sub_self]
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm hne
  · exact h0

end OMA.A368959

theorem OMA.solution : type_of% @OMA.S_oeis_a368959.main :=
  fun m hm h => OMA.A368959.main' m hm h
