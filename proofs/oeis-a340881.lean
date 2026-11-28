import OMAStatements.S_oeis_a340881
import Mathlib

namespace A340881

open OMA.S_oeis_a340881

private def triangle (n : ℕ) : ℕ := n * (n + 1) / 2

private theorem twice_triangle (n : ℕ) : 2 * triangle n = n * (n + 1) := by
  have hm : n * (n + 1) % 2 = 0 := by
    rw [Nat.mul_mod]
    by_cases he : n % 2 = 0
    · simp [he]
    · have ho : (n + 1) % 2 = 0 := by omega
      simp [ho]
  unfold triangle
  have h := Nat.mod_add_div (n * (n + 1)) 2
  omega

private theorem triangle_shift (n d : ℕ) :
    triangle (n + 2 * d) = triangle n + d * (2 * n + 2 * d + 1) := by
  have h : 2 * triangle (n + 2 * d) =
      2 * (triangle n + d * (2 * n + 2 * d + 1)) := by
    rw [twice_triangle (n + 2 * d), Nat.mul_add 2 (triangle n), twice_triangle n]
    ring
  omega

private theorem recurrence (n : ℕ) :
    a (n + 1) = a n * (2 ^ n - 1) + 2 ^ triangle n := by
  unfold a
  rw [Finset.sum_range_succ]
  congr 1
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.prod_Ico_succ_top (by
      have := Finset.mem_range.mp hk
      omega)]
    ring
  · simp [triangle]

private theorem cast_recurrence (p n : ℕ) :
    (a (n + 1) : ZMod p) = (a n : ZMod p) * (2 ^ n - 1) + 2 ^ triangle n := by
  have hpos : 1 ≤ (2 : ℕ) ^ n := by
    have : 0 < (2 : ℕ) ^ n := by positivity
    exact this
  push_cast [recurrence, Nat.cast_sub hpos]
  rfl

private theorem one : a 1 = 1 := by norm_num [a]

private theorem period (p : ℕ) (hp : p.Prime) :
    Function.Periodic (fun m : ℕ => a (m + 1) % p) (2 * (p - 1)) := by
  by_cases h₂ : p = 2
  · subst p
    have hc (n : ℕ) : (a (n + 1) : ZMod 2) = 1 := by
      induction n with
      | zero => simp [one]
      | succ n ih =>
          have ht : triangle (n + 1) ≠ 0 := by
            intro ht
            have he := twice_triangle (n + 1)
            rw [ht, mul_zero] at he
            have hpos : 0 < (n + 1) * (n + 1 + 1) := by positivity
            omega
          have hz : (2 : ZMod 2) = 0 := by decide
          rw [cast_recurrence, ih, hz, zero_pow (Nat.succ_ne_zero _), zero_pow ht]
          decide
    intro n
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp ((hc _).trans (hc _).symm)
  · let _ : Fact p.Prime := ⟨hp⟩
    have hnon : (2 : ZMod p) ≠ 0 := by
      intro hz
      have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
      exact h₂ ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hp.ne_one)
    have hf : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hnon
    let t := 2 * (p - 1)
    have hpow (i j : ℕ) : (2 : ZMod p) ^ (i + (p - 1) * j) = 2 ^ i := by
      rw [pow_add, pow_mul, hf, one_pow, mul_one]
    have hA (n : ℕ) : (2 : ZMod p) ^ (n + t) = 2 ^ n := by
      simpa only [t, Nat.mul_comm 2 (p - 1)] using hpow n 2
    have hB (n : ℕ) : (2 : ZMod p) ^ triangle (n + t) = 2 ^ triangle n := by
      change (2 : ZMod p) ^ triangle (n + 2 * (p - 1)) = _
      rw [triangle_shift]
      exact hpow _ _
    have hCast (n : ℕ) : (a (n + t + 1) : ZMod p) = (a (n + 1) : ZMod p) := by
      induction n with
      | zero =>
          simp only [zero_add, one, Nat.cast_one]
          have h0 : (2 : ZMod p) ^ t = 1 := by simpa using hA 0
          have h1 : (2 : ZMod p) ^ triangle t = 1 := by simpa [triangle] using hB 0
          rw [cast_recurrence, h0, h1, sub_self, mul_zero, zero_add]
      | succ n ih =>
          rw [cast_recurrence, cast_recurrence (n := n + 1), hA, hB]
          have hi : n + 1 + t = n + t + 1 := by omega
          rw [hi, ih]
    intro n
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp (hCast n)

end A340881

theorem OMA.solution : type_of% @OMA.S_oeis_a340881.main := by
  intro p hp
  let f (m : ℕ) := OMA.S_oeis_a340881.a (m + 1) % p
  let shift (g : ℕ → ℕ) (m : ℕ) := g (m + 1)
  have hshift (t m : ℕ) : (shift^[t] f) m = f (m + t) := by
    induction t generalizing m with
    | zero => simp
    | succ t ih =>
        rw [Function.iterate_succ_apply']
        change (shift^[t] f) (m + 1) = f (m + (t + 1))
        rw [ih]
        congr 1
        omega
  have hiff (t : ℕ) : Function.IsPeriodicPt shift t f ↔ Function.Periodic f t := by
    change (shift^[t] f = f) ↔ _
    constructor
    · intro h m
      rw [← hshift, h]
    · intro h
      funext m
      rw [hshift]
      exact h m
  have H := (hiff _).mpr (A340881.period p hp)
  exact ⟨Function.minimalPeriod shift f, H.minimalPeriod_pos (by have := hp.two_le; omega),
    (hiff _).mp (Function.isPeriodicPt_minimalPeriod shift f),
    fun U hU h => ((hiff U).mpr h).minimalPeriod_le hU, H.minimalPeriod_dvd⟩