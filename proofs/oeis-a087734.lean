import OMAStatements.S_oeis_a087734
import Mathlib

/-!
For m ≥ 1 and a bit b, size(2m + b) = size m + 1, hence f(2m + b) = 2 f(m) + (1 - b).
If f(m) ≥ 1, applying this twice gives a(2m + b) = 2 a(m) + b, and 2m + b + 1 is not a power of 2
(otherwise f(2m + b) = 0). If f(m) = 0, then m + 1 = 2^size(m), a(m) = 0 and a(2m + b) = 0; the
correction term is 1 exactly when b = 1, since 2m + 2 = 2^(size m + 1) while 2m + 1 is odd and > 1.
-/

namespace R087734
open OMA.S_oeis_a087734

theorem sz2 (m b : ℕ) (hm : 1 ≤ m) (hb : b ≤ 1) : Nat.size (2 * m + b) = Nat.size m + 1 := by
  have h1 := Nat.lt_size_self m
  have hs : 0 < Nat.size m := Nat.size_pos.mpr hm
  obtain ⟨s, hs'⟩ : ∃ s, Nat.size m = s + 1 := ⟨Nat.size m - 1, by omega⟩
  have h2 : 2 ^ s ≤ m := Nat.lt_size.mp (by omega)
  rw [hs'] at h1 ⊢
  have e1 : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
  have e2 : 2 ^ (s + 1 + 1) = 2 * 2 ^ (s + 1) := by ring
  apply le_antisymm
  · exact Nat.size_le.mpr (by omega)
  · exact Nat.succ_le_of_lt (Nat.lt_size.mpr (by omega))

theorem f_step (m b : ℕ) (hm : 1 ≤ m) (hb : b ≤ 1) : f (2 * m + b) = 2 * f m + (1 - b) := by
  unfold f
  rw [sz2 m b hm hb, pow_succ]
  have := Nat.lt_size_self m
  omega

theorem f_zero (m : ℕ) (h : f m = 0) : m + 1 = 2 ^ Nat.size m := by
  have := Nat.lt_size_self m
  unfold f at h
  omega

theorem f_eq_zero_of (n k : ℕ) (h : n + 1 = 2 ^ k) : f n = 0 := by
  have h1 := Nat.lt_size_self n
  have h2 : Nat.size n ≤ k := Nat.size_le.mpr (by omega)
  have h3 : 2 ^ Nat.size n ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h2
  unfold f
  omega

theorem fr_zero (n : ℕ) (h : ∀ k, n + 1 ≠ 2 ^ k) : fr n = 0 := by
  unfold fr
  exact if_neg (by rintro ⟨k, -, hk⟩; exact h k hk)

theorem fr_one (n k : ℕ) (hk : k < n + 2) (h : n + 1 = 2 ^ k) : fr n = 1 := by
  unfold fr
  exact if_pos ⟨k, hk, h⟩

theorem step (m b : ℕ) (hm : 1 ≤ m) (hb : b ≤ 1) :
    (a (2 * m + b) : ℤ) = 2 * (a m : ℤ) + ((b : ℕ) : ℤ) - (fr (2 * m + b) : ℤ) := by
  have hfn := f_step m b hm hb
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : f 1 = 0 := by simp [f]
  unfold a
  rw [hfn]
  rcases Nat.eq_zero_or_pos (f m) with hF | hF
  · have hm1 := f_zero m hF
    rw [hF, hf0]
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
    · have hfr : fr (2 * m + 0) = 0 := fr_zero _ (fun k hk => by
        rcases k with _ | k
        · rw [pow_zero] at hk
          omega
        · rw [pow_succ] at hk
          omega)
      rw [hfr]
      simp [hf1]
    · have hlt : Nat.size m + 1 < 2 ^ (Nat.size m + 1) := Nat.lt_two_pow_self
      have hfr : fr (2 * m + 1) = 1 :=
        fr_one (2 * m + 1) (Nat.size m + 1) (by rw [pow_succ] at hlt; omega)
          (by rw [pow_succ]; omega)
      rw [hfr]
      simp [hf0]
  · have hc := f_step (f m) (1 - b) hF (by omega)
    rw [hc, Nat.sub_sub_self hb]
    have hfr : fr (2 * m + b) = 0 := fr_zero _ (fun k hk => by
      have := f_eq_zero_of (2 * m + b) k hk
      rw [hfn] at this
      omega)
    rw [hfr]
    push_cast
    ring

end R087734

theorem OMA.solution : type_of% @OMA.S_oeis_a087734.main := by
  refine ⟨by simp [OMA.S_oeis_a087734.a, OMA.S_oeis_a087734.f],
    by simp [OMA.S_oeis_a087734.a, OMA.S_oeis_a087734.f], ?_⟩
  intro n hn
  have hd := Nat.div_add_mod n 2
  have := R087734.step (n / 2) (n % 2) (by omega) (by omega)
  rw [hd] at this
  exact this
