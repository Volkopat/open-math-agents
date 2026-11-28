import OMAStatements.S_oeis_a233419
import Mathlib

namespace A233419

open OMA.S_oeis_a233419

private theorem weight_step (n : ℕ) :
    weight n = n % 2 + weight (n / 2) := by
  by_cases h : n = 0
  · simp [h, weight]
  · unfold weight
    rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 2) h]
    rfl

private theorem weight_bit (u r : ℕ) (hr : r < 2) :
    weight (2 * u + r) = r + weight u := by
  rw [weight_step]
  have hm : (2 * u + r) % 2 = r := by omega
  have hd : (2 * u + r) / 2 = u := by omega
  rw [hm, hd]

private theorem weight_blocks (L u v : ℕ) (hu : u < 2 ^ L) :
    weight (u + 2 ^ L * v) = weight u + weight v := by
  induction L generalizing u with
  | zero =>
      have hz : u = 0 := by simpa using hu
      simp [hz, weight]
  | succ L ih =>
      have he : u + 2 ^ (L + 1) * v = u + 2 * (2 ^ L * v) := by rw [pow_succ]; ring
      have hm : (u + 2 ^ (L + 1) * v) % 2 = u % 2 := by rw [he]; omega
      have hd : (u + 2 ^ (L + 1) * v) / 2 = u / 2 + 2 ^ L * v := by rw [he]; omega
      have hsmall : u / 2 < 2 ^ L := by rw [pow_succ] at hu; omega
      rw [weight_step (u + 2 ^ (L + 1) * v), hm, hd, ih _ hsmall, weight_step u]
      omega

private theorem bound (L : ℕ) : L < 2 ^ L := by
  induction L with
  | zero => decide
  | succ L ih =>
      rw [pow_succ]
      omega

private theorem twice_odd_multiple (k : ℕ) (hk : ¬ 4 ∣ k) :
    ∃ h : ℕ, Odd h ∧ k ∣ 2 * h := by
  by_cases he : 2 ∣ k
  · obtain ⟨h, rfl⟩ := he
    exact ⟨h, Nat.odd_iff.mpr (by omega), dvd_rfl⟩
  · exact ⟨k, Nat.odd_iff.mpr (by omega), ⟨2, by omega⟩⟩

private theorem odd_square_mod (h : ℕ) (ho : Odd h) : h ^ 2 % 8 = 1 := by
  have hm := Nat.odd_iff.mp ho
  rw [pow_two, Nat.mul_mod h h 8]
  have hr : h % 8 = 1 ∨ h % 8 = 3 ∨ h % 8 = 5 ∨ h % 8 = 7 := by omega
  rcases hr with e | e | e | e <;> rw [e]

private theorem second_value (v : ℕ) (hv : weight v % 2 = 0) :
    secondOdious (2 * v + 2) = 2 * (4 * v + 1) := by
  have h₁ : weight (2 * v + 1) % 2 = 1 := by
    rw [weight_bit v 1 (by decide)]
    omega
  have h₂ : weight (4 * v + 1) % 2 = 1 := by
    rw [show 4 * v + 1 = 2 * (2 * v) + 1 by omega, weight_bit _ 1 (by decide),
      show 2 * v = 2 * v + 0 by omega, weight_bit v 0 (by decide)]
    omega
  have hfirst : odious (2 * v + 2) = 4 * v + 2 := by
    unfold odious
    rw [show 2 * v + 2 - 1 = 2 * v + 1 by omega, h₁]
    omega
  unfold secondOdious
  rw [hfirst]
  unfold odious
  rw [show 4 * v + 2 - 1 = 4 * v + 1 by omega, h₂]
  omega

end A233419

open A233419 OMA.S_oeis_a233419 in
theorem OMA.solution : type_of% @OMA.S_oeis_a233419.main := by
  intro k hk B
  obtain ⟨h, ho, hkh⟩ := twice_odd_multiple k hk
  have hh : 0 < h := by have := Nat.odd_iff.mp ho; omega
  let u := (9 * h ^ 2) / 8
  have hm : (9 * h ^ 2) % 8 = 1 := by
    rw [Nat.mul_mod, odd_square_mod h ho]
  have huEq : 8 * u + 1 = 9 * h ^ 2 := by
    have he := Nat.mod_add_div (9 * h ^ 2) 8
    rw [hm] at he
    dsimp [u]
    omega
  have huPos : 0 < u := by
    have hsq : 1 ≤ h ^ 2 := pow_pos hh 2
    omega
  let L := h.totient * (B + u + 1)
  have hL : B + u + 1 ≤ L := by
    have ht : 1 ≤ h.totient := Nat.totient_pos.mpr hh
    simpa [L] using Nat.mul_le_mul_right (B + u + 1) ht
  have hPow : (2 : ℕ) ^ L ≡ 1 [MOD h] := by
    have hBase : (2 : ℕ) ^ h.totient ≡ 1 [MOD h] := by
      by_cases hgt : 1 < h
      · change (2 : ℕ) ^ h.totient % h = 1 % h
        rw [Nat.pow_totient_mod_eq_one hgt ho.coprime_two_left, Nat.mod_eq_of_lt hgt]
      · have he : h = 1 := by omega
        simp [he, Nat.ModEq]
    simpa [L, pow_mul] using hBase.pow (B + u + 1)
  let v := u + 2 ^ L * u
  have hweight : weight v % 2 = 0 := by
    unfold v
    rw [weight_blocks L u u (by have := bound L; omega)]
    omega
  have hv : u + u ≡ v [MOD h] := by
    simpa only [one_mul] using (Nat.ModEq.refl u).add (hPow.mul_right u).symm
  have hdiv : h ∣ 4 * v + 1 := by
    have hh2 : h ∣ 9 * h ^ 2 := ⟨9 * h, by ring⟩
    apply (Nat.modEq_zero_iff_dvd).mp
    apply ((hv.mul_left 4).add_right 1).symm.trans
    rw [show 4 * (u + u) + 1 = 9 * h ^ 2 by omega]
    exact Nat.modEq_zero_iff_dvd.mpr hh2
  refine ⟨2 * v + 2, ?_, ?_⟩
  · have hmul := Nat.mul_le_mul_left (2 ^ L) (show 1 ≤ u from huPos)
    have hb := bound L
    dsimp [v]
    omega
  · rw [second_value v hweight]
    exact hkh.trans (Nat.mul_dvd_mul_left 2 hdiv)