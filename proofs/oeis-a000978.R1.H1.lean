import OMAReductions.R_oeis_a000978_R1
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Proof of `oeis-a000978.R1.H1`

Proves the forward direction of the Vrba–Reix test for Wagstaff primes: for every prime `p > 3`
such that `W = (2 ^ p + 1) / 3` is prime, `S W (p - 1) = S W 0` in `ZMod W`.

Proof outline:
1. Since `p > 3` is prime, `p` is odd, `p ≥ 5`, and `3 ∣ 2 ^ p + 1`, so `3 * W = 2 ^ p + 1`.
2. Reducing modulo `8` gives `W % 8 = 3` (hence `W % 4 = 3`), and reducing modulo `7` gives
   `W % 7 = 1 ∨ W % 7 = 4`.
3. Over the field `ZMod W`, `-1` and `2` are non-squares, so `-2` is a square (`a ^ 2 = -2`).
   By quadratic reciprocity with `7`, `legendreSym W 7 = -legendreSym 7 W = -1`, so `7` is a
   non-square; hence `14 = 7 * 2` is a square (`b ^ 2 = 14`).
4. Setting `β = (b + a) * (4 : ZMod W)⁻¹` gives `β * ((b - a) * (4 : ZMod W)⁻¹) = 1` (so `β ≠ 0`
   and `β⁻¹ = (b - a) * 4⁻¹`) and `β ^ 2 + β⁻¹ ^ 2 = 3 * 2⁻¹ = S W 0`.
5. Induction on `i` shows `S W i = β ^ (2 ^ (i + 1)) + β⁻¹ ^ (2 ^ (i + 1))`.
6. At `i = p - 1`, `2 ^ p = 3 * W - 1 = 3 * (W - 1) + 2`, so Fermat's little theorem yields
   `S W (p - 1) = β ^ 2 + β⁻¹ ^ 2 = S W 0`.
-/

namespace OeisA000978R1H1Proof

open OMA.S_oeis_a000978

private lemma S_eq_pow_add_inv_pow {m : ℕ} {β : ZMod m} (hβ : β * β⁻¹ = 1)
    (h0 : S m 0 = β ^ 2 + β⁻¹ ^ 2) :
    ∀ i : ℕ, S m i = β ^ (2 ^ (i + 1)) + β⁻¹ ^ (2 ^ (i + 1)) := by
  intro i
  induction i with
  | zero => simpa using h0
  | succ i ih =>
    unfold S
    rw [ih]
    have hmul : β ^ (2 ^ (i + 1)) * β⁻¹ ^ (2 ^ (i + 1)) = 1 := by
      rw [← mul_pow, hβ, one_pow]
    have hexp : 2 ^ (i + 1 + 1) = 2 ^ (i + 1) * 2 := by rw [pow_succ]
    rw [hexp, pow_mul, pow_mul]
    linear_combination 2 * hmul

private lemma three_mul_W {p : ℕ} (hp : Odd p) : 3 * W p = 2 ^ p + 1 := by
  unfold W
  have hdvd : 3 ∣ 2 ^ p + 1 := by
    obtain ⟨k, rfl⟩ := hp
    have hmod : 2 ^ (2 * k + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      have h4 : (2 ^ 2) % 3 = 1 := by decide
      rw [h4, one_pow]
      decide
    exact Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, hmod])
  exact Nat.mul_div_cancel' hdvd

private lemma isSquare_mul_of_not_isSquare {p : ℕ} [Fact p.Prime] {x y : ZMod p}
    (hx : x ≠ 0) (hy : y ≠ 0) (hnx : ¬ IsSquare x) (hny : ¬ IsSquare y) :
    IsSquare (x * y) := by
  have hlegx : legendreSym p x.val = -1 := by
    rw [legendreSym.eq_neg_one_iff]
    simpa [ZMod.natCast_zmod_val] using hnx
  have hlegy : legendreSym p y.val = -1 := by
    rw [legendreSym.eq_neg_one_iff]
    simpa [ZMod.natCast_zmod_val] using hny
  have hlegxy : legendreSym p ((x.val : ℤ) * (y.val : ℤ)) = 1 := by
    rw [legendreSym.mul, hlegx, hlegy]; norm_num
  have hxy : (((x.val : ℤ) * (y.val : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    simpa [ZMod.natCast_zmod_val] using mul_ne_zero hx hy
  have hsq := (legendreSym.eq_one_iff p hxy).mp hlegxy
  simpa [ZMod.natCast_zmod_val] using hsq

private lemma four_ne_zero_mod7 : ((4 : ℤ) : ZMod 7) ≠ 0 := by decide

end OeisA000978R1H1Proof

theorem OMA.solution : OMA.R_oeis_a000978_R1.H1 := by
  intro p hp hp3 hW
  have hp5 : 5 ≤ p := by
    have : p ≠ 4 := fun h => by subst h; exact absurd hp (by decide)
    omega
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  set m := OMA.S_oeis_a000978.W p
  have h3m : 3 * m = 2 ^ p + 1 := OeisA000978R1H1Proof.three_mul_W hp_odd
  have hm_ge11 : 11 ≤ m := by
    have h32 : 32 ≤ 2 ^ p := calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) hp5
    omega
  -- Congruence mod 8: 2^p % 8 = 0, so 3*m % 8 = 1, hence m % 8 = 3
  have hm8 : m % 8 = 3 := by
    have h8dvd : 8 ∣ 2 ^ p := by
      have : 2 ^ 3 ∣ 2 ^ p := Nat.pow_dvd_pow 2 (by omega)
      simpa using this
    have h2p8 : 2 ^ p % 8 = 0 := Nat.mod_eq_zero_of_dvd h8dvd
    omega
  -- Congruence mod 7: 3 ∤ p, so p % 3 ∈ {1, 2}, hence 2^p % 7 ∈ {2, 4}, hence m % 7 ∈ {1, 4}
  have hm7 : m % 7 = 1 ∨ m % 7 = 4 := by
    have hp3_ndvd : ¬ 3 ∣ p := by
      intro hd
      rcases (Nat.dvd_prime hp).mp hd with h1 | h2 <;> omega
    have hp_mod3 : p % 3 = 1 ∨ p % 3 = 2 := by omega
    have h2p_mod7 : 2 ^ p % 7 = 2 ∨ 2 ^ p % 7 = 4 := by
      have hsplit : 3 * (p / 3) + p % 3 = p := Nat.div_add_mod p 3
      rw [← hsplit, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
      have h8 : (2 ^ 3) % 7 = 1 := by decide
      rw [h8, one_pow]
      rcases hp_mod3 with h | h <;> rw [h]
      · left; decide
      · right; decide
    rcases h2p_mod7 with h | h <;> omega
  have : Fact m.Prime := ⟨hW⟩
  have hcast_ne0 : ∀ k : ℕ, 0 < k → k < m → (k : ZMod m) ≠ 0 := by
    intro k hk0 hkm h0
    have := Nat.le_of_dvd hk0 ((ZMod.natCast_eq_zero_iff k m).mp h0)
    omega
  -- Non-squares in ZMod m: -1, 2, and 7
  have hnot_neg1 : ¬ IsSquare (-1 : ZMod m) := by
    rw [ZMod.exists_sq_eq_neg_one_iff]
    omega
  have hnot_2 : ¬ IsSquare (2 : ZMod m) := by
    rw [ZMod.exists_sq_eq_two_iff (by omega : m ≠ 2)]
    omega
  have hnot_7 : ¬ IsSquare (7 : ZMod m) := by
    have : Fact (Nat.Prime 7) := ⟨by decide⟩
    have hqr := legendreSym.quadratic_reciprocity' (p := m) (q := 7) (by omega) (by decide)
    have hsign : (-1 : ℤ) ^ (m / 2 * (7 / 2)) = -1 := by
      have hodd_exp : Odd (m / 2 * (7 / 2)) := by
        refine ⟨6 * (m / 8) + 1, ?_⟩
        omega
      exact hodd_exp.neg_one_pow
    rw [hsign] at hqr
    have hleg7 : legendreSym 7 (m : ℤ) = 1 := by
      rw [legendreSym.mod 7 (m : ℤ)]
      have hm7Z : (m : ℤ) % 7 = 1 ∨ (m : ℤ) % 7 = 4 := by omega
      rw [Nat.cast_ofNat]
      rcases hm7Z with h | h
      · rw [h]; exact legendreSym.at_one 7
      · rw [h, legendreSym.eq_one_iff 7 OeisA000978R1H1Proof.four_ne_zero_mod7]
        exact ⟨2, by norm_num⟩
    have hlegm : legendreSym m (7 : ℤ) = -1 := by
      have : legendreSym m (7 : ℤ) = -legendreSym 7 (m : ℤ) := by
        simp only [Nat.cast_ofNat, neg_one_mul] at hqr; linarith
      rw [this, hleg7]
    have := (legendreSym.eq_neg_one_iff m).mp hlegm
    simpa using this
  -- Obtain a with a^2 = -2 and b with b^2 = 14 in ZMod m
  have hsq_neg2 : IsSquare (-2 : ZMod m) := by
    have h := OeisA000978R1H1Proof.isSquare_mul_of_not_isSquare
      (show (-1 : ZMod m) ≠ 0 by simp) (hcast_ne0 2 (by decide) (by omega)) hnot_neg1 hnot_2
    simpa using h
  have hsq_14 : IsSquare (14 : ZMod m) := by
    have h := OeisA000978R1H1Proof.isSquare_mul_of_not_isSquare
      (hcast_ne0 7 (by decide) (by omega)) (hcast_ne0 2 (by decide) (by omega)) hnot_7 hnot_2
    have h14 : ((7 : ℕ) : ZMod m) * ((2 : ℕ) : ZMod m) = (14 : ZMod m) := by norm_num
    rwa [h14] at h
  obtain ⟨a, ha⟩ := hsq_neg2
  obtain ⟨b, hb⟩ := hsq_14
  have ha2 : a ^ 2 = -2 := by rw [sq, ← ha]
  have hb2 : b ^ 2 = 14 := by rw [sq, ← hb]
  have h2ne0 : (2 : ZMod m) ≠ 0 := hcast_ne0 2 (by decide) (by omega)
  have h4ne0 : (4 : ZMod m) ≠ 0 := hcast_ne0 4 (by decide) (by omega)
  -- Construct β = (b + a) / 4 with β⁻¹ = (b - a) / 4 and β^2 + β⁻¹^2 = 3/2
  let β : ZMod m := (b + a) * (4 : ZMod m)⁻¹
  let γ : ZMod m := (b - a) * (4 : ZMod m)⁻¹
  have hβγ : β * γ = 1 := by
    dsimp [β, γ]
    have h16 : (4 : ZMod m) * (4 : ZMod m) = 16 := by norm_num
    have hnum : (b + a) * (b - a) = 16 := by linear_combination hb2 - ha2
    calc (b + a) * (4 : ZMod m)⁻¹ * ((b - a) * (4 : ZMod m)⁻¹)
        = ((b + a) * (b - a)) * ((4 : ZMod m) * (4 : ZMod m))⁻¹ := by rw [mul_inv]; ring
      _ = 16 * (16 : ZMod m)⁻¹ := by rw [hnum, h16]
      _ = 1 := mul_inv_cancel₀ (by rw [← h16]; exact mul_ne_zero h4ne0 h4ne0)
  have hβne0 : β ≠ 0 := fun h0 => by rw [h0, zero_mul] at hβγ; exact zero_ne_one hβγ
  have hγ_eq : β⁻¹ = γ := (eq_inv_of_mul_eq_one_right hβγ).symm
  have hβinv : β * β⁻¹ = 1 := mul_inv_cancel₀ hβne0
  have hS0 : OMA.S_oeis_a000978.S m 0 = β ^ 2 + β⁻¹ ^ 2 := by
    rw [OMA.S_oeis_a000978.S, hγ_eq]
    dsimp [β, γ]
    have h24 : (b + a) ^ 2 + (b - a) ^ 2 = 24 := by linear_combination 2 * hb2 + 2 * ha2
    have h16ne0 : (16 : ZMod m) ≠ 0 := by
      have h16 : (4 : ZMod m) * (4 : ZMod m) = 16 := by norm_num
      rw [← h16]; exact mul_ne_zero h4ne0 h4ne0
    have h4eq : (4 : ZMod m) = 2 * 2 := by norm_num
    field_simp [h2ne0, h4ne0]
    linear_combination -2 * h24
  rw [OeisA000978R1H1Proof.S_eq_pow_add_inv_pow hβinv hS0 (p - 1)]
  rw [show p - 1 + 1 = p by omega]
  have h2p_eq : 2 ^ p = (m - 1) * 3 + 2 := by omega
  have hβ_flt : β ^ (m - 1) = 1 := ZMod.pow_card_sub_one_eq_one hβne0
  have hβinv_flt : β⁻¹ ^ (m - 1) = 1 := ZMod.pow_card_sub_one_eq_one (inv_ne_zero hβne0)
  rw [h2p_eq, pow_add, pow_add, pow_mul, pow_mul, hβ_flt, hβinv_flt, one_pow, one_mul, one_mul]
  exact hS0.symm
