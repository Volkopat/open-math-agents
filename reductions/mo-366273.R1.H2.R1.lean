import OMAReductions.R_mo_366273_R1

namespace OMA.R_mo_366273_R1_H2_R1

open OMA.S_mo_366273

def H1 : Prop :=
  ∀ n : ℤ, Even n → ∃ z t d : ℤ,
    t % 3 = 1 ∧ 108 * (n - g z) + 16 = t * (t ^ 2 - 12 + 27 * d ^ 2)

def H2 : Prop :=
  ∀ a z d : ℤ, Odd d → ∃ x y w : ℤ,
    g z + (6 * a + 4) * d ^ 2 + 4 * (2 * a + 1) * (4 * a + 3) ^ 2 =
      g x + g y + g w

lemma residue_check (s d : ZMod 8)
    (h : (3 * s - 2) * ((3 * s - 2) ^ 2 - 12 + 27 * d ^ 2) = 0) :
    (s - d = 0 ∨ s - d = 2 ∨ s - d = 4 ∨ s - d = 6) ∨
      (s = 6 ∧ (d = 1 ∨ d = 3 ∨ d = 5 ∨ d = 7)) := by
  revert s d
  decide +kernel

lemma parity_or_exception (s d : ℤ)
    (h : ((3 * (s : ZMod 8) - 2) *
      ((3 * (s : ZMod 8) - 2) ^ 2 - 12 + 27 * (d : ZMod 8) ^ 2)) = 0) :
    Even (s - d) ∨ (s % 8 = 6 ∧ Odd d) := by
  have ht := residue_check (s : ZMod 8) (d : ZMod 8) h
  have cast_res (a b : ℤ) (e : (a : ZMod 8) = (b : ZMod 8)) : a % 8 = b % 8 :=
    (ZMod.intCast_eq_intCast_iff' a b 8).mp e
  rcases ht with hp | ⟨hs, hd⟩
  · left
    rw [Int.even_iff]
    rcases hp with hp | hp | hp | hp
    · have hh := cast_res (s - d) 0 (by simpa only [Int.cast_sub, Int.cast_zero] using hp)
      norm_num at hh
      omega
    · have hh := cast_res (s - d) 2 (by simpa only [Int.cast_sub, Int.cast_ofNat] using hp)
      norm_num at hh
      omega
    · have hh := cast_res (s - d) 4 (by simpa only [Int.cast_sub, Int.cast_ofNat] using hp)
      norm_num at hh
      omega
    · have hh := cast_res (s - d) 6 (by simpa only [Int.cast_sub, Int.cast_ofNat] using hp)
      norm_num at hh
      omega
  · right
    constructor
    · exact cast_res s 6 hs
    · rw [Int.odd_iff]
      rcases hd with hd | hd | hd | hd
      · have hh := cast_res d 1 (by simpa only [Int.cast_one] using hd)
        norm_num at hh
        omega
      · have hh := cast_res d 3 (by simpa only [Int.cast_ofNat] using hd)
        norm_num at hh
        omega
      · have hh := cast_res d 5 (by simpa only [Int.cast_ofNat] using hd)
        norm_num at hh
        omega
      · have hh := cast_res d 7 (by simpa only [Int.cast_ofNat] using hd)
        norm_num at hh
        omega

theorem main : H1 → H2 → OMA.R_mo_366273_R1.H2 := by
  intro hrel hfamily n hn _
  obtain ⟨z, t, d, htmod, heq⟩ := hrel n hn
  let s := (t + 2) / 3
  have ht : t = 3 * s - 2 := by dsimp [s]; omega
  have hg : Even (g z) := by
    simpa only [g, pow_two, mul_assoc] using (Int.even_mul_pred_self z).mul_left z
  obtain ⟨k, hk⟩ := hn.sub hg
  have hdiv : (8 : ℤ) ∣ t * (t ^ 2 - 12 + 27 * d ^ 2) := by
    rw [← heq, hk]
    exact ⟨27 * k + 2, by ring⟩
  have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr hdiv
  rw [ht] at hc
  push_cast at hc
  rcases parity_or_exception s d hc with hpar | ⟨hs, hd⟩
  · exact ⟨z, t, d, htmod, hpar, heq⟩
  · let a := (s - 6) / 8
    have hsa : s = 8 * a + 6 := by dsimp [a]; omega
    have ht' : t = 24 * a + 16 := by omega
    have hn' : n = g z + (6 * a + 4) * d ^ 2 +
        4 * (2 * a + 1) * (4 * a + 3) ^ 2 := by
      rw [ht'] at heq
      nlinarith only [heq]
    obtain ⟨x, y, w, hw⟩ := hfamily a z d hd
    have hrep : n = g x + g y + g w := hn'.trans hw
    obtain ⟨u, v, hu, hv, he⟩ := OMA.R_mo_366273_R1.necessary_certificate hrep
    exact ⟨w, u, v, hu, hv, he⟩

end OMA.R_mo_366273_R1_H2_R1
