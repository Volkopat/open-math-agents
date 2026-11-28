import OMAStatements.S_oeis_a182381
import Mathlib

namespace OMA.A182381

open OMA.S_oeis_a182381

theorem key (C p g : ℕ) (hp : p.Prime) (hC : IsCarmichael C) (hpC : p ∣ C) (hg : Nat.Coprime g p) :
    ((g : ZMod p)) ^ (C - 1) = 1 := by
  obtain ⟨h1, -, hF⟩ := hC
  have hC0 : C ≠ 0 := by omega
  have ha : C.factorization p ≠ 0 := (hp.factorization_pos_of_dvd hC0 hpC).ne'
  have hco : Nat.Coprime (p ^ C.factorization p) (C / p ^ C.factorization p) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hC0)
  have hmul : p ^ C.factorization p * (C / p ^ C.factorization p) = C :=
    Nat.ordProj_mul_ordCompl_eq_self C p
  obtain ⟨b, hb1, hb2⟩ := Nat.chineseRemainder hco g 1
  have hbp : b ≡ g [MOD p] := hb1.of_dvd (dvd_pow_self p ha)
  have hbC : Nat.Coprime b C := by
    rw [← hmul]
    apply Nat.Coprime.mul_right
    · apply Nat.Coprime.pow_right
      have := hbp.gcd_eq
      unfold Nat.Coprime
      rw [this]; exact hg
    · have := hb2.gcd_eq
      unfold Nat.Coprime
      rw [this]; exact Nat.gcd_one_left _
  have h2 : b ^ (C - 1) ≡ 1 [MOD p] := (hF b hbC).of_dvd hpC
  have h3 := (ZMod.natCast_eq_natCast_iff _ _ p).mpr h2
  have h4 := (ZMod.natCast_eq_natCast_iff _ _ p).mpr hbp
  push_cast at h3
  rw [← h4]; exact h3

theorem d17 : ∀ r : Fin 16, (3 : ZMod 17) ^ (r : ℕ) = 1 → r = 0 := by decide +kernel

theorem d29 : ∀ r : Fin 28, (2 : ZMod 29) ^ (r : ℕ) = 1 → r = 0 := by decide +kernel

end OMA.A182381

theorem OMA.solution : type_of% @OMA.S_oeis_a182381.main := by
  intro C hC h17 h29
  have h1 : 1 < C := hC.1
  have k17 := OMA.A182381.key C 17 3 (by norm_num) hC h17 (by norm_num)
  have k29 := OMA.A182381.key C 29 2 (by norm_num) hC h29 (by norm_num)
  have e17 : (C - 1) % 16 = 0 := by
    have hd := Nat.div_add_mod (C - 1) 16
    rw [← hd, pow_add, pow_mul] at k17
    have h16 : ((3 : ℕ) : ZMod 17) ^ 16 = 1 := by decide +kernel
    rw [h16, one_pow, one_mul] at k17
    have := OMA.A182381.d17 ⟨(C - 1) % 16, Nat.mod_lt _ (by norm_num)⟩ (by simpa using k17)
    simpa [Fin.ext_iff] using this
  have e29 : (C - 1) % 28 = 0 := by
    have hd := Nat.div_add_mod (C - 1) 28
    rw [← hd, pow_add, pow_mul] at k29
    have h28 : ((2 : ℕ) : ZMod 29) ^ 28 = 1 := by decide +kernel
    rw [h28, one_pow, one_mul] at k29
    have := OMA.A182381.d29 ⟨(C - 1) % 28, Nat.mod_lt _ (by norm_num)⟩ (by simpa using k29)
    simpa [Fin.ext_iff] using this
  exact ⟨C / 952, by omega⟩
