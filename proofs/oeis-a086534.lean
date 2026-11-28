import OMAStatements.S_oeis_a086534
import Mathlib

namespace A086534Disproof

theorem coprime_pred_self (k : ℕ) (h : 1 ≤ k) : Nat.Coprime (k - 1) k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp

theorem key (n : ℕ) : ∃ p : ℕ, p.Prime ∧ 2 ^ n ∣ p - 1 ∧ 3 ^ n ∣ p + 1 := by
  have hcop : Nat.Coprime (2 ^ n) (3 ^ n) := Nat.Coprime.pow n n (by norm_num)
  obtain ⟨r, hr1, hr2⟩ := Nat.chineseRemainder hcop 1 (3 ^ n - 1)
  have h3pos : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hc2 : Nat.Coprime r (2 ^ n) := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hr1]
    simp
  have hc3 : Nat.Coprime r (3 ^ n) := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hr2]
    exact coprime_pred_self (3 ^ n) h3pos
  have hc : Nat.Coprime r (2 ^ n * 3 ^ n) := Nat.Coprime.mul_right hc2 hc3
  have : NeZero (2 ^ n * 3 ^ n) := ⟨by positivity⟩
  have hu : IsUnit (r : ZMod (2 ^ n * 3 ^ n)) :=
    (ZMod.isUnit_iff_coprime r (2 ^ n * 3 ^ n)).mpr hc
  obtain ⟨p, hp1, hpp, hpr⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu 1
  have hmod : p ≡ r [MOD 2 ^ n * 3 ^ n] := (ZMod.natCast_eq_natCast_iff p r _).mp hpr
  have hm2 : p ≡ 1 [MOD 2 ^ n] := (Nat.ModEq.of_mul_right (3 ^ n) hmod).trans hr1
  have hm3 : p ≡ 3 ^ n - 1 [MOD 3 ^ n] := (Nat.ModEq.of_mul_left (2 ^ n) hmod).trans hr2
  refine ⟨p, hpp, ?_, ?_⟩
  · exact (Nat.modEq_iff_dvd' (by omega)).mp hm2.symm
  · have h1 : p + 1 ≡ 3 ^ n - 1 + 1 [MOD 3 ^ n] := Nat.ModEq.add_right 1 hm3
    rw [Nat.sub_add_cancel h3pos] at h1
    exact Nat.modEq_zero_iff_dvd.mp (h1.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl))

end A086534Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a086534.main) := by
  intro h
  have hsub : Set.Ici 1 ⊆ {n : ℕ | 1 ≤ n ∧ ∃ p : ℕ, OMA.S_oeis_a086534.Sandwiched n p} := by
    intro n hn
    obtain ⟨p, hpp, h2, h3⟩ := A086534Disproof.key n
    exact ⟨hn, p, hpp, ⟨2, le_refl _, h2⟩, ⟨3, by norm_num, h3⟩⟩
  exact ((Set.Ici_infinite 1).mono hsub) h
