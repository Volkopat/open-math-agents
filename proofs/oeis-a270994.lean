import OMAStatements.S_oeis_a270994
import Mathlib

-- T. Adamczewski, OEIS Open (arXiv:2608.11941), Appendix A: at n = 162178349052694 the number
-- a(n) + 4 = 1813934020268071832273 is itself a Sierpinski number, strictly between a(n) and a(n) + 28.
-- Covering set modulo 96 (recomputed here): {3, 5, 7, 17, 97, 257, 673}, all dividing 2^96 - 1; for every
-- residue r < 96 one of them divides K * 2^r + 1.

namespace OMA.P20A270994

def K : ℕ := 1813934020268071832273

lemma cover : ∀ r < 96, ∃ p ∈ [3, 5, 7, 17, 97, 257, 673], 2 ^ 96 % p = 1 ∧ (K * 2 ^ r + 1) % p = 0 := by
  decide +kernel

lemma sierp : OMA.S_oeis_a270994.IsSierpinski K := by
  refine ⟨Nat.odd_iff.mpr (by norm_num [K]), ?_⟩
  intro m hm hpr
  obtain ⟨p, hp, h96, hdiv⟩ := cover (m % 96) (Nat.mod_lt _ (by norm_num))
  have hp' : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 17 ∨ p = 97 ∨ p = 257 ∨ p = 673 := by
    simpa using hp
  have hpp : p.Prime := by
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hp673 : p ≤ 673 := by
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hp1 : 1 < p := hpp.one_lt
  have hmod : 2 ^ 96 ≡ 1 [MOD p] := by
    unfold Nat.ModEq
    rw [h96, Nat.mod_eq_of_lt hp1]
  have h2m : 2 ^ m = (2 ^ 96) ^ (m / 96) * 2 ^ (m % 96) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have hcong : K * 2 ^ m + 1 ≡ K * 2 ^ (m % 96) + 1 [MOD p] := by
    rw [h2m]
    have h1 := (hmod.pow (m / 96)).mul_right (2 ^ (m % 96))
    rw [one_pow, one_mul] at h1
    have h2 := (h1.mul_left K).add_right 1
    rw [← mul_assoc] at h2
    rw [← mul_assoc]
    exact h2
  have hdvd : p ∣ K * 2 ^ m + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    unfold Nat.ModEq at hcong
    rw [hcong, hdiv]
  have heq := (Nat.Prime.eq_one_or_self_of_dvd hpr p hdvd).resolve_left (by omega)
  have hle : K ≤ K * 2 ^ m := Nat.le_mul_of_pos_right K (by positivity)
  have hK : 673 < K := by norm_num [K]
  generalize K * 2 ^ m = t at heq hle
  omega

end OMA.P20A270994

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a270994.main) := by
  intro h
  have h3 := (h 162178349052694).2.2 OMA.P20A270994.K
    (by norm_num [OMA.S_oeis_a270994.a, OMA.P20A270994.K])
    (by norm_num [OMA.S_oeis_a270994.a, OMA.P20A270994.K])
  exact h3 OMA.P20A270994.sierp
