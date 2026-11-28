import OMAStatements.S_oeis_a023365
import Mathlib

namespace A023365
open OMA.S_oeis_a023365

lemma b_form (n : ℕ) : ∃ p : ℤ, Odd p ∧ b n = (p : ℚ) / (((2 : ℤ) ^ (3 ^ n) : ℤ) : ℚ) := by
  induction n with
  | zero =>
    refine ⟨1, by decide, ?_⟩
    simp [b]
  | succ n ih =>
    obtain ⟨p, hp, hb⟩ := ih
    have h3 : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
    obtain ⟨e, he⟩ : ∃ e, 3 ^ n = e + 1 := ⟨3 ^ n - 1, by omega⟩
    refine ⟨p * (6 * (2 ^ e) ^ 2 - p ^ 2), ?_, ?_⟩
    · apply Odd.mul hp
      have hp2 : Odd (p ^ 2) := hp.pow
      have h6 : Even (6 * ((2 : ℤ) ^ e) ^ 2) := ⟨3 * (2 ^ e) ^ 2, by ring⟩
      exact h6.sub_odd hp2
    · rw [b, hb]
      have hpow : (3 : ℕ) ^ (n + 1) = 3 * (e + 1) := by rw [pow_succ, he]; ring
      rw [hpow, he]
      push_cast
      have h2 : ((2 : ℚ) ^ e) ≠ 0 := by positivity
      field_simp
      ring

end A023365

theorem OMA.solution : type_of% @OMA.S_oeis_a023365.main := by
  intro n
  obtain ⟨p, hp, hb⟩ := A023365.b_form n
  have hc2 : Nat.Coprime p.natAbs 2 := Nat.coprime_two_right.mpr (Int.natAbs_odd.mpr hp)
  have hcop : Nat.Coprime p.natAbs ((2 : ℤ) ^ (3 ^ n)).natAbs := by
    rw [Int.natAbs_pow]
    exact Nat.Coprime.pow_right _ hc2
  have hden := Rat.den_div_eq_of_coprime (a := p) (b := (2 : ℤ) ^ (3 ^ n)) (by positivity) hcop
  rw [hb]
  unfold OMA.S_oeis_a023365.a
  rw [show n + 1 - 1 = n by omega]
  exact_mod_cast hden
