import OMAStatements.S_oeis_a156276
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
/-!
An original proof of the denominator recurrence for OEIS A156276.
Credit: @CubeJerry. Developed in this session with parallel Codex agents.

Set B(n) = 10^n E_n(1/10). The defining binomial recurrence makes B integral.
Its residue modulo 5 is 1. Modulo 8 it is 1-n for even n and 4 for odd n.
Thus the reduced denominator is 10^n for even n and 10^n/4 for odd n >= 3.
This implies the required recurrence, including its exact starting index.
-/


open scoped BigOperators

namespace OMA.A156276Residues

theorem residue_five (B : ℕ → ℤ)
    (hB : ∀ n, B n = 1 - 5 * ∑ k : Fin n,
      (n.choose k : ℤ) * 10 ^ (n - k - 1) * B k) (n : ℕ) :
    B n ≡ 1 [ZMOD 5] := by
  rw [hB n]
  simp [Int.ModEq, Int.sub_emod]

private theorem choose_two (n : ℕ) :
    2 * ((n + 3).choose 2 : ℤ) = (n + 3 : ℤ) * (n + 2) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (n + 3) 2
  norm_num [Nat.descFactorial_succ] at h
  have hh : 2 * ((n + 3).choose 2 : ℤ) = (n + 2 : ℤ) * (n + 3) := by
    exact_mod_cast h.symm
  simpa [mul_comm] using hh

private theorem choose_three (n : ℕ) :
    6 * ((n + 3).choose 3 : ℤ) = (n + 3 : ℤ) * (n + 2) * (n + 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (n + 3) 3
  have hn : n + 3 - 2 = n + 1 := by omega
  norm_num [Nat.descFactorial_succ, Nat.factorial, hn] at h
  have hh : 6 * ((n + 3).choose 3 : ℤ) = (n + 1 : ℤ) * ((n + 2) * (n + 3)) := by
    exact_mod_cast h.symm
  simpa [mul_comm, mul_left_comm, mul_assoc] using hh

theorem recurrence_eight (B : ℕ → ℤ)
    (hB : ∀ n, B n = 1 - 5 * ∑ k : Fin n,
      (n.choose k : ℤ) * 10 ^ (n - k - 1) * B k) (n : ℕ) :
    (3 : ZMod 8) * B (n + 3) = 3 -
      15 * (n + 3 : ZMod 8) * B (n + 2) -
      75 * (n + 3 : ZMod 8) * (n + 2) * B (n + 1) -
      250 * (n + 3 : ZMod 8) * (n + 2) * (n + 1) * B n := by
  have hr : (B (n + 3) : ZMod 8) = 1 - 5 * ∑ k : Fin (n + 3),
      ((n + 3).choose k : ZMod 8) * 10 ^ (n + 3 - k - 1) * B k := by
    have hh := congrArg (fun z : ℤ => (z : ZMod 8)) (hB (n + 3))
    push_cast at hh
    exact hh
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at hr
  have hzero : (∑ k : Fin n,
      ((n + 3).choose k : ZMod 8) * 10 ^ (n + 3 - k - 1) * B k) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have he : n + 3 - k - 1 = 3 + (n - k - 1) := by omega
    rw [he, pow_add]
    have hp : (10 : ZMod 8) ^ 3 = 0 := by decide
    rw [hp]
    simp
  have h2 : (2 : ZMod 8) * ((n + 3).choose 2 : ZMod 8) =
      (n + 3 : ZMod 8) * (n + 2) := by
    have hh := congrArg (fun z : ℤ => (z : ZMod 8)) (choose_two n)
    push_cast at hh
    exact hh
  have h3 : (6 : ZMod 8) * ((n + 3).choose 3 : ZMod 8) =
      (n + 3 : ZMod 8) * (n + 2) * (n + 1) := by
    have hh := congrArg (fun z : ℤ => (z : ZMod 8)) (choose_three n)
    push_cast at hh
    exact hh
  have hc1 : (n + 3).choose (n + 2) = n + 3 := by
    exact Nat.choose_succ_self_right (n + 2)
  have hc2 : (n + 3).choose (n + 1) = (n + 3).choose 2 := by
    rw [← Nat.choose_symm (by omega : n + 1 ≤ n + 3)]
    congr 1; omega
  have hc3 : (n + 3).choose n = (n + 3).choose 3 := by
    rw [← Nat.choose_symm (by omega : n ≤ n + 3)]
    congr 1; omega
  simp only [Fin.val_castSucc, Fin.val_last] at hr
  rw [hzero, hc1, hc2, hc3] at hr
  have e1 : n + 3 - (n + 2) - 1 = 0 := by omega
  have e2 : n + 3 - (n + 1) - 1 = 1 := by omega
  norm_num [e1, e2] at hr
  calc
    (3 : ZMod 8) * B (n + 3) = 3 -
        15 * (n + 3 : ZMod 8) * B (n + 2) -
        75 * (2 * ((n + 3).choose 2 : ZMod 8)) * B (n + 1) -
        250 * (6 * ((n + 3).choose 3 : ZMod 8)) * B n := by rw [hr]; ring
    _ = _ := by rw [h2, h3]; ring

private def residue (n : ℕ) : ZMod 8 := if n % 2 = 0 then 1 - n else 4

private theorem residue_recurrence (n : ℕ) :
    (3 : ZMod 8) * residue (n + 3) = 3 -
      15 * (n + 3 : ZMod 8) * residue (n + 2) -
      75 * (n + 3 : ZMod 8) * (n + 2) * residue (n + 1) -
      250 * (n + 3 : ZMod 8) * (n + 2) * (n + 1) * residue n := by
  have h0 : n % 2 = (n % 8) % 2 := by omega
  have h1 : (n + 1) % 2 = (n % 8 + 1) % 2 := by omega
  have h2 : (n + 2) % 2 = (n % 8 + 2) % 2 := by omega
  have h3 : (n + 3) % 2 = (n % 8 + 3) % 2 := by omega
  have hc : (n : ZMod 8) = ((n % 8 : ℕ) : ZMod 8) := (ZMod.natCast_mod n 8).symm
  unfold residue
  rw [h0, h1, h2, h3]
  push_cast
  rw [hc]
  have hb : n % 8 < 8 := Nat.mod_lt _ (by decide)
  interval_cases he : n % 8 <;> norm_num [he] <;> decide

private theorem cancel_three (x y : ZMod 8) (h : 3 * x = 3 * y) : x = y := by
  have hh := congrArg (fun z : ZMod 8 => 3 * z) h
  simpa only [← mul_assoc, show (3 : ZMod 8) * 3 = 1 from by decide, one_mul] using hh

theorem residue_eight (B : ℕ → ℤ)
    (hB : ∀ n, B n = 1 - 5 * ∑ k : Fin n,
      (n.choose k : ℤ) * 10 ^ (n - k - 1) * B k) (n : ℕ) :
    B n ≡ (if n % 2 = 0 then 1 - (n : ℤ) else 4) [ZMOD 8] := by
  have b0 : B 0 = 1 := by simpa using hB 0
  have b1 : B 1 = -4 := by simpa [Fin.sum_univ_succ, b0] using hB 1
  have b2 : B 2 = -9 := by
    simpa [Fin.sum_univ_succ, b0, b1, Nat.choose] using hB 2
  have hz : ∀ n, (B n : ZMod 8) = residue n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases h0 : n = 0
      · subst n; rw [b0]; rfl
      by_cases h1 : n = 1
      · subst n; rw [b1]; decide
      by_cases h2 : n = 2
      · subst n; rw [b2]; decide
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      apply cancel_three
      have hs := recurrence_eight B hB m
      rw [ih (m + 2) (by omega), ih (m + 1) (by omega), ih m (by omega)] at hs
      exact hs.trans (residue_recurrence m).symm
  apply (ZMod.intCast_eq_intCast_iff _ _ 8).mp
  simpa [residue] using hz n

end OMA.A156276Residues


namespace OMA.A156276Proof

lemma coprime_ten_of_remainders (B : ℤ) (h2 : B % 2 ≠ 0) (h5 : B % 5 ≠ 0) :
    Nat.Coprime B.natAbs 10 := by
  have htwo : Nat.Coprime 2 B.natAbs := Nat.prime_two.coprime_iff_not_dvd.mpr (by
    intro h
    have hz : (2 : ℤ) ∣ B := Int.natCast_dvd.mpr h
    exact h2 (Int.emod_eq_zero_of_dvd hz))
  have hfive : Nat.Coprime 5 B.natAbs := (by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr (by
    intro h
    have hz : (5 : ℤ) ∣ B := Int.natCast_dvd.mpr h
    exact h5 (Int.emod_eq_zero_of_dvd hz))
  simpa using (htwo.mul_left hfive).symm

lemma den_int_div_nat (B : ℤ) (D : ℕ) (hD : 0 < D)
    (hcop : Nat.Coprime B.natAbs D) : ((B : ℚ) / (D : ℚ)).den = D := by
  have h := Rat.den_div_eq_of_coprime (a := B) (b := (D : ℤ))
    (by exact_mod_cast hD) (by simpa using hcop)
  exact_mod_cast h

lemma denominator_from_residues (B : ℤ) (n : ℕ) (hn : 2 ≤ n)
    (h5 : B % 5 = 1)
    (h8 : B % 8 = if n % 2 = 0 then (1 - (n : ℤ)) % 8 else 4) :
    ((B : ℚ) / (10 : ℚ) ^ n).den = if n % 2 = 0 then 10 ^ n else 10 ^ n / 4 := by
  by_cases he : n % 2 = 0
  · rw [if_pos he] at h8 ⊢
    have h2 : B % 2 ≠ 0 := by omega
    have hc := (coprime_ten_of_remainders B h2 (by omega)).pow_right n
    simpa using den_int_div_nat B (10 ^ n) (by positivity) hc
  · rw [if_neg he] at h8 ⊢
    have hB : B = 4 * (B / 4) := by omega
    have h2 : (B / 4) % 2 ≠ 0 := by omega
    have hfive : (B / 4) % 5 ≠ 0 := by omega
    have hc := coprime_ten_of_remainders (B / 4) h2 hfive
    have hc5 : Nat.Coprime (B / 4).natAbs 5 := hc.coprime_dvd_right (by norm_num)
    have hcop : Nat.Coprime (B / 4).natAbs (25 * 10 ^ (n - 2)) := by
      apply Nat.Coprime.mul_right
      · simpa using hc5.pow_right 2
      · exact hc.pow_right (n - 2)
    have hpow : (10 : ℕ) ^ n = 4 * (25 * 10 ^ (n - 2)) := by
      calc
        (10 : ℕ) ^ n = 10 ^ ((n - 2) + 2) := by congr 1; omega
        _ = _ := by rw [pow_add]; ring
    have hrat : (B : ℚ) / (10 : ℚ) ^ n =
        ((B / 4 : ℤ) : ℚ) / (25 * 10 ^ (n - 2) : ℕ) := by
      have hbq : (B : ℚ) = 4 * ((B / 4 : ℤ) : ℚ) := by exact_mod_cast hB
      have hpq : (10 : ℚ) ^ n = 4 * (25 * (10 : ℚ) ^ (n - 2)) := by exact_mod_cast hpow
      rw [hbq, hpq]
      push_cast
      field_simp
    rw [hrat, den_int_div_nat (B / 4) (25 * 10 ^ (n - 2)) (by positivity) hcop,
      hpow]
    omega

lemma denominator_formula_step (n : ℕ) (hn : 2 ≤ n) :
    (if (n + 2) % 2 = 0 then 10 ^ (n + 2) else 10 ^ (n + 2) / 4) =
      100 * (if n % 2 = 0 then 10 ^ n else 10 ^ n / 4) := by
  have heq : (n + 2) % 2 = n % 2 := by omega
  have hp : (10 : ℕ) ^ (n + 2) = 100 * 10 ^ n := by rw [pow_add]; ring
  rw [heq, hp]
  split_ifs with he
  · rfl
  · have hfour : 4 ∣ (10 : ℕ) ^ n := by
      have hp' : (10 : ℕ) ^ n = 4 * (25 * 10 ^ (n - 2)) := by
        calc
          (10 : ℕ) ^ n = 10 ^ ((n - 2) + 2) := by congr 1; omega
          _ = _ := by rw [pow_add]; ring
      exact ⟨25 * 10 ^ (n - 2), hp'⟩
    have hmod : (10 : ℕ) ^ n % 4 = 0 := Nat.mod_eq_zero_of_dvd hfour
    omega

end OMA.A156276Proof

namespace OMA.A156276Proof
open OMA.S_oeis_a156276

def B : ℕ → ℤ
  | n => 1 - 5 * ∑ k : Fin n, (n.choose k : ℤ) * 10 ^ (n - k - 1) * B k
decreasing_by exact k.isLt

lemma B_scale (n : ℕ) : (B n : ℚ) = (10 : ℚ)^n * eulerAt (1/10) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [B, eulerAt]
    push_cast
    rw [mul_sub, ← mul_pow]
    norm_num
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [ih k k.isLt]
    have hp : (10 : ℚ)^n = (10 : ℚ)^(n-k-1) * (10 : ℚ)^(k : ℕ) * 10 := by
      rw [← pow_add, ← pow_succ]
      congr 1
      omega
    rw [hp]
    ring

end OMA.A156276Proof

namespace OMA.A156276Proof
open OMA.S_oeis_a156276

lemma euler_value (n : ℕ) : eulerAt (1/10) n = (B n : ℚ) / (10 : ℚ)^n := by
  apply (eq_div_iff (by positivity : (10 : ℚ)^n ≠ 0)).mpr
  simpa [mul_comm] using (B_scale n).symm

lemma a_formula (n : ℕ) (hn : 2 ≤ n) :
    a n = if n % 2 = 0 then 10^n else 10^n/4 := by
  have hB : ∀ n, B n = 1 - 5 * ∑ k : Fin n,
      (n.choose k : ℤ) * 10 ^ (n - k - 1) * B k := by
    intro n
    rw [B]
  have h5 := OMA.A156276Residues.residue_five B hB n
  have h8 := OMA.A156276Residues.residue_eight B hB n
  have hh5 : B n % 5 = 1 := by simpa [Int.ModEq] using h5
  have hh8 : B n % 8 = if n % 2 = 0 then (1 - (n : ℤ)) % 8 else 4 := by
    simpa only [Int.ModEq, apply_ite (fun z : ℤ => z % 8), show (4 : ℤ) % 8 = 4 from by decide] using h8
  unfold a
  rw [euler_value]
  exact denominator_from_residues (B n) n hn hh5 hh8

end OMA.A156276Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a156276.main := by
  intro n hn
  rw [OMA.A156276Proof.a_formula (n+2) (by omega), OMA.A156276Proof.a_formula n hn]
  exact OMA.A156276Proof.denominator_formula_step n hn
