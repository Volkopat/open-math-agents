import OMAReductions.R_BealConjecture_beal_conjecture_R1_H1_R1_H3_R1
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-! The signed primitive form and the fourth-power test in Manvir Jaswal,
Theorem 6.15, https://manvirjaswal.github.io/papers/x5-y3-zp/jaswal-x5y3zp.pdf.
The two inputs are the divisibility step in the CM case and the final local
comparison for that case. The prime range and sign changes are checked here. -/

namespace OMA.R_BealConjecture_beal_conjecture_R1_H1_R1_H3_R1_H3_R1

private def primitive (X Y Z : ℤ) : Prop :=
  X.natAbs.Coprime Y.natAbs ∧ X.natAbs.Coprime Z.natAbs ∧ Y.natAbs.Coprime Z.natAbs

private def signedCase (p : ℕ) (X Y Z : ℤ) : Prop :=
  p.Prime ∧ 109 < p ∧ X ≠ 0 ∧ Y ≠ 0 ∧ Z ≠ 0 ∧ primitive X Y Z ∧
  X ^ 5 + Y ^ 3 = Z ^ p ∧ (5 : ℤ) ∣ X ∧ ¬ (5 : ℤ) ∣ Y ∧ ¬ (5 : ℤ) ∣ Z

private theorem coprime_other_bases {a b c p : ℕ} (hp : 0 < p) (hab : a.Coprime b)
    (he : a ^ 5 + b ^ p = c ^ 3) : a.Coprime c ∧ b.Coprime c := by
  have hNo {q : ℕ} (hq : q.Prime) (ha : q ∣ a) (hb : q ∣ b) : False :=
    (Nat.Prime.not_coprime_iff_dvd.mpr ⟨q, hq, ha, hb⟩) hab
  constructor
  · apply Nat.coprime_of_dvd
    intro q hq ha hc
    have hA : q ∣ a ^ 5 := dvd_pow ha (by decide)
    have hC : q ∣ a ^ 5 + b ^ p := by rw [he]; exact dvd_pow hc (by decide)
    have hB := (Nat.dvd_add_right hA).mp hC
    exact hNo hq ha (hq.dvd_of_dvd_pow hB)
  · apply Nat.coprime_of_dvd
    intro q hq hb hc
    have hB : q ∣ b ^ p := dvd_pow hb hp.ne'
    have hC : q ∣ a ^ 5 + b ^ p := by rw [he]; exact dvd_pow hc (by decide)
    have hA := (Nat.dvd_add_left hB).mp hC
    exact hNo hq (hq.dvd_of_dvd_pow hA) hb

private theorem fourth_power_table : ∀ r : Fin 25,
    r.val ∈ [6, 8, 9, 12, 13, 16, 17, 19] ↔
      r.val ^ 4 % 25 = 11 ∨ r.val ^ 4 % 25 = 21 := by decide

/-- The local analysis in the proof of Theorem 6.15 forces six to divide the
fifth-power base in the fourth-power classes of type ((1,1)) at five. -/
def H1 : Prop := ∀ (p : ℕ) (X Y Z : ℤ), signedCase p X Y Z →
  Y ^ 4 % 25 = 11 ∨ Y ^ 4 % 25 = 21 → (6 : ℤ) ∣ X

/-- The level-two CM comparison and local-type mismatch for the branch with
six dividing the fifth-power base. -/
def H2 : Prop := ∀ (p : ℕ) (X Y Z : ℤ), signedCase p X Y Z → (6 : ℤ) ∣ X →
  Y ^ 4 % 25 = 11 ∨ Y ^ 4 % 25 = 21 → False

theorem main : H1 → H2 → OMA.R_BealConjecture_beal_conjecture_R1_H1_R1_H3_R1.H3 := by
  intro hCM hType a b c p ha hb hc hab hp hlarge _ _ _ _ _ he h5 hbad
  obtain ⟨hac, hbc⟩ := coprime_other_bases hp.pos hab he
  have h5b : ¬ 5 ∣ b := fun hb' => (Nat.Prime.not_coprime_iff_dvd.mpr
    ⟨5, by decide, h5, hb'⟩) hab
  have h5c : ¬ 5 ∣ c := fun hc' => (Nat.Prime.not_coprime_iff_dvd.mpr
    ⟨5, by decide, h5, hc'⟩) hac
  have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
  have heZ : (a : ℤ) ^ 5 + (-(c : ℤ)) ^ 3 = (-(b : ℤ)) ^ p := by
    have hcast : (a : ℤ) ^ 5 + (b : ℤ) ^ p = (c : ℤ) ^ 3 := by exact_mod_cast he
    rw [hpOdd.neg_pow, show (-(c : ℤ)) ^ 3 = -(c : ℤ) ^ 3 by ring]
    linarith
  have hCase : signedCase p (a : ℤ) (-(c : ℤ)) (-(b : ℤ)) := by
    refine ⟨hp, hlarge, by exact_mod_cast ha.ne', by exact_mod_cast (neg_ne_zero.mpr
      (show (c : ℤ) ≠ 0 by exact_mod_cast hc.ne')), by exact_mod_cast (neg_ne_zero.mpr
      (show (b : ℤ) ≠ 0 by exact_mod_cast hb.ne')), ?_, heZ, ?_, ?_, ?_⟩
    · simpa [primitive] using And.intro hac (And.intro hab hbc.symm)
    · exact_mod_cast h5
    · simpa using (show ¬ (5 : ℤ) ∣ (c : ℤ) by exact_mod_cast h5c)
    · simpa using (show ¬ (5 : ℤ) ∣ (b : ℤ) by exact_mod_cast h5b)
  have hfourth := (fourth_power_table ⟨c % 25, Nat.mod_lt _ (by decide)⟩).mp hbad
  change (c % 25) ^ 4 % 25 = 11 ∨ (c % 25) ^ 4 % 25 = 21 at hfourth
  rw [← Nat.pow_mod] at hfourth
  have hfourthZ : (-(c : ℤ)) ^ 4 % 25 = 11 ∨ (-(c : ℤ)) ^ 4 % 25 = 21 := by
    rw [show (-(c : ℤ)) ^ 4 = (c : ℤ) ^ 4 by ring]
    rcases hfourth with h | h
    · left
      exact_mod_cast h
    · right
      exact_mod_cast h
  have h6 := hCM p (a : ℤ) (-(c : ℤ)) (-(b : ℤ)) hCase hfourthZ
  exact hType p (a : ℤ) (-(c : ℤ)) (-(b : ℤ)) hCase h6 hfourthZ

end OMA.R_BealConjecture_beal_conjecture_R1_H1_R1_H3_R1_H3_R1
