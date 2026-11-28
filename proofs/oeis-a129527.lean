import OMAStatements.S_oeis_a129527
import Mathlib

/-!
# Proof of OEIS A129527 conjecture

Credit: @AkiRA-COM-FP
-/

open OMA.S_oeis_a129527

theorem OMA.solution : type_of% @OMA.S_oeis_a129527.main := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => omega
    | succ k =>
      rw [a]
      split_ifs with he
      · have hpart : oddPart ((k + 1) / 2) = oddPart (k + 1) :=
          Nat.ordCompl_div_of_dvd Nat.prime_two (Nat.dvd_of_mod_eq_zero he)
        have hle : oddPart ((k + 1) / 2) ≤ (k + 1) / 2 := Nat.ordCompl_le _ 2
        rw [ih ((k + 1) / 2) (by omega) (by omega), ← hpart]
        omega
      · have hd : ¬ 2 ∣ k + 1 := fun hd => he (Nat.mod_eq_zero_of_dvd hd)
        simp [oddPart, Nat.factorization_eq_zero_of_not_dvd hd]
        omega
