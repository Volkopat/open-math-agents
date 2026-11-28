import OMAStatements.S_oeis_a127804
import Mathlib

namespace OMA.CyclicPatterns127804

open OMA.S_oeis_a127804
open ArithmeticFunction Finset

private abbrev Z := (ArithmeticFunction.zeta : ArithmeticFunction ℤ)

private theorem odd_apply (f : ArithmeticFunction ℤ) (n : ℕ) :
    oddTerms f n = if Odd n then f n else 0 := rfl

private theorem odd_mul (f g : ArithmeticFunction ℤ) :
    oddTerms (f * g) = oddTerms f * oddTerms g := by
  ext n
  rw [odd_apply, mul_apply, mul_apply]
  split_ifs with hn
  · apply sum_congr rfl
    rintro ⟨a,b⟩ hab
    have h := (Nat.mem_divisorsAntidiagonal.mp hab).1
    change a*b = n at h
    rw [← h, Nat.odd_mul] at hn
    simp [odd_apply,hn.1,hn.2]
  · symm
    apply sum_eq_zero
    rintro ⟨a,b⟩ hab
    have h := (Nat.mem_divisorsAntidiagonal.mp hab).1
    change a*b = n at h
    rw [← h, Nat.odd_mul] at hn
    by_cases ha : Odd a
    · have hb : ¬ Odd b := fun hb => hn ⟨ha,hb⟩
      simp [odd_apply,hb]
    · simp [odd_apply,ha]

private theorem odd_one : oddTerms 1 = 1 := by
  ext n
  by_cases hn : n=1 <;> simp [odd_apply,one_apply,hn]

private def delta : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 2 then 1 else 0, by simp⟩

private theorem delta_apply (f : ArithmeticFunction ℤ) (n : ℕ) :
    (delta * f) n = if 2 ∣ n then f (n/2) else 0 := by
  rw [mul_apply]
  by_cases hz : n = 0
  · simp [hz]
  by_cases hn : 2 ∣ n
  · rw [if_pos hn, sum_eq_single (2,n/2)]
    · simp [delta]
    · rintro ⟨a,b⟩ hab hne
      have h := (Nat.mem_divisorsAntidiagonal.mp hab).1
      change a*b=n at h
      have ha : a ≠ 2 := by
        rintro rfl
        apply hne
        congr 1
        omega
      simp [delta,ha]
    · intro h
      exfalso
      apply h
      exact Nat.mem_divisorsAntidiagonal.mpr ⟨by dsimp; omega,hz⟩
  · rw [if_neg hn]
    apply sum_eq_zero
    rintro ⟨a,b⟩ hab
    have h := (Nat.mem_divisorsAntidiagonal.mp hab).1
    change a*b=n at h
    have ha : a ≠ 2 := by rintro rfl; exact hn ⟨b,h.symm⟩
    simp [delta,ha]

private theorem diff_apply (f g : ArithmeticFunction ℤ) (n : ℕ) :
    (f-g) n = f n - g n := rfl

private theorem odd_zeta : (1-delta)*Z = oddTerms Z := by
  ext n
  rw [sub_mul,one_mul,diff_apply,delta_apply,odd_apply]
  by_cases hz : n=0
  · simp [hz]
  by_cases h : 2 ∣ n
  · have hn : ¬ Odd n := by rw [Nat.odd_iff]; omega
    have hhalf : n/2 ≠ 0 := by omega
    simp [h,hn,ArithmeticFunction.natCoe_apply,zeta_apply_ne hz,zeta_apply_ne hhalf]
  · have hn : Odd n := by rw [Nat.odd_iff]; omega
    simp [h,hn]

private abbrev patterns := Z * (oddTerms moebius * binaryWords)

private theorem recurrence (n : ℕ) :
    patterns n - (if 2 ∣ n then patterns (n/2) else 0) = binaryWords n := by
  have inv : oddTerms Z * oddTerms moebius = 1 := by
    rw [← odd_mul, coe_zeta_mul_moebius, odd_one]
  have h : (1-delta)*patterns = binaryWords := by
    unfold patterns
    rw [← mul_assoc, odd_zeta, ← mul_assoc, inv, one_mul]
  have eq := congrArg (fun f : ArithmeticFunction ℤ => f n) h
  simpa only [sub_mul, one_mul, diff_apply, delta_apply] using eq

private theorem counts (n : ℕ) : dyadicValue n = patterns (n+1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have e := recurrence (n+1)
    have base : binaryWords (n+1) = (2:ℤ)^n := by simp [binaryWords]
    rw [base] at e
    rw [dyadicValue]
    split_ifs with oddN
    · have h : 2 ∣ n+1 := by omega
      have shift : (n+1)/2 = n/2+1 := by omega
      rw [if_pos h,shift] at e
      rw [ih (n/2) (by omega)]
      omega
    · have h : ¬ 2 ∣ n+1 := by omega
      rw [if_neg h,sub_zero] at e
      simpa using e.symm

theorem result (n : ℕ) : dyadicValue n = 1 + cyclicPatternCount (n+1) := by
  rw [counts]
  unfold patterns cyclicPatternCount
  rw [coe_zeta_mul_apply]
  omega

end OMA.CyclicPatterns127804

theorem OMA.solution : type_of% @OMA.S_oeis_a127804.main :=
  OMA.CyclicPatterns127804.result
