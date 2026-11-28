import OMAStatements.S_oeis_a251421
import Mathlib

namespace OMA.A251421

open OMA.S_oeis_a251421 PowerSeries

private def balance (n : ℕ) (x y : Bool) : ℤ :=
  (completions n x y false : ℤ) - completions n x y true

private theorem balance_step (n : ℕ) (x y : Bool) :
    balance (n+1) x y =
      (if nonconstant x y false then -balance n y false else balance n y false) +
      (if nonconstant x y true then -balance n y true else balance n y true) := by
  cases x <;> cases y <;> simp [balance, completions, nonconstant] <;> ring

private theorem balance_even (t : ℕ) (x y : Bool) : balance (2*t) x y = 2^t := by
  induction t generalizing x y with
  | zero => norm_num [balance, completions]
  | succ t ih =>
    rw [show 2*(t+1) = (2*t+1)+1 by omega, balance_step]
    cases x <;> cases y <;> simp [balance_step, nonconstant, ih, pow_succ] <;> ring

private theorem balance_odd (t : ℕ) (x y : Bool) :
    balance (2*t+1) x y = if x = y then 0 else -2 * 2^t := by
  rw [balance_step]
  cases x <;> cases y <;> simp [nonconstant, balance_even] <;> ring

private theorem completions_total (n : ℕ) (x y : Bool) :
    (completions n x y false : ℤ) + completions n x y true = 2^n := by
  induction n generalizing x y with
  | zero => norm_num [completions]
  | succ n ih =>
    cases x <;> cases y <;> simp [completions, nonconstant, pow_succ] <;>
      linarith only [ih false false, ih false true, ih true false, ih true true]

private theorem count_balance (n : ℕ) :
    2 * (countedWords n : ℤ) = 4 * 2^n +
      (balance n false false + balance n false true + balance n true false + balance n true true) := by
  simp only [countedWords, Int.natCast_add, balance]
  linarith only [completions_total n false false, completions_total n false true,
    completions_total n true false, completions_total n true true]

private def correction (n : ℕ) : ℤ := if n % 2 = 0 then 2*2^(n/2) else -2*2^(n/2)

private theorem formula (n : ℕ) (hn : 0 < n) : (a n : ℤ) = 2 * 2^n + correction n := by
  have count := count_balance n
  rw [a, if_neg (Nat.ne_of_gt hn)]
  by_cases parity : n % 2 = 0
  · have hn' : n = 2*(n/2) := by omega
    have parts (x y : Bool) : balance n x y = 2^(n/2) :=
      (congrArg (fun j => balance j x y) hn').trans (balance_even (n/2) x y)
    simp only [correction, if_pos parity]
    simp only [parts] at count
    linarith only [count]
  · have hn' : n = 2*(n/2)+1 := by omega
    have parts (x y : Bool) : balance n x y = if x = y then 0 else -2*2^(n/2) :=
      (congrArg (fun j => balance j x y) hn').trans (balance_odd (n/2) x y)
    simp only [correction, if_neg parity]
    simp [parts] at count
    linarith only [count]

private theorem recurrence (n : ℕ) (hn : 0 < n) :
    (a (n+2) : ℤ) = 2 * a n + 4*2^n := by
  have parity : (n+2) % 2 = n % 2 := by omega
  have half : (n+2) / 2 = n/2+1 := by omega
  rw [formula (n+2) (by omega), formula n hn]
  simp only [correction, parity, half, pow_add, pow_one]
  split <;> norm_num <;> ring

private theorem generating :
    (1 - 2 * X) * (1 - 2 * X ^ 2) * mk (fun n => (a n : ℤ)) =
      2 * X * (1 + 4 * X - 8 * X ^ 2) := by
  let s : ℕ → ℤ := fun n => a n
  have lhs : (1 - 2 * X) * (1 - 2 * X ^ 2) * mk s =
      mk s - C (2 : ℤ) * (mk s * X^1) - C (2 : ℤ) * (mk s * X^2) +
        C (4 : ℤ) * (mk s * X^3) := by
    simp only [map_ofNat]
    ring
  have rhs : (2 : PowerSeries ℤ) * X * (1 + 4 * X - 8 * X ^ 2) =
      C (2 : ℤ) * X^1 + C (8 : ℤ) * X^2 - C (16 : ℤ) * X^3 := by
    simp only [map_ofNat]
    ring
  change (1 - 2 * X) * (1 - 2 * X ^ 2) * mk s = _
  rw [lhs, rhs]
  apply PowerSeries.ext
  intro n
  simp only [map_add, map_sub]
  rw [coeff_C_mul_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases h : n < 4
  · interval_cases n <;> norm_num [s, a, countedWords, completions, nonconstant]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m+4 := ⟨n-4, by omega⟩
    have first := recurrence (m+2) (by omega)
    have second := recurrence (m+1) (by omega)
    have powers : (2 : ℤ)^(m+2) = 2 * 2^(m+1) := by rw [pow_succ]; ring
    have index1 : m+4-1 = m+3 := by omega
    have index2 : m+4-2 = m+2 := by omega
    have index3 : m+4-3 = m+1 := by omega
    simp [s, show 1 ≤ m+4 by omega, show 2 ≤ m+4 by omega, show 3 ≤ m+4 by omega,
      show m+4 ≠ 1 by omega, show m+4 ≠ 2 by omega, show m+4 ≠ 3 by omega,
      index1, index2, index3]
    rw [show m+2+2 = m+4 by omega, powers] at first
    rw [show m+1+2 = m+3 by omega] at second
    linarith only [first, second]

end OMA.A251421

open OMA.S_oeis_a251421 in
theorem OMA.solution : type_of% @OMA.S_oeis_a251421.main := by
  refine ⟨OMA.A251421.generating, ?_, ?_⟩
  · intro n hn parity
    have h := OMA.A251421.formula n hn
    simp only [OMA.A251421.correction, if_pos parity] at h
    have h' : (a n : ℤ) = 2 * ((2 : ℤ)^(n/2) + 2^n) := by linarith only [h]
    exact_mod_cast h'
  · intro n hn parity
    have h := OMA.A251421.formula n hn
    simp only [OMA.A251421.correction, if_neg (show n % 2 ≠ 0 by omega)] at h
    have le : (2 : ℕ)^(n/2) ≤ 2^n := Nat.pow_le_pow_right (by decide) (by omega)
    have h' : (a n : ℤ) = (2 : ℤ) * ((2 : ℤ)^n - 2^(n/2)) := by linarith only [h]
    exact_mod_cast h'