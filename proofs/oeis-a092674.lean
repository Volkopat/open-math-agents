import OMAStatements.S_oeis_a092674
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
Successive differences turn the floor-weighted sums into ordinary
divisor sums. The deviation from the totient has divisor sum −1 at
one, +1 at two, and zero elsewhere. Möbius inversion gives the exact
constant term, with at most two corrections of absolute value one.
-/

open Finset Polynomial ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open OMA.S_oeis_a092674

namespace ConstantTerms

noncomputable def term (n : ℕ) : ℤ := (polynomial n).eval 0

lemma at_zero : term 0 = 0 := by simp [term, polynomial]
lemma at_one : term 1 = 0 := by simp [term, polynomial]

lemma recursion (k : ℕ) : term (k+2) = (((k+3).choose 2 : ℕ) : ℤ) -
    ∑ i ∈ range (k+2), term i * (((k+2)/i : ℕ) : ℤ) := by
  unfold term
  rw [polynomial]
  simp only [eval_sub, eval_C, eval_finsetSum, eval_mul]
  congr 1
  let f := fun i : ℕ => eval 0 (polynomial i) * (((k+2)/i : ℕ):ℤ)
  change (∑ i : Fin (k+2), f i.val) = ∑ i ∈ range (k+2), f i
  exact Fin.sum_univ_eq_sum_range _ _

def weighted (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ range (n+1), f i * ((n/i : ℕ) : ℤ)

lemma increment (f : ℕ → ℤ) (n : ℕ) :
    weighted f (n+1) = weighted f n + ∑ i ∈ (n+1).divisors, f i := by
  have extend : ∑ i ∈ range (n+1+1), f i*((n/i : ℕ):ℤ) = weighted f n := by
    rw [Finset.sum_range_succ, Nat.div_eq_of_lt (Nat.lt_succ_self n)]
    simp [weighted]
  have step (i : ℕ) : f i * (((n+1)/i : ℕ) : ℤ) =
      f i * ((n/i : ℕ) : ℤ) + if i ∣ n+1 then f i else 0 := by
    by_cases h : i ∣ n+1
    · simp [h, Nat.succ_div_of_dvd, mul_add]
    · simp [h, Nat.succ_div_of_not_dvd]
  unfold weighted
  simp_rw [step]
  rw [Finset.sum_add_distrib, extend, ← Finset.sum_filter, Nat.filter_dvd_eq_divisors (by omega)]
  rfl

lemma total (n : ℕ) : weighted term n = (((n+1).choose 2 : ℕ) : ℤ) -
    (if n=1 then 1 else 0) := by
  match n with
  | 0 => simp [weighted, at_zero]
  | 1 => norm_num [weighted, Finset.sum_range_succ, at_zero, at_one]
  | k+2 =>
    unfold weighted
    rw [Finset.sum_range_succ, Nat.div_self (by omega), recursion]
    simp

def pulse (n : ℕ) : ℤ := (if n=2 then 1 else 0) - (if n=1 then 1 else 0)

lemma divisor_total (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, term d = (n:ℤ) + pulse n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h := increment term k
  rw [total, total] at h
  have hchoose : (((k+2).choose 2 : ℕ) : ℤ) =
      (k+1:ℕ) + (((k+1).choose 2 : ℕ):ℤ) := by
    rw [Nat.choose_succ_succ]
    simp
  unfold pulse
  rw [show k+1+1=k+2 by omega, hchoose] at h
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at *
  split_ifs at * <;> omega

lemma exact_term (n : ℕ) (hn : 0 < n) :
    term n = (n.totient : ℤ) - μ n + (if 2 ∣ n then μ (n/2) else 0) := by
  have hsum : ∀ m > 0, ∑ i ∈ m.divisors, (term i - (i.totient:ℤ)) = pulse m := by
    intro m hm
    rw [Finset.sum_sub_distrib, divisor_total m hm]
    have hφ : ∑ i ∈ m.divisors, (i.totient : ℤ) = m := by exact_mod_cast Nat.sum_totient m
    rw [hφ]
    ring
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hsum) n hn
  simp only [Int.cast_id] at h
  rw [Nat.sum_divisorsAntidiagonal' (fun x y => (μ x:ℤ) * pulse y)] at h
  simp only [pulse, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib] at h
  simp [Nat.mem_divisors, hn.ne'] at h
  omega

end ConstantTerms

open ConstantTerms

theorem OMA.solution : type_of% @OMA.S_oeis_a092674.main := by
  intro n hn
  rw [Polynomial.coeff_zero_eq_eval_zero]
  change 0 ≤ term n
  have h := exact_term n hn
  by_cases hsmall : n ≤ 2
  · interval_cases n
    · simp [at_one]
    · norm_num [recursion, at_zero, at_one, Finset.sum_range_succ]
  have hφ : 2 ≤ n.totient := by
    have hp := Nat.totient_pos.mpr hn
    have he := Nat.totient_even (show 2 < n by omega)
    obtain ⟨z, hz⟩ := he
    omega
  have hμ := abs_le.mp (ArithmeticFunction.abs_moebius_le_one (n := n))
  have hμ' := abs_le.mp (ArithmeticFunction.abs_moebius_le_one (n := n/2))
  split_ifs at h <;> omega
