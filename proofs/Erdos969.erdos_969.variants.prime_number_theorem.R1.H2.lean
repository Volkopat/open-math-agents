import OMAReductions.R_Erdos969_erdos_969_variants_prime_number_theorem_R1
import Mathlib.Data.Nat.Factorization.Root

open Finset
/-! Adapted from the Möbius indicator in the checked proof of Erdős 121.
Only square divisors with square root at most √x can contribute. -/
open ArithmeticFunction Finset
open scoped Moebius
private theorem mobius_indicator (n N : ℕ) (hn : 0 < n) (hN : n ≤ N) :
    (if Squarefree n then (1 : ℤ) else 0) =
      ∑ d ∈ Ioc 0 N, if d ^ 2 ∣ n then (μ d : ℤ) else 0 := by
  classical
  let r := Nat.floorRoot 2 n
  have hr : 0 < r := Nat.pos_of_ne_zero (Nat.floorRoot_ne_zero.mpr ⟨by decide, hn.ne'⟩)
  have hrdvd : r ^ 2 ∣ n := Nat.floorRoot_pow_dvd
  have hrle : r ≤ n := (le_self_pow (n := 2) (by omega : 1 ≤ r) (by decide)).trans
    (Nat.le_of_dvd hn hrdvd)
  have hfree : Squarefree n ↔ r = 1 := by
    constructor
    · intro h
      exact Nat.isUnit_iff.mp (h r (by simpa only [pow_two] using hrdvd))
    · intro he d hd
      have hd' : d ∣ r := Nat.pow_dvd_iff_dvd_floorRoot.mp (by simpa only [pow_two] using hd)
      rw [he] at hd'
      exact Nat.isUnit_iff.mpr (Nat.dvd_one.mp hd')
  have hfilter : (Ioc 0 N).filter (fun d => d ^ 2 ∣ n) = r.divisors := by
    ext d
    simp only [mem_filter, mem_Ioc, Nat.mem_divisors, Nat.pow_dvd_iff_dvd_floorRoot]
    change (0 < d ∧ d ≤ N) ∧ d ∣ r ↔ d ∣ r ∧ r ≠ 0
    constructor
    · exact fun hd => ⟨hd.2, hr.ne'⟩
    · intro hd
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd.1 hr, (Nat.le_of_dvd hr hd.1).trans (hrle.trans hN)⟩, hd.1⟩
  have hif : (if Squarefree n then (1 : ℤ) else 0) = (if r = 1 then 1 else 0) := by
    by_cases he : r = 1
    · simp [he, hfree.mpr he]
    · have hf : ¬Squarefree n := fun hs => he (hfree.mp hs)
      simp [he, hf]
  rw [hif, ← sum_filter, hfilter]
  have hm := congrArg (fun f : ArithmeticFunction ℤ => f r) moebius_mul_coe_zeta
  change (μ * ArithmeticFunction.zeta : ArithmeticFunction ℤ) r = (1 : ArithmeticFunction ℤ) r at hm
  rw [coe_mul_zeta_apply, one_apply] at hm
  exact_mod_cast hm.symm

private theorem count_formula (N : ℕ) :
    (((Ioc 0 N).filter Squarefree).card : ℤ) =
      ∑ d ∈ Ioc 0 N, (μ d : ℤ) * ((N / d ^ 2 : ℕ) : ℤ) := by
  classical
  have hcard : (((Ioc 0 N).filter Squarefree).card : ℤ) =
      ∑ _n ∈ (Ioc 0 N).filter Squarefree, (1 : ℤ) := by
    simp [sum_const]
  rw [hcard, sum_filter]
  calc
    _ = ∑ n ∈ Ioc 0 N, ∑ d ∈ Ioc 0 N, if d ^ 2 ∣ n then (μ d : ℤ) else 0 := by
      refine sum_congr rfl (fun n hn => ?_)
      obtain ⟨hp, hN⟩ := mem_Ioc.mp hn
      exact mobius_indicator n N hp hN
    _ = ∑ d ∈ Ioc 0 N, ∑ n ∈ Ioc 0 N, if d ^ 2 ∣ n then (μ d : ℤ) else 0 :=
      sum_comm
    _ = _ := by
      refine sum_congr rfl (fun d _ => ?_)
      rw [← sum_filter, sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div, mul_comm]

theorem OMA.solution : OMA.R_Erdos969_erdos_969_variants_prime_number_theorem_R1.H2 := by
  intro x
  have he (b : ℕ) : Icc 1 b = Ioc 0 b := by ext n; simp; omega
  unfold Erdos969.squarefreeCounting
  rw [he, count_formula, he]
  symm
  apply sum_subset_zero_on_sdiff (s₁ := Ioc 0 (Nat.sqrt x)) (s₂ := Ioc 0 x) <;> try exact fun _ _ => rfl
  · exact Ioc_subset_Ioc le_rfl (Nat.sqrt_le_self x)
  · intro d hd
    have hm := mem_sdiff.mp hd
    have hl := (mem_Ioc.mp hm.1).1
    have hdx : Nat.sqrt x < d := by by_contra! h; exact hm.2 (mem_Ioc.mpr ⟨hl,h⟩)
    have hlt : x < d^2 := by simpa [pow_two] using Nat.sqrt_lt.mp hdx
    simp [Nat.div_eq_of_lt hlt]
