import OMAStatements.S_oeis_a130095
import Mathlib.Tactic

open OMA.S_oeis_a130095 Filter Topology Finset
open scoped goldenRatio

namespace FibonacciDivisorSum

private def rest (n : ℕ) : ℕ := ∑ d ∈ (n+1).properDivisors, Nat.fib (2*d-1)

private lemma split (n : ℕ) : term (n+1) = Nat.fib (2*n+1) + rest n := by
  unfold term rest
  rw [←Nat.insert_self_properDivisors (Nat.succ_ne_zero n),
    sum_insert Nat.self_notMem_properDivisors,show 2*(n+1)-1=2*n+1 by omega]

private lemma fibBound (n : ℕ) : Nat.fib n ≤ 2^n ∧ Nat.fib (n+1) ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    change Nat.fib (n+1) ≤ 2^(n+1) ∧ Nat.fib (n+2) ≤ 2^(n+1)
    rw [Nat.fib_add_two,pow_succ]
    omega

private lemma restBound (n : ℕ) : rest n ≤ (n+1)*2^n := by
  have sub : (n+1).properDivisors ⊆ range (n+1) := by
    intro d hd
    exact mem_range.mpr (Nat.mem_properDivisors.mp hd).2
  have count : (n+1).properDivisors.card ≤ n+1 := by simpa using card_le_card sub
  have entry (d : ℕ) (hd : d ∈ (n+1).properDivisors) : Nat.fib (2*d-1) ≤ 2^n := by
    obtain ⟨⟨c,hc⟩,lt⟩ := Nat.mem_properDivisors.mp hd
    have two : 2≤c := by
      by_contra! bad
      interval_cases c <;> simp_all
    have twice := Nat.mul_le_mul_left d two
    exact (Nat.fib_mono (show 2*d-1 ≤ n by omega)).trans (fibBound n).1
  calc
    rest n ≤ ∑ _d ∈ (n+1).properDivisors, 2^n := sum_le_sum entry
    _ = (n+1).properDivisors.card*2^n := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ count

private lemma baseGt : 2 < φ^2 := by linarith [Real.goldenRatio_sq,Real.one_lt_goldenRatio]

private lemma leading (n : ℕ) :
    (Nat.fib (2*n+1):ℝ)/(φ^2)^n = (φ-ψ*(ψ^2/φ^2)^n)/Real.sqrt 5 := by
  rw [Real.coe_fib_eq,pow_succ φ (2*n),pow_succ ψ (2*n),pow_mul φ 2 n,pow_mul ψ 2 n,
    div_pow (ψ^2) (φ^2) n]
  field_simp [Real.goldenRatio_pos.ne',Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<5)]

private noncomputable def scaled (n : ℕ) : ℝ := (term (n+1):ℝ)/(φ^2)^n

private lemma normalized : Tendsto scaled atTop (𝓝 (φ/Real.sqrt 5)) := by
  have pos : 0 < φ^2 := by linarith [baseGt]
  have small : 2/φ^2 < 1 := (div_lt_one pos).mpr baseGt
  have nonneg : 0 ≤ 2/φ^2 := by positivity
  have conjSmall : ψ^2/φ^2 < 1 := by
    apply (div_lt_one pos).mpr
    linarith [Real.goldenConj_sq, Real.goldenConj_neg,baseGt]
  have geo := tendsto_pow_atTop_nhds_zero_of_lt_one nonneg small
  have geoConj := tendsto_pow_atTop_nhds_zero_of_lt_one (show 0≤ψ^2/φ^2 by positivity) conjSmall
  have bound : Tendsto (fun n : ℕ => ((n:ℝ)+1)*(2/φ^2)^n) atTop (𝓝 0) := by
    have h := (tendsto_self_mul_const_pow_of_lt_one nonneg small).add geo
    simpa only [zero_add,add_mul,one_mul] using h
  have negligible : Tendsto (fun n : ℕ => (rest n:ℝ)/(φ^2)^n) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => by positivity) _ bound
    intro n
    rw [div_pow (2:ℝ) (φ^2) n,←mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast restBound n
  have large : Tendsto (fun n : ℕ => (Nat.fib (2*n+1):ℝ)/(φ^2)^n) atTop (𝓝 (φ/Real.sqrt 5)) := by
    have h := (tendsto_const_nhds (x:=φ)).sub (geoConj.const_mul ψ)
    have j := h.div_const (Real.sqrt 5)
    simpa only [leading,mul_zero,sub_zero] using j
  have total := large.add negligible
  simp only [add_zero] at total
  apply total.congr
  intro n
  simp only [scaled,split,Nat.cast_add,add_div]

end FibonacciDivisorSum

open FibonacciDivisorSum

theorem OMA.solution : type_of% @OMA.S_oeis_a130095.main := by
  apply (tendsto_add_atTop_iff_nat 2).mp
  have coef : φ/Real.sqrt 5 ≠ 0 := by positivity
  have sh : Tendsto (fun n : ℕ => scaled (n+1)) atTop (𝓝 (φ/Real.sqrt 5)) :=
    normalized.comp (tendsto_add_atTop_nat 1)
  have h := (sh.div normalized coef).const_mul (φ^2)
  simp only [div_self coef,mul_one] at h
  apply h.congr
  intro n
  have positiveTerm : 0 < term (n+1) := by
    rw [split]
    have f := Nat.fib_pos.mpr (show 0 < 2*n+1 by omega)
    omega
  have nonzero : (term (n+1):ℝ) ≠ 0 := by exact_mod_cast positiveTerm.ne'
  change φ^2*(scaled (n+1)/scaled n) = (term (n+2):ℝ)/(term (n+1):ℝ)
  simp only [scaled,pow_succ]
  field_simp [nonzero,Real.goldenRatio_pos.ne']
