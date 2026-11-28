import OMAReductions.R_Green87_green_87_variants_order_R2
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
open Filter Asymptotics MeasureTheory Real Finset
open scoped BigOperators
namespace OMA.R_Green87_green_87_variants_order_R2_H2_R1

/-- Lower estimate for the Poisson subset-sum expectation. -/
def H1 : Prop :=
  let mass : ℕ → ℝ := fun k ↦
    (∑' a : Fin k → ℕ,
      ((Finset.univ.image (fun b : (j : Fin k) → Fin (a j + 1) ↦
        ∑ j, (j.val + 1) * (b j).val)).card : ℝ) *
      ∏ j : Fin k, Real.exp (-(1 / ((j.val + 1 : ℕ) : ℝ))) /
        ((a j).factorial * (((j.val + 1 : ℕ) : ℝ) ^ a j))) / (k : ℝ)
  let scale := fun k : ℕ ↦ (k:ℝ)^(-Green87.δ)*(1+Real.log k)^(-(3/2:ℝ))
  scale =O[atTop] mass

/-- Upper comparison with the finite ordered-simplex series at the preceding dyadic size. -/
def H2 : Prop :=
  let mass : ℕ → ℝ := fun k ↦
    (∑' a : Fin k → ℕ,
      ((Finset.univ.image (fun b : (j : Fin k) → Fin (a j + 1) ↦
        ∑ j, (j.val + 1) * (b j).val)).card : ℝ) *
      ∏ j : Fin k, Real.exp (-(1 / ((j.val + 1 : ℕ) : ℝ))) /
        ((a j).factorial * (((j.val + 1 : ℕ) : ℝ) ^ a j))) / (k : ℝ)
  let bound := fun m : ℕ ↦
    let d : ℕ := 2^m
    let u := fun r : ℕ ↦ ∫ x in (Set.Icc (0:Fin r → ℝ) 1 ∩ {x | Monotone x}),
      Finset.univ.inf' Finset.univ_nonempty (fun j : Fin (r+1) ↦
        (1+∑ i : Fin r with i.val < j.val, (d:ℝ)^(x i))/(2:ℝ)^j.val)
    Real.exp 1 / (((d:ℝ)+1)*d) * ((∑ r ∈ Finset.range (Nat.clog 4 (d^20)),
      (2*(harmonic d:ℝ))^r*u r) + Real.exp 8/(d:ℝ)^12)
  ∀ k : ℕ, 0 < k → mass k ≤ bound (Nat.log 2 k)

/-- Purely geometric dyadic estimate, including the explicit negligible tail. -/
def H3 : Prop :=
  let bound := fun m : ℕ ↦
    let d : ℕ := 2^m
    let u := fun r : ℕ ↦ ∫ x in (Set.Icc (0:Fin r → ℝ) 1 ∩ {x | Monotone x}),
      Finset.univ.inf' Finset.univ_nonempty (fun j : Fin (r+1) ↦
        (1+∑ i : Fin r with i.val < j.val, (d:ℝ)^(x i))/(2:ℝ)^j.val)
    Real.exp 1 / (((d:ℝ)+1)*d) * ((∑ r ∈ Finset.range (Nat.clog 4 (d^20)),
      (2*(harmonic d:ℝ))^r*u r) + Real.exp 8/(d:ℝ)^12)
  let scale := fun k : ℕ ↦ (k:ℝ)^(-Green87.δ)*(1+Real.log k)^(-(3/2:ℝ))
  ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, bound m ≤ C * scale (2^m)

theorem main : H1 → H2 → H3 → OMA.R_Green87_green_87_variants_order_R2.H2 := by
  intro hl hb hg
  let mass : ℕ → ℝ := fun k ↦
    (∑' a : Fin k → ℕ,
      ((Finset.univ.image (fun b : (j : Fin k) → Fin (a j + 1) ↦
        ∑ j, (j.val + 1) * (b j).val)).card : ℝ) *
      ∏ j : Fin k, Real.exp (-(1 / ((j.val + 1 : ℕ) : ℝ))) /
        ((a j).factorial * (((j.val + 1 : ℕ) : ℝ) ^ a j))) / (k : ℝ)
  let bound := fun m : ℕ ↦
    let d : ℕ := 2^m
    let u := fun r : ℕ ↦ ∫ x in (Set.Icc (0:Fin r → ℝ) 1 ∩ {x | Monotone x}),
      Finset.univ.inf' Finset.univ_nonempty (fun j : Fin (r+1) ↦
        (1+∑ i : Fin r with i.val < j.val, (d:ℝ)^(x i))/(2:ℝ)^j.val)
    Real.exp 1 / (((d:ℝ)+1)*d) * ((∑ r ∈ Finset.range (Nat.clog 4 (d^20)),
      (2*(harmonic d:ℝ))^r*u r) + Real.exp 8/(d:ℝ)^12)
  let scale := fun k : ℕ ↦ (k:ℝ)^(-Green87.δ)*(1+Real.log k)^(-(3/2:ℝ))
  change mass =Θ[atTop] scale
  refine ⟨?_,hl⟩
  obtain ⟨C,hC,hg⟩ := hg
  apply IsBigO.of_bound (C*4*(2:ℝ)^(abs Green87.δ))
  filter_upwards [eventually_ge_atTop (1:ℕ)] with k hk
  let m := Nat.log 2 k
  let d : ℕ := 2^m
  have hd : 0 < d := by dsimp [d]; positivity
  have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
  have hk' : 0 < (k:ℝ) := by exact_mod_cast hk
  have hdk : d ≤ k := Nat.pow_log_le_self 2 (Nat.ne_of_gt hk)
  have hkd : (k:ℝ) ≤ 2*d := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1<2) k
    exact_mod_cast (by simpa [d,m,pow_succ,Nat.mul_comm] using h.le : k ≤ 2*d)
  have hlog := log_le_log hk' hkd
  rw [log_mul (by norm_num) hd'.ne'] at hlog
  have hd1 : 0 ≤ log d := log_nonneg (by exact_mod_cast hd)
  have hy : 0 < 1+log (d:ℝ) := by linarith
  have hyk : 0 < 1+log (k:ℝ) := by linarith [log_nonneg (by exact_mod_cast hk : (1:ℝ)≤k)]
  have hlog2 : 1+log k ≤ 2*(1+log d) := by linarith [Real.log_two_lt_d9]
  have hc : d ≤ k := hdk
  have hp : (d:ℝ)^(-Green87.δ) ≤ (2:ℝ)^(abs Green87.δ)*(k:ℝ)^(-Green87.δ) := by
    have hz : 1 ≤ (k:ℝ)/d := (one_le_div hd').2 (by exact_mod_cast hc)
    have ha := Real.rpow_le_rpow_of_exponent_le hz (le_abs_self Green87.δ)
    have hc2 := Real.rpow_le_rpow (div_nonneg hk'.le hd'.le) ((div_le_iff₀ hd').2 hkd) (abs_nonneg Green87.δ)
    have h := ha.trans hc2
    rw [Real.div_rpow hk'.le hd'.le] at h
    rw [Real.rpow_neg hd'.le, Real.rpow_neg hk'.le,←div_eq_mul_inv]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hk' _)).2
    simpa [div_eq_inv_mul] using h
  have hls : (1+log (d:ℝ))^(-(3/2:ℝ)) ≤ 4*(1+log (k:ℝ))^(-(3/2:ℝ)) := by
    have h := Real.rpow_le_rpow hyk.le hlog2 (by norm_num : (0:ℝ) ≤ 3/2)
    rw [Real.mul_rpow (by norm_num) hy.le] at h
    have hb : (2:ℝ)^(3/2:ℝ) ≤ 4 := by
      calc
        _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = _ := by norm_num
    have hh := h.trans (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hy.le _))
    rw [Real.rpow_neg hy.le,Real.rpow_neg hyk.le,←div_eq_mul_inv]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hyk _)).2
    rwa [inv_mul_le_iff₀ (Real.rpow_pos_of_pos hy _),mul_comm _ (4:ℝ)]
  have hmass : 0 ≤ mass k := by dsimp [mass]; positivity
  have hscale : 0 ≤ scale k := by dsimp [scale]; positivity
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hmass,abs_of_nonneg hscale]
  calc
    mass k ≤ bound m := hb k hk
    _ ≤ C*scale d := hg m
    _ ≤ _ := by
      have h := mul_le_mul hp hls (Real.rpow_nonneg hy.le _) (by positivity)
      dsimp [scale]; nlinarith [mul_le_mul_of_nonneg_left h hC]
end OMA.R_Green87_green_87_variants_order_R2_H2_R1
