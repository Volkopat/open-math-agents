import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2

/-! Compare the two extremal densities only at the first integer length at which
the three-term density reaches each dyadic threshold. The length need not be
a power of two. There is at most one test length for each threshold.

H1 is the remaining combinatorial estimate at those lengths. H2 transfers
from a first crossing to an arbitrary length using interval subdivision.
The factors two in H2 respectively account for rounding the last block and
for rounding the reciprocal density to a power of two. -/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R3

open Erdos142 Filter

/-- Four-term density at the first crossing of each three-term density threshold. -/
def H1 : Prop :=
  ∃ θ C : ℝ, 1 / 2 < θ ∧ 0 < C ∧ ∀ m n : ℕ, 0 < n →
    2 ^ m * r 3 n = n → (∀ j, 0 < j → j < n → j < 2 ^ m * r 3 j) →
    (r 4 n : ℝ) ≤ C * n * ((1 : ℝ) / 2 ^ m) ^ θ

/-- A finite first crossing certifies both scale comparisons, for any progression length. -/
def H2 : Prop :=
  ∀ k N : ℕ, 0 < N → ∃ m n : ℕ, 0 < n ∧ n ≤ N ∧
    2 ^ m * r 3 n = n ∧ (∀ j, 0 < j → j < n → j < 2 ^ m * r 3 j) ∧
    N < 2 ^ (m + 1) * r 3 N ∧ n * r k N ≤ 2 * N * r k n

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2.H1 := by
  rintro ⟨θ,C,hθ,hC,first⟩ transfer
  have hθ0 : 0 ≤ θ := by linarith
  refine ⟨θ,2*C*(2:ℝ)^θ,hθ,by positivity,?_⟩
  filter_upwards [eventually_gt_atTop 0] with N hN
  obtain ⟨m,n,hn,-,he,hprev,hround,hblock⟩ := transfer 4 N hN
  have hden := first m n hn he hprev
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hround' : (N:ℝ) ≤ 2^(m+1) * (r 3 N : ℝ) := by exact_mod_cast hround.le
  have hunit : (1:ℝ)/2^m ≤ 2*((r 3 N : ℝ)/N) := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) hN']
    rw [pow_succ] at hround'
    linarith only [hround']
  have hp := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 1/2^m) hunit hθ0
  rw [Real.mul_rpow (by norm_num) (by positivity)] at hp
  have hb : (n:ℝ)*(r 4 N : ℝ) ≤ 2*N*(r 4 n : ℝ) := by exact_mod_cast hblock
  apply le_of_mul_le_mul_left (a := (n:ℝ)) _ hn'
  calc
    (n:ℝ)*(r 4 N : ℝ) ≤ 2*N*(r 4 n : ℝ) := hb
    _ ≤ 2*N*(C*n*((1:ℝ)/2^m)^θ) := by gcongr
    _ ≤ 2*N*(C*n*((2:ℝ)^θ*((r 3 N:ℝ)/N)^θ)) := by gcongr
    _ = _ := by ring

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R3
