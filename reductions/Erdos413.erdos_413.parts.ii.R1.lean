import FormalConjectures.ErdosProblems.«413»

namespace OMA.R_Erdos413_erdos_413_parts_ii_R1

open Erdos413 ArithmeticFunction
open scoped omega Omega

/-- Lau's Theorem 1.3, in the form needed here: along an infinite set of centers,
every positive distance k<n has at most C log k distinct prime factors. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ S : Set ℕ, S.Infinite ∧
    ∀ n ∈ S, ∀ k : ℕ, 2 ≤ k → k < n →
      ((ω (n - k) : ℕ) : ℝ) ≤ C * Real.log k

/-- The logarithmic error is uniformly absorbed by distance k−1. -/
def H2 : Prop :=
  ∀ C : ℝ, 0 < C → ∃ ε : ℝ, 0 < ε ∧
    ∀ k : ℕ, 2 ≤ k → ε * C * Real.log k ≤ (k : ℝ) - 1

theorem arithmetic : H2 := by
  intro C hC
  refine ⟨1 / (C + 1), by positivity, ?_⟩
  intro k hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hklog : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))
  have hlog := Real.log_le_sub_one_of_pos hkpos
  have hcoef : (1 / (C + 1)) * C ≤ 1 := by
    have hden : 0 < C + 1 := by linarith
    rw [div_mul_eq_mul_div]
    apply (div_le_one hden).2
    nlinarith
  calc
    (1 / (C + 1)) * C * Real.log k = ((1 / (C + 1)) * C) * Real.log k := by ring
    _ ≤ 1 * Real.log k := mul_le_mul_of_nonneg_right hcoef hklog
    _ ≤ (k : ℝ) - 1 := by simpa using hlog

theorem main : H1 → H2 → type_of% @Erdos413.erdos_413.parts.ii := by
  rintro ⟨C, hC, S, hS, hbound⟩ harith
  obtain ⟨ε, hε, hlog⟩ := harith C hC
  refine ⟨ε, hε, ?_⟩
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hnS, hnN⟩ := Set.infinite_iff_exists_gt.mp hS (N + 1)
  have hn : N < n - 1 := by omega
  refine ⟨n - 1, ?_, hn⟩
  intro m hm
  change (m : ℝ) + ε * (ω m : ℝ) ≤ ((n - 1 : ℕ) : ℝ)
  by_cases hm0 : m = 0
  · subst m
    simp
  · let k := n - m
    have hmk : m < n := by omega
    have hk2 : 2 ≤ k := by dsimp [k]; omega
    have hkn : k < n := by dsimp [k]; omega
    have hω := hbound n hnS k hk2 hkn
    have hεω : ε * (ω m : ℝ) ≤ (k : ℝ) - 1 := by
      have hkm : n - k = m := by dsimp [k]; omega
      rw [hkm] at hω
      have hmul := mul_le_mul_of_nonneg_left hω (le_of_lt hε)
      have hnum := hlog k hk2
      calc
        ε * (ω m : ℝ) ≤ ε * (C * Real.log k) := hmul
        _ = ε * C * Real.log k := by ring
        _ ≤ (k : ℝ) - 1 := hnum
    have hcast : (n : ℝ) = (m : ℝ) + (k : ℝ) := by
      dsimp [k]
      have hsub : n = m + (n - m) := by omega
      exact_mod_cast hsub
    have hn1 : 1 ≤ n := by omega
    rw [Nat.cast_sub hn1]
    calc
      (m : ℝ) + ε * (ω m : ℝ) = ε * (ω m : ℝ) + (m : ℝ) := by ring
      _ ≤ ((k : ℝ) - 1) + (m : ℝ) := by
        simpa [add_comm] using add_le_add_right hεω (m : ℝ)
      _ = (n : ℝ) - 1 := by rw [hcast]; ring
    norm_num

end OMA.R_Erdos413_erdos_413_parts_ii_R1
