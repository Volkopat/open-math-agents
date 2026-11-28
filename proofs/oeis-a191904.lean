import OMAStatements.S_oeis_a191904
import Mathlib

-- Proof of Mats Granvik's conjecture in OEIS A191904 (statement by @ivillar).
-- Idea: Sum_{n=1..N} T(n,k)/n = H(N) - H(floor(N/k)) with H the harmonic numbers; since
-- H(m) - log(m+1) tends to the Euler-Mascheroni constant and (N+1)/(floor(N/k)+1) tends to k,
-- the partial sums tend to log(k).

namespace OMAA191904Helpers

open Filter Topology OMA.S_oeis_a191904

theorem filt_eq (k N : ℕ) (hk : 1 ≤ k) :
    (Finset.Icc 1 N).filter (fun n => k ∣ n) = (Finset.Icc 1 (N / k)).image (fun m => k * m) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, m, rfl⟩
    refine ⟨m, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp at h1
      · exact h
    · rw [Nat.le_div_iff_mul_le (by omega)]; linarith [mul_comm k m]
  · rintro ⟨m, ⟨h1, h2⟩, rfl⟩
    refine ⟨⟨by nlinarith, ?_⟩, dvd_mul_right _ _⟩
    rw [Nat.le_div_iff_mul_le (by omega)] at h2; linarith [mul_comm k m]

theorem sum_eq (k N : ℕ) (hk : 1 ≤ k) :
    ∑ n ∈ Finset.Icc 1 N, (T n k : ℝ) / n = (harmonic N : ℝ) - (harmonic (N / k) : ℝ) := by
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have h1 : ∀ n ∈ Finset.Icc 1 N, (T n k : ℝ) / n = 1 / n - (if k ∣ n then (k : ℝ) / n else 0) := by
    intro n _
    unfold T
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, ← Finset.sum_filter, filt_eq k N hk,
    Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left (by omega) h)]
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_Icc] at hm
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast
  field_simp

theorem ratio_tendsto (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1) / ((N / k : ℕ) + 1)) atTop (𝓝 (k : ℝ)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  -- lower bound k * (N / (N + k)) and upper bound k * (1 + 1 / N)
  have hlow : Tendsto (fun N : ℕ => (k : ℝ) * ((N : ℝ) / (N + k))) atTop (𝓝 ((k : ℝ) * 1)) :=
    (tendsto_natCast_div_add_atTop (k : ℝ)).const_mul _
  have hup : Tendsto (fun N : ℕ => (k : ℝ) * (1 + 1 / (N : ℝ))) atTop (𝓝 ((k : ℝ) * (1 + 0))) :=
    (tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat).const_mul _
  rw [mul_one] at hlow
  rw [add_zero, mul_one] at hup
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup
  · filter_upwards with N
    have hq : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / k := by
      rw [le_div_iff₀ hk0]
      exact_mod_cast Nat.div_mul_le_self N k
    have hpos : (0 : ℝ) < ((N / k : ℕ) : ℝ) + 1 := by positivity
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hpos]
    have : ((N / k : ℕ) : ℝ) * k ≤ N := by
      have := (le_div_iff₀ hk0).mp hq; linarith
    nlinarith
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hq : (N : ℝ) / k < ((N / k : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hk0]
      have h := Nat.lt_div_mul_add (a := N) (b := k) (by omega)
      have h' : (N : ℝ) < ((N / k : ℕ) : ℝ) * k + k := by exact_mod_cast h
      nlinarith
    have hpos : (0 : ℝ) < ((N / k : ℕ) : ℝ) + 1 := by positivity
    rw [div_le_iff₀ hpos]
    have h1 : (N : ℝ) < k * (((N / k : ℕ) : ℝ) + 1) := by
      have := (div_lt_iff₀ hk0).mp hq; linarith
    have hNpos : (0 : ℝ) < N := by linarith
    rw [show (k : ℝ) * (1 + 1 / (N : ℝ)) * (((N / k : ℕ) : ℝ) + 1) =
      k * (((N / k : ℕ) : ℝ) + 1) * (N + 1) / N by field_simp]
    rw [le_div_iff₀ hNpos]
    nlinarith

end OMAA191904Helpers

open Filter Topology OMA.S_oeis_a191904 OMAA191904Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a191904.main := by
  intro k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have e : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, (T n k : ℝ) / n =
      ((harmonic N : ℝ) - Real.log ((N : ℝ) + 1)) -
        ((harmonic (N / k) : ℝ) - Real.log (((N / k : ℕ) : ℝ) + 1)) +
        Real.log (((N : ℝ) + 1) / (((N / k : ℕ) : ℝ) + 1)) := by
    intro N
    rw [sum_eq k N hk, Real.log_div (by positivity) (by positivity)]
    ring
  simp_rw [e]
  have h1 := Real.tendsto_harmonic_sub_log_add_one
  have h2 := h1.comp (Nat.tendsto_div_const_atTop (n := k) (by omega))
  have h3 := (ratio_tendsto k hk).log (by positivity)
  have := (h1.sub h2).add h3
  rw [sub_self, zero_add] at this
  convert this using 2
  simp [Function.comp]
