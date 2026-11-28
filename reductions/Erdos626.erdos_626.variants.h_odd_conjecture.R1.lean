import FormalConjectures.ErdosProblems.«626»
import Mathlib

-- Reduction Erdos626.erdos_626.variants.h_odd_conjecture.R1 of the odd case of Erdős Problem 626
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-! For odd m, Erdős conjectured that the largest chromatic number h^(m)(n) of a graph on n
vertices with girth greater than m is n^(2/(m+1) + o(1)). The upper bound is his theorem of 1959
(the catalogue's solved variant Erdos626.erdos_626.variants.h_upper_odd). For m = 1 the girth
condition is empty and h^(1)(n) = n; this case is proved below. For m = 3 the lower bound is known:
there are triangle-free graphs on n vertices with independence number at most C sqrt(n) log n
(Erdős 1961; Kim 1995 gives the sharp order). The lower bound for odd m >= 5 is the open part. -/

namespace OMA.R_Erdos626_erdos_626_variants_h_odd_conjecture_R1

open Filter Topology

/-- The known upper bound: h^(m)(n) <= n^(2/(m+1) + eps) for odd m. -/
def H1 : Prop :=
  ∀ m : ℕ, Odd m → ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    (Erdos626.h m n : ℝ) ≤ (n : ℝ) ^ (2 / ((m : ℝ) + 1) + ε)

/-- The open lower bound: n^(2/(m+1) - eps) <= h^(m)(n) for odd m >= 5. -/
def H2 : Prop :=
  ∀ m : ℕ, Odd m → 5 ≤ m → ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (2 / ((m : ℝ) + 1) - ε) ≤ (Erdos626.h m n : ℝ)

/-- The known lower bound for triangle-free graphs: n^(1/2 - eps) <= h^(3)(n). -/
def H3 : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ (Erdos626.h 3 n : ℝ)

theorem main : H1 → H2 → H3 → type_of% @Erdos626.erdos_626.variants.h_odd_conjecture := by
  intro h1 h2 h3 m hm
  have lower : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (2 / ((m : ℝ) + 1) - ε) ≤ (Erdos626.h m n : ℝ) := by
    intro ε hε
    obtain ⟨k, rfl⟩ := hm
    rcases (by omega : k = 0 ∨ k = 1 ∨ 2 ≤ k) with rfl | rfl | hk
    · filter_upwards [eventually_ge_atTop 1] with n hn
      rw [Erdos626.h_of_le_two _ _ (by norm_num)]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      calc (n : ℝ) ^ (2 / (((2 * 0 + 1 : ℕ) : ℝ) + 1) - ε) ≤ (n : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num; linarith)
        _ = n := Real.rpow_one _
    · filter_upwards [h3 ε hε] with n hn
      have he : 2 / (((2 * 1 + 1 : ℕ) : ℝ) + 1) - ε = (1 : ℝ) / 2 - ε := by norm_num
      rw [he]
      exact hn
    · exact h2 _ ⟨k, rfl⟩ (by omega) ε hε
  have key : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      2 / ((m : ℝ) + 1) - ε ≤ Real.log (Erdos626.h m n : ℝ) / Real.log n ∧
        Real.log (Erdos626.h m n : ℝ) / Real.log n ≤ 2 / ((m : ℝ) + 1) + ε := by
    intro ε hε
    filter_upwards [lower ε hε, h1 m hm ε hε, eventually_ge_atTop 2] with n hl hu hn
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hn0 : (0 : ℝ) < n := by linarith
    have hlog : 0 < Real.log n := Real.log_pos hn1
    have hpos : (0 : ℝ) < Erdos626.h m n := lt_of_lt_of_le (Real.rpow_pos_of_pos hn0 _) hl
    constructor
    · rw [le_div_iff₀ hlog]
      have := Real.log_le_log (Real.rpow_pos_of_pos hn0 _) hl
      rwa [Real.log_rpow hn0] at this
    · rw [div_le_iff₀ hlog]
      have := Real.log_le_log hpos hu
      rwa [Real.log_rpow hn0] at this
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [key ((2 / ((m : ℝ) + 1) - a) / 2) (by linarith)] with n hn
    linarith [hn.1]
  · intro a ha
    filter_upwards [key ((a - 2 / ((m : ℝ) + 1)) / 2) (by linarith)] with n hn
    linarith [hn.2]

end OMA.R_Erdos626_erdos_626_variants_h_odd_conjecture_R1
