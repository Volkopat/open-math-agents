import OMAReductions.R_Erdos626_erdos_626_variants_h_even_conjecture_R1
import Mathlib

-- Reduction Erdos626.erdos_626.variants.h_even_conjecture.R1.H2.R1 of step Erdos626.erdos_626.variants.h_even_conjecture.R1.H2
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the step.

/-! Let h^(m)(n) be the largest chromatic number of a graph on n vertices with girth greater
than m. The parent step is the lower bound n^(2/(m+2) - eps) <= h^(m)(n) for even m >= 2.
For m = 2 it is proved below, since h^(2)(n) = n. For m = 4 it says that some graphs of girth at
least 5 have chromatic number n^(1/3 - o(1)). This follows from the lower bound method for
r(C_4, K_t) of Spencer (1977) and Krivelevich (1995), run for the family of C_3 and C_4: delete
a maximal edge-disjoint family of short cycles from a random graph with edge probability
c n^(-2/3); the independence number stays below C n^(2/3) log n. The case of even m >= 6 is the
open part. The first case m = 6 asks for graphs of girth at least 7 with chromatic number
n^(1/4 - o(1)); the random graph method gives only n^(1/5 - o(1)). -/

namespace OMA.R_Erdos626_erdos_626_variants_h_even_conjecture_R1_H2_R1

open Filter Topology

/-- The lower bound for girth at least 5: n^(1/3 - eps) <= h^(4)(n). -/
def H1 : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ ((1 : ℝ) / 3 - ε) ≤ (Erdos626.h 4 n : ℝ)

/-- The open lower bound for even m >= 6: n^(2/(m+2) - eps) <= h^(m)(n). -/
def H2 : Prop :=
  ∀ m : ℕ, Even m → 6 ≤ m → ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (2 / ((m : ℝ) + 2) - ε) ≤ (Erdos626.h m n : ℝ)

theorem main : H1 → H2 → OMA.R_Erdos626_erdos_626_variants_h_even_conjecture_R1.H2 := by
  intro h1 h2 m hm hm2 ε hε
  obtain ⟨k, rfl⟩ := hm
  rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | hk
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Erdos626.h_of_le_two _ _ (by norm_num)]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc (n : ℝ) ^ (2 / (((1 + 1 : ℕ) : ℝ) + 2) - ε) ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num; linarith)
      _ = n := Real.rpow_one _
  · filter_upwards [h1 ε hε] with n hn
    have he : 2 / (((2 + 2 : ℕ) : ℝ) + 2) - ε = (1 : ℝ) / 3 - ε := by norm_num
    rw [he]
    exact hn
  · exact h2 _ ⟨k, rfl⟩ (by omega) ε hε

end OMA.R_Erdos626_erdos_626_variants_h_even_conjecture_R1_H2_R1
