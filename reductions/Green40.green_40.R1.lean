import FormalConjectures.GreensOpenProblems.«40»

-- Credit: @PetrouilFan
-- Reduction of Green's problem 40.  The hard open part is the divergence of
-- f_tilde (the arbitrary-subsets version).  The comparison f_tilde <= f is
-- proved upstream, so proving H1 and H2 closes the original statement.

open Filter Topology
open scoped ENNReal

namespace OMA.R_Green40_green_40_R1

def H1 : Prop := Tendsto Green40.f_tilde atTop (𝓝 ⊤)

def H2 : Prop := ∀ r : ℕ, Green40.f_tilde r ≤ Green40.f r

theorem main : H1 → H2 → type_of% @Green40.green_40 := by
  intro h1 h2
  apply ENNReal.tendsto_nhds_top
  intro n
  filter_upwards [(tendsto_order.1 h1).1 (n : ℝ≥0∞) (by simp)] with r hr
  exact lt_of_lt_of_le hr (h2 r)

end OMA.R_Green40_green_40_R1
