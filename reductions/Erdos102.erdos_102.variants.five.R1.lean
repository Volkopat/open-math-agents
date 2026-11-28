import FormalConjectures.ErdosProblems.«102»
open EuclideanGeometry
open Filter

-- Reduction Erdos102.erdos_102.variants.five.R1 of Erdos 102, five-points case.
-- Credit: @PetrouilFan
-- H1 is the open point-line incidence statement: every sufficiently large planar set
-- carrying at least c*n^2 rich lines has a line with at least five of its points.
-- H2 is a proved transfer bridge: upstream Erdos102.le_h_iff (category API, full Lean
-- proof, kernel-audited) converts that incidence statement into the h_c(n) >= 5 formulation.

namespace OMA.R_Erdos102_erdos_102_variants_five_R1

def H1 : Prop :=
  ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop,
    ∀ P : Finset ℝ², P.card = n →
      c * (n : ℝ) ^ 2 ≤ Erdos102.richLineCount P →
      ∃ L : AffineSubspace ℝ ℝ², IsLine L ∧ 5 ≤ Erdos102.pointsOn P L

def H2 : Prop :=
  (∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop,
    ∀ P : Finset ℝ², P.card = n →
      c * (n : ℝ) ^ 2 ≤ Erdos102.richLineCount P →
      ∃ L : AffineSubspace ℝ ℝ², IsLine L ∧ 5 ≤ Erdos102.pointsOn P L) →
  ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop, (5 : ℕ∞) ≤ Erdos102.h c n

lemma upstream_bridge : H2 := by
  intro hInc c hc
  filter_upwards [hInc c hc] with n hn
  simpa using (Erdos102.le_h_iff c n 5).2 (by
    intro P hP
    exact hn P hP.1 hP.2)

theorem main : H1 → H2 → type_of% @Erdos102.erdos_102.variants.five := by
  intro h1 h2
  exact h2 h1

end OMA.R_Erdos102_erdos_102_variants_five_R1
