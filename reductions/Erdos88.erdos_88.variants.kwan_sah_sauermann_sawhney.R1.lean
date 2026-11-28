import FormalConjectures.ErdosProblems.«88»

-- Reduction of Kwan–Sah–Sauermann–Sawhney, Theorem 1.1, by edge-count density.
-- Credit: @picasso250

open Filter

namespace OMA.R_Erdos88_erdos_88_variants_kwan_sah_sauermann_sawhney_R1

-- The small-count conclusion of Erdős–McKay, using a fraction of e(G).
def H1 : Prop :=
  ∀ C > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
    (G.cliqueNum : ℝ) < C * Real.logb 2 n → (G.indepNum : ℝ) < C * Real.logb 2 n →
    ∀ m : ℕ, (m : ℝ) ≤ δ * G.edgeSet.ncard →
      ∃ S : Finset (Fin n), (G.induce (S : Set (Fin n))).edgeSet.ncard = m

-- The support consequence of the biased local limit theorem (KSSS, Theorem 1.2).
-- The bounds on p² keep p in a compact subinterval of (0,1), uniformly in n.
def H2 : Prop :=
  ∀ C > (0 : ℝ), ∀ a > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
    (G.cliqueNum : ℝ) < C * Real.logb 2 n → (G.indepNum : ℝ) < C * Real.logb 2 n →
    ∀ p : ℝ, 0 ≤ p → a ≤ p ^ 2 → p ^ 2 ≤ 1 - a →
    ∀ m : ℕ, |(m : ℝ) - p ^ 2 * G.edgeSet.ncard| ≤ (n : ℝ) ^ (3 / 2 : ℝ) →
      ∃ S : Finset (Fin n), (G.induce (S : Set (Fin n))).edgeSet.ncard = m

theorem main : H1 → H2 → type_of% @Erdos88.erdos_88.variants.kwan_sah_sauermann_sawhney := by
  intro small window C hC η hη
  obtain ⟨δ, hδ, hs⟩ := small C hC
  have hw := window C hC (min δ η) (lt_min hδ hη)
  filter_upwards [hs, hw] with n hs hw
  intro G hc hi m hm
  let e : ℝ := G.edgeSet.ncard
  change (m : ℝ) ≤ (1 - η) * e at hm
  by_cases hsmall : (m : ℝ) ≤ δ * e
  · exact hs G hc hi m hsmall
  have he : 0 < e := by
    have hnonneg : 0 ≤ e := Nat.cast_nonneg _
    by_contra! hz
    have heq : e = 0 := le_antisymm hz hnonneg
    simp [heq] at hm hsmall
    omega
  let p := Real.sqrt ((m : ℝ) / e)
  have hp : p ^ 2 = (m : ℝ) / e := Real.sq_sqrt (div_nonneg (Nat.cast_nonneg _) he.le)
  apply hw G hc hi p (Real.sqrt_nonneg _)
  · rw [hp]
    exact (min_le_left _ _).trans ((le_div_iff₀ he).2 (le_of_not_ge hsmall))
  · rw [hp]
    exact ((div_le_iff₀ he).2 hm).trans (sub_le_sub_left (min_le_right _ _) 1)
  · rw [hp]
    change |(m : ℝ) - m / e * e| ≤ _
    rw [div_mul_cancel₀ _ he.ne', sub_self, abs_zero]
    positivity

end OMA.R_Erdos88_erdos_88_variants_kwan_sah_sauermann_sawhney_R1
