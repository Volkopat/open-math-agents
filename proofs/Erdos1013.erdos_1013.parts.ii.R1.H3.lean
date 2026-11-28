import OMAReductions.R_Erdos1013_erdos_1013_parts_ii_R1

/-!
# Step H3 of the reduction Erdos1013.erdos_1013.parts.ii.R1

If `a k / g k → 1` and `g (k + 1) / g k → 1`, then `a (k + 1) / a k → 1`: eventually `a k`,
`g k` and `g (k + 1)` are nonzero, and there the ratio factors as
`(a (k + 1) / g (k + 1)) * (g (k + 1) / g k) / (a k / g k)`.
-/

open Filter Topology

theorem OMA.solution : OMA.R_Erdos1013_erdos_1013_parts_ii_R1.H3 := by
  intro a g ha hg hg0
  have ha1 : Tendsto (fun k => a (k + 1) / g (k + 1)) atTop (𝓝 1) :=
    ha.comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun k => a (k + 1) / g (k + 1) * (g (k + 1) / g k) / (a k / g k))
      atTop (𝓝 1) := by
    have := (ha1.mul hg).div ha (one_ne_zero)
    simp only [mul_one, div_one] at this
    exact this
  have hane : ∀ᶠ k in atTop, a k / g k ≠ 0 := ha.eventually_ne one_ne_zero
  have hg1 : ∀ᶠ k in atTop, g (k + 1) ≠ 0 := (tendsto_add_atTop_nat 1).eventually hg0
  refine hlim.congr' ?_
  filter_upwards [hane, hg0, hg1] with k hk hgk hgk1
  have hak : a k ≠ 0 := by
    intro h; apply hk; simp [h]
  field_simp
