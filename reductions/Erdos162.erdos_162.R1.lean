import FormalConjectures.ErdosProblems.«162»

-- Reduction Erdos162.erdos_162.R1 of Erdős Problem 162
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Sketch. Fix 0 ≤ α < 1/2. The problem asks for a constant c with F(n, α) ~ c * log n. We
-- separate the order of magnitude from the existence of the constant:
-- * H1 (known): the probabilistic lower bound F(n, α) > c₁(α) log n with c₁(α) > 0. It is the
--   lower half of `Erdos162.erdos_162.variants.bounds`, already formalized in this repository.
-- * H2 (open): the ratio F(n, α) / log n converges to some real limit L(α).
-- Then L ≥ c₁ > 0 by H1, and F / (L * log n) = (F / log n) / L → 1, so F ~ L * log n.

namespace OMA.R_Erdos162_erdos_162_R1

open Filter Asymptotics Topology

def H1 : Prop :=
  ∀ α : ℝ, 0 ≤ α → α < 1 / 2 → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    c * Real.log n ≤ (Erdos162.F n α : ℝ)

def H2 : Prop :=
  ∀ α : ℝ, 0 ≤ α → α < 1 / 2 → ∃ L : ℝ,
    Tendsto (fun n : ℕ => (Erdos162.F n α : ℝ) / Real.log n) atTop (𝓝 L)

lemma log_pos_eventually : ∀ᶠ n : ℕ in atTop, 0 < Real.log n := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  exact Real.log_pos hn'

theorem main : H1 → H2 → type_of% @Erdos162.erdos_162 := by
  intro h1 h2 α h0 hα
  obtain ⟨c, hc, hlow⟩ := h1 α h0 hα
  obtain ⟨L, hL⟩ := h2 α h0 hα
  have hcL : c ≤ L := by
    apply ge_of_tendsto hL
    filter_upwards [hlow, log_pos_eventually] with n h1 h2
    rw [le_div_iff₀ h2]
    exact h1
  have hLpos : 0 < L := lt_of_lt_of_le hc hcL
  refine ⟨L, ?_⟩
  refine isEquivalent_of_tendsto_one ?_
  have h3 := hL.div_const L
  rw [div_self hLpos.ne'] at h3
  refine h3.congr' ?_
  filter_upwards [log_pos_eventually] with n hn
  simp only [Pi.div_apply]
  field_simp

end OMA.R_Erdos162_erdos_162_R1
