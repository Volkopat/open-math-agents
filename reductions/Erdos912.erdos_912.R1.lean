import FormalConjectures.ErdosProblems.«912»

-- Reduction Erdos912.erdos_912.R1 of Erdős Problem 912
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Sketch. Write g(n) = (n / log n)^(1/2) and h(n) for the number of distinct exponents in n!.
-- The problem asks for c > 0 with h ~ c * g. We separate the order of magnitude from the
-- existence of the constant:
-- * H1 (known): the lower half of the Erdős–Selfridge bound h(n) ≫ g(n) [Er82c]. It is the
--   lower half of `Erdos912.erdos_912.variants.selfridge`, already formalized in this repository.
-- * H2 (open): the ratio h(n) / g(n) converges to some real limit L.
-- Then L ≥ c > 0 by H1, g(n) > 0 for n ≥ 2, and h / (L * g) → 1, so h ~ L * g.

namespace OMA.R_Erdos912_erdos_912_R1

open Filter Asymptotics Topology

def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    c * ((n : ℝ) / Real.log n) ^ (1 / 2 : ℝ) ≤ (Erdos912.h n : ℝ)

def H2 : Prop :=
  ∃ L : ℝ, Tendsto (fun n : ℕ => (Erdos912.h n : ℝ) / ((n : ℝ) / Real.log n) ^ (1 / 2 : ℝ))
    atTop (𝓝 L)

lemma g_pos : ∀ᶠ n : ℕ in atTop, 0 < ((n : ℝ) / Real.log n) ^ (1 / 2 : ℝ) := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < Real.log n := Real.log_pos hn'
  exact Real.rpow_pos_of_pos (div_pos (by linarith) hlog) _

theorem main : H1 → H2 → type_of% @Erdos912.erdos_912 := by
  rintro ⟨c, hc, hlow⟩ ⟨L, hL⟩
  set g : ℕ → ℝ := fun n => ((n : ℝ) / Real.log n) ^ (1 / 2 : ℝ) with hg
  have hcL : c ≤ L := by
    apply ge_of_tendsto hL
    filter_upwards [hlow, g_pos] with n h1 h2
    rw [le_div_iff₀ h2]
    exact h1
  have hLpos : 0 < L := lt_of_lt_of_le hc hcL
  refine ⟨L, hLpos, ?_⟩
  refine isEquivalent_of_tendsto_one ?_
  have h2 : Tendsto (fun n : ℕ => (Erdos912.h n : ℝ) / g n / L) atTop (𝓝 (L / L)) :=
    hL.div_const L
  rw [div_self hLpos.ne'] at h2
  refine h2.congr' ?_
  filter_upwards [g_pos] with n hn
  simp only [Pi.div_apply, hg]
  rw [div_div, mul_comm]

end OMA.R_Erdos912_erdos_912_R1
