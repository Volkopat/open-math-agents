import FormalConjectures.ErdosProblems.«390»

-- Reduction Erdos390.erdos_390.R1 of Erdős Problem 390
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Sketch. Write u(n) = f(n) - 2n and g(n) = n / log n. The problem asks for a constant c with
-- u ~ c * g. We separate the order of magnitude from the existence of the constant:
-- * H1 (known): the lower half of the Erdős–Guy–Selfridge bound u(n) ≫ n / log n [EGS82]. It is
--   the lower half of `Erdos390.erdos_390.variants.theta`, already formalized in this repository.
-- * H2 (open): the ratio u(n) / g(n) converges to some real limit L.
-- Then L ≥ c > 0 by H1, and u / (L * g) = (u / g) / L → 1, so u ~ L * g.

namespace OMA.R_Erdos390_erdos_390_R1

open Filter Asymptotics Topology

def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    c * ((n : ℝ) / Real.log n) ≤ (Erdos390.f n : ℝ) - 2 * n

def H2 : Prop :=
  ∃ L : ℝ, Tendsto (fun n : ℕ => ((Erdos390.f n : ℝ) - 2 * n) / ((n : ℝ) / Real.log n))
    atTop (𝓝 L)

lemma g_pos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) / Real.log n := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < Real.log n := Real.log_pos hn'
  exact div_pos (by linarith) hlog

theorem main : H1 → H2 → type_of% @Erdos390.erdos_390 := by
  rintro ⟨c, hc, hlow⟩ ⟨L, hL⟩
  have hcL : c ≤ L := by
    apply ge_of_tendsto hL
    filter_upwards [hlow, g_pos] with n h1 h2
    rw [le_div_iff₀ h2]
    exact h1
  have hLpos : 0 < L := lt_of_lt_of_le hc hcL
  refine ⟨L, ?_⟩
  refine isEquivalent_of_tendsto_one ?_
  have h2 := hL.div_const L
  rw [div_self hLpos.ne'] at h2
  refine h2.congr' ?_
  filter_upwards [g_pos] with n hn
  simp only [Pi.div_apply]
  field_simp

end OMA.R_Erdos390_erdos_390_R1
