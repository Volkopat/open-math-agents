import FormalConjectures.ErdosProblems.«1013»

-- Reduction Erdos1013.erdos_1013.parts.ii.R1 of Erdős Problem 1013 — ii
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

open Filter

namespace OMA.R_Erdos1013_erdos_1013_parts_ii_R1

def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧
    Tendsto (fun k : ℕ => (Erdos1013.h3 k : ℝ) / (c * (k : ℝ) ^ 2 * Real.log k)) atTop (nhds 1)

def H2 : Prop :=
  ∀ c : ℝ, 0 < c →
    Tendsto (fun k : ℕ =>
      (c * ((k + 1 : ℕ) : ℝ) ^ 2 * Real.log ((k + 1 : ℕ) : ℝ)) /
        (c * (k : ℝ) ^ 2 * Real.log k)) atTop (nhds 1)

def H3 : Prop :=
  ∀ a g : ℕ → ℝ,
    Tendsto (fun k => a k / g k) atTop (nhds 1) →
    Tendsto (fun k => g (k + 1) / g k) atTop (nhds 1) →
    (∀ᶠ k in atTop, g k ≠ 0) →
    Tendsto (fun k => a (k + 1) / a k) atTop (nhds 1)

theorem main : H1 → H2 → H3 → type_of% @Erdos1013.erdos_1013.parts.ii := by
  intro h1 h2 h3
  rcases h1 with ⟨c, hcpos, hc⟩
  let g : ℕ → ℝ := fun k => c * (k : ℝ) ^ 2 * Real.log k
  have hg0 : ∀ᶠ k in atTop, g k ≠ 0 := by
    filter_upwards [Filter.eventually_gt_atTop 1] with k hk
    dsimp [g]
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans Nat.zero_lt_one hk))
    have hkR : 1 < (k : ℝ) := by exact_mod_cast hk
    have hlogk : Real.log (k : ℝ) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (ne_of_gt hkR)
    exact mul_ne_zero (mul_ne_zero (ne_of_gt hcpos) (pow_ne_zero 2 hk0)) hlogk
  have hratio_g : Tendsto (fun k => g (k + 1) / g k) atTop (nhds 1) := by
    dsimp [g]
    exact h2 c hcpos
  have hratio_a : Tendsto (fun k => (Erdos1013.h3 k : ℝ) / g k) atTop (nhds 1) := by
    simpa [g] using hc
  have hres := h3 (fun k => (Erdos1013.h3 k : ℝ)) g hratio_a hratio_g hg0
  simpa [g] using hres

end OMA.R_Erdos1013_erdos_1013_parts_ii_R1
