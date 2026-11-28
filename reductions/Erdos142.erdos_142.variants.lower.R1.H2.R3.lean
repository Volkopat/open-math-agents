import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1

/-!
# Stretched-exponential input for the logarithmic power saving

H1 is the k >= 4 case of Theorem 1.1 in OpenAI, Quasipolynomial Bounds for
Arithmetic Progressions, 23 September 2026 (preprint, not refereed):
r_k(N) <= C_k N exp(-c_k (log N)^eps_k) for every N >= 2.
Green and Tao, New bounds for Szemeredi's theorem, III, Mathematika 63
(2017) 944-1040, DOI 10.1112/S0025579317000316 (refereed journal article),
give a positive but unspecified power of log for k = 4 only.
Leng, Sah and Sawhney, Improved Bounds for Szemeredi's Theorem,
arXiv:2402.17995 (preprint), give N exp(-(log log N)^c) with 0 < c < 1
for k >= 5. Section 1.2 of the OpenAI preprint records that those two
bounds do not reach an exponent above 1. They are not used as hypotheses.

H2 is the elementary comparison that a stretched exponential beats every
polylogarithm. The bridge below specialises it at the real power 1 + 1.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3

open Erdos142 Filter Real
open scoped Topology

/-- Stretched-exponential saving for every progression length at least four. -/
def H1 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∃ C c ε : ℝ, 0 < C ∧ 0 < c ∧ 0 < ε ∧
    ∀ N : ℕ, 2 ≤ N →
      (r k N : ℝ) ≤ C * (N : ℝ) * exp (-c * log (N : ℝ) ^ ε)

/-- A stretched exponential is eventually smaller than every negative power of log. -/
def H2 : Prop :=
  ∀ A C c ε : ℝ, 0 < A → 0 < C → 0 < c → 0 < ε →
    ∀ᶠ N : ℕ in atTop,
      C * exp (-c * log (N : ℝ) ^ ε) ≤ 1 / log (N : ℝ) ^ A

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1.H2 := by
  intro hBound hCompare k hk
  obtain ⟨C, c, ε, hC, hc, hε, hAll⟩ := hBound k hk
  refine ⟨1, by norm_num, ?_⟩
  have hA : (0 : ℝ) < 1 + 1 := by norm_num
  have hEv := hCompare (1 + 1) C c ε hA hC hc hε
  filter_upwards [hEv, eventually_ge_atTop 2] with N hCmp hN2
  have hNpos : (0 : ℝ) ≤ N := by exact_mod_cast (Nat.zero_le N)
  have hr : (r k N : ℝ) ≤ C * (N : ℝ) * exp (-c * log (N : ℝ) ^ ε) := hAll N hN2
  calc
    (r k N : ℝ) ≤ C * (N : ℝ) * exp (-c * log (N : ℝ) ^ ε) := hr
    _ = (N : ℝ) * (C * exp (-c * log (N : ℝ) ^ ε)) := by ring
    _ ≤ (N : ℝ) * (1 / log (N : ℝ) ^ ((1 : ℝ) + 1)) := mul_le_mul_of_nonneg_left hCmp hNpos
    _ = (N : ℝ) / log (N : ℝ) ^ ((1 : ℝ) + 1) := by rw [mul_one_div]

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3
