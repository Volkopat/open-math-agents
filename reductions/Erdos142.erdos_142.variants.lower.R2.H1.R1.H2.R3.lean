import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1
import Mathlib.Analysis.PSeries

/-!
A finite density theorem on the intervals of length 4^(2^m) suffices.
There are only doubly exponentially spaced intervals to check, and the
required denominator is proportional to log N times (log log N)^2.
Cauchy condensation transfers their estimates to every geometric scale.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R3

open Erdos142 Filter OMA.R_Erdos142_erdos_142_variants_lower_R2

/-- Every sufficiently large test interval forces a positive-step progression
when a finite set exceeds the stated cardinality threshold. -/
def H1 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∀ᶠ m : ℕ in atTop, ∀ S : Finset ℕ,
    S ⊆ Finset.Icc 1 (4^(2^m)) → 4^(2^m) < 2^m * S.card * (m+1)^2 →
    ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a+i*d ∈ S

/-- An inverse-square majorant on the condensed sequence suffices for
summability of the original nonnegative decreasing sequence. -/
def H2 : Prop :=
  ∀ f : ℕ → ℝ, (∀ j, 0 ≤ f j) → Antitone f →
    (∀ᶠ m : ℕ in atTop, (2 : ℝ)^m * f (2^m) ≤ 1 / ((m : ℝ)+1)^2) → Summable f

-- uses note #178025
lemma condensation_bridge : H2 := by
  intro d hd0 hd hbound
  rw [← summable_condensed_iff_of_nonneg hd0 (fun _ _ _ h => hd h)]
  have hsum : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ 2) := by
    have h2 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h2
  obtain ⟨M, hM⟩ := eventually_atTop.1 hbound
  rw [← summable_nat_add_iff M]
  refine Summable.of_nonneg_of_le (fun m => by have := hd0 (2 ^ (m + M)); positivity)
    (fun m => ?_) ((summable_nat_add_iff M).mpr hsum)
  simpa [mul_comm] using hM (m + M) (Nat.le_add_left M m)

lemma density_decreases (k : ℕ) :
    Antitone (fun j : ℕ => (r k (4^j) : ℝ) / (4:ℝ)^j) := by
  intro i j hij
  have h := dyadic_density_antitone k (Nat.mul_le_mul_left 2 hij)
  dsimp only at h
  norm_num [pow_mul] at h ⊢
  exact h

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1.H2 := by
  intro hAP hseries k hk
  apply hseries _ (fun _ => by positivity) (density_decreases k)
  filter_upwards [hAP k hk] with m hm
  obtain ⟨S,hS,hfree,hcard⟩ := extremizer (show 1 < k by omega) (4^(2^m))
  have hc : 2^m * r k (4^(2^m)) * (m+1)^2 ≤ 4^(2^m) := by
    rw [← hcard]
    by_contra! h
    exact no_positive_step (by omega) hfree (hm S hS h)
  have hreal : (2:ℝ)^m * (r k (4^(2^m)) : ℝ) * ((m:ℝ)+1)^2 ≤ (4:ℝ)^(2^m : ℕ) := by
    exact_mod_cast hc
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact hreal

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R3
