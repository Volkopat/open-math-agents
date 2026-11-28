import OMAReductions.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H2_R1
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Count solvable permutation groups through nilpotent subgroup seeds
and a bounded list of additional generators. -/

namespace OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H2_R1_H1_R1

private theorem subgroup_count_of_seed {G : Type} [Group G] [Finite G] (k : ℕ)
    (hgen : ∀ S : Subgroup G, ∃ (H : Subgroup G) (x : Fin k → G),
      Group.IsNilpotent H ∧ H ⊔ Subgroup.closure (Set.range x) = S) :
    Nat.card (Subgroup G) ≤
      Nat.card {H : Subgroup G // Group.IsNilpotent H} * (Nat.card G) ^ k := by
  let F : {H : Subgroup G // Group.IsNilpotent H} × (Fin k → G) → Subgroup G :=
    fun p => p.1.1 ⊔ Subgroup.closure (Set.range p.2)
  have hF : Function.Surjective F := by
    intro S
    obtain ⟨H, x, hn, he⟩ := hgen S
    exact ⟨⟨⟨H, hn⟩, x⟩, he⟩
  simpa only [Nat.card_prod, Nat.card_fun, Nat.card_fin] using
    (Nat.card_le_card_of_surjective F hF)

private theorem times_sqrt_monotone : Monotone (fun n : ℕ => (n : ℝ) * Real.sqrt n) := by
  intro m n h
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast h
  exact mul_le_mul hmn (Real.sqrt_le_sqrt hmn) (Real.sqrt_nonneg _) (Nat.cast_nonneg _)

/-- Theorem 7 applied to short-orbit subgroups using the socle-length bound
for subdirect products and the bound for abelian sections. -/
def H1 : Prop :=
  ∀ C : ℕ, ∃ B : ℝ, 0 ≤ B ∧
    ∀ (n : ℕ) (D : Subgroup (Equiv.Perm (Fin n))), Group.IsSolvable D →
      (∀ i : Fin n, Nat.card (MulAction.orbit D i) < C) →
      ∃ k : ℕ, (k : ℝ) ≤ B * Real.sqrt n ∧
        ∀ S : Subgroup D, ∃ (A : Subgroup D) (x : Fin k → D),
          Group.IsNilpotent A ∧ A ⊔ Subgroup.closure (Set.range x) = S

/-- The small-orbit counting transfer from Theorem 6.4, at the target
quadratic coefficient and a fixed sufficiently large orbit threshold. -/
def H2 : Prop :=
  ∃ (C : ℕ) (K : ℝ), 0 ≤ K ∧ ∀ g : ℕ → ℝ, Monotone g →
    (∀ (n : ℕ) (D : Subgroup (Equiv.Perm (Fin n))), Group.IsSolvable D →
      (∀ i : Fin n, Nat.card (MulAction.orbit D i) < C) →
      (Nat.card (Subgroup D) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16 + g n)) →
    ∀ n : ℕ, (Nat.card {A : Subgroup (Equiv.Perm (Fin n)) // Group.IsSolvable A} : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16 + g n + K * n * Real.sqrt n)

/-- The weaker order bound furnished by Dixon's exponential estimate. -/
def H3 : Prop :=
  ∀ (n : ℕ) (D : Subgroup (Equiv.Perm (Fin n))), Group.IsSolvable D →
    (Nat.card D : ℝ) ≤ (2 : ℝ) ^ (2 * (n : ℝ))

theorem main : H1 → H2 → H3 →
    OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H2_R1.H1 := by
  intro hGen hTransfer hOrder
  obtain ⟨C, K, hK, hTrans⟩ := hTransfer
  obtain ⟨B, hB, hBgen⟩ := hGen C
  refine ⟨C, 2 * B + K, by positivity, ?_⟩
  intro g hg hNil
  let g' (n : ℕ) : ℝ := g n + 2 * B * ((n : ℝ) * Real.sqrt n)
  have hg' : Monotone g' := hg.add (times_sqrt_monotone.const_mul (by positivity))
  have hBound (n : ℕ) (D : Subgroup (Equiv.Perm (Fin n))) (hD : Group.IsSolvable D)
      (hOrbit : ∀ i : Fin n, Nat.card (MulAction.orbit D i) < C) :
      (Nat.card (Subgroup D) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16 + g' n) := by
    obtain ⟨k, hk, hgen⟩ := hBgen n D hD hOrbit
    have hcount : (Nat.card (Subgroup D) : ℝ) ≤
        (Nat.card {H : Subgroup D // Group.IsNilpotent H} : ℝ) * (Nat.card D : ℝ) ^ k := by
      exact_mod_cast subgroup_count_of_seed k hgen
    have hKpower : (Nat.card D : ℝ) ^ k ≤ (2 : ℝ) ^ (2 * B * ((n : ℝ) * Real.sqrt n)) := by
      calc
        _ ≤ ((2 : ℝ) ^ (2 * (n : ℝ))) ^ k := pow_le_pow_left₀ (by positivity) (hOrder n D hD) _
        _ = (2 : ℝ) ^ ((2 * (n : ℝ)) * (k : ℝ)) := by
          rw [Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)) (2 * (n : ℝ)) (k : ℝ),
            Real.rpow_natCast ((2 : ℝ) ^ (2 * (n : ℝ))) k]
        _ ≤ _ := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          calc
            _ ≤ (2 * (n : ℝ)) * (B * Real.sqrt n) :=
              mul_le_mul_of_nonneg_left hk (by positivity)
            _ = _ := by ring
    calc
      _ ≤ (Nat.card {H : Subgroup D // Group.IsNilpotent H} : ℝ) * (Nat.card D : ℝ) ^ k := hcount
      _ ≤ (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16 + g n) *
          (2 : ℝ) ^ (2 * B * ((n : ℝ) * Real.sqrt n)) :=
        mul_le_mul (hNil n D hOrbit) hKpower (by positivity) (by positivity)
      _ = (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16 + g' n) := by
        rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
        congr 1
        dsimp only [g']
        ring
  intro n
  have h := hTrans g' hg' hBound n
  convert h using 2
  dsimp only [g']
  ring

end OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H2_R1_H1_R1
