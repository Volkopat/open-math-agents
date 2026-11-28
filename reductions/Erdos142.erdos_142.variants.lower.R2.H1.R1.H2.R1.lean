import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1
import Mathlib

/-!
# Summable extremal densities from the quasipolynomial bound

The target is step H2 of reduction R2.H1.R1 of Erdős 142: for every length k at least four the
normalized extremal numbers r_k(4^j) / 4^j are summable. With the steps already proved this is
the only open leaf on the route R2 to the variant r_k(N) = o(N / log N).

H1 is the published quantitative density theorem for lengths at least four, stated for
arbitrary finite sets with no project definitions in it: a subset of [1, N] with no k-term
progression of positive step has at most C N exp(-c (log log N)^(1+η)) elements. This is the
content of OAI.Erdos3.QuantitativeDensityBound (openai/math, Results/Conclusions.lean, theorem
manuscriptQuantitativeDensityTheorem), where the same bound is put on the largest such set.
It is the one piece that needs the external proof.

H2 is a self-contained statement of real analysis with no arithmetic progressions in it: the
saving exp(-c (log log N)^(1+η)) is summable along the scales N = 4^j. For large j the term is
at most j^(-2), because log (log (4^j)) is at least log j and (log j)^η grows without bound.

The glue below takes a largest progression-free subset of [1, 4^(j+1)], applies H1 to it, and
compares the two series. The lemmas apFree_iff and exists_maximizer are copied from reduction
R3 of Erdős 142 (credit @mucoucah).
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1

open Erdos142 Filter

/-- The quasipolynomial bound for every progression length at least four. -/
def H1 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∃ C c η : ℝ, 0 < C ∧ 0 < c ∧ 0 < η ∧
    ∀ (N : ℕ) (S : Finset ℕ), 3 ≤ N → S ⊆ Finset.Icc 1 N →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
      (S.card : ℝ) ≤ C * N * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η))

/-- The saving is summable along the scales 4^j. -/
def H2 : Prop :=
  ∀ c η : ℝ, 0 < c → 0 < η →
    Summable (fun j : ℕ ↦ Real.exp (-c * (Real.log (Real.log ((4 : ℝ) ^ j))) ^ (1 + η)))

lemma apFree_iff {A : Set ℕ} {k : ℕ} (hk : 1 < k) :
    A.IsAPOfLengthFree k ↔ ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  have hk' : (1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast hk
  constructor
  · rintro hA ⟨a, d, hd, hterms⟩
    let f (i : ℕ) := a + i * d
    let T := (Finset.range k).image f
    have hf : Function.Injective f := fun i j hij =>
      Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
    have hT : ((T : Finset ℕ) : Set ℕ) = {a + n • d | (n : ℕ) (_ : n < (k : ℕ∞))} := by
      ext x
      simp [T, f]
    have hcard : T.card = k := by simp [T, Finset.card_image_of_injective _ hf]
    have hsub : (T : Set ℕ) ⊆ A := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hterms i (Finset.mem_range.mp hi)
    exact hk'.not_ge (hA _ hsub ⟨a, d, by simp [hcard], hT⟩)
  · intro hno T hsub hT
    obtain ⟨a, d, hcard, hterms⟩ := hT
    have hmem (i : ℕ) (hi : i < k) : a + i * d ∈ T := by
      rw [hterms]
      exact ⟨i, by exact_mod_cast hi, by simp⟩
    have hd : 0 < d := by
      by_contra! h
      have he : d = 0 := Nat.eq_zero_of_le_zero h
      have hs : T = {a} := by
        apply Set.Subset.antisymm
        · rw [hterms, he]
          rintro _ ⟨i, -, rfl⟩
          simp
        · apply Set.singleton_subset_iff.mpr
          simpa using hmem 0 (by omega)
      rw [hs] at hcard
      exact hk'.ne (by simpa using hcard)
    exact (hno ⟨a, d, hd, fun i hi => hsub (hmem i hi)⟩).elim

lemma exists_maximizer {k : ℕ} (hk : 1 < k) (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ (S : Set ℕ).IsAPOfLengthFree k ∧
      r k N = S.card := by
  let C : Set ℕ := {m | ∃ S : Finset ℕ, ∃ _ : S ⊆ Finset.Icc 1 N,
    ∃ _ : (S : Set ℕ).IsAPOfLengthFree k, S.card = m}
  have hz : 0 ∈ C := by
    refine ⟨∅, Finset.empty_subset _, (apFree_iff hk).mpr ?_, rfl⟩
    rintro ⟨a, d, -, h⟩
    simpa using h 0 (by omega)
  have hb : BddAbove C := by
    refine ⟨N, ?_⟩
    rintro _ ⟨S, hS, -, rfl⟩
    simpa using Finset.card_le_card hS
  obtain ⟨S, hS, hf, he⟩ := Nat.sSup_mem ⟨0, hz⟩ hb
  exact ⟨S, hS, hf, he.symm⟩

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1.H2 := by
  intro h1 h2 k hk
  obtain ⟨C, c, η, hC, hc, hη, hb⟩ := h1 k hk
  have hk1 : 1 < k := by omega
  have hbr : ∀ N : ℕ, 3 ≤ N →
      (r k N : ℝ) ≤ C * N * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η)) := by
    intro N hN
    obtain ⟨S, hS, hf, hcard⟩ := exists_maximizer hk1 N
    rw [hcard]
    exact hb N S hN hS ((apFree_iff hk1).mp hf)
  have hs : Summable (fun j : ℕ ↦
      C * Real.exp (-c * (Real.log (Real.log ((4 : ℝ) ^ j))) ^ (1 + η))) :=
    (h2 c η hc hη).mul_left C
  have hs' : Summable (fun j : ℕ ↦
      C * Real.exp (-c * (Real.log (Real.log ((4 : ℝ) ^ (j + 1)))) ^ (1 + η))) :=
    (summable_nat_add_iff 1).mpr hs
  have key : ∀ j : ℕ, (r k (4 ^ (j + 1)) : ℝ) / (4 : ℝ) ^ (j + 1) ≤
      C * Real.exp (-c * (Real.log (Real.log ((4 : ℝ) ^ (j + 1)))) ^ (1 + η)) := by
    intro j
    have h3 : 3 ≤ 4 ^ (j + 1) :=
      calc 3 ≤ 4 ^ 1 := by norm_num
        _ ≤ 4 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hb' := hbr (4 ^ (j + 1)) h3
    push_cast at hb'
    have hpos : (0 : ℝ) < (4 : ℝ) ^ (j + 1) := by positivity
    rw [div_le_iff₀ hpos]
    calc (r k (4 ^ (j + 1)) : ℝ)
        ≤ C * (4 : ℝ) ^ (j + 1) *
            Real.exp (-c * (Real.log (Real.log ((4 : ℝ) ^ (j + 1)))) ^ (1 + η)) := hb'
      _ = C * Real.exp (-c * (Real.log (Real.log ((4 : ℝ) ^ (j + 1)))) ^ (1 + η)) *
            (4 : ℝ) ^ (j + 1) := by ring
  have hshift : Summable (fun j : ℕ ↦ (r k (4 ^ (j + 1)) : ℝ) / (4 : ℝ) ^ (j + 1)) :=
    Summable.of_nonneg_of_le (fun j ↦ by positivity) key hs'
  exact (summable_nat_add_iff 1).mp hshift

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1
