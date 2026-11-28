import FormalConjectures.ErdosProblems.«5»
import Mathlib.Data.ZMod.Basic

-- Reduction Erdos5.erdos_5.variants.banks_freiberg_maynard.R2 of Erdős Problem 5 — banks freiberg maynard
-- Credit: @hiattco
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

open Filter Set
open scoped Topology

namespace OMA.R_Erdos5_erdos_5_variants_banks_freiberg_maynard_R2

-- The sieve need only handle strictly increasing integer shifts on a common grid.
def H1 : Prop := ∀ (n : ℕ) (a : Fin 9 → ℕ), StrictMono a →
    ∃ i j, i < j ∧ (a j : ℝ) / ((n : ℝ) + 1) - (a i : ℝ) / ((n : ℝ) + 1) ∈
      Erdos5.limitPointSet

-- A weakly ordered tuple can have repeated coordinates.
def H2 : Prop := ∀ (β : Fin 9 → ℝ), (∀ i, 0 ≤ β i) → Monotone β →
    ∃ a : ℕ → Fin 9 → ℕ, (∀ n, StrictMono (a n)) ∧
      Tendsto (fun n : ℕ => fun i : Fin 9 => (a n i : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 β)

lemma isClosed_bfm_configurations :
    IsClosed {β : Fin 9 → ℝ | ∃ i j, i < j ∧ β j - β i ∈ Erdos5.limitPointSet} := by
  let P := {p : Fin 9 × Fin 9 // p.1 < p.2}
  let C (p : P) : Set (Fin 9 → ℝ) :=
    (fun β => β p.val.2 - β p.val.1) ⁻¹' Erdos5.limitPointSet
  have hC (p : P) : IsClosed (C p) :=
    Erdos5.isClosed_limitPointSet.preimage
      ((continuous_apply p.val.2).sub (continuous_apply p.val.1))
  have hEq : {β : Fin 9 → ℝ | ∃ i j, i < j ∧ β j - β i ∈ Erdos5.limitPointSet} =
      ⋃ p : P, C p := by
    ext β
    constructor
    · rintro ⟨i, j, hij, hβ⟩
      exact mem_iUnion.mpr ⟨⟨(i,j), hij⟩, hβ⟩
    · intro h
      obtain ⟨p, hp⟩ := mem_iUnion.mp h
      exact ⟨p.val.1, p.val.2, p.property, hp⟩
  rw [hEq]
  exact isClosed_iUnion_of_finite hC

theorem main : H1 → H2 → type_of% @Erdos5.erdos_5.variants.banks_freiberg_maynard := by
  intro hGrid hApprox β hβ hMono
  obtain ⟨a, ha, hlim⟩ := hApprox β hβ hMono
  apply isClosed_bfm_configurations.mem_of_tendsto hlim
  exact Filter.Eventually.of_forall fun n => hGrid n (a n) (ha n)

private theorem grid_mesh_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp h

private lemma grid_approx (β : Fin 9 → ℝ) (hβ : ∀ i, 0 ≤ β i)
    (hmono : Monotone β) :
    ∃ a : ℕ → Fin 9 → ℕ, (∀ n, Monotone (a n)) ∧
      Tendsto (fun n : ℕ => fun i : Fin 9 => (a n i : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 β) := by
  let a (n : ℕ) (i : Fin 9) := ⌊β i * ((n : ℝ) + 1)⌋₊
  refine ⟨a, ?_, ?_⟩
  · intro n i j hij
    exact Nat.floor_mono (mul_le_mul_of_nonneg_right (hmono hij) (add_nonneg (Nat.cast_nonneg n) zero_le_one))
  · apply tendsto_pi_nhds.mpr
    intro i
    have tiny : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      grid_mesh_tendsto_zero
    have base : Tendsto (fun _ : ℕ => β i) atTop (𝓝 (β i)) := tendsto_const_nhds
    have low : Tendsto (fun n : ℕ => β i - 1 / ((n : ℝ) + 1)) atTop (𝓝 (β i)) := by
      simpa only [sub_zero] using base.sub tiny
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le low base
    · intro n
      have hd : 0 < (n : ℝ) + 1 := add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
      apply (le_div_iff₀ hd).mpr
      rw [sub_mul, div_mul_cancel₀ _ hd.ne']
      have ht : β i * ((n : ℝ) + 1) < (a n i : ℝ) + 1 := by
        simpa only [a, Nat.cast_add, Nat.cast_one] using
          Nat.lt_floor_add_one (β i * ((n : ℝ) + 1))
      exact (sub_le_iff_le_add).mpr ht.le
    · intro n
      have hd : 0 < (n : ℝ) + 1 := add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
      exact (div_le_iff₀ hd).mpr (Nat.floor_le (mul_nonneg (hβ i) hd.le))

/-- Adding the index to each rounded coordinate preserves convergence and separates ties. -/
theorem strict_grid_approx : H2 := by
  intro β hβ hmono
  obtain ⟨a, ha, hlim⟩ := grid_approx β hβ hmono
  refine ⟨fun n i => a n i + i.val, ?_, ?_⟩
  · intro n i j hij
    exact Nat.add_lt_add_of_le_of_lt (ha n hij.le) (Fin.lt_def.mp hij)
  · apply tendsto_pi_nhds.mpr
    intro i
    have tiny : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      grid_mesh_tendsto_zero
    have drift : Tendsto (fun n : ℕ => (i.val : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, one_mul, mul_zero] using tiny.const_mul (i.val : ℝ)
    have coord : Tendsto (fun n : ℕ => (a n i : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (β i)) :=
      tendsto_pi_nhds.mp hlim i
    simpa only [Nat.cast_add, add_div, add_zero] using coord.add drift

/-- Only the strictly increasing rational-grid sieve input remains. -/
theorem of_grid (h : H1) : type_of% @Erdos5.erdos_5.variants.banks_freiberg_maynard :=
  main h strict_grid_approx

/-- These shifts omit a residue modulo every prime. The primes at most nine divide
210, and nine residues cannot cover a larger prime field. -/
theorem admissible_nine (a : Fin 9 → ℕ) (ha : ∀ i, 210 ∣ a i) :
    ∀ p : ℕ, p.Prime → ∃ x : ℕ, ∀ i, ¬ p ∣ x + a i := by
  intro p hp
  let _ : Fact p.Prime := ⟨hp⟩
  have missing : ∃ y : ZMod p, ∀ i, (a i : ZMod p) ≠ y := by
    by_cases hsmall : p ≤ 9
    · have small_primes : ∀ j : Fin 10, j.val.Prime → j.val ∣ 210 := by decide
      have hdiv := small_primes ⟨p, by omega⟩ hp
      refine ⟨1, fun i => ?_⟩
      have hd : (p : ℤ) ∣ (a i : ℤ) := by exact_mod_cast hdiv.trans (ha i)
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
      simpa using hz.trans_ne (zero_ne_one : (0 : ZMod p) ≠ 1)
    · by_contra! hfull
      have hsurj : Function.Surjective (fun i => (a i : ZMod p)) := hfull
      have hcard := Fintype.card_le_of_surjective _ hsurj
      rw [ZMod.card, Fintype.card_fin] at hcard
      omega
  obtain ⟨y, hy⟩ := missing
  refine ⟨(-y).val, fun i hbad => hy i ?_⟩
  have hd : (p : ℤ) ∣ ((-y).val : ℤ) + (a i : ℤ) := by exact_mod_cast hbad
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
  rw [Int.cast_add, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val] at hz
  exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg, add_comm] using hz)

/-- It suffices to treat admissible integer shifts starting at zero, all divisible by 210.
Rescaling the common denominator preserves every difference on the original rational grid. -/
theorem of_admissible_grid
    (sieve : ∀ (d : ℕ) (a : Fin 9 → ℕ), 0 < d → 210 ∣ d →
      a 0 = 0 → StrictMono a → (∀ i, 210 ∣ a i) →
      (∀ p : ℕ, p.Prime → ∃ x : ℕ, ∀ i, ¬ p ∣ x + a i) →
        ∃ i j, i < j ∧ ((a j : ℝ) - (a i : ℝ)) / d ∈ Erdos5.limitPointSet) :
    type_of% @Erdos5.erdos_5.variants.banks_freiberg_maynard := by
  apply of_grid
  intro n a ha
  let b (i : Fin 9) := 210 * (a i - a 0)
  have hbase (i : Fin 9) : a 0 ≤ a i := ha.monotone (Fin.zero_le i)
  have hmono : StrictMono b := by
    intro i j hij
    have h := ha hij
    have h₀ := hbase i
    have h₁ : a i - a 0 < a j - a 0 := by omega
    exact Nat.mul_lt_mul_of_pos_left h₁ (by decide)
  have hdiv (i : Fin 9) : 210 ∣ b i := dvd_mul_right _ _
  obtain ⟨i, j, hij, hgap⟩ := sieve (210*(n+1)) b (by omega)
    (dvd_mul_right _ _) (by simp [b]) hmono hdiv (admissible_nine b hdiv)
  refine ⟨i, j, hij, ?_⟩
  have difference :
      ((b j : ℝ) - (b i : ℝ)) / ((210*(n+1) : ℕ) : ℝ) =
      (a j : ℝ) / ((n : ℝ)+1) - (a i : ℝ) / ((n : ℝ)+1) := by
    simp only [b, Nat.cast_mul, Nat.cast_sub (hbase _), Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat]
    rw [← mul_sub, mul_div_mul_left _ _ (by norm_num : (210 : ℝ) ≠ 0), ← sub_div]
    ring_nf
  rwa [difference] at hgap

end OMA.R_Erdos5_erdos_5_variants_banks_freiberg_maynard_R2
