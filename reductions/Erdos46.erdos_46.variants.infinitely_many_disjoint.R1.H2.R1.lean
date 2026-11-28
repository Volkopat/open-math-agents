import OMAReductions.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R1
import Mathlib.Analysis.Fourier.ZMod

/-! The finite orthogonality step in Croot, On a coloring conjecture
about unit fractions, Annals of Mathematics 157 (2003), equation (1.3).
The inputs are the subset selection in Proposition 1 and the
Fourier estimate on the resulting set. -/

namespace OMA.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R1_H2_R1

open Finset
open scoped Classical

private theorem char_product {L : ℕ} [NeZero L] (S : Finset ℕ) (w : ℕ → ZMod L) :
    (∏ d ∈ S, ZMod.stdAddChar (w d)) = ZMod.stdAddChar (∑ d ∈ S, w d) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert d S hd ih =>
    rw [Finset.prod_insert hd, Finset.sum_insert hd, ih, AddChar.map_add_eq_mul]

private theorem character_count (L : ℕ) [NeZero L] (D : Finset ℕ) (w : ℕ → ZMod L) :
    (∑ h : ZMod L, (∏ d ∈ D, (1 + ZMod.stdAddChar (h * w d)))).re =
      (L : ℝ) * ((D.powerset.filter (fun S ↦ ∑ d ∈ S, w d = 0)).card : ℝ) := by
  classical
  let Q := D.powerset.filter (fun S ↦ ∑ d ∈ S, w d = 0)
  have E (h : ZMod L) :
      (∏ d ∈ D, (1 + ZMod.stdAddChar (h * w d))) =
        ∑ S ∈ D.powerset, ZMod.stdAddChar (h * (∑ d ∈ S, w d)) := by
    rw [Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro S _
    rw [Finset.mul_sum]
    exact char_product S (fun d ↦ h * w d)
  have ortho (s : ZMod L) :
      (∑ h : ZMod L, ZMod.stdAddChar (h * s)) = if s = 0 then (L : ℂ) else 0 := by
    rw [AddChar.sum_mulShift s (ZMod.isPrimitive_stdAddChar L), ZMod.card]
    split_ifs <;> simp
  simp_rw [E]
  rw [Finset.sum_comm]
  simp_rw [ortho]
  rw [← Finset.sum_filter]
  change (∑ _ ∈ Q, (L : ℂ)).re = _
  simp [Q, mul_comm]

private theorem extract (D : Finset ℕ) (L : ℕ) [NeZero L]
    (hL : L = D.lcm id) (hp : ∀ d ∈ D, 0 < d)
    (mass : (∑ d ∈ D, (1 / d : ℚ)) < 2)
    (fourier : (L : ℝ) <
      (∑ h : ZMod L, ∏ d ∈ D, (1 + ZMod.stdAddChar (h * ((L / d : ℕ) : ZMod L)))).re) :
    ∃ S ⊆ D, (∑ d ∈ S, (1 / d : ℚ)) = 1 := by
  classical
  let w (d : ℕ) : ZMod L := (L / d : ℕ)
  let Q := D.powerset.filter (fun S ↦ ∑ d ∈ S, w d = 0)
  have counted := character_count L D w
  rw [show (∑ h : ZMod L, ∏ d ∈ D, (1 + ZMod.stdAddChar (h * w d))).re =
        (L : ℝ) * (Q.card : ℝ) from counted] at fourier
  have posL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have posR : (0 : ℝ) < L := by exact_mod_cast posL
  have hQ : 1 < Q.card := by
    have hc : (L : ℝ) * 1 < (L : ℝ) * (Q.card : ℝ) := by simpa using fourier
    have := (mul_lt_mul_iff_right₀ posR).mp hc
    exact_mod_cast this
  have witness : ∃ S ∈ Q, S.Nonempty := by
    by_contra! h
    have sub : Q ⊆ {∅} := by
      intro S hS
      simpa using h S hS
    have := Finset.card_le_card sub
    simp at this
    omega
  obtain ⟨S, hS, hne⟩ := witness
  have hD : S ⊆ D := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hmod : (∑ d ∈ S, w d) = 0 := (Finset.mem_filter.mp hS).2
  have hdvd : L ∣ ∑ d ∈ S, L / d :=
    (ZMod.natCast_eq_zero_iff _ _).mp (by simpa only [Nat.cast_sum, w] using hmod)
  obtain ⟨k, hk⟩ := hdvd
  have terms : (∑ d ∈ S, (1 / d : ℚ)) * (L : ℚ) = ∑ d ∈ S, ((L / d : ℕ) : ℚ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    have dL : d ∣ L := hL.symm ▸ (Finset.dvd_lcm (f := id) (hD hd))
    have dh : (d : ℚ) ≠ 0 := by exact_mod_cast (hp d (hD hd)).ne'
    rw [div_mul_eq_mul_div, one_mul]
    symm
    apply (eq_div_iff dh).2
    exact_mod_cast Nat.div_mul_cancel dL
  have integral : (∑ d ∈ S, (1 / d : ℚ)) = k := by
    apply mul_right_cancel₀ (by exact_mod_cast posL.ne' : (L : ℚ) ≠ 0)
    have hk' : (∑ d ∈ S, ((L / d : ℕ) : ℚ)) = (L : ℚ) * k := by exact_mod_cast hk
    simpa only [mul_comm (k : ℚ)] using terms.trans hk'
  have hp' (d : ℕ) (hd : d ∈ S) : 0 < (1 / d : ℚ) :=
    one_div_pos.mpr (by exact_mod_cast hp d (hD hd))
  have hlow : (0 : ℚ) < k := integral ▸ Finset.sum_pos hp' hne
  have hhigh : (k : ℚ) < 2 := integral ▸
    (Finset.sum_le_sum_of_subset_of_nonneg hD (fun d _ _ ↦ by positivity)).trans_lt mass
  have hk₀ : 0 < k := by exact_mod_cast hlow
  have hk₂ : k < 2 := by exact_mod_cast hhigh
  exact ⟨S, hD, by simpa [show k = 1 by omega] using integral⟩

/-- Croot's selection of a set with reciprocal mass close to two and
a common multiple whenever almost all denominators divide in a short interval. -/
def H1 : Prop :=
  let regular (θ δ : ℝ) (N n : ℕ) :=
    N ≤ n ∧ (n : ℝ) ≤ (N : ℝ) ^ (1 + δ) ∧
    (∀ q ∈ n.divisors, IsPrimePow q → (q : ℝ) ≤ (N : ℝ) ^ θ) ∧
    |(n.primeFactors.card : ℝ) - Real.log (Real.log n)| ≤
      (Real.log (Real.log n)) ^ (3 / 4 : ℝ) ∧
    |(n.primeFactorsList.length : ℝ) - Real.log (Real.log n)| ≤
      (Real.log (Real.log n)) ^ (3 / 4 : ℝ)
  let clustered (θ : ℝ) (N : ℕ) (D : Finset ℕ) :=
    ∀ x : ℝ,
      ((D.filter (fun d ↦ ¬ ∃ z : ℤ, |(z : ℝ) - x| ≤ (N : ℝ) ^ (3 / 4 : ℝ) / 2 ∧
        (d : ℤ) ∣ z)).card : ℝ) <
        (N : ℝ) ^ (1 - θ) / (Real.log (Real.log N)) ^ 2 →
      ∃ z : ℤ, |(z : ℝ) - x| ≤ (N : ℝ) ^ (3 / 4 : ℝ) / 2 ∧
        ∀ d ∈ D, (d : ℤ) ∣ z
  ∀ θ δ : ℝ, 0 < θ → 0 < δ → θ + δ < 1 / 4 →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ C : Finset ℕ, (∀ d ∈ C, regular θ δ N d) →
      6 < (∑ d ∈ C, (1 / d : ℚ)) → ∃ D ⊆ C, clustered θ N D ∧
      2 - 3 / (N : ℚ) ≤ (∑ d ∈ D, (1 / d : ℚ)) ∧
      (∑ d ∈ D, (1 / d : ℚ)) < 2

/-- The zero frequency and the other Fourier contributions give a sum
strictly larger than the common denominator. -/
def H2 : Prop :=
  let regular (θ δ : ℝ) (N n : ℕ) :=
    N ≤ n ∧ (n : ℝ) ≤ (N : ℝ) ^ (1 + δ) ∧
    (∀ q ∈ n.divisors, IsPrimePow q → (q : ℝ) ≤ (N : ℝ) ^ θ) ∧
    |(n.primeFactors.card : ℝ) - Real.log (Real.log n)| ≤
      (Real.log (Real.log n)) ^ (3 / 4 : ℝ) ∧
    |(n.primeFactorsList.length : ℝ) - Real.log (Real.log n)| ≤
      (Real.log (Real.log n)) ^ (3 / 4 : ℝ)
  let clustered (θ : ℝ) (N : ℕ) (D : Finset ℕ) :=
    ∀ x : ℝ,
      ((D.filter (fun d ↦ ¬ ∃ z : ℤ, |(z : ℝ) - x| ≤ (N : ℝ) ^ (3 / 4 : ℝ) / 2 ∧
        (d : ℤ) ∣ z)).card : ℝ) <
        (N : ℝ) ^ (1 - θ) / (Real.log (Real.log N)) ^ 2 →
      ∃ z : ℤ, |(z : ℝ) - x| ≤ (N : ℝ) ^ (3 / 4 : ℝ) / 2 ∧
        ∀ d ∈ D, (d : ℤ) ∣ z
  ∀ θ δ : ℝ, 0 < θ → 0 < δ → θ + δ < 1 / 4 →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ D : Finset ℕ, (∀ d ∈ D, regular θ δ N d) →
      clustered θ N D →
      2 - 3 / (N : ℚ) ≤ (∑ d ∈ D, (1 / d : ℚ)) →
      (∑ d ∈ D, (1 / d : ℚ)) < 2 →
      ∀ (L : ℕ) [NeZero L], L = D.lcm id →
        (L : ℝ) < (∑ h : ZMod L, ∏ d ∈ D,
          (1 + ZMod.stdAddChar (h * ((L / d : ℕ) : ZMod L)))).re

theorem main : H1 → H2 → OMA.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R1.H2 := by
  classical
  intro select estimate θ δ ht hd htd
  obtain ⟨N₁, hselect⟩ := select θ δ ht hd htd
  obtain ⟨N₂, hestimate⟩ := estimate θ δ ht hd htd
  refine ⟨max 2 (max N₁ N₂), ?_⟩
  intro N hN C hreg hmass
  have hN₁ : N₁ ≤ N := (le_max_left N₁ N₂).trans ((le_max_right 2 _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_right N₁ N₂).trans ((le_max_right 2 _).trans hN)
  have hNpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 2) ((le_max_left 2 _).trans hN)
  obtain ⟨D, hDC, hcluster, hlow, hhigh⟩ := hselect N hN₁ C hreg hmass
  have pos (d : ℕ) (hdD : d ∈ D) : 0 < d := hNpos.trans_le (hreg d (hDC hdD)).1
  let L := D.lcm id
  have hL : L ≠ 0 := Finset.lcm_ne_zero_iff.mpr (fun d hdD ↦ (pos d hdD).ne')
  let _ : NeZero L := ⟨hL⟩
  have hf := hestimate N hN₂ D (fun d hD ↦ hreg d (hDC hD)) hcluster hlow hhigh L rfl
  obtain ⟨S, hS, hsum⟩ := extract D L rfl pos hhigh hf
  exact ⟨S, hS.trans hDC, hsum⟩

end OMA.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R1_H2_R1
