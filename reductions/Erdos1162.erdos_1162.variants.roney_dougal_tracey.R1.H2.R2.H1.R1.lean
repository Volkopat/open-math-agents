import OMAReductions.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2
import Mathlib

/-! Roney-Dougal and Tracey, Subgroups of symmetric groups: enumeration and
asymptotic properties, https://arxiv.org/abs/2503.05416, Theorems 2 and 3
and Lemma 2.7. We verify the covering count under conjugacy, multiply the
Sylow bounds, and keep the exact coefficient 1/16 under the sum of degrees. -/
open Finset

namespace NilpotentCover

theorem nilpotent_card_le_cover {G : Type} [Group G] [Finite G]
    (C : Finset (Subgroup G))
    (hCover : ∀ S : Subgroup G, Group.IsNilpotent S →
      ∃ D ∈ C, ∃ g : G, S ≤ D.map (MulAut.conj g).toMonoidHom) :
    Nat.card {S : Subgroup G // Group.IsNilpotent S} ≤
      ∑ D : C, Nat.card G * Nat.card (Subgroup (D.1 : Subgroup G)) := by
  classical
  let I := Σ D : C, G × Subgroup (D.1 : Subgroup G)
  let represent (D : Subgroup G) (g : G) : D →* G :=
    (MulAut.conj g).toMonoidHom.comp D.subtype
  let f (a : I) : Subgroup G := a.2.2.map (represent a.1.1 a.2.1)
  have hRange (S : Subgroup G) (hNil : Group.IsNilpotent S) : S ∈ Set.range f := by
    obtain ⟨D, hD, g, hg⟩ := hCover S hNil
    have hRep : (represent D g).range = D.map (MulAut.conj g).toMonoidHom := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨y.1, y.2, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
    refine ⟨⟨⟨D, hD⟩, g, S.comap (represent D g)⟩, ?_⟩
    exact Subgroup.map_comap_eq_self (hRep ▸ hg)
  let transport (S : {S : Subgroup G // Group.IsNilpotent S}) : Set.range f :=
    ⟨S.1, hRange S.1 S.2⟩
  have hInj : Function.Injective transport := by
    intro x y h
    exact Subtype.ext (congrArg (fun S : Set.range f => S.val) h)
  calc
    _ ≤ Nat.card (Set.range f) := Nat.card_le_card_of_injective transport hInj
    _ ≤ Nat.card I := Finite.card_range_le f
    _ = _ := by rw [Nat.card_sigma]; simp only [Nat.card_prod]

private theorem perm_factorial_bound (n : ℕ) (hn : 2 ≤ n) :
    ((2 : ℝ) ^ (n : ℝ)) * (Nat.card (Equiv.Perm (Fin n)) : ℝ) ≤
      (2 : ℝ) ^ (2 * (n : ℝ) * Real.logb 2 n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : (1 : ℝ) ≤ Real.logb 2 n := by
    rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast hn)
  have hPow : (n : ℝ) ^ n = (2 : ℝ) ^ ((n : ℝ) * Real.logb 2 n) := by
    rw [mul_comm, Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)),
      Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hn0,
      Real.rpow_natCast]
  have hFin : Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  calc
    _ ≤ (2 : ℝ) ^ (n : ℝ) * (n : ℝ) ^ n := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [hFin]
      exact_mod_cast n.factorial_le_pow
    _ = (2 : ℝ) ^ ((n : ℝ) + (n : ℝ) * Real.logb 2 n) := by
      rw [hPow, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) by positivity) (sub_nonneg.mpr hlog)]

theorem nilpotent_real_cover_bound (n : ℕ) (hn : 2 ≤ n)
    (C : Finset (Subgroup (Equiv.Perm (Fin n))))
    (hC : (C.card : ℝ) ≤ (2 : ℝ) ^ (n : ℝ))
    (hCover : ∀ S : Subgroup (Equiv.Perm (Fin n)), Group.IsNilpotent S →
      ∃ D ∈ C, ∃ g : Equiv.Perm (Fin n), S ≤ D.map (MulAut.conj g).toMonoidHom)
    (q : ℝ) (hBound : ∀ D ∈ C, (Nat.card (Subgroup (D : Subgroup (Equiv.Perm (Fin n)))) : ℝ) ≤
      (2 : ℝ) ^ q) :
    (Nat.card {S : Subgroup (Equiv.Perm (Fin n)) // Group.IsNilpotent S} : ℝ) ≤
      (2 : ℝ) ^ (q + 2 * (n : ℝ) * Real.logb 2 n) := by
  have hCast : (Nat.card {S : Subgroup (Equiv.Perm (Fin n)) // Group.IsNilpotent S} : ℝ) ≤
      ∑ D : C, (Nat.card (Equiv.Perm (Fin n)) : ℝ) *
        (Nat.card (Subgroup (D.1 : Subgroup (Equiv.Perm (Fin n)))) : ℝ) := by
    exact_mod_cast nilpotent_card_le_cover C hCover
  calc
    _ ≤ ∑ D : C, (Nat.card (Equiv.Perm (Fin n)) : ℝ) * (2 : ℝ) ^ q := by
      apply hCast.trans
      exact sum_le_sum (fun D _ => mul_le_mul_of_nonneg_left (hBound D.1 D.2) (by positivity))
    _ = ((C.card : ℝ) * (Nat.card (Equiv.Perm (Fin n)) : ℝ)) * (2 : ℝ) ^ q := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      ring
    _ ≤ ((2 : ℝ) ^ (n : ℝ) * (Nat.card (Equiv.Perm (Fin n)) : ℝ)) * (2 : ℝ) ^ q := by
      gcongr
    _ ≤ (2 : ℝ) ^ (2 * (n : ℝ) * Real.logb 2 n) * (2 : ℝ) ^ q :=
      mul_le_mul_of_nonneg_right (perm_factorial_bound n hn) (by positivity)
    _ = _ := by rw [mul_comm, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

theorem small_nilpotent_card (n : ℕ) (hn : n ≤ 1) :
    Nat.card {S : Subgroup (Equiv.Perm (Fin n)) // Group.IsNilpotent S} ≤ 1 := by
  have : Subsingleton (Fin n) := ⟨fun x y => Fin.ext (by omega)⟩
  have : Subsingleton (Equiv.Perm (Fin n)) := ⟨fun f g => Equiv.ext fun x => Subsingleton.elim _ _⟩
  have : Subsingleton (Subgroup (Equiv.Perm (Fin n))) := ⟨fun x y => by
    ext g
    rw [Subsingleton.elim g 1]
    simp⟩
  exact Finite.card_le_one_iff_subsingleton.mpr inferInstance

end NilpotentCover

namespace Erdos1162NilpotentBudget

open Finset

/-- For a prime degree, the quadratic term in the exponent costs at most
one sixteenth of the square of its allocated degree. -/
theorem logb_two_le_sq_div_four {x : ℝ} (hx : 2 ≤ x) :
    Real.logb 2 x ≤ x ^ 2 / 4 := by
  have hx0 : 0 < x := by linarith
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)⁻¹) (by norm_num)
    rw [Real.log_inv] at h
    norm_num at h ⊢
    linarith
  have hlogpos : 0 < Real.log 2 := by linarith
  have hbound := Real.log_le_sub_one_of_pos (x := x / 2) (by positivity)
  rw [Real.log_div hx0.ne' (by norm_num)] at hbound
  have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ x - 2 by linarith)
  calc
    Real.logb 2 x ≤ x - 1 := by
      rw [Real.logb, div_le_iff₀ hlogpos]
      nlinarith only [hbound, hmul]
    _ ≤ x ^ 2 / 4 := by nlinarith [sq_nonneg (x - 2)]

/-- Combine the quadratic and logarithmic budget for pairwise disjoint
allocations. The prime hypothesis is only used through the lower bound 2. -/
theorem sum_exponents_le (S : Finset ℕ) (m : ℕ → ℕ) (n : ℕ) (γ : ℝ)
    (hp : ∀ p ∈ S, 2 ≤ p) (hm : ∀ p ∈ S, p ≤ m p)
    (hn : ∑ p ∈ S, m p ≤ n) (hγ : 0 ≤ γ) :
    (∑ p ∈ S, (Real.logb 2 (p : ℝ) * (m p : ℝ) ^ 2 / (4 * (p : ℝ) ^ 2) +
      γ * (m p : ℝ) * Real.logb 2 (m p : ℝ))) ≤
      (n : ℝ) ^ 2 / 16 + γ * (n : ℝ) * Real.logb 2 (n : ℝ) := by
  have hsum : (∑ p ∈ S, (m p : ℝ)) ≤ n := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.logb 2 (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp
    · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hnpos)
  have hsq : ∑ p ∈ S, (m p : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
    (Finset.sum_sq_le_sq_sum_of_nonneg fun p _ => Nat.cast_nonneg (m p)).trans
      (pow_le_pow_left₀ (Finset.sum_nonneg fun p _ => Nat.cast_nonneg (m p)) hsum 2)
  calc
    _ ≤ ∑ p ∈ S, ((m p : ℝ) ^ 2 / 16 + γ * (m p : ℝ) * Real.logb 2 (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hpS
      have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp p hpS
      have hp₀ : (0 : ℝ) < p := by linarith
      have hm₂ : (2 : ℝ) ≤ m p := by exact_mod_cast (hp p hpS).trans (hm p hpS)
      have hm₀ : (0 : ℝ) < m p := by linarith
      have hmn : (m p : ℝ) ≤ n := (Finset.single_le_sum
        (fun i _ => Nat.cast_nonneg (m i)) hpS).trans hsum
      apply add_le_add
      · rw [div_le_iff₀ (show (0 : ℝ) < 4 * (p : ℝ) ^ 2 by positivity)]
        calc
          Real.logb 2 (p : ℝ) * (m p : ℝ) ^ 2 ≤ ((p : ℝ) ^ 2 / 4) * (m p : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right (logb_two_le_sq_div_four hp₂) (sq_nonneg _)
          _ = _ := by ring
      · exact mul_le_mul_of_nonneg_left
          (Real.logb_le_logb_of_le (by norm_num) hm₀ hmn)
          (mul_nonneg hγ (Nat.cast_nonneg _))
    _ = (∑ p ∈ S, (m p : ℝ) ^ 2) / 16 +
        γ * (∑ p ∈ S, (m p : ℝ)) * Real.logb 2 (n : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum, Finset.sum_mul]
    _ ≤ _ := add_le_add (div_le_div_of_nonneg_right hsq (by norm_num))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hγ) hlogn)

/-- Multiply integer counts bounded by real powers of two, and use a bound
for the sum of the exponents. -/
theorem count_product_le {ι : Type*} (S : Finset ι) (count : ι → ℕ) (weight : ι → ℝ)
    (budget : ℝ) (hcount : ∀ i ∈ S, (count i : ℝ) ≤ (2 : ℝ) ^ weight i)
    (hbudget : ∑ i ∈ S, weight i ≤ budget) :
    ((∏ i ∈ S, count i : ℕ) : ℝ) ≤ (2 : ℝ) ^ budget := by
  rw [Nat.cast_prod]
  calc
    _ ≤ ∏ i ∈ S, (2 : ℝ) ^ weight i :=
      Finset.prod_le_prod (fun i _ => Nat.cast_nonneg (count i)) hcount
    _ = (2 : ℝ) ^ (∑ i ∈ S, weight i) :=
      (Real.rpow_sum_of_pos (by norm_num) weight S).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hbudget

end Erdos1162NilpotentBudget

namespace OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H1_R1

open Finset

/-- One product of maximal transitive nilpotent groups per orbit partition
suffices up to conjugacy. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ∃ D : Nat.Partition n → Subgroup (Equiv.Perm (Fin n)),
      (∀ a, Group.IsNilpotent (D a)) ∧
      ∀ S : Subgroup (Equiv.Perm (Fin n)), Group.IsNilpotent S →
        ∃ a : Nat.Partition n, ∃ g : Equiv.Perm (Fin n), S ≤ (D a).map (MulAut.conj g).toMonoidHom

/-- A nilpotent ambient group splits into its Sylow factors. Restricting
each factor to its orbit coordinates gives faithful permutation degrees
whose sum is at most the original degree. -/
def H2 : Prop :=
  ∀ n : ℕ, ∀ D : Subgroup (Equiv.Perm (Fin n)), Group.IsNilpotent D →
    ∃ (S : Finset ℕ) (m : ℕ → ℕ),
      (∀ p ∈ S, p.Prime ∧ p ≤ m p) ∧ (∑ p ∈ S, m p) ≤ n ∧
      Nat.card (Subgroup D) ≤
        ∏ p ∈ S, Nat.card {P : Subgroup (Equiv.Perm (Fin (m p))) // IsPGroup p P}

/-- The upper bound in Theorem 2, with uniform error obtained from the
large-prime bound and a maximum over the finitely many smaller primes. -/
def H3 : Prop :=
  ∃ γ : ℝ, 0 ≤ γ ∧ ∀ (p m : ℕ), p.Prime → p ≤ m →
    (Nat.card {P : Subgroup (Equiv.Perm (Fin m)) // IsPGroup p P} : ℝ) ≤
      (2 : ℝ) ^ (Real.logb 2 (p : ℝ) * (m : ℝ)^2 / (4 * (p : ℝ)^2) +
        γ * (m : ℝ) * Real.logb 2 (m : ℝ))

theorem main : H1 → H2 → H3 →
    OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2.H1 := by
  classical
  intro hFamily hFactors hPrime
  obtain ⟨γ, hγ, hCounts⟩ := hPrime
  refine ⟨γ + 2, by positivity, ?_⟩
  intro n
  by_cases hn : 2 ≤ n
  · obtain ⟨D, hD, hFamilyCover⟩ := hFamily n hn
    let C := (Finset.univ : Finset (Nat.Partition n)).image D
    have hC : C.card ≤ 2 ^ n := by
      calc
        _ ≤ Fintype.card (Nat.Partition n) := by
          dsimp only [C]
          simpa only [Finset.card_univ] using Finset.card_image_le (s := Finset.univ) (f := D)
        _ ≤ Fintype.card (Composition n) :=
          Fintype.card_le_of_surjective (Nat.Partition.ofComposition n) Nat.Partition.ofComposition_surj
        _ = 2 ^ (n - 1) := composition_card n
        _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.sub_le n 1)
    have hCN : ∀ U ∈ C, Group.IsNilpotent U := by
      intro U hU
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hU
      exact hD a
    have hCover : ∀ S : Subgroup (Equiv.Perm (Fin n)), Group.IsNilpotent S →
        ∃ U ∈ C, ∃ g : Equiv.Perm (Fin n), S ≤ U.map (MulAut.conj g).toMonoidHom := by
      intro S hS
      obtain ⟨a, g, h⟩ := hFamilyCover S hS
      exact ⟨D a, Finset.mem_image_of_mem D (Finset.mem_univ a), g, h⟩
    have hC' : (C.card : ℝ) ≤ (2 : ℝ) ^ (n : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast hC
    let q : ℝ := (n : ℝ)^2 / 16 + γ * (n : ℝ) * Real.logb 2 n
    have hLocal (D : Subgroup (Equiv.Perm (Fin n))) (hD : D ∈ C) :
        (Nat.card (Subgroup D) : ℝ) ≤ (2 : ℝ) ^ q := by
      obtain ⟨S, m, hp, hm, hDcount⟩ := hFactors n D (hCN D hD)
      let A (p : ℕ) := Nat.card {P : Subgroup (Equiv.Perm (Fin (m p))) // IsPGroup p P}
      let e (p : ℕ) := Real.logb 2 (p : ℝ) * (m p : ℝ)^2 / (4 * (p : ℝ)^2) +
        γ * (m p : ℝ) * Real.logb 2 (m p : ℝ)
      have hCount (p : ℕ) (hpS : p ∈ S) : (A p : ℝ) ≤ (2 : ℝ) ^ e p :=
        hCounts p (m p) (hp p hpS).1 (hp p hpS).2
      have hSum : (∑ p ∈ S, e p) ≤ q :=
        Erdos1162NilpotentBudget.sum_exponents_le S m n γ
          (fun p h => (hp p h).1.two_le) (fun p h => (hp p h).2) hm hγ
      exact (by exact_mod_cast hDcount :
          (Nat.card (Subgroup D) : ℝ) ≤ ((∏ p ∈ S, A p : ℕ) : ℝ)).trans
        (Erdos1162NilpotentBudget.count_product_le S A e q hCount hSum)
    have h := NilpotentCover.nilpotent_real_cover_bound n hn C hC' hCover q hLocal
    convert h using 2
    dsimp only [q]
    ring
  · have hsmall := NilpotentCover.small_nilpotent_card n (by omega)
    refine (show (Nat.card {S : Subgroup (Equiv.Perm (Fin n)) // Group.IsNilpotent S} : ℝ)
      ≤ 1 by exact_mod_cast hsmall).trans ?_
    have hLog : Real.logb 2 (n : ℝ) = 0 := by
      have h : n = 0 ∨ n = 1 := by omega
      rcases h with rfl | rfl <;> simp
    rw [hLog, mul_zero, add_zero]
    exact Real.one_le_rpow (by norm_num) (by positivity)

end OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H1_R1
