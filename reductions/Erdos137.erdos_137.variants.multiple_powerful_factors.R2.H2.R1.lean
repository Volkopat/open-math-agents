import OMAReductions.R_Erdos137_erdos_137_variants_multiple_powerful_factors_R2
import Mathlib.RingTheory.Radical.NatInt

/-!
A three-term window suffices under a radical lower bound for the triples
associated with (t+2)^2 - (t+1)(t+3) = 1. The even-center case has three
pairwise coprime factors. In the odd-center case the endpoints share 2.
-/

open Filter UniqueFactorizationMonoid
open scoped BigOperators

namespace OMA.R_Erdos137_erdos_137_variants_multiple_powerful_factors_R2_H2_R1

/-- Radical growth with even center. -/
def H1 : Prop :=
  ∀ᶠ t : ℕ in atTop, Even (t + 2) → t ^ 7 < radical ((t + 1) * (t + 2) * (t + 3)) ^ 4

/-- Radical growth with odd center. -/
def H2 : Prop :=
  ∀ᶠ t : ℕ in atTop, Odd (t + 2) → t ^ 7 < radical ((t + 1) * (t + 2) * (t + 3)) ^ 4

lemma radical_sq_le_single (n : ℕ) (hn : n ≠ 0) :
    radical n ^ 2 ≤ n * ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ^ 2 ∣ n), p := by
  calc
    _ = ∏ p ∈ n.primeFactors, p ^ 2 := by
      rw [Nat.radical_eq_prod_primeFactors, Finset.prod_pow]
    _ ≤ ∏ p ∈ n.primeFactors,
        p ^ n.factorization p * (if ¬ p ^ 2 ∣ n then p else 1) := by
      apply Finset.prod_le_prod'
      intro p hp
      obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
      by_cases hd : p ^ 2 ∣ n
      · simpa [hd] using Nat.pow_le_pow_right hprime.pos
          ((hprime.pow_dvd_iff_le_factorization hn).mp hd)
      · have hpos := hprime.factorization_pos_of_dvd hn hdvd
        have hlt : ¬ 2 ≤ n.factorization p :=
          fun h => hd ((hprime.pow_dvd_iff_le_factorization hn).mpr h)
        have he : n.factorization p = 1 := by omega
        rw [if_pos hd, he, pow_one, pow_two]
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Nat.prod_primeFactors_pow_factorization hn, Finset.prod_filter]

lemma radical_mul_le (a b : ℕ) : radical (a * b) ≤ radical a * radical b :=
  Nat.le_of_dvd (Nat.mul_pos (Nat.radical_pos a) (Nat.radical_pos b)) radical_mul_dvd

theorem main : H1 → H2 → OMA.R_Erdos137_erdos_137_variants_multiple_powerful_factors_R2.H2 := by
  intro hEven hOdd
  refine ⟨3, 8, by decide, by decide, ?_⟩
  filter_upwards [hEven, hOdd, eventually_ge_atTop (2 ^ 24 : ℕ)] with t he ho ht
  have hlarge : t ^ 7 < radical ((t + 1) * (t + 2) * (t + 3)) ^ 4 :=
    (Nat.even_or_odd (t + 2)).elim he ho
  by_contra h
  push Not at h
  have bound (i : ℕ) (hi0 : 0 < i) (hi3 : i ≤ 3) :
      radical (t + i) ^ 16 ≤ (2 * t) ^ 8 * t := by
    have hi : t + i ∈ Finset.Ioc t (t + 3) := Finset.mem_Ioc.mpr (by omega)
    have hsmall := h (t + i) hi
    have hle : t + i ≤ 2 * t := by omega
    calc
      _ = (radical (t + i) ^ 2) ^ 8 := by rw [← pow_mul]
      _ ≤ ((t + i) * ∏ p ∈ (t + i).primeFactors.filter (fun p => ¬ p ^ 2 ∣ t + i), p) ^ 8 :=
        Nat.pow_le_pow_left (radical_sq_le_single _ (by omega)) _
      _ = (t + i) ^ 8 * (∏ p ∈ (t + i).primeFactors.filter (fun p => ¬ p ^ 2 ∣ t + i), p) ^ 8 := by
        rw [mul_pow]
      _ ≤ _ := Nat.mul_le_mul (Nat.pow_le_pow_left hle _) hsmall
  have hfactors : radical ((t + 1) * (t + 2) * (t + 3)) ≤
      radical (t + 1) * radical (t + 2) * radical (t + 3) :=
    (radical_mul_le _ _).trans (Nat.mul_le_mul (radical_mul_le _ _) le_rfl)
  have hupper : radical ((t + 1) * (t + 2) * (t + 3)) ^ 16 ≤ t ^ 28 := by
    calc
      _ ≤ (radical (t + 1) * radical (t + 2) * radical (t + 3)) ^ 16 :=
        Nat.pow_le_pow_left hfactors _
      _ = radical (t + 1) ^ 16 * radical (t + 2) ^ 16 * radical (t + 3) ^ 16 := by
        simp only [mul_pow]
      _ ≤ ((2 * t) ^ 8 * t) * ((2 * t) ^ 8 * t) * ((2 * t) ^ 8 * t) :=
        Nat.mul_le_mul
          (Nat.mul_le_mul (bound 1 (by decide) (by decide)) (bound 2 (by decide) (by decide)))
          (bound 3 (by decide) (by decide))
      _ = 2 ^ 24 * t ^ 27 := by ring
      _ ≤ t * t ^ 27 := Nat.mul_le_mul ht le_rfl
      _ = t ^ 28 := by exact (pow_succ' t 27).symm
  have hlower : t ^ 28 < radical ((t + 1) * (t + 2) * (t + 3)) ^ 16 := by
    simpa only [← pow_mul] using Nat.pow_lt_pow_left hlarge (by decide : 4 ≠ 0)
  exact (not_lt_of_ge hupper) hlower

end OMA.R_Erdos137_erdos_137_variants_multiple_powerful_factors_R2_H2_R1
