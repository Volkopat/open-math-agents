import OMAReductions.R_OeisA217785_conjecture_3_R1
import Mathlib

/-! Every complex root of the arithmetic-progression polynomial lies in the
open unit disk. Hence its only integral divisors with unit leading coefficient
are units. Its top two coefficients force coprimality of the leading
coefficients in any factorization. These facts leave the low-degree case
and the exclusion of coprime nonunit leading coefficients in higher degrees.
For the full reciprocal-polynomial theorem see TheSil/mse_3218248 on GitHub. -/
open Polynomial OeisA217785 Finset

namespace PolyDisk

lemma telescope (z : ℂ) (n : ℕ) :
    (1-z) * (∑ k ∈ range (n+1), ((k:ℂ)+1)*z^k) =
      (∑ k ∈ range (n+1), z^k) - ((n:ℂ)+1)*z^(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ (f := fun k => z^k), mul_add, ih]
    push_cast
    rw [pow_succ z (n+1)]
    ring

lemma disk {n : ℕ} {z : ℂ} (hz : eval₂ (Int.castRingHom ℂ) z (polyS n) = 0) : ‖z‖ < 1 := by
  have hS : ∑ k ∈ range (n+1), ((k:ℂ)+1)*z^k = 0 := by simpa [polyS,eval₂_finsetSum] using hz
  have ht := telescope z n
  rw [hS,mul_zero] at ht
  have he : (∑ k ∈ range (n+1), z^k) = ((n:ℂ)+1)*z^(n+1) := by linear_combination -ht
  have he' : (∑ k ∈ range (n+1), ((n:ℂ)+1-k)*z^k) =
      ((n:ℂ)+2)*((n:ℂ)+1)*z^(n+1) := by
    calc
      _ = ∑ k ∈ range (n+1), (((n:ℂ)+2)*z^k - ((k:ℂ)+1)*z^k) := by
        apply sum_congr rfl; intros; ring
      _ = _ := by rw [sum_sub_distrib, ← mul_sum, hS, he]; ring
  by_contra! h
  let L := ‖z‖^(n+1)
  have Lpos : 0 < L := pow_pos (by linarith) _
  have hb : ‖∑ k ∈ range (n+1), ((n:ℂ)+1-k)*z^k‖ ≤ (n+1:ℝ)*((n+1:ℝ)*L) := by
    apply (norm_sum_le ..).trans
    calc
      _ ≤ ∑ _k ∈ range (n+1), ((n:ℝ)+1)*L := by
        apply sum_le_sum
        intro k hk
        have kn := mem_range.mp hk
        have hk' : (k:ℝ) ≤ n+1 := by exact_mod_cast kn.le
        have hnorm : ‖(n:ℂ)+1-k‖ = (n:ℝ)+1-k := by
          rw [show (n:ℂ)+1-k = (((n:ℝ)+1-k : ℝ):ℂ) by push_cast; rfl]
          exact (Complex.norm_real _).trans (abs_of_nonneg (sub_nonneg.mpr hk'))
        rw [norm_mul, hnorm, norm_pow]
        exact mul_le_mul (by linarith) (pow_le_pow_right₀ h kn.le) (by positivity) (by positivity)
      _ = _ := by simp
  rw [he',norm_mul,norm_mul,norm_pow] at hb
  have hnorm (m : ℕ) : ‖(m:ℂ)‖ = m := by simp
  rw [show (n:ℂ)+2 = ((n+2:ℕ):ℂ) by push_cast; ring,
      show (n:ℂ)+1 = ((n+1:ℕ):ℂ) by push_cast; ring, hnorm, hnorm] at hb
  push_cast at hb
  change _ * L ≤ _ at hb
  nlinarith [mul_pos (show 0 < (n:ℝ)+1 by positivity) Lpos]
end PolyDisk

namespace PolyDisk

lemma prodNorm (s : Multiset ℂ) (h : ∀ z ∈ s, ‖z‖ < 1) :
    ‖s.prod‖ ≤ 1 ∧ (s ≠ 0 → ‖s.prod‖ < 1) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha := h a (Multiset.mem_cons_self ..)
    have hs := (ih fun z hz => h z (Multiset.mem_cons_of_mem hz)).1
    rw [Multiset.prod_cons,norm_mul]
    have hp : ‖a‖ * ‖s.prod‖ < 1 := (mul_le_mul_of_nonneg_left hs (norm_nonneg a)).trans_lt (by simpa using ha)
    exact ⟨hp.le, fun _ => hp⟩

lemma eval_zero (n : ℕ) : eval 0 (polyS n) = 1 := by
  simp [polyS, eval_finsetSum, Finset.sum_range_succ']

lemma unit_of_unit_lead {n : ℕ} (g : Polynomial ℤ) (hd : g ∣ polyS n)
    (hu : IsUnit g.leadingCoeff) : IsUnit g := by
  have hconst : IsUnit (g.coeff 0) := by
    apply isUnit_of_dvd_one
    simpa [Polynomial.eval_zero, ← Polynomial.coeff_zero_eq_eval_zero] using
      (show (eval 0 g) ∣ 1 from (eval_zero n) ▸ eval_dvd (x := 0) hd)
  let G := g.map (Int.castRingHom ℂ)
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective (α := ℂ)
  have lead : G.leadingCoeff = (g.leadingCoeff:ℂ) := leadingCoeff_map_of_injective hinj g
  have coeff : G.coeff 0 = (g.coeff 0 : ℂ) := coeff_map ..
  have normUnit (v : ℤ) (h : IsUnit v) : ‖(v:ℂ)‖ = 1 := by
    rcases Int.isUnit_iff.mp h with rfl | rfl <;> norm_num
  have hr (z : ℂ) (hz : z ∈ G.roots) : ‖z‖ < 1 := by
    apply disk (n := n)
    have hm : G ∣ (polyS n).map (Int.castRingHom ℂ) := (mapRingHom (Int.castRingHom ℂ)).map_dvd hd
    rw [← eval_map]
    exact (isRoot_of_mem_roots hz).dvd hm
  have hprod := congrArg (fun z : ℂ => ‖z‖) (IsAlgClosed.splits G).coeff_zero_eq_leadingCoeff_mul_prod_roots
  rw [coeff, normUnit _ hconst, norm_mul, norm_mul, norm_pow, lead, normUnit _ hu] at hprod
  simp only [norm_neg, norm_one, one_pow, one_mul] at hprod
  have he : G.roots = 0 := by
    by_contra ne
    exact (prodNorm _ hr).2 ne |>.ne hprod.symm
  have hdeg : g.natDegree = 0 := by
    have h := (IsAlgClosed.splits G).natDegree_eq_card_roots
    simpa [G, he, natDegree_map_eq_of_injective hinj] using (h.trans (by rw [he]; rfl))
  rw [eq_C_of_natDegree_eq_zero hdeg]
  exact isUnit_C.mpr hconst

end PolyDisk

namespace PolyDisk

lemma coeffs (n i : ℕ) : (polyS n).coeff i = if i ≤ n then (i:ℤ)+1 else 0 := by
  simp only [polyS, finsetSum_coeff, coeff_C_mul_X_pow]
  simp [Finset.mem_range]

lemma degreeS (n : ℕ) : (polyS n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero _ (by simp [coeffs]; omega)
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  simp [coeffs, not_le.mpr hi]

lemma leadS (n : ℕ) : (polyS n).leadingCoeff = (n:ℤ)+1 := by
  simp [leadingCoeff,degreeS,coeffs]

end PolyDisk

namespace PolyDisk

lemma coprime_leads {n : ℕ} (hn : 1 ≤ n) {a b : Polynomial ℤ} (h : polyS n = a*b) :
    IsCoprime a.leadingCoeff b.leadingCoeff := by
  have top : a.leadingCoeff * b.leadingCoeff = (n:ℤ)+1 := by rw [← leadingCoeff_mul, ← h, leadS]
  have nxt := congrArg (fun f : Polynomial ℤ => f.reverse.coeff 1) h
  have nxtS : (polyS n).nextCoeff = (n:ℤ) := by
    rw [nextCoeff_of_natDegree_pos (by rw [degreeS]; omega : 0 < (polyS n).natDegree),
        degreeS, coeffs, if_pos (by omega)]
    omega
  simp only [reverse_mul_of_domain, mul_coeff_one, coeff_zero_reverse, coeff_one_reverse, nxtS] at nxt
  exact ⟨b.leadingCoeff - b.nextCoeff, -a.nextCoeff, by linear_combination top + nxt⟩

end PolyDisk

namespace OMA.R_OeisA217785_conjecture_3_R1_H2_R1

open PolyDisk

def H1 : Prop := ∀ n : ℕ, 2 ≤ n → ∀ a : Polynomial ℤ,
  a ∣ polyS n → a.natDegree ≤ 1 → IsUnit a

def H2 : Prop := ∀ n : ℕ, 2 ≤ n → ¬ (n+2).Prime →
  ∀ a b : Polynomial ℤ, 2 ≤ a.natDegree → 2 ≤ b.natDegree →
  ¬ IsUnit a.leadingCoeff → ¬ IsUnit b.leadingCoeff →
  IsCoprime a.leadingCoeff b.leadingCoeff → polyS n ≠ a*b

theorem main : H1 → H2 → OMA.R_OeisA217785_conjecture_3_R1.H2 := by
  intro linear higher n hn hp
  have hn2 : 2 ≤ n := by
    by_contra! h
    obtain rfl : n = 1 := by omega
    exact hp (by decide)
  have prim : (polyS n).IsPrimitive := by
    apply isPrimitive_iff_isUnit_of_C_dvd.mpr
    intro a ha
    exact isUnit_of_dvd_one (by simpa [PolyDisk.eval_zero] using (eval_dvd (x := 0) ha))
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast prim).mp
  refine ⟨not_isUnit_of_natDegree_pos _ (by rw [degreeS]; omega), ?_⟩
  intro a b hab
  have ha : a ∣ polyS n := ⟨b, hab⟩
  have hb : b ∣ polyS n := ⟨a, hab.trans (mul_comm ..)⟩
  by_cases la : a.natDegree ≤ 1
  · exact Or.inl (linear n hn2 a ha la)
  by_cases lb : b.natDegree ≤ 1
  · exact Or.inr (linear n hn2 b hb lb)
  by_cases ua : IsUnit a.leadingCoeff
  · exact Or.inl (unit_of_unit_lead a ha ua)
  by_cases ub : IsUnit b.leadingCoeff
  · exact Or.inr (unit_of_unit_lead b hb ub)
  exact (higher n hn2 hp a b (by omega) (by omega) ua ub (coprime_leads hn hab) hab).elim

end OMA.R_OeisA217785_conjecture_3_R1_H2_R1
