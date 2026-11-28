import OMAStatements.S_oeis_a340263
import Mathlib

/-! Irreducibility of the binomials obtained from the fractional linear substitution. -/

namespace MobiusPowers

open Polynomial IntermediateField AdjoinRoot

private theorem constant_not_square {n : ℕ} (hn : 0 < n) :
    ¬ IsSquare ((2:ℚ)^(n+1)-1) := by
  intro h
  have hZ : IsSquare ((2:ℤ)^(n+1)-1) := Rat.isSquare_intCast_iff.mp (by simpa using h)
  obtain ⟨t, ht⟩ := hZ
  have h4 := congrArg (fun z : ℤ => (z : ZMod 4)) ht
  push_cast at h4
  rw [show n+1 = 2+(n-1) by omega, pow_add, show (2:ZMod 4)^2 = 0 by decide +kernel,
    zero_mul] at h4
  have impossible : ∀ x : ZMod 4, x*x ≠ 0-1 := by decide +kernel
  exact impossible (t : ZMod 4) h4.symm

/-- A square root of the generator at any intermediate stage would give a
rational square root of the positive constant after taking its norm. -/
private theorem irreducible_tower {K : Type*} [Field K] {c : K} (hc : ¬ IsSquare c)
    (hneg : ¬ IsSquare (-c)) (j : ℕ) :
    Irreducible ((X : K[X]) ^ (2^(j+1)) - C (-c)) := by
  induction j with
  | zero =>
    apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
    intro z hz
    exact hneg ⟨z, by simpa [sq] using hz.symm⟩
  | succ j ih =>
    rw [show 2^(j+1+1) = 2*2^(j+1) by ring]
    apply X_pow_mul_sub_C_irreducible ih
    intro E _ _ x hx
    have hdeg : 0 < 2^(j+1) := by positivity
    have hint : IsIntegral K x := not_not.mp fun h => by
      simpa only [degree_zero, degree_X_pow_sub_C hdeg, WithBot.natCast_ne_bot]
        using congrArg degree (hx.symm.trans (dif_neg h))
    apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
    intro z he
    apply hc
    refine ⟨Algebra.norm K z, ?_⟩
    rw [←sq, ←map_pow, he, ←adjoin.powerBasis_gen hint,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (adjoin.powerBasis hint)]
    have heven : Even (2^(j+1)) := ⟨2^j, by rw [pow_succ]; omega⟩
    simp [minpoly_gen, hx, hdeg.ne'.symm, heven.neg_one_pow]

theorem binomial_irreducible {n : ℕ} (hn : 0 < n) :
    Irreducible ((X : ℚ[X])^(2^n) + C ((2:ℚ)^(n+1)-1)) := by
  have hpos : 0 < (2:ℚ)^(n+1)-1 := by
    have hh : (1:ℚ) < 2^(n+1) := one_lt_pow₀ (by norm_num) (by omega)
    linarith
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hneg : ¬IsSquare (-((2:ℚ)^(j+1+1)-1)) := by
    rintro ⟨z,hz⟩
    exact (mul_self_nonneg z).not_gt (hz ▸ neg_neg_of_pos hpos)
  simpa only [map_neg, sub_neg_eq_add] using irreducible_tower (constant_not_square hn) hneg j

end MobiusPowers

namespace MobiusPowers

open Polynomial IntermediateField

/-- The inverse linear fractional transformation recovers a root of the binomial,
so the transformed root has the same degree over the rational field. -/
theorem transform_irreducible {d : ℕ} (hd : 0 < d) {c : ℚ} (hc : c+1 ≠ 0)
    (hf : Irreducible ((X : ℚ[X])^d+C c)) :
    Irreducible (((X : ℚ[X])+1)^d + C c * (X-1)^d) := by
  let f : ℚ[X] := X^d+C c
  let : Fact (Irreducible f) := ⟨hf⟩
  let E := AdjoinRoot f
  let : FiniteDimensional ℚ E := (AdjoinRoot.powerBasis hf.ne_zero).finite
  let x : E := AdjoinRoot.root f
  let y : E := (x+1)/(x-1)
  let g : ℚ[X] := (X+1)^d + C c * (X-1)^d
  have hx : x^d + algebraMap ℚ E c = 0 := by
    simpa [x,f] using (AdjoinRoot.eval₂_root f)
  have hx1 : x-1 ≠ 0 := by
    intro h
    rw [sub_eq_zero.mp h, one_pow] at hx
    apply hc
    apply (algebraMap ℚ E).injective
    simpa [add_comm] using hx
  have hrel : y*(x-1) = x+1 := div_mul_cancel₀ _ hx1
  have hy1 : y-1 ≠ 0 := by
    intro h
    rw [sub_eq_zero.mp h, one_mul] at hrel
    have htwo : (2 : E) = 0 := by linear_combination -hrel
    exact (by norm_num : (2 : E) ≠ 0) htwo
  have hinv : x = (y+1)/(y-1) := by
    apply (eq_div_iff hy1).mpr
    linear_combination hrel
  have hadj : ℚ⟮x⟯ = ℚ⟮y⟯ := by
    apply le_antisymm
    · apply adjoin_simple_le_iff.mpr
      rw [hinv]
      exact div_mem (add_mem (mem_adjoin_simple_self ℚ y) (one_mem _))
        (sub_mem (mem_adjoin_simple_self ℚ y) (one_mem _))
    · apply adjoin_simple_le_iff.mpr
      exact div_mem (add_mem (mem_adjoin_simple_self ℚ x) (one_mem _))
        (sub_mem (mem_adjoin_simple_self ℚ x) (one_mem _))
  have hmon : f.Monic := monic_X_pow_add_C c hd.ne'
  have hmin : minpoly ℚ x = f := by
    symm
    apply minpoly.eq_of_irreducible_of_monic hf _ hmon
    simpa [f] using hx
  have hi : IsIntegral ℚ y := Algebra.IsIntegral.isIntegral y
  have hdeg : (minpoly ℚ y).natDegree = d := by
    have hix : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    rw [← adjoin.finrank hi, ← hadj, adjoin.finrank hix,hmin]
    exact natDegree_X_pow_add_C ..
  have hxy : y+1 = x*(y-1) := by linear_combination -hrel
  have hroot : aeval y g = 0 := by
    simp only [g, map_add, map_pow, aeval_X, map_one, map_mul, aeval_C, map_sub]
    rw [hxy, mul_pow, ← add_mul, hx, zero_mul]
  have hsmall : g.natDegree ≤ d := by
    apply (natDegree_add_le ..).trans
    apply max_le
    · rw [natDegree_pow, ← C_1, natDegree_X_add_C, mul_one]
    · apply (natDegree_mul_le ..).trans
      rw [natDegree_C, zero_add, natDegree_pow, ← C_1, natDegree_X_sub_C, mul_one]
  have hnon : g ≠ 0 := by
    intro he
    have h := congrArg (eval 1) he
    simp [g, hd.ne'] at h
  exact (associated_of_dvd_of_natDegree_le (minpoly.dvd ℚ y hroot) hnon
    (hsmall.trans_eq hdeg.symm)).irreducible_iff.mp (minpoly.irreducible hi)

end MobiusPowers

open Polynomial

theorem OMA.solution : type_of% @OMA.S_oeis_a340263.main := by
  intro n hn
  let b : ℚ := 2^n
  let d := 2^n
  have hb : b ≠ 0 := pow_ne_zero _ (by norm_num)
  have hd : 0 < d := pow_pos (by decide) _
  have hg := MobiusPowers.transform_irreducible hd
    (c := (2:ℚ)^(n+1)-1) (by simp) (MobiusPowers.binomial_irreducible hn)
  have he : Even d := (by decide : Even 2).pow_of_ne_zero hn.ne'
  have hsign : ((1:ℚ[X])-X)^d = (X-1)^d := by
    rw [← neg_sub X 1, he.neg_pow]
  have hcoef : C (1/2 : ℚ)*C (b⁻¹) * C ((2:ℚ)^(n+1)-1) =
      C (1/2 : ℚ) + C (1/2 : ℚ)*C b⁻¹*C (b-1) := by
    simp only [← C_mul, ← C_add]
    apply congrArg C
    rw [pow_succ]
    change 1/2*b⁻¹*(b*2-1) = 1/2+1/2*b⁻¹*(b-1)
    field_simp
    <;> ring
  have hrow : OMA.S_oeis_a340263.row n =
      (C (1/2 : ℚ)*C b⁻¹) * (((X:ℚ[X])+1)^d + C ((2:ℚ)^(n+1)-1)*(X-1)^d) := by
    change C (1/2 : ℚ) * ((1-X)^d + C b⁻¹ * (C (b-1)*(X-1)^d+(X+1)^d)) = _
    rw [hsign]
    linear_combination -(X-1)^d*hcoef
  rw [hrow]
  have hu : IsUnit (C (1/2 : ℚ)*C b⁻¹) :=
    (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by norm_num))).mul
      (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hb)))
  exact irreducible_mul_iff.mpr (Or.inr ⟨hg,hu⟩)
