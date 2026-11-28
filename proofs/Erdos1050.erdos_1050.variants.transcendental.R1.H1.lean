import OMAReductions.R_Erdos1050_erdos_1050_variants_transcendental_R1

/-
A specialized proof of Borwein's known irrationality theorem for q = 2.
Parent reduction: @desenyon, upstream PR #3330.
Source: Peter B. Borwein, On the irrationality of certain series,
Math. Proc. Cambridge Philos. Soc. 112(1) (1992), 141-146.
DOI: 10.1017/S030500410007081X (refereed).

The polynomial denominator has constant coefficient 1, so integer Bezout
remainders give a rational linear form in the Lambert series. Lagrange
partial fractions and P_(n-1) * P_floor((n-1)/2), with
P_r = product_(1 <= j <= r) (2^j - 1), clear its coefficients.
The remaining tail has a fixed nonzero sign. A geometric estimate makes
the resulting nonzero integer strictly smaller than 1 in absolute value.
This proof is independently written; the transcendence step remains open.
-/

import Mathlib.Data.Rat.BigOperators
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.GCongr
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace D7Lambert

open Polynomial Finset

lemma integral_split (N Q : ℤ[X]) (hQ : Q.coeff 0 = 1) (r : ℕ) :
    ∃ L U : ℤ[X], L.degree < r ∧ N = L * Q + X ^ r * U := by
  have hd : (X : ℤ[X]) ∣ Q - 1 := by
    apply X_dvd_iff.mpr
    simp [hQ]
  obtain ⟨W, hW⟩ := hd
  have hc : IsCoprime Q (X : ℤ[X]) := by
    refine ⟨1, -W, ?_⟩
    linear_combination hW
  obtain ⟨A, B, hAB⟩ := (hc.pow_right : IsCoprime Q (X ^ r))
  let L := (N * A) %ₘ (X ^ r)
  let U := N * B + ((N * A) /ₘ (X ^ r)) * Q
  refine ⟨L, U, ?_, ?_⟩
  · simpa [L] using degree_modByMonic_lt (N * A) (monic_X_pow r)
  · have he := modByMonic_add_div (N * A) (X ^ r)
    dsimp [L, U]
    linear_combination -N * hAB - Q * he

lemma integral_split_degree (N Q : ℤ[X]) (hQ : Q.coeff 0 = 1)
    (r : ℕ) (hr : 0 < r) (hN : N.natDegree ≤ r) (hdeg : Q.natDegree ≤ r+1) :
    ∃ L U : ℤ[X], L.degree < r ∧ U.natDegree ≤ r ∧ N = L * Q + X ^ r * U := by
  obtain ⟨L,U,hL,h⟩ := integral_split N Q hQ r
  refine ⟨L,U,hL,?_,h⟩
  by_cases hU : U = 0
  · simp [hU]
  have hLu : L.natDegree < r := by
    by_cases hL0 : L = 0
    · simpa [hL0] using hr
    exact (natDegree_lt_iff_degree_lt hL0).mpr hL
  have he : X ^ r * U = N - L * Q := by linear_combination -h
  have hh : (X ^ r * U).natDegree ≤ 2*r := by
    rw [he]
    apply (natDegree_sub_le ..).trans
    apply max_le (hN.trans (by omega))
    exact (natDegree_mul_le (p := L) (q := Q)).trans (by omega)
  rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hU, natDegree_X_pow] at hh
  omega

noncomputable def denPoly (n : ℕ) : ℤ[X] :=
  ∏ k ∈ range n, (1 + C (2^k) * X)

noncomputable def numPoly (t : ℤ) (n : ℕ) : ℤ[X] :=
  ∏ i ∈ Icc 1 (n-1), (C t * X - C (2^i))

lemma denPoly_zero (n : ℕ) : (denPoly n).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero]
  simp only [denPoly, eval_prod, eval_add, eval_one, eval_mul, eval_C, eval_X,
    mul_zero, add_zero, prod_const_one]

lemma denPoly_degree (n : ℕ) : (denPoly n).natDegree ≤ n := by
  unfold denPoly
  apply (natDegree_prod_le _ _).trans
  calc
    (∑ k ∈ range n, (1 + C (2^k) * X : ℤ[X]).natDegree) ≤ ∑ k ∈ range n, 1 := by
      apply sum_le_sum
      intro k hk
      exact (natDegree_add_le ..).trans (by simp)
    _ = n := by simp

lemma numPoly_degree (t : ℤ) (n : ℕ) : (numPoly t n).natDegree ≤ n-1 := by
  unfold numPoly
  apply (natDegree_prod_le _ _).trans
  calc
    (∑ i ∈ Icc 1 (n-1), (C t * X - C (2^i) : ℤ[X]).natDegree) ≤
        ∑ i ∈ Icc 1 (n-1), 1 := by
      apply sum_le_sum
      intro k hk
      apply (natDegree_sub_le ..).trans
      apply max_le _ (by simp)
      exact (natDegree_mul_le ..).trans (by simp)
    _ = n-1 := by simp

lemma integer_remainders (t : ℤ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ L U : ℤ[X], L.degree < (n-1 : ℕ) ∧ U.natDegree < n ∧
      numPoly t n = L * denPoly n + X^(n-1) * U := by
  obtain ⟨L,U,hL,hU,he⟩ := integral_split_degree (numPoly t n) (denPoly n)
    (denPoly_zero n) (n-1) (by omega) (numPoly_degree t n)
    (by simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using denPoly_degree n)
  exact ⟨L,U,hL,by omega,he⟩

noncomputable def node (k : ℕ) : ℚ := -((2:ℚ)^k)⁻¹

lemma linear_partial_fractions {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℚ) (ha : ∀ i ∈ s, a i ≠ 0)
    (hi : Set.InjOn a s) (hs : s.Nonempty)
    (U : ℚ[X]) (hU : U.natDegree < s.card) :
    U = ∑ i ∈ s, C (U.eval (-(a i)⁻¹) /
        ∏ j ∈ s.erase i, (1 - a j / a i)) *
      ∏ j ∈ s.erase i, (1 + C (a j) * X) := by
  have hn : 0 < s.card := card_pos.mpr hs
  have hninj : Set.InjOn (fun i => -(a i)⁻¹) s := by
    intro i his j hjs he
    apply hi his hjs
    simpa only [neg_inj, inv_inj] using he
  have hfactor (i : ι) : (1 + C (a i) * X : ℚ[X]).natDegree ≤ 1 := by
    apply (natDegree_add_le ..).trans
    apply max_le (by simp)
    exact (natDegree_mul_le ..).trans (by simp)
  apply eq_of_degrees_lt_of_eval_index_eq s hninj
      (degree_le_natDegree.trans_lt (by exact_mod_cast hU))
  · apply degree_le_natDegree.trans_lt
    have hb : (∑ i ∈ s, C (U.eval (-(a i)⁻¹) /
          ∏ j ∈ s.erase i, (1 - a j / a i)) *
        ∏ j ∈ s.erase i, (1 + C (a j) * X)).natDegree ≤ s.card-1 := by
      apply natDegree_sum_le_of_forall_le
      intro i his
      apply (natDegree_mul_le ..).trans
      simp only [natDegree_C, zero_add]
      apply (natDegree_prod_le ..).trans
      calc
        (∑ j ∈ s.erase i, (1 + C (a j) * X : ℚ[X]).natDegree) ≤
            ∑ j ∈ s.erase i, 1 := sum_le_sum (fun j _ => hfactor j)
        _ = s.card-1 := by simp [card_erase_of_mem his]
    exact_mod_cast (lt_of_le_of_lt hb (Nat.sub_lt hn (by decide : 0 < 1)))
  · intro i his
    rw [eval_finsetSum, sum_eq_single i]
    · simp only [eval_mul, eval_C, eval_prod, eval_add, eval_one, eval_X]
      have hd : (∏ j ∈ s.erase i, (1 - a j / a i)) ≠ 0 := by
        apply prod_ne_zero_iff.mpr
        intro j hjs
        have hj : j ∈ s := mem_of_mem_erase hjs
        have hji : j ≠ i := (mem_erase.mp hjs).1
        apply sub_ne_zero.mpr
        intro he
        have he' : a j = a i := by
          have hh := (div_eq_one_iff_eq (ha i his)).mp he.symm
          exact hh
        exact hji (hi hj his he')
      have hp : (∏ x ∈ s.erase i, (1 + a x * -(a i)⁻¹)) =
          ∏ x ∈ s.erase i, (1 - a x / a i) := by
        apply prod_congr rfl
        intro j hj
        simp [div_eq_mul_inv, sub_eq_add_neg]
      rw [hp, div_mul_cancel₀ _ hd]
    · intro j hjs hji
      simp only [eval_mul, eval_C, eval_prod, eval_add, eval_one, eval_X]
      have hz : (∏ k ∈ s.erase j, (1 + a k * -(a i)⁻¹)) = 0 := by
        apply prod_eq_zero (mem_erase.mpr ⟨hji.symm,his⟩)
        rw [mul_neg, mul_inv_cancel₀ (ha i his)]
        norm_num
      rw [hz, mul_zero]
    · exact fun h => (h his).elim

lemma node_ne_zero (k : ℕ) : node k ≠ 0 := by
  simp [node]

lemma node_injective : Function.Injective node := by
  intro i j he
  have hp : (2:ℚ)^i = 2^j := by simpa [node] using he
  exact (pow_right_inj₀ (by norm_num : (0:ℚ) < 2)
    (by norm_num : (2:ℚ) ≠ 1)).mp hp

lemma denPoly_node (n k : ℕ) (hk : k < n) :
    (denPoly n).eval₂ (Int.castRingHom ℚ) (node k) = 0 := by
  simp only [denPoly, eval₂_finsetProd, eval₂_add, eval₂_one, eval₂_mul,
    eval₂_C, eval₂_X]
  apply prod_eq_zero (mem_range.mpr hk)
  simp [node]

lemma numPoly_node (t : ℤ) (n k : ℕ) :
    (numPoly t n).eval₂ (Int.castRingHom ℚ) (node k) =
      node k ^ (n-1) * ∏ i ∈ Icc 1 (n-1), ((t:ℚ) + 2^(i+k)) := by
  simp only [numPoly, eval₂_finsetProd, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X,
    map_pow, map_ofNat, eval₂_pow, eval₂_ofNat]
  have he (i : ℕ) : (t:ℚ)*node k - 2^i = node k*((t:ℚ)+2^(i+k)) := by
    dsimp [node]
    rw [pow_add]
    field_simp <;> ring
  change (∏ i ∈ Icc 1 (n-1), ((t:ℚ)*node k - (2:ℚ)^i)) = _
  simp_rw [he]
  rw [prod_mul_distrib, prod_const]
  simp

lemma quotient_at_node {t : ℤ} {n : ℕ} {L U : ℤ[X]}
    (he : numPoly t n = L * denPoly n + X^(n-1) * U)
    {k : ℕ} (hk : k < n) :
    U.eval₂ (Int.castRingHom ℚ) (node k) =
      ∏ i ∈ Icc 1 (n-1), ((t:ℚ) + 2^(i+k)) := by
  have hh := congrArg (eval₂RingHom (Int.castRingHom ℚ) (node k)) he
  simp only [coe_eval₂RingHom, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X] at hh
  rw [denPoly_node n k hk, mul_zero, zero_add, numPoly_node] at hh
  exact mul_left_cancel₀ (pow_ne_zero _ (node_ne_zero k)) hh.symm

noncomputable def partialCoeff (t : ℤ) (n k : ℕ) : ℚ :=
  (∏ i ∈ Icc 1 (n-1), ((t:ℚ) + 2^(i+k))) /
    ∏ j ∈ (range n).erase k, (1 - (2:ℚ)^j / 2^k)

lemma quotient_partial_fractions {t : ℤ} {n : ℕ} (hn : 2 ≤ n) {L U : ℤ[X]}
    (hU : U.natDegree < n)
    (he : numPoly t n = L * denPoly n + X^(n-1) * U) :
    U.map (Int.castRingHom ℚ) =
      ∑ k ∈ range n, C (partialCoeff t n k) *
        ∏ j ∈ (range n).erase k, (1 + C ((2:ℚ)^j) * X) := by
  have hc := linear_partial_fractions (range n) (fun k => (2:ℚ)^k)
    (fun k _ => by positivity)
    (by
      intro i hi j hj he
      exact (pow_right_inj₀ (by norm_num : (0:ℚ) < 2)
        (by norm_num : (2:ℚ) ≠ 1)).mp he)
    (by exact ⟨0, mem_range.mpr (by omega)⟩)
    (U.map (Int.castRingHom ℚ))
    (by simpa using (natDegree_map_le ..).trans_lt hU)
  convert hc using 1
  apply sum_congr rfl
  intro k hk
  congr 2
  simp only [eval_map]
  rw [show -((2:ℚ)^k)⁻¹ = node k from rfl, quotient_at_node he (mem_range.mp hk)]
  rfl

def mersenneProd (r : ℕ) : ℕ := ∏ j ∈ range r, (2^(j+1)-1)

lemma mersenneProd_pos (r : ℕ) : 0 < mersenneProd r := by
  apply prod_pos
  intro j hj
  have hh : 1 < (2:ℕ)^(j+1) := one_lt_pow₀ (by norm_num) (by omega)
  omega

lemma mersenneProd_dvd {r s : ℕ} (h : r ≤ s) : mersenneProd r ∣ mersenneProd s := by
  exact prod_dvd_prod_of_subset (range r) (range s) _ (range_mono h)

lemma paired_denominator_dvd {r k : ℕ} (hk : k ≤ r) :
    mersenneProd k * mersenneProd (r-k) ∣ mersenneProd r * mersenneProd (r/2) := by
  by_cases h : k ≤ r/2
  · have h1 := mersenneProd_dvd h
    have h2 := mersenneProd_dvd (show r-k ≤ r by omega)
    simpa [mul_comm] using mul_dvd_mul h1 h2
  · have h1 := mersenneProd_dvd hk
    have h2 := mersenneProd_dvd (show r-k ≤ r/2 by omega)
    exact mul_dvd_mul h1 h2

lemma range_dist_product (n k : ℕ) (hk : k < n) :
    (∏ j ∈ (range n).erase k, (2^(Nat.dist j k)-1)) =
      mersenneProd k * mersenneProd (n-k-1) := by
  have hs : (range n).erase k = range k ∪ Ico (k+1) n := by
    ext j
    simp only [mem_erase, mem_range, mem_union, mem_Ico]
    omega
  rw [hs, prod_union (by
    rw [disjoint_left]
    intro j hj hj'
    simp only [mem_range, mem_Ico] at hj hj'
    omega)]
  congr 1
  · have he : (∏ j ∈ range k, (2^(Nat.dist j k)-1)) =
        ∏ j ∈ range k, (2^((k-1-j)+1)-1) := by
      apply prod_congr rfl
      intro j hj
      have hjk := mem_range.mp hj
      congr 2
      rw [Nat.dist_eq_sub_of_le hjk.le]
      omega
    rw [he, prod_range_reflect (fun j => (2^(j+1)-1 : ℕ)) k]
    rfl
  · rw [prod_Ico_eq_prod_range]
    have he : n-(k+1) = n-k-1 := by omega
    rw [he]
    unfold mersenneProd
    apply prod_congr rfl
    intro j hj
    congr 2
    rw [Nat.dist_eq_sub_of_le_right (by omega : k ≤ k+1+j)]
    omega

lemma dyadic_factor_ne_zero {j k : ℕ} (hjk : j ≠ k) :
    1 - (2:ℚ)^j / 2^k ≠ 0 := by
  intro he
  have hh : (2:ℚ)^j = 2^k :=
    (div_eq_one_iff_eq (by positivity)).mp (sub_eq_zero.mp he).symm
  exact hjk ((pow_right_inj₀ (by norm_num : (0:ℚ)<2)
    (by norm_num : (2:ℚ) ≠ 1)).mp hh)

lemma cleared_dyadic_factor {j k : ℕ} (hjk : j ≠ k) :
    ((2^(Nat.dist j k)-1 : ℕ):ℚ) * (1 - (2:ℚ)^j / 2^k)⁻¹ ∈
      (Int.castRingHom ℚ).range := by
  have hd := dyadic_factor_ne_zero hjk
  rcases lt_or_gt_of_ne hjk with h | h
  · refine ⟨(2:ℤ)^(k-j), ?_⟩
    change (((2:ℤ)^(k-j):ℤ):ℚ) = _
    symm
    rw [← div_eq_mul_inv, div_eq_iff hd, Nat.dist_eq_sub_of_le h.le,
      Nat.cast_sub (one_le_pow₀ (by norm_num : (1:ℕ) ≤ 2))]
    push_cast
    have hp : (2:ℚ)^k = 2^j * 2^(k-j) := by
      rw [← pow_add, Nat.add_sub_of_le h.le]
    rw [hp]
    field_simp <;> ring
  · refine ⟨-1, ?_⟩
    change ((-1:ℤ):ℚ) = _
    symm
    rw [← div_eq_mul_inv, div_eq_iff hd, Nat.dist_eq_sub_of_le_right h.le,
      Nat.cast_sub (one_le_pow₀ (by norm_num : (1:ℕ) ≤ 2))]
    push_cast
    have hp : (2:ℚ)^j = 2^k * 2^(j-k) := by
      rw [← pow_add, Nat.add_sub_of_le h.le]
    rw [hp]
    field_simp <;> ring

lemma cleared_coeff_mem (t : ℤ) {n k : ℕ} (hk : k < n) :
    ((mersenneProd (n-1) * mersenneProd ((n-1)/2):ℕ):ℚ) * partialCoeff t n k ∈
      (Int.castRingHom ℚ).range := by
  let J := (range n).erase k
  let D := ∏ j ∈ J, (2^(Nat.dist j k)-1)
  have hD : D ∣ mersenneProd (n-1) * mersenneProd ((n-1)/2) := by
    dsimp [D,J]
    rw [range_dist_product n k hk]
    have he : n-k-1 = (n-1)-k := by omega
    rw [he]
    exact paired_denominator_dvd (by omega)
  obtain ⟨d,hd⟩ := hD
  have hp : (∏ j ∈ J,
      ((2^(Nat.dist j k)-1:ℕ):ℚ) * (1-(2:ℚ)^j/2^k)⁻¹) ∈
      (Int.castRingHom ℚ).range := by
    apply Subring.prod_mem
    intro j hj
    exact cleared_dyadic_factor (mem_erase.mp hj).1
  have hnum : (∏ i ∈ Icc 1 (n-1), ((t:ℚ)+2^(i+k))) ∈
      (Int.castRingHom ℚ).range := by
    apply Subring.prod_mem
    intro i hi
    exact ⟨t+2^(i+k), by simp⟩
  have hdin : (d:ℚ) ∈ (Int.castRingHom ℚ).range := ⟨(d:ℤ), by simp⟩
  convert (Int.castRingHom ℚ).range.mul_mem hdin
    ((Int.castRingHom ℚ).range.mul_mem hnum hp) using 1
  simp only [partialCoeff, div_eq_mul_inv, ← prod_inv_distrib, prod_mul_distrib] 
  have he : ((mersenneProd (n-1)*mersenneProd ((n-1)/2):ℕ):ℚ) = (D:ℚ)*d := by
    exact_mod_cast hd
  rw [he]
  simp only [D, Nat.cast_prod]
  dsimp [J]
  ring

lemma real_den_eval (n : ℕ) (x : ℝ) :
    (denPoly n).eval₂ (Int.castRingHom ℝ) x = ∏ j ∈ range n, (1+(2:ℝ)^j*x) := by
  simp [denPoly, eval₂_finsetProd, eval₂_pow]

lemma real_quotient_eval {t : ℤ} {n : ℕ} (hn : 2 ≤ n) {L U : ℤ[X]}
    (hU : U.natDegree < n)
    (he : numPoly t n = L * denPoly n + X^(n-1) * U) (x : ℝ) :
    U.eval₂ (Int.castRingHom ℝ) x =
      ∑ k ∈ range n, (partialCoeff t n k : ℝ) *
        ∏ j ∈ (range n).erase k, (1+(2:ℝ)^j*x) := by
  have hh := congrArg (eval₂RingHom (Rat.castHom ℝ) x)
    (quotient_partial_fractions hn hU he)
  have hc : (Rat.castHom ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ := by
    ext z
    simp
  simpa only [coe_eval₂RingHom, eval₂_map, hc, eval₂_finsetSum,
    eval₂_mul, eval₂_C, eval₂_finsetProd, eval₂_add, eval₂_one, eval₂_X,
    map_pow, map_ofNat, eval₂_pow, eval₂_ofNat, Rat.coe_castHom] using hh

lemma point_decomposition {t : ℤ} {n : ℕ} (hn : 2 ≤ n) {L U : ℤ[X]}
    (hU : U.natDegree < n)
    (he : numPoly t n = L * denPoly n + X^(n-1) * U)
    (x : ℝ) (hx : x ≠ 0) (hd : ∀ k < n, 1+(2:ℝ)^k*x ≠ 0) :
    (numPoly t n).eval₂ (Int.castRingHom ℝ) x /
        (x^(n-1) * (denPoly n).eval₂ (Int.castRingHom ℝ) x) =
      (∑ k ∈ range n, (partialCoeff t n k : ℝ)/(1+(2:ℝ)^k*x)) +
        L.eval₂ (Int.castRingHom ℝ) x / x^(n-1) := by
  have hQ : (denPoly n).eval₂ (Int.castRingHom ℝ) x ≠ 0 := by
    rw [real_den_eval]
    exact prod_ne_zero_iff.mpr (fun k hk => hd k (mem_range.mp hk))
  have hsplit := congrArg (eval₂RingHom (Int.castRingHom ℝ) x) he
  simp only [coe_eval₂RingHom, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X] at hsplit
  have hu : U.eval₂ (Int.castRingHom ℝ) x /
      (denPoly n).eval₂ (Int.castRingHom ℝ) x =
        ∑ k ∈ range n, (partialCoeff t n k : ℝ)/(1+(2:ℝ)^k*x) := by
    rw [real_quotient_eval hn hU he, Finset.sum_div]
    apply sum_congr rfl
    intro k hk
    rw [real_den_eval, ← mul_prod_erase (range n) _ hk]
    have hr : (∏ j ∈ (range n).erase k, (1+(2:ℝ)^j*x)) ≠ 0 :=
      prod_ne_zero_iff.mpr (fun j hj => hd j (mem_range.mp (mem_of_mem_erase hj)))
    exact mul_div_mul_right _ _ hr
  rw [hsplit, ← hu]
  field_simp
  <;> ring


def shiftProd (t : ℤ) (n : ℕ) : ℤ := ∏ h ∈ Icc 1 (n-1), (t+2^h)

def commonDen (n : ℕ) : ℕ := mersenneProd (n-1)*mersenneProd ((n-1)/2)

noncomputable def rationalForm (t : ℤ) (n : ℕ) (L : ℤ[X]) (S : ℚ) : ℚ :=
  (∑ k ∈ range n, partialCoeff t n k * t *
    (S-∑ h ∈ range k, 1/((2:ℚ)^(h+1)+t))) +
  ∑ i ∈ range (n-1), (L.coeff i:ℚ)*(t:ℚ)^(n-1-i)/((2:ℚ)^(n-1-i)-1)

lemma rat_div_mem {a b : ℤ} (h : b ∣ a) :
    (a:ℚ)/b ∈ (Int.castRingHom ℚ).range := by
  exact ⟨a/b, Rat.intCast_div a b h⟩

lemma shift_prefix_mem (t : ℤ) {n k : ℕ} (hk : k < n) :
    (shiftProd t n:ℚ)*(∑ h ∈ range k, 1/((2:ℚ)^(h+1)+t)) ∈
      (Int.castRingHom ℚ).range := by
  rw [mul_sum]
  apply Subring.sum_mem
  intro h hh
  have hm : h+1 ∈ Icc 1 (n-1) := mem_Icc.mpr ⟨by omega, by have := mem_range.mp hh; omega⟩
  have hd : t+2^(h+1) ∣ shiftProd t n := dvd_prod_of_mem _ hm
  convert rat_div_mem hd using 1 <;> push_cast <;> ring

lemma commonDen_geo_mem {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    (commonDen n:ℚ)/((2:ℚ)^j-1) ∈ (Int.castRingHom ℚ).range := by
  have hm : j-1 ∈ range (n-1) := mem_range.mpr (by omega)
  have hd : 2^j-1 ∣ mersenneProd (n-1) := by
    have hh := dvd_prod_of_mem (fun r => (2^(r+1)-1:ℕ)) hm
    obtain ⟨d,hd⟩ := hh
    refine ⟨d,?_⟩
    simpa only [Nat.sub_add_cancel hj,mersenneProd] using hd
  have hd' : (2:ℤ)^j-1 ∣ (commonDen n:ℤ) := by
    have hh : 2^j-1 ∣ commonDen n := hd.trans (dvd_mul_right _ _)
    have hp : 1 ≤ (2:ℕ)^j := one_le_pow₀ (by norm_num)
    have hc : ((2^j-1:ℕ):ℤ) ∣ (commonDen n:ℤ) := Int.ofNat_dvd.mpr hh
    simpa only [Nat.cast_sub hp,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hc
  convert rat_div_mem hd' using 1 <;> push_cast <;> rfl

lemma rationalForm_integral (t : ℤ) {n : ℕ} (hn : 2 ≤ n) (L : ℤ[X])
    (S : ℚ) (B : ℕ) (hS : (B:ℚ)*S ∈ (Int.castRingHom ℚ).range) :
    (B:ℚ)*(commonDen n:ℚ)*(shiftProd t n:ℚ)*rationalForm t n L S ∈
      (Int.castRingHom ℚ).range := by
  let R := (Int.castRingHom ℚ).range
  have hb : (B:ℚ) ∈ R := ⟨(B:ℤ), by simp⟩
  have he : (shiftProd t n:ℚ) ∈ R := ⟨shiftProd t n, rfl⟩
  have ht : (t:ℚ) ∈ R := ⟨t,rfl⟩
  unfold rationalForm
  rw [mul_add, mul_sum, mul_sum]
  apply R.add_mem
  · apply R.sum_mem
    intro k hk
    have ha : (commonDen n:ℚ)*partialCoeff t n k ∈ R :=
      cleared_coeff_mem t (mem_range.mp hk)
    have hp : (shiftProd t n:ℚ)*(∑ h ∈ range k, 1/((2:ℚ)^(h+1)+t)) ∈ R :=
      shift_prefix_mem t (mem_range.mp hk)
    convert R.mul_mem ht (R.mul_mem ha (R.sub_mem (R.mul_mem he hS) (R.mul_mem hb hp))) using 1 <;> ring
  · apply R.sum_mem
    intro i hi
    have hij : 0 < n-1-i := by have := mem_range.mp hi; omega
    have hc : (L.coeff i:ℚ) ∈ R := ⟨L.coeff i,rfl⟩
    have hp : (t:ℚ)^(n-1-i) ∈ R := R.pow_mem ht _
    have hg : (commonDen n:ℚ)/((2:ℚ)^(n-1-i)-1) ∈ R := commonDen_geo_mem hij (by omega)
    convert R.mul_mem hb (R.mul_mem he (R.mul_mem hc (R.mul_mem hp hg))) using 1 <;> ring


open Finset

noncomputable def lambert (t : ℤ) : ℝ := ∑' m : ℕ, 1/((2:ℝ)^(m+1)+t)

lemma lambert_summable (t : ℤ) : Summable (fun m : ℕ => 1/((2:ℝ)^(m+1)+t)) := by
  let L := t.natAbs
  have ht : |(t:ℝ)| ≤ (2:ℝ)^L := by
    have hh : t.natAbs ≤ 2^t.natAbs := (Nat.lt_two_pow_self).le
    simpa only [L, Nat.cast_natAbs, Int.cast_abs, Nat.cast_pow, Nat.cast_ofNat] using
      (show (t.natAbs:ℝ) ≤ (2^t.natAbs:ℕ) by exact_mod_cast hh)
  have hb (m : ℕ) : |1/((2:ℝ)^(m+L+1)+t)| ≤ (1/(2:ℝ)^L)*(1/2:ℝ)^m := by
    have hp : (2:ℝ)^L ≤ 2^(m+L) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hd : (2:ℝ)^(m+L) ≤ 2^(m+L+1)+t := by
      rw [pow_succ]
      linarith [neg_abs_le (t:ℝ)]
    rw [abs_div, abs_one, abs_of_pos (lt_of_lt_of_le (by positivity) hd)]
    calc
      _ ≤ 1/(2:ℝ)^(m+L) := one_div_le_one_div_of_le (by positivity) hd
      _ = _ := by rw [pow_add]; simp [div_eq_mul_inv, mul_comm]
  have hg := (hasSum_geometric_of_lt_one (r := (1/2:ℝ))
    (by norm_num) (by norm_num)).mul_left (1/(2:ℝ)^L)
  apply (summable_nat_add_iff L).mp
  exact hg.summable.of_norm_bounded (fun m => by simpa [Real.norm_eq_abs] using hb m)

lemma shifted_denominator (t : ℤ) (ht : t ≠ 0) (k m : ℕ) :
    1/(1+(2:ℝ)^k*((2:ℝ)^(m+1)/t)) =
      (t:ℝ)*(1/((2:ℝ)^(m+k+1)+t)) := by
  have ht' : (t:ℝ) ≠ 0 := by exact_mod_cast ht
  have he : 1+(2:ℝ)^k*((2:ℝ)^(m+1)/t) = ((2:ℝ)^(m+k+1)+t)/t := by
    rw [show m+k+1 = k+(m+1) by omega, pow_add]
    field_simp
    ring
  rw [he, one_div, inv_div]
  ring

lemma hasSum_shifted (t : ℤ) (ht : t ≠ 0) (k : ℕ) :
    HasSum (fun m : ℕ => 1/(1+(2:ℝ)^k*((2:ℝ)^(m+1)/t)))
      ((t:ℝ)*(lambert t - ∑ h ∈ range k, 1/((2:ℝ)^(h+1)+t))) := by
  have hs := lambert_summable t
  have htail := (summable_nat_add_iff k).mpr hs
  have he := hs.sum_add_tsum_nat_add k
  have hv : (∑' m : ℕ, 1/((2:ℝ)^(m+k+1)+t)) =
      lambert t - ∑ h ∈ range k, 1/((2:ℝ)^(h+1)+t) := by
    dsimp [lambert]
    linarith only [he]
  have hh := htail.hasSum.mul_left (t:ℝ)
  rw [hv] at hh
  exact hh.congr_fun (fun m => shifted_denominator t ht k m)

lemma hasSum_negative_dyadic (j : ℕ) (hj : 0 < j) :
    HasSum (fun m : ℕ => (1/(2:ℝ)^j)^(m+1)) (1/((2:ℝ)^j-1)) := by
  have hp : 1 < (2:ℝ)^j := one_lt_pow₀ (by norm_num) hj.ne'
  have hg := (hasSum_geometric_of_lt_one (r := 1/(2:ℝ)^j)
    (by positivity) (by rw [div_lt_one (by positivity)]; exact hp)).mul_left (1/(2:ℝ)^j)
  have hh : HasSum (fun m : ℕ => (1/(2:ℝ)^j)^(m+1))
      ((1/(2:ℝ)^j)*(1-1/(2:ℝ)^j)⁻¹) := hg.congr_fun (fun m => by
    rw [pow_succ]
    ring)
  have he : (1/(2:ℝ)^j)*(1-1/(2:ℝ)^j)⁻¹ = 1/((2:ℝ)^j-1) := by
    have hne : (2:ℝ)^j-1 ≠ 0 := by linarith
    have hne' : 1-1/(2:ℝ)^j ≠ 0 := by
      have : 1/(2:ℝ)^j < 1 := (div_lt_one (by positivity)).mpr hp
      linarith
    field_simp
    <;> ring
  simpa only [he] using hh



open Finset

def triangle (n : ℕ) : ℕ := ∑ k ∈ range n, k

lemma triangle_succ (n : ℕ) : triangle (n+1) = triangle n+n := by
  simp [triangle, sum_range_succ]

lemma triangle_bound (n : ℕ) : 2*triangle n ≤ n*n := by
  induction n with
  | zero => simp [triangle]
  | succ n ih => rw [triangle_succ]; nlinarith

lemma triangle_mono : Monotone triangle := by
  intro n m h
  exact sum_le_sum_of_subset (range_mono h)

noncomputable def tailKernel (t : ℤ) (n r : ℕ) : ℝ :=
  (∏ i ∈ Icc 1 (n-1), (1-(2:ℝ)^i/2^(n+r))) /
    ∏ k ∈ range n, ((2:ℝ)^(n+r+k)+t)

lemma tail_den_lower (t : ℤ) {n r k : ℕ}
    (ht : 2*|(t:ℝ)| ≤ (2:ℝ)^n) :
    (2:ℝ)^(n+r+k)/2 ≤ (2:ℝ)^(n+r+k)+t := by
  have hp : (2:ℝ)^n ≤ 2^(n+r+k) := pow_le_pow_right₀ (by norm_num) (by omega)
  linarith [neg_abs_le (t:ℝ)]

lemma tail_num_factor_pos {n r i : ℕ} (hi : i ∈ Icc 1 (n-1)) :
    0 < 1-(2:ℝ)^i/2^(n+r) := by
  have him : i < n+r := by have := mem_Icc.mp hi; omega
  have hp : (2:ℝ)^i < 2^(n+r) := pow_lt_pow_right₀ (by norm_num) him
  have hq : (2:ℝ)^i/2^(n+r) < 1 := (div_lt_one (by positivity)).mpr hp
  linarith

lemma tailKernel_pos (t : ℤ) {n r : ℕ}
    (ht : 2*|(t:ℝ)| ≤ (2:ℝ)^n) : 0 < tailKernel t n r := by
  apply div_pos
  · exact prod_pos (fun i hi => tail_num_factor_pos hi)
  · apply prod_pos
    intro k hk
    exact lt_of_lt_of_le (by positivity) (tail_den_lower t ht)

lemma tailKernel_bound (t : ℤ) {n r : ℕ}
    (ht : 2*|(t:ℝ)| ≤ (2:ℝ)^n) :
    tailKernel t n r ≤ (2:ℝ)^n/2^(n*n+triangle n) * (1/(2:ℝ)^n)^r := by
  have hnum : (∏ i ∈ Icc 1 (n-1), (1-(2:ℝ)^i/2^(n+r))) ≤ 1 := by
    apply prod_le_one
    · intro i hi
      exact (tail_num_factor_pos hi).le
    · intro i hi
      have hh : 0 ≤ (2:ℝ)^i/2^(n+r) := by positivity
      linarith
  have hd : (∏ k ∈ range n, ((2:ℝ)^(n+r+k)/2)) ≤
      ∏ k ∈ range n, ((2:ℝ)^(n+r+k)+t) := by
    apply prod_le_prod
    · intro k hk
      positivity
    · intro k hk
      exact tail_den_lower t ht
  have hdpos : 0 < ∏ k ∈ range n, ((2:ℝ)^(n+r+k)/2) := prod_pos (fun k hk => by positivity)
  calc
    tailKernel t n r ≤ 1/(∏ k ∈ range n, ((2:ℝ)^(n+r+k)+t)) :=
      div_le_div_of_nonneg_right hnum (lt_of_lt_of_le hdpos hd).le
    _ ≤ 1/(∏ k ∈ range n, ((2:ℝ)^(n+r+k)/2)) := one_div_le_one_div_of_le hdpos hd
    _ = _ := by
      rw [prod_div_distrib, prod_const, card_range, prod_pow_eq_pow_sum]
      have hs : (∑ k ∈ range n, (n+r+k)) = n*(n+r)+triangle n := by
        rw [sum_add_distrib]
        simp [triangle, mul_comm]
      rw [hs, show n*(n+r)+triangle n = (n*n+triangle n)+n*r by ring,
        pow_add, pow_mul]
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]


lemma tailKernel_sum (t : ℤ) {n : ℕ} (hn : 0 < n)
    (ht : 2*|(t:ℝ)| ≤ (2:ℝ)^n) :
    Summable (tailKernel t n) ∧ 0 < ∑' r, tailKernel t n r ∧
      (∑' r, tailKernel t n r) ≤ (2:ℝ)^(n+1)/2^(n*n+triangle n) := by
  let C : ℝ := (2:ℝ)^n/2^(n*n+triangle n)
  have hpow : (2:ℝ) ≤ 2^n := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn)
  have hratio : 1/(2:ℝ)^n < 1 := (div_lt_one (by positivity)).mpr (lt_of_lt_of_le (by norm_num) hpow)
  have hg := (hasSum_geometric_of_lt_one (r := 1/(2:ℝ)^n)
    (by positivity) hratio).mul_left C
  have hbound (r : ℕ) : ‖tailKernel t n r‖ ≤ C*(1/(2:ℝ)^n)^r := by
    rw [Real.norm_of_nonneg (tailKernel_pos t ht).le]
    exact tailKernel_bound t ht
  have hs : Summable (tailKernel t n) := hg.summable.of_norm_bounded hbound
  have hpos : 0 < ∑' r, tailKernel t n r :=
    (tailKernel_pos t (r := 0) ht).trans_le (hs.le_tsum 0 (fun r _ => (tailKernel_pos t ht).le))
  refine ⟨hs,hpos,?_⟩
  have hb := hs.hasSum.norm_le_of_bounded hg hbound
  rw [Real.norm_of_nonneg hpos.le] at hb
  have hhalf : 1/(2:ℝ)^n ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hpow
  have hi : (1-1/(2:ℝ)^n)⁻¹ ≤ 2 := by
    calc
      _ = 1/(1-1/(2:ℝ)^n) := by simp only [one_div]
      _ ≤ 1/(1/2:ℝ) := one_div_le_one_div_of_le (by norm_num) (by linarith)
      _ = 2 := by norm_num
  have hm := mul_le_mul_of_nonneg_left hi (show 0 ≤ C by dsimp [C]; positivity)
  have he : C*2 = (2:ℝ)^(n+1)/2^(n*n+triangle n) := by
    dsimp [C]
    rw [pow_succ]
    ring
  exact hb.trans (by simpa only [he] using hm)



lemma explicit_error_bound (B C m : ℕ) (hC : 1 ≤ C) (hm : 4*C+B+5 ≤ m) :
    (B:ℝ)*(C:ℝ)^(12*m)*(2:ℝ)^(10*m*m+4*m+1) < (2:ℝ)^(16*m*m) := by
  have hB : (B:ℝ) ≤ (2:ℝ)^B := by exact_mod_cast (Nat.lt_two_pow_self (n := B)).le
  have hC' : (C:ℝ) ≤ (2:ℝ)^C := by exact_mod_cast (Nat.lt_two_pow_self (n := C)).le
  have hm5 : 5 ≤ m := by omega
  have hmul : 12*C*m ≤ 3*m*m := by
    have hh := Nat.mul_le_mul_right m (show 4*C ≤ m by omega)
    nlinarith
  have hsmall : B+4*m+1 ≤ m*m := by
    have hh := Nat.mul_le_mul_right m hm5
    omega
  have hexp : B+C*(12*m)+(10*m*m+4*m+1) < 16*m*m := by
    nlinarith
  calc
    (B:ℝ)*(C:ℝ)^(12*m)*(2:ℝ)^(10*m*m+4*m+1) ≤
        (2:ℝ)^B * ((2:ℝ)^C)^(12*m) * (2:ℝ)^(10*m*m+4*m+1) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul hB (pow_le_pow_left₀ (by positivity) hC' _) (by positivity) (by positivity)
    _ = (2:ℝ)^(B+C*(12*m)+(10*m*m+4*m+1)) := by
      rw [← pow_mul, ← pow_add, ← pow_add]
    _ < _ := pow_lt_pow_right₀ (by norm_num) hexp


noncomputable def approximation (t : ℤ) (n m : ℕ) : ℝ :=
  let x := (2:ℝ)^(m+1)/t
  (numPoly t n).eval₂ (Int.castRingHom ℝ) x /
    (x^(n-1)*(denPoly n).eval₂ (Int.castRingHom ℝ) x)

noncomputable def realForm (t : ℤ) (n : ℕ) (L : ℤ[X]) : ℝ :=
  (∑ k ∈ range n, (partialCoeff t n k:ℝ)*(t:ℝ)*
    (lambert t-∑ h ∈ range k, 1/((2:ℝ)^(h+1)+t))) +
  ∑ i ∈ range (n-1), (L.coeff i:ℝ)*(t:ℝ)^(n-1-i)/((2:ℝ)^(n-1-i)-1)

lemma approximation_tail (t : ℤ) (ht : t ≠ 0) {n r : ℕ} (hn : 0 < n) :
    approximation t n (n-1+r) = (t:ℝ)^(2*n-1)*tailKernel t n r := by
  let A : ℝ := 2^(n+r)
  have hA : A ≠ 0 := by dsimp [A]; positivity
  have ht' : (t:ℝ) ≠ 0 := by exact_mod_cast ht
  have hN : (numPoly t n).eval₂ (Int.castRingHom ℝ) (A/t) =
      A^(n-1)*(∏ i ∈ Icc 1 (n-1), (1-(2:ℝ)^i/A)) := by
    simp only [numPoly, eval₂_finsetProd, eval₂_sub, eval₂_mul, eval₂_C,
      eval₂_X, eval₂_pow, eval₂_ofNat, Int.coe_castRingHom, Int.cast_pow, Int.cast_ofNat]
    have he (i : ℕ) : (t:ℝ)*(A/t)-(2:ℝ)^i = A*(1-(2:ℝ)^i/A) := by
      field_simp
      <;> ring
    simp_rw [he]
    rw [prod_mul_distrib, prod_const]
    simp
  have hQ : (denPoly n).eval₂ (Int.castRingHom ℝ) (A/t) =
      (∏ k ∈ range n, ((2:ℝ)^(n+r+k)+t))/(t:ℝ)^n := by
    rw [real_den_eval]
    have he (k : ℕ) : 1+(2:ℝ)^k*(A/t) = ((2:ℝ)^(n+r+k)+t)/t := by
      dsimp [A]
      rw [pow_add]
      field_simp
      <;> ring
    simp_rw [he]
    rw [prod_div_distrib, prod_const, card_range]
  unfold approximation
  have he : n-1+r+1 = n+r := by omega
  rw [he]
  change (numPoly t n).eval₂ (Int.castRingHom ℝ) (A/t) / _ = _
  rw [hN,hQ]
  unfold tailKernel
  change A^(n-1)*(∏ i ∈ Icc 1 (n-1), (1-(2:ℝ)^i/A)) /
      ((A/t)^(n-1)*((∏ k ∈ range n, ((2:ℝ)^(n+r+k)+t))/(t:ℝ)^n)) =
    (t:ℝ)^(2*n-1)*((∏ i ∈ Icc 1 (n-1), (1-(2:ℝ)^i/A)) /
      ∏ k ∈ range n, ((2:ℝ)^(n+r+k)+t))
  have hepow : (t:ℝ)^(2*n-1) = (t:ℝ)^(n-1)*(t:ℝ)^n := by
    rw [← pow_add]
    congr 1
    omega
  rw [hepow, div_pow]
  by_cases hd : (∏ k ∈ range n, ((2:ℝ)^(n+r+k)+t)) = 0
  · simp [hd]
  · field_simp
    <;> ring

lemma approximation_initial_zero (t : ℤ) (ht : t ≠ 0) {n m : ℕ} (hm : m+1 < n) :
    approximation t n m = 0 := by
  have ht' : (t:ℝ) ≠ 0 := by exact_mod_cast ht
  have hN : (numPoly t n).eval₂ (Int.castRingHom ℝ) ((2:ℝ)^(m+1)/t) = 0 := by
    simp only [numPoly, eval₂_finsetProd, eval₂_sub, eval₂_mul, eval₂_C,
      eval₂_X, eval₂_pow, eval₂_ofNat, Int.coe_castRingHom, Int.cast_pow, Int.cast_ofNat]
    apply prod_eq_zero (show m+1 ∈ Icc 1 (n-1) from mem_Icc.mpr ⟨by omega,by omega⟩)
    field_simp <;> ring
  simp [approximation,hN]

lemma shifted_factor (t : ℤ) (ht : t ≠ 0) (k m : ℕ) :
    1+(2:ℝ)^k*((2:ℝ)^(m+1)/t) = ((2:ℝ)^(m+k+1)+t)/t := by
  have ht' : (t:ℝ) ≠ 0 := by exact_mod_cast ht
  rw [show m+k+1 = k+(m+1) by omega, pow_add]
  field_simp
  <;> ring

lemma hasSum_approximation (t : ℤ) (ht : t ≠ 0)
    (htp : ∀ h : ℕ, 1 ≤ h → t ≠ -(2:ℤ)^h)
    {n : ℕ} (hn : 2 ≤ n) {L U : ℤ[X]}
    (hL : L.degree < (n-1:ℕ)) (hU : U.natDegree < n)
    (he : numPoly t n = L * denPoly n + X^(n-1) * U) :
    HasSum (approximation t n) (realForm t n L) := by
  have ht' : (t:ℝ) ≠ 0 := by exact_mod_cast ht
  have hLn : L.natDegree < n-1 := by
    by_cases hL0 : L = 0
    · simp [hL0]; omega
    exact (natDegree_lt_iff_degree_lt hL0).mpr hL
  have hfirst : HasSum (fun m : ℕ => ∑ k ∈ range n,
      (partialCoeff t n k:ℝ)/(1+(2:ℝ)^k*((2:ℝ)^(m+1)/t)))
      (∑ k ∈ range n, (partialCoeff t n k:ℝ)*(t:ℝ)*
        (lambert t-∑ h ∈ range k, 1/((2:ℝ)^(h+1)+t))) := by
    apply hasSum_sum
    intro k hk
    simpa [div_eq_mul_inv,mul_assoc] using
      (hasSum_shifted t ht k).mul_left (partialCoeff t n k:ℝ)
  have hlast : HasSum (fun m : ℕ => ∑ i ∈ range (n-1),
      (L.coeff i:ℝ)*(t:ℝ)^(n-1-i)*(1/(2:ℝ)^(n-1-i))^(m+1))
      (∑ i ∈ range (n-1), (L.coeff i:ℝ)*(t:ℝ)^(n-1-i)/((2:ℝ)^(n-1-i)-1)) := by
    apply hasSum_sum
    intro i hi
    have hij : 0 < n-1-i := by have := mem_range.mp hi; omega
    simpa [div_eq_mul_inv,mul_assoc] using
      (hasSum_negative_dyadic (n-1-i) hij).mul_left ((L.coeff i:ℝ)*(t:ℝ)^(n-1-i))
  apply (hfirst.add hlast).congr_fun
  intro m
  have hx : (2:ℝ)^(m+1)/t ≠ 0 := div_ne_zero (by positivity) ht'
  have hd (k : ℕ) (hk : k < n) : 1+(2:ℝ)^k*((2:ℝ)^(m+1)/t) ≠ 0 := by
    rw [shifted_factor t ht k m]
    apply div_ne_zero _ ht'
    have hh : (2:ℤ)^(m+k+1)+t ≠ 0 := by
      intro hh
      exact htp (m+k+1) (by omega) (by omega)
    exact_mod_cast hh
  rw [show approximation t n m = _ from point_decomposition hn hU he _ hx hd]
  congr 1
  rw [eval₂_eq_sum_range' (Int.castRingHom ℝ) hLn, sum_div]
  apply sum_congr rfl
  intro i hi
  have hepow : ((2:ℝ)^(m+1)/t)^(n-1) =
      ((2:ℝ)^(m+1)/t)^(n-1-i)*((2:ℝ)^(m+1)/t)^i := by
    rw [← pow_add]
    congr 1
    have := mem_range.mp hi
    omega
  have hxpow : ((2:ℝ)^(m+1)/t)^i ≠ 0 := pow_ne_zero _ hx
  rw [hepow,mul_div_mul_right _ _ hxpow,div_pow,div_div_eq_mul_div,one_div_pow]
  simp only [← pow_mul,Nat.mul_comm (m+1) (n-1-i),Int.coe_castRingHom,div_eq_mul_inv,one_mul]

lemma realForm_tail (t : ℤ) (ht : t ≠ 0)
    (htp : ∀ h : ℕ, 1 ≤ h → t ≠ -(2:ℤ)^h)
    {n : ℕ} (hn : 2 ≤ n) {L U : ℤ[X]}
    (hL : L.degree < (n-1:ℕ)) (hU : U.natDegree < n)
    (he : numPoly t n = L * denPoly n + X^(n-1) * U) :
    realForm t n L = (t:ℝ)^(2*n-1)*(∑' r,tailKernel t n r) := by
  have hs := hasSum_approximation t ht htp hn hL hU he
  have hp : (∑ m ∈ range (n-1), approximation t n m) = 0 := by
    apply sum_eq_zero
    intro m hm
    exact approximation_initial_zero t ht (by have := mem_range.mp hm; omega)
  have hh := hs.summable.sum_add_tsum_nat_add (n-1)
  rw [hp,zero_add,hs.tsum_eq] at hh
  rw [← hh]
  have hefun : (fun r => approximation t n (r+(n-1))) =
      (fun r => (t:ℝ)^(2*n-1)*tailKernel t n r) := by
    funext r
    rw [Nat.add_comm,approximation_tail t ht (by omega)]
  rw [hefun,tsum_mul_left]

lemma realForm_of_rational {t : ℤ} {n : ℕ} (L : ℤ[X]) {S : ℚ}
    (hS : lambert t = (S:ℝ)) : realForm t n L = (rationalForm t n L S:ℝ) := by
  simp [realForm,rationalForm,hS]

lemma mersenneProd_bound (r : ℕ) : mersenneProd r ≤ 2^(triangle (r+1)) := by
  calc
    mersenneProd r ≤ ∏ j ∈ range r, (2^(j+1):ℕ) := prod_le_prod' (fun j _ => Nat.sub_le _ _)
    _ = 2^(∑ j ∈ range r, (j+1)) := prod_pow_eq_pow_sum _ _ _
    _ = 2^(triangle (r+1)) := by
      congr 1
      rw [sum_add_distrib,triangle_succ]
      simp [triangle]

lemma commonDen_bound (m : ℕ) (hm : 0 < m) : commonDen (4*m) ≤ 2^(10*m*m) := by
  have hn : 1 ≤ 4*m := by omega
  have h1 : triangle (4*m) ≤ 8*m*m := by have hh := triangle_bound (4*m); nlinarith
  have h2 : triangle ((4*m-1)/2+1) ≤ 2*m*m := by
    have hh := triangle_mono (show (4*m-1)/2+1 ≤ 2*m by omega)
    have hb := triangle_bound (2*m)
    nlinarith
  unfold commonDen
  calc
    mersenneProd (4*m-1)*mersenneProd ((4*m-1)/2) ≤
        2^(triangle (4*m))*2^(triangle ((4*m-1)/2+1)) :=
      Nat.mul_le_mul (by simpa only [Nat.sub_add_cancel hn] using mersenneProd_bound (4*m-1))
        (mersenneProd_bound _)
    _ = 2^(triangle (4*m)+triangle ((4*m-1)/2+1)) := by rw [pow_add]
    _ ≤ 2^(10*m*m) := pow_le_pow_right₀ (by decide : (1:ℕ) ≤ 2) (by nlinarith)

lemma shiftProd_abs_bound (t : ℤ) {n : ℕ} (hn : 0 < n) {C : ℝ}
    (hC : 1+|(t:ℝ)| ≤ C) : |(shiftProd t n:ℝ)| ≤ C^n*(2:ℝ)^(triangle n) := by
  have hC1 : 1 ≤ C := by linarith [abs_nonneg (t:ℝ)]
  have he : (shiftProd t n:ℝ) = ∏ h ∈ Icc 1 (n-1), ((t:ℝ)+(2:ℝ)^h) := by
    simp [shiftProd]
  have hs : (∑ h ∈ Icc 1 (n-1), h) = triangle n := by
    have he : Icc 1 (n-1) = (range n).erase 0 := by
      ext j
      simp only [mem_Icc,mem_erase,mem_range]
      omega
    rw [he]
    have hh := sum_erase_add (range n) (fun h : ℕ => h) (mem_range.mpr hn)
    simpa only [add_zero,triangle] using hh
  rw [he,abs_prod]
  calc
    (∏ h ∈ Icc 1 (n-1), |(t:ℝ)+(2:ℝ)^h|) ≤ ∏ h ∈ Icc 1 (n-1), C*(2:ℝ)^h := by
      apply prod_le_prod
      · intro h hh
        exact abs_nonneg _
      · intro h hh
        have hp : (1:ℝ) ≤ 2^h := one_le_pow₀ (by norm_num)
        have ha := abs_add_le (t:ℝ) ((2:ℝ)^h)
        rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 2^h)] at ha
        have hb := mul_le_mul_of_nonneg_left hp (abs_nonneg (t:ℝ))
        have hc := mul_le_mul_of_nonneg_right hC (by positivity : (0:ℝ) ≤ 2^h)
        nlinarith
    _ = C^(n-1)*(2:ℝ)^(triangle n) := by
      rw [prod_mul_distrib,prod_const,prod_pow_eq_pow_sum,hs]
      simp
    _ ≤ C^n*(2:ℝ)^(triangle n) := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hC1 (by omega)) (by positivity)

lemma realForm_abs_bound (t : ℤ) (ht : t ≠ 0)
    (htp : ∀ h : ℕ, 1 ≤ h → t ≠ -(2:ℤ)^h)
    {n : ℕ} (hn : 2 ≤ n) {L U : ℤ[X]}
    (hL : L.degree < (n-1:ℕ)) (hU : U.natDegree < n)
    (he : numPoly t n = L * denPoly n + X^(n-1) * U)
    (htn : 2*|(t:ℝ)| ≤ (2:ℝ)^n) {C : ℝ} (hC : 1+|(t:ℝ)| ≤ C) :
    |realForm t n L| ≤ C^(2*n)*((2:ℝ)^(n+1)/2^(n*n+triangle n)) := by
  obtain ⟨hs,hpos,hbound⟩ := tailKernel_sum t (by omega : 0<n) htn
  have hC1 : 1 ≤ C := by linarith [abs_nonneg (t:ℝ)]
  have hpow : |(t:ℝ)|^(2*n-1) ≤ C^(2*n) :=
    (pow_le_pow_left₀ (abs_nonneg _) (by linarith : |(t:ℝ)| ≤ C) _).trans
      (pow_le_pow_right₀ hC1 (by omega))
  rw [realForm_tail t ht htp hn hL hU he,abs_mul,abs_pow,abs_of_pos hpos]
  exact mul_le_mul hpow hbound hpos.le (by positivity)

lemma realForm_small (t : ℤ) (ht : t ≠ 0)
    (htp : ∀ h : ℕ, 1 ≤ h → t ≠ -(2:ℤ)^h)
    (B m : ℕ) (hm : 4*(t.natAbs+1)+B+5 ≤ m) {L U : ℤ[X]}
    (hL : L.degree < (4*m-1:ℕ)) (hU : U.natDegree < 4*m)
    (he : numPoly t (4*m) = L * denPoly (4*m) + X^(4*m-1) * U) :
    (B:ℝ)*(commonDen (4*m):ℝ)*|(shiftProd t (4*m):ℝ)| *|realForm t (4*m) L| < 1 := by
  let C : ℕ := t.natAbs+1
  have hmpos : 0 < m := by omega
  have hn : 2 ≤ 4*m := by omega
  have hta : (t.natAbs:ℝ) = |(t:ℝ)| := by simp only [Nat.cast_natAbs,Int.cast_abs]
  have hC : (C:ℝ) = 1+|(t:ℝ)| := by simp [C,hta,add_comm]
  have hC1 : 1 ≤ (C:ℝ) := by rw [hC]; linarith [abs_nonneg (t:ℝ)]
  have htn : 2*|(t:ℝ)| ≤ (2:ℝ)^(4*m) := by
    have hnat : 2*t.natAbs ≤ 4*m := by omega
    have hlo : 2*|(t:ℝ)| ≤ (4*m:ℝ) := by rw [← hta]; exact_mod_cast hnat
    exact hlo.trans (by exact_mod_cast (Nat.lt_two_pow_self (n := 4*m)).le)
  have hD : (commonDen (4*m):ℝ) ≤ (2:ℝ)^(10*m*m) := by
    exact_mod_cast commonDen_bound m hmpos
  have hE := shiftProd_abs_bound t (by omega : 0<4*m) (le_of_eq hC.symm)
  have hF := realForm_abs_bound t ht htp hn hL hU he htn (le_of_eq hC.symm)
  calc
    (B:ℝ)*(commonDen (4*m):ℝ)*|(shiftProd t (4*m):ℝ)| *|realForm t (4*m) L| ≤
        (B:ℝ)*(2:ℝ)^(10*m*m)*((C:ℝ)^(4*m)*2^(triangle (4*m)))*
          ((C:ℝ)^(2*(4*m))*(2^(4*m+1)/2^((4*m)*(4*m)+triangle (4*m)))) := by
      gcongr
    _ = ((B:ℝ)*(C:ℝ)^(12*m)*(2:ℝ)^(10*m*m+4*m+1))/(2:ℝ)^(16*m*m) := by
      have hp : (C:ℝ)^(4*m)*(C:ℝ)^(2*(4*m)) = (C:ℝ)^(12*m) := by
        rw [← pow_add]
        congr 1
        ring
      have hn' : (4*m)*(4*m) = 16*m*m := by ring
      rw [pow_add (2:ℝ) ((4*m)*(4*m)) (triangle (4*m))]
      have hnz : (2:ℝ)^(triangle (4*m)) ≠ 0 := by positivity
      have hbase : (2:ℝ)^(16*m*m) ≠ 0 := by positivity
      rw [hn']
      field_simp
      rw [show (2:ℝ)^(10*m*m+4*m+1) = (2:ℝ)^(10*m*m)*(2:ℝ)^(4*m+1) by
        rw [← pow_add]; congr 1]
      linear_combination (B:ℝ)*(2:ℝ)^(10*m*m)*(2:ℝ)^(4*m+1)*hp
    _ < 1 := (div_lt_one (by positivity)).mpr (explicit_error_bound B C m (by dsimp [C]; omega) hm)

lemma lambert_irrational (t : ℤ) (ht : t ≠ 0)
    (htp : ∀ h : ℕ, 1 ≤ h → t ≠ -(2:ℤ)^h) : Irrational (lambert t) := by
  intro hrat
  obtain ⟨S,hS0⟩ := hrat
  have hS : lambert t = (S:ℝ) := hS0.symm
  let B := S.den
  let m := 4*(t.natAbs+1)+B+5
  have hmpos : 0 < m := by dsimp [m]; omega
  have hn : 2 ≤ 4*m := by omega
  obtain ⟨L,U,hL,hU,he⟩ := integer_remainders t (4*m) hn
  have hBS : (B:ℚ)*S ∈ (Int.castRingHom ℚ).range := by
    refine ⟨S.num,?_⟩
    have hd : (S.den:ℚ) ≠ 0 := by exact_mod_cast S.den_ne_zero
    have hh := (div_eq_iff hd).mp S.num_div_den
    simpa [B,mul_comm] using hh
  obtain ⟨z,hz⟩ := rationalForm_integral t hn L S B hBS
  change (z:ℚ) = (B:ℚ)*(commonDen (4*m):ℚ)*(shiftProd t (4*m):ℚ)*rationalForm t (4*m) L S at hz
  have hreal : (z:ℝ) = (B:ℝ)*(commonDen (4*m):ℝ)*(shiftProd t (4*m):ℝ)*realForm t (4*m) L := by
    have hh := congrArg (fun q : ℚ => (q:ℝ)) hz
    push_cast at hh
    rw [← realForm_of_rational L hS] at hh
    exact hh
  have hta : (t.natAbs:ℝ) = |(t:ℝ)| := by simp only [Nat.cast_natAbs,Int.cast_abs]
  have htn : 2*|(t:ℝ)| ≤ (2:ℝ)^(4*m) := by
    have hnat : 2*t.natAbs ≤ 4*m := by dsimp [m]; omega
    have hlo : 2*|(t:ℝ)| ≤ (4*m:ℝ) := by rw [← hta]; exact_mod_cast hnat
    exact hlo.trans (by exact_mod_cast (Nat.lt_two_pow_self (n := 4*m)).le)
  have hFne : realForm t (4*m) L ≠ 0 := by
    rw [realForm_tail t ht htp hn hL hU he]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast ht))
      (tailKernel_sum t (by omega : 0<4*m) htn).2.1.ne'
  have hEne : shiftProd t (4*m) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro h hh
    have hhi := mem_Icc.mp hh
    exact fun hz => htp h hhi.1 (by omega)
  have hDpos : 0 < commonDen (4*m) := Nat.mul_pos (mersenneProd_pos _) (mersenneProd_pos _)
  have hz' : z ≠ 0 := by
    have hp : (B:ℝ)*(commonDen (4*m):ℝ)*(shiftProd t (4*m):ℝ)*realForm t (4*m) L ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by exact_mod_cast S.den_ne_zero)
        (by exact_mod_cast hDpos.ne')) (by exact_mod_cast hEne)) hFne
    intro hz0
    exact hp (by rw [← hreal,hz0]; simp)
  have hsmall : |(z:ℝ)| < 1 := by
    rw [hreal,abs_mul,abs_mul,abs_mul,abs_of_nonneg (by positivity : (0:ℝ) ≤ B),
      abs_of_nonneg (by exact_mod_cast hDpos.le : (0:ℝ) ≤ commonDen (4*m))]
    exact realForm_small t ht htp B m (by dsimp [m]; omega) hL hU he
  have hlarge : (1:ℝ) ≤ |(z:ℝ)| := by exact_mod_cast (Int.one_le_abs hz')
  linarith

end D7Lambert

theorem OMA.solution : OMA.R_Erdos1050_erdos_1050_variants_transcendental_R1.H1 := by
  intro t ht htp
  exact D7Lambert.lambert_irrational t ht htp
