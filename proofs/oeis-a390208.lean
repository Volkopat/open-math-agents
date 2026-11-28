import OMAStatements.S_oeis_a390208
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace A390208Proof

open Finset PowerSeries
open scoped BigOperators

abbrev Series := PowerSeries ℂ

abbrev Multiplicities (n : ℕ) := Fin n → Fin 3 → Fin (n + 1)

def size {n : ℕ} (m : Multiplicities n) : ℕ :=
  ∑ j : Fin n, ∑ c : Fin 3, (j.val + 1) * (m j c).val

def colour {n : ℕ} (m : Multiplicities n) : ℕ :=
  ∑ j : Fin n, ∑ c : Fin 3, c.val * (m j c).val

noncomputable def base (q : ℂ) (j : ℕ) (c : Fin 3) : Series :=
  C (q ^ c.val) * X ^ (j + 1)

noncomputable def weighted (n : ℕ) (q : ℂ) : Series :=
  ∏ j : Fin n, ∏ c : Fin 3, ∑ k : Fin (n + 1), base q j.val c ^ k.val

lemma coeff_weighted (n : ℕ) (q : ℂ) :
    coeff n (weighted n q) =
      ∑ m : Multiplicities n, if size m = n then q ^ colour m else 0 := by
  unfold weighted
  simp_rw [Fintype.prod_sum]
  rw [map_sum]
  apply sum_congr rfl
  intro m _
  simp only [base, mul_pow, ← map_pow C, ← pow_mul, prod_mul_distrib, ← map_prod C,
    prod_pow_eq_pow_sum, coeff_C_mul, coeff_X_pow]
  change q ^ colour m * (if n = size m then 1 else 0) = _
  by_cases h : size m = n
  · rw [if_pos h.symm, if_pos h, mul_one]
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero]

lemma trunc_prod_congr {ι : Type} (s : Finset ι) (k : ℕ) (f g : ι → Series)
    (h : ∀ i ∈ s, trunc k (f i) = trunc k (g i)) :
    trunc k (∏ i ∈ s, f i) = trunc k (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have htail := ih (fun j hj => h j (mem_insert_of_mem hj))
    rw [prod_insert hi, prod_insert hi, ← trunc_trunc_mul_trunc, h i (mem_insert_self i s),
      htail, trunc_trunc_mul_trunc]

lemma trunc_geometric (n j : ℕ) (q : ℂ) (c : Fin 3) :
    trunc (n + 1) (∑ k : Fin (n + 1), base q j c ^ k.val) =
      trunc (n + 1) ((1 - base q j c)⁻¹) := by
  let y := base q j c
  change trunc (n + 1) (∑ k : Fin (n + 1), y ^ k.val) =
    trunc (n + 1) ((1 - y)⁻¹)
  have hy : constantCoeff (1 - y) ≠ 0 := by
    simp [y, base, map_pow, zero_pow (Nat.succ_ne_zero j)]
  have hgeom :
      (∑ k : Fin (n + 1), y ^ k.val) = (1 - y ^ (n + 1)) * (1 - y)⁻¹ := by
    rw [Fin.sum_univ_eq_sum_range, eq_mul_inv_iff_mul_eq hy]
    exact geom_sum_mul_neg y (n + 1)
  have hp : y ^ (n + 1) = (X : Series) ^ (n + 1) *
      (C (q ^ c.val) ^ (n + 1) * X ^ (j * (n + 1))) := by
    change (C (q ^ c.val) * X ^ (j + 1) : Series) ^ (n + 1) = _
    rw [mul_pow, ← pow_mul (X : Series),
      show (j + 1) * (n + 1) = (n + 1) + j * (n + 1) by ring, pow_add]
    ring
  have hhigh : trunc (n + 1) (y ^ (n + 1) * (1 - y)⁻¹) = 0 := by
    rw [hp, mul_assoc, trunc_X_pow_self_mul]
  rw [hgeom, sub_mul, one_mul, map_sub, hhigh, sub_zero]

lemma coeff_geometric (n : ℕ) (q : ℂ) :
    coeff n (weighted n q) =
      coeff n (∏ j : Fin n, ∏ c : Fin 3, (1 - base q j.val c)⁻¹) := by
  have h : trunc (n + 1) (weighted n q) =
      trunc (n + 1) (∏ j : Fin n, ∏ c : Fin 3, (1 - base q j.val c)⁻¹) := by
    unfold weighted
    apply trunc_prod_congr
    intro j _
    apply trunc_prod_congr
    intro c _
    exact trunc_geometric n j.val q c
  simpa only [coeff_trunc, if_pos (Nat.lt_succ_self n)] using
    congrArg (fun p : Polynomial ℂ => p.coeff n) h

lemma unsigned_factor (j : ℕ) :
    (∏ c : Fin 3, (1 - base 1 j c)⁻¹) = ((1 - (X : Series) ^ (j + 1))⁻¹) ^ 3 := by
  simp [base]

lemma periodic (q : ℂ) (hq : q ^ 3 = 1) (c : ℕ) : q ^ c = q ^ (c % 3) := by
  conv_lhs => rw [← Nat.mod_add_div c 3]
  rw [pow_add, pow_mul, hq, one_pow, mul_one]

lemma cube_sq (q : ℂ) (hq : q ^ 3 = 1) (hs : 1 + q + q ^ 2 = 0) :
    (q ^ 2) ^ 3 = 1 ∧ 1 + q ^ 2 + (q ^ 2) ^ 2 = 0 := by
  constructor
  · rw [← pow_mul, show 2 * 3 = 3 * 2 by decide, pow_mul, hq, one_pow]
  · rw [← pow_mul, show 2 * 2 = 3 + 1 by decide, pow_add, hq, one_mul, pow_one]
    calc
      1 + q ^ 2 + q = 1 + q + q ^ 2 := by ring
      _ = 0 := hs

lemma cube_factor (j : ℕ) (q : ℂ) (hq : q ^ 3 = 1) (hs : 1 + q + q ^ 2 = 0) :
    (∏ c : Fin 3, (1 - base q j c)⁻¹) =
      (1 - (X : Series) ^ (3 * (j + 1)))⁻¹ := by
  let y := (X : Series) ^ (j + 1)
  let u : Series := C q
  have hu3 : u ^ 3 = 1 := by rw [show u = C q from rfl, ← map_pow, hq, map_one]
  have hus : 1 + u + u ^ 2 = 0 := by
    change 1 + C q + (C q) ^ 2 = 0
    rw [← map_pow, ← map_one C, ← map_add, ← map_add, hs, map_zero]
  have hpoly : (1 - y) * (1 - u * y) * (1 - u ^ 2 * y) = 1 - y ^ 3 := by
    calc
      _ = 1 - (1 + u + u ^ 2) * y + u * (1 + u + u ^ 2) * y ^ 2 - u ^ 3 * y ^ 3 := by ring
      _ = _ := by rw [hus, hu3]; ring
  rw [Fin.prod_univ_three]
  have hf (c : Fin 3) : base q j c = u ^ c.val * y := by simp [base, u, y, map_pow]
  simp only [hf]
  norm_num [show (0 : Fin 3).val = 0 by decide, show (1 : Fin 3).val = 1 by decide,
    show (2 : Fin 3).val = 2 by decide]
  rw [← PowerSeries.mul_inv_rev, ← PowerSeries.mul_inv_rev]
  congr 1
  rw [show (1 - u ^ 2 * y) * ((1 - u * y) * (1 - y)) =
    (1 - y) * (1 - u * y) * (1 - u ^ 2 * y) by ring, hpoly]
  dsimp [y]
  rw [← pow_mul, Nat.mul_comm (j + 1) 3]

lemma cube_filter (q : ℂ) (hq : q ^ 3 = 1) (hs : 1 + q + q ^ 2 = 0) (c : ℕ) :
    1 + q ^ 2 * q ^ c + q * (q ^ 2) ^ c = if c % 3 = 1 then 3 else 0 := by
  have h2 := cube_sq q hq hs
  rw [periodic q hq c, periodic (q ^ 2) h2.1 c]
  have hlt : c % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases c % 3
  · simpa [add_comm q (q ^ 2), add_assoc] using hs
  · norm_num
    rw [show q ^ 2 * q = q ^ 3 by ring, show q * q ^ 2 = q ^ 3 by ring, hq]
    norm_num
  · rw [show q ^ 2 * q ^ 2 = q ^ 3 * q by ring,
      show q * (q ^ 2) ^ 2 = q ^ 3 * q ^ 2 by ring, hq]
    simpa using hs

lemma coefficient_count (n : ℕ) (q : ℂ) (hq : q ^ 3 = 1) (hs : 1 + q + q ^ 2 = 0) :
    coeff n (weighted n 1) + q ^ 2 * coeff n (weighted n q) +
      q * coeff n (weighted n (q ^ 2)) = 3 * (OMA.S_oeis_a390208.a n : ℂ) := by
  rw [coeff_weighted, coeff_weighted, coeff_weighted, mul_sum, mul_sum,
    ← sum_add_distrib, ← sum_add_distrib]
  unfold OMA.S_oeis_a390208.a
  rw [Finset.natCast_card_filter, mul_sum]
  apply sum_congr rfl
  intro m _
  change (if size m = n then (1 : ℂ) ^ colour m else 0) +
    q ^ 2 * (if size m = n then q ^ colour m else 0) +
    q * (if size m = n then (q ^ 2) ^ colour m else 0) =
      3 * (if size m = n ∧ colour m % 3 = 1 then 1 else 0)
  by_cases hm : size m = n
  · simp only [hm, if_true, one_pow, true_and, cube_filter q hq hs]
    split <;> ring
  · simp [hm]

noncomputable def embed : Polynomial ℤ →+* Series := (Polynomial.coeToPowerSeries.algHom ℂ).toRingHom

lemma embed_X : embed Polynomial.X = (X : Series) := by
  simp [embed, Polynomial.coeToPowerSeries.algHom_apply]

lemma coeff_embed (n : ℕ) (f : Polynomial ℤ) : coeff n (embed f) = (f.coeff n : ℂ) := by
  simp [embed, Polynomial.coeToPowerSeries.algHom_apply, coeff_map]

lemma trunc_embed_geom (n d : ℕ) (hd : 0 < d) :
    trunc (n + 1) (embed (OMA.S_oeis_a390208.geometric n d)) =
      trunc (n + 1) ((1 - (X : Series) ^ d)⁻¹) := by
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
  have h := trunc_geometric n j 1 0
  rw [Fin.sum_univ_eq_sum_range] at h
  simpa [OMA.S_oeis_a390208.geometric, base, embed_X, ← pow_mul] using h

lemma trunc_pow_congr (n k : ℕ) (f g : Series) (h : trunc n f = trunc n g) :
    trunc n (f ^ k) = trunc n (g ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, ← trunc_trunc_mul_trunc (n := n) (f ^ k) f,
      ← trunc_trunc_mul_trunc (n := n) (g ^ k) g, ih, h]

lemma coeff_geom_power (n m k : ℕ) (hm : 0 < m) :
    ((∏ j ∈ Finset.range n, OMA.S_oeis_a390208.geometric n (m * (j + 1)) ^ k).coeff n : ℂ) =
      coeff n (∏ j ∈ Finset.range n, ((1 - (X : Series) ^ (m * (j + 1)))⁻¹) ^ k) := by
  rw [← coeff_embed, map_prod]
  have h : trunc (n + 1) (∏ j ∈ Finset.range n,
      embed (OMA.S_oeis_a390208.geometric n (m * (j + 1)) ^ k)) =
      trunc (n + 1) (∏ j ∈ Finset.range n, ((1 - (X : Series) ^ (m * (j + 1)))⁻¹) ^ k) := by
    apply trunc_prod_congr
    intro j _
    rw [map_pow]
    exact trunc_pow_congr _ _ _ _ (trunc_embed_geom _ _ (Nat.mul_pos hm (by omega)))
  simpa only [coeff_trunc, if_pos (Nat.lt_succ_self n)] using
    congrArg (fun p : Polynomial ℂ => p.coeff n) h

end A390208Proof

open A390208Proof PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a390208.main := by
  intro n
  obtain ⟨q, hq⟩ : ∃ q : ℂ, IsPrimitiveRoot q 3 :=
    ⟨_, Complex.isPrimitiveRoot_exp 3 (by decide)⟩
  have h3 : q ^ 3 = 1 := hq.pow_eq_one
  have hs : 1 + q + q ^ 2 = 0 := by
    simpa [Finset.sum_range_succ] using hq.geom_sum_eq_zero (by decide : 1 < 3)
  have h2 := cube_sq q h3 hs
  have h := coefficient_count n q h3 hs
  rw [coeff_geometric, coeff_geometric, coeff_geometric] at h
  simp_rw [unsigned_factor, cube_factor _ q h3 hs, cube_factor _ (q ^ 2) h2.1 h2.2] at h
  rw [Fin.prod_univ_eq_prod_range (fun j => ((1 - (X : Series) ^ (j + 1))⁻¹) ^ 3) n,
    Fin.prod_univ_eq_prod_range (fun j => (1 - (X : Series) ^ (3 * (j + 1)))⁻¹) n] at h
  have hG1 := coeff_geom_power n 1 3 (by decide)
  have hG3 := coeff_geom_power n 3 1 (by decide)
  simp only [one_mul] at hG1
  simp only [pow_one] at hG3
  rw [← hG1, ← hG3] at h
  apply (Int.cast_injective (α := ℂ))
  push_cast
  linear_combination -h + hs * ((∏ j ∈ Finset.range n,
    OMA.S_oeis_a390208.geometric n (3 * (j + 1))).coeff n : ℂ)
