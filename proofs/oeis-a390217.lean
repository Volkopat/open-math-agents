import OMAStatements.S_oeis_a390217
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

namespace A390217Proof

open Finset PowerSeries
open scoped BigOperators

abbrev Series := PowerSeries ℂ

abbrev Multiplicities (n : ℕ) := Fin n → Fin 4 → Fin (n + 1)

def size {n : ℕ} (m : Multiplicities n) : ℕ :=
  ∑ j : Fin n, ∑ c : Fin 4, (j.val + 1) * (m j c).val

def colour {n : ℕ} (m : Multiplicities n) : ℕ :=
  ∑ j : Fin n, ∑ c : Fin 4, c.val * (m j c).val

noncomputable def base (q : ℂ) (j : ℕ) (c : Fin 4) : Series :=
  C (q ^ c.val) * X ^ (j + 1)

noncomputable def weighted (n : ℕ) (q : ℂ) : Series :=
  ∏ j : Fin n, ∏ c : Fin 4, ∑ k : Fin (n + 1), base q j.val c ^ k.val

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

lemma trunc_geometric (n j : ℕ) (q : ℂ) (c : Fin 4) :
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
      coeff n (∏ j : Fin n, ∏ c : Fin 4, (1 - base q j.val c)⁻¹) := by
  have h : trunc (n + 1) (weighted n q) =
      trunc (n + 1) (∏ j : Fin n, ∏ c : Fin 4, (1 - base q j.val c)⁻¹) := by
    unfold weighted
    apply trunc_prod_congr
    intro j _
    apply trunc_prod_congr
    intro c _
    exact trunc_geometric n j.val q c
  simpa only [coeff_trunc, if_pos (Nat.lt_succ_self n)] using
    congrArg (fun p : Polynomial ℂ => p.coeff n) h

lemma unsigned_factor (j : ℕ) :
    (∏ c : Fin 4, (1 - base 1 j c)⁻¹) = ((1 - (X : Series) ^ (j + 1))⁻¹) ^ 4 := by
  simp [base]

lemma signed_factor (j : ℕ) :
    (∏ c : Fin 4, (1 - base (-1) j c)⁻¹) =
      ((1 - (X : Series) ^ (2 * (j + 1)))⁻¹) ^ 2 := by
  let y := (X : Series) ^ (j + 1)
  have h : (1 - y)⁻¹ * (1 + y)⁻¹ = (1 - y ^ 2)⁻¹ := by
    rw [← PowerSeries.mul_inv_rev, show (1 + y) * (1 - y) = 1 - y ^ 2 by ring]
  have hy2 : y ^ 2 = (X : Series) ^ (2 * (j + 1)) := by
    dsimp [y]
    rw [← pow_mul, Nat.mul_comm (j + 1) 2]
  rw [Fin.prod_univ_four]
  have hf (c : Fin 4) : base (-1) j c = C ((-1 : ℂ) ^ c.val) * y := rfl
  simp only [hf]
  norm_num [show (0 : Fin 4).val = 0 by decide, show (1 : Fin 4).val = 1 by decide,
    show (2 : Fin 4).val = 2 by decide, show (3 : Fin 4).val = 3 by decide, map_neg,
    map_one, one_mul, neg_mul]
  calc
    _ = ((1 - y)⁻¹ * (1 + y)⁻¹) ^ 2 := by ring
    _ = _ := by rw [h, hy2]

lemma fourth (q : ℂ) (hq : q ^ 2 = -1) : q ^ 4 = 1 := by
  rw [show 4 = 2 * 2 by decide, pow_mul, hq]
  norm_num

lemma periodic (q : ℂ) (hq : q ^ 4 = 1) (c : ℕ) : q ^ c = q ^ (c % 4) := by
  conv_lhs => rw [← Nat.mod_add_div c 4]
  rw [pow_add, pow_mul, hq, one_pow, mul_one]

lemma fourth_filter (c : ℕ) :
    1 + Complex.I ^ c + (-1 : ℂ) ^ c + (-Complex.I) ^ c = if c % 4 = 0 then 4 else 0 := by
  have hi := fourth Complex.I Complex.I_sq
  have hni := fourth (-Complex.I) (by simp [Complex.I_sq])
  rw [periodic Complex.I hi, periodic (-1 : ℂ) (by norm_num), periodic (-Complex.I) hni]
  have hlt : c % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases c % 4 <;> norm_num [pow_succ, Complex.I_mul_I]

lemma coefficient_count (n : ℕ) :
    coeff n (weighted n 1) + coeff n (weighted n Complex.I) +
      coeff n (weighted n (-1)) + coeff n (weighted n (-Complex.I)) =
      4 * (OMA.S_oeis_a390217.a n : ℂ) := by
  rw [coeff_weighted, coeff_weighted, coeff_weighted, coeff_weighted]
  simp only [← sum_add_distrib]
  unfold OMA.S_oeis_a390217.a
  rw [Finset.natCast_card_filter, mul_sum]
  apply sum_congr rfl
  intro m _
  change (if size m = n then (1 : ℂ) ^ colour m else 0) +
    (if size m = n then Complex.I ^ colour m else 0) +
    (if size m = n then (-1 : ℂ) ^ colour m else 0) +
    (if size m = n then (-Complex.I) ^ colour m else 0) =
      4 * (if size m = n ∧ colour m % 4 = 0 then 1 else 0)
  by_cases hm : size m = n
  · simp only [hm, if_true, one_pow, true_and, fourth_filter]
    split <;> ring
  · simp [hm]

lemma fourth_factor (j : ℕ) (q : ℂ) (hq : q ^ 2 = -1) :
    (∏ c : Fin 4, (1 - base q j c)⁻¹) =
      (1 - (X : Series) ^ (4 * (j + 1)))⁻¹ := by
  let y := (X : Series) ^ (j + 1)
  let u : Series := C q
  have hu2 : u ^ 2 = -1 := by
    rw [show u = C q from rfl, ← map_pow, hq, map_neg, map_one]
  have hu3 : u ^ 3 = -u := by rw [pow_succ, hu2, neg_one_mul]
  have hpoly : (1 - y) * (1 - u * y) * (1 + y) * (1 + u * y) = 1 - y ^ 4 := by
    calc
      _ = (1 - y ^ 2) * (1 - u ^ 2 * y ^ 2) := by ring
      _ = _ := by rw [hu2]; ring
  rw [Fin.prod_univ_four]
  have hf (c : Fin 4) : base q j c = u ^ c.val * y := by simp [base, u, y, map_pow]
  simp only [hf]
  norm_num [show (0 : Fin 4).val = 0 by decide, show (1 : Fin 4).val = 1 by decide,
    show (2 : Fin 4).val = 2 by decide, show (3 : Fin 4).val = 3 by decide,
    hu2, hu3, neg_mul, neg_one_mul]
  rw [← PowerSeries.mul_inv_rev, ← PowerSeries.mul_inv_rev, ← PowerSeries.mul_inv_rev]
  congr 1
  rw [show (1 + u * y) * ((1 + y) * ((1 - u * y) * (1 - y))) =
    (1 - y) * (1 - u * y) * (1 + y) * (1 + u * y) by ring, hpoly]
  dsimp [y]
  rw [← pow_mul, Nat.mul_comm (j + 1) 4]

end A390217Proof

open A390217Proof PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a390217.main := by
  intro n
  have h := coefficient_count n
  rw [coeff_geometric, coeff_geometric, coeff_geometric, coeff_geometric] at h
  simp_rw [unsigned_factor, signed_factor, fourth_factor _ Complex.I Complex.I_sq,
    fourth_factor _ (-Complex.I) (by simp [Complex.I_sq])] at h
  rw [Fin.prod_univ_eq_prod_range (fun j => ((1 - (X : Series) ^ (j + 1))⁻¹) ^ 4) n,
    Fin.prod_univ_eq_prod_range (fun j => ((1 - (X : Series) ^ (2 * (j + 1)))⁻¹) ^ 2) n,
    Fin.prod_univ_eq_prod_range (fun j => (1 - (X : Series) ^ (4 * (j + 1)))⁻¹) n] at h
  rw [map_add, map_add, show (2 : Series) = C (2 : ℂ) from (map_ofNat C 2).symm, coeff_C_mul]
  linear_combination -h / 4
