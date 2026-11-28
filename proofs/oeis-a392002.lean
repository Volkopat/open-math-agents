import OMAStatements.S_oeis_a392002
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace A392002Proof

open Finset PowerSeries
open scoped BigOperators

abbrev Multiplicities (n : ℕ) := Fin n → Fin 2 → Fin (n + 1)

def size {n : ℕ} (m : Multiplicities n) : ℕ :=
  ∑ j : Fin n, ∑ c : Fin 2, (j.val + 1) * (m j c).val

def colour {n : ℕ} (m : Multiplicities n) : ℕ :=
  ∑ j : Fin n, ∑ c : Fin 2, c.val * (m j c).val

def count (n r : ℕ) : ℚ :=
  ∑ m : Multiplicities n, if size m = n ∧ colour m % 2 = r then 1 else 0

lemma count_one (n : ℕ) : count n 1 = (OMA.S_oeis_a392002.a n : ℚ) := by
  unfold count
  rw [← sum_filter]
  simp [size, colour, OMA.S_oeis_a392002.a]

lemma parity_weight (c : ℕ) :
    (1 : ℚ) - (-1 : ℚ) ^ c =
      2 * (if c % 2 = 1 then 1 else 0) := by
  have h : (-1 : ℚ) ^ c = (-1 : ℚ) ^ (c % 2) := by
    conv_lhs => rw [← Nat.mod_add_div c 2]
    rw [pow_add, pow_mul]
    norm_num
  rw [h]
  have hbound : c % 2 < 2 := Nat.mod_lt c (by decide)
  interval_cases hmod : c % 2 <;> norm_num [hmod]

abbrev Series := PowerSeries ℚ

noncomputable def base (q : ℚ) (j : ℕ) (c : Fin 2) : Series :=
  C (q ^ c.val) * X ^ (j + 1)

noncomputable def weighted (n : ℕ) (q : ℚ) : Series :=
  ∏ j : Fin n, ∏ c : Fin 2, ∑ k : Fin (n + 1), base q j.val c ^ k.val

lemma coeff_weighted (n : ℕ) (q : ℚ) :
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

lemma coefficient_count (n : ℕ) :
    coeff n (weighted n 1) - coeff n (weighted n (-1)) =
      2 * (OMA.S_oeis_a392002.a n : ℚ) := by
  rw [coeff_weighted, coeff_weighted, ← sum_sub_distrib, ← count_one]
  unfold count
  rw [mul_sum]
  apply sum_congr rfl
  intro m _
  by_cases h : size m = n
  · simp only [h, if_true, one_pow, true_and]
    exact parity_weight (colour m)
  · simp [h]

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

lemma trunc_geometric (n j : ℕ) (q : ℚ) (c : Fin 2) :
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

lemma coeff_geometric (n : ℕ) (q : ℚ) :
    coeff n (weighted n q) =
      coeff n (∏ j : Fin n, ∏ c : Fin 2, (1 - base q j.val c)⁻¹) := by
  have h : trunc (n + 1) (weighted n q) =
      trunc (n + 1) (∏ j : Fin n, ∏ c : Fin 2, (1 - base q j.val c)⁻¹) := by
    unfold weighted
    apply trunc_prod_congr
    intro j _
    apply trunc_prod_congr
    intro c _
    exact trunc_geometric n j.val q c
  simpa only [coeff_trunc, if_pos (Nat.lt_succ_self n)] using
    congrArg (fun p : Polynomial ℚ => p.coeff n) h

lemma unsigned_factor (j : ℕ) :
    (∏ c : Fin 2, (1 - base 1 j c)⁻¹) = ((1 - (X : Series) ^ (j + 1))⁻¹) ^ 2 := by
  simp [base]

lemma signed_factor (j : ℕ) :
    (∏ c : Fin 2, (1 - base (-1) j c)⁻¹) =
      (1 - (X : Series) ^ (2 * (j + 1)))⁻¹ := by
  let y := (X : Series) ^ (j + 1)
  have h : (1 - y)⁻¹ * (1 + y)⁻¹ = (1 - y ^ 2)⁻¹ := by
    rw [← PowerSeries.mul_inv_rev, show (1 + y) * (1 - y) = 1 - y ^ 2 by ring]
  have hy2 : y ^ 2 = (X : Series) ^ (2 * (j + 1)) := by
    dsimp [y]
    rw [← pow_mul, Nat.mul_comm (j + 1) 2]
  rw [Fin.prod_univ_two]
  have hf (c : Fin 2) : base (-1) j c = C ((-1 : ℚ) ^ c.val) * y := rfl
  simp only [hf]
  norm_num [show (0 : Fin 2).val = 0 by decide, show (1 : Fin 2).val = 1 by decide,
    map_neg, map_one, one_mul, neg_mul]
  rw [h, hy2]

end A392002Proof

open A392002Proof PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a392002.main := by
  intro n
  have h := coefficient_count n
  rw [coeff_geometric, coeff_geometric] at h
  simp_rw [unsigned_factor, signed_factor] at h
  rw [Fin.prod_univ_eq_prod_range (fun j => ((1 - (X : Series) ^ (j + 1))⁻¹) ^ 2) n,
    Fin.prod_univ_eq_prod_range (fun j => (1 - (X : Series) ^ (2 * (j + 1)))⁻¹) n] at h
  rw [map_sub]
  linarith
