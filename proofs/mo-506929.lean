import OMAStatements.S_mo_506929
import Mathlib

namespace OMA.S_mo_506929_Proof

open Polynomial Finset

private def fwdDiff (k : ℕ) (f : ℕ → ℚ) : ℚ :=
  ∑ j ∈ range (k + 1), (-1 : ℚ) ^ j * (k.choose j : ℚ) * f j

private lemma fwdDiff_sub (k : ℕ) (f g : ℕ → ℚ) :
    fwdDiff k (fun j => f j - g j) = fwdDiff k f - fwdDiff k g := by
  simp only [fwdDiff, mul_sub, Finset.sum_sub_distrib]

private lemma fwdDiff_const_mul (k : ℕ) (c : ℚ) (f : ℕ → ℚ) :
    fwdDiff k (fun j => c * f j) = c * fwdDiff k f := by
  simp only [fwdDiff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

private lemma fwdDiff_sum {ι : Type*} (s : Finset ι) (k : ℕ) (f : ι → ℕ → ℚ) :
    fwdDiff k (fun j => ∑ i ∈ s, f i j) = ∑ i ∈ s, fwdDiff k (f i) := by
  simp only [fwdDiff, Finset.mul_sum]
  exact Finset.sum_comm

private lemma fwdDiff_succ (k : ℕ) (f : ℕ → ℚ) :
    fwdDiff (k + 1) f = fwdDiff k f - fwdDiff k (fun j => f (j + 1)) := by
  unfold fwdDiff
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one]
  have hsplit :
      ∑ j ∈ range (k + 1), (-1 : ℚ) ^ (j + 1) * ((k + 1).choose (j + 1) : ℚ) * f (j + 1) =
        (∑ j ∈ range (k + 1), (-1 : ℚ) ^ (j + 1) * (k.choose j : ℚ) * f (j + 1)) +
        (∑ j ∈ range (k + 1), (-1 : ℚ) ^ (j + 1) * (k.choose (j + 1) : ℚ) * f (j + 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.choose_succ_succ, Nat.cast_add]
    ring
  rw [hsplit]
  have h1 :
      ∑ j ∈ range (k + 1), (-1 : ℚ) ^ (j + 1) * (k.choose j : ℚ) * f (j + 1) =
        -(∑ j ∈ range (k + 1), (-1 : ℚ) ^ j * (k.choose j : ℚ) * f (j + 1)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ]
    ring
  have h2 :
      (∑ j ∈ range (k + 1), (-1 : ℚ) ^ (j + 1) * (k.choose (j + 1) : ℚ) * f (j + 1)) + f 0 =
        ∑ j ∈ range (k + 1), (-1 : ℚ) ^ j * (k.choose j : ℚ) * f j := by
    rw [Finset.sum_range_succ (f := fun j => (-1 : ℚ) ^ (j + 1) * (k.choose (j + 1) : ℚ) * f (j + 1))]
    rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self k)]
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
    rw [Finset.sum_range_succ' (f := fun j => (-1 : ℚ) ^ j * (k.choose j : ℚ) * f j)]
    simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one]
  linarith

private lemma fwdDiff_pow_eq_zero : ∀ k d : ℕ, d < k →
    fwdDiff k (fun j => (j : ℚ) ^ d) = 0 := by
  intro k
  induction k with
  | zero => intro d hd; omega
  | succ k ih =>
    intro d hd
    rw [fwdDiff_succ, ← fwdDiff_sub]
    have hfun : (fun j : ℕ => (j : ℚ) ^ d - ((j + 1 : ℕ) : ℚ) ^ d) =
        (fun j : ℕ => ∑ i ∈ range d, -((d.choose i : ℚ) * (j : ℚ) ^ i)) := by
      funext j
      have hpow : ((j + 1 : ℕ) : ℚ) ^ d =
          ∑ i ∈ range (d + 1), (j : ℚ) ^ i * 1 ^ (d - i) * (d.choose i : ℚ) := by
        rw [Nat.cast_add, Nat.cast_one, add_pow]
      rw [hpow, Finset.sum_range_succ]
      simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one]
      rw [Finset.sum_neg_distrib]
      have hcomm : ∑ i ∈ range d, (j : ℚ) ^ i * (d.choose i : ℚ) =
          ∑ i ∈ range d, (d.choose i : ℚ) * (j : ℚ) ^ i :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      linarith
    rw [hfun, fwdDiff_sum]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hid : i < d := Finset.mem_range.mp hi
    have hneg : (fun j : ℕ => -((d.choose i : ℚ) * (j : ℚ) ^ i)) =
        (fun j : ℕ => (-(d.choose i : ℚ)) * (j : ℚ) ^ i) := by
      funext j; ring
    rw [hneg, fwdDiff_const_mul, ih i (by omega), mul_zero]

private def W (m : ℕ) : ℚ :=
  ∑ k ∈ range (m + 1), (k + 1 : ℚ)⁻¹ * fwdDiff k (fun j => (j : ℚ) ^ m)

private lemma W_eq_sum_of_le {m M : ℕ} (h : m ≤ M) :
    W m = ∑ k ∈ range (M + 1), (k + 1 : ℚ)⁻¹ * fwdDiff k (fun j => (j : ℚ) ^ m) := by
  unfold W
  refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ h)) ?_
  intro k _ hk
  have hmk : m < k := by
    simp only [Finset.mem_range] at hk
    omega
  rw [fwdDiff_pow_eq_zero k m hmk, mul_zero]

private lemma W_zero : W 0 = 1 := by
  simp [W, fwdDiff]

private lemma sum_choose_range (n u : ℕ) :
    ∑ k ∈ range (n + 1), k.choose u = (n + 1).choose (u + 1) := by
  induction n with
  | zero =>
    cases u with
    | zero => simp
    | succ u => simp [Nat.choose_eq_zero_of_lt (by omega : 1 < u + 2)]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, add_comm, ← Nat.choose_succ_succ]

private lemma sum_W_eq_zero {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ range (n + 1), ((n + 1).choose i : ℚ) * W i = 0 := by
  have hrewrite :
      ∑ i ∈ range (n + 1), ((n + 1).choose i : ℚ) * W i =
        ∑ k ∈ range (n + 1), (k + 1 : ℚ)⁻¹ *
          fwdDiff k (fun j => ∑ i ∈ range (n + 1), ((n + 1).choose i : ℚ) * (j : ℚ) ^ i) := by
    have h1 : ∑ i ∈ range (n + 1), ((n + 1).choose i : ℚ) * W i =
        ∑ i ∈ range (n + 1), ∑ k ∈ range (n + 1),
          (k + 1 : ℚ)⁻¹ * (((n + 1).choose i : ℚ) * fwdDiff k (fun j => (j : ℚ) ^ i)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [W_eq_sum_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hi)), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.mul_sum, fwdDiff_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fwdDiff_const_mul]
  rw [hrewrite]
  have hbinom : ∀ j : ℕ,
      ∑ i ∈ range (n + 1), ((n + 1).choose i : ℚ) * (j : ℚ) ^ i =
        ((j + 1 : ℕ) : ℚ) ^ (n + 1) - (j : ℚ) ^ (n + 1) := by
    intro j
    have hpow : ((j + 1 : ℕ) : ℚ) ^ (n + 1) =
        ∑ i ∈ range (n + 2), (j : ℚ) ^ i * 1 ^ (n + 1 - i) * ((n + 1).choose i : ℚ) := by
      rw [Nat.cast_add, Nat.cast_one, add_pow]
    rw [Finset.sum_range_succ] at hpow
    simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one] at hpow
    have hcomm : ∑ i ∈ range (n + 1), (j : ℚ) ^ i * ((n + 1).choose i : ℚ) =
        ∑ i ∈ range (n + 1), ((n + 1).choose i : ℚ) * (j : ℚ) ^ i :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    linarith
  have hstep1 :
      ∑ k ∈ range (n + 1), (k + 1 : ℚ)⁻¹ *
          fwdDiff k (fun j => ∑ i ∈ range (n + 1), ((n + 1).choose i : ℚ) * (j : ℚ) ^ i) =
        -(∑ k ∈ range (n + 1), (k + 1 : ℚ)⁻¹ * fwdDiff (k + 1) (fun j => (j : ℚ) ^ (n + 1))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hfn : (fun j : ℕ => ∑ i ∈ range (n + 1), ((n + 1).choose i : ℚ) * (j : ℚ) ^ i) =
        (fun j : ℕ => ((j + 1 : ℕ) : ℚ) ^ (n + 1) - (j : ℚ) ^ (n + 1)) := funext hbinom
    rw [hfn, fwdDiff_sub, fwdDiff_succ]
    ring
  rw [hstep1, neg_eq_zero]
  have hstep2 :
      ∀ k ∈ range (n + 1),
        (k + 1 : ℚ)⁻¹ * fwdDiff (k + 1) (fun j => (j : ℚ) ^ (n + 1)) =
          ∑ u ∈ range (n + 1), (-1 : ℚ) ^ (u + 1) * (k.choose u : ℚ) * ((u + 1 : ℕ) : ℚ) ^ n := by
    intro k hk
    unfold fwdDiff
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_pow (Nat.succ_ne_zero n), mul_zero, add_zero]
    rw [Finset.mul_sum]
    have hsub :
        ∑ u ∈ range (k + 1), (k + 1 : ℚ)⁻¹ *
            ((-1 : ℚ) ^ (u + 1) * ((k + 1).choose (u + 1) : ℚ) * ((u + 1 : ℕ) : ℚ) ^ (n + 1)) =
          ∑ u ∈ range (k + 1), (-1 : ℚ) ^ (u + 1) * (k.choose u : ℚ) * ((u + 1 : ℕ) : ℚ) ^ n := by
      refine Finset.sum_congr rfl fun u _ => ?_
      have habs : ((k + 1).choose (u + 1) : ℚ) * ((u + 1 : ℕ) : ℚ) =
          (k + 1 : ℚ) * (k.choose u : ℚ) := by
        have hnat : (k + 1).choose (u + 1) * (u + 1) = (k + 1) * k.choose u :=
          (Nat.add_one_mul_choose_eq k u).symm
        have hq : (((k + 1).choose (u + 1) * (u + 1) : ℕ) : ℚ) =
            (((k + 1) * k.choose u : ℕ) : ℚ) := by exact_mod_cast hnat
        simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hq
      have hkpos : (k + 1 : ℚ) ≠ 0 := by positivity
      calc (k + 1 : ℚ)⁻¹ *
            ((-1 : ℚ) ^ (u + 1) * ((k + 1).choose (u + 1) : ℚ) * ((u + 1 : ℕ) : ℚ) ^ (n + 1))
          = (k + 1 : ℚ)⁻¹ * (-1 : ℚ) ^ (u + 1) *
              (((k + 1).choose (u + 1) : ℚ) * ((u + 1 : ℕ) : ℚ)) * ((u + 1 : ℕ) : ℚ) ^ n := by
            rw [pow_succ]; ring
        _ = (k + 1 : ℚ)⁻¹ * (-1 : ℚ) ^ (u + 1) *
              ((k + 1 : ℚ) * (k.choose u : ℚ)) * ((u + 1 : ℕ) : ℚ) ^ n := by
            rw [habs]
        _ = (-1 : ℚ) ^ (u + 1) * (k.choose u : ℚ) * ((u + 1 : ℕ) : ℚ) ^ n := by
            field_simp [hkpos]
    rw [hsub]
    refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))) ?_
    intro u _ hu
    have hku : k < u := by
      simp only [Finset.mem_range] at hu
      omega
    rw [Nat.choose_eq_zero_of_lt hku]
    simp
  rw [Finset.sum_congr rfl hstep2, Finset.sum_comm]
  have hstep3 :
      ∑ u ∈ range (n + 1), ∑ k ∈ range (n + 1),
          (-1 : ℚ) ^ (u + 1) * (k.choose u : ℚ) * ((u + 1 : ℕ) : ℚ) ^ n =
        fwdDiff (n + 1) (fun j => (j : ℚ) ^ n) := by
    have hinner : ∀ u ∈ range (n + 1),
        ∑ k ∈ range (n + 1), (-1 : ℚ) ^ (u + 1) * (k.choose u : ℚ) * ((u + 1 : ℕ) : ℚ) ^ n =
          (-1 : ℚ) ^ (u + 1) * ((n + 1).choose (u + 1) : ℚ) * ((u + 1 : ℕ) : ℚ) ^ n := by
      intro u _
      have hf : ∑ k ∈ range (n + 1), (-1 : ℚ) ^ (u + 1) * (k.choose u : ℚ) * ((u + 1 : ℕ) : ℚ) ^ n =
          (-1 : ℚ) ^ (u + 1) * ((u + 1 : ℕ) : ℚ) ^ n * (∑ k ∈ range (n + 1), (k.choose u : ℚ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [hf]
      have hhs : ∑ k ∈ range (n + 1), (k.choose u : ℚ) = ((n + 1).choose (u + 1) : ℚ) := by
        exact_mod_cast sum_choose_range n u
      rw [hhs]
      ring
    rw [Finset.sum_congr rfl hinner]
    symm
    unfold fwdDiff
    rw [Finset.sum_range_succ']
    have h0 : (0 : ℚ) ^ n = 0 := zero_pow (by omega)
    simp [h0]
  rw [hstep3]
  exact fwdDiff_pow_eq_zero (n + 1) n (Nat.lt_succ_self n)

private lemma W_eq_bernoulli (m : ℕ) : W m = _root_.bernoulli m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => rw [W_zero, _root_.bernoulli_zero]
    | succ n =>
      have hW := sum_W_eq_zero (n := n + 1) (by omega)
      have hB := _root_.sum_bernoulli (n + 2)
      simp only [show n + 2 ≠ 1 by omega, ↓reduceIte] at hB
      rw [Finset.sum_range_succ] at hW hB
      have hprev :
          ∑ i ∈ range (n + 1), ((n + 2).choose i : ℚ) * W i =
            ∑ i ∈ range (n + 1), ((n + 2).choose i : ℚ) * _root_.bernoulli i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [ih i (Finset.mem_range.mp hi)]
      have hcoeff : ((n + 2).choose (n + 1) : ℚ) ≠ 0 := by
        rw [Nat.choose_succ_self_right]
        positivity
      have hmul : ((n + 2).choose (n + 1) : ℚ) * (W (n + 1) - _root_.bernoulli (n + 1)) = 0 := by
        linarith
      rcases mul_eq_zero.mp hmul with hc | hd
      · exact absurd hc hcoeff
      · linarith

private lemma pochhammer_eval_eq_multichoose (j r : ℕ) :
    (r.factorial : ℚ)⁻¹ * (ascPochhammer ℚ r).eval (j : ℚ) = (Nat.multichoose j r : ℚ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [ascPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_natCast]
    have hrec : ((r + 1 : ℕ) : ℚ) * (Nat.multichoose j (r + 1) : ℚ) =
        ((j + r : ℕ) : ℚ) * (Nat.multichoose j r : ℚ) := by
      have hnat : (r + 1) * Nat.multichoose j (r + 1) = (j + r) * Nat.multichoose j r := by
        cases j with
        | zero =>
          simp only [Nat.multichoose_zero_succ, mul_zero, zero_add]
          cases r with
          | zero => simp
          | succ r' => simp
        | succ j' =>
          rw [Nat.multichoose_eq, Nat.multichoose_eq]
          have h1 : j' + 1 + (r + 1) - 1 = (j' + r) + 1 := by omega
          have h2 : j' + 1 + r - 1 = j' + r := by omega
          rw [h1, h2]
          have h4 := Nat.add_one_mul_choose_eq (j' + r) r
          have h5 : j' + 1 + r = j' + r + 1 := by omega
          rw [h5]
          linarith
      exact_mod_cast hnat
    have hfac : ((r + 1).factorial : ℚ) = ((r + 1 : ℕ) : ℚ) * (r.factorial : ℚ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hr1 : ((r + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    rw [hfac, mul_inv, mul_assoc, ← mul_assoc (r.factorial : ℚ)⁻¹, ih]
    apply mul_left_cancel₀ hr1
    rw [hrec]
    push_cast
    field_simp [hr1]

private lemma slotPoly_eval (a : List ℕ) (j : ℕ) :
    (OMA.S_mo_506929.slotPoly a).eval (j : ℚ) =
      (a.map (fun r => (Nat.multichoose j r : ℚ))).prod := by
  unfold OMA.S_mo_506929.slotPoly
  induction a with
  | nil => simp
  | cons r l ih =>
    simp only [List.map_cons, List.prod_cons, Polynomial.eval_mul, Polynomial.eval_C]
    rw [pochhammer_eval_eq_multichoose, ih]

private lemma slotPoly_natDegree_le (a : List ℕ) :
    (OMA.S_mo_506929.slotPoly a).natDegree ≤ a.sum := by
  unfold OMA.S_mo_506929.slotPoly
  induction a with
  | nil => simp
  | cons r l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    calc (C (r.factorial : ℚ)⁻¹ * ascPochhammer ℚ r *
            (l.map (fun r => C (r.factorial : ℚ)⁻¹ * ascPochhammer ℚ r)).prod).natDegree
        ≤ (C (r.factorial : ℚ)⁻¹ * ascPochhammer ℚ r).natDegree +
            (l.map (fun r => C (r.factorial : ℚ)⁻¹ * ascPochhammer ℚ r)).prod.natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ r + l.sum := by
          apply Nat.add_le_add _ ih
          calc (C (r.factorial : ℚ)⁻¹ * ascPochhammer ℚ r).natDegree
              ≤ (C (r.factorial : ℚ)⁻¹).natDegree + (ascPochhammer ℚ r).natDegree :=
                Polynomial.natDegree_mul_le
            _ = r := by
                rw [Polynomial.natDegree_C, zero_add, ascPochhammer_natDegree]

private lemma slotPoly_eval_zero (a : List ℕ) (ha : a ≠ []) (hpos : ∀ r ∈ a, 0 < r) :
    (OMA.S_mo_506929.slotPoly a).eval 0 = 0 := by
  have h := slotPoly_eval a 0
  simp only [Nat.cast_zero] at h
  rw [h]
  cases a with
  | nil => exact absurd rfl ha
  | cons r l =>
    have hr : 0 < r := hpos r (by simp)
    cases r with
    | zero => omega
    | succ r' => simp

private lemma neg_one_pow_sign (k j : ℕ) (hj : j ≤ k + 1) :
    (-1 : ℚ) ^ k * (-1 : ℚ) ^ (k + 1 - j) = -((-1 : ℚ) ^ j) := by
  have h1 : (-1 : ℚ) ^ k * (-1 : ℚ) ^ (k + 1 - j) * (-1 : ℚ) ^ j = -1 := by
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hj, ← pow_add]
    have h2 : k + (k + 1) = 2 * k + 1 := by omega
    rw [h2, pow_succ, pow_mul]
    norm_num
  have hsq : (-1 : ℚ) ^ j * (-1 : ℚ) ^ j = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc (-1 : ℚ) ^ k * (-1 : ℚ) ^ (k + 1 - j)
      = (-1 : ℚ) ^ k * (-1 : ℚ) ^ (k + 1 - j) * ((-1 : ℚ) ^ j * (-1 : ℚ) ^ j) := by
        rw [hsq, mul_one]
    _ = ((-1 : ℚ) ^ k * (-1 : ℚ) ^ (k + 1 - j) * (-1 : ℚ) ^ j) * (-1 : ℚ) ^ j := by ring
    _ = -((-1 : ℚ) ^ j) := by rw [h1]; ring

private lemma part1 (a : List ℕ) (ha : a ≠ []) (hpos : ∀ r ∈ a, 0 < r) :
    OMA.S_mo_506929.value a =
      -(∑ i ∈ range (a.sum + 1), (OMA.S_mo_506929.slotPoly a).coeff i * _root_.bernoulli i) := by
  have hval :
      OMA.S_mo_506929.value a =
        -(∑ m ∈ range (a.sum + 1),
            (m + 1 : ℚ)⁻¹ * fwdDiff m (fun j => (OMA.S_mo_506929.slotPoly a).eval (j : ℚ))) := by
    rw [Finset.sum_range_succ']
    have hm0 : (((0 : ℕ) : ℚ) + 1)⁻¹ * fwdDiff 0 (fun j => (OMA.S_mo_506929.slotPoly a).eval (j : ℚ)) = 0 := by
      simp [fwdDiff, slotPoly_eval_zero a ha hpos]
    rw [hm0, add_zero, ← Finset.sum_neg_distrib]
    unfold OMA.S_mo_506929.value OMA.S_mo_506929.orderedCount fwdDiff
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [div_eq_inv_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    dsimp only
    rw [slotPoly_eval]
    have hjle : j ≤ k + 1 := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hsign := neg_one_pow_sign k j hjle
    push_cast
    calc ((k : ℚ) + 2)⁻¹ * ((-1 : ℚ) ^ k *
            ((-1 : ℚ) ^ (k + 1 - j) * ((k + 1).choose j : ℚ) *
              (a.map fun r => (Nat.multichoose j r : ℚ)).prod))
        = ((k : ℚ) + 2)⁻¹ * (((-1 : ℚ) ^ k * (-1 : ℚ) ^ (k + 1 - j)) *
            ((k + 1).choose j : ℚ) * (a.map fun r => (Nat.multichoose j r : ℚ)).prod) := by ring
      _ = ((k : ℚ) + 2)⁻¹ * (-((-1 : ℚ) ^ j) *
            ((k + 1).choose j : ℚ) * (a.map fun r => (Nat.multichoose j r : ℚ)).prod) := by
          rw [hsign]
      _ = -(((k : ℚ) + 1 + 1)⁻¹ *
            ((-1 : ℚ) ^ j * ((k + 1).choose j : ℚ) *
              (a.map fun r => (Nat.multichoose j r : ℚ)).prod)) := by ring
  rw [hval]
  congr 1
  have heval_poly : ∀ j : ℕ,
      (OMA.S_mo_506929.slotPoly a).eval (j : ℚ) =
        ∑ i ∈ range (a.sum + 1), (OMA.S_mo_506929.slotPoly a).coeff i * (j : ℚ) ^ i := by
    intro j
    rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (slotPoly_natDegree_le a) (Nat.lt_succ_self _))]
  have hswap :
      ∑ m ∈ range (a.sum + 1),
          (m + 1 : ℚ)⁻¹ * fwdDiff m (fun j => (OMA.S_mo_506929.slotPoly a).eval (j : ℚ)) =
        ∑ i ∈ range (a.sum + 1), (OMA.S_mo_506929.slotPoly a).coeff i *
          (∑ m ∈ range (a.sum + 1), (m + 1 : ℚ)⁻¹ * fwdDiff m (fun j => (j : ℚ) ^ i)) := by
    have h1 :
        ∑ m ∈ range (a.sum + 1),
            (m + 1 : ℚ)⁻¹ * fwdDiff m (fun j => (OMA.S_mo_506929.slotPoly a).eval (j : ℚ)) =
          ∑ m ∈ range (a.sum + 1), ∑ i ∈ range (a.sum + 1),
            (OMA.S_mo_506929.slotPoly a).coeff i *
              ((m + 1 : ℚ)⁻¹ * fwdDiff m (fun j => (j : ℚ) ^ i)) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      have hfn : (fun j : ℕ => (OMA.S_mo_506929.slotPoly a).eval (j : ℚ)) =
          (fun j : ℕ => ∑ i ∈ range (a.sum + 1), (OMA.S_mo_506929.slotPoly a).coeff i * (j : ℚ) ^ i) :=
        funext heval_poly
      rw [hfn, fwdDiff_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [fwdDiff_const_mul]
      ring
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  rw [hswap]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← W_eq_sum_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hi)), W_eq_bernoulli]

private lemma slotPoly_two_replicate (r : ℕ) :
    OMA.S_mo_506929.slotPoly (2 :: List.replicate r 1) =
      C (1 / 2 : ℚ) * (X ^ (r + 2) + X ^ (r + 1)) := by
  unfold OMA.S_mo_506929.slotPoly
  rw [List.map_cons, List.prod_cons, List.map_replicate, List.prod_replicate]
  have h1 : C ((1 : ℕ).factorial : ℚ)⁻¹ * ascPochhammer ℚ 1 = X := by
    simp [ascPochhammer_one]
  have h2 : C ((2 : ℕ).factorial : ℚ)⁻¹ * ascPochhammer ℚ 2 =
      C (1 / 2 : ℚ) * (X ^ 2 + X) := by
    rw [ascPochhammer_succ_right, ascPochhammer_one]
    simp only [Nat.factorial_two, Nat.cast_ofNat, one_div]
    ring
  rw [h1, h2]
  ring

private lemma part2 (r : ℕ) :
    OMA.S_mo_506929.value (2 :: List.replicate r 1) =
      -(_root_.bernoulli (r + 2) + _root_.bernoulli (r + 1)) / 2 := by
  have ha : (2 :: List.replicate r 1) ≠ [] := List.cons_ne_nil _ _
  have hpos : ∀ x ∈ (2 :: List.replicate r 1), 0 < x := by
    intro x hx
    simp only [List.mem_cons, List.mem_replicate] at hx
    rcases hx with rfl | ⟨_, rfl⟩ <;> omega
  rw [part1 _ ha hpos, slotPoly_two_replicate]
  have hsum : (2 :: List.replicate r 1).sum = r + 2 := by
    simp [List.sum_replicate, add_comm]
  rw [hsum]
  have hcoeff : ∀ i : ℕ,
      (C (1 / 2 : ℚ) * (X ^ (r + 2) + X ^ (r + 1))).coeff i =
        (if i = r + 2 then (1 / 2 : ℚ) else 0) + (if i = r + 1 then (1 / 2 : ℚ) else 0) := by
    intro i
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_X_pow,
      Polynomial.coeff_X_pow]
    split_ifs <;> ring
  have htotal :
      ∑ i ∈ range (r + 2 + 1),
          (C (1 / 2 : ℚ) * (X ^ (r + 2) + X ^ (r + 1))).coeff i * _root_.bernoulli i =
        (1 / 2 : ℚ) * _root_.bernoulli (r + 2) + (1 / 2 : ℚ) * _root_.bernoulli (r + 1) := by
    simp_rw [hcoeff, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' (range (r + 2 + 1)) (r + 2),
      Finset.sum_ite_eq' (range (r + 2 + 1)) (r + 1)]
    have hmem2 : r + 2 ∈ range (r + 2 + 1) := Finset.mem_range.mpr (by omega)
    have hmem1 : r + 1 ∈ range (r + 2 + 1) := Finset.mem_range.mpr (by omega)
    simp [hmem2, hmem1]
  rw [htotal]
  ring

private lemma bernoulli_odd_val {n : ℕ} (h : n % 2 = 1) (hlt : 1 < n) : _root_.bernoulli n = 0 :=
  _root_.bernoulli_eq_zero_of_odd (Nat.odd_iff.mpr h) hlt

private lemma bernoulli_step (n : ℕ) (hn : 1 ≤ n) :
    _root_.bernoulli n =
      -(∑ k ∈ range n, ((n + 1).choose k : ℚ) * _root_.bernoulli k) / (n + 1 : ℚ) := by
  have h := _root_.sum_bernoulli (n + 1)
  simp only [show n + 1 ≠ 1 by omega, ↓reduceIte] at h
  rw [Finset.sum_range_succ, Nat.choose_succ_self_right] at h
  have hpos : (n + 1 : ℚ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hpos
  field_simp [hpos]
  push_cast at h
  linarith

private lemma bernoulli_four : _root_.bernoulli 4 = -1 / 30 := by
  rw [_root_.bernoulli_eq_bernoulli'_of_ne_one (by decide), _root_.bernoulli'_four]

private lemma bernoulli_six : _root_.bernoulli 6 = 1 / 42 := by
  rw [bernoulli_step 6 (by omega)]
  have h3 : _root_.bernoulli 3 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h5 : _root_.bernoulli 5 = 0 := bernoulli_odd_val (by decide) (by decide)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, _root_.bernoulli_zero,
    _root_.bernoulli_one, _root_.bernoulli_two, h3, bernoulli_four, h5]
  norm_num [Nat.choose]

private lemma bernoulli_eight : _root_.bernoulli 8 = -1 / 30 := by
  rw [bernoulli_step 8 (by omega)]
  have h3 : _root_.bernoulli 3 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h5 : _root_.bernoulli 5 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h7 : _root_.bernoulli 7 = 0 := bernoulli_odd_val (by decide) (by decide)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, _root_.bernoulli_zero,
    _root_.bernoulli_one, _root_.bernoulli_two, h3, bernoulli_four, h5, bernoulli_six, h7]
  norm_num [Nat.choose]

private lemma bernoulli_ten : _root_.bernoulli 10 = 5 / 66 := by
  rw [bernoulli_step 10 (by omega)]
  have h3 : _root_.bernoulli 3 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h5 : _root_.bernoulli 5 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h7 : _root_.bernoulli 7 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h9 : _root_.bernoulli 9 = 0 := bernoulli_odd_val (by decide) (by decide)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, _root_.bernoulli_zero,
    _root_.bernoulli_one, _root_.bernoulli_two, h3, bernoulli_four, h5, bernoulli_six, h7,
    bernoulli_eight, h9]
  norm_num [Nat.choose]

private lemma bernoulli_twelve : _root_.bernoulli 12 = -691 / 2730 := by
  rw [bernoulli_step 12 (by omega)]
  have h3 : _root_.bernoulli 3 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h5 : _root_.bernoulli 5 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h7 : _root_.bernoulli 7 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h9 : _root_.bernoulli 9 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h11 : _root_.bernoulli 11 = 0 := bernoulli_odd_val (by decide) (by decide)
  have c0 : Nat.choose 13 0 = 1 := by decide
  have c1 : Nat.choose 13 1 = 13 := by decide
  have c2 : Nat.choose 13 2 = 78 := by decide
  have c4 : Nat.choose 13 4 = 715 := by decide
  have c6 : Nat.choose 13 6 = 1716 := by decide
  have c8 : Nat.choose 13 8 = 1287 := by decide
  have c10 : Nat.choose 13 10 = 286 := by decide
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, _root_.bernoulli_zero,
    _root_.bernoulli_one, _root_.bernoulli_two, h3, bernoulli_four, h5, bernoulli_six, h7,
    bernoulli_eight, h9, bernoulli_ten, h11, c0, c1, c2, c4, c6, c8, c10]
  norm_num

private lemma bernoulli_fourteen : _root_.bernoulli 14 = 7 / 6 := by
  rw [bernoulli_step 14 (by omega)]
  have h3 : _root_.bernoulli 3 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h5 : _root_.bernoulli 5 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h7 : _root_.bernoulli 7 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h9 : _root_.bernoulli 9 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h11 : _root_.bernoulli 11 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h13 : _root_.bernoulli 13 = 0 := bernoulli_odd_val (by decide) (by decide)
  have c0 : Nat.choose 15 0 = 1 := by decide
  have c1 : Nat.choose 15 1 = 15 := by decide
  have c2 : Nat.choose 15 2 = 105 := by decide
  have c4 : Nat.choose 15 4 = 1365 := by decide
  have c6 : Nat.choose 15 6 = 5005 := by decide
  have c8 : Nat.choose 15 8 = 6435 := by decide
  have c10 : Nat.choose 15 10 = 3003 := by decide
  have c12 : Nat.choose 15 12 = 455 := by decide
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, _root_.bernoulli_zero,
    _root_.bernoulli_one, _root_.bernoulli_two, h3, bernoulli_four, h5, bernoulli_six, h7,
    bernoulli_eight, h9, bernoulli_ten, h11, bernoulli_twelve, h13,
    c0, c1, c2, c4, c6, c8, c10, c12]
  norm_num

private lemma bernoulli_sixteen : _root_.bernoulli 16 = -3617 / 510 := by
  rw [bernoulli_step 16 (by omega)]
  have h3 : _root_.bernoulli 3 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h5 : _root_.bernoulli 5 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h7 : _root_.bernoulli 7 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h9 : _root_.bernoulli 9 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h11 : _root_.bernoulli 11 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h13 : _root_.bernoulli 13 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h15 : _root_.bernoulli 15 = 0 := bernoulli_odd_val (by decide) (by decide)
  have c0 : Nat.choose 17 0 = 1 := by decide
  have c1 : Nat.choose 17 1 = 17 := by decide
  have c2 : Nat.choose 17 2 = 136 := by decide
  have c4 : Nat.choose 17 4 = 2380 := by decide
  have c6 : Nat.choose 17 6 = 12376 := by decide
  have c8 : Nat.choose 17 8 = 24310 := by decide
  have c10 : Nat.choose 17 10 = 19448 := by decide
  have c12 : Nat.choose 17 12 = 6188 := by decide
  have c14 : Nat.choose 17 14 = 680 := by decide
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, _root_.bernoulli_zero,
    _root_.bernoulli_one, _root_.bernoulli_two, h3, bernoulli_four, h5, bernoulli_six, h7,
    bernoulli_eight, h9, bernoulli_ten, h11, bernoulli_twelve, h13, bernoulli_fourteen, h15,
    c0, c1, c2, c4, c6, c8, c10, c12, c14]
  norm_num

private lemma bernoulli_eighteen : _root_.bernoulli 18 = 43867 / 798 := by
  rw [bernoulli_step 18 (by omega)]
  have h3 : _root_.bernoulli 3 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h5 : _root_.bernoulli 5 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h7 : _root_.bernoulli 7 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h9 : _root_.bernoulli 9 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h11 : _root_.bernoulli 11 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h13 : _root_.bernoulli 13 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h15 : _root_.bernoulli 15 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h17 : _root_.bernoulli 17 = 0 := bernoulli_odd_val (by decide) (by decide)
  have c0 : Nat.choose 19 0 = 1 := by decide
  have c1 : Nat.choose 19 1 = 19 := by decide
  have c2 : Nat.choose 19 2 = 171 := by decide
  have c4 : Nat.choose 19 4 = 3876 := by decide
  have c6 : Nat.choose 19 6 = 27132 := by decide
  have c8 : Nat.choose 19 8 = 75582 := by decide
  have c10 : Nat.choose 19 10 = 92378 := by decide
  have c12 : Nat.choose 19 12 = 50388 := by decide
  have c14 : Nat.choose 19 14 = 11628 := by decide
  have c16 : Nat.choose 19 16 = 969 := by decide
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, _root_.bernoulli_zero,
    _root_.bernoulli_one, _root_.bernoulli_two, h3, bernoulli_four, h5, bernoulli_six, h7,
    bernoulli_eight, h9, bernoulli_ten, h11, bernoulli_twelve, h13, bernoulli_fourteen, h15,
    bernoulli_sixteen, h17,
    c0, c1, c2, c4, c6, c8, c10, c12, c14, c16]
  norm_num

private lemma part3 :
    1 < OMA.S_mo_506929.value (2 :: List.replicate 14 1) ∧
      OMA.S_mo_506929.value (2 :: List.replicate 16 1) < -1 := by
  have h15 : _root_.bernoulli 15 = 0 := bernoulli_odd_val (by decide) (by decide)
  have h17 : _root_.bernoulli 17 = 0 := bernoulli_odd_val (by decide) (by decide)
  rw [part2 14, part2 16]
  norm_num [bernoulli_sixteen, h15, bernoulli_eighteen, h17]

end OMA.S_mo_506929_Proof

theorem OMA.solution : type_of% @OMA.S_mo_506929.main := by
  exact ⟨OMA.S_mo_506929_Proof.part1, OMA.S_mo_506929_Proof.part2, OMA.S_mo_506929_Proof.part3⟩
