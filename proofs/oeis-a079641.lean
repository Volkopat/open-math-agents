import OMAStatements.S_oeis_a079641
import Mathlib

namespace OMA.P_oeis_a079641

open OMA.S_oeis_a079641 Finset

/-- Rising factorial polynomial `(a)^{\overline{m}} = a (a + 1) ... (a + m - 1)` in `ℚ[X]`. -/
private noncomputable def risingPoly (a : Polynomial ℚ) : ℕ → Polynomial ℚ
  | 0 => 1
  | m + 1 => risingPoly a m * (a + Polynomial.C (m : ℚ))

private lemma risingPoly_succ_left (a : Polynomial ℚ) (m : ℕ) :
    risingPoly a (m + 1) = a * risingPoly (a + 1) m := by
  induction m with
  | zero => simp [risingPoly]
  | succ m ih =>
    simp only [risingPoly] at ih ⊢
    rw [ih]
    have h1 : a + 1 + Polynomial.C (m : ℚ) = a + Polynomial.C ((m + 1 : ℕ) : ℚ) := by
      simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]; ring
    rw [h1]
    ring

private lemma stirling2_gt (n k : ℕ) (hk : n < k) : stirling2 n k = 0 := by
  induction n generalizing k with
  | zero => cases k with | zero => omega | succ k' => rfl
  | succ n' ih =>
    cases k with
    | zero => omega
    | succ k' =>
      simp only [stirling2, ih (k' + 1) (by omega), ih k' (by omega), mul_zero, add_zero]

private lemma stirling2_diag (k : ℕ) : stirling2 k k = 1 := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    simp only [stirling2, stirling2_gt k' (k' + 1) (by omega), mul_zero, zero_add, ih]

private lemma unsignedStirling1_gt (n k : ℕ) (hk : n < k) : unsignedStirling1 n k = 0 := by
  induction n generalizing k with
  | zero => cases k with | zero => omega | succ k' => rfl
  | succ n' ih =>
    cases k with
    | zero => omega
    | succ k' =>
      simp only [unsignedStirling1, ih (k' + 1) (by omega), ih k' (by omega), mul_zero, add_zero]

private lemma risingPoly_X_eq_sum_stirling1 (r : ℕ) :
    risingPoly Polynomial.X r =
      ∑ j ∈ Finset.range (r + 1), Polynomial.C ((unsignedStirling1 r j : ℕ) : ℚ) * Polynomial.X ^ j := by
  induction r with
  | zero =>
    simp [risingPoly, unsignedStirling1]
  | succ r ih =>
    simp only [risingPoly, ih]
    rw [Finset.sum_mul]
    conv_rhs => rw [Finset.sum_range_succ']
    have hu0 : unsignedStirling1 (r + 1) 0 = 0 := rfl
    rw [hu0, Nat.cast_zero, map_zero, zero_mul, add_zero]
    have h1 : (∑ j ∈ Finset.range (r + 1),
        Polynomial.C ((unsignedStirling1 r j : ℕ) : ℚ) * Polynomial.X ^ j *
          (Polynomial.X + Polynomial.C (r : ℚ))) =
        (∑ j ∈ Finset.range (r + 1),
          Polynomial.C ((unsignedStirling1 r j : ℕ) : ℚ) * Polynomial.X ^ (j + 1)) +
        (∑ j ∈ Finset.range (r + 1),
          Polynomial.C (((r * unsignedStirling1 r j : ℕ) : ℚ)) * Polynomial.X ^ j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Nat.cast_mul, map_mul]
      ring
    rw [h1]
    have hsplit : ∑ j ∈ Finset.range (r + 1),
          Polynomial.C (((r * unsignedStirling1 r j : ℕ) : ℚ)) * Polynomial.X ^ j =
        ∑ j ∈ Finset.range (r + 1),
          Polynomial.C (((r * unsignedStirling1 r (j + 1) : ℕ) : ℚ)) * Polynomial.X ^ (j + 1) := by
      cases r with
      | zero => simp [unsignedStirling1]
      | succ r' =>
        conv_lhs => rw [Finset.sum_range_succ']
        conv_rhs => rw [Finset.sum_range_succ]
        have h0 : unsignedStirling1 (r' + 1) 0 = 0 := rfl
        have ht : unsignedStirling1 (r' + 1) (r' + 1 + 1) = 0 := unsignedStirling1_gt _ _ (by omega)
        simp only [h0, ht, mul_zero, Nat.cast_zero, map_zero, zero_mul, add_zero]
    rw [hsplit, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [unsignedStirling1, Nat.cast_add, Nat.cast_mul, map_add, map_mul]
    ring

/-- Auxiliary polynomial `f(k, r) = (r)_k * (X + k)^{\overline{r - k}}` for `k ≤ r`, else `0`. -/
private noncomputable def fPoly (k r : ℕ) : Polynomial ℚ :=
  if k ≤ r then
    Polynomial.C ((Nat.descFactorial r k : ℕ) : ℚ) *
      risingPoly (Polynomial.X + Polynomial.C (k : ℚ)) (r - k)
  else
    0

/-- Auxiliary sum `g(k, r) = f(k, r) + 2 * f(k + 1, r)`. -/
private noncomputable def gPoly (k r : ℕ) : Polynomial ℚ :=
  fPoly k r + 2 * fPoly (k + 1) r

private lemma descFactorial_eq_mul (r k : ℕ) (_hk : k ≤ r) :
    Nat.descFactorial r (k + 1) = Nat.descFactorial r k * (r - k) := by
  rw [Nat.descFactorial_succ, mul_comm]

private lemma descFactorial_succ_top (r k : ℕ) (hk : 1 ≤ k) :
    Nat.descFactorial (r + 1) k = (r + 1) * Nat.descFactorial r (k - 1) := by
  cases k with
  | zero => omega
  | succ k' =>
    simp only [Nat.add_sub_cancel]
    exact Nat.succ_descFactorial_succ r k'

/-- Key polynomial identity driving the 2-step Stieltjes recurrence:
`r * f(k, r) + f(k, r + 1) = k * g(k - 1, r) + (X + k) * g(k, r)`. -/
private lemma fPoly_step (k r : ℕ) :
    Polynomial.C (r : ℚ) * fPoly k r + fPoly k (r + 1) =
      (if k = 0 then 0 else Polynomial.C (k : ℚ) * gPoly (k - 1) r) +
        (Polynomial.X + Polynomial.C (k : ℚ)) * gPoly k r := by
  by_cases hkr : k ≤ r
  · cases k with
    | zero =>
      simp only [ite_true, zero_add, gPoly, fPoly, Nat.zero_le, ite_true, Nat.descFactorial_zero,
        Nat.cast_one, map_one, one_mul, Nat.sub_zero, Nat.cast_zero, map_zero, add_zero]
      by_cases hr1 : 1 ≤ r
      · rw [if_pos hr1]
        have hsub : r - 1 + 1 = r := by omega
        have hrise1 : risingPoly Polynomial.X r =
            Polynomial.X * risingPoly (Polynomial.X + 1) (r - 1) := by
          conv_lhs => rw [← hsub]
          exact risingPoly_succ_left Polynomial.X (r - 1)
        have hrise2 : risingPoly Polynomial.X (r + 1) =
            risingPoly Polynomial.X r * (Polynomial.X + Polynomial.C (r : ℚ)) := rfl
        rw [hrise2, Nat.descFactorial_one]
        have h2 : Polynomial.X * (2 * (Polynomial.C (r : ℚ) * risingPoly (Polynomial.X + 1) (r - 1))) =
            2 * Polynomial.C (r : ℚ) * risingPoly Polynomial.X r := by
          rw [hrise1]; ring
        linear_combination -h2
      · have hr0 : r = 0 := by omega
        subst hr0
        simp [risingPoly]
    | succ k' =>
      have hk1 : k' + 1 ≠ 0 := by omega
      rw [if_neg hk1, Nat.add_sub_cancel]
      unfold gPoly fPoly
      rw [if_pos hkr, if_pos (by omega : k' + 1 ≤ r + 1), if_pos (by omega : k' ≤ r)]
      set P := risingPoly (Polynomial.X + Polynomial.C ((k' + 1 : ℕ) : ℚ)) (r - (k' + 1))
      have hP1 : risingPoly (Polynomial.X + Polynomial.C ((k' + 1 : ℕ) : ℚ)) (r + 1 - (k' + 1)) =
          P * (Polynomial.X + Polynomial.C (r : ℚ)) := by
        have hidx : r + 1 - (k' + 1) = (r - (k' + 1)) + 1 := by omega
        rw [hidx, risingPoly]
        have hc : Polynomial.C ((k' + 1 : ℕ) : ℚ) + Polynomial.C ((r - (k' + 1) : ℕ) : ℚ) =
            Polynomial.C (r : ℚ) := by
          rw [← map_add]; congr 1; exact_mod_cast (by omega : k' + 1 + (r - (k' + 1)) = r)
        rw [add_assoc, hc]
      have hPprev : risingPoly (Polynomial.X + Polynomial.C (k' : ℚ)) (r - k') =
          (Polynomial.X + Polynomial.C (k' : ℚ)) * P := by
        have hidx : r - k' = (r - (k' + 1)) + 1 := by omega
        rw [hidx, risingPoly_succ_left]
        have hc : Polynomial.X + Polynomial.C (k' : ℚ) + 1 =
            Polynomial.X + Polynomial.C ((k' + 1 : ℕ) : ℚ) := by
          simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]; ring
        rw [hc]
      have hPnext : (Polynomial.X + Polynomial.C ((k' + 1 : ℕ) : ℚ)) *
            (if k' + 2 ≤ r then
              Polynomial.C ((Nat.descFactorial r (k' + 2) : ℕ) : ℚ) *
                risingPoly (Polynomial.X + Polynomial.C ((k' + 2 : ℕ) : ℚ)) (r - (k' + 2))
            else 0) =
          Polynomial.C (((Nat.descFactorial r (k' + 1) * (r - (k' + 1)) : ℕ) : ℚ)) * P := by
        by_cases h2 : k' + 2 ≤ r
        · rw [if_pos h2]
          have hdesc : Nat.descFactorial r (k' + 2) = Nat.descFactorial r (k' + 1) * (r - (k' + 1)) :=
            descFactorial_eq_mul r (k' + 1) hkr
          have hidx : r - (k' + 1) = (r - (k' + 2)) + 1 := by omega
          have hrise : P = (Polynomial.X + Polynomial.C ((k' + 1 : ℕ) : ℚ)) *
              risingPoly (Polynomial.X + Polynomial.C ((k' + 2 : ℕ) : ℚ)) (r - (k' + 2)) := by
            dsimp only [P]
            rw [hidx, risingPoly_succ_left]
            have hc : Polynomial.X + Polynomial.C ((k' + 1 : ℕ) : ℚ) + 1 =
                Polynomial.X + Polynomial.C ((k' + 2 : ℕ) : ℚ) := by
              simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, map_add, map_one, map_ofNat]; ring
            rw [hc]
          rw [hdesc, hrise]
          ring
        · rw [if_neg h2, mul_zero]
          have h0 : r - (k' + 1) = 0 := by omega
          simp [h0]
      have hdf1 : ((Nat.descFactorial r (k' + 1) : ℕ) : ℚ) =
          ((Nat.descFactorial r k' : ℕ) : ℚ) * ((r : ℚ) - (k' : ℚ)) := by
        have h := descFactorial_eq_mul r k' (by omega)
        rw [h]; push_cast
        have : ((r - k' : ℕ) : ℚ) = (r : ℚ) - (k' : ℚ) := by
          rw [Nat.cast_sub (by omega)]
        rw [this]
      have hdf2 : ((Nat.descFactorial (r + 1) (k' + 1) : ℕ) : ℚ) =
          ((r : ℚ) + 1) * ((Nat.descFactorial r k' : ℕ) : ℚ) := by
        have h := descFactorial_succ_top r (k' + 1) (by omega)
        simp only [Nat.add_sub_cancel] at h
        rw [h]; push_cast; ring
      have hsub_cast : ((r - (k' + 1) : ℕ) : ℚ) = (r : ℚ) - ((k' : ℚ) + 1) := by
        rw [Nat.cast_sub hkr]; push_cast; ring
      rw [hP1, hPprev, mul_add (Polynomial.X + Polynomial.C ((k' + 1 : ℕ) : ℚ)),
        show (Polynomial.X + Polynomial.C ((k' + 1 : ℕ) : ℚ)) *
          (2 * (if k' + 2 ≤ r then
            Polynomial.C ((Nat.descFactorial r (k' + 2) : ℕ) : ℚ) *
              risingPoly (Polynomial.X + Polynomial.C ((k' + 2 : ℕ) : ℚ)) (r - (k' + 2))
          else 0)) =
          2 * ((Polynomial.X + Polynomial.C ((k' + 1 : ℕ) : ℚ)) *
            (if k' + 2 ≤ r then
              Polynomial.C ((Nat.descFactorial r (k' + 2) : ℕ) : ℚ) *
                risingPoly (Polynomial.X + Polynomial.C ((k' + 2 : ℕ) : ℚ)) (r - (k' + 2))
            else 0)) by ring,
        hPnext]
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, hdf1, hdf2, hsub_cast,
        map_mul, map_add, map_sub, map_one]
      ring
  · by_cases hkeq : k = r + 1
    · subst hkeq
      rw [if_neg (by omega : r + 1 ≠ 0), Nat.add_sub_cancel]
      unfold gPoly fPoly
      rw [if_neg (by omega : ¬ r + 1 ≤ r), if_pos le_rfl, if_pos le_rfl,
        if_neg (by omega : ¬ r + 2 ≤ r)]
      simp only [Nat.sub_self, risingPoly, mul_one, mul_zero, add_zero, zero_add]
      have h1 : Nat.descFactorial (r + 1) (r + 1) = (r + 1) * Nat.descFactorial r r := by
        rw [Nat.descFactorial_self, Nat.descFactorial_self, Nat.factorial_succ]
      rw [h1]
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, map_mul, map_add, map_one]
    · unfold gPoly fPoly
      rw [if_neg hkr, if_neg (by omega : ¬ k ≤ r + 1), if_neg (by omega : ¬ k + 1 ≤ r)]
      by_cases hk0 : k = 0
      · omega
      · rw [if_neg hk0, if_neg (by omega : ¬ k - 1 ≤ r), if_neg (by omega : ¬ k - 1 + 1 ≤ r)]
        simp

/-- Coefficients `cu k n = ∑_{r=0}^n S2(n, r) * f(k, r)`. -/
private noncomputable def cu (k n : ℕ) : Polynomial ℚ :=
  ∑ r ∈ Finset.range (n + 1), Polynomial.C ((stirling2 n r : ℕ) : ℚ) * fPoly k r

/-- Coefficients `cv k n = cu k n + 2 * cu (k + 1) n`. -/
private noncomputable def cv (k n : ℕ) : Polynomial ℚ :=
  cu k n + 2 * cu (k + 1) n

private lemma cu_zero_eq_rowPoly (n : ℕ) : cu 0 n = rowPoly n := by
  unfold cu rowPoly
  have hf0 : ∀ r : ℕ, fPoly 0 r = risingPoly Polynomial.X r := by
    intro r; simp [fPoly]
  simp_rw [hf0, risingPoly_X_eq_sum_stirling1]
  have h1 : ∀ r ∈ Finset.range (n + 1),
      Polynomial.C ((stirling2 n r : ℕ) : ℚ) *
        (∑ j ∈ Finset.range (r + 1), Polynomial.C ((unsignedStirling1 r j : ℕ) : ℚ) * Polynomial.X ^ j) =
      ∑ j ∈ Finset.range (n + 1),
        Polynomial.C (((stirling2 n r * unsignedStirling1 r j : ℕ) : ℚ)) * Polynomial.X ^ j := by
    intro r hr
    rw [Finset.mul_sum]
    have hrle : r ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hsub : Finset.range (r + 1) ⊆ Finset.range (n + 1) := Finset.range_mono (by omega)
    rw [Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Nat.cast_mul, map_mul]; ring
    · intro j _ hjnot
      have hgt : r < j := by simp only [Finset.mem_range] at hjnot; omega
      simp [unsignedStirling1_gt r j hgt]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_mul, map_sum]

private lemma cu_of_lt (k n : ℕ) (h : n < k) : cu k n = 0 := by
  unfold cu
  refine Finset.sum_eq_zero (fun r hr => ?_)
  have hrle : r ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  simp [fPoly, show ¬ k ≤ r by omega]

private lemma cu_diag (k : ℕ) : cu k k = Polynomial.C ((k.factorial : ℕ) : ℚ) := by
  unfold cu
  rw [Finset.sum_range_succ]
  have h0 : ∑ r ∈ Finset.range k, Polynomial.C ((stirling2 k r : ℕ) : ℚ) * fPoly k r = 0 := by
    refine Finset.sum_eq_zero (fun r hr => ?_)
    have hrlt : r < k := Finset.mem_range.mp hr
    simp [fPoly, show ¬ k ≤ r by omega]
  rw [h0, zero_add, stirling2_diag k]
  simp [fPoly, risingPoly, Nat.descFactorial_self]

private lemma cv_diag (k : ℕ) : cv k k = Polynomial.C ((k.factorial : ℕ) : ℚ) := by
  unfold cv
  rw [cu_diag k, cu_of_lt (k + 1) k (by omega)]
  ring

private lemma cu_succ (k n : ℕ) :
    cu k (n + 1) =
      (if k = 0 then 0 else Polynomial.C (k : ℚ) * cv (k - 1) n) +
        (Polynomial.X + Polynomial.C (k : ℚ)) * cv k n := by
  have hcv_sum : ∀ m : ℕ, cv m n =
      ∑ r ∈ Finset.range (n + 1), Polynomial.C ((stirling2 n r : ℕ) : ℚ) * gPoly m r := by
    intro m
    unfold cv cu gPoly
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun r _ => by ring)
  have hlhs : cu k (n + 1) =
      ∑ r ∈ Finset.range (n + 1), Polynomial.C ((stirling2 n r : ℕ) : ℚ) *
        (Polynomial.C (r : ℚ) * fPoly k r + fPoly k (r + 1)) := by
    unfold cu
    rw [Finset.sum_range_succ']
    have hs0 : stirling2 (n + 1) 0 = 0 := rfl
    rw [hs0, Nat.cast_zero, map_zero, zero_mul, add_zero]
    have hsplit : ∑ r ∈ Finset.range (n + 1),
          Polynomial.C ((stirling2 (n + 1) (r + 1) : ℕ) : ℚ) * fPoly k (r + 1) =
        (∑ r ∈ Finset.range (n + 1),
          Polynomial.C (((r + 1 : ℕ) : ℚ)) * Polynomial.C ((stirling2 n (r + 1) : ℕ) : ℚ) *
            fPoly k (r + 1)) +
        (∑ r ∈ Finset.range (n + 1),
          Polynomial.C ((stirling2 n r : ℕ) : ℚ) * fPoly k (r + 1)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      simp only [stirling2, Nat.cast_add, Nat.cast_mul, map_add, map_mul]
      ring
    rw [hsplit]
    have hshift : ∑ r ∈ Finset.range (n + 1),
          Polynomial.C (((r + 1 : ℕ) : ℚ)) * Polynomial.C ((stirling2 n (r + 1) : ℕ) : ℚ) *
            fPoly k (r + 1) =
        ∑ r ∈ Finset.range (n + 1),
          Polynomial.C ((stirling2 n r : ℕ) : ℚ) * (Polynomial.C (r : ℚ) * fPoly k r) := by
      symm
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, map_zero, zero_mul, mul_zero, add_zero]
      symm
      rw [Finset.sum_range_succ]
      have ht : stirling2 n (n + 1) = 0 := stirling2_gt n (n + 1) (by omega)
      simp only [ht, Nat.cast_zero, map_zero, mul_zero, zero_mul, add_zero]
      refine Finset.sum_congr rfl (fun r _ => by ring)
    rw [hshift, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun r _ => by ring)
  rw [hlhs]
  simp_rw [fPoly_step k, mul_add]
  rw [Finset.sum_add_distrib]
  have h2 : ∑ x ∈ Finset.range (n + 1),
        Polynomial.C ((stirling2 n x : ℕ) : ℚ) * ((Polynomial.X + Polynomial.C (k : ℚ)) * gPoly k x) =
      (Polynomial.X + Polynomial.C (k : ℚ)) * cv k n := by
    rw [hcv_sum k, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r _ => by ring)
  rw [h2]
  by_cases hk0 : k = 0
  · subst hk0
    simp
  · simp only [hk0, ite_false]
    conv_rhs => rw [hcv_sum (k - 1), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun r _ => by ring)

/-! ### Formal power series inverse `(1 - z * f(z))⁻¹` and congruence mod `z^m` -/

private lemma coeff_mul_eq_sum_range (f g : PowerSeries (Polynomial ℚ)) (n : ℕ) :
    PowerSeries.coeff n (f * g) =
      ∑ i ∈ Finset.range (n + 1), PowerSeries.coeff i f * PowerSeries.coeff (n - i) g := by
  rw [PowerSeries.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j g) n

private lemma coeff_X_mul_zero (f : PowerSeries (Polynomial ℚ)) :
    PowerSeries.coeff 0 (PowerSeries.X * f) = 0 := by
  rw [coeff_mul_eq_sum_range]
  simp

private lemma coeff_X_mul_succ (f : PowerSeries (Polynomial ℚ)) (n : ℕ) :
    PowerSeries.coeff (n + 1) (PowerSeries.X * f) = PowerSeries.coeff n f := by
  rw [coeff_mul_eq_sum_range, Finset.sum_eq_single 1]
  · simp
  · intro b _ hb
    rw [PowerSeries.coeff_X, if_neg hb, zero_mul]
  · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))

private lemma coeff_invOneSub (f : PowerSeries (Polynomial ℚ)) (n : ℕ) :
    PowerSeries.coeff n (invOneSub f) = invOneSubAux f n := by
  unfold invOneSub
  simp

private lemma one_sub_X_mul_invOneSub (f : PowerSeries (Polynomial ℚ)) :
    (1 - PowerSeries.X * f) * invOneSub f = 1 := by
  apply PowerSeries.ext; intro n
  rw [sub_mul, one_mul, map_sub]
  cases n with
  | zero =>
    rw [mul_assoc, coeff_X_mul_zero, PowerSeries.coeff_one, if_pos rfl, coeff_invOneSub]
    simp [invOneSubAux]
  | succ m =>
    rw [PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero m), coeff_invOneSub, invOneSubAux]
    rw [mul_assoc, coeff_X_mul_succ, coeff_mul_eq_sum_range]
    have hsum : ∑ i ∈ Finset.range (m + 1),
          PowerSeries.coeff i f * PowerSeries.coeff (m - i) (invOneSub f) =
        ∑ i ∈ Finset.range (m + 1),
          PowerSeries.coeff i f * invOneSubAux f (m - i) := by
      refine Finset.sum_congr rfl (fun i _ => by rw [coeff_invOneSub])
    rw [hsum, sub_self]

private lemma invOneSub_unique (f g : PowerSeries (Polynomial ℚ))
    (h : (1 - PowerSeries.X * f) * g = 1) :
    g = invOneSub f := by
  have h1 := one_sub_X_mul_invOneSub f
  calc
    g = 1 * g := (one_mul g).symm
    _ = ((1 - PowerSeries.X * f) * invOneSub f) * g := by rw [h1]
    _ = invOneSub f * ((1 - PowerSeries.X * f) * g) := by ring
    _ = invOneSub f * 1 := by rw [h]
    _ = invOneSub f := mul_one _

private lemma invOneSub_congr_lt (f g : PowerSeries (Polynomial ℚ)) (m : ℕ)
    (h : ∀ i < m, PowerSeries.coeff i f = PowerSeries.coeff i g) :
    ∀ n ≤ m, PowerSeries.coeff n (invOneSub f) = PowerSeries.coeff n (invOneSub g) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hnm
    rw [coeff_invOneSub, coeff_invOneSub]
    cases n with
    | zero => simp [invOneSubAux]
    | succ k =>
      simp only [invOneSubAux]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hilt : i < k + 1 := Finset.mem_range.mp hi
      have h1 : PowerSeries.coeff i f = PowerSeries.coeff i g := h i (by omega)
      have h2 : invOneSubAux f (k - i) = invOneSubAux g (k - i) := by
        rw [← coeff_invOneSub, ← coeff_invOneSub]
        exact ih (k - i) (by omega) (by omega)
      rw [h1, h2]

private lemma stieltjesFold_congr_c0 (m d : ℕ) (t1 t2 : PowerSeries (Polynomial ℚ))
    (hc0 : PowerSeries.coeff 0 t1 = PowerSeries.coeff 0 t2) :
    ∀ n ≤ d, PowerSeries.coeff n (stieltjesFold m d t1) =
      PowerSeries.coeff n (stieltjesFold m d t2) := by
  induction d generalizing m with
  | zero =>
    intro n hn
    have : n = 0 := by omega
    subst this
    simpa [stieltjesFold] using hc0
  | succ d ih =>
    intro n hn
    simp only [stieltjesFold]
    refine invOneSub_congr_lt _ _ (d + 1) (fun i hi => ?_) n (by omega)
    simp only [PowerSeries.coeff_C_mul]
    rw [ih (m + 1) i (by omega)]

/-! ### Normalized formal power series `Uhat k`, `Vhat k` and exact ratios `ratioS m` -/

private noncomputable def Uhat (k : ℕ) : PowerSeries (Polynomial ℚ) :=
  PowerSeries.mk (fun n => Polynomial.C ((k.factorial : ℚ)⁻¹) * cu k (n + k))

private noncomputable def Vhat (k : ℕ) : PowerSeries (Polynomial ℚ) :=
  PowerSeries.mk (fun n => Polynomial.C ((k.factorial : ℚ)⁻¹) * cv k (n + k))

private lemma coeff_zero_Uhat (k : ℕ) : PowerSeries.coeff 0 (Uhat k) = 1 := by
  simp only [Uhat, PowerSeries.coeff_mk, zero_add, cu_diag, ← map_mul]
  have hne : (k.factorial : ℚ) ≠ 0 := by positivity
  rw [inv_mul_cancel₀ hne, map_one]

private lemma coeff_zero_Vhat (k : ℕ) : PowerSeries.coeff 0 (Vhat k) = 1 := by
  simp only [Vhat, PowerSeries.coeff_mk, zero_add, cv_diag, ← map_mul]
  have hne : (k.factorial : ℚ) ≠ 0 := by positivity
  rw [inv_mul_cancel₀ hne, map_one]

private lemma Uhat_zero_eq :
    Uhat 0 = PowerSeries.mk rowPoly := by
  apply PowerSeries.ext; intro n
  simp [Uhat, cu_zero_eq_rowPoly]

/-- Relation 1: `Vhat k = Uhat k + 2 * (k + 1) * z * Uhat (k + 1)`. -/
private lemma Vhat_eq_Uhat_add (k : ℕ) :
    Vhat k = Uhat k + PowerSeries.C (Polynomial.C (((2 * (k + 1) : ℕ) : ℚ))) *
      (PowerSeries.X * Uhat (k + 1)) := by
  apply PowerSeries.ext; intro n
  cases n with
  | zero =>
    rw [map_add, PowerSeries.coeff_C_mul, coeff_X_mul_zero, mul_zero, add_zero,
      coeff_zero_Vhat, coeff_zero_Uhat]
  | succ m =>
    rw [map_add, PowerSeries.coeff_C_mul, coeff_X_mul_succ]
    simp only [Vhat, Uhat, PowerSeries.coeff_mk]
    unfold cv
    have hidx : m + 1 + k = m + (k + 1) := by omega
    rw [hidx, Nat.factorial_succ]
    have hne : (k.factorial : ℚ) ≠ 0 := by positivity
    have hne1 : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hfac : Polynomial.C ((k.factorial : ℚ)⁻¹) * Polynomial.C (2 : ℚ) =
        Polynomial.C (((2 * (k + 1) : ℕ) : ℚ)) *
          Polynomial.C ((((k + 1) * k.factorial : ℕ) : ℚ)⁻¹) := by
      rw [← map_mul, ← map_mul]; congr 1; push_cast; field_simp
    have h2 : (2 : Polynomial ℚ) = Polynomial.C (2 : ℚ) := rfl
    rw [mul_add, ← mul_assoc, h2, hfac]
    ring

/-- Relation 2a (`k = 0`): `Uhat 0 = 1 + x * z * Vhat 0`. -/
private lemma Uhat_zero_rec :
    Uhat 0 = 1 + PowerSeries.C Polynomial.X * (PowerSeries.X * Vhat 0) := by
  apply PowerSeries.ext; intro n
  cases n with
  | zero =>
    rw [map_add, PowerSeries.coeff_one, if_pos rfl, PowerSeries.coeff_C_mul, coeff_X_mul_zero,
      mul_zero, add_zero, coeff_zero_Uhat]
  | succ m =>
    rw [map_add, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero m), zero_add,
      PowerSeries.coeff_C_mul, coeff_X_mul_succ]
    simp only [Uhat, Vhat, PowerSeries.coeff_mk, Nat.add_zero, Nat.factorial_zero,
      Nat.cast_one, inv_one, map_one, one_mul]
    rw [cu_succ 0 m]
    simp

/-- Relation 2b (`k ≥ 1`): `Uhat (k + 1) = Vhat k + (x + k + 1) * z * Vhat (k + 1)`. -/
private lemma Uhat_succ_rec (k : ℕ) :
    Uhat (k + 1) = Vhat k + PowerSeries.C (Polynomial.X + Polynomial.C ((k + 1 : ℕ) : ℚ)) *
      (PowerSeries.X * Vhat (k + 1)) := by
  apply PowerSeries.ext; intro n
  cases n with
  | zero =>
    rw [map_add, PowerSeries.coeff_C_mul, coeff_X_mul_zero, mul_zero, add_zero,
      coeff_zero_Uhat, coeff_zero_Vhat]
  | succ m =>
    rw [map_add, PowerSeries.coeff_C_mul, coeff_X_mul_succ]
    simp only [Uhat, Vhat, PowerSeries.coeff_mk]
    have hidx : m + 1 + (k + 1) = (m + (k + 1)) + 1 := by omega
    rw [hidx, cu_succ (k + 1) (m + (k + 1))]
    rw [if_neg (by omega : k + 1 ≠ 0), Nat.add_sub_cancel]
    have hidx2 : m + (k + 1) = m + 1 + k := by omega
    rw [Nat.factorial_succ]
    have hne : (k.factorial : ℚ) ≠ 0 := by positivity
    have hne1 : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hfac : Polynomial.C ((((k + 1) * k.factorial : ℕ) : ℚ)⁻¹) *
          Polynomial.C (((k + 1 : ℕ) : ℚ)) =
        Polynomial.C ((k.factorial : ℚ)⁻¹) := by
      rw [← map_mul]; congr 1; push_cast; field_simp
    rw [mul_add, ← mul_assoc, hfac, hidx2]
    ring

/-- Inverse of any power series `f` with constant term `1`, via `invOneSub`. -/
private noncomputable def invOfC0One (f : PowerSeries (Polynomial ℚ)) :
    PowerSeries (Polynomial ℚ) :=
  invOneSub (PowerSeries.mk (fun n => -PowerSeries.coeff (n + 1) f))

private lemma mul_invOfC0One (f : PowerSeries (Polynomial ℚ)) (hc0 : PowerSeries.coeff 0 f = 1) :
    f * invOfC0One f = 1 := by
  have h1 : 1 - PowerSeries.X * PowerSeries.mk (fun n => -PowerSeries.coeff (n + 1) f) = f := by
    apply PowerSeries.ext; intro n
    rw [map_sub]
    cases n with
    | zero => rw [PowerSeries.coeff_one, if_pos rfl, coeff_X_mul_zero, sub_zero, hc0]
    | succ m =>
      rw [PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero m), coeff_X_mul_succ,
        PowerSeries.coeff_mk, zero_sub, neg_neg]
  unfold invOfC0One
  conv_lhs => arg 1; rw [← h1]
  exact one_sub_X_mul_invOneSub _

private lemma coeff_zero_invOfC0One (f : PowerSeries (Polynomial ℚ)) :
    PowerSeries.coeff 0 (invOfC0One f) = 1 := by
  unfold invOfC0One
  rw [coeff_invOneSub]
  simp [invOneSubAux]

/-- Exact continued-fraction tails:
- `ratioS 0 = Uhat 0`
- `ratioS (2k + 1) = Vhat k / Uhat k`
- `ratioS (2k + 2) = Uhat (k + 1) / Vhat k`. -/
private noncomputable def ratioS : ℕ → PowerSeries (Polynomial ℚ)
  | 0 => Uhat 0
  | m + 1 =>
    if m % 2 = 0 then
      Vhat (m / 2) * invOfC0One (Uhat (m / 2))
    else
      Uhat (m / 2 + 1) * invOfC0One (Vhat (m / 2))

private lemma coeff_zero_ratioS (m : ℕ) : PowerSeries.coeff 0 (ratioS m) = 1 := by
  cases m with
  | zero => exact coeff_zero_Uhat 0
  | succ m' =>
    simp only [ratioS]
    split_ifs
    · rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
        ← PowerSeries.coeff_zero_eq_constantCoeff,
        coeff_zero_Vhat, coeff_zero_invOfC0One, mul_one]
    · rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
        ← PowerSeries.coeff_zero_eq_constantCoeff,
        coeff_zero_Uhat, coeff_zero_invOfC0One, mul_one]

private lemma ratioS_step (m : ℕ) :
    ratioS m = invOneSub (PowerSeries.C (stieltjesNum m) * ratioS (m + 1)) := by
  apply invOneSub_unique
  cases m with
  | zero =>
    have hnum : stieltjesNum 0 = Polynomial.X := by simp [stieltjesNum]
    have hr1 : ratioS 1 = Vhat 0 * invOfC0One (Uhat 0) := by simp [ratioS]
    have hrec := Uhat_zero_rec
    have hinv := mul_invOfC0One (Uhat 0) (coeff_zero_Uhat 0)
    rw [hnum, hr1]
    simp only [ratioS]
    calc
      (1 - PowerSeries.X * (PowerSeries.C Polynomial.X * (Vhat 0 * invOfC0One (Uhat 0)))) * Uhat 0
        = Uhat 0 - PowerSeries.C Polynomial.X * (PowerSeries.X * Vhat 0) * (Uhat 0 * invOfC0One (Uhat 0)) := by ring
      _ = Uhat 0 - PowerSeries.C Polynomial.X * (PowerSeries.X * Vhat 0) * 1 := by rw [hinv]
      _ = 1 := by rw [mul_one, hrec]; ring
  | succ m' =>
    by_cases hev : m' % 2 = 0
    · obtain ⟨k, hk⟩ : ∃ k, m' = 2 * k := ⟨m' / 2, by omega⟩
      subst hk
      have hnum : stieltjesNum (2 * k + 1) = Polynomial.C (((2 * (k + 1) : ℕ) : ℚ)) := by
        unfold stieltjesNum
        rw [if_neg (by omega : ¬ (2 * k + 1) % 2 = 0)]
        have : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
        rw [this]
      have hr : ratioS (2 * k + 1) = Vhat k * invOfC0One (Uhat k) := by
        simp [ratioS, show (2 * k) / 2 = k by omega]
      have hrn : ratioS (2 * k + 2) = Uhat (k + 1) * invOfC0One (Vhat k) := by
        simp [ratioS, show (2 * k + 1) / 2 = k by omega]
      have hrec := Vhat_eq_Uhat_add k
      have hinvU := mul_invOfC0One (Uhat k) (coeff_zero_Uhat k)
      have hinvV := mul_invOfC0One (Vhat k) (coeff_zero_Vhat k)
      rw [hnum, hr, hrn]
      calc
        (1 - PowerSeries.X * (PowerSeries.C (Polynomial.C (((2 * (k + 1) : ℕ) : ℚ))) *
            (Uhat (k + 1) * invOfC0One (Vhat k)))) * (Vhat k * invOfC0One (Uhat k))
          = (Vhat k - PowerSeries.C (Polynomial.C (((2 * (k + 1) : ℕ) : ℚ))) *
              (PowerSeries.X * Uhat (k + 1)) * (Vhat k * invOfC0One (Vhat k))) * invOfC0One (Uhat k) := by ring
        _ = (Vhat k - PowerSeries.C (Polynomial.C (((2 * (k + 1) : ℕ) : ℚ))) *
              (PowerSeries.X * Uhat (k + 1)) * 1) * invOfC0One (Uhat k) := by rw [hinvV]
        _ = Uhat k * invOfC0One (Uhat k) := by rw [mul_one, hrec]; ring
        _ = 1 := hinvU
    · obtain ⟨k, hk⟩ : ∃ k, m' = 2 * k + 1 := ⟨m' / 2, by omega⟩
      subst hk
      have hnum : stieltjesNum (2 * k + 2) = Polynomial.X + Polynomial.C ((k + 1 : ℕ) : ℚ) := by
        unfold stieltjesNum
        rw [if_pos (by omega : (2 * k + 2) % 2 = 0)]
        have : (2 * k + 2) / 2 = k + 1 := by omega
        rw [this]
      have hr : ratioS (2 * k + 2) = Uhat (k + 1) * invOfC0One (Vhat k) := by
        simp [ratioS, show (2 * k + 1) / 2 = k by omega]
      have hrn : ratioS (2 * k + 3) = Vhat (k + 1) * invOfC0One (Uhat (k + 1)) := by
        simp [ratioS, show (2 * k + 2) % 2 = 0 by omega, show (2 * k + 2) / 2 = k + 1 by omega]
      have hrec := Uhat_succ_rec k
      have hinvU := mul_invOfC0One (Uhat (k + 1)) (coeff_zero_Uhat (k + 1))
      have hinvV := mul_invOfC0One (Vhat k) (coeff_zero_Vhat k)
      rw [hnum, hr, hrn]
      calc
        (1 - PowerSeries.X * (PowerSeries.C (Polynomial.X + Polynomial.C ((k + 1 : ℕ) : ℚ)) *
            (Vhat (k + 1) * invOfC0One (Uhat (k + 1))))) * (Uhat (k + 1) * invOfC0One (Vhat k))
          = (Uhat (k + 1) - PowerSeries.C (Polynomial.X + Polynomial.C ((k + 1 : ℕ) : ℚ)) *
              (PowerSeries.X * Vhat (k + 1)) * (Uhat (k + 1) * invOfC0One (Uhat (k + 1)))) *
              invOfC0One (Vhat k) := by ring
        _ = (Uhat (k + 1) - PowerSeries.C (Polynomial.X + Polynomial.C ((k + 1 : ℕ) : ℚ)) *
              (PowerSeries.X * Vhat (k + 1)) * 1) * invOfC0One (Vhat k) := by rw [hinvU]
        _ = Vhat k * invOfC0One (Vhat k) := by rw [mul_one, hrec]; ring
        _ = 1 := hinvV

private lemma stieltjesFold_ratioS (m d : ℕ) :
    stieltjesFold m d (ratioS (m + d)) = ratioS m := by
  induction d generalizing m with
  | zero => simp [stieltjesFold]
  | succ d ih =>
    simp only [stieltjesFold]
    have hidx : m + 1 + d = m + (d + 1) := by omega
    rw [← hidx, ih (m + 1)]
    exact (ratioS_step m).symm

lemma solve_a079641 :
    ∀ n N : ℕ, n ≤ N → PowerSeries.coeff n (stieltjesFold 0 N 1) = rowPoly n := by
  intro n N hn
  have hc0 : PowerSeries.coeff 0 (1 : PowerSeries (Polynomial ℚ)) = PowerSeries.coeff 0 (ratioS N) := by
    rw [PowerSeries.coeff_one, if_pos rfl, coeff_zero_ratioS]
  rw [stieltjesFold_congr_c0 0 N 1 (ratioS N) hc0 n hn]
  have hfold := stieltjesFold_ratioS 0 N
  rw [Nat.zero_add] at hfold
  rw [hfold]
  change PowerSeries.coeff n (Uhat 0) = rowPoly n
  rw [Uhat_zero_eq, PowerSeries.coeff_mk]

end OMA.P_oeis_a079641

theorem OMA.solution : type_of% @OMA.S_oeis_a079641.main :=
  OMA.P_oeis_a079641.solve_a079641
