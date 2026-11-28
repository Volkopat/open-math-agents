import OMAStatements.S_oeis_a066108
import Mathlib

namespace OMA.S_oeis_a066108

open PowerSeries BigOperators

/-- For any polynomial `P` of degree `< d` (in particular `(k - x)^m` with `d = m + 1`),
the `d`-th alternating binomial difference vanishes:
`∑_{j=0}^d (-1)^j * C(d, j) * ((k - j : ℚ))^m = 0` for `m < d`. -/
private lemma alternating_binom_sum_pow_eq_zero :
    ∀ (d m : ℕ) (x : ℚ), m < d →
      ∑ j ∈ Finset.range (d + 1),
        (-1 : ℚ) ^ j * (Nat.choose d j : ℚ) * (x - (j : ℚ)) ^ m = 0
  | 0, _, _, hm => by omega
  | d + 1, m, x, hm => by
      -- Split `C(d + 1, j) = C(d, j) + C(d, j - 1)` to reduce `d + 1` to `d` and `m` to `< m`!
      have hsplit :
          ∑ j ∈ Finset.range (d + 2),
            (-1 : ℚ) ^ j * (Nat.choose (d + 1) j : ℚ) * (x - (j : ℚ)) ^ m =
          (∑ j ∈ Finset.range (d + 1),
            (-1 : ℚ) ^ j * (Nat.choose d j : ℚ) * (x - (j : ℚ)) ^ m) -
          (∑ j ∈ Finset.range (d + 1),
            (-1 : ℚ) ^ j * (Nat.choose d j : ℚ) * ((x - 1) - (j : ℚ)) ^ m) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.choose_zero_right, pow_zero, one_mul, Nat.cast_one,
          Nat.cast_zero, sub_zero]
        have h1 : ∑ j ∈ Finset.range (d + 1),
            (-1 : ℚ) ^ (j + 1) * (Nat.choose (d + 1) (j + 1) : ℚ) * (x - ((j + 1 : ℕ) : ℚ)) ^ m =
            (∑ j ∈ Finset.range d,
              (-1 : ℚ) ^ (j + 1) * (Nat.choose d (j + 1) : ℚ) * (x - ((j + 1 : ℕ) : ℚ)) ^ m) -
            (∑ j ∈ Finset.range (d + 1),
              (-1 : ℚ) ^ j * (Nat.choose d j : ℚ) * ((x - 1) - (j : ℚ)) ^ m) := by
          rw [Finset.sum_range_succ (f := fun j => (-1 : ℚ) ^ (j + 1) * (Nat.choose (d + 1) (j + 1) : ℚ) * (x - ((j + 1 : ℕ) : ℚ)) ^ m)]
          rw [Finset.sum_range_succ (f := fun j => (-1 : ℚ) ^ j * (Nat.choose d j : ℚ) * ((x - 1) - (j : ℚ)) ^ m)]
          have hmid : ∑ j ∈ Finset.range d,
              (-1 : ℚ) ^ (j + 1) * (Nat.choose (d + 1) (j + 1) : ℚ) * (x - ((j + 1 : ℕ) : ℚ)) ^ m =
              (∑ j ∈ Finset.range d,
                (-1 : ℚ) ^ (j + 1) * (Nat.choose d (j + 1) : ℚ) * (x - ((j + 1 : ℕ) : ℚ)) ^ m) -
              (∑ j ∈ Finset.range d,
                (-1 : ℚ) ^ j * (Nat.choose d j : ℚ) * ((x - 1) - (j : ℚ)) ^ m) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Nat.choose_succ_succ, Nat.cast_add, pow_succ]
            push_cast
            ring
          rw [hmid, Nat.choose_self, Nat.choose_self]
          push_cast
          rw [pow_succ]
          ring
        rw [h1]
        rw [Finset.sum_range_succ' (f := fun j => (-1 : ℚ) ^ j * (Nat.choose d j : ℚ) * (x - (j : ℚ)) ^ m)]
        simp only [Nat.choose_zero_right, pow_zero, one_mul, Nat.cast_one, Nat.cast_zero, sub_zero]
        ring
      rw [hsplit, ← Finset.sum_sub_distrib]
      -- Now `(x - j)^m - ((x - 1) - j)^m = ∑_{r < m} C(m, r) * (1 - (-1)^(m-r) ...)`:
      -- write `x - j = ((x - 1) - j) + 1`, so `((x - 1) - j + 1)^m - ((x - 1) - j)^m = ∑_{r < m} C(m, r) * ((x - 1) - j)^r`!
      have hdiff : ∀ j : ℕ,
          (x - (j : ℚ)) ^ m - ((x - 1) - (j : ℚ)) ^ m =
            ∑ r ∈ Finset.range m, (Nat.choose m r : ℚ) * ((x - 1) - (j : ℚ)) ^ r := by
        intro j
        have hadd : x - (j : ℚ) = ((x - 1) - (j : ℚ)) + 1 := by ring
        rw [hadd, add_pow, Finset.sum_range_succ]
        simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one, add_sub_cancel_right]
        refine Finset.sum_congr rfl fun r _ => by ring
      have hsum :
          ∑ j ∈ Finset.range (d + 1),
            ((-1 : ℚ) ^ j * (Nat.choose d j : ℚ) * (x - (j : ℚ)) ^ m -
             (-1 : ℚ) ^ j * (Nat.choose d j : ℚ) * ((x - 1) - (j : ℚ)) ^ m) =
          ∑ r ∈ Finset.range m, (Nat.choose m r : ℚ) *
            ∑ j ∈ Finset.range (d + 1),
              (-1 : ℚ) ^ j * (Nat.choose d j : ℚ) * ((x - 1) - (j : ℚ)) ^ r := by
        calc
          ∑ j ∈ Finset.range (d + 1),
              ((-1 : ℚ) ^ j * (Nat.choose d j : ℚ) * (x - (j : ℚ)) ^ m -
               (-1 : ℚ) ^ j * (Nat.choose d j : ℚ) * ((x - 1) - (j : ℚ)) ^ m)
            = ∑ j ∈ Finset.range (d + 1),
                (-1 : ℚ) ^ j * (Nat.choose d j : ℚ) *
                  ∑ r ∈ Finset.range m, (Nat.choose m r : ℚ) * ((x - 1) - (j : ℚ)) ^ r := by
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [← mul_sub, hdiff j]
          _ = ∑ j ∈ Finset.range (d + 1), ∑ r ∈ Finset.range m,
                (Nat.choose m r : ℚ) *
                  ((-1 : ℚ) ^ j * (Nat.choose d j : ℚ) * ((x - 1) - (j : ℚ)) ^ r) := by
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun r _ => by ring
          _ = ∑ r ∈ Finset.range m, ∑ j ∈ Finset.range (d + 1),
                (Nat.choose m r : ℚ) *
                  ((-1 : ℚ) ^ j * (Nat.choose d j : ℚ) * ((x - 1) - (j : ℚ)) ^ r) :=
                Finset.sum_comm
          _ = ∑ r ∈ Finset.range m, (Nat.choose m r : ℚ) *
                ∑ j ∈ Finset.range (d + 1),
                  (-1 : ℚ) ^ j * (Nat.choose d j : ℚ) * ((x - 1) - (j : ℚ)) ^ r := by
                refine Finset.sum_congr rfl fun r _ => by rw [← Finset.mul_sum]
      rw [hsum]
      refine Finset.sum_eq_zero fun r hr => ?_
      have hrm : r < d := by
        have := Finset.mem_range.mp hr
        omega
      rw [alternating_binom_sum_pow_eq_zero d r (x - 1) hrm, mul_zero]

/-- For `m ≥ 1`, the power series `P_m(X) = ∑_{r ≥ 1} (r * m)^m * X^(r * m)` equals `a066108Term m`. -/
private lemma a066108Term_eq_power_series (m : ℕ) (hm : 0 < m) :
    a066108Term m =
      PowerSeries.mk fun n => if n ≠ 0 ∧ m ∣ n then ((n : ℚ) ^ m) else 0 := by
  set F : PowerSeries ℚ :=
    PowerSeries.mk fun n => if n ≠ 0 ∧ m ∣ n then ((n : ℚ) ^ m) else 0
  set D : PowerSeries ℚ := (1 - PowerSeries.X ^ m) ^ (m + 1)
  have hD_const : PowerSeries.constantCoeff D = 1 := by
    simp only [D, map_pow, map_sub, map_one, PowerSeries.constantCoeff_X, zero_pow (Nat.pos_iff_ne_zero.mp hm),
      sub_zero, one_pow]
  have hD_inv : D * D⁻¹ = 1 := PowerSeries.mul_inv_cancel D (by rw [hD_const]; exact one_ne_zero)
  -- It suffices to prove `D * F = C(m^m) * ∑_{k=1}^m C(eulerian m k) * X^(k * m)`!
  have hDF : D * F =
      PowerSeries.C ((m : ℚ) ^ m) *
        ∑ k ∈ Finset.Icc 1 m, PowerSeries.C (eulerian m k) * PowerSeries.X ^ (k * m) := by
    -- Expand `D = (1 - X^m)^(m + 1) = ∑_{j=0}^{m+1} C((-1)^j * C(m+1, j)) * X^(j * m)`
    have hD_exp : D =
        ∑ j ∈ Finset.range (m + 2),
          PowerSeries.C ((-1 : ℚ) ^ j * (Nat.choose (m + 1) j : ℚ)) * PowerSeries.X ^ (j * m) := by
      have h1 : (1 - PowerSeries.X ^ m : PowerSeries ℚ) = -(PowerSeries.X ^ m) + 1 := by ring
      rw [show D = (-(PowerSeries.X ^ m) + 1) ^ (m + 1) by simp only [D, h1], add_pow]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [one_pow, mul_one, neg_pow, ← pow_mul, mul_comm m j]
      have hC : PowerSeries.C ((-1 : ℚ) ^ j * (Nat.choose (m + 1) j : ℚ)) =
          ((-1 : PowerSeries ℚ) ^ j) * ((Nat.choose (m + 1) j : ℕ) : PowerSeries ℚ) := by
        rw [map_mul, map_pow, map_neg, map_one, map_natCast]
      rw [hC]; ring
    apply PowerSeries.ext; intro n
    rw [hD_exp, Finset.sum_mul, map_sum]
    have hcoeff_lhs :
        ∑ j ∈ Finset.range (m + 2),
          PowerSeries.coeff n
            (PowerSeries.C ((-1 : ℚ) ^ j * (Nat.choose (m + 1) j : ℚ)) * PowerSeries.X ^ (j * m) * F) =
        ∑ j ∈ Finset.range (m + 2),
          (-1 : ℚ) ^ j * (Nat.choose (m + 1) j : ℚ) *
            if j * m ≤ n then PowerSeries.coeff (n - j * m) F else 0 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    rw [hcoeff_lhs]
    -- Compute RHS coefficient at `n`
    rw [PowerSeries.coeff_C_mul, map_sum]
    have hcoeff_rhs :
        (m : ℚ) ^ m * ∑ k ∈ Finset.Icc 1 m,
          PowerSeries.coeff n (PowerSeries.C (eulerian m k) * PowerSeries.X ^ (k * m)) =
        (m : ℚ) ^ m * ∑ k ∈ Finset.Icc 1 m,
          if n = k * m then eulerian m k else 0 := by
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      split_ifs <;> ring
    rw [hcoeff_rhs]
    by_cases hdiv : m ∣ n
    · obtain ⟨k, rfl⟩ := hdiv
      by_cases hk0 : k = 0
      · subst hk0
        simp only [mul_zero]
        have hl : ∑ j ∈ Finset.range (m + 2),
            (-1 : ℚ) ^ j * (Nat.choose (m + 1) j : ℚ) *
              (if j * m ≤ 0 then PowerSeries.coeff (0 - j * m) F else 0) = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          split_ifs with hle
          · have hj0 : j = 0 := by nlinarith
            subst hj0; simp [F]
          · simp
        have hr : ∑ k' ∈ Finset.Icc 1 m, (if 0 = k' * m then eulerian m k' else 0) = 0 := by
          refine Finset.sum_eq_zero fun k' hk' => ?_
          have hk1 : 1 ≤ k' := (Finset.mem_Icc.mp hk').1
          have hne : 0 ≠ k' * m := by nlinarith
          simp [hne]
        rw [hl, hr, mul_zero]
      · -- `k ≥ 1`, `n = m * k`!
        have hLHS :
            ∑ j ∈ Finset.range (m + 2),
              (-1 : ℚ) ^ j * (Nat.choose (m + 1) j : ℚ) *
                (if j * m ≤ m * k then PowerSeries.coeff (m * k - j * m) F else 0) =
            (m : ℚ) ^ m * ∑ j ∈ Finset.range (min (m + 2) (k + 1)),
              (-1 : ℚ) ^ j * ((k - j : ℕ) : ℚ) ^ m * (Nat.choose (m + 1) j : ℚ) := by
          rw [Finset.mul_sum]
          have hsub : ∀ j ∈ Finset.range (m + 2),
              (-1 : ℚ) ^ j * (Nat.choose (m + 1) j : ℚ) *
                (if j * m ≤ m * k then PowerSeries.coeff (m * k - j * m) F else 0) =
              if j < k + 1 then
                (m : ℚ) ^ m * ((-1 : ℚ) ^ j * ((k - j : ℕ) : ℚ) ^ m * (Nat.choose (m + 1) j : ℚ))
              else 0 := by
            intro j _
            by_cases hjk : j < k + 1
            · have hle : j * m ≤ m * k := by nlinarith
              have hsub_eq : m * k - j * m = m * (k - j) := by
                rw [Nat.mul_sub_left_distrib, mul_comm j m]
              simp only [hle, hjk, ↓reduceIte, hsub_eq, F, PowerSeries.coeff_mk]
              by_cases hkj : k = j
              · subst hkj
                simp [zero_pow (Nat.pos_iff_ne_zero.mp hm)]
              · have hne : m * (k - j) ≠ 0 := by
                  have : 0 < k - j := by omega
                  exact Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp hm) (Nat.pos_iff_ne_zero.mp this)
                have hd : m ∣ m * (k - j) := dvd_mul_right m (k - j)
                rw [if_pos ⟨hne, hd⟩]
                push_cast
                ring
            · have hgt : ¬ (j * m ≤ m * k) := by nlinarith
              simp [hgt, hjk]
          rw [Finset.sum_congr rfl hsub]
          rw [← Finset.sum_filter]
          have hfilt : (Finset.range (m + 2)).filter (fun j => j < k + 1) =
              Finset.range (min (m + 2) (k + 1)) := by
            ext j; simp [Finset.mem_filter, Finset.mem_range]
          rw [hfilt]
        rw [hLHS]
        by_cases hkm : k ≤ m
        · have hmin : min (m + 2) (k + 1) = k + 1 := by omega
          rw [hmin]
          have hr : ∑ k' ∈ Finset.Icc 1 m, (if m * k = k' * m then eulerian m k' else 0) =
              eulerian m k := by
            rw [Finset.sum_eq_single k]
            · simp [mul_comm]
            · intro k' _ hne
              have : m * k ≠ k' * m := by
                intro heq; apply hne
                have : k * m = k' * m := by linarith
                exact (Nat.mul_right_cancel hm this).symm
              simp [this]
            · intro h; exfalso; exact h (Finset.mem_Icc.mpr ⟨by omega, hkm⟩)
          rw [hr, eulerian]
        · have hmin : min (m + 2) (k + 1) = m + 2 := by omega
          rw [hmin]
          have hr : ∑ k' ∈ Finset.Icc 1 m, (if m * k = k' * m then eulerian m k' else 0) = 0 := by
            refine Finset.sum_eq_zero fun k' hk' => ?_
            have hk'm : k' ≤ m := (Finset.mem_Icc.mp hk').2
            have hne : m * k ≠ k' * m := by nlinarith
            simp [hne]
          rw [hr, mul_zero]
          have hzero : ∑ j ∈ Finset.range (m + 2),
              (-1 : ℚ) ^ j * ((k - j : ℕ) : ℚ) ^ m * (Nat.choose (m + 1) j : ℚ) = 0 := by
            have hconv : ∑ j ∈ Finset.range (m + 2),
                (-1 : ℚ) ^ j * ((k - j : ℕ) : ℚ) ^ m * (Nat.choose (m + 1) j : ℚ) =
                ∑ j ∈ Finset.range (m + 2),
                  (-1 : ℚ) ^ j * (Nat.choose (m + 1) j : ℚ) * ((k : ℚ) - (j : ℚ)) ^ m := by
              refine Finset.sum_congr rfl fun j hj => ?_
              have hjle : j ≤ k := by
                have := Finset.mem_range.mp hj
                omega
              rw [Nat.cast_sub hjle]; ring
            rw [hconv]
            exact alternating_binom_sum_pow_eq_zero (m + 1) m (k : ℚ) (Nat.lt_succ_self m)
          rw [hzero, mul_zero]
    · -- `¬ m ∣ n`: both sides are `0`!
      have hl : ∑ j ∈ Finset.range (m + 2),
          (-1 : ℚ) ^ j * (Nat.choose (m + 1) j : ℚ) *
            (if j * m ≤ n then PowerSeries.coeff (n - j * m) F else 0) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        split_ifs with hle
        · have hndiv : ¬ m ∣ (n - j * m) := by
            intro hd; apply hdiv
            have h1 : n = (n - j * m) + j * m := (Nat.sub_add_cancel hle).symm
            rw [h1]
            exact dvd_add hd (dvd_mul_left m j)
          simp [F, hndiv]
        · simp
      have hr : ∑ k' ∈ Finset.Icc 1 m, (if n = k' * m then eulerian m k' else 0) = 0 := by
        refine Finset.sum_eq_zero fun k' _ => ?_
        have hne : n ≠ k' * m := by
          intro heq; apply hdiv; rw [heq]; exact dvd_mul_left m k'
        simp [hne]
      rw [hl, hr, mul_zero]
  -- Multiply `hDF` by `D⁻¹` on the right!
  calc
    a066108Term m = (D * F) * D⁻¹ := by simp only [a066108Term, D, hDF]
    _ = F * (D * D⁻¹) := by ring
    _ = F := by rw [hD_inv, mul_one]

theorem main_proof :
    ∀ n M : ℕ, n ≤ M →
      PowerSeries.coeff n (∑ m ∈ Finset.Icc 1 M, a066108Term m) = (a066108 n : ℚ) := by
  intro n M hM
  rw [map_sum]
  have hsum : ∑ m ∈ Finset.Icc 1 M, PowerSeries.coeff n (a066108Term m) =
      ∑ m ∈ Finset.Icc 1 M, if n ≠ 0 ∧ m ∣ n then ((n : ℚ) ^ m) else 0 := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm_pos : 0 < m := (Finset.mem_Icc.mp hm).1
    rw [a066108Term_eq_power_series m hm_pos, PowerSeries.coeff_mk]
  rw [hsum]
  unfold a066108
  by_cases hn0 : n = 0
  · subst hn0
    simp
  · simp only [hn0, ne_eq, not_false_eq_true, true_and, ↓reduceIte, Nat.cast_sum, Nat.cast_pow]
    rw [← Finset.sum_filter]
    have hfilt : (Finset.Icc 1 M).filter (fun m => m ∣ n) = Nat.divisors n := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · intro ⟨_, hd⟩; exact ⟨hd, hn0⟩
      · intro ⟨hd, _⟩
        have hm_pos : 1 ≤ m := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn0)
        have hm_le : m ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hd
        exact ⟨⟨hm_pos, le_trans hm_le hM⟩, hd⟩
    rw [hfilt]

end OMA.S_oeis_a066108

theorem OMA.solution : type_of% @OMA.S_oeis_a066108.main :=
  OMA.S_oeis_a066108.main_proof
