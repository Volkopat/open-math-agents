import OMAStatements.S_oeis_a036837

-- Problem: A036837: Schoenheim bound L_1(n,n-5,n-6).
-- Upstream: formal-conjectures statements/oeis-a036837.lean:0 (declaration OMA.S_oeis_a036837.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: for n >= 7, 5 a(n) = C(n,5) - floor(n/5). By the definition, a(n+1) is the ceiling of
-- (n+1)/(n-4) a(n). With (n-4) C(n+1,5) = (n+1) C(n,5) one gets, for z = (C(n+1,5) - floor((n+1)/5))/5
-- (an integer by Lucas' theorem mod 5): 5((n-4) z - (n+1) a(n)) = (n+1) floor(n/5) - (n-4) floor((n+1)/5),
-- which is 0 or 5 floor(n/5), so it lies in [0, 5(n-4)) and the ceiling is z. Then
-- 120 C(n,5) = n(n-1)(n-2)(n-3)(n-4) and floor((n+5)/5) = floor(n/5) + 1 make the coefficients of
-- x^m, m >= 17, of the product with (1-x^5)(1-x)^5 vanish; those below x^17 come from a(7..16).

namespace P1A036837

open OMA.S_oeis_a036837

/-- A series times a finite sum of monomials, coefficient by coefficient. -/
theorem gf_poly (f c e : ℕ → ℚ) (d D : ℕ)
    (h : ∀ m, (∑ j ∈ Finset.range d, if j ≤ m then c j * f (m - j) else 0) =
      if m < D then e m else 0) :
    PowerSeries.mk f * (∑ j ∈ Finset.range d, PowerSeries.C (c j) * PowerSeries.X ^ j) =
      ∑ j ∈ Finset.range D, PowerSeries.C (e j) * PowerSeries.X ^ j := by
  ext m
  have hl : ∀ j, PowerSeries.coeff m (PowerSeries.mk f * (PowerSeries.C (c j) * PowerSeries.X ^ j)) =
      if j ≤ m then c j * f (m - j) else 0 := by
    intro j
    rw [mul_left_comm, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow']
    by_cases hj : j ≤ m
    · rw [if_pos hj, if_pos hj, PowerSeries.coeff_mk]
    · rw [if_neg hj, if_neg hj, mul_zero]
  have hr : ∀ j, PowerSeries.coeff m (PowerSeries.C (e j) * PowerSeries.X ^ j) =
      if m = j then e j else 0 := fun j => PowerSeries.coeff_C_mul_X_pow (e j) j m
  rw [Finset.mul_sum, map_sum, map_sum, Finset.sum_congr rfl (fun j _ => hl j),
    Finset.sum_congr rfl (fun j _ => hr j), h m, Finset.sum_ite_eq]
  simp only [Finset.mem_range]

/-- Coefficients of (x^4+x^3+x^2+x+1)(x-1)^6 = (1-x^5)(1-x)^5. -/
def cd : ℕ → ℚ
  | 0 => 1
  | 1 => -5
  | 2 => 10
  | 3 => -10
  | 4 => 5
  | 5 => -2
  | 6 => 5
  | 7 => -10
  | 8 => 10
  | 9 => -5
  | 10 => 1
  | _ => 0

/-- Coefficients of the numerator x^7(4-9x+10x^2-5x^3+2x^4-5x^5+10x^6-10x^7+5x^8-x^9). -/
def cn : ℕ → ℚ
  | 7 => 4
  | 8 => -9
  | 9 => 10
  | 10 => -5
  | 11 => 2
  | 12 => -5
  | 13 => 10
  | 14 => -10
  | 15 => 5
  | 16 => -1
  | _ => 0

theorem cd0 : cd 0 = 1 := rfl
theorem cd1 : cd 1 = -5 := rfl
theorem cd2 : cd 2 = 10 := rfl
theorem cd3 : cd 3 = -10 := rfl
theorem cd4 : cd 4 = 5 := rfl
theorem cd5 : cd 5 = -2 := rfl
theorem cd6 : cd 6 = 5 := rfl
theorem cd7 : cd 7 = -10 := rfl
theorem cd8 : cd 8 = 10 := rfl
theorem cd9 : cd 9 = -5 := rfl
theorem cd10 : cd 10 = 1 := rfl

theorem cn0 : cn 0 = 0 := rfl
theorem cn1 : cn 1 = 0 := rfl
theorem cn2 : cn 2 = 0 := rfl
theorem cn3 : cn 3 = 0 := rfl
theorem cn4 : cn 4 = 0 := rfl
theorem cn5 : cn 5 = 0 := rfl
theorem cn6 : cn 6 = 0 := rfl
theorem cn7 : cn 7 = 4 := rfl
theorem cn8 : cn 8 = -9 := rfl
theorem cn9 : cn 9 = 10 := rfl
theorem cn10 : cn 10 = -5 := rfl
theorem cn11 : cn 11 = 2 := rfl
theorem cn12 : cn 12 = -5 := rfl
theorem cn13 : cn 13 = 10 := rfl
theorem cn14 : cn 14 = -10 := rfl
theorem cn15 : cn 15 = 5 := rfl
theorem cn16 : cn 16 = -1 := rfl

theorem hden : ((PowerSeries.X ^ 4 + PowerSeries.X ^ 3 + PowerSeries.X ^ 2 + PowerSeries.X + 1) *
      (PowerSeries.X - 1) ^ 6 : PowerSeries ℚ) =
    ∑ j ∈ Finset.range 11, PowerSeries.C (cd j) * PowerSeries.X ^ j := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, cd0, cd1, cd2, cd3, cd4, cd5, cd6, cd7, cd8, cd9, cd10]
  simp only [map_neg, map_one]
  rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5,
    map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10,
    map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
  ring

theorem hnum : (PowerSeries.X ^ 7 * (4 - PowerSeries.X ^ 9 + 5 * PowerSeries.X ^ 8 -
      10 * PowerSeries.X ^ 7 + 10 * PowerSeries.X ^ 6 - 5 * PowerSeries.X ^ 5 +
      2 * PowerSeries.X ^ 4 - 5 * PowerSeries.X ^ 3 + 10 * PowerSeries.X ^ 2 -
      9 * PowerSeries.X) : PowerSeries ℚ) =
    ∑ j ∈ Finset.range 17, PowerSeries.C (cn j) * PowerSeries.X ^ j := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, cn0, cn1, cn2, cn3, cn4, cn5, cn6,
    cn7, cn8, cn9, cn10, cn11, cn12, cn13, cn14, cn15, cn16]
  simp only [map_neg, map_one, map_zero, zero_mul, zero_add]
  rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4,
    map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 9,
    map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10,
    map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5,
    map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
  ring

/-- (n-4) C(n+1,5) = (n+1) C(n,5). -/
theorem chQ (n : ℕ) (hn : 4 ≤ n) :
    ((n.choose 5 : ℕ) : ℚ) * ((n : ℚ) + 1) = (((n + 1).choose 5 : ℕ) : ℚ) * ((n : ℚ) - 4) := by
  have h := Nat.choose_mul_succ_eq n 5
  rw [show n + 1 - 5 = n - 4 by omega] at h
  have h' := congrArg (fun x : ℕ => (x : ℚ)) h
  push_cast [Nat.cast_sub hn] at h'
  linear_combination h'

/-- 120 C(n,5) = n(n-1)(n-2)(n-3)(n-4). -/
theorem prodQ (n : ℕ) (hn : 5 ≤ n) :
    ((n.choose 5 : ℕ) : ℚ) * 120 =
      (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) * ((n : ℚ) - 4) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [Nat.choose_self]
  | succ k hk ih =>
    have hc := chQ k (by omega)
    have hK : (5 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
    have hpos : (0 : ℚ) < (k : ℚ) - 4 := by linarith
    apply mul_right_cancel₀ hpos.ne'
    push_cast
    linear_combination (-120 : ℚ) * hc + ((k : ℚ) + 1) * ih

/-- Lucas mod 5: C(n,5) = floor(n/5) mod 5. -/
theorem luc (n : ℕ) : (5 : ℤ) ∣ ((n.choose 5 : ℕ) : ℤ) - ((n / 5 : ℕ) : ℤ) := by
  have hp : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := 5) (p := 5)
  rw [Nat.mod_self, Nat.div_self (by norm_num : 0 < 5), Nat.choose_zero_right,
    Nat.choose_one_right, one_mul] at h
  have h2 := Nat.modEq_iff_dvd.mp h.symm
  exact_mod_cast h2

/-- The defining step: a(n+1) = ceiling((n+1)/(n-4) a(n)) for n >= 7. -/
theorem step (n : ℕ) (hn : 7 ≤ n) :
    a (n + 1) = ⌈((n : ℚ) + 1) / ((n : ℚ) - 4) * (a n : ℚ)⌉ := by
  have e1 : n + 1 - 6 = (n - 6) + 1 := by omega
  have e2 : n + 1 - 5 = n - 4 := by omega
  have e3 : n - 4 - 1 = n - 5 := by omega
  have e4 : ((n - 4 : ℕ) : ℚ) = (n : ℚ) - 4 := by
    rw [Nat.cast_sub (by omega : 4 ≤ n), Nat.cast_ofNat]
  show L (n + 1) (n + 1 - 5) (n + 1 - 6) =
    ⌈((n : ℚ) + 1) / ((n : ℚ) - 4) * (L n (n - 5) (n - 6) : ℚ)⌉
  rw [e1, e2, L.eq_2, e3, Nat.add_sub_cancel, e4, Nat.cast_add_one]

/-- The closed form 5 a(n) = C(n,5) - floor(n/5) for n >= 7. -/
theorem closed (n : ℕ) (hn : 7 ≤ n) :
    5 * a n = ((n.choose 5 : ℕ) : ℤ) - ((n / 5 : ℕ) : ℤ) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h7 : a 7 = 4 := by
      show L 7 (7 - 5) (7 - 6) = 4
      rw [show (7 : ℕ) - 6 = 0 + 1 from rfl, L.eq_2, L.eq_1, Int.ceil_eq_iff]
      norm_num
    have hc : Nat.choose 7 5 = 21 := by decide
    rw [h7, hc]
    norm_num
  | succ k hk ih =>
    obtain ⟨z, hz⟩ := luc (k + 1)
    have hK : (7 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
    have hpos : (0 : ℚ) < (k : ℚ) - 4 := by linarith
    have hA : 5 * (a k : ℚ) = ((k.choose 5 : ℕ) : ℚ) - ((k / 5 : ℕ) : ℚ) := by exact_mod_cast ih
    have hZ : (((k + 1).choose 5 : ℕ) : ℚ) - (((k + 1) / 5 : ℕ) : ℚ) = 5 * (z : ℚ) := by
      exact_mod_cast hz
    have hc := chQ k (by omega)
    obtain ⟨W, hWd⟩ : ∃ W : ℚ, W = ((k : ℚ) - 4) * (z : ℚ) - ((k : ℚ) + 1) * (a k : ℚ) :=
      ⟨_, rfl⟩
    have hW : 5 * W = ((k : ℚ) + 1) * ((k / 5 : ℕ) : ℚ) - ((k : ℚ) - 4) * (((k + 1) / 5 : ℕ) : ℚ) := by
      rw [hWd]
      linear_combination (-((k : ℚ) - 4)) * hZ - ((k : ℚ) + 1) * hA - hc
    have hq : ((k + 1) / 5 = k / 5 + 1 ∧ k = 5 * (k / 5) + 4) ∨
        ((k + 1) / 5 = k / 5 ∧ 5 * (k / 5) ≤ k) := by omega
    have hD : 0 ≤ ((k : ℚ) + 1) * ((k / 5 : ℕ) : ℚ) - ((k : ℚ) - 4) * (((k + 1) / 5 : ℕ) : ℚ) ∧
        ((k : ℚ) + 1) * ((k / 5 : ℕ) : ℚ) - ((k : ℚ) - 4) * (((k + 1) / 5 : ℕ) : ℚ) <
          5 * ((k : ℚ) - 4) := by
      rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1]
        have h2' : (k : ℚ) = 5 * ((k / 5 : ℕ) : ℚ) + 4 := by exact_mod_cast h2
        have e : ((k : ℚ) + 1) * ((k / 5 : ℕ) : ℚ) - ((k : ℚ) - 4) * ((k / 5 + 1 : ℕ) : ℚ) = 0 := by
          push_cast
          linear_combination (-1 : ℚ) * h2'
        rw [e]
        constructor
        · exact le_refl 0
        · linarith
      · rw [h1]
        have h2' : 5 * ((k / 5 : ℕ) : ℚ) ≤ (k : ℚ) := by exact_mod_cast h2
        have e : ((k : ℚ) + 1) * ((k / 5 : ℕ) : ℚ) - ((k : ℚ) - 4) * ((k / 5 : ℕ) : ℚ) =
            5 * ((k / 5 : ℕ) : ℚ) := by ring
        rw [e]
        have hq0 : (0 : ℚ) ≤ ((k / 5 : ℕ) : ℚ) := Nat.cast_nonneg _
        constructor
        · linarith
        · linarith
    have hW0 : 0 ≤ W := by linarith [hD.1]
    have hW1 : W < (k : ℚ) - 4 := by linarith [hD.2]
    rw [step k hk]
    have hceil : ⌈((k : ℚ) + 1) / ((k : ℚ) - 4) * (a k : ℚ)⌉ = z := by
      rw [Int.ceil_eq_iff]
      constructor
      · rw [div_mul_eq_mul_div, lt_div_iff₀ hpos]
        have e : ((z : ℚ) - 1) * ((k : ℚ) - 4) = ((k : ℚ) + 1) * (a k : ℚ) + W - ((k : ℚ) - 4) := by
          rw [hWd]
          ring
        rw [e]
        linarith
      · rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
        have e : (z : ℚ) * ((k : ℚ) - 4) = ((k : ℚ) + 1) * (a k : ℚ) + W := by
          rw [hWd]
          ring
        rw [e]
        linarith
    rw [hceil]
    exact hz.symm

/-- The closed form as a rational function of n. -/
def G (n : ℕ) : ℚ :=
  ((n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) * ((n : ℚ) - 4) / 120 -
    ((n / 5 : ℕ) : ℚ)) / 5

theorem aF (n : ℕ) (hn : 7 ≤ n) : (a n : ℚ) = G n := by
  have h1 := closed n hn
  have h2 := prodQ n (by omega)
  have h1' : 5 * (a n : ℚ) = ((n.choose 5 : ℕ) : ℚ) - ((n / 5 : ℕ) : ℚ) := by exact_mod_cast h1
  unfold G
  linear_combination h1' / 5 + h2 / 600

theorem v7 : (a 7 : ℚ) = 4 := by rw [aF 7 (by norm_num)]; unfold G; norm_num
theorem v8 : (a 8 : ℚ) = 11 := by rw [aF 8 (by norm_num)]; unfold G; norm_num
theorem v9 : (a 9 : ℚ) = 25 := by rw [aF 9 (by norm_num)]; unfold G; norm_num
theorem v10 : (a 10 : ℚ) = 50 := by rw [aF 10 (by norm_num)]; unfold G; norm_num
theorem v11 : (a 11 : ℚ) = 92 := by rw [aF 11 (by norm_num)]; unfold G; norm_num
theorem v12 : (a 12 : ℚ) = 158 := by rw [aF 12 (by norm_num)]; unfold G; norm_num
theorem v13 : (a 13 : ℚ) = 257 := by rw [aF 13 (by norm_num)]; unfold G; norm_num
theorem v14 : (a 14 : ℚ) = 400 := by rw [aF 14 (by norm_num)]; unfold G; norm_num
theorem v15 : (a 15 : ℚ) = 600 := by rw [aF 15 (by norm_num)]; unfold G; norm_num
theorem v16 : (a 16 : ℚ) = 873 := by rw [aF 16 (by norm_num)]; unfold G; norm_num

/-- The coefficients of x^(k+17) vanish. -/
theorem high (k : ℕ) :
    (∑ j ∈ Finset.range 11, if j ≤ k + 17 then
      cd j * (if 7 ≤ k + 17 - j then (a (k + 17 - j) : ℚ) else 0) else 0) = 0 := by
  have hs : ∀ j ∈ Finset.range 11, (if j ≤ k + 17 then
      cd j * (if 7 ≤ k + 17 - j then (a (k + 17 - j) : ℚ) else 0) else 0) =
      cd j * G (k + 17 - j) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [if_pos (show j ≤ k + 17 by omega), if_pos (show 7 ≤ k + 17 - j by omega),
      aF (k + 17 - j) (by omega)]
  rw [Finset.sum_congr rfl hs]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add]
  rw [show k + 17 - 0 = k + 17 by omega, show k + 17 - 1 = k + 16 by omega,
    show k + 17 - 2 = k + 15 by omega, show k + 17 - 3 = k + 14 by omega,
    show k + 17 - 4 = k + 13 by omega, show k + 17 - 5 = k + 12 by omega,
    show k + 17 - 6 = k + 11 by omega, show k + 17 - 7 = k + 10 by omega,
    show k + 17 - 8 = k + 9 by omega, show k + 17 - 9 = k + 8 by omega,
    show k + 17 - 10 = k + 7 by omega]
  unfold G
  rw [show (k + 17) / 5 = (k + 12) / 5 + 1 by omega, show (k + 16) / 5 = (k + 11) / 5 + 1 by omega,
    show (k + 15) / 5 = (k + 10) / 5 + 1 by omega, show (k + 14) / 5 = (k + 9) / 5 + 1 by omega,
    show (k + 13) / 5 = (k + 8) / 5 + 1 by omega, show (k + 12) / 5 = (k + 7) / 5 + 1 by omega]
  rw [cd0, cd1, cd2, cd3, cd4, cd5, cd6, cd7, cd8, cd9, cd10]
  push_cast
  ring

end P1A036837

open OMA.S_oeis_a036837 P1A036837 in
theorem OMA.solution : type_of% @OMA.S_oeis_a036837.main := by
  rw [hden, hnum]
  refine gf_poly (fun n => if 7 ≤ n then (a n : ℚ) else 0) cd cn 11 17 ?_
  intro m
  rcases Nat.lt_or_ge m 17 with hm | hm
  · interval_cases m <;>
      norm_num [Finset.sum_range_succ, cd0, cd1, cd2, cd3, cd4, cd5, cd6, cd7, cd8, cd9, cd10,
        cn0, cn1, cn2, cn3, cn4, cn5, cn6, cn7, cn8, cn9, cn10, cn11, cn12, cn13, cn14, cn15, cn16,
        v7, v8, v9, v10, v11, v12, v13, v14, v15, v16]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 17 := ⟨m - 17, by omega⟩
    rw [if_neg (show ¬ (k + 17 < 17) by omega)]
    exact high k
