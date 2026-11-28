import OMAStatements.S_oeis_a047872

/-!
# The Bernoulli floor identity in OEIS A047872

The proof combines Euler's even-zeta formula, an exact finite check and
Beukers' positive double-integral linear forms in ζ(2). An explicit proof
of the required lcm growth bound supplies the effective cutoff at n = 2048.

* Bill McEachen's conjecture: https://oeis.org/A047872
* F. Beukers, A note on the irrationality of ζ(2) and ζ(3), 1979.
  https://doi.org/10.1112/blms/11.3.268
* D. Hanson, On the product of the primes, 1972.
  https://doi.org/10.4153/CMB-1972-007-7
-/

section

/-! Exact analytic reduction of the approved OEIS A047872 statement.
The proofs use mathlib's even-zeta values and never invoke the conjecture itself. -/

namespace A047872Certificate

noncomputable def evenZeta (n : ℕ) : ℝ := ∑' j : ℕ, 1 / (j : ℝ) ^ (2 * n)

noncomputable def center (n : ℕ) : ℝ :=
  ((n + 1) * (2 * n + 1) : ℝ) / (2 * Real.pi ^ 2)

lemma evenZeta_pos {n : ℕ} (hn : n ≠ 0) : 0 < evenZeta n := by
  exact (hasSum_zeta_nat hn).summable.tsum_pos (fun _ => by positivity) 1 (by norm_num)

lemma abs_bernoulli_eq {n : ℕ} (hn : n ≠ 0) :
    |(bernoulli (2 * n) : ℝ)| = evenZeta n * (Nat.factorial (2 * n) : ℝ) /
      (2 ^ (2 * n - 1) * Real.pi ^ (2 * n)) := by
  have hz := congrArg abs (hasSum_zeta_nat hn).tsum_eq
  change |evenZeta n| = _ at hz
  simp [abs_mul, abs_div, abs_pow, abs_of_pos Real.pi_pos, abs_of_pos (evenZeta_pos hn)] at hz
  apply (eq_div_iff (by positivity)).2
  have hf : (Nat.factorial (2 * n) : ℝ) ≠ 0 := by positivity
  field_simp [hf] at hz
  linarith only [hz]

lemma floor_eq_of_separation {v d b ε : ℝ} (hd : 0 < d)
    (hdown : 0 ≤ v - d * b) (herror : v - d * b < ε)
    (hsep : ∀ m : ℤ, 0 ≤ v - d * m → ε ≤ v - d * m) :
    ⌊b⌋ = ⌊v / d⌋ := by
  have hlow := (le_div_iff₀ hd).mp (Int.floor_le (v / d))
  have hgap := hsep ⌊v / d⌋ (by linarith)
  apply Int.floor_eq_iff.mpr
  constructor
  · exact le_of_not_gt fun h => by nlinarith [mul_pos (sub_pos.mpr h) hd]
  · exact lt_of_le_of_lt ((le_div_iff₀ hd).mpr (by linarith)) (Int.lt_floor_add_one _)

lemma evenZeta_succ_le {n : ℕ} (hn : n ≠ 0) : evenZeta (n + 1) ≤ evenZeta n := by
  apply (hasSum_zeta_nat (Nat.succ_ne_zero n)).summable.tsum_le_tsum _
    (hasSum_zeta_nat hn).summable
  intro j
  cases j with
  | zero => simp [show 2 * n ≠ 0 by omega, show 2 * (n + 1) ≠ 0 by omega]
  | succ j =>
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by exact_mod_cast Nat.le_add_left 1 j) (by omega)

lemma bernoulli_ratio {n : ℕ} (hn : n ≠ 0) :
    |(bernoulli (2 * n + 2) : ℝ) / (bernoulli (2 * n) : ℝ)| =
      center n * (evenZeta (n + 1) / evenZeta n) := by
  rw [abs_div, show 2 * n + 2 = 2 * (n + 1) by omega,
    abs_bernoulli_eq (Nat.succ_ne_zero n), abs_bernoulli_eq hn]
  rw [show 2 * (n + 1) - 1 = (2 * n - 1) + 2 by omega,
    show 2 * (n + 1) = 2 * n + 2 by omega]
  simp only [center, pow_add, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  have hf : (Nat.factorial (2 * n) : ℝ) ≠ 0 := by positivity
  field_simp [hf, ne_of_gt (evenZeta_pos hn), Real.pi_ne_zero]
  push_cast
  ring

theorem at_zero : OMA.S_oeis_a047872.a 0 = ⌊center 0⌋ := by
  have hp := Real.pi_gt_three
  have hr : ⌊center 0⌋ = 0 := by
    apply Int.floor_eq_zero_iff.mpr
    simp only [center, Nat.cast_zero, zero_add, mul_zero, one_mul, Set.mem_Ico]
    constructor
    · positivity
    · apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi ^ 2)).mpr
      nlinarith [sq_nonneg (Real.pi - 3)]
  rw [hr]
  norm_num [OMA.S_oeis_a047872.a]

theorem target_of_bounds {n : ℕ} (hn : n ≠ 0) (ε : ℝ)
    (herror : ((n + 1) * (2 * n + 1) : ℝ) * (evenZeta n - evenZeta (n + 1)) / evenZeta n < ε)
    (hsep : ∀ m : ℤ, 0 ≤ ((n + 1) * (2 * n + 1) : ℝ) - (2 * Real.pi ^ 2) * m →
      ε ≤ ((n + 1) * (2 * n + 1) : ℝ) - (2 * Real.pi ^ 2) * m) :
    OMA.S_oeis_a047872.a n = ⌊center n⌋ := by
  unfold OMA.S_oeis_a047872.a
  rw [← Rat.floor_cast (α := ℝ), Rat.cast_abs, Rat.cast_div, bernoulli_ratio hn]
  have hz := evenZeta_pos hn
  have hident : ((n + 1) * (2 * n + 1) : ℝ) - (2 * Real.pi ^ 2) *
      (center n * (evenZeta (n + 1) / evenZeta n)) =
      ((n + 1) * (2 * n + 1) : ℝ) * (evenZeta n - evenZeta (n + 1)) / evenZeta n := by
    unfold center
    field_simp [Real.pi_ne_zero, hz.ne']
  apply floor_eq_of_separation (by positivity : 0 < 2 * Real.pi ^ 2) _ _ hsep
  · rw [hident]
    have := sub_nonneg.mpr (evenZeta_succ_le hn)
    positivity
  · rwa [hident]

lemma one_le_evenZeta {n : ℕ} (hn : n ≠ 0) : 1 ≤ evenZeta n := by
  simpa [evenZeta] using (hasSum_zeta_nat hn).summable.le_tsum 1 (fun _ _ => by positivity)

lemma scaled_zeta_difference_lt_two {n : ℕ} (hn : n ≠ 0) :
    (4 : ℝ) ^ (n - 1) * (evenZeta n - evenZeta (n + 1)) < 2 := by
  have hs {k : ℕ} (hk : k ≠ 0) : HasSum (fun j : ℕ => 1 / (j : ℝ) ^ (2 * k)) (evenZeta k) :=
    (hasSum_zeta_nat hk).summable.hasSum
  have hpi : Real.pi ^ 2 < (3.15 : ℝ) ^ 2 := by gcongr; exact Real.pi_lt_d2
  refine lt_of_le_of_lt (hasSum_le ?_ (((hs hn).sub (hs (Nat.succ_ne_zero n))).mul_left _)
    hasSum_zeta_two) (by linarith)
  intro j
  by_cases hj : j < 2
  · interval_cases j <;> simp [show 2 * n ≠ 0 by omega, show 2 * (n + 1) ≠ 0 by omega]
  · have hj' : (2 : ℝ) ≤ j := by exact_mod_cast (show 2 ≤ j by omega)
    have hjpos : (0 : ℝ) < j := by linarith
    have hbase : 4 ≤ (j : ℝ) ^ 2 := by nlinarith [sq_nonneg ((j : ℝ) - 2)]
    calc
      _ ≤ 4 ^ (n - 1) * (1 / (j : ℝ) ^ (2 * n)) :=
        mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by positivity)
      _ ≤ 1 / (j : ℝ) ^ 2 := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul,
          show 2 * n = 2 * (n - 1) + 2 by omega, pow_add, pow_mul]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hbase _) (by positivity)

theorem target_of_separation {n : ℕ} (hn : n ≠ 0)
    (hsep : ∀ m : ℤ, 0 ≤ ((n + 1) * (2 * n + 1) : ℝ) - (2 * Real.pi ^ 2) * m →
      2 * ((n + 1) * (2 * n + 1) : ℝ) / 4 ^ (n - 1) ≤
        ((n + 1) * (2 * n + 1) : ℝ) - (2 * Real.pi ^ 2) * m) :
    OMA.S_oeis_a047872.a n = ⌊center n⌋ := by
  apply target_of_bounds hn _ _ hsep
  have hz := one_le_evenZeta hn
  have hgap := scaled_zeta_difference_lt_two hn
  have hpos : 0 < ((n + 1) * (2 * n + 1) : ℝ) := by positivity
  apply (div_lt_div_iff₀ (evenZeta_pos hn) (by positivity)).mpr
  nlinarith [mul_lt_mul_of_pos_left hgap hpos, mul_le_mul_of_nonneg_left hz (le_of_lt hpos)]

/-- It suffices to separate the multiples of ζ(2) with positive denominator at most
`(n+1)(2n+1)`. The second hypothesis has exactly the shape of the Beukers bound. -/
theorem target_of_large_gap {n : ℕ} (hn : n ≠ 0)
    (htail : (4 : ℝ) ^ n * (evenZeta n - 1) < 3)
    (hgap : ∀ q : ℤ, 1 ≤ q → q ≤ ((n + 1) * (2 * n + 1) : ℕ) →
      3 * (((n + 1) * (2 * n + 1) : ℕ) : ℝ) / 4 ^ n <
        |(q : ℝ) * (Real.pi ^ 2 / 6) - (((n + 1) * (2 * n + 1) : ℕ) : ℝ)|) :
    OMA.S_oeis_a047872.a n = ⌊center n⌋ := by
  let v : ℕ := (n + 1) * (2 * n + 1)
  have hv : (v : ℝ) = ((n + 1) * (2 * n + 1) : ℝ) := by simp [v]
  have hvpos : 0 < (v : ℝ) := by rw [hv]; positivity
  have hfour : (3 : ℝ) ≤ 4 ^ n :=
    le_trans (by norm_num : (3 : ℝ) ≤ 4 ^ 1) (pow_le_pow_right₀ (by norm_num) (by omega))
  apply target_of_bounds hn (3 * (v : ℝ) / 4 ^ n)
  · rw [← hv]
    have hz := one_le_evenZeta hn
    have hz' := one_le_evenZeta (Nat.succ_ne_zero n)
    have herr : 4 ^ n * (evenZeta n - evenZeta (n + 1)) < (3 : ℝ) :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) htail
    apply (div_lt_div_iff₀ (evenZeta_pos hn) (by positivity)).mpr
    nlinarith only [mul_lt_mul_of_pos_left herr hvpos, mul_le_mul_of_nonneg_left hz hvpos.le]
  · intro m hlow
    rw [← hv] at hlow ⊢
    by_cases hm : 0 < m
    · have hm' : 0 ≤ (m : ℝ) := by exact_mod_cast hm.le
      have hd : (12 : ℝ) ≤ 2 * Real.pi ^ 2 := by
        nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]
      have hq : (12 * m : ℤ) ≤ v := by
        have : (12 : ℝ) * m ≤ v := by
          linarith only [hlow, mul_le_mul_of_nonneg_right hd hm']
        exact_mod_cast this
      have hg := hgap (12 * m) (by omega) hq
      change 3 * (v : ℝ) / 4 ^ n < |((12 * m : ℤ) : ℝ) * (Real.pi ^ 2 / 6) - (v : ℝ)| at hg
      rw [show ((12 * m : ℤ) : ℝ) * (Real.pi ^ 2 / 6) - (v : ℝ) =
        -((v : ℝ) - (2 * Real.pi ^ 2) * m) by push_cast; ring, abs_neg, abs_of_nonneg hlow] at hg
      exact hg.le
    · have hm' : (m : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_gt hm)
      have hprod := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2 * Real.pi ^ 2) hm'
      apply le_trans _ (by linarith only [hprod] : (v : ℝ) ≤ v - (2 * Real.pi ^ 2) * m)
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hfour hvpos.le]

end A047872Certificate

end

section

namespace A047872.FiniteMargin

private def scale : ℕ := 10 ^ 20
private def lo : ℕ := 314159265358979323846
private def hi : ℕ := 314159265358979323847
private def v (n : ℕ) : ℕ := (n + 1) * (2 * n + 1)
private def d (n : ℕ) : ℕ := 4 ^ min n 20
private def witness (n : ℕ) : ℕ := v n * scale ^ 2 / (2 * lo ^ 2)

private def good (n : ℕ) : Bool :=
  decide (witness n * (2 * hi ^ 2) * (d n + 3) ≤ v n * scale ^ 2 * d n ∧
    v n * scale ^ 2 < (witness n + 1) * (2 * lo ^ 2))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem all_good : (List.range 2048).all good = true := by decide

private theorem good_at {n : ℕ} (hn : n < 2048) :
    witness n * (2 * hi ^ 2) * (d n + 3) ≤ v n * scale ^ 2 * d n ∧
      v n * scale ^ 2 < (witness n + 1) * (2 * lo ^ 2) := by
  have h := List.all_eq_true.mp all_good n (List.mem_range.mpr hn)
  simpa [good] using h

/-- The real number on the conjecture's right-hand side. -/
noncomputable def target (n : ℕ) : ℝ := (↑n + 1) * (2 * ↑n + 1) / (2 * Real.pi ^ 2)

/-- Even after multiplying by `4^n/(4^n+3)`, the target stays in the same unit interval. -/
theorem window {n : ℕ} (hn : n < 2048) :
    ∃ k : ℕ, (k : ℝ) ≤ target n * ((4 : ℝ) ^ n / (4 ^ n + 3)) ∧
      target n < (k : ℝ) + 1 := by
  obtain ⟨lower, upper⟩ := good_at hn
  have lowR : (witness n : ℝ) * (2 * (hi : ℝ) ^ 2) * ((d n : ℝ) + 3) ≤
      (v n : ℝ) * (scale : ℝ) ^ 2 * (d n : ℝ) := by exact_mod_cast lower
  have upR : (v n : ℝ) * (scale : ℝ) ^ 2 <
      ((witness n : ℝ) + 1) * (2 * (lo : ℝ) ^ 2) := by exact_mod_cast upper
  have hS : (0 : ℝ) < scale := by norm_num [scale]
  have hL : (0 : ℝ) < lo := by norm_num [lo]
  have hH : (0 : ℝ) < hi := by norm_num [hi]
  have pi_lo : (lo : ℝ) / scale ≤ Real.pi := by
    rw [show (lo : ℝ) / scale = 3.14159265358979323846 by norm_num [lo, scale]]
    exact Real.pi_gt_d20.le
  have pi_hi : Real.pi ≤ (hi : ℝ) / scale := by
    rw [show (hi : ℝ) / scale = 3.14159265358979323847 by norm_num [hi, scale]]
    exact Real.pi_lt_d20.le
  have hd : (d n : ℝ) ≤ (4 : ℝ) ^ n := by
    simp only [d, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) (min_le_left _ _)
  have hv : target n = (v n : ℝ) / (2 * Real.pi ^ 2) := by simp [target, v]
  refine ⟨witness n, ?_, ?_⟩
  · calc
      (witness n : ℝ) ≤ (v n : ℝ) / (2 * ((hi : ℝ) / scale) ^ 2) *
          ((d n : ℝ) / ((d n : ℝ) + 3)) := by
        field_simp
        nlinarith only [lowR]
      _ ≤ target n * ((d n : ℝ) / ((d n : ℝ) + 3)) := by
        rw [hv]
        gcongr
      _ ≤ target n * ((4 : ℝ) ^ n / (4 ^ n + 3)) := by
        have ht : 0 ≤ target n := by rw [hv]; positivity
        apply mul_le_mul_of_nonneg_left _ ht
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith only [hd]
  · calc
      target n ≤ (v n : ℝ) / (2 * ((lo : ℝ) / scale) ^ 2) := by
        rw [hv]
        gcongr
      _ < (witness n : ℝ) + 1 := by
        field_simp
        nlinarith only [upR]

/-- Any real number in the interval from the conservative lower bound through the target
has the same floor as the target. -/
theorem floor_stable {n : ℕ} (hn : n < 2048) {y : ℝ}
    (hlo : target n * ((4 : ℝ) ^ n / (4 ^ n + 3)) ≤ y) (hhi : y ≤ target n) :
    ⌊y⌋ = ⌊target n⌋ := by
  obtain ⟨k, hk, ht⟩ := window hn
  have hy : ⌊y⌋ = (k : ℤ) := Int.floor_eq_iff.mpr ⟨by exact_mod_cast hk.trans hlo,
    by exact_mod_cast hhi.trans_lt ht⟩
  have hx : ⌊target n⌋ = (k : ℤ) := Int.floor_eq_iff.mpr ⟨by exact_mod_cast (hk.trans hlo).trans hhi,
    by exact_mod_cast ht⟩
  exact hy.trans hx.symm

end A047872.FiniteMargin

end

section

namespace A047872Certificate

/-- Compare the tail from (j=2) term by term with the tail of the Basel series. -/
theorem scaled_zeta_tail_lt_three {n : ℕ} (hn : n ≠ 0) :
    (4 : ℝ) ^ n * (evenZeta n - 1) < 3 := by
  have hs : HasSum (fun j : ℕ => 1 / (j : ℝ) ^ (2 * n)) (evenZeta n) :=
    (hasSum_zeta_nat hn).summable.hasSum
  have hsingle : HasSum (fun j : ℕ => if j = 1 then (1 : ℝ) else 0) 1 :=
    hasSum_ite_eq _ _
  have htail : (4 : ℝ) ^ (n - 1) * (evenZeta n - 1) ≤ Real.pi ^ 2 / 6 - 1 := by
    apply hasSum_le _ ((hs.sub hsingle).mul_left _) (hasSum_zeta_two.sub hsingle)
    intro j
    by_cases hj : j < 2
    · interval_cases j <;> simp [show 2 * n ≠ 0 by omega]
    · have hj' : (2 : ℝ) ≤ j := by exact_mod_cast (show 2 ≤ j by omega)
      have hjpos : (0 : ℝ) < j := by linarith
      have hbase : 4 ≤ (j : ℝ) ^ 2 := by nlinarith [sq_nonneg ((j : ℝ) - 2)]
      simp only [if_neg (show j ≠ 1 by omega), sub_zero]
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul,
        show 2 * n = 2 * (n - 1) + 2 by omega, pow_add, pow_mul]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hbase _) (by positivity)
  have hpow : (4 : ℝ) ^ n = 4 ^ (n - 1) * 4 := by
    calc (4 : ℝ) ^ n = 4 ^ (n - 1 + 1) := by congr 1; omega
         _ = _ := pow_succ _ _
  have hpi : Real.pi ^ 2 < (3.15 : ℝ) ^ 2 := by gcongr; exact Real.pi_lt_d2
  rw [hpow]
  linarith

theorem zeta_ratio_lower {n : ℕ} (hn : n ≠ 0) :
    (4 : ℝ) ^ n / (4 ^ n + 3) ≤ evenZeta (n + 1) / evenZeta n := by
  apply (div_le_div_iff₀ (by positivity) (evenZeta_pos hn)).mpr
  have htail := scaled_zeta_tail_lt_three hn
  have hnext := one_le_evenZeta (Nat.succ_ne_zero n)
  nlinarith only [htail, mul_le_mul_of_nonneg_right hnext
    (by positivity : 0 ≤ (4 : ℝ) ^ n + 3)]

/-- The approved floor identity, evaluated through the finite cutoff. -/
theorem finite_target {n : ℕ} (hn : n < 2048) :
    OMA.S_oeis_a047872.a n = ⌊center n⌋ := by
  by_cases h : n = 0
  · subst n; exact at_zero
  unfold OMA.S_oeis_a047872.a
  rw [← Rat.floor_cast (α := ℝ), Rat.cast_abs, Rat.cast_div, bernoulli_ratio h]
  have hc : 0 ≤ center n := by unfold center; positivity
  apply A047872.FiniteMargin.floor_stable hn
  · exact mul_le_mul_of_nonneg_left (zeta_ratio_lower h) hc
  · exact mul_le_of_le_one_right hc ((div_le_one (evenZeta_pos h)).mpr (evenZeta_succ_le h))

/-- The error in the unnormalized difference is less than (3V/4^n). -/
theorem sharp_zeta_error {n : ℕ} (hn : n ≠ 0) :
    ((n + 1) * (2 * n + 1) : ℝ) * (evenZeta n - evenZeta (n + 1)) / evenZeta n <
      3 * ((n + 1) * (2 * n + 1) : ℝ) / 4 ^ n := by
  have hscale : 0 < (4 : ℝ) ^ n := by positivity
  have htail := scaled_zeta_tail_lt_three hn
  have hnext := one_le_evenZeta (Nat.succ_ne_zero n)
  have diff : (4 : ℝ) ^ n * (evenZeta n - evenZeta (n + 1)) < 3 := by
    nlinarith only [htail, mul_le_mul_of_nonneg_left hnext hscale.le]
  have hpos : 0 < ((n + 1) * (2 * n + 1) : ℝ) := by positivity
  apply (div_lt_div_iff₀ (evenZeta_pos hn) hscale).mpr
  nlinarith only [mul_lt_mul_of_pos_left diff hpos,
    mul_le_mul_of_nonneg_left (one_le_evenZeta hn) hpos.le]

end A047872Certificate

end

section

namespace A047872

/-- A small positive integral linear form in `z` bounds the error of any
competing rational approximation whose denominator is `q`. -/
theorem linearFormGap (z L U : ℝ) (a b p q : ℤ)
    (hL : 0 < L) (hhalf : L ≤ 1 / 2) (hU : 0 < U)
    (ha : |(a : ℝ)| ≤ U) (hq : 1 ≤ q)
    (hlo : L ≤ (a : ℝ) * z + b)
    (hhi : (q : ℝ) * ((a : ℝ) * z + b) ≤ 1 / 2) :
    L / U ≤ |(q : ℝ) * z - p| := by
  by_contra! hclose
  have hproduct : |(a : ℝ) * ((q : ℝ) * z - p)| < L := by
    rw [abs_mul]
    calc
      _ ≤ U * |(q : ℝ) * z - p| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
      _ < L := by simpa [mul_comm] using (lt_div_iff₀ hU).mp hclose
  have hqreal : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqlo : L ≤ (q : ℝ) * ((a : ℝ) * z + b) :=
    hlo.trans (le_mul_of_one_le_left (hL.le.trans hlo) hqreal)
  obtain ⟨hneg, hpos⟩ := abs_lt.mp hproduct
  have hcast : ((a * p + q * b : ℤ) : ℝ) =
      (q : ℝ) * ((a : ℝ) * z + b) - (a : ℝ) * ((q : ℝ) * z - p) := by
    push_cast
    ring
  have hzero : (0 : ℝ) < ((a * p + q * b : ℤ) : ℝ) := by rw [hcast]; linarith
  have hone : ((a * p + q * b : ℤ) : ℝ) < 1 := by rw [hcast]; linarith
  have hzero' : 0 < a * p + q * b := by exact_mod_cast hzero
  have hone' : a * p + q * b < 1 := by exact_mod_cast hone
  omega

/-- Both exponential estimates used with `m = n / 8`. -/
theorem growthPair (m : ℕ) (hm : 256 ≤ m) :
    1296 * m ^ 2 * 9 ^ m ≤ 10 ^ m ∧ 15552 * m ^ 2 < 8 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have p : 9 * (n + 1) ^ 2 ≤ 10 * n ^ 2 := by
      nlinarith only [Nat.mul_le_mul_left n hn, hn]
    have p' : (n + 1) ^ 2 ≤ 8 * n ^ 2 := by
      nlinarith only [Nat.mul_le_mul_left n hn, hn]
    constructor
    · calc
        1296 * (n + 1) ^ 2 * 9 ^ (n + 1) =
            (9 * (n + 1) ^ 2) * (1296 * 9 ^ n) := by rw [pow_succ]; ring
        _ ≤ (10 * n ^ 2) * (1296 * 9 ^ n) := Nat.mul_le_mul_right _ p
        _ = (1296 * n ^ 2 * 9 ^ n) * 10 := by ring
        _ ≤ 10 ^ n * 10 := Nat.mul_le_mul_right _ ih.1
        _ = 10 ^ (n + 1) := (pow_succ _ _).symm
    · calc
        15552 * (n + 1) ^ 2 ≤ (15552 * n ^ 2) * 8 := by
          nlinarith only [Nat.mul_le_mul_left 15552 p']
        _ < 8 ^ n * 8 := Nat.mul_lt_mul_of_pos_right ih.2 (by decide)
        _ = 8 ^ (n + 1) := (pow_succ _ _).symm

/-- The algebraic and size properties of the Beukers integral used in the proof. -/
def HasBeukersForms (z : ℝ) : Prop :=
  ∀ m : ℕ, 256 ≤ m → ∃ a b : ℤ, |(a : ℝ)| ≤ 144 ^ m ∧
    1 / (16 * 32 ^ m) ≤ (a : ℝ) * z + b ∧
    (a : ℝ) * z + b ≤ 2 * 9 ^ m / 10 ^ m

/-- The quantitative separation needed for the large-index floor comparison. -/
theorem largeIndexGap {z : ℝ} (forms : HasBeukersForms z) (n : ℕ) (hn : 2048 ≤ n)
    (q : ℤ) (hq : 1 ≤ q) (hqv : q ≤ ((n + 1) * (2 * n + 1) : ℕ)) :
    3 * (((n + 1) * (2 * n + 1) : ℕ) : ℝ) / 4 ^ n <
      |(q : ℝ) * z - (((n + 1) * (2 * n + 1) : ℕ) : ℝ)| := by
  let m := n / 8
  let v := (n + 1) * (2 * n + 1)
  change 3 * (v : ℝ) / 4 ^ n < |(q : ℝ) * z - (v : ℝ)|
  have hm : 256 ≤ m := by dsimp [m]; omega
  have hnm : n ≤ 9 * m := by dsimp [m]; omega
  have hmn : 8 * m ≤ n := by dsimp [m]; omega
  have hv : v ≤ 324 * m ^ 2 := by
    have h : (n + 1) * (2 * n + 1) ≤ (9 * m + 1) * (2 * (9 * m) + 1) := by gcongr
    dsimp [v]
    nlinarith only [h, Nat.mul_le_mul_left m hm, hm]
  obtain ⟨g₁, g₂⟩ := growthPair m hm
  have g₁' : 4 * v * 9 ^ m ≤ 10 ^ m := by
    calc
      _ ≤ 4 * (324 * m ^ 2) * 9 ^ m := by gcongr
      _ = 1296 * m ^ 2 * 9 ^ m := by ring
      _ ≤ _ := g₁
  have g₂' : 48 * v * 4608 ^ m < 4 ^ n := by
    calc
      _ ≤ (48 * (324 * m ^ 2)) * 4608 ^ m :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 48 hv)
      _ = 15552 * m ^ 2 * 4608 ^ m := by ring
      _ < 8 ^ m * 4608 ^ m := Nat.mul_lt_mul_of_pos_right g₂ (by positivity)
      _ = (8 * 4608) ^ m := (mul_pow _ _ _).symm
      _ ≤ (4 ^ 8) ^ m := Nat.pow_le_pow_left (by decide) _
      _ = 4 ^ (8 * m) := (pow_mul _ _ _).symm
      _ ≤ 4 ^ n := Nat.pow_le_pow_right (by decide) hmn
  obtain ⟨a, b, ha, hlo, hhi⟩ := forms m hm
  have qv : (q : ℝ) ≤ (v : ℝ) := by exact_mod_cast hqv
  have qpos : (0 : ℝ) ≤ q := by exact_mod_cast (by omega : (0 : ℤ) ≤ q)
  have g₁r : 4 * (v : ℝ) * 9 ^ m ≤ 10 ^ m := by exact_mod_cast g₁'
  have hhalf : (q : ℝ) * ((a : ℝ) * z + b) ≤ 1 / 2 := by
    calc
      _ ≤ (q : ℝ) * (2 * 9 ^ m / 10 ^ m) := mul_le_mul_of_nonneg_left hhi qpos
      _ ≤ (v : ℝ) * (2 * 9 ^ m / 10 ^ m) := by gcongr
      _ ≤ 1 / 2 := by rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have lhalf : (1 : ℝ) / (16 * 32 ^ m) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have : (1 : ℝ) ≤ 32 ^ m := one_le_pow₀ (by norm_num)
    linarith
  have gap := linearFormGap z _ _ a b (v : ℤ) q (by positivity) lhalf
    (by positivity) ha hq hlo hhalf
  push_cast at gap
  apply lt_of_lt_of_le _ gap
  have g₂r : 48 * (v : ℝ) * 4608 ^ m < 4 ^ n := by exact_mod_cast g₂'
  rw [div_div, div_lt_div_iff₀ (by positivity) (by positivity), one_mul]
  have hpow : (32 : ℝ) ^ m * 144 ^ m = 4608 ^ m := by rw [← mul_pow]; norm_num
  nlinarith only [g₂r, congrArg (fun x : ℝ => 48 * (v : ℝ) * x) hpow]

end A047872

end

section

namespace A047872

private def lcmCheck : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => true
  | k + 1, start, d, b =>
    let d' := Nat.lcm (start+1) d
    let b' := b*3
    decide (d' ≤ b') && lcmCheck k (start+1) d' b'

private theorem lcmUpto_succ (s : ℕ) :
    Nat.lcmUpto (s + 1) = Nat.lcm (s + 1) (Nat.lcmUpto s) := by
  have h : Finset.Icc 1 (s+1) = insert (s+1) (Finset.Icc 1 s) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [Nat.lcmUpto, h, Finset.lcm_insert]
  rfl

private theorem check_sound (k s : ℕ)
    (h : lcmCheck k s (Nat.lcmUpto s) (3 ^ s) = true) :
    ∀ j, s < j → j ≤ s+k → Nat.lcmUpto j ≤ 3 ^ j := by
  induction k generalizing s with
  | zero => omega
  | succ k ih =>
    simp only [lcmCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [← lcmUpto_succ, ← pow_succ] at h
    intro j hj hj'
    rcases (show s+1 ≤ j by omega).eq_or_lt with e | hlt
    · simpa [← e] using h.1
    · exact ih (s+1) h.2 j hlt (by omega)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 6000000 in
private theorem checked4096 : lcmCheck 4096 0 1 1 = true := by decide

/-- A single kernel-evaluated table verifies the small range in Hanson's estimate. -/
theorem hansonFinite {n : ℕ} (hn : n ≤ 4096) : Nat.lcmUpto n ≤ 3^n := by
  by_cases h : n = 0
  · subst n; simp [Nat.lcmUpto]
  · exact check_sound 4096 0 (by simpa [Nat.lcmUpto] using checked4096) n (by omega) hn

end A047872

end

section

namespace A047872

open Finset Nat

private theorem div_swap (n a b : ℕ) : n / a / b = n / b / a := by
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm a b, ← Nat.div_div_eq_div_mul]

/-- The five denominators have reciprocal sum one. Below 1806, the
last term vanishes and the other four reciprocals sum to less than one. -/
private theorem floor_count (t : ℕ) (ht : 0 < t) :
    t / 2 + t / 3 + t / 7 + t / 43 + t / 1806 + (if t < 1806 then 1 else 0) ≤ t := by
  split <;> omega

/-- The fixed Egyptian-fraction partition yields a factorial divisibility.
The remaining lcm has argument smaller by a factor of 1806. -/
theorem hansonFactorialDvd (n : ℕ) :
    lcmUpto n * (n/2).factorial * (n/3).factorial * (n/7).factorial *
      (n/43).factorial * (n/1806).factorial ∣ n.factorial * lcmUpto (n/1806) := by
  apply (factorization_le_iff_dvd (by positivity [lcmUpto_pos n])
    (by positivity [lcmUpto_pos (n / 1806)])).mp
  intro p
  by_cases hp : p.Prime
  · simp (disch := positivity [lcmUpto_pos n, lcmUpto_pos (n/1806)]) only [Nat.factorization_mul,
      Finsupp.coe_add, Pi.add_apply, factorization_lcmUpto _ hp]
    let b := p.log n + 1
    have hb (d : ℕ) : p.log (n/d) < b :=
      Nat.lt_succ_of_le (Nat.log_mono_right (Nat.div_le_self n d))
    rw [factorization_factorial hp (hb 2), factorization_factorial hp (hb 3),
      factorization_factorial hp (hb 7), factorization_factorial hp (hb 43),
      factorization_factorial hp (hb 1806), factorization_factorial hp (Nat.lt_succ_self (p.log n))]
    have hpoint (i : ℕ) (hi : i ∈ Ico 1 b) :
        n / 2 / p^i + n / 3 / p^i + n / 7 / p^i + n / 43 / p^i +
          n / 1806 / p^i + (if p.log (n/1806) + 1 ≤ i then 1 else 0) ≤ n / p^i := by
      have hi' := mem_Ico.mp hi
      have hn : n ≠ 0 := by
        rintro rfl
        simp [b] at hi
      have hpow : p^i ≤ n := (le_log_iff_pow_le hp.one_lt hn).mp (by simpa [b] using hi'.2)
      have hdiv : 0 < n / p^i := Nat.div_pos hpow (pow_pos hp.pos _)
      rw [div_swap n 2, div_swap n 3, div_swap n 7, div_swap n 43, div_swap n 1806]
      have hcut : p.log (n/1806) + 1 ≤ i ↔ n / p^i < 1806 := by
        rw [Nat.div_lt_iff_lt_mul (pow_pos hp.pos _), Nat.mul_comm 1806,
          ← Nat.div_lt_iff_lt_mul (by decide : 0 < 1806)]
        constructor
        · exact fun h => Nat.lt_pow_of_log_lt hp.one_lt h
        · intro h
          by_cases hzero : n / 1806 = 0
          · simp [hzero]; omega
          · exact lt_of_not_ge (fun hl => h.not_ge ((Nat.le_log_iff_pow_le hp.one_lt hzero).mp hl))
      simp only [hcut]
      exact floor_count _ hdiv
    have hsum := sum_le_sum hpoint
    simp only [sum_add_distrib, sum_boole] at hsum
    rw [Ico_filter_le, Nat.card_Ico] at hsum
    have hsmall := Nat.log_mono_right (b := p) (Nat.div_le_self n 1806)
    dsimp [b] at hsum ⊢
    rw [max_eq_right (by omega)] at hsum
    omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private def hansonDen : Fin 5 → ℕ := ![2,3,7,43,1806]

private theorem hansonMultinomial (a : Fin 5 → ℕ) :
    Nat.multinomial univ a ≤ ∏ i, (hansonDen i)^(a i) := by
  let w : Fin 5 → ℚ := fun i => (hansonDen i : ℚ)⁻¹
  have hw : ∑ i, w i = 1 := by norm_num [w, hansonDen, Fin.sum_univ_succ]
  have hmem : a ∈ piAntidiag univ (∑ i, a i) := by simp
  have h := single_le_sum (f := fun k : Fin 5 → ℕ =>
    (Nat.multinomial univ k : ℚ) * ∏ i, w i^k i)
    (fun k _ => by
      have hw' (i : Fin 5) : 0 ≤ w i := by dsimp [w]; positivity
      positivity) hmem
  rw [← sum_pow_eq_sum_piAntidiag, hw, one_pow] at h
  have hpos : 0 < ∏ i, (hansonDen i : ℚ)^a i := by
    apply prod_pos
    intro i _
    exact pow_pos (by fin_cases i <;> norm_num [hansonDen]) _
  simp only [w, inv_pow, prod_inv_distrib] at h
  have hh := (div_le_iff₀ hpos).mp (show (Nat.multinomial univ a : ℚ) / _ ≤ 1 by
    rwa [div_eq_mul_inv])
  exact_mod_cast (by simpa using hh : (Nat.multinomial univ a : ℚ) ≤ ∏ i, (hansonDen i : ℚ)^a i)

private theorem hansonRec (n : ℕ) (hn : 0 < n) :
    lcmUpto n ≤ n^4 * (∏ i, hansonDen i ^ (n / hansonDen i)) * lcmUpto (n/1806) := by
  let a := fun i => n / hansonDen i
  let s := ∑ i, a i
  let F := ∏ i, (a i).factorial
  have hs : s ≤ n ∧ n ≤ s + 4 := by
    simp only [s,a,hansonDen, Fin.sum_univ_succ, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Finset.sum_empty, Finset.univ_eq_empty, Nat.add_zero]
    omega
  have hstart : lcmUpto n * F ≤ n.factorial * lcmUpto (n/1806) := by
    have hh := Nat.le_of_dvd (by positivity [lcmUpto_pos (n/1806)]) (hansonFactorialDvd n)
    simpa [F,a,hansonDen, Fin.prod_univ_succ, Nat.mul_assoc] using hh
  have hfrac : n.factorial ≤ s.factorial * n^4 := by
    have h := Nat.factorial_mul_descFactorial (Nat.sub_le n s)
    rw [show n - (n - s) = s by omega] at h
    rw [← h]
    exact Nat.mul_le_mul_left _ ((Nat.descFactorial_le_pow _ _).trans
      (pow_le_pow_right₀ hn (show n - s ≤ 4 by omega)))
  have hmulti : F * Nat.multinomial univ a = s.factorial := Nat.multinomial_spec _ _
  have hF : 0 < F := Finset.prod_pos fun _ _ => Nat.factorial_pos _
  refine Nat.le_of_mul_le_mul_right ?_ hF
  calc
    _ ≤ n.factorial * lcmUpto (n/1806) := hstart
    _ ≤ (s.factorial * n^4) * lcmUpto (n/1806) := Nat.mul_le_mul_right _ hfrac
    _ = (n^4 * Nat.multinomial univ a * lcmUpto (n/1806)) * F := by rw [← hmulti]; ac_rfl
    _ ≤ _ := by gcongr; exact hansonMultinomial a

private theorem hansonWeightPow (n : ℕ) :
    (∏ i, hansonDen i^(n / hansonDen i))^1806 ≤
    (∏ i, hansonDen i^(1806 / hansonDen i))^n := by
  simp only [← Finset.prod_pow]
  apply Finset.prod_le_prod'
  intro i _
  simp only [← pow_mul]
  apply pow_le_pow_right₀
  · fin_cases i <;> decide
  · fin_cases i <;> simp [hansonDen] <;> omega

private theorem hansonWeightFit :
    2^40 * (∏ i, hansonDen i^(1806 / hansonDen i)) ≤ 3^1805 := by
  decide +kernel

private theorem hansonPolyFit (n : ℕ) (hn : 4096 ≤ n) : (n^4)^1806 ≤ (2^40)^n := by
  have blocks (k : ℕ) (hk : 16 ≤ k) : 256 * (k+1) ≤ 2^k := by
    induction k, hk using Nat.le_induction with
    | base => decide
    | succ k hk ih =>
      rw [pow_succ]
      omega
  have h : n ≤ 2^(n/256) := (show n ≤ 256 * (n/256+1) by omega).trans
    (blocks _ (by omega))
  calc
    _ = n ^ (4*1806) := (pow_mul ..).symm
    _ ≤ (2^(n/256))^(4*1806) := Nat.pow_le_pow_left h _
    _ ≤ (2^40)^n := by
      simp only [← pow_mul]
      apply pow_le_pow_right₀ (by decide)
      omega

private theorem hansonPowerStep (n W H : ℕ) (hn : 4096 ≤ n) (hweight : W^1806 ≤ H^n)
    (hfit : 2^40 * H ≤ 3^1805) (hrec : lcmUpto n ≤ n^4 * W * 3^(n/1806)) :
    lcmUpto n ≤ 3^n := by
  have hs : (3^(n/1806) : ℕ)^1806 ≤ 3^n := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by decide) (Nat.div_mul_le_self _ _)
  have hr := pow_le_pow_left₀ (Nat.zero_le _) hrec 1806
  simp only [mul_pow] at hr
  have hcost := Nat.mul_le_mul (Nat.mul_le_mul (hansonPolyFit n hn) hweight) hs
  have hbudget := Nat.mul_le_mul_right (3^n) (Nat.pow_le_pow_left hfit n)
  rw [mul_pow] at hbudget
  have hlast : ((3 : ℕ)^1805)^n * 3^n = (3^n)^1806 := by
    simp only [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hlast] at hbudget
  have hfinal : (lcmUpto n)^1806 ≤ (3^n)^1806 := Nat.le_trans hr (Nat.le_trans hcost hbudget)
  exact le_of_pow_le_pow_left₀ (by decide : (1806 : ℕ) ≠ 0) (Nat.zero_le _) hfinal

/-- Hanson's bound for the lcm of the first `n` positive integers. -/
theorem hansonBound (n : ℕ) : Nat.lcmUpto n ≤ 3^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ 4096
    · exact hansonFinite hn
    · apply hansonPowerStep n _ _ (by omega) (hansonWeightPow n) hansonWeightFit
      exact (hansonRec n (by omega)).trans (Nat.mul_le_mul_left _
        (ih _ (Nat.div_lt_self (by omega) (by decide))))

end A047872

end

section

namespace A047872

/-- The positive factor occurring to the power `m` in the Beukers integral. -/
noncomputable def beukersKernel (x y : ℝ) : ℝ :=
  x * (1 - x) * y * (1 - y) / (1 - x * y)

theorem beukersKernel_nonneg {x y : ℝ}
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) : 0 ≤ beukersKernel x y := by
  have hxy : x * y ≤ 1 := by simpa using mul_le_mul hx.2 hy.2 hy.1 zero_le_one
  exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hx.2))
    hy.1) (sub_nonneg.mpr hy.2)) (sub_nonneg.mpr hxy)

/-- On the unit square the Beukers factor is bounded by one tenth,
including its Lean value at the removable corner `(1,1)`. -/
theorem beukersKernel_le_tenth {x y : ℝ}
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) : beukersKernel x y ≤ 1 / 10 := by
  have hxy : x * y ≤ 1 := by simpa using mul_le_mul hx.2 hy.2 hy.1 zero_le_one
  rcases hxy.eq_or_lt with hcorner | hxy'
  · simp [beukersKernel, hcorner]
  let t := Real.sqrt (x * y)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht1 : t ≤ 1 := Real.sqrt_le_one.mpr hxy
  have ht2 : t ^ 2 = x * y := Real.sq_sqrt (mul_nonneg hx.1 hy.1)
  have ham : 2 * t ≤ x + y := by
    apply le_of_sq_le_sq _ (add_nonneg hx.1 hy.1)
    nlinarith only [sq_nonneg (x - y), ht2]
  have hfac : (1 - x) * (1 - y) ≤ (1 - t) ^ 2 := by nlinarith only [ham, ht2]
  have hcubic : t ^ 2 * (1 - t) ≤ (1 / 10) * (1 + t) := by
    nlinarith only [mul_nonneg (show 0 ≤ 10 * t + 2 by linarith) (sq_nonneg (t - 3/5)), ht1]
  apply (div_le_iff₀ (sub_pos.mpr hxy')).mpr
  calc
    x * (1 - x) * y * (1 - y) = t ^ 2 * ((1 - x) * (1 - y)) := by rw [ht2]; ring
    _ ≤ t ^ 2 * (1 - t) ^ 2 := mul_le_mul_of_nonneg_left hfac (sq_nonneg _)
    _ ≤ 1 / 10 * (1 - x * y) := by
      nlinarith only [mul_le_mul_of_nonneg_right hcubic (sub_nonneg.mpr ht1), ht2]

/-- On the smaller square used for the lower integral estimate. -/
theorem beukersKernel_ge_one_thirtysecond {x y : ℝ}
    (hx : x ∈ Set.Icc (1 / 4 : ℝ) (1 / 2))
    (hy : y ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) : 1 / 32 ≤ beukersKernel x y := by
  have hquad (u : ℝ) (hu : u ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
      3 / 16 ≤ u * (1 - u) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hu.1) (show 0 ≤ 3 / 4 - u by linarith [hu.2])]
  have hprod := mul_le_mul (hquad x hx) (hquad y hy) (by norm_num : (0 : ℝ) ≤ 3 / 16)
    ((by norm_num : (0 : ℝ) ≤ 3 / 16).trans (hquad x hx))
  have hxy0 : 0 ≤ x * y := mul_nonneg (by linarith [hx.1]) (by linarith [hy.1])
  have hxy1 : x * y ≤ (1 / 2 : ℝ) * (1 / 2) :=
    mul_le_mul hx.2 hy.2 (by linarith [hy.1]) (by norm_num)
  apply (le_div_iff₀ (by linarith : 0 < 1 - x * y)).mpr
  nlinarith only [hprod, hxy0]

/-- A bound for the coefficient of zeta(2) before clearing denominators. -/
theorem beukersBinomialSum_le (m : ℕ) :
    ∑ r ∈ Finset.range (m + 1), m.choose r ^ 2 * (m+r).choose r ≤ 16 ^ m := by
  have htwo : (2 : ℕ) ^ (2 * m) = 4 ^ m := by rw [pow_mul]; norm_num
  calc
    _ ≤ ∑ r ∈ Finset.range (m + 1), m.choose r ^ 2 * 4 ^ m := by
      apply Finset.sum_le_sum
      intro r hr
      have hr' := Finset.mem_range_succ_iff.mp hr
      exact Nat.mul_le_mul_left _ ((Nat.choose_le_two_pow _ _).trans
        ((pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (show m + r ≤ 2 * m by omega)).trans htwo.le))
    _ = (2*m).choose m * 4 ^ m := by rw [← Finset.sum_mul, Nat.sum_range_choose_sq]
    _ ≤ 4 ^ m * 4 ^ m := Nat.mul_le_mul_right _ ((Nat.choose_le_two_pow _ _).trans htwo.le)
    _ = 16 ^ m := by rw [← mul_pow]; norm_num

/-- Given the lcm bound, the coefficient of zeta(2) after clearing
denominators grows at most as `144 ^ m`. -/
theorem beukersScaledCoefficient_le (m d : ℕ) (hd : d ≤ 3 ^ m) :
    d ^ 2 * (∑ r ∈ Finset.range (m + 1), m.choose r ^ 2 * (m+r).choose r) ≤ 144 ^ m := by
  calc
    _ ≤ (3 ^ m) ^ 2 * 16 ^ m := Nat.mul_le_mul (Nat.pow_le_pow_left hd _) (beukersBinomialSum_le m)
    _ = 144 ^ m := by rw [← pow_mul, Nat.mul_comm m 2, pow_mul, ← mul_pow]; norm_num

end A047872

end

section

open Set MeasureTheory

namespace A047872

private theorem kernel_strict_bound {x y : ℝ} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    beukersKernel x y ≤ 99 / 1000 := by
  have hxy : x * y ≤ 1 := by simpa using mul_le_mul hx.2 hy.2 hy.1 zero_le_one
  rcases hxy.eq_or_lt with hcorner | hxy'
  · norm_num [beukersKernel, hcorner]
  let t := Real.sqrt (x * y)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht1 : t ≤ 1 := Real.sqrt_le_one.mpr hxy
  have ht2 : t ^ 2 = x * y := Real.sq_sqrt (mul_nonneg hx.1 hy.1)
  have ham : 2 * t ≤ x + y := by
    apply le_of_sq_le_sq _ (add_nonneg hx.1 hy.1)
    nlinarith only [sq_nonneg (x - y), ht2]
  have hfac : (1-x)*(1-y) ≤ (1-t)^2 := by nlinarith only [ham, ht2]
  have hcubic : t^2*(1-t) ≤ (99/1000)*(1+t) := by
    nlinarith only [mul_nonneg (show 0 ≤ 10*t+2 by linarith) (sq_nonneg (t-3/5)), ht1]
  apply (div_le_iff₀ (sub_pos.mpr hxy')).mpr
  calc
    x*(1-x)*y*(1-y) = t ^ 2 * ((1-x)*(1-y)) := by rw [ht2]; ring
    _ ≤ t ^ 2 * (1-t)^2 := mul_le_mul_of_nonneg_left hfac (sq_nonneg _)
    _ ≤ 99/1000 * (1-x*y) := by
      nlinarith only [mul_le_mul_of_nonneg_right hcubic (sub_nonneg.mpr ht1), ht2]

noncomputable def beukersDensity (m : ℕ) (p : ℝ × ℝ) : ℝ :=
  beukersKernel p.1 p.2 ^ m / (1 - p.1 * p.2)

private theorem density_bounds (m : ℕ) (hm : 256 ≤ m) (x y : ℝ)
    (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    0 ≤ beukersDensity m (x,y) ∧ beukersDensity m (x,y) ≤ 2 / 10 ^ m := by
  have hxy : x*y ≤ 1 := by simpa using mul_le_mul hx.2 hy.2 hy.1 zero_le_one
  have hk := beukersKernel_nonneg hx hy
  refine ⟨div_nonneg (pow_nonneg hk _) (sub_nonneg.mpr hxy), ?_⟩
  rcases hxy.eq_or_lt with hc | hlt
  · simp [beukersDensity, hc]; positivity
  have hd : 0 < 1-x*y := sub_pos.mpr hlt
  have h1 : beukersKernel x y / (1-x*y) ≤ 1 := by
    unfold beukersKernel
    rw [div_div, div_le_one (mul_pos hd hd)]
    have hx' : 1-x ≤ 1-x*y := by linarith [mul_le_of_le_one_right hx.1 hy.2]
    have hy' : 1-y ≤ 1-x*y := by linarith [mul_le_of_le_one_left hy.1 hx.2]
    calc
      _ = (x*y)*((1-x)*(1-y)) := by ring
      _ ≤ 1*((1-x)*(1-y)) := mul_le_mul_of_nonneg_right hxy
        (mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hy.2))
      _ ≤ _ := by rw [one_mul]; exact mul_le_mul hx' hy' (sub_nonneg.mpr hy.2) hd.le
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have he : (99/100 : ℝ)^k ≤ 1/5 := by
    calc
      _ ≤ (99/100 : ℝ)^255 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ ≤ _ := by norm_num
  calc
    beukersDensity (k+1) (x,y) =
        beukersKernel x y ^ k * (beukersKernel x y / (1-x*y)) := by
          simp [beukersDensity, pow_succ, mul_div_assoc]
    _ ≤ (99/1000 : ℝ)^k * 1 := mul_le_mul
      (pow_le_pow_left₀ hk (kernel_strict_bound hx hy) _) h1 (div_nonneg hk hd.le) (by positivity)
    _ ≤ 2 / 10 ^ (k+1) := by
      rw [mul_one, show (99/1000 : ℝ) = (99/100)/10 by norm_num, div_pow,
        pow_succ, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [mul_le_mul_of_nonneg_right he (show (0:ℝ) ≤ 10^k by positivity)]

def beukersSquare (a b : ℝ) := Icc a b ×ˢ Icc a b

noncomputable def beukersIntegral (m : ℕ) : ℝ :=
  ∫ p in beukersSquare 0 1, beukersDensity m p

theorem beukersDensity_integrableOn (m : ℕ) (hm : 256 ≤ m) :
    IntegrableOn (beukersDensity m) (beukersSquare 0 1) := by
  let S := beukersSquare 0 1
  have hS : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have volS : volume S = 1 := by
    rw [show S = Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 by rfl, Measure.volume_eq_prod,
      Measure.prod_prod, Real.volume_Icc]
    norm_num
  refine IntegrableOn.of_bound (by change volume S < _; rw [volS]; simp) ?_ (2 / 10 ^ m) ?_
  · apply Measurable.aestronglyMeasurable
    unfold beukersDensity beukersKernel
    fun_prop
  · apply (ae_restrict_iff' hS).mpr
    apply Filter.Eventually.of_forall
    intro p hp
    obtain ⟨hl,hu⟩ := density_bounds m hm p.1 p.2 hp.1 hp.2
    rwa [Real.norm_eq_abs, abs_of_nonneg hl]

/-- Absolute bounds for the unsigned Beukers integral. -/
theorem beukersIntegral_bounds (m : ℕ) (hm : 256 ≤ m) :
    1 / (16 * 32 ^ m) ≤ beukersIntegral m ∧ beukersIntegral m ≤ 2 / 10 ^ m := by
  let S := beukersSquare 0 1
  let T := beukersSquare (1/4) (1/2)
  have hS : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have hT : MeasurableSet T := measurableSet_Icc.prod measurableSet_Icc
  have volS : volume S = 1 := by
    rw [show S = Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 by rfl, Measure.volume_eq_prod,
      Measure.prod_prod, Real.volume_Icc]
    norm_num
  have volT : volume T = ENNReal.ofReal (1/16) := by
    rw [show T = Icc (1/4:ℝ) (1/2) ×ˢ Icc (1/4:ℝ) (1/2) by rfl, Measure.volume_eq_prod,
      Measure.prod_prod, Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have sub : T ⊆ S := fun p hp =>
    ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
  have hd (p : ℝ × ℝ) (hp : p ∈ S) := density_bounds m hm p.1 p.2 hp.1 hp.2
  have hi := beukersDensity_integrableOn m hm
  have hsnon : 0 ≤ᵐ[volume.restrict S] beukersDensity m :=
    (ae_restrict_iff' hS).mpr (Filter.Eventually.of_forall (fun p hp => (hd p hp).1))
  have htlow (p : ℝ × ℝ) (hp : p ∈ T) : (1/32 : ℝ)^m ≤ beukersDensity m p := by
    obtain ⟨hx, hy⟩ := hp
    have hxy : p.1 * p.2 ≤ (1/2 : ℝ)*(1/2) :=
      mul_le_mul hx.2 hy.2 (by linarith [hy.1]) (by norm_num)
    have hxy0 : 0 ≤ p.1 * p.2 := mul_nonneg (by linarith [hx.1]) (by linarith [hy.1])
    apply (le_div_iff₀ (by linarith : 0 < 1-p.1*p.2)).mpr
    calc
      _ ≤ (1/32 : ℝ)^m * 1 := by gcongr; linarith
      _ ≤ _ := by rw [mul_one]; exact pow_le_pow_left₀ (by norm_num) (beukersKernel_ge_one_thirtysecond hx hy) _
  change _ ≤ ∫ p in S, beukersDensity m p ∧ _
  constructor
  · calc
      _ = ∫ _p in T, (1/32 : ℝ)^m := by
        rw [setIntegral_const, measureReal_def, volT, ENNReal.toReal_ofReal (by norm_num)]
        simp [one_div, mul_inv_rev, smul_eq_mul, mul_comm]
      _ ≤ ∫ p in T, beukersDensity m p := setIntegral_mono_on
        (integrableOn_const (by rw [volT]; simp)) (hi.mono_set sub) hT htlow
      _ ≤ _ := setIntegral_mono_set hi hsnon sub.eventuallyLE
  · calc
      _ ≤ ∫ _p in S, (2 : ℝ)/10^m := setIntegral_mono_on hi
        (integrableOn_const (by rw [volS]; simp)) hS (fun p hp => (hd p hp).2)
      _ = _ := by simp [measureReal_def, volS]

end A047872

end

section

/-! Series and denominator clearing for the monomial moments in Beukers' proof. -/

open Finset Filter

namespace A047872.Moments

/-- The positive-integer reciprocal at position `k`, indexed from zero. -/
noncomputable def recip (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

/-- The first `r` terms of the Basel series. -/
noncomputable def squarePrefix (r : ℕ) : ℝ := ∑ k ∈ range r, (recip k) ^ 2

lemma harmonic_real (r : ℕ) : (harmonic r : ℝ) = ∑ k ∈ range r, recip k := by
  simp [harmonic, recip, one_div]

lemma divides_lcm {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) : k ∣ Nat.lcmUpto m :=
  Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hk, hkm⟩)

lemma scaled_recip {m k : ℕ} (hk : k < m) :
    (Nat.lcmUpto m : ℝ) * recip k = (Nat.lcmUpto m / (k+1) : ℕ) := by
  rw [Nat.cast_div (divides_lcm (by omega) (by omega)) (by positivity)]
  simp [recip, div_eq_mul_inv]

lemma harmonic_cleared {m r : ℕ} (hr : r ≤ m) :
    ∃ a : ℤ, (Nat.lcmUpto m : ℝ) * (harmonic r : ℝ) = a := by
  refine ⟨↑(∑ k ∈ range r, Nat.lcmUpto m / (k+1)), ?_⟩
  rw [harmonic_real, Finset.mul_sum]
  push_cast
  exact sum_congr rfl fun k hk => scaled_recip (lt_of_lt_of_le (mem_range.mp hk) hr)

lemma diagonal_cleared {m r : ℕ} (hr : r ≤ m) :
    ∃ b : ℤ, (Nat.lcmUpto m : ℝ) ^ 2 * (-(squarePrefix r)) = b := by
  let w : ℕ := ∑ k ∈ range r, (Nat.lcmUpto m / (k+1)) ^ 2
  refine ⟨-(w : ℤ), ?_⟩
  have hw : ((w : ℤ) : ℝ) = (w : ℝ) := by norm_cast
  rw [Int.cast_neg, hw, mul_neg, squarePrefix, Finset.mul_sum]
  simp only [w, Nat.cast_sum, Nat.cast_pow]
  congr 1
  apply sum_congr rfl
  intro k hk
  rw [← mul_pow, scaled_recip (lt_of_lt_of_le (mem_range.mp hk) hr)]

lemma off_diagonal_cleared {m r s : ℕ} (hr : r ≤ m) (hs : s ≤ m) (hne : r ≠ s) :
    ∃ b : ℤ, (Nat.lcmUpto m : ℝ) ^ 2 *
      (((harmonic r : ℝ) - (harmonic s : ℝ)) / ((r : ℝ) - s)) = b := by
  wlog hrs : s < r generalizing r s
  · obtain ⟨b,hb⟩ := this hs hr hne.symm (by omega)
    exact ⟨b, (by simpa only [← neg_sub (s : ℝ) r, ← neg_sub (harmonic s : ℝ) (harmonic r : ℝ),
      neg_div_neg_eq] using hb : _)⟩
  obtain ⟨a,ha⟩ := harmonic_cleared hr
  obtain ⟨b,hb⟩ := harmonic_cleared hs
  let d := Nat.lcmUpto m / (r-s)
  have hd : (d : ℝ) = (Nat.lcmUpto m : ℝ) / ((r : ℝ) - s) := by
    dsimp [d]
    rw [Nat.cast_div (divides_lcm (by omega) (by omega)) (by exact_mod_cast (by omega : r-s ≠ 0)),
      Nat.cast_sub hrs.le]
  refine ⟨(d : ℤ) * (a-b), ?_⟩
  push_cast
  rw [hd, ← ha, ← hb]
  ring

lemma hasSum_consecutive (s : ℕ) :
    HasSum (fun k : ℕ => recip (k+s) - recip (k+1+s)) (recip s) := by
  have hlim : Tendsto (fun k : ℕ => recip (k+s)) atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat s).2 (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => ?_) _).mpr
  · simp_rw [sum_range_sub' (fun k => recip (k+s))]
    simpa using tendsto_const_nhds.sub hlim
  · apply sub_nonneg.mpr
    unfold recip
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast (by omega : k+s+1 ≤ k+1+s+1)

/-- The difference of two tails of the harmonic series telescopes. -/
lemma hasSum_recip_diff (r : ℕ) :
    HasSum (fun k : ℕ => recip k - recip (k+r)) (harmonic r : ℝ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h := ih.add (hasSum_consecutive r)
    simpa [harmonic_succ, recip, add_assoc, add_comm, add_left_comm, sub_add_sub_cancel] using h

/-- The series obtained by integrating the geometric expansion of
`x^r*y^s/(1-x*y)` over the unit square. -/
noncomputable def moment (r s : ℕ) : ℝ := ∑' k : ℕ, recip (k+r) * recip (k+s)

theorem moment_off_diagonal {r s : ℕ} (hne : r ≠ s) :
    moment r s = ((harmonic r : ℝ) - (harmonic s : ℝ)) / ((r : ℝ) - s) := by
  have h := ((hasSum_recip_diff r).sub (hasSum_recip_diff s)).div_const ((r : ℝ) - s)
  apply HasSum.tsum_eq
  apply h.congr_fun
  intro k
  dsimp [recip]
  push_cast
  have hne' : (r : ℝ) - s ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  field_simp
  ring

theorem moment_diagonal (r : ℕ) : moment r r = Real.pi ^ 2 / 6 - squarePrefix r := by
  have hbase : HasSum (fun k : ℕ => recip k ^ 2) (Real.pi ^ 2 / 6) := by
    simpa [recip, div_pow] using (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
  have h := (hasSum_nat_add_iff' r).2 hbase
  simpa [moment, squarePrefix, pow_two] using h.tsum_eq

/-- LCM-squared times a monomial moment is an integer linear form in ζ(2).
Only the diagonal moments have a nonzero coefficient of ζ(2). -/
theorem moment_linear_form {m r s : ℕ} (hr : r ≤ m) (hs : s ≤ m) :
    ∃ b : ℤ, (Nat.lcmUpto m : ℝ) ^ 2 * moment r s =
      (if r = s then (Nat.lcmUpto m : ℝ) ^ 2 else 0) * (Real.pi ^ 2 / 6) + b := by
  by_cases h : r = s
  · subst s
    obtain ⟨b,hb⟩ := diagonal_cleared hr
    exact ⟨b, by rw [moment_diagonal, if_pos rfl, ← hb]; ring⟩
  · obtain ⟨b,hb⟩ := off_diagonal_cleared hr hs h
    exact ⟨b, by simpa [moment_off_diagonal h, h] using hb⟩

open Set MeasureTheory

abbrev unitSquare : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1

noncomputable def monomialKernel (r s : ℕ) (p : ℝ × ℝ) : ℝ :=
  p.1 ^ r * p.2 ^ s / (1 - p.1 * p.2)

private theorem moment_summable (r s : ℕ) : Summable (fun k : ℕ => recip (k+r) * recip (k+s)) := by
  have hb : HasSum (fun k : ℕ => recip k ^ 2) (Real.pi ^ 2 / 6) := by
    simpa [recip, div_pow] using (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
  have hmono (k t : ℕ) : recip (k+t) ≤ recip k := by
    unfold recip
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast (by omega : k+1 ≤ k+t+1)
  apply Summable.of_nonneg_of_le (fun k => by unfold recip; positivity) _ hb.summable
  intro k
  rw [pow_two]
  exact mul_le_mul (hmono k r) (hmono k s) (by unfold recip; positivity) (by unfold recip; positivity)

private theorem integral_unit_pow (k : ℕ) : ∫ x in Icc (0 : ℝ) 1, x ^ k = recip k := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_pow]
  simp [recip]

/-- The product-measure integral of the original monomial over the closed unit square. -/
theorem integral_monomialKernel (r s : ℕ) :
    ∫ p in unitSquare, monomialKernel r s p = moment r s := by
  let F (k : ℕ) (p : ℝ × ℝ) := p.1 ^ (k+r) * p.2 ^ (k+s)
  have hint (k : ℕ) : IntegrableOn (F k) unitSquare :=
    (show Continuous (F k) by dsimp [F]; fun_prop).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hterm (k : ℕ) : ∫ p in unitSquare, F k p = recip (k+r) * recip (k+s) := by
    rw [Measure.volume_eq_prod]
    exact (setIntegral_prod_mul (fun x : ℝ => x ^ (k+r)) (fun y : ℝ => y ^ (k+s))
      (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)).trans (by rw [integral_unit_pow, integral_unit_pow])
  have hsum : Summable (fun k : ℕ => ∫ p in unitSquare, ‖F k p‖) := by
    apply (moment_summable r s).congr
    intro k
    rw [← hterm]
    apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
    intro p hp
    exact (Real.norm_eq_abs _).trans (abs_of_nonneg (mul_nonneg (pow_nonneg hp.1.1 _) (pow_nonneg hp.2.1 _))) |>.symm
  have hpoint (p : ℝ × ℝ) (hp : p ∈ unitSquare) :
      monomialKernel r s p = ∑' k : ℕ, F k p := by
    have h0 : 0 ≤ p.1 * p.2 := mul_nonneg hp.1.1 hp.2.1
    have h1 : p.1 * p.2 ≤ 1 := by simpa using mul_le_mul hp.1.2 hp.2.2 hp.2.1 zero_le_one
    have he (k : ℕ) : F k p = p.1 ^ r * p.2 ^ s * (p.1 * p.2)^k := by
      dsimp [F]; rw [pow_add, pow_add, mul_pow]; ring
    simp_rw [he]
    rw [tsum_mul_left]
    rcases h1.eq_or_lt with h | h
    · simp [monomialKernel, h]
    · rw [tsum_geometric_of_lt_one h0 h]
      simp [monomialKernel, div_eq_mul_inv]
  calc
    _ = ∫ p in unitSquare, ∑' k : ℕ, F k p :=
      setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) hpoint
    _ = ∑' k : ℕ, ∫ p in unitSquare, F k p :=
      (integral_tsum_of_summable_integral_norm hint hsum).symm
    _ = _ := tsum_congr hterm

theorem integrable_monomialKernel (r s : ℕ) : IntegrableOn (monomialKernel r s) unitSquare := by
  have hpos : 0 < moment r s := (moment_summable r s).tsum_pos (fun k => by unfold recip; positivity)
    0 (by unfold recip; positivity)
  by_contra hn
  rw [← integral_monomialKernel, integral_undef hn] at hpos
  exact lt_irrefl _ hpos

/-- Denominator clearing for the actual monomial integral. -/
theorem integral_monomial_linear_form {m r s : ℕ} (hr : r ≤ m) (hs : s ≤ m) :
    ∃ b : ℤ, (Nat.lcmUpto m : ℝ) ^ 2 * (∫ p in unitSquare, monomialKernel r s p) =
      (if r = s then (Nat.lcmUpto m : ℝ) ^ 2 else 0) * (Real.pi ^ 2 / 6) + b := by
  rw [integral_monomialKernel]
  exact moment_linear_form hr hs

end A047872.Moments

end

section

open Finset

namespace A047872

def beukersSignedCoeff (m r s : ℕ) : ℤ :=
  (-1)^(m+r+s) * (m.choose r : ℤ) * ((m+r).choose r : ℤ) * (m.choose s : ℤ)

noncomputable def beukersMomentSum (m : ℕ) : ℝ :=
  ∑ r ∈ range (m+1), ∑ s ∈ range (m+1),
    (beukersSignedCoeff m r s : ℝ) * Moments.moment r s

/-- Coefficients on the diagonal have one sign. -/
private theorem diagCoeff (m r : ℕ) : beukersSignedCoeff m r r =
    (-1)^m * ((m.choose r ^ 2 * (m+r).choose r : ℕ) : ℤ) := by
  unfold beukersSignedCoeff
  rw [show m+r+r = m+2*r by omega, pow_add, pow_mul]
  push_cast
  ring_nf

theorem momentSum_linear_form (m : ℕ) (hd : Nat.lcmUpto m ≤ 3^m) :
    ∃ a b : ℤ, |(a : ℝ)| ≤ 144^m ∧ (Nat.lcmUpto m : ℝ)^2 * beukersMomentSum m =
      (a : ℝ)*(Real.pi^2/6) + b := by
  let D := Nat.lcmUpto m
  let coeff (r s : ℕ) : ℤ := if r = s then (D : ℤ)^2 else 0
  have chooseB (r s : ℕ) : ∃ b : ℤ, r ≤ m → s ≤ m →
      (D : ℝ)^2 * Moments.moment r s = (coeff r s : ℝ) * (Real.pi^2/6) + b := by
    by_cases h : r ≤ m ∧ s ≤ m
    · obtain ⟨b,hb⟩ := Moments.moment_linear_form h.1 h.2
      refine ⟨b, fun _ _ => ?_⟩
      by_cases e : r = s <;> simpa [coeff, D, e] using hb
    · exact ⟨0, fun hr hs => (h ⟨hr,hs⟩).elim⟩
  choose b hb using chooseB
  let A : ℤ := ∑ r ∈ range (m+1), ∑ s ∈ range (m+1), beukersSignedCoeff m r s * coeff r s
  let B : ℤ := ∑ r ∈ range (m+1), ∑ s ∈ range (m+1), beukersSignedCoeff m r s * b r s
  refine ⟨A, B, ?_, ?_⟩
  · have hA : A = (-1)^m * ((D^2 *
        (∑ r ∈ range (m+1), m.choose r ^ 2 * (m+r).choose r) : ℕ) : ℤ) := by
      dsimp only [A, coeff]
      simp only [mul_ite, mul_zero, Nat.cast_mul, Nat.cast_pow, Nat.cast_sum]
      rw [Finset.mul_sum]
      simp only [Finset.mul_sum]
      apply sum_congr rfl
      intro r hr
      simp [hr, diagCoeff]
      ring
    rw [hA, Int.cast_mul, abs_mul]
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, abs_pow, abs_neg, abs_one, one_pow,
      one_mul, Int.cast_natCast, Nat.abs_cast]
    exact_mod_cast beukersScaledCoefficient_le m D hd
  · dsimp only [A, B, beukersMomentSum]
    push_cast
    simp only [mul_sum, sum_mul, ← sum_add_distrib]
    apply sum_congr rfl
    intro r hr
    apply sum_congr rfl
    intro s hs
    have h := hb r s (mem_range_succ_iff.mp hr) (mem_range_succ_iff.mp hs)
    change (D : ℝ)^2 * _ = _
    linear_combination (beukersSignedCoeff m r s : ℝ) * h

/-- Moment evaluation and Hanson's explicit lcm bound suffice for the
quantitative Beukers estimate used in the approved statement. -/
theorem forms_of_moment_identity
    (hanson : ∀ m : ℕ, 256 ≤ m → Nat.lcmUpto m ≤ 3^m)
    (identity : ∀ m : ℕ, 256 ≤ m → beukersIntegral m = beukersMomentSum m) :
    HasBeukersForms (Real.pi^2/6) := by
  intro m hm
  let D := Nat.lcmUpto m
  have hd := hanson m hm
  obtain ⟨a,b,ha,h⟩ := momentSum_linear_form m hd
  rw [← identity m hm] at h
  have ⟨lo,hi⟩ := beukersIntegral_bounds m hm
  refine ⟨a,b,ha, ?_, ?_⟩ <;> rw [← h]
  · have hD : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast Nat.lcmUpto_pos m
    apply lo.trans
    apply le_mul_of_one_le_left (by linarith [show (0:ℝ) < 1/(16*32^m) by positivity])
    change 1 ≤ (D : ℝ)^2
    nlinarith only [hD, sq_nonneg ((D:ℝ)-1)]
  · have hD : (D : ℝ) ≤ 3^m := by exact_mod_cast hd
    calc
      _ ≤ ((3:ℝ)^m)^2 * (2 / 10^m) := mul_le_mul
        (pow_le_pow_left₀ (by positivity) hD 2) hi
        (lo.trans' (by positivity)) (by positivity)
      _ = _ := by rw [← pow_mul, Nat.mul_comm m 2, pow_mul]; norm_num; ring

end A047872

end

section

open Set MeasureTheory Polynomial

namespace A047872

private noncomputable def rod (m i : ℕ) (x : ℝ) : ℝ :=
  aeval x (derivative^[i] ((X : ℤ[X]) ^ m * (1-X)^m))

private theorem rod_endpoints {m i : ℕ} (hi : i < m) : rod m i 0 = 0 ∧ rod m i 1 = 0 := by
  have h (q : ℤ[X]) (x : ℝ) (hq : aeval x q = 0)
      (hd : q ^ m ∣ (X : ℤ[X]) ^ m * (1-X)^m) : rod m i x = 0 := by
    obtain ⟨a, ha⟩ := pow_sub_dvd_iterate_derivative_of_pow_dvd i hd
    simp [rod, ha, hq, show m - i ≠ 0 by omega]
  exact ⟨h X 0 (by simp) (dvd_mul_right ..), h (1-X) 1 (by simp) (dvd_mul_left ..)⟩

private theorem rod_deriv (m i : ℕ) (x : ℝ) : HasDerivAt (rod m i) (rod m (i+1) x) x := by
  simp only [rod, Function.iterate_succ_apply']
  exact Polynomial.hasDerivAt_aeval _ _

private noncomputable def ratDer (y : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  (j.factorial : ℝ) * y ^ j * ((1-x*y)⁻¹) ^ (j+1)

private theorem ratDer_deriv (y : ℝ) (j : ℕ) (x : ℝ) (h : 1-x*y ≠ 0) :
    HasDerivAt (ratDer y j) (ratDer y (j+1) x) x := by
  have hd : HasDerivAt (fun t : ℝ => 1-t*y) (-y) x := by
    simpa using ((hasDerivAt_id x).mul_const y).const_sub (1 : ℝ)
  have hinv : HasDerivAt (fun t : ℝ => (1-t*y)⁻¹) (y*((1-x*y)⁻¹)^2) x := by
    have H := hd.inv h
    change HasDerivAt (fun t : ℝ => (1-t*y)⁻¹) (-(-y)/(1-x*y)^2) x at H
    simpa only [neg_neg, div_eq_mul_inv, inv_pow] using H
  have H := (hinv.fun_pow (j+1)).const_mul ((j.factorial : ℝ)*y^j)
  apply H.congr_deriv
  simp [ratDer, Nat.factorial_succ, pow_succ]
  ring

/-- Repeated integration by parts identifies the Legendre-polynomial inner integral
with Beukers' positive integrand. The hypothesis on y keeps its denominator nonzero. -/
theorem beukers_inner_identity (m : ℕ) {y : ℝ} (hy : y ∈ Ico 0 1) :
    (∫ x : ℝ in 0..1, aeval x (shiftedLegendre m) * (1-y)^m / (1-x*y)) =
    (-1 : ℝ)^m * ∫ x : ℝ in 0..1, beukersKernel x y ^ m / (1-x*y) := by
  have hden {x : ℝ} (hx : x ∈ uIcc (0 : ℝ) 1) : 1-x*y ≠ 0 := by
    rw [uIcc_of_le zero_le_one] at hx
    have hxy := mul_le_mul_of_nonneg_right hx.2 hy.1
    nlinarith [hy.2]
  let J (i j : ℕ) := ∫ x : ℝ in 0..1, rod m i x * ratDer y j x
  have step (i j : ℕ) (hi : i < m) : J (i+1) j = -J i (j+1) := by
    have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
      (fun x _ => rod_deriv m i x) (fun x hx => ratDer_deriv y j x (hden hx))
    have hi1 : IntervalIntegrable (rod m (i+1)) volume 0 1 :=
      (Polynomial.continuous_aeval _).intervalIntegrable ..
    have hi2 : IntervalIntegrable (ratDer y (j+1)) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      intro x hx
      exact ((ratDer_deriv y (j+1) x (hden hx)).continuousAt).continuousWithinAt
    have H := h1 hi1 hi2
    obtain ⟨h0,h1'⟩ := rod_endpoints hi
    simp only [h0,h1',zero_mul,sub_zero,zero_sub] at H
    change J i (j+1) = -J (i+1) j at H
    linarith
  have chain (i j : ℕ) (hi : i ≤ m) : J i j = (-1 : ℝ)^i * J 0 (i+j) := by
    induction i generalizing j with
    | zero => simp
    | succ i ih =>
      rw [step i j (by omega), ih (j+1) (by omega), pow_succ, show i + 1 + j = i + (j + 1) by omega]
      ring
  have H := chain m 0 (by omega)
  rw [Nat.add_zero] at H
  have hrod (x : ℝ) : rod m m x = (m.factorial : ℝ) * aeval x (shiftedLegendre m) := by
    simp [rod, ← factorial_mul_shiftedLegendre_eq]
  have hleft : J m 0 = (m.factorial : ℝ) * ∫ x : ℝ in 0..1, aeval x (shiftedLegendre m) / (1-x*y) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp [J]
    rw [hrod]
    simp [ratDer, div_eq_mul_inv, mul_assoc]
  have hright : (1-y)^m * J 0 m = (m.factorial : ℝ) *
      ∫ x : ℝ in 0..1, beukersKernel x y ^ m / (1-x*y) := by
    simp only [J, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    simp [rod, ratDer, beukersKernel, mul_pow, div_eq_mul_inv, pow_succ]
    ring
  have hL : (∫ x : ℝ in 0..1, aeval x (shiftedLegendre m) * (1-y)^m / (1-x*y)) =
      (1-y)^m * ∫ x : ℝ in 0..1, aeval x (shiftedLegendre m) / (1-x*y) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hL]
  apply mul_left_cancel₀ (by positivity : (m.factorial : ℝ) ≠ 0)
  linear_combination (1-y)^m * hleft.symm + (1-y)^m * H + (-1 : ℝ)^m * hright

open Finset

/-- Pointwise expansion of the signed Legendre integrand into monomial kernels. -/
private theorem signed_expansion (m : ℕ) (x y : ℝ) :
    (-1 : ℝ)^m * (aeval x (shiftedLegendre m) * (1-y)^m / (1-x*y)) =
      ∑ r ∈ range (m+1), ∑ s ∈ range (m+1),
        ((-1 : ℝ)^(m+r+s) * (m.choose r : ℝ) * ((m+r).choose r : ℝ) * (m.choose s : ℝ)) *
        Moments.monomialKernel r s (x,y) := by
  have leg : aeval x (shiftedLegendre m) =
      ∑ r ∈ range (m+1), (-1 : ℝ)^r * (m.choose r : ℝ) * ((m+r).choose r : ℝ) * x^r := by
    simp [shiftedLegendre, Nat.choose_symm_add (a := m), map_sum]
  have en : (1-y)^m = ∑ s ∈ range (m+1), (-1 : ℝ)^s * y^s * (m.choose s : ℝ) := by
    rw [show 1-y = -y+1 by ring, add_pow]
    apply Finset.sum_congr rfl
    intro s _
    rw [show -y = (-1)*y by ring, mul_pow, one_pow, mul_one]
  rw [leg, en]
  simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  simp only [Moments.monomialKernel, pow_add, div_eq_mul_inv]
  ring

private theorem square_integral_iterated (f : ℝ × ℝ → ℝ)
    (hf : IntegrableOn f Moments.unitSquare) :
    (∫ p in Moments.unitSquare, f p) =
        ∫ y in Icc (0 : ℝ) 1, ∫ x in Icc (0 : ℝ) 1, f (x,y) := by
  have hm : (volume : Measure (ℝ × ℝ)).restrict Moments.unitSquare =
      (volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1)) := by
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  unfold IntegrableOn at hf
  rw [hm] at hf ⊢
  exact integral_prod_symm _ hf

/-- The positive double integral equals the signed finite sum of monomial moments. -/
theorem beukers_integral_moment_expansion (m : ℕ) (hm : 256 ≤ m) :
    beukersIntegral m = ∑ r ∈ range (m+1), ∑ s ∈ range (m+1),
      ((-1 : ℝ)^(m+r+s) * (m.choose r : ℝ) * ((m+r).choose r : ℝ) * (m.choose s : ℝ)) *
        Moments.moment r s := by
  let c (r s : ℕ) := (-1 : ℝ)^(m+r+s) * (m.choose r : ℝ) * ((m+r).choose r : ℝ) * (m.choose s : ℝ)
  let F (p : ℝ × ℝ) := ∑ r ∈ range (m+1), ∑ s ∈ range (m+1), c r s * Moments.monomialKernel r s p
  have hterm (r s : ℕ) : IntegrableOn (fun p => c r s * Moments.monomialKernel r s p) Moments.unitSquare :=
    (Moments.integrable_monomialKernel r s).const_mul _
  have hi (r : ℕ) : IntegrableOn (fun p => ∑ s ∈ range (m+1), c r s * Moments.monomialKernel r s p)
      Moments.unitSquare := integrable_finsetSum _ (fun s _ => hterm r s)
  have hF : IntegrableOn F Moments.unitSquare := integrable_finsetSum _ (fun r _ => hi r)
  have hden : IntegrableOn (beukersDensity m) Moments.unitSquare := by
    by_contra h
    have hpos := (beukersIntegral_bounds m hm).1
    change 1/(16*32^m) ≤ ∫ p in Moments.unitSquare, beukersDensity m p at hpos
    rw [integral_undef h] at hpos
    have : (0 : ℝ) < 1/(16*32^m) := by positivity
    linarith
  have hI : beukersIntegral m = ∫ p in Moments.unitSquare, F p := by
    unfold beukersIntegral
    change (∫ p in Moments.unitSquare, beukersDensity m p) = _
    rw [square_integral_iterated _ hden, square_integral_iterated _ hF,
      integral_Icc_eq_integral_Ico (x := (0 : ℝ)) (y := 1),
      integral_Icc_eq_integral_Ico (x := (0 : ℝ)) (y := 1)]
    apply setIntegral_congr_fun measurableSet_Ico
    intro y hy
    dsimp only
    rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one]
    have L := beukers_inner_identity m hy
    have hsign : (-1 : ℝ)^m * (-1)^m = 1 := by rw [← mul_pow]; norm_num
    calc
      _ = (-1 : ℝ)^m * (∫ x : ℝ in 0..1, aeval x (shiftedLegendre m) * (1-y)^m/(1-x*y)) := by
        rw [L, ← mul_assoc, hsign, one_mul]; rfl
      _ = _ := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        exact fun x _ => signed_expansion m x y
  rw [hI]
  dsimp only [F]
  rw [integral_finsetSum _ (fun r _ => hi r)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [integral_finsetSum _ (fun s _ => hterm r s)]
  apply Finset.sum_congr rfl
  intro s hs
  rw [integral_const_mul, Moments.integral_monomialKernel]

/-- The Beukers moment identity in the normalization used by the rational-separation bound. -/
theorem beukers_integral_eq_momentSum (m : ℕ) (hm : 256 ≤ m) :
    beukersIntegral m = beukersMomentSum m := by
  simpa [beukersMomentSum, beukersSignedCoeff] using beukers_integral_moment_expansion m hm

end A047872

end

section

namespace A047872

/-- The entire approved statement follows from the classical quantitative
properties of the Beukers forms at ζ(2). -/
theorem ofBeukersForms (forms : HasBeukersForms (Real.pi ^ 2 / 6)) :
    type_of% @OMA.S_oeis_a047872.main := by
  intro n
  by_cases small : n < 2048
  · exact A047872Certificate.finite_target small
  · have hn : n ≠ 0 := by omega
    exact A047872Certificate.target_of_large_gap hn
      (A047872Certificate.scaled_zeta_tail_lt_three hn)
      (largeIndexGap forms n (by omega))

end A047872

/-- Bill McEachen's floor formula for OEIS A047872. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a047872.main := by
  apply A047872.ofBeukersForms
  exact A047872.forms_of_moment_identity (fun m _ => A047872.hansonBound m)
    A047872.beukers_integral_eq_momentSum

end
