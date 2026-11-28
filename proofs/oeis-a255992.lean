import OMAStatements.S_oeis_a255992

-- Problem: A255992: T(n,k)=Number of length n+k 0..1 arrays with at most one downstep in every k consecutive neighbor pairs.
-- Upstream: formal-conjectures statements/oeis-a255992.lean:0 (declaration OMA.S_oeis_a255992.main)
-- Credit: @m-miyawaki-m (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Proof sketch. `F_c`, `G_c` = generating functions of `countFrom k false c`, `countFrom k true c`.
Splitting off the first bit: `F_(c+1) = 1 + X(F_c + G_c)`, `F_0 = 1 + X(F_0 + G_0)`,
`G_(c+1) = 1 + X G_c`, `G_0 = 1 + X(G_0 + F_(k-1))`; solving gives the generating function.
For the binomial formula put `Y = (1-X)⁻²`, `V = X^k((k-1)-(k-2)X)`: then
`(F_0 - Y - Σ_(s<L) X²V^sY^(s+2)) · (1-X)²Q = X²(VY)^L`, so coefficients agree below `kL+2`,
and the coefficient of `X²V^sY^(s+2)` is the inner binomial sum.
-/

namespace OMA.Sol_oeis_a255992

open PowerSeries OMA.S_oeis_a255992

/-! first-bit split -/

lemma countFrom_zero (k : ℕ) (p : Bool) (c : ℕ) : countFrom k p c 0 = 1 := by
  simp [countFrom, scan]

lemma countFrom_succ (k : ℕ) (p : Bool) (c m : ℕ) :
    countFrom k p c (m + 1) =
      (if p = true ∧ c ≠ 0 then 0 else countFrom k false (if p then k - 1 else c - 1) m) +
        countFrom k true (c - 1) m := by
  unfold countFrom
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
  rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Bool)).sum_comp]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, scan]
  cases p <;> by_cases hc : c = 0 <;> simp [hc, add_comm]

noncomputable def Fs (k c : ℕ) : PowerSeries ℤ := PowerSeries.mk fun m => (countFrom k false c m : ℤ)
noncomputable def Gs (k c : ℕ) : PowerSeries ℤ := PowerSeries.mk fun m => (countFrom k true c m : ℤ)

lemma Fs_succ (k c : ℕ) : Fs k (c + 1) = 1 + X * (Fs k c + Gs k c) := by
  ext n
  cases n with
  | zero => simp [Fs, countFrom_zero]
  | succ n =>
    rw [map_add, coeff_succ_X_mul, map_add]
    simp [Fs, Gs, countFrom_succ, coeff_one]

lemma Fs_zero (k : ℕ) : Fs k 0 = 1 + X * (Fs k 0 + Gs k 0) := by
  ext n
  cases n with
  | zero => simp [Fs, countFrom_zero]
  | succ n =>
    rw [map_add, coeff_succ_X_mul, map_add]
    simp [Fs, Gs, countFrom_succ, coeff_one]

lemma Gs_succ (k c : ℕ) : Gs k (c + 1) = 1 + X * Gs k c := by
  ext n
  cases n with
  | zero => simp [Gs, countFrom_zero]
  | succ n =>
    rw [map_add, coeff_succ_X_mul]
    simp [Gs, countFrom_succ, coeff_one]

lemma Gs_zero (k : ℕ) : Gs k 0 = 1 + X * (Gs k 0 + Fs k (k - 1)) := by
  ext n
  cases n with
  | zero => simp [Gs, countFrom_zero]
  | succ n =>
    rw [map_add, coeff_succ_X_mul, map_add]
    simp [Fs, Gs, countFrom_succ, coeff_one, add_comm]

lemma G_closed (k c : ℕ) : (1 - X) * Gs k c = 1 - X ^ c + (1 - X) * X ^ c * Gs k 0 := by
  induction c with
  | zero => ring
  | succ c ih => rw [Gs_succ]; linear_combination X * ih

lemma F_closed (k c : ℕ) : (1 - X) ^ 2 * Fs k c =
    1 - ((c : PowerSeries ℤ) + 1) * X ^ c + (c : PowerSeries ℤ) * X ^ (c + 1) +
      (1 - X) ^ 2 * X ^ c * ((c : PowerSeries ℤ) * Gs k 0 + Fs k 0) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Fs_succ]
    have hG := G_closed k c
    push_cast
    linear_combination X * ih + X * (1 - X) * hG

theorem gf : GeneratingFunction := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hmk : PowerSeries.mk (fun m => (count (j + 1) m : ℤ)) = Fs (j + 1) 0 := rfl
  rw [hmk]
  have E1 := Fs_zero (j + 1)
  have E2 := Gs_zero (j + 1)
  have E3 := F_closed (j + 1) j
  simp only [Nat.add_sub_cancel] at E2
  simp only [zsmul_eq_mul]
  push_cast
  linear_combination (-(X - 1) ^ 2 * (X * X ^ j * (j : PowerSeries ℤ) + X - 1)) * E1
    + X * (X - 1) ^ 2 * E2 + X ^ 2 * E3

/-! BinomialFormula -/

noncomputable def Y : PowerSeries ℤ := (invOneSubPow ℤ 2).val

lemma Y_mul : Y * (1 - X) ^ 2 = 1 := by
  have h := (invOneSubPow ℤ 2).val_inv
  rwa [invOneSubPow_inv_eq_one_sub_pow] at h

lemma Y_pow (s : ℕ) : (invOneSubPow ℤ (2 * s + 4)).val = Y ^ (s + 2) := by
  rw [Y, ← Units.val_pow_eq_pow_val, show 2 * s + 4 = 2 * (s + 2) by ring,
    invOneSubPow_eq_inv_one_sub_pow, invOneSubPow_eq_inv_one_sub_pow, ← pow_mul]

/-- numerator of `V`. -/
noncomputable def Vn (k : ℕ) : PowerSeries ℤ :=
  X ^ k * (((k : PowerSeries ℤ) - 1) - ((k : PowerSeries ℤ) - 2) * X)

noncomputable def R (k L : ℕ) : PowerSeries ℤ :=
  Y + ∑ s ∈ Finset.range L, X ^ 2 * Vn k ^ s * Y ^ (s + 2)

lemma trunc_identity (k L : ℕ) (hk : 1 ≤ k) :
    (Fs k 0 - R k L) * ((1 - X) ^ 2 * ((1 - X) ^ 2 - Vn k)) = X ^ 2 * (Vn k * Y) ^ L := by
  have hGF := gf k hk
  have hmk : PowerSeries.mk (fun m => (count k m : ℤ)) = Fs k 0 := rfl
  rw [hmk] at hGF
  simp only [zsmul_eq_mul] at hGF
  push_cast at hGF
  have e := Y_mul
  set S := ∑ s ∈ Finset.range L, (Vn k * Y) ^ s with hSdef
  have hS : S * (1 - Vn k * Y) = 1 - (Vn k * Y) ^ L := geom_sum_mul_neg _ _
  have hR : R k L = Y + X ^ 2 * Y ^ 2 * S := by
    rw [R, hSdef, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [hR]
  have hQ : (1 - X) ^ 2 - Vn k = 1 - 2 * X + X ^ 2 - ((k : PowerSeries ℤ) - 1) * X ^ k +
      ((k : PowerSeries ℤ) - 2) * X ^ (k + 1) := by rw [Vn]; ring
  rw [← hQ] at hGF
  linear_combination hGF - ((1 - X) ^ 2 - Vn k) * e - X ^ 2 * Y * S * ((1 - X) ^ 2 - Vn k) * e
    - X ^ 2 * S * e - X ^ 2 * hS - hQ

noncomputable def Pk (k : ℕ) : PowerSeries ℤ :=
  ((k : PowerSeries ℤ) - 1) - ((k : PowerSeries ℤ) - 2) * X

lemma coeff_eq_R (k L M : ℕ) (hk : 1 ≤ k) (hM : M < k * L + 2) :
    coeff M (Fs k 0) = coeff M (R k L) := by
  have h := trunc_identity k L hk
  have hu : IsUnit ((1 - X) ^ 2 * ((1 - X) ^ 2 - Vn k) : PowerSeries ℤ) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have : k ≠ 0 := by omega
    simp [Vn, this]
  have hd : (X : PowerSeries ℤ) ^ (k * L + 2) ∣ (Fs k 0 - R k L) := by
    rw [← hu.dvd_mul_right, h]
    refine ⟨(Pk k * Y) ^ L, ?_⟩
    rw [Vn, ← Pk, mul_assoc, mul_pow, mul_pow, ← pow_mul]
    ring
  have := (PowerSeries.X_pow_dvd_iff.mp hd) M hM
  rw [map_sub, sub_eq_zero] at this
  exact this

lemma coeff_Y (M : ℕ) : coeff M Y = (M : ℤ) + 1 := by
  rw [Y, show (2 : ℕ) = 1 + 1 from rfl, invOneSubPow_val_succ_eq_mk_add_choose, coeff_mk]
  simp [add_comm]

lemma coeff_I (s r : ℕ) : coeff r (Y ^ (s + 2)) = ((2 * s + 3 + r).choose (2 * s + 3) : ℤ) := by
  rw [← Y_pow, show 2 * s + 4 = (2 * s + 3) + 1 by ring, invOneSubPow_val_succ_eq_mk_add_choose,
    coeff_mk]

lemma Pk_pow (k s : ℕ) : Pk k ^ s = ∑ j ∈ Finset.range (s + 1),
    C ((-1 : ℤ) ^ j * (s.choose j : ℤ) * ((k : ℤ) - 1) ^ (s - j) * ((k : ℤ) - 2) ^ j) * X ^ j := by
  have : Pk k = C (-((k : ℤ) - 2)) * X + C ((k : ℤ) - 1) := by
    simp only [Pk, map_neg, map_sub, map_natCast, map_ofNat, map_one]; ring
  rw [this, add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_pow, ← map_pow, map_mul, map_natCast]
  rw [show (-((k : ℤ) - 2)) ^ j = (-1) ^ j * ((k : ℤ) - 2) ^ j by rw [neg_pow]]
  simp only [map_mul]
  ring

lemma T_coeff (k s M : ℕ) :
    coeff M (X ^ 2 * Vn k ^ s * Y ^ (s + 2)) =
      if 2 + k * s ≤ M then
        ∑ j ∈ Finset.range (s + 1),
          (-1 : ℤ) ^ j * (s.choose j : ℤ) * ((k : ℤ) - 1) ^ (s - j) * ((k : ℤ) - 2) ^ j *
            (((M - 2 - k * s + 2 * s + 3 - j).choose (2 * s + 3) : ℕ) : ℤ)
      else 0 := by
  have hre : X ^ 2 * Vn k ^ s * Y ^ (s + 2) = X ^ (2 + k * s) * (Pk k ^ s * Y ^ (s + 2)) := by
    rw [Vn, ← Pk, mul_pow, ← pow_mul, pow_add]; ring
  rw [hre, coeff_X_pow_mul']
  split_ifs with h
  · rw [Pk_pow, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_I]
    split_ifs with hj
    · congr 2
      congr 1
      rw [Nat.sub_sub]; omega
    · rw [Nat.choose_eq_zero_of_lt (n := M - 2 - k * s + 2 * s + 3 - j) (k := 2 * s + 3)
        (by rw [Nat.sub_sub]; omega)]
      simp
  · rfl

theorem bf : BinomialFormula := by
  intro n k hn hk
  have hcoef : (count k (n + k) : ℤ) = coeff (n + k) (Fs k 0) := by simp [Fs, count]
  rw [hcoef, coeff_eq_R k (n + k + 1) (n + k) hk (by nlinarith), R, map_add, coeff_Y, map_sum]
  simp_rw [T_coeff]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  push_cast
  congr 1
  have hfil : (Finset.range (n + k + 1)).filter (fun s => 2 + k * s ≤ n + k) =
      Finset.range ((n + k - 2) / k + 1) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range]
    have hk0 : 0 < k := by omega
    rw [show s < (n + k - 2) / k + 1 ↔ s ≤ (n + k - 2) / k from Nat.lt_succ_iff,
      Nat.le_div_iff_mul_le hk0, mul_comm s k]
    constructor
    · rintro ⟨-, h⟩; omega
    · intro h
      have : s ≤ k * s := Nat.le_mul_of_pos_left s (by omega)
      omega
  rw [hfil]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm s k]

end OMA.Sol_oeis_a255992

theorem OMA.solution : type_of% @OMA.S_oeis_a255992.main :=
  ⟨OMA.Sol_oeis_a255992.gf, OMA.Sol_oeis_a255992.bf⟩
