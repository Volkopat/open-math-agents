import OMAStatements.S_oeis_a126617

namespace OMA.P_oeis_a126617

open OMA.S_oeis_a126617

/-! ### Part 1: PowerSeries multiplication and `invUnit1` arithmetic -/

private lemma coeff_mul_eq_sum_range (f g : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (f * g) =
      ∑ i ∈ Finset.range (n + 1), PowerSeries.coeff i f * PowerSeries.coeff (n - i) g := by
  rw [PowerSeries.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j g) n

private lemma coeff_X_mul_zero (f : PowerSeries ℚ) :
    PowerSeries.coeff 0 (PowerSeries.X * f) = 0 := by
  rw [coeff_mul_eq_sum_range]
  simp

private lemma coeff_X_mul_succ (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (n + 1) (PowerSeries.X * f) = PowerSeries.coeff n f := by
  rw [coeff_mul_eq_sum_range, Finset.sum_eq_single 1]
  · simp
  · intro b _ hb
    rw [PowerSeries.coeff_X, if_neg hb, zero_mul]
  · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))

private lemma coeff_invOneSub (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (invOneSub f) = invOneSubAux f n := by
  unfold invOneSub; simp

private lemma one_sub_X_mul_invOneSub (f : PowerSeries ℚ) :
    (1 - PowerSeries.X * f) * invOneSub f = 1 := by
  ext n
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
          PowerSeries.coeff i f * invOneSubAux f (m - i) :=
      Finset.sum_congr rfl (fun i _ => by rw [coeff_invOneSub])
    rw [hsum, sub_self]

private lemma mul_invUnit1 (f : PowerSeries ℚ) (hc0 : PowerSeries.coeff 0 f = 1) :
    f * invUnit1 f = 1 := by
  have h1 : 1 - PowerSeries.X * PowerSeries.mk (fun n => -PowerSeries.coeff (n + 1) f) = f := by
    ext n
    rw [map_sub]
    cases n with
    | zero => rw [PowerSeries.coeff_one, if_pos rfl, coeff_X_mul_zero, sub_zero, hc0]
    | succ m =>
      rw [PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero m), coeff_X_mul_succ,
        PowerSeries.coeff_mk, zero_sub, neg_neg]
  unfold invUnit1
  conv_lhs => arg 1; rw [← h1]
  exact one_sub_X_mul_invOneSub _

private lemma coeff_zero_invUnit1 (f : PowerSeries ℚ) :
    PowerSeries.coeff 0 (invUnit1 f) = 1 := by
  unfold invUnit1; rw [coeff_invOneSub]; simp [invOneSubAux]

private lemma invUnit1_unique (f g : PowerSeries ℚ) (hc0 : PowerSeries.coeff 0 f = 1)
    (h : f * g = 1) : g = invUnit1 f := by
  have h1 := mul_invUnit1 f hc0
  calc
    g = 1 * g := (one_mul g).symm
    _ = (f * invUnit1 f) * g := by rw [h1]
    _ = invUnit1 f * (f * g) := by ring
    _ = invUnit1 f * 1 := by rw [h]
    _ = invUnit1 f := mul_one _

private lemma invOneSub_congr_lt (f g : PowerSeries ℚ) (m : ℕ)
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

private lemma invUnit1_congr_le (f g : PowerSeries ℚ) (m : ℕ)
    (h : ∀ i ≤ m, PowerSeries.coeff i f = PowerSeries.coeff i g) :
    ∀ n ≤ m, PowerSeries.coeff n (invUnit1 f) = PowerSeries.coeff n (invUnit1 g) := by
  unfold invUnit1
  refine invOneSub_congr_lt _ _ m (fun i hi => ?_)
  simp only [PowerSeries.coeff_mk]
  rw [h (i + 1) (by omega)]

private lemma mul_congr_le (f1 f2 g1 g2 : PowerSeries ℚ) (m : ℕ)
    (hf : ∀ i ≤ m, PowerSeries.coeff i f1 = PowerSeries.coeff i f2)
    (hg : ∀ i ≤ m, PowerSeries.coeff i g1 = PowerSeries.coeff i g2) :
    ∀ n ≤ m, PowerSeries.coeff n (f1 * g1) = PowerSeries.coeff n (f2 * g2) := by
  intro n hn
  rw [coeff_mul_eq_sum_range, coeff_mul_eq_sum_range]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hile : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [hf i (by omega), hg (n - i) (by omega)]

/-! ### Part 2: Exact Bell-shift recurrence `seqP (p + k) (n + 1) = (p + k) * seqP (p + k) n + seqP (p + k + 1) n` -/

private lemma seqP_zero (q : ℚ) : seqP q 0 = 1 := by
  simp [seqP, bellNum]

private lemma seqP_succ (q : ℚ) (n : ℕ) :
    seqP q (n + 1) = q * seqP q n + seqP (q + 1) n := by
  unfold seqP
  -- Rewrite seqP q (n + 1) using Pascal's identity C(n+1, i) = C(n, i) + C(n, i-1)
  have hlhs : ∑ i ∈ Finset.range (n + 2),
        q ^ (n + 1 - i) * (bellNum i : ℚ) * (Nat.choose (n + 1) i : ℚ) =
      q * (∑ i ∈ Finset.range (n + 1), q ^ (n - i) * (bellNum i : ℚ) * (Nat.choose n i : ℚ)) +
      ∑ i ∈ Finset.range (n + 1), q ^ (n - i) * (bellNum (i + 1) : ℚ) * (Nat.choose n i : ℚ) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
    have hsplit : ∑ i ∈ Finset.range (n + 1),
          q ^ (n + 1 - (i + 1)) * (bellNum (i + 1) : ℚ) * (Nat.choose (n + 1) (i + 1) : ℚ) =
        (∑ i ∈ Finset.range (n + 1),
          q ^ (n - i) * (bellNum (i + 1) : ℚ) * (Nat.choose n (i + 1) : ℚ)) +
        (∑ i ∈ Finset.range (n + 1),
          q ^ (n - i) * (bellNum (i + 1) : ℚ) * (Nat.choose n i : ℚ)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hsub : n + 1 - (i + 1) = n - i := by omega
      rw [hsub, Nat.choose_succ_succ]
      push_cast
      ring
    rw [hsplit]
    have hfirst : (∑ i ∈ Finset.range (n + 1),
          q ^ (n - i) * (bellNum (i + 1) : ℚ) * (Nat.choose n (i + 1) : ℚ)) +
        q ^ (n + 1) * (bellNum 0 : ℚ) =
        q * (∑ i ∈ Finset.range (n + 1), q ^ (n - i) * (bellNum i : ℚ) * (Nat.choose n i : ℚ)) := by
      rw [Finset.sum_range_succ]
      have hzero : Nat.choose n (n + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp only [hzero, Nat.cast_zero, mul_zero, add_zero]
      rw [Finset.mul_sum, Finset.sum_range_succ']
      simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
      have h1 : q * (q ^ n * (bellNum 0 : ℚ)) = q ^ (n + 1) * (bellNum 0 : ℚ) := by
        rw [pow_succ']; ring
      rw [h1]
      congr 1
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hilt : i < n := Finset.mem_range.mp hi
      have hpow : q ^ (n - i) = q * q ^ (n - (i + 1)) := by
        rw [← pow_succ', show n - (i + 1) + 1 = n - i by omega]
      rw [hpow]; ring
    linarith
  rw [hlhs]
  congr 1
  -- Show ∑_{i=0}^n q^(n-i) * B(i+1) * C(n, i) = ∑_{j=0}^n (q+1)^(n-j) * B(j) * C(n, j)
  have hbell : ∀ i : ℕ, (bellNum (i + 1) : ℚ) =
      ∑ j ∈ Finset.range (i + 1), (Nat.choose i j : ℚ) * (bellNum j : ℚ) := by
    intro i
    simp only [bellNum, Nat.cast_sum, Nat.cast_mul]
    exact Fin.sum_univ_eq_sum_range (fun j => (Nat.choose i j : ℚ) * (bellNum j : ℚ)) (i + 1)
  simp_rw [hbell]
  have hswap : ∑ i ∈ Finset.range (n + 1),
        q ^ (n - i) * (∑ j ∈ Finset.range (i + 1), (Nat.choose i j : ℚ) * (bellNum j : ℚ)) *
          (Nat.choose n i : ℚ) =
      ∑ j ∈ Finset.range (n + 1),
        (∑ i ∈ Finset.range (n + 1),
          if j ≤ i then q ^ (n - i) * (Nat.choose i j : ℚ) * (bellNum j : ℚ) * (Nat.choose n i : ℚ)
          else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hile : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Finset.mul_sum, Finset.sum_mul]
    have hsub : Finset.range (i + 1) ⊆ Finset.range (n + 1) := Finset.range_mono (by omega)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      have hjle : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [if_pos hjle]; ring
    · intro j _ hjnot
      have hgt : ¬ j ≤ i := by simp only [Finset.mem_range] at hjnot; omega
      rw [if_neg hgt]
  rw [hswap]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  -- Reindex i = j + r, r ∈ range (n - j + 1) via `sum_filter`
  have hfilter : (∑ i ∈ Finset.range (n + 1),
        if j ≤ i then q ^ (n - i) * (Nat.choose i j : ℚ) * (bellNum j : ℚ) * (Nat.choose n i : ℚ)
        else 0) =
      ∑ i ∈ (Finset.range (n + 1)).filter (fun i => j ≤ i),
        q ^ (n - i) * (Nat.choose i j : ℚ) * (bellNum j : ℚ) * (Nat.choose n i : ℚ) := by
    rw [Finset.sum_filter]
  rw [hfilter]
  have hbij : ∑ i ∈ (Finset.range (n + 1)).filter (fun i => j ≤ i),
        q ^ (n - i) * (Nat.choose i j : ℚ) * (bellNum j : ℚ) * (Nat.choose n i : ℚ) =
      ∑ r ∈ Finset.range (n - j + 1),
        q ^ (n - j - r) * (Nat.choose (n - j) r : ℚ) * (bellNum j : ℚ) * (Nat.choose n j : ℚ) := by
    symm
    refine Finset.sum_nbij (fun r => j + r) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_range] at hr ⊢
      omega
    · intro r1 _ r2 _ h; dsimp only at h; omega
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
      refine ⟨i - j, by simp only [Finset.mem_coe, Finset.mem_range]; omega, ?_⟩
      dsimp only; omega
    · intro r hr
      simp only [Finset.mem_range] at hr
      have hsub : n - (j + r) = n - j - r := by omega
      have hch : Nat.choose n (j + r) * Nat.choose (j + r) j =
          Nat.choose n j * Nat.choose (n - j) r := by
        have h1 : Nat.choose n (j + r) * Nat.choose (j + r) j =
            Nat.choose n j * Nat.choose (n - j) (j + r - j) :=
          Nat.choose_mul (n := n) (k := j + r) (s := j) (by omega)
        have h2 : j + r - j = r := by omega
        rw [h2] at h1
        exact h1
      have hchq : (Nat.choose n (j + r) : ℚ) * (Nat.choose (j + r) j : ℚ) =
          (Nat.choose n j : ℚ) * (Nat.choose (n - j) r : ℚ) := by
        exact_mod_cast hch
      rw [hsub]
      linear_combination -(q ^ (n - j - r) * (bellNum j : ℚ)) * hchq
  rw [hbij]
  have hbin : (1 + q) ^ (n - j) =
      ∑ r ∈ Finset.range (n - j + 1), (1 : ℚ) ^ r * q ^ (n - j - r) * (Nat.choose (n - j) r : ℚ) :=
    add_pow 1 q (n - j)
  have hbin2 : (q + 1) ^ (n - j) =
      ∑ r ∈ Finset.range (n - j + 1), q ^ (n - j - r) * (Nat.choose (n - j) r : ℚ) := by
    rw [add_comm q 1, hbin]
    refine Finset.sum_congr rfl (fun r _ => by simp)
  rw [hbin2, Finset.sum_mul, Finset.sum_mul]

/-! ### Part 3: Exact generating functions `U`, `S`, and continued-fraction tails `G` -/

private noncomputable def uSeries (p : ℚ) (k : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => seqP (p + (k : ℚ)) n)

private noncomputable def sSeries (p : ℚ) (k : ℕ) : PowerSeries ℚ :=
  1 + PowerSeries.X * uSeries p k

private lemma coeff_zero_sSeries (p : ℚ) (k : ℕ) :
    PowerSeries.coeff 0 (sSeries p k) = 1 := by
  unfold sSeries
  rw [map_add, PowerSeries.coeff_one, if_pos rfl, coeff_X_mul_zero, add_zero]

private lemma coeff_succ_sSeries (p : ℚ) (k n : ℕ) :
    PowerSeries.coeff (n + 1) (sSeries p k) = seqP (p + (k : ℚ)) n := by
  unfold sSeries uSeries
  rw [map_add, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n), zero_add, coeff_X_mul_succ,
    PowerSeries.coeff_mk]

private lemma sSeries_rec (p : ℚ) (k : ℕ) :
    (1 - PowerSeries.C (p + (k : ℚ)) * PowerSeries.X) * (sSeries p k - 1) =
      PowerSeries.X * sSeries p (k + 1) := by
  ext n
  have hsub : sSeries p k - 1 = PowerSeries.X * uSeries p k := by
    unfold sSeries; ring
  rw [hsub]
  cases n with
  | zero =>
    rw [sub_mul, one_mul, map_sub, coeff_X_mul_zero, mul_assoc,
      PowerSeries.coeff_C_mul, coeff_X_mul_zero, mul_zero, sub_zero, coeff_X_mul_zero]
  | succ m =>
    rw [sub_mul, one_mul, map_sub, coeff_X_mul_succ, mul_assoc, PowerSeries.coeff_C_mul,
      coeff_X_mul_succ, coeff_X_mul_succ]
    cases m with
    | zero =>
      rw [coeff_X_mul_zero, mul_zero, sub_zero, coeff_zero_sSeries]
      unfold uSeries; rw [PowerSeries.coeff_mk, seqP_zero]
    | succ r =>
      rw [coeff_X_mul_succ, coeff_succ_sSeries]
      unfold uSeries
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
      have hcast : p + ((k + 1 : ℕ) : ℚ) = (p + (k : ℚ)) + 1 := by push_cast; ring
      rw [hcast, seqP_succ (p + (k : ℚ)) r]
      ring

/-- Exact continued-fraction tail `G_p(k) = X + (1 - (k - 1 + p)*X) / S_p(k)`. -/
private noncomputable def gSeries (p : ℚ) (k : ℕ) : PowerSeries ℚ :=
  PowerSeries.X + (1 - PowerSeries.C ((k : ℚ) - 1 + p) * PowerSeries.X) * invUnit1 (sSeries p k)

private lemma coeff_zero_gSeries (p : ℚ) (k : ℕ) :
    PowerSeries.coeff 0 (gSeries p k) = 1 := by
  unfold gSeries
  rw [map_add, PowerSeries.coeff_X, if_neg (by decide : (0 : ℕ) ≠ 1), zero_add,
    sub_mul, one_mul, map_sub, coeff_zero_invUnit1, mul_assoc, PowerSeries.coeff_C_mul,
    coeff_X_mul_zero, mul_zero, sub_zero]

private lemma gSeries_step (p : ℚ) (k : ℕ) :
    gSeries p k =
      1 + PowerSeries.C (2 - p - (k : ℚ)) * PowerSeries.X +
        PowerSeries.X * (PowerSeries.C ((k : ℚ) - 1 + p) * PowerSeries.X - 1) *
          invUnit1 (gSeries p (k + 1)) := by
  have hinvS1 : sSeries p (k + 1) * invUnit1 (sSeries p (k + 1)) = 1 :=
    mul_invUnit1 (sSeries p (k + 1)) (coeff_zero_sSeries p (k + 1))
  have hinvS0 : sSeries p k * invUnit1 (sSeries p k) = 1 :=
    mul_invUnit1 (sSeries p k) (coeff_zero_sSeries p k)
  have hinvG1 : gSeries p (k + 1) * invUnit1 (gSeries p (k + 1)) = 1 :=
    mul_invUnit1 (gSeries p (k + 1)) (coeff_zero_gSeries p (k + 1))
  have hrec := sSeries_rec p k
  -- Step 1: (sSeries p k - 1) * (gSeries p (k + 1) - X) = X
  have hg1_sub : gSeries p (k + 1) - PowerSeries.X =
      (1 - PowerSeries.C (p + (k : ℚ)) * PowerSeries.X) * invUnit1 (sSeries p (k + 1)) := by
    unfold gSeries
    have hcoeff : ((k + 1 : ℕ) : ℚ) - 1 + p = p + (k : ℚ) := by push_cast; ring
    rw [hcoeff]; ring
  have hkey : sSeries p k * (gSeries p (k + 1) - PowerSeries.X) = gSeries p (k + 1) := by
    have hprod : (sSeries p k - 1) * (gSeries p (k + 1) - PowerSeries.X) = PowerSeries.X := by
      calc
        (sSeries p k - 1) * (gSeries p (k + 1) - PowerSeries.X)
          = ((1 - PowerSeries.C (p + (k : ℚ)) * PowerSeries.X) * (sSeries p k - 1)) *
              invUnit1 (sSeries p (k + 1)) := by rw [hg1_sub]; ring
        _ = (PowerSeries.X * sSeries p (k + 1)) * invUnit1 (sSeries p (k + 1)) := by rw [hrec]
        _ = PowerSeries.X * (sSeries p (k + 1) * invUnit1 (sSeries p (k + 1))) := by ring
        _ = PowerSeries.X * 1 := by rw [hinvS1]
        _ = PowerSeries.X := mul_one _
    linear_combination hprod
  -- Step 2: invUnit1 (sSeries p k) = 1 - X * invUnit1 (gSeries p (k + 1))
  have hinv_eq : invUnit1 (sSeries p k) = 1 - PowerSeries.X * invUnit1 (gSeries p (k + 1)) := by
    have hmul : sSeries p k * (1 - PowerSeries.X * invUnit1 (gSeries p (k + 1))) = 1 := by
      calc
        sSeries p k * (1 - PowerSeries.X * invUnit1 (gSeries p (k + 1)))
          = sSeries p k * ((gSeries p (k + 1) - PowerSeries.X) * invUnit1 (gSeries p (k + 1))) := by
              rw [sub_mul, hinvG1]
        _ = (sSeries p k * (gSeries p (k + 1) - PowerSeries.X)) * invUnit1 (gSeries p (k + 1)) := by
              ring
        _ = gSeries p (k + 1) * invUnit1 (gSeries p (k + 1)) := by rw [hkey]
        _ = 1 := hinvG1
    exact (invUnit1_unique (sSeries p k) _ (coeff_zero_sSeries p k) hmul).symm
  -- Step 3: substitute hinv_eq into gSeries p k
  conv_lhs => unfold gSeries
  rw [hinv_eq]
  have hc_lin : PowerSeries.C (2 - p - (k : ℚ)) = 1 - PowerSeries.C ((k : ℚ) - 1 + p) := by
    rw [← map_one PowerSeries.C, ← map_sub]
    congr 1; ring
  rw [hc_lin]
  ring

private lemma cfFold_gSeries (p : ℚ) (k d : ℕ) :
    cfFold p k d (gSeries p (k + d)) = gSeries p k := by
  induction d generalizing k with
  | zero => simp [cfFold]
  | succ d ih =>
    simp only [cfFold]
    have h1 := ih (k + 1)
    rw [show k + 1 + d = k + (d + 1) by omega] at h1
    rw [h1]
    exact (gSeries_step p k).symm

private lemma cfFold_congr_c0 (p : ℚ) (k d : ℕ) (t1 t2 : PowerSeries ℚ)
    (hc0 : PowerSeries.coeff 0 t1 = PowerSeries.coeff 0 t2) :
    ∀ n ≤ d, PowerSeries.coeff n (cfFold p k d t1) = PowerSeries.coeff n (cfFold p k d t2) := by
  induction d generalizing k with
  | zero =>
    intro n hn
    have : n = 0 := by omega
    subst this
    simpa [cfFold] using hc0
  | succ d ih =>
    intro n hn
    simp only [cfFold, map_add]
    congr 1
    have hrec : ∀ i ≤ d, PowerSeries.coeff i (cfFold p (k + 1) d t1) =
        PowerSeries.coeff i (cfFold p (k + 1) d t2) := ih (k + 1)
    have hinv : ∀ i ≤ d,
        PowerSeries.coeff i (invUnit1 (cfFold p (k + 1) d t1)) =
          PowerSeries.coeff i (invUnit1 (cfFold p (k + 1) d t2)) :=
      invUnit1_congr_le _ _ d hrec
    cases n with
    | zero =>
      rw [mul_assoc, coeff_X_mul_zero, mul_assoc, coeff_X_mul_zero]
    | succ m =>
      rw [mul_assoc, coeff_X_mul_succ, mul_assoc, coeff_X_mul_succ]
      exact mul_congr_le _ _ _ _ d (fun _ _ => rfl) hinv m (by omega)

private lemma cfApprox_exact (p : ℚ) :
    (1 + PowerSeries.C (1 - p) * PowerSeries.X) * invUnit1 (gSeries p 0 - PowerSeries.X) =
      sSeries p 0 := by
  have hinvS0 : sSeries p 0 * invUnit1 (sSeries p 0) = 1 :=
    mul_invUnit1 (sSeries p 0) (coeff_zero_sSeries p 0)
  have hg0 : gSeries p 0 - PowerSeries.X =
      (1 + PowerSeries.C (1 - p) * PowerSeries.X) * invUnit1 (sSeries p 0) := by
    unfold gSeries
    have hc : PowerSeries.C ((0 : ℕ) - 1 + p : ℚ) = -PowerSeries.C (1 - p) := by
      rw [← map_neg]; congr 1; push_cast; ring
    rw [hc]; ring
  have hc0 : PowerSeries.coeff 0 (gSeries p 0 - PowerSeries.X) = 1 := by
    rw [map_sub, coeff_zero_gSeries, PowerSeries.coeff_X, if_neg (by decide : (0 : ℕ) ≠ 1), sub_zero]
  have hinvG0 : (gSeries p 0 - PowerSeries.X) * invUnit1 (gSeries p 0 - PowerSeries.X) = 1 :=
    mul_invUnit1 _ hc0
  calc
    (1 + PowerSeries.C (1 - p) * PowerSeries.X) * invUnit1 (gSeries p 0 - PowerSeries.X)
      = sSeries p 0 * (((1 + PowerSeries.C (1 - p) * PowerSeries.X) * invUnit1 (sSeries p 0)) *
          invUnit1 (gSeries p 0 - PowerSeries.X)) := by
          calc
            (1 + PowerSeries.C (1 - p) * PowerSeries.X) * invUnit1 (gSeries p 0 - PowerSeries.X)
              = 1 * ((1 + PowerSeries.C (1 - p) * PowerSeries.X) * invUnit1 (gSeries p 0 - PowerSeries.X)) :=
                (one_mul _).symm
            _ = (sSeries p 0 * invUnit1 (sSeries p 0)) *
                  ((1 + PowerSeries.C (1 - p) * PowerSeries.X) * invUnit1 (gSeries p 0 - PowerSeries.X)) := by
                rw [hinvS0]
            _ = sSeries p 0 * (((1 + PowerSeries.C (1 - p) * PowerSeries.X) * invUnit1 (sSeries p 0)) *
                  invUnit1 (gSeries p 0 - PowerSeries.X)) := by ring
    _ = sSeries p 0 * ((gSeries p 0 - PowerSeries.X) * invUnit1 (gSeries p 0 - PowerSeries.X)) := by
          rw [← hg0]
    _ = sSeries p 0 * 1 := by rw [hinvG0]
    _ = sSeries p 0 := mul_one _

theorem solution :
    ∀ (p : ℚ) (n d : ℕ), n + 1 ≤ d →
      PowerSeries.coeff 0 (cfApprox p d) = 1 ∧
      PowerSeries.coeff (n + 1) (cfApprox p d) = seqP p n := by
  intro p n d hd
  have hc0_tail : PowerSeries.coeff 0 (1 : PowerSeries ℚ) =
      PowerSeries.coeff 0 (gSeries p (0 + d)) := by
    rw [PowerSeries.coeff_one, if_pos rfl, coeff_zero_gSeries]
  have hcf : ∀ i ≤ d, PowerSeries.coeff i (cfFold p 0 d 1) = PowerSeries.coeff i (gSeries p 0) := by
    intro i hi
    rw [← cfFold_gSeries p 0 d]
    exact cfFold_congr_c0 p 0 d 1 (gSeries p (0 + d)) hc0_tail i hi
  have hsub : ∀ i ≤ d,
      PowerSeries.coeff i (cfFold p 0 d 1 - PowerSeries.X) =
        PowerSeries.coeff i (gSeries p 0 - PowerSeries.X) := by
    intro i hi
    rw [map_sub, map_sub, hcf i hi]
  have hinv : ∀ i ≤ d,
      PowerSeries.coeff i (invUnit1 (cfFold p 0 d 1 - PowerSeries.X)) =
        PowerSeries.coeff i (invUnit1 (gSeries p 0 - PowerSeries.X)) :=
    invUnit1_congr_le _ _ d hsub
  have hmul : ∀ i ≤ d,
      PowerSeries.coeff i (cfApprox p d) = PowerSeries.coeff i (sSeries p 0) := by
    intro i hi
    unfold cfApprox
    rw [← cfApprox_exact p]
    exact mul_congr_le _ _ _ _ d (fun _ _ => rfl) hinv i hi
  constructor
  · rw [hmul 0 (by omega), coeff_zero_sSeries]
  · rw [hmul (n + 1) hd, coeff_succ_sSeries]
    simp

end OMA.P_oeis_a126617

theorem OMA.solution : type_of% @OMA.S_oeis_a126617.main :=
  OMA.P_oeis_a126617.solution
