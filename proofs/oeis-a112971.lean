import OMAStatements.S_oeis_a112971
import Mathlib

open PowerSeries OMA.S_oeis_a112971

namespace OMA.A112971Proof

/-! ## Step 1: the series `F = x c(x)` and `H = F(F(x))` over `ZMod 2` -/

theorem M_eq_zero {n k : ℕ} (hk : n < k) : M n k = 0 := by
  unfold M
  rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (show ¬ k ≤ n by omega)]

noncomputable def Fs : PowerSeries (ZMod 2) :=
  PowerSeries.map (Nat.castRingHom (ZMod 2)) (PowerSeries.X * c)

theorem Fs_coeff_pow (n k : ℕ) : PowerSeries.coeff n (Fs ^ k) = ((M n k : ℕ) : ZMod 2) := by
  unfold Fs M
  rw [← map_pow, PowerSeries.coeff_map]
  rfl

theorem Fs_eq : Fs = PowerSeries.X + Fs ^ 2 := by
  have hc : (PowerSeries.X : PowerSeries ℕ) * c = PowerSeries.X + (PowerSeries.X * c) ^ 2 := by
    have h1 := PowerSeries.catalanSeries_sq_mul_X_add_one
    have h2 : c = PowerSeries.catalanSeries := rfl
    rw [h2]
    calc (PowerSeries.X : PowerSeries ℕ) * PowerSeries.catalanSeries
        = PowerSeries.X * (PowerSeries.catalanSeries ^ 2 * PowerSeries.X + 1) := by rw [h1]
      _ = PowerSeries.X + (PowerSeries.X * PowerSeries.catalanSeries) ^ 2 := by ring
  unfold Fs
  conv_lhs => rw [hc]
  rw [map_add, map_pow, PowerSeries.map_X]

theorem Fs_const : PowerSeries.constantCoeff Fs = 0 := by
  have h1 := Fs_coeff_pow 0 1
  rw [pow_one, M_eq_zero (show 0 < 1 by norm_num), Nat.cast_zero] at h1
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact h1

theorem hFs : PowerSeries.HasSubst Fs := PowerSeries.HasSubst.of_constantCoeff_zero' Fs_const

noncomputable def Hs : PowerSeries (ZMod 2) := PowerSeries.subst Fs Fs

theorem Hs_eq1 : Hs = Fs + Hs ^ 2 := by
  have e : PowerSeries.subst Fs Fs =
      PowerSeries.subst Fs (PowerSeries.X + Fs ^ 2 : PowerSeries (ZMod 2)) :=
    congrArg (PowerSeries.subst Fs) Fs_eq
  rw [PowerSeries.subst_add hFs, PowerSeries.subst_X hFs, PowerSeries.subst_pow hFs] at e
  exact e

theorem two_eq_zero' : (2 : PowerSeries (ZMod 2)) = 0 := by
  have h1 : (2 : PowerSeries (ZMod 2)) = PowerSeries.C (1 + 1 : ZMod 2) := by
    rw [map_add, map_one, one_add_one_eq_two]
  rw [h1, show (1 + 1 : ZMod 2) = 0 by decide, map_zero]

/-- Mod 2, `H = x + H^4`: from `F = x + F^2` and `H = F + H^2`. -/
theorem Hs_eq : Hs = PowerSeries.X + Hs ^ 4 := by
  linear_combination (1 - Hs + Hs ^ 2 - Fs) * Hs_eq1 + Fs_eq + (Hs ^ 2 - Hs ^ 3) * two_eq_zero'

theorem Hs_rec (k : ℕ) : Hs ^ (k + 1) = PowerSeries.X * Hs ^ k + Hs ^ (k + 4) := by
  linear_combination Hs ^ k * Hs_eq

/-- The entries of the matrix square, mod 2, are the coefficients of the powers of `H`. -/
theorem coeff_Hs_pow (n k : ℕ) : PowerSeries.coeff n (Hs ^ k) = ((M2 n k : ℕ) : ZMod 2) := by
  have e : Hs ^ k = PowerSeries.subst Fs (Fs ^ k) := (PowerSeries.subst_pow hFs Fs k).symm
  rw [e, PowerSeries.coeff_subst' hFs,
    finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · unfold M2
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro d _
    simp only [Fs_coeff_pow, smul_eq_mul, Nat.cast_mul]
    ring
  · intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra hlt
    apply hd
    rw [Fs_coeff_pow n d, M_eq_zero (show n < d by omega), Nat.cast_zero, smul_zero]

theorem T0 (n : ℕ) : ((M2 n 0 : ℕ) : ZMod 2) = if n = 0 then 1 else 0 := by
  rw [← coeff_Hs_pow, pow_zero, PowerSeries.coeff_one]

theorem Tz {n k : ℕ} (hk : n < k) : ((M2 n k : ℕ) : ZMod 2) = 0 := by
  have h1 : M2 n k = 0 := by
    unfold M2
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_range] at hj
    rw [M_eq_zero (show j < k by omega), mul_zero]
  rw [h1, Nat.cast_zero]

theorem Tr (m k : ℕ) : ((M2 (m + 1) (k + 1) : ℕ) : ZMod 2) =
    ((M2 m k : ℕ) : ZMod 2) + ((M2 (m + 1) (k + 4) : ℕ) : ZMod 2) := by
  rw [← coeff_Hs_pow, ← coeff_Hs_pow, ← coeff_Hs_pow, Hs_rec k, map_add,
    PowerSeries.coeff_succ_X_mul]

/-! ## Step 2: the explicit parity matrix -/

/-- Parity of the square: for `k ≥ 1`, `C(n + j, j)` with `n = k + 3 j`, else `0`. -/
def Epar (n k : ℕ) : ZMod 2 :=
  if k = 0 then (if n = 0 then 1 else 0)
  else if k ≤ n ∧ (n - k) % 3 = 0 then (((n + (n - k) / 3).choose ((n - k) / 3) : ℕ) : ZMod 2)
  else 0

theorem Epar_k0 (n : ℕ) : Epar n 0 = if n = 0 then 1 else 0 := by
  unfold Epar
  exact if_pos rfl

theorem Epar_val (n k j : ℕ) (hk : k ≠ 0) (hj : n = k + 3 * j) :
    Epar n k = (((n + j).choose j : ℕ) : ZMod 2) := by
  unfold Epar
  rw [if_neg hk, if_pos (⟨by omega, by omega⟩ : k ≤ n ∧ (n - k) % 3 = 0)]
  rw [show (n - k) / 3 = j by omega]

theorem Epar_zero (n k : ℕ) (hk : k ≠ 0) (hc : ¬ (k ≤ n ∧ (n - k) % 3 = 0)) : Epar n k = 0 := by
  unfold Epar
  rw [if_neg hk, if_neg hc]

theorem choose_four (i : ℕ) : (((4 * i + 4).choose (i + 1) : ℕ) : ZMod 2) = 0 := by
  have h1 := Nat.add_one_mul_choose_eq (4 * i + 3) i
  have h2 : (4 * i + 4).choose (i + 1) = 4 * (4 * i + 3).choose i := by
    have h4 : (4 * i + 4).choose (i + 1) * (i + 1) = 4 * (4 * i + 3).choose i * (i + 1) := by
      rw [show 4 * i + 4 = 4 * i + 3 + 1 by ring, ← h1]
      ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos i) h4
  rw [h2, Nat.cast_mul, show ((4 : ℕ) : ZMod 2) = 0 by decide, zero_mul]

theorem Epar_rec (m k : ℕ) (hk : k ≤ m) :
    Epar (m + 1) (k + 1) = Epar m k + Epar (m + 1) (k + 4) := by
  by_cases h3 : (m - k) % 3 = 0
  · obtain ⟨j, hj⟩ : ∃ j, m = k + 3 * j := ⟨(m - k) / 3, by omega⟩
    rcases j with _ | i
    · rw [Epar_val (m + 1) (k + 1) 0 (by omega) (by omega),
        Epar_zero (m + 1) (k + 4) (by omega) (by omega)]
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0
        have hm : m = 0 := by omega
        subst hm
        rw [Epar_k0, if_pos rfl]
        simp
      · rw [Epar_val m k 0 (by omega) (by omega)]
        simp
    · rw [Epar_val (m + 1) (k + 1) (i + 1) (by omega) (by omega),
        Epar_val (m + 1) (k + 4) i (by omega) (by omega)]
      rw [show m + 1 + (i + 1) = m + 1 + i + 1 by ring, Nat.choose_succ_succ']
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0
        rw [Epar_k0, if_neg (show m ≠ 0 by omega), show m + 1 + i = 4 * i + 4 by omega,
          Nat.cast_add, choose_four i]
        ring
      · rw [Epar_val m k (i + 1) (by omega) (by omega), show m + (i + 1) = m + 1 + i by ring,
          Nat.cast_add]
        ring
  · rw [Epar_zero (m + 1) (k + 1) (by omega) (by omega),
      Epar_zero (m + 1) (k + 4) (by omega) (by omega)]
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      rw [Epar_k0, if_neg (show m ≠ 0 by omega)]
      simp
    · rw [Epar_zero m k (by omega) (by omega)]
      simp

/-- The square mod 2 equals `Epar`: both satisfy the same boundary values and recurrence. -/
theorem key (μ : ℕ) : ∀ n k : ℕ, 4 * n + (n + 1 - k) ≤ μ → ((M2 n k : ℕ) : ZMod 2) = Epar n k := by
  induction μ using Nat.strong_induction_on with
  | _ μ ih =>
    intro n k hμ
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [T0, Epar_k0]
    · by_cases hnk : n < k
      · rw [Tz hnk, Epar_zero n k (by omega) (by omega)]
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [Tr, ih (4 * m + (m + 1 - k')) (by omega) m k' le_rfl,
          ih (4 * (m + 1) + (m + 1 + 1 - (k' + 4))) (by omega) (m + 1) (k' + 4) le_rfl,
          Epar_rec m k' (by omega)]

theorem M2_mod (n k : ℕ) : ((M2 n k : ℕ) : ZMod 2) = Epar n k := key _ n k le_rfl

/-! ## Step 3: the closed form `a n = Σ_{j ≤ (n-1)/3} (C(n+j, j) mod 2)` for `n ≥ 1` -/

theorem a_E (n : ℕ) : a n = ∑ k ∈ Finset.range (n + 1), (Epar n k).val := by
  unfold a
  apply Finset.sum_congr rfl
  intro k _
  rw [← M2_mod, ZMod.val_natCast]

theorem Eval (n k : ℕ) (hn : 1 ≤ n) : (Epar n k).val =
    if 1 ≤ k ∧ k ≤ n ∧ (n - k) % 3 = 0 then (n + (n - k) / 3).choose ((n - k) / 3) % 2 else 0 := by
  by_cases hk : k = 0
  · subst hk
    rw [Epar_k0, if_neg (show n ≠ 0 by omega),
      if_neg (show ¬ (1 ≤ 0 ∧ 0 ≤ n ∧ (n - 0) % 3 = 0) by omega), ZMod.val_zero]
  · by_cases hc : k ≤ n ∧ (n - k) % 3 = 0
    · rw [Epar_val n k ((n - k) / 3) hk (by omega), if_pos ⟨by omega, hc.1, hc.2⟩,
        ZMod.val_natCast]
    · rw [Epar_zero n k hk hc, if_neg (fun h => hc ⟨h.2.1, h.2.2⟩), ZMod.val_zero]

theorem reindex (n : ℕ) (hn : 1 ≤ n) (φ : ℕ → ℕ) :
    ∑ k ∈ Finset.range (n + 1), (if 1 ≤ k ∧ k ≤ n ∧ (n - k) % 3 = 0 then φ ((n - k) / 3) else 0) =
      ∑ j ∈ Finset.range ((n - 1) / 3 + 1), φ j := by
  symm
  have hsub : (Finset.range ((n - 1) / 3 + 1)).image (fun j => n - 3 * j) ⊆
      Finset.range (n + 1) := by
    intro k hk
    simp only [Finset.mem_image, Finset.mem_range] at hk
    obtain ⟨j, _, rfl⟩ := hk
    simp only [Finset.mem_range]
    omega
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      show φ j = (if 1 ≤ n - 3 * j ∧ n - 3 * j ≤ n ∧ (n - (n - 3 * j)) % 3 = 0 then
        φ ((n - (n - 3 * j)) / 3) else 0)
      rw [if_pos ⟨by omega, by omega, by omega⟩, show (n - (n - 3 * j)) / 3 = j by omega]
    · intro x hx y hy hxy
      have hx' : x < (n - 1) / 3 + 1 := by simpa using hx
      have hy' : y < (n - 1) / 3 + 1 := by simpa using hy
      have hxy' : n - 3 * x = n - 3 * y := hxy
      omega
  · intro k hk hk'
    apply if_neg
    rintro ⟨h1, h2, h3⟩
    apply hk'
    simp only [Finset.mem_image, Finset.mem_range]
    exact ⟨(n - k) / 3, by omega, by omega⟩

theorem a_formula (n : ℕ) (hn : 1 ≤ n) :
    a n = ∑ j ∈ Finset.range ((n - 1) / 3 + 1), (n + j).choose j % 2 := by
  have hsum : ∑ k ∈ Finset.range (n + 1), (Epar n k).val = ∑ k ∈ Finset.range (n + 1),
      (if 1 ≤ k ∧ k ≤ n ∧ (n - k) % 3 = 0 then (n + (n - k) / 3).choose ((n - k) / 3) % 2
        else 0) :=
    Finset.sum_congr rfl (fun k _ => Eval n k hn)
  rw [a_E, hsum]
  exact reindex n hn (fun j => (n + j).choose j % 2)

/-! ## Step 4: Kummer's theorem at the special `n` -/

theorem log_bound (n j : ℕ) : Nat.log 2 (n + j) < n + j + 1 :=
  Nat.lt_succ_of_le (Nat.log_le_self 2 (n + j))

theorem choose_odd_of (n j : ℕ) (h : ∀ i, 1 ≤ i → ¬ (2 ^ i ≤ j % 2 ^ i + n % 2 ^ i)) :
    (n + j).choose j % 2 = 1 := by
  have hv := padicValNat_choose' (p := 2) (n := n) (k := j) (log_bound n j)
  have h0 : padicValNat 2 ((n + j).choose j) = 0 := by
    rw [hv, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i hi
    exact h i (Finset.mem_Ico.1 hi).1
  have hne : (n + j).choose j ≠ 0 := (Nat.choose_pos (by omega)).ne'
  rcases Nat.mod_two_eq_zero_or_one ((n + j).choose j) with h2 | h2
  · exfalso
    have h3 := one_le_padicValNat_of_dvd hne (Nat.dvd_of_mod_eq_zero h2)
    omega
  · exact h2

theorem choose_even_of (n j i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ n + j)
    (h : 2 ^ i ≤ j % 2 ^ i + n % 2 ^ i) : (n + j).choose j % 2 = 0 := by
  have hv := padicValNat_choose' (p := 2) (n := n) (k := j) (log_bound n j)
  have h1 : 1 ≤ padicValNat 2 ((n + j).choose j) := by
    rw [hv]
    exact Finset.one_le_card.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨hi1, by omega⟩, h⟩⟩
  exact Nat.mod_eq_zero_of_dvd (dvd_of_one_le_padicValNat h1)

theorem two_le_two_pow {i : ℕ} (hi : 1 ≤ i) : 2 ≤ 2 ^ i := by
  calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi

theorem P1 (r j : ℕ) (hj : j < 2 ^ r) : (2 ^ r + j).choose j % 2 = 1 := by
  apply choose_odd_of
  intro i hi
  by_cases hir : i ≤ r
  · rw [Nat.mod_eq_zero_of_dvd (pow_dvd_pow 2 hir)]
    have := Nat.mod_lt j (Nat.two_pow_pos i)
    omega
  · have h1 : 2 ^ (r + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
    rw [Nat.mod_eq_of_lt (show j < 2 ^ i by omega), Nat.mod_eq_of_lt (show 2 ^ r < 2 ^ i by omega)]
    omega

theorem P2 (r j : ℕ) (hj : j < 2 ^ (r + 1)) :
    (2 ^ (r + 1) + 1 + j).choose j % 2 = if j % 2 = 0 then 1 else 0 := by
  have hQ : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
  have hpos : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  split_ifs with hj2
  · apply choose_odd_of
    intro i hi
    have h2i : 2 ≤ 2 ^ i := two_le_two_pow hi
    by_cases hir : i ≤ r + 1
    · obtain ⟨t, ht⟩ := pow_dvd_pow 2 hir
      have hn : (2 ^ (r + 1) + 1) % 2 ^ i = 1 := by
        rw [ht, add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (show 1 < 2 ^ i by omega)]
      rw [hn]
      have h1 := Nat.mod_lt j (Nat.two_pow_pos i)
      have h2 : j % 2 ^ i % 2 = 0 := by
        rw [Nat.mod_mod_of_dvd j (dvd_pow_self 2 (show i ≠ 0 by omega))]
        exact hj2
      have h3 : 2 ^ i % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (show i ≠ 0 by omega))
      omega
    · have h1 : 2 ^ (r + 2) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ (r + 2) = 4 * 2 ^ r := by ring
      rw [Nat.mod_eq_of_lt (show j < 2 ^ i by omega),
        Nat.mod_eq_of_lt (show 2 ^ (r + 1) + 1 < 2 ^ i by omega)]
      omega
  · apply choose_even_of (2 ^ (r + 1) + 1) j 1 le_rfl (by omega)
    have h1 : (2 ^ (r + 1) + 1) % 2 = 1 := by omega
    rw [pow_one, h1]
    omega

theorem P3 (n r j : ℕ) (hn : n % 2 ^ r = 2 ^ r - 1) (hj1 : 1 ≤ j) (hj : j < 2 ^ r) :
    (n + j).choose j % 2 = 0 := by
  have hr : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0
      rw [pow_zero] at hj
      omega
    · exact h0
  have hlt : r < 2 ^ r := Nat.lt_two_pow_self
  have hle : n % 2 ^ r ≤ n := Nat.mod_le n (2 ^ r)
  apply choose_even_of n j r hr (by omega)
  rw [Nat.mod_eq_of_lt hj, hn]
  omega

/-! ## Step 5: A005578 and the four conjectures -/

theorem count_even (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), (if j % 2 = 0 then 1 else 0 : ℕ) = m / 2 + 1 := by
  induction m with
  | zero =>
    first
    | (rw [Finset.sum_range_one]; done)
    | (rw [Finset.sum_range_one]; rfl)
    | decide
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

theorem A_aux (r : ℕ) : A005578 r = 2 ^ r / 3 + 1 ∧ 2 ^ r % 3 = (if r % 2 = 0 then 1 else 2) := by
  induction r with
  | zero => decide
  | succ r ih =>
    obtain ⟨h1, h2⟩ := ih
    have hp : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
    rw [hp]
    simp only [A005578]
    split_ifs at h2 ⊢ <;> constructor <;> omega

theorem part1 (r : ℕ) : a (2 ^ r) = A005578 r := by
  have hpos : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have h3 : 2 ^ r % 3 ≠ 0 := by
    have := (A_aux r).2
    split_ifs at this <;> omega
  rw [a_formula (2 ^ r) hpos, (A_aux r).1]
  have hall : ∀ j ∈ Finset.range ((2 ^ r - 1) / 3 + 1), (2 ^ r + j).choose j % 2 = 1 := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact P1 r j (by omega)
  rw [Finset.sum_congr rfl hall, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  omega

theorem part2 (r : ℕ) : a (2 ^ (r + 1) + 1) = A005578 r := by
  have hp : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
  have hpos : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  rw [a_formula (2 ^ (r + 1) + 1) (by omega), (A_aux r).1]
  rw [show (2 ^ (r + 1) + 1 - 1) / 3 = 2 ^ (r + 1) / 3 by omega]
  have hall : ∀ j ∈ Finset.range (2 ^ (r + 1) / 3 + 1),
      (2 ^ (r + 1) + 1 + j).choose j % 2 = if j % 2 = 0 then 1 else 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact P2 r j (by omega)
  rw [Finset.sum_congr rfl hall, count_even]
  omega

theorem part3 (r : ℕ) : a (2 ^ r - 1) = 1 := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    rw [pow_zero, Nat.sub_self, a_E, Finset.sum_range_one, Epar_k0, if_pos rfl]
    rfl
  · have h2 : 2 ≤ 2 ^ r := two_le_two_pow hr
    rw [a_formula (2 ^ r - 1) (by omega), Finset.sum_eq_single 0]
    · simp
    · intro j hj hj0
      rw [Finset.mem_range] at hj
      exact P3 (2 ^ r - 1) r j (Nat.mod_eq_of_lt (by omega)) (by omega) (by omega)
    · intro h
      exfalso
      exact h (Finset.mem_range.2 (by omega))

theorem part4 (r : ℕ) : a (3 * 2 ^ r - 1) = 1 := by
  have hpos : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  rw [a_formula (3 * 2 ^ r - 1) (by omega), Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    rw [Finset.mem_range] at hj
    have hmod : (3 * 2 ^ r - 1) % 2 ^ r = 2 ^ r - 1 := by
      rw [show 3 * 2 ^ r - 1 = (2 ^ r - 1) + 2 ^ r * 2 by omega, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega)]
    exact P3 (3 * 2 ^ r - 1) r j hmod (by omega) (by omega)
  · intro h
    exfalso
    exact h (Finset.mem_range.2 (by omega))

end OMA.A112971Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a112971.main := by
  intro n
  exact ⟨OMA.A112971Proof.part1 n, OMA.A112971Proof.part2 n, OMA.A112971Proof.part3 n,
    OMA.A112971Proof.part4 n⟩
