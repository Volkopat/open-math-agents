import OMAStatements.S_oeis_a024849

namespace OMA.S_oeis_a024849

open Real PowerSeries





/-! ## The set -/

/-- t = 1/tau. -/
noncomputable def t : ℝ := goldenRatio⁻¹

lemma t_pos : 0 < t := inv_pos.mpr goldenRatio_pos

lemma t_lt_one : t < 1 := inv_lt_one_of_one_lt₀ one_lt_goldenRatio

lemma t_eq : t = -goldenConj := inv_goldenRatio

lemma t_sq : t ^ 2 = 1 - t := by
  rw [t_eq, neg_sq, goldenConj_sq]; ring

lemma t_mul_phi_pow (h : ℕ) : t ^ h * goldenRatio ^ h = 1 := by
  rw [← mul_pow, t, inv_mul_cancel₀ goldenRatio_ne_zero, one_pow]

lemma abs_eq (h : ℕ) : |(Nat.fib (h + 1) : ℝ) - goldenRatio * Nat.fib h| = t ^ h := by
  rw [fib_succ_sub_goldenRatio_mul_fib, abs_pow, abs_of_neg goldenConj_neg, ← t_eq]

lemma mem_S {n : ℕ} {r : ℝ} : r ∈ S n ↔ ∃ h, 1 ≤ h ∧ h ≤ n ∧ r = t ^ h := by
  simp only [S, Finset.mem_image, Finset.mem_Icc, abs_eq]
  constructor
  · rintro ⟨h, ⟨h1, h2⟩, rfl⟩; exact ⟨h, h1, h2, rfl⟩
  · rintro ⟨h, h1, h2, rfl⟩; exact ⟨h, ⟨h1, h2⟩, rfl⟩

lemma t_pow_lt_iff {i j : ℕ} : t ^ j < t ^ i ↔ i < j :=
  pow_lt_pow_iff_right_of_lt_one₀ t_pos t_lt_one

lemma phi_pow_pos (k : ℕ) : 0 < goldenRatio ^ k := pow_pos goldenRatio_pos k

lemma phi_lt_two_mul (k : ℕ) : goldenRatio ^ (k + 1) < 2 * goldenRatio ^ k := by
  rw [pow_succ]
  have := phi_pow_pos k
  nlinarith [goldenRatio_lt_two]

lemma pow_three_eq (x : ℝ) (hx : x ^ 2 = x + 1) (p : ℕ) : x ^ (p + 3) = 2 * x ^ (p + 1) + x ^ p := by
  have h3 : x ^ 3 = 2 * x + 1 := by linear_combination (x + 1) * hx
  calc x ^ (p + 3) = x ^ p * x ^ 3 := by ring
    _ = x ^ p * (2 * x + 1) := by rw [h3]
    _ = 2 * x ^ (p + 1) + x ^ p := by ring

lemma three_halves_lt : (3 : ℝ) / 2 < goldenRatio := by
  nlinarith [goldenRatio_sq, goldenRatio_pos]

/-! ## The least m -/

/-- M = floor(2 tau^(n-2)) + 1 separates the set for n >= 3. -/
lemma good_M (n : ℕ) (hn : 3 ≤ n) : Good n (⌊2 * goldenRatio ^ (n - 2)⌋₊ + 1) := by
  set M : ℕ := ⌊2 * goldenRatio ^ (n - 2)⌋₊ + 1 with hM
  have hx : 0 ≤ 2 * goldenRatio ^ (n - 2) := by positivity
  have hM1 : 2 * goldenRatio ^ (n - 2) < (M : ℝ) := by
    rw [hM]; push_cast; exact Nat.lt_floor_add_one _
  have hM2 : (M : ℝ) ≤ 2 * goldenRatio ^ (n - 2) + 1 := by
    rw [hM]; push_cast; linarith [Nat.floor_le hx]
  have hMpos : (0 : ℝ) < M := by linarith
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 3 := ⟨n - 3, by omega⟩
  have e1 : p + 3 - 2 = p + 1 := by omega
  rw [e1] at hM1 hM2
  -- tau^(p+2) < 2 tau^(p+1) < M, and M < tau^(p+3), M < 2 tau^(p+2)
  have hA : goldenRatio ^ (p + 2) < M := lt_trans (phi_lt_two_mul (p + 1)) hM1
  have hB : (M : ℝ) < goldenRatio ^ (p + 3) := by
    have h3 : goldenRatio ^ (p + 3) = 2 * goldenRatio ^ (p + 1) + goldenRatio ^ p :=
      pow_three_eq goldenRatio goldenRatio_sq p
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · -- n = 3: M = floor(2 tau) + 1 = 4 < tau^3 = 2 tau + 1
      have h1 := three_halves_lt
      have hfl : ⌊2 * goldenRatio ^ (0 + 3 - 2)⌋₊ = 3 := by
        rw [show 0 + 3 - 2 = 1 from rfl, pow_one, Nat.floor_eq_iff (by positivity)]
        constructor <;> push_cast <;> nlinarith [goldenRatio_lt_two]
      have hM4 : (M : ℝ) = 4 := by rw [hM, hfl]; norm_num
      rw [hM4, h3]
      simp
      nlinarith
    · rw [h3]
      have : 1 < goldenRatio ^ p := one_lt_pow₀ one_lt_goldenRatio hp.ne'
      linarith
  have hC : (M : ℝ) < 2 * goldenRatio ^ (p + 2) := by
    have := phi_lt_two_mul (p + 1)
    have h4 : 2 * goldenRatio ^ (p + 1) + 1 < 2 * goldenRatio ^ (p + 2) := by
      have h5 : goldenRatio ^ (p + 2) = goldenRatio ^ (p + 1) + goldenRatio ^ p := by
        rw [show p + 2 = p + 1 + 1 by ring]
        have := goldenRatio_pow_sub_goldenRatio_pow p
        rw [show p + 1 + 1 = p + 2 by ring]
        linarith
      have : 1 ≤ goldenRatio ^ p := one_le_pow₀ one_lt_goldenRatio.le
      linarith
    linarith
  intro r hr s hs hrs
  obtain ⟨j, hj1, hj2, rfl⟩ := mem_S.mp hr
  obtain ⟨i, hi1, hi2, rfl⟩ := mem_S.mp hs
  have hij : i < j := t_pow_lt_iff.mp hrs
  rcases (by omega : i + 3 ≤ p + 3 - 0 - 0 ∧ i ≤ p ∨ i = p + 1 ∨ i = p + 2) with ⟨-, hi⟩ | hi | hi
  · -- a long interval: k = floor(M t^(i+1)) + 1
    refine ⟨⌊(M : ℝ) * t ^ (i + 1)⌋ + 1, ?_, ?_⟩
    · rw [lt_div_iff₀ hMpos]
      have hk := Int.lt_floor_add_one ((M : ℝ) * t ^ (i + 1))
      have hle : t ^ j ≤ t ^ (i + 1) := pow_le_pow_of_le_one t_pos.le t_lt_one.le (by omega)
      push_cast
      nlinarith
    · rw [div_lt_iff₀ hMpos]
      have hk := Int.floor_le ((M : ℝ) * t ^ (i + 1))
      -- M t^i - M t^(i+1) = M t^(i+2) > 1
      have key : 1 < (M : ℝ) * t ^ (i + 2) := by
        have h1 : goldenRatio ^ (i + 2) ≤ goldenRatio ^ (p + 2) :=
          pow_le_pow_right₀ one_lt_goldenRatio.le (by omega)
        have h2 := t_mul_phi_pow (i + 2)
        have h3 : 0 < t ^ (i + 2) := pow_pos t_pos _
        nlinarith
      have hti : t ^ i - t ^ (i + 1) = t ^ (i + 2) := by
        rw [pow_succ, pow_add, t_sq]; ring
      push_cast
      nlinarith
  · -- i = n - 2: k = 2
    subst hi
    refine ⟨2, ?_, ?_⟩
    · rw [lt_div_iff₀ hMpos]
      have hle : t ^ j ≤ t ^ (p + 2) := pow_le_pow_of_le_one t_pos.le t_lt_one.le (by omega)
      have h2 := t_mul_phi_pow (p + 2)
      have h3 : 0 < t ^ (p + 2) := pow_pos t_pos _
      push_cast
      nlinarith
    · rw [div_lt_iff₀ hMpos]
      have h2 := t_mul_phi_pow (p + 1)
      have h3 : 0 < t ^ (p + 1) := pow_pos t_pos _
      push_cast
      nlinarith
  · -- i = n - 1, j = n: k = 1
    subst hi
    have hj : j = p + 3 := by omega
    subst hj
    refine ⟨1, ?_, ?_⟩
    · rw [lt_div_iff₀ hMpos]
      have h2 := t_mul_phi_pow (p + 3)
      have h3 : 0 < t ^ (p + 3) := pow_pos t_pos _
      push_cast
      nlinarith
    · rw [div_lt_iff₀ hMpos]
      have h2 := t_mul_phi_pow (p + 2)
      have h3 : 0 < t ^ (p + 2) := pow_pos t_pos _
      push_cast
      nlinarith

/-- No m <= 2 tau^(n-2) separates the set, for n >= 3. -/
lemma not_good (n m : ℕ) (hn : 3 ≤ n) (hm : 0 < m) (hle : (m : ℝ) ≤ 2 * goldenRatio ^ (n - 2)) :
    ¬ Good n m := by
  intro hg
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 3 := ⟨n - 3, by omega⟩
  rw [show p + 3 - 2 = p + 1 by omega] at hle
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  rcases le_or_gt (m : ℝ) (goldenRatio ^ (p + 2)) with h | h
  · -- the pair t^n < t^(n-1)
    obtain ⟨k, hk1, hk2⟩ := hg (t ^ (p + 3)) (mem_S.mpr ⟨p + 3, by omega, le_rfl, rfl⟩)
      (t ^ (p + 2)) (mem_S.mpr ⟨p + 2, by omega, by omega, rfl⟩) (t_pow_lt_iff.mpr (by omega))
    rw [lt_div_iff₀ hmpos] at hk1
    rw [div_lt_iff₀ hmpos] at hk2
    have h3 : 0 < t ^ (p + 3) := pow_pos t_pos _
    have hk : (0 : ℝ) < k := by nlinarith
    have hk' : (1 : ℝ) ≤ k := by
      have : (0 : ℤ) < k := by exact_mod_cast hk
      exact_mod_cast this
    have h2 := t_mul_phi_pow (p + 2)
    have h4 : 0 < t ^ (p + 2) := pow_pos t_pos _
    nlinarith
  · -- the pair t^(n-1) < t^(n-2)
    obtain ⟨k, hk1, hk2⟩ := hg (t ^ (p + 2)) (mem_S.mpr ⟨p + 2, by omega, by omega, rfl⟩)
      (t ^ (p + 1)) (mem_S.mpr ⟨p + 1, by omega, by omega, rfl⟩) (t_pow_lt_iff.mpr (by omega))
    rw [lt_div_iff₀ hmpos] at hk1
    rw [div_lt_iff₀ hmpos] at hk2
    have h2 := t_mul_phi_pow (p + 2)
    have h4 : 0 < t ^ (p + 2) := pow_pos t_pos _
    have hk : (1 : ℝ) < k := by nlinarith
    have hk' : (2 : ℝ) ≤ k := by
      have : (1 : ℤ) < k := by exact_mod_cast hk
      have : (2 : ℤ) ≤ k := by omega
      exact_mod_cast this
    have h5 := t_mul_phi_pow (p + 1)
    have h6 : 0 < t ^ (p + 1) := pow_pos t_pos _
    nlinarith

lemma a_eq_M (n : ℕ) (hn : 3 ≤ n) : a n = ⌊2 * goldenRatio ^ (n - 2)⌋₊ + 1 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨by omega, good_M n hn⟩
  · show _ ≤ sInf {m : ℕ | 0 < m ∧ Good n m}
    refine le_csInf ⟨⌊2 * goldenRatio ^ (n - 2)⌋₊ + 1, Nat.succ_pos _, good_M n hn⟩ ?_
    rintro m ⟨hm, hg⟩
    by_contra hlt
    rw [not_le] at hlt
    have : m ≤ ⌊2 * goldenRatio ^ (n - 2)⌋₊ := by omega
    exact not_good n m hn hm ((Nat.le_floor_iff (by positivity)).mp this) hg

/-! ## Small values and the Lucas form -/

lemma half_lt_t : 1 / 2 < t := by
  have h := t_sq
  have h0 := t_pos
  nlinarith

lemma a_two : a 2 = 2 := by
  have hsq := t_sq
  have h1 := half_lt_t
  have h2 := t_lt_one
  have hgood : Good 2 2 := by
    intro r hr s hs hrs
    obtain ⟨j, hj1, hj2, rfl⟩ := mem_S.mp hr
    obtain ⟨i, hi1, hi2, rfl⟩ := mem_S.mp hs
    have hij : i < j := t_pow_lt_iff.mp hrs
    obtain rfl : i = 1 := by omega
    obtain rfl : j = 2 := by omega
    refine ⟨1, ?_, ?_⟩ <;> push_cast <;> nlinarith
  have hbad : ¬ Good 2 1 := by
    intro hg
    obtain ⟨k, hk1, hk2⟩ := hg (t ^ 2) (mem_S.mpr ⟨2, by norm_num, le_rfl, rfl⟩) (t ^ 1)
      (mem_S.mpr ⟨1, le_rfl, by norm_num, rfl⟩) (t_pow_lt_iff.mpr (by norm_num))
    push_cast at hk1 hk2
    rw [div_one] at hk1 hk2
    have h0 : (0 : ℝ) < k := by nlinarith [t_pos]
    have h1' : (k : ℝ) < 1 := by nlinarith
    have : (0 : ℤ) < k := by exact_mod_cast h0
    have : k < (1 : ℤ) := by exact_mod_cast h1'
    omega
  unfold a
  apply le_antisymm (Nat.sInf_le (show (2 : ℕ) ∈ {m : ℕ | 0 < m ∧ Good 2 m} from ⟨by norm_num, hgood⟩))
  refine le_csInf ⟨2, by norm_num, hgood⟩ ?_
  rintro m ⟨hm, hg⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain rfl : m = 1 := by omega
  exact hbad hg

lemma phi_add_psi (k : ℕ) :
    goldenRatio ^ (k + 1) + goldenConj ^ (k + 1) = Nat.fib k + Nat.fib (k + 2) := by
  have h1 := goldenRatio_mul_fib_succ_add_fib k
  have h2 := goldenConj_mul_fib_succ_add_fib k
  have h3 : (Nat.fib (k + 2) : ℝ) = Nat.fib k + Nat.fib (k + 1) := by
    rw [Nat.fib_add_two]; push_cast; ring
  rw [← h1, ← h2, h3]
  linear_combination (Nat.fib (k + 1) : ℝ) * goldenRatio_add_goldenConj

/-- a(n) = 2 L(n-2) + [n odd] for n >= 4, with L(k) = F(k-1) + F(k+1). -/
lemma a_lucas (n : ℕ) (hn : 4 ≤ n) :
    (a n : ℤ) = 2 * (Nat.fib (n - 3) + Nat.fib (n - 1)) + (if n % 2 = 0 then 0 else 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [a_eq_M _ (by omega), show k + 4 - 2 = (k + 1) + 1 by omega, show k + 4 - 3 = k + 1 by omega,
    show k + 4 - 1 = (k + 1) + 2 by omega]
  set L : ℕ := Nat.fib (k + 1) + Nat.fib (k + 1 + 2) with hL
  have hsum := phi_add_psi (k + 1)
  have hLr : (L : ℝ) = (Nat.fib (k + 1) : ℝ) + Nat.fib (k + 1 + 2) := by rw [hL]; push_cast; ring
  have hL1 : 1 ≤ L := by
    have : 0 < Nat.fib (k + 1 + 2) := Nat.fib_pos.mpr (by omega)
    omega
  have hc : goldenConj = -t := by rw [t_eq]; ring
  have hpsi : goldenConj ^ (k + 1 + 1) = (-1) ^ (k + 1 + 1) * t ^ (k + 1 + 1) := by
    rw [hc, neg_pow]
  have htk : t ^ (k + 1 + 1) ≤ t ^ 2 := pow_le_pow_of_le_one t_pos.le t_lt_one.le (by omega)
  have htk0 : 0 < t ^ (k + 1 + 1) := pow_pos t_pos _
  have hsq := t_sq
  have hhalf := half_lt_t
  have hx : 0 ≤ 2 * goldenRatio ^ (k + 1 + 1) := by positivity
  rcases Nat.even_or_odd (k + 1 + 1) with he | ho
  · have hk2 : (k + 4) % 2 = 0 := by obtain ⟨r, hr⟩ := he; omega
    rw [he.neg_one_pow, one_mul] at hpsi
    have hcast : ((2 * L - 1 : ℕ) : ℝ) = 2 * (L : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_mul]; norm_num
    have hfl : ⌊2 * goldenRatio ^ (k + 1 + 1)⌋₊ = 2 * L - 1 := by
      rw [Nat.floor_eq_iff hx, hcast]
      constructor <;> linarith
    rw [hfl, show 2 * L - 1 + 1 = 2 * L by omega, if_pos hk2, hL]
    push_cast
    ring
  · have hk2 : ¬ (k + 4) % 2 = 0 := by obtain ⟨r, hr⟩ := ho; omega
    rw [ho.neg_one_pow] at hpsi
    have hfl : ⌊2 * goldenRatio ^ (k + 1 + 1)⌋₊ = 2 * L := by
      rw [Nat.floor_eq_iff hx]
      push_cast
      constructor <;> linarith
    rw [hfl, if_neg hk2, hL]
    push_cast
    ring

lemma a_three : a 3 = 4 := by
  rw [a_eq_M 3 le_rfl, show 3 - 2 = 1 from rfl, pow_one]
  have h1 := three_halves_lt
  have h2 := goldenRatio_lt_two
  have : ⌊2 * goldenRatio⌋₊ = 3 := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor <;> push_cast <;> linarith
  rw [this]

/-- Wu's recurrence: a(n) = a(n-1) + 2a(n-2) - a(n-3) - a(n-4) for n > 7. -/
theorem recurrence : ∀ n : ℕ, 7 < n →
    (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - a (n - 3) - a (n - 4) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  rw [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
    show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega,
    a_lucas (m + 8) (by omega), a_lucas (m + 7) (by omega), a_lucas (m + 6) (by omega),
    a_lucas (m + 5) (by omega), a_lucas (m + 4) (by omega)]
  simp only [show m + 8 - 3 = m + 5 by omega, show m + 8 - 1 = m + 7 by omega,
    show m + 7 - 3 = m + 4 by omega, show m + 7 - 1 = m + 6 by omega,
    show m + 6 - 3 = m + 3 by omega, show m + 6 - 1 = m + 5 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 1 = m + 4 by omega,
    show m + 4 - 3 = m + 1 by omega, show m + 4 - 1 = m + 3 by omega]
  have f3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  have f4 : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := Nat.fib_add_two
  have f5 : Nat.fib (m + 5) = Nat.fib (m + 3) + Nat.fib (m + 4) := Nat.fib_add_two
  have f6 : Nat.fib (m + 6) = Nat.fib (m + 4) + Nat.fib (m + 5) := Nat.fib_add_two
  have f7 : Nat.fib (m + 7) = Nat.fib (m + 5) + Nat.fib (m + 6) := Nat.fib_add_two
  rcases Nat.even_or_odd m with ⟨r, hr⟩ | ⟨r, hr⟩
  · rw [if_pos (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
    push_cast [f3, f4, f5, f6, f7]
    ring
  · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega)]
    push_cast [f3, f4, f5, f6, f7]
    ring

lemma coeff_gf (n : ℕ) : coeff n gf = if n < 2 then 0 else (a n : ℚ) := by simp [gf]

/-- Wu's g.f.: x^2(x^5 - x^4 - 3x^3 - 2x^2 + 2x + 2)/((x - 1)(x + 1)(x^2 + x - 1)), in Q[[x]]. -/
theorem gf_eq : gf = X ^ 2 * (X ^ 5 - X ^ 4 - 3 * X ^ 3 - 2 * X ^ 2 + 2 * X + 2) *
    ((X - 1) * (X + 1) * (X ^ 2 + X - 1))⁻¹ := by
  set D : ℚ⟦X⟧ := (X - 1) * (X + 1) * (X ^ 2 + X - 1) with hD
  have hden : constantCoeff D ≠ 0 := by rw [hD]; simp
  have key : gf * D = X ^ 2 * (X ^ 5 - X ^ 4 - 3 * X ^ 3 - 2 * X ^ 2 + 2 * X + 2) := by
    have e : gf * D = gf - gf * X ^ 1 - C 2 * (gf * X ^ 2) + gf * X ^ 3 + gf * X ^ 4 := by
      rw [hD]; simp only [map_ofNat]; ring
    have en : (X : ℚ⟦X⟧) ^ 2 * (X ^ 5 - X ^ 4 - 3 * X ^ 3 - 2 * X ^ 2 + 2 * X + 2) =
        C 2 * X ^ 2 + C 2 * X ^ 3 - C 2 * X ^ 4 - C 3 * X ^ 5 - X ^ 6 + X ^ 7 := by
      simp only [map_ofNat]; ring
    rw [e, en]
    ext n
    simp only [map_sub, map_add, coeff_mul_X_pow', coeff_gf, coeff_C_mul, coeff_C, coeff_X_pow]
    have h2 := a_two
    have h3 := a_three
    have h4 : (a 4 : ℤ) = 6 := by rw [a_lucas 4 le_rfl]; decide
    have h5 : (a 5 : ℤ) = 9 := by rw [a_lucas 5 (by norm_num)]; decide
    have h6 : (a 6 : ℤ) = 14 := by rw [a_lucas 6 (by norm_num)]; decide
    have h7 : (a 7 : ℤ) = 23 := by rw [a_lucas 7 (by norm_num)]; decide
    have h4' : (a 4 : ℚ) = 6 := by exact_mod_cast h4
    have h5' : (a 5 : ℚ) = 9 := by exact_mod_cast h5
    have h6' : (a 6 : ℚ) = 14 := by exact_mod_cast h6
    have h7' : (a 7 : ℚ) = 23 := by exact_mod_cast h7
    rcases Nat.lt_or_ge n 8 with hn | hn
    · interval_cases n <;> simp [h2, h3, h4', h5', h6', h7'] <;> norm_num
    · have hr := recurrence n (by omega)
      have hq : (a n : ℚ) = a (n - 1) + 2 * a (n - 2) - a (n - 3) - a (n - 4) := by
        exact_mod_cast hr
      simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
        show 4 ≤ n by omega, if_true, show ¬ (n < 2) by omega, show ¬ (n - 1 < 2) by omega,
        show ¬ (n - 2 < 2) by omega, show ¬ (n - 3 < 2) by omega, show ¬ (n - 4 < 2) by omega,
        if_false, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega,
        show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega,
        show n - 5 ≠ 0 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega]
      linarith
  calc gf = gf * (D * D⁻¹) := by rw [PowerSeries.mul_inv_cancel _ hden, mul_one]
    _ = (gf * D) * D⁻¹ := (mul_assoc gf _ _).symm
    _ = _ := by rw [key]

/-- Controls from the entry: a(2..10) = 2, 4, 6, 9, 14, 23, 36, 59, 94. -/
example : a 2 = 2 ∧ a 3 = 4 ∧ (a 4 : ℤ) = 6 ∧ (a 5 : ℤ) = 9 ∧ (a 6 : ℤ) = 14 ∧ (a 7 : ℤ) = 23 ∧
    (a 8 : ℤ) = 36 ∧ (a 9 : ℤ) = 59 ∧ (a 10 : ℤ) = 94 := by
  refine ⟨a_two, a_three, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [a_lucas _ (by norm_num)] <;> decide

/-- Both of Wu's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 7 < n → (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - a (n - 3) - a (n - 4)) ∧
    gf = X ^ 2 * (X ^ 5 - X ^ 4 - 3 * X ^ 3 - 2 * X ^ 2 + 2 * X + 2) *
      ((X - 1) * (X + 1) * (X ^ 2 + X - 1))⁻¹ :=
  ⟨recurrence, gf_eq⟩

end OMA.S_oeis_a024849

theorem OMA.solution : type_of% @OMA.S_oeis_a024849.main :=
  OMA.S_oeis_a024849.conjecture
