import OMAStatements.S_oeis_a402341

/-
# A402341: proof of the OEIS conjecture (2-adic valuation of the central coefficient)

Credit: @ShadowAlzazel
Prepared by the Fang and Fox Lemma Office (paper proof by Kumi-San, reviewed by Alo).

For even n = 2t, with M = 15t, the central coefficient a(2t) of (1 + X + ... + X^15)^(2t)
has 2-adic valuation s(M), the binary digit sum of M.

Proof (the folded circle, written without Laurent polynomials).
1. 1 + X + ... + X^15 = (1 + X)(1 + X^2)(1 + X^4)(1 + X^8).
2. Call a polynomial F good of half-degree D if F = (1 + X)^(2D) + T, where T is a Z-combination of
   the tail generators gen D J = 2^(s J + 1) (1 + X)^(2(D - J)) X^J with 1 <= J <= D.
   (In the variable v = (1 + X)^2 / X this is the strictly Kummer condition on the coefficients.)
3. Good forms multiply: products of tail generators stay tail generators, because the binary
   digit sum is subadditive, s(a + b) <= s(a) + s(b).
4. Doubling: if (1 + X^n)^2 is good of half-degree n and s(n) = 1, then
   (1 + X^(2n))^2 = ((1 + X^n)^2 - 2 X^n)^2 is good of half-degree 2n. Squaring turns the 2 into 4.
5. So (1 + X + ... + X^15)^2 is good of half-degree 15, and its t-th power is good of half-degree M.
6. The X^M coefficient of (1 + X)^(2M) is C(2M, M), with 2-adic valuation exactly s(M) (Kummer).
   The X^M coefficient of each tail generator is 2^(s J + 1) C(2(M - J), M - J), divisible by
   2^(s J + 1 + s(M - J)), hence by 2^(s M + 1). So a(2t) has 2-adic valuation exactly s(M).
-/

open Polynomial

namespace FFL_A402341

/-- The binary digit sum. -/
def s (n : ℕ) : ℕ := (Nat.digits 2 n).sum

lemma s_two_mul (m : ℕ) : s (2 * m) = s m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [s]
  · unfold s
    rw [Nat.digits_def' (by norm_num) (by omega)]
    simp

lemma s_le (n : ℕ) : s n ≤ n := Nat.digit_sum_le 2 n

lemma v_factorial (n : ℕ) : padicValNat 2 n.factorial = n - s n := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  simpa [s] using h

/-- The binary digit sum is subadditive (from Legendre's formula). -/
lemma s_add_le (a b : ℕ) : s (a + b) ≤ s a + s b := by
  have hne : (a + b).factorial ≠ 0 := Nat.factorial_ne_zero _
  have h3 : padicValNat 2 (a.factorial * b.factorial) ≤ padicValNat 2 (a + b).factorial :=
    (padicValNat_dvd_iff_le hne).mp
      (pow_padicValNat_dvd.trans (Nat.factorial_mul_factorial_dvd_factorial_add a b))
  rw [padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _), v_factorial,
    v_factorial, v_factorial] at h3
  have := s_le a
  have := s_le b
  have := s_le (a + b)
  omega

/-- Kummer: the 2-adic valuation of the central binomial coefficient C(2m, m) is s(m). -/
lemma v_central (m : ℕ) : padicValNat 2 ((2 * m).choose m) = s m := by
  have h := sub_one_mul_padicValNat_choose_eq_sub_sum_digits' (p := 2) (k := m) (n := m)
  have h2 : s (m + m) = s m := by rw [← two_mul]; exact s_two_mul m
  unfold s at h2 ⊢
  rw [two_mul]
  omega

lemma dvd_central (m : ℕ) : (2 : ℤ) ^ s m ∣ ((2 * m).choose m : ℤ) := by
  have h : 2 ^ s m ∣ (2 * m).choose m := by
    rw [← v_central]
    exact pow_padicValNat_dvd
  exact_mod_cast h

/-- Tail generators. -/
noncomputable def gen (D J : ℕ) : ℤ[X] :=
  C ((2 : ℤ) ^ (s J + 1)) * (1 + X) ^ (2 * (D - J)) * X ^ J

/-- Tails of half-degree D: the Z-span of the generators gen D J, 1 <= J <= D. -/
noncomputable def Tail (D : ℕ) : Submodule ℤ ℤ[X] :=
  Submodule.span ℤ {p | ∃ J, 1 ≤ J ∧ J ≤ D ∧ p = gen D J}

lemma gen_mem {D J : ℕ} (h1 : 1 ≤ J) (h2 : J ≤ D) : gen D J ∈ Tail D :=
  Submodule.subset_span ⟨J, h1, h2, rfl⟩

lemma coeff_gen (D J : ℕ) (hJ : J ≤ D) :
    (gen D J).coeff D = 2 ^ (s J + 1) * ((2 * (D - J)).choose (D - J) : ℤ) := by
  have h : (gen D J).coeff ((D - J) + J) =
      2 ^ (s J + 1) * ((2 * (D - J)).choose (D - J) : ℤ) := by
    rw [gen, coeff_mul_X_pow, coeff_C_mul, coeff_one_add_X_pow]
  rwa [Nat.sub_add_cancel hJ] at h

/-- The X^D coefficient of a tail of half-degree D is divisible by 2^(s D + 1). -/
lemma tail_coeff {D : ℕ} {T : ℤ[X]} (hT : T ∈ Tail D) : (2 : ℤ) ^ (s D + 1) ∣ T.coeff D := by
  induction hT using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨J, _, h2, rfl⟩ := hp
    rw [coeff_gen D J h2]
    have hs : s D ≤ s J + s (D - J) := by
      have h := s_add_le J (D - J)
      rwa [Nat.add_sub_cancel' h2] at h
    have h3 : (2 : ℤ) ^ (s D + 1) ∣ 2 ^ (s J + 1) * 2 ^ s (D - J) := by
      rw [← pow_add]
      exact pow_dvd_pow 2 (by omega)
    exact h3.trans (mul_dvd_mul_left _ (dvd_central _))
  | zero => simp
  | add x y _ _ hx hy => rw [coeff_add]; exact dvd_add hx hy
  | smul r x _ hx => rw [coeff_smul, smul_eq_mul]; exact dvd_mul_of_dvd_right hx r

/-- Multiplying a tail by (1 + X)^(2D) raises its half-degree by D. -/
lemma tail_shift {E : ℕ} (D : ℕ) {T : ℤ[X]} (hT : T ∈ Tail E) :
    (1 + X) ^ (2 * D) * T ∈ Tail (D + E) := by
  induction hT using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨J, h1, h2, rfl⟩ := hp
    have h : (1 + X) ^ (2 * D) * gen E J = gen (D + E) J := by
      unfold gen
      rw [show 2 * (D + E - J) = 2 * D + 2 * (E - J) by omega, pow_add]
      ring
    rw [h]
    exact gen_mem h1 (by omega)
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

lemma gen_mul (D E a b : ℕ) (ha : a ≤ D) (hb : b ≤ E) :
    gen D a * gen E b = (2 : ℤ) ^ (s a + s b + 1 - s (a + b)) • gen (D + E) (a + b) := by
  have hs := s_add_le a b
  have e : C ((2 : ℤ) ^ (s a + 1)) * C (2 ^ (s b + 1)) =
      C (2 ^ (s a + s b + 1 - s (a + b))) * C (2 ^ (s (a + b) + 1)) := by
    rw [← C_mul, ← C_mul, ← pow_add, ← pow_add]
    congr 2
    omega
  unfold gen
  rw [smul_eq_C_mul, show 2 * (D + E - (a + b)) = 2 * (D - a) + 2 * (E - b) by omega,
    pow_add (1 + X : ℤ[X]) (2 * (D - a)) (2 * (E - b)), pow_add (X : ℤ[X]) a b]
  linear_combination ((1 + X) ^ (2 * (D - a)) * (1 + X) ^ (2 * (E - b)) * X ^ a * X ^ b) * e

/-- Tails multiply (the jewels form a monoid). -/
lemma tail_mul {D E : ℕ} {T U : ℤ[X]} (hT : T ∈ Tail D) (hU : U ∈ Tail E) :
    T * U ∈ Tail (D + E) := by
  have h : T * U ∈ Tail D * Tail E := Submodule.mul_mem_mul hT hU
  simp only [Tail] at h
  rw [Submodule.span_mul_span] at h
  refine (Submodule.span_le.mpr ?_) h
  rintro _ ⟨p, ⟨a, ha1, ha2, rfl⟩, q, ⟨b, hb1, hb2, rfl⟩, rfl⟩
  show gen D a * gen E b ∈ Tail (D + E)
  rw [gen_mul D E a b ha2 hb2]
  exact Submodule.smul_mem _ _ (gen_mem (by omega) (by omega))

/-- The middle term of the doubling step: 4 X^n times a tail of half-degree n. -/
lemma tail_X {n : ℕ} (hn : s n = 1) {T : ℤ[X]} (hT : T ∈ Tail n) :
    C 4 * X ^ n * T ∈ Tail (2 * n) := by
  induction hT using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨J, h1, h2, rfl⟩ := hp
    have hs : s (n + J) ≤ 1 + s J := by have h := s_add_le n J; omega
    have e : (C 4 : ℤ[X]) * C (2 ^ (s J + 1)) =
        C (2 ^ (s J + 2 - s (n + J))) * C (2 ^ (s (n + J) + 1)) := by
      rw [← C_mul, ← C_mul, ← pow_add,
        show s J + 2 - s (n + J) + (s (n + J) + 1) = (s J + 1) + 2 by omega, pow_add]
      congr 1
      ring
    have h : C 4 * X ^ n * gen n J = (2 : ℤ) ^ (s J + 2 - s (n + J)) • gen (2 * n) (n + J) := by
      unfold gen
      rw [smul_eq_C_mul, show 2 * (2 * n - (n + J)) = 2 * (n - J) by omega,
        pow_add (X : ℤ[X]) n J]
      linear_combination ((1 + X) ^ (2 * (n - J)) * X ^ n * X ^ J) * e
    rw [h]
    exact Submodule.smul_mem _ _ (gen_mem (by omega) (by omega))
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

/-- Good forms of half-degree D: the leading power of (1 + X)^2 plus a tail. -/
def Good (D : ℕ) (F : ℤ[X]) : Prop := ∃ T ∈ Tail D, F = (1 + X) ^ (2 * D) + T

lemma good_mul {D E : ℕ} {F G : ℤ[X]} (hF : Good D F) (hG : Good E G) :
    Good (D + E) (F * G) := by
  obtain ⟨T, hT, rfl⟩ := hF
  obtain ⟨U, hU, rfl⟩ := hG
  refine ⟨(1 + X) ^ (2 * D) * U + (1 + X) ^ (2 * E) * T + T * U, ?_, ?_⟩
  · refine add_mem (add_mem (tail_shift D hU) ?_) (tail_mul hT hU)
    rw [add_comm D E]
    exact tail_shift E hT
  · rw [mul_add 2 D E, pow_add]
    ring

lemma good_pow {D : ℕ} {F : ℤ[X]} (hF : Good D F) (t : ℕ) : Good (t * D) (F ^ t) := by
  induction t with
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | succ t ih =>
    rw [pow_succ, Nat.succ_mul]
    exact good_mul ih hF

lemma C_four : (C 4 : ℤ[X]) = 4 := by simp

/-- Doubling keeps the jewel: squaring pays for the -2. -/
lemma good_double {n : ℕ} (hn : s n = 1) (h : Good n ((1 + X ^ n) ^ 2)) :
    Good (2 * n) ((1 + X ^ (2 * n)) ^ 2) := by
  obtain ⟨T, hT, hE⟩ := h
  have hn0 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp [s] at hn
    · omega
  have h2n : s (2 * n) = 1 := by rw [s_two_mul, hn]
  refine ⟨((1 + X) ^ (2 * n) * T + (1 + X) ^ (2 * n) * T) + T * T - gen (2 * n) n
    - C 4 * X ^ n * T + gen (2 * n) (2 * n), ?_, ?_⟩
  · refine add_mem (sub_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
    · have h1 := tail_shift n hT
      rw [← two_mul] at h1
      exact add_mem h1 h1
    · have h1 := tail_mul hT hT
      rwa [← two_mul] at h1
    · exact gen_mem hn0 (by omega)
    · exact tail_X hn hT
    · exact gen_mem (by omega) le_rfl
  · have e1 : gen (2 * n) n = C 4 * (1 + X) ^ (2 * n) * X ^ n := by
      unfold gen
      rw [hn, show 2 * (2 * n - n) = 2 * n by omega]
      norm_num
    have e2 : gen (2 * n) (2 * n) = C 4 * X ^ (2 * n) := by
      unfold gen
      rw [h2n, Nat.sub_self]
      norm_num
    have e3 : (1 + X ^ (2 * n) : ℤ[X]) ^ 2 = ((1 + X ^ n) ^ 2 - 2 * X ^ n) ^ 2 := by ring
    rw [e3, hE, e1, e2, C_four]
    ring

lemma s_one : s 1 = 1 := by norm_num [s]
lemma s_two : s 2 = 1 := by norm_num [s]
lemma s_four : s 4 = 1 := by norm_num [s]

/-- (1 + X + ... + X^15)^2 is good of half-degree 15. -/
lemma good_P : Good 15 ((∑ k ∈ Finset.range 16, (X : ℤ[X]) ^ k) ^ 2) := by
  have g1 : Good 1 ((1 + X ^ 1) ^ 2) := ⟨0, zero_mem _, by ring⟩
  have g2 := good_double (n := 1) s_one g1
  rw [show 2 * 1 = 2 from rfl] at g2
  have g4 := good_double (n := 2) s_two g2
  rw [show 2 * 2 = 4 from rfl] at g4
  have g8 := good_double (n := 4) s_four g4
  rw [show 2 * 4 = 8 from rfl] at g8
  have hP : (∑ k ∈ Finset.range 16, (X : ℤ[X]) ^ k) ^ 2 =
      (1 + X ^ 1) ^ 2 * (1 + X ^ 2) ^ 2 * (1 + X ^ 4) ^ 2 * (1 + X ^ 8) ^ 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  rw [hP]
  show Good (1 + 2 + 4 + 8) _
  exact good_mul (good_mul (good_mul g1 g2) g4) g8

/-- The theorem, for n = 2t. -/
theorem central (t : ℕ) : padicValNat 2 (OMA.S_oeis_a402341.a (2 * t)) = s (15 * t) := by
  have hidx : 15 * (2 * t) / 2 = 15 * t := by omega
  have hmapG : (OMA.S_oeis_a402341.geom16).map (Nat.castRingHom ℤ) =
      ∑ k ∈ Finset.range 16, (X : ℤ[X]) ^ k := by
    simp [OMA.S_oeis_a402341.geom16, Polynomial.map_sum]
  have h1 : ((OMA.S_oeis_a402341.a (2 * t) : ℕ) : ℤ) =
      (((∑ k ∈ Finset.range 16, (X : ℤ[X]) ^ k) ^ 2) ^ t).coeff (15 * t) := by
    rw [OMA.S_oeis_a402341.a, hidx, ← pow_mul, ← hmapG, ← Polynomial.map_pow,
      Polynomial.coeff_map]
    simp
  obtain ⟨T, hT, hE⟩ := good_pow good_P t
  rw [mul_comm t 15] at hT hE
  have hc : ((OMA.S_oeis_a402341.a (2 * t) : ℕ) : ℤ) =
      ((2 * (15 * t)).choose (15 * t) : ℤ) + T.coeff (15 * t) := by
    rw [h1, hE, coeff_add, coeff_one_add_X_pow]
  have hTd := tail_coeff hT
  have hv := v_central (15 * t)
  have hchoose0 : (2 * (15 * t)).choose (15 * t) ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hd1 : 2 ^ s (15 * t) ∣ (2 * (15 * t)).choose (15 * t) := by
    rw [← hv]
    exact pow_padicValNat_dvd
  have hd2 : ¬ 2 ^ (s (15 * t) + 1) ∣ (2 * (15 * t)).choose (15 * t) := by
    rw [← hv]
    exact pow_succ_padicValNat_not_dvd hchoose0
  have hA1 : 2 ^ s (15 * t) ∣ OMA.S_oeis_a402341.a (2 * t) := by
    have h : (2 : ℤ) ^ s (15 * t) ∣ ((OMA.S_oeis_a402341.a (2 * t) : ℕ) : ℤ) := by
      rw [hc]
      exact dvd_add (by exact_mod_cast hd1) ((pow_dvd_pow 2 (Nat.le_succ _)).trans hTd)
    exact_mod_cast h
  have hA2 : ¬ 2 ^ (s (15 * t) + 1) ∣ OMA.S_oeis_a402341.a (2 * t) := by
    intro h
    have h' : (2 : ℤ) ^ (s (15 * t) + 1) ∣ ((OMA.S_oeis_a402341.a (2 * t) : ℕ) : ℤ) := by
      exact_mod_cast h
    rw [hc] at h'
    have h'' : (2 : ℤ) ^ (s (15 * t) + 1) ∣ ((2 * (15 * t)).choose (15 * t) : ℤ) := by
      have h3 := dvd_sub h' hTd
      simpa using h3
    exact hd2 (by exact_mod_cast h'')
  have hA0 : OMA.S_oeis_a402341.a (2 * t) ≠ 0 := by
    intro h
    rw [h] at hA2
    exact hA2 (dvd_zero _)
  have le1 := (padicValNat_dvd_iff_le hA0).mp hA1
  have le2 : ¬ s (15 * t) + 1 ≤ padicValNat 2 (OMA.S_oeis_a402341.a (2 * t)) :=
    fun h => hA2 ((padicValNat_dvd_iff_le hA0).mpr h)
  omega

end FFL_A402341

theorem OMA.solution : type_of% @OMA.S_oeis_a402341.main := by
  intro n hn
  obtain ⟨t, rfl⟩ := hn
  rw [← two_mul, FFL_A402341.central]
  rw [show 15 * (2 * t) / 2 = 15 * t by omega]
  rfl
