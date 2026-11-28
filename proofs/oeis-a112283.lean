import OMAStatements.S_oeis_a112283
import Mathlib

namespace OMA.A112283Proof

open PowerSeries

/-! ## Generic coefficient lemmas for integer power series -/

theorem coeff_pow_eq_of_X_pow_dvd {f g : PowerSeries ℤ} {m : ℕ}
    (h : (X : PowerSeries ℤ) ^ m ∣ f - g) (n : ℕ) {j : ℕ} (hj : j < m) :
    coeff j (f ^ n) = coeff j (g ^ n) := by
  have h2 : (X : PowerSeries ℤ) ^ m ∣ f ^ n - g ^ n := dvd_trans h (sub_dvd_pow_sub_pow f g n)
  have h3 := (X_pow_dvd_iff.mp h2) j hj
  rw [map_sub, sub_eq_zero] at h3
  exact h3

theorem coeff_pow_add_X_pow_mul {f g h : PowerSeries ℤ} (m n : ℕ) (hfg : f = g + X ^ m * h)
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    coeff m (f ^ n) = coeff m (g ^ n) + (n : ℤ) * constantCoeff h := by
  have hsub : f - g = X ^ m * h := by rw [hfg]; ring
  have key : f ^ n - g ^ n =
      X ^ m * ((∑ i ∈ Finset.range n, f ^ i * g ^ (n - 1 - i)) * h) := by
    rw [← geom_sum₂_mul, hsub]; ring
  have hc : coeff m (f ^ n - g ^ n) = (n : ℤ) * constantCoeff h := by
    rw [key, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply]
    simp [hf, hg]
  rw [map_sub] at hc
  linarith

theorem X_pow_dvd_sub_trunc (f : PowerSeries ℤ) (N : ℕ) :
    (X : PowerSeries ℤ) ^ N ∣ f - (PowerSeries.trunc N f : PowerSeries ℤ) := by
  rw [X_pow_dvd_iff]
  intro m hm
  rw [map_sub, Polynomial.coeff_coe, coeff_trunc, if_pos hm, sub_self]

theorem coeff_pow_eq_trunc (f : PowerSeries ℤ) (N n k : ℕ) (hk : k < N) :
    coeff k (f ^ n) = ((PowerSeries.trunc N f) ^ n).coeff k := by
  rw [coeff_pow_eq_of_X_pow_dvd (X_pow_dvd_sub_trunc f N) n hk, ← Polynomial.coe_pow,
    Polynomial.coeff_coe]

/-- `[x^m] f^n = [x^m] (f mod x^m)^n + n * f_m` when `f_0 = 1` and `m ≥ 1`. -/
theorem trunc_step (f : PowerSeries ℤ) (m n : ℕ) (hm : 1 ≤ m) (hf : constantCoeff f = 1) :
    coeff m (f ^ n) =
      coeff m ((PowerSeries.trunc m f : PowerSeries ℤ) ^ n) + (n : ℤ) * coeff m f := by
  have h1 : coeff m (f ^ n) = coeff m ((PowerSeries.trunc (m + 1) f : PowerSeries ℤ) ^ n) :=
    coeff_pow_eq_of_X_pow_dvd (X_pow_dvd_sub_trunc f (m + 1)) n (Nat.lt_succ_self m)
  have h2 : (PowerSeries.trunc (m + 1) f : PowerSeries ℤ) =
      (PowerSeries.trunc m f : PowerSeries ℤ) + X ^ m * C (coeff m f) := by
    refine PowerSeries.ext fun j => ?_
    rw [map_add, Polynomial.coeff_coe, Polynomial.coeff_coe, coeff_trunc, coeff_trunc,
      coeff_X_pow_mul', coeff_C]
    rcases lt_trichotomy j m with hj | rfl | hj
    · have e1 : j < m + 1 := by omega
      have e2 : ¬ m ≤ j := by omega
      simp [e1, hj, e2]
    · simp
    · have e1 : ¬ j < m + 1 := by omega
      have e2 : ¬ j < m := by omega
      have e3 : m ≤ j := by omega
      have e4 : ¬ (j - m = 0) := by omega
      simp [e1, e2, e3, e4]
  have hc : ∀ N, 0 < N → constantCoeff (PowerSeries.trunc N f : PowerSeries ℤ) = 1 := by
    intro N hN
    rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, coeff_trunc, if_pos hN,
      coeff_zero_eq_constantCoeff_apply, hf]
  rw [h1, coeff_pow_add_X_pow_mul m n h2 (hc (m + 1) (by omega)) (hc m (by omega)),
    constantCoeff_C]

theorem coeff_one_of_pow (B : PowerSeries ℤ) (hB : constantCoeff B = 1) (n : ℕ) :
    coeff 1 (B ^ n) = (n : ℤ) * coeff 1 B := by
  have ht : (PowerSeries.trunc 1 B : PowerSeries ℤ) = 1 := by
    refine PowerSeries.ext fun j => ?_
    rw [Polynomial.coeff_coe, coeff_trunc, coeff_one]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [if_pos Nat.one_pos, if_pos rfl, coeff_zero_eq_constantCoeff_apply, hB]
    · rw [if_neg (show ¬ (j < 1) by omega), if_neg (show ¬ (j = 0) by omega)]
  rw [trunc_step B 1 n le_rfl hB, ht, one_pow, coeff_one, if_neg one_ne_zero, zero_add]

theorem dvd_coeff_mul {q r : ℤ} {f g : PowerSeries ℤ} (hf : ∀ j, q ∣ coeff j f)
    (hg : ∀ j, r ∣ coeff j g) (j : ℕ) : q * r ∣ coeff j (f * g) := by
  rw [coeff_mul]
  exact Finset.dvd_sum fun x _ => mul_dvd_mul (hf _) (hg _)

theorem dvd_coeff_pow {q : ℤ} {f : PowerSeries ℤ} (hf : ∀ j, q ∣ coeff j f) (m : ℕ) :
    ∀ j, q ^ m ∣ coeff j (f ^ m) := by
  induction m with
  | zero => intro j; simp
  | succ m ih => intro j; rw [pow_succ, pow_succ]; exact dvd_coeff_mul ih hf j

/-! ## Frobenius congruences (through polynomial truncations) -/

theorem frob_poly {p : ℕ} (hp : p.Prime) (P : Polynomial ℤ) (k : ℕ) :
    (p : ℤ) ∣ (P ^ p - Polynomial.expand ℤ p P).coeff k := by
  haveI := Fact.mk hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h : Polynomial.map (Int.castRingHom (ZMod p)) (P ^ p - Polynomial.expand ℤ p P) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_expand, ZMod.expand_card, sub_self]
  have h2 := congrArg (fun q => Polynomial.coeff q k) h
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at h2
  exact h2

theorem frob_poly2 {p : ℕ} (hp : p.Prime) (P : Polynomial ℤ) (k : ℕ) :
    (p : ℤ) ^ 2 ∣ (P ^ (p ^ 2) - Polynomial.expand ℤ p (P ^ p)).coeff k := by
  have h1 : (p : Polynomial ℤ) ∣ P ^ p - Polynomial.expand ℤ p P := by
    rw [← map_natCast (Polynomial.C (R := ℤ)) p]
    exact (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr (frob_poly hp P)
  have h2 := dvd_sub_pow_of_dvd_sub h1 1
  have e1 : P ^ (p ^ 2) = (P ^ p) ^ p ^ 1 := by rw [pow_one, ← pow_mul, sq]
  have e2 : Polynomial.expand ℤ p (P ^ p) = (Polynomial.expand ℤ p P) ^ p ^ 1 := by
    rw [pow_one, map_pow]
  have h3 : Polynomial.C ((p : ℤ) ^ 2) ∣ P ^ (p ^ 2) - Polynomial.expand ℤ p (P ^ p) := by
    rw [map_pow Polynomial.C (p : ℤ) 2, map_natCast Polynomial.C p, e1, e2]
    exact h2
  exact (Polynomial.C_dvd_iff_dvd_coeff _ _).mp h3 k

theorem frob_ndvd {p : ℕ} (hp : p.Prime) (B : PowerSeries ℤ) {k : ℕ} (hk : ¬ p ∣ k) :
    (p : ℤ) ∣ coeff k (B ^ p) := by
  have h := frob_poly hp (PowerSeries.trunc (k + 1) B) k
  rw [Polynomial.coeff_sub, Polynomial.coeff_expand hp.pos, if_neg hk, sub_zero] at h
  rw [coeff_pow_eq_trunc B (k + 1) p k (Nat.lt_succ_self k)]
  exact h

theorem frob_mul {p : ℕ} (hp : p.Prime) (B : PowerSeries ℤ) (j : ℕ) :
    (p : ℤ) ∣ coeff (p * j) (B ^ p) - coeff j B := by
  have hj : j < p * j + 1 := Nat.lt_succ_of_le (Nat.le_mul_of_pos_left j hp.pos)
  have h := frob_poly hp (PowerSeries.trunc (p * j + 1) B) (p * j)
  rw [Polynomial.coeff_sub, Polynomial.coeff_expand_mul' hp.pos, coeff_trunc, if_pos hj] at h
  rw [coeff_pow_eq_trunc B (p * j + 1) p (p * j) (Nat.lt_succ_self _)]
  exact h

theorem frob2_ndvd {p : ℕ} (hp : p.Prime) (B : PowerSeries ℤ) {k : ℕ} (hk : ¬ p ∣ k) :
    (p : ℤ) ^ 2 ∣ coeff k (B ^ (p ^ 2)) := by
  have h := frob_poly2 hp (PowerSeries.trunc (k + 1) B) k
  rw [Polynomial.coeff_sub, Polynomial.coeff_expand hp.pos, if_neg hk, sub_zero] at h
  rw [coeff_pow_eq_trunc B (k + 1) (p ^ 2) k (Nat.lt_succ_self k)]
  exact h

theorem frob2_mul {p : ℕ} (hp : p.Prime) (B : PowerSeries ℤ) (j : ℕ) :
    (p : ℤ) ^ 2 ∣ coeff (p * j) (B ^ (p ^ 2)) - coeff j (B ^ p) := by
  have hj : j < p * j + 1 := Nat.lt_succ_of_le (Nat.le_mul_of_pos_left j hp.pos)
  have h := frob_poly2 hp (PowerSeries.trunc (p * j + 1) B) (p * j)
  rw [Polynomial.coeff_sub, Polynomial.coeff_expand_mul' hp.pos,
    ← coeff_pow_eq_trunc B (p * j + 1) p j hj] at h
  rw [coeff_pow_eq_trunc B (p * j + 1) (p ^ 2) (p * j) (Nat.lt_succ_self _)]
  exact h

/-! ## The key congruence `[x^p] D^p = p * D_p (mod p^3)` for odd `p` -/

theorem key_c {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (D : PowerSeries ℤ)
    (h0 : constantCoeff D = 1) (hd : ∀ j, 1 ≤ j → j < p → (p : ℤ) ∣ coeff j D) :
    (p : ℤ) ^ 3 ∣ coeff p (D ^ p) - (p : ℤ) * coeff p D := by
  rw [trunc_step D p p (by omega) h0, add_sub_cancel_right]
  obtain ⟨V, hV⟩ : ∃ V : PowerSeries ℤ, V = (PowerSeries.trunc p D : PowerSeries ℤ) - 1 :=
    ⟨_, rfl⟩
  have hV1 : ∀ j, (p : ℤ) ∣ coeff j V := by
    intro j
    rw [hV, map_sub, Polynomial.coeff_coe, coeff_trunc, coeff_one]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [if_pos hp.pos, if_pos rfl, coeff_zero_eq_constantCoeff_apply, h0, sub_self]
      exact dvd_zero _
    · rw [if_neg (show ¬ (j = 0) by omega), sub_zero]
      by_cases hjp : j < p
      · rw [if_pos hjp]; exact hd j hj hjp
      · rw [if_neg hjp]; exact dvd_zero _
  have hVp : coeff p V = 0 := by
    rw [hV, map_sub, Polynomial.coeff_coe, coeff_trunc, coeff_one, if_neg (lt_irrefl p),
      if_neg (show ¬ (p = 0) by omega), sub_zero]
  have hH : (PowerSeries.trunc p D : PowerSeries ℤ) = V + 1 := by rw [hV]; ring
  rw [hH, add_pow, map_sum]
  apply Finset.dvd_sum
  intro i hi
  rw [Finset.mem_range] at hi
  rw [one_pow, mul_one, ← map_natCast (C (R := ℤ)) (p.choose i), coeff_mul_C]
  rcases (show i = 0 ∨ i = 1 ∨ (2 ≤ i ∧ i < p) ∨ i = p by omega) with h | h | ⟨h2, h3⟩ | h
  · rw [h, pow_zero, coeff_one, if_neg (show ¬ (p = 0) by omega), zero_mul]
    exact dvd_zero _
  · rw [h, pow_one, hVp, zero_mul]
    exact dvd_zero _
  · have hc : (p : ℤ) ∣ ((p.choose i : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr (hp.dvd_choose_self (by omega) h3)
    have hv : (p : ℤ) ^ 2 ∣ coeff p (V ^ i) :=
      dvd_trans (pow_dvd_pow _ h2) (dvd_coeff_pow hV1 i p)
    have := mul_dvd_mul hv hc
    rw [← pow_succ] at this
    exact this
  · rw [h]
    have hv : (p : ℤ) ^ 3 ∣ coeff p (V ^ p) :=
      dvd_trans (pow_dvd_pow _ hp3) (dvd_coeff_pow hV1 p p)
    exact dvd_mul_of_dvd_left hv _

/-! ## Integer arithmetic helpers -/

theorem eq_one_of_mul_bounds {q b : ℤ} (hq : 0 < q) (h1 : 1 ≤ q * b) (h2 : q * b ≤ q) :
    b = 1 := by
  have hb0 : 0 < b := by
    by_contra h
    push_neg at h
    nlinarith
  have hb1 : b ≤ 1 := by
    by_contra h
    push_neg at h
    nlinarith
  omega

theorem eq_one_of_dvd_sub {q x : ℤ} (hd : q ∣ x - 1) (h1 : 1 ≤ x) (h2 : x ≤ q) : x = 1 := by
  have := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) (by omega) hd
  omega

theorem ne_one_of_dvd {q x : ℤ} (hq : 2 ≤ q) (hd : q ∣ x) : x ≠ 1 := by
  rintro rfl
  have := Int.le_of_dvd one_pos hd
  omega

/-! ## The claim for a single row -/

theorem normalize {n : ℕ} (hn : 1 ≤ n) {a : ℕ → ℤ} (ha0 : a 0 = 1) {B : PowerSeries ℤ}
    (hB : B ^ n = mk a) : ∃ B' : PowerSeries ℤ, B' ^ n = mk a ∧ constantCoeff B' = 1 := by
  have h0 : (constantCoeff B) ^ n = 1 := by
    rw [← map_pow, ← coeff_zero_eq_constantCoeff_apply, hB, coeff_mk, ha0]
  rcases (pow_eq_one_iff_of_ne_zero (by omega)).mp h0 with h | ⟨h, he⟩
  · exact ⟨B, hB, h⟩
  · refine ⟨-B, ?_, ?_⟩
    · rw [he.neg_pow, hB]
    · rw [map_neg, h, neg_neg]

theorem prime_case {p : ℕ} (hp : p.Prime) (B : PowerSeries ℤ) (hB0 : constantCoeff B = 1)
    (hb : ∀ k, 1 ≤ k → 1 ≤ coeff k (B ^ p) ∧ coeff k (B ^ p) ≤ (p : ℤ)) :
    coeff p (B ^ p) = 1 ∧ ∀ k, 1 ≤ k → k < p → coeff k (B ^ p) ≠ 1 := by
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hb1 : coeff 1 B = 1 := by
    have h := hb 1 le_rfl
    rw [coeff_one_of_pow B hB0] at h
    exact eq_one_of_mul_bounds (by omega) h.1 h.2
  refine ⟨?_, ?_⟩
  · have h := frob_mul hp B 1
    rw [mul_one, hb1] at h
    have hpb := hb p hp.one_lt.le
    exact eq_one_of_dvd_sub h hpb.1 hpb.2
  · intro k hk1 hkp
    have hnd : ¬ p ∣ k := fun hd => by
      have := Nat.le_of_dvd (by omega) hd
      omega
    exact ne_one_of_dvd hp2 (frob_ndvd hp B hnd)

theorem sq_case {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (B : PowerSeries ℤ)
    (hB0 : constantCoeff B = 1)
    (hb : ∀ k, 1 ≤ k → 1 ≤ coeff k (B ^ (p ^ 2)) ∧ coeff k (B ^ (p ^ 2)) ≤ (p : ℤ) ^ 2) :
    coeff (p ^ 2) (B ^ (p ^ 2)) = 1 ∧ ∀ k, 1 ≤ k → k < p ^ 2 → coeff k (B ^ (p ^ 2)) ≠ 1 := by
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hb1 : coeff 1 B = 1 := by
    have h := hb 1 le_rfl
    rw [coeff_one_of_pow B hB0] at h
    push_cast at h
    exact eq_one_of_mul_bounds (pow_pos (by omega) 2) h.1 h.2
  have hD0 : constantCoeff (B ^ p) = 1 := by rw [map_pow, hB0, one_pow]
  have hd1 : coeff 1 (B ^ p) = p := by rw [coeff_one_of_pow B hB0, hb1, mul_one]
  have hdj : ∀ j, 1 ≤ j → j < p → (p : ℤ) ∣ coeff j (B ^ p) := by
    intro j hj1 hjp
    exact frob_ndvd hp B (fun hd => by
      have := Nat.le_of_dvd (by omega) hd
      omega)
  have hBB : B ^ (p ^ 2) = (B ^ p) ^ p := by rw [← pow_mul, sq]
  -- a_p = p
  have hap : coeff p (B ^ (p ^ 2)) = p := by
    have h := frob2_mul hp B 1
    rw [mul_one, hd1] at h
    have hb' := hb p hp.one_lt.le
    have h0 := Int.eq_zero_of_abs_lt_dvd h (by
      rw [abs_lt]
      constructor <;> nlinarith [hb'.1, hb'.2, hp2])
    linarith
  -- p^3 ∣ a_p - p d_p, hence d_p = 1 mod p^2
  have hc := key_c hp hp3 (B ^ p) hD0 hdj
  rw [← hBB, hap] at hc
  have hdp : (p : ℤ) ^ 2 ∣ coeff p (B ^ p) - 1 := by
    have h1 : (p : ℤ) * (p : ℤ) ^ 2 ∣ (p : ℤ) * (1 - coeff p (B ^ p)) := by
      have e1 : (p : ℤ) * (p : ℤ) ^ 2 = (p : ℤ) ^ 3 := by ring
      have e2 : (p : ℤ) * (1 - coeff p (B ^ p)) = (p : ℤ) - (p : ℤ) * coeff p (B ^ p) := by ring
      rw [e1, e2]
      exact hc
    have h2 := (mul_dvd_mul_iff_left (show (p : ℤ) ≠ 0 by omega)).mp h1
    have h3 := dvd_neg.mpr h2
    rwa [neg_sub] at h3
  refine ⟨?_, ?_⟩
  · have h := frob2_mul hp B p
    have e : p * p = p ^ 2 := by ring
    rw [e] at h
    have h2 : (p : ℤ) ^ 2 ∣ coeff (p ^ 2) (B ^ (p ^ 2)) - 1 := by
      have := dvd_add h hdp
      rwa [sub_add_sub_cancel] at this
    have hb' := hb (p ^ 2) (Nat.one_le_pow _ _ hp.pos)
    exact eq_one_of_dvd_sub h2 hb'.1 hb'.2
  · intro k hk1 hkp
    have hpz : (p : ℤ) ∣ (p : ℤ) ^ 2 := dvd_pow_self _ two_ne_zero
    by_cases hdk : p ∣ k
    · obtain ⟨j, rfl⟩ := hdk
      have hj1 : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h | h
        · subst h
          simp at hk1
        · exact h
      have hjp : j < p := by
        by_contra h
        push_neg at h
        have h' : p * p ≤ p * j := Nat.mul_le_mul le_rfl h
        rw [sq] at hkp
        exact absurd hkp (not_lt.mpr h')
      have h1 := frob2_mul hp B j
      have h2 := hdj j hj1 hjp
      have h3 : (p : ℤ) ∣ coeff (p * j) (B ^ (p ^ 2)) := by
        have h4 := dvd_trans hpz h1
        have h5 := dvd_add h4 h2
        rwa [sub_add_cancel] at h5
      exact ne_one_of_dvd hp2 h3
    · exact ne_one_of_dvd hp2 (dvd_trans hpz (frob2_ndvd hp B hdk))

theorem one_le_of_cases {n : ℕ}
    (hn : n = 1 ∨ n.Prime ∨ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ n = p ^ 2) : 1 ≤ n := by
  rcases hn with rfl | hp | ⟨p, hp, -, rfl⟩
  · exact le_rfl
  · exact hp.one_lt.le
  · exact Nat.one_le_pow _ _ hp.pos

theorem row_claim {n : ℕ} (hn : n = 1 ∨ n.Prime ∨ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ n = p ^ 2)
    {a : ℕ → ℤ} (ha : OMA.S_oeis_a112283.IsRow n a) :
    a n = 1 ∧ ∀ k, 1 ≤ k → k < n → a k ≠ 1 := by
  unfold OMA.S_oeis_a112283.IsRow at ha
  obtain ⟨ha0, hab, B, hB⟩ := ha
  have hn1 : 1 ≤ n := one_le_of_cases hn
  obtain ⟨B', hB', hB'0⟩ := normalize hn1 ha0 hB
  have hcoef : ∀ k, coeff k (B' ^ n) = a k := fun k => by rw [hB', coeff_mk]
  rcases hn with rfl | hp | ⟨p, hp, hp2, rfl⟩
  · refine ⟨?_, fun k h1 h2 => absurd h2 (by omega)⟩
    obtain ⟨h1, h2⟩ := hab 1 le_rfl
    push_cast at h2
    omega
  · have hb : ∀ k, 1 ≤ k → 1 ≤ coeff k (B' ^ n) ∧ coeff k (B' ^ n) ≤ (n : ℤ) := by
      intro k hk
      rw [hcoef]
      exact hab k hk
    obtain ⟨h1, h2⟩ := prime_case hp B' hB'0 hb
    rw [hcoef] at h1
    refine ⟨h1, fun k hk1 hkn => ?_⟩
    rw [← hcoef k]
    exact h2 k hk1 hkn
  · have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hb : ∀ k, 1 ≤ k →
        1 ≤ coeff k (B' ^ (p ^ 2)) ∧ coeff k (B' ^ (p ^ 2)) ≤ (p : ℤ) ^ 2 := by
      intro k hk
      rw [hcoef]
      have := hab k hk
      push_cast at this
      exact this
    obtain ⟨h1, h2⟩ := sq_case hp hp3 B' hB'0 hb
    rw [hcoef] at h1
    refine ⟨h1, fun k hk1 hkn => ?_⟩
    rw [← hcoef k]
    exact h2 k hk1 hkn

/-! ## Existence of the row for every `n ≥ 1` (the greedy construction) -/

/-- The next root coefficient: it puts `[x^(k+1)]` of the `n`-th power into `[1, n]`. -/
noncomputable def cstep (n : ℕ) (Q : PowerSeries ℤ) (k : ℕ) : ℤ :=
  -((coeff (k + 1) (Q ^ n) - 1) / (n : ℤ))

/-- The truncations `Qs n k` of the root (degree `≤ k`). -/
noncomputable def Qs (n : ℕ) : ℕ → PowerSeries ℤ
  | 0 => 1
  | k + 1 => Qs n k + X ^ (k + 1) * C (cstep n (Qs n k) k)

theorem Qs_zero (n : ℕ) : Qs n 0 = 1 := rfl

theorem Qs_succ (n k : ℕ) : Qs n (k + 1) = Qs n k + X ^ (k + 1) * C (cstep n (Qs n k) k) := rfl

theorem Qs_stable (n k l : ℕ) (hkl : k ≤ l) (j : ℕ) (hj : j ≤ k) :
    coeff j (Qs n l) = coeff j (Qs n k) := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    rw [Qs_succ, map_add, coeff_X_pow_mul', if_neg (show ¬ (l + 1 ≤ j) by omega), add_zero, ih]

theorem Qs_const (n k : ℕ) : constantCoeff (Qs n k) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, Qs_stable n 0 k (Nat.zero_le k) 0 le_rfl, Qs_zero,
    coeff_one, if_pos rfl]

/-- The root itself. -/
noncomputable def Bs (n : ℕ) : PowerSeries ℤ := mk fun k => coeff k (Qs n k)

theorem Bs_dvd (n k : ℕ) : (X : PowerSeries ℤ) ^ (k + 1) ∣ Bs n - Qs n k := by
  rw [X_pow_dvd_iff]
  intro j hj
  rw [map_sub, Bs, coeff_mk, Qs_stable n j k (by omega) j le_rfl, sub_self]

theorem Bs_const (n : ℕ) : constantCoeff (Bs n) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, Bs, coeff_mk, coeff_zero_eq_constantCoeff_apply,
    Qs_const]

theorem Qs_step (n k : ℕ) :
    coeff (k + 1) (Qs n (k + 1) ^ n) =
      coeff (k + 1) (Qs n k ^ n) + (n : ℤ) * cstep n (Qs n k) k := by
  rw [coeff_pow_add_X_pow_mul (k + 1) n (Qs_succ n k) (Qs_const n (k + 1)) (Qs_const n k),
    constantCoeff_C]

theorem cstep_bounds (n : ℕ) (hn : 1 ≤ n) (Q : PowerSeries ℤ) (k : ℕ) :
    1 ≤ coeff (k + 1) (Q ^ n) + (n : ℤ) * cstep n Q k ∧
      coeff (k + 1) (Q ^ n) + (n : ℤ) * cstep n Q k ≤ (n : ℤ) := by
  unfold cstep
  have hn' : (0 : ℤ) < n := by omega
  have h1 := Int.emod_add_mul_ediv (coeff (k + 1) (Q ^ n) - 1) n
  have h2 := Int.emod_nonneg (coeff (k + 1) (Q ^ n) - 1) hn'.ne'
  have h3 := Int.emod_lt_of_pos (coeff (k + 1) (Q ^ n) - 1) hn'
  rw [mul_neg, ← sub_eq_add_neg]
  constructor <;> linarith

theorem row_exists (n : ℕ) (hn : 1 ≤ n) : ∃ a : ℕ → ℤ, OMA.S_oeis_a112283.IsRow n a := by
  refine ⟨fun k => coeff k (Bs n ^ n), ?_⟩
  unfold OMA.S_oeis_a112283.IsRow
  refine ⟨?_, ?_, Bs n, ?_⟩
  · show coeff 0 (Bs n ^ n) = 1
    rw [coeff_zero_eq_constantCoeff_apply, map_pow, Bs_const, one_pow]
  · intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    show 1 ≤ coeff (k' + 1) (Bs n ^ n) ∧ coeff (k' + 1) (Bs n ^ n) ≤ (n : ℤ)
    rw [coeff_pow_eq_of_X_pow_dvd (Bs_dvd n (k' + 1)) n (Nat.lt_succ_self _), Qs_step]
    exact cstep_bounds n hn (Qs n k') k'
  · exact PowerSeries.ext fun k => by rw [coeff_mk]

end OMA.A112283Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a112283.main := by
  intro n hn
  have hn1 : 1 ≤ n := OMA.A112283Proof.one_le_of_cases hn
  have hex := OMA.A112283Proof.row_exists n hn1
  have hrow : OMA.S_oeis_a112283.IsRow n (OMA.S_oeis_a112283.T n) := by
    unfold OMA.S_oeis_a112283.T
    rw [dif_pos hex]
    exact hex.choose_spec
  obtain ⟨h1, h2⟩ := OMA.A112283Proof.row_claim hn hrow
  have hmem : n ∈ {m : ℕ | 1 ≤ m ∧ OMA.S_oeis_a112283.T n m = 1} :=
    show 1 ≤ n ∧ OMA.S_oeis_a112283.T n n = 1 from ⟨hn1, h1⟩
  unfold OMA.S_oeis_a112283.A112283
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨n, hmem⟩
  intro k hk
  have hk' : 1 ≤ k ∧ OMA.S_oeis_a112283.T n k = 1 := hk
  by_contra hlt
  push_neg at hlt
  exact h2 k hk'.1 hlt hk'.2
