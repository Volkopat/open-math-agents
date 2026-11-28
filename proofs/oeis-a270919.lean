import OMAStatements.S_oeis_a270919
import Mathlib

/-!
# Proof of OEIS A270919 Supercongruence

1. In `PowerSeries (ZMod p)` (characteristic `p`), for any `F : PowerSeries ℤ`,
   `coeff m (F^p)` is divisible by `p` for all `1 <= m < p` (Frobenius `F^p` vanishes
   on degrees not divisible by `p`).
2. For power series `F, G : PowerSeries ℤ` with `coeff 0 = 1` and `p ∣ coeff m` for `1 <= m < p`,
   `coeff m (F * G) ≡ coeff m F + coeff m G [ZMOD p^2]` for all `1 <= m <= p`, and
   `coeff 0 (F * G) = 1`, `p ∣ coeff m (F * G)` for `1 <= m < p`.
   By induction, `a(p) ≡ ∑_{k=1..p} coeff p ((factorSeries k)^p) [ZMOD p^2]`.
3. For `1 < k < p`, every nonzero term of `factorSeries k` has degree divisible by `k`,
   so `coeff p ((factorSeries k)^p) = 0` since `p` is prime (`¬ k ∣ p`).
4. For `k = p`, `factorSeries p = 1 + 2 * X^p + O(X^(2p))`, so `coeff p ((factorSeries p)^p) = 2 * p`.
5. For `k = 1`, `factorSeries 1 * (1 - X) = 1 + X`, hence `(factorSeries 1)^p * (1 - X)^p = (1 + X)^p`.
   Extracting `coeff p` modulo `p^2`, all intermediate terms `1 <= j < p` vanish mod `p^2`
   (since `p ∣ coeff j ((factorSeries 1)^p)` and `p ∣ C(p, p - j)`), leaving
   `coeff p ((factorSeries 1)^p) + (-1)^p ≡ 1 [ZMOD p^2]`.
   - For odd prime `p >= 3`: `coeff p ((factorSeries 1)^p) ≡ 2 [ZMOD p^2]`, so
     `a(p) ≡ 2 + 2 * p [ZMOD p^2]`.
   - For `p = 2`: `coeff 2 ((factorSeries 1)^2) ≡ 0 [ZMOD 4]` and `coeff 2 ((factorSeries 2)^2) = 4`,
     so `a(2) ≡ 0 ≢ 6 [ZMOD 4]`.
-/

namespace OeisA270919Proof

open Finset OMA.S_oeis_a270919

private lemma coeff_pow_prime_zmod {p : ℕ} (hp : p.Prime) (F : PowerSeries (ZMod p))
    (m : ℕ) (hm : ¬ p ∣ m) :
    PowerSeries.coeff m (F ^ p) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  -- Prove by induction on m? Better: reduce to F truncated to Polynomial (ZMod p) of degree <= m!
  let P : Polynomial (ZMod p) := ∑ i ∈ Finset.range (m + 1), Polynomial.monomial i (PowerSeries.coeff i F)
  have htrunc : PowerSeries.coeff m (F ^ p) = PowerSeries.coeff m ((P : PowerSeries (ZMod p)) ^ p) := by
    have hdiff : ∀ k : ℕ, (G1 G2 : PowerSeries (ZMod p)) →
        (∀ j ≤ m, PowerSeries.coeff j G1 = PowerSeries.coeff j G2) →
        ∀ j ≤ m, PowerSeries.coeff j (G1 ^ k) = PowerSeries.coeff j (G2 ^ k) := by
      intro k
      induction k with
      | zero => intro G1 G2 _ j _; simp
      | succ k ih =>
        intro G1 G2 h j hj
        rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
        apply Finset.sum_congr rfl
        intro x hx
        have hx' : x.1 + x.2 = j := by simpa using hx
        rw [ih G1 G2 h x.1 (by omega), h x.2 (by omega)]
    apply hdiff p F (P : PowerSeries (ZMod p)) _ m (le_refl m)
    intro j hj
    rw [Polynomial.coeff_coe, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (Finset.range (m + 1)) j]
    simp [Finset.mem_range.mpr (by omega : j < m + 1)]
  rw [htrunc, ← Polynomial.coe_pow, Polynomial.coeff_coe]
  -- Over CharP (ZMod p) p, (∑ i, c_i X^i)^p = ∑ i, c_i^p X^(p*i)
  have hpoly : P ^ p = ∑ i ∈ Finset.range (m + 1), (Polynomial.monomial i (PowerSeries.coeff i F)) ^ p := by
    simp only [P]
    have hsum_pow : ∀ (s : Finset ℕ) (f : ℕ → Polynomial (ZMod p)),
        (∑ i ∈ s, f i) ^ p = ∑ i ∈ s, (f i) ^ p := by
      intro s f
      classical
      induction s using Finset.induction_on with
      | empty => simp [zero_pow hp.ne_zero]
      | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, add_pow_char, ih]
    exact hsum_pow _ _
  rw [hpoly, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i _
  rw [Polynomial.monomial_pow, Polynomial.coeff_monomial]
  have hne : i * p ≠ m := fun h => hm ⟨i, by linarith⟩
  simp [hne]

private lemma dvd_coeff_pow_prime {p : ℕ} (hp : p.Prime) (F : PowerSeries ℤ)
    (m : ℕ) (hm : ¬ p ∣ m) :
    (p : ℤ) ∣ PowerSeries.coeff m (F ^ p) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hmap : ((PowerSeries.coeff m (F ^ p) : ℤ) : ZMod p) =
      PowerSeries.coeff m ((PowerSeries.map (Int.castRingHom (ZMod p)) F) ^ p) := by
    rw [← map_pow, PowerSeries.coeff_map]
    rfl
  rw [hmap]
  exact coeff_pow_prime_zmod hp _ m hm

private lemma coeff_zero_factorSeries (k : ℕ) :
    PowerSeries.coeff 0 (factorSeries k) = 1 := by
  simp [factorSeries]

private lemma coeff_factorSeries_of_not_dvd {k m : ℕ} (_hk : 1 ≤ k) (hnd : ¬ k ∣ m) :
    PowerSeries.coeff m (factorSeries k) = 0 := by
  have hm0 : m ≠ 0 := by
    intro h0; subst h0; exact hnd (dvd_zero k)
  simp [factorSeries, hm0, hnd]

private lemma coeff_pow_factorSeries_of_not_dvd {k : ℕ} (hk : 1 ≤ k) :
    ∀ e m : ℕ, ¬ k ∣ m → PowerSeries.coeff m ((factorSeries k) ^ e) = 0 := by
  intro e
  induction e with
  | zero =>
    intro m hnd
    have hm0 : m ≠ 0 := fun h => hnd (h ▸ dvd_zero k)
    simp [PowerSeries.coeff_one, hm0]
  | succ e ih =>
    intro m hnd
    rw [pow_succ, PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro x hx
    have hx' : x.1 + x.2 = m := by simpa using hx
    by_cases h1 : k ∣ x.1
    · have h2 : ¬ k ∣ x.2 := fun h2 => hnd (hx' ▸ dvd_add h1 h2)
      rw [coeff_factorSeries_of_not_dvd hk h2, mul_zero]
    · rw [ih x.1 h1, zero_mul]

private lemma coeff_mul_mod_sq {p : ℕ} (F G : PowerSeries ℤ)
    (hF0 : PowerSeries.coeff 0 F = 1) (hG0 : PowerSeries.coeff 0 G = 1)
    (hF : ∀ m : ℕ, 1 ≤ m → m < p → (p : ℤ) ∣ PowerSeries.coeff m F)
    (hG : ∀ m : ℕ, 1 ≤ m → m < p → (p : ℤ) ∣ PowerSeries.coeff m G)
    (m : ℕ) (hm1 : 1 ≤ m) (hmp : m ≤ p) :
    PowerSeries.coeff m (F * G) ≡ PowerSeries.coeff m F + PowerSeries.coeff m G [ZMOD ((p ^ 2 : ℕ) : ℤ)] := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hm_eq : m = (m - 1) + 1 := by omega
  rw [Finset.sum_range_succ]
  conv_lhs => rw [hm_eq, Finset.sum_range_succ']
  simp only [Nat.sub_self, Nat.sub_zero, hF0, hG0, mul_one, one_mul, ← hm_eq]
  rw [Int.modEq_iff_dvd]
  have hmid : ((p ^ 2 : ℕ) : ℤ) ∣
      ∑ k ∈ Finset.range (m - 1), PowerSeries.coeff (k + 1) F * PowerSeries.coeff (m - (k + 1)) G := by
    apply Finset.dvd_sum
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨q1, hq1⟩ := hF (k + 1) (by omega) (by omega)
    obtain ⟨q2, hq2⟩ := hG (m - (k + 1)) (by omega) (by omega)
    refine ⟨q1 * q2, ?_⟩
    rw [hq1, hq2]; push_cast; ring
  have heq : PowerSeries.coeff m F + PowerSeries.coeff m G -
      ((∑ k ∈ Finset.range (m - 1), PowerSeries.coeff (k + 1) F * PowerSeries.coeff (m - (k + 1)) G) +
        PowerSeries.coeff m G + PowerSeries.coeff m F) =
      -(∑ k ∈ Finset.range (m - 1), PowerSeries.coeff (k + 1) F * PowerSeries.coeff (m - (k + 1)) G) := by
    ring
  rw [heq]
  exact dvd_neg.mpr hmid

private lemma coeff_prod_mod_sq {p : ℕ} (hp : p.Prime) (S : Finset ℕ)
    (F : ℕ → PowerSeries ℤ)
    (h0 : ∀ k ∈ S, PowerSeries.coeff 0 (F k) = 1)
    (hdvd : ∀ k ∈ S, ∀ m : ℕ, 1 ≤ m → m < p → (p : ℤ) ∣ PowerSeries.coeff m (F k)) :
    PowerSeries.coeff 0 (∏ k ∈ S, F k) = 1 ∧
    (∀ m : ℕ, 1 ≤ m → m < p → (p : ℤ) ∣ PowerSeries.coeff m (∏ k ∈ S, F k)) ∧
    PowerSeries.coeff p (∏ k ∈ S, F k) ≡ ∑ k ∈ S, PowerSeries.coeff p (F k) [ZMOD ((p ^ 2 : ℕ) : ℤ)] := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨by simp, ?_, ?_⟩
    · intro m hm _; simp [PowerSeries.coeff_one, show m ≠ 0 by omega]
    · simp [PowerSeries.coeff_one, hp.ne_zero]
  | @insert a S ha ih =>
    have h0S : ∀ k ∈ S, PowerSeries.coeff 0 (F k) = 1 := fun k hk => h0 k (Finset.mem_insert_of_mem hk)
    have hdvdS : ∀ k ∈ S, ∀ m : ℕ, 1 ≤ m → m < p → (p : ℤ) ∣ PowerSeries.coeff m (F k) :=
      fun k hk => hdvd k (Finset.mem_insert_of_mem hk)
    obtain ⟨ih0, ihd, ihp⟩ := ih h0S hdvdS
    have h0a := h0 a (Finset.mem_insert_self a S)
    have hdva := hdvd a (Finset.mem_insert_self a S)
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    refine ⟨?_, ?_, ?_⟩
    · rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff,
        h0a, ih0, mul_one]
    · intro m hm1 hmp
      have hmod := coeff_mul_mod_sq (F a) (∏ k ∈ S, F k) h0a ih0 hdva ihd m hm1 (by omega)
      have hp_dvd_sq : (p : ℤ) ∣ ((p ^ 2 : ℕ) : ℤ) := by push_cast; exact dvd_pow_self _ (by norm_num)
      have hmodp := hmod.of_dvd hp_dvd_sq
      have hsum : (p : ℤ) ∣ PowerSeries.coeff m (F a) + PowerSeries.coeff m (∏ k ∈ S, F k) :=
        dvd_add (hdva m hm1 hmp) (ihd m hm1 hmp)
      exact (Int.modEq_zero_iff_dvd.mp (hmodp.trans (Int.modEq_zero_iff_dvd.mpr hsum)))
    · have hmod := coeff_mul_mod_sq (F a) (∏ k ∈ S, F k) h0a ih0 hdva ihd p hp.one_le (le_refl p)
      exact hmod.trans (Int.ModEq.add_left _ ihp)

private lemma factorSeries_one_mul :
    factorSeries 1 * (1 - PowerSeries.X) = 1 + PowerSeries.X := by
  ext m
  cases m with
  | zero =>
    simp [factorSeries, PowerSeries.coeff_zero_eq_constantCoeff]
  | succ m =>
    rw [mul_sub, mul_one, map_sub, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X]
    have hmulX : PowerSeries.coeff (m + 1) (factorSeries 1 * PowerSeries.X) =
        PowerSeries.coeff m (factorSeries 1) := by
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      rw [Finset.sum_eq_single m]
      · simp [PowerSeries.coeff_X]
      · intro i _ hne
        have hne1 : m + 1 - i ≠ 1 := by omega
        simp [PowerSeries.coeff_X, hne1]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    rw [hmulX]
    cases m with
    | zero => simp [factorSeries]
    | succ m => simp [factorSeries]

private lemma coeff_p_factorSeries_one_pow {p : ℕ} (hp : p.Prime) :
    PowerSeries.coeff p ((factorSeries 1) ^ p) + (-1 : ℤ) ^ p ≡ 1 [ZMOD ((p ^ 2 : ℕ) : ℤ)] := by
  have heq : (factorSeries 1) ^ p * (1 - PowerSeries.X) ^ p = (1 + PowerSeries.X) ^ p := by
    rw [← mul_pow, factorSeries_one_mul]
  have hcoeff := congrArg (PowerSeries.coeff p) heq
  have hRHS : PowerSeries.coeff p ((1 + PowerSeries.X : PowerSeries ℤ) ^ p) = 1 := by
    have hpoly : (1 + PowerSeries.X : PowerSeries ℤ) ^ p =
        (((Polynomial.X + 1 : Polynomial ℤ) ^ p : Polynomial ℤ) : PowerSeries ℤ) := by
      rw [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_one, add_comm]
    rw [hpoly, Polynomial.coeff_coe, add_pow, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single p]
    · simp [Polynomial.coeff_X_pow]
    · intro i _ hne; simp [Polynomial.coeff_X_pow, Ne.symm hne]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have h1sub : ∀ j : ℕ, j ≤ p →
      PowerSeries.coeff j ((1 - PowerSeries.X : PowerSeries ℤ) ^ p) =
        (-1 : ℤ) ^ j * (Nat.choose p j : ℤ) := by
    intro j hj
    have hpoly : (1 - PowerSeries.X : PowerSeries ℤ) ^ p =
        ((((-Polynomial.X + 1 : Polynomial ℤ) ^ p : Polynomial ℤ) : PowerSeries ℤ)) := by
      rw [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_neg, Polynomial.coe_X,
        Polynomial.coe_one, sub_eq_add_neg, add_comm]
    rw [hpoly, Polynomial.coeff_coe, add_pow, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single j]
    · rw [neg_eq_neg_one_mul, mul_pow, one_pow, mul_one]
      have hC : ((-1 : Polynomial ℤ) ^ j * Polynomial.X ^ j * (Nat.choose p j : Polynomial ℤ)) =
          Polynomial.C ((-1 : ℤ) ^ j * (Nat.choose p j : ℤ)) * Polynomial.X ^ j := by
        simp only [map_mul, map_pow, map_neg, map_one, map_natCast]; ring
      rw [hC, Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro i _ hne
      rw [neg_eq_neg_one_mul, mul_pow, one_pow, mul_one]
      have hC : ((-1 : Polynomial ℤ) ^ i * Polynomial.X ^ i * (Nat.choose p i : Polynomial ℤ)) =
          Polynomial.C ((-1 : ℤ) ^ i * (Nat.choose p i : ℤ)) * Polynomial.X ^ i := by
        simp only [map_mul, map_pow, map_neg, map_one, map_natCast]; ring
      rw [hC, Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hne)]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hF0 : PowerSeries.coeff 0 ((factorSeries 1) ^ p) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff,
      coeff_zero_factorSeries, one_pow]
  have hG0 : PowerSeries.coeff 0 ((1 - PowerSeries.X : PowerSeries ℤ) ^ p) = 1 := by
    rw [h1sub 0 (Nat.zero_le p)]; simp
  have hFp : ∀ m : ℕ, 1 ≤ m → m < p → (p : ℤ) ∣ PowerSeries.coeff m ((factorSeries 1) ^ p) := by
    intro m hm1 hmp
    apply dvd_coeff_pow_prime hp
    intro hd; have := Nat.le_of_dvd (by omega) hd; omega
  have hGp : ∀ m : ℕ, 1 ≤ m → m < p → (p : ℤ) ∣ PowerSeries.coeff m ((1 - PowerSeries.X : PowerSeries ℤ) ^ p) := by
    intro m hm1 hmp
    rw [h1sub m (by omega)]
    have hd : (p : ℤ) ∣ (Nat.choose p m : ℤ) := by
      exact_mod_cast hp.dvd_choose_self (by omega) hmp
    exact dvd_mul_of_dvd_right hd _
  have hmod := coeff_mul_mod_sq ((factorSeries 1) ^ p) ((1 - PowerSeries.X) ^ p) hF0 hG0 hFp hGp p hp.one_le (le_refl p)
  rw [hcoeff, hRHS, h1sub p (le_refl p), Nat.choose_self, Nat.cast_one, mul_one] at hmod
  exact hmod.symm

private lemma coeff_p_factorSeries_p_pow {p : ℕ} (hp : p.Prime) :
    PowerSeries.coeff p ((factorSeries p) ^ p) = 2 * (p : ℤ) := by
  -- Prove for all e : ℕ, coeff p ((factorSeries p) ^ e) = 2 * e
  have hall : ∀ e : ℕ, PowerSeries.coeff p ((factorSeries p) ^ e) = 2 * (e : ℤ) := by
    intro e
    induction e with
    | zero => simp [PowerSeries.coeff_one, hp.ne_zero]
    | succ e ih =>
      rw [pow_succ, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      have hp_eq : p = (p - 1) + 1 := by have := hp.two_le; omega
      rw [Finset.sum_range_succ]
      conv_lhs => rw [hp_eq, Finset.sum_range_succ']
      simp only [Nat.sub_self, Nat.sub_zero, ← hp_eq]
      have hmid : ∑ k ∈ Finset.range (p - 1),
          PowerSeries.coeff (k + 1) ((factorSeries p) ^ e) *
            PowerSeries.coeff (p - (k + 1)) (factorSeries p) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finset.mem_range] at hk
        have hnd : ¬ p ∣ p - (k + 1) := by
          intro hd; have := Nat.le_of_dvd (by omega) hd; omega
        rw [coeff_factorSeries_of_not_dvd hp.one_le hnd, mul_zero]
      have h0e : PowerSeries.coeff 0 ((factorSeries p) ^ e) = 1 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
          ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_zero_factorSeries, one_pow]
      have hfp : PowerSeries.coeff p (factorSeries p) = 2 := by
        simp [factorSeries, hp.ne_zero]
      rw [hmid, zero_add, h0e, one_mul, hfp, coeff_zero_factorSeries, mul_one, ih]
      push_cast; ring
  exact hall p

end OeisA270919Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a270919.main := by
  have hmain : ∀ p : ℕ, p.Prime →
      OMA.S_oeis_a270919.a p ≡ 2 * (p : ℤ) + (1 - (-1 : ℤ) ^ p) [ZMOD ((p ^ 2 : ℕ) : ℤ)] := by
    intro p hp
    unfold OMA.S_oeis_a270919.a
    have hprod := OeisA270919Proof.coeff_prod_mod_sq hp (Finset.Icc 1 p)
      (fun k => (OMA.S_oeis_a270919.factorSeries k) ^ p)
      (fun k _ => by
        rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
          ← PowerSeries.coeff_zero_eq_constantCoeff, OeisA270919Proof.coeff_zero_factorSeries, one_pow])
      (fun k _ m hm1 hmp => OeisA270919Proof.dvd_coeff_pow_prime hp _ m (fun hd => by
        have := Nat.le_of_dvd (by omega) hd; omega))
    have hsum : ∑ k ∈ Finset.Icc 1 p, PowerSeries.coeff p ((OMA.S_oeis_a270919.factorSeries k) ^ p) =
        PowerSeries.coeff p ((OMA.S_oeis_a270919.factorSeries 1) ^ p) +
        PowerSeries.coeff p ((OMA.S_oeis_a270919.factorSeries p) ^ p) := by
      have h1p : (1 : ℕ) ≠ p := hp.ne_one.symm
      have hsub : ({1, p} : Finset ℕ) ⊆ Finset.Icc 1 p := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp [hp.one_le]
      have hsplit : Finset.Icc 1 p = {1, p} ∪ (Finset.Icc 1 p \ {1, p}) := by
        ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
      rw [hsplit, Finset.sum_union disjoint_sdiff_self_right]
      have hrest : ∑ k ∈ Finset.Icc 1 p \ {1, p},
          PowerSeries.coeff p ((OMA.S_oeis_a270919.factorSeries k) ^ p) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton,
          not_or] at hk
        apply OeisA270919Proof.coeff_pow_factorSeries_of_not_dvd hk.1.1 p p
        intro hd
        rcases (Nat.dvd_prime hp).mp hd with h1 | hp'
        · exact hk.2.1 h1
        · exact hk.2.2 hp'
      rw [hrest, add_zero, Finset.sum_pair h1p]
    have h1 := OeisA270919Proof.coeff_p_factorSeries_one_pow hp
    have h1' : PowerSeries.coeff p ((OMA.S_oeis_a270919.factorSeries 1) ^ p) ≡
        1 - (-1 : ℤ) ^ p [ZMOD ((p ^ 2 : ℕ) : ℤ)] := by
      have := h1.sub_right ((-1 : ℤ) ^ p)
      simpa using this
    have hp_term := OeisA270919Proof.coeff_p_factorSeries_p_pow hp
    have hcomb := hprod.2.2
    rw [hsum, hp_term] at hcomb
    exact hcomb.trans ((h1'.add_right (2 * (p : ℤ))).trans (by rw [add_comm]))
  constructor
  · intro p hp hp3
    have h := hmain p hp
    have hodd : p % 2 = 1 := by have := hp.eq_two_or_odd; omega
    have hneg : (-1 : ℤ) ^ p = -1 := by
      have : p = 2 * (p / 2) + 1 := by omega
      rw [this, pow_succ, pow_mul]; norm_num
    rw [hneg] at h
    simpa using h
  · intro h2
    have h := hmain 2 Nat.prime_two
    have h4 : (2 * ((2 : ℕ) : ℤ) + (1 - (-1 : ℤ) ^ 2)) = 4 := by norm_num
    rw [h4] at h
    have hcontra := h.symm.trans h2
    revert hcontra
    decide
