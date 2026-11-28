import OMAStatements.S_oeis_a079144
import Mathlib

/-!
# Proof of OEIS A079144 Conjectures

By iterated finite differences `(Δ_j P)(y) = P(y) - P(y - j)` on `y^n`:
1. `(m! : ℤ) ∣ w m n` for all `m, n`, and `w m n = 0` for all `m > n`.
2. Modulo any `M >= 1`, all `m >= M` terms vanish (`M ∣ m! ∣ w m n`), so
   `a(n) ≡ ∑_{m < M} w m n (mod M)`, a fixed integer combination of `(-c)^n`.
3. Claim 1 (`phi(k)` eventual periodicity) follows from `(-c)^(n + phi(k)) ≡ (-c)^n [ZMOD k]` for `n >= k`.
4. Claim 2 (shifted Gauss congruences) follows from `(-c)^(n*p^r + i) ≡ (-c)^(n*p^(r-1) + i) [ZMOD p^r]`.
-/

namespace OeisA079144Proof

open Finset Polynomial

private noncomputable def diffQuo (P : Polynomial ℤ) (c : ℤ) : Polynomial ℤ :=
  ∑ k ∈ P.support, Polynomial.C (P.coeff k) *
    ∑ r ∈ Finset.range k, Polynomial.X ^ r * (Polynomial.X - Polynomial.C c) ^ (k - 1 - r)

private lemma eval_diffQuo (P : Polynomial ℤ) (c y : ℤ) :
    P.eval y - P.eval (y - c) = c * (diffQuo P c).eval y := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum, Polynomial.sum_def, Polynomial.sum_def]
  rw [← Finset.sum_sub_distrib]
  unfold diffQuo
  rw [Polynomial.eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
             Polynomial.eval_X, Polynomial.eval_C]
  have hgeom : (y - (y - c)) * ∑ r ∈ Finset.range k, y ^ r * (y - c) ^ (k - 1 - r) =
      y ^ k - (y - c) ^ k := by
    have h := geom_sum₂_mul y (y - c) k
    linarith
  have hc : y - (y - c) = c := by ring
  rw [hc] at hgeom
  calc P.coeff k * y ^ k - P.coeff k * (y - c) ^ k
      = P.coeff k * (y ^ k - (y - c) ^ k) := by ring
    _ = P.coeff k * (c * ∑ r ∈ Finset.range k, y ^ r * (y - c) ^ (k - 1 - r)) := by rw [← hgeom]
    _ = c * (P.coeff k * ∑ r ∈ Finset.range k, y ^ r * (y - c) ^ (k - 1 - r)) := by ring

private lemma diffQuo_eq_zero_of_deg_zero (P : Polynomial ℤ) (c : ℤ) (h : P.degree ≤ (0 : ℕ)) :
    diffQuo P c = 0 := by
  unfold diffQuo
  apply Finset.sum_eq_zero
  intro k hk
  have hkle : (k : WithBot ℕ) ≤ P.degree := Polynomial.le_degree_of_ne_zero (Polynomial.mem_support_iff.mp hk)
  have hk0 : k = 0 := by
    have := le_trans hkle h
    exact Nat.le_zero.mp (WithBot.coe_le_coe.mp this)
  subst hk0
  simp

private lemma diffQuo_degree_le (P : Polynomial ℤ) (c : ℤ) (d : ℕ) (h : P.degree ≤ ((d + 1 : ℕ) : WithBot ℕ)) :
    (diffQuo P c).degree ≤ (d : WithBot ℕ) := by
  unfold diffQuo
  apply le_trans (Polynomial.degree_sum_le _ _)
  apply Finset.sup_le
  intro k hk
  have hkle : k ≤ d + 1 := by
    have h1 := Polynomial.le_degree_of_ne_zero (Polynomial.mem_support_iff.mp hk)
    exact WithBot.coe_le_coe.mp (le_trans h1 h)
  have hdegC : (Polynomial.C (P.coeff k)).degree ≤ 0 := Polynomial.degree_C_le
  have hdegS : (∑ r ∈ Finset.range k, Polynomial.X ^ r * (Polynomial.X - Polynomial.C c) ^ (k - 1 - r)).degree ≤
      (d : WithBot ℕ) := by
    apply le_trans (Polynomial.degree_sum_le _ _)
    apply Finset.sup_le
    intro r hr
    have hrk : r < k := Finset.mem_range.mp hr
    have hd1 : (Polynomial.X ^ r : Polynomial ℤ).degree ≤ (r : WithBot ℕ) := Polynomial.degree_X_pow_le r
    have hd2 : ((Polynomial.X - Polynomial.C c) ^ (k - 1 - r) : Polynomial ℤ).degree ≤
        ((k - 1 - r : ℕ) : WithBot ℕ) := by
      have hlin : (Polynomial.X - Polynomial.C c : Polynomial ℤ).degree ≤ (1 : WithBot ℕ) :=
        le_trans (Polynomial.degree_sub_le _ _)
          (max_le Polynomial.degree_X_le (le_trans Polynomial.degree_C_le (by decide)))
      calc ((Polynomial.X - Polynomial.C c) ^ (k - 1 - r) : Polynomial ℤ).degree
          ≤ (k - 1 - r) • (Polynomial.X - Polynomial.C c : Polynomial ℤ).degree := Polynomial.degree_pow_le _ _
        _ ≤ (k - 1 - r) • (1 : WithBot ℕ) := nsmul_le_nsmul_right hlin _
        _ = ((k - 1 - r : ℕ) : WithBot ℕ) := by simp
    have hmul := le_trans (Polynomial.degree_mul_le _ _) (add_le_add hd1 hd2)
    have hsum : (r : WithBot ℕ) + ((k - 1 - r : ℕ) : WithBot ℕ) ≤ (d : WithBot ℕ) := by
      rw [← Nat.cast_add]
      exact Nat.cast_le.mpr (by omega)
    exact le_trans hmul hsum
  have hmul := le_trans (Polynomial.degree_mul_le _ _) (add_le_add hdegC hdegS)
  rwa [zero_add] at hmul

private lemma diff_poly_exists (n : ℕ) :
    ∀ m : ℕ, ∃ Q : Polynomial ℤ,
      (∀ y : ℤ, ∑ S ∈ (Finset.Icc 1 m).powerset,
          (-1 : ℤ) ^ S.card * (y - ∑ j ∈ S, (j : ℤ)) ^ n =
        (m.factorial : ℤ) * Q.eval y) ∧
      (m ≤ n → Q.degree ≤ ((n - m : ℕ) : WithBot ℕ)) ∧
      (n < m → Q = 0) := by
  intro m
  induction m with
  | zero =>
    refine ⟨Polynomial.X ^ n, ?_, ?_, fun h => by omega⟩
    · intro y; simp
    · intro _; simp
  | succ m ih =>
    rcases ih with ⟨Q, hQ_eval, hQ_deg, hQ_zero⟩
    refine ⟨diffQuo Q (m + 1 : ℤ), ?_, ?_, ?_⟩
    · intro y
      have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnotmem : m + 1 ∉ Finset.Icc 1 m := by simp
      rw [hIcc, Finset.powerset_insert]
      have hdisj : Disjoint (Finset.Icc 1 m).powerset
          ((Finset.Icc 1 m).powerset.image (insert (m + 1))) := by
        rw [Finset.disjoint_left]
        intro S hS1 hS2
        rw [Finset.mem_image] at hS2
        rcases hS2 with ⟨T, _, rfl⟩
        have := Finset.mem_powerset.mp hS1 (Finset.mem_insert_self (m + 1) T)
        exact hnotmem this
      rw [Finset.sum_union hdisj]
      have himg : ∑ S ∈ (Finset.Icc 1 m).powerset.image (insert (m + 1)),
            (-1 : ℤ) ^ S.card * (y - ∑ j ∈ S, (j : ℤ)) ^ n =
          -∑ T ∈ (Finset.Icc 1 m).powerset,
            (-1 : ℤ) ^ T.card * ((y - (m + 1 : ℤ)) - ∑ j ∈ T, (j : ℤ)) ^ n := by
        rw [Finset.sum_image]
        · rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro T hT
          have hTnot : m + 1 ∉ T := fun h => hnotmem (Finset.mem_powerset.mp hT h)
          rw [Finset.card_insert_of_notMem hTnot, Finset.sum_insert hTnot, pow_succ]
          push_cast
          ring
        · intro T1 hT1 T2 hT2 heq
          have h1 : m + 1 ∉ T1 := fun h => hnotmem (Finset.mem_powerset.mp hT1 h)
          have h2 : m + 1 ∉ T2 := fun h => hnotmem (Finset.mem_powerset.mp hT2 h)
          have := congrArg (fun S => S.erase (m + 1)) heq
          simpa [Finset.erase_insert h1, Finset.erase_insert h2] using this
      rw [himg, hQ_eval y, hQ_eval (y - (m + 1 : ℤ))]
      have hdiff := eval_diffQuo Q (m + 1 : ℤ) y
      rw [Nat.factorial_succ]
      push_cast
      linear_combination (m.factorial : ℤ) * hdiff
    · intro hle
      have h1 : Q.degree ≤ (((n - (m + 1)) + 1 : ℕ) : WithBot ℕ) := by
        have := hQ_deg (by omega)
        rwa [show n - m = (n - (m + 1)) + 1 by omega] at this
      exact diffQuo_degree_le Q (m + 1 : ℤ) (n - (m + 1)) h1
    · intro hgt
      by_cases hnm : m = n
      · subst hnm
        have h0 : Q.degree ≤ (0 : ℕ) := by simpa using hQ_deg le_rfl
        exact diffQuo_eq_zero_of_deg_zero Q (m + 1 : ℤ) h0
      · have h0 : Q = 0 := hQ_zero (by omega)
        rw [h0]; simp [diffQuo]

private lemma fact_dvd_w (m n : ℕ) : (m.factorial : ℤ) ∣ OMA.S_oeis_a079144.w m n := by
  obtain ⟨Q, hQ_eval, _, _⟩ := diff_poly_exists n m
  refine ⟨Q.eval 0, ?_⟩
  have h0 := hQ_eval 0
  simp only [zero_sub] at h0
  exact h0

private lemma w_eq_zero_of_gt {m n : ℕ} (h : n < m) : OMA.S_oeis_a079144.w m n = 0 := by
  obtain ⟨Q, hQ_eval, _, hQ_zero⟩ := diff_poly_exists n m
  have h0 := hQ_eval 0
  simp only [zero_sub] at h0
  rw [hQ_zero h, Polynomial.eval_zero, mul_zero] at h0
  exact h0

private lemma a_eq_sum_mod (M n : ℕ) (hM : 1 ≤ M) :
    OMA.S_oeis_a079144.a n ≡ ∑ m ∈ Finset.range M, OMA.S_oeis_a079144.w m n [ZMOD M] := by
  rw [← ZMod.intCast_eq_intCast_iff]
  unfold OMA.S_oeis_a079144.a
  push_cast
  by_cases h : n + 1 ≤ M
  · have hsplit : Finset.range M = Finset.range (n + 1) ∪ (Finset.range M \ Finset.range (n + 1)) := by
      ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_range]; omega
    rw [hsplit, Finset.sum_union disjoint_sdiff_self_right]
    have htail : ∑ m ∈ Finset.range M \ Finset.range (n + 1), (OMA.S_oeis_a079144.w m n : ZMod M) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      simp only [Finset.mem_sdiff, Finset.mem_range] at hm
      rw [w_eq_zero_of_gt (by omega), Int.cast_zero]
    rw [htail, add_zero]
  · have hsplit : Finset.range (n + 1) = Finset.range M ∪ (Finset.range (n + 1) \ Finset.range M) := by
      ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_range]; omega
    rw [hsplit, Finset.sum_union disjoint_sdiff_self_right]
    have htail : ∑ m ∈ Finset.range (n + 1) \ Finset.range M, (OMA.S_oeis_a079144.w m n : ZMod M) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      simp only [Finset.mem_sdiff, Finset.mem_range] at hm
      have hdvd : (M : ℤ) ∣ OMA.S_oeis_a079144.w m n :=
        dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.dvd_factorial hM (by omega))) (fact_dvd_w m n)
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr hdvd
    rw [htail, add_zero]

private lemma pow_add_totient_modEq (r : ℕ) :
    ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, k ≤ n → r ^ (n + Nat.totient k) ≡ r ^ n [MOD k] := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk n hn
    by_cases hk1 : k = 1
    · subst hk1; exact Nat.modEq_one
    · set p := k.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      set e := k.factorization p
      have he_pos : 1 ≤ e :=
        (Nat.Prime.dvd_iff_one_le_factorization hp (by omega)).mp (Nat.minFac_dvd k)
      set q := p ^ e
      have hq_dvd : q ∣ k := Nat.ordProj_dvd k p
      set m := k / q
      have hqm : q * m = k := Nat.mul_div_cancel' hq_dvd
      have hcop : Nat.Coprime q m := by
        have hpm : ¬ p ∣ m := by
          intro hpm
          have hpow1 : p ^ (e + 1) ∣ k := by
            rcases hpm with ⟨t, ht⟩
            refine ⟨t, ?_⟩
            calc k = p ^ e * m := hqm.symm
              _ = p ^ e * (p * t) := by rw [ht]
              _ = p ^ (e + 1) * t := by rw [pow_succ]; ring
          have hle := (Nat.Prime.pow_dvd_iff_le_factorization hp (by omega)).mp hpow1
          omega
        exact (hp.coprime_iff_not_dvd.mpr hpm).pow_left e
      have hm_pos : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · rw [h0, mul_zero] at hqm; omega
        · exact hpos
      have hm_lt : m < k := by
        have hq_gt1 : 1 < q := one_lt_pow₀ hp.one_lt (by omega)
        nlinarith
      suffices h : r ^ (n + Nat.totient k) ≡ r ^ n [MOD q * m] by rwa [hqm] at h
      rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
      constructor
      · by_cases hpr : p ∣ r
        · have he_le : e ≤ n := by
            have h1 : e < p ^ e := Nat.lt_pow_self hp.one_lt
            have h2 : q ≤ k := Nat.le_of_dvd (by omega) hq_dvd
            omega
          have hd1 : q ∣ r ^ n := by
            rcases hpr with ⟨t, rfl⟩
            rw [mul_pow]
            exact dvd_mul_of_dvd_left (pow_dvd_pow p he_le) _
          have hd2 : q ∣ r ^ (n + Nat.totient k) :=
            dvd_trans hd1 (pow_dvd_pow r (Nat.le_add_right n _))
          rw [Nat.ModEq, Nat.mod_eq_zero_of_dvd hd1, Nat.mod_eq_zero_of_dvd hd2]
        · have hcop_rq : Nat.Coprime r q := (hp.coprime_iff_not_dvd.mpr hpr).symm.pow_right e
          have heuler : r ^ Nat.totient q ≡ 1 [MOD q] := Nat.ModEq.pow_totient hcop_rq
          have htdvd : Nat.totient q ∣ Nat.totient k := Nat.totient_dvd_of_dvd hq_dvd
          rcases htdvd with ⟨t, ht⟩
          have hphi : r ^ Nat.totient k ≡ 1 [MOD q] := by
            rw [ht, pow_mul]
            simpa using heuler.pow t
          rw [pow_add]
          simpa using (Nat.ModEq.refl (r ^ n)).mul hphi
      · have hm_dvd : m ∣ k := ⟨q, by linarith⟩
        have htdvd : Nat.totient m ∣ Nat.totient k := Nat.totient_dvd_of_dvd hm_dvd
        rcases htdvd with ⟨t, ht⟩
        rw [ht]
        have hiter : ∀ s : ℕ, r ^ (n + Nat.totient m * s) ≡ r ^ n [MOD m] := by
          intro s
          induction s with
          | zero => simp [Nat.ModEq]
          | succ s ihs =>
            have hstep : r ^ (n + Nat.totient m * s + Nat.totient m) ≡
                r ^ (n + Nat.totient m * s) [MOD m] :=
              ih m hm_lt hm_pos (n + Nat.totient m * s) (by omega)
            rw [show n + Nat.totient m * (s + 1) = n + Nat.totient m * s + Nat.totient m by ring]
            exact hstep.trans ihs
        exact hiter t

private lemma neg_one_pow_totient_zmod (k : ℕ) (hk : 1 ≤ k) :
    ((-1 : ZMod k) ^ Nat.totient k) = 1 := by
  by_cases hk1 : k = 1
  · subst hk1; exact Subsingleton.elim _ _
  · by_cases hk2 : k = 2
    · subst hk2; decide
    · have heven : Even (Nat.totient k) := Nat.totient_even (by omega)
      rcases heven with ⟨t, ht⟩
      rw [ht, ← two_mul, pow_mul]
      norm_num

private lemma int_pow_gauss_zmod (c : ℤ) (i p n r : ℕ) (hp : p.Prime) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    (c : ZMod (p ^ r)) ^ (n * p ^ r + i) = (c : ZMod (p ^ r)) ^ (n * p ^ (r - 1) + i) := by
  rw [pow_add, pow_add]
  congr 1
  by_cases hpc : (p : ℤ) ∣ c
  · have hge : r ≤ n * p ^ (r - 1) := by
      have h1 : r ≤ 2 ^ (r - 1) := by
        cases r with
        | zero => omega
        | succ r' =>
          rw [Nat.add_sub_cancel]
          have := Nat.lt_two_pow_self (n := r')
          omega
      have h2 : 2 ^ (r - 1) ≤ p ^ (r - 1) := Nat.pow_le_pow_left hp.two_le (r - 1)
      nlinarith
    have hle : n * p ^ (r - 1) ≤ n * p ^ r :=
      Nat.mul_le_mul_left n (Nat.pow_le_pow_right hp.pos (by omega))
    have hd1 : ((p ^ r : ℕ) : ℤ) ∣ c ^ (n * p ^ (r - 1)) := by
      rcases hpc with ⟨t, rfl⟩
      rw [mul_pow, Nat.cast_pow]
      exact dvd_mul_of_dvd_left (pow_dvd_pow (p : ℤ) hge) _
    have hd2 : ((p ^ r : ℕ) : ℤ) ∣ c ^ (n * p ^ r) :=
      dvd_trans hd1 (pow_dvd_pow c hle)
    have hz1 : (c : ZMod (p ^ r)) ^ (n * p ^ (r - 1)) = 0 := by
      rw [← Int.cast_pow]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd1
    have hz2 : (c : ZMod (p ^ r)) ^ (n * p ^ r) = 0 := by
      rw [← Int.cast_pow]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd2
    rw [hz1, hz2]
  · have hcop_nat : Nat.Coprime c.natAbs (p ^ r) := by
      have hndvd : ¬ p ∣ c.natAbs := fun h => hpc (Int.natCast_dvd.mpr h)
      exact (hp.coprime_iff_not_dvd.mpr hndvd).symm.pow_right r
    have heuler_nat : c.natAbs ^ Nat.totient (p ^ r) ≡ 1 [MOD p ^ r] :=
      Nat.ModEq.pow_totient hcop_nat
    have hphi_eq : Nat.totient (p ^ r) = p ^ (r - 1) * (p - 1) := Nat.totient_prime_pow hp hr
    have hdiff : n * p ^ r = n * p ^ (r - 1) + n * Nat.totient (p ^ r) := by
      rw [hphi_eq]
      have hpow : p ^ r = p ^ (r - 1) * p := by
        have : r = (r - 1) + 1 := by omega
        conv_lhs => rw [this, pow_succ]
      have hp1 : p = 1 + (p - 1) := by have := hp.two_le; omega
      have h2 : p ^ (r - 1) * p = p ^ (r - 1) + p ^ (r - 1) * (p - 1) := by
        nth_rw 2 [hp1]; ring
      rw [hpow, h2]; ring
    rw [hdiff, pow_add]
    have hunit : (c : ZMod (p ^ r)) ^ (n * Nat.totient (p ^ r)) = 1 := by
      have hsign : (c : ZMod (p ^ r)) ^ Nat.totient (p ^ r) = 1 := by
        by_cases hc0 : 0 ≤ c
        · have heq : (c.natAbs : ℤ) = c := Int.natAbs_of_nonneg hc0
          rw [← heq, Int.cast_natCast, ← Nat.cast_pow]
          simpa using (ZMod.natCast_eq_natCast_iff _ _ (p ^ r)).mpr heuler_nat
        · have heq : -(c.natAbs : ℤ) = c := by omega
          rw [← heq, Int.cast_neg, Int.cast_natCast, neg_eq_neg_one_mul, mul_pow]
          have h1 : ((c.natAbs : ZMod (p ^ r)) ^ Nat.totient (p ^ r)) = 1 := by
            rw [← Nat.cast_pow]
            simpa using (ZMod.natCast_eq_natCast_iff _ _ (p ^ r)).mpr heuler_nat
          rw [h1, mul_one]
          exact neg_one_pow_totient_zmod (p ^ r) (Nat.one_le_pow r p hp.pos)
      rw [mul_comm, pow_mul, hsign, one_pow]
    rw [hunit, mul_one]

end OeisA079144Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a079144.main := by
  constructor
  · intro k hk
    refine ⟨k, fun n hn => ?_⟩
    have h1 := OeisA079144Proof.a_eq_sum_mod k (n + Nat.totient k) hk
    have h2 := OeisA079144Proof.a_eq_sum_mod k n hk
    refine h1.trans (Int.ModEq.trans ?_ h2.symm)
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    apply Finset.sum_congr rfl
    intro m _
    unfold OMA.S_oeis_a079144.w
    push_cast
    apply Finset.sum_congr rfl
    intro S _
    congr 1
    set c : ℕ := ∑ j ∈ S, j
    have hc_eq : (∑ j ∈ S, (j : ZMod k)) = (c : ZMod k) := by dsimp only [c]; push_cast; rfl
    rw [hc_eq, neg_eq_neg_one_mul, mul_pow, mul_pow]
    have hsign : (-1 : ZMod k) ^ (n + Nat.totient k) = (-1 : ZMod k) ^ n := by
      rw [pow_add, OeisA079144Proof.neg_one_pow_totient_zmod k hk, mul_one]
    have hpow : (c : ZMod k) ^ (n + Nat.totient k) = (c : ZMod k) ^ n := by
      simpa using (ZMod.natCast_eq_natCast_iff _ _ k).mpr
        (OeisA079144Proof.pow_add_totient_modEq c k hk n hn)
    rw [hsign, hpow]
  · intro i p n r hp hn hr
    have hM : 1 ≤ p ^ r := Nat.one_le_pow r p hp.pos
    have h1 := OeisA079144Proof.a_eq_sum_mod (p ^ r) (n * p ^ r + i) hM
    have h2 := OeisA079144Proof.a_eq_sum_mod (p ^ r) (n * p ^ (r - 1) + i) hM
    refine h1.trans (Int.ModEq.trans ?_ h2.symm)
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    apply Finset.sum_congr rfl
    intro m _
    unfold OMA.S_oeis_a079144.w
    push_cast
    apply Finset.sum_congr rfl
    intro S _
    congr 1
    have hc := OeisA079144Proof.int_pow_gauss_zmod (-(∑ j ∈ S, (j : ℤ))) i p n r hp hn hr
    push_cast at hc
    exact hc
