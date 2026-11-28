import OMAStatements.S_oeis_a355257
import Mathlib

/-!
# Proof of OEIS A355257 Conjectures

All four conjectures for `A(n, k) = Sum_{j=1..k} (k! / j) * (2^j - 1) * C(n + k - j - 1, k - j)`:
1. For `p` prime, `p ∣ (p! / j)` for `j < p`, and the `j = p` term is `(p-1)! * (2^p - 1) ≡ (-1) * 1 = -1 (mod p)`
   by Wilson's theorem and Fermat's Little Theorem.
2. For composite `k ≠ 4`, `k ∣ (k! / j)` for `j < k` and `k ∣ (k - 1)!` for `j = k`.
3. For each `k`, `A(n, k + 1)` is a polynomial in `n` of degree `<= k` (each `C(n + m - 1, m)` has degree `m <= k`),
   so by uniqueness of Lagrange interpolation (`Lagrange.eq_interpolate`) it equals the A355259 interpolating polynomial.
4. For `p` prime and `n` even, `(p - 1) ∣ A(n, p)`, and cancelling `p - 1` (coprime to `p`) from Claim 1 gives
   `A(n, p) / (p - 1) ≡ 1 [MOD p]`.
-/

namespace OeisA355257Proof

open Finset

private lemma dvd_fact_div_of_lt {k j : ℕ} (hj1 : 1 ≤ j) (hjk : j < k) :
    k ∣ k.factorial / j := by
  have hkm1 : j ≤ k - 1 := by omega
  have hjdvd : j ∣ (k - 1).factorial := Nat.dvd_factorial hj1 hkm1
  rcases hjdvd with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  have hk_eq : k = (k - 1) + 1 := by omega
  have hfact : k.factorial = k * (k - 1).factorial := by
    conv_lhs => rw [hk_eq, Nat.factorial_succ]
    rw [← hk_eq]
  rw [hfact, hq]
  have : k * (j * q) = (k * q) * j := by ring
  rw [this, Nat.mul_div_cancel _ (by omega)]

private lemma A_modEq_last (n k : ℕ) (hk : 1 ≤ k) :
    OMA.S_oeis_a355257.A n k ≡ (k - 1).factorial * (2 ^ k - 1) [MOD k] := by
  unfold OMA.S_oeis_a355257.A
  have hmem : k ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨hk, le_rfl⟩
  rw [← Finset.add_sum_erase _ _ hmem]
  have hlast : (k.factorial / k) * (2 ^ k - 1) * Nat.choose (n + k - k - 1) (k - k) =
      (k - 1).factorial * (2 ^ k - 1) := by
    have hk_eq : k = (k - 1) + 1 := by omega
    have hfk : k.factorial / k = (k - 1).factorial := by
      conv_lhs => rw [hk_eq, Nat.factorial_succ]
      rw [← hk_eq, Nat.mul_div_cancel_left _ (by omega)]
    rw [hfk, Nat.sub_self, Nat.choose_zero_right, mul_one]
  rw [hlast]
  have hdvd : k ∣ ∑ j ∈ (Finset.Icc 1 k).erase k,
      (k.factorial / j) * (2 ^ j - 1) * Nat.choose (n + k - j - 1) (k - j) := by
    apply Finset.dvd_sum
    intro j hj
    have hne : j ≠ k := (Finset.mem_erase.mp hj).1
    have hj_icc := Finset.mem_Icc.mp (Finset.mem_erase.mp hj).2
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_fact_div_of_lt hj_icc.1 (by omega)) _) _
  rcases hdvd with ⟨m, hm⟩
  rw [hm, Nat.ModEq, Nat.add_mul_mod_self_left]

private lemma claim1 (p n : ℕ) (hp : p.Prime) :
    OMA.S_oeis_a355257.A n p ≡ p - 1 [MOD p] := by
  have h1 := A_modEq_last n p hp.one_lt.le
  refine h1.trans ?_
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  have h2ge : 1 ≤ 2 ^ p := Nat.one_le_pow p 2 (by decide)
  have hp1 : 1 ≤ p := hp.one_lt.le
  rw [Nat.cast_mul, Nat.cast_sub h2ge, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
      Nat.cast_sub hp1, ZMod.natCast_self, zero_sub]
  rw [ZMod.wilsons_lemma p, ZMod.pow_card (2 : ZMod p)]
  ring

private lemma composite_dvd_pred_fact {k : ℕ} (hk2 : 2 ≤ k) (hnp : ¬ k.Prime) (hk4 : k ≠ 4) :
    k ∣ (k - 1).factorial := by
  have hex : ∃ a b : ℕ, 1 < a ∧ a ≤ b ∧ b < k ∧ a * b = k := by
    obtain ⟨a, ha_dvd, ha1, hak⟩ := Nat.exists_dvd_of_not_prime2 hk2 hnp
    rcases ha_dvd with ⟨b, hb⟩
    have hb1 : 1 < b := by nlinarith
    have hbk : b < k := by nlinarith
    by_cases hab : a ≤ b
    · exact ⟨a, b, ha1, hab, hbk, hb.symm⟩
    · exact ⟨b, a, hb1, by omega, hak, by linarith⟩
  rcases hex with ⟨a, b, ha1, hab, hbk, hmul⟩
  by_cases heq : a = b
  · subst heq
    have ha3 : 3 ≤ a := by
      by_contra hlt
      have ha2 : a = 2 := by omega
      subst ha2; omega
    have h2a_lt : 2 * a < a * a := by nlinarith
    have h2a_le : 2 * a ≤ k - 1 := by omega
    have h1 : a ∣ a.factorial := Nat.dvd_factorial (by omega) le_rfl
    have h2 : a.factorial * (2 * a) ∣ (2 * a).factorial := by
      have h2a_eq : 2 * a = (2 * a - 1) + 1 := by omega
      conv_rhs => rw [h2a_eq, Nat.factorial_succ]
      rw [← h2a_eq, mul_comm (2 * a)]
      exact mul_dvd_mul_right (Nat.factorial_dvd_factorial (by omega : a ≤ 2 * a - 1)) (2 * a)
    have h3 : a * a ∣ a.factorial * (2 * a) := by
      rcases h1 with ⟨q, hq⟩
      exact ⟨2 * q, by rw [hq]; ring⟩
    exact dvd_trans (by rw [← hmul]; exact h3)
      (dvd_trans h2 (Nat.factorial_dvd_factorial h2a_le))
  · have ha_lt_b : a < b := by omega
    have h1 : a ∣ (b - 1).factorial := Nat.dvd_factorial (by omega) (by omega)
    have h2 : a * b ∣ b.factorial := by
      have hb_eq : b = (b - 1) + 1 := by omega
      conv_rhs => rw [hb_eq, Nat.factorial_succ]
      rw [← hb_eq, mul_comm b]
      exact mul_dvd_mul_right h1 b
    exact dvd_trans (by rw [← hmul]; exact h2)
      (Nat.factorial_dvd_factorial (by omega : b ≤ k - 1))

private lemma claim2 (n k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≠ 4) :
    k ∣ OMA.S_oeis_a355257.A n k ↔ ¬ k.Prime := by
  constructor
  · intro hdvd hp
    have h0 : OMA.S_oeis_a355257.A n k % k = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have h1 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by have := hp.two_le; omega)
    have h2 : OMA.S_oeis_a355257.A n k % k = (k - 1) % k := claim1 k n hp
    have := hp.two_le
    omega
  · intro hnp
    by_cases hk_eq1 : k = 1
    · subst hk_eq1; exact one_dvd _
    · have hk2 : 2 ≤ k := by omega
      have hmod := A_modEq_last n k hk1
      have hdvd_last : k ∣ (k - 1).factorial * (2 ^ k - 1) :=
        dvd_mul_of_dvd_left (composite_dvd_pred_fact hk2 hnp hk4) _
      have h0 : ((k - 1).factorial * (2 ^ k - 1)) % k = 0 := Nat.mod_eq_zero_of_dvd hdvd_last
      exact Nat.dvd_of_mod_eq_zero (by rw [hmod, h0])

private lemma choose_add_sub_eq_prod (n m : ℕ) :
    (Nat.choose (n + m - 1) m : ℚ) * (m.factorial : ℚ) =
      ∏ i ∈ Finset.range m, ((n : ℚ) + (i : ℚ)) := by
  cases m with
  | zero => simp
  | succ m =>
    have hsub : n + (m + 1) - 1 = n + m := by omega
    rw [hsub]
    have hnat : Nat.choose (n + m) (m + 1) * (m + 1).factorial =
        ∏ i ∈ Finset.range (m + 1), (n + i) := by
      have hdesc := Nat.descFactorial_eq_factorial_mul_choose (n + m) (m + 1)
      rw [mul_comm] at hdesc
      rw [← hdesc]
      rw [Nat.descFactorial_eq_prod_range]
      cases n with
      | zero =>
        simp only [zero_add]
        have h1 : ∏ i ∈ Finset.range (m + 1), (m - i) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.lt_succ_self m))
          simp
        have h2 : ∏ i ∈ Finset.range (m + 1), i = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.succ_pos m))
          rfl
        rw [h1, h2]
      | succ n' =>
        refine Finset.prod_bij (fun i _ => m - i) ?_ ?_ ?_ ?_
        · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
        · intro i1 hi1 i2 hi2 h; simp only [Finset.mem_range] at hi1 hi2; omega
        · intro i hi; refine ⟨m - i, ?_, ?_⟩
          · simp only [Finset.mem_range] at hi ⊢; omega
          · simp only [Finset.mem_range] at hi; omega
        · intro i hi; simp only [Finset.mem_range] at hi; omega
    have hcast := congrArg (Nat.cast (R := ℚ)) hnat
    push_cast at hcast
    exact hcast

private lemma claim3 (k n : ℕ) :
    (Lagrange.interpolate (Finset.range (k + 1)) (Nat.cast (R := ℚ))
      (fun m => (OMA.S_oeis_a355257.A m (k + 1) : ℚ))).eval (n : ℚ) =
    (OMA.S_oeis_a355257.A n (k + 1) : ℚ) := by
  let P : Polynomial ℚ :=
    ∑ j ∈ Finset.Icc 1 (k + 1),
      Polynomial.C ((((k + 1).factorial / j) * (2 ^ j - 1) : ℕ) / ((k + 1 - j).factorial : ℚ)) *
        ∏ i ∈ Finset.range (k + 1 - j), (Polynomial.X + Polynomial.C (i : ℚ))
  have hP_eval : ∀ m : ℕ, P.eval (m : ℚ) = (OMA.S_oeis_a355257.A m (k + 1) : ℚ) := by
    intro m
    dsimp only [P]
    rw [Polynomial.eval_finsetSum]
    unfold OMA.S_oeis_a355257.A
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    have hprod := choose_add_sub_eq_prod m (k + 1 - j)
    have hsub : m + (k + 1) - j - 1 = m + (k + 1 - j) - 1 := by
      have := (Finset.mem_Icc.mp hj).2; omega
    rw [hsub, ← hprod]
    have hfac_ne : ((k + 1 - j).factorial : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp [hfac_ne]
  have hP_deg : P.degree < (Finset.range (k + 1)).card := by
    rw [Finset.card_range]
    have hle : P.degree ≤ (k : WithBot ℕ) := by
      apply le_trans (Polynomial.degree_sum_le _ _)
      apply Finset.sup_le
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hdeg1 : (Polynomial.C ((((k + 1).factorial / j) * (2 ^ j - 1) : ℕ) /
          ((k + 1 - j).factorial : ℚ))).degree ≤ 0 := Polynomial.degree_C_le
      have hdeg2 : (∏ i ∈ Finset.range (k + 1 - j), (Polynomial.X + Polynomial.C (i : ℚ))).degree ≤
          ((k + 1 - j : ℕ) : WithBot ℕ) := by
        calc (∏ i ∈ Finset.range (k + 1 - j), (Polynomial.X + Polynomial.C (i : ℚ))).degree
            ≤ ∑ i ∈ Finset.range (k + 1 - j), (Polynomial.X + Polynomial.C (i : ℚ)).degree :=
              Polynomial.degree_prod_le _ _
          _ ≤ ∑ _i ∈ Finset.range (k + 1 - j), (1 : WithBot ℕ) := by
              apply Finset.sum_le_sum
              intro i _
              exact le_trans (Polynomial.degree_add_le _ _) (max_le Polynomial.degree_X_le
                (le_trans Polynomial.degree_C_le (by decide)))
          _ = ((k + 1 - j : ℕ) : WithBot ℕ) := by simp
      have hmul := le_trans (Polynomial.degree_mul_le _ _) (add_le_add hdeg1 hdeg2)
      rw [zero_add] at hmul
      exact le_trans hmul (WithBot.coe_le_coe.mpr (by exact_mod_cast (show k + 1 - j ≤ k by omega)))
    exact lt_of_le_of_lt hle (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self k))
  have hinj : Set.InjOn (Nat.cast (R := ℚ)) (Finset.range (k + 1) : Set ℕ) := by
    intro a _ b _ hab
    exact Nat.cast_injective hab
  have hP_eq : P = Lagrange.interpolate (Finset.range (k + 1)) (Nat.cast (R := ℚ))
      (fun m => P.eval (m : ℚ)) :=
    Lagrange.eq_interpolate hinj hP_deg
  have hinterp_eq : Lagrange.interpolate (Finset.range (k + 1)) (Nat.cast (R := ℚ))
      (fun m => (OMA.S_oeis_a355257.A m (k + 1) : ℚ)) = P := by
    rw [hP_eq]
    congr 1
    ext m
    exact (hP_eval m).symm
  rw [hinterp_eq, hP_eval n]

private lemma pred_dvd_A_of_prime_even (p n : ℕ) (hp : p.Prime) (hn : Even n) :
    (p - 1) ∣ OMA.S_oeis_a355257.A n p := by
  by_cases hp2 : p = 2
  · subst hp2; exact one_dvd _
  · by_cases hp3 : p = 3
    · subst hp3
      unfold OMA.S_oeis_a355257.A
      have hIcc : Finset.Icc 1 3 = {1, 2, 3} := by decide
      rw [hIcc]
      rcases hn with ⟨m, rfl⟩
      have hsum : ∑ j ∈ ({1, 2, 3} : Finset ℕ),
          (Nat.factorial 3 / j) * (2 ^ j - 1) * Nat.choose (m + m + 3 - j - 1) (3 - j) =
          6 * Nat.choose (m + m + 1) 2 + 18 * m + 14 := by
        rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
        rw [show m + m + 3 - 1 - 1 = m + m + 1 by omega,
            show m + m + 3 - 2 - 1 = m + m by omega,
            show m + m + 3 - 3 - 1 = m + m - 1 by omega,
            show 3 - 1 = 2 by decide, show 3 - 2 = 1 by decide, show 3 - 3 = 0 by decide,
            Nat.choose_one_right, Nat.choose_zero_right]
        have hf1 : Nat.factorial 3 / 1 * (2 ^ 1 - 1) = 6 := by decide
        have hf2 : Nat.factorial 3 / 2 * (2 ^ 2 - 1) = 9 := by decide
        have hf3 : Nat.factorial 3 / 3 * (2 ^ 3 - 1) = 14 := by decide
        rw [hf1, hf2, hf3]; ring
      rw [hsum]
      exact ⟨3 * Nat.choose (m + m + 1) 2 + 9 * m + 7, by ring⟩
    · have hp5 : 5 ≤ p := by
        have := hp.two_le
        have : p ≠ 4 := fun h => by subst h; exact absurd hp (by decide)
        omega
      unfold OMA.S_oeis_a355257.A
      apply Finset.dvd_sum
      intro j hj
      have hj_icc := Finset.mem_Icc.mp hj
      by_cases hjp : j = p
      · rw [hjp]
        have hfk : p.factorial / p = (p - 1).factorial := by
          have hp_eq : p = (p - 1) + 1 := by omega
          conv_lhs => rw [hp_eq, Nat.factorial_succ]
          rw [← hp_eq, Nat.mul_div_cancel_left _ (by omega)]
        rw [hfk]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Nat.dvd_factorial (by omega) le_rfl) _) _
      · by_cases hjm1 : j = p - 1
        · rw [hjm1]
          have hfk : p.factorial / (p - 1) = p * (p - 2).factorial := by
            have hp_eq : p = (p - 1) + 1 := by omega
            have hpm1 : p - 1 = (p - 2) + 1 := by omega
            have hfact : p.factorial = (p * (p - 2).factorial) * (p - 1) := by
              conv_lhs => rw [hp_eq, Nat.factorial_succ]
              rw [← hp_eq]
              conv_lhs => rw [hpm1, Nat.factorial_succ]
              rw [← hpm1]; ring
            rw [hfact, Nat.mul_div_cancel _ (by omega)]
          have hch : Nat.choose (n + p - (p - 1) - 1) (p - (p - 1)) = n := by
            rw [show n + p - (p - 1) - 1 = n by omega, show p - (p - 1) = 1 by omega,
                Nat.choose_one_right]
          rw [hfk, hch]
          rcases hn with ⟨m, rfl⟩
          have hp_odd : p % 2 = 1 := by
            rcases hp.eq_two_or_odd with h2 | hodd
            · exact absurd h2 hp2
            · exact hodd
          set r := (p - 1) / 2
          have hr_eq : p - 1 = 2 * r := by omega
          have hr_le : r ≤ p - 2 := by omega
          have hr_pos : 1 ≤ r := by omega
          have hrdvd : r ∣ (p - 2).factorial := Nat.dvd_factorial hr_pos hr_le
          rcases hrdvd with ⟨q, hq⟩
          have hdiv : 2 * r ∣ p * (p - 2).factorial * (2 ^ (p - 1) - 1) * (m + m) := by
            rw [hq]
            exact ⟨p * q * (2 ^ (p - 1) - 1) * m, by ring⟩
          rwa [← hr_eq] at hdiv
        · have hj_le : j ≤ p - 2 := by omega
          have hjdvd : j ∣ (p - 2).factorial := Nat.dvd_factorial hj_icc.1 hj_le
          rcases hjdvd with ⟨q, hq⟩
          have hdiv : (p - 1) ∣ p.factorial / j := by
            refine ⟨p * q, ?_⟩
            have hp_eq : p = (p - 1) + 1 := by omega
            have hpm1 : p - 1 = (p - 2) + 1 := by omega
            have hfact : p.factorial = ((p - 1) * (p * q)) * j := by
              conv_lhs => rw [hp_eq, Nat.factorial_succ]
              rw [← hp_eq]
              conv_lhs => rw [hpm1, Nat.factorial_succ]
              rw [← hpm1, hq]; ring
            rw [hfact, Nat.mul_div_cancel _ (by omega)]
          exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hdiv _) _

private lemma claim4 (p n : ℕ) (hp : p.Prime) (hn : Even n) :
    (p - 1) ∣ OMA.S_oeis_a355257.A n p ∧ OMA.S_oeis_a355257.A n p / (p - 1) ≡ 1 [MOD p] := by
  have hdvd := pred_dvd_A_of_prime_even p n hp hn
  refine ⟨hdvd, ?_⟩
  have h1 := claim1 p n hp
  have hmul : (p - 1) * (OMA.S_oeis_a355257.A n p / (p - 1)) ≡ (p - 1) * 1 [MOD p] := by
    rw [Nat.mul_div_cancel' hdvd, mul_one]
    exact h1
  have hcop : Nat.Coprime p (p - 1) := by
    have hp_eq : p = (p - 1) + 1 := by have := hp.two_le; omega
    conv_lhs => rw [hp_eq]
    exact Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)
  exact Nat.ModEq.cancel_left_of_coprime hcop hmul

end OeisA355257Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a355257.main :=
  ⟨OeisA355257Proof.claim1, OeisA355257Proof.claim2,
   OeisA355257Proof.claim3, OeisA355257Proof.claim4⟩
