import OMAStatements.S_oeis_a179508
import Mathlib

/-!
# Proof of OEIS A179508 (Sun-Zagier Theorem)

We define the linear functional `L : Polynomial (ZMod p) → ZMod p` by `L(X^k) = bell k`.
From the Bell recurrence `bell (k + 1) = ∑_{j=0}^k C(k, j) * bell j`, we have
`L(X * P(X)) = L(P(X + 1))` for all polynomials `P`.

For `P_m(X) = ∑_{k=0}^{p-1} (-m)^{p-1-k} X^k`, we have `(X + m) * P_m(X) = X^p + m` in `Polynomial (ZMod p)`,
so `P_m(X + 1) = P_{m+1}(X)`. Applying `L` to `X * P_m(X) = (X^p + m) - m * P_m(X)` gives
`L(P_{m+1}) = bell p + m - m * L(P_m)`.
Since `bell p ≡ 2 (mod p)` (Touchard's congruence, proved via `L((X + 1)^p - X^p - 1) = 0`),
we obtain the recurrence `h(m + 1) = 2 + m - m * h(m)` with `h(1) = 2`!
-/

namespace OeisA179508Proof

open Finset Polynomial

private lemma bell_zero : OMA.S_oeis_a179508.bell 0 = 1 := by
  rw [OMA.S_oeis_a179508.bell]

private lemma bell_succ (n : ℕ) : OMA.S_oeis_a179508.bell (n + 1) =
    ∑ j ∈ Finset.range (n + 1), Nat.choose n j * OMA.S_oeis_a179508.bell j := by
  rw [OMA.S_oeis_a179508.bell]
  refine Finset.sum_bij (fun j _ => n - j) ?_ ?_ ?_ ?_
  · intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
  · intro j1 hj1 j2 hj2 h; simp only [Finset.mem_range] at hj1 hj2; omega
  · intro j hj; refine ⟨n - j, ?_, ?_⟩
    · simp only [Finset.mem_range] at hj ⊢; omega
    · simp only [Finset.mem_range] at hj; omega
  · intro j hj
    have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Nat.choose_symm hjle]

/-- The sequence `a(n)` defined by `a(0) = 0`, `a(1) = 2`, `a(n + 1) = 2 + n - n * a(n)`. -/
private def aSeq : ℕ → ℤ
  | 0 => 0
  | 1 => 2
  | n + 2 => 2 + (n + 1 : ℤ) - (n + 1 : ℤ) * aSeq (n + 1)

private lemma aSeq_succ (m : ℕ) (hm : 1 ≤ m) :
    aSeq (m + 1) = 2 + (m : ℤ) - (m : ℤ) * aSeq m := by
  cases m with
  | zero => omega
  | succ m' => rfl

/-- Linear functional `L(P) = ∑_k P.coeff k * bell k` over `ZMod p`. -/
private def L (p : ℕ) (P : Polynomial (ZMod p)) : ZMod p :=
  P.sum (fun k c => c * (OMA.S_oeis_a179508.bell k : ZMod p))

private lemma L_add (p : ℕ) (P Q : Polynomial (ZMod p)) : L p (P + Q) = L p P + L p Q := by
  unfold L
  exact Polynomial.sum_add_index P Q (fun k a => a * (OMA.S_oeis_a179508.bell k : ZMod p))
    (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

private lemma L_sub (p : ℕ) (P Q : Polynomial (ZMod p)) : L p (P - Q) = L p P - L p Q := by
  have h := L_add p (P - Q) Q
  rw [sub_add_cancel] at h
  linear_combination -h

private lemma L_smul (p : ℕ) (c : ZMod p) (P : Polynomial (ZMod p)) :
    L p (Polynomial.C c * P) = c * L p P := by
  unfold L
  rw [Polynomial.C_mul', Polynomial.sum_smul_index' _ _ _ (fun _ => zero_mul _)]
  rw [Polynomial.sum_def, Polynomial.sum_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [smul_eq_mul]
  ring

private lemma L_C (p : ℕ) (c : ZMod p) : L p (Polynomial.C c) = c := by
  unfold L
  rw [Polynomial.sum_C_index (f := fun k a => a * (OMA.S_oeis_a179508.bell k : ZMod p)) (zero_mul _),
      bell_zero, Nat.cast_one, mul_one]

private lemma L_monomial (p : ℕ) (k : ℕ) (c : ZMod p) :
    L p (Polynomial.monomial k c) = c * (OMA.S_oeis_a179508.bell k : ZMod p) := by
  unfold L
  exact Polynomial.sum_monomial_index (n := k) (a := c)
    (f := fun k (a : ZMod p) => a * (OMA.S_oeis_a179508.bell k : ZMod p)) (zero_mul _)

private lemma L_X_pow (p : ℕ) (k : ℕ) :
    L p (Polynomial.X ^ k) = (OMA.S_oeis_a179508.bell k : ZMod p) := by
  rw [← Polynomial.monomial_one_right_eq_X_pow, L_monomial, one_mul]

private lemma L_finset_sum {ι : Type*} (p : ℕ) (s : Finset ι) (f : ι → Polynomial (ZMod p)) :
    L p (∑ i ∈ s, f i) = ∑ i ∈ s, L p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [L]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, L_add, ih, Finset.sum_insert ha]

private lemma L_X_mul_eq_comp_add_one (p : ℕ) (P : Polynomial (ZMod p)) :
    L p (Polynomial.X * P) = L p (P.comp (Polynomial.X + 1)) := by
  induction P using Polynomial.induction_on' with
  | add P Q ihP ihQ =>
    rw [mul_add, Polynomial.add_comp, L_add, L_add, ihP, ihQ]
  | monomial k c =>
    rw [Polynomial.monomial_comp, Polynomial.C_mul_X_pow_eq_monomial.symm]
    rw [show Polynomial.X * (Polynomial.C c * Polynomial.X ^ k) =
          Polynomial.C c * Polynomial.X ^ (k + 1) by ring]
    rw [L_smul, L_X_pow, L_smul]
    congr 1
    rw [add_pow, L_finset_sum]
    have hbell := congrArg (Nat.cast (R := ZMod p)) (bell_succ k)
    push_cast at hbell
    rw [hbell]
    apply Finset.sum_congr rfl
    intro j _
    rw [one_pow, mul_one, show Polynomial.X ^ j * ((Nat.choose k j : ℕ) : Polynomial (ZMod p)) =
          Polynomial.C (Nat.choose k j : ZMod p) * Polynomial.X ^ j by
            rw [mul_comm]; simp]
    rw [L_smul, L_X_pow]

/-- Touchard's congruence `bell p ≡ 2 [MOD p]` via `L(X^p) = L(X^{p-1} * X) = ...`.
More directly: `L((X + 1)^p) = L(X^p + 1) = L(X^p) + 1`, and by iterating `L(P(X + 1)) = L(X * P(X))`,
`L(X * P(X + k))`... Actually: `L(P(X + 1)) = L(X * P(X))` gives for `P = X^p - X`:
`L(X^p - X) = L(X * (X^{p-1} - 1)) = L((X + 1)^{p-1} - 1)`.
Even simpler: by induction on `k`, `L(X^k) = bell k`, and we prove `L(X^p) = 2` via
`L((X + 1)^k) = L(X * X^k) = bell (k + 1)`? Wait: let's prove `L(X^p) = 2` using the
falling factorial polynomial `∏_{i=0}^{p-1} (X - i) = X^p - X` in `Polynomial (ZMod p)`!
Let `F_m(X) = ∏_{i=0}^{m-1} (X - i)`. Then `F_m(X + 1) = (X + 1) * F_{m-1}(X)`?
NO! `F_m(X + 1) = ∏_{i=0}^{m-1} (X + 1 - i) = (X + 1) * ∏_{j=0}^{m-2} (X - j) = (X + 1) * F_{m-1}(X)`!
Wait: `L(X * F_m(X)) = L(F_m(X + 1))`!
On the other hand, `X * F_m(X) = (X - m) * F_m(X) + m * F_m(X) = F_{m+1}(X) + m * F_m(X)`!
AND `L(F_0(X)) = L(1) = 1`, `L(F_1(X)) = L(X) = 1`!
Wait: `L(F_{m+1}) = L(F_m(X + 1)) - m * L(F_m)` = `L((X + 1) F_{m-1}) - m * L(F_m)`
= `L(X F_{m-1}) + L(F_{m-1}) - m * L(F_m)`!
Wait: `L(F_m)` is ALWAYS `1`!!
CHECK THAT!!
- `L(F_0) = L(1) = 1`.
- `L(F_1) = L(X) = B_1 = 1`.
- `L(F_2) = L(X(X-1)) = B_2 - B_1 = 2 - 1 = 1`.
- `L(F_3) = L(X(X-1)(X-2)) = B_3 - 3 B_2 + 2 B_1 = 5 - 6 + 2 = 1`!
BECAUSE `B_k = ∑_{j=0}^k S(k, j)` AND `X^k = ∑_{j=0}^k S(k, j) F_j(X)`!!
PROVE `L(F_m) = 1` BY INDUCTION ON `m` IN 5 LINES:
`F_{m+1}(X) = (X - m) F_m(X)`, so `L(F_{m+1}) = L(X F_m) - m L(F_m) = L(F_m(X+1)) - m L(F_m)`.
And `F_m(X + 1) = (X + 1) * F_{m-1}(X) = F_m(X) + m * F_{m-1}(X)` (since `(X + 1) - (X - (m - 1)) = m`!!)!
WAIT A SECOND!!
CHECK `(X + 1) * F_{m-1}(X) = ((X - (m - 1)) + m) * F_{m-1}(X) = F_m(X) + m * F_{m-1}(X)`!!
APPLY `L` TO BOTH SIDES:
`L(F_{m+1}) = L(F_m) + m * L(F_{m-1}) - m * L(F_m) = 1 + m * 1 - m * 1 = 1`!!
AND THEN FOR `m = p`:
`X^p - X = F_p(X)` IN `Polynomial (ZMod p)` (`ZMod.prod_X_sub_smul` / `X_pow_card_sub_X`)!
APPLY `L` TO `X^p - X = F_p(X)`:
`L(X^p) - L(X) = L(F_p) = 1`, SO `L(X^p) = 1 + L(X) = 1 + 1 = 2`!!
-/
private noncomputable def fallPoly (p : ℕ) : ℕ → Polynomial (ZMod p)
  | 0 => 1
  | m + 1 => fallPoly p m * (Polynomial.X - Polynomial.C (m : ZMod p))

private lemma fallPoly_comp_add_one (p : ℕ) :
    ∀ m : ℕ, (fallPoly p (m + 1)).comp (Polynomial.X + 1) =
      fallPoly p (m + 1) + Polynomial.C ((m + 1 : ℕ) : ZMod p) * fallPoly p m := by
  intro m
  induction m with
  | zero =>
    simp [fallPoly]
  | succ m ih =>
    have h1 : (fallPoly p (m + 2)).comp (Polynomial.X + 1) =
        (fallPoly p (m + 1)).comp (Polynomial.X + 1) *
          (Polynomial.X - Polynomial.C (m : ZMod p)) := by
      simp only [fallPoly, Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.X_comp,
                 Polynomial.C_comp]
      congr 1
      push_cast
      rw [map_add, map_one]
      ring
    rw [h1, ih, add_mul]
    simp only [fallPoly]
    push_cast
    simp only [map_add, map_one]
    ring

private lemma L_fallPoly (p : ℕ) : ∀ m : ℕ, L p (fallPoly p m) = 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero =>
      simpa [fallPoly] using L_C p 1
    | succ m =>
      cases m with
      | zero =>
        have h : fallPoly p 1 = Polynomial.X := by simp [fallPoly]
        rw [h, show Polynomial.X = Polynomial.X ^ 1 by ring, L_X_pow]
        have hb1 : OMA.S_oeis_a179508.bell 1 = 1 := by
          rw [bell_succ, Finset.sum_range_one]; simp [bell_zero]
        rw [hb1, Nat.cast_one]
      | succ m' =>
        have hrel : fallPoly p (m' + 2) =
            Polynomial.X * fallPoly p (m' + 1) -
              Polynomial.C ((m' + 1 : ℕ) : ZMod p) * fallPoly p (m' + 1) := by
          simp only [fallPoly]
          ring
        rw [hrel, L_sub, L_X_mul_eq_comp_add_one, fallPoly_comp_add_one, L_add, L_smul, L_smul]
        rw [ih (m' + 1) (by omega), ih m' (by omega)]
        ring

private lemma fallPoly_eq_prod (p : ℕ) :
    ∀ m : ℕ, fallPoly p m = ∏ i ∈ Finset.range m, (Polynomial.X - Polynomial.C (i : ZMod p)) := by
  intro m
  induction m with
  | zero => simp [fallPoly]
  | succ m ih => rw [fallPoly, ih, Finset.prod_range_succ]

private lemma bell_prime_zmod {p : ℕ} (hp : p.Prime) :
    (OMA.S_oeis_a179508.bell p : ZMod p) = 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hprod : fallPoly p p = Polynomial.X ^ p - Polynomial.X := by
    rw [fallPoly_eq_prod]
    have hcard : ∏ a : ZMod p, (Polynomial.X - Polynomial.C a) = Polynomial.X ^ p - Polynomial.X := by
      have hP_monic : (∏ a : ZMod p, (Polynomial.X - Polynomial.C a)).Monic :=
        Polynomial.monic_prod_of_monic _ _ (fun a _ => Polynomial.monic_X_sub_C a)
      have hQ_monic : (Polynomial.X ^ p - Polynomial.X : Polynomial (ZMod p)).Monic := by
        apply Polynomial.monic_X_pow_sub
        rw [Polynomial.degree_X]
        exact WithBot.coe_lt_coe.mpr hp.one_lt
      have hdvd : (∏ a : ZMod p, (Polynomial.X - Polynomial.C a)) ∣
          (Polynomial.X ^ p - Polynomial.X : Polynomial (ZMod p)) := by
        apply Finset.prod_dvd_of_coprime
        · intro a _ b _ hab
          exact Polynomial.pairwise_coprime_X_sub_C Function.injective_id hab
        · intro a _
          rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def,
              Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
              ZMod.pow_card, sub_self]
      have hdegP : (∏ a : ZMod p, (Polynomial.X - Polynomial.C a)).natDegree = p := by
        rw [Polynomial.natDegree_prod_of_monic _ _ (fun a _ => Polynomial.monic_X_sub_C a)]
        simp [ZMod.card]
      have hdegQ : (Polynomial.X ^ p - Polynomial.X : Polynomial (ZMod p)).natDegree = p := by
        rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
        · exact Polynomial.natDegree_X_pow p
        · rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]; exact hp.one_lt
      rcases hdvd with ⟨R, hR⟩
      have hR_ne : R ≠ 0 := by intro h0; rw [h0, mul_zero] at hR; exact hQ_monic.ne_zero hR
      have hdegR : R.natDegree = 0 := by
        have h1 := Polynomial.natDegree_mul hP_monic.ne_zero hR_ne
        rw [← hR, hdegP, hdegQ] at h1; omega
      have hR_eq : R = Polynomial.C (R.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdegR
      have hlc : R.coeff 0 = 1 := by
        have := congrArg Polynomial.leadingCoeff hR
        rw [hQ_monic.leadingCoeff, Polynomial.leadingCoeff_mul, hP_monic.leadingCoeff, one_mul,
            hR_eq, Polynomial.leadingCoeff_C] at this
        exact this.symm
      rw [hR, hR_eq, hlc, map_one, mul_one]
    rw [← hcard]
    refine Finset.prod_bij (fun i _ => (i : ZMod p)) ?_ ?_ ?_ ?_
    · intro i _; exact Finset.mem_univ _
    · intro i1 hi1 i2 hi2 heq
      have h1 : i1 < p := Finset.mem_range.mp hi1
      have h2 : i2 < p := Finset.mem_range.mp hi2
      have := congrArg ZMod.val heq
      rwa [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at this
    · intro a _
      exact ⟨a.val, Finset.mem_range.mpr (ZMod.val_lt a), ZMod.natCast_zmod_val a⟩
    · intro i _; rfl
  have hL := congrArg (L p) hprod
  rw [L_fallPoly, L_sub, L_X_pow, show Polynomial.X = Polynomial.X ^ 1 by ring, L_X_pow] at hL
  have hb1 : OMA.S_oeis_a179508.bell 1 = 1 := by
    rw [bell_succ, Finset.sum_range_one]; simp [bell_zero]
  rw [hb1, Nat.cast_one] at hL
  linear_combination -hL

/-- Helper polynomial `P_m(X) = ∑_{k=0}^{p-1} (-m)^{p-1-k} * X^k`. -/
private noncomputable def Pm (p : ℕ) (m : ZMod p) : Polynomial (ZMod p) :=
  ∑ k ∈ Finset.range p, Polynomial.C ((-m) ^ (p - 1 - k)) * Polynomial.X ^ k

private lemma mul_Pm_eq {p : ℕ} (hp : p.Prime) (m : ZMod p) :
    (Polynomial.X + Polynomial.C m) * Pm p m = Polynomial.X ^ p + Polynomial.C m := by
  have : Fact p.Prime := ⟨hp⟩
  have htel : (Polynomial.X - Polynomial.C (-m)) *
      ∑ k ∈ Finset.range p, Polynomial.C ((-m) ^ (p - 1 - k)) * Polynomial.X ^ k =
      Polynomial.X ^ p - Polynomial.C ((-m) ^ p) := by
    have h1 := geom_sum₂_mul (Polynomial.X : Polynomial (ZMod p)) (Polynomial.C (-m)) p
    have h2 : ∑ k ∈ Finset.range p, Polynomial.X ^ k * Polynomial.C (-m) ^ (p - 1 - k) =
        ∑ k ∈ Finset.range p, Polynomial.C ((-m) ^ (p - 1 - k)) * Polynomial.X ^ k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← map_pow, mul_comm]
    rw [h2, mul_comm] at h1
    rw [h1, map_pow]
  have hneg : Polynomial.X + Polynomial.C m = Polynomial.X - Polynomial.C (-m) := by
    rw [map_neg, sub_neg_eq_add]
  have hpow : (-m) ^ p = -m := ZMod.pow_card (-m)
  unfold Pm
  rw [hneg, htel, hpow, map_neg, sub_neg_eq_add]

private lemma Pm_comp_add_one {p : ℕ} (hp : p.Prime) (m : ZMod p) :
    (Pm p m).comp (Polynomial.X + 1) = Pm p (m + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hne : (Polynomial.X + Polynomial.C (m + 1) : Polynomial (ZMod p)) ≠ 0 :=
    Polynomial.X_add_C_ne_zero (m + 1)
  apply mul_left_cancel₀ hne
  have h1 := congrArg (fun q => q.comp (Polynomial.X + 1)) (mul_Pm_eq hp m)
  simp only [Polynomial.mul_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
             Polynomial.pow_comp] at h1
  have hxp : (Polynomial.X + 1 : Polynomial (ZMod p)) ^ p = Polynomial.X ^ p + 1 := by
    rw [add_pow_char, one_pow]
  have hlin : (Polynomial.X + 1 : Polynomial (ZMod p)) + Polynomial.C m =
      Polynomial.X + Polynomial.C (m + 1) := by
    rw [map_add, map_one]; ring
  rw [hlin, hxp] at h1
  rw [h1, mul_Pm_eq hp (m + 1), map_add, map_one]
  ring

private lemma L_Pm_succ {p : ℕ} (hp : p.Prime) (m : ZMod p) :
    L p (Pm p (m + 1)) = 2 + m - m * L p (Pm p m) := by
  have hmul : Polynomial.X * Pm p m = Polynomial.X ^ p + Polynomial.C m - Polynomial.C m * Pm p m := by
    have := mul_Pm_eq hp m
    linear_combination this
  have hL := congrArg (L p) hmul
  rw [L_X_mul_eq_comp_add_one, Pm_comp_add_one hp m, L_sub, L_add, L_X_pow, L_C, L_smul,
      bell_prime_zmod hp] at hL
  exact hL

private lemma L_Pm_eq_aSeq {p : ℕ} (hp : p.Prime) :
    ∀ n : ℕ, 1 ≤ n → L p (Pm p (n : ZMod p)) = (aSeq n : ZMod p) := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      have h0 := L_Pm_succ hp 0
      simp only [zero_add, add_zero, zero_mul, sub_zero] at h0
      simpa [aSeq] using h0
    | succ n' =>
      have hstep := L_Pm_succ hp ((n' + 1 : ℕ) : ZMod p)
      rw [ih (by omega)] at hstep
      rw [aSeq_succ (n' + 1) (by omega)]
      push_cast at hstep ⊢
      exact hstep

private lemma sun_zagier (n : ℕ) (hn : 1 ≤ n) :
    OMA.S_oeis_a179508.SatisfiesCongruence n (aSeq n) := by
  intro p hp hndvd
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : (n : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hneg0 : (-(n : ZMod p)) ≠ 0 := neg_ne_zero.mpr hn0
  have hpow_card : (-(n : ZMod p)) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hneg0
  have hsum : (∑ k ∈ Finset.range p, (OMA.S_oeis_a179508.bell k : ZMod p) * (-(n : ZMod p))⁻¹ ^ k) =
      L p (Pm p (n : ZMod p)) := by
    unfold Pm
    rw [L_finset_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkp : k ≤ p - 1 := by have := Finset.mem_range.mp hk; omega
    rw [L_smul, L_X_pow, mul_comm]
    congr 1
    have hinv : (-(n : ZMod p))⁻¹ ^ k = (-(n : ZMod p)) ^ (p - 1 - k) := by
      apply mul_right_cancel₀ (pow_ne_zero k hneg0)
      rw [← mul_pow, inv_mul_cancel₀ hneg0, one_pow, ← pow_add,
          Nat.sub_add_cancel hkp, hpow_card]
    exact hinv
  rw [hsum, L_Pm_eq_aSeq hp n hn]

private lemma unique_of_congr (n : ℕ) (hn : 1 ≤ n) (x y : ℤ)
    (hx : OMA.S_oeis_a179508.SatisfiesCongruence n x)
    (hy : OMA.S_oeis_a179508.SatisfiesCongruence n y) : x = y := by
  by_contra hne
  obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (max n (x - y).natAbs + 1)
  have hndvd : ¬ p ∣ n := by
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd; omega
  have hpx := hx p hp hndvd
  have hpy := hy p hp hndvd
  have hzeq : ((x - y : ℤ) : ZMod p) = 0 := by
    rw [Int.cast_sub, ← hpx, ← hpy, sub_self]
  have hdvdZ : (p : ℤ) ∣ (x - y) := (ZMod.intCast_zmod_eq_zero_iff_dvd (x - y) p).mp hzeq
  have hdvdN : p ∣ (x - y).natAbs := Int.natCast_dvd.mp hdvdZ
  have hpos : 0 < (x - y).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr hne)
  have hle := Nat.le_of_dvd hpos hdvdN
  have : (x - y).natAbs < p := by omega
  omega

private lemma aSeq_sign : ∀ n : ℕ, 3 ≤ n → 0 < (-1 : ℤ) ^ (n - 1) * aSeq n := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h3 : n + 1 = 3
    · rw [h3]; decide
    · by_cases h4 : n + 1 = 4
      · rw [h4]; decide
      · have hn3 : 3 ≤ n := by omega
        have hprev := ih hn3
        rw [aSeq_succ n (by omega)]
        have hpow : (-1 : ℤ) ^ (n + 1 - 1) = -((-1 : ℤ) ^ (n - 1)) := by
          have : n + 1 - 1 = (n - 1) + 1 := by omega
          rw [this, pow_succ]; ring
        rw [hpow]
        have hcalc : -((-1 : ℤ) ^ (n - 1)) * (2 + (n : ℤ) - (n : ℤ) * aSeq n) =
            (n : ℤ) * ((-1 : ℤ) ^ (n - 1) * aSeq n) - (-1 : ℤ) ^ (n - 1) * (2 + (n : ℤ)) := by ring
        rw [hcalc]
        -- Even cleaner: prove (-1)^(n-1) * aSeq n >= 2 for n >= 5, and n = 3, 4 by decide!
        have hge : ∀ k : ℕ, 5 ≤ k → 2 ≤ (-1 : ℤ) ^ (k - 1) * aSeq k := by
          intro k hk
          induction k with
          | zero => omega
          | succ k ihk =>
            by_cases hk5 : k + 1 = 5
            · rw [hk5]; decide
            · have hk5' : 5 ≤ k := by omega
              have hprev2 := ihk hk5'
              rw [aSeq_succ k (by omega)]
              have hp2 : (-1 : ℤ) ^ (k + 1 - 1) = -((-1 : ℤ) ^ (k - 1)) := by
                have : k + 1 - 1 = (k - 1) + 1 := by omega
                rw [this, pow_succ]; ring
              rw [hp2]
              have hc2 : -((-1 : ℤ) ^ (k - 1)) * (2 + (k : ℤ) - (k : ℤ) * aSeq k) =
                  (k : ℤ) * ((-1 : ℤ) ^ (k - 1) * aSeq k) - (-1 : ℤ) ^ (k - 1) * (2 + (k : ℤ)) := by ring
              rw [hc2]
              have habs : (-1 : ℤ) ^ (k - 1) ≤ 1 := by
                rcases neg_one_pow_eq_or ℤ (k - 1) with h | h <;> omega
              nlinarith
        have h2 := hge (n + 1) (by omega)
        rw [aSeq_succ n (by omega), hpow, hcalc] at h2
        omega

end OeisA179508Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a179508.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    exact ⟨OeisA179508Proof.aSeq n, OeisA179508Proof.sun_zagier n hn,
      fun y hy => OeisA179508Proof.unique_of_congr n hn y (OeisA179508Proof.aSeq n) hy
        (OeisA179508Proof.sun_zagier n hn)⟩
  · refine ⟨OeisA179508Proof.sun_zagier 1 (by decide),
            OeisA179508Proof.sun_zagier 2 (by decide),
            OeisA179508Proof.sun_zagier 3 (by decide),
            OeisA179508Proof.sun_zagier 4 (by decide),
            OeisA179508Proof.sun_zagier 5 (by decide),
            OeisA179508Proof.sun_zagier 6 (by decide),
            OeisA179508Proof.sun_zagier 7 (by decide),
            OeisA179508Proof.sun_zagier 8 (by decide),
            OeisA179508Proof.sun_zagier 9 (by decide),
            OeisA179508Proof.sun_zagier 10 (by decide)⟩
  · intro n hn x hx
    have hxeq : x = OeisA179508Proof.aSeq n :=
      OeisA179508Proof.unique_of_congr n (by omega) x (OeisA179508Proof.aSeq n) hx
        (OeisA179508Proof.sun_zagier n (by omega))
    rw [hxeq]
    exact OeisA179508Proof.aSeq_sign n hn
