import OMAReductions.R_Erdos377_erdos_377_variants_ub_R1
import Mathlib

/-!
# Proof of `Erdos377.erdos_377.variants.ub.R1.H2`

Elementary self-contained proof via:
1. Hensel-Vandermonde congruence counting (`OMA.Erdos377M1`),
2. Vinogradov's Mean Value Theorem via p-adic recursion and discrete Parseval (`OMA.Erdos377M2`),
3. Vinogradov-Korobov reciprocal exponential sum bound (`OMA.Erdos377M3`),
4. Vaughan's identity, Type I/II bounds, and Chebyshev dyadic tails (`OMA.Erdos377M4`).
-/


/-
Hensel-Vandermonde congruence counting lemma for Vinogradov's mean value theorem.
-/

namespace OMA.Erdos377M1

open Finset Polynomial Matrix
open scoped BigOperators

/-- Reciprocal polynomial `∏ i ∈ S, (1 - C (x i) * X)` satisfies Newton's derivative identity
    relating coefficients to power sums. -/
private lemma newton_deriv_coeff {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (x : ι → R) (S : Finset ι) :
    ∀ m : ℕ, 1 ≤ m →
      (∏ i ∈ S, (1 - C (x i) * X)).derivative.coeff (m - 1) =
        - ∑ r ∈ range m, (∏ i ∈ S, (1 - C (x i) * X)).coeff r * (∑ i ∈ S, (x i) ^ (m - r)) := by
  induction S using Finset.induction_on with
  | empty =>
    intro m _
    simp
  | @insert a S ha ih =>
    intro m hm
    let Q : R[X] := ∏ i ∈ S, (1 - C (x i) * X)
    have hprod : ∏ i ∈ insert a S, (1 - C (x i) * X) = (1 - C (x a) * X) * Q := by
      rw [prod_insert ha]
    have hcoeff0 : ((1 - C (x a) * X) * Q).coeff 0 = Q.coeff 0 := by
      simp [sub_mul]
    have hcoeff_succ : ∀ r : ℕ,
        ((1 - C (x a) * X) * Q).coeff (r + 1) = Q.coeff (r + 1) - x a * Q.coeff r := by
      intro r
      rw [sub_mul, one_mul, coeff_sub, mul_assoc, coeff_C_mul, mul_comm X Q, coeff_mul_X]
    have hder : ((1 - C (x a) * X) * Q).derivative =
        (1 - C (x a) * X) * Q.derivative - C (x a) * Q := by
      rw [derivative_mul, derivative_sub, derivative_one, derivative_C_mul, derivative_X,
        mul_one, zero_sub, neg_mul]
      ring
    rw [hprod]
    have hsum_ins : ∀ d : ℕ, ∑ i ∈ insert a S, (x i) ^ d = (x a) ^ d + ∑ i ∈ S, (x i) ^ d :=
      fun d => sum_insert ha
    have hsplit : ∑ r ∈ range m, ((1 - C (x a) * X) * Q).coeff r * (∑ i ∈ insert a S, (x i) ^ (m - r)) =
        (∑ r ∈ range m, ((1 - C (x a) * X) * Q).coeff r * (x a) ^ (m - r)) +
        (∑ r ∈ range m, ((1 - C (x a) * X) * Q).coeff r * (∑ i ∈ S, (x i) ^ (m - r))) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun r _ => ?_
      rw [hsum_ins, mul_add]
    have htelescope : ∑ r ∈ range m, ((1 - C (x a) * X) * Q).coeff r * (x a) ^ (m - r) =
        x a * Q.coeff (m - 1) := by
      cases m with
      | zero => omega
      | succ n =>
        clear ih hm hsplit
        induction n with
        | zero =>
          simp only [Nat.zero_add, sum_range_one, Nat.sub_zero, pow_one, Nat.sub_self, hcoeff0]
          ring
        | succ n ih' =>
          rw [sum_range_succ]
          have hshift : ∑ r ∈ range (n + 1),
              ((1 - C (x a) * X) * Q).coeff r * (x a) ^ (n + 1 + 1 - r) =
              x a * ∑ r ∈ range (n + 1),
                ((1 - C (x a) * X) * Q).coeff r * (x a) ^ (n + 1 - r) := by
            rw [mul_sum]
            refine sum_congr rfl fun r hr => ?_
            have hrlt : r < n + 1 := mem_range.mp hr
            have hsub : n + 1 + 1 - r = (n + 1 - r) + 1 := by omega
            rw [hsub, pow_succ]
            ring
          rw [hshift, ih', Nat.add_sub_cancel,
            show n + 1 + 1 - (n + 1) = 1 by omega, pow_one,
            show n + 1 + 1 - 1 = n + 1 by omega, hcoeff_succ]
          ring
    rw [hsplit, htelescope, hder, coeff_sub, coeff_C_mul]
    cases m with
    | zero => omega
    | succ n =>
      cases n with
      | zero =>
        have h1 := ih 1 le_rfl
        change Q.derivative.coeff 0 = - ∑ r ∈ range 1, Q.coeff r * ∑ i ∈ S, x i ^ (1 - r) at h1
        simp only [Nat.zero_add, Nat.sub_self, sum_range_one, Nat.sub_zero, pow_one, hcoeff0] at h1 ⊢
        have hder0 : ((1 - C (x a) * X) * Q.derivative).coeff 0 = Q.derivative.coeff 0 := by
          simp [sub_mul]
        rw [hder0, h1]
        ring
      | succ n =>
        have hsub1 : n + 1 + 1 - 1 = n + 1 := by omega
        rw [hsub1]
        have hder_c : ((1 - C (x a) * X) * Q.derivative).coeff (n + 1) =
            Q.derivative.coeff (n + 1) - x a * Q.derivative.coeff n := by
          rw [sub_mul, one_mul, coeff_sub, mul_assoc, coeff_C_mul, mul_comm X Q.derivative,
            coeff_mul_X]
        rw [hder_c]
        have h1 := ih (n + 2) (by omega)
        have h2 := ih (n + 1) (by omega)
        change Q.derivative.coeff (n + 1) =
          - ∑ r ∈ range (n + 2), Q.coeff r * ∑ i ∈ S, x i ^ (n + 2 - r) at h1
        change Q.derivative.coeff n =
          - ∑ r ∈ range (n + 1), Q.coeff r * ∑ i ∈ S, x i ^ (n + 1 - r) at h2
        have hS_sum : ∑ r ∈ range (n + 2), ((1 - C (x a) * X) * Q).coeff r * (∑ i ∈ S, x i ^ (n + 2 - r)) =
            (∑ r ∈ range (n + 2), Q.coeff r * (∑ i ∈ S, x i ^ (n + 2 - r))) -
            x a * (∑ r ∈ range (n + 1), Q.coeff r * (∑ i ∈ S, x i ^ (n + 1 - r))) := by
          rw [sum_range_succ', hcoeff0, sum_range_succ' (f := fun r => Q.coeff r * ∑ i ∈ S, x i ^ (n + 2 - r))]
          have htail : ∑ r ∈ range (n + 1), ((1 - C (x a) * X) * Q).coeff (r + 1) * (∑ i ∈ S, x i ^ (n + 2 - (r + 1))) =
              (∑ r ∈ range (n + 1), Q.coeff (r + 1) * (∑ i ∈ S, x i ^ (n + 2 - (r + 1)))) -
              x a * (∑ r ∈ range (n + 1), Q.coeff r * (∑ i ∈ S, x i ^ (n + 1 - r))) := by
            rw [mul_sum, ← sum_sub_distrib]
            refine sum_congr rfl fun r _ => ?_
            rw [hcoeff_succ]
            have hsub : n + 2 - (r + 1) = n + 1 - r := by omega
            rw [hsub]
            ring
          rw [htail]
          ring
        rw [h1, h2, hS_sum]
        ring

private lemma prod_X_sub_coeff_eq_recip {R : Type*} [CommRing R] [Nontrivial R]
    {ι : Type*} [DecidableEq ι] (x : ι → R) (S : Finset ι) :
    ∀ r ≤ S.card,
      (∏ i ∈ S, (X - C (x i))).coeff (S.card - r) = (∏ i ∈ S, (1 - C (x i) * X)).coeff r := by
  induction S using Finset.induction_on with
  | empty =>
    intro r hr
    have hr0 : r = 0 := by simpa using hr
    subst hr0
    simp
  | @insert a S ha ih =>
    intro r hr
    rw [prod_insert ha, prod_insert ha, card_insert_of_notMem ha]
    have hdeg_le : (∏ i ∈ S, (X - C (x i))).natDegree ≤ S.card := by
      calc (∏ i ∈ S, (X - C (x i))).natDegree
          ≤ ∑ i ∈ S, (X - C (x i)).natDegree := natDegree_prod_le S _
        _ = ∑ _i ∈ S, 1 := sum_congr rfl fun _ _ => natDegree_X_sub_C _
        _ = S.card := by simp
    cases r with
    | zero =>
      have h1 : ((X - C (x a)) * ∏ i ∈ S, (X - C (x i))).coeff (S.card + 1) =
          (∏ i ∈ S, (X - C (x i))).coeff S.card := by
        rw [sub_mul, coeff_sub, mul_comm X, coeff_mul_X, coeff_C_mul]
        have hzero : (∏ i ∈ S, (X - C (x i))).coeff (S.card + 1) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by omega)
        rw [hzero, mul_zero, sub_zero]
      have h2 : ((1 - C (x a) * X) * ∏ i ∈ S, (1 - C (x i) * X)).coeff 0 =
          (∏ i ∈ S, (1 - C (x i) * X)).coeff 0 := by
        simp [sub_mul]
      simpa [h1, h2] using ih 0 (Nat.zero_le _)
    | succ r =>
      have hrS : r ≤ S.card := by
        rw [card_insert_of_notMem ha] at hr
        omega
      have hsub1 : S.card + 1 - (r + 1) = S.card - r := by omega
      rw [hsub1]
      have hrhs : ((1 - C (x a) * X) * ∏ i ∈ S, (1 - C (x i) * X)).coeff (r + 1) =
          (∏ i ∈ S, (1 - C (x i) * X)).coeff (r + 1) - x a * (∏ i ∈ S, (1 - C (x i) * X)).coeff r := by
        rw [sub_mul, one_mul, coeff_sub, mul_assoc, coeff_C_mul, mul_comm X, coeff_mul_X]
      rw [hrhs]
      by_cases hrc : r = S.card
      · subst hrc
        simp only [Nat.sub_self]
        have hlhs : ((X - C (x a)) * ∏ i ∈ S, (X - C (x i))).coeff 0 =
            - x a * (∏ i ∈ S, (X - C (x i))).coeff 0 := by
          simp [sub_mul]
        have hdeg_q : (∏ i ∈ S, (1 - C (x i) * X)).natDegree ≤ S.card := by
          have hterm : ∀ i ∈ S, (1 - C (x i) * X).natDegree ≤ 1 := fun i _ =>
            (natDegree_sub_le _ _).trans (by
              simp only [natDegree_one, max_le_iff, zero_le, true_and]
              exact (natDegree_mul_le).trans (by simp [natDegree_C, natDegree_X]))
          calc (∏ i ∈ S, (1 - C (x i) * X)).natDegree
              ≤ ∑ i ∈ S, (1 - C (x i) * X).natDegree := natDegree_prod_le S _
            _ ≤ ∑ _i ∈ S, 1 := Finset.sum_le_sum (f := fun i => (1 - C (x i) * X).natDegree) hterm
            _ = S.card := by simp
        have hq0 : (∏ i ∈ S, (1 - C (x i) * X)).coeff (S.card + 1) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by omega)
        rw [hlhs, hq0, zero_sub, ← ih S.card le_rfl, Nat.sub_self]
        ring
      · have hrlt : r + 1 ≤ S.card := by omega
        have hsub2 : S.card - r = (S.card - (r + 1)) + 1 := by omega
        have hlhs : ((X - C (x a)) * ∏ i ∈ S, (X - C (x i))).coeff (S.card - r) =
            (∏ i ∈ S, (X - C (x i))).coeff (S.card - (r + 1)) -
            x a * (∏ i ∈ S, (X - C (x i))).coeff (S.card - r) := by
          rw [sub_mul, coeff_sub, coeff_C_mul, hsub2, mul_comm X, coeff_mul_X, ← hsub2]
        rw [hlhs, ih (r + 1) hrlt, ih r hrS]

private lemma prod_X_sub_eq_of_power_sums_eq {k p : ℕ} (hp : p.Prime) (hkp : k < p)
    {x y : Fin k → ZMod p}
    (hsum : ∀ j : Fin k, ∑ i : Fin k, (x i) ^ (j.1 + 1) = ∑ i : Fin k, (y i) ^ (j.1 + 1)) :
    (∏ i : Fin k, (X - C (x i))) = ∏ i : Fin k, (X - C (y i)) := by
  have : Fact p.Prime := ⟨hp⟩
  let Qx : (ZMod p)[X] := ∏ i : Fin k, (1 - C (x i) * X)
  let Qy : (ZMod p)[X] := ∏ i : Fin k, (1 - C (y i) * X)
  have hQ_coeff : ∀ r ≤ k, Qx.coeff r = Qy.coeff r := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro hrk
      cases r with
      | zero =>
        have hx0 : Qx.coeff 0 = 1 := by
          simpa [Qx] using (prod_X_sub_coeff_eq_recip x Finset.univ 0 (by simp)).symm.trans (by
            have hmon : (∏ i : Fin k, (X - C (x i))).Monic :=
              Polynomial.monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
            have hdeg : (∏ i : Fin k, (X - C (x i))).natDegree = k := by
              rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
              simp
            simpa [Polynomial.leadingCoeff, hdeg] using hmon.leadingCoeff)
        have hy0 : Qy.coeff 0 = 1 := by
          simpa [Qy] using (prod_X_sub_coeff_eq_recip y Finset.univ 0 (by simp)).symm.trans (by
            have hmon : (∏ i : Fin k, (X - C (y i))).Monic :=
              Polynomial.monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
            have hdeg : (∏ i : Fin k, (X - C (y i))).natDegree = k := by
              rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
              simp
            simpa [Polynomial.leadingCoeff, hdeg] using hmon.leadingCoeff)
        rw [hx0, hy0]
      | succ m =>
        have hdx := newton_deriv_coeff x Finset.univ (m + 1) (by omega)
        have hdy := newton_deriv_coeff y Finset.univ (m + 1) (by omega)
        change Qx.derivative.coeff m = - ∑ j ∈ range (m + 1), Qx.coeff j * ∑ i : Fin k, x i ^ (m + 1 - j) at hdx
        change Qy.derivative.coeff m = - ∑ j ∈ range (m + 1), Qy.coeff j * ∑ i : Fin k, y i ^ (m + 1 - j) at hdy
        have hsum_eq : ∑ j ∈ range (m + 1), Qx.coeff j * ∑ i : Fin k, x i ^ (m + 1 - j) =
            ∑ j ∈ range (m + 1), Qy.coeff j * ∑ i : Fin k, y i ^ (m + 1 - j) := by
          refine sum_congr rfl fun j hj => ?_
          have hjlt : j < m + 1 := mem_range.mp hj
          have h1 : Qx.coeff j = Qy.coeff j := ih j hjlt (by omega)
          have h2 : ∑ i : Fin k, x i ^ (m + 1 - j) = ∑ i : Fin k, y i ^ (m + 1 - j) := by
            have hd : m - j < k := by omega
            have := hsum ⟨m - j, hd⟩
            simpa [show m - j + 1 = m + 1 - j by omega] using this
          rw [h1, h2]
        have hder_eq : Qx.derivative.coeff m = Qy.derivative.coeff m := by rw [hdx, hdy, hsum_eq]
        rw [coeff_derivative, coeff_derivative] at hder_eq
        have hm_ne : ((m + 1 : ℕ) : ZMod p) ≠ 0 := by
          intro h0
          have hdvd : p ∣ m + 1 := (ZMod.natCast_eq_zero_iff (m + 1) p).mp h0
          have hle := Nat.le_of_dvd (by omega) hdvd
          omega
        exact mul_right_cancel₀ hm_ne (by simpa [Nat.cast_add, Nat.cast_one] using hder_eq)
  have hdegx : (∏ i : Fin k, (X - C (x i))).natDegree = k := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
    simp
  have hdegy : (∏ i : Fin k, (X - C (y i))).natDegree = k := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
    simp
  ext d
  by_cases hd : d ≤ k
  · have h1 := prod_X_sub_coeff_eq_recip x Finset.univ (k - d) (by simp)
    have h2 := prod_X_sub_coeff_eq_recip y Finset.univ (k - d) (by simp)
    simp only [card_univ, Fintype.card_fin, Nat.sub_sub_self hd] at h1 h2
    rw [h1, h2]
    exact hQ_coeff (k - d) (Nat.sub_le k d)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

/-- Base step `m = 1`: counting distinct-mod-`p` solutions to power sums mod `p`. -/
private lemma hensel_base_card_le {k p : ℕ} (hp : p.Prime) (hkp : k < p) (c : Fin k → ℤ) :
    ((Finset.univ : Finset (Fin k → Fin p)).filter fun (x : Fin k → Fin p) =>
      Function.Injective x ∧
      (∀ j : Fin k, (p : ℤ) ∣ (∑ i : Fin k, ((x i : ℕ) : ℤ) ^ (j.1 + 1)) - c j)).card
    ≤ k.factorial := by
  have : Fact p.Prime := ⟨hp⟩
  let S := (Finset.univ : Finset (Fin k → Fin p)).filter fun (x : Fin k → Fin p) =>
    Function.Injective x ∧
    (∀ j : Fin k, (p : ℤ) ∣ (∑ i : Fin k, ((x i : ℕ) : ℤ) ^ (j.1 + 1)) - c j)
  by_cases hne : S.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    have hx₀_inj : Function.Injective x₀ := (mem_filter.mp hx₀).2.1
    have hx₀_sum : ∀ j : Fin k, (p : ℤ) ∣ (∑ i : Fin k, ((x₀ i : ℕ) : ℤ) ^ (j.1 + 1)) - c j :=
      (mem_filter.mp hx₀).2.2
    let T : Finset (Fin p) := Finset.univ.image x₀
    have hT_card : T.card = k := by
      rw [card_image_of_injective _ hx₀_inj, card_univ, Fintype.card_fin]
    have hmap_mem : ∀ x ∈ S, ∀ i : Fin k, x i ∈ T := by
      intro x hx i
      have hx_sum := (mem_filter.mp hx).2.2
      have hmod : ∀ j : Fin k,
          ∑ r : Fin k, ((x r : ℕ) : ZMod p) ^ (j.1 + 1) =
          ∑ r : Fin k, ((x₀ r : ℕ) : ZMod p) ^ (j.1 + 1) := by
        intro j
        have hd1 := hx_sum j
        have hd2 := hx₀_sum j
        have hsub : (p : ℤ) ∣ (∑ r : Fin k, ((x r : ℕ) : ℤ) ^ (j.1 + 1)) -
            (∑ r : Fin k, ((x₀ r : ℕ) : ℤ) ^ (j.1 + 1)) := by
          have h1 := dvd_sub hd1 hd2
          have heq : (∑ r : Fin k, ((x r : ℕ) : ℤ) ^ (j.1 + 1)) - c j -
              ((∑ r : Fin k, ((x₀ r : ℕ) : ℤ) ^ (j.1 + 1)) - c j) =
              (∑ r : Fin k, ((x r : ℕ) : ℤ) ^ (j.1 + 1)) -
              (∑ r : Fin k, ((x₀ r : ℕ) : ℤ) ^ (j.1 + 1)) := by ring
          rwa [heq] at h1
        have hz : ((∑ r : Fin k, ((x r : ℕ) : ℤ) ^ (j.1 + 1) -
            ∑ r : Fin k, ((x₀ r : ℕ) : ℤ) ^ (j.1 + 1) : ℤ) : ZMod p) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hsub
        push_cast at hz
        exact sub_eq_zero.mp hz
      have hpoly := prod_X_sub_eq_of_power_sums_eq hp hkp hmod
      have hroot : (∏ r : Fin k, (X - C ((x₀ r : ℕ) : ZMod p))).IsRoot ((x i : ℕ) : ZMod p) := by
        rw [← hpoly, IsRoot, eval_prod]
        exact prod_eq_zero (mem_univ i) (by simp)
      rw [IsRoot, eval_prod, Finset.prod_eq_zero_iff] at hroot
      obtain ⟨r, _, hr⟩ := hroot
      simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hr
      have hval_eq : x i = x₀ r := by
        ext
        have h1 : ((x i : ℕ) : ZMod p).val = ((x₀ r : ℕ) : ZMod p).val := congrArg ZMod.val hr
        rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (x i).2,
          Nat.mod_eq_of_lt (x₀ r).2] at h1
        exact h1
      rw [hval_eq]
      exact mem_image_of_mem x₀ (mem_univ r)
    -- Inject S into (Fin k ↪ T)
    let φ : {x // x ∈ S} → (Fin k ↪ T) := fun x =>
      ⟨fun i => ⟨x.1 i, hmap_mem x.1 x.2 i⟩, fun i j hij =>
        (mem_filter.mp x.2).2.1 (congrArg Subtype.val hij)⟩
    have hφ_inj : Function.Injective φ := by
      intro a b hab
      ext i
      have := congrArg (fun f : Fin k ↪ T => (f i).1) hab
      exact congrArg Fin.val this
    have hcard_le : Fintype.card {x // x ∈ S} ≤ Fintype.card (Fin k ↪ T) :=
      Fintype.card_le_of_injective φ hφ_inj
    rw [Fintype.card_coe, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe,
      hT_card, Nat.descFactorial_self] at hcard_le
    exact hcard_le
  · change S.card ≤ k.factorial
    rw [not_nonempty_iff_eq_empty.mp hne, card_empty]
    exact Nat.zero_le _

/-- Hensel lifting step `m → m + 1` (`1 ≤ m < k`): each mod-`p^m` solution has at most
    `p^m` lifts mod `p^{m+1}`. -/
private lemma hensel_step_card_le {k p m : ℕ} (hm : 1 ≤ m) (hmk : m < k)
    (hp : p.Prime) (hkp : k < p) (c : Fin k → ℤ) :
    ((Finset.univ : Finset (Fin k → Fin (p ^ (m + 1)))).filter fun x =>
      (∀ i j : Fin k, i ≠ j → (x i : ℕ) % p ≠ (x j : ℕ) % p) ∧
      (∀ j : Fin k, ((p : ℤ) ^ min (j.1 + 1) (m + 1)) ∣
        (∑ i : Fin k, ((x i : ℕ) : ℤ) ^ (j.1 + 1)) - c j)).card
    ≤ p ^ m * ((Finset.univ : Finset (Fin k → Fin (p ^ m))).filter fun x =>
      (∀ i j : Fin k, i ≠ j → (x i : ℕ) % p ≠ (x j : ℕ) % p) ∧
      (∀ j : Fin k, ((p : ℤ) ^ min (j.1 + 1) m) ∣
        (∑ i : Fin k, ((x i : ℕ) : ℤ) ^ (j.1 + 1)) - c j)).card := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hpm_pos : 0 < p ^ m := pow_pos hp.pos m
  let S₁ := (Finset.univ : Finset (Fin k → Fin (p ^ (m + 1)))).filter fun x =>
    (∀ i j : Fin k, i ≠ j → (x i : ℕ) % p ≠ (x j : ℕ) % p) ∧
    (∀ j : Fin k, ((p : ℤ) ^ min (j.1 + 1) (m + 1)) ∣
      (∑ i : Fin k, ((x i : ℕ) : ℤ) ^ (j.1 + 1)) - c j)
  let S₀ := (Finset.univ : Finset (Fin k → Fin (p ^ m))).filter fun x =>
    (∀ i j : Fin k, i ≠ j → (x i : ℕ) % p ≠ (x j : ℕ) % p) ∧
    (∀ j : Fin k, ((p : ℤ) ^ min (j.1 + 1) m) ∣
      (∑ i : Fin k, ((x i : ℕ) : ℤ) ^ (j.1 + 1)) - c j)
  let proj : (Fin k → Fin (p ^ (m + 1))) → (Fin k → Fin (p ^ m)) :=
    fun x i => ⟨(x i : ℕ) % (p ^ m), Nat.mod_lt _ hpm_pos⟩
  have hproj_mem : ∀ x ∈ S₁, proj x ∈ S₀ := by
    intro x hx
    obtain ⟨hdist, hcong⟩ := (mem_filter.mp hx).2
    refine mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩
    · intro i j hij
      have hdvd : p ∣ p ^ m := dvd_pow_self p (by omega)
      simp only [proj, Nat.mod_mod_of_dvd _ hdvd]
      exact hdist i j hij
    · intro j
      have hmin : min (j.1 + 1) m ≤ min (j.1 + 1) (m + 1) := by omega
      have h1 : ((p : ℤ) ^ min (j.1 + 1) m) ∣ (∑ i : Fin k, ((x i : ℕ) : ℤ) ^ (j.1 + 1)) - c j :=
        (pow_dvd_pow (p : ℤ) hmin).trans (hcong j)
      have h2 : ((p : ℤ) ^ min (j.1 + 1) m) ∣
          (∑ i : Fin k, ((x i : ℕ) : ℤ) ^ (j.1 + 1)) -
          (∑ i : Fin k, ((proj x i : ℕ) : ℤ) ^ (j.1 + 1)) := by
        rw [← sum_sub_distrib]
        refine dvd_sum fun i _ => ?_
        have hmod : ((p : ℤ) ^ m) ∣ ((x i : ℕ) : ℤ) - ((proj x i : ℕ) : ℤ) := by
          refine ⟨((x i : ℕ) / p ^ m : ℕ), ?_⟩
          have hdm : p ^ m * ((x i : ℕ) / p ^ m) + (x i : ℕ) % p ^ m = (x i : ℕ) :=
            Nat.div_add_mod (x i : ℕ) (p ^ m)
          have hdmZ : (((p ^ m * ((x i : ℕ) / p ^ m) + (x i : ℕ) % p ^ m : ℕ) : ℤ)) =
              ((x i : ℕ) : ℤ) := by exact_mod_cast hdm
          simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at hdmZ
          dsimp only [proj]
          linarith
        exact (pow_dvd_pow (p : ℤ) (min_le_right _ _)).trans
          (hmod.trans (sub_dvd_pow_sub_pow _ _ _))
      have h3 := dvd_sub h1 h2
      have heq : (∑ i : Fin k, ((x i : ℕ) : ℤ) ^ (j.1 + 1)) - c j -
          ((∑ i : Fin k, ((x i : ℕ) : ℤ) ^ (j.1 + 1)) -
           (∑ i : Fin k, ((proj x i : ℕ) : ℤ) ^ (j.1 + 1))) =
          (∑ i : Fin k, ((proj x i : ℕ) : ℤ) ^ (j.1 + 1)) - c j := by ring
      rwa [heq] at h3
  have hfiber : ∀ a ∈ S₀, (S₁.filter fun x => proj x = a).card ≤ p ^ m := by
    intro a ha
    have ha_dist : ∀ i j : Fin k, i ≠ j → (a i : ℕ) % p ≠ (a j : ℕ) % p :=
      (mem_filter.mp ha).2.1
    -- Choose a subset Ifree ⊆ Fin k of size m containing any i with (a i : ℕ) % p = 0
    have hex_free : ∃ Ifree : Finset (Fin k), Ifree.card = m ∧
        ∀ i : Fin k, (a i : ℕ) % p = 0 → i ∈ Ifree := by
      let Z := (Finset.univ : Finset (Fin k)).filter fun i => (a i : ℕ) % p = 0
      have hZ_le : Z.card ≤ 1 := by
        refine Finset.card_le_one.mpr fun i hi j hj => ?_
        by_contra hij
        exact ha_dist i j hij ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)
      obtain ⟨U, hZU, hUcard⟩ := Finset.exists_superset_card_eq (s := Z) (n := m)
        (by omega) (by simp; omega)
      exact ⟨U, hUcard, fun i hi => hZU (mem_filter.mpr ⟨mem_univ i, hi⟩)⟩
    obtain ⟨Ifree, hIfree_card, hIfree_zero⟩ := hex_free
    let Isolve : Finset (Fin k) := Finset.univ \ Ifree
    have hIsolve_card : Isolve.card = k - m := by
      rw [card_sdiff, Finset.inter_univ, card_univ, Fintype.card_fin, hIfree_card]
    -- Map each x in the fiber to the restriction of (x i / p^m) to Ifree
    let ψ : (Fin k → Fin (p ^ (m + 1))) → (Ifree → Fin p) := fun x i =>
      ⟨(x i.1 : ℕ) / p ^ m, by
        have hx : (x i.1 : ℕ) < p ^ m * p := by simpa [pow_succ] using (x i.1).2
        exact Nat.div_lt_of_lt_mul (mul_comm (p ^ m) p ▸ hx)⟩
    have hψ_inj : Set.InjOn ψ (S₁.filter fun x => proj x = a) := by
      intro x hx y hy hxy
      have hx1 : x ∈ S₁ := (mem_filter.mp hx).1
      have hy1 : y ∈ S₁ := (mem_filter.mp hy).1
      have hpx : proj x = a := (mem_filter.mp hx).2
      have hpy : proj y = a := (mem_filter.mp hy).2
      let tx : Fin k → ℕ := fun i => (x i : ℕ) / p ^ m
      let ty : Fin k → ℕ := fun i => (y i : ℕ) / p ^ m
      have htx_lt : ∀ i, tx i < p := fun i => by
        have h1 : (x i : ℕ) < p ^ m * p := by simpa [pow_succ] using (x i).2
        exact Nat.div_lt_of_lt_mul (mul_comm (p ^ m) p ▸ h1)
      have hty_lt : ∀ i, ty i < p := fun i => by
        have h1 : (y i : ℕ) < p ^ m * p := by simpa [pow_succ] using (y i).2
        exact Nat.div_lt_of_lt_mul (mul_comm (p ^ m) p ▸ h1)
      have hx_eq : ∀ i, ((x i : ℕ) : ℤ) = ((a i : ℕ) : ℤ) + (p : ℤ) ^ m * (tx i : ℤ) := by
        intro i
        have hmod : (x i : ℕ) % p ^ m = (a i : ℕ) := congrArg (fun f => (f i : ℕ)) hpx
        have hdm := Nat.div_add_mod (x i : ℕ) (p ^ m)
        rw [hmod] at hdm
        have : ((p ^ m : ℕ) : ℤ) * (tx i : ℕ) + ((a i : ℕ) : ℤ) = ((x i : ℕ) : ℤ) := by
          exact_mod_cast hdm
        push_cast at this
        linarith
      have hy_eq : ∀ i, ((y i : ℕ) : ℤ) = ((a i : ℕ) : ℤ) + (p : ℤ) ^ m * (ty i : ℤ) := by
        intro i
        have hmod : (y i : ℕ) % p ^ m = (a i : ℕ) := congrArg (fun f => (f i : ℕ)) hpy
        have hdm := Nat.div_add_mod (y i : ℕ) (p ^ m)
        rw [hmod] at hdm
        have : ((p ^ m : ℕ) : ℤ) * (ty i : ℕ) + ((a i : ℕ) : ℤ) = ((y i : ℕ) : ℤ) := by
          exact_mod_cast hdm
        push_cast at this
        linarith
      have hfree_eq : ∀ i ∈ Ifree, tx i = ty i := by
        intro i hi
        have := congrArg (fun f : Ifree → Fin p => (f ⟨i, hi⟩).1) hxy
        exact this
      -- Linear system mod p for d_i := (tx i - ty i : ZMod p)
      let d : Fin k → ZMod p := fun i => (tx i : ZMod p) - (ty i : ZMod p)
      have hd_free : ∀ i ∈ Ifree, d i = 0 := fun i hi => by
        simp [d, hfree_eq i hi]
      have hlin : ∀ r : Fin (k - m),
          ∑ i ∈ Isolve, ((a i : ℕ) : ZMod p) ^ (m + r.1) * d i = 0 := by
        intro r
        let j : Fin k := ⟨m + r.1, by omega⟩
        have hmin : min (j.1 + 1) (m + 1) = m + 1 := by dsimp [j]; omega
        have hx_c := (mem_filter.mp hx1).2.2 j
        have hy_c := (mem_filter.mp hy1).2.2 j
        rw [hmin] at hx_c hy_c
        have hdiff_c : ((p : ℤ) ^ (m + 1)) ∣
            ∑ i : Fin k, (((x i : ℕ) : ℤ) ^ (j.1 + 1) - ((y i : ℕ) : ℤ) ^ (j.1 + 1)) := by
          rw [sum_sub_distrib]
          have hsub := dvd_sub hx_c hy_c
          have heq : (∑ i : Fin k, ((x i : ℕ) : ℤ) ^ (j.1 + 1)) - c j -
              ((∑ i : Fin k, ((y i : ℕ) : ℤ) ^ (j.1 + 1)) - c j) =
              (∑ i : Fin k, ((x i : ℕ) : ℤ) ^ (j.1 + 1)) -
              (∑ i : Fin k, ((y i : ℕ) : ℤ) ^ (j.1 + 1)) := by ring
          rwa [heq] at hsub
        have hterm_mod : ∀ i : Fin k, ((p : ℤ) ^ (m + 1)) ∣
            (((x i : ℕ) : ℤ) ^ (j.1 + 1) - ((y i : ℕ) : ℤ) ^ (j.1 + 1)) -
            ((p : ℤ) ^ m) * ((j.1 + 1 : ℤ) * ((a i : ℕ) : ℤ) ^ j.1 * ((tx i : ℤ) - (ty i : ℤ))) := by
          intro i
          have hbin : ∀ u : ℤ, ((p : ℤ) ^ (m + 1)) ∣
              (((a i : ℕ) : ℤ) + (p : ℤ) ^ m * u) ^ (j.1 + 1) -
              (((a i : ℕ) : ℤ) ^ (j.1 + 1) + (j.1 + 1 : ℤ) * ((a i : ℕ) : ℤ) ^ j.1 * ((p : ℤ) ^ m * u)) := by
            intro u
            rw [add_pow]
            have h01 : (∑ t ∈ range (j.1 + 1 + 1),
                  ((a i : ℕ) : ℤ) ^ t * ((p : ℤ) ^ m * u) ^ (j.1 + 1 - t) * ((j.1 + 1).choose t : ℤ)) -
                (((a i : ℕ) : ℤ) ^ (j.1 + 1) + (j.1 + 1 : ℤ) * ((a i : ℕ) : ℤ) ^ j.1 * ((p : ℤ) ^ m * u)) =
                ∑ t ∈ range j.1,
                  ((a i : ℕ) : ℤ) ^ t * ((p : ℤ) ^ m * u) ^ (j.1 + 1 - t) * ((j.1 + 1).choose t : ℤ) := by
              rw [sum_range_succ, sum_range_succ]
              simp
              ring
            rw [h01]
            refine dvd_sum fun t ht => ?_
            have htlt : t < j.1 := mem_range.mp ht
            have hexp : m + 1 ≤ m * (j.1 + 1 - t) := by
              have h2 : 2 ≤ j.1 + 1 - t := by omega
              nlinarith
            have hd1 : ((p : ℤ) ^ (m + 1)) ∣ ((p : ℤ) ^ m) ^ (j.1 + 1 - t) := by
              rw [← pow_mul]
              exact pow_dvd_pow (p : ℤ) hexp
            rw [mul_pow]
            exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hd1 _) _) _
          rw [hx_eq i, hy_eq i]
          have hsub := dvd_sub (hbin (tx i : ℤ)) (hbin (ty i : ℤ))
          have heq : (((a i : ℕ) : ℤ) + (p : ℤ) ^ m * (tx i : ℤ)) ^ (j.1 + 1) -
              (((a i : ℕ) : ℤ) ^ (j.1 + 1) + (j.1 + 1 : ℤ) * ((a i : ℕ) : ℤ) ^ j.1 * ((p : ℤ) ^ m * (tx i : ℤ))) -
              ((((a i : ℕ) : ℤ) + (p : ℤ) ^ m * (ty i : ℤ)) ^ (j.1 + 1) -
              (((a i : ℕ) : ℤ) ^ (j.1 + 1) + (j.1 + 1 : ℤ) * ((a i : ℕ) : ℤ) ^ j.1 * ((p : ℤ) ^ m * (ty i : ℤ)))) =
              (((a i : ℕ) : ℤ) + (p : ℤ) ^ m * (tx i : ℤ)) ^ (j.1 + 1) -
              (((a i : ℕ) : ℤ) + (p : ℤ) ^ m * (ty i : ℤ)) ^ (j.1 + 1) -
              ((p : ℤ) ^ m) * ((j.1 + 1 : ℤ) * ((a i : ℕ) : ℤ) ^ j.1 * ((tx i : ℤ) - (ty i : ℤ))) := by ring
          rwa [heq] at hsub
        have hlinZ : ((p : ℤ) ^ (m + 1)) ∣
            ((p : ℤ) ^ m) * ∑ i : Fin k, ((j.1 + 1 : ℤ) * ((a i : ℕ) : ℤ) ^ j.1 * ((tx i : ℤ) - (ty i : ℤ))) := by
          rw [mul_sum]
          have h1 := dvd_sub hdiff_c (Finset.dvd_sum (s := Finset.univ) fun i _ => hterm_mod i)
          rw [← sum_sub_distrib] at h1
          have heq : ∑ i : Fin k,
              ((((x i : ℕ) : ℤ) ^ (j.1 + 1) - ((y i : ℕ) : ℤ) ^ (j.1 + 1)) -
              ((((x i : ℕ) : ℤ) ^ (j.1 + 1) - ((y i : ℕ) : ℤ) ^ (j.1 + 1)) -
                ((p : ℤ) ^ m) * ((j.1 + 1 : ℤ) * ((a i : ℕ) : ℤ) ^ j.1 * ((tx i : ℤ) - (ty i : ℤ))))) =
              ∑ i : Fin k, ((p : ℤ) ^ m) * ((j.1 + 1 : ℤ) * ((a i : ℕ) : ℤ) ^ j.1 * ((tx i : ℤ) - (ty i : ℤ))) :=
            sum_congr rfl fun i _ => by ring
          rwa [heq] at h1
        have hp_dvd : (p : ℤ) ∣ ∑ i : Fin k, ((j.1 + 1 : ℤ) * ((a i : ℕ) : ℤ) ^ j.1 * ((tx i : ℤ) - (ty i : ℤ))) := by
          rw [pow_succ] at hlinZ
          exact (mul_dvd_mul_iff_left (pow_ne_zero m (Int.natCast_ne_zero.mpr hp.ne_zero))).mp hlinZ
        have hmod0 : ((∑ i : Fin k, ((j.1 + 1 : ℤ) * ((a i : ℕ) : ℤ) ^ j.1 * ((tx i : ℤ) - (ty i : ℤ))) : ℤ) : ZMod p) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hp_dvd
        push_cast at hmod0
        have hj_ne : (((j.1 + 1 : ℕ) : ZMod p)) ≠ 0 := by
          intro h0
          have hdvd := (ZMod.natCast_eq_zero_iff (j.1 + 1) p).mp h0
          have hle := Nat.le_of_dvd (by omega) hdvd
          have : j.1 < k := j.2
          omega
        have hsum_all : ∑ i : Fin k, ((a i : ℕ) : ZMod p) ^ j.1 * d i = 0 := by
          have hfac : (((j.1 + 1 : ℕ) : ZMod p)) * ∑ i : Fin k, ((a i : ℕ) : ZMod p) ^ j.1 * d i = 0 := by
            rw [mul_sum]
            simpa [d, mul_assoc] using hmod0
          exact (mul_eq_zero.mp hfac).resolve_left hj_ne
        have hsplit : ∑ i : Fin k, ((a i : ℕ) : ZMod p) ^ j.1 * d i =
            (∑ i ∈ Isolve, ((a i : ℕ) : ZMod p) ^ j.1 * d i) +
            (∑ i ∈ Ifree, ((a i : ℕ) : ZMod p) ^ j.1 * d i) := by
          rw [← sum_union (disjoint_sdiff_self_left : Disjoint Isolve Ifree)]
          congr 1
          ext i; simp
        have hfree0 : ∑ i ∈ Ifree, ((a i : ℕ) : ZMod p) ^ j.1 * d i = 0 :=
          sum_eq_zero fun i hi => by rw [hd_free i hi, mul_zero]
        rw [hsplit, hfree0, add_zero] at hsum_all
        simpa [j] using hsum_all
      -- Use Vandermonde nonsingularity on Isolve to conclude d i = 0 for all i ∈ Isolve
      let e : Fin (k - m) ≃ Isolve := (Fintype.equivFinOfCardEq (by simp [hIsolve_card])).symm
      let v : Fin (k - m) → ZMod p := fun s => ((a (e s).1 : ℕ) : ZMod p)
      let w : Fin (k - m) → ZMod p := fun s => (v s) ^ m * d (e s).1
      have hv_inj : Function.Injective v := by
        intro s₁ s₂ hs
        by_contra hne
        have hne' : (e s₁).1 ≠ (e s₂).1 := fun h => hne (e.injective (Subtype.ext h))
        have hmod : (a (e s₁).1 : ℕ) % p = (a (e s₂).1 : ℕ) % p := by
          have := congrArg ZMod.val hs
          simpa [v, ZMod.val_natCast] using this
        exact ha_dist _ _ hne' hmod
      have hv_ne0 : ∀ s : Fin (k - m), v s ≠ 0 := by
        intro s h0
        have hmod0 : (a (e s).1 : ℕ) % p = 0 := by
          have := congrArg ZMod.val h0
          simpa [v, ZMod.val_natCast] using this
        have hmem_free : (e s).1 ∈ Ifree := hIfree_zero _ hmod0
        exact (mem_sdiff.mp (e s).2).2 hmem_free
      have hVmul : (Matrix.vandermonde v).transpose *ᵥ w = 0 := by
        ext r
        simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.vandermonde_apply,
          Pi.zero_apply]
        have hreidx : ∑ s : Fin (k - m), v s ^ (r : ℕ) * w s =
            ∑ i ∈ Isolve, ((a i : ℕ) : ZMod p) ^ (m + r.1) * d i := by
          calc ∑ s : Fin (k - m), v s ^ (r : ℕ) * w s
              = ∑ s : Fin (k - m), ((a (e s).1 : ℕ) : ZMod p) ^ (m + r.1) * d (e s).1 :=
                sum_congr rfl fun s _ => by dsimp only [v, w]; rw [pow_add]; ring
            _ = ∑ x : Isolve, ((a x.1 : ℕ) : ZMod p) ^ (m + r.1) * d x.1 :=
                e.sum_comp (fun x : Isolve => ((a x.1 : ℕ) : ZMod p) ^ (m + r.1) * d x.1)
            _ = ∑ i ∈ Isolve, ((a i : ℕ) : ZMod p) ^ (m + r.1) * d i :=
                Finset.sum_coe_sort Isolve (fun i => ((a i : ℕ) : ZMod p) ^ (m + r.1) * d i)
        rw [hreidx]
        exact hlin r
      have hdet_ne : (Matrix.vandermonde v).transpose.det ≠ 0 := by
        rw [Matrix.det_transpose]
        exact Matrix.det_vandermonde_ne_zero_iff.mpr hv_inj
      have hw0 : w = 0 := by
        have hunit : IsUnit (Matrix.vandermonde v).transpose.det := isUnit_iff_ne_zero.mpr hdet_ne
        have := congrArg ((Matrix.vandermonde v).transpose⁻¹ *ᵥ ·) hVmul
        rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec,
          Matrix.mulVec_zero] at this
      have hd_all : ∀ i : Fin k, d i = 0 := by
        intro i
        by_cases hi : i ∈ Ifree
        · exact hd_free i hi
        · have hi' : i ∈ Isolve := mem_sdiff.mpr ⟨mem_univ i, hi⟩
          let s := e.symm ⟨i, hi'⟩
          have hes : (e s).1 = i := by simp [s]
          have hws : w s = 0 := congrFun hw0 s
          dsimp only [w] at hws
          have hds := (mul_eq_zero.mp hws).resolve_left (pow_ne_zero m (hv_ne0 s))
          rwa [hes] at hds
      ext i
      have htxy : tx i = ty i := by
        have hdi : (tx i : ZMod p) = (ty i : ZMod p) := sub_eq_zero.mp (hd_all i)
        have hval := congrArg ZMod.val hdi
        rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (htx_lt i),
          Nat.mod_eq_of_lt (hty_lt i)] at hval
        exact hval
      have hxZ := hx_eq i
      have hyZ := hy_eq i
      rw [htxy] at hxZ
      have : ((x i : ℕ) : ℤ) = ((y i : ℕ) : ℤ) := by linarith
      exact_mod_cast this
    calc (S₁.filter fun x => proj x = a).card
        = ((S₁.filter fun x => proj x = a).image ψ).card :=
          (card_image_of_injOn hψ_inj).symm
      _ ≤ (Finset.univ : Finset (Ifree → Fin p)).card := card_le_card (subset_univ _)
      _ = p ^ m := by simp [hIfree_card]
  calc S₁.card = ∑ a ∈ S₀, (S₁.filter fun x => proj x = a).card := by
        rw [Finset.card_eq_sum_card_fiberwise hproj_mem]
    _ ≤ ∑ _a ∈ S₀, p ^ m := sum_le_sum hfiber
    _ = p ^ m * S₀.card := by simp [mul_comm]

/-- Full Hensel-Vandermonde congruence counting lemma mod `(p, p^2, ..., p^k)`. -/
theorem hensel_vandermonde_card_le {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hkp : k < p)
    (c : Fin k → ℤ) :
    ((Finset.univ : Finset (Fin k → Fin (p ^ k))).filter fun x =>
      (∀ i j : Fin k, i ≠ j → (x i : ℕ) % p ≠ (x j : ℕ) % p) ∧
      (∀ j : Fin k, ((p : ℤ) ^ (j.1 + 1)) ∣
        (∑ i : Fin k, ((x i : ℕ) : ℤ) ^ (j.1 + 1)) - c j)).card
    ≤ k.factorial * p ^ (k * (k - 1) / 2) := by
  have haux : ∀ m : ℕ, 1 ≤ m → m ≤ k →
      ((Finset.univ : Finset (Fin k → Fin (p ^ m))).filter fun x =>
        (∀ i j : Fin k, i ≠ j → (x i : ℕ) % p ≠ (x j : ℕ) % p) ∧
        (∀ j : Fin k, ((p : ℤ) ^ min (j.1 + 1) m) ∣
          (∑ i : Fin k, ((x i : ℕ) : ℤ) ^ (j.1 + 1)) - c j)).card
      ≤ k.factorial * p ^ (m * (m - 1) / 2) := by
    intro m hm hmk
    induction m, hm using Nat.le_induction with
    | base =>
      let e : (Fin k → Fin (p ^ 1)) ≃ (Fin k → Fin p) :=
        Equiv.piCongrRight fun _ => finCongr (pow_one p)
      have hcard_eq :
          ((Finset.univ : Finset (Fin k → Fin (p ^ 1))).filter fun (x : Fin k → Fin (p ^ 1)) =>
            (∀ i j : Fin k, i ≠ j → (x i : ℕ) % p ≠ (x j : ℕ) % p) ∧
            (∀ j : Fin k, ((p : ℤ) ^ min (j.1 + 1) 1) ∣
              (∑ i : Fin k, ((x i : ℕ) : ℤ) ^ (j.1 + 1)) - c j)).card =
          ((Finset.univ : Finset (Fin k → Fin p)).filter fun (x : Fin k → Fin p) =>
            Function.Injective x ∧
            (∀ j : Fin k, (p : ℤ) ∣
              (∑ i : Fin k, ((x i : ℕ) : ℤ) ^ (j.1 + 1)) - c j)).card := by
        refine Finset.card_nbij' (fun x => e x) (fun x => e.symm x) ?_ ?_ ?_ ?_
        · intro x hx
          obtain ⟨hdist, hcong⟩ := (mem_filter.mp hx).2
          refine mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩
          · intro i j hij
            by_contra hne
            have h1 := hdist i j hne
            have h2 : (x i : ℕ) = (x j : ℕ) := by simpa [e] using congrArg Fin.val hij
            exact h1 (by rw [h2])
          · intro j
            have h1 := hcong j
            have hmin : min (j.1 + 1) 1 = 1 := by omega
            rw [hmin, pow_one] at h1
            simpa [e] using h1
        · intro x hx
          obtain ⟨hinj, hcong⟩ := (mem_filter.mp hx).2
          refine mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩
          · intro i j hij
            have h1 : (x i : ℕ) % p = (x i : ℕ) := Nat.mod_eq_of_lt (x i).2
            have h2 : (x j : ℕ) % p = (x j : ℕ) := Nat.mod_eq_of_lt (x j).2
            simpa [e, h1, h2] using fun h => hij (hinj (Fin.ext h))
          · intro j
            have hmin : min (j.1 + 1) 1 = 1 := by omega
            rw [hmin, pow_one]
            simpa [e] using hcong j
        · intro x _; exact e.symm_apply_apply x
        · intro x _; exact e.apply_symm_apply x
      rw [hcard_eq]
      simpa using hensel_base_card_le hp hkp c
    | succ m hm ih =>
      have hstep := hensel_step_card_le hm (by omega) hp hkp c
      have hih := ih (by omega)
      have hexp : m + m * (m - 1) / 2 = (m + 1) * m / 2 := by
        have hsum : 2 * m + m * (m - 1) = (m + 1) * m := by
          cases m with
          | zero => omega
          | succ t => simp; ring
        have h1 : (2 * m + m * (m - 1)) / 2 = m + m * (m - 1) / 2 := by
          rw [Nat.add_div_of_dvd_right (dvd_mul_right 2 m), Nat.mul_div_cancel_left m (by decide)]
        rw [← h1, hsum]
      calc _ ≤ p ^ m * ((Finset.univ : Finset (Fin k → Fin (p ^ m))).filter fun x =>
            (∀ i j : Fin k, i ≠ j → (x i : ℕ) % p ≠ (x j : ℕ) % p) ∧
            (∀ j : Fin k, ((p : ℤ) ^ min (j.1 + 1) m) ∣
              (∑ i : Fin k, ((x i : ℕ) : ℤ) ^ (j.1 + 1)) - c j)).card := hstep
        _ ≤ p ^ m * (k.factorial * p ^ (m * (m - 1) / 2)) := Nat.mul_le_mul_left _ hih
        _ = k.factorial * (p ^ m * p ^ (m * (m - 1) / 2)) := by ring
        _ = k.factorial * p ^ (m + m * (m - 1) / 2) := by rw [← pow_add]
        _ = k.factorial * p ^ ((m + 1) * (m + 1 - 1) / 2) := by rw [hexp, Nat.add_sub_cancel]
  have hfinal := haux k hk le_rfl
  convert hfinal using 2
  ext x
  simp only [mem_filter, mem_univ, true_and]
  refine and_congr_right fun _ => forall_congr' fun j => ?_
  have hmin : min (j.1 + 1) k = j.1 + 1 := Nat.min_eq_left j.2
  rw [hmin]

/-- Version on a box `Fin P` with `P ≤ p ^ k`. -/
theorem hensel_vandermonde_box_card_le {k p P : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hkp : k < p)
    (hP : P ≤ p ^ k) (c : Fin k → ℤ) :
    ((Finset.univ : Finset (Fin k → Fin P)).filter fun x =>
      (∀ i j : Fin k, i ≠ j → (x i : ℕ) % p ≠ (x j : ℕ) % p) ∧
      (∀ j : Fin k, ((p : ℤ) ^ (j.1 + 1)) ∣
        (∑ i : Fin k, ((x i : ℕ) : ℤ) ^ (j.1 + 1)) - c j)).card
    ≤ k.factorial * p ^ (k * (k - 1) / 2) := by
  let emb : (Fin k → Fin P) → (Fin k → Fin (p ^ k)) :=
    fun x i => ⟨(x i : ℕ), lt_of_lt_of_le (x i).2 hP⟩
  have hemb_inj : Function.Injective emb := fun x y hxy => by
    ext i
    exact congrArg (fun f => (f i : ℕ)) hxy
  have hsub :
      (((Finset.univ : Finset (Fin k → Fin P)).filter fun x =>
        (∀ i j : Fin k, i ≠ j → (x i : ℕ) % p ≠ (x j : ℕ) % p) ∧
        (∀ j : Fin k, ((p : ℤ) ^ (j.1 + 1)) ∣
          (∑ i : Fin k, ((x i : ℕ) : ℤ) ^ (j.1 + 1)) - c j)).image emb) ⊆
      ((Finset.univ : Finset (Fin k → Fin (p ^ k))).filter fun x =>
        (∀ i j : Fin k, i ≠ j → (x i : ℕ) % p ≠ (x j : ℕ) % p) ∧
        (∀ j : Fin k, ((p : ℤ) ^ (j.1 + 1)) ∣
          (∑ i : Fin k, ((x i : ℕ) : ℤ) ^ (j.1 + 1)) - c j)) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    simpa [emb] using hx
  calc _ = (((Finset.univ : Finset (Fin k → Fin P)).filter fun x =>
          (∀ i j : Fin k, i ≠ j → (x i : ℕ) % p ≠ (x j : ℕ) % p) ∧
          (∀ j : Fin k, ((p : ℤ) ^ (j.1 + 1)) ∣
            (∑ i : Fin k, ((x i : ℕ) : ℤ) ^ (j.1 + 1)) - c j)).image emb).card :=
        (card_image_of_injective _ hemb_inj).symm
    _ ≤ _ := card_le_card hsub
    _ ≤ k.factorial * p ^ (k * (k - 1) / 2) := hensel_vandermonde_card_le hk hp hkp c

end OMA.Erdos377M1


/-
Vinogradov's Mean Value Theorem via discrete orthogonality and elementary p-adic recursion.
-/

namespace OMA.Erdos377M2

open Finset Real Complex
open scoped BigOperators

noncomputable section

/-- Additive character `e(x) = exp(2π i x)`. -/
def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

lemma e_zero : e 0 = 1 := by simp [e]

lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  simp only [e, Complex.ofReal_add, mul_add, Complex.exp_add]

lemma e_neg (x : ℝ) : e (-x) = (e x)⁻¹ := by
  simp only [e, Complex.ofReal_neg, mul_neg, Complex.exp_neg]

lemma e_sub (x y : ℝ) : e (x - y) = e x * (e y)⁻¹ := by
  rw [sub_eq_add_neg, e_add, e_neg]

lemma e_star (x : ℝ) : star (e x) = e (-x) := by
  simp only [e, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, Complex.ofReal_neg]
  ring

lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  dsimp only [e]
  have h : (2 : ℂ) * ↑Real.pi * Complex.I * ↑x = ↑(2 * Real.pi * x) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma e_int (m : ℤ) : e (m : ℝ) = 1 := by
  dsimp only [e]
  have h : (2 : ℂ) * ↑Real.pi * Complex.I * ↑(m : ℝ) = ↑m * (2 * ↑Real.pi * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

lemma e_pow_nat (x : ℝ) (n : ℕ) : e x ^ n = e (n * x) := by
  dsimp only [e]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast; ring

lemma e_eq_one_iff_exists_int (x : ℝ) : e x = 1 ↔ ∃ k : ℤ, x = k := by
  dsimp only [e]
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h2pi : (2 : ℂ) * ↑Real.pi * Complex.I ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h1 : (x : ℂ) = (k : ℂ) := by
      apply mul_left_cancel₀ h2pi
      simpa [mul_comm, mul_left_comm, mul_assoc] using hk
    exact Complex.ofReal_injective (by simpa using h1)
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    push_cast; ring

/-- 1D discrete orthogonality over `Fin M`. -/
lemma sum_e_div_eq_ite {M : ℕ} (hM : 1 ≤ M) (m : ℤ) :
    (∑ a : Fin M, e ((((a : ℕ) : ℝ) * (m : ℝ)) / (M : ℝ))) =
      if (M : ℤ) ∣ m then (M : ℂ) else 0 := by
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  let ω : ℂ := e ((m : ℝ) / (M : ℝ))
  have hterm : ∀ a : Fin M, e ((((a : ℕ) : ℝ) * (m : ℝ)) / (M : ℝ)) = ω ^ (a : ℕ) := fun a => by
    dsimp only [ω]
    rw [e_pow_nat]
    congr 1; ring
  simp_rw [hterm, Fin.sum_univ_eq_sum_range (fun a => ω ^ a)]
  split_ifs with hd
  · obtain ⟨k, rfl⟩ := hd
    have hω1 : ω = 1 := by
      dsimp only [ω]
      have hdiv : (((M : ℤ) * k : ℤ) : ℝ) / (M : ℝ) = (k : ℝ) := by
        push_cast; field_simp [hM0]
      rw [hdiv, e_int]
    simp [hω1]
  · have hωne : ω ≠ 1 := by
      intro h1
      rw [e_eq_one_iff_exists_int] at h1
      obtain ⟨k, hk⟩ := h1
      have hmk : (m : ℝ) = (M : ℝ) * (k : ℝ) := by
        have := (div_eq_iff hM0).mp hk
        linarith
      have hmkZ : m = (M : ℤ) * k := by exact_mod_cast hmk
      exact hd ⟨k, hmkZ⟩
    have hωM : ω ^ M = 1 := by
      dsimp only [ω]
      rw [e_pow_nat]
      have hmul : (M : ℝ) * ((m : ℝ) / (M : ℝ)) = (m : ℝ) := mul_div_cancel₀ _ hM0
      rw [hmul, e_int]
    have hgeom : (ω - 1) * ∑ a ∈ range M, ω ^ a = ω ^ M - 1 := by
      rw [mul_comm, geom_sum_mul]
    rw [hωM, sub_self] at hgeom
    exact (mul_eq_zero.mp hgeom).resolve_left (sub_ne_zero.mpr hωne)

/-- Multi-dimensional discrete orthogonality over `∀ j : Fin k, Fin (M j)`. -/
lemma sum_prod_e_div_eq_ite {k : ℕ} (M : Fin k → ℕ) (hM : ∀ j, 1 ≤ M j) (m : Fin k → ℤ) :
    (∑ a : ∀ j : Fin k, Fin (M j),
        ∏ j : Fin k, e ((((a j : ℕ) : ℝ) * (m j : ℝ)) / (M j : ℝ))) =
      if ∀ j : Fin k, (M j : ℤ) ∣ m j then (∏ j : Fin k, (M j : ℂ)) else 0 := by
  classical
  rw [← Fintype.prod_sum (fun j (a : Fin (M j)) => e ((((a : ℕ) : ℝ) * (m j : ℝ)) / (M j : ℝ)))]
  simp_rw [sum_e_div_eq_ite (hM _)]
  split_ifs with hall
  · refine prod_congr rfl fun j _ => ?_
    simp [hall j]
  · push Not at hall
    obtain ⟨j₀, hj₀⟩ := hall
    exact prod_eq_zero (mem_univ j₀) (by simp [hj₀])

/-- Discrete Weyl character `x ↦ ∏ j, e(a_j * x^{j+1} / M_j)`. -/
def weylChar (k : ℕ) (M : Fin k → ℕ) (a : ∀ j : Fin k, Fin (M j)) (x : ℤ) : ℂ :=
  ∏ j : Fin k, e ((((a j : ℕ) : ℝ) * ((x ^ (j.1 + 1) : ℤ) : ℝ)) / (M j : ℝ))

lemma norm_weylChar (k : ℕ) (M : Fin k → ℕ) (a : ∀ j : Fin k, Fin (M j)) (x : ℤ) :
    ‖weylChar k M a x‖ = 1 := by
  simp [weylChar, norm_e]

/-- Generalized Parseval identity for a finite set `A` of `s`-tuples of integers. -/
lemma parseval_tuples {s k : ℕ} (M : Fin k → ℕ) (hM : ∀ j, 1 ≤ M j)
    (A : Finset (Fin s → ℤ))
    (hfit : ∀ x ∈ A, ∀ y ∈ A, ∀ j : Fin k,
      |(∑ i : Fin s, (x i) ^ (j.1 + 1)) - (∑ i : Fin s, (y i) ^ (j.1 + 1))| < (M j : ℤ)) :
    (∏ j : Fin k, (M j : ℝ)) *
      (((A ×ˢ A).filter fun xy =>
        ∀ j : Fin k, ∑ i : Fin s, (xy.1 i) ^ (j.1 + 1) = ∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)).card : ℝ) =
      ∑ a : ∀ j : Fin k, Fin (M j),
        ‖∑ x ∈ A, ∏ i : Fin s, weylChar k M a (x i)‖ ^ 2 := by
  classical
  have hC : ((∏ j : Fin k, (M j : ℝ)) *
      (((A ×ˢ A).filter fun xy =>
        ∀ j : Fin k, ∑ i : Fin s, (xy.1 i) ^ (j.1 + 1) = ∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)).card : ℝ) : ℂ) =
      ∑ a : ∀ j : Fin k, Fin (M j),
        ((‖∑ x ∈ A, ∏ i : Fin s, weylChar k M a (x i)‖ ^ 2 : ℝ) : ℂ) := by
    have hnorm_sq : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := fun z => by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [hnorm_sq]
    have hexpand : ∀ a : ∀ j : Fin k, Fin (M j),
        (∑ x ∈ A, ∏ i : Fin s, weylChar k M a (x i)) *
        star (∑ y ∈ A, ∏ i : Fin s, weylChar k M a (y i)) =
        ∑ xy ∈ A ×ˢ A, ∏ j : Fin k,
          e ((((a j : ℕ) : ℝ) * (((∑ i : Fin s, (xy.1 i) ^ (j.1 + 1)) -
            (∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)) : ℤ) : ℝ)) / (M j : ℝ)) := by
      intro a
      rw [star_sum, sum_mul_sum, ← Finset.sum_product']
      refine sum_congr rfl fun xy _ => ?_
      have hprod1 : ∏ i : Fin s, weylChar k M a (xy.1 i) =
          ∏ j : Fin k, e ((((a j : ℕ) : ℝ) * ((∑ i : Fin s, (xy.1 i) ^ (j.1 + 1) : ℤ) : ℝ)) / (M j : ℝ)) := by
        dsimp only [weylChar]
        rw [Finset.prod_comm]
        refine prod_congr rfl fun j _ => ?_
        have hsum_e : ∀ (S : Finset (Fin s)) (f : Fin s → ℝ),
            ∏ i ∈ S, e (f i) = e (∑ i ∈ S, f i) := fun S f => by
          induction S using Finset.induction_on with
          | empty => simp [e_zero]
          | @insert u T hu ih => rw [prod_insert hu, sum_insert hu, ih, e_add]
        rw [hsum_e]
        congr 1
        push_cast
        rw [Finset.mul_sum, Finset.sum_div]
      have hprod2 : star (∏ i : Fin s, weylChar k M a (xy.2 i)) =
          ∏ j : Fin k, e (-((((a j : ℕ) : ℝ) * ((∑ i : Fin s, (xy.2 i) ^ (j.1 + 1) : ℤ) : ℝ)) / (M j : ℝ))) := by
        have hprod1' : ∏ i : Fin s, weylChar k M a (xy.2 i) =
            ∏ j : Fin k, e ((((a j : ℕ) : ℝ) * ((∑ i : Fin s, (xy.2 i) ^ (j.1 + 1) : ℤ) : ℝ)) / (M j : ℝ)) := by
          dsimp only [weylChar]
          rw [Finset.prod_comm]
          refine prod_congr rfl fun j _ => ?_
          have hsum_e : ∀ (S : Finset (Fin s)) (f : Fin s → ℝ),
              ∏ i ∈ S, e (f i) = e (∑ i ∈ S, f i) := fun S f => by
            induction S using Finset.induction_on with
            | empty => simp [e_zero]
            | @insert u T hu ih => rw [prod_insert hu, sum_insert hu, ih, e_add]
          rw [hsum_e]
          congr 1
          push_cast
          rw [Finset.mul_sum, Finset.sum_div]
        rw [hprod1', star_prod]
        refine prod_congr rfl fun j _ => e_star _
      rw [hprod1, hprod2, ← prod_mul_distrib]
      refine prod_congr rfl fun j _ => ?_
      rw [← e_add]
      congr 1
      push_cast; ring
    simp_rw [hexpand]
    rw [Finset.sum_comm]
    simp_rw [sum_prod_e_div_eq_ite M hM]
    have hiff : ∀ xy ∈ A ×ˢ A,
        (∀ j : Fin k, (M j : ℤ) ∣ (∑ i : Fin s, (xy.1 i) ^ (j.1 + 1)) - (∑ i : Fin s, (xy.2 i) ^ (j.1 + 1))) ↔
        (∀ j : Fin k, ∑ i : Fin s, (xy.1 i) ^ (j.1 + 1) = ∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)) := by
      intro xy hxy
      obtain ⟨hx, hy⟩ := mem_product.mp hxy
      refine forall_congr' fun j => ⟨fun hd => ?_, fun heq => by rw [heq, sub_self]; exact dvd_zero _⟩
      have hlt := hfit xy.1 hx xy.2 hy j
      have h0 : (∑ i : Fin s, (xy.1 i) ^ (j.1 + 1)) - (∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)) = 0 :=
        Int.eq_zero_of_abs_lt_dvd hd hlt
      exact sub_eq_zero.mp h0
    have hsum_eq : ∑ xy ∈ A ×ˢ A, (if ∀ j : Fin k, (M j : ℤ) ∣
          (∑ i : Fin s, (xy.1 i) ^ (j.1 + 1)) - (∑ i : Fin s, (xy.2 i) ^ (j.1 + 1))
          then (∏ j : Fin k, (M j : ℂ)) else 0) =
        ∑ xy ∈ A ×ˢ A, (if ∀ j : Fin k,
          ∑ i : Fin s, (xy.1 i) ^ (j.1 + 1) = ∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)
          then (∏ j : Fin k, (M j : ℂ)) else 0) :=
      sum_congr rfl fun xy hxy => by simp [hiff xy hxy]
    rw [hsum_eq, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    push_cast; rfl
  exact Complex.ofReal_injective (by simpa [Complex.ofReal_sum] using hC)

/-- Vinogradov's mean value `J(s, k, P)`: number of `2s`-tuples in `[0, P)` with matching
    power sums of degrees `1, ..., k`. -/
def J (s k P : ℕ) : ℕ :=
  ((Finset.univ : Finset ((Fin s → Fin P) × (Fin s → Fin P))).filter fun xy =>
    ∀ j : Fin k, ∑ i : Fin s, ((xy.1 i : ℕ) : ℤ) ^ (j.1 + 1) =
      ∑ i : Fin s, ((xy.2 i : ℕ) : ℤ) ^ (j.1 + 1)).card

lemma J_triv (s k P : ℕ) : J s k P ≤ P ^ (2 * s) := by
  calc J s k P ≤ (Finset.univ : Finset ((Fin s → Fin P) × (Fin s → Fin P))).card :=
        card_le_card (filter_subset _ _)
    _ = P ^ s * P ^ s := by simp [Fintype.card_prod]
    _ = P ^ (2 * s) := by rw [← pow_add, two_mul]

lemma J_mono {s k P Q : ℕ} (hPQ : P ≤ Q) : J s k P ≤ J s k Q := by
  let emb : ((Fin s → Fin P) × (Fin s → Fin P)) → ((Fin s → Fin Q) × (Fin s → Fin Q)) :=
    fun xy => (fun i => ⟨(xy.1 i : ℕ), lt_of_lt_of_le (xy.1 i).2 hPQ⟩,
               fun i => ⟨(xy.2 i : ℕ), lt_of_lt_of_le (xy.2 i).2 hPQ⟩)
  have hemb_inj : Function.Injective emb := fun a b hab => by
    ext i
    · exact congrArg (fun p => (p.1 i : ℕ)) hab
    · exact congrArg (fun p => (p.2 i : ℕ)) hab
  calc J s k P = ((((Finset.univ : Finset ((Fin s → Fin P) × (Fin s → Fin P))).filter fun xy =>
          ∀ j : Fin k, ∑ i : Fin s, ((xy.1 i : ℕ) : ℤ) ^ (j.1 + 1) =
            ∑ i : Fin s, ((xy.2 i : ℕ) : ℤ) ^ (j.1 + 1)).image emb).card) :=
        (card_image_of_injective _ hemb_inj).symm
    _ ≤ J s k Q := card_le_card fun z hz => by
        obtain ⟨xy, hxy, rfl⟩ := mem_image.mp hz
        simpa [emb] using hxy

/-- Shift invariance of power sums of degrees `1, ..., k`. -/
lemma power_sums_shift_iff {s k : ℕ} (x y : Fin s → ℤ) (c : ℤ) :
    (∀ j : Fin k, ∑ i : Fin s, (x i + c) ^ (j.1 + 1) = ∑ i : Fin s, (y i + c) ^ (j.1 + 1)) ↔
    (∀ j : Fin k, ∑ i : Fin s, (x i) ^ (j.1 + 1) = ∑ i : Fin s, (y i) ^ (j.1 + 1)) := by
  have himp : ∀ (a b : Fin s → ℤ) (d : ℤ),
      (∀ j : Fin k, ∑ i : Fin s, (a i) ^ (j.1 + 1) = ∑ i : Fin s, (b i) ^ (j.1 + 1)) →
      (∀ j : Fin k, ∑ i : Fin s, (a i + d) ^ (j.1 + 1) = ∑ i : Fin s, (b i + d) ^ (j.1 + 1)) := by
    intro a b d h j
    simp_rw [add_pow]
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
    refine sum_congr rfl fun r hr => ?_
    have hrle : r ≤ j.1 + 1 := Nat.lt_succ_iff.mp (mem_range.mp hr)
    cases r with
    | zero => simp
    | succ r =>
      have h1 : ∀ u : Fin s → ℤ,
          ∑ i : Fin s, (u i) ^ (r + 1) * d ^ (j.1 + 1 - (r + 1)) * ((j.1 + 1).choose (r + 1) : ℤ) =
          (∑ i : Fin s, (u i) ^ (r + 1)) * (d ^ (j.1 + 1 - (r + 1)) * ((j.1 + 1).choose (r + 1) : ℤ)) :=
        fun u => by rw [Finset.sum_mul]; refine sum_congr rfl fun _ _ => by ring
      rw [h1 a, h1 b, h ⟨r, by omega⟩]
  refine ⟨fun h => ?_, himp x y c⟩
  have := himp (fun i => x i + c) (fun i => y i + c) (-c) h
  simpa [add_neg_cancel_right] using this

/-- Shifted-box Hensel counting lemma: for `P ≤ p^k`, `r < p`, and fixed `c : Fin k → ℤ`,
    the number of `y : Fin k → Fin P` pairwise distinct mod `p` with
    `p^{j+1} ∣ ∑ (y_i - r)^{j+1} - c j` for all `j < k` is at most `k! * p^{k(k-1)/2}`. -/
lemma hensel_shifted_box_card_le {k p P r : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hkp : k < p)
    (hP : P ≤ p ^ k) (hr : r < p) (c : Fin k → ℤ) :
    ((Finset.univ : Finset (Fin k → Fin P)).filter fun y =>
      (∀ i j : Fin k, i ≠ j → (y i : ℕ) % p ≠ (y j : ℕ) % p) ∧
      (∀ j : Fin k, ((p : ℤ) ^ (j.1 + 1)) ∣
        (∑ i : Fin k, (((y i : ℕ) : ℤ) - (r : ℤ)) ^ (j.1 + 1)) - c j)).card
    ≤ k.factorial * p ^ (k * (k - 1) / 2) := by
  have hpk_pos : 0 < p ^ k := pow_pos hp.pos k
  have hr_le : r ≤ p ^ k := le_trans hr.le (Nat.le_self_pow (by omega) p)
  let emb : (Fin k → Fin P) → (Fin k → Fin (p ^ k)) :=
    fun y i => ⟨((y i : ℕ) + (p ^ k - r)) % p ^ k, Nat.mod_lt _ hpk_pos⟩
  have hemb_inj : Function.Injective emb := by
    intro y₁ y₂ h
    ext i
    have h1 : ((y₁ i : ℕ) + (p ^ k - r)) % p ^ k = ((y₂ i : ℕ) + (p ^ k - r)) % p ^ k :=
      congrArg (fun f => (f i : ℕ)) h
    have hy1 : (y₁ i : ℕ) < p ^ k := lt_of_lt_of_le (y₁ i).2 hP
    have hy2 : (y₂ i : ℕ) < p ^ k := lt_of_lt_of_le (y₂ i).2 hP
    have hmod : ((y₁ i : ℕ) : ZMod (p ^ k)) = ((y₂ i : ℕ) : ZMod (p ^ k)) := by
      have h2 : (((y₁ i : ℕ) + (p ^ k - r) : ℕ) : ZMod (p ^ k)) =
          (((y₂ i : ℕ) + (p ^ k - r) : ℕ) : ZMod (p ^ k)) := by
        rw [ZMod.natCast_eq_natCast_iff']
        exact h1
      push_cast at h2
      exact add_right_cancel h2
    have hval := congrArg ZMod.val hmod
    have : NeZero (p ^ k) := ⟨hpk_pos.ne'⟩
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hy1, Nat.mod_eq_of_lt hy2] at hval
    exact hval
  have hsub :
      (((Finset.univ : Finset (Fin k → Fin P)).filter fun y =>
        (∀ i j : Fin k, i ≠ j → (y i : ℕ) % p ≠ (y j : ℕ) % p) ∧
        (∀ j : Fin k, ((p : ℤ) ^ (j.1 + 1)) ∣
          (∑ i : Fin k, (((y i : ℕ) : ℤ) - (r : ℤ)) ^ (j.1 + 1)) - c j)).image emb) ⊆
      ((Finset.univ : Finset (Fin k → Fin (p ^ k))).filter fun x =>
        (∀ i j : Fin k, i ≠ j → (x i : ℕ) % p ≠ (x j : ℕ) % p) ∧
        (∀ j : Fin k, ((p : ℤ) ^ (j.1 + 1)) ∣
          (∑ i : Fin k, ((x i : ℕ) : ℤ) ^ (j.1 + 1)) - c j)) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    obtain ⟨hdist, hcong⟩ := (mem_filter.mp hy).2
    have hpdvd : p ∣ p ^ k := dvd_pow_self p (by omega)
    refine mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩
    · intro i j hij heq
      dsimp only [emb] at heq
      rw [Nat.mod_mod_of_dvd _ hpdvd, Nat.mod_mod_of_dvd _ hpdvd] at heq
      have h1 : (((y i : ℕ) + (p ^ k - r) : ℕ) : ZMod p) =
          (((y j : ℕ) + (p ^ k - r) : ℕ) : ZMod p) :=
        (ZMod.natCast_eq_natCast_iff' _ _ p).mpr heq
      push_cast at h1
      have h2 : ((y i : ℕ) : ZMod p) = ((y j : ℕ) : ZMod p) := add_right_cancel h1
      exact hdist i j hij ((ZMod.natCast_eq_natCast_iff' _ _ p).mp h2)
    · intro j
      have hd_base : ∀ i : Fin k,
          ((p : ℤ) ^ k) ∣ ((emb y i : ℕ) : ℤ) - (((y i : ℕ) : ℤ) - (r : ℤ)) := by
        intro i
        dsimp only [emb]
        have hdm := Nat.div_add_mod ((y i : ℕ) + (p ^ k - r)) (p ^ k)
        have hdmZ : (((p ^ k * (((y i : ℕ) + (p ^ k - r)) / p ^ k) +
            ((y i : ℕ) + (p ^ k - r)) % p ^ k : ℕ) : ℤ)) =
            (((y i : ℕ) + (p ^ k - r) : ℕ) : ℤ) := by exact_mod_cast hdm
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hr_le] at hdmZ
        refine ⟨1 - ((((y i : ℕ) + (p ^ k - r)) / p ^ k : ℕ) : ℤ), ?_⟩
        linarith
      have hdiff : ((p : ℤ) ^ (j.1 + 1)) ∣
          (∑ i : Fin k, ((emb y i : ℕ) : ℤ) ^ (j.1 + 1)) -
          (∑ i : Fin k, (((y i : ℕ) : ℤ) - (r : ℤ)) ^ (j.1 + 1)) := by
        rw [← sum_sub_distrib]
        refine dvd_sum fun i _ => ?_
        exact (pow_dvd_pow (p : ℤ) j.2).trans
          ((hd_base i).trans (sub_dvd_pow_sub_pow _ _ _))
      have hadd := dvd_add hdiff (hcong j)
      have heq : (∑ i : Fin k, ((emb y i : ℕ) : ℤ) ^ (j.1 + 1)) -
          (∑ i : Fin k, (((y i : ℕ) : ℤ) - (r : ℤ)) ^ (j.1 + 1)) +
          ((∑ i : Fin k, (((y i : ℕ) : ℤ) - (r : ℤ)) ^ (j.1 + 1)) - c j) =
          (∑ i : Fin k, ((emb y i : ℕ) : ℤ) ^ (j.1 + 1)) - c j := by ring
      rwa [heq] at hadd
  calc _ = ((((Finset.univ : Finset (Fin k → Fin P)).filter fun y =>
          (∀ i j : Fin k, i ≠ j → (y i : ℕ) % p ≠ (y j : ℕ) % p) ∧
          (∀ j : Fin k, ((p : ℤ) ^ (j.1 + 1)) ∣
            (∑ i : Fin k, (((y i : ℕ) : ℤ) - (r : ℤ)) ^ (j.1 + 1)) - c j)).image emb).card) :=
        (card_image_of_injective _ hemb_inj).symm
    _ ≤ _ := card_le_card hsub
    _ ≤ k.factorial * p ^ (k * (k - 1) / 2) := OMA.Erdos377M1.hensel_vandermonde_card_le hk hp hkp c

/-- Number of solutions to `∑ u_i^{j+1} - ∑ v_i^{j+1} = c j` is at most `J s k P`. -/
lemma card_shifted_solutions_le_J {s k P : ℕ} (c : Fin k → ℤ) :
    ((Finset.univ : Finset ((Fin s → Fin P) × (Fin s → Fin P))).filter fun uv =>
      ∀ j : Fin k, (∑ i : Fin s, ((uv.1 i : ℕ) : ℤ) ^ (j.1 + 1)) -
        (∑ i : Fin s, ((uv.2 i : ℕ) : ℤ) ^ (j.1 + 1)) = c j).card ≤ J s k P := by
  classical
  let M : Fin k → ℕ := fun j => 2 * s * P ^ (j.1 + 1) + (Int.natAbs (c j)) + 2
  have hM : ∀ j, 1 ≤ M j := fun j => by dsimp [M]; omega
  let S : Finset (Fin s → ℤ) :=
    (Finset.univ : Finset (Fin s → Fin P)).image fun x i => ((x i : ℕ) : ℤ)
  have hS_inj : Function.Injective (fun (x : Fin s → Fin P) (i : Fin s) => ((x i : ℕ) : ℤ)) := by
    intro x y h
    ext i
    have := congrFun h i
    dsimp only at this
    exact_mod_cast this
  have hfit_c : ∀ x ∈ S, ∀ y ∈ S, ∀ j : Fin k,
      |(∑ i : Fin s, (x i) ^ (j.1 + 1)) - (∑ i : Fin s, (y i) ^ (j.1 + 1)) - c j| < (M j : ℤ) := by
    intro x hx y hy j
    obtain ⟨x₀, _, rfl⟩ := mem_image.mp hx
    obtain ⟨y₀, _, rfl⟩ := mem_image.mp hy
    have hbd : ∀ z : Fin s → Fin P,
        |∑ i : Fin s, ((z i : ℕ) : ℤ) ^ (j.1 + 1)| ≤ (s : ℤ) * (P : ℤ) ^ (j.1 + 1) := by
      intro z
      calc |∑ i : Fin s, ((z i : ℕ) : ℤ) ^ (j.1 + 1)|
          ≤ ∑ i : Fin s, |((z i : ℕ) : ℤ) ^ (j.1 + 1)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin s, (P : ℤ) ^ (j.1 + 1) := sum_le_sum fun i _ => by
            rw [abs_of_nonneg (by positivity)]
            exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast (z i).2.le) _
        _ = (s : ℤ) * (P : ℤ) ^ (j.1 + 1) := by simp
    have h1 := abs_sub (∑ i : Fin s, ((x₀ i : ℕ) : ℤ) ^ (j.1 + 1) -
        ∑ i : Fin s, ((y₀ i : ℕ) : ℤ) ^ (j.1 + 1)) (c j)
    have h2 := abs_sub (∑ i : Fin s, ((x₀ i : ℕ) : ℤ) ^ (j.1 + 1))
        (∑ i : Fin s, ((y₀ i : ℕ) : ℤ) ^ (j.1 + 1))
    have hc_abs : |c j| = (Int.natAbs (c j) : ℤ) := Int.abs_eq_natAbs (c j)
    have h3 : (M j : ℤ) = 2 * (s : ℤ) * (P : ℤ) ^ (j.1 + 1) + (Int.natAbs (c j) : ℤ) + 2 := by
      simp [M]
    linarith [hbd x₀, hbd y₀]
  have hfit0 : ∀ x ∈ S, ∀ y ∈ S, ∀ j : Fin k,
      |(∑ i : Fin s, (x i) ^ (j.1 + 1)) - (∑ i : Fin s, (y i) ^ (j.1 + 1))| < (M j : ℤ) := by
    intro x hx y hy j
    have h1 := hfit_c x hx y hy j
    have hc_abs : |c j| = (Int.natAbs (c j) : ℤ) := Int.abs_eq_natAbs (c j)
    obtain ⟨x₀, _, rfl⟩ := mem_image.mp hx
    obtain ⟨y₀, _, rfl⟩ := mem_image.mp hy
    have hbd : ∀ z : Fin s → Fin P,
        |∑ i : Fin s, ((z i : ℕ) : ℤ) ^ (j.1 + 1)| ≤ (s : ℤ) * (P : ℤ) ^ (j.1 + 1) := by
      intro z
      calc |∑ i : Fin s, ((z i : ℕ) : ℤ) ^ (j.1 + 1)|
          ≤ ∑ i : Fin s, |((z i : ℕ) : ℤ) ^ (j.1 + 1)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin s, (P : ℤ) ^ (j.1 + 1) := sum_le_sum fun i _ => by
            rw [abs_of_nonneg (by positivity)]
            exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast (z i).2.le) _
        _ = (s : ℤ) * (P : ℤ) ^ (j.1 + 1) := by simp
    have h2 := abs_sub (∑ i : Fin s, ((x₀ i : ℕ) : ℤ) ^ (j.1 + 1))
        (∑ i : Fin s, ((y₀ i : ℕ) : ℤ) ^ (j.1 + 1))
    have h3 : (M j : ℤ) = 2 * (s : ℤ) * (P : ℤ) ^ (j.1 + 1) + (Int.natAbs (c j) : ℤ) + 2 := by
      simp [M]
    linarith [hbd x₀, hbd y₀, Nat.cast_nonneg (α := ℤ) (Int.natAbs (c j))]
  -- Express shifted solution count via discrete orthogonality and take norm
  let N_c : ℕ := ((Finset.univ : Finset ((Fin s → Fin P) × (Fin s → Fin P))).filter fun uv =>
      ∀ j : Fin k, (∑ i : Fin s, ((uv.1 i : ℕ) : ℤ) ^ (j.1 + 1)) -
        (∑ i : Fin s, ((uv.2 i : ℕ) : ℤ) ^ (j.1 + 1)) = c j).card
  let N_S_c : ℕ := ((S ×ˢ S).filter fun xy =>
      ∀ j : Fin k, (∑ i : Fin s, (xy.1 i) ^ (j.1 + 1)) -
        (∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)) = c j).card
  have hN_eq : N_c = N_S_c := by
    let f : ((Fin s → Fin P) × (Fin s → Fin P)) → ((Fin s → ℤ) × (Fin s → ℤ)) :=
      fun uv => (fun i => ((uv.1 i : ℕ) : ℤ), fun i => ((uv.2 i : ℕ) : ℤ))
    have hf_inj : Function.Injective f := fun a b h =>
      Prod.ext (hS_inj (congrArg Prod.fst h)) (hS_inj (congrArg Prod.snd h))
    have himg : (((Finset.univ : Finset ((Fin s → Fin P) × (Fin s → Fin P))).filter fun uv =>
        ∀ j : Fin k, (∑ i : Fin s, ((uv.1 i : ℕ) : ℤ) ^ (j.1 + 1)) -
          (∑ i : Fin s, ((uv.2 i : ℕ) : ℤ) ^ (j.1 + 1)) = c j).image f) =
        ((S ×ˢ S).filter fun xy =>
          ∀ j : Fin k, (∑ i : Fin s, (xy.1 i) ^ (j.1 + 1)) -
            (∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)) = c j) := by
      ext ⟨x, y⟩
      simp only [mem_image, mem_filter, mem_univ, true_and, mem_product, S]
      constructor
      · rintro ⟨uv, huv, hfeq⟩
        have hx : (fun i => ((uv.1 i : ℕ) : ℤ)) = x := congrArg Prod.fst hfeq
        have hy : (fun i => ((uv.2 i : ℕ) : ℤ)) = y := congrArg Prod.snd hfeq
        subst hx; subst hy
        exact ⟨⟨⟨uv.1, rfl⟩, ⟨uv.2, rfl⟩⟩, huv⟩
      · rintro ⟨⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩, h⟩
        exact ⟨(u, v), h, rfl⟩
    dsimp only [N_c, N_S_c]
    rw [← himg, card_image_of_injective _ hf_inj]
  have hJ_eq : J s k P = ((S ×ˢ S).filter fun xy =>
      ∀ j : Fin k, ∑ i : Fin s, (xy.1 i) ^ (j.1 + 1) = ∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)).card := by
    let f : ((Fin s → Fin P) × (Fin s → Fin P)) → ((Fin s → ℤ) × (Fin s → ℤ)) :=
      fun uv => (fun i => ((uv.1 i : ℕ) : ℤ), fun i => ((uv.2 i : ℕ) : ℤ))
    have hf_inj : Function.Injective f := fun a b h =>
      Prod.ext (hS_inj (congrArg Prod.fst h)) (hS_inj (congrArg Prod.snd h))
    have himg : (((Finset.univ : Finset ((Fin s → Fin P) × (Fin s → Fin P))).filter fun uv =>
        ∀ j : Fin k, ∑ i : Fin s, ((uv.1 i : ℕ) : ℤ) ^ (j.1 + 1) =
          ∑ i : Fin s, ((uv.2 i : ℕ) : ℤ) ^ (j.1 + 1)).image f) =
        ((S ×ˢ S).filter fun xy =>
          ∀ j : Fin k, ∑ i : Fin s, (xy.1 i) ^ (j.1 + 1) = ∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)) := by
      ext ⟨x, y⟩
      simp only [mem_image, mem_filter, mem_univ, true_and, mem_product, S]
      constructor
      · rintro ⟨uv, huv, hfeq⟩
        have hx : (fun i => ((uv.1 i : ℕ) : ℤ)) = x := congrArg Prod.fst hfeq
        have hy : (fun i => ((uv.2 i : ℕ) : ℤ)) = y := congrArg Prod.snd hfeq
        subst hx; subst hy
        exact ⟨⟨⟨uv.1, rfl⟩, ⟨uv.2, rfl⟩⟩, huv⟩
      · rintro ⟨⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩, h⟩
        exact ⟨(u, v), h, rfl⟩
    rw [J, ← card_image_of_injective _ hf_inj, himg]
  have horth : ((∏ j : Fin k, (M j : ℝ)) * (N_S_c : ℝ) : ℂ) =
      ∑ a : ∀ j : Fin k, Fin (M j),
        ((‖∑ x ∈ S, ∏ i : Fin s, weylChar k M a (x i)‖ ^ 2 : ℝ) : ℂ) *
        ∏ j : Fin k, e (-((((a j : ℕ) : ℝ) * (c j : ℝ)) / (M j : ℝ))) := by
    have hnorm_sq : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := fun z => by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [hnorm_sq]
    have hexp : ∀ a : ∀ j : Fin k, Fin (M j),
        (∑ x ∈ S, ∏ i : Fin s, weylChar k M a (x i)) *
        star (∑ y ∈ S, ∏ i : Fin s, weylChar k M a (y i)) *
        (∏ j : Fin k, e (-((((a j : ℕ) : ℝ) * (c j : ℝ)) / (M j : ℝ)))) =
        ∑ xy ∈ S ×ˢ S, ∏ j : Fin k,
          e ((((a j : ℕ) : ℝ) * (((∑ i : Fin s, (xy.1 i) ^ (j.1 + 1)) -
            (∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)) - c j : ℤ) : ℝ)) / (M j : ℝ)) := by
      intro a
      rw [star_sum, sum_mul_sum, ← Finset.sum_product', Finset.sum_mul]
      refine sum_congr rfl fun xy _ => ?_
      have hprod : ∀ z : Fin s → ℤ, ∏ i : Fin s, weylChar k M a (z i) =
          ∏ j : Fin k, e ((((a j : ℕ) : ℝ) * ((∑ i : Fin s, (z i) ^ (j.1 + 1) : ℤ) : ℝ)) / (M j : ℝ)) := by
        intro z
        dsimp only [weylChar]
        rw [Finset.prod_comm]
        refine prod_congr rfl fun j _ => ?_
        have hsum_e : ∀ (T : Finset (Fin s)) (f : Fin s → ℝ), ∏ i ∈ T, e (f i) = e (∑ i ∈ T, f i) := by
          intro T f
          induction T using Finset.induction_on with
          | empty => simp [e_zero]
          | @insert u T' hu ih => rw [prod_insert hu, sum_insert hu, ih, e_add]
        rw [hsum_e]; congr 1; push_cast; rw [Finset.mul_sum, Finset.sum_div]
      rw [hprod xy.1, hprod xy.2, star_prod]
      simp_rw [e_star]
      rw [← prod_mul_distrib, ← prod_mul_distrib]
      refine prod_congr rfl fun j _ => ?_
      rw [← e_add, ← e_add]; congr 1; push_cast; ring
    simp_rw [hexp]
    rw [Finset.sum_comm]
    simp_rw [sum_prod_e_div_eq_ite M hM]
    have hiff : ∀ xy ∈ S ×ˢ S,
        (∀ j : Fin k, (M j : ℤ) ∣ (∑ i : Fin s, (xy.1 i) ^ (j.1 + 1)) -
          (∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)) - c j) ↔
        (∀ j : Fin k, (∑ i : Fin s, (xy.1 i) ^ (j.1 + 1)) -
          (∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)) = c j) := by
      intro xy hxy
      obtain ⟨hx, hy⟩ := mem_product.mp hxy
      refine forall_congr' fun j => ⟨fun hd => ?_, fun heq => by rw [heq, sub_self]; exact dvd_zero _⟩
      exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hd (hfit_c xy.1 hx xy.2 hy j))
    have hsum_eq : ∑ xy ∈ S ×ˢ S, (if ∀ j : Fin k, (M j : ℤ) ∣
          (∑ i : Fin s, (xy.1 i) ^ (j.1 + 1)) - (∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)) - c j
          then (∏ j : Fin k, (M j : ℂ)) else 0) =
        ∑ xy ∈ S ×ˢ S, (if ∀ j : Fin k,
          (∑ i : Fin s, (xy.1 i) ^ (j.1 + 1)) - (∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)) = c j
          then (∏ j : Fin k, (M j : ℂ)) else 0) :=
      sum_congr rfl fun xy hxy => by simp [hiff xy hxy]
    rw [hsum_eq, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    push_cast; rfl
  have hprod_pos : (0 : ℝ) < ∏ j : Fin k, (M j : ℝ) :=
    prod_pos fun j _ => by exact_mod_cast (by have := hM j; omega : 0 < M j)
  have hleR : (∏ j : Fin k, (M j : ℝ)) * (N_S_c : ℝ) ≤
      (∏ j : Fin k, (M j : ℝ)) * (J s k P : ℝ) := by
    have hnorm := congrArg norm horth
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at hnorm
    rw [hnorm, hJ_eq, parseval_tuples M hM S hfit0]
    calc ‖∑ a : ∀ j : Fin k, Fin (M j),
            ((‖∑ x ∈ S, ∏ i : Fin s, weylChar k M a (x i)‖ ^ 2 : ℝ) : ℂ) *
            ∏ j : Fin k, e (-((((a j : ℕ) : ℝ) * (c j : ℝ)) / (M j : ℝ)))‖
        ≤ ∑ a : ∀ j : Fin k, Fin (M j),
            ‖((‖∑ x ∈ S, ∏ i : Fin s, weylChar k M a (x i)‖ ^ 2 : ℝ) : ℂ) *
            ∏ j : Fin k, e (-((((a j : ℕ) : ℝ) * (c j : ℝ)) / (M j : ℝ)))‖ := norm_sum_le _ _
      _ = ∑ a : ∀ j : Fin k, Fin (M j), ‖∑ x ∈ S, ∏ i : Fin s, weylChar k M a (x i)‖ ^ 2 := by
          refine sum_congr rfl fun a _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _), norm_prod]
          simp [norm_e]
  have hnat : (N_S_c : ℝ) ≤ (J s k P : ℝ) := le_of_mul_le_mul_left hleR hprod_pos
  rw [show ((Finset.univ : Finset ((Fin s → Fin P) × (Fin s → Fin P))).filter fun uv =>
      ∀ j : Fin k, (∑ i : Fin s, ((uv.1 i : ℕ) : ℤ) ^ (j.1 + 1)) -
        (∑ i : Fin s, ((uv.2 i : ℕ) : ℤ) ^ (j.1 + 1)) = c j).card = N_c from rfl, hN_eq]
  exact_mod_cast hnat

/-- Core p-adic recursion step for `J(s, k, P)`:
    for `k ≥ 1`, `s ≥ k`, `P ≥ 1`, prime `p` with `k < p` and `P ≤ p^k`, letting
    `P₁ = (P + p - 1) / p`, we have
    `J(s, k, P) ≤ 2 * (p^(k-1) * (k-1)^s)^2 * J(s, k, P₁) +
                  2 * s^(2k) * k! * p^(2(s-k) + k(k-1)/2) * P^k * J(s-k, k, P₁)`. -/
theorem J_padic_step {s k P p : ℕ} (hk : 1 ≤ k) (hsk : k < s) (hP : 1 ≤ P)
    (hp : p.Prime) (hkp : k < p) (hPpk : P ≤ p ^ k) :
    let P₁ := (P + p - 1) / p
    (J s k P : ℝ) ≤
      2 * ((p : ℝ) ^ (k - 1) * ((k - 1 : ℕ) : ℝ) ^ s) ^ 2 * (J s k P₁ : ℝ) +
      2 * (s : ℝ) ^ (2 * k) * (k.factorial : ℝ) *
        (p : ℝ) ^ (2 * (s - k) + k * (k - 1) / 2) * (P : ℝ) ^ k * (J (s - k) k P₁ : ℝ) := by
  classical
  intro P₁
  have hp_pos : 0 < p := hp.pos
  -- Choose M_j large enough for all tuples in [0, P)^s
  let M : Fin k → ℕ := fun j => 2 * s * P ^ (j.1 + 1) + 2
  have hM : ∀ j, 1 ≤ M j := fun j => by dsimp [M]; omega
  have hprodM_pos : (0 : ℝ) < ∏ j : Fin k, (M j : ℝ) :=
    prod_pos fun j _ => by exact_mod_cast (by have := hM j; omega : 0 < M j)
  let embS : (Fin s → Fin P) → (Fin s → ℤ) := fun x i => ((x i : ℕ) : ℤ)
  have hembS_inj : Function.Injective embS := fun x y h => by
    ext i; have := congrFun h i; dsimp only [embS] at this; exact_mod_cast this
  let AllT : Finset (Fin s → Fin P) := Finset.univ
  let GoodT : Finset (Fin s → Fin P) :=
    AllT.filter fun x => k ≤ (Finset.univ.image fun i : Fin s => (x i : ℕ) % p).card
  let BadT : Finset (Fin s → Fin P) :=
    AllT.filter fun x => (Finset.univ.image fun i : Fin s => (x i : ℕ) % p).card < k
  have hfit : ∀ x ∈ AllT.image embS, ∀ y ∈ AllT.image embS, ∀ j : Fin k,
      |(∑ i : Fin s, (x i) ^ (j.1 + 1)) - (∑ i : Fin s, (y i) ^ (j.1 + 1))| < (M j : ℤ) := by
    intro x hx y hy j
    obtain ⟨x₀, _, rfl⟩ := mem_image.mp hx
    obtain ⟨y₀, _, rfl⟩ := mem_image.mp hy
    have hbd : ∀ z : Fin s → Fin P,
        |∑ i : Fin s, ((z i : ℕ) : ℤ) ^ (j.1 + 1)| ≤ (s : ℤ) * (P : ℤ) ^ (j.1 + 1) := by
      intro z
      calc |∑ i : Fin s, ((z i : ℕ) : ℤ) ^ (j.1 + 1)|
          ≤ ∑ i : Fin s, |((z i : ℕ) : ℤ) ^ (j.1 + 1)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin s, (P : ℤ) ^ (j.1 + 1) := sum_le_sum fun i _ => by
            rw [abs_of_nonneg (by positivity)]
            exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast (z i).2.le) _
        _ = (s : ℤ) * (P : ℤ) ^ (j.1 + 1) := by simp
    have h2 := abs_sub (∑ i : Fin s, ((x₀ i : ℕ) : ℤ) ^ (j.1 + 1))
        (∑ i : Fin s, ((y₀ i : ℕ) : ℤ) ^ (j.1 + 1))
    have h3 : (M j : ℤ) = 2 * (s : ℤ) * (P : ℤ) ^ (j.1 + 1) + 2 := by simp [M]
    linarith [hbd x₀, hbd y₀]
  -- Split f(a)^s = F_good(a) + F_bad(a) via Cauchy-Schwarz
  let Fset (T : Finset (Fin s → Fin P)) (a : ∀ j : Fin k, Fin (M j)) : ℂ :=
    ∑ x ∈ T, ∏ i : Fin s, weylChar k M a ((x i : ℕ) : ℤ)
  have hF_split : ∀ a, Fset AllT a = Fset GoodT a + Fset BadT a := by
    intro a
    dsimp only [Fset, GoodT, BadT]
    have hdisj : Disjoint (AllT.filter fun x => k ≤ (Finset.univ.image fun i : Fin s => (x i : ℕ) % p).card)
        (AllT.filter fun x => (Finset.univ.image fun i : Fin s => (x i : ℕ) % p).card < k) :=
      Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
    rw [← sum_union hdisj]
    congr 1
    ext x; simp only [mem_union, mem_filter]; constructor
    · intro hx; by_cases h : k ≤ (Finset.univ.image fun i : Fin s => (x i : ℕ) % p).card
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, by omega⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hJ_split : (∏ j : Fin k, (M j : ℝ)) * (J s k P : ℝ) ≤
      2 * (∑ a : ∀ j : Fin k, Fin (M j), ‖Fset BadT a‖ ^ 2) +
      2 * (∑ a : ∀ j : Fin k, Fin (M j), ‖Fset GoodT a‖ ^ 2) := by
    have hJ_card : J s k P = (((AllT.image embS) ×ˢ (AllT.image embS)).filter fun xy =>
        ∀ j : Fin k, ∑ i : Fin s, (xy.1 i) ^ (j.1 + 1) = ∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)).card := by
      let f : ((Fin s → Fin P) × (Fin s → Fin P)) → ((Fin s → ℤ) × (Fin s → ℤ)) :=
        fun xy => (embS xy.1, embS xy.2)
      have hf_inj : Function.Injective f := fun a b h =>
        Prod.ext (hembS_inj (congrArg Prod.fst h)) (hembS_inj (congrArg Prod.snd h))
      have himg : (((Finset.univ : Finset ((Fin s → Fin P) × (Fin s → Fin P))).filter fun xy =>
          ∀ j : Fin k, ∑ i : Fin s, ((xy.1 i : ℕ) : ℤ) ^ (j.1 + 1) =
            ∑ i : Fin s, ((xy.2 i : ℕ) : ℤ) ^ (j.1 + 1)).image f) =
          (((AllT.image embS) ×ˢ (AllT.image embS)).filter fun xy =>
            ∀ j : Fin k, ∑ i : Fin s, (xy.1 i) ^ (j.1 + 1) = ∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)) := by
        ext ⟨x, y⟩
        simp only [mem_image, mem_filter, mem_univ, true_and, mem_product, AllT]
        constructor
        · rintro ⟨uv, huv, hfeq⟩
          have hx : embS uv.1 = x := congrArg Prod.fst hfeq
          have hy : embS uv.2 = y := congrArg Prod.snd hfeq
          subst hx; subst hy
          exact ⟨⟨⟨uv.1, rfl⟩, ⟨uv.2, rfl⟩⟩, huv⟩
        · rintro ⟨⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩, h⟩
          exact ⟨(u, v), h, rfl⟩
      rw [J, ← card_image_of_injective _ hf_inj, himg]
    rw [hJ_card, parseval_tuples M hM (AllT.image embS) hfit]
    have hsum_F : ∀ a, ∑ x ∈ AllT.image embS, ∏ i : Fin s, weylChar k M a (x i) = Fset AllT a :=
      fun a => Finset.sum_image fun _ _ _ _ h => hembS_inj h
    simp_rw [hsum_F, hF_split]
    rw [← mul_add, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine sum_le_sum fun a _ => ?_
    have h1 : ‖Fset GoodT a + Fset BadT a‖ ≤ ‖Fset GoodT a‖ + ‖Fset BadT a‖ := norm_add_le _ _
    nlinarith [sq_nonneg (‖Fset GoodT a‖ - ‖Fset BadT a‖), norm_nonneg (Fset GoodT a),
      norm_nonneg (Fset BadT a), norm_nonneg (Fset GoodT a + Fset BadT a)]
  -- Helper: single residue class sum f_r(a) has 2m-th moment ≤ (∏ M_j) * J m k P₁
  let resClass (r : Fin p) : Finset (Fin P) :=
    (Finset.univ : Finset (Fin P)).filter fun x => (x : ℕ) % p = (r : ℕ)
  let fRes (r : Fin p) (a : ∀ j : Fin k, Fin (M j)) : ℂ :=
    ∑ x ∈ resClass r, weylChar k M a ((x : ℕ) : ℤ)
  have hres_moment : ∀ (m : ℕ) (hm : m ≤ s) (r : Fin p),
      (∑ a : ∀ j : Fin k, Fin (M j), ‖fRes r a‖ ^ (2 * m)) ≤
        (∏ j : Fin k, (M j : ℝ)) * (J m k P₁ : ℝ) := by
    intro m hm r
    let R_tup : Finset (Fin m → ℤ) :=
      ((Finset.univ : Finset (Fin m → resClass r)).image fun x i => (((x i).1 : ℕ) : ℤ))
    have hR_inj : Function.Injective (fun (x : Fin m → resClass r) (i : Fin m) => (((x i).1 : ℕ) : ℤ)) := by
      intro x y h; ext i; have := congrFun h i; dsimp only at this; exact_mod_cast this
    have hR_fit : ∀ x ∈ R_tup, ∀ y ∈ R_tup, ∀ j : Fin k,
        |(∑ i : Fin m, (x i) ^ (j.1 + 1)) - (∑ i : Fin m, (y i) ^ (j.1 + 1))| < (M j : ℤ) := by
      intro x hx y hy j
      obtain ⟨x₀, _, rfl⟩ := mem_image.mp hx
      obtain ⟨y₀, _, rfl⟩ := mem_image.mp hy
      have hbd : ∀ z : Fin m → resClass r,
          |∑ i : Fin m, (((z i).1 : ℕ) : ℤ) ^ (j.1 + 1)| ≤ (m : ℤ) * (P : ℤ) ^ (j.1 + 1) := by
        intro z
        calc |∑ i : Fin m, (((z i).1 : ℕ) : ℤ) ^ (j.1 + 1)|
            ≤ ∑ i : Fin m, |(((z i).1 : ℕ) : ℤ) ^ (j.1 + 1)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin m, (P : ℤ) ^ (j.1 + 1) := sum_le_sum fun i _ => by
              rw [abs_of_nonneg (by positivity)]
              exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast (z i).1.2.le) _
          _ = (m : ℤ) * (P : ℤ) ^ (j.1 + 1) := by simp
      have h2 := abs_sub (∑ i : Fin m, (((x₀ i).1 : ℕ) : ℤ) ^ (j.1 + 1))
          (∑ i : Fin m, (((y₀ i).1 : ℕ) : ℤ) ^ (j.1 + 1))
      have h3 : (M j : ℤ) = 2 * (s : ℤ) * (P : ℤ) ^ (j.1 + 1) + 2 := by simp [M]
      have hms : (m : ℤ) * (P : ℤ) ^ (j.1 + 1) ≤ (s : ℤ) * (P : ℤ) ^ (j.1 + 1) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hm) (by positivity)
      linarith [hbd x₀, hbd y₀]
    have hpow_eq : ∀ a : ∀ j : Fin k, Fin (M j),
        ‖fRes r a‖ ^ (2 * m) = ‖∑ x ∈ R_tup, ∏ i : Fin m, weylChar k M a (x i)‖ ^ 2 := by
      intro a
      rw [Finset.sum_image (fun _ _ _ _ h => hR_inj h)]
      have hprod : (∑ x : Fin m → resClass r, ∏ i : Fin m, weylChar k M a (((x i).1 : ℕ) : ℤ)) =
          (fRes r a) ^ m := by
        rw [← Fintype.prod_sum (fun (_ : Fin m) (u : resClass r) => weylChar k M a ((u.1 : ℕ) : ℤ))]
        simp only [Finset.prod_const, card_univ, Fintype.card_fin]
        congr 1
        dsimp only [fRes]
        exact Finset.sum_coe_sort (resClass r) (fun u => weylChar k M a ((u : ℕ) : ℤ))
      rw [hprod, norm_pow, ← pow_mul, mul_comm m 2]
    simp_rw [hpow_eq]
    rw [← parseval_tuples M hM R_tup hR_fit]
    refine mul_le_mul_of_nonneg_left ?_ hprodM_pos.le
    -- Map each solution in R_tup × R_tup to (Fin m → Fin P₁) × (Fin m → Fin P₁) via u ↦ (u - r) / p
    let toP1 : (Fin m → resClass r) → (Fin m → Fin P₁) := fun x i =>
      ⟨((x i).1 : ℕ) / p, by
        have hx : ((x i).1 : ℕ) < P := (x i).1.2
        have hlt : ((x i).1 : ℕ) / p * p < P + p - 1 := by
          have := Nat.div_mul_le_self ((x i).1 : ℕ) p
          omega
        dsimp only [P₁]
        exact Nat.div_lt_of_lt_mul (by
          have h1 : P ≤ P₁ * p := by
            dsimp only [P₁]
            have hdm := Nat.div_add_mod (P + p - 1) p
            have hrem := Nat.mod_lt (P + p - 1) hp_pos
            rw [mul_comm] at hdm
            omega
          exact lt_of_lt_of_le hx (by rwa [mul_comm] at h1))⟩
    have htoP1_inj : Function.Injective toP1 := by
      intro x y h
      ext i
      have hdiv : ((x i).1 : ℕ) / p = ((y i).1 : ℕ) / p := congrArg (fun f => (f i : ℕ)) h
      have hmodx : ((x i).1 : ℕ) % p = (r : ℕ) := (mem_filter.mp (x i).2).2
      have hmody : ((y i).1 : ℕ) % p = (r : ℕ) := (mem_filter.mp (y i).2).2
      have hdx := Nat.div_add_mod ((x i).1 : ℕ) p
      have hdy := Nat.div_add_mod ((y i).1 : ℕ) p
      rw [← hdx, ← hdy, hdiv, hmodx, hmody]
    have hcard_le : (((R_tup ×ˢ R_tup).filter fun xy =>
        ∀ j : Fin k, ∑ i : Fin m, (xy.1 i) ^ (j.1 + 1) = ∑ i : Fin m, (xy.2 i) ^ (j.1 + 1)).card) ≤
        J m k P₁ := by
      let φ : ((Fin m → resClass r) × (Fin m → resClass r)) → ((Fin m → ℤ) × (Fin m → ℤ)) :=
        fun xy => (fun i => (((xy.1 i).1 : ℕ) : ℤ), fun i => (((xy.2 i).1 : ℕ) : ℤ))
      have hφ_inj : Function.Injective φ := fun a b h =>
        Prod.ext (hR_inj (congrArg Prod.fst h)) (hR_inj (congrArg Prod.snd h))
      have himg : (((Finset.univ : Finset ((Fin m → resClass r) × (Fin m → resClass r))).filter fun xy =>
          ∀ j : Fin k, ∑ i : Fin m, (((xy.1 i).1 : ℕ) : ℤ) ^ (j.1 + 1) =
            ∑ i : Fin m, (((xy.2 i).1 : ℕ) : ℤ) ^ (j.1 + 1)).image φ) =
          ((R_tup ×ˢ R_tup).filter fun xy =>
            ∀ j : Fin k, ∑ i : Fin m, (xy.1 i) ^ (j.1 + 1) = ∑ i : Fin m, (xy.2 i) ^ (j.1 + 1)) := by
        ext ⟨x, y⟩
        simp only [mem_image, mem_filter, mem_univ, true_and, mem_product, R_tup]
        constructor
        · rintro ⟨uv, huv, hfeq⟩
          have hx : (fun i => (((uv.1 i).1 : ℕ) : ℤ)) = x := congrArg Prod.fst hfeq
          have hy : (fun i => (((uv.2 i).1 : ℕ) : ℤ)) = y := congrArg Prod.snd hfeq
          subst hx; subst hy
          exact ⟨⟨⟨uv.1, rfl⟩, ⟨uv.2, rfl⟩⟩, huv⟩
        · rintro ⟨⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩, h⟩; exact ⟨(u, v), h, rfl⟩
      rw [← himg, card_image_of_injective _ hφ_inj]
      let ψ : ((Fin m → resClass r) × (Fin m → resClass r)) → ((Fin m → Fin P₁) × (Fin m → Fin P₁)) :=
        fun xy => (toP1 xy.1, toP1 xy.2)
      have hψ_inj : Function.Injective ψ := fun a b h =>
        Prod.ext (htoP1_inj (congrArg Prod.fst h)) (htoP1_inj (congrArg Prod.snd h))
      calc _ = (((Finset.univ : Finset ((Fin m → resClass r) × (Fin m → resClass r))).filter fun xy =>
            ∀ j : Fin k, ∑ i : Fin m, (((xy.1 i).1 : ℕ) : ℤ) ^ (j.1 + 1) =
              ∑ i : Fin m, (((xy.2 i).1 : ℕ) : ℤ) ^ (j.1 + 1)).image ψ).card :=
          (card_image_of_injective _ hψ_inj).symm
        _ ≤ J m k P₁ := card_le_card fun uv huv => by
            obtain ⟨xy, hxy, rfl⟩ := mem_image.mp huv
            have hsums := (mem_filter.mp hxy).2
            refine mem_filter.mpr ⟨mem_univ _, ?_⟩
            have hlin : ∀ z : Fin m → resClass r, ∀ i : Fin m,
                (((z i).1 : ℕ) : ℤ) = (p : ℤ) * ((toP1 z i : ℕ) : ℤ) + (r : ℤ) := by
              intro z i
              have hmod : ((z i).1 : ℕ) % p = (r : ℕ) := (mem_filter.mp (z i).2).2
              have hdm := Nat.div_add_mod ((z i).1 : ℕ) p
              rw [hmod] at hdm
              have hdmZ : (((p * (((z i).1 : ℕ) / p) + (r : ℕ) : ℕ) : ℤ)) = (((z i).1 : ℕ) : ℤ) := by
                exact_mod_cast hdm
              simp only [Nat.cast_add, Nat.cast_mul] at hdmZ
              exact hdmZ.symm
            have hsh : ∀ j : Fin k,
                ∑ i : Fin m, ((p : ℤ) * ((toP1 xy.1 i : ℕ) : ℤ)) ^ (j.1 + 1) =
                ∑ i : Fin m, ((p : ℤ) * ((toP1 xy.2 i : ℕ) : ℤ)) ^ (j.1 + 1) :=
              (power_sums_shift_iff _ _ (r : ℤ)).mp (fun j => by
                simpa only [← hlin xy.1, ← hlin xy.2] using hsums j)
            intro j
            have hj := hsh j
            simp_rw [mul_pow, ← Finset.mul_sum] at hj
            exact mul_left_cancel₀ (pow_ne_zero (j.1 + 1) (Int.natCast_ne_zero.mpr hp.ne_zero)) hj
    exact_mod_cast hcard_le
  -- Bound 1: Bad tuples (≤ k - 1 distinct residues mod p)
  have hBad_bound : (∑ a : ∀ j : Fin k, Fin (M j), ‖Fset BadT a‖ ^ 2) ≤
      (∏ j : Fin k, (M j : ℝ)) * (((p : ℝ) ^ (k - 1) * ((k - 1 : ℕ) : ℝ) ^ s) ^ 2 * (J s k P₁ : ℝ)) := by
    let BadIdx : Finset (Fin s → Fin p) :=
      (Finset.univ : Finset (Fin s → Fin p)).filter fun r => (Finset.univ.image r).card < k
    have hBadIdx_card : BadIdx.card ≤ p ^ (k - 1) * (k - 1) ^ s := by
      -- Map each r ∈ BadIdx into pairs (T : Fin (k - 1) → Fin p, f : Fin s → Fin (k - 1))
      -- Actually, if k = 1 then BadIdx is empty since (image r).card ≥ 1 (as s ≥ k ≥ 1)!
      rcases Nat.eq_or_lt_of_le hk with rfl | hk2
      · have hemp : BadIdx = ∅ := by
          ext r; simp only [BadIdx, mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_lt]
          have hne : (Finset.univ : Finset (Fin s)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
          exact Finset.card_pos.mpr (hne.image r)
        rw [hemp, card_empty]; exact Nat.zero_le _
      · have hkm1_pos : 0 < k - 1 := by omega
        -- For every r ∈ BadIdx, there is T : Fin (k - 1) → Fin p and f : Fin s → Fin (k - 1) with r = T ∘ f
        have hsurj : ∀ r ∈ BadIdx, ∃ Tf : (Fin (k - 1) → Fin p) × (Fin s → Fin (k - 1)),
            r = Tf.1 ∘ Tf.2 := by
          intro r hr
          have hlt : (Finset.univ.image r).card ≤ k - 1 := by
            have := (mem_filter.mp hr).2; omega
          let U := Finset.univ.image r
          let eU : Fin U.card ≃ U := (Fintype.equivFinOfCardEq (by simp)).symm
          have hU_ne : U.Nonempty := by
            have hne : (Finset.univ : Finset (Fin s)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
            exact hne.image r
          let u₀ : Fin p := hU_ne.choose
          let T : Fin (k - 1) → Fin p := fun j =>
            if hj : j.1 < U.card then (eU ⟨j.1, hj⟩).1 else u₀
          let f : Fin s → Fin (k - 1) := fun i =>
            ⟨(eU.symm ⟨r i, mem_image_of_mem r (mem_univ i)⟩).1,
              lt_of_lt_of_le (eU.symm ⟨r i, mem_image_of_mem r (mem_univ i)⟩).2 hlt⟩
          refine ⟨(T, f), ?_⟩
          ext i
          dsimp only [Function.comp_apply, T, f]
          have hidx := (eU.symm ⟨r i, mem_image_of_mem r (mem_univ i)⟩).2
          rw [dif_pos hidx]
          have hfin : (⟨(eU.symm ⟨r i, mem_image_of_mem r (mem_univ i)⟩).1, hidx⟩ : Fin U.card) =
              eU.symm ⟨r i, mem_image_of_mem r (mem_univ i)⟩ := Fin.eta _ _
          rw [hfin]
          exact congrArg Fin.val (congrArg Subtype.val (eU.apply_symm_apply ⟨r i, mem_image_of_mem r (mem_univ i)⟩)).symm
        let Φ : ((Fin (k - 1) → Fin p) × (Fin s → Fin (k - 1))) → (Fin s → Fin p) :=
          fun Tf => Tf.1 ∘ Tf.2
        have hsub : BadIdx ⊆ (Finset.univ : Finset ((Fin (k - 1) → Fin p) × (Fin s → Fin (k - 1)))).image Φ := by
          intro r hr
          obtain ⟨Tf, rfl⟩ := hsurj r hr
          exact mem_image_of_mem Φ (mem_univ Tf)
        calc BadIdx.card ≤ ((Finset.univ : Finset ((Fin (k - 1) → Fin p) × (Fin s → Fin (k - 1)))).image Φ).card :=
              card_le_card hsub
          _ ≤ (Finset.univ : Finset ((Fin (k - 1) → Fin p) × (Fin s → Fin (k - 1)))).card := card_image_le
          _ = p ^ (k - 1) * (k - 1) ^ s := by simp [Fintype.card_prod]
    have hFBad_eq : ∀ a : ∀ j : Fin k, Fin (M j),
        Fset BadT a = ∑ r ∈ BadIdx, ∏ i : Fin s, fRes (r i) a := by
      intro a
      dsimp only [Fset, fRes]
      let rOf : (Fin s → Fin P) → (Fin s → Fin p) := fun x i => ⟨(x i : ℕ) % p, Nat.mod_lt _ hp_pos⟩
      have hrOf_mem : ∀ x ∈ BadT, rOf x ∈ BadIdx := by
        intro x hx
        refine mem_filter.mpr ⟨mem_univ _, ?_⟩
        have hlt := (mem_filter.mp hx).2
        have hcard_eq : (Finset.univ.image (rOf x)).card =
            (Finset.univ.image fun i : Fin s => (x i : ℕ) % p).card := by
          have : (Finset.univ.image (rOf x)).image Fin.val =
              (Finset.univ.image fun i : Fin s => (x i : ℕ) % p) := by
            ext u; simp [rOf]
          rw [← this, card_image_of_injective _ Fin.val_injective]
        omega
      rw [← Finset.sum_fiberwise_of_maps_to hrOf_mem]
      refine sum_congr rfl fun r hr => ?_
      have hfib : BadT.filter (fun x => rOf x = r) = Fintype.piFinset (fun i : Fin s => resClass (r i)) := by
        ext x
        simp only [mem_filter, BadT, AllT, mem_univ, true_and, Fintype.mem_piFinset, resClass]
        constructor
        · rintro ⟨_, hrx⟩ i
          exact congrArg (fun f => (f i : ℕ)) hrx
        · intro hall
          have hrx : rOf x = r := by ext i; exact hall i
          refine ⟨?_, hrx⟩
          have hcard_eq : (Finset.univ.image (rOf x)).card =
              (Finset.univ.image fun i : Fin s => (x i : ℕ) % p).card := by
            have : (Finset.univ.image (rOf x)).image Fin.val =
                (Finset.univ.image fun i : Fin s => (x i : ℕ) % p) := by
              ext u; simp [rOf]
            rw [← this, card_image_of_injective _ Fin.val_injective]
          rw [← hcard_eq, hrx]
          exact (mem_filter.mp hr).2
      rw [hfib, Finset.prod_univ_sum]
    have hcs_amgm : ∀ a : ∀ j : Fin k, Fin (M j),
        ‖Fset BadT a‖ ^ 2 ≤ (BadIdx.card : ℝ) *
          ∑ r ∈ BadIdx, (1 / (s : ℝ)) * ∑ i : Fin s, ‖fRes (r i) a‖ ^ (2 * s) := by
      intro a
      rw [hFBad_eq a]
      have htri : ‖∑ r ∈ BadIdx, ∏ i : Fin s, fRes (r i) a‖ ≤
          ∑ r ∈ BadIdx, ∏ i : Fin s, ‖fRes (r i) a‖ := by
        calc ‖∑ r ∈ BadIdx, ∏ i : Fin s, fRes (r i) a‖
            ≤ ∑ r ∈ BadIdx, ‖∏ i : Fin s, fRes (r i) a‖ := norm_sum_le _ _
          _ = ∑ r ∈ BadIdx, ∏ i : Fin s, ‖fRes (r i) a‖ := sum_congr rfl fun _ _ => norm_prod _ _
      have hcs : (∑ r ∈ BadIdx, ∏ i : Fin s, ‖fRes (r i) a‖) ^ 2 ≤
          (BadIdx.card : ℝ) * ∑ r ∈ BadIdx, (∏ i : Fin s, ‖fRes (r i) a‖) ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := BadIdx) (f := fun r => ∏ i : Fin s, ‖fRes (r i) a‖)
      have hamgm : ∀ r : Fin s → Fin p,
          (∏ i : Fin s, ‖fRes (r i) a‖) ^ 2 ≤
            (1 / (s : ℝ)) * ∑ i : Fin s, ‖fRes (r i) a‖ ^ (2 * s) := by
        intro r
        have hspos : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
        have hw_nn : ∀ i ∈ (Finset.univ : Finset (Fin s)), (0 : ℝ) ≤ 1 / (s : ℝ) := fun _ _ => by positivity
        have hw_sum : ∑ _i : Fin s, (1 / (s : ℝ)) = 1 := by
          simp [div_eq_mul_inv, hspos.ne']
        have hz_nn : ∀ i ∈ (Finset.univ : Finset (Fin s)), 0 ≤ ‖fRes (r i) a‖ ^ (2 * s) :=
          fun _ _ => by positivity
        have h := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => 1 / (s : ℝ))
          (fun i => ‖fRes (r i) a‖ ^ (2 * s)) hw_nn hw_sum hz_nn
        have hlhs : ∏ i : Fin s, (‖fRes (r i) a‖ ^ (2 * s)) ^ (1 / (s : ℝ)) =
            (∏ i : Fin s, ‖fRes (r i) a‖) ^ 2 := by
          rw [← Finset.prod_pow]
          refine prod_congr rfl fun i _ => ?_
          rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
          have hexp : ((2 * s : ℕ) : ℝ) * (1 / (s : ℝ)) = (2 : ℕ) := by
            push_cast; field_simp [hspos.ne']
          rw [hexp, Real.rpow_natCast]
        rw [hlhs, ← Finset.mul_sum] at h
        exact h
      calc ‖∑ r ∈ BadIdx, ∏ i : Fin s, fRes (r i) a‖ ^ 2
          ≤ (∑ r ∈ BadIdx, ∏ i : Fin s, ‖fRes (r i) a‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) htri 2
        _ ≤ (BadIdx.card : ℝ) * ∑ r ∈ BadIdx, (∏ i : Fin s, ‖fRes (r i) a‖) ^ 2 := hcs
        _ ≤ (BadIdx.card : ℝ) * ∑ r ∈ BadIdx, (1 / (s : ℝ)) * ∑ i : Fin s, ‖fRes (r i) a‖ ^ (2 * s) :=
            mul_le_mul_of_nonneg_left (sum_le_sum fun r _ => hamgm r) (Nat.cast_nonneg _)
    calc ∑ a : ∀ j : Fin k, Fin (M j), ‖Fset BadT a‖ ^ 2
        ≤ ∑ a : ∀ j : Fin k, Fin (M j), (BadIdx.card : ℝ) *
            ∑ r ∈ BadIdx, (1 / (s : ℝ)) * ∑ i : Fin s, ‖fRes (r i) a‖ ^ (2 * s) :=
          sum_le_sum fun a _ => hcs_amgm a
      _ = (BadIdx.card : ℝ) * ∑ r ∈ BadIdx, (1 / (s : ℝ)) *
            ∑ i : Fin s, ∑ a : ∀ j : Fin k, Fin (M j), ‖fRes (r i) a‖ ^ (2 * s) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1; refine sum_congr rfl fun r _ => ?_
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ (BadIdx.card : ℝ) * ∑ _r ∈ BadIdx, (1 / (s : ℝ)) *
            ∑ _i : Fin s, ((∏ j : Fin k, (M j : ℝ)) * (J s k P₁ : ℝ)) := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun r _ =>
            mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => hres_moment s le_rfl (r i))
              (by positivity)) (Nat.cast_nonneg _)
      _ = (∏ j : Fin k, (M j : ℝ)) * (((BadIdx.card : ℝ) ^ 2) * (J s k P₁ : ℝ)) := by
          have hs0 : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp [hs0]
      _ ≤ (∏ j : Fin k, (M j : ℝ)) * (((p : ℝ) ^ (k - 1) * ((k - 1 : ℕ) : ℝ) ^ s) ^ 2 * (J s k P₁ : ℝ)) := by
          have hcardR : (BadIdx.card : ℝ) ≤ (p : ℝ) ^ (k - 1) * ((k - 1 : ℕ) : ℝ) ^ s := by
            exact_mod_cast hBadIdx_card
          gcongr
  -- Bound 2: Good tuples (≥ k distinct residues mod p)
  have hGood_bound : (∑ a : ∀ j : Fin k, Fin (M j), ‖Fset GoodT a‖ ^ 2) ≤
      (∏ j : Fin k, (M j : ℝ)) *
        ((s : ℝ) ^ (2 * k) * (k.factorial : ℝ) *
          (p : ℝ) ^ (2 * (s - k) + k * (k - 1) / 2) * (P : ℝ) ^ k * (J (s - k) k P₁ : ℝ)) := by
    -- First convert ∑_a ‖Fset GoodT a‖^2 to physical count N_good
    let N_good : ℕ := ((GoodT ×ˢ GoodT).filter fun xy =>
      ∀ j : Fin k, ∑ i : Fin s, ((xy.1 i : ℕ) : ℤ) ^ (j.1 + 1) =
        ∑ i : Fin s, ((xy.2 i : ℕ) : ℤ) ^ (j.1 + 1)).card
    have hparseval_good : ∑ a : ∀ j : Fin k, Fin (M j), ‖Fset GoodT a‖ ^ 2 =
        (∏ j : Fin k, (M j : ℝ)) * (N_good : ℝ) := by
      have hfitG : ∀ x ∈ GoodT.image embS, ∀ y ∈ GoodT.image embS, ∀ j : Fin k,
          |(∑ i : Fin s, (x i) ^ (j.1 + 1)) - (∑ i : Fin s, (y i) ^ (j.1 + 1))| < (M j : ℤ) :=
        fun x hx y hy j => hfit x (image_subset_image (filter_subset _ _) hx)
          y (image_subset_image (filter_subset _ _) hy) j
      have hsumG : ∀ a, ∑ x ∈ GoodT.image embS, ∏ i : Fin s, weylChar k M a (x i) = Fset GoodT a :=
        fun a => Finset.sum_image fun _ _ _ _ h => hembS_inj h
      have hcardG : (((GoodT.image embS) ×ˢ (GoodT.image embS)).filter fun xy =>
          ∀ j : Fin k, ∑ i : Fin s, (xy.1 i) ^ (j.1 + 1) = ∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)).card = N_good := by
        let f : ((Fin s → Fin P) × (Fin s → Fin P)) → ((Fin s → ℤ) × (Fin s → ℤ)) :=
          fun xy => (embS xy.1, embS xy.2)
        have hf_inj : Function.Injective f := fun a b h =>
          Prod.ext (hembS_inj (congrArg Prod.fst h)) (hembS_inj (congrArg Prod.snd h))
        have himg : (((GoodT ×ˢ GoodT).filter fun xy =>
            ∀ j : Fin k, ∑ i : Fin s, ((xy.1 i : ℕ) : ℤ) ^ (j.1 + 1) =
              ∑ i : Fin s, ((xy.2 i : ℕ) : ℤ) ^ (j.1 + 1)).image f) =
            (((GoodT.image embS) ×ˢ (GoodT.image embS)).filter fun xy =>
              ∀ j : Fin k, ∑ i : Fin s, (xy.1 i) ^ (j.1 + 1) = ∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)) := by
          ext ⟨x, y⟩
          simp only [mem_image, mem_filter, mem_product]
          constructor
          · rintro ⟨uv, ⟨⟨hu, hv⟩, huv⟩, hfeq⟩
            have hx : embS uv.1 = x := congrArg Prod.fst hfeq
            have hy : embS uv.2 = y := congrArg Prod.snd hfeq
            subst hx; subst hy
            exact ⟨⟨⟨uv.1, hu, rfl⟩, ⟨uv.2, hv, rfl⟩⟩, huv⟩
          · rintro ⟨⟨⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩⟩, h⟩
            exact ⟨(u, v), ⟨⟨hu, hv⟩, h⟩, rfl⟩
        rw [← himg, card_image_of_injective _ hf_inj]
      have hp := parseval_tuples M hM (GoodT.image embS) hfitG
      simp_rw [hsumG] at hp
      rw [hcardG] at hp
      exact hp.symm
    rw [hparseval_good]
    refine mul_le_mul_of_nonneg_left ?_ hprodM_pos.le
    -- Reduce N_good to N_star where first k coordinates are pairwise distinct mod p
    let DistK : Finset (Fin k → Fin P) :=
      (Finset.univ : Finset (Fin k → Fin P)).filter fun x =>
        ∀ i j : Fin k, i ≠ j → (x i : ℕ) % p ≠ (x j : ℕ) % p
    let N_star : ℕ :=
      ((Finset.univ : Finset ((Fin k → Fin P) × (Fin (s - k) → Fin P) ×
          (Fin k → Fin P) × (Fin (s - k) → Fin P))).filter fun t =>
        t.1 ∈ DistK ∧ t.2.2.1 ∈ DistK ∧
        ∀ j : Fin k,
          (∑ i : Fin k, ((t.1 i : ℕ) : ℤ) ^ (j.1 + 1)) +
            (∑ i : Fin (s - k), ((t.2.1 i : ℕ) : ℤ) ^ (j.1 + 1)) =
          (∑ i : Fin k, ((t.2.2.1 i : ℕ) : ℤ) ^ (j.1 + 1)) +
            (∑ i : Fin (s - k), ((t.2.2.2 i : ℕ) : ℤ) ^ (j.1 + 1))).card
    have hNgood_le : N_good ≤ s ^ (2 * k) * N_star := by
      -- For each x ∈ GoodT, choose an injection ι : Fin k → Fin s with x ∘ ι ∈ DistK
      have hex_inj : ∀ x ∈ GoodT, ∃ ι : Fin k → Fin s,
          Function.Injective ι ∧ (fun j => x (ι j)) ∈ DistK := by
        intro x hx
        have hcard : k ≤ (Finset.univ.image fun i : Fin s => (x i : ℕ) % p).card :=
          (mem_filter.mp hx).2
        obtain ⟨U, hUsub, hUcard⟩ := Finset.exists_subset_card_eq hcard
        let eU : Fin k ≃ U := (Fintype.equivFinOfCardEq (by simp [hUcard])).symm
        have hex_i : ∀ j : Fin k, ∃ i : Fin s, (x i : ℕ) % p = (eU j).1 := fun j => by
          obtain ⟨i, _, hi⟩ := mem_image.mp (hUsub (eU j).2)
          exact ⟨i, hi⟩
        let ι : Fin k → Fin s := fun j => Classical.choose (hex_i j)
        have hι_mod : ∀ j : Fin k, (x (ι j) : ℕ) % p = (eU j).1 :=
          fun j => Classical.choose_spec (hex_i j)
        refine ⟨ι, ?_, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
        · intro j₁ j₂ h12
          have : (eU j₁).1 = (eU j₂).1 := by rw [← hι_mod j₁, ← hι_mod j₂, h12]
          exact eU.injective (Subtype.ext this)
        · intro j₁ j₂ hne heq
          rw [hι_mod j₁, hι_mod j₂] at heq
          exact hne (eU.injective (Subtype.ext heq))
      -- For any injection ι : Fin k → Fin s, pick a bijection σ : Fin k ⊕ Fin (s - k) ≃ Fin s
      -- agreeing with ι on the left.
      have hex_equiv : ∀ (ι : Fin k → Fin s), Function.Injective ι →
          ∃ σ : (Fin k ⊕ Fin (s - k)) ≃ Fin s, ∀ j : Fin k, σ (Sum.inl j) = ι j := by
        intro ι hι
        let Img := Finset.univ.image ι
        have hImg_card : Img.card = k := by rw [card_image_of_injective _ hι, card_univ, Fintype.card_fin]
        let Comp := (Finset.univ : Finset (Fin s)) \ Img
        have hComp_card : Comp.card = s - k := by
          rw [card_sdiff, Finset.inter_univ, card_univ, Fintype.card_fin, hImg_card]
        let eL : Fin k ≃ Img := Equiv.ofBijective (fun j => ⟨ι j, mem_image_of_mem ι (mem_univ j)⟩)
          ⟨fun a b h => hι (congrArg Subtype.val h), fun ⟨y, hy⟩ => by
            obtain ⟨j, _, rfl⟩ := mem_image.mp hy; exact ⟨j, rfl⟩⟩
        let eR : Fin (s - k) ≃ Comp := (Fintype.equivFinOfCardEq (by simp [hComp_card])).symm
        let σ : (Fin k ⊕ Fin (s - k)) ≃ Fin s :=
          { toFun := Sum.elim (fun j => (eL j).1) (fun j => (eR j).1)
            invFun := fun i => if hi : i ∈ Img then Sum.inl (eL.symm ⟨i, hi⟩)
              else Sum.inr (eR.symm ⟨i, mem_sdiff.mpr ⟨mem_univ i, hi⟩⟩)
            left_inv := by
              rintro (j | j)
              · simp [eL]
              · have hnot : (eR j).1 ∉ Img := (mem_sdiff.mp (eR j).2).2
                simp [hnot]
            right_inv := by
              intro i
              by_cases hi : i ∈ Img
              · simp [hi]
              · simp [hi] }
        exact ⟨σ, fun j => rfl⟩
      -- Map each (x, y) in N_good to ((ι_x, ι_y), (x_1, x_2, y_1, y_2))
      let Sgood := (GoodT ×ˢ GoodT).filter fun xy =>
        ∀ j : Fin k, ∑ i : Fin s, ((xy.1 i : ℕ) : ℤ) ^ (j.1 + 1) =
          ∑ i : Fin s, ((xy.2 i : ℕ) : ℤ) ^ (j.1 + 1)
      let Sstar := (Finset.univ : Finset ((Fin k → Fin P) × (Fin (s - k) → Fin P) ×
          (Fin k → Fin P) × (Fin (s - k) → Fin P))).filter fun t =>
        t.1 ∈ DistK ∧ t.2.2.1 ∈ DistK ∧
        ∀ j : Fin k,
          (∑ i : Fin k, ((t.1 i : ℕ) : ℤ) ^ (j.1 + 1)) +
            (∑ i : Fin (s - k), ((t.2.1 i : ℕ) : ℤ) ^ (j.1 + 1)) =
          (∑ i : Fin k, ((t.2.2.1 i : ℕ) : ℤ) ^ (j.1 + 1)) +
            (∑ i : Fin (s - k), ((t.2.2.2 i : ℕ) : ℤ) ^ (j.1 + 1))
      -- Fix a canonical choice of σ for each injective ι
      let pickσ (ι : Fin k → Fin s) : (Fin k ⊕ Fin (s - k)) ≃ Fin s :=
        if h : Function.Injective ι then Classical.choose (hex_equiv ι h)
        else (Fintype.equivFinOfCardEq (by simp; omega)).trans (Equiv.refl _)
      have hpickσ : ∀ (ι : Fin k → Fin s) (h : Function.Injective ι) (j : Fin k),
          pickσ ι (Sum.inl j) = ι j := fun ι h j => by
        dsimp only [pickσ]; rw [dif_pos h]; exact Classical.choose_spec (hex_equiv ι h) j
      let mapTo : {xy // xy ∈ Sgood} → ((Fin k → Fin s) × (Fin k → Fin s)) × {t // t ∈ Sstar} :=
        fun ⟨xy, hxy⟩ =>
          have hxG : xy.1 ∈ GoodT := (mem_product.mp (mem_filter.mp hxy).1).1
          have hyG : xy.2 ∈ GoodT := (mem_product.mp (mem_filter.mp hxy).1).2
          let ιx := Classical.choose (hex_inj xy.1 hxG)
          let ιy := Classical.choose (hex_inj xy.2 hyG)
          have hιx := Classical.choose_spec (hex_inj xy.1 hxG)
          have hιy := Classical.choose_spec (hex_inj xy.2 hyG)
          let σx := pickσ ιx
          let σy := pickσ ιy
          ((ιx, ιy), ⟨(fun j => xy.1 (σx (Sum.inl j)), fun j => xy.1 (σx (Sum.inr j)),
                       fun j => xy.2 (σy (Sum.inl j)), fun j => xy.2 (σy (Sum.inr j))), by
            refine mem_filter.mpr ⟨mem_univ _, ?_, ?_, ?_⟩
            · simpa [σx, hpickσ ιx hιx.1] using hιx.2
            · simpa [σy, hpickσ ιy hιy.1] using hιy.2
            · intro j
              have hsum_split : ∀ (z : Fin s → Fin P) (σ : (Fin k ⊕ Fin (s - k)) ≃ Fin s),
                  (∑ i : Fin k, ((z (σ (Sum.inl i)) : ℕ) : ℤ) ^ (j.1 + 1)) +
                  (∑ i : Fin (s - k), ((z (σ (Sum.inr i)) : ℕ) : ℤ) ^ (j.1 + 1)) =
                  ∑ i : Fin s, ((z i : ℕ) : ℤ) ^ (j.1 + 1) := fun z σ => by
                rw [← Fintype.sum_sum_type (f := fun i => ((z (σ i) : ℕ) : ℤ) ^ (j.1 + 1)),
                  σ.sum_comp (fun i => ((z i : ℕ) : ℤ) ^ (j.1 + 1))]
              rw [hsum_split xy.1 σx, hsum_split xy.2 σy]
              exact (mem_filter.mp hxy).2 j⟩)
      have hmap_inj : Function.Injective mapTo := by
        intro a b hab
        have hιx_eq : (mapTo a).1.1 = (mapTo b).1.1 := congrArg (fun z => z.1.1) hab
        have hιy_eq : (mapTo a).1.2 = (mapTo b).1.2 := congrArg (fun z => z.1.2) hab
        have ht_eq : (mapTo a).2.1 = (mapTo b).2.1 := congrArg (fun z => z.2.1) hab
        apply Subtype.ext
        ext i
        · let σ := pickσ (mapTo a).1.1
          have hσb : pickσ (mapTo b).1.1 = σ := congrArg pickσ hιx_eq.symm
          rcases h : σ.symm i with j | j
          · have hi : i = σ (Sum.inl j) := by rw [← h, σ.apply_symm_apply]
            rw [hi]
            have h1 := congrArg (fun t => (t.1 j : ℕ)) ht_eq
            dsimp only [mapTo] at h1 hσb ⊢
            change (a.1.1 (pickσ (mapTo a).1.1 (Sum.inl j)) : ℕ) =
              (b.1.1 (pickσ (mapTo b).1.1 (Sum.inl j)) : ℕ) at h1
            rw [hσb] at h1; exact h1
          · have hi : i = σ (Sum.inr j) := by rw [← h, σ.apply_symm_apply]
            rw [hi]
            have h1 := congrArg (fun t => (t.2.1 j : ℕ)) ht_eq
            dsimp only [mapTo] at h1 hσb ⊢
            change (a.1.1 (pickσ (mapTo a).1.1 (Sum.inr j)) : ℕ) =
              (b.1.1 (pickσ (mapTo b).1.1 (Sum.inr j)) : ℕ) at h1
            rw [hσb] at h1; exact h1
        · let σ := pickσ (mapTo a).1.2
          have hσb : pickσ (mapTo b).1.2 = σ := congrArg pickσ hιy_eq.symm
          rcases h : σ.symm i with j | j
          · have hi : i = σ (Sum.inl j) := by rw [← h, σ.apply_symm_apply]
            rw [hi]
            have h1 := congrArg (fun t => (t.2.2.1 j : ℕ)) ht_eq
            dsimp only [mapTo] at h1 hσb ⊢
            change (a.1.2 (pickσ (mapTo a).1.2 (Sum.inl j)) : ℕ) =
              (b.1.2 (pickσ (mapTo b).1.2 (Sum.inl j)) : ℕ) at h1
            rw [hσb] at h1; exact h1
          · have hi : i = σ (Sum.inr j) := by rw [← h, σ.apply_symm_apply]
            rw [hi]
            have h1 := congrArg (fun t => (t.2.2.2 j : ℕ)) ht_eq
            dsimp only [mapTo] at h1 hσb ⊢
            change (a.1.2 (pickσ (mapTo a).1.2 (Sum.inr j)) : ℕ) =
              (b.1.2 (pickσ (mapTo b).1.2 (Sum.inr j)) : ℕ) at h1
            rw [hσb] at h1; exact h1
      have hcard := Fintype.card_le_of_injective mapTo hmap_inj
      simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin,
        Finset.prod_const, card_univ] at hcard
      rw [← pow_add, ← two_mul] at hcard
      exact hcard
    -- Now bound N_star using Hölder over residue classes mod p + Hensel + shifted solutions
    have hNstar_bound : (N_star : ℝ) ≤
        (k.factorial : ℝ) * (p : ℝ) ^ (2 * (s - k) + k * (k - 1) / 2) * (P : ℝ) ^ k * (J (s - k) k P₁ : ℝ) := by
      -- Express (∏ M_j) * N_star in frequency space
      let Fstar (a : ∀ j : Fin k, Fin (M j)) : ℂ :=
        ∑ x ∈ DistK, ∏ i : Fin k, weylChar k M a ((x i : ℕ) : ℤ)
      let fAll (a : ∀ j : Fin k, Fin (M j)) : ℂ :=
        ∑ x : Fin P, weylChar k M a ((x : ℕ) : ℤ)
      have hNstar_freq : (∏ j : Fin k, (M j : ℝ)) * (N_star : ℝ) =
          ∑ a : ∀ j : Fin k, Fin (M j), ‖Fstar a‖ ^ 2 * ‖fAll a‖ ^ (2 * (s - k)) := by
        -- Use parseval_tuples on DistK × (Fin (s-k) → Fin P) embedded into (Fin s → ℤ)
        let eSplit : (Fin k ⊕ Fin (s - k)) ≃ Fin s :=
          (finSumFinEquiv).trans (finCongr (Nat.add_sub_of_le hsk.le))
        let Astar : Finset (Fin s → ℤ) :=
          (DistK ×ˢ (Finset.univ : Finset (Fin (s - k) → Fin P))).image fun p =>
            fun i => Sum.elim (fun j => ((p.1 j : ℕ) : ℤ)) (fun j => ((p.2 j : ℕ) : ℤ)) (eSplit.symm i)
        have hA_inj : Function.Injective (fun (p : (Fin k → Fin P) × (Fin (s - k) → Fin P)) =>
            fun i : Fin s => Sum.elim (fun j => ((p.1 j : ℕ) : ℤ)) (fun j => ((p.2 j : ℕ) : ℤ)) (eSplit.symm i)) := by
          intro a b h
          ext j
          · have := congrFun h (eSplit (Sum.inl j)); simp at this; exact_mod_cast this
          · have := congrFun h (eSplit (Sum.inr j)); simp at this; exact_mod_cast this
        have hA_sub : Astar ⊆ AllT.image embS := by
          intro z hz
          obtain ⟨p, _, rfl⟩ := mem_image.mp hz
          refine mem_image.mpr ⟨fun i => Sum.elim p.1 p.2 (eSplit.symm i), mem_univ _, ?_⟩
          ext i; dsimp only [embS]; rcases eSplit.symm i with j | j <;> rfl
        have hA_fit : ∀ x ∈ Astar, ∀ y ∈ Astar, ∀ j : Fin k,
            |(∑ i : Fin s, (x i) ^ (j.1 + 1)) - (∑ i : Fin s, (y i) ^ (j.1 + 1))| < (M j : ℤ) :=
          fun x hx y hy j => hfit x (hA_sub hx) y (hA_sub hy) j
        have hA_card : (((Astar ×ˢ Astar).filter fun xy =>
            ∀ j : Fin k, ∑ i : Fin s, (xy.1 i) ^ (j.1 + 1) = ∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)).card) = N_star := by
          let g : ((Fin k → Fin P) × (Fin (s - k) → Fin P) × (Fin k → Fin P) × (Fin (s - k) → Fin P)) →
              ((Fin s → ℤ) × (Fin s → ℤ)) := fun t =>
            (fun i => Sum.elim (fun j => ((t.1 j : ℕ) : ℤ)) (fun j => ((t.2.1 j : ℕ) : ℤ)) (eSplit.symm i),
             fun i => Sum.elim (fun j => ((t.2.2.1 j : ℕ) : ℤ)) (fun j => ((t.2.2.2 j : ℕ) : ℤ)) (eSplit.symm i))
          have hg_inj : Function.Injective g := fun a b h => by
            have h1 : (a.1, a.2.1) = (b.1, b.2.1) := hA_inj (congrArg Prod.fst h)
            have h2 : (a.2.2.1, a.2.2.2) = (b.2.2.1, b.2.2.2) := hA_inj (congrArg Prod.snd h)
            rcases Prod.mk.inj h1 with ⟨ha1, ha2⟩
            rcases Prod.mk.inj h2 with ⟨hb1, hb2⟩
            exact Prod.ext ha1 (Prod.ext ha2 (Prod.ext hb1 hb2))
          have himg : (((Finset.univ : Finset ((Fin k → Fin P) × (Fin (s - k) → Fin P) ×
              (Fin k → Fin P) × (Fin (s - k) → Fin P))).filter fun t =>
              t.1 ∈ DistK ∧ t.2.2.1 ∈ DistK ∧
              ∀ j : Fin k,
                (∑ i : Fin k, ((t.1 i : ℕ) : ℤ) ^ (j.1 + 1)) +
                  (∑ i : Fin (s - k), ((t.2.1 i : ℕ) : ℤ) ^ (j.1 + 1)) =
                (∑ i : Fin k, ((t.2.2.1 i : ℕ) : ℤ) ^ (j.1 + 1)) +
                  (∑ i : Fin (s - k), ((t.2.2.2 i : ℕ) : ℤ) ^ (j.1 + 1))).image g) =
              ((Astar ×ˢ Astar).filter fun xy =>
                ∀ j : Fin k, ∑ i : Fin s, (xy.1 i) ^ (j.1 + 1) = ∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)) := by
            have hsplit_sum : ∀ (u : Fin k → Fin P) (v : Fin (s - k) → Fin P) (j : Fin k),
                ∑ i : Fin s, (Sum.elim (fun m => ((u m : ℕ) : ℤ)) (fun m => ((v m : ℕ) : ℤ)) (eSplit.symm i)) ^ (j.1 + 1) =
                (∑ m : Fin k, ((u m : ℕ) : ℤ) ^ (j.1 + 1)) + (∑ m : Fin (s - k), ((v m : ℕ) : ℤ) ^ (j.1 + 1)) := by
              intro u v j
              rw [← eSplit.sum_comp (fun i => (Sum.elim (fun m => ((u m : ℕ) : ℤ)) (fun m => ((v m : ℕ) : ℤ)) (eSplit.symm i)) ^ (j.1 + 1))]
              simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
            ext ⟨x, y⟩
            simp only [mem_image, mem_filter, mem_univ, true_and, and_true, mem_product, Astar]
            constructor
            · rintro ⟨t, ⟨h1, h2, hsum⟩, hgeq⟩
              have hx : (g t).1 = x := congrArg Prod.fst hgeq
              have hy : (g t).2 = y := congrArg Prod.snd hgeq
              subst hx; subst hy
              refine ⟨⟨⟨(t.1, t.2.1), h1, rfl⟩, ⟨(t.2.2.1, t.2.2.2), h2, rfl⟩⟩, ?_⟩
              intro j; dsimp only [g]; rw [hsplit_sum, hsplit_sum]; exact hsum j
            · rintro ⟨⟨⟨⟨u1, v1⟩, hu1, rfl⟩, ⟨⟨u2, v2⟩, hu2, rfl⟩⟩, hsum⟩
              refine ⟨(u1, v1, u2, v2), ⟨hu1, hu2, fun j => ?_⟩, rfl⟩
              have hj := hsum j
              rwa [hsplit_sum, hsplit_sum] at hj
          rw [← himg, card_image_of_injective _ hg_inj]
        have hA_sum : ∀ a : ∀ j : Fin k, Fin (M j),
            (∑ x ∈ Astar, ∏ i : Fin s, weylChar k M a (x i)) = Fstar a * (fAll a) ^ (s - k) := by
          intro a
          rw [Finset.sum_image (fun _ _ _ _ h => hA_inj h)]
          have hterm : ∀ p : (Fin k → Fin P) × (Fin (s - k) → Fin P),
              (∏ i : Fin s, weylChar k M a (Sum.elim (fun j => ((p.1 j : ℕ) : ℤ))
                (fun j => ((p.2 j : ℕ) : ℤ)) (eSplit.symm i))) =
              (∏ j : Fin k, weylChar k M a ((p.1 j : ℕ) : ℤ)) *
              (∏ j : Fin (s - k), weylChar k M a ((p.2 j : ℕ) : ℤ)) := fun p => by
            rw [← eSplit.prod_comp (fun i => weylChar k M a (Sum.elim (fun j => ((p.1 j : ℕ) : ℤ))
              (fun j => ((p.2 j : ℕ) : ℤ)) (eSplit.symm i)))]
            simp only [Equiv.symm_apply_apply, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
          simp_rw [hterm]
          rw [Finset.sum_product]; dsimp only; rw [← Finset.sum_mul_sum]
          congr 1
          rw [← Fintype.prod_sum (fun (_ : Fin (s - k)) (x : Fin P) => weylChar k M a ((x : ℕ) : ℤ))]
          simp [fAll]
        have hp := parseval_tuples M hM Astar hA_fit
        rw [hA_card] at hp
        simp_rw [hA_sum, norm_mul, mul_pow, norm_pow, ← pow_mul, mul_comm (s - k) 2] at hp
        exact hp
      -- Split fAll a = ∑ r : Fin p, fRes r a and apply power-mean inequality
      have hfAll_eq : ∀ a, fAll a = ∑ r : Fin p, fRes r a := by
        intro a
        dsimp only [fAll, fRes]
        let modp : Fin P → Fin p := fun x => ⟨(x : ℕ) % p, Nat.mod_lt _ hp_pos⟩
        rw [← Finset.sum_fiberwise_of_maps_to (g := modp) (t := Finset.univ) (fun _ _ => mem_univ _)]
        refine sum_congr rfl fun r _ => ?_
        congr 1; ext x; simp [resClass, modp, Fin.ext_iff]
      have hfAll_pow : ∀ a : ∀ j : Fin k, Fin (M j),
          ‖fAll a‖ ^ (2 * (s - k)) ≤
            (p : ℝ) ^ (2 * (s - k) - 1) * ∑ r : Fin p, ‖fRes r a‖ ^ (2 * (s - k)) := by
        intro a
        by_cases hsk0 : s - k = 0
        · simp [hsk0]
          have : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_le
          linarith
        · have hge1 : (1 : ℝ) ≤ (2 * (s - k) : ℕ) := by exact_mod_cast (by omega : 1 ≤ 2 * (s - k))
          have htri : ‖fAll a‖ ≤ ∑ r : Fin p, ‖fRes r a‖ := by
            rw [hfAll_eq a]; exact norm_sum_le _ _
          have hrpow := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := (Finset.univ : Finset (Fin p)))
            (f := fun r => ‖fRes r a‖) hge1 (fun _ _ => norm_nonneg _)
          simp only [card_univ, Fintype.card_fin] at hrpow
          have hsub : ((2 * (s - k) : ℕ) : ℝ) - 1 = ((2 * (s - k) - 1 : ℕ) : ℝ) := by
            rw [Nat.cast_sub (by omega)]; simp
          rw [hsub, Real.rpow_natCast, Real.rpow_natCast] at hrpow
          simp_rw [Real.rpow_natCast] at hrpow
          exact (pow_le_pow_left₀ (norm_nonneg _) htri _).trans hrpow
      -- For each fixed r : Fin p, ∑_a ‖Fstar a‖^2 * ‖fRes r a‖^(2(s-k)) = (∏ M_j) * N_star_r
      have hNr_bound : ∀ r : Fin p,
          (∑ a : ∀ j : Fin k, Fin (M j), ‖Fstar a‖ ^ 2 * ‖fRes r a‖ ^ (2 * (s - k))) ≤
            (∏ j : Fin k, (M j : ℝ)) *
              ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) * (P : ℝ) ^ k * (J (s - k) k P₁ : ℝ)) := by
        intro r
        let eSplit : (Fin k ⊕ Fin (s - k)) ≃ Fin s :=
          (finSumFinEquiv).trans (finCongr (Nat.add_sub_of_le hsk.le))
        let Ar : Finset (Fin s → ℤ) :=
          (DistK ×ˢ (Finset.univ : Finset (Fin (s - k) → resClass r))).image fun t =>
            fun i => Sum.elim (fun j => ((t.1 j : ℕ) : ℤ)) (fun j => (((t.2 j).1 : ℕ) : ℤ)) (eSplit.symm i)
        have hAr_inj : Function.Injective (fun (t : (Fin k → Fin P) × (Fin (s - k) → resClass r)) =>
            fun i : Fin s => Sum.elim (fun j => ((t.1 j : ℕ) : ℤ)) (fun j => (((t.2 j).1 : ℕ) : ℤ)) (eSplit.symm i)) := by
          intro a b h
          ext j
          · have := congrFun h (eSplit (Sum.inl j)); simp at this; exact_mod_cast this
          · have := congrFun h (eSplit (Sum.inr j)); simp at this; exact_mod_cast this
        have hAr_sub : Ar ⊆ AllT.image embS := by
          intro z hz
          obtain ⟨t, _, rfl⟩ := mem_image.mp hz
          refine mem_image.mpr ⟨fun i => Sum.elim t.1 (fun j => (t.2 j).1) (eSplit.symm i), mem_univ _, ?_⟩
          ext i; dsimp only [embS]; rcases eSplit.symm i with j | j <;> rfl
        have hAr_fit : ∀ x ∈ Ar, ∀ y ∈ Ar, ∀ j : Fin k,
            |(∑ i : Fin s, (x i) ^ (j.1 + 1)) - (∑ i : Fin s, (y i) ^ (j.1 + 1))| < (M j : ℤ) :=
          fun x hx y hy j => hfit x (hAr_sub hx) y (hAr_sub hy) j
        have hAr_sum : ∀ a : ∀ j : Fin k, Fin (M j),
            (∑ x ∈ Ar, ∏ i : Fin s, weylChar k M a (x i)) = Fstar a * (fRes r a) ^ (s - k) := by
          intro a
          rw [Finset.sum_image (fun _ _ _ _ h => hAr_inj h)]
          have hterm : ∀ t : (Fin k → Fin P) × (Fin (s - k) → resClass r),
              (∏ i : Fin s, weylChar k M a (Sum.elim (fun j => ((t.1 j : ℕ) : ℤ))
                (fun j => (((t.2 j).1 : ℕ) : ℤ)) (eSplit.symm i))) =
              (∏ j : Fin k, weylChar k M a ((t.1 j : ℕ) : ℤ)) *
              (∏ j : Fin (s - k), weylChar k M a (((t.2 j).1 : ℕ) : ℤ)) := fun t => by
            rw [← eSplit.prod_comp (fun i => weylChar k M a (Sum.elim (fun j => ((t.1 j : ℕ) : ℤ))
              (fun j => (((t.2 j).1 : ℕ) : ℤ)) (eSplit.symm i)))]
            simp only [Equiv.symm_apply_apply, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
          simp_rw [hterm]
          rw [Finset.sum_product]; dsimp only; rw [← Finset.sum_mul_sum]
          congr 1
          rw [← Fintype.prod_sum (fun (_ : Fin (s - k)) (x : resClass r) => weylChar k M a ((x.1 : ℕ) : ℤ))]
          simp only [Finset.prod_const, card_univ, Fintype.card_fin]
          congr 1
          exact Finset.sum_coe_sort (resClass r) (fun u => weylChar k M a ((u : ℕ) : ℤ))
        have hparseval_r := parseval_tuples M hM Ar hAr_fit
        simp_rw [hAr_sum, norm_mul, mul_pow, norm_pow, ← pow_mul, mul_comm (s - k) 2] at hparseval_r
        rw [← hparseval_r]
        refine mul_le_mul_of_nonneg_left ?_ hprodM_pos.le
        -- Count physical solutions in Ar × Ar directly!
        let Sol_r := ((DistK ×ˢ (Finset.univ : Finset (Fin (s - k) → resClass r))) ×ˢ
            (DistK ×ˢ (Finset.univ : Finset (Fin (s - k) → resClass r)))).filter fun t =>
          ∀ j : Fin k,
            (∑ i : Fin k, ((t.1.1 i : ℕ) : ℤ) ^ (j.1 + 1)) +
              (∑ i : Fin (s - k), (((t.1.2 i).1 : ℕ) : ℤ) ^ (j.1 + 1)) =
            (∑ i : Fin k, ((t.2.1 i : ℕ) : ℤ) ^ (j.1 + 1)) +
              (∑ i : Fin (s - k), (((t.2.2 i).1 : ℕ) : ℤ) ^ (j.1 + 1))
        have hSol_eq : (((Ar ×ˢ Ar).filter fun xy =>
            ∀ j : Fin k, ∑ i : Fin s, (xy.1 i) ^ (j.1 + 1) = ∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)).card) =
            Sol_r.card := by
          let g : (((Fin k → Fin P) × (Fin (s - k) → resClass r)) ×
              ((Fin k → Fin P) × (Fin (s - k) → resClass r))) → ((Fin s → ℤ) × (Fin s → ℤ)) :=
            fun t =>
              (fun i => Sum.elim (fun j => ((t.1.1 j : ℕ) : ℤ)) (fun j => (((t.1.2 j).1 : ℕ) : ℤ)) (eSplit.symm i),
               fun i => Sum.elim (fun j => ((t.2.1 j : ℕ) : ℤ)) (fun j => (((t.2.2 j).1 : ℕ) : ℤ)) (eSplit.symm i))
          have hg_inj : Function.Injective g := fun a b h =>
            Prod.ext (hAr_inj (congrArg Prod.fst h)) (hAr_inj (congrArg Prod.snd h))
          have hsplit_sum : ∀ (u : Fin k → Fin P) (v : Fin (s - k) → resClass r) (j : Fin k),
              ∑ i : Fin s, (Sum.elim (fun m => ((u m : ℕ) : ℤ)) (fun m => (((v m).1 : ℕ) : ℤ)) (eSplit.symm i)) ^ (j.1 + 1) =
              (∑ m : Fin k, ((u m : ℕ) : ℤ) ^ (j.1 + 1)) + (∑ m : Fin (s - k), (((v m).1 : ℕ) : ℤ) ^ (j.1 + 1)) := by
            intro u v j
            rw [← eSplit.sum_comp (fun i => (Sum.elim (fun m => ((u m : ℕ) : ℤ)) (fun m => (((v m).1 : ℕ) : ℤ)) (eSplit.symm i)) ^ (j.1 + 1))]
            simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
          have himg : Sol_r.image g = ((Ar ×ˢ Ar).filter fun xy =>
              ∀ j : Fin k, ∑ i : Fin s, (xy.1 i) ^ (j.1 + 1) = ∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)) := by
            ext ⟨x, y⟩
            simp only [mem_image, mem_filter, mem_product, mem_univ, and_true, Sol_r, Ar]
            constructor
            · rintro ⟨t, ⟨⟨h1, h2⟩, hsum⟩, hgeq⟩
              have hx : (g t).1 = x := congrArg Prod.fst hgeq
              have hy : (g t).2 = y := congrArg Prod.snd hgeq
              subst hx; subst hy
              refine ⟨⟨⟨t.1, h1, rfl⟩, ⟨t.2, h2, rfl⟩⟩, fun j => ?_⟩
              dsimp only [g]; rw [hsplit_sum, hsplit_sum]; exact hsum j
            · rintro ⟨⟨⟨t1, h1, rfl⟩, ⟨t2, h2, rfl⟩⟩, hsum⟩
              refine ⟨(t1, t2), ⟨⟨h1, h2⟩, fun j => ?_⟩, rfl⟩
              have hj := hsum j; rwa [hsplit_sum, hsplit_sum] at hj
          rw [← himg, card_image_of_injective _ hg_inj]
        rw [hSol_eq]
        -- Fiberwise count over (x, y) ∈ DistK × DistK:
        -- 1. x has ≤ P^k choices
        -- 2. Given x, y must satisfy p^{j+1} ∣ ∑(y_i - r)^{j+1} - ∑(x_i - r)^{j+1} (≤ k! * p^{k(k-1)/2} choices!)
        -- 3. Given (x, y), (u, v) satisfies ∑ U_m^{j+1} - ∑ V_m^{j+1} = c_j(x, y) (≤ J (s-k) k P₁ choices!)
        let ValidXY := (DistK ×ˢ DistK).filter fun xy =>
          ∀ j : Fin k, ((p : ℤ) ^ (j.1 + 1)) ∣
            (∑ i : Fin k, (((xy.2 i : ℕ) : ℤ) - (r : ℤ)) ^ (j.1 + 1)) -
            (∑ i : Fin k, (((xy.1 i : ℕ) : ℤ) - (r : ℤ)) ^ (j.1 + 1))
        let projXY : (((Fin k → Fin P) × (Fin (s - k) → resClass r)) ×
            ((Fin k → Fin P) × (Fin (s - k) → resClass r))) → ((Fin k → Fin P) × (Fin k → Fin P)) :=
          fun t => (t.1.1, t.2.1)
        have hproj_mem : ∀ t ∈ Sol_r, projXY t ∈ ValidXY := by
          intro t ht
          have hmem := (mem_filter.mp ht).1
          have hsum := (mem_filter.mp ht).2
          have h1 : t.1.1 ∈ DistK := (mem_product.mp (mem_product.mp hmem).1).1
          have h2 : t.2.1 ∈ DistK := (mem_product.mp (mem_product.mp hmem).2).1
          refine mem_filter.mpr ⟨mem_product.mpr ⟨h1, h2⟩, ?_⟩
          -- Shift by -r using power_sums_shift_iff on the combined s-tuple
          let xFull : Fin s → ℤ := fun i =>
            Sum.elim (fun j => ((t.1.1 j : ℕ) : ℤ)) (fun j => (((t.1.2 j).1 : ℕ) : ℤ)) (eSplit.symm i)
          let yFull : Fin s → ℤ := fun i =>
            Sum.elim (fun j => ((t.2.1 j : ℕ) : ℤ)) (fun j => (((t.2.2 j).1 : ℕ) : ℤ)) (eSplit.symm i)
          have hsh := (power_sums_shift_iff (k := k) xFull yFull (-(r : ℤ))).mpr (fun (j : Fin k) => by
            have hsp : ∀ (u : Fin k → Fin P) (v : Fin (s - k) → resClass r),
                ∑ i : Fin s, (Sum.elim (fun m => ((u m : ℕ) : ℤ)) (fun m => (((v m).1 : ℕ) : ℤ)) (eSplit.symm i)) ^ (j.1 + 1) =
                (∑ m : Fin k, ((u m : ℕ) : ℤ) ^ (j.1 + 1)) + (∑ m : Fin (s - k), (((v m).1 : ℕ) : ℤ) ^ (j.1 + 1)) := by
              intro u v
              rw [← eSplit.sum_comp (fun i => (Sum.elim (fun m => ((u m : ℕ) : ℤ)) (fun m => (((v m).1 : ℕ) : ℤ)) (eSplit.symm i)) ^ (j.1 + 1))]
              simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
            dsimp only [xFull, yFull]
            rw [hsp, hsp]
            exact hsum j)
          intro j
          have hj := hsh j
          have hsp_sh : ∀ (u : Fin k → Fin P) (v : Fin (s - k) → resClass r),
              ∑ i : Fin s, (Sum.elim (fun m => ((u m : ℕ) : ℤ)) (fun m => (((v m).1 : ℕ) : ℤ)) (eSplit.symm i) + -(r : ℤ)) ^ (j.1 + 1) =
              (∑ m : Fin k, (((u m : ℕ) : ℤ) - (r : ℤ)) ^ (j.1 + 1)) +
              (p : ℤ) ^ (j.1 + 1) * (∑ m : Fin (s - k), ((((v m).1 : ℕ) / p : ℕ) : ℤ) ^ (j.1 + 1)) := by
            intro u v
            rw [← eSplit.sum_comp (fun i => (Sum.elim (fun m => ((u m : ℕ) : ℤ)) (fun m => (((v m).1 : ℕ) : ℤ)) (eSplit.symm i) + -(r : ℤ)) ^ (j.1 + 1))]
            simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
              ← sub_eq_add_neg]
            congr 1
            rw [Finset.mul_sum]
            refine sum_congr rfl fun m _ => ?_
            have hmod : ((v m).1 : ℕ) % p = (r : ℕ) := (mem_filter.mp (v m).2).2
            have hdm := Nat.div_add_mod ((v m).1 : ℕ) p
            rw [hmod] at hdm
            have hdmZ : (((p * (((v m).1 : ℕ) / p) + (r : ℕ) : ℕ) : ℤ)) = (((v m).1 : ℕ) : ℤ) := by
              exact_mod_cast hdm
            simp only [Nat.cast_add, Nat.cast_mul] at hdmZ
            have hsub : (((v m).1 : ℕ) : ℤ) - (r : ℤ) = (p : ℤ) * ((((v m).1 : ℕ) / p : ℕ) : ℤ) := by
              linarith
            rw [hsub, mul_pow]
          dsimp only [xFull, yFull] at hj
          rw [hsp_sh, hsp_sh] at hj
          refine ⟨(∑ m : Fin (s - k), ((((t.1.2 m).1 : ℕ) / p : ℕ) : ℤ) ^ (j.1 + 1)) -
                  (∑ m : Fin (s - k), ((((t.2.2 m).1 : ℕ) / p : ℕ) : ℤ) ^ (j.1 + 1)), ?_⟩
          linarith
        have hfiber_uv : ∀ xy ∈ ValidXY, (Sol_r.filter fun t => projXY t = xy).card ≤ J (s - k) k P₁ := by
          intro xy hxy
          have hcong := (mem_filter.mp hxy).2
          let c : Fin k → ℤ := fun j =>
            ((∑ i : Fin k, (((xy.2 i : ℕ) : ℤ) - (r : ℤ)) ^ (j.1 + 1)) -
             (∑ i : Fin k, (((xy.1 i : ℕ) : ℤ) - (r : ℤ)) ^ (j.1 + 1))) / ((p : ℤ) ^ (j.1 + 1))
          let toUV : (((Fin k → Fin P) × (Fin (s - k) → resClass r)) ×
              ((Fin k → Fin P) × (Fin (s - k) → resClass r))) →
              ((Fin (s - k) → Fin P₁) × (Fin (s - k) → Fin P₁)) := fun t =>
            (fun m => ⟨((t.1.2 m).1 : ℕ) / p, by
                have hx := (t.1.2 m).1.2
                have h1 : P ≤ P₁ * p := by
                  dsimp only [P₁]
                  have hdm := Nat.div_add_mod (P + p - 1) p
                  have hrem := Nat.mod_lt (P + p - 1) hp_pos
                  rw [mul_comm] at hdm
                  omega
                exact Nat.div_lt_of_lt_mul (lt_of_lt_of_le hx (by rwa [mul_comm] at h1))⟩,
             fun m => ⟨((t.2.2 m).1 : ℕ) / p, by
                have hx := (t.2.2 m).1.2
                have h1 : P ≤ P₁ * p := by
                  dsimp only [P₁]
                  have hdm := Nat.div_add_mod (P + p - 1) p
                  have hrem := Nat.mod_lt (P + p - 1) hp_pos
                  rw [mul_comm] at hdm
                  omega
                exact Nat.div_lt_of_lt_mul (lt_of_lt_of_le hx (by rwa [mul_comm] at h1))⟩)
          have htoUV_inj : Set.InjOn toUV (Sol_r.filter fun t => projXY t = xy) := by
            intro t₁ ht₁ t₂ ht₂ heq
            have hp1 : projXY t₁ = xy := (mem_filter.mp ht₁).2
            have hp2 : projXY t₂ = xy := (mem_filter.mp ht₂).2
            have hx_eq : t₁.1.1 = t₂.1.1 := by rw [show t₁.1.1 = (projXY t₁).1 from rfl, hp1, ← hp2]
            have hy_eq : t₁.2.1 = t₂.2.1 := by rw [show t₁.2.1 = (projXY t₁).2 from rfl, hp1, ← hp2]
            have hu_eq : t₁.1.2 = t₂.1.2 := by
              ext m
              have hdiv : ((t₁.1.2 m).1 : ℕ) / p = ((t₂.1.2 m).1 : ℕ) / p :=
                congrArg (fun z => (z.1 m : ℕ)) heq
              have hm1 : ((t₁.1.2 m).1 : ℕ) % p = (r : ℕ) := (mem_filter.mp (t₁.1.2 m).2).2
              have hm2 : ((t₂.1.2 m).1 : ℕ) % p = (r : ℕ) := (mem_filter.mp (t₂.1.2 m).2).2
              have hd1 := Nat.div_add_mod ((t₁.1.2 m).1 : ℕ) p
              have hd2 := Nat.div_add_mod ((t₂.1.2 m).1 : ℕ) p
              rw [← hd1, ← hd2, hdiv, hm1, hm2]
            have hv_eq : t₁.2.2 = t₂.2.2 := by
              ext m
              have hdiv : ((t₁.2.2 m).1 : ℕ) / p = ((t₂.2.2 m).1 : ℕ) / p :=
                congrArg (fun z => (z.2 m : ℕ)) heq
              have hm1 : ((t₁.2.2 m).1 : ℕ) % p = (r : ℕ) := (mem_filter.mp (t₁.2.2 m).2).2
              have hm2 : ((t₂.2.2 m).1 : ℕ) % p = (r : ℕ) := (mem_filter.mp (t₂.2.2 m).2).2
              have hd1 := Nat.div_add_mod ((t₁.2.2 m).1 : ℕ) p
              have hd2 := Nat.div_add_mod ((t₂.2.2 m).1 : ℕ) p
              rw [← hd1, ← hd2, hdiv, hm1, hm2]
            exact Prod.ext (Prod.ext hx_eq hu_eq) (Prod.ext hy_eq hv_eq)
          have himg_sub : ((Sol_r.filter fun t => projXY t = xy).image toUV) ⊆
              ((Finset.univ : Finset ((Fin (s - k) → Fin P₁) × (Fin (s - k) → Fin P₁))).filter fun uv =>
                ∀ j : Fin k, (∑ m : Fin (s - k), ((uv.1 m : ℕ) : ℤ) ^ (j.1 + 1)) -
                  (∑ m : Fin (s - k), ((uv.2 m : ℕ) : ℤ) ^ (j.1 + 1)) = c j) := by
            intro uv huv
            obtain ⟨t, ht, rfl⟩ := mem_image.mp huv
            have htSol := (mem_filter.mp ht).1
            have hpt : projXY t = xy := (mem_filter.mp ht).2
            have hsum := (mem_filter.mp htSol).2
            refine mem_filter.mpr ⟨mem_univ _, fun j => ?_⟩
            -- Shift by -r again
            let xFull : Fin s → ℤ := fun i =>
              Sum.elim (fun j => ((t.1.1 j : ℕ) : ℤ)) (fun j => (((t.1.2 j).1 : ℕ) : ℤ)) (eSplit.symm i)
            let yFull : Fin s → ℤ := fun i =>
              Sum.elim (fun j => ((t.2.1 j : ℕ) : ℤ)) (fun j => (((t.2.2 j).1 : ℕ) : ℤ)) (eSplit.symm i)
            have hsh := (power_sums_shift_iff (k := k) xFull yFull (-(r : ℤ))).mpr (fun (j' : Fin k) => by
              have hsp : ∀ (u : Fin k → Fin P) (v : Fin (s - k) → resClass r),
                  ∑ i : Fin s, (Sum.elim (fun m => ((u m : ℕ) : ℤ)) (fun m => (((v m).1 : ℕ) : ℤ)) (eSplit.symm i)) ^ (j'.1 + 1) =
                  (∑ m : Fin k, ((u m : ℕ) : ℤ) ^ (j'.1 + 1)) + (∑ m : Fin (s - k), (((v m).1 : ℕ) : ℤ) ^ (j'.1 + 1)) := by
                intro u v
                rw [← eSplit.sum_comp (fun i => (Sum.elim (fun m => ((u m : ℕ) : ℤ)) (fun m => (((v m).1 : ℕ) : ℤ)) (eSplit.symm i)) ^ (j'.1 + 1))]
                simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
              dsimp only [xFull, yFull]; rw [hsp, hsp]; exact hsum j')
            have hj := hsh j
            have hsp_sh : ∀ (u : Fin k → Fin P) (v : Fin (s - k) → resClass r),
                ∑ i : Fin s, (Sum.elim (fun m => ((u m : ℕ) : ℤ)) (fun m => (((v m).1 : ℕ) : ℤ)) (eSplit.symm i) + -(r : ℤ)) ^ (j.1 + 1) =
                (∑ m : Fin k, (((u m : ℕ) : ℤ) - (r : ℤ)) ^ (j.1 + 1)) +
                (p : ℤ) ^ (j.1 + 1) * (∑ m : Fin (s - k), ((((v m).1 : ℕ) / p : ℕ) : ℤ) ^ (j.1 + 1)) := by
              intro u v
              rw [← eSplit.sum_comp (fun i => (Sum.elim (fun m => ((u m : ℕ) : ℤ)) (fun m => (((v m).1 : ℕ) : ℤ)) (eSplit.symm i) + -(r : ℤ)) ^ (j.1 + 1))]
              simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
                ← sub_eq_add_neg]
              congr 1
              rw [Finset.mul_sum]
              refine sum_congr rfl fun m _ => ?_
              have hmod : ((v m).1 : ℕ) % p = (r : ℕ) := (mem_filter.mp (v m).2).2
              have hdm := Nat.div_add_mod ((v m).1 : ℕ) p
              rw [hmod] at hdm
              have hdmZ : (((p * (((v m).1 : ℕ) / p) + (r : ℕ) : ℕ) : ℤ)) = (((v m).1 : ℕ) : ℤ) := by
                exact_mod_cast hdm
              simp only [Nat.cast_add, Nat.cast_mul] at hdmZ
              have hsub : (((v m).1 : ℕ) : ℤ) - (r : ℤ) = (p : ℤ) * ((((v m).1 : ℕ) / p : ℕ) : ℤ) := by
                linarith
              rw [hsub, mul_pow]
            dsimp only [xFull, yFull] at hj
            rw [hsp_sh, hsp_sh] at hj
            have ht1 : t.1.1 = xy.1 := congrArg Prod.fst hpt
            have ht2 : t.2.1 = xy.2 := congrArg Prod.snd hpt
            rw [ht1, ht2] at hj
            have hmul : (p : ℤ) ^ (j.1 + 1) *
                ((∑ m : Fin (s - k), ((((t.1.2 m).1 : ℕ) / p : ℕ) : ℤ) ^ (j.1 + 1)) -
                 (∑ m : Fin (s - k), ((((t.2.2 m).1 : ℕ) / p : ℕ) : ℤ) ^ (j.1 + 1))) =
                (p : ℤ) ^ (j.1 + 1) * c j := by
              rw [Int.mul_ediv_cancel' (hcong j)]
              linarith
            exact mul_left_cancel₀ (pow_ne_zero (j.1 + 1) (Int.natCast_ne_zero.mpr hp.ne_zero)) hmul
          calc (Sol_r.filter fun t => projXY t = xy).card
              = ((Sol_r.filter fun t => projXY t = xy).image toUV).card :=
                (card_image_of_injOn htoUV_inj).symm
            _ ≤ _ := card_le_card himg_sub
            _ ≤ J (s - k) k P₁ := card_shifted_solutions_le_J c
        have hValid_card : ValidXY.card ≤ P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) := by
          have hfib : ∀ x ∈ DistK, (ValidXY.filter fun xy => xy.1 = x).card ≤
              k.factorial * p ^ (k * (k - 1) / 2) := by
            intro x _
            have hsub : ((ValidXY.filter fun xy => xy.1 = x).image Prod.snd) ⊆
                ((Finset.univ : Finset (Fin k → Fin P)).filter fun y =>
                  (∀ i j : Fin k, i ≠ j → (y i : ℕ) % p ≠ (y j : ℕ) % p) ∧
                  (∀ j : Fin k, ((p : ℤ) ^ (j.1 + 1)) ∣
                    (∑ i : Fin k, (((y i : ℕ) : ℤ) - (r : ℤ)) ^ (j.1 + 1)) -
                    (∑ i : Fin k, (((x i : ℕ) : ℤ) - (r : ℤ)) ^ (j.1 + 1)))) := by
              intro y hy
              obtain ⟨xy, hxy, rfl⟩ := mem_image.mp hy
              have hxyV := (mem_filter.mp hxy).1
              have hx1 : xy.1 = x := (mem_filter.mp hxy).2
              have hyD : xy.2 ∈ DistK := (mem_product.mp (mem_filter.mp hxyV).1).2
              have hcong := (mem_filter.mp hxyV).2
              rw [hx1] at hcong
              exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hyD).2, hcong⟩
            calc (ValidXY.filter fun xy => xy.1 = x).card
                = ((ValidXY.filter fun xy => xy.1 = x).image Prod.snd).card :=
                  (card_image_of_injOn (fun a ha b hb h2 =>
                    Prod.ext ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm) h2)).symm
              _ ≤ _ := card_le_card hsub
              _ ≤ k.factorial * p ^ (k * (k - 1) / 2) :=
                  hensel_shifted_box_card_le hk hp hkp hPpk r.2 _
          calc ValidXY.card = ∑ x ∈ DistK, (ValidXY.filter fun xy => xy.1 = x).card :=
                Finset.card_eq_sum_card_fiberwise (fun xy hxy => (mem_product.mp (mem_filter.mp hxy).1).1)
            _ ≤ ∑ _x ∈ DistK, (k.factorial * p ^ (k * (k - 1) / 2)) := sum_le_sum hfib
            _ = DistK.card * (k.factorial * p ^ (k * (k - 1) / 2)) := by simp
            _ ≤ P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) :=
                Nat.mul_le_mul_right _ ((card_le_card (subset_univ _)).trans (by simp))
        have hSol_card : Sol_r.card ≤ P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) * J (s - k) k P₁ := by
          calc Sol_r.card = ∑ xy ∈ ValidXY, (Sol_r.filter fun t => projXY t = xy).card :=
                Finset.card_eq_sum_card_fiberwise hproj_mem
            _ ≤ ∑ _xy ∈ ValidXY, J (s - k) k P₁ := sum_le_sum hfiber_uv
            _ = ValidXY.card * J (s - k) k P₁ := by simp
            _ ≤ P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) * J (s - k) k P₁ :=
                Nat.mul_le_mul_right _ hValid_card
        have hSol_R : (Sol_r.card : ℝ) ≤
            (k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) * (P : ℝ) ^ k * (J (s - k) k P₁ : ℝ) := by
          have : (Sol_r.card : ℝ) ≤
              ((P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) * J (s - k) k P₁ : ℕ) : ℝ) := by
            exact_mod_cast hSol_card
          push_cast at this
          linarith
        exact hSol_R
      -- Combine hfAll_pow and hNr_bound
      have htot : (∏ j : Fin k, (M j : ℝ)) * (N_star : ℝ) ≤
          (∏ j : Fin k, (M j : ℝ)) *
            ((k.factorial : ℝ) * (p : ℝ) ^ (2 * (s - k) + k * (k - 1) / 2) * (P : ℝ) ^ k * (J (s - k) k P₁ : ℝ)) := by
        rw [hNstar_freq]
        calc ∑ a : ∀ j : Fin k, Fin (M j), ‖Fstar a‖ ^ 2 * ‖fAll a‖ ^ (2 * (s - k))
            ≤ ∑ a : ∀ j : Fin k, Fin (M j), ‖Fstar a‖ ^ 2 *
                ((p : ℝ) ^ (2 * (s - k) - 1) * ∑ r : Fin p, ‖fRes r a‖ ^ (2 * (s - k))) :=
              sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hfAll_pow a) (sq_nonneg _)
          _ = (p : ℝ) ^ (2 * (s - k) - 1) *
                ∑ r : Fin p, ∑ a : ∀ j : Fin k, Fin (M j), ‖Fstar a‖ ^ 2 * ‖fRes r a‖ ^ (2 * (s - k)) := by
              have h1 : ∑ a : ∀ j : Fin k, Fin (M j), ‖Fstar a‖ ^ 2 *
                  ((p : ℝ) ^ (2 * (s - k) - 1) * ∑ r : Fin p, ‖fRes r a‖ ^ (2 * (s - k))) =
                  ∑ a : ∀ j : Fin k, Fin (M j), ∑ r : Fin p,
                    (p : ℝ) ^ (2 * (s - k) - 1) * (‖Fstar a‖ ^ 2 * ‖fRes r a‖ ^ (2 * (s - k))) := by
                refine sum_congr rfl fun a _ => ?_
                rw [Finset.mul_sum, Finset.mul_sum]
                refine sum_congr rfl fun r _ => by ring
              rw [h1, Finset.sum_comm, Finset.mul_sum]
              refine sum_congr rfl fun r _ => (Finset.mul_sum _ _ _).symm
          _ ≤ (p : ℝ) ^ (2 * (s - k) - 1) *
                ∑ _r : Fin p, (∏ j : Fin k, (M j : ℝ)) *
                  ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) * (P : ℝ) ^ k * (J (s - k) k P₁ : ℝ)) :=
              mul_le_mul_of_nonneg_left (sum_le_sum fun r _ => hNr_bound r) (by positivity)
          _ = (∏ j : Fin k, (M j : ℝ)) *
                ((k.factorial : ℝ) * ((p : ℝ) ^ (2 * (s - k) - 1) * (p : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2)) *
                  (P : ℝ) ^ k * (J (s - k) k P₁ : ℝ)) := by
              simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
          _ = (∏ j : Fin k, (M j : ℝ)) *
                ((k.factorial : ℝ) * (p : ℝ) ^ (2 * (s - k) + k * (k - 1) / 2) * (P : ℝ) ^ k * (J (s - k) k P₁ : ℝ)) := by
              have hpow : (p : ℝ) ^ (2 * (s - k) - 1) * (p : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) =
                  (p : ℝ) ^ (2 * (s - k) + k * (k - 1) / 2) := by
                rw [← pow_succ, Nat.sub_add_cancel (by omega), ← pow_add]
              rw [hpow]
      exact le_of_mul_le_mul_left htot hprodM_pos
    have hNgood_R : (N_good : ℝ) ≤ (s : ℝ) ^ (2 * k) * (N_star : ℝ) := by
      exact_mod_cast hNgood_le
    calc (N_good : ℝ) ≤ (s : ℝ) ^ (2 * k) * (N_star : ℝ) := hNgood_R
      _ ≤ (s : ℝ) ^ (2 * k) * ((k.factorial : ℝ) * (p : ℝ) ^ (2 * (s - k) + k * (k - 1) / 2) *
            (P : ℝ) ^ k * (J (s - k) k P₁ : ℝ)) :=
          mul_le_mul_of_nonneg_left hNstar_bound (by positivity)
      _ = (s : ℝ) ^ (2 * k) * (k.factorial : ℝ) *
            (p : ℝ) ^ (2 * (s - k) + k * (k - 1) / 2) * (P : ℝ) ^ k * (J (s - k) k P₁ : ℝ) := by ring
  have hcomb : (∏ j : Fin k, (M j : ℝ)) * (J s k P : ℝ) ≤
      (∏ j : Fin k, (M j : ℝ)) *
        (2 * ((p : ℝ) ^ (k - 1) * ((k - 1 : ℕ) : ℝ) ^ s) ^ 2 * (J s k P₁ : ℝ) +
         2 * (s : ℝ) ^ (2 * k) * (k.factorial : ℝ) *
           (p : ℝ) ^ (2 * (s - k) + k * (k - 1) / 2) * (P : ℝ) ^ k * (J (s - k) k P₁ : ℝ)) := by
    calc (∏ j : Fin k, (M j : ℝ)) * (J s k P : ℝ)
        ≤ 2 * (∑ a : ∀ j : Fin k, Fin (M j), ‖Fset BadT a‖ ^ 2) +
          2 * (∑ a : ∀ j : Fin k, Fin (M j), ‖Fset GoodT a‖ ^ 2) := hJ_split
      _ ≤ 2 * ((∏ j : Fin k, (M j : ℝ)) *
            (((p : ℝ) ^ (k - 1) * ((k - 1 : ℕ) : ℝ) ^ s) ^ 2 * (J s k P₁ : ℝ))) +
          2 * ((∏ j : Fin k, (M j : ℝ)) *
            ((s : ℝ) ^ (2 * k) * (k.factorial : ℝ) *
              (p : ℝ) ^ (2 * (s - k) + k * (k - 1) / 2) * (P : ℝ) ^ k * (J (s - k) k P₁ : ℝ))) :=
          add_le_add (mul_le_mul_of_nonneg_left hBad_bound zero_le_two)
            (mul_le_mul_of_nonneg_left hGood_bound zero_le_two)
      _ = _ := by ring
  exact le_of_mul_le_mul_left hcomb hprodM_pos

/-- Elementary exponential bound: `(1 + 1 / (4 * s)) ^ (2 * s) ≤ 2` for `s ≥ 1`. -/
private lemma one_add_inv_pow_le_two {s : ℕ} (hs : 1 ≤ s) :
    (1 + 1 / (4 * (s : ℝ))) ^ (2 * s) ≤ 2 := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have hle : 1 + 1 / (4 * (s : ℝ)) ≤ Real.exp (1 / (4 * (s : ℝ))) := by
    linarith [Real.add_one_le_exp (1 / (4 * (s : ℝ)))]
  calc (1 + 1 / (4 * (s : ℝ))) ^ (2 * s)
      ≤ (Real.exp (1 / (4 * (s : ℝ)))) ^ (2 * s) := pow_le_pow_left₀ (by positivity) hle _
    _ = Real.exp (((2 * s : ℕ) : ℝ) * (1 / (4 * (s : ℝ)))) := (Real.exp_nat_mul _ _).symm
    _ = Real.exp (1 / 2) := by
        congr 1; push_cast; field_simp [hspos.ne']; ring
    _ ≤ 2 := by
        have h1 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        have h2 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
        nlinarith [Real.exp_pos (1 / 2)]

set_option maxHeartbeats 1200000 in
/-- Vinogradov's Mean Value Theorem (classical `p`-adic recursion):
    for `k ≥ 4`, `l : ℕ`, `s = k^2 + k * l`, and `P ≥ 1`:
    `J(s, k, P) ≤ (4 * s) ^ (4 * k^2 * l + 8 * k^3) * P ^ (2s - k(k+1)/2 + (k(k+1)/2)*(1 - 1/k)^l)`. -/
theorem vinogradov_mvt {k : ℕ} (hk : 4 ≤ k) :
    ∀ (l P : ℕ), 1 ≤ P →
      let s := k ^ 2 + k * l
      (J s k P : ℝ) ≤
        ((4 * (s : ℝ)) ^ (4 * k ^ 2 * l + 8 * k ^ 3)) *
        (P : ℝ) ^ (2 * (s : ℝ) - ((k * (k + 1) : ℕ) : ℝ) / 2 +
          (((k * (k + 1) : ℕ) : ℝ) / 2) * (1 - 1 / (k : ℝ)) ^ l) := by
  intro l
  induction l with
  | zero =>
    intro P hP s
    have hPpos : (0 : ℝ) < P := by exact_mod_cast hP
    have hs_pos : 1 ≤ s := by dsimp [s]; nlinarith
    have hC_ge1 : (1 : ℝ) ≤ (4 * (s : ℝ)) ^ (4 * k ^ 2 * 0 + 8 * k ^ 3) := by
      have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs_pos
      exact one_le_pow₀ (by linarith)
    have hexp : 2 * (s : ℝ) - ((k * (k + 1) : ℕ) : ℝ) / 2 +
        (((k * (k + 1) : ℕ) : ℝ) / 2) * (1 - 1 / (k : ℝ)) ^ 0 = ((2 * s : ℕ) : ℝ) := by
      simp
    rw [hexp, Real.rpow_natCast]
    calc (J s k P : ℝ) ≤ (P : ℝ) ^ (2 * s) := by exact_mod_cast J_triv s k P
      _ = 1 * (P : ℝ) ^ (2 * s) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hC_ge1 (by positivity)
  | succ l ihl =>
    intro P
    induction P using Nat.strong_induction_on with
    | h P ihP =>
      intro hP
      let s := k ^ 2 + k * (l + 1)
      let s₀ := k ^ 2 + k * l
      have hs_eq : s = s₀ + k := by dsimp [s, s₀]; ring
      have hs_sub : s - k = s₀ := by omega
      have hsk_strict : k < s := by dsimp [s]; nlinarith
      have hPpos : (0 : ℝ) < P := by exact_mod_cast hP
      have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
      have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
      have hkpos : (0 : ℝ) < k := by linarith
      have hspos : (16 : ℝ) ≤ s := by
        have : 16 ≤ s := by dsimp [s]; nlinarith
        exact_mod_cast this
      let Δ : ℝ := ((k * (k + 1) : ℕ) : ℝ) / 2
      have hΔ_nn : 0 ≤ Δ := by dsimp [Δ]; positivity
      have h1mk : 0 ≤ 1 - 1 / (k : ℝ) := by
        have : 1 / (k : ℝ) ≤ 1 := div_le_one_of_le₀ (by linarith) hkpos.le
        linarith
      have h1mk_le1 : 1 - 1 / (k : ℝ) ≤ 1 := by
        have : 0 ≤ 1 / (k : ℝ) := by positivity
        linarith
      let δ₁ : ℝ := Δ * (1 - 1 / (k : ℝ)) ^ (l + 1)
      let δ₀ : ℝ := Δ * (1 - 1 / (k : ℝ)) ^ l
      have hδ₁_le : δ₁ ≤ Δ := by
        dsimp only [δ₁]
        exact mul_le_of_le_one_right hΔ_nn (pow_le_one₀ h1mk h1mk_le1)
      have hδ₀_le : δ₀ ≤ Δ := by
        dsimp only [δ₀]
        exact mul_le_of_le_one_right hΔ_nn (pow_le_one₀ h1mk h1mk_le1)
      have hδ₁_nn : 0 ≤ δ₁ := by dsimp [δ₁]; positivity
      have hδ₀_nn : 0 ≤ δ₀ := by dsimp [δ₀]; positivity
      let C₁ : ℝ := (4 * (s : ℝ)) ^ (4 * k ^ 2 * (l + 1) + 8 * k ^ 3)
      let C₀ : ℝ := (4 * (s₀ : ℝ)) ^ (4 * k ^ 2 * l + 8 * k ^ 3)
      change (J s k P : ℝ) ≤ C₁ * (P : ℝ) ^ (2 * (s : ℝ) - Δ + δ₁)
      -- Split into Small P vs Large P
      by_cases hPsmall : (P : ℝ) < (4 * (s : ℝ)) ^ (4 * l + 8 * k)
      · -- Small P: trivial bound J s k P ≤ P^{2s}
        have hΔ_le_k2 : Δ ≤ (k : ℝ) ^ 2 := by
          dsimp only [Δ]; push_cast; nlinarith
        have hgap : Δ - δ₁ ≤ (k : ℝ) ^ 2 := by linarith
        have hgap_nn : 0 ≤ Δ - δ₁ := by linarith
        have hP_gap : (P : ℝ) ^ (Δ - δ₁) ≤ C₁ := by
          calc (P : ℝ) ^ (Δ - δ₁)
              ≤ ((4 * (s : ℝ)) ^ (4 * l + 8 * k)) ^ (Δ - δ₁) :=
                Real.rpow_le_rpow hPpos.le hPsmall.le hgap_nn
            _ ≤ ((4 * (s : ℝ)) ^ (4 * l + 8 * k)) ^ ((k : ℝ) ^ 2) := by
                have hbase1 : (1 : ℝ) ≤ (4 * (s : ℝ)) ^ (4 * l + 8 * k) :=
                  one_le_pow₀ (by linarith)
                exact Real.rpow_le_rpow_of_exponent_le hbase1 hgap
            _ = (4 * (s : ℝ)) ^ (((4 * l + 8 * k : ℕ) : ℝ) * ((k ^ 2 : ℕ) : ℝ)) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
                push_cast; rfl
            _ = (4 * (s : ℝ)) ^ ((4 * l + 8 * k) * k ^ 2) := by
                rw [← Nat.cast_mul, Real.rpow_natCast]
            _ ≤ C₁ := by
                dsimp only [C₁]
                have hexp_le : (4 * l + 8 * k) * k ^ 2 ≤ 4 * k ^ 2 * (l + 1) + 8 * k ^ 3 := by
                  nlinarith
                exact pow_le_pow_right₀ (by linarith) hexp_le
        calc (J s k P : ℝ) ≤ (P : ℝ) ^ (2 * s) := by exact_mod_cast J_triv s k P
          _ = (P : ℝ) ^ ((2 * (s : ℝ))) := by rw [← Real.rpow_natCast]; push_cast; rfl
          _ = (P : ℝ) ^ (Δ - δ₁) * (P : ℝ) ^ (2 * (s : ℝ) - Δ + δ₁) := by
              rw [← Real.rpow_add hPpos]; congr 1; ring
          _ ≤ C₁ * (P : ℝ) ^ (2 * (s : ℝ) - Δ + δ₁) :=
              mul_le_mul_of_nonneg_right hP_gap (Real.rpow_nonneg hPpos.le _)
      · -- Large P: P ≥ (4 * s) ^ (4 * l + 8 * k)
        push Not at hPsmall
        -- Pick prime p ∈ (Q, 2Q] with Q = ⌈P^{1/k}⌉ via Bertrand's postulate
        let Q : ℕ := Nat.ceil ((P : ℝ) ^ (1 / (k : ℝ)))
        have hP_rpow_ge : (4 * (s : ℝ)) ^ (4 * (l : ℝ) / (k : ℝ) + 8) ≤ (P : ℝ) ^ (1 / (k : ℝ)) := by
          have h1 := Real.rpow_le_rpow (by positivity) hPsmall (show (0 : ℝ) ≤ 1 / (k : ℝ) by positivity)
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)] at h1
          have hexp : ((4 * l + 8 * k : ℕ) : ℝ) * (1 / (k : ℝ)) = 4 * (l : ℝ) / (k : ℝ) + 8 := by
            push_cast; field_simp [hkpos.ne']
          rwa [hexp] at h1
        have hP_rpow_ge4 : (4 * (s : ℝ)) ^ 8 ≤ (P : ℝ) ^ (1 / (k : ℝ)) := by
          refine le_trans ?_ hP_rpow_ge
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by
            have : (0 : ℝ) ≤ 4 * (l : ℝ) / (k : ℝ) := by positivity
            push_cast; linarith)
        have hQ_ge : (P : ℝ) ^ (1 / (k : ℝ)) ≤ (Q : ℝ) := Nat.le_ceil _
        have hQ_pos : 1 ≤ Q := by
          have : (1 : ℝ) ≤ (Q : ℝ) := by
            have h48 : (1 : ℝ) ≤ (4 * (s : ℝ)) ^ 8 := one_le_pow₀ (by linarith)
            linarith
          exact_mod_cast this
        obtain ⟨p, hp_prime, hQp, hp2Q⟩ := Nat.exists_prime_lt_and_le_two_mul Q (by omega)
        have hkp : k < p := by
          have h1 : (k : ℝ) < (4 * (s : ℝ)) ^ 8 := by
            have hs_ge_k : (k : ℝ) ≤ s := by
              have : k ≤ s := by dsimp [s]; nlinarith
              exact_mod_cast this
            have h4s : (4 : ℝ) * s ≤ (4 * (s : ℝ)) ^ 8 := le_self_pow₀ (by linarith) (by omega)
            linarith
          have h2 : (k : ℝ) < (p : ℝ) := lt_of_lt_of_le (lt_of_lt_of_le h1 hP_rpow_ge4)
            (hQ_ge.trans (by exact_mod_cast hQp.le))
          exact_mod_cast h2
        have hPpk : P ≤ p ^ k := by
          have h1 : (P : ℝ) ≤ (Q : ℝ) ^ k := by
            have := pow_le_pow_left₀ (Real.rpow_nonneg hPpos.le _) hQ_ge k
            rw [← Real.rpow_natCast, ← Real.rpow_mul hPpos.le] at this
            have hinv : 1 / (k : ℝ) * (k : ℝ) = 1 := one_div_mul_cancel hkpos.ne'
            rw [hinv, Real.rpow_one] at this
            exact this
          have h2 : (Q : ℝ) ^ k ≤ (p : ℝ) ^ k :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hQp.le) k
          exact_mod_cast (h1.trans h2)
        have hp_le_3 : (p : ℝ) ≤ 3 * (P : ℝ) ^ (1 / (k : ℝ)) := by
          have hQ_lt : (Q : ℝ) < (P : ℝ) ^ (1 / (k : ℝ)) + 1 := Nat.ceil_lt_add_one (Real.rpow_nonneg hPpos.le _)
          have h2Q : (p : ℝ) ≤ 2 * (Q : ℝ) := by exact_mod_cast hp2Q
          have h2le : (2 : ℝ) ≤ (P : ℝ) ^ (1 / (k : ℝ)) := by
            have h48 : (2 : ℝ) ≤ (4 * (s : ℝ)) ^ 8 := by
              calc (2 : ℝ) ≤ 4 * (s : ℝ) := by linarith
                _ ≤ (4 * (s : ℝ)) ^ 8 := le_self_pow₀ (by linarith) (by omega)
            linarith
          linarith
        have hp_ge_rpow : (P : ℝ) ^ (1 / (k : ℝ)) ≤ (p : ℝ) :=
          hQ_ge.trans (by exact_mod_cast hQp.le)
        let P₁ : ℕ := (P + p - 1) / p
        have hP₁_pos : 1 ≤ P₁ := by
          dsimp only [P₁]
          exact Nat.div_pos (by omega) hp_prime.pos
        have hP₁_lt : P₁ < P := by
          dsimp only [P₁]
          have hp2 : 2 ≤ p := hp_prime.two_le
          have hP2 : 2 ≤ P := by
            have : (2 : ℝ) ≤ (P : ℝ) := by
              have h1 : (2 : ℝ) ≤ (4 * (s : ℝ)) ^ (4 * l + 8 * k) := by
                calc (2 : ℝ) ≤ 4 * (s : ℝ) := by linarith
                  _ ≤ (4 * (s : ℝ)) ^ (4 * l + 8 * k) := le_self_pow₀ (by linarith) (by omega)
              linarith
            exact_mod_cast this
          have hmul : P + p ≤ p * P := by nlinarith
          exact Nat.div_lt_of_lt_mul (by omega)
        have hP₁_le : (P₁ : ℝ) ≤ (1 + 1 / (4 * (s : ℝ))) * ((P : ℝ) / (p : ℝ)) := by
          have hP₁_up : (P₁ : ℝ) ≤ (P : ℝ) / (p : ℝ) + 1 := by
            have h1 : P₁ * p ≤ P + p - 1 := Nat.div_mul_le_self (P + p - 1) p
            have h2 : (P₁ : ℝ) * (p : ℝ) ≤ (P : ℝ) + (p : ℝ) := by
              have h1' : P₁ * p ≤ P + p := by omega
              exact_mod_cast h1'
            have hpposR : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
            rw [le_iff_lt_or_eq] at h2
            rw [div_add_one hpposR.ne', le_div_iff₀ hpposR]
            rcases h2 with hlt | heq <;> linarith
          -- Show 1 ≤ (1 / (4 * s)) * (P / p), i.e., 4 * s * p ≤ P
          have h4sp : 4 * (s : ℝ) * (p : ℝ) ≤ (P : ℝ) := by
            have hP_ge_p3 : (P : ℝ) ^ (1 / (k : ℝ)) * (P : ℝ) ^ (1 / (k : ℝ)) ≤ (P : ℝ) := by
              rw [← Real.rpow_add hPpos]
              have hexp : 1 / (k : ℝ) + 1 / (k : ℝ) ≤ 1 := by
                have h2k : 2 / (k : ℝ) ≤ 1 := (div_le_one hkpos).mpr (by linarith)
                have hsum : 1 / (k : ℝ) + 1 / (k : ℝ) = 2 / (k : ℝ) := by ring
                linarith
              simpa using Real.rpow_le_rpow_of_exponent_le hP1 hexp
            have h4s3 : 12 * (s : ℝ) ≤ (P : ℝ) ^ (1 / (k : ℝ)) := by
              have h1 : 12 * (s : ℝ) ≤ (4 * (s : ℝ)) ^ 8 := by
                have h4s2 : (4 * (s : ℝ)) ^ 2 ≤ (4 * (s : ℝ)) ^ 8 :=
                  pow_le_pow_right₀ (by linarith) (by omega)
                nlinarith
              linarith
            nlinarith [Real.rpow_nonneg hPpos.le (1 / (k : ℝ))]
          have hpposR : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
          have h1le : 1 ≤ (1 / (4 * (s : ℝ))) * ((P : ℝ) / (p : ℝ)) := by
            rw [one_div_mul_eq_div, div_div, one_le_div (by positivity)]
            linarith [h4sp]
          linarith
        -- Apply J_padic_step!
        have hstep := J_padic_step (s := s) (k := k) (P := P) (p := p)
          (by omega) hsk_strict hP hp_prime hkp hPpk
        change (J s k P : ℝ) ≤
          2 * ((p : ℝ) ^ (k - 1) * ((k - 1 : ℕ) : ℝ) ^ s) ^ 2 * (J s k P₁ : ℝ) +
          2 * (s : ℝ) ^ (2 * k) * (k.factorial : ℝ) *
            (p : ℝ) ^ (2 * (s - k) + k * (k - 1) / 2) * (P : ℝ) ^ k * (J (s - k) k P₁ : ℝ) at hstep
        -- Bound Term 1 (Bad) ≤ (1/2) * C₁ * P^{2s - Δ + δ₁} using ihP
        have hTerm1 : 2 * ((p : ℝ) ^ (k - 1) * ((k - 1 : ℕ) : ℝ) ^ s) ^ 2 * (J s k P₁ : ℝ) ≤
            (1 / 2) * C₁ * (P : ℝ) ^ (2 * (s : ℝ) - Δ + δ₁) := by
          have hihP := ihP P₁ hP₁_lt hP₁_pos
          change (J s k P₁ : ℝ) ≤ C₁ * (P₁ : ℝ) ^ (2 * (s : ℝ) - Δ + δ₁) at hihP
          have hE_pos : 0 ≤ 2 * (s : ℝ) - Δ + δ₁ := by
            have : Δ ≤ (k : ℝ) ^ 2 := by dsimp [Δ]; push_cast; nlinarith
            have hsk2 : (k : ℝ) ^ 2 ≤ s := by
              have : k ^ 2 ≤ s := by dsimp [s]; omega
              exact_mod_cast this
            linarith
          have hE_le2s : 2 * (s : ℝ) - Δ + δ₁ ≤ (2 * s : ℕ) := by
            push_cast; linarith
          have hP₁_pow : (P₁ : ℝ) ^ (2 * (s : ℝ) - Δ + δ₁) ≤
              2 * ((P : ℝ) / (p : ℝ)) ^ (2 * (s : ℝ) - Δ + δ₁) := by
            calc (P₁ : ℝ) ^ (2 * (s : ℝ) - Δ + δ₁)
                ≤ ((1 + 1 / (4 * (s : ℝ))) * ((P : ℝ) / (p : ℝ))) ^ (2 * (s : ℝ) - Δ + δ₁) :=
                  Real.rpow_le_rpow (Nat.cast_nonneg _) hP₁_le hE_pos
              _ = (1 + 1 / (4 * (s : ℝ))) ^ (2 * (s : ℝ) - Δ + δ₁) *
                  ((P : ℝ) / (p : ℝ)) ^ (2 * (s : ℝ) - Δ + δ₁) :=
                  Real.mul_rpow (by positivity) (by positivity)
              _ ≤ (1 + 1 / (4 * (s : ℝ))) ^ ((2 * s : ℕ) : ℝ) *
                  ((P : ℝ) / (p : ℝ)) ^ (2 * (s : ℝ) - Δ + δ₁) := by
                  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
                  exact Real.rpow_le_rpow_of_exponent_le (by linarith [show (0 : ℝ) ≤ 1 / (4 * (s : ℝ)) by positivity]) hE_le2s
              _ ≤ 2 * ((P : ℝ) / (p : ℝ)) ^ (2 * (s : ℝ) - Δ + δ₁) := by
                  rw [Real.rpow_natCast]
                  exact mul_le_mul_of_nonneg_right (one_add_inv_pow_le_two (by dsimp [s]; nlinarith))
                    (Real.rpow_nonneg (by positivity) _)
          have hpposR : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
          have hp_exp_le : (p : ℝ) ^ (2 * (k - 1)) / (p : ℝ) ^ (2 * (s : ℝ) - Δ + δ₁) ≤
              ((p : ℝ) ^ (k ^ 2))⁻¹ := by
            rw [div_le_iff₀ (Real.rpow_pos_of_pos hpposR _), inv_mul_eq_div,
              le_div_iff₀ (pow_pos hpposR _), ← pow_add, ← Real.rpow_natCast]
            refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp_prime.one_le) ?_
            have h1 : (2 * (k - 1) + k ^ 2 : ℕ) = k ^ 2 + 2 * k - 2 := by omega
            have h2 : ((2 * (k - 1) + k ^ 2 : ℕ) : ℝ) ≤ (k : ℝ) ^ 2 + 2 * (k : ℝ) - 2 := by
              rw [h1, Nat.cast_sub (by nlinarith)]; push_cast; linarith
            have hΔ_eq : Δ = (k : ℝ) * ((k : ℝ) + 1) / 2 := by dsimp [Δ]; push_cast; ring
            have hsk2 : (k : ℝ) ^ 2 ≤ s := by
              have : k ^ 2 ≤ s := by dsimp [s]; omega
              exact_mod_cast this
            nlinarith
          have hp_k2_ge : 8 * ((k - 1 : ℕ) : ℝ) ^ (2 * s) ≤ (p : ℝ) ^ (k ^ 2) := by
            have h1 : (4 * (s : ℝ)) ^ (4 * (l : ℝ) / (k : ℝ) + 8) ≤ (p : ℝ) :=
              hP_rpow_ge.trans hp_ge_rpow
            have h2 := Real.rpow_le_rpow (by positivity) h1 (show (0 : ℝ) ≤ (k ^ 2 : ℕ) by positivity)
            rw [← Real.rpow_mul (by linarith), Real.rpow_natCast] at h2
            have hexp : (4 * (l : ℝ) / (k : ℝ) + 8) * ((k ^ 2 : ℕ) : ℝ) = ((4 * k * l + 8 * k ^ 2 : ℕ) : ℝ) := by
              push_cast; field_simp [hkpos.ne']
            rw [hexp, Real.rpow_natCast] at h2
            have hle_exp : 2 * s + 1 ≤ 4 * k * l + 8 * k ^ 2 := by dsimp [s]; nlinarith
            have hk_le_4s : ((k - 1 : ℕ) : ℝ) ≤ 4 * (s : ℝ) := by
              have hk2 : k ≤ k ^ 2 := Nat.le_self_pow (by omega) k
              have : k - 1 ≤ 4 * s := by dsimp [s]; omega
              exact_mod_cast this
            calc 8 * ((k - 1 : ℕ) : ℝ) ^ (2 * s)
                ≤ (4 * (s : ℝ)) * (4 * (s : ℝ)) ^ (2 * s) :=
                  mul_le_mul (by linarith) (pow_le_pow_left₀ (Nat.cast_nonneg _) hk_le_4s _)
                    (by positivity) (by linarith)
              _ = (4 * (s : ℝ)) ^ (2 * s + 1) := by rw [pow_succ']
              _ ≤ (4 * (s : ℝ)) ^ (4 * k * l + 8 * k ^ 2) := pow_le_pow_right₀ (by linarith) hle_exp
              _ ≤ (p : ℝ) ^ (k ^ 2) := h2
          calc 2 * ((p : ℝ) ^ (k - 1) * ((k - 1 : ℕ) : ℝ) ^ s) ^ 2 * (J s k P₁ : ℝ)
              ≤ 2 * ((p : ℝ) ^ (2 * (k - 1)) * ((k - 1 : ℕ) : ℝ) ^ (2 * s)) *
                  (C₁ * (2 * ((P : ℝ) / (p : ℝ)) ^ (2 * (s : ℝ) - Δ + δ₁))) := by
                have hsq : ((p : ℝ) ^ (k - 1) * ((k - 1 : ℕ) : ℝ) ^ s) ^ 2 =
                    (p : ℝ) ^ (2 * (k - 1)) * ((k - 1 : ℕ) : ℝ) ^ (2 * s) := by
                  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (k - 1) 2, mul_comm s 2]
                rw [hsq]
                refine mul_le_mul_of_nonneg_left (hihP.trans (mul_le_mul_of_nonneg_left hP₁_pow (by dsimp [C₁]; positivity)))
                  (by positivity)
            _ = (4 * ((k - 1 : ℕ) : ℝ) ^ (2 * s) * ((p : ℝ) ^ (2 * (k - 1)) / (p : ℝ) ^ (2 * (s : ℝ) - Δ + δ₁))) *
                  (C₁ * (P : ℝ) ^ (2 * (s : ℝ) - Δ + δ₁)) := by
                rw [Real.div_rpow hPpos.le hpposR.le]; ring
            _ ≤ (4 * ((k - 1 : ℕ) : ℝ) ^ (2 * s) * ((p : ℝ) ^ (k ^ 2))⁻¹) *
                  (C₁ * (P : ℝ) ^ (2 * (s : ℝ) - Δ + δ₁)) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp_exp_le (by positivity))
                  (mul_nonneg (by dsimp [C₁]; positivity) (Real.rpow_nonneg hPpos.le _))
            _ ≤ (1 / 2) * (C₁ * (P : ℝ) ^ (2 * (s : ℝ) - Δ + δ₁)) := by
                refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by dsimp [C₁]; positivity) (Real.rpow_nonneg hPpos.le _))
                rw [mul_inv_le_iff₀ (pow_pos hpposR _)]
                linarith
            _ = (1 / 2) * C₁ * (P : ℝ) ^ (2 * (s : ℝ) - Δ + δ₁) := by ring
        -- Bound Term 2 (Good) ≤ (1/2) * C₁ * P^{2s - Δ + δ₁} using ihl
        have hTerm2 : 2 * (s : ℝ) ^ (2 * k) * (k.factorial : ℝ) *
            (p : ℝ) ^ (2 * (s - k) + k * (k - 1) / 2) * (P : ℝ) ^ k * (J (s - k) k P₁ : ℝ) ≤
            (1 / 2) * C₁ * (P : ℝ) ^ (2 * (s : ℝ) - Δ + δ₁) := by
          rw [hs_sub]
          have hihl := ihl P₁ hP₁_pos
          change (J s₀ k P₁ : ℝ) ≤ C₀ * (P₁ : ℝ) ^ (2 * (s₀ : ℝ) - Δ + δ₀) at hihl
          have hE₀_pos : 0 ≤ 2 * (s₀ : ℝ) - Δ + δ₀ := by
            have : Δ ≤ (k : ℝ) ^ 2 := by dsimp [Δ]; push_cast; nlinarith
            have hsk2 : (k : ℝ) ^ 2 ≤ s₀ := by
              have : k ^ 2 ≤ s₀ := by dsimp [s₀]; omega
              exact_mod_cast this
            linarith
          have hE₀_le2s : 2 * (s₀ : ℝ) - Δ + δ₀ ≤ (2 * s : ℕ) := by
            have : (s₀ : ℝ) ≤ s := by exact_mod_cast (by omega : s₀ ≤ s)
            push_cast; linarith
          have hP₁_pow : (P₁ : ℝ) ^ (2 * (s₀ : ℝ) - Δ + δ₀) ≤
              2 * ((P : ℝ) / (p : ℝ)) ^ (2 * (s₀ : ℝ) - Δ + δ₀) := by
            calc (P₁ : ℝ) ^ (2 * (s₀ : ℝ) - Δ + δ₀)
                ≤ ((1 + 1 / (4 * (s : ℝ))) * ((P : ℝ) / (p : ℝ))) ^ (2 * (s₀ : ℝ) - Δ + δ₀) :=
                  Real.rpow_le_rpow (Nat.cast_nonneg _) hP₁_le hE₀_pos
              _ = (1 + 1 / (4 * (s : ℝ))) ^ (2 * (s₀ : ℝ) - Δ + δ₀) *
                  ((P : ℝ) / (p : ℝ)) ^ (2 * (s₀ : ℝ) - Δ + δ₀) :=
                  Real.mul_rpow (by positivity) (by positivity)
              _ ≤ (1 + 1 / (4 * (s : ℝ))) ^ ((2 * s : ℕ) : ℝ) *
                  ((P : ℝ) / (p : ℝ)) ^ (2 * (s₀ : ℝ) - Δ + δ₀) := by
                  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
                  exact Real.rpow_le_rpow_of_exponent_le (by linarith [show (0 : ℝ) ≤ 1 / (4 * (s : ℝ)) by positivity]) hE₀_le2s
              _ ≤ 2 * ((P : ℝ) / (p : ℝ)) ^ (2 * (s₀ : ℝ) - Δ + δ₀) := by
                  rw [Real.rpow_natCast]
                  exact mul_le_mul_of_nonneg_right (one_add_inv_pow_le_two (by dsimp [s]; nlinarith))
                    (Real.rpow_nonneg (by positivity) _)
          have hpposR : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
          -- Exact exponent identity: p^{2s₀ + k(k-1)/2} * P^k * (P/p)^{2s₀ - Δ + δ₀}
          --   = P^{2s - k - Δ + δ₀} * p^{k^2 - δ₀}
          have hk_even : ((k * (k - 1) / 2 : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
            have h2 : 2 ∣ k * (k - 1) := by
              rcases Nat.even_or_odd k with ⟨t, rfl⟩ | ⟨t, rfl⟩
              · exact ⟨t * (t + t - 1), by ring⟩
              · refine ⟨(2 * t + 1) * t, ?_⟩
                have hsub : 2 * t + 1 - 1 = 2 * t := by omega
                rw [hsub]; ring
            have hcast : ((k * (k - 1) / 2 : ℕ) : ℝ) * 2 = ((k * (k - 1) : ℕ) : ℝ) := by
              exact_mod_cast Nat.div_mul_cancel h2
            rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ k)] at hcast
            push_cast at hcast; linarith
          have hcomb_P_p : (p : ℝ) ^ (2 * s₀ + k * (k - 1) / 2) * (P : ℝ) ^ k *
              ((P : ℝ) / (p : ℝ)) ^ (2 * (s₀ : ℝ) - Δ + δ₀) =
              (P : ℝ) ^ (2 * (s : ℝ) - (k : ℝ) - Δ + δ₀) * (p : ℝ) ^ ((k : ℝ) ^ 2 - δ₀) := by
            rw [Real.div_rpow hPpos.le hpposR.le, ← Real.rpow_natCast (p : ℝ),
              ← Real.rpow_natCast (P : ℝ)]
            have hP_comb : (P : ℝ) ^ (k : ℝ) * (P : ℝ) ^ (2 * (s₀ : ℝ) - Δ + δ₀) =
                (P : ℝ) ^ (2 * (s : ℝ) - (k : ℝ) - Δ + δ₀) := by
              rw [← Real.rpow_add hPpos]
              congr 1
              have hs_cast : (s : ℝ) = (s₀ : ℝ) + (k : ℝ) := by exact_mod_cast hs_eq
              linarith
            have hp_comb : (p : ℝ) ^ ((2 * s₀ + k * (k - 1) / 2 : ℕ) : ℝ) /
                (p : ℝ) ^ (2 * (s₀ : ℝ) - Δ + δ₀) = (p : ℝ) ^ ((k : ℝ) ^ 2 - δ₀) := by
              rw [← Real.rpow_sub hpposR]
              congr 1
              rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hk_even]
              have hΔ_eq : Δ = (k : ℝ) * ((k : ℝ) + 1) / 2 := by dsimp [Δ]; push_cast; ring
              linarith
            calc (p : ℝ) ^ ((2 * s₀ + k * (k - 1) / 2 : ℕ) : ℝ) * (P : ℝ) ^ (k : ℝ) *
                  ((P : ℝ) ^ (2 * (s₀ : ℝ) - Δ + δ₀) / (p : ℝ) ^ (2 * (s₀ : ℝ) - Δ + δ₀))
                = ((P : ℝ) ^ (k : ℝ) * (P : ℝ) ^ (2 * (s₀ : ℝ) - Δ + δ₀)) *
                  ((p : ℝ) ^ ((2 * s₀ + k * (k - 1) / 2 : ℕ) : ℝ) / (p : ℝ) ^ (2 * (s₀ : ℝ) - Δ + δ₀)) := by ring
              _ = _ := by rw [hP_comb, hp_comb]
          have hk2_sub_δ₀ : 0 ≤ (k : ℝ) ^ 2 - δ₀ := by
            have : Δ ≤ (k : ℝ) ^ 2 := by dsimp [Δ]; push_cast; nlinarith
            linarith
          have hp_pow_le : (p : ℝ) ^ ((k : ℝ) ^ 2 - δ₀) ≤
              (3 : ℝ) ^ (k ^ 2) * (P : ℝ) ^ ((k : ℝ) - δ₀ / (k : ℝ)) := by
            calc (p : ℝ) ^ ((k : ℝ) ^ 2 - δ₀)
                ≤ (3 * (P : ℝ) ^ (1 / (k : ℝ))) ^ ((k : ℝ) ^ 2 - δ₀) :=
                  Real.rpow_le_rpow hpposR.le hp_le_3 hk2_sub_δ₀
              _ = (3 : ℝ) ^ ((k : ℝ) ^ 2 - δ₀) * ((P : ℝ) ^ (1 / (k : ℝ))) ^ ((k : ℝ) ^ 2 - δ₀) :=
                  Real.mul_rpow (by norm_num) (Real.rpow_nonneg hPpos.le _)
              _ ≤ (3 : ℝ) ^ ((k ^ 2 : ℕ) : ℝ) * ((P : ℝ) ^ (1 / (k : ℝ))) ^ ((k : ℝ) ^ 2 - δ₀) := by
                  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Real.rpow_nonneg hPpos.le _) _)
                  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
              _ = (3 : ℝ) ^ (k ^ 2) * (P : ℝ) ^ ((k : ℝ) - δ₀ / (k : ℝ)) := by
                  rw [Real.rpow_natCast, ← Real.rpow_mul hPpos.le]
                  congr 2
                  field_simp [hkpos.ne']
          have hP_final : (P : ℝ) ^ (2 * (s : ℝ) - (k : ℝ) - Δ + δ₀) * (P : ℝ) ^ ((k : ℝ) - δ₀ / (k : ℝ)) =
              (P : ℝ) ^ (2 * (s : ℝ) - Δ + δ₁) := by
            rw [← Real.rpow_add hPpos]
            congr 1
            have hδ_step : δ₁ = δ₀ - δ₀ / (k : ℝ) := by
              dsimp only [δ₁, δ₀]; rw [pow_succ]; ring
            linarith
          have hconst_le : 4 * (s : ℝ) ^ (2 * k) * (k.factorial : ℝ) * (3 : ℝ) ^ (k ^ 2) * C₀ ≤
              (1 / 2) * C₁ := by
            have hC₀_le : C₀ ≤ (4 * (s : ℝ)) ^ (4 * k ^ 2 * l + 8 * k ^ 3) :=
              pow_le_pow_left₀ (by positivity) (by
                have : (s₀ : ℝ) ≤ s := by exact_mod_cast (by omega : s₀ ≤ s)
                linarith) _
            have hfac_le : (k.factorial : ℝ) ≤ (4 * (s : ℝ)) ^ k := by
              have h1 : k.factorial ≤ k ^ k := Nat.factorial_le_pow k
              have h2 : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast h1
              have h3 : (k : ℝ) ≤ 4 * (s : ℝ) := by
                have hk2 : k ≤ k ^ 2 := Nat.le_self_pow (by omega) k
                have : k ≤ 4 * s := by dsimp [s]; omega
                exact_mod_cast this
              exact h2.trans (pow_le_pow_left₀ hkpos.le h3 k)
            have h3_le : (3 : ℝ) ^ (k ^ 2) ≤ (4 * (s : ℝ)) ^ (k ^ 2) :=
              pow_le_pow_left₀ (by norm_num) (by linarith) _
            have hs2k_le : (s : ℝ) ^ (2 * k) ≤ (4 * (s : ℝ)) ^ (2 * k) :=
              pow_le_pow_left₀ (by linarith) (by linarith) _
            have h8_le : (8 : ℝ) ≤ (4 * (s : ℝ)) ^ 1 := by simp; linarith
            have hsum_exp : 1 + 2 * k + k + k ^ 2 + (4 * k ^ 2 * l + 8 * k ^ 3) ≤
                4 * k ^ 2 * (l + 1) + 8 * k ^ 3 := by
              have h1 : 1 + 3 * k + k ^ 2 ≤ 4 * k ^ 2 := by nlinarith [hk]
              rw [mul_add, mul_one]; omega
            have h8prod : 8 * (s : ℝ) ^ (2 * k) * (k.factorial : ℝ) * (3 : ℝ) ^ (k ^ 2) * C₀ ≤ C₁ := by
              have hm1 : 8 * (s : ℝ) ^ (2 * k) ≤ (4 * (s : ℝ)) ^ 1 * (4 * (s : ℝ)) ^ (2 * k) :=
                mul_le_mul h8_le hs2k_le (by positivity) (by positivity)
              have hm2 : 8 * (s : ℝ) ^ (2 * k) * (k.factorial : ℝ) ≤
                  (4 * (s : ℝ)) ^ 1 * (4 * (s : ℝ)) ^ (2 * k) * (4 * (s : ℝ)) ^ k :=
                mul_le_mul hm1 hfac_le (by positivity) (by positivity)
              have hm3 : 8 * (s : ℝ) ^ (2 * k) * (k.factorial : ℝ) * (3 : ℝ) ^ (k ^ 2) ≤
                  (4 * (s : ℝ)) ^ 1 * (4 * (s : ℝ)) ^ (2 * k) * (4 * (s : ℝ)) ^ k * (4 * (s : ℝ)) ^ (k ^ 2) :=
                mul_le_mul hm2 h3_le (by positivity) (by positivity)
              have hm4 : 8 * (s : ℝ) ^ (2 * k) * (k.factorial : ℝ) * (3 : ℝ) ^ (k ^ 2) * C₀ ≤
                  (4 * (s : ℝ)) ^ 1 * (4 * (s : ℝ)) ^ (2 * k) * (4 * (s : ℝ)) ^ k *
                    (4 * (s : ℝ)) ^ (k ^ 2) * (4 * (s : ℝ)) ^ (4 * k ^ 2 * l + 8 * k ^ 3) :=
                mul_le_mul hm3 hC₀_le (by dsimp [C₀]; positivity) (by positivity)
              calc 8 * (s : ℝ) ^ (2 * k) * (k.factorial : ℝ) * (3 : ℝ) ^ (k ^ 2) * C₀
                  ≤ (4 * (s : ℝ)) ^ 1 * (4 * (s : ℝ)) ^ (2 * k) * (4 * (s : ℝ)) ^ k *
                    (4 * (s : ℝ)) ^ (k ^ 2) * (4 * (s : ℝ)) ^ (4 * k ^ 2 * l + 8 * k ^ 3) := hm4
                _ = (4 * (s : ℝ)) ^ (1 + 2 * k + k + k ^ 2 + (4 * k ^ 2 * l + 8 * k ^ 3)) := by
                    simp only [pow_add]
                _ ≤ C₁ := pow_le_pow_right₀ (by linarith) hsum_exp
            linarith
          calc 2 * (s : ℝ) ^ (2 * k) * (k.factorial : ℝ) *
                (p : ℝ) ^ (2 * s₀ + k * (k - 1) / 2) * (P : ℝ) ^ k * (J s₀ k P₁ : ℝ)
              ≤ 2 * (s : ℝ) ^ (2 * k) * (k.factorial : ℝ) *
                (p : ℝ) ^ (2 * s₀ + k * (k - 1) / 2) * (P : ℝ) ^ k *
                (C₀ * (2 * ((P : ℝ) / (p : ℝ)) ^ (2 * (s₀ : ℝ) - Δ + δ₀))) :=
                mul_le_mul_of_nonneg_left (hihl.trans (mul_le_mul_of_nonneg_left hP₁_pow (by dsimp [C₀]; positivity)))
                  (by positivity)
            _ = (4 * (s : ℝ) ^ (2 * k) * (k.factorial : ℝ) * C₀) *
                ((p : ℝ) ^ (2 * s₀ + k * (k - 1) / 2) * (P : ℝ) ^ k *
                  ((P : ℝ) / (p : ℝ)) ^ (2 * (s₀ : ℝ) - Δ + δ₀)) := by ring
            _ = (4 * (s : ℝ) ^ (2 * k) * (k.factorial : ℝ) * C₀) *
                ((P : ℝ) ^ (2 * (s : ℝ) - (k : ℝ) - Δ + δ₀) * (p : ℝ) ^ ((k : ℝ) ^ 2 - δ₀)) := by
                rw [hcomb_P_p]
            _ ≤ (4 * (s : ℝ) ^ (2 * k) * (k.factorial : ℝ) * C₀) *
                ((P : ℝ) ^ (2 * (s : ℝ) - (k : ℝ) - Δ + δ₀) *
                  ((3 : ℝ) ^ (k ^ 2) * (P : ℝ) ^ ((k : ℝ) - δ₀ / (k : ℝ)))) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hp_pow_le (Real.rpow_nonneg hPpos.le _))
                  (by dsimp [C₀]; positivity)
            _ = (4 * (s : ℝ) ^ (2 * k) * (k.factorial : ℝ) * (3 : ℝ) ^ (k ^ 2) * C₀) *
                ((P : ℝ) ^ (2 * (s : ℝ) - (k : ℝ) - Δ + δ₀) * (P : ℝ) ^ ((k : ℝ) - δ₀ / (k : ℝ))) := by ring
            _ = (4 * (s : ℝ) ^ (2 * k) * (k.factorial : ℝ) * (3 : ℝ) ^ (k ^ 2) * C₀) *
                (P : ℝ) ^ (2 * (s : ℝ) - Δ + δ₁) := by rw [hP_final]
            _ ≤ (1 / 2) * C₁ * (P : ℝ) ^ (2 * (s : ℝ) - Δ + δ₁) :=
                mul_le_mul_of_nonneg_right hconst_le (Real.rpow_nonneg hPpos.le _)
        linarith [hstep, hTerm1, hTerm2]

end

end OMA.Erdos377M2


/-
Vinogradov-Korobov bound for reciprocal exponential sums `∑_{x ∈ (M, N]} e(α / x)`
using finite geometric series expansion, discrete Weyl grid rounding, discrete Abel
summation, and Vinogradov's Mean Value Theorem (`M2_VMVT.vinogradov_mvt`).
-/

namespace OMA.Erdos377M3

open Finset Real Complex OMA.Erdos377M2
open scoped BigOperators

noncomputable section

/-- Lipschitz bound `‖e(x) - 1‖ ≤ 2π |x|`. -/
lemma norm_e_sub_one_le (x : ℝ) : ‖e x - 1‖ ≤ 2 * Real.pi * |x| := by
  have h1 : e x - 1 = Complex.exp (↑(Real.pi * x) * Complex.I) *
      (Complex.exp (↑(Real.pi * x) * Complex.I) - Complex.exp (-(↑(Real.pi * x) * Complex.I))) := by
    rw [mul_sub, ← Complex.exp_add, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    congr 2
    dsimp only [e]; push_cast; ring
  have h2 : Complex.exp (↑(Real.pi * x) * Complex.I) - Complex.exp (-(↑(Real.pi * x) * Complex.I)) =
      (2 * Real.sin (Real.pi * x) : ℂ) * Complex.I := by
    rw [show -(↑(Real.pi * x) * Complex.I) = ↑(-(Real.pi * x)) * Complex.I by push_cast; ring]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    simp only [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_sin]
    ring
  rw [h1, h2, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, Complex.norm_I, mul_one]
  rw [show (2 * (Real.sin (Real.pi * x) : ℂ)) = ((2 * Real.sin (Real.pi * x) : ℝ) : ℂ) by push_cast; rfl]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc 2 * |Real.sin (Real.pi * x)| ≤ 2 * |Real.pi * x| :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs) (by norm_num)
    _ = 2 * Real.pi * |x| := by rw [abs_mul, abs_of_pos Real.pi_pos]; ring

/-- Lipschitz bound `‖e(x) - e(y)‖ ≤ 2π |x - y|`. -/
lemma norm_e_sub_e_le (x y : ℝ) : ‖e x - e y‖ ≤ 2 * Real.pi * |x - y| := by
  have h : e x - e y = e y * (e (x - y) - 1) := by
    rw [mul_sub, mul_one, ← e_add, add_sub_cancel]
  rw [h, norm_mul, norm_e, one_mul]
  exact norm_e_sub_one_le (x - y)

/-- Discrete Abel summation on `Finset.range (m + 1)`. -/
lemma abel_sum_range_succ (m : ℕ) (w g : ℕ → ℂ) :
    ∑ y ∈ range (m + 1), w y * g y =
      w m * (∑ y ∈ range (m + 1), g y) -
      ∑ t ∈ range m, (w (t + 1) - w t) * (∑ y ∈ range (t + 1), g y) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun t => (w (t + 1) - w t) * _),
      sum_range_succ (fun y => g y) (m + 1)]
    ring

/-- Exact finite geometric-series expansion of `1 / (x + y)` up to degree `k`. -/
lemma geom_recip_expand {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (k : ℕ) :
    1 / (x + y) = 1 / x +
      (∑ j : Fin k, ((-1 : ℝ) ^ (j.1 + 1) / x ^ (j.1 + 2)) * y ^ (j.1 + 1)) +
      (-1 : ℝ) ^ (k + 1) * (y / x) ^ (k + 1) / (x + y) := by
  have hxy : x + y ≠ 0 := by linarith
  have hx0 : x ≠ 0 := hx.ne'
  induction k with
  | zero =>
    simp only [Finset.univ_eq_empty, sum_empty, add_zero, zero_add, pow_one]
    field_simp [hx0, hxy]
    ring
  | succ k ih =>
    rw [ih, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hstep : (-1 : ℝ) ^ (k + 1) * (y / x) ^ (k + 1) / (x + y) =
        ((-1 : ℝ) ^ (k + 1) / x ^ (k + 2)) * y ^ (k + 1) +
        (-1 : ℝ) ^ (k + 2) * (y / x) ^ (k + 2) / (x + y) := by
      have hxpow : x ^ (k + 2) ≠ 0 := pow_ne_zero _ hx0
      rw [div_pow, div_pow, pow_succ (-1 : ℝ) (k + 1), pow_succ x (k + 1), pow_succ y (k + 1)]
      field_simp [hx0, hxy, pow_ne_zero (k + 1) hx0]
      ring
    linarith

/-- Purely algebraic difference bound for `1 / x^m`: for `0 < x₁ ≤ x₂` and `m ≥ 1`,
    `m * (x₂ - x₁) * x₁^(m-1) / (x₁^m * x₂^m) ≤ 1/x₁^m - 1/x₂^m ≤ m * (x₂ - x₁) * x₂^(m-1) / (x₁^m * x₂^m)`. -/
lemma inv_pow_sub_bounds {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hle : x₁ ≤ x₂) (m : ℕ) :
    (m : ℝ) * (x₂ - x₁) * x₁ ^ (m - 1) / (x₁ ^ m * x₂ ^ m) ≤ 1 / x₁ ^ m - 1 / x₂ ^ m ∧
    1 / x₁ ^ m - 1 / x₂ ^ m ≤ (m : ℝ) * (x₂ - x₁) * x₂ ^ (m - 1) / (x₁ ^ m * x₂ ^ m) := by
  have hx₂ : 0 < x₂ := lt_of_lt_of_le hx₁ hle
  have hden : 0 < x₁ ^ m * x₂ ^ m := by positivity
  have hdiff : 1 / x₁ ^ m - 1 / x₂ ^ m = (x₂ ^ m - x₁ ^ m) / (x₁ ^ m * x₂ ^ m) := by
    field_simp [pow_ne_zero m hx₁.ne', pow_ne_zero m hx₂.ne']
  rw [hdiff]
  have hgeom : x₂ ^ m - x₁ ^ m = (x₂ - x₁) * ∑ i ∈ range m, x₂ ^ i * x₁ ^ (m - 1 - i) := by
    rw [mul_comm, geom_sum₂_mul]
  constructor
  · refine div_le_div_of_nonneg_right ?_ hden.le
    rw [hgeom]
    have hsum : (m : ℝ) * x₁ ^ (m - 1) ≤ ∑ i ∈ range m, x₂ ^ i * x₁ ^ (m - 1 - i) := by
      calc (m : ℝ) * x₁ ^ (m - 1) = ∑ _i ∈ range m, x₁ ^ (m - 1) := by simp
        _ ≤ ∑ i ∈ range m, x₂ ^ i * x₁ ^ (m - 1 - i) := sum_le_sum fun i hi => by
            have him : i ≤ m - 1 := by have := mem_range.mp hi; omega
            calc x₁ ^ (m - 1) = x₁ ^ (i + (m - 1 - i)) := by congr 1; omega
              _ = x₁ ^ i * x₁ ^ (m - 1 - i) := pow_add _ _ _
              _ ≤ x₂ ^ i * x₁ ^ (m - 1 - i) :=
                  mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx₁.le hle i) (by positivity)
    have : (x₂ - x₁) * ((m : ℝ) * x₁ ^ (m - 1)) ≤ (x₂ - x₁) * ∑ i ∈ range m, x₂ ^ i * x₁ ^ (m - 1 - i) :=
      mul_le_mul_of_nonneg_left hsum (by linarith)
    linarith
  · refine div_le_div_of_nonneg_right ?_ hden.le
    rw [hgeom]
    have hsum : ∑ i ∈ range m, x₂ ^ i * x₁ ^ (m - 1 - i) ≤ (m : ℝ) * x₂ ^ (m - 1) := by
      calc ∑ i ∈ range m, x₂ ^ i * x₁ ^ (m - 1 - i)
          ≤ ∑ _i ∈ range m, x₂ ^ (m - 1) := sum_le_sum fun i hi => by
            have him : i ≤ m - 1 := by have := mem_range.mp hi; omega
            calc x₂ ^ i * x₁ ^ (m - 1 - i)
                ≤ x₂ ^ i * x₂ ^ (m - 1 - i) :=
                  mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx₁.le hle _) (by positivity)
              _ = x₂ ^ (i + (m - 1 - i)) := (pow_add _ _ _).symm
              _ = x₂ ^ (m - 1) := by congr 1; omega
        _ = (m : ℝ) * x₂ ^ (m - 1) := by simp
    have : (x₂ - x₁) * ∑ i ∈ range m, x₂ ^ i * x₁ ^ (m - 1 - i) ≤ (x₂ - x₁) * ((m : ℝ) * x₂ ^ (m - 1)) :=
      mul_le_mul_of_nonneg_left hsum (by linarith)
    linarith

/-- Existence of a derivative index `r : Fin k` with `1 ≤ r.1` such that
    `M₀^(-3/2) ≤ (r.1 + 2) * α / M₀^(r.1 + 3) ≤ M₀^(-1/2)`. -/
private lemma exists_good_deriv_index {M M₀ k : ℕ} {α : ℝ}
    (hM : 100 ≤ M) (hM₀_lo : M ≤ M₀) (hM₀_hi : M₀ ≤ 2 * M) (hk : 4 ≤ k)
    (hα_lo : (M : ℝ) ^ (3 : ℕ) ≤ α) (hα_hi : α ≤ (M : ℝ) ^ ((k : ℝ) / 2))
    (hkM : 16 * k ≤ Nat.sqrt M) :
    ∃ r : Fin k, 1 ≤ r.1 ∧
      (M₀ : ℝ) ^ (-(3 : ℝ) / 2) ≤ ((r.1 + 2 : ℕ) : ℝ) * α / (M₀ : ℝ) ^ (r.1 + 3) ∧
      ((r.1 + 2 : ℕ) : ℝ) * α / (M₀ : ℝ) ^ (r.1 + 3) ≤ (M₀ : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hM₀pos : (0 : ℝ) < M₀ := by exact_mod_cast (by omega : 0 < M₀)
  have hM100 : (100 : ℝ) ≤ M := by exact_mod_cast hM
  have hM₀_ge : (M : ℝ) ≤ M₀ := by exact_mod_cast hM₀_lo
  have hM₀_le : (M₀ : ℝ) ≤ 2 * M := by exact_mod_cast hM₀_hi
  have hα_pos : 0 < α := lt_of_lt_of_le (by positivity) hα_lo
  let u : ℕ → ℝ := fun j => ((j + 2 : ℕ) : ℝ) * α / (M₀ : ℝ) ^ (j + 3)
  let A : ℝ := (M₀ : ℝ) ^ (-(3 : ℝ) / 2)
  let B : ℝ := (M₀ : ℝ) ^ (-(1 : ℝ) / 2)
  have hBA : B = (M₀ : ℝ) * A := by
    dsimp only [A, B]
    calc (M₀ : ℝ) ^ (-(1 : ℝ) / 2) = (M₀ : ℝ) ^ ((1 : ℝ) + -(3 : ℝ) / 2) := by congr 1; ring
      _ = (M₀ : ℝ) ^ (1 : ℝ) * (M₀ : ℝ) ^ (-(3 : ℝ) / 2) := Real.rpow_add hM₀pos _ _
      _ = (M₀ : ℝ) * (M₀ : ℝ) ^ (-(3 : ℝ) / 2) := by rw [Real.rpow_one]
  have hu1_ge : A ≤ u 1 := by
    dsimp only [u, A]
    have h1 : 3 / (16 * (M : ℝ)) ≤ 3 * α / (M₀ : ℝ) ^ 4 := by
      have hM₀4 : (M₀ : ℝ) ^ 4 ≤ 16 * (M : ℝ) ^ 4 := by
        calc (M₀ : ℝ) ^ 4 ≤ (2 * (M : ℝ)) ^ 4 := pow_le_pow_left₀ hM₀pos.le hM₀_le 4
          _ = 16 * (M : ℝ) ^ 4 := by ring
      calc 3 / (16 * (M : ℝ)) = 3 * (M : ℝ) ^ 3 / (16 * (M : ℝ) ^ 4) := by field_simp [hMpos.ne']
        _ ≤ 3 * α / (16 * (M : ℝ) ^ 4) := by gcongr
        _ ≤ 3 * α / (M₀ : ℝ) ^ 4 := div_le_div_of_nonneg_left (by positivity) (by positivity) hM₀4
    have h2 : (M₀ : ℝ) ^ (-(3 : ℝ) / 2) ≤ 3 / (16 * (M : ℝ)) := by
      have hMsqrt : (10 : ℝ) ≤ (M : ℝ) ^ ((1 : ℝ) / 2) := by
        have h100 : (10 : ℝ) = ((100 : ℝ) ^ ((1 : ℝ) / 2)) := by
          rw [show (100 : ℝ) = (10 : ℝ) ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast,
            ← Real.rpow_mul (by norm_num)]
          norm_num
        rw [h100]
        exact Real.rpow_le_rpow (by norm_num) hM100 (by norm_num)
      have hM32 : 10 * (M : ℝ) ≤ (M : ℝ) ^ ((3 : ℝ) / 2) := by
        have h32 : (M : ℝ) ^ ((3 : ℝ) / 2) = (M : ℝ) ^ ((1 : ℝ) / 2) * (M : ℝ) := by
          calc (M : ℝ) ^ ((3 : ℝ) / 2) = (M : ℝ) ^ (((1 : ℝ) / 2) + 1) := by congr 1; ring
            _ = (M : ℝ) ^ ((1 : ℝ) / 2) * (M : ℝ) ^ (1 : ℝ) := Real.rpow_add hMpos _ _
            _ = (M : ℝ) ^ ((1 : ℝ) / 2) * (M : ℝ) := by rw [Real.rpow_one]
        rw [h32]; nlinarith
      have hM₀32 : (M : ℝ) ^ ((3 : ℝ) / 2) ≤ (M₀ : ℝ) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow hMpos.le hM₀_ge (by norm_num)
      rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring, Real.rpow_neg hM₀pos.le]
      rw [inv_eq_one_div, div_le_div_iff₀ (Real.rpow_pos_of_pos hM₀pos _) (by positivity)]
      nlinarith
    simpa using h2.trans h1
  have huk_le : u (k - 1) ≤ B := by
    dsimp only [u, B]
    have hk1 : k - 1 + 2 = k + 1 := by omega
    have hk2 : k - 1 + 3 = k + 2 := by omega
    rw [hk1, hk2]
    have hk_le_sqrt : ((k + 1 : ℕ) : ℝ) ≤ (M : ℝ) ^ ((1 : ℝ) / 2) := by
      have hsq : (Nat.sqrt M : ℝ) ≤ (M : ℝ) ^ ((1 : ℝ) / 2) := by
        have h1 : ((Nat.sqrt M : ℕ) : ℝ) ^ (2 : ℕ) ≤ (M : ℝ) := by
          have : Nat.sqrt M ^ 2 ≤ M := by simpa [sq] using Nat.sqrt_le M
          exact_mod_cast this
        have h2 := Real.rpow_le_rpow (by positivity) h1 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)] at h2
        simpa using h2
      have hk16 : ((k + 1 : ℕ) : ℝ) ≤ (Nat.sqrt M : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ Nat.sqrt M)
      exact hk16.trans hsq
    have hM₀_ge_pow : (M : ℝ) ^ (k + 2) ≤ (M₀ : ℝ) ^ (k + 2) :=
      pow_le_pow_left₀ hMpos.le hM₀_ge _
    have hα_div : ((k + 1 : ℕ) : ℝ) * α / (M₀ : ℝ) ^ (k + 2) ≤ (M : ℝ) ^ (-(1 : ℝ)) := by
      calc ((k + 1 : ℕ) : ℝ) * α / (M₀ : ℝ) ^ (k + 2)
          ≤ (M : ℝ) ^ ((1 : ℝ) / 2) * (M : ℝ) ^ ((k : ℝ) / 2) / (M : ℝ) ^ (k + 2) :=
            div_le_div₀ (by positivity)
              (mul_le_mul hk_le_sqrt hα_hi hα_pos.le (Real.rpow_nonneg hMpos.le _))
              (by positivity) hM₀_ge_pow
        _ = (M : ℝ) ^ ((1 : ℝ) / 2 + (k : ℝ) / 2 - ((k + 2 : ℕ) : ℝ)) := by
            rw [← Real.rpow_add hMpos, ← Real.rpow_natCast (M : ℝ), ← Real.rpow_sub hMpos]
        _ ≤ (M : ℝ) ^ (-(1 : ℝ)) := by
            refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
            have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
            push_cast; linarith
    have hM_le_B : (M : ℝ) ^ (-(1 : ℝ)) ≤ (M₀ : ℝ) ^ (-(1 : ℝ) / 2) := by
      have hM₀_le_M2 : (M₀ : ℝ) ≤ (M : ℝ) ^ (2 : ℕ) := by nlinarith
      have h1 : (M₀ : ℝ) ^ ((1 : ℝ) / 2) ≤ (M : ℝ) := by
        have h2 := Real.rpow_le_rpow hM₀pos.le hM₀_le_M2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
        rw [← Real.rpow_natCast, ← Real.rpow_mul hMpos.le] at h2
        simpa using h2
      rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring, Real.rpow_neg hMpos.le,
        Real.rpow_neg hM₀pos.le, Real.rpow_one]
      exact inv_anti₀ (Real.rpow_pos_of_pos hM₀pos _) h1
    exact hα_div.trans hM_le_B
  have hstep : ∀ j : ℕ, u j / (M₀ : ℝ) ≤ u (j + 1) := by
    intro j
    dsimp only [u]
    rw [div_div, ← pow_succ, show j + 3 + 1 = j + 1 + 3 from by omega]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    refine mul_le_mul_of_nonneg_right ?_ hα_pos.le
    exact_mod_cast (by omega : j + 2 ≤ j + 1 + 2)
  -- Pick the minimal j ≥ 1 with u j ≤ B
  have hex : ∃ j, 1 ≤ j ∧ j < k ∧ u j ≤ B := ⟨k - 1, by omega, by omega, huk_le⟩
  classical
  let j₀ := Nat.find hex
  have hj₀ : 1 ≤ j₀ ∧ j₀ < k ∧ u j₀ ≤ B := Nat.find_spec hex
  refine ⟨⟨j₀, hj₀.2.1⟩, hj₀.1, ?_, hj₀.2.2⟩
  change A ≤ u j₀
  rcases Nat.eq_or_lt_of_le hj₀.1 with h1 | hgt
  · rw [← h1]; exact hu1_ge
  · have hprev : ¬ (1 ≤ j₀ - 1 ∧ j₀ - 1 < k ∧ u (j₀ - 1) ≤ B) :=
      Nat.find_min hex (by omega)
    have hgtB : B < u (j₀ - 1) := by
      by_contra hle; push Not at hle
      exact hprev ⟨by omega, by omega, hle⟩
    have hst := hstep (j₀ - 1)
    rw [Nat.sub_add_cancel (by omega)] at hst
    have hA_lt : A < u (j₀ - 1) / (M₀ : ℝ) := by
      rw [lt_div_iff₀ hM₀pos]
      linarith [hBA]
    linarith

set_option maxHeartbeats 1600000 in
/-- Single-block Vinogradov-Korobov exponential sum bound on `[M₀, M₀ + L')`
    where `M ≤ M₀ ≤ 2 * M` and `L' ≤ L = M / (4 * k)`. -/
private lemma block_recip_sum_bound
    {M M₀ L' k l : ℕ} {α : ℝ}
    (hM : 100 ≤ M) (hM₀_lo : M ≤ M₀) (hM₀_hi : M₀ ≤ 2 * M)
    (hL' : L' ≤ M / (4 * k))
    (hk : 4 ≤ k) (hl : 1 ≤ l)
    (hα_lo : (M : ℝ) ^ (3 : ℕ) ≤ α)
    (hα_hi : α ≤ (M : ℝ) ^ ((k : ℝ) / 2))
    (hkY : 16 * k ≤ Nat.sqrt M) :
    let L := M / (4 * k)
    let s := k ^ 2 + k * l
    let Y := Nat.sqrt M
    let δ : ℝ := ((k * (k + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (k : ℝ)) ^ l
    ‖∑ x ∈ Ico M₀ (M₀ + L'), e (α / (x : ℝ))‖ ≤
      2 * (L : ℝ) * ((4 * (s : ℝ)) ^ (5 * k) * (Y : ℝ) ^ ((-1 + δ) / (2 * (s : ℝ))) + 1 / (Y : ℝ)) +
      2 * (Y : ℝ) := by
  classical
  intro L s Y δ
  have hY_ge_10 : 10 ≤ Y := by
    have : 100 ≤ M := hM
    exact Nat.le_sqrt.mpr (by omega)
  have hY_pos : 0 < Y := by omega
  have hY_Rpos : (0 : ℝ) < Y := by exact_mod_cast hY_pos
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hM₀pos : (0 : ℝ) < M₀ := by exact_mod_cast (by omega : 0 < M₀)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hs_ge16 : 16 ≤ s := by dsimp [s]; nlinarith
  have hspos : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hα_pos : 0 < α := lt_of_lt_of_le (by positivity) hα_lo
  have hY2_le_M : Y ^ 2 ≤ M := by simpa [sq] using Nat.sqrt_le M
  have hM_lt_Y1 : M < (Y + 1) ^ 2 := by simpa [sq] using Nat.lt_succ_sqrt M
  have hY_le_sqrtM : (Y : ℝ) ≤ (M : ℝ) ^ ((1 : ℝ) / 2) := by
    have h1 : (Y : ℝ) ^ (2 : ℕ) ≤ (M : ℝ) := by exact_mod_cast hY2_le_M
    have h2 := Real.rpow_le_rpow (by positivity) h1 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)] at h2
    simpa using h2
  have hL_ge_4Y : 4 * Y ≤ L := by
    dsimp only [L]
    have h1 : 4 * Y * (4 * k) ≤ Y ^ 2 := by nlinarith
    exact (Nat.le_div_iff_mul_le (by omega : 0 < 4 * k)).mpr (h1.trans hY2_le_M)
  have hL_pos : 1 ≤ L := by omega
  have hL_Rpos : (0 : ℝ) < L := by exact_mod_cast hL_pos
  -- Step 1: Shift by y ∈ range Y and average
  have hshift_y : ∀ y ∈ range Y,
      ‖(∑ x ∈ Ico M₀ (M₀ + L'), e (α / (x : ℝ))) -
       (∑ x ∈ Ico M₀ (M₀ + L'), e (α / ((x + y : ℕ) : ℝ)))‖ ≤ 2 * (Y : ℝ) := by
    intro y hy
    have hyY : y < Y := mem_range.mp hy
    have hreidx : ∑ x ∈ Ico M₀ (M₀ + L'), e (α / ((x + y : ℕ) : ℝ)) =
        ∑ z ∈ Ico (M₀ + y) (M₀ + L' + y), e (α / (z : ℝ)) := by
      refine Finset.sum_bij (fun x _ => x + y) ?_ ?_ ?_ ?_
      · intro x hx; rw [mem_Ico] at hx ⊢; omega
      · intro a _ b _ h; omega
      · intro z hz; rw [mem_Ico] at hz; exact ⟨z - y, mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro x _; rfl
    rw [hreidx]
    let A := Ico M₀ (M₀ + L')
    let B := Ico (M₀ + y) (M₀ + L' + y)
    have hdiff : (∑ x ∈ A, e (α / (x : ℝ))) - (∑ z ∈ B, e (α / (z : ℝ))) =
        (∑ x ∈ A \ B, e (α / (x : ℝ))) - (∑ z ∈ B \ A, e (α / (z : ℝ))) := by
      have hA : ∑ x ∈ A, e (α / (x : ℝ)) = (∑ x ∈ A \ B, e (α / (x : ℝ))) + (∑ x ∈ A ∩ B, e (α / (x : ℝ))) := by
        rw [← Finset.sum_union (disjoint_sdiff_inter A B), sdiff_union_inter]
      have hB : ∑ z ∈ B, e (α / (z : ℝ)) = (∑ z ∈ B \ A, e (α / (z : ℝ))) + (∑ z ∈ B ∩ A, e (α / (z : ℝ))) := by
        rw [← Finset.sum_union (disjoint_sdiff_inter B A), sdiff_union_inter]
      rw [hA, hB, inter_comm B A]; ring
    rw [hdiff]
    have hAB_sub : A \ B ⊆ Ico M₀ (M₀ + y) := by
      intro x hx; rw [mem_sdiff, mem_Ico, mem_Ico] at hx; rw [mem_Ico]; omega
    have hBA_sub : B \ A ⊆ Ico (M₀ + L') (M₀ + L' + y) := by
      intro z hz; rw [mem_sdiff, mem_Ico, mem_Ico] at hz; rw [mem_Ico]; omega
    have h1 : ‖∑ x ∈ A \ B, e (α / (x : ℝ))‖ ≤ y := by
      calc ‖∑ x ∈ A \ B, e (α / (x : ℝ))‖ ≤ ∑ x ∈ A \ B, ‖e (α / (x : ℝ))‖ := norm_sum_le _ _
        _ = ((A \ B).card : ℝ) := by simp [norm_e]
        _ ≤ ((Ico M₀ (M₀ + y)).card : ℝ) := by exact_mod_cast card_le_card hAB_sub
        _ = y := by simp
    have h2 : ‖∑ z ∈ B \ A, e (α / (z : ℝ))‖ ≤ y := by
      calc ‖∑ z ∈ B \ A, e (α / (z : ℝ))‖ ≤ ∑ z ∈ B \ A, ‖e (α / (z : ℝ))‖ := norm_sum_le _ _
        _ = ((B \ A).card : ℝ) := by simp [norm_e]
        _ ≤ ((Ico (M₀ + L') (M₀ + L' + y)).card : ℝ) := by exact_mod_cast card_le_card hBA_sub
        _ = y := by simp
    have hyR : (y : ℝ) ≤ Y := by exact_mod_cast hyY.le
    calc ‖(∑ x ∈ A \ B, e (α / (x : ℝ))) - (∑ z ∈ B \ A, e (α / (z : ℝ)))‖
        ≤ ‖∑ x ∈ A \ B, e (α / (x : ℝ))‖ + ‖∑ z ∈ B \ A, e (α / (z : ℝ))‖ := norm_sub_le _ _
      _ ≤ 2 * (Y : ℝ) := by linarith
  have havg : ‖∑ x ∈ Ico M₀ (M₀ + L'), e (α / (x : ℝ))‖ ≤
      (1 / (Y : ℝ)) * (∑ x ∈ Ico M₀ (M₀ + L'), ‖∑ y ∈ range Y, e (α / ((x + y : ℕ) : ℝ))‖) +
      2 * (Y : ℝ) := by
    have hsum_eq : ((Y : ℂ)) * (∑ x ∈ Ico M₀ (M₀ + L'), e (α / (x : ℝ))) =
        (∑ x ∈ Ico M₀ (M₀ + L'), ∑ y ∈ range Y, e (α / ((x + y : ℕ) : ℝ))) +
        (∑ y ∈ range Y, ((∑ x ∈ Ico M₀ (M₀ + L'), e (α / (x : ℝ))) -
          (∑ x ∈ Ico M₀ (M₀ + L'), e (α / ((x + y : ℕ) : ℝ))))) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul, Finset.sum_comm]
      ring
    have hnorm := congrArg norm hsum_eq
    rw [norm_mul, Complex.norm_natCast] at hnorm
    have hbd : (Y : ℝ) * ‖∑ x ∈ Ico M₀ (M₀ + L'), e (α / (x : ℝ))‖ ≤
        (∑ x ∈ Ico M₀ (M₀ + L'), ‖∑ y ∈ range Y, e (α / ((x + y : ℕ) : ℝ))‖) +
        (Y : ℝ) * (2 * (Y : ℝ)) := by
      rw [hnorm]
      calc ‖(∑ x ∈ Ico M₀ (M₀ + L'), ∑ y ∈ range Y, e (α / ((x + y : ℕ) : ℝ))) +
            (∑ y ∈ range Y, ((∑ x ∈ Ico M₀ (M₀ + L'), e (α / (x : ℝ))) -
              (∑ x ∈ Ico M₀ (M₀ + L'), e (α / ((x + y : ℕ) : ℝ)))))‖
          ≤ ‖∑ x ∈ Ico M₀ (M₀ + L'), ∑ y ∈ range Y, e (α / ((x + y : ℕ) : ℝ))‖ +
            ‖∑ y ∈ range Y, ((∑ x ∈ Ico M₀ (M₀ + L'), e (α / (x : ℝ))) -
              (∑ x ∈ Ico M₀ (M₀ + L'), e (α / ((x + y : ℕ) : ℝ))))‖ := norm_add_le _ _
        _ ≤ (∑ x ∈ Ico M₀ (M₀ + L'), ‖∑ y ∈ range Y, e (α / ((x + y : ℕ) : ℝ))‖) +
            (∑ y ∈ range Y, ‖(∑ x ∈ Ico M₀ (M₀ + L'), e (α / (x : ℝ))) -
              (∑ x ∈ Ico M₀ (M₀ + L'), e (α / ((x + y : ℕ) : ℝ)))‖) :=
            add_le_add (norm_sum_le _ _) (norm_sum_le _ _)
        _ ≤ (∑ x ∈ Ico M₀ (M₀ + L'), ‖∑ y ∈ range Y, e (α / ((x + y : ℕ) : ℝ))‖) +
            (∑ _y ∈ range Y, (2 * (Y : ℝ))) :=
            add_le_add le_rfl (sum_le_sum hshift_y)
        _ = (∑ x ∈ Ico M₀ (M₀ + L'), ‖∑ y ∈ range Y, e (α / ((x + y : ℕ) : ℝ))‖) +
            (Y : ℝ) * (2 * (Y : ℝ)) := by simp
    have hdiv := div_le_div_of_nonneg_right hbd hY_Rpos.le
    rw [mul_div_cancel_left₀ _ hY_Rpos.ne', add_div, mul_div_cancel_left₀ _ hY_Rpos.ne',
      ← one_div_mul_eq_div] at hdiv
    exact hdiv
  -- Step 2: Geometric series expansion removes remainder R(x,y) with total error ≤ 1 per x!
  let β (x : ℕ) (j : Fin k) : ℝ := ((-1 : ℝ) ^ (j.1 + 1) * α) / (x : ℝ) ^ (j.1 + 2)
  let polySum (x : ℕ) : ℂ :=
    ∑ y ∈ range Y, e (∑ j : Fin k, β x j * ((y : ℝ) ^ (j.1 + 1)))
  have hpoly_approx : ∀ x ∈ Ico M₀ (M₀ + L'),
      ‖∑ y ∈ range Y, e (α / ((x + y : ℕ) : ℝ))‖ ≤ ‖polySum x‖ + 1 := by
    intro x hx
    have hxM : M ≤ x := le_trans hM₀_lo (mem_Ico.mp hx).1
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    have hfact : ∑ y ∈ range Y, e (α / ((x + y : ℕ) : ℝ)) =
        e (α / (x : ℝ)) * ∑ y ∈ range Y,
          e ((∑ j : Fin k, β x j * ((y : ℝ) ^ (j.1 + 1))) +
             α * ((-1 : ℝ) ^ (k + 1) * ((y : ℝ) / (x : ℝ)) ^ (k + 1) / ((x : ℝ) + (y : ℝ)))) := by
      rw [Finset.mul_sum]
      refine sum_congr rfl fun y _ => ?_
      rw [← e_add]
      congr 1
      have hge := geom_recip_expand hxpos (Nat.cast_nonneg y) k
      have hmul := congrArg (α * ·) hge
      have hlhs : α * (1 / ((x : ℝ) + (y : ℝ))) = α / ((x + y : ℕ) : ℝ) := by
        push_cast; ring
      rw [hlhs, mul_add, mul_add, Finset.mul_sum] at hmul
      rw [hmul]
      have h1 : α * (1 / (x : ℝ)) = α / (x : ℝ) := by ring
      have h2 : ∑ j : Fin k, α * (((-1 : ℝ) ^ (j.1 + 1) / (x : ℝ) ^ (j.1 + 2)) * (y : ℝ) ^ (j.1 + 1)) =
          ∑ j : Fin k, β x j * (y : ℝ) ^ (j.1 + 1) :=
        sum_congr rfl fun j _ => by dsimp only [β]; ring
      rw [h1, h2]; ring
    rw [hfact, norm_mul, norm_e, one_mul]
    have hrem : ‖(∑ y ∈ range Y, e ((∑ j : Fin k, β x j * ((y : ℝ) ^ (j.1 + 1))) +
            α * ((-1 : ℝ) ^ (k + 1) * ((y : ℝ) / (x : ℝ)) ^ (k + 1) / ((x : ℝ) + (y : ℝ))))) -
          polySum x‖ ≤ 1 := by
      dsimp only [polySum]
      rw [← Finset.sum_sub_distrib]
      calc ‖∑ y ∈ range Y, _‖ ≤ ∑ y ∈ range Y, ‖_‖ := norm_sum_le _ _
        _ ≤ ∑ _y ∈ range Y, (1 / (Y : ℝ)) := sum_le_sum fun y hy => by
            have hyY : (y : ℝ) ≤ Y := by exact_mod_cast (mem_range.mp hy).le
            have hstep := norm_e_sub_e_le
              ((∑ j : Fin k, β x j * ((y : ℝ) ^ (j.1 + 1))) +
                α * ((-1 : ℝ) ^ (k + 1) * ((y : ℝ) / (x : ℝ)) ^ (k + 1) / ((x : ℝ) + (y : ℝ))))
              (∑ j : Fin k, β x j * ((y : ℝ) ^ (j.1 + 1)))
            rw [add_sub_cancel_left] at hstep
            refine hstep.trans ?_
            have hR_le : |α * ((-1 : ℝ) ^ (k + 1) * ((y : ℝ) / (x : ℝ)) ^ (k + 1) / ((x : ℝ) + (y : ℝ)))| ≤
                (M : ℝ) ^ (-(3 : ℝ) / 2) := by
              rw [abs_mul, abs_of_pos hα_pos, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
                one_mul, abs_pow, abs_of_nonneg (by positivity), abs_of_pos (by positivity)]
              have hxM_R : (M : ℝ) ≤ x := by exact_mod_cast hxM
              have hxy_ge : (M : ℝ) ≤ (x : ℝ) + (y : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) y]
              have hyx_le : (y : ℝ) / (x : ℝ) ≤ (M : ℝ) ^ (-(1 : ℝ) / 2) := by
                calc (y : ℝ) / (x : ℝ) ≤ (Y : ℝ) / (M : ℝ) :=
                      div_le_div₀ (Nat.cast_nonneg _) hyY hMpos hxM_R
                  _ ≤ (M : ℝ) ^ ((1 : ℝ) / 2) / (M : ℝ) :=
                      div_le_div_of_nonneg_right hY_le_sqrtM hMpos.le
                  _ = (M : ℝ) ^ (-(1 : ℝ) / 2) := by
                      calc (M : ℝ) ^ ((1 : ℝ) / 2) / (M : ℝ)
                          = (M : ℝ) ^ ((1 : ℝ) / 2) / (M : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
                        _ = (M : ℝ) ^ (((1 : ℝ) / 2) - 1) := (Real.rpow_sub hMpos _ _).symm
                        _ = (M : ℝ) ^ (-(1 : ℝ) / 2) := by congr 1; ring
              calc α * (((y : ℝ) / (x : ℝ)) ^ (k + 1) / ((x : ℝ) + (y : ℝ)))
                  ≤ (M : ℝ) ^ ((k : ℝ) / 2) * (((M : ℝ) ^ (-(1 : ℝ) / 2)) ^ (k + 1) / (M : ℝ)) := by
                    refine mul_le_mul hα_hi ?_ (by positivity) (Real.rpow_nonneg hMpos.le _)
                    exact div_le_div₀ (by positivity) (pow_le_pow_left₀ (by positivity) hyx_le _) hMpos hxy_ge
                _ = (M : ℝ) ^ (-(3 : ℝ) / 2) := by
                    rw [← Real.rpow_natCast ((M : ℝ) ^ _), ← Real.rpow_mul hMpos.le]
                    calc (M : ℝ) ^ ((k : ℝ) / 2) * ((M : ℝ) ^ (-(1 : ℝ) / 2 * ((k + 1 : ℕ) : ℝ)) / (M : ℝ))
                        = (M : ℝ) ^ ((k : ℝ) / 2) * ((M : ℝ) ^ (-(1 : ℝ) / 2 * ((k + 1 : ℕ) : ℝ)) / (M : ℝ) ^ (1 : ℝ)) := by
                          rw [Real.rpow_one]
                      _ = (M : ℝ) ^ ((k : ℝ) / 2) * (M : ℝ) ^ (-(1 : ℝ) / 2 * ((k + 1 : ℕ) : ℝ) - 1) := by
                          rw [← Real.rpow_sub hMpos]
                      _ = (M : ℝ) ^ ((k : ℝ) / 2 + (-(1 : ℝ) / 2 * ((k + 1 : ℕ) : ℝ) - 1)) := by
                          rw [← Real.rpow_add hMpos]
                      _ = (M : ℝ) ^ (-(3 : ℝ) / 2) := by congr 1; push_cast; ring
            have h2pi_le : 2 * Real.pi * (M : ℝ) ^ (-(3 : ℝ) / 2) ≤ 1 / (Y : ℝ) := by
              have hpi : Real.pi < 4 := Real.pi_lt_four
              have hM32 : (M : ℝ) ^ ((3 : ℝ) / 2) = (M : ℝ) * (M : ℝ) ^ ((1 : ℝ) / 2) := by
                calc (M : ℝ) ^ ((3 : ℝ) / 2) = (M : ℝ) ^ ((1 : ℝ) + (1 : ℝ) / 2) := by congr 1; ring
                  _ = (M : ℝ) ^ (1 : ℝ) * (M : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_add hMpos _ _
                  _ = (M : ℝ) * (M : ℝ) ^ ((1 : ℝ) / 2) := by rw [Real.rpow_one]
              rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring, Real.rpow_neg hMpos.le,
                hM32, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hY_Rpos]
              have hM100 : (100 : ℝ) ≤ M := by exact_mod_cast hM
              have h1 : 2 * Real.pi * (Y : ℝ) ≤ 8 * (M : ℝ) ^ ((1 : ℝ) / 2) := by nlinarith
              nlinarith [Real.rpow_pos_of_pos hMpos ((1 : ℝ) / 2)]
            exact (mul_le_mul_of_nonneg_left hR_le (by positivity)).trans h2pi_le
        _ = 1 := by simp [hY_Rpos.ne']
    calc ‖∑ y ∈ range Y, e ((∑ j : Fin k, β x j * ((y : ℝ) ^ (j.1 + 1))) +
            α * ((-1 : ℝ) ^ (k + 1) * ((y : ℝ) / (x : ℝ)) ^ (k + 1) / ((x : ℝ) + (y : ℝ))))‖
        = ‖polySum x + ((∑ y ∈ range Y, e ((∑ j : Fin k, β x j * ((y : ℝ) ^ (j.1 + 1))) +
            α * ((-1 : ℝ) ^ (k + 1) * ((y : ℝ) / (x : ℝ)) ^ (k + 1) / ((x : ℝ) + (y : ℝ))))) - polySum x)‖ := by
          congr 1; ring
      _ ≤ ‖polySum x‖ + ‖_‖ := norm_add_le _ _
      _ ≤ ‖polySum x‖ + 1 := by linarith
  -- Step 3: Discrete grid G_j = 8 * s * Y^(j+1) and rounding a(x) : ∀ j : Fin k, Fin (G j)
  let G : Fin k → ℕ := fun j => 8 * s * Y ^ (j.1 + 1)
  have hG_pos : ∀ j : Fin k, 1 ≤ G j := fun j => by
    dsimp only [G]
    have h1 : 1 ≤ Y ^ (j.1 + 1) := one_le_pow₀ hY_pos
    nlinarith
  have hG_Rpos : ∀ j : Fin k, (0 : ℝ) < G j := fun j => by
    exact_mod_cast (by have := hG_pos j; omega : 0 < G j)
  let aOf (x : ℕ) : ∀ j : Fin k, Fin (G j) := fun j =>
    ⟨((Int.floor ((G j : ℝ) * β x j)).emod (G j : ℤ)).toNat, by
      have hGj : (0 : ℤ) < (G j : ℤ) := by exact_mod_cast (by have := hG_pos j; omega : 0 < G j)
      have hnn : 0 ≤ (Int.floor ((G j : ℝ) * β x j)).emod (G j : ℤ) := Int.emod_nonneg _ hGj.ne'
      have hlt : (Int.floor ((G j : ℝ) * β x j)).emod (G j : ℤ) < (G j : ℤ) := Int.emod_lt_of_pos _ hGj
      omega⟩
  let mOf (x : ℕ) (j : Fin k) : ℤ := (Int.floor ((G j : ℝ) * β x j)).ediv (G j : ℤ)
  have hround : ∀ (x : ℕ) (j : Fin k),
      (mOf x j : ℝ) + ((aOf x j : ℕ) : ℝ) / (G j : ℝ) ≤ β x j ∧
      β x j < (mOf x j : ℝ) + (((aOf x j : ℕ) : ℝ) + 1) / (G j : ℝ) := by
    intro x j
    have hGj_Zpos : (0 : ℤ) < (G j : ℤ) := by exact_mod_cast (by have := hG_pos j; omega : 0 < G j)
    have hdm := Int.emod_add_mul_ediv (Int.floor ((G j : ℝ) * β x j)) (G j : ℤ)
    have hmod_nn : 0 ≤ (Int.floor ((G j : ℝ) * β x j)).emod (G j : ℤ) := Int.emod_nonneg _ hGj_Zpos.ne'
    have hfl_le : (Int.floor ((G j : ℝ) * β x j) : ℝ) ≤ (G j : ℝ) * β x j := Int.floor_le _
    have hlt_fl : (G j : ℝ) * β x j < (Int.floor ((G j : ℝ) * β x j) : ℝ) + 1 := Int.lt_floor_add_one _
    have hcast : (Int.floor ((G j : ℝ) * β x j) : ℝ) =
        (G j : ℝ) * (mOf x j : ℝ) + ((aOf x j : ℕ) : ℝ) := by
      have h1 : ((((aOf x j : ℕ) : ℤ) + (G j : ℤ) * mOf x j : ℤ) : ℝ) =
          (Int.floor ((G j : ℝ) * β x j) : ℝ) := by
        have ha : ((aOf x j : ℕ) : ℤ) = (Int.floor ((G j : ℝ) * β x j)).emod (G j : ℤ) := by
          dsimp only [aOf]
          exact Int.toNat_of_nonneg hmod_nn
        rw [ha]; exact_mod_cast hdm
      push_cast at h1; linarith
    have hGR := hG_Rpos j
    constructor
    · rw [← mul_le_mul_iff_right₀ hGR]
      field_simp [hGR.ne']
      linarith
    · rw [← mul_lt_mul_iff_right₀ hGR]
      field_simp [hGR.ne']
      linarith
  -- Step 4: Discrete Abel summation bounds ‖polySum x‖^{2s} by partial Weyl sums at aOf x!
  let partialWeyl (t : ℕ) (a : ∀ j : Fin k, Fin (G j)) : ℂ :=
    ∑ y ∈ range t, weylChar k G a (y : ℤ)
  have hpoly_abel : ∀ x : ℕ,
      ‖polySum x‖ ^ (2 * s) ≤
        (2 : ℝ) ^ (2 * s) * (‖partialWeyl Y (aOf x)‖ ^ (2 * s) +
          (1 / (Y : ℝ)) * ∑ t ∈ range Y, ‖partialWeyl (t + 1) (aOf x)‖ ^ (2 * s)) := by
    intro x
    let δβ (j : Fin k) : ℝ := β x j - (mOf x j : ℝ) - ((aOf x j : ℕ) : ℝ) / (G j : ℝ)
    have hδβ_bounds : ∀ j : Fin k, 0 ≤ δβ j ∧ δβ j < 1 / (G j : ℝ) := fun j => by
      have hr := hround x j
      dsimp only [δβ]
      have : (((aOf x j : ℕ) : ℝ) + 1) / (G j : ℝ) = ((aOf x j : ℕ) : ℝ) / (G j : ℝ) + 1 / (G j : ℝ) := by ring
      constructor <;> linarith
    let φ (y : ℕ) : ℝ := ∑ j : Fin k, δβ j * ((y : ℝ) ^ (j.1 + 1))
    have hterm_eq : ∀ y : ℕ, e (∑ j : Fin k, β x j * ((y : ℝ) ^ (j.1 + 1))) =
        e (φ y) * weylChar k G (aOf x) (y : ℤ) := by
      intro y
      have hweyl : weylChar k G (aOf x) (y : ℤ) =
          e (∑ j : Fin k, (((aOf x j : ℕ) : ℝ) / (G j : ℝ)) * ((y : ℝ) ^ (j.1 + 1))) := by
        dsimp only [weylChar]
        have hsum_e : ∀ (S : Finset (Fin k)) (f : Fin k → ℝ), ∏ j ∈ S, e (f j) = e (∑ j ∈ S, f j) := by
          intro S f
          induction S using Finset.induction_on with
          | empty => simp [e_zero]
          | @insert u T hu ih => rw [prod_insert hu, sum_insert hu, ih, e_add]
        rw [hsum_e]; congr 1
        refine sum_congr rfl fun j _ => ?_
        push_cast; ring
      rw [hweyl, ← e_add]
      have hdiff_int : (∑ j : Fin k, β x j * ((y : ℝ) ^ (j.1 + 1))) -
          (φ y + ∑ j : Fin k, (((aOf x j : ℕ) : ℝ) / (G j : ℝ)) * ((y : ℝ) ^ (j.1 + 1))) =
          ((∑ j : Fin k, mOf x j * ((y : ℤ) ^ (j.1 + 1)) : ℤ) : ℝ) := by
        dsimp only [φ, δβ]
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        push_cast
        refine sum_congr rfl fun j _ => by ring
      have h1 : ∑ j : Fin k, β x j * ((y : ℝ) ^ (j.1 + 1)) =
          (φ y + ∑ j : Fin k, (((aOf x j : ℕ) : ℝ) / (G j : ℝ)) * ((y : ℝ) ^ (j.1 + 1))) +
          ((∑ j : Fin k, mOf x j * ((y : ℤ) ^ (j.1 + 1)) : ℤ) : ℝ) := by linarith
      rw [h1, e_add, e_int, mul_one]
    have hpoly_le : ‖polySum x‖ ≤ ‖partialWeyl Y (aOf x)‖ +
        (1 / (Y : ℝ)) * ∑ t ∈ range Y, ‖partialWeyl (t + 1) (aOf x)‖ := by
      dsimp only [polySum]
      simp_rw [hterm_eq]
      have hYeq : Y = (Y - 1) + 1 := by omega
      rw [hYeq, abel_sum_range_succ (Y - 1) (fun y => e (φ y)) (fun y => weylChar k G (aOf x) (y : ℤ))]
      rw [← hYeq]
      have hdiff_φ : ∀ t ∈ range (Y - 1), ‖e (φ (t + 1)) - e (φ t)‖ ≤ 1 / (Y : ℝ) := by
        intro t ht
        have htY : t + 1 ≤ Y := by have := mem_range.mp ht; omega
        refine (norm_e_sub_e_le _ _).trans ?_
        have hstep : |φ (t + 1) - φ t| ≤ 1 / (8 * (Y : ℝ)) := by
          dsimp only [φ]
          rw [← Finset.sum_sub_distrib]
          calc |∑ j : Fin k, (δβ j * ((t + 1 : ℕ) : ℝ) ^ (j.1 + 1) - δβ j * (t : ℝ) ^ (j.1 + 1))|
              ≤ ∑ j : Fin k, |δβ j * (((t + 1 : ℕ) : ℝ) ^ (j.1 + 1) - (t : ℝ) ^ (j.1 + 1))| := by
                have := Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset (Fin k)))
                  (f := fun j => δβ j * ((t + 1 : ℕ) : ℝ) ^ (j.1 + 1) - δβ j * (t : ℝ) ^ (j.1 + 1))
                refine this.trans_eq (sum_congr rfl fun j _ => by congr 1; ring)
            _ ≤ ∑ j : Fin k, (1 / (G j : ℝ)) * (((j.1 + 1 : ℕ) : ℝ) * (Y : ℝ) ^ j.1) := by
                refine sum_le_sum fun j _ => ?_
                have hpow_diff : ((t + 1 : ℕ) : ℝ) ^ (j.1 + 1) - (t : ℝ) ^ (j.1 + 1) ≤
                    ((j.1 + 1 : ℕ) : ℝ) * (Y : ℝ) ^ j.1 := by
                  have hgeom : ((t + 1 : ℕ) : ℝ) ^ (j.1 + 1) - (t : ℝ) ^ (j.1 + 1) =
                      (((t + 1 : ℕ) : ℝ) - (t : ℝ)) *
                        ∑ i ∈ range (j.1 + 1), ((t + 1 : ℕ) : ℝ) ^ i * (t : ℝ) ^ (j.1 - i) := by
                    have h := geom_sum₂_mul ((t + 1 : ℕ) : ℝ) (t : ℝ) (j.1 + 1)
                    simp only [Nat.add_sub_cancel] at h
                    linarith
                  rw [hgeom]
                  have hsub1 : ((t + 1 : ℕ) : ℝ) - (t : ℝ) = 1 := by push_cast; ring
                  rw [hsub1, one_mul]
                  calc ∑ i ∈ range (j.1 + 1), ((t + 1 : ℕ) : ℝ) ^ i * (t : ℝ) ^ (j.1 - i)
                      ≤ ∑ _i ∈ range (j.1 + 1), (Y : ℝ) ^ j.1 := sum_le_sum fun i hi => by
                        have hij : i ≤ j.1 := Nat.lt_succ_iff.mp (mem_range.mp hi)
                        have ht1Y : ((t + 1 : ℕ) : ℝ) ≤ Y := by exact_mod_cast htY
                        have htY' : (t : ℝ) ≤ Y := by exact_mod_cast (by omega : t ≤ Y)
                        calc ((t + 1 : ℕ) : ℝ) ^ i * (t : ℝ) ^ (j.1 - i)
                            ≤ (Y : ℝ) ^ i * (Y : ℝ) ^ (j.1 - i) :=
                              mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) ht1Y i)
                                (pow_le_pow_left₀ (Nat.cast_nonneg _) htY' _) (by positivity) (by positivity)
                          _ = (Y : ℝ) ^ (i + (j.1 - i)) := (pow_add _ _ _).symm
                          _ = (Y : ℝ) ^ j.1 := by congr 1; omega
                    _ = ((j.1 + 1 : ℕ) : ℝ) * (Y : ℝ) ^ j.1 := by simp
                have hpow_nn : 0 ≤ ((t + 1 : ℕ) : ℝ) ^ (j.1 + 1) - (t : ℝ) ^ (j.1 + 1) := by
                  have : (t : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ t
                  linarith [pow_le_pow_left₀ (Nat.cast_nonneg t) this (j.1 + 1)]
                rw [abs_mul, abs_of_nonneg (hδβ_bounds j).1, abs_of_nonneg hpow_nn]
                exact mul_le_mul (hδβ_bounds j).2.le hpow_diff hpow_nn (by positivity)
            _ = (∑ j : Fin k, ((j.1 + 1 : ℕ) : ℝ)) / (8 * (s : ℝ) * (Y : ℝ)) := by
                rw [Finset.sum_div]
                refine sum_congr rfl fun j _ => ?_
                dsimp only [G]
                push_cast
                rw [pow_succ]
                field_simp [hspos.ne', hY_Rpos.ne', (pow_pos hY_Rpos j.1).ne']
            _ ≤ 1 / (8 * (Y : ℝ)) := by
                have hsum_k : (∑ j : Fin k, ((j.1 + 1 : ℕ) : ℝ)) ≤ (s : ℝ) := by
                  have hnat : ∑ j : Fin k, (j.1 + 1) ≤ k ^ 2 := by
                    calc ∑ j : Fin k, (j.1 + 1) ≤ ∑ _j : Fin k, k := sum_le_sum fun j _ => j.2
                      _ = k * k := by simp
                      _ = k ^ 2 := (sq k).symm
                  have hks : k ^ 2 ≤ s := by dsimp [s]; omega
                  exact_mod_cast (hnat.trans hks)
                rw [div_le_div_iff₀ (by positivity) (by positivity)]
                nlinarith
        have hpi : Real.pi < 4 := Real.pi_lt_four
        calc 2 * Real.pi * |φ (t + 1) - φ t| ≤ 2 * Real.pi * (1 / (8 * (Y : ℝ))) :=
              mul_le_mul_of_nonneg_left hstep (by positivity)
          _ ≤ 1 / (Y : ℝ) := by
              rw [show 2 * Real.pi * (1 / (8 * (Y : ℝ))) = (Real.pi / 4) * (1 / (Y : ℝ)) by ring]
              have : Real.pi / 4 ≤ 1 := by linarith
              nlinarith [show (0 : ℝ) < 1 / (Y : ℝ) by positivity]
      calc ‖e (φ (Y - 1)) * partialWeyl Y (aOf x) -
            ∑ t ∈ range (Y - 1), (e (φ (t + 1)) - e (φ t)) * partialWeyl (t + 1) (aOf x)‖
          ≤ ‖e (φ (Y - 1)) * partialWeyl Y (aOf x)‖ +
            ‖∑ t ∈ range (Y - 1), (e (φ (t + 1)) - e (φ t)) * partialWeyl (t + 1) (aOf x)‖ := norm_sub_le _ _
        _ ≤ ‖partialWeyl Y (aOf x)‖ +
            ∑ t ∈ range (Y - 1), ‖e (φ (t + 1)) - e (φ t)‖ * ‖partialWeyl (t + 1) (aOf x)‖ := by
            rw [norm_mul, norm_e, one_mul]
            refine add_le_add le_rfl ((norm_sum_le _ _).trans_eq (sum_congr rfl fun _ _ => norm_mul _ _))
        _ ≤ ‖partialWeyl Y (aOf x)‖ +
            ∑ t ∈ range (Y - 1), (1 / (Y : ℝ)) * ‖partialWeyl (t + 1) (aOf x)‖ :=
            add_le_add le_rfl (sum_le_sum fun t ht => mul_le_mul_of_nonneg_right (hdiff_φ t ht) (norm_nonneg _))
        _ ≤ ‖partialWeyl Y (aOf x)‖ +
            (1 / (Y : ℝ)) * ∑ t ∈ range Y, ‖partialWeyl (t + 1) (aOf x)‖ := by
            rw [← Finset.mul_sum]
            refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (by positivity))
            exact sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => norm_nonneg _)
    -- Raise to 2s-th power using (A + B)^(2s) ≤ 2^(2s) * (A^(2s) + B^(2s)) and Jensen
    have h2s_ge1 : (1 : ℝ) ≤ (2 * s : ℕ) := by exact_mod_cast (by omega : 1 ≤ 2 * s)
    have hjensen : ((1 / (Y : ℝ)) * ∑ t ∈ range Y, ‖partialWeyl (t + 1) (aOf x)‖) ^ (2 * s) ≤
        (1 / (Y : ℝ)) * ∑ t ∈ range Y, ‖partialWeyl (t + 1) (aOf x)‖ ^ (2 * s) := by
      have hr := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := range Y)
        (f := fun t => ‖partialWeyl (t + 1) (aOf x)‖) h2s_ge1 (fun _ _ => norm_nonneg _)
      simp only [card_range] at hr
      have hsub : ((2 * s : ℕ) : ℝ) - 1 = ((2 * s - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [hsub, Real.rpow_natCast, Real.rpow_natCast] at hr
      simp_rw [Real.rpow_natCast] at hr
      rw [mul_pow, one_div_pow, one_div_mul_eq_div, one_div_mul_eq_div]
      rw [div_le_div_iff₀ (pow_pos hY_Rpos _) hY_Rpos]
      have hYpow : (Y : ℝ) ^ (2 * s) = (Y : ℝ) ^ (2 * s - 1) * (Y : ℝ) := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      rw [hYpow]
      nlinarith [hr]
    have hab : ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → (A + B) ^ (2 * s) ≤ (2 : ℝ) ^ (2 * s) * (A ^ (2 * s) + B ^ (2 * s)) := by
      intro A B hA hB
      have hmax : A + B ≤ 2 * max A B := by linarith [le_max_left A B, le_max_right A B]
      calc (A + B) ^ (2 * s) ≤ (2 * max A B) ^ (2 * s) :=
            pow_le_pow_left₀ (by linarith) hmax _
        _ = (2 : ℝ) ^ (2 * s) * (max A B) ^ (2 * s) := mul_pow _ _ _
        _ ≤ (2 : ℝ) ^ (2 * s) * (A ^ (2 * s) + B ^ (2 * s)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rcases le_total A B with h | h
            · rw [max_eq_right h]; linarith [pow_nonneg hA (2 * s)]
            · rw [max_eq_left h]; linarith [pow_nonneg hB (2 * s)]
    calc ‖polySum x‖ ^ (2 * s)
        ≤ (‖partialWeyl Y (aOf x)‖ + (1 / (Y : ℝ)) * ∑ t ∈ range Y, ‖partialWeyl (t + 1) (aOf x)‖) ^ (2 * s) :=
          pow_le_pow_left₀ (norm_nonneg _) hpoly_le _
      _ ≤ (2 : ℝ) ^ (2 * s) * (‖partialWeyl Y (aOf x)‖ ^ (2 * s) +
            ((1 / (Y : ℝ)) * ∑ t ∈ range Y, ‖partialWeyl (t + 1) (aOf x)‖) ^ (2 * s)) :=
          hab _ _ (norm_nonneg _) (by positivity)
      _ ≤ (2 : ℝ) ^ (2 * s) * (‖partialWeyl Y (aOf x)‖ ^ (2 * s) +
            (1 / (Y : ℝ)) * ∑ t ∈ range Y, ‖partialWeyl (t + 1) (aOf x)‖ ^ (2 * s)) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl hjensen) (by positivity)
  -- Step 5: Multiplicity bound for x ↦ aOf x on Ico M₀ (M₀ + L') via the single index r!
  have hmult : ∀ a₀ : ∀ j : Fin k, Fin (G j),
      (((Ico M₀ (M₀ + L')).filter fun x => aOf x = a₀).card : ℝ) ≤ 12 * (L : ℝ) / (Y : ℝ) := by
    obtain ⟨r, hr1, hur_lo, hur_hi⟩ := exists_good_deriv_index hM hM₀_lo hM₀_hi hk hα_lo hα_hi hkY
    let u_r : ℝ := ((r.1 + 2 : ℕ) : ℝ) * α / (M₀ : ℝ) ^ (r.1 + 3)
    have hur_pos : 0 < u_r := lt_of_lt_of_le (Real.rpow_pos_of_pos hM₀pos _) hur_lo
    let m := r.1 + 2
    have hm_le : m ≤ k + 1 := by omega
    -- Ratio (x / M₀)^(2m) ≤ 2 for x ≤ M₀ + L
    have hratio2 : ∀ x : ℕ, x ≤ M₀ + L → ((x : ℝ) / (M₀ : ℝ)) ^ (2 * m) ≤ 2 := by
      intro x hx
      have h1 : (x : ℝ) / (M₀ : ℝ) ≤ 1 + 1 / (4 * (k : ℝ)) := by
        have hLM : (L : ℝ) ≤ (M₀ : ℝ) / (4 * (k : ℝ)) := by
          have h1 : L * (4 * k) ≤ M := Nat.div_mul_le_self M (4 * k)
          have h2 : (L : ℝ) * (4 * (k : ℝ)) ≤ (M₀ : ℝ) := by exact_mod_cast (h1.trans hM₀_lo)
          rw [le_div_iff₀ (by positivity)]; linarith
        have hxR : (x : ℝ) ≤ (M₀ : ℝ) + (L : ℝ) := by exact_mod_cast hx
        rw [div_le_iff₀ hM₀pos]
        have : (1 + 1 / (4 * (k : ℝ))) * (M₀ : ℝ) = (M₀ : ℝ) + (M₀ : ℝ) / (4 * (k : ℝ)) := by ring
        linarith
      have h2 : 1 + 1 / (4 * (k : ℝ)) ≤ Real.exp (1 / (4 * (k : ℝ))) := by
        linarith [Real.add_one_le_exp (1 / (4 * (k : ℝ)))]
      calc ((x : ℝ) / (M₀ : ℝ)) ^ (2 * m)
          ≤ (Real.exp (1 / (4 * (k : ℝ)))) ^ (2 * m) :=
            pow_le_pow_left₀ (by positivity) (h1.trans h2) _
        _ = Real.exp (((2 * m : ℕ) : ℝ) * (1 / (4 * (k : ℝ)))) := (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp (5 / 8) := by
            refine Real.exp_le_exp.mpr ?_
            have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
            have hmR : (m : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast hm_le
            rw [show ((2 * m : ℕ) : ℝ) * (1 / (4 * (k : ℝ))) = (m : ℝ) / (2 * (k : ℝ)) by push_cast; ring]
            rw [div_le_iff₀ (by positivity)]
            nlinarith
        _ ≤ 2 := by
            have hlt : (5 / 8 : ℝ) ≤ 0.69 := by norm_num
            have hlog2 : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
            calc Real.exp (5 / 8) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by linarith)
              _ = 2 := Real.exp_log (by norm_num)
    -- Spacing and total variation of β x r on [M₀, M₀ + L]
    have hβ_dist : ∀ x₁ x₂ : ℕ, M₀ ≤ x₁ → x₁ ≤ x₂ → x₂ ≤ M₀ + L →
        ((x₂ : ℝ) - (x₁ : ℝ)) * (u_r / 2) ≤ |β x₁ r - β x₂ r| ∧
        |β x₁ r - β x₂ r| ≤ ((x₂ : ℝ) - (x₁ : ℝ)) * u_r := by
      intro x₁ x₂ hx₁ h12 hx₂
      have hx₁pos : (0 : ℝ) < x₁ := by exact_mod_cast (by omega : 0 < x₁)
      have hx₂pos : (0 : ℝ) < x₂ := by exact_mod_cast (by omega : 0 < x₂)
      have h12R : (x₁ : ℝ) ≤ x₂ := by exact_mod_cast h12
      have hM₀x₁ : (M₀ : ℝ) ≤ x₁ := by exact_mod_cast hx₁
      have habs : |β x₁ r - β x₂ r| = α * (1 / (x₁ : ℝ) ^ m - 1 / (x₂ : ℝ) ^ m) := by
        dsimp only [β, m]
        have heq : (-1 : ℝ) ^ (r.1 + 1) * α / (x₁ : ℝ) ^ (r.1 + 2) -
            (-1 : ℝ) ^ (r.1 + 1) * α / (x₂ : ℝ) ^ (r.1 + 2) =
            (-1 : ℝ) ^ (r.1 + 1) * (α * (1 / (x₁ : ℝ) ^ (r.1 + 2) - 1 / (x₂ : ℝ) ^ (r.1 + 2))) := by ring
        rw [heq, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg]
        have : (x₁ : ℝ) ^ (r.1 + 2) ≤ (x₂ : ℝ) ^ (r.1 + 2) := pow_le_pow_left₀ hx₁pos.le h12R _
        have : 1 / (x₂ : ℝ) ^ (r.1 + 2) ≤ 1 / (x₁ : ℝ) ^ (r.1 + 2) :=
          one_div_le_one_div_of_le (by positivity) this
        exact mul_nonneg hα_pos.le (by linarith)
      rw [habs]
      have hbd := inv_pow_sub_bounds hx₁pos h12R m
      constructor
      · have h1 : ((x₂ : ℝ) - (x₁ : ℝ)) * (u_r / 2) ≤
            α * ((m : ℝ) * ((x₂ : ℝ) - (x₁ : ℝ)) * (x₁ : ℝ) ^ (m - 1) / ((x₁ : ℝ) ^ m * (x₂ : ℝ) ^ m)) := by
          have hr2 := hratio2 x₂ hx₂
          have hx₂_le : (x₂ : ℝ) ^ (2 * m) ≤ 2 * (M₀ : ℝ) ^ (2 * m) := by
            rw [div_pow, div_le_iff₀ (by positivity)] at hr2; exact hr2
          have hden_le : (x₁ : ℝ) ^ m * (x₂ : ℝ) ^ m ≤ 2 * (M₀ : ℝ) ^ (2 * m) := by
            calc (x₁ : ℝ) ^ m * (x₂ : ℝ) ^ m ≤ (x₂ : ℝ) ^ m * (x₂ : ℝ) ^ m :=
                  mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx₁pos.le h12R m) (by positivity)
              _ = (x₂ : ℝ) ^ (2 * m) := by rw [← pow_add, two_mul]
              _ ≤ 2 * (M₀ : ℝ) ^ (2 * m) := hx₂_le
          have hnum_ge : (M₀ : ℝ) ^ (m - 1) ≤ (x₁ : ℝ) ^ (m - 1) :=
            pow_le_pow_left₀ hM₀pos.le hM₀x₁ _
          have hdiv_ge : (M₀ : ℝ) ^ (m - 1) / (2 * (M₀ : ℝ) ^ (2 * m)) ≤
              (x₁ : ℝ) ^ (m - 1) / ((x₁ : ℝ) ^ m * (x₂ : ℝ) ^ m) :=
            div_le_div₀ (by positivity) hnum_ge (by positivity) hden_le
          have hsimp : (M₀ : ℝ) ^ (m - 1) / (2 * (M₀ : ℝ) ^ (2 * m)) = 1 / (2 * (M₀ : ℝ) ^ (r.1 + 3)) := by
            have hpow : (M₀ : ℝ) ^ (2 * m) = (M₀ : ℝ) ^ (m - 1) * (M₀ : ℝ) ^ (r.1 + 3) := by
              rw [← pow_add]; congr 1; dsimp [m]; omega
            rw [hpow]; field_simp [pow_ne_zero _ hM₀pos.ne']
          rw [hsimp] at hdiv_ge
          have hmul := mul_le_mul_of_nonneg_left hdiv_ge (show 0 ≤ α * (m : ℝ) * ((x₂ : ℝ) - (x₁ : ℝ)) by
            exact mul_nonneg (mul_nonneg hα_pos.le (Nat.cast_nonneg _)) (by linarith))
          have hlhs : α * (m : ℝ) * ((x₂ : ℝ) - (x₁ : ℝ)) * (1 / (2 * (M₀ : ℝ) ^ (r.1 + 3))) =
              ((x₂ : ℝ) - (x₁ : ℝ)) * (u_r / 2) := by dsimp only [u_r, m]; ring
          have hrhs : α * (m : ℝ) * ((x₂ : ℝ) - (x₁ : ℝ)) * ((x₁ : ℝ) ^ (m - 1) / ((x₁ : ℝ) ^ m * (x₂ : ℝ) ^ m)) =
              α * ((m : ℝ) * ((x₂ : ℝ) - (x₁ : ℝ)) * (x₁ : ℝ) ^ (m - 1) / ((x₁ : ℝ) ^ m * (x₂ : ℝ) ^ m)) := by ring
          linarith
        exact h1.trans (mul_le_mul_of_nonneg_left hbd.1 hα_pos.le)
      · refine (mul_le_mul_of_nonneg_left hbd.2 hα_pos.le).trans ?_
        have hfrac : (x₂ : ℝ) ^ (m - 1) / ((x₁ : ℝ) ^ m * (x₂ : ℝ) ^ m) ≤ 1 / (M₀ : ℝ) ^ (r.1 + 3) := by
          have hpow : (x₂ : ℝ) ^ m = (x₂ : ℝ) ^ (m - 1) * (x₂ : ℝ) := by
            rw [← pow_succ, Nat.sub_add_cancel (by dsimp [m]; omega)]
          rw [hpow]
          have hsimp : (x₂ : ℝ) ^ (m - 1) / ((x₁ : ℝ) ^ m * ((x₂ : ℝ) ^ (m - 1) * (x₂ : ℝ))) =
              1 / ((x₁ : ℝ) ^ m * (x₂ : ℝ)) := by
            field_simp [pow_ne_zero _ hx₂pos.ne', pow_ne_zero _ hx₁pos.ne', hx₂pos.ne']
          rw [hsimp]
          refine one_div_le_one_div_of_le (by positivity) ?_
          have hM₀p : (M₀ : ℝ) ^ (r.1 + 3) = (M₀ : ℝ) ^ m * (M₀ : ℝ) := by
            dsimp [m]; rw [← pow_succ]
          rw [hM₀p]
          exact mul_le_mul (pow_le_pow_left₀ hM₀pos.le hM₀x₁ m) (hM₀x₁.trans h12R) hM₀pos.le (by positivity)
        have hmul := mul_le_mul_of_nonneg_left hfrac (show 0 ≤ α * (m : ℝ) * ((x₂ : ℝ) - (x₁ : ℝ)) by
          exact mul_nonneg (mul_nonneg hα_pos.le (Nat.cast_nonneg _)) (by linarith))
        have hlhs : α * ((m : ℝ) * ((x₂ : ℝ) - (x₁ : ℝ)) * (x₂ : ℝ) ^ (m - 1) / ((x₁ : ℝ) ^ m * (x₂ : ℝ) ^ m)) =
            α * (m : ℝ) * ((x₂ : ℝ) - (x₁ : ℝ)) * ((x₂ : ℝ) ^ (m - 1) / ((x₁ : ℝ) ^ m * (x₂ : ℝ) ^ m)) := by ring
        have hrhs : α * (m : ℝ) * ((x₂ : ℝ) - (x₁ : ℝ)) * (1 / (M₀ : ℝ) ^ (r.1 + 3)) =
            ((x₂ : ℝ) - (x₁ : ℝ)) * u_r := by dsimp only [u_r, m]; ring
        linarith
    intro a₀
    let S := (Ico M₀ (M₀ + L')).filter fun x => aOf x = a₀
    by_cases hSne : S.Nonempty
    · let W := S.image (fun x => mOf x r)
      have hWne : W.Nonempty := hSne.image _
      let wmin := W.min' hWne
      let wmax := W.max' hWne
      -- Bound W.card ≤ L * u_r + 2
      have hW_card : (W.card : ℝ) ≤ (L : ℝ) * u_r + 2 := by
        obtain ⟨x₁, hx₁, hmx₁⟩ := mem_image.mp (W.min'_mem hWne)
        obtain ⟨x₂, hx₂, hmx₂⟩ := mem_image.mp (W.max'_mem hWne)
        have hx₁_ico := mem_Ico.mp (mem_filter.mp hx₁).1
        have hx₂_ico := mem_Ico.mp (mem_filter.mp hx₂).1
        have ha₁ : aOf x₁ r = a₀ r := congrFun (mem_filter.mp hx₁).2 r
        have ha₂ : aOf x₂ r = a₀ r := congrFun (mem_filter.mp hx₂).2 r
        have hr₁ := hround x₁ r
        have hr₂ := hround x₂ r
        rw [hmx₁, ha₁] at hr₁
        rw [hmx₂, ha₂] at hr₂
        have hβ_le : |β x₁ r - β x₂ r| ≤ (L : ℝ) * u_r := by
          rcases le_total x₁ x₂ with h12 | h21
          · have hd := (hβ_dist x₁ x₂ hx₁_ico.1 h12 (by omega)).2
            have hdiff : (x₂ : ℝ) - (x₁ : ℝ) ≤ L := by
              have : x₂ - x₁ ≤ L := by omega
              rw [← Nat.cast_sub h12]; exact_mod_cast this
            exact hd.trans (mul_le_mul_of_nonneg_right hdiff hur_pos.le)
          · rw [abs_sub_comm]
            have hd := (hβ_dist x₂ x₁ hx₂_ico.1 h21 (by omega)).2
            have hdiff : (x₁ : ℝ) - (x₂ : ℝ) ≤ L := by
              have : x₁ - x₂ ≤ L := by omega
              rw [← Nat.cast_sub h21]; exact_mod_cast this
            exact hd.trans (mul_le_mul_of_nonneg_right hdiff hur_pos.le)
        have hw_sub : (wmax : ℝ) - (wmin : ℝ) ≤ (L : ℝ) * u_r + 1 := by
          have hG1 : 1 / (G r : ℝ) ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hG_pos r) (hG_Rpos r).le
          have h1 : (wmax : ℝ) - (wmin : ℝ) - 1 / (G r : ℝ) ≤ β x₂ r - β x₁ r := by
            have : (((a₀ r : ℕ) : ℝ) + 1) / (G r : ℝ) = ((a₀ r : ℕ) : ℝ) / (G r : ℝ) + 1 / (G r : ℝ) := by ring
            linarith
          have h2 : β x₂ r - β x₁ r ≤ |β x₁ r - β x₂ r| := by
            rw [abs_sub_comm]; exact le_abs_self _
          linarith
        have hW_sub : W ⊆ Finset.Icc wmin wmax := fun w hw =>
          Finset.mem_Icc.mpr ⟨W.min'_le w hw, W.le_max' w hw⟩
        have hW_le : W.card ≤ (Finset.Icc wmin wmax).card := card_le_card hW_sub
        have hIcc_card : ((Finset.Icc wmin wmax).card : ℝ) = (wmax : ℝ) - (wmin : ℝ) + 1 := by
          rw [Int.card_Icc]
          have hle : wmin ≤ wmax := W.min'_le _ (W.max'_mem hWne)
          have hnn : 0 ≤ wmax + 1 - wmin := by omega
          have hcast : (((wmax + 1 - wmin).toNat : ℤ) : ℝ) = ((wmax + 1 - wmin : ℤ) : ℝ) := by
            rw [Int.toNat_of_nonneg hnn]
          have h1 : (((wmax + 1 - wmin).toNat : ℕ) : ℝ) = (wmax : ℝ) - (wmin : ℝ) + 1 := by
            have := hcast; push_cast at this; linarith
          exact h1
        have hcardR : (W.card : ℝ) ≤ ((Finset.Icc wmin wmax).card : ℝ) := by exact_mod_cast hW_le
        linarith
      -- Bound each fiber S_w = {x ∈ S | mOf x r = w} by 1 + 2 / (u_r * G r)
      have hfib_card : ∀ w ∈ W,
          ((S.filter fun x => mOf x r = w).card : ℝ) ≤ 1 + 2 / (u_r * (G r : ℝ)) := by
        intro w hw
        let Sw := S.filter fun x => mOf x r = w
        have hSw_ne : Sw.Nonempty := by
          obtain ⟨x, hx, hxw⟩ := mem_image.mp hw
          exact ⟨x, mem_filter.mpr ⟨hx, hxw⟩⟩
        let xmin := Sw.min' hSw_ne
        let xmax := Sw.max' hSw_ne
        have hmin_mem := mem_filter.mp (Sw.min'_mem hSw_ne)
        have hmax_mem := mem_filter.mp (Sw.max'_mem hSw_ne)
        have hmin_ico := mem_Ico.mp (mem_filter.mp hmin_mem.1).1
        have hmax_ico := mem_Ico.mp (mem_filter.mp hmax_mem.1).1
        have hle_mm : xmin ≤ xmax := Sw.min'_le _ (Sw.max'_mem hSw_ne)
        have hd := (hβ_dist xmin xmax hmin_ico.1 hle_mm (by omega)).1
        have hr1' := hround xmin r
        have hr2' := hround xmax r
        rw [hmin_mem.2, congrFun (mem_filter.mp hmin_mem.1).2 r] at hr1'
        rw [hmax_mem.2, congrFun (mem_filter.mp hmax_mem.1).2 r] at hr2'
        have hdiff_lt : |β xmin r - β xmax r| < 1 / (G r : ℝ) := by
          have : (((a₀ r : ℕ) : ℝ) + 1) / (G r : ℝ) = ((a₀ r : ℕ) : ℝ) / (G r : ℝ) + 1 / (G r : ℝ) := by ring
          rw [abs_lt]; constructor <;> linarith
        have hspan : (xmax : ℝ) - (xmin : ℝ) ≤ 2 / (u_r * (G r : ℝ)) := by
          have h1 : ((xmax : ℝ) - (xmin : ℝ)) * (u_r / 2) ≤ 1 / (G r : ℝ) := hd.trans hdiff_lt.le
          rw [le_div_iff₀ (mul_pos hur_pos (hG_Rpos r))]
          have h2 := mul_le_mul_of_nonneg_right h1 (hG_Rpos r).le
          rw [one_div_mul_cancel (hG_Rpos r).ne'] at h2
          linarith
        have hSw_sub : Sw ⊆ Finset.Icc xmin xmax := fun x hx =>
          Finset.mem_Icc.mpr ⟨Sw.min'_le x hx, Sw.le_max' x hx⟩
        have hSw_le : Sw.card ≤ xmax + 1 - xmin := by
          exact (card_le_card hSw_sub).trans (by rw [Nat.card_Icc])
        have hSw_R : (Sw.card : ℝ) ≤ (xmax : ℝ) - (xmin : ℝ) + 1 := by
          have h1 : (Sw.card : ℝ) ≤ ((xmax + 1 - xmin : ℕ) : ℝ) := by exact_mod_cast hSw_le
          rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one] at h1
          linarith
        linarith
      -- Multiply W.card * fiber bound ≤ 12 * L / Y
      have hScard_prod : (S.card : ℝ) ≤ ((L : ℝ) * u_r + 2) * (1 + 2 / (u_r * (G r : ℝ))) := by
        have hpart : S.card = ∑ w ∈ W, (S.filter fun x => mOf x r = w).card :=
          Finset.card_eq_sum_card_fiberwise (fun x hx => mem_image_of_mem _ hx)
        have hpartR : (S.card : ℝ) = ∑ w ∈ W, ((S.filter fun x => mOf x r = w).card : ℝ) := by
          exact_mod_cast hpart
        rw [hpartR]
        calc ∑ w ∈ W, ((S.filter fun x => mOf x r = w).card : ℝ)
            ≤ ∑ _w ∈ W, (1 + 2 / (u_r * (G r : ℝ))) := sum_le_sum hfib_card
          _ = (W.card : ℝ) * (1 + 2 / (u_r * (G r : ℝ))) := by simp only [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ((L : ℝ) * u_r + 2) * (1 + 2 / (u_r * (G r : ℝ))) :=
              mul_le_mul_of_nonneg_right hW_card (by positivity)
      -- Bound each of the 4 expanded terms by multiples of L / Y!
      have hGr_ge : 8 * (k : ℝ) ^ 2 * (Y : ℝ) ^ 2 ≤ (G r : ℝ) := by
        have h1 : 8 * k ^ 2 * Y ^ 2 ≤ G r := by
          dsimp only [G]
          have hks : k ^ 2 ≤ s := by dsimp [s]; omega
          have hYpow : Y ^ 2 ≤ Y ^ (r.1 + 1) := Nat.pow_le_pow_right hY_pos (by omega)
          nlinarith
        exact_mod_cast h1
      have hT1 : (L : ℝ) * u_r ≤ (L : ℝ) / (Y : ℝ) := by
        have hM₀_ge_Y2 : (Y : ℝ) ^ (2 : ℕ) ≤ (M₀ : ℝ) := by exact_mod_cast (hY2_le_M.trans hM₀_lo)
        have h1 : (M₀ : ℝ) ^ (-(1 : ℝ) / 2) ≤ 1 / (Y : ℝ) := by
          have hsq : (Y : ℝ) ≤ (M₀ : ℝ) ^ ((1 : ℝ) / 2) := by
            have h2 := Real.rpow_le_rpow (by positivity) hM₀_ge_Y2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
            rw [← Real.rpow_natCast, ← Real.rpow_mul hY_Rpos.le] at h2
            simpa using h2
          rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring, Real.rpow_neg hM₀pos.le, inv_eq_one_div]
          exact one_div_le_one_div_of_le hY_Rpos hsq
        calc (L : ℝ) * u_r ≤ (L : ℝ) * (1 / (Y : ℝ)) :=
              mul_le_mul_of_nonneg_left (hur_hi.trans h1) hL_Rpos.le
          _ = (L : ℝ) / (Y : ℝ) := by ring
      have hT2 : (2 : ℝ) ≤ (L : ℝ) / (Y : ℝ) := by
        rw [le_div_iff₀ hY_Rpos]
        have : 2 * Y ≤ L := by omega
        exact_mod_cast this
      have hT3 : 2 * (L : ℝ) / (G r : ℝ) ≤ (L : ℝ) / (Y : ℝ) := by
        rw [div_le_div_iff₀ (hG_Rpos r) hY_Rpos]
        have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast hY_pos
        have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
        have hk2 : (16 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
        have hY2 : (Y : ℝ) ≤ (Y : ℝ) ^ 2 := by nlinarith
        have hGr2Y : 2 * (Y : ℝ) ≤ (G r : ℝ) := by nlinarith [hGr_ge, hk2, hY2]
        nlinarith [hL_Rpos]
      have hT4 : 4 / (u_r * (G r : ℝ)) ≤ 8 * ((L : ℝ) / (Y : ℝ)) := by
        -- u_r ≥ M₀^(-3/2) ≥ 1 / (8 * Y^3), G r ≥ 8 * k^2 * Y^2
        have hM₀_le_4Y2 : (M₀ : ℝ) ≤ 4 * (Y : ℝ) ^ (2 : ℕ) := by
          have h1 : M₀ ≤ 2 * (Y + 1) ^ 2 := by nlinarith
          have h2 : 2 * (Y + 1) ^ 2 ≤ 4 * Y ^ 2 := by nlinarith
          exact_mod_cast (h1.trans h2)
        have hM₀32 : (M₀ : ℝ) ^ ((3 : ℝ) / 2) ≤ 8 * (Y : ℝ) ^ (3 : ℕ) := by
          have h1 := Real.rpow_le_rpow hM₀pos.le hM₀_le_4Y2 (show (0 : ℝ) ≤ 3 / 2 by norm_num)
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast (Y : ℝ),
            ← Real.rpow_mul hY_Rpos.le] at h1
          have h432 : (4 : ℝ) ^ ((3 : ℝ) / 2) = 8 := by
            rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast,
              ← Real.rpow_mul (by norm_num)]
            norm_num
          have hexp : ((2 : ℕ) : ℝ) * (3 / 2) = ((3 : ℕ) : ℝ) := by norm_num
          rw [h432, hexp, Real.rpow_natCast] at h1
          exact h1
        have hur_ge : 1 / (8 * (Y : ℝ) ^ (3 : ℕ)) ≤ u_r := by
          refine le_trans ?_ hur_lo
          rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring, Real.rpow_neg hM₀pos.le, inv_eq_one_div]
          exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hM₀pos _) hM₀32
        have hprod_ge : (k : ℝ) ^ 2 / (Y : ℝ) ≤ u_r * (G r : ℝ) := by
          calc (k : ℝ) ^ 2 / (Y : ℝ) = (1 / (8 * (Y : ℝ) ^ (3 : ℕ))) * (8 * (k : ℝ) ^ 2 * (Y : ℝ) ^ 2) := by
                field_simp [hY_Rpos.ne']
            _ ≤ u_r * (G r : ℝ) := mul_le_mul hur_ge hGr_ge (by positivity) hur_pos.le
        have h4_le : 4 / (u_r * (G r : ℝ)) ≤ 4 * (Y : ℝ) / (k : ℝ) ^ 2 := by
          rw [show 4 * (Y : ℝ) / (k : ℝ) ^ 2 = 4 / ((k : ℝ) ^ 2 / (Y : ℝ)) by field_simp [hY_Rpos.ne', hkpos.ne']]
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hprod_ge
        have hL_ge_Y2 : (Y : ℝ) ^ 2 / (8 * (k : ℝ)) ≤ (L : ℝ) := by
          have h1 : Y ^ 2 ≤ (L + 1) * (4 * k) := by
            dsimp only [L]
            have hdm := Nat.div_add_mod M (4 * k)
            have hrem := Nat.mod_lt M (by omega : 0 < 4 * k)
            nlinarith
          have h2 : Y ^ 2 ≤ 8 * k * L := by nlinarith
          rw [div_le_iff₀ (by positivity)]
          have : (Y : ℝ) ^ 2 ≤ 8 * (k : ℝ) * (L : ℝ) := by exact_mod_cast h2
          linarith
        calc 4 / (u_r * (G r : ℝ)) ≤ 4 * (Y : ℝ) / (k : ℝ) ^ 2 := h4_le
          _ ≤ (Y : ℝ) / (k : ℝ) := by
              rw [div_le_div_iff₀ (by positivity) hkpos]
              have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
              have h4k : 4 * (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
              nlinarith [hY_Rpos]
          _ = 8 * (((Y : ℝ) ^ 2 / (8 * (k : ℝ))) / (Y : ℝ)) := by field_simp [hY_Rpos.ne', hkpos.ne']
          _ ≤ 8 * ((L : ℝ) / (Y : ℝ)) :=
              mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hL_ge_Y2 hY_Rpos.le) (by norm_num)
      have hexp : ((L : ℝ) * u_r + 2) * (1 + 2 / (u_r * (G r : ℝ))) =
          (L : ℝ) * u_r + 2 + 2 * (L : ℝ) / (G r : ℝ) + 4 / (u_r * (G r : ℝ)) := by
        field_simp [hur_pos.ne', (hG_Rpos r).ne']
        ring
      rw [hexp] at hScard_prod
      change (S.card : ℝ) ≤ 12 * (L : ℝ) / (Y : ℝ)
      have h12 : 12 * (L : ℝ) / (Y : ℝ) = 12 * ((L : ℝ) / (Y : ℝ)) := by ring
      linarith [hScard_prod, hT1, hT2, hT3, hT4, h12]
    · change (S.card : ℝ) ≤ 12 * (L : ℝ) / (Y : ℝ)
      rw [Finset.not_nonempty_iff_eq_empty.mp hSne, card_empty, Nat.cast_zero]
      positivity
  -- Step 6: Parseval bound for ∑_{a} ‖partialWeyl t a‖^{2s} ≤ (∏ G_j) * J(s, k, Y) for t ≤ Y
  have hparseval_t : ∀ t : ℕ, t ≤ Y →
      (∑ a : ∀ j : Fin k, Fin (G j), ‖partialWeyl t a‖ ^ (2 * s)) ≤
        (∏ j : Fin k, (G j : ℝ)) * (J s k Y : ℝ) := by
    intro t htY
    let A_t : Finset (Fin s → ℤ) :=
      (Finset.univ : Finset (Fin s → Fin t)).image fun x i => ((x i : ℕ) : ℤ)
    have hAt_inj : Function.Injective (fun (x : Fin s → Fin t) (i : Fin s) => ((x i : ℕ) : ℤ)) := by
      intro x y h; ext i; have := congrFun h i; dsimp only at this; exact_mod_cast this
    have hAt_fit : ∀ x ∈ A_t, ∀ y ∈ A_t, ∀ j : Fin k,
        |(∑ i : Fin s, (x i) ^ (j.1 + 1)) - (∑ i : Fin s, (y i) ^ (j.1 + 1))| < (G j : ℤ) := by
      intro x hx y hy j
      obtain ⟨x₀, _, rfl⟩ := mem_image.mp hx
      obtain ⟨y₀, _, rfl⟩ := mem_image.mp hy
      have hbd : ∀ z : Fin s → Fin t,
          |∑ i : Fin s, ((z i : ℕ) : ℤ) ^ (j.1 + 1)| ≤ (s : ℤ) * (Y : ℤ) ^ (j.1 + 1) := by
        intro z
        calc |∑ i : Fin s, ((z i : ℕ) : ℤ) ^ (j.1 + 1)|
            ≤ ∑ i : Fin s, |((z i : ℕ) : ℤ) ^ (j.1 + 1)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin s, (Y : ℤ) ^ (j.1 + 1) := sum_le_sum fun i _ => by
              rw [abs_of_nonneg (by positivity)]
              exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast (le_trans (z i).2.le htY)) _
          _ = (s : ℤ) * (Y : ℤ) ^ (j.1 + 1) := by simp
      have h2 := abs_sub (∑ i : Fin s, ((x₀ i : ℕ) : ℤ) ^ (j.1 + 1))
          (∑ i : Fin s, ((y₀ i : ℕ) : ℤ) ^ (j.1 + 1))
      have hG_cast : (G j : ℤ) = 8 * (s : ℤ) * (Y : ℤ) ^ (j.1 + 1) := by simp [G]
      have hpos : (0 : ℤ) < (s : ℤ) * (Y : ℤ) ^ (j.1 + 1) := by positivity
      linarith [hbd x₀, hbd y₀]
    have hpow_eq : ∀ a : ∀ j : Fin k, Fin (G j),
        ‖partialWeyl t a‖ ^ (2 * s) = ‖∑ x ∈ A_t, ∏ i : Fin s, weylChar k G a (x i)‖ ^ 2 := by
      intro a
      rw [Finset.sum_image (fun _ _ _ _ h => hAt_inj h)]
      have hprod : (∑ x : Fin s → Fin t, ∏ i : Fin s, weylChar k G a ((x i : ℕ) : ℤ)) =
          (partialWeyl t a) ^ s := by
        rw [← Fintype.prod_sum (fun (_ : Fin s) (u : Fin t) => weylChar k G a ((u : ℕ) : ℤ))]
        simp only [Finset.prod_const, card_univ, Fintype.card_fin]
        congr 1
        dsimp only [partialWeyl]
        exact Fin.sum_univ_eq_sum_range (fun u => weylChar k G a (u : ℤ)) t
      rw [hprod, norm_pow, ← pow_mul, mul_comm s 2]
    simp_rw [hpow_eq]
    rw [← parseval_tuples G hG_pos A_t hAt_fit]
    have hcard : (((A_t ×ˢ A_t).filter fun xy =>
        ∀ j : Fin k, ∑ i : Fin s, (xy.1 i) ^ (j.1 + 1) = ∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)).card) =
        J s k t := by
      let f : ((Fin s → Fin t) × (Fin s → Fin t)) → ((Fin s → ℤ) × (Fin s → ℤ)) :=
        fun uv => (fun i => ((uv.1 i : ℕ) : ℤ), fun i => ((uv.2 i : ℕ) : ℤ))
      have hf_inj : Function.Injective f := fun a b h =>
        Prod.ext (hAt_inj (congrArg Prod.fst h)) (hAt_inj (congrArg Prod.snd h))
      have himg : (((Finset.univ : Finset ((Fin s → Fin t) × (Fin s → Fin t))).filter fun uv =>
          ∀ j : Fin k, ∑ i : Fin s, ((uv.1 i : ℕ) : ℤ) ^ (j.1 + 1) =
            ∑ i : Fin s, ((uv.2 i : ℕ) : ℤ) ^ (j.1 + 1)).image f) =
          ((A_t ×ˢ A_t).filter fun xy =>
            ∀ j : Fin k, ∑ i : Fin s, (xy.1 i) ^ (j.1 + 1) = ∑ i : Fin s, (xy.2 i) ^ (j.1 + 1)) := by
        ext ⟨x, y⟩
        simp only [mem_image, mem_filter, mem_univ, true_and, mem_product, A_t]
        constructor
        · rintro ⟨uv, huv, hfeq⟩
          have hx : (fun i => ((uv.1 i : ℕ) : ℤ)) = x := congrArg Prod.fst hfeq
          have hy : (fun i => ((uv.2 i : ℕ) : ℤ)) = y := congrArg Prod.snd hfeq
          subst hx; subst hy
          exact ⟨⟨⟨uv.1, rfl⟩, ⟨uv.2, rfl⟩⟩, huv⟩
        · rintro ⟨⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩, h⟩
          exact ⟨(u, v), h, rfl⟩
      rw [J, ← card_image_of_injective _ hf_inj, himg]
    rw [hcard]
    refine mul_le_mul_of_nonneg_left (by exact_mod_cast J_mono htY) (prod_nonneg fun j _ => (hG_Rpos j).le)
  -- Step 7: Sum ‖polySum x‖^{2s} over x ∈ Ico M₀ (M₀ + L'), apply VMVT, and take 2s-th root!
  have hsum_2s : (∑ x ∈ Ico M₀ (M₀ + L'), ‖polySum x‖ ^ (2 * s)) ≤
      (2 : ℝ) ^ (2 * s + 1) * (12 * (L : ℝ) / (Y : ℝ)) *
        ((∏ j : Fin k, (G j : ℝ)) * (J s k Y : ℝ)) := by
    have hfib_sum : ∀ (t : ℕ), t ≤ Y →
        (∑ x ∈ Ico M₀ (M₀ + L'), ‖partialWeyl t (aOf x)‖ ^ (2 * s)) ≤
          (12 * (L : ℝ) / (Y : ℝ)) * ((∏ j : Fin k, (G j : ℝ)) * (J s k Y : ℝ)) := by
      intro t htY
      rw [← Finset.sum_fiberwise_of_maps_to (g := aOf) (t := Finset.univ) (fun _ _ => mem_univ _)]
      calc ∑ a : ∀ j : Fin k, Fin (G j), ∑ x ∈ (Ico M₀ (M₀ + L')).filter (fun x => aOf x = a),
              ‖partialWeyl t (aOf x)‖ ^ (2 * s)
          = ∑ a : ∀ j : Fin k, Fin (G j),
              (((Ico M₀ (M₀ + L')).filter (fun x => aOf x = a)).card : ℝ) * ‖partialWeyl t a‖ ^ (2 * s) := by
            refine sum_congr rfl fun a _ => ?_
            have hcongr : ∑ x ∈ (Ico M₀ (M₀ + L')).filter (fun x => aOf x = a), ‖partialWeyl t (aOf x)‖ ^ (2 * s) =
                ∑ _x ∈ (Ico M₀ (M₀ + L')).filter (fun x => aOf x = a), ‖partialWeyl t a‖ ^ (2 * s) :=
              sum_congr rfl fun x hx => by rw [(mem_filter.mp hx).2]
            rw [hcongr, Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ a : ∀ j : Fin k, Fin (G j), (12 * (L : ℝ) / (Y : ℝ)) * ‖partialWeyl t a‖ ^ (2 * s) :=
            sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hmult a) (by positivity)
        _ = (12 * (L : ℝ) / (Y : ℝ)) * ∑ a : ∀ j : Fin k, Fin (G j), ‖partialWeyl t a‖ ^ (2 * s) :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ (12 * (L : ℝ) / (Y : ℝ)) * ((∏ j : Fin k, (G j : ℝ)) * (J s k Y : ℝ)) :=
            mul_le_mul_of_nonneg_left (hparseval_t t htY) (by positivity)
    calc ∑ x ∈ Ico M₀ (M₀ + L'), ‖polySum x‖ ^ (2 * s)
        ≤ ∑ x ∈ Ico M₀ (M₀ + L'), (2 : ℝ) ^ (2 * s) * (‖partialWeyl Y (aOf x)‖ ^ (2 * s) +
            (1 / (Y : ℝ)) * ∑ t ∈ range Y, ‖partialWeyl (t + 1) (aOf x)‖ ^ (2 * s)) :=
          sum_le_sum fun x _ => hpoly_abel x
      _ = (2 : ℝ) ^ (2 * s) * ((∑ x ∈ Ico M₀ (M₀ + L'), ‖partialWeyl Y (aOf x)‖ ^ (2 * s)) +
            (1 / (Y : ℝ)) * ∑ t ∈ range Y, ∑ x ∈ Ico M₀ (M₀ + L'), ‖partialWeyl (t + 1) (aOf x)‖ ^ (2 * s)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
      _ ≤ (2 : ℝ) ^ (2 * s) * ((12 * (L : ℝ) / (Y : ℝ)) * ((∏ j : Fin k, (G j : ℝ)) * (J s k Y : ℝ)) +
            (1 / (Y : ℝ)) * ∑ _t ∈ range Y, (12 * (L : ℝ) / (Y : ℝ)) * ((∏ j : Fin k, (G j : ℝ)) * (J s k Y : ℝ))) := by
          refine mul_le_mul_of_nonneg_left (add_le_add (hfib_sum Y le_rfl) ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left (sum_le_sum fun t ht => hfib_sum (t + 1) (mem_range.mp ht)) (by positivity)
      _ = (2 : ℝ) ^ (2 * s + 1) * (12 * (L : ℝ) / (Y : ℝ)) * ((∏ j : Fin k, (G j : ℝ)) * (J s k Y : ℝ)) := by
          simp only [Finset.sum_const, card_range, nsmul_eq_mul]
          rw [pow_succ]
          field_simp [hY_Rpos.ne']
          ring
  -- Evaluate ∏ G_j * J(s, k, Y) via vinogradov_mvt
  have hprodG_J : (∏ j : Fin k, (G j : ℝ)) * (J s k Y : ℝ) ≤
      (8 * (s : ℝ)) ^ k * (4 * (s : ℝ)) ^ (4 * k ^ 2 * l + 8 * k ^ 3) *
        (Y : ℝ) ^ (2 * (s : ℝ) + δ) := by
    have hprodG : ∏ j : Fin k, (G j : ℝ) = (8 * (s : ℝ)) ^ k * (Y : ℝ) ^ (((k * (k + 1) : ℕ) : ℝ) / 2) := by
      have h1 : ∏ j : Fin k, (G j : ℝ) = (8 * (s : ℝ)) ^ k * (Y : ℝ) ^ (∑ j : Fin k, (j.1 + 1)) := by
        dsimp only [G]
        simp_rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [Finset.prod_mul_distrib, Finset.prod_const, card_univ, Fintype.card_fin,
          Finset.prod_pow_eq_pow_sum]
      rw [h1, ← Real.rpow_natCast (Y : ℝ)]
      congr 2
      have hsum_nat : 2 * ∑ j : Fin k, (j.1 + 1) = k * (k + 1) := by
        rw [Fin.sum_univ_eq_sum_range (fun i => i + 1) k]
        have haux : ∀ n : ℕ, 2 * ∑ i ∈ range n, (i + 1) = n * (n + 1) := fun n => by
          induction n with
          | zero => simp
          | succ m ih => rw [sum_range_succ, mul_add, ih]; ring
        exact haux k
      have hsum_R : 2 * ((∑ j : Fin k, (j.1 + 1) : ℕ) : ℝ) = ((k * (k + 1) : ℕ) : ℝ) := by
        exact_mod_cast hsum_nat
      linarith
    have hvmvt := vinogradov_mvt hk l Y hY_pos
    change (J s k Y : ℝ) ≤ (4 * (s : ℝ)) ^ (4 * k ^ 2 * l + 8 * k ^ 3) *
      (Y : ℝ) ^ (2 * (s : ℝ) - ((k * (k + 1) : ℕ) : ℝ) / 2 + δ) at hvmvt
    rw [hprodG]
    calc (8 * (s : ℝ)) ^ k * (Y : ℝ) ^ (((k * (k + 1) : ℕ) : ℝ) / 2) * (J s k Y : ℝ)
        ≤ (8 * (s : ℝ)) ^ k * (Y : ℝ) ^ (((k * (k + 1) : ℕ) : ℝ) / 2) *
          ((4 * (s : ℝ)) ^ (4 * k ^ 2 * l + 8 * k ^ 3) *
            (Y : ℝ) ^ (2 * (s : ℝ) - ((k * (k + 1) : ℕ) : ℝ) / 2 + δ)) :=
          mul_le_mul_of_nonneg_left hvmvt (by positivity)
      _ = (8 * (s : ℝ)) ^ k * (4 * (s : ℝ)) ^ (4 * k ^ 2 * l + 8 * k ^ 3) *
          ((Y : ℝ) ^ (((k * (k + 1) : ℕ) : ℝ) / 2) *
            (Y : ℝ) ^ (2 * (s : ℝ) - ((k * (k + 1) : ℕ) : ℝ) / 2 + δ)) := by ring
      _ = (8 * (s : ℝ)) ^ k * (4 * (s : ℝ)) ^ (4 * k ^ 2 * l + 8 * k ^ 3) *
          (Y : ℝ) ^ (2 * (s : ℝ) + δ) := by
          rw [← Real.rpow_add hY_Rpos]; congr 2; ring
  -- Hölder on ∑_{x ∈ Ico M₀ (M₀ + L')} ‖polySum x‖
  have hpoly_sum_le : (1 / (Y : ℝ)) * (∑ x ∈ Ico M₀ (M₀ + L'), ‖polySum x‖) ≤
      2 * (L : ℝ) * (4 * (s : ℝ)) ^ (5 * k) * (Y : ℝ) ^ ((-1 + δ) / (2 * (s : ℝ))) := by
    have h2s_ge1 : (1 : ℝ) ≤ (2 * s : ℕ) := by exact_mod_cast (by omega : 1 ≤ 2 * s)
    have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := Ico M₀ (M₀ + L'))
      (f := fun x => ‖polySum x‖) h2s_ge1 (fun _ _ => norm_nonneg _)
    have hsub : ((2 * s : ℕ) : ℝ) - 1 = ((2 * s - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hsub, Real.rpow_natCast, Real.rpow_natCast] at hholder
    simp_rw [Real.rpow_natCast] at hholder
    have hcard_le_L : ((Ico M₀ (M₀ + L')).card : ℝ) ≤ L := by
      rw [Nat.card_Ico, show M₀ + L' - M₀ = L' by omega]; exact_mod_cast hL'
    have hpow2s : (∑ x ∈ Ico M₀ (M₀ + L'), ‖polySum x‖) ^ (2 * s) ≤
        (2 * (L : ℝ) * (4 * (s : ℝ)) ^ (5 * k) * (Y : ℝ) * (Y : ℝ) ^ ((-1 + δ) / (2 * (s : ℝ)))) ^ (2 * s) := by
      have hconst_le : 24 * (8 * (s : ℝ)) ^ k * (4 * (s : ℝ)) ^ (4 * k ^ 2 * l + 8 * k ^ 3) ≤
          ((4 * (s : ℝ)) ^ (5 * k)) ^ (2 * s) := by
        have h4s_ge : (64 : ℝ) ≤ 4 * (s : ℝ) := by
          have : (16 : ℝ) ≤ s := by exact_mod_cast hs_ge16
          linarith
        have h24 : (24 : ℝ) ≤ (4 * (s : ℝ)) ^ 1 := by simp; linarith
        have h8s : (8 * (s : ℝ)) ^ k ≤ (4 * (s : ℝ)) ^ (2 * k) := by
          calc (8 * (s : ℝ)) ^ k ≤ ((4 * (s : ℝ)) ^ 2) ^ k :=
                pow_le_pow_left₀ (by positivity) (by nlinarith) k
            _ = (4 * (s : ℝ)) ^ (2 * k) := (pow_mul _ _ _).symm
        have hexp_le : 1 + 2 * k + (4 * k ^ 2 * l + 8 * k ^ 3) ≤ 5 * k * (2 * s) := by
          dsimp only [s]
          have hk2 : 2 * k ≤ k ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right k (by omega)
          have hk3 : k ^ 2 ≤ k ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
          have hk3_1 : 1 ≤ k ^ 3 := one_le_pow₀ (by omega)
          have h1 : 1 + 2 * k ≤ 2 * k ^ 3 := by omega
          have h2 : 4 * k ^ 2 * l ≤ 10 * k ^ 2 * l := Nat.mul_le_mul_right l (by omega)
          rw [show 5 * k * (2 * (k ^ 2 + k * l)) = 10 * k ^ 2 * l + 10 * k ^ 3 by ring]
          omega
        have hm1 : 24 * (8 * (s : ℝ)) ^ k ≤ (4 * (s : ℝ)) ^ 1 * (4 * (s : ℝ)) ^ (2 * k) :=
          mul_le_mul h24 h8s (by positivity) (by positivity)
        have hm2 : 24 * (8 * (s : ℝ)) ^ k * (4 * (s : ℝ)) ^ (4 * k ^ 2 * l + 8 * k ^ 3) ≤
            (4 * (s : ℝ)) ^ 1 * (4 * (s : ℝ)) ^ (2 * k) * (4 * (s : ℝ)) ^ (4 * k ^ 2 * l + 8 * k ^ 3) :=
          mul_le_mul_of_nonneg_right hm1 (by positivity)
        calc 24 * (8 * (s : ℝ)) ^ k * (4 * (s : ℝ)) ^ (4 * k ^ 2 * l + 8 * k ^ 3)
            ≤ (4 * (s : ℝ)) ^ 1 * (4 * (s : ℝ)) ^ (2 * k) * (4 * (s : ℝ)) ^ (4 * k ^ 2 * l + 8 * k ^ 3) := hm2
          _ = (4 * (s : ℝ)) ^ (1 + 2 * k + (4 * k ^ 2 * l + 8 * k ^ 3)) := by simp only [pow_add]
          _ ≤ (4 * (s : ℝ)) ^ (5 * k * (2 * s)) := pow_le_pow_right₀ (by linarith) hexp_le
          _ = ((4 * (s : ℝ)) ^ (5 * k)) ^ (2 * s) := pow_mul _ _ _
      have hY_comb : (Y : ℝ) ^ (2 * (s : ℝ) + δ) / (Y : ℝ) =
          ((Y : ℝ) * (Y : ℝ) ^ ((-1 + δ) / (2 * (s : ℝ)))) ^ (2 * s) := by
        rw [mul_pow, ← Real.rpow_natCast (Y : ℝ), ← Real.rpow_natCast ((Y : ℝ) ^ _),
          ← Real.rpow_mul hY_Rpos.le, ← Real.rpow_add hY_Rpos]
        calc (Y : ℝ) ^ (2 * (s : ℝ) + δ) / (Y : ℝ)
            = (Y : ℝ) ^ (2 * (s : ℝ) + δ) / (Y : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = (Y : ℝ) ^ (2 * (s : ℝ) + δ - 1) := (Real.rpow_sub hY_Rpos _ _).symm
          _ = (Y : ℝ) ^ (((2 * s : ℕ) : ℝ) + (-1 + δ) / (2 * (s : ℝ)) * ((2 * s : ℕ) : ℝ)) := by
              congr 1; push_cast; field_simp [hspos.ne']; ring
      have hL_pow : (L : ℝ) ^ (2 * s - 1) * (L : ℝ) = (L : ℝ) ^ (2 * s) := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      calc (∑ x ∈ Ico M₀ (M₀ + L'), ‖polySum x‖) ^ (2 * s)
          ≤ ((Ico M₀ (M₀ + L')).card : ℝ) ^ (2 * s - 1) *
              ∑ x ∈ Ico M₀ (M₀ + L'), ‖polySum x‖ ^ (2 * s) := hholder
        _ ≤ (L : ℝ) ^ (2 * s - 1) *
              ((2 : ℝ) ^ (2 * s + 1) * (12 * (L : ℝ) / (Y : ℝ)) *
                ((8 * (s : ℝ)) ^ k * (4 * (s : ℝ)) ^ (4 * k ^ 2 * l + 8 * k ^ 3) *
                  (Y : ℝ) ^ (2 * (s : ℝ) + δ))) := by
            refine mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard_le_L _)
              (hsum_2s.trans (mul_le_mul_of_nonneg_left hprodG_J (by positivity)))
              (sum_nonneg fun _ _ => by positivity) (by positivity)
        _ = (2 : ℝ) ^ (2 * s) * ((L : ℝ) ^ (2 * s - 1) * (L : ℝ)) *
              (24 * (8 * (s : ℝ)) ^ k * (4 * (s : ℝ)) ^ (4 * k ^ 2 * l + 8 * k ^ 3)) *
              ((Y : ℝ) ^ (2 * (s : ℝ) + δ) / (Y : ℝ)) := by
            rw [pow_succ]; ring
        _ ≤ (2 : ℝ) ^ (2 * s) * (L : ℝ) ^ (2 * s) *
              ((4 * (s : ℝ)) ^ (5 * k)) ^ (2 * s) *
              ((Y : ℝ) * (Y : ℝ) ^ ((-1 + δ) / (2 * (s : ℝ)))) ^ (2 * s) := by
            rw [hL_pow, hY_comb]
            gcongr
        _ = (2 * (L : ℝ) * (4 * (s : ℝ)) ^ (5 * k) * (Y : ℝ) *
              (Y : ℝ) ^ ((-1 + δ) / (2 * (s : ℝ)))) ^ (2 * s) := by
            simp only [mul_pow]; ring
    have hroot : ∑ x ∈ Ico M₀ (M₀ + L'), ‖polySum x‖ ≤
        2 * (L : ℝ) * (4 * (s : ℝ)) ^ (5 * k) * (Y : ℝ) * (Y : ℝ) ^ ((-1 + δ) / (2 * (s : ℝ))) := by
      have h1 := Real.rpow_le_rpow (pow_nonneg (sum_nonneg fun _ _ => norm_nonneg _) _) hpow2s
        (show (0 : ℝ) ≤ 1 / (2 * (s : ℝ)) by positivity)
      rw [← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_mul (sum_nonneg fun _ _ => norm_nonneg _),
        ← Real.rpow_mul (by positivity)] at h1
      have hinv : ((2 * s : ℕ) : ℝ) * (1 / (2 * (s : ℝ))) = 1 := by
        push_cast; field_simp [hspos.ne']
      rw [hinv, Real.rpow_one, Real.rpow_one] at h1
      exact h1
    calc (1 / (Y : ℝ)) * (∑ x ∈ Ico M₀ (M₀ + L'), ‖polySum x‖)
        ≤ (1 / (Y : ℝ)) * (2 * (L : ℝ) * (4 * (s : ℝ)) ^ (5 * k) * (Y : ℝ) *
            (Y : ℝ) ^ ((-1 + δ) / (2 * (s : ℝ)))) :=
          mul_le_mul_of_nonneg_left hroot (by positivity)
      _ = 2 * (L : ℝ) * (4 * (s : ℝ)) ^ (5 * k) * (Y : ℝ) ^ ((-1 + δ) / (2 * (s : ℝ))) := by
          field_simp [hY_Rpos.ne']
  -- Combine Steps 1, 2, and 7!
  have hcard_le_L : ((Ico M₀ (M₀ + L')).card : ℝ) ≤ L := by
    rw [Nat.card_Ico, show M₀ + L' - M₀ = L' by omega]; exact_mod_cast hL'
  calc ‖∑ x ∈ Ico M₀ (M₀ + L'), e (α / (x : ℝ))‖
      ≤ (1 / (Y : ℝ)) * (∑ x ∈ Ico M₀ (M₀ + L'), ‖∑ y ∈ range Y, e (α / ((x + y : ℕ) : ℝ))‖) +
          2 * (Y : ℝ) := havg
    _ ≤ (1 / (Y : ℝ)) * (∑ x ∈ Ico M₀ (M₀ + L'), (‖polySum x‖ + 1)) + 2 * (Y : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left (sum_le_sum hpoly_approx) (by positivity)) le_rfl
    _ = (1 / (Y : ℝ)) * (∑ x ∈ Ico M₀ (M₀ + L'), ‖polySum x‖) +
          ((Ico M₀ (M₀ + L')).card : ℝ) / (Y : ℝ) + 2 * (Y : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]; ring
    _ ≤ 2 * (L : ℝ) * (4 * (s : ℝ)) ^ (5 * k) * (Y : ℝ) ^ ((-1 + δ) / (2 * (s : ℝ))) +
          (L : ℝ) / (Y : ℝ) + 2 * (Y : ℝ) := by
        have h1 : ((Ico M₀ (M₀ + L')).card : ℝ) / (Y : ℝ) ≤ (L : ℝ) / (Y : ℝ) :=
          div_le_div_of_nonneg_right hcard_le_L hY_Rpos.le
        linarith [hpoly_sum_le]
    _ ≤ 2 * (L : ℝ) * ((4 * (s : ℝ)) ^ (5 * k) * (Y : ℝ) ^ ((-1 + δ) / (2 * (s : ℝ))) + 1 / (Y : ℝ)) +
          2 * (Y : ℝ) := by
        have h1 : 2 * (L : ℝ) * (1 / (Y : ℝ)) = 2 * ((L : ℝ) / (Y : ℝ)) := by ring
        have h2 : 0 ≤ (L : ℝ) / (Y : ℝ) := by positivity
        linarith

/-- Main Vinogradov-Korobov reciprocal exponential sum bound on `(M, N]` (`M ≤ N ≤ 2 * M`). -/
theorem vinogradov_reciprocal_sum
    {M N k l : ℕ} {α : ℝ}
    (hMN : M ≤ N) (hN2M : N ≤ 2 * M)
    (hM : 100 ≤ M) (hk : 4 ≤ k) (hl : 1 ≤ l)
    (hα_lo : (M : ℝ) ^ (3 : ℕ) ≤ α)
    (hα_hi : α ≤ (M : ℝ) ^ ((k : ℝ) / 2))
    (hkY : 16 * k ≤ Nat.sqrt M) :
    let s := k ^ 2 + k * l
    let Y := Nat.sqrt M
    let δ : ℝ := ((k * (k + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (k : ℝ)) ^ l
    ‖∑ x ∈ Ioc M N, e (α / (x : ℝ))‖ ≤
      4 * (M : ℝ) * ((4 * (s : ℝ)) ^ (5 * k) * (Y : ℝ) ^ ((-1 + δ) / (2 * (s : ℝ))) + 1 / (Y : ℝ)) +
      10 * (k : ℝ) * (Y : ℝ) := by
  intro s Y δ
  let L := M / (4 * k)
  let B := 4 * k + 1
  have hY2 : Y ^ 2 ≤ M := by simpa [sq] using Nat.sqrt_le M
  have hL_ge : 4 * k ≤ L := by
    dsimp only [L]
    have h1 : 4 * k * (4 * k) ≤ Y ^ 2 := by nlinarith
    exact (Nat.le_div_iff_mul_le (by omega : 0 < 4 * k)).mpr (h1.trans hY2)
  have hBL_ge : N - M ≤ B * L := by
    have hdm := Nat.div_add_mod M (4 * k)
    have hrem := Nat.mod_lt M (by omega : 0 < 4 * k)
    have hNM : N - M ≤ M := by omega
    dsimp only [B, L] at hL_ge ⊢
    rw [add_mul, one_mul]
    nlinarith
  -- Partition Ioc M N = Ico (M + 1) (N + 1) into B blocks of length ≤ L
  let blk (b : ℕ) : Finset ℕ :=
    Ico (min (N + 1) (M + 1 + b * L)) (min (N + 1) (M + 1 + (b + 1) * L))
  have hpart : Ioc M N = (range B).biUnion blk := by
    ext x
    simp only [mem_Ioc, mem_biUnion, mem_range, blk, mem_Ico]
    constructor
    · intro ⟨hx1, hx2⟩
      have hLpos : 0 < L := by omega
      let b := (x - (M + 1)) / L
      have hb_lt : b < B := by
        dsimp only [b]
        exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; omega)
      refine ⟨b, hb_lt, ?_, ?_⟩
      · have h1 : b * L ≤ x - (M + 1) := Nat.div_mul_le_self (x - (M + 1)) L
        omega
      · have hdm := Nat.div_add_mod (x - (M + 1)) L
        have hrem := Nat.mod_lt (x - (M + 1)) hLpos
        have h1 : x - (M + 1) < (b + 1) * L := by
          dsimp only [b]; rw [add_mul, one_mul, mul_comm L] at *; omega
        omega
    · rintro ⟨b, _, h1, h2⟩
      omega
  have hdisj : Set.PairwiseDisjoint (range B : Set ℕ) blk := by
    intro b₁ _ b₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx1 hx2
    simp only [blk, mem_Ico] at hx1 hx2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (b₁ + 1) * L ≤ b₂ * L := Nat.mul_le_mul_right L (by omega)
      omega
    · have : (b₂ + 1) * L ≤ b₁ * L := Nat.mul_le_mul_right L (by omega)
      omega
  rw [hpart, Finset.sum_biUnion hdisj]
  let E : ℝ := (4 * (s : ℝ)) ^ (5 * k) * (Y : ℝ) ^ ((-1 + δ) / (2 * (s : ℝ))) + 1 / (Y : ℝ)
  have hE_nn : 0 ≤ E := by
    dsimp only [E]
    have hY_pos : 0 < Y := by have : 10 ≤ Y := Nat.le_sqrt.mpr (by omega); omega
    have hs_pos : 0 < s := by dsimp [s]; nlinarith
    positivity
  have hblk_bd : ∀ b ∈ range B,
      ‖∑ x ∈ blk b, e (α / (x : ℝ))‖ ≤ 2 * (L : ℝ) * E + 2 * (Y : ℝ) := by
    intro b _
    dsimp only [blk]
    let M₀ := min (N + 1) (M + 1 + b * L)
    let M₁ := min (N + 1) (M + 1 + (b + 1) * L)
    change ‖∑ x ∈ Ico M₀ M₁, e (α / (x : ℝ))‖ ≤ 2 * (L : ℝ) * E + 2 * (Y : ℝ)
    by_cases hemp : M₁ ≤ M₀
    · rw [Finset.Ico_eq_empty_of_le hemp, Finset.sum_empty, norm_zero]
      positivity
    · push Not at hemp
      have hM₀_lo : M ≤ M₀ := by dsimp [M₀]; omega
      have hM₀_hi : M₀ ≤ 2 * M := by dsimp [M₀]; omega
      have hlen : M₁ - M₀ ≤ L := by
        dsimp only [M₀, M₁]
        have : M + 1 + (b + 1) * L = M + 1 + b * L + L := by ring
        omega
      have hM₁_eq : M₁ = M₀ + (M₁ - M₀) := by omega
      rw [hM₁_eq]
      exact block_recip_sum_bound hM hM₀_lo hM₀_hi hlen hk hl hα_lo hα_hi hkY
  have hsum_bd : ‖∑ b ∈ range B, ∑ x ∈ blk b, e (α / (x : ℝ))‖ ≤
      (B : ℝ) * (2 * (L : ℝ) * E + 2 * (Y : ℝ)) := by
    calc ‖∑ b ∈ range B, ∑ x ∈ blk b, e (α / (x : ℝ))‖
        ≤ ∑ b ∈ range B, ‖∑ x ∈ blk b, e (α / (x : ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ _b ∈ range B, (2 * (L : ℝ) * E + 2 * (Y : ℝ)) := sum_le_sum hblk_bd
      _ = (B : ℝ) * (2 * (L : ℝ) * E + 2 * (Y : ℝ)) := by
          simp only [Finset.sum_const, card_range, nsmul_eq_mul]
  have hBL_le : (B : ℝ) * (2 * (L : ℝ)) ≤ 4 * (M : ℝ) := by
    have h1 : 4 * k * L ≤ M := by
      dsimp only [L]; rw [mul_comm]; exact Nat.div_mul_le_self M (4 * k)
    have h2 : L ≤ M := Nat.div_le_self M (4 * k)
    have h3 : B * (2 * L) ≤ 4 * M := by dsimp only [B]; nlinarith
    have h4 : ((B * (2 * L) : ℕ) : ℝ) ≤ ((4 * M : ℕ) : ℝ) := by exact_mod_cast h3
    push_cast at h4; exact h4
  have hBY_le : (B : ℝ) * (2 * (Y : ℝ)) ≤ 10 * (k : ℝ) * (Y : ℝ) := by
    have h1 : B * 2 ≤ 10 * k := by dsimp only [B]; omega
    have h2 : (B : ℝ) * 2 ≤ 10 * (k : ℝ) := by exact_mod_cast h1
    nlinarith [Nat.cast_nonneg (α := ℝ) Y]
  calc ‖∑ b ∈ range B, ∑ x ∈ blk b, e (α / (x : ℝ))‖
      ≤ (B : ℝ) * (2 * (L : ℝ) * E + 2 * (Y : ℝ)) := hsum_bd
    _ = ((B : ℝ) * (2 * (L : ℝ))) * E + (B : ℝ) * (2 * (Y : ℝ)) := by ring
    _ ≤ 4 * (M : ℝ) * E + 10 * (k : ℝ) * (Y : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_right hBL_le hE_nn) hBY_le

end

end OMA.Erdos377M3


/-
Vaughan's identity + Vinogradov-Korobov reciprocal sum bound (`M3_RecipSum`) + Chebyshev's
upper bound (`Chebyshev.theta_le_log4_mul_x`), proving `OMA.R_Erdos377_erdos_377_variants_ub_R1.H2`.
-/

namespace OMA.Erdos377M4

open Finset Real Complex Filter ArithmeticFunction Chebyshev OMA.Erdos377M2 OMA.Erdos377M3
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

/- ### Part 1: Elementary divisor-squared and Abel summation bounds -/

/-- Möbius function is bounded by 1 in absolute value. -/
private lemma abs_moebius_le_one (d : ℕ) : |(μ d : ℝ)| ≤ 1 := by
  by_cases hs : Squarefree d
  · rw [ArithmeticFunction.moebius_apply_of_squarefree hs]
    push_cast
    rw [abs_pow, abs_neg, abs_one, one_pow]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
    simp

/-- Reindexing `∑ d ∈ k.divisors, f (k / d) = ∑ d ∈ k.divisors, f d`. -/
private lemma sum_divisors_div_eq (k : ℕ) (f : ℕ → ℝ) :
    ∑ d ∈ k.divisors, f (k / d) = ∑ d ∈ k.divisors, f d := by
  by_cases hk : k = 0
  · subst hk; simp
  · refine Finset.sum_bij (fun d _ => k / d) ?_ ?_ ?_ ?_
    · intro d hd
      exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hd).1, hk⟩
    · intro d₁ hd₁ d₂ hd₂ heq
      have h1 := Nat.div_mul_cancel (Nat.mem_divisors.mp hd₁).1
      have h2 := Nat.div_mul_cancel (Nat.mem_divisors.mp hd₂).1
      have hpos : 0 < k / d₁ := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) (Nat.mem_divisors.mp hd₁).1)
        (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd₁).1 (Nat.pos_of_ne_zero hk))
      rw [heq] at h1 hpos
      exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
    · intro d hd
      refine ⟨k / d, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hd).1, hk⟩, ?_⟩
      exact Nat.div_div_self (Nat.mem_divisors.mp hd).1 hk
    · intro _ _; rfl

/-- Subadditivity of nonnegative sums over finite `biUnion`. -/
private lemma sum_biUnion_le_sum {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (t : ι → Finset α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hunion : ∑ x ∈ t a ∪ s.biUnion t, f x ≤ ∑ x ∈ t a, f x + ∑ x ∈ s.biUnion t, f x := by
      have h := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
      linarith [sum_nonneg (s := t a ∩ s.biUnion t) fun x _ => hf x]
    linarith

/-- Multiplicative sub-additivity of divisor count: `τ(a * b) ≤ τ(a) * τ(b)`. -/
private lemma divisors_mul_card_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (a * b).divisors.card ≤ a.divisors.card * b.divisors.card := by
  have hsub : (a * b).divisors ⊆ (a.divisors ×ˢ b.divisors).image (fun p => p.1 * p.2) := by
    intro d hd
    have hd_dvd : d ∣ a * b := (Nat.mem_divisors.mp hd).1
    let g := Nat.gcd d a
    have hg_dvd_d : g ∣ d := Nat.gcd_dvd_left d a
    have hg_dvd_a : g ∣ a := Nat.gcd_dvd_right d a
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right d (by omega)
    have hcop : Nat.Coprime (d / g) (a / g) := Nat.coprime_div_gcd_div_gcd hg_pos
    have hdvd_mul : (d / g) ∣ (a / g) * b := by
      have h1 : g * (d / g) ∣ g * ((a / g) * b) := by
        rw [Nat.mul_div_cancel' hg_dvd_d, ← mul_assoc, Nat.mul_div_cancel' hg_dvd_a]
        exact hd_dvd
      exact (mul_dvd_mul_iff_left hg_pos.ne').mp h1
    have hdg_dvd_b : (d / g) ∣ b := hcop.dvd_of_dvd_mul_left hdvd_mul
    refine mem_image.mpr ⟨(g, d / g), mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hg_dvd_a, by omega⟩,
      Nat.mem_divisors.mpr ⟨hdg_dvd_b, by omega⟩⟩, ?_⟩
    exact Nat.mul_div_cancel' hg_dvd_d
  calc (a * b).divisors.card ≤ ((a.divisors ×ˢ b.divisors).image (fun p => p.1 * p.2)).card :=
        card_le_card hsub
    _ ≤ (a.divisors ×ˢ b.divisors).card := card_image_le
    _ = a.divisors.card * b.divisors.card := card_product _ _

/-- Harmonic sum bound: `∑_{k=1}^M 1/k ≤ 1 + log M` for `M ≥ 1`. -/
private lemma sum_inv_le_one_add_log {M : ℕ} (hM : 1 ≤ M) :
    ∑ k ∈ Icc 1 M, (1 : ℝ) / (k : ℝ) ≤ 1 + Real.log (M : ℝ) := by
  induction M with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hIcc : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
        ext x; simp only [mem_Icc, mem_insert]; omega
      rw [hIcc, sum_insert (by simp)]
      have hstep : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
        have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
        have hm1pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m + 1)
        have hlog := Real.log_le_sub_one_of_pos (div_pos hmpos hm1pos)
        rw [Real.log_div hmpos.ne' hm1pos.ne'] at hlog
        have hsub : (m : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 = -(1 / ((m + 1 : ℕ) : ℝ)) := by
          push_cast; field_simp [hm1pos.ne']; ring
        linarith
      linarith [ih hm]

/-- Divisor sum bound: `∑_{m=1}^M τ(m) ≤ M * (1 + log M)`. -/
private lemma sum_tau_le {M : ℕ} (hM : 1 ≤ M) :
    ∑ m ∈ Icc 1 M, (m.divisors.card : ℝ) ≤ (M : ℝ) * (1 + Real.log (M : ℝ)) := by
  have hswap : ∑ m ∈ Icc 1 M, (m.divisors.card : ℝ) =
      ∑ d ∈ Icc 1 M, (((Icc 1 M).filter fun m => d ∣ m).card : ℝ) := by
    have hnat : ∑ m ∈ Icc 1 M, m.divisors.card =
        ∑ d ∈ Icc 1 M, ((Icc 1 M).filter fun m => d ∣ m).card := by
      simp_rw [Finset.card_eq_sum_ones]
      calc ∑ m ∈ Icc 1 M, ∑ _d ∈ m.divisors, (1 : ℕ)
          = ∑ m ∈ Icc 1 M, ∑ d ∈ Icc 1 M, if d ∣ m then 1 else 0 := by
            refine sum_congr rfl fun m hm => ?_
            rw [← Finset.sum_filter]
            congr 1; ext d; simp only [Nat.mem_divisors, mem_filter, mem_Icc]
            have hm1 := (mem_Icc.mp hm).1
            have hm2 := (mem_Icc.mp hm).2
            constructor
            · rintro ⟨hd, _⟩
              exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), le_trans (Nat.le_of_dvd (by omega) hd) hm2⟩, hd⟩
            · rintro ⟨_, hd⟩; exact ⟨hd, by omega⟩
        _ = ∑ d ∈ Icc 1 M, ∑ m ∈ Icc 1 M, if d ∣ m then 1 else 0 := Finset.sum_comm
        _ = ∑ d ∈ Icc 1 M, ∑ _m ∈ (Icc 1 M).filter (fun m => d ∣ m), 1 :=
            sum_congr rfl fun _ _ => (Finset.sum_filter _ _).symm
    exact_mod_cast hnat
  rw [hswap]
  have hmult_le : ∀ d ∈ Icc 1 M, (((Icc 1 M).filter fun m => d ∣ m).card : ℝ) ≤ (M : ℝ) / (d : ℝ) := by
    intro d hd
    have hd1 := (mem_Icc.mp hd).1
    have hsub : ((Icc 1 M).filter fun m => d ∣ m) ⊆ (Icc 1 (M / d)).image (fun q => d * q) := by
      intro m hm
      obtain ⟨hm_icc, hdm⟩ := mem_filter.mp hm
      obtain ⟨q, rfl⟩ := hdm
      have hq1 : 1 ≤ q := by
        rcases Nat.eq_zero_or_pos q with rfl | hq
        · simp at hm_icc
        · exact hq
      have hq2 : q ≤ M / d := (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact (mem_Icc.mp hm_icc).2)
      exact mem_image.mpr ⟨q, mem_Icc.mpr ⟨hq1, hq2⟩, rfl⟩
    have hcard : ((Icc 1 M).filter fun m => d ∣ m).card ≤ M / d := by
      calc _ ≤ ((Icc 1 (M / d)).image (fun q => d * q)).card := card_le_card hsub
        _ ≤ (Icc 1 (M / d)).card := card_image_le
        _ = M / d := by simp
    have hdiv : ((M / d : ℕ) : ℝ) ≤ (M : ℝ) / (d : ℝ) := by
      have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      rw [le_div_iff₀ hdpos]
      exact_mod_cast Nat.div_mul_le_self M d
    exact (by exact_mod_cast hcard : (((Icc 1 M).filter fun m => d ∣ m).card : ℝ) ≤ (M / d : ℕ)).trans hdiv
  calc ∑ d ∈ Icc 1 M, (((Icc 1 M).filter fun m => d ∣ m).card : ℝ)
      ≤ ∑ d ∈ Icc 1 M, (M : ℝ) / (d : ℝ) := sum_le_sum hmult_le
    _ = (M : ℝ) * ∑ d ∈ Icc 1 M, (1 : ℝ) / (d : ℝ) := by
        rw [Finset.mul_sum]; refine sum_congr rfl fun _ _ => by ring
    _ ≤ (M : ℝ) * (1 + Real.log (M : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_inv_le_one_add_log hM) (Nat.cast_nonneg _)

/-- Reciprocal divisor sum bound: `∑_{m=1}^M τ(m) / m ≤ (1 + log M)^2`. -/
private lemma sum_tau_div_le {M : ℕ} (hM : 1 ≤ M) :
    ∑ m ∈ Icc 1 M, (m.divisors.card : ℝ) / (m : ℝ) ≤ (1 + Real.log (M : ℝ)) ^ 2 := by
  have h1 : ∑ m ∈ Icc 1 M, (m.divisors.card : ℝ) / (m : ℝ) =
      ∑ m ∈ Icc 1 M, ∑ d ∈ Icc 1 M, if d ∣ m then (1 : ℝ) / (m : ℝ) else 0 := by
    refine sum_congr rfl fun m hm => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hfilt : (Icc 1 M).filter (fun d => d ∣ m) = m.divisors := by
      ext d; simp only [mem_filter, mem_Icc, Nat.mem_divisors]
      have hm1 := (mem_Icc.mp hm).1; have hm2 := (mem_Icc.mp hm).2
      exact ⟨fun ⟨_, hd⟩ => ⟨hd, by omega⟩,
        fun ⟨hd, _⟩ => ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), le_trans (Nat.le_of_dvd (by omega) hd) hm2⟩, hd⟩⟩
    rw [hfilt]; ring
  rw [h1, Finset.sum_comm]
  have hinner : ∀ d ∈ Icc 1 M,
      (∑ m ∈ Icc 1 M, if d ∣ m then (1 : ℝ) / (m : ℝ) else 0) ≤
        ((1 : ℝ) / (d : ℝ)) * (∑ q ∈ Icc 1 M, (1 : ℝ) / (q : ℝ)) := by
    intro d hd
    have hd1 := (mem_Icc.mp hd).1
    rw [← Finset.sum_filter]
    have hbij : ∑ m ∈ (Icc 1 M).filter (fun m => d ∣ m), (1 : ℝ) / (m : ℝ) =
        ∑ q ∈ Icc 1 (M / d), (1 : ℝ) / ((d * q : ℕ) : ℝ) := by
      refine Finset.sum_bij (fun m _ => m / d) ?_ ?_ ?_ ?_
      · intro m hm
        obtain ⟨hm_icc, hdm⟩ := mem_filter.mp hm
        have hm1 := (mem_Icc.mp hm_icc).1; have hm2 := (mem_Icc.mp hm_icc).2
        refine mem_Icc.mpr ⟨?_, Nat.div_le_div_right hm2⟩
        have := Nat.le_of_dvd (by omega) hdm
        exact Nat.div_pos this (by omega)
      · intro m₁ hm₁ m₂ hm₂ heq
        have h1 := Nat.mul_div_cancel' (mem_filter.mp hm₁).2
        have h2 := Nat.mul_div_cancel' (mem_filter.mp hm₂).2
        rw [← h1, ← h2, heq]
      · intro q hq
        have hq1 := (mem_Icc.mp hq).1; have hq2 := (mem_Icc.mp hq).2
        have hdq : d * q ≤ M := by
          have := (Nat.le_div_iff_mul_le (by omega)).mp hq2; linarith
        refine ⟨d * q, mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith, hdq⟩, dvd_mul_right d q⟩,
          Nat.mul_div_cancel_left q (by omega)⟩
      · intro m hm
        rw [Nat.mul_div_cancel' (mem_filter.mp hm).2]
    rw [hbij]
    have hpull : ∑ q ∈ Icc 1 (M / d), (1 : ℝ) / ((d * q : ℕ) : ℝ) =
        ((1 : ℝ) / (d : ℝ)) * ∑ q ∈ Icc 1 (M / d), (1 : ℝ) / (q : ℝ) := by
      rw [Finset.mul_sum]; refine sum_congr rfl fun q _ => by push_cast; ring
    rw [hpull]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.div_le_self M d))
      (fun _ _ _ => by positivity)
  calc ∑ d ∈ Icc 1 M, ∑ m ∈ Icc 1 M, (if d ∣ m then (1 : ℝ) / (m : ℝ) else 0)
      ≤ ∑ d ∈ Icc 1 M, ((1 : ℝ) / (d : ℝ)) * (∑ q ∈ Icc 1 M, (1 : ℝ) / (q : ℝ)) := sum_le_sum hinner
    _ = (∑ d ∈ Icc 1 M, (1 : ℝ) / (d : ℝ)) ^ 2 := by rw [← Finset.sum_mul, sq]
    _ ≤ (1 + Real.log (M : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (sum_nonneg fun _ _ => by positivity) (sum_inv_le_one_add_log hM) 2

/-- Divisor-squared sum bound: `∑_{m=1}^M τ(m)^2 ≤ M * (1 + log M)^3`. -/
private lemma sum_tau_sq_le {M : ℕ} (hM : 1 ≤ M) :
    ∑ m ∈ Icc 1 M, (m.divisors.card : ℝ) ^ 2 ≤ (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 3 := by
  have hlog_nn : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  have h1 : ∑ m ∈ Icc 1 M, (m.divisors.card : ℝ) ^ 2 =
      ∑ m ∈ Icc 1 M, ∑ d ∈ Icc 1 M, if d ∣ m then (m.divisors.card : ℝ) else 0 := by
    refine sum_congr rfl fun m hm => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, sq]
    have hfilt : (Icc 1 M).filter (fun d => d ∣ m) = m.divisors := by
      ext d; simp only [mem_filter, mem_Icc, Nat.mem_divisors]
      have hm1 := (mem_Icc.mp hm).1; have hm2 := (mem_Icc.mp hm).2
      exact ⟨fun ⟨_, hd⟩ => ⟨hd, by omega⟩,
        fun ⟨hd, _⟩ => ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), le_trans (Nat.le_of_dvd (by omega) hd) hm2⟩, hd⟩⟩
    rw [hfilt]
  rw [h1, Finset.sum_comm]
  have hinner : ∀ d ∈ Icc 1 M,
      (∑ m ∈ Icc 1 M, if d ∣ m then (m.divisors.card : ℝ) else 0) ≤
        ((M : ℝ) * (1 + Real.log (M : ℝ))) * ((d.divisors.card : ℝ) / (d : ℝ)) := by
    intro d hd
    have hd1 := (mem_Icc.mp hd).1
    have hd2 := (mem_Icc.mp hd).2
    rw [← Finset.sum_filter]
    have hbij : ∑ m ∈ (Icc 1 M).filter (fun m => d ∣ m), (m.divisors.card : ℝ) =
        ∑ q ∈ Icc 1 (M / d), ((d * q).divisors.card : ℝ) := by
      refine Finset.sum_bij (fun m _ => m / d) ?_ ?_ ?_ ?_
      · intro m hm
        obtain ⟨hm_icc, hdm⟩ := mem_filter.mp hm
        have hm1 := (mem_Icc.mp hm_icc).1; have hm2 := (mem_Icc.mp hm_icc).2
        exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdm) (by omega), Nat.div_le_div_right hm2⟩
      · intro m₁ hm₁ m₂ hm₂ heq
        have h1 := Nat.mul_div_cancel' (mem_filter.mp hm₁).2
        have h2 := Nat.mul_div_cancel' (mem_filter.mp hm₂).2
        rw [← h1, ← h2, heq]
      · intro q hq
        have hq1 := (mem_Icc.mp hq).1; have hq2 := (mem_Icc.mp hq).2
        have hdq : d * q ≤ M := by have := (Nat.le_div_iff_mul_le (by omega)).mp hq2; linarith
        exact ⟨d * q, mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith, hdq⟩, dvd_mul_right d q⟩,
          Nat.mul_div_cancel_left q (by omega)⟩
      · intro m hm; rw [Nat.mul_div_cancel' (mem_filter.mp hm).2]
    rw [hbij]
    have hMd_pos : 1 ≤ M / d := Nat.div_pos hd2 (by omega)
    have hlog_le : Real.log ((M / d : ℕ) : ℝ) ≤ Real.log (M : ℝ) :=
      Real.log_le_log (by exact_mod_cast hMd_pos) (by exact_mod_cast Nat.div_le_self M d)
    have hdiv_le : ((M / d : ℕ) : ℝ) ≤ (M : ℝ) / (d : ℝ) := by
      have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      rw [le_div_iff₀ hdpos]; exact_mod_cast Nat.div_mul_le_self M d
    calc ∑ q ∈ Icc 1 (M / d), ((d * q).divisors.card : ℝ)
        ≤ ∑ q ∈ Icc 1 (M / d), (d.divisors.card : ℝ) * (q.divisors.card : ℝ) :=
          sum_le_sum fun q hq => by exact_mod_cast divisors_mul_card_le hd1 (mem_Icc.mp hq).1
      _ = (d.divisors.card : ℝ) * ∑ q ∈ Icc 1 (M / d), (q.divisors.card : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ (d.divisors.card : ℝ) * (((M / d : ℕ) : ℝ) * (1 + Real.log ((M / d : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left (sum_tau_le hMd_pos) (Nat.cast_nonneg _)
      _ ≤ (d.divisors.card : ℝ) * (((M : ℝ) / (d : ℝ)) * (1 + Real.log (M : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact mul_le_mul hdiv_le (by linarith) (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ (M / d : ℕ) by exact_mod_cast hMd_pos)]) (by positivity)
      _ = ((M : ℝ) * (1 + Real.log (M : ℝ))) * ((d.divisors.card : ℝ) / (d : ℝ)) := by ring
  calc ∑ d ∈ Icc 1 M, ∑ m ∈ Icc 1 M, (if d ∣ m then (m.divisors.card : ℝ) else 0)
      ≤ ∑ d ∈ Icc 1 M, ((M : ℝ) * (1 + Real.log (M : ℝ))) * ((d.divisors.card : ℝ) / (d : ℝ)) := sum_le_sum hinner
    _ = ((M : ℝ) * (1 + Real.log (M : ℝ))) * ∑ d ∈ Icc 1 M, (d.divisors.card : ℝ) / (d : ℝ) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ ((M : ℝ) * (1 + Real.log (M : ℝ))) * (1 + Real.log (M : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_tau_div_le hM) (by positivity)
    _ = (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 3 := by ring

/-- Discrete Abel summation on `Ioc P N` for a nonnegative increasing real weight `w` (`P < N`). -/
private lemma abel_increasing_Ioc {P N : ℕ} (hPN : P < N) (w : ℕ → ℝ) (g : ℕ → ℂ) {B : ℝ}
    (hB : 0 ≤ B)
    (hw_nn : ∀ m ∈ Ioc P N, 0 ≤ w m)
    (hw_mono : ∀ m ∈ Ioc P N, m + 1 ≤ N → w m ≤ w (m + 1))
    (hsum : ∀ t ∈ Icc P N, ‖∑ m ∈ Ioc P t, g m‖ ≤ B) :
    ‖∑ m ∈ Ioc P N, (w m : ℂ) * g m‖ ≤ 2 * w N * B := by
  let L := N - P
  have hL : 1 ≤ L := by omega
  have hreidx : ∑ m ∈ Ioc P N, (w m : ℂ) * g m =
      ∑ y ∈ range ((L - 1) + 1), (w (P + 1 + y) : ℂ) * g (P + 1 + y) := by
    refine Finset.sum_bij (fun m _ => m - (P + 1)) ?_ ?_ ?_ ?_
    · intro m hm; rw [mem_Ioc] at hm; rw [mem_range]; omega
    · intro a ha b hb h; rw [mem_Ioc] at ha hb; omega
    · intro y hy; rw [mem_range] at hy
      exact ⟨P + 1 + y, mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro m hm
      rw [mem_Ioc] at hm
      have hmeq : P + 1 + (m - (P + 1)) = m := by omega
      rw [hmeq]
  rw [hreidx, abel_sum_range_succ (L - 1) (fun y => (w (P + 1 + y) : ℂ)) (fun y => g (P + 1 + y))]
  have hpartial : ∀ t : ℕ, t < L →
      ∑ y ∈ range (t + 1), g (P + 1 + y) = ∑ m ∈ Ioc P (P + 1 + t), g m := by
    intro t _
    refine Finset.sum_bij (fun y _ => P + 1 + y) ?_ ?_ ?_ ?_
    · intro y hy; rw [mem_range] at hy; rw [mem_Ioc]; omega
    · intro a _ b _ h; omega
    · intro m hm; rw [mem_Ioc] at hm
      exact ⟨m - (P + 1), mem_range.mpr (by omega), by omega⟩
    · intro _ _; rfl
  have hN_eq : P + 1 + (L - 1) = N := by omega
  rw [hpartial (L - 1) (by omega), hN_eq]
  have h1 : ‖(w N : ℂ) * ∑ m ∈ Ioc P N, g m‖ ≤ w N * B := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw_nn N (mem_Ioc.mpr ⟨hPN, le_rfl⟩))]
    exact mul_le_mul_of_nonneg_left (hsum N (mem_Icc.mpr ⟨hPN.le, le_rfl⟩))
      (hw_nn N (mem_Ioc.mpr ⟨hPN, le_rfl⟩))
  have h2 : ‖∑ t ∈ range (L - 1), ((w (P + 1 + (t + 1)) : ℂ) - (w (P + 1 + t) : ℂ)) *
        ∑ y ∈ range (t + 1), g (P + 1 + y)‖ ≤ w N * B := by
    calc ‖∑ t ∈ range (L - 1), _‖
        ≤ ∑ t ∈ range (L - 1), ‖((w (P + 1 + (t + 1)) : ℂ) - (w (P + 1 + t) : ℂ)) *
            ∑ y ∈ range (t + 1), g (P + 1 + y)‖ := norm_sum_le _ _
      _ ≤ ∑ t ∈ range (L - 1), (w (P + 1 + (t + 1)) - w (P + 1 + t)) * B := by
          refine sum_le_sum fun t ht => ?_
          have htL : t < L - 1 := mem_range.mp ht
          rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, hpartial t (by omega)]
          have hdiff_nn : 0 ≤ w (P + 1 + (t + 1)) - w (P + 1 + t) := by
            have hle := hw_mono (P + 1 + t) (mem_Ioc.mpr ⟨by omega, by omega⟩) (by omega)
            rw [show P + 1 + (t + 1) = P + 1 + t + 1 by omega]; linarith
          rw [Real.norm_of_nonneg hdiff_nn]
          exact mul_le_mul_of_nonneg_left (hsum _ (mem_Icc.mpr ⟨by omega, by omega⟩)) hdiff_nn
      _ = (∑ t ∈ range (L - 1), (w (P + 1 + (t + 1)) - w (P + 1 + t))) * B := (Finset.sum_mul _ _ _).symm
      _ = (w N - w (P + 1)) * B := by
          have htel : ∑ t ∈ range (L - 1), (w (P + 1 + (t + 1)) - w (P + 1 + t)) =
              w (P + 1 + (L - 1)) - w (P + 1) :=
            Finset.sum_range_sub (fun t => w (P + 1 + t)) (L - 1)
          rw [htel, hN_eq]
      _ ≤ w N * B := by
          have hnn := hw_nn (P + 1) (mem_Ioc.mpr ⟨by omega, by omega⟩)
          nlinarith
  calc ‖(w N : ℂ) * ∑ m ∈ Ioc P N, g m - _‖
      ≤ ‖(w N : ℂ) * ∑ m ∈ Ioc P N, g m‖ + ‖_‖ := norm_sub_le _ _
    _ ≤ 2 * w N * B := by linarith

/-- Discrete Abel summation on `Ioc P N` for a nonnegative decreasing real weight `w` (`P < N`). -/
private lemma abel_decreasing_Ioc {P N : ℕ} (hPN : P < N) (w : ℕ → ℝ) (g : ℕ → ℂ) {B : ℝ}
    (_hB : 0 ≤ B)
    (hw_nn : ∀ m ∈ Ioc P N, 0 ≤ w m)
    (hw_anti : ∀ m ∈ Ioc P N, m + 1 ≤ N → w (m + 1) ≤ w m)
    (hsum : ∀ t ∈ Icc P N, ‖∑ m ∈ Ioc P t, g m‖ ≤ B) :
    ‖∑ m ∈ Ioc P N, (w m : ℂ) * g m‖ ≤ w (P + 1) * B := by
  let L := N - P
  have hreidx : ∑ m ∈ Ioc P N, (w m : ℂ) * g m =
      ∑ y ∈ range ((L - 1) + 1), (w (P + 1 + y) : ℂ) * g (P + 1 + y) := by
    refine Finset.sum_bij (fun m _ => m - (P + 1)) ?_ ?_ ?_ ?_
    · intro m hm; rw [mem_Ioc] at hm; rw [mem_range]; omega
    · intro a ha b hb h; rw [mem_Ioc] at ha hb; omega
    · intro y hy; rw [mem_range] at hy
      exact ⟨P + 1 + y, mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro m hm
      rw [mem_Ioc] at hm
      have hmeq : P + 1 + (m - (P + 1)) = m := by omega
      rw [hmeq]
  rw [hreidx, abel_sum_range_succ (L - 1) (fun y => (w (P + 1 + y) : ℂ)) (fun y => g (P + 1 + y))]
  have hpartial : ∀ t : ℕ, t < L →
      ∑ y ∈ range (t + 1), g (P + 1 + y) = ∑ m ∈ Ioc P (P + 1 + t), g m := by
    intro t _
    refine Finset.sum_bij (fun y _ => P + 1 + y) ?_ ?_ ?_ ?_
    · intro y hy; rw [mem_range] at hy; rw [mem_Ioc]; omega
    · intro a _ b _ h; omega
    · intro m hm; rw [mem_Ioc] at hm
      exact ⟨m - (P + 1), mem_range.mpr (by omega), by omega⟩
    · intro _ _; rfl
  have hN_eq : P + 1 + (L - 1) = N := by omega
  rw [hpartial (L - 1) (by omega), hN_eq]
  have h1 : ‖(w N : ℂ) * ∑ m ∈ Ioc P N, g m‖ ≤ w N * B := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw_nn N (mem_Ioc.mpr ⟨hPN, le_rfl⟩))]
    exact mul_le_mul_of_nonneg_left (hsum N (mem_Icc.mpr ⟨hPN.le, le_rfl⟩))
      (hw_nn N (mem_Ioc.mpr ⟨hPN, le_rfl⟩))
  have h2 : ‖∑ t ∈ range (L - 1), ((w (P + 1 + (t + 1)) : ℂ) - (w (P + 1 + t) : ℂ)) *
        ∑ y ∈ range (t + 1), g (P + 1 + y)‖ ≤ (w (P + 1) - w N) * B := by
    calc ‖∑ t ∈ range (L - 1), _‖
        ≤ ∑ t ∈ range (L - 1), ‖((w (P + 1 + (t + 1)) : ℂ) - (w (P + 1 + t) : ℂ)) *
            ∑ y ∈ range (t + 1), g (P + 1 + y)‖ := norm_sum_le _ _
      _ ≤ ∑ t ∈ range (L - 1), (w (P + 1 + t) - w (P + 1 + (t + 1))) * B := by
          refine sum_le_sum fun t ht => ?_
          have htL : t < L - 1 := mem_range.mp ht
          rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, hpartial t (by omega)]
          have hdiff_nn : 0 ≤ w (P + 1 + t) - w (P + 1 + (t + 1)) := by
            have hle := hw_anti (P + 1 + t) (mem_Ioc.mpr ⟨by omega, by omega⟩) (by omega)
            rw [show P + 1 + (t + 1) = P + 1 + t + 1 by omega]; linarith
          rw [Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg hdiff_nn]
          exact mul_le_mul_of_nonneg_left (hsum _ (mem_Icc.mpr ⟨by omega, by omega⟩)) hdiff_nn
      _ = (∑ t ∈ range (L - 1), (w (P + 1 + t) - w (P + 1 + (t + 1)))) * B := (Finset.sum_mul _ _ _).symm
      _ = (w (P + 1) - w N) * B := by
          have htel : ∑ t ∈ range (L - 1), (w (P + 1 + t) - w (P + 1 + (t + 1))) =
              w (P + 1) - w (P + 1 + (L - 1)) := by
            have := Finset.sum_range_sub' (fun t => w (P + 1 + t)) (L - 1)
            simpa using this
          rw [htel, hN_eq]
  calc ‖(w N : ℂ) * ∑ m ∈ Ioc P N, g m - _‖
      ≤ ‖(w N : ℂ) * ∑ m ∈ Ioc P N, g m‖ + ‖_‖ := norm_sub_le _ _
    _ ≤ w N * B + (w (P + 1) - w N) * B := add_le_add h1 h2
    _ = w (P + 1) * B := by ring

/- ### Part 2: Uniform Vinogradov-Korobov reciprocal sum corollary -/

set_option maxHeartbeats 1600000 in
/-- Uniform reciprocal exponential sum saving `M₁ / (log n)^12` across the entire
    Vinogradov range `exp((1/8) * (log n)^(9/10)) ≤ M₁ ≤ 2 * n^(1/100)` and `n^(1/2) ≤ α ≤ 2 * n`. -/
private lemma recip_sum_uniform :
    ∀ᶠ n : ℕ in atTop,
      ∀ (M₁ N₁ : ℕ) (α : ℝ),
        Real.exp ((1 / 8 : ℝ) * (Real.log (n : ℝ)) ^ ((9 : ℝ) / 10)) ≤ (M₁ : ℝ) →
        (M₁ : ℝ) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 100) →
        M₁ ≤ N₁ → N₁ ≤ 2 * M₁ →
        (n : ℝ) ^ ((1 : ℝ) / 2) ≤ |α| → |α| ≤ 2 * (n : ℝ) →
        ‖∑ x ∈ Ioc M₁ N₁, e (α / (x : ℝ))‖ ≤ (M₁ : ℝ) / (Real.log (n : ℝ)) ^ 12 := by
  -- Asymptotic growth of L = log n: we need several elementary inequalities for large L.
  have hL_top : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogL_o1 : Tendsto (fun L : ℝ => Real.log L / L ^ ((1 : ℝ) / 10)) atTop (nhds 0) :=
    isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10) |>.tendsto_div_nhds_zero
  have hL10_top : Tendsto (fun L : ℝ => L ^ ((1 : ℝ) / 10)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)
  have hL9_top : Tendsto (fun L : ℝ => L ^ ((9 : ℝ) / 10)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9 / 10)
  -- Key exponent comparison: L^(7/10) / (10^6 * log L) ≥ 500 * L^(1/10) * log L + 20 * log L + 20
  have hkey_L : ∀ᶠ L : ℝ in atTop,
      1000 ≤ L ∧
      Real.log L ≤ L ^ ((1 : ℝ) / 10) ∧
      (500 * L ^ ((1 : ℝ) / 10) * Real.log L + 20 * Real.log L + 20) * (1000000 * Real.log L) ≤
        L ^ ((7 : ℝ) / 10) ∧
      (1 / 24 : ℝ) * L ^ ((9 : ℝ) / 10) ≥ 20 * Real.log L + 100 := by
    have h1 : ∀ᶠ L : ℝ in atTop, Real.log L / L ^ ((1 : ℝ) / 10) < 1 / 1000000 :=
      hlogL_o1.eventually (gt_mem_nhds (by norm_num))
    have h2 : ∀ᶠ L : ℝ in atTop, (100000000 : ℝ) ≤ L ^ ((1 : ℝ) / 10) :=
      hL10_top.eventually_ge_atTop 100000000
    filter_upwards [eventually_ge_atTop (1000 : ℝ), h1, h2] with L hL1000 hlo hbig
    have hLpos : 0 < L := by linarith
    have hL10_pos : 0 < L ^ ((1 : ℝ) / 10) := Real.rpow_pos_of_pos hLpos _
    have hlogL_pos : 0 < Real.log L := Real.log_pos (by linarith)
    have hlogL_le : Real.log L ≤ L ^ ((1 : ℝ) / 10) / 1000000 := by
      have := (div_lt_iff₀ hL10_pos).mp hlo; linarith
    have hL10_pow : ∀ m : ℕ, (L ^ ((1 : ℝ) / 10)) ^ m = L ^ ((m : ℝ) / 10) := fun m => by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]; congr 1; ring
    refine ⟨hL1000, by linarith, ?_, ?_⟩
    · have hA : 500 * L ^ ((1 : ℝ) / 10) * Real.log L + 20 * Real.log L + 20 ≤
          (L ^ ((1 : ℝ) / 10)) ^ 2 := by
        nlinarith [hL10_pos, hlogL_pos]
      have hB : 1000000 * Real.log L ≤ L ^ ((1 : ℝ) / 10) := by linarith
      have hprod : (500 * L ^ ((1 : ℝ) / 10) * Real.log L + 20 * Real.log L + 20) * (1000000 * Real.log L) ≤
          (L ^ ((1 : ℝ) / 10)) ^ 3 := by
        calc _ ≤ (L ^ ((1 : ℝ) / 10)) ^ 2 * L ^ ((1 : ℝ) / 10) :=
              mul_le_mul hA hB (by positivity) (by positivity)
          _ = (L ^ ((1 : ℝ) / 10)) ^ 3 := by ring
      have h37 : (L ^ ((1 : ℝ) / 10)) ^ 3 ≤ L ^ ((7 : ℝ) / 10) := by
        rw [hL10_pow 3]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      exact hprod.trans h37
    · have h9 : (L ^ ((1 : ℝ) / 10)) ^ 9 = L ^ ((9 : ℝ) / 10) := by
        simpa using hL10_pow 9
      have hge : L ^ ((1 : ℝ) / 10) ≤ L ^ ((9 : ℝ) / 10) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      linarith
  filter_upwards [hL_top.eventually hkey_L, eventually_ge_atTop 1000] with n hL hn1000
  obtain ⟨hL1000, hlogL_le, hdom, hL9_big⟩ := hL
  let L : ℝ := Real.log (n : ℝ)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hlogL_pos : 0 < Real.log L := Real.log_pos (by dsimp [L]; linarith)
  intro M₁ N₁ α hM₁_lo hM₁_hi hMN hN2M hα_lo hα_hi
  -- Reduce to α > 0 using star(e(x)) = e(-x)
  suffices hpos : ∀ (β : ℝ), (n : ℝ) ^ ((1 : ℝ) / 2) ≤ β → β ≤ 2 * (n : ℝ) →
      ‖∑ x ∈ Ioc M₁ N₁, e (β / (x : ℝ))‖ ≤ (M₁ : ℝ) / L ^ 12 by
    rcases le_or_gt 0 α with hα0 | hα0
    · rw [abs_of_nonneg hα0] at hα_lo hα_hi
      exact hpos α hα_lo hα_hi
    · rw [abs_of_neg hα0] at hα_lo hα_hi
      have hconj : (∑ x ∈ Ioc M₁ N₁, e (α / (x : ℝ))) = star (∑ x ∈ Ioc M₁ N₁, e ((-α) / (x : ℝ))) := by
        rw [star_sum]
        refine sum_congr rfl fun x _ => ?_
        rw [e_star]; congr 1; ring
      rw [hconj, norm_star]
      exact hpos (-α) hα_lo hα_hi
  intro β hβ_lo hβ_hi
  have hβ_pos : 0 < β := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hβ_lo
  have hM₁_ge100 : 100 ≤ M₁ := by
    have h1 : (100 : ℝ) ≤ (M₁ : ℝ) := by
      have hexp : (100 : ℝ) ≤ Real.exp ((1 / 8 : ℝ) * L ^ ((9 : ℝ) / 10)) := by
        have h10 : (10 : ℝ) ≤ (1 / 8 : ℝ) * L ^ ((9 : ℝ) / 10) := by linarith
        have h100 : (100 : ℝ) ≤ Real.exp 10 := by
          have : (2 : ℝ) ^ 10 ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 10
          rw [← Real.exp_nat_mul] at this; norm_num at this ⊢; linarith
        exact h100.trans (Real.exp_le_exp.mpr h10)
      exact hexp.trans hM₁_lo
    exact_mod_cast h1
  have hM₁_pos : (0 : ℝ) < M₁ := by exact_mod_cast (by omega : 0 < M₁)
  have hlogM_lo : (1 / 8 : ℝ) * L ^ ((9 : ℝ) / 10) ≤ Real.log (M₁ : ℝ) := by
    have := Real.log_le_log (Real.exp_pos _) hM₁_lo
    rwa [Real.log_exp] at this
  have hlogM_pos : 0 < Real.log (M₁ : ℝ) := lt_of_lt_of_le (by positivity) hlogM_lo
  have hlogβ_le : Real.log β ≤ 2 * L := by
    have h1 : Real.log β ≤ Real.log (2 * (n : ℝ)) := Real.log_le_log hβ_pos hβ_hi
    rw [Real.log_mul (by norm_num) hnpos.ne'] at h1
    have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    linarith
  -- Choose k and l
  let k : ℕ := Nat.ceil (2 * Real.log β / Real.log (M₁ : ℝ)) + 4
  let l : ℕ := Nat.ceil (3 * (k : ℝ) * Real.log (k : ℝ)) + 1
  let s : ℕ := k ^ 2 + k * l
  let Y : ℕ := Nat.sqrt M₁
  have hk4 : 4 ≤ k := by dsimp [k]; omega
  have hl1 : 1 ≤ l := by dsimp [l]; omega
  have hkR_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk_le : (k : ℝ) ≤ 33 * L ^ ((1 : ℝ) / 10) := by
    have hfrac : 2 * Real.log β / Real.log (M₁ : ℝ) ≤ 32 * L ^ ((1 : ℝ) / 10) := by
      rw [div_le_iff₀ hlogM_pos]
      have hL9_mul : L ^ ((1 : ℝ) / 10) * L ^ ((9 : ℝ) / 10) = L := by
        rw [← Real.rpow_add hLpos]; norm_num
      have h1 : 32 * L ^ ((1 : ℝ) / 10) * ((1 / 8 : ℝ) * L ^ ((9 : ℝ) / 10)) = 4 * L := by
        calc _ = 4 * (L ^ ((1 : ℝ) / 10) * L ^ ((9 : ℝ) / 10)) := by ring
          _ = 4 * L := by rw [hL9_mul]
      have h2 := mul_le_mul_of_nonneg_left hlogM_lo (show (0 : ℝ) ≤ 32 * L ^ ((1 : ℝ) / 10) by positivity)
      linarith
    have hceil : (Nat.ceil (2 * Real.log β / Real.log (M₁ : ℝ)) : ℝ) <
        2 * Real.log β / Real.log (M₁ : ℝ) + 1 :=
      Nat.ceil_lt_add_one (div_nonneg (mul_nonneg zero_le_two (Real.log_nonneg (by
        have h1 : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
        linarith))) hlogM_pos.le)
    have hL10_ge : (5 : ℝ) ≤ L ^ ((1 : ℝ) / 10) := by
      have : (5 : ℝ) ≤ Real.log L := by
        have h1 : Real.exp 5 ≤ 1000 := by
          have : Real.exp 5 = (Real.exp 1) ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
          rw [this]
          have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
          have : (Real.exp 1) ^ 5 < 3 ^ 5 := pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
          norm_num at this; linarith
        have := Real.log_le_log (Real.exp_pos 5) (h1.trans hL1000)
        rwa [Real.log_exp] at this
      linarith
    dsimp only [k]; push_cast; linarith
  -- Verify M₁^3 ≤ β and β ≤ M₁^(k/2)
  have hβ_ge_M3 : (M₁ : ℝ) ^ (3 : ℕ) ≤ β := by
    have h1 : (M₁ : ℝ) ^ (3 : ℕ) ≤ 8 * (n : ℝ) ^ ((3 : ℝ) / 100) := by
      calc (M₁ : ℝ) ^ (3 : ℕ) ≤ (2 * (n : ℝ) ^ ((1 : ℝ) / 100)) ^ (3 : ℕ) :=
            pow_le_pow_left₀ hM₁_pos.le hM₁_hi 3
        _ = 8 * ((n : ℝ) ^ ((1 : ℝ) / 100)) ^ (3 : ℕ) := by ring
        _ = 8 * (n : ℝ) ^ ((3 : ℝ) / 100) := by
            rw [← Real.rpow_natCast ((n : ℝ) ^ _), ← Real.rpow_mul hnpos.le]; congr 2; norm_num
    have h2 : 8 * (n : ℝ) ^ ((3 : ℝ) / 100) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := by
      have hn_ge : (8 : ℝ) ≤ (n : ℝ) ^ ((47 : ℝ) / 100) := by
        have h1000 : (8 : ℝ) ≤ (1000 : ℝ) ^ ((47 : ℝ) / 100) := by
          have hpow : (8 : ℝ) ^ (100 : ℕ) ≤ (1000 : ℝ) ^ (47 : ℕ) := by norm_num
          have hr := Real.rpow_le_rpow (by positivity) hpow (show (0 : ℝ) ≤ 1 / 100 by norm_num)
          rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
            ← Real.rpow_mul (by norm_num)] at hr
          norm_num at hr; exact hr
        exact h1000.trans (Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hn1000) (by norm_num))
      have hmul := mul_le_mul_of_nonneg_right hn_ge (Real.rpow_nonneg hnpos.le ((3 : ℝ) / 100))
      rw [← Real.rpow_add hnpos] at hmul
      norm_num at hmul; exact hmul
    exact (h1.trans h2).trans hβ_lo
  have hβ_le_Mk : β ≤ (M₁ : ℝ) ^ ((k : ℝ) / 2) := by
    have hk_ge : 2 * Real.log β / Real.log (M₁ : ℝ) ≤ (k : ℝ) := by
      dsimp only [k]; push_cast
      linarith [Nat.le_ceil (2 * Real.log β / Real.log (M₁ : ℝ))]
    have hlog_le : Real.log β ≤ ((k : ℝ) / 2) * Real.log (M₁ : ℝ) := by
      have := (div_le_iff₀ hlogM_pos).mp hk_ge
      linarith
    calc β = Real.exp (Real.log β) := (Real.exp_log hβ_pos).symm
      _ ≤ Real.exp (((k : ℝ) / 2) * Real.log (M₁ : ℝ)) := Real.exp_le_exp.mpr hlog_le
      _ = (M₁ : ℝ) ^ ((k : ℝ) / 2) := by rw [Real.rpow_def_of_pos hM₁_pos, mul_comm]
  -- Lower bound on Y = Nat.sqrt M₁: log Y ≥ (1/24) * L^(9/10)
  have hY_ge10 : 10 ≤ Y := Nat.le_sqrt.mpr (by omega)
  have hY_pos : 0 < Y := by omega
  have hY_Rpos : (0 : ℝ) < Y := by exact_mod_cast hY_pos
  have hY_lo : Real.exp ((1 / 24 : ℝ) * L ^ ((9 : ℝ) / 10)) ≤ (Y : ℝ) := by
    have hM_lt : (M₁ : ℝ) ≤ ((Y : ℝ) + 1) ^ 2 := by
      have h1 : M₁ ≤ (Y + 1) ^ 2 := by simpa [sq] using (Nat.lt_succ_sqrt M₁).le
      exact_mod_cast h1
    have h2Y : (Y : ℝ) + 1 ≤ 2 * (Y : ℝ) := by
      have : (1 : ℝ) ≤ Y := by exact_mod_cast hY_pos
      linarith
    have h4Y2 : (M₁ : ℝ) ≤ 4 * (Y : ℝ) ^ 2 := by nlinarith
    have hsqrt : (1 / 2 : ℝ) * (M₁ : ℝ) ^ ((1 : ℝ) / 2) ≤ (Y : ℝ) := by
      have h1 := Real.rpow_le_rpow hM₁_pos.le h4Y2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast (Y : ℝ),
        ← Real.rpow_mul hY_Rpos.le] at h1
      have h412 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num)]
        norm_num
      rw [h412] at h1; norm_num at h1; linarith
    have hexp_half : Real.exp ((1 / 16 : ℝ) * L ^ ((9 : ℝ) / 10)) ≤ (M₁ : ℝ) ^ ((1 : ℝ) / 2) := by
      have h1 := Real.rpow_le_rpow (Real.exp_pos _).le hM₁_lo (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      rw [← Real.exp_mul] at h1
      have heq : (1 / 8 : ℝ) * L ^ ((9 : ℝ) / 10) * (1 / 2) = (1 / 16 : ℝ) * L ^ ((9 : ℝ) / 10) := by ring
      rwa [heq] at h1
    have hgap : (1 / 24 : ℝ) * L ^ ((9 : ℝ) / 10) + 1 ≤ (1 / 16 : ℝ) * L ^ ((9 : ℝ) / 10) := by
      have : (48 : ℝ) ≤ L ^ ((9 : ℝ) / 10) := by linarith
      linarith
    have h2_le_e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc Real.exp ((1 / 24 : ℝ) * L ^ ((9 : ℝ) / 10))
        = (1 / 2 : ℝ) * (2 * Real.exp ((1 / 24 : ℝ) * L ^ ((9 : ℝ) / 10))) := by ring
      _ ≤ (1 / 2 : ℝ) * (Real.exp 1 * Real.exp ((1 / 24 : ℝ) * L ^ ((9 : ℝ) / 10))) := by
          gcongr
      _ = (1 / 2 : ℝ) * Real.exp ((1 / 24 : ℝ) * L ^ ((9 : ℝ) / 10) + 1) := by
          rw [← Real.exp_add]; congr 2; ring
      _ ≤ (1 / 2 : ℝ) * Real.exp ((1 / 16 : ℝ) * L ^ ((9 : ℝ) / 10)) := by
          gcongr
      _ ≤ (1 / 2 : ℝ) * (M₁ : ℝ) ^ ((1 : ℝ) / 2) := by gcongr
      _ ≤ (Y : ℝ) := hsqrt
  have hlogY_lo : (1 / 24 : ℝ) * L ^ ((9 : ℝ) / 10) ≤ Real.log (Y : ℝ) := by
    have := Real.log_le_log (Real.exp_pos _) hY_lo
    rwa [Real.log_exp] at this
  have hY_ge_L14 : 120 * L ^ 13 ≤ (Y : ℝ) := by
    have h1 : Real.log (120 * L ^ 13) ≤ (1 / 24 : ℝ) * L ^ ((9 : ℝ) / 10) := by
      rw [Real.log_mul (by norm_num) (pow_pos hLpos 13).ne', Real.log_pow]
      have hlog120 : Real.log 120 ≤ 5 := by
        have : (120 : ℝ) ≤ Real.exp 5 := by
          have : (2.7 : ℝ) ^ 5 ≤ (Real.exp 1) ^ 5 :=
            pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 5
          rw [← Real.exp_nat_mul] at this; norm_num at this ⊢; linarith
        have := Real.log_le_log (by norm_num) this; rwa [Real.log_exp] at this
      push_cast; linarith
    calc 120 * L ^ 13 = Real.exp (Real.log (120 * L ^ 13)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp ((1 / 24 : ℝ) * L ^ ((9 : ℝ) / 10)) := Real.exp_le_exp.mpr h1
      _ ≤ (Y : ℝ) := hY_lo
  have hkY : 16 * k ≤ Y := by
    have h1 : 16 * (k : ℝ) ≤ (Y : ℝ) := by
      have hL10_le_L : L ^ ((1 : ℝ) / 10) ≤ L := by
        conv_rhs => rw [← Real.rpow_one L]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have h528 : 528 * L ≤ 120 * L ^ 13 := by
        have hL12 : (5 : ℝ) ≤ L ^ 12 := by
          have : (1000 : ℝ) ^ 12 ≤ L ^ 12 := pow_le_pow_left₀ (by norm_num) hL1000 12
          norm_num at this; linarith
        have hL13 : L ^ 13 = L * L ^ 12 := by ring
        nlinarith [hLpos]
      linarith [hk_le, hY_ge_L14, h528]
    exact_mod_cast h1
  -- Invoke M3_RecipSum.vinogradov_reciprocal_sum!
  have hvk := vinogradov_reciprocal_sum hMN hN2M hM₁_ge100 hk4 hl1 hβ_ge_M3 hβ_le_Mk hkY
  let δ : ℝ := ((k * (k + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (k : ℝ)) ^ l
  change ‖∑ x ∈ Ioc M₁ N₁, e (β / (x : ℝ))‖ ≤
    4 * (M₁ : ℝ) * ((4 * (s : ℝ)) ^ (5 * k) * (Y : ℝ) ^ ((-1 + δ) / (2 * (s : ℝ))) + 1 / (Y : ℝ)) +
    10 * (k : ℝ) * (Y : ℝ) at hvk
  -- Bound δ ≤ 1/2
  have hδ_le : δ ≤ 1 / 2 := by
    have h1mk : 1 - 1 / (k : ℝ) ≤ Real.exp (-(1 / (k : ℝ))) := by
      linarith [Real.add_one_le_exp (-(1 / (k : ℝ)))]
    have h1mk_nn : 0 ≤ 1 - 1 / (k : ℝ) := by
      have : 1 / (k : ℝ) ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast (by omega : 1 ≤ k)) hkR_pos.le
      linarith
    have hpow_le : (1 - 1 / (k : ℝ)) ^ l ≤ (k : ℝ) ^ (-(3 : ℝ)) := by
      have hl_ge : 3 * (k : ℝ) * Real.log (k : ℝ) ≤ (l : ℝ) := by
        dsimp only [l]; push_cast
        linarith [Nat.le_ceil (3 * (k : ℝ) * Real.log (k : ℝ))]
      calc (1 - 1 / (k : ℝ)) ^ l ≤ (Real.exp (-(1 / (k : ℝ)))) ^ l :=
            pow_le_pow_left₀ h1mk_nn h1mk l
        _ = Real.exp (-((l : ℝ) / (k : ℝ))) := by rw [← Real.exp_nat_mul]; congr 1; ring
        _ ≤ Real.exp (-(3 * Real.log (k : ℝ))) := by
            refine Real.exp_le_exp.mpr ?_
            have : 3 * Real.log (k : ℝ) ≤ (l : ℝ) / (k : ℝ) := by
              rw [le_div_iff₀ hkR_pos]; linarith
            linarith
        _ = (k : ℝ) ^ (-(3 : ℝ)) := by
            rw [Real.rpow_def_of_pos hkR_pos]; congr 1; ring
    have hkk1 : ((k * (k + 1) : ℕ) : ℝ) / 2 ≤ (k : ℝ) ^ (2 : ℕ) := by
      have hk4R : (4 : ℝ) ≤ k := by exact_mod_cast hk4
      push_cast; nlinarith
    calc δ ≤ (k : ℝ) ^ (2 : ℕ) * (k : ℝ) ^ (-(3 : ℝ)) :=
          mul_le_mul hkk1 hpow_le (pow_nonneg h1mk_nn l) (by positivity)
      _ = (k : ℝ) ^ (-(1 : ℝ)) := by
          rw [← Real.rpow_natCast (k : ℝ), ← Real.rpow_add hkR_pos]; congr 1; norm_num
      _ = 1 / (k : ℝ) := by rw [Real.rpow_neg_one, inv_eq_one_div]
      _ ≤ 1 / 2 := by
          have hk4R : (4 : ℝ) ≤ k := by exact_mod_cast hk4
          rw [div_le_div_iff₀ hkR_pos (by norm_num)]; linarith
  -- Bound s ≤ 10000 * L^(2/10) * log L and 4 * s ≤ L^2
  have hs_pos : (0 : ℝ) < s := by exact_mod_cast (by dsimp [s]; nlinarith : 0 < s)
  have hlogk_le : Real.log (k : ℝ) ≤ Real.log L := by
    refine Real.log_le_log hkR_pos ?_
    have hL10_le : 33 * L ^ ((1 : ℝ) / 10) ≤ L := by
      have h9 : (33 : ℝ) ≤ L ^ ((9 : ℝ) / 10) := by linarith [hL9_big]
      have hmul := mul_le_mul_of_nonneg_right h9 (Real.rpow_nonneg hLpos.le ((1 : ℝ) / 10))
      rw [← Real.rpow_add hLpos] at hmul; norm_num at hmul; linarith
    exact hk_le.trans hL10_le
  have hl_le : (l : ℝ) ≤ 4 * (k : ℝ) * Real.log L := by
    have hceil : (Nat.ceil (3 * (k : ℝ) * Real.log (k : ℝ)) : ℝ) <
        3 * (k : ℝ) * Real.log (k : ℝ) + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg (by norm_num) hkR_pos.le)
        (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))))
    have hlogk_ge1 : (1 : ℝ) ≤ Real.log (k : ℝ) := by
      have : Real.exp 1 ≤ (k : ℝ) := by
        have hk4R : (4 : ℝ) ≤ k := by exact_mod_cast hk4
        linarith [Real.exp_one_lt_d9]
      have := Real.log_le_log (Real.exp_pos 1) this
      rwa [Real.log_exp] at this
    have hk4R : (4 : ℝ) ≤ k := by exact_mod_cast hk4
    have h1 : 3 * (k : ℝ) * Real.log (k : ℝ) + 2 ≤ 4 * (k : ℝ) * Real.log (k : ℝ) := by nlinarith
    have h2 : 4 * (k : ℝ) * Real.log (k : ℝ) ≤ 4 * (k : ℝ) * Real.log L :=
      mul_le_mul_of_nonneg_left hlogk_le (by positivity)
    dsimp only [l]; push_cast; linarith
  have hs_le : (s : ℝ) ≤ 6000 * L ^ ((2 : ℝ) / 10) * Real.log L := by
    have hlogL_ge1 : (1 : ℝ) ≤ Real.log L := by
      have : Real.exp 1 ≤ L := by linarith [Real.exp_one_lt_d9]
      have := Real.log_le_log (Real.exp_pos 1) this; rwa [Real.log_exp] at this
    have hk2_le : (k : ℝ) ^ 2 ≤ 1089 * L ^ ((2 : ℝ) / 10) := by
      have hsq := pow_le_pow_left₀ hkR_pos.le hk_le 2
      rw [mul_pow, ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hLpos.le] at hsq
      norm_num at hsq ⊢; linarith
    have hs_cast : (s : ℝ) = (k : ℝ) ^ 2 + (k : ℝ) * (l : ℝ) := by dsimp [s]; push_cast; ring
    have hkl : (k : ℝ) * (l : ℝ) ≤ 4 * (k : ℝ) ^ 2 * Real.log L := by
      calc (k : ℝ) * (l : ℝ) ≤ (k : ℝ) * (4 * (k : ℝ) * Real.log L) :=
            mul_le_mul_of_nonneg_left hl_le hkR_pos.le
        _ = 4 * (k : ℝ) ^ 2 * Real.log L := by ring
    nlinarith [Real.rpow_nonneg hLpos.le ((2 : ℝ) / 10)]
  have hlog4s_le : Real.log (4 * (s : ℝ)) ≤ 3 * Real.log L := by
    have h4s_le : 4 * (s : ℝ) ≤ L ^ 3 := by
      have hL2 : L ^ ((2 : ℝ) / 10) ≤ L := by
        conv_rhs => rw [← Real.rpow_one L]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have hlogL_le_L : Real.log L ≤ L := by linarith [Real.log_le_sub_one_of_pos hLpos]
      have h24k : 24000 * L ^ ((2 : ℝ) / 10) * Real.log L ≤ L ^ 3 := by
        have h1 : (24000 : ℝ) * L ^ ((2 : ℝ) / 10) ≤ L ^ 2 := by
          have hL18 : (24000 : ℝ) ≤ L ^ ((9 : ℝ) / 10) * L ^ ((9 : ℝ) / 10) := by
            have : (200 : ℝ) ≤ L ^ ((9 : ℝ) / 10) := by linarith [hL9_big]
            nlinarith
          have hmul : (24000 : ℝ) * L ^ ((2 : ℝ) / 10) ≤
              (L ^ ((9 : ℝ) / 10) * L ^ ((9 : ℝ) / 10)) * L ^ ((2 : ℝ) / 10) :=
            mul_le_mul_of_nonneg_right hL18 (Real.rpow_nonneg hLpos.le _)
          rw [← Real.rpow_add hLpos, ← Real.rpow_add hLpos] at hmul
          have h2eq : (9 : ℝ) / 10 + 9 / 10 + 2 / 10 = (2 : ℕ) := by norm_num
          rw [h2eq, Real.rpow_natCast] at hmul; exact hmul
        nlinarith [hlogL_pos]
      linarith
    have h1 := Real.log_le_log (by positivity) h4s_le
    rwa [Real.log_pow] at h1
  -- Main term: (4*s)^(5*k) * Y^((-1+δ)/(2*s)) ≤ 1 / (12 * L^12)
  have hmain_le : (4 * (s : ℝ)) ^ (5 * k) * (Y : ℝ) ^ ((-1 + δ) / (2 * (s : ℝ))) ≤
      1 / (12 * L ^ 12) := by
    have hY_pow_le : (Y : ℝ) ^ ((-1 + δ) / (2 * (s : ℝ))) ≤ (Y : ℝ) ^ (-(1 / (4 * (s : ℝ)))) := by
      refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hY_pos) ?_
      rw [show -(1 / (4 * (s : ℝ))) = (-1 / 2) / (2 * (s : ℝ)) by ring]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    have hlog_lhs : Real.log ((4 * (s : ℝ)) ^ (5 * k) * (Y : ℝ) ^ (-(1 / (4 * (s : ℝ))))) ≤
        Real.log (1 / (12 * L ^ 12)) := by
      rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hY_Rpos _).ne',
        Real.log_pow, Real.log_rpow hY_Rpos, Real.log_div one_ne_zero (by positivity),
        Real.log_one, zero_sub, Real.log_mul (by norm_num) (pow_pos hLpos 12).ne', Real.log_pow]
      have hterm1 : ((5 * k : ℕ) : ℝ) * Real.log (4 * (s : ℝ)) ≤ 500 * L ^ ((1 : ℝ) / 10) * Real.log L := by
        push_cast
        have h4s_ge1 : (1 : ℝ) ≤ 4 * (s : ℝ) := by
          have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (by dsimp [s]; nlinarith : 1 ≤ s)
          linarith
        have h1 : 5 * (k : ℝ) * Real.log (4 * (s : ℝ)) ≤ 5 * (33 * L ^ ((1 : ℝ) / 10)) * (3 * Real.log L) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hk_le (by norm_num)) hlog4s_le
            (Real.log_nonneg h4s_ge1) (by positivity)
        have hnn : 0 ≤ L ^ ((1 : ℝ) / 10) * Real.log L := by positivity
        linarith
      have hterm2 : L ^ ((7 : ℝ) / 10) / (1000000 * Real.log L) ≤
          (1 / (4 * (s : ℝ))) * Real.log (Y : ℝ) := by
        have hden : 4 * (s : ℝ) ≤ 24000 * L ^ ((2 : ℝ) / 10) * Real.log L := by linarith
        have h1 : (1 / (24000 * L ^ ((2 : ℝ) / 10) * Real.log L)) * ((1 / 24 : ℝ) * L ^ ((9 : ℝ) / 10)) ≤
            (1 / (4 * (s : ℝ))) * Real.log (Y : ℝ) :=
          mul_le_mul (one_div_le_one_div_of_le (by positivity) hden) hlogY_lo (by positivity) (by positivity)
        have h2 : (1 / (24000 * L ^ ((2 : ℝ) / 10) * Real.log L)) * ((1 / 24 : ℝ) * L ^ ((9 : ℝ) / 10)) =
            L ^ ((7 : ℝ) / 10) / (576000 * Real.log L) := by
          have hsub : L ^ ((9 : ℝ) / 10) / L ^ ((2 : ℝ) / 10) = L ^ ((7 : ℝ) / 10) := by
            rw [← Real.rpow_sub hLpos]; congr 1; norm_num
          calc _ = (L ^ ((9 : ℝ) / 10) / L ^ ((2 : ℝ) / 10)) / (576000 * Real.log L) := by ring
            _ = L ^ ((7 : ℝ) / 10) / (576000 * Real.log L) := by rw [hsub]
        have h3 : L ^ ((7 : ℝ) / 10) / (1000000 * Real.log L) ≤
            L ^ ((7 : ℝ) / 10) / (576000 * Real.log L) :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg hLpos.le _) (by positivity) (by linarith)
        linarith
      have hlog12 : Real.log 12 ≤ 20 := by
        have : (12 : ℝ) ≤ Real.exp 20 := by
          have : (2 : ℝ) ^ 20 ≤ (Real.exp 1) ^ 20 :=
            pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 20
          rw [← Real.exp_nat_mul] at this; norm_num at this ⊢; linarith
        have := Real.log_le_log (by norm_num) this; rwa [Real.log_exp] at this
      have hdom' : 500 * L ^ ((1 : ℝ) / 10) * Real.log L + 20 * Real.log L + 20 ≤
          L ^ ((7 : ℝ) / 10) / (1000000 * Real.log L) :=
        (le_div_iff₀ (by positivity)).mpr hdom
      have hneg_eq : -(1 / (4 * (s : ℝ))) * Real.log (Y : ℝ) = -((1 / (4 * (s : ℝ))) * Real.log (Y : ℝ)) := by ring
      push_cast at hterm1 ⊢; linarith
    have hexp_le := Real.exp_le_exp.mpr hlog_lhs
    rw [Real.exp_log (by positivity), Real.exp_log (by positivity)] at hexp_le
    exact (mul_le_mul_of_nonneg_left hY_pow_le (by positivity)).trans hexp_le
  -- Bound the two smaller error terms: 1/Y ≤ 1/(12 L^12) and 10*k*Y ≤ M₁/(3 L^12)
  have h1Y_le : 1 / (Y : ℝ) ≤ 1 / (12 * L ^ 12) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    have : L ^ 12 ≤ L ^ 13 := pow_le_pow_right₀ (by linarith) (by omega)
    linarith [hY_ge_L14]
  have h10kY_le : 10 * (k : ℝ) * (Y : ℝ) ≤ (M₁ : ℝ) / (3 * L ^ 12) := by
    have hY2 : (Y : ℝ) * (Y : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast Nat.sqrt_le M₁
    have h30kL : 30 * (k : ℝ) * L ^ 12 ≤ (Y : ℝ) := by
      have hL10_le_L : L ^ ((1 : ℝ) / 10) ≤ L := by
        conv_rhs => rw [← Real.rpow_one L]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have hkL : 30 * (k : ℝ) * L ^ 12 ≤ 30 * (33 * L) * L ^ 12 := by
        have hkL' : (k : ℝ) ≤ 33 * L := hk_le.trans (mul_le_mul_of_nonneg_left hL10_le_L (by norm_num))
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkL' (by norm_num)) (by positivity)
      have h990 : 30 * (33 * L) * L ^ 12 = 990 * L ^ 13 := by ring
      -- Wait: hY_ge_L14 gave 120 * L^13 ≤ Y, and we want 990 * L^13 ≤ Y!
      -- Since L ≥ 1000 and Y ≥ exp(L^(9/10)/24) ≥ exp(20 log L + 100) = e^100 * L^20,
      -- even 1000 * L^13 ≤ Y! Let's prove 1000 * L^13 ≤ Y from hL9_big!
      have hY_ge_1000L13 : 1000 * L ^ 13 ≤ (Y : ℝ) := by
        have h1 : Real.log (1000 * L ^ 13) ≤ (1 / 24 : ℝ) * L ^ ((9 : ℝ) / 10) := by
          rw [Real.log_mul (by norm_num) (pow_pos hLpos 13).ne', Real.log_pow]
          have hlog1000 : Real.log 1000 ≤ 10 := by
            have : (1000 : ℝ) ≤ Real.exp 10 := by
              have : (2 : ℝ) ^ 10 ≤ (Real.exp 1) ^ 10 :=
                pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 10
              rw [← Real.exp_nat_mul] at this; norm_num at this ⊢; linarith
            have := Real.log_le_log (by norm_num) this; rwa [Real.log_exp] at this
          push_cast; linarith
        calc 1000 * L ^ 13 = Real.exp (Real.log (1000 * L ^ 13)) := (Real.exp_log (by positivity)).symm
          _ ≤ Real.exp ((1 / 24 : ℝ) * L ^ ((9 : ℝ) / 10)) := Real.exp_le_exp.mpr h1
          _ ≤ (Y : ℝ) := hY_lo
      linarith
    rw [le_div_iff₀ (by positivity)]
    calc 10 * (k : ℝ) * (Y : ℝ) * (3 * L ^ 12)
        = (30 * (k : ℝ) * L ^ 12) * (Y : ℝ) := by ring
      _ ≤ (Y : ℝ) * (Y : ℝ) := mul_le_mul_of_nonneg_right h30kL hY_Rpos.le
      _ ≤ (M₁ : ℝ) := hY2
  calc ‖∑ x ∈ Ioc M₁ N₁, e (β / (x : ℝ))‖
      ≤ 4 * (M₁ : ℝ) * ((4 * (s : ℝ)) ^ (5 * k) * (Y : ℝ) ^ ((-1 + δ) / (2 * (s : ℝ))) + 1 / (Y : ℝ)) +
          10 * (k : ℝ) * (Y : ℝ) := hvk
    _ ≤ 4 * (M₁ : ℝ) * (1 / (12 * L ^ 12) + 1 / (12 * L ^ 12)) + (M₁ : ℝ) / (3 * L ^ 12) :=
        add_le_add (mul_le_mul_of_nonneg_left (add_le_add hmain_le h1Y_le) (by positivity)) h10kY_le
    _ = (M₁ : ℝ) / L ^ 12 := by ring

/- ### Part 3: Vaughan's identity and dyadic prime exponential sum bound -/

/-- Pointwise Vaughan identity for `m > V`:
    `Λ m = (∑ d ∈ m.divisors with d ≤ U, μ d * log (m / d))
         - (∑ k ∈ m.divisors with k ≤ U * V, (∑ d ∈ k.divisors with d ≤ U ∧ k / d ≤ V, μ d * Λ (k / d)))
         - (∑ a ∈ m.divisors with U < a ∧ V < m / a, (∑ d ∈ a.divisors with d ≤ U, μ d) * Λ (m / a))`. -/
private lemma vaughan_pointwise {U V m : ℕ} (hU : 1 ≤ U) (_hV : 1 ≤ V) (hm : V < m) :
    Λ m =
      (∑ d ∈ m.divisors.filter (· ≤ U), (μ d : ℝ) * Real.log ((m / d : ℕ) : ℝ)) -
      (∑ k ∈ m.divisors.filter (· ≤ U * V),
        ∑ d ∈ k.divisors.filter (fun d => d ≤ U ∧ k / d ≤ V), (μ d : ℝ) * Λ (k / d)) -
      (∑ a ∈ m.divisors.filter (fun a => U < a ∧ V < m / a),
        (∑ d ∈ a.divisors.filter (· ≤ U), (μ d : ℝ)) * Λ (m / a)) := by
  -- Use ArithmeticFunction convolution identity:
  -- μ_≤U * log - (μ_≤U * Λ_≤V) * ζ - (μ_≤U * ζ - 1) * Λ_>V = Λ - Λ_≤V = Λ (since m > V)!
  let μU : ArithmeticFunction ℝ :=
    ⟨fun d => if d ≤ U then (μ d : ℝ) else 0, by simp [ArithmeticFunction.map_zero]⟩
  let ΛV : ArithmeticFunction ℝ :=
    ⟨fun d => if d ≤ V then Λ d else 0, by simp [ArithmeticFunction.map_zero]⟩
  let Λhi : ArithmeticFunction ℝ :=
    ⟨fun d => if V < d then Λ d else 0, by simp⟩
  have hΛ_split : Λ = ΛV + Λhi := by
    ext n
    change Λ n = (if n ≤ V then Λ n else 0) + (if V < n then Λ n else 0)
    by_cases h : n ≤ V
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]
  have hconv : Λhi = μU * ArithmeticFunction.log - (μU * ΛV) * (ζ : ArithmeticFunction ℝ) -
      (μU * (ζ : ArithmeticFunction ℝ) - 1) * Λhi := by
    have h1 : ArithmeticFunction.log = Λ * (ζ : ArithmeticFunction ℝ) :=
      ArithmeticFunction.vonMangoldt_mul_zeta.symm
    rw [h1, hΛ_split]
    ring
  have hm_eq := congrArg (fun (F : ArithmeticFunction ℝ) => F m) hconv
  have hΛhi_m : Λhi m = Λ m := by dsimp [Λhi]; simp [hm]
  rw [hΛhi_m] at hm_eq
  change Λ m = (μU * ArithmeticFunction.log) m - ((μU * ΛV) * (ζ : ArithmeticFunction ℝ)) m -
      ((μU * (ζ : ArithmeticFunction ℝ) - 1) * Λhi) m at hm_eq
  rw [hm_eq]
  -- Match each of the 3 terms!
  have hT1 : (μU * ArithmeticFunction.log) m =
      ∑ d ∈ m.divisors.filter (· ≤ U), (μ d : ℝ) * Real.log ((m / d : ℕ) : ℝ) := by
    rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (f := fun d q => μU d * ArithmeticFunction.log q)]
    have hfilt : ∑ d ∈ m.divisors, μU d * ArithmeticFunction.log (m / d) =
        ∑ d ∈ m.divisors.filter (· ≤ U), μU d * ArithmeticFunction.log (m / d) := by
      symm; refine Finset.sum_filter_of_ne fun d _ hne => ?_
      by_contra hgt
      exact hne (by change (if d ≤ U then (μ d : ℝ) else 0) * _ = 0; simp [hgt])
    rw [hfilt]
    refine sum_congr rfl fun d hd => ?_
    have hdU : d ≤ U := (mem_filter.mp hd).2
    change (if d ≤ U then (μ d : ℝ) else 0) * ArithmeticFunction.log (m / d) = _
    simp [hdU, ArithmeticFunction.log_apply]
  have hT2 : ((μU * ΛV) * (ζ : ArithmeticFunction ℝ)) m =
      ∑ k ∈ m.divisors.filter (· ≤ U * V),
        ∑ d ∈ k.divisors.filter (fun d => d ≤ U ∧ k / d ≤ V), (μ d : ℝ) * Λ (k / d) := by
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    have hzero : ∀ k ∈ m.divisors, U * V < k → (μU * ΛV) k = 0 := by
      intro k _ hkUV
      rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (f := fun d q => μU d * ΛV q)]
      refine Finset.sum_eq_zero fun d hd => ?_
      have hdk : d ∣ k := (Nat.mem_divisors.mp hd).1
      change (if d ≤ U then (μ d : ℝ) else 0) * (if k / d ≤ V then Λ (k / d) else 0) = 0
      split_ifs with h1 h2
      · have hprod : d * (k / d) = k := Nat.mul_div_cancel' hdk
        have : d * (k / d) ≤ U * V := Nat.mul_le_mul h1 h2
        omega
      · simp
      · simp
      · simp
    rw [← Finset.sum_filter_of_ne (p := fun k => k ≤ U * V) (fun k hk hne => by
      by_contra hlt; exact hne (hzero k hk (lt_of_not_ge hlt)))]
    refine sum_congr rfl fun k _ => ?_
    rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (f := fun d q => μU d * ΛV q)]
    have hfilt : ∑ d ∈ k.divisors, μU d * ΛV (k / d) =
        ∑ d ∈ k.divisors.filter (fun d => d ≤ U ∧ k / d ≤ V), μU d * ΛV (k / d) := by
      symm; refine Finset.sum_filter_of_ne fun d _ hne => ?_
      by_contra hnot
      change (if d ≤ U then (μ d : ℝ) else 0) * (if k / d ≤ V then Λ (k / d) else 0) ≠ 0 at hne
      by_cases h1 : d ≤ U
      · have h2 : ¬ k / d ≤ V := fun h2 => hnot ⟨h1, h2⟩
        exact hne (by simp [h1, h2])
      · exact hne (by simp [h1])
    rw [hfilt]
    refine sum_congr rfl fun d hd => ?_
    have ⟨h1, h2⟩ := (mem_filter.mp hd).2
    change (if d ≤ U then (μ d : ℝ) else 0) * (if k / d ≤ V then Λ (k / d) else 0) = _
    simp [h1, h2]
  have hT3 : ((μU * (ζ : ArithmeticFunction ℝ) - 1) * Λhi) m =
      ∑ a ∈ m.divisors.filter (fun a => U < a ∧ V < m / a),
        (∑ d ∈ a.divisors.filter (· ≤ U), (μ d : ℝ)) * Λ (m / a) := by
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (f := fun a b => (μU * (ζ : ArithmeticFunction ℝ) - 1) a * Λhi b)]
    have hvanish : ∀ a ∈ m.divisors, a ≤ U → (μU * (ζ : ArithmeticFunction ℝ) - 1) a = 0 := by
      intro a ha haU
      have ha_pos : a ≠ 0 := by
        intro h0; rw [h0] at ha; exact (Nat.mem_divisors.mp ha).2 (zero_dvd_iff.mp (Nat.mem_divisors.mp ha).1)
      change (μU * (ζ : ArithmeticFunction ℝ)) a - (1 : ArithmeticFunction ℝ) a = 0
      rw [ArithmeticFunction.coe_mul_zeta_apply]
      have hsum_eq : ∑ d ∈ a.divisors, μU d = ∑ d ∈ a.divisors, (μ d : ℝ) := by
        refine sum_congr rfl fun d hd => ?_
        have hda : d ≤ a := Nat.le_of_dvd (Nat.pos_of_ne_zero ha_pos) (Nat.mem_divisors.mp hd).1
        change (if d ≤ U then (μ d : ℝ) else 0) = (μ d : ℝ)
        simp [le_trans hda haU]
      rw [hsum_eq]
      have hmob : ∑ d ∈ a.divisors, (μ d : ℝ) = (1 : ArithmeticFunction ℝ) a := by
        have h : ((μ : ArithmeticFunction ℤ) * (ζ : ArithmeticFunction ℤ)) a = (1 : ArithmeticFunction ℤ) a :=
          congrArg (fun F => F a) ArithmeticFunction.moebius_mul_coe_zeta
        rw [ArithmeticFunction.coe_mul_zeta_apply] at h
        have hR : ∑ d ∈ a.divisors, (μ d : ℝ) = (((1 : ArithmeticFunction ℤ) a : ℤ) : ℝ) := by
          exact_mod_cast h
        rw [hR]
        by_cases ha1 : a = 1
        · subst ha1; simp
        · simp [ArithmeticFunction.one_apply_ne ha1]
      rw [hmob, sub_self]
    have hfilt_eq : ∑ a ∈ m.divisors, (μU * (ζ : ArithmeticFunction ℝ) - 1) a * Λhi (m / a) =
        ∑ a ∈ m.divisors.filter (fun a => U < a ∧ V < m / a),
          (μU * (ζ : ArithmeticFunction ℝ) - 1) a * Λhi (m / a) := by
      symm
      refine Finset.sum_filter_of_ne fun a ha hne => ?_
      constructor
      · by_contra hle; exact hne (by rw [hvanish a ha (not_lt.mp hle), zero_mul])
      · by_contra hle; exact hne (by change _ * (if V < m / a then Λ (m / a) else 0) = 0; simp [hle])
    rw [hfilt_eq]
    refine sum_congr rfl fun a ha => ?_
    obtain ⟨ha_div, haU, hmaV⟩ := mem_filter.mp ha
    have hΛ_eq : Λhi (m / a) = Λ (m / a) := by
      change (if V < m / a then Λ (m / a) else 0) = Λ (m / a); simp [hmaV]
    have ha_ne1 : a ≠ 1 := by omega
    have hcoeff : (μU * (ζ : ArithmeticFunction ℝ) - 1) a =
        ∑ d ∈ a.divisors.filter (· ≤ U), (μ d : ℝ) := by
      change (μU * (ζ : ArithmeticFunction ℝ)) a - (1 : ArithmeticFunction ℝ) a = _
      rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply_ne ha_ne1, sub_zero]
      have : ∑ d ∈ a.divisors, μU d = ∑ d ∈ a.divisors.filter (· ≤ U), μU d := by
        symm; refine Finset.sum_filter_of_ne fun d _ hne => ?_
        by_contra hgt; exact hne (by change (if d ≤ U then (μ d : ℝ) else 0) = 0; simp [hgt])
      rw [this]
      exact sum_congr rfl fun d hd => by change (if d ≤ U then (μ d : ℝ) else 0) = _; simp [(mem_filter.mp hd).2]
    rw [hΛ_eq, hcoeff]
  rw [hT1, hT2, hT3]

set_option maxHeartbeats 800000 in
/-- Single dyadic block bound for Vaughan Type II sums (`S3`) via Cauchy-Schwarz. -/
private lemma vaughan_S3_dyadic_bound
    {n P N U A A' : ℕ} {α₀ : ℝ}
    (hn1000 : 1000 ≤ n)
    (hL1000 : 1000 ≤ Real.log (n : ℝ))
    (hL9_log : (1 / 24 : ℝ) * (Real.log (n : ℝ)) ^ ((9 : ℝ) / 10) ≥ 10 * Real.log (Real.log (n : ℝ)) + 20)
    (hunif : ∀ (M₁ N₁ : ℕ) (α : ℝ),
      Real.exp ((1 / 8 : ℝ) * (Real.log (n : ℝ)) ^ ((9 : ℝ) / 10)) ≤ (M₁ : ℝ) →
      (M₁ : ℝ) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 100) →
      M₁ ≤ N₁ → N₁ ≤ 2 * M₁ →
      (n : ℝ) ^ ((1 : ℝ) / 2) ≤ |α| → |α| ≤ 2 * (n : ℝ) →
      ‖∑ x ∈ Ioc M₁ N₁, e (α / (x : ℝ))‖ ≤ (M₁ : ℝ) / (Real.log (n : ℝ)) ^ 12)
    (hP_ge_exp : Real.exp ((1 / 2 : ℝ) * (Real.log (n : ℝ)) ^ ((9 : ℝ) / 10)) ≤ (P : ℝ))
    (hP_hi : (P : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 100))
    (hN2P : N ≤ 2 * P)
    (hlog2P_le_L : Real.log ((2 * P : ℕ) : ℝ) ≤ Real.log (n : ℝ))
    (hU_pos : 1 ≤ U)
    (hU_ge_half : (1 / 2 : ℝ) * (P : ℝ) ^ ((1 : ℝ) / 3) ≤ (U : ℝ))
    (hU_ge_exp : Real.exp ((1 / 8 : ℝ) * (Real.log (n : ℝ)) ^ ((9 : ℝ) / 10)) ≤ (U : ℝ))
    (hα₀_lo : (n : ℝ) ≤ α₀) (hα₀_hi : α₀ ≤ 2 * (n : ℝ))
    (hUA : U ≤ A) (hAA' : A < A') (hA'2A : A' ≤ 2 * A) (hA'NU : A' ≤ N / U) :
    ‖∑ a ∈ Ioc A A', ((∑ d ∈ a.divisors.filter (· ≤ U), (μ d : ℝ) : ℝ) : ℂ) *
      ∑ b ∈ Ioc (max U (P / a)) (N / a), (Λ b : ℂ) * e (α₀ / ((a * b : ℕ) : ℝ))‖ ≤
      3 * (P : ℝ) / (Real.log (n : ℝ)) ^ 3 := by
  let L : ℝ := Real.log (n : ℝ)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hA_pos : 1 ≤ A := by omega
  have hA_Rpos : (0 : ℝ) < A := by exact_mod_cast hA_pos
  have hPpos : (0 : ℝ) < P := lt_of_lt_of_le (Real.exp_pos _) hP_ge_exp
  let w : ℕ → ℝ := fun a => ∑ d ∈ a.divisors.filter (· ≤ U), (μ d : ℝ)
  have hw_le_tau : ∀ a : ℕ, |w a| ≤ (a.divisors.card : ℝ) := fun a => by
    dsimp only [w]
    calc |∑ d ∈ a.divisors.filter (· ≤ U), (μ d : ℝ)|
        ≤ ∑ d ∈ a.divisors.filter (· ≤ U), |(μ d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ a.divisors.filter (· ≤ U), (1 : ℝ) := sum_le_sum fun d _ => abs_moebius_le_one d
      _ = ((a.divisors.filter (· ≤ U)).card : ℝ) := by simp
      _ ≤ (a.divisors.card : ℝ) := by exact_mod_cast card_le_card (filter_subset _ _)
  -- Step 1: Cauchy-Schwarz in a ∈ Ioc A A'
  have hcs : ‖∑ a ∈ Ioc A A', (w a : ℂ) *
        ∑ b ∈ Ioc (max U (P / a)) (N / a), (Λ b : ℂ) * e (α₀ / ((a * b : ℕ) : ℝ))‖ ^ 2 ≤
      (∑ a ∈ Ioc A A', (w a) ^ 2) *
      (∑ a ∈ Ioc A A', ‖∑ b ∈ Ioc (max U (P / a)) (N / a), (Λ b : ℂ) * e (α₀ / ((a * b : ℕ) : ℝ))‖ ^ 2) := by
    have htri : ‖∑ a ∈ Ioc A A', (w a : ℂ) *
          ∑ b ∈ Ioc (max U (P / a)) (N / a), (Λ b : ℂ) * e (α₀ / ((a * b : ℕ) : ℝ))‖ ≤
        ∑ a ∈ Ioc A A', |w a| *
          ‖∑ b ∈ Ioc (max U (P / a)) (N / a), (Λ b : ℂ) * e (α₀ / ((a * b : ℕ) : ℝ))‖ := by
      calc ‖∑ a ∈ Ioc A A', _‖ ≤ ∑ a ∈ Ioc A A', ‖_‖ := norm_sum_le _ _
        _ = _ := sum_congr rfl fun a _ => by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hcs' := Finset.sum_mul_sq_le_sq_mul_sq (Ioc A A') (fun a => |w a|)
      (fun a => ‖∑ b ∈ Ioc (max U (P / a)) (N / a), (Λ b : ℂ) * e (α₀ / ((a * b : ℕ) : ℝ))‖)
    simp_rw [sq_abs] at hcs'
    exact hsq.trans hcs'
  -- Step 2: ∑ (w a)^2 ≤ 16 * A * L^3
  have hw_sq : ∑ a ∈ Ioc A A', (w a) ^ 2 ≤ 16 * (A : ℝ) * L ^ 3 := by
    have hA'2P : A' ≤ 2 * P := le_trans hA'NU (le_trans (Nat.div_le_self N U) hN2P)
    calc ∑ a ∈ Ioc A A', (w a) ^ 2
        ≤ ∑ a ∈ Ioc A A', (a.divisors.card : ℝ) ^ 2 :=
          sum_le_sum fun a _ => by
            rw [← sq_abs (w a)]; exact pow_le_pow_left₀ (abs_nonneg _) (hw_le_tau a) 2
      _ ≤ ∑ a ∈ Icc 1 A', (a.divisors.card : ℝ) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (Ioc_subset_Icc_self.trans (Icc_subset_Icc_left (by omega)))
            (fun _ _ _ => sq_nonneg _)
      _ ≤ (A' : ℝ) * (1 + Real.log (A' : ℝ)) ^ 3 := sum_tau_sq_le (by omega)
      _ ≤ (2 * (A : ℝ)) * (2 * L) ^ 3 := by
          have hlogA' : 1 + Real.log (A' : ℝ) ≤ 2 * L := by
            have h1 : Real.log (A' : ℝ) ≤ Real.log ((2 * P : ℕ) : ℝ) :=
              Real.log_le_log (by exact_mod_cast (by omega : 0 < A')) (by exact_mod_cast hA'2P)
            linarith [h1.trans hlog2P_le_L]
          exact mul_le_mul (by exact_mod_cast hA'2A)
            (pow_le_pow_left₀ (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ A' by exact_mod_cast (by omega : 1 ≤ A'))]) hlogA' 3)
            (by positivity) (by positivity)
      _ = 16 * (A : ℝ) * L ^ 3 := by ring
  -- Step 3: Expand ∑_a ‖∑_b‖^2
  let B_max : ℕ := N / A
  have hB_le : (B_max : ℝ) ≤ 2 * (P : ℝ) / (A : ℝ) := by
    have h1 : B_max * A ≤ 2 * P := le_trans (Nat.div_mul_le_self N A) hN2P
    rw [le_div_iff₀ hA_Rpos]; exact_mod_cast h1
  have hB_le_2P : B_max ≤ 2 * P := le_trans (Nat.div_le_self N A) hN2P
  have hexp_sq : (∑ a ∈ Ioc A A',
        ‖∑ b ∈ Ioc (max U (P / a)) (N / a), (Λ b : ℂ) * e (α₀ / ((a * b : ℕ) : ℝ))‖ ^ 2) ≤
      ∑ b₁ ∈ Icc 1 B_max, ∑ b₂ ∈ Icc 1 B_max,
        Λ b₁ * Λ b₂ *
          ‖∑ a ∈ (Ioc A A').filter (fun a => max U (P / a) < b₁ ∧ b₁ ≤ N / a ∧ max U (P / a) < b₂ ∧ b₂ ≤ N / a),
            e ((α₀ * ((b₂ : ℝ) - (b₁ : ℝ)) / ((b₁ : ℝ) * (b₂ : ℝ))) / (a : ℝ))‖ := by
    have hC_eq : ((∑ a ∈ Ioc A A',
          ‖∑ b ∈ Ioc (max U (P / a)) (N / a), (Λ b : ℂ) * e (α₀ / ((a * b : ℕ) : ℝ))‖ ^ 2 : ℝ) : ℂ) =
        ∑ b₁ ∈ Icc 1 B_max, ∑ b₂ ∈ Icc 1 B_max,
          ((Λ b₁ * Λ b₂ : ℝ) : ℂ) *
            ∑ a ∈ (Ioc A A').filter (fun a => max U (P / a) < b₁ ∧ b₁ ≤ N / a ∧ max U (P / a) < b₂ ∧ b₂ ≤ N / a),
              e ((α₀ * ((b₂ : ℝ) - (b₁ : ℝ)) / ((b₁ : ℝ) * (b₂ : ℝ))) / (a : ℝ)) := by
      rw [Complex.ofReal_sum]
      have hnorm_sq : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := fun z => by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp_rw [hnorm_sq]
      have hterm_a : ∀ a ∈ Ioc A A',
          (∑ b ∈ Ioc (max U (P / a)) (N / a), (Λ b : ℂ) * e (α₀ / ((a * b : ℕ) : ℝ))) *
          star (∑ b ∈ Ioc (max U (P / a)) (N / a), (Λ b : ℂ) * e (α₀ / ((a * b : ℕ) : ℝ))) =
          ∑ b₁ ∈ Icc 1 B_max, ∑ b₂ ∈ Icc 1 B_max,
            if max U (P / a) < b₁ ∧ b₁ ≤ N / a ∧ max U (P / a) < b₂ ∧ b₂ ≤ N / a then
              ((Λ b₁ * Λ b₂ : ℝ) : ℂ) *
                e ((α₀ * ((b₂ : ℝ) - (b₁ : ℝ)) / ((b₁ : ℝ) * (b₂ : ℝ))) / (a : ℝ))
            else 0 := by
        intro a ha
        have haA : A < a := (mem_Ioc.mp ha).1
        have hsub : Ioc (max U (P / a)) (N / a) ⊆ Icc 1 B_max := by
          intro b hb
          have hb1 := (mem_Ioc.mp hb).1; have hb2 := (mem_Ioc.mp hb).2
          exact mem_Icc.mpr ⟨by have := le_max_left U (P / a); omega,
            le_trans hb2 (Nat.div_le_div_left haA.le (by omega))⟩
        rw [star_sum, Finset.sum_mul_sum]
        have h1 : ∀ f : ℕ → ℕ → ℂ,
            (∑ b₁ ∈ Ioc (max U (P / a)) (N / a), ∑ b₂ ∈ Ioc (max U (P / a)) (N / a), f b₁ b₂) =
            ∑ b₁ ∈ Icc 1 B_max, ∑ b₂ ∈ Icc 1 B_max,
              if max U (P / a) < b₁ ∧ b₁ ≤ N / a ∧ max U (P / a) < b₂ ∧ b₂ ≤ N / a then f b₁ b₂ else 0 := by
          intro f
          have hinner : ∀ b₁ ∈ Ioc (max U (P / a)) (N / a),
              ∑ b₂ ∈ Ioc (max U (P / a)) (N / a), f b₁ b₂ =
              ∑ b₂ ∈ Icc 1 B_max, if max U (P / a) < b₁ ∧ b₁ ≤ N / a ∧ max U (P / a) < b₂ ∧ b₂ ≤ N / a then f b₁ b₂ else 0 := by
            intro b₁ hb₁
            rw [← Finset.sum_filter]
            congr 1; ext b₂; simp only [mem_Ioc, mem_filter, mem_Icc] at hb₁ ⊢
            constructor
            · intro hb₂; exact ⟨⟨by have := le_max_left U (P / a); omega,
                le_trans hb₂.2 (Nat.div_le_div_left haA.le (by omega))⟩, hb₁.1, hb₁.2, hb₂.1, hb₂.2⟩
            · rintro ⟨_, _, _, h1, h2⟩; exact ⟨h1, h2⟩
          rw [sum_congr rfl hinner, ← Finset.sum_subset hsub]
          intro b₁ _ hb₁_not
          refine Finset.sum_eq_zero fun b₂ _ => ?_
          rw [mem_Ioc] at hb₁_not
          rw [if_neg (by tauto)]
        rw [h1]
        refine sum_congr rfl fun b₁ hb₁ => sum_congr rfl fun b₂ hb₂ => ?_
        split_ifs with hcond
        · have hb₁0 : (b₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (mem_Icc.mp hb₁).1; omega)
          have hb₂0 : (b₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (mem_Icc.mp hb₂).1; omega)
          have ha0 : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          rw [star_mul', e_star, Complex.star_def, Complex.conj_ofReal]
          have hexp : e (α₀ / ((a * b₁ : ℕ) : ℝ)) * e (-(α₀ / ((a * b₂ : ℕ) : ℝ))) =
              e ((α₀ * ((b₂ : ℝ) - (b₁ : ℝ)) / ((b₁ : ℝ) * (b₂ : ℝ))) / (a : ℝ)) := by
            rw [← e_add]; congr 1; push_cast; field_simp [ha0, hb₁0, hb₂0]; ring
          calc ((Λ b₁ : ℂ) * e (α₀ / ((a * b₁ : ℕ) : ℝ))) *
                ((Λ b₂ : ℂ) * e (-(α₀ / ((a * b₂ : ℕ) : ℝ))))
              = ((Λ b₁ : ℂ) * (Λ b₂ : ℂ)) *
                (e (α₀ / ((a * b₁ : ℕ) : ℝ)) * e (-(α₀ / ((a * b₂ : ℕ) : ℝ)))) := by ring
            _ = ((Λ b₁ * Λ b₂ : ℝ) : ℂ) * _ := by rw [hexp]; push_cast; rfl
        · rfl
      rw [sum_congr rfl hterm_a, Finset.sum_comm]
      refine sum_congr rfl fun b₁ _ => ?_
      rw [Finset.sum_comm]
      refine sum_congr rfl fun b₂ _ => ?_
      rw [← Finset.sum_filter, Finset.mul_sum]
    have hnorm := congrArg norm hC_eq
    rw [Complex.norm_real, Real.norm_of_nonneg (sum_nonneg fun _ _ => sq_nonneg _)] at hnorm
    rw [hnorm]
    calc ‖∑ b₁ ∈ Icc 1 B_max, ∑ b₂ ∈ Icc 1 B_max, _‖
        ≤ ∑ b₁ ∈ Icc 1 B_max, ‖∑ b₂ ∈ Icc 1 B_max, _‖ := norm_sum_le _ _
      _ ≤ ∑ b₁ ∈ Icc 1 B_max, ∑ b₂ ∈ Icc 1 B_max, ‖_‖ := sum_le_sum fun _ _ => norm_sum_le _ _
      _ = _ := sum_congr rfl fun b₁ _ => sum_congr rfl fun b₂ _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
            (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg)]
  -- Step 4: Filtered a-set is an interval Ioc M' N' ⊆ Ioc A A'
  have hfilt_interval : ∀ b₁ b₂ : ℕ, 1 ≤ b₁ → 1 ≤ b₂ →
      ∃ M' N' : ℕ, A ≤ M' ∧ M' ≤ N' ∧ N' ≤ A' ∧
        (Ioc A A').filter (fun a => max U (P / a) < b₁ ∧ b₁ ≤ N / a ∧ max U (P / a) < b₂ ∧ b₂ ≤ N / a) =
          Ioc M' N' := by
    intro b₁ b₂ hb₁ hb₂
    by_cases hU12 : U < b₁ ∧ U < b₂
    · let M' := min A' (max A (max (P / b₁) (P / b₂)))
      let N' := min A' (min (N / b₁) (N / b₂))
      by_cases hMN' : M' ≤ N'
      · refine ⟨M', N', by omega, hMN', by omega, ?_⟩
        ext a
        simp only [mem_filter, mem_Ioc]
        constructor
        · rintro ⟨⟨haA, haA'⟩, h1, h2, h3, h4⟩
          have hPa1 : P / a < b₁ := lt_of_le_of_lt (le_max_right _ _) h1
          have hPa2 : P / a < b₂ := lt_of_le_of_lt (le_max_right _ _) h3
          have hP_lt1 : P < a * b₁ := by
            have hdm := Nat.div_add_mod P a; have hrem := Nat.mod_lt P (by omega : 0 < a); nlinarith
          have hP_lt2 : P < a * b₂ := by
            have hdm := Nat.div_add_mod P a; have hrem := Nat.mod_lt P (by omega : 0 < a); nlinarith
          have hab1_le : a * b₁ ≤ N := by
            have := (Nat.le_div_iff_mul_le (by omega : 0 < a)).mp h2; linarith
          have hab2_le : a * b₂ ≤ N := by
            have := (Nat.le_div_iff_mul_le (by omega : 0 < a)).mp h4; linarith
          have hPb1 : P / b₁ < a := by
            by_contra hle; push Not at hle
            have := Nat.mul_le_mul_right b₁ hle; have := Nat.div_mul_le_self P b₁; omega
          have hPb2 : P / b₂ < a := by
            by_contra hle; push Not at hle
            have := Nat.mul_le_mul_right b₂ hle; have := Nat.div_mul_le_self P b₂; omega
          have hNb1 : a ≤ N / b₁ := (Nat.le_div_iff_mul_le (by omega : 0 < b₁)).mpr hab1_le
          have hNb2 : a ≤ N / b₂ := (Nat.le_div_iff_mul_le (by omega : 0 < b₂)).mpr hab2_le
          dsimp only [M', N']; omega
        · rintro ⟨haM', haN'⟩
          dsimp only [M', N'] at haM' haN'
          have haA : A < a := by omega
          have haA' : a ≤ A' := by omega
          have hPb1 : P / b₁ < a := by omega
          have hPb2 : P / b₂ < a := by omega
          have hNb1 : a ≤ N / b₁ := by omega
          have hNb2 : a ≤ N / b₂ := by omega
          have hP_lt1 : P < a * b₁ := by
            have hdm := Nat.div_add_mod P b₁; have hrem := Nat.mod_lt P (by omega : 0 < b₁); nlinarith
          have hP_lt2 : P < a * b₂ := by
            have hdm := Nat.div_add_mod P b₂; have hrem := Nat.mod_lt P (by omega : 0 < b₂); nlinarith
          have hab1_le : a * b₁ ≤ N := (Nat.le_div_iff_mul_le (by omega : 0 < b₁)).mp hNb1
          have hab2_le : a * b₂ ≤ N := (Nat.le_div_iff_mul_le (by omega : 0 < b₂)).mp hNb2
          have hPa1 : P / a < b₁ := by
            by_contra hle; push Not at hle
            have h1 := Nat.mul_le_mul_left a hle
            have h2 : a * (P / a) ≤ P := by rw [mul_comm]; exact Nat.div_mul_le_self P a
            omega
          have hPa2 : P / a < b₂ := by
            by_contra hle; push Not at hle
            have h1 := Nat.mul_le_mul_left a hle
            have h2 : a * (P / a) ≤ P := by rw [mul_comm]; exact Nat.div_mul_le_self P a
            omega
          refine ⟨⟨haA, haA'⟩, max_lt hU12.1 hPa1,
            (Nat.le_div_iff_mul_le (by omega : 0 < a)).mpr (by linarith),
            max_lt hU12.2 hPa2,
            (Nat.le_div_iff_mul_le (by omega : 0 < a)).mpr (by linarith)⟩
      · refine ⟨A, A, le_rfl, le_rfl, hAA'.le, ?_⟩
        rw [Finset.Ioc_self]
        ext a; simp only [mem_filter, mem_Ioc, notMem_empty, iff_false]
        rintro ⟨⟨haA, haA'⟩, h1, h2, h3, h4⟩
        have hPa1 : P / a < b₁ := lt_of_le_of_lt (le_max_right _ _) h1
        have hPa2 : P / a < b₂ := lt_of_le_of_lt (le_max_right _ _) h3
        have hP_lt1 : P < a * b₁ := by
          have hdm := Nat.div_add_mod P a; have hrem := Nat.mod_lt P (by omega : 0 < a); nlinarith
        have hP_lt2 : P < a * b₂ := by
          have hdm := Nat.div_add_mod P a; have hrem := Nat.mod_lt P (by omega : 0 < a); nlinarith
        have hab1_le : a * b₁ ≤ N := by
          have := (Nat.le_div_iff_mul_le (by omega : 0 < a)).mp h2; linarith
        have hab2_le : a * b₂ ≤ N := by
          have := (Nat.le_div_iff_mul_le (by omega : 0 < a)).mp h4; linarith
        have hPb1 : P / b₁ < a := by
          by_contra hle; push Not at hle
          have := Nat.mul_le_mul_right b₁ hle; have := Nat.div_mul_le_self P b₁; omega
        have hPb2 : P / b₂ < a := by
          by_contra hle; push Not at hle
          have := Nat.mul_le_mul_right b₂ hle; have := Nat.div_mul_le_self P b₂; omega
        have hNb1 : a ≤ N / b₁ := (Nat.le_div_iff_mul_le (by omega : 0 < b₁)).mpr hab1_le
        have hNb2 : a ≤ N / b₂ := (Nat.le_div_iff_mul_le (by omega : 0 < b₂)).mpr hab2_le
        dsimp only [M', N'] at hMN'; omega
    · refine ⟨A, A, le_rfl, le_rfl, hAA'.le, ?_⟩
      rw [Finset.Ioc_self]
      ext a; simp only [mem_filter, mem_Ioc, notMem_empty, iff_false]
      rintro ⟨_, h1, _, h3, _⟩
      exact hU12 ⟨lt_of_le_of_lt (le_max_left _ _) h1, lt_of_le_of_lt (le_max_left _ _) h3⟩
  -- Step 5: Bound each (b₁, b₂) term
  have hterm_bd : ∀ b₁ ∈ Icc 1 B_max, ∀ b₂ ∈ Icc 1 B_max,
      Λ b₁ * Λ b₂ *
        ‖∑ a ∈ (Ioc A A').filter (fun a => max U (P / a) < b₁ ∧ b₁ ≤ N / a ∧ max U (P / a) < b₂ ∧ b₂ ≤ N / a),
          e ((α₀ * ((b₂ : ℝ) - (b₁ : ℝ)) / ((b₁ : ℝ) * (b₂ : ℝ))) / (a : ℝ))‖ ≤
        if b₁ = b₂ then L ^ 2 * (A : ℝ) else L ^ 2 * (2 * (A : ℝ) / L ^ 12) := by
    intro b₁ hb₁ b₂ hb₂
    have hb₁1 := (mem_Icc.mp hb₁).1; have hb₁2 := (mem_Icc.mp hb₁).2
    have hb₂1 := (mem_Icc.mp hb₂).1; have hb₂2 := (mem_Icc.mp hb₂).2
    have hΛ1 : Λ b₁ ≤ L :=
      ArithmeticFunction.vonMangoldt_le_log.trans
        ((Real.log_le_log (by exact_mod_cast hb₁1) (by exact_mod_cast (le_trans hb₁2 hB_le_2P))).trans hlog2P_le_L)
    have hΛ2 : Λ b₂ ≤ L :=
      ArithmeticFunction.vonMangoldt_le_log.trans
        ((Real.log_le_log (by exact_mod_cast hb₂1) (by exact_mod_cast (le_trans hb₂2 hB_le_2P))).trans hlog2P_le_L)
    have hΛprod : Λ b₁ * Λ b₂ ≤ L ^ 2 := by
      rw [sq]; exact mul_le_mul hΛ1 hΛ2 ArithmeticFunction.vonMangoldt_nonneg hLpos.le
    obtain ⟨M', N', hAM', hMN', hN'A', hfilt_eq⟩ := hfilt_interval b₁ b₂ hb₁1 hb₂1
    rw [hfilt_eq]
    split_ifs with heq
    · have hcard : ‖∑ a ∈ Ioc M' N', e ((α₀ * ((b₂ : ℝ) - (b₁ : ℝ)) / ((b₁ : ℝ) * (b₂ : ℝ))) / (a : ℝ))‖ ≤ (A : ℝ) := by
        calc ‖∑ a ∈ Ioc M' N', e ((α₀ * ((b₂ : ℝ) - (b₁ : ℝ)) / ((b₁ : ℝ) * (b₂ : ℝ))) / (a : ℝ))‖
            ≤ ∑ a ∈ Ioc M' N', ‖e ((α₀ * ((b₂ : ℝ) - (b₁ : ℝ)) / ((b₁ : ℝ) * (b₂ : ℝ))) / (a : ℝ))‖ := norm_sum_le _ _
          _ = ((Ioc M' N').card : ℝ) := by simp [norm_e]
          _ ≤ (A : ℝ) := by rw [Nat.card_Ioc]; exact_mod_cast (by omega : N' - M' ≤ A)
      exact mul_le_mul hΛprod hcard (norm_nonneg _) (by positivity)
    · have hM'_lo : Real.exp ((1 / 8 : ℝ) * L ^ ((9 : ℝ) / 10)) ≤ (M' : ℝ) :=
        hU_ge_exp.trans (by exact_mod_cast (le_trans hUA hAM'))
      have hM'_hi : (M' : ℝ) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 100) := by
        have h1 : M' ≤ 2 * P := le_trans (le_trans hMN' hN'A') (le_trans hA'NU (le_trans (Nat.div_le_self N U) hN2P))
        have h2 : (M' : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast h1
        linarith [hP_hi]
      have hN'2M' : N' ≤ 2 * M' := by omega
      let α₁ : ℝ := α₀ * ((b₂ : ℝ) - (b₁ : ℝ)) / ((b₁ : ℝ) * (b₂ : ℝ))
      have hα₁_abs : |α₁| = α₀ * |(b₂ : ℝ) - (b₁ : ℝ)| / ((b₁ : ℝ) * (b₂ : ℝ)) := by
        dsimp only [α₁]
        rw [abs_div, abs_mul, abs_of_pos (lt_of_lt_of_le hnpos hα₀_lo),
          abs_of_pos (by positivity : (0 : ℝ) < (b₁ : ℝ) * (b₂ : ℝ))]
      have hdiff_ge1 : (1 : ℝ) ≤ |(b₂ : ℝ) - (b₁ : ℝ)| := by
        rcases lt_or_gt_of_ne heq with hlt | hgt
        · have hpos : (0 : ℝ) < (b₂ : ℝ) - (b₁ : ℝ) := by
            have : (b₁ : ℝ) < b₂ := by exact_mod_cast hlt
            linarith
          rw [abs_of_pos hpos]
          have : (b₁ : ℝ) + 1 ≤ b₂ := by exact_mod_cast hlt
          linarith
        · have hneg : (b₂ : ℝ) - (b₁ : ℝ) < 0 := by
            have : (b₂ : ℝ) < b₁ := by exact_mod_cast hgt
            linarith
          rw [abs_of_neg hneg]
          have : (b₂ : ℝ) + 1 ≤ b₁ := by exact_mod_cast hgt
          linarith
      have hdiff_le : |(b₂ : ℝ) - (b₁ : ℝ)| ≤ (b₁ : ℝ) * (b₂ : ℝ) := by
        have h1 : (1 : ℝ) ≤ b₁ := by exact_mod_cast hb₁1
        have h2 : (1 : ℝ) ≤ b₂ := by exact_mod_cast hb₂1
        rw [abs_le]; constructor <;> nlinarith
      have hα₁_lo : (n : ℝ) ^ ((1 : ℝ) / 2) ≤ |α₁| := by
        rw [hα₁_abs, le_div_iff₀ (by positivity)]
        have hb12 : (b₁ : ℝ) * (b₂ : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := by
          have h1 : (b₁ : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast (le_trans hb₁2 hB_le_2P)
          have h2 : (b₂ : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast (le_trans hb₂2 hB_le_2P)
          have hprod : (b₁ : ℝ) * (b₂ : ℝ) ≤ 4 * (n : ℝ) ^ ((2 : ℝ) / 100) := by
            have hP2 : (P : ℝ) ^ (2 : ℕ) ≤ (n : ℝ) ^ ((2 : ℝ) / 100) := by
              calc (P : ℝ) ^ (2 : ℕ) ≤ ((n : ℝ) ^ ((1 : ℝ) / 100)) ^ (2 : ℕ) :=
                    pow_le_pow_left₀ hPpos.le hP_hi 2
                _ = (n : ℝ) ^ ((2 : ℝ) / 100) := by
                    rw [← Real.rpow_natCast ((n : ℝ) ^ _), ← Real.rpow_mul hnpos.le]
                    congr 1; norm_num
            have h12 : (b₁ : ℝ) * (b₂ : ℝ) ≤ 4 * (P : ℝ) ^ (2 : ℕ) := by
              have hP0 := hPpos.le
              have hb10 : (0 : ℝ) ≤ b₁ := Nat.cast_nonneg _
              have hb20 : (0 : ℝ) ≤ b₂ := Nat.cast_nonneg _
              nlinarith [mul_le_mul h1 h2 hb20 (by linarith)]
            linarith
          have h4 : (4 : ℝ) ≤ (n : ℝ) ^ ((48 : ℝ) / 100) := by
            have : (4 : ℝ) ≤ (1000 : ℝ) ^ ((48 : ℝ) / 100) := by
              have hp : (4 : ℝ) ^ (100 : ℕ) ≤ (1000 : ℝ) ^ (48 : ℕ) := by norm_num
              have hr := Real.rpow_le_rpow (by positivity) hp (show (0 : ℝ) ≤ 1 / 100 by norm_num)
              rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
                ← Real.rpow_mul (by norm_num)] at hr
              norm_num at hr ⊢; exact hr
            exact this.trans (Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hn1000) (by norm_num))
          have hmul := mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hnpos.le ((2 : ℝ) / 100))
          rw [← Real.rpow_add hnpos] at hmul; norm_num at hmul; linarith
        have hsq : (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) = (n : ℝ) := by
          rw [← Real.rpow_add hnpos]; norm_num
        nlinarith [Real.rpow_nonneg hnpos.le ((1 : ℝ) / 2), hα₀_lo, hdiff_ge1]
      have hα₁_hi : |α₁| ≤ 2 * (n : ℝ) := by
        rw [hα₁_abs]
        have h1 : α₀ * |(b₂ : ℝ) - (b₁ : ℝ)| / ((b₁ : ℝ) * (b₂ : ℝ)) ≤ α₀ := by
          rw [div_le_iff₀ (by positivity)]
          exact mul_le_mul_of_nonneg_left hdiff_le (by linarith)
        exact h1.trans hα₀_hi
      have hcall := hunif M' N' α₁ hM'_lo hM'_hi hMN' hN'2M' hα₁_lo hα₁_hi
      have hM'_le_2A : (M' : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast (le_trans hMN' (le_trans hN'A' hA'2A))
      have hcall' : ‖∑ a ∈ Ioc M' N', e (α₁ / (a : ℝ))‖ ≤ 2 * (A : ℝ) / L ^ 12 :=
        hcall.trans (div_le_div_of_nonneg_right hM'_le_2A (by positivity))
      exact mul_le_mul hΛprod hcall' (norm_nonneg _) (by positivity)
  -- Step 6: Sum diagonal + off-diagonal and combine with hw_sq
  have hdouble_bd : (∑ a ∈ Ioc A A',
        ‖∑ b ∈ Ioc (max U (P / a)) (N / a), (Λ b : ℂ) * e (α₀ / ((a * b : ℕ) : ℝ))‖ ^ 2) ≤
      2 * (P : ℝ) * L ^ 2 + 8 * (P : ℝ) ^ 2 / ((A : ℝ) * L ^ 10) := by
    calc _ ≤ ∑ b₁ ∈ Icc 1 B_max, ∑ b₂ ∈ Icc 1 B_max,
            (if b₁ = b₂ then L ^ 2 * (A : ℝ) else L ^ 2 * (2 * (A : ℝ) / L ^ 12)) :=
          hexp_sq.trans (sum_le_sum fun b₁ hb₁ => sum_le_sum fun b₂ hb₂ => hterm_bd b₁ hb₁ b₂ hb₂)
      _ ≤ ∑ b₁ ∈ Icc 1 B_max, ∑ b₂ ∈ Icc 1 B_max,
            ((if b₁ = b₂ then L ^ 2 * (A : ℝ) else 0) + L ^ 2 * (2 * (A : ℝ) / L ^ 12)) := by
          refine sum_le_sum fun b₁ _ => sum_le_sum fun b₂ _ => ?_
          split_ifs <;> linarith [show 0 ≤ L ^ 2 * (2 * (A : ℝ) / L ^ 12) by positivity]
      _ = (B_max : ℝ) * (L ^ 2 * (A : ℝ)) + (B_max : ℝ) ^ 2 * (L ^ 2 * (2 * (A : ℝ) / L ^ 12)) := by
          simp_rw [Finset.sum_add_distrib]
          have hcardB : (Icc 1 B_max).card = B_max := by
            rw [Nat.card_Icc]; exact Nat.add_sub_cancel B_max 1
          have hdiag : ∑ b₁ ∈ Icc 1 B_max, ∑ b₂ ∈ Icc 1 B_max, (if b₁ = b₂ then L ^ 2 * (A : ℝ) else 0) =
              (B_max : ℝ) * (L ^ 2 * (A : ℝ)) := by
            have h1 : ∀ b₁ ∈ Icc 1 B_max,
                ∑ b₂ ∈ Icc 1 B_max, (if b₁ = b₂ then L ^ 2 * (A : ℝ) else 0) = L ^ 2 * (A : ℝ) :=
              fun b₁ hb₁ => by simp [hb₁]
            rw [sum_congr rfl h1, Finset.sum_const, hcardB, nsmul_eq_mul]
          have hoff : ∑ _b₁ ∈ Icc 1 B_max, ∑ _b₂ ∈ Icc 1 B_max, (L ^ 2 * (2 * (A : ℝ) / L ^ 12)) =
              (B_max : ℝ) ^ 2 * (L ^ 2 * (2 * (A : ℝ) / L ^ 12)) := by
            simp only [Finset.sum_const, hcardB, nsmul_eq_mul]
            ring
          rw [hdiag, hoff]
      _ ≤ (2 * (P : ℝ) / (A : ℝ)) * (L ^ 2 * (A : ℝ)) +
          (2 * (P : ℝ) / (A : ℝ)) ^ 2 * (L ^ 2 * (2 * (A : ℝ) / L ^ 12)) := by
          refine add_le_add (mul_le_mul_of_nonneg_right hB_le (by positivity))
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hB_le 2) (by positivity))
      _ = 2 * (P : ℝ) * L ^ 2 + 8 * (P : ℝ) ^ 2 / ((A : ℝ) * L ^ 10) := by
          field_simp [hA_Rpos.ne', hLpos.ne']; ring
  have hsq_final : ‖∑ a ∈ Ioc A A', (w a : ℂ) *
        ∑ b ∈ Ioc (max U (P / a)) (N / a), (Λ b : ℂ) * e (α₀ / ((a * b : ℕ) : ℝ))‖ ^ 2 ≤
      (3 * (P : ℝ) / L ^ 3) ^ 2 := by
    have hdiag_le : 32 * (P : ℝ) * (A : ℝ) * L ^ 5 ≤ (P : ℝ) ^ 2 / L ^ 6 := by
      have hAU : (A : ℝ) ≤ 4 * (P : ℝ) ^ ((2 : ℝ) / 3) := by
        have h1 : (A : ℝ) ≤ (2 * (P : ℝ)) / (U : ℝ) := by
          have hA_le_NU : A * U ≤ 2 * P := le_trans (Nat.mul_le_mul_right U (le_trans hAA'.le hA'NU))
            (le_trans (Nat.div_mul_le_self N U) hN2P)
          rw [le_div_iff₀ (by exact_mod_cast hU_pos)]; exact_mod_cast hA_le_NU
        have h2 : (2 * (P : ℝ)) / (U : ℝ) ≤ (2 * (P : ℝ)) / ((1 / 2 : ℝ) * (P : ℝ) ^ ((1 : ℝ) / 3)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hU_ge_half
        have h3 : (2 * (P : ℝ)) / ((1 / 2 : ℝ) * (P : ℝ) ^ ((1 : ℝ) / 3)) = 4 * (P : ℝ) ^ ((2 : ℝ) / 3) := by
          have hPsplit : (P : ℝ) = (P : ℝ) ^ ((2 : ℝ) / 3) * (P : ℝ) ^ ((1 : ℝ) / 3) := by
            rw [← Real.rpow_add hPpos]; norm_num
          rw [div_eq_iff (by positivity)]
          calc 2 * (P : ℝ) = 2 * ((P : ℝ) ^ ((2 : ℝ) / 3) * (P : ℝ) ^ ((1 : ℝ) / 3)) := by rw [← hPsplit]
            _ = 4 * (P : ℝ) ^ ((2 : ℝ) / 3) * ((1 / 2 : ℝ) * (P : ℝ) ^ ((1 : ℝ) / 3)) := by ring
        linarith
      have hP13_ge : 128 * L ^ 11 ≤ (P : ℝ) ^ ((1 : ℝ) / 3) := by
        have h1 : Real.exp ((1 / 6 : ℝ) * L ^ ((9 : ℝ) / 10)) ≤ (P : ℝ) ^ ((1 : ℝ) / 3) := by
          have h := Real.rpow_le_rpow (Real.exp_pos _).le hP_ge_exp (show (0 : ℝ) ≤ 1 / 3 by norm_num)
          rw [← Real.exp_mul] at h
          have heq : (1 / 2 : ℝ) * L ^ ((9 : ℝ) / 10) * (1 / 3) = (1 / 6 : ℝ) * L ^ ((9 : ℝ) / 10) := by ring
          rwa [heq] at h
        have h2 : Real.log (128 * L ^ 11) ≤ (1 / 6 : ℝ) * L ^ ((9 : ℝ) / 10) := by
          rw [Real.log_mul (by norm_num) (pow_pos hLpos 11).ne', Real.log_pow]
          have hlog128 : Real.log 128 ≤ 10 := by
            have : (128 : ℝ) ≤ Real.exp 10 := by
              have : (2 : ℝ) ^ 10 ≤ (Real.exp 1) ^ 10 :=
                pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 10
              rw [← Real.exp_nat_mul] at this; norm_num at this ⊢; linarith
            have := Real.log_le_log (by norm_num) this; rwa [Real.log_exp] at this
          change (1 / 24 : ℝ) * L ^ ((9 : ℝ) / 10) ≥ 10 * Real.log L + 20 at hL9_log
          have hlogL_nn : 0 ≤ Real.log L := Real.log_nonneg (by change 1000 ≤ L at hL1000; linarith)
          push_cast; linarith [hL9_log, hlogL_nn]
        calc 128 * L ^ 11 = Real.exp (Real.log (128 * L ^ 11)) := (Real.exp_log (by positivity)).symm
          _ ≤ Real.exp ((1 / 6 : ℝ) * L ^ ((9 : ℝ) / 10)) := Real.exp_le_exp.mpr h2
          _ ≤ (P : ℝ) ^ ((1 : ℝ) / 3) := h1
      have hPsplit : (P : ℝ) ^ ((2 : ℝ) / 3) * (P : ℝ) ^ ((1 : ℝ) / 3) = (P : ℝ) := by
        rw [← Real.rpow_add hPpos]; norm_num
      rw [le_div_iff₀ (by positivity)]
      calc 32 * (P : ℝ) * (A : ℝ) * L ^ 5 * L ^ 6
          ≤ 32 * (P : ℝ) * (4 * (P : ℝ) ^ ((2 : ℝ) / 3)) * L ^ 5 * L ^ 6 := by gcongr
        _ = (P : ℝ) * (P : ℝ) ^ ((2 : ℝ) / 3) * (128 * L ^ 11) := by ring
        _ ≤ (P : ℝ) * (P : ℝ) ^ ((2 : ℝ) / 3) * (P : ℝ) ^ ((1 : ℝ) / 3) :=
            mul_le_mul_of_nonneg_left hP13_ge (by positivity)
        _ = (P : ℝ) ^ 2 := by rw [mul_assoc, hPsplit, sq]
    have hoff_le : 128 * (P : ℝ) ^ 2 / L ^ 7 ≤ 8 * (P : ℝ) ^ 2 / L ^ 6 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 128 * L ^ 6 ≤ 8 * L ^ 7 := by rw [pow_succ]; nlinarith [pow_pos hLpos 6]
      nlinarith [sq_nonneg (P : ℝ)]
    calc ‖_‖ ^ 2 ≤ (∑ a ∈ Ioc A A', (w a) ^ 2) *
          (∑ a ∈ Ioc A A', ‖∑ b ∈ Ioc (max U (P / a)) (N / a), (Λ b : ℂ) * e (α₀ / ((a * b : ℕ) : ℝ))‖ ^ 2) := hcs
      _ ≤ (16 * (A : ℝ) * L ^ 3) * (2 * (P : ℝ) * L ^ 2 + 8 * (P : ℝ) ^ 2 / ((A : ℝ) * L ^ 10)) :=
          mul_le_mul hw_sq hdouble_bd (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      _ = 32 * (P : ℝ) * (A : ℝ) * L ^ 5 + 128 * (P : ℝ) ^ 2 / L ^ 7 := by
          field_simp [hA_Rpos.ne', hLpos.ne']; ring
      _ ≤ (P : ℝ) ^ 2 / L ^ 6 + 8 * (P : ℝ) ^ 2 / L ^ 6 := add_le_add hdiag_le hoff_le
      _ = (3 * (P : ℝ) / L ^ 3) ^ 2 := by ring
  change ‖∑ a ∈ Ioc A A', (w a : ℂ) *
    ∑ b ∈ Ioc (max U (P / a)) (N / a), (Λ b : ℂ) * e (α₀ / ((a * b : ℕ) : ℝ))‖ ≤ 3 * (P : ℝ) / L ^ 3
  nlinarith [norm_nonneg (∑ a ∈ Ioc A A', (w a : ℂ) *
    ∑ b ∈ Ioc (max U (P / a)) (N / a), (Λ b : ℂ) * e (α₀ / ((a * b : ℕ) : ℝ))),
    show (0 : ℝ) ≤ 3 * (P : ℝ) / L ^ 3 by positivity]

set_option maxHeartbeats 800000 in
/-- Dyadic-block prime exponential sum bound via Vaughan's identity + `recip_sum_uniform`:
    for all sufficiently large `n`, for `h ∈ {1, 2}`, for every `P, N : ℕ` with
    `exp((log n)^(9/10)) / 2 ≤ P ≤ n^(1/100)` and `P < N ≤ 2 * P`,
    `‖∑ p ∈ (Ioc P N).filter Nat.Prime, (log p : ℂ) * e ((h * n : ℝ) / p)‖ ≤ 10 * P / (log n)^2`. -/
private lemma dyadic_prime_sum_bound :
    ∀ᶠ n : ℕ in atTop,
      ∀ (h P N : ℕ), 1 ≤ h → h ≤ 2 →
        Real.exp ((Real.log (n : ℝ)) ^ ((9 : ℝ) / 10)) / 2 ≤ (P : ℝ) →
        (P : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 100) →
        P < N → N ≤ 2 * P →
        ‖∑ p ∈ (Ioc P N).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e (((h * n : ℕ) : ℝ) / (p : ℝ))‖ ≤
          10 * (P : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
  obtain ⟨C_ψ, hC_ψ⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hL_top : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogL_o : Tendsto (fun L : ℝ => Real.log L / L ^ ((9 : ℝ) / 10)) atTop (nhds 0) :=
    isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 9 / 10) |>.tendsto_div_nhds_zero
  have hL_big : ∀ᶠ L : ℝ in atTop,
      1000 ≤ L ∧
      (1 / 24 : ℝ) * L ^ ((9 : ℝ) / 10) ≥ 10 * Real.log L + 20 ∧
      Real.exp ((1 / 12 : ℝ) * L ^ ((9 : ℝ) / 10)) ≥ 100 * (|C_ψ| + 1) * L ^ 10 ∧
      Real.exp ((1 / 12 : ℝ) * L ^ ((9 : ℝ) / 10)) ≥ 1000000 := by
    have h1 : ∀ᶠ L : ℝ in atTop, Real.log L / L ^ ((9 : ℝ) / 10) < 1 / 1000 :=
      hlogL_o.eventually (gt_mem_nhds (by norm_num))
    have h2 : ∀ᶠ L : ℝ in atTop, Real.log (100 * (|C_ψ| + 1)) + 1000 ≤ L ^ ((9 : ℝ) / 10) / 24 :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9 / 10)).eventually_ge_atTop
        (24 * (Real.log (100 * (|C_ψ| + 1)) + 1000)) |>.mono fun L hL => by linarith
    filter_upwards [eventually_ge_atTop (1000 : ℝ), h1, h2] with L hL1000 hlo hCbig
    have hLpos : 0 < L := by linarith
    have hL9_pos : 0 < L ^ ((9 : ℝ) / 10) := Real.rpow_pos_of_pos hLpos _
    have hlogL_lt : Real.log L < L ^ ((9 : ℝ) / 10) / 1000 := by
      have := (div_lt_iff₀ hL9_pos).mp hlo; linarith
    have hlog_bd : Real.log (100 * (|C_ψ| + 1) * L ^ 10) ≤ (1 / 12 : ℝ) * L ^ ((9 : ℝ) / 10) := by
      rw [Real.log_mul (by positivity) (pow_pos hLpos 10).ne', Real.log_pow]
      push_cast; linarith
    have hexp_C : 100 * (|C_ψ| + 1) * L ^ 10 ≤ Real.exp ((1 / 12 : ℝ) * L ^ ((9 : ℝ) / 10)) := by
      calc _ = Real.exp (Real.log (100 * (|C_ψ| + 1) * L ^ 10)) := (Real.exp_log (by positivity)).symm
        _ ≤ _ := Real.exp_le_exp.mpr hlog_bd
    have hexp_1e6 : (1000000 : ℝ) ≤ Real.exp ((1 / 12 : ℝ) * L ^ ((9 : ℝ) / 10)) := by
      have h1 : (1000000 : ℝ) ≤ 100 * (|C_ψ| + 1) * L ^ 10 := by
        have hL10 : (10000 : ℝ) ≤ L ^ 10 := by
          have : (1000 : ℝ) ^ 10 ≤ L ^ 10 := pow_le_pow_left₀ (by norm_num) hL1000 10
          norm_num at this; linarith
        nlinarith [abs_nonneg C_ψ]
      exact h1.trans hexp_C
    have hlogC_nn : 0 ≤ Real.log (100 * (|C_ψ| + 1)) :=
      Real.log_nonneg (by nlinarith [abs_nonneg C_ψ])
    exact ⟨hL1000, by linarith, hexp_C, hexp_1e6⟩
  filter_upwards [recip_sum_uniform, hL_top.eventually hL_big, eventually_ge_atTop 1000] with n hunif hLbig hn1000
  obtain ⟨hL1000, hL9_log, hL9_C, hL9_1e6⟩ := hLbig
  let L : ℝ := Real.log (n : ℝ)
  change 1000 ≤ L at hL1000
  change (1 / 24 : ℝ) * L ^ ((9 : ℝ) / 10) ≥ 10 * Real.log L + 20 at hL9_log
  change Real.exp ((1 / 12 : ℝ) * L ^ ((9 : ℝ) / 10)) ≥ 100 * (|C_ψ| + 1) * L ^ 10 at hL9_C
  change Real.exp ((1 / 12 : ℝ) * L ^ ((9 : ℝ) / 10)) ≥ 1000000 at hL9_1e6
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hLpos : 0 < L := by linarith
  have hlogL_pos : 0 < Real.log L := Real.log_pos (by linarith)
  intro h P N hh1 hh2 hP_lo hP_hi hPN hN2P
  -- Basic bounds on P, U, V
  have hP_ge_exp : Real.exp ((1 / 2 : ℝ) * L ^ ((9 : ℝ) / 10)) ≤ (P : ℝ) := by
    have hgap : (1 / 2 : ℝ) * L ^ ((9 : ℝ) / 10) + 1 ≤ L ^ ((9 : ℝ) / 10) := by linarith
    calc Real.exp ((1 / 2 : ℝ) * L ^ ((9 : ℝ) / 10))
        ≤ Real.exp ((1 / 2 : ℝ) * L ^ ((9 : ℝ) / 10) + 1) / 2 := by
          rw [Real.exp_add]
          have : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
          nlinarith [Real.exp_pos ((1 / 2 : ℝ) * L ^ ((9 : ℝ) / 10))]
      _ ≤ Real.exp (L ^ ((9 : ℝ) / 10)) / 2 := by gcongr
      _ ≤ (P : ℝ) := hP_lo
  have hP_ge_1e6 : 1000000 ≤ P := by
    have h1 : (1000000 : ℝ) ≤ (P : ℝ) := by
      calc (1000000 : ℝ) ≤ Real.exp ((1 / 12 : ℝ) * L ^ ((9 : ℝ) / 10)) := hL9_1e6
        _ ≤ Real.exp ((1 / 2 : ℝ) * L ^ ((9 : ℝ) / 10)) := Real.exp_le_exp.mpr (by linarith [Real.rpow_pos_of_pos hLpos ((9 : ℝ) / 10)])
        _ ≤ (P : ℝ) := hP_ge_exp
    exact_mod_cast h1
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hlog2P_le_L : Real.log ((2 * P : ℕ) : ℝ) ≤ L := by
    have h2P_le_n : ((2 * P : ℕ) : ℝ) ≤ (n : ℝ) := by
      have h1 : 2 * (n : ℝ) ^ ((1 : ℝ) / 100) ≤ (n : ℝ) := by
        have hn99 : (2 : ℝ) ≤ (n : ℝ) ^ ((99 : ℝ) / 100) := by
          have : (2 : ℝ) ≤ (1000 : ℝ) ^ ((99 : ℝ) / 100) := by
            have hp : (2 : ℝ) ^ (100 : ℕ) ≤ (1000 : ℝ) ^ (99 : ℕ) := by norm_num
            have hr := Real.rpow_le_rpow (by positivity) hp (show (0 : ℝ) ≤ 1 / 100 by norm_num)
            rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
              ← Real.rpow_mul (by norm_num)] at hr
            norm_num at hr; exact hr
          exact this.trans (Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hn1000) (by norm_num))
        have hmul := mul_le_mul_of_nonneg_right hn99 (Real.rpow_nonneg hnpos.le ((1 : ℝ) / 100))
        rw [← Real.rpow_add hnpos] at hmul; norm_num at hmul; exact hmul
      push_cast; linarith
    exact Real.log_le_log (by positivity) h2P_le_n
  -- Set U = V = ⌊P^(1/3)⌋
  let U : ℕ := Nat.floor ((P : ℝ) ^ ((1 : ℝ) / 3))
  have hU_le_P13 : (U : ℝ) ≤ (P : ℝ) ^ ((1 : ℝ) / 3) := Nat.floor_le (by positivity)
  have hU_ge_half : (1 / 2 : ℝ) * (P : ℝ) ^ ((1 : ℝ) / 3) ≤ (U : ℝ) := by
    have hP13_ge : (100 : ℝ) ≤ (P : ℝ) ^ ((1 : ℝ) / 3) := by
      have h1 : (100 : ℝ) ^ (3 : ℕ) ≤ (P : ℝ) := by norm_num; exact_mod_cast hP_ge_1e6
      have h2 := Real.rpow_le_rpow (by positivity) h1 (show (0 : ℝ) ≤ 1 / 3 by norm_num)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h2
      norm_num at h2; exact h2
    have hfl := Nat.lt_floor_add_one ((P : ℝ) ^ ((1 : ℝ) / 3))
    linarith
  have hU_ge_50 : 50 ≤ U := by
    have h1 : (50 : ℝ) ≤ (U : ℝ) := by
      have hP13_ge : (100 : ℝ) ≤ (P : ℝ) ^ ((1 : ℝ) / 3) := by
        have h1 : (100 : ℝ) ^ (3 : ℕ) ≤ (P : ℝ) := by norm_num; exact_mod_cast hP_ge_1e6
        have h2 := Real.rpow_le_rpow (by positivity) h1 (show (0 : ℝ) ≤ 1 / 3 by norm_num)
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h2
        norm_num at h2; exact h2
      linarith
    exact_mod_cast h1
  have hU_pos : 1 ≤ U := by omega
  have hU3_le_P : U ^ 3 ≤ P := by
    have h1 : (U : ℝ) ^ (3 : ℕ) ≤ (P : ℝ) := by
      calc (U : ℝ) ^ (3 : ℕ) ≤ ((P : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hU_le_P13 3
        _ = (P : ℝ) := by
            rw [← Real.rpow_natCast ((P : ℝ) ^ _), ← Real.rpow_mul hPpos.le]; norm_num
    exact_mod_cast h1
  have hU_lt_P : U < P := by
    have hU2 : U ≤ U ^ 2 := by rw [sq]; exact Nat.le_mul_self U
    have hU3 : U ^ 2 < U ^ 3 := by rw [pow_succ]; nlinarith
    omega
  have hU_ge_exp : Real.exp ((1 / 8 : ℝ) * L ^ ((9 : ℝ) / 10)) ≤ (U : ℝ) := by
    have hP13_exp : Real.exp ((1 / 6 : ℝ) * L ^ ((9 : ℝ) / 10)) ≤ (P : ℝ) ^ ((1 : ℝ) / 3) := by
      have h1 := Real.rpow_le_rpow (Real.exp_pos _).le hP_ge_exp (show (0 : ℝ) ≤ 1 / 3 by norm_num)
      rw [← Real.exp_mul] at h1
      have heq : (1 / 2 : ℝ) * L ^ ((9 : ℝ) / 10) * (1 / 3) = (1 / 6 : ℝ) * L ^ ((9 : ℝ) / 10) := by ring
      rwa [heq] at h1
    have hgap : (1 / 8 : ℝ) * L ^ ((9 : ℝ) / 10) + 1 ≤ (1 / 6 : ℝ) * L ^ ((9 : ℝ) / 10) := by linarith
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc Real.exp ((1 / 8 : ℝ) * L ^ ((9 : ℝ) / 10))
        ≤ (1 / 2 : ℝ) * Real.exp ((1 / 8 : ℝ) * L ^ ((9 : ℝ) / 10) + 1) := by
          rw [Real.exp_add]; nlinarith [Real.exp_pos ((1 / 8 : ℝ) * L ^ ((9 : ℝ) / 10))]
      _ ≤ (1 / 2 : ℝ) * Real.exp ((1 / 6 : ℝ) * L ^ ((9 : ℝ) / 10)) := by gcongr
      _ ≤ (1 / 2 : ℝ) * (P : ℝ) ^ ((1 : ℝ) / 3) := by gcongr
      _ ≤ (U : ℝ) := hU_ge_half
  -- Step 1: Prime vs Λ difference ≤ P / L^2
  let α₀ : ℝ := ((h * n : ℕ) : ℝ)
  have hh1R : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have hh2R : (h : ℝ) ≤ 2 := by exact_mod_cast hh2
  have hα₀_lo : (n : ℝ) ≤ α₀ := by dsimp [α₀]; push_cast; nlinarith
  have hα₀_hi : α₀ ≤ 2 * (n : ℝ) := by dsimp [α₀]; push_cast; nlinarith
  have hprime_vs_Λ :
      ‖(∑ p ∈ (Ioc P N).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e (α₀ / (p : ℝ))) -
       (∑ m ∈ Ioc P N, (Λ m : ℂ) * e (α₀ / (m : ℝ)))‖ ≤ (P : ℝ) / L ^ 2 := by
    have hsub : (∑ m ∈ Ioc P N, (Λ m : ℂ) * e (α₀ / (m : ℝ))) -
        (∑ p ∈ (Ioc P N).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e (α₀ / (p : ℝ))) =
        ∑ m ∈ (Ioc P N).filter (fun m => ¬ m.Prime), (Λ m : ℂ) * e (α₀ / (m : ℝ)) := by
      have hpart := (Finset.sum_filter_add_sum_filter_not (Ioc P N) Nat.Prime
        (fun m => (Λ m : ℂ) * e (α₀ / (m : ℝ)))).symm
      have hpr : ∑ p ∈ (Ioc P N).filter Nat.Prime, (Λ p : ℂ) * e (α₀ / (p : ℝ)) =
          ∑ p ∈ (Ioc P N).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e (α₀ / (p : ℝ)) :=
        sum_congr rfl fun p hp => by rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hp).2]
      rw [hpart, hpr]; ring
    rw [norm_sub_rev, hsub]
    have htri : ‖∑ m ∈ (Ioc P N).filter (fun m => ¬ m.Prime), (Λ m : ℂ) * e (α₀ / (m : ℝ))‖ ≤
        ψ (N : ℝ) - θ (N : ℝ) := by
      calc ‖∑ m ∈ (Ioc P N).filter (fun m => ¬ m.Prime), (Λ m : ℂ) * e (α₀ / (m : ℝ))‖
          ≤ ∑ m ∈ (Ioc P N).filter (fun m => ¬ m.Prime), ‖(Λ m : ℂ) * e (α₀ / (m : ℝ))‖ := norm_sum_le _ _
        _ = ∑ m ∈ (Ioc P N).filter (fun m => ¬ m.Prime), Λ m := by
            refine sum_congr rfl fun m _ => ?_
            rw [norm_mul, norm_e, mul_one, Complex.norm_real,
              Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        _ ≤ ∑ m ∈ (Ioc 0 N).filter (fun m => ¬ m.Prime), Λ m :=
            sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (Ioc_subset_Ioc_left (Nat.zero_le P)))
              (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
        _ = ψ (N : ℝ) - θ (N : ℝ) := by
            dsimp only [Chebyshev.psi, Chebyshev.theta]
            rw [Nat.floor_natCast]
            have hpart := (Finset.sum_filter_add_sum_filter_not (Ioc 0 N) Nat.Prime (fun m => Λ m)).symm
            have hpr : ∑ p ∈ (Ioc 0 N).filter Nat.Prime, Λ p = ∑ p ∈ (Ioc 0 N).filter Nat.Prime, Real.log p :=
              sum_congr rfl fun p hp => ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hp).2
            linarith
    have hψ_bd : ψ (N : ℝ) - θ (N : ℝ) ≤ (|C_ψ| + 1) * Real.sqrt ((2 * P : ℕ) : ℝ) := by
      have h1 := hC_ψ (N : ℝ)
      have hsq : Real.sqrt (N : ℝ) ≤ Real.sqrt ((2 * P : ℕ) : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hN2P)
      have hle : C_ψ * Real.sqrt (N : ℝ) ≤ (|C_ψ| + 1) * Real.sqrt ((2 * P : ℕ) : ℝ) := by
        calc C_ψ * Real.sqrt (N : ℝ) ≤ |C_ψ| * Real.sqrt (N : ℝ) :=
              mul_le_mul_of_nonneg_right (le_abs_self C_ψ) (Real.sqrt_nonneg _)
          _ ≤ (|C_ψ| + 1) * Real.sqrt ((2 * P : ℕ) : ℝ) :=
              mul_le_mul (by linarith) hsq (Real.sqrt_nonneg _) (by positivity)
      exact h1.trans hle
    have hsqrt_le : (|C_ψ| + 1) * Real.sqrt ((2 * P : ℕ) : ℝ) ≤ (P : ℝ) / L ^ 2 := by
      have h2P_sq : Real.sqrt ((2 * P : ℕ) : ℝ) ≤ 2 * (P : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow]
        push_cast
        rw [Real.mul_rpow (by norm_num) hPpos.le]
        have h212 : (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 := by
          conv_rhs => rw [← Real.rpow_one (2 : ℝ)]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        nlinarith [Real.rpow_nonneg hPpos.le ((1 : ℝ) / 2)]
      have hP12_ge : 2 * (|C_ψ| + 1) * L ^ 2 ≤ (P : ℝ) ^ ((1 : ℝ) / 2) := by
        have h1 : Real.exp ((1 / 4 : ℝ) * L ^ ((9 : ℝ) / 10)) ≤ (P : ℝ) ^ ((1 : ℝ) / 2) := by
          have h := Real.rpow_le_rpow (Real.exp_pos _).le hP_ge_exp (show (0 : ℝ) ≤ 1 / 2 by norm_num)
          rw [← Real.exp_mul] at h
          have heq : (1 / 2 : ℝ) * L ^ ((9 : ℝ) / 10) * (1 / 2) = (1 / 4 : ℝ) * L ^ ((9 : ℝ) / 10) := by ring
          rwa [heq] at h
        have h2 : 2 * (|C_ψ| + 1) * L ^ 2 ≤ 100 * (|C_ψ| + 1) * L ^ 10 := by
          have : L ^ 2 ≤ L ^ 10 := pow_le_pow_right₀ (by linarith) (by omega)
          nlinarith [abs_nonneg C_ψ]
        have h3 : Real.exp ((1 / 12 : ℝ) * L ^ ((9 : ℝ) / 10)) ≤ Real.exp ((1 / 4 : ℝ) * L ^ ((9 : ℝ) / 10)) :=
          Real.exp_le_exp.mpr (by linarith [Real.rpow_pos_of_pos hLpos ((9 : ℝ) / 10)])
        linarith
      rw [le_div_iff₀ (by positivity)]
      have hP_eq : (P : ℝ) ^ ((1 : ℝ) / 2) * (P : ℝ) ^ ((1 : ℝ) / 2) = (P : ℝ) := by
        rw [← Real.rpow_add hPpos]; norm_num
      calc (|C_ψ| + 1) * Real.sqrt ((2 * P : ℕ) : ℝ) * L ^ 2
          ≤ (|C_ψ| + 1) * (2 * (P : ℝ) ^ ((1 : ℝ) / 2)) * L ^ 2 := by gcongr
        _ = (2 * (|C_ψ| + 1) * L ^ 2) * (P : ℝ) ^ ((1 : ℝ) / 2) := by ring
        _ ≤ (P : ℝ) ^ ((1 : ℝ) / 2) * (P : ℝ) ^ ((1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right hP12_ge (Real.rpow_nonneg hPpos.le _)
        _ = (P : ℝ) := hP_eq
    exact (htri.trans hψ_bd).trans hsqrt_le
  -- Step 2: Apply Vaughan's identity on Ioc P N with U = V
  have hΛ_vaughan : (∑ m ∈ Ioc P N, (Λ m : ℂ) * e (α₀ / (m : ℝ))) =
      (∑ d ∈ Icc 1 U, ((μ d : ℝ) : ℂ) *
        ∑ b ∈ Ioc (P / d) (N / d), (Real.log (b : ℝ) : ℂ) * e (α₀ / ((d * b : ℕ) : ℝ))) -
      (∑ k ∈ Icc 1 (U * U),
        ((∑ d ∈ k.divisors.filter (fun d => d ≤ U ∧ k / d ≤ U), (μ d : ℝ) * Λ (k / d) : ℝ) : ℂ) *
        ∑ b ∈ Ioc (P / k) (N / k), e (α₀ / ((k * b : ℕ) : ℝ))) -
      (∑ a ∈ Ioc U (N / U),
        ((∑ d ∈ a.divisors.filter (· ≤ U), (μ d : ℝ) : ℝ) : ℂ) *
        ∑ b ∈ Ioc (max U (P / a)) (N / a), (Λ b : ℂ) * e (α₀ / ((a * b : ℕ) : ℝ))) := by
    have hpt : ∀ m ∈ Ioc P N, (Λ m : ℂ) * e (α₀ / (m : ℝ)) =
        (∑ d ∈ m.divisors.filter (· ≤ U), ((μ d : ℝ) : ℂ) * (Real.log ((m / d : ℕ) : ℝ) : ℂ) * e (α₀ / (m : ℝ))) -
        (∑ k ∈ m.divisors.filter (· ≤ U * U),
          ((∑ d ∈ k.divisors.filter (fun d => d ≤ U ∧ k / d ≤ U), (μ d : ℝ) * Λ (k / d) : ℝ) : ℂ) * e (α₀ / (m : ℝ))) -
        (∑ a ∈ m.divisors.filter (fun a => U < a ∧ U < m / a),
          ((∑ d ∈ a.divisors.filter (· ≤ U), (μ d : ℝ) : ℝ) : ℂ) * (Λ (m / a) : ℂ) * e (α₀ / (m : ℝ))) := by
      intro m hm
      have hmU : U < m := lt_trans hU_lt_P (mem_Ioc.mp hm).1
      have hv := vaughan_pointwise hU_pos hU_pos hmU
      rw [hv]
      push_cast
      rw [sub_mul, sub_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    rw [sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    -- Helper: double sum swap ∑_{m ∈ Ioc P N} ∑_{x ∈ m.divisors, cond} g x (m / x)
    have hS1_eq : (∑ m ∈ Ioc P N, ∑ d ∈ m.divisors.filter (· ≤ U),
          ((μ d : ℝ) : ℂ) * (Real.log ((m / d : ℕ) : ℝ) : ℂ) * e (α₀ / (m : ℝ))) =
        ∑ d ∈ Icc 1 U, ((μ d : ℝ) : ℂ) *
          ∑ b ∈ Ioc (P / d) (N / d), (Real.log (b : ℝ) : ℂ) * e (α₀ / ((d * b : ℕ) : ℝ)) := by
      have h1 : ∀ m ∈ Ioc P N, ∑ d ∈ m.divisors.filter (· ≤ U),
            ((μ d : ℝ) : ℂ) * (Real.log ((m / d : ℕ) : ℝ) : ℂ) * e (α₀ / (m : ℝ)) =
          ∑ d ∈ Icc 1 U, if d ∣ m then
            ((μ d : ℝ) : ℂ) * (Real.log ((m / d : ℕ) : ℝ) : ℂ) * e (α₀ / (m : ℝ)) else 0 := by
        intro m hm
        rw [← Finset.sum_filter]
        congr 1; ext d; simp only [mem_filter, Nat.mem_divisors, mem_Icc]
        have hm0 : m ≠ 0 := by have := (mem_Ioc.mp hm).1; omega
        exact ⟨fun ⟨⟨hd, _⟩, hU⟩ => ⟨⟨Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hm0), hU⟩, hd⟩,
          fun ⟨⟨_, hU⟩, hd⟩ => ⟨⟨hd, hm0⟩, hU⟩⟩
      rw [sum_congr rfl h1, Finset.sum_comm]
      refine sum_congr rfl fun d hd => ?_
      have hd1 := (mem_Icc.mp hd).1
      rw [← Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_bij (fun m _ => m / d) ?_ ?_ ?_ ?_
      · intro m hm
        obtain ⟨hm_ioc, hdm⟩ := mem_filter.mp hm
        have hm1 := (mem_Ioc.mp hm_ioc).1; have hm2 := (mem_Ioc.mp hm_ioc).2
        refine mem_Ioc.mpr ⟨?_, Nat.div_le_div_right hm2⟩
        by_contra hle; push Not at hle
        have h1 : d * (m / d) ≤ d * (P / d) := Nat.mul_le_mul_left d hle
        rw [Nat.mul_div_cancel' hdm] at h1
        have h2 : d * (P / d) ≤ P := by rw [mul_comm]; exact Nat.div_mul_le_self P d
        omega
      · intro m₁ hm₁ m₂ hm₂ heq
        have h1 := Nat.mul_div_cancel' (mem_filter.mp hm₁).2
        have h2 := Nat.mul_div_cancel' (mem_filter.mp hm₂).2
        rw [← h1, ← h2, heq]
      · intro b hb
        have hb1 := (mem_Ioc.mp hb).1; have hb2 := (mem_Ioc.mp hb).2
        have hdb_gt : P < d * b := by
          have hdm := Nat.div_add_mod P d
          have hrem := Nat.mod_lt P (by omega : 0 < d)
          nlinarith
        have hdb_le : d * b ≤ N := by
          have := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hb2; linarith
        exact ⟨d * b, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hdb_gt, hdb_le⟩, dvd_mul_right d b⟩,
          Nat.mul_div_cancel_left b (by omega)⟩
      · intro m hm
        rw [Nat.mul_div_cancel' (mem_filter.mp hm).2]; ring
    have hS2_eq : (∑ m ∈ Ioc P N, ∑ k ∈ m.divisors.filter (· ≤ U * U),
          ((∑ d ∈ k.divisors.filter (fun d => d ≤ U ∧ k / d ≤ U), (μ d : ℝ) * Λ (k / d) : ℝ) : ℂ) *
            e (α₀ / (m : ℝ))) =
        ∑ k ∈ Icc 1 (U * U),
          ((∑ d ∈ k.divisors.filter (fun d => d ≤ U ∧ k / d ≤ U), (μ d : ℝ) * Λ (k / d) : ℝ) : ℂ) *
          ∑ b ∈ Ioc (P / k) (N / k), e (α₀ / ((k * b : ℕ) : ℝ)) := by
      have h1 : ∀ m ∈ Ioc P N, ∑ k ∈ m.divisors.filter (· ≤ U * U),
            ((∑ d ∈ k.divisors.filter (fun d => d ≤ U ∧ k / d ≤ U), (μ d : ℝ) * Λ (k / d) : ℝ) : ℂ) *
              e (α₀ / (m : ℝ)) =
          ∑ k ∈ Icc 1 (U * U), if k ∣ m then
            ((∑ d ∈ k.divisors.filter (fun d => d ≤ U ∧ k / d ≤ U), (μ d : ℝ) * Λ (k / d) : ℝ) : ℂ) *
              e (α₀ / (m : ℝ)) else 0 := by
        intro m hm
        rw [← Finset.sum_filter]
        congr 1; ext k; simp only [mem_filter, Nat.mem_divisors, mem_Icc]
        have hm0 : m ≠ 0 := by have := (mem_Ioc.mp hm).1; omega
        exact ⟨fun ⟨⟨hk, _⟩, hUU⟩ => ⟨⟨Nat.pos_of_dvd_of_pos hk (Nat.pos_of_ne_zero hm0), hUU⟩, hk⟩,
          fun ⟨⟨_, hUU⟩, hk⟩ => ⟨⟨hk, hm0⟩, hUU⟩⟩
      rw [sum_congr rfl h1, Finset.sum_comm]
      refine sum_congr rfl fun k hk => ?_
      have hk1 := (mem_Icc.mp hk).1
      rw [← Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_bij (fun m _ => m / k) ?_ ?_ ?_ ?_
      · intro m hm
        obtain ⟨hm_ioc, hkm⟩ := mem_filter.mp hm
        have hm1 := (mem_Ioc.mp hm_ioc).1; have hm2 := (mem_Ioc.mp hm_ioc).2
        refine mem_Ioc.mpr ⟨?_, Nat.div_le_div_right hm2⟩
        by_contra hle; push Not at hle
        have h1 : k * (m / k) ≤ k * (P / k) := Nat.mul_le_mul_left k hle
        rw [Nat.mul_div_cancel' hkm] at h1
        have h2 : k * (P / k) ≤ P := by rw [mul_comm]; exact Nat.div_mul_le_self P k
        omega
      · intro m₁ hm₁ m₂ hm₂ heq
        have h1 := Nat.mul_div_cancel' (mem_filter.mp hm₁).2
        have h2 := Nat.mul_div_cancel' (mem_filter.mp hm₂).2
        rw [← h1, ← h2, heq]
      · intro b hb
        have hb1 := (mem_Ioc.mp hb).1; have hb2 := (mem_Ioc.mp hb).2
        have hkb_gt : P < k * b := by
          have hdm := Nat.div_add_mod P k
          have hrem := Nat.mod_lt P (by omega : 0 < k)
          nlinarith
        have hkb_le : k * b ≤ N := by
          have := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp hb2; linarith
        exact ⟨k * b, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hkb_gt, hkb_le⟩, dvd_mul_right k b⟩,
          Nat.mul_div_cancel_left b (by omega)⟩
      · intro m hm; rw [Nat.mul_div_cancel' (mem_filter.mp hm).2]
    have hS3_eq : (∑ m ∈ Ioc P N, ∑ a ∈ m.divisors.filter (fun a => U < a ∧ U < m / a),
          ((∑ d ∈ a.divisors.filter (· ≤ U), (μ d : ℝ) : ℝ) : ℂ) * (Λ (m / a) : ℂ) * e (α₀ / (m : ℝ))) =
        ∑ a ∈ Ioc U (N / U),
          ((∑ d ∈ a.divisors.filter (· ≤ U), (μ d : ℝ) : ℝ) : ℂ) *
          ∑ b ∈ Ioc (max U (P / a)) (N / a), (Λ b : ℂ) * e (α₀ / ((a * b : ℕ) : ℝ)) := by
      have h1 : ∀ m ∈ Ioc P N, ∑ a ∈ m.divisors.filter (fun a => U < a ∧ U < m / a),
            ((∑ d ∈ a.divisors.filter (· ≤ U), (μ d : ℝ) : ℝ) : ℂ) * (Λ (m / a) : ℂ) * e (α₀ / (m : ℝ)) =
          ∑ a ∈ Ioc U (N / U), if a ∣ m ∧ U < m / a then
            ((∑ d ∈ a.divisors.filter (· ≤ U), (μ d : ℝ) : ℝ) : ℂ) * (Λ (m / a) : ℂ) * e (α₀ / (m : ℝ)) else 0 := by
        intro m hm
        rw [← Finset.sum_filter]
        congr 1; ext a; simp only [mem_filter, Nat.mem_divisors, mem_Ioc]
        have hm1 := (mem_Ioc.mp hm).1; have hm2 := (mem_Ioc.mp hm).2
        constructor
        · rintro ⟨⟨ha, _⟩, hUa, hUma⟩
          have ha_le : a ≤ N / U := by
            have hmul : a * U ≤ m := by
              have : a * U ≤ a * (m / a) := Nat.mul_le_mul_left a hUma.le
              rwa [Nat.mul_div_cancel' ha] at this
            exact (Nat.le_div_iff_mul_le (by omega : 0 < U)).mpr (le_trans hmul hm2)
          exact ⟨⟨hUa, ha_le⟩, ha, hUma⟩
        · rintro ⟨⟨hUa, _⟩, ha, hUma⟩
          exact ⟨⟨ha, by omega⟩, hUa, hUma⟩
      rw [sum_congr rfl h1, Finset.sum_comm]
      refine sum_congr rfl fun a ha => ?_
      have ha1 := (mem_Ioc.mp ha).1
      rw [← Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_bij (fun m _ => m / a) ?_ ?_ ?_ ?_
      · intro m hm
        obtain ⟨hm_ioc, ham, hUma⟩ := mem_filter.mp hm
        have hm1 := (mem_Ioc.mp hm_ioc).1; have hm2 := (mem_Ioc.mp hm_ioc).2
        refine mem_Ioc.mpr ⟨max_lt hUma ?_, Nat.div_le_div_right hm2⟩
        by_contra hle; push Not at hle
        have h1 : a * (m / a) ≤ a * (P / a) := Nat.mul_le_mul_left a hle
        rw [Nat.mul_div_cancel' ham] at h1
        have h2 : a * (P / a) ≤ P := by rw [mul_comm]; exact Nat.div_mul_le_self P a
        omega
      · intro m₁ hm₁ m₂ hm₂ heq
        have h1 := Nat.mul_div_cancel' (mem_filter.mp hm₁).2.1
        have h2 := Nat.mul_div_cancel' (mem_filter.mp hm₂).2.1
        rw [← h1, ← h2, heq]
      · intro b hb
        have hb1 := (mem_Ioc.mp hb).1; have hb2 := (mem_Ioc.mp hb).2
        have hUb : U < b := lt_of_le_of_lt (le_max_left _ _) hb1
        have hPab : P / a < b := lt_of_le_of_lt (le_max_right _ _) hb1
        have hab_gt : P < a * b := by
          have hdm := Nat.div_add_mod P a
          have hrem := Nat.mod_lt P (by omega : 0 < a)
          nlinarith
        have hab_le : a * b ≤ N := by
          have := (Nat.le_div_iff_mul_le (by omega : 0 < a)).mp hb2; linarith
        exact ⟨a * b, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hab_gt, hab_le⟩, dvd_mul_right a b,
          by rwa [Nat.mul_div_cancel_left b (by omega)]⟩, Nat.mul_div_cancel_left b (by omega)⟩
      · intro m hm; rw [Nat.mul_div_cancel' (mem_filter.mp hm).2.1]; ring
    rw [hS1_eq, hS2_eq, hS3_eq]
  -- Helper: Type I call to hunif for 1 ≤ d ≤ U * U and P / d ≤ t ≤ N / d
  have hTypeI_call : ∀ (d t : ℕ), 1 ≤ d → d ≤ U * U → P / d ≤ t → t ≤ N / d →
      ‖∑ b ∈ Ioc (P / d) t, e (α₀ / ((d * b : ℕ) : ℝ))‖ ≤ 2 * ((P / d : ℕ) : ℝ) / L ^ 12 := by
    intro d t hd1 hdUU ht1 ht2
    have hrew : ∑ b ∈ Ioc (P / d) t, e (α₀ / ((d * b : ℕ) : ℝ)) =
        ∑ b ∈ Ioc (P / d) t, e ((α₀ / (d : ℝ)) / (b : ℝ)) :=
      sum_congr rfl fun b _ => by congr 1; push_cast; ring
    rw [hrew]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
    have hPd_ge_U : U ≤ P / d := by
      have : U * d ≤ P := by
        calc U * d ≤ U * (U * U) := Nat.mul_le_mul_left U hdUU
          _ = U ^ 3 := by ring
          _ ≤ P := hU3_le_P
      exact (Nat.le_div_iff_mul_le (by omega)).mpr this
    have hPd_lo : Real.exp ((1 / 8 : ℝ) * L ^ ((9 : ℝ) / 10)) ≤ ((P / d : ℕ) : ℝ) :=
      hU_ge_exp.trans (by exact_mod_cast hPd_ge_U)
    have hPd_hi : ((P / d : ℕ) : ℝ) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 100) := by
      have : ((P / d : ℕ) : ℝ) ≤ (P : ℝ) := by exact_mod_cast Nat.div_le_self P d
      linarith [hP_hi, Real.rpow_nonneg hnpos.le ((1 : ℝ) / 100)]
    have ht_le2 : t ≤ 2 * (P / d) + 1 := by
      have h1 : N / d ≤ (2 * P) / d := Nat.div_le_div_right hN2P
      have hdm := Nat.div_add_mod P d
      have hrem := Nat.mod_lt P (by omega : 0 < d)
      have h2 : (2 * P) / d ≤ 2 * (P / d) + 1 := by
        have hlt : 2 * P < d * (2 * (P / d) + 2) := by nlinarith
        exact Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul hlt)
      omega
    have hαd_lo : (n : ℝ) ^ ((1 : ℝ) / 2) ≤ |α₀ / (d : ℝ)| := by
      rw [abs_of_pos (div_pos (lt_of_lt_of_le hnpos hα₀_lo) hdpos)]
      have hd_le_n : (d : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := by
        have h1 : (d : ℝ) ≤ (P : ℝ) := by exact_mod_cast (le_trans hdUU (by nlinarith : U * U ≤ P))
        have h2 : (n : ℝ) ^ ((1 : ℝ) / 100) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
        linarith
      rw [le_div_iff₀ hdpos]
      have hsq : (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) = (n : ℝ) := by
        rw [← Real.rpow_add hnpos]; norm_num
      nlinarith [Real.rpow_nonneg hnpos.le ((1 : ℝ) / 2)]
    have hαd_hi : |α₀ / (d : ℝ)| ≤ 2 * (n : ℝ) := by
      rw [abs_of_pos (div_pos (lt_of_lt_of_le hnpos hα₀_lo) hdpos)]
      exact (div_le_self (by linarith) (by exact_mod_cast hd1)).trans hα₀_hi
    by_cases ht2P : t ≤ 2 * (P / d)
    · have h1 := hunif (P / d) t (α₀ / (d : ℝ)) hPd_lo hPd_hi ht1 ht2P hαd_lo hαd_hi
      change ‖∑ b ∈ Ioc (P / d) t, e ((α₀ / (d : ℝ)) / (b : ℝ))‖ ≤ ((P / d : ℕ) : ℝ) / L ^ 12 at h1
      have hnn : 0 ≤ ((P / d : ℕ) : ℝ) / L ^ 12 := by positivity
      have h2eq : 2 * ((P / d : ℕ) : ℝ) / L ^ 12 = 2 * (((P / d : ℕ) : ℝ) / L ^ 12) := by ring
      linarith
    · have ht_eq : t = 2 * (P / d) + 1 := by omega
      rw [ht_eq]
      have hIoc_split : Ioc (P / d) (2 * (P / d) + 1) =
          insert (2 * (P / d) + 1) (Ioc (P / d) (2 * (P / d))) := by
        ext x; simp only [mem_Ioc, mem_insert]; omega
      rw [hIoc_split, sum_insert (by simp)]
      have h1 := hunif (P / d) (2 * (P / d)) (α₀ / (d : ℝ)) hPd_lo hPd_hi (by omega) le_rfl hαd_lo hαd_hi
      change ‖∑ b ∈ Ioc (P / d) (2 * (P / d)), e ((α₀ / (d : ℝ)) / (b : ℝ))‖ ≤ ((P / d : ℕ) : ℝ) / L ^ 12 at h1
      have h1_le : (1 : ℝ) ≤ ((P / d : ℕ) : ℝ) / L ^ 12 := by
        rw [one_le_div (by positivity)]
        have hL12_le : L ^ 12 ≤ Real.exp ((1 / 8 : ℝ) * L ^ ((9 : ℝ) / 10)) := by
          have hlog : Real.log (L ^ 12) ≤ (1 / 8 : ℝ) * L ^ ((9 : ℝ) / 10) := by
            rw [Real.log_pow]; push_cast; linarith [hL9_log]
          calc L ^ 12 = Real.exp (Real.log (L ^ 12)) := (Real.exp_log (by positivity)).symm
            _ ≤ _ := Real.exp_le_exp.mpr hlog
        exact hL12_le.trans hPd_lo
      calc ‖e ((α₀ / (d : ℝ)) / ((2 * (P / d) + 1 : ℕ) : ℝ)) + ∑ b ∈ Ioc (P / d) (2 * (P / d)), _‖
          ≤ ‖e ((α₀ / (d : ℝ)) / ((2 * (P / d) + 1 : ℕ) : ℝ))‖ + ‖∑ b ∈ Ioc (P / d) (2 * (P / d)), _‖ :=
            norm_add_le _ _
        _ ≤ 1 + ((P / d : ℕ) : ℝ) / L ^ 12 := by rw [norm_e]; linarith
        _ ≤ 2 * ((P / d : ℕ) : ℝ) / L ^ 12 := by
            have h2eq : 2 * ((P / d : ℕ) : ℝ) / L ^ 12 = 2 * (((P / d : ℕ) : ℝ) / L ^ 12) := by ring
            linarith
  -- Bound Term S1 ≤ P / L^2
  have hS1_bd : ‖∑ d ∈ Icc 1 U, ((μ d : ℝ) : ℂ) *
      ∑ b ∈ Ioc (P / d) (N / d), (Real.log (b : ℝ) : ℂ) * e (α₀ / ((d * b : ℕ) : ℝ))‖ ≤
      (P : ℝ) / L ^ 2 := by
    have hinner : ∀ d ∈ Icc 1 U,
        ‖((μ d : ℝ) : ℂ) * ∑ b ∈ Ioc (P / d) (N / d), (Real.log (b : ℝ) : ℂ) * e (α₀ / ((d * b : ℕ) : ℝ))‖ ≤
          4 * L * ((P : ℝ) / (d : ℝ)) / L ^ 12 := by
      intro d hd
      have hd1 := (mem_Icc.mp hd).1; have hdU := (mem_Icc.mp hd).2
      have hμ1 : ‖((μ d : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_moebius_le_one d
      rw [norm_mul]
      have hsum_bd : ‖∑ b ∈ Ioc (P / d) (N / d), (Real.log (b : ℝ) : ℂ) * e (α₀ / ((d * b : ℕ) : ℝ))‖ ≤
          4 * L * ((P : ℝ) / (d : ℝ)) / L ^ 12 := by
        by_cases hlt : P / d < N / d
        · have hab := abel_increasing_Ioc hlt (fun b => Real.log (b : ℝ))
            (fun b => e (α₀ / ((d * b : ℕ) : ℝ))) (B := 2 * ((P / d : ℕ) : ℝ) / L ^ 12)
            (by positivity)
            (fun b hb => Real.log_nonneg (by
              have h1 : 0 < b := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hb).1
              exact_mod_cast h1))
            (fun b hb _ => Real.log_le_log
              (by
                have h1 : 0 < b := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hb).1
                exact_mod_cast h1)
              (by exact_mod_cast Nat.le_succ b))
            (fun t ht => hTypeI_call d t hd1 (le_trans hdU (Nat.le_mul_self U)) (mem_Icc.mp ht).1 (mem_Icc.mp ht).2)
          have hlog_le : Real.log ((N / d : ℕ) : ℝ) ≤ L := by
            have h1 : N / d ≤ 2 * P := le_trans (Nat.div_le_self N d) hN2P
            have hNd_pos : 0 < N / d := lt_of_le_of_lt (Nat.zero_le _) hlt
            have h2 : Real.log ((N / d : ℕ) : ℝ) ≤ Real.log ((2 * P : ℕ) : ℝ) :=
              Real.log_le_log (by exact_mod_cast hNd_pos) (by exact_mod_cast h1)
            exact h2.trans hlog2P_le_L
          have hPd_le : ((P / d : ℕ) : ℝ) ≤ (P : ℝ) / (d : ℝ) := by
            have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
            rw [le_div_iff₀ hdpos]; exact_mod_cast Nat.div_mul_le_self P d
          calc ‖∑ b ∈ Ioc (P / d) (N / d), _‖
              ≤ 2 * Real.log ((N / d : ℕ) : ℝ) * (2 * ((P / d : ℕ) : ℝ) / L ^ 12) := hab
            _ ≤ 2 * L * (2 * ((P : ℝ) / (d : ℝ)) / L ^ 12) := by
                refine mul_le_mul (mul_le_mul_of_nonneg_left hlog_le zero_le_two)
                  (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hPd_le zero_le_two) (by positivity))
                  (by positivity) (by positivity)
            _ = 4 * L * ((P : ℝ) / (d : ℝ)) / L ^ 12 := by ring
        · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
          positivity
      calc ‖((μ d : ℝ) : ℂ)‖ * ‖∑ b ∈ Ioc (P / d) (N / d), _‖
          ≤ 1 * (4 * L * ((P : ℝ) / (d : ℝ)) / L ^ 12) :=
            mul_le_mul hμ1 hsum_bd (norm_nonneg _) zero_le_one
        _ = 4 * L * ((P : ℝ) / (d : ℝ)) / L ^ 12 := one_mul _
    calc ‖∑ d ∈ Icc 1 U, _‖ ≤ ∑ d ∈ Icc 1 U, ‖_‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ Icc 1 U, (4 * L * ((P : ℝ) / (d : ℝ)) / L ^ 12) := sum_le_sum hinner
      _ = (4 * (P : ℝ) / L ^ 11) * ∑ d ∈ Icc 1 U, (1 : ℝ) / (d : ℝ) := by
          rw [Finset.mul_sum]; refine sum_congr rfl fun d _ => by field_simp [hLpos.ne']
      _ ≤ (4 * (P : ℝ) / L ^ 11) * (1 + Real.log (U : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_inv_le_one_add_log hU_pos) (by positivity)
      _ ≤ (P : ℝ) / L ^ 2 := by
          have hlogU : 1 + Real.log (U : ℝ) ≤ 2 * L := by
            have h1 : Real.log (U : ℝ) ≤ Real.log ((2 * P : ℕ) : ℝ) :=
              Real.log_le_log (by exact_mod_cast hU_pos) (by exact_mod_cast (by omega : U ≤ 2 * P))
            linarith [h1.trans hlog2P_le_L]
          have hL8 : (8 : ℝ) ≤ L ^ 8 := by
            have : (1000 : ℝ) ^ 8 ≤ L ^ 8 := pow_le_pow_left₀ (by norm_num) hL1000 8
            norm_num at this; linarith
          calc (4 * (P : ℝ) / L ^ 11) * (1 + Real.log (U : ℝ))
              ≤ (4 * (P : ℝ) / L ^ 11) * (2 * L) := mul_le_mul_of_nonneg_left hlogU (by positivity)
            _ = (8 / L ^ 8) * ((P : ℝ) / L ^ 2) := by field_simp [hLpos.ne']; ring
            _ ≤ 1 * ((P : ℝ) / L ^ 2) :=
                mul_le_mul_of_nonneg_right ((div_le_one (by positivity)).mpr hL8) (by positivity)
            _ = (P : ℝ) / L ^ 2 := one_mul _
  -- Bound Term S2 ≤ P / L^2
  have hS2_bd : ‖∑ k ∈ Icc 1 (U * U),
      ((∑ d ∈ k.divisors.filter (fun d => d ≤ U ∧ k / d ≤ U), (μ d : ℝ) * Λ (k / d) : ℝ) : ℂ) *
      ∑ b ∈ Ioc (P / k) (N / k), e (α₀ / ((k * b : ℕ) : ℝ))‖ ≤ (P : ℝ) / L ^ 2 := by
    have hcoeff_bd : ∀ k ∈ Icc 1 (U * U),
        ‖((∑ d ∈ k.divisors.filter (fun d => d ≤ U ∧ k / d ≤ U), (μ d : ℝ) * Λ (k / d) : ℝ) : ℂ)‖ ≤ L := by
      intro k hk
      have hk1 := (mem_Icc.mp hk).1; have hkUU := (mem_Icc.mp hk).2
      rw [Complex.norm_real, Real.norm_eq_abs]
      calc |∑ d ∈ k.divisors.filter (fun d => d ≤ U ∧ k / d ≤ U), (μ d : ℝ) * Λ (k / d)|
          ≤ ∑ d ∈ k.divisors.filter (fun d => d ≤ U ∧ k / d ≤ U), |(μ d : ℝ) * Λ (k / d)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ k.divisors.filter (fun d => d ≤ U ∧ k / d ≤ U), Λ (k / d) := by
            refine sum_le_sum fun d _ => ?_
            rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
            nlinarith [abs_moebius_le_one d, ArithmeticFunction.vonMangoldt_nonneg (n := k / d)]
        _ ≤ ∑ d ∈ k.divisors, Λ (k / d) :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
        _ = ∑ d ∈ k.divisors, Λ d := sum_divisors_div_eq k (fun d => Λ d)
        _ = Real.log (k : ℝ) := ArithmeticFunction.vonMangoldt_sum
        _ ≤ L := by
            have hk2P : k ≤ 2 * P := le_trans hkUU (by nlinarith)
            exact (Real.log_le_log (by exact_mod_cast hk1) (by exact_mod_cast hk2P)).trans hlog2P_le_L
    have hinner : ∀ k ∈ Icc 1 (U * U),
        ‖((∑ d ∈ k.divisors.filter (fun d => d ≤ U ∧ k / d ≤ U), (μ d : ℝ) * Λ (k / d) : ℝ) : ℂ) *
          ∑ b ∈ Ioc (P / k) (N / k), e (α₀ / ((k * b : ℕ) : ℝ))‖ ≤
          2 * L * ((P : ℝ) / (k : ℝ)) / L ^ 12 := by
      intro k hk
      have hk1 := (mem_Icc.mp hk).1; have hkUU := (mem_Icc.mp hk).2
      rw [norm_mul]
      have hPk_le : ((P / k : ℕ) : ℝ) ≤ (P : ℝ) / (k : ℝ) := by
        have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
        rw [le_div_iff₀ hkpos]; exact_mod_cast Nat.div_mul_le_self P k
      have hsum : ‖∑ b ∈ Ioc (P / k) (N / k), e (α₀ / ((k * b : ℕ) : ℝ))‖ ≤
          2 * ((P : ℝ) / (k : ℝ)) / L ^ 12 := by
        by_cases hle : P / k ≤ N / k
        · exact (hTypeI_call k (N / k) hk1 hkUU hle le_rfl).trans
            (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hPk_le zero_le_two) (by positivity))
        · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]; positivity
      calc ‖_‖ * ‖_‖ ≤ L * (2 * ((P : ℝ) / (k : ℝ)) / L ^ 12) :=
            mul_le_mul (hcoeff_bd k hk) hsum (norm_nonneg _) hLpos.le
        _ = 2 * L * ((P : ℝ) / (k : ℝ)) / L ^ 12 := by ring
    calc ‖∑ k ∈ Icc 1 (U * U), _‖ ≤ ∑ k ∈ Icc 1 (U * U), ‖_‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Icc 1 (U * U), (2 * L * ((P : ℝ) / (k : ℝ)) / L ^ 12) := sum_le_sum hinner
      _ = (2 * (P : ℝ) / L ^ 11) * ∑ k ∈ Icc 1 (U * U), (1 : ℝ) / (k : ℝ) := by
          rw [Finset.mul_sum]; refine sum_congr rfl fun k _ => by field_simp [hLpos.ne']
      _ ≤ (2 * (P : ℝ) / L ^ 11) * (1 + Real.log ((U * U : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_inv_le_one_add_log (by nlinarith)) (by positivity)
      _ ≤ (P : ℝ) / L ^ 2 := by
          have hlogUU : 1 + Real.log ((U * U : ℕ) : ℝ) ≤ 2 * L := by
            have h1 : Real.log ((U * U : ℕ) : ℝ) ≤ Real.log ((2 * P : ℕ) : ℝ) :=
              Real.log_le_log (by exact_mod_cast (by nlinarith : 0 < U * U))
                (by exact_mod_cast (by nlinarith : U * U ≤ 2 * P))
            linarith [h1.trans hlog2P_le_L]
          have hL8 : (4 : ℝ) ≤ L ^ 8 := by
            have : (1000 : ℝ) ^ 8 ≤ L ^ 8 := pow_le_pow_left₀ (by norm_num) hL1000 8
            norm_num at this; linarith
          calc (2 * (P : ℝ) / L ^ 11) * (1 + Real.log ((U * U : ℕ) : ℝ))
              ≤ (2 * (P : ℝ) / L ^ 11) * (2 * L) := mul_le_mul_of_nonneg_left hlogUU (by positivity)
            _ = (4 / L ^ 8) * ((P : ℝ) / L ^ 2) := by field_simp [hLpos.ne']; ring
            _ ≤ 1 * ((P : ℝ) / L ^ 2) :=
                mul_le_mul_of_nonneg_right ((div_le_one (by positivity)).mpr hL8) (by positivity)
            _ = (P : ℝ) / L ^ 2 := one_mul _
  -- Bound Term S3 (Type II) ≤ 7 * P / L^2 via dyadic decomposition + vaughan_S3_dyadic_bound!
  have hS3_bd : ‖∑ a ∈ Ioc U (N / U),
      ((∑ d ∈ a.divisors.filter (· ≤ U), (μ d : ℝ) : ℝ) : ℂ) *
      ∑ b ∈ Ioc (max U (P / a)) (N / a), (Λ b : ℂ) * e (α₀ / ((a * b : ℕ) : ℝ))‖ ≤
      7 * (P : ℝ) / L ^ 2 := by
    let K := Nat.log 2 (2 * P) + 1
    let dblk (j : ℕ) : Finset ℕ :=
      Ioc (min (N / U) (U * 2 ^ j)) (min (N / U) (U * 2 ^ (j + 1)))
    have hpart_S3 : Ioc U (N / U) = (range K).biUnion dblk := by
      ext a
      simp only [mem_Ioc, mem_biUnion, mem_range, dblk]
      constructor
      · intro ⟨hUa, haNU⟩
        let j := Nat.log 2 ((a - 1) / U)
        have haU_pos : 1 ≤ (a - 1) / U := Nat.div_pos (by omega) hU_pos
        have hj_pow : 2 ^ j ≤ (a - 1) / U := Nat.pow_log_le_self 2 (by omega)
        have hj_lt : (a - 1) / U < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) ((a - 1) / U)
        have hjK : j < K := by
          have : (a - 1) / U ≤ 2 * P := le_trans (Nat.div_le_self (a - 1) U)
            (le_trans (by omega : a - 1 ≤ N / U) (le_trans (Nat.div_le_self N U) hN2P))
          have hlog_le : j ≤ Nat.log 2 (2 * P) := Nat.log_mono_right this
          omega
        refine ⟨j, hjK, ?_, ?_⟩
        · have h1 : U * 2 ^ j ≤ a - 1 := by
            have := Nat.mul_le_mul_left U hj_pow
            have h2 : U * ((a - 1) / U) ≤ a - 1 := by rw [mul_comm]; exact Nat.div_mul_le_self (a - 1) U
            omega
          omega
        · have h2 : a - 1 < U * 2 ^ (j + 1) := by
            have hdm := Nat.div_add_mod (a - 1) U
            have hrem := Nat.mod_lt (a - 1) hU_pos
            have h3 : (a - 1) / U + 1 ≤ 2 ^ (j + 1) := hj_lt
            nlinarith
          omega
      · rintro ⟨j, _, h1, h2⟩
        have h1' : U ≤ U * 2 ^ j := Nat.le_mul_of_pos_right U (pow_pos (by norm_num) j)
        omega
    have hdisj_S3 : Set.PairwiseDisjoint (range K : Set ℕ) dblk := by
      intro j₁ _ j₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro a ha1 ha2
      simp only [dblk, mem_Ioc] at ha1 ha2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : 2 ^ (j₁ + 1) ≤ 2 ^ j₂ := Nat.pow_le_pow_right (by norm_num) hlt
        have : U * 2 ^ (j₁ + 1) ≤ U * 2 ^ j₂ := Nat.mul_le_mul_left U this
        omega
      · have : 2 ^ (j₂ + 1) ≤ 2 ^ j₁ := Nat.pow_le_pow_right (by norm_num) hgt
        have : U * 2 ^ (j₂ + 1) ≤ U * 2 ^ j₁ := Nat.mul_le_mul_left U this
        omega
    have hK_le : (K : ℝ) ≤ 2 * L := by
      have h2K : (2 : ℝ) ^ (Nat.log 2 (2 * P)) ≤ ((2 * P : ℕ) : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 (by omega : 2 * P ≠ 0)
      have hlog2K : (Nat.log 2 (2 * P) : ℝ) * Real.log 2 ≤ L := by
        have h1 := Real.log_le_log (by positivity) h2K
        rw [Real.log_pow] at h1
        exact h1.trans hlog2P_le_L
      have hlog2 : (0.69 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      dsimp only [K]; push_cast; nlinarith
    rw [hpart_S3, Finset.sum_biUnion hdisj_S3]
    calc ‖∑ j ∈ range K, ∑ a ∈ dblk j, _‖
        ≤ ∑ j ∈ range K, ‖∑ a ∈ dblk j, _‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ range K, (3 * (P : ℝ) / L ^ 3) := by
          refine sum_le_sum fun j _ => ?_
          dsimp only [dblk]
          let A := min (N / U) (U * 2 ^ j)
          let A' := min (N / U) (U * 2 ^ (j + 1))
          by_cases hlt : A < A'
          · have hUA : U ≤ A := by
              have h1 : U ≤ U * 2 ^ j := Nat.le_mul_of_pos_right U (pow_pos (by norm_num) j)
              have h2 : U ≤ N / U := (Nat.le_div_iff_mul_le hU_pos).mpr (by nlinarith)
              dsimp [A]; omega
            have hA'2A : A' ≤ 2 * A := by
              dsimp only [A, A']
              have : U * 2 ^ (j + 1) = 2 * (U * 2 ^ j) := by rw [pow_succ]; ring
              omega
            exact vaughan_S3_dyadic_bound hn1000 hL1000 hL9_log hunif hP_ge_exp hP_hi hN2P
              hlog2P_le_L hU_pos hU_ge_half hU_ge_exp hα₀_lo hα₀_hi hUA hlt hA'2A (min_le_left _ _)
          · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]; positivity
      _ = (K : ℝ) * (3 * (P : ℝ) / L ^ 3) := by simp
      _ ≤ (2 * L) * (3 * (P : ℝ) / L ^ 3) := mul_le_mul_of_nonneg_right hK_le (by positivity)
      _ = 6 * (P : ℝ) / L ^ 2 := by field_simp [hLpos.ne']; ring
      _ ≤ 7 * (P : ℝ) / L ^ 2 := by gcongr; norm_num
  -- Combine hprime_vs_Λ, hS1_bd, hS2_bd, hS3_bd!
  have hΛ_bd : ‖∑ m ∈ Ioc P N, (Λ m : ℂ) * e (α₀ / (m : ℝ))‖ ≤ 9 * (P : ℝ) / L ^ 2 := by
    rw [hΛ_vaughan]
    have h1 := norm_sub_le
      ((∑ d ∈ Icc 1 U, ((μ d : ℝ) : ℂ) *
        ∑ b ∈ Ioc (P / d) (N / d), (Real.log (b : ℝ) : ℂ) * e (α₀ / ((d * b : ℕ) : ℝ))) -
      (∑ k ∈ Icc 1 (U * U),
        ((∑ d ∈ k.divisors.filter (fun d => d ≤ U ∧ k / d ≤ U), (μ d : ℝ) * Λ (k / d) : ℝ) : ℂ) *
        ∑ b ∈ Ioc (P / k) (N / k), e (α₀ / ((k * b : ℕ) : ℝ))))
      (∑ a ∈ Ioc U (N / U),
        ((∑ d ∈ a.divisors.filter (· ≤ U), (μ d : ℝ) : ℝ) : ℂ) *
        ∑ b ∈ Ioc (max U (P / a)) (N / a), (Λ b : ℂ) * e (α₀ / ((a * b : ℕ) : ℝ)))
    have h2 := norm_sub_le
      (∑ d ∈ Icc 1 U, ((μ d : ℝ) : ℂ) *
        ∑ b ∈ Ioc (P / d) (N / d), (Real.log (b : ℝ) : ℂ) * e (α₀ / ((d * b : ℕ) : ℝ)))
      (∑ k ∈ Icc 1 (U * U),
        ((∑ d ∈ k.divisors.filter (fun d => d ≤ U ∧ k / d ≤ U), (μ d : ℝ) * Λ (k / d) : ℝ) : ℂ) *
        ∑ b ∈ Ioc (P / k) (N / k), e (α₀ / ((k * b : ℕ) : ℝ)))
    have h9 : (P : ℝ) / L ^ 2 + (P : ℝ) / L ^ 2 + 7 * (P : ℝ) / L ^ 2 = 9 * (P : ℝ) / L ^ 2 := by ring
    linarith [hS1_bd, hS2_bd, hS3_bd, h1, h2, h9]
  have htri : ‖∑ p ∈ (Ioc P N).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e (α₀ / (p : ℝ))‖ ≤
      ‖(∑ p ∈ (Ioc P N).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e (α₀ / (p : ℝ))) -
       (∑ m ∈ Ioc P N, (Λ m : ℂ) * e (α₀ / (m : ℝ)))‖ +
      ‖∑ m ∈ Ioc P N, (Λ m : ℂ) * e (α₀ / (m : ℝ))‖ := by
    calc ‖∑ p ∈ (Ioc P N).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e (α₀ / (p : ℝ))‖
        = ‖((∑ p ∈ (Ioc P N).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e (α₀ / (p : ℝ))) -
            (∑ m ∈ Ioc P N, (Λ m : ℂ) * e (α₀ / (m : ℝ)))) +
            (∑ m ∈ Ioc P N, (Λ m : ℂ) * e (α₀ / (m : ℝ)))‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  change ‖∑ p ∈ (Ioc P N).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e (α₀ / (p : ℝ))‖ ≤ 10 * (P : ℝ) / L ^ 2
  have h10 : (P : ℝ) / L ^ 2 + 9 * (P : ℝ) / L ^ 2 = 10 * (P : ℝ) / L ^ 2 := by ring
  linarith [htri, hprime_vs_Λ, hΛ_bd, h10]

/- ### Part 4: Band 1 (Vinogradov) and Band 2 (Chebyshev) reciprocal prime bounds -/

/-- Band 1 bound: for all sufficiently large `n` and `h ∈ {1, 2}`,
    `‖∑ p ∈ (Ioc A B).filter Nat.Prime, e (h * n / p) / p‖ ≤ 1`
    whenever `exp((log n)^(9/10)) ≤ A ≤ B ≤ n^(1/100)`. -/
private lemma band1_recip_bound :
    ∀ᶠ n : ℕ in atTop,
      ∀ (h A B : ℕ), 1 ≤ h → h ≤ 2 →
        Real.exp ((Real.log (n : ℝ)) ^ ((9 : ℝ) / 10)) ≤ (A : ℝ) →
        (B : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 100) →
        ‖∑ p ∈ (Ioc A B).filter Nat.Prime, e (((h * n : ℕ) : ℝ) / (p : ℝ)) / (p : ℂ)‖ ≤ 1 := by
  have hL_top : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [dyadic_prime_sum_bound, hL_top.eventually (eventually_ge_atTop (1000 : ℝ)),
    eventually_ge_atTop 1000] with n hdyad hL1000 hn1000
  let L : ℝ := Real.log (n : ℝ)
  have hLpos : 0 < L := by dsimp [L]; linarith
  intro h A B hh1 hh2 hA_lo hB_hi
  by_cases hAB : B ≤ A
  · rw [Finset.Ioc_eq_empty (by omega), Finset.filter_empty, Finset.sum_empty, norm_zero]
    exact zero_le_one
  · push Not at hAB
    have hA_ge10 : 10 ≤ A := by
      have h1 : (10 : ℝ) ≤ (A : ℝ) := by
        have h10 : (10 : ℝ) ≤ L ^ ((9 : ℝ) / 10) := by
          have : (10 : ℝ) ^ (10 : ℕ) ≤ L ^ (9 : ℕ) := by
            have h1000 : (1000 : ℝ) ^ (9 : ℕ) ≤ L ^ (9 : ℕ) := pow_le_pow_left₀ (by norm_num) hL1000 9
            norm_num at h1000 ⊢; linarith
          have hr := Real.rpow_le_rpow (by positivity) this (show (0 : ℝ) ≤ 1 / 10 by norm_num)
          rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
            ← Real.rpow_mul hLpos.le] at hr
          norm_num at hr; exact hr
        have hexp : (10 : ℝ) ≤ Real.exp 10 := by linarith [Real.add_one_le_exp (10 : ℝ)]
        exact (hexp.trans (Real.exp_le_exp.mpr h10)).trans hA_lo
      exact_mod_cast h1
    -- Partition Ioc A B into dyadic blocks Ioc (min B (A * 2^j)) (min B (A * 2^(j+1)))
    let K := Nat.log 2 B + 1
    let dblk (j : ℕ) : Finset ℕ := Ioc (min B (A * 2 ^ j)) (min B (A * 2 ^ (j + 1)))
    have hpart : Ioc A B = (range K).biUnion dblk := by
      ext p
      simp only [mem_Ioc, mem_biUnion, mem_range, dblk]
      constructor
      · intro ⟨hAp, hpB⟩
        let j := Nat.log 2 ((p - 1) / A)
        have hpA_pos : 1 ≤ (p - 1) / A := Nat.div_pos (by omega) (by omega)
        have hj_pow : 2 ^ j ≤ (p - 1) / A := Nat.pow_log_le_self 2 (by omega)
        have hj_lt : (p - 1) / A < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) ((p - 1) / A)
        have hjK : j < K := by
          have : (p - 1) / A ≤ B := le_trans (Nat.div_le_self (p - 1) A) (by omega)
          have hlog_le : j ≤ Nat.log 2 B := Nat.log_mono_right this
          omega
        refine ⟨j, hjK, ?_, ?_⟩
        · have h1 : A * 2 ^ j ≤ p - 1 := by
            have := Nat.mul_le_mul_left A hj_pow
            have h2 : A * ((p - 1) / A) ≤ p - 1 := by rw [mul_comm]; exact Nat.div_mul_le_self (p - 1) A
            omega
          omega
        · have h2 : p - 1 < A * 2 ^ (j + 1) := by
            have hdm := Nat.div_add_mod (p - 1) A
            have hrem := Nat.mod_lt (p - 1) (by omega : 0 < A)
            have h3 : (p - 1) / A + 1 ≤ 2 ^ (j + 1) := hj_lt
            nlinarith
          omega
      · rintro ⟨j, _, h1, h2⟩
        have h1' : A ≤ A * 2 ^ j := Nat.le_mul_of_pos_right A (pow_pos (by norm_num) j)
        omega
    have hdisj : Set.PairwiseDisjoint (range K : Set ℕ) dblk := by
      intro j₁ _ j₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro p hp1 hp2
      simp only [dblk, mem_Ioc] at hp1 hp2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : A * 2 ^ (j₁ + 1) ≤ A * 2 ^ j₂ := Nat.mul_le_mul_left A (Nat.pow_le_pow_right (by norm_num) hlt)
        omega
      · have : A * 2 ^ (j₂ + 1) ≤ A * 2 ^ j₁ := Nat.mul_le_mul_left A (Nat.pow_le_pow_right (by norm_num) hgt)
        omega
    have hfilt_biUnion : (Ioc A B).filter Nat.Prime = (range K).biUnion (fun j => (dblk j).filter Nat.Prime) := by
      rw [hpart, Finset.filter_biUnion]
    have hdisj_filt : Set.PairwiseDisjoint (range K : Set ℕ) (fun j => (dblk j).filter Nat.Prime) :=
      fun j₁ hj₁ j₂ hj₂ hne => (hdisj hj₁ hj₂ hne).mono (filter_subset _ _) (filter_subset _ _)
    rw [hfilt_biUnion, Finset.sum_biUnion hdisj_filt]
    -- Bound each dyadic block via Abel summation + hdyad: ≤ 10 / L^2
    have hblk_bd : ∀ j ∈ range K,
        ‖∑ p ∈ (dblk j).filter Nat.Prime, e (((h * n : ℕ) : ℝ) / (p : ℝ)) / (p : ℂ)‖ ≤ 10 / L ^ 2 := by
      intro j _
      dsimp only [dblk]
      let P := min B (A * 2 ^ j)
      let N := min B (A * 2 ^ (j + 1))
      by_cases hlt : P < N
      · have hP_ge_A : A ≤ P := by
          have h1 : A ≤ A * 2 ^ j := Nat.le_mul_of_pos_right A (pow_pos (by norm_num) j)
          dsimp [P]; omega
        have hP_lo : Real.exp (L ^ ((9 : ℝ) / 10)) / 2 ≤ (P : ℝ) := by
          have : Real.exp (L ^ ((9 : ℝ) / 10)) ≤ (P : ℝ) := hA_lo.trans (by exact_mod_cast hP_ge_A)
          linarith [Real.exp_pos (L ^ ((9 : ℝ) / 10))]
        have hP_hi : (P : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 100) :=
          (by exact_mod_cast min_le_left B (A * 2 ^ j) : (P : ℝ) ≤ B).trans hB_hi
        have hN2P : N ≤ 2 * P := by
          dsimp only [P, N]
          have : A * 2 ^ (j + 1) = 2 * (A * 2 ^ j) := by rw [pow_succ]; ring
          omega
        -- Rewrite prime sum as Ioc P N sum with decreasing weight w(m) = 1 / (m * log m)
        let w : ℕ → ℝ := fun m => 1 / ((m : ℝ) * Real.log (m : ℝ))
        let g : ℕ → ℂ := fun m => if m.Prime then (Real.log (m : ℝ) : ℂ) * e (((h * n : ℕ) : ℝ) / (m : ℝ)) else 0
        have hrew : ∑ p ∈ (Ioc P N).filter Nat.Prime, e (((h * n : ℕ) : ℝ) / (p : ℝ)) / (p : ℂ) =
            ∑ m ∈ Ioc P N, (w m : ℂ) * g m := by
          rw [Finset.sum_filter]
          refine sum_congr rfl fun m hm => ?_
          have hm2 : 2 ≤ m := by have := (mem_Ioc.mp hm).1; omega
          have hlog_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
          dsimp only [w, g]
          split_ifs with hp
          · rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul]
            have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            have hlog0 : (Real.log (m : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog_pos.ne'
            have hmR : ((m : ℝ) : ℂ) = (m : ℂ) := by norm_cast
            rw [hmR]
            field_simp [hm0, hlog0]
          · simp
        rw [hrew]
        have hab := abel_decreasing_Ioc hlt w g (B := 10 * (P : ℝ) / L ^ 2) (by positivity)
          (fun m hm => by
            dsimp only [w]
            have hm2 : 2 ≤ m := by have := (mem_Ioc.mp hm).1; omega
            have hlog_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
            positivity)
          (fun m hm _ => by
            dsimp only [w]
            have hm2 : 2 ≤ m := by have := (mem_Ioc.mp hm).1; omega
            have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
            have hlog_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
            refine one_div_le_one_div_of_le (by positivity) ?_
            exact mul_le_mul (by exact_mod_cast Nat.le_succ m)
              (Real.log_le_log hmpos (by exact_mod_cast Nat.le_succ m)) hlog_pos.le (by positivity))
          (fun t ht => by
            have ht1 := (mem_Icc.mp ht).1; have ht2 := (mem_Icc.mp ht).2
            by_cases hPt : P < t
            · have hsum_g : ∑ m ∈ Ioc P t, g m =
                  ∑ p ∈ (Ioc P t).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e (((h * n : ℕ) : ℝ) / (p : ℝ)) := by
                rw [Finset.sum_filter]
              rw [hsum_g]
              exact hdyad h P t hh1 hh2 hP_lo hP_hi hPt (le_trans ht2 hN2P)
            · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]; positivity)
        have hw_le : w (P + 1) ≤ 1 / (P : ℝ) := by
          dsimp only [w]
          have hPpos : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
          have hlog1 : (1 : ℝ) ≤ Real.log ((P + 1 : ℕ) : ℝ) := by
            have : Real.exp 1 ≤ ((P + 1 : ℕ) : ℝ) := by
              have : (10 : ℝ) ≤ ((P + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 10 ≤ P + 1)
              linarith [Real.exp_one_lt_d9]
            have := Real.log_le_log (Real.exp_pos 1) this; rwa [Real.log_exp] at this
          refine one_div_le_one_div_of_le hPpos ?_
          have hP1 : (P : ℝ) ≤ ((P + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ P
          nlinarith
        calc ‖∑ m ∈ Ioc P N, (w m : ℂ) * g m‖ ≤ w (P + 1) * (10 * (P : ℝ) / L ^ 2) := hab
          _ ≤ (1 / (P : ℝ)) * (10 * (P : ℝ) / L ^ 2) :=
              mul_le_mul_of_nonneg_right hw_le (by positivity)
          _ = 10 / L ^ 2 := by
              have hPpos : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
              field_simp [hPpos.ne']
      · rw [Finset.Ioc_eq_empty (by omega), Finset.filter_empty, Finset.sum_empty, norm_zero]
        positivity
    have hK_le : (K : ℝ) ≤ 2 * L := by
      have hB_le_n : (B : ℝ) ≤ (n : ℝ) := by
        have h1 : (n : ℝ) ^ ((1 : ℝ) / 100) ≤ (n : ℝ) := by
          conv_rhs => rw [← Real.rpow_one (n : ℝ)]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
        exact hB_hi.trans h1
      have h2K : (2 : ℝ) ^ (Nat.log 2 B) ≤ (B : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 (by omega : B ≠ 0)
      have hlog2K : (Nat.log 2 B : ℝ) * Real.log 2 ≤ L := by
        have h1 := Real.log_le_log (by positivity) (h2K.trans hB_le_n)
        rwa [Real.log_pow] at h1
      have hlog2 : (0.69 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      dsimp only [K]; push_cast; nlinarith
    calc ‖∑ j ∈ range K, ∑ p ∈ (dblk j).filter Nat.Prime, e (((h * n : ℕ) : ℝ) / (p : ℝ)) / (p : ℂ)‖
        ≤ ∑ j ∈ range K, ‖∑ p ∈ (dblk j).filter Nat.Prime, e (((h * n : ℕ) : ℝ) / (p : ℝ)) / (p : ℂ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _j ∈ range K, (10 / L ^ 2) := sum_le_sum hblk_bd
      _ = (K : ℝ) * (10 / L ^ 2) := by simp
      _ ≤ (2 * L) * (10 / L ^ 2) := mul_le_mul_of_nonneg_right hK_le (by positivity)
      _ = 20 / L := by field_simp [hLpos.ne']; ring
      _ ≤ 1 := (div_le_one hLpos).mpr (by linarith)

/-- Band 2 bound via `Chebyshev.theta_le_log4_mul_x`:
    for all sufficiently large `n`, `∑_{p ∈ Ioc ⌊n^(1/100)⌋ n, p.Prime} (1 / p) ≤ 500`. -/
private lemma band2_chebyshev_bound :
    ∀ᶠ n : ℕ in atTop,
      ∑ p ∈ (Ioc (Nat.floor ((n : ℝ) ^ ((1 : ℝ) / 100))) n).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤ 500 := by
  have h100_top : Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 100)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).comp tendsto_natCast_atTop_atTop
  filter_upwards [h100_top.eventually_ge_atTop (1000 : ℝ)] with n hn100
  let B := Nat.floor ((n : ℝ) ^ ((1 : ℝ) / 100))
  have hB_ge : 1000 ≤ B := Nat.le_floor hn100
  have hB_le_n : B ≤ n := by
    have hnpos : (0 : ℝ) < n := by
      by_contra hle; push Not at hle
      have hn0 : n = 0 := by exact_mod_cast le_antisymm hle (Nat.cast_nonneg n)
      rw [hn0] at hn100; norm_num at hn100
    have h1 : (n : ℝ) ^ ((1 : ℝ) / 100) ≤ (n : ℝ) := by
      have hn1 : (1 : ℝ) ≤ n := by
        by_contra hlt; push Not at hlt
        have hn_lt1 : n < 1 := by exact_mod_cast hlt
        have hn0 : n = 0 := by omega
        rw [hn0] at hn100; norm_num at hn100
      conv_rhs => rw [← Real.rpow_one (n : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    exact_mod_cast (Nat.floor_le (by positivity)).trans h1
  let J₀ := Nat.log 2 B
  let J₁ := Nat.log 2 n
  have hJ₀_pos : 1 ≤ J₀ := by
    have : 2 ^ 1 ≤ B := by omega
    exact Nat.le_log_of_pow_le (by norm_num) this
  have hJ₀_le_J₁ : J₀ ≤ J₁ := Nat.log_mono_right hB_le_n
  -- Show J₁ ≤ 102 * J₀ (since 2^(J₀ + 1) > B ≥ n^(1/100) / 2, so n ≤ (2^(J₀+2))^100 = 2^(100*J₀ + 200))
  have hJ₁_le : J₁ ≤ 125 * J₀ := by
    have hB_ge_half : (n : ℝ) ^ ((1 : ℝ) / 100) ≤ 2 * (B : ℝ) := by
      have h1 := Nat.lt_floor_add_one ((n : ℝ) ^ ((1 : ℝ) / 100))
      have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
      linarith
    have hB_lt : (B : ℝ) < (2 : ℝ) ^ (J₀ + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) B
    have hn_le : (n : ℝ) ≤ ((2 : ℝ) ^ (J₀ + 2)) ^ (100 : ℕ) := by
      have h1 : (n : ℝ) ^ ((1 : ℝ) / 100) ≤ (2 : ℝ) ^ (J₀ + 2) := by
        rw [pow_succ]; linarith
      have h2 := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg n) _) h1 100
      rw [← Real.rpow_natCast ((n : ℝ) ^ _), ← Real.rpow_mul (Nat.cast_nonneg n)] at h2
      norm_num at h2; exact h2
    have hn_nat : n ≤ 2 ^ (100 * (J₀ + 2)) := by
      rw [← pow_mul] at hn_le
      have : (n : ℝ) ≤ ((2 ^ ((J₀ + 2) * 100) : ℕ) : ℝ) := by push_cast; exact hn_le
      have hnat : n ≤ 2 ^ ((J₀ + 2) * 100) := by exact_mod_cast this
      rwa [mul_comm] at hnat
    have hJ₁_bd : J₁ ≤ 100 * (J₀ + 2) := by
      have h1 : 2 ^ J₁ ≤ 2 ^ (100 * (J₀ + 2)) :=
        le_trans (Nat.pow_log_le_self 2 (by omega : n ≠ 0)) hn_nat
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    have hJ₀_ge9 : 9 ≤ J₀ := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
    omega
  -- Cover Ioc B n by dyadic intervals Ioc (2^j) (2^(j+1)) for j ∈ Icc J₀ J₁
  have hcover : (Ioc B n).filter Nat.Prime ⊆ (Icc J₀ J₁).biUnion (fun j => (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime) := by
    intro p hp
    obtain ⟨hp_ioc, hp_pr⟩ := mem_filter.mp hp
    have hBp := (mem_Ioc.mp hp_ioc).1; have hpn := (mem_Ioc.mp hp_ioc).2
    let j := Nat.log 2 (p - 1)
    have hj_pow : 2 ^ j ≤ p - 1 := Nat.pow_log_le_self 2 (by omega)
    have hj_lt : p - 1 < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) (p - 1)
    refine mem_biUnion.mpr ⟨j, mem_Icc.mpr ⟨Nat.log_mono_right (by omega), Nat.log_mono_right (by omega)⟩,
      mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, hp_pr⟩⟩
  -- Bound each dyadic block by 4 / j using Chebyshev.theta_le_log4_mul_x!
  have hblk_cheb : ∀ j ∈ Icc J₀ J₁,
      ∑ p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤ 4 / (j : ℝ) := by
    intro j hj
    have hj1 : 1 ≤ j := le_trans hJ₀_pos (mem_Icc.mp hj).1
    have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hden_pos : (0 : ℝ) < (2 : ℝ) ^ j * ((j : ℝ) * Real.log 2) := by positivity
    have hterm : ∀ p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) ≤ Real.log (p : ℝ) / ((2 : ℝ) ^ j * ((j : ℝ) * Real.log 2)) := by
      intro p hp
      have hp_ioc := (mem_filter.mp hp).1
      have hp_gt : 2 ^ j < p := (mem_Ioc.mp hp_ioc).1
      have hp_ge : (2 : ℝ) ^ j ≤ (p : ℝ) := by exact_mod_cast hp_gt.le
      have hlog_ge : (j : ℝ) * Real.log 2 ≤ Real.log (p : ℝ) := by
        have h1 := Real.log_le_log (by positivity) hp_ge
        rwa [Real.log_pow] at h1
      rw [div_le_div_iff₀ (by exact_mod_cast (mem_filter.mp hp).2.pos) hden_pos]
      nlinarith [mul_le_mul hp_ge hlog_ge (by positivity) (by positivity)]
    have htheta := Chebyshev.theta_le_log4_mul_x (x := ((2 ^ (j + 1) : ℕ) : ℝ)) (by positivity)
    have hsub_th : (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime ⊆ (Ioc 0 (2 ^ (j + 1))).filter Nat.Prime :=
      filter_subset_filter _ (Ioc_subset_Ioc_left (Nat.zero_le _))
    have hsum_log : ∑ p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, Real.log (p : ℝ) ≤
        Real.log 4 * ((2 ^ (j + 1) : ℕ) : ℝ) := by
      have h1 : ∑ p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, Real.log (p : ℝ) ≤
          θ ((2 ^ (j + 1) : ℕ) : ℝ) := by
        dsimp only [Chebyshev.theta]
        rw [Nat.floor_natCast]
        exact sum_le_sum_of_subset_of_nonneg hsub_th
          (fun p hp _ => Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le))
      exact h1.trans htheta
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
    calc ∑ p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
        ≤ ∑ p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime,
            Real.log (p : ℝ) / ((2 : ℝ) ^ j * ((j : ℝ) * Real.log 2)) := sum_le_sum hterm
      _ = (∑ p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, Real.log (p : ℝ)) /
            ((2 : ℝ) ^ j * ((j : ℝ) * Real.log 2)) := (Finset.sum_div _ _ _).symm
      _ ≤ (Real.log 4 * ((2 ^ (j + 1) : ℕ) : ℝ)) / ((2 : ℝ) ^ j * ((j : ℝ) * Real.log 2)) :=
            div_le_div_of_nonneg_right hsum_log hden_pos.le
      _ = 4 / (j : ℝ) := by
            rw [hlog4, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
            field_simp [hlog2_pos.ne', hjpos.ne', (pow_pos (by norm_num : (0 : ℝ) < 2) j).ne']
            ring
  calc ∑ p ∈ (Ioc B n).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
      ≤ ∑ p ∈ (Icc J₀ J₁).biUnion (fun j => (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime), (1 : ℝ) / (p : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hcover (fun _ _ _ => by positivity)
    _ ≤ ∑ j ∈ Icc J₀ J₁, ∑ p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) :=
        sum_biUnion_le_sum _ _ _ (fun _ => by positivity)
    _ ≤ ∑ j ∈ Icc J₀ J₁, (4 / (j : ℝ)) := sum_le_sum hblk_cheb
    _ ≤ ∑ _j ∈ Icc J₀ J₁, (4 / (J₀ : ℝ)) := sum_le_sum fun j hj =>
        div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hJ₀_pos)
          (by exact_mod_cast (mem_Icc.mp hj).1)
    _ = ((J₁ + 1 - J₀ : ℕ) : ℝ) * (4 / (J₀ : ℝ)) := by simp [Nat.card_Icc]
    _ ≤ (125 * (J₀ : ℝ)) * (4 / (J₀ : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have : J₁ + 1 - J₀ ≤ 125 * J₀ := by omega
        exact_mod_cast this
    _ = 500 := by
        have hJ₀R : (J₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        field_simp [hJ₀R]; ring

/- ### Part 5: Connecting trigonometric modes to `e (h * n / p)` and proving `H2` -/

private lemma cos_two_theta_eq_re_e (n p : ℕ) (hp : 0 < p) :
    Real.cos (2 * (2 * Real.pi * ((n % p : ℕ) : ℝ) / (p : ℝ))) =
      (e (((2 * n : ℕ) : ℝ) / (p : ℝ))).re := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hmod : (((2 * n : ℕ) : ℝ) / (p : ℝ)) =
      2 * ((n % p : ℕ) : ℝ) / (p : ℝ) + (((2 * (n / p) : ℕ) : ℤ) : ℝ) := by
    have hdm : p * (n / p) + n % p = n := Nat.div_add_mod n p
    have hdmR : (p : ℝ) * ((n / p : ℕ) : ℝ) + ((n % p : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hdm
    rw [Int.cast_natCast, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hp0]; linarith
  rw [hmod, e_add, e_int, mul_one]
  dsimp only [e]
  have harg : (2 : ℂ) * ↑Real.pi * Complex.I * ↑(2 * ((n % p : ℕ) : ℝ) / (p : ℝ)) =
      ↑(2 * (2 * Real.pi * ((n % p : ℕ) : ℝ) / (p : ℝ))) * Complex.I := by push_cast; ring
  rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

private lemma sin_theta_eq_im_e (n p : ℕ) (hp : 0 < p) :
    Real.sin (2 * Real.pi * ((n % p : ℕ) : ℝ) / (p : ℝ)) =
      (e (((1 * n : ℕ) : ℝ) / (p : ℝ))).im := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hmod : (((1 * n : ℕ) : ℝ) / (p : ℝ)) =
      ((n % p : ℕ) : ℝ) / (p : ℝ) + (((n / p : ℕ) : ℤ) : ℝ) := by
    have hdm : p * (n / p) + n % p = n := Nat.div_add_mod n p
    have hdmR : (p : ℝ) * ((n / p : ℕ) : ℝ) + ((n % p : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hdm
    rw [one_mul, Int.cast_natCast]
    field_simp [hp0]; linarith
  rw [hmod, e_add, e_int, mul_one]
  dsimp only [e]
  have harg : (2 : ℂ) * ↑Real.pi * Complex.I * ↑(((n % p : ℕ) : ℝ) / (p : ℝ)) =
      ↑(2 * Real.pi * ((n % p : ℕ) : ℝ) / (p : ℝ)) * Complex.I := by push_cast; ring
  rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Main theorem: `OMA.R_Erdos377_erdos_377_variants_ub_R1.H2`. -/
theorem H2_proved : OMA.R_Erdos377_erdos_377_variants_ub_R1.H2 := by
  have hloglog : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hL_top : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [band1_recip_bound, band2_chebyshev_bound,
    hloglog.eventually_ge_atTop (100000 : ℝ),
    hL_top.eventually (eventually_ge_atTop (1000 : ℝ)),
    eventually_ge_atTop 1000] with n hb1 hb2 hll hL1000 hn1000
  dsimp only
  let Bset := n.primesLE.filter (fun (p : ℕ) => (9 / 10 : ℝ) * Real.log (Real.log (n : ℝ)) < Real.log (Real.log (p : ℝ)))
  let θp := fun (p : ℕ) => 2 * Real.pi * ((n % p : ℕ) : ℝ) / (p : ℝ)
  let A : ℕ := Nat.floor (Real.exp ((Real.log (n : ℝ)) ^ ((9 : ℝ) / 10)))
  let C : ℕ := Nat.floor ((n : ℝ) ^ ((1 : ℝ) / 100))
  have hLpos : 0 < Real.log (n : ℝ) := by linarith
  have hA_eq : ∀ p : ℕ, p.Prime →
      ((9 / 10 : ℝ) * Real.log (Real.log (n : ℝ)) < Real.log (Real.log (p : ℝ)) ↔ A < p) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
    have hexp_lhs : Real.exp ((9 / 10 : ℝ) * Real.log (Real.log (n : ℝ))) = (Real.log (n : ℝ)) ^ ((9 : ℝ) / 10) := by
      rw [Real.rpow_def_of_pos hLpos, mul_comm]
    constructor
    · intro hlt
      have h1 := Real.exp_lt_exp.mpr hlt
      rw [hexp_lhs, Real.exp_log hlogp_pos] at h1
      have h2 := Real.exp_lt_exp.mpr h1
      rw [Real.exp_log (by linarith)] at h2
      exact (Nat.floor_lt (Real.exp_pos _).le).mpr h2
    · intro hAp
      have h2 : Real.exp ((Real.log (n : ℝ)) ^ ((9 : ℝ) / 10)) < (p : ℝ) :=
        (Nat.floor_lt (Real.exp_pos _).le).mp hAp
      have h1 := Real.log_lt_log (Real.exp_pos _) h2
      rw [Real.log_exp] at h1
      have h0 := Real.log_lt_log (Real.rpow_pos_of_pos hLpos _) h1
      rwa [← hexp_lhs, Real.log_exp] at h0
  -- Split Bset into B1 = (Ioc A C).filter Nat.Prime and B2 ⊆ (Ioc C n).filter Nat.Prime
  have hA_le_C : A ≤ C := by
    have h1 : Real.exp ((Real.log (n : ℝ)) ^ ((9 : ℝ) / 10)) ≤ (n : ℝ) ^ ((1 : ℝ) / 100) := by
      have hL9 : (Real.log (n : ℝ)) ^ ((9 : ℝ) / 10) ≤ (1 / 100 : ℝ) * Real.log (n : ℝ) := by
        -- log (log n) ≥ 100000 implies log n ≥ e^100000 ≥ 100^10, so (log n)^(1/10) ≥ 100!
        have hL_ge : (100 : ℝ) ^ (10 : ℕ) ≤ Real.log (n : ℝ) := by
          have h1 : (100 : ℝ) ^ (10 : ℕ) ≤ Real.exp 100000 := by
            have : (100 : ℝ) ^ (10 : ℕ) ≤ (2 : ℝ) ^ (100 : ℕ) := by norm_num
            have h2 : (2 : ℝ) ^ (100 : ℕ) ≤ Real.exp 100 := by
              have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
              have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2e 100
              rwa [← Real.exp_nat_mul, show ((100 : ℕ) : ℝ) * 1 = 100 by norm_num] at hpow
            exact (this.trans h2).trans (Real.exp_le_exp.mpr (by norm_num))
          have h2 : Real.exp 100000 ≤ Real.log (n : ℝ) := by
            calc Real.exp 100000 ≤ Real.exp (Real.log (Real.log (n : ℝ))) := Real.exp_le_exp.mpr hll
              _ = Real.log (n : ℝ) := Real.exp_log hLpos
          exact h1.trans h2
        have hL10 : (100 : ℝ) ≤ (Real.log (n : ℝ)) ^ ((1 : ℝ) / 10) := by
          have hr := Real.rpow_le_rpow (by positivity) hL_ge (show (0 : ℝ) ≤ 1 / 10 by norm_num)
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at hr
          norm_num at hr; exact hr
        have hmul := mul_le_mul_of_nonneg_right hL10 (Real.rpow_nonneg hLpos.le ((9 : ℝ) / 10))
        rw [← Real.rpow_add hLpos] at hmul; norm_num at hmul; linarith
      calc Real.exp ((Real.log (n : ℝ)) ^ ((9 : ℝ) / 10))
          ≤ Real.exp ((1 / 100 : ℝ) * Real.log (n : ℝ)) := Real.exp_le_exp.mpr hL9
        _ = (n : ℝ) ^ ((1 : ℝ) / 100) := by
            rw [Real.rpow_def_of_pos (by exact_mod_cast (by omega : 0 < n)), mul_comm]
    exact Nat.floor_mono h1
  have hC_le_n : C ≤ n := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have h1 : (n : ℝ) ^ ((1 : ℝ) / 100) ≤ (n : ℝ) := by
      conv_rhs => rw [← Real.rpow_one (n : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
    exact_mod_cast (Nat.floor_le (by positivity)).trans h1
  have hBset_eq : Bset = ((Ioc A C).filter Nat.Prime) ∪ ((Ioc C n).filter Nat.Prime) := by
    ext p
    simp only [Bset, mem_filter, Nat.mem_primesLE, mem_union, mem_Ioc]
    constructor
    · rintro ⟨⟨hpn, hp⟩, hlt⟩
      have hAp := (hA_eq p hp).mp hlt
      by_cases hpC : p ≤ C
      · exact Or.inl ⟨⟨hAp, hpC⟩, hp⟩
      · exact Or.inr ⟨⟨by omega, hpn⟩, hp⟩
    · rintro (⟨⟨hAp, hpC⟩, hp⟩ | ⟨⟨hCp, hpn⟩, hp⟩)
      · exact ⟨⟨le_trans hpC hC_le_n, hp⟩, (hA_eq p hp).mpr hAp⟩
      · exact ⟨⟨hpn, hp⟩, (hA_eq p hp).mpr (lt_of_le_of_lt hA_le_C hCp)⟩
  have hdisj_B : Disjoint ((Ioc A C).filter Nat.Prime) ((Ioc C n).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have := (mem_Ioc.mp (mem_filter.mp hp1).1).2
    have := (mem_Ioc.mp (mem_filter.mp hp2).1).1
    omega
  -- Band 1 contribution ≤ 3 (use A' = A + 1? Wait: A = ⌊exp(...)⌋ < exp(...), so A + 1 ≥ exp(...)!
  -- Peel off p = A + 1 if it's in Ioc A C, norm ≤ 1 / (A+1) ≤ 1; remaining Ioc (A+1) C uses hb1!)
  have hBand1_cos : ∑ p ∈ (Ioc A C).filter Nat.Prime, Real.cos (2 * θp p) / (p : ℝ) ≤ 2 := by
    have hre : ∑ p ∈ (Ioc A C).filter Nat.Prime, Real.cos (2 * θp p) / (p : ℝ) =
        (∑ p ∈ (Ioc A C).filter Nat.Prime, e (((2 * n : ℕ) : ℝ) / (p : ℝ)) / (p : ℂ)).re := by
      rw [Complex.re_sum]
      refine sum_congr rfl fun p hp => ?_
      have hp_pr := (mem_filter.mp hp).2
      rw [show (p : ℂ) = ((p : ℝ) : ℂ) by norm_cast, Complex.div_ofReal_re, ← cos_two_theta_eq_re_e n p hp_pr.pos]
    rw [hre]
    refine (Complex.re_le_norm _).trans ?_
    by_cases hAC1 : A + 1 ≤ C
    · have hsplit : (Ioc A C).filter Nat.Prime =
          ((Ioc A (A + 1)).filter Nat.Prime) ∪ ((Ioc (A + 1) C).filter Nat.Prime) := by
        ext p; simp only [mem_filter, mem_Ioc, mem_union]
        constructor
        · rintro ⟨⟨h1, h2⟩, hp⟩
          by_cases h : p ≤ A + 1
          · exact Or.inl ⟨⟨h1, h⟩, hp⟩
          · exact Or.inr ⟨⟨by omega, h2⟩, hp⟩
        · rintro (⟨⟨h1, h2⟩, hp⟩ | ⟨⟨h1, h2⟩, hp⟩) <;> exact ⟨⟨by omega, by omega⟩, hp⟩
      have hdisj1 : Disjoint ((Ioc A (A + 1)).filter Nat.Prime) ((Ioc (A + 1) C).filter Nat.Prime) := by
        rw [Finset.disjoint_left]; intro p h1 h2
        have := (mem_Ioc.mp (mem_filter.mp h1).1).2
        have := (mem_Ioc.mp (mem_filter.mp h2).1).1; omega
      rw [hsplit, Finset.sum_union hdisj1]
      have hpt1 : ‖∑ p ∈ (Ioc A (A + 1)).filter Nat.Prime, e (((2 * n : ℕ) : ℝ) / (p : ℝ)) / (p : ℂ)‖ ≤ 1 := by
        calc ‖∑ p ∈ (Ioc A (A + 1)).filter Nat.Prime, _‖
            ≤ ∑ p ∈ (Ioc A (A + 1)).filter Nat.Prime, ‖e (((2 * n : ℕ) : ℝ) / (p : ℝ)) / (p : ℂ)‖ := norm_sum_le _ _
          _ ≤ ∑ _p ∈ (Ioc A (A + 1)).filter Nat.Prime, (1 : ℝ) := sum_le_sum fun p hp => by
              rw [norm_div, norm_e, Complex.norm_natCast]
              exact div_le_one_of_le₀ (by exact_mod_cast (mem_filter.mp hp).2.one_le) (Nat.cast_nonneg _)
          _ = (((Ioc A (A + 1)).filter Nat.Prime).card : ℝ) := by simp
          _ ≤ ((Ioc A (A + 1)).card : ℝ) := by exact_mod_cast card_le_card (filter_subset _ _)
          _ = 1 := by simp
      have hrest := hb1 2 (A + 1) C (by omega) le_rfl
        (by push_cast; dsimp [A]; exact (Nat.lt_floor_add_one _).le)
        (Nat.floor_le (by positivity))
      exact (norm_add_le _ _).trans (by linarith)
    · have hsub : (Ioc A C).filter Nat.Prime ⊆ Ioc A (A + 1) :=
        (filter_subset _ _).trans (Ioc_subset_Ioc_right (by omega))
      calc ‖∑ p ∈ (Ioc A C).filter Nat.Prime, _‖
          ≤ ∑ p ∈ (Ioc A C).filter Nat.Prime, ‖e (((2 * n : ℕ) : ℝ) / (p : ℝ)) / (p : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ _p ∈ (Ioc A C).filter Nat.Prime, (1 : ℝ) := sum_le_sum fun p hp => by
            rw [norm_div, norm_e, Complex.norm_natCast]
            exact div_le_one_of_le₀ (by exact_mod_cast (mem_filter.mp hp).2.one_le) (Nat.cast_nonneg _)
        _ = (((Ioc A C).filter Nat.Prime).card : ℝ) := by simp
        _ ≤ ((Ioc A (A + 1)).card : ℝ) := by exact_mod_cast card_le_card hsub
        _ ≤ 2 := by simp
  have hBand1_sin : ∑ p ∈ (Ioc A C).filter Nat.Prime, Real.sin (θp p) / (p : ℝ) ≤ 2 := by
    have him : ∑ p ∈ (Ioc A C).filter Nat.Prime, Real.sin (θp p) / (p : ℝ) =
        (∑ p ∈ (Ioc A C).filter Nat.Prime, e (((1 * n : ℕ) : ℝ) / (p : ℝ)) / (p : ℂ)).im := by
      rw [Complex.im_sum]
      refine sum_congr rfl fun p hp => ?_
      have hp_pr := (mem_filter.mp hp).2
      rw [show (p : ℂ) = ((p : ℝ) : ℂ) by norm_cast, Complex.div_ofReal_im, ← sin_theta_eq_im_e n p hp_pr.pos]
    rw [him]
    refine (Complex.im_le_norm _).trans ?_
    by_cases hAC1 : A + 1 ≤ C
    · have hsplit : (Ioc A C).filter Nat.Prime =
          ((Ioc A (A + 1)).filter Nat.Prime) ∪ ((Ioc (A + 1) C).filter Nat.Prime) := by
        ext p; simp only [mem_filter, mem_Ioc, mem_union]
        constructor
        · rintro ⟨⟨h1, h2⟩, hp⟩
          by_cases h : p ≤ A + 1
          · exact Or.inl ⟨⟨h1, h⟩, hp⟩
          · exact Or.inr ⟨⟨by omega, h2⟩, hp⟩
        · rintro (⟨⟨h1, h2⟩, hp⟩ | ⟨⟨h1, h2⟩, hp⟩) <;> exact ⟨⟨by omega, by omega⟩, hp⟩
      have hdisj1 : Disjoint ((Ioc A (A + 1)).filter Nat.Prime) ((Ioc (A + 1) C).filter Nat.Prime) := by
        rw [Finset.disjoint_left]; intro p h1 h2
        have := (mem_Ioc.mp (mem_filter.mp h1).1).2
        have := (mem_Ioc.mp (mem_filter.mp h2).1).1; omega
      rw [hsplit, Finset.sum_union hdisj1]
      have hpt1 : ‖∑ p ∈ (Ioc A (A + 1)).filter Nat.Prime, e (((1 * n : ℕ) : ℝ) / (p : ℝ)) / (p : ℂ)‖ ≤ 1 := by
        calc ‖∑ p ∈ (Ioc A (A + 1)).filter Nat.Prime, _‖
            ≤ ∑ p ∈ (Ioc A (A + 1)).filter Nat.Prime, ‖e (((1 * n : ℕ) : ℝ) / (p : ℝ)) / (p : ℂ)‖ := norm_sum_le _ _
          _ ≤ ∑ _p ∈ (Ioc A (A + 1)).filter Nat.Prime, (1 : ℝ) := sum_le_sum fun p hp => by
              rw [norm_div, norm_e, Complex.norm_natCast]
              exact div_le_one_of_le₀ (by exact_mod_cast (mem_filter.mp hp).2.one_le) (Nat.cast_nonneg _)
          _ = (((Ioc A (A + 1)).filter Nat.Prime).card : ℝ) := by simp
          _ ≤ ((Ioc A (A + 1)).card : ℝ) := by exact_mod_cast card_le_card (filter_subset _ _)
          _ = 1 := by simp
      have hrest := hb1 1 (A + 1) C le_rfl (by omega)
        (by push_cast; dsimp [A]; exact (Nat.lt_floor_add_one _).le)
        (Nat.floor_le (by positivity))
      exact (norm_add_le _ _).trans (by linarith)
    · have hsub : (Ioc A C).filter Nat.Prime ⊆ Ioc A (A + 1) :=
        (filter_subset _ _).trans (Ioc_subset_Ioc_right (by omega))
      calc ‖∑ p ∈ (Ioc A C).filter Nat.Prime, _‖
          ≤ ∑ p ∈ (Ioc A C).filter Nat.Prime, ‖e (((1 * n : ℕ) : ℝ) / (p : ℝ)) / (p : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ _p ∈ (Ioc A C).filter Nat.Prime, (1 : ℝ) := sum_le_sum fun p hp => by
            rw [norm_div, norm_e, Complex.norm_natCast]
            exact div_le_one_of_le₀ (by exact_mod_cast (mem_filter.mp hp).2.one_le) (Nat.cast_nonneg _)
        _ = (((Ioc A C).filter Nat.Prime).card : ℝ) := by simp
        _ ≤ ((Ioc A (A + 1)).card : ℝ) := by exact_mod_cast card_le_card hsub
        _ ≤ 2 := by simp
  -- Band 2 contribution ≤ 1500 via Chebyshev
  have hBand2_cos : ∑ p ∈ (Ioc C n).filter Nat.Prime, Real.cos (2 * θp p) / (p : ℝ) ≤ 500 := by
    calc ∑ p ∈ (Ioc C n).filter Nat.Prime, Real.cos (2 * θp p) / (p : ℝ)
        ≤ ∑ p ∈ (Ioc C n).filter Nat.Prime, (1 : ℝ) / (p : ℝ) :=
          sum_le_sum fun p _ => div_le_div_of_nonneg_right (Real.cos_le_one _) (Nat.cast_nonneg _)
      _ ≤ 500 := hb2
  have hBand2_sin : ∑ p ∈ (Ioc C n).filter Nat.Prime, Real.sin (θp p) / (p : ℝ) ≤ 500 := by
    calc ∑ p ∈ (Ioc C n).filter Nat.Prime, Real.sin (θp p) / (p : ℝ)
        ≤ ∑ p ∈ (Ioc C n).filter Nat.Prime, (1 : ℝ) / (p : ℝ) :=
          sum_le_sum fun p _ => div_le_div_of_nonneg_right (Real.sin_le_one _) (Nat.cast_nonneg _)
      _ ≤ 500 := hb2
  -- Combine Band 1 + Band 2 ≤ 1506 ≤ 100000 / 50 ≤ log (log n) / 50!
  change (∑ p ∈ Bset, Real.cos (2 * θp p) / (p : ℝ)) +
    2 * (∑ p ∈ Bset, Real.sin (θp p) / (p : ℝ)) ≤ Real.log (Real.log (n : ℝ)) / 50
  rw [hBset_eq, Finset.sum_union hdisj_B, Finset.sum_union hdisj_B]
  linarith [hBand1_cos, hBand1_sin, hBand2_cos, hBand2_sin, hll]

end

end OMA.Erdos377M4


theorem OMA.solution : OMA.R_Erdos377_erdos_377_variants_ub_R1.H2 :=
  OMA.Erdos377M4.H2_proved
