import OMAStatements.S_oeis_a208599
import Mathlib.SetTheory.Cardinal.Finite

namespace OMA.S_oeis_a208599_Proof

open OMA.S_oeis_a208599 PowerSeries

private def constWord (n : ℕ) : BalancedWord n :=
  ⟨fun _ => ⟨n, by omega⟩, by simp⟩

private lemma vadd_constWord (n : ℕ) (g : Fin 5) : g +ᵥ constWord n = constWord n :=
  rfl

private lemma fixed_imp_const (n : ℕ) (w : BalancedWord n) (g : Fin 5) (hg : g ≠ 0)
    (h : g +ᵥ w = w) : w = constWord n := by
  have hstep : ∀ i : Fin 5, w.1 (i + g) = w.1 i := fun i =>
    congrFun (congrArg Subtype.val h) i
  have hall : ∀ i : Fin 5, w.1 i = w.1 0 := by
    have h1 : w.1 1 = w.1 0 := by
      fin_cases g
      · exact absurd rfl hg
      · exact hstep 0
      · calc w.1 1 = w.1 (4 + 2) := rfl
          _ = w.1 4 := hstep 4
          _ = w.1 (2 + 2) := rfl
          _ = w.1 2 := hstep 2
          _ = w.1 (0 + 2) := rfl
          _ = w.1 0 := hstep 0
      · calc w.1 1 = w.1 (3 + 3) := rfl
          _ = w.1 3 := hstep 3
          _ = w.1 (0 + 3) := rfl
          _ = w.1 0 := hstep 0
      · calc w.1 1 = w.1 (2 + 4) := rfl
          _ = w.1 2 := hstep 2
          _ = w.1 (3 + 4) := rfl
          _ = w.1 3 := hstep 3
          _ = w.1 (4 + 4) := rfl
          _ = w.1 4 := hstep 4
          _ = w.1 (0 + 4) := rfl
          _ = w.1 0 := hstep 0
    have h2 : w.1 2 = w.1 0 := by
      fin_cases g
      · exact absurd rfl hg
      · exact (hstep 1).trans h1
      · exact hstep 0
      · calc w.1 2 = w.1 (4 + 3) := rfl
          _ = w.1 4 := hstep 4
          _ = w.1 (1 + 3) := rfl
          _ = w.1 1 := hstep 1
          _ = w.1 0 := h1
      · calc w.1 2 = w.1 (3 + 4) := rfl
          _ = w.1 3 := hstep 3
          _ = w.1 (4 + 4) := rfl
          _ = w.1 4 := hstep 4
          _ = w.1 (0 + 4) := rfl
          _ = w.1 0 := hstep 0
    have h3 : w.1 3 = w.1 0 := by
      fin_cases g
      · exact absurd rfl hg
      · exact (hstep 2).trans h2
      · exact (hstep 1).trans h1
      · exact hstep 0
      · calc w.1 3 = w.1 (4 + 4) := rfl
          _ = w.1 4 := hstep 4
          _ = w.1 (0 + 4) := rfl
          _ = w.1 0 := hstep 0
    have h4 : w.1 4 = w.1 0 := by
      fin_cases g
      · exact absurd rfl hg
      · exact (hstep 3).trans h3
      · exact (hstep 2).trans h2
      · exact (hstep 1).trans h1
      · exact hstep 0
    intro i
    fin_cases i
    · rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have hsum : ∑ i : Fin 5, (w.1 i).val = 5 * n := w.2
  rw [Fin.sum_univ_five] at hsum
  have h01 := congrArg Fin.val (hall 1)
  have h02 := congrArg Fin.val (hall 2)
  have h03 := congrArg Fin.val (hall 3)
  have h04 := congrArg Fin.val (hall 4)
  have h0val : (w.1 0).val = n := by omega
  apply Subtype.ext
  funext i
  apply Fin.ext
  rw [hall i]
  exact h0val

private lemma burnside_five (n : ℕ) :
    5 * necklaceCount n = Fintype.card (BalancedWord n) + 4 := by
  classical
  let r := AddAction.orbitRel (Fin 5) (BalancedWord n)
  let Q := Quotient r
  let q0 : Q := Quotient.mk r (constWord n)
  have hcardQ : necklaceCount n = Fintype.card Q := by
    unfold necklaceCount
    exact Nat.card_eq_fintype_card
  rw [hcardQ]
  have hpart : Fintype.card (BalancedWord n) =
      ∑ q : Q, (Finset.univ.filter fun w : BalancedWord n => Quotient.mk r w = q).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun w _ => Finset.mem_univ (Quotient.mk r w))
  have hfib0 :
      (Finset.univ.filter fun w : BalancedWord n => Quotient.mk r w = q0).card = 1 := by
    have hset : (Finset.univ.filter fun w : BalancedWord n => Quotient.mk r w = q0) =
        {constWord n} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        have hrel : r.r w (constWord n) := Quotient.exact h
        rcases hrel with ⟨g, hg⟩
        dsimp only at hg
        rw [vadd_constWord] at hg
        exact hg.symm
      · intro hw
        subst hw
        rfl
    rw [hset, Finset.card_singleton]
  have hfib_ne : ∀ q : Q, q ≠ q0 →
      (Finset.univ.filter fun w : BalancedWord n => Quotient.mk r w = q).card = 5 := by
    intro q hq
    obtain ⟨w, rfl⟩ := Quotient.exists_rep q
    have hw0 : w ≠ constWord n := fun heq => hq (by rw [heq])
    have hbij :
        (Finset.univ.filter fun u : BalancedWord n => Quotient.mk r u = Quotient.mk r w).card =
        (Finset.univ : Finset (Fin 5)).card := by
      symm
      refine Finset.card_bij (fun g _ => g +ᵥ w)
        (fun g _ => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact Quotient.sound ⟨g, rfl⟩)
        (fun g1 _ g2 _ h => by
          by_contra hne
          have hsub : (g1 - g2) +ᵥ w = w := by
            have h1 : (-g2) +ᵥ (g1 +ᵥ w) = (-g2) +ᵥ (g2 +ᵥ w) := congrArg ((-g2) +ᵥ ·) h
            rw [← add_vadd, ← add_vadd, neg_add_cancel, zero_vadd] at h1
            rwa [show -g2 + g1 = g1 - g2 by abel] at h1
          exact hw0 (fixed_imp_const n w (g1 - g2) (sub_ne_zero.2 hne) hsub))
        (fun u hu => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
          obtain ⟨g, hg⟩ := Quotient.exact hu
          exact ⟨g, Finset.mem_univ g, hg⟩)
    rw [hbij, Finset.card_fin]
  rw [hpart, ← Finset.add_sum_erase _ _ (Finset.mem_univ q0), hfib0]
  have hsum :
      (∑ q ∈ Finset.univ.erase q0,
        (Finset.univ.filter fun w : BalancedWord n => Quotient.mk r w = q).card) =
      ∑ _q ∈ Finset.univ.erase q0, 5 := by
    refine Finset.sum_congr rfl fun q hq => hfib_ne q (Finset.mem_erase.1 hq).1
  rw [hsum, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ q0),
      Finset.card_univ, smul_eq_mul]
  have hpos : 1 ≤ Fintype.card Q := Fintype.card_pos_iff.2 ⟨q0⟩
  omega

private noncomputable def S (n : ℕ) : PowerSeries ℤ :=
  ∑ k ∈ Finset.range (2 * n + 1), X ^ k

private lemma coeff_mul_S (n : ℕ) (F : PowerSeries ℤ) (m : ℕ) :
    PowerSeries.coeff m (F * S n) =
      ∑ k ∈ Finset.range (2 * n + 1), if k ≤ m then PowerSeries.coeff (m - k) F else 0 := by
  unfold S
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [PowerSeries.coeff_mul_X_pow']

private lemma coeff_S_pow (n r m : ℕ) :
    PowerSeries.coeff m (S n ^ r) =
      (((Finset.univ : Finset (Fin r → Fin (2 * n + 1))).filter
        (fun w => ∑ i, (w i).val = m)).card : ℤ) := by
  induction r generalizing m with
  | zero =>
    rw [pow_zero, PowerSeries.coeff_one]
    by_cases hm : m = 0
    · subst hm
      simp
    · simp only [hm, ↓reduceIte]
      have hemp : ((Finset.univ : Finset (Fin 0 → Fin (2 * n + 1))).filter
          (fun w => ∑ i, (w i).val = m)) = ∅ := by
        ext w
        simp [hm, eq_comm]
      rw [hemp, Finset.card_empty]
      rfl
  | succ r ih =>
    rw [pow_succ, coeff_mul_S]
    have hstep :
        (∑ k ∈ Finset.range (2 * n + 1),
          if k ≤ m then PowerSeries.coeff (m - k) (S n ^ r) else 0) =
        ∑ a : Fin (2 * n + 1),
          (((Finset.univ : Finset (Fin r → Fin (2 * n + 1))).filter
            (fun w => ∑ i, (w i).val + a.val = m)).card : ℤ) := by
      rw [Fin.sum_univ_eq_sum_range (fun k =>
        (((Finset.univ : Finset (Fin r → Fin (2 * n + 1))).filter
          (fun w => ∑ i, (w i).val + k = m)).card : ℤ))]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hkm : k ≤ m
      · simp only [hkm, ↓reduceIte, ih (m - k)]
        congr 2
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      · simp only [hkm, ↓reduceIte]
        have hemp : ((Finset.univ : Finset (Fin r → Fin (2 * n + 1))).filter
            (fun w => ∑ i, (w i).val + k = m)) = ∅ := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          omega
        rw [hemp, Finset.card_empty]
        rfl
    rw [hstep, ← Nat.cast_sum]
    congr 1
    have hbij :
        ((Finset.univ : Finset (Fin (r + 1) → Fin (2 * n + 1))).filter
          (fun w => ∑ i, (w i).val = m)).card =
        ∑ a : Fin (2 * n + 1),
          ((Finset.univ : Finset (Fin r → Fin (2 * n + 1))).filter
            (fun w => ∑ i, (w i).val + a.val = m)).card := by
      rw [← Finset.card_sigma]
      refine Finset.card_bij
        (fun w _ => ⟨w 0, fun i => w i.succ⟩)
        (fun w hw => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sigma] at hw ⊢
          rw [Fin.sum_univ_succ] at hw
          omega)
        (fun w1 _ w2 _ h => by
          simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
          funext i
          refine Fin.cases h.1 (fun k => congrFun h.2 k) i)
        (fun p hp => by
          simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hp
          refine ⟨Fin.cons p.1 p.2, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [Fin.sum_univ_succ]
            simp only [Fin.cons_zero, Fin.cons_succ]
            omega
          · rfl)
    exact hbij.symm

private lemma S_mul_one_sub_X (n : ℕ) :
    S n * (1 - X : PowerSeries ℤ) = 1 - X ^ (2 * n + 1) := by
  unfold S
  have h : ∀ N : ℕ, (∑ k ∈ Finset.range N, (X : PowerSeries ℤ) ^ k) * (1 - X) = 1 - X ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, add_mul, ih]
      ring
  exact h (2 * n + 1)

private noncomputable def binomSeries (d : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun m => ((m + d).choose d : ℤ)

private lemma binomSeries_mul_one_sub_X (d : ℕ) :
    binomSeries (d + 1) * (1 - X : PowerSeries ℤ) = binomSeries d := by
  ext m
  have hL : PowerSeries.coeff m (binomSeries (d + 1) * (1 - X : PowerSeries ℤ)) =
      PowerSeries.coeff m (binomSeries (d + 1)) -
        PowerSeries.coeff m (binomSeries (d + 1) * X ^ 1) := by
    have hring : binomSeries (d + 1) * (1 - X : PowerSeries ℤ) =
        binomSeries (d + 1) - binomSeries (d + 1) * X ^ 1 := by ring
    rw [hring, map_sub]
  rw [hL, PowerSeries.coeff_mul_X_pow']
  unfold binomSeries
  simp only [PowerSeries.coeff_mk]
  cases m with
  | zero => simp
  | succ m =>
    simp only [show 1 ≤ m + 1 by omega, ↓reduceIte, show m + 1 - 1 = m by omega]
    have hp : (m + 1 + (d + 1)).choose (d + 1) = (m + (d + 1)).choose d + (m + (d + 1)).choose (d + 1) := by
      rw [show m + 1 + (d + 1) = (m + (d + 1)) + 1 by omega, Nat.choose_succ_succ]
    have hq : m + (d + 1) = m + 1 + d := by omega
    rw [hp, hq]
    push_cast
    ring

private lemma binomSeries4_mul :
    binomSeries 4 * (1 - X : PowerSeries ℤ) ^ 5 = 1 := by
  have h0 : binomSeries 0 * (1 - X : PowerSeries ℤ) = 1 := by
    ext m
    have hring : binomSeries 0 * (1 - X : PowerSeries ℤ) =
        binomSeries 0 - binomSeries 0 * X ^ 1 := by ring
    rw [hring, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_one]
    unfold binomSeries
    simp only [PowerSeries.coeff_mk, Nat.choose_zero_right]
    cases m with
    | zero => simp
    | succ m => simp
  calc
    binomSeries 4 * (1 - X : PowerSeries ℤ) ^ 5
        = ((((binomSeries 4 * (1 - X)) * (1 - X)) * (1 - X)) * (1 - X)) * (1 - X) := by ring
    _ = (((binomSeries 3 * (1 - X)) * (1 - X)) * (1 - X)) * (1 - X) := by
          rw [binomSeries_mul_one_sub_X 3]
    _ = ((binomSeries 2 * (1 - X)) * (1 - X)) * (1 - X) := by
          rw [binomSeries_mul_one_sub_X 2]
    _ = (binomSeries 1 * (1 - X)) * (1 - X) := by
          rw [binomSeries_mul_one_sub_X 1]
    _ = binomSeries 0 * (1 - X) := by
          rw [binomSeries_mul_one_sub_X 0]
    _ = 1 := h0

private lemma card_balancedWord_eq (n : ℕ) (hn : 1 ≤ n) :
    (Fintype.card (BalancedWord n) : ℤ) =
      ((5 * n + 4).choose 4 : ℤ) - 5 * ((3 * n + 3).choose 4 : ℤ) +
        10 * ((n + 2).choose 4 : ℤ) := by
  have hcard : (Fintype.card (BalancedWord n) : ℤ) = PowerSeries.coeff (5 * n) (S n ^ 5) := by
    rw [coeff_S_pow n 5 (5 * n)]
    congr 1
    unfold BalancedWord
    rw [Fintype.card_subtype]
  rw [hcard]
  have hid : S n ^ 5 = (1 - X ^ (2 * n + 1) : PowerSeries ℤ) ^ 5 * binomSeries 4 := by
    calc
      S n ^ 5 = S n ^ 5 * 1 := (mul_one _).symm
      _ = S n ^ 5 * (binomSeries 4 * (1 - X) ^ 5) := by rw [binomSeries4_mul]
      _ = (S n * (1 - X)) ^ 5 * binomSeries 4 := by ring
      _ = (1 - X ^ (2 * n + 1)) ^ 5 * binomSeries 4 := by rw [S_mul_one_sub_X n]
  rw [hid]
  have hexp : (1 - X ^ (2 * n + 1) : PowerSeries ℤ) ^ 5 * binomSeries 4 =
      binomSeries 4
      - C (5 : ℤ) * (binomSeries 4 * X ^ (2 * n + 1))
      + C (10 : ℤ) * (binomSeries 4 * X ^ (4 * n + 2))
      - C (10 : ℤ) * (binomSeries 4 * X ^ (6 * n + 3))
      + C (5 : ℤ) * (binomSeries 4 * X ^ (8 * n + 4))
      - binomSeries 4 * X ^ (10 * n + 5) := by
    have h2 : (X ^ (2 * n + 1) : PowerSeries ℤ) ^ 2 = X ^ (4 * n + 2) := by
      rw [← pow_mul]; congr 1; omega
    have h3 : (X ^ (2 * n + 1) : PowerSeries ℤ) ^ 3 = X ^ (6 * n + 3) := by
      rw [← pow_mul]; congr 1; omega
    have h4 : (X ^ (2 * n + 1) : PowerSeries ℤ) ^ 4 = X ^ (8 * n + 4) := by
      rw [← pow_mul]; congr 1; omega
    have h5 : (X ^ (2 * n + 1) : PowerSeries ℤ) ^ 5 = X ^ (10 * n + 5) := by
      rw [← pow_mul]; congr 1; omega
    simp only [map_ofNat]
    calc
      (1 - X ^ (2 * n + 1) : PowerSeries ℤ) ^ 5 * binomSeries 4
          = (1 - 5 * X ^ (2 * n + 1) + 10 * (X ^ (2 * n + 1)) ^ 2 -
              10 * (X ^ (2 * n + 1)) ^ 3 + 5 * (X ^ (2 * n + 1)) ^ 4 -
              (X ^ (2 * n + 1)) ^ 5) * binomSeries 4 := by ring
      _ = (1 - 5 * X ^ (2 * n + 1) + 10 * X ^ (4 * n + 2) -
            10 * X ^ (6 * n + 3) + 5 * X ^ (8 * n + 4) -
            X ^ (10 * n + 5)) * binomSeries 4 := by rw [h2, h3, h4, h5]
      _ = _ := by ring
  rw [hexp]
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow']
  simp only [show 2 * n + 1 ≤ 5 * n by omega,
    show ¬ (6 * n + 3 ≤ 5 * n) by omega,
    show ¬ (8 * n + 4 ≤ 5 * n) by omega,
    show ¬ (10 * n + 5 ≤ 5 * n) by omega,
    ↓reduceIte, mul_zero, sub_zero, add_zero]
  by_cases hn2 : 2 ≤ n
  · simp only [show 4 * n + 2 ≤ 5 * n by omega, ↓reduceIte, binomSeries, PowerSeries.coeff_mk,
      show 5 * n - (2 * n + 1) + 4 = 3 * n + 3 by omega,
      show 5 * n - (4 * n + 2) + 4 = n + 2 by omega]
  · have hn1 : n = 1 := by omega
    subst hn1
    simp [binomSeries, PowerSeries.coeff_mk]

private lemma choose1_q (k : ℕ) : (k.choose 1 : ℚ) = (k : ℚ) := by simp

private lemma choose2_q (k : ℕ) : (k.choose 2 : ℚ) = (k : ℚ) * ((k : ℚ) - 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ]
    push_cast
    rw [ih, choose1_q]
    ring

private lemma choose3_q (k : ℕ) :
    (k.choose 3 : ℚ) = (k : ℚ) * ((k : ℚ) - 1) * ((k : ℚ) - 2) / 6 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ]
    push_cast
    rw [ih, choose2_q]
    ring

private lemma choose4_q (k : ℕ) :
    (k.choose 4 : ℚ) = (k : ℚ) * ((k : ℚ) - 1) * ((k : ℚ) - 2) * ((k : ℚ) - 3) / 24 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ]
    push_cast
    rw [ih, choose3_q]
    ring

private lemma necklaceCount_poly (n : ℕ) (hn : 1 ≤ n) :
    (necklaceCount n : ℚ) =
      23 / 12 * (n : ℚ) ^ 4 + 23 / 6 * (n : ℚ) ^ 3 + 37 / 12 * (n : ℚ) ^ 2 +
        7 / 6 * (n : ℚ) + 1 := by
  have hb : (5 : ℚ) * (necklaceCount n : ℚ) = (Fintype.card (BalancedWord n) : ℚ) + 4 := by
    exact_mod_cast burnside_five n
  have hc : (Fintype.card (BalancedWord n) : ℚ) =
      ((5 * n + 4).choose 4 : ℚ) - 5 * ((3 * n + 3).choose 4 : ℚ) +
        10 * ((n + 2).choose 4 : ℚ) := by
    exact_mod_cast card_balancedWord_eq n hn
  rw [hc, choose4_q, choose4_q, choose4_q] at hb
  push_cast at hb
  linarith

private theorem main_proved :
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (necklaceCount n : ℚ))) *
        (1 - X)^5 = X * (11 + 22*X + 16*X^2 - 4*X^3 + X^4) ∧
    ∀ n : ℕ, 5 < n → (necklaceCount n : ℚ) =
      5*(necklaceCount (n-1) : ℚ) - 10*(necklaceCount (n-2) : ℚ) +
      10*(necklaceCount (n-3) : ℚ) - 5*(necklaceCount (n-4) : ℚ) +
      (necklaceCount (n-5) : ℚ) := by
  have hrec : ∀ m : ℕ, 1 ≤ m →
      (necklaceCount (m + 5) : ℚ) =
        5 * (necklaceCount (m + 4) : ℚ) - 10 * (necklaceCount (m + 3) : ℚ) +
        10 * (necklaceCount (m + 2) : ℚ) - 5 * (necklaceCount (m + 1) : ℚ) +
        (necklaceCount m : ℚ) := by
    intro m hm
    rw [necklaceCount_poly (m + 5) (by omega), necklaceCount_poly (m + 4) (by omega),
        necklaceCount_poly (m + 3) (by omega), necklaceCount_poly (m + 2) (by omega),
        necklaceCount_poly (m + 1) (by omega), necklaceCount_poly m hm]
    push_cast
    ring
  constructor
  · set F : PowerSeries ℚ :=
      PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (necklaceCount n : ℚ))
    have hD : (1 - X : PowerSeries ℚ) ^ 5 =
        1 - 5 * X + 10 * X ^ 2 - 10 * X ^ 3 + 5 * X ^ 4 - X ^ 5 := by ring
    have hR : X * (11 + 22 * X + 16 * X ^ 2 - 4 * X ^ 3 + X ^ 4 : PowerSeries ℚ) =
        (11 : ℚ) • X + (22 : ℚ) • X ^ 2 + (16 : ℚ) • X ^ 3 - (4 : ℚ) • X ^ 4 + X ^ 5 := by
      simp only [Algebra.smul_def, map_ofNat]
      ring
    ext n
    have hL : PowerSeries.coeff n (F * (1 - X) ^ 5) =
        PowerSeries.coeff n F
        - 5 * PowerSeries.coeff n (F * X ^ 1)
        + 10 * PowerSeries.coeff n (F * X ^ 2)
        - 10 * PowerSeries.coeff n (F * X ^ 3)
        + 5 * PowerSeries.coeff n (F * X ^ 4)
        - PowerSeries.coeff n (F * X ^ 5) := by
      rw [hD]
      have hring : F * (1 - 5 * X + 10 * X ^ 2 - 10 * X ^ 3 + 5 * X ^ 4 - X ^ 5) =
          F - (5 : ℚ) • (F * X ^ 1) + (10 : ℚ) • (F * X ^ 2) - (10 : ℚ) • (F * X ^ 3) +
            (5 : ℚ) • (F * X ^ 4) - (F * X ^ 5) := by
        simp only [Algebra.smul_def, map_ofNat]
        ring
      rw [hring]
      simp only [map_sub, map_add, map_smul, smul_eq_mul]
    rw [hL, hR]
    simp only [map_sub, map_add, map_smul, smul_eq_mul,
      PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
    match n with
    | 0 => simp [F]
    | 1 => norm_num [F, necklaceCount_poly 1 (by omega)]
    | 2 => norm_num [F, necklaceCount_poly 1 (by omega), necklaceCount_poly 2 (by omega)]
    | 3 =>
      norm_num [F, necklaceCount_poly 1 (by omega), necklaceCount_poly 2 (by omega),
        necklaceCount_poly 3 (by omega)]
    | 4 =>
      norm_num [F, necklaceCount_poly 1 (by omega), necklaceCount_poly 2 (by omega),
        necklaceCount_poly 3 (by omega), necklaceCount_poly 4 (by omega)]
    | 5 =>
      norm_num [F, necklaceCount_poly 1 (by omega), necklaceCount_poly 2 (by omega),
        necklaceCount_poly 3 (by omega), necklaceCount_poly 4 (by omega),
        necklaceCount_poly 5 (by omega)]
    | m + 6 =>
      simp only [F, PowerSeries.coeff_mk,
        show 1 ≤ m + 6 by omega, show 2 ≤ m + 6 by omega, show 3 ≤ m + 6 by omega,
        show 4 ≤ m + 6 by omega, show 5 ≤ m + 6 by omega,
        show m + 6 ≠ 1 by omega, show m + 6 ≠ 2 by omega, show m + 6 ≠ 3 by omega,
        show m + 6 ≠ 4 by omega, show m + 6 ≠ 5 by omega,
        show m + 6 ≠ 0 by omega,
        show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
        show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
        show m + 6 - 5 = m + 1 by omega,
        show m + 5 ≠ 0 by omega, show m + 4 ≠ 0 by omega, show m + 3 ≠ 0 by omega,
        show m + 2 ≠ 0 by omega, show m + 1 ≠ 0 by omega,
        ↓reduceIte, mul_zero, sub_zero, add_zero]
      have hr := hrec (m + 1) (by omega)
      have hr' : (necklaceCount (m + 6) : ℚ) =
          5 * (necklaceCount (m + 5) : ℚ) - 10 * (necklaceCount (m + 4) : ℚ) +
          10 * (necklaceCount (m + 3) : ℚ) - 5 * (necklaceCount (m + 2) : ℚ) +
          (necklaceCount (m + 1) : ℚ) := hr
      linarith
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simpa [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
      show m + 5 - 5 = m by omega] using hrec m (by omega)

end OMA.S_oeis_a208599_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a208599.main :=
  OMA.S_oeis_a208599_Proof.main_proved
