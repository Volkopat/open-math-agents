import OMAReductions.R_OeisA217785_conjecture_4_R1
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.CharP.Lemmas

/-!
# Proof of `OeisA217785.conjecture_4.R1.H2`

Proves that for `n = 8 * k * (k + 1)` with `k > 0`, the polynomial
`polyS n = ∑ j ∈ range (n + 1), (j + 1) * X ^ j` is reducible modulo every prime `p`.

We handle four exhaustive cases:
1. `p = 2`: `polyS (2 * m) mod 2 = (∑ j ∈ range (m + 1), X ^ j) ^ 2` is a square of degree `m ≥ 8`.
2. `p ∣ n + 1` (with `p` odd): `polyS n mod p` has degree `n - 1 ≥ 15` and root `1`.
3. `p ∣ 2 * k + 1` (with `p` odd): `polyS n (1) = (n + 1) * (2 * k + 1) ^ 2 ≡ 0 (mod p)` while
   `deg (polyS n mod p) = n ≥ 16`, so `1` is a root.
4. Otherwise `p` is odd and coprime to `(n + 1) * (2 * k + 1)`. If `f = polyS n mod p` were
   irreducible of even degree `n = 8 * k * (k + 1)`, its Frobenius automorphism `φ(x) = x ^ p` on
   `K = AdjoinRoot g` (for monic `g = (n + 1)⁻¹ • f`) cyclically permutes the `n` distinct roots
   `α_j = φ^j(α)` of `g`. Hence `Δ = ∏_{i < j} (α_i - α_j) ≠ 0` satisfies `φ(Δ) = -Δ`, so `Δ ^ 2`
   cannot be a square of an element of `ZMod p`. On the other hand, differentiating
   `(X - 1)^2 * f(X) = (n + 1) X^(n + 2) - (n + 2) X^(n + 1) + 1` gives
   `(α_j - 1) * g'(α_j) = (n + 2) * α_j ^ n`. Taking the product over `j : Fin n` yields
   `g(1) * Δ ^ 2 = (n + 2) ^ n * g(0) ^ n`. Since `g(1) = (2 * k + 1) ^ 2` and `n` is even,
   `Δ ^ 2` is a square in `ZMod p`, contradiction.
-/

namespace OeisA217785Conjecture4R1H2Proof

open Polynomial Finset

private lemma polyS_mul_X_sub_one_sq (n : ℕ) :
    (X - 1) ^ 2 * OeisA217785.polyS n =
      C ((n : ℤ) + 1) * X ^ (n + 2) - C ((n : ℤ) + 2) * X ^ (n + 1) + 1 := by
  induction n with
  | zero =>
    simp [OeisA217785.polyS]
    ring
  | succ m ih =>
    have hstep : OeisA217785.polyS (m + 1) =
        OeisA217785.polyS m + C ((m : ℤ) + 2) * X ^ (m + 1) := by
      unfold OeisA217785.polyS
      rw [Finset.sum_range_succ]
      congr 1
    rw [hstep, mul_add, ih]
    push_cast
    simp only [map_add, map_one, map_ofNat]
    ring

private lemma coeff_polyS (n j : ℕ) :
    (OeisA217785.polyS n).coeff j = if j ≤ n then (j : ℤ) + 1 else 0 := by
  unfold OeisA217785.polyS
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  split_ifs with hj
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb)]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (by omega)) hnot
  · refine Finset.sum_eq_zero fun b hb => ?_
    have hlt : b < n + 1 := Finset.mem_range.mp hb
    rw [if_neg (by omega)]

private lemma eval_one_polyS (n : ℕ) :
    2 * (OeisA217785.polyS n).eval 1 = ((n : ℤ) + 1) * ((n : ℤ) + 2) := by
  induction n with
  | zero =>
    simp [OeisA217785.polyS]
  | succ m ih =>
    have hstep : OeisA217785.polyS (m + 1) =
        OeisA217785.polyS m + C ((m : ℤ) + 2) * X ^ (m + 1) := by
      unfold OeisA217785.polyS
      rw [Finset.sum_range_succ]
      congr 1
    rw [hstep, eval_add, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one, mul_add, ih]
    push_cast
    ring

private lemma eval_zero_polyS (n : ℕ) : (OeisA217785.polyS n).eval 0 = 1 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, coeff_polyS]
  simp

private lemma not_irreducible_of_root_of_one_lt_natDegree {F : Type*} [Field F]
    {f : F[X]} (hdeg : 1 < f.natDegree) (hroot : f.eval 1 = 0) : ¬ Irreducible f := by
  intro hirr
  have hdvd : (X - 1 : F[X]) ∣ f := by
    rw [show (1 : F[X]) = C (1 : F) by simp, dvd_iff_isRoot]
    exact hroot
  obtain ⟨q, hq⟩ := hdvd
  rcases hirr.isUnit_or_isUnit hq with hu | hu
  · have hdeg1 : (X - 1 : F[X]).natDegree = 1 := natDegree_X_sub_C 1
    have hdeg0 : (X - 1 : F[X]).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  · have hdegq : q.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have hne1 : (X - 1 : F[X]) ≠ 0 := X_sub_C_ne_zero 1
    have hneq : q ≠ 0 := hu.ne_zero
    have hdegf : f.natDegree = (X - 1 : F[X]).natDegree + q.natDegree := by
      rw [hq, natDegree_mul hne1 hneq]
    have hdeg1 : (X - 1 : F[X]).natDegree = 1 := natDegree_X_sub_C 1
    omega

private lemma case_p_eq_two (k : ℕ) (hk : 0 < k) :
    let n := 8 * k * (k + 1)
    ¬ Irreducible (Polynomial.map (Int.castRingHom (ZMod 2)) (OeisA217785.polyS n)) := by
  intro n
  set m := 4 * k * (k + 1)
  have hn : n = 2 * m := by dsimp [n, m]; ring
  set q : (ZMod 2)[X] := ∑ j ∈ range (m + 1), X ^ j
  have hsq : Polynomial.map (Int.castRingHom (ZMod 2)) (OeisA217785.polyS n) = q * q := by
    have hq2 : q * q = ∑ j ∈ range (m + 1), (X : (ZMod 2)[X]) ^ (2 * j) := by
      rw [← sq]
      dsimp only [q]
      have h2zero : (2 : (ZMod 2)[X]) = 0 := by
        rw [← map_ofNat (C : ZMod 2 →+* (ZMod 2)[X]) 2, show (2 : ZMod 2) = 0 by decide, map_zero]
      have hsq_sum : ∀ r : ℕ, (∑ j ∈ range r, (X : (ZMod 2)[X]) ^ j) ^ 2 =
          ∑ j ∈ range r, (X : (ZMod 2)[X]) ^ (2 * j) := by
        intro r
        induction r with
        | zero => simp
        | succ r ih =>
          rw [Finset.sum_range_succ, Finset.sum_range_succ]
          calc (∑ j ∈ range r, (X : (ZMod 2)[X]) ^ j + X ^ r) ^ 2
              = (∑ j ∈ range r, (X : (ZMod 2)[X]) ^ j) ^ 2 + (X ^ r) ^ 2 +
                  2 * ((∑ j ∈ range r, (X : (ZMod 2)[X]) ^ j) * X ^ r) := by ring
            _ = (∑ j ∈ range r, (X : (ZMod 2)[X]) ^ (2 * j)) + X ^ (2 * r) := by
                rw [ih, h2zero, zero_mul, add_zero, ← pow_mul, mul_comm]
      exact hsq_sum (m + 1)
    rw [hq2]
    ext r
    rw [coeff_map, coeff_polyS, finsetSum_coeff]
    simp only [coeff_X_pow]
    by_cases hle : r ≤ 2 * m
    · rw [if_pos (by omega)]
      rcases Nat.even_or_odd r with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · have ht : t ∈ range (m + 1) := Finset.mem_range.mpr (by omega)
        rw [Finset.sum_eq_single t]
        · have h1 : t + t = 2 * t := by omega
          rw [if_pos h1]
          have h2 : (((t + t : ℕ) : ℤ) + 1 : ℤ) = 2 * (t : ℤ) + 1 := by push_cast; ring
          rw [show (Int.castRingHom (ZMod 2)) (((t + t : ℕ) : ℤ) + 1) =
            ((2 * (t : ℤ) + 1 : ℤ) : ZMod 2) by rw [h2]; rfl]
          push_cast
          have hchar2 : (2 : ZMod 2) = 0 := by decide
          rw [hchar2, zero_mul, zero_add]
        · intro b _ hb
          rw [if_neg (by omega)]
        · intro hnot; exact absurd ht hnot
      · have hsum0 : ∑ b ∈ range (m + 1), (if 2 * t + 1 = 2 * b then (1 : ZMod 2) else 0) = 0 :=
          Finset.sum_eq_zero fun b _ => if_neg (by omega)
        rw [hsum0]
        have h2 : (((2 * t + 1 : ℕ) : ℤ) + 1 : ℤ) = 2 * ((t : ℤ) + 1) := by push_cast; ring
        rw [show (Int.castRingHom (ZMod 2)) (((2 * t + 1 : ℕ) : ℤ) + 1) =
          ((2 * ((t : ℤ) + 1) : ℤ) : ZMod 2) by rw [h2]; rfl]
        push_cast
        have hchar2 : (2 : ZMod 2) = 0 := by decide
        rw [hchar2, zero_mul]
    · rw [if_neg (by omega), map_zero]
      symm
      refine Finset.sum_eq_zero fun b hb => ?_
      have := Finset.mem_range.mp hb
      rw [if_neg (by omega)]
  intro hirr
  rw [hsq] at hirr
  have hunit : IsUnit q := by
    rcases hirr.isUnit_or_isUnit rfl with h | h <;> exact h
  have hdeg0 : q.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
  have hcoeffm : q.coeff m = 1 := by
    dsimp only [q]
    rw [finsetSum_coeff]
    simp only [coeff_X_pow]
    rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb; rw [if_neg hb.symm]
    · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
  have hge : m ≤ q.natDegree := Polynomial.le_natDegree_of_ne_zero (by rw [hcoeffm]; decide)
  have hm : 8 ≤ m := by dsimp [m]; nlinarith
  omega

private lemma prod_sub_pairs_sq {K : Type*} [CommRing K] {n : ℕ} (a : Fin n → K) :
    (∏ i : Fin n, ∏ j ∈ Finset.univ.erase i, (a i - a j)) =
      (-1 : K) ^ (n * (n - 1) / 2) *
        (∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j : Fin n => i < j), (a i - a j)) ^ 2 := by
  -- Express as product over ordered pairs (i, j) with i ≠ j, split into i < j and j < i
  let P_lt : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 < p.2)
  let P_gt : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.2 < p.1)
  have hdisj : Disjoint P_lt P_gt := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (Finset.mem_filter.mp hp1).2
    have h2 := (Finset.mem_filter.mp hp2).2
    exact lt_asymm h1 h2
  have hunion : P_lt ∪ P_gt = Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2) := by
    ext ⟨i, j⟩
    simp only [P_lt, P_gt, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      ne_iff_lt_or_gt]
  have hlhs : (∏ i : Fin n, ∏ j ∈ Finset.univ.erase i, (a i - a j)) =
      ∏ p ∈ P_lt ∪ P_gt, (a p.1 - a p.2) := by
    rw [hunion]
    rw [show Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2) =
        (Finset.univ.sigma (fun i : Fin n => Finset.univ.erase i)).map
          ⟨fun x => (x.1, x.2), fun x y h => by cases x; cases y; cases h; rfl⟩ by
      ext ⟨i, j⟩
      simp [ne_comm]
      exact ⟨fun h => ⟨i, j, h, rfl⟩,
        fun ⟨a, b, h, heq⟩ => by obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; exact h⟩]
    rw [Finset.prod_map, Finset.prod_sigma]
    rfl
  have hlt_eq : (∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j : Fin n => i < j), (a i - a j)) =
      ∏ p ∈ P_lt, (a p.1 - a p.2) := by
    rw [show P_lt = (Finset.univ.sigma (fun i : Fin n => Finset.univ.filter (fun j : Fin n => i < j))).map
        ⟨fun x => (x.1, x.2), fun x y h => by cases x; cases y; cases h; rfl⟩ by
      ext ⟨i, j⟩
      simp [P_lt]
      exact ⟨fun h => ⟨i, j, h, rfl⟩,
        fun ⟨a, b, h, heq⟩ => by obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; exact h⟩]
    rw [Finset.prod_map, Finset.prod_sigma]
    rfl
  have hgt_eq : ∏ p ∈ P_gt, (a p.1 - a p.2) =
      (-1 : K) ^ P_lt.card * ∏ p ∈ P_lt, (a p.1 - a p.2) := by
    have hbij : ∏ p ∈ P_gt, (a p.1 - a p.2) = ∏ p ∈ P_lt, (-(a p.1 - a p.2)) := by
      refine Finset.prod_nbij Prod.swap ?_ ?_ ?_ ?_
      · intro p hp
        simp only [P_gt, P_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact hp
      · intro p₁ _ p₂ _ h
        exact Prod.swap_injective h
      · intro p hp
        refine ⟨p.swap, ?_, Prod.swap_swap p⟩
        simp only [Finset.mem_coe, P_gt, P_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact hp
      · intro p _
        simp [Prod.swap]
    rw [hbij, Finset.prod_neg]
  have hcard : P_lt.card = n * (n - 1) / 2 := by
    have h2card : P_lt.card + P_gt.card = n * n - n := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
      have hne_card : (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2)).card =
          (Finset.univ : Finset (Fin n × Fin n)).card -
          (Finset.univ.filter (fun p : Fin n × Fin n => p.1 = p.2)).card := by
        have hsum := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin n × Fin n))) (p := fun p => p.1 = p.2)
        simp only [← ne_eq] at hsum
        omega
      rw [hne_card, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
      have hdiag : (Finset.univ.filter (fun p : Fin n × Fin n => p.1 = p.2)).card = n := by
        have : Finset.univ.filter (fun p : Fin n × Fin n => p.1 = p.2) =
            Finset.univ.image (fun i : Fin n => (i, i)) := by
          ext ⟨i, j⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
          constructor
          · rintro rfl; exact ⟨i, rfl, rfl⟩
          · rintro ⟨k, rfl, rfl⟩; rfl
        rw [this, Finset.card_image_of_injective _ (fun x y h => (Prod.mk.inj h).1),
          Finset.card_univ, Fintype.card_fin]
      rw [hdiag]
    have heq_card : P_lt.card = P_gt.card := by
      refine Finset.card_nbij Prod.swap ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_coe, P_gt, P_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact hp
      · intro p₁ _ p₂ _ h; exact Prod.swap_injective h
      · intro p hp
        refine ⟨p.swap, ?_, Prod.swap_swap p⟩
        simp only [Finset.mem_coe, P_gt, P_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact hp
    have hmul : n * n - n = n * (n - 1) := by
      cases n with
      | zero => simp
      | succ m => simp [Nat.mul_succ, Nat.succ_mul]
    omega
  rw [hlhs, Finset.prod_union hdisj, hgt_eq, hlt_eq, hcard]
  ring

private lemma frobenius_delta_sign {K : Type*} [CommRing K] {n : ℕ} (hn : 0 < n)
    (φ : K →+* K) (a : Fin n → K)
    (hshift : ∀ j : Fin n, φ (a j) = a ⟨(j.val + 1) % n, Nat.mod_lt _ hn⟩) :
    φ (∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j : Fin n => i < j), (a i - a j)) =
      (-1 : K) ^ (n - 1) *
        (∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j : Fin n => i < j), (a i - a j)) := by
  let P_lt : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 < p.2)
  have hlt_eq : (∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j : Fin n => i < j), (a i - a j)) =
      ∏ p ∈ P_lt, (a p.1 - a p.2) := by
    rw [show P_lt = (Finset.univ.sigma (fun i : Fin n => Finset.univ.filter (fun j : Fin n => i < j))).map
        ⟨fun x => (x.1, x.2), fun x y h => by cases x; cases y; cases h; rfl⟩ by
      ext ⟨i, j⟩
      simp [P_lt]
      exact ⟨fun h => ⟨i, j, h, rfl⟩,
        fun ⟨a, b, h, heq⟩ => by obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; exact h⟩]
    rw [Finset.prod_map, Finset.prod_sigma]
    rfl
  rw [hlt_eq, map_prod]
  let P1 : Finset (Fin n × Fin n) := P_lt.filter (fun p => p.2.val + 1 < n)
  let P2 : Finset (Fin n × Fin n) := P_lt.filter (fun p => ¬ p.2.val + 1 < n)
  let Q1 : Finset (Fin n × Fin n) := P_lt.filter (fun p => 0 < p.1.val)
  let Q2 : Finset (Fin n × Fin n) := P_lt.filter (fun p => ¬ 0 < p.1.val)
  have hP_split : ∏ p ∈ P_lt, φ (a p.1 - a p.2) =
      (∏ p ∈ P1, φ (a p.1 - a p.2)) * (∏ p ∈ P2, φ (a p.1 - a p.2)) :=
    (Finset.prod_filter_mul_prod_filter_not P_lt (fun p => p.2.val + 1 < n) _).symm
  have hQ_split : ∏ p ∈ P_lt, (a p.1 - a p.2) =
      (∏ p ∈ Q1, (a p.1 - a p.2)) * (∏ p ∈ Q2, (a p.1 - a p.2)) :=
    (Finset.prod_filter_mul_prod_filter_not P_lt (fun p => 0 < p.1.val) _).symm
  have h1 : ∏ p ∈ P1, φ (a p.1 - a p.2) = ∏ q ∈ Q1, (a q.1 - a q.2) := by
    refine Finset.prod_nbij
      (fun p => (⟨(p.1.val + 1) % n, Nat.mod_lt _ hn⟩, ⟨(p.2.val + 1) % n, Nat.mod_lt _ hn⟩))
      ?_ ?_ ?_ ?_
    · intro p hp
      simp only [P1, P_lt, Q1, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      have hlt : p.1.val < p.2.val := hp.1
      have h1lt : p.1.val + 1 < n := by omega
      have h2lt : p.2.val + 1 < n := hp.2
      exact ⟨by change (p.1.val + 1) % n < (p.2.val + 1) % n
                rw [Nat.mod_eq_of_lt h1lt, Nat.mod_eq_of_lt h2lt]; omega,
             by rw [Nat.mod_eq_of_lt h1lt]; omega⟩
    · intro p₁ hp₁ p₂ hp₂ heq
      simp only [Finset.mem_coe, P1, P_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
      have hlt1 : p₁.1.val < p₁.2.val := hp₁.1
      have hlt2 : p₂.1.val < p₂.2.val := hp₂.1
      have h1a : p₁.1.val + 1 < n := by omega
      have h1b : p₁.2.val + 1 < n := hp₁.2
      have h2a : p₂.1.val + 1 < n := by omega
      have h2b : p₂.2.val + 1 < n := hp₂.2
      simp only [Nat.mod_eq_of_lt h1a, Nat.mod_eq_of_lt h1b, Nat.mod_eq_of_lt h2a,
        Nat.mod_eq_of_lt h2b, Prod.mk.injEq, Fin.mk.injEq] at heq
      ext <;> omega
    · intro q hq
      simp only [Finset.mem_coe, Q1, P_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have hlt : q.1.val < q.2.val := hq.1
      have hq1 : 0 < q.1.val := hq.2
      refine ⟨(⟨q.1.val - 1, by omega⟩, ⟨q.2.val - 1, by omega⟩), ?_, ?_⟩
      · simp only [Finset.mem_coe, P1, P_lt, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨by change q.1.val - 1 < q.2.val - 1; omega, by omega⟩
      · ext
        · dsimp only; rw [show q.1.val - 1 + 1 = q.1.val by omega, Nat.mod_eq_of_lt q.1.isLt]
        · dsimp only; rw [show q.2.val - 1 + 1 = q.2.val by omega, Nat.mod_eq_of_lt q.2.isLt]
    · intro p _
      rw [map_sub, hshift, hshift]
  have h2 : ∏ p ∈ P2, φ (a p.1 - a p.2) = (-1 : K) ^ Q2.card * ∏ q ∈ Q2, (a q.1 - a q.2) := by
    have hbij : ∏ p ∈ P2, φ (a p.1 - a p.2) = ∏ q ∈ Q2, (-(a q.1 - a q.2)) := by
      refine Finset.prod_nbij
        (fun p => (⟨0, hn⟩, ⟨(p.1.val + 1) % n, Nat.mod_lt _ hn⟩))
        ?_ ?_ ?_ ?_
      · intro p hp
        simp only [P2, P_lt, Q2, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        have hlt : p.1.val < p.2.val := hp.1
        have hp2 : p.2.val = n - 1 := by omega
        have hp1 : p.1.val + 1 < n := by omega
        exact ⟨by change 0 < (p.1.val + 1) % n; rw [Nat.mod_eq_of_lt hp1]; omega,
               by omega⟩
      · intro p₁ hp₁ p₂ hp₂ heq
        simp only [Finset.mem_coe, P2, P_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
        have hlt1 : p₁.1.val < p₁.2.val := hp₁.1
        have hlt2 : p₂.1.val < p₂.2.val := hp₂.1
        have h1 : p₁.1.val + 1 < n := by omega
        have h2' : p₂.1.val + 1 < n := by omega
        simp only [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2', Prod.mk.injEq, Fin.mk.injEq] at heq
        ext <;> omega
      · intro q hq
        simp only [Finset.mem_coe, Q2, P_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        have hq1 : q.1.val = 0 := by omega
        have hq2 : 0 < q.2.val := by have : q.1.val < q.2.val := hq.1; omega
        refine ⟨(⟨q.2.val - 1, by omega⟩, ⟨n - 1, by omega⟩), ?_, ?_⟩
        · simp only [Finset.mem_coe, P2, P_lt, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨by change q.2.val - 1 < n - 1; omega, by omega⟩
        · ext
          · exact hq1.symm
          · dsimp only; rw [show q.2.val - 1 + 1 = q.2.val by omega, Nat.mod_eq_of_lt q.2.isLt]
      · intro p hp
        simp only [P2, P_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        have hp2 : p.2.val + 1 = n := by omega
        rw [map_sub, hshift, hshift]
        have hmod : (p.2.val + 1) % n = 0 := by rw [hp2, Nat.mod_self]
        have hfin : (⟨(p.2.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨0, hn⟩ := Fin.ext hmod
        rw [hfin]
        ring
    rw [hbij, Finset.prod_neg]
  have hQ2_card : Q2.card = n - 1 := by
    have hbij : Q2 = (Finset.univ.filter (fun j : Fin n => 0 < j.val)).image (fun j => (⟨0, hn⟩, j)) := by
      ext ⟨i, j⟩
      simp only [Q2, P_lt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Prod.mk.injEq]
      constructor
      · rintro ⟨hij, hi0⟩
        have hi : i = ⟨0, hn⟩ := Fin.ext (by dsimp only; omega)
        exact ⟨j, by change i.val < j.val at hij; omega, hi.symm, rfl⟩
      · rintro ⟨j', hj', rfl, rfl⟩
        exact ⟨by change 0 < j'.val; exact hj', by dsimp only; omega⟩
    rw [hbij, Finset.card_image_of_injective _ (fun x y h => (Prod.mk.inj h).2)]
    have hcompl : (Finset.univ.filter (fun j : Fin n => 0 < j.val)) = Finset.univ.erase ⟨0, hn⟩ := by
      ext j
      simp [Fin.ext_iff]
      omega
    rw [hcompl, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  rw [hP_split, h1, h2, hQ2_card, hQ_split]
  ring

private lemma case_odd_coprime (k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp2 : p ≠ 2)
    (hn1 : ((8 * k * (k + 1) + 1 : ℤ) : ZMod p) ≠ 0)
    (hk1 : ((2 * k + 1 : ℤ) : ZMod p) ≠ 0) :
    let n := 8 * k * (k + 1)
    ¬ Irreducible (Polynomial.map (Int.castRingHom (ZMod p)) (OeisA217785.polyS n)) := by
  intro n hirr
  have : Fact p.Prime := ⟨hp⟩
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
    have := Nat.le_of_dvd (by decide) hdvd
    have := hp.two_le
    omega
  set f : (ZMod p)[X] := Polynomial.map (Int.castRingHom (ZMod p)) (OeisA217785.polyS n)
  set a : ZMod p := (((n : ℤ) + 1 : ℤ) : ZMod p)
  have ha : a ≠ 0 := by
    dsimp [a, n]
    simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hn1
  have hf_deg : f.natDegree = n := by
    apply le_antisymm
    · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun j hj => ?_
      rw [coeff_map, coeff_polyS, if_neg (by omega), map_zero]
    · apply Polynomial.le_natDegree_of_ne_zero
      rw [coeff_map, coeff_polyS, if_pos le_rfl]
      exact ha
  have hf_lc : f.leadingCoeff = a := by
    rw [Polynomial.leadingCoeff, hf_deg, coeff_map, coeff_polyS, if_pos le_rfl]
    rfl
  set g : (ZMod p)[X] := C a⁻¹ * f
  have hg_monic : g.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hf_lc,
      inv_mul_cancel₀ ha]
  have hg_deg : g.natDegree = n := by
    rw [Polynomial.natDegree_C_mul (inv_ne_zero ha), hf_deg]
  have hg_irr : Irreducible g := by
    have hunit : IsUnit (C a⁻¹ : (ZMod p)[X]) := Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero ha))
    exact (associated_unit_mul_left f _ hunit).irreducible_iff.mpr hirr
  have : Fact (Irreducible g) := ⟨hg_irr⟩
  let K := AdjoinRoot g
  let emb : ZMod p →+* K := AdjoinRoot.of g
  have hn_pos : 0 < n := by dsimp [n]; nlinarith
  -- K has finite cardinality p ^ n
  let hpb := AdjoinRoot.powerBasis hg_irr.ne_zero
  have : Fintype K := Fintype.ofEquiv (Fin hpb.dim → ZMod p) hpb.basis.equivFun.toEquiv.symm
  have hcardK : Fintype.card K = p ^ n := by
    rw [Fintype.card_congr hpb.basis.equivFun.toEquiv, Fintype.card_fun, ZMod.card p,
      Fintype.card_fin, AdjoinRoot.powerBasis_dim, hg_deg]
  have : CharP K p := charP_of_injective_ringHom emb.injective p
  let α : K := AdjoinRoot.root g
  let φ : K →+* K := frobenius K p
  let roots : Fin n → K := fun j => (φ^[j.val]) α
  have hφ_emb : ∀ c : ZMod p, φ (emb c) = emb c := fun c => by
    change (emb c) ^ p = emb c
    rw [← map_pow, ZMod.pow_card]
  have hφ_aeval : ∀ (h : (ZMod p)[X]) (x : K), φ (Polynomial.aeval x h) = Polynomial.aeval (φ x) h := by
    intro h x
    induction h using Polynomial.induction_on' with
    | add p1 p2 ih1 ih2 => simp [ih1, ih2]
    | monomial d c =>
      simp only [Polynomial.aeval_monomial, map_mul, map_pow]
      have : (algebraMap (ZMod p) K) c = emb c := rfl
      rw [this, hφ_emb]
  have hφ_iter_aeval : ∀ (m : ℕ) (h : (ZMod p)[X]) (x : K),
      (φ^[m]) (Polynomial.aeval x h) = Polynomial.aeval ((φ^[m]) x) h := by
    intro m
    induction m with
    | zero => intro _ _; rfl
    | succ m ih =>
      intro h x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hφ_aeval]
  have hroot_g : ∀ j : Fin n, Polynomial.aeval (roots j) g = 0 := fun j => by
    dsimp only [roots]
    rw [← hφ_iter_aeval]
    have h0 : Polynomial.aeval α g = 0 := AdjoinRoot.eval₂_root g
    have hzero : ∀ m : ℕ, (φ^[m]) 0 = 0 := fun m => by
      induction m with
      | zero => rfl
      | succ m ih => rw [Function.iterate_succ_apply', ih, map_zero]
    rw [h0, hzero]
  have hφ_iter_pow : ∀ (m : ℕ) (x : K), (φ^[m]) x = x ^ (p ^ m) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [Function.iterate_succ_apply', ih]
      change (x ^ p ^ m) ^ p = x ^ p ^ (m + 1)
      rw [← pow_mul, pow_succ]
  -- Pairwise distinctness of roots
  have hroots_inj : Function.Injective roots := by
    intro i j hij
    by_contra hne
    wlog hlt : i.val < j.val generalizing i j
    · exact this hij.symm (Ne.symm hne) (by omega)
    have hφ_inj : Function.Injective φ := φ.injective
    have hiter_inj : Function.Injective (φ^[i.val]) := hφ_inj.iterate i.val
    have hfix_α : (φ^[j.val - i.val]) α = α := by
      apply hiter_inj
      rw [← Function.iterate_add_apply, show i.val + (j.val - i.val) = j.val by omega]
      exact hij.symm
    have hfix_all : ∀ x : K, x ^ (p ^ (j.val - i.val)) = x := by
      intro x
      obtain ⟨h, rfl⟩ := AdjoinRoot.mk_surjective x
      have hmk : AdjoinRoot.mk g h = Polynomial.aeval α h := by
        rw [← AdjoinRoot.aeval_eq]
      rw [hmk, ← hφ_iter_pow, hφ_iter_aeval, hfix_α]
    set d := j.val - i.val
    have hd_lt : d < n := by omega
    have hpoly_ne : (X ^ (p ^ d) - X : K[X]) ≠ 0 := by
      intro h0
      have h1 : (X ^ (p ^ d) - X : K[X]).coeff (p ^ d) = 0 := by rw [h0]; simp
      have hp_gt : 1 < p ^ d := one_lt_pow₀ hp.one_lt (by omega)
      rw [coeff_sub, coeff_X_pow_self, coeff_X, if_neg (by omega), sub_zero] at h1
      exact one_ne_zero h1
    have hcard_le : Fintype.card K ≤ (X ^ (p ^ d) - X : K[X]).natDegree := by
      have hsub : (Finset.univ : Finset K).val ⊆ (X ^ (p ^ d) - X : K[X]).roots := by
        intro x _
        rw [Polynomial.mem_roots hpoly_ne, Polynomial.IsRoot, eval_sub, eval_pow, eval_X,
          hfix_all x, sub_self]
      have hle1 : (Finset.univ : Finset K).card ≤ (X ^ (p ^ d) - X : K[X]).roots.card :=
        Multiset.card_le_card ((Multiset.le_iff_subset (Finset.univ : Finset K).nodup).mpr hsub)
      exact hle1.trans (Polynomial.card_roots' _)
    have hdeg_le : (X ^ (p ^ d) - X : K[X]).natDegree ≤ p ^ d := by
      refine Polynomial.natDegree_sub_le _ _ |>.trans (max_le ?_ ?_)
      · exact Polynomial.natDegree_X_pow_le _
      · exact Polynomial.natDegree_X_le.trans (Nat.one_le_pow _ _ hp.pos)
    have hlt_pow : p ^ d < p ^ n := Nat.pow_lt_pow_right hp.one_lt hd_lt
    omega
  -- Factorization of g.map emb
  have hg_fac : g.map emb = ∏ j : Fin n, (X - C (roots j)) := by
    have hdvd : (∏ j : Fin n, (X - C (roots j))) ∣ g.map emb := by
      refine Finset.prod_dvd_of_coprime ?_ ?_
      · intro i _ j _ hij
        have hne : roots i ≠ roots j := fun h => hij (hroots_inj h)
        exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
      · intro j _
        rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_map]
        exact hroot_g j
    have hmon_prod : (∏ j : Fin n, (X - C (roots j))).Monic :=
      Polynomial.monic_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)
    have hmon_g : (g.map emb).Monic := hg_monic.map emb
    have hdeg_prod : (∏ j : Fin n, (X - C (roots j))).natDegree = n := by
      rw [Polynomial.natDegree_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)]
      simp
    have hdeg_g : (g.map emb).natDegree = n := by
      rw [Polynomial.natDegree_map_eq_of_injective emb.injective, hg_deg]
    exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon_prod hmon_g hdvd (by omega)
  -- Shift property of φ on roots
  have hshift : ∀ j : Fin n, φ (roots j) = roots ⟨(j.val + 1) % n, Nat.mod_lt _ hn_pos⟩ := fun j => by
    dsimp only [roots]
    by_cases hlt : j.val + 1 < n
    · rw [Nat.mod_eq_of_lt hlt, ← Function.iterate_succ_apply' φ j.val α]
    · have hj : j.val + 1 = n := by omega
      rw [hj, Nat.mod_self, Function.iterate_zero_apply, ← Function.iterate_succ_apply' φ j.val α,
        Nat.succ_eq_add_one, hj, hφ_iter_pow, ← hcardK, FiniteField.pow_card]
  -- Define Δ and show φ Δ = -Δ and Δ ≠ 0
  set Δ : K := ∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j : Fin n => i < j), (roots i - roots j)
  have hΔ_ne : Δ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    have hij : i < j := (Finset.mem_filter.mp hj).2
    exact sub_ne_zero.mpr (fun h => ne_of_lt hij (hroots_inj h))
  have hφΔ : φ Δ = -Δ := by
    have h := frobenius_delta_sign hn_pos φ roots hshift
    have hodd : Odd (n - 1) := by
      refine ⟨4 * k * (k + 1) - 1, ?_⟩
      have h1 : 1 ≤ 4 * k * (k + 1) := by nlinarith
      have h2 : n = 2 * (4 * k * (k + 1)) := by dsimp [n]; ring
      omega
    rw [hodd.neg_one_pow, neg_one_mul] at h
    exact h
  have hΔ_not_sq : ∀ c : ZMod p, emb c ^ 2 ≠ Δ ^ 2 := by
    intro c hc
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hc.symm with h | h
    · have h1 : φ Δ = Δ := by rw [h, hφ_emb]
      rw [hφΔ] at h1
      have h2Δ : (2 : K) * Δ = 0 := by linear_combination -h1
      have h2K : (2 : K) ≠ 0 := by
        intro h20
        have : emb (2 : ZMod p) = 0 := by rw [map_ofNat]; exact h20
        exact h2ne (emb.injective (by rw [this, map_zero]))
      exact hΔ_ne ((mul_eq_zero.mp h2Δ).resolve_left h2K)
    · have h1 : φ Δ = Δ := by rw [h, map_neg, hφ_emb]
      rw [hφΔ] at h1
      have h2Δ : (2 : K) * Δ = 0 := by linear_combination -h1
      have h2K : (2 : K) ≠ 0 := by
        intro h20
        have : emb (2 : ZMod p) = 0 := by rw [map_ofNat]; exact h20
        exact h2ne (emb.injective (by rw [this, map_zero]))
      exact hΔ_ne ((mul_eq_zero.mp h2Δ).resolve_left h2K)
  -- Compute ∏ g'(roots j) = Δ^2
  have hderiv_at : ∀ i : Fin n, (g.map emb).derivative.eval (roots i) =
      ∏ j ∈ Finset.univ.erase i, (roots i - roots j) := fun i => by
    rw [hg_fac, ← Finset.mul_prod_erase Finset.univ (fun j => X - C (roots j)) (Finset.mem_univ i),
      Polynomial.derivative_mul]
    simp [Polynomial.eval_prod]
  have hprod_deriv : ∏ i : Fin n, (g.map emb).derivative.eval (roots i) = Δ ^ 2 := by
    simp_rw [hderiv_at]
    rw [prod_sub_pairs_sq roots]
    have heven : Even (n * (n - 1) / 2) := by
      refine ⟨2 * k * (k + 1) * (n - 1), ?_⟩
      have : n * (n - 1) = 2 * (4 * k * (k + 1) * (n - 1)) := by dsimp [n]; ring
      rw [this, Nat.mul_div_right _ (by decide)]
      ring
    rw [heven.neg_one_pow, one_mul]
  -- Algebraic identity for (roots i - 1) * (g.map emb).derivative.eval (roots i)
  have hf_id : (X - 1 : (ZMod p)[X]) ^ 2 * f =
      C a * X ^ (n + 2) - C ((n : ZMod p) + 2) * X ^ (n + 1) + 1 := by
    have h := congrArg (Polynomial.map (Int.castRingHom (ZMod p))) (polyS_mul_X_sub_one_sq n)
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
      Polynomial.map_X, Polynomial.map_one, Polynomial.map_C] at h
    simpa [f, a] using h
  have hg_id : (X - 1 : (ZMod p)[X]) ^ 2 * g =
      X ^ (n + 2) - C (a⁻¹ * ((n : ZMod p) + 2)) * X ^ (n + 1) + C a⁻¹ := by
    dsimp only [g]
    have h1 : (X - 1 : (ZMod p)[X]) ^ 2 * (C a⁻¹ * f) = C a⁻¹ * ((X - 1 : (ZMod p)[X]) ^ 2 * f) := by
      ring
    rw [h1, hf_id]
    simp only [mul_add, mul_sub, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ha, map_one, one_mul, mul_one]
  have hg_idK : (X - 1 : K[X]) ^ 2 * (g.map emb) =
      X ^ (n + 2) - C (emb (a⁻¹ * ((n : ZMod p) + 2))) * X ^ (n + 1) + C (emb a⁻¹) := by
    have h := congrArg (Polynomial.map emb) hg_id
    simpa [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
      Polynomial.map_X, Polynomial.map_one, Polynomial.map_C] using h
  have hg_deriv_idK :
      2 * (X - 1 : K[X]) * (g.map emb) + (X - 1 : K[X]) ^ 2 * (g.map emb).derivative =
        C ((n + 2 : ℕ) : K) * X ^ (n + 1) -
        C (emb (a⁻¹ * ((n : ZMod p) + 2)) * ((n + 1 : ℕ) : K)) * X ^ n := by
    have h := congrArg Polynomial.derivative hg_idK
    simp only [Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_pow, Polynomial.derivative_X_pow, Polynomial.derivative_C,
      Polynomial.derivative_X, Polynomial.derivative_one, add_zero, sub_zero, mul_one,
      Nat.add_sub_cancel, show n + 2 - 1 = n + 1 by omega, show (2 : ℕ) - 1 = 1 by rfl,
      pow_one, Nat.cast_ofNat] at h
    convert h using 1
    · simp only [map_ofNat]
    · simp only [C_mul, C_eq_natCast]
      ring
  have heval1_g : g.eval 1 = ((2 * k + 1 : ℤ) : ZMod p) ^ 2 := by
    have h1 := congrArg (Int.castRingHom (ZMod p)) (eval_one_polyS n)
    have hf1 : f.eval 1 = (Int.castRingHom (ZMod p)) ((OeisA217785.polyS n).eval 1) := by
      rw [Polynomial.eval_map, ← map_one (Int.castRingHom (ZMod p)), Polynomial.eval₂_at_apply]
    have hn2 : ((n : ℤ) + 2 : ℤ) = 2 * ((2 * (k : ℤ) + 1) ^ 2) := by dsimp [n]; ring
    have h2eq : (2 : ZMod p) * f.eval 1 = a * (2 * ((2 * k + 1 : ℤ) : ZMod p) ^ 2) := by
      rw [hf1]
      have h1' : (2 : ZMod p) * (((OeisA217785.polyS n).eval 1 : ℤ) : ZMod p) =
          (((n : ℤ) + 1 : ℤ) : ZMod p) * (((n : ℤ) + 2 : ℤ) : ZMod p) := by
        simpa using h1
      rw [hn2] at h1'
      simpa [a] using h1'
    have hf1_eq : f.eval 1 = a * ((2 * k + 1 : ℤ) : ZMod p) ^ 2 := by
      apply mul_left_cancel₀ h2ne
      linear_combination h2eq
    dsimp only [g]
    rw [eval_mul, eval_C, hf1_eq, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  have heval0_g : g.eval 0 = a⁻¹ := by
    have hf0 : f.eval 0 = 1 := by
      rw [Polynomial.eval_map, ← map_zero (Int.castRingHom (ZMod p)), Polynomial.eval₂_at_apply]
      simpa using congrArg (Int.castRingHom (ZMod p)) (eval_zero_polyS n)
    dsimp only [g]
    rw [eval_mul, eval_C, hf0, mul_one]
  have hroot_ne_one : ∀ i : Fin n, roots i ≠ 1 := fun i hi => by
    have h0 : g.eval 1 = 0 := by
      have h1 : emb (g.eval 1) = 0 := by
        have := hroot_g i
        rw [hi, Polynomial.aeval_def] at this
        have h1' : Polynomial.eval₂ emb (emb 1) g = 0 := by simpa using this
        rwa [Polynomial.eval₂_at_apply] at h1'
      exact emb.injective (by rw [h1, map_zero])
    rw [heval1_g] at h0
    exact hk1 (sq_eq_zero_iff.mp h0)
  have hstep_i : ∀ i : Fin n, (roots i - 1) * (g.map emb).derivative.eval (roots i) =
      emb ((n : ZMod p) + 2) * (roots i) ^ n := fun i => by
    have h := congrArg (Polynomial.eval (roots i)) hg_deriv_idK
    have hg0 : (g.map emb).eval (roots i) = 0 := by
      rw [Polynomial.eval_map]; exact hroot_g i
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_one, eval_C, hg0, mul_zero,
      zero_add] at h
    have hn1_emb : ((n + 1 : ℕ) : K) = emb a := by
      dsimp [a]; simp
    have hn2_emb : ((n + 2 : ℕ) : K) = emb ((n : ZMod p) + 2) := by
      simp [map_ofNat]
    rw [hn1_emb, hn2_emb] at h
    have hsimp : emb (a⁻¹ * ((n : ZMod p) + 2)) * emb a = emb ((n : ZMod p) + 2) := by
      rw [← map_mul, mul_comm a⁻¹, mul_assoc, inv_mul_cancel₀ ha, mul_one]
    rw [hsimp] at h
    have hfac : (roots i - 1) * ((roots i - 1) * (g.map emb).derivative.eval (roots i)) =
        (roots i - 1) * (emb ((n : ZMod p) + 2) * roots i ^ n) := by
      calc (roots i - 1) * ((roots i - 1) * (g.map emb).derivative.eval (roots i))
          = (roots i - 1) ^ 2 * (g.map emb).derivative.eval (roots i) := by ring
        _ = emb ((n : ZMod p) + 2) * roots i ^ (n + 1) -
            emb ((n : ZMod p) + 2) * roots i ^ n := h
        _ = (roots i - 1) * (emb ((n : ZMod p) + 2) * roots i ^ n) := by
            rw [pow_succ]; ring
    exact mul_left_cancel₀ (sub_ne_zero.mpr (hroot_ne_one i)) hfac
  have hprod_id : (∏ i : Fin n, (roots i - 1)) * Δ ^ 2 =
      emb ((n : ZMod p) + 2) ^ n * (∏ i : Fin n, roots i) ^ n := by
    rw [← hprod_deriv, ← Finset.prod_mul_distrib]
    simp_rw [hstep_i]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_pow]
  have hneven : Even n := ⟨4 * k * (k + 1), by dsimp [n]; ring⟩
  have hprod_sub1 : ∏ i : Fin n, (roots i - 1) = emb (((2 * k + 1 : ℤ) : ZMod p) ^ 2) := by
    have h1 := congrArg (Polynomial.eval (1 : K)) hg_fac
    rw [Polynomial.eval_map, ← map_one emb, Polynomial.eval₂_at_apply, Polynomial.eval_prod] at h1
    simp only [eval_sub, eval_X, eval_C, map_one] at h1
    have hsign : ∏ i : Fin n, (1 - roots i) = (-1 : K) ^ n * ∏ i : Fin n, (roots i - 1) := by
      rw [show (∏ i : Fin n, (1 - roots i)) = ∏ i : Fin n, (-(roots i - 1)) from
        Finset.prod_congr rfl fun i _ => by ring, Finset.prod_neg]
      simp
    rw [hsign, hneven.neg_one_pow, one_mul] at h1
    rw [← h1, heval1_g]
  have hprod_0 : ∏ i : Fin n, roots i = emb a⁻¹ := by
    have h0 := congrArg (Polynomial.eval (0 : K)) hg_fac
    rw [Polynomial.eval_map, ← map_zero emb, Polynomial.eval₂_at_apply, Polynomial.eval_prod] at h0
    simp only [eval_sub, eval_X, eval_C, map_zero, zero_sub] at h0
    rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin, hneven.neg_one_pow, one_mul] at h0
    rw [← h0, heval0_g]
  rw [hprod_sub1, hprod_0] at hprod_id
  set m := 4 * k * (k + 1)
  have hnm : n = 2 * m := by dsimp [n, m]; ring
  let c : ZMod p := (((n : ZMod p) + 2) ^ m * (a⁻¹) ^ m) / ((2 * k + 1 : ℤ) : ZMod p)
  apply hΔ_not_sq c
  have h2k_ne : emb ((2 * k + 1 : ℤ) : ZMod p) ^ 2 ≠ 0 := by
    apply pow_ne_zero 2
    intro h0
    exact hk1 (emb.injective (by rw [h0, map_zero]))
  apply mul_left_cancel₀ h2k_ne
  rw [← map_pow, hprod_id]
  simp only [← map_pow, ← map_mul]
  congr 1
  dsimp only [c]
  rw [hnm]
  have h2k_ne' : ((2 * k + 1 : ℤ) : ZMod p) ≠ 0 := hk1
  field_simp [h2k_ne']
  ring

end OeisA217785Conjecture4R1H2Proof

theorem OMA.solution : OMA.R_OeisA217785_conjecture_4_R1.H2 := by
  intro n _ ⟨k, hk, hneq⟩ p hp
  subst hneq
  by_cases hp2 : p = 2
  · subst hp2
    exact OeisA217785Conjecture4R1H2Proof.case_p_eq_two k hk
  have : Fact p.Prime := ⟨hp⟩
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
    have := Nat.le_of_dvd (by decide) hdvd
    have := hp.two_le
    omega
  set m := 8 * k * (k + 1)
  have hm16 : 16 ≤ m := by dsimp [m]; nlinarith
  set f : Polynomial (ZMod p) := Polynomial.map (Int.castRingHom (ZMod p)) (OeisA217785.polyS m)
  by_cases hn1 : ((8 * k * (k + 1) + 1 : ℤ) : ZMod p) = 0
  · apply OeisA217785Conjecture4R1H2Proof.not_irreducible_of_root_of_one_lt_natDegree
    · have hcoeff : f.coeff (m - 1) ≠ 0 := by
        rw [Polynomial.coeff_map, OeisA217785Conjecture4R1H2Proof.coeff_polyS, if_pos (by omega)]
        have h1 : (((m - 1 : ℕ) : ℤ) + 1 : ℤ) = (m : ℤ) := by omega
        rw [show (Int.castRingHom (ZMod p)) (((m - 1 : ℕ) : ℤ) + 1) = ((m : ℤ) : ZMod p) by
          rw [h1]; rfl]
        have hm0 : ((m : ℤ) : ZMod p) = -1 := by
          have : ((m : ℤ) : ZMod p) + 1 = 0 := by
            dsimp [m]; simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hn1
          linear_combination this
        rw [hm0]; exact neg_ne_zero.mpr one_ne_zero
      have hge := Polynomial.le_natDegree_of_ne_zero hcoeff
      omega
    · have h1 := congrArg (Int.castRingHom (ZMod p))
        (OeisA217785Conjecture4R1H2Proof.eval_one_polyS m)
      have hf1 : f.eval 1 = (((OeisA217785.polyS m).eval 1 : ℤ) : ZMod p) := by
        rw [Polynomial.eval_map, ← map_one (Int.castRingHom (ZMod p)), Polynomial.eval₂_at_apply]; rfl
      have h2f : (2 : ZMod p) * f.eval 1 = 0 := by
        rw [hf1]
        have h1' : (2 : ZMod p) * (((OeisA217785.polyS m).eval 1 : ℤ) : ZMod p) =
            (((m : ℤ) + 1 : ℤ) : ZMod p) * (((m : ℤ) + 2 : ℤ) : ZMod p) := by
          simpa using h1
        have hm1 : (((m : ℤ) + 1 : ℤ) : ZMod p) = 0 := by
          dsimp [m]; simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hn1
        rw [h1', hm1, zero_mul]
      exact (mul_eq_zero.mp h2f).resolve_left h2ne
  by_cases hk1 : ((2 * k + 1 : ℤ) : ZMod p) = 0
  · apply OeisA217785Conjecture4R1H2Proof.not_irreducible_of_root_of_one_lt_natDegree
    · have hcoeff : f.coeff m ≠ 0 := by
        rw [Polynomial.coeff_map, OeisA217785Conjecture4R1H2Proof.coeff_polyS, if_pos le_rfl]
        dsimp [m]
        simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hn1
      have hge := Polynomial.le_natDegree_of_ne_zero hcoeff
      omega
    · have h1 := congrArg (Int.castRingHom (ZMod p))
        (OeisA217785Conjecture4R1H2Proof.eval_one_polyS m)
      have hf1 : f.eval 1 = (((OeisA217785.polyS m).eval 1 : ℤ) : ZMod p) := by
        rw [Polynomial.eval_map, ← map_one (Int.castRingHom (ZMod p)), Polynomial.eval₂_at_apply]; rfl
      have hn2 : ((m : ℤ) + 2 : ℤ) = 2 * ((2 * (k : ℤ) + 1) ^ 2) := by dsimp [m]; ring
      have h2f : (2 : ZMod p) * f.eval 1 = 0 := by
        rw [hf1]
        have h1' : (2 : ZMod p) * (((OeisA217785.polyS m).eval 1 : ℤ) : ZMod p) =
            (((m : ℤ) + 1 : ℤ) : ZMod p) * (((m : ℤ) + 2 : ℤ) : ZMod p) := by
          simpa using h1
        rw [hn2] at h1'
        have hk1' : (2 : ZMod p) * (k : ZMod p) + 1 = 0 := by simpa using hk1
        rw [h1']
        push_cast
        rw [hk1']
        ring
      exact (mul_eq_zero.mp h2f).resolve_left h2ne
  exact OeisA217785Conjecture4R1H2Proof.case_odd_coprime k p hk hp hp2 hn1 hk1
