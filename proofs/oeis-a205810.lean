import OMAStatements.S_oeis_a205810
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

namespace OMA.P_oeis_a205810

open OMA.S_oeis_a205810

private lemma aeval_C_int (q : ℚ) (z : ℤ) :
    Polynomial.aeval q (Polynomial.C z) = (z : ℚ) := by
  simp

private lemma aeval_eq_eval_map (q : ℚ) (P : Polynomial ℤ) :
    Polynomial.eval q (P.map (Int.castRingHom ℚ)) = Polynomial.aeval q P := by
  rw [Polynomial.eval_map, Polynomial.aeval_def]
  rfl

/-- Degree bound: `(chebT2 n).coeff j = 0` for `j > n`, i.e., `natDegree ≤ n`. -/
private lemma chebT2_coeff_eq_zero_of_lt : ∀ n j : ℕ, n < j → (chebT2 n).coeff j = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro j hj
    match n with
    | 0 =>
      rw [chebT2, show (2 : Polynomial ℤ) = Polynomial.C 2 by rfl, Polynomial.coeff_C, if_neg (by omega)]
    | 1 =>
      rw [chebT2, Polynomial.coeff_X, if_neg (by omega)]
    | m + 2 =>
      rw [chebT2, Polynomial.coeff_sub]
      cases j with
      | zero => omega
      | succ j' =>
        rw [Polynomial.coeff_X_mul, ih (m + 1) (by omega) j' (by omega),
            ih m (by omega) (j' + 1) (by omega), sub_zero]

private lemma chebT2_natDegree_le (n : ℕ) : (chebT2 n).natDegree ≤ n :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun j hj => chebT2_coeff_eq_zero_of_lt n j hj)

/-- Degree bound for `rowPolyA205810 n`: all coefficients at `k > 2 * n` vanish. -/
private lemma rowPoly_coeff_eq_zero_of_gt (n k : ℕ) (hk : 2 * n < k) :
    (rowPolyA205810 n).coeff k = 0 := by
  unfold rowPolyA205810
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_range] at hj
  have hdeg : (Polynomial.C ((chebT2 n).coeff j) * Polynomial.X ^ (n - j) *
      (1 + Polynomial.X + Polynomial.X ^ 2) ^ j).natDegree ≤ 2 * n := by
    have h1 : (1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ).natDegree ≤ 2 := by
      compute_degree!
    have h2 : ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ) ^ j).natDegree ≤ 2 * j := by
      calc ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ) ^ j).natDegree
          ≤ j * (1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ).natDegree := Polynomial.natDegree_pow_le
        _ ≤ j * 2 := Nat.mul_le_mul_left j h1
        _ = 2 * j := by ring
    have h3 : (Polynomial.C ((chebT2 n).coeff j) * Polynomial.X ^ (n - j)).natDegree ≤ n - j := by
      calc (Polynomial.C ((chebT2 n).coeff j) * Polynomial.X ^ (n - j)).natDegree
          ≤ (Polynomial.C ((chebT2 n).coeff j)).natDegree + (Polynomial.X ^ (n - j) : Polynomial ℤ).natDegree :=
            Polynomial.natDegree_mul_le
        _ ≤ 0 + (n - j) := by simp
        _ = n - j := by omega
    calc (Polynomial.C ((chebT2 n).coeff j) * Polynomial.X ^ (n - j) *
            (1 + Polynomial.X + Polynomial.X ^ 2) ^ j).natDegree
        ≤ (Polynomial.C ((chebT2 n).coeff j) * Polynomial.X ^ (n - j)).natDegree +
            ((1 + Polynomial.X + Polynomial.X ^ 2) ^ j).natDegree := Polynomial.natDegree_mul_le
      _ ≤ (n - j) + 2 * j := Nat.add_le_add h3 h2
      _ ≤ 2 * n := by omega
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- Evaluation of `chebT2 k` at `q + q⁻¹` in `ℚ` (`q ≠ 0`) equals `q^k + (q⁻¹)^k`. -/
private lemma aeval_chebT2 (q : ℚ) (hq : q ≠ 0) :
    ∀ k : ℕ, Polynomial.aeval (q + q⁻¹) (chebT2 k) = q ^ k + (q⁻¹) ^ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 =>
      rw [chebT2]
      simp [show (2 : Polynomial ℤ) = (1 : Polynomial ℤ) + 1 by norm_num]
    | 1 =>
      rw [chebT2]
      simp
    | m + 2 =>
      rw [chebT2, map_sub, map_mul, Polynomial.aeval_X, ih (m + 1) (by omega), ih m (by omega)]
      have hqq : q * q⁻¹ = 1 := mul_inv_cancel₀ hq
      have hq1 : q ^ (m + 2) = q * q ^ (m + 1) := by ring
      have hq2 : q ^ (m + 1) = q * q ^ m := by ring
      have hi1 : (q⁻¹) ^ (m + 2) = q⁻¹ * (q⁻¹) ^ (m + 1) := by ring
      have hi2 : (q⁻¹) ^ (m + 1) = q⁻¹ * (q⁻¹) ^ m := by ring
      calc (q + q⁻¹) * (q ^ (m + 1) + (q⁻¹) ^ (m + 1)) - (q ^ m + (q⁻¹) ^ m)
          = q * q ^ (m + 1) + q⁻¹ * (q⁻¹) ^ (m + 1) +
              (q * q⁻¹) * (q⁻¹) ^ m + (q * q⁻¹) * q ^ m - (q ^ m + (q⁻¹) ^ m) := by
              rw [hq2, hi2]; ring
        _ = q ^ (m + 2) + (q⁻¹) ^ (m + 2) := by rw [hqq, hq1, hi1]; ring

/-- Evaluation of `rowPolyA205810 n` at `q ≠ 0` equals `q^n * aeval (1 + q + q⁻¹) (chebT2 n)`. -/
private lemma aeval_rowPoly (n : ℕ) (q : ℚ) (hq : q ≠ 0) :
    Polynomial.aeval q (rowPolyA205810 n) = q ^ n * Polynomial.aeval (1 + q + q⁻¹) (chebT2 n) := by
  have hsum : Polynomial.aeval (1 + q + q⁻¹) (chebT2 n) =
      ∑ j ∈ Finset.range (n + 1), ((chebT2 n).coeff j : ℚ) * (1 + q + q⁻¹) ^ j := by
    rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le (chebT2_natDegree_le n))]
    simp [Algebra.smul_def]
  rw [hsum, Finset.mul_sum]
  unfold rowPolyA205810
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  simp only [map_mul, map_pow, map_add, map_one, aeval_C_int, Polynomial.aeval_X]
  have hq_eq : 1 + q + q⁻¹ = (1 + q + q ^ 2) / q := by field_simp; ring
  rw [hq_eq, div_pow]
  have hexp : q ^ n = q ^ (n - j) * q ^ j := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
  rw [hexp]
  have hqj : q ^ j ≠ 0 := pow_ne_zero j hq
  field_simp

/-- Two integer polynomials with identical `aeval` on all `m : ℕ` (`m ≥ 1`) are equal. -/
private lemma poly_eq_of_aeval_nat_eq (P Q : Polynomial ℤ)
    (h : ∀ m : ℕ, 1 ≤ m → Polynomial.aeval (m : ℚ) P = Polynomial.aeval (m : ℚ) Q) :
    P = Q := by
  set D : Polynomial ℤ := P - Q
  have hDq : D.map (Int.castRingHom ℚ) = 0 := by
    by_contra hne
    have hfin : ((D.map (Int.castRingHom ℚ)).roots.toFinset : Set ℚ).Finite := Finset.finite_toSet _
    have hinj : Function.Injective (fun m : ℕ => ((m + 1 : ℕ) : ℚ)) := by
      intro a b hab
      dsimp only at hab
      have h1 : a + 1 = b + 1 := by exact_mod_cast hab
      omega
    have hinf : Set.Infinite {x : ℚ | (D.map (Int.castRingHom ℚ)).IsRoot x} := by
      refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective hinj)
      rintro x ⟨m, rfl⟩
      change Polynomial.eval ((m + 1 : ℕ) : ℚ) (D.map (Int.castRingHom ℚ)) = 0
      rw [aeval_eq_eval_map]
      simp only [D, map_sub, h (m + 1) (by omega), sub_self]
    have hsub_roots : {x : ℚ | (D.map (Int.castRingHom ℚ)).IsRoot x} ⊆
        ((D.map (Int.castRingHom ℚ)).roots.toFinset : Set ℚ) := by
      intro x hx
      simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne]
      exact hx
    exact hinf (hfin.subset hsub_roots)
  have hD0 : D = 0 := by
    ext k
    have hk := congrArg (fun R => R.coeff k) hDq
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast, Int.cast_eq_zero] at hk
    exact hk
  exact sub_eq_zero.mp hD0

/-- Palindromicity of `rowPolyA205810 n`: `a205810 n (2 * n - k) = a205810 n k` for `k ≤ 2 * n`. -/
private lemma a205810_symm (n k : ℕ) (hk : k ≤ 2 * n) :
    a205810 n (2 * n - k) = a205810 n k := by
  set P : Polynomial ℤ := rowPolyA205810 n
  set Q : Polynomial ℤ :=
    ∑ j ∈ Finset.range (2 * n + 1), Polynomial.C (P.coeff (2 * n - j)) * Polynomial.X ^ j
  have hPQ : P = Q := by
    apply poly_eq_of_aeval_nat_eq
    intro m hm
    have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hP : Polynomial.aeval (m : ℚ) P =
        (m : ℚ) ^ (2 * n) * Polynomial.aeval ((m : ℚ)⁻¹) P := by
      rw [aeval_rowPoly n (m : ℚ) hm0, aeval_rowPoly n ((m : ℚ)⁻¹) (inv_ne_zero hm0)]
      rw [inv_inv, show 1 + (m : ℚ)⁻¹ + (m : ℚ) = 1 + (m : ℚ) + (m : ℚ)⁻¹ by ring]
      rw [inv_pow, show (m : ℚ) ^ (2 * n) = (m : ℚ) ^ n * (m : ℚ) ^ n by rw [← pow_add]; congr 1; omega]
      field_simp
    have hP_inv : Polynomial.aeval ((m : ℚ)⁻¹) P =
        ∑ j ∈ Finset.range (2 * n + 1), (P.coeff j : ℚ) * ((m : ℚ)⁻¹) ^ j := by
      have hdeg : P.natDegree ≤ 2 * n :=
        Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun j hj => rowPoly_coeff_eq_zero_of_gt n j hj)
      rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hdeg)]
      simp [Algebra.smul_def]
    rw [hP, hP_inv, Finset.mul_sum]
    simp only [Q, map_sum, map_mul, map_pow, aeval_C_int, Polynomial.aeval_X]
    apply Finset.sum_bij (fun j _ => 2 * n - j)
    · intro j hj; rw [Finset.mem_range] at hj ⊢; omega
    · intro j1 h1 j2 h2 heq; rw [Finset.mem_range] at h1 h2; omega
    · intro j hj; rw [Finset.mem_range] at hj
      exact ⟨2 * n - j, Finset.mem_range.mpr (by omega), by omega⟩
    · intro j hj
      rw [Finset.mem_range] at hj
      rw [show 2 * n - (2 * n - j) = j by omega, inv_pow]
      have hexp : (m : ℚ) ^ (2 * n) = (m : ℚ) ^ (2 * n - j) * (m : ℚ) ^ j := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]
      rw [hexp]
      have hmj : (m : ℚ) ^ j ≠ 0 := pow_ne_zero j hm0
      field_simp
  have hc := congrArg (fun R => R.coeff k) hPQ
  simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at hc
  rw [Finset.sum_eq_single k] at hc
  · simpa [a205810, P] using hc.symm
  · intro j _ hne; simp [hne.symm]
  · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot

/-- Two integer polynomials with identical `aeval` at `m + m⁻¹` for all `m ≥ 1` are equal. -/
private lemma poly_eq_of_aeval_add_inv_eq (P Q : Polynomial ℤ)
    (h : ∀ m : ℕ, 1 ≤ m →
      Polynomial.aeval ((m : ℚ) + (m : ℚ)⁻¹) P = Polynomial.aeval ((m : ℚ) + (m : ℚ)⁻¹) Q) :
    P = Q := by
  set D : Polynomial ℤ := P - Q
  have hDq : D.map (Int.castRingHom ℚ) = 0 := by
    by_contra hne
    have hfin : ((D.map (Int.castRingHom ℚ)).roots.toFinset : Set ℚ).Finite := Finset.finite_toSet _
    have hinj : Function.Injective (fun m : ℕ => ((m + 1 : ℕ) : ℚ) + ((m + 1 : ℕ) : ℚ)⁻¹) := by
      intro a b hab
      dsimp only at hab
      have ha : (1 : ℚ) ≤ ((a + 1 : ℕ) : ℚ) := by exact_mod_cast (show 1 ≤ a + 1 by omega)
      have hb : (1 : ℚ) ≤ ((b + 1 : ℕ) : ℚ) := by exact_mod_cast (show 1 ≤ b + 1 by omega)
      have ha0 : ((a + 1 : ℕ) : ℚ) ≠ 0 := by linarith
      have hb0 : ((b + 1 : ℕ) : ℚ) ≠ 0 := by linarith
      have hprod : (((a + 1 : ℕ) : ℚ) - ((b + 1 : ℕ) : ℚ)) *
          (((a + 1 : ℕ) : ℚ) * ((b + 1 : ℕ) : ℚ) - 1) = 0 := by
        have h1 : (((a + 1 : ℕ) : ℚ) + ((a + 1 : ℕ) : ℚ)⁻¹ -
            (((b + 1 : ℕ) : ℚ) + ((b + 1 : ℕ) : ℚ)⁻¹)) *
            (((a + 1 : ℕ) : ℚ) * ((b + 1 : ℕ) : ℚ)) = 0 := by rw [hab, sub_self, zero_mul]
        have h2 : (((a + 1 : ℕ) : ℚ) + ((a + 1 : ℕ) : ℚ)⁻¹ -
            (((b + 1 : ℕ) : ℚ) + ((b + 1 : ℕ) : ℚ)⁻¹)) *
            (((a + 1 : ℕ) : ℚ) * ((b + 1 : ℕ) : ℚ)) =
            (((a + 1 : ℕ) : ℚ) - ((b + 1 : ℕ) : ℚ)) *
            (((a + 1 : ℕ) : ℚ) * ((b + 1 : ℕ) : ℚ) - 1) := by field_simp; ring
        linarith
      rcases mul_eq_zero.mp hprod with hdiff | hmul1
      · have heq : ((a + 1 : ℕ) : ℚ) = ((b + 1 : ℕ) : ℚ) := sub_eq_zero.mp hdiff
        have hnat : a + 1 = b + 1 := by exact_mod_cast heq
        omega
      · have h1 : ((a + 1 : ℕ) : ℚ) * ((b + 1 : ℕ) : ℚ) = 1 := sub_eq_zero.mp hmul1
        have hnat : (a + 1) * (b + 1) = 1 := by exact_mod_cast h1
        have ha1 : a + 1 = 1 := Nat.eq_one_of_mul_eq_one_right hnat
        have hb1 : b + 1 = 1 := Nat.eq_one_of_mul_eq_one_left hnat
        omega
    have hinf : Set.Infinite {x : ℚ | (D.map (Int.castRingHom ℚ)).IsRoot x} := by
      refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective hinj)
      rintro x ⟨m, rfl⟩
      change Polynomial.eval (((m + 1 : ℕ) : ℚ) + ((m + 1 : ℕ) : ℚ)⁻¹) (D.map (Int.castRingHom ℚ)) = 0
      rw [aeval_eq_eval_map]
      simp only [D, map_sub, h (m + 1) (by omega), sub_self]
    have hsub_roots : {x : ℚ | (D.map (Int.castRingHom ℚ)).IsRoot x} ⊆
        ((D.map (Int.castRingHom ℚ)).roots.toFinset : Set ℚ) := by
      intro x hx
      simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne]
      exact hx
    exact hinf (hfin.subset hsub_roots)
  have hD0 : D = 0 := by
    ext k
    have hk := congrArg (fun R => R.coeff k) hDq
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast, Int.cast_eq_zero] at hk
    exact hk
  exact sub_eq_zero.mp hD0

private lemma prove_main :
    ∀ n : ℕ, 1 ≤ n →
      (chebT2 n).comp (Polynomial.X + 1) =
        (∑ k ∈ Finset.range (n + 1), Polynomial.C (a205810 n (n - k)) * chebT2 k) -
          Polynomial.C (a205810 n n) := by
  intro n _
  apply poly_eq_of_aeval_add_inv_eq
  intro m hm
  set q : ℚ := (m : ℚ)
  have hq : q ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hqn : q ^ n ≠ 0 := pow_ne_zero n hq
  have hL : Polynomial.aeval (q + q⁻¹) ((chebT2 n).comp (Polynomial.X + 1)) =
      (q ^ n)⁻¹ * Polynomial.aeval q (rowPolyA205810 n) := by
    rw [Polynomial.aeval_comp, map_add, Polynomial.aeval_X, map_one,
        show q + q⁻¹ + 1 = 1 + q + q⁻¹ by ring, aeval_rowPoly n q hq]
    field_simp
  have hRpoly : Polynomial.aeval q (rowPolyA205810 n) =
      ∑ j ∈ Finset.range (2 * n + 1), (a205810 n j : ℚ) * q ^ j := by
    have hdeg : (rowPolyA205810 n).natDegree ≤ 2 * n :=
      Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun j hj => rowPoly_coeff_eq_zero_of_gt n j hj)
    rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hdeg)]
    simp [a205810, Algebra.smul_def]
  have hsplit : (q ^ n)⁻¹ * (∑ j ∈ Finset.range (2 * n + 1), (a205810 n j : ℚ) * q ^ j) =
      (a205810 n n : ℚ) +
        ∑ k ∈ Finset.Icc 1 n, (a205810 n (n - k) : ℚ) * (q ^ k + (q⁻¹) ^ k) := by
    rw [Finset.mul_sum]
    have h2n : Finset.range (2 * n + 1) =
        Finset.range n ∪ ({n} ∪ Finset.Icc (n + 1) (2 * n)) := by
      ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]; omega
    have hd1 : Disjoint (Finset.range n) ({n} ∪ Finset.Icc (n + 1) (2 * n)) :=
      Finset.disjoint_left.mpr (fun j h1 h2 => by
        simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc] at h1 h2; omega)
    have hd2 : Disjoint ({n} : Finset ℕ) (Finset.Icc (n + 1) (2 * n)) :=
      Finset.disjoint_left.mpr (fun j h1 h2 => by
        simp only [Finset.mem_singleton, Finset.mem_Icc] at h1 h2; omega)
    rw [h2n, Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_singleton]
    have hmid : (q ^ n)⁻¹ * ((a205810 n n : ℚ) * q ^ n) = (a205810 n n : ℚ) := by field_simp
    have hlo : ∑ j ∈ Finset.range n, (q ^ n)⁻¹ * ((a205810 n j : ℚ) * q ^ j) =
        ∑ k ∈ Finset.Icc 1 n, (a205810 n (n - k) : ℚ) * (q⁻¹) ^ k := by
      symm
      apply Finset.sum_bij (fun k _ => n - k)
      · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
      · intro k1 h1 k2 h2 heq; rw [Finset.mem_Icc] at h1 h2; omega
      · intro j hj; rw [Finset.mem_range] at hj
        exact ⟨n - j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro k hk
        rw [Finset.mem_Icc] at hk
        have hexp : q ^ n = q ^ (n - k) * q ^ k := by rw [← pow_add, Nat.sub_add_cancel hk.2]
        rw [hexp, inv_pow]
        have h1 : q ^ (n - k) ≠ 0 := pow_ne_zero _ hq
        have h2 : q ^ k ≠ 0 := pow_ne_zero _ hq
        field_simp
    have hhi : ∑ j ∈ Finset.Icc (n + 1) (2 * n), (q ^ n)⁻¹ * ((a205810 n j : ℚ) * q ^ j) =
        ∑ k ∈ Finset.Icc 1 n, (a205810 n (n - k) : ℚ) * q ^ k := by
      symm
      apply Finset.sum_bij (fun k _ => n + k)
      · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
      · intro k1 _ k2 _ heq; omega
      · intro j hj; rw [Finset.mem_Icc] at hj
        exact ⟨j - n, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro k hk
        rw [Finset.mem_Icc] at hk
        have hsym : a205810 n (n + k) = a205810 n (n - k) := by
          have := a205810_symm n (n - k) (by omega)
          rw [show 2 * n - (n - k) = n + k by omega] at this
          exact this
        rw [hsym, pow_add]
        field_simp
    rw [hmid, hlo, hhi]
    have hcomb : (∑ k ∈ Finset.Icc 1 n, (a205810 n (n - k) : ℚ) * (q⁻¹) ^ k) +
        (∑ k ∈ Finset.Icc 1 n, (a205810 n (n - k) : ℚ) * q ^ k) =
        ∑ k ∈ Finset.Icc 1 n, (a205810 n (n - k) : ℚ) * (q ^ k + (q⁻¹) ^ k) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k _; ring
    linarith
  rw [hL, hRpoly, hsplit]
  rw [map_sub, map_sum, aeval_C_int]
  have hRHS : (∑ k ∈ Finset.range (n + 1),
        Polynomial.aeval (q + q⁻¹) (Polynomial.C (a205810 n (n - k)) * chebT2 k)) =
      2 * (a205810 n n : ℚ) +
        ∑ k ∈ Finset.Icc 1 n, (a205810 n (n - k) : ℚ) * (q ^ k + (q⁻¹) ^ k) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.sub_zero, map_mul, aeval_C_int, aeval_chebT2 q hq, pow_zero]
    have hIcc : ∑ k ∈ Finset.range n,
          (a205810 n (n - (k + 1)) : ℚ) * (q ^ (k + 1) + (q⁻¹) ^ (k + 1)) =
        ∑ k ∈ Finset.Icc 1 n, (a205810 n (n - k) : ℚ) * (q ^ k + (q⁻¹) ^ k) := by
      apply Finset.sum_bij (fun k _ => k + 1)
      · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Icc]; omega
      · intro k1 _ k2 _ heq; omega
      · intro j hj; rw [Finset.mem_Icc] at hj
        exact ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
      · intro k _; rfl
    rw [hIcc]
    ring
  rw [hRHS]
  ring

end OMA.P_oeis_a205810

theorem OMA.solution : type_of% @OMA.S_oeis_a205810.main :=
  OMA.P_oeis_a205810.prove_main
