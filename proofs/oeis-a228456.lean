import OMAStatements.S_oeis_a228456

-- Problem: A228456: Determinant of the (n+1) X (n+1) matrix with (i,j)-entry equal to A086618(i+j) for all i,j = 0,...,n.
-- Upstream: formal-conjectures statements/oeis-a228456.lean:0 (declaration OMA.S_oeis_a228456.main)
-- Credit: Daniel Whorlow (@draonbioetl), original complete proof in PR #18403.
-- This revision retains the construction and bounds, replacing the manual PSD Hadamard
-- argument by Mathlib Gram-Schmidt and PSD factorization, using Mathlib Chebyshev
-- polynomials, and shortening the integral Cauchy-Schwarz argument via discrim_le_zero.

namespace OMA_A228456_Part1

open Finset Matrix
open scoped Classical

private abbrev b_seq := OMA.S_oeis_a228456.b

private abbrev a_seq := OMA.S_oeis_a228456.a

/-! ### Section 1: Binomial transform tb(m) and Hankel congruence -/

private def tb (m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (m / 2 + 1), m.choose (2 * j) * (2 * j).choose j * catalan (m - j)

private lemma choose_three_mul (m k j : ℕ) (hjk : j ≤ k) (hkj : k + j ≤ m) :
    m.choose (k + j) * (k + j).choose (2 * j) * (2 * j).choose j =
      m.choose k * (k.choose j * (m - k).choose j) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show k + j ≤ m by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show 2 * j ≤ k + j by omega)
  have h3 := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j by omega)
  have h4 := Nat.choose_mul_factorial_mul_factorial (show k ≤ m by omega)
  have h5 := Nat.choose_mul_factorial_mul_factorial (show j ≤ k by omega)
  have h6 := Nat.choose_mul_factorial_mul_factorial (show j ≤ m - k by omega)
  have hpos : 0 < (m - (k + j)).factorial * (k - j).factorial * j.factorial * j.factorial := by
    positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [show k + j - 2 * j = k - j by omega] at h2
  rw [show 2 * j - j = j by omega] at h3
  rw [show m - k - j = m - (k + j) by omega] at h6
  have hL : m.choose (k + j) * (k + j).choose (2 * j) * (2 * j).choose j *
      ((m - (k + j)).factorial * (k - j).factorial * j.factorial * j.factorial) = m.factorial := by
    calc m.choose (k + j) * (k + j).choose (2 * j) * (2 * j).choose j *
          ((m - (k + j)).factorial * (k - j).factorial * j.factorial * j.factorial)
        = m.choose (k + j) * (m - (k + j)).factorial *
          ((k + j).choose (2 * j) * ((2 * j).choose j * j.factorial * j.factorial) * (k - j).factorial) := by ring
      _ = m.choose (k + j) * (m - (k + j)).factorial *
          ((k + j).choose (2 * j) * (2 * j).factorial * (k - j).factorial) := by rw [h3]
      _ = m.choose (k + j) * (k + j).factorial * (m - (k + j)).factorial := by rw [h2]; ring
      _ = m.factorial := h1
  have hR : m.choose k * (k.choose j * (m - k).choose j) *
      ((m - (k + j)).factorial * (k - j).factorial * j.factorial * j.factorial) = m.factorial := by
    calc m.choose k * (k.choose j * (m - k).choose j) *
          ((m - (k + j)).factorial * (k - j).factorial * j.factorial * j.factorial)
        = m.choose k * (k.choose j * j.factorial * (k - j).factorial) *
          ((m - k).choose j * j.factorial * (m - (k + j)).factorial) := by ring
      _ = m.choose k * k.factorial * (m - k).factorial := by rw [h5, h6]
      _ = m.factorial := h4
  rw [hL, hR]

private lemma b_eq_binom_tb (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), m.choose k ^ 2 * catalan k) =
      ∑ r ∈ Finset.range (m + 1), m.choose r * tb r := by
  have hsum_j : ∀ k ≤ m, m.choose k ^ 2 =
      ∑ j ∈ Finset.range (min k (m - k) + 1), m.choose k * (k.choose j * (m - k).choose j) := by
    intro k hk
    rw [← Finset.mul_sum, sq]
    congr 1
    have hv := Nat.add_choose_eq k (m - k) k
    rw [Nat.add_sub_of_le hk, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => k.choose x * (m - k).choose y)] at hv
    rw [hv]
    have hsplit : ∑ i ∈ Finset.range (k + 1), k.choose i * (m - k).choose (k - i) =
        ∑ j ∈ Finset.range (k + 1), k.choose j * (m - k).choose j := by
      refine Finset.sum_bij (fun i _ => k - i) ?_ ?_ ?_ ?_
      · intro i hi; rw [Finset.mem_range] at hi ⊢; omega
      · intro i1 hi1 i2 hi2 heq; rw [Finset.mem_range] at hi1 hi2; omega
      · intro j hj; rw [Finset.mem_range] at hj; exact ⟨k - j, Finset.mem_range.mpr (by omega), by omega⟩
      · intro i hi; rw [Finset.mem_range] at hi
        rw [Nat.choose_symm (by omega : i ≤ k)]
    rw [hsplit]
    symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun j hj hnot => ?_
    rw [Finset.mem_range] at hj hnot
    rw [Nat.choose_eq_zero_of_lt (by omega : m - k < j), mul_zero]
  have hL : ∑ k ∈ Finset.range (m + 1), m.choose k ^ 2 * catalan k =
      ∑ k ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (min k (m - k) + 1),
        m.choose (k + j) * (k + j).choose (2 * j) * (2 * j).choose j * catalan k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [hsum_j k (by omega), Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [choose_three_mul m k j (by omega) (by omega)]
  rw [hL]
  simp only [tb, Finset.mul_sum, Finset.sum_sigma']
  refine Finset.sum_bij (fun x _ => ⟨x.1 + x.2, x.2⟩) ?_ ?_ ?_ ?_
  · intro ⟨k, j⟩ hkj
    simp only [Finset.mem_sigma, Finset.mem_range] at hkj ⊢
    omega
  · intro ⟨k1, j1⟩ _ ⟨k2, j2⟩ _ heq
    have h1 : k1 + j1 = k2 + j2 := congrArg Sigma.fst heq
    have h2 : j1 = j2 := congrArg Sigma.snd heq
    apply Sigma.ext
    · dsimp only; omega
    · refine heq_of_eq ?_; dsimp only; omega
  · intro ⟨r, j⟩ hrj
    simp only [Finset.mem_sigma, Finset.mem_range] at hrj
    refine ⟨⟨r - j, j⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range]; omega
    · apply Sigma.ext
      · dsimp only; omega
      · rfl
  · intro ⟨k, j⟩ _
    dsimp only
    rw [Nat.add_sub_cancel]; ring

private lemma hankel_b_eq_tb_det (n : ℕ) :
    a_seq n = (Matrix.of fun i j : Fin (n + 1) => (tb (i + j) : ℤ)).det := by
  let P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
    Matrix.of fun i r => ((i : ℕ).choose (r : ℕ) : ℤ)
  let Ht : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
    Matrix.of fun r s => (tb (r + s) : ℤ)
  have hP_det : P.det = 1 := by
    have htri : P.IsLowerTriangular := by
      intro i j hij
      have hlt : (i : ℕ) < (j : ℕ) := hij
      change ((i : ℕ).choose (j : ℕ) : ℤ) = 0
      rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero]
    rw [Matrix.det_of_isLowerTriangular P htri]
    refine Finset.prod_eq_one fun i _ => ?_
    change ((i : ℕ).choose (i : ℕ) : ℤ) = 1
    simp
  have hmat : (Matrix.of fun i j : Fin (n + 1) => b_seq (i + j)) = P * Ht * Pᵀ := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, P, Ht, b_seq, OMA.S_oeis_a228456.b]
    have hsum_cast : (∑ k ∈ Finset.range ((i : ℕ) + (j : ℕ) + 1),
        (((i : ℕ) + (j : ℕ)).choose k ^ 2 * catalan k : ℕ) : ℤ) =
        ∑ t ∈ Finset.range ((i : ℕ) + (j : ℕ) + 1),
          ((((i : ℕ) + (j : ℕ)).choose t : ℤ) * (tb t : ℤ)) := by
      have h := congrArg (Nat.cast (R := ℤ)) (b_eq_binom_tb ((i : ℕ) + (j : ℕ)))
      simpa [Nat.cast_sum, Nat.cast_mul] using h
    rw [hsum_cast]
    -- Expand RHS: ∑ s : Fin (n+1), (∑ r : Fin (n+1), C(i,r) * tb(r+s)) * C(j,s)
    have hR : ∑ s : Fin (n + 1), (∑ r : Fin (n + 1), ((i : ℕ).choose r : ℤ) * (tb (r + s) : ℤ)) *
          ((j : ℕ).choose s : ℤ) =
        ∑ r ∈ Finset.range ((i : ℕ) + 1), ∑ s ∈ Finset.range ((j : ℕ) + 1),
          ((i : ℕ).choose r : ℤ) * ((j : ℕ).choose s : ℤ) * (tb (r + s) : ℤ) := by
      have h1 : ∀ s : Fin (n + 1),
          (∑ r : Fin (n + 1), ((i : ℕ).choose r : ℤ) * (tb (r + s) : ℤ)) * ((j : ℕ).choose s : ℤ) =
          ∑ r : Fin (n + 1), ((i : ℕ).choose r : ℤ) * ((j : ℕ).choose s : ℤ) * (tb (r + s) : ℤ) := by
        intro s; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun r _ => by ring
      simp_rw [h1]
      rw [Finset.sum_comm]
      have hfin_i : ∀ f : ℕ → ℤ, (∀ r, (i : ℕ) < r → f r = 0) →
          ∑ r : Fin (n + 1), f r = ∑ r ∈ Finset.range ((i : ℕ) + 1), f r := by
        intro f hf
        rw [Fin.sum_univ_eq_sum_range]
        symm
        refine Finset.sum_subset (Finset.range_mono (by omega)) fun r hr hnot => ?_
        rw [Finset.mem_range] at hr hnot
        exact hf r (by omega)
      have hfin_j : ∀ f : ℕ → ℤ, (∀ s, (j : ℕ) < s → f s = 0) →
          ∑ s : Fin (n + 1), f s = ∑ s ∈ Finset.range ((j : ℕ) + 1), f s := by
        intro f hf
        rw [Fin.sum_univ_eq_sum_range]
        symm
        refine Finset.sum_subset (Finset.range_mono (by omega)) fun s hs hnot => ?_
        rw [Finset.mem_range] at hs hnot
        exact hf s (by omega)
      have hfin_i_app := hfin_i
        (fun r => ∑ s : Fin (n + 1), ((i : ℕ).choose r : ℤ) * ((j : ℕ).choose s : ℤ) * (tb (r + s) : ℤ))
        (fun r hr => Finset.sum_eq_zero fun s _ => by rw [Nat.choose_eq_zero_of_lt hr]; simp)
      rw [hfin_i_app]
      refine Finset.sum_congr rfl fun r _ => ?_
      exact hfin_j
        (fun s => ((i : ℕ).choose r : ℤ) * ((j : ℕ).choose s : ℤ) * (tb (r + s) : ℤ))
        (fun s hs => by rw [Nat.choose_eq_zero_of_lt hs]; simp)
    rw [hR]
    -- Group by t = r + s using Vandermonde
    have hV : ∀ t ∈ Finset.range ((i : ℕ) + (j : ℕ) + 1),
        ((((i : ℕ) + (j : ℕ)).choose t : ℤ) * (tb t : ℤ)) =
        ∑ r ∈ Finset.range (t + 1),
          ((i : ℕ).choose r : ℤ) * ((j : ℕ).choose (t - r) : ℤ) * (tb t : ℤ) := by
      intro t _
      rw [← Finset.sum_mul]
      congr 1
      have hv := Nat.add_choose_eq (i : ℕ) (j : ℕ) t
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => (i : ℕ).choose x * (j : ℕ).choose y)] at hv
      have hcast := congrArg (Nat.cast (R := ℤ)) hv
      simpa [Nat.cast_sum, Nat.cast_mul] using hcast
    rw [Finset.sum_congr rfl hV, Finset.sum_sigma', Finset.sum_sigma']
    -- Both sides have zero terms when r > i or t - r > j
    have hfiltL : ∑ x ∈ (Finset.range ((i : ℕ) + (j : ℕ) + 1)).sigma (fun t => Finset.range (t + 1)),
          ((i : ℕ).choose x.2 : ℤ) * ((j : ℕ).choose (x.1 - x.2) : ℤ) * (tb x.1 : ℤ) =
        ∑ x ∈ ((Finset.range ((i : ℕ) + (j : ℕ) + 1)).sigma (fun t => Finset.range (t + 1))).filter
            (fun x => x.2 ≤ (i : ℕ) ∧ x.1 - x.2 ≤ (j : ℕ)),
          ((i : ℕ).choose x.2 : ℤ) * ((j : ℕ).choose (x.1 - x.2) : ℤ) * (tb x.1 : ℤ) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun ⟨t, r⟩ hmem hnot => ?_
      simp only [Finset.mem_filter, hmem, true_and, not_and_or, not_le] at hnot
      rcases hnot with h1 | h2
      · rw [Nat.choose_eq_zero_of_lt h1]; simp
      · rw [Nat.choose_eq_zero_of_lt h2]; simp
    rw [hfiltL]
    refine Finset.sum_bij (fun x _ => ⟨x.2, x.1 - x.2⟩) ?_ ?_ ?_ ?_
    · intro ⟨t, r⟩ hx
      simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range] at hx ⊢
      omega
    · intro ⟨t1, r1⟩ hx1 ⟨t2, r2⟩ hx2 heq
      simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range] at hx1 hx2
      have h1 : r1 = r2 := congrArg Sigma.fst heq
      have h2 : t1 - r1 = t2 - r2 := congrArg Sigma.snd heq
      apply Sigma.ext
      · dsimp only; omega
      · refine heq_of_eq ?_; dsimp only; omega
    · intro ⟨r, s⟩ hrs
      simp only [Finset.mem_sigma, Finset.mem_range] at hrs
      refine ⟨⟨r + s, r⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range]; omega
      · apply Sigma.ext
        · rfl
        · refine heq_of_eq ?_; dsimp only; omega
    · intro ⟨t, r⟩ hx
      simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range] at hx
      dsimp only
      rw [show r + (t - r) = t by omega]
  simp only [a_seq, OMA.S_oeis_a228456.a, hmat, Matrix.det_mul, Matrix.det_transpose, hP_det, one_mul, mul_one]
  rfl

/-! ### Section 2: 2-adic valuations via binary digit sum s2(n) -/

private def s2 (n : ℕ) : ℕ := (Nat.digits 2 n).sum

private lemma s2_zero : s2 0 = 0 := by simp [s2]

private lemma s2_two_mul {m : ℕ} (hm : 0 < m) : s2 (2 * m) = s2 m := by
  simp only [s2]
  rw [Nat.digits_def' (by decide : 1 < 2) (by omega : 0 < 2 * m)]
  simp [Nat.mul_div_right m (by decide : 0 < 2)]

private lemma s2_two_mul_add_one (m : ℕ) : s2 (2 * m + 1) = s2 m + 1 := by
  simp only [s2]
  rw [Nat.digits_def' (by decide : 1 < 2) (by omega : 0 < 2 * m + 1)]
  have hmod : (2 * m + 1) % 2 = 1 := by omega
  have hdiv : (2 * m + 1) / 2 = m := by omega
  rw [hmod, hdiv, List.sum_cons]
  ring

private lemma s2_succ_add_v2 (n : ℕ) : s2 (n + 1) + padicValNat 2 (n + 1) = s2 n + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hev : n % 2 = 0
    · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
      have hnd : ¬ 2 ∣ (2 * m + 1) := by omega
      rw [padicValNat.eq_zero_of_not_dvd hnd, add_zero, s2_two_mul_add_one]
      cases m with
      | zero => simp [s2_zero]
      | succ k => rw [s2_two_mul (by omega)]
    · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
      have h2eq : 2 * m + 1 + 1 = 2 * (m + 1) := by ring
      rw [h2eq, s2_two_mul (by omega), s2_two_mul_add_one,
        padicValNat.mul (by decide) (by omega : m + 1 ≠ 0), padicValNat.self (by decide)]
      have hih := ih m (by omega)
      omega

private lemma v2_factorial_add_s2 (n : ℕ) : padicValNat 2 n.factorial + s2 n = n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction n with
  | zero => simp [s2_zero]
  | succ k ih =>
    rw [Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero k)]
    have hs := s2_succ_add_v2 k
    omega

private lemma v2_choose {n k : ℕ} (hk : k ≤ n) :
    padicValNat 2 (n.choose k) = s2 k + s2 (n - k) - s2 n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Nat.choose_mul_factorial_mul_factorial hk
  have hch_ne : n.choose k ≠ 0 := (Nat.choose_pos hk).ne'
  have hv := congrArg (padicValNat 2) h
  rw [padicValNat.mul (mul_ne_zero hch_ne (Nat.factorial_ne_zero k)) (Nat.factorial_ne_zero (n - k)),
    padicValNat.mul hch_ne (Nat.factorial_ne_zero k)] at hv
  have hf1 := v2_factorial_add_s2 n
  have hf2 := v2_factorial_add_s2 k
  have hf3 := v2_factorial_add_s2 (n - k)
  omega

private lemma v2_central (j : ℕ) : padicValNat 2 ((2 * j).choose j) = s2 j := by
  rw [v2_choose (by omega : j ≤ 2 * j), show 2 * j - j = j by omega]
  cases j with
  | zero => simp [s2_zero]
  | succ k => rw [s2_two_mul (by omega)]; omega

private lemma catalan_mul_succ (n : ℕ) : (n + 1) * catalan n = (2 * n).choose n := by
  rw [catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose]
  exact Nat.mul_div_cancel' (Nat.succ_dvd_centralBinom n)

private lemma catalan_ne_zero (n : ℕ) : catalan n ≠ 0 := by
  have h := catalan_mul_succ n
  intro h0; rw [h0, mul_zero] at h
  exact (Nat.choose_pos (by omega : n ≤ 2 * n)).ne h

private lemma v2_catalan (n : ℕ) : padicValNat 2 (catalan n) = s2 (n + 1) - 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcat : (n + 1) * catalan n = (2 * n).choose n := catalan_mul_succ n
  have hcat_ne : catalan n ≠ 0 := catalan_ne_zero n
  have hv := congrArg (padicValNat 2) hcat
  rw [padicValNat.mul (by omega) hcat_ne, v2_central] at hv
  have hs := s2_succ_add_v2 n
  omega

private lemma s2_pos_of_pos {n : ℕ} (hn : 0 < n) : 1 ≤ s2 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hev : n % 2 = 0
    · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
      rw [s2_two_mul (by omega)]; exact ih m (by omega) (by omega)
    · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
      rw [s2_two_mul_add_one]; omega

private lemma s2_eq_one_iff (n : ℕ) : s2 n = 1 ↔ ∃ r : ℕ, n = 2 ^ r := by
  constructor
  · induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hs
      have hn : 0 < n := by
        by_contra h0; have hn0 : n = 0 := by omega
        rw [hn0, s2_zero] at hs; omega
      by_cases hev : n % 2 = 0
      · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
        rw [s2_two_mul (by omega)] at hs
        rcases ih m (by omega) hs with ⟨r, rfl⟩
        exact ⟨r + 1, by rw [pow_succ]; ring⟩
      · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
        rw [s2_two_mul_add_one] at hs
        have hm0 : m = 0 := by
          by_contra hm; have := s2_pos_of_pos (by omega : 0 < m); omega
        subst hm0; exact ⟨0, by norm_num⟩
  · rintro ⟨r, rfl⟩
    induction r with
    | zero => simp [s2]
    | succ k ih =>
      rw [pow_succ, mul_comm, s2_two_mul (pow_pos (by decide) k), ih]

private lemma s2_add_le (a b : ℕ) : s2 (a + b) ≤ s2 a + s2 b := by
  have := v2_choose (n := a + b) (k := a) (by omega)
  rw [Nat.add_sub_cancel_left] at this
  have h1 : padicValNat 2 ((a + b).choose a) + s2 (a + b) = s2 a + s2 b := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h := Nat.choose_mul_factorial_mul_factorial (show a ≤ a + b by omega)
    rw [Nat.add_sub_cancel_left] at h
    have hv := congrArg (padicValNat 2) h
    rw [padicValNat.mul (mul_ne_zero (Nat.choose_pos (by omega)).ne' (Nat.factorial_ne_zero a))
        (Nat.factorial_ne_zero b),
      padicValNat.mul (Nat.choose_pos (by omega)).ne' (Nat.factorial_ne_zero a)] at hv
    have hf1 := v2_factorial_add_s2 (a + b)
    have hf2 := v2_factorial_add_s2 a
    have hf3 := v2_factorial_add_s2 b
    omega
  omega

private lemma pow_two_dvd_iff_le_v2 {n k : ℕ} (hn : n ≠ 0) :
    2 ^ k ∣ n ↔ k ≤ padicValNat 2 n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact padicValNat_dvd_iff_le hn

private lemma tb_mod_two (m : ℕ) :
    tb m % 2 = if ∃ r : ℕ, m + 1 = 2 ^ r then 1 else 0 := by
  have hterms : ∀ j ∈ Finset.range (m / 2 + 1), j ≠ 0 →
      2 ∣ m.choose (2 * j) * (2 * j).choose j * catalan (m - j) := by
    intro j _ hj0
    have h2 : 2 ∣ (2 * j).choose j := by
      have : 2 ^ 1 ∣ (2 * j).choose j := by
        rw [pow_two_dvd_iff_le_v2 (Nat.choose_pos (by omega)).ne', v2_central]
        exact s2_pos_of_pos (by omega)
      simpa using this
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h2 _) _
  have htb_mod : tb m % 2 = catalan m % 2 := by
    simp only [tb]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega : 0 < m / 2 + 1))]
    have hrest : 2 ∣ ∑ j ∈ (Finset.range (m / 2 + 1)).erase 0,
        m.choose (2 * j) * (2 * j).choose j * catalan (m - j) := by
      refine Finset.dvd_sum fun j hj => ?_
      rw [Finset.mem_erase] at hj
      exact hterms j hj.2 hj.1
    rcases hrest with ⟨c, hc⟩
    simp only [mul_zero, Nat.choose_zero_right, one_mul, Nat.sub_zero, hc]
    omega
  rw [htb_mod]
  have hcat_ne : catalan m ≠ 0 := catalan_ne_zero m
  split_ifs with hpow
  · have hv0 : padicValNat 2 (catalan m) = 0 := by
      rw [v2_catalan, (s2_eq_one_iff (m + 1)).mpr hpow]
    have hnd : ¬ 2 ∣ catalan m := by
      intro hd
      have h1 : 1 ≤ padicValNat 2 (catalan m) :=
        (pow_two_dvd_iff_le_v2 hcat_ne).mp (by simpa using hd)
      omega
    omega
  · have hs2 : 2 ≤ s2 (m + 1) := by
      have h1 := s2_pos_of_pos (by omega : 0 < m + 1)
      have hne : s2 (m + 1) ≠ 1 := fun h => hpow ((s2_eq_one_iff (m + 1)).mp h)
      omega
    have hd : 2 ∣ catalan m := by
      have h1 : 2 ^ 1 ∣ catalan m := (pow_two_dvd_iff_le_v2 hcat_ne).mpr (by rw [v2_catalan]; omega)
      simpa using h1
    omega

private lemma tb_two_mul_even {k : ℕ} (hk : 1 ≤ k) : tb (2 * k) % 2 = 0 := by
  rw [tb_mod_two]
  split_ifs with h
  · rcases h with ⟨r, hr⟩
    cases r with
    | zero => omega
    | succ r =>
      have : 2 ∣ 2 ^ (r + 1) := dvd_pow_self 2 (by omega)
      rw [← hr] at this; omega
  · rfl

private lemma tb_four_mul_mod_four {k : ℕ} (hk : 1 ≤ k) :
    tb (4 * k) % 4 = if ∃ r : ℕ, k = 2 ^ r then 2 else 0 := by
  have hterm4 : ∀ j ∈ Finset.range (4 * k / 2 + 1), j ≠ 0 →
      4 ∣ (4 * k).choose (2 * j) * (2 * j).choose j * catalan (4 * k - j) := by
    intro j hj hj0
    rw [Finset.mem_range] at hj
    have hcat_ne : catalan (4 * k - j) ≠ 0 := catalan_ne_zero (4 * k - j)
    have hprod_ne : (4 * k).choose (2 * j) * (2 * j).choose j * catalan (4 * k - j) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (Nat.choose_pos (by omega)).ne' (Nat.choose_pos (by omega)).ne') hcat_ne
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    suffices hle : 2 ≤ padicValNat 2 ((4 * k).choose (2 * j) * (2 * j).choose j * catalan (4 * k - j)) by
      have h4 := (pow_two_dvd_iff_le_v2 hprod_ne).mpr hle
      simpa using h4
    rw [padicValNat.mul (mul_ne_zero (Nat.choose_pos (by omega)).ne' (Nat.choose_pos (by omega)).ne') hcat_ne,
      padicValNat.mul (Nat.choose_pos (by omega)).ne' (Nat.choose_pos (by omega)).ne',
      v2_choose (by omega), v2_central, v2_catalan]
    have hsj : 1 ≤ s2 j := s2_pos_of_pos (by omega)
    by_cases hsj2 : 2 ≤ s2 j
    · omega
    have hsj1 : s2 j = 1 := by omega
    rcases (s2_eq_one_iff j).mp hsj1 with ⟨a, rfl⟩
    by_cases ha0 : a = 0
    · subst ha0
      -- j = 1: s2(2) + s2(4k-2) - s2(4k) >= 1 since 4k-2 has bit 1 = 1!
      have hs4k : s2 (4 * k) = s2 k := by
        rw [show 4 * k = 2 * (2 * k) by ring, s2_two_mul (by omega), s2_two_mul (by omega)]
      have hch1 : 1 ≤ padicValNat 2 ((4 * k).choose 2) := by
        rw [show (4 * k).choose 2 = 2 * k * (4 * k - 1) by
          rw [Nat.choose_two_right]; have : 4 * k * (4 * k - 1) = 2 * (2 * k * (4 * k - 1)) := by ring
          rw [this, Nat.mul_div_right _ (by decide)]]
        rw [← pow_two_dvd_iff_le_v2 (Nat.mul_ne_zero (by omega) (by omega))]
        exact dvd_mul_of_dvd_left (dvd_mul_right 2 k) _
      rw [v2_choose (by omega)] at hch1
      have hs1 : s2 1 = 1 := by decide
      simp only [pow_zero, mul_one, show 4 * k - 1 + 1 = 4 * k by omega, hs1] at hch1 ⊢
      omega
    · -- a >= 1: 4*k - 2^a + 1 is odd >= 3, so s2(4*k - 2^a + 1) >= 2!
      have h2a : 2 ≤ 2 ^ a := le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) (by omega))
      have hodd : (4 * k - 2 ^ a + 1) % 2 = 1 := by
        have h2d : 2 ∣ 2 ^ a := dvd_pow_self 2 ha0
        omega
      have hge3 : 3 ≤ 4 * k - 2 ^ a + 1 := by
        have : 2 * 2 ^ a ≤ 4 * k := by omega
        omega
      have hnotpow : ¬ ∃ r : ℕ, 4 * k - 2 ^ a + 1 = 2 ^ r := by
        rintro ⟨r, hr⟩
        cases r with
        | zero => omega
        | succ r =>
          have : 2 ∣ 2 ^ (r + 1) := dvd_pow_self 2 (by omega)
          rw [← hr] at this; omega
      have hs_ge2 : 2 ≤ s2 (4 * k - 2 ^ a + 1) := by
        have h1 := s2_pos_of_pos (by omega : 0 < 4 * k - 2 ^ a + 1)
        have hne : s2 (4 * k - 2 ^ a + 1) ≠ 1 := fun h => hnotpow ((s2_eq_one_iff _).mp h)
        omega
      omega
  have htb_mod : tb (4 * k) % 4 = catalan (4 * k) % 4 := by
    simp only [tb]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega : 0 < 4 * k / 2 + 1))]
    have hrest : 4 ∣ ∑ j ∈ (Finset.range (4 * k / 2 + 1)).erase 0,
        (4 * k).choose (2 * j) * (2 * j).choose j * catalan (4 * k - j) := by
      refine Finset.dvd_sum fun j hj => ?_
      rw [Finset.mem_erase] at hj
      exact hterm4 j hj.2 hj.1
    rcases hrest with ⟨c, hc⟩
    simp only [mul_zero, Nat.choose_zero_right, one_mul, Nat.sub_zero, hc]
    omega
  rw [htb_mod]
  have hcat_ne : catalan (4 * k) ≠ 0 := catalan_ne_zero (4 * k)
  have hs4k1 : s2 (4 * k + 1) = s2 k + 1 := by
    rw [show 4 * k + 1 = 2 * (2 * k) + 1 by ring, s2_two_mul_add_one, s2_two_mul (by omega)]
  have hv_cat : padicValNat 2 (catalan (4 * k)) = s2 k := by
    rw [v2_catalan, hs4k1]; omega
  split_ifs with hpow
  · have hv1 : padicValNat 2 (catalan (4 * k)) = 1 := by
      rw [hv_cat, (s2_eq_one_iff k).mpr hpow]
    have hd2 : 2 ∣ catalan (4 * k) := by
      have := (pow_two_dvd_iff_le_v2 hcat_ne).mpr (by omega : 1 ≤ padicValNat 2 (catalan (4 * k)))
      simpa using this
    have hnd4 : ¬ 4 ∣ catalan (4 * k) := by
      intro hd
      have := (pow_two_dvd_iff_le_v2 hcat_ne).mp (by simpa using hd : 2 ^ 2 ∣ catalan (4 * k))
      omega
    omega
  · have hs2 : 2 ≤ s2 k := by
      have h1 := s2_pos_of_pos (by omega : 0 < k)
      have hne : s2 k ≠ 1 := fun h => hpow ((s2_eq_one_iff k).mp h)
      omega
    have hd4 : 4 ∣ catalan (4 * k) := by
      have := (pow_two_dvd_iff_le_v2 hcat_ne).mpr (by omega : 2 ≤ padicValNat 2 (catalan (4 * k)))
      simpa using this
    omega

private lemma tb_four_mul_add_two_mod_eight {k : ℕ} (hk : 1 ≤ k) :
    tb (4 * k + 2) % 8 = 0 := by
  by_cases hk1 : k = 1
  · subst hk1
    -- tb 6 = 2752, 2752 % 8 = 0
    have h6 : tb 6 = 2752 := by
      simp only [tb, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
      have hc3 : catalan 3 = 5 := by
        rw [catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose]; decide
      have hc4 : catalan 4 = 14 := by
        rw [catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose]; decide
      have hc5 : catalan 5 = 42 := by
        rw [catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose]; decide
      have hc6 : catalan 6 = 132 := by
        rw [catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose]; decide
      norm_num [hc3, hc4, hc5, hc6, Nat.choose]
    rw [h6]
  have hk2 : 2 ≤ k := by omega
  -- For k >= 2: (1) every j >= 2 term is divisible by 8; (2) j=0 + j=1 is divisible by 8!
  have hterm8 : ∀ j ∈ Finset.range ((4 * k + 2) / 2 + 1), 2 ≤ j →
      8 ∣ (4 * k + 2).choose (2 * j) * (2 * j).choose j * catalan (4 * k + 2 - j) := by
    intro j hj hj2
    rw [Finset.mem_range] at hj
    have hcat_ne : catalan (4 * k + 2 - j) ≠ 0 := catalan_ne_zero (4 * k + 2 - j)
    have hprod_ne : (4 * k + 2).choose (2 * j) * (2 * j).choose j * catalan (4 * k + 2 - j) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (Nat.choose_pos (by omega)).ne' (Nat.choose_pos (by omega)).ne') hcat_ne
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    suffices hle : 3 ≤ padicValNat 2 ((4 * k + 2).choose (2 * j) * (2 * j).choose j * catalan (4 * k + 2 - j)) by
      have h8 := (pow_two_dvd_iff_le_v2 hprod_ne).mpr hle
      simpa using h8
    rw [padicValNat.mul (mul_ne_zero (Nat.choose_pos (by omega)).ne' (Nat.choose_pos (by omega)).ne') hcat_ne,
      padicValNat.mul (Nat.choose_pos (by omega)).ne' (Nat.choose_pos (by omega)).ne',
      v2_choose (by omega), v2_central, v2_catalan]
    by_cases hsj3 : 3 ≤ s2 j
    · omega
    by_cases hsj2 : s2 j = 2
    · -- Need v2(C(4k+2, 2j)) + (s2(4k+3-j) - 1) >= 1
      by_cases hpow : ∃ r : ℕ, 4 * k + 2 - j + 1 = 2 ^ r
      · rcases hpow with ⟨r, hr⟩
        -- If j is even, 4k+3-j is odd >= 5, cannot be 2^r!
        by_cases hj_ev : j % 2 = 0
        · have hge5 : 5 ≤ 4 * k + 2 - j + 1 := by omega
          cases r with
          | zero => omega
          | succ r =>
            have : 2 ∣ 2 ^ (r + 1) := dvd_pow_self 2 (by omega)
            rw [← hr] at this; omega
        · -- j is odd with s2 j = 2, so j = 2*m + 1 with s2 m = 1, i.e. m = 2^a (a >= 0)
          obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m + 1 := ⟨j / 2, by omega⟩
          rw [s2_two_mul_add_one] at hsj2
          rcases (s2_eq_one_iff m).mp (by omega) with ⟨a, rfl⟩
          -- 4*k + 2 - (2*2^a + 1) + 1 = 4*k + 2 - 2^(a+1) = 2^r
          by_cases ha0 : a = 0
          · -- j = 3: 4*k = 2^r, so k = 2^(r-2) with k >= 2 => 2 ∣ k => 8 ∣ 4*k
            -- Then C(4k+2, 6): 2*j = 6, check s2(6) + s2(4k-4) - s2(4k+2) >= 1!
            subst ha0
            have h4k_eq : 4 * k = 2 ^ r := by omega
            have hs4k2 : s2 (4 * k + 2) = 2 := by
              rw [show 4 * k + 2 = 2 * (2 * k + 1) by ring, s2_two_mul (by omega), s2_two_mul_add_one]
              have hsk : s2 k = 1 := by
                have hsk4 : s2 (4 * k) = 1 := by rw [h4k_eq]; exact (s2_eq_one_iff _).mpr ⟨r, rfl⟩
                rw [show 4 * k = 2 * (2 * k) by ring, s2_two_mul (by omega), s2_two_mul (by omega)] at hsk4
                exact hsk4
              omega
            have hs3 : s2 3 = 2 := by decide
            have hs6 : s2 6 = 2 := by decide
            have hpos_rem : 0 < 4 * k + 2 - 6 := by omega
            have hs_rem : 1 ≤ s2 (4 * k + 2 - 6) := s2_pos_of_pos hpos_rem
            have hpos_cat : 1 ≤ s2 (4 * k + 2 - 3 + 1) := s2_pos_of_pos (by omega)
            simp only [pow_zero, mul_one, show 2 * (2 + 1) = 6 by decide,
              show (2 : ℕ) + 1 = 3 by decide]
            omega
          · -- a >= 1: 4 ∣ 2^(a+1), so 4*k + 2 - 2^(a+1) ≡ 2 (mod 4) and >= 4! Cannot be 2^r!
            have h4d : 4 ∣ 2 * 2 ^ a := by
              have : 2 ∣ 2 ^ a := dvd_pow_self 2 ha0
              rcases this with ⟨t, ht⟩; exact ⟨t, by linarith⟩
            have hmod4 : (4 * k + 2 - (2 * 2 ^ a + 1) + 1) % 4 = 2 := by omega
            have hge6 : 4 ≤ 4 * k + 2 - (2 * 2 ^ a + 1) + 1 := by omega
            cases r with
            | zero => omega
            | succ r =>
              cases r with
              | zero => omega
              | succ r =>
                have h4pow : 4 ∣ 2 ^ (r + 2) := by
                  rw [pow_add]; exact dvd_mul_of_dvd_right (by decide : 4 ∣ 2 ^ 2) _
                rw [← hr] at h4pow; omega
      · have hs_ge2 : 2 ≤ s2 (4 * k + 2 - j + 1) := by
          have h1 := s2_pos_of_pos (by omega : 0 < 4 * k + 2 - j + 1)
          have hne : s2 (4 * k + 2 - j + 1) ≠ 1 := fun h => hpow ((s2_eq_one_iff _).mp h)
          omega
        omega
    · -- s2 j = 1, j >= 2 => j = 2^a with a >= 1
      have hsj1 : s2 j = 1 := by have := s2_pos_of_pos (by omega : 0 < j); omega
      rcases (s2_eq_one_iff j).mp hsj1 with ⟨a, rfl⟩
      have ha1 : 1 ≤ a := by
        cases a with
        | zero => simp at hj2
        | succ _ => omega
      by_cases ha_eq1 : a = 1
      · -- j = 2: 2*j = 4, 4k+2 - 2 + 1 = 4k + 1, s2(4k+1) = s2(k) + 1
        subst ha_eq1
        have hs4k1 : s2 (4 * k + 2 - 2 ^ 1 + 1) = s2 k + 1 := by
          rw [show 4 * k + 2 - 2 ^ 1 + 1 = 2 * (2 * k) + 1 by omega, s2_two_mul_add_one,
            s2_two_mul (by omega)]
        by_cases hsk2 : 2 ≤ s2 k
        · rw [hs4k1]; omega
        · -- s2 k = 1 and k >= 2 => k is even! So 8 ∣ 4*k, hence 4k+2 has bit 2 = 0, so v2(C(4k+2, 4)) >= 1!
          have hsk1 : s2 k = 1 := by have := s2_pos_of_pos (by omega : 0 < k); omega
          rcases (s2_eq_one_iff k).mp hsk1 with ⟨r, rfl⟩
          have hr1 : 1 ≤ r := by
            cases r with
            | zero => simp at hk2
            | succ _ => omega
          have hs4k2 : s2 (4 * 2 ^ r + 2) = 2 := by
            rw [show 4 * 2 ^ r + 2 = 2 * (2 * 2 ^ r + 1) by ring, s2_two_mul (by omega),
              s2_two_mul_add_one, (s2_eq_one_iff (2 ^ r)).mpr ⟨r, rfl⟩]
          have hs4 : s2 (2 * 2 ^ 1) = 1 := by decide
          -- 4 * 2^r + 2 - 4 = 2 * (2 * 2^r - 1) has s2 = r + 1 >= 2!
          have hrem_ge2 : 2 ≤ s2 (4 * 2 ^ r + 2 - 2 * 2 ^ 1) := by
            have hrem_eq : 4 * 2 ^ r + 2 - 2 * 2 ^ 1 = 2 * (2 * 2 ^ r - 1) := by
              have : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by decide)
              omega
            rw [hrem_eq, s2_two_mul (by have : 2 ≤ 2 ^ r := le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) hr1); omega)]
            have hodd : (2 * 2 ^ r - 1) % 2 = 1 := by
              have : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by decide); omega
            have hge3 : 3 ≤ 2 * 2 ^ r - 1 := by
              have : 2 ≤ 2 ^ r := le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) hr1); omega
            have hnotp : ¬ ∃ t : ℕ, 2 * 2 ^ r - 1 = 2 ^ t := by
              rintro ⟨t, ht⟩
              cases t with
              | zero => omega
              | succ t =>
                have : 2 ∣ 2 ^ (t + 1) := dvd_pow_self 2 (by omega)
                rw [← ht] at this; omega
            have h1 := s2_pos_of_pos (by omega : 0 < 2 * 2 ^ r - 1)
            have hne : s2 (2 * 2 ^ r - 1) ≠ 1 := fun h => hnotp ((s2_eq_one_iff _).mp h)
            omega
          rw [hs4k1, hsk1, hs4k2, hs4]; omega
      · -- a >= 2: 4 ∣ 2^a, so 4*k + 2 - 2^a + 1 = 4*(k - 2^(a-2)) + 3 has bits 0 and 1 = 1 AND higher bit >= 1!
        have ha2 : 2 ≤ a := by omega
        have h4d : 4 ∣ 2 ^ a := by
          rw [show a = (a - 2) + 2 by omega, pow_add]
          exact dvd_mul_of_dvd_right (by decide : 4 ∣ 2 ^ 2) _
        rcases h4d with ⟨q, hq⟩
        have hqpos : 0 < q := by
          have : 4 ≤ 2 ^ a := le_trans (by decide : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by decide) ha2)
          omega
        have hkgtq : q < k := by
          have : 2 * 2 ^ a ≤ 4 * k + 2 := by omega
          omega
        have heq3 : 4 * k + 2 - 2 ^ a + 1 = 2 * (2 * (k - q) + 1) + 1 := by omega
        have hs3 : 3 ≤ s2 (4 * k + 2 - 2 ^ a + 1) := by
          rw [heq3, s2_two_mul_add_one, s2_two_mul_add_one]
          have := s2_pos_of_pos (by omega : 0 < k - q)
          omega
        omega
  -- Now sum = term(0) + term(1) + ∑_{j >= 2} term(j)
  have hsplit : tb (4 * k + 2) =
      catalan (4 * k + 2) + (4 * k + 2).choose 2 * 2 * catalan (4 * k + 1) +
      ∑ j ∈ (Finset.range ((4 * k + 2) / 2 + 1)).filter (fun j => 2 ≤ j),
        (4 * k + 2).choose (2 * j) * (2 * j).choose j * catalan (4 * k + 2 - j) := by
    simp only [tb]
    have hlt2 : 1 < (4 * k + 2) / 2 + 1 := by omega
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range ((4 * k + 2) / 2 + 1)) (fun j => j < 2)]
    have hfilt_lt : (Finset.range ((4 * k + 2) / 2 + 1)).filter (fun j => j < 2) = {0, 1} := by
      ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]; omega
    have hfilt_ge : (Finset.range ((4 * k + 2) / 2 + 1)).filter (fun j => ¬ j < 2) =
        (Finset.range ((4 * k + 2) / 2 + 1)).filter (fun j => 2 ≤ j) := by
      ext j; simp only [Finset.mem_filter, not_lt]
    rw [hfilt_lt, hfilt_ge, Finset.sum_pair (by decide : (0 : ℕ) ≠ 1)]
    simp only [mul_zero, mul_one, Nat.choose_zero_right, one_mul, Nat.sub_zero,
      show (2 : ℕ).choose 1 = 2 by decide, show 4 * k + 2 - 1 = 4 * k + 1 by omega]
  rw [hsplit]
  have hrest8 : 8 ∣ ∑ j ∈ (Finset.range ((4 * k + 2) / 2 + 1)).filter (fun j => 2 ≤ j),
      (4 * k + 2).choose (2 * j) * (2 * j).choose j * catalan (4 * k + 2 - j) :=
    Finset.dvd_sum fun j hj => by
      rw [Finset.mem_filter] at hj; exact hterm8 j hj.1 hj.2
  -- Show 8 ∣ catalan (4*k + 2) + (4*k + 2).choose 2 * 2 * catalan (4*k + 1)
  have hpair8 : 8 ∣ catalan (4 * k + 2) + (4 * k + 2).choose 2 * 2 * catalan (4 * k + 1) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc1_ne : catalan (4 * k + 1) ≠ 0 := catalan_ne_zero (4 * k + 1)
    have hc2_ne : catalan (4 * k + 2) ≠ 0 := catalan_ne_zero (4 * k + 2)
    have hs4k2 : s2 (4 * k + 2) = s2 k + 1 := by
      rw [show 4 * k + 2 = 2 * (2 * k + 1) by ring, s2_two_mul (by omega), s2_two_mul_add_one]
    have hs4k3 : s2 (4 * k + 3) = s2 k + 2 := by
      rw [show 4 * k + 3 = 2 * (2 * k + 1) + 1 by ring, s2_two_mul_add_one, s2_two_mul_add_one]
    have hv_c2 : padicValNat 2 (catalan (4 * k + 2)) = s2 k + 1 := by rw [v2_catalan, hs4k3]; omega
    have hv_c1 : padicValNat 2 (catalan (4 * k + 1)) = s2 k := by rw [v2_catalan, hs4k2]; omega
    have hch2 : (4 * k + 2).choose 2 * 2 = (4 * k + 2) * (4 * k + 1) := by
      rw [Nat.choose_two_right, show 4 * k + 2 - 1 = 4 * k + 1 by omega,
        Nat.div_mul_cancel (dvd_mul_of_dvd_left ⟨2 * k + 1, by ring⟩ (4 * k + 1))]
    rw [hch2]
    have hv_t1 : padicValNat 2 ((4 * k + 2) * (4 * k + 1) * catalan (4 * k + 1)) = s2 k + 1 := by
      rw [padicValNat.mul (by positivity) hc1_ne, padicValNat.mul (by omega) (by omega), hv_c1]
      have hv4k1 : padicValNat 2 (4 * k + 1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
      have hv4k2 : padicValNat 2 (4 * k + 2) = 1 := by
        rw [show 4 * k + 2 = 2 * (2 * k + 1) by ring,
          padicValNat.mul (by decide) (by omega), padicValNat.self (by decide),
          padicValNat.eq_zero_of_not_dvd (by omega)]
      omega
    by_cases hsk2 : 2 ≤ s2 k
    · have h1 : 8 ∣ catalan (4 * k + 2) := by
        have := (pow_two_dvd_iff_le_v2 hc2_ne).mpr (by omega : 3 ≤ padicValNat 2 (catalan (4 * k + 2)))
        simpa using this
      have h2 : 8 ∣ (4 * k + 2) * (4 * k + 1) * catalan (4 * k + 1) := by
        have := (pow_two_dvd_iff_le_v2 (mul_ne_zero (by positivity) hc1_ne)).mpr
          (by omega : 3 ≤ padicValNat 2 ((4 * k + 2) * (4 * k + 1) * catalan (4 * k + 1)))
        simpa using this
      exact dvd_add h1 h2
    · have hsk1 : s2 k = 1 := by have := s2_pos_of_pos (by omega : 0 < k); omega
      have hd4_1 : 4 ∣ catalan (4 * k + 2) := by
        have := (pow_two_dvd_iff_le_v2 hc2_ne).mpr (by omega : 2 ≤ padicValNat 2 (catalan (4 * k + 2)))
        simpa using this
      have hnd8_1 : ¬ 8 ∣ catalan (4 * k + 2) := by
        intro hd
        have := (pow_two_dvd_iff_le_v2 hc2_ne).mp (by simpa using hd : 2 ^ 3 ∣ catalan (4 * k + 2))
        omega
      have hd4_2 : 4 ∣ (4 * k + 2) * (4 * k + 1) * catalan (4 * k + 1) := by
        have := (pow_two_dvd_iff_le_v2 (mul_ne_zero (by positivity) hc1_ne)).mpr
          (by omega : 2 ≤ padicValNat 2 ((4 * k + 2) * (4 * k + 1) * catalan (4 * k + 1)))
        simpa using this
      have hnd8_2 : ¬ 8 ∣ (4 * k + 2) * (4 * k + 1) * catalan (4 * k + 1) := by
        intro hd
        have := (pow_two_dvd_iff_le_v2 (mul_ne_zero (by positivity) hc1_ne)).mp
          (by simpa using hd : 2 ^ 3 ∣ (4 * k + 2) * (4 * k + 1) * catalan (4 * k + 1))
        omega
      omega
  have htot := dvd_add hpair8 hrest8
  omega

private lemma tb_zero : tb 0 = 1 := by
  simp [tb, catalan_zero]

private lemma tb_two : tb 2 = 4 := by
  simp only [tb, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  have hc1 : catalan 1 = 1 := by
    rw [catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose]; decide
  have hc2 : catalan 2 = 2 := by
    rw [catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose]; decide
  norm_num [hc1, hc2, Nat.choose]

/-! ### Section 3: Catalan ballot triangle & exact Hankel identities -/

private def dyckFrom : ℕ → ℕ → ℕ → ℕ
  | 0, a, b => if a = b then 1 else 0
  | s + 1, a, 0 => dyckFrom s a 1
  | s + 1, a, b + 1 => dyckFrom s a b + dyckFrom s a (b + 2)

private lemma dyckFrom_eq_zero_of_lt {s a b : ℕ} (h : a + s < b) : dyckFrom s a b = 0 := by
  induction s generalizing a b with
  | zero => simp [dyckFrom]; omega
  | succ s ih =>
    cases b with
    | zero => omega
    | succ b =>
      simp only [dyckFrom]
      rw [ih (by omega), ih (by omega)]

private lemma dyckFrom_self (s a : ℕ) : dyckFrom s a (a + s) = 1 := by
  induction s generalizing a with
  | zero => simp [dyckFrom]
  | succ s ih =>
    rw [show a + (s + 1) = (a + s) + 1 by omega]
    simp only [dyckFrom]
    rw [ih a, dyckFrom_eq_zero_of_lt (by omega : a + s < a + s + 2), add_zero]

private lemma dyckFrom_symm (s a b : ℕ) : dyckFrom s a b = dyckFrom s b a := by
  induction s generalizing a b with
  | zero => simp [dyckFrom, eq_comm]
  | succ s ih =>
    -- Prove step on first argument by induction on s
    have hstep : ∀ t x y, dyckFrom (t + 1) x y =
        (if x = 0 then dyckFrom t 1 y else dyckFrom t (x - 1) y + dyckFrom t (x + 1) y) := by
      intro t
      induction t with
      | zero =>
        intro x y
        cases x with
        | zero => cases y with | zero => simp [dyckFrom] | succ y => cases y <;> simp [dyckFrom]
        | succ x =>
          cases y with
          | zero => cases x <;> simp [dyckFrom]
          | succ y =>
            simp only [dyckFrom, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
              Nat.add_sub_cancel]
            by_cases h1 : x = y
            · subst h1; simp
            · by_cases h2 : x + 1 = y + 2
              · have : x = y + 1 := by omega
                subst this; simp [show y + 1 + 1 ≠ y by omega]
              · by_cases h3 : x + 2 = y + 1
                · have : y = x + 1 := by omega
                  subst this; simp [show x ≠ x + 1 + 1 by omega]
                · simp [show x + 1 ≠ y by omega, show x ≠ y + 1 by omega,
                    show x + 2 ≠ y + 1 by omega]
      | succ t iht =>
        intro x y
        cases y with
        | zero => simp only [dyckFrom]; exact iht x 1
        | succ y =>
          change dyckFrom (t + 1) x y + dyckFrom (t + 1) x (y + 2) =
            if x = 0 then dyckFrom t 1 y + dyckFrom t 1 (y + 2)
            else (dyckFrom t (x - 1) y + dyckFrom t (x - 1) (y + 2)) +
              (dyckFrom t (x + 1) y + dyckFrom t (x + 1) (y + 2))
          rw [iht x y, iht x (y + 2)]
          split_ifs <;> ring
    rw [hstep s a b]
    cases a with
    | zero => simp [dyckFrom, ih]
    | succ a =>
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel, dyckFrom]
      rw [ih a b, ih (a + 2) b]

private lemma dyckFrom_add (s1 s2 a b : ℕ) :
    dyckFrom (s1 + s2) a b = ∑ c ∈ Finset.range (a + s1 + 1), dyckFrom s1 a c * dyckFrom s2 c b := by
  induction s2 generalizing b with
  | zero =>
    simp only [add_zero, dyckFrom]
    by_cases hle : b ≤ a + s1
    · rw [Finset.sum_eq_single b]
      · simp
      · intro c _ hne; simp [hne]
      · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
    · rw [dyckFrom_eq_zero_of_lt (by omega)]
      symm
      refine Finset.sum_eq_zero fun c hc => ?_
      rw [Finset.mem_range] at hc
      simp [show c ≠ b by omega]
  | succ s2 ih =>
    rw [show s1 + (s2 + 1) = (s1 + s2) + 1 by omega]
    cases b with
    | zero =>
      simp only [dyckFrom]
      exact ih 1
    | succ b =>
      simp only [dyckFrom]
      rw [ih b, ih (b + 2), ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => by ring

private lemma dyckFrom_zero_parity (s h : ℕ) (hne : s % 2 ≠ h % 2) : dyckFrom s 0 h = 0 := by
  induction s generalizing h with
  | zero => simp [dyckFrom]; omega
  | succ s ih =>
    cases h with
    | zero => simp only [dyckFrom]; exact ih 1 (by omega)
    | succ h =>
      simp only [dyckFrom]
      rw [ih h (by omega), ih (h + 2) (by omega)]

private lemma dyckFrom_zero_closed (s h : ℕ) (hpar : s % 2 = h % 2) (hle : h ≤ s) :
    dyckFrom s 0 h = s.choose ((s - h) / 2) - (if h < s then s.choose ((s - h) / 2 - 1) else 0) := by
  induction s generalizing h with
  | zero =>
    have : h = 0 := by omega
    subst this; simp [dyckFrom]
  | succ s ih =>
    by_cases heq : h = s + 1
    · subst heq
      have h1 := dyckFrom_self (s + 1) 0
      rw [zero_add] at h1; rw [h1]; simp
    have hlt : h < s + 1 := by omega
    simp only [hlt, ↓reduceIte]
    cases h with
    | zero =>
      simp only [dyckFrom]
      have hih := ih 1 (by omega) (by omega)
      rw [hih]
      by_cases hs1 : 1 < s
      · simp only [hs1, ↓reduceIte]
        have heven : s % 2 = 1 := by omega
        obtain ⟨m, rfl⟩ : ∃ m, s = 2 * m + 1 := ⟨s / 2, by omega⟩
        have hm1 : 1 ≤ m := by omega
        have hch1 : (2 * m + 2).choose (m + 1) = (2 * m + 1).choose m + (2 * m + 1).choose (m + 1) :=
          Nat.choose_succ_succ (2 * m + 1) m
        have hch2 : (2 * m + 2).choose m = (2 * m + 1).choose (m - 1) + (2 * m + 1).choose m := by
          have := Nat.choose_succ_succ (2 * m + 1) (m - 1)
          rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, show m - 1 + 1 = m by omega] at this
          exact this
        have hsym : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m := by
          have := Nat.choose_symm (show m ≤ 2 * m + 1 by omega)
          rwa [show 2 * m + 1 - m = m + 1 by omega] at this
        have hle1 : (2 * m + 1).choose (m - 1) ≤ (2 * m + 1).choose m := by
          have := Nat.choose_le_succ_of_lt_half_left (n := 2 * m + 1) (r := m - 1) (by omega)
          rwa [show m - 1 + 1 = m by omega] at this
        have hdiv1 : (2 * m + 1 - 1) / 2 = m := by omega
        have hdiv2 : (2 * m + 1 + 1 - 0) / 2 = m + 1 := by omega
        rw [hdiv1, hdiv2, show 2 * m + 1 + 1 = 2 * m + 2 by omega, Nat.add_sub_cancel]
        omega
      · have hs : s = 1 := by omega
        subst hs; simp
    | succ h =>
      simp only [dyckFrom]
      have hih1 := ih h (by omega) (by omega)
      rw [hih1]
      by_cases hlt2 : h + 2 ≤ s
      · have hih2 := ih (h + 2) (by omega) hlt2
        rw [hih2]
        set d := (s - h) / 2
        have hpar_s : s - h = 2 * d := by omega
        have hdiv_top : (s + 1 - (h + 1)) / 2 = d := by omega
        have hdiv2 : (s - (h + 2)) / 2 = d - 1 := by omega
        have hd1 : 1 ≤ d := by omega
        rw [hdiv_top, hdiv2]
        have hlt_h : h < s := by omega
        simp only [hlt_h, ↓reduceIte]
        have hpas1 : (s + 1).choose d = s.choose (d - 1) + s.choose d := by
          have := Nat.choose_succ_succ s (d - 1)
          rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, show d - 1 + 1 = d by omega] at this
          exact this
        by_cases hlt3 : h + 2 < s
        · simp only [hlt3, ↓reduceIte]
          have hd2 : 2 ≤ d := by omega
          have hpas2 : (s + 1).choose (d - 1) = s.choose (d - 2) + s.choose (d - 1) := by
            have := Nat.choose_succ_succ s (d - 2)
            rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, show d - 2 + 1 = d - 1 by omega] at this
            exact this
          have hle1 : s.choose (d - 1) ≤ s.choose d := by
            have := Nat.choose_le_succ_of_lt_half_left (n := s) (r := d - 1) (by omega)
            rwa [show d - 1 + 1 = d by omega] at this
          have hle2 : s.choose (d - 2) ≤ s.choose (d - 1) := by
            have := Nat.choose_le_succ_of_lt_half_left (n := s) (r := d - 2) (by omega)
            rwa [show d - 2 + 1 = d - 1 by omega] at this
          rw [show d - 1 - 1 = d - 2 by omega]
          omega
        · simp only [hlt3, ↓reduceIte, Nat.sub_zero]
          have hd_eq : d = 1 := by omega
          rw [hd_eq]
          simp only [Nat.sub_self, Nat.choose_zero_right, Nat.choose_one_right]
          omega
      · exfalso; omega

private lemma dyckFrom_catalan (n : ℕ) : dyckFrom (2 * n) 0 0 = catalan n := by
  cases n with
  | zero => simp [dyckFrom]
  | succ k =>
    rw [dyckFrom_zero_closed (2 * (k + 1)) 0 (by omega) (by omega)]
    simp only [Nat.sub_zero, show 0 < 2 * (k + 1) by omega, ↓reduceIte,
      show 2 * (k + 1) / 2 = k + 1 by omega]
    have h1 : (k + 2) * catalan (k + 1) = (2 * (k + 1)).choose (k + 1) := catalan_mul_succ (k + 1)
    have h2 : (k + 2) * (2 * (k + 1)).choose k = (k + 1) * (2 * (k + 1)).choose (k + 1) := by
      have := Nat.choose_succ_right_eq (2 * (k + 1)) k
      rw [show 2 * (k + 1) - k = k + 2 by omega] at this
      linarith
    have hle : (2 * (k + 1)).choose k ≤ (2 * (k + 1)).choose (k + 1) :=
      Nat.choose_le_succ_of_lt_half_left (by omega)
    have hmul : (k + 2) * ((2 * (k + 1)).choose (k + 1) - (2 * (k + 1)).choose k) =
        (k + 2) * catalan (k + 1) := by
      rw [Nat.mul_sub_left_distrib, h2, h1]
      have hsplit : (k + 2) * (2 * (k + 1)).choose (k + 1) =
          (k + 1) * (2 * (k + 1)).choose (k + 1) + (2 * (k + 1)).choose (k + 1) := by ring
      rw [hsplit, Nat.add_sub_cancel_left]
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < k + 2) hmul

private lemma catalan_hankel_det_one (n : ℕ) :
    (Matrix.of fun i j : Fin n => (catalan (i + j) : ℤ)).det = 1 := by
  let L : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i k => (dyckFrom (2 * (i : ℕ)) 0 (2 * (k : ℕ)) : ℤ)
  have hL_det : L.det = 1 := by
    have htri : L.IsLowerTriangular := by
      intro i k hik
      have hlt : (i : ℕ) < (k : ℕ) := hik
      change (dyckFrom (2 * (i : ℕ)) 0 (2 * (k : ℕ)) : ℤ) = 0
      rw [dyckFrom_eq_zero_of_lt (by omega : 0 + 2 * (i : ℕ) < 2 * (k : ℕ)), Nat.cast_zero]
    rw [Matrix.det_of_isLowerTriangular L htri]
    refine Finset.prod_eq_one fun i _ => ?_
    have h1 := dyckFrom_self (2 * (i : ℕ)) 0
    rw [zero_add] at h1
    change (dyckFrom (2 * (i : ℕ)) 0 (2 * (i : ℕ)) : ℤ) = 1
    simp [h1]
  have hmat : (Matrix.of fun i j : Fin n => (catalan (i + j) : ℤ)) = L * Lᵀ := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, L]
    rw [← dyckFrom_catalan ((i : ℕ) + (j : ℕ)), show 2 * ((i : ℕ) + (j : ℕ)) = 2 * (i : ℕ) + 2 * (j : ℕ) by ring,
      dyckFrom_add]
    have hcast : ((∑ c ∈ Finset.range (0 + 2 * (i : ℕ) + 1),
        dyckFrom (2 * (i : ℕ)) 0 c * dyckFrom (2 * (j : ℕ)) c 0 : ℕ) : ℤ) =
        ∑ c ∈ Finset.range (2 * (i : ℕ) + 1),
          (dyckFrom (2 * (i : ℕ)) 0 c : ℤ) * (dyckFrom (2 * (j : ℕ)) 0 c : ℤ) := by
      rw [zero_add, Nat.cast_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Nat.cast_mul, dyckFrom_symm (2 * (j : ℕ)) c 0]
    rw [hcast]
    -- Restrict to even c = 2*k (odd c give 0 by parity)
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (2 * (i : ℕ) + 1)) (fun c => c % 2 = 0)]
    have hodd0 : ∑ c ∈ (Finset.range (2 * (i : ℕ) + 1)).filter (fun c => ¬ c % 2 = 0),
        (dyckFrom (2 * (i : ℕ)) 0 c : ℤ) * (dyckFrom (2 * (j : ℕ)) 0 c : ℤ) = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      rw [Finset.mem_filter] at hc
      rw [dyckFrom_zero_parity (2 * (i : ℕ)) c (by omega)]; simp
    rw [hodd0, add_zero]
    symm
    have hfin : ∑ k : Fin n, (dyckFrom (2 * (i : ℕ)) 0 (2 * (k : ℕ)) : ℤ) *
          (dyckFrom (2 * (j : ℕ)) 0 (2 * (k : ℕ)) : ℤ) =
        ∑ k ∈ Finset.range ((i : ℕ) + 1),
          (dyckFrom (2 * (i : ℕ)) 0 (2 * k) : ℤ) * (dyckFrom (2 * (j : ℕ)) 0 (2 * k) : ℤ) := by
      rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
        (dyckFrom (2 * (i : ℕ)) 0 (2 * k) : ℤ) * (dyckFrom (2 * (j : ℕ)) 0 (2 * k) : ℤ))]
      symm
      refine Finset.sum_subset (Finset.range_mono (by omega)) fun k hk hnot => ?_
      rw [Finset.mem_range] at hk hnot
      rw [dyckFrom_eq_zero_of_lt (by omega : 0 + 2 * (i : ℕ) < 2 * k)]; simp
    rw [hfin]
    refine Finset.sum_bij (fun k _ => 2 * k) ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢; omega
    · intro k1 _ k2 _ heq; omega
    · intro c hc; simp only [Finset.mem_filter, Finset.mem_range] at hc
      exact ⟨c / 2, Finset.mem_range.mpr (by omega), by omega⟩
    · intro k _; rfl
  rw [hmat, Matrix.det_mul, Matrix.det_transpose, hL_det, mul_one]

private lemma catalan_shift_hankel_facts (m : ℕ) :
    let B1 : Matrix (Fin m) (Fin m) ℤ := Matrix.of fun i j => (catalan (i + j + 1) : ℤ)
    let b0 : Fin m → ℤ := fun i => (catalan i : ℤ)
    B1.det = 1 ∧ (∑ i : Fin m, ∑ j : Fin m, b0 i * B1⁻¹ i j * b0 j) = (m : ℤ) := by
  intro B1 b0
  let L1 : Matrix (Fin m) (Fin m) ℤ :=
    Matrix.of fun i k => (dyckFrom (2 * (i : ℕ) + 1) 0 (2 * (k : ℕ) + 1) : ℤ)
  have hL1_det : L1.det = 1 := by
    have htri : L1.IsLowerTriangular := by
      intro i k hik
      have hlt : (i : ℕ) < (k : ℕ) := hik
      change (dyckFrom (2 * (i : ℕ) + 1) 0 (2 * (k : ℕ) + 1) : ℤ) = 0
      rw [dyckFrom_eq_zero_of_lt (by omega : 0 + (2 * (i : ℕ) + 1) < 2 * (k : ℕ) + 1), Nat.cast_zero]
    rw [Matrix.det_of_isLowerTriangular L1 htri]
    refine Finset.prod_eq_one fun i _ => ?_
    have h1 := dyckFrom_self (2 * (i : ℕ) + 1) 0
    rw [zero_add] at h1
    change (dyckFrom (2 * (i : ℕ) + 1) 0 (2 * (i : ℕ) + 1) : ℤ) = 1
    simp [h1]
  have hmat : B1 = L1 * L1ᵀ := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, B1, L1]
    rw [← dyckFrom_catalan ((i : ℕ) + (j : ℕ) + 1),
      show 2 * ((i : ℕ) + (j : ℕ) + 1) = (2 * (i : ℕ) + 1) + (2 * (j : ℕ) + 1) by ring,
      dyckFrom_add]
    have hcast : ((∑ c ∈ Finset.range (0 + (2 * (i : ℕ) + 1) + 1),
        dyckFrom (2 * (i : ℕ) + 1) 0 c * dyckFrom (2 * (j : ℕ) + 1) c 0 : ℕ) : ℤ) =
        ∑ c ∈ Finset.range (2 * (i : ℕ) + 2),
          (dyckFrom (2 * (i : ℕ) + 1) 0 c : ℤ) * (dyckFrom (2 * (j : ℕ) + 1) 0 c : ℤ) := by
      rw [zero_add, Nat.cast_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Nat.cast_mul, dyckFrom_symm (2 * (j : ℕ) + 1) c 0]
    rw [hcast]
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (2 * (i : ℕ) + 2)) (fun c => c % 2 = 1)]
    have hev0 : ∑ c ∈ (Finset.range (2 * (i : ℕ) + 2)).filter (fun c => ¬ c % 2 = 1),
        (dyckFrom (2 * (i : ℕ) + 1) 0 c : ℤ) * (dyckFrom (2 * (j : ℕ) + 1) 0 c : ℤ) = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      rw [Finset.mem_filter] at hc
      rw [dyckFrom_zero_parity (2 * (i : ℕ) + 1) c (by omega)]; simp
    rw [hev0, add_zero]
    symm
    have hfin : ∑ k : Fin m, (dyckFrom (2 * (i : ℕ) + 1) 0 (2 * (k : ℕ) + 1) : ℤ) *
          (dyckFrom (2 * (j : ℕ) + 1) 0 (2 * (k : ℕ) + 1) : ℤ) =
        ∑ k ∈ Finset.range ((i : ℕ) + 1),
          (dyckFrom (2 * (i : ℕ) + 1) 0 (2 * k + 1) : ℤ) *
            (dyckFrom (2 * (j : ℕ) + 1) 0 (2 * k + 1) : ℤ) := by
      rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
        (dyckFrom (2 * (i : ℕ) + 1) 0 (2 * k + 1) : ℤ) *
          (dyckFrom (2 * (j : ℕ) + 1) 0 (2 * k + 1) : ℤ))]
      symm
      refine Finset.sum_subset (Finset.range_mono (by omega)) fun k hk hnot => ?_
      rw [Finset.mem_range] at hk hnot
      rw [dyckFrom_eq_zero_of_lt (by omega : 0 + (2 * (i : ℕ) + 1) < 2 * k + 1)]; simp
    rw [hfin]
    refine Finset.sum_bij (fun k _ => 2 * k + 1) ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢; omega
    · intro k1 _ k2 _ heq; omega
    · intro c hc; simp only [Finset.mem_filter, Finset.mem_range] at hc
      exact ⟨c / 2, Finset.mem_range.mpr (by omega), by omega⟩
    · intro k _; rfl
  have hB1_det : B1.det = 1 := by rw [hmat, Matrix.det_mul, Matrix.det_transpose, hL1_det, mul_one]
  refine ⟨hB1_det, ?_⟩
  -- Alternating vector alt(k) = (-1)^k satisfies L1 *ᵥ alt = b0!
  let alt : Fin m → ℤ := fun k => (-1 : ℤ) ^ (k : ℕ)
  have hL1_alt : L1.mulVec alt = b0 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, L1, Matrix.of_apply, alt, b0]
    have hfin : ∑ k : Fin m, (dyckFrom (2 * (i : ℕ) + 1) 0 (2 * (k : ℕ) + 1) : ℤ) * (-1 : ℤ) ^ (k : ℕ) =
        ∑ k ∈ Finset.range ((i : ℕ) + 1),
          (dyckFrom (2 * (i : ℕ) + 1) 0 (2 * k + 1) : ℤ) * (-1 : ℤ) ^ k := by
      rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
        (dyckFrom (2 * (i : ℕ) + 1) 0 (2 * k + 1) : ℤ) * (-1 : ℤ) ^ k)]
      symm
      refine Finset.sum_subset (Finset.range_mono (by omega)) fun k hk hnot => ?_
      rw [Finset.mem_range] at hk hnot
      rw [dyckFrom_eq_zero_of_lt (by omega : 0 + (2 * (i : ℕ) + 1) < 2 * k + 1)]; simp
    rw [hfin]
    -- Telescope using dyckFrom (2*i + 1) 0 (2*k + 1) = dyckFrom (2*i) 0 (2*k) + dyckFrom (2*i) 0 (2*k + 2)
    have htel : ∀ N : ℕ, ∑ k ∈ Finset.range (N + 1),
        ((dyckFrom (2 * (i : ℕ)) 0 (2 * k) : ℤ) + (dyckFrom (2 * (i : ℕ)) 0 (2 * (k + 1)) : ℤ)) * (-1 : ℤ) ^ k =
        (dyckFrom (2 * (i : ℕ)) 0 0 : ℤ) + (-1 : ℤ) ^ N * (dyckFrom (2 * (i : ℕ)) 0 (2 * (N + 1)) : ℤ) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]; ring
    have hsum_eq : ∑ k ∈ Finset.range ((i : ℕ) + 1),
          (dyckFrom (2 * (i : ℕ) + 1) 0 (2 * k + 1) : ℤ) * (-1 : ℤ) ^ k =
        ∑ k ∈ Finset.range ((i : ℕ) + 1),
          ((dyckFrom (2 * (i : ℕ)) 0 (2 * k) : ℤ) + (dyckFrom (2 * (i : ℕ)) 0 (2 * (k + 1)) : ℤ)) * (-1 : ℤ) ^ k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [dyckFrom, show 2 * (k + 1) = 2 * k + 2 by ring, Nat.cast_add]
    rw [hsum_eq, htel (i : ℕ), dyckFrom_eq_zero_of_lt (by omega : 0 + 2 * (i : ℕ) < 2 * ((i : ℕ) + 1)),
      Nat.cast_zero, mul_zero, add_zero, dyckFrom_catalan]
  -- Now b0ᵀ * B1⁻¹ * b0 = altᵀ * L1ᵀ * (L1 * L1ᵀ)⁻¹ * L1 * alt = altᵀ * alt = m!
  have hL1_unit : IsUnit L1.det := by rw [hL1_det]; exact isUnit_one
  have hB1_inv : B1⁻¹ = (L1ᵀ)⁻¹ * L1⁻¹ := by
    rw [hmat, Matrix.mul_inv_rev]
  have hquad : (∑ i : Fin m, ∑ j : Fin m, b0 i * B1⁻¹ i j * b0 j) =
      dotProduct b0 (B1⁻¹.mulVec b0) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hquad, ← hL1_alt, hB1_inv]
  have hL1_inv_cancel : ((L1ᵀ)⁻¹ * L1⁻¹).mulVec (L1.mulVec alt) = (L1ᵀ)⁻¹.mulVec alt := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hL1_unit, Matrix.mul_one]
  rw [hL1_inv_cancel]
  have hdot : dotProduct (L1.mulVec alt) ((L1ᵀ)⁻¹.mulVec alt) =
      dotProduct alt (L1ᵀ.mulVec ((L1ᵀ)⁻¹.mulVec alt)) := by
    rw [← Matrix.vecMul_transpose]
    exact (Matrix.dotProduct_mulVec alt L1ᵀ ((L1ᵀ)⁻¹.mulVec alt)).symm
  have hL1t_unit : IsUnit (L1ᵀ).det := by rw [Matrix.det_transpose]; exact hL1_unit
  rw [hdot, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hL1t_unit, Matrix.one_mulVec]
  simp only [dotProduct, alt]
  have hsq : ∀ k : Fin m, (-1 : ℤ) ^ (k : ℕ) * (-1 : ℤ) ^ (k : ℕ) = 1 := fun k => by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  simp [hsq]

/-! ### Section 4: Block Schur complement & Leibniz mod-4 / mod-8 determinant lemmas -/

private lemma det_fromBlocks_of_isUnit_ur {R : Type*} [CommRing R] {k : ℕ}
    (A B C D : Matrix (Fin k) (Fin k) R) (hB : IsUnit B.det) :
    (Matrix.fromBlocks A B D C).det = (-1 : R) ^ k * B.det * (D - C * B⁻¹ * A).det := by
  let S : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R :=
    Matrix.fromBlocks (0 : Matrix (Fin k) (Fin k) R) 1 1 0
  have hprod : Matrix.fromBlocks A B D C * S = Matrix.fromBlocks B A C D := by
    rw [Matrix.fromBlocks_multiply]
    simp
  have hS_det : S.det = (-1 : R) ^ k := by
    have h1 : S = (1 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R).submatrix
        (Equiv.sumComm (Fin k) (Fin k)) id := by
      ext (i | i) (j | j) <;> simp [S, Matrix.one_apply]
    rw [h1, Matrix.det_permute, Matrix.det_one, mul_one]
    -- sign of Equiv.sumComm on Fin k ⊕ Fin k is (-1)^k!
    have hsign : (Equiv.Perm.sign (Equiv.sumComm (Fin k) (Fin k)) : R) = (-1 : R) ^ k := by
      -- Equiv.sumComm is product of k disjoint transpositions (inl i, inr i)!
      have hcomm : Equiv.sumComm (Fin k) (Fin k) =
          (List.ofFn (fun i : Fin k => Equiv.swap (Sum.inl i) (Sum.inr i))).prod := by
        ext x
        have hact : ∀ (l : List (Fin k)) (hl : l.Nodup) (y : Fin k ⊕ Fin k),
            (l.map (fun i => Equiv.swap (Sum.inl i) (Sum.inr i))).prod y =
            match y with
            | Sum.inl j => if j ∈ l then Sum.inr j else Sum.inl j
            | Sum.inr j => if j ∈ l then Sum.inl j else Sum.inr j := by
          intro l
          induction l with
          | nil => intro _ y; cases y <;> simp
          | cons a t ih =>
            intro hl y
            rw [List.nodup_cons] at hl
            simp only [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
            rw [ih hl.2]
            cases y with
            | inl j =>
              by_cases hja : j = a
              · subst hja; simp [hl.1, Equiv.swap_apply_left]
              · by_cases hjt : j ∈ t
                · simp [hjt, hja, Equiv.swap_apply_of_ne_of_ne]
                · simp [hjt, hja, Equiv.swap_apply_of_ne_of_ne]
            | inr j =>
              by_cases hja : j = a
              · subst hja; simp [hl.1, Equiv.swap_apply_right]
              · by_cases hjt : j ∈ t
                · simp [hjt, hja, Equiv.swap_apply_of_ne_of_ne]
                · simp [hjt, hja, Equiv.swap_apply_of_ne_of_ne]
        have hlist : List.ofFn (fun i : Fin k => Equiv.swap (Sum.inl i) (Sum.inr i)) =
            (List.finRange k).map (fun i => Equiv.swap (Sum.inl i) (Sum.inr i)) := by
          apply List.ext_getElem (by simp)
          intro i h1 h2; simp
        rw [hlist, hact (List.finRange k) (List.nodup_finRange k) x]
        cases x <;> simp [List.mem_finRange]
      rw [hcomm, map_list_prod]
      have hmap : ((List.ofFn fun i : Fin k => Equiv.swap (Sum.inl i) (Sum.inr i)).map
          (Equiv.Perm.sign (α := Fin k ⊕ Fin k))) = List.replicate k (-1 : ℤˣ) := by
        apply List.ext_getElem
        · simp
        · intro i h1 h2
          simp [Equiv.Perm.sign_swap (Sum.inl_ne_inr)]
      rw [hmap, List.prod_replicate]
      simp
    exact hsign
  have h1 := congrArg Matrix.det hprod
  haveI : Invertible B := Matrix.invertibleOfIsUnitDet B hB
  have hBinv : ⅟B = B⁻¹ := invOf_eq_right_inv (Matrix.mul_nonsing_inv B hB)
  rw [Matrix.det_mul, hS_det, Matrix.det_fromBlocks₁₁ B A C D, hBinv] at h1
  -- Since ((-1)^k)^2 = 1, multiply both sides by (-1)^k
  have hsq : (-1 : R) ^ k * (-1 : R) ^ k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have h2 := congrArg (fun x => x * (-1 : R) ^ k) h1
  rw [mul_assoc, hsq, mul_one] at h2
  rw [h2]; ring

private lemma det_one_add_two_mul_zmod4 {k : ℕ} (X : Matrix (Fin k) (Fin k) (ZMod 4)) :
    (1 + (2 : ZMod 4) • X).det = 1 + 2 * X.trace := by
  rw [Matrix.det_apply]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : Equiv.Perm (Fin k)))]
  have hrest : ∑ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin k)),
      Equiv.Perm.sign σ • ∏ i : Fin k, (1 + (2 : ZMod 4) • X) (σ i) i = 0 := by
    refine Finset.sum_eq_zero fun σ hσ => ?_
    rw [Finset.mem_erase] at hσ
    have hex : ∃ i : Fin k, σ i ≠ i := by
      by_contra hall; push Not at hall
      exact hσ.1 (Equiv.ext hall)
    rcases hex with ⟨i, hi⟩
    let j := σ i
    have hji : j ≠ i := hi
    have hσj : σ j ≠ j := fun h => hji (σ.injective h)
    have hprod0 : ∏ t : Fin k, (1 + (2 : ZMod 4) • X) (σ t) t = 0 := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      rw [← Finset.mul_prod_erase (Finset.univ.erase i) _ (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)]
      set P := ∏ x ∈ (Finset.univ.erase i).erase j, (1 + (2 : ZMod 4) • X) (σ x) x
      have h1 : (1 + (2 : ZMod 4) • X) (σ i) i = 2 * X (σ i) i := by
        simp [Matrix.one_apply, hi]
      have h2 : (1 + (2 : ZMod 4) • X) (σ j) j = 2 * X (σ j) j := by
        simp [Matrix.one_apply, hσj]
      rw [h1, h2]
      have h4 : (2 : ZMod 4) * (2 : ZMod 4) = 0 := by decide
      calc (2 * X (σ i) i) * (2 * X (σ j) j * P)
          = ((2 : ZMod 4) * 2) * (X (σ i) i * X (σ j) j * P) := by ring
        _ = 0 := by rw [h4, zero_mul]
    rw [hprod0, smul_zero]
  rw [hrest, add_zero, map_one, one_smul]
  -- Evaluate ∏ i, (1 + 2 * X i i) = 1 + 2 * ∑ i, X i i in ZMod 4
  have hprod_id : ∀ s : Finset (Fin k),
      ∏ i ∈ s, (1 + (2 : ZMod 4) * X i i) = 1 + 2 * ∑ i ∈ s, X i i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
      have h4 : (2 : ZMod 4) * (2 : ZMod 4) = 0 := by decide
      calc (1 + 2 * X a a) * (1 + 2 * ∑ x ∈ s, X x x)
          = 1 + 2 * (X a a + ∑ x ∈ s, X x x) + ((2 : ZMod 4) * 2) * (X a a * ∑ x ∈ s, X x x) := by ring
        _ = 1 + 2 * (X a a + ∑ x ∈ s, X x x) := by rw [h4, zero_mul, add_zero]
  simpa [Matrix.trace, Matrix.diag] using hprod_id Finset.univ

private lemma det_one_sub_col0_sub_four_zmod8 {k : ℕ} (hk : 0 < k)
    (v : Fin k → ZMod 8) (N : Matrix (Fin k) (Fin k) (ZMod 8)) :
    let M : Matrix (Fin k) (Fin k) (ZMod 8) := Matrix.of fun i j => if j = ⟨0, hk⟩ then 2 * v i else 0
    (1 - M - (4 : ZMod 8) • N).det = 1 - 2 * v ⟨0, hk⟩ - 4 * N.trace := by
  intro M
  rw [Matrix.det_apply]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : Equiv.Perm (Fin k)))]
  have hrest : ∑ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin k)),
      Equiv.Perm.sign σ • ∏ i : Fin k, (1 - M - (4 : ZMod 8) • N) (σ i) i = 0 := by
    refine Finset.sum_eq_zero fun σ hσ => ?_
    rw [Finset.mem_erase] at hσ
    have hex : ∃ i : Fin k, σ i ≠ i := by
      by_contra hall; push Not at hall
      exact hσ.1 (Equiv.ext hall)
    rcases hex with ⟨i, hi⟩
    let j := σ i
    have hji : j ≠ i := hi
    have hσj : σ j ≠ j := fun h => hji (σ.injective h)
    have hprod0 : ∏ t : Fin k, (1 - M - (4 : ZMod 8) • N) (σ t) t = 0 := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      rw [← Finset.mul_prod_erase (Finset.univ.erase i) _ (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)]
      set P := ∏ x ∈ (Finset.univ.erase i).erase j, (1 - M - (4 : ZMod 8) • N) (σ x) x
      have h8 : (2 : ZMod 8) * (4 : ZMod 8) = 0 := by decide
      have h16 : (4 : ZMod 8) * (4 : ZMod 8) = 0 := by decide
      by_cases hi0 : i = ⟨0, hk⟩
      · have hj0 : j ≠ ⟨0, hk⟩ := fun h => hji (h.trans hi0.symm)
        have hσ0 : σ ⟨0, hk⟩ ≠ ⟨0, hk⟩ := by rwa [← hi0]
        have h1 : (1 - M - (4 : ZMod 8) • N) (σ i) i = -(2 * v (σ i)) - 4 * N (σ i) i := by
          simp [M, hi0, hσ0]
        have h2 : (1 - M - (4 : ZMod 8) • N) (σ j) j = -(4 * N (σ j) j) := by
          simp [hσj, M, hj0]
        rw [h1, h2]
        calc (-(2 * v (σ i)) - 4 * N (σ i) i) * (-(4 * N (σ j) j) * P)
            = ((2 : ZMod 8) * 4) * (v (σ i) * N (σ j) j * P) +
              ((4 : ZMod 8) * 4) * (N (σ i) i * N (σ j) j * P) := by ring
          _ = 0 := by rw [h8, h16, zero_mul, zero_mul, add_zero]
      · by_cases hj0 : j = ⟨0, hk⟩
        · have hσ0 : σ ⟨0, hk⟩ ≠ ⟨0, hk⟩ := by rwa [← hj0]
          have h1 : (1 - M - (4 : ZMod 8) • N) (σ i) i = -(4 * N (σ i) i) := by
            simp [hi, M, hi0]
          have h2 : (1 - M - (4 : ZMod 8) • N) (σ j) j = -(2 * v (σ j)) - 4 * N (σ j) j := by
            simp [M, hj0, hσ0]
          rw [h1, h2]
          calc -(4 * N (σ i) i) * ((-(2 * v (σ j)) - 4 * N (σ j) j) * P)
              = ((2 : ZMod 8) * 4) * (N (σ i) i * v (σ j) * P) +
                ((4 : ZMod 8) * 4) * (N (σ i) i * N (σ j) j * P) := by ring
            _ = 0 := by rw [h8, h16, zero_mul, zero_mul, add_zero]
        · have h1 : (1 - M - (4 : ZMod 8) • N) (σ i) i = -(4 * N (σ i) i) := by
            simp [hi, M, hi0]
          have h2 : (1 - M - (4 : ZMod 8) • N) (σ j) j = -(4 * N (σ j) j) := by
            simp [hσj, M, hj0]
          rw [h1, h2]
          calc -(4 * N (σ i) i) * (-(4 * N (σ j) j) * P)
              = ((4 : ZMod 8) * 4) * (N (σ i) i * N (σ j) j * P) := by ring
            _ = 0 := by rw [h16, zero_mul]
    rw [hprod0, smul_zero]
  rw [hrest, add_zero, map_one, one_smul]
  simp only [Equiv.Perm.coe_one, id_eq]
  -- Evaluate ∏ i, (1 - M i i - 4 * N i i)
  have hprod_rest : ∀ s : Finset (Fin k),
      ∏ i ∈ s, (1 - (4 : ZMod 8) * N i i) = 1 - 4 * ∑ i ∈ s, N i i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
      have h16 : (4 : ZMod 8) * (4 : ZMod 8) = 0 := by decide
      calc (1 - 4 * N a a) * (1 - 4 * ∑ x ∈ s, N x x)
          = 1 - 4 * (N a a + ∑ x ∈ s, N x x) + ((4 : ZMod 8) * 4) * (N a a * ∑ x ∈ s, N x x) := by ring
        _ = 1 - 4 * (N a a + ∑ x ∈ s, N x x) := by rw [h16, zero_mul, add_zero]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ⟨0, hk⟩)]
  have herase : ∏ i ∈ Finset.univ.erase ⟨0, hk⟩, (1 - M - (4 : ZMod 8) • N) i i =
      ∏ i ∈ Finset.univ.erase ⟨0, hk⟩, (1 - (4 : ZMod 8) * N i i) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hne : i ≠ ⟨0, hk⟩ := (Finset.mem_erase.mp hi).1
    simp [M, hne]
  rw [herase, hprod_rest]
  simp only [Equiv.Perm.coe_one, id_eq, Matrix.sub_apply, Matrix.one_apply_eq, M, Matrix.of_apply,
    ↓reduceIte, Matrix.smul_apply, smul_eq_mul]
  have htr : N.trace = N ⟨0, hk⟩ ⟨0, hk⟩ + ∑ i ∈ Finset.univ.erase ⟨0, hk⟩, N i i := by
    simp only [Matrix.trace, Matrix.diag]
    exact (Finset.add_sum_erase Finset.univ (fun i => N i i) (Finset.mem_univ ⟨0, hk⟩)).symm
  rw [htr]
  have h8 : (2 : ZMod 8) * (4 : ZMod 8) = 0 := by decide
  have h16 : (4 : ZMod 8) * (4 : ZMod 8) = 0 := by decide
  calc (1 - 2 * v ⟨0, hk⟩ - 4 * N ⟨0, hk⟩ ⟨0, hk⟩) * (1 - 4 * ∑ i ∈ Finset.univ.erase ⟨0, hk⟩, N i i)
      = 1 - 2 * v ⟨0, hk⟩ - 4 * (N ⟨0, hk⟩ ⟨0, hk⟩ + ∑ i ∈ Finset.univ.erase ⟨0, hk⟩, N i i) +
        ((2 : ZMod 8) * 4) * (v ⟨0, hk⟩ * ∑ i ∈ Finset.univ.erase ⟨0, hk⟩, N i i) +
        ((4 : ZMod 8) * 4) * (N ⟨0, hk⟩ ⟨0, hk⟩ * ∑ i ∈ Finset.univ.erase ⟨0, hk⟩, N i i) := by ring
    _ = 1 - 2 * v ⟨0, hk⟩ - 4 * (N ⟨0, hk⟩ ⟨0, hk⟩ + ∑ i ∈ Finset.univ.erase ⟨0, hk⟩, N i i) := by
        rw [h8, h16, zero_mul, zero_mul, add_zero, add_zero]

/-! ### Section 5: Main mod-8 theorem (odd n ≡ 3^(m+1) mod 8; even n ≡ 1 mod 4) -/

private lemma zmod8_sq_of_odd (x : ZMod 8) (hx : IsUnit x) : x * x = 1 := by
  rcases hx with ⟨u, hu⟩
  have hex : ∃ y : ZMod 8, x * y = 1 := ⟨(u⁻¹ : (ZMod 8)ˣ), by rw [← hu]; exact u.mul_inv⟩
  revert hex; fin_cases x <;> decide

private lemma zmod4_sq_of_odd (x : ZMod 4) (hx : IsUnit x) : x * x = 1 := by
  rcases hx with ⟨u, hu⟩
  have hex : ∃ y : ZMod 4, x * y = 1 := ⟨(u⁻¹ : (ZMod 4)ˣ), by rw [← hu]; exact u.mul_inv⟩
  revert hex; fin_cases x <;> decide

private lemma zmod8_isUnit_of_mod2_eq_one (x : ZMod 8)
    (hx : ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2) x = 1) : IsUnit x := by
  suffices h : x * x = 1 from isUnit_iff_exists_inv.mpr ⟨x, h⟩
  revert hx; fin_cases x <;> decide

private lemma zmod4_isUnit_of_mod2_eq_one (x : ZMod 4)
    (hx : ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) x = 1) : IsUnit x := by
  suffices h : x * x = 1 from isUnit_iff_exists_inv.mpr ⟨x, h⟩
  revert hx; fin_cases x <;> decide

private lemma trace_alt_mul_symm_zmod2 {k : ℕ}
    (X A : Matrix (Fin k) (Fin k) (ZMod 2))
    (hXs : Xᵀ = X) (hXd : ∀ i, X i i = 0) (hAs : Aᵀ = A) :
    (X * A).trace = 0 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  -- Pair (i, j) with (j, i): since X j i * A i j = X i j * A j i, off-diagonal pairs cancel in ZMod 2!
  have hdiag : ∑ i : Fin k, ∑ j : Fin k, X i j * A j i =
      ∑ p : Fin k × Fin k, X p.1 p.2 * A p.2 p.1 :=
    (Fintype.sum_prod_type (fun p : Fin k × Fin k => X p.1 p.2 * A p.2 p.1)).symm
  rw [hdiag]
  have hsplit : ∑ p : Fin k × Fin k, X p.1 p.2 * A p.2 p.1 =
      (∑ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 = p.2), X p.1 p.2 * A p.2 p.1) +
      (∑ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2), X p.1 p.2 * A p.2 p.1) +
      (∑ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.2 < p.1), X p.1 p.2 * A p.2 p.1) := by
    rw [← Finset.sum_union, ← Finset.sum_union]
    · congr 1; ext ⟨i, j⟩
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases lt_trichotomy i j with h | h | h <;> simp [h]
    · rw [Finset.disjoint_left]; intro ⟨i, j⟩ h1 h2
      simp only [Finset.mem_union, Finset.mem_filter] at h1 h2
      omega
    · rw [Finset.disjoint_left]; intro ⟨i, j⟩ h1 h2
      simp only [Finset.mem_filter] at h1 h2
      omega
  rw [hsplit]
  have h0 : ∑ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 = p.2), X p.1 p.2 * A p.2 p.1 = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.mem_filter] at hp; rw [hp.2, hXd, zero_mul]
  have hpair : ∑ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.2 < p.1), X p.1 p.2 * A p.2 p.1 =
      ∑ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2), X p.1 p.2 * A p.2 p.1 := by
    refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro ⟨i, j⟩ hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp
    · intro ⟨i1, j1⟩ _ ⟨i2, j2⟩ _ heq; cases heq; rfl
    · intro ⟨i, j⟩ hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact ⟨(j, i), by simp [hp], rfl⟩
    · intro ⟨i, j⟩ _
      have hXij : X i j = X j i := by simpa using congrFun (congrFun hXs j) i
      have hAji : A j i = A i j := by simpa using congrFun (congrFun hAs i) j
      rw [hXij, hAji]
  rw [h0, zero_add, hpair, ← two_mul]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_mul]

private lemma quad_form_symm_split {R : Type*} [CommRing R] {k : ℕ}
    (M : Matrix (Fin k) (Fin k) R) (hMs : Mᵀ = M) (v : Fin k → R) :
    (∑ r : Fin k, ∑ s : Fin k, v r * M r s * v s) =
      (∑ r : Fin k, v r * v r * M r r) +
      2 * ∑ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2), v p.1 * M p.1 p.2 * v p.2 := by
  have hprod : (∑ r : Fin k, ∑ s : Fin k, v r * M r s * v s) =
      ∑ p : Fin k × Fin k, v p.1 * M p.1 p.2 * v p.2 :=
    (Fintype.sum_prod_type (fun p : Fin k × Fin k => v p.1 * M p.1 p.2 * v p.2)).symm
  rw [hprod]
  have hsplit : ∑ p : Fin k × Fin k, v p.1 * M p.1 p.2 * v p.2 =
      (∑ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 = p.2), v p.1 * M p.1 p.2 * v p.2) +
      (∑ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2), v p.1 * M p.1 p.2 * v p.2) +
      (∑ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.2 < p.1), v p.1 * M p.1 p.2 * v p.2) := by
    rw [← Finset.sum_union, ← Finset.sum_union]
    · congr 1; ext ⟨i, j⟩
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases lt_trichotomy i j with h | h | h <;> simp [h]
    · rw [Finset.disjoint_left]; intro ⟨i, j⟩ h1 h2
      simp only [Finset.mem_union, Finset.mem_filter] at h1 h2; omega
    · rw [Finset.disjoint_left]; intro ⟨i, j⟩ h1 h2
      simp only [Finset.mem_filter] at h1 h2; omega
  rw [hsplit]
  have hdiag : ∑ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 = p.2), v p.1 * M p.1 p.2 * v p.2 =
      ∑ r : Fin k, v r * v r * M r r := by
    refine Finset.sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
    · intro p _; exact Finset.mem_univ _
    · intro ⟨i1, j1⟩ h1 ⟨i2, j2⟩ h2 heq
      simp only [Finset.mem_filter] at h1 h2; dsimp only at heq; subst heq; cases h1.2; cases h2.2; rfl
    · intro r _; exact ⟨(r, r), by simp, rfl⟩
    · intro ⟨i, j⟩ h; simp only [Finset.mem_filter] at h; rcases h with ⟨_, rfl⟩; ring
  have hpair : ∑ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.2 < p.1), v p.1 * M p.1 p.2 * v p.2 =
      ∑ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2), v p.1 * M p.1 p.2 * v p.2 := by
    refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro ⟨i, j⟩ hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp
    · intro ⟨i1, j1⟩ _ ⟨i2, j2⟩ _ heq; cases heq; rfl
    · intro ⟨i, j⟩ hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact ⟨(j, i), by simp [hp], rfl⟩
    · intro ⟨i, j⟩ _
      have hM : M i j = M j i := by simpa using congrFun (congrFun hMs j) i
      rw [hM]; ring
  rw [hdiag, hpair]; ring

private lemma catalan_mod2_parity_support (m : ℕ)
    (v : Fin (m + 1) → ZMod 2)
    (hv : (Matrix.of fun i j : Fin (m + 1) => (catalan ((i : ℕ) + (j : ℕ)) : ZMod 2)).mulVec v =
      fun i => if i = 0 then 1 else 0) :
    v 0 = (if m % 2 = 0 then 1 else 0) ∧
    ∀ r : Fin (m + 1), v r ≠ 0 → (r : ℕ) % 2 = m % 2 := by
  let B2 : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2) :=
    Matrix.of fun i j => (catalan ((i : ℕ) + (j : ℕ)) : ZMod 2)
  have hB2_det : B2.det = 1 := by
    have h1 := congrArg (Int.castRingHom (ZMod 2)) (catalan_hankel_det_one (m + 1))
    rw [RingHom.map_det] at h1
    have hmap : (Int.castRingHom (ZMod 2)).mapMatrix
        (Matrix.of fun i j : Fin (m + 1) => (catalan ((i : ℕ) + (j : ℕ)) : ℤ)) = B2 := by
      ext i j; simp [B2]
    rw [hmap, map_one] at h1
    exact h1
  have hB2_entry : ∀ i j : Fin (m + 1),
      B2 i j = if ∃ t : ℕ, (i : ℕ) + (j : ℕ) + 1 = 2 ^ t then 1 else 0 := by
    intro i j
    simp only [B2, Matrix.of_apply]
    have hcat_ne : catalan ((i : ℕ) + (j : ℕ)) ≠ 0 := catalan_ne_zero _
    split_ifs with hpow
    · have hv0 : padicValNat 2 (catalan ((i : ℕ) + (j : ℕ))) = 0 := by
        rw [v2_catalan, (s2_eq_one_iff _).mpr hpow]
      have hnd : ¬ 2 ∣ catalan ((i : ℕ) + (j : ℕ)) := fun hd => by
        have := (pow_two_dvd_iff_le_v2 hcat_ne).mp (by simpa using hd : 2 ^ 1 ∣ _); omega
      have hmod : catalan ((i : ℕ) + (j : ℕ)) % 2 = 1 := by omega
      rw [← ZMod.natCast_mod, hmod]; simp
    · have hs2 : 2 ≤ s2 ((i : ℕ) + (j : ℕ) + 1) := by
        have h1 := s2_pos_of_pos (by omega : 0 < (i : ℕ) + (j : ℕ) + 1)
        have hne : s2 ((i : ℕ) + (j : ℕ) + 1) ≠ 1 := fun h => hpow ((s2_eq_one_iff _).mp h)
        omega
      have hd : 2 ∣ catalan ((i : ℕ) + (j : ℕ)) := by
        have := (pow_two_dvd_iff_le_v2 hcat_ne).mpr (by rw [v2_catalan]; omega : 1 ≤ _); simpa using this
      exact (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have hB2_same_par : ∀ i j : Fin (m + 1), (i : ℕ) % 2 = (j : ℕ) % 2 → ¬ (i = 0 ∧ j = 0) → B2 i j = 0 := by
    intro i j hpar hne
    rw [hB2_entry]
    split_ifs with hpow
    · exfalso
      rcases hpow with ⟨t, ht⟩
      have hge3 : 3 ≤ (i : ℕ) + (j : ℕ) + 1 := by
        by_contra hlt; apply hne; constructor <;> (apply Fin.ext; simp only [Fin.val_zero]; omega)
      cases t with
      | zero => omega
      | succ t =>
        have : 2 ∣ 2 ^ (t + 1) := dvd_pow_self 2 (by omega)
        rw [← ht] at this; omega
    · rfl
  have hB2_00 : B2 0 0 = 1 := by simp [B2, catalan_zero]
  -- Split cases on parity of m!
  by_cases hm_ev : m % 2 = 0
  · obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
    simp only [show 2 * k % 2 = 0 by omega, ↓reduceIte]
    -- Permute Fin (2*k+1) ≃ (Unit ⊕ Fin k) ⊕ Fin k: inl (inl ()) -> 0, inl (inr a) -> 2a+2, inr b -> 2b+1
    let e : (Unit ⊕ Fin k) ⊕ Fin k ≃ Fin (2 * k + 1) :=
      { toFun := fun x => match x with
          | Sum.inl (Sum.inl ()) => ⟨0, by omega⟩
          | Sum.inl (Sum.inr a) => ⟨2 * (a : ℕ) + 2, by omega⟩
          | Sum.inr b => ⟨2 * (b : ℕ) + 1, by omega⟩
        invFun := fun i =>
          if h0 : (i : ℕ) = 0 then Sum.inl (Sum.inl ())
          else if he : (i : ℕ) % 2 = 0 then Sum.inl (Sum.inr ⟨(i : ℕ) / 2 - 1, by omega⟩)
          else Sum.inr ⟨(i : ℕ) / 2, by omega⟩
        left_inv := fun x => by
          rcases x with (⟨⟩ | a) | b
          · simp
          · simp only [show 2 * (a : ℕ) + 2 ≠ 0 by omega, ↓reduceDIte, show (2 * (a : ℕ) + 2) % 2 = 0 by omega]
            congr 2; ext; simp
          · simp only [show 2 * (b : ℕ) + 1 ≠ 0 by omega, ↓reduceDIte, show (2 * (b : ℕ) + 1) % 2 ≠ 0 by omega]
            congr 1; ext; simp; omega
        right_inv := fun i => by
          by_cases h0 : (i : ℕ) = 0
          · ext; simp [h0]
          · by_cases he : (i : ℕ) % 2 = 0
            · ext; simp [h0, he]; omega
            · ext; simp [h0, he]; omega }
    -- Let U : Matrix (Fin k) (Fin k) (ZMod 2) be B2 (2a+2) (2b+1)
    let U : Matrix (Fin k) (Fin k) (ZMod 2) :=
      Matrix.of fun a b => B2 ⟨2 * (a : ℕ) + 2, by omega⟩ ⟨2 * (b : ℕ) + 1, by omega⟩
    -- Prove U.det = 1 by showing (B2.submatrix e e).det = U.det * U.det!
    have hU_det : U.det = 1 := by
      let e2 : Unit ⊕ (Fin k ⊕ Fin k) ≃ Fin (2 * k + 1) :=
        (Equiv.sumAssoc Unit (Fin k) (Fin k)).symm.trans e
      have hdet1 : (B2.submatrix e2 e2).det = 1 := by
        rw [Matrix.det_submatrix_equiv_self, hB2_det]
      let r0 : Matrix Unit (Fin k ⊕ Fin k) (ZMod 2) :=
        Matrix.of fun _ y => match y with | Sum.inl _ => 0 | Sum.inr b => B2 0 ⟨2 * (b : ℕ) + 1, by omega⟩
      let c0 : Matrix (Fin k ⊕ Fin k) Unit (ZMod 2) := r0ᵀ
      let Dblk : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) (ZMod 2) :=
        Matrix.fromBlocks (0 : Matrix (Fin k) (Fin k) (ZMod 2)) U Uᵀ 0
      have hsub : B2.submatrix e2 e2 = Matrix.fromBlocks (1 : Matrix Unit Unit (ZMod 2)) r0 c0 Dblk := by
        ext (⟨⟩ | (a | b)) (⟨⟩ | (c | d))
        · simp [e2, e, hB2_00]
        · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, r0, Matrix.of_apply, e2, e,
            Equiv.trans_apply, Equiv.sumAssoc_symm_apply_inl, Equiv.sumAssoc_symm_apply_inr_inl, Equiv.coe_fn_mk]
          exact hB2_same_par ⟨0, by omega⟩ ⟨2 * (c : ℕ) + 2, by omega⟩ (by simp)
            (by intro h; have := congrArg Fin.val h.2; simp at this)
        · simp [e2, e, r0]
        · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, c0, r0, Matrix.transpose_apply,
            Matrix.of_apply, e2, e, Equiv.trans_apply, Equiv.sumAssoc_symm_apply_inl,
            Equiv.sumAssoc_symm_apply_inr_inl, Equiv.coe_fn_mk]
          exact hB2_same_par ⟨2 * (a : ℕ) + 2, by omega⟩ ⟨0, by omega⟩ (by simp)
            (by intro h; have := congrArg Fin.val h.1; simp at this)
        · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, Dblk, Matrix.fromBlocks_apply₁₁,
            Matrix.zero_apply, e2, e, Equiv.trans_apply, Equiv.sumAssoc_symm_apply_inr_inl, Equiv.coe_fn_mk]
          exact hB2_same_par ⟨2 * (a : ℕ) + 2, by omega⟩ ⟨2 * (c : ℕ) + 2, by omega⟩ (by simp)
            (by intro h; have := congrArg Fin.val h.1; simp at this)
        · simp [e2, e, Dblk, U]
        · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, c0, r0, Matrix.transpose_apply,
            Matrix.of_apply, e2, e, Equiv.trans_apply, Equiv.sumAssoc_symm_apply_inl,
            Equiv.sumAssoc_symm_apply_inr_inr, Equiv.coe_fn_mk]
          simp [B2, add_comm]
        · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, Dblk, Matrix.fromBlocks_apply₂₁,
            Matrix.transpose_apply, U, Matrix.of_apply, e2, e, Equiv.trans_apply,
            Equiv.sumAssoc_symm_apply_inr_inr, Equiv.sumAssoc_symm_apply_inr_inl, Equiv.coe_fn_mk]
          simp [B2, add_comm]
        · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, Dblk, Matrix.fromBlocks_apply₂₂,
            Matrix.zero_apply, e2, e, Equiv.trans_apply, Equiv.sumAssoc_symm_apply_inr_inr, Equiv.coe_fn_mk]
          exact hB2_same_par ⟨2 * (b : ℕ) + 1, by omega⟩ ⟨2 * (d : ℕ) + 1, by omega⟩ (by simp)
            (by intro h; have := congrArg Fin.val h.1; simp at this)
      have : Invertible (1 : Matrix Unit Unit (ZMod 2)) := invertibleOne
      rw [hsub, Matrix.det_fromBlocks₁₁] at hdet1
      simp only [Matrix.det_one, invOf_one, Matrix.mul_one, one_mul] at hdet1
      let Xblk : Matrix (Fin k) (Fin k) (ZMod 2) :=
        -(Matrix.of fun (b d : Fin k) => B2 0 ⟨2 * (b : ℕ) + 1, by omega⟩ * B2 0 ⟨2 * (d : ℕ) + 1, by omega⟩)
      have hschur : Dblk - c0 * r0 = Matrix.fromBlocks (0 : Matrix (Fin k) (Fin k) (ZMod 2)) U Uᵀ Xblk := by
        ext (a | b) (c | d) <;> simp [Dblk, c0, r0, Xblk, Matrix.mul_apply]
      rw [hschur] at hdet1
      -- det (fromBlocks 0 U Uᵀ Xblk) = U.det * U.det in ZMod 2!
      have hdet_blk : (Matrix.fromBlocks (0 : Matrix (Fin k) (Fin k) (ZMod 2)) U Uᵀ Xblk).det =
          U.det * U.det := by
        let S : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) (ZMod 2) := Matrix.fromBlocks 0 1 1 0
        have hS : S.det = 1 := by
          have h1 := det_fromBlocks_of_isUnit_ur (0 : Matrix (Fin k) (Fin k) (ZMod 2)) 1 0 1 (by simp)
          have h2 : (-1 : ZMod 2) = 1 := by decide
          simpa [S, h2] using h1
        have hmul : Matrix.fromBlocks (0 : Matrix (Fin k) (Fin k) (ZMod 2)) U Uᵀ Xblk * S =
            Matrix.fromBlocks U 0 Xblk Uᵀ := by
          rw [Matrix.fromBlocks_multiply]; simp
        have hdetm := congrArg Matrix.det hmul
        rw [Matrix.det_mul, hS, mul_one, Matrix.det_fromBlocks_zero₁₂, Matrix.det_transpose] at hdetm
        exact hdetm
      rw [hdet_blk] at hdet1
      have hsq : ∀ z : ZMod 2, z * z = 1 → z = 1 := by decide
      exact hsq U.det hdet1
    -- Now from row 2a+2 of B2 *ᵥ v = e0, we get U *ᵥ v_odd = 0!
    let v_odd : Fin k → ZMod 2 := fun b => v ⟨2 * (b : ℕ) + 1, by omega⟩
    have hUv : U.mulVec v_odd = 0 := by
      ext a
      have hrow := congrFun hv ⟨2 * (a : ℕ) + 2, by omega⟩
      simp only [show (⟨2 * (a : ℕ) + 2, by omega⟩ : Fin (2 * k + 1)) ≠ 0 by
        intro h; have := congrArg Fin.val h; simp at this, ↓reduceIte] at hrow
      simp only [Matrix.mulVec, dotProduct, U, v_odd, Matrix.of_apply, Pi.zero_apply]
      rw [← hrow]
      simp only [Matrix.mulVec, dotProduct]
      -- Sum over Fin (2k+1) splits into even (which vanish!) and odd (= U *ᵥ v_odd)
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin (2 * k + 1) => (j : ℕ) % 2 = 1)]
      have hev0 : ∑ j ∈ Finset.univ.filter (fun j : Fin (2 * k + 1) => ¬ (j : ℕ) % 2 = 1),
          B2 ⟨2 * (a : ℕ) + 2, by omega⟩ j * v j = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [Finset.mem_filter] at hj
        rw [hB2_same_par _ _ (by simp; omega) (by intro h; have := congrArg Fin.val h.1; simp at this), zero_mul]
      rw [hev0, add_zero]
      refine Finset.sum_bij (fun b _ => ⟨2 * (b : ℕ) + 1, by omega⟩) ?_ ?_ ?_ ?_
      · intro b _; simp
      · intro b1 _ b2 _ heq; ext; have := congrArg Fin.val heq; simp at this; omega
      · intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact ⟨⟨(j : ℕ) / 2, by omega⟩, Finset.mem_univ _, by ext; simp; omega⟩
      · intro b _; rfl
    have hU_unit : IsUnit U.det := by rw [hU_det]; exact isUnit_one
    have hv_odd0 : v_odd = 0 := by
      have h1 := congrArg (U⁻¹.mulVec) hUv
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU_unit, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
      exact h1
    have hv_odd_zero : ∀ r : Fin (2 * k + 1), (r : ℕ) % 2 = 1 → v r = 0 := by
      intro r hr
      have h := congrFun hv_odd0 ⟨(r : ℕ) / 2, by omega⟩
      simp only [v_odd, Pi.zero_apply] at h
      convert h using 2; ext; simp; omega
    have hv0 : v 0 = 1 := by
      have hrow0 := congrFun hv 0
      simp only [↓reduceIte, Matrix.mulVec, dotProduct] at hrow0
      change ∑ x : Fin (2 * k + 1), B2 0 x * v x = 1 at hrow0
      rw [Finset.sum_eq_single (0 : Fin (2 * k + 1))] at hrow0
      · rw [hB2_00, one_mul] at hrow0; exact hrow0
      · intro j _ hj0
        by_cases hpar : (j : ℕ) % 2 = 1
        · rw [hv_odd_zero j hpar, mul_zero]
        · rw [hB2_same_par 0 j (by simp; omega) (by intro h; exact hj0 h.2), zero_mul]
      · intro h; exact absurd (Finset.mem_univ 0) h
    refine ⟨hv0, fun r hr => ?_⟩
    by_contra hne
    have hodd : (r : ℕ) % 2 = 1 := by omega
    exact hr (hv_odd_zero r hodd)
  · -- m is odd: m = 2*k + 1, so m + 1 = 2*(k + 1)
    obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
    simp only [show (2 * k + 1) % 2 ≠ 0 by omega, ↓reduceIte]
    -- Permute Fin (2k+2) ≃ Fin (k+1) ⊕ Fin (k+1): inl a -> 2a, inr b -> 2b+1
    let e : Fin (k + 1) ⊕ Fin (k + 1) ≃ Fin (2 * k + 2) :=
      { toFun := fun x => match x with
          | Sum.inl a => ⟨2 * (a : ℕ), by omega⟩
          | Sum.inr b => ⟨2 * (b : ℕ) + 1, by omega⟩
        invFun := fun i =>
          if h : (i : ℕ) % 2 = 0 then Sum.inl ⟨(i : ℕ) / 2, by omega⟩
          else Sum.inr ⟨(i : ℕ) / 2, by omega⟩
        left_inv := fun x => by
          cases x with
          | inl a => simp
          | inr b => simp; ext; simp; omega
        right_inv := fun i => by
          by_cases h : (i : ℕ) % 2 = 0
          · ext; simp [h]; omega
          · ext; simp [h]; omega }
    let U : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2) :=
      Matrix.of fun a b => B2 ⟨2 * (a : ℕ), by omega⟩ ⟨2 * (b : ℕ) + 1, by omega⟩
    have hU_det : U.det = 1 := by
      have hdet1 : (B2.submatrix e e).det = 1 := by
        rw [Matrix.det_submatrix_equiv_self, hB2_det]
      let E00 : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2) :=
        Matrix.of fun a c => if a = 0 ∧ c = 0 then 1 else 0
      have hsub : B2.submatrix e e = Matrix.fromBlocks E00 U Uᵀ 0 := by
        ext (a | b) (c | d)
        · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, E00, Matrix.of_apply, e, Equiv.coe_fn_mk]
          by_cases h0 : a = 0 ∧ c = 0
          · rcases h0 with ⟨rfl, rfl⟩; simp [hB2_00]
          · simp only [h0, ↓reduceIte]
            exact hB2_same_par ⟨2 * (a : ℕ), by omega⟩ ⟨2 * (c : ℕ), by omega⟩ (by simp) (by
              intro h; apply h0; constructor <;> ext <;> [have := congrArg Fin.val h.1; have := congrArg Fin.val h.2] <;> simp at * <;> omega)
        · simp [e, U]
        · simp [e, U, B2, add_comm]
        · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, e, Equiv.coe_fn_mk]
          exact hB2_same_par ⟨2 * (b : ℕ) + 1, by omega⟩ ⟨2 * (d : ℕ) + 1, by omega⟩ (by simp)
            (by intro h; have := congrArg Fin.val h.1; simp at this)
      rw [hsub] at hdet1
      let S : Matrix (Fin (k + 1) ⊕ Fin (k + 1)) (Fin (k + 1) ⊕ Fin (k + 1)) (ZMod 2) := Matrix.fromBlocks 0 1 1 0
      have hS : S.det = 1 := by
        have h1 := det_fromBlocks_of_isUnit_ur (0 : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2)) 1 0 1 (by simp)
        have h2 : (-1 : ZMod 2) = 1 := by decide
        simpa [S, h2] using h1
      have hmul : Matrix.fromBlocks E00 U Uᵀ 0 * S = Matrix.fromBlocks U E00 0 Uᵀ := by
        rw [Matrix.fromBlocks_multiply]; simp
      have hdetm := congrArg Matrix.det hmul
      rw [Matrix.det_mul, hS, mul_one, Matrix.det_fromBlocks_zero₂₁, Matrix.det_transpose] at hdetm
      rw [hdetm] at hdet1
      have hsq : ∀ z : ZMod 2, z * z = 1 → z = 1 := by decide
      exact hsq U.det hdet1
    let v_ev : Fin (k + 1) → ZMod 2 := fun a => v ⟨2 * (a : ℕ), by omega⟩
    have hUtv : Uᵀ.mulVec v_ev = 0 := by
      ext b
      have hrow := congrFun hv ⟨2 * (b : ℕ) + 1, by omega⟩
      simp only [show (⟨2 * (b : ℕ) + 1, by omega⟩ : Fin (2 * k + 2)) ≠ 0 by
        intro h; have := congrArg Fin.val h; simp at this, ↓reduceIte] at hrow
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, U, v_ev, Matrix.of_apply, Pi.zero_apply]
      rw [← hrow]
      simp only [Matrix.mulVec, dotProduct]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin (2 * k + 2) => (j : ℕ) % 2 = 0)]
      have hodd0 : ∑ j ∈ Finset.univ.filter (fun j : Fin (2 * k + 2) => ¬ (j : ℕ) % 2 = 0),
          B2 ⟨2 * (b : ℕ) + 1, by omega⟩ j * v j = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [Finset.mem_filter] at hj
        rw [hB2_same_par _ _ (by simp; omega) (by intro h; have := congrArg Fin.val h.1; simp at this), zero_mul]
      rw [hodd0, add_zero]
      refine Finset.sum_bij (fun a _ => ⟨2 * (a : ℕ), by omega⟩) ?_ ?_ ?_ ?_
      · intro a _; simp
      · intro a1 _ a2 _ heq; ext; have := congrArg Fin.val heq; simp at this; omega
      · intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact ⟨⟨(j : ℕ) / 2, by omega⟩, Finset.mem_univ _, by ext; simp; omega⟩
      · intro a _; simp [B2, add_comm]
    have hUt_unit : IsUnit (Uᵀ).det := by rw [Matrix.det_transpose, hU_det]; exact isUnit_one
    have hv_ev0 : v_ev = 0 := by
      have h1 := congrArg ((Uᵀ)⁻¹.mulVec) hUtv
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hUt_unit, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
      exact h1
    have hv_ev_zero : ∀ r : Fin (2 * k + 2), (r : ℕ) % 2 = 0 → v r = 0 := by
      intro r hr
      have h := congrFun hv_ev0 ⟨(r : ℕ) / 2, by omega⟩
      simp only [v_ev, Pi.zero_apply] at h
      convert h using 2; ext; simp; omega
    refine ⟨hv_ev_zero 0 (by simp), fun r hr => ?_⟩
    by_contra hne
    have hev : (r : ℕ) % 2 = 0 := by omega
    exact hr (hv_ev_zero r hev)
private lemma odd_hankel_mod8 (m : ℕ) :
    (a_seq (2 * m + 1) : ZMod 8) = (3 : ZMod 8) ^ (m + 1) := by
  rw [hankel_b_eq_tb_det]
  set Ht : Matrix (Fin (2 * m + 2)) (Fin (2 * m + 2)) (ZMod 8) :=
    Matrix.of fun i j => (tb ((i : ℕ) + (j : ℕ)) : ZMod 8)
  have hcast_det : ((Matrix.of fun i j : Fin (2 * m + 2) => (tb ((i : ℕ) + (j : ℕ)) : ℤ)).det : ZMod 8) =
      Ht.det := by
    have h1 := RingHom.map_det (Int.castRingHom (ZMod 8))
      (Matrix.of fun i j : Fin (2 * m + 2) => (tb ((i : ℕ) + (j : ℕ)) : ℤ))
    have hmap : (Int.castRingHom (ZMod 8)).mapMatrix
        (Matrix.of fun i j : Fin (2 * m + 2) => (tb ((i : ℕ) + (j : ℕ)) : ℤ)) = Ht := by
      ext i j; simp [Ht]
    rw [hmap] at h1
    exact h1
  rw [hcast_det]
  -- Permute Fin (2m+2) ≃ Fin (m+1) ⊕ Fin (m+1) via even (2i) and odd (2i+1)
  let e : Fin (m + 1) ⊕ Fin (m + 1) ≃ Fin (2 * m + 2) :=
    { toFun := fun x => match x with
        | Sum.inl i => ⟨2 * (i : ℕ), by omega⟩
        | Sum.inr i => ⟨2 * (i : ℕ) + 1, by omega⟩
      invFun := fun k =>
        if h : (k : ℕ) % 2 = 0 then Sum.inl ⟨(k : ℕ) / 2, by omega⟩
        else Sum.inr ⟨(k : ℕ) / 2, by omega⟩
      left_inv := fun x => by
        cases x with
        | inl i => simp
        | inr i => simp; ext; simp; omega
      right_inv := fun k => by
        by_cases h : (k : ℕ) % 2 = 0
        · ext; simp [h]; omega
        · ext; simp [h]; omega }
  have hperm_det : Ht.det = (Ht.submatrix e e).det := (Matrix.det_submatrix_equiv_self e Ht).symm
  rw [hperm_det]
  let A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 8) := Matrix.of fun i j => (tb (2 * (i + j)) : ZMod 8)
  let B : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 8) := Matrix.of fun i j => (tb (2 * (i + j) + 1) : ZMod 8)
  let C : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 8) := Matrix.of fun i j => (tb (2 * (i + j + 1)) : ZMod 8)
  have hblk : Ht.submatrix e e = Matrix.fromBlocks A B Bᵀ C := by
    ext (i | i) (j | j) <;> simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.transpose_apply, Ht, A, B, C, Matrix.of_apply, e, Equiv.coe_fn_mk]
    · congr 2; ring
    · congr 2; ring
    · congr 2; ring
    · congr 2; ring
  rw [hblk]
  -- Check B mod 2 equals Catalan Hankel matrix mod 2, so B.det is a unit in ZMod 8!
  let φ82 := ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)
  have hB_mod2 : B.map φ82 = Matrix.of fun i j : Fin (m + 1) => (catalan (i + j) : ZMod 2) := by
    ext i j
    simp only [Matrix.map_apply, B, Matrix.of_apply, map_natCast]
    have h1 := tb_mod_two (2 * ((i : ℕ) + (j : ℕ)) + 1)
    have h2 : (catalan ((i : ℕ) + (j : ℕ))) % 2 =
        if ∃ r : ℕ, (i : ℕ) + (j : ℕ) + 1 = 2 ^ r then 1 else 0 := by
      have hcat_ne : catalan ((i : ℕ) + (j : ℕ)) ≠ 0 := catalan_ne_zero _
      split_ifs with hpow
      · have hv0 : padicValNat 2 (catalan ((i : ℕ) + (j : ℕ))) = 0 := by
          rw [v2_catalan, (s2_eq_one_iff _).mpr hpow]
        have hnd : ¬ 2 ∣ catalan ((i : ℕ) + (j : ℕ)) := fun hd => by
          have := (pow_two_dvd_iff_le_v2 hcat_ne).mp (by simpa using hd : 2 ^ 1 ∣ _); omega
        omega
      · have hs2 : 2 ≤ s2 ((i : ℕ) + (j : ℕ) + 1) := by
          have h1 := s2_pos_of_pos (by omega : 0 < (i : ℕ) + (j : ℕ) + 1)
          have hne : s2 ((i : ℕ) + (j : ℕ) + 1) ≠ 1 := fun h => hpow ((s2_eq_one_iff _).mp h)
          omega
        have hd : 2 ∣ catalan ((i : ℕ) + (j : ℕ)) := by
          have := (pow_two_dvd_iff_le_v2 hcat_ne).mpr (by rw [v2_catalan]; omega : 1 ≤ _); simpa using this
        omega
    have hiff : (∃ r : ℕ, 2 * ((i : ℕ) + (j : ℕ)) + 1 + 1 = 2 ^ r) ↔
        (∃ r : ℕ, (i : ℕ) + (j : ℕ) + 1 = 2 ^ r) := by
      constructor
      · rintro ⟨r, hr⟩
        cases r with
        | zero => omega
        | succ r => exact ⟨r, by rw [pow_succ] at hr; omega⟩
      · rintro ⟨r, hr⟩
        exact ⟨r + 1, by rw [pow_succ]; omega⟩
    have hmod_eq : tb (2 * ((i : ℕ) + (j : ℕ)) + 1) % 2 = catalan ((i : ℕ) + (j : ℕ)) % 2 := by
      rw [h1, h2]; simp [hiff]
    rw [ZMod.natCast_eq_natCast_iff']
    exact hmod_eq
  have hB_det_mod2 : φ82 B.det = 1 := by
    rw [RingHom.map_det]
    change (B.map φ82).det = 1
    rw [hB_mod2]
    have h1 := congrArg (Int.castRingHom (ZMod 2)) (catalan_hankel_det_one (m + 1))
    rw [RingHom.map_det] at h1
    have hmap : (Int.castRingHom (ZMod 2)).mapMatrix
        (Matrix.of fun i j : Fin (m + 1) => (catalan ((i : ℕ) + (j : ℕ)) : ℤ)) =
        Matrix.of fun i j : Fin (m + 1) => (catalan ((i : ℕ) + (j : ℕ)) : ZMod 2) := by
      ext i j; simp
    rw [hmap, map_one] at h1
    exact h1
  have hB_unit : IsUnit B.det := zmod8_isUnit_of_mod2_eq_one B.det hB_det_mod2
  have hBt_unit : IsUnit (Bᵀ).det := by rw [Matrix.det_transpose]; exact hB_unit
  rw [det_fromBlocks_of_isUnit_ur A B C Bᵀ hB_unit]
  -- Factor out Bᵀ: (Bᵀ - C * B⁻¹ * A).det = (Bᵀ).det * (1 - (Bᵀ)⁻¹ * C * B⁻¹ * A).det
  have hfact : Bᵀ - C * B⁻¹ * A = Bᵀ * (1 - (Bᵀ)⁻¹ * C * B⁻¹ * A) := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hBt_unit, Matrix.one_mul]
  rw [hfact, Matrix.det_mul, Matrix.det_transpose, ← mul_assoc, mul_assoc ((-1 : ZMod 8) ^ (m + 1)),
    zmod8_sq_of_odd B.det hB_unit, mul_one]
  -- Write A = E00 + 2 • A' and C = 2 • C'
  let A' : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 8) :=
    Matrix.of fun i j => if i = 0 ∧ j = 0 then 0 else ((tb (2 * ((i : ℕ) + (j : ℕ))) / 2 : ℕ) : ZMod 8)
  let C' : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 8) :=
    Matrix.of fun i j => ((tb (2 * ((i : ℕ) + (j : ℕ) + 1)) / 2 : ℕ) : ZMod 8)
  let E00 : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 8) :=
    Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0
  have hA_eq : A = E00 + (2 : ZMod 8) • A' := by
    ext i j
    simp only [A, E00, A', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    by_cases h0 : i = 0 ∧ j = 0
    · rcases h0 with ⟨rfl, rfl⟩; simp [tb_zero]
    · simp only [h0, ↓reduceIte, zero_add]
      have hpos : 1 ≤ (i : ℕ) + (j : ℕ) := by
        by_contra hlt; apply h0; constructor <;> (apply Fin.ext; simp only [Fin.val_zero]; omega)
      have hev := tb_two_mul_even hpos
      have hdiv : 2 * (tb (2 * ((i : ℕ) + (j : ℕ))) / 2) = tb (2 * ((i : ℕ) + (j : ℕ))) := by omega
      exact (congrArg (Nat.cast (R := ZMod 8)) hdiv.symm).trans (by push_cast; rfl)
  have hC_eq : C = (2 : ZMod 8) • C' := by
    ext i j
    simp only [C, C', Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    have hev := tb_two_mul_even (show 1 ≤ (i : ℕ) + (j : ℕ) + 1 by omega)
    have hdiv : 2 * (tb (2 * ((i : ℕ) + (j : ℕ) + 1)) / 2) = tb (2 * ((i : ℕ) + (j : ℕ) + 1)) := by omega
    exact (congrArg (Nat.cast (R := ZMod 8)) hdiv.symm).trans (by push_cast; rfl)
  let X' : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 8) := (Bᵀ)⁻¹ * C' * B⁻¹
  have hinner : 1 - (Bᵀ)⁻¹ * C * B⁻¹ * A =
      1 - (Matrix.of fun i j => if j = ⟨0, Nat.succ_pos m⟩ then 2 * X' i 0 else 0) -
        (4 : ZMod 8) • (X' * A') := by
    rw [hC_eq, hA_eq]
    ext i j
    simp only [X', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.sub_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    have hME : ((Bᵀ)⁻¹ * C' * B⁻¹ * E00) i j = if j = 0 then ((Bᵀ)⁻¹ * C' * B⁻¹) i 0 else 0 := by
      simp only [Matrix.mul_apply, E00, Matrix.of_apply]
      by_cases hj : j = 0
      · subst hj; simp
      · simp [hj]
    have h4 : (2 : ZMod 8) * (2 : ZMod 8) = 4 := by decide
    simp only [show (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) = 0 from rfl]
    rw [hME]
    split_ifs <;> ring
  rw [hinner, det_one_sub_col0_sub_four_zmod8 (Nat.succ_pos m) (fun i => X' i 0) (X' * A')]
  -- Step A: Show 4 * (X' * A').trace = 0 in ZMod 8 (i.e., φ82 (X' * A').trace = 0)
  have htr0 : (4 : ZMod 8) * (X' * A').trace = 0 := by
    suffices h2 : φ82 (X' * A').trace = 0 by
      have hfin : ∀ z : ZMod 8, ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2) z = 0 → (4 : ZMod 8) * z = 0 := by
        intro z hz; revert hz; fin_cases z <;> decide
      exact hfin _ h2
    have hmap_tr : φ82 (X' * A').trace = ((X' * A').map φ82).trace := by
      simp [Matrix.trace, Matrix.diag]
    rw [hmap_tr, Matrix.map_mul]
    have hB_sym : Bᵀ = B := by ext i j; simp [B, add_comm]
    have hC'_sym : C'ᵀ = C' := by ext i j; simp [C', add_comm]
    have hA'_sym : A'ᵀ = A' := by ext i j; simp [A', add_comm, and_comm]
    have hX'_sym : X'ᵀ = X' := by
      simp only [X', Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
        hB_sym, hC'_sym, Matrix.mul_assoc]
    have hC'_diag_mod2 : ∀ r : Fin (m + 1), φ82 (C' r r) = 0 := by
      intro r
      simp only [C', Matrix.of_apply, map_natCast]
      by_cases hr0 : (r : ℕ) = 0
      · rw [hr0]; simp [tb_two]; decide
      · have h8 := tb_four_mul_add_two_mod_eight (show 1 ≤ (r : ℕ) by omega)
        have hidx : 2 * ((r : ℕ) + (r : ℕ) + 1) = 4 * (r : ℕ) + 2 := by ring
        rw [hidx, ZMod.natCast_eq_zero_iff]
        omega
    have hX'_diag_mod2 : ∀ i : Fin (m + 1), (X'.map φ82) i i = 0 := by
      intro i
      have hBinv_sym : (B⁻¹)ᵀ = B⁻¹ := by rw [Matrix.transpose_nonsing_inv B, hB_sym]
      have hX'i : X' i i = ∑ r : Fin (m + 1), ∑ s : Fin (m + 1), (B⁻¹) r i * C' r s * (B⁻¹) s i := by
        simp only [X', hB_sym, Matrix.mul_apply, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
        have hBi : B⁻¹ i r = B⁻¹ r i := by simpa using congrFun (congrFun hBinv_sym r) i
        rw [hBi]
      rw [Matrix.map_apply, hX'i, map_sum]
      have h2 : ∑ r : Fin (m + 1), φ82 (∑ s : Fin (m + 1), B⁻¹ r i * C' r s * B⁻¹ s i) =
          ∑ r : Fin (m + 1), ∑ s : Fin (m + 1), φ82 (B⁻¹ r i) * (C'.map φ82) r s * φ82 (B⁻¹ s i) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [map_sum]; refine Finset.sum_congr rfl fun s _ => by simp
      have hC'm_sym : (C'.map φ82)ᵀ = C'.map φ82 := by
        ext a b; simp only [Matrix.transpose_apply, Matrix.map_apply]
        exact congrArg φ82 (congrFun (congrFun hC'_sym a) b)
      rw [h2, quad_form_symm_split (C'.map φ82) hC'm_sym (fun r => φ82 (B⁻¹ r i))]
      have h2z : (2 : ZMod 2) = 0 := by decide
      rw [h2z, zero_mul, add_zero]
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [Matrix.map_apply, hC'_diag_mod2 r, mul_zero]
    have hX'm_sym : (X'.map φ82)ᵀ = X'.map φ82 := by
      ext a b; simp only [Matrix.transpose_apply, Matrix.map_apply]
      exact congrArg φ82 (congrFun (congrFun hX'_sym a) b)
    have hA'm_sym : (A'.map φ82)ᵀ = A'.map φ82 := by
      ext a b; simp only [Matrix.transpose_apply, Matrix.map_apply]
      exact congrArg φ82 (congrFun (congrFun hA'_sym a) b)
    exact trace_alt_mul_symm_zmod2 (X'.map φ82) (A'.map φ82) hX'm_sym hX'_diag_mod2 hA'm_sym
  -- Step B: Show 2 * X' 0 0 = 4 * (m + 1) in ZMod 8!
  have hX00 : (2 : ZMod 8) * X' ⟨0, Nat.succ_pos m⟩ 0 = 4 * ((m + 1 : ℕ) : ZMod 8) := by
    have hB_sym : Bᵀ = B := by ext i j; simp [B, add_comm]
    have hBinv_sym : (B⁻¹)ᵀ = B⁻¹ := by rw [Matrix.transpose_nonsing_inv B, hB_sym]
    have hC_sym : Cᵀ = C := by ext i j; simp [C, add_comm]
    set v : Fin (m + 1) → ZMod 8 := fun r => B⁻¹ r 0
    have h2X : (2 : ZMod 8) * X' ⟨0, Nat.succ_pos m⟩ 0 =
        ∑ r : Fin (m + 1), ∑ s : Fin (m + 1), v r * C r s * v s := by
      have h1 : (2 : ZMod 8) • X' = (Bᵀ)⁻¹ * C * B⁻¹ := by
        simp only [X', hC_eq, Matrix.mul_smul, Matrix.smul_mul]
      have h2 := congrFun (congrFun h1 ⟨0, Nat.succ_pos m⟩) 0
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, hB_sym, Finset.sum_mul] at h2
      rw [h2, Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
      have hBi : B⁻¹ ⟨0, Nat.succ_pos m⟩ r = B⁻¹ r 0 := by
        have := congrFun (congrFun hBinv_sym r) 0
        simpa using this
      simp only [v, hBi]
    rw [h2X, quad_form_symm_split C hC_sym v]
    -- Apply catalan_mod2_parity_support to v2 = φ82 ∘ v!
    let v2 : Fin (m + 1) → ZMod 2 := fun r => φ82 (v r)
    have hBv : (Matrix.of fun i j : Fin (m + 1) => (catalan ((i : ℕ) + (j : ℕ)) : ZMod 2)).mulVec v2 =
        fun i => if i = 0 then 1 else 0 := by
      rw [← hB_mod2]
      have hmul : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB_unit
      ext i
      have h1 := congrArg φ82 (congrFun (congrFun hmul i) 0)
      simp only [Matrix.mul_apply, Matrix.one_apply, map_sum, map_mul, apply_ite φ82, map_one, map_zero] at h1
      simpa [Matrix.mulVec, dotProduct, v2, v] using h1
    have ⟨hv2_0, hv2_par⟩ := catalan_mod2_parity_support m v2 hBv
    -- Diagonal part: ∑ r, v r * v r * C r r = 4 * (m + 1)
    have hdiag : (∑ r : Fin (m + 1), v r * v r * C r r) = 4 * ((m + 1 : ℕ) : ZMod 8) := by
      rw [Finset.sum_eq_single (0 : Fin (m + 1))]
      · have hC00 : C 0 0 = 4 := by simp [C, tb_two]
        rw [hC00]
        have hstep : ∀ z : ZMod 8, φ82 z = (if m % 2 = 0 then 1 else 0) →
            z * z * 4 = 4 * ((m + 1 : ℕ) : ZMod 8) := by
          intro z hz
          by_cases hm : m % 2 = 0
          · simp only [hm, ↓reduceIte] at hz
            have h4m : (4 : ZMod 8) * ((m + 1 : ℕ) : ZMod 8) = 4 := by
              obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
              push_cast
              have h8 : (8 : ZMod 8) = 0 := by decide
              calc (4 : ZMod 8) * (2 * (k : ZMod 8) + 1) = (8 : ZMod 8) * (k : ZMod 8) + 4 := by ring
                _ = 4 := by rw [h8, zero_mul, zero_add]
            rw [h4m]
            have hfin : ∀ u : ZMod 8, ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2) u = 1 → u * u * 4 = 4 := by
              intro u hu; revert hu; fin_cases u <;> decide
            exact hfin z hz
          · simp only [hm, ↓reduceIte] at hz
            have h4m : (4 : ZMod 8) * ((m + 1 : ℕ) : ZMod 8) = 0 := by
              obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
              push_cast
              have h8 : (8 : ZMod 8) = 0 := by decide
              calc (4 : ZMod 8) * (2 * (k : ZMod 8) + 1 + 1) = (8 : ZMod 8) * ((k : ZMod 8) + 1) := by ring
                _ = 0 := by rw [h8, zero_mul]
            rw [h4m]
            have hfin : ∀ u : ZMod 8, ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2) u = 0 → u * u * 4 = 0 := by
              intro u hu; revert hu; fin_cases u <;> decide
            exact hfin z hz
        exact hstep (v 0) hv2_0
      · intro r _ hr0
        have hr1 : 1 ≤ (r : ℕ) := by
          by_contra hlt; apply hr0; apply Fin.ext; simp only [Fin.val_zero]; omega
        have hCrr : C r r = 0 := by
          simp only [C, Matrix.of_apply]
          have hidx : 2 * ((r : ℕ) + (r : ℕ) + 1) = 4 * (r : ℕ) + 2 := by ring
          rw [hidx, ZMod.natCast_eq_zero_iff]
          have := tb_four_mul_add_two_mod_eight hr1; omega
        rw [hCrr, mul_zero]
      · intro h; exact absurd (Finset.mem_univ 0) h
    -- Off-diagonal part: 2 * ∑_{r < s} v r * C r s * v s = 0 in ZMod 8!
    have hoff : (2 : ZMod 8) * ∑ p ∈ Finset.univ.filter (fun p : Fin (m + 1) × Fin (m + 1) => p.1 < p.2),
        v p.1 * C p.1 p.2 * v p.2 = 0 := by
      have heven_z8 : ∀ z : ZMod 8, ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2) z = 0 → ∃ t : ZMod 8, z = 2 * t := by
        intro z hz
        fin_cases z
        · exact ⟨0, rfl⟩
        · exfalso; revert hz; decide
        · exact ⟨1, rfl⟩
        · exfalso; revert hz; decide
        · exact ⟨2, rfl⟩
        · exfalso; revert hz; decide
        · exact ⟨3, rfl⟩
        · exfalso; revert hz; decide
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun ⟨r, s⟩ hrs => ?_
      rw [Finset.mem_filter] at hrs
      by_cases hvr : v2 r = 0
      · -- v r is even AND C r s is even, so 2 * v r * C r s * v s = 0 in ZMod 8!
        rcases heven_z8 (v r) hvr with ⟨t, ht⟩
        have hC_ev : C r s = 2 * C' r s := by
          have := congrFun (congrFun hC_eq r) s; simpa using this
        rw [ht, hC_ev]
        have h8 : (8 : ZMod 8) = 0 := by decide
        calc (2 : ZMod 8) * (2 * t * (2 * C' r s) * v s) = (8 : ZMod 8) * (t * C' r s * v s) := by ring
          _ = 0 := by rw [h8, zero_mul]
      · by_cases hvs : v2 s = 0
        · rcases heven_z8 (v s) hvs with ⟨t, ht⟩
          have hC_ev : C r s = 2 * C' r s := by
            have := congrFun (congrFun hC_eq r) s; simpa using this
          rw [ht, hC_ev]
          have h8 : (8 : ZMod 8) = 0 := by decide
          calc (2 : ZMod 8) * (v r * (2 * C' r s) * (2 * t)) = (8 : ZMod 8) * (v r * C' r s * t) := by ring
            _ = 0 := by rw [h8, zero_mul]
        · -- Both r and s have parity m % 2, and r < s => (r + s) is even >= 2 => C r s = 0 in ZMod 8!
          have hpr := hv2_par r hvr
          have hps := hv2_par s hvs
          have hsum_ev : ((r : ℕ) + (s : ℕ)) % 2 = 0 := by omega
          have hsum_pos : 2 ≤ (r : ℕ) + (s : ℕ) := by
            have : (r : ℕ) < (s : ℕ) := hrs.2; omega
          obtain ⟨q, hq⟩ : ∃ q, (r : ℕ) + (s : ℕ) = 2 * q := ⟨((r : ℕ) + (s : ℕ)) / 2, by omega⟩
          have hq1 : 1 ≤ q := by omega
          have hCrs : C r s = 0 := by
            simp only [C, Matrix.of_apply]
            have hidx : 2 * ((r : ℕ) + (s : ℕ) + 1) = 4 * q + 2 := by omega
            rw [hidx, ZMod.natCast_eq_zero_iff]
            have := tb_four_mul_add_two_mod_eight hq1; omega
          rw [hCrs, mul_zero, zero_mul, mul_zero]
    rw [hdiag, hoff, add_zero]
  rw [htr0, sub_zero, hX00]
  -- Check (-1)^(m+1) * (1 - 4*(m+1)) = 3^(m+1) in ZMod 8!
  clear * -
  induction m with
  | zero => decide
  | succ m ih =>
    have hL : (-1 : ZMod 8) ^ (m + 1 + 1) = (-1 : ZMod 8) ^ (m + 1) * (-1) := pow_succ _ _
    have hR : (3 : ZMod 8) ^ (m + 1 + 1) = (3 : ZMod 8) ^ (m + 1) * 3 := pow_succ _ _
    rw [hL, hR, ← ih]
    have hm2 : ∀ t : ZMod 8, (-1 : ZMod 8) * (1 - 4 * (t + 1)) = 3 * (1 - 4 * t) := by
      intro t; fin_cases t <;> rfl
    have hstep := hm2 ((m + 1 : ℕ) : ZMod 8)
    rw [Nat.cast_succ]
    calc (-1 : ZMod 8) ^ (m + 1) * (-1) * (1 - 4 * (((m + 1 : ℕ) : ZMod 8) + 1))
        = (-1 : ZMod 8) ^ (m + 1) * ((-1) * (1 - 4 * (((m + 1 : ℕ) : ZMod 8) + 1))) := by ring
      _ = (-1 : ZMod 8) ^ (m + 1) * (3 * (1 - 4 * ((m + 1 : ℕ) : ZMod 8))) := by rw [hstep]
      _ = (-1 : ZMod 8) ^ (m + 1) * (1 - 4 * ((m + 1 : ℕ) : ZMod 8)) * 3 := by ring

private lemma even_hankel_mod4 (m : ℕ) :
    (a_seq (2 * m) : ZMod 4) = 1 := by
  rw [hankel_b_eq_tb_det]
  cases m with
  | zero =>
    simp [Matrix.det_fin_one, tb_zero]
  | succ k =>
    set m := k + 1
    set Ht : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) (ZMod 4) :=
      Matrix.of fun i j => (tb ((i : ℕ) + (j : ℕ)) : ZMod 4)
    have hcast_det : ((Matrix.of fun i j : Fin (2 * m + 1) => (tb ((i : ℕ) + (j : ℕ)) : ℤ)).det : ZMod 4) =
        Ht.det := by
      have h1 := (RingHom.map_det (Int.castRingHom (ZMod 4))
        (Matrix.of fun i j : Fin (2 * m + 1) => (tb ((i : ℕ) + (j : ℕ)) : ℤ)))
      have hmap : (Int.castRingHom (ZMod 4)).mapMatrix
          (Matrix.of fun i j : Fin (2 * m + 1) => (tb ((i : ℕ) + (j : ℕ)) : ℤ)) = Ht := by
        ext i j; simp [Ht]
      rw [hmap] at h1
      exact h1
    rw [hcast_det]
    let e : Unit ⊕ (Fin m ⊕ Fin m) ≃ Fin (2 * m + 1) :=
      { toFun := fun x => match x with
          | Sum.inl () => ⟨0, by omega⟩
          | Sum.inr (Sum.inl a) => ⟨2 * (a : ℕ) + 2, by omega⟩
          | Sum.inr (Sum.inr b) => ⟨2 * (b : ℕ) + 1, by omega⟩
        invFun := fun i =>
          if h0 : (i : ℕ) = 0 then Sum.inl ()
          else if he : (i : ℕ) % 2 = 0 then Sum.inr (Sum.inl ⟨(i : ℕ) / 2 - 1, by omega⟩)
          else Sum.inr (Sum.inr ⟨(i : ℕ) / 2, by omega⟩)
        left_inv := fun x => by
          rcases x with ⟨⟩ | (a | b)
          · simp
          · simp only [show 2 * (a : ℕ) + 2 ≠ 0 by omega, ↓reduceDIte, show (2 * (a : ℕ) + 2) % 2 = 0 by omega]
            congr 2; ext; simp
          · simp only [show 2 * (b : ℕ) + 1 ≠ 0 by omega, ↓reduceDIte, show (2 * (b : ℕ) + 1) % 2 ≠ 0 by omega]
            congr 2; ext; simp; omega
        right_inv := fun i => by
          by_cases h0 : (i : ℕ) = 0
          · ext; simp [h0]
          · by_cases he : (i : ℕ) % 2 = 0
            · ext; simp [h0, he]; omega
            · ext; simp [h0, he]; omega }
    rw [(Matrix.det_submatrix_equiv_self e Ht).symm]
    -- Define blocks in ZMod 4
    let a_vec : Fin m → ZMod 4 := fun a => ((tb (2 * ((a : ℕ) + 1)) / 2 : ℕ) : ZMod 4)
    let b_vec : Fin m → ZMod 4 := fun b => (tb (2 * (b : ℕ) + 1) : ZMod 4)
    let A_tilde : Matrix (Fin m) (Fin m) (ZMod 4) :=
      Matrix.of fun a c => ((tb (2 * ((a : ℕ) + (c : ℕ) + 2)) / 2 : ℕ) : ZMod 4)
    let B_tilde : Matrix (Fin m) (Fin m) (ZMod 4) :=
      Matrix.of fun a b => (tb (2 * ((a : ℕ) + (b : ℕ) + 1) + 1) : ZMod 4)
    let C' : Matrix (Fin m) (Fin m) (ZMod 4) :=
      Matrix.of fun b d => ((tb (2 * ((b : ℕ) + (d : ℕ) + 1)) / 2 : ℕ) : ZMod 4)
    let r0 : Matrix Unit (Fin m ⊕ Fin m) (ZMod 4) :=
      Matrix.of fun _ y => match y with | Sum.inl a => 2 * a_vec a | Sum.inr b => b_vec b
    let c0 : Matrix (Fin m ⊕ Fin m) Unit (ZMod 4) := r0ᵀ
    let Dblk : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 4) :=
      Matrix.fromBlocks ((2 : ZMod 4) • A_tilde) B_tilde B_tildeᵀ ((2 : ZMod 4) • C')
    have hsub : Ht.submatrix e e = Matrix.fromBlocks (1 : Matrix Unit Unit (ZMod 4)) r0 c0 Dblk := by
      ext (⟨⟩ | (a | b)) (⟨⟩ | (c | d))
      · simp [Ht, e, tb_zero]
      · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, r0, Matrix.of_apply, Ht, e, Equiv.coe_fn_mk, a_vec]
        have hev := tb_two_mul_even (show 1 ≤ (c : ℕ) + 1 by omega)
        have hdiv : 2 * (tb (2 * ((c : ℕ) + 1)) / 2) = tb (2 * ((c : ℕ) + 1)) := by omega
        rw [show 0 + (2 * (c : ℕ) + 2) = 2 * ((c : ℕ) + 1) by ring]
        exact (congrArg (Nat.cast (R := ZMod 4)) hdiv.symm).trans (by push_cast; rfl)
      · simp [Ht, e, r0, b_vec]
      · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, c0, r0, Matrix.transpose_apply,
          Matrix.of_apply, Ht, e, Equiv.coe_fn_mk, a_vec]
        have hev := tb_two_mul_even (show 1 ≤ (a : ℕ) + 1 by omega)
        have hdiv : 2 * (tb (2 * ((a : ℕ) + 1)) / 2) = tb (2 * ((a : ℕ) + 1)) := by omega
        rw [show 2 * (a : ℕ) + 2 + 0 = 2 * ((a : ℕ) + 1) by ring]
        exact (congrArg (Nat.cast (R := ZMod 4)) hdiv.symm).trans (by push_cast; rfl)
      · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, Dblk, Matrix.fromBlocks_apply₁₁,
          Matrix.smul_apply, smul_eq_mul, A_tilde, Matrix.of_apply, Ht, e, Equiv.coe_fn_mk]
        have hev := tb_two_mul_even (show 1 ≤ (a : ℕ) + (c : ℕ) + 2 by omega)
        have hdiv : 2 * (tb (2 * ((a : ℕ) + (c : ℕ) + 2)) / 2) = tb (2 * ((a : ℕ) + (c : ℕ) + 2)) := by omega
        rw [show 2 * (a : ℕ) + 2 + (2 * (c : ℕ) + 2) = 2 * ((a : ℕ) + (c : ℕ) + 2) by ring]
        exact (congrArg (Nat.cast (R := ZMod 4)) hdiv.symm).trans (by push_cast; rfl)
      · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, Dblk, Matrix.fromBlocks_apply₁₂,
          B_tilde, Matrix.of_apply, Ht, e, Equiv.coe_fn_mk]
        congr 2; ring
      · simp [Ht, e, c0, r0, b_vec]
      · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, Dblk, Matrix.fromBlocks_apply₂₁,
          Matrix.transpose_apply, B_tilde, Matrix.of_apply, Ht, e, Equiv.coe_fn_mk]
        congr 2; ring
      · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, Dblk, Matrix.fromBlocks_apply₂₂,
          Matrix.smul_apply, smul_eq_mul, C', Matrix.of_apply, Ht, e, Equiv.coe_fn_mk]
        have hev := tb_two_mul_even (show 1 ≤ (b : ℕ) + (d : ℕ) + 1 by omega)
        have hdiv : 2 * (tb (2 * ((b : ℕ) + (d : ℕ) + 1)) / 2) = tb (2 * ((b : ℕ) + (d : ℕ) + 1)) := by omega
        rw [show 2 * (b : ℕ) + 1 + (2 * (d : ℕ) + 1) = 2 * ((b : ℕ) + (d : ℕ) + 1) by ring]
        exact (congrArg (Nat.cast (R := ZMod 4)) hdiv.symm).trans (by push_cast; rfl)
    have : Invertible (1 : Matrix Unit Unit (ZMod 4)) := invertibleOne
    rw [hsub, Matrix.det_fromBlocks₁₁]
    simp only [Matrix.det_one, invOf_one, Matrix.mul_one, one_mul]
    let W : Matrix (Fin m) (Fin m) (ZMod 4) := B_tilde - Matrix.of fun a b => 2 * a_vec a * b_vec b
    let D : Matrix (Fin m) (Fin m) (ZMod 4) := (2 : ZMod 4) • C' - Matrix.of fun b d => b_vec b * b_vec d
    have hschur : Dblk - c0 * r0 = Matrix.fromBlocks ((2 : ZMod 4) • A_tilde) W Wᵀ D := by
      have h4 : (2 : ZMod 4) * (2 : ZMod 4) = 0 := by decide
      ext (a | b) (c | d)
      · simp only [Matrix.sub_apply, Dblk, Matrix.fromBlocks_apply₁₁, Matrix.mul_apply, c0, r0,
          Matrix.transpose_apply, Matrix.of_apply, Fintype.sum_unique, Matrix.smul_apply, smul_eq_mul]
        calc 2 * A_tilde a c - 2 * a_vec a * (2 * a_vec c)
            = 2 * A_tilde a c - ((2 : ZMod 4) * 2) * (a_vec a * a_vec c) := by ring
          _ = 2 * A_tilde a c := by rw [h4, zero_mul, sub_zero]
      · simp [Dblk, W, c0, r0, Matrix.mul_apply]
      · simp [Dblk, W, c0, r0, Matrix.mul_apply]; ring
      · simp [Dblk, D, c0, r0, Matrix.mul_apply]
    rw [hschur]
    -- Show W mod 2 = shifted Catalan Hankel matrix mod 2, so W.det is a unit in ZMod 4!
    let φ42 := ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)
    have htb_cat_mod2 : ∀ t : ℕ, (tb (2 * t + 1) : ZMod 2) = (catalan t : ZMod 2) := by
      intro t
      have h1 := tb_mod_two (2 * t + 1)
      have hcat_ne : catalan t ≠ 0 := catalan_ne_zero t
      have h2 : catalan t % 2 = if ∃ r : ℕ, t + 1 = 2 ^ r then 1 else 0 := by
        split_ifs with hpow
        · have hv0 : padicValNat 2 (catalan t) = 0 := by rw [v2_catalan, (s2_eq_one_iff _).mpr hpow]
          have hnd : ¬ 2 ∣ catalan t := fun hd => by
            have := (pow_two_dvd_iff_le_v2 hcat_ne).mp (by simpa using hd : 2 ^ 1 ∣ _); omega
          omega
        · have hs2 : 2 ≤ s2 (t + 1) := by
            have h1 := s2_pos_of_pos (by omega : 0 < t + 1)
            have hne : s2 (t + 1) ≠ 1 := fun h => hpow ((s2_eq_one_iff _).mp h)
            omega
          have hd : 2 ∣ catalan t := by
            have := (pow_two_dvd_iff_le_v2 hcat_ne).mpr (by rw [v2_catalan]; omega : 1 ≤ _); simpa using this
          omega
      have hiff : (∃ r : ℕ, 2 * t + 1 + 1 = 2 ^ r) ↔ (∃ r : ℕ, t + 1 = 2 ^ r) := by
        constructor
        · rintro ⟨r, hr⟩; cases r with | zero => omega | succ r => exact ⟨r, by rw [pow_succ] at hr; omega⟩
        · rintro ⟨r, hr⟩; exact ⟨r + 1, by rw [pow_succ]; omega⟩
      rw [ZMod.natCast_eq_natCast_iff', h1, h2]; simp [hiff]
    let B1_int : Matrix (Fin m) (Fin m) ℤ := Matrix.of fun i j => (catalan ((i : ℕ) + (j : ℕ) + 1) : ℤ)
    let b0_int : Fin m → ℤ := fun i => (catalan (i : ℕ) : ℤ)
    have ⟨hB1_det, hB1_quad⟩ := catalan_shift_hankel_facts m
    have hW_mod2 : W.map φ42 = B1_int.map (Int.castRingHom (ZMod 2)) := by
      ext a b
      simp only [Matrix.map_apply, W, B_tilde, B1_int, Matrix.sub_apply, Matrix.of_apply,
        map_sub, map_mul, map_natCast, map_intCast, Int.cast_natCast]
      have h2z : φ42 2 = 0 := by decide
      rw [show φ42 2 = 0 from h2z, zero_mul, zero_mul, sub_zero]
      exact htb_cat_mod2 ((a : ℕ) + (b : ℕ) + 1)
    have hW_det_mod2 : φ42 W.det = 1 := by
      rw [RingHom.map_det]
      change (W.map φ42).det = 1
      rw [hW_mod2]
      change ((Int.castRingHom (ZMod 2)).mapMatrix B1_int).det = 1
      rw [← RingHom.map_det, hB1_det, map_one]
    have hW_unit : IsUnit W.det := zmod4_isUnit_of_mod2_eq_one W.det hW_det_mod2
    have hWt_unit : IsUnit (Wᵀ).det := by rw [Matrix.det_transpose]; exact hW_unit
    rw [det_fromBlocks_of_isUnit_ur ((2 : ZMod 4) • A_tilde) W D Wᵀ hW_unit]
    have hfact : Wᵀ - D * W⁻¹ * ((2 : ZMod 4) • A_tilde) =
        Wᵀ * (1 + (2 : ZMod 4) • (-((Wᵀ)⁻¹ * D * W⁻¹ * A_tilde))) := by
      calc Wᵀ - D * W⁻¹ * ((2 : ZMod 4) • A_tilde)
          = Wᵀ - (2 : ZMod 4) • (D * W⁻¹ * A_tilde) := by rw [Matrix.mul_smul]
        _ = Wᵀ - (2 : ZMod 4) • ((Wᵀ * (Wᵀ)⁻¹) * D * W⁻¹ * A_tilde) := by
            rw [Matrix.mul_nonsing_inv _ hWt_unit, Matrix.one_mul]
        _ = Wᵀ + (2 : ZMod 4) • (-(Wᵀ * ((Wᵀ)⁻¹ * D * W⁻¹ * A_tilde))) := by
            rw [sub_eq_add_neg, ← smul_neg]
            simp only [Matrix.mul_assoc]
        _ = Wᵀ * (1 + (2 : ZMod 4) • (-((Wᵀ)⁻¹ * D * W⁻¹ * A_tilde))) := by
            rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_neg]
    rw [hfact, Matrix.det_mul, Matrix.det_transpose, ← mul_assoc, mul_assoc ((-1 : ZMod 4) ^ m),
      zmod4_sq_of_odd W.det hW_unit, mul_one, det_one_add_two_mul_zmod4]
    -- Show 2 * (-((Wᵀ)⁻¹ * D * W⁻¹ * A_tilde)).trace = 2 * (m : ZMod 4) in ZMod 4!
    have htr_mod2 : φ42 (-((Wᵀ)⁻¹ * D * W⁻¹ * A_tilde)).trace = (m : ZMod 2) := by
      have hmap_tr : ∀ M : Matrix (Fin m) (Fin m) (ZMod 4), φ42 M.trace = (M.map φ42).trace :=
        fun M => by simp [Matrix.trace, Matrix.diag]
      rw [Matrix.trace_neg, map_neg, hmap_tr]
      have hneg : ∀ z : ZMod 2, -z = z := by intro z; fin_cases z <;> rfl
      rw [hneg]
      simp only [Matrix.map_mul]
      have hD_mod2 : D.map φ42 = Matrix.of fun i j => (b0_int i : ZMod 2) * (b0_int j : ZMod 2) := by
        ext i j
        simp only [Matrix.map_apply, D, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
          Matrix.of_apply, map_sub, map_mul, b_vec, b0_int, map_natCast, Int.cast_natCast]
        have h2z : φ42 2 = 0 := by decide
        rw [h2z, zero_mul, zero_sub, hneg, htb_cat_mod2, htb_cat_mod2]
      have hW_inv_mod2 : W⁻¹.map φ42 = B1_int⁻¹.map (Int.castRingHom (ZMod 2)) := by
        have hB1_unit : IsUnit B1_int.det := by rw [hB1_det]; exact isUnit_one
        have h1 : B1_int.map (Int.castRingHom (ZMod 2)) * W⁻¹.map φ42 = 1 := by
          rw [← hW_mod2, ← Matrix.map_mul, Matrix.mul_nonsing_inv W hW_unit,
            Matrix.map_one _ (map_zero _) (map_one _)]
        have h2 : B1_int⁻¹.map (Int.castRingHom (ZMod 2)) * B1_int.map (Int.castRingHom (ZMod 2)) = 1 := by
          rw [← Matrix.map_mul, Matrix.nonsing_inv_mul B1_int hB1_unit,
            Matrix.map_one _ (map_zero _) (map_one _)]
        calc W⁻¹.map φ42 = 1 * W⁻¹.map φ42 := (Matrix.one_mul _).symm
          _ = (B1_int⁻¹.map (Int.castRingHom (ZMod 2)) * B1_int.map (Int.castRingHom (ZMod 2))) * W⁻¹.map φ42 := by rw [h2]
          _ = B1_int⁻¹.map (Int.castRingHom (ZMod 2)) * (B1_int.map (Int.castRingHom (ZMod 2)) * W⁻¹.map φ42) := by rw [Matrix.mul_assoc]
          _ = B1_int⁻¹.map (Int.castRingHom (ZMod 2)) := by rw [h1, Matrix.mul_one]
      have hWt_inv_mod2 : (Wᵀ)⁻¹.map φ42 = (B1_int⁻¹.map (Int.castRingHom (ZMod 2)))ᵀ := by
        ext a b
        have h1 := congrFun (congrFun (Matrix.transpose_nonsing_inv W) a) b
        simp only [Matrix.map_apply, Matrix.transpose_apply] at h1 ⊢
        rw [← h1]
        exact congrFun (congrFun hW_inv_mod2 b) a
      rw [hWt_inv_mod2, hD_mod2, hW_inv_mod2]
      -- Let w_i = ∑ j, B1⁻¹_{i,j} * b0_j in ZMod 2
      let w : Fin m → ZMod 2 := fun i => ∑ j : Fin m, (B1_int⁻¹ i j : ZMod 2) * (b0_int j : ZMod 2)
      have hB1_sym : B1_intᵀ = B1_int := by ext i j; simp [B1_int, add_comm]
      have hB1inv_sym : (B1_int⁻¹)ᵀ = B1_int⁻¹ := by rw [Matrix.transpose_nonsing_inv B1_int, hB1_sym]
      have htr_quad : ((B1_int⁻¹.map (Int.castRingHom (ZMod 2)))ᵀ *
            (Matrix.of fun i j => (b0_int i : ZMod 2) * (b0_int j : ZMod 2)) *
            B1_int⁻¹.map (Int.castRingHom (ZMod 2)) * A_tilde.map φ42).trace =
          ∑ r : Fin m, ∑ s : Fin m, w r * (A_tilde.map φ42) r s * w s := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
          Matrix.map_apply, Matrix.of_apply, Int.coe_castRingHom]
        have hstep1 : ∀ i j : Fin m,
            ∑ x : Fin m, (∑ y : Fin m, (B1_int⁻¹ y i : ZMod 2) * ((b0_int y : ZMod 2) * (b0_int x : ZMod 2))) *
              (B1_int⁻¹ x j : ZMod 2) = w i * w j := by
          intro i j
          simp only [w, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          have h1 : B1_int⁻¹ y i = B1_int⁻¹ i y := congrFun (congrFun hB1inv_sym i) y
          have h2 : B1_int⁻¹ x j = B1_int⁻¹ j x := congrFun (congrFun hB1inv_sym j) x
          rw [h1, h2]; ring
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
        rw [hstep1 r s]
        have hAs : A_tilde s r = A_tilde r s := by simp [A_tilde, add_comm]
        rw [hAs]; ring
      rw [htr_quad, quad_form_symm_split (A_tilde.map φ42) (by ext i j; simp [A_tilde, add_comm]) w]
      have h2z : (2 : ZMod 2) = 0 := by decide
      rw [h2z, zero_mul, add_zero]
      -- For each r : Fin m, w r * w r = w r in ZMod 2, and (A_tilde.map φ42) r r = (b0_int r : ZMod 2)!
      have hAt_diag : ∀ r : Fin m, (A_tilde.map φ42) r r = (b0_int r : ZMod 2) := by
        intro r
        simp only [Matrix.map_apply, A_tilde, Matrix.of_apply, map_natCast, b0_int, Int.cast_natCast]
        have hidx : 2 * ((r : ℕ) + (r : ℕ) + 2) = 4 * ((r : ℕ) + 1) := by ring
        rw [hidx]
        have h4 := tb_four_mul_mod_four (show 1 ≤ (r : ℕ) + 1 by omega)
        have htb_div : (tb (4 * ((r : ℕ) + 1)) / 2) % 2 = if ∃ t : ℕ, (r : ℕ) + 1 = 2 ^ t then 1 else 0 := by
          split_ifs at h4 ⊢ <;> omega
        have hcat_ne : catalan (r : ℕ) ≠ 0 := catalan_ne_zero (r : ℕ)
        have hcat_mod : catalan (r : ℕ) % 2 = if ∃ t : ℕ, (r : ℕ) + 1 = 2 ^ t then 1 else 0 := by
          split_ifs with hpow
          · have hv0 : padicValNat 2 (catalan (r : ℕ)) = 0 := by rw [v2_catalan, (s2_eq_one_iff _).mpr hpow]
            have hnd : ¬ 2 ∣ catalan (r : ℕ) := fun hd => by
              have := (pow_two_dvd_iff_le_v2 hcat_ne).mp (by simpa using hd : 2 ^ 1 ∣ _); omega
            omega
          · have hs2 : 2 ≤ s2 ((r : ℕ) + 1) := by
              have h1 := s2_pos_of_pos (by omega : 0 < (r : ℕ) + 1)
              have hne : s2 ((r : ℕ) + 1) ≠ 1 := fun h => hpow ((s2_eq_one_iff _).mp h)
              omega
            have hd : 2 ∣ catalan (r : ℕ) := by
              have := (pow_two_dvd_iff_le_v2 hcat_ne).mpr (by rw [v2_catalan]; omega : 1 ≤ _); simpa using this
            omega
        rw [ZMod.natCast_eq_natCast_iff', htb_div, hcat_mod]
      have hsq2 : ∀ z : ZMod 2, z * z = z := by intro z; fin_cases z <;> rfl
      have hsum_eq : (∑ r : Fin m, w r * w r * (A_tilde.map φ42) r r) =
          ((∑ i : Fin m, ∑ j : Fin m, b0_int i * B1_int⁻¹ i j * b0_int j : ℤ) : ZMod 2) := by
        simp only [Int.cast_sum, Int.cast_mul]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hsq2, hAt_diag r]
        simp only [w, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [hsum_eq, hB1_quad, Int.cast_natCast]
    have h2tr : (2 : ZMod 4) * (-((Wᵀ)⁻¹ * D * W⁻¹ * A_tilde)).trace = 2 * (m : ZMod 4) := by
      have hlift : ∀ z : ZMod 4, φ42 z = (m : ZMod 2) → (2 : ZMod 4) * z = 2 * (m : ZMod 4) := by
        intro z hz
        have hm2 : ((m : ZMod 2)) = φ42 (m : ZMod 4) := by simp [φ42]
        rw [hm2] at hz
        have hsub : φ42 (z - (m : ZMod 4)) = 0 := by rw [map_sub, hz, sub_self]
        have h20 : ∀ u : ZMod 4, φ42 u = 0 → (2 : ZMod 4) * u = 0 := by intro u; fin_cases u <;> decide
        have := h20 (z - (m : ZMod 4)) hsub
        linear_combination this
      exact hlift _ htr_mod2
    rw [h2tr]
    -- (-1)^m * (1 + 2 * m) = 1 in ZMod 4!
    clear * -
    induction m with
    | zero => decide
    | succ t ih =>
      rw [pow_succ]; push_cast
      have hstep : ∀ z : ZMod 4, (-1 : ZMod 4) * (1 + 2 * (z + 1)) = 1 + 2 * z := by
        intro z; fin_cases z <;> decide
      have := hstep (t : ZMod 4)
      calc (-1 : ZMod 4) ^ t * -1 * (1 + 2 * ((t : ZMod 4) + 1))
          = (-1 : ZMod 4) ^ t * (-1 * (1 + 2 * ((t : ZMod 4) + 1))) := by ring
        _ = (-1 : ZMod 4) ^ t * (1 + 2 * (t : ZMod 4)) := by rw [this]
        _ = 1 := ih

theorem part1_main (n : ℕ) : Odd (a_seq n) ∧ a_seq n % 8 ≠ 7 := by
  by_cases hev : n % 2 = 0
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    have h4 := even_hankel_mod4 m
    have hdvd : (4 : ℤ) ∣ a_seq (2 * m) - 1 := by
      have hz : ((a_seq (2 * m) - 1 : ℤ) : ZMod 4) = 0 := by push_cast; rw [h4, sub_self]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    rcases hdvd with ⟨q, hq⟩
    refine ⟨⟨2 * q, by omega⟩, by omega⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    have h8 := odd_hankel_mod8 m
    have hpow : (3 : ZMod 8) ^ (m + 1) = 1 ∨ (3 : ZMod 8) ^ (m + 1) = 3 := by
      clear hev h8
      induction m with
      | zero => right; decide
      | succ k ih =>
        rw [show k + 1 + 1 = (k + 1) + 1 by ring, pow_succ]
        rcases ih with h | h
        · right; rw [h]; decide
        · left; rw [h]; decide
    rcases hpow with h1 | h3
    · rw [h1] at h8
      have hdvd : (8 : ℤ) ∣ a_seq (2 * m + 1) - 1 := by
        have hz : ((a_seq (2 * m + 1) - 1 : ℤ) : ZMod 8) = 0 := by push_cast; rw [h8, sub_self]
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
      rcases hdvd with ⟨q, hq⟩
      refine ⟨⟨4 * q, by omega⟩, by omega⟩
    · rw [h3] at h8
      have hdvd : (8 : ℤ) ∣ a_seq (2 * m + 1) - 3 := by
        have hz : ((a_seq (2 * m + 1) - 3 : ℤ) : ZMod 8) = 0 := by push_cast; rw [h8, sub_self]
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
      rcases hdvd with ⟨q, hq⟩
      refine ⟨⟨4 * q + 1, by omega⟩, by omega⟩

end OMA_A228456_Part1

namespace OMA_A228456_Part2

open Filter Topology Matrix

private lemma continuous_poly_eval (p : Polynomial ℝ) : Continuous (fun x : ℝ => p.eval x) :=
  p.continuous

private abbrev b_seq := OMA.S_oeis_a228456.b

private abbrev a_seq := OMA.S_oeis_a228456.a

/-! ### Section 1: 2D Iterated Integral Representation of b(m) -/

private noncomputable def kern (φ θ : ℝ) : ℝ :=
  1 + 4 * Real.cos φ ^ 2 + 4 * Real.cos φ * Real.cos θ

private lemma kern_nonneg (φ θ : ℝ) : 0 ≤ kern φ θ := by
  have h1 : kern φ θ =
      (1 + 2 * Real.cos φ * Real.cos θ) ^ 2 + (2 * Real.cos φ * Real.sin θ) ^ 2 := by
    unfold kern
    have hcs := Real.sin_sq_add_cos_sq θ
    nlinarith
  rw [h1]
  positivity

private lemma kern_le_nine (φ θ : ℝ) : kern φ θ ≤ 9 := by
  unfold kern
  have h1 : |Real.cos φ| ≤ 1 := Real.abs_cos_le_one φ
  have h2 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  have h1' : -1 ≤ Real.cos φ ∧ Real.cos φ ≤ 1 := abs_le.mp h1
  have h2' : -1 ≤ Real.cos θ ∧ Real.cos θ ≤ 1 := abs_le.mp h2
  nlinarith

private lemma continuous_kern : Continuous (fun p : ℝ × ℝ => kern p.1 p.2) := by
  unfold kern
  fun_prop

private noncomputable def exp2D (g : ℝ → ℝ) : ℝ :=
  (1 / Real.pi ^ 2) *
    ∫ φ in (0 : ℝ)..Real.pi,
      (∫ θ in (-Real.pi)..Real.pi, g (kern φ θ)) * Real.sin φ ^ 2

private lemma integral_exp_I_int_mul (n : ℤ) :
    ∫ θ in (-Real.pi)..Real.pi, Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ)) =
      if n = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hn : n = 0
  · subst hn
    simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const, ↓reduceIte, Complex.real_smul]
    push_cast
    ring
  · simp only [hn, ↓reduceIte]
    have hne : Complex.I * (n : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hn)
    set c : ℂ := Complex.I * (n : ℂ)
    have hderiv : ∀ θ ∈ Set.uIcc (-Real.pi) Real.pi,
        HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ)) / c)
          (Complex.exp (c * (θ : ℂ))) θ := by
      intro θ _
      have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c θ := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).const_mul c
      have h2 : HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ)))
          (Complex.exp (c * (θ : ℂ)) * c) θ := h1.cexp
      have h3 := h2.div_const c
      simpa [mul_div_cancel_right₀ _ hne] using h3
    have hint : IntervalIntegrable (fun t : ℝ => Complex.exp (c * (t : ℂ)))
        MeasureTheory.volume (-Real.pi) Real.pi := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have hexp : Complex.exp (c * (Real.pi : ℂ)) = Complex.exp (c * ((-Real.pi : ℝ) : ℂ)) := by
      have hdiff : c * (Real.pi : ℂ) =
          c * ((-Real.pi : ℝ) : ℂ) + (n : ℂ) * (2 * Real.pi * Complex.I) := by
        simp only [c, Complex.ofReal_neg]
        ring
      rw [hdiff, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hexp, sub_self]

private lemma inner_integral_pow (r : ℝ) (m : ℕ) :
    ∫ θ in (-Real.pi)..Real.pi, (1 + r ^ 2 + 2 * r * Real.cos θ) ^ m =
      2 * Real.pi * ∑ k ∈ Finset.range (m + 1), ((m.choose k : ℝ) ^ 2 * r ^ (2 * k)) := by
  have hC :
      ∫ θ in (-Real.pi)..Real.pi,
        (((1 + r ^ 2 + 2 * r * Real.cos θ) ^ m : ℝ) : ℂ) =
      ((2 * Real.pi * ∑ k ∈ Finset.range (m + 1),
        ((m.choose k : ℝ) ^ 2 * r ^ (2 * k)) : ℝ) : ℂ) := by
    have hfun : ∀ θ : ℝ,
        (((1 + r ^ 2 + 2 * r * Real.cos θ) ^ m : ℝ) : ℂ) =
        ∑ j ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (m + 1),
          ((m.choose j : ℂ) * (m.choose k : ℂ) * (r : ℂ) ^ (j + k)) *
            Complex.exp (Complex.I * (((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (θ : ℂ)) := by
      intro θ
      have hbase : ((1 + r ^ 2 + 2 * r * Real.cos θ : ℝ) : ℂ) =
          (1 + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (1 + (r : ℂ) * Complex.exp (-(Complex.I * (θ : ℂ)))) := by
        have hsum : Complex.exp (Complex.I * (θ : ℂ)) +
            Complex.exp (-(Complex.I * (θ : ℂ))) = 2 * (Real.cos θ : ℂ) := by
          have h1 : Complex.exp (Complex.I * (θ : ℂ)) =
              (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
            rw [mul_comm, Complex.exp_mul_I]
            simp [Complex.ofReal_cos, Complex.ofReal_sin]
          have h2 : Complex.exp (-(Complex.I * (θ : ℂ))) =
              (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
            have : -(Complex.I * (θ : ℂ)) = ((-θ : ℝ) : ℂ) * Complex.I := by
              push_cast; ring
            rw [this, Complex.exp_mul_I]
            simp [Complex.ofReal_cos, Complex.ofReal_sin, sub_eq_add_neg]
          rw [h1, h2]
          ring
        have hprod : Complex.exp (Complex.I * (θ : ℂ)) *
            Complex.exp (-(Complex.I * (θ : ℂ))) = 1 := by
          rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
        rw [Complex.ofReal_cos] at hsum
        push_cast
        linear_combination -(r : ℂ) * hsum - (r : ℂ) ^ 2 * hprod
      rw [Complex.ofReal_pow, hbase, mul_pow]
      rw [add_comm (1 : ℂ) _, add_pow, add_comm (1 : ℂ) _, add_pow]
      simp only [one_pow, mul_one]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hexp :
          Complex.exp (Complex.I * (θ : ℂ)) ^ j *
          Complex.exp (-(Complex.I * (θ : ℂ))) ^ k =
          Complex.exp (Complex.I * (((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (θ : ℂ)) := by
        rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [mul_pow, mul_pow]
      linear_combination ((r : ℂ) ^ j * (r : ℂ) ^ k * (m.choose j : ℂ) * (m.choose k : ℂ)) * hexp
        + (m.choose j : ℂ) * (m.choose k : ℂ) *
            Complex.exp (Complex.I * (((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (θ : ℂ)) *
            (pow_add (r : ℂ) j k).symm
    simp_rw [hfun]
    rw [intervalIntegral.integral_finsetSum]
    swap
    · intro j _
      apply Continuous.intervalIntegrable
      fun_prop
    have hstep : ∀ j ∈ Finset.range (m + 1),
        ∫ θ in (-Real.pi)..Real.pi,
          ∑ k ∈ Finset.range (m + 1),
            ((m.choose j : ℂ) * (m.choose k : ℂ) * (r : ℂ) ^ (j + k)) *
              Complex.exp (Complex.I * (((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (θ : ℂ)) =
        (2 * Real.pi : ℂ) * ((m.choose j : ℂ) ^ 2 * (r : ℂ) ^ (2 * j)) := by
      intro j hj
      rw [intervalIntegral.integral_finsetSum]
      swap
      · intro k _
        apply Continuous.intervalIntegrable
        fun_prop
      simp_rw [intervalIntegral.integral_const_mul, integral_exp_I_int_mul]
      have hite : ∀ k ∈ Finset.range (m + 1),
          ((m.choose j : ℂ) * (m.choose k : ℂ) * (r : ℂ) ^ (j + k)) *
            (if (j : ℤ) - (k : ℤ) = 0 then (2 * Real.pi : ℂ) else 0) =
          if k = j then (2 * Real.pi : ℂ) * ((m.choose j : ℂ) ^ 2 * (r : ℂ) ^ (2 * j)) else 0 := by
        intro k _
        by_cases hkj : k = j
        · subst hkj
          simp only [sub_self, ↓reduceIte]
          rw [two_mul]
          ring
        · have hsub : (j : ℤ) - (k : ℤ) ≠ 0 := by omega
          simp [hkj, hsub]
      rw [Finset.sum_congr rfl hite, Finset.sum_ite_eq' _ _ _]
      simp [hj]
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
    push_cast
    rfl
  rw [intervalIntegral.integral_ofReal] at hC
  exact Complex.ofReal_injective hC

private lemma outer_integral_cos_pow (k : ℕ) :
    ∫ φ in (0 : ℝ)..Real.pi, (2 * Real.cos φ) ^ (2 * k) =
      Real.pi * ((2 * k).choose k : ℝ) := by
  have hsymm :
      ∫ φ in (-Real.pi)..Real.pi, (2 * Real.cos φ) ^ (2 * k) =
        2 * ∫ φ in (0 : ℝ)..Real.pi, (2 * Real.cos φ) ^ (2 * k) := by
    have hsplit := (intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume)
      (f := fun φ : ℝ => (2 * Real.cos φ) ^ (2 * k))
      (a := -Real.pi) (b := 0) (c := Real.pi)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)).symm
    rw [hsplit]
    have hneg : ∫ φ in (-Real.pi)..0, (2 * Real.cos φ) ^ (2 * k) =
        ∫ φ in (0 : ℝ)..Real.pi, (2 * Real.cos φ) ^ (2 * k) := by
      have hcomp := intervalIntegral.integral_comp_neg
        (f := fun φ : ℝ => (2 * Real.cos φ) ^ (2 * k)) (a := 0) (b := Real.pi)
      simpa [Real.cos_neg] using hcomp.symm
    linarith
  have hfull :
      ∫ φ in (-Real.pi)..Real.pi, (2 * Real.cos φ) ^ (2 * k) =
        2 * Real.pi * ((2 * k).choose k : ℝ) := by
    have hC :
        ∫ φ in (-Real.pi)..Real.pi, (((2 * Real.cos φ) ^ (2 * k) : ℝ) : ℂ) =
          ((2 * Real.pi * ((2 * k).choose k : ℝ) : ℝ) : ℂ) := by
      have hfun : ∀ φ : ℝ,
          (((2 * Real.cos φ) ^ (2 * k) : ℝ) : ℂ) =
          ∑ j ∈ Finset.range (2 * k + 1),
            ((2 * k).choose j : ℂ) *
              Complex.exp (Complex.I * ((2 * (j : ℤ) - 2 * (k : ℤ) : ℤ) : ℂ) * (φ : ℂ)) := by
        intro φ
        have hbase : ((2 * Real.cos φ : ℝ) : ℂ) =
            Complex.exp (Complex.I * (φ : ℂ)) + Complex.exp (-(Complex.I * (φ : ℂ))) := by
          have h1 : Complex.exp (Complex.I * (φ : ℂ)) =
              (Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I := by
            rw [mul_comm, Complex.exp_mul_I]
            simp [Complex.ofReal_cos, Complex.ofReal_sin]
          have h2 : Complex.exp (-(Complex.I * (φ : ℂ))) =
              (Real.cos φ : ℂ) - (Real.sin φ : ℂ) * Complex.I := by
            have : -(Complex.I * (φ : ℂ)) = ((-φ : ℝ) : ℂ) * Complex.I := by
              push_cast; ring
            rw [this, Complex.exp_mul_I]
            simp [Complex.ofReal_cos, Complex.ofReal_sin, sub_eq_add_neg]
          rw [h1, h2]
          push_cast
          ring
        rw [Complex.ofReal_pow, hbase, add_pow]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjle : j ≤ 2 * k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hexp :
            Complex.exp (Complex.I * (φ : ℂ)) ^ j *
            Complex.exp (-(Complex.I * (φ : ℂ))) ^ (2 * k - j) =
            Complex.exp (Complex.I * ((2 * (j : ℤ) - 2 * (k : ℤ) : ℤ) : ℂ) * (φ : ℂ)) := by
          rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
          congr 1
          have hsub : ((2 * k - j : ℕ) : ℂ) = 2 * (k : ℂ) - (j : ℂ) := by
            rw [Nat.cast_sub hjle]
            push_cast
            rfl
          rw [hsub]
          push_cast
          ring
        rw [hexp, mul_comm]
      simp_rw [hfun]
      rw [intervalIntegral.integral_finsetSum]
      swap
      · intro j _
        apply Continuous.intervalIntegrable
        fun_prop
      simp_rw [intervalIntegral.integral_const_mul, integral_exp_I_int_mul]
      have hite : ∀ j ∈ Finset.range (2 * k + 1),
          ((2 * k).choose j : ℂ) *
            (if 2 * (j : ℤ) - 2 * (k : ℤ) = 0 then (2 * Real.pi : ℂ) else 0) =
          if j = k then (2 * Real.pi : ℂ) * ((2 * k).choose k : ℂ) else 0 := by
        intro j _
        by_cases hjk : j = k
        · subst hjk
          simp [mul_comm]
        · have hne : 2 * (j : ℤ) - 2 * (k : ℤ) ≠ 0 := by omega
          simp [hjk, hne]
      rw [Finset.sum_congr rfl hite, Finset.sum_ite_eq' _ _ _]
      have hkmem : k ∈ Finset.range (2 * k + 1) := Finset.mem_range.mpr (by omega)
      simp only [hkmem, ↓reduceIte]
      push_cast
      rfl
    rw [intervalIntegral.integral_ofReal] at hC
    exact Complex.ofReal_injective hC
  linarith

private lemma outer_integral_catalan (k : ℕ) :
    ∫ φ in (0 : ℝ)..Real.pi, (2 * Real.cos φ) ^ (2 * k) * Real.sin φ ^ 2 =
      (Real.pi / 2) * (catalan k : ℝ) := by
  have hfun : ∀ φ : ℝ,
      (2 * Real.cos φ) ^ (2 * k) * Real.sin φ ^ 2 =
        (2 * Real.cos φ) ^ (2 * k) - (1 / 4 : ℝ) * (2 * Real.cos φ) ^ (2 * (k + 1)) := by
    intro φ
    have hcs := Real.sin_sq_add_cos_sq φ
    have hpow : (2 * Real.cos φ) ^ (2 * (k + 1)) =
        (2 * Real.cos φ) ^ (2 * k) * (4 * Real.cos φ ^ 2) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
      ring
    rw [hpow]
    linear_combination (2 * Real.cos φ) ^ (2 * k) * hcs
  simp_rw [hfun]
  rw [intervalIntegral.integral_sub
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul,
    outer_integral_cos_pow k, outer_integral_cos_pow (k + 1)]
  have hcat_nat : (k + 1) * catalan k = (2 * k).choose k := by
    rw [catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose]
    exact Nat.mul_div_cancel' (Nat.succ_dvd_centralBinom k)
  have hcb_nat : (k + 1) * (2 * (k + 1)).choose (k + 1) = 2 * (2 * k + 1) * (2 * k).choose k := by
    have h1 := Nat.choose_mul_factorial_mul_factorial (show k + 1 ≤ 2 * (k + 1) by omega)
    have h2 := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
    rw [show 2 * (k + 1) - (k + 1) = k + 1 by omega] at h1
    rw [show 2 * k - k = k by omega] at h2
    have hf : (2 * (k + 1)).factorial = (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
      ring
    have hpos : 0 < (k + 1) * k.factorial * k.factorial := by positivity
    apply Nat.eq_of_mul_eq_mul_right hpos
    have hL : (k + 1) * (2 * (k + 1)).choose (k + 1) * ((k + 1) * k.factorial * k.factorial) =
        (2 * (k + 1)).choose (k + 1) * (k + 1).factorial * (k + 1).factorial := by
      rw [Nat.factorial_succ]; ring
    have hR : 2 * (2 * k + 1) * (2 * k).choose k * ((k + 1) * k.factorial * k.factorial) =
        (2 * k + 2) * (2 * k + 1) * ((2 * k).choose k * k.factorial * k.factorial) := by ring
    rw [hL, h1, hf, ← h2, hR]
  have hcat_R : ((k : ℝ) + 1) * (catalan k : ℝ) = ((2 * k).choose k : ℝ) := by
    exact_mod_cast hcat_nat
  have hcb_R : ((k : ℝ) + 1) * ((2 * (k + 1)).choose (k + 1) : ℝ) =
      2 * (2 * (k : ℝ) + 1) * ((2 * k).choose k : ℝ) := by
    exact_mod_cast hcb_nat
  have hkpos : (k : ℝ) + 1 ≠ 0 := by positivity
  apply mul_left_cancel₀ hkpos
  linear_combination -(Real.pi / 4) * hcb_R - (Real.pi / 2) * hcat_R

private lemma b_eq_exp2D (m : ℕ) : (b_seq m : ℝ) = exp2D (fun x => x ^ m) := by
  unfold exp2D b_seq OMA.S_oeis_a228456.b
  have hinner : ∀ φ : ℝ,
      ∫ θ in (-Real.pi)..Real.pi, (kern φ θ) ^ m =
        2 * Real.pi * ∑ k ∈ Finset.range (m + 1),
          ((m.choose k : ℝ) ^ 2 * (2 * Real.cos φ) ^ (2 * k)) := by
    intro φ
    have hkeq : ∀ θ : ℝ, kern φ θ =
        1 + (2 * Real.cos φ) ^ 2 + 2 * (2 * Real.cos φ) * Real.cos θ := by
      intro θ; unfold kern; ring
    simp_rw [hkeq]
    exact inner_integral_pow (2 * Real.cos φ) m
  simp_rw [hinner]
  have hmul : ∀ φ : ℝ,
      (2 * Real.pi * ∑ k ∈ Finset.range (m + 1),
          ((m.choose k : ℝ) ^ 2 * (2 * Real.cos φ) ^ (2 * k))) * Real.sin φ ^ 2 =
      ∑ k ∈ Finset.range (m + 1),
        (2 * Real.pi * (m.choose k : ℝ) ^ 2) *
          ((2 * Real.cos φ) ^ (2 * k) * Real.sin φ ^ 2) := by
    intro φ
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [hmul]
  rw [intervalIntegral.integral_finsetSum]
  swap
  · intro k _
    apply Continuous.intervalIntegrable
    fun_prop
  simp_rw [intervalIntegral.integral_const_mul, outer_integral_catalan]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp [hpi]

private lemma continuous_inner_kern {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    Continuous (fun φ : ℝ => ∫ θ in a..b, f (kern φ θ)) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun φ θ => f (kern φ θ)) (hf.comp continuous_kern) a b

private lemma exp2D_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    exp2D (fun x => f x + g x) = exp2D f + exp2D g := by
  unfold exp2D
  have h1 : ∀ φ : ℝ,
      ∫ θ in (-Real.pi)..Real.pi, (f (kern φ θ) + g (kern φ θ)) =
      (∫ θ in (-Real.pi)..Real.pi, f (kern φ θ)) +
      (∫ θ in (-Real.pi)..Real.pi, g (kern φ θ)) := fun φ =>
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (hf.comp (continuous_kern.comp (continuous_const.prodMk continuous_id))) _ _)
      (Continuous.intervalIntegrable (hg.comp (continuous_kern.comp (continuous_const.prodMk continuous_id))) _ _)
  simp_rw [h1, add_mul]
  have hcF : Continuous (fun φ : ℝ => (∫ θ in (-Real.pi)..Real.pi, f (kern φ θ)) * Real.sin φ ^ 2) :=
    (continuous_inner_kern hf (-Real.pi) Real.pi).mul (by fun_prop)
  have hcG : Continuous (fun φ : ℝ => (∫ θ in (-Real.pi)..Real.pi, g (kern φ θ)) * Real.sin φ ^ 2) :=
    (continuous_inner_kern hg (-Real.pi) Real.pi).mul (by fun_prop)
  rw [intervalIntegral.integral_add (hcF.intervalIntegrable _ _) (hcG.intervalIntegrable _ _)]
  ring

private lemma exp2D_const_mul (c : ℝ) {f : ℝ → ℝ} :
    exp2D (fun x => c * f x) = c * exp2D f := by
  unfold exp2D
  simp_rw [intervalIntegral.integral_const_mul, mul_assoc, intervalIntegral.integral_const_mul]
  ring

private lemma exp2D_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    exp2D (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, exp2D (f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp [exp2D]
  | insert a s ha ih =>
    have hfa : Continuous (f a) := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, Continuous (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hcsum : Continuous (fun x => ∑ i ∈ s, f i x) := continuous_finsetSum s hfs
    simp_rw [Finset.sum_insert ha]
    rw [exp2D_add hfa hcsum, ih hfs]

private lemma exp2D_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x, 0 ≤ x → x ≤ 9 → f x ≤ g x) :
    exp2D f ≤ exp2D g := by
  unfold exp2D
  have hpi2 : 0 ≤ (1 : ℝ) / Real.pi ^ 2 := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hpi2
  have hcF : Continuous (fun φ : ℝ => (∫ θ in (-Real.pi)..Real.pi, f (kern φ θ)) * Real.sin φ ^ 2) :=
    (continuous_inner_kern hf (-Real.pi) Real.pi).mul (by fun_prop)
  have hcG : Continuous (fun φ : ℝ => (∫ θ in (-Real.pi)..Real.pi, g (kern φ θ)) * Real.sin φ ^ 2) :=
    (continuous_inner_kern hg (-Real.pi) Real.pi).mul (by fun_prop)
  refine intervalIntegral.integral_mono_on Real.pi_pos.le (hcF.intervalIntegrable _ _)
    (hcG.intervalIntegrable _ _) fun φ _ => ?_
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  refine intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
    ((hf.comp (continuous_kern.comp (continuous_const.prodMk continuous_id))).intervalIntegrable _ _)
    ((hg.comp (continuous_kern.comp (continuous_const.prodMk continuous_id))).intervalIntegrable _ _)
    fun θ _ => hfg (kern φ θ) (kern_nonneg φ θ) (kern_le_nine φ θ)

private lemma exp2D_one : exp2D (fun _ => 1) = 1 := by
  have h := b_eq_exp2D 0
  simp only [pow_zero] at h
  have hb0 : b_seq 0 = 1 := by simp [b_seq, OMA.S_oeis_a228456.b, catalan_zero]
  rw [hb0] at h
  simpa using h.symm

/-! ### Section 2: Hankel Quadratic Forms, Hadamard Upper Bound, and Schur Lower Bound -/

private def Hmat (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => (b_seq (i + j) : ℝ)

private lemma Hmat_symm (n : ℕ) : (Hmat n).IsSymm := by
  ext i j
  simp [Hmat, add_comm]

private lemma Hmat_det_eq (n : ℕ) : (Hmat n).det = (a_seq n : ℝ) := by
  unfold Hmat a_seq OMA.S_oeis_a228456.a
  have h := (RingHom.map_det (Int.castRingHom ℝ)
    (Matrix.of fun i j : Fin (n + 1) => b_seq (i + j))).symm
  have hmap : (Int.castRingHom ℝ).mapMatrix (Matrix.of fun i j : Fin (n + 1) => b_seq (i + j)) =
      Matrix.of fun i j : Fin (n + 1) => (b_seq (i + j) : ℝ) := by
    ext i j; simp
  rw [hmap] at h
  exact h

private noncomputable def polyOfVec {n : ℕ} (v : Fin (n + 1) → ℝ) : Polynomial ℝ :=
  ∑ i : Fin (n + 1), Polynomial.C (v i) * Polynomial.X ^ (i : ℕ)

private lemma eval_polyOfVec {n : ℕ} (v : Fin (n + 1) → ℝ) (x : ℝ) :
    (polyOfVec v).eval x = ∑ i : Fin (n + 1), v i * x ^ (i : ℕ) := by
  simp [polyOfVec, Polynomial.eval_finsetSum]

private lemma quadForm_Hmat {n : ℕ} (v : Fin (n + 1) → ℝ) :
    dotProduct v ((Hmat n).mulVec v) = exp2D (fun x => ((polyOfVec v).eval x) ^ 2) := by
  have hfun : ∀ x : ℝ, ((polyOfVec v).eval x) ^ 2 =
      ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), (v i * v j) * x ^ ((i : ℕ) + (j : ℕ)) := by
    intro x
    rw [eval_polyOfVec, sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]
    ring
  simp_rw [hfun]
  rw [exp2D_finset_sum]
  swap
  · intro i _
    exact continuous_finsetSum _ fun j _ => by fun_prop
  simp only [dotProduct, Matrix.mulVec, Hmat, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [exp2D_finset_sum]
  swap
  · intro j _
    fun_prop
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [exp2D_const_mul, ← b_eq_exp2D]
  ring

private lemma quadForm_Hmat_nonneg {n : ℕ} (v : Fin (n + 1) → ℝ) :
    0 ≤ dotProduct v ((Hmat n).mulVec v) := by
  rw [quadForm_Hmat]
  have h0 : exp2D (fun _ => 0) = 0 := by
    simpa using exp2D_const_mul 0 (f := fun _ => 1)
  rw [← h0]
  exact exp2D_mono continuous_const ((continuous_poly_eval _).pow 2) fun x _ _ => sq_nonneg _

/- Elementary Hadamard inequality for symmetric PSD real matrices. -/
open InnerProductSpace WithLp
open scoped InnerProductSpace MatrixOrder

private lemma gram_det_le {n : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin n)) :
    (Matrix.gram ℝ v).det ≤ ∏ i, inner ℝ (v i) (v i) := by
  let b := gramSchmidtOrthonormalBasis (𝕜 := ℝ) (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n)) v
  have hg := Matrix.gram_eq_conjTranspose_mul b v
  change Matrix.gram ℝ v = (b.toBasis.toMatrix v)ᴴ * b.toBasis.toMatrix v at hg
  rw [hg, Matrix.det_mul, Matrix.det_conjTranspose]
  change (b.toBasis.det v) * (b.toBasis.det v) ≤ _
  rw [gramSchmidtOrthonormalBasis_det, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun i _ => mul_self_nonneg _) fun i _ => ?_
  simpa [real_inner_self_eq_norm_sq, b.orthonormal.1 i] using real_inner_mul_inner_self_le (b i) (v i)

private lemma hadamard_psd {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ)
    (hsymm : M.IsSymm) (hpsd : ∀ v, 0 ≤ dotProduct v (M.mulVec v)) :
    0 ≤ M.det ∧ M.det ≤ ∏ i : Fin m, M i i := by
  have hM : M.PosSemidef := .of_dotProduct_mulVec_nonneg (by simpa [Matrix.IsHermitian] using hsymm.eq) (by simpa using hpsd)
  refine ⟨hM.det_nonneg, ?_⟩
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  let v : Fin m → EuclideanSpace ℝ (Fin m) := fun i => toLp 2 (fun j => B j i)
  have hg : Matrix.gram ℝ v = M := by
    rw [hB]
    ext i j
    simp [Matrix.gram, v, EuclideanSpace.inner_toLp_toLp, Matrix.mul_apply, dotProduct, mul_comm]
  simpa [← hg, Matrix.gram_apply] using gram_det_le v



/-- Upper bound on Hankel determinant from any family of monic polynomials `p k` of degree `k`. -/
private lemma Hmat_det_le_prod_monic (n : ℕ) (p : ℕ → Polynomial ℝ)
    (hdeg : ∀ k ≤ n, (p k).natDegree = k)
    (hmon : ∀ k ≤ n, (p k).leadingCoeff = 1) :
    (Hmat n).det ≤ ∏ k ∈ Finset.range (n + 1), exp2D (fun x => ((p k).eval x) ^ 2) := by
  let P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.of fun i j => (p i).coeff j
  have hP_tri : P.IsLowerTriangular := by
    intro i j hij
    change (p i).coeff j = 0
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [hdeg i (Nat.lt_succ_iff.mp i.isLt)]
    exact hij
  have hP_det : P.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular P hP_tri]
    refine Finset.prod_eq_one fun i _ => ?_
    change (p i).coeff i = 1
    have hd := hdeg i (Nat.lt_succ_iff.mp i.isLt)
    have hm := hmon i (Nat.lt_succ_iff.mp i.isLt)
    rw [Polynomial.leadingCoeff, hd] at hm
    exact hm
  let G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := P * Hmat n * Pᵀ
  have hG_det : G.det = (Hmat n).det := by
    simp [G, Matrix.det_mul, Matrix.det_transpose, hP_det]
  have hG_symm : G.IsSymm := by
    change Gᵀ = G
    simp only [G, Matrix.transpose_mul, Matrix.transpose_transpose, (Hmat_symm n).eq, Matrix.mul_assoc]
  have hG_psd : ∀ v, 0 ≤ dotProduct v (G.mulVec v) := by
    intro v
    have h1 : dotProduct v (G.mulVec v) = dotProduct (Pᵀ.mulVec v) ((Hmat n).mulVec (Pᵀ.mulVec v)) := by
      dsimp only [G]
      rw [Matrix.mul_assoc P (Hmat n) Pᵀ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    rw [h1]
    exact quadForm_Hmat_nonneg _
  have hhad := (hadamard_psd G hG_symm hG_psd).2
  rw [hG_det] at hhad
  have hdiag : ∀ i : Fin (n + 1), G i i = exp2D (fun x => ((p i).eval x) ^ 2) := by
    intro i
    let v : Fin (n + 1) → ℝ := fun j => P i j
    have hv : G i i = dotProduct v ((Hmat n).mulVec v) := by
      simp only [G, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, v,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    rw [hv, quadForm_Hmat]
    have hpeq : polyOfVec v = p i := by
      ext m
      by_cases hm : m < n + 1
      · simp only [polyOfVec, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_eq_single ⟨m, hm⟩]
        · simp [v, P]
        · intro b _ hb
          have hne : m ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
          simp [hne]
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      · have h1 : (polyOfVec v).coeff m = 0 := by
          simp only [polyOfVec, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
            Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
          refine Finset.sum_eq_zero fun b _ => ?_
          have hne : m ≠ (b : ℕ) := by omega
          simp [hne]
        have h2 : (p i).coeff m = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          rw [hdeg i (Nat.lt_succ_iff.mp i.isLt)]
          omega
        rw [h1, h2]
    rw [hpeq]
  calc
    (Hmat n).det ≤ ∏ i : Fin (n + 1), G i i := hhad
    _ = ∏ i : Fin (n + 1), exp2D (fun x => ((p i).eval x) ^ 2) :=
      Finset.prod_congr rfl fun i _ => hdiag i
    _ = ∏ k ∈ Finset.range (n + 1), exp2D (fun x => ((p k).eval x) ^ 2) := by
      rw [Fin.prod_univ_eq_prod_range (fun k : ℕ => exp2D (fun x => ((p k).eval x) ^ 2))]

/-- Lower bound on Hankel determinant from a lower bound `c k` over all monic degree-`k` polynomials. -/
private lemma prod_le_Hmat_det (c : ℕ → ℝ) (hc_pos : ∀ k, 0 < c k)
    (hc : ∀ k (q : Polynomial ℝ), q.natDegree = k → q.leadingCoeff = 1 →
      c k ≤ exp2D (fun x => (q.eval x) ^ 2)) :
    ∀ n : ℕ, ∏ k ∈ Finset.range (n + 1), c k ≤ (Hmat n).det
  | 0 => by
    rw [Finset.prod_range_one]
    have hdet0 : (Hmat 0).det = exp2D (fun x => ((1 : Polynomial ℝ).eval x) ^ 2) := by
      simp [Hmat, Matrix.det_unique, b_eq_exp2D]
    rw [hdet0]
    exact hc 0 1 Polynomial.natDegree_one Polynomial.leadingCoeff_one
  | n + 1 => by
    have hIH := prod_le_Hmat_det c hc_pos hc n
    have hprod_pos : 0 < ∏ k ∈ Finset.range (n + 1), c k :=
      Finset.prod_pos fun k _ => hc_pos k
    have hAn_pos : 0 < (Hmat n).det := lt_of_lt_of_le hprod_pos hIH
    have hAn_unit : IsUnit (Hmat n).det := isUnit_iff_ne_zero.mpr hAn_pos.ne'
    haveI : Invertible (Hmat n) := Matrix.invertibleOfIsUnitDet (Hmat n) hAn_unit
    let f : Fin (n + 1) ⊕ Unit ≃ Fin (n + 2) :=
      { toFun := Sum.elim Fin.castSucc (fun _ => Fin.last (n + 1))
        invFun := fun i => Fin.lastCases (Sum.inr ()) Sum.inl i
        left_inv := fun x => by
          cases x with
          | inl i => simp [Fin.lastCases_castSucc]
          | inr u => cases u; simp [Fin.lastCases_last]
        right_inv := fun i =>
          Fin.lastCases (by simp [Fin.lastCases_last]) (fun j => by simp [Fin.lastCases_castSucc]) i }
    let u : Fin (n + 1) → ℝ := fun i => (b_seq ((i : ℕ) + (n + 1)) : ℝ)
    let d : ℝ := (b_seq (2 * (n + 1)) : ℝ)
    let M' : Matrix (Fin (n + 1) ⊕ Unit) (Fin (n + 1) ⊕ Unit) ℝ :=
      Matrix.reindex f.symm f.symm (Hmat (n + 1))
    have hM'_eq : M' = Matrix.fromBlocks
        (Hmat n)
        (Matrix.of fun i (_ : Unit) => u i)
        (Matrix.of fun (_ : Unit) j => u j)
        (Matrix.of fun (_ _ : Unit) => d) := by
      ext x y
      cases x with
      | inl i =>
        cases y with
        | inl j => simp [M', f, Hmat]
        | inr v => cases v; simp [M', f, Hmat, u]
      | inr v =>
        cases v
        cases y with
        | inl j => simp [M', f, Hmat, u, add_comm]
        | inr w =>
          cases w
          simp [M', f, Hmat, d, two_mul]
    have hschur : (Hmat (n + 1)).det =
        (Hmat n).det * (d - dotProduct u ((⅟(Hmat n)).mulVec u)) := by
      rw [← Matrix.det_reindex_self f.symm (Hmat (n + 1))]
      change M'.det = _
      rw [hM'_eq, Matrix.det_fromBlocks₁₁]
      congr 1
      rw [Matrix.det_unique]
      simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply, dotProduct, Matrix.mulVec]
      congr 1
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    let w : Fin (n + 1) → ℝ := -((⅟(Hmat n)).mulVec u)
    let v : Fin (n + 2) → ℝ := Fin.lastCases (1 : ℝ) w
    have hquad : dotProduct v ((Hmat (n + 1)).mulVec v) =
        d - dotProduct u ((⅟(Hmat n)).mulVec u) := by
      have hAw : (Hmat n).mulVec w = -u := by
        dsimp [w]
        rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, mul_invOf_self, Matrix.one_mulVec]
      have hmul_cast : ∀ i : Fin (n + 1),
          ((Hmat (n + 1)).mulVec v) i.castSucc = 0 := by
        intro i
        rw [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
        simp only [v, Fin.lastCases_castSucc, Fin.lastCases_last, mul_one]
        have h1 : ∑ j : Fin (n + 1), Hmat (n + 1) i.castSucc j.castSucc * w j =
            ((Hmat n).mulVec w) i := rfl
        have h2 : Hmat (n + 1) i.castSucc (Fin.last (n + 1)) = u i := by
          simp [Hmat, u]
        rw [h1, h2, hAw]
        simp
      have hmul_last : ((Hmat (n + 1)).mulVec v) (Fin.last (n + 1)) =
          d - dotProduct u ((⅟(Hmat n)).mulVec u) := by
        rw [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
        simp only [v, Fin.lastCases_castSucc, Fin.lastCases_last, mul_one]
        have h1 : ∀ j : Fin (n + 1),
            Hmat (n + 1) (Fin.last (n + 1)) j.castSucc = u j := fun j => by
          simp [Hmat, u, add_comm]
        have h2 : Hmat (n + 1) (Fin.last (n + 1)) (Fin.last (n + 1)) = d := by
          simp [Hmat, d, two_mul]
        simp_rw [h1, h2]
        have hdot : ∑ j : Fin (n + 1), u j * w j = -dotProduct u ((⅟(Hmat n)).mulVec u) := by
          dsimp [w, dotProduct]
          simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
        rw [hdot]
        ring
      rw [dotProduct, Fin.sum_univ_castSucc]
      simp only [hmul_cast, mul_zero, Finset.sum_const_zero, zero_add, v,
        Fin.lastCases_last, one_mul, hmul_last]
    have hpoly_deg : (polyOfVec v).natDegree = n + 1 := by
      have hcoeff_top : (polyOfVec v).coeff (n + 1) = 1 := by
        simp only [polyOfVec, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_eq_single (Fin.last (n + 1))]
        · simp [v, Fin.lastCases_last]
        · intro b _ hb
          have hne : n + 1 ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
          simp [hne]
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      have hcoeff_gt : ∀ m, n + 1 < m → (polyOfVec v).coeff m = 0 := by
        intro m hm
        simp only [polyOfVec, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
        refine Finset.sum_eq_zero fun b _ => ?_
        have hne : m ≠ (b : ℕ) := by omega
        simp [hne]
      apply le_antisymm
      · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        exact hcoeff_gt
      · exact Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff_top]; norm_num)
    have hpoly_mon : (polyOfVec v).leadingCoeff = 1 := by
      rw [Polynomial.leadingCoeff, hpoly_deg]
      simp only [polyOfVec, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_eq_single (Fin.last (n + 1))]
      · simp [v, Fin.lastCases_last]
      · intro b _ hb
        have hne : n + 1 ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
        simp [hne]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    have hstep : c (n + 1) ≤ d - dotProduct u ((⅟(Hmat n)).mulVec u) := by
      rw [← hquad, quadForm_Hmat]
      exact hc (n + 1) (polyOfVec v) hpoly_deg hpoly_mon
    rw [Finset.prod_range_succ, hschur]
    exact mul_le_mul hIH hstep (hc_pos (n + 1)).le hAn_pos.le

/-! ### Section 3: Monic Chebyshev T_k Upper Bound -/

private noncomputable abbrev chebT (k : ℕ) : Polynomial ℝ := Polynomial.Chebyshev.T ℝ k
private lemma chebT_eval_cos (k : ℕ) (t : ℝ) :
    (chebT k).eval (Real.cos t) = Real.cos ((k : ℝ) * t) := by
  simpa [chebT] using Polynomial.Chebyshev.T_real_cos t (k : ℤ)


private lemma abs_chebT_le_one (k : ℕ) {y : ℝ} (hy1 : -1 ≤ y) (hy2 : y ≤ 1) :
    |(chebT k).eval y| ≤ 1 := by
  have hcos : Real.cos (Real.arccos y) = y := Real.cos_arccos hy1 hy2
  rw [← hcos, chebT_eval_cos]
  exact Real.abs_cos_le_one _

private lemma chebT_deg_lc (k : ℕ) :
    (chebT k).natDegree = k ∧
      (chebT k).leadingCoeff = if k = 0 then 1 else (2 : ℝ) ^ (k - 1) := by
  simp only [chebT, Polynomial.Chebyshev.natDegree_T, Polynomial.Chebyshev.leadingCoeff_T, Int.natAbs_natCast]
  split_ifs with h <;> simp_all


private noncomputable def monicCheb (k : ℕ) : Polynomial ℝ :=
  if k = 0 then 1
  else Polynomial.C (2 * ((9 : ℝ) / 4) ^ k) *
    (chebT k).comp (Polynomial.C (2 / 9) * Polynomial.X - Polynomial.C 1)

private lemma monicCheb_deg_lc (k : ℕ) :
    (monicCheb k).natDegree = k ∧ (monicCheb k).leadingCoeff = 1 := by
  by_cases hk : k = 0
  · subst hk; simp [monicCheb]
  · simp only [monicCheb, hk, ↓reduceIte]
    set L : Polynomial ℝ := Polynomial.C (2 / 9) * Polynomial.X - Polynomial.C 1
    have hL_deg : L.natDegree = 1 := by
      dsimp [L]
      rw [sub_eq_add_neg, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
      · rw [Polynomial.natDegree_C_mul (by norm_num), Polynomial.natDegree_X]
      · rw [Polynomial.natDegree_neg, Polynomial.natDegree_C,
          Polynomial.natDegree_C_mul (by norm_num), Polynomial.natDegree_X]
        norm_num
    have hL_lc : L.leadingCoeff = 2 / 9 := by
      dsimp [L]
      rw [sub_eq_add_neg, add_comm, Polynomial.leadingCoeff_add_of_degree_lt]
      · rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_X, mul_one]
      · rw [Polynomial.degree_neg]
        apply Polynomial.degree_lt_degree
        rw [Polynomial.natDegree_C, Polynomial.natDegree_C_mul (by norm_num), Polynomial.natDegree_X]
        norm_num
    have hT := chebT_deg_lc k
    have hT_lc : (chebT k).leadingCoeff = (2 : ℝ) ^ (k - 1) := by
      simpa [hk] using hT.2
    have hc_ne : (2 * ((9 : ℝ) / 4) ^ k) ≠ 0 := by positivity
    have hcomp_deg : ((chebT k).comp L).natDegree = k := by
      rw [Polynomial.natDegree_comp, hT.1, hL_deg, mul_one]
    have hcomp_lc : ((chebT k).comp L).leadingCoeff = (2 : ℝ) ^ (k - 1) * (2 / 9) ^ k := by
      rw [Polynomial.leadingCoeff_comp (by rw [hL_deg]; norm_num), hT_lc, hL_lc, hT.1]
    refine ⟨?_, ?_⟩
    · rw [Polynomial.natDegree_C_mul hc_ne, hcomp_deg]
    · rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hcomp_lc]
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      rw [Nat.succ_sub_one, pow_succ, pow_succ]
      have hprod : (2 : ℝ) ^ m * (2 / 9) ^ m * (9 / 4) ^ m = 1 := by
        rw [← mul_pow, ← mul_pow]; norm_num
      calc 2 * (((9 : ℝ) / 4) ^ m * (9 / 4)) * ((2 : ℝ) ^ m * ((2 / 9) ^ m * (2 / 9)))
          = ((2 : ℝ) ^ m * (2 / 9) ^ m * (9 / 4) ^ m) * (2 * (9 / 4) * (2 / 9)) := by ring
        _ = 1 := by rw [hprod]; norm_num

private lemma monicCheb_sq_le (k : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx9 : x ≤ 9) :
    ((monicCheb k).eval x) ^ 2 ≤ 4 * ((9 : ℝ) / 4) ^ (2 * k) := by
  by_cases hk : k = 0
  · subst hk; simp only [monicCheb, ↓reduceIte, Polynomial.eval_one]; norm_num
  · simp only [monicCheb, hk, ↓reduceIte, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X]
    have hy1 : -1 ≤ (2 / 9 : ℝ) * x - 1 := by linarith
    have hy2 : (2 / 9 : ℝ) * x - 1 ≤ 1 := by linarith
    have habs := abs_chebT_le_one k hy1 hy2
    have hsq : ((chebT k).eval ((2 / 9 : ℝ) * x - 1)) ^ 2 ≤ 1 := by
      nlinarith [sq_abs ((chebT k).eval ((2 / 9 : ℝ) * x - 1)),
        abs_nonneg ((chebT k).eval ((2 / 9 : ℝ) * x - 1))]
    have hpow : (2 * ((9 : ℝ) / 4) ^ k) ^ 2 = 4 * ((9 : ℝ) / 4) ^ (2 * k) := by
      rw [mul_pow, ← pow_mul, mul_comm k 2]
      norm_num
    rw [mul_pow, hpow]
    nlinarith [show (0 : ℝ) ≤ 4 * ((9 : ℝ) / 4) ^ (2 * k) by positivity]

private lemma a_seq_upper_bound (n : ℕ) :
    (a_seq n : ℝ) ≤ 4 ^ (n + 1) * ((9 : ℝ) / 4) ^ (n * (n + 1)) := by
  rw [← Hmat_det_eq n]
  have h1 := Hmat_det_le_prod_monic n monicCheb
    (fun k _ => (monicCheb_deg_lc k).1) (fun k _ => (monicCheb_deg_lc k).2)
  have h2 : ∀ k ∈ Finset.range (n + 1),
      exp2D (fun x => ((monicCheb k).eval x) ^ 2) ≤ 4 * ((9 : ℝ) / 4) ^ (2 * k) := by
    intro k _
    have hconst : exp2D (fun _ => 4 * ((9 : ℝ) / 4) ^ (2 * k)) = 4 * ((9 : ℝ) / 4) ^ (2 * k) := by
      rw [show (fun _ : ℝ => 4 * ((9 : ℝ) / 4) ^ (2 * k)) =
            (fun x : ℝ => (4 * ((9 : ℝ) / 4) ^ (2 * k)) * (1 : ℝ)) by ext; ring,
        exp2D_const_mul, exp2D_one, mul_one]
    rw [← hconst]
    exact exp2D_mono ((continuous_poly_eval _).pow 2) continuous_const fun x hx0 hx9 => monicCheb_sq_le k hx0 hx9
  have hnn : ∀ k ∈ Finset.range (n + 1), 0 ≤ exp2D (fun x => ((monicCheb k).eval x) ^ 2) := by
    intro k _
    have h0 : exp2D (fun _ => 0) = 0 := by simpa using exp2D_const_mul 0 (f := fun _ => 1)
    rw [← h0]
    exact exp2D_mono continuous_const ((continuous_poly_eval _).pow 2) fun x _ _ => sq_nonneg _
  have hprod : ∏ k ∈ Finset.range (n + 1), (4 * ((9 : ℝ) / 4) ^ (2 * k)) =
      4 ^ (n + 1) * ((9 : ℝ) / 4) ^ (n * (n + 1)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    congr 1
    -- Wait: prod_pow_eq_pow_sum is for constant base
    have hsum : ∑ k ∈ Finset.range (n + 1), 2 * k = n * (n + 1) := by
      rw [← Finset.mul_sum]
      have := Finset.sum_range_id_mul_two (n + 1)
      simpa [mul_comm] using this
    rw [← hsum]
    clear h1 h2 hnn hsum
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.prod_range_succ, Finset.sum_range_succ, pow_add, ih]
  calc
    (Hmat n).det ≤ ∏ k ∈ Finset.range (n + 1), exp2D (fun x => ((monicCheb k).eval x) ^ 2) := h1
    _ ≤ ∏ k ∈ Finset.range (n + 1), (4 * ((9 : ℝ) / 4) ^ (2 * k)) := Finset.prod_le_prod hnn h2
    _ = 4 ^ (n + 1) * ((9 : ℝ) / 4) ^ (n * (n + 1)) := hprod

/-! ### Section 4: Monic Chebyshev U_k Lower Bound on [-1, 1] and [a, b] -/

private noncomputable abbrev chebU (k : ℕ) : Polynomial ℝ := Polynomial.Chebyshev.U ℝ k
private lemma chebU_eval_cos_mul_sin (k : ℕ) (t : ℝ) :
    (chebU k).eval (Real.cos t) * Real.sin t = Real.sin (((k + 1 : ℕ) : ℝ) * t) := by
  simpa [chebU] using Polynomial.Chebyshev.U_real_cos t (k : ℤ)
private lemma chebU_deg_lc (k : ℕ) :
    (chebU k).natDegree = k ∧ (chebU k).leadingCoeff = (2 : ℝ) ^ k := by
  simp [chebU]



private lemma integral_cos_int_mul_zero_pi (d : ℤ) :
    ∫ t in (0 : ℝ)..Real.pi, Real.cos ((d : ℝ) * t) = if d = 0 then Real.pi else 0 := by
  by_cases hd : d = 0
  · subst hd; simp
  · simp only [hd, ↓reduceIte]
    have hne : (d : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hd
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) Real.pi,
        HasDerivAt (fun x : ℝ => Real.sin ((d : ℝ) * x) / (d : ℝ)) (Real.cos ((d : ℝ) * t)) t := by
      intro t _
      have h1 : HasDerivAt (fun x : ℝ => (d : ℝ) * x) (d : ℝ) t := by
        simpa using (hasDerivAt_id t).const_mul (d : ℝ)
      have h2 := h1.sin.div_const (d : ℝ)
      simpa [mul_div_cancel_right₀ _ hne] using h2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    have hsinpi : Real.sin ((d : ℝ) * Real.pi) = 0 := Real.sin_int_mul_pi d
    simp [hsinpi]

private lemma integral_sin_mul_sin (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∫ t in (0 : ℝ)..Real.pi, Real.sin ((m : ℝ) * t) * Real.sin ((n : ℝ) * t) =
      if m = n then Real.pi / 2 else 0 := by
  have hfun : ∀ t : ℝ,
      Real.sin ((m : ℝ) * t) * Real.sin ((n : ℝ) * t) =
        (1 / 2 : ℝ) * (Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t) -
          Real.cos ((((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * t)) := by
    intro t
    have h1 := Real.cos_sub ((m : ℝ) * t) ((n : ℝ) * t)
    have h2 := Real.cos_add ((m : ℝ) * t) ((n : ℝ) * t)
    have hs1 : (((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t = (m : ℝ) * t - (n : ℝ) * t := by push_cast; ring
    have hs2 : (((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * t = (m : ℝ) * t + (n : ℝ) * t := by push_cast; ring
    rw [hs1, hs2]
    linarith
  simp_rw [hfun]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    integral_cos_int_mul_zero_pi, integral_cos_int_mul_zero_pi]
  have hplus : (m : ℤ) + (n : ℤ) ≠ 0 := by omega
  simp only [hplus, ↓reduceIte, sub_zero]
  by_cases hmn : m = n
  · subst hmn; simp [div_eq_mul_inv, mul_comm]
  · have hsub : (m : ℤ) - (n : ℤ) ≠ 0 := by omega
    simp [hmn, hsub]

private lemma integral_poly_lt_deg_orthog (k : ℕ) :
    ∀ d : ℕ, d < k → ∀ r : Polynomial ℝ, r.natDegree ≤ d →
      ∫ t in (0 : ℝ)..Real.pi,
        r.eval (Real.cos t) * Real.sin t * Real.sin (((k + 1 : ℕ) : ℝ) * t) = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hdk r hr
    by_cases hr0 : r = 0
    · simp [hr0]
    · set m : ℕ := r.natDegree
      have hmk : m < k := lt_of_le_of_lt hr hdk
      set c : ℝ := r.leadingCoeff / (2 : ℝ) ^ m
      set r' : Polynomial ℝ := r - Polynomial.C c * chebU m
      have hr_eq : r = Polynomial.C c * chebU m + r' := by dsimp [r']; ring
      have hr'_int : ∫ t in (0 : ℝ)..Real.pi,
          r'.eval (Real.cos t) * Real.sin t * Real.sin (((k + 1 : ℕ) : ℝ) * t) = 0 := by
        by_cases hr'0 : r' = 0
        · simp [hr'0]
        · have hr'_lt : r'.natDegree < m := by
            have hU := chebU_deg_lc m
            have hdeg_term : (Polynomial.C c * chebU m).natDegree = m := by
              have hcne : c ≠ 0 := by
                dsimp [c]
                exact div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hr0) (by positivity)
              rw [Polynomial.natDegree_C_mul hcne, hU.1]
            have hcoeff_m : r'.coeff m = 0 := by
              dsimp [r', c]
              rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
              have hUm : (chebU m).coeff m = (2 : ℝ) ^ m := by
                have := hU.2; rw [Polynomial.leadingCoeff, hU.1] at this; exact this
              have hrm : r.coeff m = r.leadingCoeff := rfl
              rw [hUm, hrm, div_mul_cancel₀ _ (by positivity), sub_self]
            have hle : r'.natDegree ≤ m := by
              refine le_trans (Polynomial.natDegree_sub_le r _) ?_
              simp [m, hdeg_term]
            exact lt_of_le_of_ne hle fun heq => by
              have hne : r'.coeff r'.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hr'0
              rw [heq] at hne
              exact hne hcoeff_m
          exact ih r'.natDegree (lt_of_lt_of_le hr'_lt hr) (lt_trans hr'_lt hmk) r' le_rfl
      have hU_int : ∫ t in (0 : ℝ)..Real.pi,
          (Polynomial.C c * chebU m).eval (Real.cos t) * Real.sin t *
            Real.sin (((k + 1 : ℕ) : ℝ) * t) = 0 := by
        have hfun : ∀ t : ℝ,
            (Polynomial.C c * chebU m).eval (Real.cos t) * Real.sin t *
              Real.sin (((k + 1 : ℕ) : ℝ) * t) =
            c * (Real.sin (((m + 1 : ℕ) : ℝ) * t) * Real.sin (((k + 1 : ℕ) : ℝ) * t)) := by
          intro t
          simp only [Polynomial.eval_mul, Polynomial.eval_C]
          calc c * (chebU m).eval (Real.cos t) * Real.sin t * Real.sin (((k + 1 : ℕ) : ℝ) * t)
              = c * (((chebU m).eval (Real.cos t) * Real.sin t) * Real.sin (((k + 1 : ℕ) : ℝ) * t)) := by ring
            _ = c * (Real.sin (((m + 1 : ℕ) : ℝ) * t) * Real.sin (((k + 1 : ℕ) : ℝ) * t)) := by
              rw [chebU_eval_cos_mul_sin m t]
        simp_rw [hfun]
        rw [intervalIntegral.integral_const_mul,
          integral_sin_mul_sin (m + 1) (k + 1) (Nat.succ_pos m) (Nat.succ_pos k)]
        have hne : m + 1 ≠ k + 1 := by omega
        simp only [hne, ↓reduceIte, mul_zero]
      have hsplit : ∀ t : ℝ,
          r.eval (Real.cos t) * Real.sin t * Real.sin (((k + 1 : ℕ) : ℝ) * t) =
          (Polynomial.C c * chebU m).eval (Real.cos t) * Real.sin t *
            Real.sin (((k + 1 : ℕ) : ℝ) * t) +
          r'.eval (Real.cos t) * Real.sin t * Real.sin (((k + 1 : ℕ) : ℝ) * t) := by
        intro t
        rw [hr_eq, Polynomial.eval_add]
        ring
      simp_rw [hsplit]
      have hc1 : Continuous (fun t : ℝ => (Polynomial.C c * chebU m).eval (Real.cos t) *
          Real.sin t * Real.sin (((k + 1 : ℕ) : ℝ) * t)) :=
        (((continuous_poly_eval _).comp Real.continuous_cos).mul Real.continuous_sin).mul (by fun_prop)
      have hc2 : Continuous (fun t : ℝ => r'.eval (Real.cos t) *
          Real.sin t * Real.sin (((k + 1 : ℕ) : ℝ) * t)) :=
        (((continuous_poly_eval _).comp Real.continuous_cos).mul Real.continuous_sin).mul (by fun_prop)
      rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
        hU_int, hr'_int, add_zero]

private lemma integral_monic_chebU_inner (k : ℕ) (q : Polynomial ℝ)
    (hdeg : q.natDegree = k) (hmon : q.leadingCoeff = 1) :
    ∫ t in (0 : ℝ)..Real.pi,
      q.eval (Real.cos t) * Real.sin t * Real.sin (((k + 1 : ℕ) : ℝ) * t) =
      Real.pi / (2 * (2 : ℝ) ^ k) := by
  set c : ℝ := 1 / (2 : ℝ) ^ k
  set r : Polynomial ℝ := q - Polynomial.C c * chebU k
  have hq_eq : q = Polynomial.C c * chebU k + r := by dsimp [r]; ring
  have hr_int : ∫ t in (0 : ℝ)..Real.pi,
      r.eval (Real.cos t) * Real.sin t * Real.sin (((k + 1 : ℕ) : ℝ) * t) = 0 := by
    by_cases hr0 : r = 0
    · simp [hr0]
    · have hr_lt : r.natDegree < k := by
        have hU := chebU_deg_lc k
        have hdeg_term : (Polynomial.C c * chebU k).natDegree = k := by
          rw [Polynomial.natDegree_C_mul (by dsimp [c]; positivity), hU.1]
        have hcoeff_k : r.coeff k = 0 := by
          dsimp [r, c]
          rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
          have hUk : (chebU k).coeff k = (2 : ℝ) ^ k := by
            have := hU.2; rw [Polynomial.leadingCoeff, hU.1] at this; exact this
          have hqk : q.coeff k = 1 := by rw [← hdeg]; exact hmon
          rw [hUk, hqk, one_div_mul_cancel (by positivity), sub_self]
        have hle : r.natDegree ≤ k := by
          refine le_trans (Polynomial.natDegree_sub_le q _) ?_
          simp [hdeg, hdeg_term]
        exact lt_of_le_of_ne hle fun heq => by
          have hne : r.coeff r.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hr0
          rw [heq] at hne
          exact hne hcoeff_k
      exact integral_poly_lt_deg_orthog k r.natDegree hr_lt r le_rfl
  have hU_int : ∫ t in (0 : ℝ)..Real.pi,
      (Polynomial.C c * chebU k).eval (Real.cos t) * Real.sin t *
        Real.sin (((k + 1 : ℕ) : ℝ) * t) = Real.pi / (2 * (2 : ℝ) ^ k) := by
    have hfun : ∀ t : ℝ,
        (Polynomial.C c * chebU k).eval (Real.cos t) * Real.sin t *
          Real.sin (((k + 1 : ℕ) : ℝ) * t) =
        c * (Real.sin (((k + 1 : ℕ) : ℝ) * t) * Real.sin (((k + 1 : ℕ) : ℝ) * t)) := by
      intro t
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      calc c * (chebU k).eval (Real.cos t) * Real.sin t * Real.sin (((k + 1 : ℕ) : ℝ) * t)
          = c * (((chebU k).eval (Real.cos t) * Real.sin t) * Real.sin (((k + 1 : ℕ) : ℝ) * t)) := by ring
        _ = c * (Real.sin (((k + 1 : ℕ) : ℝ) * t) * Real.sin (((k + 1 : ℕ) : ℝ) * t)) := by
          rw [chebU_eval_cos_mul_sin k t]
    simp_rw [hfun]
    rw [intervalIntegral.integral_const_mul,
      integral_sin_mul_sin (k + 1) (k + 1) (Nat.succ_pos k) (Nat.succ_pos k)]
    simp only [↓reduceIte, c]
    ring
  have hsplit : ∀ t : ℝ,
      q.eval (Real.cos t) * Real.sin t * Real.sin (((k + 1 : ℕ) : ℝ) * t) =
      (Polynomial.C c * chebU k).eval (Real.cos t) * Real.sin t *
        Real.sin (((k + 1 : ℕ) : ℝ) * t) +
      r.eval (Real.cos t) * Real.sin t * Real.sin (((k + 1 : ℕ) : ℝ) * t) := by
    intro t
    rw [hq_eq, Polynomial.eval_add]
    ring
  simp_rw [hsplit]
  have hc1 : Continuous (fun t : ℝ => (Polynomial.C c * chebU k).eval (Real.cos t) *
      Real.sin t * Real.sin (((k + 1 : ℕ) : ℝ) * t)) :=
    (((continuous_poly_eval _).comp Real.continuous_cos).mul Real.continuous_sin).mul (by fun_prop)
  have hc2 : Continuous (fun t : ℝ => r.eval (Real.cos t) *
      Real.sin t * Real.sin (((k + 1 : ℕ) : ℝ) * t)) :=
    (((continuous_poly_eval _).comp Real.continuous_cos).mul Real.continuous_sin).mul (by fun_prop)
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
    hU_int, hr_int, add_zero]

private lemma intervalIntegral_cauchy_schwarz {a b : ℝ} (hab : a ≤ b)
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    (∫ t in a..b, f t * g t) ^ 2 ≤ (∫ t in a..b, f t ^ 2) * (∫ t in a..b, g t ^ 2) := by
  set A := ∫ t in a..b, f t ^ 2
  set B := ∫ t in a..b, f t * g t
  set C := ∫ t in a..b, g t ^ 2
  have hquad : ∀ lam : ℝ, 0 ≤ A + 2 * lam * B + lam ^ 2 * C := by
    intro lam
    have hnn : 0 ≤ ∫ t in a..b, (f t + lam * g t) ^ 2 :=
      intervalIntegral.integral_nonneg hab fun t _ => sq_nonneg _
    have hexp : ∀ t : ℝ, (f t + lam * g t) ^ 2 =
        f t ^ 2 + 2 * lam * (f t * g t) + lam ^ 2 * g t ^ 2 := fun t => by ring
    simp_rw [hexp] at hnn
    rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hnn
    exact hnn
  have hd := discrim_le_zero (a := C) (b := 2 * B) (c := A)
    (fun x => by nlinarith [hquad x])
  dsimp only [discrim] at hd
  nlinarith

private lemma monic_L2_lower_unit (k : ℕ) (q : Polynomial ℝ)
    (hdeg : q.natDegree = k) (hmon : q.leadingCoeff = 1) :
    Real.pi / (2 * (4 : ℝ) ^ k) ≤ ∫ u in (-1 : ℝ)..1, (q.eval u) ^ 2 := by
  have hc_qcos : Continuous (fun t : ℝ => q.eval (Real.cos t)) :=
    (continuous_poly_eval q).comp Real.continuous_cos
  have hcs := intervalIntegral_cauchy_schwarz Real.pi_pos.le
    (f := fun t => q.eval (Real.cos t) * Real.sin t)
    (g := fun t => Real.sin (((k + 1 : ℕ) : ℝ) * t))
    (hc_qcos.mul Real.continuous_sin) (by fun_prop)
  rw [integral_monic_chebU_inner k q hdeg hmon] at hcs
  have hg2 : ∫ t in (0 : ℝ)..Real.pi, Real.sin (((k + 1 : ℕ) : ℝ) * t) ^ 2 = Real.pi / 2 := by
    simp_rw [sq]
    simpa using integral_sin_mul_sin (k + 1) (k + 1) (Nat.succ_pos k) (Nat.succ_pos k)
  rw [hg2] at hcs
  have hsin2 : Real.pi / (2 * (4 : ℝ) ^ k) ≤
      ∫ t in (0 : ℝ)..Real.pi, (q.eval (Real.cos t) * Real.sin t) ^ 2 := by
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have h4 : ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k := by
      rw [← pow_mul, mul_comm k 2, pow_mul]; norm_num
    have h1 : (Real.pi / (2 * (2 : ℝ) ^ k)) ^ 2 =
        (Real.pi / (2 * (4 : ℝ) ^ k)) * (Real.pi / 2) := by
      rw [div_pow, mul_pow, h4]
      ring
    rw [h1] at hcs
    exact le_of_mul_le_mul_right hcs (by positivity)
  have hle_sin : ∫ t in (0 : ℝ)..Real.pi, (q.eval (Real.cos t) * Real.sin t) ^ 2 ≤
      ∫ t in (0 : ℝ)..Real.pi, (q.eval (Real.cos t)) ^ 2 * Real.sin t := by
    refine intervalIntegral.integral_mono_on Real.pi_pos.le
      (((hc_qcos.mul Real.continuous_sin).pow 2).intervalIntegrable _ _)
      (((hc_qcos.pow 2).mul Real.continuous_sin).intervalIntegrable _ _) fun t ht => ?_
    have hsnn : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2
    have hsle : Real.sin t ≤ 1 := Real.sin_le_one t
    have hqnn : 0 ≤ (q.eval (Real.cos t)) ^ 2 := sq_nonneg _
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (by nlinarith) hqnn
  have hsubst : ∫ t in (0 : ℝ)..Real.pi, (q.eval (Real.cos t)) ^ 2 * Real.sin t =
      ∫ u in (-1 : ℝ)..1, (q.eval u) ^ 2 := by
    have hcomp := intervalIntegral.integral_comp_mul_deriv
      (a := (0 : ℝ)) (b := Real.pi)
      (f := Real.cos) (f' := fun t => -Real.sin t)
      (g := fun u => (q.eval u) ^ 2)
      (fun t _ => Real.hasDerivAt_cos t)
      (by fun_prop) ((continuous_poly_eval q).pow 2)
    rw [Real.cos_zero, Real.cos_pi, intervalIntegral.integral_symm (-1 : ℝ) 1] at hcomp
    dsimp only [Function.comp_apply] at hcomp
    have hneg : ∫ t in (0 : ℝ)..Real.pi, (q.eval (Real.cos t)) ^ 2 * (-Real.sin t) =
        -(∫ t in (0 : ℝ)..Real.pi, (q.eval (Real.cos t)) ^ 2 * Real.sin t) := by
      simp_rw [mul_neg, intervalIntegral.integral_neg]
    linarith
  linarith

private lemma monic_L2_lower_interval {a b : ℝ} (hab : a < b) (k : ℕ) (q : Polynomial ℝ)
    (hdeg : q.natDegree = k) (hmon : q.leadingCoeff = 1) :
    (Real.pi * (b - a) / 4) * ((b - a) / 4) ^ (2 * k) ≤
      ∫ x in a..b, (q.eval x) ^ 2 := by
  set L : ℝ := b - a
  set mid : ℝ := (a + b) / 2
  have hL_pos : 0 < L := sub_pos.mpr hab
  have hcomp := intervalIntegral.integral_comp_mul_deriv
    (a := (-1 : ℝ)) (b := 1)
    (f := fun u => mid + (L / 2) * u) (f' := fun _ => L / 2)
    (g := fun x => (q.eval x) ^ 2)
    (fun u _ => by
      have h1 : HasDerivAt (fun x : ℝ => (L / 2) * x) (L / 2) u := by
        simpa using (hasDerivAt_id u).const_mul (L / 2)
      simpa using h1.const_add mid)
    (by fun_prop) ((continuous_poly_eval q).pow 2)
  have hfa : mid + (L / 2) * (-1) = a := by dsimp [mid, L]; ring
  have hfb : mid + (L / 2) * 1 = b := by dsimp [mid, L]; ring
  dsimp only [Function.comp_apply] at hcomp
  simp_rw [mul_comm _ (L / 2)] at hcomp
  rw [hfa, hfb, intervalIntegral.integral_const_mul] at hcomp
  set aff : Polynomial ℝ := Polynomial.C (L / 2) * Polynomial.X + Polynomial.C mid
  set qtilde : Polynomial ℝ := Polynomial.C ((2 / L) ^ k) * q.comp aff
  have haff_deg : aff.natDegree = 1 := by
    dsimp [aff]
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · rw [Polynomial.natDegree_C_mul (by positivity), Polynomial.natDegree_X]
    · rw [Polynomial.natDegree_C, Polynomial.natDegree_C_mul (by positivity), Polynomial.natDegree_X]
      norm_num
  have haff_lc : aff.leadingCoeff = L / 2 := by
    dsimp [aff]
    rw [add_comm, Polynomial.leadingCoeff_add_of_degree_lt]
    · rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_X, mul_one]
    · apply Polynomial.degree_lt_degree
      rw [Polynomial.natDegree_C, Polynomial.natDegree_C_mul (by positivity), Polynomial.natDegree_X]
      norm_num
  have hqt_deg : qtilde.natDegree = k := by
    dsimp [qtilde]
    rw [Polynomial.natDegree_C_mul (by positivity), Polynomial.natDegree_comp, hdeg, haff_deg, mul_one]
  have hqt_mon : qtilde.leadingCoeff = 1 := by
    dsimp [qtilde]
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_comp (by rw [haff_deg]; norm_num),
      hmon, haff_lc, hdeg, one_mul, ← mul_pow]
    have h1 : (2 / L) * (L / 2) = 1 := by field_simp [hL_pos.ne']
    rw [h1, one_pow]
  have heval : ∀ u : ℝ, (q.eval (mid + (L / 2) * u)) ^ 2 =
      (L / 2) ^ (2 * k) * (qtilde.eval u) ^ 2 := by
    intro u
    have h1 : qtilde.eval u = (2 / L) ^ k * q.eval (mid + (L / 2) * u) := by
      simp [qtilde, aff, add_comm]
    rw [h1, mul_pow, ← mul_assoc, ← pow_mul, mul_comm k 2, ← mul_pow]
    have h2 : (L / 2) * (2 / L) = 1 := by field_simp [hL_pos.ne']
    rw [h2, one_pow, one_mul]
  simp_rw [heval] at hcomp
  rw [intervalIntegral.integral_const_mul] at hcomp
  have hunit := monic_L2_lower_unit k qtilde hqt_deg hqt_mon
  rw [← hcomp]
  have hcoef : (L / 2) * ((L / 2) ^ (2 * k) * (Real.pi / (2 * (4 : ℝ) ^ k))) =
      (Real.pi * L / 4) * (L / 4) ^ (2 * k) := by
    have h4 : (4 : ℝ) ^ k = (2 : ℝ) ^ (2 * k) := by
      rw [pow_mul]; norm_num
    rw [h4]
    have hdiv : (L / 2) ^ (2 * k) / (2 : ℝ) ^ (2 * k) = (L / 4) ^ (2 * k) := by
      rw [← div_pow]; congr 1; ring
    calc
      (L / 2) * ((L / 2) ^ (2 * k) * (Real.pi / (2 * (2 : ℝ) ^ (2 * k))))
        = (Real.pi * L / 4) * ((L / 2) ^ (2 * k) / (2 : ℝ) ^ (2 * k)) := by ring
      _ = (Real.pi * L / 4) * (L / 4) ^ (2 * k) := by rw [hdiv]
  rw [← hcoef]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hunit (by positivity)) (by positivity)

/-! ### Section 5: 1D Change of Variables Lower Bound for exp2D -/

private lemma intervalIntegral_mono_subinterval {f : ℝ → ℝ} (hf : Continuous f)
    (hnn : ∀ x, 0 ≤ f x) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ x in b..c, f x ≤ ∫ x in a..d, f x := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume) (a := a) (b := b) (c := c)
    (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume) (a := a) (b := c) (c := d)
    (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
  have hn1 : 0 ≤ ∫ x in a..b, f x := intervalIntegral.integral_nonneg hab fun x _ => hnn x
  have hn2 : 0 ≤ ∫ x in c..d, f x := intervalIntegral.integral_nonneg hcd fun x _ => hnn x
  linarith

private lemma exp2D_swap_rect {α β : ℝ} (hα_pos : 0 < α) (hα_lt_β : α < β)
    {h : ℝ → ℝ} (hh : Continuous h) :
    ∫ φ in α..β, (∫ θ in (-α)..α, h (kern φ θ)) =
    ∫ θ in (-α)..α, (∫ φ in α..β, h (kern φ θ)) := by
  have hI : MeasureTheory.IntegrableOn (Function.uncurry (fun φ θ => h (kern φ θ)))
      (Set.Ioc α β ×ˢ Set.Ioc (-α) α) (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have hK : IsCompact (Set.Icc α β ×ˢ Set.Icc (-α) α) := isCompact_Icc.prod isCompact_Icc
    exact (ContinuousOn.integrableOn_compact hK (hh.comp continuous_kern).continuousOn).mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  have h1 := intervalIntegral.integral_of_le (μ := MeasureTheory.volume) hα_lt_β.le
    (f := fun φ => ∫ θ in (-α)..α, h (kern φ θ))
  have h2 : ∀ φ, ∫ θ in (-α)..α, h (kern φ θ) =
      ∫ θ in Set.Ioc (-α) α, h (kern φ θ) := fun φ =>
    intervalIntegral.integral_of_le (μ := MeasureTheory.volume) (by linarith)
  have h3 := intervalIntegral.integral_of_le (μ := MeasureTheory.volume) (show -α ≤ α by linarith)
    (f := fun θ => ∫ φ in α..β, h (kern φ θ))
  have h4 : ∀ θ, ∫ φ in α..β, h (kern φ θ) =
      ∫ φ in Set.Ioc α β, h (kern φ θ) := fun θ =>
    intervalIntegral.integral_of_le (μ := MeasureTheory.volume) hα_lt_β.le
  rw [h1, h3]
  simp_rw [h2, h4]
  have hI' : MeasureTheory.Integrable (Function.uncurry (fun φ θ => h (kern φ θ)))
      ((MeasureTheory.volume.restrict (Set.Ioc α β)).prod
        (MeasureTheory.volume.restrict (Set.Ioc (-α) α))) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hI
  exact MeasureTheory.integral_integral_swap hI'

private lemma exp2D_step4_lower {ε δ α β : ℝ}
    (hδ0 : 0 < δ) (hδ_lt : δ < 1 / 8) (hε_eq : ε = 8 * δ)
    (hα_cos : Real.cos α = 1 - δ) (hβ_cos : Real.cos β = -1 / 2 + δ)
    (hα_pos : 0 < α) (hα_lt_β : α < β) (hβ_lt_pi : β < Real.pi)
    {h : ℝ → ℝ} (hh : Continuous h) (hnn : ∀ x, 0 ≤ h x)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (-α) α) :
    (1 / 12 : ℝ) * ∫ x in (2 * ε)..(9 - 2 * ε), h x ≤ ∫ φ in α..β, h (kern φ θ) := by
  have hα_lt_pi : α < Real.pi := lt_trans hα_lt_β hβ_lt_pi
  have hcosθ_ge : 1 - δ ≤ Real.cos θ := by
    have habsθ : |θ| ≤ α := abs_le.mpr hθ
    have hcos_abs : Real.cos θ = Real.cos |θ| := by
      cases le_or_gt 0 θ with
      | inl h0 => rw [abs_of_nonneg h0]
      | inr h0 => rw [abs_of_neg h0, Real.cos_neg]
    rw [hcos_abs, ← hα_cos]
    exact Real.strictAntiOn_cos.antitoneOn ⟨abs_nonneg θ, le_trans habsθ hα_lt_pi.le⟩
      ⟨hα_pos.le, hα_lt_pi.le⟩ habsθ
  have hcosθ_le : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hderiv : ∀ φ ∈ Set.uIcc α β,
      HasDerivAt (fun t : ℝ => kern t θ)
        (-4 * Real.sin φ * (2 * Real.cos φ + Real.cos θ)) φ := by
    intro φ _
    have hcos : HasDerivAt (fun t : ℝ => Real.cos t) (-Real.sin φ) φ := Real.hasDerivAt_cos φ
    have hsq : HasDerivAt (fun t : ℝ => Real.cos t ^ 2)
        (↑(2 : ℕ) * Real.cos φ ^ (2 - 1) * (-Real.sin φ)) φ := hcos.pow 2
    have h2 := (hsq.const_mul 4).const_add 1
    have h3 := (hcos.const_mul 4).mul_const (Real.cos θ)
    have h4 := h2.add h3
    have heq : 4 * (↑(2 : ℕ) * Real.cos φ ^ (2 - 1) * (-Real.sin φ)) +
        4 * (-Real.sin φ) * Real.cos θ =
        -4 * Real.sin φ * (2 * Real.cos φ + Real.cos θ) := by norm_num; ring
    rw [heq] at h4
    exact h4
  have hcomp := intervalIntegral.integral_comp_mul_deriv
    (a := α) (b := β)
    (f := fun t : ℝ => kern t θ)
    (f' := fun t : ℝ => -4 * Real.sin t * (2 * Real.cos t + Real.cos θ))
    (g := h) hderiv (by fun_prop) hh
  dsimp only [Function.comp_apply] at hcomp
  have hsubst : ∫ φ in α..β, (4 * Real.sin φ * (2 * Real.cos φ + Real.cos θ)) * h (kern φ θ) =
      ∫ x in (kern β θ)..(kern α θ), h x := by
    rw [intervalIntegral.integral_symm (kern α θ) (kern β θ), ← hcomp,
      ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun φ _ => ?_
    ring
  have hc_hk : Continuous (fun φ : ℝ => h (kern φ θ)) :=
    hh.comp (by unfold kern; fun_prop)
  have hle12 :
      ∫ φ in α..β, (4 * Real.sin φ * (2 * Real.cos φ + Real.cos θ)) * h (kern φ θ) ≤
      12 * ∫ φ in α..β, h (kern φ θ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hα_lt_β.le
      (((by fun_prop : Continuous (fun φ : ℝ => 4 * Real.sin φ * (2 * Real.cos φ + Real.cos θ))).mul
        hc_hk).intervalIntegrable _ _)
      ((continuous_const.mul hc_hk).intervalIntegrable _ _) fun φ hφ => ?_
    have hφ0 : 0 ≤ φ := le_trans hα_pos.le hφ.1
    have hφpi : φ ≤ Real.pi := le_trans hφ.2 hβ_lt_pi.le
    have hsin_nn : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi hφ0 hφpi
    have hsin_le : Real.sin φ ≤ 1 := Real.sin_le_one φ
    have hcosφ_le : Real.cos φ ≤ 1 := Real.cos_le_one φ
    have hcosφ_ge : -1 / 2 + δ ≤ Real.cos φ := by
      rw [← hβ_cos]
      exact Real.strictAntiOn_cos.antitoneOn ⟨hφ0, hφpi⟩
        ⟨(lt_trans hα_pos hα_lt_β).le, hβ_lt_pi.le⟩ hφ.2
    have hfac_le : 4 * Real.sin φ * (2 * Real.cos φ + Real.cos θ) ≤ 12 := by
      have hsum_nn : 0 ≤ 2 * Real.cos φ + Real.cos θ := by linarith
      have hsum_le : 2 * Real.cos φ + Real.cos θ ≤ 3 := by linarith
      have h1 : Real.sin φ * (2 * Real.cos φ + Real.cos θ) ≤ 1 * 3 :=
        mul_le_mul hsin_le hsum_le hsum_nn zero_le_one
      linarith
    exact mul_le_mul_of_nonneg_right hfac_le (hnn _)
  have hα_ge : 9 - 2 * ε ≤ kern α θ := by
    unfold kern
    rw [hα_cos]
    have h1 : 4 * (1 - δ) * (1 - δ) ≤ 4 * (1 - δ) * Real.cos θ :=
      mul_le_mul_of_nonneg_left hcosθ_ge (by linarith)
    have hsq : 0 ≤ δ ^ 2 := sq_nonneg δ
    linarith
  have hβ_le : kern β θ ≤ 2 * ε := by
    unfold kern
    rw [hβ_cos]
    have h1 : 4 * (-1 / 2 + δ) * Real.cos θ ≤ 4 * (-1 / 2 + δ) * (1 - δ) :=
      mul_le_mul_of_nonpos_left hcosθ_ge (by linarith)
    have halg : 1 + 4 * (-1 / 2 + δ) ^ 2 + 4 * (-1 / 2 + δ) * (1 - δ) = 2 * δ := by ring
    linarith
  have hsubint : ∫ x in (2 * ε)..(9 - 2 * ε), h x ≤ ∫ x in (kern β θ)..(kern α θ), h x :=
    intervalIntegral_mono_subinterval hh hnn hβ_le hα_ge
  linarith

private lemma exp2D_lower_bound_aux {ε δ α β : ℝ}
    (hδ0 : 0 < δ) (hδ_lt : δ < 1 / 8) (hε_eq : ε = 8 * δ)
    (hα_cos : Real.cos α = 1 - δ) (hβ_cos : Real.cos β = -1 / 2 + δ)
    (hα_pos : 0 < α) (hα_lt_β : α < β) (hβ_lt_pi : β < Real.pi)
    {h : ℝ → ℝ} (hh : Continuous h) (hnn : ∀ x, 0 ≤ h x) :
    δ * α / (6 * Real.pi ^ 2) * ∫ x in (2 * ε)..(9 - 2 * ε), h x ≤ exp2D h := by
  have hα_lt_pi : α < Real.pi := lt_trans hα_lt_β hβ_lt_pi
  have houter_nn : ∀ φ : ℝ,
      0 ≤ (∫ θ in (-Real.pi)..Real.pi, h (kern φ θ)) * Real.sin φ ^ 2 := fun φ =>
    mul_nonneg (intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) fun θ _ => hnn _)
      (sq_nonneg _)
  have houter_cont : Continuous (fun φ : ℝ =>
      (∫ θ in (-Real.pi)..Real.pi, h (kern φ θ)) * Real.sin φ ^ 2) :=
    (continuous_inner_kern hh (-Real.pi) Real.pi).mul (by fun_prop)
  have hstep1 :
      ∫ φ in α..β, (∫ θ in (-Real.pi)..Real.pi, h (kern φ θ)) * Real.sin φ ^ 2 ≤
      ∫ φ in (0 : ℝ)..Real.pi, (∫ θ in (-Real.pi)..Real.pi, h (kern φ θ)) * Real.sin φ ^ 2 :=
    intervalIntegral_mono_subinterval houter_cont houter_nn hα_pos.le hβ_lt_pi.le
  have hinner_cont_α : Continuous (fun φ : ℝ => ∫ θ in (-α)..α, h (kern φ θ)) :=
    continuous_inner_kern hh (-α) α
  have hstep2 :
      δ * ∫ φ in α..β, (∫ θ in (-α)..α, h (kern φ θ)) ≤
      ∫ φ in α..β, (∫ θ in (-Real.pi)..Real.pi, h (kern φ θ)) * Real.sin φ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hα_lt_β.le
      ((continuous_const.mul hinner_cont_α).intervalIntegrable _ _)
      (houter_cont.intervalIntegrable _ _) fun φ hφ => ?_
    have hφ0 : 0 ≤ φ := le_trans hα_pos.le hφ.1
    have hφpi : φ ≤ Real.pi := le_trans hφ.2 hβ_lt_pi.le
    have hcos_le : Real.cos φ ≤ 1 - δ := by
      rw [← hα_cos]
      exact Real.strictAntiOn_cos.antitoneOn ⟨hα_pos.le, hα_lt_pi.le⟩ ⟨hφ0, hφpi⟩ hφ.1
    have hcos_ge : -1 / 2 + δ ≤ Real.cos φ := by
      rw [← hβ_cos]
      exact Real.strictAntiOn_cos.antitoneOn ⟨hφ0, hφpi⟩ ⟨(lt_trans hα_pos hα_lt_β).le, hβ_lt_pi.le⟩ hφ.2
    have hsin2 : δ ≤ Real.sin φ ^ 2 := by
      have hcs := Real.sin_sq_add_cos_sq φ
      have hprod : (Real.cos φ - (1 - δ)) * (Real.cos φ + (1 - δ)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      have hsq : Real.cos φ ^ 2 ≤ (1 - δ) ^ 2 := by linarith
      have hd2 : (1 - δ) ^ 2 ≤ 1 - δ := by
        have : δ * (δ - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hδ0.le (by linarith)
        linarith
      linarith
    have hcθ : Continuous (fun θ : ℝ => h (kern φ θ)) :=
      hh.comp (by unfold kern; fun_prop)
    have hθ_sub : ∫ θ in (-α)..α, h (kern φ θ) ≤ ∫ θ in (-Real.pi)..Real.pi, h (kern φ θ) :=
      intervalIntegral_mono_subinterval hcθ (fun θ => hnn _) (by linarith) hα_lt_pi.le
    have hθ_nn : 0 ≤ ∫ θ in (-α)..α, h (kern φ θ) :=
      intervalIntegral.integral_nonneg (by linarith) fun θ _ => hnn _
    calc
      δ * ∫ θ in (-α)..α, h (kern φ θ)
        ≤ Real.sin φ ^ 2 * ∫ θ in (-α)..α, h (kern φ θ) :=
          mul_le_mul_of_nonneg_right hsin2 hθ_nn
      _ ≤ Real.sin φ ^ 2 * ∫ θ in (-Real.pi)..Real.pi, h (kern φ θ) :=
          mul_le_mul_of_nonneg_left hθ_sub (sq_nonneg _)
      _ = (∫ θ in (-Real.pi)..Real.pi, h (kern φ θ)) * Real.sin φ ^ 2 := mul_comm _ _
  have hswap := exp2D_swap_rect hα_pos hα_lt_β hh
  have hstep4 : ∀ θ ∈ Set.Icc (-α) α,
      (1 / 12 : ℝ) * ∫ x in (2 * ε)..(9 - 2 * ε), h x ≤ ∫ φ in α..β, h (kern φ θ) :=
    fun _ hθ => exp2D_step4_lower hδ0 hδ_lt hε_eq hα_cos hβ_cos hα_pos hα_lt_β hβ_lt_pi hh hnn hθ
  have hφ_cont : Continuous (fun θ : ℝ => ∫ φ in α..β, h (kern φ θ)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun θ φ => h (kern φ θ))
      (by show Continuous (fun p : ℝ × ℝ => h (kern p.2 p.1)); exact hh.comp (by unfold kern; fun_prop)) α β
  have hstep5 :
      (2 * α) * ((1 / 12 : ℝ) * ∫ x in (2 * ε)..(9 - 2 * ε), h x) ≤
      ∫ θ in (-α)..α, (∫ φ in α..β, h (kern φ θ)) := by
    have hconst : ∫ _θ in (-α)..α, ((1 / 12 : ℝ) * ∫ x in (2 * ε)..(9 - 2 * ε), h x) =
        (2 * α) * ((1 / 12 : ℝ) * ∫ x in (2 * ε)..(9 - 2 * ε), h x) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [← hconst]
    exact intervalIntegral.integral_mono_on (by linarith)
      (continuous_const.intervalIntegrable _ _) (hφ_cont.intervalIntegrable _ _) hstep4
  unfold exp2D
  have hpi2 : 0 < (1 : ℝ) / Real.pi ^ 2 := by positivity
  have hcomb : δ * ((2 * α) * ((1 / 12 : ℝ) * ∫ x in (2 * ε)..(9 - 2 * ε), h x)) ≤
      ∫ φ in (0 : ℝ)..Real.pi, (∫ θ in (-Real.pi)..Real.pi, h (kern φ θ)) * Real.sin φ ^ 2 := by
    calc
      δ * ((2 * α) * ((1 / 12 : ℝ) * ∫ x in (2 * ε)..(9 - 2 * ε), h x))
        ≤ δ * ∫ θ in (-α)..α, (∫ φ in α..β, h (kern φ θ)) :=
          mul_le_mul_of_nonneg_left hstep5 hδ0.le
      _ = δ * ∫ φ in α..β, (∫ θ in (-α)..α, h (kern φ θ)) := by rw [hswap]
      _ ≤ ∫ φ in α..β, (∫ θ in (-Real.pi)..Real.pi, h (kern φ θ)) * Real.sin φ ^ 2 := hstep2
      _ ≤ ∫ φ in (0 : ℝ)..Real.pi,
            (∫ θ in (-Real.pi)..Real.pi, h (kern φ θ)) * Real.sin φ ^ 2 := hstep1
  have hmul := mul_le_mul_of_nonneg_left hcomb hpi2.le
  calc
    δ * α / (6 * Real.pi ^ 2) * ∫ x in (2 * ε)..(9 - 2 * ε), h x
      = (1 / Real.pi ^ 2) * (δ * ((2 * α) * ((1 / 12 : ℝ) * ∫ x in (2 * ε)..(9 - 2 * ε), h x))) := by
        ring
    _ ≤ (1 / Real.pi ^ 2) *
          ∫ φ in (0 : ℝ)..Real.pi, (∫ θ in (-Real.pi)..Real.pi, h (kern φ θ)) * Real.sin φ ^ 2 := hmul

private lemma exp2D_lower_bound {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C > 0, ∀ h : ℝ → ℝ, Continuous h → (∀ x, 0 ≤ h x) →
      C * ∫ x in (2 * ε)..(9 - 2 * ε), h x ≤ exp2D h := by
  let δ : ℝ := ε / 8
  have hδ0 : 0 < δ := by dsimp [δ]; linarith
  have hδ_lt : δ < 1 / 8 := by dsimp [δ]; linarith
  have hε_eq : ε = 8 * δ := by dsimp [δ]; ring
  let α : ℝ := Real.arccos (1 - δ)
  let β : ℝ := Real.arccos (-1 / 2 + δ)
  have hα_cos : Real.cos α = 1 - δ := Real.cos_arccos (by linarith) (by linarith)
  have hβ_cos : Real.cos β = -1 / 2 + δ := Real.cos_arccos (by linarith) (by linarith)
  have hα_pos : 0 < α := by dsimp [α]; rw [Real.arccos_pos]; linarith
  have hα_lt_β : α < β := Real.arccos_lt_arccos (by linarith) (by linarith) (by linarith)
  have hβ_lt_pi : β < Real.pi := by dsimp [β]; rw [Real.arccos_lt_pi]; linarith
  exact ⟨δ * α / (6 * Real.pi ^ 2), by positivity, fun h hh hnn =>
    exp2D_lower_bound_aux hδ0 hδ_lt hε_eq hα_cos hβ_cos hα_pos hα_lt_β hβ_lt_pi hh hnn⟩

private lemma a_seq_lower_bound {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ K > 0, ∀ n : ℕ,
      K ^ (n + 1) * ((9 : ℝ) / 4 - ε) ^ (n * (n + 1)) ≤ (a_seq n : ℝ) := by
  obtain ⟨C, hC_pos, hC⟩ := exp2D_lower_bound hε0 hε1
  set L : ℝ := 9 - 4 * ε
  have hL_pos : 0 < L := by dsimp [L]; linarith
  have hab : 2 * ε < 9 - 2 * ε := by linarith
  have hL_eq : (9 - 2 * ε) - 2 * ε = L := by dsimp [L]; ring
  have hL4 : L / 4 = (9 : ℝ) / 4 - ε := by dsimp [L]; ring
  set K : ℝ := C * (Real.pi * L / 4)
  have hK_pos : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK_pos, fun n => ?_⟩
  rw [← Hmat_det_eq n]
  let c : ℕ → ℝ := fun k => K * ((9 : ℝ) / 4 - ε) ^ (2 * k)
  have hc_pos : ∀ k, 0 < c k := fun k => by
    dsimp [c]
    have : 0 < (9 : ℝ) / 4 - ε := by linarith
    positivity
  have hc : ∀ k (q : Polynomial ℝ), q.natDegree = k → q.leadingCoeff = 1 →
      c k ≤ exp2D (fun x => (q.eval x) ^ 2) := by
    intro k q hdeg hmon
    have h1 := monic_L2_lower_interval hab k q hdeg hmon
    rw [hL_eq, hL4] at h1
    have h2 := hC (fun x => (q.eval x) ^ 2) ((continuous_poly_eval q).pow 2) (fun x => sq_nonneg _)
    calc
      c k = C * ((Real.pi * L / 4) * ((9 : ℝ) / 4 - ε) ^ (2 * k)) := by dsimp [c, K]; ring
      _ ≤ C * ∫ x in (2 * ε)..(9 - 2 * ε), (q.eval x) ^ 2 :=
        mul_le_mul_of_nonneg_left h1 hC_pos.le
      _ ≤ exp2D (fun x => (q.eval x) ^ 2) := h2
  have hprod : ∏ k ∈ Finset.range (n + 1), c k =
      K ^ (n + 1) * ((9 : ℝ) / 4 - ε) ^ (n * (n + 1)) := by
    dsimp [c]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    congr 1
    have hsum : ∑ k ∈ Finset.range (n + 1), 2 * k = n * (n + 1) := by
      rw [← Finset.mul_sum]
      have := Finset.sum_range_id_mul_two (n + 1)
      simpa [mul_comm] using this
    rw [← hsum]
    clear * -
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.prod_range_succ, Finset.sum_range_succ, pow_add, ih]
  rw [← hprod]
  exact prod_le_Hmat_det c hc_pos hc n

/-! ### Section 6: Positivity and Limit Theorems -/

theorem part2_pos (n : ℕ) : 0 < a_seq n := by
  obtain ⟨K, hK_pos, hK⟩ := a_seq_lower_bound (ε := 1 / 2) (by norm_num) (by norm_num)
  have hposR : (0 : ℝ) < (a_seq n : ℝ) := by
    have h1 := hK n
    have h2 : (0 : ℝ) < K ^ (n + 1) * ((9 : ℝ) / 4 - 1 / 2) ^ (n * (n + 1)) := by positivity
    linarith
  exact_mod_cast hposR

private lemma tendsto_bound_rpow {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Tendsto (fun n : ℕ => (A ^ (n + 1) * B ^ (n * (n + 1))) ^ ((1 : ℝ) / (n : ℝ) ^ 2))
      atTop (𝓝 B) := by
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ) ^ 2) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have hinv2 : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 0) := by
      have := hinv.mul hinv
      simpa [sq, one_div] using this
    have hsum : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ) + (1 : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (0 + 0)) :=
      hinv.add hinv2
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := by positivity
    field_simp [hnR]
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ) * ((n : ℝ) + 1)) / (n : ℝ) ^ 2) atTop (𝓝 1) := by
    have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have hsum : Tendsto (fun n : ℕ => (1 : ℝ) + (1 : ℝ) / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hinv
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := by positivity
    field_simp [hnR]
  have hA_lim : Tendsto (fun n : ℕ => A ^ (((n : ℝ) + 1) / (n : ℝ) ^ 2)) atTop (𝓝 (A ^ (0 : ℝ))) :=
    (ContinuousAt.tendsto (Real.continuousAt_const_rpow hA.ne')).comp h1
  have hB_lim : Tendsto (fun n : ℕ => B ^ (((n : ℝ) * ((n : ℝ) + 1)) / (n : ℝ) ^ 2)) atTop (𝓝 (B ^ (1 : ℝ))) :=
    (ContinuousAt.tendsto (Real.continuousAt_const_rpow hB.ne')).comp h2
  have hprod := hA_lim.mul hB_lim
  rw [Real.rpow_zero, Real.rpow_one, one_mul] at hprod
  refine hprod.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast A (n + 1), ← Real.rpow_natCast B (n * (n + 1)),
    ← Real.rpow_mul hA.le, ← Real.rpow_mul hB.le]
  push_cast
  simp [div_eq_mul_inv]

theorem part2_limit :
    Tendsto (fun n : ℕ => (a_seq n : ℝ) ^ ((1 : ℝ) / (n : ℝ) ^ 2)) atTop (𝓝 (9 / 4)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set ε : ℝ := min (δ / 2) (1 / 2)
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨K, hK_pos, hK⟩ := a_seq_lower_bound hε0 hε1
  have hup := tendsto_bound_rpow (A := 4) (B := (9 : ℝ) / 4) (by norm_num) (by norm_num)
  have hlo := tendsto_bound_rpow (A := K) (B := (9 : ℝ) / 4 - ε) hK_pos (by linarith)
  have hev_up : ∀ᶠ n : ℕ in atTop,
      (4 ^ (n + 1) * ((9 : ℝ) / 4) ^ (n * (n + 1))) ^ ((1 : ℝ) / (n : ℝ) ^ 2) <
        (9 : ℝ) / 4 + δ :=
    hup.eventually (Iio_mem_nhds (by linarith))
  have hev_lo : ∀ᶠ n : ℕ in atTop,
      (9 : ℝ) / 4 - δ <
        (K ^ (n + 1) * ((9 : ℝ) / 4 - ε) ^ (n * (n + 1))) ^ ((1 : ℝ) / (n : ℝ) ^ 2) :=
    hlo.eventually (Ioi_mem_nhds (by linarith))
  have hev := (hev_up.and hev_lo).and (Filter.eventually_ge_atTop 1)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨⟨h1, h2⟩, hn1⟩ := hN n hn
  have hpos : (0 : ℝ) < (a_seq n : ℝ) := by exact_mod_cast part2_pos n
  have hexp_nn : 0 ≤ (1 : ℝ) / (n : ℝ) ^ 2 := by positivity
  have hle_up : (a_seq n : ℝ) ^ ((1 : ℝ) / (n : ℝ) ^ 2) ≤
      (4 ^ (n + 1) * ((9 : ℝ) / 4) ^ (n * (n + 1))) ^ ((1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.rpow_le_rpow hpos.le (a_seq_upper_bound n) hexp_nn
  have hge_lo : (K ^ (n + 1) * ((9 : ℝ) / 4 - ε) ^ (n * (n + 1))) ^ ((1 : ℝ) / (n : ℝ) ^ 2) ≤
      (a_seq n : ℝ) ^ ((1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.rpow_le_rpow (by
      have : (0 : ℝ) < (9 : ℝ) / 4 - ε := by linarith
      positivity) (hK n) hexp_nn
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end OMA_A228456_Part2

theorem OMA.solution : type_of% @OMA.S_oeis_a228456.main :=
  ⟨fun n =>
    ⟨OMA_A228456_Part2.part2_pos n,
     (OMA_A228456_Part1.part1_main n).1,
     (OMA_A228456_Part1.part1_main n).2⟩,
   OMA_A228456_Part2.part2_limit⟩
