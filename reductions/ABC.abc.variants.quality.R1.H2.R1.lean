import OMAReductions.R_ABC_abc_variants_quality_R1
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Order.Interval.Finset.Nat

/-!
Write R for the radical of abc, C for the radical of c, and B for the
radical of ab. The factors C and B have product R. For an exceptional
triple, the product of the weighted squares C² R^ε and B² R^ε is
less than c². This gives a split by the deficit of C. If C² ≥ c,
the stronger bound B² R^(2ε) < c holds. A prime cube must divide c
in the first two cases and ab in the third. An elementary height bound
first removes all triples with abc ≤ K R² for any fixed K.
-/

namespace OMA.R_ABC_abc_variants_quality_R1_H2_R1

/-- The square of the sum radical is small even after weighting. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℕ,
    {(a, b, c) : ℕ × ℕ × ℕ |
      0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
      a + b = c ∧ ¬ Squarefree c ∧ ¬ Squarefree (a * b) ∧
      (ABC.radical (a * b * c) : ℝ) ^ (1 + ε) < (c : ℝ) ∧
      K * ABC.radical (a * b * c) ^ 2 < a * b * c ∧
      (ABC.radical c : ℝ)^2 * (ABC.radical (a * b * c) : ℝ)^ε < (c : ℝ) ∧
      (∃ p : ℕ, p.Prime ∧ p ^ 3 ∣ c)}.Finite

/-- The square of the sum radical is small, but the weighted square is large. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℕ,
    {(a, b, c) : ℕ × ℕ × ℕ |
      0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
      a + b = c ∧ ¬ Squarefree c ∧ ¬ Squarefree (a * b) ∧
      (ABC.radical (a * b * c) : ℝ) ^ (1 + ε) < (c : ℝ) ∧
      K * ABC.radical (a * b * c) ^ 2 < a * b * c ∧
      ABC.radical c ^ 2 < c ∧
      (c : ℝ) ≤ (ABC.radical c : ℝ)^2 * (ABC.radical (a * b * c) : ℝ)^ε ∧
      (ABC.radical (a * b) : ℝ)^2 * (ABC.radical (a * b * c) : ℝ)^ε < (c : ℝ) ∧
      (∃ p : ℕ, p.Prime ∧ p ^ 3 ∣ c)}.Finite

/-- The square of the sum radical is at least the sum. -/
def H3 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℕ,
    {(a, b, c) : ℕ × ℕ × ℕ |
      0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
      a + b = c ∧ ¬ Squarefree c ∧ ¬ Squarefree (a * b) ∧
      (ABC.radical (a * b * c) : ℝ) ^ (1 + ε) < (c : ℝ) ∧
      K * ABC.radical (a * b * c) ^ 2 < a * b * c ∧
      c ≤ ABC.radical c ^ 2 ∧ ABC.radical (a * b) ^ 2 < a * b ∧
      (ABC.radical (a * b) : ℝ)^2 * (ABC.radical (a * b * c) : ℝ)^(2 * ε) < (c : ℝ) ∧
      (∃ p : ℕ, p.Prime ∧ p ^ 3 ∣ a * b)}.Finite

section Proof

open scoped BigOperators

private lemma radical_pos (n : ℕ) : 0 < ABC.radical n :=
  Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos

private lemma radical_mul {m n : ℕ} (h : m.Coprime n) :
    ABC.radical (m * n) = ABC.radical m * ABC.radical n := by
  unfold ABC.radical
  rw [h.primeFactors_mul, Finset.prod_union h.disjoint_primeFactors]

private lemma coprime_product_sum {a b c : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hp : ({a, b, c} : Set ℕ).Pairwise Nat.Coprime) (hs : a + b = c) :
    (a * b).Coprime c := by
  have hac : a.Coprime c := hp (by simp) (by simp) (by omega)
  have hbc : b.Coprime c := hp (by simp) (by simp) (by omega)
  exact hac.mul_left hbc

private lemma product_ge_sum_sub_one {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    a + b - 1 ≤ a * b := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  rw [Nat.succ_mul, Nat.mul_succ]
  omega

/-- When both squared radicals dominate their integers, the total radical
already dominates c. -/
lemma sum_le_radical_of_square_bounds {a b c : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hp : ({a, b, c} : Set ℕ).Pairwise Nat.Coprime) (hs : a + b = c)
    (hc : c ≤ ABC.radical c ^ 2) (hab : a * b ≤ ABC.radical (a * b) ^ 2) :
    c ≤ ABC.radical (a * b * c) := by
  have hprod : c - 1 ≤ a * b := hs ▸ product_ge_sum_sub_one ha hb
  have hbound : (c - 1) * c ≤ ABC.radical (a * b * c) ^ 2 := by
    calc
      (c - 1) * c ≤ a * b * c := Nat.mul_le_mul_right c hprod
      _ ≤ ABC.radical (a * b)^2 * ABC.radical c^2 := Nat.mul_le_mul hab hc
      _ = _ := by rw [radical_mul (coprime_product_sum ha hb hp hs), mul_pow]
  by_contra! h
  have hle : ABC.radical (a * b * c) ≤ c - 1 := by omega
  have hlt : (c - 1)^2 < (c - 1) * c := by
    rw [pow_two]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  exact (not_lt_of_ge (hbound.trans (Nat.pow_le_pow_left hle 2))) hlt

lemma le_radical_sq_of_no_prime_cube {n : ℕ} (hn : 0 < n)
    (h : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ n) : n ≤ ABC.radical n ^ 2 := by
  calc
    n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
      (Nat.prod_factorization_pow_eq_self hn.ne').symm
    _ ≤ ∏ p ∈ n.primeFactors, p ^ 2 := by
      apply Finset.prod_le_prod'
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hle : n.factorization p ≤ 2 := by
        by_contra! hlarge
        exact h p hprime ((hprime.pow_dvd_iff_le_factorization hn.ne').mpr (by omega))
      exact Nat.pow_le_pow_right hprime.pos hle
    _ = ABC.radical n ^ 2 := Finset.prod_pow _ _ id

private lemma prime_cube_of_radical_sq_lt {n : ℕ} (hn : 0 < n)
    (h : ABC.radical n ^ 2 < n) : ∃ p : ℕ, p.Prime ∧ p ^ 3 ∣ n := by
  by_contra! hnone
  exact (not_lt_of_ge (le_radical_sq_of_no_prime_cube hn hnone)) h

/-- The cube-free contribution to the ABC conjecture is empty. -/
lemma sum_le_radical_of_no_prime_cube {a b c : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hp : ({a, b, c} : Set ℕ).Pairwise Nat.Coprime) (hs : a + b = c)
    (h : ∀ p : ℕ, p.Prime → ¬ p^3 ∣ a * b * c) :
    c ≤ ABC.radical (a * b * c) := by
  have hab : ∀ p : ℕ, p.Prime → ¬ p^3 ∣ a * b :=
    fun p hprime hdiv => h p hprime (dvd_mul_of_dvd_left hdiv c)
  have hc : ∀ p : ℕ, p.Prime → ¬ p^3 ∣ c :=
    fun p hprime hdiv => h p hprime (dvd_mul_of_dvd_right hdiv (a * b))
  exact sum_le_radical_of_square_bounds ha hb hp hs
    (le_radical_sq_of_no_prime_cube (by omega) hc)
    (le_radical_sq_of_no_prime_cube (Nat.mul_pos ha hb) hab)

private lemma weighted_product_lt {x y r c ε : ℝ} (hr : 0 < r)
    (heq : r = x * y) (hbad : r^(1 + ε) < c) :
    (x^2 * r^ε) * (y^2 * r^ε) < c^2 := by
  have hprod : (x^2 * r^ε) * (y^2 * r^ε) = (r^(1 + ε))^2 := by
    rw [Real.rpow_add hr, Real.rpow_one, heq]
    ring
  rw [hprod]
  exact pow_lt_pow_left₀ hbad (Real.rpow_nonneg hr.le _) (by decide)

private lemma weighted_right_lt {x y r c ε : ℝ} (hc : 0 ≤ c) (hr : 0 < r)
    (heq : r = x * y) (hbad : r^(1 + ε) < c) (hleft : c ≤ x^2 * r^ε) :
    y^2 * r^ε < c := by
  by_contra! hright
  have h := mul_le_mul hleft hright hc
    (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hr.le _))
  exact (not_lt_of_ge (by simpa only [pow_two] using h)) (weighted_product_lt hr heq hbad)

private lemma stronger_right_lt {x y r c ε : ℝ} (hc : 0 ≤ c) (hr : 0 < r)
    (heq : r = x * y) (hbad : r^(1 + ε) < c) (hleft : c ≤ x^2) :
    y^2 * r^(2 * ε) < c := by
  by_contra! hright
  have h := mul_le_mul hleft hright hc (sq_nonneg x)
  have he : x^2 * (y^2 * r^(2 * ε)) = (x^2 * r^ε) * (y^2 * r^ε) := by
    rw [show 2 * ε = ε + ε by ring, Real.rpow_add hr]
    ring
  rw [he, ← pow_two] at h
  exact (not_lt_of_ge h) (weighted_product_lt hr heq hbad)

/-- For fixed K, a bounded quotient abc / R² gives only finitely many
exceptions at any positive quality gap. -/
lemma finite_of_bounded_cube_excess (ε : ℝ) (hε : 0 < ε) (K : ℕ) :
    {(a, b, c) : ℕ × ℕ × ℕ |
      0 < a ∧ 0 < b ∧ a + b = c ∧
      (ABC.radical (a * b * c) : ℝ)^(1 + ε) < (c : ℝ) ∧
      a * b * c ≤ K * ABC.radical (a * b * c)^2}.Finite := by
  let L : ℝ := 2 * (K : ℝ)
  let M : ℝ := L ^ (2 * ε)⁻¹
  have hL : 0 ≤ L := by dsimp [L]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt M
  let T := K * N ^ 2
  apply (Set.finite_Iic (T, T, T)).subset
  rintro ⟨a, b, c⟩ ⟨ha, hb, hs, hbad, hcap⟩
  let R : ℝ := ABC.radical (a * b * c)
  have hR : 0 < R := by
    dsimp only [R]
    exact_mod_cast radical_pos (a * b * c)
  have hmul : c ≤ 2 * (a * b) := by
    have hprod : c - 1 ≤ a * b := hs ▸ product_ge_sum_sub_one ha hb
    omega
  have hcsq : c ^ 2 ≤ 2 * (a * b * c) := by
    rw [pow_two, ← Nat.mul_assoc]
    exact Nat.mul_le_mul_right c hmul
  have hcap' : (↑(a * b * c) : ℝ) ≤ (K : ℝ) * R ^ 2 := by
    dsimp [R]
    exact_mod_cast hcap
  have hsize : (c : ℝ)^2 ≤ L * R^2 := by
    calc
      (c : ℝ)^2 ≤ 2 * (↑(a * b * c) : ℝ) := by exact_mod_cast hcsq
      _ ≤ L * R^2 := by
        dsimp only [L]
        rw [mul_assoc (2 : ℝ) (K : ℝ) (R ^ 2)]
        exact mul_le_mul_of_nonneg_left hcap' (by norm_num : (0 : ℝ) ≤ 2)
  have hsquared : (R ^ (1 + ε))^2 < (c : ℝ)^2 :=
    pow_lt_pow_left₀ hbad (Real.rpow_nonneg hR.le _) (by decide)
  have hpow : (R^(1 + ε))^2 = R^2 * R^(2 * ε) := by
    rw [show 2 * ε = ε + ε by ring, Real.rpow_add hR ε ε,
      Real.rpow_add hR 1 ε, Real.rpow_one]
    ring
  rw [hpow] at hsquared
  have hRpow : R^(2 * ε) < L :=
    lt_of_mul_lt_mul_left (hsquared.trans_le (by simpa only [mul_comm] using hsize))
      (sq_nonneg R)
  have hRbound : R < M :=
    (Real.lt_rpow_inv_iff_of_pos hR.le hL (by linarith : 0 < 2 * ε)).mpr hRpow
  have hRN : ABC.radical (a * b * c) ≤ N := by
    have h := (hRbound.trans hN).le
    dsimp only [R] at h
    exact_mod_cast h
  have hcT : c ≤ T := by
    calc
      c = 1 * c := (Nat.one_mul c).symm
      _ ≤ a * b * c := Nat.mul_le_mul_right c (Nat.mul_pos ha hb)
      _ ≤ K * ABC.radical (a * b * c)^2 := hcap
      _ ≤ T := Nat.mul_le_mul_left K (Nat.pow_le_pow_left hRN 2)
  change a ≤ T ∧ b ≤ T ∧ c ≤ T
  omega

theorem main : H1 → H2 → H3 → OMA.R_ABC_abc_variants_quality_R1.H2 := by
  intro h1 h2 h3 ε hε
  obtain ⟨K1, h1⟩ := h1 ε hε
  obtain ⟨K2, h2⟩ := h2 ε hε
  obtain ⟨K3, h3⟩ := h3 ε hε
  let K := max K1 (max K2 K3)
  apply (((h1.union h2).union h3).union (finite_of_bounded_cube_excess ε hε K)).subset
  rintro ⟨a, b, c⟩ ⟨ha, hb, hc, hp, hs, hnsC, hnsAB, hbad⟩
  by_cases hcap : a * b * c ≤ K * ABC.radical (a * b * c)^2
  · exact Or.inr ⟨ha, hb, hs, hbad, hcap⟩
  left
  have hK : ∀ t ≤ K, t * ABC.radical (a * b * c)^2 < a * b * c :=
    fun t ht => (Nat.mul_le_mul_right _ ht).trans_lt (lt_of_not_ge hcap)
  have hK1 := hK K1 (le_max_left _ _)
  have hK2 := hK K2 ((le_max_left K2 K3).trans (le_max_right _ _))
  have hK3 := hK K3 ((le_max_right K2 K3).trans (le_max_right _ _))
  have hR := radical_pos (a * b * c)
  have hRpos : (0 : ℝ) < (ABC.radical (a * b * c) : ℝ) := by exact_mod_cast hR
  have hRone : (1 : ℝ) ≤ (ABC.radical (a * b * c) : ℝ) := by
    exact_mod_cast (show 1 ≤ ABC.radical (a * b * c) from hR)
  have hC : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc.le
  have hmul : (ABC.radical (a * b * c) : ℝ) =
      (ABC.radical c : ℝ) * (ABC.radical (a * b) : ℝ) := by
    exact_mod_cast (radical_mul (coprime_product_sum ha hb hp hs)).trans (Nat.mul_comm _ _)
  by_cases hweight : (ABC.radical c : ℝ)^2 *
      (ABC.radical (a * b * c) : ℝ)^ε < (c : ℝ)
  · have hw : (1 : ℝ) ≤ (ABC.radical (a * b * c) : ℝ)^ε :=
      Real.one_le_rpow hRone hε.le
    have hsq : ABC.radical c ^ 2 < c := by
      exact_mod_cast (le_mul_of_one_le_right (sq_nonneg (ABC.radical c : ℝ)) hw).trans_lt hweight
    exact Or.inl (Or.inl ⟨ha, hb, hc, hp, hs, hnsC, hnsAB, hbad, hK1, hweight,
      prime_cube_of_radical_sq_lt hc hsq⟩)
  · by_cases hsq : ABC.radical c ^ 2 < c
    · have hr := weighted_right_lt hC hRpos hmul hbad (le_of_not_gt hweight)
      exact Or.inl (Or.inr ⟨ha, hb, hc, hp, hs, hnsC, hnsAB, hbad, hK2, hsq,
        le_of_not_gt hweight, hr, prime_cube_of_radical_sq_lt hc hsq⟩)
    · have hcsq : (c : ℝ) ≤ (ABC.radical c : ℝ)^2 := by
        exact_mod_cast (le_of_not_gt hsq)
      have habsq : ABC.radical (a * b)^2 < a * b := by
        by_contra! hab
        have hcle : (c : ℝ) ≤ (ABC.radical (a * b * c) : ℝ) := by
          exact_mod_cast sum_le_radical_of_square_bounds ha hb hp hs (le_of_not_gt hsq) hab
        have hr : (ABC.radical (a * b * c) : ℝ) ≤
            (ABC.radical (a * b * c) : ℝ)^(1 + ε) :=
          Real.self_le_rpow_of_one_le hRone (by linarith)
        exact (not_lt_of_ge (hcle.trans hr)) hbad
      have hr := stronger_right_lt hC hRpos hmul hbad hcsq
      exact Or.inr ⟨ha, hb, hc, hp, hs, hnsC, hnsAB, hbad, hK3, le_of_not_gt hsq,
        habsq, hr, prime_cube_of_radical_sq_lt (Nat.mul_pos ha hb) habsq⟩

end Proof

end OMA.R_ABC_abc_variants_quality_R1_H2_R1
