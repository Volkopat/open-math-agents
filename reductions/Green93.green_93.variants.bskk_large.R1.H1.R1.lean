import OMAReductions.R_Green93_green_93_variants_bskk_large_R1

/-!
Reduction of `Green93.green_93.variants.bskk_large.R1.H1` (small-degree divisor bound for random
monic integer polynomials with coefficients uniform in `{0, ..., M}` and nonzero constant term,
Bary-Soroker-Koukoulopoulos-Kozma, *Invent. Math.* 233 (2023), Sections 2.1-2.2) to two disjoint,
unconditional anti-concentration hypotheses:

- `H1`: Cyclotomic / root-of-unity small-degree divisor bound (BSKK23 Proposition 2.1, Halasz /
  Littlewood-Offord anti-concentration at roots of unity).
- `H2`: Non-cyclotomic small-degree irreducible monic divisor bound (BSKK23 Proposition 2.2,
  Breuillard-Varju Mahler-measure contraction).

In `main`, we prove completely from scratch in Lean 4:
1. Exact sample geometry: `eligible.card = M * (M + 1)^(n - 1)` for all `1 <= n`.
2. Monic-irreducible factor extraction in `Z[X]`: every positive-degree divisor `g | f_a` of a
   monic polynomial `f_a` with `f_a.coeff 0 != 0` has a monic irreducible factor `q | g | f_a`
   with `1 <= q.natDegree <= g.natDegree` and `q.coeff 0 != 0`.
3. Elementary integer root bounds for `Green93.monicPoly`: `eval r f_a > 0` for all `r >= 0` and
   `eval r f_a != 0` for all `r < -M`, forcing every integer root into `[-M, -1]`.
4. Cyclotomic vs non-cyclotomic partition, union bound, and exponent unification `c = min c1 c2`.
-/

namespace OMA.R_Green93_green_93_variants_bskk_large_R1_H1_R1

/- BSKK23 Proposition 2.1: bound on eligible coefficient vectors whose monic polynomial is divisible
by a monic irreducible cyclotomic factor of degree at most n^(1/10). -/
def H1 : Prop :=
  ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ n₁ : ℕ, ∀ M n : ℕ, 34 ≤ M → n₁ ≤ n →
    (Real.log (M : ℝ)) ^ 3 ≤ n →
    ({a : Fin n → Fin (M + 1) |
        (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0 ∧
        ∃ q : Polynomial ℤ, q.Monic ∧ Irreducible q ∧
          q ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
          1 ≤ q.natDegree ∧ (q.natDegree : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) ∧
          ∃ k : ℕ, 1 ≤ k ∧ q ∣ Polynomial.X ^ k - 1}.ncard : ℝ) ≤
      ((n : ℝ) ^ (-c₁) / 4) * ((M : ℝ) * (M + 1 : ℝ) ^ (n - 1))

/- BSKK23 Proposition 2.2: bound on eligible coefficient vectors whose monic polynomial is divisible
by a monic irreducible non-cyclotomic factor with nonzero constant term of degree at most n^(1/10). -/
def H2 : Prop :=
  ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ n₂ : ℕ, ∀ M n : ℕ, 34 ≤ M → n₂ ≤ n →
    (Real.log (M : ℝ)) ^ 3 ≤ n →
    ({a : Fin n → Fin (M + 1) |
        (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0 ∧
        ∃ q : Polynomial ℤ, q.Monic ∧ Irreducible q ∧ q.coeff 0 ≠ 0 ∧
          q ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
          1 ≤ q.natDegree ∧ (q.natDegree : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) ∧
          ∀ k : ℕ, 1 ≤ k → ¬ (q ∣ Polynomial.X ^ k - 1)}.ncard : ℝ) ≤
      ((n : ℝ) ^ (-c₂) / 4) * ((M : ℝ) * (M + 1 : ℝ) ^ (n - 1))

/- ============================================================================
   Part 1: Basic Properties and Exact Sample Cardinality of Green93.monicPoly
   ============================================================================ -/

/- Every Green93.monicPoly is monic of degree n. -/
lemma monicPoly_monic {n : ℕ} (a : Fin n → ℕ) : (Green93.monicPoly a).Monic := by
  cases n with
  | zero =>
    simp [Green93.monicPoly]
  | succ n =>
    unfold Green93.monicPoly
    apply (Polynomial.monic_X_pow (n + 1)).add_of_left
    have hdeg_sum : (∑ j : Fin (n + 1), Polynomial.C (a j : ℤ) * Polynomial.X ^ (j : ℕ)).natDegree ≤ n := by
      refine Polynomial.natDegree_sum_le_of_forall_le Finset.univ _ fun j _ => ?_
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt_succ j.isLt)
    have hlt : (∑ j : Fin (n + 1), Polynomial.C (a j : ℤ) * Polynomial.X ^ (j : ℕ)).degree <
        (Polynomial.X ^ (n + 1) : Polynomial ℤ).degree := by
      rw [Polynomial.degree_X_pow]
      by_cases h0 : (∑ j : Fin (n + 1), Polynomial.C (a j : ℤ) * Polynomial.X ^ (j : ℕ)) = 0
      · rw [h0, Polynomial.degree_zero]
        exact WithBot.bot_lt_coe (n + 1)
      · rw [Polynomial.degree_eq_natDegree h0]
        exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le hdeg_sum)
    exact hlt

/- For 1 <= n, the constant term of Green93.monicPoly a is (a ⟨0, _⟩ : ℤ). -/
lemma monicPoly_coeff_zero {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℕ) :
    (Green93.monicPoly a).coeff 0 = (a ⟨0, by omega⟩ : ℤ) := by
  classical
  unfold Green93.monicPoly
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow]
  have hn0 : 0 ≠ n := by omega
  simp only [hn0, ↓reduceIte, zero_add, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin n)]
  · simp
  · intro j _ hjne
    have hj0 : 0 ≠ j.val := fun h => hjne (Fin.ext h.symm)
    simp [hj0]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/- Exact cardinality of the eligible coefficient set: M * (M + 1)^(n - 1) for 1 <= n. -/
lemma eligible_card_eq {M n : ℕ} (hn : 1 ≤ n)
    {dec : DecidablePred (fun a : Fin n → Fin (M + 1) =>
      (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0)} :
    (@Finset.filter (Fin n → Fin (M + 1)) _ dec Finset.univ).card = M * (M + 1) ^ (n - 1) := by
  classical
  let E := @Finset.filter (Fin n → Fin (M + 1)) _ dec Finset.univ
  have hmem_iff : ∀ a : Fin n → Fin (M + 1), a ∈ E ↔ (a ⟨0, by omega⟩).val ≠ 0 := by
    intro a
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and, monicPoly_coeff_zero hn]
    exact Nat.cast_ne_zero
  let eqv : E ≃ {x : Fin (M + 1) // x.val ≠ 0} × (Fin (n - 1) → Fin (M + 1)) :=
    { toFun := fun a =>
        (⟨a.1 ⟨0, by omega⟩, (hmem_iff a.1).mp a.2⟩,
         fun i => a.1 ⟨i.val + 1, by omega⟩)
      invFun := fun p =>
        ⟨fun j => if hj : j.val = 0 then p.1.1 else p.2 ⟨j.val - 1, by omega⟩,
         (hmem_iff _).mpr (by simp [p.1.2])⟩
      left_inv := fun a => by
        apply Subtype.ext
        funext j
        by_cases hj : j.val = 0
        · simp only [hj, ↓reduceDIte]
          exact congrArg a.1 (Fin.ext hj.symm)
        · simp only [hj, ↓reduceDIte]
          exact congrArg a.1 (Fin.ext (by dsimp only; omega))
      right_inv := fun p => by
        apply Prod.ext
        · apply Subtype.ext
          simp
        · funext i
          have hi : i.val + 1 ≠ 0 := by omega
          simp only [hi, ↓reduceDIte, Nat.add_sub_cancel] }
  have hcard1 : Fintype.card {x : Fin (M + 1) // x.val ≠ 0} = M := by
    have hset : (Finset.univ.filter fun x : Fin (M + 1) => x.val ≠ 0) =
        (Finset.univ : Finset (Fin (M + 1))).erase ⟨0, Nat.succ_pos M⟩ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq,
        Fin.ext_iff, and_true]
    rw [Fintype.card_subtype, hset, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hcard2 : Fintype.card (Fin (n - 1) → Fin (M + 1)) = (M + 1) ^ (n - 1) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hcardE : Fintype.card E = M * (M + 1) ^ (n - 1) := by
    rw [Fintype.card_congr eqv, Fintype.card_prod, hcard1, hcard2]
  simpa only [Fintype.card_coe] using hcardE

/- ============================================================================
   Part 2: Monic Normalization and Irreducible Monic Factor Extraction in Z[X]
   ============================================================================ -/

/- Any divisor of a monic integer polynomial has leading coefficient 1 or -1. -/
lemma leadingCoeff_eq_one_or_neg_one_of_dvd_monic {f g : Polynomial ℤ}
    (hf : f.Monic) (hdvd : g ∣ f) :
    g.leadingCoeff = 1 ∨ g.leadingCoeff = -1 := by
  rcases hdvd with ⟨h, rfl⟩
  have hlc : g.leadingCoeff * h.leadingCoeff = 1 := by
    rw [← Polynomial.leadingCoeff_mul]
    exact hf
  have hu : IsUnit g.leadingCoeff := isUnit_iff_exists_inv.mpr ⟨h.leadingCoeff, hlc⟩
  exact Int.isUnit_iff.mp hu

/- Normalizing any divisor g of a monic integer polynomial to a monic divisor of the same degree. -/
lemma exists_monic_dvd_same_degree {f g : Polynomial ℤ} (hf : f.Monic) (hdvd : g ∣ f) :
    ∃ g' : Polynomial ℤ, g'.Monic ∧ g'.natDegree = g.natDegree ∧ g' ∣ f ∧ (IsUnit g' ↔ IsUnit g) := by
  rcases leadingCoeff_eq_one_or_neg_one_of_dvd_monic hf hdvd with h1 | hm1
  · exact ⟨g, h1, rfl, hdvd, Iff.rfl⟩
  · refine ⟨-g, ?_, Polynomial.natDegree_neg g, dvd_trans (neg_dvd.mpr dvd_rfl) hdvd,
      ⟨fun hu => by simpa using hu.neg, fun hu => hu.neg⟩⟩
    rw [Polynomial.Monic, Polynomial.leadingCoeff_neg, hm1, neg_neg]

/- A monic integer polynomial of positive degree is not a unit. -/
lemma not_isUnit_of_monic_pos_natDegree {g : Polynomial ℤ} (hg : g.Monic) (hdeg : 1 ≤ g.natDegree) :
    ¬ IsUnit g := by
  intro hu
  rcases hu.exists_right_inv with ⟨h, hgh⟩
  have hne_g : g ≠ 0 := hg.ne_zero
  have hne_h : h ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hgh
    exact zero_ne_one hgh
  have hdeg_mul : (g * h).natDegree = g.natDegree + h.natDegree :=
    Polynomial.natDegree_mul hne_g hne_h
  rw [hgh, Polynomial.natDegree_one] at hdeg_mul
  omega

/- A monic integer polynomial of degree 0 equals 1 (hence is a unit). -/
lemma isUnit_of_monic_natDegree_zero {g : Polynomial ℤ} (hg : g.Monic) (hdeg : g.natDegree = 0) :
    IsUnit g := by
  have hg1 : g = 1 := Polynomial.eq_one_of_monic_natDegree_zero hg hdeg
  rw [hg1]
  exact isUnit_one

/- Every positive-degree divisor of a monic integer polynomial f with f.coeff 0 != 0 is divisible by
a monic irreducible factor q of degree between 1 and g.natDegree with q.coeff 0 != 0. -/
lemma exists_monic_irreducible_dvd_of_monic :
    ∀ (d : ℕ) (f g : Polynomial ℤ),
      f.Monic → f.coeff 0 ≠ 0 → g.Monic → 1 ≤ g.natDegree → g.natDegree = d → g ∣ f →
      ∃ q : Polynomial ℤ, q.Monic ∧ Irreducible q ∧ q.coeff 0 ≠ 0 ∧
        1 ≤ q.natDegree ∧ q.natDegree ≤ g.natDegree ∧ q ∣ f := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro f g hf hf0 hg hg_pos hg_deg hdvd
    by_cases hirr : Irreducible g
    · have hg0 : g.coeff 0 ≠ 0 := by
        intro h0
        rcases hdvd with ⟨h, rfl⟩
        rw [Polynomial.mul_coeff_zero, h0, zero_mul] at hf0
        exact hf0 rfl
      exact ⟨g, hg, hirr, hg0, hg_pos, le_rfl, hdvd⟩
    · have hnotu : ¬ IsUnit g := not_isUnit_of_monic_pos_natDegree hg hg_pos
      have hfac : ∃ u v : Polynomial ℤ, g = u * v ∧ ¬ IsUnit u ∧ ¬ IsUnit v := by
        rw [irreducible_iff] at hirr
        push Not at hirr
        exact hirr hnotu
      rcases hfac with ⟨u, v, huv, hnu, hnv⟩
      have hu_dvd : u ∣ g := ⟨v, huv⟩
      have hv_dvd : v ∣ g := ⟨u, by rw [mul_comm]; exact huv⟩
      obtain ⟨u', hu'_monic, hu'_deg, hu'_dvd, hu'_unit⟩ := exists_monic_dvd_same_degree hg hu_dvd
      obtain ⟨v', hv'_monic, hv'_deg, hv'_dvd, hv'_unit⟩ := exists_monic_dvd_same_degree hg hv_dvd
      have hnu' : ¬ IsUnit u' := fun h => hnu (hu'_unit.mp h)
      have hnv' : ¬ IsUnit v' := fun h => hnv (hv'_unit.mp h)
      have hu'_pos : 1 ≤ u'.natDegree := by
        by_contra h0
        have hdeg0 : u'.natDegree = 0 := by omega
        exact hnu' (isUnit_of_monic_natDegree_zero hu'_monic hdeg0)
      have hv'_pos : 1 ≤ v'.natDegree := by
        by_contra h0
        have hdeg0 : v'.natDegree = 0 := by omega
        exact hnv' (isUnit_of_monic_natDegree_zero hv'_monic hdeg0)
      have hu_ne : u ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at huv
        exact hg.ne_zero huv
      have hv_ne : v ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at huv
        exact hg.ne_zero huv
      have hsum_deg : u'.natDegree + v'.natDegree = g.natDegree := by
        rw [hu'_deg, hv'_deg, ← Polynomial.natDegree_mul hu_ne hv_ne, ← huv]
      have hu'_lt : u'.natDegree < d := by omega
      obtain ⟨q, hq_monic, hq_irr, hq0, hq_pos, hq_le, hq_dvd⟩ :=
        ih u'.natDegree hu'_lt f u' hf hf0 hu'_monic hu'_pos rfl (dvd_trans hu'_dvd hdvd)
      exact ⟨q, hq_monic, hq_irr, hq0, hq_pos, hq_le.trans (by omega), hq_dvd⟩

/- General form for any (not necessarily monic) positive-degree divisor g of a monic f. -/
lemma exists_monic_irreducible_dvd_of_dvd_monic {f g : Polynomial ℤ}
    (hf : f.Monic) (hf0 : f.coeff 0 ≠ 0) (hdvd : g ∣ f) (hdeg : 0 < g.natDegree) :
    ∃ q : Polynomial ℤ, q.Monic ∧ Irreducible q ∧ q.coeff 0 ≠ 0 ∧
      1 ≤ q.natDegree ∧ q.natDegree ≤ g.natDegree ∧ q ∣ f := by
  obtain ⟨g', hg'_monic, hg'_deg, hg'_dvd, _⟩ := exists_monic_dvd_same_degree hf hdvd
  obtain ⟨q, hq_monic, hq_irr, hq0, hq_pos, hq_le, hq_dvd⟩ :=
    exists_monic_irreducible_dvd_of_monic g'.natDegree f g' hf hf0 hg'_monic (by omega) rfl hg'_dvd
  exact ⟨q, hq_monic, hq_irr, hq0, hq_pos, by omega, hq_dvd⟩

/- ============================================================================
   Part 3: Elementary Integer Root Bounds for Green93.monicPoly
   ============================================================================ -/

/- Evaluating Green93.monicPoly a at any nonnegative integer r gives a strictly positive integer
when the constant term is nonzero and 1 <= n. -/
lemma monicPoly_eval_pos_of_nonneg {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℕ)
    (ha0 : (Green93.monicPoly a).coeff 0 ≠ 0) {r : ℤ} (hr : 0 ≤ r) :
    0 < (Green93.monicPoly a).eval r := by
  have hpos0 : 0 < (a ⟨0, by omega⟩ : ℤ) := by
    rw [monicPoly_coeff_zero hn] at ha0
    have : 0 ≤ (a ⟨0, by omega⟩ : ℤ) := Nat.cast_nonneg _
    omega
  unfold Green93.monicPoly
  rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finsetSum]
  have hpow_nn : 0 ≤ r ^ n := pow_nonneg hr n
  have hterm_nn : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ (Polynomial.C (a j : ℤ) * Polynomial.X ^ (j : ℕ)).eval r := by
    intro j _
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr j.val)
  have hsum_ge : (a ⟨0, by omega⟩ : ℤ) ≤
      ∑ j : Fin n, (Polynomial.C (a j : ℤ) * Polynomial.X ^ (j : ℕ)).eval r := by
    have hsingle := Finset.single_le_sum hterm_nn (Finset.mem_univ (⟨0, by omega⟩ : Fin n))
    simpa [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] using hsingle
  linarith

/- Geometric sum identity in ℕ: (t - 1) * ∑_{j < m} t^j + 1 = t^m for t >= 1. -/
lemma geom_sum_nat_identity {t : ℕ} (ht : 1 ≤ t) :
    ∀ m : ℕ, (t - 1) * (∑ j ∈ Finset.range m, t ^ j) + 1 = t ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, pow_succ]
    have hmul : (t - 1) * t ^ m + t ^ m = t ^ m * t := by
      have : (t - 1 + 1) * t ^ m = t * t ^ m := by rw [Nat.sub_add_cancel ht]
      linarith
    omega

/- No integer r < -M can be a root of Green93.monicPoly a when every coefficient satisfies a j <= M. -/
lemma monicPoly_eval_ne_zero_of_lt_neg {M n : ℕ} (a : Fin n → ℕ) (haM : ∀ j, a j ≤ M)
    {r : ℤ} (hr : r < -(M : ℤ)) :
    (Green93.monicPoly a).eval r ≠ 0 := by
  let t : ℕ := (-r).toNat
  have hr_neg : r < 0 := by
    have : (0 : ℤ) ≤ (M : ℤ) := Nat.cast_nonneg M
    omega
  have hr_eq : r = -(t : ℤ) := by
    dsimp only [t]
    omega
  have ht_ge : M + 1 ≤ t := by omega
  have ht1 : 1 ≤ t := by omega
  have habs_sum : |∑ j : Fin n, (a j : ℤ) * r ^ j.val| < (t : ℤ) ^ n := by
    have h1 : |∑ j : Fin n, (a j : ℤ) * r ^ j.val| ≤
        ∑ j : Fin n, |(a j : ℤ) * r ^ j.val| := Finset.abs_sum_le_sum_abs _ _
    have h2 : ∑ j : Fin n, |(a j : ℤ) * r ^ j.val| ≤
        ∑ j : Fin n, ((t - 1 : ℕ) : ℤ) * (t : ℤ) ^ j.val := by
      refine Finset.sum_le_sum fun j _ => ?_
      rw [abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg (a j)), hr_eq, abs_neg,
        abs_of_nonneg (Nat.cast_nonneg t)]
      have hle : (a j : ℤ) ≤ ((t - 1 : ℕ) : ℤ) := by
        have : a j ≤ t - 1 := by have := haM j; omega
        exact_mod_cast this
      exact mul_le_mul_of_nonneg_right hle (pow_nonneg (Nat.cast_nonneg t) j.val)
    have h3 : (∑ j : Fin n, ((t - 1 : ℕ) : ℤ) * (t : ℤ) ^ j.val) =
        ((t - 1 : ℕ) : ℤ) * (∑ j ∈ Finset.range n, (t : ℤ) ^ j) := by
      rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun j => (t : ℤ) ^ j) n]
    have hgeomZ : ((t - 1 : ℕ) : ℤ) * (∑ j ∈ Finset.range n, (t : ℤ) ^ j) + 1 = (t : ℤ) ^ n := by
      exact_mod_cast geom_sum_nat_identity ht1 n
    linarith
  intro heval
  unfold Green93.monicPoly at heval
  rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finsetSum] at heval
  have hsum_eq : (∑ j : Fin n, (Polynomial.C (a j : ℤ) * Polynomial.X ^ (j : ℕ)).eval r) =
      ∑ j : Fin n, (a j : ℤ) * r ^ j.val := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [hsum_eq] at heval
  have hpow_eq : ∑ j : Fin n, (a j : ℤ) * r ^ j.val = -(r ^ n) := by linarith
  rw [hpow_eq, abs_neg, abs_pow, hr_eq, abs_neg, abs_of_nonneg (Nat.cast_nonneg t)] at habs_sum
  exact lt_irrefl _ habs_sum

/- Any integer root of an eligible Green93.monicPoly lies in [-M, -1]. -/
lemma int_root_bounds_of_monicPoly {M n : ℕ} (hn : 1 ≤ n) (a : Fin n → Fin (M + 1))
    (ha0 : (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0) {r : ℤ}
    (hroot : (Green93.monicPoly fun j => (a j : ℕ)).eval r = 0) :
    -(M : ℤ) ≤ r ∧ r ≤ -1 := by
  constructor
  · by_contra hlt
    push Not at hlt
    exact monicPoly_eval_ne_zero_of_lt_neg (fun j => (a j : ℕ)) (fun j => Nat.le_of_lt_succ (a j).isLt) hlt hroot
  · by_contra hge
    push Not at hge
    have hpos := monicPoly_eval_pos_of_nonneg hn (fun j => (a j : ℕ)) ha0 (r := r) (by omega)
    omega

/- ============================================================================
   Part 4: Main Reduction Theorem
   ============================================================================ -/

/- Deduction of OMA.R_Green93_green_93_variants_bskk_large_R1.H1 from H1 (cyclotomic divisor bound)
and H2 (non-cyclotomic small-degree divisor bound). -/
theorem main : H1 → H2 →
    OMA.R_Green93_green_93_variants_bskk_large_R1.H1 := by
  intro hH1 hH2
  obtain ⟨c₁, hc₁_pos, n₁, h1⟩ := hH1
  obtain ⟨c₂, hc₂_pos, n₂, h2⟩ := hH2
  refine ⟨min c₁ c₂, lt_min hc₁_pos hc₂_pos, max 1 (max n₁ n₂), ?_⟩
  intro M n hM hn hlogM
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnn₁ : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnn₂ : n₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  classical
  dsimp only
  set eligible := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
    (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0
  set bad := eligible.filter fun a => ∃ g : Polynomial ℤ,
    g ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
    0 < g.natDegree ∧ (g.natDegree : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ)
  set S_cyc := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
    (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0 ∧
    ∃ q : Polynomial ℤ, q.Monic ∧ Irreducible q ∧
      q ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
      1 ≤ q.natDegree ∧ (q.natDegree : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) ∧
      ∃ k : ℕ, 1 ≤ k ∧ q ∣ Polynomial.X ^ k - 1
  set S_noncyc := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
    (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0 ∧
    ∃ q : Polynomial ℤ, q.Monic ∧ Irreducible q ∧ q.coeff 0 ≠ 0 ∧
      q ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
      1 ≤ q.natDegree ∧ (q.natDegree : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) ∧
      ∀ k : ℕ, 1 ≤ k → ¬ (q ∣ Polynomial.X ^ k - 1)
  have hbad_sub : bad ⊆ S_cyc ∪ S_noncyc := by
    intro a ha
    simp only [bad, eligible, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rcases ha with ⟨ha0, g, hg_dvd, hg_pos, hg_le⟩
    have hf_monic : (Green93.monicPoly fun j => (a j : ℕ)).Monic :=
      monicPoly_monic (fun j => (a j : ℕ))
    obtain ⟨q, hq_monic, hq_irr, hq0, hq_pos, hq_le_g, hq_dvd⟩ :=
      exists_monic_irreducible_dvd_of_dvd_monic hf_monic ha0 hg_dvd hg_pos
    have hq_le_n : (q.natDegree : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) :=
      le_trans (by exact_mod_cast hq_le_g) hg_le
    by_cases hcyc : ∃ k : ℕ, 1 ≤ k ∧ q ∣ Polynomial.X ^ k - 1
    · refine Finset.mem_union_left _ ?_
      simp only [S_cyc, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨ha0, q, hq_monic, hq_irr, hq_dvd, hq_pos, hq_le_n, hcyc⟩
    · refine Finset.mem_union_right _ ?_
      simp only [S_noncyc, Finset.mem_filter, Finset.mem_univ, true_and]
      push Not at hcyc
      exact ⟨ha0, q, hq_monic, hq_irr, hq0, hq_dvd, hq_pos, hq_le_n, hcyc⟩
  have hcard_le : (bad.card : ℝ) ≤ (S_cyc.card : ℝ) + (S_noncyc.card : ℝ) := by
    have hnat : bad.card ≤ S_cyc.card + S_noncyc.card :=
      (Finset.card_le_card hbad_sub).trans (Finset.card_union_le S_cyc S_noncyc)
    exact_mod_cast hnat
  have hcyc_ncard : ({a : Fin n → Fin (M + 1) |
      (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0 ∧
      ∃ q : Polynomial ℤ, q.Monic ∧ Irreducible q ∧
        q ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
        1 ≤ q.natDegree ∧ (q.natDegree : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) ∧
        ∃ k : ℕ, 1 ≤ k ∧ q ∣ Polynomial.X ^ k - 1}.ncard : ℝ) = (S_cyc.card : ℝ) := by
    have hset : {a : Fin n → Fin (M + 1) |
        (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0 ∧
        ∃ q : Polynomial ℤ, q.Monic ∧ Irreducible q ∧
          q ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
          1 ≤ q.natDegree ∧ (q.natDegree : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) ∧
          ∃ k : ℕ, 1 ≤ k ∧ q ∣ Polynomial.X ^ k - 1} = (S_cyc : Set _) := by
      ext a
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, S_cyc, Finset.mem_filter, Finset.mem_univ,
        true_and]
    rw [hset, Set.ncard_coe_finset]
  have hnoncyc_ncard : ({a : Fin n → Fin (M + 1) |
      (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0 ∧
      ∃ q : Polynomial ℤ, q.Monic ∧ Irreducible q ∧ q.coeff 0 ≠ 0 ∧
        q ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
        1 ≤ q.natDegree ∧ (q.natDegree : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) ∧
        ∀ k : ℕ, 1 ≤ k → ¬ (q ∣ Polynomial.X ^ k - 1)}.ncard : ℝ) = (S_noncyc.card : ℝ) := by
    have hset : {a : Fin n → Fin (M + 1) |
        (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0 ∧
        ∃ q : Polynomial ℤ, q.Monic ∧ Irreducible q ∧ q.coeff 0 ≠ 0 ∧
          q ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
          1 ≤ q.natDegree ∧ (q.natDegree : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) ∧
          ∀ k : ℕ, 1 ≤ k → ¬ (q ∣ Polynomial.X ^ k - 1)} = (S_noncyc : Set _) := by
      ext a
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, S_noncyc, Finset.mem_filter, Finset.mem_univ,
        true_and]
    rw [hset, Set.ncard_coe_finset]
  have hb1 : (S_cyc.card : ℝ) ≤ ((n : ℝ) ^ (-c₁) / 4) * ((M : ℝ) * (M + 1 : ℝ) ^ (n - 1)) := by
    rw [← hcyc_ncard]
    exact h1 M n hM hnn₁ hlogM
  have hb2 : (S_noncyc.card : ℝ) ≤ ((n : ℝ) ^ (-c₂) / 4) * ((M : ℝ) * (M + 1 : ℝ) ^ (n - 1)) := by
    rw [← hnoncyc_ncard]
    exact h2 M n hM hnn₂ hlogM
  have helig_card : (eligible.card : ℝ) = (M : ℝ) * (M + 1 : ℝ) ^ (n - 1) := by
    have hnat : eligible.card = M * (M + 1) ^ (n - 1) := eligible_card_eq hn1
    exact_mod_cast hnat
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hrpow1 : (n : ℝ) ^ (-c₁) ≤ (n : ℝ) ^ (-min c₁ c₂) :=
    Real.rpow_le_rpow_of_exponent_le hn_ge1 (neg_le_neg (min_le_left c₁ c₂))
  have hrpow2 : (n : ℝ) ^ (-c₂) ≤ (n : ℝ) ^ (-min c₁ c₂) :=
    Real.rpow_le_rpow_of_exponent_le hn_ge1 (neg_le_neg (min_le_right c₁ c₂))
  have helig_nn : (0 : ℝ) ≤ (M : ℝ) * (M + 1 : ℝ) ^ (n - 1) := by positivity
  rw [helig_card]
  calc
    (bad.card : ℝ) ≤ (S_cyc.card : ℝ) + (S_noncyc.card : ℝ) := hcard_le
    _ ≤ ((n : ℝ) ^ (-c₁) / 4) * ((M : ℝ) * (M + 1 : ℝ) ^ (n - 1)) +
        ((n : ℝ) ^ (-c₂) / 4) * ((M : ℝ) * (M + 1 : ℝ) ^ (n - 1)) := add_le_add hb1 hb2
    _ ≤ ((n : ℝ) ^ (-min c₁ c₂) / 4) * ((M : ℝ) * (M + 1 : ℝ) ^ (n - 1)) +
        ((n : ℝ) ^ (-min c₁ c₂) / 4) * ((M : ℝ) * (M + 1 : ℝ) ^ (n - 1)) := by gcongr
    _ = ((n : ℝ) ^ (-min c₁ c₂) / 2) * ((M : ℝ) * (M + 1 : ℝ) ^ (n - 1)) := by ring

end OMA.R_Green93_green_93_variants_bskk_large_R1_H1_R1
