import FormalConjectures.ErdosProblems.«240»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Algebra.Polynomial.HasseDeriv

/-!
# Tijdeman's gap theorem for `P`-smooth numbers via Baker–Feldman

We prove `Erdos240.erdos_240.variants.tijdeman_finite`: for any finite nonempty set `P` of primes,
there exists `C > 0` such that `a P i / (log (a P i)) ^ C = O(a P (i + 1) - a P i)`.

The proof combines:
1. Smooth-number enumeration and prime-factorization bookkeeping (inlined from reduction R1).
2. A self-contained Baker–Feldman lower bound `c * B ^ (-C) ≤ |∑_{p ∈ S} b_p * log p|` for any
   fixed finite set `S` of rational primes, using Feldman block polynomials, Siegel's lemma over
   `ℤ`, an explicit algebraic Hermite–Schwarz extrapolation lemma via `dslope` and the Maximum
   Modulus Principle (with no contour integrals and no Kummer theory), and a discrete shift-operator
   nonvanishing argument.
-/

namespace BakerFeldman

open Filter Asymptotics Polynomial

/- Section 1: Elementary arithmetic helpers & unique factorization nonvanishing -/

lemma pow_le_two_pow_eventually (d C : ℕ) :
    ∃ m : ℕ, 1 ≤ m ∧ C * m ^ d ≤ 2 ^ m := by
  have hlim : Tendsto (fun m : ℕ => ((C : ℝ) * (m : ℝ) ^ d) / (2 : ℝ) ^ m) atTop (nhds 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ d * Real.exp (-(Real.log 2) * x)) atTop (nhds 0) := by
      have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have h2 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d
      have h3 : Tendsto (fun x : ℝ => (Real.log 2 * x) ^ d * Real.exp (-(Real.log 2 * x)))
          atTop (nhds 0) :=
        h2.comp (tendsto_id.const_mul_atTop hpos)
      have h4 := h3.const_mul ((Real.log 2) ^ d)⁻¹
      simp only [mul_zero] at h4
      refine h4.congr (fun x => ?_)
      have hne : Real.log 2 ^ d ≠ 0 := pow_ne_zero d hpos.ne'
      rw [mul_pow, neg_mul]
      field_simp [hne]
    have h5 : Tendsto (fun m : ℕ => (C : ℝ) * ((m : ℝ) ^ d * Real.exp (-(Real.log 2) * (m : ℝ))))
        atTop (nhds 0) := by
      simpa using (h1.comp tendsto_natCast_atTop_atTop).const_mul (C : ℝ)
    refine h5.congr (fun m => ?_)
    have h2pow : (2 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [h2pow, div_eq_mul_inv, ← Real.exp_neg, mul_assoc]
    ring_nf
  have hev := (tendsto_order.mp hlim).2 1 zero_lt_one
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  have hlt := hN (max N 1) (le_max_left _ _)
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (max N 1) := by positivity
  rw [div_lt_one hpos] at hlt
  exact_mod_cast hlt.le

lemma sum_int_mul_log_ne_zero {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {b : ℕ → ℤ} (hne : ∃ p ∈ S, b p ≠ 0) :
    ∑ p ∈ S, (b p : ℝ) * Real.log (p : ℝ) ≠ 0 := by
  intro hzero
  set Spos := S.filter (fun p => 0 < b p)
  set Sneg := S.filter (fun p => b p < 0)
  have hdisj : Disjoint Spos Sneg := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_filter] at hp1 hp2
    omega
  have hsplit : ∑ p ∈ S, (b p : ℝ) * Real.log (p : ℝ) =
      (∑ p ∈ Spos, ((b p).natAbs : ℝ) * Real.log (p : ℝ)) -
      (∑ p ∈ Sneg, ((b p).natAbs : ℝ) * Real.log (p : ℝ)) := by
    have hsub : Spos ∪ Sneg ⊆ S := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [← Finset.sum_subset hsub]
    · rw [Finset.sum_union hdisj, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mem_filter] at hp
        have hnat : ((b p).natAbs : ℤ) = b p := Int.natAbs_of_nonneg hp.2.le
        have hcast : ((b p).natAbs : ℝ) = (b p : ℝ) := by
          rw [← Int.cast_natCast (R := ℝ), hnat]
        rw [hcast]
      · apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mem_filter] at hp
        have hnat : -((b p).natAbs : ℤ) = b p := by
          have := Int.ofNat_natAbs_of_nonpos hp.2.le
          omega
        have hcast : -((b p).natAbs : ℝ) = (b p : ℝ) := by
          rw [← Int.cast_natCast (R := ℝ), ← Int.cast_neg, hnat]
        rw [← neg_mul, hcast]
    · intro p hp hnot
      simp only [Spos, Sneg, Finset.mem_union, Finset.mem_filter, not_or, not_and] at hnot
      have h0 : b p = 0 := by
        have h1 : ¬ (0 < b p) := hnot.1 hp
        have h2 : ¬ (b p < 0) := hnot.2 hp
        omega
      simp [h0]
  rw [hsplit, sub_eq_zero] at hzero
  set Ppos : ℕ := ∏ p ∈ Spos, p ^ (b p).natAbs
  set Pneg : ℕ := ∏ p ∈ Sneg, p ^ (b p).natAbs
  have hPpos_pos : 0 < Ppos :=
    Finset.prod_pos fun p hp => pow_pos (hS p (Finset.mem_filter.mp hp).1).pos _
  have hPneg_pos : 0 < Pneg :=
    Finset.prod_pos fun p hp => pow_pos (hS p (Finset.mem_filter.mp hp).1).pos _
  have hlog_eq : Real.log (Ppos : ℝ) = Real.log (Pneg : ℝ) := by
    have hL : Real.log (Ppos : ℝ) = ∑ p ∈ Spos, ((b p).natAbs : ℝ) * Real.log (p : ℝ) := by
      simp only [Ppos, Nat.cast_prod, Nat.cast_pow]
      rw [Real.log_prod]
      · apply Finset.sum_congr rfl
        intro p _
        rw [Real.log_pow]
      · intro p hp
        exact pow_ne_zero _ (by exact_mod_cast (hS p (Finset.mem_filter.mp hp).1).ne_zero)
    have hR : Real.log (Pneg : ℝ) = ∑ p ∈ Sneg, ((b p).natAbs : ℝ) * Real.log (p : ℝ) := by
      simp only [Pneg, Nat.cast_prod, Nat.cast_pow]
      rw [Real.log_prod]
      · apply Finset.sum_congr rfl
        intro p _
        rw [Real.log_pow]
      · intro p hp
        exact pow_ne_zero _ (by exact_mod_cast (hS p (Finset.mem_filter.mp hp).1).ne_zero)
    rw [hL, hR, hzero]
  have hPeq : Ppos = Pneg := by
    have hR : (Ppos : ℝ) = (Pneg : ℝ) :=
      Real.log_injOn_pos (Set.mem_Ioi.mpr (by exact_mod_cast hPpos_pos))
        (Set.mem_Ioi.mpr (by exact_mod_cast hPneg_pos)) hlog_eq
    exact_mod_cast hR
  obtain ⟨p₀, hp₀S, hp₀ne⟩ := hne
  have hp₀pr : p₀.Prime := hS p₀ hp₀S
  have hcontra : ∀ (A B : Finset ℕ), Disjoint A B → (∀ q ∈ B, q.Prime) →
      p₀ ∈ A → 0 < (b p₀).natAbs →
      ∏ p ∈ A, p ^ (b p).natAbs = ∏ p ∈ B, p ^ (b p).natAbs → False := by
    intro A B hAB hB hp₀A hexp heq
    have hdvdA : p₀ ∣ ∏ p ∈ A, p ^ (b p).natAbs :=
      dvd_trans (dvd_pow_self p₀ (by omega)) (Finset.dvd_prod_of_mem _ hp₀A)
    rw [heq] at hdvdA
    obtain ⟨q, hqB, hq_dvd⟩ := (Prime.dvd_finsetProd_iff hp₀pr.prime _).mp hdvdA
    have hq_eq : p₀ = q :=
      (Nat.prime_dvd_prime_iff_eq hp₀pr (hB q hqB)).mp (hp₀pr.dvd_of_dvd_pow hq_dvd)
    subst hq_eq
    exact Finset.disjoint_left.mp hAB hp₀A hqB
  rcases lt_or_gt_of_ne hp₀ne with hlt | hgt
  · exact hcontra Sneg Spos hdisj.symm (fun q hq => hS q (Finset.mem_filter.mp hq).1)
      (Finset.mem_filter.mpr ⟨hp₀S, hlt⟩) (Int.natAbs_pos.mpr hp₀ne) hPeq.symm
  · exact hcontra Spos Sneg hdisj (fun q hq => hS q (Finset.mem_filter.mp hq).1)
      (Finset.mem_filter.mpr ⟨hp₀S, hgt⟩) (Int.natAbs_pos.mpr hp₀ne) hPeq

/- Section 2: Siegel's Lemma over `ℤ` -/

lemma siegel_lemma {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℤ) (H : ℕ) (hH : ∀ j i, (A j i).natAbs ≤ H)
    (hcard : 0 < Fintype.card ι) (h2 : 2 * Fintype.card κ ≤ Fintype.card ι) :
    ∃ x : ι → ℤ, (∃ i, x i ≠ 0) ∧
      (∀ i, (x i).natAbs ≤ 2 * Fintype.card ι * H + 1) ∧
      (∀ j, ∑ i, A j i * x i = 0) := by
  classical
  set X := Fintype.card ι
  set Y := Fintype.card κ
  set M := 2 * X * H + 1
  have hMpos : 1 ≤ M := by omega
  set R := X * H * M
  let f : (ι → Fin (M + 1)) → (κ → Fin (2 * R + 1)) := fun v j =>
    let s : ℤ := ∑ i : ι, A j i * (v i : ℤ)
    ⟨(s + R).toNat, by
      have habs : |s| ≤ (R : ℤ) := by
        calc |s| = |∑ i : ι, A j i * (v i : ℤ)| := rfl
          _ ≤ ∑ i : ι, |A j i * (v i : ℤ)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : ι, ((H : ℤ) * (M : ℤ)) := by
              apply Finset.sum_le_sum
              intro i _
              rw [abs_mul]
              have h1 : |A j i| ≤ (H : ℤ) := by
                rw [← Int.natCast_natAbs]
                exact_mod_cast hH j i
              have h2v : |(v i : ℤ)| ≤ (M : ℤ) := by
                rw [abs_of_nonneg (Nat.cast_nonneg _)]
                exact_mod_cast Nat.lt_succ_iff.mp (v i).isLt
              exact mul_le_mul h1 h2v (abs_nonneg _) (Nat.cast_nonneg _)
          _ = (R : ℤ) := by
              simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, X, R]
              push_cast
              ring
      have hlo : -(R : ℤ) ≤ s := (abs_le.mp habs).1
      have hhi : s ≤ (R : ℤ) := (abs_le.mp habs).2
      omega⟩
  have hlt : Fintype.card (κ → Fin (2 * R + 1)) < Fintype.card (ι → Fin (M + 1)) := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    have hstep : 2 * R + 1 < (M + 1) ^ 2 := by
      have h2R : 2 * R = 2 * X * H * M := by dsimp only [R]; ring
      have hM : 2 * X * H + 1 = M := rfl
      nlinarith
    by_cases hY : Y = 0
    · change (2 * R + 1) ^ Y < (M + 1) ^ X
      rw [hY, pow_zero]
      exact one_lt_pow₀ (by omega : 1 < M + 1) (by omega)
    · calc (2 * R + 1) ^ Y
          < ((M + 1) ^ 2) ^ Y := Nat.pow_lt_pow_left hstep hY
        _ = (M + 1) ^ (2 * Y) := by rw [← pow_mul]
        _ ≤ (M + 1) ^ X := Nat.pow_le_pow_right (by omega) h2
  obtain ⟨v₁, v₂, hne, hfeq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt
  refine ⟨fun i => (v₁ i : ℤ) - (v₂ i : ℤ), ?_, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    apply hne
    funext i
    have hi := hall i
    ext
    omega
  · intro i
    have h1 := (v₁ i).isLt
    have h2i := (v₂ i).isLt
    have habs : |((v₁ i : ℤ) - (v₂ i : ℤ))| ≤ (M : ℤ) := by
      rw [abs_le]; constructor <;> omega
    exact Int.ofNat_le.mp (by rw [Int.natCast_natAbs]; exact habs)
  · intro j
    have hjeq := congr_fun hfeq j
    have hval := congr_arg Fin.val hjeq
    dsimp only [f] at hval
    have hbound : ∀ v : ι → Fin (M + 1), -(R : ℤ) ≤ ∑ i : ι, A j i * (v i : ℤ) := by
      intro v
      have habs : |∑ i : ι, A j i * (v i : ℤ)| ≤ (R : ℤ) := by
        calc |∑ i : ι, A j i * (v i : ℤ)|
            ≤ ∑ i : ι, |A j i * (v i : ℤ)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : ι, ((H : ℤ) * (M : ℤ)) := by
              apply Finset.sum_le_sum
              intro i _
              rw [abs_mul]
              have h1 : |A j i| ≤ (H : ℤ) := by
                rw [← Int.natCast_natAbs]; exact_mod_cast hH j i
              have h2v : |(v i : ℤ)| ≤ (M : ℤ) := by
                rw [abs_of_nonneg (Nat.cast_nonneg _)]
                exact_mod_cast Nat.lt_succ_iff.mp (v i).isLt
              exact mul_le_mul h1 h2v (abs_nonneg _) (Nat.cast_nonneg _)
          _ = (R : ℤ) := by
              simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, X, R]
              push_cast; ring
      exact (abs_le.mp habs).1
    have h1 := hbound v₁
    have h2v := hbound v₂
    have heqsum : ∑ i : ι, A j i * (v₁ i : ℤ) = ∑ i : ι, A j i * (v₂ i : ℤ) := by omega
    calc ∑ i : ι, A j i * ((v₁ i : ℤ) - (v₂ i : ℤ))
        = (∑ i : ι, A j i * (v₁ i : ℤ)) - (∑ i : ι, A j i * (v₂ i : ℤ)) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl; intro i _; ring
      _ = 0 := sub_eq_zero.mpr heqsum

/- Section 3: Feldman Block Polynomials, Denominators, and Algebraic Size Bounds -/

noncomputable def deltaPoly (a : ℕ) : Polynomial ℚ :=
  ((a.factorial : ℚ)⁻¹) • ∏ r ∈ Finset.range a, (X + C ((r + 1 : ℕ) : ℚ))

noncomputable def binomPoly (j : ℕ) : Polynomial ℚ :=
  ((j.factorial : ℚ)⁻¹) • ∏ r ∈ Finset.range j, (X - C (r : ℚ))

noncomputable def feldmanPoly (k l₀ : ℕ) : Polynomial ℚ :=
  (deltaPoly k) ^ (l₀ / k) * deltaPoly (l₀ % k)

lemma deltaPoly_zero : deltaPoly 0 = 1 := by
  simp [deltaPoly]

lemma binomPoly_zero : binomPoly 0 = 1 := by
  simp [binomPoly]

lemma natDegree_deltaPoly (a : ℕ) : (deltaPoly a).natDegree = a := by
  unfold deltaPoly
  have hfac : ((a.factorial : ℚ)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero a)
  rw [Polynomial.smul_eq_C_mul, natDegree_C_mul hfac]
  rw [natDegree_prod_of_monic _ _ fun r _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

lemma deltaPoly_ne_zero (a : ℕ) : deltaPoly a ≠ 0 := by
  unfold deltaPoly
  have hfac : ((a.factorial : ℚ)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero a)
  have hmon : (∏ r ∈ Finset.range a, (X + C ((r + 1 : ℕ) : ℚ))).Monic :=
    monic_prod_of_monic _ _ fun r _ => monic_X_add_C _
  exact smul_ne_zero hfac hmon.ne_zero

lemma natDegree_feldmanPoly {k : ℕ} (_hk : 0 < k) (l₀ : ℕ) :
    (feldmanPoly k l₀).natDegree = l₀ := by
  unfold feldmanPoly
  rw [natDegree_mul (pow_ne_zero _ (deltaPoly_ne_zero k)) (deltaPoly_ne_zero _),
    natDegree_pow, natDegree_deltaPoly, natDegree_deltaPoly]
  rw [mul_comm]
  exact Nat.div_add_mod l₀ k

lemma feldmanPoly_ne_zero (k l₀ : ℕ) : feldmanPoly k l₀ ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (deltaPoly_ne_zero k)) (deltaPoly_ne_zero _)

lemma sum_feldmanPoly_ne_zero {k L₀ : ℕ} (hk : 0 < k) (c : Fin (L₀ + 1) → ℚ)
    (hne : ∃ i, c i ≠ 0) :
    ∑ i : Fin (L₀ + 1), C (c i) * feldmanPoly k i.val ≠ 0 := by
  classical
  set S := Finset.univ.filter (fun i : Fin (L₀ + 1) => c i ≠ 0)
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  set imax := S.max' hSne
  have himax_mem : imax ∈ S := Finset.max'_mem S hSne
  have himax_ne : c imax ≠ 0 := (Finset.mem_filter.mp himax_mem).2
  have hterm_deg : (C (c imax) * feldmanPoly k imax.val).natDegree = imax.val := by
    rw [natDegree_C_mul himax_ne, natDegree_feldmanPoly hk]
  have hterm_ne : C (c imax) * feldmanPoly k imax.val ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr himax_ne) (feldmanPoly_ne_zero k _)
  have hsum_eq : ∑ i : Fin (L₀ + 1), C (c i) * feldmanPoly k i.val =
      C (c imax) * feldmanPoly k imax.val +
      ∑ i ∈ S.erase imax, C (c i) * feldmanPoly k i.val := by
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    · rw [← Finset.add_sum_erase _ _ himax_mem]
    · intro i _ hi
      have h0 : c i = 0 := by
        by_contra hc
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hc⟩)
      simp [h0]
  rw [hsum_eq]
  have hrest_deg : (∑ i ∈ S.erase imax, C (c i) * feldmanPoly k i.val).natDegree < imax.val ∨
      ∑ i ∈ S.erase imax, C (c i) * feldmanPoly k i.val = 0 := by
    by_cases h0 : ∑ i ∈ S.erase imax, C (c i) * feldmanPoly k i.val = 0
    · exact Or.inr h0
    · left
      have hlt : ∀ i ∈ S.erase imax, (C (c i) * feldmanPoly k i.val).natDegree < imax.val := by
        intro i hi
        have hiS : i ∈ S := Finset.mem_of_mem_erase hi
        have hine : i ≠ imax := Finset.ne_of_mem_erase hi
        have hle : i ≤ imax := Finset.le_max' S i hiS
        have hlt_i : i < imax := lt_of_le_of_ne hle hine
        have hci : c i ≠ 0 := (Finset.mem_filter.mp hiS).2
        rw [natDegree_C_mul hci, natDegree_feldmanPoly hk]
        exact hlt_i
      have hle_max := natDegree_sum_le (S.erase imax) (fun i => C (c i) * feldmanPoly k i.val)
      have hfold : (S.erase imax).fold max 0 (fun i => (C (c i) * feldmanPoly k i.val).natDegree) <
          imax.val := by
        rw [Finset.fold_max_lt]
        refine ⟨?_, hlt⟩
        have hne_er : (S.erase imax).Nonempty := by
          by_contra hem
          rw [Finset.not_nonempty_iff_eq_empty] at hem
          rw [hem, Finset.sum_empty] at h0
          exact h0 rfl
        obtain ⟨j, hj⟩ := hne_er
        exact lt_of_le_of_lt (Nat.zero_le _) (hlt j hj)
      exact lt_of_le_of_lt hle_max hfold
  rcases hrest_deg with hlt | h0
  · intro heq
    have hneg : C (c imax) * feldmanPoly k imax.val =
        -(∑ i ∈ S.erase imax, C (c i) * feldmanPoly k i.val) := eq_neg_of_add_eq_zero_left heq
    have hdeg := congr_arg Polynomial.natDegree hneg
    rw [natDegree_neg, hterm_deg] at hdeg
    omega
  · rw [h0, add_zero]
    exact hterm_ne

lemma eval_binomPoly_nat (j n : ℕ) : (binomPoly j).eval (n : ℚ) = (n.choose j : ℚ) := by
  unfold binomPoly
  rw [eval_smul, smul_eq_mul, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  have hprod : ∏ r ∈ Finset.range j, ((n : ℚ) - (r : ℚ)) = (n.descFactorial j : ℚ) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.prod_range_succ, ih, Nat.descFactorial_succ]
      by_cases hjn : j ≤ n
      · rw [Nat.cast_mul, Nat.cast_sub hjn, mul_comm]
      · have hzero : n.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
        simp [hzero]
  rw [hprod, inv_mul_eq_div, Nat.choose_eq_descFactorial_div_factorial]
  rw [Nat.cast_div (Nat.factorial_dvd_descFactorial n j) (by exact_mod_cast Nat.factorial_ne_zero j)]

lemma eval_deltaPoly_nat (a n : ℕ) : (deltaPoly a).eval (n : ℚ) = ((n + a).choose a : ℚ) := by
  unfold deltaPoly
  rw [eval_smul, smul_eq_mul, eval_prod]
  simp only [eval_add, eval_X, eval_C]
  have hprod : ∏ r ∈ Finset.range a, ((n : ℚ) + ((r + 1 : ℕ) : ℚ)) =
      ((n + a).descFactorial a : ℚ) := by
    have hnat : ∏ r ∈ Finset.range a, (n + (r + 1)) = (n + a).descFactorial a := by
      induction a with
      | zero => simp
      | succ a ih =>
        rw [Finset.prod_range_succ, ih, ← add_assoc, Nat.succ_descFactorial_succ, mul_comm]
    have hcast : ∏ r ∈ Finset.range a, ((n : ℚ) + ((r + 1 : ℕ) : ℚ)) =
        ((∏ r ∈ Finset.range a, (n + (r + 1)) : ℕ) : ℚ) := by
      push_cast; rfl
    rw [hcast, hnat]
  rw [hprod, inv_mul_eq_div, Nat.choose_eq_descFactorial_div_factorial]
  rw [Nat.cast_div (Nat.factorial_dvd_descFactorial (n + a) a)
    (by exact_mod_cast Nat.factorial_ne_zero a)]

lemma taylor_deltaPoly_eq (a s : ℕ) :
    Polynomial.taylor (s : ℚ) (deltaPoly a) =
      ∑ j ∈ Finset.range (a + 1), C (((s + a).choose (a - j) : ℕ) : ℚ) * binomPoly j := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := Set.range (fun n : ℕ => (n : ℚ))) ?_ ?_
  · intro x hx
    obtain ⟨n, rfl⟩ := hx
    simp only [Set.mem_ofPred_eq, Polynomial.taylor_apply, eval_comp, eval_add, eval_X, eval_C,
      eval_finsetSum, eval_mul]
    rw [show (n : ℚ) + (s : ℚ) = ((n + s : ℕ) : ℚ) by push_cast; ring]
    rw [eval_deltaPoly_nat]
    have hch : ((n + s + a).choose a : ℚ) =
        ∑ j ∈ Finset.range (a + 1), (((s + a).choose (a - j) : ℕ) : ℚ) * (n.choose j : ℚ) := by
      have h1 : n + s + a = (s + a) + n := by omega
      rw [h1, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      push_cast
      rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro j hj
      have hja : j ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hsub : a - (a - j) = j := by omega
      simp [hsub]
    rw [hch]
    apply Finset.sum_congr rfl
    intro j _
    rw [eval_binomPoly_nat]
  · exact Set.infinite_range_of_injective Nat.cast_injective

lemma dvd_lcmUpto {r k : ℕ} (hr1 : 1 ≤ r) (hrk : r ≤ k) : r ∣ Nat.lcmUpto k := by
  unfold Nat.lcmUpto
  exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hr1, hrk⟩)

lemma lcmUpto_pow_mul_coeff_binomPoly_int {k j m : ℕ} (hjk : j ≤ k) :
    ∃ z : ℤ, (z : ℚ) = ((Nat.lcmUpto k : ℚ) ^ m) * (binomPoly j).coeff m := by
  set d := Nat.lcmUpto k
  have hcomp_coeff : ((binomPoly j).comp (C (d : ℚ) * X)).coeff m =
      (d : ℚ) ^ m * (binomPoly j).coeff m := by
    rw [Polynomial.comp_C_mul_X_coeff]
    ring
  rw [← hcomp_coeff]
  suffices hmem : ∃ P : Polynomial ℤ, P.map (Int.castRingHom ℚ) =
      (binomPoly j).comp (C (d : ℚ) * X) by
    obtain ⟨P, hP⟩ := hmem
    refine ⟨P.coeff m, ?_⟩
    rw [← hP, Polynomial.coeff_map, Int.coe_castRingHom]
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · refine ⟨1, ?_⟩
    simp [binomPoly_zero]
  · have hfac : (j.factorial : ℚ) = (j : ℚ) * ∏ r ∈ Finset.Ico 1 j, (r : ℚ) := by
      have hnat : j.factorial = j * ∏ r ∈ Finset.Ico 1 j, r := by
        cases j with
        | zero => omega
        | succ j' =>
          rw [Nat.factorial_succ]
          congr 1
          clear hcomp_coeff hjpos hjk
          induction j' with
          | zero => simp
          | succ t ih =>
            rw [Nat.factorial_succ, ih]
            have hIco : Finset.Ico 1 (t + 2) = insert (t + 1) (Finset.Ico 1 (t + 1)) := by
              ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
            rw [hIco, Finset.prod_insert (by simp)]
      rw [← Nat.cast_prod, ← Nat.cast_mul]
      exact_mod_cast hnat
    have hprod_split : ∏ r ∈ Finset.range j, (X - C (r : ℚ)) =
        X * ∏ r ∈ Finset.Ico 1 j, (X - C (r : ℚ)) := by
      have hrg : Finset.range j = insert 0 (Finset.Ico 1 j) := by
        ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
      rw [hrg, Finset.prod_insert (by simp), Nat.cast_zero, C_0, sub_zero]
    have hbinom_eq : binomPoly j =
        (C ((j : ℚ)⁻¹) * X) * ∏ r ∈ Finset.Ico 1 j, (C ((r : ℚ)⁻¹) * X - 1) := by
      unfold binomPoly
      rw [hprod_split, hfac, mul_inv, Polynomial.smul_eq_C_mul, C_mul, ← Finset.prod_inv_distrib]
      have h1 : C (∏ r ∈ Finset.Ico 1 j, (r : ℚ)⁻¹) * (∏ r ∈ Finset.Ico 1 j, (X - C (r : ℚ))) =
          ∏ r ∈ Finset.Ico 1 j, (C ((r : ℚ)⁻¹) * X - 1) := by
        rw [map_prod, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro r hr
        have hr0 : (r : ℚ) ≠ 0 := by
          have := (Finset.mem_Ico.mp hr).1
          exact_mod_cast (by omega : r ≠ 0)
        rw [mul_sub, ← C_mul, inv_mul_cancel₀ hr0, C_1]
      calc (C (j : ℚ)⁻¹ * C (∏ r ∈ Finset.Ico 1 j, (r : ℚ)⁻¹)) *
            (X * ∏ r ∈ Finset.Ico 1 j, (X - C (r : ℚ)))
          = (C (j : ℚ)⁻¹ * X) *
            (C (∏ r ∈ Finset.Ico 1 j, (r : ℚ)⁻¹) * ∏ r ∈ Finset.Ico 1 j, (X - C (r : ℚ))) := by ring
        _ = (C (j : ℚ)⁻¹ * X) * ∏ r ∈ Finset.Ico 1 j, (C ((r : ℚ)⁻¹) * X - 1) := by rw [h1]
    have hdvd_j : j ∣ d := dvd_lcmUpto hjpos hjk
    refine ⟨(C ((d / j : ℕ) : ℤ) * X) * ∏ r ∈ Finset.Ico 1 j, (C ((d / r : ℕ) : ℤ) * X - 1), ?_⟩
    rw [hbinom_eq, Polynomial.mul_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
      Polynomial.prod_comp]
    simp only [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_C,
      Polynomial.map_X, Polynomial.map_one, Int.coe_castRingHom, Int.cast_natCast]
    congr 1
    · rw [← mul_assoc, ← C_mul]
      have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
      have hq : ((d / j : ℕ) : ℚ) = (j : ℚ)⁻¹ * (d : ℚ) := by
        rw [Nat.cast_div hdvd_j hj0, div_eq_inv_mul]
      rw [hq]
    · apply Finset.prod_congr rfl
      intro r hr
      rw [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
        Polynomial.one_comp, ← mul_assoc, ← C_mul]
      have hr1 : 1 ≤ r := (Finset.mem_Ico.mp hr).1
      have hrk : r ≤ k := le_trans (le_of_lt (Finset.mem_Ico.mp hr).2) hjk
      have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
      have hq : ((d / r : ℕ) : ℚ) = (r : ℚ)⁻¹ * (d : ℚ) := by
        rw [Nat.cast_div (dvd_lcmUpto hr1 hrk) hr0, div_eq_inv_mul]
      rw [hq]

lemma lcmUpto_pow_mul_hasseDeriv_deltaPoly_int {k a m s : ℕ} (hak : a ≤ k) :
    ∃ z : ℤ, (z : ℚ) = ((Nat.lcmUpto k : ℚ) ^ m) * (Polynomial.hasseDeriv m (deltaPoly a)).eval (s : ℚ) := by
  rw [← Polynomial.taylor_coeff, taylor_deltaPoly_eq, Polynomial.finsetSum_coeff, Finset.mul_sum]
  have hterm : ∀ j ∈ Finset.range (a + 1), ∃ z : ℤ,
      (z : ℚ) = (Nat.lcmUpto k : ℚ) ^ m * (C (((s + a).choose (a - j) : ℕ) : ℚ) * binomPoly j).coeff m := by
    intro j hj
    have hjk : j ≤ k := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hak
    obtain ⟨z, hz⟩ := lcmUpto_pow_mul_coeff_binomPoly_int (m := m) hjk
    refine ⟨(((s + a).choose (a - j) : ℕ) : ℤ) * z, ?_⟩
    rw [Polynomial.coeff_C_mul, Int.cast_mul, Int.cast_natCast, hz]
    ring
  choose f hf using hterm
  refine ⟨∑ j ∈ (Finset.range (a + 1)).attach, f j.1 j.2, ?_⟩
  rw [Int.cast_sum, ← Finset.sum_attach (Finset.range (a + 1))]
  apply Finset.sum_congr rfl
  intro j _
  exact hf j.1 j.2

lemma lcmUpto_pow_mul_hasseDeriv_mul_int {k s : ℕ} {P Q : Polynomial ℚ}
    (hP : ∀ m, ∃ z : ℤ, (z : ℚ) = ((Nat.lcmUpto k : ℚ) ^ m) * (Polynomial.hasseDeriv m P).eval (s : ℚ))
    (hQ : ∀ m, ∃ z : ℤ, (z : ℚ) = ((Nat.lcmUpto k : ℚ) ^ m) * (Polynomial.hasseDeriv m Q).eval (s : ℚ))
    (m : ℕ) :
    ∃ z : ℤ, (z : ℚ) = ((Nat.lcmUpto k : ℚ) ^ m) * (Polynomial.hasseDeriv m (P * Q)).eval (s : ℚ) := by
  rw [Polynomial.hasseDeriv_mul, Polynomial.eval_finsetSum, Finset.mul_sum]
  have hterm : ∀ ij ∈ Finset.HasAntidiagonal.antidiagonal m, ∃ z : ℤ,
      (z : ℚ) = (Nat.lcmUpto k : ℚ) ^ m *
        ((Polynomial.hasseDeriv ij.1 P * Polynomial.hasseDeriv ij.2 Q).eval (s : ℚ)) := by
    intro ij hij
    obtain ⟨z₁, hz₁⟩ := hP ij.1
    obtain ⟨z₂, hz₂⟩ := hQ ij.2
    refine ⟨z₁ * z₂, ?_⟩
    rw [Int.cast_mul, hz₁, hz₂, Polynomial.eval_mul]
    have hsum : ij.1 + ij.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    rw [← hsum, pow_add]
    ring
  choose f hf using hterm
  refine ⟨∑ ij ∈ (Finset.HasAntidiagonal.antidiagonal m).attach, f ij.1 ij.2, ?_⟩
  rw [Int.cast_sum, ← Finset.sum_attach (Finset.HasAntidiagonal.antidiagonal m)]
  apply Finset.sum_congr rfl
  intro ij _
  exact hf ij.1 ij.2

lemma lcmUpto_pow_mul_hasseDeriv_pow_int {k s : ℕ} {P : Polynomial ℚ}
    (hP : ∀ m, ∃ z : ℤ, (z : ℚ) = ((Nat.lcmUpto k : ℚ) ^ m) * (Polynomial.hasseDeriv m P).eval (s : ℚ))
    (q m : ℕ) :
    ∃ z : ℤ, (z : ℚ) = ((Nat.lcmUpto k : ℚ) ^ m) * (Polynomial.hasseDeriv m (P ^ q)).eval (s : ℚ) := by
  induction q generalizing m with
  | zero =>
    rw [pow_zero]
    cases m with
    | zero => exact ⟨1, by simp⟩
    | succ m =>
      refine ⟨0, ?_⟩
      have h0 : Polynomial.hasseDeriv (m + 1) (1 : Polynomial ℚ) = 0 := by
        ext j
        rw [Polynomial.hasseDeriv_coeff, Polynomial.coeff_zero]
        have hlt : 1 ≤ j + (m + 1) := by omega
        rw [Polynomial.coeff_one, if_neg (by omega), mul_zero]
      rw [h0, Polynomial.eval_zero, mul_zero, Int.cast_zero]
  | succ q ih =>
    rw [pow_succ]
    exact lcmUpto_pow_mul_hasseDeriv_mul_int ih hP m

lemma lcmUpto_pow_mul_hasseDeriv_feldmanPoly_int {k : ℕ} (hk : 0 < k) (l₀ m s : ℕ) :
    ∃ z : ℤ, (z : ℚ) = ((Nat.lcmUpto k : ℚ) ^ m) *
      (Polynomial.hasseDeriv m (feldmanPoly k l₀)).eval (s : ℚ) := by
  unfold feldmanPoly
  apply lcmUpto_pow_mul_hasseDeriv_mul_int
  · exact lcmUpto_pow_mul_hasseDeriv_pow_int
      (fun r => lcmUpto_pow_mul_hasseDeriv_deltaPoly_int le_rfl) _
  · exact fun r => lcmUpto_pow_mul_hasseDeriv_deltaPoly_int (le_of_lt (Nat.mod_lt l₀ hk))

lemma log_lcmUpto_le (k : ℕ) : Real.log (Nat.lcmUpto k : ℝ) ≤ 6 * (k : ℝ) := by
  rw [← Chebyshev.psi_eq_log_lcmUpto]
  have h1 := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg k)
  have hlog4 : Real.log 4 < 2 := by
    have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h4, Real.log_pow]
    push_cast
    have := Real.log_two_lt_d9
    linarith
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith

lemma lcmUpto_le_exp (k : ℕ) : (Nat.lcmUpto k : ℝ) ≤ Real.exp (6 * (k : ℝ)) := by
  have hpos : (0 : ℝ) < (Nat.lcmUpto k : ℝ) := by exact_mod_cast Nat.lcmUpto_pos k
  rw [← Real.log_le_iff_le_exp hpos]
  exact log_lcmUpto_le k

/- Purely algebraic coefficient majorant `normSum` for `feldmanPoly` -/

noncomputable def normSum (P : Polynomial ℂ) : ℝ :=
  ∑ m ∈ Finset.range (P.natDegree + 1), ‖P.coeff m‖

lemma normSum_nonneg (P : Polynomial ℂ) : 0 ≤ normSum P :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma normSum_eq_sum_of_natDegree_le {P : Polynomial ℂ} {N : ℕ} (hN : P.natDegree ≤ N) :
    normSum P = ∑ m ∈ Finset.range (N + 1), ‖P.coeff m‖ := by
  unfold normSum
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hN))
  intro m _ hm
  rw [Finset.mem_range] at hm
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]

lemma norm_coeff_le_normSum (P : Polynomial ℂ) (m : ℕ) : ‖P.coeff m‖ ≤ normSum P := by
  by_cases hm : m ≤ P.natDegree
  · exact Finset.single_le_sum (fun _ _ => norm_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]
    exact normSum_nonneg P

lemma normSum_smul (c : ℂ) (P : Polynomial ℂ) : normSum (c • P) = ‖c‖ * normSum P := by
  by_cases hc : c = 0
  · subst hc; simp [normSum]
  · rw [normSum_eq_sum_of_natDegree_le (Polynomial.natDegree_smul_le c P)]
    unfold normSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [Polynomial.coeff_smul, smul_eq_mul, norm_mul]

lemma normSum_X_add_C (a : ℂ) : normSum (X + C a) ≤ 1 + ‖a‖ := by
  rw [normSum_eq_sum_of_natDegree_le (show (X + C a).natDegree ≤ 1 by
    exact le_trans (Polynomial.natDegree_add_le _ _) (by simp))]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [zero_add, Polynomial.coeff_add, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
    Polynomial.coeff_X_one, Polynomial.coeff_C_succ, add_zero, norm_one]
  linarith

lemma normSum_mul_le (P Q : Polynomial ℂ) : normSum (P * Q) ≤ normSum P * normSum Q := by
  set N := P.natDegree + Q.natDegree
  rw [normSum_eq_sum_of_natDegree_le (Polynomial.natDegree_mul_le)]
  calc ∑ m ∈ Finset.range (N + 1), ‖(P * Q).coeff m‖
      ≤ ∑ m ∈ Finset.range (N + 1),
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m, ‖P.coeff ij.1‖ * ‖Q.coeff ij.2‖ := by
        apply Finset.sum_le_sum
        intro m _
        rw [Polynomial.coeff_mul]
        calc ‖∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m, P.coeff ij.1 * Q.coeff ij.2‖
            ≤ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m, ‖P.coeff ij.1 * Q.coeff ij.2‖ :=
              norm_sum_le _ _
          _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m, ‖P.coeff ij.1‖ * ‖Q.coeff ij.2‖ := by
              apply Finset.sum_congr rfl; intro ij _; rw [norm_mul]
    _ = (∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖) *
        (∑ j ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff j‖) := by
        rw [Finset.sum_mul_sum]
        set S := (Finset.range (P.natDegree + 1)) ×ˢ (Finset.range (Q.natDegree + 1))
        calc ∑ m ∈ Finset.range (N + 1),
              ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m, ‖P.coeff ij.1‖ * ‖Q.coeff ij.2‖
            = ∑ m ∈ Finset.range (N + 1),
              ∑ ij ∈ (Finset.HasAntidiagonal.antidiagonal m).filter (· ∈ S),
                ‖P.coeff ij.1‖ * ‖Q.coeff ij.2‖ := by
              apply Finset.sum_congr rfl
              intro m _
              symm
              apply Finset.sum_subset (Finset.filter_subset _ _)
              intro ij hij_mem hij
              have hnotS : ij ∉ S := fun hS => hij (Finset.mem_filter.mpr ⟨hij_mem, hS⟩)
              simp only [S, Finset.mem_product, Finset.mem_range, not_and] at hnotS
              by_cases h1 : ij.1 < P.natDegree + 1
              · have h2 : ¬ (ij.2 < Q.natDegree + 1) := hnotS h1
                rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := Q) (by omega), norm_zero, mul_zero]
              · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := P) (by omega), norm_zero, zero_mul]
          _ = ∑ ij ∈ S, ‖P.coeff ij.1‖ * ‖Q.coeff ij.2‖ := by
              rw [← Finset.sum_biUnion]
              · congr 1
                ext ij
                simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter,
                  Finset.HasAntidiagonal.mem_antidiagonal, S, Finset.mem_product]
                constructor
                · rintro ⟨_, _, _, hmem⟩; exact hmem
                · intro hmem
                  exact ⟨ij.1 + ij.2, by omega, rfl, hmem⟩
              · intro m₁ _ m₂ _ hne
                change Disjoint _ _
                rw [Finset.disjoint_left]
                intro ij h1 h2
                rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at h1 h2
                exact hne (h1.1.symm.trans h2.1)
          _ = ∑ i ∈ Finset.range (P.natDegree + 1),
              ∑ j ∈ Finset.range (Q.natDegree + 1), ‖P.coeff i‖ * ‖Q.coeff j‖ :=
              Finset.sum_product (Finset.range (P.natDegree + 1)) (Finset.range (Q.natDegree + 1))
                (fun ij => ‖P.coeff ij.1‖ * ‖Q.coeff ij.2‖)

lemma normSum_one : normSum 1 = 1 := by
  simp [normSum]

lemma normSum_prod_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ) :
    normSum (∏ i ∈ s, f i) ≤ ∏ i ∈ s, normSum (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [normSum_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact le_trans (normSum_mul_le _ _)
      (mul_le_mul_of_nonneg_left ih (normSum_nonneg _))

lemma normSum_pow_le (P : Polynomial ℂ) (q : ℕ) : normSum (P ^ q) ≤ (normSum P) ^ q := by
  induction q with
  | zero => simp [normSum_one]
  | succ q ih =>
    rw [pow_succ, pow_succ]
    exact le_trans (normSum_mul_le _ _) (mul_le_mul_of_nonneg_right ih (normSum_nonneg _))

lemma pow_div_factorial_mono {X : ℝ} (hX : 0 ≤ X) {a k : ℕ} (hak : a ≤ k) :
    (X + (a : ℝ)) ^ a / (a.factorial : ℝ) ≤ (X + (k : ℝ)) ^ k / (k.factorial : ℝ) := by
  induction hak with
  | refl => exact le_rfl
  | @step m hm ih =>
    refine le_trans ih ?_
    have h1 : (1 : ℝ) ≤ (X + ((m + 1 : ℕ) : ℝ)) / ((m + 1 : ℕ) : ℝ) := by
      rw [one_le_div (by positivity)]
      push_cast; linarith
    have h2 : (X + (m : ℝ)) ^ m ≤ (X + ((m + 1 : ℕ) : ℝ)) ^ m := by
      apply pow_le_pow_left₀ (by positivity)
      push_cast; linarith
    have hfac : (((m + 1).factorial : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
    calc (X + (m : ℝ)) ^ m / (m.factorial : ℝ)
        = (X + (m : ℝ)) ^ m / (m.factorial : ℝ) * 1 := (mul_one _).symm
      _ ≤ (X + ((m + 1 : ℕ) : ℝ)) ^ m / (m.factorial : ℝ) *
          ((X + ((m + 1 : ℕ) : ℝ)) / ((m + 1 : ℕ) : ℝ)) := by
          apply mul_le_mul (div_le_div_of_nonneg_right h2 (by positivity)) h1 zero_le_one
            (by positivity)
      _ = (X + ((m + 1 : ℕ) : ℝ)) ^ (m + 1) / (((m + 1).factorial : ℕ) : ℝ) := by
          rw [pow_succ, hfac]; ring

lemma pow_div_factorial_le_exp_pow {X : ℝ} (hX : 0 ≤ X) {k : ℕ} (hk : 0 < k) :
    (X + (k : ℝ)) ^ k / (k.factorial : ℝ) ≤ (Real.exp 1 * (X + (k : ℝ)) / (k : ℝ)) ^ k := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hexp : (k : ℝ) ^ k / (k.factorial : ℝ) ≤ Real.exp (k : ℝ) := by
    have h := Real.sum_le_exp_of_nonneg hkpos.le (k + 1)
    exact le_trans (Finset.single_le_sum
      (f := fun i => (k : ℝ) ^ i / (i.factorial : ℝ))
      (fun i _ => div_nonneg (pow_nonneg hkpos.le _) (Nat.cast_nonneg _))
      (Finset.mem_range.mpr (Nat.lt_succ_self k))) h
  have hfac_inv : ((k.factorial : ℝ))⁻¹ ≤ (Real.exp 1 / (k : ℝ)) ^ k := by
    rw [div_pow, ← Real.exp_nat_mul, mul_one]
    rw [le_div_iff₀ (pow_pos hkpos k), inv_mul_eq_div]
    exact hexp
  calc (X + (k : ℝ)) ^ k / (k.factorial : ℝ)
      = (X + (k : ℝ)) ^ k * ((k.factorial : ℝ))⁻¹ := div_eq_mul_inv _ _
    _ ≤ (X + (k : ℝ)) ^ k * (Real.exp 1 / (k : ℝ)) ^ k :=
        mul_le_mul_of_nonneg_left hfac_inv (by positivity)
    _ = (Real.exp 1 * (X + (k : ℝ)) / (k : ℝ)) ^ k := by
        rw [← mul_pow]; ring_nf

lemma normSum_taylor_deltaPoly_le {a k : ℕ} (hk : 0 < k) (hak : a ≤ k) (z : ℂ) {R : ℝ}
    (hR : ‖z‖ ≤ R) :
    normSum (Polynomial.taylor z ((deltaPoly a).map (algebraMap ℚ ℂ))) ≤
      (Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ)) ^ k := by
  have hR0 : 0 ≤ R := le_trans (norm_nonneg z) hR
  unfold deltaPoly
  rw [Polynomial.map_smul, Polynomial.map_prod, Polynomial.taylor_apply,
    Polynomial.smul_comp, Polynomial.prod_comp, normSum_smul]
  have hnorm_smul : ‖(algebraMap ℚ ℂ) ((a.factorial : ℚ)⁻¹)‖ = ((a.factorial : ℝ))⁻¹ := by
    simp
  have hprod : normSum (∏ r ∈ Finset.range a,
      (Polynomial.map (algebraMap ℚ ℂ) (X + C ((r + 1 : ℕ) : ℚ))).comp (X + C z)) ≤
      (R + 1 + (a : ℝ)) ^ a := by
    calc normSum (∏ r ∈ Finset.range a,
            (Polynomial.map (algebraMap ℚ ℂ) (X + C ((r + 1 : ℕ) : ℚ))).comp (X + C z))
        ≤ ∏ r ∈ Finset.range a,
            normSum ((Polynomial.map (algebraMap ℚ ℂ) (X + C ((r + 1 : ℕ) : ℚ))).comp (X + C z)) :=
          normSum_prod_le _ _
      _ ≤ ∏ _r ∈ Finset.range a, (R + 1 + (a : ℝ)) := by
          apply Finset.prod_le_prod (fun _ _ => normSum_nonneg _)
          intro r hr
          have hra : r + 1 ≤ a := Finset.mem_range.mp hr
          have heq : (Polynomial.map (algebraMap ℚ ℂ) (X + C ((r + 1 : ℕ) : ℚ))).comp (X + C z) =
              X + C (z + ((r + 1 : ℕ) : ℂ)) := by
            simp [Polynomial.add_comp, Polynomial.X_comp, add_assoc]
          rw [heq]
          calc normSum (X + C (z + ((r + 1 : ℕ) : ℂ)))
              ≤ 1 + ‖z + ((r + 1 : ℕ) : ℂ)‖ := normSum_X_add_C _
            _ ≤ 1 + (‖z‖ + ‖((r + 1 : ℕ) : ℂ)‖) := by
                linarith [norm_add_le z ((r + 1 : ℕ) : ℂ)]
            _ ≤ R + 1 + (a : ℝ) := by
                rw [Complex.norm_natCast]
                have hle : ((r + 1 : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast hra
                linarith
      _ = (R + 1 + (a : ℝ)) ^ a := by simp
  have hstep : ‖(algebraMap ℚ ℂ) ((a.factorial : ℚ)⁻¹)‖ *
      normSum (∏ r ∈ Finset.range a,
        (Polynomial.map (algebraMap ℚ ℂ) (X + C ((r + 1 : ℕ) : ℚ))).comp (X + C z)) ≤
      (R + 1 + (a : ℝ)) ^ a / (a.factorial : ℝ) := by
    rw [hnorm_smul, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hprod (by positivity)
  calc ‖(algebraMap ℚ ℂ) ((a.factorial : ℚ)⁻¹)‖ *
        normSum (∏ r ∈ Finset.range a,
          (Polynomial.map (algebraMap ℚ ℂ) (X + C ((r + 1 : ℕ) : ℚ))).comp (X + C z))
      ≤ (R + 1 + (a : ℝ)) ^ a / (a.factorial : ℝ) := hstep
    _ ≤ (R + 1 + (k : ℝ)) ^ k / (k.factorial : ℝ) :=
          pow_div_factorial_mono (by linarith) hak
    _ ≤ (Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ)) ^ k :=
          pow_div_factorial_le_exp_pow (by linarith) hk

lemma norm_eval_hasseDeriv_feldmanPoly_le {k L₀ l₀ m : ℕ} (hk : 0 < k) (hl : l₀ ≤ L₀)
    (z : ℂ) {R : ℝ} (hR : ‖z‖ ≤ R) :
    ‖((Polynomial.hasseDeriv m (feldmanPoly k l₀)).map (algebraMap ℚ ℂ)).eval z‖ ≤
      (Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k) := by
  have hR0 : 0 ≤ R := le_trans (norm_nonneg z) hR
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hbase_ge1 : (1 : ℝ) ≤ Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ) := by
    rw [one_le_div hkpos]
    have he1 : (1 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    nlinarith
  rw [← Polynomial.hasseDeriv_map, ← Polynomial.taylor_coeff]
  refine le_trans (norm_coeff_le_normSum _ m) ?_
  unfold feldmanPoly
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.taylor_apply,
    Polynomial.mul_comp, Polynomial.pow_comp]
  have h1 := normSum_taylor_deltaPoly_le hk le_rfl z hR
  have h2 := normSum_taylor_deltaPoly_le hk (le_of_lt (Nat.mod_lt l₀ hk)) z hR
  rw [Polynomial.taylor_apply] at h1 h2
  calc normSum (((deltaPoly k).map (algebraMap ℚ ℂ)).comp (X + C z) ^ (l₀ / k) *
          ((deltaPoly (l₀ % k)).map (algebraMap ℚ ℂ)).comp (X + C z))
      ≤ normSum (((deltaPoly k).map (algebraMap ℚ ℂ)).comp (X + C z) ^ (l₀ / k)) *
        normSum (((deltaPoly (l₀ % k)).map (algebraMap ℚ ℂ)).comp (X + C z)) :=
          normSum_mul_le _ _
    _ ≤ (normSum (((deltaPoly k).map (algebraMap ℚ ℂ)).comp (X + C z))) ^ (l₀ / k) *
        normSum (((deltaPoly (l₀ % k)).map (algebraMap ℚ ℂ)).comp (X + C z)) :=
          mul_le_mul_of_nonneg_right (normSum_pow_le _ _) (normSum_nonneg _)
    _ ≤ ((Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ)) ^ k) ^ (l₀ / k) *
        (Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ)) ^ k := by
          exact mul_le_mul (pow_le_pow_left₀ (normSum_nonneg _) h1 _) h2 (normSum_nonneg _)
            (by positivity)
    _ = (Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ)) ^ (k * (l₀ / k) + k) := by
          rw [← pow_mul, ← pow_add]
    _ ≤ (Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k) := by
          apply pow_le_pow_right₀ hbase_ge1
          have hdiv : k * (l₀ / k) ≤ l₀ := Nat.mul_div_le l₀ k
          omega

/- Section 4: Zero-Contour-Integral Hermite–Schwarz Extrapolation Lemma -/

noncomputable def normSumHalf (P : Polynomial ℂ) : ℝ :=
  ∑ m ∈ Finset.range (P.natDegree + 1), ‖P.coeff m‖ * ((1 / 2 : ℝ) ^ m)

lemma normSumHalf_nonneg (P : Polynomial ℂ) : 0 ≤ normSumHalf P :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (by positivity)

lemma normSumHalf_eq_sum_of_natDegree_le {P : Polynomial ℂ} {N : ℕ} (hN : P.natDegree ≤ N) :
    normSumHalf P = ∑ m ∈ Finset.range (N + 1), ‖P.coeff m‖ * ((1 / 2 : ℝ) ^ m) := by
  unfold normSumHalf
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hN))
  intro m _ hm
  rw [Finset.mem_range] at hm
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), norm_zero, zero_mul]

lemma norm_coeff_le_two_pow_mul_normSumHalf (P : Polynomial ℂ) (m : ℕ) :
    ‖P.coeff m‖ ≤ (2 : ℝ) ^ m * normSumHalf P := by
  have hterm : ‖P.coeff m‖ * ((1 / 2 : ℝ) ^ m) ≤ normSumHalf P := by
    by_cases hm : m ≤ P.natDegree
    · exact Finset.single_le_sum (fun _ _ => mul_nonneg (norm_nonneg _) (by positivity))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), norm_zero, zero_mul]
      exact normSumHalf_nonneg P
  have hmul := mul_le_mul_of_nonneg_left hterm (show (0 : ℝ) ≤ (2 : ℝ) ^ m by positivity)
  have hcancel : (2 : ℝ) ^ m * (‖P.coeff m‖ * (1 / 2 : ℝ) ^ m) = ‖P.coeff m‖ := by
    rw [mul_left_comm, ← mul_pow]
    norm_num
  linarith

lemma normSumHalf_one : normSumHalf 1 = 1 := by
  simp [normSumHalf]

lemma normSumHalf_mul_le (P Q : Polynomial ℂ) :
    normSumHalf (P * Q) ≤ normSumHalf P * normSumHalf Q := by
  set N := P.natDegree + Q.natDegree
  rw [normSumHalf_eq_sum_of_natDegree_le Polynomial.natDegree_mul_le]
  calc ∑ m ∈ Finset.range (N + 1), ‖(P * Q).coeff m‖ * (1 / 2 : ℝ) ^ m
      ≤ ∑ m ∈ Finset.range (N + 1),
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m,
            (‖P.coeff ij.1‖ * (1 / 2 : ℝ) ^ ij.1) * (‖Q.coeff ij.2‖ * (1 / 2 : ℝ) ^ ij.2) := by
        apply Finset.sum_le_sum
        intro m _
        rw [Polynomial.coeff_mul]
        calc ‖∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m, P.coeff ij.1 * Q.coeff ij.2‖ * (1 / 2 : ℝ) ^ m
            ≤ (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m, ‖P.coeff ij.1 * Q.coeff ij.2‖) * (1 / 2 : ℝ) ^ m :=
              mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
          _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m,
                (‖P.coeff ij.1‖ * (1 / 2 : ℝ) ^ ij.1) * (‖Q.coeff ij.2‖ * (1 / 2 : ℝ) ^ ij.2) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro ij hij
              have hsum : ij.1 + ij.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
              rw [norm_mul, ← hsum, pow_add]; ring
    _ = normSumHalf P * normSumHalf Q := by
        unfold normSumHalf
        rw [Finset.sum_mul_sum]
        set S := (Finset.range (P.natDegree + 1)) ×ˢ (Finset.range (Q.natDegree + 1))
        calc ∑ m ∈ Finset.range (N + 1),
              ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m,
                (‖P.coeff ij.1‖ * (1 / 2 : ℝ) ^ ij.1) * (‖Q.coeff ij.2‖ * (1 / 2 : ℝ) ^ ij.2)
            = ∑ m ∈ Finset.range (N + 1),
              ∑ ij ∈ (Finset.HasAntidiagonal.antidiagonal m).filter (· ∈ S),
                (‖P.coeff ij.1‖ * (1 / 2 : ℝ) ^ ij.1) * (‖Q.coeff ij.2‖ * (1 / 2 : ℝ) ^ ij.2) := by
              apply Finset.sum_congr rfl
              intro m _
              symm
              apply Finset.sum_subset (Finset.filter_subset _ _)
              intro ij hij_mem hij
              have hnotS : ij ∉ S := fun hS => hij (Finset.mem_filter.mpr ⟨hij_mem, hS⟩)
              simp only [S, Finset.mem_product, Finset.mem_range, not_and] at hnotS
              by_cases h1 : ij.1 < P.natDegree + 1
              · have h2 : ¬ (ij.2 < Q.natDegree + 1) := hnotS h1
                rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := Q) (by omega), norm_zero, zero_mul, mul_zero]
              · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := P) (by omega), norm_zero, zero_mul, zero_mul]
          _ = ∑ ij ∈ S,
                (‖P.coeff ij.1‖ * (1 / 2 : ℝ) ^ ij.1) * (‖Q.coeff ij.2‖ * (1 / 2 : ℝ) ^ ij.2) := by
              rw [← Finset.sum_biUnion]
              · congr 1
                ext ij
                simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter,
                  Finset.HasAntidiagonal.mem_antidiagonal, S, Finset.mem_product]
                constructor
                · rintro ⟨_, _, _, hmem⟩; exact hmem
                · intro hmem; exact ⟨ij.1 + ij.2, by omega, rfl, hmem⟩
              · intro m₁ _ m₂ _ hne
                change Disjoint _ _
                rw [Finset.disjoint_left]
                intro ij h1 h2
                rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at h1 h2
                exact hne (h1.1.symm.trans h2.1)
          _ = ∑ i ∈ Finset.range (P.natDegree + 1),
              ∑ j ∈ Finset.range (Q.natDegree + 1),
                (‖P.coeff i‖ * (1 / 2 : ℝ) ^ i) * (‖Q.coeff j‖ * (1 / 2 : ℝ) ^ j) :=
              Finset.sum_product (Finset.range (P.natDegree + 1)) (Finset.range (Q.natDegree + 1))
                (fun ij => (‖P.coeff ij.1‖ * (1 / 2 : ℝ) ^ ij.1) * (‖Q.coeff ij.2‖ * (1 / 2 : ℝ) ^ ij.2))

lemma normSumHalf_prod_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ) :
    normSumHalf (∏ i ∈ s, f i) ≤ ∏ i ∈ s, normSumHalf (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [normSumHalf_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact le_trans (normSumHalf_mul_le _ _)
      (mul_le_mul_of_nonneg_left ih (normSumHalf_nonneg _))

lemma normSumHalf_pow_le (P : Polynomial ℂ) (q : ℕ) :
    normSumHalf (P ^ q) ≤ (normSumHalf P) ^ q := by
  induction q with
  | zero => simp [normSumHalf_one]
  | succ q ih =>
    rw [pow_succ, pow_succ]
    exact le_trans (normSumHalf_mul_le _ _) (mul_le_mul_of_nonneg_right ih (normSumHalf_nonneg _))

noncomputable def truncPoly (S : ℕ) (P : Polynomial ℂ) : Polynomial ℂ :=
  ∑ m ∈ Finset.range S, C (P.coeff m) * X ^ m

lemma coeff_truncPoly (S : ℕ) (P : Polynomial ℂ) (m : ℕ) :
    (truncPoly S P).coeff m = if m < S then P.coeff m else 0 := by
  unfold truncPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hm : m < S
  · rw [if_pos hm, Finset.sum_eq_single m]
    · simp
    · intro b _ hne; exact if_neg (Ne.symm hne)
    · intro hnot; exact False.elim (hnot (Finset.mem_range.mpr hm))
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro b hb
    have hlt : b < S := Finset.mem_range.mp hb
    exact if_neg (by omega)

lemma natDegree_truncPoly_le (S : ℕ) (P : Polynomial ℂ) :
    (truncPoly S P).natDegree ≤ S := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [coeff_truncPoly, if_neg (by omega)]

lemma normSumHalf_truncPoly_le (S : ℕ) (P : Polynomial ℂ) :
    normSumHalf (truncPoly S P) ≤ normSumHalf P := by
  set N := max S P.natDegree
  rw [normSumHalf_eq_sum_of_natDegree_le (le_trans (natDegree_truncPoly_le S P) (le_max_left _ _)),
    normSumHalf_eq_sum_of_natDegree_le (le_max_right S P.natDegree)]
  apply Finset.sum_le_sum
  intro m _
  rw [coeff_truncPoly]
  split_ifs
  · exact le_rfl
  · rw [norm_zero, zero_mul]
    exact mul_nonneg (norm_nonneg _) (by positivity)

lemma coeff_mul_eq_of_coeff_eq_lt {S : ℕ} {A B B' : Polynomial ℂ}
    (hB : ∀ m < S, B.coeff m = B'.coeff m) {m : ℕ} (hm : m < S) :
    (A * B).coeff m = (A * B').coeff m := by
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hsum : ij.1 + ij.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [hB ij.2 (by omega)]

lemma coeff_mul_eq_of_coeff_eq_lt_left {S : ℕ} {A A' B : Polynomial ℂ}
    (hA : ∀ m < S, A.coeff m = A'.coeff m) {m : ℕ} (hm : m < S) :
    (A * B).coeff m = (A' * B).coeff m := by
  rw [mul_comm A B, mul_comm A' B]
  exact coeff_mul_eq_of_coeff_eq_lt hA hm

lemma coeff_pow_eq_one_of_coeff_eq_one {S : ℕ} {P : Polynomial ℂ}
    (hP : ∀ m < S, P.coeff m = (1 : Polynomial ℂ).coeff m) (q : ℕ) :
    ∀ m < S, (P ^ q).coeff m = (1 : Polynomial ℂ).coeff m := by
  induction q with
  | zero => intro m _; simp
  | succ q ih =>
    intro m hm
    rw [pow_succ]
    calc (P ^ q * P).coeff m
        = (1 * P).coeff m := coeff_mul_eq_of_coeff_eq_lt_left ih hm
      _ = P.coeff m := by rw [one_mul]
      _ = (1 : Polynomial ℂ).coeff m := hP m hm

lemma coeff_prod_eq_one_of_coeff_eq_one {ι : Type*} (s : Finset ι) (S : ℕ) (f : ι → Polynomial ℂ)
    (hf : ∀ i ∈ s, ∀ m < S, (f i).coeff m = (1 : Polynomial ℂ).coeff m) :
    ∀ m < S, (∏ i ∈ s, f i).coeff m = (1 : Polynomial ℂ).coeff m := by
  classical
  induction s using Finset.induction_on with
  | empty => intro m _; simp
  | insert a s ha ih =>
    intro m hm
    rw [Finset.prod_insert ha]
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    calc (f a * ∏ i ∈ s, f i).coeff m
        = (1 * ∏ i ∈ s, f i).coeff m := coeff_mul_eq_of_coeff_eq_lt_left h1 hm
      _ = (∏ i ∈ s, f i).coeff m := by rw [one_mul]
      _ = (1 : Polynomial ℂ).coeff m := h2 m hm

noncomputable def invTrunc (S : ℕ) (c : ℂ) : Polynomial ℂ :=
  ∑ a ∈ Finset.range S, C (c⁻¹ * (-c⁻¹) ^ a) * X ^ a

lemma coeff_invTrunc (S : ℕ) (c : ℂ) (m : ℕ) :
    (invTrunc S c).coeff m = if m < S then c⁻¹ * (-c⁻¹) ^ m else 0 := by
  unfold invTrunc
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hm : m < S
  · rw [if_pos hm, Finset.sum_eq_single m]
    · simp
    · intro b _ hne; exact if_neg (Ne.symm hne)
    · intro hnot; exact False.elim (hnot (Finset.mem_range.mpr hm))
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro b hb
    have hlt : b < S := Finset.mem_range.mp hb
    exact if_neg (by omega)

lemma mul_invTrunc_coeff {S : ℕ} {c : ℂ} (hc : c ≠ 0) {m : ℕ} (hm : m < S) :
    ((C c + X) * invTrunc S c).coeff m = (1 : Polynomial ℂ).coeff m := by
  rw [add_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul, coeff_invTrunc, if_pos hm]
  cases m with
  | zero =>
    simp [mul_inv_cancel₀ hc]
  | succ m =>
    rw [Polynomial.coeff_X_mul, coeff_invTrunc, if_pos (by omega)]
    rw [pow_succ, Polynomial.coeff_one]
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    have h1 : c * (c⁻¹ * ((-c⁻¹) ^ m * (-c⁻¹))) = (-c⁻¹) ^ m * (-c⁻¹) := by
      rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    rw [h1]
    ring

lemma normSumHalf_invTrunc_le {S : ℕ} {c : ℂ} (hc : 1 ≤ ‖c‖) :
    normSumHalf (invTrunc S c) ≤ 2 / ‖c‖ := by
  have hcpos : 0 < ‖c‖ := lt_of_lt_of_le zero_lt_one hc
  have hdeg : (invTrunc S c).natDegree ≤ S := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm; rw [coeff_invTrunc, if_neg (by omega)]
  rw [normSumHalf_eq_sum_of_natDegree_le hdeg]
  calc ∑ m ∈ Finset.range (S + 1), ‖(invTrunc S c).coeff m‖ * (1 / 2 : ℝ) ^ m
      ≤ ∑ m ∈ Finset.range (S + 1), ‖c‖⁻¹ * (1 / 2 : ℝ) ^ m := by
        apply Finset.sum_le_sum
        intro m _
        rw [coeff_invTrunc]
        split_ifs
        · rw [norm_mul, norm_inv, norm_pow, norm_neg, norm_inv]
          have hpow : (‖c‖⁻¹) ^ m ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hc)
          have hmul : ‖c‖⁻¹ * (‖c‖⁻¹) ^ m ≤ ‖c‖⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
          rw [mul_one] at hmul
          exact mul_le_mul_of_nonneg_right hmul (by positivity)
        · rw [norm_zero, zero_mul]; positivity
    _ = ‖c‖⁻¹ * ∑ m ∈ Finset.range (S + 1), (1 / 2 : ℝ) ^ m := by rw [← Finset.mul_sum]
    _ ≤ ‖c‖⁻¹ * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [geom_sum_eq (by norm_num)]
        have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (S + 1) := by positivity
        have hrew : ((1 / 2 : ℝ) ^ (S + 1) - 1) / ((1 / 2 : ℝ) - 1) =
            2 * (1 - (1 / 2 : ℝ) ^ (S + 1)) := by ring
        rw [hrew]; linarith
    _ = 2 / ‖c‖ := by ring

/- Polynomial derivatives & iteratedDeriv -/

lemma derivative_hasseDeriv_eq (m : ℕ) (P : Polynomial ℂ) :
    Polynomial.derivative (Polynomial.hasseDeriv m P) =
      ((m + 1 : ℕ) : ℂ) • Polynomial.hasseDeriv (m + 1) P := by
  have h := LinearMap.congr_fun (Polynomial.hasseDeriv_comp (R := ℂ) 1 m) P
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, Polynomial.hasseDeriv_one] at h
  rw [h, add_comm 1 m, Nat.choose_one_right, nsmul_eq_mul, Polynomial.smul_eq_C_mul]
  simp

lemma hasDerivAt_eval_poly (P : Polynomial ℂ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => P.eval w) (P.derivative.eval z) z := by
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_id] using
    Polynomial.hasDerivAt_aeval P z

lemma iteratedDeriv_eval_poly (s : ℕ) (P : Polynomial ℂ) (z : ℂ) :
    iteratedDeriv s (fun w : ℂ => P.eval w) z =
      (s.factorial : ℂ) * (Polynomial.hasseDeriv s P).eval z := by
  induction s generalizing P z with
  | zero => simp
  | succ s ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun w : ℂ => P.eval w) = fun w : ℂ => P.derivative.eval w := by
      funext w; exact (hasDerivAt_eval_poly P w).deriv
    rw [hd, ih P.derivative z, ← Polynomial.hasseDeriv_one]
    have hcomp := LinearMap.congr_fun (Polynomial.hasseDeriv_comp (R := ℂ) s 1) P
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hcomp
    rw [hcomp, Polynomial.eval_smul, nsmul_eq_mul, Nat.choose_succ_self_right,
      Nat.factorial_succ]
    push_cast; ring

lemma iteratedDeriv_eval_poly_eq_factorial_mul_taylor_coeff (s : ℕ) (P : Polynomial ℂ) (a : ℂ) :
    iteratedDeriv s (fun w : ℂ => P.eval w) a =
      (s.factorial : ℂ) * (Polynomial.taylor a P).coeff s := by
  rw [iteratedDeriv_eval_poly, Polynomial.taylor_coeff]

/- Entire factorization via `dslope` -/

lemma iteratedDeriv_mul_linear (a : ℂ) {q : ℂ → ℂ} (hq : Differentiable ℂ q) (s : ℕ) :
    iteratedDeriv (s + 1) (fun z => (z - a) * q z) a =
      ((s + 1 : ℕ) : ℂ) * iteratedDeriv s q a := by
  have h1 : ContDiffAt ℂ (s + 1 : ℕ) (fun z : ℂ => z - a) a :=
    (differentiable_id.sub (differentiable_const a)).contDiff.contDiffAt
  have h2 : ContDiffAt ℂ (s + 1 : ℕ) q a := hq.contDiff.contDiffAt
  change iteratedDeriv (s + 1) ((fun z : ℂ => z - a) * q) a = _
  rw [iteratedDeriv_mul h1 h2]
  rw [Finset.sum_eq_single 1]
  · have hd1 : iteratedDeriv 1 (fun z : ℂ => z - a) a = 1 := by
      rw [iteratedDeriv_one]
      exact ((hasDerivAt_id a).sub_const a).deriv
    simp [hd1]
  · intro i hi hne
    have hle : i ≤ s + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rcases i with _ | i'
    · simp
    · rcases i' with _ | i''
      · exact False.elim (hne rfl)
      · have hzero : iteratedDeriv (i'' + 2) (fun z : ℂ => z - a) a = 0 := by
          rw [iteratedDeriv_succ', iteratedDeriv_succ']
          have hd1 : deriv (fun z : ℂ => z - a) = fun _ => (1 : ℂ) := by
            funext w; exact ((hasDerivAt_id w).sub_const a).deriv
          rw [hd1]
          have hd2 : deriv (fun _ : ℂ => (1 : ℂ)) = (0 : ℂ → ℂ) := by
            funext w; exact deriv_const w (1 : ℂ)
          rw [hd2]; simp
        rw [hzero, mul_zero, zero_mul]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

lemma exists_entire_mul_sub_pow_eq (a : ℂ) (S : ℕ) {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hvan : ∀ s < S, iteratedDeriv s g a = 0) :
    ∃ q : ℂ → ℂ, Differentiable ℂ q ∧ ∀ z, g z = (z - a) ^ S * q z := by
  induction S generalizing g with
  | zero => exact ⟨g, hg, fun z => by simp⟩
  | succ S ih =>
    have hga : g a = 0 := by simpa using hvan 0 (Nat.succ_pos S)
    have hq1_diff : Differentiable ℂ (dslope g a) := by
      rw [← differentiableOn_univ]
      exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr hg.differentiableOn
    have hfac : ∀ z, g z = (z - a) * dslope g a z := by
      intro z
      have h := sub_smul_dslope g a z
      rw [smul_eq_mul, hga, sub_zero] at h
      exact h.symm
    have hvan1 : ∀ s < S, iteratedDeriv s (dslope g a) a = 0 := by
      intro s hs
      have h0 : iteratedDeriv (s + 1) g a = 0 := hvan (s + 1) (Nat.succ_lt_succ hs)
      have heq : g = fun z => (z - a) * dslope g a z := funext hfac
      rw [heq, iteratedDeriv_mul_linear a hq1_diff s] at h0
      have hne : ((s + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero s
      exact (mul_eq_zero.mp h0).resolve_left hne
    obtain ⟨q, hq_diff, hq_eq⟩ := ih hq1_diff hvan1
    refine ⟨q, hq_diff, fun z => ?_⟩
    rw [hfac z, hq_eq z, pow_succ', mul_assoc]

lemma iteratedDeriv_mul_eq_zero_of_left_ne_zero {a : ℂ} {S : ℕ} {u v : ℂ → ℂ}
    (hu : Differentiable ℂ u) (hv : Differentiable ℂ v) (hua : u a ≠ 0)
    (hvan : ∀ s < S, iteratedDeriv s (fun z => u z * v z) a = 0) :
    ∀ s < S, iteratedDeriv s v a = 0 := by
  intro s hs
  induction s using Nat.strong_induction_on with
  | h s ih =>
    have h0 : iteratedDeriv s (u * v) a = 0 := hvan s hs
    rw [iteratedDeriv_mul hu.contDiff.contDiffAt hv.contDiff.contDiffAt] at h0
    rw [Finset.sum_eq_single 0] at h0
    · simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero, Nat.sub_zero] at h0
      exact (mul_eq_zero.mp h0).resolve_left hua
    · intro i hi hne
      have hle : i ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hlt : s - i < s := by omega
      rw [ih (s - i) hlt (lt_trans hlt hs), mul_zero]
    · intro hnot; exact False.elim (hnot (Finset.mem_range.mpr (Nat.succ_pos s)))

lemma exists_entire_mul_prod_pow_eq (I : Finset ℂ) (S : ℕ) {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hvan : ∀ a ∈ I, ∀ s < S, iteratedDeriv s g a = 0) :
    ∃ q : ℂ → ℂ, Differentiable ℂ q ∧ ∀ z, g z = (∏ a ∈ I, (z - a) ^ S) * q z := by
  classical
  induction I using Finset.induction_on generalizing g with
  | empty => exact ⟨g, hg, fun z => by simp⟩
  | insert a I ha ih =>
    obtain ⟨q₁, hq₁_diff, hq₁_eq⟩ := exists_entire_mul_sub_pow_eq a S hg
      (hvan a (Finset.mem_insert_self a I))
    have hvan₁ : ∀ b ∈ I, ∀ s < S, iteratedDeriv s q₁ b = 0 := by
      intro b hb
      have hne : b - a ≠ 0 := sub_ne_zero.mpr (fun hba => ha (hba ▸ hb))
      have hpow_diff : Differentiable ℂ (fun z : ℂ => (z - a) ^ S) :=
        (differentiable_id.sub (differentiable_const a)).pow S
      have hvan_b : ∀ s < S, iteratedDeriv s (fun z => (z - a) ^ S * q₁ z) b = 0 := by
        intro s hs
        have heq : (fun z => (z - a) ^ S * q₁ z) = g := funext fun z => (hq₁_eq z).symm
        rw [heq]
        exact hvan b (Finset.mem_insert_of_mem hb) s hs
      exact iteratedDeriv_mul_eq_zero_of_left_ne_zero hpow_diff hq₁_diff (pow_ne_zero S hne) hvan_b
    obtain ⟨q, hq_diff, hq_eq⟩ := ih hq₁_diff hvan₁
    refine ⟨q, hq_diff, fun z => ?_⟩
    rw [Finset.prod_insert ha, mul_assoc, ← hq_eq z, ← hq₁_eq z]

/- Combinatorial factorial/binomial ratio bound for Hermite interpolation -/

lemma prod_Icc_sub_eq_descFactorial {h l' : ℕ} (hl' : h < l') :
    ∏ u ∈ Finset.Icc 1 h, (l' - u) = (l' - 1).descFactorial h := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hIcc : Finset.Icc 1 (h + 1) = insert (h + 1) (Finset.Icc 1 h) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.prod_insert (by simp), ih (by omega), Nat.descFactorial_succ]
    have hsub : l' - 1 - h = l' - (h + 1) := by omega
    rw [hsub]

lemma prod_Icc_erase_abs_sub_eq {h l : ℕ} (hl1 : 1 ≤ l) (hlh : l ≤ h) :
    (∏ u ∈ (Finset.Icc 1 h).erase l, |(l : ℤ) - (u : ℤ)|) =
      (((l - 1).factorial * (h - l).factorial : ℕ) : ℤ) := by
  have hpart : (Finset.Icc 1 h).erase l = Finset.Ico 1 l ∪ Finset.Ioc l h := by
    ext x; simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union,
      Finset.mem_Ico, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Ico 1 l) (Finset.Ioc l h) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [Finset.mem_Ico, Finset.mem_Ioc] at h1 h2; omega
  rw [hpart, Finset.prod_union hdisj, Nat.cast_mul]
  congr 1
  · have hleft : ∏ u ∈ Finset.Ico 1 l, |(l : ℤ) - (u : ℤ)| =
        ((∏ u ∈ Finset.Ico 1 l, (l - u) : ℕ) : ℤ) := by
      rw [Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro u hu
      have hul : u < l := (Finset.mem_Ico.mp hu).2
      rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ (l : ℤ) - (u : ℤ)), Int.ofNat_sub hul.le]
    rw [hleft]
    congr 1
    clear hpart hdisj hleft hlh
    induction l with
    | zero => omega
    | succ l' ih =>
      rcases Nat.eq_zero_or_pos l' with rfl | hl'pos
      · simp
      · have hIco : Finset.Ico 1 (l' + 1) = insert 1 (Finset.Ico 2 (l' + 1)) := by
          ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
        have hbij : ∏ u ∈ Finset.Ico 2 (l' + 1), (l' + 1 - u) =
            ∏ u ∈ Finset.Ico 1 l', (l' - u) := by
          refine Finset.prod_bij (fun u _ => u - 1) ?_ ?_ ?_ ?_
          · intro u hu; simp only [Finset.mem_Ico] at hu ⊢; omega
          · intro u₁ hu₁ u₂ hu₂ heq; simp only [Finset.mem_Ico] at hu₁ hu₂; omega
          · intro b hb; refine ⟨b + 1, ?_, by omega⟩; simp only [Finset.mem_Ico] at hb ⊢; omega
          · intro u hu; simp only [Finset.mem_Ico] at hu; omega
        rw [hIco, Finset.prod_insert (by simp), hbij, ih hl'pos]
        have hsub : l' + 1 - 1 = l' := by omega
        rw [hsub]
        cases l' with
        | zero => omega
        | succ m => rw [Nat.factorial_succ]; simp
  · have hright : ∏ u ∈ Finset.Ioc l h, |(l : ℤ) - (u : ℤ)| =
        ((∏ u ∈ Finset.Ioc l h, (u - l) : ℕ) : ℤ) := by
      rw [Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro u hu
      have hlu : l < u := (Finset.mem_Ioc.mp hu).1
      rw [abs_of_nonpos (by omega : (l : ℤ) - (u : ℤ) ≤ 0), neg_sub, Int.ofNat_sub hlu.le]
    rw [hright]
    congr 1
    have hbij : ∏ u ∈ Finset.Ioc l h, (u - l) = ∏ r ∈ Finset.Icc 1 (h - l), r := by
      refine Finset.prod_bij (fun u _ => u - l) ?_ ?_ ?_ ?_
      · intro u hu; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hu ⊢; omega
      · intro u₁ hu₁ u₂ hu₂ heq; simp only [Finset.mem_Ioc] at hu₁ hu₂; omega
      · intro b hb; refine ⟨b + l, ?_, by omega⟩; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hb ⊢; omega
      · intro u _; rfl
    rw [hbij]
    set m := h - l
    clear hpart hdisj hright hbij hl1 hlh
    induction m with
    | zero => simp
    | succ m ih =>
      have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.prod_insert (by simp), ih, Nat.factorial_succ]

lemma factorial_ratio_le {h l l' : ℕ} (hl1 : 1 ≤ l) (hlh : l ≤ h) (hl'lo : h < l')
    (hl'hi : l' ≤ 2 * h) :
    ((l' - 1).descFactorial h : ℝ) / (((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ≤
      (h : ℝ) * (2 : ℝ) ^ (3 * h) := by
  have h1 : (l' - 1).descFactorial h = h.factorial * (l' - 1).choose h := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
  have h2 : h.factorial = h * (h - 1).factorial := by
    cases h with
    | zero => omega
    | succ h' => simp [Nat.factorial_succ]
  have h3 : (h - 1).factorial = (h - 1).choose (l - 1) * ((l - 1).factorial * (h - l).factorial) := by
    have hsub : h - 1 - (l - 1) = h - l := by omega
    have hmul := Nat.choose_mul_factorial_mul_factorial (show l - 1 ≤ h - 1 by omega)
    rw [hsub] at hmul
    rw [← hmul, mul_assoc]
  have hden_pos : (0 : ℝ) < (((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) := by positivity
  have hnum_eq : ((l' - 1).descFactorial h : ℝ) =
      ((h * (h - 1).choose (l - 1) * (l' - 1).choose h : ℕ) : ℝ) *
      (((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) := by
    have hnat : (l' - 1).descFactorial h =
        h * (h - 1).choose (l - 1) * (l' - 1).choose h * ((l - 1).factorial * (h - l).factorial) := by
      rw [h1, h2, h3]; ring
    rw [← Nat.cast_mul, hnat]
  rw [hnum_eq, mul_div_cancel_right₀ _ hden_pos.ne']
  have hc1 : (h - 1).choose (l - 1) ≤ 2 ^ h :=
    le_trans (Nat.choose_le_two_pow _ _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hc2 : (l' - 1).choose h ≤ 2 ^ (2 * h) :=
    le_trans (Nat.choose_le_two_pow _ _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hprod : h * (h - 1).choose (l - 1) * (l' - 1).choose h ≤ h * 2 ^ (3 * h) := by
    calc h * (h - 1).choose (l - 1) * (l' - 1).choose h
        ≤ h * 2 ^ h * 2 ^ (2 * h) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left h hc1) hc2
      _ = h * 2 ^ (3 * h) := by rw [mul_assoc, ← pow_add]; congr 2; omega
  exact_mod_cast hprod

/- Main Hermite–Schwarz Extrapolation Theorem (ZERO contour integrals) -/

theorem hermite_schwarz_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {h S l' : ℕ} (hh : 1 ≤ h) (hS : 1 ≤ S) (hl'lo : h < l') (hl'hi : l' ≤ 2 * h)
    {Mf eps : ℝ} (_hMf : 0 ≤ Mf) (heps : 0 ≤ eps)
    (hcircle : ∀ w : ℂ, ‖w‖ = 32 * (h : ℝ) → ‖f w‖ ≤ Mf)
    (hderiv : ∀ l ∈ Finset.Icc 1 h, ∀ s < S,
      ‖iteratedDeriv s f (l : ℂ) / (s.factorial : ℂ)‖ ≤ eps) :
    ‖f (l' : ℂ)‖ ≤
      ((2 / 31 : ℝ) ^ (h * S)) * Mf +
      4 * (h : ℝ) * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
  classical
  set R : ℝ := 32 * (h : ℝ)
  have hRpos : 0 < R := by positivity
  -- Define nodal polynomials E and E_l in ℂ[X]
  let E : Polynomial ℂ := ∏ u ∈ Finset.Icc 1 h, (X - C (u : ℂ)) ^ S
  let El : ℕ → Polynomial ℂ := fun l => ∏ u ∈ (Finset.Icc 1 h).erase l, (X - C (u : ℂ)) ^ S
  have hE_split : ∀ l ∈ Finset.Icc 1 h, E = (X - C (l : ℂ)) ^ S * El l := by
    intro l hl
    dsimp only [E, El]
    exact (Finset.mul_prod_erase (Finset.Icc 1 h) (fun u => (X - C (u : ℂ)) ^ S) hl).symm
  -- Truncated inverse H_l(Y) of E_l(l + Y) mod Y^S
  let Hl : ℕ → Polynomial ℂ := fun l =>
    truncPoly S (∏ u ∈ (Finset.Icc 1 h).erase l, invTrunc S ((l : ℂ) - (u : ℂ)) ^ S)
  -- Taylor polynomial T_l(Y) of f at l
  let Tl : ℕ → Polynomial ℂ := fun l =>
    ∑ s ∈ Finset.range S, C (iteratedDeriv s f (l : ℂ) / (s.factorial : ℂ)) * X ^ s
  -- Gl(Y) = truncPoly S (Tl l * Hl l)
  let Gl : ℕ → Polynomial ℂ := fun l => truncPoly S (Tl l * Hl l)
  -- Hermite interpolating polynomial Q(X) = ∑_{l=1}^h E_l(X) * G_l(X - l)
  let Q : Polynomial ℂ := ∑ l ∈ Finset.Icc 1 h, El l * (Gl l).comp (X - C (l : ℂ))
  -- Step 1: Coefficient bounds on Hl, Tl, Gl
  have hHl_bound : ∀ l ∈ Finset.Icc 1 h,
      normSumHalf (Hl l) ≤
        ((2 : ℝ) ^ ((h - 1) * S)) / ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S) := by
    intro l hl
    have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
    have hlh : l ≤ h := (Finset.mem_Icc.mp hl).2
    refine le_trans (normSumHalf_truncPoly_le S _) ?_
    refine le_trans (normSumHalf_prod_le _ _) ?_
    calc ∏ u ∈ (Finset.Icc 1 h).erase l, normSumHalf (invTrunc S ((l : ℂ) - (u : ℂ)) ^ S)
        ≤ ∏ u ∈ (Finset.Icc 1 h).erase l, (2 / ‖(l : ℂ) - (u : ℂ)‖) ^ S := by
          apply Finset.prod_le_prod (fun _ _ => normSumHalf_nonneg _)
          intro u hu
          have hne : u ≠ l := Finset.ne_of_mem_erase hu
          have hge1 : (1 : ℝ) ≤ ‖(l : ℂ) - (u : ℂ)‖ := by
            have hcast : ((l : ℂ) - (u : ℂ)) = (((l : ℤ) - (u : ℤ) : ℤ) : ℂ) := by push_cast; ring
            rw [hcast, Complex.norm_intCast]
            have h1 : (1 : ℤ) ≤ |(l : ℤ) - (u : ℤ)| := by
              rcases lt_or_gt_of_ne hne with hlt | hgt
              · rw [abs_of_pos (by omega : (0 : ℤ) < (l : ℤ) - (u : ℤ))]; omega
              · rw [abs_of_neg (by omega : (l : ℤ) - (u : ℤ) < 0)]; omega
            exact_mod_cast h1
          exact le_trans (normSumHalf_pow_le _ S)
            (pow_le_pow_left₀ (normSumHalf_nonneg _) (normSumHalf_invTrunc_le hge1) S)
      _ = ((2 : ℝ) ^ ((h - 1) * S)) / ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S) := by
          simp only [div_pow, Finset.prod_div_distrib]
          rw [Finset.prod_const, Finset.card_erase_of_mem hl, Nat.card_Icc,
            show h + 1 - 1 = h by omega, ← pow_mul, mul_comm S (h - 1)]
          congr 1
          rw [Finset.prod_pow]
          congr 1
          have hprod := prod_Icc_erase_abs_sub_eq hl1 hlh
          have hcast : ∏ u ∈ (Finset.Icc 1 h).erase l, ‖(l : ℂ) - (u : ℂ)‖ =
              ((∏ u ∈ (Finset.Icc 1 h).erase l, |(l : ℤ) - (u : ℤ)| : ℤ) : ℝ) := by
            rw [Int.cast_prod]
            apply Finset.prod_congr rfl
            intro u _
            have hc : ((l : ℂ) - (u : ℂ)) = (((l : ℤ) - (u : ℤ) : ℤ) : ℂ) := by push_cast; ring
            rw [hc, Complex.norm_intCast, Int.cast_abs]
          rw [hcast, hprod, Int.cast_natCast]
  have hTl_bound : ∀ l ∈ Finset.Icc 1 h, normSumHalf (Tl l) ≤ 2 * eps := by
    intro l hl
    have hcoeff : ∀ m, (Tl l).coeff m =
        if m < S then iteratedDeriv m f (l : ℂ) / (m.factorial : ℂ) else 0 := by
      intro m
      dsimp only [Tl]
      rw [Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul_X_pow]
      by_cases hm : m < S
      · rw [if_pos hm, Finset.sum_eq_single m]
        · simp
        · intro b _ hne; exact if_neg (Ne.symm hne)
        · intro hnot; exact False.elim (hnot (Finset.mem_range.mpr hm))
      · rw [if_neg hm]
        apply Finset.sum_eq_zero
        intro b hb
        have hlt : b < S := Finset.mem_range.mp hb
        exact if_neg (by omega)
    have hdeg : (Tl l).natDegree ≤ S := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm; rw [hcoeff m, if_neg (by omega)]
    rw [normSumHalf_eq_sum_of_natDegree_le hdeg]
    calc ∑ m ∈ Finset.range (S + 1), ‖(Tl l).coeff m‖ * (1 / 2 : ℝ) ^ m
        ≤ ∑ m ∈ Finset.range (S + 1), eps * (1 / 2 : ℝ) ^ m := by
          apply Finset.sum_le_sum
          intro m _
          rw [hcoeff m]
          split_ifs with hm
          · exact mul_le_mul_of_nonneg_right (hderiv l hl m hm) (by positivity)
          · rw [norm_zero, zero_mul]; positivity
      _ = eps * ∑ m ∈ Finset.range (S + 1), (1 / 2 : ℝ) ^ m := by rw [← Finset.mul_sum]
      _ ≤ eps * 2 := by
          apply mul_le_mul_of_nonneg_left _ heps
          rw [geom_sum_eq (by norm_num)]
          have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (S + 1) := by positivity
          have hrew : ((1 / 2 : ℝ) ^ (S + 1) - 1) / ((1 / 2 : ℝ) - 1) =
              2 * (1 - (1 / 2 : ℝ) ^ (S + 1)) := by ring
          rw [hrew]; linarith
      _ = 2 * eps := by ring
  have hGl_coeff : ∀ l ∈ Finset.Icc 1 h, ∀ k < S,
      ‖(Gl l).coeff k‖ ≤
        ((2 : ℝ) ^ (h * S + 1)) * eps / ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S) := by
    intro l hl k hk
    have hnh : normSumHalf (Gl l) ≤
        2 * eps * (((2 : ℝ) ^ ((h - 1) * S)) /
          ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S)) := by
      refine le_trans (normSumHalf_truncPoly_le S _) ?_
      refine le_trans (normSumHalf_mul_le _ _) ?_
      exact mul_le_mul (hTl_bound l hl) (hHl_bound l hl) (normSumHalf_nonneg _) (by positivity)
    refine le_trans (norm_coeff_le_two_pow_mul_normSumHalf (Gl l) k) ?_
    have h2k : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ S :=
      pow_le_pow_right₀ (by norm_num) (le_of_lt hk)
    calc (2 : ℝ) ^ k * normSumHalf (Gl l)
        ≤ (2 : ℝ) ^ S * (2 * eps * (((2 : ℝ) ^ ((h - 1) * S)) /
            ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S))) :=
          mul_le_mul h2k hnh (normSumHalf_nonneg _) (by positivity)
      _ = ((2 : ℝ) ^ (h * S + 1)) * eps / ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S) := by
          have hexp : S + 1 + (h - 1) * S = h * S + 1 := by
            have : (h - 1) * S + S = h * S := by
              cases h with
              | zero => omega
              | succ h' => simp [Nat.add_mul]
            omega
          have hpow : (2 : ℝ) ^ S * 2 * (2 : ℝ) ^ ((h - 1) * S) = (2 : ℝ) ^ (h * S + 1) := by
            rw [← hexp, pow_add, pow_add, pow_one]
          calc (2 : ℝ) ^ S * (2 * eps * ((2 : ℝ) ^ ((h - 1) * S) /
                ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S)))
              = ((2 : ℝ) ^ S * 2 * (2 : ℝ) ^ ((h - 1) * S)) * eps /
                  ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S) := by ring
            _ = (2 : ℝ) ^ (h * S + 1) * eps /
                  ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S) := by rw [hpow]
  -- Step 2: Exact vanishing of f - Q to order S at every l ∈ Icc 1 h
  have hQ_van : ∀ l ∈ Finset.Icc 1 h, ∀ s < S,
      iteratedDeriv s (fun z => f z - Q.eval z) (l : ℂ) = 0 := by
    intro l hl s hs
    have hQdiff : Differentiable ℂ (fun z : ℂ => Q.eval z) :=
      fun z => (hasDerivAt_eval_poly Q z).differentiableAt
    have hsub_deriv : iteratedDeriv s (fun z => f z - Q.eval z) (l : ℂ) =
        iteratedDeriv s f (l : ℂ) - iteratedDeriv s (fun z => Q.eval z) (l : ℂ) := by
      have h1 : ContDiffAt ℂ (s : ℕ) f (l : ℂ) := hf.contDiff.contDiffAt
      have h2 : ContDiffAt ℂ (s : ℕ) (fun z : ℂ => Q.eval z) (l : ℂ) := hQdiff.contDiff.contDiffAt
      exact iteratedDeriv_fun_sub h1 h2
    rw [hsub_deriv, sub_eq_zero, iteratedDeriv_eval_poly_eq_factorial_mul_taylor_coeff]
    -- Compute (taylor (l : ℂ) Q).coeff s
    have htaylor_Q : (Polynomial.taylor (l : ℂ) Q).coeff s =
        iteratedDeriv s f (l : ℂ) / (s.factorial : ℂ) := by
      rw [Polynomial.taylor_apply]
      dsimp only [Q]
      rw [Polynomial.sum_comp, Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single l]
      · rw [Polynomial.mul_comp, Polynomial.comp_assoc]
        have hcompX : (X - C (l : ℂ)).comp (X + C (l : ℂ)) = X := by
          simp [Polynomial.sub_comp, Polynomial.X_comp]
        rw [hcompX, Polynomial.comp_X]
        -- (El l).comp (X + C l) * Gl l has same s-th coeff as Tl l!
        have hEl_Hl : ∀ m < S,
            (((El l).comp (X + C (l : ℂ))) * Hl l).coeff m = (1 : Polynomial ℂ).coeff m := by
          intro m hm
          have h1 : (((El l).comp (X + C (l : ℂ))) * Hl l).coeff m =
              (((El l).comp (X + C (l : ℂ))) *
                (∏ u ∈ (Finset.Icc 1 h).erase l, invTrunc S ((l : ℂ) - (u : ℂ)) ^ S)).coeff m := by
            apply coeff_mul_eq_of_coeff_eq_lt _ hm
            intro k hk; exact (coeff_truncPoly S _ k).trans (if_pos hk)
          rw [h1]
          dsimp only [El]
          rw [Polynomial.prod_comp, ← Finset.prod_mul_distrib]
          apply coeff_prod_eq_one_of_coeff_eq_one _ S _ _ m hm
          intro u hu k hk
          rw [Polynomial.pow_comp, ← mul_pow]
          apply coeff_pow_eq_one_of_coeff_eq_one _ S k hk
          intro j hj
          have hlin : (X - C (u : ℂ)).comp (X + C (l : ℂ)) = C ((l : ℂ) - (u : ℂ)) + X := by
            simp [Polynomial.sub_comp, Polynomial.X_comp]; ring
          rw [hlin]
          have hne : (l : ℂ) - (u : ℂ) ≠ 0 := by
            have hu_ne : u ≠ l := Finset.ne_of_mem_erase hu
            exact sub_ne_zero.mpr (by exact_mod_cast hu_ne.symm)
          exact mul_invTrunc_coeff hne hj
        have hstep1 : (((El l).comp (X + C (l : ℂ))) * Gl l).coeff s =
            (((El l).comp (X + C (l : ℂ))) * (Tl l * Hl l)).coeff s := by
          apply coeff_mul_eq_of_coeff_eq_lt _ hs
          intro k hk; exact (coeff_truncPoly S _ k).trans (if_pos hk)
        rw [hstep1]
        have hrearr : ((El l).comp (X + C (l : ℂ))) * (Tl l * Hl l) =
            Tl l * (((El l).comp (X + C (l : ℂ))) * Hl l) := by ring
        rw [hrearr]
        calc (Tl l * (((El l).comp (X + C (l : ℂ))) * Hl l)).coeff s
            = (Tl l * 1).coeff s := coeff_mul_eq_of_coeff_eq_lt hEl_Hl hs
          _ = (Tl l).coeff s := by rw [mul_one]
          _ = iteratedDeriv s f (l : ℂ) / (s.factorial : ℂ) := by
              dsimp only [Tl]
              rw [Polynomial.finsetSum_coeff]
              simp only [Polynomial.coeff_C_mul_X_pow]
              rw [Finset.sum_eq_single s]
              · simp
              · intro b _ hne; exact if_neg (Ne.symm hne)
              · intro hnot; exact False.elim (hnot (Finset.mem_range.mpr hs))
      · intro u hu hul
        -- El u contains factor (X - C l)^S, so (El u).comp (X + C l) is divisible by X^S
        have hl_mem : l ∈ (Finset.Icc 1 h).erase u := Finset.mem_erase.mpr ⟨hul.symm, hl⟩
        have hEl_u : El u = (X - C (l : ℂ)) ^ S *
            ∏ v ∈ ((Finset.Icc 1 h).erase u).erase l, (X - C (v : ℂ)) ^ S :=
          (Finset.mul_prod_erase ((Finset.Icc 1 h).erase u)
            (fun v : ℕ => (X - C (v : ℂ)) ^ S) hl_mem).symm
        rw [hEl_u, Polynomial.mul_comp, Polynomial.mul_comp, Polynomial.pow_comp]
        have hsub : (X - C (l : ℂ)).comp (X + C (l : ℂ)) = X := by
          simp [Polynomial.sub_comp, Polynomial.X_comp]
        rw [hsub, mul_assoc, Polynomial.coeff_X_pow_mul']
        exact if_neg (by omega)
      · intro hnot; exact False.elim (hnot hl)
    rw [htaylor_Q]
    have hfac_ne : (s.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero s
    field_simp [hfac_ne]
  -- Step 3: Entire factorization (f - Q) = E * q
  have hdiff_sub : Differentiable ℂ (fun z => f z - Q.eval z) :=
    hf.sub (fun z => (hasDerivAt_eval_poly Q z).differentiableAt)
  let I : Finset ℂ := (Finset.Icc 1 h).image (fun u : ℕ => (u : ℂ))
  have hE_eq_prod : ∀ z : ℂ, E.eval z = ∏ a ∈ I, (z - a) ^ S := by
    intro z
    dsimp only [E, I]
    rw [Polynomial.eval_prod, Finset.prod_image (fun x _ y _ hxy => Nat.cast_injective hxy)]
    simp [Polynomial.eval_pow, Polynomial.eval_sub]
  have hvan_I : ∀ a ∈ I, ∀ s < S, iteratedDeriv s (fun z => f z - Q.eval z) a = 0 := by
    intro a ha s hs
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ha
    exact hQ_van l hl s hs
  obtain ⟨q, hq_diff, hq_eq⟩ := exists_entire_mul_prod_pow_eq I S hdiff_sub hvan_I
  have hq_E : ∀ z, f z - Q.eval z = E.eval z * q z := fun z => by
    rw [hE_eq_prod z]; exact hq_eq z
  -- Step 4: Bounds on E(l'), E(w), Q(l'), Q(w)/E(w)
  have hEl'_norm : ‖E.eval (l' : ℂ)‖ = (((l' - 1).descFactorial h : ℕ) : ℝ) ^ S := by
    dsimp only [E]
    rw [Polynomial.eval_prod, norm_prod]
    have h1 : ∏ u ∈ Finset.Icc 1 h, ‖((X - C (u : ℂ)) ^ S).eval (l' : ℂ)‖ =
        (∏ u ∈ Finset.Icc 1 h, ((l' - u : ℕ) : ℝ)) ^ S := by
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro u hu
      have hul' : u ≤ l' := le_trans (Finset.mem_Icc.mp hu).2 (le_of_lt hl'lo)
      simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        norm_pow]
      congr 1
      rw [← Nat.cast_sub hul', Complex.norm_natCast]
    rw [h1, ← Nat.cast_prod, prod_Icc_sub_eq_descFactorial hl'lo]
  have hEl'_upper : ‖E.eval (l' : ℂ)‖ ≤ (2 * (h : ℝ)) ^ (h * S) := by
    dsimp only [E]
    rw [Polynomial.eval_prod, norm_prod]
    calc ∏ u ∈ Finset.Icc 1 h, ‖((X - C (u : ℂ)) ^ S).eval (l' : ℂ)‖
        ≤ ∏ _u ∈ Finset.Icc 1 h, (2 * (h : ℝ)) ^ S := by
          apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          intro u hu
          have hu1 : 1 ≤ u := (Finset.mem_Icc.mp hu).1
          have hul' : u ≤ l' := le_trans (Finset.mem_Icc.mp hu).2 (le_of_lt hl'lo)
          simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
            norm_pow]
          apply pow_le_pow_left₀ (norm_nonneg _)
          rw [← Nat.cast_sub hul', Complex.norm_natCast]
          have hle : l' - u ≤ 2 * h := by omega
          exact_mod_cast hle
      _ = (2 * (h : ℝ)) ^ (h * S) := by
          rw [Finset.prod_const, Nat.card_Icc, show h + 1 - 1 = h by omega, ← pow_mul, mul_comm S h]
  have hEw_lower : ∀ w : ℂ, ‖w‖ = R → (31 * (h : ℝ)) ^ (h * S) ≤ ‖E.eval w‖ := by
    intro w hw
    dsimp only [E]
    rw [Polynomial.eval_prod, norm_prod]
    have hconst : (31 * (h : ℝ)) ^ (h * S) = ∏ _u ∈ Finset.Icc 1 h, (31 * (h : ℝ)) ^ S := by
      rw [Finset.prod_const, Nat.card_Icc, show h + 1 - 1 = h by omega, ← pow_mul, mul_comm h S]
    rw [hconst]
    apply Finset.prod_le_prod (fun _ _ => by positivity)
    intro u hu
    have huh : u ≤ h := (Finset.mem_Icc.mp hu).2
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      norm_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hrev := norm_sub_norm_le w (u : ℂ)
    rw [hw, Complex.norm_natCast] at hrev
    have huR : (u : ℝ) ≤ (h : ℝ) := by exact_mod_cast huh
    dsimp only [R] at hrev
    linarith
  have hQ_eval_l' : ‖Q.eval (l' : ℂ)‖ ≤
      2 * (h : ℝ) * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
    dsimp only [Q]
    rw [Polynomial.eval_finsetSum]
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ l ∈ Finset.Icc 1 h, ‖(El l * (Gl l).comp (X - C (l : ℂ))).eval (l' : ℂ)‖
        ≤ ∑ _l ∈ Finset.Icc 1 h,
            2 * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
          apply Finset.sum_le_sum
          intro l hl
          have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
          have hlh : l ≤ h := (Finset.mem_Icc.mp hl).2
          rw [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_sub,
            Polynomial.eval_X, Polynomial.eval_C, norm_mul]
          -- ‖(El l).eval l'‖ ≤ ‖E.eval l'‖ because |l' - l| ≥ 1
          have hEl_le : ‖(El l).eval (l' : ℂ)‖ ≤ ‖E.eval (l' : ℂ)‖ := by
            rw [hE_split l hl, Polynomial.eval_mul, norm_mul]
            have hge1 : (1 : ℝ) ≤ ‖((X - C (l : ℂ)) ^ S).eval (l' : ℂ)‖ := by
              simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
                Polynomial.eval_C, norm_pow]
              apply one_le_pow₀
              rw [← Nat.cast_sub (le_of_lt (lt_of_le_of_lt hlh hl'lo)), Complex.norm_natCast]
              have : 1 ≤ l' - l := by omega
              exact_mod_cast this
            have h1mul := mul_le_mul_of_nonneg_right hge1 (norm_nonneg ((El l).eval (l' : ℂ)))
            rwa [one_mul] at h1mul
          -- Bound ‖(Gl l).eval (l' - l)‖
          have hGl_val : ‖(Gl l).eval ((l' : ℂ) - (l : ℂ))‖ ≤
              (S : ℝ) * ((2 * (h : ℝ)) ^ S) *
              (((2 : ℝ) ^ (h * S + 1)) * eps /
                ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S)) := by
            dsimp only [Gl, truncPoly]
            rw [Polynomial.eval_finsetSum]
            refine le_trans (norm_sum_le _ _) ?_
            calc ∑ k ∈ Finset.range S, ‖(C ((Tl l * Hl l).coeff k) * X ^ k).eval ((l' : ℂ) - (l : ℂ))‖
                ≤ ∑ _k ∈ Finset.range S, ((2 * (h : ℝ)) ^ S) *
                    (((2 : ℝ) ^ (h * S + 1)) * eps /
                      ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S)) := by
                  apply Finset.sum_le_sum
                  intro k hk
                  have hkS : k < S := Finset.mem_range.mp hk
                  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
                    Polynomial.eval_X, norm_mul, norm_pow]
                  have hc : ‖(Tl l * Hl l).coeff k‖ ≤
                      ((2 : ℝ) ^ (h * S + 1)) * eps /
                        ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S) := by
                    have heq : (Tl l * Hl l).coeff k = (Gl l).coeff k := by
                      rw [coeff_truncPoly, if_pos hkS]
                    rw [heq]; exact hGl_coeff l hl k hkS
                  have hpow : ‖(l' : ℂ) - (l : ℂ)‖ ^ k ≤ (2 * (h : ℝ)) ^ S := by
                    have hnorm : ‖(l' : ℂ) - (l : ℂ)‖ ≤ 2 * (h : ℝ) := by
                      rw [← Nat.cast_sub (le_of_lt (lt_of_le_of_lt hlh hl'lo)), Complex.norm_natCast]
                      have : l' - l ≤ 2 * h := by omega
                      exact_mod_cast this
                    have h2h1 : (1 : ℝ) ≤ 2 * (h : ℝ) := by
                      have : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
                      linarith
                    exact le_trans (pow_le_pow_left₀ (norm_nonneg _) hnorm k)
                      (pow_le_pow_right₀ h2h1 (le_of_lt hkS))
                  rw [mul_comm]
                  exact mul_le_mul hpow hc (norm_nonneg _) (by positivity)
              _ = (S : ℝ) * ((2 * (h : ℝ)) ^ S) *
                    (((2 : ℝ) ^ (h * S + 1)) * eps /
                      ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S)) := by
                  simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
          calc ‖(El l).eval (l' : ℂ)‖ * ‖(Gl l).eval ((l' : ℂ) - (l : ℂ))‖
              ≤ ‖E.eval (l' : ℂ)‖ * ((S : ℝ) * ((2 * (h : ℝ)) ^ S) *
                  (((2 : ℝ) ^ (h * S + 1)) * eps /
                    ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S))) :=
                mul_le_mul hEl_le hGl_val (norm_nonneg _) (norm_nonneg _)
            _ = (S : ℝ) * ((2 * (h : ℝ)) ^ S) * ((2 : ℝ) ^ (h * S + 1)) *
                  (((l' - 1).descFactorial h : ℝ) /
                    (((l - 1).factorial * (h - l).factorial : ℕ) : ℝ)) ^ S * eps := by
                rw [hEl'_norm, div_pow]; ring
            _ ≤ (S : ℝ) * ((2 * (h : ℝ)) ^ S) * ((2 : ℝ) ^ (h * S + 1)) *
                  ((h : ℝ) * (2 : ℝ) ^ (3 * h)) ^ S * eps := by
                have hrat := factorial_ratio_le hl1 hlh hl'lo hl'hi
                have hpow := pow_le_pow_left₀ (by positivity) hrat S
                gcongr
            _ = 2 * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
                have hsplit : ((h : ℝ) * (2 : ℝ) ^ (3 * h)) ^ S =
                    (h : ℝ) ^ S * (2 : ℝ) ^ (3 * h * S) := by rw [mul_pow, ← pow_mul]
                have h16 : (2 : ℝ) ^ (h * S) * (2 : ℝ) ^ (3 * h * S) = (16 : ℝ) ^ (h * S) := by
                  rw [← pow_add, show h * S + 3 * h * S = 4 * (h * S) by ring, pow_mul]
                  norm_num
                have h2h : (2 * (h : ℝ)) ^ S * (h : ℝ) ^ S = (2 * (h : ℝ) ^ 2) ^ S := by
                  rw [← mul_pow]; congr 1; ring
                rw [hsplit, pow_succ]
                calc (S : ℝ) * (2 * (h : ℝ)) ^ S * ((2 : ℝ) ^ (h * S) * 2) *
                      ((h : ℝ) ^ S * (2 : ℝ) ^ (3 * h * S)) * eps
                    = 2 * (S : ℝ) * ((2 * (h : ℝ)) ^ S * (h : ℝ) ^ S) *
                        ((2 : ℝ) ^ (h * S) * (2 : ℝ) ^ (3 * h * S)) * eps := by ring
                  _ = 2 * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
                        rw [h2h, h16]
      _ = 2 * (h : ℝ) * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
          rw [Finset.sum_const, Nat.card_Icc, show h + 1 - 1 = h by omega, nsmul_eq_mul]; ring
  -- Step 5: Bound ‖E(l')‖ * ‖q(w)‖ on the circle ‖w‖ = R
  have hq_circle : ∀ w : ℂ, ‖w‖ = R →
      ‖E.eval (l' : ℂ)‖ * ‖q w‖ ≤
        ((2 / 31 : ℝ) ^ (h * S)) * Mf +
        2 * (h : ℝ) * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
    intro w hw
    have hEw_pos : 0 < ‖E.eval w‖ := lt_of_lt_of_le (by positivity) (hEw_lower w hw)
    have hEw_ne : E.eval w ≠ 0 := norm_pos_iff.mp hEw_pos
    have hqw : q w = f w / E.eval w - Q.eval w / E.eval w := by
      have h := hq_E w
      rw [← sub_div]
      exact eq_div_of_mul_eq hEw_ne (by rw [mul_comm]; exact h.symm)
    rw [hqw]
    have htri : ‖f w / E.eval w - Q.eval w / E.eval w‖ ≤
        ‖f w‖ / ‖E.eval w‖ + ‖Q.eval w / E.eval w‖ := by
      calc ‖f w / E.eval w - Q.eval w / E.eval w‖
          ≤ ‖f w / E.eval w‖ + ‖Q.eval w / E.eval w‖ := norm_sub_le _ _
        _ = ‖f w‖ / ‖E.eval w‖ + ‖Q.eval w / E.eval w‖ := by rw [norm_div]
    have hterm1 : ‖E.eval (l' : ℂ)‖ * (‖f w‖ / ‖E.eval w‖) ≤ ((2 / 31 : ℝ) ^ (h * S)) * Mf := by
      have hrat : ‖E.eval (l' : ℂ)‖ / ‖E.eval w‖ ≤ (2 / 31 : ℝ) ^ (h * S) := by
        rw [div_le_iff₀ hEw_pos]
        calc ‖E.eval (l' : ℂ)‖
            ≤ (2 * (h : ℝ)) ^ (h * S) := hEl'_upper
          _ = (2 / 31 : ℝ) ^ (h * S) * (31 * (h : ℝ)) ^ (h * S) := by
              rw [← mul_pow]; congr 1; ring
          _ ≤ (2 / 31 : ℝ) ^ (h * S) * ‖E.eval w‖ :=
              mul_le_mul_of_nonneg_left (hEw_lower w hw) (by positivity)
      calc ‖E.eval (l' : ℂ)‖ * (‖f w‖ / ‖E.eval w‖)
          = (‖E.eval (l' : ℂ)‖ / ‖E.eval w‖) * ‖f w‖ := by ring
        _ ≤ ((2 / 31 : ℝ) ^ (h * S)) * Mf :=
            mul_le_mul hrat (hcircle w hw) (norm_nonneg _) (by positivity)
    have hterm2 : ‖E.eval (l' : ℂ)‖ * ‖Q.eval w / E.eval w‖ ≤
        2 * (h : ℝ) * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
      have hQdiv : Q.eval w / E.eval w =
          ∑ l ∈ Finset.Icc 1 h, (Gl l).eval (w - (l : ℂ)) / (w - (l : ℂ)) ^ S := by
        dsimp only [Q]
        rw [Polynomial.eval_finsetSum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro l hl
        rw [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C, hE_split l hl, Polynomial.eval_mul]
        have hEl_ne : (El l).eval w ≠ 0 := by
          intro h0; rw [hE_split l hl, Polynomial.eval_mul, h0, mul_zero] at hEw_ne; exact hEw_ne rfl
        simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        rw [mul_comm ((El l).eval w), mul_div_mul_right _ _ hEl_ne]
      rw [hQdiv]
      refine le_trans (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)) ?_
      rw [Finset.mul_sum]
      calc ∑ l ∈ Finset.Icc 1 h, ‖E.eval (l' : ℂ)‖ * ‖(Gl l).eval (w - (l : ℂ)) / (w - (l : ℂ)) ^ S‖
          ≤ ∑ _l ∈ Finset.Icc 1 h,
              2 * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
            apply Finset.sum_le_sum
            intro l hl
            have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
            have hlh : l ≤ h := (Finset.mem_Icc.mp hl).2
            have hwl : (1 : ℝ) ≤ ‖w - (l : ℂ)‖ := by
              have hrev := norm_sub_norm_le w (l : ℂ)
              rw [hw, Complex.norm_natCast] at hrev
              have hlR : (l : ℝ) ≤ (h : ℝ) := by exact_mod_cast hlh
              have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
              dsimp only [R] at hrev; linarith
            have hGl_div : ‖(Gl l).eval (w - (l : ℂ)) / (w - (l : ℂ)) ^ S‖ ≤
                (S : ℝ) * (((2 : ℝ) ^ (h * S + 1)) * eps /
                  ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S)) := by
              rw [norm_div, norm_pow, div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one hwl) S)]
              dsimp only [Gl, truncPoly]
              rw [Polynomial.eval_finsetSum]
              refine le_trans (norm_sum_le _ _) ?_
              calc ∑ k ∈ Finset.range S, ‖(C ((Tl l * Hl l).coeff k) * X ^ k).eval (w - (l : ℂ))‖
                  ≤ ∑ _k ∈ Finset.range S,
                      (((2 : ℝ) ^ (h * S + 1)) * eps /
                        ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S)) *
                      ‖w - (l : ℂ)‖ ^ S := by
                    apply Finset.sum_le_sum
                    intro k hk
                    have hkS : k < S := Finset.mem_range.mp hk
                    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
                      Polynomial.eval_X, norm_mul, norm_pow]
                    have hc : ‖(Tl l * Hl l).coeff k‖ ≤
                        ((2 : ℝ) ^ (h * S + 1)) * eps /
                          ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S) := by
                      have heq : (Tl l * Hl l).coeff k = (Gl l).coeff k := by
                        rw [coeff_truncPoly, if_pos hkS]
                      rw [heq]; exact hGl_coeff l hl k hkS
                    exact mul_le_mul hc (pow_le_pow_right₀ hwl (le_of_lt hkS))
                      (pow_nonneg (norm_nonneg _) k) (by positivity)
                _ = (S : ℝ) * (((2 : ℝ) ^ (h * S + 1)) * eps /
                      ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S)) *
                    ‖w - (l : ℂ)‖ ^ S := by
                    simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
            have h2hS : (1 : ℝ) ≤ (2 * (h : ℝ)) ^ S := by
              apply one_le_pow₀
              have : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
              linarith
            calc ‖E.eval (l' : ℂ)‖ * ‖(Gl l).eval (w - (l : ℂ)) / (w - (l : ℂ)) ^ S‖
                ≤ ‖E.eval (l' : ℂ)‖ * ((S : ℝ) * (((2 : ℝ) ^ (h * S + 1)) * eps /
                    ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S))) :=
                  mul_le_mul_of_nonneg_left hGl_div (norm_nonneg _)
              _ = (S : ℝ) * ((2 : ℝ) ^ (h * S + 1)) *
                    (((l' - 1).descFactorial h : ℝ) /
                      (((l - 1).factorial * (h - l).factorial : ℕ) : ℝ)) ^ S * eps := by
                  rw [hEl'_norm, div_pow]; ring
              _ ≤ (S : ℝ) * ((2 : ℝ) ^ (h * S + 1)) *
                    ((h : ℝ) * (2 : ℝ) ^ (3 * h)) ^ S * eps := by
                  have hrat := factorial_ratio_le hl1 hlh hl'lo hl'hi
                  have hpow := pow_le_pow_left₀ (by positivity) hrat S
                  gcongr
              _ ≤ (S : ℝ) * ((2 * (h : ℝ)) ^ S) * ((2 : ℝ) ^ (h * S + 1)) *
                    ((h : ℝ) * (2 : ℝ) ^ (3 * h)) ^ S * eps := by
                  have hnn : 0 ≤ (S : ℝ) * ((2 : ℝ) ^ (h * S + 1)) *
                      ((h : ℝ) * (2 : ℝ) ^ (3 * h)) ^ S * eps := by positivity
                  calc (S : ℝ) * ((2 : ℝ) ^ (h * S + 1)) * ((h : ℝ) * (2 : ℝ) ^ (3 * h)) ^ S * eps
                      = 1 * ((S : ℝ) * ((2 : ℝ) ^ (h * S + 1)) *
                          ((h : ℝ) * (2 : ℝ) ^ (3 * h)) ^ S * eps) := (one_mul _).symm
                    _ ≤ (2 * (h : ℝ)) ^ S * ((S : ℝ) * ((2 : ℝ) ^ (h * S + 1)) *
                          ((h : ℝ) * (2 : ℝ) ^ (3 * h)) ^ S * eps) :=
                        mul_le_mul_of_nonneg_right h2hS hnn
                    _ = _ := by ring
              _ = 2 * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
                  have hsplit : ((h : ℝ) * (2 : ℝ) ^ (3 * h)) ^ S =
                      (h : ℝ) ^ S * (2 : ℝ) ^ (3 * h * S) := by rw [mul_pow, ← pow_mul]
                  have h16 : (2 : ℝ) ^ (h * S) * (2 : ℝ) ^ (3 * h * S) = (16 : ℝ) ^ (h * S) := by
                    rw [← pow_add, show h * S + 3 * h * S = 4 * (h * S) by ring, pow_mul]
                    norm_num
                  have h2h : (2 * (h : ℝ)) ^ S * (h : ℝ) ^ S = (2 * (h : ℝ) ^ 2) ^ S := by
                    rw [← mul_pow]; congr 1; ring
                  rw [hsplit, pow_succ]
                  calc (S : ℝ) * (2 * (h : ℝ)) ^ S * ((2 : ℝ) ^ (h * S) * 2) *
                        ((h : ℝ) ^ S * (2 : ℝ) ^ (3 * h * S)) * eps
                      = 2 * (S : ℝ) * ((2 * (h : ℝ)) ^ S * (h : ℝ) ^ S) *
                          ((2 : ℝ) ^ (h * S) * (2 : ℝ) ^ (3 * h * S)) * eps := by ring
                    _ = 2 * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
                          rw [h2h, h16]
        _ = 2 * (h : ℝ) * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
            rw [Finset.sum_const, Nat.card_Icc, show h + 1 - 1 = h by omega, nsmul_eq_mul]; ring
    calc ‖E.eval (l' : ℂ)‖ * ‖f w / E.eval w - Q.eval w / E.eval w‖
        ≤ ‖E.eval (l' : ℂ)‖ * (‖f w‖ / ‖E.eval w‖ + ‖Q.eval w / E.eval w‖) :=
          mul_le_mul_of_nonneg_left htri (norm_nonneg _)
      _ = ‖E.eval (l' : ℂ)‖ * (‖f w‖ / ‖E.eval w‖) + ‖E.eval (l' : ℂ)‖ * ‖Q.eval w / E.eval w‖ :=
          mul_add _ _ _
      _ ≤ _ := add_le_add hterm1 hterm2
  -- Step 6: Apply Maximum Modulus Principle to `fun w => E.eval l' * q w` on `Metric.ball 0 R`
  set Bnd : ℝ := ((2 / 31 : ℝ) ^ (h * S)) * Mf +
      2 * (h : ℝ) * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps
  have hmax : ‖E.eval (l' : ℂ) * q (l' : ℂ)‖ ≤ Bnd := by
    have hdiff_mul : DiffContOnCl ℂ (fun w => E.eval (l' : ℂ) * q w) (Metric.ball (0 : ℂ) R) :=
      ((differentiable_const _).mul hq_diff).diffContOnCl
    have hfront : ∀ w ∈ frontier (Metric.ball (0 : ℂ) R), ‖E.eval (l' : ℂ) * q w‖ ≤ Bnd := by
      intro w hw
      rw [frontier_ball (0 : ℂ) hRpos.ne', Metric.mem_sphere, dist_zero_right] at hw
      rw [norm_mul]
      exact hq_circle w hw
    have hmem : (l' : ℂ) ∈ closure (Metric.ball (0 : ℂ) R) := by
      rw [closure_ball (0 : ℂ) hRpos.ne', Metric.mem_closedBall, dist_zero_right,
        Complex.norm_natCast]
      have : (l' : ℝ) ≤ 2 * (h : ℝ) := by exact_mod_cast hl'hi
      dsimp only [R]; linarith
    exact Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdiff_mul hfront hmem
  have hfl' : f (l' : ℂ) = Q.eval (l' : ℂ) + E.eval (l' : ℂ) * q (l' : ℂ) := by
    have h := hq_E (l' : ℂ); linear_combination h
  rw [hfl']
  calc ‖Q.eval (l' : ℂ) + E.eval (l' : ℂ) * q (l' : ℂ)‖
      ≤ ‖Q.eval (l' : ℂ)‖ + ‖E.eval (l' : ℂ) * q (l' : ℂ)‖ := norm_add_le _ _
    _ ≤ 2 * (h : ℝ) * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps + Bnd :=
        add_le_add hQ_eval_l' hmax
    _ = ((2 / 31 : ℝ) ^ (h * S)) * Mf +
        4 * (h : ℝ) * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
        dsimp only [Bnd]; ring

/- Section 5: Purely Discrete Shift-Operator Nonvanishing -/

def shiftAction (P : Polynomial ℚ) (u : ℕ → ℚ) (s : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * u (s + j)

lemma shiftAction_eq_sum_of_natDegree_le {P : Polynomial ℚ} {N : ℕ} (hN : P.natDegree ≤ N)
    (u : ℕ → ℚ) (s : ℕ) :
    shiftAction P u s = ∑ j ∈ Finset.range (N + 1), P.coeff j * u (s + j) := by
  unfold shiftAction
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hN))
  intro j _ hj
  rw [Finset.mem_range] at hj
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

lemma shiftAction_zero_seq (P : Polynomial ℚ) : shiftAction P (fun _ => 0) = fun _ => 0 := by
  funext s; simp [shiftAction]

lemma shiftAction_sum {ι : Type*} (I : Finset ι) (P : Polynomial ℚ) (f : ι → ℕ → ℚ) (s : ℕ) :
    shiftAction P (fun t => ∑ i ∈ I, f i t) s = ∑ i ∈ I, shiftAction P (f i) s := by
  unfold shiftAction
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

lemma shiftAction_X_sub_C (a : ℚ) (u : ℕ → ℚ) (s : ℕ) :
    shiftAction (X - C a) u s = u (s + 1) - a * u s := by
  rw [shiftAction_eq_sum_of_natDegree_le (show (X - C a).natDegree ≤ 1 by
    rw [Polynomial.natDegree_X_sub_C])]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [zero_add, add_zero, Polynomial.coeff_sub, Polynomial.coeff_X_zero,
    Polynomial.coeff_C_zero, Polynomial.coeff_X_one, Polynomial.coeff_C_succ, sub_zero, one_mul]
  ring

lemma shiftAction_mul_X_sub_C (P : Polynomial ℚ) (a : ℚ) (u : ℕ → ℚ) (s : ℕ) :
    shiftAction (P * (X - C a)) u s = shiftAction P (shiftAction (X - C a) u) s := by
  set N := P.natDegree + 1
  have hdeg : (P * (X - C a)).natDegree ≤ N := by
    exact le_trans Polynomial.natDegree_mul_le (by rw [Polynomial.natDegree_X_sub_C])
  rw [shiftAction_eq_sum_of_natDegree_le hdeg]
  have hmul_sub : P * (X - C a) = P * X - C a * P := by ring
  rw [hmul_sub]
  simp_rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, sub_mul]
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ j ∈ Finset.range (N + 1), (P * X).coeff j * u (s + j) =
      ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * u (s + j + 1) := by
    rw [Finset.sum_range_succ']
    simp only [Polynomial.coeff_mul_X_zero, zero_mul, add_zero, Polynomial.coeff_mul_X]
    apply Finset.sum_congr rfl
    intro j _
    rw [show s + (j + 1) = s + j + 1 by omega]
  have h2 : ∑ j ∈ Finset.range (N + 1), a * P.coeff j * u (s + j) =
      ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * (a * u (s + j)) := by
    rw [Finset.sum_range_succ]
    have htop : P.coeff (P.natDegree + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [htop, mul_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [h1, h2, ← Finset.sum_sub_distrib]
  change _ = ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * shiftAction (X - C a) u (s + j)
  apply Finset.sum_congr rfl
  intro j _
  rw [shiftAction_X_sub_C]; ring

lemma shiftAction_mul (P R : Polynomial ℚ) (u : ℕ → ℚ) :
    shiftAction (P * R) u = shiftAction P (shiftAction R u) := by
  induction R using Polynomial.induction_on' with
  | add R₁ R₂ ih₁ ih₂ =>
    funext s
    have hdeg1 : (P * (R₁ + R₂)).natDegree ≤ P.natDegree + max R₁.natDegree R₂.natDegree :=
      le_trans Polynomial.natDegree_mul_le (Nat.add_le_add_left (Polynomial.natDegree_add_le _ _) _)
    have hadd_act : ∀ v, shiftAction (R₁ + R₂) v = fun t => shiftAction R₁ v t + shiftAction R₂ v t := by
      intro v; funext t
      set M := max R₁.natDegree R₂.natDegree
      rw [shiftAction_eq_sum_of_natDegree_le (le_trans (Polynomial.natDegree_add_le _ _) le_rfl),
        shiftAction_eq_sum_of_natDegree_le (le_max_left R₁.natDegree R₂.natDegree),
        shiftAction_eq_sum_of_natDegree_le (le_max_right R₁.natDegree R₂.natDegree)]
      simp_rw [Polynomial.coeff_add, add_mul]
      exact Finset.sum_add_distrib
    rw [mul_add, hadd_act]
    have hP_add : shiftAction (P * R₁ + P * R₂) u s =
        shiftAction (P * R₁) u s + shiftAction (P * R₂) u s := by
      set M := max (P * R₁).natDegree (P * R₂).natDegree
      rw [shiftAction_eq_sum_of_natDegree_le (le_trans (Polynomial.natDegree_add_le _ _) le_rfl),
        shiftAction_eq_sum_of_natDegree_le (le_max_left _ _),
        shiftAction_eq_sum_of_natDegree_le (le_max_right _ _)]
      simp_rw [Polynomial.coeff_add, add_mul]
      exact Finset.sum_add_distrib
    rw [hP_add, ih₁, ih₂]
    unfold shiftAction
    simp_rw [mul_add]
    exact (Finset.sum_add_distrib).symm
  | monomial n a =>
    funext s
    have hR : shiftAction (Polynomial.monomial n a) u = fun t => a * u (t + n) := by
      funext t
      rw [shiftAction_eq_sum_of_natDegree_le (Polynomial.natDegree_monomial_le a)]
      rw [Finset.sum_eq_single n]
      · simp
      · intro j _ hne
        rw [Polynomial.coeff_monomial, if_neg hne.symm, zero_mul]
      · intro hnot; exact False.elim (hnot (Finset.mem_range.mpr (Nat.lt_succ_self n)))
    rw [hR]
    have hdeg : (P * Polynomial.monomial n a).natDegree ≤ P.natDegree + n :=
      le_trans Polynomial.natDegree_mul_le (Nat.add_le_add_left (Polynomial.natDegree_monomial_le a) _)
    rw [shiftAction_eq_sum_of_natDegree_le hdeg]
    have hmul_mon : ∀ j, (P * Polynomial.monomial n a).coeff j =
        if n ≤ j then P.coeff (j - n) * a else 0 := by
      intro j
      rw [← Polynomial.C_mul_X_pow_eq_monomial, ← mul_assoc, mul_comm P (C a), mul_assoc,
        Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
      split_ifs <;> ring
    simp_rw [hmul_mon, ite_mul, zero_mul]
    unfold shiftAction
    calc ∑ j ∈ Finset.range (P.natDegree + n + 1), (if n ≤ j then P.coeff (j - n) * a * u (s + j) else 0)
        = ∑ j ∈ Finset.Ico n (P.natDegree + n + 1), P.coeff (j - n) * a * u (s + j) := by
          rw [← Finset.sum_filter]
          have hflt : (Finset.range (P.natDegree + n + 1)).filter (fun j => n ≤ j) =
              Finset.Ico n (P.natDegree + n + 1) := by
            ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
          rw [hflt]
      _ = ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * (a * u (s + j + n)) := by
          refine Finset.sum_bij (fun j _ => j - n) ?_ ?_ ?_ ?_
          · intro j hj; simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢; omega
          · intro j₁ hj₁ j₂ hj₂ heq; simp only [Finset.mem_Ico] at hj₁ hj₂; omega
          · intro b hb; refine ⟨b + n, ?_, by omega⟩
            simp only [Finset.mem_Ico, Finset.mem_range] at hb ⊢; omega
          · intro j hj; simp only [Finset.mem_Ico] at hj
            have hadd : s + j = s + (j - n) + n := by omega
            rw [hadd]; ring

lemma natDegree_comp_X_add_one_sub_lt {Q : Polynomial ℚ} (hQ : 0 < Q.natDegree) :
    (Q.comp (X + 1) - Q).natDegree < Q.natDegree := by
  have hdeg_comp : (Q.comp (X + 1)).natDegree = Q.natDegree := by
    rw [Polynomial.natDegree_comp]
    have : (X + 1 : Polynomial ℚ).natDegree = 1 := by
      simpa using Polynomial.natDegree_X_add_C (1 : ℚ)
    rw [this, mul_one]
  have hlc_comp : (Q.comp (X + 1)).leadingCoeff = Q.leadingCoeff := by
    have hmon : (X + 1 : Polynomial ℚ).Monic := by
      simpa using Polynomial.monic_X_add_C (1 : ℚ)
    rw [Polynomial.leadingCoeff_comp (by
      have : (X + 1 : Polynomial ℚ).natDegree = 1 := by
        simpa using Polynomial.natDegree_X_add_C (1 : ℚ)
      omega)]
    simp [hmon.leadingCoeff]
  have hle : (Q.comp (X + 1) - Q).natDegree ≤ Q.natDegree - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [Polynomial.coeff_sub]
    rcases eq_or_lt_of_le (show Q.natDegree ≤ m by omega) with rfl | hgt
    · have h1 : (Q.comp (X + 1)).coeff Q.natDegree = (Q.comp (X + 1)).leadingCoeff := by
        rw [← hdeg_comp, Polynomial.coeff_natDegree]
      rw [h1, hlc_comp, Polynomial.coeff_natDegree, sub_self]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : (Q.comp (X + 1)).natDegree < m),
        Polynomial.coeff_eq_zero_of_natDegree_lt hgt, sub_self]
  omega

lemma shiftAction_pow_X_sub_C_eval_mul_pow (ω : ℚ) (d : ℕ) :
    ∀ Q : Polynomial ℚ, Q.natDegree ≤ d →
      shiftAction ((X - C ω) ^ (d + 1)) (fun s : ℕ => Q.eval (s : ℚ) * ω ^ s) = fun _ => 0 := by
  induction d with
  | zero =>
    intro Q hQ
    funext s
    rw [pow_one, shiftAction_X_sub_C]
    have hconst : Q = C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hQ)
    rw [hconst]
    simp [pow_succ]; ring
  | succ d ih =>
    intro Q hQ
    rw [pow_succ, shiftAction_mul]
    have hstep : shiftAction (X - C ω) (fun s : ℕ => Q.eval (s : ℚ) * ω ^ s) =
        fun s : ℕ => (C ω * (Q.comp (X + 1) - Q)).eval (s : ℚ) * ω ^ s := by
      funext s
      rw [shiftAction_X_sub_C, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
        Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
        pow_succ, Nat.cast_add, Nat.cast_one]
      ring
    rw [hstep]
    by_cases hQ0 : Q.natDegree = 0
    · have hconst : Q = C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hQ0
      have hzero : C ω * (Q.comp (X + 1) - Q) = 0 := by rw [hconst]; simp
      rw [hzero]
      simp only [Polynomial.eval_zero, zero_mul]
      exact shiftAction_zero_seq _
    · have hlt : (C ω * (Q.comp (X + 1) - Q)).natDegree ≤ d := by
        refine le_trans (Polynomial.natDegree_C_mul_le ω _) ?_
        have := natDegree_comp_X_add_one_sub_lt (Nat.pos_of_ne_zero hQ0)
        omega
      exact ih _ hlt

lemma exp_poly_zero_of_zero_on_Icc {ι : Type*} [Fintype ι]
    (ω : ι → ℕ) (hω_inj : Function.Injective ω) (hω_pos : ∀ i, 0 < ω i)
    (L₀ : ℕ) (Q : ι → Polynomial ℚ) (hdeg : ∀ i, (Q i).natDegree ≤ L₀)
    (hvan : ∀ s ∈ Finset.Icc 1 ((L₀ + 1) * Fintype.card ι),
      ∑ i : ι, (Q i).eval (s : ℚ) * (ω i : ℚ) ^ s = 0) :
    ∀ i, Q i = 0 := by
  classical
  set u : ℕ → ℚ := fun s => ∑ i : ι, (Q i).eval (s : ℚ) * (ω i : ℚ) ^ s
  set χ : Polynomial ℚ := ∏ i : ι, (X - C (ω i : ℚ)) ^ (L₀ + 1)
  have hχ_monic : χ.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun i _ => (Polynomial.monic_X_sub_C _).pow _
  set D := (L₀ + 1) * Fintype.card ι
  have hχ_deg : χ.natDegree = D := by
    dsimp only [χ, D]
    rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => (Polynomial.monic_X_sub_C _).pow _]
    simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
    ring
  have hχ_kill : ∀ s, shiftAction χ u s = 0 := by
    intro s
    dsimp only [u]
    rw [shiftAction_sum]
    apply Finset.sum_eq_zero
    intro i _
    have hsplit : χ = (∏ j ∈ Finset.univ.erase i, (X - C (ω j : ℚ)) ^ (L₀ + 1)) *
        (X - C (ω i : ℚ)) ^ (L₀ + 1) := by
      dsimp only [χ]
      rw [mul_comm]
      exact (Finset.mul_prod_erase Finset.univ (fun j => (X - C (ω j : ℚ)) ^ (L₀ + 1))
        (Finset.mem_univ i)).symm
    rw [hsplit, shiftAction_mul, shiftAction_pow_X_sub_C_eval_mul_pow _ L₀ (Q i) (hdeg i),
      shiftAction_zero_seq]
  -- Strong induction: u s = 0 for ALL s ≥ 1
  have hall_zero : ∀ s, 1 ≤ s → u s = 0 := by
    intro s hs
    induction s using Nat.strong_induction_on with
    | h s ih =>
      by_cases hle : s ≤ D
      · exact hvan s (Finset.mem_Icc.mpr ⟨hs, hle⟩)
      · set t := s - D
        have ht1 : 1 ≤ t := by omega
        have htd : t + D = s := by omega
        have hkill := hχ_kill t
        unfold shiftAction at hkill
        rw [hχ_deg, Finset.sum_range_succ, ← hχ_deg, hχ_monic.coeff_natDegree, one_mul,
          hχ_deg, htd] at hkill
        have hsum0 : ∑ j ∈ Finset.range D, χ.coeff j * u (t + j) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          have hjD : j < D := Finset.mem_range.mp hj
          rw [ih (t + j) (by omega) (by omega), mul_zero]
        rw [hsum0, zero_add] at hkill
        exact hkill
  -- Dominant-term limit contradiction if any Q i ≠ 0
  by_contra hnot
  push Not at hnot
  set S := Finset.univ.filter (fun i : ι => Q i ≠ 0)
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hnot
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨imax, himaxS, himax_ge⟩ := Finset.exists_max_image S ω hSne
  have hQmax_ne : Q imax ≠ 0 := (Finset.mem_filter.mp himaxS).2
  have hωmax_pos : (0 : ℝ) < (ω imax : ℝ) := by exact_mod_cast hω_pos imax
  -- For every s ≥ 1, in ℝ: (Q imax).eval s + ∑_{i ∈ S.erase imax} (Q i).eval s * (ω i / ω imax)^s = 0
  have heval_cast : ∀ (P : Polynomial ℚ) (s : ℕ),
      (P.map (algebraMap ℚ ℝ)).eval (s : ℝ) = Rat.cast (P.eval (s : ℚ)) := by
    intro P s
    rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Rat.cast_sum]
    have hdeg : (P.map (algebraMap ℚ ℝ)).natDegree = P.natDegree :=
      Polynomial.natDegree_map_eq_of_injective Rat.cast_injective P
    rw [hdeg]
    apply Finset.sum_congr rfl
    intro j _
    rw [Polynomial.coeff_map, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]
    rfl
  have hreal_eq : ∀ s : ℕ, 1 ≤ s →
      ((Q imax).map (algebraMap ℚ ℝ)).eval (s : ℝ) +
      ∑ i ∈ S.erase imax,
        ((Q i).map (algebraMap ℚ ℝ)).eval (s : ℝ) * ((ω i : ℝ) / (ω imax : ℝ)) ^ s = 0 := by
    intro s hs
    have hu0 : (u s : ℝ) = 0 := by rw [hall_zero s hs, Rat.cast_zero]
    have hdiv0 : (u s : ℝ) / (ω imax : ℝ) ^ s = 0 := by rw [hu0, zero_div]
    rw [← hdiv0]
    dsimp only [u]
    rw [Rat.cast_sum, Finset.sum_div]
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    · rw [← Finset.add_sum_erase _ _ himaxS]
      congr 1
      · rw [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
          heval_cast, mul_div_cancel_right₀ _ (pow_ne_zero s hωmax_pos.ne')]
      · apply Finset.sum_congr rfl
        intro i _
        rw [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
          heval_cast, mul_div_assoc, ← div_pow]
    · intro i _ hi
      have hQ0 : Q i = 0 := by
        by_contra hne
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
      simp [hQ0]
  -- Each term in S.erase imax tends to 0
  have htail_zero : Tendsto (fun s : ℕ =>
      ∑ i ∈ S.erase imax,
        ((Q i).map (algebraMap ℚ ℝ)).eval (s : ℝ) * ((ω i : ℝ) / (ω imax : ℝ)) ^ s)
      atTop (nhds 0) := by
    have hterm : ∀ i ∈ S.erase imax, Tendsto (fun s : ℕ =>
        ((Q i).map (algebraMap ℚ ℝ)).eval (s : ℝ) * ((ω i : ℝ) / (ω imax : ℝ)) ^ s)
        atTop (nhds 0) := by
      intro i hi
      have hiS : i ∈ S := Finset.mem_of_mem_erase hi
      have hine : i ≠ imax := Finset.ne_of_mem_erase hi
      have hlt_nat : ω i < ω imax :=
        lt_of_le_of_ne (himax_ge i hiS) (fun h => hine (hω_inj h))
      set r : ℝ := (ω i : ℝ) / (ω imax : ℝ)
      have hr0 : 0 < r := div_pos (by exact_mod_cast hω_pos i) hωmax_pos
      have hr1 : r < 1 := (div_lt_one hωmax_pos).mpr (by exact_mod_cast hlt_nat)
      have hlogr : 0 < -Real.log r := neg_pos.mpr (Real.log_neg hr0 hr1)
      set P : Polynomial ℝ := (Q i).map (algebraMap ℚ ℝ)
      have hpow_lim : ∀ j : ℕ, Tendsto (fun s : ℕ => (s : ℝ) ^ j * r ^ s) atTop (nhds 0) := by
        intro j
        have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero j).comp
          (tendsto_id.const_mul_atTop hlogr)
        have h2 := (h1.comp tendsto_natCast_atTop_atTop).const_mul ((-Real.log r) ^ j)⁻¹
        simp only [mul_zero] at h2
        refine h2.congr (fun s => ?_)
        dsimp only [Function.comp_apply, id_eq]
        have hr_pow : r ^ s = Real.exp (-((-Real.log r) * (s : ℝ))) := by
          rw [neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hr0]
        rw [hr_pow]
        have hne : (-Real.log r) ^ j ≠ 0 := pow_ne_zero j hlogr.ne'
        rw [mul_pow]; field_simp [hne]
      have hsum_lim : Tendsto (fun s : ℕ =>
          ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * ((s : ℝ) ^ j * r ^ s))
          atTop (nhds 0) := by
        have h := tendsto_finsetSum (Finset.range (P.natDegree + 1)) fun j _ =>
          by simpa using (hpow_lim j).const_mul (P.coeff j)
        simpa [Finset.sum_const_zero] using h
      refine hsum_lim.congr (fun s => ?_)
      rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _; ring
    simpa [Finset.sum_const_zero] using tendsto_finsetSum (S.erase imax) hterm
  -- Meanwhile |((Q imax).map ...).eval s| is eventually ≥ |leadingCoeff| / 2 > 0
  set Pmax : Polynomial ℝ := (Q imax).map (algebraMap ℚ ℝ)
  have hPmax_ne : Pmax ≠ 0 := by
    intro h0
    apply hQmax_ne
    exact Polynomial.map_injective (algebraMap ℚ ℝ) Rat.cast_injective
      (by rw [Polynomial.map_zero]; exact h0)
  have hlc_pos : 0 < |Pmax.leadingCoeff| := abs_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr hPmax_ne)
  have hlead_lim : Tendsto (fun s : ℕ => Pmax.eval (s : ℝ) / (s : ℝ) ^ Pmax.natDegree)
      atTop (nhds Pmax.leadingCoeff) := by
    set d := Pmax.natDegree
    have hrew : ∀ᶠ s : ℕ in atTop,
        Pmax.eval (s : ℝ) / (s : ℝ) ^ d =
          Pmax.leadingCoeff + ∑ j ∈ Finset.range d, Pmax.coeff j * ((s : ℝ) ^ (d - j))⁻¹ := by
      filter_upwards [eventually_ge_atTop 1] with s hs
      have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
      rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, add_div, Finset.sum_div]
      rw [mul_div_cancel_right₀ _ (pow_ne_zero d hs0), add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hjd : j < d := Finset.mem_range.mp hj
      rw [mul_div_assoc]
      have hpow : (s : ℝ) ^ d = (s : ℝ) ^ j * (s : ℝ) ^ (d - j) := by
        rw [← pow_add, Nat.add_sub_cancel' hjd.le]
      rw [hpow, div_mul_eq_div_div, div_self (pow_ne_zero j hs0), one_div]
    rw [tendsto_congr' hrew]
    have hsum0 : Tendsto (fun s : ℕ =>
        ∑ j ∈ Finset.range d, Pmax.coeff j * ((s : ℝ) ^ (d - j))⁻¹) atTop (nhds 0) := by
      have h := tendsto_finsetSum (Finset.range d) fun j hj => by
        have hjd : 0 < d - j := by have := Finset.mem_range.mp hj; omega
        have h1 : Tendsto (fun s : ℕ => ((s : ℝ) ^ (d - j))⁻¹) atTop (nhds 0) :=
          tendsto_inv_atTop_zero.comp
            ((tendsto_pow_atTop hjd.ne').comp tendsto_natCast_atTop_atTop)
        simpa using h1.const_mul (Pmax.coeff j)
      simpa [Finset.sum_const_zero] using h
    simpa using hsum0.const_add Pmax.leadingCoeff
  have hev_lead : ∀ᶠ s : ℕ in atTop, |Pmax.leadingCoeff| / 2 < |Pmax.eval (s : ℝ)| := by
    have h1 := ((tendsto_order.mp hlead_lim.abs).1 (|Pmax.leadingCoeff| / 2) (by linarith))
    filter_upwards [h1, eventually_ge_atTop 1] with s hs h1s
    have hpow1 : (1 : ℝ) ≤ (s : ℝ) ^ Pmax.natDegree :=
      one_le_pow₀ (by exact_mod_cast h1s)
    rw [abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hpow1), lt_div_iff₀ (lt_of_lt_of_le zero_lt_one hpow1)] at hs
    nlinarith
  have hev_tail : ∀ᶠ s : ℕ in atTop,
      |∑ i ∈ S.erase imax, ((Q i).map (algebraMap ℚ ℝ)).eval (s : ℝ) *
        ((ω i : ℝ) / (ω imax : ℝ)) ^ s| < |Pmax.leadingCoeff| / 2 :=
    (tendsto_order.mp htail_zero.abs).2 (|Pmax.leadingCoeff| / 2) (by linarith)
  have hev_all := hev_lead.and (hev_tail.and (eventually_ge_atTop 1))
  obtain ⟨s, hs_lead, hs_tail, hs1⟩ := hev_all.exists
  have heq := hreal_eq s hs1
  have habs_eq : |Pmax.eval (s : ℝ)| =
      |∑ i ∈ S.erase imax, ((Q i).map (algebraMap ℚ ℝ)).eval (s : ℝ) *
        ((ω i : ℝ) / (ω imax : ℝ)) ^ s| := by
    have hneg : Pmax.eval (s : ℝ) =
        -(∑ i ∈ S.erase imax, ((Q i).map (algebraMap ℚ ℝ)).eval (s : ℝ) *
          ((ω i : ℝ) / (ω imax : ℝ)) ^ s) := eq_neg_of_add_eq_zero_left heq
    rw [hneg, abs_neg]
  linarith

/- Section 6: Auxiliary Functions `Psi` and `G`, Derivative Recurrence, & Approximation Error -/

abbrev Idx (L₀ L m : ℕ) := Fin (L₀ + 1) × (Fin (m + 1) → Fin (L + 1))

def betaRat {m : ℕ} (b : Fin (m + 1) → ℤ) (r : Fin m) : ℚ :=
  -(b (Fin.castSucc r) : ℚ) / (b (Fin.last m) : ℚ)

def gammaRat {L₀ L m : ℕ} (b : Fin (m + 1) → ℤ) (idx : Idx L₀ L m) (r : Fin m) : ℚ :=
  ((idx.2 (Fin.castSucc r)).val : ℚ) + ((idx.2 (Fin.last m)).val : ℚ) * betaRat b r

def gammaInt {L₀ L m : ℕ} (b : Fin (m + 1) → ℤ) (idx : Idx L₀ L m) (r : Fin m) : ℤ :=
  b (Fin.last m) * ((idx.2 (Fin.castSucc r)).val : ℤ) -
    b (Fin.castSucc r) * ((idx.2 (Fin.last m)).val : ℤ)

lemma bn_mul_gammaRat {L₀ L m : ℕ} {b : Fin (m + 1) → ℤ} (hbn : b (Fin.last m) ≠ 0)
    (idx : Idx L₀ L m) (r : Fin m) :
    (b (Fin.last m) : ℚ) * gammaRat b idx r = (gammaInt b idx r : ℚ) := by
  unfold gammaRat betaRat gammaInt
  have hbnQ : (b (Fin.last m) : ℚ) ≠ 0 := by exact_mod_cast hbn
  push_cast
  field_simp [hbnQ]
  ring

lemma abs_betaRat_le_one {m : ℕ} {b : Fin (m + 1) → ℤ} (hbn : 0 < b (Fin.last m))
    (hble : ∀ i, |b i| ≤ b (Fin.last m)) (r : Fin m) :
    |(betaRat b r : ℝ)| ≤ 1 := by
  unfold betaRat
  push_cast
  have hbnR : (0 : ℝ) < (b (Fin.last m) : ℝ) := by exact_mod_cast hbn
  rw [abs_div, abs_neg, abs_of_pos hbnR, div_le_one hbnR]
  have h1 := hble (Fin.castSucc r)
  exact_mod_cast h1

lemma abs_gammaRat_le {L₀ L m : ℕ} {b : Fin (m + 1) → ℤ} (hbn : 0 < b (Fin.last m))
    (hble : ∀ i, |b i| ≤ b (Fin.last m)) (idx : Idx L₀ L m) (r : Fin m) :
    |(gammaRat b idx r : ℝ)| ≤ 2 * (L : ℝ) := by
  unfold gammaRat
  push_cast
  have h1 : ((idx.2 (Fin.castSucc r)).val : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast Nat.lt_succ_iff.mp (idx.2 (Fin.castSucc r)).isLt
  have h2 : ((idx.2 (Fin.last m)).val : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast Nat.lt_succ_iff.mp (idx.2 (Fin.last m)).isLt
  have hβ := abs_betaRat_le_one hbn hble r
  calc |((idx.2 (Fin.castSucc r)).val : ℝ) + ((idx.2 (Fin.last m)).val : ℝ) * (betaRat b r : ℝ)|
      ≤ |((idx.2 (Fin.castSucc r)).val : ℝ)| + |((idx.2 (Fin.last m)).val : ℝ) * (betaRat b r : ℝ)| :=
        abs_add_le _ _
    _ = ((idx.2 (Fin.castSucc r)).val : ℝ) + ((idx.2 (Fin.last m)).val : ℝ) * |(betaRat b r : ℝ)| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ (L : ℝ) + (L : ℝ) * 1 := by
        have : ((idx.2 (Fin.last m)).val : ℝ) * |(betaRat b r : ℝ)| ≤ (L : ℝ) * 1 :=
          mul_le_mul h2 hβ (abs_nonneg _) (Nat.cast_nonneg _)
        linarith
    _ = 2 * (L : ℝ) := by ring

lemma abs_gammaInt_le {L₀ L m : ℕ} {b : Fin (m + 1) → ℤ} (hbn : 0 < b (Fin.last m))
    (hble : ∀ i, |b i| ≤ b (Fin.last m)) (idx : Idx L₀ L m) (r : Fin m) :
    |(gammaInt b idx r : ℝ)| ≤ 2 * (b (Fin.last m) : ℝ) * (L : ℝ) := by
  have hbnR : (0 : ℝ) < (b (Fin.last m) : ℝ) := by exact_mod_cast hbn
  have heq : (gammaInt b idx r : ℝ) = (b (Fin.last m) : ℝ) * (gammaRat b idx r : ℝ) := by
    have hq := bn_mul_gammaRat (ne_of_gt hbn) idx r
    have hr := congr_arg (Rat.cast (K := ℝ)) hq
    simpa using hr.symm
  rw [heq, abs_mul, abs_of_pos hbnR]
  have := abs_gammaRat_le hbn hble idx r
  nlinarith

noncomputable def Psi {L₀ L m : ℕ} (k : ℕ) (p : Fin (m + 1) → ℕ) (b : Fin (m + 1) → ℤ)
    (c : Idx L₀ L m → ℤ) (t : Fin (m + 1) → ℕ) (s : ℕ) : ℚ :=
  ∑ idx : Idx L₀ L m, (c idx : ℚ) *
    (Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).eval (s : ℚ) *
    (∏ r : Fin m, (gammaRat b idx r) ^ (t (Fin.succ r))) *
    (∏ i : Fin (m + 1), ((p i : ℚ) ^ (idx.2 i).val) ^ s)

noncomputable def G {L₀ L m : ℕ} (k : ℕ) (p : Fin (m + 1) → ℕ) (b : Fin (m + 1) → ℤ)
    (c : Idx L₀ L m → ℤ) (t : Fin (m + 1) → ℕ) (z : ℂ) : ℂ :=
  ∑ idx : Idx L₀ L m, (c idx : ℂ) *
    ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).map (algebraMap ℚ ℂ)).eval z *
    (∏ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r))) *
    Complex.exp (z * ∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ))

lemma Psi_cleared_int {L₀ L m : ℕ} {k : ℕ} (hk : 0 < k)
    (p : Fin (m + 1) → ℕ) {b : Fin (m + 1) → ℤ} (hbn : b (Fin.last m) ≠ 0)
    (c : Idx L₀ L m → ℤ) (t : Fin (m + 1) → ℕ) (s : ℕ) :
    ∃ z : ℤ, (z : ℚ) =
      ((Nat.lcmUpto k : ℚ) ^ (t 0)) *
      ((b (Fin.last m) : ℚ) ^ (∑ r : Fin m, t (Fin.succ r))) *
      Psi k p b c t s := by
  unfold Psi
  rw [Finset.mul_sum]
  have hterm : ∀ idx : Idx L₀ L m, ∃ z : ℤ,
      (z : ℚ) =
        ((Nat.lcmUpto k : ℚ) ^ (t 0)) *
        ((b (Fin.last m) : ℚ) ^ (∑ r : Fin m, t (Fin.succ r))) *
        ((c idx : ℚ) *
          (Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).eval (s : ℚ) *
          (∏ r : Fin m, (gammaRat b idx r) ^ (t (Fin.succ r))) *
          (∏ i : Fin (m + 1), ((p i : ℚ) ^ (idx.2 i).val) ^ s)) := by
    intro idx
    obtain ⟨zF, hzF⟩ := lcmUpto_pow_mul_hasseDeriv_feldmanPoly_int hk idx.1.val (t 0) s
    refine ⟨c idx * zF * (∏ r : Fin m, (gammaInt b idx r) ^ (t (Fin.succ r))) *
        (∏ i : Fin (m + 1), ((p i : ℤ) ^ (idx.2 i).val) ^ s), ?_⟩
    have hprod_gamma :
        ((b (Fin.last m) : ℚ) ^ (∑ r : Fin m, t (Fin.succ r))) *
          (∏ r : Fin m, (gammaRat b idx r) ^ (t (Fin.succ r))) =
        ∏ r : Fin m, ((gammaInt b idx r : ℚ) ^ (t (Fin.succ r))) := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro r _
      rw [← mul_pow, bn_mul_gammaRat hbn idx r]
    push_cast
    rw [hzF, ← hprod_gamma]
    ring
  choose f hf using hterm
  refine ⟨∑ idx : Idx L₀ L m, f idx, ?_⟩
  rw [Int.cast_sum]
  exact Finset.sum_congr rfl fun idx _ => hf idx

lemma Psi_lower_of_ne_zero {L₀ L m : ℕ} {k : ℕ} (hk : 0 < k)
    (p : Fin (m + 1) → ℕ) {b : Fin (m + 1) → ℤ} (hbn : 0 < b (Fin.last m))
    (c : Idx L₀ L m → ℤ) (t : Fin (m + 1) → ℕ) (s : ℕ)
    (hne : Psi k p b c t s ≠ 0) :
    (((Nat.lcmUpto k : ℝ) ^ (t 0)) * ((b (Fin.last m) : ℝ) ^ (∑ r : Fin m, t (Fin.succ r))))⁻¹ ≤
      |(Psi k p b c t s : ℝ)| := by
  obtain ⟨z, hz⟩ := Psi_cleared_int hk p (ne_of_gt hbn) c t s
  have hden_pos : (0 : ℝ) < ((Nat.lcmUpto k : ℝ) ^ (t 0)) *
      ((b (Fin.last m) : ℝ) ^ (∑ r : Fin m, t (Fin.succ r))) := by
    have h1 : (0 : ℝ) < (Nat.lcmUpto k : ℝ) := by exact_mod_cast Nat.lcmUpto_pos k
    have h2 : (0 : ℝ) < (b (Fin.last m) : ℝ) := by exact_mod_cast hbn
    positivity
  have hz_ne : z ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at hz
    have hdenQ : ((Nat.lcmUpto k : ℚ) ^ (t 0)) *
        ((b (Fin.last m) : ℚ) ^ (∑ r : Fin m, t (Fin.succ r))) ≠ 0 := by
      have h1 : (Nat.lcmUpto k : ℚ) ≠ 0 := by exact_mod_cast (Nat.lcmUpto_pos k).ne'
      have h2 : (b (Fin.last m) : ℚ) ≠ 0 := by exact_mod_cast hbn.ne'
      positivity
    exact hne ((mul_eq_zero.mp hz.symm).resolve_left hdenQ)
  have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by
    have : (1 : ℤ) ≤ |z| := Int.one_le_abs hz_ne
    exact_mod_cast this
  have hcast : (z : ℝ) =
      (((Nat.lcmUpto k : ℝ) ^ (t 0)) * ((b (Fin.last m) : ℝ) ^ (∑ r : Fin m, t (Fin.succ r)))) *
      (Psi k p b c t s : ℝ) := by
    have := congr_arg (Rat.cast (K := ℝ)) hz
    simpa using this
  rw [hcast, abs_mul, abs_of_pos hden_pos] at hz1
  rw [inv_le_iff_one_le_mul₀' hden_pos]
  exact hz1

lemma G_differentiable {L₀ L m : ℕ} (k : ℕ) (p : Fin (m + 1) → ℕ) (b : Fin (m + 1) → ℤ)
    (c : Idx L₀ L m → ℤ) (t : Fin (m + 1) → ℕ) :
    Differentiable ℂ (G k p b c t) := by
  unfold G
  refine Differentiable.fun_sum fun idx _ => ?_
  have hpoly : Differentiable ℂ (fun z : ℂ =>
      ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).map (algebraMap ℚ ℂ)).eval z) :=
    fun z => (hasDerivAt_eval_poly _ z).differentiableAt
  have hexp : Differentiable ℂ (fun z : ℂ =>
      Complex.exp (z * ∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ))) :=
    (differentiable_id.mul_const _).cexp
  exact (((differentiable_const _).mul hpoly).mul (differentiable_const _)).mul hexp

lemma hasDerivAt_G {L₀ L m : ℕ} (k : ℕ) (p : Fin (m + 1) → ℕ) (b : Fin (m + 1) → ℤ)
    (c : Idx L₀ L m → ℤ) (t : Fin (m + 1) → ℕ) (z : ℂ) :
    HasDerivAt (G k p b c t)
      (((t 0 + 1 : ℕ) : ℂ) * G k p b c (Function.update t 0 (t 0 + 1)) z +
        ∑ r : Fin m, (Real.log (p (Fin.castSucc r) : ℝ) : ℂ) *
          G k p b c (Function.update t (Fin.succ r) (t (Fin.succ r) + 1)) z) z := by
  have hterm : ∀ idx : Idx L₀ L m,
      HasDerivAt
        (fun w => (c idx : ℂ) *
          ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).map (algebraMap ℚ ℂ)).eval w *
          (∏ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r))) *
          Complex.exp (w * ∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ)))
        (((t 0 + 1 : ℕ) : ℂ) * ((c idx : ℂ) *
            ((Polynomial.hasseDeriv (t 0 + 1) (feldmanPoly k idx.1.val)).map (algebraMap ℚ ℂ)).eval z *
            (∏ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r))) *
            Complex.exp (z * ∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ))) +
          ∑ r : Fin m, (Real.log (p (Fin.castSucc r) : ℝ) : ℂ) * ((c idx : ℂ) *
            ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).map (algebraMap ℚ ℂ)).eval z *
            (∏ r' : Fin m, ((gammaRat b idx r' : ℚ) : ℂ) ^ (Function.update t (Fin.succ r) (t (Fin.succ r) + 1) (Fin.succ r'))) *
            Complex.exp (z * ∑ r' : Fin m, ((gammaRat b idx r' : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r') : ℝ) : ℂ))))
        z := by
    intro idx
    set P : Polynomial ℂ := (feldmanPoly k idx.1.val).map (algebraMap ℚ ℂ)
    set gam : ℂ := ∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ)
    set coef : ℂ := (c idx : ℂ) * (∏ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r)))
    have hpoly : HasDerivAt (fun w => (Polynomial.hasseDeriv (t 0) P).eval w)
        (((t 0 + 1 : ℕ) : ℂ) * (Polynomial.hasseDeriv (t 0 + 1) P).eval z) z := by
      have h1 := hasDerivAt_eval_poly (Polynomial.hasseDeriv (t 0) P) z
      rw [derivative_hasseDeriv_eq, Polynomial.eval_smul, smul_eq_mul] at h1
      exact h1
    have hexp : HasDerivAt (fun w => Complex.exp (w * gam)) (gam * Complex.exp (z * gam)) z := by
      have h1 : HasDerivAt (fun w => w * gam) (1 * gam) z := (hasDerivAt_id z).mul_const gam
      rw [one_mul] at h1
      simpa [mul_comm] using h1.cexp
    have hmul := (hpoly.mul hexp).const_mul coef
    simp only [Pi.mul_apply] at hmul
    have hfun_eq : (fun w => coef * ((Polynomial.hasseDeriv (t 0) P).eval w * Complex.exp (w * gam))) =
        (fun w => (c idx : ℂ) *
          ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).map (algebraMap ℚ ℂ)).eval w *
          (∏ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r))) *
          Complex.exp (w * gam)) := by
      funext w; rw [Polynomial.hasseDeriv_map]; dsimp only [coef, P]; ring
    rw [hfun_eq] at hmul
    refine hmul.congr_deriv ?_
    rw [Polynomial.hasseDeriv_map, Polynomial.hasseDeriv_map]
    have hprod_upd : ∀ r : Fin m,
        (∏ r' : Fin m, ((gammaRat b idx r' : ℚ) : ℂ) ^
          (Function.update t (Fin.succ r) (t (Fin.succ r) + 1) (Fin.succ r'))) =
        ((gammaRat b idx r : ℚ) : ℂ) *
          (∏ r' : Fin m, ((gammaRat b idx r' : ℚ) : ℂ) ^ (t (Fin.succ r'))) := by
      intro r
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r),
        ← Finset.mul_prod_erase Finset.univ (fun r' => ((gammaRat b idx r' : ℚ) : ℂ) ^ (t (Fin.succ r')))
          (Finset.mem_univ r)]
      simp only [Function.update_self, pow_succ']
      rw [mul_assoc]
      congr 2
      apply Finset.prod_congr rfl
      intro r' hr'
      have hne : Fin.succ r' ≠ Fin.succ r := Fin.succ_injective _ |>.ne (Finset.ne_of_mem_erase hr')
      rw [Function.update_of_ne hne]
    simp_rw [hprod_upd]
    dsimp only [coef, gam, P]
    rw [mul_add]
    congr 1
    · ring
    · rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro r _; ring
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun idx _ => hterm idx)
  refine hsum.congr_deriv ?_
  unfold G
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro idx _
    have hupd0 : Function.update t 0 (t 0 + 1) 0 = t 0 + 1 := Function.update_self 0 _ t
    have hupds : ∀ r : Fin m, Function.update t 0 (t 0 + 1) (Fin.succ r) = t (Fin.succ r) :=
      fun r => Function.update_of_ne (Fin.succ_ne_zero r) _ t
    simp_rw [hupd0, hupds]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro idx _
    have hupd0 : Function.update t (Fin.succ r) (t (Fin.succ r) + 1) 0 = t 0 :=
      Function.update_of_ne (Fin.succ_ne_zero r).symm _ t
    simp_rw [hupd0]

lemma norm_iteratedDeriv_G_le {L₀ L m : ℕ} (k : ℕ) (p : Fin (m + 1) → ℕ)
    (hp : ∀ i, (p i).Prime) (b : Fin (m + 1) → ℤ) (c : Idx L₀ L m → ℤ)
    (s : ℕ) (t : Fin (m + 1) → ℕ) (z : ℂ) {Emax : ℝ} (hEmax : 0 ≤ Emax)
    (hG : ∀ u : Fin (m + 1) → ℕ, (∑ i, u i) = (∑ i, t i) + s → ‖G k p b c u z‖ ≤ Emax) :
    ‖iteratedDeriv s (G k p b c t) z‖ ≤
      (((∑ i, t i) + s + 1 : ℕ) + ∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ)) ^ s * Emax := by
  set αm : ℝ := ∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ)
  have hαm : 0 ≤ αm := Finset.sum_nonneg fun r _ =>
    Real.log_nonneg (by exact_mod_cast (hp (Fin.castSucc r)).one_lt.le)
  induction s generalizing t with
  | zero =>
    simp only [iteratedDeriv_zero, pow_zero, one_mul]
    exact hG t (by omega)
  | succ s ih =>
    rw [iteratedDeriv_succ']
    have hderiv_eq : deriv (G k p b c t) =
        fun w => ((t 0 + 1 : ℕ) : ℂ) * G k p b c (Function.update t 0 (t 0 + 1)) w +
          ∑ r : Fin m, (Real.log (p (Fin.castSucc r) : ℝ) : ℂ) *
            G k p b c (Function.update t (Fin.succ r) (t (Fin.succ r) + 1)) w := by
      funext w; exact (hasDerivAt_G k p b c t w).deriv
    rw [hderiv_eq]
    have hcd0 : ContDiffAt ℂ (s : ℕ) (fun w => ((t 0 + 1 : ℕ) : ℂ) * G k p b c (Function.update t 0 (t 0 + 1)) w) z :=
      ((differentiable_const _).mul (G_differentiable k p b c _)).contDiff.contDiffAt
    have hcd_r : ∀ r : Fin m, ContDiffAt ℂ (s : ℕ)
        (fun w => (Real.log (p (Fin.castSucc r) : ℝ) : ℂ) *
          G k p b c (Function.update t (Fin.succ r) (t (Fin.succ r) + 1)) w) z := fun r =>
      ((differentiable_const _).mul (G_differentiable k p b c _)).contDiff.contDiffAt
    have hcd_sum : ContDiffAt ℂ (s : ℕ)
        (fun w => ∑ r : Fin m, (Real.log (p (Fin.castSucc r) : ℝ) : ℂ) *
          G k p b c (Function.update t (Fin.succ r) (t (Fin.succ r) + 1)) w) z :=
      ContDiffAt.sum fun r _ => hcd_r r
    rw [iteratedDeriv_fun_add hcd0 hcd_sum, iteratedDeriv_const_mul_field,
      iteratedDeriv_fun_sum (fun r _ => hcd_r r)]
    simp_rw [iteratedDeriv_const_mul_field]
    have hsum_upd : ∀ j : Fin (m + 1), (∑ i, Function.update t j (t j + 1) i) = (∑ i, t i) + 1 := by
      intro j
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j),
        ← Finset.add_sum_erase Finset.univ t (Finset.mem_univ j)]
      simp only [Function.update_self]
      have hrest : ∑ i ∈ Finset.univ.erase j, Function.update t j (t j + 1) i =
          ∑ i ∈ Finset.univ.erase j, t i :=
        Finset.sum_congr rfl fun i hi => Function.update_of_ne (Finset.ne_of_mem_erase hi) _ t
      rw [hrest]; omega
    have hbase_eq : ∀ j : Fin (m + 1),
        (((∑ i, Function.update t j (t j + 1) i) + s + 1 : ℕ) : ℝ) + αm =
        (((∑ i, t i) + (s + 1) + 1 : ℕ) : ℝ) + αm := by
      intro j; rw [hsum_upd j]; push_cast; ring
    have hih_j : ∀ j : Fin (m + 1),
        ‖iteratedDeriv s (G k p b c (Function.update t j (t j + 1))) z‖ ≤
        ((((∑ i, t i) + (s + 1) + 1 : ℕ) : ℝ) + αm) ^ s * Emax := by
      intro j
      rw [← hbase_eq j]
      exact ih (Function.update t j (t j + 1)) (fun u hu => hG u (by rw [hu, hsum_upd j]; omega))
    have ht0_le : (t 0 : ℝ) ≤ ∑ i : Fin (m + 1), (t i : ℝ) :=
      Finset.single_le_sum (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ (0 : Fin (m + 1)))
    calc ‖((t 0 + 1 : ℕ) : ℂ) * iteratedDeriv s (G k p b c (Function.update t 0 (t 0 + 1))) z +
            ∑ r : Fin m, (Real.log (p (Fin.castSucc r) : ℝ) : ℂ) *
              iteratedDeriv s (G k p b c (Function.update t (Fin.succ r) (t (Fin.succ r) + 1))) z‖
        ≤ ‖((t 0 + 1 : ℕ) : ℂ) * iteratedDeriv s (G k p b c (Function.update t 0 (t 0 + 1))) z‖ +
            ∑ r : Fin m, ‖(Real.log (p (Fin.castSucc r) : ℝ) : ℂ) *
              iteratedDeriv s (G k p b c (Function.update t (Fin.succ r) (t (Fin.succ r) + 1))) z‖ :=
          le_trans (norm_add_le _ _) (add_le_add le_rfl (norm_sum_le _ _))
      _ ≤ ((t 0 + 1 : ℕ) : ℝ) * (((((∑ i, t i) + (s + 1) + 1 : ℕ) : ℝ) + αm) ^ s * Emax) +
            ∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ) *
              (((((∑ i, t i) + (s + 1) + 1 : ℕ) : ℝ) + αm) ^ s * Emax) := by
          apply add_le_add
          · rw [norm_mul, Complex.norm_natCast]
            exact mul_le_mul_of_nonneg_left (hih_j 0) (Nat.cast_nonneg _)
          · apply Finset.sum_le_sum
            intro r _
            have hlog0 : 0 ≤ Real.log (p (Fin.castSucc r) : ℝ) :=
              Real.log_nonneg (by exact_mod_cast (hp (Fin.castSucc r)).one_lt.le)
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlog0]
            exact mul_le_mul_of_nonneg_left (hih_j (Fin.succ r)) hlog0
      _ = (((t 0 + 1 : ℕ) : ℝ) + αm) * (((((∑ i, t i) + (s + 1) + 1 : ℕ) : ℝ) + αm) ^ s * Emax) := by
          rw [← Finset.sum_mul]; ring
      _ ≤ ((((∑ i, t i) + (s + 1) + 1 : ℕ) : ℝ) + αm) *
            (((((∑ i, t i) + (s + 1) + 1 : ℕ) : ℝ) + αm) ^ s * Emax) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          push_cast; linarith
      _ = ((((∑ i, t i) + (s + 1) + 1 : ℕ) : ℝ) + αm) ^ (s + 1) * Emax := by
          rw [pow_succ']; ring

lemma norm_G_le {L₀ L m k T₀ : ℕ} (hk : 0 < k)
    (p : Fin (m + 1) → ℕ) (hp : ∀ i, (p i).Prime)
    {b : Fin (m + 1) → ℤ} (hbn : 0 < b (Fin.last m)) (hble : ∀ i, |b i| ≤ b (Fin.last m))
    (c : Idx L₀ L m → ℤ) {Cmax : ℝ} (hCmax : ∀ idx, |(c idx : ℝ)| ≤ Cmax) (hC0 : 0 ≤ Cmax)
    {t : Fin (m + 1) → ℕ} (ht : ∑ i, t i ≤ T₀)
    {z : ℂ} {R : ℝ} (hR : ‖z‖ ≤ R) :
    ‖G k p b c t z‖ ≤
      (Fintype.card (Idx L₀ L m) : ℝ) * Cmax *
      ((Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k)) *
      ((2 * (L : ℝ) + 1) ^ T₀) *
      Real.exp (2 * (L : ℝ) * (∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ)) * R) := by
  have hR0 : 0 ≤ R := le_trans (norm_nonneg z) hR
  unfold G
  refine le_trans (norm_sum_le _ _) ?_
  calc ∑ idx : Idx L₀ L m,
        ‖(c idx : ℂ) *
          ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).map (algebraMap ℚ ℂ)).eval z *
          (∏ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r))) *
          Complex.exp (z * ∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ))‖
      ≤ ∑ _idx : Idx L₀ L m,
          Cmax * ((Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k)) *
          ((2 * (L : ℝ) + 1) ^ T₀) *
          Real.exp (2 * (L : ℝ) * (∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ)) * R) := by
        apply Finset.sum_le_sum
        intro idx _
        rw [norm_mul, norm_mul, norm_mul]
        have h1 : ‖(c idx : ℂ)‖ ≤ Cmax := by
          rw [Complex.norm_intCast]; exact hCmax idx
        have h2 : ‖((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).map (algebraMap ℚ ℂ)).eval z‖ ≤
            (Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k) :=
          norm_eval_hasseDeriv_feldmanPoly_le hk (Nat.lt_succ_iff.mp idx.1.isLt) z hR
        have h3 : ‖∏ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r))‖ ≤
            (2 * (L : ℝ) + 1) ^ T₀ := by
          rw [norm_prod]
          calc ∏ r : Fin m, ‖((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r))‖
              ≤ ∏ r : Fin m, (2 * (L : ℝ) + 1) ^ (t (Fin.succ r)) := by
                apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
                intro r _
                rw [norm_pow, Complex.norm_ratCast]
                apply pow_le_pow_left₀ (abs_nonneg _)
                linarith [abs_gammaRat_le hbn hble idx r]
            _ = (2 * (L : ℝ) + 1) ^ (∑ r : Fin m, t (Fin.succ r)) := by
                rw [Finset.prod_pow_eq_pow_sum]
            _ ≤ (2 * (L : ℝ) + 1) ^ T₀ := by
                apply pow_le_pow_right₀ (by have : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L; linarith)
                have hsum_split : ∑ i : Fin (m + 1), t i = t 0 + ∑ r : Fin m, t (Fin.succ r) :=
                  Fin.sum_univ_succ t
                omega
        have h4 : ‖Complex.exp (z * ∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ))‖ ≤
            Real.exp (2 * (L : ℝ) * (∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ)) * R) := by
          rw [Complex.norm_exp]
          apply Real.exp_le_exp.mpr
          refine le_trans (Complex.re_le_norm _) ?_
          rw [norm_mul]
          have hsum_norm : ‖∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ)‖ ≤
              2 * (L : ℝ) * ∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ) := by
            refine le_trans (norm_sum_le _ _) ?_
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum
            intro r _
            have hlog0 : 0 ≤ Real.log (p (Fin.castSucc r) : ℝ) :=
              Real.log_nonneg (by exact_mod_cast (hp (Fin.castSucc r)).one_lt.le)
            rw [norm_mul, Complex.norm_ratCast, Complex.norm_real, Real.norm_of_nonneg hlog0]
            exact mul_le_mul_of_nonneg_right (abs_gammaRat_le hbn hble idx r) hlog0
          calc ‖z‖ * ‖∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ)‖
              ≤ R * (2 * (L : ℝ) * ∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ)) :=
                mul_le_mul hR hsum_norm (norm_nonneg _) hR0
            _ = 2 * (L : ℝ) * (∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ)) * R := by ring
        have h12 := mul_le_mul h1 h2 (norm_nonneg _) hC0
        have h123 := mul_le_mul h12 h3 (norm_nonneg _) (by positivity)
        exact mul_le_mul h123 h4 (norm_nonneg _) (by positivity)
    _ = (Fintype.card (Idx L₀ L m) : ℝ) * Cmax *
        ((Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k)) *
        ((2 * (L : ℝ) + 1) ^ T₀) *
        Real.exp (2 * (L : ℝ) * (∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ)) * R) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

lemma norm_G_sub_Psi_le {L₀ L m k T₀ : ℕ} (hk : 0 < k)
    (p : Fin (m + 1) → ℕ) (hp : ∀ i, (p i).Prime)
    {b : Fin (m + 1) → ℤ} (hbn : 0 < b (Fin.last m)) (hble : ∀ i, |b i| ≤ b (Fin.last m))
    (c : Idx L₀ L m → ℤ) {Cmax : ℝ} (hCmax : ∀ idx, |(c idx : ℝ)| ≤ Cmax) (hC0 : 0 ≤ Cmax)
    {t : Fin (m + 1) → ℕ} (ht : ∑ i, t i ≤ T₀) (s : ℕ)
    (hsmall : (s : ℝ) * (L : ℝ) *
      (|∑ i : Fin (m + 1), (b i : ℝ) * Real.log (p i : ℝ)| / (b (Fin.last m) : ℝ)) ≤ 1) :
    ‖G k p b c t (s : ℂ) - ((Psi k p b c t s : ℚ) : ℂ)‖ ≤
      2 * (s : ℝ) * (L : ℝ) *
      (|∑ i : Fin (m + 1), (b i : ℝ) * Real.log (p i : ℝ)| / (b (Fin.last m) : ℝ)) *
      (Fintype.card (Idx L₀ L m) : ℝ) * Cmax *
      ((Real.exp 1 * ((s : ℝ) + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k)) *
      ((2 * (L : ℝ) + 1) ^ T₀) *
      Real.exp ((L : ℝ) * (∑ i : Fin (m + 1), Real.log (p i : ℝ)) * (s : ℝ)) := by
  set Λ : ℝ := ∑ i : Fin (m + 1), (b i : ℝ) * Real.log (p i : ℝ)
  set Λ' : ℝ := Λ / (b (Fin.last m) : ℝ)
  have hbnR : (0 : ℝ) < (b (Fin.last m) : ℝ) := by exact_mod_cast hbn
  have hΛ'abs : |Λ'| = |Λ| / (b (Fin.last m) : ℝ) := by
    rw [abs_div, abs_of_pos hbnR]
  have hlin : ∑ r : Fin m, (betaRat b r : ℝ) * Real.log (p (Fin.castSucc r) : ℝ) =
      Real.log (p (Fin.last m) : ℝ) - Λ' := by
    have hsplit : Λ = (∑ r : Fin m, (b (Fin.castSucc r) : ℝ) * Real.log (p (Fin.castSucc r) : ℝ)) +
        (b (Fin.last m) : ℝ) * Real.log (p (Fin.last m) : ℝ) := Fin.sum_univ_castSucc _
    have h1 : Λ' = (∑ r : Fin m, (b (Fin.castSucc r) : ℝ) / (b (Fin.last m) : ℝ) *
          Real.log (p (Fin.castSucc r) : ℝ)) + Real.log (p (Fin.last m) : ℝ) := by
      dsimp only [Λ']
      rw [hsplit, add_div, Finset.sum_div, mul_div_cancel_left₀ _ hbnR.ne']
      congr 1; apply Finset.sum_congr rfl; intro r _; ring
    have h2 : ∑ r : Fin m, (betaRat b r : ℝ) * Real.log (p (Fin.castSucc r) : ℝ) =
        -(∑ r : Fin m, (b (Fin.castSucc r) : ℝ) / (b (Fin.last m) : ℝ) *
          Real.log (p (Fin.castSucc r) : ℝ)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro r _; unfold betaRat; push_cast; ring
    linarith
  have heval_C : ∀ (P : Polynomial ℚ),
      (P.map (algebraMap ℚ ℂ)).eval (s : ℂ) = ((P.eval (s : ℚ) : ℚ) : ℂ) := by
    intro P
    rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Rat.cast_sum]
    have hdeg : (P.map (algebraMap ℚ ℂ)).natDegree = P.natDegree :=
      Polynomial.natDegree_map_eq_of_injective Rat.cast_injective P
    rw [hdeg]
    apply Finset.sum_congr rfl
    intro j _
    rw [Polynomial.coeff_map, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]
    rfl
  unfold G Psi
  rw [Rat.cast_sum, ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  calc ∑ idx : Idx L₀ L m,
        ‖(c idx : ℂ) *
            ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).map (algebraMap ℚ ℂ)).eval (s : ℂ) *
            (∏ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r))) *
            Complex.exp ((s : ℂ) * ∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ)) -
          (((c idx : ℚ) *
            (Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).eval (s : ℚ) *
            (∏ r : Fin m, (gammaRat b idx r) ^ (t (Fin.succ r))) *
            (∏ i : Fin (m + 1), ((p i : ℚ) ^ (idx.2 i).val) ^ s) : ℚ) : ℂ)‖
      ≤ ∑ _idx : Idx L₀ L m,
          2 * (s : ℝ) * (L : ℝ) * |Λ'| * Cmax *
          ((Real.exp 1 * ((s : ℝ) + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k)) *
          ((2 * (L : ℝ) + 1) ^ T₀) *
          Real.exp ((L : ℝ) * (∑ i : Fin (m + 1), Real.log (p i : ℝ)) * (s : ℝ)) := by
        apply Finset.sum_le_sum
        intro idx _
        have hcast_term :
            (((c idx : ℚ) *
              (Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).eval (s : ℚ) *
              (∏ r : Fin m, (gammaRat b idx r) ^ (t (Fin.succ r))) *
              (∏ i : Fin (m + 1), ((p i : ℚ) ^ (idx.2 i).val) ^ s) : ℚ) : ℂ) =
            (c idx : ℂ) *
              ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).map (algebraMap ℚ ℂ)).eval (s : ℂ) *
              (∏ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r))) *
              (∏ i : Fin (m + 1), ((p i : ℂ) ^ (idx.2 i).val) ^ s) := by
          rw [heval_C]
          push_cast
          rfl
        rw [hcast_term, ← mul_sub]
        have hexp_split :
            Complex.exp ((s : ℂ) * ∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ)) =
            (∏ i : Fin (m + 1), ((p i : ℂ) ^ (idx.2 i).val) ^ s) *
              Complex.exp (-((s : ℝ) * ((idx.2 (Fin.last m)).val : ℝ) * Λ' : ℝ)) := by
          have hsum_real :
              (s : ℝ) * (∑ r : Fin m, (gammaRat b idx r : ℝ) * Real.log (p (Fin.castSucc r) : ℝ)) =
              (∑ i : Fin (m + 1), ((s : ℝ) * ((idx.2 i).val : ℝ) * Real.log (p i : ℝ))) +
                (-((s : ℝ) * ((idx.2 (Fin.last m)).val : ℝ) * Λ')) := by
            have h1 : ∑ r : Fin m, (gammaRat b idx r : ℝ) * Real.log (p (Fin.castSucc r) : ℝ) =
                (∑ r : Fin m, ((idx.2 (Fin.castSucc r)).val : ℝ) * Real.log (p (Fin.castSucc r) : ℝ)) +
                ((idx.2 (Fin.last m)).val : ℝ) * (Real.log (p (Fin.last m) : ℝ) - Λ') := by
              rw [← hlin, Finset.mul_sum, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro r _; unfold gammaRat; push_cast; ring
            rw [h1, Fin.sum_univ_castSucc, mul_add, Finset.mul_sum]
            have h2 : ∑ r : Fin m, (s : ℝ) * (((idx.2 (Fin.castSucc r)).val : ℝ) * Real.log (p (Fin.castSucc r) : ℝ)) =
                ∑ r : Fin m, (s : ℝ) * ((idx.2 (Fin.castSucc r)).val : ℝ) * Real.log (p (Fin.castSucc r) : ℝ) :=
              Finset.sum_congr rfl fun r _ => by ring
            rw [h2]; ring
          have hsum_C :
              (s : ℂ) * ∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ) =
              ((∑ i : Fin (m + 1), ((s : ℝ) * ((idx.2 i).val : ℝ) * Real.log (p i : ℝ)) : ℝ) : ℂ) +
                ((-((s : ℝ) * ((idx.2 (Fin.last m)).val : ℝ) * Λ') : ℝ) : ℂ) := by
            have hcast1 : ((s : ℝ) * (∑ r : Fin m, (gammaRat b idx r : ℝ) * Real.log (p (Fin.castSucc r) : ℝ)) : ℝ) =
                (∑ i : Fin (m + 1), ((s : ℝ) * ((idx.2 i).val : ℝ) * Real.log (p i : ℝ))) +
                  (-((s : ℝ) * ((idx.2 (Fin.last m)).val : ℝ) * Λ')) := hsum_real
            have hcastC := congr_arg (Complex.ofReal) hcast1
            simpa [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_neg,
              Complex.ofReal_natCast, Complex.ofReal_ratCast] using hcastC
          rw [hsum_C, Complex.exp_add]
          congr 1
          · rw [Complex.ofReal_sum, Complex.exp_sum]
            apply Finset.prod_congr rfl
            intro i _
            have hpi : (0 : ℝ) < (p i : ℝ) := by exact_mod_cast (hp i).pos
            have hreal_pow : Real.exp ((s : ℝ) * ((idx.2 i).val : ℝ) * Real.log (p i : ℝ)) =
                ((p i : ℝ) ^ (idx.2 i).val) ^ s := by
              rw [← pow_mul, mul_comm (idx.2 i).val s, ← Nat.cast_mul,
                Real.exp_nat_mul, Real.exp_log hpi]
            have hC := congr_arg Complex.ofReal hreal_pow
            simpa [Complex.ofReal_exp] using hC
          · rw [Complex.ofReal_neg]
        rw [hexp_split, show (∏ i : Fin (m + 1), ((p i : ℂ) ^ (idx.2 i).val) ^ s) *
              Complex.exp (-((s : ℝ) * ((idx.2 (Fin.last m)).val : ℝ) * Λ' : ℝ)) -
              (∏ i : Fin (m + 1), ((p i : ℂ) ^ (idx.2 i).val) ^ s) =
            (∏ i : Fin (m + 1), ((p i : ℂ) ^ (idx.2 i).val) ^ s) *
              (Complex.exp (-((s : ℝ) * ((idx.2 (Fin.last m)).val : ℝ) * Λ' : ℝ)) - 1) by ring]
        rw [norm_mul, norm_mul, norm_mul, norm_mul]
        have h1 : ‖(c idx : ℂ)‖ ≤ Cmax := by rw [Complex.norm_intCast]; exact hCmax idx
        have h2 : ‖((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).map (algebraMap ℚ ℂ)).eval (s : ℂ)‖ ≤
            (Real.exp 1 * ((s : ℝ) + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k) :=
          norm_eval_hasseDeriv_feldmanPoly_le hk (Nat.lt_succ_iff.mp idx.1.isLt) (s : ℂ)
            (by rw [Complex.norm_natCast])
        have h3 : ‖∏ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r))‖ ≤
            (2 * (L : ℝ) + 1) ^ T₀ := by
          rw [norm_prod]
          calc ∏ r : Fin m, ‖((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r))‖
              ≤ ∏ r : Fin m, (2 * (L : ℝ) + 1) ^ (t (Fin.succ r)) := by
                apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
                intro r _
                rw [norm_pow, Complex.norm_ratCast]
                apply pow_le_pow_left₀ (abs_nonneg _)
                linarith [abs_gammaRat_le hbn hble idx r]
            _ = (2 * (L : ℝ) + 1) ^ (∑ r : Fin m, t (Fin.succ r)) := by
                rw [Finset.prod_pow_eq_pow_sum]
            _ ≤ (2 * (L : ℝ) + 1) ^ T₀ := by
                apply pow_le_pow_right₀ (by have : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L; linarith)
                have hsum_split : ∑ i : Fin (m + 1), t i = t 0 + ∑ r : Fin m, t (Fin.succ r) :=
                  Fin.sum_univ_succ t
                omega
        have h4 : ‖∏ i : Fin (m + 1), ((p i : ℂ) ^ (idx.2 i).val) ^ s‖ ≤
            Real.exp ((L : ℝ) * (∑ i : Fin (m + 1), Real.log (p i : ℝ)) * (s : ℝ)) := by
          rw [norm_prod, Finset.mul_sum, Finset.sum_mul, Real.exp_sum]
          apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          intro i _
          have hpi : (0 : ℝ) < (p i : ℝ) := by exact_mod_cast (hp i).pos
          have hlog0 : 0 ≤ Real.log (p i : ℝ) := Real.log_nonneg (by exact_mod_cast (hp i).one_lt.le)
          have hli : ((idx.2 i).val : ℝ) ≤ (L : ℝ) := by
            exact_mod_cast Nat.lt_succ_iff.mp (idx.2 i).isLt
          rw [norm_pow, norm_pow, Complex.norm_natCast]
          calc ((p i : ℝ) ^ (idx.2 i).val) ^ s
              = Real.exp (((idx.2 i).val : ℝ) * Real.log (p i : ℝ) * (s : ℝ)) := by
                rw [← pow_mul, mul_comm (idx.2 i).val s, mul_comm _ (s : ℝ), ← mul_assoc,
                  ← Nat.cast_mul, Real.exp_nat_mul, Real.exp_log hpi]
            _ ≤ Real.exp ((L : ℝ) * Real.log (p i : ℝ) * (s : ℝ)) := by
                apply Real.exp_le_exp.mpr
                exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hli hlog0) (Nat.cast_nonneg _)
        have h5 : ‖Complex.exp (-((s : ℝ) * ((idx.2 (Fin.last m)).val : ℝ) * Λ' : ℝ)) - 1‖ ≤
            2 * (s : ℝ) * (L : ℝ) * |Λ'| := by
          have hln : ((idx.2 (Fin.last m)).val : ℝ) ≤ (L : ℝ) := by
            exact_mod_cast Nat.lt_succ_iff.mp (idx.2 (Fin.last m)).isLt
          have hnorm_arg : ‖(-((s : ℝ) * ((idx.2 (Fin.last m)).val : ℝ) * Λ' : ℝ) : ℂ)‖ ≤
              (s : ℝ) * (L : ℝ) * |Λ'| := by
            rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
              abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hln (Nat.cast_nonneg _)) (abs_nonneg _)
          have hle1 : ‖(-((s : ℝ) * ((idx.2 (Fin.last m)).val : ℝ) * Λ' : ℝ) : ℂ)‖ ≤ 1 := by
            refine le_trans hnorm_arg ?_
            rw [hΛ'abs]; exact hsmall
          have hexp_err := Complex.norm_exp_sub_one_le hle1
          have h2mul := mul_le_mul_of_nonneg_left hnorm_arg (by norm_num : (0 : ℝ) ≤ 2)
          linarith
        have ha := mul_le_mul h1 h2 (norm_nonneg _) hC0
        have hb := mul_le_mul ha h3 (norm_nonneg _) (by positivity)
        have hc := mul_le_mul hb h4 (norm_nonneg _) (by positivity)
        have hd := mul_le_mul hc h5 (norm_nonneg _) (by positivity)
        linarith
    _ = 2 * (s : ℝ) * (L : ℝ) * (|Λ| / (b (Fin.last m) : ℝ)) *
        (Fintype.card (Idx L₀ L m) : ℝ) * Cmax *
        ((Real.exp 1 * ((s : ℝ) + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k)) *
        ((2 * (L : ℝ) + 1) ^ T₀) *
        Real.exp ((L : ℝ) * (∑ i : Fin (m + 1), Real.log (p i : ℝ)) * (s : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hΛ'abs]; ring

lemma prime_pow_prod_injective {n L : ℕ} {p : Fin n → ℕ} (hp_pr : ∀ i, (p i).Prime)
    (hp_inj : Function.Injective p) :
    Function.Injective (fun μ : Fin n → Fin (L + 1) => ∏ i : Fin n, p i ^ (μ i).val) := by
  intro μ₁ μ₂ heq
  funext i
  ext
  have h1 := congr_arg (fun x => x.factorization (p i)) heq
  have hfac : ∀ μ : Fin n → Fin (L + 1),
      (∏ j : Fin n, p j ^ (μ j).val).factorization (p i) = (μ i).val := by
    intro μ
    rw [Nat.factorization_prod (fun j _ => pow_ne_zero _ (hp_pr j).ne_zero), Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single i]
    · rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        (hp_pr i).factorization_self, mul_one]
    · intro j _ hji
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      have hne : p i ≠ p j := fun h => hji (hp_inj h).symm
      rw [(hp_pr j).factorization, Finsupp.single_eq_of_ne hne, mul_zero]
    · intro hnot; exact False.elim (hnot (Finset.mem_univ i))
  rw [hfac μ₁, hfac μ₂] at h1
  exact h1

/- Section 7: Core Baker–Feldman Lower Bound for Fixed Ordered Primes -/

lemma real_log_thirty_one_div_two_ge_two : (2 : ℝ) ≤ Real.log (31 / 2 : ℝ) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have hexp1 : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have hexp_pos : 0 < Real.exp 1 := Real.exp_pos 1
  rw [hexp2]
  nlinarith

lemma real_log_le_self_of_pos {x : ℝ} (hx : 0 < x) : Real.log x ≤ x := by
  have := Real.log_le_sub_one_of_pos hx
  linarith

lemma real_log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hlog : Real.log x = Real.log (Real.sqrt x ^ 2) := by rw [hsq]
  rw [hlog, Real.log_pow]
  push_cast
  linarith [real_log_le_self_of_pos hs_pos]

/- Modular helpers for `baker_feldman_core` -/

lemma baker_matrix_entry_bound {m L₀ L k T₀ c_h c₀ : ℕ}
    (hk_pos : 0 < k) (hL₀_eq : L₀ = c₀ * k)
    (p : Fin (m + 1) → ℕ) (hp_pr : ∀ i, (p i).Prime)
    {b : Fin (m + 1) → ℤ} (hbn_pos : 0 < b (Fin.last m)) (hb_le : ∀ i, |b i| ≤ b (Fin.last m))
    {α : ℝ} (hα_ge : ∑ i : Fin (m + 1), Real.log (p i : ℝ) ≤ α)
    (hlog2L : Real.log (2 * (L : ℝ) + 1) + 1 ≤ (0.5 : ℝ) * (k : ℝ))
    (hD_lt_k1 : Real.log (b (Fin.last m) : ℝ) < (k : ℝ) + 1)
    {s : ℕ} (hs_le : s ≤ c_h * k)
    {t : Fin (m + 1) → ℕ} (ht_sum : ∑ i : Fin (m + 1), t i ≤ T₀)
    (idx : Idx L₀ L m) (z : ℤ)
    (hz : (z : ℚ) =
      ((Nat.lcmUpto k : ℚ) ^ (t 0)) *
      ((b (Fin.last m) : ℚ) ^ (∑ r : Fin m, t (Fin.succ r))) *
      ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).eval (s : ℚ) *
        (∏ r : Fin m, (gammaRat b idx r) ^ (t (Fin.succ r))) *
        (∏ i : Fin (m + 1), ((p i : ℚ) ^ (idx.2 i).val) ^ s))) :
    |(z : ℝ)| ≤ Real.exp ((7.5 * (T₀ : ℝ) +
      ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * ((c_h : ℝ) + 2)) +
      α * (L : ℝ) * (c_h : ℝ)) * (k : ℝ)) := by
  have hkR_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
  have hbnR_pos : (0 : ℝ) < (b (Fin.last m) : ℝ) := by exact_mod_cast hbn_pos
  have hbnR_ge1 : (1 : ℝ) ≤ (b (Fin.last m) : ℝ) := by exact_mod_cast hbn_pos
  have hcast := congr_arg (Rat.cast (K := ℝ)) hz
  simp only [Rat.cast_intCast, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_prod] at hcast
  rw [hcast, abs_mul, abs_mul, abs_mul, abs_mul]
  have ht_split : t 0 + ∑ r : Fin m, t (Fin.succ r) ≤ T₀ := by
    rwa [Fin.sum_univ_succ] at ht_sum
  have ht0_le : t 0 ≤ T₀ := by omega
  have htr_le : ∑ r : Fin m, t (Fin.succ r) ≤ T₀ := by omega
  have hb1 : |((Nat.lcmUpto k : ℝ) ^ (t 0))| ≤ Real.exp (6 * (T₀ : ℝ) * (k : ℝ)) := by
    rw [abs_of_nonneg (by positivity)]
    calc (Nat.lcmUpto k : ℝ) ^ (t 0)
        ≤ (Real.exp (6 * (k : ℝ))) ^ (t 0) :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (lcmUpto_le_exp k) _
      _ = Real.exp ((t 0 : ℝ) * (6 * (k : ℝ))) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (6 * (T₀ : ℝ) * (k : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have : (t 0 : ℝ) ≤ (T₀ : ℝ) := by exact_mod_cast ht0_le
          nlinarith
  have hb2 : |Rat.cast ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).eval (s : ℚ))| ≤
      Real.exp (((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * ((c_h : ℝ) + 2)) * (k : ℝ)) := by
    set P := Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)
    have heval_C : (P.map (algebraMap ℚ ℂ)).eval (s : ℂ) = ((P.eval (s : ℚ) : ℚ) : ℂ) := by
      rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Rat.cast_sum]
      have hdeg : (P.map (algebraMap ℚ ℂ)).natDegree = P.natDegree :=
        Polynomial.natDegree_map_eq_of_injective Rat.cast_injective P
      rw [hdeg]
      apply Finset.sum_congr rfl; intro j _
      rw [Polynomial.coeff_map, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]; rfl
    have hnorm_eq : |Rat.cast (P.eval (s : ℚ))| = ‖(P.map (algebraMap ℚ ℂ)).eval (s : ℂ)‖ := by
      rw [heval_C, Complex.norm_ratCast]
    rw [hnorm_eq]
    have hsR : ‖(s : ℂ)‖ ≤ ((c_h * k : ℕ) : ℝ) := by
      rw [Complex.norm_natCast]; exact_mod_cast hs_le
    refine le_trans (norm_eval_hasseDeriv_feldmanPoly_le hk_pos (Nat.lt_succ_iff.mp idx.1.isLt) _ hsR) ?_
    have hbase_le : Real.exp 1 * (((c_h * k : ℕ) : ℝ) + 1 + (k : ℝ)) / (k : ℝ) ≤
        Real.exp 1 * ((c_h : ℝ) + 2) := by
      rw [div_le_iff₀ hkR_pos]
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
      have he0 : 0 < Real.exp 1 := Real.exp_pos 1
      push_cast; nlinarith
    have hpos_b : 0 < Real.exp 1 * ((c_h : ℝ) + 2) := by positivity
    calc (Real.exp 1 * (((c_h * k : ℕ) : ℝ) + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k)
        ≤ (Real.exp 1 * ((c_h : ℝ) + 2)) ^ (L₀ + k) :=
          pow_le_pow_left₀ (by positivity) hbase_le _
      _ = Real.exp (((L₀ + k : ℕ) : ℝ) * Real.log (Real.exp 1 * ((c_h : ℝ) + 2))) := by
          rw [Real.exp_nat_mul, Real.exp_log hpos_b]
      _ = Real.exp (((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * ((c_h : ℝ) + 2)) * (k : ℝ)) := by
          rw [hL₀_eq]; push_cast; ring_nf
  have hb3 : |((b (Fin.last m) : ℝ) ^ (∑ r : Fin m, t (Fin.succ r)))| *
      |∏ r : Fin m, ((gammaRat b idx r : ℝ) ^ (t (Fin.succ r)))| ≤
      Real.exp ((1.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) := by
    rw [← abs_mul, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, Finset.abs_prod]
    calc ∏ r : Fin m, |(b (Fin.last m) : ℝ) ^ (t (Fin.succ r)) *
            (gammaRat b idx r : ℝ) ^ (t (Fin.succ r))|
        ≤ ∏ r : Fin m, (2 * (b (Fin.last m) : ℝ) * (L : ℝ) + 1) ^ (t (Fin.succ r)) := by
          apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
          intro r _
          rw [← mul_pow, abs_pow, abs_mul, abs_of_pos hbnR_pos]
          apply pow_le_pow_left₀ (by positivity)
          have := abs_gammaRat_le hbn_pos hb_le idx r
          nlinarith
      _ = (2 * (b (Fin.last m) : ℝ) * (L : ℝ) + 1) ^ (∑ r : Fin m, t (Fin.succ r)) :=
          Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ (2 * (b (Fin.last m) : ℝ) * (L : ℝ) + 1) ^ T₀ := by
          apply pow_le_pow_right₀ _ htr_le
          have : 0 ≤ 2 * (b (Fin.last m) : ℝ) * (L : ℝ) := by positivity
          linarith
      _ ≤ ((b (Fin.last m) : ℝ) * (2 * (L : ℝ) + 1)) ^ T₀ := by
          apply pow_le_pow_left₀ (by positivity); nlinarith
      _ = Real.exp ((T₀ : ℝ) * (Real.log (b (Fin.last m) : ℝ) + Real.log (2 * (L : ℝ) + 1))) := by
          rw [Real.exp_nat_mul, Real.exp_add, Real.exp_log hbnR_pos,
            Real.exp_log (by positivity : (0 : ℝ) < 2 * (L : ℝ) + 1)]
      _ ≤ Real.exp ((1.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have hsum : Real.log (b (Fin.last m) : ℝ) + Real.log (2 * (L : ℝ) + 1) ≤ (1.5 : ℝ) * (k : ℝ) := by
            linarith
          have := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg T₀)
          linarith
  have hb4 : |∏ i : Fin (m + 1), (((p i : ℝ) ^ (idx.2 i).val) ^ s)| ≤
      Real.exp (α * (L : ℝ) * (c_h : ℝ) * (k : ℝ)) := by
    rw [abs_of_nonneg (Finset.prod_nonneg fun _ _ => by positivity)]
    have hs_leR : (s : ℝ) ≤ (c_h : ℝ) * (k : ℝ) := by exact_mod_cast hs_le
    calc ∏ i : Fin (m + 1), (((p i : ℝ) ^ (idx.2 i).val) ^ s)
        ≤ ∏ i : Fin (m + 1), Real.exp ((L : ℝ) * Real.log (p i : ℝ) * ((c_h : ℝ) * (k : ℝ))) := by
          apply Finset.prod_le_prod (fun _ _ => by positivity)
          intro i _
          have hpi : (0 : ℝ) < (p i : ℝ) := by exact_mod_cast (hp_pr i).pos
          have hlog0 : 0 ≤ Real.log (p i : ℝ) := Real.log_nonneg (by exact_mod_cast (hp_pr i).one_lt.le)
          have hli : ((idx.2 i).val : ℝ) ≤ (L : ℝ) := by
            exact_mod_cast Nat.lt_succ_iff.mp (idx.2 i).isLt
          rw [← pow_mul, ← Real.exp_log (pow_pos hpi _), Real.log_pow, Nat.cast_mul]
          apply Real.exp_le_exp.mpr
          have h1 : ((idx.2 i).val : ℝ) * (s : ℝ) ≤ (L : ℝ) * ((c_h : ℝ) * (k : ℝ)) :=
            mul_le_mul hli hs_leR (Nat.cast_nonneg _) (Nat.cast_nonneg _)
          have h2 := mul_le_mul_of_nonneg_right h1 hlog0
          linarith
      _ = Real.exp ((L : ℝ) * (∑ i : Fin (m + 1), Real.log (p i : ℝ)) * ((c_h : ℝ) * (k : ℝ))) := by
          rw [← Real.exp_sum, Finset.mul_sum, Finset.sum_mul]
      _ ≤ Real.exp (α * (L : ℝ) * (c_h : ℝ) * (k : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have hnn : 0 ≤ (L : ℝ) * ((c_h : ℝ) * (k : ℝ)) := by positivity
          nlinarith
  have hrearr :
      |((Nat.lcmUpto k : ℝ) ^ (t 0))| *
        |((b (Fin.last m) : ℝ) ^ (∑ r : Fin m, t (Fin.succ r)))| *
        (|Rat.cast ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).eval (s : ℚ))| *
          |∏ r : Fin m, ((gammaRat b idx r : ℝ) ^ (t (Fin.succ r)))| *
          |∏ i : Fin (m + 1), (((p i : ℝ) ^ (idx.2 i).val) ^ s)|) =
      |((Nat.lcmUpto k : ℝ) ^ (t 0))| *
        (|((b (Fin.last m) : ℝ) ^ (∑ r : Fin m, t (Fin.succ r)))| *
          |∏ r : Fin m, ((gammaRat b idx r : ℝ) ^ (t (Fin.succ r)))|) *
        |Rat.cast ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).eval (s : ℚ))| *
        |∏ i : Fin (m + 1), (((p i : ℝ) ^ (idx.2 i).val) ^ s)| := by ring
  rw [hrearr]
  have h13 := mul_le_mul hb1 hb3 (by positivity) (by positivity)
  have h132 := mul_le_mul h13 hb2 (abs_nonneg _) (by positivity)
  have h1324 := mul_le_mul h132 hb4 (abs_nonneg _) (by positivity)
  refine le_trans h1324 ?_
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  ring_nf; linarith

set_option maxHeartbeats 800000 in
lemma baker_extrap_step {m L₀ L k K S T₀ c_h c₀ j : ℕ}
    (hk_pos : 0 < k) (hL1 : 1 ≤ L) (hS1 : 1 ≤ S) (hc_h1 : 1 ≤ c_h) (hjK : j + 1 ≤ K)
    (hL₀_eq : L₀ = c₀ * k) (hT₀_eq : T₀ = K * S) (hc_h_eq : c_h = 32 * K)
    (p : Fin (m + 1) → ℕ) (hp_pr : ∀ i, (p i).Prime)
    {b : Fin (m + 1) → ℤ} (hbn_pos : 0 < b (Fin.last m)) (hb_le : ∀ i, |b i| ≤ b (Fin.last m))
    (hD_le_15k : Real.log (b (Fin.last m) : ℝ) ≤ (1.5 : ℝ) * (k : ℝ))
    {α M₀ C_tot Cmax : ℝ} (hα_ge1 : 1 ≤ α)
    (hα_sum : ∑ i : Fin (m + 1), Real.log (p i : ℝ) ≤ α)
    (hαm_le : ∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ) ≤ α)
    (h65α : 65 * α * (L : ℝ) ≤ (0.55 : ℝ) * (S : ℝ))
    (hM₀_eq : M₀ = 7.5 * (T₀ : ℝ) + ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * ((c_h : ℝ) + 2)) +
        α * (L : ℝ) * (c_h : ℝ))
    (hC_tot_eq : C_tot = M₀ + 10 * (T₀ : ℝ) +
        2 * ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) +
        α * (L : ℝ) * (2 : ℝ) ^ K * (c_h : ℝ) + 3 * (2 : ℝ) ^ K * (c_h : ℝ) * (S : ℝ) + 20)
    (hCtot_pos : 0 < C_tot)
    (hpoly_S_dom :
      2 * ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) + 10 * (c_h : ℝ) ≤
        (0.8 : ℝ) * (c_h : ℝ) * (S : ℝ))
    (hT0log2L : (T₀ : ℝ) * Real.log (2 * (L : ℝ) + 1) ≤ (0.5 : ℝ) * (T₀ : ℝ) * (k : ℝ))
    (hlogErr :
      Real.log (32 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (S : ℝ) *
        ((2 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2) ^ S) *
        (((T₀ : ℝ) + α + 1) ^ S) * (2 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ))) ≤ 2 * (k : ℝ))
    (hΛ'_lt : |∑ i : Fin (m + 1), (b i : ℝ) * Real.log (p i : ℝ)| / (b (Fin.last m) : ℝ) <
        Real.exp (-(C_tot + 2) * (k : ℝ)))
    (c : Idx L₀ L m → ℤ) (hCmax_nn : 0 ≤ Cmax) (hc_abs : ∀ idx, |(c idx : ℝ)| ≤ Cmax)
    (hUCmax : (Fintype.card (Idx L₀ L m) : ℝ) * Cmax ≤ Real.exp ((M₀ + 1) * (k : ℝ)))
    (hIH : ∀ s ∈ Finset.Icc 1 (2 ^ j * (c_h * k)), ∀ t : Fin (m + 1) → ℕ,
        (∑ i, t i) ≤ (K - j) * S → Psi k p b c t s = 0) :
    ∀ s ∈ Finset.Icc 1 (2 ^ (j + 1) * (c_h * k)), ∀ t : Fin (m + 1) → ℕ,
      (∑ i, t i) ≤ (K - (j + 1)) * S → Psi k p b c t s = 0 := by
  intro s hs t ht
  have hj_le : j ≤ K := by omega
  have hkR_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
  have hLR_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
  have hbnR_pos : (0 : ℝ) < (b (Fin.last m) : ℝ) := by exact_mod_cast hbn_pos
  set h₀ : ℕ := c_h * k
  have hh₀1 : 1 ≤ h₀ := Nat.mul_pos hc_h1 hk_pos
  set hj : ℕ := 2 ^ j * h₀
  have hhj1 : 1 ≤ hj := Nat.mul_pos (Nat.one_le_pow j 2 (by norm_num)) hh₀1
  have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
  have hs_hi : s ≤ 2 * hj := by
    have hmem : s ≤ 2 ^ (j + 1) * (c_h * k) := (Finset.mem_Icc.mp hs).2
    have hmul : 2 ^ (j + 1) * (c_h * k) = 2 * hj := by
      dsimp only [hj, h₀]; rw [pow_succ']; ring
    exact hmul ▸ hmem
  by_cases hle_hj : s ≤ hj
  · exact hIH s (Finset.mem_Icc.mpr ⟨hs1, hle_hj⟩) t
      (le_trans ht (Nat.mul_le_mul_right S (by omega)))
  · have hs_lo : hj < s := by omega
    by_contra hPsi_ne
    have ht_le_T0 : ∑ i, t i ≤ T₀ := by
      rw [hT₀_eq]; exact le_trans ht (Nat.mul_le_mul_right S (Nat.sub_le K (j + 1)))
    set Λ'abs : ℝ := |∑ i : Fin (m + 1), (b i : ℝ) * Real.log (p i : ℝ)| / (b (Fin.last m) : ℝ)
    have hΛ'abs_nn : 0 ≤ Λ'abs := div_nonneg (abs_nonneg _) hbnR_pos.le
    -- 1. Liouville lower bound
    have hliouv : Real.exp (-(7.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) ≤ |(Psi k p b c t s : ℝ)| := by
      refine le_trans ?_ (Psi_lower_of_ne_zero hk_pos p hbn_pos c t s hPsi_ne)
      rw [show -(7.5 : ℝ) * (T₀ : ℝ) * (k : ℝ) = -((7.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) by ring, Real.exp_neg]
      have hlcm_pos : (0 : ℝ) < (Nat.lcmUpto k : ℝ) := by exact_mod_cast Nat.lcmUpto_pos k
      apply inv_anti₀ (by positivity)
      have ht0_le : t 0 ≤ T₀ := le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)) ht_le_T0
      have htr_le : ∑ r : Fin m, t (Fin.succ r) ≤ T₀ := by
        have := Fin.sum_univ_succ t; omega
      have h1 : (Nat.lcmUpto k : ℝ) ^ (t 0) ≤ Real.exp (6 * (T₀ : ℝ) * (k : ℝ)) := by
        calc (Nat.lcmUpto k : ℝ) ^ (t 0)
            ≤ (Real.exp (6 * (k : ℝ))) ^ (t 0) :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) (lcmUpto_le_exp k) _
          _ = Real.exp ((t 0 : ℝ) * (6 * (k : ℝ))) := by rw [← Real.exp_nat_mul]
          _ ≤ Real.exp (6 * (T₀ : ℝ) * (k : ℝ)) := by
              apply Real.exp_le_exp.mpr
              have hle : (t 0 : ℝ) ≤ (T₀ : ℝ) := by exact_mod_cast ht0_le
              nlinarith only [hle, hkR_pos]
      have h2 : (b (Fin.last m) : ℝ) ^ (∑ r : Fin m, t (Fin.succ r)) ≤
          Real.exp ((1.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) := by
        calc (b (Fin.last m) : ℝ) ^ (∑ r : Fin m, t (Fin.succ r))
            = Real.exp (((∑ r : Fin m, t (Fin.succ r) : ℕ) : ℝ) * Real.log (b (Fin.last m) : ℝ)) := by
              rw [Real.exp_nat_mul, Real.exp_log hbnR_pos]
          _ ≤ Real.exp ((1.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) := by
              apply Real.exp_le_exp.mpr
              have htrR : ((∑ r : Fin m, t (Fin.succ r) : ℕ) : ℝ) ≤ (T₀ : ℝ) := by exact_mod_cast htr_le
              have hD0 : 0 ≤ Real.log (b (Fin.last m) : ℝ) :=
                Real.log_nonneg (by exact_mod_cast hbn_pos)
              have hT0nn : (0 : ℝ) ≤ (T₀ : ℝ) := Nat.cast_nonneg T₀
              nlinarith only [htrR, hD0, hD_le_15k, hT0nn, hkR_pos]
      calc (Nat.lcmUpto k : ℝ) ^ (t 0) * (b (Fin.last m) : ℝ) ^ (∑ r : Fin m, t (Fin.succ r))
          ≤ Real.exp (6 * (T₀ : ℝ) * (k : ℝ)) * Real.exp ((1.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = Real.exp ((7.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) := by
            rw [← Real.exp_add]; congr 1; ring
    -- 2. Smallness check at any l ≤ 2^K * h₀
    have hsmall_any : ∀ l : ℕ, l ≤ 2 ^ K * h₀ → (l : ℝ) * (L : ℝ) * Λ'abs ≤ 1 := by
      intro l hl
      have hlR : (l : ℝ) ≤ (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) := by
        have : l ≤ 2 ^ K * (c_h * k) := hl
        simpa [mul_assoc] using (show (l : ℝ) ≤ ((2 ^ K * (c_h * k) : ℕ) : ℝ) by exact_mod_cast this)
      have hlog_lL : Real.log ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ)) ≤ 2 * (k : ℝ) := by
        refine le_trans ?_ hlogErr
        apply Real.log_le_log (by positivity)
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) := by
          have ha : (1 : ℝ) ≤ (2 : ℝ) ^ K := one_le_pow₀ (by norm_num)
          have hb : (1 : ℝ) ≤ (c_h : ℝ) := by exact_mod_cast hc_h1
          have hc : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
          exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ha hb) hc
        have h2 : (1 : ℝ) ≤ (2 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2) ^ S := by
          apply one_le_pow₀
          have hsq : (1 : ℝ) ≤ ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2 := one_le_pow₀ h1
          linarith
        have h3 : (1 : ℝ) ≤ ((T₀ : ℝ) + α + 1) ^ S := by
          apply one_le_pow₀
          have : (0 : ℝ) ≤ (T₀ : ℝ) := Nat.cast_nonneg T₀
          linarith
        have h4 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS1
        have hge1 : (1 : ℝ) ≤ 32 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (S : ℝ) *
            ((2 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2) ^ S) *
            (((T₀ : ℝ) + α + 1) ^ S) * 2 := by
          have ha : (1 : ℝ) ≤ 32 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) := by linarith
          have hb : (1 : ℝ) ≤ 32 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) * (S : ℝ) :=
            one_le_mul_of_one_le_of_one_le ha h4
          have hc : (1 : ℝ) ≤ 32 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) * (S : ℝ) *
              ((2 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2) ^ S) :=
            one_le_mul_of_one_le_of_one_le hb h2
          have hd : (1 : ℝ) ≤ 32 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) * (S : ℝ) *
              ((2 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2) ^ S) * (((T₀ : ℝ) + α + 1) ^ S) :=
            one_le_mul_of_one_le_of_one_le hc h3
          linarith
        have hnn : 0 ≤ (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ) := by positivity
        calc (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ)
            = 1 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ)) := (one_mul _).symm
          _ ≤ (32 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (S : ℝ) *
                ((2 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2) ^ S) *
                (((T₀ : ℝ) + α + 1) ^ S) * 2) *
              ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ)) :=
              mul_le_mul_of_nonneg_right hge1 hnn
          _ = _ := by ring
      have hlL_exp : (l : ℝ) * (L : ℝ) ≤ Real.exp (2 * (k : ℝ)) := by
        calc (l : ℝ) * (L : ℝ)
            ≤ (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ) :=
              mul_le_mul_of_nonneg_right hlR (Nat.cast_nonneg L)
          _ ≤ Real.exp (2 * (k : ℝ)) := by
              rw [← Real.log_le_iff_le_exp (by positivity)]; exact hlog_lL
      calc (l : ℝ) * (L : ℝ) * Λ'abs
          ≤ Real.exp (2 * (k : ℝ)) * Real.exp (-(C_tot + 2) * (k : ℝ)) :=
            mul_le_mul hlL_exp hΛ'_lt.le hΛ'abs_nn (by positivity)
        _ = Real.exp (-C_tot * (k : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith only [hCtot_pos, hkR_pos])
        _ = 1 := Real.exp_zero
    -- 3. Common upper bound on `‖G u l - Psi u l‖`
    set E_diff : ℝ :=
      2 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ) * Λ'abs *
      Real.exp ((M₀ + 1 + ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) +
        (0.5 : ℝ) * (T₀ : ℝ) + α * (L : ℝ) * (2 : ℝ) ^ K * (c_h : ℝ)) * (k : ℝ))
    have hdiff_bound : ∀ l : ℕ, l ≤ 2 ^ K * h₀ → ∀ u : Fin (m + 1) → ℕ, (∑ i, u i) ≤ T₀ →
        ‖G k p b c u (l : ℂ) - ((Psi k p b c u l : ℚ) : ℂ)‖ ≤ E_diff := by
      intro l hl u hu
      refine le_trans (norm_G_sub_Psi_le hk_pos p hp_pr hbn_pos hb_le c hc_abs hCmax_nn hu l (hsmall_any l hl)) ?_
      have hlR : (l : ℝ) ≤ (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) := by
        have : l ≤ 2 ^ K * (c_h * k) := hl
        simpa [mul_assoc] using (show (l : ℝ) ≤ ((2 ^ K * (c_h * k) : ℕ) : ℝ) by exact_mod_cast this)
      have hP_le : (Real.exp 1 * ((l : ℝ) + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k) ≤
          Real.exp (((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) * (k : ℝ)) := by
        have hbase : Real.exp 1 * ((l : ℝ) + 1 + (k : ℝ)) / (k : ℝ) ≤
            Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2) := by
          rw [div_le_iff₀ hkR_pos]
          have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
          have he0 : 0 < Real.exp 1 := Real.exp_pos 1
          have h2Kc : 0 ≤ (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) := by positivity
          nlinarith only [hlR, hk1, he0, h2Kc]
        calc (Real.exp 1 * ((l : ℝ) + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k)
            ≤ (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) ^ (L₀ + k) :=
              pow_le_pow_left₀ (by positivity) hbase _
          _ = Real.exp (((L₀ + k : ℕ) : ℝ) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2))) := by
              rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
          _ = Real.exp (((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) * (k : ℝ)) := by
              rw [hL₀_eq]; push_cast; ring_nf
      have h2L_le : (2 * (L : ℝ) + 1) ^ T₀ ≤ Real.exp ((0.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) := by
        rw [← Real.exp_log (by positivity : (0 : ℝ) < (2 * (L : ℝ) + 1) ^ T₀), Real.log_pow]
        exact Real.exp_le_exp.mpr hT0log2L
      have hexp_le : Real.exp ((L : ℝ) * (∑ i : Fin (m + 1), Real.log (p i : ℝ)) * (l : ℝ)) ≤
          Real.exp (α * (L : ℝ) * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hsum_nn : 0 ≤ ∑ i : Fin (m + 1), Real.log (p i : ℝ) :=
          Finset.sum_nonneg fun i _ => Real.log_nonneg (by exact_mod_cast (hp_pr i).one_lt.le)
        have h1 := mul_le_mul hα_sum hlR (Nat.cast_nonneg l) (by linarith)
        have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg L)
        linarith
      have hfront : 2 * (l : ℝ) * (L : ℝ) * Λ'abs ≤ 2 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ) * Λ'abs := by
        have hnn : 0 ≤ 2 * (L : ℝ) * Λ'abs := by positivity
        nlinarith only [hlR, hnn]
      have hprod1 := mul_le_mul hUCmax hP_le (by positivity) (by positivity)
      have hprod2 := mul_le_mul hprod1 h2L_le (by positivity) (by positivity)
      have hprod3 := mul_le_mul hprod2 hexp_le (by positivity) (by positivity)
      have hprod4 := mul_le_mul hfront hprod3 (by positivity) (by positivity)
      refine le_trans ?_ (le_trans hprod4 ?_)
      · apply le_of_eq; ring
      · apply le_of_eq
        dsimp only [E_diff]
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1; congr 1; ring
    -- 4. Circle bound Mf on ‖w‖ = 32 * hj
    set Mf : ℝ := Real.exp ((M₀ + 1 + ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) +
        (0.5 : ℝ) * (T₀ : ℝ) + 64 * α * (L : ℝ) * (2 : ℝ) ^ j * (c_h : ℝ)) * (k : ℝ))
    have hcircle : ∀ w : ℂ, ‖w‖ = 32 * (hj : ℝ) → ‖G k p b c t w‖ ≤ Mf := by
      intro w hw
      refine le_trans (norm_G_le hk_pos p hp_pr hbn_pos hb_le c hc_abs hCmax_nn ht_le_T0 hw.le) ?_
      have h2j_le : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hj_le
      have hP_le : (Real.exp 1 * (32 * (hj : ℝ) + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k) ≤
          Real.exp (((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) * (k : ℝ)) := by
        have hbase : Real.exp 1 * (32 * (hj : ℝ) + 1 + (k : ℝ)) / (k : ℝ) ≤
            Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2) := by
          rw [div_le_iff₀ hkR_pos]
          have hhj_eq : (hj : ℝ) = (2 : ℝ) ^ j * (c_h : ℝ) * (k : ℝ) := by
            dsimp only [hj, h₀]; push_cast; ring
          have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
          have he0 : 0 < Real.exp 1 := Real.exp_pos 1
          have hck : 0 ≤ (c_h : ℝ) * (k : ℝ) := by positivity
          have h2j_mul : (2 : ℝ) ^ j * ((c_h : ℝ) * (k : ℝ)) ≤ (2 : ℝ) ^ K * ((c_h : ℝ) * (k : ℝ)) :=
            mul_le_mul_of_nonneg_right h2j_le hck
          rw [hhj_eq]; nlinarith only [h2j_mul, hk1, he0]
        calc (Real.exp 1 * (32 * (hj : ℝ) + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k)
            ≤ (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) ^ (L₀ + k) :=
              pow_le_pow_left₀ (by positivity) hbase _
          _ = Real.exp (((L₀ + k : ℕ) : ℝ) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2))) := by
              rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
          _ = Real.exp (((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) * (k : ℝ)) := by
              rw [hL₀_eq]; push_cast; ring_nf
      have h2L_le : (2 * (L : ℝ) + 1) ^ T₀ ≤ Real.exp ((0.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) := by
        rw [← Real.exp_log (by positivity : (0 : ℝ) < (2 * (L : ℝ) + 1) ^ T₀), Real.log_pow]
        exact Real.exp_le_exp.mpr hT0log2L
      have hexp_le : Real.exp (2 * (L : ℝ) * (∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ)) * (32 * (hj : ℝ))) ≤
          Real.exp (64 * α * (L : ℝ) * (2 : ℝ) ^ j * (c_h : ℝ) * (k : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hhj_eq : (hj : ℝ) = (2 : ℝ) ^ j * (c_h : ℝ) * (k : ℝ) := by
          dsimp only [hj, h₀]; push_cast; ring
        rw [hhj_eq]
        have hnn : 0 ≤ 2 * (L : ℝ) * (32 * ((2 : ℝ) ^ j * (c_h : ℝ) * (k : ℝ))) := by positivity
        nlinarith only [hαm_le, hnn]
      have h1 := mul_le_mul hUCmax hP_le (by positivity) (by positivity)
      have h2 := mul_le_mul h1 h2L_le (by positivity) (by positivity)
      have h3 := mul_le_mul h2 hexp_le (by positivity) (by positivity)
      refine le_trans h3 (le_of_eq ?_)
      dsimp only [Mf]
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    -- 5. Derivative bound eps at l ∈ Icc 1 hj and s' < S
    set eps : ℝ := (((T₀ : ℝ) + α + 1) ^ S) * E_diff
    have heps_nn : 0 ≤ eps := by positivity
    have hderiv : ∀ l ∈ Finset.Icc 1 hj, ∀ s' < S,
        ‖iteratedDeriv s' (G k p b c t) (l : ℂ) / (s'.factorial : ℂ)‖ ≤ eps := by
      intro l hl s' hs'
      have hl_hi : l ≤ 2 ^ K * h₀ :=
        le_trans (Finset.mem_Icc.mp hl).2 (Nat.mul_le_mul_right h₀ (Nat.pow_le_pow_right (by norm_num) hj_le))
      have hfac1 : (1 : ℝ) ≤ (s'.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos s'
      rw [norm_div, Complex.norm_natCast]
      refine le_trans (div_le_self (norm_nonneg _) hfac1) ?_
      have hG_at_l : ∀ u : Fin (m + 1) → ℕ, (∑ i, u i) = (∑ i, t i) + s' →
          ‖G k p b c u (l : ℂ)‖ ≤ E_diff := by
        intro u hu
        have hu_le : ∑ i, u i ≤ (K - j) * S := by
          have h1 : (K - (j + 1)) * S + S = (K - j) * S := by
            have : K - j = K - (j + 1) + 1 := by omega
            rw [this, Nat.add_mul, one_mul]
          omega
        have hPsi0 : Psi k p b c u l = 0 := hIH l hl u hu_le
        have hsub := hdiff_bound l hl_hi u (by rw [hT₀_eq]; exact le_trans hu_le (Nat.mul_le_mul_right S (Nat.sub_le K j)))
        rwa [hPsi0, Rat.cast_zero, sub_zero] at hsub
      refine le_trans (norm_iteratedDeriv_G_le k p hp_pr b c s' t (l : ℂ) (by positivity) hG_at_l) ?_
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hbase1 : (((∑ i, t i) + s' + 1 : ℕ) : ℝ) + ∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ) ≤
          (T₀ : ℝ) + α + 1 := by
        have hts : ∑ i, t i + s' ≤ T₀ := by
          rw [hT₀_eq]
          have h1 : (K - (j + 1)) * S + S ≤ K * S := by
            have : K - (j + 1) + 1 ≤ K := by omega
            calc (K - (j + 1)) * S + S = (K - (j + 1) + 1) * S := by ring
              _ ≤ K * S := Nat.mul_le_mul_right S this
          omega
        have htsR : ((∑ i, t i + s' : ℕ) : ℝ) ≤ (T₀ : ℝ) := by exact_mod_cast hts
        push_cast at htsR ⊢; linarith
      have hge1 : (1 : ℝ) ≤ (T₀ : ℝ) + α + 1 := by
        have : (0 : ℝ) ≤ (T₀ : ℝ) := Nat.cast_nonneg T₀
        linarith
      calc ((((∑ i, t i) + s' + 1 : ℕ) : ℝ) + ∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ)) ^ s'
          ≤ ((T₀ : ℝ) + α + 1) ^ s' := pow_le_pow_left₀ (by positivity) hbase1 s'
        _ ≤ ((T₀ : ℝ) + α + 1) ^ S := pow_le_pow_right₀ hge1 (le_of_lt hs')
    -- 6. Apply Hermite-Schwarz
    have hHS := hermite_schwarz_bound (G_differentiable k p b c t) hhj1 hS1 hs_lo hs_hi
      (by positivity) heps_nn hcircle hderiv
    -- 7. Compare all three terms to Liouville lower bound
    have hterm1_lt : ((2 / 31 : ℝ) ^ (hj * S)) * Mf < (1 / 2 : ℝ) * Real.exp (-(7.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) := by
      have hpow_le : (2 / 31 : ℝ) ^ (hj * S) ≤ Real.exp (-2 * (hj : ℝ) * (S : ℝ)) := by
        have hpos : (0 : ℝ) < 2 / 31 := by norm_num
        rw [← Real.exp_log (pow_pos hpos _), Real.log_pow]
        apply Real.exp_le_exp.mpr
        have hlog : Real.log (2 / 31 : ℝ) ≤ -2 := by
          have hinv : Real.log (2 / 31 : ℝ) = -Real.log (31 / 2 : ℝ) := by
            rw [← Real.log_inv]; norm_num
          linarith [real_log_thirty_one_div_two_ge_two]
        have hnn : (0 : ℝ) ≤ ((hj * S : ℕ) : ℝ) := Nat.cast_nonneg _
        push_cast at hnn ⊢; nlinarith only [hlog, hnn]
      have h12 : (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
      rw [h12, ← Real.exp_add]
      refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right hpow_le (by positivity)) ?_
      dsimp only [Mf]
      rw [← Real.exp_add]
      apply Real.exp_lt_exp.mpr
      have h2j1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      have hhj_eq : (hj : ℝ) = (2 : ℝ) ^ j * (c_h : ℝ) * (k : ℝ) := by
        dsimp only [hj, h₀]; push_cast; ring
      have hlog2 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
      have hlog_mono : Real.log (Real.exp 1 * ((c_h : ℝ) + 2)) ≤
          Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) := by
        apply Real.log_le_log (by positivity)
        have h2K1 : (1 : ℝ) ≤ (2 : ℝ) ^ K := one_le_pow₀ (by norm_num)
        have he0 : 0 < Real.exp 1 := Real.exp_pos 1
        have hch0 : (0 : ℝ) ≤ (c_h : ℝ) := Nat.cast_nonneg _
        have h32 : (c_h : ℝ) + 2 ≤ 32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2 := by nlinarith only [h2K1, hch0]
        exact mul_le_mul_of_nonneg_left h32 he0.le
      have hT0R : (T₀ : ℝ) = (K : ℝ) * (S : ℝ) := by rw [hT₀_eq]; push_cast; rfl
      have hchR : (c_h : ℝ) = 32 * (K : ℝ) := by rw [hc_h_eq]; push_cast; rfl
      have h16T0 : (15.5 : ℝ) * (T₀ : ℝ) ≤ (0.5 : ℝ) * (c_h : ℝ) * (S : ℝ) := by
        rw [hT0R, hchR]
        have hKS : (0 : ℝ) ≤ (K : ℝ) * (S : ℝ) := by positivity
        linarith
      have hch1R : (1 : ℝ) ≤ (c_h : ℝ) := by exact_mod_cast hc_h1
      have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
      have hS1R : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS1
      have hchS_nn : (0 : ℝ) ≤ (c_h : ℝ) * (S : ℝ) := by positivity
      have h2j_mul : (0.5 : ℝ) * (c_h : ℝ) * (S : ℝ) + (0.8 : ℝ) * (c_h : ℝ) * (S : ℝ) ≤
          (1.3 : ℝ) * ((2 : ℝ) ^ j * (c_h : ℝ) * (S : ℝ)) := by
        have := mul_le_mul_of_nonneg_right h2j1 hchS_nn
        linarith
      have h65_mul : α * (L : ℝ) * (c_h : ℝ) + 64 * α * (L : ℝ) * (2 : ℝ) ^ j * (c_h : ℝ) ≤
          65 * α * (L : ℝ) * ((2 : ℝ) ^ j * (c_h : ℝ)) := by
        have hnn : 0 ≤ α * (L : ℝ) * (c_h : ℝ) := by positivity
        have := mul_le_mul_of_nonneg_left h2j1 hnn
        linarith
      have h65_bnd : 65 * α * (L : ℝ) * ((2 : ℝ) ^ j * (c_h : ℝ)) ≤
          (0.55 : ℝ) * ((2 : ℝ) ^ j * (c_h : ℝ) * (S : ℝ)) := by
        have hnn : 0 ≤ (2 : ℝ) ^ j * (c_h : ℝ) := by positivity
        have := mul_le_mul_of_nonneg_right h65α hnn
        linarith
      have hmain_per_k :
          M₀ + 1 + ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) +
            (0.5 : ℝ) * (T₀ : ℝ) + 64 * α * (L : ℝ) * (2 : ℝ) ^ j * (c_h : ℝ) +
            (7.5 : ℝ) * (T₀ : ℝ) + 1 <
          2 * ((2 : ℝ) ^ j * (c_h : ℝ) * (S : ℝ)) := by
        rw [hM₀_eq]
        have h2c0 : ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * ((c_h : ℝ) + 2)) ≤
            ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left hlog_mono (by positivity)
        have h015 : (0.15 : ℝ) * ((2 : ℝ) ^ j * (c_h : ℝ) * (S : ℝ)) > 0 := by positivity
        linarith
      rw [hhj_eq]
      have hmulk := mul_lt_mul_of_pos_right hmain_per_k hkR_pos
      linarith
    have hterm2_lt :
        4 * (hj : ℝ) * (S : ℝ) * ((2 * (hj : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (hj * S)) * eps <
          (1 / 4 : ℝ) * Real.exp (-(7.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) := by
      have h2j_le : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hj_le
      have hhj_le : (hj : ℝ) ≤ (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) := by
        have : (hj : ℝ) = (2 : ℝ) ^ j * (c_h : ℝ) * (k : ℝ) := by dsimp only [hj, h₀]; push_cast; ring
        rw [this]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2j_le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
      have hpoly_part :
          4 * (hj : ℝ) * (S : ℝ) * ((2 * (hj : ℝ) ^ 2) ^ S) * (((T₀ : ℝ) + α + 1) ^ S) *
            (2 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ)) ≤
          (1 / 4 : ℝ) * Real.exp (2 * (k : ℝ)) := by
        have hle :
            16 * (hj : ℝ) * (S : ℝ) * ((2 * (hj : ℝ) ^ 2) ^ S) * (((T₀ : ℝ) + α + 1) ^ S) *
              (2 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ)) ≤
            32 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (S : ℝ) *
              ((2 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2) ^ S) *
              (((T₀ : ℝ) + α + 1) ^ S) * (2 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ)) := by
          have hsq : (hj : ℝ) ^ 2 ≤ ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hhj_le 2
          have hpow : (2 * (hj : ℝ) ^ 2) ^ S ≤ (2 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2) ^ S :=
            pow_le_pow_left₀ (by positivity) (by linarith) S
          have h16_32 : 16 * (hj : ℝ) ≤ 32 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) := by linarith
          have h1 := mul_le_mul_of_nonneg_right h16_32 (Nat.cast_nonneg S)
          have h2 := mul_le_mul h1 hpow (by positivity) (by positivity)
          have h3 := mul_le_mul_of_nonneg_right h2 (show 0 ≤ (((T₀ : ℝ) + α + 1) ^ S) *
              (2 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ)) by positivity)
          linarith
        have hexp := (Real.log_le_iff_le_exp (by positivity)).mp hlogErr
        linarith
      have h16_le : (16 : ℝ) ^ (hj * S) ≤ Real.exp (3 * (2 : ℝ) ^ K * (c_h : ℝ) * (S : ℝ) * (k : ℝ)) := by
        rw [← Real.exp_log (by positivity : (0 : ℝ) < (16 : ℝ) ^ (hj * S)), Real.log_pow]
        apply Real.exp_le_exp.mpr
        have hlog16 : Real.log 16 ≤ 3 := by
          have h16 : (16 : ℝ) = 2 ^ 4 := by norm_num
          rw [h16, Real.log_pow]; push_cast
          linarith [Real.log_two_lt_d9]
        have hprod_le : ((hj * S : ℕ) : ℝ) ≤ (2 : ℝ) ^ K * (c_h : ℝ) * (S : ℝ) * (k : ℝ) := by
          push_cast
          have := mul_le_mul_of_nonneg_right hhj_le (Nat.cast_nonneg S)
          linarith
        have hnn : (0 : ℝ) ≤ ((hj * S : ℕ) : ℝ) := Nat.cast_nonneg _
        nlinarith only [hlog16, hprod_le, hnn]
      have hrearr :
          4 * (hj : ℝ) * (S : ℝ) * ((2 * (hj : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (hj * S)) * eps =
          (4 * (hj : ℝ) * (S : ℝ) * ((2 * (hj : ℝ) ^ 2) ^ S) * (((T₀ : ℝ) + α + 1) ^ S) *
            (2 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ))) *
          ((16 : ℝ) ^ (hj * S)) * Λ'abs *
          Real.exp ((M₀ + 1 + ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) +
            (0.5 : ℝ) * (T₀ : ℝ) + α * (L : ℝ) * (2 : ℝ) ^ K * (c_h : ℝ)) * (k : ℝ)) := by
        dsimp only [eps, E_diff]; ring
      rw [hrearr]
      have h1 := mul_le_mul hpoly_part h16_le (by positivity) (by positivity)
      have h2 : (4 * (hj : ℝ) * (S : ℝ) * ((2 * (hj : ℝ) ^ 2) ^ S) * (((T₀ : ℝ) + α + 1) ^ S) *
            (2 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ))) * ((16 : ℝ) ^ (hj * S)) * Λ'abs <
          ((1 / 4 : ℝ) * Real.exp (2 * (k : ℝ)) * Real.exp (3 * (2 : ℝ) ^ K * (c_h : ℝ) * (S : ℝ) * (k : ℝ))) *
            Real.exp (-(C_tot + 2) * (k : ℝ)) := by
        have hpos_lhs : 0 < (1 / 4 : ℝ) * Real.exp (2 * (k : ℝ)) *
            Real.exp (3 * (2 : ℝ) ^ K * (c_h : ℝ) * (S : ℝ) * (k : ℝ)) := by positivity
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right h1 hΛ'abs_nn)
          (mul_lt_mul_of_pos_left hΛ'_lt hpos_lhs)
      refine lt_of_lt_of_le (mul_lt_mul_of_pos_right h2 (Real.exp_pos _)) ?_
      rw [mul_assoc, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have hlog0 : 0 ≤ Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) := by
        apply Real.log_nonneg
        have he1 : (1 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
        have h2K1 : (1 : ℝ) ≤ (2 : ℝ) ^ K := one_le_pow₀ (by norm_num)
        have hch1 : (1 : ℝ) ≤ (c_h : ℝ) := by exact_mod_cast hc_h1
        have h32 : (1 : ℝ) ≤ 32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2 := by
          have := one_le_mul_of_one_le_of_one_le h2K1 hch1; linarith
        exact one_le_mul_of_one_le_of_one_le he1 h32
      have hT0nn : (0 : ℝ) ≤ (T₀ : ℝ) := Nat.cast_nonneg T₀
      have hc0nn : (0 : ℝ) ≤ (c₀ : ℝ) + 1 := by positivity
      have hexp_per_k :
          2 + 3 * (2 : ℝ) ^ K * (c_h : ℝ) * (S : ℝ) - (C_tot + 2) +
            (M₀ + 1 + ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) +
              (0.5 : ℝ) * (T₀ : ℝ) + α * (L : ℝ) * (2 : ℝ) ^ K * (c_h : ℝ)) ≤
          -(7.5 : ℝ) * (T₀ : ℝ) := by
        rw [hC_tot_eq]
        have hmul_log : 0 ≤ ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) :=
          mul_nonneg hc0nn hlog0
        linarith
      have hmulk := mul_le_mul_of_nonneg_right hexp_per_k hkR_pos.le
      linarith
    have hterm3_lt : ‖G k p b c t (s : ℂ) - ((Psi k p b c t s : ℚ) : ℂ)‖ <
        (1 / 4 : ℝ) * Real.exp (-(7.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) := by
      have hs_le_max : s ≤ 2 ^ K * h₀ := by
        have h1 : 2 ^ (j + 1) ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hjK
        exact le_trans (Finset.mem_Icc.mp hs).2 (Nat.mul_le_mul_right h₀ h1)
      refine lt_of_le_of_lt (hdiff_bound s hs_le_max t ht_le_T0) ?_
      refine lt_of_le_of_lt ?_ hterm2_lt
      have hhjR : (1 : ℝ) ≤ (hj : ℝ) := by exact_mod_cast hhj1
      have hSR : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS1
      have h1 : (1 : ℝ) ≤ (2 * (hj : ℝ) ^ 2) ^ S := by
        apply one_le_pow₀
        have : (1 : ℝ) ≤ (hj : ℝ) ^ 2 := one_le_pow₀ hhjR
        linarith
      have h2 : (1 : ℝ) ≤ (16 : ℝ) ^ (hj * S) := one_le_pow₀ (by norm_num)
      have h3 : (1 : ℝ) ≤ ((T₀ : ℝ) + α + 1) ^ S := by
        apply one_le_pow₀
        have : (0 : ℝ) ≤ (T₀ : ℝ) := Nat.cast_nonneg T₀
        linarith
      have hge1 : (1 : ℝ) ≤ 4 * (hj : ℝ) * (S : ℝ) * ((2 * (hj : ℝ) ^ 2) ^ S) *
          ((16 : ℝ) ^ (hj * S)) * (((T₀ : ℝ) + α + 1) ^ S) := by
        have ha : (1 : ℝ) ≤ 4 * (hj : ℝ) := by linarith
        have hb := one_le_mul_of_one_le_of_one_le ha hSR
        have hc := one_le_mul_of_one_le_of_one_le hb h1
        have hd := one_le_mul_of_one_le_of_one_le hc h2
        exact one_le_mul_of_one_le_of_one_le hd h3
      have hEd0 : 0 ≤ E_diff := by positivity
      calc E_diff = 1 * E_diff := (one_mul _).symm
        _ ≤ (4 * (hj : ℝ) * (S : ℝ) * ((2 * (hj : ℝ) ^ 2) ^ S) *
              ((16 : ℝ) ^ (hj * S)) * (((T₀ : ℝ) + α + 1) ^ S)) * E_diff :=
            mul_le_mul_of_nonneg_right hge1 hEd0
        _ = 4 * (hj : ℝ) * (S : ℝ) * ((2 * (hj : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (hj * S)) * eps := by
            dsimp only [eps]; ring
    have hPsi_norm : |(Psi k p b c t s : ℝ)| = ‖((Psi k p b c t s : ℚ) : ℂ)‖ := by
      rw [Complex.norm_ratCast]
    have htri : ‖((Psi k p b c t s : ℚ) : ℂ)‖ ≤
        ‖G k p b c t (s : ℂ) - ((Psi k p b c t s : ℚ) : ℂ)‖ + ‖G k p b c t (s : ℂ)‖ := by
      have heq : ((Psi k p b c t s : ℚ) : ℂ) =
          G k p b c t (s : ℂ) - (G k p b c t (s : ℂ) - ((Psi k p b c t s : ℚ) : ℂ)) := by ring
      calc ‖((Psi k p b c t s : ℚ) : ℂ)‖
          = ‖G k p b c t (s : ℂ) - (G k p b c t (s : ℂ) - ((Psi k p b c t s : ℚ) : ℂ))‖ := by
              congr 1
        _ ≤ ‖G k p b c t (s : ℂ)‖ + ‖G k p b c t (s : ℂ) - ((Psi k p b c t s : ℚ) : ℂ)‖ :=
            norm_sub_le _ _
        _ = _ := add_comm _ _
    linarith

lemma explicit_u_base (d : ℕ) :
    ∃ s₀ : ℕ, 2 * d ≤ s₀ ∧ ∀ s : ℕ, s₀ ≤ s → (2 * s) ^ d ≤ 2 ^ s := by
  have hlim : Tendsto (fun s : ℕ => ((2 * (s : ℝ)) ^ d) / (2 : ℝ) ^ s) atTop (nhds 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ d * Real.exp (-(Real.log 2) * x)) atTop (nhds 0) := by
      have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have h2 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d
      have h3 := h2.comp (tendsto_id.const_mul_atTop hpos)
      have h4 := h3.const_mul ((Real.log 2) ^ d)⁻¹
      simp only [mul_zero] at h4
      refine h4.congr (fun x => ?_)
      have hne : Real.log 2 ^ d ≠ 0 := pow_ne_zero d hpos.ne'
      simp only [Function.comp_apply, id_eq]
      rw [mul_pow, neg_mul]
      field_simp [hne]
    have h5 := (h1.comp tendsto_natCast_atTop_atTop).const_mul ((2 : ℝ) ^ d)
    simp only [mul_zero] at h5
    refine h5.congr (fun s => ?_)
    have h2pow : (2 : ℝ) ^ s = Real.exp ((s : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    simp only [Function.comp_apply]
    rw [h2pow, mul_pow, div_eq_mul_inv, ← Real.exp_neg, mul_assoc]
    ring_nf
  have hev := (tendsto_order.mp hlim).2 1 zero_lt_one
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  set s₀ : ℕ := max N (max (2 * d) 1)
  refine ⟨s₀, le_trans (le_max_left _ _) (le_max_right _ _), fun s hs => ?_⟩
  have hs₀ : (2 * s₀) ^ d ≤ 2 ^ s₀ := by
    have hlt := hN s₀ (le_max_left _ _)
    have hpos : (0 : ℝ) < (2 : ℝ) ^ s₀ := by positivity
    rw [div_lt_one hpos] at hlt
    exact_mod_cast hlt.le
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
  induction k with
  | zero => simpa using hs₀
  | succ k ih =>
    have ih' := ih (Nat.le_add_right s₀ k)
    set t : ℕ := s₀ + k
    have ht : 2 * d ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (Nat.le_add_right s₀ k)
    have ht1 : 1 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (Nat.le_add_right s₀ k)
    have hstep : (2 * (t + 1)) ^ d ≤ 2 * (2 * t) ^ d := by
      have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht1
      have hrat : ((2 * ((t + 1 : ℕ) : ℝ)) / (2 * (t : ℝ))) ^ d ≤ (2 : ℝ) := by
        have h1 : (2 * ((t + 1 : ℕ) : ℝ)) / (2 * (t : ℝ)) = 1 + 1 / (t : ℝ) := by
          push_cast; field_simp
        rw [h1]
        have hexp : 1 + 1 / (t : ℝ) ≤ Real.exp (1 / (t : ℝ)) := by
          linarith [Real.add_one_le_exp (1 / (t : ℝ))]
        have hpow : (1 + 1 / (t : ℝ)) ^ d ≤ (Real.exp (1 / (t : ℝ))) ^ d :=
          pow_le_pow_left₀ (by positivity) hexp d
        rw [← Real.exp_nat_mul] at hpow
        have hd_le : (d : ℝ) * (1 / (t : ℝ)) ≤ (1 / 2 : ℝ) := by
          rw [mul_one_div, div_le_iff₀ htR]
          have : (2 * d : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
          linarith
        have hexp2 : Real.exp ((d : ℝ) * (1 / (t : ℝ))) ≤ Real.exp (1 / 2 : ℝ) :=
          Real.exp_le_exp.mpr hd_le
        have hexp_half : Real.exp (1 / 2 : ℝ) ≤ 2 := by
          have hsq : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
            rw [← Real.exp_nat_mul]; norm_num
          have he3 : Real.exp 1 ≤ 4 := le_trans Real.exp_one_lt_d9.le (by norm_num)
          nlinarith [Real.exp_pos (1 / 2 : ℝ)]
        exact le_trans hpow (le_trans hexp2 hexp_half)
      have hden : (0 : ℝ) < (2 * (t : ℝ)) ^ d := by positivity
      rw [div_pow, div_le_iff₀ hden] at hrat
      exact_mod_cast hrat
    calc (2 * (s₀ + (k + 1))) ^ d
        = (2 * (t + 1)) ^ d := by rw [show s₀ + (k + 1) = t + 1 by dsimp only [t]; omega]
      _ ≤ 2 * (2 * t) ^ d := hstep
      _ ≤ 2 * 2 ^ t := Nat.mul_le_mul_left 2 ih'
      _ = 2 ^ (s₀ + (k + 1)) := by rw [← add_assoc, pow_succ']

noncomputable def bf_C_poly_of (n s_ratio : ℕ) : ℕ :=
  max (8 * 2 ^ n * (2 * n * s_ratio + 1) ^ n)
      (200000 * n * (2 * n * s_ratio + 1) ^ n) + 100
noncomputable def bf_L_p (u : ℕ) : ℕ := 2 ^ u
noncomputable def bf_K_p (n u : ℕ) : ℕ := 2 * n * u
noncomputable def bf_S_p (s_ratio u : ℕ) : ℕ := s_ratio * bf_L_p u
noncomputable def bf_T₀_p (n s_ratio u : ℕ) : ℕ := bf_K_p n u * bf_S_p s_ratio u
noncomputable def bf_c_h_p (n u : ℕ) : ℕ := 32 * bf_K_p n u
noncomputable def bf_c₀_p (n s_ratio u : ℕ) : ℕ :=
  4 * bf_c_h_p n u * (bf_K_p n u * s_ratio + 1) ^ n
noncomputable def bf_M₀_p (n s_ratio u : ℕ) (α : ℝ) : ℝ :=
  7.5 * (bf_T₀_p n s_ratio u : ℝ) +
    ((bf_c₀_p n s_ratio u : ℝ) + 1) * Real.log (Real.exp 1 * ((bf_c_h_p n u : ℝ) + 2)) +
    α * (bf_L_p u : ℝ) * (bf_c_h_p n u : ℝ)
noncomputable def bf_C_tot_p (n s_ratio u : ℕ) (α : ℝ) : ℝ :=
  bf_M₀_p n s_ratio u α + 10 * (bf_T₀_p n s_ratio u : ℝ) +
    2 * ((bf_c₀_p n s_ratio u : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ bf_K_p n u * (bf_c_h_p n u : ℝ) + 2)) +
    α * (bf_L_p u : ℝ) * (2 : ℝ) ^ bf_K_p n u * (bf_c_h_p n u : ℝ) +
    3 * (2 : ℝ) ^ bf_K_p n u * (bf_c_h_p n u : ℝ) * (bf_S_p s_ratio u : ℝ) + 20
noncomputable def bf_A1_p (u : ℕ) : ℝ :=
  Real.log (2 * (bf_L_p u : ℝ) + 1) + 1
noncomputable def bf_A2_p (n s_ratio u : ℕ) : ℝ :=
  Real.log (20 * ((bf_c₀_p n s_ratio u : ℝ) + 1) ^ 2 * ((bf_L_p u : ℝ) + 1) ^ (2 * n))
noncomputable def bf_A3_p (n s_ratio u : ℕ) (α : ℝ) : ℝ :=
  Real.log (32 * (2 : ℝ) ^ bf_K_p n u * (bf_c_h_p n u : ℝ) * (bf_S_p s_ratio u : ℝ) *
    ((2 * ((2 : ℝ) ^ bf_K_p n u * (bf_c_h_p n u : ℝ)) ^ 2) ^ bf_S_p s_ratio u) *
    (((bf_T₀_p n s_ratio u : ℝ) + α + 1) ^ bf_S_p s_ratio u) *
    (2 * (2 : ℝ) ^ bf_K_p n u * (bf_c_h_p n u : ℝ) * (bf_L_p u : ℝ)))
noncomputable def bf_k₀_p (n s_ratio u : ℕ) (α : ℝ) : ℕ :=
  max 10 (max ((4 * (2 * bf_S_p s_ratio u + 4) + 1) ^ 2)
    (Nat.ceil (2 * max 0 (bf_A1_p u) + 2 * max 0 (bf_A2_p n s_ratio u) + 2 * max 0 (bf_A3_p n s_ratio u α) + 10)))
noncomputable def bf_C_p (n s_ratio u : ℕ) (α : ℝ) : ℝ := bf_C_tot_p n s_ratio u α + 2
noncomputable def bf_B₀_p (n s_ratio u : ℕ) (α : ℝ) : ℝ := max 2 (Real.exp ((bf_k₀_p n s_ratio u α : ℝ) + 1))

noncomputable def bf_s_ratio (α : ℝ) : ℕ := Nat.ceil (128 * α) + 1
noncomputable def bf_C_poly (n : ℕ) (α : ℝ) : ℕ :=
  max (8 * 2 ^ n * (2 * n * bf_s_ratio α + 1) ^ n)
      (200000 * n * (2 * n * bf_s_ratio α + 1) ^ n) + 100
noncomputable def bf_u (s₀ n : ℕ) (α : ℝ) : ℕ :=
  2 * (s₀ + Nat.log 2 (bf_C_poly n α) + 1)
noncomputable def bf_L (s₀ n : ℕ) (α : ℝ) : ℕ := 2 ^ bf_u s₀ n α
noncomputable def bf_K (s₀ n : ℕ) (α : ℝ) : ℕ := 2 * n * bf_u s₀ n α
noncomputable def bf_S (s₀ n : ℕ) (α : ℝ) : ℕ := bf_s_ratio α * bf_L s₀ n α
noncomputable def bf_T₀ (s₀ n : ℕ) (α : ℝ) : ℕ := bf_K s₀ n α * bf_S s₀ n α
noncomputable def bf_c_h (s₀ n : ℕ) (α : ℝ) : ℕ := 32 * bf_K s₀ n α
noncomputable def bf_c₀ (s₀ n : ℕ) (α : ℝ) : ℕ :=
  4 * bf_c_h s₀ n α * (bf_K s₀ n α * bf_s_ratio α + 1) ^ n
noncomputable def bf_M₀ (s₀ n : ℕ) (α : ℝ) : ℝ :=
  7.5 * (bf_T₀ s₀ n α : ℝ) +
    ((bf_c₀ s₀ n α : ℝ) + 1) * Real.log (Real.exp 1 * ((bf_c_h s₀ n α : ℝ) + 2)) +
    α * (bf_L s₀ n α : ℝ) * (bf_c_h s₀ n α : ℝ)
noncomputable def bf_C_tot (s₀ n : ℕ) (α : ℝ) : ℝ :=
  bf_M₀ s₀ n α + 10 * (bf_T₀ s₀ n α : ℝ) +
    2 * ((bf_c₀ s₀ n α : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ bf_K s₀ n α * (bf_c_h s₀ n α : ℝ) + 2)) +
    α * (bf_L s₀ n α : ℝ) * (2 : ℝ) ^ bf_K s₀ n α * (bf_c_h s₀ n α : ℝ) +
    3 * (2 : ℝ) ^ bf_K s₀ n α * (bf_c_h s₀ n α : ℝ) * (bf_S s₀ n α : ℝ) + 20
noncomputable def bf_A1 (s₀ n : ℕ) (α : ℝ) : ℝ :=
  Real.log (2 * (bf_L s₀ n α : ℝ) + 1) + 1
noncomputable def bf_A2 (s₀ n : ℕ) (α : ℝ) : ℝ :=
  Real.log (20 * ((bf_c₀ s₀ n α : ℝ) + 1) ^ 2 * ((bf_L s₀ n α : ℝ) + 1) ^ (2 * n))
noncomputable def bf_A3 (s₀ n : ℕ) (α : ℝ) : ℝ :=
  Real.log (32 * (2 : ℝ) ^ bf_K s₀ n α * (bf_c_h s₀ n α : ℝ) * (bf_S s₀ n α : ℝ) *
    ((2 * ((2 : ℝ) ^ bf_K s₀ n α * (bf_c_h s₀ n α : ℝ)) ^ 2) ^ bf_S s₀ n α) *
    (((bf_T₀ s₀ n α : ℝ) + α + 1) ^ bf_S s₀ n α) *
    (2 * (2 : ℝ) ^ bf_K s₀ n α * (bf_c_h s₀ n α : ℝ) * (bf_L s₀ n α : ℝ)))
noncomputable def bf_k₀ (s₀ n : ℕ) (α : ℝ) : ℕ :=
  max 10 (max ((4 * (2 * bf_S s₀ n α + 4) + 1) ^ 2)
    (Nat.ceil (2 * max 0 (bf_A1 s₀ n α) + 2 * max 0 (bf_A2 s₀ n α) + 2 * max 0 (bf_A3 s₀ n α) + 10)))
noncomputable def bf_C (s₀ n : ℕ) (α : ℝ) : ℝ := bf_C_tot s₀ n α + 2
noncomputable def bf_B₀ (s₀ n : ℕ) (α : ℝ) : ℝ := max 2 (Real.exp ((bf_k₀ s₀ n α : ℝ) + 1))

set_option maxHeartbeats 400000 in
private theorem baker_feldman_core_of_params {m : ℕ} (hm : 1 ≤ m)
    (p : Fin (m + 1) → ℕ) (hp_pr : ∀ i, (p i).Prime) (hp_inj : Function.Injective p)
    (α : ℝ) (hα_ge1 : 1 ≤ α) (hα_sum : ∑ i : Fin (m + 1), Real.log (p i : ℝ) ≤ α)
    (s_ratio u : ℕ) (hs_ratio_pos : 1 ≤ s_ratio) (hs_ratio_ge : 128 * α ≤ (s_ratio : ℝ))
    (hu1 : 1 ≤ u) (hu_dom : bf_C_poly_of (m + 1) s_ratio * u ^ (m + 2) ≤ 2 ^ u) :
    0 < bf_C_p (m + 1) s_ratio u α ∧ 2 ≤ bf_B₀_p (m + 1) s_ratio u α ∧
      ∀ b : Fin (m + 1) → ℤ,
        bf_B₀_p (m + 1) s_ratio u α ≤ (b (Fin.last m) : ℝ) →
        (∀ i, |b i| ≤ b (Fin.last m)) →
        ((b (Fin.last m) : ℝ)) ^ (-(bf_C_p (m + 1) s_ratio u α)) ≤
          |∑ i : Fin (m + 1), (b i : ℝ) * Real.log (p i : ℝ)| := by
  classical
  let n : ℕ := m + 1
  have hn2 : 2 ≤ n := by dsimp only [n]; omega
  have hαm_le : ∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ) ≤ α := by
    have hsplit : ∑ i : Fin (m + 1), Real.log (p i : ℝ) =
        (∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ)) + Real.log (p (Fin.last m) : ℝ) :=
      Fin.sum_univ_castSucc _
    have hlast : 0 ≤ Real.log (p (Fin.last m) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (hp_pr (Fin.last m)).one_lt.le)
    linarith
  set C_poly : ℕ := bf_C_poly_of n s_ratio
  have hu_dom' : C_poly * u ^ (n + 1) ≤ 2 ^ u := hu_dom
  set L : ℕ := 2 ^ u
  have hL_eq : L = bf_L_p u := rfl
  have hL1 : 1 ≤ L := Nat.one_le_pow u 2 (by norm_num)
  set K : ℕ := 2 * n * u
  have hK_eq : K = bf_K_p n u := rfl
  have hn1 : 1 ≤ n := by dsimp only [n]; omega
  have hK1 : 1 ≤ K := Nat.mul_pos (Nat.mul_pos (by norm_num) hn1) hu1
  set S : ℕ := s_ratio * L
  have hS_eq : S = bf_S_p s_ratio u := rfl
  have hS1 : 1 ≤ S := Nat.mul_pos hs_ratio_pos hL1
  set T₀ : ℕ := K * S
  have hT₀_eq : T₀ = bf_T₀_p n s_ratio u := rfl
  have hT₀1 : 1 ≤ T₀ := Nat.mul_pos hK1 hS1
  set c_h : ℕ := 32 * K
  have hc_h_eq : c_h = bf_c_h_p n u := rfl
  have hc_h1 : 1 ≤ c_h := Nat.mul_pos (by norm_num) hK1
  set c₀ : ℕ := 4 * c_h * (K * s_ratio + 1) ^ n
  have hc₀_eq : c₀ = bf_c₀_p n s_ratio u := rfl
  have hc₀1 : 1 ≤ c₀ := by
    dsimp only [c₀]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) hc_h1) (pow_pos (Nat.succ_pos _) _)
  -- Verify key parameter inequalities from `hu_dom`
  have hK_dom : 8 * (K * s_ratio + 1) ^ n * (L + 1) ^ n ≤ 2 ^ K := by
    have hL_le : L + 1 ≤ 2 * 2 ^ u := by dsimp only [L]; omega
    have hKsr : K * s_ratio + 1 ≤ (2 * n * s_ratio + 1) * u := by
      dsimp only [K]
      rw [show 2 * n * u * s_ratio + 1 = 2 * n * s_ratio * u + 1 by ring,
        show (2 * n * s_ratio + 1) * u = 2 * n * s_ratio * u + u by ring]
      exact Nat.add_le_add_left hu1 _
    have hu_n : u ^ n ≤ u ^ (n + 1) := Nat.pow_le_pow_right hu1 (Nat.le_succ n)
    have h1 : 8 * 2 ^ n * (2 * n * s_ratio + 1) ^ n * u ^ n ≤ 2 ^ u := by
      calc 8 * 2 ^ n * (2 * n * s_ratio + 1) ^ n * u ^ n
          ≤ C_poly * u ^ (n + 1) := by
            apply Nat.mul_le_mul _ hu_n
            dsimp only [C_poly, bf_C_poly_of]
            exact le_trans (le_max_left _ _) (Nat.le_add_right _ 100)
        _ ≤ 2 ^ u := hu_dom'
    have h2 : (2 ^ u) * (2 ^ (n * u)) ≤ 2 ^ K := by
      rw [← pow_add]
      apply Nat.pow_le_pow_right (by norm_num)
      dsimp only [K]
      rw [show u + n * u = (n + 1) * u by ring]
      exact Nat.mul_le_mul_right u (by omega)
    have hpow_un : ((2 : ℕ) ^ u) ^ n = 2 ^ (n * u) := by rw [← pow_mul, mul_comm u n]
    calc 8 * (K * s_ratio + 1) ^ n * (L + 1) ^ n
        ≤ 8 * ((2 * n * s_ratio + 1) * u) ^ n * (2 * 2 ^ u) ^ n := by
          apply Nat.mul_le_mul (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hKsr n))
            (Nat.pow_le_pow_left hL_le n)
      _ = (8 * 2 ^ n * (2 * n * s_ratio + 1) ^ n * u ^ n) * 2 ^ (n * u) := by
          rw [mul_pow (2 * n * s_ratio + 1) u n, mul_pow 2 (2 ^ u) n, hpow_un]; ring
      _ ≤ 2 ^ u * 2 ^ (n * u) := Nat.mul_le_mul_right _ h1
      _ ≤ 2 ^ K := h2
  have hpoly_S_dom :
      2 * ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) + 10 * (c_h : ℝ) ≤
        (0.8 : ℝ) * (c_h : ℝ) * (S : ℝ) := by
    have h2K1 : (1 : ℝ) ≤ (2 : ℝ) ^ K := one_le_pow₀ (by norm_num)
    have hch1 : (1 : ℝ) ≤ (c_h : ℝ) := by exact_mod_cast hc_h1
    have hprod2Kc : (1 : ℝ) ≤ (2 : ℝ) ^ K * (c_h : ℝ) := one_le_mul_of_one_le_of_one_le h2K1 hch1
    have h32pos : (0 : ℝ) < 32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2 := by linarith only [hprod2Kc]
    have harg_pos : 0 < Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2) :=
      mul_pos (Real.exp_pos 1) h32pos
    have hlog_bnd : Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) ≤ 14000 * (n : ℝ) * (u : ℝ) := by
      have harg_le : Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2) ≤
          (192 * (c_h : ℝ)) * (2 : ℝ) ^ K := by
        have he3 : Real.exp 1 ≤ 3 := le_trans Real.exp_one_lt_d9.le (by norm_num)
        have h1 : 32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2 ≤ 64 * (c_h : ℝ) * (2 : ℝ) ^ K := by
          linarith only [hprod2Kc]
        calc Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)
            ≤ 3 * (64 * (c_h : ℝ) * (2 : ℝ) ^ K) := mul_le_mul he3 h1 h32pos.le (by norm_num)
          _ = (192 * (c_h : ℝ)) * (2 : ℝ) ^ K := by ring
      have h192ne : (192 * (c_h : ℝ)) ≠ 0 := by linarith only [hch1]
      have h2Kne : ((2 : ℝ) ^ K) ≠ 0 := pow_ne_zero K (by norm_num)
      calc Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2))
          ≤ Real.log ((192 * (c_h : ℝ)) * (2 : ℝ) ^ K) := Real.log_le_log harg_pos harg_le
        _ = Real.log (192 * (c_h : ℝ)) + (K : ℝ) * Real.log 2 := by
            rw [Real.log_mul h192ne h2Kne, Real.log_pow]
        _ ≤ 192 * (c_h : ℝ) + (K : ℝ) * 1 := by
            have h1 := real_log_le_self_of_pos (by linarith only [hch1] : (0 : ℝ) < 192 * (c_h : ℝ))
            have h2 : Real.log 2 ≤ 1 := le_trans Real.log_two_lt_d9.le (by norm_num)
            have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
            have hKm := mul_le_mul_of_nonneg_left h2 hK0
            linarith only [h1, hKm]
        _ ≤ 14000 * (n : ℝ) * (u : ℝ) := by
            have hch_eq : (c_h : ℝ) = 64 * (n : ℝ) * (u : ℝ) := by
              dsimp only [c_h, K]; push_cast; ring
            have hK_eq : (K : ℝ) = 2 * (n : ℝ) * (u : ℝ) := by
              dsimp only [K]; push_cast; ring
            rw [hch_eq, hK_eq]
            have hnu : (0 : ℝ) ≤ (n : ℝ) * (u : ℝ) := mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg u)
            linarith only [hnu]
    have hc0_le : ((c₀ : ℝ) + 1) ≤ 5 * (c_h : ℝ) * ((2 * (n : ℝ) * (s_ratio : ℝ) + 1) * (u : ℝ)) ^ n := by
      have hu1R : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu1
      have h2ns : (0 : ℝ) ≤ 2 * (n : ℝ) * (s_ratio : ℝ) :=
        mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) (Nat.cast_nonneg s_ratio)
      have hKsr : (K : ℝ) * (s_ratio : ℝ) + 1 ≤ (2 * (n : ℝ) * (s_ratio : ℝ) + 1) * (u : ℝ) := by
        have hKeq : (K : ℝ) = 2 * (n : ℝ) * (u : ℝ) := by dsimp only [K]; push_cast; ring
        rw [hKeq]; nlinarith only [hu1R, h2ns]
      have hKs0 : 0 ≤ (K : ℝ) * (s_ratio : ℝ) + 1 := by
        have h1 : (0 : ℝ) ≤ (K : ℝ) * (s_ratio : ℝ) := mul_nonneg (Nat.cast_nonneg K) (Nat.cast_nonneg s_ratio)
        linarith only [h1]
      have hpow : ((K : ℝ) * (s_ratio : ℝ) + 1) ^ n ≤
          ((2 * (n : ℝ) * (s_ratio : ℝ) + 1) * (u : ℝ)) ^ n :=
        pow_le_pow_left₀ hKs0 hKsr n
      have hc0_eq : (c₀ : ℝ) = 4 * (c_h : ℝ) * ((K : ℝ) * (s_ratio : ℝ) + 1) ^ n := by
        dsimp only [c₀]; push_cast; rfl
      have hpow1 : (1 : ℝ) ≤ ((2 * (n : ℝ) * (s_ratio : ℝ) + 1) * (u : ℝ)) ^ n := by
        apply one_le_pow₀
        nlinarith only [hu1R, h2ns]
      have hchpow : (1 : ℝ) ≤ (c_h : ℝ) * ((2 * (n : ℝ) * (s_ratio : ℝ) + 1) * (u : ℝ)) ^ n :=
        one_le_mul_of_one_le_of_one_le hch1 hpow1
      have h4ch : 4 * (c_h : ℝ) * ((K : ℝ) * (s_ratio : ℝ) + 1) ^ n ≤
          4 * (c_h : ℝ) * ((2 * (n : ℝ) * (s_ratio : ℝ) + 1) * (u : ℝ)) ^ n :=
        mul_le_mul_of_nonneg_left hpow (by linarith only [hch1])
      rw [hc0_eq]; linarith only [h4ch, hchpow]
    have hlog_pos : 0 ≤ Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) := by
      apply Real.log_nonneg
      have he1 : (1 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith only [this]
      have h32 : (1 : ℝ) ≤ 32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2 := by linarith only [hprod2Kc]
      exact one_le_mul_of_one_le_of_one_le he1 h32
    have hu_domR : (C_poly : ℝ) * (u : ℝ) ^ (n + 1) ≤ (L : ℝ) := by
      have : (C_poly * u ^ (n + 1) : ℕ) ≤ 2 ^ u := hu_dom'
      dsimp only [L]
      exact_mod_cast this
    have hCpoly_ge : (200000 * (n : ℝ) * (2 * (n : ℝ) * (s_ratio : ℝ) + 1) ^ n + 100 : ℝ) ≤ (C_poly : ℝ) := by
      have hnat : 200000 * n * (2 * n * s_ratio + 1) ^ n + 100 ≤ C_poly := by
        dsimp only [C_poly, bf_C_poly_of]
        exact Nat.add_le_add_right (le_max_right _ _) 100
      exact_mod_cast hnat
    have hu1R : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu1
    have hch1R : (0 : ℝ) ≤ (c_h : ℝ) := Nat.cast_nonneg _
    have hs1R : (1 : ℝ) ≤ (s_ratio : ℝ) := by exact_mod_cast hs_ratio_pos
    have hS_eq' : (S : ℝ) = (s_ratio : ℝ) * (L : ℝ) := by dsimp only [S]; push_cast; rfl
    have hprod_bound :
        2 * (5 * (c_h : ℝ) * ((2 * (n : ℝ) * (s_ratio : ℝ) + 1) * (u : ℝ)) ^ n) *
          (14000 * (n : ℝ) * (u : ℝ)) + 10 * (c_h : ℝ) ≤
        (0.8 : ℝ) * (c_h : ℝ) * (S : ℝ) := by
      rw [mul_pow, hS_eq']
      have h1 : 140000 * (n : ℝ) * (2 * (n : ℝ) * (s_ratio : ℝ) + 1) ^ n * (u : ℝ) ^ (n + 1) + 10 ≤
          (0.8 : ℝ) * (C_poly : ℝ) * (u : ℝ) ^ (n + 1) := by
        have hup : (1 : ℝ) ≤ (u : ℝ) ^ (n + 1) := one_le_pow₀ hu1R
        have h2ns0 : (0 : ℝ) ≤ 2 * (n : ℝ) * (s_ratio : ℝ) + 1 := by
          have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg n)) (Nat.cast_nonneg s_ratio)
          linarith only [this]
        have hpos_t : 0 ≤ (n : ℝ) * (2 * (n : ℝ) * (s_ratio : ℝ) + 1) ^ n * (u : ℝ) ^ (n + 1) :=
          mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg h2ns0 n)) (by linarith only [hup])
        nlinarith only [hCpoly_ge, hup, hpos_t]
      have h2 : (0.8 : ℝ) * (C_poly : ℝ) * (u : ℝ) ^ (n + 1) ≤ (0.8 : ℝ) * (s_ratio : ℝ) * (L : ℝ) := by
        have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
        nlinarith only [hu_domR, hs1R, hL0]
      calc 2 * (5 * (c_h : ℝ) * ((2 * (n : ℝ) * (s_ratio : ℝ) + 1) ^ n * (u : ℝ) ^ n)) *
              (14000 * (n : ℝ) * (u : ℝ)) + 10 * (c_h : ℝ)
          = (c_h : ℝ) * (140000 * (n : ℝ) * (2 * (n : ℝ) * (s_ratio : ℝ) + 1) ^ n *
              (u : ℝ) ^ (n + 1) + 10) := by rw [pow_succ]; ring
        _ ≤ (c_h : ℝ) * ((0.8 : ℝ) * (s_ratio : ℝ) * (L : ℝ)) :=
            mul_le_mul_of_nonneg_left (le_trans h1 h2) hch1R
        _ = (0.8 : ℝ) * (c_h : ℝ) * ((s_ratio : ℝ) * (L : ℝ)) := by ring
    have hmul_le : 2 * ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) ≤
        2 * (5 * (c_h : ℝ) * ((2 * (n : ℝ) * (s_ratio : ℝ) + 1) * (u : ℝ)) ^ n) *
          (14000 * (n : ℝ) * (u : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_left hc0_le (by norm_num : (0 : ℝ) ≤ 2)
      have h2ns0 : (0 : ℝ) ≤ 2 * (n : ℝ) * (s_ratio : ℝ) + 1 := by
        have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg n)) (Nat.cast_nonneg s_ratio)
        linarith only [this]
      have hnn : 0 ≤ 2 * (5 * (c_h : ℝ) * ((2 * (n : ℝ) * (s_ratio : ℝ) + 1) * (u : ℝ)) ^ n) :=
        mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) hch1R)
          (pow_nonneg (mul_nonneg h2ns0 (by linarith only [hu1R])) n))
      exact mul_le_mul h1 hlog_bnd hlog_pos hnn
    linarith only [hmul_le, hprod_bound]
  set M₀ : ℝ :=
    7.5 * (T₀ : ℝ) + ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * ((c_h : ℝ) + 2)) + α * (L : ℝ) * (c_h : ℝ)
  have hM₀_eq : M₀ = bf_M₀_p n s_ratio u α := rfl
  have hM₀_nn : 0 ≤ M₀ := by
    have hlog0 : 0 ≤ Real.log (Real.exp 1 * ((c_h : ℝ) + 2)) := by
      apply Real.log_nonneg
      have he1 : (1 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith only [this]
      have hch0 : (0 : ℝ) ≤ (c_h : ℝ) := Nat.cast_nonneg c_h
      nlinarith only [he1, hch0]
    positivity
  set C_tot : ℝ :=
    M₀ + 10 * (T₀ : ℝ) + 2 * ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) +
      α * (L : ℝ) * (2 : ℝ) ^ K * (c_h : ℝ) + 3 * (2 : ℝ) ^ K * (c_h : ℝ) * (S : ℝ) + 20
  have hC_tot_eq : C_tot = bf_C_tot_p n s_ratio u α := rfl
  have hCtot_pos : 0 < C_tot := by
    have hlog0 : 0 ≤ Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) := by
      apply Real.log_nonneg
      have he1 : (1 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith only [this]
      have h2K1 : (1 : ℝ) ≤ (2 : ℝ) ^ K := one_le_pow₀ (by norm_num)
      have hch1 : (1 : ℝ) ≤ (c_h : ℝ) := by exact_mod_cast hc_h1
      have h32 : (1 : ℝ) ≤ 32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2 := by nlinarith only [h2K1, hch1]
      nlinarith only [he1, h32]
    positivity
  set k₀ : ℕ := bf_k₀_p n s_ratio u α
  have hk₀10 : 10 ≤ k₀ := by dsimp only [k₀, bf_k₀_p]; exact le_max_left _ _
  have hk₀_prop : ∀ k : ℕ, k₀ ≤ k →
      (Real.log (2 * (L : ℝ) + 1) + 1 ≤ (0.5 : ℝ) * (k : ℝ)) ∧
      (Real.log (20 * ((c₀ : ℝ) * (k : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n)) ≤ (k : ℝ)) ∧
      ((T₀ : ℝ) * Real.log (2 * (L : ℝ) + 1) ≤ (0.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) ∧
      (Real.log (32 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (S : ℝ) *
        ((2 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2) ^ S) *
        (((T₀ : ℝ) + α + 1) ^ S) * (2 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ))) ≤ 2 * (k : ℝ)) := by
    intro k hk
    set A1 : ℝ := bf_A1_p u
    set A2 : ℝ := bf_A2_p n s_ratio u
    set A3 : ℝ := bf_A3_p n s_ratio u α
    set D_deg : ℕ := 2 * S + 4
    set N₁ : ℕ := (4 * D_deg + 1) ^ 2
    have hk10 : 10 ≤ k := le_trans hk₀10 hk
    have hkN₁ : N₁ ≤ k := by
      have h1 : N₁ ≤ k₀ := by dsimp only [k₀, bf_k₀_p, N₁, D_deg, bf_S_p]; exact le_trans (le_max_left _ _) (le_max_right _ _)
      exact le_trans h1 hk
    have hkA : 2 * max 0 A1 + 2 * max 0 A2 + 2 * max 0 A3 + 10 ≤ (k : ℝ) := by
      have h1 : Nat.ceil (2 * max 0 A1 + 2 * max 0 A2 + 2 * max 0 A3 + 10) ≤ k₀ := by
        dsimp only [k₀, bf_k₀_p, A1, A2, A3]
        exact le_trans (le_max_right _ _) (le_max_right _ _)
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans h1 hk)
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hlogk : (D_deg : ℝ) * Real.log (k : ℝ) ≤ (0.5 : ℝ) * (k : ℝ) := by
      have hsq : 4 * (D_deg : ℝ) ≤ Real.sqrt (k : ℝ) := by
        have h1 : ((4 * D_deg + 1 : ℕ) : ℝ) ^ 2 ≤ (k : ℝ) := by
          have : (4 * D_deg + 1) ^ 2 ≤ k := hkN₁
          exact_mod_cast this
        have h2 : ((4 * D_deg + 1 : ℕ) : ℝ) ≤ Real.sqrt (k : ℝ) := by
          rw [← Real.sqrt_sq (Nat.cast_nonneg _)]
          exact Real.sqrt_le_sqrt h1
        push_cast at h2; linarith
      have hlog_sq := real_log_le_two_sqrt hk_pos
      have hsqrt_sq : Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) = (k : ℝ) := Real.mul_self_sqrt hk_pos.le
      have hsqrt_nn : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
      have hDnn : (0 : ℝ) ≤ (D_deg : ℝ) := Nat.cast_nonneg D_deg
      nlinarith only [hsq, hlog_sq, hsqrt_sq, hsqrt_nn, hDnn]
    have hA1 : A1 ≤ (0.5 : ℝ) * (k : ℝ) := by
      have h1 := le_max_right (0 : ℝ) A1
      have h2 := le_max_left (0 : ℝ) A2
      have h3 := le_max_left (0 : ℝ) A3
      linarith only [hkA, h1, h2, h3]
    have hA2 : A2 ≤ (0.5 : ℝ) * (k : ℝ) := by
      have h1 := le_max_left (0 : ℝ) A1
      have h2 := le_max_right (0 : ℝ) A2
      have h3 := le_max_left (0 : ℝ) A3
      linarith only [hkA, h1, h2, h3]
    have hA3 : A3 ≤ (0.5 : ℝ) * (k : ℝ) := by
      have h1 := le_max_left (0 : ℝ) A1
      have h2 := le_max_left (0 : ℝ) A2
      have h3 := le_max_right (0 : ℝ) A3
      linarith only [hkA, h1, h2, h3]
    have hlogk_nn : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
    have hA1' : Real.log (2 * (L : ℝ) + 1) + 1 ≤ (0.5 : ℝ) * (k : ℝ) := hA1
    refine ⟨hA1', ?_, ?_, ?_⟩
    · have hle : 20 * ((c₀ : ℝ) * (k : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n) ≤
          (20 * ((c₀ : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n)) * (k : ℝ) ^ 2 := by
        have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
        have h1 : (c₀ : ℝ) * (k : ℝ) + 1 ≤ ((c₀ : ℝ) + 1) * (k : ℝ) := by
          have : (0 : ℝ) ≤ (c₀ : ℝ) := Nat.cast_nonneg c₀
          nlinarith only [hk1, this]
        have h2 := pow_le_pow_left₀ (by positivity) h1 2
        rw [mul_pow] at h2
        have h3 : 0 ≤ 20 * ((L : ℝ) + 1) ^ (2 * n) := by positivity
        nlinarith only [h2, h3]
      calc Real.log (20 * ((c₀ : ℝ) * (k : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n))
          ≤ Real.log ((20 * ((c₀ : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n)) * (k : ℝ) ^ 2) :=
            Real.log_le_log (by positivity) hle
        _ = A2 + 2 * Real.log (k : ℝ) := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
            dsimp only [A2, bf_A2_p]; push_cast; rfl
        _ ≤ (0.5 : ℝ) * (k : ℝ) + (D_deg : ℝ) * Real.log (k : ℝ) := by
            have h2D : (2 : ℝ) ≤ (D_deg : ℝ) := by dsimp only [D_deg]; exact_mod_cast (by omega : 2 ≤ 2 * S + 4)
            nlinarith only [hA2, h2D, hlogk_nn]
        _ ≤ (k : ℝ) := by linarith only [hlogk]
    · rw [show (0.5 : ℝ) * (T₀ : ℝ) * (k : ℝ) = (T₀ : ℝ) * ((0.5 : ℝ) * (k : ℝ)) by ring]
      exact mul_le_mul_of_nonneg_left (by linarith only [hA1']) (Nat.cast_nonneg T₀)
    · have hfact :
          32 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (S : ℝ) *
            ((2 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2) ^ S) *
            (((T₀ : ℝ) + α + 1) ^ S) * (2 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ)) =
          (32 * (2 : ℝ) ^ K * (c_h : ℝ) * (S : ℝ) *
            ((2 * ((2 : ℝ) ^ K * (c_h : ℝ)) ^ 2) ^ S) *
            (((T₀ : ℝ) + α + 1) ^ S) * (2 * (2 : ℝ) ^ K * (c_h : ℝ) * (L : ℝ))) *
            (k : ℝ) ^ (2 * S + 2) := by
        have h1 : (2 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2) ^ S =
            (2 * ((2 : ℝ) ^ K * (c_h : ℝ)) ^ 2) ^ S * (k : ℝ) ^ (2 * S) := by
          rw [mul_pow, mul_pow, mul_pow, mul_pow, ← pow_mul]
          ring
        rw [h1, show 2 * S + 2 = 2 * S + 1 + 1 by omega, pow_succ, pow_succ]
        ring
      rw [hfact, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      have hdeg_le : ((2 * S + 2 : ℕ) : ℝ) ≤ (D_deg : ℝ) := by
        dsimp only [D_deg]; exact_mod_cast (by omega : 2 * S + 2 ≤ 2 * S + 4)
      have hmul := mul_le_mul_of_nonneg_right hdeg_le hlogk_nn
      have hA3_eq : A3 = Real.log (32 * (2 : ℝ) ^ K * (c_h : ℝ) * (S : ℝ) *
            ((2 * ((2 : ℝ) ^ K * (c_h : ℝ)) ^ 2) ^ S) *
            (((T₀ : ℝ) + α + 1) ^ S) * (2 * (2 : ℝ) ^ K * (c_h : ℝ) * (L : ℝ))) := rfl
      rw [← hA3_eq]
      linarith only [hA3, hmul, hlogk]
  have hC_def : bf_C_p (m + 1) s_ratio u α = C_tot + 2 := rfl
  have hB₀_def : bf_B₀_p (m + 1) s_ratio u α = max 2 (Real.exp ((k₀ : ℝ) + 1)) := rfl
  rw [hC_def, hB₀_def]
  refine ⟨by linarith only [hCtot_pos], le_max_left _ _, ?_⟩
  intro b hbn_ge hb_le
  set b_n : ℤ := b (Fin.last m)
  have hbnR_ge2 : (2 : ℝ) ≤ (b_n : ℝ) := le_trans (le_max_left _ _) hbn_ge
  have hbn_pos : 0 < b_n := by
    have : (0 : ℝ) < (b_n : ℝ) := by linarith only [hbnR_ge2]
    exact_mod_cast this
  have hbnR_pos : (0 : ℝ) < (b_n : ℝ) := by exact_mod_cast hbn_pos
  set D : ℝ := Real.log (b_n : ℝ)
  have hD_ge : (k₀ : ℝ) + 1 ≤ D := by
    rw [Real.le_log_iff_exp_le hbnR_pos]
    exact le_trans (le_max_right _ _) hbn_ge
  set k : ℕ := Nat.floor D
  have hk_ge : k₀ ≤ k := by
    have h1 : (k₀ : ℝ) ≤ D := by linarith only [hD_ge]
    exact Nat.le_floor h1
  have hk10 : 10 ≤ k := le_trans hk₀10 hk_ge
  have hk_pos : 0 < k := by omega
  have hkR_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
  have hk_le_D : (k : ℝ) ≤ D := Nat.floor_le (by have := Nat.cast_nonneg (α := ℝ) k₀; linarith only [hD_ge, this])
  have hD_lt_k1 : D < (k : ℝ) + 1 := Nat.lt_floor_add_one D
  have hD_le_15k : D ≤ (1.5 : ℝ) * (k : ℝ) := by
    have : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk10
    linarith only [hD_lt_k1, this]
  obtain ⟨hlog2L, hlogU2, hT0log2L, hlogErr⟩ := hk₀_prop k hk_ge
  set Λ : ℝ := ∑ i : Fin n, (b i : ℝ) * Real.log (p i : ℝ)
  set Λ' : ℝ := Λ / (b_n : ℝ)
  have hΛ'abs : |Λ'| = |Λ| / (b_n : ℝ) := by rw [abs_div, abs_of_pos hbnR_pos]
  -- Proof by contradiction: assume |Λ| < b_n ^ (-(C_tot + 2))
  by_contra hlt_contra
  push Not at hlt_contra
  have hΛ_lt_exp : |Λ| < Real.exp (-(C_tot + 2) * D) := by
    rwa [Real.rpow_def_of_pos hbnR_pos, mul_comm D] at hlt_contra
  have hΛ'_lt : |Λ'| < Real.exp (-(C_tot + 2) * (k : ℝ)) := by
    have h1 : |Λ'| ≤ |Λ| := by
      rw [hΛ'abs]; exact div_le_self (abs_nonneg _) (by linarith only [hbnR_ge2])
    have h2 : Real.exp (-(C_tot + 2) * D) ≤ Real.exp (-(C_tot + 2) * (k : ℝ)) := by
      apply Real.exp_le_exp.mpr; nlinarith only [hCtot_pos, hk_le_D]
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le hΛ_lt_exp h2)
  -- Define `h₀`, `L₀` and construct coefficients `c : Idx L₀ L m → ℤ` via Siegel's Lemma
  set h₀ : ℕ := c_h * k
  have hh₀1 : 1 ≤ h₀ := Nat.mul_pos hc_h1 hk_pos
  set L₀ : ℕ := c₀ * k
  have hL₀1 : 1 ≤ L₀ := Nat.mul_pos hc₀1 hk_pos
  -- Equation index type: `(s_idx : Fin h₀)` representing `s = s_idx.val + 1 ∈ 1..h₀`,
  -- and `t : {t : Fin n → Fin (T₀ + 1) // ∑ i, (t i).val ≤ T₀}`
  let EqIdx := Fin h₀ × {t : Fin n → Fin (T₀ + 1) // ∑ i : Fin n, (t i).val ≤ T₀}
  have hcard_Eq : Fintype.card EqIdx ≤ h₀ * (T₀ + 1) ^ n := by
    dsimp only [EqIdx]
    rw [Fintype.card_prod, Fintype.card_fin]
    apply Nat.mul_le_mul_left h₀
    have hsub := Fintype.card_subtype_le (fun t : Fin n → Fin (T₀ + 1) => ∑ i : Fin n, (t i).val ≤ T₀)
    simpa [Fintype.card_fun, Fintype.card_fin] using hsub
  have hcard_Idx : Fintype.card (Idx L₀ L m) = (L₀ + 1) * (L + 1) ^ n := by
    simp [Idx, Fintype.card_prod, Fintype.card_fin, n]
  have hcard_pos : 0 < Fintype.card (Idx L₀ L m) := by rw [hcard_Idx]; positivity
  have h2card : 2 * Fintype.card EqIdx ≤ Fintype.card (Idx L₀ L m) := by
    have hT0L : T₀ + 1 ≤ (K * s_ratio + 1) * L := by
      have : T₀ = K * s_ratio * L := by dsimp only [T₀, S]; ring
      rw [this, add_mul, one_mul]
      exact Nat.add_le_add_left hL1 _
    have hc0_ge : 2 * c_h * (K * s_ratio + 1) ^ n ≤ c₀ := by
      dsimp only [c₀]
      exact Nat.mul_le_mul_right ((K * s_ratio + 1) ^ n) (Nat.mul_le_mul_right c_h (by norm_num : 2 ≤ 4))
    calc 2 * Fintype.card EqIdx
        ≤ 2 * (h₀ * (T₀ + 1) ^ n) := Nat.mul_le_mul_left 2 hcard_Eq
      _ ≤ 2 * (h₀ * ((K * s_ratio + 1) * L) ^ n) :=
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left h₀ (Nat.pow_le_pow_left hT0L n))
      _ = (2 * c_h * (K * s_ratio + 1) ^ n) * (k * L ^ n) := by
          dsimp only [h₀]; rw [mul_pow]; ring
      _ ≤ c₀ * (k * L ^ n) := Nat.mul_le_mul_right _ hc0_ge
      _ = L₀ * L ^ n := by dsimp only [L₀]; ring
      _ ≤ (L₀ + 1) * (L + 1) ^ n :=
          Nat.mul_le_mul (Nat.le_succ _) (Nat.pow_le_pow_left (Nat.le_succ L) n)
      _ = Fintype.card (Idx L₀ L m) := hcard_Idx.symm
  -- Build integer matrix A : EqIdx → Idx L₀ L m → ℤ
  have hmat_exists : ∀ (eq : EqIdx) (idx : Idx L₀ L m), ∃ z : ℤ,
      (z : ℚ) =
        ((Nat.lcmUpto k : ℚ) ^ (eq.2.1 0).val) *
        ((b_n : ℚ) ^ (∑ r : Fin m, (eq.2.1 (Fin.succ r)).val)) *
        ((Polynomial.hasseDeriv (eq.2.1 0).val (feldmanPoly k idx.1.val)).eval ((eq.1.val + 1 : ℕ) : ℚ) *
          (∏ r : Fin m, (gammaRat b idx r) ^ (eq.2.1 (Fin.succ r)).val) *
          (∏ i : Fin n, ((p i : ℚ) ^ (idx.2 i).val) ^ (eq.1.val + 1))) := by
    intro eq idx
    obtain ⟨zF, hzF⟩ := lcmUpto_pow_mul_hasseDeriv_feldmanPoly_int hk_pos idx.1.val (eq.2.1 0).val (eq.1.val + 1)
    refine ⟨zF * (∏ r : Fin m, (gammaInt b idx r) ^ (eq.2.1 (Fin.succ r)).val) *
        (∏ i : Fin n, ((p i : ℤ) ^ (idx.2 i).val) ^ (eq.1.val + 1)), ?_⟩
    have hpg : ((b_n : ℚ) ^ (∑ r : Fin m, (eq.2.1 (Fin.succ r)).val)) *
        (∏ r : Fin m, (gammaRat b idx r) ^ (eq.2.1 (Fin.succ r)).val) =
        ∏ r : Fin m, ((gammaInt b idx r : ℚ) ^ (eq.2.1 (Fin.succ r)).val) := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro r _
      rw [← mul_pow, bn_mul_gammaRat (ne_of_gt hbn_pos) idx r]
    simp only [Int.cast_mul, Int.cast_prod, Int.cast_pow, Int.cast_natCast]
    rw [hzF, ← hpg]
    ring
  choose Amat hAmat using hmat_exists
  -- Bound |Amat eq idx| ≤ Hmat using `baker_matrix_entry_bound`
  set Hmat : ℕ := Nat.ceil (Real.exp (M₀ * (k : ℝ)))
  have hAmat_bound : ∀ eq idx, (Amat eq idx).natAbs ≤ Hmat := by
    intro eq idx
    have hreal : |(Amat eq idx : ℝ)| ≤ Real.exp (M₀ * (k : ℝ)) := by
      exact baker_matrix_entry_bound hk_pos rfl p hp_pr hbn_pos hb_le hα_sum hlog2L hD_lt_k1
        (show eq.1.val + 1 ≤ c_h * k from eq.1.isLt) eq.2.2 idx (Amat eq idx) (hAmat eq idx)
    have hnatR : ((Amat eq idx).natAbs : ℝ) ≤ (Hmat : ℝ) := by
      rw [← Int.cast_natCast (R := ℝ), Int.natCast_natAbs, Int.cast_abs]
      exact le_trans hreal (Nat.le_ceil _)
    exact_mod_cast hnatR
  -- Apply Siegel's Lemma!
  obtain ⟨c, hc_ne, hc_bound, hc_zero⟩ := siegel_lemma Amat Hmat hAmat_bound hcard_pos h2card
  set Cmax : ℝ := ((2 * Fintype.card (Idx L₀ L m) * Hmat + 1 : ℕ) : ℝ)
  have hCmax_nn : 0 ≤ Cmax := Nat.cast_nonneg _
  have hc_abs : ∀ idx, |(c idx : ℝ)| ≤ Cmax := by
    intro idx
    have hnat : ((c idx).natAbs : ℝ) ≤ Cmax := by
      dsimp only [Cmax]; exact_mod_cast hc_bound idx
    rwa [← Int.cast_natCast (R := ℝ), Int.natCast_natAbs, Int.cast_abs] at hnat
  have hUCmax : (Fintype.card (Idx L₀ L m) : ℝ) * Cmax ≤ Real.exp ((M₀ + 1) * (k : ℝ)) := by
    have hHmat_le : (Hmat : ℝ) ≤ 2 * Real.exp (M₀ * (k : ℝ)) := by
      have h1 : (Hmat : ℝ) < Real.exp (M₀ * (k : ℝ)) + 1 := Nat.ceil_lt_add_one (by positivity)
      have h2 : (1 : ℝ) ≤ Real.exp (M₀ * (k : ℝ)) := Real.one_le_exp (by positivity)
      linarith only [h1, h2]
    have hcardR : (Fintype.card (Idx L₀ L m) : ℝ) = ((c₀ : ℝ) * (k : ℝ) + 1) * ((L : ℝ) + 1) ^ n := by
      rw [hcard_Idx]; dsimp only [L₀]; push_cast; rfl
    have hcard_ge1 : (1 : ℝ) ≤ (Fintype.card (Idx L₀ L m) : ℝ) := by exact_mod_cast hcard_pos
    have hpoly_le : (Fintype.card (Idx L₀ L m) : ℝ) * Cmax ≤
        (20 * ((c₀ : ℝ) * (k : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n)) * Real.exp (M₀ * (k : ℝ)) := by
      have hexp1 : (1 : ℝ) ≤ Real.exp (M₀ * (k : ℝ)) := Real.one_le_exp (by positivity)
      have hC : Cmax ≤ 5 * (Fintype.card (Idx L₀ L m) : ℝ) * Real.exp (M₀ * (k : ℝ)) := by
        dsimp only [Cmax]; push_cast
        have h1 : (1 : ℝ) ≤ (Fintype.card (Idx L₀ L m) : ℝ) * Real.exp (M₀ * (k : ℝ)) :=
          one_le_mul_of_one_le_of_one_le hcard_ge1 hexp1
        have h2 := mul_le_mul_of_nonneg_left hHmat_le (show (0 : ℝ) ≤ 2 * (Fintype.card (Idx L₀ L m) : ℝ) by positivity)
        linarith only [h1, h2]
      have hsq : (Fintype.card (Idx L₀ L m) : ℝ) * (Fintype.card (Idx L₀ L m) : ℝ) =
          ((c₀ : ℝ) * (k : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n) := by
        rw [hcardR, two_mul, pow_add]; ring
      calc (Fintype.card (Idx L₀ L m) : ℝ) * Cmax
          ≤ (Fintype.card (Idx L₀ L m) : ℝ) * (5 * (Fintype.card (Idx L₀ L m) : ℝ) * Real.exp (M₀ * (k : ℝ))) :=
            mul_le_mul_of_nonneg_left hC (by positivity)
        _ = 5 * (((c₀ : ℝ) * (k : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n)) * Real.exp (M₀ * (k : ℝ)) := by
            rw [← hsq]; ring
        _ ≤ 20 * ((c₀ : ℝ) * (k : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n) * Real.exp (M₀ * (k : ℝ)) := by
            have hnn : 0 ≤ ((c₀ : ℝ) * (k : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n) * Real.exp (M₀ * (k : ℝ)) := by
              positivity
            linarith only [hnn]
    have h20 : 20 * ((c₀ : ℝ) * (k : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n) ≤ Real.exp (k : ℝ) := by
      rw [← Real.log_le_iff_le_exp (by positivity)]; exact hlogU2
    calc (Fintype.card (Idx L₀ L m) : ℝ) * Cmax
        ≤ Real.exp (k : ℝ) * Real.exp (M₀ * (k : ℝ)) :=
          le_trans hpoly_le (mul_le_mul_of_nonneg_right h20 (by positivity))
      _ = Real.exp ((M₀ + 1) * (k : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
  -- Base case j = 0: Psi c t s = 0 for all 1 ≤ s ≤ h₀ and ∑ i, t i ≤ T₀
  have hbase : ∀ s ∈ Finset.Icc 1 h₀, ∀ t : Fin n → ℕ, (∑ i, t i) ≤ T₀ →
      Psi k p b c t s = 0 := by
    intro s hs t ht
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
    have hsh : s ≤ h₀ := (Finset.mem_Icc.mp hs).2
    let eq : EqIdx :=
      (⟨s - 1, by omega⟩,
       ⟨fun i => ⟨t i, by
          have := Finset.single_le_sum (f := t) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          omega⟩,
        by simpa using ht⟩)
    have hz : ∑ idx : Idx L₀ L m, Amat eq idx * c idx = 0 := hc_zero eq
    have hq : ((Nat.lcmUpto k : ℚ) ^ (t 0)) * ((b_n : ℚ) ^ (∑ r : Fin m, t (Fin.succ r))) *
        Psi k p b c t s = 0 := by
      unfold Psi
      rw [Finset.mul_sum]
      have hsum_eq : ∑ idx : Idx L₀ L m,
            ((Nat.lcmUpto k : ℚ) ^ (t 0)) * ((b_n : ℚ) ^ (∑ r : Fin m, t (Fin.succ r))) *
            ((c idx : ℚ) *
              (Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).eval (s : ℚ) *
              (∏ r : Fin m, (gammaRat b idx r) ^ (t (Fin.succ r))) *
              (∏ i : Fin n, ((p i : ℚ) ^ (idx.2 i).val) ^ s)) =
          ∑ idx : Idx L₀ L m, (Amat eq idx : ℚ) * (c idx : ℚ) := by
        apply Finset.sum_congr rfl
        intro idx _
        have hA := hAmat eq idx
        have hs_eq : eq.1.val + 1 = s := by dsimp only [eq]; omega
        have ht_eq : ∀ i, (eq.2.1 i).val = t i := fun _ => rfl
        simp only [hs_eq, ht_eq] at hA
        rw [hA]; ring
      rw [hsum_eq]
      have hzQ : (∑ idx : Idx L₀ L m, (Amat eq idx : ℚ) * (c idx : ℚ)) =
          ((∑ idx : Idx L₀ L m, Amat eq idx * c idx : ℤ) : ℚ) := by push_cast; rfl
      rw [hzQ, hz, Int.cast_zero]
    have hdenQ : ((Nat.lcmUpto k : ℚ) ^ (t 0)) * ((b_n : ℚ) ^ (∑ r : Fin m, t (Fin.succ r))) ≠ 0 := by
      have h1 : (Nat.lcmUpto k : ℚ) ≠ 0 := by exact_mod_cast (Nat.lcmUpto_pos k).ne'
      have h2 : (b_n : ℚ) ≠ 0 := by exact_mod_cast hbn_pos.ne'
      positivity
    exact (mul_eq_zero.mp hq).resolve_left hdenQ
  -- Extrapolation induction over j = 0..K using `baker_extrap_step`!
  have h65α : 65 * α * (L : ℝ) ≤ (0.55 : ℝ) * (S : ℝ) := by
    have hS_eq : (S : ℝ) = (s_ratio : ℝ) * (L : ℝ) := by dsimp only [S]; push_cast; rfl
    rw [hS_eq]
    have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    nlinarith only [hs_ratio_ge, hL0, hα_ge1]
  have hextrap : ∀ j : ℕ, j ≤ K →
      ∀ s ∈ Finset.Icc 1 (2 ^ j * h₀), ∀ t : Fin n → ℕ, (∑ i, t i) ≤ (K - j) * S →
      Psi k p b c t s = 0 := by
    intro j
    induction j with
    | zero =>
      intro _ s hs t ht
      simp only [pow_zero, one_mul, Nat.sub_zero] at hs ht
      exact hbase s hs t ht
    | succ j ih =>
      intro hjK
      exact baker_extrap_step hk_pos hL1 hS1 hc_h1 hjK rfl rfl rfl p hp_pr hbn_pos hb_le hD_le_15k
        hα_ge1 hα_sum hαm_le h65α rfl rfl hCtot_pos hpoly_S_dom hT0log2L hlogErr
        (by rw [← hΛ'abs]; exact hΛ'_lt) c hCmax_nn hc_abs hUCmax (ih (by omega))
  -- Step K: Psi c 0 s = 0 for all 1 ≤ s ≤ 2^K * h₀ ≥ (L₀ + 1) * (L + 1)^n
  have hvan_K : ∀ s ∈ Finset.Icc 1 ((L₀ + 1) * Fintype.card (Fin n → Fin (L + 1))),
      Psi k p b c (fun _ => 0) s = 0 := by
    intro s hs
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
    have hs_hi : s ≤ 2 ^ K * h₀ := by
      have h1 := (Finset.mem_Icc.mp hs).2
      simp only [Fintype.card_fun, Fintype.card_fin] at h1
      have hL0_le : L₀ + 1 ≤ 2 * c₀ * k := by
        have h2L : L₀ + 1 ≤ 2 * L₀ := by omega
        calc L₀ + 1 ≤ 2 * L₀ := h2L
          _ = 2 * c₀ * k := by dsimp only [L₀]; ring
      have hdom : (L₀ + 1) * (L + 1) ^ n ≤ 2 ^ K * h₀ := by
        calc (L₀ + 1) * (L + 1) ^ n
            ≤ (2 * c₀ * k) * (L + 1) ^ n := Nat.mul_le_mul_right _ hL0_le
          _ = (8 * (K * s_ratio + 1) ^ n * (L + 1) ^ n) * h₀ := by
              dsimp only [c₀, h₀]; ring
          _ ≤ 2 ^ K * h₀ := Nat.mul_le_mul_right h₀ hK_dom
      exact le_trans h1 hdom
    exact hextrap K le_rfl s (Finset.mem_Icc.mpr ⟨hs1, hs_hi⟩) (fun _ => 0) (by simp)
  -- Apply discrete shift-operator nonvanishing (Section 5)!
  let ω : (Fin n → Fin (L + 1)) → ℕ := fun μ => ∏ i : Fin n, p i ^ (μ i).val
  have hω_inj : Function.Injective ω := prime_pow_prod_injective hp_pr hp_inj
  have hω_pos : ∀ μ, 0 < ω μ := fun μ => Finset.prod_pos fun i _ => pow_pos (hp_pr i).pos _
  let Q : (Fin n → Fin (L + 1)) → Polynomial ℚ :=
    fun μ => ∑ l₀ : Fin (L₀ + 1), C (c (l₀, μ) : ℚ) * feldmanPoly k l₀.val
  have hQ_deg : ∀ μ, (Q μ).natDegree ≤ L₀ := by
    intro μ
    refine le_trans (Polynomial.natDegree_sum_le Finset.univ _) ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le L₀, fun l₀ _ => ?_⟩
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [natDegree_feldmanPoly hk_pos]
    exact Nat.lt_succ_iff.mp l₀.isLt
  have hvan_Q : ∀ s ∈ Finset.Icc 1 ((L₀ + 1) * Fintype.card (Fin n → Fin (L + 1))),
      ∑ μ : Fin n → Fin (L + 1), (Q μ).eval (s : ℚ) * (ω μ : ℚ) ^ s = 0 := by
    intro s hs
    have hPsi0 := hvan_K s hs
    rw [← hPsi0]
    unfold Psi
    simp only [Polynomial.hasseDeriv_zero, LinearMap.id_apply, pow_zero, Finset.prod_const_one, mul_one]
    rw [Fintype.sum_prod_type_right]
    apply Finset.sum_congr rfl
    intro μ _
    dsimp only [Q, ω]
    rw [Polynomial.eval_finsetSum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l₀ _
    rw [Polynomial.eval_mul, Polynomial.eval_C, Nat.cast_prod, Finset.prod_pow]
    simp only [Nat.cast_pow]; rfl
  have hQ_all_zero := exp_poly_zero_of_zero_on_Icc ω hω_inj hω_pos L₀ Q hQ_deg hvan_Q
  obtain ⟨⟨l₀_ne, μ_ne⟩, hne⟩ := hc_ne
  have hQne : Q μ_ne ≠ 0 :=
    sum_feldmanPoly_ne_zero hk_pos (fun l₀ => (c (l₀, μ_ne) : ℚ)) ⟨l₀_ne, by exact_mod_cast hne⟩
  exact hQne (hQ_all_zero μ_ne)

theorem baker_feldman_core_uniform {m : ℕ} (hm : 1 ≤ m)
    (s₀ : ℕ) (hs₀_pow : ∀ s : ℕ, s₀ ≤ s → (2 * s) ^ (m + 2) ≤ 2 ^ s)
    (p : Fin (m + 1) → ℕ) (hp_pr : ∀ i, (p i).Prime) (hp_inj : Function.Injective p)
    (α : ℝ) (hα_ge1 : 1 ≤ α) (hα_sum : ∑ i : Fin (m + 1), Real.log (p i : ℝ) ≤ α) :
    0 < bf_C s₀ (m + 1) α ∧ 2 ≤ bf_B₀ s₀ (m + 1) α ∧
      ∀ b : Fin (m + 1) → ℤ,
        bf_B₀ s₀ (m + 1) α ≤ (b (Fin.last m) : ℝ) →
        (∀ i, |b i| ≤ b (Fin.last m)) →
        ((b (Fin.last m) : ℝ)) ^ (-(bf_C s₀ (m + 1) α)) ≤
          |∑ i : Fin (m + 1), (b i : ℝ) * Real.log (p i : ℝ)| := by
  set s_ratio : ℕ := bf_s_ratio α
  have hs_ratio_pos : 1 ≤ s_ratio := by dsimp only [s_ratio, bf_s_ratio]; omega
  have hs_ratio_ge : 128 * α ≤ (s_ratio : ℝ) := by
    have h1 := Nat.le_ceil (128 * α)
    dsimp only [s_ratio, bf_s_ratio]; push_cast; linarith
  set C_poly : ℕ := bf_C_poly (m + 1) α
  set s_u : ℕ := s₀ + Nat.log 2 C_poly + 1
  set u : ℕ := 2 * s_u
  have hu1 : 1 ≤ u := by dsimp only [u, s_u]; omega
  have hu_dom : bf_C_poly_of (m + 1) s_ratio * u ^ (m + 2) ≤ 2 ^ u := by
    have h1 : u ^ (m + 2) ≤ 2 ^ s_u := hs₀_pow s_u (by dsimp only [s_u]; omega)
    have h2 : C_poly ≤ 2 ^ s_u := by
      have hlt : C_poly < 2 ^ (Nat.log 2 C_poly + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num) C_poly
      have hpow : 2 ^ (Nat.log 2 C_poly + 1) ≤ 2 ^ s_u :=
        Nat.pow_le_pow_right (by norm_num) (by dsimp only [s_u]; omega)
      exact le_trans hlt.le hpow
    have hCeq : bf_C_poly_of (m + 1) s_ratio = C_poly := rfl
    rw [hCeq]
    calc C_poly * u ^ (m + 2)
        ≤ 2 ^ s_u * 2 ^ s_u := Nat.mul_le_mul h2 h1
      _ = 2 ^ u := by rw [← pow_add]; dsimp only [u]; ring_nf
  exact baker_feldman_core_of_params hm p hp_pr hp_inj α hα_ge1 hα_sum
    s_ratio u hs_ratio_pos hs_ratio_ge hu1 hu_dom

/- Section 8: Polynomial bounds in `α` and scaled uniform Baker–Feldman -/

def PolyBound (f : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∃ D : ℕ, 0 < C ∧ ∀ α : ℝ, 1 ≤ α → f α ≤ C * α ^ D

lemma polyBound_const (c : ℝ) : PolyBound (fun _ => c) := by
  refine ⟨max c 1, 0, by positivity, fun α _ => ?_⟩
  simp only [pow_zero, mul_one]; exact le_max_left _ _

lemma polyBound_id : PolyBound (fun α => α) :=
  ⟨1, 1, zero_lt_one, fun α _ => by simp⟩

lemma polyBound_le {f g : ℝ → ℝ} (hg : PolyBound g) (hfg : ∀ α : ℝ, 1 ≤ α → f α ≤ g α) :
    PolyBound f := by
  obtain ⟨C, D, hC, h⟩ := hg
  exact ⟨C, D, hC, fun α hα => le_trans (hfg α hα) (h α hα)⟩

lemma polyBound_add {f g : ℝ → ℝ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun α => f α + g α) := by
  obtain ⟨Cf, Df, hCf, hfb⟩ := hf
  obtain ⟨Cg, Dg, hCg, hgb⟩ := hg
  refine ⟨Cf + Cg, max Df Dg, add_pos hCf hCg, fun α hα => ?_⟩
  have h1 : α ^ Df ≤ α ^ max Df Dg := pow_le_pow_right₀ hα (le_max_left _ _)
  have h2 : α ^ Dg ≤ α ^ max Df Dg := pow_le_pow_right₀ hα (le_max_right _ _)
  have hf1 : f α ≤ Cf * α ^ max Df Dg :=
    le_trans (hfb α hα) (mul_le_mul_of_nonneg_left h1 hCf.le)
  have hg1 : g α ≤ Cg * α ^ max Df Dg :=
    le_trans (hgb α hα) (mul_le_mul_of_nonneg_left h2 hCg.le)
  linarith

lemma polyBound_max {f g : ℝ → ℝ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun α => max (f α) (g α)) := by
  obtain ⟨Cf, Df, hCf, hfb⟩ := hf
  obtain ⟨Cg, Dg, hCg, hgb⟩ := hg
  refine ⟨Cf + Cg, max Df Dg, add_pos hCf hCg, fun α hα => ?_⟩
  have h1 : α ^ Df ≤ α ^ max Df Dg := pow_le_pow_right₀ hα (le_max_left _ _)
  have h2 : α ^ Dg ≤ α ^ max Df Dg := pow_le_pow_right₀ hα (le_max_right _ _)
  have hnn : 0 ≤ α ^ max Df Dg := by positivity
  exact max_le
    (le_trans (hfb α hα) (by nlinarith))
    (le_trans (hgb α hα) (by nlinarith))

lemma polyBound_mul {f g : ℝ → ℝ} (hf : PolyBound f) (hg : PolyBound g)
    (_hf0 : ∀ α : ℝ, 1 ≤ α → 0 ≤ f α) (hg0 : ∀ α : ℝ, 1 ≤ α → 0 ≤ g α) :
    PolyBound (fun α => f α * g α) := by
  obtain ⟨Cf, Df, hCf, hfb⟩ := hf
  obtain ⟨Cg, Dg, hCg, hgb⟩ := hg
  refine ⟨Cf * Cg, Df + Dg, mul_pos hCf hCg, fun α hα => ?_⟩
  calc f α * g α
      ≤ (Cf * α ^ Df) * (Cg * α ^ Dg) :=
        mul_le_mul (hfb α hα) (hgb α hα) (hg0 α hα) (by positivity)
    _ = (Cf * Cg) * α ^ (Df + Dg) := by rw [pow_add]; ring

lemma polyBound_pow {f : ℝ → ℝ} (hf : PolyBound f) (_hf0 : ∀ α : ℝ, 1 ≤ α → 0 ≤ f α) (k : ℕ) :
    PolyBound (fun α => (f α) ^ k) := by
  obtain ⟨C, D, hC, hb⟩ := hf
  refine ⟨C ^ k, D * k, pow_pos hC k, fun α hα => ?_⟩
  calc (f α) ^ k ≤ (C * α ^ D) ^ k := pow_le_pow_left₀ (_hf0 α hα) (hb α hα) k
    _ = C ^ k * α ^ (D * k) := by rw [mul_pow, ← pow_mul]

lemma polyBound_natCeil {f : ℝ → ℝ} (hf : PolyBound f) :
    PolyBound (fun α => (Nat.ceil (f α) : ℝ)) := by
  apply polyBound_le (polyBound_add (polyBound_max (polyBound_const 0) hf) (polyBound_const 1))
  intro α _
  by_cases h0 : f α ≤ 0
  · rw [Nat.ceil_eq_zero.mpr h0, Nat.cast_zero]; positivity
  · have hlt : (Nat.ceil (f α) : ℝ) < f α + 1 := Nat.ceil_lt_add_one (not_le.mp h0).le
    linarith [le_max_right (0 : ℝ) (f α)]

lemma polyBound_log {f : ℝ → ℝ} (hf : PolyBound f) (hf1 : ∀ α : ℝ, 1 ≤ α → 1 ≤ f α) :
    PolyBound (fun α => Real.log (f α)) :=
  polyBound_le hf fun α hα => real_log_le_self_of_pos (lt_of_lt_of_le zero_lt_one (hf1 α hα))

private lemma bf_s_ratio_poly : PolyBound (fun α => (bf_s_ratio α : ℝ)) := by
  apply polyBound_le (polyBound_add (polyBound_natCeil (polyBound_mul (polyBound_const 128) polyBound_id
    (fun _ _ => by norm_num) (fun α hα => by linarith))) (polyBound_const 1))
  intro α _; dsimp only [bf_s_ratio]; push_cast; rfl

private lemma bf_C_poly_poly (n : ℕ) : PolyBound (fun α => (bf_C_poly n α : ℝ)) := by
  have hbase : PolyBound (fun α => 2 * (n : ℝ) * (bf_s_ratio α : ℝ) + 1) :=
    polyBound_add (polyBound_mul (polyBound_const (2 * n)) bf_s_ratio_poly
      (fun _ _ => by positivity) (fun _ _ => Nat.cast_nonneg _)) (polyBound_const 1)
  have hpow := polyBound_pow hbase (fun _ _ => by positivity) n
  have h1 := polyBound_mul (polyBound_const (8 * (2 : ℝ) ^ n)) hpow
    (fun _ _ => by positivity) (fun _ _ => by positivity)
  have h2 := polyBound_mul (polyBound_const (200000 * (n : ℝ))) hpow
    (fun _ _ => by positivity) (fun _ _ => by positivity)
  refine polyBound_le (polyBound_add (polyBound_max h1 h2) (polyBound_const 100)) fun α _ => ?_
  dsimp only [bf_C_poly]; push_cast; rfl

private lemma bf_L_poly (s₀ n : ℕ) : PolyBound (fun α => (bf_L s₀ n α : ℝ)) := by
  have hL_le : ∀ α : ℝ, 1 ≤ α → (bf_L s₀ n α : ℝ) ≤
      4 * (2 : ℝ) ^ (2 * s₀) * (bf_C_poly n α : ℝ) ^ 2 := by
    intro α _
    have hne : bf_C_poly n α ≠ 0 := by dsimp only [bf_C_poly]; omega
    have hpow : 2 ^ Nat.log 2 (bf_C_poly n α) ≤ bf_C_poly n α := Nat.pow_log_le_self 2 hne
    have hnat : bf_L s₀ n α ≤ 4 * 2 ^ (2 * s₀) * (bf_C_poly n α) ^ 2 := by
      calc bf_L s₀ n α = 2 ^ (2 * (s₀ + Nat.log 2 (bf_C_poly n α) + 1)) := rfl
        _ = 4 * 2 ^ (2 * s₀) * (2 ^ Nat.log 2 (bf_C_poly n α)) ^ 2 := by
            rw [show 2 * (s₀ + Nat.log 2 (bf_C_poly n α) + 1) =
              2 + 2 * s₀ + 2 * Nat.log 2 (bf_C_poly n α) by omega]
            rw [pow_add, pow_add, pow_mul, mul_comm 2 (Nat.log 2 _), pow_mul]; ring
        _ ≤ 4 * 2 ^ (2 * s₀) * (bf_C_poly n α) ^ 2 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpow 2)
    exact_mod_cast hnat
  exact polyBound_le (polyBound_mul (polyBound_const (4 * (2 : ℝ) ^ (2 * s₀)))
    (polyBound_pow (bf_C_poly_poly n) (fun _ _ => Nat.cast_nonneg _) 2)
    (fun _ _ => by positivity) (fun _ _ => by positivity)) hL_le

private lemma bf_u_poly (s₀ n : ℕ) : PolyBound (fun α => (bf_u s₀ n α : ℝ)) :=
  polyBound_le (bf_L_poly s₀ n) fun α _ => by
    exact_mod_cast (Nat.lt_pow_self (by norm_num : 1 < 2)).le

private lemma bf_K_poly (s₀ n : ℕ) : PolyBound (fun α => (bf_K s₀ n α : ℝ)) :=
  polyBound_le (polyBound_mul (polyBound_const (2 * n)) (bf_u_poly s₀ n)
    (fun _ _ => by positivity) (fun _ _ => Nat.cast_nonneg _)) fun α _ => by
      dsimp only [bf_K]; push_cast; rfl

private lemma bf_S_poly (s₀ n : ℕ) : PolyBound (fun α => (bf_S s₀ n α : ℝ)) :=
  polyBound_le (polyBound_mul bf_s_ratio_poly (bf_L_poly s₀ n)
    (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)) fun α _ => by
      dsimp only [bf_S]; push_cast; rfl

private lemma bf_T₀_poly (s₀ n : ℕ) : PolyBound (fun α => (bf_T₀ s₀ n α : ℝ)) :=
  polyBound_le (polyBound_mul (bf_K_poly s₀ n) (bf_S_poly s₀ n)
    (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)) fun α _ => by
      dsimp only [bf_T₀]; push_cast; rfl

private lemma bf_c_h_poly (s₀ n : ℕ) : PolyBound (fun α => (bf_c_h s₀ n α : ℝ)) :=
  polyBound_le (polyBound_mul (polyBound_const 32) (bf_K_poly s₀ n)
    (fun _ _ => by positivity) (fun _ _ => Nat.cast_nonneg _)) fun α _ => by
      dsimp only [bf_c_h]; push_cast; rfl

private lemma bf_c₀_poly (s₀ n : ℕ) : PolyBound (fun α => (bf_c₀ s₀ n α : ℝ)) := by
  have hbase := polyBound_add (polyBound_mul (bf_K_poly s₀ n) bf_s_ratio_poly
    (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)) (polyBound_const 1)
  have hpow := polyBound_pow hbase (fun _ _ => by positivity) n
  refine polyBound_le (polyBound_mul (polyBound_mul (polyBound_const 4) (bf_c_h_poly s₀ n)
    (fun _ _ => by positivity) (fun _ _ => Nat.cast_nonneg _)) hpow
    (fun _ _ => by positivity) (fun _ _ => by positivity)) fun α _ => ?_
  dsimp only [bf_c₀]; push_cast; ring_nf; rfl

private lemma bf_2K_poly (s₀ n : ℕ) : PolyBound (fun α => (2 : ℝ) ^ bf_K s₀ n α) := by
  refine polyBound_le (polyBound_pow (bf_L_poly s₀ n) (fun _ _ => Nat.cast_nonneg _) (2 * n)) fun α _ => ?_
  have heq : (2 : ℝ) ^ bf_K s₀ n α = (bf_L s₀ n α : ℝ) ^ (2 * n) := by
    dsimp only [bf_K, bf_L]; push_cast; rw [← pow_mul, mul_comm (2 * n)]
  rw [heq]

lemma bf_C_poly_bound (s₀ n : ℕ) : PolyBound (fun α => bf_C s₀ n α) := by
  have hM₀ : PolyBound (fun α => bf_M₀ s₀ n α) := by
    have ht1 := polyBound_mul (polyBound_const 7.5) (bf_T₀_poly s₀ n)
      (fun _ _ => by positivity) (fun _ _ => Nat.cast_nonneg _)
    have hlog1 := polyBound_log (polyBound_mul (polyBound_const (Real.exp 1))
      (polyBound_add (bf_c_h_poly s₀ n) (polyBound_const 2))
      (fun _ _ => by positivity) (fun _ _ => by positivity))
      (fun α _ => by
        have : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        have : (2 : ℝ) ≤ (bf_c_h s₀ n α : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) (bf_c_h s₀ n α)]
        nlinarith)
    have ht2 := polyBound_mul (polyBound_add (bf_c₀_poly s₀ n) (polyBound_const 1)) hlog1
      (fun _ _ => by positivity) (fun α _ => Real.log_nonneg (by
        have : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        have : (2 : ℝ) ≤ (bf_c_h s₀ n α : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) (bf_c_h s₀ n α)]
        nlinarith))
    have ht3 := polyBound_mul (polyBound_mul polyBound_id (bf_L_poly s₀ n)
      (fun α hα => by linarith) (fun _ _ => Nat.cast_nonneg _)) (bf_c_h_poly s₀ n)
      (fun α hα => mul_nonneg (by linarith) (Nat.cast_nonneg _)) (fun _ _ => Nat.cast_nonneg _)
    exact polyBound_le (polyBound_add (polyBound_add ht1 ht2) ht3) fun α _ => by
      dsimp only [bf_M₀]; rfl
  have hCtot : PolyBound (fun α => bf_C_tot s₀ n α) := by
    have ht2 := polyBound_mul (polyBound_const 10) (bf_T₀_poly s₀ n)
      (fun _ _ => by positivity) (fun _ _ => Nat.cast_nonneg _)
    have hlog2 := polyBound_log (polyBound_mul (polyBound_const (Real.exp 1))
      (polyBound_add (polyBound_mul (polyBound_mul (polyBound_const 32) (bf_2K_poly s₀ n)
        (fun _ _ => by positivity) (fun _ _ => by positivity)) (bf_c_h_poly s₀ n)
        (fun _ _ => by positivity) (fun _ _ => Nat.cast_nonneg _)) (polyBound_const 2))
      (fun _ _ => by positivity) (fun _ _ => by positivity))
      (fun α _ => by
        have : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ bf_K s₀ n α := pow_nonneg (by norm_num) _
        have h2 : (0 : ℝ) ≤ (bf_c_h s₀ n α : ℝ) := Nat.cast_nonneg _
        nlinarith [mul_nonneg h1 h2])
    have ht3 := polyBound_mul (polyBound_mul (polyBound_const 2)
      (polyBound_add (bf_c₀_poly s₀ n) (polyBound_const 1)) (fun _ _ => by positivity) (fun _ _ => by positivity))
      hlog2 (fun _ _ => by positivity) (fun α _ => Real.log_nonneg (by
        have : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ bf_K s₀ n α := pow_nonneg (by norm_num) _
        have h2 : (0 : ℝ) ≤ (bf_c_h s₀ n α : ℝ) := Nat.cast_nonneg _
        nlinarith [mul_nonneg h1 h2]))
    have ht4 := polyBound_mul (polyBound_mul (polyBound_mul polyBound_id (bf_L_poly s₀ n)
      (fun α hα => by linarith) (fun _ _ => Nat.cast_nonneg _)) (bf_2K_poly s₀ n)
      (fun α hα => mul_nonneg (by linarith) (Nat.cast_nonneg _)) (fun _ _ => by positivity)) (bf_c_h_poly s₀ n)
      (fun α hα => mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) (pow_nonneg (by norm_num) _))
      (fun _ _ => Nat.cast_nonneg _)
    have ht5 := polyBound_mul (polyBound_mul (polyBound_mul (polyBound_const 3) (bf_2K_poly s₀ n)
      (fun _ _ => by positivity) (fun _ _ => by positivity)) (bf_c_h_poly s₀ n)
      (fun _ _ => by positivity) (fun _ _ => Nat.cast_nonneg _)) (bf_S_poly s₀ n)
      (fun _ _ => by positivity) (fun _ _ => Nat.cast_nonneg _)
    exact polyBound_le (polyBound_add (polyBound_add (polyBound_add (polyBound_add
      (polyBound_add hM₀ ht2) ht3) ht4) ht5) (polyBound_const 20)) fun α _ => by
      dsimp only [bf_C_tot]; rfl
  exact polyBound_add hCtot (polyBound_const 2)

lemma bf_log_B₀_poly_bound (s₀ n : ℕ) (hn : 1 ≤ n) : PolyBound (fun α => Real.log (bf_B₀ s₀ n α)) := by
  have hA1 : PolyBound (fun α => bf_A1 s₀ n α) := by
    have hlog := polyBound_log (polyBound_add (polyBound_mul (polyBound_const 2) (bf_L_poly s₀ n)
      (fun _ _ => by positivity) (fun _ _ => Nat.cast_nonneg _)) (polyBound_const 1))
      (fun α _ => by linarith [Nat.cast_nonneg (α := ℝ) (bf_L s₀ n α)])
    exact polyBound_le (polyBound_add hlog (polyBound_const 1)) fun α _ => by dsimp only [bf_A1]; rfl
  have hA2 : PolyBound (fun α => bf_A2 s₀ n α) := by
    have hc01_nn : ∀ α : ℝ, 1 ≤ α → 0 ≤ (bf_c₀ s₀ n α : ℝ) + 1 := fun α _ =>
      add_nonneg (Nat.cast_nonneg _) zero_le_one
    have hL1_nn : ∀ α : ℝ, 1 ≤ α → 0 ≤ (bf_L s₀ n α : ℝ) + 1 := fun α _ =>
      add_nonneg (Nat.cast_nonneg _) zero_le_one
    have harg := polyBound_mul (polyBound_mul (polyBound_const 20)
      (polyBound_pow (polyBound_add (bf_c₀_poly s₀ n) (polyBound_const 1)) hc01_nn 2)
      (fun _ _ => by norm_num) (fun α hα => pow_nonneg (hc01_nn α hα) 2))
      (polyBound_pow (polyBound_add (bf_L_poly s₀ n) (polyBound_const 1)) hL1_nn (2 * n))
      (fun α hα => mul_nonneg (by norm_num) (pow_nonneg (hc01_nn α hα) 2))
      (fun α hα => pow_nonneg (hL1_nn α hα) (2 * n))
    have hlog := polyBound_log harg fun α _ => by
      have h1 : (1 : ℝ) ≤ ((bf_c₀ s₀ n α : ℝ) + 1) ^ 2 :=
        one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) (bf_c₀ s₀ n α)])
      have h2 : (1 : ℝ) ≤ ((bf_L s₀ n α : ℝ) + 1) ^ (2 * n) :=
        one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) (bf_L s₀ n α)])
      nlinarith
    exact polyBound_le hlog fun α _ => by dsimp only [bf_A2]; rfl
  have hA3 : PolyBound (fun α => bf_A3 s₀ n α) := by
    have h2Kch := polyBound_mul (bf_2K_poly s₀ n) (bf_c_h_poly s₀ n)
      (fun _ _ => by positivity) (fun _ _ => Nat.cast_nonneg _)
    have hX1 := polyBound_mul (polyBound_mul (polyBound_const 32) h2Kch
      (fun _ _ => by positivity) (fun _ _ => by positivity)) (bf_S_poly s₀ n)
      (fun _ _ => by positivity) (fun _ _ => Nat.cast_nonneg _)
    have hX2 := polyBound_mul (polyBound_const 2) (polyBound_pow h2Kch (fun _ _ => by positivity) 2)
      (fun _ _ => by positivity) (fun _ _ => by positivity)
    have hX3 := polyBound_add (polyBound_add (bf_T₀_poly s₀ n) polyBound_id) (polyBound_const 1)
    have hX4 := polyBound_mul (polyBound_mul (polyBound_const 2) h2Kch
      (fun _ _ => by positivity) (fun _ _ => by positivity)) (bf_L_poly s₀ n)
      (fun _ _ => by positivity) (fun _ _ => Nat.cast_nonneg _)
    have hS_pos : ∀ α : ℝ, 1 ≤ α → 1 ≤ (bf_S s₀ n α : ℝ) := fun α _ => by
      have : 1 ≤ bf_S s₀ n α := by
        dsimp only [bf_S, bf_s_ratio, bf_L]
        exact Nat.mul_pos (by omega) (Nat.one_le_pow _ 2 (by norm_num))
      exact_mod_cast this
    have hch_pos : ∀ α : ℝ, 1 ≤ α → 1 ≤ (bf_c_h s₀ n α : ℝ) := fun α _ => by
      have : 1 ≤ bf_c_h s₀ n α := by
        dsimp only [bf_c_h, bf_K, bf_u]
        exact Nat.mul_pos (by norm_num) (Nat.mul_pos (Nat.mul_pos (by norm_num) hn) (by omega))
      exact_mod_cast this
    have hL_pos : ∀ α : ℝ, 1 ≤ α → 1 ≤ (bf_L s₀ n α : ℝ) := fun α _ => by
      exact_mod_cast Nat.one_le_pow (bf_u s₀ n α) 2 (by norm_num)
    have h2K_pos : ∀ α : ℝ, 1 ≤ α → 1 ≤ (2 : ℝ) ^ bf_K s₀ n α := fun _ _ => one_le_pow₀ (by norm_num)
    have hX1_pos : ∀ α : ℝ, 1 ≤ α → 1 ≤ 32 * ((2 : ℝ) ^ bf_K s₀ n α * (bf_c_h s₀ n α : ℝ)) * (bf_S s₀ n α : ℝ) :=
      fun α hα => by
        have h12 := one_le_mul_of_one_le_of_one_le (h2K_pos α hα) (hch_pos α hα)
        exact one_le_mul_of_one_le_of_one_le (by linarith) (hS_pos α hα)
    have hX2_pos : ∀ α : ℝ, 1 ≤ α → 1 ≤ 2 * ((2 : ℝ) ^ bf_K s₀ n α * (bf_c_h s₀ n α : ℝ)) ^ 2 :=
      fun α hα => by
        have h1 := one_le_mul_of_one_le_of_one_le (h2K_pos α hα) (hch_pos α hα)
        have h2 := one_le_pow₀ h1 (n := 2)
        linarith
    have hX3_pos : ∀ α : ℝ, 1 ≤ α → 1 ≤ (bf_T₀ s₀ n α : ℝ) + α + 1 := fun α hα => by
      linarith [Nat.cast_nonneg (α := ℝ) (bf_T₀ s₀ n α)]
    have hX4_pos : ∀ α : ℝ, 1 ≤ α → 1 ≤ 2 * ((2 : ℝ) ^ bf_K s₀ n α * (bf_c_h s₀ n α : ℝ)) * (bf_L s₀ n α : ℝ) :=
      fun α hα => by
        have h12 := one_le_mul_of_one_le_of_one_le (h2K_pos α hα) (hch_pos α hα)
        exact one_le_mul_of_one_le_of_one_le (by linarith) (hL_pos α hα)
    have hsum := polyBound_add
      (polyBound_add (polyBound_log hX1 hX1_pos)
        (polyBound_mul (bf_S_poly s₀ n) (polyBound_log hX2 hX2_pos)
          (fun _ _ => Nat.cast_nonneg _) (fun α hα => Real.log_nonneg (hX2_pos α hα))))
      (polyBound_add
        (polyBound_mul (bf_S_poly s₀ n) (polyBound_log hX3 hX3_pos)
          (fun _ _ => Nat.cast_nonneg _) (fun α hα => Real.log_nonneg (hX3_pos α hα)))
        (polyBound_log hX4 hX4_pos))
    refine polyBound_le hsum fun α hα => ?_
    have hp1 : 0 < 32 * ((2 : ℝ) ^ bf_K s₀ n α * (bf_c_h s₀ n α : ℝ)) * (bf_S s₀ n α : ℝ) := by linarith [hX1_pos α hα]
    have hp2 : 0 < (2 * ((2 : ℝ) ^ bf_K s₀ n α * (bf_c_h s₀ n α : ℝ)) ^ 2) ^ bf_S s₀ n α := pow_pos (by linarith [hX2_pos α hα]) _
    have hp3 : 0 < ((bf_T₀ s₀ n α : ℝ) + α + 1) ^ bf_S s₀ n α := pow_pos (by linarith [hX3_pos α hα]) _
    have hp4 : 0 < 2 * ((2 : ℝ) ^ bf_K s₀ n α * (bf_c_h s₀ n α : ℝ)) * (bf_L s₀ n α : ℝ) := by linarith [hX4_pos α hα]
    dsimp only [bf_A3]
    have hmul_assoc : 32 * (2 : ℝ) ^ bf_K s₀ n α * (bf_c_h s₀ n α : ℝ) * (bf_S s₀ n α : ℝ) *
        (2 * ((2 : ℝ) ^ bf_K s₀ n α * (bf_c_h s₀ n α : ℝ)) ^ 2) ^ bf_S s₀ n α *
        ((bf_T₀ s₀ n α : ℝ) + α + 1) ^ bf_S s₀ n α *
        (2 * (2 : ℝ) ^ bf_K s₀ n α * (bf_c_h s₀ n α : ℝ) * (bf_L s₀ n α : ℝ)) =
      (32 * ((2 : ℝ) ^ bf_K s₀ n α * (bf_c_h s₀ n α : ℝ)) * (bf_S s₀ n α : ℝ)) *
        ((2 * ((2 : ℝ) ^ bf_K s₀ n α * (bf_c_h s₀ n α : ℝ)) ^ 2) ^ bf_S s₀ n α) *
        (((bf_T₀ s₀ n α : ℝ) + α + 1) ^ bf_S s₀ n α) *
        (2 * ((2 : ℝ) ^ bf_K s₀ n α * (bf_c_h s₀ n α : ℝ)) * (bf_L s₀ n α : ℝ)) := by ring
    rw [hmul_assoc, Real.log_mul (mul_pos (mul_pos hp1 hp2) hp3).ne' hp4.ne',
      Real.log_mul (mul_pos hp1 hp2).ne' hp3.ne',
      Real.log_mul hp1.ne' hp2.ne', Real.log_pow, Real.log_pow]
    linarith
  have hk₀ : PolyBound (fun α => (bf_k₀ s₀ n α : ℝ)) := by
    have hD : PolyBound (fun α => (((4 * (2 * bf_S s₀ n α + 4) + 1) ^ 2 : ℕ) : ℝ)) := by
      have h8S_nn : ∀ α : ℝ, 1 ≤ α → 0 ≤ 8 * (bf_S s₀ n α : ℝ) + 17 := fun α _ =>
        add_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (by norm_num)
      have h1 := polyBound_add (polyBound_mul (polyBound_const 8) (bf_S_poly s₀ n)
        (fun _ _ => by norm_num) (fun _ _ => Nat.cast_nonneg _)) (polyBound_const 17)
      refine polyBound_le (polyBound_pow h1 h8S_nn 2) fun α _ => ?_
      push_cast; ring_nf; rfl
    have hmax_nn : ∀ (f : ℝ → ℝ) (α : ℝ), 1 ≤ α → 0 ≤ max 0 (f α) := fun _ _ _ => le_max_left _ _
    have hceil := polyBound_natCeil (polyBound_add (polyBound_add (polyBound_add
      (polyBound_mul (polyBound_const 2) (polyBound_max (polyBound_const 0) hA1)
        (fun _ _ => by norm_num) (hmax_nn _))
      (polyBound_mul (polyBound_const 2) (polyBound_max (polyBound_const 0) hA2)
        (fun _ _ => by norm_num) (hmax_nn _)))
      (polyBound_mul (polyBound_const 2) (polyBound_max (polyBound_const 0) hA3)
        (fun _ _ => by norm_num) (hmax_nn _)))
      (polyBound_const 10))
    refine polyBound_le (polyBound_max (polyBound_const 10) (polyBound_max hD hceil)) fun α _ => ?_
    dsimp only [bf_k₀]
    rw [Nat.cast_max, Nat.cast_max]; rfl
  refine polyBound_le (polyBound_max (polyBound_const (Real.log 2)) (polyBound_add hk₀ (polyBound_const 1)))
    fun α _ => ?_
  dsimp only [bf_B₀]
  rcases le_total 2 (Real.exp ((bf_k₀ s₀ n α : ℝ) + 1)) with h | h
  · rw [max_eq_right h, Real.log_exp]; exact le_max_right _ _
  · rw [max_eq_left h]; exact le_max_left _ _

theorem baker_feldman_scaled (S : Finset ℕ) (h2S : 2 ≤ S.card) (hS : ∀ p ∈ S, p.Prime)
    (s₀ : ℕ) (hs₀_pow : ∀ s : ℕ, s₀ ≤ s → (2 * s) ^ (S.card + 1) ≤ 2 ^ s)
    (α : ℝ) (hα_ge1 : 1 ≤ α) (hα_sum : ∑ p ∈ S, Real.log (p : ℝ) ≤ α)
    (b : ℕ → ℤ) (B : ℝ) (hB : bf_B₀ s₀ S.card α ≤ B)
    (hbB : ∀ p ∈ S, |(b p : ℝ)| ≤ B) (hne : ∃ p ∈ S, b p ≠ 0) :
    (3 * B) ^ (-(bf_C s₀ S.card α + 1)) ≤ |∑ p ∈ S, (b p : ℝ) * Real.log (p : ℝ)| := by
  classical
  set n := S.card
  set m := n - 1
  have hmn : m + 1 = n := by omega
  have hm1 : 1 ≤ m := by omega
  let e : Fin (m + 1) ≃ S := (Fintype.equivFinOfCardEq (by simp [hmn, n])).symm
  let v : Fin (m + 1) → ℤ := fun i => b (e i : ℕ)
  have hsum_v : ∑ p ∈ S, (b p : ℝ) * Real.log (p : ℝ) =
      ∑ i : Fin (m + 1), (v i : ℝ) * Real.log ((e i : ℕ) : ℝ) := by
    rw [← Finset.sum_attach S]
    exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm
  rw [hsum_v]
  have hne_v : ∃ i, v i ≠ 0 := by
    obtain ⟨q, hqS, hqne⟩ := hne
    refine ⟨e.symm ⟨q, hqS⟩, ?_⟩
    dsimp only [v]; simpa using hqne
  have huniv_ne : (Finset.univ : Finset (Fin (m + 1))).Nonempty := ⟨0, Finset.mem_univ 0⟩
  obtain ⟨pivot, _, hpivot_max⟩ := Finset.exists_max_image Finset.univ (fun i => |v i|) huniv_ne
  have hpivot_ne : v pivot ≠ 0 := by
    obtain ⟨i₀, hi₀⟩ := hne_v
    exact abs_pos.mp (lt_of_lt_of_le (abs_pos.mpr hi₀) (hpivot_max i₀ (Finset.mem_univ i₀)))
  let w : Fin (m + 1) → ℤ := fun i => if 0 < v pivot then v i else -v i
  have hw_sum : |∑ i : Fin (m + 1), (w i : ℝ) * Real.log ((e i : ℕ) : ℝ)| =
      |∑ i : Fin (m + 1), (v i : ℝ) * Real.log ((e i : ℕ) : ℝ)| := by
    dsimp only [w]
    split_ifs
    · rfl
    · have hneg : ∑ i : Fin (m + 1), ((-v i : ℤ) : ℝ) * Real.log ((e i : ℕ) : ℝ) =
          -(∑ i : Fin (m + 1), (v i : ℝ) * Real.log ((e i : ℕ) : ℝ)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl; intro i _; push_cast; ring
      rw [hneg, abs_neg]
  rw [← hw_sum]
  have hw_piv_eq : w pivot = |v pivot| := by
    dsimp only [w]
    split_ifs with hpos
    · exact (abs_of_pos hpos).symm
    · exact (abs_of_neg (lt_of_le_of_ne (not_lt.mp hpos) hpivot_ne)).symm
  have hw_piv_pos : 0 < w pivot := by rw [hw_piv_eq]; exact abs_pos.mpr hpivot_ne
  have hw_max : ∀ i, |w i| ≤ w pivot := by
    intro i; rw [hw_piv_eq]; dsimp only [w]; split_ifs
    · exact hpivot_max i (Finset.mem_univ i)
    · rw [abs_neg]; exact hpivot_max i (Finset.mem_univ i)
  have hw_piv_le_B : (w pivot : ℝ) ≤ B := by
    rw [hw_piv_eq, Int.cast_abs]; exact hbB (e pivot : ℕ) (e pivot).2
  let σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap pivot (Fin.last m)
  let p' : Fin (m + 1) → ℕ := fun i => (e (σ i) : ℕ)
  have hp'_pr : ∀ i, (p' i).Prime := fun i => hS (e (σ i)) (e (σ i)).2
  have hp'_inj : Function.Injective p' := fun i j hij =>
    σ.injective (e.injective (Subtype.ext hij))
  have hsum_p' : ∑ i : Fin (m + 1), Real.log (p' i : ℝ) ≤ α := by
    have h1 : ∑ i : Fin (m + 1), Real.log (p' i : ℝ) =
        ∑ i : Fin (m + 1), Real.log ((e i : ℕ) : ℝ) :=
      Equiv.sum_comp σ (fun i => Real.log ((e i : ℕ) : ℝ))
    have h2 : ∑ i : Fin (m + 1), Real.log ((e i : ℕ) : ℝ) = ∑ p ∈ S, Real.log (p : ℝ) := by
      rw [← Finset.sum_attach S]
      exact Fintype.sum_equiv e _ _ fun _ => rfl
    linarith
  have hs₀_m : ∀ s : ℕ, s₀ ≤ s → (2 * s) ^ (m + 2) ≤ 2 ^ s := by
    rw [show m + 2 = S.card + 1 by omega]; exact hs₀_pow
  obtain ⟨hC_pos, hB₀_ge2, hcore⟩ :=
    baker_feldman_core_uniform hm1 s₀ hs₀_m p' hp'_pr hp'_inj α hα_ge1 hsum_p'
  have hm_eq : m + 1 = n := hmn
  rw [← hm_eq]
  rw [← hm_eq] at hB
  set C := bf_C s₀ (m + 1) α
  set B₀ := bf_B₀ s₀ (m + 1) α
  have hB_ge2 : 2 ≤ B := le_trans hB₀_ge2 hB
  have hB_pos : 0 < B := by linarith
  by_cases hbig : B₀ ≤ (w pivot : ℝ)
  · let w' : Fin (m + 1) → ℤ := fun i => w (σ i)
    have hlast : w' (Fin.last m) = w pivot := by dsimp only [w', σ]; rw [Equiv.swap_apply_right]
    have h1 := hcore w' (by rwa [hlast]) (fun i => by rw [hlast]; exact hw_max (σ i))
    rw [hlast] at h1
    have hsum_eq : ∑ i : Fin (m + 1), (w' i : ℝ) * Real.log (p' i : ℝ) =
        ∑ i : Fin (m + 1), (w i : ℝ) * Real.log ((e i : ℕ) : ℝ) :=
      Equiv.sum_comp σ (fun i => (w i : ℝ) * Real.log ((e i : ℕ) : ℝ))
    rw [hsum_eq] at h1
    have hwp_pos : (0 : ℝ) < (w pivot : ℝ) := by exact_mod_cast hw_piv_pos
    have hle3B : (w pivot : ℝ) ≤ 3 * B := by linarith
    have hpow1 : (3 * B) ^ (-C) ≤ (w pivot : ℝ) ^ (-C) :=
      Real.rpow_le_rpow_of_nonpos hwp_pos hle3B (by linarith)
    have hpow2 : (3 * B) ^ (-(C + 1)) ≤ (3 * B) ^ (-C) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    exact le_trans hpow2 (le_trans hpow1 h1)
  · push Not at hbig
    have hwp_ge1 : (1 : ℝ) ≤ (w pivot : ℝ) := by exact_mod_cast hw_piv_pos
    have hwp_posR : (0 : ℝ) < (w pivot : ℝ) := by linarith
    have hB₀_nn : 0 ≤ B₀ := by linarith
    set M : ℕ := Nat.ceil (B₀ / (w pivot : ℝ)) + 1
    have hM_ge1 : 1 ≤ M := by omega
    have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_ge1
    have hM_mul_ge : B₀ ≤ ((M : ℤ) * w pivot : ℝ) := by
      have h1 : B₀ / (w pivot : ℝ) ≤ (M : ℝ) := by
        have := Nat.le_ceil (B₀ / (w pivot : ℝ))
        dsimp only [M]; push_cast; linarith
      have h2 := (div_le_iff₀ hwp_posR).mp h1
      push_cast; linarith
    have hM_le_3B : (M : ℝ) ≤ 3 * B := by
      have h1 : (M : ℝ) < B₀ / (w pivot : ℝ) + 2 := by
        have := Nat.ceil_lt_add_one (div_nonneg hB₀_nn hwp_posR.le)
        dsimp only [M]; push_cast; linarith
      have h2 : B₀ / (w pivot : ℝ) ≤ B₀ := div_le_self hB₀_nn hwp_ge1
      linarith
    have hMw_le_3B : (M : ℝ) * (w pivot : ℝ) ≤ 3 * B := by
      have h1 : (M : ℝ) < B₀ / (w pivot : ℝ) + 2 := by
        have := Nat.ceil_lt_add_one (div_nonneg hB₀_nn hwp_posR.le)
        dsimp only [M]; push_cast; linarith
      have h2 : (M : ℝ) * (w pivot : ℝ) < B₀ + 2 * (w pivot : ℝ) := by
        have := mul_lt_mul_of_pos_right h1 hwp_posR
        rwa [add_mul, div_mul_cancel₀ _ hwp_posR.ne'] at this
      linarith
    let w' : Fin (m + 1) → ℤ := fun i => (M : ℤ) * w (σ i)
    have hlast : w' (Fin.last m) = (M : ℤ) * w pivot := by
      dsimp only [w', σ]; rw [Equiv.swap_apply_right]
    have h1 := hcore w' (by rw [hlast]; push_cast; exact hM_mul_ge) (fun i => by
      rw [hlast, abs_mul, abs_of_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ (M : ℤ)))]
      exact mul_le_mul_of_nonneg_left (hw_max (σ i)) (by exact_mod_cast (by omega : (0 : ℤ) ≤ (M : ℤ))))
    rw [hlast] at h1
    have hsum_eq : ∑ i : Fin (m + 1), (w' i : ℝ) * Real.log (p' i : ℝ) =
        (M : ℝ) * ∑ i : Fin (m + 1), (w i : ℝ) * Real.log ((e i : ℕ) : ℝ) := by
      have hsub : ∑ i : Fin (m + 1), (w' i : ℝ) * Real.log (p' i : ℝ) =
          (M : ℝ) * ∑ i : Fin (m + 1), (w (σ i) : ℝ) * Real.log (p' i : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        dsimp only [w']; push_cast; ring
      rw [hsub, Equiv.sum_comp σ (fun i => (w i : ℝ) * Real.log ((e i : ℕ) : ℝ))]
    rw [hsum_eq, abs_mul, abs_of_pos hM_pos] at h1
    push_cast at h1
    have hMw_pos : (0 : ℝ) < (M : ℝ) * (w pivot : ℝ) := mul_pos hM_pos hwp_posR
    have hpow1 : (3 * B) ^ (-C) ≤ ((M : ℝ) * (w pivot : ℝ)) ^ (-C) :=
      Real.rpow_le_rpow_of_nonpos hMw_pos hMw_le_3B (by linarith)
    have h2 : (3 * B) ^ (-C) ≤ (M : ℝ) * |∑ i : Fin (m + 1), (w i : ℝ) * Real.log ((e i : ℕ) : ℝ)| :=
      le_trans hpow1 h1
    have h3 : (3 * B) ^ (-C) / (M : ℝ) ≤ |∑ i : Fin (m + 1), (w i : ℝ) * Real.log ((e i : ℕ) : ℝ)| :=
      (div_le_iff₀ hM_pos).mpr (by linarith)
    have h4 : (3 * B) ^ (-(C + 1)) = (3 * B) ^ (-C) / (3 * B) := by
      rw [show -(C + 1) = -C + (-1) by ring, Real.rpow_add (by linarith), Real.rpow_neg_one, div_eq_mul_inv]
    have h5 : (3 * B) ^ (-C) / (3 * B) ≤ (3 * B) ^ (-C) / (M : ℝ) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg (by linarith) _) hM_pos hM_le_3B
    linarith

/- Inlined R1.H2, R1.H3, and R1.main -/

lemma smooth_pow_mem {P : Set ℕ} {p : ℕ} (hp : p ∈ P) (hpp : p.Prime) (k : ℕ) :
    p ^ k ∈ Erdos675.composedOf P := by
  refine ⟨pow_pos hpp.pos k, fun q hq hqd => ?_⟩
  have := (Nat.prime_dvd_prime_iff_eq hq hpp).1 (hq.dvd_of_dvd_pow hqd)
  rw [this]; exact hp

lemma smooth_mul_mem {P : Set ℕ} {p m : ℕ} (hp : p ∈ P) (hpp : p.Prime)
    (hm : m ∈ Erdos675.composedOf P) : p * m ∈ Erdos675.composedOf P := by
  refine ⟨Nat.mul_pos hpp.pos hm.1, fun q hq hqd => ?_⟩
  rcases (Nat.Prime.dvd_mul hq).1 hqd with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hq hpp).1 h]; exact hp
  · exact hm.2 q hq h

lemma smooth_infinite {P : Set ℕ} {p : ℕ} (hp : p ∈ P) (hpp : p.Prime) :
    (Set.ofPred (· ∈ Erdos675.composedOf P)).Infinite := by
  have hinj : Function.Injective (fun k : ℕ => p ^ k) := Nat.pow_right_injective hpp.two_le
  exact Set.infinite_of_injective_forall_mem hinj fun k => smooth_pow_mem hp hpp k

lemma smooth_H2 :
    ∀ P : Set ℕ, P.Nonempty → P ⊆ {p : ℕ | p.Prime} →
      StrictMono (Erdos240.a P) ∧ (∀ i, Erdos240.a P i ∈ Erdos675.composedOf P) ∧
        ∀ p ∈ P, ∀ i, Erdos240.a P (i + 1) ≤ p * Erdos240.a P i := by
  classical
  intro P hne hsub
  obtain ⟨p₀, hp₀⟩ := hne
  have hinf := smooth_infinite hp₀ (hsub hp₀)
  have hmem : ∀ i, Erdos240.a P i ∈ Erdos675.composedOf P := fun i =>
    Nat.nth_mem_of_infinite hinf i
  refine ⟨Nat.nth_strictMono hinf, hmem, fun p hp i => ?_⟩
  have hpp : p.Prime := hsub hp
  have hpm := smooth_mul_mem hp hpp (hmem i)
  have hpos := (hmem i).1
  obtain ⟨k, hk⟩ : ∃ k, Nat.nth (· ∈ Erdos675.composedOf P) k = p * Erdos240.a P i :=
    ⟨_, Nat.nth_count hpm⟩
  have hlt : Erdos240.a P i < Nat.nth (· ∈ Erdos675.composedOf P) k := by
    rw [hk]
    have := hpp.two_le
    nlinarith
  have hik : i < k := (Nat.nth_lt_nth hinf).1 hlt
  have : Erdos240.a P (i + 1) ≤ Nat.nth (· ∈ Erdos675.composedOf P) k :=
    (Nat.nth_le_nth hinf).2 hik
  rwa [hk] at this

lemma smooth_logsum (S : Finset ℕ) (n : ℕ) (hS : ∀ p : ℕ, p.Prime → p ∣ n → p ∈ S) :
    Real.log (n : ℝ) = ∑ p ∈ S, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  apply Finset.sum_subset
  · intro p hp
    rw [Nat.support_factorization] at hp
    exact hS p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  · intro p _ hp
    rw [Finsupp.notMem_support_iff] at hp
    rw [hp]; simp

lemma smooth_fact_le (n p : ℕ) (hn : 0 < n) :
    (n.factorization p : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  by_cases hp : p.Prime
  · have h1 : p ^ n.factorization p ≤ n := Nat.le_of_dvd hn (Nat.ordProj_dvd n p)
    have h2 : 2 ^ n.factorization p ≤ p ^ n.factorization p := Nat.pow_le_pow_left hp.two_le _
    have h3 : ((2 : ℝ)) ^ n.factorization p ≤ (n : ℝ) := by exact_mod_cast le_trans h2 h1
    have h4 := Real.log_le_log (by positivity) h3
    rw [Real.log_pow] at h4
    rwa [le_div_iff₀ hl2]
  · rw [Nat.factorization_eq_zero_of_not_prime n hp]
    simp only [Nat.cast_zero]
    exact div_nonneg (Real.log_nonneg hn1) hl2.le

lemma smooth_H3 :
    ∀ (S : Finset ℕ) (x y : ℕ), 0 < x → 0 < y →
      (∀ p : ℕ, p.Prime → p ∣ x → p ∈ S) → (∀ p : ℕ, p.Prime → p ∣ y → p ∈ S) →
      ∃ b : ℕ → ℤ, Real.log (y : ℝ) - Real.log (x : ℝ) = ∑ p ∈ S, (b p : ℝ) * Real.log p ∧
        ∀ p ∈ S, |(b p : ℝ)| ≤ Real.log ((max x y : ℕ) : ℝ) / Real.log 2 := by
  intro S x y hx hy hSx hSy
  refine ⟨fun p => (y.factorization p : ℤ) - (x.factorization p : ℤ), ?_, ?_⟩
  · rw [smooth_logsum S y hSy, smooth_logsum S x hSx, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro p _; push_cast; ring
  · intro p _
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hx1 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
    have hy1 : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
    have hxm : (x : ℝ) ≤ ((max x y : ℕ) : ℝ) := by exact_mod_cast le_max_left x y
    have hym : (y : ℝ) ≤ ((max x y : ℕ) : ℝ) := by exact_mod_cast le_max_right x y
    have a1 := smooth_fact_le x p hx
    have a2 := smooth_fact_le y p hy
    have b1 : Real.log (x : ℝ) / Real.log 2 ≤ Real.log ((max x y : ℕ) : ℝ) / Real.log 2 :=
      div_le_div_of_nonneg_right (Real.log_le_log hx1 hxm) hl2.le
    have b2 : Real.log (y : ℝ) / Real.log 2 ≤ Real.log ((max x y : ℕ) : ℝ) / Real.log 2 :=
      div_le_div_of_nonneg_right (Real.log_le_log hy1 hym) hl2.le
    have c1 : (0 : ℝ) ≤ (x.factorization p : ℝ) := Nat.cast_nonneg _
    have c2 : (0 : ℝ) ≤ (y.factorization p : ℝ) := Nat.cast_nonneg _
    simp only [Int.cast_sub, Int.cast_natCast]
    rw [abs_le]; constructor <;> linarith

lemma bf_C_nonneg (s₀ n : ℕ) {α : ℝ} (hα : 0 ≤ α) : 0 ≤ bf_C s₀ n α := by
  have hlog1 : 0 ≤ Real.log (Real.exp 1 * ((bf_c_h s₀ n α : ℝ) + 2)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    nlinarith [Nat.cast_nonneg (α := ℝ) (bf_c_h s₀ n α)]
  have hlog2 : 0 ≤ Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ bf_K s₀ n α * (bf_c_h s₀ n α : ℝ) + 2)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2K : (0 : ℝ) ≤ (2 : ℝ) ^ bf_K s₀ n α := pow_nonneg (by norm_num) _
    have hch : (0 : ℝ) ≤ (bf_c_h s₀ n α : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg h2K hch]
  have hM₀ : 0 ≤ bf_M₀ s₀ n α := by
    dsimp only [bf_M₀]
    refine add_nonneg (add_nonneg ?_ ?_) ?_
    · exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    · exact mul_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (bf_c₀ s₀ n α)]) hlog1
    · exact mul_nonneg (mul_nonneg hα (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  dsimp only [bf_C, bf_C_tot]
  have h2K : (0 : ℝ) ≤ (2 : ℝ) ^ bf_K s₀ n α := pow_nonneg (by norm_num) _
  have hT : (0 : ℝ) ≤ (bf_T₀ s₀ n α : ℝ) := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ (bf_c₀ s₀ n α : ℝ) := Nat.cast_nonneg _
  have hL : (0 : ℝ) ≤ (bf_L s₀ n α : ℝ) := Nat.cast_nonneg _
  have hch : (0 : ℝ) ≤ (bf_c_h s₀ n α : ℝ) := Nat.cast_nonneg _
  have hS : (0 : ℝ) ≤ (bf_S s₀ n α : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg h2K hch, mul_nonneg hL (mul_nonneg h2K hch), mul_nonneg (mul_nonneg h2K hch) hS]

/- Section 9: Prime selection via Chebyshev + Uniform Baker–Feldman -/

def GoodGap (S : Finset ℕ) (θ : ℝ) : Prop :=
  ∀ x y : ℕ, x ∈ Erdos675.composedOf (S : Set ℕ) → y ∈ Erdos675.composedOf (S : Set ℕ) →
    x < y → y ≤ 2 * x → (x : ℝ) ^ θ ≤ ((y - x : ℕ) : ℝ)

lemma goodGap_two {ε : ℝ} (_hε0 : 0 < ε) (_hε1 : ε < 1) : GoodGap {2} (1 - ε) := by
  intro x y hx hy hxy hy2x
  have hpow2 : ∀ w : ℕ, w ∈ Erdos675.composedOf (({2} : Finset ℕ) : Set ℕ) →
      w = 2 ^ (w.factorization 2) := by
    intro w hw
    apply Nat.eq_of_factorization_eq hw.1.ne' (pow_ne_zero _ (by norm_num))
    intro p
    rw [Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_apply]
    split_ifs with hp
    · subst hp; rfl
    · by_cases hpp : p.Prime
      · by_cases hpd : p ∣ w
        · have hmem := hw.2 p hpp hpd
          simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hmem
          exact absurd hmem.symm hp
        · simp [Nat.factorization_eq_zero_of_not_dvd hpd]
      · simp [Nat.factorization_eq_zero_of_not_prime w hpp]
  have hx2 := hpow2 x hx
  have hy2 := hpow2 y hy
  have hlt_exp : x.factorization 2 < y.factorization 2 := by
    by_contra hle
    push Not at hle
    have : y ≤ x := by rw [hx2, hy2]; exact Nat.pow_le_pow_right (by norm_num) hle
    omega
  have h2x_le_y : 2 * x ≤ y := by
    calc 2 * x = 2 * 2 ^ x.factorization 2 := by conv_lhs => rw [hx2]
      _ = 2 ^ (x.factorization 2 + 1) := by rw [pow_succ']
      _ ≤ 2 ^ y.factorization 2 := Nat.pow_le_pow_right (by norm_num) hlt_exp
      _ = y := hy2.symm
  have hy_eq : y = 2 * x := by omega
  have hsub_eq : ((y - x : ℕ) : ℝ) = (x : ℝ) := by
    rw [hy_eq, show 2 * x - x = x by omega]
  rw [hsub_eq]
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx.1
  calc (x : ℝ) ^ (1 - ε) ≤ (x : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    _ = (x : ℝ) := Real.rpow_one _

lemma chebyshev_primes_Ioc_four_mul :
    ∀ᶠ X : ℕ in atTop,
      (Real.log 2 / 2) * (X : ℝ) / Real.log (4 * (X : ℝ)) ≤
        (((Finset.Ioc X (4 * X)).filter Nat.Prime).card : ℝ) := by
  rw [Filter.eventually_atTop]
  refine ⟨3000000, fun X hX => ?_⟩
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hXge : (3000000 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlog4X_pos : 0 < Real.log (4 * (X : ℝ)) := Real.log_pos (by linarith)
  have htheta_diff : Chebyshev.theta (4 * (X : ℝ)) - Chebyshev.theta (X : ℝ) =
      ∑ p ∈ (Finset.Ioc X (4 * X)).filter Nat.Prime, Real.log (p : ℝ) := by
    have h4X_fl : ⌊4 * (X : ℝ)⌋₊ = 4 * X := by
      rw [show 4 * (X : ℝ) = ((4 * X : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
    simp only [Chebyshev.theta, Nat.floor_natCast, h4X_fl]
    have hsub : (Finset.Ioc 0 X).filter Nat.Prime ⊆ (Finset.Ioc 0 (4 * X)).filter Nat.Prime :=
      Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right (by omega))
    have hsdiff : ((Finset.Ioc 0 (4 * X)).filter Nat.Prime) \ ((Finset.Ioc 0 X).filter Nat.Prime) =
        (Finset.Ioc X (4 * X)).filter Nat.Prime := by
      ext p
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨⟨hp0, hp4X⟩, hp_pr⟩, hnot⟩
        refine ⟨⟨?_, hp4X⟩, hp_pr⟩
        by_contra hle; apply hnot; exact ⟨⟨hp0, by omega⟩, hp_pr⟩
      · rintro ⟨⟨hpX, hp4X⟩, hp_pr⟩
        exact ⟨⟨⟨by omega, hp4X⟩, hp_pr⟩, fun h => by omega⟩
    rw [← Finset.sum_sdiff hsub, hsdiff]; ring
  have hsum_le : ∑ p ∈ (Finset.Ioc X (4 * X)).filter Nat.Prime, Real.log (p : ℝ) ≤
      (((Finset.Ioc X (4 * X)).filter Nat.Prime).card : ℝ) * Real.log (4 * (X : ℝ)) := by
    calc ∑ p ∈ (Finset.Ioc X (4 * X)).filter Nat.Prime, Real.log (p : ℝ)
        ≤ ∑ _p ∈ (Finset.Ioc X (4 * X)).filter Nat.Prime, Real.log (4 * (X : ℝ)) := by
          apply Finset.sum_le_sum
          intro p hp
          rw [Finset.mem_filter, Finset.mem_Ioc] at hp
          exact Real.log_le_log (by exact_mod_cast (by omega : 0 < p)) (by exact_mod_cast hp.1.2)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have htheta4 := Chebyshev.theta_ge (4 * X)
  have hthetaX := Chebyshev.theta_le_log4_mul_x hXpos.le
  have hlog4_eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hX14 : (40 : ℝ) ≤ (X : ℝ) ^ (1 / 4 : ℝ) := by
    have h1 : (40 : ℝ) ^ 4 ≤ (X : ℝ) := by linarith
    have h2 : (40 : ℝ) = ((40 : ℝ) ^ 4) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_natCast 40 4, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [h2]
    exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have hlog4X_le : Real.log (4 * (X : ℝ)) ≤ 8 * (X : ℝ) ^ (1 / 4 : ℝ) := by
    have h1 : Real.log (4 * (X : ℝ)) = 4 * Real.log ((4 * (X : ℝ)) ^ (1 / 4 : ℝ)) := by
      rw [← Real.log_rpow (by positivity), ← Real.rpow_mul (by positivity)]; norm_num
    have h2 : Real.log ((4 * (X : ℝ)) ^ (1 / 4 : ℝ)) ≤ (4 * (X : ℝ)) ^ (1 / 4 : ℝ) :=
      real_log_le_self_of_pos (by positivity)
    have h3 : (4 * (X : ℝ)) ^ (1 / 4 : ℝ) = (4 : ℝ) ^ (1 / 4 : ℝ) * (X : ℝ) ^ (1 / 4 : ℝ) :=
      Real.mul_rpow (by norm_num) hXpos.le
    have h4 : (4 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
      have : (4 : ℝ) ≤ (2 : ℝ) ^ 4 := by norm_num
      calc (4 : ℝ) ^ (1 / 4 : ℝ) ≤ ((2 : ℝ) ^ 4) ^ (1 / 4 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) this (by norm_num)
        _ = 2 := by rw [← Real.rpow_natCast 2 4, ← Real.rpow_mul (by norm_num)]; norm_num
    calc Real.log (4 * (X : ℝ))
        = 4 * Real.log ((4 * (X : ℝ)) ^ (1 / 4 : ℝ)) := h1
      _ ≤ 4 * ((4 : ℝ) ^ (1 / 4 : ℝ) * (X : ℝ) ^ (1 / 4 : ℝ)) := by rw [← h3]; linarith
      _ ≤ 4 * (2 * (X : ℝ) ^ (1 / 4 : ℝ)) := by gcongr
      _ = 8 * (X : ℝ) ^ (1 / 4 : ℝ) := by ring
  have hlog5X_le : Real.log (4 * (X : ℝ) + 1) ≤ 8 * (X : ℝ) ^ (1 / 4 : ℝ) := by
    have hle : 4 * (X : ℝ) + 1 ≤ 5 * (X : ℝ) := by linarith
    have h1 : Real.log (4 * (X : ℝ) + 1) ≤ Real.log (5 * (X : ℝ)) :=
      Real.log_le_log (by positivity) hle
    have h2 : Real.log (5 * (X : ℝ)) = 4 * Real.log ((5 * (X : ℝ)) ^ (1 / 4 : ℝ)) := by
      rw [← Real.log_rpow (by positivity), ← Real.rpow_mul (by positivity)]; norm_num
    have h3 : Real.log ((5 * (X : ℝ)) ^ (1 / 4 : ℝ)) ≤ (5 * (X : ℝ)) ^ (1 / 4 : ℝ) :=
      real_log_le_self_of_pos (by positivity)
    have h4 : (5 * (X : ℝ)) ^ (1 / 4 : ℝ) = (5 : ℝ) ^ (1 / 4 : ℝ) * (X : ℝ) ^ (1 / 4 : ℝ) :=
      Real.mul_rpow (by norm_num) hXpos.le
    have h5 : (5 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
      have : (5 : ℝ) ≤ (2 : ℝ) ^ 4 := by norm_num
      calc (5 : ℝ) ^ (1 / 4 : ℝ) ≤ ((2 : ℝ) ^ 4) ^ (1 / 4 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) this (by norm_num)
        _ = 2 := by rw [← Real.rpow_natCast 2 4, ← Real.rpow_mul (by norm_num)]; norm_num
    calc Real.log (4 * (X : ℝ) + 1)
        ≤ Real.log (5 * (X : ℝ)) := h1
      _ = 4 * Real.log ((5 * (X : ℝ)) ^ (1 / 4 : ℝ)) := h2
      _ ≤ 4 * ((5 : ℝ) ^ (1 / 4 : ℝ) * (X : ℝ) ^ (1 / 4 : ℝ)) := by rw [← h4]; linarith
      _ ≤ 4 * (2 * (X : ℝ) ^ (1 / 4 : ℝ)) := by gcongr
      _ = 8 * (X : ℝ) ^ (1 / 4 : ℝ) := by ring
  have hsqrt_eq : Real.sqrt (4 * (X : ℝ)) = 2 * (X : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by norm_num, Real.sqrt_eq_rpow]
  have hpow34 : (X : ℝ) ^ (1 / 4 : ℝ) ≤ (X : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hmul34 : (X : ℝ) ^ (1 / 2 : ℝ) * (X : ℝ) ^ (1 / 4 : ℝ) = (X : ℝ) ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hXpos]; norm_num
  have hX34_X : (X : ℝ) ^ (3 / 4 : ℝ) * 40 ≤ (X : ℝ) := by
    have h1 : (X : ℝ) ^ (3 / 4 : ℝ) * (X : ℝ) ^ (1 / 4 : ℝ) = (X : ℝ) := by
      rw [← Real.rpow_add hXpos]; norm_num
    nlinarith [Real.rpow_nonneg hXpos.le (3 / 4 : ℝ)]
  have herr_le : Real.log (((4 * X : ℕ) : ℝ) + 1) +
      2 * Real.sqrt ((4 * X : ℕ) : ℝ) * Real.log ((4 * X : ℕ) : ℝ) ≤ (X : ℝ) := by
    push_cast
    have h1 : 2 * Real.sqrt (4 * (X : ℝ)) * Real.log (4 * (X : ℝ)) ≤ 32 * (X : ℝ) ^ (3 / 4 : ℝ) := by
      rw [hsqrt_eq]
      have h2 := mul_le_mul_of_nonneg_left hlog4X_le (show 0 ≤ 2 * (2 * (X : ℝ) ^ (1 / 2 : ℝ)) by positivity)
      calc 2 * (2 * (X : ℝ) ^ (1 / 2 : ℝ)) * Real.log (4 * (X : ℝ))
          ≤ 2 * (2 * (X : ℝ) ^ (1 / 2 : ℝ)) * (8 * (X : ℝ) ^ (1 / 4 : ℝ)) := h2
        _ = 32 * ((X : ℝ) ^ (1 / 2 : ℝ) * (X : ℝ) ^ (1 / 4 : ℝ)) := by ring
        _ = 32 * (X : ℝ) ^ (3 / 4 : ℝ) := by rw [hmul34]
    linarith
  have hl2 : (0.69 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hmain : (Real.log 2 / 2) * (X : ℝ) ≤
      (((Finset.Ioc X (4 * X)).filter Nat.Prime).card : ℝ) * Real.log (4 * (X : ℝ)) := by
    have hcast4 : ((4 * X : ℕ) : ℝ) = 4 * (X : ℝ) := by push_cast; ring
    rw [hcast4] at htheta4 herr_le
    rw [← htheta_diff] at hsum_le
    rw [hlog4_eq] at hthetaX
    nlinarith
  rwa [div_le_iff₀ hlog4X_pos]

def SmoothLe (S : Finset ℕ) (Y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Y).filter (fun w => w.primeFactors ⊆ S)

lemma smoothLe_card_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (Y : ℕ) :
    (SmoothLe S Y).card ≤ (Nat.log 2 Y + 1) ^ S.card := by
  classical
  let R := Nat.log 2 Y
  let f : ℕ → (S → Fin (R + 1)) := fun w p =>
    ⟨min (w.factorization (p : ℕ)) R, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hmem : ∀ w ∈ SmoothLe S Y, f w ∈ (Finset.univ : Finset (S → Fin (R + 1))) :=
    fun _ _ => Finset.mem_univ _
  have hinj : Set.InjOn f (SmoothLe S Y : Set ℕ) := by
    intro w₁ hw₁ w₂ hw₂ hfeq
    simp only [Finset.mem_coe, SmoothLe, Finset.mem_filter, Finset.mem_Icc] at hw₁ hw₂
    have hfac_lt : ∀ w : ℕ, 1 ≤ w ∧ w ≤ Y → ∀ p ∈ S, w.factorization p ≤ R := by
      intro w hw p hpS
      have hpp : p.Prime := hS p hpS
      have h1 : 2 ^ w.factorization p ≤ p ^ w.factorization p := Nat.pow_le_pow_left hpp.two_le _
      have h2 : p ^ w.factorization p ≤ w := Nat.le_of_dvd hw.1 (Nat.ordProj_dvd w p)
      have hlt : Y < 2 ^ (R + 1) := Nat.lt_pow_succ_log_self (by norm_num) Y
      have h3 : 2 ^ w.factorization p < 2 ^ (R + 1) :=
        lt_of_le_of_lt (le_trans h1 (le_trans h2 hw.2)) hlt
      have h4 : w.factorization p < R + 1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h3
      omega
    apply Nat.eq_of_factorization_eq (by have := hw₁.1.1; omega) (by have := hw₂.1.1; omega)
    intro p
    by_cases hpS : p ∈ S
    · have h1 := congrFun hfeq ⟨p, hpS⟩
      have hval := congrArg Fin.val h1
      dsimp only [f] at hval
      rw [min_eq_left (hfac_lt w₁ hw₁.1 p hpS), min_eq_left (hfac_lt w₂ hw₂.1 p hpS)] at hval
      exact hval
    · by_cases hpp : p.Prime
      · have hd1 : ¬ p ∣ w₁ := fun hd => hpS (hw₁.2 (Nat.mem_primeFactors.mpr ⟨hpp, hd, by have := hw₁.1.1; omega⟩))
        have hd2 : ¬ p ∣ w₂ := fun hd => hpS (hw₂.2 (Nat.mem_primeFactors.mpr ⟨hpp, hd, by have := hw₂.1.1; omega⟩))
        rw [Nat.factorization_eq_zero_of_not_dvd hd1, Nat.factorization_eq_zero_of_not_dvd hd2]
      · rw [Nat.factorization_eq_zero_of_not_prime w₁ hpp, Nat.factorization_eq_zero_of_not_prime w₂ hpp]
  calc (SmoothLe S Y).card
      ≤ (Finset.univ : Finset (S → Fin (R + 1))).card := Finset.card_le_card_of_injOn f hmem hinj
    _ = (R + 1) ^ S.card := by simp [Fintype.card_fin]

noncomputable def BadQ (X : ℕ) (ε : ℝ) (r u v : ℕ) : Finset ℕ :=
  (Finset.Ioc X (4 * X)).filter (fun q =>
    |(v : ℝ) * (q : ℝ) ^ r - (u : ℝ)| < (max ((v : ℝ) * (q : ℝ) ^ r) (u : ℝ)) ^ (1 - ε))

lemma pow_sub_pow_ge {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ r : ℕ, 1 ≤ r → (b - a) * a ^ (r - 1) ≤ b ^ r - a ^ r := by
  intro r hr
  induction r with
  | zero => omega
  | succ r _ =>
    rcases r with _ | r
    · simp
    · have h1 : b ^ (r + 1 + 1) - a ^ (r + 1 + 1) =
          (b - a) * b ^ (r + 1) + a * (b ^ (r + 1) - a ^ (r + 1)) := by ring
      have h2 : a ^ (r + 1) ≤ b ^ (r + 1) := pow_le_pow_left₀ ha hab _
      have h3 : 0 ≤ b - a := sub_nonneg.mpr hab
      have h4 : (b - a) * a ^ (r + 1) ≤ (b - a) * b ^ (r + 1) := mul_le_mul_of_nonneg_left h2 h3
      have h5 : 0 ≤ a * (b ^ (r + 1) - a ^ (r + 1)) := mul_nonneg ha (sub_nonneg.mpr h2)
      rw [show r + 1 + 1 - 1 = r + 1 by omega]
      linarith

lemma badQ_card_le {X : ℕ} (hX1 : 1 ≤ X) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hXε : 4 ≤ (X : ℝ) ^ ε) {r u v : ℕ} (hr : 1 ≤ r) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    ((BadQ X ε r u v).card : ℝ) ≤ 16 * (X : ℝ) ^ (1 - ε) + 1 := by
  classical
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX1
  have hX1R : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
  by_cases hne : (BadQ X ε r u v).Nonempty
  · set qmin := (BadQ X ε r u v).min' hne
    set qmax := (BadQ X ε r u v).max' hne
    have hqmin_mem := Finset.min'_mem (BadQ X ε r u v) hne
    have hqmax_mem := Finset.max'_mem (BadQ X ε r u v) hne
    have hsub_Icc : BadQ X ε r u v ⊆ Finset.Icc qmin qmax := fun q hq =>
      Finset.mem_Icc.mpr ⟨Finset.min'_le _ q hq, Finset.le_max' _ q hq⟩
    have hcard_le : (BadQ X ε r u v).card ≤ qmax - qmin + 1 := by
      calc (BadQ X ε r u v).card ≤ (Finset.Icc qmin qmax).card := Finset.card_le_card hsub_Icc
        _ = qmax + 1 - qmin := Nat.card_Icc qmin qmax
        _ = qmax - qmin + 1 := by
          have := Finset.min'_le _ qmax hqmax_mem
          omega
    have hqmin_flt := Finset.mem_filter.mp hqmin_mem
    have hqmax_flt := Finset.mem_filter.mp hqmax_mem
    have hqmin_Ioc := Finset.mem_Ioc.mp hqmin_flt.1
    have hqmax_Ioc := Finset.mem_Ioc.mp hqmax_flt.1
    have hqmin_le_max : qmin ≤ qmax := Finset.min'_le _ qmax hqmax_mem
    have hu_le : (u : ℝ) ≤ 2 * (v : ℝ) * (4 * (X : ℝ)) ^ r := by
      by_contra hu_gt
      push Not at hu_gt
      have h1 : (v : ℝ) * (qmin : ℝ) ^ r ≤ (v : ℝ) * (4 * (X : ℝ)) ^ r := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg v)
        exact pow_le_pow_left₀ (Nat.cast_nonneg qmin) (by exact_mod_cast hqmin_Ioc.2) r
      have h2 : (v : ℝ) * (qmin : ℝ) ^ r < (u : ℝ) / 2 := by linarith
      have h3 : (u : ℝ) / 2 < |(v : ℝ) * (qmin : ℝ) ^ r - (u : ℝ)| := by
        rw [abs_of_neg (by linarith)]; linarith
      have hmax_eq : max ((v : ℝ) * (qmin : ℝ) ^ r) (u : ℝ) = (u : ℝ) := max_eq_right (by linarith)
      have hX_le_u : (X : ℝ) ≤ (u : ℝ) := by
        have h4X1 : (1 : ℝ) ≤ 4 * (X : ℝ) := by linarith
        have hXr : (X : ℝ) ≤ (4 * (X : ℝ)) ^ r := by
          calc (X : ℝ) ≤ 4 * (X : ℝ) := by linarith
            _ = (4 * (X : ℝ)) ^ 1 := (pow_one _).symm
            _ ≤ (4 * (X : ℝ)) ^ r := pow_le_pow_right₀ h4X1 hr
        have hv1 : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
        nlinarith
      have huε : 2 ≤ (u : ℝ) ^ ε := by
        calc (2 : ℝ) ≤ 4 := by norm_num
          _ ≤ (X : ℝ) ^ ε := hXε
          _ ≤ (u : ℝ) ^ ε := Real.rpow_le_rpow hXpos.le hX_le_u hε0.le
      have hupos : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
      have hpow_le : (u : ℝ) ^ (1 - ε) ≤ (u : ℝ) / 2 := by
        rw [Real.rpow_sub hupos, Real.rpow_one]
        exact div_le_div_of_nonneg_left hupos.le (by norm_num) huε
      have hflt := hqmin_flt.2
      rw [hmax_eq] at hflt
      linarith
    have hmax_bound : ∀ q ∈ BadQ X ε r u v,
        (max ((v : ℝ) * (q : ℝ) ^ r) (u : ℝ)) ^ (1 - ε) ≤
          (2 * (v : ℝ) * (4 * (X : ℝ)) ^ r) ^ (1 - ε) := by
      intro q hq
      have hq_Ioc := Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1
      have h1 : (v : ℝ) * (q : ℝ) ^ r ≤ 2 * (v : ℝ) * (4 * (X : ℝ)) ^ r := by
        have hq4 : (v : ℝ) * (q : ℝ) ^ r ≤ (v : ℝ) * (4 * (X : ℝ)) ^ r :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hq_Ioc.2) r)
            (Nat.cast_nonneg _)
        have hnn : 0 ≤ (v : ℝ) * (4 * (X : ℝ)) ^ r := by positivity
        linarith
      exact Real.rpow_le_rpow (by positivity) (max_le h1 hu_le) (by linarith)
    have hdiff_lt : (v : ℝ) * ((qmax : ℝ) ^ r - (qmin : ℝ) ^ r) ≤
        2 * (2 * (v : ℝ) * (4 * (X : ℝ)) ^ r) ^ (1 - ε) := by
      have h1 := hqmax_flt.2
      have h2 := hqmin_flt.2
      have hb1 := hmax_bound qmax hqmax_mem
      have hb2 := hmax_bound qmin hqmin_mem
      have htri : |(v : ℝ) * (qmax : ℝ) ^ r - (v : ℝ) * (qmin : ℝ) ^ r| ≤
          |(v : ℝ) * (qmax : ℝ) ^ r - (u : ℝ)| + |(v : ℝ) * (qmin : ℝ) ^ r - (u : ℝ)| := by
        rw [show (v : ℝ) * (qmax : ℝ) ^ r - (v : ℝ) * (qmin : ℝ) ^ r =
          ((v : ℝ) * (qmax : ℝ) ^ r - (u : ℝ)) - ((v : ℝ) * (qmin : ℝ) ^ r - (u : ℝ)) by ring]
        exact abs_sub _ _
      have hpow_ge : (qmin : ℝ) ^ r ≤ (qmax : ℝ) ^ r :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hqmin_le_max) r
      have hnn : 0 ≤ (v : ℝ) * ((qmax : ℝ) ^ r - (qmin : ℝ) ^ r) :=
        mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hpow_ge)
      rw [show (v : ℝ) * (qmax : ℝ) ^ r - (v : ℝ) * (qmin : ℝ) ^ r =
        (v : ℝ) * ((qmax : ℝ) ^ r - (qmin : ℝ) ^ r) by ring, abs_of_nonneg hnn] at htri
      linarith
    have hqmin_le_maxR : (qmin : ℝ) ≤ (qmax : ℝ) := by exact_mod_cast hqmin_le_max
    have hpow_diff : ((qmax : ℝ) - (qmin : ℝ)) * (X : ℝ) ^ (r - 1) ≤ (qmax : ℝ) ^ r - (qmin : ℝ) ^ r := by
      have h1 := pow_sub_pow_ge (Nat.cast_nonneg qmin) hqmin_le_maxR r hr
      have h2 : (X : ℝ) ^ (r - 1) ≤ (qmin : ℝ) ^ (r - 1) :=
        pow_le_pow_left₀ hXpos.le (by exact_mod_cast hqmin_Ioc.1.le) _
      exact le_trans (mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr hqmin_le_maxR)) h1
    have hvpos : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
    have hv1 : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
    have hden_pos : 0 < (v : ℝ) * (X : ℝ) ^ (r - 1) := by positivity
    have hqdiff_le : (qmax : ℝ) - (qmin : ℝ) ≤ 16 * (X : ℝ) ^ (1 - ε) := by
      have h1 : (v : ℝ) * (X : ℝ) ^ (r - 1) * ((qmax : ℝ) - (qmin : ℝ)) ≤
          2 * (2 * (v : ℝ) * (4 * (X : ℝ)) ^ r) ^ (1 - ε) := by
        have := mul_le_mul_of_nonneg_left hpow_diff (Nat.cast_nonneg v)
        linarith
      rw [← le_div_iff₀' hden_pos] at h1
      refine le_trans h1 ?_
      have hsplit : (2 * (v : ℝ) * (4 * (X : ℝ)) ^ r) ^ (1 - ε) =
          (2 : ℝ) ^ (1 - ε) * (v : ℝ) ^ (1 - ε) * ((4 : ℝ) ^ (1 - ε) * (X : ℝ) ^ (1 - ε)) ^ r := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by norm_num) (Nat.cast_nonneg _),
          ← Real.rpow_natCast (4 * (X : ℝ)) r,
          ← Real.rpow_mul (by positivity), mul_comm (r : ℝ) (1 - ε), Real.rpow_mul (by positivity),
          Real.rpow_natCast, Real.mul_rpow (by norm_num) hXpos.le]
      have h2_le : (2 : ℝ) ^ (1 - ε) ≤ 2 := by
        calc (2 : ℝ) ^ (1 - ε) ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := Real.rpow_one 2
      have hv_le : (v : ℝ) ^ (1 - ε) ≤ (v : ℝ) := by
        calc (v : ℝ) ^ (1 - ε) ≤ (v : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hv1 (by linarith)
          _ = (v : ℝ) := Real.rpow_one _
      have h4_le : (4 : ℝ) ^ (1 - ε) ≤ 4 := by
        calc (4 : ℝ) ^ (1 - ε) ≤ (4 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 4 := Real.rpow_one 4
      have hX_split : (X : ℝ) ^ (1 - ε) = (X : ℝ) / (X : ℝ) ^ ε := by
        rw [Real.rpow_sub hXpos, Real.rpow_one]
      have hratio_le : (4 : ℝ) ^ (1 - ε) * (X : ℝ) ^ (1 - ε) ≤ (X : ℝ) := by
        rw [hX_split]
        have : (4 : ℝ) ^ (1 - ε) * ((X : ℝ) / (X : ℝ) ^ ε) = (X : ℝ) * ((4 : ℝ) ^ (1 - ε) / (X : ℝ) ^ ε) := by ring
        rw [this]
        have hfrac : (4 : ℝ) ^ (1 - ε) / (X : ℝ) ^ ε ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith
        nlinarith
      have hpow_r : ((4 : ℝ) ^ (1 - ε) * (X : ℝ) ^ (1 - ε)) ^ r ≤
          ((4 : ℝ) ^ (1 - ε) * (X : ℝ) ^ (1 - ε)) * (X : ℝ) ^ (r - 1) := by
        conv_lhs => rw [show r = 1 + (r - 1) by omega, pow_add, pow_one]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio_le _) (by positivity)
      have hpow_r2 : ((4 : ℝ) ^ (1 - ε) * (X : ℝ) ^ (1 - ε)) ^ r ≤ 4 * (X : ℝ) ^ (1 - ε) * (X : ℝ) ^ (r - 1) := by
        have : (4 : ℝ) ^ (1 - ε) * (X : ℝ) ^ (1 - ε) ≤ 4 * (X : ℝ) ^ (1 - ε) := by
          nlinarith [Real.rpow_nonneg hXpos.le (1 - ε)]
        nlinarith [pow_nonneg hXpos.le (r - 1)]
      rw [div_le_iff₀ hden_pos, hsplit]
      calc 2 * ((2 : ℝ) ^ (1 - ε) * (v : ℝ) ^ (1 - ε) * ((4 : ℝ) ^ (1 - ε) * (X : ℝ) ^ (1 - ε)) ^ r)
          ≤ 2 * (2 * (v : ℝ) * (4 * (X : ℝ) ^ (1 - ε) * (X : ℝ) ^ (r - 1))) := by
            gcongr
        _ = 16 * (X : ℝ) ^ (1 - ε) * ((v : ℝ) * (X : ℝ) ^ (r - 1)) := by ring
    have hcardR : ((BadQ X ε r u v).card : ℝ) ≤ (qmax : ℝ) - (qmin : ℝ) + 1 := by
      have h1 : ((BadQ X ε r u v).card : ℝ) ≤ ((qmax - qmin + 1 : ℕ) : ℝ) := by exact_mod_cast hcard_le
      have h2 : ((qmax - qmin : ℕ) : ℝ) = (qmax : ℝ) - (qmin : ℝ) := Nat.cast_sub hqmin_le_max
      push_cast at h1; linarith
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
    positivity

lemma bf_large_gap {ε : ℝ} (hε0 : 0 < ε) (S' : Finset ℕ) (h2S' : 2 ≤ S'.card)
    (hS' : ∀ p ∈ S', p.Prime) (s₀ : ℕ)
    (hs₀_pow : ∀ s : ℕ, s₀ ≤ s → (2 * s) ^ (S'.card + 1) ≤ 2 ^ s)
    (α : ℝ) (hα_ge1 : 1 ≤ α) (hα_sum : ∑ p ∈ S', Real.log (p : ℝ) ≤ α)
    {x y : ℕ} (hx : x ∈ Erdos675.composedOf (S' : Set ℕ))
    (hy : y ∈ Erdos675.composedOf (S' : Set ℕ)) (hxy : x < y) (hy2x : y ≤ 2 * x)
    (hx_gt2 : (2 : ℝ) < (x : ℝ))
    (hlogx_ge : max 2 (max ((bf_C s₀ S'.card α + 1) * Real.log (3 * bf_B₀ s₀ S'.card α) / ε)
      (((8 * (bf_C s₀ S'.card α + 1)) / ε) ^ 2)) ≤ Real.log (x : ℝ)) :
    (x : ℝ) ^ (1 - ε) ≤ ((y - x : ℕ) : ℝ) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx_pos : (0 : ℝ) < (x : ℝ) := by linarith
  have hy_pos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy.1
  obtain ⟨b, hlog_diff, hb_bd⟩ := smooth_H3 S' x y hx.1 hy.1
    (fun p hp hd => by simpa using hx.2 p hp hd)
    (fun p hp hd => by simpa using hy.2 p hp hd)
  rw [max_eq_right hxy.le] at hb_bd
  have hΛ_pos : 0 < Real.log (y : ℝ) - Real.log (x : ℝ) := by
    have hxyR : (x : ℝ) < (y : ℝ) := by exact_mod_cast hxy
    have := Real.log_lt_log hx_pos hxyR
    linarith
  have hnz : ∃ p ∈ S', b p ≠ 0 := by
    by_contra hall; push Not at hall
    have : ∑ p ∈ S', (b p : ℝ) * Real.log (p : ℝ) = 0 :=
      Finset.sum_eq_zero fun p hp => by rw [hall p hp]; simp
    linarith
  set B : ℝ := max (bf_B₀ s₀ S'.card α) (Real.log (y : ℝ) / Real.log 2)
  have hbak := baker_feldman_scaled S' h2S' hS' s₀ hs₀_pow α hα_ge1 hα_sum
    b B (le_max_left _ _) (fun p hp => le_trans (hb_bd p hp) (le_max_right _ _)) hnz
  rw [← hlog_diff, abs_of_pos hΛ_pos] at hbak
  have hlogy_le : Real.log (y : ℝ) / Real.log 2 ≤ 4 * Real.log (x : ℝ) := by
    have h1 : Real.log (y : ℝ) ≤ Real.log 2 + Real.log (x : ℝ) := by
      rw [← Real.log_mul (by norm_num) hx_pos.ne']
      exact Real.log_le_log hy_pos (by exact_mod_cast hy2x)
    have h2 : Real.log (y : ℝ) ≤ 2 * Real.log (x : ℝ) := by
      have h3 : Real.log 2 ≤ Real.log (x : ℝ) := Real.log_le_log (by norm_num) hx_gt2.le
      linarith
    have h4 : (1 / 2 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
    rw [div_le_iff₀ hl2]; nlinarith
  have h3B_le : 3 * B ≤ max (3 * bf_B₀ s₀ S'.card α) (12 * Real.log (x : ℝ)) := by
    dsimp only [B]
    rcases le_total (bf_B₀ s₀ S'.card α) (Real.log (y : ℝ) / Real.log 2) with h | h
    · rw [max_eq_right h]; exact le_trans (by linarith) (le_max_right _ _)
    · rw [max_eq_left h]; exact le_max_left _ _
  have hC_nn : 0 ≤ bf_C s₀ S'.card α := bf_C_nonneg s₀ S'.card (by linarith)
  have hB₀_ge2' : 2 ≤ bf_B₀ s₀ S'.card α := by dsimp only [bf_B₀]; exact le_max_left _ _
  have hB_pos : 0 < B := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hlogx_ge2 : 2 ≤ Real.log (x : ℝ) := le_trans (le_max_left _ _) hlogx_ge
  have hlog3B_le : (bf_C s₀ S'.card α + 1) * Real.log (3 * B) ≤ ε * Real.log (x : ℝ) := by
    have h3B_pos : 0 < 3 * B := by linarith
    have hlog_mono := Real.log_le_log h3B_pos h3B_le
    rcases le_total (3 * bf_B₀ s₀ S'.card α) (12 * Real.log (x : ℝ)) with h | h
    · rw [max_eq_right h] at hlog_mono
      have hsqrt : Real.log (12 * Real.log (x : ℝ)) ≤ 8 * Real.sqrt (Real.log (x : ℝ)) := by
        have h1 := real_log_le_two_sqrt (show 0 < 12 * Real.log (x : ℝ) by linarith)
        rw [Real.sqrt_mul (by norm_num)] at h1
        have h2 : Real.sqrt 12 ≤ 4 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        calc Real.log (12 * Real.log (x : ℝ))
            ≤ 2 * (Real.sqrt 12 * Real.sqrt (Real.log (x : ℝ))) := h1
          _ ≤ 2 * (4 * Real.sqrt (Real.log (x : ℝ))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)) (by norm_num)
          _ = 8 * Real.sqrt (Real.log (x : ℝ)) := by ring
      have hL2 : ((8 * (bf_C s₀ S'.card α + 1)) / ε) ^ 2 ≤ Real.log (x : ℝ) :=
        le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hlogx_ge
      have h8C_nn : 0 ≤ (8 * (bf_C s₀ S'.card α + 1)) / ε :=
        div_nonneg (mul_nonneg (by norm_num) (add_nonneg hC_nn zero_le_one)) hε0.le
      have hsqrt2 : (8 * (bf_C s₀ S'.card α + 1)) / ε ≤ Real.sqrt (Real.log (x : ℝ)) := by
        rw [← Real.sqrt_sq h8C_nn]
        exact Real.sqrt_le_sqrt hL2
      have hmul : 8 * (bf_C s₀ S'.card α + 1) ≤ ε * Real.sqrt (Real.log (x : ℝ)) := by
        rw [div_le_iff₀ hε0] at hsqrt2
        linarith
      have hsq : Real.sqrt (Real.log (x : ℝ)) * Real.sqrt (Real.log (x : ℝ)) = Real.log (x : ℝ) :=
        Real.mul_self_sqrt (by linarith)
      have hstep1 : (bf_C s₀ S'.card α + 1) * Real.log (3 * B) ≤
          (bf_C s₀ S'.card α + 1) * (8 * Real.sqrt (Real.log (x : ℝ))) :=
        mul_le_mul_of_nonneg_left (le_trans hlog_mono hsqrt) (add_nonneg hC_nn zero_le_one)
      have hstep2 : (bf_C s₀ S'.card α + 1) * (8 * Real.sqrt (Real.log (x : ℝ))) =
          (8 * (bf_C s₀ S'.card α + 1)) * Real.sqrt (Real.log (x : ℝ)) := by ring
      have hstep3 : (8 * (bf_C s₀ S'.card α + 1)) * Real.sqrt (Real.log (x : ℝ)) ≤
          (ε * Real.sqrt (Real.log (x : ℝ))) * Real.sqrt (Real.log (x : ℝ)) :=
        mul_le_mul_of_nonneg_right hmul (Real.sqrt_nonneg _)
      calc (bf_C s₀ S'.card α + 1) * Real.log (3 * B)
          ≤ (bf_C s₀ S'.card α + 1) * (8 * Real.sqrt (Real.log (x : ℝ))) := hstep1
        _ = (8 * (bf_C s₀ S'.card α + 1)) * Real.sqrt (Real.log (x : ℝ)) := hstep2
        _ ≤ (ε * Real.sqrt (Real.log (x : ℝ))) * Real.sqrt (Real.log (x : ℝ)) := hstep3
        _ = ε * Real.log (x : ℝ) := by rw [mul_assoc, hsq]
    · rw [max_eq_left h] at hlog_mono
      have hL1 : (bf_C s₀ S'.card α + 1) * Real.log (3 * bf_B₀ s₀ S'.card α) / ε ≤ Real.log (x : ℝ) :=
        le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hlogx_ge
      rw [div_le_iff₀ hε0] at hL1
      exact le_trans (mul_le_mul_of_nonneg_left hlog_mono (add_nonneg hC_nn zero_le_one)) (by linarith [hL1])
  have hxε_ge : (3 * B) ^ (bf_C s₀ S'.card α + 1) ≤ (x : ℝ) ^ ε := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < 3 * B), Real.rpow_def_of_pos hx_pos]
    exact Real.exp_le_exp.mpr (by linarith [hlog3B_le])
  have hgap_log : (x : ℝ) ^ (-ε) ≤ Real.log (y : ℝ) - Real.log (x : ℝ) := by
    have hinv : ((x : ℝ) ^ ε)⁻¹ ≤ ((3 * B) ^ (bf_C s₀ S'.card α + 1))⁻¹ :=
      inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _) hxε_ge
    rw [← Real.rpow_neg hx_pos.le, ← Real.rpow_neg (by linarith)] at hinv
    exact le_trans hinv hbak
  have hgap : (x : ℝ) * (Real.log (y : ℝ) - Real.log (x : ℝ)) ≤ ((y - x : ℕ) : ℝ) := by
    rw [Nat.cast_sub hxy.le, ← Real.log_div hy_pos.ne' hx_pos.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hy_pos hx_pos)
    have e : (x : ℝ) * ((y : ℝ) / (x : ℝ) - 1) = (y : ℝ) - (x : ℝ) := by field_simp
    nlinarith
  have hmul : (x : ℝ) ^ (1 - ε) = (x : ℝ) * (x : ℝ) ^ (-ε) := by
    rw [show 1 - ε = 1 + (-ε) by ring, Real.rpow_add hx_pos, Real.rpow_one]
  rw [hmul]
  exact le_trans (mul_le_mul_of_nonneg_left hgap_log hx_pos.le) hgap

set_option maxHeartbeats 400000 in
lemma exists_next_prime {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (S : Finset ℕ) (h2 : 2 ∈ S) (hS : ∀ p ∈ S, p.Prime) (hGood : GoodGap S (1 - ε)) :
    ∃ q : ℕ, q.Prime ∧ (∀ p ∈ S, p < q) ∧ GoodGap (insert q S) (1 - ε) := by
  classical
  let n : ℕ := S.card + 1
  have hn1 : 1 ≤ n := by omega
  have hS_ne : S.Nonempty := ⟨2, h2⟩
  obtain ⟨s₀, _, hs₀_pow⟩ := explicit_u_base (n + 1)
  obtain ⟨C_C, D_C, hCC_pos, hC_bd⟩ := bf_C_poly_bound s₀ n
  obtain ⟨C_B, D_B, hCB_pos, hB_bd⟩ := bf_log_B₀_poly_bound s₀ n hn1
  let α_const : ℝ := (∑ p ∈ S, Real.log (p : ℝ)) + 3
  have hα_const_ge3 : 3 ≤ α_const := by
    have : 0 ≤ ∑ p ∈ S, Real.log (p : ℝ) :=
      Finset.sum_nonneg fun p hp => Real.log_nonneg (by exact_mod_cast (hS p hp).one_lt.le)
    dsimp only [α_const]; linarith
  let α_fn : ℕ → ℝ := fun X => α_const * Real.log (X : ℝ)
  have hα_ge1 : ∀ X : ℕ, 3 ≤ X → 1 ≤ α_fn X := by
    intro X hX
    have hlog3 : 1 ≤ Real.log (X : ℝ) := by
      rw [Real.le_log_iff_exp_le (by exact_mod_cast (by omega : 0 < X))]
      have := Real.exp_one_lt_d9
      have : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
      linarith
    dsimp only [α_fn]; nlinarith
  have hα_sum : ∀ X : ℕ, 3 ≤ X → ∀ q ∈ Finset.Ioc X (4 * X),
      ∑ p ∈ insert q S, Real.log (p : ℝ) ≤ α_fn X := by
    intro X hX q hq
    have hq_le : (q : ℝ) ≤ 4 * (X : ℝ) := by
      exact_mod_cast (Finset.mem_Ioc.mp hq).2
    have hq_pos : (0 : ℝ) < (q : ℝ) := by
      have := (Finset.mem_Ioc.mp hq).1
      exact_mod_cast (by omega : 0 < q)
    have hX_ne : (X : ℝ) ≠ 0 := by exact_mod_cast (by omega : X ≠ 0)
    have hlogq : Real.log (q : ℝ) ≤ Real.log 4 + Real.log (X : ℝ) := by
      rw [← Real.log_mul (by norm_num) hX_ne]
      exact Real.log_le_log hq_pos hq_le
    have hlog4 : Real.log 4 ≤ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; linarith [Real.log_two_lt_d9]
    have hlogX1 : 1 ≤ Real.log (X : ℝ) := by
      rw [Real.le_log_iff_exp_le (by exact_mod_cast (by omega : 0 < X))]
      have := Real.exp_one_lt_d9
      have : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
      linarith
    have hsum_ins : ∑ p ∈ insert q S, Real.log (p : ℝ) ≤ Real.log (q : ℝ) + ∑ p ∈ S, Real.log (p : ℝ) := by
      have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
        have hq_gt := (Finset.mem_Ioc.mp hq).1
        exact_mod_cast (by omega : 1 ≤ q)
      by_cases hqS : q ∈ S
      · rw [Finset.insert_eq_of_mem hqS]; linarith [Real.log_nonneg hq1]
      · rw [Finset.sum_insert hqS]
    dsimp only [α_fn, α_const]; nlinarith
  let L_fn : ℕ → ℝ := fun X =>
    max 2 (max ((bf_C s₀ n (α_fn X) + 1) * Real.log (3 * bf_B₀ s₀ n (α_fn X)) / ε)
               (((8 * (bf_C s₀ n (α_fn X) + 1)) / ε) ^ 2))
  let Y_fn : ℕ → ℕ := fun X => Nat.ceil (2 * Real.exp (L_fn X)) + 4
  have hY_polylog : ∃ A_Y : ℝ, ∃ E_Y : ℕ, 0 < A_Y ∧ ∀ X : ℕ, 3 ≤ X →
      Real.log (Y_fn X : ℝ) ≤ A_Y * (Real.log (X : ℝ)) ^ E_Y := by
    let K_C := C_C * α_const ^ D_C
    let K_B := C_B * α_const ^ D_B
    let E_Y := max (D_C + D_B) (2 * D_C)
    let A1 := ((K_C + 1) * (Real.log 3 + K_B)) / ε
    let A2 := (8 * (K_C + 1) / ε) ^ 2
    let A_Y := Real.log 3 + max 2 (max A1 A2)
    refine ⟨A_Y, E_Y, by positivity, fun X hX => ?_⟩
    have hlogX1 : 1 ≤ Real.log (X : ℝ) := by
      rw [Real.le_log_iff_exp_le (by exact_mod_cast (by omega : 0 < X))]
      have := Real.exp_one_lt_d9
      have : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
      linarith
    have hα1 := hα_ge1 X hX
    have hC1 : bf_C s₀ n (α_fn X) ≤ K_C * (Real.log (X : ℝ)) ^ D_C := by
      have h := hC_bd (α_fn X) hα1
      dsimp only [α_fn, K_C] at h ⊢
      rw [mul_pow] at h; linarith
    have hB1 : Real.log (bf_B₀ s₀ n (α_fn X)) ≤ K_B * (Real.log (X : ℝ)) ^ D_B := by
      have h := hB_bd (α_fn X) hα1
      dsimp only [α_fn, K_B] at h ⊢
      rw [mul_pow] at h; linarith
    have hlog3B : Real.log (3 * bf_B₀ s₀ n (α_fn X)) ≤
        (Real.log 3 + K_B) * (Real.log (X : ℝ)) ^ D_B := by
      have hBpos : 0 < bf_B₀ s₀ n (α_fn X) := by
        dsimp only [bf_B₀]; positivity
      rw [Real.log_mul (by norm_num) hBpos.ne']
      have hpow1 : 1 ≤ (Real.log (X : ℝ)) ^ D_B := one_le_pow₀ hlogX1
      nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)]
    have hC_plus : bf_C s₀ n (α_fn X) + 1 ≤ (K_C + 1) * (Real.log (X : ℝ)) ^ D_C := by
      have hpow1 : 1 ≤ (Real.log (X : ℝ)) ^ D_C := one_le_pow₀ hlogX1
      nlinarith
    have hB₀_ge2 : 2 ≤ bf_B₀ s₀ n (α_fn X) := by dsimp only [bf_B₀]; exact le_max_left _ _
    have hC_nn : 0 ≤ bf_C s₀ n (α_fn X) := bf_C_nonneg s₀ n (by linarith)
    have hpowE : ∀ d, d ≤ E_Y → (Real.log (X : ℝ)) ^ d ≤ (Real.log (X : ℝ)) ^ E_Y :=
      fun d hd => pow_le_pow_right₀ hlogX1 hd
    have hterm1 : (bf_C s₀ n (α_fn X) + 1) * Real.log (3 * bf_B₀ s₀ n (α_fn X)) / ε ≤
        A1 * (Real.log (X : ℝ)) ^ E_Y := by
      have hmul : (bf_C s₀ n (α_fn X) + 1) * Real.log (3 * bf_B₀ s₀ n (α_fn X)) ≤
          ((K_C + 1) * (Real.log 3 + K_B)) * (Real.log (X : ℝ)) ^ (D_C + D_B) := by
        have h1 : 0 ≤ Real.log (3 * bf_B₀ s₀ n (α_fn X)) := Real.log_nonneg (by linarith)
        calc (bf_C s₀ n (α_fn X) + 1) * Real.log (3 * bf_B₀ s₀ n (α_fn X))
            ≤ ((K_C + 1) * (Real.log (X : ℝ)) ^ D_C) * ((Real.log 3 + K_B) * (Real.log (X : ℝ)) ^ D_B) :=
              mul_le_mul hC_plus hlog3B h1 (by positivity)
          _ = ((K_C + 1) * (Real.log 3 + K_B)) * (Real.log (X : ℝ)) ^ (D_C + D_B) := by
              rw [pow_add]; ring
      have h2 := le_trans hmul (mul_le_mul_of_nonneg_left (hpowE (D_C + D_B) (le_max_left _ _)) (by positivity))
      dsimp only [A1]
      rw [show ((K_C + 1) * (Real.log 3 + K_B)) / ε * (Real.log (X : ℝ)) ^ E_Y =
        ((K_C + 1) * (Real.log 3 + K_B)) * (Real.log (X : ℝ)) ^ E_Y / ε by ring]
      exact div_le_div_of_nonneg_right h2 hε0.le
    have hterm2 : ((8 * (bf_C s₀ n (α_fn X) + 1)) / ε) ^ 2 ≤ A2 * (Real.log (X : ℝ)) ^ E_Y := by
      have h1 : (8 * (bf_C s₀ n (α_fn X) + 1)) / ε ≤ (8 * (K_C + 1) / ε) * (Real.log (X : ℝ)) ^ D_C := by
        rw [show (8 * (K_C + 1) / ε) * (Real.log (X : ℝ)) ^ D_C =
          (8 * (K_C + 1) * (Real.log (X : ℝ)) ^ D_C) / ε by ring]
        exact div_le_div_of_nonneg_right (by linarith) hε0.le
      have h2 := pow_le_pow_left₀ (by positivity) h1 2
      rw [mul_pow, ← pow_mul, mul_comm D_C 2] at h2
      have h3 := mul_le_mul_of_nonneg_left (hpowE (2 * D_C) (le_max_right _ _)) (by positivity : 0 ≤ (8 * (K_C + 1) / ε) ^ 2)
      dsimp only [A2]
      exact le_trans h2 h3
    have hL_le : L_fn X ≤ max 2 (max A1 A2) * (Real.log (X : ℝ)) ^ E_Y := by
      have hpow1 : 1 ≤ (Real.log (X : ℝ)) ^ E_Y := one_le_pow₀ hlogX1
      dsimp only [L_fn]
      refine max_le ?_ (max_le ?_ ?_)
      · calc (2 : ℝ) ≤ max 2 (max A1 A2) := le_max_left _ _
          _ ≤ max 2 (max A1 A2) * (Real.log (X : ℝ)) ^ E_Y := le_mul_of_one_le_right (by positivity) hpow1
      · exact le_trans hterm1 (mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_right _ _)) (by positivity))
      · exact le_trans hterm2 (mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_right _ _)) (by positivity))
    have hY_le : (Y_fn X : ℝ) ≤ 3 * Real.exp (L_fn X) := by
      have hL2 : 2 ≤ L_fn X := le_max_left _ _
      have hexp7 : 7 ≤ Real.exp (L_fn X) := by
        have h1 : Real.exp 2 ≤ Real.exp (L_fn X) := Real.exp_le_exp.mpr hL2
        have h2 : (7 : ℝ) ≤ Real.exp 2 := by
          have : (2.7 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le
          have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          nlinarith
        linarith
      have hceil : (Nat.ceil (2 * Real.exp (L_fn X)) : ℝ) < 2 * Real.exp (L_fn X) + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      dsimp only [Y_fn]; push_cast; linarith
    have hlogY : Real.log (Y_fn X : ℝ) ≤ Real.log 3 + L_fn X := by
      have hYpos : (0 : ℝ) < (Y_fn X : ℝ) := by dsimp only [Y_fn]; positivity
      calc Real.log (Y_fn X : ℝ) ≤ Real.log (3 * Real.exp (L_fn X)) := Real.log_le_log hYpos hY_le
        _ = Real.log 3 + L_fn X := by rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
    have hpow1 : 1 ≤ (Real.log (X : ℝ)) ^ E_Y := one_le_pow₀ hlogX1
    dsimp only [A_Y]
    nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)]
  obtain ⟨A_Y, E_Y, hAY_pos, hY_bd⟩ := hY_polylog
  let hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  let R_bd := A_Y / Real.log 2 + 1
  have hR_bd : ∀ X : ℕ, 3 ≤ X → ((Nat.log 2 (Y_fn X) : ℝ) + 1) ≤ R_bd * (Real.log (X : ℝ)) ^ E_Y := by
    intro X hX
    have hlogX1 : 1 ≤ Real.log (X : ℝ) := by
      rw [Real.le_log_iff_exp_le (by exact_mod_cast (by omega : 0 < X))]
      have := Real.exp_one_lt_d9
      have : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
      linarith
    have h1 : (2 : ℝ) ^ (Nat.log 2 (Y_fn X)) ≤ (Y_fn X : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by dsimp only [Y_fn]; omega)
    have h2 : (Nat.log 2 (Y_fn X) : ℝ) * Real.log 2 ≤ Real.log (Y_fn X : ℝ) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (by exact_mod_cast h1)
    have h3 : (Nat.log 2 (Y_fn X) : ℝ) ≤ Real.log (Y_fn X : ℝ) / Real.log 2 :=
      (le_div_iff₀ hl2).mpr h2
    have h4 := div_le_div_of_nonneg_right (hY_bd X hX) hl2.le
    rw [mul_div_right_comm] at h4
    have hpow1 : 1 ≤ (Real.log (X : ℝ)) ^ E_Y := one_le_pow₀ hlogX1
    dsimp only [R_bd]
    nlinarith
  let E_tot : ℕ := E_Y * (2 * S.card + 1) + 1
  let C_tot_bad : ℝ := 17 * R_bd ^ (2 * S.card + 1)
  have h_compare : ∀ᶠ X : ℕ in atTop,
      C_tot_bad * (Real.log (X : ℝ)) ^ E_tot * (X : ℝ) ^ (1 - ε) <
        (Real.log 2 / 2) * (X : ℝ) / Real.log (4 * (X : ℝ)) := by
    have hlog_littleO := isLittleO_log_rpow_rpow_atTop (E_tot + 1 : ℝ) hε0
    have hbound := hlog_littleO.bound (show 0 < (Real.log 2 / 4) / (2 * C_tot_bad) by positivity)
    rw [Filter.eventually_atTop] at hbound
    obtain ⟨M_r, hM_r⟩ := hbound
    rw [Filter.eventually_atTop]
    refine ⟨max 4 (Nat.ceil M_r + 1), fun X hX => ?_⟩
    have hX4 : 4 ≤ X := le_trans (le_max_left _ _) hX
    have hXR : M_r ≤ (X : ℝ) := by
      have h1 : Nat.ceil M_r + 1 ≤ X := le_trans (le_max_right _ _) hX
      have h2 := Nat.le_ceil M_r
      linarith [show (Nat.ceil M_r : ℝ) ≤ (X : ℝ) by exact_mod_cast (by omega : Nat.ceil M_r ≤ X)]
    have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
    have hlogX1 : 1 ≤ Real.log (X : ℝ) := by
      rw [Real.le_log_iff_exp_le hXpos]
      have := Real.exp_one_lt_d9
      have : (4 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX4
      linarith
    have hb := hM_r (X : ℝ) hXR
    have hrpow_eq1 : Real.log (X : ℝ) ^ ((E_tot + 1 : ℕ) : ℝ) = Real.log (X : ℝ) ^ (E_tot + 1) :=
      Real.rpow_natCast _ _
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hb
    have hpow_nat : (Real.log (X : ℝ) ^ (E_tot + 1 : ℝ)) = Real.log (X : ℝ) ^ E_tot * Real.log (X : ℝ) := by
      rw [show (E_tot + 1 : ℝ) = ((E_tot + 1 : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast, pow_succ]
    rw [hpow_nat] at hb
    have hlog4X : Real.log (4 * (X : ℝ)) ≤ 2 * Real.log (X : ℝ) := by
      rw [Real.log_mul (by norm_num) hXpos.ne']
      have : Real.log 4 ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hX4)
      linarith
    have hlog4X_pos : 0 < Real.log (4 * (X : ℝ)) := Real.log_pos (by exact_mod_cast (by omega : 1 < 4 * X))
    have hXsplit : (X : ℝ) ^ (1 - ε) * (X : ℝ) ^ ε = (X : ℝ) := by
      rw [← Real.rpow_add hXpos]; ring_nf; exact Real.rpow_one _
    have h1 : C_tot_bad * (Real.log (X : ℝ)) ^ E_tot * Real.log (4 * (X : ℝ)) ≤
        (Real.log 2 / 4) * (X : ℝ) ^ ε := by
      have hC_ne : C_tot_bad ≠ 0 := by positivity
      calc C_tot_bad * (Real.log (X : ℝ)) ^ E_tot * Real.log (4 * (X : ℝ))
          ≤ C_tot_bad * (Real.log (X : ℝ)) ^ E_tot * (2 * Real.log (X : ℝ)) := by
            gcongr
        _ = (2 * C_tot_bad) * (Real.log (X : ℝ) ^ E_tot * Real.log (X : ℝ)) := by ring
        _ ≤ (2 * C_tot_bad) * ((Real.log 2 / 4) / (2 * C_tot_bad) * (X : ℝ) ^ ε) := by
            gcongr
        _ = (Real.log 2 / 4) * (X : ℝ) ^ ε := by field_simp [hC_ne]
    have h2 : C_tot_bad * (Real.log (X : ℝ)) ^ E_tot * (X : ℝ) ^ (1 - ε) * Real.log (4 * (X : ℝ)) <
        (Real.log 2 / 2) * (X : ℝ) := by
      have h3 := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hXpos.le (1 - ε))
      have h4 : (Real.log 2 / 4) * (X : ℝ) ^ ε * (X : ℝ) ^ (1 - ε) = (Real.log 2 / 4) * (X : ℝ) := by
        rw [mul_assoc, mul_comm ((X : ℝ) ^ ε), hXsplit]
      nlinarith
    rwa [lt_div_iff₀ hlog4X_pos]
  have hXε_ev : ∀ᶠ X : ℕ in atTop, 4 ≤ (X : ℝ) ^ ε := by
    have htend : Tendsto (fun X : ℕ => (X : ℝ) ^ ε) atTop atTop :=
      (tendsto_rpow_atTop hε0).comp tendsto_natCast_atTop_atTop
    exact htend.eventually (eventually_ge_atTop 4)
  have hall := chebyshev_primes_Ioc_four_mul.and (h_compare.and (hXε_ev.and
    (eventually_ge_atTop (max 3 (S.max' hS_ne)))))
  rw [Filter.eventually_atTop] at hall
  obtain ⟨X₀, hX₀⟩ := hall
  obtain ⟨hcheb, hcmp, hXε, hXge⟩ := hX₀ X₀ le_rfl
  have hX3 : 3 ≤ X₀ := le_trans (le_max_left _ _) hXge
  have hXS : S.max' hS_ne ≤ X₀ := le_trans (le_max_right _ _) hXge
  have hXpos : (0 : ℝ) < (X₀ : ℝ) := by exact_mod_cast (by omega : 0 < X₀)
  let Y := Y_fn X₀
  let R := Nat.log 2 Y
  let Triples := (Finset.Icc 1 R) ×ˢ (SmoothLe S Y ×ˢ SmoothLe S Y)
  let BadUnion := Triples.biUnion (fun t => BadQ X₀ ε t.1 t.2.1 t.2.2)
  have hBad_card : (BadUnion.card : ℝ) ≤ C_tot_bad * (Real.log (X₀ : ℝ)) ^ E_tot * (X₀ : ℝ) ^ (1 - ε) := by
    have hlogX1 : 1 ≤ Real.log (X₀ : ℝ) := by
      rw [Real.le_log_iff_exp_le hXpos]
      have := Real.exp_one_lt_d9
      have : (3 : ℝ) ≤ (X₀ : ℝ) := by exact_mod_cast hX3
      linarith
    have htri_sum : (BadUnion.card : ℝ) ≤ ∑ t ∈ Triples, ((BadQ X₀ ε t.1 t.2.1 t.2.2).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have heach : ∀ t ∈ Triples, ((BadQ X₀ ε t.1 t.2.1 t.2.2).card : ℝ) ≤ 17 * (X₀ : ℝ) ^ (1 - ε) := by
      intro t ht
      simp only [Triples, Finset.mem_product, Finset.mem_Icc, SmoothLe, Finset.mem_filter] at ht
      have hbad := badQ_card_le (by omega : 1 ≤ X₀) hε0 hε1 hXε ht.1.1 ht.2.1.1.1 ht.2.2.1.1
      have hX1e : (1 : ℝ) ≤ (X₀ : ℝ) ^ (1 - ε) := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ X₀)) (by linarith)
      linarith
    have hsum_le : ∑ t ∈ Triples, ((BadQ X₀ ε t.1 t.2.1 t.2.2).card : ℝ) ≤
        (Triples.card : ℝ) * (17 * (X₀ : ℝ) ^ (1 - ε)) := by
      calc ∑ t ∈ Triples, ((BadQ X₀ ε t.1 t.2.1 t.2.2).card : ℝ)
          ≤ ∑ _t ∈ Triples, (17 * (X₀ : ℝ) ^ (1 - ε)) := Finset.sum_le_sum heach
        _ = (Triples.card : ℝ) * (17 * (X₀ : ℝ) ^ (1 - ε)) := by rw [Finset.sum_const, nsmul_eq_mul]
    have hT_card : (Triples.card : ℝ) ≤ R_bd ^ (2 * S.card + 1) * (Real.log (X₀ : ℝ)) ^ E_tot := by
      have htc : Triples.card = R * (SmoothLe S Y).card * (SmoothLe S Y).card := by
        dsimp only [Triples]; rw [Finset.card_product, Finset.card_product, Nat.card_Icc]
        rw [show R + 1 - 1 = R by omega]; ring
      have hR_le : (R : ℝ) ≤ R_bd * (Real.log (X₀ : ℝ)) ^ E_Y := by
        have := hR_bd X₀ hX3; linarith
      have hRbd_nn : 0 ≤ R_bd := add_nonneg (div_nonneg hAY_pos.le hl2.le) zero_le_one
      have hlogX_nn : 0 ≤ Real.log (X₀ : ℝ) := by linarith
      have hRX_nn : 0 ≤ R_bd * (Real.log (X₀ : ℝ)) ^ E_Y :=
        mul_nonneg hRbd_nn (pow_nonneg hlogX_nn _)
      have hS_le : ((SmoothLe S Y).card : ℝ) ≤ (R_bd * (Real.log (X₀ : ℝ)) ^ E_Y) ^ S.card := by
        have h1 : ((SmoothLe S Y).card : ℝ) ≤ ((R : ℝ) + 1) ^ S.card := by
          exact_mod_cast smoothLe_card_le S hS Y
        exact le_trans h1 (pow_le_pow_left₀ (add_nonneg (Nat.cast_nonneg _) zero_le_one) (hR_bd X₀ hX3) S.card)
      have hprod : (Triples.card : ℝ) ≤ R_bd ^ (2 * S.card + 1) * (Real.log (X₀ : ℝ)) ^ (E_Y * (2 * S.card + 1)) := by
        rw [htc]; push_cast
        have hmul1 : (R : ℝ) * ((SmoothLe S Y).card : ℝ) * ((SmoothLe S Y).card : ℝ) ≤
            (R_bd * (Real.log (X₀ : ℝ)) ^ E_Y) *
              ((R_bd * (Real.log (X₀ : ℝ)) ^ E_Y) ^ S.card) *
              ((R_bd * (Real.log (X₀ : ℝ)) ^ E_Y) ^ S.card) :=
          mul_le_mul (mul_le_mul hR_le hS_le (Nat.cast_nonneg _) hRX_nn) hS_le (Nat.cast_nonneg _)
            (mul_nonneg hRX_nn (pow_nonneg hRX_nn _))
        have heq : (R_bd * (Real.log (X₀ : ℝ)) ^ E_Y) *
              ((R_bd * (Real.log (X₀ : ℝ)) ^ E_Y) ^ S.card) *
              ((R_bd * (Real.log (X₀ : ℝ)) ^ E_Y) ^ S.card) =
            R_bd ^ (2 * S.card + 1) * (Real.log (X₀ : ℝ)) ^ (E_Y * (2 * S.card + 1)) := by
          rw [show 2 * S.card + 1 = 1 + S.card + S.card by omega, pow_add, pow_add, pow_one,
            mul_pow, mul_add, mul_add, mul_one, pow_add, pow_add, ← pow_mul]
          ring
        exact le_trans hmul1 heq.le
      have hpow_le : (Real.log (X₀ : ℝ)) ^ (E_Y * (2 * S.card + 1)) ≤ (Real.log (X₀ : ℝ)) ^ E_tot :=
        pow_le_pow_right₀ hlogX1 (by dsimp only [E_tot]; omega)
      exact le_trans hprod (mul_le_mul_of_nonneg_left hpow_le (pow_nonneg hRbd_nn _))
    calc (BadUnion.card : ℝ)
        ≤ (Triples.card : ℝ) * (17 * (X₀ : ℝ) ^ (1 - ε)) := le_trans htri_sum hsum_le
      _ ≤ (R_bd ^ (2 * S.card + 1) * (Real.log (X₀ : ℝ)) ^ E_tot) * (17 * (X₀ : ℝ) ^ (1 - ε)) :=
          mul_le_mul_of_nonneg_right hT_card (mul_nonneg (by norm_num) (Real.rpow_nonneg hXpos.le _))
      _ = C_tot_bad * (Real.log (X₀ : ℝ)) ^ E_tot * (X₀ : ℝ) ^ (1 - ε) := by
          dsimp only [C_tot_bad]; ring
  have hlt_card : BadUnion.card < ((Finset.Ioc X₀ (4 * X₀)).filter Nat.Prime).card := by
    have : (BadUnion.card : ℝ) < (((Finset.Ioc X₀ (4 * X₀)).filter Nat.Prime).card : ℝ) :=
      lt_of_le_of_lt hBad_card (lt_of_lt_of_le hcmp hcheb)
    exact_mod_cast this
  obtain ⟨q, hq_sdiff⟩ : (((Finset.Ioc X₀ (4 * X₀)).filter Nat.Prime) \ BadUnion).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hsub : (Finset.Ioc X₀ (4 * X₀)).filter Nat.Prime ⊆ BadUnion := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have := Finset.card_le_card hsub
    omega
  rw [Finset.mem_sdiff, Finset.mem_filter] at hq_sdiff
  obtain ⟨⟨hq_Ioc, hq_pr⟩, hq_not_bad⟩ := hq_sdiff
  have hq_gt_S : ∀ p ∈ S, p < q := by
    intro p hpS
    have hp_le := Finset.le_max' S p hpS
    have hq_gt := (Finset.mem_Ioc.mp hq_Ioc).1
    omega
  have hq_not_S : q ∉ S := fun hmem => (hq_gt_S q hmem).false
  refine ⟨q, hq_pr, hq_gt_S, ?_⟩
  intro x y hx hy hxy hy2x
  have hS' : ∀ p ∈ insert q S, p.Prime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hpS
    · exact hq_pr
    · exact hS p hpS
  by_cases hyY : Y ≤ y
  · have hx_ge : Real.exp (L_fn X₀) ≤ (x : ℝ) := by
      have h1 : (2 * Real.exp (L_fn X₀) + 4 : ℝ) ≤ (Y : ℝ) := by
        have := Nat.le_ceil (2 * Real.exp (L_fn X₀))
        dsimp only [Y, Y_fn]; push_cast; linarith
      have h2 : (Y : ℝ) ≤ 2 * (x : ℝ) := by exact_mod_cast le_trans hyY hy2x
      linarith
    have hx_gt2 : (2 : ℝ) < (x : ℝ) := by
      have hL2 : (2 : ℝ) ≤ L_fn X₀ := le_max_left _ _
      have : 7 ≤ Real.exp 2 := by
        have h1 : (2.7 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith
      linarith [Real.exp_le_exp.mpr hL2]
    have hx_pos : (0 : ℝ) < (x : ℝ) := by linarith
    have hlogx_ge : L_fn X₀ ≤ Real.log (x : ℝ) := by
      rwa [Real.le_log_iff_exp_le hx_pos]
    have hcard_eq : (insert q S).card = n := Finset.card_insert_of_notMem hq_not_S
    have h2card : 2 ≤ (insert q S).card := by rw [hcard_eq]; dsimp only [n]; have := hS_ne.card_pos; omega
    have hs₀_card : ∀ s : ℕ, s₀ ≤ s → (2 * s) ^ ((insert q S).card + 1) ≤ 2 ^ s := by
      rw [hcard_eq]; exact hs₀_pow
    have hlogx_ge' : max 2 (max ((bf_C s₀ (insert q S).card (α_fn X₀) + 1) *
          Real.log (3 * bf_B₀ s₀ (insert q S).card (α_fn X₀)) / ε)
        (((8 * (bf_C s₀ (insert q S).card (α_fn X₀) + 1)) / ε) ^ 2)) ≤ Real.log (x : ℝ) := by
      rw [hcard_eq]; exact hlogx_ge
    exact bf_large_gap hε0 (insert q S) h2card hS' s₀ hs₀_card (α_fn X₀) (hα_ge1 X₀ hX3)
      (hα_sum X₀ hX3 q hq_Ioc) hx hy hxy hy2x hx_gt2 hlogx_ge'
  · push Not at hyY
    by_cases hyq : y < q
    · have hndvd_x : ¬ q ∣ x := fun hd => absurd (Nat.le_of_dvd hx.1 hd) (by omega)
      have hndvd_y : ¬ q ∣ y := fun hd => absurd (Nat.le_of_dvd hy.1 hd) (by omega)
      have hxS : x ∈ Erdos675.composedOf (S : Set ℕ) := ⟨hx.1, fun p hp hpd => by
        rcases Finset.mem_insert.mp (by simpa using hx.2 p hp hpd) with rfl | hpS
        · exact absurd hpd hndvd_x
        · exact hpS⟩
      have hyS : y ∈ Erdos675.composedOf (S : Set ℕ) := ⟨hy.1, fun p hp hpd => by
        rcases Finset.mem_insert.mp (by simpa using hy.2 p hp hpd) with rfl | hpS
        · exact absurd hpd hndvd_y
        · exact hpS⟩
      exact hGood x y hxS hyS hxy hy2x
    · push Not at hyq
      set rx := x.factorization q
      set ry := y.factorization q
      set r₀ := min rx ry
      have hqr0_x : q ^ r₀ ∣ x := (hq_pr.pow_dvd_iff_le_factorization hx.1.ne').mpr (min_le_left _ _)
      have hqr0_y : q ^ r₀ ∣ y := (hq_pr.pow_dvd_iff_le_factorization hy.1.ne').mpr (min_le_right _ _)
      set x₀ := x / q ^ r₀
      set y₀ := y / q ^ r₀
      have hx_eq : x = q ^ r₀ * x₀ := (Nat.mul_div_cancel' hqr0_x).symm
      have hy_eq : y = q ^ r₀ * y₀ := (Nat.mul_div_cancel' hqr0_y).symm
      have hqr0_pos : 0 < q ^ r₀ := pow_pos hq_pr.pos _
      have hx₀_pos : 0 < x₀ := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hx_eq; omega
      have hy₀_pos : 0 < y₀ := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hy_eq; omega
      have hx₀y₀ : x₀ < y₀ := by nlinarith
      have hy₀2x₀ : y₀ ≤ 2 * x₀ := by nlinarith
      have hy₀_lt_Y : y₀ < Y := lt_of_le_of_lt (Nat.div_le_self y _) hyY
      have hsub_eq : ((y - x : ℕ) : ℝ) = (q ^ r₀ : ℝ) * ((y₀ - x₀ : ℕ) : ℝ) := by
        have : y - x = q ^ r₀ * (y₀ - x₀) := by rw [hx_eq, hy_eq, ← Nat.mul_sub]
        rw [this]; push_cast; rfl
      have hqr0_ge1 : (1 : ℝ) ≤ (q ^ r₀ : ℝ) := by exact_mod_cast hqr0_pos
      have hqr0_rpow : (q ^ r₀ : ℝ) ^ (1 - ε) ≤ (q ^ r₀ : ℝ) := by
        calc (q ^ r₀ : ℝ) ^ (1 - ε) ≤ (q ^ r₀ : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hqr0_ge1 (by linarith)
          _ = (q ^ r₀ : ℝ) := Real.rpow_one _
      have hx_rpow : (x : ℝ) ^ (1 - ε) = (q ^ r₀ : ℝ) ^ (1 - ε) * (x₀ : ℝ) ^ (1 - ε) := by
        rw [hx_eq]; push_cast
        exact Real.mul_rpow (by positivity) (by positivity)
      have hlift : (x₀ : ℝ) ^ (1 - ε) ≤ ((y₀ - x₀ : ℕ) : ℝ) → (x : ℝ) ^ (1 - ε) ≤ ((y - x : ℕ) : ℝ) := by
        intro hgap0
        rw [hx_rpow, hsub_eq]
        exact mul_le_mul hqr0_rpow hgap0 (by positivity) (by positivity)
      apply hlift
      have hx₀_mem : ∀ p : ℕ, p.Prime → p ∣ x₀ → p ∈ insert q S := fun p hp hpd => by
        simpa using hx.2 p hp (dvd_trans hpd (by rw [hx_eq]; exact dvd_mul_left _ _))
      have hy₀_mem : ∀ p : ℕ, p.Prime → p ∣ y₀ → p ∈ insert q S := fun p hp hpd => by
        simpa using hy.2 p hp (dvd_trans hpd (by rw [hy_eq]; exact dvd_mul_left _ _))
      have hfac_x₀ : x₀.factorization q = rx - r₀ := by
        have h1 := Nat.factorization_mul hqr0_pos.ne' hx₀_pos.ne'
        rw [← hx_eq, hq_pr.factorization_pow] at h1
        have h2 := congrArg (fun f : ℕ →₀ ℕ => f q) h1
        simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at h2
        change rx = r₀ + x₀.factorization q at h2
        omega
      have hfac_y₀ : y₀.factorization q = ry - r₀ := by
        have h1 := Nat.factorization_mul hqr0_pos.ne' hy₀_pos.ne'
        rw [← hy_eq, hq_pr.factorization_pow] at h1
        have h2 := congrArg (fun f : ℕ →₀ ℕ => f q) h1
        simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at h2
        change ry = r₀ + y₀.factorization q at h2
        omega
      by_cases hreq : rx = ry
      · have hx₀_ndvd : ¬ q ∣ x₀ := by
          intro hd
          have := hq_pr.factorization_pos_of_dvd hx₀_pos.ne' hd
          omega
        have hy₀_ndvd : ¬ q ∣ y₀ := by
          intro hd
          have := hq_pr.factorization_pos_of_dvd hy₀_pos.ne' hd
          omega
        have hx₀S : x₀ ∈ Erdos675.composedOf (S : Set ℕ) := ⟨hx₀_pos, fun p hp hpd => by
          rcases Finset.mem_insert.mp (hx₀_mem p hp hpd) with rfl | hpS
          · exact absurd hpd hx₀_ndvd
          · exact hpS⟩
        have hy₀S : y₀ ∈ Erdos675.composedOf (S : Set ℕ) := ⟨hy₀_pos, fun p hp hpd => by
          rcases Finset.mem_insert.mp (hy₀_mem p hp hpd) with rfl | hpS
          · exact absurd hpd hy₀_ndvd
          · exact hpS⟩
        exact hGood x₀ y₀ hx₀S hy₀S hx₀y₀ hy₀2x₀
      · have hsmooth_of_ndvd : ∀ w : ℕ, 0 < w → w ≤ Y → ¬ q ∣ w →
            (∀ p : ℕ, p.Prime → p ∣ w → p ∈ insert q S) → w ∈ SmoothLe S Y := by
          intro w hw0 hwY hndvd hmem
          rw [SmoothLe, Finset.mem_filter, Finset.mem_Icc]
          refine ⟨⟨hw0, hwY⟩, fun p hp => ?_⟩
          have hp_pr := Nat.prime_of_mem_primeFactors hp
          have hp_dv := Nat.dvd_of_mem_primeFactors hp
          rcases Finset.mem_insert.mp (hmem p hp_pr hp_dv) with rfl | hpS
          · exact absurd hp_dv hndvd
          · exact hpS
        have hpair : ∃ r u v : ℕ, r ∈ Finset.Icc 1 R ∧ u ∈ SmoothLe S Y ∧ v ∈ SmoothLe S Y ∧
            ((x₀ = u ∧ y₀ = v * q ^ r) ∨ (x₀ = v * q ^ r ∧ y₀ = u)) := by
          rcases lt_or_gt_of_ne hreq with hlt | hgt
          · have hr₀_eq : r₀ = rx := min_eq_left hlt.le
            have hx₀_ndvd : ¬ q ∣ x₀ := fun hd => by
              have := hq_pr.factorization_pos_of_dvd hx₀_pos.ne' hd; omega
            set r := ry - rx
            have hr1 : 1 ≤ r := by omega
            have hqr_dvd : q ^ r ∣ y₀ :=
              (hq_pr.pow_dvd_iff_le_factorization hy₀_pos.ne').mpr (by omega)
            set v := y₀ / q ^ r
            have hv_pos : 0 < v := Nat.pos_of_ne_zero fun h0 => by
              have := Nat.mul_div_cancel' hqr_dvd
              change q ^ r * v = y₀ at this
              rw [h0, mul_zero] at this
              omega
            have hy₀_eq : y₀ = v * q ^ r := by rw [mul_comm, Nat.mul_div_cancel' hqr_dvd]
            have hv_ndvd : ¬ q ∣ v := fun hd => by
              have h1 : q ^ (r + 1) ∣ y₀ := by
                rw [hy₀_eq, pow_succ]; obtain ⟨t, ht⟩ := hd; rw [ht]; exact ⟨t, by ring⟩
              have h2 := (hq_pr.pow_dvd_iff_le_factorization hy₀_pos.ne').mp h1
              omega
            have hr_le : r ≤ R := by
              have h2r : 2 ^ r ≤ Y := by
                have h1 : 2 ^ r ≤ q ^ r := Nat.pow_le_pow_left hq_pr.two_le r
                have h2 : q ^ r ≤ v * q ^ r := Nat.le_mul_of_pos_left _ hv_pos
                omega
              exact Nat.le_log_of_pow_le (by norm_num) h2r
            refine ⟨r, x₀, v, Finset.mem_Icc.mpr ⟨hr1, hr_le⟩,
              hsmooth_of_ndvd x₀ hx₀_pos (by omega) hx₀_ndvd hx₀_mem,
              hsmooth_of_ndvd v hv_pos (by have : v ≤ v * q ^ r := Nat.le_mul_of_pos_right _ (pow_pos hq_pr.pos _); omega)
                hv_ndvd (fun p hp hpd => hy₀_mem p hp (dvd_trans hpd (by rw [hy₀_eq]; exact dvd_mul_right _ _))),
              Or.inl ⟨rfl, hy₀_eq⟩⟩
          · have hr₀_eq : r₀ = ry := min_eq_right hgt.le
            have hy₀_ndvd : ¬ q ∣ y₀ := fun hd => by
              have := hq_pr.factorization_pos_of_dvd hy₀_pos.ne' hd; omega
            set r := rx - ry
            have hr1 : 1 ≤ r := by omega
            have hqr_dvd : q ^ r ∣ x₀ :=
              (hq_pr.pow_dvd_iff_le_factorization hx₀_pos.ne').mpr (by omega)
            set v := x₀ / q ^ r
            have hv_pos : 0 < v := Nat.pos_of_ne_zero fun h0 => by
              have := Nat.mul_div_cancel' hqr_dvd
              change q ^ r * v = x₀ at this
              rw [h0, mul_zero] at this
              omega
            have hx₀_eq : x₀ = v * q ^ r := by rw [mul_comm, Nat.mul_div_cancel' hqr_dvd]
            have hv_ndvd : ¬ q ∣ v := fun hd => by
              have h1 : q ^ (r + 1) ∣ x₀ := by
                rw [hx₀_eq, pow_succ]; obtain ⟨t, ht⟩ := hd; rw [ht]; exact ⟨t, by ring⟩
              have h2 := (hq_pr.pow_dvd_iff_le_factorization hx₀_pos.ne').mp h1
              omega
            have hr_le : r ≤ R := by
              have h2r : 2 ^ r ≤ Y := by
                have h1 : 2 ^ r ≤ q ^ r := Nat.pow_le_pow_left hq_pr.two_le r
                have h2 : q ^ r ≤ v * q ^ r := Nat.le_mul_of_pos_left _ hv_pos
                omega
              exact Nat.le_log_of_pow_le (by norm_num) h2r
            refine ⟨r, y₀, v, Finset.mem_Icc.mpr ⟨hr1, hr_le⟩,
              hsmooth_of_ndvd y₀ hy₀_pos (by omega) hy₀_ndvd hy₀_mem,
              hsmooth_of_ndvd v hv_pos (by have : v ≤ v * q ^ r := Nat.le_mul_of_pos_right _ (pow_pos hq_pr.pos _); omega)
                hv_ndvd (fun p hp hpd => hx₀_mem p hp (dvd_trans hpd (by rw [hx₀_eq]; exact dvd_mul_right _ _))),
              Or.inr ⟨hx₀_eq, rfl⟩⟩
        obtain ⟨r, u, v, hr_mem, hu_mem, hv_mem, hcases⟩ := hpair
        have hnot_badQ : q ∉ BadQ X₀ ε r u v := by
          intro hbad
          apply hq_not_bad
          exact Finset.mem_biUnion.mpr ⟨(r, u, v), Finset.mem_product.mpr ⟨hr_mem, Finset.mem_product.mpr ⟨hu_mem, hv_mem⟩⟩, hbad⟩
        rw [BadQ, Finset.mem_filter] at hnot_badQ
        push Not at hnot_badQ
        have hgood_q := hnot_badQ hq_Ioc
        rcases hcases with ⟨hx₀_eq', hy₀_eq'⟩ | ⟨hx₀_eq', hy₀_eq'⟩
        · have hyR : (v : ℝ) * (q : ℝ) ^ r = (y₀ : ℝ) := by exact_mod_cast hy₀_eq'.symm
          have hxR : (u : ℝ) = (x₀ : ℝ) := by exact_mod_cast hx₀_eq'.symm
          rw [hyR, hxR] at hgood_q
          have hmax_eq : max (y₀ : ℝ) (x₀ : ℝ) = (y₀ : ℝ) :=
            max_eq_left (by exact_mod_cast hx₀y₀.le)
          have habs_eq : |(y₀ : ℝ) - (x₀ : ℝ)| = ((y₀ - x₀ : ℕ) : ℝ) := by
            rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hx₀y₀.le)),
              Nat.cast_sub hx₀y₀.le]
          rw [hmax_eq, habs_eq] at hgood_q
          have hxpow : (x₀ : ℝ) ^ (1 - ε) ≤ (y₀ : ℝ) ^ (1 - ε) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hx₀y₀.le) (by linarith)
          exact le_trans hxpow hgood_q
        · have hxR : (v : ℝ) * (q : ℝ) ^ r = (x₀ : ℝ) := by exact_mod_cast hx₀_eq'.symm
          have hyR : (u : ℝ) = (y₀ : ℝ) := by exact_mod_cast hy₀_eq'.symm
          rw [hxR, hyR] at hgood_q
          have hmax_eq : max (x₀ : ℝ) (y₀ : ℝ) = (y₀ : ℝ) :=
            max_eq_right (by exact_mod_cast hx₀y₀.le)
          have habs_eq : |(x₀ : ℝ) - (y₀ : ℝ)| = ((y₀ - x₀ : ℕ) : ℝ) := by
            rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hx₀y₀.le)),
              Nat.cast_sub hx₀y₀.le]
            ring
          rw [hmax_eq, habs_eq] at hgood_q
          have hxpow : (x₀ : ℝ) ^ (1 - ε) ≤ (y₀ : ℝ) ^ (1 - ε) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hx₀y₀.le) (by linarith)
          exact le_trans hxpow hgood_q

end BakerFeldman

theorem OMA.solution : type_of% @Erdos240.erdos_240.variants.tijdeman_epsilon := by
  open Filter Asymptotics BakerFeldman in
  intro ε hε
  by_cases hε1 : 1 ≤ ε
  · refine ⟨{p : ℕ | p.Prime}, Nat.infinite_setOfPred_prime, fun _ h => h, ?_⟩
    have hne : ({p : ℕ | p.Prime} : Set ℕ).Nonempty := ⟨2, Nat.prime_two⟩
    obtain ⟨hmono, hmem, _⟩ := smooth_H2 {p : ℕ | p.Prime} hne (fun _ h => h)
    refine IsBigO.of_bound 1 ?_
    refine Eventually.of_forall fun i => ?_
    have hxy : Erdos240.a {p : ℕ | p.Prime} i < Erdos240.a {p : ℕ | p.Prime} (i + 1) :=
      hmono (Nat.lt_succ_self i)
    have hx1 : (1 : ℝ) ≤ (Erdos240.a {p : ℕ | p.Prime} i : ℝ) := by exact_mod_cast (hmem i).1
    have hgap1 : (1 : ℝ) ≤ ((Erdos240.a {p : ℕ | p.Prime} (i + 1) - Erdos240.a {p : ℕ | p.Prime} i : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ Erdos240.a {p : ℕ | p.Prime} (i + 1) - Erdos240.a {p : ℕ | p.Prime} i by omega)
    have hpow1 : (Erdos240.a {p : ℕ | p.Prime} i : ℝ) ^ (1 - ε) ≤ 1 := by
      calc (Erdos240.a {p : ℕ | p.Prime} i : ℝ) ^ (1 - ε)
          ≤ (Erdos240.a {p : ℕ | p.Prime} i : ℝ) ^ (0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
        _ = 1 := Real.rpow_zero _
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul]
    linarith
  · push Not at hε1
    let State := { S : Finset ℕ // 2 ∈ S ∧ (∀ p ∈ S, p.Prime) ∧ GoodGap S (1 - ε) } × ℕ
    let nextStep : State → State := fun prev =>
      let S := prev.1.1
      let h2 := prev.1.2.1
      let hS := prev.1.2.2.1
      let hG := prev.1.2.2.2
      let hne := exists_next_prime hε hε1 S h2 hS hG
      let q := Classical.choose hne
      let hq := Classical.choose_spec hne
      (⟨insert q S, Finset.mem_insert_of_mem h2,
        fun p hp => by rcases Finset.mem_insert.mp hp with rfl | hpS; exact hq.1; exact hS p hpS,
        hq.2.2⟩, q)
    let stepFn : ℕ → State := Nat.rec
      (⟨{2}, Finset.mem_singleton_self 2, fun p hp => by simp only [Finset.mem_singleton] at hp; rw [hp]; exact Nat.prime_two,
        goodGap_two hε hε1⟩, 2)
      (fun _ prev => nextStep prev)
    let p_seq : ℕ → ℕ := fun k => (stepFn k).2
    have hp_mem : ∀ k : ℕ, p_seq k ∈ (stepFn k).1.1 := by
      intro k
      cases k with
      | zero => exact Finset.mem_singleton_self 2
      | succ k => exact Finset.mem_insert_self _ _
    have hp_sub : ∀ k : ℕ, (stepFn k).1.1 ⊆ (stepFn (k + 1)).1.1 := fun k _ h =>
      Finset.mem_insert_of_mem h
    have nextStep_lt : ∀ prev : State, ∀ r ∈ prev.1.1, r < (nextStep prev).2 := by
      intro prev r hr
      dsimp only [nextStep]
      exact (Classical.choose_spec (exists_next_prime hε hε1 prev.1.1 prev.1.2.1 prev.1.2.2.1 prev.1.2.2.2)).2.1 r hr
    have hp_lt : ∀ k : ℕ, ∀ r ∈ (stepFn k).1.1, r < p_seq (k + 1) :=
      fun k r hr => nextStep_lt (stepFn k) r hr
    have hp_mono : StrictMono p_seq := by
      refine strictMono_nat_of_lt_succ fun k => ?_
      exact hp_lt k (p_seq k) (hp_mem k)
    have hmem_of_lt : ∀ k j : ℕ, j ≤ k → p_seq j ∈ (stepFn k).1.1 := by
      intro k
      induction k with
      | zero =>
        intro j hj
        have hj0 : j = 0 := by omega
        rw [hj0]
        exact hp_mem 0
      | succ k ih =>
        intro j hj
        rcases eq_or_lt_of_le hj with rfl | hlt
        · exact hp_mem (k + 1)
        · exact hp_sub k (ih j (by omega))
    let P : Set ℕ := Set.range p_seq
    have hP_inf : P.Infinite := Set.infinite_range_of_injective hp_mono.injective
    have hP_pr : P ⊆ {p : ℕ | p.Prime} := by
      rintro p ⟨k, rfl⟩
      exact (stepFn k).1.2.2.1 (p_seq k) (hp_mem k)
    have hP_ne : P.Nonempty := ⟨2, ⟨0, rfl⟩⟩
    have h2P : 2 ∈ P := ⟨0, rfl⟩
    obtain ⟨hmono, hmem, hstep⟩ := smooth_H2 P hP_ne hP_pr
    refine ⟨P, hP_inf, hP_pr, IsBigO.of_bound 1 (Eventually.of_forall fun i => ?_)⟩
    set x := Erdos240.a P i
    set y := Erdos240.a P (i + 1)
    have hxy : x < y := hmono (Nat.lt_succ_self i)
    have hy2x : y ≤ 2 * x := hstep 2 h2P i
    have hx_mem := hmem i
    have hy_mem := hmem (i + 1)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, y < p_seq k := by
      have := hp_mono.tendsto_atTop.eventually (eventually_gt_atTop y)
      rw [Filter.eventually_atTop] at this
      obtain ⟨k, hk⟩ := this
      exact ⟨k, hk k le_rfl⟩
    have h_in_Sk : ∀ w : ℕ, w ∈ Erdos675.composedOf P → w ≤ y → w ∈ Erdos675.composedOf ((stepFn k).1.1 : Set ℕ) := by
      intro w hw hwy
      refine ⟨hw.1, fun r hr hrd => ?_⟩
      obtain ⟨j, hj⟩ := hw.2 r hr hrd
      have hrl : r ≤ y := le_trans (Nat.le_of_dvd hw.1 hrd) hwy
      have hjk : j < k := by
        by_contra hkj
        push Not at hkj
        have hle := hp_mono.monotone hkj
        omega
      rw [← hj]
      exact hmem_of_lt k j hjk.le
    have hgap := (stepFn k).1.2.2.2 x y (h_in_Sk x hx_mem hxy.le) (h_in_Sk y hy_mem le_rfl) hxy hy2x
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul]
    exact hgap

