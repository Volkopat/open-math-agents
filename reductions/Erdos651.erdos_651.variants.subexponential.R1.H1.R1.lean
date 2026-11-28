import OMAReductions.R_Erdos651_erdos_651_variants_subexponential_R1
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Sum

-- Credit: @LordMike
-- Port of reductions/Erdos651.erdos_651.R1.H1.R1.lean by its author onto the identical hypothesis statement Erdos651.erdos_651.variants.subexponential.R1.H1.

/-!
Split the three-dimensional argument of Pohoata and Zakharov into extraction
of compatible clusters and the local cups-versus-caps theorem. Taking the
number of clusters fixed lets the extraction use a fixed size threshold.

Source: https://arxiv.org/abs/2208.04878, Proposition 2.1 and Section 3.
Credit: @justusklocke-cloud
-/

open Filter Erdos651
open scoped EuclideanGeometry BigOperators

namespace OMA.R_Erdos651_erdos_651_variants_subexponential_R1_H1_R1

/-- A weighted binomial estimate for the dimension-three construction. -/
private theorem binomial_bound (t n : ℕ) (ht : 2 ≤ t) (hn : t ≤ n) :
    let a := n / t + 1
    (((n + a).choose a : ℕ) : ℝ) ^ 12 ≤ (t : ℝ) ^ ((72 : ℝ) * n / t) := by
  let a := n / t + 1
  let b : ℝ := (n + a).choose a
  change b ^ 12 ≤ (t : ℝ) ^ ((72 : ℝ) * n / t)
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hnR : (t : ℝ) ≤ n := by exact_mod_cast hn
  have htpos : 0 < (t : ℝ) := by linarith
  have hb : 0 < b := by
    dsimp [b]
    exact_mod_cast Nat.choose_pos (Nat.le_add_left a n)
  have hdiv : ((n / t : ℕ) : ℝ) ≤ (n : ℝ) / t := by
    apply (le_div_iff₀ htpos).mpr
    exact_mod_cast Nat.div_mul_le_self n t
  have hratio : 1 ≤ (n : ℝ) / t := by
    exact (le_div_iff₀ htpos).mpr (by simpa using hnR)
  have haR : (a : ℝ) ≤ 2 * ((n : ℝ) / t) := by
    dsimp [a]
    push_cast
    linarith
  have ha : a ≤ n := Nat.succ_le_of_lt (Nat.div_lt_self (by omega) (by omega))
  have hNR : (n : ℝ) + a ≤ 2 * n := by
    have ha' : (a : ℝ) ≤ n := by exact_mod_cast ha
    linarith
  have hweighted : b * (t : ℝ) ^ n ≤ (1 + (t : ℝ)) ^ (n + a) := by
    rw [add_pow]
    have hterm := Finset.single_le_sum
      (f := fun j => (1 : ℝ) ^ j * (t : ℝ) ^ (n + a - j) * ((n + a).choose j : ℝ))
      (fun j _ => by positivity)
      (Finset.mem_range.mpr (show a < n + a + 1 by omega))
    simpa [b, mul_comm ((t : ℝ) ^ n)] using hterm
  have hlog := Real.log_le_log (mul_pos hb (pow_pos htpos n)) hweighted
  have hbase : 0 < 1 + (1 : ℝ) / t := by positivity
  have hsplit : Real.log (1 + (t : ℝ)) = Real.log (t : ℝ) + Real.log (1 + (1 : ℝ) / t) := by
    rw [← Real.log_mul htpos.ne' hbase.ne']
    congr 1
    field_simp
    ring
  rw [Real.log_mul hb.ne' (pow_ne_zero _ htpos.ne'), Real.log_pow, Real.log_pow, hsplit,
    Nat.cast_add] at hlog
  have hsmall : Real.log (1 + (1 : ℝ) / t) ≤ (1 : ℝ) / t := by
    linarith [Real.log_le_sub_one_of_pos hbase]
  have hmain : Real.log b ≤ (a : ℝ) * Real.log (t : ℝ) + ((n : ℝ) + a) / t := by
    have hterm := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ (n : ℝ) + a by positivity)
    rw [mul_one_div] at hterm
    linarith only [hlog, hterm]
  have hhalf : (1 / 2 : ℝ) ≤ Real.log (t : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)⁻¹) (by norm_num)
    rw [Real.log_inv] at h
    exact (show (1 / 2 : ℝ) ≤ Real.log 2 by linarith).trans (Real.log_le_log (by norm_num) htR)
  have hscaled : Real.log b ≤ 6 * ((n : ℝ) / t) * Real.log (t : ℝ) := by
    have hlogterm := mul_le_mul_of_nonneg_right haR (show 0 ≤ Real.log (t : ℝ) by linarith)
    have hsum := div_le_div_of_nonneg_right hNR htpos.le
    rw [mul_div_assoc] at hsum
    have hcost := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 4 * ((n : ℝ) / t) by positivity)
    linarith only [hmain, hlogterm, hsum, hcost]
  apply (Real.log_le_log_iff (pow_pos hb _) (Real.rpow_pos_of_pos htpos _)).mp
  rw [Real.log_pow, Real.log_rpow htpos, mul_div_assoc]
  norm_num
  linarith only [hscaled]

/-- Compatible caps give an `n`-element subset in convex position. -/
private theorem cap_glue {t n : ℕ} (ht : 0 < t) (X : Finset (ℝ^3))
    (K : Fin t → Finset (ℝ^3)) (P : Fin t → Set (ℝ^3))
    (hKX : ∀ i, K i ⊆ X) (hKcard : ∀ i, (K i).card = n / t + 1)
    (hKconvex : ∀ i x, x ∈ K i →
      x ∉ convexHull ℝ (P i ∪ ((K i).erase x : Set (ℝ^3))))
    (hKpair : ∀ i j, i ≠ j → Disjoint (K i) (K j) ∧ (K j : Set (ℝ^3)) ⊆ P i) :
    Erdos651.HasConvexSubset n X := by
  classical
  let U := Finset.univ.biUnion K
  have hUX : U ⊆ X := by
    intro x hx
    obtain ⟨i, -, hxi⟩ := Finset.mem_biUnion.mp hx
    exact hKX i hxi
  have hUcard : U.card = t * (n / t + 1) := by
    have hdisj : ((Finset.univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint K := by
      intro i _ j _ hij
      exact (hKpair i j hij).1
    change (Finset.univ.biUnion K).card = _
    rw [Finset.card_biUnion hdisj]
    simp [hKcard]
  have hcard : n ≤ U.card := by
    rw [hUcard]
    calc
      n = t * (n / t) + n % t := (Nat.div_add_mod n t).symm
      _ ≤ t * (n / t) + t := Nat.add_le_add_left (Nat.mod_lt n ht).le _
      _ = t * (n / t + 1) := by rw [Nat.mul_add, Nat.mul_one]
  obtain ⟨Y, hYU, hYcard⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨Y, hYU.trans hUX, hYcard, ?_⟩
  rw [convexIndependent_set_iff_notMem_convexHull_sdiff]
  intro x hx hmem
  obtain ⟨i, -, hxi⟩ := Finset.mem_biUnion.mp (hYU hx)
  apply hKconvex i x hxi
  refine convexHull_mono ?_ hmem
  intro y hy
  obtain ⟨j, -, hyj⟩ := Finset.mem_biUnion.mp (hYU hy.1)
  by_cases hij : i = j
  · subst j
    exact Or.inr (Finset.mem_erase.mpr ⟨fun h => hy.2 (Set.mem_singleton_iff.mpr h), hyj⟩)
  · exact Or.inl ((hKpair i j hij).2 hyj)

/-- The cluster extraction preceding the local cups-versus-caps step in Section 3. -/
def H1 : Prop :=
  ∀ t : ℕ, 2 ≤ t → ∃ B : ℕ, ∀ X : Finset (ℝ^3),
    IsInGeneralPosition X → B ≤ X.card →
    ∃ (Y : Fin t → Finset (ℝ^3)) (P : Fin t → Set (ℝ^3)),
      (∀ i, Y i ⊆ X ∧ X.card ≤ (Y i).card ^ 4 ∧
        (∃ e : (ℝ^3) ≃ᵃ[ℝ] (ℝ^3), P i = {x | ∀ j : Fin 3, e x j ≤ 0} ∧
          ∀ (j : Fin 3) (Z : Finset (ℝ^3)), Z ⊆ Y i → Z.card ≤ 3 →
            AffineIndependent ℝ
              (fun x : ↥(Z : Set (ℝ^3)) => fun k : Fin 2 => e x (j.succAbove k))) ∧
        (∀ x ∈ Y i, ∀ y ∈ Y i, x ≠ y → Disjoint (line[ℝ, x, y] : Set (ℝ^3)) (P i))) ∧
      ∀ i j, i ≠ j → Disjoint (Y i) (Y j) ∧ (Y j : Set (ℝ^3)) ⊆ P i

/-- The three-faced case of Proposition 2.1, with a relaxed binomial threshold. -/
def H2 : Prop :=
  ∀ (P : Set (ℝ^3)) (Y : Finset (ℝ^3)) (a n : ℕ),
    (∃ e : (ℝ^3) ≃ᵃ[ℝ] (ℝ^3), P = {x | ∀ j : Fin 3, e x j ≤ 0} ∧
      ∀ (j : Fin 3) (Z : Finset (ℝ^3)), Z ⊆ Y → Z.card ≤ 3 →
        AffineIndependent ℝ
          (fun x : ↥(Z : Set (ℝ^3)) => fun k : Fin 2 => e x (j.succAbove k))) →
    IsInGeneralPosition Y →
    (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → Disjoint (line[ℝ, x, y] : Set (ℝ^3)) P) →
    2 ≤ a → 2 ≤ n → ((n + a).choose a) ^ 3 < Y.card →
    HasConvexSubset n Y ∨ ∃ K ⊆ Y, K.card = a ∧
      ∀ x ∈ K, x ∉ convexHull ℝ (P ∪ (K.erase x : Set (ℝ^3)))

theorem main : H1 → H2 → OMA.R_Erdos651_erdos_651_variants_subexponential_R1.H1 := by
  classical
  intro hclusters hcups ε hε
  have htlim : Tendsto (fun t : ℕ => Real.log t / (t : ℝ)) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he := htlim.eventually_lt_const (show 0 < Real.log 2 * (ε / 2) / 72 by positivity)
  obtain ⟨t, hcoef, ht⟩ := (he.and (eventually_ge_atTop 2)).exists
  have ht0 : 0 < t := by omega
  have htR : (0 : ℝ) < t := by exact_mod_cast ht0
  have hcoeff : Real.log t * 72 / t ≤ Real.log 2 * (ε / 2) := by
    have h := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 72)).mp hcoef
    calc
      _ = (Real.log t / (t : ℝ)) * 72 := by ring
      _ ≤ _ := h.le
  obtain ⟨B, hB⟩ := hclusters t ht
  have hlimit : Tendsto (fun n : ℕ => (2 : ℝ) ^ (ε / 2 * (n : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num)).comp
      (Tendsto.const_mul_atTop (by positivity : 0 < ε / 2) tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop t, hlimit.eventually_ge_atTop (B : ℝ),
    hlimit.eventually_ge_atTop (2 : ℝ)] with n hnt hBR htwo
  let a := n / t + 1
  let M := (n + a).choose a
  let R := (2 : ℝ) ^ (ε / 2 * (n : ℝ))
  have hM : (M : ℝ) ^ 12 ≤ R := by
    refine (binomial_bound t n ht hnt).trans ?_
    dsimp only [R]
    rw [Real.rpow_def_of_pos htR, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    calc
      _ = (Real.log t * 72 / t) * n := by ring
      _ ≤ (Real.log 2 * (ε / 2)) * n :=
        mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg n)
      _ = _ := by ring
  let N := ⌊R⌋₊ + 1
  have hN : N ∈ cardSet 3 n := by
    intro X hgen hsize
    have hXR : R < (X.card : ℝ) := by
      have hNcast : (N : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast hsize
      exact (Nat.lt_floor_add_one R).trans_le (by simpa only [N, Nat.cast_add, Nat.cast_one] using hNcast)
    have hXB : B ≤ X.card := by exact_mod_cast hBR.trans hXR.le
    obtain ⟨Y, P, hY, hpair⟩ := hB X hgen hXB
    by_contra hbad
    have hbig : M ^ 12 < X.card := by exact_mod_cast hM.trans_lt hXR
    have ha : 2 ≤ a := by
      have hq : 1 ≤ n / t := (Nat.le_div_iff_mul_le ht0).mpr (by simpa using hnt)
      omega
    have hEvery (i : Fin t) : ∃ K ⊆ Y i, K.card = a ∧
        ∀ x ∈ K, x ∉ convexHull ℝ (P i ∪ (K.erase x : Set (ℝ^3))) := by
      obtain ⟨hsub, hcard, hcone, hfree⟩ := hY i
      have hgenY : IsInGeneralPosition (Y i) :=
        fun Z hZY hZ => hgen Z (hZY.trans hsub) hZ
      have hlarge : M ^ 3 < (Y i).card := by
        by_contra! hsmall
        have hpow := Nat.pow_le_pow_left hsmall 4
        rw [← pow_mul] at hpow
        exact (not_lt_of_ge (hcard.trans hpow)) hbig
      rcases hcups (P i) (Y i) a n hcone hgenY hfree ha (ht.trans hnt) hlarge with
        hconvex | hcap
      · obtain ⟨Z, hZY, hZcard, hZ⟩ := hconvex
        exact (hbad ⟨Z, hZY.trans hsub, hZcard, hZ⟩).elim
      · exact hcap
    choose K hKY hKsize hKconvex using hEvery
    apply hbad
    refine cap_glue ht0 X K P (fun i => (hKY i).trans (hY i).1) hKsize hKconvex ?_
    intro i j hij
    obtain ⟨hd, hp⟩ := hpair i j hij
    exact ⟨hd.mono (hKY i) (hKY j), fun x hx => hp (hKY j hx)⟩
  have hRnonneg : 0 ≤ R := Real.rpow_nonneg (by norm_num) _
  calc
    (f 3 n : ℝ) ≤ N := by exact_mod_cast f_le hN
    _ ≤ R + 1 := by
      dsimp only [N]
      push_cast
      linarith [Nat.floor_le hRnonneg]
    _ ≤ R * R := by
      have hmul := mul_le_mul_of_nonneg_right htwo hRnonneg
      linarith
    _ = _ := by
      dsimp only [R]
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring

end OMA.R_Erdos651_erdos_651_variants_subexponential_R1_H1_R1
