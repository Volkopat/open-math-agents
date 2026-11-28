import OMAStatements.S_mo_138395

open scoped BigOperators

/-!
For a nonnegative geometric mass vector m of total mass K, the scaled entropy is
K times the unnormalized entropy of m minus K times the entropy of the one mass K.
The deficit is concave under mass rescaling at fixed overlap, so three atoms suffice.
On three atoms, bounded surprisal variance rules out a negative interior minimum
along a line preserving the endpoint masses. The remaining binary case follows
from convexity and slope bounds in log odds.
-/

section BridgeSection

open scoped BigOperators
open Finset

namespace EntropyBridge

noncomputable def entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

noncomputable def geom (x y a : ℝ) : ℝ :=
  x ^ a * y ^ (1 - a)

lemma geom_smul (q x y a : ℝ) (hq : 0 ≤ q) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ha : 0 ≤ a) (hb : 0 ≤ 1-a) :
    geom (q*x) (q*y) a = q * geom x y a := by
  unfold geom
  rw [Real.mul_rpow hq hx, Real.mul_rpow hq hy]
  have h := Real.rpow_add_of_nonneg hq ha hb
  rw [show a + (1-a) = 1 by ring, Real.rpow_one] at h
  calc
    _ = (q^a * q^(1-a)) * (x^a * y^(1-a)) := by ring
    _ = _ := by rw [← h]

lemma scaled_entropy_identity {ι : Type*} [Fintype ι] (m : ι → ℝ) {K : ℝ}
    (hK : K ≠ 0) (hs : ∑ i, m i = K) :
    K^2 * entropy (fun i => m i / K) = K * entropy m - K * Real.negMulLog K := by
  have hn : ∑ i, m i / K = 1 := by rw [← Finset.sum_div, hs, div_self hK]
  have ht : entropy m = K * entropy (fun i => m i / K) + Real.negMulLog K := by
    unfold entropy
    calc
      (∑ i, Real.negMulLog (m i)) =
          ∑ i, ((m i / K) * Real.negMulLog K + K * Real.negMulLog (m i / K)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Real.negMulLog_mul]
        congr 1
        field_simp
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hn, one_mul]
        ring
  rw [ht]
  ring

lemma affinity_le_one {ι : Type*} [Fintype ι] (x y : ι → ℝ) {a : ℝ}
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) (hsx : ∑ i, x i = 1)
    (hsy : ∑ i, y i = 1) (ha : 0 ≤ a) (hb : 0 ≤ 1-a) :
    ∑ i, geom (x i) (y i) a ≤ 1 := by
  calc
    _ ≤ (∑ i, (a * x i + (1-a) * y i)) :=
      Finset.sum_le_sum fun i _ =>
        Real.geom_mean_le_arith_mean2_weighted ha hb (hx i) (hy i) (by ring)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsx, hsy]
      ring

lemma sparse_minimum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → Fin 3 → ℝ) (C A : ι → ℝ) (hC : ∀ i, 0 < C i)
    (hv : ∀ i, v i 0 = 1) (b : Fin 3 → ℝ)
    (b0 : b 0 = 2) (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hqb : (∑ i, q i • v i) = b) :
    ∃ p : ι → ℝ, (∀ i, 0 ≤ p i) ∧ ((∑ i, p i • v i) = b) ∧
      (univ.filter (fun i => 0 < p i)).card ≤ 3 ∧
      (∑ i, (C i * Real.negMulLog (p i) + A i * p i)) ≤
        ∑ i, (C i * Real.negMulLog (q i) + A i * q i) := by
  classical
  let L (p : ι → ℝ) : Fin 3 → ℝ := ∑ i, p i • v i
  let F (p : ι → ℝ) : ℝ := ∑ i, (C i * Real.negMulLog (p i) + A i * p i)
  let S := Set.Icc (0 : ι → ℝ) (fun _ => (2 : ℝ)) ∩ {p | L p = b}
  have mass (p : ι → ℝ) (hp : L p = b) : ∑ i, p i = 2 := by
    have h := congrFun hp (0 : Fin 3)
    simpa [L, Finset.sum_apply, hv, b0] using h
  have mem (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp : L p = b) : p ∈ S := by
    refine ⟨⟨hp0, fun i => ?_⟩, hp⟩
    rw [← mass p hp]
    exact Finset.single_le_sum (fun j _ => hp0 j) (mem_univ i)
  have hL : Continuous L := by
    unfold L
    fun_prop
  have hF : Continuous F := by
    unfold F
    fun_prop
  have hS : IsCompact S := isCompact_Icc.inter_right (isClosed_singleton.preimage hL)
  obtain ⟨p, hp, hmin⟩ := hS.exists_isMinOn ⟨q, mem q hq hqb⟩ hF.continuousOn
  have hp0 : ∀ i, 0 ≤ p i := hp.1.1
  have hpb : L p = b := hp.2
  refine ⟨p, hp0, hpb, ?_, hmin (mem q hq hqb)⟩
  by_contra! hlarge
  let T := univ.filter (fun i => 0 < p i)
  have hpos (i : T) : 0 < p i := (mem_filter.mp i.2).2
  have hdep : ¬ LinearIndependent ℝ (fun i : T => v i) := by
    intro hi
    have h := hi.fintype_card_le_finrank
    have h' : T.card ≤ 3 := by simpa [Module.finrank_fintype_fun_eq_card] using h
    exact (not_le_of_gt hlarge) h'
  obtain ⟨e, he, i, hei⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let d : ι → ℝ := fun j => if h : j ∈ T then e ⟨j,h⟩ else 0
  have hd : L d = 0 := by
    change (∑ j, d j • v j) = 0
    have hsum : (∑ j, d j • v j) = ∑ j ∈ T, d j • v j := by
      symm
      exact Finset.sum_subset (subset_univ _) (fun j _ hj => by simp [d, hj])
    rw [hsum, ← Finset.sum_finset_coe]
    simpa [d] using he
  obtain ⟨j, hj, hjmin⟩ := T.exists_min_image
    (fun j => p j / (1 + |d j|)) ⟨i, i.2⟩
  let ε := p j / (1 + |d j|)
  have hε : 0 < ε := div_pos (hpos ⟨j,hj⟩) (by positivity)
  have hbound (j : ι) : ε * |d j| ≤ p j := by
    by_cases hj : j ∈ T
    · have h := (le_div_iff₀ (by positivity : 0 < 1 + |d j|)).mp (hjmin j hj)
      change ε * (1 + |d j|) ≤ p j at h
      linarith
    · simpa [d, hj] using hp0 j
  let u : ι → ℝ := fun j => p j + ε * d j
  let w : ι → ℝ := fun j => p j - ε * d j
  have hu (j : ι) : 0 ≤ u j := by
    dsimp [u]
    have h := mul_le_mul_of_nonneg_left (neg_abs_le (d j)) hε.le
    linarith [hbound j]
  have hw (j : ι) : 0 ≤ w j := by
    dsimp [w]
    have h := mul_le_mul_of_nonneg_left (le_abs_self (d j)) hε.le
    linarith [hbound j]
  have huL : L u = b := by
    simp only [L, u, add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
    change L p + ε • L d = b
    simp [hpb, hd]
  have hwL : L w = b := by
    simp only [L, w, sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
    change L p - ε • L d = b
    simp [hpb, hd]
  have havg (j : ι) : (1/2 : ℝ) * u j + (1/2 : ℝ) * w j = p j := by
    dsimp [u, w]
    ring
  have hne : u i ≠ w i := by
    have hdi : d i ≠ 0 := by simpa [d, i.2] using hei
    intro heq
    have hm : ε * d i = 0 := by dsimp [u, w] at heq; linarith
    exact (mul_ne_zero hε.ne' hdi) hm
  have hconc (j : ι) :
      (1/2 : ℝ) * Real.negMulLog (u j) + (1/2 : ℝ) * Real.negMulLog (w j) ≤
        Real.negMulLog (p j) := by
    have h := Real.concaveOn_negMulLog.2 (hu j) (hw j)
      (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : 0 ≤ (1/2 : ℝ))
      (by norm_num : (1/2 : ℝ) + 1/2 = 1)
    simpa only [smul_eq_mul, havg] using h
  have hstrict :
      (1/2 : ℝ) * Real.negMulLog (u i) + (1/2 : ℝ) * Real.negMulLog (w i) <
        Real.negMulLog (p i) := by
    have h := Real.strictConcaveOn_negMulLog.2 (hu i) (hw i) hne
      (by norm_num : 0 < (1/2 : ℝ)) (by norm_num : 0 < (1/2 : ℝ))
      (by norm_num : (1/2 : ℝ) + 1/2 = 1)
    simpa only [smul_eq_mul, havg] using h
  have haux (j : ι) :
      (1/2 : ℝ) * (C j * Real.negMulLog (u j) + A j * u j) +
      (1/2 : ℝ) * (C j * Real.negMulLog (w j) + A j * w j) ≤
      C j * Real.negMulLog (p j) + A j * p j := by
    have h := mul_le_mul_of_nonneg_left (hconc j) (hC j).le
    have h' := congrArg (fun z => A j * z) (havg j)
    linarith only [h, h']
  have haux' :
      (1/2 : ℝ) * (C i * Real.negMulLog (u i) + A i * u i) +
      (1/2 : ℝ) * (C i * Real.negMulLog (w i) + A i * w i) <
      C i * Real.negMulLog (p i) + A i * p i := by
    have h := mul_lt_mul_of_pos_left hstrict (hC i)
    have h' := congrArg (fun z => A i * z) (havg i)
    linarith only [h, h']
  have hlt : (1/2 : ℝ) * F u + (1/2 : ℝ) * F w < F p := by
    unfold F
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_lt_sum (fun k _ => haux k) ⟨i, mem_univ _, haux'⟩
  have hu' := hmin (mem u hu huL)
  have hw' := hmin (mem w hw hwL)
  change F p ≤ F u at hu'
  change F p ≤ F w at hw'
  linarith only [hlt, hu', hw']

end EntropyBridge

namespace EntropyBridge

noncomputable def affinity {ι : Type*} [Fintype ι] (x y : ι → ℝ) (a : ℝ) : ℝ :=
  ∑ i, geom (x i) (y i) a

noncomputable def deficit {ι : Type*} [Fintype ι] (x y : ι → ℝ) (a : ℝ) : ℝ :=
  a * entropy x + (1-a) * entropy y -
    (affinity x y a)^2 * entropy (fun i => geom (x i) (y i) a / affinity x y a)

lemma sparse_deficit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι → ℝ) (a : ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (sx : ∑ i, x i = 1) (sy : ∑ i, y i = 1)
    (ha : 0 < a) (hb : 0 < 1-a)
    (hK : 0 < affinity x y a) (hK1 : affinity x y a < 1) :
    ∃ x' y' : ι → ℝ, (∀ i, 0 ≤ x' i) ∧ (∀ i, 0 ≤ y' i) ∧
      ((∑ i, x' i) = 1) ∧ ((∑ i, y' i) = 1) ∧
      affinity x' y' a = affinity x y a ∧
      (univ.filter (fun i => 0 < x' i + y' i)).card ≤ 3 ∧
      deficit x' y' a ≤ deficit x y a := by
  classical
  let K := affinity x y a
  let q (i : ι) := x i + y i
  let r (i : ι) := if q i = 0 then 1 else x i / q i
  let s (i : ι) := 1-r i
  let c (i : ι) := geom (r i) (s i) a
  let C (i : ι) := a * r i + (1-a) * s i - K * c i
  let A (i : ι) := a * Real.negMulLog (r i) + (1-a) * Real.negMulLog (s i) -
    K * Real.negMulLog (c i)
  let v (i : ι) : Fin 3 → ℝ := ![1, r i, c i]
  let b : Fin 3 → ℝ := ![2, 1, K]
  have hq (i : ι) : 0 ≤ q i := add_nonneg (hx i) (hy i)
  have hr (i : ι) : 0 ≤ r i := by
    dsimp [r]
    split_ifs
    · norm_num
    · exact div_nonneg (hx i) (hq i)
  have hr' (i : ι) : r i ≤ 1 := by
    dsimp [r]
    split_ifs with h
    · rfl
    · exact (div_le_one (lt_of_le_of_ne (hq i) (Ne.symm h))).2
        (le_add_of_nonneg_right (hy i))
  have hs (i : ι) : 0 ≤ s i := sub_nonneg.mpr (hr' i)
  have hqr (i : ι) : q i * r i = x i := by
    by_cases h : q i = 0
    · have hxi : x i = 0 := by dsimp [q] at h; linarith [hx i, hy i]
      simp [h, hxi]
    · simp only [r, if_neg h]
      field_simp
  have hqs (i : ι) : q i * s i = y i := by
    dsimp [s]
    rw [mul_sub, mul_one, hqr]
    dsimp [q]
    ring
  have hqc (i : ι) : q i * c i = geom (x i) (y i) a := by
    rw [← hqr i, ← hqs i, geom_smul _ _ _ _ (hq i) (hr i) (hs i) ha.le hb.le]
  have hC (i : ι) : 0 < C i := by
    have hamgm : (c i) ≤ a * r i + (1-a) * s i :=
      Real.geom_mean_le_arith_mean2_weighted ha.le hb.le (hr i) (hs i) (by ring)
    have havg : 0 < a * r i + (1-a) * s i := by
      obtain h | h := (hr i).eq_or_lt
      · have hsi : s i = 1 := by simp [s, ← h]
        simp [← h, hsi, hb]
      · exact add_pos_of_pos_of_nonneg (mul_pos ha h) (mul_nonneg hb.le (hs i))
    change 0 < _ - K * c i
    have hh := mul_le_mul_of_nonneg_left hamgm hK.le
    have hh' := mul_lt_mul_of_pos_right hK1 havg
    linarith only [hh, hh']
  have hbq : (∑ i, q i • v i) = b := by
    ext j
    fin_cases j
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      change (∑ i, q i * 1) = 2
      simp only [mul_one, q, Finset.sum_add_distrib, sx, sy]
      norm_num
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      change (∑ i, q i * r i) = 1
      simp only [hqr, sx]
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      change (∑ i, q i * c i) = K
      simp only [hqc, K, affinity]
  obtain ⟨p, hp, hpb, hcard, hmin⟩ := sparse_minimum v C A hC (fun _ => rfl) b rfl q hq hbq
  let xp (i : ι) := p i * r i
  let yp (i : ι) := p i * s i
  have hps : (∑ i, p i) = 2 := by
    have h := congrFun hpb (0 : Fin 3)
    simpa [Finset.sum_apply, v, b] using h
  have hpx : (∑ i, xp i) = 1 := by
    have h := congrFun hpb (1 : Fin 3)
    simpa [Finset.sum_apply, v, b, xp] using h
  have hpy : (∑ i, yp i) = 1 := by
    simp only [yp, s, mul_sub, mul_one, Finset.sum_sub_distrib, hps]
    change (2 : ℝ) - (∑ i, xp i) = 1
    rw [hpx]
    norm_num
  have hpc : (∑ i, p i * c i) = K := by
    have h := congrFun hpb (2 : Fin 3)
    simpa [Finset.sum_apply, v, b] using h
  have hrp (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (i : ι) :
      geom (p i * r i) (p i * s i) a = p i * c i :=
    geom_smul _ _ _ _ (hp i) (hr i) (hs i) ha.le hb.le
  have hpK : affinity xp yp a = K := by
    simp only [affinity, xp, yp, hrp p hp, hpc]
  have hc' (i : ι) : xp i + yp i = p i := by dsimp [xp, yp, s]; ring
  refine ⟨xp, yp, fun i => mul_nonneg (hp i) (hr i), fun i => mul_nonneg (hp i) (hs i),
    hpx, hpy, hpK, by simpa only [hc'] using hcard, ?_⟩
  have formula (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) (htK : (∑ i, t i * c i) = K) :
      deficit (fun i => t i * r i) (fun i => t i * s i) a =
        (∑ i, (C i * Real.negMulLog (t i) + A i * t i)) + K * Real.negMulLog K := by
    have hk : affinity (fun i => t i * r i) (fun i => t i * s i) a = K := by
      simp only [affinity, hrp t ht, htK]
    unfold deficit
    simp only [hk, hrp t ht]
    rw [scaled_entropy_identity (fun i => t i * c i) hK.ne' htK]
    have htotal : a * entropy (fun i => t i * r i) +
        (1-a) * entropy (fun i => t i * s i) - K * entropy (fun i => t i * c i) =
          ∑ i, (C i * Real.negMulLog (t i) + A i * t i) := by
      unfold entropy
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Real.negMulLog_mul, C, A]
      ring
    change a * entropy (fun i => t i * r i) + (1-a) * entropy (fun i => t i * s i) -
      (K * entropy (fun i => t i * c i) - K * Real.negMulLog K) = _
    linarith only [htotal]
  have hleft := formula p hp hpc
  have hright := formula q hq (by simp only [hqc, K, affinity])
  simp only [hqr, hqs] at hright
  change deficit (fun i => p i * r i) (fun i => p i * s i) a ≤ deficit x y a
  linarith only [hleft, hright, hmin]

end EntropyBridge

namespace EntropyBridge

lemma equal_of_affinity_one {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) (a : ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (sx : ∑ i, x i = 1) (sy : ∑ i, y i = 1) (ha : 0 < a) (hb : 0 < 1-a)
    (hK : affinity x y a = 1) : x = y := by
  classical
  have hle (i : ι) : geom (x i) (y i) a ≤ a * x i + (1-a) * y i :=
    Real.geom_mean_le_arith_mean2_weighted ha.le hb.le (hx i) (hy i) (by ring)
  have hsum : (∑ i, (a * x i + (1-a) * y i)) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sx, sy]
    ring
  funext i
  apply (Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos ha hb (hx i) (hy i) (by ring)).mp
  change geom (x i) (y i) a = _
  by_contra hne
  have hlt := Finset.sum_lt_sum (fun j (_ : j ∈ univ) => hle j)
    ⟨i, mem_univ _, lt_of_le_of_ne (hle i) hne⟩
  change affinity x y a < (∑ i, (a * x i + (1-a) * y i)) at hlt
  rw [hK, hsum] at hlt
  exact (lt_irrefl _) hlt

lemma all_of_fin_le_three
    (small : ∀ (n : ℕ), n ≤ 3 → ∀ (x y : Fin n → ℝ) (a : ℝ),
        (∀ i, 0 ≤ x i) → (∀ i, 0 ≤ y i) → (∑ i, x i) = 1 → (∑ i, y i) = 1 →
        0 ≤ a → a ≤ 1 → 0 < affinity x y a → 0 ≤ deficit x y a)
    (n : ℕ) (x y : Fin n → ℝ) (a : ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (sx : ∑ i, x i = 1) (sy : ∑ i, y i = 1)
    (ha : 0 ≤ a) (hb : a ≤ 1) (hK : 0 < affinity x y a) :
    0 ≤ deficit x y a := by
  classical
  by_cases ha0 : a = 0
  · subst a
    simp [deficit, affinity, geom, sy]
  by_cases ha1 : a = 1
  · subst a
    simp [deficit, affinity, geom, sx]
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb' : 0 < 1-a := sub_pos.mpr (lt_of_le_of_ne hb ha1)
  have hK' : affinity x y a ≤ 1 := affinity_le_one x y hx hy sx sy ha hb'.le
  obtain he | hlt := hK'.eq_or_lt
  · have hxy := equal_of_affinity_one x y a hx hy sx sy ha' hb' he
    subst y
    have hg (i : Fin n) : geom (x i) (x i) a = x i := by
      unfold geom
      rw [← Real.rpow_add_of_nonneg (hx i) ha hb'.le, show a + (1-a) = 1 by ring,
        Real.rpow_one]
    simp only [deficit, he, one_pow, hg, div_one, one_mul]
    ring_nf
    exact le_rfl
  obtain ⟨u, w, hu, hw, su, sw, hKuw, hcard, hle⟩ :=
    sparse_deficit x y a hx hy sx sy ha' hb' hK hlt
  let T := univ.filter (fun i => 0 < u i + w i)
  let k := Fintype.card ↥T
  let e : Fin k ≃ ↥T := (Fintype.equivFin ↥T).symm
  let U : Fin k → ℝ := fun j => u (e j)
  let W : Fin k → ℝ := fun j => w (e j)
  have hk : k ≤ 3 := by simpa [k, T] using hcard
  have hz (i : Fin n) (hi : i ∉ T) : u i = 0 ∧ w i = 0 := by
    have hn : ¬ 0 < u i + w i := by simpa [T] using hi
    exact ⟨by linarith [hu i, hw i], by linarith [hu i, hw i]⟩
  have hs (f : ℝ → ℝ → ℝ) (hf : f 0 0 = 0) :
      (∑ i, f (U i) (W i)) = ∑ i, f (u i) (w i) := by
    calc
      _ = ∑ i : ↥T, f (u i) (w i) := Fintype.sum_equiv e _ _ (by intro i; rfl)
      _ = ∑ i ∈ T, f (u i) (w i) := Finset.sum_finset_coe (fun i => f (u i) (w i)) T
      _ = _ := Finset.sum_subset (subset_univ _) (fun i _ hi => by
        rw [(hz i hi).1, (hz i hi).2, hf])
  have hgeom : geom 0 0 a = 0 := by simp [geom, Real.zero_rpow ha'.ne']
  have hU : (∑ i, U i) = 1 := (hs (fun x _ => x) rfl).trans su
  have hW : (∑ i, W i) = 1 := (hs (fun _ y => y) rfl).trans sw
  have hUW : affinity U W a = affinity u w a := hs (fun x y => geom x y a) hgeom
  have hduw : deficit U W a = deficit u w a := by
    simp only [deficit, hUW, entropy]
    rw [hs (fun x _ => Real.negMulLog x) Real.negMulLog_zero,
      hs (fun _ y => Real.negMulLog y) Real.negMulLog_zero,
      hs (fun x y => Real.negMulLog (geom x y a / affinity u w a))
        (by simp [hgeom])]
  have hsmall := small k hk U W a (fun j => hu (e j)) (fun j => hw (e j))
    hU hW ha hb (hUW.symm ▸ hKuw.symm ▸ hK)
  rw [hduw] at hsmall
  exact hsmall.trans hle

end EntropyBridge



namespace EntropyBridge

private lemma sinh_ge_self_nonneg {t : ℝ} (ht : 0 ≤ t) : t ≤ Real.sinh t := by
  have hd (x : ℝ) : HasDerivAt (fun x => Real.sinh x - x) (Real.cosh x - 1) x :=
    (Real.hasDerivAt_sinh x).sub (hasDerivAt_id x)
  have hm := monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt)
    (fun x => by rw [(hd x).deriv]; exact sub_nonneg.mpr (Real.one_le_cosh x))
  simpa only [Real.sinh_zero, sub_zero, sub_nonneg] using hm ht

private lemma cosh_sq_ge_twice_sq (u : ℝ) : 2 * u ^ 2 ≤ (Real.cosh u)^2 := by
  have hh : 2 * (|u| / 2) = |u| := by ring
  have hc := Real.cosh_two_mul (|u| / 2)
  rw [hh, Real.cosh_abs, Real.cosh_sq'] at hc
  have hs := sinh_ge_self_nonneg (t := |u| / 2) (by positivity)
  have hs0 : 0 ≤ Real.sinh (|u| / 2) := le_trans (by positivity) hs
  have hs2 := pow_le_pow_left₀ (by positivity : 0 ≤ |u| / 2) hs 2
  have hu : |u|^2 = u^2 := sq_abs u
  have hcosh : 1 + u ^ 2 / 2 ≤ Real.cosh u := by
    nlinarith only [hc, hs2, hu]
  have hp : 0 ≤ 1 + u^2/2 := by positivity
  have hsq := pow_le_pow_left₀ hp hcosh 2
  nlinarith only [hsq, sq_nonneg (u^2/2-1)]

lemma log_pair_variance_bound {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * y * (Real.log x - Real.log y)^2 ≤ (x+y)^2 / 2 := by
  rcases hx.eq_or_lt with hx | hx
  · simpa [← hx] using (by positivity : 0 ≤ y^2/2)
  rcases hy.eq_or_lt with hy | hy
  · simpa [← hy] using (by positivity : 0 ≤ x^2/2)
  let u := (Real.log x - Real.log y)/2
  let t := Real.exp u
  have ht : 0 < t := Real.exp_pos _
  have ht2 : t^2 * y = x := by
    rw [pow_two]
    change Real.exp u * Real.exp u * y = x
    rw [← Real.exp_add, show u+u = Real.log x - Real.log y by dsimp [u]; ring,
      Real.exp_sub, Real.exp_log hx, Real.exp_log hy]
    field_simp
  have hcosh : 2 * Real.cosh u = t + 1/t := by
    rw [Real.cosh_eq, Real.exp_neg]
    dsimp [t]
    ring
  have hprod : 4*x*y*(Real.cosh u)^2 = (x+y)^2 := by
    have h : 4 * (Real.cosh u)^2 = (t + 1/t)^2 := by
      nlinarith only [congrArg (fun x : ℝ => x ^ 2) hcosh]
    calc
      _ = x*y*(4*(Real.cosh u)^2) := by ring
      _ = _ := by rw [h, ← ht2]; field_simp
  have hmul := mul_le_mul_of_nonneg_left (cosh_sq_ge_twice_sq u)
    (show 0 ≤ 4*x*y by positivity)
  change 4*x*y*(2*u^2) ≤ 4*x*y*(Real.cosh u)^2 at hmul
  rw [hprod] at hmul
  dsimp [u] at hmul
  nlinarith only [hmul]

/-- The variance of natural-log surprisal is at most one on three atoms. -/
lemma ternary_surprisal_variance (p : Fin 3 → ℝ) (hp : ∀ i, 0 ≤ p i)
    (h1 : (∑ i, p i) = 1) :
    (∑ i, p i * (-Real.log (p i) - (∑ j, p j * -Real.log (p j)))^2) ≤ 1 := by
  have hp2 : p 2 = 1 - p 0 - p 1 := by
    rw [Fin.sum_univ_three] at h1
    linarith only [h1]
  have hvar :
      (∑ i, p i * (-Real.log (p i) - (∑ j, p j * -Real.log (p j)))^2) =
        p 0 * p 1 * (Real.log (p 0)-Real.log (p 1))^2 +
        p 0 * p 2 * (Real.log (p 0)-Real.log (p 2))^2 +
        p 1 * p 2 * (Real.log (p 1)-Real.log (p 2))^2 := by
    simp only [Fin.sum_univ_three]
    generalize Real.log (p 0) = l₀
    generalize Real.log (p 1) = l₁
    generalize Real.log (p 2) = l₂
    rw [hp2]
    ring
  have hineq : (p 0+p 1)^2/2 + (p 0+p 2)^2/2 + (p 1+p 2)^2/2 ≤ 1 := by
    rw [Fin.sum_univ_three] at h1
    have hp01 : 0 ≤ p 0 * p 1 := mul_nonneg (hp 0) (hp 1)
    have hp02 : 0 ≤ p 0 * p 2 := mul_nonneg (hp 0) (hp 2)
    have hp12 : 0 ≤ p 1 * p 2 := mul_nonneg (hp 1) (hp 2)
    have hs := congrArg (fun t : ℝ => t^2) h1
    nlinarith only [hs, hp01, hp02, hp12]
  rw [hvar]
  linarith only [hineq, log_pair_variance_bound (hp 0) (hp 1),
    log_pair_variance_bound (hp 0) (hp 2), log_pair_variance_bound (hp 1) (hp 2)]

end EntropyBridge

end BridgeSection

section LogOddsSection

namespace EntropyBridge

open Real Set

noncomputable def oddsEntropy (u : ℝ) : ℝ :=
  (1 + exp u) * log (1 + exp (-u)) + (1 + exp (-u)) * log (1 + exp u)

noncomputable def oddsEnergy (u : ℝ) : ℝ :=
  log (1 + exp u) + log (1 + exp (-u))

noncomputable def oddsEntropySlope (u : ℝ) : ℝ :=
  exp u * log (1 + exp (-u)) - exp (-u) * log (1 + exp u)

private lemma log_one_add_lower {t : ℝ} (ht : 0 ≤ t) : t / (1+t) ≤ log (1+t) := by
  have h := one_sub_inv_le_log_of_pos (show 0 < 1 + t by positivity)
  convert h using 1
  field_simp
  <;> ring

private lemma exp_neg_deriv (u : ℝ) :
    HasDerivAt (fun u => exp (-u)) (-exp (-u)) u := by
  convert (hasDerivAt_exp (-u)).comp u (hasDerivAt_id u).neg using 1 <;>
    first | rfl | simp [Function.comp_def]

private lemma log_exp_deriv (u : ℝ) :
    HasDerivAt (fun u => log (1 + exp u)) (exp u / (1 + exp u)) u :=
  ((hasDerivAt_exp u).const_add 1).log (by positivity)

private lemma log_exp_neg_deriv (u : ℝ) :
    HasDerivAt (fun u => log (1 + exp (-u))) (-exp (-u) / (1 + exp (-u))) u :=
  ((exp_neg_deriv u).const_add 1).log (by positivity)

private lemma exp_product (u : ℝ) : exp u * exp (-u) = 1 := by
  rw [← exp_add, add_neg_cancel, exp_zero]

lemma oddsEntropy_neg (u : ℝ) : oddsEntropy (-u) = oddsEntropy u := by
  simp [oddsEntropy, add_comm]

lemma oddsEnergy_neg (u : ℝ) : oddsEnergy (-u) = oddsEnergy u := by
  simp [oddsEnergy, add_comm]

lemma oddsEntropy_deriv (u : ℝ) : HasDerivAt oddsEntropy (oddsEntropySlope u) u := by
  have h := (((hasDerivAt_exp u).const_add 1).mul (log_exp_neg_deriv u)).add
    (((exp_neg_deriv u).const_add 1).mul (log_exp_deriv u))
  convert h using 1 <;> try rfl
  unfold oddsEntropySlope
  have hpos : 0 < exp u := exp_pos _
  rw [exp_neg]
  field_simp
  <;> ring

lemma oddsEntropySlope_deriv (u : ℝ) :
    HasDerivAt oddsEntropySlope
      (exp u * log (1 + exp (-u)) + exp (-u) * log (1 + exp u) - 1) u := by
  have h := ((hasDerivAt_exp u).mul (log_exp_neg_deriv u)).sub
    ((exp_neg_deriv u).mul (log_exp_deriv u))
  convert h using 1 <;> try rfl
  have hpos : 0 < exp u := exp_pos _
  rw [exp_neg]
  field_simp
  <;> ring

lemma oddsEnergy_deriv (u : ℝ) :
    HasDerivAt oddsEnergy ((exp u - 1) / (exp u + 1)) u := by
  have h := (log_exp_deriv u).add (log_exp_neg_deriv u)
  convert h using 1 <;> try rfl
  have hpos : 0 < exp u := exp_pos _
  rw [exp_neg]
  field_simp
  <;> ring

lemma oddsEntropy_convex : ConvexOn ℝ univ oddsEntropy := by
  have hderiv : deriv oddsEntropy = oddsEntropySlope :=
    funext fun u => (oddsEntropy_deriv u).deriv
  apply convexOn_of_deriv2_nonneg' convex_univ
  · exact fun u _ => (oddsEntropy_deriv u).differentiableAt.differentiableWithinAt
  · rw [hderiv]
    exact fun u _ => (oddsEntropySlope_deriv u).differentiableAt.differentiableWithinAt
  · intro u _
    change 0 ≤ deriv (deriv oddsEntropy) u
    rw [hderiv, (oddsEntropySlope_deriv u).deriv]
    have h₀ := mul_le_mul_of_nonneg_left (log_one_add_lower (exp_nonneg (-u))) (exp_nonneg u)
    have h₁ := mul_le_mul_of_nonneg_left (log_one_add_lower (exp_nonneg u)) (exp_nonneg (-u))
    rw [← mul_div_assoc, exp_product] at h₀
    rw [← mul_div_assoc, mul_comm (exp (-u)) (exp u), exp_product] at h₁
    have hs : 1/(1+exp (-u)) + 1/(1+exp u) = 1 := by
      have hpos : 0 < exp u := exp_pos _
      rw [exp_neg]
      field_simp
      <;> ring
    linarith only [h₀, h₁, hs]

lemma oddsEntropy_ge_two (u : ℝ) : 2 ≤ oddsEntropy u := by
  have h₀ := oddsEntropy_convex.2 (mem_univ u) (mem_univ (-u))
    (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : 0 ≤ (1/2 : ℝ))
    (by norm_num : (1/2 : ℝ) + 1/2 = 1)
  simp only [smul_eq_mul, oddsEntropy_neg, show (1/2 : ℝ)*u + (1/2 : ℝ)*(-u) = 0 by ring] at h₀
  have h₁ := log_one_add_lower (show (0:ℝ) ≤ 1 by norm_num)
  norm_num [oddsEntropy] at h₀ h₁
  unfold oddsEntropy
  linarith only [h₀, h₁]

private lemma slope_comparison (r : ℝ) (hr : 1 ≤ r) :
    r * log (1 + r⁻¹) - r⁻¹ * log (1 + r) ≤ (r-1)/(r+1) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let F (t : ℝ) := t*((r-1)/(r+1)) - r*log (1+t/r) + r⁻¹*log (1+r*t)
  have hF (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt F (r*(r-1)*(1-t)^2 / ((r+1)*(r+t)*(1+r*t))) t := by
    have hleft := ((hasDerivAt_id t).div_const r).const_add 1
    have hright := ((hasDerivAt_id t).const_mul r).const_add 1
    have h₀ : 0 < 1+t/r := by positivity
    have h₁ : 0 < 1+r*t := by positivity
    have h := (((hasDerivAt_id t).mul_const ((r-1)/(r+1))).sub
      ((hleft.log h₀.ne').const_mul r)).add ((hright.log h₁.ne').const_mul r⁻¹)
    convert h using 1 <;> try rfl
    have h₂ : 0 < r+t := by positivity
    change _ = 1*((r-1)/(r+1)) - r*(1/r/(1+t/r)) + r⁻¹*(r*1/(1+r*t))
    have htR : 1+t/r=(r+t)/r := by field_simp
    rw [htR]
    field_simp [hr0.ne', h₂.ne', h₁.ne']
    <;> ring
  have hmono : MonotoneOn F (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t ht => (hF t ht).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t ∈ Ici (0:ℝ) := interior_subset ht
      exact (hF t ht').differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 0 ≤ t := @interior_subset ℝ _ (Ici 0) t ht
      rw [(hF t ht').deriv]
      exact div_nonneg (by have := sub_nonneg.mpr hr; positivity) (by positivity)
  have h := hmono (show (0:ℝ) ∈ Ici 0 by simp) (show (1:ℝ) ∈ Ici 0 by simp) zero_le_one
  simp [F, one_div] at h
  linarith only [h]

lemma oddsEnergy_mono : MonotoneOn oddsEnergy (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · exact fun u _ => (oddsEnergy_deriv u).continuousAt.continuousWithinAt
  · exact fun u _ => (oddsEnergy_deriv u).differentiableAt.differentiableWithinAt
  · intro u hu
    have hu' : u ∈ Ici (0:ℝ) := interior_subset hu
    rw [(oddsEnergy_deriv u).deriv]
    exact div_nonneg (sub_nonneg.mpr (by simpa using exp_le_exp.mpr hu')) (by positivity)

lemma oddsEnergy_sub_entropy_mono : MonotoneOn (fun u => oddsEnergy u - oddsEntropy u) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · exact fun u _ => ((oddsEnergy_deriv u).sub (oddsEntropy_deriv u)).continuousAt.continuousWithinAt
  · exact fun u _ => ((oddsEnergy_deriv u).sub (oddsEntropy_deriv u)).differentiableAt.differentiableWithinAt
  · intro u hu
    have hu' : u ∈ Ici (0:ℝ) := interior_subset hu
    change 0 ≤ deriv (oddsEnergy - oddsEntropy) u
    rw [((oddsEnergy_deriv u).sub (oddsEntropy_deriv u)).deriv]
    apply sub_nonneg.mpr
    have hr : 1 ≤ exp u := by simpa using exp_le_exp.mpr hu'
    simpa only [oddsEntropySlope, exp_neg] using slope_comparison _ hr

lemma oddsEnergy_abs (u : ℝ) : oddsEnergy |u| = oddsEnergy u := by
  rcases le_total 0 u with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, oddsEnergy_neg]

lemma oddsEntropy_abs (u : ℝ) : oddsEntropy |u| = oddsEntropy u := by
  rcases le_total 0 u with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, oddsEntropy_neg]

lemma oddsEnergy_le_and_entropy_diff {u v : ℝ} (huv : |u| ≤ |v|) :
    oddsEnergy u ≤ oddsEnergy v ∧
      oddsEntropy v ≤ oddsEntropy u + (oddsEnergy v - oddsEnergy u) := by
  have h₀ := oddsEnergy_mono (abs_nonneg u) (abs_nonneg v) huv
  have h₁ := oddsEnergy_sub_entropy_mono (abs_nonneg u) (abs_nonneg v) huv
  simp only [oddsEnergy_abs, oddsEntropy_abs] at h₀ h₁
  exact ⟨h₀, by linarith only [h₁]⟩

end EntropyBridge

end LogOddsSection

section WeightSection

namespace EntropyBridge

open Real Set

private lemma sinh_ge_self {x : ℝ} (hx : 0 ≤ x) : x ≤ sinh x := by
  have hd (x : ℝ) : HasDerivAt (fun x => sinh x - x) (cosh x - 1) x :=
    (hasDerivAt_sinh x).sub (hasDerivAt_id x)
  have hm := monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt)
    (fun x => by rw [(hd x).deriv]; exact sub_nonneg.mpr (one_le_cosh x))
  simpa only [sinh_zero, sub_zero, sub_nonneg] using hm hx

private lemma sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) : sinh x ≤ x * cosh x := by
  let f (t : ℝ) := t * cosh t - sinh t
  have hd (t : ℝ) : HasDerivAt f (t * sinh t) t := by
    have h := ((hasDerivAt_id t).mul (hasDerivAt_cosh t)).sub (hasDerivAt_sinh t)
    convert h using 1 <;> try rfl
    simp
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 0 ≤ t := @interior_subset ℝ _ (Ici 0) t ht
      rw [(hd t).deriv]
      exact mul_nonneg ht' (ht'.trans (sinh_ge_self ht'))
  have h := hm (show (0 : ℝ) ∈ Ici 0 by simp) hx hx
  simpa [f, sub_nonneg] using h

private lemma sinh_div_mono : MonotoneOn (fun t : ℝ => sinh t / t) (Ioi 0) := by
  have hd (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun t => sinh t / t) ((cosh t*t - sinh t)/t^2) t := by
    convert (hasDerivAt_sinh t).div (hasDerivAt_id t) ht.ne' using 1 <;> first | rfl | simp
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
  · exact fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' : 0 < t := @interior_subset ℝ _ (Ioi 0) t ht
    rw [(hd t ht').deriv, mul_comm (cosh t)]
    exact div_nonneg (sub_nonneg.mpr (sinh_le_mul_cosh ht'.le)) (by positivity)

private lemma exp_sub_one_eq_sinh (x : ℝ) : exp (2*x) - 1 = 2 * exp x * sinh x := by
  rw [show 2*x=x+x by ring, exp_add, sinh_eq, exp_neg]
  have hx := (exp_pos x).ne'
  field_simp

private lemma one_sub_exp_eq_sinh (x : ℝ) : 1 - exp (-(2*x)) = 2 * exp (-x) * sinh x := by
  have h := exp_sub_one_eq_sinh (-x)
  rw [sinh_neg, show 2 * (-x) = -(2*x) by ring] at h
  linarith only [h]

private lemma weight_quotient_bound {a b ℓ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a+b=1) (hℓ : 0 < ℓ) :
    b * (1 - exp (-a*ℓ)) * (1 + ℓ/2) ≤ a * (exp (b*ℓ)-1) := by
  let x := ℓ/2
  have hx : 0 < x := by dsimp [x]; positivity
  have hp : 0 < b*x := mul_pos hb hx
  have hq : 0 < a*x := mul_pos ha hx
  have haq : a*x ≤ x := by
    calc
      a*x ≤ (a+b)*x := by gcongr; linarith
      _ = x := by rw [hab, one_mul]
  have hmono := sinh_div_mono hq hx haq
  have hq' : sinh (a*x) * x ≤ sinh x * (a*x) := (div_le_div_iff₀ hq hx).mp hmono
  have hp' : b*x ≤ sinh (b*x) := sinh_ge_self hp.le
  have hsx : 0 ≤ sinh x := hx.le.trans (sinh_ge_self hx.le)
  have hprod : b * sinh (a*x) * x ≤ a * sinh (b*x) * sinh x := by
    calc
      _ = b * (sinh (a*x) * x) := by ring
      _ ≤ b * (sinh x * (a*x)) := mul_le_mul_of_nonneg_left hq' hb.le
      _ = a * (b*x) * sinh x := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp' ha.le) hsx
  have heq : exp (b*x) * exp (-x) = exp (-(a*x)) := by
    rw [← exp_add]
    congr 1
    linear_combination x * hab
  have heL : exp (b*ℓ) - 1 = 2 * exp (b*x) * sinh (b*x) := by
    rw [← exp_sub_one_eq_sinh]
    congr 2
    dsimp [x]
    ring
  have heR : 1 - exp (-a*ℓ) = 2 * exp (-(a*x)) * sinh (a*x) := by
    rw [← one_sub_exp_eq_sinh]
    congr 2
    dsimp [x]
    ring
  have heX : 1 - exp (-ℓ) = 2 * exp (-x) * sinh x := by
    rw [← one_sub_exp_eq_sinh]
    congr 2
    dsimp [x]
    ring
  have hcross :
      b*(1-exp (-a*ℓ))*ℓ ≤ a*(exp (b*ℓ)-1)*(1-exp (-ℓ)) := by
    rw [heR, heL, heX]
    change b * (2*exp (-(a*x))*sinh (a*x)) * ℓ ≤
      a * (2*exp (b*x)*sinh (b*x)) * (2*exp (-x)*sinh x)
    rw [show ℓ=2*x by dsimp [x]; ring]
    calc
      _ = (4*exp (-(a*x))) * (b*sinh (a*x)*x) := by ring
      _ ≤ (4*exp (-(a*x))) * (a*sinh (b*x)*sinh x) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = _ := by rw [← heq]; ring
  have hden : 0 < 1-exp (-ℓ) := by
    have := exp_lt_exp.mpr (show -ℓ < 0 by linarith)
    simpa using sub_pos.mpr (show exp (-ℓ) < 1 by simpa using this)
  have htanh : (1+x)*sinh x ≤ x*exp x := by
    have hh := sinh_le_mul_cosh hx.le
    rw [← cosh_add_sinh]
    nlinarith only [hh]
  have hden' : (1+ℓ/2)*(1-exp (-ℓ)) ≤ ℓ := by
    change (1+x)*(1-exp (-ℓ)) ≤ ℓ
    rw [heX, show ℓ=2*x by dsimp [x]; ring]
    calc
      _ = (2*exp (-x))*((1+x)*sinh x) := by ring
      _ ≤ (2*exp (-x))*(x*exp x) := mul_le_mul_of_nonneg_left htanh (by positivity)
      _ = _ := by
        have hh : exp (-x)*exp x = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
        calc
          _ = 2*x*(exp (-x)*exp x) := by ring
          _ = _ := by rw [hh, mul_one]
  have hA : 0 ≤ b*(1-exp (-a*ℓ)) := by
    have h : exp (-a*ℓ) ≤ 1 := by
      simpa using exp_le_exp.mpr (show -a*ℓ ≤ 0 by nlinarith only [mul_pos ha hℓ])
    exact mul_nonneg hb.le (sub_nonneg.mpr h)
  apply le_of_mul_le_mul_right _ hden
  calc
    _ = (b*(1-exp (-a*ℓ)))*((1+ℓ/2)*(1-exp (-ℓ))) := by ring
    _ ≤ b*(1-exp (-a*ℓ))*ℓ := mul_le_mul_of_nonneg_left hden' hA
    _ ≤ _ := hcross

lemma weighted_binary_factors {a b ℓ g₀ g₁ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a+b=1) (hℓ : 0 ≤ ℓ) (hg₀ : 2 ≤ g₀) (hg₁ : g₁ ≤ g₀+ℓ) :
    a*g₀ + b*g₁ ≤ a*exp (b*ℓ)*g₀ + b*exp (-a*ℓ)*g₁ := by
  rcases hℓ.eq_or_lt with h | h
  · rw [← h]
    simp
  have hg₀' : 0 ≤ g₀ := by linarith only [hg₀]
  have hb' : 0 ≤ b*(1-exp (-a*ℓ)) := by
    have hh : exp (-a*ℓ) ≤ 1 := by
      simpa using exp_le_exp.mpr (show -a*ℓ ≤ 0 by nlinarith only [mul_pos ha h])
    exact mul_nonneg hb.le (sub_nonneg.mpr hh)
  have hgg : g₁ ≤ (1+ℓ/2)*g₀ := by
    nlinarith only [hg₁, mul_nonneg h.le (sub_nonneg.mpr hg₀)]
  have h₁ := mul_le_mul_of_nonneg_left hgg hb'
  have h₂ := mul_le_mul_of_nonneg_right (weight_quotient_bound ha hb hab h) hg₀'
  linarith only [h₁, h₂]

end EntropyBridge

end WeightSection

section BinarySection

namespace EntropyBridge

open Real Set

private lemma odds_interp_ordered {a b u v : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a+b=1) (huv : |u| ≤ |v|) :
    exp (-(a*oddsEnergy u+b*oddsEnergy v)) * oddsEntropy (a*u+b*v) ≤
      a*(exp (-oddsEnergy u)*oddsEntropy u) + b*(exp (-oddsEnergy v)*oddsEntropy v) := by
  let ℓ := oddsEnergy v - oddsEnergy u
  obtain ⟨hAB, hG⟩ := oddsEnergy_le_and_entropy_diff huv
  have hbound := weighted_binary_factors ha hb hab (show 0 ≤ ℓ from sub_nonneg.mpr hAB)
    (oddsEntropy_ge_two u) hG
  have hconv := oddsEntropy_convex.2 (mem_univ u) (mem_univ v) ha.le hb.le hab
  simp only [smul_eq_mul] at hconv
  let s := exp (-(a*oddsEnergy u+b*oddsEnergy v))
  have hs : 0 ≤ s := (exp_pos _).le
  have hu : s*exp (b*ℓ) = exp (-oddsEnergy u) := by
    unfold s
    rw [← exp_add]
    congr 1
    dsimp [ℓ]
    linear_combination -(oddsEnergy u) * hab
  have hv : s*exp (-a*ℓ) = exp (-oddsEnergy v) := by
    unfold s
    rw [← exp_add]
    congr 1
    dsimp [ℓ]
    linear_combination -(oddsEnergy v) * hab
  change s * oddsEntropy (a*u+b*v) ≤ _
  calc
    _ ≤ s*(a*oddsEntropy u+b*oddsEntropy v) := mul_le_mul_of_nonneg_left hconv hs
    _ ≤ s*(a*exp (b*ℓ)*oddsEntropy u+b*exp (-a*ℓ)*oddsEntropy v) :=
      mul_le_mul_of_nonneg_left hbound hs
    _ = a*((s*exp (b*ℓ))*oddsEntropy u)+b*((s*exp (-a*ℓ))*oddsEntropy v) := by ring
    _ = _ := by rw [hu,hv]

lemma odds_interp {a b u v : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1) :
    exp (-(a*oddsEnergy u+b*oddsEnergy v)) * oddsEntropy (a*u+b*v) ≤
      a*(exp (-oddsEnergy u)*oddsEntropy u) + b*(exp (-oddsEnergy v)*oddsEntropy v) := by
  rcases le_total |u| |v| with h | h
  · exact odds_interp_ordered ha hb hab h
  · rw [add_comm (a*oddsEnergy u), add_comm (a*u), add_comm (a * _)]
    exact odds_interp_ordered hb ha (by linarith only [hab]) h

private lemma binary_representation {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x+y=1) :
    exp (-oddsEnergy (log x-log y)) = x*y ∧
      x*y*oddsEntropy (log x-log y) = negMulLog x + negMulLog y := by
  have h₀ : exp (log x-log y) = x/y := by rw [exp_sub, exp_log hx, exp_log hy]
  have h₁ : exp (-(log x-log y)) = y/x := by
    rw [neg_sub, exp_sub, exp_log hx, exp_log hy]
  have h₂ : 1 + x/y = 1/y := by
    field_simp
    linarith only [hxy]
  have h₃ : 1 + y/x = 1/x := by
    field_simp
    linarith only [hxy]
  constructor
  · rw [oddsEnergy,h₀,h₁,h₂,h₃,one_div,one_div,log_inv,log_inv,
      neg_add, neg_neg, neg_neg, exp_add, exp_log hy, exp_log hx, mul_comm]
  · rw [oddsEntropy,h₀,h₁,h₂,h₃,one_div,one_div,log_inv,log_inv]
    simp only [negMulLog_def]
    field_simp
    <;> ring

lemma entropy_nonneg_prob {ι : Type*} [Fintype ι] (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hs : (∑ i,x i) = 1) : 0 ≤ entropy x := by
  apply Finset.sum_nonneg
  intro i _
  apply Real.negMulLog_nonneg (hx i)
  rw [← hs]
  exact Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)

theorem binary_target (x y : Fin 2 → ℝ) (a : ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (sx : (∑ i,x i) = 1) (sy : (∑ i,y i) = 1)
    (ha : 0 ≤ a) (ha' : a ≤ 1) (hK : 0 < affinity x y a) :
    0 ≤ deficit x y a := by
  by_cases ha0 : a=0
  · subst a
    simp [deficit, affinity, geom, sy]
  by_cases ha1 : a=1
  · subst a
    simp [deficit, affinity, geom, sx]
  have ha0' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb : 0 < 1-a := sub_pos.mpr (lt_of_le_of_ne ha' ha1)
  let m (i : Fin 2) := geom (x i) (y i) a
  let K := affinity x y a
  let z (i : Fin 2) := m i / K
  have hm0 (i : Fin 2) : 0 ≤ m i :=
    mul_nonneg (rpow_nonneg (hx i) _) (rpow_nonneg (hy i) _)
  have hm_eq : m 0 + m 1 = K := by simp [K, affinity, Fin.sum_univ_two, m]
  have hpos : 0 < K := hK
  by_cases hp : ∀ i, 0 < x i ∧ 0 < y i
  · have hm (i : Fin 2) : 0 < m i :=
      mul_pos (rpow_pos_of_pos (hp i).1 _) (rpow_pos_of_pos (hp i).2 _)
    have hz (i : Fin 2) : 0 < z i := div_pos (hm i) hpos
    have hzx : z 0 + z 1 = 1 := by
      dsimp [z]
      rw [← add_div, hm_eq, div_self hpos.ne']
    let u := log (x 0)-log (x 1)
    let v := log (y 0)-log (y 1)
    let w := log (z 0)-log (z 1)
    have hrepX := binary_representation (hp 0).1 (hp 1).1 (by simpa [Fin.sum_univ_two] using sx)
    have hrepY := binary_representation (hp 0).2 (hp 1).2 (by simpa [Fin.sum_univ_two] using sy)
    have hrepZ := binary_representation (hz 0) (hz 1) hzx
    have hentX : exp (-oddsEnergy u)*oddsEntropy u = entropy x := by
      rw [show exp (-oddsEnergy u)=x 0*x 1 from hrepX.1]
      simpa [entropy, Fin.sum_univ_two] using hrepX.2
    have hentY : exp (-oddsEnergy v)*oddsEntropy v = entropy y := by
      rw [show exp (-oddsEnergy v)=y 0*y 1 from hrepY.1]
      simpa [entropy, Fin.sum_univ_two] using hrepY.2
    have hentZ : z 0*z 1*oddsEntropy w = entropy z := by
      simpa [entropy, Fin.sum_univ_two] using hrepZ.2
    have hw : w = a*u+(1-a)*v := by
      have hlog (i : Fin 2) : log (z i) = a*log (x i)+(1-a)*log (y i)-log K := by
        change log (m i / K) = _
        rw [log_div (hm i).ne' hpos.ne']
        unfold m geom
        rw [log_mul (rpow_pos_of_pos (hp i).1 _).ne' (rpow_pos_of_pos (hp i).2 _).ne',
          log_rpow (hp i).1, log_rpow (hp i).2]
      dsimp [w, u, v]
      rw [hlog 0, hlog 1]
      ring
    have hmprod : m 0*m 1 = (x 0*x 1)^a * (y 0*y 1)^(1-a) := by
      unfold m geom
      rw [mul_rpow (hx 0) (hx 1), mul_rpow (hy 0) (hy 1)]
      ring
    have hpexp : exp (-(a*oddsEnergy u+(1-a)*oddsEnergy v)) = m 0*m 1 := by
      rw [hmprod, ← (show exp (-oddsEnergy u)=x 0*x 1 from hrepX.1),
        ← (show exp (-oddsEnergy v)=y 0*y 1 from hrepY.1),
        ← exp_mul, ← exp_mul, ← exp_add]
      congr 1
      ring
    have hscaled : K^2 * entropy z = (m 0*m 1) * oddsEntropy w := by
      rw [← hentZ]
      dsimp [z]
      field_simp
      <;> ring
    have hI := odds_interp ha0' hb (by ring : a+(1-a)=1) (u := u) (v := v)
    rw [hentX, hentY, hpexp, ← hw, ← hscaled] at hI
    exact sub_nonneg.mpr hI
  · push Not at hp
    obtain ⟨i, hi⟩ := hp
    have hz0 : m i = 0 := by
      by_cases hz : x i = 0
      · simp [m, geom, hz, Real.zero_rpow ha0'.ne']
      · have hzi : y i = 0 := by
          have ht : 0 < x i := lt_of_le_of_ne (hx i) (Ne.symm hz)
          exact le_antisymm (hi ht) (hy i)
        simp [m, geom, hzi, Real.zero_rpow hb.ne']
    have hZ : entropy z = 0 := by
      fin_cases i
      · change m 0 = 0 at hz0
        have hm1 : m 1 = K := by simpa [hz0] using hm_eq
        simp [entropy, Fin.sum_univ_two, z, hz0, hm1, hpos.ne']
      · change m 1 = 0 at hz0
        have hm1 : m 0 = K := by simpa [hz0] using hm_eq
        simp [entropy, Fin.sum_univ_two, z, hz0, hm1, hpos.ne']
    change 0 ≤ a * entropy x + (1-a) * entropy y - K^2 * entropy z
    rw [hZ, mul_zero, sub_zero]
    exact add_nonneg (mul_nonneg ha (entropy_nonneg_prob x hx sx))
      (mul_nonneg hb.le (entropy_nonneg_prob y hy sy))

end EntropyBridge

end BinarySection

section CurvatureSection

open scoped BigOperators Topology
open Filter Real

namespace EntropyBridge

noncomputable def scaleLine {ι : Type*} (p d : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  (1+t*d i)*p i

@[simp] lemma scaleLine_zero {ι : Type*} (p d : ι → ℝ) : scaleLine p d 0 = p := by
  ext i
  simp [scaleLine]

lemma scaleLine_mass {ι : Type*} [Fintype ι] (p d : ι → ℝ) (t : ℝ) :
    (∑ i, scaleLine p d t i) = (∑ i,p i) + t*(∑ i,d i*p i) := by
  simp only [scaleLine, add_mul, one_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

private lemma affine_deriv (r k t : ℝ) :
    HasDerivAt (fun t => r+t*k) k t := by
  convert ((hasDerivAt_id t).mul_const k).const_add r using 1 <;> first | rfl | simp

private lemma scaleLine_deriv {ι : Type*} (p d : ι → ℝ) (t : ℝ) (i : ι) :
    HasDerivAt (fun t => scaleLine p d t i) (d i*p i) t :=
  (affine_deriv 1 (d i) t).mul_const (p i)

private lemma affine_entropy_deriv {f : ℝ → ℝ} {t s : ℝ} (hf : HasDerivAt f s t)
    (h0 : f t ≠ 0) :
    HasDerivAt (fun t => negMulLog (f t)) (s*(-log (f t)-1)) t := by
  convert (hasDerivAt_negMulLog h0).comp t hf using 1 <;>
    first | rfl | ring

private noncomputable def lineSlope {ι : Type*} [Fintype ι]
    (p d : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, d i*p i*(-log (scaleLine p d t i)-1)

private lemma entropy_line_deriv {ι : Type*} [Fintype ι] (p d : ι → ℝ) (t : ℝ)
    (hp : ∀ i, 0 ≤ p i) (ht : ∀ i, 0 < 1+t*d i) :
    HasDerivAt (fun t => entropy (scaleLine p d t)) (lineSlope p d t) t := by
  apply HasDerivAt.fun_sum
  intro i _
  rcases (hp i).eq_or_lt with h | h
  · simp [scaleLine, ← h, hasDerivAt_const]
  · exact affine_entropy_deriv (scaleLine_deriv p d t i) (mul_pos (ht i) h).ne'

private lemma lineSlope_deriv {ι : Type*} [Fintype ι] (p d : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) :
    HasDerivAt (lineSlope p d) (-(∑ i,p i*(d i)^2)) 0 := by
  rw [← Finset.sum_neg_distrib]
  apply HasDerivAt.fun_sum
  intro i _
  rcases (hp i).eq_or_lt with h | h
  · simp [← h, hasDerivAt_const]
  · have hpos : 0 < scaleLine p d 0 i := by simpa using h
    have hd := ((((scaleLine_deriv p d 0 i).log hpos.ne').neg).sub_const 1).const_mul
      (d i*p i)
    convert hd using 1 <;> try rfl
    rw [scaleLine_zero]
    field_simp
    <;> ring

noncomputable def lineMass {ι : Type*} [Fintype ι] (m d : ι → ℝ) (t : ℝ) : ℝ :=
  (∑ i,m i) + t*(∑ i,d i*m i)

@[simp] lemma lineMass_zero {ι : Type*} [Fintype ι] (m d : ι → ℝ) :
    lineMass m d 0 = ∑ i,m i := by simp [lineMass]

noncomputable def lineDeficit {ι : Type*} [Fintype ι] (x y m d : ι → ℝ) (a t : ℝ) : ℝ :=
  a*entropy (scaleLine x d t)+(1-a)*entropy (scaleLine y d t) -
    lineMass m d t * entropy (scaleLine m d t) + lineMass m d t * negMulLog (lineMass m d t)

private noncomputable def lineDeficitSlope {ι : Type*} [Fintype ι]
    (x y m d : ι → ℝ) (a t : ℝ) : ℝ :=
  let k := ∑ i,d i*m i
  let K := lineMass m d t
  a*lineSlope x d t+(1-a)*lineSlope y d t -
    (k*entropy (scaleLine m d t)+K*lineSlope m d t) +
    (k*negMulLog K+K*(k*(-log K-1)))

private lemma lineDeficit_deriv {ι : Type*} [Fintype ι]
    (x y m d : ι → ℝ) (a t : ℝ)
    (hx : ∀ i,0 ≤ x i) (hy : ∀ i,0 ≤ y i) (hm : ∀ i,0 ≤ m i)
    (ht : ∀ i,0 < 1+t*d i) (hK : 0 < lineMass m d t) :
    HasDerivAt (lineDeficit x y m d a) (lineDeficitSlope x y m d a t) t := by
  have hK' : HasDerivAt (lineMass m d) (∑ i,d i*m i) t := affine_deriv _ _ _
  have hh := affine_entropy_deriv hK' hK.ne'
  have h := (((entropy_line_deriv x d t hx ht).const_mul a).add
    ((entropy_line_deriv y d t hy ht).const_mul (1-a))).sub
      (hK'.mul (entropy_line_deriv m d t hm ht)) |>.add (hK'.mul hh)
  exact h

private lemma lineDeficitSlope_deriv {ι : Type*} [Fintype ι]
    (x y m d : ι → ℝ) (a : ℝ)
    (hx : ∀ i,0 ≤ x i) (hy : ∀ i,0 ≤ y i) (hm : ∀ i,0 ≤ m i)
    {K : ℝ} (hK : 0 < K) (hs : (∑ i,m i) = K) :
    let k := ∑ i,d i*m i
    HasDerivAt (lineDeficitSlope x y m d a)
      (-(a*(∑ i,x i*(d i)^2)+(1-a)*(∑ i,y i*(d i)^2)-K*(∑ i,m i*(d i)^2)) -
        2*k*lineSlope m d 0 + 2*k^2*(-log K-1) - k^2) 0 := by
  have hK0 : lineMass m d 0 = K := by simpa using hs
  have hK' : HasDerivAt (lineMass m d) (∑ i,d i*m i) 0 := affine_deriv _ _ _
  have hk0 : lineMass m d 0 ≠ 0 := hK0 ▸ hK.ne'
  have hh := affine_entropy_deriv hK' hk0
  have hh' := (((hK'.log hk0).neg).sub_const 1).const_mul (∑ i,d i*m i)
  have h := (((lineSlope_deriv x d hx).const_mul a).add
    ((lineSlope_deriv y d hy).const_mul (1-a))).sub
      (((entropy_line_deriv m d 0 hm (by simp)).const_mul (∑ i,d i*m i)).add
        (hK'.mul (lineSlope_deriv m d hm))) |>.add
      ((hh.const_mul (∑ i,d i*m i)).add (hK'.mul hh'))
  dsimp only
  convert h using 1 <;> try rfl
  simp only [Pi.neg_apply, hK0]
  field_simp [hK.ne']
  <;> ring

lemma lineDeficit_continuous {ι : Type*} [Fintype ι]
    (x y m d : ι → ℝ) (a : ℝ) : Continuous (lineDeficit x y m d a) := by
  unfold lineDeficit lineMass entropy scaleLine
  fun_prop

lemma lineDeficit_deriv2 {ι : Type*} [Fintype ι] (x y m d : ι → ℝ) (a : ℝ)
    (hx : ∀ i,0 ≤ x i) (hy : ∀ i,0 ≤ y i) (hm : ∀ i,0 ≤ m i)
    {K : ℝ} (hK : 0 < K) (hs : (∑ i,m i) = K) :
    let k := ∑ i,d i*m i
    deriv (deriv (lineDeficit x y m d a)) 0 =
      -(∑ i,(a*x i+(1-a)*y i-K*m i)*(d i)^2) -
        2*k*(∑ i,m i*d i*(-log (m i/K))) - k^2 := by
  have hzero : ContinuousAt (fun _ : ℝ => (0 : ℝ)) 0 := continuousAt_const
  have hqt : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 < 1+t*d i := by
    apply eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun t : ℝ => 1+t*d i) 0 :=
      (affine_deriv 1 (d i) 0).continuousAt
    exact hzero.eventually_lt hc (by simp)
  have hKt : ∀ᶠ t : ℝ in 𝓝 0, 0 < lineMass m d t := by
    have hc : ContinuousAt (lineMass m d) 0 := (affine_deriv _ _ _).continuousAt
    exact hzero.eventually_lt hc (by simpa [hs] using hK)
  have heq : deriv (lineDeficit x y m d a) =ᶠ[𝓝 0] lineDeficitSlope x y m d a := by
    filter_upwards [hqt, hKt] with t hqt hKt
    exact (lineDeficit_deriv x y m d a t hx hy hm hqt hKt).deriv
  let k := ∑ i,d i*m i
  have hslope : lineSlope m d 0 = (∑ i,m i*d i*(-log (m i/K))) + k*(-log K-1) := by
    unfold lineSlope
    rw [scaleLine_zero]
    change (∑ i, d i*m i*(-log (m i)-1)) = _
    dsimp [k]
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rcases (hm i).eq_or_lt with h | h
    · simp [← h]
    · rw [log_div h.ne' hK.ne']
      ring
  have hcoeff :
      (∑ i,(a*x i+(1-a)*y i-K*m i)*(d i)^2) =
        a*(∑ i,x i*(d i)^2)+(1-a)*(∑ i,y i*(d i)^2)-K*(∑ i,m i*(d i)^2) := by
    simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      mul_assoc, Finset.mul_sum]
  change deriv (deriv (lineDeficit x y m d a)) 0 = _
  rw [heq.deriv_eq, (lineDeficitSlope_deriv x y m d a hx hy hm hK hs).deriv, hslope,
    hcoeff]
  change _ - 2*k*(_+k*_) + 2*k^2*_ - k^2 = _ - 2*k*_ - k^2
  ring

end EntropyBridge

end CurvatureSection

section CurvatureSignSection

open scoped BigOperators
open Real Finset

namespace EntropyBridge

private lemma weighted_cs {ι : Type*} [Fintype ι] (w u v : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i,w i*u i*v i)^2 ≤ (∑ i,w i*(u i)^2)*(∑ i,w i*(v i)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq univ
    (fun i => sqrt (w i)*u i) (fun i => sqrt (w i)*v i)
  have hL (i : ι) : (sqrt (w i)*u i)*(sqrt (w i)*v i) = w i*u i*v i := by
    rw [mul_mul_mul_comm, ← sq, sq_sqrt (hw i)]
    ring
  have hR (z : ι → ℝ) (i : ι) : (sqrt (w i)*z i)^2 = w i*(z i)^2 := by
    rw [mul_pow, sq_sqrt (hw i)]
  simpa only [hL, hR] using h

private lemma cross_term_bound {K A B k V : ℝ} (hK0 : 0 ≤ K) (hK1 : K < 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hk : k^2 ≤ (1-K)*A) (hV : V^2 ≤ K*B)
    (hpos : 0 < A+(1-K)*B) :
    -(A+(1-K)*B) < 2*k*V := by
  let C := (1+K)/2
  let D := A+(1-K)*B
  have hcd : 0 ≤ C*D := mul_nonneg (by dsimp [C]; positivity) hpos.le
  have hkV := mul_le_mul hk hV (sq_nonneg V) (by positivity : 0 ≤ (1-K)*A)
  have hD2 : 4*(1-K)*A*B ≤ D^2 := by
    dsimp [D]
    nlinarith only [sq_nonneg (A-(1-K)*B)]
  have hC : K ≤ C^2 := by
    dsimp [C]
    nlinarith only [sq_nonneg (1-K)]
  have hbound : (2*k*V)^2 ≤ (C*D)^2 := calc
    _ ≤ K*(4*(1-K)*A*B) := by nlinarith only [hkV]
    _ ≤ K*D^2 := mul_le_mul_of_nonneg_left hD2 hK0
    _ ≤ C^2*D^2 := mul_le_mul_of_nonneg_right hC (sq_nonneg D)
    _ = _ := by ring
  have habs : |2*k*V| ≤ C*D := by
    apply (sq_le_sq₀ (abs_nonneg _) hcd).mp
    rwa [sq_abs]
  have hsmall : C*D < D := by
    have hC1 : C < 1 := by dsimp [C]; linarith only [hK1]
    simpa using mul_lt_mul_of_pos_right hC1 hpos
  change -D < 2*k*V
  linarith only [neg_abs_le (2*k*V), habs, hsmall]

lemma ternary_line_curvature_negative (x y m d : Fin 3 → ℝ) (a : ℝ)
    (hx : ∀ i,0 ≤ x i) (hy : ∀ i,0 ≤ y i) (hm : ∀ i,0 ≤ m i)
    (hxy : ∀ i,0 < x i+y i)
    (sx : (∑ i,x i)=1) (sy : (∑ i,y i)=1)
    (ha : 0 < a) (hb : 0 < 1-a)
    (hamgm : ∀ i, m i ≤ a*x i+(1-a)*y i)
    (hdx : (∑ i,d i*x i)=0) (hdy : (∑ i,d i*y i)=0) (hd : ∃ i,d i ≠ 0)
    {K : ℝ} (hK : 0 < K) (hK1 : K < 1) (hKsum : (∑ i,m i)=K) :
    deriv (deriv (lineDeficit x y m d a)) 0 < 0 := by
  let δ (i : Fin 3) := a*x i+(1-a)*y i-m i
  let p (i : Fin 3) := m i/K
  let L (i : Fin 3) := -log (p i)
  let H := ∑ i,p i*L i
  let A := ∑ i,δ i*(d i)^2
  let B := ∑ i,m i*(d i)^2
  let k := ∑ i,d i*m i
  let V := ∑ i,m i*d i*(L i-H)
  have hδ (i : Fin 3) : 0 ≤ δ i := sub_nonneg.mpr (hamgm i)
  have hp (i : Fin 3) : 0 ≤ p i := div_nonneg (hm i) hK.le
  have hpM (i : Fin 3) : m i = K*p i := by dsimp [p]; field_simp
  have hp1 : (∑ i,p i) = 1 := by dsimp [p]; rw [← Finset.sum_div, hKsum, div_self hK.ne']
  have hL (i : Fin 3) : p i*L i = negMulLog (p i) := by dsimp [L, negMulLog]; ring
  have hH : 0 ≤ H := by
    dsimp [H]
    simp only [hL]
    apply sum_nonneg
    intro i _
    apply negMulLog_nonneg (hp i)
    rw [← hp1]
    exact single_le_sum (fun j _ => hp j) (mem_univ i)
  have hA : 0 ≤ A := sum_nonneg fun i _ => mul_nonneg (hδ i) (sq_nonneg _)
  have hB : 0 ≤ B := sum_nonneg fun i _ => mul_nonneg (hm i) (sq_nonneg _)
  have hsumδ : (∑ i,δ i)=1-K := by
    simp only [δ, sum_sub_distrib, sum_add_distrib, ← mul_sum, sx, sy, hKsum]
    ring
  have hkδ : (∑ i,δ i*d i) = -k := by
    simp only [δ, sub_mul, add_mul, sum_sub_distrib, sum_add_distrib, mul_assoc, ← mul_sum]
    have hₓ : (∑ i,x i*d i)=0 := by simpa only [mul_comm] using hdx
    have hᵧ : (∑ i,y i*d i)=0 := by simpa only [mul_comm] using hdy
    have hₘ : (∑ i,m i*d i)=k := by simp only [k, mul_comm]
    rw [hₓ,hᵧ,hₘ]
    ring
  have hkBound : k^2 ≤ (1-K)*A := by
    have h := weighted_cs δ d (fun _ => 1) hδ
    simp only [mul_one, one_pow, hkδ, neg_sq, hsumδ] at h
    simpa only [A, mul_comm] using h
  have hvar : (∑ i,m i*(L i-H)^2) ≤ K := by
    have hh := ternary_surprisal_variance p hp hp1
    have h := mul_le_mul_of_nonneg_left hh hK.le
    change K * (∑ i,p i*(L i-H)^2) ≤ K*1 at h
    simp only [mul_one, Finset.mul_sum, ← mul_assoc, ← hpM] at h
    exact h
  have hV : V^2 ≤ K*B := by
    have h := weighted_cs m d (fun i => L i-H) hm
    exact h.trans (by rw [mul_comm K B]; exact mul_le_mul_of_nonneg_left hvar hB)
  have hCoeff :
      (∑ i,(a*x i+(1-a)*y i-K*m i)*(d i)^2) = A+(1-K)*B := by
    dsimp [A,B]
    rw [Finset.mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    dsimp [δ]
    ring
  have hD : 0 < A+(1-K)*B := by
    rw [← hCoeff]
    obtain ⟨i,hi⟩ := hd
    have hstrict (j : Fin 3) : 0 < a*x j+(1-a)*y j-K*m j := by
      have hM : 0 < a*x j+(1-a)*y j := by
        rcases (hx j).eq_or_lt with h | h
        · have hy' : 0 < y j := by linarith only [hxy j,h]
          rw [← h, mul_zero, zero_add]
          exact mul_pos hb hy'
        · exact add_pos_of_pos_of_nonneg (mul_pos ha h) (mul_nonneg hb.le (hy j))
      have h₀ := mul_lt_mul_of_pos_right hK1 hM
      have h₁ := mul_le_mul_of_nonneg_left (hamgm j) hK.le
      linarith only [h₀,h₁]
    exact sum_pos' (fun j _ => mul_nonneg (hstrict j).le (sq_nonneg _))
      ⟨i,mem_univ i,mul_pos (hstrict i) (sq_pos_of_ne_zero hi)⟩
  have hcenter : (∑ i,m i*d i*L i) = V + k*H := by
    dsimp [V,k]
    rw [sum_mul, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [lineDeficit_deriv2 x y m d a hx hy hm hK hKsum, hCoeff]
  change -(A+(1-K)*B) - 2*k*(∑ i,m i*d i*L i) - k^2 < 0
  rw [hcenter]
  have hcross := cross_term_bound hK.le hK1 hA hB hkBound hV hD
  have hl := mul_nonneg hH (sq_nonneg k)
  nlinarith only [hcross, hl, sq_nonneg k]

end EntropyBridge

end CurvatureSignSection

section TernarySection

open scoped Topology BigOperators
open Real Filter Finset Set

namespace EntropyBridge

private noncomputable def deficitFromMass {ι : Type*} [Fintype ι]
    (x y m : ι → ℝ) (a : ℝ) : ℝ :=
  a * entropy x + (1-a) * entropy y -
    (∑ i,m i) * entropy m + (∑ i,m i) * negMulLog (∑ i,m i)

private lemma deficitFromMass_eq_deficit {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) (a : ℝ) (hK : 0 < affinity x y a) :
    deficitFromMass x y (fun i => geom (x i) (y i) a) a = deficit x y a := by
  unfold deficitFromMass deficit
  have h := scaled_entropy_identity (fun i => geom (x i) (y i) a) hK.ne'
    (rfl : (∑ i,geom (x i) (y i) a) = affinity x y a)
  rw [h]
  simp only [affinity]
  ring

private lemma ternary_boundary (x y : Fin 3 → ℝ) (a : ℝ) (i : Fin 3)
    (hx : ∀ j,0 ≤ x j) (hy : ∀ j,0 ≤ y j) (hxi : x i=0) (hyi : y i=0)
    (sx : (∑ j,x j)=1) (sy : (∑ j,y j)=1)
    (ha : 0 < a) (hb : 0 < 1-a) (hK : 0 < affinity x y a) :
    0 ≤ deficit x y a := by
  let X (j : Fin 2) := x (i.succAbove j)
  let Y (j : Fin 2) := y (i.succAbove j)
  have hsum (f : ℝ → ℝ → ℝ) (hf : f 0 0 = 0) :
      (∑ j,f (x j) (y j)) = ∑ j,f (X j) (Y j) := by
    rw [Fin.sum_univ_succAbove _ i, hxi, hyi, hf, zero_add]
  have hsX := (hsum (fun x _ => x) rfl).symm.trans sx
  have hsY := (hsum (fun _ y => y) rfl).symm.trans sy
  have hg : geom 0 0 a = 0 := by simp [geom, Real.zero_rpow ha.ne']
  have hAff : affinity x y a = affinity X Y a := hsum (fun x y => geom x y a) hg
  have hd : deficit x y a = deficit X Y a := by
    unfold deficit entropy
    rw [hAff, hsum (fun x _ => negMulLog x) negMulLog_zero,
      hsum (fun _ y => negMulLog y) negMulLog_zero,
      hsum (fun x y => negMulLog (geom x y a / affinity X Y a)) (by simp [hg])]
  rw [hd]
  exact binary_target X Y a (fun j => hx _) (fun j => hy _) hsX hsY ha.le
    (by linarith only [hb]) (hAff ▸ hK)

private lemma not_local_min_of_deriv2_negative {f : ℝ → ℝ}
    (hf : ContinuousAt f 0) (hneg : deriv (deriv f) 0 < 0) : ¬ IsLocalMin f 0 := by
  intro hmin
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hf
  have hconst : f =ᶠ[𝓝 0] (fun _ : ℝ => f 0) := by
    filter_upwards [hmin, hmax] with t h₁ h₂
    exact le_antisymm h₂ h₁
  have h := hconst.deriv.deriv_eq
  simp at h
  exact hneg.ne h

theorem ternary_target (x y : Fin 3 → ℝ) (a : ℝ)
    (hx : ∀ i,0 ≤ x i) (hy : ∀ i,0 ≤ y i)
    (sx : (∑ i,x i)=1) (sy : (∑ i,y i)=1)
    (ha : 0 ≤ a) (ha' : a ≤ 1) (hK : 0 < affinity x y a) :
    0 ≤ deficit x y a := by
  classical
  by_cases ha0 : a = 0
  · subst a
    simp [deficit, affinity, geom, sy]
  by_cases ha1 : a = 1
  · subst a
    simp [deficit, affinity, geom, sx]
  have ha0' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb : 0 < 1-a := sub_pos.mpr (lt_of_le_of_ne ha' ha1)
  by_cases hzero : ∃ i, x i = 0 ∧ y i = 0
  · obtain ⟨i,hxi,hyi⟩ := hzero
    exact ternary_boundary x y a i hx hy hxi hyi sx sy ha0' hb hK
  have hxy (i : Fin 3) : 0 < x i+y i := by
    by_contra! h
    exact hzero ⟨i,by linarith only [h,hx i,hy i],by linarith only [h,hx i,hy i]⟩
  let m (i : Fin 3) := geom (x i) (y i) a
  let X (q : Fin 3 → ℝ) (i : Fin 3) := q i*x i
  let Y (q : Fin 3 → ℝ) (i : Fin 3) := q i*y i
  let M (q : Fin 3 → ℝ) (i : Fin 3) := q i*m i
  let F (q : Fin 3 → ℝ) := deficitFromMass (X q) (Y q) (M q) a
  let S := Set.Icc (0 : Fin 3 → ℝ) (fun i => 2/(x i+y i)) ∩
    ({q | (∑ i, X q i)=1} ∩ {q | (∑ i,Y q i)=1})
  have hm (i : Fin 3) : 0 ≤ m i :=
    mul_nonneg (rpow_nonneg (hx i) _) (rpow_nonneg (hy i) _)
  have memS (q : Fin 3 → ℝ) (hq : ∀ i,0 ≤ q i)
      (hxq : (∑ i,X q i)=1) (hyq : (∑ i,Y q i)=1) : q ∈ S := by
    have hmass : (∑ i,q i*(x i+y i)) = 2 := by
      simp only [mul_add, sum_add_distrib]
      change (∑ i,X q i)+(∑ i,Y q i) = 2
      rw [hxq,hyq]
      norm_num
    refine ⟨⟨hq,fun i => ?_⟩,hxq,hyq⟩
    apply (le_div_iff₀ (hxy i)).mpr
    rw [← hmass]
    exact single_le_sum (fun j _ => mul_nonneg (hq j) (hxy j).le) (mem_univ i)
  have hF : Continuous F := by
    unfold F deficitFromMass entropy X Y M
    fun_prop
  have hX : Continuous (fun q => ∑ i,X q i) := by unfold X; fun_prop
  have hY : Continuous (fun q => ∑ i,Y q i) := by unfold Y; fun_prop
  have hS : IsCompact S := isCompact_Icc.inter_right
    ((isClosed_singleton.preimage hX).inter (isClosed_singleton.preimage hY))
  have hOne : (fun _ => (1:ℝ)) ∈ S :=
    memS _ (fun _ => zero_le_one) (by simpa [X] using sx) (by simpa [Y] using sy)
  obtain ⟨q,hq,hmin⟩ := hS.exists_isMinOn ⟨_,hOne⟩ hF.continuousOn
  have hFone : F (fun _ => 1) = deficit x y a := by
    simpa [F,X,Y,M,m] using deficitFromMass_eq_deficit x y a hK
  by_contra! hbad
  have hminneg : F q < 0 := by
    have h := hmin hOne
    change F q ≤ F (fun _ => 1) at h
    rw [hFone] at h
    exact h.trans_lt hbad
  have hq0 (i : Fin 3) : 0 ≤ q i := hq.1.1 i
  have hXq (i : Fin 3) : 0 ≤ X q i := mul_nonneg (hq0 i) (hx i)
  have hYq (i : Fin 3) : 0 ≤ Y q i := mul_nonneg (hq0 i) (hy i)
  have hMq (i : Fin 3) : 0 ≤ M q i := mul_nonneg (hq0 i) (hm i)
  have sxq : (∑ i,X q i)=1 := hq.2.1
  have syq : (∑ i,Y q i)=1 := hq.2.2
  have hgeom (i : Fin 3) : geom (X q i) (Y q i) a = M q i :=
    geom_smul _ _ _ _ (hq0 i) (hx i) (hy i) ha hb.le
  let K := affinity (X q) (Y q) a
  have hsumK : (∑ i,M q i)=K := by simp only [K,affinity,hgeom]
  have hKq : 0 < K := by
    by_contra! h
    have h₀ : 0 ≤ K := hsumK ▸ sum_nonneg fun i _ => hMq i
    have heq := le_antisymm h h₀
    have hf : F q = a*entropy (X q)+(1-a)*entropy (Y q) := by
      simp [F,deficitFromMass,hsumK,heq]
    rw [hf] at hminneg
    exact (not_lt_of_ge (add_nonneg (mul_nonneg ha (entropy_nonneg_prob _ hXq sxq))
      (mul_nonneg hb.le (entropy_nonneg_prob _ hYq syq)))) hminneg
  have hfq : F q = deficit (X q) (Y q) a := by
    simpa only [hgeom] using deficitFromMass_eq_deficit (X q) (Y q) a hKq
  have hKlt : K < 1 := by
    have hle := affinity_le_one (X q) (Y q) hXq hYq sxq syq ha hb.le
    rcases hle.eq_or_lt with he | hh
    · have hxyeq := equal_of_affinity_one (X q) (Y q) a hXq hYq sxq syq ha0' hb he
      have hh (i : Fin 3) : geom (X q i) (X q i) a = X q i := by
        unfold geom
        rw [← rpow_add_of_nonneg (hXq i) ha hb.le,show a+(1-a)=1 by ring,rpow_one]
      rw [hfq,← hxyeq] at hminneg
      simp only [deficit,affinity,hh,sxq,one_pow,div_one,one_mul] at hminneg
      linarith only [hminneg]
    · exact hh
  have hXqYq (i : Fin 3) : 0 < X q i+Y q i := by
    by_contra! hh
    have h₁ : X q i=0 := by linarith only [hh,hXq i,hYq i]
    have h₂ : Y q i=0 := by linarith only [hh,hXq i,hYq i]
    have h := ternary_boundary (X q) (Y q) a i hXq hYq h₁ h₂ sxq syq ha0' hb hKq
    rw [← hfq] at h
    exact (not_lt_of_ge h) hminneg
  let v (i : Fin 3) : Fin 2 → ℝ := ![X q i, Y q i]
  have hDep : ¬LinearIndependent ℝ v := by
    intro h
    have hh := h.fintype_card_le_finrank
    simpa [Module.finrank_fintype_fun_eq_card] using hh
  obtain ⟨d,hdv,hd⟩ := Fintype.not_linearIndependent_iff.mp hDep
  have hdx : (∑ i,d i*X q i)=0 := by
    have h := congrFun hdv (0 : Fin 2)
    simpa [Finset.sum_apply,v] using h
  have hdy : (∑ i,d i*Y q i)=0 := by
    have h := congrFun hdv (1 : Fin 2)
    simpa [Finset.sum_apply,v] using h
  have hamgm (i : Fin 3) : M q i ≤ a*X q i+(1-a)*Y q i := by
    rw [← hgeom]
    exact geom_mean_le_arith_mean2_weighted ha hb.le (hXq i) (hYq i) (by ring)
  have hcurv := ternary_line_curvature_negative (X q) (Y q) (M q) d a hXq hYq hMq
    hXqYq sxq syq ha0' hb hamgm hdx hdy hd hKq hKlt hsumK
  have hforbid := not_local_min_of_deriv2_negative
    (lineDeficit_continuous (X q) (Y q) (M q) d a).continuousAt hcurv
  apply hforbid
  let q' := scaleLine q d
  have hX' (t : ℝ) : X (q' t) = scaleLine (X q) d t := by ext i; simp only [X,q',scaleLine,mul_assoc]
  have hY' (t : ℝ) : Y (q' t) = scaleLine (Y q) d t := by ext i; simp only [Y,q',scaleLine,mul_assoc]
  have hM' (t : ℝ) : M (q' t) = scaleLine (M q) d t := by ext i; simp only [M,q',scaleLine,mul_assoc]
  have hline (t : ℝ) : F (q' t) = lineDeficit (X q) (Y q) (M q) d a t := by
    unfold F deficitFromMass lineDeficit lineMass
    rw [hX',hY',hM',scaleLine_mass]
  change ∀ᶠ t : ℝ in 𝓝 0, lineDeficit (X q) (Y q) (M q) d a 0 ≤
      lineDeficit (X q) (Y q) (M q) d a t
  have hc0 : ContinuousAt (fun _ : ℝ => (0:ℝ)) 0 := continuousAt_const
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ i,0 < 1+t*d i := by
    apply eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun t : ℝ => 1+t*d i) 0 := by fun_prop
    exact hc0.eventually_lt hc (by simp)
  filter_upwards [hnear] with t ht
  rw [← hline 0,← hline t,show q' 0=q from scaleLine_zero _ _]
  apply hmin
  apply memS _ (fun i => mul_nonneg (ht i).le (hq0 i))
  · change (∑ i, X (q' t) i) = 1
    rw [hX', scaleLine_mass, sxq, hdx, mul_zero, add_zero]
  · change (∑ i, Y (q' t) i) = 1
    rw [hY', scaleLine_mass, syq, hdy, mul_zero, add_zero]

end EntropyBridge

end TernarySection

section SolutionTailSection

namespace EntropyBridge

lemma all_small (n : ℕ) (hn : n ≤ 3) (x y : Fin n → ℝ) (a : ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (sx : (∑ i,x i)=1) (sy : (∑ i,y i)=1)
    (ha : 0 ≤ a) (ha' : a ≤ 1) (hK : 0 < affinity x y a) : 0 ≤ deficit x y a := by
  rcases (show n=0 ∨ n=1 ∨ n=2 ∨ n=3 by omega) with rfl | rfl | rfl | rfl
  · simp at sx
  · have hx' : x = fun _ => 1 := by
      ext i
      fin_cases i
      simpa [Fin.sum_univ_one] using sx
    have hy' : y = fun _ => 1 := by
      ext i
      fin_cases i
      simpa [Fin.sum_univ_one] using sy
    rw [hx', hy']
    simp [deficit, affinity, geom, entropy]
  · exact binary_target x y a hx hy sx sy ha ha' hK
  · exact ternary_target x y a hx hy sx sy ha ha' hK

end EntropyBridge

theorem OMA.solution : type_of% @OMA.S_mo_138395.main := by
  intro n X Y hX sX hY sY α hα hα' hK
  exact sub_nonneg.mp
    (EntropyBridge.all_of_fin_le_three EntropyBridge.all_small n X Y α hX hY sX sY hα hα' hK)

end SolutionTailSection
