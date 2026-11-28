import OMAReductions.R_Green72_no_k_in_line_big_R1
import Mathlib

/-!
# Large-parameter no-k-in-line theorem (Grebennikov--Kwan)

This file proves `OMA.R_Green72_no_k_in_line_big_R1.H1`: for every `k > 10^37` and `N ≥ k`,
there exists a subset `s ⊆ [0, N)^2` of size `(k - 1) * N` with at most `k - 1` points on
every integer line.

Following Grebennikov and Kwan, *No-(k+1)-in-line problem for large constant k*
(arXiv:2510.17743), together with the block-reduction and grid-adjustment framework of
Kovács, Nagy, and Szabó (arXiv:2502.00176):

1. Elementary real inequalities, Ore--Ryser's criterion for `k`-regular spanning bipartite
   subgraphs (proved via augmenting paths), and Kőnig 1-factor peeling.
2. Discrete grid lines and the polynomial-tails bound `≤ 18 / α^2` on lines of weight `≥ α`
   through any grid point.
3. Finite discrete probability distributions on `Finset.powerset`, independent Bernoulli
   subsampling, Chernoff bounds, and the conditional Lovász Local Lemma.
4. Iterative subsampling of spread distributions on nice sets and regularisation via
   Ore--Ryser, proving the relaxed theorem for `10^36 ≤ r ≤ 0.9 * n`.
5. Derivation of the exact bound for `10^37 ≤ r ≤ N` using the explicit complement
   construction when `r ≥ 2N/3` and the `4 × 4` block decomposition plus `(r, N)` adjustments
   when `r < 2N/3`.
-/

namespace Green72H1

open Finset

/- ## Section 1: Elementary Real and Combinatorial Inequalities -/

lemma choose_le_exp_pow (m r : ℕ) (hr : 0 < r) :
    (m.choose r : ℝ) ≤ (Real.exp 1 * (m : ℝ) / (r : ℝ)) ^ r := by
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hfac_pos : (0 : ℝ) < (r.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos r)
  have h1 : (m.choose r : ℝ) * (r.factorial : ℝ) ≤ (m : ℝ) ^ r := by
    have hnat : m.choose r * r.factorial ≤ m ^ r := by
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow m r
    exact_mod_cast hnat
  have h2 : (r : ℝ) ^ r / (r.factorial : ℝ) ≤ Real.exp (r : ℝ) := by
    simpa [Real.exp_eq_exp_ℝ] using
      Real.sum_le_exp_of_nonneg (Nat.cast_nonneg r) (r + 1) |> fun h =>
        (Finset.single_le_sum (f := fun i => (r : ℝ) ^ i / (i.factorial : ℝ))
          (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self r))).trans h
  have h3 : (r : ℝ) ^ r ≤ (r.factorial : ℝ) * Real.exp (r : ℝ) := by
    rwa [div_le_iff₀ hfac_pos, mul_comm] at h2
  have hexp : Real.exp (r : ℝ) = (Real.exp 1) ^ r := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [hexp] at h3
  rw [div_pow, mul_pow, le_div_iff₀ (pow_pos hr_pos r)]
  have hmul : (m.choose r : ℝ) * (r : ℝ) ^ r * (r.factorial : ℝ) ≤
      (Real.exp 1) ^ r * (m : ℝ) ^ r * (r.factorial : ℝ) := by
    calc (m.choose r : ℝ) * (r : ℝ) ^ r * (r.factorial : ℝ)
        = ((m.choose r : ℝ) * (r.factorial : ℝ)) * (r : ℝ) ^ r := by ring
      _ ≤ (m : ℝ) ^ r * ((r.factorial : ℝ) * (Real.exp 1) ^ r) :=
          mul_le_mul h1 h3 (pow_nonneg hr_pos.le r) (pow_nonneg (Nat.cast_nonneg m) r)
      _ = (Real.exp 1) ^ r * (m : ℝ) ^ r * (r.factorial : ℝ) := by ring
  exact le_of_mul_le_mul_right hmul hfac_pos

lemma log_one_add_ge_two_div {x : ℝ} (hx : 0 ≤ x) :
    2 * x / (2 + x) ≤ Real.log (1 + x) := by
  let f : ℝ → ℝ := fun t => Real.log (1 + t) - 2 * t / (2 + t)
  have hf0 : f 0 = 0 := by simp [f]
  have hderiv : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt f (t ^ 2 / ((1 + t) * (2 + t) ^ 2)) t := by
    intro t ht
    have h1 : (1 : ℝ) + t ≠ 0 := by linarith [Set.mem_Ici.mp ht]
    have h2 : (2 : ℝ) + t ≠ 0 := by linarith [Set.mem_Ici.mp ht]
    have hd1 : HasDerivAt (fun s => Real.log (1 + s)) (1 / (1 + t)) t := by
      simpa using ((hasDerivAt_id t).const_add (1 : ℝ)).log h1
    have hd2 : HasDerivAt (fun s => 2 * s / (2 + s)) (4 / (2 + t) ^ 2) t := by
      have hnum : HasDerivAt (fun s => (2 : ℝ) * s) 2 t := by
        simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
      have hden : HasDerivAt (fun s => (2 : ℝ) + s) 1 t := by
        simpa using (hasDerivAt_id t).const_add (2 : ℝ)
      refine (hnum.div hden h2).congr_deriv ?_
      field_simp [h2]
      ring
    refine (hd1.sub hd2).congr_deriv ?_
    field_simp [h1, h2]
    ring
  have hmono : MonotoneOn f (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Set.Ici (0 : ℝ) := interior_subset ht
      rw [(hderiv t ht').deriv]
      have : 0 < (1 + t) * (2 + t) ^ 2 := by
        have : 0 ≤ t := ht'
        positivity
      positivity
  have hle := hmono (Set.self_mem_Ici) hx hx
  rw [hf0] at hle
  dsimp [f] at hle
  linarith

lemma chernoff_log_upper {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    δ ^ 2 / 3 ≤ (1 + δ) * Real.log (1 + δ) - δ := by
  have hlog := log_one_add_ge_two_div hδ0
  have h2 : 0 < 2 + δ := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlog (by linarith : (0 : ℝ) ≤ 1 + δ)
  have hdiff : (1 + δ) * (2 * δ / (2 + δ)) - δ = δ ^ 2 / (2 + δ) := by
    field_simp [h2.ne']
    ring
  have h3 : δ ^ 2 / 3 ≤ δ ^ 2 / (2 + δ) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) h2]
    nlinarith [sq_nonneg δ]
  linarith

lemma chernoff_log_lower {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    δ ^ 2 / 3 ≤ (1 - δ) * Real.log (1 - δ) + δ := by
  let f : ℝ → ℝ := fun t => (1 - t) * Real.log (1 - t) + t - t ^ 2 / 2
  have hf0 : f 0 = 0 := by simp [f]
  have hderiv : ∀ t ∈ Set.Ico (0 : ℝ) 1, HasDerivAt f (-Real.log (1 - t) - t) t := by
    intro t ht
    have h1 : 0 < 1 - t := by linarith [ht.2]
    have hd_sub : HasDerivAt (fun s => (1 : ℝ) - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
    have hd_log : HasDerivAt (fun s => Real.log (1 - s)) (-1 / (1 - t)) t := by
      simpa using hd_sub.log h1.ne'
    have hd_prod : HasDerivAt (fun s => (1 - s) * Real.log (1 - s))
        ((-1) * Real.log (1 - t) + (1 - t) * (-1 / (1 - t))) t := hd_sub.mul hd_log
    have hd_sq : HasDerivAt (fun s => s ^ 2 / 2) t t := by
      refine ((hasDerivAt_pow 2 t).div_const (2 : ℝ)).congr_deriv ?_
      ring
    refine ((hd_prod.add (hasDerivAt_id t)).sub hd_sq).congr_deriv ?_
    field_simp [h1.ne']
    ring
  have hmono : MonotoneOn f (Set.Ico (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
    · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Set.Ico (0 : ℝ) 1 := interior_subset ht
      rw [(hderiv t ht').deriv]
      have hlog : Real.log (1 - t) ≤ -t := by
        have := Real.log_le_sub_one_of_pos (by linarith [ht'.2] : 0 < 1 - t)
        linarith
      linarith
  have hle := hmono ⟨le_rfl, zero_lt_one⟩ ⟨hδ0, hδ1⟩ hδ0
  rw [hf0] at hle
  dsimp [f] at hle
  nlinarith [sq_nonneg δ]

lemma one_sub_mul_exp_three_ge_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    1 ≤ (1 - x) * Real.exp (3 * x) := by
  have hexp : 1 + 3 * x ≤ Real.exp (3 * x) := by
    linarith [Real.add_one_le_exp (3 * x)]
  have hmul : (1 - x) * (1 + 3 * x) ≤ (1 - x) * Real.exp (3 * x) :=
    mul_le_mul_of_nonneg_left hexp (by linarith)
  nlinarith [sq_nonneg x]

lemma exp_sq_div_13_ge {u : ℝ} (hu : 1000 ≤ u) :
    2 * (5 * u ^ 12) ^ 15 ≤ Real.exp (u ^ 2 / 13) := by
  have hu0 : 0 ≤ u := by linarith
  have hbase : u ^ 2 / 4680 ≤ Real.exp (u ^ 2 / 4680) := by
    linarith [Real.add_one_le_exp (u ^ 2 / 4680)]
  have hpow : (u ^ 2 / 4680) ^ 360 ≤ Real.exp (u ^ 2 / 13) := by
    calc (u ^ 2 / 4680) ^ 360
        ≤ (Real.exp (u ^ 2 / 4680)) ^ 360 := pow_le_pow_left₀ (by positivity) hbase 360
      _ = Real.exp (360 * (u ^ 2 / 4680)) := (Real.exp_nat_mul _ 360).symm
      _ = Real.exp (u ^ 2 / 13) := by congr 1; ring
  have hcube : (2 : ℝ) ≤ u ^ 3 / (4680 : ℝ) ^ 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (4680 : ℝ) ^ 2)]
    have : (1000 : ℝ) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
    linarith
  have hpow2 : (2 : ℝ) ^ 180 ≤ (u ^ 3 / (4680 : ℝ) ^ 2) ^ 180 :=
    pow_le_pow_left₀ (by norm_num) hcube 180
  have hcoef : (2 : ℝ) * (5 : ℝ) ^ 15 ≤ (2 : ℝ) ^ 180 := by norm_num
  calc 2 * (5 * u ^ 12) ^ 15
      = (2 * (5 : ℝ) ^ 15) * u ^ 180 := by ring
    _ ≤ (2 : ℝ) ^ 180 * u ^ 180 := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hu0 180)
    _ ≤ (u ^ 3 / (4680 : ℝ) ^ 2) ^ 180 * u ^ 180 :=
        mul_le_mul_of_nonneg_right hpow2 (pow_nonneg hu0 180)
    _ = ((u ^ 3 / (4680 : ℝ) ^ 2) * u) ^ 180 := (mul_pow _ _ 180).symm
    _ = ((u ^ 2 / 4680) ^ 2) ^ 180 := by congr 1; ring
    _ = (u ^ 2 / 4680) ^ 360 := by rw [← pow_mul]
    _ ≤ Real.exp (u ^ 2 / 13) := hpow

lemma geom_sum_quarter_lt_half (M : ℕ) :
    ∑ b ∈ Finset.Icc 1 M, ((1 : ℝ) / 4) ^ b < 1 / 2 := by
  have h1 : ∑ b ∈ Finset.Icc 1 M, ((1 : ℝ) / 4) ^ b =
      (∑ b ∈ Finset.range (M + 1), ((1 : ℝ) / 4) ^ b) - 1 := by
    rw [Finset.sum_range_eq_add_Ico _ (Nat.succ_pos M)]
    have hIco : Finset.Ico 1 (M + 1) = Finset.Icc 1 M := rfl
    rw [hIco, pow_zero]
    ring
  rw [h1, geom_sum_eq (by norm_num : ((1 : ℝ) / 4) ≠ 1)]
  have hpos : (0 : ℝ) ≤ ((1 : ℝ) / 4) ^ (M + 1) := by positivity
  have halg : (((1 : ℝ) / 4) ^ (M + 1) - 1) / (1 / 4 - 1) - 1 =
      1 / 3 - 4 / 3 * ((1 : ℝ) / 4) ^ (M + 1) := by ring
  linarith

/- ## Section 2: Bipartite Regular Subgraphs (Ore--Ryser and Kőnig Peeling) -/

def degL (H : Finset (ℕ × ℕ)) (x : ℕ) : ℕ :=
  (H.filter (fun p => p.1 = x)).card

def degR (H : Finset (ℕ × ℕ)) (y : ℕ) : ℕ :=
  (H.filter (fun p => p.2 = y)).card

def IsKRegular (n k : ℕ) (H : Finset (ℕ × ℕ)) : Prop :=
  H ⊆ range n ×ˢ range n ∧
  (∀ x ∈ range n, degL H x = k) ∧
  (∀ y ∈ range n, degR H y = k)

lemma card_eq_sum_degL {n : ℕ} {H : Finset (ℕ × ℕ)} (hH : H ⊆ range n ×ˢ range n) :
    H.card = ∑ x ∈ range n, degL H x :=
  Finset.card_eq_sum_card_fiberwise fun _ hp => (Finset.mem_product.mp (hH hp)).1

lemma card_eq_sum_degR {n : ℕ} {H : Finset (ℕ × ℕ)} (hH : H ⊆ range n ×ˢ range n) :
    H.card = ∑ y ∈ range n, degR H y :=
  Finset.card_eq_sum_card_fiberwise fun _ hp => (Finset.mem_product.mp (hH hp)).2

lemma isKRegular_card {n k : ℕ} {H : Finset (ℕ × ℕ)} (h : IsKRegular n k H) :
    H.card = k * n := by
  rw [card_eq_sum_degL h.1]
  calc ∑ x ∈ range n, degL H x = ∑ _x ∈ range n, k := Finset.sum_congr rfl fun x hx => h.2.1 x hx
    _ = k * n := by simp [mul_comm]

lemma card_filter_prod_eq_sum_degL {H : Finset (ℕ × ℕ)} (A : Finset ℕ) :
    (H.filter (fun p => p.1 ∈ A)).card = ∑ x ∈ A, degL H x := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := H.filter (fun p => p.1 ∈ A))
    (t := A) (fun _ hp => (Finset.mem_filter.mp hp).2)]
  refine Finset.sum_congr rfl fun x hx => ?_
  congr 1
  ext p
  simp only [Finset.mem_filter]
  exact ⟨fun ⟨⟨hp, _⟩, hpx⟩ => ⟨hp, hpx⟩, fun ⟨hp, hpx⟩ => ⟨⟨hp, hpx ▸ hx⟩, hpx⟩⟩

lemma card_filter_prod_eq_sum_degR {H : Finset (ℕ × ℕ)} (B : Finset ℕ) :
    (H.filter (fun p => p.2 ∈ B)).card = ∑ y ∈ B, degR H y := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (s := H.filter (fun p => p.2 ∈ B))
    (t := B) (fun _ hp => (Finset.mem_filter.mp hp).2)]
  refine Finset.sum_congr rfl fun y hy => ?_
  congr 1
  ext p
  simp only [Finset.mem_filter]
  exact ⟨fun ⟨⟨hp, _⟩, hpy⟩ => ⟨hp, hpy⟩, fun ⟨hp, hpy⟩ => ⟨⟨hp, hpy ▸ hy⟩, hpy⟩⟩

private def bfsLayer (n : ℕ) (S H : Finset (ℕ × ℕ)) (a₀ : ℕ) :
    ℕ → Finset ℕ × Finset ℕ
  | 0 => ({a₀}, ∅)
  | t + 1 =>
    let prev := bfsLayer n S H a₀ t
    let B' := prev.2 ∪ (range n).filter (fun b => ∃ a ∈ prev.1, (a, b) ∈ S \ H)
    let A' := prev.1 ∪ (range n).filter (fun a => ∃ b ∈ B', (a, b) ∈ H)
    (A', B')

private lemma mem_bfsB_succ {n : ℕ} {S H : Finset (ℕ × ℕ)} {a₀ t b : ℕ} :
    b ∈ (bfsLayer n S H a₀ (t + 1)).2 ↔
      b ∈ (bfsLayer n S H a₀ t).2 ∨
      (b ∈ range n ∧ ∃ a ∈ (bfsLayer n S H a₀ t).1, (a, b) ∈ S \ H) := by
  simp only [bfsLayer, Finset.mem_union, Finset.mem_filter]

private lemma mem_bfsA_succ {n : ℕ} {S H : Finset (ℕ × ℕ)} {a₀ t a : ℕ} :
    a ∈ (bfsLayer n S H a₀ (t + 1)).1 ↔
      a ∈ (bfsLayer n S H a₀ t).1 ∨
      (a ∈ range n ∧ ∃ b ∈ (bfsLayer n S H a₀ (t + 1)).2, (a, b) ∈ H) := by
  simp only [bfsLayer, Finset.mem_union, Finset.mem_filter]

private lemma bfsLayer_subset (n : ℕ) (S H : Finset (ℕ × ℕ)) (a₀ : ℕ) (ha₀ : a₀ ∈ range n) :
    ∀ t, (bfsLayer n S H a₀ t).1 ⊆ range n ∧ (bfsLayer n S H a₀ t).2 ⊆ range n
  | 0 => ⟨Finset.singleton_subset_iff.mpr ha₀, Finset.empty_subset _⟩
  | t + 1 => by
    have ih := bfsLayer_subset n S H a₀ ha₀ t
    simp only [bfsLayer]
    exact ⟨Finset.union_subset ih.1 (Finset.filter_subset _ _),
      Finset.union_subset ih.2 (Finset.filter_subset _ _)⟩

private lemma bfsLayer_mono (n : ℕ) (S H : Finset (ℕ × ℕ)) (a₀ : ℕ) :
    ∀ t, (bfsLayer n S H a₀ t).1 ⊆ (bfsLayer n S H a₀ (t + 1)).1 ∧
         (bfsLayer n S H a₀ t).2 ⊆ (bfsLayer n S H a₀ (t + 1)).2 := by
  intro t
  simp only [bfsLayer]
  exact ⟨Finset.subset_union_left, Finset.subset_union_left⟩

private lemma bfsLayer_mono_le (n : ℕ) (S H : Finset (ℕ × ℕ)) (a₀ : ℕ) {s t : ℕ} (hst : s ≤ t) :
    (bfsLayer n S H a₀ s).1 ⊆ (bfsLayer n S H a₀ t).1 ∧
    (bfsLayer n S H a₀ s).2 ⊆ (bfsLayer n S H a₀ t).2 := by
  induction hst with
  | refl => exact ⟨Subset.rfl, Subset.rfl⟩
  | @step m _ ih =>
    have hm := bfsLayer_mono n S H a₀ m
    exact ⟨ih.1.trans hm.1, ih.2.trans hm.2⟩

private lemma bfsLayer_stable (n : ℕ) (S H : Finset (ℕ × ℕ)) (a₀ : ℕ) {t : ℕ}
    (hEq : (bfsLayer n S H a₀ (t + 1)).1 = (bfsLayer n S H a₀ t).1) :
    (bfsLayer n S H a₀ (t + 1)).2 = (bfsLayer n S H a₀ (t + 2)).2 ∧
    (bfsLayer n S H a₀ (t + 1)).1 = (bfsLayer n S H a₀ (t + 2)).1 := by
  have hB : (bfsLayer n S H a₀ (t + 2)).2 = (bfsLayer n S H a₀ (t + 1)).2 := by
    apply Finset.Subset.antisymm
    · intro b hb
      rcases mem_bfsB_succ.mp hb with hb | ⟨hbn, a, ha, hab⟩
      · exact hb
      · rw [hEq] at ha
        exact mem_bfsB_succ.mpr (Or.inr ⟨hbn, a, ha, hab⟩)
    · exact (bfsLayer_mono n S H a₀ (t + 1)).2
  have hA : (bfsLayer n S H a₀ (t + 2)).1 = (bfsLayer n S H a₀ (t + 1)).1 := by
    apply Finset.Subset.antisymm
    · intro a ha
      rcases mem_bfsA_succ.mp ha with ha | ⟨han, b, hb, hab⟩
      · exact ha
      · rw [hB] at hb
        exact mem_bfsA_succ.mpr (Or.inr ⟨han, b, hb, hab⟩)
    · exact (bfsLayer_mono n S H a₀ (t + 1)).1
  exact ⟨hB.symm, hA.symm⟩

private lemma bfsLayer_fixed (n : ℕ) (S H : Finset (ℕ × ℕ)) (a₀ : ℕ) (ha₀ : a₀ ∈ range n) :
    (bfsLayer n S H a₀ (n + 1)).1 = (bfsLayer n S H a₀ n).1 ∧
    (bfsLayer n S H a₀ (n + 1)).2 = (bfsLayer n S H a₀ n).2 := by
  have hex : ∃ t < n, (bfsLayer n S H a₀ (t + 1)).1 = (bfsLayer n S H a₀ t).1 := by
    by_contra hno
    push Not at hno
    have hgrow : ∀ t ≤ n, t + 1 ≤ (bfsLayer n S H a₀ t).1.card := by
      intro t ht
      induction t with
      | zero => simp [bfsLayer]
      | succ t ih =>
        have hlt : (bfsLayer n S H a₀ t).1 ⊂ (bfsLayer n S H a₀ (t + 1)).1 :=
          Finset.ssubset_iff_subset_ne.mpr
            ⟨(bfsLayer_mono n S H a₀ t).1, (hno t (by omega)).symm⟩
        have hcard := Finset.card_lt_card hlt
        have := ih (by omega)
        omega
    have hle : (bfsLayer n S H a₀ n).1.card ≤ n := by
      simpa using Finset.card_le_card (bfsLayer_subset n S H a₀ ha₀ n).1
    have hge := hgrow n le_rfl
    omega
  obtain ⟨t, ht, hEq⟩ := hex
  have hstay : ∀ m, (bfsLayer n S H a₀ (t + m + 1)).1 = (bfsLayer n S H a₀ (t + m)).1 ∧
      (bfsLayer n S H a₀ (t + m + 2)).2 = (bfsLayer n S H a₀ (t + m + 1)).2 := by
    intro m
    induction m with
    | zero =>
      have hst := bfsLayer_stable n S H a₀ hEq
      exact ⟨hEq, hst.1.symm⟩
    | succ m ih =>
      have hst := bfsLayer_stable n S H a₀ ih.1
      have hst2 := bfsLayer_stable n S H a₀ hst.2.symm
      exact ⟨hst.2.symm, hst2.1.symm⟩
  have hA := (hstay (n - t)).1
  have hB := (hstay (n - 1 - t)).2
  rw [show t + (n - t) = n by omega] at hA
  rw [show t + (n - 1 - t) + 1 = n by omega, show t + (n - 1 - t) + 2 = n + 1 by omega] at hB
  exact ⟨hA, hB⟩

/-- From a shortest alternating path in `bfsLayer` ending at `b ∈ B t` with `degR H b < k`,
construct a strictly larger valid subgraph `H' ⊆ S`. -/
private lemma bfs_augment {n k a₀ : ℕ} {S H : Finset (ℕ × ℕ)} (hS : S ⊆ range n ×ˢ range n)
    (hHS : H ⊆ S) (ha₀ : a₀ ∈ range n) (hdegA₀ : degL H a₀ < k)
    (hdegL : ∀ x ∈ range n, degL H x ≤ k) (hdegR : ∀ y ∈ range n, degR H y ≤ k)
    {t : ℕ} (ht : 1 ≤ t) {b : ℕ} (hb : b ∈ (bfsLayer n S H a₀ t).2)
    (hmin : ∀ s < t, ∀ y ∈ (bfsLayer n S H a₀ s).2, degR H y = k)
    (hdegb : degR H b < k) :
    ∃ H' ⊆ S, (∀ x ∈ range n, degL H' x ≤ k) ∧ (∀ y ∈ range n, degR H' y ≤ k) ∧
      H.card < H'.card := by
  classical
  -- Backtrack sequences `as : Fin t → ℕ` and `bs : Fin t → ℕ` in strictly decreasing layers
  have hchain : ∀ s (hs : 1 ≤ s), ∀ y ∈ (bfsLayer n S H a₀ s).2,
      (∀ r < s, y ∉ (bfsLayer n S H a₀ r).2) →
      ∃ (as bs : ℕ → ℕ),
        as 0 = a₀ ∧ bs (s - 1) = y ∧
        (∀ j < s, (as j, bs j) ∈ S \ H) ∧
        (∀ j, j + 1 < s → (as (j + 1), bs j) ∈ H) ∧
        (∀ j < s, as j ∈ (bfsLayer n S H a₀ j).1 ∧ (∀ r < j, as j ∉ (bfsLayer n S H a₀ r).1)) ∧
        (∀ j < s, bs j ∈ (bfsLayer n S H a₀ (j + 1)).2 ∧
          (∀ r < j + 1, bs j ∉ (bfsLayer n S H a₀ r).2)) := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro hs y hy hymin
      have hy_not_prev : y ∉ (bfsLayer n S H a₀ (s - 1)).2 := hymin (s - 1) (by omega)
      have hs_eq : s = (s - 1) + 1 := by omega
      have hy' : y ∈ (bfsLayer n S H a₀ ((s - 1) + 1)).2 := hs_eq ▸ hy
      rw [mem_bfsB_succ] at hy'
      rcases hy' with hyprev | ⟨_, a, ha, hay⟩
      · exact False.elim (hy_not_prev hyprev)
      · -- Pick minimal r ≤ s - 1 with a ∈ (bfsLayer r).1
        have hexA : ∃ r, a ∈ (bfsLayer n S H a₀ r).1 := ⟨s - 1, ha⟩
        let r := Nat.find hexA
        have har : a ∈ (bfsLayer n S H a₀ r).1 := Nat.find_spec hexA
        have hr_le : r ≤ s - 1 := Nat.find_min' hexA ha
        have hr_min : ∀ q < r, a ∉ (bfsLayer n S H a₀ q).1 := fun q hq => Nat.find_min hexA hq
        have hr_eq : r = s - 1 := by
          by_contra hne
          have hr_lt : r < s - 1 := by omega
          have hy_early : y ∈ (bfsLayer n S H a₀ (r + 1)).2 :=
            mem_bfsB_succ.mpr (Or.inr ⟨(Finset.mem_product.mp (hS (Finset.mem_sdiff.mp hay).1)).2, a, har, hay⟩)
          exact hymin (r + 1) (by omega) hy_early
        rw [hr_eq] at har hr_min
        by_cases hs1 : s = 1
        · subst hs1
          have ha_eq : a = a₀ := by simpa [bfsLayer] using har
          subst ha_eq
          refine ⟨fun _ => a, fun _ => y, rfl, rfl, ?_, ?_, ?_, ?_⟩
          · intro j hj; have : j = 0 := by omega
            subst this; exact hay
          · intro j hj; omega
          · intro j hj; have : j = 0 := by omega
            subst this; exact ⟨har, fun q hq => by omega⟩
          · intro j hj; have : j = 0 := by omega
            subst this; exact ⟨hy, hymin⟩
        · have hs2 : 2 ≤ s := by omega
          have ha_not_prev : a ∉ (bfsLayer n S H a₀ (s - 2)).1 := hr_min (s - 2) (by omega)
          have hseq2 : s - 1 = (s - 2) + 1 := by omega
          have ha' : a ∈ (bfsLayer n S H a₀ ((s - 2) + 1)).1 := hseq2 ▸ har
          rw [mem_bfsA_succ] at ha'
          rcases ha' with haprev | ⟨_, b', hb', hab'⟩
          · exact False.elim (ha_not_prev haprev)
          · -- b' ∈ (bfsLayer (s - 1)).2 and cannot be in an earlier B-layer (else a would be in an earlier A-layer)
            have hb'_mem : b' ∈ (bfsLayer n S H a₀ (s - 1)).2 := hseq2.symm ▸ hb'
            have hb'_min : ∀ q < s - 1, b' ∉ (bfsLayer n S H a₀ q).2 := by
              intro q hq hbq
              cases q with
              | zero => simp [bfsLayer] at hbq
              | succ q' =>
                have ha_early : a ∈ (bfsLayer n S H a₀ (q' + 1)).1 :=
                  mem_bfsA_succ.mpr (Or.inr ⟨(Finset.mem_product.mp (hS (hHS hab'))).1, b', hbq, hab'⟩)
                exact hr_min (q' + 1) (by omega) ha_early
            obtain ⟨as₀, bs₀, ha0, hbs_last, hadd₀, hdel₀, has_lay, hbs_lay⟩ :=
              ih (s - 1) (by omega) (by omega) b' hb'_mem hb'_min
            let as : ℕ → ℕ := fun j => if j = s - 1 then a else as₀ j
            let bs : ℕ → ℕ := fun j => if j = s - 1 then y else bs₀ j
            refine ⟨as, bs, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp [as, show (0 : ℕ) ≠ s - 1 by omega, ha0]
            · simp [bs]
            · intro j hj
              by_cases hjs : j = s - 1
              · simp only [as, bs, if_pos hjs]; exact hay
              · simp only [as, bs, if_neg hjs]; exact hadd₀ j (by omega)
            · intro j hj
              by_cases hjs : j + 1 = s - 1
              · have hjs' : j = s - 2 := by omega
                simp only [as, bs, if_pos hjs, if_neg (show j ≠ s - 1 by omega)]
                rw [show j = s - 1 - 1 by omega, hbs_last]
                exact hab'
              · simp only [as, bs, if_neg hjs, if_neg (show j ≠ s - 1 by omega)]
                exact hdel₀ j (by omega)
            · intro j hj
              by_cases hjs : j = s - 1
              · subst hjs; simp only [as, if_pos rfl]; exact ⟨har, hr_min⟩
              · simp only [as, if_neg hjs]; exact has_lay j (by omega)
            · intro j hj
              by_cases hjs : j = s - 1
              · subst hjs
                simp only [bs, if_pos rfl]
                rw [show s - 1 + 1 = s by omega]
                exact ⟨hy, hymin⟩
              · simp only [bs, if_neg hjs]; exact hbs_lay j (by omega)
  have hb_min : ∀ r < t, b ∉ (bfsLayer n S H a₀ r).2 := fun r hr hbr =>
    ne_of_lt hdegb (hmin r hr b hbr)
  obtain ⟨as, bs, ha0, hbs_last, hadd, hdel, has_lay, hbs_lay⟩ := hchain t ht b hb hb_min
  -- Pairwise distinctness of as and bs from strictly increasing layers
  have has_inj : ∀ i < t, ∀ j < t, as i = as j → i = j := by
    intro i hi j hj heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (has_lay j hj).2 i hlt (heq ▸ (has_lay i hi).1)
    · exact (has_lay i hi).2 j hgt (heq.symm ▸ (has_lay j hj).1)
  have hbs_inj : ∀ i < t, ∀ j < t, bs i = bs j → i = j := by
    intro i hi j hj heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (hbs_lay j hj).2 (i + 1) (by omega) (heq ▸ (hbs_lay i hi).1)
    · exact (hbs_lay i hi).2 (j + 1) (by omega) (heq.symm ▸ (hbs_lay j hj).1)
  let Eadd : Finset (ℕ × ℕ) := (range t).image (fun j => (as j, bs j))
  let Edel : Finset (ℕ × ℕ) := (range (t - 1)).image (fun j => (as (j + 1), bs j))
  have hEadd_sub : Eadd ⊆ S \ H := by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
    exact hadd j (Finset.mem_range.mp hj)
  have hEdel_sub : Edel ⊆ H := by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
    exact hdel j (by have := Finset.mem_range.mp hj; omega)
  have hEadd_card : Eadd.card = t := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intro i hi j hj heq
      exact has_inj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) (congrArg Prod.fst heq)
  have hEdel_card : Edel.card = t - 1 := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intro i hi j hj heq
      exact hbs_inj i (by have := Finset.mem_range.mp hi; omega)
        j (by have := Finset.mem_range.mp hj; omega) (congrArg Prod.snd heq)
  let H' := (H \ Edel) ∪ Eadd
  have hDisj : Disjoint (H \ Edel) Eadd := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    exact (Finset.mem_sdiff.mp (hEadd_sub hp2)).2 (Finset.mem_sdiff.mp hp1).1
  refine ⟨H', ?_, ?_, ?_, ?_⟩
  · exact Finset.union_subset (Finset.sdiff_subset.trans hHS) (hEadd_sub.trans Finset.sdiff_subset)
  · -- Check left degrees in H'
    intro x hx
    have hfilt : H'.filter (fun p => p.1 = x) =
        ((H.filter (fun p => p.1 = x)) \ (Edel.filter (fun p => p.1 = x))) ∪
        (Eadd.filter (fun p => p.1 = x)) := by
      ext p; simp only [H', Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]; tauto
    have hdisj_x : Disjoint ((H.filter (fun p => p.1 = x)) \ (Edel.filter (fun p => p.1 = x)))
        (Eadd.filter (fun p => p.1 = x)) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      exact (Finset.mem_sdiff.mp (hEadd_sub (Finset.mem_filter.mp hp2).1)).2
        (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp1).1).1
    have hsub_x : Edel.filter (fun p => p.1 = x) ⊆ H.filter (fun p => p.1 = x) :=
      Finset.filter_subset_filter _ hEdel_sub
    have hdeg_eq : degL H' x = degL H x - (Edel.filter (fun p => p.1 = x)).card +
        (Eadd.filter (fun p => p.1 = x)).card := by
      unfold degL
      rw [hfilt, Finset.card_union_of_disjoint hdisj_x, Finset.card_sdiff_of_subset hsub_x]
    have hle_H : (Edel.filter (fun p => p.1 = x)).card ≤ degL H x :=
      Finset.card_le_card hsub_x
    by_cases hmem : ∃ j < t, as j = x
    · obtain ⟨j, hj, rfl⟩ := hmem
      have hadd_x : (Eadd.filter (fun p => p.1 = as j)).card = 1 := by
        have hEq : Eadd.filter (fun p => p.1 = as j) = {(as j, bs j)} := by
          ext p
          simp only [Eadd, Finset.mem_filter, Finset.mem_image, Finset.mem_range, Finset.mem_singleton]
          constructor
          · rintro ⟨⟨i, hi, rfl⟩, heq⟩
            have := has_inj i hi j hj heq
            subst this; rfl
          · rintro rfl; exact ⟨⟨j, hj, rfl⟩, rfl⟩
        rw [hEq, Finset.card_singleton]
      by_cases hj0 : j = 0
      · subst hj0
        rw [hdeg_eq, hadd_x, ha0]
        omega
      · have hdel_x : (Edel.filter (fun p => p.1 = as j)).card = 1 := by
          have hEq : Edel.filter (fun p => p.1 = as j) = {(as j, bs (j - 1))} := by
            ext p
            simp only [Edel, Finset.mem_filter, Finset.mem_image, Finset.mem_range, Finset.mem_singleton]
            constructor
            · rintro ⟨⟨i, hi, rfl⟩, heq⟩
              have := has_inj (i + 1) (by omega) j hj heq
              have : i = j - 1 := by omega
              subst this; simp [show j - 1 + 1 = j by omega]
            · rintro rfl
              exact ⟨⟨j - 1, by omega, by simp [show j - 1 + 1 = j by omega]⟩, rfl⟩
          rw [hEq, Finset.card_singleton]
        have hxdeg := hdegL (as j) hx
        rw [hdeg_eq, hadd_x, hdel_x]
        omega
    · have hadd_x : (Eadd.filter (fun p => p.1 = x)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro p hp
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
        exact fun h => hmem ⟨j, Finset.mem_range.mp hj, h⟩
      have hxdeg := hdegL x hx
      rw [hdeg_eq, hadd_x]
      omega
  · -- Check right degrees in H'
    intro y hy
    have hfilt : H'.filter (fun p => p.2 = y) =
        ((H.filter (fun p => p.2 = y)) \ (Edel.filter (fun p => p.2 = y))) ∪
        (Eadd.filter (fun p => p.2 = y)) := by
      ext p; simp only [H', Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]; tauto
    have hdisj_y : Disjoint ((H.filter (fun p => p.2 = y)) \ (Edel.filter (fun p => p.2 = y)))
        (Eadd.filter (fun p => p.2 = y)) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      exact (Finset.mem_sdiff.mp (hEadd_sub (Finset.mem_filter.mp hp2).1)).2
        (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp1).1).1
    have hsub_y : Edel.filter (fun p => p.2 = y) ⊆ H.filter (fun p => p.2 = y) :=
      Finset.filter_subset_filter _ hEdel_sub
    have hdeg_eq : degR H' y = degR H y - (Edel.filter (fun p => p.2 = y)).card +
        (Eadd.filter (fun p => p.2 = y)).card := by
      unfold degR
      rw [hfilt, Finset.card_union_of_disjoint hdisj_y, Finset.card_sdiff_of_subset hsub_y]
    have hle_H : (Edel.filter (fun p => p.2 = y)).card ≤ degR H y :=
      Finset.card_le_card hsub_y
    by_cases hmem : ∃ j < t, bs j = y
    · obtain ⟨j, hj, rfl⟩ := hmem
      have hadd_y : (Eadd.filter (fun p => p.2 = bs j)).card = 1 := by
        have hEq : Eadd.filter (fun p => p.2 = bs j) = {(as j, bs j)} := by
          ext p
          simp only [Eadd, Finset.mem_filter, Finset.mem_image, Finset.mem_range, Finset.mem_singleton]
          constructor
          · rintro ⟨⟨i, hi, rfl⟩, heq⟩
            have := hbs_inj i hi j hj heq
            subst this; rfl
          · rintro rfl; exact ⟨⟨j, hj, rfl⟩, rfl⟩
        rw [hEq, Finset.card_singleton]
      by_cases hjt : j = t - 1
      · subst hjt
        rw [hdeg_eq, hadd_y, hbs_last]
        omega
      · have hdel_y : (Edel.filter (fun p => p.2 = bs j)).card = 1 := by
          have hEq : Edel.filter (fun p => p.2 = bs j) = {(as (j + 1), bs j)} := by
            ext p
            simp only [Edel, Finset.mem_filter, Finset.mem_image, Finset.mem_range, Finset.mem_singleton]
            constructor
            · rintro ⟨⟨i, hi, rfl⟩, heq⟩
              have := hbs_inj i (by omega) j hj heq
              subst this; rfl
            · rintro rfl; exact ⟨⟨j, by omega, rfl⟩, rfl⟩
          rw [hEq, Finset.card_singleton]
        have hydeg := hdegR (bs j) hy
        rw [hdeg_eq, hadd_y, hdel_y]
        omega
    · have hadd_y : (Eadd.filter (fun p => p.2 = y)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro p hp
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
        exact fun h => hmem ⟨j, Finset.mem_range.mp hj, h⟩
      have hydeg := hdegR y hy
      rw [hdeg_eq, hadd_y]
      omega
  · -- Strictly larger cardinality
    have hle_card : Edel.card ≤ H.card := Finset.card_le_card hEdel_sub
    rw [show H'.card = (H \ Edel).card + Eadd.card from Finset.card_union_of_disjoint hDisj,
      Finset.card_sdiff_of_subset hEdel_sub, hEadd_card, hEdel_card]
    omega

/-- Ore--Ryser criterion for the existence of a `k`-regular spanning subgraph in a bipartite graph
on `range n × range n`. -/
theorem ore_ryser {n k : ℕ} {S : Finset (ℕ × ℕ)} (hS : S ⊆ range n ×ˢ range n)
    (hOR : ∀ A ⊆ range n, ∀ B ⊆ range n,
      k * A.card ≤ (S.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card + k * B.card) :
    ∃ H ⊆ S, IsKRegular n k H := by
  classical
  let valid : Finset (Finset (ℕ × ℕ)) :=
    S.powerset.filter (fun H => (∀ x ∈ range n, degL H x ≤ k) ∧ (∀ y ∈ range n, degR H y ≤ k))
  have hne : valid.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset S, ?_, ?_⟩⟩
    · intro x _; simp [degL]
    · intro y _; simp [degR]
  obtain ⟨H, hHmem, hHmax⟩ := Finset.exists_max_image valid Finset.card hne
  have hHS : H ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hHmem).1
  have hHsub : H ⊆ range n ×ˢ range n := hHS.trans hS
  have hdegL : ∀ x ∈ range n, degL H x ≤ k := (Finset.mem_filter.mp hHmem).2.1
  have hdegR : ∀ y ∈ range n, degR H y ≤ k := (Finset.mem_filter.mp hHmem).2.2
  have hcard_le : H.card ≤ k * n := by
    rw [card_eq_sum_degL hHsub]
    calc ∑ x ∈ range n, degL H x ≤ ∑ _x ∈ range n, k := Finset.sum_le_sum hdegL
      _ = k * n := by simp [mul_comm]
  by_cases hfull : H.card = k * n
  · refine ⟨H, hHS, hHsub, ?_, ?_⟩
    · intro x hx
      by_contra hne_x
      have hlt_x : degL H x < k := lt_of_le_of_ne (hdegL x hx) hne_x
      have hsum_lt : ∑ u ∈ range n, degL H u < ∑ _u ∈ range n, k :=
        Finset.sum_lt_sum hdegL ⟨x, hx, hlt_x⟩
      rw [← card_eq_sum_degL hHsub] at hsum_lt
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm] at hsum_lt
      omega
    · intro y hy
      by_contra hne_y
      have hlt_y : degR H y < k := lt_of_le_of_ne (hdegR y hy) hne_y
      have hsum_lt : ∑ v ∈ range n, degR H v < ∑ _v ∈ range n, k :=
        Finset.sum_lt_sum hdegR ⟨y, hy, hlt_y⟩
      rw [← card_eq_sum_degR hHsub] at hsum_lt
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm] at hsum_lt
      omega
  · -- Contradiction: pick a₀ ∈ range n with degL H a₀ < k and run BFS
    exfalso
    have hlt : H.card < k * n := lt_of_le_of_ne hcard_le hfull
    have hex_a₀ : ∃ a₀ ∈ range n, degL H a₀ < k := by
      by_contra hall
      push Not at hall
      have hge : k * n ≤ H.card := by
        rw [card_eq_sum_degL hHsub]
        calc k * n = ∑ _x ∈ range n, k := by simp [mul_comm]
          _ ≤ ∑ x ∈ range n, degL H x := Finset.sum_le_sum hall
      omega
    obtain ⟨a₀, ha₀, hdegA₀⟩ := hex_a₀
    -- Every vertex in every BFS layer B t must have degR = k
    have hBfull : ∀ t, ∀ y ∈ (bfsLayer n S H a₀ t).2, degR H y = k := by
      intro t
      induction t using Nat.strong_induction_on with
      | h t ih =>
        intro y hy
        cases t with
        | zero => simp [bfsLayer] at hy
        | succ t' =>
          have hy_in : y ∈ range n := (bfsLayer_subset n S H a₀ ha₀ (t' + 1)).2 hy
          by_contra hne_y
          have hlt_y : degR H y < k := lt_of_le_of_ne (hdegR y hy_in) hne_y
          obtain ⟨H', hH'S, hH'L, hH'R, hH'gt⟩ :=
            bfs_augment hS hHS ha₀ hdegA₀ hdegL hdegR (Nat.succ_pos t') hy ih hlt_y
          have hH'mem : H' ∈ valid :=
            Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hH'S, hH'L, hH'R⟩
          have := hHmax H' hH'mem
          omega
    let A := (bfsLayer n S H a₀ n).1
    let B := (bfsLayer n S H a₀ n).2
    have hAsub : A ⊆ range n := (bfsLayer_subset n S H a₀ ha₀ n).1
    have hBsub : B ⊆ range n := (bfsLayer_subset n S H a₀ ha₀ n).2
    have hfix := bfsLayer_fixed n S H a₀ ha₀
    have ha₀A : a₀ ∈ A := (bfsLayer_mono_le n S H a₀ (Nat.zero_le n)).1 (by simp [bfsLayer])
    -- No edge of S \ H goes from A to range n \ B
    have hSH_empty : S.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B) ⊆
        H.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B) := by
      intro p hp
      obtain ⟨hpS, hpA, hpB⟩ := Finset.mem_filter.mp hp
      refine Finset.mem_filter.mpr ⟨?_, hpA, hpB⟩
      by_contra hpH
      have hmemB : p.2 ∈ (bfsLayer n S H a₀ (n + 1)).2 :=
        mem_bfsB_succ.mpr (Or.inr ⟨(Finset.mem_sdiff.mp hpB).1, p.1, hpA, Finset.mem_sdiff.mpr ⟨hpS, hpH⟩⟩)
      rw [hfix.2] at hmemB
      exact (Finset.mem_sdiff.mp hpB).2 hmemB
    -- Every edge of H into B comes from A
    have hHB_in_A : H.filter (fun p => p.2 ∈ B) = H.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B) := by
      ext p
      simp only [Finset.mem_filter]
      refine ⟨fun ⟨hpH, hpB⟩ => ⟨hpH, ?_, hpB⟩, fun ⟨hpH, _, hpB⟩ => ⟨hpH, hpB⟩⟩
      have hmemA : p.1 ∈ (bfsLayer n S H a₀ (n + 1)).1 :=
        mem_bfsA_succ.mpr (Or.inr ⟨(Finset.mem_product.mp (hHsub hpH)).1, p.2, hfix.2.symm ▸ hpB, hpH⟩)
      rw [hfix.1] at hmemA
      exact hmemA
    -- Partition H-edges out of A into B vs range n \ B
    have hpart : (H.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card +
        (H.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B)).card =
        (H.filter (fun p => p.1 ∈ A)).card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext p
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
        constructor
        · rintro (⟨hpH, hpA, _⟩ | ⟨hpH, hpA, _⟩) <;> exact ⟨hpH, hpA⟩
        · rintro ⟨hpH, hpA⟩
          by_cases hpb : p.2 ∈ B
          · exact Or.inr ⟨hpH, hpA, hpb⟩
          · exact Or.inl ⟨hpH, hpA, (Finset.mem_product.mp (hHsub hpH)).2, hpb⟩
      · rw [Finset.disjoint_left]
        intro p hp1 hp2
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp1).2.2).2 (Finset.mem_filter.mp hp2).2.2
    have hsumA : (H.filter (fun p => p.1 ∈ A)).card < k * A.card := by
      rw [card_filter_prod_eq_sum_degL A]
      calc ∑ x ∈ A, degL H x < ∑ _x ∈ A, k :=
            Finset.sum_lt_sum (fun x hx => hdegL x (hAsub hx)) ⟨a₀, ha₀A, hdegA₀⟩
        _ = k * A.card := by simp [mul_comm]
    have hsumB : (H.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B)).card = k * B.card := by
      rw [← hHB_in_A, card_filter_prod_eq_sum_degR B]
      calc ∑ y ∈ B, degR H y = ∑ _y ∈ B, k := Finset.sum_congr rfl fun y hy => hBfull n y hy
        _ = k * B.card := by simp [mul_comm]
    have hcut_le : (S.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card ≤
        (H.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card :=
      Finset.card_le_card hSH_empty
    have hOR_AB := hOR A hAsub B hBsub
    omega

/-- Every `k`-regular bipartite graph (`k ≥ 1`) contains a `1`-factor whose removal leaves a
`(k - 1)`-regular bipartite graph. -/
lemma exists_one_factor_of_regular {n k : ℕ} (hk : 1 ≤ k) {S : Finset (ℕ × ℕ)}
    (hS : IsKRegular n k S) :
    ∃ M ⊆ S, IsKRegular n 1 M ∧ IsKRegular n (k - 1) (S \ M) := by
  have hOR : ∀ A ⊆ range n, ∀ B ⊆ range n,
      1 * A.card ≤ (S.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card + 1 * B.card := by
    intro A hA B hB
    have hpart : (S.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card +
        (S.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B)).card = (S.filter (fun p => p.1 ∈ A)).card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext p
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
        constructor
        · rintro (⟨hpS, hpA, _⟩ | ⟨hpS, hpA, _⟩) <;> exact ⟨hpS, hpA⟩
        · rintro ⟨hpS, hpA⟩
          by_cases hpb : p.2 ∈ B
          · exact Or.inr ⟨hpS, hpA, hpb⟩
          · exact Or.inl ⟨hpS, hpA, (Finset.mem_product.mp (hS.1 hpS)).2, hpb⟩
      · rw [Finset.disjoint_left]
        intro p hp1 hp2
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp1).2.2).2 (Finset.mem_filter.mp hp2).2.2
    have hA_eq : (S.filter (fun p => p.1 ∈ A)).card = k * A.card := by
      rw [card_filter_prod_eq_sum_degL A]
      calc ∑ x ∈ A, degL S x = ∑ _x ∈ A, k := Finset.sum_congr rfl fun x hx => hS.2.1 x (hA hx)
        _ = k * A.card := by simp [mul_comm]
    have hAB_le : (S.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B)).card ≤ k * B.card := by
      calc (S.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B)).card
          ≤ (S.filter (fun p => p.2 ∈ B)).card :=
            Finset.card_le_card (fun p hp => by
              simp only [Finset.mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.2⟩)
        _ = ∑ y ∈ B, degR S y := card_filter_prod_eq_sum_degR B
        _ = ∑ _y ∈ B, k := Finset.sum_congr rfl fun y hy => hS.2.2 y (hB hy)
        _ = k * B.card := by simp [mul_comm]
    have hmul : k * A.card ≤
        (S.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card + k * B.card := by omega
    by_cases hle : A.card ≤ B.card
    · omega
    · have h1 : k * (A.card - B.card) ≤
          (S.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card := by
        rw [Nat.mul_sub_left_distrib]; omega
      have h2 : 1 * (A.card - B.card) ≤ k * (A.card - B.card) := Nat.mul_le_mul_right _ hk
      omega
  obtain ⟨M, hMS, hMreg⟩ := ore_ryser hS.1 hOR
  refine ⟨M, hMS, hMreg, Finset.sdiff_subset.trans hS.1, ?_, ?_⟩
  · intro x hx
    have hfilt : (S \ M).filter (fun p => p.1 = x) =
        S.filter (fun p => p.1 = x) \ M.filter (fun p => p.1 = x) := by
      ext p; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
    unfold degL
    rw [hfilt, Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ hMS)]
    exact congrArg₂ (· - ·) (hS.2.1 x hx) (hMreg.2.1 x hx)
  · intro y hy
    have hfilt : (S \ M).filter (fun p => p.2 = y) =
        S.filter (fun p => p.2 = y) \ M.filter (fun p => p.2 = y) := by
      ext p; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
    unfold degR
    rw [hfilt, Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ hMS)]
    exact congrArg₂ (· - ·) (hS.2.2 y hy) (hMreg.2.2 y hy)

/-- Peel `t` disjoint `1`-factors from a `k`-regular bipartite graph (`t ≤ k`). -/
lemma peel_one_factors {n k : ℕ} (t : ℕ) (ht : t ≤ k) {S : Finset (ℕ × ℕ)}
    (hS : IsKRegular n k S) :
    ∃ (P : Fin t → Finset (ℕ × ℕ)) (R : Finset (ℕ × ℕ)),
      (∀ i, P i ⊆ S ∧ IsKRegular n 1 (P i)) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      R ⊆ S ∧ IsKRegular n (k - t) R ∧
      (∀ i, Disjoint (P i) R) ∧
      (∀ p ∈ S, p ∈ R ∨ ∃ i, p ∈ P i) := by
  induction t generalizing k S with
  | zero =>
    exact ⟨Fin.elim0, S, fun i => i.elim0, fun i => i.elim0, Subset.rfl, by simpa using hS,
      fun i => i.elim0, fun p hp => Or.inl hp⟩
  | succ t ih =>
    obtain ⟨M, hMS, hMreg, hSMreg⟩ := exists_one_factor_of_regular (by omega : 1 ≤ k) hS
    obtain ⟨P₀, R, hP₀, hdisj₀, hRsub, hRreg, hPR, hcov⟩ := ih (by omega : t ≤ k - 1) hSMreg
    let P : Fin (t + 1) → Finset (ℕ × ℕ) := Fin.cases M P₀
    refine ⟨P, R, ?_, ?_, hRsub.trans Finset.sdiff_subset, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ⟨hMS, hMreg⟩ (fun j => ⟨(hP₀ j).1.trans Finset.sdiff_subset, (hP₀ j).2⟩) i
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases (fun h => absurd rfl h) (fun j' _ => ?_) j
        exact Finset.disjoint_of_subset_right (hP₀ j').1 Finset.disjoint_sdiff
      · refine Fin.cases (fun _ => ?_) (fun j' h => ?_) j
        · exact (Finset.disjoint_of_subset_right (hP₀ i').1 Finset.disjoint_sdiff).symm
        · exact hdisj₀ i' j' (fun he => h (congrArg Fin.succ he))
    · have hsub : k - 1 - t = k - (t + 1) := by omega
      rwa [hsub] at hRreg
    · intro i
      refine Fin.cases (Finset.disjoint_of_subset_right hRsub Finset.disjoint_sdiff) hPR i
    · intro p hp
      by_cases hpM : p ∈ M
      · exact Or.inr ⟨0, hpM⟩
      · rcases hcov p (Finset.mem_sdiff.mpr ⟨hp, hpM⟩) with hpR | ⟨j, hpj⟩
        · exact Or.inl hpR
        · exact Or.inr ⟨j.succ, hpj⟩

/- ## Section 3: Discrete Grid Lines and Polynomial Tails -/

def grid (n : ℕ) : Finset (ℕ × ℕ) := range n ×ˢ range n

def lineThrough (n : ℕ) (p q : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (grid n).filter fun r =>
    ((q.2 : ℤ) - (p.2 : ℤ)) * ((r.1 : ℤ) - (p.1 : ℤ)) =
    ((q.1 : ℤ) - (p.1 : ℤ)) * ((r.2 : ℤ) - (p.2 : ℤ))

def allLines (n : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  ((grid n ×ˢ grid n).filter fun pq => pq.1 ≠ pq.2).image fun pq => lineThrough n pq.1 pq.2

lemma mem_lineThrough_left {n : ℕ} {p q : ℕ × ℕ} (hp : p ∈ grid n) :
    p ∈ lineThrough n p q := by
  simp [lineThrough, hp]

lemma mem_lineThrough_right {n : ℕ} {p q : ℕ × ℕ} (hq : q ∈ grid n) :
    q ∈ lineThrough n p q := by
  simp only [lineThrough, Finset.mem_filter]
  exact ⟨hq, by ring⟩

lemma filter_linear_eq_lineThrough {n : ℕ} {a b c : ℤ} (hab : a ≠ 0 ∨ b ≠ 0)
    {p q : ℕ × ℕ} (hp : p ∈ (grid n).filter fun i => a * i.1 + b * i.2 = c)
    (hq : q ∈ (grid n).filter fun i => a * i.1 + b * i.2 = c) (hpq : p ≠ q) :
    (grid n).filter (fun i => a * i.1 + b * i.2 = c) = lineThrough n p q := by
  obtain ⟨hpG, hpeq⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqG, hqeq⟩ := Finset.mem_filter.mp hq
  have hd : a * ((q.1 : ℤ) - p.1) + b * ((q.2 : ℤ) - p.2) = 0 := by linarith
  have hneq : (q.1 : ℤ) - p.1 ≠ 0 ∨ (q.2 : ℤ) - p.2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hpq
    exact Prod.ext (by omega) (by omega)
  ext r
  simp only [lineThrough, Finset.mem_filter]
  refine ⟨fun ⟨hrG, hreq⟩ => ⟨hrG, ?_⟩, fun ⟨hrG, hcol⟩ => ⟨hrG, ?_⟩⟩
  · have hdr : a * ((r.1 : ℤ) - p.1) + b * ((r.2 : ℤ) - p.2) = 0 := by linarith
    rcases hab with ha | hb
    · apply mul_left_cancel₀ ha
      linear_combination ((q.2 : ℤ) - p.2) * hdr - ((r.2 : ℤ) - p.2) * hd
    · apply mul_left_cancel₀ hb
      linear_combination -((q.1 : ℤ) - p.1) * hdr + ((r.1 : ℤ) - p.1) * hd
  · rcases hneq with hx | hy
    · have : ((q.1 : ℤ) - p.1) * (a * (r.1 : ℤ) + b * (r.2 : ℤ) - c) = 0 := by
        linear_combination ((r.1 : ℤ) - p.1) * hd - b * hcol + ((q.1 : ℤ) - p.1) * hpeq
      have := (mul_eq_zero.mp this).resolve_left hx
      linarith
    · have : ((q.2 : ℤ) - p.2) * (a * (r.1 : ℤ) + b * (r.2 : ℤ) - c) = 0 := by
        linear_combination ((r.2 : ℤ) - p.2) * hd + a * hcol + ((q.2 : ℤ) - p.2) * hpeq
      have := (mul_eq_zero.mp this).resolve_left hy
      linarith

lemma lineThrough_eq_of_mem {n : ℕ} {L : Finset (ℕ × ℕ)} (hL : L ∈ allLines n)
    {p q : ℕ × ℕ} (hp : p ∈ L) (hq : q ∈ L) (hpq : p ≠ q) :
    L = lineThrough n p q := by
  obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp hL
  obtain ⟨huvG, huv_ne⟩ := Finset.mem_filter.mp huv
  let a : ℤ := (v.2 : ℤ) - u.2
  let b : ℤ := (u.1 : ℤ) - v.1
  let c : ℤ := a * u.1 + b * u.2
  dsimp only at huv_ne
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h; push Not at h; apply huv_ne
    exact Prod.ext (by dsimp [b] at h; omega) (by dsimp [a] at h; omega)
  have hEq : lineThrough n u v = (grid n).filter (fun i => a * i.1 + b * i.2 = c) := by
    ext r; simp only [lineThrough, Finset.mem_filter, a, b, c]
    exact ⟨fun ⟨hr, he⟩ => ⟨hr, by linarith⟩, fun ⟨hr, he⟩ => ⟨hr, by linarith⟩⟩
  rw [hEq] at hp hq ⊢
  exact filter_linear_eq_lineThrough hab hp hq hpq

lemma line_subset_grid {n : ℕ} {L : Finset (ℕ × ℕ)} (hL : L ∈ allLines n) : L ⊆ grid n := by
  obtain ⟨⟨u, v⟩, _, rfl⟩ := Finset.mem_image.mp hL
  exact Finset.filter_subset _ _

lemma line_card_bounds {n : ℕ} {L : Finset (ℕ × ℕ)} (hL : L ∈ allLines n) :
    2 ≤ L.card ∧ L.card ≤ n := by
  obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp hL
  obtain ⟨huvG, huv_ne⟩ := Finset.mem_filter.mp huv
  dsimp only at huv_ne
  obtain ⟨huG, hvG⟩ := Finset.mem_product.mp huvG
  constructor
  · have hsub : ({u, v} : Finset (ℕ × ℕ)) ⊆ lineThrough n u v := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact mem_lineThrough_left huG
      · rw [Finset.mem_singleton.mp hx]; exact mem_lineThrough_right hvG
    have h2 : ({u, v} : Finset (ℕ × ℕ)).card = 2 := Finset.card_pair huv_ne
    exact h2 ▸ Finset.card_le_card hsub
  · by_cases hx : u.1 = v.1
    · have hinj : Set.InjOn Prod.snd (lineThrough n u v : Set (ℕ × ℕ)) := by
        intro r hr s hs heq
        have hr' := (Finset.mem_filter.mp (Finset.mem_coe.mp hr)).2
        have hs' := (Finset.mem_filter.mp (Finset.mem_coe.mp hs)).2
        have hyne : (v.2 : ℤ) - u.2 ≠ 0 := by
          intro h; apply huv_ne; exact Prod.ext hx (by omega)
        rw [hx, sub_self, zero_mul] at hr' hs'
        have hr1 : (r.1 : ℤ) - v.1 = 0 := (mul_eq_zero.mp hr').resolve_left hyne
        have hs1 : (s.1 : ℤ) - v.1 = 0 := (mul_eq_zero.mp hs').resolve_left hyne
        exact Prod.ext (by omega) heq
      calc (lineThrough n u v).card
          = ((lineThrough n u v).image Prod.snd).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (range n).card := Finset.card_le_card (by
            intro y hy; obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy
            exact (Finset.mem_product.mp (Finset.mem_filter.mp hr).1).2)
        _ = n := Finset.card_range n
    · have hinj : Set.InjOn Prod.fst (lineThrough n u v : Set (ℕ × ℕ)) := by
        intro r hr s hs heq
        have hr' := (Finset.mem_filter.mp (Finset.mem_coe.mp hr)).2
        have hs' := (Finset.mem_filter.mp (Finset.mem_coe.mp hs)).2
        have hxne : (v.1 : ℤ) - u.1 ≠ 0 := by omega
        have hmul : ((v.1 : ℤ) - u.1) * ((r.2 : ℤ) - s.2) = 0 := by
          have : (r.1 : ℤ) = s.1 := by exact_mod_cast heq
          linear_combination -hr' + hs' + ((v.2 : ℤ) - u.2) * this
        have hy : (r.2 : ℤ) - s.2 = 0 := (mul_eq_zero.mp hmul).resolve_left hxne
        exact Prod.ext heq (by omega)
      calc (lineThrough n u v).card
          = ((lineThrough n u v).image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (range n).card := Finset.card_le_card (by
            intro x hx; obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
            exact (Finset.mem_product.mp (Finset.mem_filter.mp hr).1).1)
        _ = n := Finset.card_range n

lemma horizLine_mem {n y : ℕ} (hn : 2 ≤ n) (hy : y ∈ range n) :
    (grid n).filter (fun p => p.2 = y) ∈ allLines n := by
  have h0 : (0, y) ∈ grid n :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), hy⟩
  have h1 : (1, y) ∈ grid n :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), hy⟩
  have heq : (grid n).filter (fun p => p.2 = y) = lineThrough n (0, y) (1, y) := by
    ext r; simp only [lineThrough, Finset.mem_filter]
    exact ⟨fun ⟨hr, he⟩ => ⟨hr, by simp [he]⟩, fun ⟨hr, he⟩ => ⟨hr, by omega⟩⟩
  rw [heq]
  exact Finset.mem_image.mpr ⟨((0, y), (1, y)),
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h0, h1⟩, by simp⟩, rfl⟩

lemma vertLine_mem {n x : ℕ} (hn : 2 ≤ n) (hx : x ∈ range n) :
    (grid n).filter (fun p => p.1 = x) ∈ allLines n := by
  have h0 : (x, 0) ∈ grid n :=
    Finset.mem_product.mpr ⟨hx, Finset.mem_range.mpr (by omega)⟩
  have h1 : (x, 1) ∈ grid n :=
    Finset.mem_product.mpr ⟨hx, Finset.mem_range.mpr (by omega)⟩
  have heq : (grid n).filter (fun p => p.1 = x) = lineThrough n (x, 0) (x, 1) := by
    ext r; simp only [lineThrough, Finset.mem_filter]
    exact ⟨fun ⟨hr, he⟩ => ⟨hr, by simp [he]⟩, fun ⟨hr, he⟩ => ⟨hr, by omega⟩⟩
  rw [heq]
  exact Finset.mem_image.mpr ⟨((x, 0), (x, 1)),
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h0, h1⟩, by simp⟩, rfl⟩

/-- If a line `L ∈ allLines n` has primitive step `(u, v)` with `M = max u |v|`, then
`L.card ≤ (n - 1) / M + 1`. -/
lemma line_card_le_of_step {n : ℕ} {L : Finset (ℕ × ℕ)} (hL : L ∈ allLines n)
    {p q : ℕ × ℕ} (hp : p ∈ L) (hq : q ∈ L) (hpq : p ≠ q) :
    ∃ u v : ℤ, 0 ≤ u ∧ (u ≠ 0 ∨ v ≠ 0) ∧
      (∀ r ∈ L, ∃ t : ℤ, (r.1 : ℤ) - p.1 = t * u ∧ (r.2 : ℤ) - p.2 = t * v) ∧
      (∀ r ∈ grid n, ((∃ t : ℤ, (r.1 : ℤ) - p.1 = t * u ∧ (r.2 : ℤ) - p.2 = t * v) → r ∈ L)) ∧
      ((L.card : ℝ) < (n : ℝ) / ((max u.natAbs v.natAbs : ℕ) : ℝ) + 1) := by
  have hL_eq : L = lineThrough n p q := lineThrough_eq_of_mem hL hp hq hpq
  let dx0 : ℤ := (q.1 : ℤ) - p.1
  let dy0 : ℤ := (q.2 : ℤ) - p.2
  -- Orient so dx ≥ 0
  let dx : ℤ := if 0 ≤ dx0 then dx0 else -dx0
  let dy : ℤ := if 0 ≤ dx0 then dy0 else -dy0
  let g : ℕ := Int.gcd dx dy
  have hdx_nonneg : 0 ≤ dx := by dsimp [dx]; split_ifs <;> omega
  have hne0 : dx0 ≠ 0 ∨ dy0 ≠ 0 := by
    by_contra h; push Not at h; apply hpq
    exact Prod.ext (by dsimp [dx0] at h; omega) (by dsimp [dy0] at h; omega)
  have hg_pos : 0 < g := by
    apply Nat.pos_of_ne_zero
    intro hg0
    have h1 := Int.gcd_eq_zero_iff.mp hg0
    dsimp [dx, dy] at h1
    split_ifs at h1 <;> omega
  let u : ℤ := dx / (g : ℤ)
  let v : ℤ := dy / (g : ℤ)
  have hu_dvd : (g : ℤ) ∣ dx := Int.gcd_dvd_left dx dy
  have hv_dvd : (g : ℤ) ∣ dy := Int.gcd_dvd_right dx dy
  have hgu : (g : ℤ) * u = dx := Int.mul_ediv_cancel' hu_dvd
  have hgv : (g : ℤ) * v = dy := Int.mul_ediv_cancel' hv_dvd
  have hu_nonneg : 0 ≤ u := Int.ediv_nonneg hdx_nonneg (Nat.cast_nonneg g)
  have huv_ne : u ≠ 0 ∨ v ≠ 0 := by
    by_contra h; push Not at h
    rw [h.1, mul_zero] at hgu; rw [h.2, mul_zero] at hgv
    dsimp [dx, dy] at hgu hgv
    split_ifs at hgu hgv <;> omega
  have hcop : IsCoprime u v := by
    have hgcd1 : Int.gcd u v = 1 := by
      have hm : Int.gcd ((g : ℤ) * u) ((g : ℤ) * v) = g * Int.gcd u v := by
        simpa [Int.natAbs_natCast] using Int.gcd_mul_left (g : ℤ) u v
      rw [hgu, hgv] at hm
      have : g = g * Int.gcd u v := hm
      nlinarith
    exact Int.isCoprime_iff_gcd_eq_one.mpr hgcd1
  have hcol_iff : ∀ r ∈ grid n, r ∈ L ↔ v * ((r.1 : ℤ) - p.1) = u * ((r.2 : ℤ) - p.2) := by
    intro r hrG
    rw [hL_eq]
    simp only [lineThrough, Finset.mem_filter, hrG, true_and]
    have h1 : dy * ((r.1 : ℤ) - p.1) = dx * ((r.2 : ℤ) - p.2) ↔
        dy0 * ((r.1 : ℤ) - p.1) = dx0 * ((r.2 : ℤ) - p.2) := by
      dsimp [dx, dy]; split_ifs <;> constructor <;> intro h <;> linarith
    rw [← h1, ← hgu, ← hgv]
    have hgne : (g : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hg_pos.ne'
    constructor
    · intro h; apply mul_left_cancel₀ hgne; linarith
    · intro h; linear_combination (g : ℤ) * h
  have hparam : ∀ r ∈ L, ∃ t : ℤ, (r.1 : ℤ) - p.1 = t * u ∧ (r.2 : ℤ) - p.2 = t * v := by
    intro r hr
    have hrG : r ∈ grid n := line_subset_grid hL hr
    have hcol := (hcol_iff r hrG).mp hr
    have hu_div : u ∣ (r.1 : ℤ) - p.1 := by
      have hdvd : u ∣ v * ((r.1 : ℤ) - p.1) := ⟨(r.2 : ℤ) - p.2, hcol⟩
      exact hcop.dvd_of_dvd_mul_left hdvd
    rcases hu_div with ⟨t, ht⟩
    by_cases hu0 : u = 0
    · have hv_unit : v = 1 ∨ v = -1 := by
        have h1 : Int.gcd 0 v = 1 := by
          rw [← hu0]; exact Int.isCoprime_iff_gcd_eq_one.mp hcop
        simp only [Int.gcd_zero_left] at h1
        omega
      have hr1 : (r.1 : ℤ) - p.1 = 0 := by rw [ht, hu0, zero_mul]
      rcases hv_unit with hv1 | hv1
      · refine ⟨(r.2 : ℤ) - p.2, by rw [hu0, mul_zero, hr1], by rw [hv1, mul_one]⟩
      · refine ⟨-((r.2 : ℤ) - p.2), by rw [hu0, mul_zero, hr1], by rw [hv1]; ring⟩
    · refine ⟨t, by linarith, ?_⟩
      apply mul_left_cancel₀ hu0
      linear_combination -hcol + v * ht
  refine ⟨u, v, hu_nonneg, huv_ne, hparam, ?_, ?_⟩
  · rintro r hrG ⟨t, ht1, ht2⟩
    exact (hcol_iff r hrG).mpr (by linear_combination v * ht1 - u * ht2)
  · -- Bound L.card using M = max u.natAbs v.natAbs
    let M : ℕ := max u.natAbs v.natAbs
    have hM_pos : 0 < M := by
      rcases huv_ne with hu0 | hv0
      · exact lt_of_lt_of_le (Int.natAbs_pos.mpr hu0) (le_max_left _ _)
      · exact lt_of_lt_of_le (Int.natAbs_pos.mpr hv0) (le_max_right _ _)
    have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM_pos
    -- Pick the coordinate achieving M
    have hcard_nat : (L.card - 1) * M < n := by
      have hne : L.Nonempty := ⟨p, hp⟩
      by_cases hmax : u.natAbs ≥ v.natAbs
      · have hM_eq : M = u.natAbs := max_eq_left hmax
        have hu_pos : 0 < u := by omega
        -- Project L to Prod.fst; all values lie in [0, n) and are congruent mod M, distinct
        let X := L.image Prod.fst
        have hXcard : X.card = L.card := by
          apply Finset.card_image_of_injOn
          intro r hr s hs heq
          obtain ⟨tr, htr1, htr2⟩ := hparam r hr
          obtain ⟨ts, hts1, hts2⟩ := hparam s hs
          have hteq : tr = ts := by
            have : (tr - ts) * u = 0 := by
              have : (r.1 : ℤ) = s.1 := by exact_mod_cast heq
              linarith
            have := (mul_eq_zero.mp this).resolve_right hu_pos.ne'
            linarith
          subst hteq
          exact Prod.ext heq (by omega)
        have hXne : X.Nonempty := hne.image Prod.fst
        let xmin := X.min' hXne
        let xmax := X.max' hXne
        have hxmax_lt : xmax < n := by
          obtain ⟨r, hr, hr_eq⟩ := Finset.mem_image.mp (X.max'_mem hXne)
          change X.max' hXne < n
          rw [← hr_eq]; exact (Finset.mem_range.mp (Finset.mem_product.mp (line_subset_grid hL hr)).1)
        have hdiv_all : ∀ x ∈ X, ∃ j ≤ (xmax - xmin) / M, x = xmin + j * M := by
          intro x hx
          obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
          obtain ⟨r0, hr0, hr0_eq⟩ := Finset.mem_image.mp (X.min'_mem hXne)
          obtain ⟨tr, htr1, _⟩ := hparam r hr
          obtain ⟨t0, ht01, _⟩ := hparam r0 hr0
          have hle1 : xmin ≤ r.1 := X.min'_le _ hx
          have hle2 : r.1 ≤ xmax := X.le_max' _ hx
          have hdiff : ((r.1 : ℤ) - (xmin : ℤ)) = (tr - t0) * u := by
            have hmin_eq : (r0.1 : ℤ) = (xmin : ℤ) := by exact_mod_cast hr0_eq
            linarith
          have hu_eq : u = (M : ℤ) := by omega
          have htnonneg : 0 ≤ tr - t0 := by
            have : 0 ≤ (tr - t0) * (M : ℤ) := by rw [← hu_eq, ← hdiff]; omega
            nlinarith
          let j : ℕ := (tr - t0).toNat
          have hj_cast : (j : ℤ) = tr - t0 := Int.toNat_of_nonneg htnonneg
          have hj_eq : r.1 = xmin + j * M := by
            have h1 : (r.1 : ℤ) = (xmin : ℤ) + (j : ℤ) * (M : ℤ) := by
              rw [hj_cast, ← hu_eq]; linarith
            exact_mod_cast h1
          refine ⟨j, ?_, hj_eq⟩
          exact (Nat.le_div_iff_mul_le hM_pos).mpr (by omega)
        have hXle : X.card ≤ (xmax - xmin) / M + 1 := by
          have hsub : X ⊆ (range ((xmax - xmin) / M + 1)).image (fun j => xmin + j * M) := by
            intro x hx
            obtain ⟨j, hj, rfl⟩ := hdiv_all x hx
            exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
          exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
        have hmul : (L.card - 1) * M ≤ xmax - xmin :=
          (Nat.le_div_iff_mul_le hM_pos).mp (Nat.sub_le_of_le_add (hXcard ▸ hXle))
        omega
      · have hM_eq : M = v.natAbs := max_eq_right (by omega)
        have hv_ne : v ≠ 0 := by omega
        let Y := L.image Prod.snd
        have hYcard : Y.card = L.card := by
          apply Finset.card_image_of_injOn
          intro r hr s hs heq
          obtain ⟨tr, htr1, htr2⟩ := hparam r hr
          obtain ⟨ts, hts1, hts2⟩ := hparam s hs
          have hteq : tr = ts := by
            have : (tr - ts) * v = 0 := by
              have : (r.2 : ℤ) = s.2 := by exact_mod_cast heq
              linarith
            have := (mul_eq_zero.mp this).resolve_right hv_ne
            linarith
          subst hteq
          exact Prod.ext (by omega) heq
        have hYne : Y.Nonempty := hne.image Prod.snd
        let ymin := Y.min' hYne
        let ymax := Y.max' hYne
        have hymax_lt : ymax < n := by
          obtain ⟨r, hr, hr_eq⟩ := Finset.mem_image.mp (Y.max'_mem hYne)
          change Y.max' hYne < n
          rw [← hr_eq]; exact (Finset.mem_range.mp (Finset.mem_product.mp (line_subset_grid hL hr)).2)
        have hdiv_all : ∀ y ∈ Y, ∃ j ≤ (ymax - ymin) / M, y = ymin + j * M := by
          intro y hy
          obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy
          obtain ⟨r0, hr0, hr0_eq⟩ := Finset.mem_image.mp (Y.min'_mem hYne)
          obtain ⟨tr, _, htr2⟩ := hparam r hr
          obtain ⟨t0, _, ht02⟩ := hparam r0 hr0
          have hle1 : ymin ≤ r.2 := Y.min'_le _ hy
          have hle2 : r.2 ≤ ymax := Y.le_max' _ hy
          have hdiff : ((r.2 : ℤ) - (ymin : ℤ)) = (tr - t0) * v := by
            have hmin_eq : (r0.2 : ℤ) = (ymin : ℤ) := by exact_mod_cast hr0_eq
            linarith
          have hdvd_M : (M : ℤ) ∣ ((r.2 : ℤ) - (ymin : ℤ)) := by
            rw [hdiff]
            have : (M : ℤ) ∣ v := by
              rw [hM_eq]; exact Int.natAbs_dvd.mpr dvd_rfl
            exact dvd_mul_of_dvd_right this _
          rcases hdvd_M with ⟨q, hq⟩
          have hqnn : 0 ≤ q := by nlinarith
          let j : ℕ := q.toNat
          have hj_cast : (j : ℤ) = q := Int.toNat_of_nonneg hqnn
          have hj_eq : r.2 = ymin + j * M := by
            have h1 : (r.2 : ℤ) = (ymin : ℤ) + (j : ℤ) * (M : ℤ) := by
              rw [hj_cast]; linarith
            exact_mod_cast h1
          refine ⟨j, ?_, hj_eq⟩
          exact (Nat.le_div_iff_mul_le hM_pos).mpr (by omega)
        have hYle : Y.card ≤ (ymax - ymin) / M + 1 := by
          have hsub : Y ⊆ (range ((ymax - ymin) / M + 1)).image (fun j => ymin + j * M) := by
            intro y hy
            obtain ⟨j, hj, rfl⟩ := hdiv_all y hy
            exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
          exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
        have hmul : (L.card - 1) * M ≤ ymax - ymin :=
          (Nat.le_div_iff_mul_le hM_pos).mp (Nat.sub_le_of_le_add (hYcard ▸ hYle))
        omega
    have hL1 : 1 ≤ L.card := by have := (line_card_bounds hL).1; omega
    have hcast : ((L.card : ℝ) - 1) * (M : ℝ) < (n : ℝ) := by
      have : (((L.card - 1) * M : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast hcard_nat
      rw [Nat.cast_mul, Nat.cast_sub hL1, Nat.cast_one] at this
      exact this
    have hdiv : (L.card : ℝ) - 1 < (n : ℝ) / (M : ℝ) := (lt_div_iff₀ hMR).mpr hcast
    linarith

/-- Proposition 2.4 of Grebennikov--Kwan: for any grid point `p ∈ [0, n)^2` and `α ∈ (0, 1]`,
at most `18 / α^2` lines in `allLines n` passing through `p` have at least `α * n` points. -/
theorem polynomial_tails_lines {n : ℕ} (hn : 1 ≤ n) (p : ℕ × ℕ)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (((allLines n).filter (fun L => p ∈ L ∧ α * (n : ℝ) ≤ (L.card : ℝ))).card : ℝ) ≤
      18 / α ^ 2 := by
  classical
  let S := (allLines n).filter (fun L => p ∈ L ∧ α * (n : ℝ) ≤ (L.card : ℝ))
  change (S.card : ℝ) ≤ 18 / α ^ 2
  by_cases hsmall : α ≤ 2 / (n : ℝ)
  · -- At most n^2 lines pass through p (pick any second point in grid n)
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hsub : S ⊆ ((grid n).erase p).image (lineThrough n p) := by
      intro L hL
      obtain ⟨hLall, hpL, _⟩ := Finset.mem_filter.mp hL
      have h2 : 2 ≤ L.card := (line_card_bounds hLall).1
      obtain ⟨q, hqL, hqp⟩ := Finset.exists_mem_ne (by omega : 1 < L.card) p
      refine Finset.mem_image.mpr ⟨q, Finset.mem_erase.mpr ⟨hqp, line_subset_grid hLall hqL⟩, ?_⟩
      exact (lineThrough_eq_of_mem hLall hpL hqL hqp.symm).symm
    have hcard : S.card ≤ n * n := by
      calc S.card ≤ (((grid n).erase p).image (lineThrough n p)).card := Finset.card_le_card hsub
        _ ≤ ((grid n).erase p).card := Finset.card_image_le
        _ ≤ (grid n).card := Finset.card_le_card (Finset.erase_subset _ _)
        _ = n * n := by simp [grid]
    have hcardR : (S.card : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (S.card : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast hcard
      simpa [pow_two] using this
    have hn_le : (n : ℝ) ≤ 2 / α := by
      rw [le_div_iff₀ hα0]
      have := (le_div_iff₀ hn_pos).mp hsmall
      linarith
    have hsq : (n : ℝ) ^ 2 ≤ (2 / α) ^ 2 := pow_le_pow_left₀ hn_pos.le hn_le 2
    have h4 : (2 / α) ^ 2 ≤ 18 / α ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (pow_pos hα0 2) (pow_pos hα0 2)]
      nlinarith [pow_pos hα0 2]
    exact hcardR.trans (hsq.trans h4)
  · push Not at hsmall
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    let l : ℕ := Nat.ceil (2 / α)
    have hl_ge : 2 / α ≤ (l : ℝ) := Nat.le_ceil _
    have hl_lt : (l : ℝ) < 2 / α + 1 := Nat.ceil_lt_add_one (by positivity)
    have hl_le_n : l ≤ n := by
      apply Nat.ceil_le.mpr
      rw [div_le_iff₀ hα0]
      have := (div_lt_iff₀ hn_pos).mp hsmall
      linarith
    have hl_pos : 1 ≤ l := by
      have : (0 : ℝ) < l := lt_of_lt_of_le (by positivity) hl_ge
      have : 0 < l := by exact_mod_cast this
      omega
    -- Map each L ∈ S to a direction (u, v) in [0, l) × [-(l-1), l-1]
    let dirs : Finset (ℤ × ℤ) :=
      (Finset.Ico (0 : ℤ) (l : ℤ)) ×ˢ (Finset.Icc (-(l : ℤ) + 1) ((l : ℤ) - 1))
    have hdir_exists : ∀ L ∈ S, ∃ d ∈ dirs,
        (∀ r ∈ L, ∃ t : ℤ, (r.1 : ℤ) - p.1 = t * d.1 ∧ (r.2 : ℤ) - p.2 = t * d.2) ∧
        (∀ r ∈ grid n, (∃ t : ℤ, (r.1 : ℤ) - p.1 = t * d.1 ∧ (r.2 : ℤ) - p.2 = t * d.2) → r ∈ L) := by
      intro L hL
      obtain ⟨hLall, hpL, hLbig⟩ := Finset.mem_filter.mp hL
      have h2 : 2 ≤ L.card := (line_card_bounds hLall).1
      obtain ⟨q, hqL, hqp⟩ := Finset.exists_mem_ne (by omega : 1 < L.card) p
      obtain ⟨u, v, hu0, huv_ne, hpar1, hpar2, hbound⟩ :=
        line_card_le_of_step hLall hpL hqL hqp.symm
      let M : ℕ := max u.natAbs v.natAbs
      have hM_pos : (0 : ℝ) < M := by
        have : 0 < M := by
          rcases huv_ne with h | h
          · exact lt_of_lt_of_le (Int.natAbs_pos.mpr h) (le_max_left _ _)
          · exact lt_of_lt_of_le (Int.natAbs_pos.mpr h) (le_max_right _ _)
        exact_mod_cast this
      have hM_lt : M < l := by
        by_contra hge
        push Not at hge
        have hMR : (l : ℝ) ≤ (M : ℝ) := by exact_mod_cast hge
        have hlR : (0 : ℝ) < l := Nat.cast_pos.mpr (by omega)
        have h1 : (n : ℝ) / (M : ℝ) ≤ (n : ℝ) / (l : ℝ) :=
          div_le_div_of_nonneg_left hn_pos.le hlR hMR
        have h2 : (1 : ℝ) ≤ (n : ℝ) / (l : ℝ) := by
          rw [le_div_iff₀ hlR, one_mul]; exact_mod_cast hl_le_n
        have h3 : 2 * ((n : ℝ) / (l : ℝ)) ≤ α * (n : ℝ) := by
          have : 2 / (l : ℝ) ≤ α := (div_le_iff₀ hlR).mpr ((div_le_iff₀ hα0).mp hl_ge |> fun h => by linarith)
          calc 2 * ((n : ℝ) / (l : ℝ)) = (2 / (l : ℝ)) * (n : ℝ) := by ring
            _ ≤ α * (n : ℝ) := mul_le_mul_of_nonneg_right this hn_pos.le
        linarith
      refine ⟨(u, v), ?_, hpar1, hpar2⟩
      refine Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨hu0, ?_⟩, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
      · have : u.natAbs < l := lt_of_le_of_lt (le_max_left _ _) hM_lt
        omega
      · have : v.natAbs < l := lt_of_le_of_lt (le_max_right _ _) hM_lt
        omega
      · have : v.natAbs < l := lt_of_le_of_lt (le_max_right _ _) hM_lt
        omega
    choose f hf_mem hf1 hf2 using hdir_exists
    have hcard_le : S.card ≤ dirs.card := by
      refine Finset.card_le_card_of_injOn (fun L => if hL : L ∈ S then f L hL else (0, 0))
        (fun L hL => by
          have hL' : L ∈ S := Finset.mem_coe.mp hL
          simp only [Finset.mem_coe, dif_pos hL']
          exact hf_mem L hL') ?_
      intro L₁ hL₁ L₂ hL₂ heq
      have hL₁' : L₁ ∈ S := Finset.mem_coe.mp hL₁
      have hL₂' : L₂ ∈ S := Finset.mem_coe.mp hL₂
      simp only [dif_pos hL₁', dif_pos hL₂'] at heq
      ext r
      constructor
      · intro hr
        exact hf2 L₂ hL₂' r (line_subset_grid (Finset.mem_filter.mp hL₁').1 hr)
          (heq ▸ hf1 L₁ hL₁' r hr)
      · intro hr
        exact hf2 L₁ hL₁' r (line_subset_grid (Finset.mem_filter.mp hL₂').1 hr)
          (heq.symm ▸ hf1 L₂ hL₂' r hr)
    have hdirs_card : dirs.card = l * (2 * l - 1) := by
      dsimp [dirs]
      rw [Finset.card_product, Int.card_Ico, Int.card_Icc]
      have h1 : ((l : ℤ) - 0).toNat = l := by omega
      have h2 : ((l : ℤ) - 1 + 1 - (-(l : ℤ) + 1)).toNat = 2 * l - 1 := by omega
      rw [h1, h2]
    have hS_le : (S.card : ℝ) ≤ 2 * (l : ℝ) ^ 2 := by
      have hnat : S.card ≤ 2 * l * l := by
        calc S.card ≤ l * (2 * l - 1) := hdirs_card ▸ hcard_le
          _ ≤ l * (2 * l) := Nat.mul_le_mul_left l (Nat.sub_le _ _)
          _ = 2 * l * l := by ring
      have : (S.card : ℝ) ≤ ((2 * l * l : ℕ) : ℝ) := by exact_mod_cast hnat
      simpa [pow_two, mul_assoc] using this
    have hl_le3 : (l : ℝ) ≤ 3 / α := by
      have h1 : (1 : ℝ) ≤ 1 / α := by rw [le_div_iff₀ hα0]; linarith
      have h2 : 2 / α + 1 / α = 3 / α := by ring
      linarith
    calc (S.card : ℝ) ≤ 2 * (l : ℝ) ^ 2 := hS_le
      _ ≤ 2 * (3 / α) ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg l) hl_le3 2) (by norm_num)
      _ = 18 / α ^ 2 := by ring

/- ## Section 4: Discrete Distributions, Bernoulli Subsampling, Chernoff and Conditional LLL -/

section DiscreteProb

open scoped Classical

/-- A discrete probability distribution on subsets of a finite ground set `U`. -/
structure Dist {α : Type*} (U : Finset α) where
  w : Finset α → ℝ
  nonneg : ∀ S, 0 ≤ w S
  sum_eq : ∑ S ∈ U.powerset, w S = 1

noncomputable def Dist.prob {α : Type*} {U : Finset α} (μ : Dist U)
    (E : Finset α → Prop) : ℝ :=
  ∑ S ∈ U.powerset, if E S then μ.w S else 0

lemma Dist.prob_nonneg {α : Type*} {U : Finset α} (μ : Dist U) (E : Finset α → Prop) :
    0 ≤ μ.prob E :=
  Finset.sum_nonneg fun S _ => by split_ifs <;> [exact μ.nonneg S; exact le_rfl]

lemma Dist.prob_true {α : Type*} {U : Finset α} (μ : Dist U) :
    μ.prob (fun _ => True) = 1 := by
  simp [Dist.prob, μ.sum_eq]

lemma Dist.prob_mono {α : Type*} {U : Finset α} (μ : Dist U) {E F : Finset α → Prop}
    (h : ∀ S ∈ U.powerset, E S → F S) : μ.prob E ≤ μ.prob F := by
  refine Finset.sum_le_sum fun S hS => ?_
  by_cases hE : E S
  · simp [hE, h S hS hE]
  · simp only [if_neg hE]; split_ifs <;> [exact μ.nonneg S; exact le_rfl]

lemma Dist.prob_congr {α : Type*} {U : Finset α} (μ : Dist U) {E F : Finset α → Prop}
    (h : ∀ S ∈ U.powerset, E S ↔ F S) : μ.prob E = μ.prob F := by
  apply le_antisymm
  · exact μ.prob_mono fun S hS hE => (h S hS).mp hE
  · exact μ.prob_mono fun S hS hF => (h S hS).mpr hF

lemma Dist.prob_le_one {α : Type*} {U : Finset α} (μ : Dist U) (E : Finset α → Prop) :
    μ.prob E ≤ 1 := by
  rw [← μ.prob_true]
  exact μ.prob_mono fun _ _ _ => trivial

lemma Dist.prob_and_add_and_not {α : Type*} {U : Finset α} (μ : Dist U)
    (E F : Finset α → Prop) :
    μ.prob (fun S => E S ∧ F S) + μ.prob (fun S => ¬ E S ∧ F S) = μ.prob F := by
  unfold Dist.prob
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hE : E S <;> by_cases hF : F S <;> simp [hE, hF]

lemma Dist.prob_compl {α : Type*} {U : Finset α} (μ : Dist U) (E : Finset α → Prop) :
    μ.prob (fun S => ¬ E S) = 1 - μ.prob E := by
  have h := μ.prob_and_add_and_not E (fun _ => True)
  have h1 : μ.prob (fun S => E S ∧ True) = μ.prob E := μ.prob_congr fun _ _ => by simp
  have h2 : μ.prob (fun S => ¬ E S ∧ True) = μ.prob (fun S => ¬ E S) := μ.prob_congr fun _ _ => by simp
  rw [h1, h2, μ.prob_true] at h
  linarith

lemma Dist.prob_or_le {α : Type*} {U : Finset α} (μ : Dist U) (E F : Finset α → Prop) :
    μ.prob (fun S => E S ∨ F S) ≤ μ.prob E + μ.prob F := by
  unfold Dist.prob
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun S _ => ?_
  by_cases hE : E S <;> by_cases hF : F S <;> simp [hE, hF, μ.nonneg S]

lemma Dist.prob_exists_le {α ι : Type*} {U : Finset α} (μ : Dist U)
    (I : Finset ι) (E : ι → Finset α → Prop) :
    μ.prob (fun S => ∃ i ∈ I, E i S) ≤ ∑ i ∈ I, μ.prob (E i) := by
  induction I using Finset.induction_on with
  | empty => simp [Dist.prob]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hcongr : μ.prob (fun S => ∃ i ∈ insert a s, E i S) =
        μ.prob (fun S => E a S ∨ ∃ i ∈ s, E i S) := by
      refine μ.prob_congr fun S _ => ?_
      simp [Finset.mem_insert]
    rw [hcongr]
    exact (μ.prob_or_le _ _).trans (add_le_add le_rfl ih)

lemma Dist.exists_of_prob_pos {α : Type*} {U : Finset α} (μ : Dist U)
    {E : Finset α → Prop} (hpos : 0 < μ.prob E) :
    ∃ S ⊆ U, 0 < μ.w S ∧ E S := by
  by_contra hall
  push Not at hall
  have hle : μ.prob E ≤ 0 := by
    apply Finset.sum_nonpos
    intro S hS
    by_cases hE : E S
    · rw [if_pos hE]
      exact le_of_not_gt fun hw => hall S (Finset.mem_powerset.mp hS) hw hE
    · rw [if_neg hE]
  linarith

/-- Independent `Ber(p)` weight on subsets of `S₀`. -/
noncomputable def bernW {α : Type*} [DecidableEq α] (S₀ : Finset α) (p : ℝ) (S : Finset α) : ℝ :=
  if S ⊆ S₀ then p ^ S.card * (1 - p) ^ (S₀ \ S).card else 0

lemma bernW_nonneg {α : Type*} [DecidableEq α] {S₀ : Finset α} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset α) :
    0 ≤ bernW S₀ p S := by
  unfold bernW
  split_ifs
  · exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  · exact le_rfl

lemma bernW_of_subset {α : Type*} [DecidableEq α] {S₀ S : Finset α} {p : ℝ}
    (hS : S ⊆ S₀) :
    bernW S₀ p S = p ^ S.card * (1 - p) ^ (S₀ \ S).card := by
  simp [bernW, hS]

lemma bernW_sum_eq_one {α : Type*} [DecidableEq α] (S₀ : Finset α) (p : ℝ) :
    ∑ S ∈ S₀.powerset, bernW S₀ p S = 1 := by
  induction S₀ using Finset.induction_on with
  | empty => simp [bernW]
  | insert a s ha ih =>
    rw [Finset.powerset_insert, Finset.sum_union]
    · have h1 : ∑ S ∈ s.powerset, bernW (insert a s) p S =
          (1 - p) * ∑ S ∈ s.powerset, bernW s p S := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S hS => ?_
        have hSs : S ⊆ s := Finset.mem_powerset.mp hS
        have haS : a ∉ S := fun h => ha (hSs h)
        rw [bernW_of_subset (hSs.trans (Finset.subset_insert a s)), bernW_of_subset hSs]
        have hsdiff : insert a s \ S = insert a (s \ S) := Finset.insert_sdiff_of_notMem s haS
        rw [hsdiff, Finset.card_insert_of_notMem (fun h => ha (Finset.mem_sdiff.mp h).1), pow_succ]
        ring
      have h2 : ∑ S ∈ s.powerset.image (insert a), bernW (insert a s) p S =
          p * ∑ S ∈ s.powerset, bernW s p S := by
        rw [Finset.sum_image, Finset.mul_sum]
        · refine Finset.sum_congr rfl fun S hS => ?_
          have hSs : S ⊆ s := Finset.mem_powerset.mp hS
          have haS : a ∉ S := fun h => ha (hSs h)
          rw [bernW_of_subset (Finset.insert_subset_insert a hSs), bernW_of_subset hSs,
            Finset.card_insert_of_notMem haS, pow_succ]
          have hsdiff : insert a s \ insert a S = s \ S := by
            ext x; simp only [Finset.mem_sdiff, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hxs, hx⟩
              · exact False.elim (hx (Or.inl rfl))
              · exact ⟨hxs, fun h => hx (Or.inr h)⟩
            · rintro ⟨hxs, hxS⟩
              exact ⟨Or.inr hxs, fun h => by
                rcases h with rfl | h
                · exact ha hxs
                · exact hxS h⟩
          rw [hsdiff]
          ring
        · intro S₁ hS₁ S₂ hS₂ heq
          have ha1 : a ∉ S₁ := fun h => ha (Finset.mem_powerset.mp hS₁ h)
          have ha2 : a ∉ S₂ := fun h => ha (Finset.mem_powerset.mp hS₂ h)
          have := congrArg (fun t => t.erase a) heq
          simpa [Finset.erase_insert ha1, Finset.erase_insert ha2] using this
      rw [h1, h2, ih]
      ring
    · rw [Finset.disjoint_left]
      intro S hS1 hS2
      obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hS2
      exact ha (Finset.mem_powerset.mp hS1 (Finset.mem_insert_self a T))

noncomputable def bernDist {α : Type*} [DecidableEq α] {U S₀ : Finset α}
    (hS₀ : S₀ ⊆ U) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Dist U where
  w := bernW S₀ p
  nonneg := bernW_nonneg hp0 hp1
  sum_eq := by
    have hsub : S₀.powerset ⊆ U.powerset := Finset.powerset_mono.mpr hS₀
    rw [← Finset.sum_subset hsub]
    · exact bernW_sum_eq_one S₀ p
    · intro S _ hS
      simp [bernW, Finset.mem_powerset.not.mp hS]

/-- Factorization of `bernW` over a disjoint union `A ∪ B`. -/
lemma bernW_sum_union {α : Type*} [DecidableEq α] {A B : Finset α} (hAB : Disjoint A B)
    (p : ℝ) (g h : Finset α → ℝ) :
    ∑ S ∈ (A ∪ B).powerset, bernW (A ∪ B) p S * (g (S ∩ A) * h (S ∩ B)) =
      (∑ S₁ ∈ A.powerset, bernW A p S₁ * g S₁) *
      (∑ S₂ ∈ B.powerset, bernW B p S₂ * h S₂) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_bij (fun S _ => (S ∩ A, S ∩ B)) ?_ ?_ ?_ ?_
  · intro S _
    exact Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
      Finset.mem_powerset.mpr Finset.inter_subset_right⟩
  · intro S₁ hS₁ S₂ hS₂ heq
    have h1 : S₁ ∩ A = S₂ ∩ A := congrArg Prod.fst heq
    have h2 : S₁ ∩ B = S₂ ∩ B := congrArg Prod.snd heq
    have hs1 : S₁ ⊆ A ∪ B := Finset.mem_powerset.mp hS₁
    have hs2 : S₂ ⊆ A ∪ B := Finset.mem_powerset.mp hS₂
    calc S₁ = S₁ ∩ (A ∪ B) := (Finset.inter_eq_left.mpr hs1).symm
      _ = (S₁ ∩ A) ∪ (S₁ ∩ B) := Finset.inter_union_distrib_left S₁ A B
      _ = (S₂ ∩ A) ∪ (S₂ ∩ B) := by rw [h1, h2]
      _ = S₂ ∩ (A ∪ B) := (Finset.inter_union_distrib_left S₂ A B).symm
      _ = S₂ := Finset.inter_eq_left.mpr hs2
  · intro ⟨S₁, S₂⟩ hmem
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
    have hS₁ : S₁ ⊆ A := Finset.mem_powerset.mp h1
    have hS₂ : S₂ ⊆ B := Finset.mem_powerset.mp h2
    refine ⟨S₁ ∪ S₂, Finset.mem_powerset.mpr (Finset.union_subset_union hS₁ hS₂), ?_⟩
    ext x <;> simp only [Finset.mem_inter, Finset.mem_union]
    · exact ⟨fun ⟨hx, hxA⟩ => hx.elim id fun hx2 => False.elim (Finset.disjoint_left.mp hAB hxA (hS₂ hx2)),
        fun hx => ⟨Or.inl hx, hS₁ hx⟩⟩
    · exact ⟨fun ⟨hx, hxB⟩ => hx.elim (fun hx1 => False.elim (Finset.disjoint_left.mp hAB (hS₁ hx1) hxB)) id,
        fun hx => ⟨Or.inr hx, hS₂ hx⟩⟩
  · intro S hS
    have hSUB : S ⊆ A ∪ B := Finset.mem_powerset.mp hS
    have hdisjS : Disjoint (S ∩ A) (S ∩ B) :=
      hAB.mono Finset.inter_subset_right Finset.inter_subset_right
    have hSunion : S = (S ∩ A) ∪ (S ∩ B) := by
      rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hSUB]
    have hScard : S.card = (S ∩ A).card + (S ∩ B).card := by
      conv_lhs => rw [hSunion]
      exact Finset.card_union_of_disjoint hdisjS
    have hdisjD : Disjoint (A \ (S ∩ A)) (B \ (S ∩ B)) :=
      hAB.mono Finset.sdiff_subset Finset.sdiff_subset
    have hDunion : (A ∪ B) \ S = (A \ (S ∩ A)) ∪ (B \ (S ∩ B)) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto
    have hDcard : ((A ∪ B) \ S).card = (A \ (S ∩ A)).card + (B \ (S ∩ B)).card := by
      rw [hDunion, Finset.card_union_of_disjoint hdisjD]
    rw [bernW_of_subset hSUB, bernW_of_subset Finset.inter_subset_right,
      bernW_of_subset Finset.inter_subset_right, hScard, hDcard, pow_add, pow_add]
    ring

/-- Independence of events depending on disjoint coordinate sets under `bernDist`. -/
lemma bern_prob_indep {α : Type*} [DecidableEq α] {U S₀ X Y : Finset α}
    (hS₀ : S₀ ⊆ U) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hXY : Disjoint X Y) {E F : Finset α → Prop}
    (hE : ∀ S ⊆ S₀, E S ↔ E (S ∩ X)) (hF : ∀ S ⊆ S₀, F S ↔ F (S ∩ Y)) :
    (bernDist hS₀ hp0 hp1).prob (fun S => E S ∧ F S) =
      (bernDist hS₀ hp0 hp1).prob E * (bernDist hS₀ hp0 hp1).prob F := by
  let A := S₀ ∩ X
  let B := S₀ \ X
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact (Finset.mem_sdiff.mp hxB).2 (Finset.mem_inter.mp hxA).2
  have hS₀_eq : S₀ = A ∪ B := by
    ext x; simp only [A, B, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have hprob_eq : ∀ P : Finset α → Prop,
      (bernDist hS₀ hp0 hp1).prob P =
        ∑ S ∈ (A ∪ B).powerset, bernW (A ∪ B) p S * (if P S then (1 : ℝ) else 0) := by
    intro P
    unfold Dist.prob bernDist
    dsimp only
    have hsub : S₀.powerset ⊆ U.powerset := Finset.powerset_mono.mpr hS₀
    rw [← Finset.sum_subset hsub]
    · rw [← hS₀_eq]
      refine Finset.sum_congr rfl fun S _ => ?_
      split_ifs <;> simp
    · intro S _ hS
      simp [bernW, Finset.mem_powerset.not.mp hS]
  have h1 : ∀ S ∈ (A ∪ B).powerset, E S ↔ E (S ∩ A) := by
    intro S hS
    have hSS₀ : S ⊆ S₀ := hS₀_eq.symm ▸ Finset.mem_powerset.mp hS
    rw [hE S hSS₀]
    have hEq : S ∩ X = S ∩ A := by
      ext x; simp only [A, Finset.mem_inter]
      exact ⟨fun ⟨hxS, hxX⟩ => ⟨hxS, hSS₀ hxS, hxX⟩, fun ⟨hxS, _, hxX⟩ => ⟨hxS, hxX⟩⟩
    rw [hEq]
  have h2 : ∀ S ∈ (A ∪ B).powerset, F S ↔ F (S ∩ B) := by
    intro S hS
    have hSS₀ : S ⊆ S₀ := hS₀_eq.symm ▸ Finset.mem_powerset.mp hS
    rw [hF S hSS₀, hF (S ∩ B) (Finset.inter_subset_left.trans hSS₀)]
    have hEq : S ∩ Y = (S ∩ B) ∩ Y := by
      ext x; simp only [B, Finset.mem_inter, Finset.mem_sdiff]
      exact ⟨fun ⟨hxS, hxY⟩ => ⟨⟨hxS, hSS₀ hxS, fun hxX => Finset.disjoint_left.mp hXY hxX hxY⟩, hxY⟩,
        fun ⟨⟨hxS, _⟩, hxY⟩ => ⟨hxS, hxY⟩⟩
    rw [hEq]
  rw [hprob_eq (fun S => E S ∧ F S), hprob_eq E, hprob_eq F]
  have h1' := bernW_sum_union hAB p (fun S₁ => if E S₁ then (1 : ℝ) else 0)
    (fun S₂ => if F S₂ then (1 : ℝ) else 0)
  have h2' := bernW_sum_union hAB p (fun S₁ => if E S₁ then (1 : ℝ) else 0) (fun _ => (1 : ℝ))
  have h3' := bernW_sum_union hAB p (fun _ => (1 : ℝ)) (fun S₂ => if F S₂ then (1 : ℝ) else 0)
  calc _
      = ∑ S ∈ (A ∪ B).powerset, bernW (A ∪ B) p S *
          ((if E (S ∩ A) then (1 : ℝ) else 0) * (if F (S ∩ B) then (1 : ℝ) else 0)) := by
        refine Finset.sum_congr rfl fun S hS => ?_
        by_cases hEA : E (S ∩ A) <;> by_cases hFB : F (S ∩ B)
        · simp only [if_pos (And.intro ((h1 S hS).mpr hEA) ((h2 S hS).mpr hFB)), if_pos hEA, if_pos hFB, mul_one]
        · simp only [if_neg (fun h : E S ∧ F S => hFB ((h2 S hS).mp h.2)), if_neg hFB, mul_zero]
        · simp only [if_neg (fun h : E S ∧ F S => hEA ((h1 S hS).mp h.1)), if_neg hEA, zero_mul]
        · simp only [if_neg (fun h : E S ∧ F S => hEA ((h1 S hS).mp h.1)), if_neg hEA, zero_mul]
    _ = (∑ S₁ ∈ A.powerset, bernW A p S₁ * if E S₁ then (1 : ℝ) else 0) *
        (∑ S₂ ∈ B.powerset, bernW B p S₂ * if F S₂ then (1 : ℝ) else 0) := h1'
    _ = ((∑ S₁ ∈ A.powerset, bernW A p S₁ * if E S₁ then (1 : ℝ) else 0) *
          (∑ S₂ ∈ B.powerset, bernW B p S₂ * (1 : ℝ))) *
        ((∑ S₁ ∈ A.powerset, bernW A p S₁ * (1 : ℝ)) *
          (∑ S₂ ∈ B.powerset, bernW B p S₂ * if F S₂ then (1 : ℝ) else 0)) := by
        have hsumA : ∑ S₁ ∈ A.powerset, bernW A p S₁ * (1 : ℝ) = 1 := by simpa using bernW_sum_eq_one A p
        have hsumB : ∑ S₂ ∈ B.powerset, bernW B p S₂ * (1 : ℝ) = 1 := by simpa using bernW_sum_eq_one B p
        rw [hsumA, hsumB, mul_one, one_mul]
    _ = (∑ S ∈ (A ∪ B).powerset, bernW (A ∪ B) p S * ((if E (S ∩ A) then (1 : ℝ) else 0) * (1 : ℝ))) *
        (∑ S ∈ (A ∪ B).powerset, bernW (A ∪ B) p S * ((1 : ℝ) * (if F (S ∩ B) then (1 : ℝ) else 0))) := by
        rw [← h2', ← h3']
    _ = (∑ S ∈ (A ∪ B).powerset, bernW (A ∪ B) p S * if E S then (1 : ℝ) else 0) *
        (∑ S ∈ (A ∪ B).powerset, bernW (A ∪ B) p S * if F S then (1 : ℝ) else 0) := by
        congr 1
        · refine Finset.sum_congr rfl fun S hS => ?_
          by_cases hEA : E (S ∩ A)
          · simp only [if_pos ((h1 S hS).mpr hEA), if_pos hEA, mul_one]
          · simp only [if_neg (fun h => hEA ((h1 S hS).mp h)), if_neg hEA, zero_mul]
        · refine Finset.sum_congr rfl fun S hS => ?_
          by_cases hFB : F (S ∩ B)
          · simp only [if_pos ((h2 S hS).mpr hFB), if_pos hFB, one_mul]
          · simp only [if_neg (fun h => hFB ((h2 S hS).mp h)), if_neg hFB, mul_zero]

/-- Marginal of `bernDist` onto a subset `A ⊆ S₀`. -/
lemma bern_prob_inter {α : Type*} [DecidableEq α] {U S₀ A : Finset α}
    (hS₀ : S₀ ⊆ U) (hAS₀ : A ⊆ S₀) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : Finset α → Prop) :
    (bernDist hS₀ hp0 hp1).prob (fun S => P (S ∩ A)) =
      ∑ S₁ ∈ A.powerset.filter P, bernW A p S₁ := by
  let B := S₀ \ A
  have hAB : Disjoint A B := Finset.disjoint_sdiff
  have hS₀_eq : S₀ = A ∪ B := (Finset.union_sdiff_of_subset hAS₀).symm
  unfold Dist.prob bernDist
  dsimp only
  have hsub : S₀.powerset ⊆ U.powerset := Finset.powerset_mono.mpr hS₀
  rw [← Finset.sum_subset hsub]
  · rw [hS₀_eq]
    have hrew : ∑ S ∈ (A ∪ B).powerset, (if P (S ∩ A) then bernW (A ∪ B) p S else 0) =
        ∑ S ∈ (A ∪ B).powerset, bernW (A ∪ B) p S * ((if P (S ∩ A) then (1 : ℝ) else 0) * (1 : ℝ)) := by
      refine Finset.sum_congr rfl fun S _ => ?_
      split_ifs <;> simp
    rw [hrew, bernW_sum_union hAB p (fun S₁ => if P S₁ then (1 : ℝ) else 0) (fun _ => (1 : ℝ))]
    have hsumB : ∑ S₂ ∈ B.powerset, bernW B p S₂ * (1 : ℝ) = 1 := by
      simpa using bernW_sum_eq_one B p
    rw [hsumB, mul_one, Finset.sum_filter]
    refine Finset.sum_congr rfl fun S₁ _ => ?_
    split_ifs <;> simp
  · intro S _ hS
    simp [bernW, Finset.mem_powerset.not.mp hS]

/-- Probability of containing a fixed subset `T ⊆ S₀` under `bernDist S₀ p`. -/
lemma bern_prob_subset {α : Type*} [DecidableEq α] {U S₀ T : Finset α}
    (hS₀ : S₀ ⊆ U) (hTS₀ : T ⊆ S₀) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernDist hS₀ hp0 hp1).prob (fun S => T ⊆ S) = p ^ T.card := by
  have hcongr : (bernDist hS₀ hp0 hp1).prob (fun S => T ⊆ S) =
      (bernDist hS₀ hp0 hp1).prob (fun S => S ∩ T = T) :=
    (bernDist hS₀ hp0 hp1).prob_congr fun _ _ => Finset.inter_eq_right.symm
  rw [hcongr, bern_prob_inter hS₀ hTS₀ hp0 hp1 (fun S₁ => S₁ = T), Finset.sum_filter]
  rw [Finset.sum_eq_single T]
  · simp [bernW_of_subset Subset.rfl]
  · intro S₁ _ hne; simp [hne]
  · intro hnot; exact False.elim (hnot (Finset.mem_powerset.mpr Subset.rfl))

/-- Moment generating function of `|S|` under `bernW A p`. -/
lemma bernW_mgf {α : Type*} [DecidableEq α] (A : Finset α) (p t : ℝ) :
    ∑ S ∈ A.powerset, bernW A p S * Real.exp (t * (S.card : ℝ)) =
      (1 - p + p * Real.exp t) ^ A.card := by
  induction A using Finset.induction_on with
  | empty => simp [bernW]
  | insert a s ha ih =>
    rw [Finset.powerset_insert, Finset.sum_union, Finset.card_insert_of_notMem ha, pow_succ]
    · have h1 : ∑ S ∈ s.powerset, bernW (insert a s) p S * Real.exp (t * (S.card : ℝ)) =
          (1 - p) * ∑ S ∈ s.powerset, bernW s p S * Real.exp (t * (S.card : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S hS => ?_
        have hSs : S ⊆ s := Finset.mem_powerset.mp hS
        have haS : a ∉ S := fun h => ha (hSs h)
        rw [bernW_of_subset (hSs.trans (Finset.subset_insert a s)), bernW_of_subset hSs,
          Finset.insert_sdiff_of_notMem s haS,
          Finset.card_insert_of_notMem (fun h => ha (Finset.mem_sdiff.mp h).1), pow_succ]
        ring
      have h2 : ∑ S ∈ s.powerset.image (insert a),
            bernW (insert a s) p S * Real.exp (t * (S.card : ℝ)) =
          (p * Real.exp t) * ∑ S ∈ s.powerset, bernW s p S * Real.exp (t * (S.card : ℝ)) := by
        rw [Finset.sum_image, Finset.mul_sum]
        · refine Finset.sum_congr rfl fun S hS => ?_
          have hSs : S ⊆ s := Finset.mem_powerset.mp hS
          have haS : a ∉ S := fun h => ha (hSs h)
          rw [bernW_of_subset (Finset.insert_subset_insert a hSs), bernW_of_subset hSs,
            Finset.card_insert_of_notMem haS, pow_succ, Nat.cast_add, Nat.cast_one]
          have hsdiff : insert a s \ insert a S = s \ S := by
            ext x; simp only [Finset.mem_sdiff, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hxs, hx⟩
              · exact False.elim (hx (Or.inl rfl))
              · exact ⟨hxs, fun h => hx (Or.inr h)⟩
            · rintro ⟨hxs, hxS⟩
              exact ⟨Or.inr hxs, fun h => by
                rcases h with rfl | h
                · exact ha hxs
                · exact hxS h⟩
          rw [hsdiff, mul_add, mul_one, Real.exp_add]
          ring
        · intro S₁ hS₁ S₂ hS₂ heq
          have ha1 : a ∉ S₁ := fun h => ha (Finset.mem_powerset.mp hS₁ h)
          have ha2 : a ∉ S₂ := fun h => ha (Finset.mem_powerset.mp hS₂ h)
          have := congrArg (fun t => t.erase a) heq
          simpa [Finset.erase_insert ha1, Finset.erase_insert ha2] using this
      rw [h1, h2, ih]
      ring
    · rw [Finset.disjoint_left]
      intro S hS1 hS2
      obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hS2
      exact ha (Finset.mem_powerset.mp hS1 (Finset.mem_insert_self a T))

/-- Upper Chernoff tail for `|S ∩ A|` with upper bound `(A.card : ℝ) ≤ M`. -/
lemma bern_chernoff_upper_le {α : Type*} [DecidableEq α] {U S₀ A : Finset α}
    (hS₀ : S₀ ⊆ U) (hAS₀ : A ⊆ S₀) {p δ M : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hAM : (A.card : ℝ) ≤ M) :
    (bernDist hS₀ hp0 hp1).prob (fun S => (1 + δ) * (p * M) < ((S ∩ A).card : ℝ)) ≤
      Real.exp (-(δ ^ 2 * (p * M) / 3)) := by
  rw [bern_prob_inter hS₀ hAS₀ hp0 hp1 (fun S₁ => (1 + δ) * (p * M) < (S₁.card : ℝ))]
  let t : ℝ := Real.log (1 + δ)
  have ht0 : 0 < t := Real.log_pos (by linarith)
  have hexpt : Real.exp t = 1 + δ := Real.exp_log (by linarith)
  have hM0 : 0 ≤ M := (Nat.cast_nonneg A.card).trans hAM
  have hmarkov : Real.exp (t * ((1 + δ) * (p * M))) *
      ∑ S₁ ∈ A.powerset.filter (fun S₁ => (1 + δ) * (p * M) < (S₁.card : ℝ)), bernW A p S₁ ≤
      ∑ S₁ ∈ A.powerset, bernW A p S₁ * Real.exp (t * (S₁.card : ℝ)) := by
    rw [Finset.mul_sum]
    calc ∑ S₁ ∈ A.powerset.filter (fun S₁ => (1 + δ) * (p * M) < (S₁.card : ℝ)),
            Real.exp (t * ((1 + δ) * (p * M))) * bernW A p S₁
        ≤ ∑ S₁ ∈ A.powerset.filter (fun S₁ => (1 + δ) * (p * M) < (S₁.card : ℝ)),
            bernW A p S₁ * Real.exp (t * (S₁.card : ℝ)) := by
          refine Finset.sum_le_sum fun S₁ hS₁ => ?_
          rw [mul_comm (Real.exp _)]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (bernW_nonneg hp0 hp1 S₁)
          exact mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hS₁).2.le ht0.le
      _ ≤ ∑ S₁ ∈ A.powerset, bernW A p S₁ * Real.exp (t * (S₁.card : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun S₁ _ _ =>
            mul_nonneg (bernW_nonneg hp0 hp1 S₁) (Real.exp_pos _).le
  rw [bernW_mgf A p t, hexpt] at hmarkov
  have hmgf_le : (1 - p + p * (1 + δ)) ^ A.card ≤ Real.exp (p * M * δ) := by
    have hstep : 1 - p + p * (1 + δ) ≤ Real.exp (p * δ) := by
      have := Real.add_one_le_exp (p * δ)
      linarith
    have hnn : 0 ≤ 1 - p + p * (1 + δ) := by nlinarith
    calc (1 - p + p * (1 + δ)) ^ A.card
        ≤ (Real.exp (p * δ)) ^ A.card := pow_le_pow_left₀ hnn hstep A.card
      _ = Real.exp ((A.card : ℝ) * (p * δ)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (p * M * δ) := Real.exp_le_exp.mpr (by
          have : (A.card : ℝ) * (p * δ) ≤ M * (p * δ) :=
            mul_le_mul_of_nonneg_right hAM (mul_nonneg hp0 hδ0.le)
          linarith)
  have hcomb : Real.exp (t * ((1 + δ) * (p * M))) *
      ∑ S₁ ∈ A.powerset.filter (fun S₁ => (1 + δ) * (p * M) < (S₁.card : ℝ)), bernW A p S₁ ≤
      Real.exp (p * M * δ) := hmarkov.trans hmgf_le
  have hdiv : ∑ S₁ ∈ A.powerset.filter (fun S₁ => (1 + δ) * (p * M) < (S₁.card : ℝ)), bernW A p S₁ ≤
      Real.exp (p * M * δ - t * ((1 + δ) * (p * M))) := by
    rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos _), mul_comm]
    exact hcomb
  refine hdiv.trans (Real.exp_le_exp.mpr ?_)
  have hlog := chernoff_log_upper hδ0.le hδ1
  have hpm : 0 ≤ p * M := mul_nonneg hp0 hM0
  have hmul := mul_le_mul_of_nonneg_left hlog hpm
  dsimp [t]
  linarith

/-- Lower Chernoff tail for `|S ∩ A|`. -/
lemma bern_chernoff_lower {α : Type*} [DecidableEq α] {U S₀ A : Finset α}
    (hS₀ : S₀ ⊆ U) (hAS₀ : A ⊆ S₀) {p δ : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (bernDist hS₀ hp0 hp1).prob (fun S => ((S ∩ A).card : ℝ) < (1 - δ) * (p * (A.card : ℝ))) ≤
      Real.exp (-(δ ^ 2 * (p * (A.card : ℝ)) / 3)) := by
  rw [bern_prob_inter hS₀ hAS₀ hp0 hp1 (fun S₁ => (S₁.card : ℝ) < (1 - δ) * (p * (A.card : ℝ)))]
  let t : ℝ := Real.log (1 - δ)
  have ht0 : t < 0 := Real.log_neg (by linarith) (by linarith)
  have hexpt : Real.exp t = 1 - δ := Real.exp_log (by linarith)
  have hmarkov : Real.exp (t * ((1 - δ) * (p * (A.card : ℝ)))) *
      ∑ S₁ ∈ A.powerset.filter (fun S₁ => (S₁.card : ℝ) < (1 - δ) * (p * (A.card : ℝ))),
        bernW A p S₁ ≤
      ∑ S₁ ∈ A.powerset, bernW A p S₁ * Real.exp (t * (S₁.card : ℝ)) := by
    rw [Finset.mul_sum]
    calc ∑ S₁ ∈ A.powerset.filter (fun S₁ => (S₁.card : ℝ) < (1 - δ) * (p * (A.card : ℝ))),
            Real.exp (t * ((1 - δ) * (p * (A.card : ℝ)))) * bernW A p S₁
        ≤ ∑ S₁ ∈ A.powerset.filter (fun S₁ => (S₁.card : ℝ) < (1 - δ) * (p * (A.card : ℝ))),
            bernW A p S₁ * Real.exp (t * (S₁.card : ℝ)) := by
          refine Finset.sum_le_sum fun S₁ hS₁ => ?_
          rw [mul_comm (Real.exp _)]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (bernW_nonneg hp0 hp1 S₁)
          exact mul_le_mul_of_nonpos_left (Finset.mem_filter.mp hS₁).2.le ht0.le
      _ ≤ ∑ S₁ ∈ A.powerset, bernW A p S₁ * Real.exp (t * (S₁.card : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun S₁ _ _ =>
            mul_nonneg (bernW_nonneg hp0 hp1 S₁) (Real.exp_pos _).le
  rw [bernW_mgf A p t, hexpt] at hmarkov
  have hmgf_le : (1 - p + p * (1 - δ)) ^ A.card ≤ Real.exp (-(p * (A.card : ℝ) * δ)) := by
    have hstep : 1 - p + p * (1 - δ) ≤ Real.exp (-(p * δ)) := by
      have := Real.add_one_le_exp (-(p * δ))
      linarith
    have hnn : 0 ≤ 1 - p + p * (1 - δ) := by nlinarith
    calc (1 - p + p * (1 - δ)) ^ A.card
        ≤ (Real.exp (-(p * δ))) ^ A.card := pow_le_pow_left₀ hnn hstep A.card
      _ = Real.exp ((A.card : ℝ) * (-(p * δ))) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp (-(p * (A.card : ℝ) * δ)) := by congr 1; ring
  have hcomb := hmarkov.trans hmgf_le
  have hdiv : ∑ S₁ ∈ A.powerset.filter (fun S₁ => (S₁.card : ℝ) < (1 - δ) * (p * (A.card : ℝ))),
        bernW A p S₁ ≤
      Real.exp (-(p * (A.card : ℝ) * δ) - t * ((1 - δ) * (p * (A.card : ℝ)))) := by
    rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos _), mul_comm]
    exact hcomb
  refine hdiv.trans (Real.exp_le_exp.mpr ?_)
  have hlog := chernoff_log_lower hδ0.le hδ1
  have hpm : 0 ≤ p * (A.card : ℝ) := mul_nonneg hp0 (Nat.cast_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hlog hpm
  dsimp [t]
  linarith

/-- Union bound for light lines: `P(|S ∩ A| ≥ r) ≤ C(|A|, r) * p^r`. -/
lemma bern_card_ge_le {α : Type*} [DecidableEq α] {U S₀ A : Finset α}
    (hS₀ : S₀ ⊆ U) (hAS₀ : A ⊆ S₀) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (r : ℕ) :
    (bernDist hS₀ hp0 hp1).prob (fun S => r ≤ (S ∩ A).card) ≤
      ((A.card.choose r : ℕ) : ℝ) * p ^ r := by
  have himp : ∀ S ∈ U.powerset, r ≤ (S ∩ A).card → ∃ T ∈ A.powersetCard r, T ⊆ S := by
    intro S _ hcard
    obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hcard
    exact ⟨T, Finset.mem_powersetCard.mpr ⟨hTS.trans Finset.inter_subset_right, hTcard⟩,
      hTS.trans Finset.inter_subset_left⟩
  calc (bernDist hS₀ hp0 hp1).prob (fun S => r ≤ (S ∩ A).card)
      ≤ (bernDist hS₀ hp0 hp1).prob (fun S => ∃ T ∈ A.powersetCard r, T ⊆ S) :=
        (bernDist hS₀ hp0 hp1).prob_mono himp
    _ ≤ ∑ T ∈ A.powersetCard r, (bernDist hS₀ hp0 hp1).prob (fun S => T ⊆ S) :=
        (bernDist hS₀ hp0 hp1).prob_exists_le (A.powersetCard r) (fun T S => T ⊆ S)
    _ = ∑ _T ∈ A.powersetCard r, p ^ r := by
        refine Finset.sum_congr rfl fun T hT => ?_
        obtain ⟨hTA, hTcard⟩ := Finset.mem_powersetCard.mp hT
        rw [bern_prob_subset hS₀ (hTA.trans hAS₀) hp0 hp1, hTcard]
    _ = ((A.card.choose r : ℕ) : ℝ) * p ^ r := by
        simp [Finset.card_powersetCard]

/-- Conditional Lovász Local Lemma (Proposition 2.2 of Grebennikov--Kwan) on `bernDist`. -/
theorem lll_conditional {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    {U S₀ : Finset α} (hS₀ : S₀ ⊆ U) {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (J : Finset ι) (E : ι → Finset α → Prop) (X : ι → Finset α)
    (hdep : ∀ j ∈ J, ∀ S ⊆ S₀, E j S ↔ E j (S ∩ X j))
    (hq0 : 0 ≤ q) (hq4 : q ≤ 1 / 4)
    (hprob : ∀ j ∈ J, (bernDist hS₀ hp0 hp1).prob (E j) ≤ q)
    {Δ : ℕ}
    (hdeg : ∀ j ∈ J, (J.filter (fun j' => j' ≠ j ∧ ¬ Disjoint (X j) (X j'))).card ≤ Δ)
    (hlll : 4 * q * (Δ : ℝ) ≤ 1) :
    let μ := bernDist hS₀ hp0 hp1
    let avoid : Finset ι → Finset α → Prop := fun R S => ∀ j ∈ R, ¬ E j S
    0 < μ.prob (avoid J) ∧
    (∀ (F : Finset α → Prop) (XF : Finset α) (M : ℕ),
      (∀ S ⊆ S₀, F S ↔ F (S ∩ XF)) →
      (J.filter (fun j => ¬ Disjoint XF (X j))).card ≤ M →
      μ.prob (fun S => F S ∧ avoid J S) ≤ μ.prob F * Real.exp (6 * q * (M : ℝ)) * μ.prob (avoid J)) := by
  intro μ avoid
  have h12q_pos : 0 < 1 - 2 * q := by linarith
  -- Dependency of `avoid R` on `R.biUnion X`
  have havoid_dep : ∀ R ⊆ J, ∀ S ⊆ S₀, avoid R S ↔ avoid R (S ∩ R.biUnion X) := by
    intro R hRJ S hSS₀
    constructor <;> intro h j hj
    · have hEq : (S ∩ R.biUnion X) ∩ X j = S ∩ X j := by
        ext x; simp only [Finset.mem_inter, Finset.mem_biUnion]
        exact ⟨fun ⟨⟨hxS, _⟩, hxX⟩ => ⟨hxS, hxX⟩, fun ⟨hxS, hxX⟩ => ⟨⟨hxS, j, hj, hxX⟩, hxX⟩⟩
      rw [hdep j (hRJ hj) (S ∩ R.biUnion X) (Finset.inter_subset_left.trans hSS₀), hEq,
        ← hdep j (hRJ hj) S hSS₀]
      exact h j hj
    · have hEq : (S ∩ R.biUnion X) ∩ X j = S ∩ X j := by
        ext x; simp only [Finset.mem_inter, Finset.mem_biUnion]
        exact ⟨fun ⟨⟨hxS, _⟩, hxX⟩ => ⟨hxS, hxX⟩, fun ⟨hxS, hxX⟩ => ⟨⟨hxS, j, hj, hxX⟩, hxX⟩⟩
      have hj' := h j hj
      rw [hdep j (hRJ hj) (S ∩ R.biUnion X) (Finset.inter_subset_left.trans hSS₀), hEq,
        ← hdep j (hRJ hj) S hSS₀] at hj'
      exact hj'
  -- Key inductive claim on |R|
  have hind : ∀ n : ℕ, ∀ R ⊆ J, R.card = n →
      0 < μ.prob (avoid R) ∧
      (∀ i ∈ J, i ∉ R → μ.prob (fun S => E i S ∧ avoid R S) ≤ 2 * q * μ.prob (avoid R)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro R hRJ hRcard
      -- Step 1: Show 0 < μ.prob (avoid R)
      have hRpos : 0 < μ.prob (avoid R) := by
        by_cases hRemp : R = ∅
        · subst hRemp
          have : μ.prob (avoid ∅) = 1 := by
            rw [← μ.prob_true]; exact μ.prob_congr fun _ _ => by simp [avoid]
          rw [this]; norm_num
        · obtain ⟨r, hrR⟩ := Finset.nonempty_iff_ne_empty.mpr hRemp
          let R' := R.erase r
          have hR'J : R' ⊆ J := (Finset.erase_subset r R).trans hRJ
          have hR'card : R'.card < n := by
            rw [← hRcard]; exact Finset.card_erase_lt_of_mem hrR
          have hIH := ih R'.card hR'card R' hR'J rfl
          have hsplit : μ.prob (fun S => E r S ∧ avoid R' S) + μ.prob (avoid R) =
              μ.prob (avoid R') := by
            have hcongr : μ.prob (fun S => ¬ E r S ∧ avoid R' S) = μ.prob (avoid R) := by
              refine μ.prob_congr fun S _ => ?_
              simp only [avoid, R', Finset.mem_erase]
              exact ⟨fun ⟨hr, hrest⟩ j hj => by
                by_cases hjr : j = r
                · exact hjr ▸ hr
                · exact hrest j ⟨hjr, hj⟩,
                fun hall => ⟨hall r hrR, fun j ⟨_, hj⟩ => hall j hj⟩⟩
            rw [← hcongr]
            exact μ.prob_and_add_and_not (E r) (avoid R')
          have hbound := hIH.2 r (hRJ hrR) (Finset.notMem_erase r R)
          have hge : (1 - 2 * q) * μ.prob (avoid R') ≤ μ.prob (avoid R) := by linarith
          exact lt_of_lt_of_le (mul_pos h12q_pos hIH.1) hge
      -- Helper: telescoping lower bound for any R₁ ⊆ R with R₂ = R \ R₁ when R₁ is nonempty
      have htelesc : ∀ R₂ ⊆ R, R₂ ≠ R →
          (1 - 2 * q) ^ (R \ R₂).card * μ.prob (avoid R₂) ≤ μ.prob (avoid R) := by
        intro R₂ hR₂R hne
        -- Induct on m = (R \ R₂).card
        have hgen : ∀ (D : Finset ι), D ⊆ R → Disjoint D R₂ → D ∪ R₂ ⊆ R →
            (D ∪ R₂).card ≤ R.card →
            (∀ T ⊆ D ∪ R₂, T.card < R.card → ∀ j ∈ J, j ∉ T →
              μ.prob (fun S => E j S ∧ avoid T S) ≤ 2 * q * μ.prob (avoid T)) →
            (1 - 2 * q) ^ D.card * μ.prob (avoid R₂) ≤ μ.prob (avoid (D ∪ R₂)) := by
          intro D
          induction D using Finset.induction_on with
          | empty => intro _ _ _ _ _; simp
          | insert d D' hdD' ihD =>
            intro hDR hdisj hUsub hUcard hstep
            have hdnotR₂ : d ∉ R₂ := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self d D')
            have hdnotU : d ∉ D' ∪ R₂ := by simp [hdD', hdnotR₂]
            have hD'sub : D' ∪ R₂ ⊆ insert d D' ∪ R₂ :=
              Finset.union_subset_union_left (Finset.subset_insert d D')
            have hD'card_lt : (D' ∪ R₂).card < R.card := by
              have hlt : (D' ∪ R₂).card < (insert d (D' ∪ R₂)).card := by
                rw [Finset.card_insert_of_notMem hdnotU]; omega
              rw [Finset.insert_union] at hUcard
              exact lt_of_lt_of_le hlt hUcard
            have hD'prev := ihD ((Finset.subset_insert d D').trans hDR)
              (hdisj.mono_left (Finset.subset_insert d D'))
              (hD'sub.trans hUsub) (hD'card_lt.le)
              (fun T hT => hstep T (hT.trans hD'sub))
            have hstep_d := hstep (D' ∪ R₂) hD'sub hD'card_lt d
              (hRJ (hDR (Finset.mem_insert_self d D'))) hdnotU
            have hsplit : μ.prob (fun S => E d S ∧ avoid (D' ∪ R₂) S) +
                μ.prob (avoid (insert d D' ∪ R₂)) = μ.prob (avoid (D' ∪ R₂)) := by
              have hcongr : μ.prob (fun S => ¬ E d S ∧ avoid (D' ∪ R₂) S) =
                  μ.prob (avoid (insert d D' ∪ R₂)) := by
                refine μ.prob_congr fun S _ => ?_
                simp only [avoid, Finset.insert_union, Finset.mem_insert]
                exact ⟨fun ⟨hd, hr⟩ j hj => hj.elim (fun h => h ▸ hd) (hr j),
                  fun hall => ⟨hall d (Or.inl rfl), fun j hj => hall j (Or.inr hj)⟩⟩
              rw [← hcongr]
              exact μ.prob_and_add_and_not (E d) (avoid (D' ∪ R₂))
            have hge : (1 - 2 * q) * μ.prob (avoid (D' ∪ R₂)) ≤ μ.prob (avoid (insert d D' ∪ R₂)) := by
              linarith
            rw [Finset.card_insert_of_notMem hdD', pow_succ, mul_comm ((1 - 2 * q) ^ D'.card),
              mul_assoc]
            exact (mul_le_mul_of_nonneg_left hD'prev h12q_pos.le).trans hge
        have hstep_all : ∀ T ⊆ (R \ R₂) ∪ R₂, T.card < R.card → ∀ j ∈ J, j ∉ T →
            μ.prob (fun S => E j S ∧ avoid T S) ≤ 2 * q * μ.prob (avoid T) := by
          intro T hT hTlt j hj hjT
          rw [Finset.sdiff_union_of_subset hR₂R] at hT
          exact (ih T.card (hRcard ▸ hTlt) T (hT.trans hRJ) rfl).2 j hj hjT
        have hres := hgen (R \ R₂) Finset.sdiff_subset Finset.sdiff_disjoint
          (by rw [Finset.sdiff_union_of_subset hR₂R]) (by rw [Finset.sdiff_union_of_subset hR₂R])
          hstep_all
        rwa [Finset.sdiff_union_of_subset hR₂R] at hres
      -- Step 2: Prove conditional bound for i ∈ J \ R
      refine ⟨hRpos, fun i hiJ hiR => ?_⟩
      let R₂ := R.filter (fun j => Disjoint (X i) (X j))
      have hR₂R : R₂ ⊆ R := Finset.filter_subset _ _
      have hdisj_i : Disjoint (X i) (R₂.biUnion X) := by
        rw [Finset.disjoint_biUnion_right]
        intro j hj
        exact (Finset.mem_filter.mp hj).2
      have hindep : μ.prob (fun S => E i S ∧ avoid R₂ S) = μ.prob (E i) * μ.prob (avoid R₂) :=
        bern_prob_indep hS₀ hp0 hp1 hdisj_i (hdep i hiJ) (havoid_dep R₂ (hR₂R.trans hRJ))
      have hmono : μ.prob (fun S => E i S ∧ avoid R S) ≤ μ.prob (fun S => E i S ∧ avoid R₂ S) :=
        μ.prob_mono fun S _ ⟨hEi, hAv⟩ => ⟨hEi, fun j hj => hAv j (hR₂R hj)⟩
      have hle_q : μ.prob (fun S => E i S ∧ avoid R S) ≤ q * μ.prob (avoid R₂) := by
        calc μ.prob (fun S => E i S ∧ avoid R S)
            ≤ μ.prob (E i) * μ.prob (avoid R₂) := hmono.trans hindep.le
          _ ≤ q * μ.prob (avoid R₂) := mul_le_mul_of_nonneg_right (hprob i hiJ) (μ.prob_nonneg _)
      by_cases hEq : R₂ = R
      · rw [hEq] at hle_q
        have hnn : 0 ≤ q * μ.prob (avoid R) := mul_nonneg hq0 (μ.prob_nonneg _)
        linarith
      · have hR₁_card : (R \ R₂).card ≤ Δ := by
          have hsub : R \ R₂ ⊆ J.filter (fun j' => j' ≠ i ∧ ¬ Disjoint (X i) (X j')) := by
            intro j hj
            obtain ⟨hjR, hjnot⟩ := Finset.mem_sdiff.mp hj
            refine Finset.mem_filter.mpr ⟨hRJ hjR, fun hji => hiR (hji ▸ hjR), fun hdisj => ?_⟩
            exact hjnot (Finset.mem_filter.mpr ⟨hjR, hdisj⟩)
          exact (Finset.card_le_card hsub).trans (hdeg i hiJ)
        have htel := htelesc R₂ hR₂R hEq
        have hbern : (1 : ℝ) / 2 ≤ (1 - 2 * q) ^ (R \ R₂).card := by
          have h1 : 1 - ((R \ R₂).card : ℝ) * (2 * q) ≤ (1 - 2 * q) ^ (R \ R₂).card := by
            have := one_add_mul_le_pow (a := -(2 * q)) (by linarith : (-2 : ℝ) ≤ -(2 * q)) (R \ R₂).card
            simpa [sub_eq_add_neg, mul_neg] using this
          have hcardR : ((R \ R₂).card : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hR₁_card
          have h2 : ((R \ R₂).card : ℝ) * (2 * q) ≤ 2 * q * (Δ : ℝ) := by
            have := mul_le_mul_of_nonneg_right hcardR (by linarith : 0 ≤ 2 * q)
            linarith
          linarith
        have hR₂_le : μ.prob (avoid R₂) ≤ 2 * μ.prob (avoid R) := by
          have h1 : (1 / 2 : ℝ) * μ.prob (avoid R₂) ≤ μ.prob (avoid R) :=
            (mul_le_mul_of_nonneg_right hbern (μ.prob_nonneg _)).trans htel
          linarith
        calc μ.prob (fun S => E i S ∧ avoid R S)
            ≤ q * μ.prob (avoid R₂) := hle_q
          _ ≤ q * (2 * μ.prob (avoid R)) := mul_le_mul_of_nonneg_left hR₂_le hq0
          _ = 2 * q * μ.prob (avoid R) := by ring
  have hJpos : 0 < μ.prob (avoid J) := (hind J.card J Subset.rfl rfl).1
  refine ⟨hJpos, fun F XF M hFdep hM => ?_⟩
  let J₂ := J.filter (fun j => Disjoint XF (X j))
  have hJ₂J : J₂ ⊆ J := Finset.filter_subset _ _
  have hdisj_F : Disjoint XF (J₂.biUnion X) := by
    rw [Finset.disjoint_biUnion_right]
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  have hindepF : μ.prob (fun S => F S ∧ avoid J₂ S) = μ.prob F * μ.prob (avoid J₂) :=
    bern_prob_indep hS₀ hp0 hp1 hdisj_F hFdep (havoid_dep J₂ hJ₂J)
  have hmonoF : μ.prob (fun S => F S ∧ avoid J S) ≤ μ.prob F * μ.prob (avoid J₂) :=
    (μ.prob_mono fun S _ ⟨hFS, hAv⟩ => ⟨hFS, fun j hj => hAv j (hJ₂J hj)⟩).trans hindepF.le
  -- Telescope from J₂ to J = (J \ J₂) ∪ J₂
  have htelJ : ∀ D : Finset ι, D ⊆ J → Disjoint D J₂ →
      (1 - 2 * q) ^ D.card * μ.prob (avoid J₂) ≤ μ.prob (avoid (D ∪ J₂)) := by
    intro D
    induction D using Finset.induction_on with
    | empty => intro _ _; simp
    | insert d D' hdD' ihD =>
      intro hDJ hdisj
      have hdnotJ₂ : d ∉ J₂ := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self d D')
      have hdnotU : d ∉ D' ∪ J₂ := by simp [hdD', hdnotJ₂]
      have hD'prev := ihD ((Finset.subset_insert d D').trans hDJ)
        (hdisj.mono_left (Finset.subset_insert d D'))
      have hUsub : D' ∪ J₂ ⊆ J := Finset.union_subset ((Finset.subset_insert d D').trans hDJ) hJ₂J
      have hstep_d := (hind (D' ∪ J₂).card (D' ∪ J₂) hUsub rfl).2 d
        (hDJ (Finset.mem_insert_self d D')) hdnotU
      have hsplit : μ.prob (fun S => E d S ∧ avoid (D' ∪ J₂) S) +
          μ.prob (avoid (insert d D' ∪ J₂)) = μ.prob (avoid (D' ∪ J₂)) := by
        have hcongr : μ.prob (fun S => ¬ E d S ∧ avoid (D' ∪ J₂) S) =
            μ.prob (avoid (insert d D' ∪ J₂)) := by
          refine μ.prob_congr fun S _ => ?_
          simp only [avoid, Finset.insert_union, Finset.mem_insert]
          exact ⟨fun ⟨hd, hr⟩ j hj => hj.elim (fun h => h ▸ hd) (hr j),
            fun hall => ⟨hall d (Or.inl rfl), fun j hj => hall j (Or.inr hj)⟩⟩
        rw [← hcongr]
        exact μ.prob_and_add_and_not (E d) (avoid (D' ∪ J₂))
      have hge : (1 - 2 * q) * μ.prob (avoid (D' ∪ J₂)) ≤ μ.prob (avoid (insert d D' ∪ J₂)) := by
        linarith
      rw [Finset.card_insert_of_notMem hdD', pow_succ, mul_comm ((1 - 2 * q) ^ D'.card), mul_assoc]
      exact (mul_le_mul_of_nonneg_left hD'prev h12q_pos.le).trans hge
  have htel_full : (1 - 2 * q) ^ (J \ J₂).card * μ.prob (avoid J₂) ≤ μ.prob (avoid J) := by
    have h := htelJ (J \ J₂) Finset.sdiff_subset Finset.sdiff_disjoint
    rwa [Finset.sdiff_union_of_subset hJ₂J] at h
  have hM_ge : (J \ J₂).card ≤ M := by
    have hsub : J \ J₂ ⊆ J.filter (fun j => ¬ Disjoint XF (X j)) := by
      intro j hj
      obtain ⟨hjJ, hjnot⟩ := Finset.mem_sdiff.mp hj
      exact Finset.mem_filter.mpr ⟨hjJ, fun hdisj => hjnot (Finset.mem_filter.mpr ⟨hjJ, hdisj⟩)⟩
    exact (Finset.card_le_card hsub).trans hM
  have hexp_ge : 1 ≤ (1 - 2 * q) ^ (J \ J₂).card * Real.exp (6 * q * (M : ℝ)) := by
    have h1 : 1 ≤ (1 - 2 * q) * Real.exp (6 * q) := by
      have := one_sub_mul_exp_three_ge_one (x := 2 * q) (by linarith) (by linarith)
      rwa [show 3 * (2 * q) = 6 * q by ring] at this
    have hpow1 : (1 : ℝ) ≤ ((1 - 2 * q) * Real.exp (6 * q)) ^ (J \ J₂).card := by
      simpa using pow_le_pow_left₀ zero_le_one h1 (J \ J₂).card
    rw [mul_pow, ← Real.exp_nat_mul] at hpow1
    have hcard_le : ((J \ J₂).card : ℝ) * (6 * q) ≤ 6 * q * (M : ℝ) := by
      have hR : ((J \ J₂).card : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge
      have := mul_le_mul_of_nonneg_right hR (by linarith : 0 ≤ 6 * q)
      linarith
    exact hpow1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcard_le)
      (pow_nonneg h12q_pos.le _))
  have hJ₂_le : μ.prob (avoid J₂) ≤ Real.exp (6 * q * (M : ℝ)) * μ.prob (avoid J) := by
    calc μ.prob (avoid J₂)
        = 1 * μ.prob (avoid J₂) := (one_mul _).symm
      _ ≤ ((1 - 2 * q) ^ (J \ J₂).card * Real.exp (6 * q * (M : ℝ))) * μ.prob (avoid J₂) :=
          mul_le_mul_of_nonneg_right hexp_ge (μ.prob_nonneg _)
      _ = Real.exp (6 * q * (M : ℝ)) * ((1 - 2 * q) ^ (J \ J₂).card * μ.prob (avoid J₂)) := by ring
      _ ≤ Real.exp (6 * q * (M : ℝ)) * μ.prob (avoid J) :=
          mul_le_mul_of_nonneg_left htel_full (Real.exp_pos _).le
  calc μ.prob (fun S => F S ∧ avoid J S)
      ≤ μ.prob F * μ.prob (avoid J₂) := hmonoF
    _ ≤ μ.prob F * (Real.exp (6 * q * (M : ℝ)) * μ.prob (avoid J)) :=
        mul_le_mul_of_nonneg_left hJ₂_le (μ.prob_nonneg _)
    _ = μ.prob F * Real.exp (6 * q * (M : ℝ)) * μ.prob (avoid J) := by ring

end DiscreteProb

/- ## Section 5: Grebennikov--Kwan Section 4 (Nice Sets, Spread Distributions, Regularisation) -/

section NiceAndReg

open scoped Classical

/-- Definition 4.1 of Grebennikov--Kwan parameterized by `u = m^(1/12)` (so `m = u^12`, `δ = u⁻¹`). -/
def IsNice (n : ℕ) (u : ℝ) (S : Finset (ℕ × ℕ)) : Prop :=
  S ⊆ grid n ∧
  (∀ L ∈ allLines n, (u ^ 8)⁻¹ * (n : ℝ) < (L.card : ℝ) →
    (1 - u⁻¹) * u ^ 12 * ((L.card : ℝ) / (n : ℝ)) ≤ ((S ∩ L).card : ℝ) ∧
    ((S ∩ L).card : ℝ) ≤ (1 + u⁻¹) * u ^ 12 * ((L.card : ℝ) / (n : ℝ))) ∧
  (∀ L ∈ allLines n, (u ^ 24)⁻¹ * (n : ℝ) < (L.card : ℝ) → (L.card : ℝ) ≤ (u ^ 8)⁻¹ * (n : ℝ) →
    ((S ∩ L).card : ℝ) ≤ (1 + u⁻¹) * u ^ 4) ∧
  (∀ L ∈ allLines n, (L.card : ℝ) ≤ (u ^ 24)⁻¹ * (n : ℝ) → (S ∩ L).card ≤ 14) ∧
  (∀ I ⊆ range n, ∀ J ⊆ range n, (n : ℝ) / 10 ≤ (I.card : ℝ) → (n : ℝ) / 10 ≤ (J.card : ℝ) →
    (1 - u⁻¹) * (I.card : ℝ) * (J.card : ℝ) * (u ^ 12 / (n : ℝ)) ≤ ((S ∩ (I ×ˢ J)).card : ℝ) ∧
    ((S ∩ (I ×ˢ J)).card : ℝ) ≤ (1 + u⁻¹) * (I.card : ℝ) * (J.card : ℝ) * (u ^ 12 / (n : ℝ)))

def IsSpread (n : ℕ) (ρ : ℝ) (μ : Dist (grid n)) : Prop :=
  ∀ T ⊆ grid n, μ.prob (fun S => T ⊆ S) ≤ ρ ^ T.card

def SupportedOn {α : Type*} {U : Finset α} (μ : Dist U) (P : Finset α → Prop) : Prop :=
  ∀ S ⊆ U, 0 < μ.w S → P S

/-- Unified preconditions on `S₀` for one subsampling iteration (covers both Case (a) and Case (b)). -/
def IsPrevNice (n : ℕ) (u m₀ : ℝ) (S₀ : Finset (ℕ × ℕ)) : Prop :=
  S₀ ⊆ grid n ∧
  (∀ L ∈ allLines n, (u ^ 24)⁻¹ * (n : ℝ) < (L.card : ℝ) →
    (1 - u⁻¹ ^ 3) * m₀ * ((L.card : ℝ) / (n : ℝ)) ≤ ((S₀ ∩ L).card : ℝ) ∧
    ((S₀ ∩ L).card : ℝ) ≤ (1 + u⁻¹ ^ 3) * m₀ * ((L.card : ℝ) / (n : ℝ))) ∧
  (∀ L ∈ allLines n, (m₀ ^ 2)⁻¹ * (n : ℝ) < (L.card : ℝ) → (L.card : ℝ) ≤ (u ^ 24)⁻¹ * (n : ℝ) →
    ((S₀ ∩ L).card : ℝ) ≤ (1 + u⁻¹ ^ 3) * m₀ * (u ^ 24)⁻¹) ∧
  (∀ L ∈ allLines n, (L.card : ℝ) ≤ (m₀ ^ 2)⁻¹ * (n : ℝ) → (S₀ ∩ L).card ≤ 14) ∧
  (∀ I ⊆ range n, ∀ J ⊆ range n, (n : ℝ) / 10 ≤ (I.card : ℝ) → (n : ℝ) / 10 ≤ (J.card : ℝ) →
    (1 - u⁻¹ ^ 3) * (I.card : ℝ) * (J.card : ℝ) * (m₀ / (n : ℝ)) ≤ ((S₀ ∩ (I ×ˢ J)).card : ℝ) ∧
    ((S₀ ∩ (I ×ˢ J)).card : ℝ) ≤ (1 + u⁻¹ ^ 3) * (I.card : ℝ) * (J.card : ℝ) * (m₀ / (n : ℝ)))

lemma exp_le_one_add_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp x ≤ 1 + 2 * x := by
  have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have hpos : 0 < 1 - x := by linarith
  have h2 : Real.exp x ≤ (1 - x)⁻¹ := by
    have : (Real.exp (-x))⁻¹ ≤ (1 - x)⁻¹ := inv_anti₀ hpos h1
    simpa [Real.exp_neg] using this
  have h3 : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith [sq_nonneg x]
  exact h2.trans h3

lemma inv_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ 1 + 2 * x := by
  rw [inv_le_iff_one_le_mul₀ (by linarith : 0 < 1 - x)]
  nlinarith [sq_nonneg x]

lemma isPrevNice_of_isNice_cube {n : ℕ} {u : ℝ} (hu : 1000 ≤ u) {S₀ : Finset (ℕ × ℕ)}
    (h : IsNice n (u ^ 3) S₀) :
    IsPrevNice n u (u ^ 36) S₀ := by
  have hu0 : 0 < u := by linarith
  have hinv : (u ^ 3)⁻¹ = u⁻¹ ^ 3 := by rw [inv_pow]
  have h8 : ((u ^ 3) ^ 8)⁻¹ = (u ^ 24)⁻¹ := by congr 1; ring
  have h24 : ((u ^ 3) ^ 24)⁻¹ = ((u ^ 36) ^ 2)⁻¹ := by congr 1; ring
  have h12 : (u ^ 3) ^ 12 = u ^ 36 := by ring
  have h4 : (u ^ 3) ^ 4 = u ^ 36 * (u ^ 24)⁻¹ := by
    field_simp [hu0.ne']
  refine ⟨h.1, ?_, ?_, ?_, ?_⟩
  · intro L hL hbig
    have := h.2.1 L hL (by rwa [h8])
    rwa [hinv, h12] at this
  · intro L hL hlo hhi
    have := h.2.2.1 L hL (by rwa [h24]) (by rwa [h8])
    rwa [hinv, h4, ← mul_assoc] at this
  · intro L hL hle
    exact h.2.2.2.1 L hL (by rwa [h24])
  · intro I hI J hJ hIc hJc
    have := h.2.2.2.2 I hI J hJ hIc hJc
    rwa [hinv, h12] at this

lemma isPrevNice_grid {n : ℕ} {u : ℝ} (hu : 1000 ≤ u) (hn : u ^ 12 ≤ (n : ℝ)) :
    IsPrevNice n u (n : ℝ) (grid n) := by
  have hu0 : 0 < u := by linarith
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn
  have huinv : 0 ≤ u⁻¹ ^ 3 := by positivity
  refine ⟨Subset.rfl, ?_, ?_, ?_, ?_⟩
  · intro L hL _
    rw [Finset.inter_eq_right.mpr (line_subset_grid hL)]
    have hLnn : (0 : ℝ) ≤ (L.card : ℝ) := Nat.cast_nonneg L.card
    have h1 : (1 - u⁻¹ ^ 3) * (n : ℝ) * ((L.card : ℝ) / (n : ℝ)) = (1 - u⁻¹ ^ 3) * (L.card : ℝ) := by
      field_simp [hn0.ne']
    have h2 : (1 + u⁻¹ ^ 3) * (n : ℝ) * ((L.card : ℝ) / (n : ℝ)) = (1 + u⁻¹ ^ 3) * (L.card : ℝ) := by
      field_simp [hn0.ne']
    rw [h1, h2]
    exact ⟨by nlinarith, by nlinarith⟩
  · intro L hL _ hhi
    rw [Finset.inter_eq_right.mpr (line_subset_grid hL)]
    have hnn : 0 ≤ (n : ℝ) * (u ^ 24)⁻¹ := by positivity
    nlinarith
  · intro L hL hle
    have h2 : (2 : ℝ) ≤ (L.card : ℝ) := by exact_mod_cast (line_card_bounds hL).1
    have h1 : ((n : ℝ) ^ 2)⁻¹ * (n : ℝ) = (n : ℝ)⁻¹ := by field_simp [hn0.ne']
    rw [h1] at hle
    have h1le : (1 : ℝ) ≤ (n : ℝ) := by
      have : (1 : ℝ) ≤ u ^ 12 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ u)
      linarith
    have hinv1 : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1le
    linarith
  · intro I hI J hJ _ _
    have hsub : I ×ˢ J ⊆ grid n := Finset.product_subset_product hI hJ
    rw [Finset.inter_eq_right.mpr hsub, Finset.card_product, Nat.cast_mul, div_self hn0.ne', mul_one]
    have hIJ : 0 ≤ (I.card : ℝ) * (J.card : ℝ) := by positivity
    exact ⟨by nlinarith, by nlinarith⟩

private def badLineEvent (n : ℕ) (u : ℝ) (L S : Finset (ℕ × ℕ)) : Prop :=
  if (u ^ 8)⁻¹ * (n : ℝ) < (L.card : ℝ) then
    ¬ ((1 - u⁻¹) * u ^ 12 * ((L.card : ℝ) / (n : ℝ)) ≤ ((S ∩ L).card : ℝ) ∧
       ((S ∩ L).card : ℝ) ≤ (1 + u⁻¹) * u ^ 12 * ((L.card : ℝ) / (n : ℝ)))
  else if (u ^ 24)⁻¹ * (n : ℝ) < (L.card : ℝ) then
    ¬ (((S ∩ L).card : ℝ) ≤ (1 + u⁻¹) * u ^ 4)
  else
    ¬ ((S ∩ L).card ≤ 14)

private lemma bad_line_prob_le_light {n : ℕ} {u m₀ : ℝ}
    (hu : 1000 ≤ u) (hm₀_lo : u ^ 12 ≤ m₀)
    {S₀ : Finset (ℕ × ℕ)} (hS₀ : IsPrevNice n u m₀ S₀)
    {hp0 : 0 ≤ u ^ 12 / m₀} {hp1 : u ^ 12 / m₀ ≤ 1}
    {L : Finset (ℕ × ℕ)} (hLall : L ∈ allLines n)
    (hLw : (m₀ ^ 2)⁻¹ * (n : ℝ) < (L.card : ℝ))
    (hmed : (L.card : ℝ) ≤ (u ^ 24)⁻¹ * (n : ℝ)) :
    (bernDist hS₀.1 hp0 hp1).prob (fun S => ¬ ((S ∩ L).card ≤ 14)) ≤ (1 / (5 * u ^ 12)) ^ 15 := by
  have hu0 : 0 < u := by linarith
  have hm₀_pos : 0 < m₀ := lt_of_lt_of_le (pow_pos hu0 12) hm₀_lo
  let p : ℝ := u ^ 12 / m₀
  let δ : ℝ := u⁻¹
  have hδ_pos : 0 < δ := inv_pos.mpr hu0
  have hδ_le : δ ≤ 1 / 1000 := by dsimp [δ]; rw [inv_le_comm₀ hu0 (by norm_num)]; linarith
  have hAsub : S₀ ∩ L ⊆ S₀ := Finset.inter_subset_left
  have hSinter : ∀ S ⊆ S₀, S ∩ L = S ∩ (S₀ ∩ L) := by
    intro S hSS₀; ext x; simp only [Finset.mem_inter]
    exact ⟨fun ⟨hxS, hxL⟩ => ⟨hxS, hSS₀ hxS, hxL⟩, fun ⟨hxS, _, hxL⟩ => ⟨hxS, hxL⟩⟩
  have hS₀_hi := hS₀.2.2.1 L hLall hLw hmed
  have hsub_ev : (bernDist hS₀.1 hp0 hp1).prob (fun S => ¬ ((S ∩ L).card ≤ 14)) ≤
      (bernDist hS₀.1 hp0 hp1).prob (fun S => 15 ≤ (S ∩ (S₀ ∩ L)).card) := by
    unfold Dist.prob bernDist; dsimp only
    refine Finset.sum_le_sum fun S _ => ?_
    by_cases hSS₀ : S ⊆ S₀
    · by_cases hbad : ¬ ((S ∩ L).card ≤ 14)
      · have h15 : 15 ≤ (S ∩ (S₀ ∩ L)).card := by rw [← hSinter S hSS₀]; omega
        simp only [if_pos hbad, if_pos h15, le_rfl]
      · simp only [if_neg hbad]; split_ifs <;> [exact bernW_nonneg hp0 hp1 S; exact le_rfl]
    · simp [bernW, hSS₀]
  have hbind := bern_card_ge_le hS₀.1 hAsub hp0 hp1 15
  have hch := choose_le_exp_pow (S₀ ∩ L).card 15 (by omega)
  have hbase : Real.exp 1 * ((S₀ ∩ L).card : ℝ) / 15 * p ≤ 1 / (5 * u ^ 12) := by
    have h1 : ((S₀ ∩ L).card : ℝ) * p ≤ (1 + δ ^ 3) * (u ^ 12)⁻¹ := by
      have := mul_le_mul_of_nonneg_right hS₀_hi hp0
      have halg : (1 + u⁻¹ ^ 3) * m₀ * (u ^ 24)⁻¹ * p = (1 + δ ^ 3) * (u ^ 12)⁻¹ := by
        dsimp [p, δ]; field_simp [hm₀_pos.ne', hu0.ne']
      linarith
    have h2 : Real.exp 1 * (1 + δ ^ 3) / 15 ≤ 1 / 5 := by
      have he2 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
      have hδ3 : δ ^ 3 ≤ 1 / 1000 := by
        have : δ ^ 3 ≤ (1 / 1000 : ℝ) ^ 3 := pow_le_pow_left₀ hδ_pos.le hδ_le 3
        linarith
      nlinarith only [he2, hδ3, Real.exp_pos 1]
    calc Real.exp 1 * ((S₀ ∩ L).card : ℝ) / 15 * p
        = (Real.exp 1 / 15) * (((S₀ ∩ L).card : ℝ) * p) := by ring
      _ ≤ (Real.exp 1 / 15) * ((1 + δ ^ 3) * (u ^ 12)⁻¹) :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg (Real.exp_pos 1).le (by norm_num))
      _ = (Real.exp 1 * (1 + δ ^ 3) / 15) * (u ^ 12)⁻¹ := by ring
      _ ≤ (1 / 5 : ℝ) * (u ^ 12)⁻¹ := mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr (pow_nonneg hu0.le 12))
      _ = 1 / (5 * u ^ 12) := by ring
  have hnn : 0 ≤ Real.exp 1 * ((S₀ ∩ L).card : ℝ) / 15 * p :=
    mul_nonneg (div_nonneg (mul_nonneg (Real.exp_pos 1).le (Nat.cast_nonneg _)) (by norm_num)) hp0
  calc (bernDist hS₀.1 hp0 hp1).prob _ ≤ (((S₀ ∩ L).card.choose 15 : ℕ) : ℝ) * p ^ 15 := hsub_ev.trans hbind
    _ ≤ (Real.exp 1 * ((S₀ ∩ L).card : ℝ) / 15) ^ 15 * p ^ 15 :=
        mul_le_mul_of_nonneg_right hch (pow_nonneg hp0 15)
    _ = (Real.exp 1 * ((S₀ ∩ L).card : ℝ) / 15 * p) ^ 15 := (mul_pow _ _ 15).symm
    _ ≤ (1 / (5 * u ^ 12)) ^ 15 := pow_le_pow_left₀ hnn hbase 15

private lemma bad_line_prob_le {n : ℕ} {u m₀ : ℝ}
    (hu : 1000 ≤ u) (hm₀_lo : u ^ 12 ≤ m₀) (hm₀_n : m₀ ≤ (n : ℝ))
    {S₀ : Finset (ℕ × ℕ)} (hS₀ : IsPrevNice n u m₀ S₀)
    {hp0 : 0 ≤ u ^ 12 / m₀} {hp1 : u ^ 12 / m₀ ≤ 1}
    {L : Finset (ℕ × ℕ)} (hLall : L ∈ allLines n) (hLw : (m₀ ^ 2)⁻¹ * (n : ℝ) < (L.card : ℝ)) :
    (bernDist hS₀.1 hp0 hp1).prob (badLineEvent n u L) ≤ (1 / (5 * u ^ 12)) ^ 15 := by
  have hu0 : 0 < u := by linarith
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have hm_pos : 0 < u ^ 12 := by positivity
  have hm₀_pos : 0 < m₀ := lt_of_lt_of_le hm_pos hm₀_lo
  have hn_pos : (0 : ℝ) < n := lt_of_lt_of_le hm₀_pos hm₀_n
  let p : ℝ := u ^ 12 / m₀
  let δ : ℝ := u⁻¹
  have hδ_pos : 0 < δ := inv_pos.mpr hu0
  have hδ_le : δ ≤ 1 / 1000 := by dsimp [δ]; rw [inv_le_comm₀ hu0 (by norm_num)]; linarith
  have hδ3_le : δ ^ 3 ≤ 1 / 1000000000 := by
    calc δ ^ 3 ≤ (1 / 1000 : ℝ) ^ 3 := pow_le_pow_left₀ hδ_pos.le hδ_le 3
      _ = 1 / 1000000000 := by norm_num
  have hδ3_lt : δ ^ 3 ≤ δ / 4 := by
    have hsq : δ ^ 2 ≤ 1 / 4 := by nlinarith
    nlinarith [show δ ^ 3 = δ * δ ^ 2 by ring]
  let μ := bernDist hS₀.1 hp0 hp1
  have hexp_le_q : 2 * Real.exp (-(u ^ 2 / 13)) ≤ (1 / (5 * u ^ 12)) ^ 15 := by
    have hge := exp_sq_div_13_ge hu
    rw [Real.exp_neg, one_div, inv_pow, mul_inv_le_iff₀ (Real.exp_pos _),
      inv_mul_eq_div, le_div_iff₀ (by positivity : 0 < (5 * u ^ 12) ^ 15)]
    linarith
  have hAsub : S₀ ∩ L ⊆ S₀ := Finset.inter_subset_left
  have hSinter : ∀ S ⊆ S₀, S ∩ L = S ∩ (S₀ ∩ L) := by
    intro S hSS₀; ext x; simp only [Finset.mem_inter]
    exact ⟨fun ⟨hxS, hxL⟩ => ⟨hxS, hSS₀ hxS, hxL⟩, fun ⟨hxS, _, hxL⟩ => ⟨hxS, hxL⟩⟩
  change μ.prob (badLineEvent n u L) ≤ (1 / (5 * u ^ 12)) ^ 15
  unfold badLineEvent
  split_ifs with hheavy hmed
  · -- Heavy line: w(L) > u⁻⁸
    have hmed_cond : (u ^ 24)⁻¹ * (n : ℝ) < (L.card : ℝ) := by
      have h1 : (u ^ 24)⁻¹ ≤ (u ^ 8)⁻¹ := inv_anti₀ (by positivity)
        (by calc u ^ 8 = u ^ 8 * 1 := (mul_one _).symm
          _ ≤ u ^ 8 * u ^ 16 := mul_le_mul_of_nonneg_left (one_le_pow₀ hu1) (by positivity)
          _ = u ^ 24 := by ring)
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right h1 hn_pos.le) hheavy
    obtain ⟨hS₀_lo, hS₀_hi⟩ := hS₀.2.1 L hLall hmed_cond
    have hA_eq : (1 - δ ^ 3) * u ^ 12 * ((L.card : ℝ) / (n : ℝ)) ≤ p * ((S₀ ∩ L).card : ℝ) := by
      have := mul_le_mul_of_nonneg_left hS₀_lo hp0
      have heq : p * ((1 - u⁻¹ ^ 3) * m₀ * ((L.card : ℝ) / (n : ℝ))) =
          (1 - δ ^ 3) * u ^ 12 * ((L.card : ℝ) / (n : ℝ)) := by
        dsimp [p, δ]; field_simp [hm₀_pos.ne']
      linarith
    have hA_upper_imp : ∀ S ⊆ S₀,
        (1 + δ) * u ^ 12 * ((L.card : ℝ) / (n : ℝ)) < ((S ∩ L).card : ℝ) →
        (1 + δ / 2) * (p * ((S₀ ∩ L).card : ℝ)) < ((S ∩ (S₀ ∩ L)).card : ℝ) := by
      intro S hSS₀ hgt
      rw [← hSinter S hSS₀]
      have h1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS₀_hi hp0)
        (by positivity : 0 ≤ 1 + δ / 2)
      have h2 : (1 + δ / 2) * (p * ((1 + u⁻¹ ^ 3) * m₀ * ((L.card : ℝ) / (n : ℝ)))) =
          (1 + δ / 2) * (1 + δ ^ 3) * (u ^ 12 * ((L.card : ℝ) / (n : ℝ))) := by
        dsimp [p, δ]; field_simp [hm₀_pos.ne']
      have h3 : (1 + δ / 2) * (1 + δ ^ 3) ≤ 1 + δ := by nlinarith
      have hnn : 0 ≤ u ^ 12 * ((L.card : ℝ) / (n : ℝ)) := by positivity
      have hprod : (1 + δ / 2) * (p * ((S₀ ∩ L).card : ℝ)) ≤
          (1 + δ) * u ^ 12 * ((L.card : ℝ) / (n : ℝ)) := by
        calc (1 + δ / 2) * (p * ((S₀ ∩ L).card : ℝ))
            ≤ (1 + δ / 2) * (1 + δ ^ 3) * (u ^ 12 * ((L.card : ℝ) / (n : ℝ))) := h2 ▸ h1
          _ ≤ (1 + δ) * (u ^ 12 * ((L.card : ℝ) / (n : ℝ))) := mul_le_mul_of_nonneg_right h3 hnn
          _ = (1 + δ) * u ^ 12 * ((L.card : ℝ) / (n : ℝ)) := by ring
      linarith
    have hA_lower_imp : ∀ S ⊆ S₀,
        ((S ∩ L).card : ℝ) < (1 - δ) * u ^ 12 * ((L.card : ℝ) / (n : ℝ)) →
        ((S ∩ (S₀ ∩ L)).card : ℝ) < (1 - δ / 2) * (p * ((S₀ ∩ L).card : ℝ)) := by
      intro S hSS₀ hlt
      rw [← hSinter S hSS₀]
      have h1 := mul_le_mul_of_nonneg_left hA_eq (by linarith : 0 ≤ 1 - δ / 2)
      have h3 : 1 - δ ≤ (1 - δ / 2) * (1 - δ ^ 3) := by nlinarith
      have hnn : 0 ≤ u ^ 12 * ((L.card : ℝ) / (n : ℝ)) := by positivity
      have hprod : (1 - δ) * u ^ 12 * ((L.card : ℝ) / (n : ℝ)) ≤
          (1 - δ / 2) * (p * ((S₀ ∩ L).card : ℝ)) := by
        calc (1 - δ) * u ^ 12 * ((L.card : ℝ) / (n : ℝ))
            = (1 - δ) * (u ^ 12 * ((L.card : ℝ) / (n : ℝ))) := by ring
          _ ≤ (1 - δ / 2) * (1 - δ ^ 3) * (u ^ 12 * ((L.card : ℝ) / (n : ℝ))) :=
              mul_le_mul_of_nonneg_right h3 hnn
          _ = (1 - δ / 2) * ((1 - δ ^ 3) * u ^ 12 * ((L.card : ℝ) / (n : ℝ))) := by ring
          _ ≤ (1 - δ / 2) * (p * ((S₀ ∩ L).card : ℝ)) := h1
      linarith
    have hexp_bound : u ^ 2 / 13 ≤ (δ / 2) ^ 2 * (p * ((S₀ ∩ L).card : ℝ)) / 3 := by
      have hw : (u ^ 8)⁻¹ < (L.card : ℝ) / (n : ℝ) := (lt_div_iff₀ hn_pos).mpr hheavy
      have hpm : (1 - δ ^ 3) * u ^ 4 ≤ p * ((S₀ ∩ L).card : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hw.le (by nlinarith : 0 ≤ (1 - δ ^ 3) * u ^ 12)
        have halg : (1 - δ ^ 3) * u ^ 12 * (u ^ 8)⁻¹ = (1 - δ ^ 3) * u ^ 4 := by
          field_simp [hu0.ne']
        linarith
      have h1 : (δ / 2) ^ 2 * ((1 - δ ^ 3) * u ^ 4) / 3 = (1 - δ ^ 3) / 12 * u ^ 2 := by
        dsimp [δ]; field_simp [hu0.ne']; ring
      have h2 := mul_le_mul_of_nonneg_left hpm (by positivity : 0 ≤ (δ / 2) ^ 2)
      have h3 : u ^ 2 / 13 ≤ (1 - δ ^ 3) / 12 * u ^ 2 := by nlinarith [sq_nonneg u]
      linarith
    have hhi_prob := bern_chernoff_upper_le hS₀.1 hAsub hp0 hp1 (by positivity : 0 < δ / 2)
      (by linarith) (le_refl ((S₀ ∩ L).card : ℝ))
    have hlo_prob := bern_chernoff_lower hS₀.1 hAsub hp0 hp1 (by positivity : 0 < δ / 2)
      (by linarith)
    have hsub_ev : μ.prob (fun S => ¬ ((1 - δ) * u ^ 12 * ((L.card : ℝ) / (n : ℝ)) ≤ ((S ∩ L).card : ℝ) ∧
          ((S ∩ L).card : ℝ) ≤ (1 + δ) * u ^ 12 * ((L.card : ℝ) / (n : ℝ)))) ≤
        μ.prob (fun S => ((S ∩ (S₀ ∩ L)).card : ℝ) < (1 - δ / 2) * (p * ((S₀ ∩ L).card : ℝ)) ∨
          (1 + δ / 2) * (p * ((S₀ ∩ L).card : ℝ)) < ((S ∩ (S₀ ∩ L)).card : ℝ)) := by
      unfold Dist.prob μ bernDist; dsimp only
      refine Finset.sum_le_sum fun S _ => ?_
      by_cases hSS₀ : S ⊆ S₀
      · by_cases hbad : ¬ ((1 - δ) * u ^ 12 * ((L.card : ℝ) / (n : ℝ)) ≤ ((S ∩ L).card : ℝ) ∧
            ((S ∩ L).card : ℝ) ≤ (1 + δ) * u ^ 12 * ((L.card : ℝ) / (n : ℝ)))
        · have hor : ((S ∩ (S₀ ∩ L)).card : ℝ) < (1 - δ / 2) * (p * ((S₀ ∩ L).card : ℝ)) ∨
              (1 + δ / 2) * (p * ((S₀ ∩ L).card : ℝ)) < ((S ∩ (S₀ ∩ L)).card : ℝ) := by
            rw [not_and_or, not_le, not_le] at hbad
            exact hbad.elim (fun h1 => Or.inl (hA_lower_imp S hSS₀ h1))
              (fun h2 => Or.inr (hA_upper_imp S hSS₀ h2))
          simp only [if_pos hbad, if_pos hor, le_rfl]
        · simp only [if_neg hbad]; split_ifs <;> [exact bernW_nonneg hp0 hp1 S; exact le_rfl]
      · simp [bernW, hSS₀]
    have hexp_mono : Real.exp (-((δ / 2) ^ 2 * (p * ((S₀ ∩ L).card : ℝ)) / 3)) ≤
        Real.exp (-(u ^ 2 / 13)) := Real.exp_le_exp.mpr (by linarith)
    calc μ.prob _ ≤ μ.prob (fun S => ((S ∩ (S₀ ∩ L)).card : ℝ) < (1 - δ / 2) * (p * ((S₀ ∩ L).card : ℝ))) +
          μ.prob (fun S => (1 + δ / 2) * (p * ((S₀ ∩ L).card : ℝ)) < ((S ∩ (S₀ ∩ L)).card : ℝ)) :=
          hsub_ev.trans (μ.prob_or_le _ _)
      _ ≤ 2 * Real.exp (-(u ^ 2 / 13)) := by linarith
      _ ≤ (1 / (5 * u ^ 12)) ^ 15 := hexp_le_q
  · -- Medium line: u⁻²⁴ < w(L) ≤ u⁻⁸
    push Not at hheavy
    have hS₀_hi := (hS₀.2.1 L hLall hmed).2
    let M : ℝ := (1 + δ ^ 3) * m₀ * (u ^ 8)⁻¹
    have hAM : ((S₀ ∩ L).card : ℝ) ≤ M := by
      have hw : (L.card : ℝ) / (n : ℝ) ≤ (u ^ 8)⁻¹ := (div_le_iff₀ hn_pos).mpr hheavy
      have := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ (1 + u⁻¹ ^ 3) * m₀)
      exact hS₀_hi.trans (by simpa [M, δ] using this)
    have hpM : p * M = (1 + δ ^ 3) * u ^ 4 := by
      dsimp [p, M, δ]; field_simp [hm₀_pos.ne', hu0.ne']
    have hprod_le : (1 + δ / 2) * (p * M) ≤ (1 + δ) * u ^ 4 := by
      rw [hpM]
      have h1 : (1 + δ / 2) * (1 + δ ^ 3) ≤ 1 + δ := by nlinarith
      have := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ u ^ 4)
      linarith
    have hsub_ev : μ.prob (fun S => ¬ (((S ∩ L).card : ℝ) ≤ (1 + δ) * u ^ 4)) ≤
        μ.prob (fun S => (1 + δ / 2) * (p * M) < ((S ∩ (S₀ ∩ L)).card : ℝ)) := by
      unfold Dist.prob μ bernDist; dsimp only
      refine Finset.sum_le_sum fun S _ => ?_
      by_cases hSS₀ : S ⊆ S₀
      · by_cases hbad : ¬ (((S ∩ L).card : ℝ) ≤ (1 + δ) * u ^ 4)
        · have hgt : (1 + δ / 2) * (p * M) < ((S ∩ (S₀ ∩ L)).card : ℝ) := by
            rw [← hSinter S hSS₀]; linarith
          simp only [if_pos hbad, if_pos hgt, le_rfl]
        · simp only [if_neg hbad]; split_ifs <;> [exact bernW_nonneg hp0 hp1 S; exact le_rfl]
      · simp [bernW, hSS₀]
    have hcher := bern_chernoff_upper_le hS₀.1 hAsub hp0 hp1 (by positivity : 0 < δ / 2)
      (by linarith) hAM
    have hexp_ge : u ^ 2 / 13 ≤ (δ / 2) ^ 2 * (p * M) / 3 := by
      rw [hpM]
      have halg : (δ / 2) ^ 2 * ((1 + δ ^ 3) * u ^ 4) / 3 = (1 + δ ^ 3) / 12 * u ^ 2 := by
        dsimp [δ]; field_simp [hu0.ne']; ring
      rw [halg]
      have hcoef : (1 / 13 : ℝ) ≤ (1 + δ ^ 3) / 12 := by linarith [pow_nonneg hδ_pos.le 3]
      have := mul_le_mul_of_nonneg_right hcoef (sq_nonneg u)
      linarith
    calc μ.prob _ ≤ Real.exp (-((δ / 2) ^ 2 * (p * M) / 3)) := hsub_ev.trans hcher
      _ ≤ Real.exp (-(u ^ 2 / 13)) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 2 * Real.exp (-(u ^ 2 / 13)) := by linarith [Real.exp_pos (-(u ^ 2 / 13))]
      _ ≤ (1 / (5 * u ^ 12)) ^ 15 := hexp_le_q
  · -- Light line: m₀⁻² < w(L) ≤ u⁻²⁴
    push Not at hmed
    exact bad_line_prob_le_light hu hm₀_lo hS₀ hLall hLw hmed

private lemma quasirandom_pair_prob_le {n : ℕ} {u m₀ : ℝ}
    (hu : 1000 ≤ u) (hm₀_lo : u ^ 12 ≤ m₀) (hm₀_n : m₀ ≤ (n : ℝ))
    {S₀ : Finset (ℕ × ℕ)} (hS₀ : IsPrevNice n u m₀ S₀)
    {hp0 : 0 ≤ u ^ 12 / m₀} {hp1 : u ^ 12 / m₀ ≤ 1}
    {I J' : Finset ℕ} (hI : I ⊆ range n) (hJ' : J' ⊆ range n)
    (hIc : (n : ℝ) / 10 ≤ (I.card : ℝ)) (hJc : (n : ℝ) / 10 ≤ (J'.card : ℝ)) :
    (bernDist hS₀.1 hp0 hp1).prob (fun S =>
      ¬ ((1 - u⁻¹) * (I.card : ℝ) * (J'.card : ℝ) * (u ^ 12 / (n : ℝ)) ≤
            ((S ∩ (I ×ˢ J')).card : ℝ) ∧
         ((S ∩ (I ×ˢ J')).card : ℝ) ≤
            (1 + u⁻¹) * (I.card : ℝ) * (J'.card : ℝ) * (u ^ 12 / (n : ℝ)))) ≤
      2 * Real.exp (-(u ^ 10 * (n : ℝ) / 1300)) := by
  have hu0 : 0 < u := by linarith
  have hm_pos : 0 < u ^ 12 := by positivity
  have hm₀_pos : 0 < m₀ := lt_of_lt_of_le hm_pos hm₀_lo
  have hn_pos : (0 : ℝ) < n := lt_of_lt_of_le hm₀_pos hm₀_n
  let p : ℝ := u ^ 12 / m₀
  let δ : ℝ := u⁻¹
  have hδ_pos : 0 < δ := inv_pos.mpr hu0
  have hδ_le : δ ≤ 1 / 1000 := by dsimp [δ]; rw [inv_le_comm₀ hu0 (by norm_num)]; linarith
  have hδ3_le : δ ^ 3 ≤ 1 / 1000000000 := by
    calc δ ^ 3 ≤ (1 / 1000 : ℝ) ^ 3 := pow_le_pow_left₀ hδ_pos.le hδ_le 3
      _ = 1 / 1000000000 := by norm_num
  have hδ3_lt : δ ^ 3 ≤ δ / 4 := by
    have hsq : δ ^ 2 ≤ 1 / 4 := by nlinarith
    nlinarith [show δ ^ 3 = δ * δ ^ 2 by ring]
  let μ := bernDist hS₀.1 hp0 hp1
  let A := S₀ ∩ (I ×ˢ J')
  have hAsub : A ⊆ S₀ := Finset.inter_subset_left
  have hSinter : ∀ S ⊆ S₀, S ∩ (I ×ˢ J') = S ∩ A := by
    intro S hSS₀; ext x; simp only [A, Finset.mem_inter]
    exact ⟨fun ⟨hxS, hxP⟩ => ⟨hxS, hSS₀ hxS, hxP⟩, fun ⟨hxS, _, hxP⟩ => ⟨hxS, hxP⟩⟩
  obtain ⟨hA_lo, hA_hi⟩ := hS₀.2.2.2.2 I hI J' hJ' hIc hJc
  have hpA_lo : (1 - δ ^ 3) * (I.card : ℝ) * (J'.card : ℝ) * (u ^ 12 / (n : ℝ)) ≤
      p * (A.card : ℝ) := by
    have := mul_le_mul_of_nonneg_left hA_lo hp0
    have halg : p * ((1 - u⁻¹ ^ 3) * (I.card : ℝ) * (J'.card : ℝ) * (m₀ / (n : ℝ))) =
        (1 - δ ^ 3) * (I.card : ℝ) * (J'.card : ℝ) * (u ^ 12 / (n : ℝ)) := by
      dsimp [p, δ]; field_simp [hm₀_pos.ne', hn_pos.ne']
    linarith
  have hpA_hi : p * (A.card : ℝ) ≤
      (1 + δ ^ 3) * (I.card : ℝ) * (J'.card : ℝ) * (u ^ 12 / (n : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hA_hi hp0
    have halg : p * ((1 + u⁻¹ ^ 3) * (I.card : ℝ) * (J'.card : ℝ) * (m₀ / (n : ℝ))) =
        (1 + δ ^ 3) * (I.card : ℝ) * (J'.card : ℝ) * (u ^ 12 / (n : ℝ)) := by
      dsimp [p, δ]; field_simp [hm₀_pos.ne', hn_pos.ne']
    linarith
  have hbase_nn : 0 ≤ (I.card : ℝ) * (J'.card : ℝ) * (u ^ 12 / (n : ℝ)) := by positivity
  have hsub_ev : μ.prob (fun S =>
      ¬ ((1 - δ) * (I.card : ℝ) * (J'.card : ℝ) * (u ^ 12 / (n : ℝ)) ≤ ((S ∩ (I ×ˢ J')).card : ℝ) ∧
         ((S ∩ (I ×ˢ J')).card : ℝ) ≤ (1 + δ) * (I.card : ℝ) * (J'.card : ℝ) * (u ^ 12 / (n : ℝ)))) ≤
      μ.prob (fun S => ((S ∩ A).card : ℝ) < (1 - δ / 2) * (p * (A.card : ℝ)) ∨
        (1 + δ / 2) * (p * (A.card : ℝ)) < ((S ∩ A).card : ℝ)) := by
    unfold Dist.prob μ bernDist; dsimp only
    refine Finset.sum_le_sum fun S _ => ?_
    by_cases hSS₀ : S ⊆ S₀
    · by_cases hbad : ¬ ((1 - δ) * (I.card : ℝ) * (J'.card : ℝ) * (u ^ 12 / (n : ℝ)) ≤
            ((S ∩ (I ×ˢ J')).card : ℝ) ∧
          ((S ∩ (I ×ˢ J')).card : ℝ) ≤
            (1 + δ) * (I.card : ℝ) * (J'.card : ℝ) * (u ^ 12 / (n : ℝ)))
      · have hor : ((S ∩ A).card : ℝ) < (1 - δ / 2) * (p * (A.card : ℝ)) ∨
            (1 + δ / 2) * (p * (A.card : ℝ)) < ((S ∩ A).card : ℝ) := by
          rw [not_and_or, not_le, not_le, hSinter S hSS₀] at hbad
          rcases hbad with h1 | h2
          · left
            have hprod : 1 - δ ≤ (1 - δ / 2) * (1 - δ ^ 3) := by nlinarith
            have hc1 : (1 - δ) * ((I.card : ℝ) * (J'.card : ℝ) * (u ^ 12 / (n : ℝ))) ≤
                (1 - δ / 2) * (1 - δ ^ 3) * ((I.card : ℝ) * (J'.card : ℝ) * (u ^ 12 / (n : ℝ))) :=
              mul_le_mul_of_nonneg_right hprod hbase_nn
            have hc2 := mul_le_mul_of_nonneg_left hpA_lo (by linarith : 0 ≤ 1 - δ / 2)
            linarith
          · right
            have hprod : (1 + δ / 2) * (1 + δ ^ 3) ≤ 1 + δ := by nlinarith
            have hc1 : (1 + δ / 2) * (1 + δ ^ 3) * ((I.card : ℝ) * (J'.card : ℝ) * (u ^ 12 / (n : ℝ))) ≤
                (1 + δ) * ((I.card : ℝ) * (J'.card : ℝ) * (u ^ 12 / (n : ℝ))) :=
              mul_le_mul_of_nonneg_right hprod hbase_nn
            have hc2 := mul_le_mul_of_nonneg_left hpA_hi (by positivity : 0 ≤ 1 + δ / 2)
            linarith
        simp only [if_pos hbad, if_pos hor, le_rfl]
      · simp only [if_neg hbad]; split_ifs <;> [exact bernW_nonneg hp0 hp1 S; exact le_rfl]
    · simp [bernW, hSS₀]
  have hhi_p := bern_chernoff_upper_le hS₀.1 hAsub hp0 hp1 (by positivity : 0 < δ / 2)
    (by linarith) (le_refl (A.card : ℝ))
  have hlo_p := bern_chernoff_lower hS₀.1 hAsub hp0 hp1 (by positivity : 0 < δ / 2)
    (by linarith)
  have hexp_ge : u ^ 10 * (n : ℝ) / 1300 ≤ (δ / 2) ^ 2 * (p * (A.card : ℝ)) / 3 := by
    have hIJ_ge : (n : ℝ) / 10 * ((n : ℝ) / 10) ≤ (I.card : ℝ) * (J'.card : ℝ) :=
      mul_le_mul hIc hJc (by positivity) (Nat.cast_nonneg _)
    have hpA_ge : (1 - δ ^ 3) * (u ^ 12 * (n : ℝ) / 100) ≤ p * (A.card : ℝ) := by
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hIJ_ge (by linarith : 0 ≤ 1 - δ ^ 3))
        (by positivity : 0 ≤ u ^ 12 / (n : ℝ))
      have halg : (1 - δ ^ 3) * ((n : ℝ) / 10 * ((n : ℝ) / 10)) * (u ^ 12 / (n : ℝ)) =
          (1 - δ ^ 3) * (u ^ 12 * (n : ℝ) / 100) := by
        field_simp [hn_pos.ne']; ring
      linarith
    have h1 := mul_le_mul_of_nonneg_left hpA_ge (by positivity : 0 ≤ (δ / 2) ^ 2)
    have halg : (δ / 2) ^ 2 * ((1 - δ ^ 3) * (u ^ 12 * (n : ℝ) / 100)) / 3 =
        (1 - δ ^ 3) / 1200 * (u ^ 10 * (n : ℝ)) := by
      dsimp [δ]; field_simp [hu0.ne']; ring
    have h2 : u ^ 10 * (n : ℝ) / 1300 ≤ (1 - δ ^ 3) / 1200 * (u ^ 10 * (n : ℝ)) := by
      nlinarith [show 0 ≤ u ^ 10 * (n : ℝ) by positivity]
    linarith
  have hmono_e : Real.exp (-((δ / 2) ^ 2 * (p * (A.card : ℝ)) / 3)) ≤
      Real.exp (-(u ^ 10 * (n : ℝ) / 1300)) := Real.exp_le_exp.mpr (by linarith)
  calc μ.prob _ ≤ μ.prob (fun S => ((S ∩ A).card : ℝ) < (1 - δ / 2) * (p * (A.card : ℝ))) +
        μ.prob (fun S => (1 + δ / 2) * (p * (A.card : ℝ)) < ((S ∩ A).card : ℝ)) :=
        hsub_ev.trans (μ.prob_or_le _ _)
    _ ≤ 2 * Real.exp (-(u ^ 10 * (n : ℝ) / 1300)) := by linarith

/-- Conditional single-outcome subsampling step inside Lemma 4.2. -/
private lemma subsampling_fixed_S0 {n : ℕ} {u m₀ : ℝ}
    (hu : 1000 ≤ u) (hm₀_lo : u ^ 12 ≤ m₀) (hm₀_hi : m₀ ≤ u ^ 36) (hm₀_n : m₀ ≤ (n : ℝ))
    {S₀ : Finset (ℕ × ℕ)} (hS₀ : IsPrevNice n u m₀ S₀)
    (hp0 : 0 ≤ u ^ 12 / m₀) (hp1 : u ^ 12 / m₀ ≤ 1) :
    let μ := bernDist hS₀.1 hp0 hp1
    0 < μ.prob (IsNice n u) ∧
    (∀ T ⊆ grid n, T.Nonempty → T ⊆ S₀ →
      μ.prob (fun S => T ⊆ S ∧ IsNice n u S) ≤
        ((u ^ 12 / m₀) * (1 + u⁻¹ ^ 36) ^ 2) ^ T.card * μ.prob (IsNice n u)) := by
  have hu0 : 0 < u := by linarith
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have hm_pos : 0 < u ^ 12 := by positivity
  have hm₀_pos : 0 < m₀ := lt_of_lt_of_le hm_pos hm₀_lo
  have hn_pos : (0 : ℝ) < n := lt_of_lt_of_le hm₀_pos hm₀_n
  have hn_ge2 : 2 ≤ n := by
    have h1 : (2 : ℝ) ≤ u ^ 12 := by
      have : (1000 : ℝ) ^ 12 ≤ u ^ 12 := pow_le_pow_left₀ (by norm_num) hu 12
      linarith
    exact_mod_cast h1.trans (hm₀_lo.trans hm₀_n)
  let p : ℝ := u ^ 12 / m₀
  let δ : ℝ := u⁻¹
  have hδ_pos : 0 < δ := inv_pos.mpr hu0
  have hδ_le : δ ≤ 1 / 1000 := by dsimp [δ]; rw [inv_le_comm₀ hu0 (by norm_num)]; linarith
  have hδ3_le : δ ^ 3 ≤ 1 / 1000000000 := by
    calc δ ^ 3 ≤ (1 / 1000 : ℝ) ^ 3 := pow_le_pow_left₀ hδ_pos.le hδ_le 3
      _ = 1 / 1000000000 := by norm_num
  let μ := bernDist hS₀.1 hp0 hp1
  let J : Finset (Finset (ℕ × ℕ)) :=
    (allLines n).filter fun L => (m₀ ^ 2)⁻¹ * (n : ℝ) < (L.card : ℝ) ∧ (S₀ ∩ L).Nonempty
  let E : Finset (ℕ × ℕ) → Finset (ℕ × ℕ) → Prop := badLineEvent n u
  let X : Finset (ℕ × ℕ) → Finset (ℕ × ℕ) := fun L => S₀ ∩ L
  have hdep : ∀ L ∈ J, ∀ S ⊆ S₀, E L S ↔ E L (S ∩ X L) := by
    intro L _ S hSS₀
    have hEq : (S ∩ X L) ∩ L = S ∩ L := by
      ext x; simp only [X, Finset.mem_inter]
      exact ⟨fun ⟨⟨hxS, _⟩, hxL⟩ => ⟨hxS, hxL⟩, fun ⟨hxS, hxL⟩ => ⟨⟨hxS, hSS₀ hxS, hxL⟩, hxL⟩⟩
    dsimp only [E, badLineEvent]; rw [hEq]
  let q : ℝ := (1 / (5 * u ^ 12)) ^ 15
  have hq0 : 0 ≤ q := by positivity
  have hq4 : q ≤ 1 / 4 := by
    dsimp [q]
    have h5 : (2 : ℝ) ≤ 5 * u ^ 12 := by have : (1 : ℝ) ≤ u ^ 12 := one_le_pow₀ hu1; linarith
    have hinv : 1 / (5 * u ^ 12) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h5
    calc (1 / (5 * u ^ 12)) ^ 15 ≤ (1 / 2 : ℝ) ^ 15 := pow_le_pow_left₀ (by positivity) hinv 15
      _ ≤ 1 / 4 := by norm_num
  have hprob : ∀ L ∈ J, μ.prob (E L) ≤ q := fun L hLJ =>
    bad_line_prob_le hu hm₀_lo hm₀_n hS₀ (Finset.mem_filter.mp hLJ).1 (Finset.mem_filter.mp hLJ).2.1
  let D : ℕ := Nat.floor (18 * m₀ ^ 4)
  have hD_le : (D : ℝ) ≤ 18 * m₀ ^ 4 := Nat.floor_le (by positivity)
  have hpt_deg : ∀ v : ℕ × ℕ, (J.filter (fun L => v ∈ L)).card ≤ D := by
    intro v
    apply Nat.le_floor
    have hsub : J.filter (fun L => v ∈ L) ⊆
        (allLines n).filter (fun L => v ∈ L ∧ (m₀ ^ 2)⁻¹ * (n : ℝ) ≤ (L.card : ℝ)) := by
      intro L hL
      obtain ⟨hLJ, hvL⟩ := Finset.mem_filter.mp hL
      obtain ⟨hLall, hLw, _⟩ := Finset.mem_filter.mp hLJ
      exact Finset.mem_filter.mpr ⟨hLall, hvL, hLw.le⟩
    have hcard_le : ((J.filter (fun L => v ∈ L)).card : ℝ) ≤
        (((allLines n).filter (fun L => v ∈ L ∧ (m₀ ^ 2)⁻¹ * (n : ℝ) ≤ (L.card : ℝ))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hα1 : (m₀ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
      have : (1 : ℝ) ≤ m₀ := (one_le_pow₀ hu1).trans hm₀_lo; nlinarith)
    have hpt := polynomial_tails_lines (by omega : 1 ≤ n) v (by positivity : 0 < (m₀ ^ 2)⁻¹) hα1
    have halg : 18 / ((m₀ ^ 2)⁻¹) ^ 2 = 18 * m₀ ^ 4 := by field_simp [hm₀_pos.ne']
    exact hcard_le.trans (halg ▸ hpt)
  have hset_deg : ∀ Y : Finset (ℕ × ℕ),
      (J.filter (fun L => ¬ Disjoint Y (X L))).card ≤ Y.card * D := by
    intro Y
    have hsub : J.filter (fun L => ¬ Disjoint Y (X L)) ⊆
        Y.biUnion (fun v => J.filter (fun L => v ∈ L)) := by
      intro L hL
      obtain ⟨hLJ, hnd⟩ := Finset.mem_filter.mp hL
      rw [Finset.not_disjoint_iff] at hnd
      obtain ⟨v, hvY, hvXL⟩ := hnd
      exact Finset.mem_biUnion.mpr ⟨v, hvY, Finset.mem_filter.mpr ⟨hLJ, (Finset.mem_inter.mp hvXL).2⟩⟩
    calc (J.filter (fun L => ¬ Disjoint Y (X L))).card
        ≤ (Y.biUnion (fun v => J.filter (fun L => v ∈ L))).card := Finset.card_le_card hsub
      _ ≤ ∑ v ∈ Y, (J.filter (fun L => v ∈ L)).card := Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ Y, D := Finset.sum_le_sum fun v _ => hpt_deg v
      _ = Y.card * D := by simp
  have hXL_le : ∀ L ∈ J, ((X L).card : ℝ) ≤ (1 + δ ^ 3) * m₀ := by
    intro L hLJ
    obtain ⟨hLall, hLw, _⟩ := Finset.mem_filter.mp hLJ
    by_cases h1 : (u ^ 24)⁻¹ * (n : ℝ) < (L.card : ℝ)
    · have hhi := (hS₀.2.1 L hLall h1).2
      have hLn : (L.card : ℝ) / (n : ℝ) ≤ 1 := by
        rw [div_le_one hn_pos]; exact_mod_cast (line_card_bounds hLall).2
      have hmul := mul_le_mul_of_nonneg_left hLn (by positivity : 0 ≤ (1 + u⁻¹ ^ 3) * m₀)
      rw [mul_one] at hmul
      exact hhi.trans hmul
    · push Not at h1
      have hhi := hS₀.2.2.1 L hLall hLw h1
      have hu24 : (u ^ 24)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hu1)
      have hmul := mul_le_mul_of_nonneg_left hu24 (by positivity : 0 ≤ (1 + u⁻¹ ^ 3) * m₀)
      rw [mul_one] at hmul
      exact hhi.trans hmul
  let Δ : ℕ := Nat.floor (20 * u ^ 180)
  have hΔ_le : (Δ : ℝ) ≤ 20 * u ^ 180 := Nat.floor_le (by positivity)
  have hdeg : ∀ L ∈ J, (J.filter (fun L' => L' ≠ L ∧ ¬ Disjoint (X L) (X L'))).card ≤ Δ := by
    intro L hLJ
    apply Nat.le_floor
    have h1 : (J.filter (fun L' => L' ≠ L ∧ ¬ Disjoint (X L) (X L'))).card ≤ (X L).card * D :=
      (Finset.card_le_card (fun L' hL' => by
        simp only [Finset.mem_filter] at hL' ⊢; exact ⟨hL'.1, hL'.2.2⟩)).trans (hset_deg (X L))
    have h1R : ((J.filter (fun L' => L' ≠ L ∧ ¬ Disjoint (X L) (X L'))).card : ℝ) ≤
        ((X L).card : ℝ) * (D : ℝ) := by exact_mod_cast h1
    have hm₀5 : m₀ ^ 5 ≤ u ^ 180 := by
      calc m₀ ^ 5 ≤ (u ^ 36) ^ 5 := pow_le_pow_left₀ hm₀_pos.le hm₀_hi 5
        _ = u ^ 180 := by ring
    calc ((J.filter (fun L' => L' ≠ L ∧ ¬ Disjoint (X L) (X L'))).card : ℝ)
        ≤ ((X L).card : ℝ) * (D : ℝ) := h1R
      _ ≤ ((1 + δ ^ 3) * m₀) * (18 * m₀ ^ 4) :=
          mul_le_mul (hXL_le L hLJ) hD_le (Nat.cast_nonneg D) (by positivity)
      _ = (18 * (1 + δ ^ 3)) * m₀ ^ 5 := by ring
      _ ≤ 20 * u ^ 180 := mul_le_mul (by linarith) hm₀5 (by positivity) (by norm_num)
  have hlll : 4 * q * (Δ : ℝ) ≤ 1 := by
    have h1 : 4 * q * (Δ : ℝ) ≤ 4 * (1 / (5 * u ^ 12)) ^ 15 * (20 * u ^ 180) :=
      mul_le_mul_of_nonneg_left hΔ_le (by positivity)
    have h2 : 4 * (1 / (5 * u ^ 12)) ^ 15 * (20 * u ^ 180) = 80 / (5 : ℝ) ^ 15 := by
      field_simp [hu0.ne']; ring
    rw [h2] at h1
    linarith [show (80 : ℝ) / (5 : ℝ) ^ 15 ≤ 1 by norm_num]
  obtain ⟨hEpos, hLLL_cond⟩ := lll_conditional hS₀.1 hp0 hp1 J E X hdep hq0 hq4 hprob hdeg hlll
  let avoidJ : Finset (ℕ × ℕ) → Prop := fun S => ∀ L ∈ J, ¬ E L S
  have hS₀_card : (S₀.card : ℝ) ≤ (n : ℝ) * ((1 + δ ^ 3) * m₀) := by
    have hpart : S₀.card = ∑ y ∈ range n, (S₀ ∩ (grid n).filter (fun p => p.2 = y)).card := by
      rw [card_eq_sum_degR hS₀.1]
      refine Finset.sum_congr rfl fun y _ => ?_
      unfold degR; congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_inter]
      exact ⟨fun ⟨hpS, hpy⟩ => ⟨hpS, hS₀.1 hpS, hpy⟩, fun ⟨hpS, _, hpy⟩ => ⟨hpS, hpy⟩⟩
    have hrow : ∀ y ∈ range n, ((S₀ ∩ (grid n).filter (fun p => p.2 = y)).card : ℝ) ≤
        (1 + δ ^ 3) * m₀ := by
      intro y hy
      let Ly := (grid n).filter (fun p => p.2 = y)
      have hLy_mem : Ly ∈ allLines n := horizLine_mem hn_ge2 hy
      have hLy_card : Ly.card = n := by
        have hEq : Ly = (range n).image (fun x => (x, y)) := by
          ext ⟨a, b⟩; simp only [Ly, grid, Finset.mem_filter, Finset.mem_product, Finset.mem_image]
          exact ⟨fun ⟨⟨ha, _⟩, hb⟩ => ⟨a, ha, Prod.ext rfl hb.symm⟩,
            fun ⟨a, ha, heq⟩ => by cases heq; exact ⟨⟨ha, hy⟩, rfl⟩⟩
        rw [hEq, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h), Finset.card_range]
      have hbig : (u ^ 24)⁻¹ * (n : ℝ) < (Ly.card : ℝ) := by
        rw [hLy_card]
        have : (u ^ 24)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by
          have : (1000 : ℝ) ^ 24 ≤ u ^ 24 := pow_le_pow_left₀ (by norm_num) hu 24; linarith)
        nlinarith
      have hhi := (hS₀.2.1 Ly hLy_mem hbig).2
      rw [hLy_card, div_self hn_pos.ne', mul_one] at hhi
      exact hhi
    rw [show (S₀.card : ℝ) = ∑ y ∈ range n, ((S₀ ∩ (grid n).filter (fun p => p.2 = y)).card : ℝ) by
      rw [hpart, Nat.cast_sum]]
    calc ∑ y ∈ range n, ((S₀ ∩ (grid n).filter (fun p => p.2 = y)).card : ℝ)
        ≤ ∑ _y ∈ range n, ((1 + δ ^ 3) * m₀) := Finset.sum_le_sum hrow
      _ = (n : ℝ) * ((1 + δ ^ 3) * m₀) := by simp
  have hJ_card : (J.card : ℝ) ≤ 20 * u ^ 180 * (n : ℝ) := by
    have hsub : J ⊆ S₀.biUnion (fun v => J.filter (fun L => v ∈ L)) := by
      intro L hLJ
      obtain ⟨v, hv⟩ := (Finset.mem_filter.mp hLJ).2.2
      obtain ⟨hvS₀, hvL⟩ := Finset.mem_inter.mp hv
      exact Finset.mem_biUnion.mpr ⟨v, hvS₀, Finset.mem_filter.mpr ⟨hLJ, hvL⟩⟩
    have h1 : J.card ≤ S₀.card * D := by
      calc J.card ≤ (S₀.biUnion (fun v => J.filter (fun L => v ∈ L))).card := Finset.card_le_card hsub
        _ ≤ ∑ v ∈ S₀, (J.filter (fun L => v ∈ L)).card := Finset.card_biUnion_le
        _ ≤ ∑ _v ∈ S₀, D := Finset.sum_le_sum fun v _ => hpt_deg v
        _ = S₀.card * D := by simp
    have h1R : (J.card : ℝ) ≤ (S₀.card : ℝ) * (D : ℝ) := by exact_mod_cast h1
    have hm₀5 : m₀ ^ 5 ≤ u ^ 180 := by
      calc m₀ ^ 5 ≤ (u ^ 36) ^ 5 := pow_le_pow_left₀ hm₀_pos.le hm₀_hi 5
        _ = u ^ 180 := by ring
    calc (J.card : ℝ) ≤ (S₀.card : ℝ) * (D : ℝ) := h1R
      _ ≤ ((n : ℝ) * ((1 + δ ^ 3) * m₀)) * (18 * m₀ ^ 4) :=
          mul_le_mul hS₀_card hD_le (Nat.cast_nonneg D) (by positivity)
      _ = (18 * (1 + δ ^ 3)) * m₀ ^ 5 * (n : ℝ) := by ring
      _ ≤ 20 * u ^ 180 * (n : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul (by linarith) hm₀5 (by positivity) (by norm_num)) hn_pos.le
  have hqJ : q * (J.card : ℝ) ≤ (n : ℝ) := by
    have h1 : q * (J.card : ℝ) ≤ (1 / (5 * u ^ 12)) ^ 15 * (20 * u ^ 180 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hJ_card hq0
    have h2 : (1 / (5 * u ^ 12)) ^ 15 * (20 * u ^ 180 * (n : ℝ)) = (20 / (5 : ℝ) ^ 15) * (n : ℝ) := by
      field_simp [hu0.ne']
    rw [h2] at h1
    have h3 : (20 : ℝ) / (5 : ℝ) ^ 15 ≤ 1 := by norm_num
    exact h1.trans (by nlinarith)
  let E₄ : Finset (ℕ × ℕ) → Prop := fun S =>
    ∃ I ∈ (range n).powerset, ∃ J' ∈ (range n).powerset,
      (n : ℝ) / 10 ≤ (I.card : ℝ) ∧ (n : ℝ) / 10 ≤ (J'.card : ℝ) ∧
      ¬ ((1 - δ) * (I.card : ℝ) * (J'.card : ℝ) * (u ^ 12 / (n : ℝ)) ≤ ((S ∩ (I ×ˢ J')).card : ℝ) ∧
         ((S ∩ (I ×ˢ J')).card : ℝ) ≤ (1 + δ) * (I.card : ℝ) * (J'.card : ℝ) * (u ^ 12 / (n : ℝ)))
  have hE₄_prob : μ.prob (fun S => E₄ S ∧ avoidJ S) ≤ Real.exp (-(n : ℝ)) * μ.prob avoidJ := by
    let pairs := ((range n).powerset ×ˢ (range n).powerset).filter fun IJ =>
      (n : ℝ) / 10 ≤ (IJ.1.card : ℝ) ∧ (n : ℝ) / 10 ≤ (IJ.2.card : ℝ)
    let Fpair : Finset ℕ × Finset ℕ → Finset (ℕ × ℕ) → Prop := fun IJ S =>
      ¬ ((1 - δ) * (IJ.1.card : ℝ) * (IJ.2.card : ℝ) * (u ^ 12 / (n : ℝ)) ≤
            ((S ∩ (IJ.1 ×ˢ IJ.2)).card : ℝ) ∧
         ((S ∩ (IJ.1 ×ˢ IJ.2)).card : ℝ) ≤
            (1 + δ) * (IJ.1.card : ℝ) * (IJ.2.card : ℝ) * (u ^ 12 / (n : ℝ)))
    have hmono : μ.prob (fun S => E₄ S ∧ avoidJ S) ≤
        μ.prob (fun S => ∃ IJ ∈ pairs, Fpair IJ S ∧ avoidJ S) := by
      refine μ.prob_mono fun S _ ⟨hE₄S, hAv⟩ => ?_
      obtain ⟨I, hI, J', hJ', hIc, hJc, hbad⟩ := hE₄S
      exact ⟨(I, J'), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hI, hJ'⟩, hIc, hJc⟩, hbad, hAv⟩
    have hpair_bound : ∀ IJ ∈ pairs,
        μ.prob (fun S => Fpair IJ S ∧ avoidJ S) ≤
          2 * Real.exp (-(u ^ 10 * (n : ℝ) / 1300)) * Real.exp (6 * (n : ℝ)) * μ.prob avoidJ := by
      intro IJ hIJ
      obtain ⟨hIJp, hIc, hJc⟩ := Finset.mem_filter.mp hIJ
      obtain ⟨hI, hJ'⟩ := Finset.mem_product.mp hIJp
      have hFdep : ∀ S ⊆ S₀, Fpair IJ S ↔ Fpair IJ (S ∩ (IJ.1 ×ˢ IJ.2)) := by
        intro S _; dsimp only [Fpair]; rw [Finset.inter_assoc, Finset.inter_self]
      have hM : (J.filter (fun L => ¬ Disjoint (IJ.1 ×ˢ IJ.2) (X L))).card ≤ J.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      have hcond := hLLL_cond (Fpair IJ) (IJ.1 ×ˢ IJ.2) J.card hFdep hM
      have hF_le : μ.prob (Fpair IJ) ≤ 2 * Real.exp (-(u ^ 10 * (n : ℝ) / 1300)) :=
        quasirandom_pair_prob_le hu hm₀_lo hm₀_n hS₀
          (Finset.mem_powerset.mp hI) (Finset.mem_powerset.mp hJ') hIc hJc
      have hexp6 : Real.exp (6 * q * (J.card : ℝ)) ≤ Real.exp (6 * (n : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith)
      calc μ.prob (fun S => Fpair IJ S ∧ avoidJ S)
          ≤ μ.prob (Fpair IJ) * Real.exp (6 * q * (J.card : ℝ)) * μ.prob avoidJ := hcond
        _ ≤ (2 * Real.exp (-(u ^ 10 * (n : ℝ) / 1300))) * Real.exp (6 * (n : ℝ)) * μ.prob avoidJ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul hF_le hexp6 (Real.exp_pos _).le (by positivity))
              (μ.prob_nonneg _)
    have hpairs_card : (pairs.card : ℝ) ≤ (2 : ℝ) ^ (2 * n) := by
      have hnat : pairs.card ≤ 2 ^ (2 * n) := by
        calc pairs.card ≤ ((range n).powerset ×ˢ (range n).powerset).card :=
              Finset.card_le_card (Finset.filter_subset _ _)
          _ = 2 ^ n * 2 ^ n := by simp [Finset.card_powerset]
          _ = 2 ^ (2 * n) := by rw [← pow_add, two_mul]
      exact_mod_cast hnat
    have h2_le_e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hpow2 : (2 : ℝ) ^ (2 * n) * 2 ≤ Real.exp (3 * (n : ℝ)) := by
      have h1 : (2 : ℝ) ^ (2 * n) ≤ Real.exp (2 * (n : ℝ)) := by
        calc (2 : ℝ) ^ (2 * n) ≤ (Real.exp 1) ^ (2 * n) := pow_le_pow_left₀ (by norm_num) h2_le_e _
          _ = Real.exp ((2 * n : ℕ) * (1 : ℝ)) := (Real.exp_nat_mul 1 (2 * n)).symm
          _ = Real.exp (2 * (n : ℝ)) := by push_cast; ring_nf
      have h2 : (2 : ℝ) ≤ Real.exp (n : ℝ) := by
        have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
        exact h2_le_e.trans (Real.exp_le_exp.mpr h1n)
      calc (2 : ℝ) ^ (2 * n) * 2 ≤ Real.exp (2 * (n : ℝ)) * Real.exp (n : ℝ) :=
            mul_le_mul h1 h2 (by norm_num) (Real.exp_pos _).le
        _ = Real.exp (3 * (n : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
    have hu10_ge : (10 : ℝ) ≤ u ^ 10 / 1300 := by
      have : (1000 : ℝ) ^ 10 ≤ u ^ 10 := pow_le_pow_left₀ (by norm_num) hu 10; linarith
    have hfinal_exp : (2 : ℝ) ^ (2 * n) * (2 * Real.exp (-(u ^ 10 * (n : ℝ) / 1300)) *
        Real.exp (6 * (n : ℝ))) ≤ Real.exp (-(n : ℝ)) := by
      calc (2 : ℝ) ^ (2 * n) * (2 * Real.exp (-(u ^ 10 * (n : ℝ) / 1300)) * Real.exp (6 * (n : ℝ)))
          = ((2 : ℝ) ^ (2 * n) * 2) * (Real.exp (-(u ^ 10 * (n : ℝ) / 1300)) * Real.exp (6 * (n : ℝ))) := by ring
        _ ≤ Real.exp (3 * (n : ℝ)) * (Real.exp (-(u ^ 10 * (n : ℝ) / 1300)) * Real.exp (6 * (n : ℝ))) :=
            mul_le_mul_of_nonneg_right hpow2 (by positivity)
        _ = Real.exp (3 * (n : ℝ) + -(u ^ 10 * (n : ℝ) / 1300) + 6 * (n : ℝ)) := by
            rw [← Real.exp_add, ← Real.exp_add, add_assoc]
        _ ≤ Real.exp (-(n : ℝ)) := Real.exp_le_exp.mpr (by nlinarith)
    calc μ.prob (fun S => E₄ S ∧ avoidJ S)
        ≤ ∑ IJ ∈ pairs, μ.prob (fun S => Fpair IJ S ∧ avoidJ S) :=
          hmono.trans (μ.prob_exists_le pairs fun IJ S => Fpair IJ S ∧ avoidJ S)
      _ ≤ ∑ _IJ ∈ pairs, (2 * Real.exp (-(u ^ 10 * (n : ℝ) / 1300)) *
            Real.exp (6 * (n : ℝ)) * μ.prob avoidJ) := Finset.sum_le_sum hpair_bound
      _ = (pairs.card : ℝ) * (2 * Real.exp (-(u ^ 10 * (n : ℝ) / 1300)) *
            Real.exp (6 * (n : ℝ))) * μ.prob avoidJ := by simp [mul_assoc]
      _ ≤ ((2 : ℝ) ^ (2 * n) * (2 * Real.exp (-(u ^ 10 * (n : ℝ) / 1300)) *
            Real.exp (6 * (n : ℝ)))) * μ.prob avoidJ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hpairs_card (by positivity)) (μ.prob_nonneg _)
      _ ≤ Real.exp (-(n : ℝ)) * μ.prob avoidJ :=
            mul_le_mul_of_nonneg_right hfinal_exp (μ.prob_nonneg _)
  have hgood_imp_nice : ∀ S ⊆ S₀, avoidJ S ∧ ¬ E₄ S → IsNice n u S := by
    intro S hSS₀ ⟨hAv, hnot4⟩
    refine ⟨hSS₀.trans hS₀.1, ?_, ?_, ?_, ?_⟩
    · intro L hLall hheavy
      have hmed : (u ^ 24)⁻¹ * (n : ℝ) < (L.card : ℝ) := by
        have h1 : (u ^ 24)⁻¹ ≤ (u ^ 8)⁻¹ := inv_anti₀ (by positivity)
          (by calc u ^ 8 = u ^ 8 * 1 := (mul_one _).symm
            _ ≤ u ^ 8 * u ^ 16 := mul_le_mul_of_nonneg_left (one_le_pow₀ hu1) (by positivity)
            _ = u ^ 24 := by ring)
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right h1 hn_pos.le) hheavy
      have hLw : (m₀ ^ 2)⁻¹ * (n : ℝ) < (L.card : ℝ) := by
        have h1 : (m₀ ^ 2)⁻¹ ≤ (u ^ 24)⁻¹ := inv_anti₀ (by positivity) (by
          have := pow_le_pow_left₀ hm_pos.le hm₀_lo 2
          linarith [show (u ^ 12) ^ 2 = u ^ 24 by ring])
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right h1 hn_pos.le) hmed
      have hne : (S₀ ∩ L).Nonempty := by
        have hlo := (hS₀.2.1 L hLall hmed).1
        have hpos : (0 : ℝ) < ((S₀ ∩ L).card : ℝ) := by
          have : (0 : ℝ) < (L.card : ℝ) := lt_of_le_of_lt (by positivity) hheavy
          have : 0 < 1 - u⁻¹ ^ 3 := by linarith
          linarith [show 0 < (1 - u⁻¹ ^ 3) * m₀ * ((L.card : ℝ) / (n : ℝ)) by positivity]
        exact Finset.card_pos.mp (by exact_mod_cast hpos)
      have hnotE := hAv L (Finset.mem_filter.mpr ⟨hLall, hLw, hne⟩)
      dsimp only [E, badLineEvent] at hnotE
      rw [if_pos hheavy, not_not] at hnotE
      exact hnotE
    · intro L hLall hmed hheavy
      by_cases hne : (S₀ ∩ L).Nonempty
      · have hLw : (m₀ ^ 2)⁻¹ * (n : ℝ) < (L.card : ℝ) := by
          have h1 : (m₀ ^ 2)⁻¹ ≤ (u ^ 24)⁻¹ := inv_anti₀ (by positivity) (by
            have := pow_le_pow_left₀ hm_pos.le hm₀_lo 2
            linarith [show (u ^ 12) ^ 2 = u ^ 24 by ring])
          exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right h1 hn_pos.le) hmed
        have hnotE := hAv L (Finset.mem_filter.mpr ⟨hLall, hLw, hne⟩)
        dsimp only [E, badLineEvent] at hnotE
        rw [if_neg (not_lt.mpr hheavy), if_pos hmed, not_not] at hnotE
        exact hnotE
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        have h0 : S ∩ L = ∅ := Finset.subset_empty.mp
          ((Finset.inter_subset_inter_right hSS₀).trans hne.subset)
        rw [h0]; simp; positivity
    · intro L hLall hlight
      by_cases hLw : (m₀ ^ 2)⁻¹ * (n : ℝ) < (L.card : ℝ)
      · by_cases hne : (S₀ ∩ L).Nonempty
        · have hnotE := hAv L (Finset.mem_filter.mpr ⟨hLall, hLw, hne⟩)
          dsimp only [E, badLineEvent] at hnotE
          have hnot_heavy : ¬ ((u ^ 8)⁻¹ * (n : ℝ) < (L.card : ℝ)) := by
            have h1 : (u ^ 24)⁻¹ ≤ (u ^ 8)⁻¹ := inv_anti₀ (by positivity)
              (by calc u ^ 8 = u ^ 8 * 1 := (mul_one _).symm
                _ ≤ u ^ 8 * u ^ 16 := mul_le_mul_of_nonneg_left (one_le_pow₀ hu1) (by positivity)
                _ = u ^ 24 := by ring)
            have := mul_le_mul_of_nonneg_right h1 hn_pos.le
            linarith
          rw [if_neg hnot_heavy, if_neg (not_lt.mpr hlight), not_not] at hnotE
          exact hnotE
        · rw [Finset.not_nonempty_iff_eq_empty] at hne
          have h0 : S ∩ L = ∅ := Finset.subset_empty.mp
            ((Finset.inter_subset_inter_right hSS₀).trans hne.subset)
          rw [h0]; simp
      · push Not at hLw
        exact (Finset.card_le_card (Finset.inter_subset_inter_right hSS₀)).trans
          (hS₀.2.2.2.1 L hLall hLw)
    · intro I hI J' hJ' hIc hJc
      by_contra hbad
      exact hnot4 ⟨I, Finset.mem_powerset.mpr hI, J', Finset.mem_powerset.mpr hJ', hIc, hJc, hbad⟩
  have hnice_ge : (1 - Real.exp (-(n : ℝ))) * μ.prob avoidJ ≤ μ.prob (IsNice n u) := by
    have h1 : μ.prob (fun S => ¬ E₄ S ∧ avoidJ S) ≤ μ.prob (IsNice n u) := by
      unfold Dist.prob μ bernDist; dsimp only
      refine Finset.sum_le_sum fun S _ => ?_
      by_cases hSS₀ : S ⊆ S₀
      · by_cases hgood : ¬ E₄ S ∧ avoidJ S
        · simp only [if_pos hgood, if_pos (hgood_imp_nice S hSS₀ ⟨hgood.2, hgood.1⟩), le_rfl]
        · simp only [if_neg hgood]; split_ifs <;> [exact bernW_nonneg hp0 hp1 S; exact le_rfl]
      · simp [bernW, hSS₀]
    have hsplit := μ.prob_and_add_and_not E₄ avoidJ
    linarith
  have hexp_n_le : Real.exp (-(n : ℝ)) ≤ (1 / 2) * u⁻¹ ^ 36 := by
    have h1 : 2 * u ^ 36 ≤ Real.exp (u ^ 12) := by
      have hb : u ^ 12 / 4 ≤ Real.exp (u ^ 12 / 4) := by linarith [Real.add_one_le_exp (u ^ 12 / 4)]
      have hp4 : (u ^ 12 / 4) ^ 4 ≤ Real.exp (u ^ 12) := by
        calc (u ^ 12 / 4) ^ 4 ≤ (Real.exp (u ^ 12 / 4)) ^ 4 := pow_le_pow_left₀ (by positivity) hb 4
          _ = Real.exp (4 * (u ^ 12 / 4)) := (Real.exp_nat_mul _ 4).symm
          _ = Real.exp (u ^ 12) := by congr 1; ring
      have hu12 : (512 : ℝ) ≤ u ^ 12 := by
        have : (1000 : ℝ) ^ 12 ≤ u ^ 12 := pow_le_pow_left₀ (by norm_num) hu 12; linarith
      calc 2 * u ^ 36 = (512 / 256) * u ^ 36 := by ring
        _ ≤ (u ^ 12 / 256) * u ^ 36 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = (u ^ 12 / 4) ^ 4 := by ring
        _ ≤ Real.exp (u ^ 12) := hp4
    have h2 : Real.exp (-(n : ℝ)) ≤ (Real.exp (u ^ 12))⁻¹ := by
      rw [← Real.exp_neg]; exact Real.exp_le_exp.mpr (by linarith)
    calc Real.exp (-(n : ℝ)) ≤ (Real.exp (u ^ 12))⁻¹ := h2
      _ ≤ (2 * u ^ 36)⁻¹ := inv_anti₀ (by positivity) h1
      _ = (1 / 2) * u⁻¹ ^ 36 := by rw [mul_inv, inv_pow]; ring
  have h1sub_pos : 0 < 1 - Real.exp (-(n : ℝ)) := by
    have : u⁻¹ ^ 36 ≤ 1 := pow_le_one₀ (by positivity) (by linarith); linarith
  have hnice_pos : 0 < μ.prob (IsNice n u) := lt_of_lt_of_le (mul_pos h1sub_pos hEpos) hnice_ge
  refine ⟨hnice_pos, fun T _ hTne hTS₀ => ?_⟩
  have hnice_imp_avoid : ∀ S ⊆ S₀, IsNice n u S → avoidJ S := by
    intro S _ hSnice L hLJ
    obtain ⟨hLall, _, _⟩ := Finset.mem_filter.mp hLJ
    dsimp only [E, badLineEvent]
    split_ifs with hheavy hmed
    · rw [not_not]; exact hSnice.2.1 L hLall hheavy
    · rw [not_not]; exact hSnice.2.2.1 L hLall hmed (not_lt.mp hheavy)
    · rw [not_not]; exact hSnice.2.2.2.1 L hLall (not_lt.mp hmed)
  have hle_avoid : μ.prob (fun S => T ⊆ S ∧ IsNice n u S) ≤
      μ.prob (fun S => T ⊆ S ∧ avoidJ S) := by
    unfold Dist.prob μ bernDist; dsimp only
    refine Finset.sum_le_sum fun S _ => ?_
    by_cases hSS₀ : S ⊆ S₀
    · by_cases hgood : T ⊆ S ∧ IsNice n u S
      · simp only [if_pos hgood, if_pos (And.intro hgood.1 (hnice_imp_avoid S hSS₀ hgood.2)), le_rfl]
      · simp only [if_neg hgood]; split_ifs <;> [exact bernW_nonneg hp0 hp1 S; exact le_rfl]
    · simp [bernW, hSS₀]
  have hTdep : ∀ S ⊆ S₀, (T ⊆ S) ↔ (T ⊆ S ∩ T) := by
    intro S _; exact ⟨fun h => Finset.subset_inter h Subset.rfl, fun h => h.trans Finset.inter_subset_left⟩
  have hTcond := hLLL_cond (fun S => T ⊆ S) T (T.card * D) hTdep (hset_deg T)
  rw [bern_prob_subset hS₀.1 hTS₀ hp0 hp1] at hTcond
  have h6qD : 6 * q * (D : ℝ) ≤ (1 / 2) * u⁻¹ ^ 36 := by
    have hm₀4 : m₀ ^ 4 ≤ u ^ 144 := by
      calc m₀ ^ 4 ≤ (u ^ 36) ^ 4 := pow_le_pow_left₀ hm₀_pos.le hm₀_hi 4
        _ = u ^ 144 := by ring
    have h1 : 6 * q * (D : ℝ) ≤ 6 * (1 / (5 * u ^ 12)) ^ 15 * (18 * u ^ 144) :=
      mul_le_mul_of_nonneg_left (hD_le.trans (mul_le_mul_of_nonneg_left hm₀4 (by norm_num))) (by positivity)
    have h2 : 6 * (1 / (5 * u ^ 12)) ^ 15 * (18 * u ^ 144) = (108 / (5 : ℝ) ^ 15) * u⁻¹ ^ 36 := by
      field_simp [hu0.ne']; ring
    rw [h2] at h1
    have h3 : (108 : ℝ) / (5 : ℝ) ^ 15 ≤ 1 / 2 := by norm_num
    exact h1.trans (mul_le_mul_of_nonneg_right h3 (by positivity))
  have hexp6qD : Real.exp (6 * q * (D : ℝ)) ≤ 1 + u⁻¹ ^ 36 := by
    have hhalf : 6 * q * (D : ℝ) ≤ 1 / 2 := h6qD.trans (by
      have : u⁻¹ ^ 36 ≤ 1 := pow_le_one₀ (by positivity) (by linarith); linarith)
    exact (exp_le_one_add_two_mul (by positivity) hhalf).trans (by linarith)
  have hinv_exp : (1 - Real.exp (-(n : ℝ)))⁻¹ ≤ 1 + u⁻¹ ^ 36 := by
    have hhalf : Real.exp (-(n : ℝ)) ≤ 1 / 2 := hexp_n_le.trans (by
      have : u⁻¹ ^ 36 ≤ 1 := pow_le_one₀ (by positivity) (by linarith); linarith)
    exact (inv_one_sub_le (Real.exp_pos _).le hhalf).trans (by linarith)
  have hTcard_ge1 : 1 ≤ T.card := Finset.card_pos.mpr hTne
  have hpow_fac : (1 + u⁻¹ ^ 36) * (p * (1 + u⁻¹ ^ 36)) ^ T.card ≤
      (p * (1 + u⁻¹ ^ 36) ^ 2) ^ T.card := by
    have h1 : (1 + u⁻¹ ^ 36) ≤ (1 + u⁻¹ ^ 36) ^ T.card :=
      le_self_pow₀ (by linarith [pow_nonneg hδ_pos.le 36] : (1 : ℝ) ≤ 1 + u⁻¹ ^ 36) (by omega)
    calc (1 + u⁻¹ ^ 36) * (p * (1 + u⁻¹ ^ 36)) ^ T.card
        ≤ (1 + u⁻¹ ^ 36) ^ T.card * (p * (1 + u⁻¹ ^ 36)) ^ T.card :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ((1 + u⁻¹ ^ 36) * (p * (1 + u⁻¹ ^ 36))) ^ T.card := (mul_pow _ _ _).symm
      _ = (p * (1 + u⁻¹ ^ 36) ^ 2) ^ T.card := by congr 1; ring
  have havoid_le : μ.prob avoidJ ≤ (1 - Real.exp (-(n : ℝ)))⁻¹ * μ.prob (IsNice n u) := by
    rw [inv_mul_eq_div, le_div_iff₀ h1sub_pos, mul_comm]; exact hnice_ge
  have hexp_split : Real.exp (6 * q * ((T.card * D : ℕ) : ℝ)) =
      (Real.exp (6 * q * (D : ℝ))) ^ T.card := by
    rw [Nat.cast_mul, ← Real.exp_nat_mul]; congr 1; ring
  calc μ.prob (fun S => T ⊆ S ∧ IsNice n u S)
      ≤ p ^ T.card * Real.exp (6 * q * ((T.card * D : ℕ) : ℝ)) * μ.prob avoidJ :=
        hle_avoid.trans hTcond
    _ = (p * Real.exp (6 * q * (D : ℝ))) ^ T.card * μ.prob avoidJ := by
        rw [hexp_split, mul_pow]
    _ ≤ (p * (1 + u⁻¹ ^ 36)) ^ T.card * ((1 - Real.exp (-(n : ℝ)))⁻¹ * μ.prob (IsNice n u)) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_left hexp6qD hp0) T.card) havoid_le (μ.prob_nonneg _) (by positivity)
    _ ≤ (p * (1 + u⁻¹ ^ 36)) ^ T.card * ((1 + u⁻¹ ^ 36) * μ.prob (IsNice n u)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hinv_exp (μ.prob_nonneg _)) (by positivity)
    _ = ((1 + u⁻¹ ^ 36) * (p * (1 + u⁻¹ ^ 36)) ^ T.card) * μ.prob (IsNice n u) := by ring
    _ ≤ (p * (1 + u⁻¹ ^ 36) ^ 2) ^ T.card * μ.prob (IsNice n u) :=
        mul_le_mul_of_nonneg_right hpow_fac (μ.prob_nonneg _)

/-- Unified Lemma 4.2 of Grebennikov--Kwan: from any `((1 + u⁻¹^36) * m₀ / n)`-spread distribution
supported on `IsPrevNice n u m₀`, produce a `((u^12 + 1) / n)`-spread distribution supported on
`IsNice n u`. -/
lemma induction_step_core {n : ℕ} {u m₀ : ℝ}
    (hu : 1000 ≤ u) (hm₀_lo : u ^ 12 ≤ m₀) (hm₀_hi : m₀ ≤ u ^ 36) (hm₀_n : m₀ ≤ (n : ℝ))
    (μ₀ : Dist (grid n))
    (hsupp : SupportedOn μ₀ (IsPrevNice n u m₀))
    (hspread : IsSpread n ((1 + u⁻¹ ^ 36) * m₀ / (n : ℝ)) μ₀) :
    ∃ μ₁ : Dist (grid n), SupportedOn μ₁ (IsNice n u) ∧
      IsSpread n ((u ^ 12 + 1) / (n : ℝ)) μ₁ := by
  have hu0 : 0 < u := by linarith
  have hm_pos : 0 < u ^ 12 := by positivity
  have hm₀_pos : 0 < m₀ := lt_of_lt_of_le hm_pos hm₀_lo
  have hn_pos : (0 : ℝ) < n := lt_of_lt_of_le hm₀_pos hm₀_n
  let p : ℝ := u ^ 12 / m₀
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := (div_le_one hm₀_pos).mpr hm₀_lo
  -- Conditional weight ν(S₀, S) for each S₀ ∈ (grid n).powerset
  let ν : Finset (ℕ × ℕ) → Finset (ℕ × ℕ) → ℝ := fun S₀ S =>
    if h : IsPrevNice n u m₀ S₀ then
      if IsNice n u S then
        bernW S₀ p S / (bernDist h.1 hp0 hp1).prob (IsNice n u)
      else 0
    else 0
  have hν_nonneg : ∀ S₀ S, 0 ≤ ν S₀ S := by
    intro S₀ S
    dsimp only [ν]
    split_ifs with h1 _
    · exact div_nonneg (bernW_nonneg hp0 hp1 S) ((bernDist h1.1 hp0 hp1).prob_nonneg _)
    · exact le_rfl
    · exact le_rfl
  have hν_sum : ∀ S₀, IsPrevNice n u m₀ S₀ →
      ∑ S ∈ (grid n).powerset, ν S₀ S = 1 := by
    intro S₀ hS₀
    have hpos := (subsampling_fixed_S0 hu hm₀_lo hm₀_hi hm₀_n hS₀ hp0 hp1).1
    have hrew : ∑ S ∈ (grid n).powerset, ν S₀ S =
        (∑ S ∈ (grid n).powerset, if IsNice n u S then bernW S₀ p S else 0) /
          (bernDist hS₀.1 hp0 hp1).prob (IsNice n u) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun S _ => ?_
      dsimp only [ν]
      rw [dif_pos hS₀]
      split_ifs <;> simp
    rw [hrew]
    exact div_self hpos.ne'
  let μ₁ : Dist (grid n) :=
    { w := fun S => ∑ S₀ ∈ (grid n).powerset, μ₀.w S₀ * ν S₀ S
      nonneg := fun S => Finset.sum_nonneg fun S₀ _ => mul_nonneg (μ₀.nonneg S₀) (hν_nonneg S₀ S)
      sum_eq := by
        rw [Finset.sum_comm]
        calc ∑ S₀ ∈ (grid n).powerset, ∑ S ∈ (grid n).powerset, μ₀.w S₀ * ν S₀ S
            = ∑ S₀ ∈ (grid n).powerset, μ₀.w S₀ * ∑ S ∈ (grid n).powerset, ν S₀ S := by
              refine Finset.sum_congr rfl fun S₀ _ => (Finset.mul_sum ..).symm
          _ = ∑ S₀ ∈ (grid n).powerset, μ₀.w S₀ := by
              refine Finset.sum_congr rfl fun S₀ hS₀ => ?_
              by_cases hw : 0 < μ₀.w S₀
              · rw [hν_sum S₀ (hsupp S₀ (Finset.mem_powerset.mp hS₀) hw), mul_one]
              · have hw0 : μ₀.w S₀ = 0 := le_antisymm (le_of_not_gt hw) (μ₀.nonneg S₀)
                rw [hw0, zero_mul]
          _ = 1 := μ₀.sum_eq }
  refine ⟨μ₁, ?_, ?_⟩
  · -- SupportedOn μ₁ (IsNice n u)
    intro S _ hw
    by_contra hnot
    have h0 : μ₁.w S = 0 := by
      apply Finset.sum_eq_zero
      intro S₀ _
      have : ν S₀ S = 0 := by dsimp only [ν]; by_cases h1 : IsPrevNice n u m₀ S₀ <;> simp [h1, hnot]
      rw [this, mul_zero]
    linarith
  · -- Spreadness of μ₁
    intro T hTgrid
    by_cases hTemp : T = ∅
    · subst hTemp
      rw [Finset.card_empty, pow_zero]
      exact μ₁.prob_le_one _
    have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hTemp
    -- Exchange sums: μ₁.prob (T ⊆ S) = ∑ S₀, μ₀.w S₀ * (∑ S ⊇ T, ν S₀ S)
    have hprob_eq : μ₁.prob (fun S => T ⊆ S) =
        ∑ S₀ ∈ (grid n).powerset, μ₀.w S₀ *
          (∑ S ∈ (grid n).powerset, if T ⊆ S then ν S₀ S else 0) := by
      unfold Dist.prob
      dsimp only [μ₁]
      calc _
          = ∑ S ∈ (grid n).powerset, ∑ S₀ ∈ (grid n).powerset, μ₀.w S₀ * (if T ⊆ S then ν S₀ S else 0) := by
            refine Finset.sum_congr rfl fun S _ => ?_
            by_cases hTS : T ⊆ S
            · simp only [if_pos hTS]
            · simp only [if_neg hTS, mul_zero, Finset.sum_const_zero]
        _ = ∑ S₀ ∈ (grid n).powerset, ∑ S ∈ (grid n).powerset, μ₀.w S₀ * (if T ⊆ S then ν S₀ S else 0) :=
            Finset.sum_comm
        _ = ∑ S₀ ∈ (grid n).powerset, μ₀.w S₀ * (∑ S ∈ (grid n).powerset, if T ⊆ S then ν S₀ S else 0) :=
            Finset.sum_congr rfl fun S₀ _ => (Finset.mul_sum ..).symm
    have hinner : ∀ S₀ ∈ (grid n).powerset,
        μ₀.w S₀ * (∑ S ∈ (grid n).powerset, if T ⊆ S then ν S₀ S else 0) ≤
          (p * (1 + u⁻¹ ^ 36) ^ 2) ^ T.card * (if T ⊆ S₀ then μ₀.w S₀ else 0) := by
      intro S₀ hS₀mem
      by_cases hw : 0 < μ₀.w S₀
      · have hS₀prev : IsPrevNice n u m₀ S₀ := hsupp S₀ (Finset.mem_powerset.mp hS₀mem) hw
        by_cases hTS₀ : T ⊆ S₀
        · rw [if_pos hTS₀]
          obtain ⟨hpos, hbound⟩ := subsampling_fixed_S0 hu hm₀_lo hm₀_hi hm₀_n hS₀prev hp0 hp1
          have hsum_eq : ∑ S ∈ (grid n).powerset, (if T ⊆ S then ν S₀ S else 0) =
              (bernDist hS₀prev.1 hp0 hp1).prob (fun S => T ⊆ S ∧ IsNice n u S) /
                (bernDist hS₀prev.1 hp0 hp1).prob (IsNice n u) := by
            rw [show (bernDist hS₀prev.1 hp0 hp1).prob (fun S => T ⊆ S ∧ IsNice n u S) =
                ∑ S ∈ (grid n).powerset, if T ⊆ S ∧ IsNice n u S then bernW S₀ p S else 0 by
              unfold Dist.prob; dsimp only [bernDist]
              refine Finset.sum_congr rfl fun S _ => ?_
              by_cases h : T ⊆ S ∧ IsNice n u S
              · simp only [if_pos h]
              · simp only [if_neg h]]
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl fun S _ => ?_
            dsimp only [ν]; rw [dif_pos hS₀prev]
            by_cases h1 : T ⊆ S <;> by_cases h2 : IsNice n u S
            · simp only [if_pos h1, if_pos h2, if_pos (And.intro h1 h2)]
            · simp only [if_pos h1, if_neg h2, if_neg (fun h : T ⊆ S ∧ IsNice n u S => h2 h.2), zero_div]
            · simp only [if_neg h1, if_neg (fun h : T ⊆ S ∧ IsNice n u S => h1 h.1), zero_div]
            · simp only [if_neg h1, if_neg (fun h : T ⊆ S ∧ IsNice n u S => h1 h.1), zero_div]
          rw [hsum_eq]
          have hdiv_le : (bernDist hS₀prev.1 hp0 hp1).prob (fun S => T ⊆ S ∧ IsNice n u S) /
              (bernDist hS₀prev.1 hp0 hp1).prob (IsNice n u) ≤
              (p * (1 + u⁻¹ ^ 36) ^ 2) ^ T.card :=
            (div_le_iff₀ hpos).mpr (hbound T hTgrid hTne hTS₀)
          have := mul_le_mul_of_nonneg_left hdiv_le hw.le
          linarith
        · rw [if_neg hTS₀, mul_zero]
          have hzero : ∑ S ∈ (grid n).powerset, (if T ⊆ S then ν S₀ S else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro S _
            by_cases hTS : T ⊆ S
            · have hnotSS₀ : ¬ (S ⊆ S₀) := fun h => hTS₀ (hTS.trans h)
              have : ν S₀ S = 0 := by
                dsimp only [ν]; split_ifs <;> simp [bernW, hnotSS₀]
              simp [hTS, this]
            · simp [hTS]
          rw [hzero, mul_zero]
      · have hw0 : μ₀.w S₀ = 0 := le_antisymm (le_of_not_gt hw) (μ₀.nonneg S₀)
        rw [hw0, zero_mul]; split_ifs <;> simp
    have hstep1 : μ₁.prob (fun S => T ⊆ S) ≤
        (p * (1 + u⁻¹ ^ 36) ^ 2) ^ T.card * μ₀.prob (fun S₀ => T ⊆ S₀) := by
      rw [hprob_eq]
      calc ∑ S₀ ∈ (grid n).powerset, μ₀.w S₀ * (∑ S ∈ (grid n).powerset, if T ⊆ S then ν S₀ S else 0)
          ≤ ∑ S₀ ∈ (grid n).powerset, (p * (1 + u⁻¹ ^ 36) ^ 2) ^ T.card * (if T ⊆ S₀ then μ₀.w S₀ else 0) :=
            Finset.sum_le_sum hinner
        _ = (p * (1 + u⁻¹ ^ 36) ^ 2) ^ T.card * μ₀.prob (fun S₀ => T ⊆ S₀) := by
            unfold Dist.prob; rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun S₀ _ => ?_
            by_cases hTS₀ : T ⊆ S₀
            · simp only [if_pos hTS₀]
            · simp only [if_neg hTS₀]
    have hbase : (p * (1 + u⁻¹ ^ 36) ^ 2) * ((1 + u⁻¹ ^ 36) * m₀ / (n : ℝ)) ≤
        (u ^ 12 + 1) / (n : ℝ) := by
      have halg : (p * (1 + u⁻¹ ^ 36) ^ 2) * ((1 + u⁻¹ ^ 36) * m₀ / (n : ℝ)) =
          ((1 + u⁻¹ ^ 36) ^ 3 * u ^ 12) / (n : ℝ) := by
        dsimp [p]; field_simp [hm₀_pos.ne', hn_pos.ne']
      rw [halg]
      apply div_le_div_of_nonneg_right _ hn_pos.le
      have hx : u⁻¹ ^ 36 ≤ (1 : ℝ) / 10 ^ 108 := by
        have h1 : u⁻¹ ≤ 1 / 1000 := by rw [inv_le_comm₀ hu0 (by norm_num)]; linarith
        calc u⁻¹ ^ 36 ≤ (1 / 1000 : ℝ) ^ 36 := pow_le_pow_left₀ (by positivity) h1 36
          _ = 1 / 10 ^ 108 := by norm_num
      have hx0 : 0 ≤ u⁻¹ ^ 36 := by positivity
      have hcube : (1 + u⁻¹ ^ 36) ^ 3 ≤ 1 + 4 * u⁻¹ ^ 36 := by
        have h1 : u⁻¹ ^ 36 ≤ 1 / 4 := hx.trans (by norm_num)
        nlinarith [sq_nonneg (u⁻¹ ^ 36)]
      have hmul := mul_le_mul_of_nonneg_right hcube hm_pos.le
      have h4 : 4 * u⁻¹ ^ 36 * u ^ 12 ≤ 1 := by
        have halg2 : 4 * u⁻¹ ^ 36 * u ^ 12 = 4 / u ^ 24 := by field_simp [hu0.ne']
        rw [halg2, div_le_one (by positivity : 0 < u ^ 24)]
        have : (1000 : ℝ) ^ 24 ≤ u ^ 24 := pow_le_pow_left₀ (by norm_num) hu 24
        linarith
      linarith
    calc μ₁.prob (fun S => T ⊆ S)
        ≤ (p * (1 + u⁻¹ ^ 36) ^ 2) ^ T.card * ((1 + u⁻¹ ^ 36) * m₀ / (n : ℝ)) ^ T.card :=
          hstep1.trans (mul_le_mul_of_nonneg_left (hspread T hTgrid) (by positivity))
      _ = ((p * (1 + u⁻¹ ^ 36) ^ 2) * ((1 + u⁻¹ ^ 36) * m₀ / (n : ℝ))) ^ T.card := (mul_pow _ _ _).symm
      _ ≤ ((u ^ 12 + 1) / (n : ℝ)) ^ T.card := pow_le_pow_left₀ (by positivity) hbase T.card

/-- Downward iteration of Lemma 4.2: for any `1000 ≤ u` and `u^12 ≤ n`, there exists a
`((u^12 + 1) / n)`-spread distribution supported on `IsNice n u`. -/
lemma iterated_nice_dist {n : ℕ} {u : ℝ} (hu : 1000 ≤ u) (hn : u ^ 12 ≤ (n : ℝ)) :
    ∃ μ : Dist (grid n), SupportedOn μ (IsNice n u) ∧
      IsSpread n ((u ^ 12 + 1) / (n : ℝ)) μ := by
  have hstep : ∀ t : ℕ, ∀ u : ℝ, 1000 ≤ u → u ^ 12 ≤ (n : ℝ) → (n : ℝ) ≤ (u ^ (3 ^ t)) ^ 12 →
      ∃ μ : Dist (grid n), SupportedOn μ (IsNice n u) ∧
        IsSpread n ((u ^ 12 + 1) / (n : ℝ)) μ := by
    intro t
    induction t with
    | zero =>
      intro u hu hn hle
      have hm₀_hi : (n : ℝ) ≤ u ^ 36 := by
        have h1 : (n : ℝ) ≤ u ^ 12 := by simpa using hle
        have h2 : u ^ 12 ≤ u ^ 36 := by
          have : (1 : ℝ) ≤ u ^ 24 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ u)
          nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ u) 12, show u ^ 36 = u ^ 12 * u ^ 24 by ring]
        exact h1.trans h2
      let μ₀ : Dist (grid n) :=
        { w := fun S => if S = grid n then 1 else 0
          nonneg := fun S => by split_ifs <;> norm_num
          sum_eq := by
            rw [Finset.sum_eq_single (grid n)]
            · simp
            · intro S _ hne; simp [hne]
            · intro hnot; exact False.elim (hnot (Finset.mem_powerset.mpr Subset.rfl)) }
      have hsupp : SupportedOn μ₀ (IsPrevNice n u (n : ℝ)) := by
        intro S _ hw
        have hEq : S = grid n := by
          by_contra hne; simp [μ₀, hne] at hw
        exact hEq ▸ isPrevNice_grid hu hn
      have hspread : IsSpread n ((1 + u⁻¹ ^ 36) * (n : ℝ) / (n : ℝ)) μ₀ := by
        intro T _
        have hn_pos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn
        have hge1 : (1 : ℝ) ≤ (1 + u⁻¹ ^ 36) * (n : ℝ) / (n : ℝ) := by
          rw [mul_div_cancel_right₀ _ hn_pos.ne']
          linarith [pow_nonneg (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ u)) 36]
        exact (μ₀.prob_le_one _).trans (one_le_pow₀ hge1)
      exact induction_step_core hu hn hm₀_hi le_rfl μ₀ hsupp hspread
    | succ t ih =>
      intro u hu hn hle
      by_cases hbase : (n : ℝ) ≤ u ^ 36
      · let μ₀ : Dist (grid n) :=
          { w := fun S => if S = grid n then 1 else 0
            nonneg := fun S => by split_ifs <;> norm_num
            sum_eq := by
              rw [Finset.sum_eq_single (grid n)]
              · simp
              · intro S _ hne; simp [hne]
              · intro hnot; exact False.elim (hnot (Finset.mem_powerset.mpr Subset.rfl)) }
        have hsupp : SupportedOn μ₀ (IsPrevNice n u (n : ℝ)) := by
          intro S _ hw
          have hEq : S = grid n := by
            by_contra hne; simp [μ₀, hne] at hw
          exact hEq ▸ isPrevNice_grid hu hn
        have hspread : IsSpread n ((1 + u⁻¹ ^ 36) * (n : ℝ) / (n : ℝ)) μ₀ := by
          intro T _
          have hn_pos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn
          have hge1 : (1 : ℝ) ≤ (1 + u⁻¹ ^ 36) * (n : ℝ) / (n : ℝ) := by
            rw [mul_div_cancel_right₀ _ hn_pos.ne']
            linarith [pow_nonneg (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ u)) 36]
          exact (μ₀.prob_le_one _).trans (one_le_pow₀ hge1)
        exact induction_step_core hu hn hbase le_rfl μ₀ hsupp hspread
      · push Not at hbase
        have hu3 : 1000 ≤ u ^ 3 := by
          have : (1000 : ℝ) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
          linarith
        have hu3_12 : (u ^ 3) ^ 12 ≤ (n : ℝ) := by
          have : (u ^ 3) ^ 12 = u ^ 36 := by ring
          linarith
        have hle' : (n : ℝ) ≤ ((u ^ 3) ^ (3 ^ t)) ^ 12 := by
          have : ((u ^ 3) ^ (3 ^ t)) ^ 12 = (u ^ (3 ^ (t + 1))) ^ 12 := by
            congr 1; rw [← pow_mul, ← pow_succ']
          rwa [this]
        obtain ⟨μ₀, hsupp₀, hspread₀⟩ := ih (u ^ 3) hu3 hu3_12 hle'
        have hsupp' : SupportedOn μ₀ (IsPrevNice n u (u ^ 36)) :=
          fun S hS hw => isPrevNice_of_isNice_cube hu (hsupp₀ S hS hw)
        have hspread' : IsSpread n ((1 + u⁻¹ ^ 36) * u ^ 36 / (n : ℝ)) μ₀ := by
          intro T hT
          have heq : ((u ^ 3) ^ 12 + 1) / (n : ℝ) = (1 + u⁻¹ ^ 36) * u ^ 36 / (n : ℝ) := by
            have hu0 : u ≠ 0 := by linarith
            field_simp [hu0]
          rw [← heq]
          exact hspread₀ T hT
        have hm_lo : u ^ 12 ≤ u ^ 36 := by
          have : (1 : ℝ) ≤ u ^ 24 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ u)
          nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ u) 12, show u ^ 36 = u ^ 12 * u ^ 24 by ring]
        exact induction_step_core hu hm_lo le_rfl hbase.le μ₀ hsupp' hspread'
  have hex_t : (n : ℝ) ≤ (u ^ (3 ^ n)) ^ 12 := by
    have h1 : (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
    have h2 : (2 : ℝ) ^ n ≤ u ^ n := pow_le_pow_left₀ (by norm_num) (by linarith) n
    have h3 : n ≤ 3 ^ n := (Nat.lt_pow_self (by norm_num : 1 < 3)).le
    have h4 : u ^ n ≤ u ^ (3 ^ n) := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ u) h3
    have h5 : u ^ (3 ^ n) ≤ (u ^ (3 ^ n)) ^ 12 :=
      le_self_pow₀ (one_le_pow₀ (by linarith : (1 : ℝ) ≤ u)) (by omega)
    exact h1.trans (h2.trans (h4.trans h5))
  exact hstep n u hu hn hex_t

/-- Helper for Lemma 4.3: probability that a Type 3 pair `(A, B)` violates Ore--Ryser is `< 1/2`. -/
private lemma type3_fail_prob_lt_half {n k : ℕ} {u : ℝ}
    (hk : 10 ^ 36 ≤ k) (hkn : 10 * k ≤ 9 * n) (hu0 : 0 ≤ u) (hu12 : u ^ 12 = (201 / 200 : ℝ) * (k : ℝ))
    (μ : Dist (grid n)) (hsupp : SupportedOn μ (IsNice n u))
    (hspread : IsSpread n ((u ^ 12 + 1) / (n : ℝ)) μ) :
    μ.prob (fun S => ∃ A ∈ (range n).powerset, ∃ B ∈ (range n).powerset,
      B.card < A.card ∧ A.card ≤ 2 * B.card ∧ 10 * B.card ≤ n ∧
      (S.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card + k * B.card < k * A.card) < 1 / 2 := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn_ge2 : 2 ≤ n := by omega
  have hu_ge : 1000 ≤ u := by
    by_contra hlt; push Not at hlt
    have hpow : u ^ 12 < (1000 : ℝ) ^ 12 := pow_lt_pow_left₀ hlt hu0 (by omega)
    have : (10 ^ 36 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hdeg_lo : ∀ S, IsNice n u S → ∀ x ∈ range n, ((1 + 1 / 200 : ℝ) * (1 - 1 / 800) * (k : ℝ)) ≤ (degL S x : ℝ) := by
    intro S hS x hx
    let Lx := (grid n).filter (fun p => p.1 = x)
    have hLx_mem : Lx ∈ allLines n := vertLine_mem hn_ge2 hx
    have hLx_card : Lx.card = n := by
      have hEq : Lx = (range n).image (fun y => (x, y)) := by
        ext ⟨a, b⟩; simp only [Lx, grid, Finset.mem_filter, Finset.mem_product, Finset.mem_image]
        exact ⟨fun ⟨⟨_, hb⟩, ha⟩ => ⟨b, hb, Prod.ext ha.symm rfl⟩,
          fun ⟨b, hb, heq⟩ => by cases heq; exact ⟨⟨hx, hb⟩, rfl⟩⟩
      rw [hEq, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h), Finset.card_range]
    have hbig : (u ^ 8)⁻¹ * (n : ℝ) < (Lx.card : ℝ) := by
      rw [hLx_card]
      have : (u ^ 8)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by
        have : (1000 : ℝ) ^ 8 ≤ u ^ 8 := pow_le_pow_left₀ (by norm_num) hu_ge 8
        linarith)
      nlinarith
    have hlo := (hS.2.1 Lx hLx_mem hbig).1
    rw [hLx_card, div_self hn_pos.ne', mul_one, hu12] at hlo
    have hEq : S ∩ Lx = S.filter (fun p => p.1 = x) := by
      ext p; simp only [Lx, Finset.mem_inter, Finset.mem_filter]
      exact ⟨fun ⟨hpS, _, hpx⟩ => ⟨hpS, hpx⟩, fun ⟨hpS, hpx⟩ => ⟨hpS, hS.1 hpS, hpx⟩⟩
    rw [hEq] at hlo
    have huinv : u⁻¹ ≤ 1 / 800 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc (1 + 1 / 200 : ℝ) * (1 - 1 / 800) * (k : ℝ)
        = (1 - 1 / 800) * ((201 / 200 : ℝ) * (k : ℝ)) := by ring
      _ ≤ (1 - u⁻¹) * ((201 / 200 : ℝ) * (k : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (degL S x : ℝ) := hlo
  -- For a Type 3 pair (A, B) with S nice, violation implies (S ∩ (A × B)).card ≥ k * B.card
  have hviol_dense : ∀ S, IsNice n u S → ∀ A ⊆ range n, ∀ B ⊆ range n,
      (S.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card + k * B.card < k * A.card →
      k * B.card ≤ (S ∩ (A ×ˢ B)).card := by
    intro S hS A hA B _ hviol
    have hpart : (S.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card +
        (S ∩ (A ×ˢ B)).card = (S.filter (fun p => p.1 ∈ A)).card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext p
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_inter, Finset.mem_product, Finset.mem_sdiff]
        constructor
        · rintro (⟨hpS, hpA, _⟩ | ⟨hpS, hpA, _⟩) <;> exact ⟨hpS, hpA⟩
        · rintro ⟨hpS, hpA⟩
          by_cases hpB : p.2 ∈ B
          · exact Or.inr ⟨hpS, hpA, hpB⟩
          · exact Or.inl ⟨hpS, hpA, (Finset.mem_product.mp (hS.1 hpS)).2, hpB⟩
      · rw [Finset.disjoint_left]
        intro p hp1 hp2
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp1).2.2).2 (Finset.mem_product.mp (Finset.mem_inter.mp hp2).2).2
    have hsumA : ((k * A.card : ℕ) : ℝ) ≤ ((S.filter (fun p => p.1 ∈ A)).card : ℝ) := by
      rw [card_filter_prod_eq_sum_degL A, Nat.cast_sum, Nat.cast_mul]
      calc (k : ℝ) * (A.card : ℝ) = ∑ _x ∈ A, (k : ℝ) := by simp [mul_comm]
        _ ≤ ∑ x ∈ A, (degL S x : ℝ) := Finset.sum_le_sum fun x hx => by
            have h1 := hdeg_lo S hS x (hA hx)
            nlinarith
    have hsumA_nat : k * A.card ≤ (S.filter (fun p => p.1 ∈ A)).card := by exact_mod_cast hsumA
    omega
  -- Union bound over b ∈ Icc 1 (n / 10)
  let Bset : ℕ → Finset (Finset ℕ × Finset ℕ) := fun b =>
    ((range n).powerset.filter (fun A => b < A.card ∧ A.card ≤ 2 * b)) ×ˢ
    ((range n).powersetCard b)
  have hle_b : μ.prob (fun S => ∃ A ∈ (range n).powerset, ∃ B ∈ (range n).powerset,
      B.card < A.card ∧ A.card ≤ 2 * B.card ∧ 10 * B.card ≤ n ∧
      (S.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card + k * B.card < k * A.card) ≤
      ∑ b ∈ Finset.Icc 1 (n / 10),
        μ.prob (fun S => ∃ AB ∈ Bset b, k * b ≤ (S ∩ (AB.1 ×ˢ AB.2)).card) := by
    have hsub : μ.prob (fun S => ∃ A ∈ (range n).powerset, ∃ B ∈ (range n).powerset,
        B.card < A.card ∧ A.card ≤ 2 * B.card ∧ 10 * B.card ≤ n ∧
        (S.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card + k * B.card < k * A.card) ≤
        μ.prob (fun S => ∃ b ∈ Finset.Icc 1 (n / 10),
          ∃ AB ∈ Bset b, k * b ≤ (S ∩ (AB.1 ×ˢ AB.2)).card) := by
      unfold Dist.prob
      refine Finset.sum_le_sum fun S hS => ?_
      by_cases hw : 0 < μ.w S
      · have hSnice := hsupp S (Finset.mem_powerset.mp hS) hw
        by_cases hbad : ∃ A ∈ (range n).powerset, ∃ B ∈ (range n).powerset,
            B.card < A.card ∧ A.card ≤ 2 * B.card ∧ 10 * B.card ≤ n ∧
            (S.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card + k * B.card < k * A.card
        · rcases hbad with ⟨A, hA, B, hB, hlt, hle2, h10, hviol⟩
          have hb1 : 1 ≤ B.card := by omega
          have hbn : B.card ≤ n / 10 := by omega
          have hdense := hviol_dense S hSnice A (Finset.mem_powerset.mp hA)
            B (Finset.mem_powerset.mp hB) hviol
          have hex : ∃ b ∈ Finset.Icc 1 (n / 10), ∃ AB ∈ Bset b,
              k * b ≤ (S ∩ (AB.1 ×ˢ AB.2)).card :=
            ⟨B.card, Finset.mem_Icc.mpr ⟨hb1, hbn⟩, (A, B),
              Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hA, hlt, hle2⟩,
                Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hB, rfl⟩⟩, hdense⟩
          rw [if_pos hex]
          split_ifs <;> [exact le_rfl; exact μ.nonneg S]
        · simp only [if_neg hbad]; split_ifs <;> [exact μ.nonneg S; exact le_rfl]
      · have hw0 : μ.w S = 0 := le_antisymm (le_of_not_gt hw) (μ.nonneg S)
        simp [hw0]
    exact hsub.trans (μ.prob_exists_le (Finset.Icc 1 (n / 10)) _)
  -- Bound each b ∈ Icc 1 (n / 10) by (1/4)^b
  have hterm_b : ∀ b ∈ Finset.Icc 1 (n / 10),
      μ.prob (fun S => ∃ AB ∈ Bset b, k * b ≤ (S ∩ (AB.1 ×ˢ AB.2)).card) ≤ ((1 : ℝ) / 4) ^ b := by
    intro b hb
    obtain ⟨hb1, hbn⟩ := Finset.mem_Icc.mp hb
    have hb_pos : (0 : ℝ) < b := Nat.cast_pos.mpr (by omega)
    have h10b : 10 * (b : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 10 * b ≤ n by omega)
    -- Bound each AB ∈ Bset b by (6 * b / n)^(k * b)
    have hAB_prob : ∀ AB ∈ Bset b,
        μ.prob (fun S => k * b ≤ (S ∩ (AB.1 ×ˢ AB.2)).card) ≤
          (6 * (b : ℝ) / (n : ℝ)) ^ (k * b) := by
      intro AB hAB
      obtain ⟨hA_mem, hB_mem⟩ := Finset.mem_product.mp hAB
      obtain ⟨hAp, hAlt, hAle2⟩ := Finset.mem_filter.mp hA_mem
      obtain ⟨hBsub, hBcard⟩ := Finset.mem_powersetCard.mp hB_mem
      have hAsub : AB.1 ⊆ range n := Finset.mem_powerset.mp hAp
      have hPsub : AB.1 ×ˢ AB.2 ⊆ grid n := Finset.product_subset_product hAsub hBsub
      have himp : ∀ S ∈ (grid n).powerset, k * b ≤ (S ∩ (AB.1 ×ˢ AB.2)).card →
          ∃ E ∈ (AB.1 ×ˢ AB.2).powersetCard (k * b), E ⊆ S := by
        intro S _ hcard
        obtain ⟨E, hES, hEcard⟩ := Finset.exists_subset_card_eq hcard
        exact ⟨E, Finset.mem_powersetCard.mpr ⟨hES.trans Finset.inter_subset_right, hEcard⟩,
          hES.trans Finset.inter_subset_left⟩
      have h1 : μ.prob (fun S => k * b ≤ (S ∩ (AB.1 ×ˢ AB.2)).card) ≤
          (((AB.1.card * b).choose (k * b) : ℕ) : ℝ) * ((u ^ 12 + 1) / (n : ℝ)) ^ (k * b) := by
        calc μ.prob (fun S => k * b ≤ (S ∩ (AB.1 ×ˢ AB.2)).card)
            ≤ μ.prob (fun S => ∃ E ∈ (AB.1 ×ˢ AB.2).powersetCard (k * b), E ⊆ S) := μ.prob_mono himp
          _ ≤ ∑ E ∈ (AB.1 ×ˢ AB.2).powersetCard (k * b), μ.prob (fun S => E ⊆ S) :=
              μ.prob_exists_le _ _
          _ ≤ ∑ _E ∈ (AB.1 ×ˢ AB.2).powersetCard (k * b), ((u ^ 12 + 1) / (n : ℝ)) ^ (k * b) := by
              refine Finset.sum_le_sum fun E hE => ?_
              obtain ⟨hEP, hEcard⟩ := Finset.mem_powersetCard.mp hE
              simpa [hEcard] using hspread E (hEP.trans hPsub)
          _ = (((AB.1.card * b).choose (k * b) : ℕ) : ℝ) * ((u ^ 12 + 1) / (n : ℝ)) ^ (k * b) := by
              simp [Finset.card_powersetCard, Finset.card_product, hBcard]
      have hch := choose_le_exp_pow (AB.1.card * b) (k * b) (by positivity)
      have hbase : Real.exp 1 * ((AB.1.card * b : ℕ) : ℝ) / ((k * b : ℕ) : ℝ) *
          ((u ^ 12 + 1) / (n : ℝ)) ≤ 6 * (b : ℝ) / (n : ℝ) := by
        have hA2b : (AB.1.card : ℝ) ≤ 2 * (b : ℝ) := by exact_mod_cast hAle2
        have hu1 : u ^ 12 + 1 ≤ (101 / 100 : ℝ) * (k : ℝ) := by
          rw [hu12]
          have : (200 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 200 ≤ k by omega)
          linarith
        have he_le : Real.exp 1 ≤ 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num) |> le_of_lt
        have halg : Real.exp 1 * ((AB.1.card * b : ℕ) : ℝ) / ((k * b : ℕ) : ℝ) *
            ((u ^ 12 + 1) / (n : ℝ)) =
            (Real.exp 1 * (AB.1.card : ℝ) * ((u ^ 12 + 1) / (k : ℝ))) / (n : ℝ) := by
          push_cast; field_simp [hk_pos.ne', hb_pos.ne', hn_pos.ne']
        rw [halg]
        apply div_le_div_of_nonneg_right _ hn_pos.le
        have hrat : (u ^ 12 + 1) / (k : ℝ) ≤ 101 / 100 := (div_le_iff₀ hk_pos).mpr hu1
        have h1 : Real.exp 1 * (AB.1.card : ℝ) * ((u ^ 12 + 1) / (k : ℝ)) ≤
            2.72 * (2 * (b : ℝ)) * (101 / 100) := by
          have h1a := mul_le_mul he_le hA2b (Nat.cast_nonneg _) (by norm_num)
          exact mul_le_mul h1a hrat (by positivity) (by positivity)
        linarith
      calc μ.prob (fun S => k * b ≤ (S ∩ (AB.1 ×ˢ AB.2)).card)
          ≤ (Real.exp 1 * ((AB.1.card * b : ℕ) : ℝ) / ((k * b : ℕ) : ℝ)) ^ (k * b) *
              ((u ^ 12 + 1) / (n : ℝ)) ^ (k * b) :=
            h1.trans (mul_le_mul_of_nonneg_right hch (by positivity))
        _ = (Real.exp 1 * ((AB.1.card * b : ℕ) : ℝ) / ((k * b : ℕ) : ℝ) *
              ((u ^ 12 + 1) / (n : ℝ))) ^ (k * b) := (mul_pow _ _ _).symm
        _ ≤ (6 * (b : ℝ) / (n : ℝ)) ^ (k * b) := pow_le_pow_left₀ (by positivity) hbase (k * b)
    -- Bound (Bset b).card ≤ 2^b * (e * n / b)^(3 * b)
    have hBset_card : ((Bset b).card : ℝ) ≤ (2 : ℝ) ^ b * (Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ (3 * b) := by
      have hcardA : (((range n).powerset.filter (fun A => b < A.card ∧ A.card ≤ 2 * b)).card : ℝ) ≤
          (2 : ℝ) ^ b * (Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ (2 * b) := by
        have hpart : ((range n).powerset.filter (fun A => b < A.card ∧ A.card ≤ 2 * b)).card ≤
            ∑ a ∈ Finset.Icc (b + 1) (2 * b), n.choose a := by
          have hsub : (range n).powerset.filter (fun A => b < A.card ∧ A.card ≤ 2 * b) ⊆
              (Finset.Icc (b + 1) (2 * b)).biUnion (fun a => (range n).powersetCard a) := by
            intro A hA
            obtain ⟨hAp, h1, h2⟩ := Finset.mem_filter.mp hA
            exact Finset.mem_biUnion.mpr ⟨A.card, Finset.mem_Icc.mpr ⟨by omega, h2⟩,
              Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hAp, rfl⟩⟩
          calc ((range n).powerset.filter (fun A => b < A.card ∧ A.card ≤ 2 * b)).card
              ≤ ((Finset.Icc (b + 1) (2 * b)).biUnion (fun a => (range n).powersetCard a)).card :=
                Finset.card_le_card hsub
            _ ≤ ∑ a ∈ Finset.Icc (b + 1) (2 * b), ((range n).powersetCard a).card :=
                Finset.card_biUnion_le
            _ = ∑ a ∈ Finset.Icc (b + 1) (2 * b), n.choose a := by simp [Finset.card_powersetCard]
        have hpartR : (((range n).powerset.filter (fun A => b < A.card ∧ A.card ≤ 2 * b)).card : ℝ) ≤
            ∑ a ∈ Finset.Icc (b + 1) (2 * b), (n.choose a : ℝ) := by
          rw [← Nat.cast_sum]; exact_mod_cast hpart
        have hbase_ge1 : (1 : ℝ) ≤ Real.exp 1 * (n : ℝ) / (b : ℝ) := by
          rw [le_div_iff₀ hb_pos, one_mul]
          have : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          nlinarith
        have heach : ∀ a ∈ Finset.Icc (b + 1) (2 * b),
            (n.choose a : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ (2 * b) := by
          intro a ha
          obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
          have hch := choose_le_exp_pow n a (by omega)
          have h1 : Real.exp 1 * (n : ℝ) / (a : ℝ) ≤ Real.exp 1 * (n : ℝ) / (b : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) hb_pos (by exact_mod_cast (show b ≤ a by omega))
          calc (n.choose a : ℝ)
              ≤ (Real.exp 1 * (n : ℝ) / (a : ℝ)) ^ a := hch
            _ ≤ (Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ a := pow_le_pow_left₀ (by positivity) h1 a
            _ ≤ (Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ (2 * b) := pow_le_pow_right₀ hbase_ge1 ha2
        have hIcc_card : (Finset.Icc (b + 1) (2 * b)).card = b := by
          rw [Nat.card_Icc]; omega
        have hb_le_2b : (b : ℝ) ≤ (2 : ℝ) ^ b := by
          exact_mod_cast (Nat.lt_two_pow_self (n := b)).le
        calc (((range n).powerset.filter (fun A => b < A.card ∧ A.card ≤ 2 * b)).card : ℝ)
            ≤ ∑ _a ∈ Finset.Icc (b + 1) (2 * b), (Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ (2 * b) :=
              hpartR.trans (Finset.sum_le_sum heach)
          _ = (b : ℝ) * (Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ (2 * b) := by
              rw [Finset.sum_const, hIcc_card, nsmul_eq_mul]
          _ ≤ (2 : ℝ) ^ b * (Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ (2 * b) :=
              mul_le_mul_of_nonneg_right hb_le_2b (by positivity)
      have hcardB : (((range n).powersetCard b).card : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ b := by
        rw [Finset.card_powersetCard, Finset.card_range]
        exact choose_le_exp_pow n b (by omega)
      have hprod : ((Bset b).card : ℝ) =
          (((range n).powerset.filter (fun A => b < A.card ∧ A.card ≤ 2 * b)).card : ℝ) *
          (((range n).powersetCard b).card : ℝ) := by
        dsimp [Bset]; rw [Finset.card_product, Nat.cast_mul]
      rw [hprod]
      calc _ ≤ ((2 : ℝ) ^ b * (Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ (2 * b)) *
              (Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ b :=
            mul_le_mul hcardA hcardB (Nat.cast_nonneg _) (by positivity)
        _ = (2 : ℝ) ^ b * (Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ (3 * b) := by
            rw [mul_assoc, ← pow_add, show 2 * b + b = 3 * b by ring]
    -- Combine
    have hfac : 2 * (6 * Real.exp 1) ^ 3 * (6 / 10 : ℝ) ^ (k - 3) ≤ 1 / 4 := by
      have hk30 : 30 ≤ k - 3 := by omega
      have hpow30 : (6 / 10 : ℝ) ^ (k - 3) ≤ (6 / 10 : ℝ) ^ 30 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hk30
      have he3 : (6 * Real.exp 1) ^ 3 ≤ (6 * (2.72 : ℝ)) ^ 3 :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left
          (lt_trans Real.exp_one_lt_d9 (by norm_num)).le (by norm_num)) 3
      calc 2 * (6 * Real.exp 1) ^ 3 * (6 / 10 : ℝ) ^ (k - 3)
          ≤ 2 * (6 * (2.72 : ℝ)) ^ 3 * (6 / 10 : ℝ) ^ 30 :=
            mul_le_mul (mul_le_mul_of_nonneg_left he3 (by norm_num)) hpow30 (by positivity) (by positivity)
        _ ≤ 1 / 4 := by norm_num
    have hbn_ratio : 6 * (b : ℝ) / (n : ℝ) ≤ 6 / 10 := by
      rw [div_le_div_iff₀ hn_pos (by norm_num : (0 : ℝ) < 10)]
      linarith
    have halg : (2 : ℝ) ^ b * (Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ (3 * b) *
        (6 * (b : ℝ) / (n : ℝ)) ^ (k * b) =
        (2 * (6 * Real.exp 1) ^ 3 * (6 * (b : ℝ) / (n : ℝ)) ^ (k - 3)) ^ b := by
      have hk3 : k * b = 3 * b + (k - 3) * b := by
        rw [← Nat.add_mul, Nat.add_sub_of_le (by omega : 3 ≤ k)]
      rw [hk3, pow_add]
      have hcancel : (Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ (3 * b) * (6 * (b : ℝ) / (n : ℝ)) ^ (3 * b) =
          ((6 * Real.exp 1) ^ 3) ^ b := by
        rw [← mul_pow, show Real.exp 1 * (n : ℝ) / (b : ℝ) * (6 * (b : ℝ) / (n : ℝ)) =
          6 * Real.exp 1 by field_simp [hb_pos.ne', hn_pos.ne'], pow_mul]
      calc (2 : ℝ) ^ b * (Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ (3 * b) *
            ((6 * (b : ℝ) / (n : ℝ)) ^ (3 * b) * (6 * (b : ℝ) / (n : ℝ)) ^ ((k - 3) * b))
          = (2 : ℝ) ^ b * ((Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ (3 * b) *
              (6 * (b : ℝ) / (n : ℝ)) ^ (3 * b)) * ((6 * (b : ℝ) / (n : ℝ)) ^ (k - 3)) ^ b := by
            rw [pow_mul]; ring
        _ = (2 : ℝ) ^ b * ((6 * Real.exp 1) ^ 3) ^ b * ((6 * (b : ℝ) / (n : ℝ)) ^ (k - 3)) ^ b := by
            rw [hcancel]
        _ = (2 * (6 * Real.exp 1) ^ 3 * (6 * (b : ℝ) / (n : ℝ)) ^ (k - 3)) ^ b := by
            rw [← mul_pow, ← mul_pow]
    calc μ.prob (fun S => ∃ AB ∈ Bset b, k * b ≤ (S ∩ (AB.1 ×ˢ AB.2)).card)
        ≤ ∑ AB ∈ Bset b, μ.prob (fun S => k * b ≤ (S ∩ (AB.1 ×ˢ AB.2)).card) :=
          μ.prob_exists_le (Bset b) _
      _ ≤ ∑ _AB ∈ Bset b, (6 * (b : ℝ) / (n : ℝ)) ^ (k * b) := Finset.sum_le_sum hAB_prob
      _ = ((Bset b).card : ℝ) * (6 * (b : ℝ) / (n : ℝ)) ^ (k * b) := by simp
      _ ≤ ((2 : ℝ) ^ b * (Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ (3 * b)) *
            (6 * (b : ℝ) / (n : ℝ)) ^ (k * b) :=
          mul_le_mul_of_nonneg_right hBset_card (by positivity)
      _ = (2 * (6 * Real.exp 1) ^ 3 * (6 * (b : ℝ) / (n : ℝ)) ^ (k - 3)) ^ b := halg
      _ ≤ (2 * (6 * Real.exp 1) ^ 3 * (6 / 10 : ℝ) ^ (k - 3)) ^ b :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hbn_ratio (k - 3)) (by positivity)) b
      _ ≤ ((1 : ℝ) / 4) ^ b := pow_le_pow_left₀ (by positivity) hfac b
  exact (hle_b.trans (Finset.sum_le_sum hterm_b)).trans_lt (geom_sum_quarter_lt_half (n / 10))

/-- Transpose of a grid subset `(x, y) ↦ (y, x)` preserves `IsNice` and `IsSpread`. -/
private def swapSet (S : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) := S.image Prod.swap

private lemma swapSet_invol (S : Finset (ℕ × ℕ)) : swapSet (swapSet S) = S := by
  ext ⟨a, b⟩; simp [swapSet]

private lemma swapSet_card (S : Finset (ℕ × ℕ)) : (swapSet S).card = S.card :=
  Finset.card_image_of_injective S Prod.swap_injective

private lemma swapSet_grid (n : ℕ) : swapSet (grid n) = grid n := by
  ext ⟨a, b⟩; simp [swapSet, grid]

private lemma swapSet_allLines {n : ℕ} {L : Finset (ℕ × ℕ)} (hL : L ∈ allLines n) :
    swapSet L ∈ allLines n := by
  obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp hL
  obtain ⟨huvG, hne⟩ := Finset.mem_filter.mp huv
  obtain ⟨hu, hv⟩ := Finset.mem_product.mp huvG
  have heq : swapSet (lineThrough n u v) = lineThrough n u.swap v.swap := by
    ext ⟨a, b⟩
    simp only [swapSet, lineThrough, grid, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
      Prod.fst_swap, Prod.snd_swap]
    constructor
    · rintro ⟨⟨x, y⟩, ⟨⟨hx, hy⟩, hcol⟩, hsw⟩
      cases hsw
      exact ⟨⟨hy, hx⟩, by linarith⟩
    · rintro ⟨⟨ha, hb⟩, hcol⟩
      exact ⟨(b, a), ⟨⟨hb, ha⟩, by linarith⟩, rfl⟩
  rw [heq]
  refine Finset.mem_image.mpr ⟨(u.swap, v.swap), Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
  · exact Finset.mem_product.mpr
      ⟨by simpa [grid] using (Finset.mem_product.mp hu).symm,
       by simpa [grid] using (Finset.mem_product.mp hv).symm⟩
  · intro h; exact hne (Prod.swap_injective h)

private lemma swapSet_isNice {n : ℕ} {u : ℝ} {S : Finset (ℕ × ℕ)} (h : IsNice n u S) :
    IsNice n u (swapSet S) := by
  have hinter : ∀ A : Finset (ℕ × ℕ), (swapSet S ∩ A).card = (S ∩ swapSet A).card := by
    intro A
    have hEq : swapSet S ∩ A = swapSet (S ∩ swapSet A) := by
      ext ⟨a, b⟩; simp [swapSet]
    rw [hEq, swapSet_card]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← swapSet_grid n]; exact Finset.image_subset_image h.1
  · intro L hL hbig
    have hswL := swapSet_allLines hL
    rw [hinter L, ← swapSet_card L]
    exact h.2.1 (swapSet L) hswL (by rwa [swapSet_card])
  · intro L hL hlo hhi
    have hswL := swapSet_allLines hL
    rw [hinter L]
    exact h.2.2.1 (swapSet L) hswL (by rwa [swapSet_card]) (by rwa [swapSet_card])
  · intro L hL hle
    have hswL := swapSet_allLines hL
    rw [hinter L]
    exact h.2.2.2.1 (swapSet L) hswL (by rwa [swapSet_card])
  · intro I hI J hJ hIc hJc
    have hprod : swapSet (I ×ˢ J) = J ×ˢ I := by
      ext ⟨a, b⟩; simp [swapSet, and_comm]
    rw [hinter (I ×ˢ J), hprod]
    have hres := h.2.2.2.2 J hJ I hI hJc hIc
    simpa [mul_comm (I.card : ℝ) (J.card : ℝ), mul_assoc] using hres

/-- Lemma 4.3 + Theorem 1.2 (`relaxed-version`) of Grebennikov--Kwan:
for `10^36 ≤ k` and `10 * k ≤ 9 * n`, there exists a `k`-regular subset `S' ⊆ grid n` with
`|S' ∩ L| ≤ k * (|L| / n + 1 / 100)` for every line `L ∈ allLines n`. -/
theorem relaxed_version {n k : ℕ} (hk : 10 ^ 36 ≤ k) (hkn : 10 * k ≤ 9 * n) :
    ∃ S' : Finset (ℕ × ℕ), IsKRegular n k S' ∧
      ∀ L ∈ allLines n, ((S' ∩ L).card : ℝ) ≤ (k : ℝ) * ((L.card : ℝ) / (n : ℝ) + 1 / 100) := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn_ge2 : 2 ≤ n := by omega
  let u : ℝ := ((201 / 200 : ℝ) * (k : ℝ)) ^ ((1 : ℝ) / 12)
  have hu0 : 0 < u := Real.rpow_pos_of_pos (by positivity) _
  have hu12 : u ^ 12 = (201 / 200 : ℝ) * (k : ℝ) := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hu_ge : 1000 ≤ u := by
    by_contra hlt; push Not at hlt
    have hpow : u ^ 12 < (1000 : ℝ) ^ 12 := pow_lt_pow_left₀ hlt hu0.le (by omega)
    have : (10 ^ 36 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hu12_le_n : u ^ 12 ≤ (n : ℝ) := by
    rw [hu12]
    have : (10 : ℝ) * (k : ℝ) ≤ 9 * (n : ℝ) := by exact_mod_cast hkn
    linarith
  obtain ⟨μ, hsupp, hspread⟩ := iterated_nice_dist hu_ge hu12_le_n
  -- Define transposed distribution μT(S) = μ(swapSet S)
  let μT : Dist (grid n) :=
    { w := fun S => μ.w (swapSet S)
      nonneg := fun S => μ.nonneg (swapSet S)
      sum_eq := by
        rw [← μ.sum_eq]
        refine Finset.sum_bij (fun S _ => swapSet S) ?_ ?_ ?_ (fun _ _ => rfl)
        · intro S hS
          rw [Finset.mem_powerset, ← swapSet_grid n]
          exact Finset.image_subset_image (Finset.mem_powerset.mp hS)
        · intro S₁ _ S₂ _ heq
          have := congrArg swapSet heq
          simpa [swapSet_invol] using this
        · intro S hS
          refine ⟨swapSet S, ?_, swapSet_invol S⟩
          rw [Finset.mem_powerset, ← swapSet_grid n]
          exact Finset.image_subset_image (Finset.mem_powerset.mp hS) }
  have hμT_prob : ∀ P : Finset (ℕ × ℕ) → Prop,
      μT.prob P = μ.prob (fun S => P (swapSet S)) := by
    intro P
    unfold Dist.prob
    dsimp only [μT]
    refine Finset.sum_bij (fun S _ => swapSet S) ?_ ?_ ?_ ?_
    · intro S hS
      rw [Finset.mem_powerset, ← swapSet_grid n]
      exact Finset.image_subset_image (Finset.mem_powerset.mp hS)
    · intro S₁ _ S₂ _ heq
      have := congrArg swapSet heq
      simpa [swapSet_invol] using this
    · intro S hS
      refine ⟨swapSet S, ?_, swapSet_invol S⟩
      rw [Finset.mem_powerset, ← swapSet_grid n]
      exact Finset.image_subset_image (Finset.mem_powerset.mp hS)
    · intro S _; by_cases hP : P S
      · simp only [if_pos hP, swapSet_invol]
      · simp only [if_neg hP, swapSet_invol]
  have hsuppT : SupportedOn μT (IsNice n u) := by
    intro S hS hw
    have hswS : swapSet S ⊆ grid n := by
      rw [← swapSet_grid n]; exact Finset.image_subset_image hS
    have hnice := hsupp (swapSet S) hswS hw
    simpa [swapSet_invol] using swapSet_isNice hnice
  have hspreadT : IsSpread n ((u ^ 12 + 1) / (n : ℝ)) μT := by
    intro T hT
    rw [hμT_prob]
    have hcongr : μ.prob (fun S => T ⊆ swapSet S) = μ.prob (fun S => swapSet T ⊆ S) := by
      refine μ.prob_congr fun S _ => ?_
      constructor <;> intro h x hx
      · obtain ⟨y, hyT, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨z, hzS, hzy⟩ := Finset.mem_image.mp (h hyT)
        have : z = y.swap := by
          have := congrArg Prod.swap hzy; simpa using this
        exact this ▸ hzS
      · have hsw : x.swap ∈ swapSet T := Finset.mem_image.mpr ⟨x, hx, rfl⟩
        exact Finset.mem_image.mpr ⟨x.swap, h hsw, by simp⟩
    rw [hcongr, ← swapSet_card T]
    exact hspread (swapSet T) (by rw [← swapSet_grid n]; exact Finset.image_subset_image hT)
  -- Type 3 failure probability < 1/2
  let Bad3 : Finset (ℕ × ℕ) → Prop := fun S =>
    ∃ A ∈ (range n).powerset, ∃ B ∈ (range n).powerset,
      B.card < A.card ∧ A.card ≤ 2 * B.card ∧ 10 * B.card ≤ n ∧
      (S.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card + k * B.card < k * A.card
  have hBad3 : μ.prob Bad3 < 1 / 2 := type3_fail_prob_lt_half hk hkn hu0.le hu12 μ hsupp hspread
  have hBad3T : μ.prob (fun S => Bad3 (swapSet S)) < 1 / 2 := by
    rw [← hμT_prob]
    exact type3_fail_prob_lt_half hk hkn hu0.le hu12 μT hsuppT hspreadT
  have hgood_pos : 0 < μ.prob (fun S => ¬ (Bad3 S ∨ Bad3 (swapSet S))) := by
    rw [μ.prob_compl]
    have := μ.prob_or_le Bad3 (fun S => Bad3 (swapSet S))
    linarith
  obtain ⟨S, hSgrid, hSw, hSgood⟩ := μ.exists_of_prob_pos hgood_pos
  have hSnice : IsNice n u S := hsupp S hSgrid hSw
  rw [not_or] at hSgood
  obtain ⟨hnot3, hnot3T⟩ := hSgood
  -- Verify Ore--Ryser condition for S across all 7 types
  have hOR_types : ∀ (S₀ : Finset (ℕ × ℕ)), IsNice n u S₀ → ¬ Bad3 S₀ →
      ∀ A ⊆ range n, ∀ B ⊆ range n, B.card < A.card → 2 * B.card ≤ n →
        k * A.card ≤ (S₀.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card + k * B.card := by
    intro S₀ hS₀nice hS₀not3 A hA B hB hBA hBhalf
    have hdeg_bounds : ∀ x ∈ range n,
        (1 - 1 / 800) * ((201 / 200 : ℝ) * (k : ℝ)) ≤ (degL S₀ x : ℝ) ∧
        (degL S₀ x : ℝ) ≤ (1 + 1 / 800) * ((201 / 200 : ℝ) * (k : ℝ)) := by
      intro x hx
      let Lx := (grid n).filter (fun p => p.1 = x)
      have hLx_mem : Lx ∈ allLines n := vertLine_mem hn_ge2 hx
      have hLx_card : Lx.card = n := by
        have hEq : Lx = (range n).image (fun y => (x, y)) := by
          ext ⟨a, b⟩; simp only [Lx, grid, Finset.mem_filter, Finset.mem_product, Finset.mem_image]
          exact ⟨fun ⟨⟨_, hb⟩, ha⟩ => ⟨b, hb, Prod.ext ha.symm rfl⟩,
            fun ⟨b, hb, heq⟩ => by cases heq; exact ⟨⟨hx, hb⟩, rfl⟩⟩
        rw [hEq, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h), Finset.card_range]
      have hbig : (u ^ 8)⁻¹ * (n : ℝ) < (Lx.card : ℝ) := by
        rw [hLx_card]
        have : (u ^ 8)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by
          have : (1000 : ℝ) ^ 8 ≤ u ^ 8 := pow_le_pow_left₀ (by norm_num) hu_ge 8
          linarith)
        nlinarith
      obtain ⟨hlo, hhi⟩ := hS₀nice.2.1 Lx hLx_mem hbig
      rw [hLx_card, div_self hn_pos.ne', mul_one, hu12] at hlo hhi
      have hEq : S₀ ∩ Lx = S₀.filter (fun p => p.1 = x) := by
        ext p; simp only [Lx, Finset.mem_inter, Finset.mem_filter]
        exact ⟨fun ⟨hpS, _, hpx⟩ => ⟨hpS, hpx⟩, fun ⟨hpS, hpx⟩ => ⟨hpS, hS₀nice.1 hpS, hpx⟩⟩
      rw [hEq] at hlo hhi
      have huinv : u⁻¹ ≤ 1 / 800 := by rw [inv_le_comm₀ hu0 (by norm_num)]; linarith
      exact ⟨(mul_le_mul_of_nonneg_right (by linarith) (by positivity)).trans hlo,
        hhi.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))⟩
    have hdegR_upper : ∀ y ∈ range n,
        (degR S₀ y : ℝ) ≤ (1 + 1 / 800) * ((201 / 200 : ℝ) * (k : ℝ)) := by
      intro y hy
      let Ly := (grid n).filter (fun p => p.2 = y)
      have hLy_mem : Ly ∈ allLines n := horizLine_mem hn_ge2 hy
      have hLy_card : Ly.card = n := by
        have hEq : Ly = (range n).image (fun x => (x, y)) := by
          ext ⟨a, b⟩; simp only [Ly, grid, Finset.mem_filter, Finset.mem_product, Finset.mem_image]
          exact ⟨fun ⟨⟨ha, _⟩, hb⟩ => ⟨a, ha, Prod.ext rfl hb.symm⟩,
            fun ⟨a, ha, heq⟩ => by cases heq; exact ⟨⟨ha, hy⟩, rfl⟩⟩
        rw [hEq, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h), Finset.card_range]
      have hbig : (u ^ 8)⁻¹ * (n : ℝ) < (Ly.card : ℝ) := by
        rw [hLy_card]
        have : (u ^ 8)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by
          have : (1000 : ℝ) ^ 8 ≤ u ^ 8 := pow_le_pow_left₀ (by norm_num) hu_ge 8
          linarith)
        nlinarith
      have hhi := (hS₀nice.2.1 Ly hLy_mem hbig).2
      rw [hLy_card, div_self hn_pos.ne', mul_one, hu12] at hhi
      have hEq : S₀ ∩ Ly = S₀.filter (fun p => p.2 = y) := by
        ext p; simp only [Ly, Finset.mem_inter, Finset.mem_filter]
        exact ⟨fun ⟨hpS, _, hpy⟩ => ⟨hpS, hpy⟩, fun ⟨hpS, hpy⟩ => ⟨hpS, hS₀nice.1 hpS, hpy⟩⟩
      rw [hEq] at hhi
      have huinv : u⁻¹ ≤ 1 / 800 := by rw [inv_le_comm₀ hu0 (by norm_num)]; linarith
      exact hhi.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    by_cases htype2 : (n : ℝ) / 10 ≤ (A.card : ℝ)
    · -- Type 2: |A| ≥ n/10 and |range n \ B| ≥ n/2 ≥ n/10
      have hBcomp_card : (range n \ B).card = n - B.card := by
        rw [Finset.card_sdiff_of_subset hB, Finset.card_range]
      have hBcomp_ge : (n : ℝ) / 10 ≤ ((range n \ B).card : ℝ) := by
        rw [hBcomp_card, Nat.cast_sub (by have := Finset.card_le_card hB; simp at this; omega)]
        have : 2 * (B.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hBhalf
        linarith
      have hqr := (hS₀nice.2.2.2.2 A hA (range n \ B) Finset.sdiff_subset htype2 hBcomp_ge).1
      have hEq : S₀ ∩ (A ×ˢ (range n \ B)) = S₀.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B) := by
        ext p; simp [Finset.mem_inter, Finset.mem_filter, Finset.mem_product]
      rw [hEq, hu12] at hqr
      have huinv : u⁻¹ ≤ 1 / 800 := by rw [inv_le_comm₀ hu0 (by norm_num)]; linarith
      have hprod1 : (1 : ℝ) ≤ (1 - u⁻¹) * (201 / 200) := by linarith
      have hA_le_n : (A.card : ℝ) ≤ (n : ℝ) := by
        have := Finset.card_le_card hA; simp at this; exact_mod_cast this
      have hB_le_n : B.card ≤ n := by have := Finset.card_le_card hB; simp at this; omega
      have h2 : (k : ℝ) * ((A.card : ℝ) - (B.card : ℝ)) ≤
          ((S₀.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card : ℝ) := by
        have hstep1 : (k : ℝ) * ((A.card : ℝ) - (B.card : ℝ)) ≤
            (k : ℝ) * (A.card : ℝ) * (((n : ℝ) - (B.card : ℝ)) / (n : ℝ)) := by
          have : (A.card : ℝ) - (B.card : ℝ) ≤ (A.card : ℝ) * (((n : ℝ) - (B.card : ℝ)) / (n : ℝ)) := by
            rw [← mul_div_assoc, le_div_iff₀ hn_pos]
            nlinarith [Nat.cast_nonneg (α := ℝ) B.card]
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left this hk_pos.le
        have hstep2 : (k : ℝ) * (A.card : ℝ) * (((n : ℝ) - (B.card : ℝ)) / (n : ℝ)) ≤
            (1 - u⁻¹) * (A.card : ℝ) * ((range n \ B).card : ℝ) * ((201 / 200 : ℝ) * (k : ℝ) / (n : ℝ)) := by
          rw [hBcomp_card, Nat.cast_sub hB_le_n]
          have hnn : 0 ≤ (A.card : ℝ) * ((n : ℝ) - (B.card : ℝ)) * (k : ℝ) / (n : ℝ) := by
            have : (B.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hB_le_n
            have : 0 ≤ (n : ℝ) - (B.card : ℝ) := by linarith
            positivity
          have hmul := mul_le_mul_of_nonneg_right hprod1 hnn
          have halg1 : (1 : ℝ) * ((A.card : ℝ) * ((n : ℝ) - (B.card : ℝ)) * (k : ℝ) / (n : ℝ)) =
              (k : ℝ) * (A.card : ℝ) * (((n : ℝ) - (B.card : ℝ)) / (n : ℝ)) := by ring
          have halg2 : (1 - u⁻¹) * (201 / 200 : ℝ) * ((A.card : ℝ) * ((n : ℝ) - (B.card : ℝ)) * (k : ℝ) / (n : ℝ)) =
              (1 - u⁻¹) * (A.card : ℝ) * ((n : ℝ) - (B.card : ℝ)) * ((201 / 200 : ℝ) * (k : ℝ) / (n : ℝ)) := by ring
          linarith
        exact hstep1.trans (hstep2.trans hqr)
      have hR : ((k * A.card : ℕ) : ℝ) ≤
          (((S₀.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card + k * B.card : ℕ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast hR
    · push Not at htype2
      by_cases htype1 : 2 * B.card < A.card
      · -- Type 1: |A| > 2 |B|
        have hpart : (S₀.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card +
            (S₀.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B)).card = (S₀.filter (fun p => p.1 ∈ A)).card := by
          rw [← Finset.card_union_of_disjoint]
          · congr 1; ext p
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
            constructor
            · rintro (⟨hpS, hpA, _⟩ | ⟨hpS, hpA, _⟩) <;> exact ⟨hpS, hpA⟩
            · rintro ⟨hpS, hpA⟩
              by_cases hpB : p.2 ∈ B
              · exact Or.inr ⟨hpS, hpA, hpB⟩
              · exact Or.inl ⟨hpS, hpA, (Finset.mem_product.mp (hS₀nice.1 hpS)).2, hpB⟩
          · rw [Finset.disjoint_left]
            intro p hp1 hp2
            exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp1).2.2).2 (Finset.mem_filter.mp hp2).2.2
        have hsumA : (A.card : ℝ) * ((1 - 1 / 800) * ((201 / 200 : ℝ) * (k : ℝ))) ≤
            ((S₀.filter (fun p => p.1 ∈ A)).card : ℝ) := by
          rw [card_filter_prod_eq_sum_degL A, Nat.cast_sum]
          calc (A.card : ℝ) * ((1 - 1 / 800) * ((201 / 200 : ℝ) * (k : ℝ)))
              = ∑ _x ∈ A, ((1 - 1 / 800) * ((201 / 200 : ℝ) * (k : ℝ))) := by simp
            _ ≤ ∑ x ∈ A, (degL S₀ x : ℝ) := Finset.sum_le_sum fun x hx => (hdeg_bounds x (hA hx)).1
        have hsumB : ((S₀.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B)).card : ℝ) ≤
            (B.card : ℝ) * ((1 + 1 / 800) * ((201 / 200 : ℝ) * (k : ℝ))) := by
          have hle : (S₀.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B)).card ≤
              (S₀.filter (fun p => p.2 ∈ B)).card :=
            Finset.card_le_card fun p hp => by simp only [Finset.mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.2⟩
          have hleR : ((S₀.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B)).card : ℝ) ≤
              ((S₀.filter (fun p => p.2 ∈ B)).card : ℝ) := by exact_mod_cast hle
          rw [card_filter_prod_eq_sum_degR B, Nat.cast_sum] at hleR
          calc ((S₀.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B)).card : ℝ)
              ≤ ∑ y ∈ B, (degR S₀ y : ℝ) := hleR
            _ ≤ ∑ _y ∈ B, ((1 + 1 / 800) * ((201 / 200 : ℝ) * (k : ℝ))) :=
                Finset.sum_le_sum fun y hy => hdegR_upper y (hB hy)
            _ = (B.card : ℝ) * ((1 + 1 / 800) * ((201 / 200 : ℝ) * (k : ℝ))) := by simp
        have hpartR : ((S₀.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card : ℝ) +
            ((S₀.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B)).card : ℝ) =
            ((S₀.filter (fun p => p.1 ∈ A)).card : ℝ) := by exact_mod_cast hpart
        have h2BA : 2 * (B.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast htype1.le
        have hR : ((k * A.card : ℕ) : ℝ) ≤
            (((S₀.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card + k * B.card : ℕ) : ℝ) := by
          push_cast; nlinarith
        exact_mod_cast hR
      · -- Type 3: |B| < |A| ≤ 2|B| and 10*|B| ≤ n
        push Not at htype1
        have h10B : 10 * B.card ≤ n := by
          have : (B.card : ℝ) < (n : ℝ) / 10 := lt_trans (by exact_mod_cast hBA) htype2
          have : (10 * B.card : ℝ) < (n : ℝ) := by linarith
          exact_mod_cast this.le
        by_contra hlt
        push Not at hlt
        exact hS₀not3 ⟨A, Finset.mem_powerset.mpr hA, B, Finset.mem_powerset.mpr hB,
          hBA, htype1, h10B, hlt⟩
  have hOR : ∀ A ⊆ range n, ∀ B ⊆ range n,
      k * A.card ≤ (S.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card + k * B.card := by
    intro A hA B hB
    by_cases h0 : A.card ≤ B.card
    · exact (Nat.mul_le_mul_left k h0).trans (Nat.le_add_left _ _)
    push Not at h0
    by_cases hBhalf : 2 * B.card ≤ n
    · exact hOR_types S hSnice hnot3 A hA B hB h0 hBhalf
    · -- Symmetric case (types 1*, 2*, 3*): apply to swapSet S with A' = range n \ B, B' = range n \ A
      push Not at hBhalf
      have hAcard_le : A.card ≤ n := by have := Finset.card_le_card hA; simp at this; omega
      have hBcard_le : B.card ≤ n := by have := Finset.card_le_card hB; simp at this; omega
      let A' := range n \ B
      let B' := range n \ A
      have hA'card : A'.card = n - B.card := by rw [Finset.card_sdiff_of_subset hB, Finset.card_range]
      have hB'card : B'.card = n - A.card := by rw [Finset.card_sdiff_of_subset hA, Finset.card_range]
      have hdual := hOR_types (swapSet S) (swapSet_isNice hSnice) hnot3T
        A' Finset.sdiff_subset B' Finset.sdiff_subset (by omega) (by omega)
      have hsw_eq : ((swapSet S).filter (fun p => p.1 ∈ A' ∧ p.2 ∈ range n \ B')).card =
          (S.filter (fun p => p.1 ∈ A ∧ p.2 ∈ range n \ B)).card := by
        have hB'comp : range n \ B' = A := by
          ext x; simp only [B', Finset.mem_sdiff]; exact ⟨fun ⟨_, h⟩ => by by_contra hx; exact h ⟨‹_›, hx⟩,
            fun hx => ⟨hA hx, fun h => h.2 hx⟩⟩
        rw [hB'comp]
        have hEq : (swapSet S).filter (fun p => p.1 ∈ A' ∧ p.2 ∈ A) =
            swapSet (S.filter (fun p => p.1 ∈ A ∧ p.2 ∈ A')) := by
          ext ⟨x, y⟩; simp [swapSet, and_comm]
        rw [hEq, swapSet_card]
      rw [hsw_eq, hA'card, hB'card] at hdual
      have hsub1 : k * n - k * B.card = k * (n - B.card) := (Nat.mul_sub_left_distrib k n B.card).symm
      have hsub2 : k * n - k * A.card = k * (n - A.card) := (Nat.mul_sub_left_distrib k n A.card).symm
      have hle1 : k * B.card ≤ k * n := Nat.mul_le_mul_left k hBcard_le
      have hle2 : k * A.card ≤ k * n := Nat.mul_le_mul_left k hAcard_le
      omega
  obtain ⟨S', hS'S, hS'reg⟩ := ore_ryser hSnice.1 hOR
  refine ⟨S', hS'reg, fun L hLall => ?_⟩
  have hleS : ((S' ∩ L).card : ℝ) ≤ ((S ∩ L).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_right hS'S)
  have huinv : u⁻¹ ≤ 1 / 1000 := by rw [inv_le_comm₀ hu0 (by norm_num)]; linarith
  by_cases hheavy : (u ^ 8)⁻¹ * (n : ℝ) < (L.card : ℝ)
  · have hhi := (hSnice.2.1 L hLall hheavy).2
    rw [hu12] at hhi
    have h1 : (1 + u⁻¹) * ((201 / 200 : ℝ) * (k : ℝ)) * ((L.card : ℝ) / (n : ℝ)) ≤
        (k : ℝ) * ((L.card : ℝ) / (n : ℝ) + 1 / 100) := by
      have hLn : (L.card : ℝ) / (n : ℝ) ≤ 1 := by
        rw [div_le_one hn_pos]; exact_mod_cast (line_card_bounds hLall).2
      have hLn0 : 0 ≤ (L.card : ℝ) / (n : ℝ) := by positivity
      have hcoef : (1 + u⁻¹) * (201 / 200 : ℝ) ≤ 1 + 1 / 100 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hk_pos.le hLn0)
      have halg : (1 + u⁻¹) * (201 / 200 : ℝ) * ((k : ℝ) * ((L.card : ℝ) / (n : ℝ))) =
          (1 + u⁻¹) * ((201 / 200 : ℝ) * (k : ℝ)) * ((L.card : ℝ) / (n : ℝ)) := by ring
      nlinarith
    exact hleS.trans (hhi.trans h1)
  · push Not at hheavy
    by_cases hmed : (u ^ 24)⁻¹ * (n : ℝ) < (L.card : ℝ)
    · have hhi := hSnice.2.2.1 L hLall hmed hheavy
      have hu4_le : (1 + u⁻¹) * u ^ 4 ≤ (k : ℝ) * (1 / 100) := by
        have h1 : u ^ 4 ≤ (1 / 200 : ℝ) * u ^ 12 := by
          have : (200 : ℝ) ≤ u ^ 8 := by
            have : (1000 : ℝ) ^ 8 ≤ u ^ 8 := pow_le_pow_left₀ (by norm_num) hu_ge 8
            linarith
          nlinarith [show u ^ 12 = u ^ 4 * u ^ 8 by ring, pow_nonneg hu0.le 4]
        rw [hu12] at h1
        nlinarith [pow_nonneg hu0.le 4]
      have hLn0 : 0 ≤ (L.card : ℝ) / (n : ℝ) := div_nonneg (Nat.cast_nonneg _) hn_pos.le
      exact hleS.trans (hhi.trans (hu4_le.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hLn0) hk_pos.le)))
    · push Not at hmed
      have hhi : ((S ∩ L).card : ℝ) ≤ 14 := by exact_mod_cast hSnice.2.2.2.1 L hLall hmed
      have hk14 : (14 : ℝ) ≤ (k : ℝ) * (1 / 100) := by
        have : (1400 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1400 ≤ k by omega)
        linarith
      have hLn0 : 0 ≤ (L.card : ℝ) / (n : ℝ) := div_nonneg (Nat.cast_nonneg _) hn_pos.le
      exact hleS.trans (hhi.trans (hk14.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hLn0) hk_pos.le)))

end NiceAndReg

/- ## Section 6: From the Relaxed Theorem to the Main Theorem -/

section MainReduction

private lemma disj_mono {α : Type*} {a b c d : Finset α}
    (ha : a ⊆ c) (hb : b ⊆ d) (h : Disjoint c d) : Disjoint a b :=
  Finset.disjoint_of_subset_left ha (Finset.disjoint_of_subset_right hb h)

/-- Any non-axis, non-diagonal integer line meets `[0, N)^2` in at most `(N + 1) / 2` points. -/
lemma line_card_le_half_of_not_diag {N : ℕ} {a b c : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hne1 : a ≠ b) (hne2 : a ≠ -b) :
    ((grid N).filter (fun p => a * p.1 + b * p.2 = c)).card ≤ (N + 1) / 2 := by
  let L := (grid N).filter (fun p => a * p.1 + b * p.2 = c)
  change L.card ≤ (N + 1) / 2
  by_cases hN0 : N = 0
  · subst hN0; simp [L, grid]
  by_cases hsmall : L.card ≤ 1
  · omega
  push Not at hsmall
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hsmall
  have hL_eq : L = lineThrough N p q := filter_linear_eq_lineThrough (Or.inl ha) hp hq hpq
  have hpG : p ∈ grid N := (Finset.mem_filter.mp hp).1
  have hqG : q ∈ grid N := (Finset.mem_filter.mp hq).1
  have hLall : L ∈ allLines N := by
    rw [hL_eq]
    exact Finset.mem_image.mpr ⟨(p, q), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hpG, hqG⟩, hpq⟩, rfl⟩
  obtain ⟨u, v, hu_nn, huv_ne, hparam, _, hcard_lt⟩ := line_card_le_of_step hLall hp hq hpq
  obtain ⟨t, ht1, ht2⟩ := hparam q hq
  have ht_ne : t ≠ 0 := by
    intro ht0
    rw [ht0, zero_mul] at ht1 ht2
    exact hpq (Prod.ext (by omega) (by omega))
  have hp_eq : a * (p.1 : ℤ) + b * (p.2 : ℤ) = c := (Finset.mem_filter.mp hp).2
  have hq_eq : a * (q.1 : ℤ) + b * (q.2 : ℤ) = c := (Finset.mem_filter.mp hq).2
  have huv_orth : a * u + b * v = 0 := by
    have hmul : t * (a * u + b * v) = 0 := by
      have hdiff : a * ((q.1 : ℤ) - p.1) + b * ((q.2 : ℤ) - p.2) = 0 := by linarith
      rw [ht1, ht2] at hdiff
      linarith
    exact (mul_eq_zero.mp hmul).resolve_left ht_ne
  have hM_ge2 : 2 ≤ max u.natAbs v.natAbs := by
    by_contra hlt
    push Not at hlt
    have hu_le : u.natAbs ≤ 1 := (le_max_left u.natAbs v.natAbs).trans (by omega)
    have hv_le : v.natAbs ≤ 1 := (le_max_right u.natAbs v.natAbs).trans (by omega)
    have hu_cases : u = 0 ∨ u = 1 := by omega
    have hv_cases : v = -1 ∨ v = 0 ∨ v = 1 := by omega
    rcases hu_cases with rfl | rfl
    · rcases hv_cases with rfl | rfl | rfl
      · simp at huv_orth; exact hb huv_orth
      · exact huv_ne.elim (fun h => h rfl) (fun h => h rfl)
      · simp at huv_orth; exact hb huv_orth
    · rcases hv_cases with rfl | rfl | rfl
      · exact hne1 (by linarith)
      · simp at huv_orth; exact ha huv_orth
      · exact hne2 (by linarith)
  have hM_pos : (0 : ℝ) < ((max u.natAbs v.natAbs : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hM_ge2R : (2 : ℝ) ≤ ((max u.natAbs v.natAbs : ℕ) : ℝ) := by exact_mod_cast hM_ge2
  have hdiv : (N : ℝ) / ((max u.natAbs v.natAbs : ℕ) : ℝ) ≤ (N : ℝ) / 2 :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by norm_num) hM_ge2R
  have hltR : (L.card : ℝ) < (N : ℝ) / 2 + 1 := lt_of_lt_of_le hcard_lt (by linarith)
  have h2R : ((2 * L.card : ℕ) : ℝ) < ((N + 2 : ℕ) : ℝ) := by push_cast; linarith
  have h2N : 2 * L.card < N + 2 := by exact_mod_cast h2R
  omega

/-- Explicit complement construction when `2 * N ≤ 3 * r` (KNS-25 Proposition 3.1). -/
lemma case_large_k {N r : ℕ} (hN : 3 ≤ N) (hrN : r ≤ N) (hlarge : 2 * N ≤ 3 * r) :
    ∃ S : Finset (ℕ × ℕ), IsKRegular N r S ∧
      ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 →
        (S.filter (fun p => a * p.1 + b * p.2 = c)).card ≤ r := by
  let d : ℕ := N - r
  have h3d : 3 * d ≤ N := by omega
  let m : ℕ := N - 2 * d
  have hm_pos : 0 < m := by omega
  have hdm : d ≤ m := by omega
  let rowIdx : ℕ → ℕ := fun i => if i < N - 3 * d then d + i else i + 2 * d
  have hrow_lt : ∀ i < m, rowIdx i < N := by
    intro i hi; dsimp [rowIdx]; split_ifs <;> omega
  have hrow_range : ∀ i < m, (d ≤ rowIdx i ∧ rowIdx i < N - 2 * d) ∨ (N - d ≤ rowIdx i ∧ rowIdx i < N) := by
    intro i hi; dsimp [rowIdx]; split_ifs
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have hrow_inj : ∀ i₁ < m, ∀ i₂ < m, rowIdx i₁ = rowIdx i₂ → i₁ = i₂ := by
    intro i₁ h1 i₂ h2 heq
    dsimp [rowIdx] at heq
    split_ifs at heq <;> omega
  have hrow_surj : ∀ y < N, ((d ≤ y ∧ y < N - 2 * d) ∨ (N - d ≤ y ∧ y < N)) →
      ∃ i < m, rowIdx i = y := by
    intro y hy hyc
    rcases hyc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨y - d, by omega, ?_⟩
      dsimp [rowIdx]; rw [if_pos (by omega)]; omega
    · refine ⟨y - 2 * d, by omega, ?_⟩
      dsimp [rowIdx]; rw [if_neg (by omega)]; omega
  let P₀ : Finset (ℕ × ℕ) := range d ×ˢ range d
  let P₁ : Finset (ℕ × ℕ) := Ico d (2 * d) ×ˢ Ico (N - 2 * d) (N - d)
  let P₂ : Finset (ℕ × ℕ) :=
    (range m ×ˢ range d).image (fun ij => (2 * d + ij.1, rowIdx ((ij.1 + ij.2) % m)))
  let P : Finset (ℕ × ℕ) := P₀ ∪ P₁ ∪ P₂
  have hP₀_sub : P₀ ⊆ grid N := by
    intro p hp; simp only [P₀, grid, Finset.mem_product, Finset.mem_range] at hp ⊢; omega
  have hP₁_sub : P₁ ⊆ grid N := by
    intro p hp; simp only [P₁, grid, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hp ⊢; omega
  have hP₂_sub : P₂ ⊆ grid N := by
    intro p hp
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hp
    simp only [Finset.mem_product, Finset.mem_range] at hij
    simp only [grid, Finset.mem_product, Finset.mem_range]
    exact ⟨by omega, hrow_lt _ (Nat.mod_lt _ hm_pos)⟩
  have hP_sub : P ⊆ grid N := Finset.union_subset (Finset.union_subset hP₀_sub hP₁_sub) hP₂_sub
  have hP₀_degL : ∀ x ∈ range N, degL P₀ x = if x < d then d else 0 := by
    intro x _
    unfold degL
    split_ifs with hx
    · have hEq : P₀.filter (fun p => p.1 = x) = (range d).image (fun y => (x, y)) := by
        ext ⟨a, b⟩; simp only [P₀, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image]
        exact ⟨fun ⟨⟨_, hb⟩, ha⟩ => ⟨b, hb, Prod.ext ha.symm rfl⟩,
          fun ⟨b, hb, heq⟩ => by cases heq; exact ⟨⟨hx, hb⟩, rfl⟩⟩
      rw [hEq, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h), Finset.card_range]
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p hp heq; simp only [P₀, Finset.mem_product, Finset.mem_range] at hp; omega
  have hP₁_degL : ∀ x ∈ range N, degL P₁ x = if d ≤ x ∧ x < 2 * d then d else 0 := by
    intro x _
    unfold degL
    split_ifs with hx
    · have hEq : P₁.filter (fun p => p.1 = x) = (Ico (N - 2 * d) (N - d)).image (fun y => (x, y)) := by
        ext ⟨a, b⟩; simp only [P₁, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_image]
        exact ⟨fun ⟨⟨_, hb⟩, ha⟩ => ⟨b, hb, Prod.ext ha.symm rfl⟩,
          fun ⟨b, hb, heq⟩ => by cases heq; exact ⟨⟨hx, hb⟩, rfl⟩⟩
      rw [hEq, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h), Nat.card_Ico]
      omega
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p hp heq; simp only [P₁, Finset.mem_product, Finset.mem_Ico] at hp; omega
  have hP₂_degL : ∀ x ∈ range N, degL P₂ x = if 2 * d ≤ x then d else 0 := by
    intro x hxN
    have hxlt : x < N := Finset.mem_range.mp hxN
    unfold degL
    split_ifs with hx
    · let i : ℕ := x - 2 * d
      have hi : i < m := by omega
      have hEq : P₂.filter (fun p => p.1 = x) = (range d).image (fun j => (x, rowIdx ((i + j) % m))) := by
        ext ⟨a, b⟩
        simp only [P₂, Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_range]
        constructor
        · rintro ⟨⟨⟨i', j'⟩, ⟨hi', hj'⟩, hpeq⟩, hax⟩
          have h1 : 2 * d + i' = a := congrArg Prod.fst hpeq
          have h2 : rowIdx ((i' + j') % m) = b := congrArg Prod.snd hpeq
          have hi'eq : i' = i := by omega
          exact ⟨j', hj', Prod.ext hax.symm (by rw [← hi'eq, h2])⟩
        · rintro ⟨j, hj, hpeq⟩
          have h1 : x = a := congrArg Prod.fst hpeq
          have h2 : rowIdx ((i + j) % m) = b := congrArg Prod.snd hpeq
          exact ⟨⟨(i, j), ⟨hi, hj⟩, Prod.ext (by omega) h2⟩, h1.symm⟩
      rw [hEq, Finset.card_image_of_injOn]
      · exact Finset.card_range d
      · intro j₁ hj₁ j₂ hj₂ heq
        have hj₁' : j₁ < d := Finset.mem_range.mp (Finset.mem_coe.mp hj₁)
        have hj₂' : j₂ < d := Finset.mem_range.mp (Finset.mem_coe.mp hj₂)
        have hr_eq : rowIdx ((i + j₁) % m) = rowIdx ((i + j₂) % m) := congrArg Prod.snd heq
        have hmod := hrow_inj _ (Nat.mod_lt _ hm_pos) _ (Nat.mod_lt _ hm_pos) hr_eq
        have h1 : (i + j₁) % m = if i + j₁ < m then i + j₁ else i + j₁ - m := by
          split_ifs with h
          · exact Nat.mod_eq_of_lt h
          · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        have h2 : (i + j₂) % m = if i + j₂ < m then i + j₂ else i + j₂ - m := by
          split_ifs with h
          · exact Nat.mod_eq_of_lt h
          · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [h1, h2] at hmod
        split_ifs at hmod <;> omega
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p hp heq
      obtain ⟨⟨i', j'⟩, _, rfl⟩ := Finset.mem_image.mp hp
      dsimp only at heq; omega
  have hP₀_degR : ∀ y ∈ range N, degR P₀ y = if y < d then d else 0 := by
    intro y _
    unfold degR
    split_ifs with hy
    · have hEq : P₀.filter (fun p => p.2 = y) = (range d).image (fun x => (x, y)) := by
        ext ⟨a, b⟩; simp only [P₀, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image]
        exact ⟨fun ⟨⟨ha, _⟩, hb⟩ => ⟨a, ha, Prod.ext rfl hb.symm⟩,
          fun ⟨a, ha, heq⟩ => by cases heq; exact ⟨⟨ha, hy⟩, rfl⟩⟩
      rw [hEq, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h), Finset.card_range]
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p hp heq; simp only [P₀, Finset.mem_product, Finset.mem_range] at hp; omega
  have hP₁_degR : ∀ y ∈ range N, degR P₁ y = if N - 2 * d ≤ y ∧ y < N - d then d else 0 := by
    intro y _
    unfold degR
    split_ifs with hy
    · have hEq : P₁.filter (fun p => p.2 = y) = (Ico d (2 * d)).image (fun x => (x, y)) := by
        ext ⟨a, b⟩; simp only [P₁, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_image]
        exact ⟨fun ⟨⟨ha, _⟩, hb⟩ => ⟨a, ha, Prod.ext rfl hb.symm⟩,
          fun ⟨a, ha, heq⟩ => by cases heq; exact ⟨⟨ha, hy⟩, rfl⟩⟩
      rw [hEq, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h), Nat.card_Ico]
      omega
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p hp heq; simp only [P₁, Finset.mem_product, Finset.mem_Ico] at hp; omega
  have hP₂_degR : ∀ y ∈ range N, degR P₂ y = if (d ≤ y ∧ y < N - 2 * d) ∨ (N - d ≤ y ∧ y < N) then d else 0 := by
    intro y hyN
    have hylt : y < N := Finset.mem_range.mp hyN
    unfold degR
    split_ifs with hy
    · obtain ⟨r₀, hr₀, hr₀_eq⟩ := hrow_surj y hylt hy
      have hEq : P₂.filter (fun p => p.2 = y) =
          (range d).image (fun j => (2 * d + (r₀ + m - j) % m, y)) := by
        ext ⟨a, b⟩
        simp only [P₂, Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_range]
        constructor
        · rintro ⟨⟨⟨i', j'⟩, ⟨hi', hj'⟩, hpeq⟩, hby⟩
          have h1 : 2 * d + i' = a := congrArg Prod.fst hpeq
          have h2 : rowIdx ((i' + j') % m) = b := congrArg Prod.snd hpeq
          have hmod : (i' + j') % m = r₀ := hrow_inj _ (Nat.mod_lt _ hm_pos) _ hr₀ (h2.trans (hby.trans hr₀_eq.symm))
          have hi'_eq : (r₀ + m - j') % m = i' := by
            have hA : (i' + j') % m = if i' + j' < m then i' + j' else i' + j' - m := by
              split_ifs with h
              · exact Nat.mod_eq_of_lt h
              · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
            have hB : (r₀ + m - j') % m = if j' ≤ r₀ then r₀ - j' else r₀ + m - j' := by
              split_ifs with h
              · rw [show r₀ + m - j' = (r₀ - j') + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              · exact Nat.mod_eq_of_lt (by omega)
            rw [hA] at hmod; rw [hB]
            split_ifs at hmod ⊢ <;> omega
          exact ⟨j', hj', Prod.ext (by rw [hi'_eq, h1]) hby.symm⟩
        · rintro ⟨j, hj, hpeq⟩
          have h1 : 2 * d + (r₀ + m - j) % m = a := congrArg Prod.fst hpeq
          have h2 : y = b := congrArg Prod.snd hpeq
          let i' := (r₀ + m - j) % m
          have hi' : i' < m := Nat.mod_lt _ hm_pos
          have hmod : (i' + j) % m = r₀ := by
            have hB : i' = if j ≤ r₀ then r₀ - j else r₀ + m - j := by
              dsimp [i']
              split_ifs with h
              · rw [show r₀ + m - j = (r₀ - j) + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              · exact Nat.mod_eq_of_lt (by omega)
            rw [hB]
            split_ifs with h
            · rw [show r₀ - j + j = r₀ by omega, Nat.mod_eq_of_lt hr₀]
            · rw [show r₀ + m - j + j = r₀ + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hr₀]
          exact ⟨⟨(i', j), ⟨hi', hj⟩, Prod.ext h1 (by rw [hmod, hr₀_eq, h2])⟩, h2.symm⟩
      rw [hEq, Finset.card_image_of_injOn]
      · exact Finset.card_range d
      · intro j₁ hj₁ j₂ hj₂ heq
        have hj₁' : j₁ < d := Finset.mem_range.mp (Finset.mem_coe.mp hj₁)
        have hj₂' : j₂ < d := Finset.mem_range.mp (Finset.mem_coe.mp hj₂)
        have hmod : (r₀ + m - j₁) % m = (r₀ + m - j₂) % m := by
          have := congrArg Prod.fst heq; dsimp only at this; omega
        have h1 : (r₀ + m - j₁) % m = if j₁ ≤ r₀ then r₀ - j₁ else r₀ + m - j₁ := by
          split_ifs with h
          · rw [show r₀ + m - j₁ = (r₀ - j₁) + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          · exact Nat.mod_eq_of_lt (by omega)
        have h2 : (r₀ + m - j₂) % m = if j₂ ≤ r₀ then r₀ - j₂ else r₀ + m - j₂ := by
          split_ifs with h
          · rw [show r₀ + m - j₂ = (r₀ - j₂) + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          · exact Nat.mod_eq_of_lt (by omega)
        rw [h1, h2] at hmod
        split_ifs at hmod <;> omega
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p hp heq
      obtain ⟨⟨i', j'⟩, _, rfl⟩ := Finset.mem_image.mp hp
      dsimp only at heq
      have hr := hrow_range _ (Nat.mod_lt (i' + j') hm_pos)
      rw [heq] at hr
      exact hy hr
  have hdisj01 : Disjoint P₀ P₁ := by
    rw [Finset.disjoint_left]; intro p hp0 hp1
    simp only [P₀, Finset.mem_product, Finset.mem_range] at hp0
    simp only [P₁, Finset.mem_product, Finset.mem_Ico] at hp1
    omega
  have hdisj012 : Disjoint (P₀ ∪ P₁) P₂ := by
    rw [Finset.disjoint_left]; intro p hp01 hp2
    obtain ⟨⟨i', j'⟩, _, rfl⟩ := Finset.mem_image.mp hp2
    rcases Finset.mem_union.mp hp01 with hp0 | hp1
    · simp only [P₀, Finset.mem_product, Finset.mem_range] at hp0; omega
    · simp only [P₁, Finset.mem_product, Finset.mem_Ico] at hp1; omega
  have hPreg : IsKRegular N d P := by
    refine ⟨hP_sub, ?_, ?_⟩
    · intro x hx
      have hEq : P.filter (fun p => p.1 = x) =
          (P₀.filter (fun p => p.1 = x) ∪ P₁.filter (fun p => p.1 = x)) ∪ P₂.filter (fun p => p.1 = x) := by
        simp [P, Finset.filter_union]
      unfold degL; rw [hEq, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
      · change degL P₀ x + degL P₁ x + degL P₂ x = d
        rw [hP₀_degL x hx, hP₁_degL x hx, hP₂_degL x hx]
        split_ifs <;> omega
      · exact disj_mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj01
      · exact disj_mono
          (Finset.union_subset (Finset.filter_subset _ _ |>.trans Finset.subset_union_left)
            (Finset.filter_subset _ _ |>.trans Finset.subset_union_right))
          (Finset.filter_subset _ _) hdisj012
    · intro y hy
      have hEq : P.filter (fun p => p.2 = y) =
          (P₀.filter (fun p => p.2 = y) ∪ P₁.filter (fun p => p.2 = y)) ∪ P₂.filter (fun p => p.2 = y) := by
        simp [P, Finset.filter_union]
      unfold degR; rw [hEq, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
      · change degR P₀ y + degR P₁ y + degR P₂ y = d
        rw [hP₀_degR y hy, hP₁_degR y hy, hP₂_degR y hy]
        have hylt : y < N := Finset.mem_range.mp hy
        split_ifs <;> omega
      · exact disj_mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj01
      · exact disj_mono
          (Finset.union_subset (Finset.filter_subset _ _ |>.trans Finset.subset_union_left)
            (Finset.filter_subset _ _ |>.trans Finset.subset_union_right))
          (Finset.filter_subset _ _) hdisj012
  let S : Finset (ℕ × ℕ) := grid N \ P
  have hSreg : IsKRegular N r S := by
    refine ⟨Finset.sdiff_subset, ?_, ?_⟩
    · intro x hx
      have hEq : S.filter (fun p => p.1 = x) =
          (grid N).filter (fun p => p.1 = x) \ P.filter (fun p => p.1 = x) := by
        ext p; simp only [S, Finset.mem_filter, Finset.mem_sdiff]; tauto
      unfold degL
      rw [hEq, Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ hP_sub)]
      have hgridL : ((grid N).filter (fun p => p.1 = x)).card = N := by
        have hG : (grid N).filter (fun p => p.1 = x) = (range N).image (fun y => (x, y)) := by
          ext ⟨a, b⟩; simp only [grid, Finset.mem_filter, Finset.mem_product, Finset.mem_image]
          exact ⟨fun ⟨⟨_, hb⟩, ha⟩ => ⟨b, hb, Prod.ext ha.symm rfl⟩,
            fun ⟨b, hb, heq⟩ => by cases heq; exact ⟨⟨hx, hb⟩, rfl⟩⟩
        rw [hG, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h), Finset.card_range]
      rw [hgridL]
      have hPx : (P.filter (fun p => p.1 = x)).card = d := hPreg.2.1 x hx
      rw [hPx]; omega
    · intro y hy
      have hEq : S.filter (fun p => p.2 = y) =
          (grid N).filter (fun p => p.2 = y) \ P.filter (fun p => p.2 = y) := by
        ext p; simp only [S, Finset.mem_filter, Finset.mem_sdiff]; tauto
      unfold degR
      rw [hEq, Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ hP_sub)]
      have hgridR : ((grid N).filter (fun p => p.2 = y)).card = N := by
        have hG : (grid N).filter (fun p => p.2 = y) = (range N).image (fun x => (x, y)) := by
          ext ⟨a, b⟩; simp only [grid, Finset.mem_filter, Finset.mem_product, Finset.mem_image]
          exact ⟨fun ⟨⟨ha, _⟩, hb⟩ => ⟨a, ha, Prod.ext rfl hb.symm⟩,
            fun ⟨a, ha, heq⟩ => by cases heq; exact ⟨⟨ha, hy⟩, rfl⟩⟩
        rw [hG, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h), Finset.card_range]
      rw [hgridR]
      have hPy : (P.filter (fun p => p.2 = y)).card = d := hPreg.2.2 y hy
      rw [hPy]; omega
  refine ⟨S, hSreg, fun a b c ha hb => ?_⟩
  let L := (grid N).filter (fun p => a * p.1 + b * p.2 = c)
  have hSL : S.filter (fun p => a * p.1 + b * p.2 = c) = L \ (L ∩ P) := by
    ext p; simp only [S, L, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_inter]; tauto
  rw [hSL, Finset.card_sdiff_of_subset Finset.inter_subset_left]
  by_cases hdiag1 : a = -b
  · -- Slope +1: b * (y - x) = c
    subst hdiag1
    by_cases hdvd : b ∣ c
    · obtain ⟨c₀, rfl⟩ := hdvd
      have hL_eq : L = (grid N).filter (fun p => (p.2 : ℤ) - (p.1 : ℤ) = c₀) := by
        ext p; simp only [L, Finset.mem_filter]
        refine and_congr_right fun _ => ?_
        constructor
        · intro h; apply mul_left_cancel₀ hb; linarith
        · intro h; linear_combination b * h
      have hL_le : L.card ≤ N - c₀.natAbs := by
        rw [hL_eq]
        by_cases hc0 : 0 ≤ c₀
        · have hinj : Set.InjOn Prod.fst (((grid N).filter (fun p => (p.2 : ℤ) - p.1 = c₀)) : Set (ℕ × ℕ)) := by
            intro p hp q hq heq
            have hp' := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
            have hq' := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
            exact Prod.ext heq (by omega)
          calc ((grid N).filter (fun p => (p.2 : ℤ) - p.1 = c₀)).card
              = (((grid N).filter (fun p => (p.2 : ℤ) - p.1 = c₀)).image Prod.fst).card :=
                (Finset.card_image_of_injOn hinj).symm
            _ ≤ (range (N - c₀.natAbs)).card := Finset.card_le_card (by
                intro x hx; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
                obtain ⟨hpG, hpeq⟩ := Finset.mem_filter.mp hp
                simp only [grid, Finset.mem_product, Finset.mem_range] at hpG
                exact Finset.mem_range.mpr (by omega))
            _ = N - c₀.natAbs := Finset.card_range _
        · have hinj : Set.InjOn Prod.snd (((grid N).filter (fun p => (p.2 : ℤ) - p.1 = c₀)) : Set (ℕ × ℕ)) := by
            intro p hp q hq heq
            have hp' := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
            have hq' := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
            exact Prod.ext (by omega) heq
          calc ((grid N).filter (fun p => (p.2 : ℤ) - p.1 = c₀)).card
              = (((grid N).filter (fun p => (p.2 : ℤ) - p.1 = c₀)).image Prod.snd).card :=
                (Finset.card_image_of_injOn hinj).symm
            _ ≤ (range (N - c₀.natAbs)).card := Finset.card_le_card (by
                intro y hy; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
                obtain ⟨hpG, hpeq⟩ := Finset.mem_filter.mp hp
                simp only [grid, Finset.mem_product, Finset.mem_range] at hpG
                exact Finset.mem_range.mpr (by omega))
            _ = N - c₀.natAbs := Finset.card_range _
      by_cases hcd : d ≤ c₀.natAbs
      · omega
      · -- Meet P₀ in at least d - c₀.natAbs points
        have hP₀_ge : d - c₀.natAbs ≤ (L ∩ P).card := by
          by_cases hc0 : 0 ≤ c₀
          · let f : ℕ → ℕ × ℕ := fun x => (x, x + c₀.natAbs)
            have hsub : (range (d - c₀.natAbs)).image f ⊆ L ∩ P := by
              intro p hp
              obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
              have hxlt : x < d - c₀.natAbs := Finset.mem_range.mp hx
              rw [Finset.mem_inter, hL_eq]
              dsimp only [f]
              refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
                Finset.mem_range.mpr (by omega)⟩, by omega⟩, ?_⟩
              exact Finset.mem_union_left P₂ (Finset.mem_union_left P₁
                (Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩))
            have hcard := Finset.card_le_card hsub
            rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h), Finset.card_range] at hcard
            exact hcard
          · let f : ℕ → ℕ × ℕ := fun y => (y + c₀.natAbs, y)
            have hsub : (range (d - c₀.natAbs)).image f ⊆ L ∩ P := by
              intro p hp
              obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
              have hylt : y < d - c₀.natAbs := Finset.mem_range.mp hy
              rw [Finset.mem_inter, hL_eq]
              dsimp only [f]
              refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
                Finset.mem_range.mpr (by omega)⟩, by omega⟩, ?_⟩
              exact Finset.mem_union_left P₂ (Finset.mem_union_left P₁
                (Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩))
            have hcard := Finset.card_le_card hsub
            rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h), Finset.card_range] at hcard
            exact hcard
        omega
    · have hLemp : L = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro p _ h
        exact hdvd ⟨(p.2 : ℤ) - p.1, by linarith⟩
      simp [hLemp]
  · by_cases hdiag2 : a = b
    · -- Slope -1: a * (x + y) = c
      subst hdiag2
      by_cases hdvd : a ∣ c
      · obtain ⟨s, rfl⟩ := hdvd
        have hL_eq : L = (grid N).filter (fun p => (p.1 : ℤ) + (p.2 : ℤ) = s) := by
          ext p; simp only [L, Finset.mem_filter]
          refine and_congr_right fun _ => ?_
          constructor
          · intro h; apply mul_left_cancel₀ ha; linarith
          · intro h; linear_combination a * h
        let t : ℤ := s - ((N - 1 : ℕ) : ℤ)
        have hL_le : L.card ≤ N - t.natAbs := by
          rw [hL_eq]
          have hinj : Set.InjOn Prod.fst (((grid N).filter (fun p => (p.1 : ℤ) + p.2 = s)) : Set (ℕ × ℕ)) := by
            intro p hp q hq heq
            have hp' := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
            have hq' := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
            exact Prod.ext heq (by omega)
          by_cases ht0 : t ≤ 0
          · calc ((grid N).filter (fun p => (p.1 : ℤ) + p.2 = s)).card
                = (((grid N).filter (fun p => (p.1 : ℤ) + p.2 = s)).image Prod.fst).card :=
                  (Finset.card_image_of_injOn hinj).symm
              _ ≤ (range (N - t.natAbs)).card := Finset.card_le_card (by
                  intro x hx; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
                  obtain ⟨hpG, hpeq⟩ := Finset.mem_filter.mp hp
                  simp only [grid, Finset.mem_product, Finset.mem_range] at hpG
                  exact Finset.mem_range.mpr (by dsimp [t] at ht0 ⊢; omega))
              _ = N - t.natAbs := Finset.card_range _
          · calc ((grid N).filter (fun p => (p.1 : ℤ) + p.2 = s)).card
                = (((grid N).filter (fun p => (p.1 : ℤ) + p.2 = s)).image Prod.fst).card :=
                  (Finset.card_image_of_injOn hinj).symm
              _ ≤ (Ico t.natAbs N).card := Finset.card_le_card (by
                  intro x hx; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
                  obtain ⟨hpG, hpeq⟩ := Finset.mem_filter.mp hp
                  simp only [grid, Finset.mem_product, Finset.mem_range] at hpG
                  exact Finset.mem_Ico.mpr ⟨by dsimp [t] at ht0 ⊢; omega, hpG.1⟩)
              _ = N - t.natAbs := Nat.card_Ico _ _
        by_cases htd : d ≤ t.natAbs
        · omega
        · -- Meet P₁ in at least d - t.natAbs points
          have hP₁_ge : d - t.natAbs ≤ (L ∩ P).card := by
            by_cases ht0 : t ≤ 0
            · let f : ℕ → ℕ × ℕ := fun u => (d + u, N - 2 * d + (d - 1 - t.natAbs - u))
              have hsub : (range (d - t.natAbs)).image f ⊆ L ∩ P := by
                intro p hp
                obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
                have hult : u < d - t.natAbs := Finset.mem_range.mp hu
                rw [Finset.mem_inter, hL_eq]
                dsimp only [f]
                refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
                  Finset.mem_range.mpr (by omega)⟩, by dsimp [t] at ht0 ⊢; omega⟩, ?_⟩
                exact Finset.mem_union_left P₂ (Finset.mem_union_right P₀
                  (Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩,
                    Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩))
              have hcard := Finset.card_le_card hsub
              rw [Finset.card_image_of_injective _ (fun u₁ u₂ h => by
                have := congrArg Prod.fst h; dsimp [f] at this; omega), Finset.card_range] at hcard
              exact hcard
            · let f : ℕ → ℕ × ℕ := fun u => (d + u, N - 2 * d + (d - 1 + t.natAbs - u))
              have hsub : (Ico t.natAbs d).image f ⊆ L ∩ P := by
                intro p hp
                obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
                obtain ⟨hu1, hu2⟩ := Finset.mem_Ico.mp hu
                rw [Finset.mem_inter, hL_eq]
                dsimp only [f]
                refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
                  Finset.mem_range.mpr (by omega)⟩, by dsimp [t] at ht0 ⊢; omega⟩, ?_⟩
                exact Finset.mem_union_left P₂ (Finset.mem_union_right P₀
                  (Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩,
                    Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩))
              have hcard := Finset.card_le_card hsub
              rw [Finset.card_image_of_injective _ (fun u₁ u₂ h => by
                have := congrArg Prod.fst h; dsimp [f] at this; omega), Nat.card_Ico] at hcard
              exact hcard
          omega
      · have hLemp : L = ∅ := by
          rw [Finset.filter_eq_empty_iff]; intro p _ h
          exact hdvd ⟨(p.1 : ℤ) + p.2, by linarith⟩
        simp [hLemp]
    · -- Non-diagonal generic line
      have hhalf : L.card ≤ (N + 1) / 2 := line_card_le_half_of_not_diag (N := N) (c := c) ha hb hdiag2 hdiag1
      omega

/-- Block weight matrix for the `4 × 4` block decomposition (KNS-25 Lemma 3.5). -/
def w4Nat (i j : ℕ) : ℕ := if i = j ∨ i + j = 3 then 2 else 3

def W4 (i j : Fin 4) : ℕ := w4Nat i.1 j.1

def block4 (m : ℕ) (i j : Fin 4) : Finset (ℕ × ℕ) :=
  Ico (i.1 * m) ((i.1 + 1) * m) ×ˢ Ico (j.1 * m) ((j.1 + 1) * m)

private lemma w4Nat_symm (i j : ℕ) : w4Nat i j = w4Nat j i := by
  unfold w4Nat; congr 1; exact propext (by omega)

private lemma w4Nat_reflect {i j : ℕ} (hi : i < 4) : w4Nat (3 - i) j = w4Nat i j := by
  unfold w4Nat; congr 1; exact propext (by omega)

private lemma w4Nat_le_three (i j : ℕ) : w4Nat i j ≤ 3 := by
  unfold w4Nat; split_ifs <;> omega

private lemma W4_row_sum (i : Fin 4) : ∑ j : Fin 4, W4 i j = 10 := by
  fin_cases i <;> decide

private lemma W4_col_sum (j : Fin 4) : ∑ i : Fin 4, W4 i j = 10 := by
  fin_cases j <;> decide

private lemma W4_total_sum : ∑ i : Fin 4, ∑ j : Fin 4, W4 i j = 40 := by
  decide

private lemma w4Nat_diag_sum_le (q : ℕ) (hq : q < 4) :
    ∑ b ∈ range (4 - q), w4Nat b (b + q) ≤ 8 := by
  interval_cases q <;> decide

private lemma w4Nat_diag_sum_succ_le (q : ℕ) (hq : q < 4) :
    ∑ b ∈ range (3 - q), w4Nat b (b + q + 1) ≤ 8 := by
  interval_cases q <;> decide

/-- Weighted block-incidence bound for every non-axis integer line on `[0, 4m)^2`
(KNS-25 Lemma 3.5). -/
lemma block4_expectation_bound {m : ℕ} (hm : 1 ≤ m) {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    let L := (grid (4 * m)).filter (fun p => a * p.1 + b * p.2 = c)
    ∑ i : Fin 4, ∑ j : Fin 4, W4 i j * (L ∩ block4 m i j).card ≤ 8 * m := by
  intro L
  let wPt : ℕ × ℕ → ℕ := fun p => w4Nat (p.1 / m) (p.2 / m)
  -- Express weighted block sum as a sum over L of wPt
  have hsum_eq : ∑ i : Fin 4, ∑ j : Fin 4, W4 i j * (L ∩ block4 m i j).card =
      ∑ p ∈ L, wPt p := by
    have h1 : ∀ i j : Fin 4, W4 i j * (L ∩ block4 m i j).card =
        ∑ p ∈ L ∩ block4 m i j, wPt p := by
      intro i j
      rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hpB := (Finset.mem_inter.mp hp).2
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hpB
      obtain ⟨hx1, hx2⟩ := Finset.mem_Ico.mp hx
      obtain ⟨hy1, hy2⟩ := Finset.mem_Ico.mp hy
      have hdivx : p.1 / m = i.1 := by
        apply le_antisymm
        · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr hx2)
        · exact (Nat.le_div_iff_mul_le (by omega)).mpr hx1
      have hdivy : p.2 / m = j.1 := by
        apply le_antisymm
        · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr hy2)
        · exact (Nat.le_div_iff_mul_le (by omega)).mpr hy1
      dsimp [W4, wPt]; rw [hdivx, hdivy]
    simp_rw [h1]
    rw [← Fintype.sum_prod_type']
    rw [← Finset.sum_biUnion]
    · congr 1
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter]
      constructor
      · rintro ⟨_, hpL, _⟩; exact hpL
      · intro hpL
        have hpG := (Finset.mem_filter.mp hpL).1
        obtain ⟨hx, hy⟩ := Finset.mem_product.mp hpG
        have hxlt : p.1 < 4 * m := Finset.mem_range.mp hx
        have hylt : p.2 < 4 * m := Finset.mem_range.mp hy
        have hix : p.1 / m < 4 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
        have hiy : p.2 / m < 4 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
        refine ⟨(⟨p.1 / m, hix⟩, ⟨p.2 / m, hiy⟩), hpL, ?_⟩
        simp only [block4, Finset.mem_product, Finset.mem_Ico]
        exact ⟨⟨Nat.div_mul_le_self p.1 m, by
          rw [add_mul, one_mul]; exact Nat.lt_div_mul_add (by omega)⟩,
          ⟨Nat.div_mul_le_self p.2 m, by
          rw [add_mul, one_mul]; exact Nat.lt_div_mul_add (by omega)⟩⟩
    · intro ij₁ _ ij₂ _ hne
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      have hb1 := (Finset.mem_inter.mp hp1).2
      have hb2 := (Finset.mem_inter.mp hp2).2
      simp only [block4, Finset.mem_product, Finset.mem_Ico] at hb1 hb2
      have hdivx1 : p.1 / m = ij₁.1.1 := le_antisymm
        (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr hb1.1.2))
        ((Nat.le_div_iff_mul_le (by omega)).mpr hb1.1.1)
      have hdivx2 : p.1 / m = ij₂.1.1 := le_antisymm
        (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr hb2.1.2))
        ((Nat.le_div_iff_mul_le (by omega)).mpr hb2.1.1)
      have hdivy1 : p.2 / m = ij₁.2.1 := le_antisymm
        (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr hb1.2.2))
        ((Nat.le_div_iff_mul_le (by omega)).mpr hb1.2.1)
      have hdivy2 : p.2 / m = ij₂.2.1 := le_antisymm
        (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr hb2.2.2))
        ((Nat.le_div_iff_mul_le (by omega)).mpr hb2.2.1)
      apply hne
      exact Prod.ext (Fin.ext (hdivx1.symm.trans hdivx2)) (Fin.ext (hdivy1.symm.trans hdivy2))
  rw [hsum_eq]
  -- Helper for positive-slope diagonal y - x = t with 0 ≤ t
  have hdiag_nonneg : ∀ t : ℕ,
      ∑ p ∈ (grid (4 * m)).filter (fun p => (p.2 : ℤ) - (p.1 : ℤ) = (t : ℤ)), wPt p ≤ 8 * m := by
    intro t
    by_cases ht : 4 * m ≤ t
    · have hemp : (grid (4 * m)).filter (fun p => (p.2 : ℤ) - (p.1 : ℤ) = (t : ℤ)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro p hp
        simp only [grid, Finset.mem_product, Finset.mem_range] at hp; omega
      rw [hemp]; simp
    push Not at ht
    have hEq : (grid (4 * m)).filter (fun p => (p.2 : ℤ) - (p.1 : ℤ) = (t : ℤ)) =
        (range (4 * m - t)).image (fun x => (x, x + t)) := by
      ext ⟨x, y⟩
      simp only [grid, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨⟨hx, hy⟩, hxy⟩; exact ⟨x, by omega, Prod.ext rfl (by omega)⟩
      · rintro ⟨x', hx', heq⟩; cases heq; exact ⟨⟨by omega, by omega⟩, by omega⟩
    rw [hEq, Finset.sum_image (fun _ _ _ _ h => congrArg Prod.fst h)]
    let q : ℕ := t / m
    let s : ℕ := t % m
    have hq_lt : q < 4 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
    have hs_lt : s < m := Nat.mod_lt t (by omega)
    have ht_eq : t = q * m + s := by
      have := Nat.div_add_mod t m; dsimp [q, s]; linarith
    -- Partition range (4 * m - t) by r = x % m ∈ range m
    let g : ℕ → Finset ℕ := fun r =>
      if r < m - s then (range (4 - q)).image (fun b => b * m + r)
      else (range (3 - q)).image (fun b => b * m + r)
    have hpart : range (4 * m - t) = (range m).biUnion g := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_range, g]
      constructor
      · intro hx
        refine ⟨x % m, Nat.mod_lt x (by omega), ?_⟩
        have hxm : x = (x / m) * m + x % m := by have := Nat.div_add_mod x m; linarith
        split_ifs with hr
        · refine Finset.mem_image.mpr ⟨x / m, Finset.mem_range.mpr ?_, hxm.symm⟩
          by_contra hge; push Not at hge
          have : (4 - q) * m ≤ (x / m) * m := Nat.mul_le_mul_right m hge
          have h4q : (4 - q) * m = 4 * m - q * m := Nat.sub_mul 4 q m
          omega
        · refine Finset.mem_image.mpr ⟨x / m, Finset.mem_range.mpr ?_, hxm.symm⟩
          by_contra hge; push Not at hge
          have : (3 - q) * m ≤ (x / m) * m := Nat.mul_le_mul_right m hge
          have h3q : (3 - q) * m = 3 * m - q * m := Nat.sub_mul 3 q m
          omega
      · rintro ⟨r, hr, hx⟩
        split_ifs at hx with hrm
        · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
          have hblt : b < 4 - q := Finset.mem_range.mp hb
          have hbm : (b + 1) * m ≤ (4 - q) * m := Nat.mul_le_mul_right m (by omega)
          have hbm' : (b + 1) * m = b * m + m := by ring
          have h4q : (4 - q) * m = 4 * m - q * m := Nat.sub_mul 4 q m
          omega
        · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
          have hblt : b < 3 - q := Finset.mem_range.mp hb
          have hbm : (b + 1) * m ≤ (3 - q) * m := Nat.mul_le_mul_right m (by omega)
          have hbm' : (b + 1) * m = b * m + m := by ring
          have h3q : (3 - q) * m = 3 * m - q * m := Nat.sub_mul 3 q m
          omega
    have hdisj : Set.PairwiseDisjoint (range m : Set ℕ) g := by
      intro r₁ hr₁ r₂ hr₂ hne
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have hr₁' : r₁ < m := Finset.mem_range.mp (Finset.mem_coe.mp hr₁)
      have hr₂' : r₂ < m := Finset.mem_range.mp (Finset.mem_coe.mp hr₂)
      dsimp [g] at hx1 hx2
      have hmod1 : x % m = r₁ := by
        split_ifs at hx1 <;>
        · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hx1
          rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hr₁']
      have hmod2 : x % m = r₂ := by
        split_ifs at hx2 <;>
        · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hx2
          rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hr₂']
      exact hne (hmod1.symm.trans hmod2)
    rw [hpart, Finset.sum_biUnion hdisj]
    calc ∑ r ∈ range m, ∑ x ∈ g r, wPt (x, x + t)
        ≤ ∑ _r ∈ range m, 8 := by
          refine Finset.sum_le_sum fun r hr => ?_
          have hrlt : r < m := Finset.mem_range.mp hr
          dsimp [g]
          split_ifs with hrm
          · rw [Finset.sum_image (fun b₁ _ b₂ _ heq => by nlinarith)]
            have hcongr : ∑ b ∈ range (4 - q), wPt (b * m + r, b * m + r + t) =
                ∑ b ∈ range (4 - q), w4Nat b (b + q) := by
              refine Finset.sum_congr rfl fun b _ => ?_
              dsimp [wPt]
              have hdiv1 : (b * m + r) / m = b := by
                rw [mul_comm b m, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hrlt, add_zero]
              have hdiv2 : (b * m + r + t) / m = b + q := by
                rw [show b * m + r + t = m * (b + q) + (r + s) by rw [ht_eq]; ring]
                rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), add_zero]
              rw [hdiv1, hdiv2]
            rw [hcongr]
            exact w4Nat_diag_sum_le q hq_lt
          · rw [Finset.sum_image (fun b₁ _ b₂ _ heq => by nlinarith)]
            have hcongr : ∑ b ∈ range (3 - q), wPt (b * m + r, b * m + r + t) =
                ∑ b ∈ range (3 - q), w4Nat b (b + q + 1) := by
              refine Finset.sum_congr rfl fun b _ => ?_
              dsimp [wPt]
              have hdiv1 : (b * m + r) / m = b := by
                rw [mul_comm b m, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hrlt, add_zero]
              have hdiv2 : (b * m + r + t) / m = b + q + 1 := by
                rw [show b * m + r + t = m * (b + q + 1) + (r + s - m) by
                  have h1 : m * (b + q + 1) = b * m + q * m + m := by ring
                  rw [h1, ht_eq]; omega]
                rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), add_zero]
              rw [hdiv1, hdiv2]
            rw [hcongr]
            exact w4Nat_diag_sum_succ_le q hq_lt
      _ = 8 * m := by simp [mul_comm]
  -- Helper for any positive-slope diagonal y - x = c₀
  have hdiag_pos : ∀ c₀ : ℤ,
      ∑ p ∈ (grid (4 * m)).filter (fun p => (p.2 : ℤ) - (p.1 : ℤ) = c₀), wPt p ≤ 8 * m := by
    intro c₀
    by_cases hc : 0 ≤ c₀
    · have heq : c₀ = (c₀.toNat : ℤ) := by omega
      rw [heq]; exact hdiag_nonneg c₀.toNat
    · -- Swap (x, y) ↔ (y, x)
      let t := (-c₀).toNat
      have heq : -c₀ = (t : ℤ) := by omega
      have hbij : ∑ p ∈ (grid (4 * m)).filter (fun p => (p.2 : ℤ) - (p.1 : ℤ) = c₀), wPt p =
          ∑ p ∈ (grid (4 * m)).filter (fun p => (p.2 : ℤ) - (p.1 : ℤ) = (t : ℤ)), wPt p := by
        refine Finset.sum_bij (fun p _ => p.swap) ?_ ?_ ?_ ?_
        · intro p hp
          simp only [grid, Finset.mem_filter, Finset.mem_product, Prod.fst_swap, Prod.snd_swap] at hp ⊢
          exact ⟨⟨hp.1.2, hp.1.1⟩, by omega⟩
        · intro p₁ _ p₂ _ h; exact Prod.swap_injective h
        · intro p hp
          refine ⟨p.swap, ?_, Prod.swap_swap p⟩
          simp only [grid, Finset.mem_filter, Finset.mem_product, Prod.fst_swap, Prod.snd_swap] at hp ⊢
          exact ⟨⟨hp.1.2, hp.1.1⟩, by omega⟩
        · intro p _; dsimp [wPt]; exact w4Nat_symm _ _
      rw [hbij]
      exact hdiag_nonneg t
  by_cases h1 : a = -b
  · subst h1
    by_cases hdvd : b ∣ c
    · obtain ⟨c₀, rfl⟩ := hdvd
      have hLeq : L = (grid (4 * m)).filter (fun p => (p.2 : ℤ) - (p.1 : ℤ) = c₀) := by
        ext p; simp only [L, Finset.mem_filter]
        refine and_congr_right fun _ => ?_
        exact ⟨fun h => mul_left_cancel₀ hb (by linarith), fun h => by linear_combination b * h⟩
      rw [hLeq]; exact hdiag_pos c₀
    · have hemp : L = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro p _ h
        exact hdvd ⟨(p.2 : ℤ) - p.1, by linarith⟩
      rw [hemp]; simp
  · by_cases h2 : a = b
    · subst h2
      by_cases hdvd : a ∣ c
      · obtain ⟨s, rfl⟩ := hdvd
        have hLeq : L = (grid (4 * m)).filter (fun p => (p.1 : ℤ) + (p.2 : ℤ) = s) := by
          ext p; simp only [L, Finset.mem_filter]
          refine and_congr_right fun _ => ?_
          exact ⟨fun h => mul_left_cancel₀ ha (by linarith), fun h => by linear_combination a * h⟩
        rw [hLeq]
        -- Reflect x ↦ 4m - 1 - x to reduce x + y = s to y - x' = s - (4m - 1)
        let c₀ : ℤ := s - ((4 * m - 1 : ℕ) : ℤ)
        have hbij : ∑ p ∈ (grid (4 * m)).filter (fun p => (p.1 : ℤ) + (p.2 : ℤ) = s), wPt p =
            ∑ p ∈ (grid (4 * m)).filter (fun p => (p.2 : ℤ) - (p.1 : ℤ) = c₀), wPt p := by
          refine Finset.sum_bij (fun p _ => (4 * m - 1 - p.1, p.2)) ?_ ?_ ?_ ?_
          · intro p hp
            simp only [grid, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
            exact ⟨⟨by omega, hp.1.2⟩, by dsimp [c₀]; omega⟩
          · intro p₁ hp₁ p₂ hp₂ h
            simp only [grid, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp₁ hp₂
            have h1' := congrArg Prod.fst h
            have h2' := congrArg Prod.snd h
            dsimp only at h1' h2'
            exact Prod.ext (by omega) h2'
          · intro p hp
            simp only [grid, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
            refine ⟨(4 * m - 1 - p.1, p.2), ?_, Prod.ext (by omega) rfl⟩
            simp only [grid, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
            exact ⟨⟨by omega, hp.1.2⟩, by dsimp [c₀] at hp; omega⟩
          · intro p hp
            have hxlt : p.1 < 4 * m := Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
            have hq_lt : p.1 / m < 4 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
            have hdiv_ref : (4 * m - 1 - p.1) / m = 3 - p.1 / m := by
              have hdiv_eq : p.1 = (p.1 / m) * m + p.1 % m := by have := Nat.div_add_mod p.1 m; linarith
              have hrem : p.1 % m < m := Nat.mod_lt p.1 (by omega)
              have hrew : 4 * m - 1 - p.1 = m * (3 - p.1 / m) + (m - 1 - p.1 % m) := by
                have h3 : m * (3 - p.1 / m) = 3 * m - (p.1 / m) * m := by
                  rw [mul_comm, Nat.sub_mul]
                have hle3 : (p.1 / m) * m ≤ 3 * m := Nat.mul_le_mul_right m (by omega)
                omega
              rw [hrew, Nat.mul_add_div (by omega),
                Nat.div_eq_of_lt (show m - 1 - p.1 % m < m by omega), add_zero]
            dsimp [wPt]
            rw [hdiv_ref, w4Nat_reflect hq_lt]
        rw [hbij]; exact hdiag_pos c₀
      · have hemp : L = ∅ := by
          rw [Finset.filter_eq_empty_iff]; intro p _ h
          exact hdvd ⟨(p.1 : ℤ) + p.2, by linarith⟩
        rw [hemp]; simp
    · -- Non-diagonal generic line
      have hhalf := line_card_le_half_of_not_diag (N := 4 * m) (c := c) ha hb h2 h1
      calc ∑ p ∈ L, wPt p ≤ ∑ _p ∈ L, 3 := Finset.sum_le_sum fun p _ => w4Nat_le_three _ _
        _ = 3 * L.card := by simp [mul_comm]
        _ ≤ 3 * ((4 * m + 1) / 2) := Nat.mul_le_mul_left 3 hhalf
        _ ≤ 8 * m := by omega

/-- `4 × 4` block assembly from `relaxed_version` (Grebennikov--Kwan Section 5). -/
lemma block4_construction {N' r' : ℕ}
    (hr' : 10 ^ 37 ≤ r') (h4r : 4 * r' ≤ 3 * N') (h4N : 4 ∣ N') (h10r : 10 ∣ r') :
    ∃ S₀ : Finset (ℕ × ℕ), IsKRegular N' r' S₀ ∧
      ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 →
        (S₀.filter (fun p => a * p.1 + b * p.2 = c)).card ≤ r' - 15 := by
  let m : ℕ := N' / 4
  let q : ℕ := r' / 10
  have hN'_eq : N' = 4 * m := by obtain ⟨t, ht⟩ := h4N; dsimp [m]; omega
  have hr'_eq : r' = 10 * q := by obtain ⟨t, ht⟩ := h10r; dsimp [q]; omega
  have hq_ge : 10 ^ 36 ≤ q := by omega
  have hm_ge : 1 ≤ m := by omega
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  -- Invoke relaxed_version on each of the 16 blocks
  have hblock_ex : ∀ ij : Fin 4 × Fin 4,
      ∃ S : Finset (ℕ × ℕ), IsKRegular m (W4 ij.1 ij.2 * q) S ∧
        ∀ L ∈ allLines m, ((S ∩ L).card : ℝ) ≤
          ((W4 ij.1 ij.2 * q : ℕ) : ℝ) * ((L.card : ℝ) / (m : ℝ) + 1 / 100) := by
    intro ⟨i, j⟩
    have hW2 : 2 ≤ W4 i j := by unfold W4 w4Nat; split_ifs <;> omega
    have hW3 : W4 i j ≤ 3 := w4Nat_le_three i.1 j.1
    have hk_ge : 10 ^ 36 ≤ W4 i j * q := by nlinarith
    have h10k : 10 * (W4 i j * q) ≤ 9 * m := by nlinarith
    exact relaxed_version hk_ge h10k
  let Sblk : Fin 4 → Fin 4 → Finset (ℕ × ℕ) := fun i j => Classical.choose (hblock_ex (i, j))
  have hSblk_reg : ∀ i j, IsKRegular m (W4 i j * q) (Sblk i j) :=
    fun i j => (Classical.choose_spec (hblock_ex (i, j))).1
  have hSblk_line : ∀ i j, ∀ L ∈ allLines m, ((Sblk i j ∩ L).card : ℝ) ≤
      ((W4 i j * q : ℕ) : ℝ) * ((L.card : ℝ) / (m : ℝ) + 1 / 100) :=
    fun i j => (Classical.choose_spec (hblock_ex (i, j))).2
  let shift : Fin 4 → Fin 4 → ℕ × ℕ → ℕ × ℕ := fun i j p => (i.1 * m + p.1, j.1 * m + p.2)
  have hshift_inj : ∀ i j, Function.Injective (shift i j) := by
    intro i j p₁ p₂ h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    dsimp [shift] at h1 h2
    exact Prod.ext (by omega) (by omega)
  let Tblk : Fin 4 → Fin 4 → Finset (ℕ × ℕ) := fun i j => (Sblk i j).image (shift i j)
  have hTblk_sub : ∀ i j, Tblk i j ⊆ block4 m i j := by
    intro i j p hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
    have huG := (hSblk_reg i j).1 hu
    simp only [Finset.mem_product, Finset.mem_range] at huG
    simp only [block4, shift, Finset.mem_product, Finset.mem_Ico]
    exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩
  have hblock_sub_grid : ∀ i j, block4 m i j ⊆ grid N' := by
    intro i j p hp
    simp only [block4, Finset.mem_product, Finset.mem_Ico] at hp
    simp only [grid, Finset.mem_product, Finset.mem_range]
    have hi : i.1 + 1 ≤ 4 := i.2
    have hj : j.1 + 1 ≤ 4 := j.2
    exact ⟨by nlinarith, by nlinarith⟩
  have hblock_disj : ∀ ij₁ ij₂ : Fin 4 × Fin 4, ij₁ ≠ ij₂ →
      Disjoint (block4 m ij₁.1 ij₁.2) (block4 m ij₂.1 ij₂.2) := by
    intro ij₁ ij₂ hne
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [block4, Finset.mem_product, Finset.mem_Ico] at hp1 hp2
    have hx : ij₁.1.1 = ij₂.1.1 := by nlinarith
    have hy : ij₁.2.1 = ij₂.2.1 := by nlinarith
    exact hne (Prod.ext (Fin.ext hx) (Fin.ext hy))
  have hTblk_disj : ∀ ij₁ ij₂ : Fin 4 × Fin 4, ij₁ ≠ ij₂ →
      Disjoint (Tblk ij₁.1 ij₁.2) (Tblk ij₂.1 ij₂.2) :=
    fun ij₁ ij₂ hne => disj_mono (hTblk_sub ij₁.1 ij₁.2) (hTblk_sub ij₂.1 ij₂.2) (hblock_disj ij₁ ij₂ hne)
  let S₀ : Finset (ℕ × ℕ) := Finset.univ.biUnion (fun ij : Fin 4 × Fin 4 => Tblk ij.1 ij.2)
  have hS₀_reg : IsKRegular N' r' S₀ := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨⟨i, j⟩, _, hpT⟩ := Finset.mem_biUnion.mp hp
      exact hblock_sub_grid i j (hTblk_sub i j hpT)
    · intro x hx
      have hxlt : x < 4 * m := by have := Finset.mem_range.mp hx; omega
      let i₀ : Fin 4 := ⟨x / m, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)⟩
      let x₀ : ℕ := x % m
      have hx₀ : x₀ ∈ range m := Finset.mem_range.mpr (Nat.mod_lt x (by omega))
      have hx_eq : x = i₀.1 * m + x₀ := by have := Nat.div_add_mod x m; dsimp [i₀, x₀]; linarith
      unfold degL
      have hfilt : S₀.filter (fun p => p.1 = x) =
          Finset.univ.biUnion (fun ij : Fin 4 × Fin 4 => (Tblk ij.1 ij.2).filter (fun p => p.1 = x)) := by
        ext p; simp [S₀]
      rw [hfilt, Finset.card_biUnion (fun ij₁ _ ij₂ _ hne =>
        disj_mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) (hTblk_disj ij₁ ij₂ hne))]
      rw [Fintype.sum_prod_type_right]
      have hterm : ∀ j : Fin 4, ∀ i : Fin 4,
          ((Tblk i j).filter (fun p => p.1 = x)).card = if i = i₀ then W4 i₀ j * q else 0 := by
        intro j i
        split_ifs with hi
        · subst hi
          have hEq : (Tblk i₀ j).filter (fun p => p.1 = x) =
              ((Sblk i₀ j).filter (fun p => p.1 = x₀)).image (shift i₀ j) := by
            ext p
            simp only [Tblk, Finset.mem_filter, Finset.mem_image]
            constructor
            · rintro ⟨⟨u, hu, rfl⟩, hpx⟩
              exact ⟨u, ⟨hu, by dsimp [shift] at hpx; omega⟩, rfl⟩
            · rintro ⟨u, ⟨hu, hux⟩, rfl⟩
              exact ⟨⟨u, hu, rfl⟩, by dsimp [shift]; omega⟩
          rw [hEq, Finset.card_image_of_injective _ (hshift_inj i₀ j)]
          exact (hSblk_reg i₀ j).2.1 x₀ hx₀
        · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro p hp hpx
          have hpB := hTblk_sub i j hp
          simp only [block4, Finset.mem_product, Finset.mem_Ico] at hpB
          have h1 : i.1 * m ≤ x := hpx ▸ hpB.1.1
          have h2 : x < (i.1 + 1) * m := hpx ▸ hpB.1.2
          have hdiv : x / m = i.1 := le_antisymm
            (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr h2))
            ((Nat.le_div_iff_mul_le (by omega)).mpr h1)
          exact hi (Fin.ext hdiv.symm)
      simp_rw [hterm]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← Finset.sum_mul, W4_row_sum i₀, hr'_eq]
    · intro y hy
      have hylt : y < 4 * m := by have := Finset.mem_range.mp hy; omega
      let j₀ : Fin 4 := ⟨y / m, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)⟩
      let y₀ : ℕ := y % m
      have hy₀ : y₀ ∈ range m := Finset.mem_range.mpr (Nat.mod_lt y (by omega))
      have hy_eq : y = j₀.1 * m + y₀ := by have := Nat.div_add_mod y m; dsimp [j₀, y₀]; linarith
      unfold degR
      have hfilt : S₀.filter (fun p => p.2 = y) =
          Finset.univ.biUnion (fun ij : Fin 4 × Fin 4 => (Tblk ij.1 ij.2).filter (fun p => p.2 = y)) := by
        ext p; simp [S₀]
      rw [hfilt, Finset.card_biUnion (fun ij₁ _ ij₂ _ hne =>
        disj_mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) (hTblk_disj ij₁ ij₂ hne))]
      rw [Fintype.sum_prod_type]
      have hterm : ∀ i : Fin 4, ∀ j : Fin 4,
          ((Tblk i j).filter (fun p => p.2 = y)).card = if j = j₀ then W4 i j₀ * q else 0 := by
        intro i j
        split_ifs with hj
        · subst hj
          have hEq : (Tblk i j₀).filter (fun p => p.2 = y) =
              ((Sblk i j₀).filter (fun p => p.2 = y₀)).image (shift i j₀) := by
            ext p
            simp only [Tblk, Finset.mem_filter, Finset.mem_image]
            constructor
            · rintro ⟨⟨u, hu, rfl⟩, hpy⟩
              exact ⟨u, ⟨hu, by dsimp [shift] at hpy; omega⟩, rfl⟩
            · rintro ⟨u, ⟨hu, huy⟩, rfl⟩
              exact ⟨⟨u, hu, rfl⟩, by dsimp [shift]; omega⟩
          rw [hEq, Finset.card_image_of_injective _ (hshift_inj i j₀)]
          exact (hSblk_reg i j₀).2.2 y₀ hy₀
        · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro p hp hpy
          have hpB := hTblk_sub i j hp
          simp only [block4, Finset.mem_product, Finset.mem_Ico] at hpB
          have h1 : j.1 * m ≤ y := hpy ▸ hpB.2.1
          have h2 : y < (j.1 + 1) * m := hpy ▸ hpB.2.2
          have hdiv : y / m = j.1 := le_antisymm
            (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr h2))
            ((Nat.le_div_iff_mul_le (by omega)).mpr h1)
          exact hj (Fin.ext hdiv.symm)
      simp_rw [hterm]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← Finset.sum_mul, W4_col_sum j₀, hr'_eq]
  refine ⟨S₀, hS₀_reg, fun a b c ha hb => ?_⟩
  let L := (grid (4 * m)).filter (fun p => a * p.1 + b * p.2 = c)
  have hS₀_filt : S₀.filter (fun p => a * p.1 + b * p.2 = c) =
      Finset.univ.biUnion (fun ij : Fin 4 × Fin 4 => (Tblk ij.1 ij.2) ∩ L) := by
    ext p
    simp only [S₀, L, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter]
    constructor
    · rintro ⟨⟨ij, hpT⟩, heq⟩
      exact ⟨ij, hpT, hN'_eq ▸ hblock_sub_grid ij.1 ij.2 (hTblk_sub ij.1 ij.2 hpT), heq⟩
    · rintro ⟨ij, hpT, _, heq⟩
      exact ⟨⟨ij, hpT⟩, heq⟩
  have hcard_sum : (S₀.filter (fun p => a * p.1 + b * p.2 = c)).card =
      ∑ i : Fin 4, ∑ j : Fin 4, ((Tblk i j) ∩ L).card := by
    rw [hS₀_filt, Finset.card_biUnion (fun ij₁ _ ij₂ _ hne =>
      disj_mono Finset.inter_subset_left Finset.inter_subset_left (hTblk_disj ij₁ ij₂ hne)),
      Fintype.sum_prod_type]
  have hblk_bound : ∀ i j : Fin 4, (((Tblk i j) ∩ L).card : ℝ) ≤
      ((W4 i j * q : ℕ) : ℝ) * (((L ∩ block4 m i j).card : ℝ) / (m : ℝ) + 1 / 100) := by
    intro i j
    let c' : ℤ := c - a * ((i.1 * m : ℕ) : ℤ) - b * ((j.1 * m : ℕ) : ℤ)
    let Lij := (grid m).filter (fun u => a * u.1 + b * u.2 = c')
    have hLij_card : Lij.card = (L ∩ block4 m i j).card := by
      have hEq : L ∩ block4 m i j = Lij.image (shift i j) := by
        ext ⟨x, y⟩
        simp only [L, Lij, block4, shift, grid, Finset.mem_inter, Finset.mem_filter,
          Finset.mem_product, Finset.mem_range, Finset.mem_Ico, Finset.mem_image]
        constructor
        · rintro ⟨⟨_, heq⟩, ⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
          rw [add_mul, one_mul] at hx2 hy2
          refine ⟨(x - i.1 * m, y - j.1 * m), ⟨⟨by omega, by omega⟩, ?_⟩,
            Prod.ext (by omega) (by omega)⟩
          dsimp [c']
          have hx' : ((x - i.1 * m : ℕ) : ℤ) = (x : ℤ) - ((i.1 * m : ℕ) : ℤ) := by omega
          have hy' : ((y - j.1 * m : ℕ) : ℤ) = (y : ℤ) - ((j.1 * m : ℕ) : ℤ) := by omega
          rw [hx', hy']; push_cast; linear_combination heq
        · rintro ⟨⟨u, v⟩, ⟨⟨hu, hv⟩, heq⟩, hpeq⟩
          have h1 : i.1 * m + u = x := congrArg Prod.fst hpeq
          have h2 : j.1 * m + v = y := congrArg Prod.snd hpeq
          have hi4 : (i.1 + 1) * m ≤ 4 * m := Nat.mul_le_mul_right m i.2
          have hj4 : (j.1 + 1) * m ≤ 4 * m := Nat.mul_le_mul_right m j.2
          simp_rw [add_mul, one_mul] at hi4 hj4 ⊢
          refine ⟨⟨⟨by omega, by omega⟩, ?_⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
          dsimp [c'] at heq
          have hx' : (x : ℤ) = ((i.1 * m : ℕ) : ℤ) + (u : ℤ) := by omega
          have hy' : (y : ℤ) = ((j.1 * m : ℕ) : ℤ) + (v : ℤ) := by omega
          rw [hx', hy']; push_cast at heq ⊢; linear_combination heq
      rw [hEq, Finset.card_image_of_injective _ (hshift_inj i j)]
    have hTL_card : ((Tblk i j) ∩ L).card = (Sblk i j ∩ Lij).card := by
      have hEq : Tblk i j ∩ L = (Sblk i j ∩ Lij).image (shift i j) := by
        ext p
        simp only [Tblk, L, Lij, shift, Finset.mem_inter, Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨⟨u, huS, rfl⟩, ⟨_, heq⟩⟩
          refine ⟨u, ⟨huS, (hSblk_reg i j).1 huS, ?_⟩, rfl⟩
          dsimp [c']; push_cast at heq ⊢; linear_combination heq
        · rintro ⟨u, ⟨huS, huG, heq⟩, rfl⟩
          refine ⟨⟨u, huS, rfl⟩, ⟨?_, ?_⟩⟩
          · exact hN'_eq ▸ hblock_sub_grid i j (hTblk_sub i j (Finset.mem_image.mpr ⟨u, huS, rfl⟩))
          · dsimp [c'] at heq; push_cast at heq ⊢; linear_combination heq
      rw [hEq, Finset.card_image_of_injective _ (hshift_inj i j)]
    rw [hTL_card, ← hLij_card]
    by_cases h2 : 2 ≤ Lij.card
    · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < Lij.card)
      have hLij_all : Lij ∈ allLines m := by
        dsimp only [Lij]
        rw [filter_linear_eq_lineThrough (Or.inl ha) hu hv huv]
        exact Finset.mem_image.mpr ⟨(u, v), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hv).1⟩, huv⟩, rfl⟩
      exact hSblk_line i j Lij hLij_all
    · push Not at h2
      have hle1 : (Sblk i j ∩ Lij).card ≤ 1 :=
        (Finset.card_le_card Finset.inter_subset_right).trans (by omega)
      have hle1R : ((Sblk i j ∩ Lij).card : ℝ) ≤ 1 := by exact_mod_cast hle1
      have hW2 : 2 ≤ W4 i j := by unfold W4 w4Nat; split_ifs <;> omega
      have hr_ge : (100 : ℝ) ≤ ((W4 i j * q : ℕ) : ℝ) := by
        exact_mod_cast (show 100 ≤ W4 i j * q by nlinarith)
      have hnn : 0 ≤ (Lij.card : ℝ) / (m : ℝ) := div_nonneg (Nat.cast_nonneg _) hm_pos.le
      nlinarith only [hle1R, hr_ge, hnn]
  have hsum_R : ((S₀.filter (fun p => a * p.1 + b * p.2 = c)).card : ℝ) ≤ (84 / 100 : ℝ) * (r' : ℝ) := by
    rw [hcard_sum]
    push_cast
    calc ∑ i : Fin 4, ∑ j : Fin 4, ((Tblk i j ∩ L).card : ℝ)
        ≤ ∑ i : Fin 4, ∑ j : Fin 4,
            ((W4 i j * q : ℕ) : ℝ) * (((L ∩ block4 m i j).card : ℝ) / (m : ℝ) + 1 / 100) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hblk_bound i j
      _ = ((q : ℝ) / (m : ℝ)) * (∑ i : Fin 4, ∑ j : Fin 4, ((W4 i j * (L ∩ block4 m i j).card : ℕ) : ℝ)) +
          ((q : ℝ) / 100) * (∑ i : Fin 4, ∑ j : Fin 4, (W4 i j : ℝ)) := by
          simp_rw [Nat.cast_mul]; simp only [Finset.mul_sum]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ ≤ ((q : ℝ) / (m : ℝ)) * (8 * (m : ℝ)) + ((q : ℝ) / 100) * 40 := by
          have hexp : (∑ i : Fin 4, ∑ j : Fin 4, ((W4 i j * (L ∩ block4 m i j).card : ℕ) : ℝ)) ≤ 8 * (m : ℝ) := by
            exact_mod_cast block4_expectation_bound (c := c) hm_ge ha hb
          have hW40 : (∑ i : Fin 4, ∑ j : Fin 4, (W4 i j : ℝ)) = 40 := by
            exact_mod_cast W4_total_sum
          rw [hW40]
          have h1 := mul_le_mul_of_nonneg_left hexp (by positivity : (0 : ℝ) ≤ (q : ℝ) / (m : ℝ))
          linarith
      _ = (84 / 100 : ℝ) * (r' : ℝ) := by
          have hr'R : (r' : ℝ) = 10 * (q : ℝ) := by exact_mod_cast hr'_eq
          rw [hr'R]; field_simp [hm_pos.ne']; ring
  have hR_le : ((S₀.filter (fun p => a * p.1 + b * p.2 = c)).card : ℝ) ≤ ((r' - 15 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    have hr'R : (100 : ℝ) ≤ (r' : ℝ) := by exact_mod_cast (show 100 ≤ r' by omega)
    push_cast
    linarith
  exact_mod_cast hR_le

/-- Reduce the regularity parameter from `r'` down to `r` by peeling `r' - r` 1-factors
(KNS-25 Lemma 3.12). -/
lemma adjust_k {N' r' r : ℕ} (hrle : r ≤ r') (hdiff : r' - r ≤ 9) (hr'15 : 15 ≤ r')
    {S₀ : Finset (ℕ × ℕ)} (hS₀ : IsKRegular N' r' S₀)
    (hline : ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 →
      (S₀.filter (fun p => a * p.1 + b * p.2 = c)).card ≤ r' - 15) :
    ∃ S₁ : Finset (ℕ × ℕ), IsKRegular N' r S₁ ∧
      ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 →
        (S₁.filter (fun p => a * p.1 + b * p.2 = c)).card ≤ r - 6 := by
  obtain ⟨_, S₁, _, _, hS₁sub, hS₁reg, _, _⟩ := peel_one_factors (r' - r) (by omega) hS₀
  have hsub : r' - (r' - r) = r := by omega
  rw [hsub] at hS₁reg
  refine ⟨S₁, hS₁reg, fun a b c ha hb => ?_⟩
  have hle := Finset.card_le_card (Finset.filter_subset_filter (fun p => a * p.1 + b * p.2 = c) hS₁sub)
  have h0 := hline a b c ha hb
  omega

/-- Enlarge the grid from `N'` to `N` (`N - N' ≤ 3`) using `d` disjoint 1-factors
(KNS-25 Lemma 3.13). -/
lemma adjust_n {N' N r : ℕ} (hNN : N' ≤ N) (hdiff : N - N' ≤ 3) (hrN' : r ≤ N')
    (hdr : N - N' ≤ r) (hr6 : 6 ≤ r)
    {S₁ : Finset (ℕ × ℕ)} (hS₁ : IsKRegular N' r S₁)
    (hline : ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 →
      (S₁.filter (fun p => a * p.1 + b * p.2 = c)).card ≤ r - 6) :
    ∃ S : Finset (ℕ × ℕ), IsKRegular N r S ∧
      ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 →
        (S.filter (fun p => a * p.1 + b * p.2 = c)).card ≤ r := by
  let d : ℕ := N - N'
  obtain ⟨P, _, hP, hPdisj, _, _, _, _⟩ := peel_one_factors d hdr hS₁
  have hPcard : ∀ j : Fin d, r ≤ (P j).card := by
    intro j; rw [isKRegular_card (hP j).2, one_mul]; exact hrN'
  have hQex : ∀ j : Fin d, ∃ Q ⊆ P j, Q.card = r :=
    fun j => Finset.exists_subset_card_eq (hPcard j)
  let Q : Fin d → Finset (ℕ × ℕ) := fun j => Classical.choose (hQex j)
  have hQsub : ∀ j, Q j ⊆ P j := fun j => (Classical.choose_spec (hQex j)).1
  have hQcard : ∀ j, (Q j).card = r := fun j => (Classical.choose_spec (hQex j)).2
  have hQsubS₁ : ∀ j, Q j ⊆ S₁ := fun j => (hQsub j).trans (hP j).1
  have hQdisj : ∀ i j : Fin d, i ≠ j → Disjoint (Q i) (Q j) :=
    fun i j hne => disj_mono (hQsub i) (hQsub j) (hPdisj i j hne)
  -- In a 1-regular graph P j, each x and each y appear at most once in Q j
  have hQ_fst_inj : ∀ j, Set.InjOn Prod.fst (Q j : Set (ℕ × ℕ)) := by
    intro j p hp q hq heq
    have hpP : p ∈ (P j).filter (fun u => u.1 = p.1) :=
      Finset.mem_filter.mpr ⟨hQsub j (Finset.mem_coe.mp hp), rfl⟩
    have hqP : q ∈ (P j).filter (fun u => u.1 = p.1) :=
      Finset.mem_filter.mpr ⟨hQsub j (Finset.mem_coe.mp hq), heq.symm⟩
    have h1 : ((P j).filter (fun u => u.1 = p.1)).card = 1 :=
      (hP j).2.2.1 p.1 (Finset.mem_product.mp ((hP j).2.1 (hQsub j (Finset.mem_coe.mp hp)))).1
    exact Finset.card_le_one.mp h1.le p hpP q hqP
  have hQ_snd_inj : ∀ j, Set.InjOn Prod.snd (Q j : Set (ℕ × ℕ)) := by
    intro j p hp q hq heq
    have hpP : p ∈ (P j).filter (fun u => u.2 = p.2) :=
      Finset.mem_filter.mpr ⟨hQsub j (Finset.mem_coe.mp hp), rfl⟩
    have hqP : q ∈ (P j).filter (fun u => u.2 = p.2) :=
      Finset.mem_filter.mpr ⟨hQsub j (Finset.mem_coe.mp hq), heq.symm⟩
    have h1 : ((P j).filter (fun u => u.2 = p.2)).card = 1 :=
      (hP j).2.2.2 p.2 (Finset.mem_product.mp ((hP j).2.1 (hQsub j (Finset.mem_coe.mp hp)))).2
    exact Finset.card_le_one.mp h1.le p hpP q hqP
  let Qall : Finset (ℕ × ℕ) := Finset.univ.biUnion Q
  let AddR : Finset (ℕ × ℕ) := Finset.univ.biUnion (fun j : Fin d => (Q j).image (fun p => (N' + j.1, p.2)))
  let AddC : Finset (ℕ × ℕ) := Finset.univ.biUnion (fun j : Fin d => (Q j).image (fun p => (p.1, N' + j.1)))
  let S : Finset (ℕ × ℕ) := (S₁ \ Qall) ∪ AddR ∪ AddC
  have hQall_sub : Qall ⊆ S₁ := Finset.biUnion_subset.mpr fun j _ => hQsubS₁ j
  have hAddR_bounds : ∀ p ∈ AddR, N' ≤ p.1 ∧ p.1 < N ∧ p.2 < N' := by
    intro p hp
    obtain ⟨j, _, hpj⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hpj
    have huG := (hS₁.1 (hQsubS₁ j hu))
    simp only [Finset.mem_product, Finset.mem_range] at huG
    exact ⟨Nat.le_add_right _ _, by omega, huG.2⟩
  have hAddC_bounds : ∀ p ∈ AddC, p.1 < N' ∧ N' ≤ p.2 ∧ p.2 < N := by
    intro p hp
    obtain ⟨j, _, hpj⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hpj
    have huG := (hS₁.1 (hQsubS₁ j hu))
    simp only [Finset.mem_product, Finset.mem_range] at huG
    exact ⟨huG.1, Nat.le_add_right _ _, by omega⟩
  have hS1_bounds : ∀ p ∈ S₁ \ Qall, p.1 < N' ∧ p.2 < N' := by
    intro p hp
    have huG := hS₁.1 (Finset.mem_sdiff.mp hp).1
    simpa [Finset.mem_product, Finset.mem_range] using huG
  have hdisj_SR : Disjoint (S₁ \ Qall) AddR := by
    rw [Finset.disjoint_left]; intro p h1 h2
    have := (hS1_bounds p h1).1; have := (hAddR_bounds p h2).1; omega
  have hdisj_SRC : Disjoint ((S₁ \ Qall) ∪ AddR) AddC := by
    rw [Finset.disjoint_left]; intro p h1 h2
    have hC := (hAddC_bounds p h2).2.1
    rcases Finset.mem_union.mp h1 with h1a | h1b
    · have := (hS1_bounds p h1a).2; omega
    · have := (hAddR_bounds p h1b).2.2; omega
  have hSreg : IsKRegular N r S := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_range]
      rcases Finset.mem_union.mp hp with hp1 | hpC
      · rcases Finset.mem_union.mp hp1 with hpS | hpR
        · have h := hS1_bounds p hpS; omega
        · have h := hAddR_bounds p hpR; omega
      · have h := hAddC_bounds p hpC; omega
    · intro x hx
      have hxlt : x < N := Finset.mem_range.mp hx
      unfold degL
      have hfilt : S.filter (fun p => p.1 = x) =
          ((S₁ \ Qall).filter (fun p => p.1 = x) ∪ AddR.filter (fun p => p.1 = x)) ∪
            AddC.filter (fun p => p.1 = x) := by
        simp [S, Finset.filter_union]
      rw [hfilt, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
      · by_cases hxN' : x < N'
        · have hx' : x ∈ range N' := Finset.mem_range.mpr hxN'
          have hAddR0 : (AddR.filter (fun p => p.1 = x)).card = 0 := by
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro p hp hpx; have := (hAddR_bounds p hp).1; omega
          have hS1Q : ((S₁ \ Qall).filter (fun p => p.1 = x)).card =
              r - ∑ j : Fin d, ((Q j).filter (fun p => p.1 = x)).card := by
            have hEq : (S₁ \ Qall).filter (fun p => p.1 = x) =
                S₁.filter (fun p => p.1 = x) \ Qall.filter (fun p => p.1 = x) := by
              ext p; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
            rw [hEq, Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ hQall_sub)]
            have hQfilt : Qall.filter (fun p => p.1 = x) =
                Finset.univ.biUnion (fun j : Fin d => (Q j).filter (fun p => p.1 = x)) := by
              ext p; simp [Qall]
            rw [hQfilt, Finset.card_biUnion (fun i _ j _ hne =>
              disj_mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) (hQdisj i j hne))]
            exact congrArg (· - _) (hS₁.2.1 x hx')
          have hAddC_eq : (AddC.filter (fun p => p.1 = x)).card =
              ∑ j : Fin d, ((Q j).filter (fun p => p.1 = x)).card := by
            have hfiltC : AddC.filter (fun p => p.1 = x) =
                Finset.univ.biUnion (fun j : Fin d =>
                  ((Q j).image (fun p => (p.1, N' + j.1))).filter (fun p => p.1 = x)) := by
              ext p; simp [AddC]
            rw [hfiltC, Finset.card_biUnion]
            · refine Finset.sum_congr rfl fun j _ => ?_
              have hEq : ((Q j).image (fun p => (p.1, N' + j.1))).filter (fun p => p.1 = x) =
                  ((Q j).filter (fun p => p.1 = x)).image (fun p => (p.1, N' + j.1)) := by
                ext p; simp only [Finset.mem_filter, Finset.mem_image]
                exact ⟨fun ⟨⟨u, hu, heq⟩, hpx⟩ => ⟨u, ⟨hu, by cases heq; exact hpx⟩, heq⟩,
                  fun ⟨u, ⟨hu, hux⟩, heq⟩ => ⟨⟨u, hu, heq⟩, by cases heq; exact hux⟩⟩
              rw [hEq, Finset.card_image_of_injOn]
              intro u hu v hv heq
              exact hQ_fst_inj j (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).1
                (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).1 (by have h := congrArg Prod.fst heq; exact h)
            · intro i _ j _ hne
              dsimp [Function.onFun]
              rw [Finset.disjoint_left]; intro p hp1 hp2
              obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hp1).1
              obtain ⟨v, _, heq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hp2).1
              have h2 := congrArg Prod.snd heq; dsimp only at h2
              exact hne (Fin.ext (by omega))
          have hsum_le : ∑ j : Fin d, ((Q j).filter (fun p => p.1 = x)).card ≤ r := by
            have hsub : Finset.univ.biUnion (fun j : Fin d => (Q j).filter (fun p => p.1 = x)) ⊆
                S₁.filter (fun p => p.1 = x) := by
              intro p hp
              obtain ⟨j, _, hpj⟩ := Finset.mem_biUnion.mp hp
              exact Finset.filter_subset_filter _ (hQsubS₁ j) hpj
            calc ∑ j : Fin d, ((Q j).filter (fun p => p.1 = x)).card
                = (Finset.univ.biUnion (fun j : Fin d => (Q j).filter (fun p => p.1 = x))).card :=
                  (Finset.card_biUnion (fun i _ j _ hne =>
                    disj_mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) (hQdisj i j hne))).symm
              _ ≤ (S₁.filter (fun p => p.1 = x)).card := Finset.card_le_card hsub
              _ = r := hS₁.2.1 x hx'
          rw [hS1Q, hAddR0, hAddC_eq]; omega
        · -- x = N' + j₀
          let j₀ : Fin d := ⟨x - N', by omega⟩
          have hx_eq : x = N' + j₀.1 := by dsimp [j₀]; omega
          have hS10 : ((S₁ \ Qall).filter (fun p => p.1 = x)).card = 0 := by
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro p hp hpx; have := (hS1_bounds p hp).1; omega
          have hAddC0 : (AddC.filter (fun p => p.1 = x)).card = 0 := by
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro p hp hpx; have := (hAddC_bounds p hp).1; omega
          have hAddR_eq : AddR.filter (fun p => p.1 = x) =
              (Q j₀).image (fun p => (N' + j₀.1, p.2)) := by
            ext p
            simp only [AddR, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
            constructor
            · rintro ⟨⟨j, u, hu, rfl⟩, hpx⟩
              have hj : j = j₀ := Fin.ext (by dsimp only at hpx; omega)
              subst hj; exact ⟨u, hu, rfl⟩
            · rintro ⟨u, hu, rfl⟩
              exact ⟨⟨j₀, u, hu, rfl⟩, hx_eq.symm⟩
          rw [hS10, hAddC0, hAddR_eq, Finset.card_image_of_injOn]
          · simp [hQcard j₀]
          · intro u hu v hv heq
            exact hQ_snd_inj j₀ hu hv (by have h := congrArg Prod.snd heq; exact h)
      · exact disj_mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj_SR
      · exact disj_mono
          (Finset.union_subset (Finset.filter_subset _ _ |>.trans Finset.subset_union_left)
            (Finset.filter_subset _ _ |>.trans Finset.subset_union_right))
          (Finset.filter_subset _ _) hdisj_SRC
    · intro y hy
      have hylt : y < N := Finset.mem_range.mp hy
      unfold degR
      have hfilt : S.filter (fun p => p.2 = y) =
          ((S₁ \ Qall).filter (fun p => p.2 = y) ∪ AddR.filter (fun p => p.2 = y)) ∪
            AddC.filter (fun p => p.2 = y) := by
        simp [S, Finset.filter_union]
      rw [hfilt, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
      · by_cases hyN' : y < N'
        · have hy' : y ∈ range N' := Finset.mem_range.mpr hyN'
          have hAddC0 : (AddC.filter (fun p => p.2 = y)).card = 0 := by
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro p hp hpy; have := (hAddC_bounds p hp).2.1; omega
          have hS1Q : ((S₁ \ Qall).filter (fun p => p.2 = y)).card =
              r - ∑ j : Fin d, ((Q j).filter (fun p => p.2 = y)).card := by
            have hEq : (S₁ \ Qall).filter (fun p => p.2 = y) =
                S₁.filter (fun p => p.2 = y) \ Qall.filter (fun p => p.2 = y) := by
              ext p; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
            rw [hEq, Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ hQall_sub)]
            have hQfilt : Qall.filter (fun p => p.2 = y) =
                Finset.univ.biUnion (fun j : Fin d => (Q j).filter (fun p => p.2 = y)) := by
              ext p; simp [Qall]
            rw [hQfilt, Finset.card_biUnion (fun i _ j _ hne =>
              disj_mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) (hQdisj i j hne))]
            exact congrArg (· - _) (hS₁.2.2 y hy')
          have hAddR_eq : (AddR.filter (fun p => p.2 = y)).card =
              ∑ j : Fin d, ((Q j).filter (fun p => p.2 = y)).card := by
            have hfiltR : AddR.filter (fun p => p.2 = y) =
                Finset.univ.biUnion (fun j : Fin d =>
                  ((Q j).image (fun p => (N' + j.1, p.2))).filter (fun p => p.2 = y)) := by
              ext p; simp [AddR]
            rw [hfiltR, Finset.card_biUnion]
            · refine Finset.sum_congr rfl fun j _ => ?_
              have hEq : ((Q j).image (fun p => (N' + j.1, p.2))).filter (fun p => p.2 = y) =
                  ((Q j).filter (fun p => p.2 = y)).image (fun p => (N' + j.1, p.2)) := by
                ext p; simp only [Finset.mem_filter, Finset.mem_image]
                exact ⟨fun ⟨⟨u, hu, heq⟩, hpy⟩ => ⟨u, ⟨hu, by cases heq; exact hpy⟩, heq⟩,
                  fun ⟨u, ⟨hu, huy⟩, heq⟩ => ⟨⟨u, hu, heq⟩, by cases heq; exact huy⟩⟩
              rw [hEq, Finset.card_image_of_injOn]
              intro u hu v hv heq
              exact hQ_snd_inj j (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).1
                (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).1 (by have h := congrArg Prod.snd heq; exact h)
            · intro i _ j _ hne
              dsimp [Function.onFun]
              rw [Finset.disjoint_left]; intro p hp1 hp2
              obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hp1).1
              obtain ⟨v, _, heq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hp2).1
              have h1 := congrArg Prod.fst heq; dsimp only at h1
              exact hne (Fin.ext (by omega))
          have hsum_le : ∑ j : Fin d, ((Q j).filter (fun p => p.2 = y)).card ≤ r := by
            have hsub : Finset.univ.biUnion (fun j : Fin d => (Q j).filter (fun p => p.2 = y)) ⊆
                S₁.filter (fun p => p.2 = y) := by
              intro p hp
              obtain ⟨j, _, hpj⟩ := Finset.mem_biUnion.mp hp
              exact Finset.filter_subset_filter _ (hQsubS₁ j) hpj
            calc ∑ j : Fin d, ((Q j).filter (fun p => p.2 = y)).card
                = (Finset.univ.biUnion (fun j : Fin d => (Q j).filter (fun p => p.2 = y))).card :=
                  (Finset.card_biUnion (fun i _ j _ hne =>
                    disj_mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) (hQdisj i j hne))).symm
              _ ≤ (S₁.filter (fun p => p.2 = y)).card := Finset.card_le_card hsub
              _ = r := hS₁.2.2 y hy'
          rw [hS1Q, hAddC0, hAddR_eq]; omega
        · -- y = N' + j₀
          let j₀ : Fin d := ⟨y - N', by omega⟩
          have hy_eq : y = N' + j₀.1 := by dsimp [j₀]; omega
          have hS10 : ((S₁ \ Qall).filter (fun p => p.2 = y)).card = 0 := by
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro p hp hpy; have := (hS1_bounds p hp).2; omega
          have hAddR0 : (AddR.filter (fun p => p.2 = y)).card = 0 := by
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro p hp hpy; have := (hAddR_bounds p hp).2.2; omega
          have hAddC_eq : AddC.filter (fun p => p.2 = y) =
              (Q j₀).image (fun p => (p.1, N' + j₀.1)) := by
            ext p
            simp only [AddC, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
            constructor
            · rintro ⟨⟨j, u, hu, rfl⟩, hpy⟩
              have hj : j = j₀ := Fin.ext (by dsimp only at hpy; omega)
              subst hj; exact ⟨u, hu, rfl⟩
            · rintro ⟨u, hu, rfl⟩
              exact ⟨⟨j₀, u, hu, rfl⟩, hy_eq.symm⟩
          rw [hS10, hAddR0, hAddC_eq, Finset.card_image_of_injOn]
          · simp [hQcard j₀]
          · intro u hu v hv heq
            exact hQ_fst_inj j₀ hu hv (by have h := congrArg Prod.fst heq; exact h)
      · exact disj_mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj_SR
      · exact disj_mono
          (Finset.union_subset (Finset.filter_subset _ _ |>.trans Finset.subset_union_left)
            (Finset.filter_subset _ _ |>.trans Finset.subset_union_right))
          (Finset.filter_subset _ _) hdisj_SRC
  refine ⟨S, hSreg, fun a b c ha hb => ?_⟩
  have hfilt : S.filter (fun p => a * p.1 + b * p.2 = c) =
      ((S₁ \ Qall).filter (fun p => a * p.1 + b * p.2 = c) ∪
        AddR.filter (fun p => a * p.1 + b * p.2 = c)) ∪
        AddC.filter (fun p => a * p.1 + b * p.2 = c) := by
    simp [S, Finset.filter_union]
  have hle_sum : (S.filter (fun p => a * p.1 + b * p.2 = c)).card ≤
      ((S₁ \ Qall).filter (fun p => a * p.1 + b * p.2 = c)).card +
      (AddR.filter (fun p => a * p.1 + b * p.2 = c)).card +
      (AddC.filter (fun p => a * p.1 + b * p.2 = c)).card := by
    rw [hfilt]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have h1 : ((S₁ \ Qall).filter (fun p => a * p.1 + b * p.2 = c)).card ≤ r - 6 :=
    (Finset.card_le_card (Finset.filter_subset_filter (fun p : ℕ × ℕ => a * p.1 + b * p.2 = c) Finset.sdiff_subset)).trans (hline a b c ha hb)
  have h2 : (AddR.filter (fun p => a * p.1 + b * p.2 = c)).card ≤ d := by
    have hEq : AddR.filter (fun p => a * p.1 + b * p.2 = c) =
        Finset.univ.biUnion (fun j : Fin d =>
          ((Q j).image (fun p => (N' + j.1, p.2))).filter (fun p => a * p.1 + b * p.2 = c)) := by
      ext p; simp [AddR]
    rw [hEq]
    calc (Finset.univ.biUnion _).card
        ≤ ∑ j : Fin d, (((Q j).image (fun p => (N' + j.1, p.2))).filter
            (fun p => a * p.1 + b * p.2 = c)).card := Finset.card_biUnion_le
      _ ≤ ∑ _j : Fin d, 1 := by
          refine Finset.sum_le_sum fun j _ => Finset.card_le_one.mpr ?_
          intro p hp q hq
          obtain ⟨hpI, hpeq⟩ := Finset.mem_filter.mp hp
          obtain ⟨hqI, hqeq⟩ := Finset.mem_filter.mp hq
          obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hpI
          obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hqI
          have hy : (u.2 : ℤ) = (v.2 : ℤ) := mul_left_cancel₀ hb (by linarith)
          exact Prod.ext rfl (by omega)
      _ = d := by simp
  have h3 : (AddC.filter (fun p => a * p.1 + b * p.2 = c)).card ≤ d := by
    have hEq : AddC.filter (fun p => a * p.1 + b * p.2 = c) =
        Finset.univ.biUnion (fun j : Fin d =>
          ((Q j).image (fun p => (p.1, N' + j.1))).filter (fun p => a * p.1 + b * p.2 = c)) := by
      ext p; simp [AddC]
    rw [hEq]
    calc (Finset.univ.biUnion _).card
        ≤ ∑ j : Fin d, (((Q j).image (fun p => (p.1, N' + j.1))).filter
            (fun p => a * p.1 + b * p.2 = c)).card := Finset.card_biUnion_le
      _ ≤ ∑ _j : Fin d, 1 := by
          refine Finset.sum_le_sum fun j _ => Finset.card_le_one.mpr ?_
          intro p hp q hq
          obtain ⟨hpI, hpeq⟩ := Finset.mem_filter.mp hp
          obtain ⟨hqI, hqeq⟩ := Finset.mem_filter.mp hq
          obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hpI
          obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hqI
          have hx : (u.1 : ℤ) = (v.1 : ℤ) := mul_left_cancel₀ ha (by linarith)
          exact Prod.ext (by omega) rfl
      _ = d := by simp
  omega

end MainReduction

end Green72H1

/-- Complete proof of `OMA.R_Green72_no_k_in_line_big_R1.H1`. -/
theorem OMA.solution : OMA.R_Green72_no_k_in_line_big_R1.H1 := by
  intro k N hk hkN
  let r : ℕ := k - 1
  have hr_ge : 10 ^ 37 ≤ r := by omega
  have hrN : r ≤ N := by omega
  have hN3 : 3 ≤ N := by omega
  obtain ⟨S, hSreg, hgen⟩ : ∃ S : Finset (ℕ × ℕ), Green72H1.IsKRegular N r S ∧
      ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 →
        (S.filter (fun p => a * p.1 + b * p.2 = c)).card ≤ r := by
    by_cases hlarge : 2 * N ≤ 3 * r
    · exact Green72H1.case_large_k hN3 hrN hlarge
    · push Not at hlarge
      let N' : ℕ := 4 * (N / 4)
      let r' : ℕ := 10 * ((r + 9) / 10)
      have h4N : 4 ∣ N' := ⟨N / 4, rfl⟩
      have h10r : 10 ∣ r' := ⟨(r + 9) / 10, rfl⟩
      have hNN' : N' ≤ N := by dsimp [N']; omega
      have hNdiff : N - N' ≤ 3 := by dsimp [N']; omega
      have hrr' : r ≤ r' := by dsimp [r']; omega
      have hrdiff : r' - r ≤ 9 := by dsimp [r']; omega
      have hr'ge : 10 ^ 37 ≤ r' := by omega
      have h4r : 4 * r' ≤ 3 * N' := by omega
      have hrN' : r ≤ N' := by omega
      obtain ⟨S₀, hS₀reg, hS₀line⟩ := Green72H1.block4_construction hr'ge h4r h4N h10r
      obtain ⟨S₁, hS₁reg, hS₁line⟩ := Green72H1.adjust_k hrr' hrdiff (by omega) hS₀reg hS₀line
      exact Green72H1.adjust_n hNN' hNdiff hrN' (by omega) (by omega) hS₁reg hS₁line
  refine ⟨S, hSreg.1, Green72H1.isKRegular_card hSreg, ?_⟩
  intro a b c hab _ _ _ _
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := hab.resolve_left (not_not.mpr rfl)
    by_cases hdvd : b ∣ c
    · obtain ⟨y₀, rfl⟩ := hdvd
      by_cases hy : 0 ≤ y₀ ∧ y₀ < (N : ℤ)
      · have hsub : S.filter (fun i => (0 : ℤ) * i.1 + b * i.2 = b * y₀) ⊆
            S.filter (fun i => i.2 = y₀.toNat) := by
          intro p hp
          obtain ⟨hpS, hpeq⟩ := Finset.mem_filter.mp hp
          have hp2 : (p.2 : ℤ) = y₀ := mul_left_cancel₀ hb (by linarith)
          exact Finset.mem_filter.mpr ⟨hpS, by omega⟩
        exact (Finset.card_le_card hsub).trans
          (le_of_eq (hSreg.2.2 y₀.toNat (Finset.mem_range.mpr (by omega))))
      · have hemp : S.filter (fun i => (0 : ℤ) * i.1 + b * i.2 = b * y₀) = ∅ := by
          rw [Finset.filter_eq_empty_iff]; intro p hp hpeq
          have hp2 : (p.2 : ℤ) = y₀ := mul_left_cancel₀ hb (by linarith)
          have hpG := Finset.mem_range.mp (Finset.mem_product.mp (hSreg.1 hp)).2
          omega
        rw [hemp]; simp
    · have hemp : S.filter (fun i => (0 : ℤ) * i.1 + b * i.2 = c) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro p _ hpeq
        exact hdvd ⟨(p.2 : ℤ), by linarith⟩
      rw [hemp]; simp
  · by_cases hb : b = 0
    · subst hb
      by_cases hdvd : a ∣ c
      · obtain ⟨x₀, rfl⟩ := hdvd
        by_cases hx : 0 ≤ x₀ ∧ x₀ < (N : ℤ)
        · have hsub : S.filter (fun i => a * i.1 + (0 : ℤ) * i.2 = a * x₀) ⊆
              S.filter (fun i => i.1 = x₀.toNat) := by
            intro p hp
            obtain ⟨hpS, hpeq⟩ := Finset.mem_filter.mp hp
            have hp1 : (p.1 : ℤ) = x₀ := mul_left_cancel₀ ha (by linarith)
            exact Finset.mem_filter.mpr ⟨hpS, by omega⟩
          exact (Finset.card_le_card hsub).trans
            (le_of_eq (hSreg.2.1 x₀.toNat (Finset.mem_range.mpr (by omega))))
        · have hemp : S.filter (fun i => a * i.1 + (0 : ℤ) * i.2 = a * x₀) = ∅ := by
            rw [Finset.filter_eq_empty_iff]; intro p hp hpeq
            have hp1 : (p.1 : ℤ) = x₀ := mul_left_cancel₀ ha (by linarith)
            have hpG := Finset.mem_range.mp (Finset.mem_product.mp (hSreg.1 hp)).1
            omega
          rw [hemp]; simp
      · have hemp : S.filter (fun i => a * i.1 + (0 : ℤ) * i.2 = c) = ∅ := by
          rw [Finset.filter_eq_empty_iff]; intro p _ hpeq
          exact hdvd ⟨(p.1 : ℤ), by linarith⟩
        rw [hemp]; simp
    · exact hgen a b c ha hb
