import FormalConjectures.ErdosProblems.«1083»
import Mathlib

/-! Erdős problem 1083. In dimension d+1, any configuration with at least
   n^(d/(d+1)) points in an isometric copy of Euclidean d-space inherits the
   sharp lower bound from dimension d. Thus only the sparse case and the
   three-dimensional base case are needed. The upper bound is Erdős's grid.
   For the full mathematical result see the September 2026 OpenAI preprint,
   The higher-dimensional Erdős distinct-distances conjecture, and Yao Xu's
   independent Lean formalization at github.com/cadamcat/distinct-distances-lean4. -/

open scoped EuclideanGeometry

namespace OMA.R_Erdos1083_erdos_1083_R2

def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ P : Finset (ℝ^3), 2 ≤ P.card →
    c * (P.card : ℝ) ^ ((2 : ℝ) / 3) ≤ (distinctDistances P : ℝ)

def H2 : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∃ c : ℝ, 0 < c ∧ ∀ P : Finset (ℝ^(d + 1)), 2 ≤ P.card →
    (¬ ∃ (Q : Finset (ℝ^d)) (f : (ℝ^d) → (ℝ^(d + 1))), Isometry f ∧
      (∀ x ∈ Q, f x ∈ P) ∧ 2 ≤ Q.card ∧
      (P.card : ℝ) ^ ((d : ℝ) / ((d + 1 : ℕ) : ℝ)) ≤ (Q.card : ℝ)) →
    c * (P.card : ℝ) ^ ((2 : ℝ) / ((d + 1 : ℕ) : ℝ)) ≤ (distinctDistances P : ℝ)

theorem distances_mono_of_isometry {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {P : Finset Y} {Q : Finset X} {f : X → Y} (hf : Isometry f)
    (hPQ : ∀ x ∈ Q, f x ∈ P) : distinctDistances Q ≤ distinctDistances P := by
  classical
  unfold distinctDistances distanceSet
  apply Finset.card_le_card
  intro r hr
  obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨hx, hy, hne⟩ := Finset.mem_offDiag.mp hxy
  exact Finset.mem_image.mpr ⟨(f x, f y),
    Finset.mem_offDiag.mpr ⟨hPQ x hx, hPQ y hy, hf.injective.ne hne⟩, hf.dist_eq x y⟩

theorem dimensional_lower (hbase : H1) (hsparse : H2) (d : ℕ) (hd : 3 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ P : Finset (ℝ^d), 2 ≤ P.card →
      c * (P.card : ℝ) ^ ((2 : ℝ) / (d : ℝ)) ≤ (distinctDistances P : ℝ) := by
  classical
  induction d, hd using Nat.le_induction with
  | base => simpa [H1] using hbase
  | succ d hd ih =>
    obtain ⟨b, hb, hlow⟩ := ih
    obtain ⟨c, hc, hs⟩ := hsparse d hd
    refine ⟨min b c, lt_min hb hc, ?_⟩
    intro P hP
    have hnonneg : 0 ≤ (P.card : ℝ) ^ ((2 : ℝ) / ((d + 1 : ℕ) : ℝ)) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    by_cases h : ∃ (Q : Finset (ℝ^d)) (f : (ℝ^d) → (ℝ^(d + 1))), Isometry f ∧
      (∀ x ∈ Q, f x ∈ P) ∧ 2 ≤ Q.card ∧
      (P.card : ℝ) ^ ((d : ℝ) / ((d + 1 : ℕ) : ℝ)) ≤ (Q.card : ℝ)
    · obtain ⟨Q, f, hf, hmem, hQ, hcard⟩ := h
      have hdpos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
      have hcancel : (d : ℝ) / ((d + 1 : ℕ) : ℝ) * (2 / (d : ℝ)) =
          2 / ((d + 1 : ℕ) : ℝ) := by
        rw [Nat.cast_add, Nat.cast_one]
        have hden : (d : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hdpos.ne', hden]
      have hpow :
          (P.card : ℝ) ^ ((2 : ℝ) / ((d + 1 : ℕ) : ℝ)) ≤
            (Q.card : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by
        rw [← hcancel, Real.rpow_mul (Nat.cast_nonneg P.card)]
        exact Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) hcard (by positivity)
      calc
        _ ≤ b * (P.card : ℝ) ^ ((2 : ℝ) / ((d + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hnonneg
        _ ≤ b * (Q.card : ℝ) ^ ((2 : ℝ) / (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow hb.le
        _ ≤ (distinctDistances Q : ℝ) := hlow Q hQ
        _ ≤ (distinctDistances P : ℝ) := by exact_mod_cast distances_mono_of_isometry hf hmem
    · exact (mul_le_mul_of_nonneg_right (min_le_right b c) hnonneg).trans (hs P hP h)



-- Integer-box construction for the upper bound (Erdős, 1946).
-- See also the formalization by Yao Xu in DistinctDistances/Upper.lean,
-- https://github.com/cadamcat/distinct-distances-lean4/tree/1a5c79b9834ff8f4563ef94fa8046261aa8fddaf
lemma coordinate_distance (a b : ℕ) :
    dist (a : ℝ) (b : ℝ) = (Nat.dist a b : ℝ) := by
  rw [Real.dist_eq]
  rcases le_total a b with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr (by exact_mod_cast h)
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h, abs_of_nonneg]
    exact sub_nonneg.mpr (by exact_mod_cast h)

lemma box_witness (d k n : ℕ) (hn : n ≤ (k + 1) ^ d) :
    ∃ P : Finset (EuclideanSpace ℝ (Fin d)), P.card = n ∧
      distinctDistances P ≤ d * k ^ 2 + 1 := by
  classical
  let point (a : Fin d → Fin (k + 1)) : EuclideanSpace ℝ (Fin d) :=
    WithLp.toLp 2 fun i => ((a i).val : ℝ)
  have hinj : Function.Injective point := by
    intro a b hab
    funext i
    apply Fin.ext
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v i) hab
    change ((a i).val : ℝ) = ((b i).val : ℝ) at h
    exact_mod_cast h
  let box := Finset.univ.image point
  have hbox : box.card = (k + 1) ^ d := by
    dsimp only [box]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  obtain ⟨P, hP, hcard⟩ := Finset.exists_subset_card_eq (s := box) (n := n) (hbox.symm ▸ hn)
  refine ⟨P, hcard, ?_⟩
  let values := (Finset.range (d * k ^ 2 + 1)).image (fun j : ℕ => Real.sqrt j)
  have hsub : distanceSet P ⊆ values := by
    intro r hr
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hx, hy, _⟩ := Finset.mem_offDiag.mp hxy
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (hP hx)
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp (hP hy)
    let q (i : Fin d) := Nat.dist (a i).val (b i).val
    have hq (i : Fin d) : q i ≤ k := by
      have ha := (a i).isLt
      have hb := (b i).isLt
      dsimp only [q, Nat.dist]
      omega
    have hsum : (∑ i, q i ^ 2) ≤ d * k ^ 2 := calc
      (∑ i, q i ^ 2) ≤ ∑ _i : Fin d, k ^ 2 :=
        Finset.sum_le_sum (fun i _ => Nat.pow_le_pow_left (hq i) 2)
      _ = d * k ^ 2 := by simp
    refine Finset.mem_image.mpr ⟨∑ i, q i ^ 2, Finset.mem_range.mpr (by omega), ?_⟩
    change Real.sqrt _ = dist (point a) (point b)
    rw [EuclideanSpace.dist_eq]
    congr 1
    change ((∑ i, q i ^ 2 : ℕ) : ℝ) = ∑ i, dist ((a i).val : ℝ) ((b i).val : ℝ) ^ 2
    simp only [Nat.cast_sum, Nat.cast_pow, coordinate_distance, q]
  calc
    distinctDistances P ≤ values.card := Finset.card_le_card hsub
    _ ≤ (Finset.range (d * k ^ 2 + 1)).card := Finset.card_image_le
    _ = d * k ^ 2 + 1 := Finset.card_range _

lemma grid_upper (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ P : Finset (EuclideanSpace ℝ (Fin d)), P.card = n ∧
        (distinctDistances P : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by
  refine ⟨d + 1, by positivity, ?_⟩
  intro n hn
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hnpos : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  let r : ℝ := (n : ℝ) ^ ((1 : ℝ) / d)
  have hr : 1 ≤ r := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) (by positivity)
  have hrd : r ^ d = (n : ℝ) := by
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos, one_div_mul_cancel hdpos.ne', Real.rpow_one]
  have hrsq : r ^ 2 = (n : ℝ) ^ ((2 : ℝ) / d) := by
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos]
    congr 1
    push_cast
    ring
  let k := ⌊r⌋₊
  have hk : (k : ℝ) ≤ r := Nat.floor_le (by linarith)
  have hk1 : r ≤ (k : ℝ) + 1 := (Nat.lt_floor_add_one r).le
  have hcap : n ≤ (k + 1) ^ d := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ r) hk1 d
    rw [hrd] at h
    exact_mod_cast h
  obtain ⟨P,hcard,hcount⟩ := box_witness d k n hcap
  refine ⟨P,hcard,?_⟩
  have hsquare : (k : ℝ) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hk 2
  have hscale := mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg d : 0 ≤ (d : ℝ))
  have hone : (1 : ℝ) ≤ r ^ 2 := one_le_pow₀ hr
  rw [← hrsq]
  have hcount' : (distinctDistances P : ℝ) ≤ (d : ℝ) * (k : ℝ) ^ 2 + 1 := by exact_mod_cast hcount
  linarith


theorem minimum_bounds {X : Type*} [MetricSpace X] {c C a : ℝ}
    (lower : ∀ P : Finset X, 2 ≤ P.card →
      c * (P.card : ℝ) ^ a ≤ (distinctDistances P : ℝ))
    (upper : ∀ n : ℕ, 2 ≤ n → ∃ P : Finset X, P.card = n ∧
      (distinctDistances P : ℝ) ≤ C * (n : ℝ) ^ a)
    (n : ℕ) (hn : 2 ≤ n) :
    c * (n : ℝ) ^ a ≤ (minimalDistinctDistances X n : ℝ) ∧
      (minimalDistinctDistances X n : ℝ) ≤ C * (n : ℝ) ^ a := by
  obtain ⟨P, hP, hupper⟩ := upper n hn
  let counts : Set ℕ := {m | ∃ Q : Finset X, Q.card = n ∧ distinctDistances Q = m}
  have hPmem : distinctDistances P ∈ counts := ⟨P, hP, rfl⟩
  have hattained : sInf counts ∈ counts := Nat.sInf_mem ⟨_, hPmem⟩
  obtain ⟨Q, hQ, hmin⟩ := hattained
  change c * (n : ℝ) ^ a ≤ ((sInf counts : ℕ) : ℝ) ∧
    ((sInf counts : ℕ) : ℝ) ≤ C * (n : ℝ) ^ a
  constructor
  · have h := lower Q (hQ.symm ▸ hn)
    simpa only [hQ, hmin] using h
  · have hle : sInf counts ≤ distinctDistances P := Nat.sInf_le hPmem
    exact (Nat.cast_le.mpr hle).trans hupper

open Filter Asymptotics
open scoped Topology

/-- Multiplicative constants in a two-sided power law contribute a vanishing exponent. -/
theorem exponent_of_bounds {F : ℕ → ℝ} {a c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (h : ∀ n : ℕ, 2 ≤ n → c * (n : ℝ) ^ a ≤ F n ∧ F n ≤ C * (n : ℝ) ^ a) :
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ n : ℕ in atTop, F n = (n : ℝ) ^ (a - o n) := by
  let e := fun n : ℕ => a * Real.log n - Real.log (F n)
  have hlog : ∀ᶠ n : ℕ in atTop, -Real.log C ≤ e n ∧ e n ≤ -Real.log c := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hp := Real.rpow_pos_of_pos hn' a
    obtain ⟨hl, hu⟩ := h n hn
    have hFl := Real.log_le_log ((mul_pos hc hp)) hl
    have hFu := Real.log_le_log ((mul_pos hc hp).trans_le hl) hu
    rw [Real.log_mul hc.ne' hp.ne', Real.log_rpow hn'] at hFl
    rw [Real.log_mul hC.ne' hp.ne', Real.log_rpow hn'] at hFu
    dsimp [e]
    constructor <;> linarith
  refine ⟨fun n => e n / Real.log n, (isLittleO_one_iff ℝ).mpr ?_, ?_⟩
  · exact tendsto_bdd_div_atTop_nhds_zero (hlog.mono fun _ h' => h'.1)
      (hlog.mono fun _ h' => h'.2) (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    have hlogn := (Real.log_pos hn').ne'
    have hFn := (mul_pos hc (Real.rpow_pos_of_pos (zero_lt_one.trans hn') a)).trans_le (h n hn).1
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hn'), ← Real.exp_log hFn]
    apply congrArg Real.exp
    dsimp [e]
    field_simp [hlogn]
    ring

theorem main : H1 → H2 → type_of% @Erdos1083.erdos_1083 := by
  intro hbase hsparse d hd
  obtain ⟨c, hc, hl⟩ := dimensional_lower hbase hsparse d hd
  obtain ⟨C, hC, hu⟩ := grid_upper d hd
  exact exponent_of_bounds hc hC (minimum_bounds hl hu)

end OMA.R_Erdos1083_erdos_1083_R2
