import FormalConjectures.ErdosProblems.«506»

open EuclideanGeometry

namespace OMA.Segre

def x : Fin 8 → ℤ := ![-1, -1, 1, 1, -2, -2, 2, 2]
def y : Fin 8 → ℤ := ![-1, 1, -1, 1, -2, 2, -2, 2]

def den : Fin 18 → ℤ := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]
def cu : Fin 18 → ℤ := ![-6, -3, -3, -2, 0, 0, 0, 0, 0, 0, 2, 3, 3, 6, -3, -3, 3, 3]
def cv : Fin 18 → ℤ := ![0, -3, 3, 0, -6, -2, 0, 0, 2, 6, 0, -3, 3, 0, -3, 3, -3, 3]
def cw : Fin 18 → ℤ := ![-4, 8, 8, 4, -4, 4, 2, 8, 4, -4, 4, 8, 8, -4, 4, 4, 4, 4]

def q (i : Fin 8) : ℤ := x i ^ 2 + y i ^ 2

def det (i j k : Fin 8) : ℤ :=
  (x j - x i) * (y k - y i) - (x k - x i) * (y j - y i)

def uNum (i j k : Fin 8) : ℤ :=
  (q j - q i) * (y k - y i) - (q k - q i) * (y j - y i)

def vNum (i j k : Fin 8) : ℤ :=
  (x j - x i) * (q k - q i) - (x k - x i) * (q j - q i)

def wNum (i j k : Fin 8) : ℤ :=
  q i * det i j k - x i * uNum i j k - y i * vNum i j k

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem table : ∀ i j k : Fin 8, i ≠ j → i ≠ k → j ≠ k →
    uNum i j k ≠ 0 ∨ vNum i j k ≠ 0 ∨ det i j k ≠ 0 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem tableCover : ∀ i j k : Fin 8, i ≠ j → i ≠ k → j ≠ k → det i j k ≠ 0 →
    ∃ m : Fin 18, den m ≠ 0 ∧
      uNum i j k * den m = cu m * det i j k ∧
      vNum i j k * den m = cv m * det i j k ∧
      wNum i j k * den m = cw m * det i j k := by decide

def point (i : Fin 8) : EuclideanSpace ℝ (Fin 2) := !₂[(x i : ℝ), (y i : ℝ)]

theorem point_injective : Function.Injective point := by
  have hc : ∀ i j : Fin 8, x i = x j → y i = y j → i = j := by decide
  intro i j h
  exact hc i j
    (Int.cast_injective (congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h))
    (Int.cast_injective (congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) h))

def pts : Finset (EuclideanSpace ℝ (Fin 2)) :=
  Finset.univ.map ⟨point, point_injective⟩

theorem mem_pts (i : Fin 8) : point i ∈ pts := by simp [pts]

theorem pts_indices {p : EuclideanSpace ℝ (Fin 2)} (h : p ∈ pts) :
    ∃ i : Fin 8, point i = p := by simpa [pts] using h

theorem circleEquation (s : Sphere (EuclideanSpace ℝ (Fin 2))) (i : Fin 8) (hi : point i ∈ s) :
    (q i : ℝ) =
      (x i : ℝ) * (2 * s.center 0) + (y i : ℝ) * (2 * s.center 1) +
        (s.radius ^ 2 - (s.center 0) ^ 2 - (s.center 1) ^ 2) := by
  have h := EuclideanSpace.dist_sq_eq (point i) s.center
  rw [mem_sphere.mp hi, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq,
    sq_abs, sq_abs] at h
  change s.radius ^ 2 = ((x i : ℝ) - s.center 0) ^ 2 + ((y i : ℝ) - s.center 1) ^ 2 at h
  push_cast [q]
  linear_combination -h

theorem pts_not_cospherical : ¬ Cospherical (pts : Set (EuclideanSpace ℝ (Fin 2))) := by
  rw [cospherical_iff_exists_sphere]
  rintro ⟨s, hs⟩
  have h0 := circleEquation s 0 (hs (mem_pts 0))
  have h3 := circleEquation s 3 (hs (mem_pts 3))
  have h7 := circleEquation s 7 (hs (mem_pts 7))
  norm_num [q, show x 0 = -1 by decide, show y 0 = -1 by decide,
    show x 3 = 1 by decide, show y 3 = 1 by decide,
    show x 7 = 2 by decide, show y 7 = 2 by decide] at h0 h3 h7
  linarith

theorem pts_not_collinear : ¬ Collinear ℝ (pts : Set (EuclideanSpace ℝ (Fin 2))) := by
  rw [collinear_iff_of_mem (mem_pts 0)]
  rintro ⟨v, hv⟩
  obtain ⟨a, ha⟩ := hv (point 1) (mem_pts 1)
  obtain ⟨b, hb⟩ := hv (point 2) (mem_pts 2)
  have ha0 := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) ha
  have ha1 := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) ha
  have hb0 := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) hb
  change (x 1 : ℝ) = a * v 0 + (x 0 : ℝ) at ha0
  change (y 1 : ℝ) = a * v 1 + (y 0 : ℝ) at ha1
  change (x 2 : ℝ) = b * v 0 + (x 0 : ℝ) at hb0
  norm_num [x, y] at ha0 ha1
  have hane : a ≠ 0 := by intro h; norm_num [h] at ha1
  have hv0 := ha0.resolve_left hane
  norm_num [show x 2 = 1 by decide, show x 0 = -1 by decide, hv0] at hb0

noncomputable def candidate (m : Fin 18) : Sphere (EuclideanSpace ℝ (Fin 2)) :=
  let u : ℝ := (cu m : ℝ) / (den m : ℝ)
  let v : ℝ := (cv m : ℝ) / (den m : ℝ)
  let w : ℝ := (cw m : ℝ) / (den m : ℝ)
  ⟨!₂[u / 2, v / 2], Real.sqrt (w + (u / 2)^2 + (v / 2)^2)⟩

theorem circleInTable (s : Sphere (EuclideanSpace ℝ (Fin 2))) (i j k : Fin 8)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : point i ∈ s) (hj : point j ∈ s) (hk : point k ∈ s) :
    s ∈ Set.range candidate := by
  let U := 2 * s.center 0
  let V := 2 * s.center 1
  let W := s.radius ^ 2 - (s.center 0) ^ 2 - (s.center 1) ^ 2
  have e₁ : (q i : ℝ) = (x i : ℝ) * U + (y i : ℝ) * V + W := circleEquation s i hi
  have e₂ : (q j : ℝ) = (x j : ℝ) * U + (y j : ℝ) * V + W := circleEquation s j hj
  have e₃ : (q k : ℝ) = (x k : ℝ) * U + (y k : ℝ) * V + W := circleEquation s k hk
  have hU : (uNum i j k : ℝ) = U * (det i j k : ℝ) := by
    push_cast [uNum, det]
    linear_combination ((y k : ℝ) - y i) * (e₂ - e₁) - ((y j : ℝ) - y i) * (e₃ - e₁)
  have hV : (vNum i j k : ℝ) = V * (det i j k : ℝ) := by
    push_cast [vNum, det]
    linear_combination ((x j : ℝ) - x i) * (e₃ - e₁) - ((x k : ℝ) - x i) * (e₂ - e₁)
  have hW : (wNum i j k : ℝ) = W * (det i j k : ℝ) := by
    push_cast [wNum]
    rw [hU, hV, e₁]
    ring
  have hd : det i j k ≠ 0 := by
    intro h
    have hd' : (det i j k : ℝ) = 0 := by exact_mod_cast h
    rw [hd', mul_zero] at hU hV
    exact (table i j k hij hik hjk).elim (fun hn => hn (by exact_mod_cast hU))
      (fun h' => h'.elim (fun hn => hn (by exact_mod_cast hV)) (fun hn => hn h))
  obtain ⟨m, hm, hu, hv, hw⟩ := tableCover i j k hij hik hjk hd
  have hd' : (det i j k : ℝ) ≠ 0 := by exact_mod_cast hd
  have hm' : (den m : ℝ) ≠ 0 := by exact_mod_cast hm
  have cancel {a b z : ℝ} (h₁ : a = z * det i j k)
      (h₂ : a * den m = b * det i j k) : b / den m = z := by
    apply (div_eq_iff hm').2
    apply mul_right_cancel₀ hd'
    rw [← h₂, h₁]
    ring
  have hu' : (cu m : ℝ) / den m = U := cancel hU (by exact_mod_cast hu)
  have hv' : (cv m : ℝ) / den m = V := cancel hV (by exact_mod_cast hv)
  have hw' : (cw m : ℝ) / den m = W := cancel hW (by exact_mod_cast hw)
  refine ⟨m, Sphere.ext ?_ ?_⟩
  · dsimp [candidate]
    rw [hu', hv']
    ext a
    fin_cases a
    · change U / 2 = s.center 0
      dsimp [U]
      ring
    · change V / 2 = s.center 1
      dsimp [V]
      ring
  · dsimp [candidate]
    rw [hw', hu', hv']
    have heq : W + (U/2)^2 + (V/2)^2 = s.radius ^ 2 := by dsimp [U, V, W]; ring
    rw [heq, Real.sqrt_sq (mem_sphere.mp hi ▸ dist_nonneg)]

end OMA.Segre

open OMA.Segre

theorem OMA.solution : type_of% @Erdos506.erdos_506.variants.segre_n_eq_eight := by
  refine ⟨pts, by simp [pts], pts_not_collinear, pts_not_cospherical, ?_⟩
  have hsub : {s : Sphere (EuclideanSpace ℝ (Fin 2)) |
      3 ≤ {p ∈ (pts : Set (EuclideanSpace ℝ (Fin 2))) | p ∈ s}.ncard} ⊆ Set.range candidate := by
    intro s hs
    have hf : {p ∈ (pts : Set (EuclideanSpace ℝ (Fin 2))) | p ∈ s}.Finite :=
      pts.finite_toSet.subset (fun _ h => h.1)
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff hf).1 hs
    obtain ⟨i, rfl⟩ := pts_indices ha.1
    obtain ⟨j, rfl⟩ := pts_indices hb.1
    obtain ⟨k, rfl⟩ := pts_indices hc.1
    exact circleInTable s i j k (fun h => hab (congrArg point h))
      (fun h => hac (congrArg point h)) (fun h => hbc (congrArg point h)) ha.2 hb.2 hc.2
  unfold Erdos506.numCircles
  have hrange : (Set.range candidate).ncard ≤ 18 := by
    rw [← Set.image_univ]
    exact (Set.ncard_image_le (Set.toFinite _)).trans (by simp)
  have hbound := (Set.ncard_le_ncard hsub (Set.finite_range _)).trans hrange
  exact hbound.trans_lt (by decide)
