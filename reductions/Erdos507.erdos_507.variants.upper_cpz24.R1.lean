import FormalConjectures.ErdosProblems.«507»

/-!
# From short pairs and off-diagonal incidences to the Heilbronn bound

The two hypotheses use the same ambient size n. The first is an elementary
packing problem in the disk. The second is the assigned-line estimate of
Cohen, Pohoata and Zakharov, in coordinate distance, with floor(n/8) points.
The determinant argument below eliminates the parameter along the line.
-/

namespace OMA.R_Erdos507_erdos_507_variants_upper_cpz24_R1

open Asymptotics Filter Topology Erdos507
open scoped EuclideanGeometry

private lemma area_of_near_line (a b c : ℝ²) (t s r : ℝ)
    (hs : ∀ k : Fin 2, |b k - a k| ≤ s)
    (hr : ∀ k : Fin 2, |c k - a k - t * (b k - a k)| ≤ r) :
    |EuclideanGeometry.triangle_area a b c| ≤ s * r := by
  have hs0 : 0 ≤ s := (abs_nonneg _).trans (hs 0)
  have prod (j k : Fin 2) :
      |(b j - a j) * (c k - a k - t * (b k - a k))| ≤ s * r := by
    rw [abs_mul]
    exact mul_le_mul (hs j) (hr k) (abs_nonneg _) hs0
  have hdet : EuclideanGeometry.triangle_area a b c =
      ((b 0 - a 0) * (c 1 - a 1 - t * (b 1 - a 1)) -
       (b 1 - a 1) * (c 0 - a 0 - t * (b 0 - a 0))) / 2 := by
    rw [EuclideanGeometry.triangle_area_eq_det, Matrix.det_fin_three]
    simp
    ring
  rw [hdet, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), div_le_iff₀ (by norm_num)]
  refine (abs_sub _ _).trans ?_
  linarith [prod 0 1, prod 1 0]

private lemma triple_injective {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    Function.Injective (![(j, false), (j, true), (i, false)] : Fin 3 → Fin m × Bool) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | rfl | simp [hij, Ne.symm hij] at hab

/-- A positive fraction of the points can be paired disjointly with both
coordinate differences of each pair of order at most the inverse square root. -/
def H1 : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℝ²,
    S.card = n → (S : Set ℝ²) ⊆ Metric.closedBall 0 1 →
    ∃ p : (Fin (n / 8) × Bool) ↪ ℝ², (∀ k, p k ∈ S) ∧
      ∀ j (k : Fin 2), |p (j, true) k - p (j, false) k| ≤ A / (n : ℝ) ^ ((1 : ℝ) / 2)

/-- Among distinct points, each assigned a nonzero line direction, some point
is close to a different point's line. The two inequalities measure distance in
the coordinate maximum norm. The line directions need no normalization. -/
def H2 : Prop :=
  ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∃ B : ℝ, 0 < B ∧
    ∀ᶠ n : ℕ in atTop, ∀ x d : Fin (n / 8) → ℝ²,
      Function.Injective x → (∀ i, x i ∈ Metric.closedBall 0 1) → (∀ i, d i ≠ 0) →
      ∃ i j, i ≠ j ∧ ∃ t : ℝ, ∀ k : Fin 2,
        |x i k - x j k - t * d j k| ≤ B / (n : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ e n

theorem main : H1 → H2 → type_of% @Erdos507.erdos_507.variants.upper_cpz24 := by
  classical
  rintro ⟨A, hA, hpack⟩ ⟨e, he, B, hB, hnear⟩
  refine ⟨e, he, Asymptotics.IsBigO.of_bound (A * B) ?_⟩
  filter_upwards [hpack, hnear, eventually_ge_atTop (1 : ℕ)] with n pack near hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hα : 0 ≤ α n :=
    Real.sSup_nonneg fun _ ⟨_, _, h⟩ => h ▸ Real.sInf_nonneg fun _ ⟨_, _, _, h'⟩ => h' ▸ abs_nonneg _
  change ‖α n‖ ≤ A * B * ‖upperBarrier n * (n : ℝ) ^ e n‖
  have hbarr : 0 ≤ upperBarrier n := by unfold upperBarrier; positivity
  rw [Real.norm_of_nonneg hα, Real.norm_of_nonneg (mul_nonneg hbarr (Real.rpow_pos_of_pos hn0 _).le)]
  refine Real.sSup_le ?_ (mul_nonneg (mul_nonneg hA.le hB.le)
    (mul_nonneg hbarr (Real.rpow_pos_of_pos hn0 _).le))
  rintro _ ⟨S, ⟨hcard, hdisk, _⟩, rfl⟩
  obtain ⟨p, hmem, hshort⟩ := pack S hcard hdisk
  let x : Fin (n / 8) → ℝ² := fun i => p (i, false)
  let y : Fin (n / 8) → ℝ² := fun i => p (i, true)
  have hinj : Function.Injective x := fun _ _ h => congrArg Prod.fst (p.injective h)
  have hdir : ∀ i, y i - x i ≠ 0 := by
    intro i hz
    have h : (i, true) = (i, false) := p.injective (sub_eq_zero.mp hz)
    simpa using congrArg Prod.snd h
  obtain ⟨i, j, hij, t, hline⟩ :=
    near x (fun i => y i - x i) hinj (fun i => hdisk (hmem (i, false))) hdir
  let v : Fin 3 → Fin (n / 8) × Bool := ![(j, false), (j, true), (i, false)]
  have hv : Function.Injective v := triple_injective i j hij
  have hmin : minTriangleArea S ≤ |EuclideanGeometry.triangle_area (x j) (y j) (x i)| :=
    csInf_le ⟨0, by rintro _ ⟨_, _, _, rfl⟩; exact abs_nonneg _⟩
      ⟨fun k => p (v k), p.injective.comp hv, fun k => hmem (v k), rfl⟩
  refine hmin.trans ((area_of_near_line (x j) (y j) (x i) t _ _ (hshort j)
    (fun k => by simpa only [PiLp.sub_apply] using hline k)).trans_eq ?_)
  have hexp : (n : ℝ) ^ ((7 : ℝ) / 6) =
      (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_add hn0]
    norm_num
  rw [upperBarrier, hexp]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end OMA.R_Erdos507_erdos_507_variants_upper_cpz24_R1
