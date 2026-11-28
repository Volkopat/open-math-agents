import OMAStatements.S_mo_157184
import Mathlib

/-
Lan, Hu and Sun, Theorem 1.2 (arXiv:1903.03917), give divergent iterates
of conditional expectation. The finite projection words of Kopecká and
Paszkiewicz (arXiv:1508.05029) motivate the line selection used here.

The samples consist of independent Gaussian coordinates, a discrete label
for each stage, and an independent uniform threshold. In a selected pair
of Gaussian coordinates, reflection averages project onto the line chosen
by its label when the threshold is sufficiently small. Forgetting the
threshold repeats a controllable damping on the perpendicular line.
Forgetting the labels then averages these dampings into a plane operator.
Powers of this operator approximate each of a sequence of line projections
carrying one coordinate almost to the next. Alternating even and odd pairs
lets the same fields act throughout the infinite schedule.
-/

namespace ProjectionWords

def cut {ι : Type*} (w : ℕ → List ι) : ℕ → ℕ
  | 0 => 0
  | n + 1 => cut w n + (w n).length

theorem cut_strictMono {ι : Type*} {w : ℕ → List ι} (hw : ∀ n, (w n) ≠ []) :
    StrictMono (cut w) := by
  apply strictMono_nat_of_lt_succ
  intro n
  simpa [cut] using List.length_pos_iff.mpr (hw n)

noncomputable def schedule {ι : Type*} [Inhabited ι] (w : ℕ → List ι)
    (hw : ∀ n, w n ≠ []) : ℕ → ι
  | 0 => default
  | t+1 =>
    let n := Nat.find (show ∃ n, t < cut w (n+1) from
      ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) ((cut_strictMono hw).id_le (t+1))⟩)
    (w n)[t - cut w n]?.getD default

theorem schedule_at {ι : Type*} [Inhabited ι] {w : ℕ → List ι}
    (hw : ∀ n, w n ≠ []) (n j : ℕ) (hj : j < (w n).length) :
    schedule w hw (cut w n + j + 1) = (w n)[j] := by
  unfold schedule
  dsimp only
  have hit : cut w n + j < cut w (n+1) := by simpa [cut] using hj
  have hex : ∃ m, cut w n + j < cut w (m+1) := ⟨n, hit⟩
  have hn : Nat.find (p := fun m => cut w n + j < cut w (m+1)) hex = n := by
    apply le_antisymm (Nat.find_min' hex hit)
    apply Nat.le_of_not_gt
    intro he
    have hle := (cut_strictMono hw).monotone (Nat.succ_le_of_lt he)
    have hlt := Nat.find_spec (p := fun m => cut w n + j < cut w (m+1)) hex
    exact (not_lt_of_ge (hle.trans (Nat.le_add_right _ _))) hlt
  simp [hn, hj]

theorem fold_from {ι E : Type*} (T : ι → E → E) (x : ℕ → E) (t : ℕ)
    (w : List ι)
    (h : ∀ j (hj : j < w.length), x (t+j+1) = T w[j] (x (t+j))) :
    x (t+w.length) = w.foldl (fun v i => T i v) (x t) := by
  induction w generalizing t with
  | nil => simp
  | cons a w ih =>
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    simp only [List.length_cons, List.foldl_cons]
    rw [show t + (w.length + 1) = (t+1) + w.length by omega, ← h0]
    apply ih
    intro j hj
    have hh := h (j+1) (by simpa using hj)
    rw [List.getElem_cons_succ] at hh
    simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hh

theorem fold_dist {ι E : Type*} [PseudoMetricSpace E] (T : ι → E → E)
    (hT : ∀ i x y, dist (T i x) (T i y) ≤ dist x y) (w : List ι) (x y : E) :
    dist (w.foldl (fun v i => T i v) x) (w.foldl (fun v i => T i v) y) ≤ dist x y := by
  induction w generalizing x y with
  | nil => rfl
  | cons i w ih => exact (ih _ _).trans (hT i x y)

theorem separated_orbit {ι E : Type*} [Inhabited ι] [PseudoMetricSpace E]
    (T : ι → E → E) (hT : ∀ i x y, dist (T i x) (T i y) ≤ dist x y)
    (w : ℕ → List ι) (hw : ∀ n, w n ≠ []) (e : ℕ → E)
    (move : ∀ n, dist ((w n).foldl (fun v i => T i v) (e n)) (e (n+1)) ≤
      (1/16 : ℝ) * (1/2 : ℝ)^n)
    (sep : ∀ n, 5/4 ≤ dist (e n) (e (n+1)))
    (x : ℕ → E) (x0 : x 0 = e 0)
    (step : ∀ t, x (t+1) = T (schedule w hw (t+1)) (x t)) :
    ∀ N, ∃ i ≥ N, ∃ j ≥ N, 1 < dist (x i) (x j) := by
  have near (n : ℕ) : dist (x (cut w n)) (e n) ≤ (1/8 : ℝ) * (1 - (1/2 : ℝ)^n) := by
    induction n with
    | zero => simp [cut, x0]
    | succ n ih =>
      have walk := fold_from T x (cut w n) (w n) (fun j hj => by
        rw [step, schedule_at hw n j hj])
      change dist (x (cut w n + (w n).length)) _ ≤ _
      rw [walk]
      have ht := dist_triangle
        ((w n).foldl (fun v i => T i v) (x (cut w n)))
        ((w n).foldl (fun v i => T i v) (e n)) (e (n+1))
      have hb := (fold_dist T hT (w n) _ _).trans ih
      rw [pow_succ]
      linarith [move n]
  intro N
  refine ⟨cut w N, (cut_strictMono hw).id_le _, cut w (N+1),
    (Nat.le_succ N).trans ((cut_strictMono hw).id_le _), ?_⟩
  have h := dist_triangle4 (e N) (x (cut w N)) (x (cut w (N+1))) (e (N+1))
  rw [dist_comm (e N) (x (cut w N))] at h
  have hp : 0 < (1/2 : ℝ)^N := by positivity
  have hp' : 0 < (1/2 : ℝ)^(N+1) := by positivity
  linarith [near N, near (N+1), sep N]

end ProjectionWords


open MeasureTheory
namespace Wave9Z
variable {Ω : Type*} [m : MeasurableSpace Ω]

/-- The ambient measurable events fixed by preimage under a reflection. -/
abbrev fixedEvents (τ : Ω → Ω) : MeasurableSpace Ω where
  MeasurableSet' s := MeasurableSet s ∧ τ ⁻¹' s = s
  measurableSet_empty := ⟨MeasurableSet.empty, rfl⟩
  measurableSet_compl _ h := ⟨h.1.compl, by rw [Set.preimage_compl, h.2]⟩
  measurableSet_iUnion f h := ⟨MeasurableSet.iUnion (fun i => (h i).1), by
    rw [Set.preimage_iUnion]
    exact congrArg Set.iUnion (funext fun i => (h i).2)⟩

theorem fixedEvents_le (τ : Ω → Ω) : fixedEvents τ ≤ m := fun _ hs => hs.1

theorem reflection_average (μ : Measure Ω) [IsProbabilityMeasure μ] (τ : Ω → Ω)
    (hτ : Function.Involutive τ) (hp : MeasurePreserving τ μ μ)
    (f : Ω → ℝ) (hf : Measurable f) (hi : Integrable f μ) :
    (fun x => (1/2 : ℝ) * (f x + f (τ x))) =ᵐ[μ] μ[f | fixedEvents τ] := by
  let g := fun x => (1/2 : ℝ) * (f x + f (τ x))
  have hg : Measurable g := measurable_const.mul (hf.add (hf.comp hp.measurable))
  have hgm : Measurable[fixedEvents τ] g := by
    intro s hs
    refine ⟨hg hs, ?_⟩
    ext x
    change (1/2 : ℝ) * (f (τ x) + f (τ (τ x))) ∈ s ↔ (1/2 : ℝ) * (f x + f (τ x)) ∈ s
    rw [hτ x, add_comm (f (τ x))]
  have hc := hp.integrable_comp_of_integrable hi
  have hgint : Integrable g μ := (hi.add hc).const_mul _
  apply ae_eq_condExp_of_forall_setIntegral_eq (fixedEvents_le τ) hi
  · exact fun _ _ _ => hgint.integrableOn
  · intro s hs _
    have hem := (MeasurableEquiv.ofInvolutive τ hτ hp.measurable).measurableEmbedding
    have heq := hp.setIntegral_preimage_emb hem f s
    rw [show τ ⁻¹' s = s from hs.2] at heq
    have hiτ : Integrable (fun x => f (τ x)) μ := hc
    rw [integral_const_mul, integral_add hi.integrableOn hiτ.integrableOn, heq]
    ring
  · exact hgm.stronglyMeasurable.aestronglyMeasurable

end Wave9Z

open MeasureTheory Filter Topology
namespace Wave9Z
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Late pairs bounded away from zero refute the exact eLpNorm limit in the root. -/
theorem reject_limit {f : ℕ → Ω → ℝ} (hf : ∀ n, MemLp (f n) 2 μ)
    (hgap : ∀ N : ℕ, ∃ i ≥ N, ∃ j ≥ N, 1 ≤ eLpNorm (f i - f j) 2 μ) :
    ¬ ∃ y : Ω → ℝ, MemLp y 2 μ ∧ Tendsto (fun k => eLpNorm (f k - y) 2 μ) atTop (𝓝 0) := by
  rintro ⟨y, hy, hlim⟩
  have hev := hlim.eventually_lt_const (show (0:ENNReal) < 1/2 by norm_num)
  obtain ⟨N,hN⟩ := eventually_atTop.1 hev
  obtain ⟨i,hi,j,hj,hij⟩ := hgap N
  have h₁ := hN i hi
  have h₂ := hN j hj
  have heq : f i - f j = (f i-y) - (f j-y) := by abel
  rw [heq] at hij
  have hle := hij.trans (eLpNorm_sub_le ((hf i).sub hy).1 ((hf j).sub hy).1 (by norm_num))
  have hlt := ENNReal.add_lt_add h₁ h₂
  rw [ENNReal.add_halves] at hlt
  exact (not_lt_of_ge hle) hlt

end Wave9Z

open ProbabilityTheory MeasureTheory
namespace Wave9Z

theorem orthogonal_blocks {I : Type*} {d : I → ℕ}
    (U : (i : I) → EuclideanSpace ℝ (Fin (d i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d i))) :
    MeasurePreserving (fun x i => U i (x i))
      (Measure.infinitePi fun i => stdGaussian (EuclideanSpace ℝ (Fin (d i))))
      (Measure.infinitePi fun i => stdGaussian (EuclideanSpace ℝ (Fin (d i)))) where
  measurable := measurable_pi_lambda _ fun i => (U i).continuous.measurable.comp (measurable_pi_apply i)
  map_eq := by
    rw [Measure.infinitePi_map_pi _ (fun i => (U i).continuous.measurable)]
    simp_rw [stdGaussian_map]

theorem second_moment {J : Type*} [Fintype J] (v : EuclideanSpace ℝ J) :
    ∫ x, (inner ℝ v x)^2 ∂(stdGaussian (EuclideanSpace ℝ J)) = ‖v‖^2 := by
  let L := innerSL ℝ v
  have h := variance_dual_stdGaussian L
  rw [variance_eq_integral (by fun_prop), integral_strongDual_stdGaussian] at h
  simpa [L] using h

end Wave9Z

namespace Wave9Z

theorem lost_upper {d : ℝ} (h₁ : d ≤ 1) (s : ℕ) :
    1 - (1-d)^s ≤ s*d := by
  have h := one_add_mul_le_pow (a := -d) (by linarith) s
  rw [← sub_eq_add_neg] at h
  linarith

theorem survival {d : ℝ} (h₀ : 0 ≤ d) (h₁ : d ≤ 1) (s : ℕ) :
    (1-d)^s * (1 + s*d) ≤ 1 := by
  calc
    _ ≤ (1-d)^s * (1+d)^s := by
      gcongr
      exact one_add_mul_le_pow (by linarith) _
    _ = ((1-d)*(1+d))^s := (mul_pow ..).symm
    _ ≤ 1 := pow_le_one₀ (mul_nonneg (by linarith) (by linarith)) (by nlinarith [sq_nonneg d])

theorem selected_loss {d : ℝ} (h₀ : 0 ≤ d) (h₁ : d ≤ 1) (s : ℕ) (hs : s*d = 1) :
    1/2 ≤ 1 - (1-d)^s := by
  have h := survival h₀ h₁ s
  rw [hs] at h
  linarith

theorem suppress_line {c R : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1) (r : ℕ)
    (hR : R ≤ (r:ℝ)*c) (hR' : 0 ≤ R) : (1-c)^r ≤ 1 / (1+R) := by
  apply (le_div_iff₀ (by linarith)).2
  exact (mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (by linarith) r)).trans
    (survival hc hc' r)

noncomputable def ux (t : ℝ) := (1-t^2)/(1+t^2)
noncomputable def uy (t : ℝ) := 2*t/(1+t^2)

theorem chord (s t : ℝ) :
    1 - (ux s * ux t + uy s * uy t) = 2*(s-t)^2 / ((1+s^2)*(1+t^2)) := by
  unfold ux uy
  field_simp
  ring

theorem dot_loss (s t : ℝ) :
    1 - (ux s * ux t + uy s * uy t) ≤ 2*(s-t)^2 := by
  rw [chord]
  apply div_le_self (by positivity)
  nlinarith [sq_nonneg s, sq_nonneg t, mul_nonneg (sq_nonneg s) (sq_nonneg t)]

end Wave9Z

namespace Wave9Z

/-- Rewrite exponents using distances h=j−i, l=k−j.
    The window before the selected axis costs at most R/A after amplification. -/
theorem earlier_axis (R A : ℝ) (hR : 0 ≤ R) (hA : 1 ≤ A) (i h l : ℕ) :
    (R*A^(i+(h+1))) * (1/A^i) * ((A^2)^l / (A^2)^((h+1)+l)) ≤ R/A := by
  have hpos : 0 < A := by linarith
  have heq : (R*A^(i+(h+1))) * (1/A^i) * ((A^2)^l / (A^2)^((h+1)+l)) =
      (R/A)/(A^h) := by
    simp only [pow_add, pow_succ]
    field_simp
    ring
  rw [heq]
  apply div_le_self (by positivity) (one_le_pow₀ hA)

theorem later_axis (R A : ℝ) (hR : 0 ≤ R) (hA : 1 ≤ A) (j h : ℕ) :
    (R*A^j) * (1/A^(j+(h+1))) ≤ R/A := by
  have hpos : 0 < A := by linarith
  have heq : (R*A^j) * (1/A^(j+(h+1))) = (R/A)/(A^h) := by
    simp only [pow_add, pow_succ]
    field_simp
  rw [heq]
  apply div_le_self (by positivity) (one_le_pow₀ hA)

end Wave9Z

namespace Wave9Z
abbrev Op (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E →L[ℝ] E

/-- Total leakage in the compressed plane if each undesired term has size at most b. -/
theorem leakage {E : Type*} [NormedAddCommGroup E] {I : Type*} [Fintype I] [DecidableEq I] (j : I) (v : I → E) (x : E)
    (b : ℝ) (hb : 0 ≤ b) (hv : ∀ i, i ≠ j → ‖v i‖ ≤ b) :
    ‖(x - ∑ i, v i) - (x - v j)‖ ≤ Fintype.card I * b := by
  have hremove := Finset.sum_erase_add (s := (Finset.univ : Finset I)) v (Finset.mem_univ j)
  rw [← hremove, show x - ((∑ i ∈ Finset.univ.erase j, v i) + v j) - (x-v j) =
    -(∑ i ∈ Finset.univ.erase j, v i) by abel, norm_neg]
  calc
    _ ≤ ∑ i ∈ Finset.univ.erase j, ‖v i‖ := norm_sum_le ..
    _ ≤ ∑ _i ∈ Finset.univ.erase j, b := Finset.sum_le_sum fun i hi => hv i (Finset.ne_of_mem_erase hi)
    _ ≤ ∑ _i : I, b := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset ..) (fun _ _ _ => hb)
    _ = _ := by simp

end Wave9Z

namespace Wave9Z
open Finset

theorem perturb_power {A : Type*} [NormedRing A] [NormOneClass A]
    (a b : A) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖a^n-b^n‖ ≤ n * ‖a-b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hbn : ‖b^n‖ ≤ 1 := (norm_pow_le ..).trans (pow_le_one₀ (norm_nonneg _) hb)
    rw [pow_succ, pow_succ, show a^n*a-b^n*b = (a^n-b^n)*a + b^n*(a-b) by noncomm_ring]
    calc
      _ ≤ ‖(a^n-b^n)*a‖ + ‖b^n*(a-b)‖ := norm_add_le ..
      _ ≤ ‖a^n-b^n‖ * ‖a‖ + ‖b^n‖ * ‖a-b‖ := add_le_add (norm_mul_le ..) (norm_mul_le ..)
      _ ≤ ((n:ℝ)*‖a-b‖)*1 + 1*‖a-b‖ := by gcongr
      _ = _ := by push_cast; ring

end Wave9Z

namespace ProjectionWords
open MeasureTheory Filter Topology

noncomputable def condition {Ω : Type} {G : MeasurableSpace Ω} [m : MeasurableSpace Ω] (μ : Measure Ω)
    (hG : G ≤ m) (f : Ω →₂[μ] ℝ) : Ω →₂[μ] ℝ :=
  condExpL2 ℝ ℝ hG f

theorem condition_dist {Ω : Type} {G : MeasurableSpace Ω} [m : MeasurableSpace Ω] (μ : Measure Ω)
    (hG : G ≤ m) (f g : Ω →₂[μ] ℝ) :
    dist (condition μ hG f) (condition μ hG g) ≤ dist f g := by
  rw [_root_.dist_eq_norm, _root_.dist_eq_norm]
  exact (show ‖condExpL2 ℝ ℝ hG f - condExpL2 ℝ ℝ hG g‖ ≤ ‖f-g‖ from
    by rw [← map_sub]; exact norm_condExpL2_le _ _)

theorem condition_ae {Ω : Type} {G : MeasurableSpace Ω} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (hG : G ≤ m) (f : Ω →₂[μ] ℝ) :
    (condition μ hG f : Ω → ℝ) =ᵐ[μ] μ[⇑f | G] := by
  have h := (Lp.memLp f).condExpL2_ae_eq_condExp (𝕜 := ℝ) hG
  simpa [condition] using h

theorem disproof_of_local_words {Ω : Type} [m : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (G : Fin 6 → MeasurableSpace Ω) (hG : ∀ i, G i ≤ m)
    (w : ℕ → List (Fin 6)) (hw : ∀ n, w n ≠ []) (e : ℕ → Ω →₂[μ] ℝ)
    (move : ∀ n, dist ((w n).foldl (fun v i => condition μ (hG i) v) (e n)) (e (n+1)) ≤
      (1/16 : ℝ) * (1/2 : ℝ)^n)
    (sep : ∀ n, 5/4 ≤ dist (e n) (e (n+1))) :
    ¬ (type_of% @OMA.S_mo_157184.main) := by
  intro hall
  let s := schedule w hw
  let x : ℕ → Ω →₂[μ] ℝ := Nat.rec (e 0) (fun t v => condition μ (hG (s (t+1))) v)
  have gap := separated_orbit (fun i => condition μ (hG i)) (fun i => condition_dist μ (hG i))
    w hw e move sep x rfl (fun _ => rfl)
  have eqn (t : ℕ) : OMA.S_mo_157184.iter μ G s (⇑(e 0)) t =ᵐ[μ] ⇑(x t) := by
    induction t with
    | zero => rfl
    | succ t ih => exact (condExp_congr_ae ih).trans (condition_ae μ (hG _) _).symm
  obtain ⟨y, hy, hc⟩ := hall Ω μ 6 G hG s _ (Lp.memLp (e 0))
  apply Wave9Z.reject_limit (f := fun n => ⇑(x n)) (fun n => Lp.memLp _) ?_ ⟨y, hy, ?_⟩
  · intro N
    obtain ⟨i, hi, j, hj, hg⟩ := gap N
    refine ⟨i, hi, j, hj, ?_⟩
    rw [← Lp.edist_def, Lp.edist_dist]
    simpa using ENNReal.ofReal_le_ofReal hg.le
  · convert hc using 1
    exact funext fun k => (eLpNorm_congr_ae ((eqn k).sub Filter.EventuallyEq.rfl)).symm

end ProjectionWords

namespace ProjectionWords
open Wave9Z
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

/-- A convex interpolation between the identity and a contraction. -/
theorem damping_norm (Q : Op E) (hP : ‖1 - Q‖ ≤ 1) {c : ℝ}
    (hc : 0 ≤ c) (hc' : c ≤ 1) : ‖1 - c • Q‖ ≤ 1 := by
  have he : 1 - c • Q = (1-c) • (1 : Op E) + c • (1-Q) := by
    rw [sub_smul, one_smul, smul_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖(1-c) • (1 : Op E)‖ + ‖c • (1-Q)‖ := norm_add_le ..
    _ = (1-c) + c * ‖1-Q‖ := by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc,
      abs_of_nonneg (sub_nonneg.mpr hc')]
    _ ≤ (1-c) + c * 1 := by gcongr
    _ = 1 := by ring

theorem damping_power (Q : Op E) (hQ : Q * Q = Q) (c : ℝ) (r : ℕ) :
    (1 - c • Q)^r = (1-Q) + (1-c)^r • Q := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, ih, add_mul, sub_mul, one_mul, mul_sub, mul_one,
      mul_sub, mul_one]
    simp only [mul_smul_comm, smul_mul_assoc, hQ, smul_smul, pow_succ, mul_sub, mul_one,
      sub_smul, mul_comm c]
    abel

def exposure (A k : ℕ) (i : Fin k) : ℕ := (A^2)^(k - (i.val+1))
def repetitions (R A S k : ℕ) (i : Fin k) : ℕ := R * S * A^(i.val+1)
noncomputable def mass (A S k : ℕ) (i : Fin k) : ℝ := 1 / ((S:ℝ) * (A:ℝ)^(i.val+1))
noncomputable def loss (A k : ℕ) (i : Fin k) (s : ℕ) : ℝ :=
  1 - (1 - 1 / (exposure A k i : ℝ))^s

theorem loss_mem {A k : ℕ} (hA : 1 ≤ A) (i : Fin k) (s : ℕ) :
    0 ≤ loss A k i s ∧ loss A k i s ≤ 1 := by
  have h : 1 ≤ (exposure A k i : ℝ) := by
    unfold exposure
    push_cast
    exact one_le_pow₀ (one_le_pow₀ (by exact_mod_cast hA))
  have hd : 1 / (exposure A k i : ℝ) ≤ 1 := (one_div_le_one_div_of_le (by norm_num) h).trans_eq (by norm_num)
  exact ⟨sub_nonneg.mpr (pow_le_one₀ (by linarith) (by have := one_div_nonneg.mpr (show 0 ≤ (exposure A k i : ℝ) by positivity); linarith)),
    sub_le_self _ (pow_nonneg (by linarith) _)⟩

theorem selected_half {A k : ℕ} (hA : 1 ≤ A) (j : Fin k) :
    1/2 ≤ loss A k j (exposure A k j) := by
  have h : 1 ≤ (exposure A k j : ℝ) := by
    unfold exposure
    push_cast
    exact one_le_pow₀ (one_le_pow₀ (by exact_mod_cast hA))
  apply selected_loss (by positivity)
  · apply (div_le_iff₀ (by linarith)).2
    linarith
  · field_simp

theorem other_loss {R A S k : ℕ} (hA : 1 ≤ A) (hS : 0 < S) (i j : Fin k) (hij : i ≠ j) :
    (repetitions R A S k j : ℝ) * (mass A S k i * loss A k i (exposure A k j)) ≤ R / (A:ℝ) := by
  have ha : (1:ℝ) ≤ A := by exact_mod_cast hA
  have ha0 : (0:ℝ) < A := by linarith
  have hs0 : (0:ℝ) < S := by exact_mod_cast hS
  have hcancel : (repetitions R A S k j : ℝ) * mass A S k i =
      ((R:ℝ) * (A:ℝ)^(j.val+1)) * (1/(A:ℝ)^(i.val+1)) := by
    unfold repetitions mass
    push_cast
    field_simp
  rw [← mul_assoc, hcancel]
  rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun he => hij (Fin.ext he)) with h | h
  · have hx : 1 ≤ (exposure A k i : ℝ) := by
      unfold exposure
      push_cast
      exact one_le_pow₀ (one_le_pow₀ ha)
    have hbound := lost_upper (d := 1/(exposure A k i : ℝ))
      (by apply (div_le_iff₀ (by linarith)).2; linarith) (exposure A k j)
    have he := earlier_axis (R:ℝ) (A:ℝ) (by positivity) ha (i.val+1)
      (j.val-(i.val+1)) (k-(j.val+1))
    have e₁ : i.val+1+(j.val-(i.val+1)+1) = j.val+1 := by omega
    have e₂ : (j.val-(i.val+1)+1)+(k-(j.val+1)) = k-(i.val+1) := by omega
    rw [e₁, e₂] at he
    apply (mul_le_mul_of_nonneg_left hbound (by positivity)).trans
    simpa only [exposure, Nat.cast_pow, div_eq_mul_inv, one_mul] using he
  · have he := later_axis (R:ℝ) (A:ℝ) (by positivity) ha (j.val+1) (i.val-(j.val+1))
    rw [show j.val+1+(i.val-(j.val+1)+1) = i.val+1 by omega] at he
    exact (mul_le_of_le_one_right (by positivity) (loss_mem hA i _).2).trans he

end ProjectionWords

namespace ProjectionWords
open Wave9Z
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

noncomputable def mix {k : ℕ} (Q : Fin k → Op E) (A S s : ℕ) : Op E :=
  1 - ∑ i, (mass A S k i * loss A k i s) • Q i

theorem mass_budget {A S k : ℕ} (ha : 1 ≤ A) (hs : 1 ≤ S) (hk : k ≤ A) :
    ∑ i : Fin k, mass A S k i ≤ 1 := by
  have hA : (1:ℝ) ≤ A := by exact_mod_cast ha
  have hS : (1:ℝ) ≤ S := by exact_mod_cast hs
  have hpos : (0:ℝ) < A := by linarith
  calc
    _ ≤ ∑ _i : Fin k, (1/(A:ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      apply one_div_le_one_div_of_le hpos
      calc
        (A:ℝ) = 1 * (A:ℝ) := (one_mul _).symm
        _ ≤ (A:ℝ)^i.val * A := by gcongr; exact one_le_pow₀ hA
        _ = (A:ℝ)^(i.val+1) := (pow_succ ..).symm
        _ ≤ (S:ℝ) * (A:ℝ)^(i.val+1) := le_mul_of_one_le_left (by positivity) hS
    _ = (k:ℝ) / A := by simp [div_eq_mul_inv]
    _ ≤ 1 := (div_le_one hpos).mpr (by exact_mod_cast hk)

theorem mix_norm {k A S : ℕ} (ha : 1 ≤ A) (hs : 1 ≤ S) (hk : k ≤ A)
    (Q : Fin k → Op E) (hQ : ∀ i, ‖1 - Q i‖ ≤ 1) (s : ℕ) : ‖mix Q A S s‖ ≤ 1 := by
  let c := fun i => mass A S k i * loss A k i s
  have hm (i : Fin k) : 0 ≤ mass A S k i := by unfold mass; positivity
  have hc (i : Fin k) : 0 ≤ c i := mul_nonneg (hm i) (loss_mem ha i s).1
  have hb : ∑ i, c i ≤ 1 := (Finset.sum_le_sum fun i _ =>
    mul_le_of_le_one_right (hm i) (loss_mem ha i s).2).trans (mass_budget ha hs hk)
  have he : mix Q A S s = (1 - ∑ i, c i) • (1 : Op E) + ∑ i, c i • (1-Q i) := by
    simp only [sub_smul, one_smul, Finset.sum_smul, smul_sub, Finset.sum_sub_distrib, mix, c]
    abel
  rw [he]
  calc
    _ ≤ ‖(1-∑ i, c i) • (1 : Op E)‖ + ‖∑ i, c i • (1-Q i)‖ := norm_add_le ..
    _ ≤ (1-∑ i, c i) + ∑ i, ‖c i • (1-Q i)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hb), norm_one, mul_one]
      gcongr
      exact norm_sum_le ..
    _ ≤ (1-∑ i, c i) + ∑ i, c i := by
      gcongr with i
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hc i)]
      exact mul_le_of_le_one_right (hc i) (hQ i)
    _ = 1 := by ring

theorem select_direction {k R A S : ℕ} (ha : 1 ≤ A) (hs : 1 ≤ S) (hk : k ≤ A)
    (Q : Fin k → Op E) (hP : ∀ i, ‖1-Q i‖ ≤ 1) (hQ : ∀ i, ‖Q i‖ ≤ 1)
    (idem : ∀ i, Q i * Q i = Q i) (j : Fin k) :
    ‖(mix Q A S (exposure A k j))^(repetitions R A S k j) - (1-Q j)‖ ≤
      (k:ℝ) * (R/(A:ℝ)) + 1/(1+(R:ℝ)/2) := by
  let r := repetitions R A S k j
  let s := exposure A k j
  let c := fun i => mass A S k i * loss A k i s
  let C : Op E := 1 - c j • Q j
  let M := mix Q A S s
  have hm : 0 ≤ mass A S k j := by unfold mass; positivity
  have hc : 0 ≤ c j := mul_nonneg hm (loss_mem ha j _).1
  have hc' : c j ≤ 1 := calc
    _ ≤ mass A S k j := mul_le_of_le_one_right hm (loss_mem ha j _).2
    _ ≤ ∑ i, mass A S k i := Finset.single_le_sum (fun i _ => by unfold mass; positivity) (Finset.mem_univ j)
    _ ≤ 1 := mass_budget ha hs hk
  have hr : 0 ≤ (r:ℝ) := by positivity
  have hpow := perturb_power M C (mix_norm ha hs hk Q hP _) (damping_norm _ (hP j) hc hc') r
  have hd : (r:ℝ) * ‖M-C‖ ≤ (k:ℝ)*(R/(A:ℝ)) := by
    rw [← Real.norm_of_nonneg hr, ← norm_smul]
    change ‖(r:ℝ) • ((1 - ∑ i, c i • Q i) - (1 - c j • Q j))‖ ≤ _
    simp only [smul_sub, Finset.smul_sum, smul_smul]
    apply (leakage j (fun i => ((r:ℝ)*c i) • Q i) _ (R/(A:ℝ)) (by positivity) ?_).trans_eq
    · simp
    · intro i hij
      have hci : 0 ≤ c i := mul_nonneg (by unfold mass; positivity) (loss_mem ha i _).1
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr hci)]
      exact (mul_le_of_le_one_right (mul_nonneg hr hci) (hQ i)).trans (other_loss ha hs i j hij)
  have ha0 : (0:ℝ) < A := by exact_mod_cast ha
  have hs0 : (0:ℝ) < S := by exact_mod_cast hs
  have hcancel : (r:ℝ) * mass A S k j = R := by
    unfold r repetitions mass
    push_cast
    field_simp
  have hrc : (R:ℝ)/2 ≤ (r:ℝ)*c j := by
    change _ ≤ (r:ℝ) * (_ * _)
    rw [← mul_assoc, hcancel]
    have hh := mul_le_mul_of_nonneg_left (selected_half ha j) (show (0:ℝ) ≤ R by positivity)
    linarith
  have hdecay := suppress_line hc hc' r hrc (by positivity)
  have hclose : ‖C^r - (1-Q j)‖ ≤ 1 / (1+(R:ℝ)/2) := by
    rw [show C^r = 1-Q j + (1-c j)^r • Q j from damping_power _ (idem j) _ _, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sub_nonneg.mpr hc') _)]
    exact (mul_le_of_le_one_right (pow_nonneg (sub_nonneg.mpr hc') _) (hQ j)).trans hdecay
  exact (norm_sub_le_norm_sub_add_norm_sub (M^r) (C^r) (1-Q j)).trans
    (add_le_add (hpow.trans hd) hclose)

end ProjectionWords

namespace ProjectionWords
open Wave9Z
open scoped RealInnerProductSpace

abbrev Plane := EuclideanSpace ℝ (Fin 2)
noncomputable def ray (t : ℝ) : Plane := WithLp.toLp 2 ![ux t, uy t]
theorem ray_inner (s t : ℝ) : inner ℝ (ray s) (ray t) = ux s * ux t + uy s * uy t := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two, ray, mul_comm]

theorem ray_unit (t : ℝ) : ‖ray t‖ = 1 := by
  have h := chord t t
  rw [← ray_inner, real_inner_self_eq_norm_sq] at h
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div] at h
  nlinarith [norm_nonneg (ray t)]

noncomputable def line (k : ℕ) (j : Fin k) : Submodule ℝ Plane :=
  ℝ ∙ ray (((j.val+1:ℕ):ℝ) / k)

noncomputable def across (k : ℕ) (j : Fin k) : Op Plane := (line k j)ᗮ.starProjection

theorem ideal_step {k : ℕ} (j : Fin k) :
    dist (((1 - across k j : Op Plane)) (ray ((j:ℝ)/k))) (ray (((j.val+1:ℕ):ℝ)/k)) ≤
      2 / (k:ℝ)^2 := by
  let t : ℝ := ((j.val+1:ℕ):ℝ)/k
  let s : ℝ := (j:ℝ)/k
  have hk : 0 < (k:ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
  have he : 1 - across k j = (line k j).starProjection := by
    rw [across, Submodule.starProjection_orthogonal']; abel
  rw [he, line, Submodule.starProjection_singleton, ray_unit]
  simp only [one_pow, RCLike.ofReal_one, div_one]
  have diff (a : ℝ) (u : Plane) : a • u - u = (a-1) • u := by rw [sub_smul, one_smul]
  rw [dist_eq_norm, diff, norm_smul, ray_unit, mul_one,
    Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg]
  · rw [ray_inner]
    apply (dot_loss t s).trans_eq
    unfold t s
    push_cast
    field_simp
    ring
  · rw [ray_inner, chord]
    positivity

def rate (k : ℕ) : ℕ := 2*k^2
def base (k : ℕ) : ℕ := 4*rate k*k^3

theorem le_base {k : ℕ} (hk : 0 < k) : k ≤ base k := by
  apply (le_self_pow₀ (show 1 ≤ k from hk) (by decide : 3 ≠ 0)).trans
  exact Nat.le_mul_of_pos_left _ (by unfold rate; positivity)

theorem mixed_step {k S : ℕ} (hk : 0 < k) (hs : 1 ≤ S) (j : Fin k) :
    let M := mix (across k) (base k) S (exposure (base k) k j)
    let r := repetitions (rate k) (base k) S k j
    dist ((M^r) (ray ((j:ℝ)/k))) (ray (((j.val+1:ℕ):ℝ)/k)) ≤ 4/(k:ℝ)^2 := by
  dsimp only
  have hkA := le_base hk
  have hP (i : Fin k) : 1 - across k i = (line k i).starProjection := by
    rw [across, Submodule.starProjection_orthogonal']; abel
  have hn := select_direction (R := rate k) (show 1 ≤ base k from Nat.le_trans hk hkA) hs hkA (across k)
    (fun i => by rw [hP]; exact Submodule.starProjection_norm_le _) (fun i => Submodule.starProjection_norm_le _)
    (fun i => Submodule.isIdempotentElem_starProjection _) j
  let M := mix (across k) (base k) S (exposure (base k) k j)
  let r := repetitions (rate k) (base k) S k j
  let v := ray ((j:ℝ)/k)
  have hnear : dist ((M^r) v) ((1-across k j : Op Plane) v) ≤
      (k:ℝ)*(rate k/(base k:ℝ)) + 1/(1+(rate k:ℝ)/2) := by
    rw [dist_eq_norm]
    apply ((M^r - (1-across k j)).le_opNorm v).trans
    simpa [v, ray_unit] using hn
  apply (dist_triangle _ ((1-across k j : Op Plane) v) _).trans
  apply (add_le_add hnear (ideal_step j)).trans
  have hpos : 0 < (k:ℝ) := by exact_mod_cast hk
  unfold base rate
  push_cast
  field_simp
  nlinarith [sq_nonneg (k:ℝ)]

theorem finite_word {E ι : Type*} [PseudoMetricSpace E] (T : ι → E → E)
    (hT : ∀ i x y, dist (T i x) (T i y) ≤ dist x y) {k S : ℕ} (hk : 0 < k) (hs : 1 ≤ S)
    (F : Plane → E) (hF : ∀ v u, dist (F v) (F u) ≤ dist v u)
    (device : ∀ (s : ℕ), ∃ w : List ι, ∀ v,
      w.foldl (fun x i => T i x) (F v) = F ((mix (across k) (base k) S s) v)) :
    ∃ w : List ι, dist (w.foldl (fun x i => T i x) (F (ray 0))) (F (ray 1)) ≤ 4/(k:ℝ) := by
  have walk (m : ℕ) (hm : m ≤ k) : ∃ w : List ι,
      dist (w.foldl (fun x i => T i x) (F (ray 0))) (F (ray ((m:ℝ)/k))) ≤ (m:ℝ)*(4/(k:ℝ)^2) := by
    induction m with
    | zero => exact ⟨[], by simp⟩
    | succ m ih =>
      obtain ⟨u, hu⟩ := ih (by omega)
      let j : Fin k := ⟨m, by omega⟩
      let M := mix (across k) (base k) S (exposure (base k) k j)
      obtain ⟨w, hw⟩ := device (exposure (base k) k j)
      have rep (r : ℕ) : ∃ q : List ι, ∀ v,
          q.foldl (fun x i => T i x) (F v) = F ((M^r) v) := by
        induction r with
        | zero => exact ⟨[], by simp⟩
        | succ r ih =>
          obtain ⟨q,hq⟩ := ih
          exact ⟨q++w, fun v => by rw [List.foldl_append, hq, hw, pow_succ']; rfl⟩
      obtain ⟨q, hq⟩ := rep (repetitions (rate k) (base k) S k j)
      refine ⟨u++q, ?_⟩
      rw [List.foldl_append]
      let v := ray ((m:ℝ)/k)
      apply (dist_triangle _ (q.foldl (fun x i => T i x) (F v)) _).trans
      have h₁ := (fold_dist T hT q _ _).trans hu
      apply (add_le_add h₁ ?_).trans (show (m:ℝ)*(4/(k:ℝ)^2) + 4/(k:ℝ)^2 = ((m+1:ℕ):ℝ)*(4/(k:ℝ)^2) by push_cast; ring).le
      rw [hq]
      exact (hF _ _).trans (mixed_step hk hs j)
  obtain ⟨w, hw⟩ := walk k le_rfl
  have hpos : (0:ℝ) < k := by exact_mod_cast hk
  refine ⟨w, ?_⟩
  rw [div_self hpos.ne'] at hw
  apply hw.trans_eq
  field_simp
end ProjectionWords

namespace ProjectionWords
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

def size (n : ℕ) : ℕ := 64 * 2^n
theorem size_pos (n : ℕ) : 0 < size n := by unfold size; positivity

abbrev Tag (n : ℕ) := Option (Fin (size n))
instance {k : ℕ} : MeasurableSpace (Option (Fin k)) := ⊤
instance {k : ℕ} : DiscreteMeasurableSpace (Option (Fin k)) := ⟨fun _ => trivial⟩
abbrev Labels := (n : ℕ) → Tag n
abbrev Noise := ℤ × Fin 2 → ℝ
abbrev Sample := (unitInterval × Labels) × Noise

noncomputable def localWeight (k : ℕ) : Option (Fin k) → ℝ
  | none => 1 - ∑ i, mass (base k) 1 k i
  | some i => mass (base k) 1 k i

theorem weight_nonneg {k : ℕ} (hk : 0 < k) (a : Option (Fin k)) : 0 ≤ localWeight k a := by
  cases a with
  | none => exact sub_nonneg.mpr (mass_budget (Nat.le_trans hk (le_base hk)) le_rfl (le_base hk))
  | some j => unfold localWeight mass; positivity

noncomputable def tagPMF (n : ℕ) : PMF (Tag n) :=
  PMF.ofFintype (fun a => ENNReal.ofReal (localWeight (size n) a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => weight_nonneg (size_pos _) i), Fintype.sum_option]
    simp [localWeight])

noncomputable abbrev tags (n : ℕ) := (tagPMF n).toMeasure
noncomputable abbrev labelLaw : Measure Labels := Measure.infinitePi tags
noncomputable abbrev noiseLaw : Measure Noise := Measure.infinitePi fun _ => gaussianReal 0 1
noncomputable abbrev sampleLaw : Measure Sample := ((volume : Measure unitInterval).prod labelLaw).prod noiseLaw

theorem tags_real (n : ℕ) (a : Tag n) : (tags n).real {a} = localWeight (size n) a := by
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact ENNReal.toReal_ofReal (weight_nonneg (size_pos n) a)

/-- Reindex the odd pairs as the right member of one even pair and the left
member of the following pair. Integer indexing makes this a permutation. -/
def pairing : Bool → (ℤ × Fin 2) ≃ (ℤ × Fin 2)
  | false => Equiv.refl _
  | true => {
    toFun := fun (i,j) => if j = 0 then (i,1) else (i+1,0)
    invFun := fun (i,j) => if j = 0 then (i-1,1) else (i,0)
    left_inv := by rintro ⟨i,j⟩; fin_cases j <;> simp
    right_inv := by rintro ⟨i,j⟩; fin_cases j <;> simp }

noncomputable def blocks (p : Bool) : Noise ≃ᵐ (ℤ → Plane) :=
  ((MeasurableEquiv.piCongrLeft (fun _ => ℝ) (pairing p).symm).trans
    (MeasurableEquiv.curry ℤ (Fin 2) ℝ)).trans
    (MeasurableEquiv.piCongrRight (fun _ => MeasurableEquiv.toLp 2 _))

theorem blocks_apply (p : Bool) (x : Noise) (i : ℤ) (j : Fin 2) :
    blocks p x i j = x (pairing p (i,j)) := by
  change (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (pairing p).symm x) (i,j) = _
  generalize hh : (i,j) = z
  obtain ⟨y,rfl⟩ := (pairing p).symm.surjective z
  simp [MeasurableEquiv.piCongrLeft_apply_apply]

theorem blocks_law (p : Bool) : MeasurePreserving (blocks p) noiseLaw
    (Measure.infinitePi fun _ => stdGaussian Plane) := by
  have h₁ : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (pairing p).symm)
      noiseLaw noiseLaw := ⟨by fun_prop, Measure.infinitePi_map_piCongrLeft (fun _ => gaussianReal 0 1) (pairing p).symm⟩
  have h₂ : MeasurePreserving (MeasurableEquiv.curry ℤ (Fin 2) ℝ) noiseLaw
      (Measure.infinitePi fun _ : ℤ => Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1) :=
    ⟨by fun_prop, Measure.infinitePi_map_curry (fun (_ : ℤ) (_ : Fin 2) => gaussianReal 0 1)⟩
  have h₃ : MeasurePreserving (fun y : ℤ → Fin 2 → ℝ => fun i => WithLp.toLp 2 (y i))
      (Measure.infinitePi fun _ : ℤ => Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1)
      (Measure.infinitePi fun _ : ℤ => stdGaussian Plane) := by
    refine ⟨measurable_pi_lambda _ (fun i => (MeasurableEquiv.toLp 2 _).measurable.comp (measurable_pi_apply i)), ?_⟩
    have hm (_ : ℤ) : Measurable (WithLp.toLp 2 : (Fin 2 → ℝ) → Plane) := (MeasurableEquiv.toLp 2 _).measurable
    rw [Measure.infinitePi_map_pi _ hm]
    simp_rw [Measure.infinitePi_eq_pi (ι := Fin 2), map_pi_eq_stdGaussian]
  exact h₃.comp (h₂.comp h₁)

def stage (p : Bool) (i : ℤ) : ℕ := 2*i.toNat + p.toNat
def parity (n : ℕ) : Bool := n%2 = 1
def anchor (n : ℕ) : ℤ := (n/2 : ℕ)

theorem stage_at (n : ℕ) : stage (parity n) (anchor n) = n := by
  simp only [stage, anchor, Int.toNat_natCast, parity]
  by_cases h : n%2 = 1 <;> simp [h] <;> omega

noncomputable def planeAt (n : ℕ) (x : Sample) : Plane := blocks (parity n) x.2 (anchor n)

theorem planeLaw (n : ℕ) : MeasurePreserving (planeAt n) sampleLaw (stdGaussian Plane) :=
  (measurePreserving_eval_infinitePi _ _).comp ((blocks_law _).comp measurePreserving_snd)

noncomputable def scalar (n : ℕ) (v : Plane) (x : Sample) : ℝ := inner ℝ v (planeAt n x)

theorem scalar_mem (n : ℕ) (v : Plane) : MemLp (scalar n v) 2 sampleLaw := by
  let L := innerSL ℝ v
  have h : MemLp (fun y => inner ℝ v y) 2 (stdGaussian Plane) :=
    L.lipschitz.comp_memLp L.map_zero IsGaussian.memLp_two_id
  exact h.comp_measurePreserving (planeLaw n)

noncomputable def cylinder (n : ℕ) (v : Plane) : Sample →₂[sampleLaw] ℝ :=
  (scalar_mem n v).toLp _

theorem scalar_norm (n : ℕ) (v : Plane) : eLpNorm (scalar n v) 2 sampleLaw = ENNReal.ofReal ‖v‖ := by
  have h : MemLp (fun y => inner ℝ v y) 2 (stdGaussian Plane) :=
    (innerSL ℝ v).lipschitz.comp_memLp (innerSL ℝ v).map_zero IsGaussian.memLp_two_id
  rw [show scalar n v = (fun y => inner ℝ v y) ∘ planeAt n from rfl,
    eLpNorm_comp_measurePreserving h.1 (planeLaw n), h.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num [Real.norm_eq_abs, sq_abs, Wave9Z.second_moment, ← Real.sqrt_eq_rpow]

theorem cylinder_dist (n : ℕ) (u v : Plane) :
    dist (cylinder n u) (cylinder n v) = dist u v := by
  rw [Lp.dist_edist, cylinder, cylinder, Lp.edist_toLp_toLp,
    show scalar n u - scalar n v = scalar n (u-v) from funext fun x => (inner_sub_left ..).symm,
    scalar_norm, ENNReal.toReal_ofReal (norm_nonneg _), dist_eq_norm]

theorem endpoint_eq (n : ℕ) : cylinder n (ray 1) = cylinder (n+1) (ray 0) := by
  apply Lp.ext
  refine (scalar_mem _ _).coeFn_toLp.trans (Filter.EventuallyEq.trans ?_ (scalar_mem _ _).coeFn_toLp.symm)
  apply Filter.Eventually.of_forall
  intro x
  simp [scalar, planeAt, ray, Wave9Z.ux, Wave9Z.uy, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_two, blocks_apply, parity, anchor, pairing]
  by_cases hn : n%2 = 1
  · have hs : (n+1)%2 ≠ 1 := by omega
    norm_num [hn, hs]
    have he : (n:ℤ)/2 + 1 = ((n:ℤ)+1)/2 := by exact_mod_cast (show n/2+1=(n+1)/2 by omega)
    rw [he]
  · have hs : (n+1)%2 = 1 := by omega
    norm_num [hn, hs]
    have he : (n:ℤ)/2 = ((n:ℤ)+1)/2 := by exact_mod_cast (show n/2=(n+1)/2 by omega)
    rw [he]

theorem endpoint_dist (n : ℕ) : 5/4 ≤ dist (cylinder n (ray 0)) (cylinder (n+1) (ray 0)) := by
  rw [← endpoint_eq, cylinder_dist, dist_eq_norm]
  have h : ‖ray 0 - ray 1‖^2 = 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right]
    norm_num [ray_inner, ray_unit, Wave9Z.ux, Wave9Z.uy]
  nlinarith [norm_nonneg (ray 0-ray 1)]

end ProjectionWords

namespace ProjectionWords
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

noncomputable def threshold {k : ℕ} (j : Fin k) : unitInterval :=
  ⟨1/(exposure (base k) k j : ℝ), by
    have hk : 0 < k := Nat.zero_lt_of_lt j.isLt
    have ha : (1:ℝ) ≤ base k := by exact_mod_cast (Nat.le_trans hk (le_base hk))
    have h : (1:ℝ) ≤ exposure (base k) k j := by
      unfold exposure
      push_cast
      exact one_le_pow₀ (one_le_pow₀ ha)
    exact ⟨by positivity, (div_le_iff₀ (by linarith)).mpr (by linarith)⟩⟩

noncomputable def turn {k : ℕ} (b : unitInterval) : Option (Fin k) → Plane ≃ₗᵢ[ℝ] Plane
  | none => LinearIsometryEquiv.refl ℝ Plane
  | some j => if b ≤ threshold j then (line k j).reflection else LinearIsometryEquiv.refl ℝ Plane

theorem turn_twice {k : ℕ} (b : unitInterval) (a : Option (Fin k)) (v : Plane) :
    turn b a (turn b a v) = v := by
  cases a with
  | none => rfl
  | some j => by_cases h : b ≤ threshold j <;> simp [turn,h]

theorem measurable_turn {k : ℕ} :
    Measurable (fun t : (unitInterval × Plane) × Option (Fin k) => turn t.1.1 t.2 t.1.2) := by
  apply measurable_from_prod_countable_left
  intro a
  cases a with
  | none => exact measurable_snd
  | some j =>
    change Measurable (fun t : unitInterval × Plane => turn t.1 (some j) t.2)
    have heq (t : unitInterval × Plane) : turn t.1 (some j) t.2 = if t.1 ≤ threshold j then (line k j).reflection t.2 else t.2 := by
      by_cases h : t.1 ≤ threshold j <;> simp [turn, h]
    simp_rw [heq]
    exact Measurable.ite (measurableSet_le measurable_fst measurable_const)
      ((line k j).reflection.continuous.measurable.comp measurable_snd) measurable_snd

noncomputable def twist (p : Bool) (a : unitInterval × Labels) (z : Noise) : Noise :=
  (blocks p).symm (fun i => turn a.1 (a.2 (stage p i)) (blocks p z i))

noncomputable def reflectSample (p : Bool) (x : Sample) : Sample := (x.1, twist p x.1 x.2)

theorem twist_measurable (p : Bool) : Measurable (Function.uncurry (twist p)) := by
  apply (blocks p).symm.measurable.comp
  apply measurable_pi_lambda
  intro i
  exact measurable_turn.comp (((measurable_fst.comp measurable_fst).prodMk
    ((measurable_pi_apply i).comp ((blocks p).measurable.comp measurable_snd))).prodMk
    ((measurable_pi_apply (stage p i)).comp (measurable_snd.comp measurable_fst)))

theorem reflect_law (p : Bool) : MeasurePreserving (reflectSample p) sampleLaw sampleLaw := by
  apply (MeasurePreserving.id _).skew_product (twist_measurable p)
  apply Filter.Eventually.of_forall
  intro a
  exact ((blocks_law p).symm.comp ((Wave9Z.orthogonal_blocks (fun i => turn a.1 (a.2 (stage p i)))).comp
    (blocks_law p))).map_eq

theorem reflect_involution (p : Bool) : Function.Involutive (reflectSample p) := by
  rintro ⟨a,z⟩
  refine Prod.ext ?_ ?_
  · rfl
  change (blocks p).symm _ = z
  apply (blocks p).injective
  simp [reflectSample, twist, turn_twice]

theorem reflect_plane (n : ℕ) (x : Sample) :
    planeAt n (reflectSample (parity n) x) = turn x.1.1 (x.1.2 n) (planeAt n x) := by
  unfold planeAt reflectSample twist
  simp only [MeasurableEquiv.apply_symm_apply]
  generalize ht : stage (parity n) (anchor n) = m
  rw [stage_at] at ht
  subst m
  rfl

/-- Conditional expectation onto the second factor, after a measure-preserving
change of coordinates. This allows the same sample space to forget either
one or both auxiliary labels. -/
theorem average_fiber {Ω A B : Type} [MeasurableSpace Ω] [MeasurableSpace A] [mB : MeasurableSpace B]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure A) [IsProbabilityMeasure ν]
    (ρ : Measure B) [IsProbabilityMeasure ρ] (e : Ω ≃ᵐ A × B) (he : MeasurePreserving e μ (ν.prod ρ))
    (f : A × B → ℝ) (hf : Measurable f) (hi : Integrable f (ν.prod ρ)) :
    let π := fun x => (e x).2
    (fun x => ∫ a, f (a, π x) ∂ν) =ᵐ[μ] μ[f ∘ e | mB.comap π] := by
  dsimp only
  let g := fun b => ∫ a, f (a,b) ∂ν
  have hgm : Measurable g := (StronglyMeasurable.integral_prod_left (f := fun a b => f (a,b)) hf.stronglyMeasurable).measurable
  have hπ := measurable_snd.comp e.measurable
  have hp := measurePreserving_snd.comp he
  apply ae_eq_condExp_of_forall_setIntegral_eq hπ.comap_le (he.integrable_comp_of_integrable hi)
  · exact fun _ _ _ => (hp.integrable_comp_of_integrable hi.integral_prod_right).integrableOn
  · rintro _ ⟨t,ht,rfl⟩ _
    let S : Set (A × B) := Set.univ ×ˢ t
    have hset : (Prod.snd ∘ e) ⁻¹' t = e ⁻¹' S := by ext; simp [S]
    rw [hset]
    change ∫ x in e ⁻¹' S, g (e x).2 ∂μ = ∫ x in e ⁻¹' S, f (e x) ∂μ
    rw [he.setIntegral_preimage_emb e.measurableEmbedding (fun z => g z.2), he.setIntegral_preimage_emb e.measurableEmbedding f]
    have hi' : Integrable (fun z : A × B => g z.2) (ν.prod ρ) :=
      measurePreserving_snd.integrable_comp_of_integrable hi.integral_prod_right
    have hr : (ν.prod ρ).restrict S = ν.prod (ρ.restrict t) := by simp [S, ← Measure.prod_restrict]
    have h₁ := hi'.integrableOn (s := S)
    have h₂ := hi.integrableOn (s := S)
    rw [IntegrableOn, hr] at h₁ h₂
    rw [hr, integral_prod_symm _ h₁, integral_prod_symm _ h₂]
    simp [g]
  · exact (hgm.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable.aestronglyMeasurable

end ProjectionWords

namespace ProjectionWords
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

noncomputable def coeff (k s : ℕ) (v : Plane) : Option (Fin k) → Plane
  | none => v
  | some j => v - loss (base k) k j s • across k j v

theorem coeff_zero {k : ℕ} (a : Option (Fin k)) (v : Plane) : coeff k 0 v a = v := by
  cases a <;> simp [coeff, loss]

noncomputable def averaged {k : ℕ} (b : unitInterval) (a : Option (Fin k)) (u : Plane) : Plane :=
  (1/2 : ℝ) • (u + turn b a u)

theorem averaged_inner {k : ℕ} (b : unitInterval) (a : Option (Fin k)) (u z : Plane) :
    inner ℝ (averaged b a u) z = (1/2 : ℝ) * (inner ℝ u z + inner ℝ u (turn b a z)) := by
  have h := (turn b a).inner_map_map (turn b a u) z
  rw [turn_twice] at h
  simp [averaged, real_inner_smul_left, inner_add_left, h, mul_add]

theorem averaged_off {k : ℕ} (b : unitInterval) (v : Plane) : averaged b (none : Option (Fin k)) v = v := by
  change (1/2:ℝ) • (v+v) = v
  rw [← two_smul ℝ v, smul_smul]
  norm_num

theorem averaged_on {k : ℕ} (b : unitInterval) (j : Fin k) (v : Plane) :
    averaged b (some j) v = if b ≤ threshold j then (line k j).starProjection v else v := by
  by_cases h : b ≤ threshold j
  · simp only [averaged, turn, if_pos h, Submodule.reflection_apply]
    rw [add_sub_cancel, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    norm_num
  · simpa [averaged, turn, h] using averaged_off (k := k) b v

theorem integral_switch (u : unitInterval) (c d : ℝ) :
    (∫ b : unitInterval, if b ≤ u then c else d) = (u:ℝ)*c + (1-u:ℝ)*d := by
  change (∫ b, (Set.Iic u).piecewise (fun _ => c) (fun _ => d) b) = _
  rw [integral_piecewise measurableSet_Iic (integrableOn_const (by simp)) (integrableOn_const (by simp)),
    setIntegral_const, setIntegral_const, measureReal_compl measurableSet_Iic]
  simp [measureReal_def, ENNReal.toReal_ofReal u.2.1]

theorem time_average (k s : ℕ) (v z : Plane) (a : Option (Fin k)) :
    (∫ b : unitInterval, inner ℝ (averaged b a (coeff k s v a)) z) =
      inner ℝ (coeff k (s+1) v a) z := by
  cases a with
  | none => simp [averaged_off, coeff]
  | some j =>
    simp_rw [averaged_on, apply_ite (fun u => inner ℝ u z), integral_switch]
    have hp : (line k j).starProjection (across k j v) = 0 := by
      have he := congrArg (fun M : Wave9Z.Op Plane => M v) (Submodule.isIdempotentElem_starProjection (line k j)).eq
      change (line k j).starProjection ((line k j).starProjection v) = (line k j).starProjection v at he
      simp [across, he]
    simp only [coeff, map_sub, map_smul, hp, smul_zero, sub_zero]
    have hq : (line k j).starProjection v = v - across k j v := by simp [across]
    rw [hq]
    simp only [inner_sub_left, real_inner_smul_left, threshold, loss, pow_succ]
    ring

theorem label_average (n s : ℕ) (v z : Plane) :
    (∫ a : Labels, inner ℝ (coeff (size n) s v (a n)) z ∂labelLaw) =
      inner ℝ ((mix (across (size n)) (base (size n)) 1 s) v) z := by
  let F := fun a : Tag n => inner ℝ (coeff (size n) s v a) z
  have hm : Measurable F := Measurable.of_discrete
  have hp := measurePreserving_eval_infinitePi tags n
  have hi := integral_map hp.measurable.aemeasurable (hm.stronglyMeasurable.aestronglyMeasurable
    (μ := labelLaw.map (fun a => a n)))
  rw [hp.map_eq] at hi
  change (∫ a : Labels, F (a n) ∂labelLaw) = _
  rw [← hi, integral_fintype Integrable.of_finite, Fintype.sum_option]
  simp only [tags_real, F, localWeight, coeff, mix, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    inner_sub_left, real_inner_smul_left, sum_inner, smul_eq_mul, mul_sub, sub_mul, one_mul,
    Finset.sum_sub_distrib, Finset.sum_mul]
  ring_nf

noncomputable def tagged (n s : ℕ) (v : Plane) (x : Sample) : ℝ :=
  inner ℝ (coeff (size n) s v (x.1.2 n)) (planeAt n x)

noncomputable def intermediate (n s : ℕ) (v : Plane) (x : Sample) : ℝ :=
  inner ℝ (averaged x.1.1 (x.1.2 n) (coeff (size n) s v (x.1.2 n))) (planeAt n x)

theorem tagged_measurable (n s : ℕ) (v : Plane) : Measurable (tagged n s v) := by
  apply Measurable.inner
  · exact (Measurable.of_discrete (f := coeff (size n) s v)).comp ((measurable_pi_apply (X := Tag) n).comp (measurable_snd.comp measurable_fst))
  · exact (planeLaw n).measurable

theorem intermediate_eq (n s : ℕ) (v : Plane) (x : Sample) :
    intermediate n s v x = (1/2:ℝ) * (tagged n s v x + tagged n s v (reflectSample (parity n) x)) := by
  unfold intermediate tagged
  rw [averaged_inner, reflect_plane]
  rfl

theorem intermediate_measurable (n s : ℕ) (v : Plane) : Measurable (intermediate n s v) := by
  simp_rw [show intermediate n s v = _ from funext (intermediate_eq n s v)]
  exact measurable_const.mul ((tagged_measurable ..).add ((tagged_measurable ..).comp (reflect_law _).measurable))

end ProjectionWords

namespace ProjectionWords
open MeasureTheory ProbabilityTheory

abbrev forgetLabels : MeasurableSpace Sample := MeasurableSpace.comap Prod.snd inferInstance
abbrev forgetThreshold : MeasurableSpace Sample :=
  MeasurableSpace.comap (fun x : Sample => (x.1.2,x.2)) inferInstance

/-- The four active fields, the trivial field, and the ambient field. -/
noncomputable def fields : Fin 6 → MeasurableSpace Sample :=
  ![forgetLabels, forgetThreshold, Wave9Z.fixedEvents (reflectSample false),
    Wave9Z.fixedEvents (reflectSample true), ⊥, inferInstance]

theorem fields_le (i : Fin 6) : fields i ≤ (inferInstance : MeasurableSpace Sample) := by
  fin_cases i
  · exact measurable_snd.comap_le
  · exact ((measurable_snd.comp measurable_fst).prodMk measurable_snd).comap_le
  · exact Wave9Z.fixedEvents_le _
  · exact Wave9Z.fixedEvents_le _
  · exact bot_le
  · exact le_rfl

noncomputable def applyField (i : Fin 6) (y : Sample →₂[sampleLaw] ℝ) : Sample →₂[sampleLaw] ℝ :=
  condition sampleLaw (fields_le i) y

def reflectionIndex (p : Bool) : Fin 6 := if p then 3 else 2

theorem reflectionField (p : Bool) : fields (reflectionIndex p) = Wave9Z.fixedEvents (reflectSample p) := by
  cases p <;> rfl

theorem apply_reflection (n s : ℕ) (v : Plane) (y : Sample →₂[sampleLaw] ℝ)
    (hy : ⇑y =ᵐ[sampleLaw] tagged n s v) :
    ⇑(applyField (reflectionIndex (parity n)) y) =ᵐ[sampleLaw] intermediate n s v := by
  apply (condition_ae sampleLaw (fields_le _) _).trans
  rw [reflectionField]
  apply (condExp_congr_ae hy).trans
  have hI := ((Lp.memLp y).integrable (by norm_num)).congr hy
  apply (Wave9Z.reflection_average sampleLaw _ (reflect_involution _) (reflect_law _)
    _ (tagged_measurable ..) hI).symm.trans
  exact Filter.Eventually.of_forall fun x => (intermediate_eq n s v x).symm

theorem apply_threshold (n s : ℕ) (v : Plane) (y : Sample →₂[sampleLaw] ℝ)
    (hy : ⇑y =ᵐ[sampleLaw] intermediate n s v) :
    ⇑(applyField 1 y) =ᵐ[sampleLaw] tagged n (s+1) v := by
  let e : Sample ≃ᵐ unitInterval × Labels × Noise := MeasurableEquiv.prodAssoc
  let f := intermediate n s v ∘ e.symm
  have hm : Measurable f := (intermediate_measurable ..).comp e.symm.measurable
  have he := measurePreserving_prodAssoc (volume : Measure unitInterval) labelLaw noiseLaw
  have hi : Integrable f ((volume : Measure unitInterval).prod (labelLaw.prod noiseLaw)) :=
    he.symm.integrable_comp_of_integrable (((Lp.memLp y).integrable (by norm_num)).congr hy)
  apply (condition_ae sampleLaw (fields_le 1) y).trans
  apply (condExp_congr_ae hy).trans
  apply (average_fiber sampleLaw volume (labelLaw.prod noiseLaw) e he f hm hi).symm.trans
  apply Filter.Eventually.of_forall
  intro x
  exact time_average (size n) s v (planeAt n x) (x.1.2 n)

theorem apply_labels (n s : ℕ) (v : Plane) (y : Sample →₂[sampleLaw] ℝ)
    (hy : ⇑y =ᵐ[sampleLaw] tagged n s v) :
    applyField 0 y = cylinder n (mix (across (size n)) (base (size n)) 1 s v) := by
  apply Lp.ext
  apply (condition_ae sampleLaw (fields_le 0) y).trans
  apply (condExp_congr_ae hy).trans
  let e := MeasurableEquiv.refl Sample
  have hi := ((Lp.memLp y).integrable (by norm_num)).congr hy
  apply (average_fiber sampleLaw (volume.prod labelLaw) noiseLaw e (MeasurePreserving.id _)
    (tagged n s v) (tagged_measurable ..) hi).symm.trans
  apply Filter.EventuallyEq.trans _ (scalar_mem _ _).coeFn_toLp.symm
  apply Filter.Eventually.of_forall
  intro x
  let z := planeAt n x
  let f := fun a : Labels => inner ℝ (coeff (size n) s v (a n)) z
  change (∫ a : unitInterval × Labels, f a.2 ∂volume.prod labelLaw) = _
  rw [integral_fun_snd]
  simpa [f, z, scalar] using label_average n s v (planeAt n x)

theorem local_device (n s : ℕ) : ∃ w : List (Fin 6), ∀ v : Plane,
    w.foldl (fun y i => applyField i y) (cylinder n v) =
      cylinder n ((mix (across (size n)) (base (size n)) 1 s) v) := by
  have powers (t : ℕ) : ∃ w : List (Fin 6), ∀ v : Plane,
      ⇑(w.foldl (fun y i => applyField i y) (cylinder n v)) =ᵐ[sampleLaw] tagged n t v := by
    induction t with
    | zero =>
      refine ⟨[], fun v => (scalar_mem _ _).coeFn_toLp.trans ?_⟩
      exact Filter.Eventually.of_forall fun x => by simp [tagged, coeff_zero, scalar]
    | succ t ih =>
      obtain ⟨w,hw⟩ := ih
      refine ⟨w ++ [reflectionIndex (parity n),1], fun v => ?_⟩
      rw [List.foldl_append]
      exact apply_threshold n t v _ (apply_reflection n t v _ (hw v))
  obtain ⟨w,hw⟩ := powers s
  refine ⟨w ++ [0], fun v => ?_⟩
  rw [List.foldl_append]
  exact apply_labels n s v _ (hw v)

end ProjectionWords

open ProjectionWords in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_157184.main) := by
  have close (n : ℕ) : ∃ w : List (Fin 6),
      dist (w.foldl (fun y i => applyField i y) (cylinder n (ray 0))) (cylinder (n+1) (ray 0)) ≤
        (1/16 : ℝ) * (1/2 : ℝ)^n := by
    obtain ⟨w,hw⟩ := finite_word applyField (fun i => condition_dist _ (fields_le i))
      (size_pos n) (S := 1) le_rfl (cylinder n) (fun u v => (cylinder_dist n u v).le) (local_device n)
    refine ⟨w, ?_⟩
    rw [← endpoint_eq]
    apply hw.trans_eq
    unfold size
    push_cast
    rw [div_pow]
    field_simp
    ring
  choose w hw using close
  have hne (n : ℕ) : w n ≠ [] := by
    intro h
    have hm := hw n
    rw [h, List.foldl_nil] at hm
    have hp := pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1) (n := n)
    linarith [endpoint_dist n]
  exact disproof_of_local_words sampleLaw fields fields_le w hne (fun n => cylinder n (ray 0)) hw endpoint_dist
