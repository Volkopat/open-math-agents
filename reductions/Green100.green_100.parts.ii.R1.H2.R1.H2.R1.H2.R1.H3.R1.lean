import OMAReductions.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1
import Mathlib

/-!
Reduction `Green100.green_100.parts.ii.R1.H2.R1.H2.R1.H2.R1.H3.R1` of step
`Green100.green_100.parts.ii.R1.H2.R1.H2.R1.H2.R1.H3`.

Credit: @nnkostov.
Source: Alekseev, Liu and Thom, arXiv:2609.37761v2, Proposition 2.2, Theorem A (Theorem 4.3),
Corollary 5.1 and Theorem 5.2.
-/

namespace OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1_H3_R1

open Filter
open scoped Topology
open OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1

/-- Alekseev-Liu-Thom, Theorem A (Theorem 4.3): a spectral gap off the relative commutant of a
nonempty finite unitary tuple in a tracial matrix ultraproduct lifts to coordinatewise partitions
of the identity into nonzero orthogonal projections and asymptotically close doubled unitaries
commuting with each partition, with a uniform scalar gap on every corner. -/
def H1 : Prop :=
  ∀ (d : ℕ → ℕ), (∀ n, 0 < d n) → ∀ (ι : Type) [Fintype ι] [Nonempty ι]
    (u : ι → (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) (κ : ℝ), 0 < κ →
  let q := fun (n : ℕ) (y : Matrix (Fin (d n)) (Fin (d n)) ℂ) => (∑ a, ∑ b, ‖y a b‖ ^ 2) / (d n : ℝ)
  let B := fun (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ) =>
    ∃ C : ℝ, ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (y n)‖ ≤ C
  let K := fun (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ) => B y ∧ ∀ a,
    Tendsto (fun n => q n ((u a n : Matrix _ _ ℂ) * y n - y n * (u a n : Matrix _ _ ℂ))) (hyperfilter ℕ) (𝓝 0)
  (∀ y, B y → ∃ e, K e ∧ ∀ ε > 0, ∀ᶠ n in hyperfilter ℕ,
    κ * q n (y n - e n) ≤ ε + ∑ a, q n ((u a n : Matrix _ _ ℂ) * y n - y n * (u a n : Matrix _ _ ℂ))) →
  ∃ (m : ℕ → ℕ) (e : (n : ℕ) → Fin (m n) → Matrix (Fin (d n)) (Fin (d n)) ℂ)
    (v : Bool → ι → (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) (c : ℝ), 0 < c ∧
    (∀ n i, star (e n i) = e n i ∧ e n i * e n i = e n i ∧ e n i ≠ 0) ∧
    (∀ n i j, i ≠ j → e n i * e n j = 0) ∧
    (∀ n, ∑ i, e n i = 1) ∧
    (∀ b a n i, (v b a n : Matrix _ _ ℂ) * e n i = e n i * (v b a n : Matrix _ _ ℂ)) ∧
    (∀ b a, Tendsto (fun n => q n ((v b a n : Matrix _ _ ℂ) - (u a n : Matrix _ _ ℂ))) (hyperfilter ℕ) (𝓝 0)) ∧
    ∀ n i (x : Matrix (Fin (d n)) (Fin (d n)) ℂ), e n i * x * e n i = x →
      c * q n (x - (x.trace / (e n i).trace) • e n i) ≤
        (1 / (8 * (Fintype.card ι : ℝ))) *
          ∑ b : Bool, ∑ a : ι, q n ((v b a n : Matrix _ _ ℂ) * x - x * (v b a n : Matrix _ _ ℂ))

/-- Alekseev-Liu-Thom, Theorem 5.2 (for positive self-adjoint unitary-mixture channels): given
coordinatewise partitions into nonzero orthogonal projections and positive self-adjoint convex
combinations of commuting unitary conjugations that are asymptotically idempotent in `∞ → 2` norm
and asymptotically scalar on every diagonal corner, the ultraproduct fixed-point algebra is
internal. -/
def H2 : Prop :=
  ∀ (d : ℕ → ℕ), (∀ n, 0 < d n) →
  ∀ (m : ℕ → ℕ) (e : (n : ℕ) → Fin (m n) → Matrix (Fin (d n)) (Fin (d n)) ℂ),
  (∀ n i, star (e n i) = e n i ∧ e n i * e n i = e n i ∧ e n i ≠ 0) →
  (∀ n i j, i ≠ j → e n i * e n j = 0) →
  (∀ n, ∑ i, e n i = 1) →
  ∀ (L : ℕ → ℕ) (w : (n : ℕ) → Fin (L n) → ℝ)
    (V : (n : ℕ) → Fin (L n) → Matrix.unitaryGroup (Fin (d n)) ℂ),
  (∀ n s, 0 ≤ w n s) → (∀ n, ∑ s, w n s = 1) →
  (∀ n s i, (V n s : Matrix _ _ ℂ) * e n i = e n i * (V n s : Matrix _ _ ℂ)) →
  let q := fun (n : ℕ) (y : Matrix (Fin (d n)) (Fin (d n)) ℂ) => (∑ a, ∑ b, ‖y a b‖ ^ 2) / (d n : ℝ)
  let B := fun (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ) =>
    ∃ C : ℝ, ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (y n)‖ ≤ C
  let F := fun (n : ℕ) (x : Matrix (Fin (d n)) (Fin (d n)) ℂ) =>
    ∑ s : Fin (L n), (w n s : ℂ) • (star (V n s : Matrix _ _ ℂ) * x * (V n s : Matrix _ _ ℂ))
  (∀ n x, F n x = ∑ s : Fin (L n), (w n s : ℂ) • ((V n s : Matrix _ _ ℂ) * x * star (V n s : Matrix _ _ ℂ))) →
  (∀ n x, 0 ≤ ((star x * F n x).trace).re) →
  (∃ δ : ℕ → ℝ, Tendsto δ (hyperfilter ℕ) (𝓝 0) ∧
    ∀ n x, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) x‖ ≤ 1 → q n (F n (F n x) - F n x) ≤ δ n) →
  (∃ σ : ℕ → ℝ, Tendsto σ (hyperfilter ℕ) (𝓝 0) ∧
    ∀ n i x, e n i * x * e n i = x → q n (F n x - (x.trace / (e n i).trace) • e n i) ≤ σ n * q n x) →
  ∃ A : (n : ℕ) → StarSubalgebra ℂ (Matrix (Fin (d n)) (Fin (d n)) ℂ), ∀ y, B y →
    (Tendsto (fun n => q n (y n - F n (y n))) (hyperfilter ℕ) (𝓝 0) ↔
      ∃ a, B a ∧ (∀ n, a n ∈ A n) ∧ Tendsto (fun n => q n (y n - a n)) (hyperfilter ℕ) (𝓝 0))

/- ### Hilbert-Schmidt trace inner product and basic matrix bounds -/

lemma trace_star_mul_self_eq {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    (star A * A).trace = ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.star_apply,
    Complex.ofReal_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]

lemma re_trace_star_mul_self {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ((star A * A).trace).re = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [trace_star_mul_self_eq, Complex.ofReal_re]

lemma re_trace_star_mul_comm {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) :
    ((star A * B).trace).re = ((star B * A).trace).re := by
  have h : star (star A * B).trace = (star B * A).trace := by
    rw [Matrix.trace, star_sum, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diag_apply, Matrix.mul_apply, star_sum, star_mul', Matrix.star_apply,
      star_star, mul_comm]
  rw [← Complex.conj_re, ← Complex.star_def, h]

lemma ss_eq_zero_iff {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    (∑ i, ∑ j, ‖A i j‖ ^ 2) = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    have h1 : ∀ a ∈ (Finset.univ : Finset (Fin k)), (∑ b, ‖A a b‖ ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _).1 h
    have h2 : ∀ b ∈ (Finset.univ : Finset (Fin k)), ‖A i b‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 (h1 i (Finset.mem_univ _))
    have h3 := h2 j (Finset.mem_univ _)
    simpa using h3
  · rintro rfl
    simp

lemma ss_add_eq {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) :
    ∑ i, ∑ j, ‖(A + B) i j‖ ^ 2 =
      (∑ i, ∑ j, ‖A i j‖ ^ 2) + 2 * ((star A * B).trace).re + (∑ i, ∑ j, ‖B i j‖ ^ 2) := by
  rw [← re_trace_star_mul_self, ← re_trace_star_mul_self, ← re_trace_star_mul_self]
  have h : star (A + B) * (A + B) = star A * A + star A * B + star B * A + star B * B := by
    rw [star_add]; noncomm_ring
  rw [h, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    Complex.add_re, Complex.add_re, Complex.add_re, re_trace_star_mul_comm B A]
  ring

lemma ss_sub_eq {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) :
    ∑ i, ∑ j, ‖(A - B) i j‖ ^ 2 =
      (∑ i, ∑ j, ‖A i j‖ ^ 2) - 2 * ((star A * B).trace).re + (∑ i, ∑ j, ‖B i j‖ ^ 2) := by
  rw [← re_trace_star_mul_self, ← re_trace_star_mul_self, ← re_trace_star_mul_self]
  have h : star (A - B) * (A - B) = star A * A - star A * B - star B * A + star B * B := by
    rw [star_sub]; noncomm_ring
  rw [h, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
    Complex.add_re, Complex.sub_re, Complex.sub_re, re_trace_star_mul_comm B A]
  ring

lemma abs_re_trace_star_mul_le {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) :
    |((star A * B).trace).re| ≤
      Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) * Real.sqrt (∑ i, ∑ j, ‖B i j‖ ^ 2) := by
  let u : EuclideanSpace ℂ (Fin k × Fin k) := WithLp.toLp 2 (fun p => A p.1 p.2)
  let v : EuclideanSpace ℂ (Fin k × Fin k) := WithLp.toLp 2 (fun p => B p.1 p.2)
  have hu : ‖u‖ = Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg u), EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  have hv : ‖v‖ = Real.sqrt (∑ i, ∑ j, ‖B i j‖ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg v), EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  have hin : @inner ℂ _ _ u v = (star A * B).trace := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fintype.sum_prod_type,
      Matrix.trace, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.star_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    change B j i * star (A j i) = star (A j i) * B j i
    rw [mul_comm]
  rw [← hu, ← hv, ← hin]
  exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm u v)

lemma ss_le_card_mul_opNorm_sq {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ (k : ℝ) * ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) A‖ ^ 2 := by
  have h := ss_mul_left_le A (1 : Matrix (Fin k) (Fin k) ℂ)
  have h1 : ∑ i : Fin k, ∑ j : Fin k, ‖(1 : Matrix (Fin k) (Fin k) ℂ) i j‖ ^ 2 = (k : ℝ) := by
    rw [← re_trace_star_mul_self]
    simp [Matrix.trace]
  rw [mul_one, h1, mul_comm] at h
  exact h

lemma q_le_opNorm_sq {k : ℕ} (hk : 0 < k) (A : Matrix (Fin k) (Fin k) ℂ) :
    (∑ i, ∑ j, ‖A i j‖ ^ 2) / (k : ℝ) ≤ ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) A‖ ^ 2 := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  rw [div_le_iff₀ hk']
  linarith [ss_le_card_mul_opNorm_sq A]

lemma sqrt_ss_add_le {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) :
    Real.sqrt (∑ i, ∑ j, ‖(A + B) i j‖ ^ 2) ≤
      Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) + Real.sqrt (∑ i, ∑ j, ‖B i j‖ ^ 2) := by
  let u : EuclideanSpace ℂ (Fin k × Fin k) := WithLp.toLp 2 (fun p => A p.1 p.2)
  let v : EuclideanSpace ℂ (Fin k × Fin k) := WithLp.toLp 2 (fun p => B p.1 p.2)
  have hnorm : ∀ X : Matrix (Fin k) (Fin k) ℂ,
      ‖(WithLp.toLp 2 (fun p : Fin k × Fin k => X p.1 p.2) : EuclideanSpace ℂ (Fin k × Fin k))‖ =
        Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2) := fun X => by
    rw [← Real.sqrt_sq (norm_nonneg _), EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  have huv : u + v = WithLp.toLp 2 (fun p : Fin k × Fin k => (A + B) p.1 p.2) := by
    ext ⟨i, j⟩; rfl
  have h := norm_add_le u v
  rw [huv, hnorm (A + B), hnorm A, hnorm B] at h
  exact h

lemma sqrt_ss_sum_le {k : ℕ} {α : Type*} (s : Finset α) (f : α → Matrix (Fin k) (Fin k) ℂ) :
    Real.sqrt (∑ i, ∑ j, ‖(∑ a ∈ s, f a) i j‖ ^ 2) ≤
      ∑ a ∈ s, Real.sqrt (∑ i, ∑ j, ‖(f a) i j‖ ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (sqrt_ss_add_le _ _).trans (by gcongr)

lemma ss_smul {k : ℕ} (c : ℂ) (A : Matrix (Fin k) (Fin k) ℂ) :
    ∑ i, ∑ j, ‖(c • A) i j‖ ^ 2 = ‖c‖ ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]

lemma sqrt_ss_smul {k : ℕ} (c : ℂ) (A : Matrix (Fin k) (Fin k) ℂ) :
    Real.sqrt (∑ i, ∑ j, ‖(c • A) i j‖ ^ 2) = ‖c‖ * Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  rw [ss_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

lemma ss_star {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ∑ i, ∑ j, ‖(star A) i j‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [Finset.sum_comm]
  simp [Matrix.star_apply]

lemma ss_comm_unitary_eq {k : ℕ} {U : Matrix (Fin k) (Fin k) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) (x : Matrix (Fin k) (Fin k) ℂ) :
    ((∑ i, ∑ j, ‖(U * x - x * U) i j‖ ^ 2 : ℝ) : ℂ) =
      (star x * ((2 : ℂ) • x - (star U * x * U + U * x * star U))).trace := by
  rw [← trace_star_mul_self_eq]
  have h1 := Unitary.star_mul_self_of_mem hU
  have h2 := Unitary.mul_star_self_of_mem hU
  have hexp : star (U * x - x * U) * (U * x - x * U) =
      star x * (star U * U) * x - star x * star U * x * U - star U * star x * U * x +
        star U * star x * x * U := by
    rw [star_sub, star_mul, star_mul]; noncomm_ring
  rw [hexp, h1, mul_one, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub]
  have t1 : (star U * star x * x * U).trace = (star x * x).trace := by
    have ha : star U * star x * x * U = star U * (star x * x * U) := by noncomm_ring
    have hb : star x * x * U * star U = star x * x * (U * star U) := by noncomm_ring
    rw [ha, Matrix.trace_mul_comm, hb, h2, mul_one]
  have t2 : (star U * star x * U * x).trace = (star x * (U * x * star U)).trace := by
    have ha : star U * star x * U * x = star U * (star x * U * x) := by noncomm_ring
    rw [ha, Matrix.trace_mul_comm]
    congr 1; noncomm_ring
  rw [t1, t2]
  have t3 : star x * ((2 : ℂ) • x - (star U * x * U + U * x * star U)) =
      star x * x + star x * x - star x * star U * x * U - star x * (U * x * star U) := by
    rw [mul_sub, mul_add, mul_smul_comm, two_smul]; noncomm_ring
  rw [t3, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_add]
  ring

lemma ss_comm_unitary_le {k : ℕ} {U : Matrix (Fin k) (Fin k) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) (x : Matrix (Fin k) (Fin k) ℂ) :
    ∑ i, ∑ j, ‖(U * x - x * U) i j‖ ^ 2 ≤ 4 * ∑ i, ∑ j, ‖x i j‖ ^ 2 := by
  calc ∑ i, ∑ j, ‖(U * x - x * U) i j‖ ^ 2
      = ∑ i, ∑ j, ‖(U * x + -(x * U)) i j‖ ^ 2 := by rw [sub_eq_add_neg]
    _ ≤ 2 * (∑ i, ∑ j, ‖(U * x) i j‖ ^ 2) + 2 * (∑ i, ∑ j, ‖(-(x * U)) i j‖ ^ 2) :=
        ss_add_le _ _
    _ = 4 * ∑ i, ∑ j, ‖x i j‖ ^ 2 := by
        rw [ss_neg, ss_unitary_mul hU, ss_mul_unitary hU]; ring

/- ### Convex combinations of unitary conjugations and lazy Markov operators -/

lemma unitary_mix_opNorm_le {k : ℕ} {α : Type*} [Fintype α]
    (w : α → ℝ) (V : α → Matrix.unitaryGroup (Fin k) ℂ)
    (hw : ∀ s, 0 ≤ w s) (hsum : ∑ s, w s = 1) (x : Matrix (Fin k) (Fin k) ℂ) :
    ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ)
      (∑ s, (w s : ℂ) • (star (V s : Matrix (Fin k) (Fin k) ℂ) * x * (V s : Matrix (Fin k) (Fin k) ℂ)))‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ := by
  rw [map_sum]
  calc ‖∑ s, Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ)
          ((w s : ℂ) • (star (V s : Matrix (Fin k) (Fin k) ℂ) * x * (V s : Matrix (Fin k) (Fin k) ℂ)))‖
      ≤ ∑ s, ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ)
          ((w s : ℂ) • (star (V s : Matrix (Fin k) (Fin k) ℂ) * x * (V s : Matrix (Fin k) (Fin k) ℂ)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ s, w s * ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (hw s)]
        exact mul_le_mul_of_nonneg_left (opnorm_conj_le (V s).2 x) (hw s)
    _ = ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ := by
        rw [← Finset.sum_mul, hsum, one_mul]

lemma unitary_mix_ss_le {k : ℕ} {α : Type*} [Fintype α]
    (w : α → ℝ) (V : α → Matrix.unitaryGroup (Fin k) ℂ)
    (hw : ∀ s, 0 ≤ w s) (hsum : ∑ s, w s = 1) (x : Matrix (Fin k) (Fin k) ℂ) :
    ∑ i, ∑ j, ‖(∑ s, (w s : ℂ) • (star (V s : Matrix (Fin k) (Fin k) ℂ) * x *
        (V s : Matrix (Fin k) (Fin k) ℂ))) i j‖ ^ 2 ≤
      ∑ i, ∑ j, ‖x i j‖ ^ 2 := by
  have h1 : Real.sqrt (∑ i, ∑ j, ‖(∑ s, (w s : ℂ) •
      (star (V s : Matrix (Fin k) (Fin k) ℂ) * x * (V s : Matrix (Fin k) (Fin k) ℂ))) i j‖ ^ 2) ≤
      Real.sqrt (∑ i, ∑ j, ‖x i j‖ ^ 2) := by
    calc _ ≤ ∑ s, Real.sqrt (∑ i, ∑ j, ‖((w s : ℂ) •
            (star (V s : Matrix (Fin k) (Fin k) ℂ) * x * (V s : Matrix (Fin k) (Fin k) ℂ))) i j‖ ^ 2) :=
          sqrt_ss_sum_le _ _
      _ = ∑ s, w s * Real.sqrt (∑ i, ∑ j, ‖x i j‖ ^ 2) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [sqrt_ss_smul, Complex.norm_real, Real.norm_of_nonneg (hw s),
            ss_mul_unitary (V s).2, ss_unitary_mul (Unitary.star_mem (V s).2)]
      _ = Real.sqrt (∑ i, ∑ j, ‖x i j‖ ^ 2) := by rw [← Finset.sum_mul, hsum, one_mul]
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at h2
  exact h2

lemma unitary_mix_adjoint {k : ℕ} {α : Type*} [Fintype α]
    (w : α → ℝ) (V : α → Matrix.unitaryGroup (Fin k) ℂ)
    (x y : Matrix (Fin k) (Fin k) ℂ) :
    (star (∑ s, (w s : ℂ) • (star (V s : Matrix (Fin k) (Fin k) ℂ) * x *
        (V s : Matrix (Fin k) (Fin k) ℂ))) * y).trace =
      (star x * (∑ s, (w s : ℂ) • ((V s : Matrix (Fin k) (Fin k) ℂ) * y *
        star (V s : Matrix (Fin k) (Fin k) ℂ)))).trace := by
  rw [star_sum, Finset.sum_mul, Matrix.trace_sum, Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [star_smul, Complex.star_def, Complex.conj_ofReal, smul_mul_assoc, mul_smul_comm,
    Matrix.trace_smul, Matrix.trace_smul]
  congr 1
  have ha : star (star (V s : Matrix (Fin k) (Fin k) ℂ) * x * (V s : Matrix (Fin k) (Fin k) ℂ)) * y =
      star (V s : Matrix (Fin k) (Fin k) ℂ) * (star x * (V s : Matrix (Fin k) (Fin k) ℂ) * y) := by
    rw [star_mul, star_mul, star_star]; noncomm_ring
  rw [ha, Matrix.trace_mul_comm]
  congr 1; noncomm_ring

lemma unitary_mix_trace {k : ℕ} {α : Type*} [Fintype α]
    (w : α → ℝ) (V : α → Matrix.unitaryGroup (Fin k) ℂ)
    (hsum : ∑ s, w s = 1) (x : Matrix (Fin k) (Fin k) ℂ) :
    (∑ s, (w s : ℂ) • (star (V s : Matrix (Fin k) (Fin k) ℂ) * x *
      (V s : Matrix (Fin k) (Fin k) ℂ))).trace = x.trace := by
  rw [Matrix.trace_sum]
  have h : ∀ s, ((w s : ℂ) • (star (V s : Matrix (Fin k) (Fin k) ℂ) * x *
      (V s : Matrix (Fin k) (Fin k) ℂ))).trace = (w s : ℂ) * x.trace := fun s => by
    rw [Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm, ← mul_assoc,
      Unitary.mul_star_self_of_mem (V s).2, one_mul]
  simp_rw [h, ← Finset.sum_mul, ← Complex.ofReal_sum, hsum, Complex.ofReal_one, one_mul]

lemma comm_star_of_comm_unitary {k : ℕ} {U : Matrix (Fin k) (Fin k) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) {e : Matrix (Fin k) (Fin k) ℂ}
    (hc : U * e = e * U) : star U * e = e * star U := by
  calc star U * e = star U * (e * U) * star U := by
        rw [mul_assoc, mul_assoc, Unitary.mul_star_self_of_mem hU, mul_one]
    _ = star U * (U * e) * star U := by rw [hc]
    _ = (star U * U) * e * star U := by noncomm_ring
    _ = e * star U := by rw [Unitary.star_mul_self_of_mem hU, one_mul]

lemma unitary_mix_comm {k : ℕ} {α : Type*} [Fintype α]
    (w : α → ℝ) (V : α → Matrix.unitaryGroup (Fin k) ℂ)
    {e : Matrix (Fin k) (Fin k) ℂ}
    (hc : ∀ s, (V s : Matrix (Fin k) (Fin k) ℂ) * e = e * (V s : Matrix (Fin k) (Fin k) ℂ))
    (x : Matrix (Fin k) (Fin k) ℂ) :
    (∑ s, (w s : ℂ) • (star (V s : Matrix (Fin k) (Fin k) ℂ) * (e * x * e) *
      (V s : Matrix (Fin k) (Fin k) ℂ))) =
      e * (∑ s, (w s : ℂ) • (star (V s : Matrix (Fin k) (Fin k) ℂ) * x *
        (V s : Matrix (Fin k) (Fin k) ℂ))) * e := by
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  have h1 := comm_star_of_comm_unitary (V s).2 (hc s)
  calc star (V s : Matrix (Fin k) (Fin k) ℂ) * (e * x * e) * (V s : Matrix (Fin k) (Fin k) ℂ)
      = (star (V s : Matrix (Fin k) (Fin k) ℂ) * e) * x * (e * (V s : Matrix (Fin k) (Fin k) ℂ)) := by
        noncomm_ring
    _ = (e * star (V s : Matrix (Fin k) (Fin k) ℂ)) * x * ((V s : Matrix (Fin k) (Fin k) ℂ) * e) := by
        rw [h1, hc s]
    _ = e * (star (V s : Matrix (Fin k) (Fin k) ℂ) * x * (V s : Matrix (Fin k) (Fin k) ℂ)) * e := by
        noncomm_ring

lemma unitary_mix_fix {k : ℕ} {α : Type*} [Fintype α]
    (w : α → ℝ) (V : α → Matrix.unitaryGroup (Fin k) ℂ)
    (hsum : ∑ s, w s = 1) {e : Matrix (Fin k) (Fin k) ℂ}
    (hc : ∀ s, (V s : Matrix (Fin k) (Fin k) ℂ) * e = e * (V s : Matrix (Fin k) (Fin k) ℂ)) :
    (∑ s, (w s : ℂ) • (star (V s : Matrix (Fin k) (Fin k) ℂ) * e *
      (V s : Matrix (Fin k) (Fin k) ℂ))) = e := by
  have h : ∀ s, (w s : ℂ) • (star (V s : Matrix (Fin k) (Fin k) ℂ) * e *
      (V s : Matrix (Fin k) (Fin k) ℂ)) = (w s : ℂ) • e := fun s => by
    rw [mul_assoc, ← hc s, ← mul_assoc, Unitary.star_mul_self_of_mem (V s).2, one_mul]
  simp_rw [h, ← Finset.sum_smul, ← Complex.ofReal_sum, hsum, Complex.ofReal_one, one_smul]

/- ### Self-adjoint contractive lazy operators `T = (1/2) I + (1/2) S` -/

lemma lazy_inner_sub_sq {k : ℕ} (S : Module.End ℂ (Matrix (Fin k) (Fin k) ℂ))
    (hSss : ∀ x, ∑ i, ∑ j, ‖(S x) i j‖ ^ 2 ≤ ∑ i, ∑ j, ‖x i j‖ ^ 2)
    (x : Matrix (Fin k) (Fin k) ℂ) :
    let T : Module.End ℂ (Matrix (Fin k) (Fin k) ℂ) := (1 / 2 : ℂ) • 1 + (1 / 2 : ℂ) • S
    ∑ i, ∑ j, ‖(T x) i j‖ ^ 2 ≤ ((star x * T x).trace).re := by
  intro T
  have hTx : T x = (1 / 2 : ℂ) • (x + S x) := by
    simp only [T, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, smul_add]
  have h1 : ∑ i, ∑ j, ‖(T x) i j‖ ^ 2 =
      (1 / 4 : ℝ) * ((∑ i, ∑ j, ‖x i j‖ ^ 2) + 2 * ((star x * S x).trace).re +
        (∑ i, ∑ j, ‖(S x) i j‖ ^ 2)) := by
    rw [hTx, ss_smul, ss_add_eq]
    have hn : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real]
      norm_num
    rw [hn]
    ring
  have h2 : ((star x * T x).trace).re =
      (1 / 2 : ℝ) * (∑ i, ∑ j, ‖x i j‖ ^ 2) + (1 / 2 : ℝ) * ((star x * S x).trace).re := by
    rw [hTx, mul_smul_comm, mul_add, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul, Complex.add_re,
      re_trace_star_mul_self]
    ring
  linarith [hSss x]

lemma pow_sa {k : ℕ} (T : Module.End ℂ (Matrix (Fin k) (Fin k) ℂ))
    (hTsa : ∀ x y, (star (T x) * y).trace = (star x * T y).trace)
    (r : ℕ) (x y : Matrix (Fin k) (Fin k) ℂ) :
    (star ((T ^ r) x) * y).trace = (star x * (T ^ r) y).trace := by
  induction r generalizing x y with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, hTsa, ih, ← Module.End.mul_apply, ← pow_succ, pow_succ']

lemma pow_ss_le {k : ℕ} (T : Module.End ℂ (Matrix (Fin k) (Fin k) ℂ))
    (hTss : ∀ x, ∑ i, ∑ j, ‖(T x) i j‖ ^ 2 ≤ ∑ i, ∑ j, ‖x i j‖ ^ 2)
    (r : ℕ) (x : Matrix (Fin k) (Fin k) ℂ) :
    ∑ i, ∑ j, ‖((T ^ r) x) i j‖ ^ 2 ≤ ∑ i, ∑ j, ‖x i j‖ ^ 2 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (hTss _).trans ih

lemma pow_opNorm_le {k : ℕ} (T : Module.End ℂ (Matrix (Fin k) (Fin k) ℂ))
    (hTop : ∀ x, ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (T x)‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖)
    (r : ℕ) (x : Matrix (Fin k) (Fin k) ℂ) :
    ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) ((T ^ r) x)‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (hTop _).trans ih

lemma pow_pos_re {k : ℕ} (T : Module.End ℂ (Matrix (Fin k) (Fin k) ℂ))
    (hTsa : ∀ x y, (star (T x) * y).trace = (star x * T y).trace)
    (hTpos : ∀ x, 0 ≤ ((star x * T x).trace).re)
    (r : ℕ) (x : Matrix (Fin k) (Fin k) ℂ) :
    0 ≤ ((star x * (T ^ r) x).trace).re := by
  rcases Nat.even_or_odd r with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [pow_add, Module.End.mul_apply, ← pow_sa T hTsa m, re_trace_star_mul_self]
    positivity
  · rw [pow_succ, two_mul, pow_add, Module.End.mul_apply, Module.End.mul_apply,
      ← pow_sa T hTsa m]
    have hcomm : (T ^ m) (T x) = T ((T ^ m) x) := by
      rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply]
    rw [hcomm]
    exact hTpos _

lemma energy_pow_le {k : ℕ} (T : Module.End ℂ (Matrix (Fin k) (Fin k) ℂ))
    (hTsa : ∀ x y, (star (T x) * y).trace = (star x * T y).trace)
    (hTpos : ∀ x, 0 ≤ ((star x * T x).trace).re)
    (r : ℕ) (x : Matrix (Fin k) (Fin k) ℂ) :
    (2 * (r : ℝ) + 1) * ((star ((T ^ r) x) * ((T ^ r) x - T ((T ^ r) x))).trace).re ≤
      ∑ i, ∑ j, ‖x i j‖ ^ 2 := by
  let c : ℕ → ℝ := fun j => ((star x * ((T ^ j) x - (T ^ (j + 1)) x)).trace).re
  have hdec : ∀ j, c (j + 1) ≤ c j := fun j => by
    have hdiff : c j - c (j + 1) =
        ((star x * ((T ^ j) ((1 - T) ((1 - T) x)))).trace).re := by
      simp only [c, ← Complex.sub_re, ← Matrix.trace_sub, ← mul_sub]
      congr 2
      have h1 : (1 - T) ((1 - T) x) = x - T x - T (x - T x) := by simp
      have p1 : ∀ y, (T ^ j) (T y) = (T ^ (j + 1)) y := fun y => by
        rw [← Module.End.mul_apply, ← pow_succ]
      have p2 : (T ^ j) (T (T x)) = (T ^ (j + 2)) x := by
        rw [p1, ← Module.End.mul_apply, ← pow_succ]
      rw [h1, map_sub, map_sub, map_sub, map_sub, p1, p2]
    have hnn : 0 ≤ ((star x * ((T ^ j) ((1 - T) ((1 - T) x)))).trace).re := by
      have h1Tsa : ∀ a b, (star ((1 - T) a) * b).trace = (star a * (1 - T) b).trace := fun a b => by
        simp only [LinearMap.sub_apply, Module.End.one_apply, star_sub, sub_mul, mul_sub,
          Matrix.trace_sub, hTsa]
      have hcomm1 : ∀ m y, (T ^ m) ((1 - T) y) = (1 - T) ((T ^ m) y) := fun m y => by
        simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
        have : (T ^ m) (T y) = T ((T ^ m) y) := by
          rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply]
        rw [this]
      rcases Nat.even_or_odd j with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · rw [pow_add, Module.End.mul_apply, ← pow_sa T hTsa m, hcomm1, ← h1Tsa, hcomm1,
          re_trace_star_mul_self]
        positivity
      · rw [pow_succ, two_mul, pow_add, Module.End.mul_apply, Module.End.mul_apply,
          ← pow_sa T hTsa m]
        have hstep : (T ^ m) (T ((1 - T) ((1 - T) x))) =
            (1 - T) (T ((1 - T) ((T ^ m) x))) := by
          rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply]
          have hT1 : T ((1 - T) ((1 - T) ((T ^ m) x))) =
              (1 - T) (T ((1 - T) ((T ^ m) x))) := by
            simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
          rw [hcomm1, hcomm1, hT1]
        rw [hstep, ← h1Tsa]
        exact hTpos _
    linarith
  have hanti : Antitone c := antitone_nat_of_succ_le hdec
  have hcr : c (2 * r) = ((star ((T ^ r) x) * ((T ^ r) x - T ((T ^ r) x))).trace).re := by
    simp only [c]
    have h1 : (T ^ (2 * r)) x - (T ^ (2 * r + 1)) x =
        (T ^ r) ((T ^ r) x - T ((T ^ r) x)) := by
      rw [map_sub, ← Module.End.mul_apply, ← pow_add, ← two_mul]
      have h2 : (T ^ r) (T ((T ^ r) x)) = (T ^ (2 * r + 1)) x := by
        rw [← Module.End.mul_apply, ← pow_succ, ← Module.End.mul_apply, ← pow_add]
        congr 2; omega
      rw [h2]
    rw [h1, ← pow_sa T hTsa r]
  have hsum : ∑ j ∈ Finset.range (2 * r + 1), c j =
      (∑ i, ∑ j, ‖x i j‖ ^ 2) - ((star x * (T ^ (2 * r + 1)) x).trace).re := by
    have ht : ∑ j ∈ Finset.range (2 * r + 1), c j =
        ∑ j ∈ Finset.range (2 * r + 1),
          (((star x * (T ^ j) x).trace).re - ((star x * (T ^ (j + 1)) x).trace).re) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [c, mul_sub, Matrix.trace_sub, Complex.sub_re]
    rw [ht, Finset.sum_range_sub' (fun j => ((star x * (T ^ j) x).trace).re) (2 * r + 1)]
    simp [re_trace_star_mul_self]
  have hle : (2 * (r : ℝ) + 1) * c (2 * r) ≤ ∑ j ∈ Finset.range (2 * r + 1), c j := by
    have hcard : ((Finset.range (2 * r + 1)).card : ℝ) = 2 * (r : ℝ) + 1 := by
      rw [Finset.card_range]; push_cast; ring
    rw [← hcard, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun j hj => hanti (Nat.le_of_lt_succ (Finset.mem_range.1 hj))
  rw [← hcr]
  linarith [hle, hsum, pow_pos_re T hTsa hTpos (2 * r + 1) x]

/- ### Representing lazy operators and their powers as unitary mixtures -/

lemma unitary_tuple_mix {k : ℕ} {α : Type*} [Fintype α] [Nonempty α]
    (U : α → Matrix.unitaryGroup (Fin k) ℂ) :
    ∃ (L : ℕ) (w : Fin L → ℝ) (V : Fin L → Matrix.unitaryGroup (Fin k) ℂ),
      (∀ s, 0 ≤ w s) ∧ (∑ s, w s = 1) ∧
      (∀ s, (V s : Matrix (Fin k) (Fin k) ℂ) = 1 ∨
        ∃ a, (V s : Matrix (Fin k) (Fin k) ℂ) = (U a : Matrix (Fin k) (Fin k) ℂ) ∨
          (V s : Matrix (Fin k) (Fin k) ℂ) = star (U a : Matrix (Fin k) (Fin k) ℂ)) ∧
      ∀ x : Matrix (Fin k) (Fin k) ℂ,
        (1 / 2 : ℂ) • x + (1 / (4 * (Fintype.card α : ℂ))) •
          ∑ a, ((U a : Matrix (Fin k) (Fin k) ℂ) * x * star (U a : Matrix (Fin k) (Fin k) ℂ) +
            star (U a : Matrix (Fin k) (Fin k) ℂ) * x * (U a : Matrix (Fin k) (Fin k) ℂ)) =
          ∑ s, (w s : ℂ) • (star (V s : Matrix (Fin k) (Fin k) ℂ) * x *
            (V s : Matrix (Fin k) (Fin k) ℂ)) := by
  classical
  let e : Option (Bool × α) ≃ Fin (Fintype.card (Option (Bool × α))) := Fintype.equivFin _
  let w0 : Option (Bool × α) → ℝ := fun o =>
    match o with
    | none => 1 / 2
    | some _ => 1 / (4 * (Fintype.card α : ℝ))
  let V0 : Option (Bool × α) → Matrix.unitaryGroup (Fin k) ℂ := fun o =>
    match o with
    | none => 1
    | some (false, a) => U a
    | some (true, a) => (U a)⁻¹
  refine ⟨Fintype.card (Option (Bool × α)), fun s => w0 (e.symm s), fun s => V0 (e.symm s),
    ?_, ?_, ?_, ?_⟩
  · intro s
    dsimp only
    cases h : e.symm s with
    | none => norm_num [w0]
    | some _ => dsimp only [w0]; positivity
  · dsimp only
    rw [Equiv.sum_comp e.symm w0, Fintype.sum_option, Fintype.sum_prod_type]
    have hpos : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    simp only [w0, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_bool]
    field_simp [hpos]
    ring
  · intro s
    dsimp only
    cases h : e.symm s with
    | none => exact Or.inl rfl
    | some p =>
      rcases p with ⟨b, a⟩
      cases b
      · exact Or.inr ⟨a, Or.inl rfl⟩
      · exact Or.inr ⟨a, Or.inr rfl⟩
  · intro x
    rw [Equiv.sum_comp e.symm (fun o => (w0 o : ℂ) • (star (V0 o : Matrix (Fin k) (Fin k) ℂ) * x *
      (V0 o : Matrix (Fin k) (Fin k) ℂ)))]
    rw [Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [w0, V0, Matrix.UnitaryGroup.one_val, star_one, one_mul, mul_one,
      Matrix.UnitaryGroup.inv_val, star_star, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast, ← Finset.smul_sum,
      ← smul_add, ← Finset.sum_add_distrib]

lemma mix_comp {k : ℕ}
    {L1 L2 : ℕ} (w1 : Fin L1 → ℝ) (V1 : Fin L1 → Matrix.unitaryGroup (Fin k) ℂ)
    (w2 : Fin L2 → ℝ) (V2 : Fin L2 → Matrix.unitaryGroup (Fin k) ℂ)
    (hw1 : ∀ s, 0 ≤ w1 s) (hs1 : ∑ s, w1 s = 1)
    (hw2 : ∀ t, 0 ≤ w2 t) (hs2 : ∑ t, w2 t = 1) :
    ∃ (L : ℕ) (w : Fin L → ℝ) (V : Fin L → Matrix.unitaryGroup (Fin k) ℂ),
      (∀ r, 0 ≤ w r) ∧ (∑ r, w r = 1) ∧
      (∀ e : Matrix (Fin k) (Fin k) ℂ,
        (∀ s, (V1 s : Matrix (Fin k) (Fin k) ℂ) * e = e * (V1 s : Matrix (Fin k) (Fin k) ℂ)) →
        (∀ t, (V2 t : Matrix (Fin k) (Fin k) ℂ) * e = e * (V2 t : Matrix (Fin k) (Fin k) ℂ)) →
        ∀ r, (V r : Matrix (Fin k) (Fin k) ℂ) * e = e * (V r : Matrix (Fin k) (Fin k) ℂ)) ∧
      ∀ x : Matrix (Fin k) (Fin k) ℂ,
        (∑ s, (w1 s : ℂ) • (star (V1 s : Matrix (Fin k) (Fin k) ℂ) *
          (∑ t, (w2 t : ℂ) • (star (V2 t : Matrix (Fin k) (Fin k) ℂ) * x *
            (V2 t : Matrix (Fin k) (Fin k) ℂ))) *
          (V1 s : Matrix (Fin k) (Fin k) ℂ))) =
        ∑ r, (w r : ℂ) • (star (V r : Matrix (Fin k) (Fin k) ℂ) * x *
          (V r : Matrix (Fin k) (Fin k) ℂ)) := by
  let e : Fin L1 × Fin L2 ≃ Fin (L1 * L2) := finProdFinEquiv
  refine ⟨L1 * L2, fun r => w1 (e.symm r).1 * w2 (e.symm r).2,
    fun r => V2 (e.symm r).2 * V1 (e.symm r).1, ?_, ?_, ?_, ?_⟩
  · intro r; exact mul_nonneg (hw1 _) (hw2 _)
  · dsimp only
    rw [Equiv.sum_comp e.symm (fun p : Fin L1 × Fin L2 => w1 p.1 * w2 p.2), Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hs2, mul_one, hs1]
  · intro M h1 h2 r
    change (V2 (e.symm r).2 : Matrix (Fin k) (Fin k) ℂ) * (V1 (e.symm r).1 : Matrix (Fin k) (Fin k) ℂ) * M =
      M * ((V2 (e.symm r).2 : Matrix (Fin k) (Fin k) ℂ) * (V1 (e.symm r).1 : Matrix (Fin k) (Fin k) ℂ))
    rw [mul_assoc, h1, ← mul_assoc, h2, mul_assoc]
  · intro x
    dsimp only
    rw [Equiv.sum_comp e.symm (fun p : Fin L1 × Fin L2 =>
      ((w1 p.1 * w2 p.2 : ℝ) : ℂ) •
        (star ((V2 p.2 * V1 p.1 : Matrix.unitaryGroup (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ) *
          x * ((V2 p.2 * V1 p.1 : Matrix.unitaryGroup (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ)))]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    change (w1 s : ℂ) • (star (V1 s : Matrix (Fin k) (Fin k) ℂ) *
        ((w2 t : ℂ) • (star (V2 t : Matrix (Fin k) (Fin k) ℂ) * x * (V2 t : Matrix (Fin k) (Fin k) ℂ))) *
        (V1 s : Matrix (Fin k) (Fin k) ℂ)) =
      ((w1 s * w2 t : ℝ) : ℂ) •
        (star ((V2 t : Matrix (Fin k) (Fin k) ℂ) * (V1 s : Matrix (Fin k) (Fin k) ℂ)) *
          x * ((V2 t : Matrix (Fin k) (Fin k) ℂ) * (V1 s : Matrix (Fin k) (Fin k) ℂ)))
    rw [mul_smul_comm, smul_mul_assoc, smul_smul, Complex.ofReal_mul, star_mul]
    noncomm_ring

lemma mix_pow_rep {k : ℕ} {L0 : ℕ}
    (w0 : Fin L0 → ℝ) (V0 : Fin L0 → Matrix.unitaryGroup (Fin k) ℂ)
    (hw0 : ∀ s, 0 ≤ w0 s) (hs0 : ∑ s, w0 s = 1)
    (Q : Module.End ℂ (Matrix (Fin k) (Fin k) ℂ))
    (hQ : ∀ x, Q x = ∑ s, (w0 s : ℂ) • (star (V0 s : Matrix (Fin k) (Fin k) ℂ) * x *
      (V0 s : Matrix (Fin k) (Fin k) ℂ)))
    (N : ℕ) :
    ∃ (L : ℕ) (w : Fin L → ℝ) (V : Fin L → Matrix.unitaryGroup (Fin k) ℂ),
      (∀ s, 0 ≤ w s) ∧ (∑ s, w s = 1) ∧
      (∀ e : Matrix (Fin k) (Fin k) ℂ,
        (∀ s, (V0 s : Matrix (Fin k) (Fin k) ℂ) * e = e * (V0 s : Matrix (Fin k) (Fin k) ℂ)) →
        ∀ s, (V s : Matrix (Fin k) (Fin k) ℂ) * e = e * (V s : Matrix (Fin k) (Fin k) ℂ)) ∧
      ∀ x, (Q ^ N) x = ∑ s, (w s : ℂ) • (star (V s : Matrix (Fin k) (Fin k) ℂ) * x *
        (V s : Matrix (Fin k) (Fin k) ℂ)) := by
  induction N with
  | zero =>
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => by norm_num, by simp, ?_, ?_⟩
    · intro e _ _; simp
    · intro x; simp
  | succ N ih =>
    obtain ⟨L1, w1, V1, hw1, hs1, hc1, hrep1⟩ := ih
    obtain ⟨L, w, V, hw, hs, hc, hcomp⟩ := mix_comp w0 V0 w1 V1 hw0 hs0 hw1 hs1
    refine ⟨L, w, V, hw, hs, fun e he => hc e he (hc1 e he), fun x => ?_⟩
    rw [pow_succ', Module.End.mul_apply, hQ, hrep1, hcomp]

lemma mix_symm_of_sa {k L : ℕ} (w : Fin L → ℝ) (V : Fin L → Matrix.unitaryGroup (Fin k) ℂ)
    (hsa : ∀ x y : Matrix (Fin k) (Fin k) ℂ,
      (star (∑ s, (w s : ℂ) • (star (V s : Matrix (Fin k) (Fin k) ℂ) * x *
        (V s : Matrix (Fin k) (Fin k) ℂ))) * y).trace =
        (star x * (∑ s, (w s : ℂ) • (star (V s : Matrix (Fin k) (Fin k) ℂ) * y *
          (V s : Matrix (Fin k) (Fin k) ℂ)))).trace)
    (x : Matrix (Fin k) (Fin k) ℂ) :
    (∑ s, (w s : ℂ) • (star (V s : Matrix (Fin k) (Fin k) ℂ) * x *
      (V s : Matrix (Fin k) (Fin k) ℂ))) =
      ∑ s, (w s : ℂ) • ((V s : Matrix (Fin k) (Fin k) ℂ) * x *
        star (V s : Matrix (Fin k) (Fin k) ℂ)) := by
  let A := ∑ s, (w s : ℂ) • (star (V s : Matrix (Fin k) (Fin k) ℂ) * x *
    (V s : Matrix (Fin k) (Fin k) ℂ))
  let B := ∑ s, (w s : ℂ) • ((V s : Matrix (Fin k) (Fin k) ℂ) * x *
    star (V s : Matrix (Fin k) (Fin k) ℂ))
  have hzero : (star (A - B) * (A - B)).trace = 0 := by
    rw [mul_sub, Matrix.trace_sub, ← hsa (A - B) x, unitary_mix_adjoint w V (A - B) x, sub_self]
  have hss : ∑ i, ∑ j, ‖(A - B) i j‖ ^ 2 = 0 := by
    rw [← re_trace_star_mul_self, hzero, Complex.zero_re]
  exact sub_eq_zero.1 ((ss_eq_zero_iff (A - B)).1 hss)

/- ### Telescoping bound between `Q^N` and `T^N` -/

lemma conj_diff_sqrt_ss_le {k : ℕ} {U V : Matrix (Fin k) (Fin k) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin k) ℂ)
    {x : Matrix (Fin k) (Fin k) ℂ}
    (hx : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ ≤ 1) :
    Real.sqrt (∑ i, ∑ j, ‖(V * x * star V - U * x * star U) i j‖ ^ 2) ≤
      2 * Real.sqrt (∑ i, ∑ j, ‖(V - U) i j‖ ^ 2) := by
  have heq : V * x * star V - U * x * star U = (V - U) * x * star V + U * x * star (V - U) := by
    rw [star_sub]; noncomm_ring
  rw [heq]
  have h1 : Real.sqrt (∑ i, ∑ j, ‖((V - U) * x * star V) i j‖ ^ 2) ≤
      Real.sqrt (∑ i, ∑ j, ‖(V - U) i j‖ ^ 2) := by
    refine Real.sqrt_le_sqrt ?_
    rw [ss_mul_unitary (Unitary.star_mem hV)]
    calc ∑ i, ∑ j, ‖((V - U) * x) i j‖ ^ 2
        ≤ ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ ^ 2 * ∑ i, ∑ j, ‖(V - U) i j‖ ^ 2 :=
          ss_mul_right_le (V - U) x
      _ ≤ 1 ^ 2 * ∑ i, ∑ j, ‖(V - U) i j‖ ^ 2 := by gcongr
      _ = ∑ i, ∑ j, ‖(V - U) i j‖ ^ 2 := by ring
  have h2 : Real.sqrt (∑ i, ∑ j, ‖(U * x * star (V - U)) i j‖ ^ 2) ≤
      Real.sqrt (∑ i, ∑ j, ‖(V - U) i j‖ ^ 2) := by
    refine Real.sqrt_le_sqrt ?_
    rw [mul_assoc, ss_unitary_mul hU]
    calc ∑ i, ∑ j, ‖(x * star (V - U)) i j‖ ^ 2
        ≤ ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ ^ 2 * ∑ i, ∑ j, ‖(star (V - U)) i j‖ ^ 2 :=
          ss_mul_left_le x (star (V - U))
      _ ≤ 1 ^ 2 * ∑ i, ∑ j, ‖(V - U) i j‖ ^ 2 := by
          rw [ss_star]; gcongr
      _ = ∑ i, ∑ j, ‖(V - U) i j‖ ^ 2 := by ring
  linarith [sqrt_ss_add_le ((V - U) * x * star V) (U * x * star (V - U))]

lemma pow_diff_sqrt_ss_le {k : ℕ}
    (Q T : Module.End ℂ (Matrix (Fin k) (Fin k) ℂ))
    (hQss : ∀ x, ∑ i, ∑ j, ‖(Q x) i j‖ ^ 2 ≤ ∑ i, ∑ j, ‖x i j‖ ^ 2)
    (hTop : ∀ x, ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (T x)‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖)
    {D : ℝ}
    (hQT : ∀ x, ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ ≤ 1 →
      Real.sqrt (∑ i, ∑ j, ‖(Q x - T x) i j‖ ^ 2) ≤ D)
    (N : ℕ) (x : Matrix (Fin k) (Fin k) ℂ)
    (hx : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ ≤ 1) :
    Real.sqrt (∑ i, ∑ j, ‖((Q ^ N) x - (T ^ N) x) i j‖ ^ 2) ≤ (N : ℝ) * D := by
  induction N with
  | zero => simp
  | succ N ih =>
    have heq : (Q ^ (N + 1)) x - (T ^ (N + 1)) x =
        Q ((Q ^ N) x - (T ^ N) x) + (Q ((T ^ N) x) - T ((T ^ N) x)) := by
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, map_sub]
      abel
    rw [heq, Nat.cast_succ, add_mul, one_mul]
    have h1 : Real.sqrt (∑ i, ∑ j, ‖(Q ((Q ^ N) x - (T ^ N) x)) i j‖ ^ 2) ≤ (N : ℝ) * D :=
      (Real.sqrt_le_sqrt (hQss _)).trans ih
    have h2 : Real.sqrt (∑ i, ∑ j, ‖(Q ((T ^ N) x) - T ((T ^ N) x)) i j‖ ^ 2) ≤ D :=
      hQT _ ((pow_opNorm_le T hTop N x).trans hx)
    linarith [sqrt_ss_add_le (Q ((Q ^ N) x - (T ^ N) x)) (Q ((T ^ N) x) - T ((T ^ N) x))]

/- ### Corner scalar decay for lazy operators with a scalar gap -/

lemma proj_trace_ne_zero {k : ℕ} {e : Matrix (Fin k) (Fin k) ℂ}
    (hsa : star e = e) (hid : e * e = e) (hne : e ≠ 0) : e.trace ≠ 0 := by
  have heq : e.trace = ((∑ i, ∑ j, ‖e i j‖ ^ 2 : ℝ) : ℂ) := by
    rw [← trace_star_mul_self_eq, hsa, hid]
  rw [heq]
  exact Complex.ofReal_ne_zero.2 (mt (ss_eq_zero_iff e).1 hne)

lemma corner_scalar_decay {k : ℕ} {e : Matrix (Fin k) (Fin k) ℂ}
    (hsa : star e = e) (hid : e * e = e) (hne : e ≠ 0)
    (Q : Module.End ℂ (Matrix (Fin k) (Fin k) ℂ))
    (hQtr : ∀ x, (Q x).trace = x.trace)
    (hQfix : Q e = e)
    (hQcor : ∀ x, e * x * e = x → e * Q x * e = Q x)
    (hQlazy : ∀ x, ∑ i, ∑ j, ‖(Q x) i j‖ ^ 2 ≤ ((star x * Q x).trace).re)
    {c : ℝ} (hc1 : c ≤ 1)
    (hgap : ∀ x, e * x * e = x →
      c * (∑ i, ∑ j, ‖(x - (x.trace / e.trace) • e) i j‖ ^ 2) ≤
        ((star x * (x - Q x)).trace).re)
    (N : ℕ) (x : Matrix (Fin k) (Fin k) ℂ) (hx : e * x * e = x) :
    ∑ i, ∑ j, ‖((Q ^ N) x - (x.trace / e.trace) • e) i j‖ ^ 2 ≤
      (1 - c) ^ N * ∑ i, ∑ j, ‖x i j‖ ^ 2 := by
  have hetr : e.trace ≠ 0 := proj_trace_ne_zero hsa hid hne
  let α : ℂ := x.trace / e.trace
  let x0 : Matrix (Fin k) (Fin k) ℂ := x - α • e
  have hx0_cor : e * x0 * e = x0 := by
    simp only [x0, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, hx, hid]
  have hx0_tr : x0.trace = 0 := by
    simp only [x0, α, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, div_mul_cancel₀ _ hetr,
      sub_self]
  have hQpow_fix : ∀ r, (Q ^ r) e = e := fun r => by
    induction r with
    | zero => simp
    | succ r ih => rw [pow_succ', Module.End.mul_apply, ih, hQfix]
  have hQpow_cor : ∀ r y, e * y * e = y → e * (Q ^ r) y * e = (Q ^ r) y := fun r y hy => by
    induction r with
    | zero => simpa using hy
    | succ r ih => rw [pow_succ', Module.End.mul_apply]; exact hQcor _ ih
  have hQpow_tr : ∀ r y, ((Q ^ r) y).trace = y.trace := fun r y => by
    induction r with
    | zero => simp
    | succ r ih => rw [pow_succ', Module.End.mul_apply, hQtr, ih]
  have hstep : ∀ y, e * y * e = y → y.trace = 0 →
      ∑ i, ∑ j, ‖(Q y) i j‖ ^ 2 ≤ (1 - c) * ∑ i, ∑ j, ‖y i j‖ ^ 2 := fun y hy hyt => by
    have hg := hgap y hy
    rw [hyt, zero_div, zero_smul, sub_zero, mul_sub, Matrix.trace_sub, Complex.sub_re,
      re_trace_star_mul_self] at hg
    linarith [hQlazy y]
  have hpow : ∀ r, ∑ i, ∑ j, ‖((Q ^ r) x0) i j‖ ^ 2 ≤
      (1 - c) ^ r * ∑ i, ∑ j, ‖x0 i j‖ ^ 2 := fun r => by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ']
      calc ∑ i, ∑ j, ‖(Q ((Q ^ r) x0)) i j‖ ^ 2
          ≤ (1 - c) * ∑ i, ∑ j, ‖((Q ^ r) x0) i j‖ ^ 2 :=
            hstep _ (hQpow_cor r x0 hx0_cor) (by rw [hQpow_tr, hx0_tr])
        _ ≤ (1 - c) * ((1 - c) ^ r * ∑ i, ∑ j, ‖x0 i j‖ ^ 2) :=
            mul_le_mul_of_nonneg_left ih (by linarith)
        _ = (1 - c) * (1 - c) ^ r * ∑ i, ∑ j, ‖x0 i j‖ ^ 2 := by ring
  have horth : (star x0 * (α • e)).trace = 0 := by
    have he1 : e * x0 = x0 := by
      calc e * x0 = e * (e * x0 * e) := by rw [hx0_cor]
        _ = (e * e) * x0 * e := by noncomm_ring
        _ = x0 := by rw [hid, hx0_cor]
    have h2 : (star x0 * e).trace = 0 := by
      have hst : star (star x0 * e).trace = (e * x0).trace := by
        rw [Matrix.trace, star_sum, Matrix.trace]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Matrix.diag_apply, Matrix.mul_apply, star_sum, star_mul', Matrix.star_apply,
          star_star]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hsij : star (e j i) = e i j := by
          have := congrFun (congrFun hsa i) j
          simpa [Matrix.star_apply] using this
        rw [hsij, mul_comm]
      rw [he1, hx0_tr] at hst
      exact star_eq_zero.1 hst
    rw [mul_smul_comm, Matrix.trace_smul, h2, smul_zero]
  have hx0_le : ∑ i, ∑ j, ‖x0 i j‖ ^ 2 ≤ ∑ i, ∑ j, ‖x i j‖ ^ 2 := by
    have hsplit : x = x0 + α • e := by simp [x0]
    have hpyth := ss_add_eq x0 (α • e)
    rw [← hsplit, horth, Complex.zero_re] at hpyth
    have hnn : 0 ≤ ∑ i, ∑ j, ‖(α • e) i j‖ ^ 2 := by positivity
    linarith
  have heq : (Q ^ N) x - α • e = (Q ^ N) x0 := by
    simp only [x0, map_sub, map_smul, hQpow_fix]
  rw [heq]
  exact (hpow N).trans (mul_le_mul_of_nonneg_left hx0_le (pow_nonneg (by linarith) N))

/- ### Ultrafilter limits and Proposition 2.2 helpers -/

lemma exists_ultralimit_Icc (f : ℕ → ℝ) {a b : ℝ} (hf : ∀ n, f n ∈ Set.Icc a b) :
    ∃ L ∈ Set.Icc a b, Tendsto f (hyperfilter ℕ) (𝓝 L) := by
  have hmem : Set.Icc a b ∈ ((hyperfilter ℕ).map f : Filter ℝ) :=
    Filter.mem_map.2 (Filter.Eventually.of_forall hf)
  exact isCompact_Icc.ultrafilter_le_nhds ((hyperfilter ℕ).map f) (Filter.le_principal_iff.2 hmem)

lemma hyperfilter_le_atTop : (hyperfilter ℕ : Filter ℕ) ≤ atTop :=
  Filter.hyperfilter_le_cofinite.trans_eq Nat.cofinite_eq_atTop

lemma lazy_cauchy_of_gap {d : ℕ → ℕ} (hd : ∀ n, 0 < d n)
    (Tn : (n : ℕ) → Module.End ℂ (Matrix (Fin (d n)) (Fin (d n)) ℂ))
    (hTn_sa : ∀ n x y, (star (Tn n x) * y).trace = (star x * Tn n y).trace)
    (hTn_lazy : ∀ n x, ∑ i, ∑ j, ‖(Tn n x) i j‖ ^ 2 ≤ ((star x * Tn n x).trace).re)
    (hTn_ss : ∀ n x, ∑ i, ∑ j, ‖(Tn n x) i j‖ ^ 2 ≤ ∑ i, ∑ j, ‖x i j‖ ^ 2)
    (hTn_op : ∀ n x, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (Tn n x)‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) x‖)
    {κ0 : ℝ} (hκ0_pos : 0 < κ0) (hκ0_le : κ0 ≤ 1 / 2)
    (hgap : ∀ y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ,
      (∃ C : ℝ, ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (y n)‖ ≤ C) →
      ∃ e : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ,
        (∃ Ce : ℝ, ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (e n)‖ ≤ Ce) ∧
        (∀ r : ℕ, Tendsto (fun n => (∑ i, ∑ j, ‖(e n - (Tn n ^ r) (e n)) i j‖ ^ 2) / (d n : ℝ))
          (hyperfilter ℕ) (𝓝 0)) ∧
        ∀ ε > 0, ∀ᶠ n in hyperfilter ℕ,
          κ0 * ((∑ i, ∑ j, ‖(y n - e n) i j‖ ^ 2) / (d n : ℝ)) ≤
            ε + ((star (y n) * (y n - Tn n (y n))).trace).re / (d n : ℝ))
    (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ)
    (hy : ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (y n)‖ ≤ 1)
    (j k : ℕ) (hjk : j ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in hyperfilter ℕ,
      (∑ a, ∑ b, ‖((Tn n ^ k) (y n) - (Tn n ^ j) (y n)) a b‖ ^ 2) / (d n : ℝ) ≤ (1 - κ0) ^ j + ε := by
  let q : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ → ℝ :=
    fun n M => (∑ a, ∑ b, ‖M a b‖ ^ 2) / (d n : ℝ)
  have hy_q : ∀ r n, q n ((Tn n ^ r) (y n)) ∈ Set.Icc (0 : ℝ) 1 := fun r n => by
    constructor
    · positivity
    · calc q n ((Tn n ^ r) (y n))
          ≤ ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) ((Tn n ^ r) (y n))‖ ^ 2 :=
            q_le_opNorm_sq (hd n) _
        _ ≤ 1 ^ 2 := by
            gcongr; exact (pow_opNorm_le (Tn n) (hTn_op n) r (y n)).trans (hy n)
        _ = 1 := by ring
  choose a ha_mem ha_lim using fun r => exists_ultralimit_Icc (fun n => q n ((Tn n ^ r) (y n))) (hy_q r)
  have ha_anti : Antitone a := antitone_nat_of_succ_le fun r => by
    refine le_of_tendsto_of_tendsto' (ha_lim (r + 1)) (ha_lim r) fun n => ?_
    rw [pow_succ', Module.End.mul_apply]
    exact div_le_div_of_nonneg_right (hTn_ss n _) (Nat.cast_nonneg _)
  have ha_step : ∀ m r : ℕ, κ0 * (a m - a (m + r)) ≤ a m - a (m + 1) := by
    intro m r
    let z : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ := fun n => (Tn n ^ m) (y n)
    have hzB : ∃ C : ℝ, ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (z n)‖ ≤ C :=
      ⟨1, fun n => (pow_opNorm_le (Tn n) (hTn_op n) m (y n)).trans (hy n)⟩
    obtain ⟨e, ⟨Ce, hCe⟩, hefix, hegap⟩ := hgap z hzB
    have hCe_nn : 0 ≤ Ce := le_trans (norm_nonneg _) (hCe 0)
    let w : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ := fun n => z n - e n
    have hw_bound : ∀ n, q n (w n) ∈ Set.Icc (0 : ℝ) (2 + 2 * Ce ^ 2) := fun n => by
      constructor
      · positivity
      · calc q n (w n) ≤ 2 * q n (z n) + 2 * q n (e n) := q_sub_le _ _
          _ ≤ 2 * 1 + 2 * Ce ^ 2 := by
              gcongr
              · exact (hy_q m n).2
              · exact (q_le_opNorm_sq (hd n) (e n)).trans (by gcongr; exact hCe n)
          _ = 2 + 2 * Ce ^ 2 := by ring
    obtain ⟨Lw, _, hLw_lim⟩ := exists_ultralimit_Icc (fun n => q n (w n)) hw_bound
    have hLw_gap : κ0 * Lw ≤ a m - a (m + 1) := by
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      have h1 : Tendsto (fun n => κ0 * q n (w n)) (hyperfilter ℕ) (𝓝 (κ0 * Lw)) :=
        hLw_lim.const_mul κ0
      have h2 : Tendsto (fun n => δ + (q n (z n) - q n ((Tn n) (z n)))) (hyperfilter ℕ)
          (𝓝 (δ + (a m - a (m + 1)))) := by
        have hshift : ∀ n, q n ((Tn n) (z n)) = q n ((Tn n ^ (m + 1)) (y n)) := fun n => by
          simp [z, pow_succ', Module.End.mul_apply]
        simp_rw [hshift]
        exact tendsto_const_nhds.add ((ha_lim m).sub (ha_lim (m + 1)))
      have hle : ∀ᶠ n in hyperfilter ℕ,
          κ0 * q n (w n) ≤ δ + (q n (z n) - q n (Tn n (z n))) := by
        filter_upwards [hegap δ hδ] with n hn
        have hdn : (0 : ℝ) < (d n : ℝ) := Nat.cast_pos.2 (hd n)
        have hE : ((star (z n) * (z n - Tn n (z n))).trace).re / (d n : ℝ) ≤
            q n (z n) - q n (Tn n (z n)) := by
          have hl := hTn_lazy n (z n)
          rw [mul_sub, Matrix.trace_sub, Complex.sub_re, re_trace_star_mul_self, sub_div]
          exact sub_le_sub_left (div_le_div_of_nonneg_right hl hdn.le) _
        linarith
      have hlim := le_of_tendsto_of_tendsto h1 h2 hle
      linarith
    have ham_le : a m - a (m + r) ≤ Lw := by
      let err : ℕ → ℝ := fun n =>
        q n (z n) - q n ((Tn n ^ r) (z n)) - (q n (w n) - q n ((Tn n ^ r) (w n)))
      have herr_zero : Tendsto err (hyperfilter ℕ) (𝓝 0) := by
        have hexp : ∀ n, err n =
            2 * (((star (w n) * (e n - (Tn n ^ (2 * r)) (e n))).trace).re / (d n : ℝ)) +
            (2 * (((star ((Tn n ^ r) (e n)) * (e n - (Tn n ^ r) (e n))).trace).re / (d n : ℝ)) +
              q n (e n - (Tn n ^ r) (e n))) := by
          intro n
          have hz1 : z n = w n + e n := by simp [w]
          have hz2 : (Tn n ^ r) (z n) = (Tn n ^ r) (w n) + (Tn n ^ r) (e n) := by
            rw [hz1, map_add]
          have hq1 : q n (z n) = q n (w n) + 2 * (((star (w n) * e n).trace).re / (d n : ℝ)) + q n (e n) := by
            simp only [q, hz1, ss_add_eq]; ring
          have hq2 : q n ((Tn n ^ r) (z n)) =
              q n ((Tn n ^ r) (w n)) +
              2 * (((star ((Tn n ^ r) (w n)) * (Tn n ^ r) (e n)).trace).re / (d n : ℝ)) +
              q n ((Tn n ^ r) (e n)) := by
            simp only [q, hz2, ss_add_eq]; ring
          have hsa : (star ((Tn n ^ r) (w n)) * (Tn n ^ r) (e n)).trace =
              (star (w n) * (Tn n ^ (2 * r)) (e n)).trace := by
            rw [pow_sa (Tn n) (hTn_sa n) r, ← Module.End.mul_apply, ← pow_add, ← two_mul]
          have hsub_tr : ((star (w n) * (e n - (Tn n ^ (2 * r)) (e n))).trace).re =
              ((star (w n) * e n).trace).re - ((star (w n) * (Tn n ^ (2 * r)) (e n)).trace).re := by
            rw [mul_sub, Matrix.trace_sub, Complex.sub_re]
          have he_split : e n = (Tn n ^ r) (e n) + (e n - (Tn n ^ r) (e n)) := by abel
          have hqe : q n (e n) - q n ((Tn n ^ r) (e n)) =
              2 * (((star ((Tn n ^ r) (e n)) * (e n - (Tn n ^ r) (e n))).trace).re / (d n : ℝ)) +
              q n (e n - (Tn n ^ r) (e n)) := by
            have h1 := congrArg (fun M => q n M) he_split
            simp only [q, ss_add_eq, add_div, mul_div_assoc] at h1
            linarith
          simp only [err, hq1, hq2, hsa, hsub_tr, sub_div]
          linarith
        have hterm1 : Tendsto (fun n => (((star (w n) * (e n - (Tn n ^ (2 * r)) (e n))).trace).re / (d n : ℝ)))
            (hyperfilter ℕ) (𝓝 0) := by
          have hlim : Tendsto (fun n => Real.sqrt (2 + 2 * Ce ^ 2) *
              Real.sqrt (q n (e n - (Tn n ^ (2 * r)) (e n)))) (hyperfilter ℕ) (𝓝 0) := by
            have h := (hefix (2 * r)).sqrt.const_mul (Real.sqrt (2 + 2 * Ce ^ 2))
            rw [Real.sqrt_zero, mul_zero] at h
            exact h
          refine squeeze_zero_norm (fun n => ?_) hlim
          rw [Real.norm_eq_abs, abs_div, abs_of_pos (a := (d n : ℝ)) (Nat.cast_pos.2 (hd n))]
          have hdn : (0 : ℝ) < (d n : ℝ) := Nat.cast_pos.2 (hd n)
          have hcs := abs_re_trace_star_mul_le (w n) (e n - (Tn n ^ (2 * r)) (e n))
          calc |((star (w n) * (e n - (Tn n ^ (2 * r)) (e n))).trace).re| / (d n : ℝ)
              ≤ (Real.sqrt (∑ i, ∑ j, ‖(w n) i j‖ ^ 2) *
                  Real.sqrt (∑ i, ∑ j, ‖(e n - (Tn n ^ (2 * r)) (e n)) i j‖ ^ 2)) / (d n : ℝ) :=
                div_le_div_of_nonneg_right hcs hdn.le
            _ = Real.sqrt (q n (w n)) * Real.sqrt (q n (e n - (Tn n ^ (2 * r)) (e n))) := by
                simp only [q]
                rw [Real.sqrt_div (by positivity), Real.sqrt_div (by positivity),
                  div_mul_div_comm, Real.mul_self_sqrt hdn.le]
            _ ≤ Real.sqrt (2 + 2 * Ce ^ 2) * Real.sqrt (q n (e n - (Tn n ^ (2 * r)) (e n))) :=
                mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hw_bound n).2) (Real.sqrt_nonneg _)
        have hterm2 : Tendsto (fun n => (((star ((Tn n ^ r) (e n)) * (e n - (Tn n ^ r) (e n))).trace).re / (d n : ℝ)))
            (hyperfilter ℕ) (𝓝 0) := by
          have hlim : Tendsto (fun n => Ce * Real.sqrt (q n (e n - (Tn n ^ r) (e n))))
              (hyperfilter ℕ) (𝓝 0) := by
            have h := (hefix r).sqrt.const_mul Ce
            rw [Real.sqrt_zero, mul_zero] at h
            exact h
          refine squeeze_zero_norm (fun n => ?_) hlim
          rw [Real.norm_eq_abs, abs_div, abs_of_pos (a := (d n : ℝ)) (Nat.cast_pos.2 (hd n))]
          have hdn : (0 : ℝ) < (d n : ℝ) := Nat.cast_pos.2 (hd n)
          have hcs := abs_re_trace_star_mul_le ((Tn n ^ r) (e n)) (e n - (Tn n ^ r) (e n))
          have hTe_q : q n ((Tn n ^ r) (e n)) ≤ Ce ^ 2 := by
            calc q n ((Tn n ^ r) (e n))
                ≤ ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) ((Tn n ^ r) (e n))‖ ^ 2 :=
                  q_le_opNorm_sq (hd n) _
              _ ≤ Ce ^ 2 := by
                  gcongr; exact (pow_opNorm_le (Tn n) (hTn_op n) r (e n)).trans (hCe n)
          calc |((star ((Tn n ^ r) (e n)) * (e n - (Tn n ^ r) (e n))).trace).re| / (d n : ℝ)
              ≤ (Real.sqrt (∑ i, ∑ j, ‖((Tn n ^ r) (e n)) i j‖ ^ 2) *
                  Real.sqrt (∑ i, ∑ j, ‖(e n - (Tn n ^ r) (e n)) i j‖ ^ 2)) / (d n : ℝ) :=
                div_le_div_of_nonneg_right hcs hdn.le
            _ = Real.sqrt (q n ((Tn n ^ r) (e n))) * Real.sqrt (q n (e n - (Tn n ^ r) (e n))) := by
                simp only [q]
                rw [Real.sqrt_div (by positivity), Real.sqrt_div (by positivity),
                  div_mul_div_comm, Real.mul_self_sqrt hdn.le]
            _ ≤ Ce * Real.sqrt (q n (e n - (Tn n ^ r) (e n))) := by
                refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
                calc Real.sqrt (q n ((Tn n ^ r) (e n)))
                    ≤ Real.sqrt (Ce ^ 2) := Real.sqrt_le_sqrt hTe_q
                  _ = Ce := Real.sqrt_sq hCe_nn
        have hsum := (hterm1.const_mul 2).add ((hterm2.const_mul 2).add (hefix r))
        simp only [mul_zero, add_zero] at hsum
        exact hsum.congr fun n => (hexp n).symm
      have h1 : Tendsto (fun n => q n (z n) - q n ((Tn n ^ r) (z n))) (hyperfilter ℕ)
          (𝓝 (a m - a (m + r))) := by
        have hshift : ∀ n, q n ((Tn n ^ r) (z n)) = q n ((Tn n ^ (m + r)) (y n)) := fun n => by
          simp only [z, ← Module.End.mul_apply, ← pow_add, add_comm r m]
        simp_rw [hshift]
        exact (ha_lim m).sub (ha_lim (m + r))
      have hle : ∀ n, q n (z n) - q n ((Tn n ^ r) (z n)) ≤ q n (w n) + err n := fun n => by
        simp only [err]
        have hnn : 0 ≤ q n ((Tn n ^ r) (w n)) := by positivity
        linarith
      have h2 : Tendsto (fun n => q n (w n) + err n) (hyperfilter ℕ) (𝓝 (Lw + 0)) :=
        hLw_lim.add herr_zero
      simpa using le_of_tendsto_of_tendsto' h1 h2 hle
    have : κ0 * (a m - a (m + r)) ≤ κ0 * Lw := mul_le_mul_of_nonneg_left ham_le hκ0_pos.le
    linarith
  let b : ℝ := ⨅ r : ℕ, a r
  have hbdd : BddBelow (Set.range a) := ⟨0, by rintro _ ⟨r, rfl⟩; exact (ha_mem r).1⟩
  have hb_le : ∀ r, b ≤ a r := fun r => ciInf_le hbdd r
  have hb_nonneg : 0 ≤ b := le_ciInf fun r => (ha_mem r).1
  have hstep_b : ∀ m, a (m + 1) - b ≤ (1 - κ0) * (a m - b) := by
    intro m
    have h1 : ∀ r, a m - a (m + r) ≤ (a m - a (m + 1)) / κ0 := fun r => by
      rw [le_div_iff₀ hκ0_pos, mul_comm]
      exact ha_step m r
    have h2 : a m - b ≤ (a m - a (m + 1)) / κ0 := by
      have h3 : ∀ r, a m - (a m - a (m + 1)) / κ0 ≤ a r := fun r => by
        have hr : a (m + r) ≤ a r := ha_anti (Nat.le_add_left r m)
        linarith [h1 r]
      linarith [le_ciInf h3]
    rw [le_div_iff₀ hκ0_pos] at h2
    nlinarith
  have hgeom : ∀ m, a m - b ≤ (1 - κ0) ^ m := by
    intro m
    induction m with
    | zero => simp; linarith [(ha_mem 0).2, hb_nonneg]
    | succ m ih =>
      rw [pow_succ']
      exact (hstep_b m).trans (mul_le_mul_of_nonneg_left ih (by linarith))
  have hexp_le : ∀ n, q n ((Tn n ^ k) (y n) - (Tn n ^ j) (y n)) ≤
      q n ((Tn n ^ k) (y n)) + q n ((Tn n ^ j) (y n)) -
        2 * q n ((Tn n ^ ((j + k + 1) / 2)) (y n)) := by
    intro n
    have hdn : (0 : ℝ) < (d n : ℝ) := Nat.cast_pos.2 (hd n)
    simp only [q]
    rw [ss_sub_eq]
    have hinner : ∑ i, ∑ l, ‖((Tn n ^ ((j + k + 1) / 2)) (y n)) i l‖ ^ 2 ≤
        ((star ((Tn n ^ k) (y n)) * (Tn n ^ j) (y n)).trace).re := by
      rw [pow_sa (Tn n) (hTn_sa n) k, ← Module.End.mul_apply, ← pow_add]
      rcases Nat.even_or_odd (k + j) with ⟨t, ht⟩ | ⟨t, ht⟩
      · have hdiv : (j + k + 1) / 2 = t := by omega
        rw [hdiv, ht, pow_add, Module.End.mul_apply, ← pow_sa (Tn n) (hTn_sa n) t,
          re_trace_star_mul_self]
      · have hdiv : (j + k + 1) / 2 = t + 1 := by omega
        have h2t : (Tn n ^ (2 * t + 1)) (y n) = (Tn n ^ t) ((Tn n ^ t) (Tn n (y n))) := by
          rw [pow_succ, two_mul, pow_add, Module.End.mul_apply, Module.End.mul_apply]
        have hcomm : (Tn n ^ t) (Tn n (y n)) = Tn n ((Tn n ^ t) (y n)) := by
          rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply]
        rw [hdiv, ht, h2t, ← pow_sa (Tn n) (hTn_sa n) t, hcomm, pow_succ', Module.End.mul_apply]
        exact hTn_lazy n ((Tn n ^ t) (y n))
    have := div_le_div_of_nonneg_right hinner hdn.le
    ring_nf at this ⊢
    linarith
  have hmid : (j + k + 1) / 2 ≤ k := by omega
  have hlim_rhs : Tendsto
      (fun n => q n ((Tn n ^ k) (y n)) + q n ((Tn n ^ j) (y n)) -
        2 * q n ((Tn n ^ ((j + k + 1) / 2)) (y n)))
      (hyperfilter ℕ) (𝓝 (a k + a j - 2 * a ((j + k + 1) / 2))) :=
    ((ha_lim k).add (ha_lim j)).sub ((ha_lim ((j + k + 1) / 2)).const_mul 2)
  have hbound_val : a k + a j - 2 * a ((j + k + 1) / 2) < (1 - κ0) ^ j + ε := by
    have h1 : a k ≤ a ((j + k + 1) / 2) := ha_anti hmid
    have h2 : b ≤ a ((j + k + 1) / 2) := hb_le _
    have h3 : a j - b ≤ (1 - κ0) ^ j := hgeom j
    linarith
  filter_upwards [hlim_rhs.eventually (gt_mem_nhds hbound_val)] with n hn
  linarith [hexp_le n]

lemma lazy_uniform_transfer {d : ℕ → ℕ}
    (Tn : (n : ℕ) → Module.End ℂ (Matrix (Fin (d n)) (Fin (d n)) ℂ))
    {κ0 : ℝ}
    (hcauchy : ∀ (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ),
      (∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (y n)‖ ≤ 1) →
      ∀ j k : ℕ, j ≤ k → ∀ ε > 0, ∀ᶠ n in hyperfilter ℕ,
        (∑ a, ∑ b, ‖((Tn n ^ k) (y n) - (Tn n ^ j) (y n)) a b‖ ^ 2) / (d n : ℝ) ≤ (1 - κ0) ^ j + ε)
    (j k : ℕ) (hjk : j ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in hyperfilter ℕ, ∀ x : Matrix (Fin (d n)) (Fin (d n)) ℂ,
      ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) x‖ ≤ 1 →
      (∑ a, ∑ b, ‖((Tn n ^ k) x - (Tn n ^ j) x) a b‖ ^ 2) / (d n : ℝ) ≤ (1 - κ0) ^ j + ε := by
  classical
  by_contra hnot
  have hbad : ∀ᶠ n in hyperfilter ℕ,
      ∃ x : Matrix (Fin (d n)) (Fin (d n)) ℂ,
        ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) x‖ ≤ 1 ∧
        (1 - κ0) ^ j + ε < (∑ a, ∑ b, ‖((Tn n ^ k) x - (Tn n ^ j) x) a b‖ ^ 2) / (d n : ℝ) := by
    have hcompl := Ultrafilter.eventually_not.2 hnot
    filter_upwards [hcompl] with n hn
    push Not at hn
    exact hn
  let y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ := fun n =>
    if h : ∃ x : Matrix (Fin (d n)) (Fin (d n)) ℂ,
        ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) x‖ ≤ 1 ∧
        (1 - κ0) ^ j + ε < (∑ a, ∑ b, ‖((Tn n ^ k) x - (Tn n ^ j) x) a b‖ ^ 2) / (d n : ℝ)
    then h.choose else 0
  have hy : ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (y n)‖ ≤ 1 := fun n => by
    by_cases h : ∃ x : Matrix (Fin (d n)) (Fin (d n)) ℂ,
        ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) x‖ ≤ 1 ∧
        (1 - κ0) ^ j + ε < (∑ a, ∑ b, ‖((Tn n ^ k) x - (Tn n ^ j) x) a b‖ ^ 2) / (d n : ℝ)
    · dsimp only [y]; rw [dif_pos h]; exact h.choose_spec.1
    · dsimp only [y]; rw [dif_neg h]; simp
  have hgood := hcauchy y hy j k hjk (ε / 2) (by linarith)
  have hboth : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), False := by
    filter_upwards [hbad, hgood] with n hn1 hn2
    have hy_eq : y n = hn1.choose := by dsimp only [y]; rw [dif_pos hn1]
    rw [hy_eq] at hn2
    linarith [hn1.choose_spec.2]
  exact (Filter.NeBot.ne (inferInstance : (hyperfilter ℕ : Filter ℕ).NeBot))
    (Filter.eventually_false_iff_eq_bot.1 hboth)

lemma lazy_markov_props {k : ℕ} {α : Type*} [Fintype α] [Nonempty α]
    (U : α → Matrix.unitaryGroup (Fin k) ℂ) :
    ∃ (S T : Module.End ℂ (Matrix (Fin k) (Fin k) ℂ)),
      (∀ x, S x = (1 / (2 * (Fintype.card α : ℂ))) •
        ∑ a : α, ((U a : Matrix (Fin k) (Fin k) ℂ) * x * star (U a : Matrix (Fin k) (Fin k) ℂ) +
          star (U a : Matrix (Fin k) (Fin k) ℂ) * x * (U a : Matrix (Fin k) (Fin k) ℂ))) ∧
      (T = (1 / 2 : ℂ) • 1 + (1 / 2 : ℂ) • S) ∧
      (∀ x y, (star (T x) * y).trace = (star x * T y).trace) ∧
      (∀ x, ∑ i, ∑ j, ‖(T x) i j‖ ^ 2 ≤ ((star x * T x).trace).re) ∧
      (∀ x, ∑ i, ∑ j, ‖(T x) i j‖ ^ 2 ≤ ∑ i, ∑ j, ‖x i j‖ ^ 2) ∧
      (∀ x, ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (T x)‖ ≤
        ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖) ∧
      (∀ x, ∑ i, ∑ j, ‖(x - T x) i j‖ ^ 2 ≤ ((star x * (x - T x)).trace).re) ∧
      (∀ x, ((star x * (x - T x)).trace).re =
        (1 / (4 * (Fintype.card α : ℝ))) *
          ∑ a : α, ∑ i, ∑ j, ‖((U a : Matrix (Fin k) (Fin k) ℂ) * x -
            x * (U a : Matrix (Fin k) (Fin k) ℂ)) i j‖ ^ 2) := by
  have hcard_pos : (0 : ℝ) < (Fintype.card α : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  have hcard_ne : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hcard_cne : (Fintype.card α : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let S : Module.End ℂ (Matrix (Fin k) (Fin k) ℂ) :=
    { toFun := fun x =>
        (1 / (2 * (Fintype.card α : ℂ))) •
          ∑ a : α, ((U a : Matrix (Fin k) (Fin k) ℂ) * x * star (U a : Matrix (Fin k) (Fin k) ℂ) +
            star (U a : Matrix (Fin k) (Fin k) ℂ) * x * (U a : Matrix (Fin k) (Fin k) ℂ))
      map_add' := fun x y => by
        rw [← smul_add, ← Finset.sum_add_distrib]
        congr 1; refine Finset.sum_congr rfl fun a _ => by noncomm_ring
      map_smul' := fun r x => by
        simp only [RingHom.id_apply]
        rw [smul_comm r]
        congr 1
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [smul_add, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc] }
  let T : Module.End ℂ (Matrix (Fin k) (Fin k) ℂ) := (1 / 2 : ℂ) • 1 + (1 / 2 : ℂ) • S
  have hS_mix : ∀ x, S x =
      ∑ p : Bool × α, ((1 / (2 * (Fintype.card α : ℝ)) : ℝ) : ℂ) •
        (star ((if p.1 then (U p.2)⁻¹ else U p.2 : Matrix.unitaryGroup (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ) *
          x * ((if p.1 then (U p.2)⁻¹ else U p.2 : Matrix.unitaryGroup (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ)) := by
    intro x
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [S, LinearMap.coe_mk, AddHom.coe_mk, ↓reduceIte, Bool.false_eq_true,
      Matrix.UnitaryGroup.inv_val, star_star, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast, ← Finset.smul_sum,
      ← smul_add, ← Finset.sum_add_distrib]
  have hS_wsum : ∑ _p : Bool × α, (1 / (2 * (Fintype.card α : ℝ))) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
      nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hcard_ne]
  have hS_sa : ∀ x y, (star (S x) * y).trace = (star x * S y).trace := fun x y => by
    simp only [S, LinearMap.coe_mk, AddHom.coe_mk, star_smul, smul_mul_assoc, mul_smul_comm,
      Matrix.trace_smul, star_sum, Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum]
    have hcoef : star (1 / (2 * (Fintype.card α : ℂ))) = 1 / (2 * (Fintype.card α : ℂ)) := by
      rw [show (1 / (2 * (Fintype.card α : ℂ))) = ((1 / (2 * (Fintype.card α : ℝ)) : ℝ) : ℂ) by
          push_cast; rfl, Complex.star_def, Complex.conj_ofReal]
    rw [hcoef]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [star_add, add_mul, mul_add, Matrix.trace_add, Matrix.trace_add, add_comm]
    congr 1
    · have ha : star (star (U a : Matrix (Fin k) (Fin k) ℂ) * x * (U a : Matrix (Fin k) (Fin k) ℂ)) * y =
          star (U a : Matrix (Fin k) (Fin k) ℂ) * (star x * (U a : Matrix (Fin k) (Fin k) ℂ) * y) := by
        rw [star_mul, star_mul, star_star]; noncomm_ring
      rw [ha, Matrix.trace_mul_comm]; congr 1; noncomm_ring
    · have hb : star ((U a : Matrix (Fin k) (Fin k) ℂ) * x * star (U a : Matrix (Fin k) (Fin k) ℂ)) * y =
          (U a : Matrix (Fin k) (Fin k) ℂ) * (star x * star (U a : Matrix (Fin k) (Fin k) ℂ) * y) := by
        rw [star_mul, star_mul, star_star]; noncomm_ring
      rw [hb, Matrix.trace_mul_comm]; congr 1; noncomm_ring
  have hS_ss : ∀ x, ∑ i, ∑ j, ‖(S x) i j‖ ^ 2 ≤ ∑ i, ∑ j, ‖x i j‖ ^ 2 := fun x => by
    rw [hS_mix x]
    exact unitary_mix_ss_le _ _ (fun _ => by positivity) hS_wsum x
  have hS_op : ∀ x, ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (S x)‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ := fun x => by
    rw [hS_mix x]
    exact unitary_mix_opNorm_le _ _ (fun _ => by positivity) hS_wsum x
  refine ⟨S, T, fun _ => rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp only [T, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, star_add,
      star_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, Matrix.trace_add,
      Matrix.trace_smul, hS_sa]
    have hhalf : star (1 / 2 : ℂ) = 1 / 2 := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.star_def, Complex.conj_ofReal]
    rw [hhalf]
  · intro x; exact lazy_inner_sub_sq S hS_ss x
  · intro x
    have h1 : Real.sqrt (∑ i, ∑ j, ‖(T x) i j‖ ^ 2) ≤ Real.sqrt (∑ i, ∑ j, ‖x i j‖ ^ 2) := by
      have hTx : T x = (1 / 2 : ℂ) • x + (1 / 2 : ℂ) • S x := by simp [T]
      rw [hTx]
      have hn : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real]; norm_num
      calc Real.sqrt (∑ i, ∑ j, ‖((1 / 2 : ℂ) • x + (1 / 2 : ℂ) • S x) i j‖ ^ 2)
          ≤ Real.sqrt (∑ i, ∑ j, ‖((1 / 2 : ℂ) • x) i j‖ ^ 2) +
              Real.sqrt (∑ i, ∑ j, ‖((1 / 2 : ℂ) • S x) i j‖ ^ 2) := sqrt_ss_add_le _ _
        _ = (1 / 2 : ℝ) * Real.sqrt (∑ i, ∑ j, ‖x i j‖ ^ 2) +
              (1 / 2 : ℝ) * Real.sqrt (∑ i, ∑ j, ‖(S x) i j‖ ^ 2) := by
            rw [sqrt_ss_smul, sqrt_ss_smul, hn]
        _ ≤ (1 / 2 : ℝ) * Real.sqrt (∑ i, ∑ j, ‖x i j‖ ^ 2) +
              (1 / 2 : ℝ) * Real.sqrt (∑ i, ∑ j, ‖x i j‖ ^ 2) := by
            linarith [Real.sqrt_le_sqrt (hS_ss x)]
        _ = Real.sqrt (∑ i, ∑ j, ‖x i j‖ ^ 2) := by ring
    have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at h2
    exact h2
  · intro x
    have hTx : T x = (1 / 2 : ℂ) • x + (1 / 2 : ℂ) • S x := by simp [T]
    rw [hTx, map_add, map_smul, map_smul]
    have hn : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real]; norm_num
    calc ‖(1 / 2 : ℂ) • Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x +
            (1 / 2 : ℂ) • Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (S x)‖
        ≤ ‖(1 / 2 : ℂ) • Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ +
            ‖(1 / 2 : ℂ) • Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (S x)‖ :=
          norm_add_le _ _
      _ = (1 / 2 : ℝ) * ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ +
            (1 / 2 : ℝ) * ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (S x)‖ := by
          rw [norm_smul, norm_smul, hn]
      _ ≤ (1 / 2 : ℝ) * ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ +
            (1 / 2 : ℝ) * ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ := by
          gcongr; exact hS_op x
      _ = ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) x‖ := by ring
  · intro x
    have hsub : x - T x = (1 / 2 : ℂ) • (x - S x) := by
      simp only [T, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
      module
    have h1 : ∑ i, ∑ j, ‖(x - T x) i j‖ ^ 2 =
        (1 / 4 : ℝ) * ((∑ i, ∑ j, ‖x i j‖ ^ 2) - 2 * ((star x * S x).trace).re +
          (∑ i, ∑ j, ‖(S x) i j‖ ^ 2)) := by
      rw [hsub, ss_smul, ss_sub_eq]
      have hn : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real]; norm_num
      rw [hn]; ring
    have h2 : ((star x * (x - T x)).trace).re =
        (1 / 2 : ℝ) * (∑ i, ∑ j, ‖x i j‖ ^ 2) - (1 / 2 : ℝ) * ((star x * S x).trace).re := by
      rw [hsub, mul_smul_comm, mul_sub, Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul,
        show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul, Complex.sub_re,
        re_trace_star_mul_self]
      ring
    linarith [hS_ss x]
  · intro x
    have hc : (star x * (x - T x)).trace =
        (1 / (4 * (Fintype.card α : ℂ))) *
          ∑ a : α, ((∑ i, ∑ j, ‖((U a : Matrix (Fin k) (Fin k) ℂ) * x -
            x * (U a : Matrix (Fin k) (Fin k) ℂ)) i j‖ ^ 2 : ℝ) : ℂ) := by
      simp_rw [ss_comm_unitary_eq (U _).2]
      rw [← Matrix.trace_sum, ← Finset.mul_sum, ← smul_eq_mul (1 / (4 * (Fintype.card α : ℂ))),
        ← Matrix.trace_smul, ← mul_smul_comm]
      congr 2
      have h1 : (1 / (4 * (Fintype.card α : ℂ))) •
          ∑ _a : α, (2 : ℂ) • x = (1 / 2 : ℂ) • x := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
        congr 1; field_simp [hcard_cne]; ring
      have h2 : ∑ a : α, (star (U a : Matrix (Fin k) (Fin k) ℂ) * x * (U a : Matrix (Fin k) (Fin k) ℂ) +
            (U a : Matrix (Fin k) (Fin k) ℂ) * x * star (U a : Matrix (Fin k) (Fin k) ℂ)) =
          ∑ a : α, ((U a : Matrix (Fin k) (Fin k) ℂ) * x * star (U a : Matrix (Fin k) (Fin k) ℂ) +
            star (U a : Matrix (Fin k) (Fin k) ℂ) * x * (U a : Matrix (Fin k) (Fin k) ℂ)) :=
        Finset.sum_congr rfl fun a _ => add_comm _ _
      rw [Finset.sum_sub_distrib, smul_sub, h1, h2]
      simp only [T, S, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
        LinearMap.coe_mk, AddHom.coe_mk, smul_smul]
      have hcoef : (1 / 2 : ℂ) * (1 / (2 * (Fintype.card α : ℂ))) =
          1 / (4 * (Fintype.card α : ℂ)) := by field_simp [hcard_cne]; ring
      rw [hcoef]
      module
    have hre := congrArg Complex.re hc
    rw [show (1 / (4 * (Fintype.card α : ℂ))) = ((1 / (4 * (Fintype.card α : ℝ)) : ℝ) : ℂ) by
        push_cast; rfl,
      Complex.re_ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re] at hre
    exact hre

/- ### Main reduction: Theorem A (H1) + Theorem 5.2 (H2) → Theorem B (H3) -/

theorem main : H1 → H2 → OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1.H3 := by
  classical
  intro hH1 hH2 d hd ι _ u κ hκ
  dsimp only
  intro hgap
  by_cases hι : IsEmpty ι
  · refine ⟨fun n => ⊤, fun y hy => ?_⟩
    constructor
    · intro _
      refine ⟨y, hy, fun _ => trivial, ?_⟩
      simp
    · intro _
      exact ⟨hy, fun a => (hι.false a).elim⟩
  have : Nonempty ι := not_isEmpty_iff.mp hι
  have hcard_cne : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  -- Step 1: Apply Theorem A (H1) to obtain projection partitions and doubled unitaries.
  obtain ⟨m, e, v, c, hc_pos, he_proj, he_orth, he_sum, hv_comm, hv_close, hscalar_gap⟩ :=
    hH1 d hd ι u κ hκ hgap
  let q : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ → ℝ :=
    fun n y => (∑ a, ∑ b, ‖y a b‖ ^ 2) / (d n : ℝ)
  let B : ((n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ) → Prop :=
    fun y => ∃ C : ℝ, ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (y n)‖ ≤ C
  let K : ((n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ) → Prop :=
    fun y => B y ∧ ∀ a,
      Tendsto (fun n => q n ((u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n -
        y n * (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ))) (hyperfilter ℕ) (𝓝 0)
  -- Construct lazy Markov operators Tn (from u) and Qn (from v).
  choose Sn Tn hSn_def hTn_def hTn_sa hTn_lazy hTn_ss hTn_op hTn_sub_le hTn_energy_ss using
    fun n => lazy_markov_props (fun a : ι => u a n)
  choose Rn Qn hRn_def hQn_def hQn_sa hQn_lazy hQn_ss _ _ hQn_energy_ss using
    fun n => lazy_markov_props (fun p : Bool × ι => v p.1 p.2 n)
  have hTn_pos : ∀ n x, 0 ≤ ((star x * Tn n x).trace).re :=
    fun n x => le_trans (by positivity) (hTn_lazy n x)
  have hQn_pos : ∀ n x, 0 ≤ ((star x * Qn n x).trace).re :=
    fun n x => le_trans (by positivity) (hQn_lazy n x)
  have hTn_energy : ∀ n x, ((star x * (x - Tn n x)).trace).re / (d n : ℝ) =
      (1 / (4 * (Fintype.card ι : ℝ))) *
        ∑ a : ι, q n ((u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x -
          x * (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) := fun n x => by
    rw [hTn_energy_ss n x, mul_div_assoc, Finset.sum_div]
  have hQn_energy : ∀ n x, ((star x * (x - Qn n x)).trace).re / (d n : ℝ) =
      (1 / (8 * (Fintype.card ι : ℝ))) *
        ∑ b : Bool, ∑ a : ι, q n ((v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x -
          x * (v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) := fun n x => by
    rw [hQn_energy_ss n x, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat,
      show 4 * (2 * (Fintype.card ι : ℝ)) = 8 * (Fintype.card ι : ℝ) by ring,
      mul_div_assoc, Finset.sum_div, Fintype.sum_prod_type]
  -- Step 2: Elements of K are asymptotically fixed by every fixed power of Tn.
  have hK_fix_one : ∀ z, K z →
      Tendsto (fun n => q n (z n - Tn n (z n))) (hyperfilter ℕ) (𝓝 0) := by
    intro z hz
    have hle : ∀ n, q n (z n - Tn n (z n)) ≤
        (1 / (4 * (Fintype.card ι : ℝ))) *
          ∑ a : ι, q n ((u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * z n -
            z n * (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) := fun n => by
      rw [← hTn_energy n (z n)]
      exact div_le_div_of_nonneg_right (hTn_sub_le n (z n)) (Nat.cast_nonneg _)
    refine squeeze_zero (fun n => by positivity) hle ?_
    simpa using (tendsto_finsetSum Finset.univ fun a _ => hz.2 a).const_mul
      (1 / (4 * (Fintype.card ι : ℝ)))
  have hK_fix_pow : ∀ z, K z → ∀ r : ℕ,
      Tendsto (fun n => q n (z n - (Tn n ^ r) (z n))) (hyperfilter ℕ) (𝓝 0) := by
    intro z hz r
    induction r with
    | zero => simp [q]
    | succ r ih =>
      have hsplit : ∀ n, z n - (Tn n ^ (r + 1)) (z n) =
          (z n - Tn n (z n)) + Tn n (z n - (Tn n ^ r) (z n)) := fun n => by
        rw [map_sub, pow_succ', Module.End.mul_apply]; abel
      simp_rw [hsplit]
      refine tendsto_q_add (hK_fix_one z hz) ?_
      refine squeeze_zero (fun n => by positivity) (fun n => ?_) ih
      exact div_le_div_of_nonneg_right (hTn_ss n _) (Nat.cast_nonneg _)
  -- Step 3 & 4: Exponential Cauchy decay and uniform transfer (Proposition 2.2).
  let κ0 : ℝ := min (κ / (4 * (Fintype.card ι : ℝ))) (1 / 2)
  have hκ0_pos : 0 < κ0 := lt_min (div_pos hκ (by positivity)) (by norm_num)
  have hκ0_le : κ0 ≤ 1 / 2 := min_le_right _ _
  have hκ0_gap : κ0 ≤ κ / (4 * (Fintype.card ι : ℝ)) := min_le_left _ _
  have hT_cauchy : ∀ (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ),
      (∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (y n)‖ ≤ 1) →
      ∀ j k : ℕ, j ≤ k → ∀ ε > 0, ∀ᶠ n in hyperfilter ℕ,
        q n ((Tn n ^ k) (y n) - (Tn n ^ j) (y n)) ≤ (1 - κ0) ^ j + ε := by
    intro y hy j k hjk ε hε
    refine lazy_cauchy_of_gap hd Tn hTn_sa hTn_lazy hTn_ss hTn_op hκ0_pos hκ0_le ?_ y hy j k hjk hε
    intro z hzB
    obtain ⟨ez, hezK, hezgap⟩ := hgap z hzB
    refine ⟨ez, hezK.1, hK_fix_pow ez hezK, fun δ hδ => ?_⟩
    have h4 : (0 : ℝ) < 4 * (Fintype.card ι : ℝ) := by positivity
    filter_upwards [hezgap (4 * (Fintype.card ι : ℝ) * δ) (mul_pos h4 hδ)] with n hn
    have hdiv : (κ / (4 * (Fintype.card ι : ℝ))) * q n (z n - ez n) ≤
        δ + ((star (z n) * (z n - Tn n (z n))).trace).re / (d n : ℝ) := by
      rw [hTn_energy n (z n)]
      have h1 := div_le_div_of_nonneg_right hn h4.le
      rw [mul_div_right_comm, add_div, mul_div_cancel_left₀ _ h4.ne'] at h1
      rwa [one_div, inv_mul_eq_div]
    have hκw : κ0 * q n (z n - ez n) ≤ (κ / (4 * (Fintype.card ι : ℝ))) * q n (z n - ez n) :=
      mul_le_mul_of_nonneg_right hκ0_gap (by positivity)
    linarith
  have hT_unif : ∀ (j k : ℕ), j ≤ k → ∀ ε > 0, ∀ᶠ n in hyperfilter ℕ,
      ∀ x : Matrix (Fin (d n)) (Fin (d n)) ℂ,
        ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) x‖ ≤ 1 →
        q n ((Tn n ^ k) x - (Tn n ^ j) x) ≤ (1 - κ0) ^ j + ε :=
    fun j k hjk _ hε => lazy_uniform_transfer Tn hT_cauchy j k hjk hε
  -- Step 5: Diagonalization to construct ℓ_n →_ω ∞.
  let W : ℕ → Set ℕ := fun M =>
    {n : ℕ | M ≤ n ∧ ∀ j k, 1 ≤ j → j ≤ k → k ≤ M →
      ∀ x : Matrix (Fin (d n)) (Fin (d n)) ℂ,
        ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) x‖ ≤ 1 →
        q n ((Tn n ^ k) x - (Tn n ^ j) x) ≤ (1 - κ0) ^ j + 1 / (M : ℝ)}
  have hW_mem : ∀ M, 1 ≤ M → ∀ᶠ n in hyperfilter ℕ, n ∈ W M := by
    intro M hM
    have h1 : ∀ᶠ n in hyperfilter ℕ, M ≤ n :=
      (Filter.eventually_ge_atTop M).filter_mono hyperfilter_le_atTop
    have h2 : ∀ᶠ n in hyperfilter ℕ,
        ∀ p ∈ (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter (fun p => p.1 ≤ p.2),
          ∀ x : Matrix (Fin (d n)) (Fin (d n)) ℂ,
            ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) x‖ ≤ 1 →
            q n ((Tn n ^ p.2) x - (Tn n ^ p.1) x) ≤ (1 - κ0) ^ p.1 + 1 / (M : ℝ) := by
      rw [Filter.eventually_all_finset]
      intro p hp
      exact hT_unif p.1 p.2 (Finset.mem_filter.1 hp).2 (1 / (M : ℝ)) (by positivity)
    filter_upwards [h1, h2] with n hn1 hn2
    refine ⟨hn1, fun j k hj hjk hk => hn2 (j, k) ?_⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_product.2
      ⟨Finset.mem_Icc.2 ⟨hj, hjk.trans hk⟩, Finset.mem_Icc.2 ⟨hj.trans hjk, hk⟩⟩, hjk⟩
  let S_idx : ℕ → Finset ℕ := fun n => (Finset.Icc 1 n).filter (fun M => n ∈ W M)
  let ℓ : ℕ → ℕ := fun n => if h : (S_idx n).Nonempty then (S_idx n).max' h else 0
  have hℓ_atTop : Tendsto ℓ (hyperfilter ℕ) atTop := by
    rw [Filter.tendsto_atTop]
    intro M
    let M' := max M 1
    filter_upwards [hW_mem M' (le_max_right M 1)] with n hn
    have hmem : M' ∈ S_idx n := Finset.mem_filter.2
      ⟨Finset.mem_Icc.2 ⟨le_max_right M 1, hn.1⟩, hn⟩
    have hne : (S_idx n).Nonempty := ⟨M', hmem⟩
    have hge : M' ≤ ℓ n := by
      simp only [ℓ, dif_pos hne]
      exact Finset.le_max' _ _ hmem
    exact (le_max_left M 1).trans hge
  have hℓ_prop : ∀ n, 1 ≤ ℓ n → n ∈ W (ℓ n) := by
    intro n hℓ1
    dsimp only [ℓ] at hℓ1 ⊢
    split_ifs at hℓ1 ⊢ with h
    · exact (Finset.mem_filter.1 (Finset.max'_mem (S_idx n) h)).2
    · omega
  -- Step 6: Choose N_n →_ω ∞ with 2 * N_n ≤ ℓ_n and N_n * Δ_n →_ω 0 (Corollary 5.1).
  let Δ : ℕ → ℝ := fun n =>
    ∑ b : Bool, ∑ a : ι, Real.sqrt (q n ((v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) -
      (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)))
  have hΔ_nonneg : ∀ n, 0 ≤ Δ n := fun n =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hΔ_zero : Tendsto Δ (hyperfilter ℕ) (𝓝 0) := by
    have : Tendsto Δ (hyperfilter ℕ) (𝓝 (∑ _b : Bool, ∑ _a : ι, (0 : ℝ))) :=
      tendsto_finsetSum Finset.univ fun b _ =>
        tendsto_finsetSum Finset.univ fun a _ => by
          have hs := (hv_close b a).sqrt
          rw [Real.sqrt_zero] at hs
          exact hs
    simpa using this
  let N : ℕ → ℕ := fun n =>
    min (ℓ n / 2) (if Δ n = 0 then ℓ n / 2 else Nat.floor (1 / Real.sqrt (Δ n)))
  have h2N_le : ∀ n, 2 * N n ≤ ℓ n := fun n => by
    have : N n ≤ ℓ n / 2 := min_le_left _ _
    omega
  have hN_atTop : Tendsto N (hyperfilter ℕ) atTop := by
    rw [Filter.tendsto_atTop]
    intro K
    have h1 : ∀ᶠ n in hyperfilter ℕ, 2 * K ≤ ℓ n :=
      hℓ_atTop.eventually (Filter.eventually_ge_atTop (2 * K))
    have h2 : ∀ᶠ n in hyperfilter ℕ, Δ n < 1 / (((K + 1 : ℕ) : ℝ) ^ 2) :=
      hΔ_zero.eventually (gt_mem_nhds (by positivity))
    filter_upwards [h1, h2] with n hn1 hn2
    refine le_min (by omega) ?_
    split_ifs with h0
    · omega
    · have hpos : 0 < Δ n := lt_of_le_of_ne (hΔ_nonneg n) (Ne.symm h0)
      have hsq : Real.sqrt (Δ n) < 1 / ((K + 1 : ℕ) : ℝ) := by
        have hlt : Real.sqrt (Δ n) < Real.sqrt (1 / (((K + 1 : ℕ) : ℝ) ^ 2)) :=
          Real.sqrt_lt_sqrt (hΔ_nonneg n) hn2
        rwa [Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_sq (by positivity)] at hlt
      have hinv : ((K + 1 : ℕ) : ℝ) < 1 / Real.sqrt (Δ n) := by
        rw [lt_div_iff₀ (Real.sqrt_pos.2 hpos)]
        have := (lt_div_iff₀ (by positivity : (0 : ℝ) < ((K + 1 : ℕ) : ℝ))).1 hsq
        linarith
      exact Nat.le_floor (by push_cast at hinv; linarith)
  have hNΔ_zero : Tendsto (fun n => (N n : ℝ) * Δ n) (hyperfilter ℕ) (𝓝 0) := by
    refine squeeze_zero (fun n => mul_nonneg (Nat.cast_nonneg _) (hΔ_nonneg n)) (fun n => ?_)
      (by simpa using hΔ_zero.sqrt)
    by_cases h0 : Δ n = 0
    · simp [h0]
    · have hpos : 0 < Δ n := lt_of_le_of_ne (hΔ_nonneg n) (Ne.symm h0)
      have hNle : (N n : ℝ) ≤ 1 / Real.sqrt (Δ n) := by
        have h1 : N n ≤ Nat.floor (1 / Real.sqrt (Δ n)) := by
          simp [N, h0]
        exact (Nat.cast_le.2 h1).trans (Nat.floor_le (by positivity))
      calc (N n : ℝ) * Δ n ≤ (1 / Real.sqrt (Δ n)) * Δ n :=
            mul_le_mul_of_nonneg_right hNle (hΔ_nonneg n)
        _ = Real.sqrt (Δ n) := by
            rw [one_div, inv_mul_eq_div, div_eq_iff (Real.sqrt_pos.2 hpos).ne',
              Real.mul_self_sqrt (hΔ_nonneg n)]
  -- Step 7: Single-step and N-step comparison between Qn and Tn.
  have hQT_step : ∀ n x, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) x‖ ≤ 1 →
      Real.sqrt (∑ i, ∑ j, ‖(Qn n x - Tn n x) i j‖ ^ 2) ≤ Real.sqrt (d n : ℝ) * Δ n := by
    intro n x hx
    have hdn : (0 : ℝ) < (d n : ℝ) := Nat.cast_pos.2 (hd n)
    have hdiff : Qn n x - Tn n x =
        (1 / (8 * (Fintype.card ι : ℂ))) •
          ∑ b : Bool, ∑ a : ι,
            (((v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
                star (v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) -
              (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
                star (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) +
            (star (v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
                (v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) -
              star (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
                (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ))) := by
      rw [hQn_def n, hTn_def n]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, hRn_def n,
        hSn_def n, Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul,
        Nat.cast_ofNat]
      have hT2 : (1 / 2 : ℂ) • (1 / (2 * (Fintype.card ι : ℂ))) •
          ∑ a : ι, ((u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
              star (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) +
            star (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
              (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) =
          (1 / (8 * (Fintype.card ι : ℂ))) •
            ∑ _b : Bool, ∑ a : ι, ((u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
                star (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) +
              star (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
                (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) := by
        rw [Fintype.sum_bool, ← two_smul ℂ, smul_smul, smul_smul]
        congr 1; field_simp [hcard_cne]; ring
      have hQ2 : (1 / 2 : ℂ) • (1 / (2 * (2 * (Fintype.card ι : ℂ)))) •
          ∑ b : Bool, ∑ a : ι, ((v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
              star (v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) +
            star (v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
              (v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) =
          (1 / (8 * (Fintype.card ι : ℂ))) •
            ∑ b : Bool, ∑ a : ι, ((v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
                star (v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) +
              star (v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
                (v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) := by
        rw [smul_smul]; congr 1; field_simp [hcard_cne]; ring
      rw [add_sub_add_left_eq_sub, hQ2, hT2, ← smul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => by abel
    rw [hdiff, sqrt_ss_smul]
    have hnormc : ‖(1 / (8 * (Fintype.card ι : ℂ)))‖ = 1 / (8 * (Fintype.card ι : ℝ)) := by
      rw [show (1 / (8 * (Fintype.card ι : ℂ))) = ((1 / (8 * (Fintype.card ι : ℝ)) : ℝ) : ℂ) by
          push_cast; rfl, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hnormc]
    have hsum_le : Real.sqrt (∑ i, ∑ j, ‖(∑ b : Bool, ∑ a : ι,
        (((v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
            star (v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) -
          (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
            star (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) +
        (star (v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
            (v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) -
          star (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
            (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)))) i j‖ ^ 2) ≤
        4 * Real.sqrt (d n : ℝ) * Δ n := by
      calc _ ≤ ∑ b : Bool, Real.sqrt (∑ i, ∑ j, ‖(∑ a : ι,
            (((v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
                star (v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) -
              (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
                star (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) +
            (star (v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
                (v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) -
              star (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
                (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)))) i j‖ ^ 2) :=
          sqrt_ss_sum_le _ _
        _ ≤ ∑ b : Bool, ∑ a : ι, Real.sqrt (∑ i, ∑ j, ‖(((v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
              star (v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) -
              (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
                star (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) +
              (star (v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
                (v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) -
              star (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
                (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ))) i j‖ ^ 2) :=
          Finset.sum_le_sum fun b _ => sqrt_ss_sum_le _ _
        _ ≤ ∑ b : Bool, ∑ a : ι, 4 * (Real.sqrt (d n : ℝ) *
              Real.sqrt (q n ((v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) -
                (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)))) := by
          refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun a _ => ?_
          have h1 := conj_diff_sqrt_ss_le (u a n).2 (v b a n).2 hx
          have h2 := conj_diff_sqrt_ss_le (Unitary.star_mem (u a n).2)
            (Unitary.star_mem (v b a n).2) hx
          rw [star_star, star_star, ← star_sub, ss_star] at h2
          have hsq : Real.sqrt (d n : ℝ) *
              Real.sqrt (q n ((v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) -
                (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ))) =
              Real.sqrt (∑ i, ∑ j, ‖((v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) -
                (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) i j‖ ^ 2) := by
            simp only [q]
            rw [Real.sqrt_div (by positivity), mul_div_cancel₀ _ (Real.sqrt_pos.2 hdn).ne']
          rw [hsq]
          linarith [sqrt_ss_add_le
            ((v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
                star (v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) -
              (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
                star (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ))
            (star (v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
                (v b a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) -
              star (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
                (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ))]
        _ = 4 * Real.sqrt (d n : ℝ) * Δ n := by
          simp only [Δ, Finset.mul_sum]; ring_nf
    have hle1 : (1 / (8 * (Fintype.card ι : ℝ))) * (4 * Real.sqrt (d n : ℝ) * Δ n) ≤
        Real.sqrt (d n : ℝ) * Δ n := by
      have hcard_ge : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
      have hcoeff : (1 / (8 * (Fintype.card ι : ℝ))) * 4 ≤ 1 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
      calc (1 / (8 * (Fintype.card ι : ℝ))) * (4 * Real.sqrt (d n : ℝ) * Δ n)
          = ((1 / (8 * (Fintype.card ι : ℝ))) * 4) * (Real.sqrt (d n : ℝ) * Δ n) := by ring
        _ ≤ 1 * (Real.sqrt (d n : ℝ) * Δ n) :=
            mul_le_mul_of_nonneg_right hcoeff (mul_nonneg (Real.sqrt_nonneg _) (hΔ_nonneg n))
        _ = Real.sqrt (d n : ℝ) * Δ n := one_mul _
    exact (mul_le_mul_of_nonneg_left hsum_le (by positivity)).trans hle1
  have hQT_pow : ∀ n (r : ℕ) x, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) x‖ ≤ 1 →
      q n ((Qn n ^ r) x - (Tn n ^ r) x) ≤ ((r : ℝ) * Δ n) ^ 2 := by
    intro n r x hx
    have hdn : (0 : ℝ) < (d n : ℝ) := Nat.cast_pos.2 (hd n)
    have h1 := pow_diff_sqrt_ss_le (Qn n) (Tn n) (hQn_ss n) (hTn_op n) (hQT_step n) r x hx
    have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rw [Real.sq_sqrt (by positivity), mul_pow, mul_pow, Real.sq_sqrt hdn.le] at h2
    simp only [q]
    rw [div_le_iff₀ hdn]
    linarith
  -- Step 8: Represent F_n := Q_n ^ (N n) as a self-adjoint unitary mixture commuting with e_n.
  have hQn_rep0 : ∀ n, ∃ (L0 : ℕ) (w0 : Fin L0 → ℝ) (V0 : Fin L0 → Matrix.unitaryGroup (Fin (d n)) ℂ),
      (∀ s, 0 ≤ w0 s) ∧ (∑ s, w0 s = 1) ∧
      (∀ s i, (V0 s : Matrix (Fin (d n)) (Fin (d n)) ℂ) * e n i =
        e n i * (V0 s : Matrix (Fin (d n)) (Fin (d n)) ℂ)) ∧
      ∀ x, Qn n x = ∑ s, (w0 s : ℂ) • (star (V0 s : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
        (V0 s : Matrix (Fin (d n)) (Fin (d n)) ℂ)) := by
    intro n
    obtain ⟨L0, w0, V0, hw0, hs0, hV0_mem, hV0_eq⟩ :=
      unitary_tuple_mix (fun p : Bool × ι => v p.1 p.2 n)
    refine ⟨L0, w0, V0, hw0, hs0, ?_, ?_⟩
    · intro s i
      rcases hV0_mem s with h1 | ⟨⟨b, a⟩, h2 | h3⟩
      · rw [h1, one_mul, mul_one]
      · rw [h2]; exact hv_comm b a n i
      · rw [h3]; exact comm_star_of_comm_unitary (v b a n).2 (hv_comm b a n i)
    · intro x
      have hQeq : Qn n x = (1 / 2 : ℂ) • x + (1 / (4 * (Fintype.card (Bool × ι) : ℂ))) •
          ∑ p : Bool × ι, ((v p.1 p.2 n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
              star (v p.1 p.2 n : Matrix (Fin (d n)) (Fin (d n)) ℂ) +
            star (v p.1 p.2 n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
              (v p.1 p.2 n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) := by
        rw [hQn_def n]
        simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, hRn_def n,
          smul_smul, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
        congr 2; field_simp [hcard_cne]; ring
      rw [hQeq, hV0_eq]
  choose L0 w0 V0 hw0 hs0 hc0 hQ0_rep using hQn_rep0
  choose L w V hw_nn hw_sum hV_comm hFn_rep using
    fun n => mix_pow_rep (w0 n) (V0 n) (hw0 n) (hs0 n) (Qn n) (hQ0_rep n) (N n)
  let F : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ → Matrix (Fin (d n)) (Fin (d n)) ℂ :=
    fun n x => ∑ s : Fin (L n), (w n s : ℂ) • (star (V n s : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
      (V n s : Matrix (Fin (d n)) (Fin (d n)) ℂ))
  have hF_eq : ∀ n x, F n x = (Qn n ^ (N n)) x := fun n x => (hFn_rep n x).symm
  have hF_symm : ∀ n x, F n x =
      ∑ s : Fin (L n), (w n s : ℂ) • ((V n s : Matrix (Fin (d n)) (Fin (d n)) ℂ) * x *
        star (V n s : Matrix (Fin (d n)) (Fin (d n)) ℂ)) := by
    intro n x
    refine mix_symm_of_sa (w n) (V n) (fun a b => ?_) x
    simp_rw [← hFn_rep n]
    exact pow_sa (Qn n) (hQn_sa n) (N n) a b
  have hF_pos : ∀ n x, 0 ≤ ((star x * F n x).trace).re := fun n x => by
    rw [hF_eq n x]
    exact pow_pos_re (Qn n) (hQn_sa n) (hQn_pos n) (N n) x
  let δ : ℕ → ℝ := fun n =>
    4 * (2 * (N n : ℝ) * Δ n) ^ 2 + 4 * ((1 - κ0) ^ (N n) + 1 / (ℓ n : ℝ)) +
      2 * ((N n : ℝ) * Δ n) ^ 2
  have hδ_zero : Tendsto δ (hyperfilter ℕ) (𝓝 0) := by
    have h1 : Tendsto (fun n => 4 * (2 * (N n : ℝ) * Δ n) ^ 2) (hyperfilter ℕ) (𝓝 0) := by
      have : Tendsto (fun n => (2 : ℝ) * ((N n : ℝ) * Δ n)) (hyperfilter ℕ) (𝓝 0) := by
        simpa using hNΔ_zero.const_mul 2
      simpa [mul_assoc] using (this.pow 2).const_mul 4
    have h2 : Tendsto (fun n => (1 - κ0) ^ (N n)) (hyperfilter ℕ) (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)).comp hN_atTop
    have h3 : Tendsto (fun n => 1 / (ℓ n : ℝ)) (hyperfilter ℕ) (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp hℓ_atTop
    have h4 : Tendsto (fun n => 2 * ((N n : ℝ) * Δ n) ^ 2) (hyperfilter ℕ) (𝓝 0) := by
      simpa using (hNΔ_zero.pow 2).const_mul 2
    simpa [δ] using (h1.add ((h2.add h3).const_mul 4)).add h4
  have hδ_bound : ∀ n x, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) x‖ ≤ 1 →
      q n (F n (F n x) - F n x) ≤ δ n := by
    intro n x hx
    rw [hF_eq, hF_eq, ← Module.End.mul_apply, ← pow_add, ← two_mul]
    by_cases hN0 : N n = 0
    · simp only [hN0, mul_zero, pow_zero, Module.End.one_apply, sub_self, q, Matrix.zero_apply,
        norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
        zero_div]
      have : 0 ≤ (1 - κ0) ^ (N n) := pow_nonneg (by linarith) _
      have : 0 ≤ 1 / (ℓ n : ℝ) := by positivity
      dsimp only [δ]; positivity
    · have hN1 : 1 ≤ N n := Nat.pos_of_ne_zero hN0
      have hℓ1 : 1 ≤ ℓ n := by have := h2N_le n; omega
      have hsplit : (Qn n ^ (2 * N n)) x - (Qn n ^ (N n)) x =
          (((Qn n ^ (2 * N n)) x - (Tn n ^ (2 * N n)) x) +
            ((Tn n ^ (2 * N n)) x - (Tn n ^ (N n)) x)) +
          ((Tn n ^ (N n)) x - (Qn n ^ (N n)) x) := by abel
      rw [hsplit]
      have hq1 := q_add_le
        (((Qn n ^ (2 * N n)) x - (Tn n ^ (2 * N n)) x) + ((Tn n ^ (2 * N n)) x - (Tn n ^ (N n)) x))
        ((Tn n ^ (N n)) x - (Qn n ^ (N n)) x)
      have hq2 := q_add_le
        ((Qn n ^ (2 * N n)) x - (Tn n ^ (2 * N n)) x)
        ((Tn n ^ (2 * N n)) x - (Tn n ^ (N n)) x)
      have hb1 : q n ((Qn n ^ (2 * N n)) x - (Tn n ^ (2 * N n)) x) ≤ (2 * (N n : ℝ) * Δ n) ^ 2 := by
        simpa [Nat.cast_mul, mul_assoc] using hQT_pow n (2 * N n) x hx
      have hb2 : q n ((Tn n ^ (2 * N n)) x - (Tn n ^ (N n)) x) ≤ (1 - κ0) ^ (N n) + 1 / (ℓ n : ℝ) :=
        (hℓ_prop n hℓ1).2 (N n) (2 * N n) hN1 (by omega) (h2N_le n) x hx
      have hb3 : q n ((Tn n ^ (N n)) x - (Qn n ^ (N n)) x) ≤ ((N n : ℝ) * Δ n) ^ 2 := by
        have hcomm : q n ((Tn n ^ (N n)) x - (Qn n ^ (N n)) x) =
            q n ((Qn n ^ (N n)) x - (Tn n ^ (N n)) x) := by
          dsimp only [q]; rw [ss_sub_comm]
        rw [hcomm]
        exact hQT_pow n (N n) x hx
      dsimp only [δ]
      linarith
  let c' : ℝ := min c (1 / 2)
  have hc'_pos : 0 < c' := lt_min hc_pos (by norm_num)
  have hc'_le : c' ≤ 1 := (min_le_right c (1 / 2)).trans (by norm_num)
  let σ : ℕ → ℝ := fun n => (1 - c') ^ (N n)
  have hσ_zero : Tendsto σ (hyperfilter ℕ) (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)).comp hN_atTop
  have hσ_bound : ∀ n i x, e n i * x * e n i = x →
      q n (F n x - (x.trace / (e n i).trace) • e n i) ≤ σ n * q n x := by
    intro n i x hx
    rw [hF_eq n x]
    have hdn : (0 : ℝ) < (d n : ℝ) := Nat.cast_pos.2 (hd n)
    have hQtr : ∀ y, (Qn n y).trace = y.trace := fun y => by
      rw [hQ0_rep n y]; exact unitary_mix_trace (w0 n) (V0 n) (hs0 n) y
    have hQfix : Qn n (e n i) = e n i := by
      rw [hQ0_rep n (e n i)]; exact unitary_mix_fix (w0 n) (V0 n) (hs0 n) (fun s => hc0 n s i)
    have hQcor : ∀ y, e n i * y * e n i = y → e n i * Qn n y * e n i = Qn n y := fun y hy => by
      rw [hQ0_rep n y, ← unitary_mix_comm (w0 n) (V0 n) (fun s => hc0 n s i) y, hy]
    have hgap_ss : ∀ y, e n i * y * e n i = y →
        c' * (∑ a, ∑ b, ‖(y - (y.trace / (e n i).trace) • e n i) a b‖ ^ 2) ≤
          ((star y * (y - Qn n y)).trace).re := fun y hy => by
      have hg := hscalar_gap n i y hy
      rw [← hQn_energy n y] at hg
      have hg' : c' * q n (y - (y.trace / (e n i).trace) • e n i) ≤
          ((star y * (y - Qn n y)).trace).re / (d n : ℝ) :=
        (mul_le_mul_of_nonneg_right (min_le_left c (1 / 2)) (by positivity)).trans hg
      simp only [q] at hg'
      rw [mul_div_assoc', div_le_div_iff_of_pos_right hdn] at hg'
      exact hg'
    have hdec := corner_scalar_decay (he_proj n i).1 (he_proj n i).2.1 (he_proj n i).2.2
      (Qn n) hQtr hQfix hQcor (hQn_lazy n) hc'_le hgap_ss (N n) x hx
    simp only [q, σ]
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right hdec hdn.le
  -- Step 9: Apply Theorem 5.2 (H2) and verify `K y ↔ q n (y n - F n (y n)) →_ω 0`.
  obtain ⟨A, hA⟩ := hH2 d hd m e he_proj he_orth he_sum L w V hw_nn hw_sum
    (fun n s i => hV_comm n (e n i) (fun s0 => hc0 n s0 i) s) hF_symm hF_pos
    ⟨δ, hδ_zero, hδ_bound⟩ ⟨σ, hσ_zero, hσ_bound⟩
  refine ⟨A, fun y hy => Iff.trans ?_ (hA y hy)⟩
  obtain ⟨Cy, hCy⟩ := hy
  let C : ℝ := max Cy 1
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right Cy 1)
  have hCy_le : ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (y n)‖ ≤ C :=
    fun n => (hCy n).trans (le_max_left Cy 1)
  have hFT_y : Tendsto (fun n => q n (F n (y n) - (Tn n ^ (N n)) (y n))) (hyperfilter ℕ) (𝓝 0) := by
    refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      (by simpa using (hNΔ_zero.pow 2).const_mul (C ^ 2))
    rw [hF_eq n (y n)]
    let y1 : Matrix (Fin (d n)) (Fin (d n)) ℂ := ((1 / C : ℝ) : ℂ) • y n
    have hy1 : ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) y1‖ ≤ 1 := by
      simp only [y1, map_smul, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / C)]
      rw [one_div, inv_mul_le_iff₀ hC_pos, mul_one]
      exact hCy_le n
    have h1 := hQT_pow n (N n) y1 hy1
    have hscale : (Qn n ^ (N n)) (y n) - (Tn n ^ (N n)) (y n) =
        (C : ℂ) • ((Qn n ^ (N n)) y1 - (Tn n ^ (N n)) y1) := by
      simp only [y1, map_smul, ← smul_sub, smul_smul]
      rw [show (C : ℂ) * ((1 / C : ℝ) : ℂ) = 1 by
        rw [← Complex.ofReal_mul, one_div, mul_inv_cancel₀ hC_pos.ne', Complex.ofReal_one], one_smul]
    rw [hscale]
    simp only [q, ss_smul, Complex.norm_real, Real.norm_of_nonneg hC_pos.le]
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg C)
  constructor
  · intro hKy
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hq_sub : ∃ j : ℕ, 1 ≤ j ∧ 8 * C ^ 2 * (1 - κ0) ^ j < ε / 4 := by
      have hpow0 : Tendsto (fun j : ℕ => 8 * C ^ 2 * (1 - κ0) ^ j) atTop (𝓝 0) := by
        have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 - κ0) (by linarith) (by linarith)).const_mul (8 * C ^ 2)
        rw [mul_zero] at h
        exact h
      obtain ⟨j, hj⟩ := (hpow0.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 4))).exists_forall_of_atTop
      exact ⟨max j 1, le_max_right j 1, hj (max j 1) (le_max_left j 1)⟩
    obtain ⟨j, hj1, hj_lt⟩ := hq_sub
    have h1 : ∀ᶠ n in hyperfilter ℕ, q n (y n - (Tn n ^ j) (y n)) < ε / 8 :=
      (hK_fix_pow y hKy j).eventually (gt_mem_nhds (by linarith))
    have h2 : ∀ᶠ n in hyperfilter ℕ, q n (F n (y n) - (Tn n ^ (N n)) (y n)) < ε / 8 :=
      hFT_y.eventually (gt_mem_nhds (by linarith))
    have h3 : ∀ᶠ n in hyperfilter ℕ, j ≤ N n := hN_atTop.eventually (Filter.eventually_ge_atTop j)
    have h4 : ∀ᶠ n in hyperfilter ℕ, 8 * C ^ 2 * (1 / (ℓ n : ℝ)) < ε / 4 := by
      have hlim : Tendsto (fun n => 8 * C ^ 2 * (1 / (ℓ n : ℝ))) (hyperfilter ℕ) (𝓝 0) := by
        have h := (tendsto_one_div_atTop_nhds_zero_nat.comp hℓ_atTop).const_mul (8 * C ^ 2)
        rw [mul_zero] at h
        exact h
      exact hlim.eventually (gt_mem_nhds (by linarith))
    filter_upwards [h1, h2, h3, h4] with n hn1 hn2 hn3 hn4
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
    have hℓ1 : 1 ≤ ℓ n := by have := h2N_le n; omega
    have hTN_Tj : q n ((Tn n ^ (N n)) (y n) - (Tn n ^ j) (y n)) ≤
        C ^ 2 * ((1 - κ0) ^ j + 1 / (ℓ n : ℝ)) := by
      let y1 : Matrix (Fin (d n)) (Fin (d n)) ℂ := ((1 / C : ℝ) : ℂ) • y n
      have hy1 : ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) y1‖ ≤ 1 := by
        simp only [y1, map_smul, norm_smul, Complex.norm_real,
          Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / C)]
        rw [one_div, inv_mul_le_iff₀ hC_pos, mul_one]
        exact hCy_le n
      have hb := (hℓ_prop n hℓ1).2 j (N n) hj1 hn3 (by have := h2N_le n; omega) y1 hy1
      have hscale : (Tn n ^ (N n)) (y n) - (Tn n ^ j) (y n) =
          (C : ℂ) • ((Tn n ^ (N n)) y1 - (Tn n ^ j) y1) := by
        simp only [y1, map_smul, ← smul_sub, smul_smul]
        rw [show (C : ℂ) * ((1 / C : ℝ) : ℂ) = 1 by
          rw [← Complex.ofReal_mul, one_div, mul_inv_cancel₀ hC_pos.ne', Complex.ofReal_one], one_smul]
      rw [hscale]
      simp only [q, ss_smul, Complex.norm_real, Real.norm_of_nonneg hC_pos.le]
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hb (sq_nonneg C)
    have hsplit : y n - F n (y n) =
        ((y n - (Tn n ^ j) (y n)) + ((Tn n ^ j) (y n) - (Tn n ^ (N n)) (y n))) +
        ((Tn n ^ (N n)) (y n) - F n (y n)) := by abel
    rw [hsplit]
    have ha1 : q n (((y n - (Tn n ^ j) (y n)) + ((Tn n ^ j) (y n) - (Tn n ^ (N n)) (y n))) +
        ((Tn n ^ (N n)) (y n) - F n (y n))) ≤
        2 * q n ((y n - (Tn n ^ j) (y n)) + ((Tn n ^ j) (y n) - (Tn n ^ (N n)) (y n))) +
        2 * q n ((Tn n ^ (N n)) (y n) - F n (y n)) :=
      q_add_le _ _
    have ha2 : q n ((y n - (Tn n ^ j) (y n)) + ((Tn n ^ j) (y n) - (Tn n ^ (N n)) (y n))) ≤
        2 * q n (y n - (Tn n ^ j) (y n)) + 2 * q n ((Tn n ^ j) (y n) - (Tn n ^ (N n)) (y n)) :=
      q_add_le _ _
    have hsym1 : q n ((Tn n ^ j) (y n) - (Tn n ^ (N n)) (y n)) =
        q n ((Tn n ^ (N n)) (y n) - (Tn n ^ j) (y n)) := by
      dsimp only [q]; rw [ss_sub_comm]
    have hsym2 : q n ((Tn n ^ (N n)) (y n) - F n (y n)) =
        q n (F n (y n) - (Tn n ^ (N n)) (y n)) := by
      dsimp only [q]; rw [ss_sub_comm]
    rw [hsym1] at ha2
    rw [hsym2] at ha1
    linarith
  · intro hyF
    refine ⟨⟨Cy, hCy⟩, fun a => ?_⟩
    have hyT : Tendsto (fun n => q n (y n - (Tn n ^ (N n)) (y n))) (hyperfilter ℕ) (𝓝 0) := by
      have hsp : ∀ n, y n - (Tn n ^ (N n)) (y n) =
          (y n - F n (y n)) + (F n (y n) - (Tn n ^ (N n)) (y n)) := fun n => by abel
      simp_rw [hsp]
      exact tendsto_q_add hyF hFT_y
    have hE_TN : Tendsto
        (fun n => ((star ((Tn n ^ (N n)) (y n)) *
          ((Tn n ^ (N n)) (y n) - Tn n ((Tn n ^ (N n)) (y n)))).trace).re / (d n : ℝ))
        (hyperfilter ℕ) (𝓝 0) := by
      have hlimE : Tendsto (fun n => C ^ 2 * (1 / (2 * (N n : ℝ) + 1))) (hyperfilter ℕ) (𝓝 0) := by
        have h2 : Tendsto (fun n => 2 * (N n : ℝ) + 1) (hyperfilter ℕ) atTop :=
          ((tendsto_natCast_atTop_atTop.comp hN_atTop).const_mul_atTop two_pos).atTop_add tendsto_const_nhds
        have h1 : Tendsto (fun n => 1 / (2 * (N n : ℝ) + 1)) (hyperfilter ℕ) (𝓝 0) :=
          tendsto_const_nhds.div_atTop h2
        have h3 := h1.const_mul (C ^ 2)
        rw [mul_zero] at h3
        exact h3
      refine squeeze_zero (fun n => ?_) (fun n => ?_) hlimE
      · rw [hTn_energy]
        exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
      · have hdn : (0 : ℝ) < (d n : ℝ) := Nat.cast_pos.2 (hd n)
        have h1 := energy_pow_le (Tn n) (hTn_sa n) (hTn_pos n) (N n) (y n)
        have hpos : (0 : ℝ) < 2 * (N n : ℝ) + 1 := by positivity
        have h2 : ((star ((Tn n ^ (N n)) (y n)) *
            ((Tn n ^ (N n)) (y n) - Tn n ((Tn n ^ (N n)) (y n)))).trace).re / (d n : ℝ) ≤
            q n (y n) / (2 * (N n : ℝ) + 1) := by
          simp only [q]
          rw [div_div, div_le_div_iff₀ hdn (mul_pos hdn hpos)]
          nlinarith
        have h3 : q n (y n) ≤ C ^ 2 :=
          (q_le_opNorm_sq (hd n) (y n)).trans (by gcongr; exact hCy_le n)
        calc _ ≤ q n (y n) / (2 * (N n : ℝ) + 1) := h2
          _ ≤ C ^ 2 * (1 / (2 * (N n : ℝ) + 1)) := by
              rw [mul_one_div]; exact div_le_div_of_nonneg_right h3 hpos.le
    have hcomm_TN : Tendsto
        (fun n => q n ((u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * (Tn n ^ (N n)) (y n) -
          (Tn n ^ (N n)) (y n) * (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)))
        (hyperfilter ℕ) (𝓝 0) := by
      refine squeeze_zero (fun n => by positivity) (fun n => ?_)
        (by simpa using hE_TN.const_mul (4 * (Fintype.card ι : ℝ)))
      rw [hTn_energy n ((Tn n ^ (N n)) (y n)), ← mul_assoc, mul_one_div_cancel (by positivity), one_mul]
      exact Finset.single_le_sum (f := fun b => q n ((u b n : Matrix (Fin (d n)) (Fin (d n)) ℂ) *
        (Tn n ^ (N n)) (y n) - (Tn n ^ (N n)) (y n) * (u b n : Matrix (Fin (d n)) (Fin (d n)) ℂ)))
        (fun _ _ => by positivity) (Finset.mem_univ a)
    refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      (by simpa using (hcomm_TN.const_mul 2).add (hyT.const_mul 8))
    have hsp : (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n -
        y n * (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) =
        ((u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * (Tn n ^ (N n)) (y n) -
          (Tn n ^ (N n)) (y n) * (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) +
        ((u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * (y n - (Tn n ^ (N n)) (y n)) -
          (y n - (Tn n ^ (N n)) (y n)) * (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) := by
      noncomm_ring
    rw [hsp]
    have h1 := q_add_le
      ((u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * (Tn n ^ (N n)) (y n) -
        (Tn n ^ (N n)) (y n) * (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ))
      ((u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * (y n - (Tn n ^ (N n)) (y n)) -
        (y n - (Tn n ^ (N n)) (y n)) * (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ))
    have h2 : q n ((u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * (y n - (Tn n ^ (N n)) (y n)) -
        (y n - (Tn n ^ (N n)) (y n)) * (u a n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) ≤
        4 * q n (y n - (Tn n ^ (N n)) (y n)) := by
      simp only [q, mul_div_assoc']
      exact div_le_div_of_nonneg_right (ss_comm_unitary_le (u a n).2 _) (Nat.cast_nonneg _)
    linarith

end OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1_H3_R1
