import OMAStatements.S_mo_408662
import Mathlib

namespace OMA.S_mo_408662

open Matrix Polynomial Finset
open scoped BigOperators ComplexConjugate

private theorem periodic_pow {w : ℂ} {n : ℕ} (h : w ^ n = 1) (k : ℕ) :
    w ^ (k % n) = w ^ k := by
  calc
    w ^ (k % n) = w ^ (k % n) * (w ^ n) ^ (k / n) := by simp [h]
    _ = w ^ k := by rw [← pow_mul, ← pow_add, Nat.mod_add_div]

/-- Reindexing a Hankel row by cyclic translation conjugates the Fourier vector. -/
private theorem row_transform {n : ℕ} [NeZero n] (c : ℕ → ℂ) (i : Fin n)
    (w : ℂ) (hw : w ^ n = 1) :
    (∑ j : Fin n, c (i + j).val * w ^ j.val) =
      conj (w ^ i.val) * transform n c w := by
  have hwn : ‖w‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hw (NeZero.ne n)
  have hi : conj (w ^ i.val) * w ^ i.val = 1 := by
    rw [Complex.conj_mul', norm_pow, hwn]
    simp
  calc
    _ = ∑ j : Fin n, conj (w ^ i.val) * (c (i + j).val * w ^ (i + j).val) := by
      apply Finset.sum_congr rfl
      intro j _
      have hpow : w ^ (i + j).val = w ^ i.val * w ^ j.val := by
        change w ^ ((i.val + j.val) % n) = _
        rw [periodic_pow hw, pow_add]
      rw [hpow]
      calc
        _ = (conj (w ^ i.val) * w ^ i.val) * (c (i + j).val * w ^ j.val) := by rw [hi, one_mul]
        _ = _ := by ring
    _ = conj (w ^ i.val) * ∑ j : Fin n, c j.val * w ^ j.val := by
      rw [← Finset.mul_sum]
      congr 1
      exact Fintype.sum_equiv (Equiv.addLeft i) _ _ (fun _ => rfl)
    _ = _ := by
      unfold transform
      exact congrArg (fun v => conj (w ^ i.val) * v)
        (Fin.sum_univ_eq_sum_range (fun j => c j * w ^ j) n)

private theorem gram_spectrum (n : ℕ) (hn : 0 < n) (c : ℕ → ℂ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ n) :
    ((hankel n c)ᴴ * hankel n c).charpoly =
      ∏ i : Fin n, (X - C ((‖transform n c (ζ ^ i.val)‖ ^ 2 : ℝ) : ℂ)) := by
  let : NeZero n := ⟨hn.ne'⟩
  let w (j : Fin n) : ℂ := ζ ^ j.val
  let H := hankel n c
  let V := (vandermonde w)ᵀ
  let W : Matrix (Fin n) (Fin n) ℂ := .of fun i j => conj (w j ^ i.val)
  let T (j : Fin n) : ℂ := transform n c (w j)
  let D (j : Fin n) : ℂ := (‖T j‖ ^ 2 : ℝ)
  have hw (j : Fin n) : w j ^ n = 1 := by
    rw [show w j = ζ ^ j.val from rfl, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hV : H * V = W * diagonal T := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    exact row_transform c i (w j) (hw j)
  have hW : Hᴴ * W = V * diagonal (fun j => conj (T j)) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    have hrow := congrArg (starRingEnd ℂ) (row_transform c i (w j) (hw j))
    simp only [map_sum, map_mul, starRingEnd_apply,
      star_star] at hrow
    simpa only [H, W, V, T, conjTranspose_apply, hankel, Matrix.of_apply, transpose_apply,
      vandermonde, starRingEnd_apply, add_comm] using hrow
  have hD : diagonal (fun j => conj (T j)) * diagonal T = diagonal D := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext j
    simpa only [D, Complex.ofReal_pow] using Complex.conj_mul' (T j)
  have hgram : (Hᴴ * H) * V = V * diagonal D := by
    rw [mul_assoc, hV, ← mul_assoc, hW, mul_assoc, hD]
  have hVdet : V.det ≠ 0 := by
    rw [Matrix.det_transpose]
    apply det_vandermonde_ne_zero_iff.mpr
    intro i j h
    exact Fin.ext (hζ.pow_inj i.isLt j.isLt h)
  have hunit : IsUnit V.det := isUnit_iff_ne_zero.mpr hVdet
  obtain ⟨U, hU⟩ := (Matrix.isUnit_iff_isUnit_det V).mpr hunit
  have hconj : Hᴴ * H = V * diagonal D * V⁻¹ := by
    rw [← hgram]
    exact (V.mul_nonsing_inv_cancel_right (Hᴴ * H) hunit).symm
  change (Hᴴ * H).charpoly = _
  rw [hconj, ← hU, charpoly_units_conj, charpoly_diagonal]

private theorem sum_pair {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    ∑ j ∈ Finset.range (2 * n), f j =
      ∑ j ∈ Finset.range n, (f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ac_rfl

/-- Separating the even and odd powers gives the two evaluations. -/
private theorem split_transform (n : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    transform (2 * n) c z =
      transform n (fun i => c (2*i)) (z^2) + z * transform n (fun i => c (2*i+1)) (z^2) := by
  unfold transform
  rw [sum_pair, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [pow_mul]
  · apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ, pow_mul]
    ring

private theorem split_neg (n : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    transform (2 * n) c (-z) =
      transform n (fun i => c (2*i)) (z^2) - z * transform n (fun i => c (2*i+1)) (z^2) := by
  rw [split_transform, neg_sq, neg_mul, sub_eq_add_neg]

private theorem split_estimate (E B z : ℂ) (hz : ‖z‖ = 1) :
    |‖E + z * B‖ - ‖E - z * B‖| ≤ 2 * ‖B‖ ∧
      2 * ‖B‖ ≤ ‖E + z * B‖ + ‖E - z * B‖ := by
  have hval : ‖(E + z * B) - (E - z * B)‖ = 2 * ‖B‖ := by
    rw [show E + z * B - (E - z * B) = 2 * (z * B) by ring, norm_mul, norm_mul, hz, one_mul]
    norm_num
  constructor
  · rw [← hval]
    exact abs_norm_sub_norm_le _ _
  · rw [← hval]
    exact norm_sub_le _ _

private theorem sample_interpolation (N : ℕ) (d : ℕ → ℝ) :
    ∃ P : ℝ[X], ∀ i < N, P.eval ((i : ℝ) + 1) = d i := by
  let v (i : ℕ) : ℝ := (i : ℝ) + 1
  refine ⟨Lagrange.interpolate (Finset.range N) v d, ?_⟩
  intro i hi
  apply Lagrange.eval_interpolate_at_node d _ (Finset.mem_range.mpr hi)
  intro a _ b _ h
  have hab : (a : ℝ) = (b : ℝ) := by dsimp [v] at h; linarith
  exact_mod_cast hab

/-- One free sample dominates all the prescribed samples on the unit circle. -/
private theorem large_spectrum (n : ℕ) (hn : 0 < n) (b : ℕ → ℝ) (R : ℝ) :
    ∃ P : ℝ[X], (∀ i < n, P.eval (2 * ((i : ℝ) + 1)) = b i) ∧
      ∀ z : ℂ, z ^ (2*n) = 1 →
        R ≤ ‖transform (2*n) (fun i => ((P.eval ((i:ℝ)+1) : ℝ) : ℂ)) z‖ := by
  let S : ℝ := ∑ i ∈ Finset.range n, ‖b i‖
  let K : ℝ := max R 0 + S
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => norm_nonneg (b i)
  have hK : 0 ≤ K := add_nonneg (le_max_right _ _) hS
  let d (i : ℕ) : ℝ := if i = 0 then K else if i % 2 = 1 then b (i / 2) else 0
  obtain ⟨P, hP⟩ := sample_interpolation (2*n) d
  have hOdd (i : ℕ) (hi : i < n) : P.eval (((2 * i + 1 : ℕ) : ℝ) + 1) = b i := by
    rw [hP _ (by omega)]
    have hm : (2 * i + 1) % 2 = 1 := by omega
    have hd : (2 * i + 1) / 2 = i := by omega
    simp [d, hm, hd]
  refine ⟨P, ?_, ?_⟩
  · intro i hi
    convert hOdd i hi using 2 <;> push_cast <;> ring
  · intro z hz
    have hz1 : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz (by omega)
    let a (i : ℕ) : ℂ := (P.eval ((i : ℝ) + 1) : ℝ)
    change R ≤ ‖transform (2*n) a z‖
    have hE : transform n (fun i => a (2 * i)) (z ^ 2) = (K : ℂ) := by
      unfold transform
      rw [Finset.sum_eq_single 0]
      · have hzero : a 0 = (K : ℂ) := by
          dsimp only [a]
          rw [hP 0 (by omega), show d 0 = K from if_pos rfl]
        simpa only [mul_zero, pow_zero, mul_one] using hzero
      · intro i hi hi0
        have hil : i < n := Finset.mem_range.mp hi
        have hne : 2 * i ≠ 0 := by omega
        have hm : (2 * i) % 2 = 0 := by omega
        have hzero : a (2 * i) = 0 := by
          dsimp only [a]
          rw [hP (2*i) (by omega)]
          simp [d, hne, hm]
        change a (2 * i) * (z ^ 2) ^ i = 0
        rw [hzero, zero_mul]
      · intro h
        exact (h (Finset.mem_range.mpr hn)).elim
    have hB : ‖transform n (fun i => a (2 * i + 1)) (z ^ 2)‖ ≤ S := by
      unfold transform
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro i hi
      have hbi : a (2 * i + 1) = (b i : ℂ) :=
        congrArg Complex.ofReal (hOdd i (Finset.mem_range.mp hi))
      change ‖a (2 * i + 1) * (z ^ 2) ^ i‖ ≤ ‖b i‖
      rw [hbi, norm_mul, norm_pow, norm_pow, hz1, one_pow, one_pow, mul_one, Complex.norm_real]
    rw [split_transform, hE]
    let B := transform n (fun i => a (2 * i + 1)) (z ^ 2)
    have hnorm : ‖z * B‖ ≤ S := by rw [norm_mul, hz1, one_mul]; exact hB
    have htriangle := norm_sub_le ((K : ℂ) + z * B) (z * B)
    rw [add_sub_cancel_right, Complex.norm_real, Real.norm_of_nonneg hK] at htriangle
    have hR : R ≤ max R 0 := le_max_left _ _
    dsimp [K] at htriangle
    linarith

end OMA.S_mo_408662

open OMA.S_mo_408662 in
theorem OMA.solution : type_of% @OMA.S_mo_408662.main := by
  refine ⟨gram_spectrum, ?_, sample_interpolation, large_spectrum⟩
  intro n c z
  dsimp
  refine ⟨split_transform n c z, split_neg n c z, ?_⟩
  intro hz
  rw [split_transform n c z, split_neg n c z]
  exact split_estimate _ _ _ hz