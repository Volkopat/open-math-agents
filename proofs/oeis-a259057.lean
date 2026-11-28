import OMAStatements.S_oeis_a259057
import Mathlib

/-!
Wolfdieter Lang's divisibility conjecture for his even bisymmetric matrices.
In size at least four, add the two central columns and subtract the columns
immediately outside them. The resulting column has two sixes and zeros
elsewhere. This gives a nonzero kernel vector after reduction modulo three.
-/

namespace BisymmetricDivisibility

open OMA.S_oeis_a259057 Matrix

/-- Sum two columns that are mirror images, using the depth of the row. -/
private theorem paired (n x y : ℤ) (hy : 2*y ≤ n-1) :
    entry n x y + entry n x (n-1-y) =
      n+1 + 2 * min (min x (n-1-x)) y * (n - min (min x (n-1-x)) y) := by
  let d := min (min x (n-1-x)) y
  have h₁ : radius n x y = d := by unfold radius d; omega
  have h₂ : radius n x (n-1-y) = d := by unfold radius d; omega
  have hdist : |x-y| + |x-(n-1-y)| = n-1-2*d := by
    simp only [abs_eq_max_neg, d]
    omega
  change _ = n+1+2*d*(n-d)
  simp only [entry, h₁, h₂]
  linarith only [hdist]

private theorem central (k x : ℤ) :
    (3 : ℤ) ∣ entry (2*k+4) x (k+1) + entry (2*k+4) x (k+2) -
      (entry (2*k+4) x k + entry (2*k+4) x (k+3)) := by
  have hi := paired (2*k+4) x (k+1) (by omega)
  have ho := paired (2*k+4) x k (by omega)
  rw [show 2*k+4-1-(k+1) = k+2 by ring] at hi
  rw [show 2*k+4-1-k = k+3 by ring] at ho
  rw [hi, ho]
  let r := min x (2*k+4-1-x)
  change 3 ∣ (2*k+4+1+2*min r (k+1)*(2*k+4-min r (k+1))) -
    (2*k+4+1+2*min r k*(2*k+4-min r k))
  have hr : r ≤ k+1 := by dsimp [r]; omega
  rw [min_eq_left hr]
  by_cases h : r ≤ k
  · simp [min_eq_left h]
  · have he : r = k+1 := by omega
    rw [min_eq_right (by omega : k ≤ r), he]
    exact ⟨2, by ring⟩

private theorem determinant_dvd (k : ℕ) : (3 : ℤ) ∣ (B (2*(k+2))).det := by
  let n := 2*(k+2)
  let left : Fin n := ⟨k, by dsimp [n]; omega⟩
  let middle₁ : Fin n := ⟨k+1, by dsimp [n]; omega⟩
  let middle₂ : Fin n := ⟨k+2, by dsimp [n]; omega⟩
  let right : Fin n := ⟨k+3, by dsimp [n]; omega⟩
  let M : Matrix (Fin n) (Fin n) (ZMod 3) := (B n).map fun x => (x : ZMod 3)
  let v : Fin n → ZMod 3 :=
    (Pi.single middle₁ 1 + Pi.single middle₂ 1) - (Pi.single left 1 + Pi.single right 1)
  have hv : v ≠ 0 := by
    intro h
    have e := congrFun h middle₁
    have h₁ : middle₁ ≠ middle₂ := by intro q; have := congrArg Fin.val q; dsimp [middle₁,middle₂] at this; omega
    have h₂ : middle₁ ≠ left := by intro q; have := congrArg Fin.val q; dsimp [middle₁,left] at this; omega
    have h₃ : middle₁ ≠ right := by intro q; have := congrArg Fin.val q; dsimp [middle₁,right] at this; omega
    simp [v, h₁, h₂, h₃] at e
  have hMv : M *ᵥ v = 0 := by
    funext i
    simp only [v, mulVec_sub, mulVec_add, mulVec_single_one, Pi.sub_apply, Pi.add_apply,
      Pi.zero_apply, col_apply]
    have hd := central (k : ℤ) (i.val : ℤ)
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 hd
    push_cast at hz
    simpa [M, B, entry, n, middle₁, middle₂, left, right, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, mul_add] using hz
  have hdet : M.det = 0 := (Matrix.exists_mulVec_eq_zero_iff).1 ⟨v, hv, hMv⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1
  rw [Int.cast_det]
  exact hdet

theorem result : type_of% @OMA.S_oeis_a259057.main := by
  intro m hm
  match m with
  | 0 => omega
  | 1 =>
    refine ⟨-1, ?_⟩
    change ((B 2).det : ℚ) / 3 = -1
    rw [Matrix.det_fin_two]
    norm_num [B, entry, radius, Fin.isValue]
  | k + 2 =>
    obtain ⟨z, hz⟩ := determinant_dvd k
    exact ⟨z, by rw [normalizedDet, hz]; push_cast; ring⟩

end BisymmetricDivisibility

theorem OMA.solution : type_of% @OMA.S_oeis_a259057.main := BisymmetricDivisibility.result
