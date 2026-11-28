import OMAStatements.S_oeis_a350689

open Matrix Polynomial OMA.S_oeis_a350689

namespace OMA.A350689Proof

-- Within each pair of consecutive indices, the floor entry is affine
-- in the pair numbers, with one correction for an even row and odd column.
def u (i : ℕ) : Fin 3 → ℚ := ![1, -(i / 2 : ℕ), 1 - (i % 2 : ℕ)]
def v (j : ℕ) : Fin 3 → ℚ := ![(j / 2 : ℕ), 1, (j % 2 : ℕ)]
def A (n : ℕ) : Matrix (Fin n) (Fin 3) ℚ := fun i => u i.val
def B (n : ℕ) : Matrix (Fin 3) (Fin n) ℚ := fun i j => v j.val i
lemma entry (i j : ℕ) :
    ((⌊(((j : ℚ) + 1) - ((i : ℚ) + 1) + 1) / 2⌋ : ℤ) : ℚ) =
    ∑ t : Fin 3, u i t * v j t := by
  have hi : (i : ℚ) = 2 * ((i / 2 : ℕ) : ℚ) + (i % 2 : ℕ) := by exact_mod_cast (show i = 2 * (i / 2) + i%2 by omega)
  have hj : (j : ℚ) = 2 * ((j / 2 : ℕ) : ℚ) + (j % 2 : ℕ) := by exact_mod_cast (show j = 2 * (j / 2) + j%2 by omega)
  have hfloor : ⌊(((j : ℚ) + 1) - ((i : ℚ) + 1) + 1) / 2⌋ =
      (j/2 : ℕ) - (i/2 : ℕ) + (1 - (i%2 : ℕ)) * (j%2 : ℕ) := by
    apply Int.floor_eq_iff.mpr
    simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_natCast]
    rcases (show i%2=0 ∨ i%2=1 by omega) with h|h <;>
      rcases (show j%2=0 ∨ j%2=1 by omega) with g|g <;>
      rw [h] at hi <;> rw [g] at hj <;> rw [h,g] <;> norm_num at hi hj ⊢ <;> constructor <;> linarith
  rw [hfloor]
  simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_natCast]
  simp [u, v, Fin.sum_univ_succ]
  ring

-- Sum the outer products of the first n indices in the reversed product.
def partialSum (n : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  fun i j => ∑ t ∈ Finset.range n, v t i * u t j
def evenSum (t : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![t*(t-1), -t*(t-1)*(2*t-1)/3, t*(t-1)/2;
     2*t, -t*(t-1), t;
     t, -t*(t-1)/2, 0]
-- Adding one even index and one odd index gives a polynomial recurrence.
lemma evenClosed (t : ℕ) : partialSum (2*t) = evenSum t := by
  induction t with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> norm_num [partialSum,evenSum]
  | succ t ih =>
    ext i j
    have h := congrFun (congrFun ih i) j
    change (∑ k ∈ Finset.range (2*t), v k i * u k j) = _ at h
    change (∑ k ∈ Finset.range (2*(t+1)), v k i * u k j) = _
    rw [show 2*(t+1) = 2*t+1+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,h]
    fin_cases i <;> fin_cases j <;> simp [u,v,evenSum, Nat.mul_comm 2 t] <;> ring_nf <;> simp only [show (1+t*2)/2 = t by omega] <;> ring
lemma swapSum (n : ℕ) : B n * A n = partialSum n := by
  ext i j
  exact Fin.sum_univ_eq_sum_range (fun t => v t i * u t j) n

lemma oddClosed (t : ℕ) : partialSum (2*t+1) =
    evenSum t + Matrix.of (fun i j => v (2*t) i * u (2*t) j) := by
  ext i j
  have h := congrFun (congrFun (evenClosed t) i) j
  change (∑ k ∈ Finset.range (2*t+1), v k i * u k j) = _
  rw [Finset.sum_range_succ]
  exact congrArg (· + v (2*t) i * u (2*t) j) h

lemma detEven (t : ℕ) : (partialSum (2*t)).det =
    -((t : ℚ)^3 * ((t : ℚ)^2-1)/6) := by
  rw [evenClosed, Matrix.det_fin_three]
  simp [evenSum]
  ring

lemma detOdd (t : ℕ) : (partialSum (2*t+1)).det =
    -((2*(t : ℚ)+1)*(t : ℚ)^2*(t+1 : ℚ)^2/12) := by
  rw [oddClosed, Matrix.det_fin_three]
  simp [evenSum, Matrix.add_apply, u, v, Nat.mul_comm 2 t]
  ring

lemma factor (n : ℕ) : M n = A n * B n := by
  ext i j
  exact entry i.val j.val

lemma third (n : ℕ) (hn : 3 ≤ n) : extTrace (M n) 3 = (partialSum n).det := by
  rw [extTrace, if_pos hn, factor, ← swapSum,
    Matrix.charpoly_mul_comm_of_le (A n) (B n) (by simpa using hn)]
  simp [coeff_X_pow_mul', Matrix.det_eq_sign_charpoly_coeff]

lemma higher (n k : ℕ) (hk : 3 < k) : extTrace (M n) k = 0 := by
  unfold extTrace
  split
  next hn =>
    rw [factor, Matrix.charpoly_mul_comm_of_le (A n) (B n) (by simpa using (show 3 ≤ n by omega))]
    simp [coeff_X_pow_mul', show ¬ n-3 ≤ n-k by omega]
  next => rfl

lemma absDet (n : ℕ) (hn : 3 ≤ n) : |(partialSum n).det| = a n := by
  let t := n / 2
  have ht : (1 : ℚ) ≤ t := by exact_mod_cast (show 1 ≤ t by dsimp [t]; omega)
  have hs : (0 : ℚ) ≤ (t : ℚ)^2-1 := by nlinarith [sq_nonneg ((t : ℚ)-1)]
  rcases (show n = 2*t ∨ n = 2*t+1 by dsimp [t]; omega) with he|ho
  · rw [he, detEven, abs_neg, abs_of_nonneg (by positivity)]
    simp [a, pow_mul]
    ring
  · rw [ho, detOdd, abs_neg, abs_of_nonneg (by positivity)]
    simp [a, pow_succ (a := (-1:ℚ)) (2*t), pow_mul]
    ring

end OMA.A350689Proof

open OMA.A350689Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a350689.main := by
  intro n hn
  refine ⟨?_, higher n⟩
  by_cases h : 3 ≤ n
  · rw [third n h, absDet n h]
  · have he : n = 2 := by omega
    subst n
    norm_num [extTrace, a]
