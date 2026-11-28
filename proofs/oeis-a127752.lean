import OMAStatements.S_oeis_a127752

/-
# A127752: proof of the OEIS conjecture (row sums mod 2 = A035263, shifted)

Credit: @ShadowAlzazel
Prepared by the Fang and Fox Lemma Office: https://shadowalzazel.github.io/Fang-and-Fox-Lemma-Office/

Proof.
1. The row sums a of the inverse triangle solve A a = 1. Row n of that system reads
   (1/(3n+1)) Σ_(ceil(n/2) ≤ k ≤ n) a(k) = 1, i.e. the window sum is 3n+1.
2. Differencing consecutive windows gives a doubling recursion
   r(0) = 1, r(2m+1) = r(m) + 3, r(2m+2) = 3, and r solves the window identity (blockSum_r).
   The truncated triangle is lower triangular with nonzero diagonal, hence invertible, so the
   row sums of its inverse are exactly r (rowSum_inv_tri), for every truncation size.
3. Mod 2: r(2m+2) is odd and r(2m+1) has the opposite parity of r(m); by strong induction
   r(n) mod 2 = (exponent of 2 in 2(n+1)) mod 2 = A035263(n+1) (r_mod_two).
-/

open Matrix Finset OMA.S_oeis_a127752

namespace FFL_A127752

/-- The doubling recursion: `r 0 = 1`, `r (2m+1) = r m + 3`, `r (2m+2) = 3`. -/
def r : ℕ → ℕ
  | 0 => 1
  | n + 1 => if (n + 1) % 2 = 1 then r (n / 2) + 3 else 3

lemma r_zero : r 0 = 1 := by simp [r]

lemma r_odd (m : ℕ) : r (2 * m + 1) = r m + 3 := by
  rw [r, if_pos (by omega)]
  congr 2; omega

lemma r_even (m : ℕ) : r (2 * m + 2) = 3 := by
  rw [r, if_neg (by omega)]

/-- Window sums: `Σ_(ceil(n/2) ≤ k ≤ n) r k = 3n + 1`. -/
lemma blockSum_r (n : ℕ) : ∑ k ∈ Ico ((n + 1) / 2) (n + 1), r k = 3 * n + 1 := by
  induction n with
  | zero => simp [r_zero]
  | succ n ih =>
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · have h1 : (2 * m + 1) / 2 = m := by omega
      have h2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      rw [h1] at ih; rw [h2]
      have e : ∑ k ∈ Ico m (2 * m + 1 + 1), r k
          = r m + ∑ k ∈ Ico (m + 1) (2 * m + 1 + 1), r k :=
        Finset.sum_eq_sum_Ico_succ_bot (by omega) _
      rw [Finset.sum_Ico_succ_top (by omega), ih, r_odd] at e
      omega
    · have h1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      have h2 : (2 * m + 1 + 1 + 1) / 2 = m + 1 := by omega
      rw [h1] at ih; rw [h2, Finset.sum_Ico_succ_top (by omega), ih,
        show 2 * m + 1 + 1 = 2 * m + 2 from rfl, r_even]
      omega

lemma tri_mulVec_r (N : ℕ) :
    triangle N *ᵥ (fun k : Fin N => (r k : ℚ)) = fun _ => 1 := by
  funext i
  simp only [mulVec, dotProduct, triangle, ite_mul, zero_mul]
  rw [Fin.sum_univ_eq_sum_range
    (fun x => if x ≤ (i : ℕ) ∧ (i : ℕ) ≤ 2 * x then 1 / (3 * (i : ℚ) + 1) * (r x : ℚ) else 0)]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  have hf : (range N).filter (fun x => x ≤ (i : ℕ) ∧ (i : ℕ) ≤ 2 * x)
      = Ico (((i : ℕ) + 1) / 2) ((i : ℕ) + 1) := by
    ext x; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [hf, ← Nat.cast_sum, blockSum_r]
  push_cast
  field_simp

lemma tri_lower (N : ℕ) : (triangle N).IsLowerTriangular := by
  intro i j hij
  have : (i : ℕ) < j := hij
  simp only [triangle]; rw [if_neg (by omega)]

lemma tri_det_isUnit (N : ℕ) : IsUnit (triangle N).det := by
  rw [det_of_isLowerTriangular _ (tri_lower N), isUnit_iff_ne_zero,
    Finset.prod_ne_zero_iff]
  intro i _
  simp only [triangle, le_refl, true_and]
  rw [if_pos (by omega)]
  positivity

/-- Row sums of the inverse of every truncation are given by `r`. -/
theorem rowSum_inv_tri (N : ℕ) (n : Fin N) : a N n = r n := by
  have h : (triangle N)⁻¹ *ᵥ (fun _ => (1 : ℚ)) = fun k : Fin N => (r k : ℚ) := by
    rw [← tri_mulVec_r, mulVec_mulVec, nonsing_inv_mul _ (tri_det_isUnit N), one_mulVec]
  have := congrFun h n
  simpa [a, mulVec, dotProduct] using this

theorem r_mod_two (n : ℕ) : r n % 2 = A035263 (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    unfold A035263
    rcases n with _ | n
    · simp [r_zero]
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · have ihm := ih m (by omega)
      unfold A035263 at ihm
      rw [r_odd, show 2 * (2 * m + 1 + 1) = 2 * (2 * (m + 1)) by ring,
        padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]
      omega
    · rw [show 2 * m + 1 + 1 = 2 * m + 2 from rfl, r_even,
        padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
        padicValNat.eq_zero_of_not_dvd (by omega)]

end FFL_A127752

theorem OMA.solution : type_of% @OMA.S_oeis_a127752.main := by
  intro N n
  refine ⟨FFL_A127752.r n, by rw [FFL_A127752.rowSum_inv_tri]; norm_cast, ?_⟩
  rw [← FFL_A127752.r_mod_two]; push_cast; rfl
