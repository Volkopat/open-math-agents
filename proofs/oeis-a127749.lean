import OMAStatements.S_oeis_a127749

/-
# A127749: proof of both OEIS conjectures

Credit: @ShadowAlzazel
Prepared by the Fang and Fox Lemma Office (Lean by Claude Code).

Conjecture 1 (row sums mod 2 = Fredholm-Rueppel A036987). The row sums r of the inverse solve
A r = 1, so every window sum over ceil(n/2) <= k <= n equals 2n+1. Differencing windows gives
r(0) = 1, r(2m+1) = r(m) + 2, r(2m+2) = 2, hence r(n) is odd iff n = 2^j - 1.

Conjecture 2 (row sums of the triangle mod 2 = A111982). A closed form for the inverse.
For q >= 1 say that q is a binary prefix of m if m / 2^i = q for some i, and put
C_k(m) = 1 if k+1 is a binary prefix of m, else 0. Then
  M(n,k) = C_k(n+1) - C_k(n)
is the inverse of A101688 (that is A111967), and (2k+1) M(n,k) is the inverse of the triangle
1/(2n+1) [k <= n <= 2k] (that is A127749). Proof: the window sums of column k of M telescope to
C_k(n+1) - C_k(floor((n+1)/2)), and C_k(m) = [m = k+1] + C_k(floor(m/2)), because the binary
prefixes of m are m itself and the binary prefixes of floor(m/2). So every window sum is
[n = k], which is the identity matrix (for any nonzero row weights w(n), the inverse of
(1/w(n)) [k <= n <= 2k] is w(k) M(n,k)).
Every entry of M is a difference of two values in {0, 1}, so it lies in {-1, 0, 1}. Then each
entry (2k+1) M(n,k) of A127749 is 0 or odd, so its residue mod 2 is |M(n,k)|, and the row
sums of A127749 mod 2 are the row sums of |A111967|, which is A111982 by definition.
-/

open Matrix Finset OMA.S_oeis_a127749

namespace FFL_A127749

/-! ## Conjecture 1: the doubling recursion (as for A127750) -/

/-- The doubling recursion: `r 0 = 1`, `r (2m+1) = r m + 2`, `r (2m+2) = 2`. -/
def r : ℕ → ℕ
  | 0 => 1
  | n + 1 => if (n + 1) % 2 = 1 then r (n / 2) + 2 else 2

lemma r_zero : r 0 = 1 := by simp [r]

lemma r_odd (m : ℕ) : r (2 * m + 1) = r m + 2 := by
  rw [r, if_pos (by omega)]
  congr 2; omega

lemma r_even (m : ℕ) : r (2 * m + 2) = 2 := by
  rw [r, if_neg (by omega)]

/-- Window sums: the sum of `r k` over `ceil(n/2) ≤ k ≤ n` is `2n + 1`. -/
lemma blockSum_r (n : ℕ) : ∑ k ∈ Ico ((n + 1) / 2) (n + 1), r k = 2 * n + 1 := by
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
    (fun x => if x ≤ (i : ℕ) ∧ (i : ℕ) ≤ 2 * x then 1 / (2 * (i : ℚ) + 1) * (r x : ℚ) else 0)]
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
theorem rowSum_T (N : ℕ) (n : Fin N) : ∑ k, T N n k = r n := by
  have h : (triangle N)⁻¹ *ᵥ (fun _ => (1 : ℚ)) = fun k : Fin N => (r k : ℚ) := by
    rw [← tri_mulVec_r, mulVec_mulVec, nonsing_inv_mul _ (tri_det_isUnit N), one_mulVec]
  have := congrFun h n
  simpa [T, mulVec, dotProduct] using this

/-- `2m+1` has the form `2^j - 1` iff `m` does. -/
lemma odd_form_iff (m : ℕ) : (∃ j : ℕ, 2 * m + 1 = 2 ^ j - 1) ↔ (∃ j : ℕ, m = 2 ^ j - 1) := by
  constructor
  · rintro ⟨j, hj⟩
    rcases j with _ | j
    · simp at hj
    · refine ⟨j, ?_⟩
      have h1 : 0 < 2 ^ j := Nat.two_pow_pos j
      rw [pow_succ] at hj
      omega
  · rintro ⟨j, hj⟩
    refine ⟨j + 1, ?_⟩
    have h1 : 0 < 2 ^ j := Nat.two_pow_pos j
    rw [pow_succ]
    omega

theorem r_mod_two (n : ℕ) : (r n : ℤ) % 2 = (A036987 n : ℤ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    unfold A036987
    rcases n with _ | n
    · have h0 : ∃ m : ℕ, 0 = 2 ^ m - 1 := ⟨0, by norm_num⟩
      rw [if_pos h0, r_zero]
      norm_num
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · -- n + 1 = 2m + 1
      have ihm := ih m (by omega)
      unfold A036987 at ihm
      rw [r_odd]
      by_cases h : ∃ j : ℕ, m = 2 ^ j - 1
      · have h' : ∃ j : ℕ, 2 * m + 1 = 2 ^ j - 1 := (odd_form_iff m).2 h
        rw [if_pos h] at ihm
        rw [if_pos h']
        push_cast at ihm ⊢
        omega
      · have h' : ¬ ∃ j : ℕ, 2 * m + 1 = 2 ^ j - 1 := fun hh => h ((odd_form_iff m).1 hh)
        rw [if_neg h] at ihm
        rw [if_neg h']
        push_cast at ihm ⊢
        omega
    · -- n + 1 = 2m + 2
      rw [show 2 * m + 1 + 1 = 2 * m + 2 from rfl, r_even]
      have h' : ¬ ∃ j : ℕ, 2 * m + 2 = 2 ^ j - 1 := by
        rintro ⟨j, hj⟩
        rcases j with _ | j
        · simp at hj
        · have h1 : 0 < 2 ^ j := Nat.two_pow_pos j
          rw [pow_succ] at hj
          omega
      rw [if_neg h']
      norm_num

/-! ## Conjecture 2: a closed form for the inverse -/

open scoped Classical in
/-- `C k m = 1` if `k + 1` is a binary prefix of `m` (some `m / 2^i` equals `k + 1`), else `0`. -/
noncomputable def C (k m : ℕ) : ℤ := if ∃ i : ℕ, m / 2 ^ i = k + 1 then 1 else 0

/-- The closed form of A111967: `M n k = C k (n+1) - C k n`. -/
noncomputable def M (n k : ℕ) : ℤ := C k (n + 1) - C k n

/-- The binary prefixes of `m` are `m` and the binary prefixes of `m / 2`. -/
lemma prefix_iff (q m : ℕ) :
    (∃ i : ℕ, m / 2 ^ i = q) ↔ (m = q ∨ ∃ i : ℕ, m / 2 / 2 ^ i = q) := by
  constructor
  · rintro ⟨i, hi⟩
    rcases i with _ | i
    · left; simpa using hi
    · right
      refine ⟨i, ?_⟩
      rw [Nat.div_div_eq_div_mul, ← pow_succ']
      exact hi
  · rintro (h | ⟨i, hi⟩)
    · exact ⟨0, by simpa using h⟩
    · refine ⟨i + 1, ?_⟩
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
      exact hi

/-- The doubling step for prefix indicators. -/
lemma C_step (k m : ℕ) : C k m = (if m = k + 1 then 1 else 0) + C k (m / 2) := by
  unfold C
  by_cases hm : m = k + 1
  · have h1 : ∃ i : ℕ, m / 2 ^ i = k + 1 := ⟨0, by simpa using hm⟩
    have h2 : ¬ ∃ i : ℕ, m / 2 / 2 ^ i = k + 1 := by
      rintro ⟨i, hi⟩
      have : m / 2 / 2 ^ i ≤ m / 2 := Nat.div_le_self _ _
      omega
    rw [if_pos h1, if_pos hm, if_neg h2]
    norm_num
  · rw [if_neg hm, zero_add]
    have hiff : (∃ i : ℕ, m / 2 ^ i = k + 1) ↔ (∃ i : ℕ, m / 2 / 2 ^ i = k + 1) := by
      rw [prefix_iff]
      constructor
      · rintro (h | h)
        · exact absurd h hm
        · exact h
      · intro h
        exact Or.inr h
    by_cases h : ∃ i : ℕ, m / 2 / 2 ^ i = k + 1
    · rw [if_pos (hiff.2 h), if_pos h]
    · rw [if_neg (fun hh => h (hiff.1 hh)), if_neg h]

lemma tele (f : ℕ → ℤ) {a b : ℕ} (h : a ≤ b) :
    ∑ j ∈ Ico a b, (f (j + 1) - f j) = f b - f a := by
  rw [Finset.sum_Ico_eq_sub _ h, Finset.sum_range_sub, Finset.sum_range_sub]
  ring

/-- Column `k` of `M` has window sums `[n = k]`. -/
lemma window_M (n k : ℕ) :
    ∑ j ∈ Ico ((n + 1) / 2) (n + 1), M j k = if n = k then 1 else 0 := by
  simp only [M]
  rw [tele (C k) (by omega), C_step k (n + 1)]
  by_cases h : n = k
  · simp [h]
  · simp [h]

lemma M_cases (n k : ℕ) : M n k = 0 ∨ M n k = 1 ∨ M n k = -1 := by
  unfold M C
  split_ifs <;> simp

/-- The triangle with row weights `1 / w n`. -/
def triW (w : ℕ → ℚ) (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  fun n k => if (k : ℕ) ≤ n ∧ (n : ℕ) ≤ 2 * k then 1 / w n else 0

/-- Its inverse, in closed form. -/
noncomputable def invW (w : ℕ → ℚ) (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  fun n k => w k * (M n k : ℚ)

lemma triW_mul_invW (w : ℕ → ℚ) (hw : ∀ n, w n ≠ 0) (N : ℕ) : triW w N * invW w N = 1 := by
  ext i k
  simp only [mul_apply, triW, invW, ite_mul, zero_mul]
  rw [Fin.sum_univ_eq_sum_range
    (fun x => if x ≤ (i : ℕ) ∧ (i : ℕ) ≤ 2 * x then 1 / w i * (w k * (M x k : ℚ)) else 0)]
  rw [← Finset.sum_filter]
  have hf : (range N).filter (fun x => x ≤ (i : ℕ) ∧ (i : ℕ) ≤ 2 * x)
      = Ico (((i : ℕ) + 1) / 2) ((i : ℕ) + 1) := by
    ext x; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [hf, ← Finset.mul_sum, ← Finset.mul_sum, ← Int.cast_sum, window_M, Matrix.one_apply]
  by_cases h : i = k
  · subst h
    have hw' := hw i
    simp only [if_true]
    push_cast
    field_simp
  · have h' : (i : ℕ) ≠ k := fun e => h (Fin.ext e)
    rw [if_neg h', if_neg h]
    simp

lemma T_eq (N : ℕ) : T N = invW (fun n => 2 * (n : ℚ) + 1) N := by
  unfold T
  apply Matrix.inv_eq_right_inv
  have e : triangle N = triW (fun n => 2 * (n : ℚ) + 1) N := rfl
  rw [e]
  exact triW_mul_invW _ (fun n => by positivity) N

lemma inv101688_eq (N : ℕ) : (triangle101688 N)⁻¹ = invW (fun _ => 1) N := by
  apply Matrix.inv_eq_right_inv
  have e : triangle101688 N = triW (fun _ => 1) N := by
    ext i j
    simp [triangle101688, triW]
  rw [e]
  exact triW_mul_invW _ (fun _ => one_ne_zero) N

/-- Each entry of A127749, reduced mod 2, is the absolute value of the entry of A111967. -/
lemma entry_mod_two (n k : ℕ) : (2 * (k : ℤ) + 1) * M n k % 2 = |M n k| := by
  rcases M_cases n k with h | h | h <;> rw [h] <;> norm_num

end FFL_A127749

theorem OMA.solution : type_of% @OMA.S_oeis_a127749.main := by
  refine ⟨fun N n => ?_, fun N n => ?_⟩
  · refine ⟨FFL_A127749.r n, by rw [FFL_A127749.rowSum_T]; norm_cast, ?_⟩
    exact FFL_A127749.r_mod_two n
  · refine ⟨fun k => (2 * ((k : ℕ) : ℤ) + 1) * FFL_A127749.M n k, fun k => ?_, ?_⟩
    · rw [FFL_A127749.T_eq]
      simp [FFL_A127749.invW]
    · rw [OMA.S_oeis_a127749.A111982, FFL_A127749.inv101688_eq]
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [FFL_A127749.entry_mod_two]
      simp [FFL_A127749.invW]
