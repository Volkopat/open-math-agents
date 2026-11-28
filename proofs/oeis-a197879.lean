import OMAStatements.S_oeis_a197879
import Mathlib

namespace OMA.S_oeis_a197879

lemma s2lo : (1.414 : ℝ) < Real.sqrt 2 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num
lemma s2hi : Real.sqrt 2 < 1.415 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma fr_step (x : ℝ) :
    Int.fract (x + Real.sqrt 2) =
      if Int.fract x + (Real.sqrt 2 - 1) < 1 then Int.fract x + (Real.sqrt 2 - 1)
      else Int.fract x + (Real.sqrt 2 - 1) - 1 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  have hx : x = ⌊x⌋ + Int.fract x := (Int.floor_add_fract x).symm
  have := s2lo; have := s2hi
  split_ifs with h
  · rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, ⌊x⌋ + 1, ?_⟩
    push_cast; linarith
  · rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, ⌊x⌋ + 2, ?_⟩
    push_cast; linarith

lemma part1 (n : ℕ) : a n = if 1 / 2 < Int.fract (Real.sqrt 2 * n) then 1 else 0 := by
  unfold a
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8:ℝ) = 2^2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have ht : 0 ≤ Real.sqrt 2 * n := by positivity
  set t := Real.sqrt 2 * n with htd
  have hn : (n : ℝ) * Real.sqrt 8 = 2 * t := by rw [h8, htd]; ring
  rw [hn]
  have hk : ((⌊t⌋₊ : ℤ)) = ⌊t⌋ := Int.natCast_floor_eq_floor ht
  have hf : Int.fract t = t - ⌊t⌋₊ := by
    rw [Int.fract, ← hk]; push_cast; ring
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  have hne : Int.fract t ≠ 1/2 := by
    intro h
    have : Real.sqrt 2 * n = (⌊t⌋₊ : ℝ) + 1/2 := by linarith
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp at this; linarith [Nat.cast_nonneg (α := ℝ) ⌊t⌋₊]
    · have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
      apply hirr
      refine ⟨((2 * ⌊t⌋₊ + 1 : ℕ) : ℚ) / (2 * n), ?_⟩
      have : (n:ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      linarith
  split_ifs with h
  · have : ⌊2 * t⌋₊ = 2 * ⌊t⌋₊ + 1 := by
      rw [Nat.floor_eq_iff (by positivity)]
      push_cast; constructor <;> linarith
    omega
  · push_neg at h
    have h' : Int.fract t < 1/2 := lt_of_le_of_ne h hne
    have : ⌊2 * t⌋₊ = 2 * ⌊t⌋₊ := by
      rw [Nat.floor_eq_iff (by positivity)]
      push_cast; constructor <;> linarith
    omega

lemma gstep (m : ℕ) : Int.fract (Real.sqrt 2 * ((m + 1 : ℕ) : ℝ)) =
    if Int.fract (Real.sqrt 2 * m) + (Real.sqrt 2 - 1) < 1 then Int.fract (Real.sqrt 2 * m) + (Real.sqrt 2 - 1)
      else Int.fract (Real.sqrt 2 * m) + (Real.sqrt 2 - 1) - 1 := by
  rw [← fr_step]; congr 1; push_cast; ring

theorem sol : (∀ n : ℕ, 1 ≤ n → a n = if 1 / 2 < Int.fract (Real.sqrt 2 * n) then 1 else 0) ∧
    (∀ n : ℕ, 1 ≤ n → ¬ (a n = a (n + 1) ∧ a (n + 1) = a (n + 2))) := by
  refine ⟨fun n _ => part1 n, fun n _ => ?_⟩
  rintro ⟨h1, h2⟩
  rw [part1 n, part1 (n+1)] at h1
  rw [part1 (n+1), part1 (n+2)] at h2
  have g1 := gstep n
  have g2 := gstep (n + 1)
  have h0 := Int.fract_nonneg (Real.sqrt 2 * n)
  have h0' := Int.fract_lt_one (Real.sqrt 2 * n)
  have := s2lo; have := s2hi
  generalize Int.fract (Real.sqrt 2 * (n:ℝ)) = f at *
  generalize Int.fract (Real.sqrt 2 * ((n + 1 : ℕ) : ℝ)) = f1 at *
  generalize Int.fract (Real.sqrt 2 * ((n + 2 : ℕ) : ℝ)) = f2 at *
  split_ifs at h1 h2 g1 g2 <;> (try simp at h1 h2) <;> linarith

end OMA.S_oeis_a197879

theorem OMA.solution : type_of% @OMA.S_oeis_a197879.main := OMA.S_oeis_a197879.sol
