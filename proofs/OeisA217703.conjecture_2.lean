import FormalConjectures.OEIS.«217703»
import Mathlib.Analysis.PSeries

/-! Shorter proof of `OeisA217703.conjecture_2` via harmonic descent. -/

open OeisA217703 Finset

private lemma hdesc (g : ℕ → ℝ) (m : ℕ) (L : ℝ) (hl : ∀ k, L ≤ g k)
    (hd : ∀ k : ℕ, 1 / ((k + m : ℕ) : ℝ) ≤ g k - g (k + 1)) : False :=
  Real.not_summable_one_div_natCast <| (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) m).mp <|
    summable_of_sum_range_le (c := g 0 - L) (fun _ => by positivity) fun N =>
      (sum_le_sum fun k _ => hd k).trans <| by rw [sum_range_sub' g N]; linarith [hl N]

private lemma rstep {n t u : ℝ} (hn : 1 ≤ n) (hD : 0 < n + 2 + t) (ht : t ≤ n)
    (hu : u * (n * (n + 2 + t)) = (n + 1) * (n * t - 1)) : 1 / (n + 1) ≤ 4 * t - 4 * u := by
  have hn' : 0 < n := by linarith
  have hnum : n / 2 ≤ n * (t ^ 2 + t + 1) + 1 := by
    nlinarith [mul_nonneg hn'.le (sq_nonneg (2 * t + 1))]
  have he : (t - u) * (n * (n + 2 + t)) = n * (t ^ 2 + t + 1) + 1 := by nlinarith only [hu]
  refine (div_le_iff₀ (by linarith : 0 < n + 1)).2 <| le_of_mul_le_mul_right ?_ (mul_pos hn' hD)
  nlinarith only [congrArg (fun z : ℝ => (n + 1) * z) he,
    mul_nonneg (sub_nonneg.mpr hnum) (show 0 ≤ n + 1 by linarith),
    mul_nonneg hn'.le (sub_nonneg.mpr ht)]

private lemma recstep {n t u : ℝ} (hn : 1 ≤ n) (ht : t ≤ -1) (hu' : u < 0)
    (hu : u * (n * (n + 2 + t)) = (n + 1) * (n * t - 1)) : 1 / (n + 1) ≤ -4 / t - -4 / u := by
  have ht' : t < 0 := by linarith
  have hE : 0 < (n + 1) * (t * (n * t - 1)) :=
    mul_pos (by linarith) (mul_pos_of_neg_of_neg ht' (by nlinarith))
  refine le_of_mul_le_mul_right ?_ hE
  have he : (-4 / t - -4 / u) * ((n + 1) * (t * (n * t - 1))) = 4 * (n * (t ^ 2 + t + 1) + 1) := by
    calc _ = -4 * ((n + 1) * (n * t - 1)) + 4 / u * t * ((n + 1) * (n * t - 1)) := by
            field_simp [ht'.ne, hu'.ne]; ring
      _ = _ := by rw [← hu]; field_simp [hu'.ne]; nlinarith only [hu]
  rw [he, show 1 / (n + 1) * ((n + 1) * (t * (n * t - 1))) = t * (n * t - 1) by field_simp]
  nlinarith [mul_nonneg (by linarith : 0 ≤ n)
      (show 0 ≤ 3 * t ^ 2 + 5 * t + 4 by nlinarith [sq_nonneg (6 * t + 5)]),
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hn) ht'.le]

theorem OMA.solution : type_of% @OeisA217703.conjecture_2 := by
  intro h
  let b (k : ℕ) : ℝ := a (k + 2178)
  let N (k : ℕ) : ℝ := (k + 2179 : ℕ)
  let t (k : ℕ) := N k - N k ^ 3 * b k / b (k + 1)
  have hb (k : ℕ) : b k < 0 := by dsimp only [b]; exact_mod_cast (h (k + 2178)).2 (Or.inr (by omega))
  have hN (k : ℕ) : (1 : ℝ) ≤ N k := by dsimp only [N]; exact_mod_cast (show 1 ≤ k + 2179 by omega)
  have hstep (k : ℕ) : 0 < N k + 2 + t k ∧ t k ≤ N k ∧
      t (k + 1) * (N k * (N k + 2 + t k)) = (N k + 1) * (N k * t k - 1) := by
    have hrec : b (k + 2) = 2 * N k * (N k + 1) * b (k + 1) - N k ^ 4 * b k := by
      have hz : a (k + 2178 + 2) = 2 * ((k + 2178 : ℕ) + 1 : ℤ) * (((k + 2178 : ℕ) + 1 : ℤ) + 1) *
          a (k + 2178 + 1) - ((k + 2178 : ℕ) + 1 : ℤ) ^ 4 * a (k + 2178) := by rw [a]
      dsimp only [b, N]
      rw [show k + 2 + 2178 = k + 2178 + 2 by omega, show k + 1 + 2178 = k + 2178 + 1 by omega, hz]
      push_cast; ring
    have hN0 : 0 < N k := by linarith [hN k]
    have he : N k * (N k + 2 + t k) = b (k + 2) / b (k + 1) := by
      dsimp only [t]; rw [hrec]; field_simp [(hb (k + 1)).ne]; ring
    refine ⟨pos_of_mul_pos_right (he ▸ div_pos_of_neg_of_neg (hb (k + 2)) (hb (k + 1))) hN0.le,
      by have := div_nonneg_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hN0.le 3) (hb k).le)
           (hb (k + 1)).le; dsimp only [t]; linarith,
      by rw [he]; dsimp only [t]; rw [show N (k + 1) = N k + 1 by dsimp [N]; push_cast; ring]
         field_simp [(hb (k + 2)).ne, (hb (k + 1)).ne]; rw [hrec]; ring⟩
  have hs (k : ℕ) := rstep (hN k) (hstep k).1 (hstep k).2.1 (hstep k).2.2
  have hanti : Antitone t := antitone_nat_of_succ_le fun k => by
    have := hs k
    have : (0 : ℝ) < 1 / (N k + 1) := by positivity
    linarith
  obtain ⟨K, hK⟩ : ∃ K, t K ≤ -1 := by
    by_contra! hh
    exact hdesc (fun k => 4 * t k) 2180 (-4) (fun k => by linarith [hh k]) fun k => by
      convert hs k using 1; dsimp only [N]; push_cast; ring_nf
  have hlow (k : ℕ) : t (k + K) ≤ -1 := (hanti (by omega)).trans hK
  exact hdesc (fun k => -4 / t (k + K)) (K + 2180) 0
    (fun k => div_nonneg_of_nonpos (by norm_num) (by linarith [hlow k])) fun k => by
      have hu : t (k + K + 1) < 0 := (hanti (Nat.le_succ _) |>.trans (hlow k)).trans_lt (by norm_num)
      convert recstep (hN (k + K)) (hlow k) hu (hstep (k + K)).2.2 using 1
      · dsimp only [N]; push_cast; ring_nf
      · ring_nf
