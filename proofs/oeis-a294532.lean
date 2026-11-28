import OMAStatements.S_oeis_a294532

namespace OMA.S_oeis_a294532

private theorem indexBound {f : ℕ → ℕ} (hf : StrictMono f) (n : ℕ) : f 0+n ≤ f n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : f n < f (n+1) := hf (Nat.lt_succ_self n)
    change f 0 + (n+1) ≤ f (n+1)
    omega

private theorem correctionBounds {v : Profile} (hv : v ∈ profiles) {n x y : ℕ}
    (hy : n+3 ≤ y) (hxy : y < x) :
    0 ≤ correction v (n+2) x y ∧ correction v (n+2) x y ≤ 4*(x:ℤ) + 2*(n+2:ℤ) + 3 := by
  simp only [profiles, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    norm_num [correction] <;> omega

/-- Two consecutive integers above 3 cannot both be in `a`, so gaps in the
complementary sequence `b` are at most two. -/
private theorem complementBound {a b : ℕ → ℕ} (ha : StrictMono a) (hb : StrictMono b)
    (ha0 : a 0 = 1) (ha1 : a 1 = 2) (hb0 : b 0 = 3) (hcomp : complementary a b)
    (hrec : ∀ n, a (n+1) + a n ≤ a (n+2)) : ∀ n, b n ≤ 2*n+3 := by
  have gap (n : ℕ) : b (n+1) ≤ b n+2 := by
    have hnext (v : ℕ) (hv : b n < v) (hvb : v ∈ Set.range b) : b (n+1) ≤ v := by
      obtain ⟨j,rfl⟩ := hvb
      exact hb.monotone (hb.lt_iff_lt.mp hv)
    by_cases h1 : b n+1 ∈ Set.range b
    · have := hnext _ (Nat.lt_succ_self _) h1
      omega
    · have hmem : b n+1 ∈ Set.range a := by
        by_contra h
        exact h1 ((hcomp _ (by omega)).2 h)
      obtain ⟨i, hi⟩ := hmem
      have hbn := indexBound hb n
      have hg : b n+2 < a (i+1) := by
        cases i with
        | zero => omega
        | succ i =>
          cases i with
          | zero => change a 1 = b n+1 at hi; omega
          | succ i =>
            change a (i+2) = b n+1 at hi
            change b n+2 < a (i+3)
            have h : a (i+2) + a (i+1) ≤ a (i+3) := hrec (i+1)
            have h2 := indexBound ha (i+1)
            omega
      have hmiss : b n+2 ∉ Set.range a := by
        rintro ⟨j,hj⟩
        by_cases hji : j ≤ i
        · have := ha.monotone hji
          omega
        · have := ha.monotone (show i+1 ≤ j by omega)
          omega
      exact hnext _ (by omega) ((hcomp _ (by omega)).2 hmiss)
  intro n
  induction n with
  | zero => omega
  | succ n ih => have := gap n; omega

private theorem cubicLower {a : ℕ → ℕ} (hp : ∀ n, 0 < a n)
    (hrec : ∀ n, a (n+1) + a n ≤ a (n+2)) : ∀ n, (n+1)^3 ≤ 1000*a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n ≤ 7
    · have h := hp n
      interval_cases n <;> norm_num <;> omega
    · obtain ⟨k, rfl⟩ : ∃ k, n = k+2 := ⟨n-2, by omega⟩
      have h0 := ih k (by omega)
      have h1 := ih (k+1) (by omega)
      change (k+2)^3 ≤ 1000*a (k+1) at h1
      change (k+3)^3 ≤ 1000*a (k+2)
      have hr := hrec k
      have hc : (k+3)^3 ≤ (k+2)^3 + (k+1)^3 := by
        obtain ⟨j,rfl⟩ : ∃ j, k = j+6 := ⟨k-6, by omega⟩
        ring_nf
        omega
      omega

private theorem ratioLimit {a : ℕ → ℕ} (ha0 : a 0 = 1) (ha1 : a 1 = 2) (hp : ∀ n, 0 < a n)
    (hlo : ∀ n, a (n+1)+a n ≤ a (n+2))
    (hhi : ∀ n, a (n+2) ≤ a (n+1)+a n+32*(n+1)) :
    Filter.Tendsto (fun n : ℕ => (a (n+1) : ℝ) / a n) Filter.atTop (nhds Real.goldenRatio) := by
  let D (n : ℕ) : ℝ := a (n+1) - Real.goldenRatio * a n
  let E (n : ℕ) : ℝ := (a (n+2):ℝ) - a (n+1) - a n
  have hstep (n : ℕ) : D (n+1) = (1-Real.goldenRatio)*D n + E n := by
    dsimp only [D,E]
    linear_combination -((a n):ℝ) * Real.goldenRatio_sq
  have hcoef : |1-Real.goldenRatio| ≤ 1 := abs_le.mpr ⟨by linarith [Real.goldenRatio_lt_two], by linarith [Real.goldenRatio_pos]⟩
  have herror (n : ℕ) : |D n| ≤ 32*((n:ℝ)+1)^2 := by
    induction n with
    | zero =>
      simp only [D, zero_add, ha0, ha1, Nat.cast_one, Nat.cast_ofNat, mul_one, Nat.cast_zero]
      exact abs_le.mpr ⟨by linarith [Real.goldenRatio_lt_two], by linarith [Real.goldenRatio_pos]⟩
    | succ n ih =>
      have hl : (a (n+1):ℝ) + a n ≤ a (n+2) := by exact_mod_cast hlo n
      have hh : (a (n+2):ℝ) ≤ a (n+1) + a n + 32*((n:ℝ)+1) := by exact_mod_cast hhi n
      have he : 0 ≤ E n := by dsimp [E]; linarith
      have hE : E n ≤ 32*((n:ℝ)+1) := by dsimp [E]; linarith
      rw [hstep]
      calc
        _ ≤ |(1-Real.goldenRatio)*D n| + |E n| := abs_add_le ..
        _ ≤ |D n| + E n := by rw [abs_mul, abs_of_nonneg he]; gcongr; exact mul_le_of_le_one_left (abs_nonneg _) hcoef
        _ ≤ _ := by push_cast; nlinarith
  apply (tendsto_sub_nhds_zero_iff).mp
  have htop : Filter.Tendsto (fun n : ℕ => (32000:ℝ)/((n:ℝ)+1)) Filter.atTop (nhds 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 32000
  apply squeeze_zero_norm _ htop
  intro n
  have ha : 0 < (a n:ℝ) := by exact_mod_cast hp n
  have hn : 0 < (n:ℝ)+1 := by positivity
  have hc : ((n:ℝ)+1)^3 ≤ 1000*(a n:ℝ) := by exact_mod_cast cubicLower hp hlo n
  have hd : (a (n+1):ℝ)/a n - Real.goldenRatio = D n / a n := by dsimp [D]; field_simp
  rw [Real.norm_eq_abs, hd, abs_div, abs_of_pos ha]
  apply (div_le_div_iff₀ ha hn).mpr
  calc
    |D n| * ((n:ℝ)+1) ≤ 32*((n:ℝ)+1)^2*((n:ℝ)+1) := mul_le_mul_of_nonneg_right (herror n) hn.le
    _ ≤ _ := by nlinarith

end OMA.S_oeis_a294532

open OMA.S_oeis_a294532 in
theorem OMA.solution : type_of% @OMA.S_oeis_a294532.main := by
  intro v hv a b ha hb ha0 ha1 hb0 hcomp hrec
  have hstep (n : ℕ) := correctionBounds hv (n := n) (x := b (n+1)) (y := b n)
    (by have := indexBound hb n; omega) (hb (Nat.lt_succ_self n))
  have hlo (n : ℕ) : a (n+1)+a n ≤ a (n+2) := by
    have := (hstep n).1
    have := hrec n
    omega
  have hbBound := complementBound ha hb ha0 ha1 hb0 hcomp hlo
  apply ratioLimit ha0 ha1 (fun n => by have := indexBound ha n; omega) hlo
  intro n
  have := (hstep n).2
  have := hbBound (n+1)
  have := hrec n
  omega
