import FormalConjectures.ErdosProblems.«873»

/-! The Erdős–Szemerédi upper bound via telescoping logarithmic increments. -/

open Filter
open scoped BigOperators ENNReal

theorem OMA.solution : type_of% @Erdos873.erdos_873.variants.triple_upper_bound := by
  classical
  refine ⟨4, by norm_num, fun a ha hm => ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  let P (i : ℕ) : Prop := (((Finset.range 3).lcm (fun j => a (i + j)) : ℕ) : ℝ) < X
  let N := ⌊X⌋₊ + 1
  let W := (Finset.range N).filter P
  have hlcm3 (i : ℕ) : (Finset.range 3).lcm (fun j => a (i + j)) = (a (i + 2)).lcm ((a i).lcm (a (i + 1))) := by
    rw [show Finset.range 3 = {2, 0, 1} by decide, Finset.lcm_insert, Finset.lcm_insert]; simp; rfl
  have haSz (i : ℕ) : i + 1 ≤ a i := by
    induction i with
    | zero => exact ha
    | succ i ih => have : a i < a (i + 1) := hm (Nat.lt_succ_self i); omega
  have hUp {i} (hi : P i) : (a (i + 2) : ℝ) < X := by
    have hl : a (i + 2) ≤ (a (i + 2)).lcm ((a i).lcm (a (i + 1))) := Nat.le_of_dvd
      (Nat.lcm_pos (by have := haSz (i + 2); omega)
        (Nat.lcm_pos (by have := haSz i; omega) (by have := haSz (i + 1); omega))) (Nat.dvd_lcm_left _ _)
    have hl' : (a (i + 2) : ℝ) ≤ (((a (i + 2)).lcm ((a i).lcm (a (i + 1))) : ℕ) : ℝ) := by exact_mod_cast hl
    exact hl'.trans_lt (by simpa only [P, hlcm3] using hi)
  have hset : {i : ℕ | P i} = (W : Set ℕ) := by
    ext i; simp only [Set.mem_ofPred_eq, Finset.mem_coe, W, Finset.mem_filter, Finset.mem_range]
    refine ⟨fun hi => ⟨Nat.lt_succ_of_le (Nat.le_floor ((by exact_mod_cast (show i ≤ a (i + 2) by
      have := haSz (i + 2); omega) : (i : ℝ) ≤ a (i + 2)).trans (hUp hi).le)), hi⟩, fun h => h.2⟩
  let L (i : ℕ) := min (Real.log (a i : ℝ)) (Real.log X)
  have hL : Monotone L := fun i j h => min_le_min (Real.log_le_log
    (by exact_mod_cast (show 0 < a i by have := haSz i; omega)) (by exact_mod_cast hm.monotone h)) le_rfl
  have hLnn (i : ℕ) : 0 ≤ L i :=
    le_min (Real.log_nonneg (by exact_mod_cast (show 1 ≤ a i by have := haSz i; omega))) (Real.log_nonneg hX)
  have hLstep {i} (hi : P i) : 1 ≤ 2 * X ^ (1 / 3 : ℝ) * (L (i + 2) - L i) := by
    have hpos (j : ℕ) : (0 : ℝ) < a j := by exact_mod_cast (show 0 < a j by have := haSz j; omega)
    have h1 : a i < a (i + 1) := hm (by omega)
    have h2 : a (i + 1) < a (i + 2) := hm (by omega)
    have hlt : (a i : ℝ) ≤ a (i + 2) := by exact_mod_cast h1.le.trans h2.le
    rw [show L (i + 2) = Real.log (a (i + 2)) from min_eq_left (Real.log_le_log (hpos _) (hUp hi).le),
      show L i = Real.log (a i) from min_eq_left (Real.log_le_log (hpos _) (hlt.trans (hUp hi).le))]
    let x := a i; let y := a (i + 1); let z := a (i + 2)
    have hx : 0 < x := by have := haSz i; omega
    have hz : 0 < z := by omega
    have hgcd {u v w : ℕ} (huv : u < v) (hw : v - u ≤ w) : u.gcd v ≤ w :=
      (Nat.le_of_dvd (Nat.sub_pos_of_lt huv) (Nat.dvd_sub (Nat.gcd_dvd_right u v) (Nat.gcd_dvd_left u v))).trans hw
    have hb : z.gcd (x.lcm y) ≤ z.gcd x * z.gcd y := Nat.le_of_dvd
      (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ hz) (Nat.gcd_pos_of_pos_left _ hz))
      ((Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ((Nat.gcd_dvd_right _ _).trans
        (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)))).trans (gcd_mul_dvd_mul_gcd z x y))
    have hgapN : x ^ 3 ≤ z.lcm (x.lcm y) * (z - x) ^ 3 := by
      have hw1 : x.gcd y ≤ z - x := hgcd h1 (by omega)
      have hw2 : z.gcd x ≤ z - x := by rw [Nat.gcd_comm]; exact hgcd (by omega) le_rfl
      have hw3 : z.gcd y ≤ z - x := by rw [Nat.gcd_comm]; exact hgcd h2 (by omega)
      calc x ^ 3 ≤ x * y * z := by rw [pow_succ, pow_two]; gcongr; omega
        _ = x.gcd y * (z.gcd (x.lcm y) * z.lcm (x.lcm y)) := by
            rw [Nat.gcd_mul_lcm]; calc x * y * z = (x.gcd y * x.lcm y) * z := by rw [Nat.gcd_mul_lcm]
              _ = _ := by ac_rfl
        _ ≤ x.gcd y * ((z.gcd x * z.gcd y) * z.lcm (x.lcm y)) := by gcongr
        _ ≤ (z - x) * (((z - x) * (z - x)) * z.lcm (x.lcm y)) := by gcongr
        _ = _ := by ring
    let s := X ^ (1 / 3 : ℝ)
    have hs : 1 ≤ s := Real.one_le_rpow hX (by norm_num)
    have hs3 : s ^ 3 = X := by dsimp only [s]; rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ X)]; norm_num
    have hxr : (0 : ℝ) < x := hpos i; have hzr : (0 : ℝ) < z := hpos (i + 2)
    have hgap : 0 ≤ (z : ℝ) - x := sub_nonneg.2 hlt
    have hcube : (x : ℝ) ^ 3 ≤ (z.lcm (x.lcm y) : ℝ) * ((z : ℝ) - x) ^ 3 := by
      rw [← Nat.cast_sub (h1.le.trans h2.le)]; exact_mod_cast hgapN
    have hlcm : (z.lcm (x.lcm y) : ℝ) < X := by simpa only [P, hlcm3] using hi
    have hsg : (x : ℝ) ≤ s * ((z : ℝ) - x) := by
      have hp' := hcube.trans (mul_le_mul_of_nonneg_right hlcm.le (pow_nonneg hgap 3))
      rw [← hs3, ← mul_pow] at hp'
      exact (pow_le_pow_iff_left₀ hxr.le (mul_nonneg (by linarith) hgap) (by decide : 3 ≠ 0)).1 hp'
    have hrel : 1 / (s + 1) ≤ ((z : ℝ) - x) / z := (div_le_div_iff₀ (by linarith) hzr).2 (by linarith)
    have hlog := Real.log_le_sub_one_of_pos (div_pos hxr hzr)
    rw [Real.log_div hxr.ne' hzr.ne'] at hlog
    rw [sub_div, div_self hzr.ne'] at hrel
    have hcoef : 1 ≤ 2 * s * (1 / (s + 1)) := by rw [mul_one_div, le_div_iff₀ (by linarith)]; linarith
    exact hcoef.trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
  have htel (m : ℕ) : (∑ i ∈ Finset.range m, (L (i + 2) - L i)) = L m + L (m + 1) - L 0 - L 1 := by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  have hcoef : 0 ≤ 2 * X ^ (1 / 3 : ℝ) := by positivity
  have hcard : (W.card : ℝ) ≤ 4 * X ^ (1 / 3 : ℝ) * Real.log X := by
    calc (W.card : ℝ) = ∑ _ ∈ W, (1 : ℝ) := by simp
      _ ≤ ∑ i ∈ W, 2 * X ^ (1 / 3 : ℝ) * (L (i + 2) - L i) :=
          Finset.sum_le_sum fun i hi => hLstep (Finset.mem_filter.mp hi).2
      _ ≤ ∑ i ∈ Finset.range N, 2 * X ^ (1 / 3 : ℝ) * (L (i + 2) - L i) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ =>
            mul_nonneg hcoef (sub_nonneg.2 (hL (by omega)))
      _ = 2 * X ^ (1 / 3 : ℝ) * (L N + L (N + 1) - L 0 - L 1) := by rw [← Finset.mul_sum, htel]
      _ ≤ 2 * X ^ (1 / 3 : ℝ) * (2 * Real.log X) := mul_le_mul_of_nonneg_left
          (by linarith [min_le_right (Real.log (a N : ℝ)) (Real.log X),
            min_le_right (Real.log (a (N + 1) : ℝ)) (Real.log X), hLnn 0, hLnn 1]) hcoef
      _ = _ := by ring
  change ({i : ℕ | P i}.encard : EReal) ≤ _
  rw [hset, Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe,
    ← EReal.coe_ennreal_toReal (by simp : (W.card : ℝ≥0∞) ≠ ⊤)]
  exact EReal.coe_le_coe (by simpa using hcard)
