import OMAStatements.S_oeis_a007598
import Mathlib

/-!
Peter Bala's reciprocal Fibonacci identities (OEIS A007598).
The fixed sums telescope by Cassini's and Catalan's identities. For the
family we use Sela Fried's odd-shift argument, including cancellation
among the terms with a negative Fibonacci index.
-/

open Filter Finset
open scoped Topology

noncomputable section

namespace OMA.A007598

private def F (n : ℕ) : ℝ := Nat.fib n

private def Z (n : ℤ) : ℝ := Int.fib n

private theorem Z_nat (n : ℕ) : Z n = F n := by simp [Z, F]

private theorem F_pos {n : ℕ} (h : 0 < n) : 0 < F n := by
  unfold F
  exact_mod_cast Nat.fib_pos.mpr h

private theorem F_rec (n : ℕ) : F (n + 2) = F n + F (n + 1) := by
  simp [F, Nat.fib_add_two]

private theorem F_mono : Monotone F := fun _ _ h => by
  unfold F
  exact_mod_cast Nat.fib_mono h

private theorem Z_catalan (m s : ℤ) :
    Z (m + s) ^ 2 - Z m * Z (m + 2 * s) = (-1 : ℝ) ^ m.natAbs * Z s ^ 2 := by
  unfold Z
  exact_mod_cast Int.fib_add_sq_sub_fib_mul_fib_add_two_mul m s

private theorem F_catalan (m s : ℕ) :
    F (m + s) ^ 2 - F m * F (m + 2 * s) = (-1 : ℝ) ^ m * F s ^ 2 := by
  have h := Z_catalan (m : ℤ) (s : ℤ)
  have h1 : (m:ℤ) + (s:ℤ) = ((m+s:ℕ):ℤ) := by push_cast; rfl
  have h2 : (m:ℤ) + 2*(s:ℤ) = ((m+2*s:ℕ):ℤ) := by push_cast; rfl
  simpa only [h1, h2, Z_nat, Int.natAbs_natCast] using h

private theorem telescope (f : ℕ → ℝ) (j : ℕ) {l : ℝ}
    (h : Tendsto f atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => ∑ i ∈ range n, (f i - f (i + j))) atTop
      (𝓝 ((∑ i ∈ range j, f i) - ∑ _i ∈ range j, l)) := by
  have hfinite : Tendsto (fun n : ℕ => ∑ i ∈ range j, f (n + i)) atTop
      (𝓝 (∑ _i ∈ range j, l)) :=
    tendsto_finsetSum _ fun i _ => h.comp (tendsto_add_atTop_nat i)
  have heq (n : ℕ) : (∑ i ∈ range n, (f i - f (i + j))) =
      (∑ i ∈ range j, f i) - ∑ i ∈ range j, f (n + i) := by
    rw [sum_sub_distrib]
    have h1 := sum_range_add f j n
    have h2 := sum_range_add f n j
    simp_rw [Nat.add_comm j] at h1
    linear_combination h1 - h2
  simpa only [heq] using tendsto_const_nhds.sub hfinite

private def B (i : ℕ) : ℝ := 1 / (F (i + 1) * F (i + 3))

private def V (i : ℕ) : ℝ := 1 / (F (i + 1) * F (i + 2))

private def R (i : ℕ) : ℝ := F (i + 2) / F (i + 1)

private def D (i : ℕ) : ℝ := (-1 : ℝ) ^ (i + 1) * B i

private theorem B_nonneg (i : ℕ) : 0 ≤ B i :=
  (one_div_pos.mpr (mul_pos (F_pos (by omega)) (F_pos (by omega)))).le

private theorem F_top : Tendsto F atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (5 : ℕ)] with i hi
  unfold F
  exact_mod_cast Nat.le_fib_self hi

private theorem V_zero : Tendsto V atTop (𝓝 0) := by
  have h : Tendsto (fun i : ℕ => F (i+1) * F (i+2)) atTop atTop :=
    Tendsto.atTop_mul_atTop₀ (F_top.comp (tendsto_add_atTop_nat 1))
      (F_top.comp (tendsto_add_atTop_nat 2))
  refine h.inv_tendsto_atTop.congr fun i => ?_
  simp only [Pi.inv_apply, V, one_div]

private theorem B_diff (i : ℕ) : B i = V i - V (i + 1) := by
  unfold B V
  have h1 := F_pos (n := i+1) (by omega)
  have h2 := F_pos (n := i+2) (by omega)
  have h3 := F_pos (n := i+3) (by omega)
  have h := F_rec (i + 1)
  field_simp [h1.ne', h2.ne', h3.ne']
  linear_combination -h

private theorem B_sum (j : ℕ) : HasSum (fun i => B (i+j)) (V j) := by
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun i => B_nonneg (i+j)) _).mpr ?_
  have h := telescope (fun i => V (i+j)) 1 (V_zero.comp (tendsto_add_atTop_nat j))
  convert h using 1
  · ext n
    apply sum_congr rfl
    intro i _
    rw [B_diff, show i + j + 1 = i + 1 + j by omega]
  · simp

private theorem D_diff (i : ℕ) : D i = R i - R (i + 2) := by
  have hc := F_catalan (i + 1) 1
  have h := F_rec (i + 2)
  have hc' : F (i + 2)^2 - F (i + 1) * F (i + 3) = (-1:ℝ)^(i+1) := by
    simpa [F, Nat.fib_one] using hc
  have h1 := F_pos (n := i+1) (by omega)
  have h3 := F_pos (n := i+3) (by omega)
  unfold D B R
  field_simp [h1.ne', h3.ne']
  linear_combination -hc' + F (i+1) * h - F (i+2) * F_rec (i+1)

private theorem D_sum (j : ℕ) :
    HasSum (fun i => D (i+j)) (R j + R (j+1) - 2 * Real.goldenRatio) := by
  have hnorm : Summable (fun i => ‖D (i+j)‖) := by
    simpa only [D, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul, abs_of_nonneg (B_nonneg _)] using (B_sum j).summable
  refine (hasSum_iff_tendsto_nat_of_summable_norm hnorm).mpr ?_
  have hR : Tendsto R atTop (𝓝 Real.goldenRatio) :=
    tendsto_fib_succ_div_fib_atTop.comp (tendsto_add_atTop_nat 1)
  have h := telescope (fun i => R (i+j)) 2 (hR.comp (tendsto_add_atTop_nat j))
  convert h using 1
  · ext n
    apply sum_congr rfl
    intro i _
    rw [D_diff, show i + j + 2 = i + 2 + j by omega]
  · simp [sum_range_succ]
    ring

private theorem reciprocal_gap (i : ℕ) :
    1 / (F (i+1) * F (i+5)) = (B i + B (i+2)) / 3 := by
  have h1 := F_pos (n := i+1) (by omega)
  have h3 := F_pos (n := i+3) (by omega)
  have h5 := F_pos (n := i+5) (by omega)
  have ha := F_rec (i+1)
  have hb := F_rec (i+2)
  have hc := F_rec (i+3)
  unfold B
  field_simp [h1.ne', h3.ne', h5.ne']
  linear_combination ha - hb - hc

private theorem reciprocal_pair (x t : ℝ) (hx : x ≠ 0) (ht : t^2 = 1)
    (hp : x+t ≠ 0) (hm : x-t ≠ 0) :
    1 / (x - 1/x) = (1/(x+t) + 1/(x-t))/2 := by
  have hmul : (x+t)*(x-t) = x^2-1 := by linear_combination -ht
  have he : x-1/x = (x^2-1)/x := by field_simp [hx]
  rw [he, ← hmul]
  field_simp [hx, hp, hm]
  ring

private theorem fixed_term (i : ℕ) :
    1 / (OMA.S_oeis_a007598.a (i+3) - 1 / OMA.S_oeis_a007598.a (i+3)) =
      (B (i+1) + (B i + B (i+2)) / 3) / 2 := by
  have h1 := F_pos (n := i+1) (by omega)
  have h2 := F_pos (n := i+2) (by omega)
  have h3 := F_pos (n := i+3) (by omega)
  have h4 := F_pos (n := i+4) (by omega)
  have h5 := F_pos (n := i+5) (by omega)
  have hA : F (i+3)^2 + (-1:ℝ)^(i+3) = F (i+2)*F (i+4) := by
    have h := F_catalan (i+2) 1
    norm_num [F, pow_succ] at h ⊢
    linear_combination h
  have hB : F (i+3)^2 - (-1:ℝ)^(i+3) = F (i+1)*F (i+5) := by
    have h := F_catalan (i+1) 2
    norm_num [F, pow_succ] at h ⊢
    linear_combination h
  have hp : ((-1:ℝ)^(i+3))^2 = 1 := by rw [← pow_mul]; simp
  change 1 / (F (i+3)^2 - 1 / F (i+3)^2) = _
  rw [← reciprocal_gap]
  unfold B
  rw [← hA, ← hB]
  exact reciprocal_pair _ _ (pow_ne_zero _ h3.ne') hp
    (hA ▸ (mul_pos h2 h4).ne') (hB ▸ (mul_pos h1 h5).ne')

private theorem fixed_term_signed (i : ℕ) :
    (-1:ℝ)^(i+3) / (OMA.S_oeis_a007598.a (i+3) - 1 / OMA.S_oeis_a007598.a (i+3)) =
      (-D (i+1) + (D i + D (i+2)) / 3) / 2 := by
  rw [← mul_one_div, fixed_term]
  unfold D
  rw [show i + 3 = (i + 1) + 2 by omega, pow_add,
    show i + 1 + 1 = (i+1) + 1 by rfl, pow_succ]
  norm_num [show i + 2 + 1 = i + 1 + 2 by omega, pow_add]
  ring

private theorem fixed_sums :
    HasSum (fun i : ℕ => 1/(OMA.S_oeis_a007598.a (i+3) -
      1/OMA.S_oeis_a007598.a (i+3))) (4/9 : ℝ) ∧
    HasSum (fun i : ℕ => (-1:ℝ)^(i+3)/(OMA.S_oeis_a007598.a (i+3) -
      1/OMA.S_oeis_a007598.a (i+3))) (-(10 - 3 * Real.sqrt 5)/18) := by
  constructor
  · simp_rw [fixed_term]
    have h := ((B_sum 1).add (((B_sum 0).add (B_sum 2)).div_const 3)).div_const 2
    have hs : (V 1 + (V 0 + V 2) / 3) / 2 = 4 / 9 := by
      norm_num [V, F, Nat.fib]
    simpa only [hs, Nat.add_zero] using h
  · simp_rw [fixed_term_signed]
    have h := ((D_sum 1).neg.add (((D_sum 0).add (D_sum 2)).div_const 3)).div_const 2
    have hs : (-(R 1 + R (1+1) - 2 * Real.goldenRatio) +
        ((R 0 + R (0+1) - 2 * Real.goldenRatio) +
          (R 2 + R (2+1) - 2 * Real.goldenRatio))/3)/2 =
        -(10 - 3 * Real.sqrt 5)/18 := by
      norm_num [R, F, Nat.fib, Real.goldenRatio]
      ring
    simpa only [hs, Nat.add_zero] using h

private theorem Z_add (m n : ℤ) :
    Z (m+n) = Z (m-1)*Z n + Z m*Z (n+1) := by
  unfold Z
  exact_mod_cast Int.fib_add m n

private theorem Z_neg_nat (n : ℕ) : Z (-(n:ℤ)) = (-1:ℝ)^(n+1)*F n := by
  unfold Z F
  exact_mod_cast Int.fib_neg_natCast n

private theorem Z_ne {n : ℤ} (h : n ≠ 0) : Z n ≠ 0 := by
  unfold Z
  exact_mod_cast fun hz => h (Int.fib_eq_zero.mp hz)

private def G (s : ℕ) (m : ℤ) : ℝ := 1 / (Z m * Z (m+s))

private theorem odd_gap (s : ℕ) (hs : Odd s) (m : ℤ) :
    Z s * (Z (m+2*(s:ℤ)) - Z m) = Z (2*(s:ℤ))*Z (m+s) := by
  have hplus := Z_add (m+s) s
  have hminus := Z_add (m+s) (-(s:ℤ))
  have hdouble := Z_add s s
  have hEven : Even (s+1) := by obtain ⟨k,hk⟩ := hs; exact ⟨k+1,by omega⟩
  have hneg : Z (-(s:ℤ)) = Z s := by rw [Z_neg_nat, hEven.neg_one_pow, one_mul, Z_nat]
  have hp : 0 < s := hs.pos
  have hneg' : Z (-(s:ℤ)+1) = -Z ((s:ℤ)-1) := by
    have hcast : ((s-1 : ℕ) : ℤ) = (s:ℤ)-1 := by omega
    rw [show -(s:ℤ)+1 = -((s-1 : ℕ):ℤ) by omega, Z_neg_nat,
      show s-1+1=s by omega, hs.neg_one_pow, neg_one_mul, ← hcast, Z_nat]
  rw [show m + s + s = m+2*(s:ℤ) by ring] at hplus
  rw [show m + s + -(s:ℤ) = m by ring, hneg, hneg'] at hminus
  rw [show (s:ℤ) + s = 2*(s:ℤ) by ring] at hdouble
  linear_combination Z s * (hplus - hminus) - Z (m+s) * hdouble

private theorem family_term (s : ℕ) (hs : Odd s) (i : ℕ) (hi : i+1 ≠ s) :
    1 / (F (i+1)^2 + (-1:ℝ)^(i+1)*F s^2) =
      (Z s / Z (2*(s:ℤ))) * (G s ((i:ℤ)+1-s) - G s ((i:ℤ)+1)) := by
  let m : ℤ := (i:ℤ)+1-s
  have hm0 : m ≠ 0 := by dsimp [m]; omega
  have hm1 : m+s = (i:ℤ)+1 := by dsimp [m]; ring
  have hm2 : m+2*(s:ℤ) = (i:ℤ)+1+s := by dsimp [m]; ring
  have h0 := Z_ne hm0
  have h1 := Z_ne (show m+s ≠ 0 by rw [hm1]; omega)
  have h2 := Z_ne (show m+2*(s:ℤ) ≠ 0 by rw [hm2]; omega)
  have h3 := Z_ne (show (2:ℤ)*s ≠ 0 by have := hs.pos; omega)
  have hc := Z_catalan m s
  have hsign : (-1:ℝ)^m.natAbs = -((-1:ℝ)^(i+1)) := by
    have hmParity : m.natAbs % 2 ≠ (i+1) % 2 := by
      obtain ⟨k,hk⟩ := hs
      dsimp [m]
      omega
    rw [neg_one_pow_eq_pow_mod_two m.natAbs, neg_one_pow_eq_pow_mod_two (i+1)]
    have hr : m.natAbs % 2 < 2 := Nat.mod_lt _ (by decide)
    have hr' : (i+1) % 2 < 2 := Nat.mod_lt _ (by decide)
    interval_cases (m.natAbs % 2) <;> interval_cases ((i+1) % 2) <;> norm_num at *
  have hF : Z (m+s) = F (i+1) := by
    rw [hm1, ← Nat.cast_add_one, Z_nat]
  rw [hsign, hF, Z_nat] at hc
  have heq : F (i+1)^2 + (-1:ℝ)^(i+1)*F s^2 =
      Z m * Z (m+2*(s:ℤ)) := by linear_combination hc
  rw [heq]
  change _ = _ * (G s m - G s ((i:ℤ)+1))
  rw [← hm1]
  unfold G
  rw [show m + s + s = m+2*(s:ℤ) by ring]
  field_simp [h0, h1, h2, h3]
  linear_combination -(odd_gap s hs m)

private theorem head_sum (s : ℕ) (hs : Odd s) :
    (∑ i ∈ range s, G s ((i:ℤ)+1-s)) = 0 := by
  have hp := hs.pos
  have hsucc : s = (s-1)+1 := by omega
  nth_rw 1 [hsucc]
  rw [sum_range_succ]
  have hz : G s (((s-1:ℕ):ℤ)+1-s) = 0 := by
    rw [show (((s-1:ℕ):ℤ)+1-s) = 0 by omega]
    simp [G, Z]
  rw [hz, add_zero]
  let f (i : ℕ) := G s ((i:ℤ)+1-s)
  change (∑ i ∈ range (s-1), f i) = 0
  have hpair (i : ℕ) (hi : i ∈ range (s-1)) : f (s-1-1-i) = -f i := by
    have hi' := mem_range.mp hi
    let d := s-1-i
    let e := i+1
    have hd : 0 < d := by dsimp [d]; omega
    have he : 0 < e := by dsimp [e]; omega
    have hds : d+e = s := by dsimp [d,e]; omega
    have hd' : (((s-1-1-i:ℕ):ℤ)+1-s) = -(e:ℤ) := by dsimp [e]; omega
    have he' : (i:ℤ)+1-s = -(d:ℤ) := by dsimp [d]; omega
    have hde : -(d:ℤ)+s = (e:ℤ) := by omega
    have hed : -(e:ℤ)+s = (d:ℤ) := by omega
    dsimp [f, G]
    rw [hd', he', hed, hde, Z_neg_nat, Z_neg_nat, Z_nat, Z_nat]
    have hsign : (-1:ℝ)^(d+1) * (-1:ℝ)^(e+1) = -1 := by
      rw [← pow_add, show d+1+(e+1) = s+2 by omega, pow_add, hs.neg_one_pow]
      norm_num
    have hflip : (-1:ℝ)^(e+1) = -((-1:ℝ)^(d+1)) := by
      rcases neg_one_pow_eq_or ℝ (d+1) with h | h <;> rw [h] at hsign ⊢ <;>
        linarith
    rw [hflip]
    ring
  have hsum : (∑ i ∈ range (s-1), f (s-1-1-i)) = -(∑ i ∈ range (s-1), f i) := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl hpair
  rw [sum_range_reflect] at hsum
  linarith

private theorem G_summable (s : ℕ) (hs : 0 < s) :
    Summable (fun i : ℕ => G s ((i:ℤ)+1)) := by
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_nonneg_of_le _ _ (B_sum 0).summable
  · intro i
    unfold G
    rw [show ((i+1:ℕ):ℤ)+1 = ((i+2:ℕ):ℤ) by omega, ← Nat.cast_add, Z_nat, Z_nat]
    exact (one_div_pos.mpr (mul_pos (F_pos (by omega)) (F_pos (by omega)))).le
  · intro i
    unfold G B
    rw [show ((i+1:ℕ):ℤ)+1 = ((i+2:ℕ):ℤ) by omega, ← Nat.cast_add, Z_nat, Z_nat]
    apply one_div_le_one_div_of_le (mul_pos (F_pos (by omega)) (F_pos (by omega)))
    exact mul_le_mul (F_mono (by omega)) (F_mono (by omega)) (F_pos (by omega)).le
      (F_pos (by omega)).le

private theorem family_sum (s : ℕ) (hs : Odd s) :
    HasSum (fun i : ℕ => if i+1=s then 0 else
      1 / (F (i+1)^2 + (-1:ℝ)^(i+1)*F s^2)) (1/Z (2*(s:ℤ))^2) := by
  let g (i : ℕ) := G s ((i:ℤ)+1)
  let g' (i : ℕ) := G s ((i:ℤ)+1-s)
  have hp := hs.pos
  have hg : Summable g := G_summable s hp
  have heq (i : ℕ) : g' (i+s) = g i := by
    dsimp [g', g]
    congr 1
    ring
  have hg' : HasSum g' (∑' i, g i) := by
    have h : HasSum (fun i => g' (i+s)) (∑' i, g i) := by
      simpa only [heq] using hg.hasSum
    have hh := (hasSum_nat_add_iff (f := g') (g := ∑' i, g i) s).mp h
    simpa only [g', head_sum s hs, add_zero] using hh
  let c := Z s / Z (2*(s:ℤ))
  have hz : HasSum (fun i => c * (g' i - g i)) 0 := by
    simpa only [sub_self, mul_zero] using (hg'.sub hg.hasSum).mul_left c
  have hc : c * G s s = 1/Z (2*(s:ℤ))^2 := by
    have h1 := Z_ne (show (s:ℤ) ≠ 0 by omega)
    have h2 := Z_ne (show (2:ℤ)*s ≠ 0 by omega)
    dsimp [c, G]
    rw [show (s:ℤ)+s = 2*(s:ℤ) by ring]
    field_simp [h1,h2]
  have hsng : HasSum (fun i : ℕ => if i+1=s then c * G s s else 0) (c * G s s) := by
    have hh : HasSum (fun i : ℕ => if i = s-1 then c * G s s else 0) (c * G s s) :=
      hasSum_ite_eq _ _
    simpa only [show ∀ i : ℕ, i+1=s ↔ i=s-1 by omega] using hh
  rw [← hc]
  convert hz.add hsng using 1
  · ext i
    by_cases hi : i+1=s
    · have hi' : (i:ℤ)+1=s := by exact_mod_cast hi
      simp [hi, g', g, hi', G, Z, c]
    · simpa only [hi, if_false, add_zero] using family_term s hs i hi
  · simp

end OMA.A007598

theorem OMA.solution : type_of% @OMA.S_oeis_a007598.main := by
  obtain ⟨h1,h2⟩ := OMA.A007598.fixed_sums
  refine ⟨h1,h2,?_⟩
  intro k
  have h := OMA.A007598.family_sum (2*k+1) (odd_two_mul_add_one k)
  have he : ((2:ℤ) * ((2*k+1:ℕ):ℤ)) = ((4*k+2:ℕ):ℤ) := by push_cast; ring
  simpa only [he, OMA.A007598.Z_nat, OMA.A007598.F, OMA.S_oeis_a007598.a] using h
