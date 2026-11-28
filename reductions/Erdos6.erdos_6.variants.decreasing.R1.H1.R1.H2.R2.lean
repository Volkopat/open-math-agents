import OMAReductions.R_Erdos6_erdos_6_variants_decreasing_R1_H1_R1
import Mathlib

/- Second reduction of the primitive-character mean (step H2 of #8656).
H1 is the Siegel-Walfisz bound with a logarithmic saving and H2 is Vaughan's cumulative
mean-value theorem; both are stated verbatim as in the merged reduction
ElliottHalberstamConjecture.elliott_halberstam.variants.bombieri_vinogradov.R1.H1.R1.H2.R1
by @marcusbuffett (#6059). The scalar cutoff and reciprocal Abel summation lemmas below are
copied from that file (namespace renamed), which adapts Jonas Whidden (@kimihiro64),
Bombieri-Vinogradov in Lean, commit 7a1748306e026825ed6a5555516cc2f28989b2ac, Apache-2.0.
The main proof splits the conductors at (log x)^(A+3) and takes the moduli up to
sqrt x / (log x)^(A+3). -/
section
namespace E6BVAux.RealAnalysis


theorem floor_half_bounds {T : Real} (hT : 2 <= T) :
    And (1 <= Nat.floor T)
      (And ((Nat.floor T : Real) <= T) (T / 2 <= (Nat.floor T : Real))) := by
  have hOne : (1 : Real) <= T := by linarith
  have hRaw : (((1 : Nat) : Real) <= T) := by simpa only [Nat.cast_one] using hOne
  have hUpper : (Nat.floor T : Real) <= T := Nat.floor_le (show 0 <= T by linarith)
  refine And.intro (Nat.le_floor hRaw) (And.intro hUpper ?_)
  have hFloor := Nat.lt_floor_add_one T
  linarith

end E6BVAux.RealAnalysis
end

section
namespace E6BVAux.RealAnalysis


theorem polylog_floor_cutoff_bounds {X B : Real}
    (hX : Real.exp (4 : Real) <= X) (hB : 1 <= B) :
    And (1 <= Nat.floor ((Real.log X) ^ B))
      (And ((Nat.floor ((Real.log X) ^ B) : Real) <= (Real.log X) ^ B)
        ((Real.log X) ^ B / 2 <= (Nat.floor ((Real.log X) ^ B) : Real))) := by
  have hXPos : 0 < X := (Real.exp_pos (4 : Real)).trans_le hX
  have hLogFour : 4 <= Real.log X := (Real.le_log_iff_exp_le hXPos).mpr hX
  have hLogOne : 1 <= Real.log X := by linarith
  have hPower : Real.log X <= (Real.log X) ^ B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hLogOne hB
  have hTwo : 2 <= (Real.log X) ^ B := by linarith
  exact floor_half_bounds hTwo

end E6BVAux.RealAnalysis
end

section
namespace E6BVAux.RealAnalysis


theorem exists_bounded_half_power_gap {theta : Real} (hTheta : theta < 1 / 2) :
    exists delta : Real, And (0 < delta) (And (delta <= 1 / 6) (theta + delta <= 1 / 2)) := by
  have hPos : 0 < min (1 / 6 : Real) (1 / 2 - theta) :=
    lt_min (by linarith) (by linarith)
  have hCap := min_le_left (1 / 6 : Real) (1 / 2 - theta)
  have hGap := min_le_right (1 / 6 : Real) (1 / 2 - theta)
  exact Exists.intro (min (1 / 6 : Real) (1 / 2 - theta))
    (And.intro hPos (And.intro hCap (by linarith)))

end E6BVAux.RealAnalysis
end

section
namespace E6BVAux.RealAnalysis


theorem eventually_log_rpow_le_rpow (b : Real) {delta : Real} (hDelta : 0 < delta) :
    Filter.Eventually (fun X : Real => (Real.log X) ^ b <= X ^ delta) Filter.atTop := by
  have hBound := (_root_.isLittleO_log_rpow_rpow_atTop b hDelta).def
    (show (0 : Real) < 1 from zero_lt_one)
  refine (hBound.and (Filter.eventually_ge_atTop (1 : Real))).mono ?_
  intro X h
  have hX : 0 <= X := zero_le_one.trans h.2
  have hLog : 0 <= (Real.log X) ^ b := Real.rpow_nonneg (Real.log_nonneg h.2) b
  have hPower : 0 <= X ^ delta := Real.rpow_nonneg hX delta
  simpa only [Real.norm_of_nonneg hLog, Real.norm_of_nonneg hPower, one_mul] using h.1

end E6BVAux.RealAnalysis
end

section
namespace E6BVAux.RealAnalysis


theorem sum_Icc_le_sum_Icc_add_sum_Ioc (F : Nat -> Real) (hF : forall n, 0 <= F n)
    (R Q : Nat) :
    Finset.sum (Finset.Icc 1 Q) F <=
      Finset.sum (Finset.Icc 1 R) F + Finset.sum (Finset.Ioc R Q) F := by
  have hCover : forall n, (Finset.Icc 1 Q : Set Nat) n ->
      ((Union.union (Finset.Icc 1 R) (Finset.Ioc R Q) : Finset Nat) : Set Nat) n := by
    intro n hn
    have hAlternatives : Or ((Finset.Icc 1 R : Set Nat) n)
        ((Finset.Ioc R Q : Set Nat) n) := by
      by_cases hnR : n <= R
      case pos =>
        exact Or.inl (Finset.mem_Icc.mpr (And.intro (Finset.mem_Icc.mp hn).1 hnR))
      case neg =>
        exact Or.inr (Finset.mem_Ioc.mpr (And.intro (Nat.lt_of_not_ge hnR)
          (Finset.mem_Icc.mp hn).2))
    exact (Finset.mem_union (a := n) (s := Finset.Icc 1 R)
      (t := Finset.Ioc R Q)).mpr hAlternatives
  have hDisjoint : Disjoint (Finset.Icc 1 R) (Finset.Ioc R Q) :=
    Finset.disjoint_left.mpr (fun _ hn hnTail =>
      (Nat.not_lt_of_ge (Finset.mem_Icc.mp hn).2) (Finset.mem_Ioc.mp hnTail).1)
  calc
    Finset.sum (Finset.Icc 1 Q) F <=
        Finset.sum (Union.union (Finset.Icc 1 R) (Finset.Ioc R Q)) F :=
      Finset.sum_le_sum_of_subset_of_nonneg hCover (fun n _ _ => hF n)
    _ = Finset.sum (Finset.Icc 1 R) F + Finset.sum (Finset.Ioc R Q) F :=
      Finset.sum_union hDisjoint

end E6BVAux.RealAnalysis
end

section
namespace E6BVAux.RealAnalysis


theorem quadratic_div_boundary_le (a b c q r : Real)
    (ha : 0 <= a) (hr : 0 < r) (hrq : r <= q) :
    (a + b * q + c * q ^ 2) / q <= a / r + b + c * q := by
  have hq : 0 < q := hr.trans_le hrq
  have hqZero : Ne q 0 := by positivity
  have hIdentity : (a + b * q + c * q ^ 2) / q = a / q + b + c * q := by
    field_simp
  have hConstant : a / q <= a / r := div_le_div_of_nonneg_left ha hr hrq
  rw [hIdentity]
  linarith

end E6BVAux.RealAnalysis
end

section
namespace E6BVAux.RealAnalysis


theorem quadratic_div_reciprocal_kernel_le (a b c k : Real) (hc : 0 <= c) (hk : 0 < k) :
    (a + b * k + c * k ^ 2) / (k * (k + 1)) <=
      a / (k * (k + 1)) + b / (k + 1) + c := by
  have hkZero : Ne k 0 := by positivity
  have hkOne : Ne (k + 1) 0 := by positivity
  have hIdentity : (a + b * k + c * k ^ 2) / (k * (k + 1)) =
      a / (k * (k + 1)) + b / (k + 1) + c - c / (k + 1) := by
    field_simp
    ring
  have hRemainder : 0 <= c / (k + 1) := by positivity
  rw [hIdentity]
  linarith

end E6BVAux.RealAnalysis
end

section
namespace E6BVAux.RealAnalysis


theorem mul_sub_reciprocal_eq_div_mul (a x : Real)
    (hx : Ne x 0) (hxOne : Ne (x + 1) 0) :
    a * (1 / x - 1 / (x + 1)) = a / (x * (x + 1)) := by
  field_simp
  ring

end E6BVAux.RealAnalysis
end

section
namespace E6BVAux.RealAnalysis


theorem sum_reciprocal_product_Ico {R Q : Nat} (hR : 1 <= R) (hRQ : R <= Q) :
    Finset.sum (Finset.Ico R Q) (fun k => 1 / ((k : Real) * ((k : Real) + 1))) =
      1 / (R : Real) - 1 / (Q : Real) := by
  induction Q, hRQ using Nat.le_induction with
  | base => simp
  | succ Q hRQ ih =>
    have hQ : 0 < Q := Nat.lt_of_lt_of_le Nat.zero_lt_one (hR.trans hRQ)
    have hQReal : (0 : Real) < (Q : Real) := Nat.cast_pos.mpr hQ
    have hDiff : 1 / (Q : Real) - 1 / ((Q : Real) + 1) =
        1 / ((Q : Real) * ((Q : Real) + 1)) := by
      simpa only [one_mul] using mul_sub_reciprocal_eq_div_mul 1 (Q : Real)
        (by positivity) (by positivity)
    rw [Finset.sum_Ico_succ_top hRQ, ih, <- hDiff]
    simp only [Nat.cast_add, Nat.cast_one]
    ring


theorem sum_reciprocal_product_Ico_le {R Q : Nat} (hR : 1 <= R) (hRQ : R <= Q) :
    Finset.sum (Finset.Ico R Q) (fun k => 1 / ((k : Real) * ((k : Real) + 1))) <=
      1 / (R : Real) := by
  rw [sum_reciprocal_product_Ico hR hRQ]
  have hInv : (0 : Real) <= 1 / (Q : Real) := by positivity
  linarith

end E6BVAux.RealAnalysis
end

section
namespace E6BVAux.RealAnalysis

theorem sum_one_div_Icc_le_one_add_log (Q : Nat) :
    Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real)) <=
      1 + Real.log (Q : Real) := by
  calc
    Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real)) = (harmonic Q : Real) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast, one_div]
    _ <= 1 + Real.log (Q : Real) := harmonic_le_one_add_log Q

end E6BVAux.RealAnalysis
end

section
namespace E6BVAux.RealAnalysis


theorem sum_one_div_add_one_Ico_le {R Q : Nat} (hR : 1 <= R) :
    Finset.sum (Finset.Ico R Q) (fun k => 1 / ((k : Real) + 1)) <=
      1 + Real.log (Q : Real) := by
  have hSubset : forall k, (Finset.Ico R Q : Set Nat) k ->
      (Finset.Icc 1 Q : Set Nat) k := by
    intro k hk
    exact Finset.mem_Icc.mpr (And.intro (hR.trans (Finset.mem_Ico.mp hk).1)
      (Finset.mem_Ico.mp hk).2.le)
  calc
    Finset.sum (Finset.Ico R Q) (fun k => 1 / ((k : Real) + 1)) <=
        Finset.sum (Finset.Ico R Q) (fun k => 1 / (k : Real)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkPos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one
        (hR.trans (Finset.mem_Ico.mp hk).1)
      have hkReal : (0 : Real) < (k : Real) := Nat.cast_pos.mpr hkPos
      exact one_div_le_one_div_of_le hkReal (by linarith)
    _ <= Finset.sum (Finset.Icc 1 Q) (fun k => 1 / (k : Real)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hSubset (fun k _ _ => by positivity)
    _ <= 1 + Real.log (Q : Real) := sum_one_div_Icc_le_one_add_log Q

end E6BVAux.RealAnalysis
end

section
namespace E6BVAux.RealAnalysis


theorem sum_quadratic_div_reciprocal_kernel_le (a b c : Real)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c) {R Q : Nat}
    (hR : 1 <= R) (hRQ : R <= Q) :
    Finset.sum (Finset.Ico R Q)
        (fun k => (a + b * (k : Real) + c * (k : Real) ^ 2) /
          ((k : Real) * ((k : Real) + 1))) <=
      a / (R : Real) + b * (1 + Real.log (Q : Real)) + c * (Q : Real) := by
  have hCard : ((Finset.Ico R Q).card : Real) <= (Q : Real) := by
    rw [Nat.card_Ico]
    exact Nat.cast_le.mpr (Nat.sub_le Q R)
  have hConstant := mul_le_mul_of_nonneg_left
    (sum_reciprocal_product_Ico_le hR hRQ) ha
  have hLinear := mul_le_mul_of_nonneg_left
    (sum_one_div_add_one_Ico_le (Q := Q) hR) hb
  have hQuadratic := mul_le_mul_of_nonneg_right hCard hc
  calc
    Finset.sum (Finset.Ico R Q)
        (fun k => (a + b * (k : Real) + c * (k : Real) ^ 2) /
          ((k : Real) * ((k : Real) + 1))) <=
        Finset.sum (Finset.Ico R Q)
          (fun k => a / ((k : Real) * ((k : Real) + 1)) +
            b / ((k : Real) + 1) + c) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkPos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one
        (hR.trans (Finset.mem_Ico.mp hk).1)
      exact quadratic_div_reciprocal_kernel_le a b c (k : Real) hc
        (Nat.cast_pos.mpr hkPos)
    _ = a * Finset.sum (Finset.Ico R Q)
          (fun k => 1 / ((k : Real) * ((k : Real) + 1))) +
        b * Finset.sum (Finset.Ico R Q) (fun k => 1 / ((k : Real) + 1)) +
        ((Finset.Ico R Q).card : Real) * c := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.mul_sum, mul_one_div]
    _ <= a * (1 / (R : Real)) + b * (1 + Real.log (Q : Real)) + (Q : Real) * c :=
      add_le_add (add_le_add hConstant hLinear) hQuadratic
    _ = a / (R : Real) + b * (1 + Real.log (Q : Real)) + c * (Q : Real) := by
      rw [mul_one_div]
      ring

end E6BVAux.RealAnalysis
end

section
namespace E6BVAux.RealAnalysis


theorem sum_Ioc_mul_eq_abel (F g : Nat -> Real) {R Q : Nat} (hRQ : R <= Q) :
    Finset.sum (Finset.Ioc R Q) (fun n => F n * g n) =
      Finset.sum (Finset.Icc 1 Q) F * g Q -
        Finset.sum (Finset.Icc 1 R) F * g R +
          Finset.sum (Finset.Ico R Q)
            (fun k => Finset.sum (Finset.Icc 1 k) F * (g k - g (k + 1))) := by
  induction Q, hRQ using Nat.le_induction with
  | base => simp
  | succ Q hRQ ih =>
    rw [Finset.sum_Ioc_succ_top hRQ, Finset.sum_Ico_succ_top hRQ,
      Finset.sum_Icc_succ_top (Nat.succ_pos Q), ih]
    ring

end E6BVAux.RealAnalysis
end

section
namespace E6BVAux.RealAnalysis


theorem sum_Ioc_div_eq_abel (F : Nat -> Real) {R Q : Nat}
    (hR : 1 <= R) (hRQ : R <= Q) :
    Finset.sum (Finset.Ioc R Q) (fun n => F n / (n : Real)) =
      Finset.sum (Finset.Icc 1 Q) F / (Q : Real) -
        Finset.sum (Finset.Icc 1 R) F / (R : Real) +
          Finset.sum (Finset.Ico R Q)
            (fun k => Finset.sum (Finset.Icc 1 k) F / ((k : Real) * ((k : Real) + 1))) := by
  have hAbel := sum_Ioc_mul_eq_abel F (fun n => 1 / (n : Real)) hRQ
  simp only [mul_one_div] at hAbel
  rw [hAbel]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkPos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one
    (hR.trans (Finset.mem_Ico.mp hk).1)
  have hkReal : (0 : Real) < (k : Real) := Nat.cast_pos.mpr hkPos
  simp only [Nat.cast_add, Nat.cast_one]
  exact mul_sub_reciprocal_eq_div_mul (Finset.sum (Finset.Icc 1 k) F) (k : Real)
    (by positivity) (by positivity)

end E6BVAux.RealAnalysis
end

section
namespace E6BVAux.RealAnalysis


theorem sum_Ioc_div_le_of_quadratic_partial_sums (F : Nat -> Real) (a b c : Real)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c) (hF : forall n, 0 <= F n)
    {R Q : Nat} (hR : 1 <= R) (hRQ : R <= Q)
    (hBound : forall k : Nat, 1 <= k -> k <= Q ->
      Finset.sum (Finset.Icc 1 k) F <= a + b * (k : Real) + c * (k : Real) ^ 2) :
    Finset.sum (Finset.Ioc R Q) (fun n => F n / (n : Real)) <=
      2 * a / (R : Real) + b * (2 + Real.log (Q : Real)) + 2 * c * (Q : Real) := by
  have hRReal : (0 : Real) < (R : Real) :=
    Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hR)
  have hRQReal : (R : Real) <= (Q : Real) := Nat.cast_le.mpr hRQ
  have hBoundary : Finset.sum (Finset.Icc 1 Q) F / (Q : Real) <=
      a / (R : Real) + b + c * (Q : Real) :=
    (div_le_div_of_nonneg_right (hBound Q (hR.trans hRQ) (Nat.le_refl Q))
      (Nat.cast_nonneg Q)).trans
      (quadratic_div_boundary_le a b c (Q : Real) (R : Real) ha hRReal hRQReal)
  have hKernel :
      Finset.sum (Finset.Ico R Q)
        (fun k => Finset.sum (Finset.Icc 1 k) F / ((k : Real) * ((k : Real) + 1))) <=
      Finset.sum (Finset.Ico R Q)
        (fun k => (a + b * (k : Real) + c * (k : Real) ^ 2) /
          ((k : Real) * ((k : Real) + 1))) := by
    apply Finset.sum_le_sum
    intro k hk
    exact div_le_div_of_nonneg_right
      (hBound k (hR.trans (Finset.mem_Ico.mp hk).1) (Finset.mem_Ico.mp hk).2.le)
      (by positivity)
  have hKernelBound := hKernel.trans
    (sum_quadratic_div_reciprocal_kernel_le a b c ha hb hc hR hRQ)
  have hDiscard : 0 <= Finset.sum (Finset.Icc 1 R) F / (R : Real) :=
    div_nonneg (Finset.sum_nonneg (fun n _ => hF n)) (Nat.cast_nonneg R)
  rw [sum_Ioc_div_eq_abel F hR hRQ]
  calc
    Finset.sum (Finset.Icc 1 Q) F / (Q : Real) -
        Finset.sum (Finset.Icc 1 R) F / (R : Real) +
          Finset.sum (Finset.Ico R Q)
            (fun k => Finset.sum (Finset.Icc 1 k) F / ((k : Real) * ((k : Real) + 1))) <=
        (a / (R : Real) + b + c * (Q : Real)) +
          (a / (R : Real) + b * (1 + Real.log (Q : Real)) + c * (Q : Real)) := by
      linarith
    _ = 2 * a / (R : Real) + b * (2 + Real.log (Q : Real)) +
        2 * c * (Q : Real) := by ring


theorem sum_Ioc_div_le_of_scaled_quadratic_partial_sums
    (F : Nat -> Real) (L a b c : Real) (hL : 0 <= L)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c) (hF : forall n, 0 <= F n)
    {R Q : Nat} (hR : 1 <= R) (hRQ : R <= Q)
    (hBound : forall k : Nat, 1 <= k -> k <= Q ->
      Finset.sum (Finset.Icc 1 k) F <= L * (a + b * (k : Real) + c * (k : Real) ^ 2)) :
    Finset.sum (Finset.Ioc R Q) (fun n => F n / (n : Real)) <=
      L * (2 * a / (R : Real) + b * (2 + Real.log (Q : Real)) +
        2 * c * (Q : Real)) := by
  have hScaled : forall k : Nat, 1 <= k -> k <= Q ->
      Finset.sum (Finset.Icc 1 k) F <=
        L * a + (L * b) * (k : Real) + (L * c) * (k : Real) ^ 2 := by
    intro k hk hkQ
    calc
      Finset.sum (Finset.Icc 1 k) F <=
          L * (a + b * (k : Real) + c * (k : Real) ^ 2) := hBound k hk hkQ
      _ = L * a + (L * b) * (k : Real) + (L * c) * (k : Real) ^ 2 := by ring
  calc
    Finset.sum (Finset.Ioc R Q) (fun n => F n / (n : Real)) <=
        2 * (L * a) / (R : Real) + (L * b) * (2 + Real.log (Q : Real)) +
          2 * (L * c) * (Q : Real) :=
      sum_Ioc_div_le_of_quadratic_partial_sums F (L * a) (L * b) (L * c)
        (by positivity) (by positivity) (by positivity) hF hR hRQ hScaled
    _ = L * (2 * a / (R : Real) + b * (2 + Real.log (Q : Real)) +
        2 * c * (Q : Real)) := by ring

end E6BVAux.RealAnalysis
end

section
namespace E6BVAux.RealAnalysis


theorem log_mul_nat_nonneg {X : Real} {m : Nat} (hX : 1 <= X) (hm : 1 <= m) :
    0 <= Real.log (X * (m : Real)) := by
  apply Real.log_nonneg
  have hRaw : (((1 : Nat) : Real) <= (m : Real)) := Nat.cast_le.mpr hm
  have hM : (1 : Real) <= (m : Real) := by simpa only [Nat.cast_one] using hRaw
  calc
    (1 : Real) = 1 * 1 := by ring
    _ <= X * (m : Real) := by gcongr


theorem log_mul_nat_pow_le {X : Real} {m n : Nat}
    (hX : 1 <= X) (hm : 1 <= m) (hmn : m <= n) (p : Nat) :
    Real.log (X * (m : Real)) ^ p <= Real.log (X * (n : Real)) ^ p := by
  have hXPos : 0 < X := by linarith
  have hMPos : (0 : Real) < (m : Real) :=
    Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hm)
  have hProductPos : 0 < X * (m : Real) := by positivity
  have hProduct : X * (m : Real) <= X * (n : Real) :=
    mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hmn) hXPos.le
  have hLog := Real.log_le_log hProductPos hProduct
  have hNonneg := log_mul_nat_nonneg hX hm
  gcongr

end E6BVAux.RealAnalysis
end

section
namespace E6BVAux.RealAnalysis


theorem conductor_log_range {X : Real} {Q : Nat}
    (hX : Real.exp (4 : Real) <= X) (hQ : 1 <= Q) (hQX : (Q : Real) <= X) :
    And (4 <= Real.log X)
      (And (0 <= Real.log (Q : Real))
        (And (Real.log (Q : Real) <= Real.log X)
          (And (0 <= Real.log (X * (Q : Real)))
            (Real.log (X * (Q : Real)) <= 2 * Real.log X)))) := by
  have hXPos : 0 < X := (Real.exp_pos (4 : Real)).trans_le hX
  have hLogFour : 4 <= Real.log X := (Real.le_log_iff_exp_le hXPos).mpr hX
  have hQPos : (0 : Real) < (Q : Real) :=
    Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hQ)
  have hQNonneg : 0 <= Real.log (Q : Real) := Real.log_natCast_nonneg Q
  have hQLe : Real.log (Q : Real) <= Real.log X := Real.log_le_log hQPos hQX
  have hProduct : Real.log (X * (Q : Real)) = Real.log X + Real.log (Q : Real) :=
    Real.log_mul (ne_of_gt hXPos) (ne_of_gt hQPos)
  have hProductNonneg : 0 <= Real.log (X * (Q : Real)) := by rw [hProduct]; linarith
  have hProductLe : Real.log (X * (Q : Real)) <= 2 * Real.log X := by rw [hProduct]; linarith
  exact And.intro hLogFour (And.intro hQNonneg
    (And.intro hQLe (And.intro hProductNonneg hProductLe)))

end E6BVAux.RealAnalysis
end

section
namespace E6BVAux.RealAnalysis


theorem conductor_log_envelopes {X : Real} {Q : Nat}
    (hX : Real.exp (4 : Real) <= X) (hQ : 1 <= Q) (hQX : (Q : Real) <= X) :
    And (Real.log (X * (Q : Real)) ^ 3 <= 8 * (Real.log X) ^ 3)
      (And ((1 + Real.log (Q : Real)) ^ 2 <= 4 * (Real.log X) ^ 2)
        (2 + Real.log (Q : Real) <= 3 * Real.log X)) := by
  have hRange := conductor_log_range hX hQ hQX
  have hLogFour := hRange.1
  have hQNonneg := hRange.2.1
  have hQLe := hRange.2.2.1
  have hProductNonneg := hRange.2.2.2.1
  have hProductLe := hRange.2.2.2.2
  have hCube : Real.log (X * (Q : Real)) ^ 3 <= 8 * (Real.log X) ^ 3 := by
    calc
      Real.log (X * (Q : Real)) ^ 3 <= (2 * Real.log X) ^ 3 := by gcongr
      _ = 8 * (Real.log X) ^ 3 := by ring
  have hSquareRange : 1 + Real.log (Q : Real) <= 2 * Real.log X := by linarith
  have hSquareNonneg : 0 <= 1 + Real.log (Q : Real) := by linarith
  have hSquare : (1 + Real.log (Q : Real)) ^ 2 <= 4 * (Real.log X) ^ 2 := by
    calc
      (1 + Real.log (Q : Real)) ^ 2 <= (2 * Real.log X) ^ 2 := by gcongr
      _ = 4 * (Real.log X) ^ 2 := by ring
  exact And.intro hCube (And.intro hSquare (by linarith))

end E6BVAux.RealAnalysis
end

section
namespace E6BVAux.RealAnalysis


theorem two_mul_div_le_of_half_le {T r X : Real}
    (hT : 0 < T) (hCut : T / 2 <= r) (hX : 0 <= X) :
    2 * X / r <= 4 * X / T := by
  calc
    2 * X / r <= 2 * X / (T / 2) :=
      div_le_div_of_nonneg_left (a := 2 * X) (b := r) (c := T / 2)
        (by positivity) (by positivity) hCut
    _ = 4 * X / T := by ring

end E6BVAux.RealAnalysis
end

section
namespace E6BVAux.RealAnalysis


theorem rpow_mul_div_le_div {L X u v w : Real}
    (hL : 1 <= L) (hX : 0 <= X) (hDegree : u + w <= v) :
    L ^ u * (X / L ^ v) <= X / L ^ w := by
  have hLPos : 0 < L := zero_lt_one.trans_le hL
  have hVPos : 0 < L ^ v := Real.rpow_pos_of_pos hLPos v
  have hWPos : 0 < L ^ w := Real.rpow_pos_of_pos hLPos w
  have hVNe : Ne (L ^ v) 0 := ne_of_gt hVPos
  have hWNe : Ne (L ^ w) 0 := ne_of_gt hWPos
  have hProduct : (L ^ u * (X / L ^ v)) * L ^ w <= X := by
    calc
      (L ^ u * (X / L ^ v)) * L ^ w = X * L ^ (u + w) / L ^ v := by
        rw [Real.rpow_add hLPos u w]
        ring
      _ <= X * L ^ v / L ^ v :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL hDegree) hX)
          hVPos.le
      _ = X := by field_simp
  calc
    L ^ u * (X / L ^ v) = (L ^ u * (X / L ^ v)) * L ^ w / L ^ w := by field_simp
    _ <= X / L ^ w := div_le_div_of_nonneg_right hProduct hWPos.le


theorem pow_mul_div_le_div {L X v w : Real} (n : Nat)
    (hL : 1 <= L) (hX : 0 <= X) (hDegree : (n : Real) + w <= v) :
    L ^ n * (X / L ^ v) <= X / L ^ w := by
  simpa only [Real.rpow_natCast] using
    (rpow_mul_div_le_div (L := L) (X := X) (u := (n : Real)) (v := v) (w := w)
      hL hX hDegree)

end E6BVAux.RealAnalysis
end
section
namespace E6BVAux.RealAnalysis


theorem rpow_mul_rpow_le_div_of_saving {X L b t delta w p : Real}
    (hX : 1 <= X) (hL : 1 <= L) (hLog : L ^ b <= X ^ delta)
    (hDegree : w + p <= b) (hGap : t + delta <= 1) :
    X ^ t * L ^ p <= X / L ^ w := by
  have hXPos : 0 < X := zero_lt_one.trans_le hX
  have hLPos : 0 < L := zero_lt_one.trans_le hL
  have hWPos : 0 < L ^ w := Real.rpow_pos_of_pos hLPos w
  have hWNe : Ne (L ^ w) 0 := ne_of_gt hWPos
  have hLogDegree : L ^ (w + p) <= X ^ delta :=
    (Real.rpow_le_rpow_of_exponent_le hL hDegree).trans hLog
  have hProduct : (X ^ t * L ^ p) * L ^ w <= X := by
    calc
      (X ^ t * L ^ p) * L ^ w = X ^ t * L ^ (w + p) := by
        rw [Real.rpow_add hLPos w p]
        ring
      _ <= X ^ t * X ^ delta :=
        mul_le_mul_of_nonneg_left hLogDegree (Real.rpow_nonneg hXPos.le t)
      _ = X ^ (t + delta) := (Real.rpow_add hXPos t delta).symm
      _ <= X ^ (1 : Real) := Real.rpow_le_rpow_of_exponent_le hX hGap
      _ = X := Real.rpow_one X
  calc
    X ^ t * L ^ p = (X ^ t * L ^ p) * L ^ w / L ^ w := by field_simp
    _ <= X / L ^ w := div_le_div_of_nonneg_right hProduct hWPos.le


theorem rpow_mul_pow_le_div_of_saving {X L b t delta w : Real} (p : Nat)
    (hX : 1 <= X) (hL : 1 <= L) (hLog : L ^ b <= X ^ delta)
    (hDegree : w + (p : Real) <= b) (hGap : t + delta <= 1) :
    X ^ t * L ^ p <= X / L ^ w := by
  simpa only [Real.rpow_natCast] using
    (rpow_mul_rpow_le_div_of_saving (X := X) (L := L) (b := b) (t := t)
      (delta := delta) (w := w) (p := (p : Real)) hX hL hLog hDegree hGap)

end E6BVAux.RealAnalysis
end

namespace OMA.R_Erdos6_erdos_6_variants_decreasing_R1_H1_R1_H2_R2
open Finset Real Filter ArithmeticFunction
open scoped Classical

/-- Siegel-Walfisz for primitive characters of polylogarithmic conductor, with a logarithmic saving. -/
def H1 : Prop :=
  ∀ A B : ℝ, 0 < A → 0 < B → ∃ C > (0:ℝ), ∀ᶠ x : ℕ in atTop,
    ∀ d : ℕ, 1 ≤ d → (d:ℝ) ≤ (Real.log x)^B →
    ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive → χ ≠ 1 → ∀ y ≤ x,
      ‖∑ n ∈ Icc 1 y, (Λ n : ℂ) * χ (n : ZMod d)‖ ≤ C*x/(Real.log x)^A

/-- Vaughan's cumulative mean-value estimate, before reciprocal Abel summation. -/
def H2 : Prop :=
  let P (x d : ℕ) := (∑ χ ∈ ((Finset.univ.filter
    (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive)).erase 1),
      (Finset.range (x+1)).sup' (by simp) (fun y => ‖∑ n ∈ Icc 1 y,
        (Λ n : ℂ) * χ (n : ZMod d)‖)) / (d.totient : ℝ)
  ∃ C > (0:ℝ), ∀ x k : ℕ, 2 ≤ x → 1 ≤ k →
    ∑ d ∈ Icc 1 k, (d:ℝ) * P x d ≤ (C * Real.log ((x:ℝ)*k)^3) *
      (x + (x:ℝ)^(5/6:ℝ)*k + (x:ℝ)^(1/2:ℝ)*(k:ℝ)^2)

theorem not_isPrimitive_one {d : ℕ} (hd : 2 ≤ d) :
    ¬ (1 : DirichletCharacter ℂ d).IsPrimitive := by
  intro h
  haveI : NeZero d := ⟨by omega⟩
  have h1 := DirichletCharacter.conductor_one (R := ℂ) (n := d)
  have h2 : (1 : DirichletCharacter ℂ d).conductor = d := h
  omega

theorem range_sum_eq_Icc_sum {d : ℕ} (χ : DirichletCharacter ℂ d) (N : ℕ) :
    ∑ n ∈ range (N+1), χ (n : ZMod d) * (Λ n : ℂ) =
      ∑ n ∈ Icc 1 N, (Λ n : ℂ) * χ (n : ZMod d) := by
  have hr : range (N+1) = insert 0 (Icc 1 N) := by
    ext n; simp only [mem_range, mem_insert, mem_Icc]; omega
  rw [hr, sum_insert (by simp)]
  simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, mul_zero, zero_add]
  exact sum_congr rfl (fun n _ => mul_comm _ _)

theorem main : H1 → H2 → OMA.R_Erdos6_erdos_6_variants_decreasing_R1_H1_R1.H2 := by
  intro small large A hA
  let P (x d : ℕ) := (∑ χ ∈ ((Finset.univ.filter
    (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive)).erase 1),
      (Finset.range (x+1)).sup' (by simp) (fun y => ‖∑ n ∈ Icc 1 y,
        (Λ n : ℂ) * χ (n : ZMod d)‖)) / (d.totient : ℝ)
  obtain ⟨V, hV, vaughan⟩ := large
  let E : ℝ := A + 3
  have hE : 0 < E := by dsimp [E]; linarith
  obtain ⟨S, hS, hs⟩ := small (A + E) E (by linarith) hE
  refine ⟨A + 3, (S + 80 * V) * 2 ^ A, le_refl _, by positivity, ?_⟩
  have hfl := tendsto_nat_floor_atTop (α := ℝ)
  have natlim := (tendsto_natCast_atTop_atTop (R := ℝ))
  have sav := E6BVAux.RealAnalysis.eventually_log_rpow_le_rpow (A + 4)
    (by norm_num : (0:ℝ) < 1/6)
  filter_upwards [hfl.eventually hs,
    hfl.eventually (natlim.eventually (eventually_ge_atTop (Real.exp 4))),
    hfl.eventually (natlim.eventually sav), eventually_ge_atTop (2:ℝ)]
    with x hsx hx4 hsav hx2
  set N := ⌊x⌋₊ with hNdef
  set X : ℝ := (N : ℝ) with hXdef
  have xp : 0 < X := (Real.exp_pos _).trans_le hx4
  have L4 : 4 ≤ Real.log X := (Real.le_log_iff_exp_le xp).2 hx4
  have lp : 0 < Real.log X := by linarith
  have X2 : (2:ℝ) ≤ X := by
    have hh := Real.add_one_le_exp (4:ℝ)
    linarith
  have N2 : 2 ≤ N := by
    have h : (2:ℝ) ≤ (N:ℝ) := X2
    exact_mod_cast h
  have x1 : 1 ≤ X := by linarith
  have Xx : X ≤ x := Nat.floor_le (by linarith)
  have xX : x < X + 1 := Nat.lt_floor_add_one x
  have xpos : 0 < x := by linarith
  have logXx : Real.log X ≤ Real.log x := Real.log_le_log xp Xx
  -- the cutoffs
  set Q := ⌊Real.sqrt x / (Real.log x) ^ (A + 3)⌋₊ with hQdef
  let R := ⌊(Real.log X) ^ E⌋₊
  have cut := E6BVAux.RealAnalysis.polylog_floor_cutoff_bounds (B := E) hx4
    (by dsimp [E]; linarith)
  have hR : 1 ≤ R := cut.1
  have hP (d : ℕ) : 0 ≤ P N d := by
    dsimp [P]
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply sum_nonneg
    intro χ _
    exact (norm_nonneg _).trans (Finset.le_sup' (fun y => ‖∑ n ∈ Icc 1 y,
      (Λ n : ℂ) * χ (n : ZMod d)‖) (by simp : 0 ∈ range (N+1)))
  -- step 1: compare with the maximal primitive mean
  have term (d : ℕ) (hd : 3 ≤ d) :
      (1/(Nat.totient d:ℝ)) *
        ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
          ‖∑ n ∈ range (N+1), χ (n : ZMod d) * (Λ n : ℂ)‖ ≤ P N d := by
    dsimp only [P]
    rw [Finset.erase_eq_self.mpr (by
      simp only [mem_filter, mem_univ, true_and]
      exact not_isPrimitive_one (by omega)), one_div_mul_eq_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply sum_le_sum
    intro χ _
    rw [range_sum_eq_Icc_sum]
    exact Finset.le_sup' (fun y => ‖∑ n ∈ Icc 1 y, (Λ n : ℂ) * χ (n : ZMod d)‖)
      (mem_range.mpr (Nat.lt_succ_self N))
  have step1 : (∑ k ∈ Ico 2 Q, (1/(Nat.totient (k+1):ℝ)) *
      ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ (k+1) => χ.IsPrimitive),
        ‖∑ n ∈ range (N+1), χ (n : ZMod (k+1)) * (Λ n : ℂ)‖) ≤
      ∑ d ∈ Icc 1 Q, P N d := by
    calc _ ≤ ∑ k ∈ Ico 2 Q, P N (k+1) :=
          sum_le_sum (fun k hk => term (k+1) (by have := (mem_Ico.mp hk).1; omega))
      _ = ∑ d ∈ (Ico 2 Q).image (· + 1), P N d :=
          (sum_image (fun a _ b _ h => by simpa using h)).symm
      _ ≤ ∑ d ∈ Icc 1 Q, P N d := by
          apply sum_le_sum_of_subset_of_nonneg _ (fun d _ _ => hP d)
          intro d hd
          simp only [mem_image, mem_Ico] at hd
          obtain ⟨k, hk, rfl⟩ := hd
          simp only [mem_Icc]; omega
  -- step 2: small conductors by Siegel-Walfisz
  have sBound : ∑ d ∈ Icc 1 R, P N d ≤ S*X/(Real.log X)^A := by
    let K := S*X/(Real.log X)^(A+E)
    have kn : 0 ≤ K := by dsimp [K]; positivity
    have each (d : ℕ) (hd : d ∈ Icc 1 R) : P N d ≤ K := by
      have h1 := (mem_Icc.mp hd).1
      have dr : (d:ℝ) ≤ (Real.log X)^E := (Nat.cast_le.mpr (mem_Icc.mp hd).2).trans cut.2.1
      have tot : 0 < (d.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega : 0<d)
      dsimp only [P]
      apply (div_le_iff₀ tot).2
      let T := (Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive)).erase 1
      have cc : T.card ≤ d.totient := by
        have bound := card_le_univ T
        haveI : NeZero d := ⟨by omega⟩
        simpa only [← Nat.card_eq_fintype_card,
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity] using bound
      calc
        _ ≤ ∑ χ ∈ T, K := by
          dsimp only [T]
          apply sum_le_sum
          intro χ hc
          apply Finset.sup'_le
          intro y hy
          exact hsx d h1 dr χ (mem_filter.mp (mem_erase.mp hc).2).2 (mem_erase.mp hc).1 y
            (by have := mem_range.mp hy; omega)
        _ = (T.card:ℝ)*K := by simp
        _ ≤ _ := by rw [mul_comm K]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast cc) kn
    calc
      _ ≤ ∑ _d ∈ Icc 1 R, K := sum_le_sum each
      _ = (R:ℝ)*K := by simp
      _ ≤ (Real.log X)^E*K := mul_le_mul_of_nonneg_right cut.2.1 kn
      _ = _ := by dsimp [K]; rw [Real.rpow_add lp A E]; field_simp
  -- the bound in terms of N
  have core : ∑ d ∈ Icc 1 Q, P N d ≤ (S + 80*V) * X/(Real.log X)^A := by
    have lA : 0 < (Real.log X)^A := Real.rpow_pos_of_pos lp A
    have base : 0 ≤ X/(Real.log X)^A := by positivity
    by_cases hrq : R ≤ Q
    · have hQ : 1 ≤ Q := hR.trans hrq
      -- size of Q
      have sq2 : Real.sqrt x ≤ Real.sqrt 2 * Real.sqrt X := by
        rw [← Real.sqrt_mul (by norm_num)]
        exact Real.sqrt_le_sqrt (by linarith)
      have lpow : (Real.log X)^(A+3) ≤ (Real.log x)^(A+3) :=
        Real.rpow_le_rpow lp.le logXx (by linarith)
      have lpos3 : 0 < (Real.log X)^(A+3) := Real.rpow_pos_of_pos lp _
      have Qle : (Q:ℝ) ≤ Real.sqrt 2 * Real.sqrt X / (Real.log X)^(A+3) := by
        calc (Q:ℝ) ≤ Real.sqrt x / (Real.log x)^(A+3) :=
            Nat.floor_le (div_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _))
          _ ≤ Real.sqrt 2 * Real.sqrt X / (Real.log X)^(A+3) :=
            div_le_div₀ (by positivity) sq2 lpos3 lpow
      have s2 : Real.sqrt 2 ≤ 3/2 := by
        nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
      have l1 : 1 ≤ (Real.log X)^(A+3) := Real.one_le_rpow (by linarith) (by linarith)
      have sX : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt xp.le
      have sXge : Real.sqrt 2 ≤ Real.sqrt X := Real.sqrt_le_sqrt X2
      have qx : (Q:ℝ) ≤ X := by
        calc (Q:ℝ) ≤ Real.sqrt 2 * Real.sqrt X / (Real.log X)^(A+3) := Qle
          _ ≤ Real.sqrt 2 * Real.sqrt X := div_le_self (by positivity) l1
          _ ≤ Real.sqrt X * Real.sqrt X :=
            mul_le_mul_of_nonneg_right sXge (Real.sqrt_nonneg _)
          _ = X := sX
      have env := E6BVAux.RealAnalysis.conductor_log_envelopes hx4 hQ qx
      have rng := E6BVAux.RealAnalysis.conductor_log_range hx4 hQ qx
      have tail := E6BVAux.RealAnalysis.sum_Ioc_div_le_of_scaled_quadratic_partial_sums
        (fun d => (d:ℝ)*P N d) (V*Real.log (X*Q)^3) X (X^(5/6:ℝ)) (X^(1/2:ℝ))
        (mul_nonneg hV.le (pow_nonneg rng.2.2.2.1 3)) xp.le (by positivity) (by positivity)
        (fun d => mul_nonneg (Nat.cast_nonneg _) (hP d)) hR hrq
        (fun k hk hq => (vaughan N k N2 hk).trans (by
          have logle := E6BVAux.RealAnalysis.log_mul_nat_pow_le x1 hk hq 3
          change (V*Real.log (X*k)^3)*_ ≤ (V*Real.log (X*Q)^3)*_
          gcongr))
      have cutid : ∑ d ∈ Ioc R Q, P N d = ∑ d ∈ Ioc R Q, (d:ℝ)*P N d/d := by
        apply sum_congr rfl
        intro d hd
        have pos : (0:ℝ)<d := by exact_mod_cast (by have := (mem_Ioc.mp hd).1; omega : 0<d)
        field_simp
      have split := E6BVAux.RealAnalysis.sum_Icc_le_sum_Icc_add_sum_Ioc (P N) hP R Q
      rw [cutid] at split
      -- the three pieces of the tail
      set Lg := Real.log X with hLg
      have Lg1 : 1 ≤ Lg := by linarith
      have inv : 2 * X / (R:ℝ) ≤ 4 * X / Lg^E :=
        E6BVAux.RealAnalysis.two_mul_div_le_of_half_le (Real.rpow_pos_of_pos lp E) cut.2.2 xp.le
      have i3 : Lg^3 * (X / Lg^E) ≤ X / Lg^A :=
        E6BVAux.RealAnalysis.pow_mul_div_le_div 3 Lg1 xp.le
          (show ((3:ℕ):ℝ) + A ≤ A + 3 by push_cast; linarith)
      have i3' : Lg^3 * (X / Lg^(A+3)) ≤ X / Lg^A :=
        E6BVAux.RealAnalysis.pow_mul_div_le_div 3 Lg1 xp.le
          (show ((3:ℕ):ℝ) + A ≤ A + 3 by push_cast; linarith)
      have mix : X^(5/6:ℝ) * Lg^4 ≤ X / Lg^A :=
        E6BVAux.RealAnalysis.rpow_mul_pow_le_div_of_saving 4 x1 Lg1 hsav
          (by norm_num) (by norm_num)
      have root : X^(1/2:ℝ) * (Q:ℝ) ≤ 3/2 * (X / Lg^(A+3)) := by
        rw [← Real.sqrt_eq_rpow]
        calc Real.sqrt X * (Q:ℝ) ≤ Real.sqrt X * (Real.sqrt 2 * Real.sqrt X / Lg^(A+3)) :=
              mul_le_mul_of_nonneg_left Qle (Real.sqrt_nonneg _)
          _ = Real.sqrt 2 * ((Real.sqrt X * Real.sqrt X) / Lg^(A+3)) := by ring
          _ = Real.sqrt 2 * (X / Lg^(A+3)) := by rw [sX]
          _ ≤ 3/2 * (X / Lg^(A+3)) := mul_le_mul_of_nonneg_right s2 (by positivity)
      have tailB : V*Real.log (X*Q)^3 * (2*X/(R:ℝ) + X^(5/6:ℝ)*(2 + Real.log (Q:ℝ)) +
          2*X^(1/2:ℝ)*(Q:ℝ)) ≤ 80*V*(X/Lg^A) := by
        have hlog3 : Real.log (X*Q)^3 ≤ 8*Lg^3 := env.1
        have h2 : 2 + Real.log (Q:ℝ) ≤ 3*Lg := env.2.2
        have hin : 0 ≤ 2*X/(R:ℝ) + X^(5/6:ℝ)*(2 + Real.log (Q:ℝ)) + 2*X^(1/2:ℝ)*(Q:ℝ) := by
          have : 0 ≤ Real.log (Q:ℝ) := Real.log_nonneg (by exact_mod_cast hQ)
          positivity
        calc V*Real.log (X*Q)^3 * (2*X/(R:ℝ) + X^(5/6:ℝ)*(2 + Real.log (Q:ℝ)) +
              2*X^(1/2:ℝ)*(Q:ℝ))
            ≤ V*(8*Lg^3) * (4*X/Lg^E + X^(5/6:ℝ)*(3*Lg) + 2*(3/2*(X/Lg^(A+3)))) := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left hlog3 hV.le) _ hin (by positivity)
              have hm : X^(5/6:ℝ)*(2 + Real.log (Q:ℝ)) ≤ X^(5/6:ℝ)*(3*Lg) :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
              have hr : 2*X^(1/2:ℝ)*(Q:ℝ) ≤ 2*(3/2*(X/Lg^(A+3))) := by
                rw [mul_assoc]; exact mul_le_mul_of_nonneg_left root (by norm_num)
              linarith
          _ = V*(32*(Lg^3*(X/Lg^E)) + 24*(X^(5/6:ℝ)*Lg^4) + 24*(Lg^3*(X/Lg^(A+3)))) := by
              ring
          _ ≤ V*(32*(X/Lg^A) + 24*(X/Lg^A) + 24*(X/Lg^A)) := by gcongr
          _ = 80*V*(X/Lg^A) := by ring
      calc ∑ d ∈ Icc 1 Q, P N d ≤ ∑ d ∈ Icc 1 R, P N d + ∑ d ∈ Ioc R Q, (d:ℝ)*P N d/d := split
        _ ≤ S*X/Lg^A + 80*V*(X/Lg^A) := add_le_add sBound (tail.trans tailB)
        _ = (S + 80*V) * X/Lg^A := by ring
    · have sub : Icc 1 Q ⊆ Icc 1 R := Icc_subset_Icc_right (by omega)
      refine (sum_le_sum_of_subset_of_nonneg sub (fun d _ _ => hP d)).trans (sBound.trans ?_)
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) base
  -- back to the real variable
  have logx2 : Real.log x ≤ 2 * Real.log X := by
    have hxX2 : x ≤ X^2 := by nlinarith
    calc Real.log x ≤ Real.log (X^2) := Real.log_le_log xpos hxX2
      _ = 2 * Real.log X := by rw [Real.log_pow]; norm_num
  have lx : 0 < Real.log x := lp.trans_le logXx
  have powle : (Real.log x)^A ≤ 2^A * (Real.log X)^A := by
    rw [← Real.mul_rpow (by norm_num) lp.le]
    exact Real.rpow_le_rpow lx.le logx2 hA.le
  have lxA : 0 < (Real.log x)^A := Real.rpow_pos_of_pos lx A
  have lXA : 0 < (Real.log X)^A := Real.rpow_pos_of_pos lp A
  have conv : X/(Real.log X)^A ≤ 2^A * x/(Real.log x)^A := by
    rw [div_le_div_iff₀ lXA lxA]
    calc X * (Real.log x)^A ≤ x * (2^A * (Real.log X)^A) :=
          mul_le_mul Xx powle lxA.le xpos.le
      _ = 2^A * x * (Real.log X)^A := by ring
  have K0 : 0 ≤ S + 80*V := by positivity
  refine step1.trans (core.trans ?_)
  calc (S + 80*V) * X/(Real.log X)^A = (S + 80*V) * (X/(Real.log X)^A) := by ring
    _ ≤ (S + 80*V) * (2^A * x/(Real.log x)^A) := mul_le_mul_of_nonneg_left conv K0
    _ = (S + 80*V) * 2^A * x/(Real.log x)^A := by ring

end OMA.R_Erdos6_erdos_6_variants_decreasing_R1_H1_R1_H2_R2
