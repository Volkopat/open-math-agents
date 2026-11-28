import OMAStatements.S_oeis_a026765
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.PowerSeries.Expand

/-!
A proof of Maksym Voznyy's generating-function conjecture for OEIS A026765,
starting from the defining triangle A026758. The formal power series all have
rational coefficients. See https://oeis.org/A026765 and https://oeis.org/A026758 .
Credit: @VirtualMe64
-/

namespace A026765Proof

open OMA.S_oeis_a026765

-- Pair successive rows and split the resulting walk at columns zero and one.
def profile (m : ℕ) (j : ℤ) : ℕ := triangle (2*m+1) ((m:ℤ)+j)
def leftProfile (m k : ℕ) : ℕ := profile m (-(k:ℤ))
def rightProfile (m k : ℕ) : ℕ := profile m ((k:ℤ)+1)

theorem evenTriangle (m : ℕ) (k : ℤ) :
    triangle (2*m+2) k = triangle (2*m+1) (k-1) + triangle (2*m+1) k := by
  rw [triangle]
  simp

theorem profileStep (m : ℕ) (j : ℤ) :
    profile (m+1) j = profile m (j-1) + (if j ≤ 0 then 3 else 2) * profile m j +
      profile m (j+1) := by
  have e : 2*(m+1)+1 = (2*m+1)+2 := by omega
  have cut : (2:ℤ) * ((m:ℤ)+1+j) ≤ ((2*m+1+1 : ℕ):ℤ) ↔ j ≤ 0 := by omega
  have odd : (2*m+1)%2=1 := by omega
  unfold profile
  rw [e, triangle]
  rw [show ((m+1 : ℕ):ℤ) = (m:ℤ)+1 by omega]
  simp only [odd, true_and]
  simp only [cut]
  rw [evenTriangle, evenTriangle]
  have e₀ : (m:ℤ)+1+j-1 = m+j := by omega
  have e₁ : (m:ℤ)+1+j-1-1 = m+(j-1) := by omega
  have e₂ : (m:ℤ)+1+j = m+(j+1) := by omega
  rw [e₁, e₀, e₂]
  split <;> omega

theorem leftProfileZero (k : ℕ) : leftProfile 0 k = (if k = 0 then 1 else 0) := by
  simp [leftProfile, profile, triangle, show -((k:ℕ):ℤ) ≠ 1 by omega]

theorem rightProfileZero (k : ℕ) : rightProfile 0 k = (if k = 0 then 1 else 0) := by
  simp [rightProfile, profile, triangle, show (k:ℤ)+1 ≠ 0 by omega, show ((k:ℤ)+1 = 1) ↔ k=0 by omega]

theorem leftProfileInterface (m : ℕ) : leftProfile (m+1) 0 =
    leftProfile m 1 + 3*leftProfile m 0 + rightProfile m 0 := by
  simp [leftProfile, rightProfile, profileStep]

theorem rightProfileInterface (m : ℕ) : rightProfile (m+1) 0 =
    leftProfile m 0 + 2*rightProfile m 0 + rightProfile m 1 := by
  simp [leftProfile, rightProfile, profileStep]

theorem leftProfileInterior (m k : ℕ) : leftProfile (m+1) (k+1) =
    leftProfile m (k+2) + 3*leftProfile m (k+1) + leftProfile m k := by
  simp only [leftProfile, profileStep]
  rw [show ((k+1:ℕ):ℤ) = (k:ℤ)+1 by omega, show ((k+2:ℕ):ℤ)=(k:ℤ)+2 by omega]
  have e₁ : -((k:ℤ)+1)-1 = -(k+2) := by omega
  have e₂ : -((k:ℤ)+1)+1 = -k := by omega
  rw [e₁, e₂, if_pos (by omega)]

theorem rightProfileInterior (m k : ℕ) : rightProfile (m+1) (k+1) =
    rightProfile m k + 2*rightProfile m (k+1) + rightProfile m (k+2) := by
  simp only [rightProfile, profileStep]
  rw [show ((k+1:ℕ):ℤ) = (k:ℤ)+1 by omega, show ((k+2:ℕ):ℤ)=(k:ℤ)+2 by omega]
  have e₁ : (k:ℤ)+1+1-1 = k+1 := by omega
  have e₂ : (k:ℤ)+1+1+1 = k+2+1 := by omega
  rw [e₁, e₂, if_neg (by omega)]


theorem triangleOutside : ∀ (n : ℕ) (k : ℤ), (k < 0 ∨ (n:ℤ) < k) → triangle n k = 0
  | 0, k, h => by simp [triangle, show k ≠ 0 by omega]
  | 1, k, h => by simp [triangle, show ¬(k = 0 ∨ k = 1) by omega]
  | n+2, k, h => by
    rw [triangle, triangleOutside (n+1) (k-1) (by omega),
      triangleOutside (n+1) k (by omega), triangleOutside n (k-1) (by omega)]
    simp

theorem prefixCongr (f g : ℕ → ℕ) (n : ℕ) (h : ∀ k, k < n → f k = g k) :
    prefixSum f n = prefixSum g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [prefixSum]
    rw [ih (by intro k hk; apply h; omega), h n (by omega)]

theorem prefixSplit (f : ℕ → ℕ) (a b : ℕ) :
    prefixSum f (a+b) = prefixSum f a + prefixSum (fun k => f (a+k)) b := by
  induction b with
  | zero => simp [prefixSum]
  | succ b ih =>
    change prefixSum f (a+b) + f (a+b) = prefixSum f a +
      (prefixSum (fun k => f (a+k)) b + f (a+b))
    rw [ih, Nat.add_assoc]

theorem prefixFront (f : ℕ → ℕ) (n : ℕ) :
    prefixSum f (n+1) = f 0 + prefixSum (fun k => f (k+1)) n := by
  rw [show n+1=1+n by omega, prefixSplit]
  simp only [prefixSum, Nat.zero_add]
  congr 1
  apply prefixCongr; intro k _; congr 1; omega

theorem prefixReverse (f : ℕ → ℕ) (n : ℕ) :
    prefixSum (fun k => f (n-1-k)) n = prefixSum f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [prefixFront]
    simp only [Nat.add_sub_cancel, Nat.sub_zero]
    change f n + prefixSum (fun k => f (n - (k+1))) n = prefixSum f n + f n
    rw [show prefixSum (fun k => f (n - (k+1))) n =
        prefixSum (fun k => f (n-1-k)) n from
        prefixCongr _ _ _ (by intro k _; congr 1; omega), ih, Nat.add_comm]

theorem prefixPlus (f g : ℕ → ℕ) (n : ℕ) :
    prefixSum (fun k => f k + g k) n = prefixSum f n + prefixSum g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [prefixSum]; omega

theorem oddRowSplit (m : ℕ) : rowSum (2*m+1) =
    prefixSum (leftProfile m) (m+1) + prefixSum (rightProfile m) (m+1) := by
  let f (k:ℕ) := triangle (2*m+1) k
  change prefixSum f (2*m+1+1) = _
  rw [show 2*m+1+1 = (m+1)+(m+1) by omega, prefixSplit]
  congr 1
  · rw [← prefixReverse f (m+1)]
    apply prefixCongr
    intro k hk
    unfold f leftProfile profile
    congr 1; omega
  · apply prefixCongr
    intro k _
    unfold f rightProfile profile
    congr 1; omega

theorem evenRowDouble (m : ℕ) : rowSum (2*m+2) = 2*rowSum (2*m+1) := by
  let f (k:ℕ) := triangle (2*m+1) k
  let g (k:ℕ) := triangle (2*m+1) ((k:ℤ)-1)
  let len := 2*m+2
  change prefixSum (fun k => triangle (2*m+2) k) (len+1) = 2*prefixSum f len
  rw [show prefixSum (fun k => triangle (2*m+2) k) (len+1) =
        prefixSum (fun k => g k + f k) (len+1) from
        prefixCongr _ _ _ (by intro k _; exact evenTriangle m _), prefixPlus]
  have e₁ : prefixSum g (len+1) = prefixSum f len := by
    rw [prefixFront]
    have gz : g 0 = 0 := by
      unfold g
      apply triangleOutside
      left; decide
    rw [gz, Nat.zero_add]
    apply prefixCongr
    intro k _
    unfold f g
    congr 1; omega
  have e₂ : prefixSum f (len+1) = prefixSum f len := by
    change prefixSum f len + f len = prefixSum f len
    have fz : f len = 0 := triangleOutside (2*m+1) (len:ℤ) (Or.inr (by dsimp [len]; omega))
    rw [fz, Nat.add_zero]
  rw [e₁, e₂]; omega



theorem leftProfileOutside (m k : ℕ) (h : m < k) : leftProfile m k = 0 := by
  unfold leftProfile profile
  apply triangleOutside
  left; omega

theorem rightProfileOutside (m k : ℕ) (h : m < k) : rightProfile m k = 0 := by
  unfold rightProfile profile
  apply triangleOutside
  right; omega

theorem rowSumZero : rowSum 0 = 1 := by decide

-- Lift the interior and boundary recurrences to identities of power series.
open PowerSeries

private noncomputable def oaProfileSeries (f : ℕ → ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun m => (f m : ℚ)

private noncomputable def oaLeft (k : ℕ) : PowerSeries ℚ :=
  oaProfileSeries (fun m => leftProfile m k)

private noncomputable def oaRight (k : ℕ) : PowerSeries ℚ :=
  oaProfileSeries (fun m => rightProfile m k)

private theorem oaProfileSeriesStep (f u v w : ℕ → ℕ) (c d : ℕ) (hz : f 0 = d)
    (hs : ∀ m, f (m+1) = u m + c * v m + w m) :
    oaProfileSeries f = C (d : ℚ) +
      X * (oaProfileSeries u + C (c : ℚ) * oaProfileSeries v + oaProfileSeries w) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp only [oaProfileSeries, coeff_mk, map_add, coeff_zero_C, coeff_zero_X_mul, add_zero, hz]
  | succ n =>
    simp only [oaProfileSeries, coeff_mk, map_add, coeff_C, Nat.succ_ne_zero, if_false,
      zero_add, coeff_succ_X_mul, coeff_C_mul]
    exact_mod_cast hs n

private theorem oaLeftBoundary :
    oaLeft 0 = 1 + X * (oaLeft 1 + 3 * oaLeft 0 + oaRight 0) := by
  simpa only [oaLeft, oaRight, Nat.cast_ofNat, map_ofNat, Nat.cast_one, map_one] using
    oaProfileSeriesStep (leftProfile · 0) (leftProfile · 1) (leftProfile · 0) (rightProfile · 0)
      3 1 (by simp [leftProfileZero]) leftProfileInterface

private theorem oaRightBoundary :
    oaRight 0 = 1 + X * (oaRight 1 + 2 * oaRight 0 + oaLeft 0) := by
  simpa only [oaLeft, oaRight, Nat.cast_ofNat, map_ofNat, Nat.cast_one, map_one] using
    oaProfileSeriesStep (rightProfile · 0) (rightProfile · 1) (rightProfile · 0) (leftProfile · 0)
      2 1 (by simp [rightProfileZero]) (fun m => by rw [rightProfileInterface]; omega)

private theorem oaLeftStep (k : ℕ) :
    oaLeft (k+1) = X * (oaLeft k + C (3:ℚ) * oaLeft (k+1) + oaLeft (k+2)) := by
  simpa only [oaLeft, Nat.cast_zero, map_zero, zero_add, Nat.cast_ofNat] using
    oaProfileSeriesStep (leftProfile · (k+1)) (leftProfile · k) (leftProfile · (k+1))
      (leftProfile · (k+2)) 3 0 (by simp [leftProfileZero])
      (fun m => by rw [leftProfileInterior]; omega)

private theorem oaRightStep (k : ℕ) :
    oaRight (k+1) = X * (oaRight k + C (2:ℚ) * oaRight (k+1) + oaRight (k+2)) := by
  simpa only [oaRight, Nat.cast_zero, map_zero, zero_add, Nat.cast_ofNat] using
    oaProfileSeriesStep (rightProfile · (k+1)) (rightProfile · k) (rightProfile · (k+1))
      (rightProfile · (k+2)) 2 0 (by simp [rightProfileZero]) (fun m => rightProfileInterior m k)

-- Construct the root with zero constant term for each of the two walk kernels.
private def oaKernelCoeff (c : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => (if n = 0 then 1 else 0) + c * oaKernelCoeff c n +
      ∑ i : Fin (n+1), oaKernelCoeff c i.val * oaKernelCoeff c (n - i.val)
termination_by n => n
decreasing_by
  all_goals first | exact Nat.lt_succ_self _ | exact Fin.isLt _ | exact Nat.lt_succ_of_le (Nat.sub_le _ _)

private noncomputable def oaKernel (c : ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (oaKernelCoeff c)

private theorem oaKernel_zero (c : ℚ) : PowerSeries.constantCoeff (oaKernel c) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, oaKernel, PowerSeries.coeff_mk, oaKernelCoeff]

private theorem oaKernel_eq (c : ℚ) :
    oaKernel c = PowerSeries.X * (1 + PowerSeries.C c * oaKernel c + oaKernel c ^ 2) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
      PowerSeries.constantCoeff_X, zero_mul] using oaKernel_zero c
  | succ n =>
    have shift (f : PowerSeries ℚ) :
        PowerSeries.coeff (n+1) (PowerSeries.X * f) = PowerSeries.coeff n f := by
      simpa only [pow_one] using PowerSeries.coeff_X_pow_mul f 1 n
    rw [shift]
    simp only [map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul]
    simp only [sq, PowerSeries.coeff_mul, oaKernel, PowerSeries.coeff_mk]
    rw [oaKernelCoeff, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => oaKernelCoeff c i * oaKernelCoeff c j)]
    rw [← Fin.sum_univ_eq_sum_range]

-- Coefficient induction gives the unique geometric profile on each half-line.
private theorem oaHalfLineAbstract {R K : Type*} [CommSemiring R] [CommSemiring K]
    (coef : ℕ → R → K) (t c r : R) (w : K)
    (hext : ∀ {x y : R}, (∀ n, coef n x = coef n y) → x = y)
    (hz : ∀ x, coef 0 (t*x) = 0)
    (hs : ∀ (n : ℕ) x y z, coef (n+1) (t*(x+c*y+z)) =
      coef n x + w*coef n y + coef n z)
    (hr : r = t*(1+c*r+r^2))
    (F : ℕ → R) (hf : ∀ k, F (k+1) = t*(F k+c*F (k+1)+F (k+2))) :
    ∀ k, F k = F 0*r^k := by
  let G (k : ℕ) := F 0*r^k
  have hg (k : ℕ) : G (k+1) = t*(G k+c*G (k+1)+G (k+2)) := by
    change F 0*r^(k+1) = t*(F 0*r^k+c*(F 0*r^(k+1))+F 0*r^(k+2))
    calc
      F 0*r^(k+1) = F 0*r^k*r := by rw [pow_succ]; ring
      _ = F 0*r^k*(t*(1+c*r+r^2)) := congrArg (fun x => F 0*r^k*x) hr
      _ = _ := by simp only [pow_succ]; ring
  have h0 : F 0 = G 0 := by simp [G]
  have go (n : ℕ) : ∀ k, coef n (F k) = coef n (G k) := by
    induction n with
    | zero =>
      intro k
      cases k with
      | zero => exact congrArg (coef 0) h0
      | succ k => calc
          coef 0 (F (k+1)) = 0 := by rw [hf k, hz]
          _ = coef 0 (G (k+1)) := by rw [hg k, hz]
    | succ n ih =>
      intro k
      cases k with
      | zero => exact congrArg (coef (n+1)) h0
      | succ k => calc
          coef (n+1) (F (k+1)) = coef n (F k) + w*coef n (F (k+1)) + coef n (F (k+2)) := by
            conv_lhs => rw [hf k, hs]
          _ = coef n (G k) + w*coef n (G (k+1)) + coef n (G (k+2)) := by
            rw [ih k, ih (k+1), ih (k+2)]
          _ = coef (n+1) (G (k+1)) := by conv_rhs => rw [hg k, hs]
  exact fun k => hext (fun n => go n k)

open PowerSeries in
private theorem oaHalfLine (c : ℚ) (r : PowerSeries ℚ)
    (hr : r = X*(1+C c*r+r^2)) (F : ℕ → PowerSeries ℚ)
    (hf : ∀ k, F (k+1) = X*(F k+C c*F (k+1)+F (k+2))) :
    ∀ k, F k = F 0*r^k :=
  oaHalfLineAbstract (fun n p => coeff n p) X (C c) r c
    (fun h => PowerSeries.ext h) coeff_zero_X_mul
    (fun n a b d => by simp only [coeff_succ_X_mul, map_add, coeff_C_mul])
    hr F hf

-- Define geometric half-line sums through their finite coefficient sums.
open PowerSeries
open scoped BigOperators
noncomputable section

/-- Coefficientwise geometric sum of a half-line. -/
private def oaHalf (A r : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => ∑ k ∈ Finset.range (n+1), coeff n (A * r^k)

private theorem oaHalf_coeff (A r : PowerSeries ℚ) (n : ℕ) :
    coeff n (oaHalf A r) = ∑ k ∈ Finset.range (n+1), coeff n (A * r^k) :=
  PowerSeries.coeff_mk _ _

private theorem oaPowerCoeffZero (A r : PowerSeries ℚ) (hr : constantCoeff r = 0)
    (i k : ℕ) (hik : i < k) : coeff i (A * r^k) = 0 := by
  obtain ⟨u, hu⟩ := PowerSeries.X_dvd_iff.mpr hr
  calc
    coeff i (A * r^k) = coeff i ((A * u^k) * (X : PowerSeries ℚ)^k) := by
      rw [hu, mul_pow]
      ac_rfl
    _ = 0 := by rw [PowerSeries.coeff_mul_X_pow', if_neg (Nat.not_le.mpr hik)]

private theorem oaHalf_trunc (A r : PowerSeries ℚ) (hr : constantCoeff r = 0)
    (n i : ℕ) (hi : i ≤ n) :
    coeff i (oaHalf A r) = coeff i (∑ k ∈ Finset.range (n+1), A * r^k) := by
  rw [oaHalf_coeff, map_sum]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hi))
  intro k _ hk
  exact oaPowerCoeffZero A r hr i k (by simp at hk; omega)

private theorem oaGeomTrunc (A r : PowerSeries ℚ) (n : ℕ) :
    (∑ k ∈ Finset.range n, A * r^k) * (1-r) = A - A*r^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
    ring

private theorem oaHalf_mul (A r : PowerSeries ℚ) (hr : constantCoeff r = 0) :
    oaHalf A r * (1-r) = A := by
  apply PowerSeries.ext
  intro n
  let S : PowerSeries ℚ := ∑ k ∈ Finset.range (n+1), A * r^k
  have hcoeff : coeff n (oaHalf A r * (1-r)) = coeff n (S*(1-r)) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hpn : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
    rw [oaHalf_trunc A r hr n p.1 (by omega)]
  calc
    coeff n (oaHalf A r * (1-r)) = coeff n (S*(1-r)) := hcoeff
    _ = coeff n A := by
      dsimp only [S]
      rw [oaGeomTrunc, map_sub, oaPowerCoeffZero A r hr n (n+1) (by omega), sub_zero]

end

-- Identify each coefficient of a half-line sum with its triangle prefix sum.
private theorem oaPrefixCast (f : ℕ → ℕ) (n : ℕ) :
    (prefixSum f n : ℚ) = ∑ k ∈ Finset.range n, (f k : ℚ) := by
  induction n with
  | zero => simp [prefixSum]
  | succ n ih => simp [prefixSum, Finset.sum_range_succ, ih]

private theorem oaHalfPrefix (f : ℕ → ℕ → ℕ) (A r : PowerSeries ℚ)
    (hf : ∀ m k, PowerSeries.coeff m (A*r^k) = (f m k : ℚ)) (m : ℕ) :
    PowerSeries.coeff m (oaHalf A r) = (prefixSum (f m) (m+1) : ℚ) := by
  rw [oaHalf_coeff, oaPrefixCast]
  exact Finset.sum_congr rfl (fun k _ => hf m k)

-- Relate the sum of both profiles to the series for even rows.
open PowerSeries in
private theorem oaEvenFromHalves (A r B s : PowerSeries ℚ)
    (hf : ∀ m k, coeff m (A*r^k) = (leftProfile m k : ℚ))
    (hg : ∀ m k, coeff m (B*s^k) = (rightProfile m k : ℚ)) :
    PowerSeries.mk (fun m => (rowSum (2*m) : ℚ)) =
      1 + 2*X*(oaHalf A r + oaHalf B s) := by
  let H := oaHalf A r + oaHalf B s
  have hodd (m : ℕ) : (rowSum (2*m+1) : ℚ) = coeff m H := by
    rw [oddRowSplit, Nat.cast_add]
    change _ = coeff m (oaHalf A r + oaHalf B s)
    rw [map_add, oaHalfPrefix leftProfile A r hf, oaHalfPrefix rightProfile B s hg]
  change _ = 1 + 2*X*H
  rw [show 2*X*H = X*H+X*H by ring]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp only [coeff_mk, Nat.mul_zero, rowSumZero, Nat.cast_one, map_add,
      coeff_zero_X_mul, coeff_one, if_true, add_zero]
  | succ m =>
    rw [coeff_mk, show 2*(m+1) = 2*m+2 by omega, evenRowDouble]
    simp only [Nat.cast_mul, Nat.cast_ofNat, map_add, coeff_one, Nat.succ_ne_zero,
      if_false, zero_add, coeff_succ_X_mul, hodd]
    ring

-- Eliminate the boundary values and kernel roots by polynomial identities.
private theorem oaEvenAlgebra {K : Type*} [CommRing K] [IsDomain K]
    (t r s A B L R E : K)
    (hr : r = t * (1 + 3*r + r^2))
    (hs : s = t * (1 + 2*s + s^2))
    (ha : A = 1 + t * (A*r + 3*A + B))
    (hb : B = 1 + t * (B*s + 2*B + A))
    (hL : L*(1-r) = A) (hR : R*(1-s) = B)
    (hE : E = 1 + 2*t*(L+R))
    (nr : 1-r ≠ 0) (ns : 1-s ≠ 0) :
    (1-4*t)*(1-5*t)*E^2 = 1-t := by
  have ar : t*A - t*r*B = r := by
    calc
      _ = r + r*(A - (1+t*(A*r+3*A+B))) - A*(r-t*(1+3*r+r^2)) := by ring
      _ = r := by rw [← ha, ← hr]; ring
  have bs : t*B - t*s*A = s := by
    calc
      _ = s + s*(B - (1+t*(B*s+2*B+A))) - B*(s-t*(1+2*s+s^2)) := by ring
      _ = s := by rw [← hb, ← hs]; ring
  have ratio : ((1-r)*(1-s))*E = (1+r)*(1+s) := by
    rw [hE]
    calc
      _ = (1+r)*(1+s) + 2*t*(1-s)*(L*(1-r)-A)
            + 2*t*(1-r)*(R*(1-s)-B) + 2*((t*A-t*r*B)-r)
            + 2*((t*B-t*s*A)-s) := by ring
      _ = (1+r)*(1+s) := by rw [hL, hR, ar, bs]; ring
  have rr : (1-5*t)*(1+r)^2 = (1-t)*(1-r)^2 := by
    calc
      _ = (1-t)*(1-r)^2 + 4*(r-t*(1+3*r+r^2)) := by ring
      _ = (1-t)*(1-r)^2 := by rw [← hr]; ring
  have ss : (1-4*t)*(1+s)^2 = (1-s)^2 := by
    calc
      _ = (1-s)^2 + 4*(s-t*(1+2*s+s^2)) := by ring
      _ = (1-s)^2 := by rw [← hs]; ring
  apply mul_left_cancel₀ (pow_ne_zero 2 (mul_ne_zero nr ns))
  calc
    ((1-r)*(1-s))^2 * ((1-4*t)*(1-5*t)*E^2) =
        (1-5*t)*(1-4*t)*(((1-r)*(1-s))*E)^2 := by ring
    _ = (1-5*t)*(1-4*t)*((1+r)*(1+s))^2 := by rw [ratio]
    _ = ((1-5*t)*(1+r)^2)*((1-4*t)*(1+s)^2) := by ring
    _ = ((1-r)*(1-s))^2 * (1-t) := by rw [rr,ss]; ring

-- Apply the elimination to the actual row sums.
open PowerSeries in
private theorem oaEvenMain :
    (1-4*X)*(1-5*X)*(PowerSeries.mk (fun m => (rowSum (2*m) : ℚ)))^2 = 1-X := by
  let r := oaKernel 3
  let s := oaKernel 2
  let L := oaHalf (oaLeft 0) r
  let R := oaHalf (oaRight 0) s
  let E := PowerSeries.mk (fun m => (rowSum (2*m) : ℚ))
  have hl := oaHalfLine 3 r (oaKernel_eq 3) oaLeft oaLeftStep
  have hr := oaHalfLine 2 s (oaKernel_eq 2) oaRight oaRightStep
  have comb : E = 1 + 2*X*(L+R) := by
    apply oaEvenFromHalves (oaLeft 0) r (oaRight 0) s
    · intro m k
      rw [← hl k]
      simp only [oaLeft, oaProfileSeries, coeff_mk]
    · intro m k
      rw [← hr k]
      simp only [oaRight, oaProfileSeries, coeff_mk]
  have coeffNe (p : PowerSeries ℚ) (hp : constantCoeff p = 0) : 1-p ≠ 0 := by
    intro e
    have h := congrArg constantCoeff e
    simp [hp] at h
  apply oaEvenAlgebra X r s (oaLeft 0) (oaRight 0) L R E
  · simpa only [r, map_ofNat] using oaKernel_eq 3
  · simpa only [s, map_ofNat] using oaKernel_eq 2
  · simpa only [hl 1, pow_one] using oaLeftBoundary
  · simpa only [hr 1, pow_one] using oaRightBoundary
  · exact oaHalf_mul _ _ (oaKernel_zero 3)
  · exact oaHalf_mul _ _ (oaKernel_zero 2)
  · exact comb
  · exact coeffNe _ (oaKernel_zero 3)
  · exact coeffNe _ (oaKernel_zero 2)

-- Recover the full generating series by interleaving even and odd coefficients.
open PowerSeries in
private theorem oaFullAlgebra (a : ℕ → ℕ) (a0 : a 0 = 1)
    (dbl : ∀ m, a (2*m+2) = 2*a (2*m+1))
    (E G : PowerSeries ℚ)
    (hE : E = PowerSeries.mk (fun m ↦ (a (2*m) : ℚ)))
    (hG : G = PowerSeries.mk (fun n ↦ (a n : ℚ)))
    (heven : (1-4*X)*(1-5*X)*E^2 = 1-X) :
    (1-2*X)*(1-5*X^2)*(1+2*X*G)^2 = (1+2*X)*(1-X^2) := by
  let D := expand 2 (by decide) E
  have Dcoeff (i : ℕ) : coeff i D = if 2 ∣ i then (a (2*(i/2)) : ℚ) else 0 := by
    simp only [D, coeff_expand, hE, coeff_mk]
  have shift (n : ℕ) (F : PowerSeries ℚ) : coeff (n+1) (X*F) = coeff n F := by
    simpa only [pow_one] using coeff_X_pow_mul F 1 n
  have Y : 1+2*X*G = (1+2*X)*D := by
    rw [show 1+2*X*G = 1+(X*G+X*G) by ring,
      show (1+2*X)*D = D+(X*D+X*D) by ring]
    apply PowerSeries.ext
    intro n
    cases n with
    | zero =>
      have zeroX (F : PowerSeries ℚ) : coeff 0 (X*F) = 0 := by
        rw [coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X, zero_mul]
      simp only [map_add, zeroX, Dcoeff]
      simp [coeff_one, a0]
    | succ m =>
      simp only [map_add, shift, hG, coeff_mk, Dcoeff]
      have z : coeff (m+1) (1 : PowerSeries ℚ) = 0 := by simp [coeff_one]
      rw [z, zero_add]
      by_cases even : 2 ∣ m
      · have odd : ¬ 2 ∣ m+1 := by omega
        have half : 2*(m/2) = m := by omega
        simp [even, odd, half]
      · have next : 2 ∣ m+1 := by omega
        have half : 2*((m+1)/2) = 2*(m/2)+2 := by omega
        have old : 2*(m/2)+1 = m := by omega
        simp only [if_pos next, if_neg even, add_zero, half, dbl, old, Nat.cast_mul, Nat.cast_ofNat]
        ring
  have scaled : (1-4*X^2)*(1-5*X^2)*D^2 = 1-X^2 := by
    have h := congrArg (expand 2 (by decide) (R := ℚ)) heven
    have c (m : ℕ) : expand 2 (by decide) (m : PowerSeries ℚ) = m :=
      map_natCast _ m
    have c4 := c 4
    have c5 := c 5
    norm_num at c4 c5
    simpa only [map_mul, map_sub, map_one, map_pow, expand_X, c4, c5, D] using h
  calc
    _ = (1+2*X)*((1-4*X^2)*(1-5*X^2)*D^2) := by rw [Y]; ring
    _ = _ := by rw [scaled]

end A026765Proof

open OMA.S_oeis_a026765 A026765Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a026765.main := by
  exact oaFullAlgebra rowSum rowSumZero evenRowDouble _ rowGF rfl rfl oaEvenMain
