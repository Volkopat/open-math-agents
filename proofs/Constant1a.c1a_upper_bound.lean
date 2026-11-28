import FormalConjectures.OptimizationConstants.«1a»
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Algebra.BigOperators.ModEq

/-! A nonnegative step function gives the upper bound on the Sidon
autocorrelation constant. Its autoconvolution is linear between grid points.
At the grid points the values are the weighted discrete convolution
coefficients, which the kernel checks simultaneously as the digits of a square. -/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConstantCell

noncomputable def wideCell (h i x : ℝ) : ℝ := (Set.Icc i (i + h)).indicator (fun _ => (1 : ℝ)) x

noncomputable def cell (i x : ℝ) : ℝ := wideCell 1 i x

theorem wideCell_nonneg (h i x : ℝ) : 0 ≤ wideCell h i x := by
  classical
  by_cases hx : x ∈ Set.Icc i (i + h) <;> simp [wideCell, hx]

theorem measurable_wideCell (h i : ℝ) : Measurable (wideCell h i) :=
  measurable_const.indicator measurableSet_Icc

theorem integrable_wideCell (h i : ℝ) : Integrable (wideCell h i) :=
  (integrableOn_const (C := (1 : ℝ)) (by simp [Real.volume_Icc])).integrable_indicator
    measurableSet_Icc

theorem integral_wideCell (h i : ℝ) (hh : 0 ≤ h) : (∫ x, wideCell h i x) = h := by
  change (∫ x, (Set.Icc i (i + h)).indicator (fun _ => (1 : ℝ)) x) = h
  rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, mul_one,
    Real.volume_real_Icc_of_le (by linarith)]
  ring

theorem memLp_wideCell (h i : ℝ) (p : ENNReal) : MemLp (wideCell h i) p :=
  memLp_indicator_const p measurableSet_Icc 1 (Or.inr (by simp [Real.volume_Icc]))

theorem intervalIntegral_wideCell (h i a b : ℝ) (hh : 0 ≤ h)
    (ha : a ≤ i) (hb : i + h ≤ b) : (∫ x in a..b, wideCell h i x) = h := by
  have hab : a ≤ b := ha.trans ((le_add_of_nonneg_right hh).trans hb)
  rw [intervalIntegral.integral_of_le hab, ← integral_indicator measurableSet_Ioc]
  calc
    (∫ x, (Set.Ioc a b).indicator (wideCell h i) x) = ∫ x, wideCell h i x := by
      apply integral_congr_ae
      filter_upwards [(volume : Measure ℝ).ae_ne a] with x hxa
      by_cases hx : x ∈ Set.Icc i (i + h)
      · have hx' : x ∈ Set.Ioc a b :=
          ⟨lt_of_le_of_ne (ha.trans hx.1) hxa.symm, hx.2.trans hb⟩
        simp [hx']
      · simp [wideCell, hx, Set.indicator_apply]
    _ = h := integral_wideCell h i hh

theorem cell_nonneg (i x : ℝ) : 0 ≤ cell i x := wideCell_nonneg 1 i x

theorem measurable_cell (i : ℝ) : Measurable (cell i) := measurable_wideCell 1 i

theorem integrable_cell (i : ℝ) : Integrable (cell i) := integrable_wideCell 1 i

private theorem wideCell_product (h T i j : ℝ) :
    (fun x => wideCell h i (T - x) * wideCell h j x) =
      (Set.Icc (max (T - (i + h)) j) (min (T - i) (j + h))).indicator
        (fun _ => (1 : ℝ)) := by
  classical
  funext x
  have hx : x ∈ Set.Icc (max (T - (i + h)) j) (min (T - i) (j + h)) ↔
      T - x ∈ Set.Icc i (i + h) ∧ x ∈ Set.Icc j (j + h) := by
    simp only [Set.mem_Icc, max_le_iff, le_min_iff]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
      exact ⟨⟨by linarith, by linarith⟩, h₂, h₄⟩
    · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
      exact ⟨⟨by linarith, h₃⟩, by linarith, h₄⟩
  by_cases h₁ : T - x ∈ Set.Icc i (i + h) <;>
    by_cases h₂ : x ∈ Set.Icc j (j + h) <;> simp [wideCell, hx, h₁, h₂]

theorem integrable_wideCell_product (h T i j : ℝ) :
    Integrable (fun x => wideCell h i (T - x) * wideCell h j x) := by
  rw [wideCell_product]
  exact (integrableOn_const (C := (1 : ℝ)) (by simp [Real.volume_Icc])).integrable_indicator
    measurableSet_Icc

/-- The overlap length forms a triangle centered at the sum of the cell midpoints. -/
theorem integral_wideCell_product (h T i j : ℝ) :
    (∫ x, wideCell h i (T - x) * wideCell h j x) = max 0 (h - |T - (i + j + h)|) := by
  change (∫ x, (fun x => wideCell h i (T - x) * wideCell h j x) x) = _
  rw [wideCell_product, integral_indicator_const _ measurableSet_Icc, smul_eq_mul, mul_one,
    Real.volume_real_Icc, max_comm]
  congr 1
  rcases le_total T (i + j + h) with hT | hT
  · rw [abs_of_nonpos (by linarith : T - (i + j + h) ≤ 0),
      min_eq_left (by linarith : T - i ≤ j + h),
      max_eq_right (by linarith : T - (i + h) ≤ j)]
    ring
  · rw [abs_of_nonneg (by linarith : 0 ≤ T - (i + j + h)),
      min_eq_right (by linarith : j + h ≤ T - i),
      max_eq_left (by linarith : j ≤ T - (i + h))]
    ring

theorem integrable_cell_product (T i j : ℝ) :
    Integrable (fun x => cell i (T - x) * cell j x) :=
  integrable_wideCell_product 1 T i j

theorem integral_cell_product (T i j : ℝ) :
    (∫ x, cell i (T - x) * cell j x) = max 0 (1 - |T - (i + j + 1)|) :=
  integral_wideCell_product 1 T i j

/-- On an affine grid the common width scales the overlap, and the origin shifts the center. -/
theorem integral_gridCell_product (a h T i j : ℝ) (hh : 0 < h) :
    (∫ x, wideCell h (a + h * i) (T - x) * wideCell h (a + h * j) x) =
      h * max 0 (1 - |(T - 2 * a) / h - (i + j + 1)|) := by
  rw [integral_wideCell_product, mul_max_of_nonneg _ _ hh.le, mul_zero]
  have he : T - (a + h * i + (a + h * j) + h) =
      h * ((T - 2 * a) / h - (i + j + 1)) := by
    field_simp [hh.ne']
    ring
  rw [he, abs_mul, abs_of_nonneg hh.le, mul_sub, mul_one]

/-- The two triangles whose supports contain a noninteger point give the interpolation weights. -/
theorem triangle_grid (i j k : ℤ) (θ : ℝ) (h₀ : 0 ≤ θ) (h₁ : θ ≤ 1) :
    max 0 (1 - |(k : ℝ) + θ - ((i : ℝ) + (j : ℝ) + 1)|) =
      (if i + j = k then θ else 0) + (if i + j = k - 1 then 1 - θ else 0) := by
  by_cases he : i + j = k
  · have hc : (i : ℝ) + (j : ℝ) = (k : ℝ) := by exact_mod_cast he
    rw [if_pos he, if_neg (by omega), add_zero, hc]
    rw [abs_of_nonpos (by linarith : (k : ℝ) + θ - ((k : ℝ) + 1) ≤ 0),
      max_eq_right (by linarith)]
    ring
  · by_cases he' : i + j = k - 1
    · have hc : (i : ℝ) + (j : ℝ) = (k : ℝ) - 1 := by exact_mod_cast he'
      rw [if_neg he, if_pos he', zero_add, hc]
      rw [abs_of_nonneg (by linarith : 0 ≤ (k : ℝ) + θ - ((k : ℝ) - 1 + 1)),
        max_eq_right (by linarith)]
      ring
    · rw [if_neg he, if_neg he', add_zero]
      apply max_eq_left
      rcases le_total (i + j) k with h | h
      · have hc : (i : ℝ) + (j : ℝ) + 2 ≤ (k : ℝ) := by
          exact_mod_cast (show i + j + 2 ≤ k by omega)
        rw [abs_of_nonneg (by linarith : 0 ≤ (k : ℝ) + θ - ((i : ℝ) + j + 1))]
        linarith
      · have hc : (k : ℝ) + 1 ≤ (i : ℝ) + (j : ℝ) := by
          exact_mod_cast (show k + 1 ≤ i + j by omega)
        rw [abs_of_nonpos (by linarith : (k : ℝ) + θ - ((i : ℝ) + j + 1) ≤ 0)]
        linarith

end ConstantCell

namespace CellCertificate
open Finset

def coeff (n : ℕ) (w : ℕ → ℕ) (k : ℤ) : ℕ :=
  ∑ i ∈ range n, ∑ j ∈ range n, if (i : ℤ)+j=k then w i*w j else 0

private lemma weighted_digit {ι : Type*} (s : Finset ι) (e w : ι → ℕ) (q j : ℕ)
    (hq : 2 ≤ q) (hs : (∑ x ∈ s, w x) < q) :
    ((∑ x ∈ s, w x * q ^ e x) / q ^ j) % q =
      ∑ x ∈ s, if e x = j then w x else 0 := by
  classical
  let lo := s.filter fun x => e x < j
  let mid := s.filter fun x => e x = j
  let hi := s.filter fun x => j < e x
  let W := ∑ x ∈ mid, w x
  have hpos : 0 < q := by omega
  have partial_le (t : Finset ι) (ht : t ⊆ s) :
      (∑ x ∈ t, w x) ≤ ∑ x ∈ s, w x := sum_le_sum_of_subset_of_nonneg ht (by intros; omega)
  have hlo : (∑ x ∈ lo, w x*q ^ e x) < q ^ j := by
    cases j with
    | zero => simp [lo]
    | succ j =>
      calc
        (∑ x ∈ lo, w x*q ^ e x) ≤ ∑ x ∈ lo, w x*q ^ j :=
          sum_le_sum fun x hx => Nat.mul_le_mul_left _ (pow_le_pow_right' (by omega : 1 ≤ q)
            (Nat.le_of_lt_succ (mem_filter.mp hx).2))
        _ = (∑ x ∈ lo, w x)*q^j := by rw [sum_mul]
        _ < q^(j+1) := by
          rw [pow_succ, Nat.mul_comm (q^j) q]
          exact Nat.mul_lt_mul_of_pos_right ((partial_le lo (filter_subset _ _)).trans_lt hs)
            (pow_pos hpos _)
  have hmid : (∑ x ∈ mid, w x*q ^ e x) = W*q^j := by
    rw [show W = ∑ x ∈ mid, w x from rfl, sum_mul]
    exact sum_congr rfl fun x hx => by rw [(mem_filter.mp hx).2]
  have hhi : q ^ (j+1) ∣ ∑ x ∈ hi, w x*q ^ e x := by
    apply dvd_sum
    intro x hx
    exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow _ (Nat.succ_le_of_lt (mem_filter.mp hx).2)) _
  obtain ⟨u, hu⟩ := hhi
  let rest := s.filter fun x => ¬ e x < j
  have hrestMid : (rest.filter fun x => e x = j) = mid := by
    ext x
    simp only [rest, mid, mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, by omega⟩, h.2⟩⟩
  have hrestHi : (rest.filter fun x => e x ≠ j) = hi := by
    ext x
    simp only [rest, hi, mem_filter]
    exact ⟨fun h => ⟨h.1.1, by have := h.1.2; have := h.2; omega⟩,
      fun h => ⟨⟨h.1, by omega⟩, by omega⟩⟩
  have hsum : (∑ x ∈ s, w x*q ^ e x) = (∑ x ∈ lo, w x*q ^ e x) +
      (∑ x ∈ mid, w x*q ^ e x) + (∑ x ∈ hi, w x*q ^ e x) := by
    have hfirst := sum_filter_add_sum_filter_not s (fun x => e x < j) (fun x => w x*q^e x)
    have hsecond := sum_filter_add_sum_filter_not rest (fun x => e x = j) (fun x => w x*q^e x)
    rw [hrestMid,hrestHi] at hsecond
    rw [← hfirst, ← hsecond, add_assoc]
  have hupper : W < q := (partial_le mid (filter_subset _ _)).trans_lt hs
  rw [← sum_filter]
  change ((∑ x ∈ s, w x*q ^ e x) / q^j) % q = W
  rw [hsum, hmid, hu, pow_succ, mul_assoc, add_assoc, mul_comm W, ← mul_add,
    Nat.add_mul_div_left _ _ (pow_pos hpos _), Nat.div_eq_of_lt hlo, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hupper]

theorem coeff_le_of_digits (n q U X : ℕ) (w : ℕ → ℕ) (hq : 2 ≤ q)
    (hs : (∑ i ∈ range n, w i)^2 < q) (hX : (∑ i ∈ range n, w i*q^i) = X)
    (hb : ∀ j < 2*n, (X^2 / q^j) % q ≤ U) (k : ℤ) : coeff n w k ≤ U := by
  classical
  by_cases hk : 0 ≤ k ∧ k < 2*(n : ℤ)
  · let a := (range n).product (range n)
    let wt (z : ℕ × ℕ) := w z.1 * w z.2
    let expn (z : ℕ × ℕ) := z.1 + z.2
    have hw : (∑ z ∈ a, wt z) < q := by
      rw [sq, Finset.sum_mul_sum] at hs
      simpa only [a, wt, product_eq_sprod, sum_product] using hs
    have he : (∑ z ∈ a, wt z * q^expn z) = X^2 := by
      rw [← hX, sq, sum_mul]
      simp only [a, wt, expn, product_eq_sprod, sum_product, mul_sum, pow_add]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
    have hd := weighted_digit a expn wt q k.toNat hq hw
    rw [he] at hd
    have hj : k.toNat < 2*n := by omega
    have hh := hb k.toNat hj
    rw [hd] at hh
    simpa only [a, wt, expn, coeff, product_eq_sprod, sum_product,
      show ∀ i j : ℕ, (i+j=k.toNat) ↔ ((i:ℤ)+j=k) by intros; omega] using hh
  · have hz : coeff n w k = 0 := by
      unfold coeff
      apply sum_eq_zero
      intro i hi
      apply sum_eq_zero
      intro j hj
      have := mem_range.mp hi
      have := mem_range.mp hj
      rw [if_neg (by omega)]
    omega

def digit (X q i : ℕ) := X / q^i % q

theorem digit_pack (X q n : ℕ) :
    (∑ i ∈ range n, digit X q i*q^i) = X % q^n := by
  induction n with
  | zero => simp [Nat.mod_one]
  | succ n ih => rw [sum_range_succ, ih, Nat.mod_pow_succ, digit, Nat.mul_comm]

theorem digit_sum (X q n S B : ℕ) (hq : 1 < q) (hX : X < q^n)
    (hmax : ∀ i < n, digit X q i ≤ B) (hl : n*B < q-1) (hS : X % (q-1) = S) :
    (∑ i ∈ range n, digit X q i) = S := by
  have sq : q ≡ 1 [MOD q-1] := by
    apply (Nat.modEq_iff_dvd' (by omega : 1 ≤ q)).2 (dvd_refl _) |>.symm
  have hr : (∑ i ∈ range n, digit X q i*q^i) ≡ (∑ i ∈ range n, digit X q i) [MOD q-1] := by
    apply Nat.ModEq.sum
    intro i _
    simpa using (sq.pow i).mul_left (digit X q i)
  have hu : (∑ i ∈ range n, digit X q i) ≤ n*B := by
    simpa using (sum_le_sum fun i (hi : i ∈ range n) => hmax i (mem_range.mp hi))
  rw [digit_pack, Nat.mod_eq_of_lt hX] at hr
  change X % (q-1) = _ % (q-1) at hr
  rwa [hS, Nat.mod_eq_of_lt (hu.trans_lt hl), eq_comm] at hr

private def checkDigits (q bound : ℕ) : ℕ → ℕ → Bool
  | 0, x => decide (x % q ≤ bound)
  | depth+1, x =>
    let scale := q ^ (2 ^ depth)
    checkDigits q bound depth (x % scale) && checkDigits q bound depth (x / scale)

private lemma checkDigits_sound {q bound d x : ℕ} (_hq : 2 ≤ q)
    (hc : checkDigits q bound d x = true) (j : ℕ) (hj : j < 2^d) :
    x / q^j % q ≤ bound := by
  induction d generalizing x j with
  | zero =>
    have : j = 0 := by simpa using hj
    simpa [this, checkDigits] using hc
  | succ d ih =>
    have hparts := Bool.and_eq_true_iff.mp hc
    by_cases h : j < 2 ^ d
    · have hh := ih hparts.1 j h
      have hsplit : x / q^j % q = (x % q^(2^d)) / q^j % q := by
        conv_rhs => rw [show 2^d = j + (2^d - j) by omega, pow_add]
        rw [Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
        obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : 2^d - j ≠ 0)
        rw [hr, pow_succ]
        exact Nat.dvd_mul_left _ _
      exact hsplit ▸ hh
    · have hj' : j - 2^d < 2^d := by rw [pow_succ] at hj; omega
      have hh := ih hparts.2 (j-2^d) hj'
      rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_of_le (by omega : 2^d ≤ j)] at hh
      exact hh

private def base : ℕ := 2^52

private def dec : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ
  | 0, _, _, _, _ => []
  | f+1, p, z, m, y =>
    if y % 16 < 8 then
      let z := z + y % 16 * m
      let x := if z % 2 = 0 then p + z / 2 else p - (z + 1) / 2
      x :: dec f x 0 1 (y / 16)
    else dec f p (z + (y % 16 - 8) * m) (8 * m) (y / 16)

private def pr (s : ℕ) : List ℕ → List ℕ
  | a :: b :: t => (a + 2^s * b) :: pr s t
  | l => l

private def pk : ℕ → ℕ → List ℕ → ℕ
  | 0, _, l => l.headD 0
  | k+1, s, l => pk k (2*s) (pr s l)

/- The integer heights come from the Together AI first-autocorrelation witness
at revision c388c6f, rounded to the nearest multiple of 1/30,000,000, stored as
zigzag differences in base-8 varint nibbles. -/
private def X : ℕ := pk 15 52 (dec 66245 0 0 1 0x698ab82e8ee69b8498c1dfa18ca29db2afb38ed299a6f859d2fcc1fcc6ba188979d1bcb3d84ce299a7f862fa3fd5a85da783be6985fc2bc7cf199928b5f1d882a8c68e19c1aaf1f9d19cf6ed198f38ba6992bbb1ab91ece1d9a19dc188c5af1ed3ee2bcb1cb7992fa1eea58849e5ae48a2eaf7fe29ef5cf4a8198a1edc19fe79d2dd91d991f8d2aaf4ca2eaa2eec7c83ec6ee29e5ca6fe5bc1a92d3db4c95da7bb5cf28ed18d81aac7fe1cbf28dfb59e8df4ee98e39c9a5fcc3f8c29ae7b84ecd4bc939ef1bea5ea5ff3cae2cba1a881ef91b9f6fd1b9e28c83b981de19896fb5b92be1b8a6ef4e1c885982cd5fb1df93cb1bdc7e84de4ac1ccc2af5f9189918f959f6a96cb1ccf1bdb3a8e2de81ae82e1fc82dd18af693b892bb1a9e2ad849e1df94a92bbe1bde3cdf2e9f3fd2aa6bc2aae4ec49b1ecd389f3adb3da928d83fec2dca6be5fe1cba4ce38f4ae1cfe4da2ea18b97df59288f1faf2eed1b9c1ef86b84c9d3a9af38a9db2eceac3fdce18cec1cf839e82eac4aaf4f9b49bb1ec1bf6b9389839dc28a81cab6d91bb18fe18fc3bc86885fb6cf3fe79e3eb2bdd5ed18cc1dca5c85ef1adf6b4cf4c85ce1d82ea3ab5f1df91ecf199f1f81abc3df1aab29882fba18fe1eeb1eea1cf1e992ce839db2fa1bda1ef84ae39cb1df91f8a3ff83bdb39d948b4ac58e1ac188a189c199b3dc92fab1ffb1eec38dc3bba1bb81bea7d819a4cf18bf5ac39a6ca1b8f1a9918b1cad28bf2de95b82dde1eb84ff938cfb1ecffd1db9f83fdca6ea81be839e82ed83d994ebd3fcb1b8b28cb7cb2dc838ba2cbe4a82bf1dc9181ada1f9e49c38c28859c3cc5c92ad91a991f19e84ec1b6c918b92ee18fc71aab5d81ff19fb5a94bd1add6e829ee1b9c2fa39858c198e1aad2cb1ce2cf2bba1ea48c2ec3e61aff6db3d82881bcb1ee97eb3fe4be1adc19e83dc18e2bf93bad3a8f1ca83ffa3c8e4ea4f2fe2fe3bd7ad38b29c19c81ca9199f1ae3fd78d1d8d7f1fda28ce388f289fb198af918da9a2baea2888438e83ffc1afb38a93bdd28df1fb91fab19fa2ee82cda38f1ab4fc1ad1cf6f8199a19ba18c199c1ec6cf1c891bb92bd1a9e79a4bd6f97b959c48c39c6bf4bd3af48a7828c48f7e85de59f1ed1fe18f81e9e28c2d92b82992882ca4dc1ff28f1da2f94cb49d5ab186fb6bd58e1a8e1b8c6ce4da1891c892dcd289f69e1c9e1c9e299199b6d949e6ea19a86ae1e68a4ed1b8d7ed48b4bb5ef1ea6f818ee1cdd18abd4dad94eb8e6dda7b18fa38ee28de2e91a9f1a891bdd19b97d81f9a1aea5cc49e5dc1aa5db5919c86da3885a3d3cf4b93ed19d29968a6ec4ff3a91dc6dc1ca1aa200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004d2bd1f829188d5f92a818ec4ac6000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001ebb3c8b1fea2cac2da2b91ef1b939d48d38969c6c81da1ca3ca387d39959d2ab6f3fd5cf18d3f85985ee2ce2fd1cf1d94c38948b78e18c819a1ff1cd1cb1fd23ff6bf72c828f1bd18a1e81de6a198a5fe281939d1fd5a4e8232af19c19c4000000000000000000000000001dd39b1ba29e681a1a1c288b2bb97c91e9a2f9e1ce2db7f959f49a58a7ec2918d95ad49a4e3887c2881c85ff1c9d299d4e97ea28b87da2f1bb5df5d92eb1f81a8b1a9d5e29d2ea18cc4a95fb6ff719aa19fe1aaa1dec1dcb1ead1c9f78f199c1eba18a81bae18a83d18e91ad69f7fe1aec5c8285a91dcd78a1bfe2004f1c918d18bd2ff1cce2980000029cb1b9f2ca2b3de18bc4ea2ee2fe19e2d812000003fbf688f4baf5aea188be7e80000000000000003991ee92cc93e2cde1e8c2ca481a32400001aff29ff29ac1bce678d4cb58f1cf4a28f1eba5c8401022000000000000000000000000000000000000000000000006e918cabb5fcea1ebac49ac2bdc49800006a92eef2bff1b882acc1c8e3981896ed1bfd2cdf3d8b3a93aca48d819de58c2be78758b7b3f87818129f19c281ca18dd1aa968b2ce1fe38b5f81fd6bf1bcf7dc1ecc38c19e1aee1e79f1de92bb6991d9289c1bae4c8218dd2fd92db1aa829918a86de1acc4b97cd6eb3a83895af5b3e8286ad1e86be18879c2e8691bb28b69f2ce18fc29f4fd6891ce4dc1dbe1b85eaf1baf8d7dcba2ebcc7dcc38aa7fc5ec28db4df2ff1ce2a9b48db1fb82dce1d8e5f6df3fd19b1afb1d9d3e1fac1faa3ea1d8e19fe3fc7c0000000001f7b94891da4da5a818518a93cb94b9f198a49e81ca81ee1dee6e91faf18a97e92884e81db81bb83ee1dbf1ebd1bfd29cb38c5f81e8e28da1cb818b92ebb39cd2981c9e18981a8a29e1acb5be18fc18fc4993ba29fe184cd3cd1b92986c819fd1da929cd3fc385e81c9d28bbf1aadc97b9ae3beea1b8be49c86d8189d3ab91fbd6ff4fc28bb299b1faa18bc4ac7978e19918a18bf4bf18ab4a2ab879c1efa1ac85bf5cc1eb81d8396e2c81fe82802b3fd1da97fd1db588189a1b8e1acb2fa94b9d3c9928ce58882e9e7ba4fe1d8b1f8d6ed1d8b4b819fc29d819f81b8b28e96cb1fe2ebd19ad1e1dec2afe1cfc6fb1cfb2aff7d92a82d1aee2a9e2aec1c884fa1da1eb3f96e91ce81afe283f2cf1ab28fb39cf3a9b6ae1bea58c2ee92caaf19ae8f78eca3ea881b9983aca7dc5aa38cd3adb2acb6d2eed3bbb29f83ffc2ff81ce499188f2ba3a938f7a91ecc2c8c784be1c879929b198e38a2f82d859c1af87a2eb19b3991d9f2e996fd1caa1dfc6be2baf39ad4bfb3cad39c8688a38b81acc7fa1bdd2bbf6e93cb1aae5d818fa4cc3df1aff1ecb6cb2d8f19ab6ab1ef82dd81dca1db1abf1ebd298b19ef49b1fde3a8c2dda19ae2ca29f5bf791a8198e69c19de6af1bab1aef3a992c992a8b2aa1bde2ca83beb2faf918bd896d9c848ade19fcc3bec2ea81aa838ff3bfb389d79b38893c8f1c9e3da83bee2be1ef4af3b84f1aca5d83d81bbe19e868a5cc5ed6ae1eca3a81bfd18bb18ae1a9819b84fd1ed92ab919891b9b3ab18ec1b9e5fc2aed299f2dcd1aff2ebc2ffa28bc1fc1a8e3ad1eb97e1ffd68b1ac1aee1aac4ff59b18ed1adb2fef2abd3ff1eba3ab82fd83c948b4ed2acd2abd2ca928d83a8c2cba3b8381ce1eb6b6892918ee2bfe48d5ad4e93aef39992acf4982adc2f883fed2ced96cb8b58cca3bcee18abc2fde2c8a2b8a28bf3fb92fd91fdf3ca93a9d1cdc4a8a4e9e1bcc6dc2ce3de2d849289684ac5f2ae189a1eb18ad2bf3da1991f8d39f29ca2cfa4ef2d9b28ad2dc4b91aaf1c8288c28fc1f9f198929c939cd1aae4c8c29fc4f3892d81b9d7f92fc1e859c3b84fc5bc1b81bdf2fcb28df18dd1ed1dbe2ba8289e2e81da3fe1fbd3daf2ec919a83ace3f8c5ec3a82cd1c991b8b1cf39f2ed1bfe18fa1dc28b1fcb3be928893ec1bae1fde2d9b1eefb49bed3ac982b8fa6dbc28e81dcc19ac1ca929bf19ed288b3bdf39ed6b83bae3e8829be19ae1c8a4ce18f18ea6da4dc681ff02f6bf5af5db3992ab2ed5fe448e6f84b7c919ef1a8f76ac7ae4e7af3ca7dd1f8918dc2c8c18ce2dd3993cc6cd28f3d939d36fc1acc4fe2de18ef2ac91fbf18fb1acf1ace2aee1dca6a381ac1abf1cab19ef1a981de81fdc4fc6c18b91bf94bd7fa392dd1ba3ba7c2fc6db2eef28af1a9e1eac2a389d18fd929ced1edee1ca9c4f986e81d8e6aa1bab1faf1bdd2bbd3c9b2ce919aa39dc38881ec87fc2d979f2bf19ca18ea281cb1997fc6cc4db198b7b97b4d68949e19dc7be1ad85ba7bb1edd1edd4fd59a6cc3b4f92eb6cd3b6dc1b8a7ca1cf3891b82997a939968c1aec5be3fa3e3cd1c93e93896c96eb19fa1baa4fa1d919a1e81ce92ad91ad91bde1ee81e8c18fa2984b91cfb198f68a3e82fb6581cd1c91b9b288f181ece5ac6ff29b95b8b1a8cd19fbe18ace38ec4ea39a3bc6ff1bff18ed1d892bdb1eb97bc2aac2f8c18aa48c2882bf2fe7ca1ac2e92df1c18c1ef7d3a948d1cf3fb4cd3ae19b81aec3ec5e1bf6ff69f5cd2c258d3b929c6dc2ca6ba1be691c81ca1aa38f1ccb6996b818be4b86c86dc1d84af18af2eb5eb1b9b18aa188c1991dc4e81dc1aef1bd97d949e4ba2fa4f849e7ac18ef29fb6bf6ea1bb19bf2e1c87bf1def3f5d87fa59c5d1dcb2bad4bd9699c4faa59a7e6ce4bc48b38b28b1ccb28cd2afd1f9c2adc1dbe4b7b188a69e2dc6de29a59d1ccd3ed4c3d58b1984aa7a979d2cd29e18ce6981b38f74ae4983bc39c5881f18e3f86a0000000697ad581d81aa2fa21f92ee4e318bd2df7cb5fe4b818a21fd5af7af1d9b1deb3b85ec6fa19e85ea7b188d1cdf1e9d2bc2bd2ad68a5cc3991eb5c2ed4fa18de3fd1caf3ef18ad3eaa288e7ad3de5d828918c3cc29f3ad1bed2cdd1b9a2ca81fcc5c18bb6ef3cc5f829d48c4ba2ab791bf2c92ba18b58b1cd1df2f94994c86fa4f96f18986ea2f2ed395dc49c291a4948d691eb3ae488285d1893af2c82c8180000006d1bf1cbb1e81fd6b1cf794a8418891dfd297fa1bbc19ee4ce5f189d68b4eb3ae559b26e1db1a934aa39819ca2dd1bef5fe19ea7c87800000002ab18bf18eb1dd49c1afc1c5db2f92cb3de1d1ab7ba2ca49a1b2f7ad7cb6938c5d82ea3fb2f93a94ff1fe1ccc4ac4d38f3e81ba2eb5ff5af53ce2ba1f3df1b4d1aad68f6dd1b8e1cb81c9c01891ac581e004bb1ded1aa59e5ce13cb3c84881cb1ccd18cf6ca79c6a81d3fd3fa5a81876fd1f8f3ef59e59d6f5aa6ca18ee1bc6bf69b29c69198e5ca18e3a20000000000000000000000000000000000000000034bf3e5849f7991c8919b94af2cd1c9f3aca2aba69a4a81c06f3e94be291893af18af19b1bee2ac28213e91f8d4a9199c1aee693fa200015b928dd3991ada1ae18f3be7a1d18d1991ae4ec5cc4b69f1cdb4ab4de1dac4ec28f6a958859c0188b1ed95d1bea4ba39a2ca1c84d6fd48b7cc39a7c201294f93896c94cd3de188a29c18e1a3cc484794b1b9198f7eb1d997ee3cc1919cd1fff1c991cc919a91dfb4a9a2ecc1afc4a81ce3891ff19eb6d819a83a691d9b1ae91da2ba18de2ee18be1ee5dd18cd3ea1bdc39a3a84e84de28862e91cdf28ad6cd1cec6ba1bb91acf2b85dc39c7de18fe2d869d18ed6eb1bdd4ef5b81eca19985fa2ad3dc4de48a4bdb6d91e8c28b81cd5f92da2c83cc2bd6188e2ae29d4d96386b5fb1f3cb3c1ea5be5b2a918c61d829c4fc3ea19e1f991ccb1c8b18ea5cc2b86eb1c9d19eb1fad1fab1bbf5dbc3efe1faa4c18ef1be92b29ff7c818cc4e1ac828fb1add7ee4cc18da2ab2b85be29b1cfb1de28ce5c1ff19de2fa5cb1dcb3ff1db59f5ff59e1ea7e91897a86cc5a2de4ae3ee58b1aaf5fb1bb5ee78e1bcc4ba2a919a91ed3f86da58cb5c92d8a28a87e4d96ea3fe1b82d4c39c1e93c919bf59f1ac3dc1a1ead2ecb7d1a987be2cc7fc1c94cb2286be5dc79c1fbb29ed28cf28dc1db85da6b94b918f198f28dd1ddf5bda2baa3da58199b292a82c891cba4ba5f1f9e2baf5c97fa39c1f8198b5dd1afc1dde19e919f1d8e1da7993df3ee7cd1fff4bc1dc1de68b4d85f7c4ec7fa6e3cd4cc2aa1ae1aff6a92c939b19b86de4ab1bb29a1dab7db6fd6a93e9f6e84ce82cca3bb5ed2d28d6d2d4af1d5ea3ba48b2ef18a2da58b2aa9299f5ef1b981dfc19885f8797c5de6de6a78c28b869d1fb92eb91de82caa5cc1aed18eb79f1dfb1cdd19fd3cde1b983b3f1d919be78e7cb2c83af7fb7c4af4eb5bc1fba19be19991f992ee1acc19ad18db18da49e6992ac4881dcf2bbf2ef6a2cd19f1aa869a189a6be4f81ac2b18ce18e38c1ca97b9582da6ac2ad1aa92bb2f81dcb2a8f2adb49992893adc6e9a39a84bc1e848f198d5ab2e1b9d18e9188839e4cd3d93e1b859f1bb928ad3ab1bcc1eee1dfc1daa3ec18b49c5987be18ac6c1c9f6996cf5b84ba29a4bb18ef289b1dcf3fb39c2bfa7818ff19896b1bc81fac2b85be1bdf2a9919ab2fd2af19ac1dfa1df82881dc91ba93e92bb29b381dd3ea7ae18f84cd29b9392b18df181fcc7f818887f818ca188c3ab1c9f69839a19995b958e4e7fd6bb1ecf19af3c829fc1cad19d992a8dd1eb885dac7de83cd81c9a79819d91ca91f8d068d1e8d3f18ea3ce18a7a2eb59919ff1d9b1be94b82a9e2cba29da7fc298682f83c1b83ec18ad1af49a281f95eb3b93cb4fb7b929f18ca5ec1cc1dc92baf28b1d8c1ece383b85d9289f1fd2883cd4a87da1cac58a1acb29ef18891a8d1a1c9e3c81ec3fc7cc4b19db1bc91be93cf4f828d81cbe1b9a6ea7fa58c79d19b91bb3f282ad481ae49f1ccd28ad3bf1aec7ec2dc91a9bd28ecb1ceda7fda18eac38ea79c4a84cd28ab2ccf3df19a95995fc1bac19da7ae3c81d81fe3cd18cd18bd3ae1fbe1ffe1eca18b82af4fd4929b2ef2ad1e8b7bd19ee68e5b96ef2ff59d18e4985de1ac86aa4e929cb2ea91e288e2a985ee18c7891cdb291eb189f1df3981c8c69a3bb288d19d96fb16fe4aa7ca1b9a18aa2d9188d19991ceb1dab18d1eec2a981bea59a3bc6ce1adb19df2ae2cc1983996b2b818cd1bff18cd4f3a873afd19cab1dfcd1cbb8199cc7eec38983ce19e1a892c8f29ff7cb1ec91faf2c91f9e1da81bbc6da38f4cf1bdd1dab3cf6b81ecc1cee19da3ee1c82a82af5a93bd59e1cc5e5de7ae5a5f4d92bdd1dc96918ee1bce2b83d91dcd2a8f3828fc1bae2ad5db4ed7ad2d2ba2e92a84f878a5db6bb1adb19dd1dad791dbe1abe7fa1aba1b8c4cc6d1be92adb2bef7a2af828ba1ba81ab84f819d69d3cf1a9f1aa6fc29f7c93e1e918ab1baf3df3ee3f838ef18ded1c89d1a9cc18efe78be29de7d83981d992edb28fb1ded19d93d1a19fc199c29a829ae5f4ff19fd4ff1a858c1dbe1efc1bb8188a4a1ff3ab4bb4fb2dd4dc2fc2aa5be3ae3f91a9b1ad91aeb2f92bc18c3f94cd5af5ef1a8a2afc18dc7b189b68d5cd7f6df5ed4ac3b85ca29a4bf1bc91b9f299d3cd1cbe6ac1a9a1dae18a84bc7c19eb1dab3ff2e1de2e69a1acc6ae4982ae1de199d7d918c3b919d2aa1bc91eb97f96be6bc7fa29cf78bf19bc918a8c7dea4fee1afc18985881bfb2a991ee92bdb28af7b2ae1baa2ac82c8a1cac4e81da5ed29b1ed1b8198a18da6f83de2eb7b3d92eb18ef6bd19ba7982ae1bc82da19f918bf6eb6cd49928b4db2eb1da3aa4a92ae29c81baa3df19e94994bd7e3e901cc3fc2dc48f19af1f8d1adb68f1b81fac1fbc19ea2ec1a1dc18bb18ff7c93bf3dc1c869a18ac4ca7aa1cf18cf7ef49f49d2e4cc2fc199198b7ef3fb4de38e2b1d8b58bf5ffd7a9868ce2ebc3985ae6ae68919f919df1e991acf7fb3a81d9828ca1b9e7ec4ba1aa1a28a2fd6b91c94ae48a1aa1bd29f2eb6a2fd58d4fa59848a6f82b7f78b18a96ad29d38a2db1fd4bb48e2fc18ea1ada1cc1e84a1ee4fd391a8f3c92a91b4c86f5fd19c93bb4ba18cc1a986fe1ca1bb429c1ad918cf1cb94d94f81ce1a7ac7fe7a83879f1bcb1aad1f968e6e5ff6c19f1992a3db1993b7eb38fb3fed5ace58ce2afe2fe7da2b918e9198d5c95dd19ed2df3991eba2a8a1cac1fc29c5b5c7ce4a86eb199b2ec3ca4c5d83da4ad6ef1bb1bc38c3ae38b4cc5d81d87bf198f1cad5fd5bf6e938e28f19da6de1dce1b985ae4ca2fc4f4ef7dc1aef5f96fd6d93ac3ec6f819c1ebf18ad3ca49c1fae78e5a95a1a83bf5dd1d9b1af929e2bf28c1b8879819de181cad1f9f1ba91885c82ec19ab6f18e81883db29a3fe1cb198b1dc91eed3ade3be8298e28a2b59d4ff7cb1881a8959f18ed3d818b81b9e191eba3be189d6af188f2bc58c2bf2cc2ea2d83eb4ad79b28c05c18985982c1abc2fe6cb7cd6f918fb2bb4fb18cf3fe5ba1ba84de18b82b83ea6fe3e1ed4b6a81ee918b96f91de4ac18c828f18e1a8d6c9585ab1d9a1d9a2ba6e3997bd7991bbb7ed19ee4dc4f188e4ce48f5c5eb7ad19eb7c93a5de1c95d1a9c3fc4992de198e6a878d29dd1bdf3cce2fe819a81c1ab189d4d939b31bf7ad78b1fac491fd4fe49e3883895d4bd68f5a95894cc69e1abe7c85b18af19f19f2dc2d91eb2e94d842c92c93d19884ae2db29ef1f1a868c4db3ca3e85ec4f829d1981d92e92e9d5af6a6be7be2cb1cd4ce1add1dd1bac5d91c8c687ed28f49e1ee7df19ff19b929b85de1e8d28f199e6818d38879a18ed1abf199d2eb1bc7885be4a48687a83db4b94d91ac2bf81fa84c81bbb19ab5c94b95bf7fe3f81cf4e918ca5d2a29c79e18c81cc1fb1ad49b2eb1bd3af1aa1a9c3d819d7af69b18aa189e59c4c4e93f2cd6ce1886bd19af451dff2a7be1e885e958d1de1ee3896fb1d93f5ac1cad1d2dc2aa4ba5eb2cb39a68b1be5be18d95ae5e81ce6fd3a2be68c189f2fcb19ee29d86e7818c83ca2ef1ae5a87e91d93a94ff6fd18f6b82b83ad1ee2fc1da6e83ed4e82b85cd4af49d38a1d9c2a81abb2d19a1a8a1bac1838d29b92df5ee1849f494da3da4cc3f81ae97ed1df1aba4c87d3cc1ca4dc1cc1dd1f7991a8f6c4ca38b5a93ed6997cb29e39a78a59a6ea18f4db5d91b93b7994d6aa18ac6cc48a4ef1cfb19994dd6ea188c18de1eee2c48a4c5c96ef7a3ee19e918b97b1b981dfc1c97eb5c9185e85cc1dc91dcd3b82ac3ad1ca1bd5f83ae1ea1f198d29c3b93fb1d81c82cf3ee1bca7ec4987e1cf1ca4ec007918a92ae1db91bdd2ff781aaa395ce1cf81c84ef2891d838f2a91d936ea6cc28c3dd3dd2db2db3b69f19a91a1eb4df3d69f28b1fca289e1f5f95ef4dd7bf1c8d28992cca1ada19fa1dea58d28cb1bf91ba96ca1ad81c981cf8188928d18f1881bd1fe4a82ad68d18b81cca1ec4aa5e11cf188b1a8b3b94f4f96db1ac2de2be2de3b1b94c919cf618c28f7a5ab49b2ea29bc2cea1abe2a0000018cf28bd18f19d6d919b3ca5fc1df3c878a58a11bb2cb2993f3ef1ac9199f6c81aae2fe1ad1df3af2ef3891be5c3895b92ce49d1df91cae29ca3f7cf595cd18df1daf1fd928ec1bd87981b8e1f1aaf1db9198b1db81aea19ea2919cb4d6b81db84e818d9199d58e1ea1cf2e7d879838929d3cf5ed6a92cd38f59f381fe2d1ca3de3ca5ac4ce1fdb4e9781996e1eb6cb3eb5be1aa879c1ac198e4aa591aa7b1ecb3dd4f8792fd2bd4ea1b882ed5b4ec5fe38d6cd79b5eb3b938d2ab5a93f93c5b819ae1b6dd2ae1ca2aa69c39a68f6a38c19ab7b7de5ee7f94db189b1af91bbd79928887fc198a1cae3b6e91fb3a95cc183b819b85cd78f196fc1f7f5bb1f3b84fa1b96fd7a694d5a83d1e8958d2984fa3a2a97b4e82a829c1b92bc19e7be48f2a9f1acd3ba2c83af2af18ac1bea5bc6d87b5d93af2ba3dd5f39a18f19c6ba1adc4f81af7cb6993fa1e3ca39d4f93ac494ab4af3a94a8268b1b488582eb1ea18bc4b8188d1db93c91d83ae2fe3bb6cb2982bc199918bf2c1b9a3ec7b19d7b22b95cb1a9c1ba7bd38f48f58e7ce1bdc5ca2ef18ad2ab39a4e839d5e97f5f1ab3f6e91da91b3ba4fc79a7de2fc5be4e18f1b6d918ad7d82bb6ff2891ee2d1de5ac1983cf1cf1ad3991aeb2d91b8c1f85dc1bd82f78f39a68e3fd4f1fa4ff6dc7d5fd19cf68f19c1ff285fb5c91a5dc18ec4da6a74ff1fc1fa29e01bb92ef7ca294c948b3f95cb58d38d4c6ec1bec2ae189f6eb4839c68c48a7bc2cb38d2e693ad2f818ee3da2ff68f3df568c3ac3e91fd4bf2881ba5e91bcd7df18d48c6fe1bda1bc82ee18868a3b7ed1ba92ff1d38f683e18b39c29c58f1b892cb1fe2d9188919ef19a81a9a29aa1ada4a1e92894cb79d38f39b1fa78e2a85ff39f198c18ca2df2cd19db18eb1f94ce5fa7fc5d82fb5ab5dc69e3ae38919ed1fa79a1d1ed1bad1bef2cd5fa75918be2dc1ac4ab1f94d848c1fc3bb4ac3b4f918cd3b92b81efc5c83cf7db7ed4e1a818ed7f94ef2fb38e18ee18dc28b188b2f91992fb591ddc2ba85ac19e39a18189f4cf6f7fd7fd1dc59c181df1ff2d2f92e92ed6c91ded1c8d2cae288e2b981d9e3ed5fb5bd7ad1aab6bb5ef49919ac1aec4ec3ec6c1f2ff2ab6c95eb1f19ec18ee1a8a6de6ad4996ea1d85b95b929d2ca7ac2b83d85b9189949f38d58919e1dda1e9a5c81ccd5af2ea2dc6f6cd6fb3fb1df7c919f39d3ea5e83dc18e7d95fd2d94db6e2d849f5ba199a28e6eb58e3dd5bd6ab4fb1ffa2f8a79c39a18e3b2f93cd2e82b938d5be4d848958d4f97f94ab1de4ea6f92dfd2ccb2acc2dca28fe58c38b2bd1819c6df1a9f7e929b4ac6fc2ea3ee6dc3c18a7c1adf6df3ac1eba79e3c83ca2bf1ab28a4d39b5af4b958d19ce3dc5f81eb19df3d92ff1af92ac2af81d8a2da19cb19f6f3fd3cb1beb1e928d3f959b2ee1cf2d29c6e83aa2c91add6f18f96d92ac48b58a1c8c6b19d81eb2a891bbb18b3bf1f9e39bc1da84d843bf1e2bf4982eb1ef3de4dc4e81a891c9f6ef1aa2aa2ae18ed388d2deb2d9c2efc1f9a18bc1b86948d189d1a991bcf5a9387881cde1cb819aa49b188b29e3ec4df03b81d8c4de1ba1c84ac1ef1ce21ed2f97e28f18ba5b84b5b919af19ad1c993c97c829ac1bfa2be18bb1aeb6ef1c8c2cc1efb18df1d919c6d59821aa3fd3a81a87d1aeb49f68b6db18ee3bc1de3a5ea2c3ef4c96df6dd2aa7bc2be82eae18e1c59b769d3ef5b91fa18cc1be1cd199b58d2da19d18a9399199b2ccb29a929c82eb82afa1fcc6ca418ab79d18b92bf92bc5ea6bd38aa2ecc19ea5f919c94a93ac19f95fe49a2cc1bf86fe1db4fe4991ba5d1cfd7cb19f5dd4da1dd85ea18bf1abd1d996df1ef5ba1bcc19b85ca49b2e92a83c2d828f2eb5e2fa6cf4ec5d1986d87ac1dae1891bff6ad2ed939cf2ada1f8e78c1ac8188c18f1acb1b8b6f91b9e18b919d919f81efa28ee59e2c91b8b18cf6ac1fd188d1ba7b1a929f6ef5df6a29c2fc189d2add2a891aaa29b819da1bc818fc5ed18e96ab19cb4f1a996eb298e19f81cca28fc69a1ee4bb59a48c38848f19b919881c9e1b9a22ab3eb5d919c918fb7e7b3c59c18a18f918bf3bf49e3cc1e68a3ca1be6ab3bb19a1bc39a28b4e81cf19cb2df58978b3883be6be1ed819b69b1f9f1da94c91dc199c2f851dce59a7ef28ed18ae69818a1afd1beb1aea1aa87be6b5ad39b5e829b5fd3cd4fe1e9e3e87bf79918a9291bbe1dd1a991ba1ddc19ee3a85d859a7af19b918af7ef4d919dd7bf28ec7981cfa48928fa5b85991db3f93a3f5df18ca1b883fa7e3af6cb2cf1eb2d9392dd5894ab1db2dc3bf2af18e83b81bb3eb05aa59c19fb1afb19ac19fc7a848c6b9791cda4c919ed6d97ef79818da7be2881dc96af1881d9b1a8a1ba2a91a96ea4af18f2b2bb3df38918a94fd68c38e49b1ae4be6e3b82c2de4ca4fc1be19ad18ff3cd7f81dfe5c91aa94cc1ac81fb839c18f1fd19bd18cf4dd5fc1fa4ce1efc5bd2cd19c84a83de180001cd78f58b282fa6ae1eb4f95b92c94dc7be1ad39d3b1af3ef39d4f1f91bf59b4af29d1be19ca28c87bf7b93bc1de1bc6da5b81be39e3c958f4db1b9b19f28e39b2cc5b1aa79b1cd1bfa1ae85d6fd3bf7e3cb3ef3ef4fe59c2d818df41ea1be5b1f97df4c93b83de18b1bc2ba4c2fc1ea1ff1ff18dd5f918ac4ba19c86ee6e877db5c92bd4e86fc4fe28947c82c291a1a018b199d3ca2da3996ab4cd19d4ce4bc1fe2891bb7ca39e491e96b2bf4e81a7ad19eb19d92bb59a1b82ea28ee29b1af4e82da18c00000019978d198b1aed6db78c4b83e8118e1cce5f87b19ed1ab78c7c1a991add58c18ca28a3829a193c92c92b84cd38d4ac3c5cf1db1ed3ac38c4be2ed6af1aa92881db81eea1b8000005d69f1df6a82994a3d8192f581b3891aa919a949a1bfa6ea2fd3e94fd6c4ec5a81982000000038d1a904af2ef483de5d1b7a3b1aa3de2e86000073ef39f4eb189d4e919a6992f81d8e19a2a83c87e18a9195ac5f81ee38b18b4dc188432db1aed7ab1c86f93cd5918c2cc7189f3a92878a4de197b49c29e7d849d5cb2e4ec38a2da2c85dc49828200013cf4a91bbd7df4dc2cc2be5be5b91ed28f4e86ac2bc7ba3c0000013ad4991e86c1d95dd1bc4ce2ff5bd4d87ca2d835ab19ab5e18d7bf1a29c188a6ce48918ef69b1c918f3be38c2ac28a1be4ca3a2f83be18a4e61996a1c69f18b1ac1cf1ab38b5bb1eb6f186b1b91eb6b5f7a5aa3b87b7969e38d6cd19cf1ef7ea1bc81b8a4de000002d4cd1acf3ab6b3dd49d2ec39e2fc6f83bf6f18f2d96d91fb4ca4ef2e18d84e82bb5fb1ba96eb48a4ba2d92be39a1f85c85ef7f95fe1aae78829f5af6ed3d96ff1c995aa79a1adc5ec38d5e91bfd199f2ba18da189a18fa4fc1de7df71b838e2d919d69818ec68a2fe6b4bd4ff2bf3ed69f7eb49b4c3fc1e7ab3da3d819d1d929a28d38c4e86d3fb7ad5ad48e7de18de189a3ba293be194ac188f5b94ad28d39f684d2d2ec19b6cc79a18c5bd4896f79f59d1eb1cd3e819da1afc2982bb6dd5d93d82a91a9d7992b87ca6ea6ef1b9d3be4fa3fa5b96e96992cd5ab79d38a3fa18ce29e59f6ff4895ac7fa49c2da18ec5aa4dc3f91da29e1ef1d82a18b3cc48a7c59c3b979929b18f5a959d2a69e4da6bb1a9b3885ea3be539f3b91f3982ff19f94c939c4ee5883ec49848e4a4e1dc2fc1ed918fb1e3b849a41ef586e1ab3884c82b28f28b58b3ff28c4b6cf48b2fe6b82bc6ac5ea2ca29a1af4eb4ef3992a852e5991ff3db1e1ce4fb1ad3e5ab1ab91bc4ee7ba3b6cf58d1d91fc1aca6bc4fe1a8a5a3ac5e1d82be4918b1c6281ff1d18881f92fd38c3bc18ff19af2ef19c81b9c5f18bd3905d3f7919f19ef6bf19b5f5c18d2ca4dc48e4ba3ac2b84f83987e1da95d939e5aa19c68f29f29f63883fe5a81e31c959d38d2bf2ff29f1ee5a3be1c93be39e2f82aa39a2dd3f1a84ee7991bbf28ab1891ca1de6a49b7b5c82ff1dff6bd1b1a9a12f948f2ac18ee1bfa78a1fc2bf5cd4f3da18fa1aa4fd7c7ce18f4be3884cd1ae2d979e1da1bd4896b938d18ac5be3bf6b93a3a84c87b4bd6e5dd1f2dd4bd1cb4bb5ca6ce1ad1c1a9a7de1ee5801cfb4995aa3be1dd5ab2e93c92de6f828e19d5b7af68b18dd1aa5ac3fb6e95b2ec59a1cc18da5fc1ae5bf1a1df5bc2d81f91b8d4d96a92dd1ba2af1ec7b3fc4f85bf7ef1fa68a3d91f81ea6db186e848e3883a2be189d28d1bc7bc5bf2dd18eb7c3aa2adc188d2aa5e91eb7cd1c9e6d19991ff1bbc6958a3987ed19a91f18e5895ff39a2cd5b4ba2bd1b9a199e2ae3eb182fc6f1f91cb4ba1aaa7d3ef1d84c2a94b1b392a92ba4b939b18b819eb1d8f18ed19e1f839b5d18b86f7b1b81cd84981fa3cb38b2ef1bf3c83b828b18da2ce1f9b1afb2881db4ad683b85dc2a83ed1a488695bd7fe5af3ab5a94fe18987dc79f189e2d85e838e4acf189f7aa1cc81fce7bf4f3b97c838b18ed28d91b995bc29cb2adc1af81bec0796fc419a618e919b95ff2cc5886ba6ed1dd5da198e3fc2a919ad1981886fd6b7ba1f9c3de4d9696892a6a2fa48b1ba1bbe1afb19997ef7aa6a818f91df4e85c939b6f918de18ac5b95cb2ab4ba5bb39c19e7e1cc82bc7896dd1fe18de2b18fd4df2be4a85ac2cd1ad2cd4aa1bd5ad2a3ab7cc4e1ff918ea5ee2ed1a983bd2ca19dd1dbd198e19ca3fe3a78e66e968918db6ec29b81ad1d8f6e5b85be1ae2d918e5ea7eb3a918df1893ea1b838e1dc69918e3ea6ac3dd1d9f3bf3cf1aed4ae1aae19ac28a2bb3af38d5f3e93f2ad3c91ebc5f918eb1fc959e1a9818cd1f868e1bcf5cb6818fe18fc481ba1ec488493e18bb3dd7fc29a3ec1fc2c94eb48b7dd1dd6ba7fc7ac2cf7a2ed2fa292cd4e2ad1a86b19ad2d3b839e1bce1ee4ad5f91cbd4c1fe1ff81b9b2ca3bf482d6b9681fbc6bb7cb18a97cc1aed1cfe5fa6dc2ab4bd29e29949e4c939d19c6d82dd2bd39b6c3de2b92bb68d1e8b5dc4da1ec3e83885ae4a81ba19b9289b18bb1b1efc5df1cf39d1fda1af2fc18c1de1cc95eb3918d818cc4ae18c7a63f91c1a9b7ab2dd3eb3cc79a7e28d2da4883a838831e87d81abb38c58d3a1ea1c5895b94b939d2dc1bd3bd4de7ba1afa5fa189b1a9918dd18ba19ef6fc1992d3ee4a2cb188c1a9e2bd2e8918bf18ad1cba59a18f828e3a83a82ef7b7cd2a5f83ce5fa1be4cf79b1ce4ac38c3ef1bb949c5dc1fe4ce3de7e2b2bd079f2c91bcc2ef3be5e3f59b3a81fe189c19da1eab198f6a19b81ccc1abe4ce2af18af6af6ab7ed29b39a3cc4cc1be38c48b1ba1ca68c796eb19d1bb58929c582aa2ab1bd69a5ff6a91f83b1fd28f3ff4981cfc19ba48d58d19ed18892af3da1e84a1cf86cc392fb3e948d5c591f1cfd31d9c1cca6f7cb3cd691da5ca2da29a18be28c18e7b97e3c82f95e918f94bc19bc4ce4ca2ab4ab3db1cf2986bd4d188a4ba2fc4f81bb39b1ac85f81a84c91aff4af3d19ec18be1bfa28e3bf18d7991dbf18eb6f4ac1e7f2e93997b2ab2c93de19ba69c4bd18c29884ab5fb19a1b2aa4ce188928b1fe5bc2f82893fb4a3da3e39f01a48b3db4d818a19b4a3891ec1ea7b1d2d292b91ca4fe58c6ac1de3ac3981ea1949929d3d3bc294ff7bf3cb1bc1dd6991ed7d81dde198a2a96c94d94db3bb5eb1ab7882ab2d84ea7fd4e19d819c86ee1883f91bab2f6ab6cc199e78a1d3ff19ab1ceb5ea4886af1994f75c868718a4fc3bf5992af1b819cc78c78f1fff5ff4ae3cc1f873bc1bdc4bd38b5ab1cf3be3de61c3d93f93c4ff192be69a191dc3fd61db5cb3bb6ed3dd4da68839e1cf595ec5b839e491f29d4ae3893e92ed28d5ff2c3938f1cc3ac18aa18a84fc1bb58d5ed3ef6af59d4de2ad83cc5cd4a86de2aa39c1cd3cf7ed1f92d92ab4959859c1ed3848d18c968e4be2db7dd2ef2bc1fa4da4a96881cec383fd5f91abd6da1eb818cd19dd1de1d8c18ec3dc2ab4c95e5db3cf3cd1cb68e5ba6c188919ef58d5c1cd4e81db4f839b33dc6aa34db4e968b5895b6d86dc1df1fe18ba58e6d5cd3eb2ba188a1892bd5bf48d1ba4a1bab1ae96ae1efa29987ae1ad1f9591cd68b2ec66f3fa5dc188180011dd3bb1983da3a000005f5e93a383de2cf6dd3ff2cb1d91ff4ab1c87ee189e1ff5eb4da6fc39c1aa600000000000000000003188f18d4b1af1a86bd19f2cc18958a4ae2bd19975b3b58e7e2a94f4bd18b4bc19d2df39c1bb1c93de6da2fe0000000001895894de1ae000000000000000000001391d93c91b8918bd58d2b1e49b2ab2881bf18ac7987e81e2ca1b949d2cc783db418ea3ac1be681ac48407d7ab1fd7cd2d93ae5981b95a918b1bf1bd3f93892ff393f82d92ec25c968b3e49e29f4cd2a91ce1987d49948b4df3d3dc1a982be5ae28c1fd69d1a8f18bb18c2882e1cc18bb2c918c87ac481af3af49e1aaa5ca5d6e96ad2ff381ae2d4fd58e3eb38f5ee2ee2ca783e91b94fb2cb4d92882e91ac3b2ee4c4ae7ca19dc7b5fb4d3ae7aa78d39f3cb19e81b7e4a4ba2fd6bd1dd3b96c3bc19b3d82df7e18b1dd1e87b5e1af3dc1e1db1db4ed1be6f4de1ec1fd49d2828b591cd48f2ff6d3bb2c93a5e95f84ce1fa19b1b8d7d94b93de18ac4aa6891a9b4983d1d94bb3fd1eb4d3fe1adc5fc2c2d1da4ee1cf2eb398384aa3e94b91ad25d5f84c81ac6e92dd2ab5bc1ac6ba1a93d1b869e3db39f1ca1f3aa48782ac7eb1dbd1d8948e5aa1bd2bd2a1bd4d1bf199e3e82b82ff5ba2cc2d95f49283ac5781f3e28c4c1d8281bd7d4ce2e91a82f18e1a8b487982f9199b1fc2ae3cb69e7b83fa19d78b1cd18f1fe2d81aaa39f2a1d1ad188e3ef5ef2df3a93cf1c93a819a181bb1f82ee19b3c2ab7d18995dd586da28a1b9c188e1cb198f18f2ae2cf7a1dd1cb83de239f4ef28d6de2bc3cb7bf38f7ea1879b199b119a84bc1a94db39949a2e819ae2b5d1dc79a7e6cd5cd4891ea5e8383c5fa5e81cc3ea5a3da1d938f2ab29b1a91ad4859d2d94db49d1dbe1b9b2b9f7cc1ade19fe48d1fc6c68f1ec38a692948a18f828d59a19fc7ef19bb4bd6b1c83ca4ee1b82cc1939e5c6fd2d4d1a84dd18b94bf6f5eb18ba19ee3ce2d81cd4c6fd6892cf3f87a2ae4b83af6cb1996f1ce19b3939a2bb7bd4bf7e6d81e848f59d7f9693b86cc2ee28b3fb6ea3fc1db1ad2cb4bc19bd4e819883be6c3d81b8e4fc1a995b5a939d2c3ac6b5d92cf38c18e85991985d91edd39a29b188d3b86ea2b81fa918d2ac7fc3ae2fe4be3bc7ca1dbc7f94ed3e6a1de6d1fd2e7da7882c838b1bcf1ee1d9778f1bbd1a18e5895dc18ac5c838c1df5d91ac95fb48c79e3cc2a82b68a69a3ed1bd4ac28c3bd5b94dd49b5a3af3d7ff4895aa1ff18b394aa5d8195ff69e6ce3d819c78d4ef19eb281dfe1faa4ea49b1cb3a1bbd5a91a3aa6fb3c7b53ac1fa19bc2dc3fb5df1beb1a82f82c1ce87ac3991bdd3a95cc19de2dc7ab18d5da1bce1dba1bcf7dd6f7e38969d58f2a84de1bbc28e18ff1baf1a86e2dc3c91edb4fb3cd4ba1ef81bd86f84cf1bd7d6b94db1f87b48c1abe29a28c5e4d95a97b1cc1c91dd6b93bd4981885b19dd3af69e5ce58e59c4d3986f5bf198a4ca1a18dc7c6b91cef3cb1aaa1fea1cbc6e44d5af1cbb1db2ca59f18b2e92f28a5e2aa1af3fd1c87ad2de1da3ea3981e1bf1db92e95a819ac19ee2df49b49a5ee2b85cf69b1d78481df28d1e2d5a819b19eb1ccb1ac2a91e85d5a94f1ab1bc7cc2be2ef58c2fa5af2ff1ad2f87d48c1aca6d82f5ef5ad1bd7b5dc2ab5991aad4e919de3d6df1acd1894994cf18981daa391eee39e5ab19b5893bf1bce29e7c95df39c68a3919fa19fc19cf5c96bf18e94bd4897db3e91a93b78c18f818b3fb49b4bf5af3be38b18f3ab1ba6bf5da24cc6986fa1ef6a7dc4ca39a6db6df692ad3ea4f1ff4ae3da4c85d5ad5fb1ee49f2e92b4bf1f5ca1be1a939a38c6dd4b5cb1bc6e1fa3cf618ae6da18d49b791dc49e7eb1dd4ef48b29c19fa58d1cdd7f95ac18da1bf6f18a03ca1aa1e893f2be6de1eb3c2cc2b195ce1be1bb17818f2b2e95fd6ed5ef49d2918aa1c8a3ec2c991bf951fa28f1b3f38c596a1af81bc91d2ec4ba3b3b82ce5bc38a7ff294ab1de6c18e29c18e6e198a2e84fd7cf3fd1b5cf7c96cd5892af1f199a5fc3de2ea4eb4b1bef7819e4d82dc3c839b6dc595e94ab19f2ec6fb4f91a9f29c19b81afa391adf18ed198a6bc1fd19ad1893c3a81b91acf48e58a7bc2c86af2d91ca5f1ace18aa3819be4a81bcb1bed3eb2ee19c4bb3ef3c1aa828aa6de1ef949f1e93da1ba5cf587a87b82d4af18c91bc3ce6bc59a29829a7ec189a7e979d69b29918d4ac2aa2be28e2e85ba1db5dd7ff04b95ab3df6dd3c83f68e59a7de6ea79f28f1c8f2994cc49c1fc2aa1bd1aae68e18cd6af1ef1ec1fd04dd5d868a199c29f1bdd1f891b9818be7e1fb2fd19b18e4ba1883d818c49e2a1a949f18c1aec3de2a84d95f94fb4982df3dd18f5987a819de3984f95c919e7a6dd39e5e1d3f97f3fe28b2c96c97db7887fe1d83a7d7e7ea6fc3cb4bf1a93e4ee2ff7ed1ad93fd1b8a1aec198f1c819b7bd19f6ab2cb1ff81cc2ee29b6eb4dd7ab2f96c84f81c8189c285bd1b984bd3b2ef3be7fa1a8c1bf1cc58939b1fa3f28f3ed3ae6bb6f19a919c3bd3f84a18c2b81bbe5ad6f91acb7bd694ca18ce18ae2ae24819f69f1f92b81aa2c82fa2be2ea5dc1fc18cd18c92ce3c5887f82cc189b2b92ae3ae3ae5af39f7ac586c94887fc3fe2cc48c79d5897fd1a84b82bc18c3a59919ba1d9e3cb7fd28bb6a918e191bf918d95c3987ea2ab4ce293db3bc1aa4ff6de18ec6ff2be4982c82b939b2a1cea1ee4f48a3ee79e39b6d6f4dd1bad2c85ea4d481b8d4bd287a81eff4d959f1891ad5fc2fe3fd4fc2f818db3ba62a92bf3fb2f9286de2bb5ac3cb1ac2be3bd3ae2aa1acc59959d4ec5c4f83ca5e5cf1b92fa691fb395be1bc81db2fa7cf1a8d3fc2a8c2fba4cc1abd3c188c4fe1a983de052b38400000000000000000005f2df3eb7ad19fd2f2fd19be04e9199d1ba59c18ee5bc5dd18cb1de1e986b83da20000000001526000131b3b1e480000012cd49d6d81e00011941811892ff3ae4a1ad5f2882a1db5cf4e4d93c87de1a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004df1a9d1a9b38bd28ff5bb3bc7bc5a818992fd4bb2e7ac2fd1a869a18bf2dd1df6ce6bc1ae878c1cdb4e919bc2ac2db6a918b19eb5e6a6f68f5d81b93eb29b19b39e1ee19b18dd18fb2db2ec49c3cf29e1ea1aba1d8c59f2af2d1bc1fd58f4db19f5c2d868c19ff5f4bf7ea5ca19bb19891ec3ab5ed3eb1ac1c9868e28c7b939f3cf1ca3ca7c7de5be4ba18b1bad48d4de4fc3dd18a96cb5ca18ac18f9198793c97d1eae1ae818ef3dd588188e6ea19d4ef1b819aa2eb5bd6a91c8b3bb19ee6c81cea4cd18d1ba91c8d5fa1dc879e191bbf3dd5ec5d83eb3eb3a94dc3fb1fd3aa1a886f84de3f6af6dd34ee48a591b5f1dc39e19f29e2af4ff2cd69929d538a4ce39b49b1fe1ea2b819ce3dd18fb78e3be18c1f4cc6ac786ff19992c94d81af837db3ed2d19f7d2db2a29c2b95e1e3ab4ae7de26ec188b19891aab1fc78819b1db79c6f7bb6ce4be1aa19b4a1ec59d6ef18fa441f2bf4896893c95ca5dc4ce7f48b3bb5fa6ec5c97ad18ab4fe2f29e6b82ce3c91ec1c83cd3cd6a6ec189a1a2e282fe18ea38f3c919d969f3f93af1ac3ff3ba69a2ea6bf1dc2c93eb3dc7c18919a66e2bb486bc2cc2fd19a94a86f81bee18a86a29b5cb4ef4df6f9785b858c2dc1d959b1da5bc3c84fb6a918cd7a919fa7f83b28d18ea1bc18c84ad18f38c2a828b5c938a1c18a1cf4ff2ec3fd4af5df19b7b81a883d84af18dd4dd1fa48818af198d5eb18de69e3fe2ea7f2ed581bf189b6dd36fa69c29849e3d5d4a83db2996ef19cf7cb4ef3de1dd4e86ae2fa6bd48e6b28f1de3c84f869a19c19d5f91f38c2cc2d91bbd2ba1dea1e887ec5c758979d5eb7ef5d92ba68a18ec28a6bf1fa4ce119ff78b7f91a9f4ee1aba3ce18f18d819d85af29a5c6b29c4bf19995be3e3a84e19919c1e93bd3d5bb1981bbe6cc1aab1dcd1ad4c86d828d1c91dd19b83be3a59c2e828c37891ddf3e92ac5fe2b6c19e1e5aa2a829f6f3bb18ef3cb69b3cc7b81e8e1fd1a84cb1ad2a6cb4e91de7cc4ce3cc39e7b18a87ae3f1acf199d218ac1bb81af83b1e94cb59918cb1a8b1ae18cc38e39819e69f199e69e385f929fb1dcb198d1ea948a1da81aca1efc1cda4e949c5886959b5dd3ab3cc19e6aa5992ad19fe494e91b8918f95dc1bda1e918cf19c93eb59c6b86ed19995995fa3ac29a58a18ae29b18a1c6cd5a96e4b81883ce4e81ea4bc5ea28b1af5ef19cf59d6ef3ce6ae1dfc2eb5ef1bf1ec5e4af69d5c4ca6be2ea1fa3f79a4dc2cb19ad6f92f948c1a8c1aee7d738f5fb6bb1ab96ef4849c48818f78d1f9c19c81a996f97bf19e91bb1d892e1dde1eec3ca482f6982ec29e49b1dbb1ab92cc2be7e81dc6f5ac1b94e91f96819a85ea1ca18c91bdb4ff5cc5cc1b9f1cfb4a91ac82b83ec4b3ea5bf5d5dc22f282849a75ec19dc6cc7ac5df3ef18a91adb4ad39b2a2d85fc4f81fb3cb3da1bc2ed6a919a4ba6d3e3ba1aa69e7fc4f49b1dbd1bd1aa828fa5cc11c819828a1b8f2ec198f1c8f2cf18a849e2c91cc1a9e2cd18cd18bb5893af58f7eb1cea2e81da1bbe7dc58c39f2bb2ff619a93aa4da1b91aa1b7aa7be19a4b6fd5fc19ac2e97cb68b1f86de18bc4bb19cb4881daa5ce1bc1cf5cc2ed1b39c4811f1c11e00001963f5bd5fd5ff29b29e69c3af69b29b38e6ce5b868b1bdd29f1caa2ee1dad3ad58b1ac6fa199e7ec2b4b958a2f7ff289f18ad2ac1f8e2cb1bb95ca1fb3e919bc5fe1de4e87c91f94db5ae1f84bb188b4dc1ecc18be2dd2959e1ab7ef2ff5be4aa1cb58d3e81dd18af1da3b38918b2e94af2bbb5bd7ba1ffa3cf1bfd6fd4d85bc29a4ab2be5fb6dd49d2ca4cb6d3de3bd5d91d9a3bb82b2ad1ada18dc3f19e3996bd6dc29a384ef6b28d1ade4ac6fb18b5bd1c928d28a7dc2c84991bb7ac4ee3982a4ef1c8929f2a9281abb1af3a87ac6f59a3f91996da6c6cb1fc9199f1a8d1ae1e8a7ec3e86b91df19ae7fa5db4eb198d48d3a819a3e82983b7bb79b2ae5be27fc1d9e18a1ec3819839c7886dc1bf5eb1cbd1ff1ec3cf5fb3cf18c1fa1c81a3bd7df6c5ec2cd18cd39d1b9c5e19a91988199c7f1fb1de2a839a4fa3c18b3c2819c928d1cc6fc1aba2da2dd1db2aa19a5ff7db1af5ce7e19c4f4cd4893ad5dd4d1b92fe7be1cea4fa19b1ba92ad58a4d691cc3883c55bf786d3cd2b29d6d1de1df2cd7ee7dc5c18b1a95a1db1ad5ee1ec1ec49b3fb19a2981ea42fd5cd19f96a1bf2fb2881a84b1cf1fb2af2bc2d873d948b538c2cc2b82d3cd1ab2da49e3c1ca3fc4d82de3a28b48b2d4f794c287a2a1dd1dbc3c2fb5ee2be4c4ad28a928d5b4e828839d3dd58d59b1c3ee1ad84a4a91fc39c4cf7b7d3b91ac2b979281a82c71bd2ad29f3b3d5f1de4be4c83c7d1e91ad29f1fb1bb2d4a1fe2e39f3af7f6e7f1e928b2bf18f2bf4991ad1a4a1f28b2bb6bc2aa1e86a94dd5bf22fa4ea29e2992eb2b293a1ce28c1ba81f981a9e3f87d49d1fb648e29e2bf2ab1af5fd18db4d84883892db2e58e79a22d85938f1aa9383db1ee877bb5ff78c3ca5ea1fe78c4df3c199d4e97bd4fe4b818bf1a96818b7bd791bcc1aa2fd2aa93a83fe2bc2882bf1b4e94d381cc2be681e94eb4db1db28a1b8181a4c1ae7b3eb38f1b2c06e184cf3da2ac4858d2bd1e83be49c2ac1ff3ed29b18f3496d6e91acb18fb4cf3f1ae2c81e3fd48d2dd19f18d7c1991981cc3ac28819e6a1c4f94a92c4be1ce828b6e1bdb3de19da5d818b96c918ed38d2a93882c69e2ea6d83b92ef6fa5828b4958c1d86dd5f1f81e8e691ad3d1a92f2bf481b91f1ec4e1dc1da6d28d38b2ad2e18487f128c19e4c2f81bc11ef31cc28e3ae1ef5ff5ad7c4fc3ea2de4b1dd1df5f7941993f5e18d28f2b969386f1ed3df692ea28d7d5b3cc2c81e84c1ac2ca2aa29a29a1ca2ab1bf5928a3ce4d19f261897d18f5c1af18b2ed18c5a2ac1fa2f6a5c2b1af4a4ba7c1f95fb1e93d6e181af18a3f1aa1da1aa1ed1c928828e6c2ad2d91db2f3e4b491a95b1c82cc1d5f1ed1fc2c1f18f4fb7b94ab2a4ce2fa1b38b1db2e2ac2c4f5b6b1d91995b1e2ac29c18d3ab48b29b1bd58c4c3b3b83ae3fe3bc2da2da1ea2c6a6e13a7f11d92bf1b4e1ff1a1da2ca1b2e92bd1e2981dc42a95f4f6918c1dc1c8783f1bb1cf2ef1af219d19b1a81e3c84c83ee1a1891be1b82d6e2a11cc1981a4e19c1c81ca6928292b91a19c28a1fe3895bf2ff28c68e4cc329f7e1aa3b4af7918f3bb2cf1818828a3ba39819a19d2b91bf1c928d494e39e2882fa3ea2fa1ee6a28a4c1fb1891e831ce1ea1cb1ff6d296e1981e1ed3ab18d1981ec11992ed2dd1cf794e18a1dc2dc4a2b93db2ab5e3bc5829b491f84fe68c5982f1f97f1df3bb1ef2991f3c2a3e481aa183a5f1fd1eb2a91d1a2dc1bb86ba1dc92a96fe18be3f1ac7d18ad19cd1fa2a82bd3e85b4f188d4eb2ec1dee2ee2d918bd18de2e1fc69c38f3bd2af68382bc3ad78c11acb1efd1dae1b818ed29a6d6c83881c85d78b6b93cb1bc1eb6881e2de1dd3be48b3a92d829d3cb39838a3cc19c1b8591dd18d1df29e1b92db5c48c6b86f86ee592ab18b2dc7cf4ad2a9394a18a4e2da48a1da1ce4a3d1d1fb519c05f97cf48e1b929f4f6c5eb4cd18aa1b882a85cf5e29d1f928f5e83ae1bb6bf55e2ae1a8f6f2fb6fd2991fd4b81fa3ce4987f81d19e1a8819ba1caf28b18dc48b2bd5ad3f96d283bc49828e1cf2bb19e91dd28819b81ff28968d18e91de4ea6e2e5c5cc6e2af29b1d91fc2ea66b4c1dc3fa3fa2cc7e38d39f3ef6e1e91885b19d4c2be3e83a82a681ad3a7d3ad1bd1bd783bc2e4ed2c49c59c29836b1ea1da183cd2a91e1ad1ab619e2be3f81a81df4ad4a101cc181a2cc29e2ca3ca7c39c1cc393bb3cc29c1fe4c01da1ba2c19b3ef29d2c3de1a04e59c4da1aa4f96bf3996e6a1fa2ac1cc1fa5c28d28f29d3b3ac28938b1aa3ac4d84fe2da18c1d92dd2cd49f2bf319b6b2918848c49a7a1a812be2ae38b1ff1819c5a2c92c95d3983ee3e48b3ff1fa2ee384db1fb5b19f2dd2d4e1aa2be1cc5d1bb7b11891af72f2b819c1ee1fe7a1fe18a138b2cb21be1bb21d82c1e929f18b2e1d82cc2929b1dc6ae18cc1985eb189b4ef181fc28c7a28c19c1bc1e1fd2cd1f1de2bd3db29a4d84da48c2fc4e3af7cd5cf4d93df1b91bf11ac2ba2ac1cc2fd19919c3ea4ae21818a4c1f85d6f2885be59a6a3df4fd1de5881bc2fb1fd7b1a1dd4e5e1be3d83983c1bd1bf6d18d1ad1b94d1fc2aa38a2ca585f2cb2eb3eb3d1fc28c4f1db1af2f4b1ad2bf1bf6831bf19f1cc3de49c1ae29f69f4fb791fc2ca2981aa3ac58e19c36f1b919a1b1bf2881fc38c1dc4e4e6d4a948f3fb2db2f1ab2d1d81de29a2ae1894d6f1c839e393d686a1cc6b19c2fa3fa6c01791e5e00000000000028929f1c1cb3db3bd2896b1c1fc6a1d2e281ad2d91bb3c1f8691ad1ab492b4f6d3a4a7b18d1a9783984a81ac19f39d1ab2f7c1a86c1df6a3da1b82c19d7d1b2b1992a5a4e785a5819d2991894c6d1dd18d61ba1be1ba18e1b95f2e4c2c18f18f2f2e2b81ea2fc3ce28c3a5f2f2d681981d1ab6d19c2ca29a19c5f1ad6a1981c0492a939592892ab19b3e1b85a3a4e7f191919e1e92fb2af1db1ed5919391c1fe2d828a78681fc2cc1fa3e1cd1fb6a2a81a84b1bf596f184d197c1c182c38382802c4c1e1cd2df1cf1cb7f3c1ac1aa5c381b1997d01dc1bc52ab2b96d2f291d1e1c828c18a18c4a3e1ac2c2f92eb1f5c18e1a21fd2fb3b2ba1dc6a4a2881d28b1e91bb2b381b86a1ba1be1ac19e1f19f1de1cf2df1a91cb2f7933aa2d81e82c382b1d06c185d2af182883e19b3b391e1883c7a682a197b5f53d691db796c1a1ed29f7b2b3a1f2819a4c63e3e2a1ce2ca29e4b19f3b71b1af29483a2f13a683a4f7d1c92c1be1fe3a596d4d4a7e3e07b6b3e491cb6b15e1ec18e4a73c1ae18a2a483f1df5f781c819c00291eb1ef2f1c81e282d92a91ed1af697c1ba1de355f29c1c87c7929f6f7b1af19f800000000019918895e83bc0000000000000568d48a29a3f3fb2b81fa1a0000000000000000000000000000000000000000000000000000000000000000000000001a96b18f39c202bd29f18b493ac1a92da4c4dd5e92f1886f28d1af4a6ae1ba1de2ce5a4c93cb1a92ff3991e91d4ca7aa68c4a4bf38d1e9395c5c6c1ba1c6e2dc2bc4a1ab2ab1ff391aa2ac2ba5c05693cd69d58f4cf48f1af1ae3ba2bc7c681e4f19a391ab4a18e3a2d3c192b3924a1aa1da5e55f4f19a1984cb4b1c929d291dc4ea48c3ce2b1ca3d818f39597f3fb1e2db3d5b85de7a00000000000000000000000000000000000000000000000000000000000000000000000000000000004d2a2c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018997ad1ec4b1897b1d91bba685de1d289d3aa118957783cd6e2ac2e829818e83800019394c01bd1ccb3ae18a1ef2a1b9c40000001f1a9f59d2ae18b1ebc000000297b18e95cb1f7c86ae1da73c001ab6fd19f958b78818d83b19c93dd19985aa69e5c001a8b1ffd38f51dfe3bc7819dd29f3e92da1bc1c8a5b82f968d5ef1f2e85d6ce4cf3ed5fc1d8e19a00054df1e92a96c81ca7df1ac91dc59819891fb18ce1bce3880620000000596cd3eb6dd3c91dac6c81fb5bb1db2bf2ed6dc1aa2e59f2fa2cb3a28a18d91bfd7ff4fa48a2a82bd18ff2ed18be299a1bfc2fc19c1804f4b1af3d2cc39d3d84000000000000000000000000000000000000000000000000000000000000000000000000000000000000039d4ef4cb3f958f6bc4e92e91ae5f6cb6db1fb6c3ba7bf3ff2ff4b6a1c858c18ba2fe148f19839c5fc3ee1ec1cb2fd69b2fd2d5ae6d868e5b82cc2fb4b19968f1dcb6eb6894819da7ba18f82e83f6eb3ff3fa3cc2fd2b95da1ce3897bd1bd7a19f1e91c91dd65cc58c4ec2be2ae1ce19c2cc2f19e96bd1d91dc3e85fe2ee6cf4ed4df39e18e3ba4c1fe18ac5f833b94b5819e3ea1cc3af2dd18b7bf5ce5ec1cc6e7a20007978200000000000000000000000000000000000000000000000000000000003f6fb19db48e72a1c3b491ab5b682e1de1bbe1b80000003fb18df1a8c2ce200000000000000000000000071cd931c5b29b1bf6e3dc4882de4a487a01ed38f1a82ab2c78e2be00000000000000000000000000000000000000000000000000000000000000001b7b91ae28a49c200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007d1bad48c5ce2a399d1aef3adc7db4f919c818ae6ca00000006b1aef3cb2f818a94dbf3fb1eac78a1cd81b8818f2c8f18f95992aca2f8c1aec20000000000000000000000000000000000000000000000000000000000000000000019ef3bbb4efb3dcc5c9e2be0000193fb3d4cc04d2db39a18000000000001006b18d6db6ca28e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001eb11ce1a51840002b2bff1bfc5f7aa1ee0000000000000059f1bf91cb84ea0000018d3db4de40074bb97e9b2a2bd78e1b8c2da2f828bc18d91e8d6de5af59c5eb2a94fb2fc2fb83e9c5982b992fc92afa3f9c2bbc1bb2a8b4ceb4cf7c948f1ca4987ac5d91fb1fb1a86bc48e28e18a39e39f1bd39e6f4dd2ab4887a49d1b8b5bd18e6c928b4bd5d95c4ce28e1d92c96848a1fd83b39c3991ad2af4bd4ab2d91ca2f81be28c2e81fc1d1e92891b95fc2aca6f1ecf1cbb48e3ac28c5e7a3be29d6f2f584ca3b8c4fb82000000000000000000000000000000000000000000000000000000000000000000000000000000003404891aef5dd19881bce2000000000000002992d97d3db188f3881a881ca2de3d9281df3bb198d28df1ead4b1caa1e8a3b96a96c2887b82a8848a3e380000000000000000000000000000000000000000000000000000000001ed1ef519a1f86a0001f1a63b3ad285e4e29c200001cb3a1e6e60000000000000000000002b1ed19d1ce2c1f2af3ef1995a1ce2ea2ce4a6b28b18f2d79238838a1a0001591b96b4d2ae7e728f1d85d1f4b2ae000019d2e93a85e20000000000000000033af1cd1ec7e5a01ce000003bb5db3fb1ed2a2b848381a97f2cb1eb4a3ba39e4a1eb1bd1ad19e1fe2a1d3c9691d1ce1be7d1a4d29b1ef291d818c1ac2be1828d39d1f969792b91891e19e3da7a1be1fc2c1896f681ec1fc28a3d96d1bb18d195b4fb4e94d6c1ed1fa7de2f848e2c8198b2ed2a92b91a29a2fa1fe7a2ba4882bc3b2eb19a93f92e2ec4f81fc7c1e93f1af3891fb1e4c1ee2ef28f1ab18c1ba71de5ae18c1b818df1bd84a818be4a00004f1fbf3df7fb4ec1bfe1aca3a1dd61ac4892c9f02fc18fc1da2ac1fdf6be2a8c219cb1ccf189c4aef28dd1d8838b1e5dc1aae1b884b92e96f87ee58d1b9d2dab79b2fb61e95aa68f6b8292cb1fac3d81bf81fe97ef2bea48c18f5db2ee58f49e3a2da1bbd28ec1fce1dbc6cf6e96f19fc1c91ccd48f1f1b9e2ca3cc18a18ae2814f2c918c78b49b49b2a918c1cbc1cbf2f8f2ccb79f28b4ca2aec2efa19b858f4fb69b18918bf1ff93bc1fac6ac1d85bd2d8e4ba19bc19a2ded18c928de19e3bf69c1c9b298f4a82cb189199e28be2ed68f1cc38e1bac3a4991eeb1dcb1cf19ab1bf95ba2bca18981ada3a81a94f91def18ed6e5ae19d92d5d93de6fe7ad02a94ba1da58a3cf19f2a96e81f9f1ca958d7ac1c985fe4cb3fa1a8c2ec1ba39e29fb1fd18b81ecd2881ea682b84d6984883c83bc1bb1daf18da2ae82cea582df19ed2ae1a882c002af2a818018b1faf1eb918ce2da1bbc6f92f91aae6bc52891bbb18df39e1ca5a92dd19be5ee1b19a82b800018b29db29e929ac198e4de2f82c8205c918cf4894839a1ba82ae5f2dd7d3df1bc6e87c00000000000000132b4e91894ec1b829188b1da3dd48e784c424ba3a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005ff29ed5fc4aa4c93e91bfd48a7c285ad49f2ac5818a1b1cd198c1abe3829c2fd1b3fe1bc3cb28f0298e5fb1ce92f18b84be6819b91bdb6fc7ba4cd7cd5ef3ce6db5ca19d3cd3ca51a8e1df1981bee7c842cb782949f1bdf2ba5fe7e82cc0072cf2ec91afd696892d819ae6cd68d2be29b39f2e92b6e1868d18ad01cc2b81b9a19fe5c91e2bd3ef24e949d18ff291e22dc18de1ec81fa3b83ca29c289a4fa58919d2f819fb1c7b1ba5e81fee1880000000000000000000000019cd28ff1ee949b2ea4a81bb7a7fb1cc1ed1aab6ab19298e1a85fc2bfa1b8c18a95ec9488e39fc68b58a1f839e1aa939db48d69a1ace1891cff492a8a1def6d91bd81ee188e7ea7f84dc000000000004f4a9b4de7e4f6a22d1dc1aaa1cb91f981ebc29b2a91ea2e69d18a93dd1bcb1c95bb3ab81cf800000000000001b18d586cb288b2c8a398191bcd5ee68a00000000000000000000000000000000000000000001323d2cb18cd7cd19cc19d860000000000000000002bb19b3cc400000000000000000000000000000000000000000000000000000348df3ad91db839987ed9388d1d8ca18cff4bdf1bba59e1eba4b8e1dce19de7cc7ef19dd2eda5f80000005f5ba93a8939b96be4de83c982aa84f81f5cdd5bc2fd83ed1cba7ae01cb2bbb58fb3de3dd48cb29ed3d8e199dc3cd2dbd1bfb7ec1de81dab39bc1cea60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000012000000794a93b992d8d2ee82cd189928ec3dd42dac6fa4000000000000000000000000000000000000000019cd2899139fb2a9b3eb849cc5ca1a1cd4ef2ec3ee6119f7bf79c19a42829399189d1afd19d1aac289189d2e9f58f2b91da94fd187af1bce28f81ab91eba39d38f91e981bcb18ee58e6b828d4e81e8e19a1bdf4ee2f79879b2bdf5a85de1cd4cc6dc2bdb1ace1e9a1eaa5bd1a59b1cc6a19ff78d1c9c2c8a18ae58c2ad19e4c18df3f919fe3bc7bb6ff1efa1a1f2cab2e991dee2b8c19be2e011bd97df96da28c1bf97dc1cca1cd91e9b2a985ba1cb4cd2dcd58f3ec19d4ac3f848a18991bad1dbd1be5de3be3dc1afe2bf81ad81af19ad3cd6fa7c284a1bdc188a2895df1caf1b8d189a3bd1b8a28bc5df18ae7e92da5ca19a3bf19ff4ff2aca1b9c48f49e19fe4ce2918938d485b59c5ef3cf3cf3ec3a92cb4894a6a1cd19f91c8b28928b6e7dd2cb69c1cb12ed6de7ec2ebe1eac1de1de7fa60000000340000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000194ef3894ca3ca000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000289581ba00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001d1b94a91bdf1adf1c9e3bc79a1cc1883a49f3dc3a3ad4a5c8600000011ef4ed1b8d18c91cb685ec1c9c1cb18af68a4b7df6e919894ad1db5c81ce918e1bac5aa5849b7ca2dfc2ca1a8b4aab1bef2b9839fe1eb2fcb59d1e9b1bdd18f1ec85da6ea1eac4c1fed2fae299c1fed1dbf79e6de6fd2ab929bd7e2bec2cea1df2bb4d85fe3892a818ac7ee1ca42918cd1adb3fd6d19bd1ec928485ee18bf29fb2bf19bb2bc82a987df5cd1e3db28828938c1c8b1f95aba3b2dad28991cff19e82dfa7cc58d7d81af86de6ab1edf2cc7ad2adf2e9f79a18d92cfb2a4c983de82fde29dd1cdb2c9d2fa969e1f881be81fb81c9e1cec1afc7f81dd28fb4fbf3daf1dcf28da18aa6ca2dd2df91ed91ddc1a983fe298e3bca1d8c1ee1eb84ac2df97db3a1b8c2ca7fa1aaa78192b2c1b4991de18c387d91c81e58c19c284bd1ad7839f7f5eb19e2ad2acd1ccd1efd1cea5ab2c9218d6a81b9c19a81eb19ee288d1991dd81ead1ccb1cae18dd4dd19ca1da1aa7a919ac2992acb2be81b8c3c95ef4fa1cbf58b3b299918b819ba7cc4eb1879b1be4bb28ba29cc4a819fd1bef1f4d81cb1f9a29fc5ca1fa2af19a18e7e2af7df2ceb3ef69819c1a91c893b9d2fae1cdc1fed2b97d1faa2fcf7fb1a9f1ce1ce829b388e1f9c1bee5ac2a1ef1ce48b1cbb18cf18eb1bd48a1dfc1b987e1fef29ad3b81cae1da7cf4a1eff1acf7e2a8a1cba4fe6f1adf2ff6db2e81b8e3b93dcf2dc1bfa188c7ea1ea9198b2bd2eb19e93ba2aea18e28b4be3cb18aa2fe1bbd188d38ce2fb7b829f2ccf69869f18881ebc18ba7dc4ec1c9919ff1eef2c9918f5985fd81a8a6f91faf3ed39f3cc2ba18bc4ec1b878f18cf2cf4fe4ae7cb497aa79c28c1ba96b82ca19cb18b939966ff1cbb3991ff3e5db2a919de2d9e4fc28c97dc7b838828b1ecd1e8f2c83fb4a3b83fa1ca1bda49b5bf1b7a92af2986cc2dd1b8e1bfe1ccb1d893e39e5bf1b19fa188b5af18ad6c969f199a1fbc3bc02e93a82f4fb29da1a982f189f198d1e8198a3f18de1dc2cb7ce7f91ded288e5fb5db38c1eae18c95cdd1ca82fde7ae2cd2ff1895f87ba3ac4cc2cd1a893df5a19c91fd1db1c886f81fb5bf1f81bc1b8b19bd19bf295bf2bc1bab7c978a2ba19fc1cb8198d58f6a2ea1dc5e848e18bb18c928f3ad5c1cfa1dc819dd1ae918d4fa4c6ac7c9481b8a18d81fa48f1dff1aff6aa59e1a982fe3dd6ad4dd4cf4df19fe1c918b69d18ec2b883e81fdd4fb7ea19be58f1bc918f91da1afe1ae28c81acc6fc2cf11bec1efc2da40002d92b8b28cf4b818bf1a9919eb2d3ff39b1bdb18e82baa7be29e1dbd1ac695bf7c81fa84882df189f1fc3b58a2ab2da91aab7ec59a19f78d5f91cdd1bee2dd81aba2bdf2e48919c949b2edc2a884b81ceb1cad7d28f786ac19cc19c92afa3cc4f81bf5ba1bd3ca19b3ab1cde48d4ad91b3ef1ced6ae4959c5ab386d6de71c1eac1cfc1ca1d82adb1f8919df4df79e7ec5da2fb78e4d8789198d38f1fad4fa2d84df1cdf1bbd79a2abe5ac1dab1acb19981dc84f82d19b6c918fb1f9b1d9d4bb599e3af18cb2e883a91e8b18cc2b8a1e9e2dbe19ec2add2bef2ae2b818d9199b5fb3b83fc18be1dab2abb782ec819d6ff1ba2cce4ba2de21a81fb18cd7de1eec49d1ecb19aa2f18e91da91eed5b92fe7b5985fb1b9d18f4a8c1bf4dd1fbe188b6f818993e1eb29f7f2939b7a91eb1ed1caf29bc19ea1ab81df389d1fcb38d29dc18f85ff1add4cb4d94c858978d3aa1aba2aaa1de2e8b2ac93d929d86ac19c639e3ca18ac1da49c6fa2ba2bbf2dc4fe2b895cd19e1a8d1dbb6b91b8d28d298a2e8e1dbc68a4fa39e1db3fd6fd19fd2cc6ac1af19dd386ea7fc4a96cf19991b5cc28c29e1a9f6ef2de4ea6c91bbf3a84986cc1fb6b92eb5c82aca19f839c1dc9293a81b919881ca1bce2f84d2fb4bd5f94dd73da6e85fe18fb183ce18ac1ccc1919fb3b8b2f9b6f97c87e82ae2eb5c81baa5b81b96cf7e1d8a1dca18ac58d3eb1d913a1b93dd29f2a92cf38b51f97b1b8692a4bc29a1ac39c2c81e1dd6c4c4d2b18c28c1dc1e84d2bd39f1bb5b3189188592b91dd5e2887a5e82af3c96b3ac3ac1ee2a84f7d2b684f4bb2ff1be4bc1a1bf1ef2b9229f5d1981ba19818e291ed5b1992bd18c4b859e1af5f92fd49838a7918d28f1db1ab4f4b2fb2dd2aa6ac5fc4c792891f1a919e3c3e291eb2fd3bd3ab1db4a29d1f918c19c6c69385a18d1dd1ec49c3f4cb4e91cf31f2d18c1ee1d5b391a91ef28f2d97b2fc2fc2cc1f818e7d1ae7c3f19791ad1fd6a19a2928f28b481ea687975a6f4f4c1cc4c3c18a3f1df28b1d91cd5a59c39a1fb2bf1ad3d4ec4f582ac1c1c2ed696a2c2a87be3eb6cd5886f94a2e1fa78a3b948b2cc18f18a2b91e9e1cdd28e5c29c2881ae4a19f19f7d191cc2884e291ed1e92c96b1c82ba2ae2bc28e1d82f1ff6d4f1992bb1cc48f1ba3fd1ab4b1d1c93f28c7e3f3993b482f1895f6f194a2c4829a2f81ca72891cb1a181b2c29e38a1ea42ea2ef492e828b2bf1db61ea1ac19c2aa6a2d828e18a7d29b5cf3b82de79b59c385b4ab68969c4ec194d4bb4b1adf19ec2ac48f5dc1af18cd1ff18e3ac2aa2b4cb18cb1de1afe18b93fb39f7aa7e828cb4aa1e9e2bf93ae5b829e1f81f819c1e2af29e2df11fd1eb18f1fc38e6c1f1ce1ca5b1ff2f5e19c7e384c5d1df7d19d6d2d2c281895c1881d1af7d4a6a28f2aa1be784fe2ce5a1ee3a3b6b1d918919f69491bc5cb1c81b91c2fe3c029f1d97c5f5a7a1dd6dd1ff2984e5eb5d6ed4eb7de19ba38c18c1cc4fd6bf2ab3981efc1b993eb6bc1c939f5cc4f481ecc58a18dd7fd4cc58e1a982c8d18dd6d693de2bf3e581ae6e5c5c1ad28b1df2a92ed1ef1cf6a85883ac6a94ae5bb3eb3af71dd2fc19a5f5a81bd3e281d9692a1c48199c1bbc1ef181ce2a91d9f1b81abe2dda19ea6dd3bcb1eef1bd28d5bc3dc4829d19b2cb28d1d91aa2ac1ad3af49e3bc6ea5d84ce198d2bb5f87f1ff6a6a87ad6ed5dc28c58b1ceb1cb84a82bd28f1ef2de1bb4dd1e81af69c58a1892e499289a5fe2af1c93ff28c1cf4cd4893b281b2de5982a81881ed18d1be4af391af49a4e94fe2fa3ea783ac5a3fc3ae18ff5a2e83ce4bc381df37a7f91afd3d4d29c3bc1aa81e59929af48b1b8e2ccc4f83e1f1c82be3ec5984be1ea1c91bb18b1cd3af5a92fb2be19fc6f829d2eb2f91ff458c3ea7cf1bb49a4b95dd19d4c87cd6bb3fc4ea29e6d29e2ee3c1af5db4cd3f12e48f19f1bf19b7b1cf1ab291ac1ae18b2df4f18c2fe2be38a6ba6dc6a85a3d1cf2cc39c2ba1d1d9284f2cc24f919f6a4f48a2ac2ff38d6d781ab6b5ce2a873f2884a1ee3ec2ca29f7fb7a94f91ac1ce48c2dc19e3fb58b3c93f481cd2f94b5d1892982dc1897f1be1fa1fe7a1aa1fb1892e3cf1c92de5d958d3be1da594e929c1ee2fc52af18e1bf1bb1cb1d907e3a1cf29918d3ba4ca1de1df3ab2b29e1fe5285bc5dc19e06c2d3af6b6a2e81ba2bf2f91c1ef3ab79a4b83c2e3f92cd293e7818a29a3ac1e5931b82a929b3ca4fe1e28d49f28f4fc1fe4ac2a18d3ff5ad2fb6a28e2da1fc1ee2ce18e4f1ad7d3d5d4d4ce4c8183ff4fb3ed7882c91bc1b2d481ef6891cd19d83b486e5e29e4ad6d29d1bc94dd5ed3c5d97af19bc28ea792dc3ba6bb18cf281bfa5d83dc6d91c5cf4f7ba1ad93ce1dff42df38d3a2c2919b49b19c2ca5a3f4ed1e9282fa3cc4e5d2f2ac1c84e04e1b819d1ef5bb4fb2bd1986d84d81ec781d96dd69f38b19b3ea3cc682f9183ea1ea1e91fb1be3ba1f81e4b4e1882d8281a8d1cc49c5cb3dd3ac68c5de2c4df3fe3a84a2fb4eb2ac18e2fc19d83a85ea1ab18c4e86fb188d1c39d59b5981fca1c8e1f93818f7984fa1bea3ec6b189a1c013600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000029f3b93b93bd2ed6b5e7a6e497d5f14b2bd2ab1bf7b5a19a1b18f4a7c6c1dd4d5d3df2cf1ab1ad1bd1eb29d1d28c684f294d3d5e7e18d1bb1f18b1df7918829e19a6a19a19e1cd39b2991a919d6b1c6c6c5b818ac3bf18f486f29d1bf5982cbe7a86df3cc1c1fb1dd3da1fa1baf1cad4be3d81bdb5bf1d782de18a1d85ad1ba1e83b815e6c93d92c381de3be3b29a1fe1b83d193e1897f3d7f1bd3be1b9c1eb81df3ef28c5dc2be2e1fa91fdb2ca92d2cc1fc18bc18ed7819a3b1ab491983cb5bc19f7b919f27a392c1881ec29a1ae7c6ea6bc49b2948c18ac3ae4bb1bef2c9283e3db18b93d1bb19b3e3c395bd28ad2eb19be6d1c1ba5a4df4ed7aa19fc19b2ae1cda4ea3b3994db18b394ac492a6b1be386ce3981cd2e92b91893bc19e1a4c3ae195893db2e2de1fa3e59919ad1bc93886dc185ed2f95e1dbe19fc1fca2e5f94a5df69a1d919923a2c1f3f829f2a86be2ba4e1cb2bf3db2cd1f91bb5b2e3c92fd5ae19a4bb19ad4ef4d81b8e1ee7d1d92d6e2d1cc3e3d6c2e7938a18c3bd5b7b4a1cc6a582a92e94a5b1892d39e2ca2885e781bb2f2e61cf1db4bd48f18b1b819c591a918a2c828e5e1ea4982ac6b19d1a91fd191983ca1dc1db1897c29c28a3d3ac5d5e3ae1ec3de6e1fc1aa18c382d5d7928c3fe4c92d918a1bcc5e33897cd491f4bc6c84a00000396db69b12a82fe3d1b992cf5f49c5e5bd1aae7dc1de4ff3de4f3e9188a1cc001df6db2f95d7c5ba1bc1ea1b82cb2bd1ae2ab3cb4b97a2f82cc1c95991f9682fa5d3d94f1cb7b5b83be1de6b1a9186e1d864d4807d1bb59199399792d1c186b5973a1b2d6b1af1891af4a91ac28c6c188b189382dc5f85c43fd4ab381c96b3e1e6b3b4b84cc2e5b1db5b6981eb28f49f1a93ba19bb7e929d4b82ef691b87d92ab1f92cf1e93aa29c3b29b59b1f7a2e3ca3da4b28a3c859c28a198281ad3dd1ac19a19b2bd2ef6d51d92bd38f2cd1ab696d29f2ee3fc38c1b87a2ce1ee3e1e6d28b283bc4be5984ca5e1fd7b5b4d3918c1bb1cf39b2ff2fd184a2c18d2bf4a5c2c5a19c2da19a1b939b1991da5f28b23ae3bc1c83ad1cb191b8829f6d929e29a1aa3f5e7f1ad781d2f2c1e1e828e19a69691a4aa3fa1ce4f82f869585d818c1ff18d4cd482e187b1ba3ec18e1cf18b593f3a391fb1bf63e1ac58e39c1985ff29de1ce001c928bf3d819ac1fa69f18a91af5e2aae200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000037db3eaf18b928cb4cd1892d83ce7e2b19b2a29a28e5b2b4c82ee1c82bc2ec2bc3b2a92cb6f2f1c92fd2e91c919f7d52ac6a219f7b86e81838f1db4a1ba29c4ca5a82ee4d1897c2dc1d86f3c92ef3d29a2981cc18d1ad682882e18a1d83ac3dc7d4de4b87f5ad3ff1be28e4de3a182be218d191da3a81cc181991fd1b1ab92eb3d3d28a7ee4ab199f5e9718fc2e8829e000000049791df6d1d1d81ca1cf19d19b1eb19c3a82c80000000000491c91d92b1bf1ac3fa2c193ad49f3bd19b1d81fa4a5f1a919f5f3d1a919b1ca2b81e2a96d5f1bd1af36f1b31af29d7819e1cb19d19c19a28f2eb5e3a1b18e19e1ad792981ba5b4d2be2dc2e81ff796972848c4e81de1f7f2dd4b1ec2ae1c1f82a3fc187f28e5e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018d2dd1ab36a1851dd1c9591fa2982981d848000000000000000000391bf2c785e00000033d1f1f2f3d1ab1ab2b18a3a8482003222938b59d29839d77ae2b840000192db29af1db97f97de18aa5dc38a69c38819a4bd1dd5ad1db91aa86ae4cb1fcb59978d3ee28ba18987c919bd49e29ee18da1aad1dcb18ed62cda18a7ef7ac6f818d1ff549f19e1ed1ebf4e1bfa1cac5d81ee21d1cf3a4d1f81a003400000000000000000000000000000000000000000000000000001d3ff6c91eed4bc93c8d2bcd29ef2fbb3f91991dad1baf31bc5fd1cab68f5c81bfc19ea3ea19dd28849e6ed3bd18a1ae128e44ae1bbe1ad18cb7fd38d69781dc4aa3be1de3cb4bd3cb29f7f19c2b82d87a1de2be3f82aa4819f48939f3e1ca381aa2e839c3985f2a96218b1eb29d2d92b3a85982ae2bf28e1aa1bb1fe3ba2ae1ba1ce25f4e19ba7ea4be4f94dd7918c4c1ae4e1bc39c78829b82fca2cec2bac2d9e2daa18a80000000000000000000000000000000000000000000000000000000000000000000000032191bb19b1d91ac1e29e5c13a93ad483aa2fa0000000000000000000000000000000000000000000000000003f19919b3d2921e3f1cb18f6b19d28b1df293a5e3a1ad1af28851ab19d3b18d1ae39e38a2be6d1e9697a1d8584c6a28819c693891bd3c93db2bb682d82881be19e38e2cc1e1cb1ad25e7d2cb3cb2f91eb5d1eb1ad6919b2bd38b1b91981cc5b51ec2da38e2fa181fb2ef1ab1982bc2ea29e2c7d02a18e49a49c2ea7c6821f682a2d3a4000000000005d4b1aa000000000000000071af1fd18f19a1ae481dd3b1be68585a1e2000000000000000000000000000000000000000001492996c2a3cd29c2a929f1cd1df2eb3b92bb2e93dd2db19d3f6c28841c38a3fa1fc53a1ec2b82a85a2e1c81cc786b4f7c5e18a2c18f291fc38a1dc205929f2995f1a8281cd6d3b2c1919b1bd72ea3ec2ea3c0001df38b7f3a002e01bc1dc1fc01bd7f119a198492dd1f961a4c1a92f91fb2b391896d18b2a3a793a2d7a49e6b7c3582ae5a7f1fb28d2cf3ff2b92d3be1af6a5d1691bd1cf3bb2c7a287f03dc3ac2ba3f838f3bf2b2ac694dd48d1cc1f81ea2da1d82ec5ca5c82895ef6ad38d4af3e91cb4c95eb793ea2be3cc2cc4dd49f1d85ba5b838a33b93bd4f1ca3a84ec4bc4d1cb5918f2ae5b18a18ab4fd2bc18bc6ae3a868918db3b939a3fa1bde18de60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018b2db3a2e486b29b2ed18f6e7c2ae2ba1a1ba1b3a4e4b7b5a1982a000000000000000001b495e000003b18f7f2819819c00000000000000000000000000000000000000000000000002f28928929f29f18d2f6b6d3919d1fb2f192a81d818a1dc1bc1db1ed03d2f5e3881ee1e618e1fe1ae2c391fd2df1af4e52ab2cb1ab2a29a29818f3e91bb2a1b8687d18b7c11f1ff1fb4d28c1c81df1df79591bb1bf592e1941a82fa4982c8719b3838c4882985b2891e96f1a92893f3c74f4b5f5b7a786c7a2ec3ba7c5c1bc5c4f1e1cc5a28191bd2bd28d18f3b18d42c1eb2af1e91b4d5a1fe1881f3818e2c819e3f19d3d2b2d391a818e1ee3d81ae1985e400000000000001b1df492d1993c4853a1de188001b92bf49d59b5cd3cf1ed5b28f4893cb4f1c2b19f189581de72d93cf4cf4ed3bb5d3815d6b1b9592982ec1ca481ac1f85a1881ee1f81fe2ba2ca1f85c3a7818c1ae1dc5e5d4f28b3df2fd1ad291b92d94992ff1db791f681ee2c81ec7a29e3ec3ae3d858e3aa12df29d6d1cc2e81a74c18a1ce3af1ef2fb2891961a91892d3d0181b91891c5f18f5f293583c283c6a1aa2da2ac1ec2a1dd19d3c1982ac2fc3b83ee2cc3a82ca38c39a1aa19f1fd39f4992cf1f91bb294e5c5c1a82c2dd3db1eb19d18f1cf28918d5c1dc29e38c3ba2ce18c7b6d5b4b5d1d3a4f1eb1c919b42aa2ca18c1d4b76f7f1d19c28e1ba18828e1dc18c2e294bc2b819e1a83d2f1f691994b1e1cc38e1ce28002d791b7e292b4f1991f73c5c5b18d18f2f18c1e81da6e400000000000001493d18a00071803b4d2892d92c901da1885b18f2d25d2bb2ff1bb2919d1ad49397a1fa1ca784a19c1a81be2ac1c81ce6819a1ea2e52d738197f1e5c3c00000000000000000000000000000000000000000000000000000000000000000000000002d5dd18a4ea28001b1c000000000001b92af2992f6818d3d94ab28b4d1ad1fb794183929f299381ca1d29d38d2f91d9491e1d382e838c1dc19a7e06f6d719e19e5b1db3d3a3b1991a91af1cd595c3e15a1de18e1bc1fc1da281b83883c82fe2a829e28e1aa1c6b5d3f3b4f6b197829a1e8287f1db1fb1c829b2b929c1e87a1ac1c81b8381d2b1ad1bb69471db2891bb7938681bf2cd2b2c81cc6a2ac1fe19c7597f18591fd1bf594a1d81ac5e1891ad1b1da29a1ee2b81be71d3a5b1bf2ad3eb3b939d29d2b2aa2ea1ca8380000000000000568d1edf69b1a1bec11a9e4ea1871a918e918b5bf198a4ce39a1b28969d1ad91f9e3f820001020196f4ad4bf2ce18d28e5a87b3997fb1aed39c1b9e1f84ac4e5bf18fd18ba4fc39c5a0000012c96ab38f4a92aa6dc1ae2ee2af6e6c2f93db1a8685e19a1bc1ea2dc5a000000000000001d49f3b94f1f83be1cc19e3800000000016dd19d91dcc1ec18a06d1c7919cf1adb689188d5ff4f91828b2c82fe5be6e1a87ce18a286918e83dd7d878c2da2c97cd3bd5af29d5f81baa3c93af48f4cf4b91df18d1df39d3995a2fa28f1cb4bd58b1e1b92bc5b1fb3e2aa3c1fe1d81f92cd1af2c28e1ca6e18818e1db189919d1ba4a28f2bd19b1cd21c84ce3cc1da4a6d791ee68e7c3ef7db2e979d1e91ec3aa3de6b87cc199e1e9d39f39b1dd382986fe4ae7fe59a4fe2c82a82f2e87e1f3b933b6bd38d19e7818b92c85bb2995aa28e2d1ff2ad39b28973bc2be3ba2d82fe2bc29e2bc38e3d819a1bc4ae2f819a3c391cf3bf1ef3d15c1987d29d62983c2a4e7a1f81fc4c191ec5c3e618000000001b2db49b2eb1fb1e2e1bf39929d29d1db1896b11928f1be695d7d19f54f5c2b82ac129b3ad2eb3db39b6f1b81c18d6d1895d01f81a918a1da1bc1ec3a1fb7f6e7c1cd4db4d94cf4a93cd19f1e1b81881e91af1f181ca1ee2ba1ec1be2ba2ba28c1b8387f6d1b4e1ac7c5f1ed1ff1cf28f1fd7f4b3f4f3b5f18f1df19d2a2d4f6a1b81ee3a829c4c3c3e19c1fa2ae2dc2fe2c82c829a18e41f82c83981fa282f7b6682e792e2ca3ec38c3cc2ee2e29b2e918d581cc1c818a291f391ad5b2c1da3bc1cc53e1be1ea38001b1c00000000000000000000000000000000000000000000000002b2a207180000000000000000000000000000000118b184d3f3a1da0000001ad1ab3d1531c63f693e19e484d42e3d2993af2bf4b3c6c3f1db1dd1919c1be4d19f5f181a8581a1c1bc1887c6a18a18842f3381c5c7c26d619a18a1e76728949f3ff38f1f929b28d1f91ab02e1a82b51e4d1ef1cf11cc2aa29e6d3eb1ed1f83ca383c93bf3bd1ca682d94ad4f93eb19a1a1df1c7c1ba5c61c04d5c28e1aa4e2a1e1c82f82ba1a81b583884c81f83e239391ba29e6c1e5a19e1c82de2f81da1f838a18a0000000000000000000000000000000000000000000000000000000000000000000000000033f2d561f523d18f18a19e2546b5928a00001df3d29c20000000000000000000000000000000000000000000000000000000000000000000000000000005b1cb29938d3fd4ab3d92b929d2b929f2c91cb1af29f4af3f94893991bf6e1882281ef1d93b1b1d1d4d19b7b1ab2b92af19f5f1892b5814d1fd1e92ab28f19971b2f43b19f19f41dc2a829e18a6b7f381a57e1a3f1a6d1ab4b618f28f2cb1cb29d2991fd1993d6949581ba1ea7e28b3e93bb29f4f1ac2aa1a802a72d2a19c1dc2ac39a3ea3ea2985a1de2fc3ec4ee4ba1fe6c1ea3b84ce4aa2c8197f1af1f97f1c7a4c2803f181da483818a3a4b0386a3c81d3ba7851f81a81cf2bb289391de2ba3b82c81ba69e29d6cd6fb1c1c194a1f1cb22ca3a83fc38a18e19f1cb1a91b791996d38188198587c48569795c1dc1ae19a628b2bb6d3e1883e3c1c5f1cd38b3bb2bb22881fa4c11af2cf19b7e1e18d1fb2db2cb2bb5918b2ab5b19a1ee1da78281ac1fe6e1f5a5c2b5d2785a581ad1ea7d19a1e28f2c96d6e28e1c81a1e3f18d2a96ab4e4ba5ca3c11a11a1bc19818d2cd3c91fd2ac3e828c1f838219e1cc2f6b2c1c86e18e4c1d5b2b1b1973931a7e1d81884c1ba2a82f838a39c2b81c4f18f1b4681dc39e46f7d0683c7d1f92db691ba5c1982fd4d1e96f5f1ba19f7a19c183f35a6f1ed1f918f1cd1ab1b96a28c2ea2ea6e1dd2892f281b1d581ce1ba4a491d4b4f79197c1981ca4e3e61bd2bf7f4d3e3c18f1cd394c6e683e191991db1f3c61b3f1bb1fd18f395d382981ca7919955c4a1e72e6b2bd3dd1cf2d1da1933f7b6b619c28c5c4d293b39a1c1f1818e4e2bc6f2ab6b6b7a19a29a1cc1b82b82ce1885e7b1dd2891af6b292c19e4a1a1c93b2df2bd6f4e1c5e482ae295b4c1ae1ac1bc2981ed2d1ad1cf1a92d4835d691db2bf1ef1995b7a1b5d1ca2981fa2be18e3d6a2b1b91f91891ff1f92af1df01ae1bc1b81ee29e3ae3887c18e28e7e1da1d819e2f6919b581a81b85e1b2c1e691bf1b94d1fa28e1ca5818a2e491a51db28f7b1f1ae7e4f6d3b21805d1d91c93a19a4e618f1cd3f1fc4881ab7d1c95f7c1ca1cc581cc2bc2ea1ea58284e000000119b1bf1d918c7c1aa18e00000000000000000291df29f1ff5d1be5c2b1911ae2d818c2c002b1db1bd51e392b949f3d91ed1a91df1dd18d3b6828a1f82818b3a93bb2cd2af1992c1d195a2b82a8781d3b4ee4bc2dd1a4e3c94819928b1d3982dd1e949c3ca18e1c91f2db6cf79d59a48c3b82af19fa58c4ee1fc6e28c78020000000000000000000000000000000000349f1a8f4af7ea18f6d85bc6000000000000000000000000000000000000000000029d29f2981b929c4c28d69f19a9189f5ea59a18f29d18af1ae938f48a28c38c29b48b5c9189d18e198a3ba7f1db5be18b81ba5fb189d7bf2f86e49f2c949f3a92e2fd6eb5fd4a5ba2a97f7584ea1cd81a981a8f2ff5f93f92fa7f19d7b12e5a182925a2cc2ca18c1893ac4cf1cb4f5c1dc2e1ab19181893e94b9695d62982b7a29c3b81c82d85e3af3ad2bf3b5e4bc69c1ddc18f18eb5b92b86f95ae38da1ec848a1baf6c93b69a6c818ff7ab7f92eb1bc5ba7981ac6ab1a95aa1f6ab7d92ab3cc7fa7ca291bc69c3f828c2a81ea4ac58a3b82f2af1ec2d29b1ad1994b959b1be4b1cb18d2af7c63e1c6d18f3d1e78281996828e38a1b938a6828294d19a1981881ee29c1dc686d1ff1eb691b296d28b1f91df1c91891d1981de1a83a3c18eb6b38a3a83b81a8e5a29d928fb69d1ae819d87aa2da2c95ac59a59a2c801af1bd1e918e21cd2ee28e1a0000000000000000000000000004f2cf1f9697b284f1af1c97f4f7b1cf1bd294a1fa1cc49595f1af1df593d2d1f2e28e3d83b829e1ba386e1f81de1880000002b1cd4796f3b1f1d91f1fa29a1a8189792d291ba18a6c01e0341f19b4f12b2e28594f2bb18b691df3cb49d2e92a92991dd2f1ba1ae7d182ca28e7a7c1ea1cc1d82d82e82e81da1e81ae000000000000000000000000000074d1bf2993a92c9189118819c4e48581b84e14a3f1db2ed28a3bc1ca4d1bd1e82e83e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000491391901980004b2cb7a1f1ff1bd18c2ae2ca0000005518b18b56e19c38000005d3b71a4e4820000000000000000000000000000000000051a91cb1bd1d04f1996b293f3a1ae1aa4a01a283e7a7c2c2818a1800000000000000000000000000035f2b6a2e00394b19192d797b67c19a682a2806b6840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000015b1cb1ee3c0000003ed1ec3e6e2e2f23a2c0000000000001200000000000000000000000000000000000000000000000000000000000000000011df4f06d3a80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a9d1cb1af693f2a2e3e4a2c41b413f4b287818e29a2ae1c801ba2bb396b4b492f182f4d2e2b3918484a285a2e2e4c7819e371aa1ee1aa033c3d19f7b5f3d171bd18b3d7a069838000000000000000000000000000000000048cb48c2cc68c4df55e2bd3bc1e8e2be2e1ac3a81be2400000000001200000000000000000000000299d1bdfd6c93a82d1dcde68e000496cc97aef5bb1ce981fa800000000000000000000000000000000003cfbf2cb87de4958a28a29a5ae4e6cd2bc3ee1be1ad04e283c1bc1ce1aa6b4b2d91ad591882a83b83de39a6a2991ff1fb2eb2a91ab1dd19d1ad4f4c6c1e6a181be2dc3a81fc2ac2ae819d9e18b81fb4cf1adcb3bd3ee2ea48a39a5ebe6a9c4cbe3d9d5fa84da0000000000000000000000000000000001ca8d31bb681a93c94b93848a7ee2a81da48a1bc18e1ce2c82ac3981a8481ce1829a2ac18e6f38d3bd2dd3a93cd19d28f391bc3b1ab18f1a92ad3eb5e958d2cb6b1fa2ec2de2ba48859b48f1cd92191b1db83b94dd39d3ff5a6ab7e93dbd4bef6cad1ff6dc39c1a818a28b1cd1fc3ec4b86ea48c29e7a4b69396f6b1d5f3b4b18e1fc1e2a82b84ce4fe2bc284fa2db82ecd805f97af48d3a93c94cb7cb1c9f7af4db59b4cd2eb31bd4c96f958d4c94bf1ff2ed39938b2bb28b1af3b1fe3a81da29e1fa5a1aa1e82f83ae38a2cc2dc1fc4d39b3bb3eb2f9491d93ec42a81ff2ad1ef198f2df1df3fb49b5dd1ef18d4e2ab5a849b7b94ff2b91b2a83d4db4fb4b95cb4dd4bf2ef65e5b1fb28b1ef1b91d91bb1ad19d291ef19b1f91f947c497d1dab18ee2c83fe4ae2da18b2cf6b1ec7a1ca4885ea2c81cb5d1ee2fc28a29e1ec28c28c1ca3a4c38c3ea298295f7491ad1919a285f7a1ec1ec29a2e849a5ea2da2928b3cf1ed19b4901fc39e4ca5ca2de5a1ca28a29e2a1b39e7c84ec49e4ac2ba184d591882d81fc6c1f7b691ef28d591c82ee3ac49e3fa2f81b81ea28828c1ce42b61ab28f29d4af6e5fd7f3b2c92ab17e1e82ca3bc2de581b4c6c1881de2aa3dc3ee3dc1f81a818e1b81ce1e1bf1c95681ce2cc2be1cc1686a7d1a94b718d2b92ad328e1fa18a391d19b4db2a97b3b3c818a7a19e7c793cf3bd5d4a818e29b2ff19f181d62c3d62ea5fa68e4da4bc4a83fe3fa3aa2e83e4e1de2aa18c4c1a81ce19a3918f4a1ae282bd6ff2db2fa4dc49e3be2fc1b80000000000000000000000000000000000002f1cb7f3923c1ca1ae01991886b3d1bc000591b93af6d2d83da00000000018f39b5df3f95b018b2ad2dd1fb2a91af18f1cd1fb2ed2ad18d1818a18e2c5182f3891d9e1bfd1beb4b95a1ca1db4cb781eb38d4c96a95ef58948b4ef4f948f5f96995fb4db3cd2ef28d2a92d92bd1ad7b18d2992ef2fd39b2ef2df2af2bb3cf4e93f92c91ad6f18f491e2f1f92897c3ba1b91f92c938d7f2b6b5d7a4f82be29b6bf19d29f1fb1c91ad19919f1cf2ab1d91df1af28f3bf3ab3ed4cd5bb4e92fb29d2cd2e91e94f18b1ef2ed3cb38d1ef1af1db28b3cd39cb189e78a293c92bd1ea58c3e1e81d83ca6fa69c5aa5aa6a85e848e4883b83de3de4ac49a2ac2cc3fc2ea18c18c1f4d392b3818a2a4b4c2be3bc2d81fa1ec28e2de2f828e7e1b84a18d2db1c919b6d1cb19f795f1c18e1b3b5d3c4b3ec4cc38a1ec1fa28e2aa2cc1ba2a83e828e2821aa1ee1fe7c394d722e584c6e7c1be2ac2da2ca39c5ba1aba2dde38c18b2ad1bd2b7d19b5d2bf1895f2fb6b1b19d1a92ef2df1e96b1cd2db39d2b93e6c19d781ee3c1fc29e1aa1da2881aa2dc4882dc51c928929918b61cd3892cf1dd1cd2f1aa3aa3dc3de3da3ce2f81de1de4e5f18f7b2818a1ca7b1fd77e1981ca2aa28e2fc29e581ee3ea39c2dc2de2cc39e3e83ac2de1ca2d5d3a7c29829e7814b1db2fb48f5fb7f1a83ba2ac35d7b32ba48a7ba1bda19aa33e3c2fe3c83ca2ce1ea48319791bd1bd2cf2cf7f494c1fe1ba229596d5e3ca49a3d82ea1dc4e1cc1d86c7e18c1ac5c20000000000000000000000000000000000000000000000000000000000000000000000000000000000000006919d1893b2b1818c2c3a1cc2c0003b32e1a1191c00001d493838000000000000000000006d693c7c280000000000000000000000001db3ed2b92df3fb3eb2b96f3d5f29b1d19e6b2b92af1ed291e82dc29a1fc1ba281af2db2ad3f1c181e6e1ea1c87d38d3af3992fb2af1fb2ae1ebe1bdb6fd4ea7ac1aba1eea6ac1039d7eb18b82dc318af1cdd1edb2cef2ebf29a4efa3bfe6d4df3db4af18df29f91efb5a5e81dcc2dca2ae859c0000000000000000000007bbb939c81d83e19c1fd3ad65e581ea4ca5fc2de491ed1aa2dc28c318d2ad38b48d48f3891dd1c28c7a28d38d3a93ff3892bb1b93c28c29c2982fc2984c38919d9189e4fc2df38f79f1c8b4bf1bca1ba2de79c2acf49955ec7da18dc2cf8389e4ad68ff3fbf1cb3ec3bc4ea18ac1fcc1dfc3cc18d18ad1edf1ddf48f382e5268287f2af2d92c96d4a582a84ac6be4dc39a2e86dc3dca6eefe)

private def weights := digit X base

set_option maxHeartbeats 8000000 in
private theorem weight_bound : checkDigits base 111555 15 X = true := by decide +kernel

set_option maxHeartbeats 8000000 in
private theorem square_bound : checkDigits base 22543334906 16 (X^2) = true := by decide +kernel

private theorem pack_size : X < base^30000 := by decide +kernel

private theorem weight_sum : (∑ i ∈ Finset.range 30000, weights i) = 29999955 := by
  apply digit_sum X base 30000 29999955 111555 (by decide) pack_size
  · intro i hi
    exact checkDigits_sound (by decide) weight_bound i (by omega)
  · decide
  · decide +kernel

private theorem coefficients (k : ℤ) : coeff 30000 weights k ≤ 22543334906 := by
  apply coeff_le_of_digits 30000 base 22543334906 X weights (by decide)
  · rw [weight_sum]
    decide
  · exact (digit_pack X base 30000).trans (Nat.mod_eq_of_lt pack_size)
  · intro j hj
    exact checkDigits_sound (by decide) square_bound j (by omega)

end CellCertificate

namespace ConstantCell

open Finset

noncomputable def weighted (n : ℕ) (w : ℕ → ℕ) (a h x : ℝ) : ℝ :=
  ∑ i ∈ range n, (w i : ℝ) * wideCell h (a + h * i) x

theorem weighted_convolution_le (n : ℕ) (w : ℕ → ℕ) (a h : ℝ) (hh : 0 < h) (U : ℝ)
    (hU : ∀ k : ℤ, (CellCertificate.coeff n w k : ℝ) ≤ U) (T : ℝ) :
    (∫ x, weighted n w a h (T - x) * weighted n w a h x) ≤ h * U := by
  let f (i j : ℕ) (x : ℝ) :=
    (w i : ℝ) * (w j : ℝ) *
      (wideCell h (a + h * i) (T - x) * wideCell h (a + h * j) x)
  have hfi (i j : ℕ) : Integrable (f i j) :=
    (integrable_wideCell_product h T (a + h * i) (a + h * j)).const_mul _
  have hsum (i : ℕ) : Integrable (fun x => ∑ j ∈ range n, f i j x) :=
    integrable_finsetSum _ (fun j _ => hfi i j)
  let Y := (T - 2 * a) / h
  let k : ℤ := ⌊Y⌋
  let θ := Y - (k : ℝ)
  have hθ₀ : 0 ≤ θ := sub_nonneg.mpr (Int.floor_le Y)
  have hθ₁ : θ ≤ 1 := (Int.fract_lt_one Y).le
  have hY : (T - 2 * a) / h = (k : ℝ) + θ := by
    dsimp [θ, Y]
    ring
  let g (k : ℤ) (i j : ℕ) : ℝ :=
    if (i : ℤ) + j = k then (w i : ℝ) * (w j : ℝ) else 0
  have hCoeff (k : ℤ) : (∑ i ∈ range n, ∑ j ∈ range n, g k i j) =
      (CellCertificate.coeff n w k : ℝ) := by
    simp [CellCertificate.coeff, g]
  have hterm (i j : ℕ) :
      (∫ x, f i j x) = h * (g k i j * θ + g (k - 1) i j * (1 - θ)) := by
    dsimp only [f]
    rw [integral_const_mul, integral_gridCell_product a h T (i : ℝ) (j : ℝ) hh, hY]
    rw [show (i : ℝ) = ((i : ℤ) : ℝ) by norm_cast,
      show (j : ℝ) = ((j : ℤ) : ℝ) by norm_cast, triangle_grid _ _ _ θ hθ₀ hθ₁]
    dsimp only [g]
    split_ifs <;> ring
  calc
    (∫ x, weighted n w a h (T - x) * weighted n w a h x) =
        ∫ x, ∑ i ∈ range n, ∑ j ∈ range n, f i j x := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      simp only [weighted]
      rw [sum_mul]
      apply sum_congr rfl
      intro i _
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      dsimp [f]
      ring
    _ = ∑ i ∈ range n, ∑ j ∈ range n, ∫ x, f i j x := by
      rw [integral_finsetSum _ (fun i _ => hsum i)]
      apply sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun j _ => hfi i j)
    _ = ∑ i ∈ range n, ∑ j ∈ range n, h * (g k i j * θ + g (k - 1) i j * (1 - θ)) := by
      simp_rw [hterm]
    _ = h * ((CellCertificate.coeff n w k : ℝ) * θ +
        (CellCertificate.coeff n w (k - 1) : ℝ) * (1 - θ)) := by
      simp only [← mul_sum, sum_add_distrib, ← sum_mul, hCoeff]
    _ ≤ h * U := by
      apply mul_le_mul_of_nonneg_left _ hh.le
      calc
        _ ≤ U * θ + U * (1 - θ) :=
          add_le_add (mul_le_mul_of_nonneg_right (hU k) hθ₀)
            (mul_le_mul_of_nonneg_right (hU (k - 1)) (sub_nonneg.mpr hθ₁))
        _ = U := by ring

theorem weighted_cell_convolution_le (n : ℕ) (w : ℕ → ℕ) (U : ℝ)
    (hU : ∀ k : ℤ, (CellCertificate.coeff n w k : ℝ) ≤ U) (T : ℝ) :
    (∫ u : ℝ, (∑ i ∈ Finset.range n, (w i : ℝ) * cell (i : ℝ) (T - u)) *
      (∑ i ∈ Finset.range n, (w i : ℝ) * cell (i : ℝ) u)) ≤ U := by
  simpa [weighted, cell] using (weighted_convolution_le n w 0 1 (by norm_num) U hU T)

end ConstantCell

namespace OMA

open ConstantCell

private lemma memLp_weightedCell (i w : ℝ) (q : ℝ≥0∞) :
    MemLp (fun x => w * cell i x) q :=
  (memLp_indicator_const q measurableSet_Icc (1 : ℝ)
    (Or.inr (isCompact_Icc.measure_lt_top.ne))).const_mul w

private lemma integral_weightedCell (n i : ℕ) (hi : i < n) (w : ℝ) :
    (∫ x in (0 : ℝ)..(n : ℝ), w * cell i x) = w := by
  have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hi
  have hsub : Icc (i : ℝ) ((i : ℝ) + 1) ⊆ Icc (0 : ℝ) n :=
    Icc_subset_Icc (Nat.cast_nonneg _) hi'
  rw [intervalIntegral.integral_of_le (Nat.cast_nonneg _), ← integral_Icc_eq_integral_Ioc]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    change w * (Icc (i : ℝ) ((i : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) x = 0
    rw [Set.indicator_of_notMem (fun hi => hx (hsub hi)), mul_zero])]
  have hcell : (∫ x : ℝ, cell i x) = volume.real (Icc (i : ℝ) ((i : ℝ) + 1)) :=
    integral_indicator_one measurableSet_Icc
  rw [integral_const_mul, hcell]
  simp [Measure.real, Real.volume_Icc]

lemma c1a_le_of_weighted_cell_convolution (n : ℕ) (w : ℕ → ℕ) (U : ℝ)
    (hn : 0 < n) (hs : 0 < ∑ i ∈ Finset.range n, w i)
    (hconv : ∀ T : ℝ,
      (∫ u : ℝ, (∑ i ∈ Finset.range n, (w i : ℝ) * cell (i : ℝ) (T - u)) *
        (∑ i ∈ Finset.range n, (w i : ℝ) * cell (i : ℝ) u)) ≤ U) :
    Constant1a.C1a ≤ 2 * (n : ℝ) * U / ((∑ i ∈ Finset.range n, w i : ℕ) : ℝ) ^ 2 := by
  let a : ℝ := 2 * n
  let s : ℝ := ∑ i ∈ Finset.range n, (w i : ℝ)
  let g (x : ℝ) := ∑ i ∈ Finset.range n, (w i : ℝ) * cell i x
  let f (x : ℝ) := g (a * (x + 1 / 4))
  have hapos : 0 < a := by dsimp [a]; positivity
  have hspos : 0 < s := by
    dsimp [s]
    rw [← Nat.cast_sum]
    exact_mod_cast hs
  have hfnonneg : 0 ≤ f := by
    intro x
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (Nat.cast_nonneg _) (indicator_nonneg (fun _ _ => zero_le_one) _)
  have hg2 : MemLp g 2 :=
    memLp_finsetSum _ fun i _ => memLp_weightedCell i (w i) 2
  have hfg2 : MemLp (fun x : ℝ => g (a * x)) 2 := by
    have hmap : MemLp g 2 (Measure.map (fun x : ℝ => a * x) volume) := by
      rw [Real.map_volume_mul_left hapos.ne']
      exact hg2.smul_measure ENNReal.ofReal_ne_top
    exact hmap.comp_of_map (measurable_const.mul measurable_id).aemeasurable
  have hf2 : MemLp f 2 :=
    hfg2.comp_measurePreserving (measurePreserving_add_right volume (1 / 4 : ℝ))
  have hmass : (∫ x in (-1 / 4 : ℝ)..(1 / 4), f x) = a⁻¹ * s := by
    have hG : (∫ x in (0 : ℝ)..(n : ℝ), g x) = s := by
      dsimp [g, s]
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun i hi => ?_
        exact integral_weightedCell n i (Finset.mem_range.mp hi) _
      · intro i _
        exact ((memLp_one_iff_integrable.mp (memLp_weightedCell i (w i) 1))).intervalIntegrable
    change (∫ x in (-1 / 4 : ℝ)..(1 / 4), (fun u => g (a * u)) (x + 1 / 4)) = _
    rw [intervalIntegral.integral_comp_add_right (fun u : ℝ => g (a * u)) (1 / 4),
      intervalIntegral.integral_comp_mul_left g hapos.ne']
    have hlo : a * (-1 / 4 + 1 / 4) = 0 := by ring
    have hhi : a * (1 / 4 + 1 / 4) = (n : ℝ) := by dsimp [a]; ring
    rw [hlo, hhi, hG, smul_eq_mul]
  have hfconv (t : ℝ) : (∫ x : ℝ, f (t - x) * f x) ≤ a⁻¹ * U := by
    let H (u : ℝ) := g (a * (t + 1 / 2) - u) * g u
    have harg (x : ℝ) : a * (t - x + 1 / 4) =
        a * (t + 1 / 2) - a * (x + 1 / 4) := by ring
    calc
      _ = ∫ x : ℝ, (fun v => H (a * v)) (x + 1 / 4) := by
        change (∫ x : ℝ, g (a * (t - x + 1 / 4)) * g (a * (x + 1 / 4))) = _
        simp_rw [harg]
        rfl
      _ = ∫ x : ℝ, H (a * x) :=
        integral_add_right_eq_self (μ := volume) (fun v : ℝ => H (a * v)) (1 / 4)
      _ = a⁻¹ * ∫ u : ℝ, H u := by
        rw [Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hapos), smul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hconv _) (inv_nonneg.mpr hapos.le)
  unfold Constant1a.C1a
  refine csSup_le ?_ ?_
  · refine ⟨0, ?_⟩
    intro F hF _
    rw [zero_mul]
    apply Real.sSup_nonneg
    rintro _ ⟨t, _, rfl⟩
    exact integral_nonneg fun x => mul_nonneg (hF (t - x)) (hF x)
  · intro C hC
    have hC' := hC hfnonneg hf2
    have hSup : sSup {∫ x, f (t - x) * f x | t ∈ Icc (-1 / 2 : ℝ) (1 / 2)}
        ≤ a⁻¹ * U := by
      refine csSup_le ⟨_, ⟨0, by norm_num, rfl⟩⟩ ?_
      rintro _ ⟨t, _, rfl⟩
      exact hfconv t
    rw [hmass] at hC'
    have hbound := mul_le_mul_of_nonneg_right (hC'.trans hSup) (sq_nonneg a)
    have hleft : C * (a⁻¹ * s) ^ 2 * a ^ 2 = C * s ^ 2 := by
      field_simp [hapos.ne']
    have hright : a⁻¹ * U * a ^ 2 = a * U := by
      field_simp [hapos.ne']
    rw [hleft, hright] at hbound
    have hcast : ((∑ i ∈ Finset.range n, w i : ℕ) : ℝ) = s := by
      simp [s, Nat.cast_sum]
    change C ≤ a * U / _ ^ 2
    rw [hcast]
    exact (le_div_iff₀ (sq_pos_of_pos hspos)).mpr hbound

end OMA

theorem OMA.solution : type_of% @Constant1a.c1a_upper_bound := by
  have hs : 0 < ∑ i ∈ Finset.range 30000, CellCertificate.weights i := by
    rw [CellCertificate.weight_sum]
    decide
  have hcoeff (k : ℤ) :
      (CellCertificate.coeff 30000 CellCertificate.weights k : ℝ) ≤ 22543334906 := by
    exact_mod_cast CellCertificate.coefficients k
  have hh := OMA.c1a_le_of_weighted_cell_convolution 30000 CellCertificate.weights
    22543334906 (by decide) hs
    (ConstantCell.weighted_cell_convolution_le 30000 CellCertificate.weights 22543334906 hcoeff)
  rw [CellCertificate.weight_sum] at hh
  exact hh.trans (by norm_num)