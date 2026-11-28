import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_32
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.ModEq
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.Tactic

/-!
# Reduction of `Bugeaud32.adamczewski_faverjon`

Following B. Adamczewski & C. Faverjon (*Mahler's method in several variables and finite
automata*, `arXiv:2012.08283`, 2020, Theorem 1.1(i) and Appendix A, Conjecture A.3), we reduce
the algebraic independence of irrational automatic numbers in multiplicatively independent bases
to two independent classical pillars of Mahler's method:
1. `H1`: **One-variable Mahler transcendence** (Nishioka / Adamczewski–Bell): if a bounded sequence
   `a : ℕ → ℕ` belongs to a finite `k`-Mahler system (`k ≥ 2`) and its generating series value
   `F_a(α) = ∑' n, (a n : ℝ) * α ^ n` at a rational `α ∈ (0, 1)` is irrational, then `F_a(α)` is
   transcendental over `ℚ`.
2. `H2`: **Multivariate Mahler purity** (Adamczewski–Faverjon 2020, Theorem 1.1(i)): if bounded
   sequences `a_i : ℕ → ℕ` belong to finite `k_i`-Mahler systems (`k_i ≥ 2`), rational points
   `α_i ∈ (0, 1)` have `ℚ`-linearly independent logarithms, and each value `F_{a_i}(α_i)` is
   transcendental over `ℚ`, then the values `(F_{a_i}(α_i))_i` are algebraically independent over
   `ℚ`.

Inside `main`, we prove from scratch:
- Base-`b` digit-sequence telescoping: `Int.fract x = (b : ℝ)⁻¹ * ∑' n, (digitSeq b x n : ℝ) * ((b : ℝ)⁻¹)^n`
  for `2 ≤ b`, hence `ξ i = ⌊ξ i⌋ + (b i : ℝ)⁻¹ * F_{a i}((b i : ℝ)⁻¹)` and `Irrational (F_{a i}((b i : ℝ)⁻¹))`.
- The Mahler system dissection `F_s(z) = ∑ j : Fin k, z^j * F_{tr s j}(z^k)` for every element `s`
  of the finite `k`-kernel of a `k`-automatic sequence (`|z| < 1`), by reindexing summable series
  via `n ↦ (n / k, n % k)`.
- `LinearIndependent ℚ (fun i => Real.log ((b i : ℝ)⁻¹))` from `Nat.MultiplicativelyIndependentFamily b`.
- Invertible `ℚ`-affine transport of `AlgebraicIndependent ℚ` from `(F_{a i}((b i : ℝ)⁻¹))_i` to `ξ`.

Thanks to @MechaNuggan for the `k`-kernel Mahler-dissection, floor-telescoping, and affine
algebraic-independence transport architecture.
Credit: @tkaiman
-/

namespace OMA.R_Bugeaud32_adamczewski_faverjon_R1

open AutomaticSequence NormalNumber Finset Filter
open scoped BigOperators Classical Topology

/- ### Step 1: Generating series summability and `k`-kernel Mahler dissection -/

private lemma summable_digit_series {s : ℕ → ℕ} {B : ℕ} (hs : ∀ n, s n ≤ B)
    {z : ℝ} (hz : |z| < 1) :
    Summable (fun n : ℕ => (s n : ℝ) * z ^ n) := by
  have hgeom : Summable (fun n : ℕ => (B : ℝ) * |z| ^ n) :=
    (summable_geometric_of_lt_one (abs_nonneg z) hz).mul_left (B : ℝ)
  refine Summable.of_norm_bounded hgeom fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_pow]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hs n) (pow_nonneg (abs_nonneg z) n)

private lemma tsum_mahler_dissection {k B : ℕ} (hk : 2 ≤ k) {s : ℕ → ℕ}
    (hs : ∀ n, s n ≤ B) {z : ℝ} (hz : |z| < 1) :
    ∑' n : ℕ, (s n : ℝ) * z ^ n =
      ∑ j : Fin k, z ^ j.1 * ∑' m : ℕ, (s (k * m + j.1) : ℝ) * (z ^ k) ^ m := by
  have hkpos : 0 < k := by omega
  have hzk : |z ^ k| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg z) hz (by omega)
  have hsum : Summable (fun n : ℕ => (s n : ℝ) * z ^ n) := summable_digit_series hs hz
  have hsum_j : ∀ j : Fin k,
      Summable (fun m : ℕ => (s (k * m + j.1) : ℝ) * (z ^ k) ^ m) :=
    fun j => summable_digit_series (fun m => hs (k * m + j.1)) hzk
  have hpart : ∀ N : ℕ,
      ∑ n ∈ Finset.range (k * N), (s n : ℝ) * z ^ n =
        ∑ j : Fin k, z ^ j.1 * ∑ m ∈ Finset.range N, (s (k * m + j.1) : ℝ) * (z ^ k) ^ m := by
    intro N
    induction N with
    | zero => simp
    | succ M ih =>
      have hmul_succ : k * (M + 1) = k * M + k := by ring
      rw [hmul_succ, Finset.sum_range_add, ih]
      have hstep : ∑ j ∈ Finset.range k, (s (k * M + j) : ℝ) * z ^ (k * M + j) =
          ∑ j : Fin k, z ^ j.1 * ((s (k * M + j.1) : ℝ) * (z ^ k) ^ M) := by
        rw [← Fin.sum_univ_eq_sum_range (fun j => (s (k * M + j) : ℝ) * z ^ (k * M + j)) k]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pow_add, pow_mul]; ring
      rw [hstep, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_range_succ, mul_add]
  have htend_lhs : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (k * N), (s n : ℝ) * z ^ n)
      atTop (𝓝 (∑' n : ℕ, (s n : ℝ) * z ^ n)) := by
    have hmul_top : Tendsto (fun N : ℕ => k * N) atTop atTop :=
      Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by nlinarith⟩
    exact hsum.hasSum.tendsto_sum_nat.comp hmul_top
  have htend_rhs : Tendsto
      (fun N : ℕ => ∑ j : Fin k, z ^ j.1 * ∑ m ∈ Finset.range N, (s (k * m + j.1) : ℝ) * (z ^ k) ^ m)
      atTop (𝓝 (∑ j : Fin k, z ^ j.1 * ∑' m : ℕ, (s (k * m + j.1) : ℝ) * (z ^ k) ^ m)) :=
    tendsto_finsetSum Finset.univ fun j _ =>
      ((hsum_j j).hasSum.tendsto_sum_nat).const_mul (z ^ j.1)
  exact tendsto_nhds_unique htend_lhs (by simpa only [← hpart] using htend_rhs)

/- ### Step 2: Base-`b` digit telescoping -/

private lemma digitSeq_lt_base {b : ℕ} (hb : 2 ≤ b) (x : ℝ) (n : ℕ) :
    digitSeq b x n < b :=
  Nat.mod_lt _ (by omega)

private lemma floor_mul_base_div {b : ℕ} (hb : 2 ≤ b) (x : ℝ) (n : ℕ) :
    ⌊(b : ℝ) ^ (n + 1) * Int.fract x⌋₊ / b = ⌊(b : ℝ) ^ n * Int.fract x⌋₊ := by
  have hbpos : (0 : ℝ) < (b : ℝ) := by positivity
  have hfr_nn : 0 ≤ Int.fract x := Int.fract_nonneg x
  set M := ⌊(b : ℝ) ^ n * Int.fract x⌋₊
  have hlo : (M : ℝ) ≤ (b : ℝ) ^ n * Int.fract x := Nat.floor_le (by positivity)
  have hhi : (b : ℝ) ^ n * Int.fract x < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  have hpow : (b : ℝ) ^ (n + 1) * Int.fract x = (b : ℝ) * ((b : ℝ) ^ n * Int.fract x) := by
    rw [pow_succ]; ring
  have hlo' : ((b * M : ℕ) : ℝ) ≤ (b : ℝ) ^ (n + 1) * Int.fract x := by
    rw [hpow, Nat.cast_mul]; nlinarith
  have hhi' : (b : ℝ) ^ (n + 1) * Int.fract x < ((b * M + b : ℕ) : ℝ) := by
    rw [hpow, Nat.cast_add, Nat.cast_mul]; nlinarith
  have hge : b * M ≤ ⌊(b : ℝ) ^ (n + 1) * Int.fract x⌋₊ := Nat.le_floor hlo'
  have hlt : ⌊(b : ℝ) ^ (n + 1) * Int.fract x⌋₊ < b * M + b :=
    (Nat.floor_lt (by positivity)).mpr hhi'
  have h1 : M ≤ ⌊(b : ℝ) ^ (n + 1) * Int.fract x⌋₊ / b := by
    have := Nat.div_le_div_right hge (c := b)
    rwa [Nat.mul_div_right M (by omega)] at this
  have h2 : ⌊(b : ℝ) ^ (n + 1) * Int.fract x⌋₊ / b < M + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    linarith
  omega

private lemma partial_sum_digitSeq {b : ℕ} (hb : 2 ≤ b) (x : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (digitSeq b x n : ℝ) * ((b : ℝ)⁻¹) ^ (n + 1) =
      (⌊(b : ℝ) ^ N * Int.fract x⌋₊ : ℝ) / (b : ℝ) ^ N := by
  have hbne : (b : ℝ) ≠ 0 := by positivity
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, one_mul, div_one]
    have hlt : Int.fract x < 1 := Int.fract_lt_one x
    have hfl : ⌊Int.fract x⌋₊ = 0 := Nat.floor_eq_zero.mpr hlt
    simp [hfl]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hdiv := floor_mul_base_div hb x m
    have hdm : b * ⌊(b : ℝ) ^ m * Int.fract x⌋₊ + digitSeq b x m =
        ⌊(b : ℝ) ^ (m + 1) * Int.fract x⌋₊ := by
      dsimp [digitSeq]
      rw [← hdiv]
      exact Nat.div_add_mod _ b
    have hdmR : (b : ℝ) * (⌊(b : ℝ) ^ m * Int.fract x⌋₊ : ℝ) + (digitSeq b x m : ℝ) =
        (⌊(b : ℝ) ^ (m + 1) * Int.fract x⌋₊ : ℝ) := by exact_mod_cast hdm
    have hpowR : (b : ℝ) ^ (m + 1) * Int.fract x = (b : ℝ) ^ m * Int.fract x * (b : ℝ) := by
      rw [pow_succ]; ring
    rw [inv_pow, pow_succ]
    field_simp [hbne, pow_ne_zero m hbne]
    rw [← hpowR]
    linarith

private lemma fract_eq_tsum_digitSeq {b : ℕ} (hb : 2 ≤ b) (x : ℝ) :
    Int.fract x = (b : ℝ)⁻¹ * ∑' n : ℕ, (digitSeq b x n : ℝ) * ((b : ℝ)⁻¹) ^ n := by
  have hbpos : (0 : ℝ) < (b : ℝ) := by positivity
  have hinv_lt : |(b : ℝ)⁻¹| < 1 := by
    rw [abs_of_pos (inv_pos.mpr hbpos)]
    have : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
    exact inv_lt_one_of_one_lt₀ this
  have hsum : Summable (fun n : ℕ => (digitSeq b x n : ℝ) * ((b : ℝ)⁻¹) ^ n) :=
    summable_digit_series (fun n => (digitSeq_lt_base hb x n).le) hinv_lt
  have hsum1 : Summable (fun n : ℕ => (digitSeq b x n : ℝ) * ((b : ℝ)⁻¹) ^ (n + 1)) := by
    refine (hsum.mul_left ((b : ℝ)⁻¹)).congr fun n => ?_
    rw [pow_succ]; ring
  have htend1 : Tendsto (fun N => ∑ n ∈ Finset.range N,
      (digitSeq b x n : ℝ) * ((b : ℝ)⁻¹) ^ (n + 1)) atTop
      (𝓝 (∑' n : ℕ, (digitSeq b x n : ℝ) * ((b : ℝ)⁻¹) ^ (n + 1))) :=
    hsum1.hasSum.tendsto_sum_nat
  have htend2 : Tendsto (fun N => (⌊(b : ℝ) ^ N * Int.fract x⌋₊ : ℝ) / (b : ℝ) ^ N)
      atTop (𝓝 (Int.fract x)) := by
    have hzero : Tendsto (fun N : ℕ => ((b : ℝ)⁻¹) ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hbpos.le)
        (by simpa [abs_of_pos (inv_pos.mpr hbpos)] using hinv_lt)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using tendsto_const_nhds.sub hzero : Tendsto (fun N : ℕ => Int.fract x - ((b : ℝ)⁻¹) ^ N) atTop (𝓝 (Int.fract x)))
      tendsto_const_nhds (fun N => ?_) (fun N => ?_)
    · have hlt : (b : ℝ) ^ N * Int.fract x - 1 < (⌊(b : ℝ) ^ N * Int.fract x⌋₊ : ℝ) := by
        linarith [Nat.lt_floor_add_one ((b : ℝ) ^ N * Int.fract x)]
      have hdiv := div_le_div_of_nonneg_right hlt.le (pow_nonneg hbpos.le N)
      have heq : ((b : ℝ) ^ N * Int.fract x - 1) / (b : ℝ) ^ N = Int.fract x - ((b : ℝ)⁻¹) ^ N := by
        rw [sub_div, mul_div_cancel_left₀ _ (pow_ne_zero N hbpos.ne'), inv_pow, one_div]
      linarith
    · have hle : (⌊(b : ℝ) ^ N * Int.fract x⌋₊ : ℝ) ≤ (b : ℝ) ^ N * Int.fract x :=
        Nat.floor_le (mul_nonneg (pow_nonneg hbpos.le N) (Int.fract_nonneg x))
      rw [div_le_iff₀ (pow_pos hbpos N)]
      linarith
  have heq_fn : (fun N => ∑ n ∈ Finset.range N, (digitSeq b x n : ℝ) * ((b : ℝ)⁻¹) ^ (n + 1)) =
      (fun N => (⌊(b : ℝ) ^ N * Int.fract x⌋₊ : ℝ) / (b : ℝ) ^ N) :=
    funext (partial_sum_digitSeq hb x)
  rw [heq_fn] at htend1
  have htsum_eq : Int.fract x = ∑' n : ℕ, (digitSeq b x n : ℝ) * ((b : ℝ)⁻¹) ^ (n + 1) :=
    tendsto_nhds_unique htend2 htend1
  rw [htsum_eq, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [pow_succ]; ring

/- ### Step 3: Affine transport of `AlgebraicIndependent ℚ` -/

private lemma algebraicIndependent_affine_transport {r : ℕ}
    (y ξ : Fin r → ℝ) (m : Fin r → ℤ) (b : Fin r → ℕ) (hb : ∀ i, 2 ≤ b i)
    (hrel : ∀ i, ξ i = (m i : ℝ) + ((b i : ℝ)⁻¹) * y i)
    (hy : AlgebraicIndependent ℚ y) :
    AlgebraicIndependent ℚ ξ := by
  rw [algebraicIndependent_iff] at hy ⊢
  intro P hP
  let fwd : Fin r → MvPolynomial (Fin r) ℚ :=
    fun i => MvPolynomial.C (m i : ℚ) + MvPolynomial.C ((b i : ℚ)⁻¹) * MvPolynomial.X i
  let bwd : Fin r → MvPolynomial (Fin r) ℚ :=
    fun i => MvPolynomial.C (b i : ℚ) * (MvPolynomial.X i - MvPolynomial.C (m i : ℚ))
  let Q : MvPolynomial (Fin r) ℚ := MvPolynomial.bind₁ fwd P
  have hQ_eval : MvPolynomial.aeval y Q = 0 := by
    have hcomp : MvPolynomial.aeval y Q = MvPolynomial.aeval (fun i => MvPolynomial.aeval y (fwd i)) P := by
      dsimp [Q]
      rw [MvPolynomial.aeval_bind₁]
    rw [hcomp]
    have hfun : (fun i => MvPolynomial.aeval y (fwd i)) = ξ := by
      ext i
      dsimp [fwd]
      simp [hrel i]
    rw [hfun]
    exact hP
  have hQ0 : Q = 0 := hy Q hQ_eval
  have hback : MvPolynomial.bind₁ bwd Q = P := by
    dsimp [Q]
    rw [MvPolynomial.bind₁_bind₁]
    have hid : (fun i => MvPolynomial.bind₁ bwd (fwd i)) = MvPolynomial.X := by
      ext i
      dsimp [fwd, bwd]
      simp only [map_add, map_mul, MvPolynomial.bind₁_C_right, MvPolynomial.bind₁_X_right]
      have hbi : (b i : ℚ) ≠ 0 := by exact_mod_cast (show b i ≠ 0 by have := hb i; omega)
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hbi, map_one, one_mul, add_sub_cancel]
    rw [hid, MvPolynomial.bind₁_X_left]
    rfl
  rw [← hback, hQ0, map_zero]

/- ### Hypotheses and main reduction theorem -/

/-- **One-variable Mahler transcendence** (Loxton–van der Poorten / Nishioka / Adamczewski–Bell):
if a bounded sequence `a : ℕ → ℕ` belongs to a finite `k`-Mahler system (`k ≥ 2`) and its
generating series value `∑' n, (a n : ℝ) * (α : ℝ) ^ n` at a rational `α ∈ (0, 1)` is irrational,
then that value is transcendental over `ℚ`. -/
def H1 : Prop :=
  ∀ (k B : ℕ), 2 ≤ k → ∀ (α : ℚ), 0 < α → α < 1 →
    ∀ (a : ℕ → ℕ) (S : Finset (ℕ → ℕ)),
      a ∈ S → (∀ s ∈ S, ∀ n, s n ≤ B) →
      (∃ tr : S → Fin k → S, ∀ (s : S) (z : ℝ), |z| < 1 →
        ∑' n : ℕ, (s.1 n : ℝ) * z ^ n =
          ∑ j : Fin k, z ^ j.1 * ∑' m : ℕ, ((tr s j).1 m : ℝ) * (z ^ k) ^ m) →
      Irrational (∑' n : ℕ, (a n : ℝ) * (α : ℝ) ^ n) →
      Transcendental ℚ (∑' n : ℕ, (a n : ℝ) * (α : ℝ) ^ n)

/-- **Multivariate Mahler purity** (Adamczewski–Faverjon 2020, `arXiv:2012.08283`, Theorem 1.1(i)):
if bounded sequences `a_i : ℕ → ℕ` belong to finite `k_i`-Mahler systems (`k_i ≥ 2`), rational
points `α_i ∈ (0, 1)` have `ℚ`-linearly independent logarithms, and each value
`∑' n, (a_i n : ℝ) * (α_i : ℝ) ^ n` is transcendental over `ℚ`, then these `r` values are
algebraically independent over `ℚ`. -/
def H2 : Prop :=
  ∀ (r : ℕ) (k B : Fin r → ℕ) (α : Fin r → ℚ) (a : Fin r → ℕ → ℕ),
    (∀ i, 2 ≤ k i) → (∀ i, 0 < α i ∧ α i < 1) →
    LinearIndependent ℚ (fun i => Real.log (α i : ℝ)) →
    (∀ i, ∃ (S : Finset (ℕ → ℕ)), a i ∈ S ∧ (∀ s ∈ S, ∀ n, s n ≤ B i) ∧
      ∃ tr : S → Fin (k i) → S, ∀ (s : S) (z : ℝ), |z| < 1 →
        ∑' n : ℕ, (s.1 n : ℝ) * z ^ n =
          ∑ j : Fin (k i), z ^ j.1 * ∑' m : ℕ, ((tr s j).1 m : ℝ) * (z ^ (k i)) ^ m) →
    (∀ i, Transcendental ℚ (∑' n : ℕ, (a i n : ℝ) * (α i : ℝ) ^ n)) →
    AlgebraicIndependent ℚ (fun i => ∑' n : ℕ, (a i n : ℝ) * (α i : ℝ) ^ n)

theorem main : H1 → H2 → type_of% @Bugeaud32.adamczewski_faverjon := by
  intro h1 h2 r b hb hind ξ hauto hirr
  choose k hk hka using hauto
  let α : Fin r → ℚ := fun i => (b i : ℚ)⁻¹
  let a : Fin r → ℕ → ℕ := fun i => digitSeq (b i) (ξ i)
  let y : Fin r → ℝ := fun i => ∑' n : ℕ, (a i n : ℝ) * (α i : ℝ) ^ n
  have hα_pos_lt : ∀ i, 0 < α i ∧ α i < 1 := by
    intro i
    have hbi : (1 : ℚ) < (b i : ℚ) := by exact_mod_cast (show 1 < b i by have := hb i; omega)
    exact ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ hbi⟩
  have hrel : ∀ i, ξ i = ((⌊ξ i⌋ : ℤ) : ℝ) + ((b i : ℝ)⁻¹) * y i := by
    intro i
    have hfr := fract_eq_tsum_digitSeq (hb i) (ξ i)
    have hsub : Int.fract (ξ i) = ξ i - (⌊ξ i⌋ : ℝ) := rfl
    have hyi : y i = ∑' n : ℕ, (digitSeq (b i) (ξ i) n : ℝ) * ((b i : ℝ)⁻¹) ^ n := by
      dsimp [y, a, α]; simp
    rw [← hyi] at hfr
    linarith
  have hy_irr : ∀ i, Irrational (y i) := by
    intro i ⟨q, hq⟩
    apply hirr i
    refine ⟨(⌊ξ i⌋ : ℚ) + (b i : ℚ)⁻¹ * q, ?_⟩
    have hrel_i := hrel i
    rw [← hq] at hrel_i
    push_cast
    linarith [hrel_i]
  have hsys : ∀ i, ∃ (S : Finset (ℕ → ℕ)), a i ∈ S ∧ (∀ s ∈ S, ∀ n, s n ≤ b i) ∧
      ∃ tr : S → Fin (k i) → S, ∀ (s : S) (z : ℝ), |z| < 1 →
        ∑' n : ℕ, (s.1 n : ℝ) * z ^ n =
          ∑ j : Fin (k i), z ^ j.1 * ∑' m : ℕ, ((tr s j).1 m : ℝ) * (z ^ (k i)) ^ m := by
    intro i
    have hfin : (kKernel (k i) (a i)).Finite := hka i
    let S : Finset (ℕ → ℕ) := hfin.toFinset
    have ha_mem : a i ∈ S := hfin.mem_toFinset.mpr (self_mem_kKernel (k i) (a i))
    have hs_bd : ∀ s ∈ S, ∀ n, s n ≤ b i := by
      intro s hs n
      obtain ⟨e, rem, _, rfl⟩ := hfin.mem_toFinset.mp hs
      exact (digitSeq_lt_base (hb i) (ξ i) _).le
    have htr_mem : ∀ (s : S) (j : Fin (k i)), (fun m => s.1 (k i * m + j.1)) ∈ S := by
      intro s j
      obtain ⟨e, rem, hrem, hseq⟩ := hfin.mem_toFinset.mp s.2
      refine hfin.mem_toFinset.mpr ⟨e + 1, k i ^ e * j.1 + rem, ?_, ?_⟩
      · have h1 : k i ^ e * j.1 + rem < k i ^ e * j.1 + k i ^ e := Nat.add_lt_add_left hrem _
        have h2 : k i ^ e * j.1 + k i ^ e = k i ^ e * (j.1 + 1) := by ring
        have h3 : k i ^ e * (j.1 + 1) ≤ k i ^ e * k i := Nat.mul_le_mul_left _ j.2
        have h4 : k i ^ e * k i = k i ^ (e + 1) := (pow_succ (k i) e).symm
        omega
      · funext m
        have harg : k i ^ e * (k i * m + j.1) + rem = k i ^ (e + 1) * m + (k i ^ e * j.1 + rem) := by
          rw [pow_succ]; ring
        have hval := congrFun hseq (k i * m + j.1)
        exact hval.trans (congrArg (a i) harg)
    let tr : S → Fin (k i) → S := fun s j => ⟨fun m => s.1 (k i * m + j.1), htr_mem s j⟩
    refine ⟨S, ha_mem, hs_bd, tr, fun s z hz => ?_⟩
    exact tsum_mahler_dissection (hk i) (hs_bd s.1 s.2) hz
  have hy_trans : ∀ i, Transcendental ℚ (y i) := by
    intro i
    obtain ⟨S, ha_mem, hs_bd, tr, htr⟩ := hsys i
    exact h1 (k i) (b i) (hk i) (α i) (hα_pos_lt i).1 (hα_pos_lt i).2 (a i) S ha_mem hs_bd
      ⟨tr, htr⟩ (hy_irr i)
  have hlog_ind : LinearIndependent ℚ (fun i => Real.log (α i : ℝ)) := by
    have heq : (fun i => Real.log (α i : ℝ)) = fun i => -Real.log (b i : ℝ) := by
      ext i
      dsimp [α]
      rw [Rat.cast_inv, Rat.cast_natCast, Real.log_inv]
    rw [heq]
    exact hind.neg
  have hy_ind : AlgebraicIndependent ℚ y := h2 r k b α a hk hα_pos_lt hlog_ind hsys hy_trans
  exact algebraicIndependent_affine_transport y ξ (fun i => ⌊ξ i⌋) b hb hrel hy_ind

end OMA.R_Bugeaud32_adamczewski_faverjon_R1
