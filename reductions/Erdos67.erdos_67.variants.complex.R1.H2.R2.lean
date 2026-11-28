import OMAReductions.R_Erdos67_erdos_67_variants_complex_R1

/-!
Reduction of `Erdos67.erdos_67.variants.complex.R1.H2` (Tao, *Discrete Analysis* 2016:1,
Theorem 1.8: unbounded `L^2` partial-sum energy for any stochastic completely multiplicative
`S^1`-valued function) to two completely deterministic, decoupled analytic number theory pillars
from Tao (2016):

- `H1`: Tao (2016), *Forum Math. Pi* 4, Theorem 1.3 (logarithmically averaged two-point Elliott
  conjecture for completely multiplicative `S^1`-valued functions): if the logarithmic two-point
  correlation `(1 / L(X)) * sum_{m=1}^X (1 / m) * g(m) * conj(g(m + d))` fails to tend to `0` for
  some shift `d >= 1`, then `g` is pretentious (finite Granville-Soundararajan pretentious distance
  to some twisted Dirichlet character `chi(n) * n^(i t)`).
- `H2`: Tao (2016), *Discrete Analysis* 2016:1, Section 4 (generalized Borwein-Choi-Coons
  logarithmic `L^2` divergence): every pretentious completely multiplicative `S^1`-valued function
  has diverging logarithmic mean-square partial sums
  `(1 / L(X)) * sum_{n=1}^X (1 / n) * ||sum_{j=1}^n g(j)||^2 -> +infty`.

In `main` and the private lemmas below, we prove completely from scratch in Lean 4:
1. Complete multiplicativity, unit norm, and continuity of the prime-coordinate random function
   `gOf z j = prod_{p in j.primeFactors} (z p)^1 ^ j.factorization p`.
2. Exact unit-sum norm-square expansion
   `||sum_{h=1}^H f(h)||^2 = H + 2 * sum_{d=1}^{H-1} sum_{h1=1}^{H-d} Re(f(h1) * conj(f(h1 + d)))`,
   short-interval `L^2` bound `<= 4 * B` from uniform partial-sum bound `<= B`, explicit
   logarithmic shift error `<= 3 * H` via telescoping `sum 1/(n*(n+1)) <= 1`, and harmonic sum
   divergence `L(2^k) >= k / 2`.
3. Reverse-Markov + `limsup`-measure (`measure_iInter_eq_iInf`) construction of a positive-measure
   set `E_inf` (`mu E_inf >= 1 / (16 * H) > 0`) on which some shift `d in [1, H - 1]` has
   non-vanishing logarithmic two-point correlations.
4. Pointwise application of `H1` and `H2` on `E_inf`, followed by monotone measure continuity
   (`measure_iUnion_eq_iSup`) and Markov's inequality on `F_X`, contradicting `int F_X dmu <= B`.
-/

namespace OMA.R_Erdos67_erdos_67_variants_complex_R1_H2_R2

open MeasureTheory

/- Tao (2016, Forum Math. Pi 4, Theorem 1.3): if a completely multiplicative S^1-valued function
has non-vanishing logarithmically averaged two-point correlation at some shift d >= 1, then it
pretends to a twisted Dirichlet character chi(n) * n^(i t). -/
def H1 : Prop :=
  ∀ (g : ℕ → ℂ) (d : ℕ),
    1 ≤ d →
    g 1 = 1 →
    (∀ n : ℕ, 1 ≤ n → ‖g n‖ = 1) →
    (∀ a b : ℕ, 1 ≤ a → 1 ≤ b → g (a * b) = g a * g b) →
    ¬ Filter.Tendsto
      (fun X : ℕ =>
        ((1 / (∑ m ∈ Finset.Icc 1 X, (1 / (m : ℝ)))) : ℂ) *
          ∑ m ∈ Finset.Icc 1 X, ((1 / (m : ℝ)) : ℂ) * (g m * star (g (m + d))))
      Filter.atTop (nhds 0) →
    ∃ (q : ℕ) (χ : ℕ → ℂ) (t M : ℝ),
      1 ≤ q ∧ χ 1 = 1 ∧
      (∀ a b : ℕ, χ (a * b) = χ a * χ b) ∧
      (∀ n : ℕ, χ (n + q) = χ n) ∧
      (∀ n : ℕ, Nat.Coprime n q → ‖χ n‖ = 1) ∧
      (∀ n : ℕ, ¬ Nat.Coprime n q → χ n = 0) ∧
      ∀ X : ℕ,
        ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
          (1 - (g p * star (χ p * Complex.exp (Complex.I * t * Real.log (p : ℝ)))).re) /
            (p : ℝ) ≤ M

/- Tao (2016, Discrete Analysis 2016:1, Section 4): every pretentious completely multiplicative
S^1-valued function has diverging logarithmic L^2 mean of its partial sums. -/
def H2 : Prop :=
  ∀ (g : ℕ → ℂ),
    g 1 = 1 →
    (∀ n : ℕ, 1 ≤ n → ‖g n‖ = 1) →
    (∀ a b : ℕ, 1 ≤ a → 1 ≤ b → g (a * b) = g a * g b) →
    (∃ (q : ℕ) (χ : ℕ → ℂ) (t M : ℝ),
      1 ≤ q ∧ χ 1 = 1 ∧
      (∀ a b : ℕ, χ (a * b) = χ a * χ b) ∧
      (∀ n : ℕ, χ (n + q) = χ n) ∧
      (∀ n : ℕ, Nat.Coprime n q → ‖χ n‖ = 1) ∧
      (∀ n : ℕ, ¬ Nat.Coprime n q → χ n = 0) ∧
      ∀ X : ℕ,
        ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
          (1 - (g p * star (χ p * Complex.exp (Complex.I * t * Real.log (p : ℝ)))).re) /
            (p : ℝ) ≤ M) →
    Filter.Tendsto
      (fun X : ℕ =>
        (1 / (∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)))) *
          ∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)) * ‖∑ j ∈ Finset.Icc 1 n, g j‖ ^ 2)
      Filter.atTop Filter.atTop

section

private def gOf (z : ℕ → Metric.sphere (0 : ℂ) 1) (j : ℕ) : ℂ :=
  ∏ p ∈ j.primeFactors, (z p).1 ^ j.factorization p

private lemma gOf_one (z : ℕ → Metric.sphere (0 : ℂ) 1) : gOf z 1 = 1 := by
  simp [gOf]

private lemma norm_gOf (z : ℕ → Metric.sphere (0 : ℂ) 1) (j : ℕ) : ‖gOf z j‖ = 1 := by
  unfold gOf
  rw [norm_prod]
  refine Finset.prod_eq_one fun p _ => ?_
  rw [norm_pow, mem_sphere_zero_iff_norm.mp (z p).2, one_pow]

private lemma gOf_eq_prod_of_subset (z : ℕ → Metric.sphere (0 : ℂ) 1) (j : ℕ)
    (s : Finset ℕ) (hs : j.primeFactors ⊆ s) :
    gOf z j = ∏ p ∈ s, (z p).1 ^ j.factorization p := by
  unfold gOf
  refine Finset.prod_subset hs fun p _ hp => ?_
  have hfac : j.factorization p = 0 := by
    by_contra hne
    apply hp
    rw [← Nat.support_factorization j, Finsupp.mem_support_iff]
    exact hne
  rw [hfac, pow_zero]

private lemma gOf_mul (z : ℕ → Metric.sphere (0 : ℂ) 1) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    gOf z (a * b) = gOf z a * gOf z b := by
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  have hpf : (a * b).primeFactors = a.primeFactors ∪ b.primeFactors := Nat.primeFactors_mul ha0 hb0
  have hsubA : a.primeFactors ⊆ (a * b).primeFactors := by rw [hpf]; exact Finset.subset_union_left
  have hsubB : b.primeFactors ⊆ (a * b).primeFactors := by rw [hpf]; exact Finset.subset_union_right
  rw [gOf_eq_prod_of_subset z a _ hsubA, gOf_eq_prod_of_subset z b _ hsubB, ← Finset.prod_mul_distrib]
  unfold gOf
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply, pow_add]

private lemma continuous_gOf (j : ℕ) : Continuous (fun z => gOf z j) := by
  unfold gOf
  fun_prop

private lemma harmonicSum_pos {X : ℕ} (hX : 1 ≤ X) :
    0 < ∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)) := by
  have h1 : (1 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)) := by
    have hmem : (1 : ℕ) ∈ Finset.Icc 1 X := Finset.mem_Icc.mpr ⟨le_rfl, hX⟩
    have hle := Finset.single_le_sum (f := fun n : ℕ => (1 / (n : ℝ)))
      (fun n _ => by positivity) hmem
    simpa using hle
  linarith

private lemma harmonicSum_two_pow_ge (k : ℕ) :
    (k : ℝ) / 2 ≤ ∑ n ∈ Finset.Icc (1 : ℕ) (2 ^ k), (1 / (n : ℝ)) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have h2pos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hsplit : Finset.Icc (1 : ℕ) (2 ^ (k + 1)) =
        Finset.Icc (1 : ℕ) (2 ^ k) ∪ Finset.Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1)) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_union]
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      omega
    have hdisj : Disjoint (Finset.Icc (1 : ℕ) (2 ^ k)) (Finset.Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1))) := by
      rw [Finset.disjoint_left]
      intro n h1 h2
      simp only [Finset.mem_Icc] at h1 h2
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have hblock : (1 / 2 : ℝ) ≤ ∑ n ∈ Finset.Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1)), (1 / (n : ℝ)) := by
      have hcard : (Finset.Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1))).card = 2 ^ k := by
        rw [Nat.card_Icc]
        have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        omega
      have hlb : ∑ _n ∈ Finset.Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1)), (1 / ((2 ^ (k + 1) : ℕ) : ℝ)) ≤
          ∑ n ∈ Finset.Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1)), (1 / (n : ℝ)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn1 : 1 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
        have hn2 : n ≤ 2 ^ (k + 1) := (Finset.mem_Icc.mp hn).2
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        exact one_div_le_one_div_of_le hn_pos (by exact_mod_cast hn2)
      rw [Finset.sum_const, hcard, nsmul_eq_mul] at hlb
      have heq : ((2 ^ k : ℕ) : ℝ) * (1 / ((2 ^ (k + 1) : ℕ) : ℝ)) = 1 / 2 := by
        push_cast
        have hne : (2 : ℝ) ^ k ≠ 0 := by positivity
        rw [pow_succ]
        calc (2 : ℝ) ^ k * (1 / ((2 : ℝ) ^ k * 2)) = ((2 : ℝ) ^ k / (2 : ℝ) ^ k) * (1 / 2) := by ring
          _ = 1 * (1 / 2) := by rw [div_self hne]
          _ = 1 / 2 := one_mul _
      linarith
    push_cast
    linarith

private lemma harmonicSum_ge_eventually (R : ℝ) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X → R ≤ ∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)) := by
  let k : ℕ := Nat.ceil (2 * max R 0)
  refine ⟨2 ^ k, Nat.one_le_two_pow, fun X hX => ?_⟩
  have hsub : Finset.Icc (1 : ℕ) (2 ^ k) ⊆ Finset.Icc 1 X := Finset.Icc_subset_Icc_right hX
  have hmono : ∑ n ∈ Finset.Icc (1 : ℕ) (2 ^ k), (1 / (n : ℝ)) ≤ ∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  have hk : 2 * max R 0 ≤ (k : ℝ) := Nat.le_ceil _
  have hR : R ≤ (k : ℝ) / 2 := by linarith [le_max_left R 0]
  exact hR.trans ((harmonicSum_two_pow_ge k).trans hmono)

private lemma sum_telescope_le_one (X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) ≤ 1 := by
  cases X with
  | zero =>
    simp
  | succ X =>
    have heq : ∀ m : ℕ, ∑ n ∈ Finset.Icc 1 (m + 1), (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) =
        1 - 1 / ((m + 1 : ℕ) + 1 : ℝ) := by
      intro m
      induction m with
      | zero => simp
      | succ k ihk =>
        have hsp : Finset.Icc 1 (k + 2) = insert (k + 2) (Finset.Icc 1 (k + 1)) := by
          ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnm : k + 2 ∉ Finset.Icc 1 (k + 1) := by simp only [Finset.mem_Icc]; omega
        rw [hsp, Finset.sum_insert hnm, ihk]
        push_cast
        ring
    rw [heq X]
    have hnn : (0 : ℝ) ≤ 1 / ((X + 1 : ℕ) + 1 : ℝ) := by positivity
    linarith

private lemma log_shift_error_le (F : ℕ → ℂ) (hF : ∀ m : ℕ, ‖F m‖ ≤ 1)
    {h₁ X : ℕ} (hh₁ : 1 ≤ h₁) (hX : 1 ≤ X) :
    ‖(∑ n ∈ Finset.Icc 1 X, ((1 / (n : ℝ)) : ℂ) * F (n + h₁)) -
      (∑ m ∈ Finset.Icc 1 X, ((1 / (m : ℝ)) : ℂ) * F m)‖ ≤ 3 * (h₁ : ℝ) := by
  let S₁ : ℂ := ∑ n ∈ Finset.Icc 1 X, ((1 / (n : ℝ)) : ℂ) * F (n + h₁)
  let S₂ : ℂ := ∑ n ∈ Finset.Icc 1 X, ((1 / ((n + h₁ : ℕ) : ℝ)) : ℂ) * F (n + h₁)
  let S₃ : ℂ := ∑ m ∈ Finset.Icc 1 X, ((1 / (m : ℝ)) : ℂ) * F m
  have h12 : ‖S₁ - S₂‖ ≤ (h₁ : ℝ) := by
    have hdiff : S₁ - S₂ =
        ∑ n ∈ Finset.Icc 1 X, (((1 / (n : ℝ) - 1 / ((n + h₁ : ℕ) : ℝ)) : ℝ) : ℂ) * F (n + h₁) := by
      dsimp only [S₁, S₂]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      push_cast
      ring
    rw [hdiff]
    calc ‖∑ n ∈ Finset.Icc 1 X, (((1 / (n : ℝ) - 1 / ((n + h₁ : ℕ) : ℝ)) : ℝ) : ℂ) * F (n + h₁)‖
        ≤ ∑ n ∈ Finset.Icc 1 X, ‖(((1 / (n : ℝ) - 1 / ((n + h₁ : ℕ) : ℝ)) : ℝ) : ℂ) * F (n + h₁)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 X, (h₁ : ℝ) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
          have hnh_pos : (0 : ℝ) < (n : ℝ) + (h₁ : ℝ) := by positivity
          have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
          have hsub_nn : 0 ≤ 1 / (n : ℝ) - 1 / ((n + h₁ : ℕ) : ℝ) := by
            push_cast
            have hle : (n : ℝ) ≤ (n : ℝ) + (h₁ : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) h₁]
            linarith [one_div_le_one_div_of_le hn_pos hle]
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hsub_nn]
          have hmul1 : (1 / (n : ℝ) - 1 / ((n + h₁ : ℕ) : ℝ)) * ‖F (n + h₁)‖ ≤
              (1 / (n : ℝ) - 1 / ((n + h₁ : ℕ) : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left (hF _) hsub_nn
          rw [mul_one] at hmul1
          have hident : 1 / (n : ℝ) - 1 / ((n + h₁ : ℕ) : ℝ) =
              (h₁ : ℝ) / ((n : ℝ) * ((n : ℝ) + (h₁ : ℝ))) := by
            push_cast
            field_simp [ne_of_gt hn_pos, ne_of_gt hnh_pos]
            ring
          have hident2 : (h₁ : ℝ) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) =
              (h₁ : ℝ) / ((n : ℝ) * ((n : ℝ) + 1)) := by
            field_simp [ne_of_gt hn_pos, ne_of_gt hn1_pos]
            ring
          have hden_le : (n : ℝ) * ((n : ℝ) + 1) ≤ (n : ℝ) * ((n : ℝ) + (h₁ : ℝ)) := by
            have hh1 : (1 : ℝ) ≤ (h₁ : ℝ) := by exact_mod_cast hh₁
            nlinarith
          have hfrac : (h₁ : ℝ) / ((n : ℝ) * ((n : ℝ) + (h₁ : ℝ))) ≤
              (h₁ : ℝ) / ((n : ℝ) * ((n : ℝ) + 1)) :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg h₁) (mul_pos hn_pos hn1_pos) hden_le
          linarith
      _ = (h₁ : ℝ) * ∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
          rw [← Finset.mul_sum]
      _ ≤ (h₁ : ℝ) * 1 := mul_le_mul_of_nonneg_left (sum_telescope_le_one X) (Nat.cast_nonneg h₁)
      _ = (h₁ : ℝ) := mul_one _
  have h23 : ‖S₂ - S₃‖ ≤ 2 * (h₁ : ℝ) := by
    let term : ℕ → ℂ := fun m => ((1 / (m : ℝ)) : ℂ) * F m
    have hS₂_eq : S₂ = ∑ m ∈ Finset.Icc (h₁ + 1) (X + h₁), term m := by
      dsimp only [S₂, term]
      refine Finset.sum_nbij (fun n => n + h₁) ?_ ?_ ?_ ?_
      · intro n hn
        simp only [Finset.mem_Icc] at hn ⊢
        omega
      · intro a _ b _ hab
        dsimp only at hab
        omega
      · intro m hm
        simp only [Finset.mem_coe, Finset.mem_Icc] at hm
        refine ⟨m - h₁, Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩),
          by dsimp only; omega⟩
      · intro _ _; rfl
    have hsplitA : ∑ m ∈ Finset.Icc 1 (X + h₁), term m =
        S₃ + ∑ m ∈ Finset.Icc (X + 1) (X + h₁), term m := by
      have hunion : Finset.Icc 1 (X + h₁) = Finset.Icc 1 X ∪ Finset.Icc (X + 1) (X + h₁) := by
        ext m; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Icc 1 X) (Finset.Icc (X + 1) (X + h₁)) := by
        rw [Finset.disjoint_left]; intro m h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
      rw [hunion, Finset.sum_union hdisj]
    have hsplitB : ∑ m ∈ Finset.Icc 1 (X + h₁), term m =
        (∑ m ∈ Finset.Icc 1 h₁, term m) + S₂ := by
      have hunion : Finset.Icc 1 (X + h₁) = Finset.Icc 1 h₁ ∪ Finset.Icc (h₁ + 1) (X + h₁) := by
        ext m; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Icc 1 h₁) (Finset.Icc (h₁ + 1) (X + h₁)) := by
        rw [Finset.disjoint_left]; intro m h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
      rw [hunion, Finset.sum_union hdisj, hS₂_eq]
    have hdiff : S₂ - S₃ =
        (∑ m ∈ Finset.Icc (X + 1) (X + h₁), term m) - (∑ m ∈ Finset.Icc 1 h₁, term m) := by
      linear_combination hsplitA - hsplitB
    have hterm_le : ∀ m : ℕ, 1 ≤ m → ‖term m‖ ≤ 1 := by
      intro m hm
      dsimp only [term]
      rw [norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg m)]
      have h1m : 1 / (m : ℝ) ≤ 1 := by
        have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        exact div_le_one_of_le₀ hm1 (by positivity)
      calc (1 / (m : ℝ)) * ‖F m‖ ≤ 1 * 1 := mul_le_mul h1m (hF m) (norm_nonneg _) zero_le_one
        _ = 1 := mul_one 1
    have hnormA : ‖∑ m ∈ Finset.Icc (X + 1) (X + h₁), term m‖ ≤ (h₁ : ℝ) := by
      calc ‖∑ m ∈ Finset.Icc (X + 1) (X + h₁), term m‖
          ≤ ∑ m ∈ Finset.Icc (X + 1) (X + h₁), ‖term m‖ := norm_sum_le _ _
        _ ≤ ∑ _m ∈ Finset.Icc (X + 1) (X + h₁), (1 : ℝ) :=
            Finset.sum_le_sum fun m hm => hterm_le m (by have := (Finset.mem_Icc.mp hm).1; omega)
        _ = (h₁ : ℝ) := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
            have hnat : X + h₁ + 1 - (X + 1) = h₁ := by omega
            rw [hnat]
    have hnormB : ‖∑ m ∈ Finset.Icc 1 h₁, term m‖ ≤ (h₁ : ℝ) := by
      calc ‖∑ m ∈ Finset.Icc 1 h₁, term m‖
          ≤ ∑ m ∈ Finset.Icc 1 h₁, ‖term m‖ := norm_sum_le _ _
        _ ≤ ∑ _m ∈ Finset.Icc 1 h₁, (1 : ℝ) :=
            Finset.sum_le_sum fun m hm => hterm_le m (Finset.mem_Icc.mp hm).1
        _ = (h₁ : ℝ) := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
            have hnat : h₁ + 1 - 1 = h₁ := by omega
            rw [hnat]
    rw [hdiff]
    calc ‖(∑ m ∈ Finset.Icc (X + 1) (X + h₁), term m) - (∑ m ∈ Finset.Icc 1 h₁, term m)‖
        ≤ ‖∑ m ∈ Finset.Icc (X + 1) (X + h₁), term m‖ + ‖∑ m ∈ Finset.Icc 1 h₁, term m‖ :=
          norm_sub_le _ _
      _ ≤ (h₁ : ℝ) + (h₁ : ℝ) := add_le_add hnormA hnormB
      _ = 2 * (h₁ : ℝ) := by ring
  calc ‖S₁ - S₃‖ = ‖(S₁ - S₂) + (S₂ - S₃)‖ := by congr 1; ring
    _ ≤ ‖S₁ - S₂‖ + ‖S₂ - S₃‖ := norm_add_le _ _
    _ ≤ (h₁ : ℝ) + 2 * (h₁ : ℝ) := add_le_add h12 h23
    _ = 3 * (h₁ : ℝ) := by ring

private lemma norm_sq_sum_unit (f : ℕ → ℂ) (H : ℕ)
    (hf : ∀ h ∈ Finset.Icc 1 H, ‖f h‖ = 1) :
    ‖∑ h ∈ Finset.Icc 1 H, f h‖ ^ 2 =
      (H : ℝ) + 2 * ∑ d ∈ Finset.Icc 1 (H - 1),
        ∑ h₁ ∈ Finset.Icc 1 (H - d), (f h₁ * star (f (h₁ + d))).re := by
  let I := Finset.Icc 1 H
  have hsq : ‖∑ h ∈ I, f h‖ ^ 2 = ∑ h₁ ∈ I, ∑ h₂ ∈ I, (f h₁ * star (f h₂)).re := by
    have h1 : ‖∑ h ∈ I, f h‖ ^ 2 = ((∑ h ∈ I, f h) * star (∑ h ∈ I, f h)).re := by
      rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [h1, Complex.star_def, map_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum, ← Complex.star_def]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun h₁ _ => ?_
    rw [Complex.re_sum]
  rw [hsq]
  have hsplit : ∑ h₁ ∈ I, ∑ h₂ ∈ I, (f h₁ * star (f h₂)).re =
      ∑ p ∈ I ×ˢ I, (f p.1 * star (f p.2)).re :=
    (Finset.sum_product I I (fun p => (f p.1 * star (f p.2)).re)).symm
  rw [hsplit]
  let Diag := (I ×ˢ I).filter fun p => p.1 = p.2
  let Lt := (I ×ˢ I).filter fun p => p.1 < p.2
  let Gt := (I ×ˢ I).filter fun p => p.2 < p.1
  have hpart : I ×ˢ I = Diag ∪ (Lt ∪ Gt) := by
    ext ⟨a, b⟩
    simp only [Diag, Lt, Gt, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h
      rcases lt_trichotomy a b with hlt | heq | hgt
      · exact Or.inr (Or.inl ⟨h, hlt⟩)
      · exact Or.inl ⟨h, heq⟩
      · exact Or.inr (Or.inr ⟨h, hgt⟩)
    · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hd1 : Disjoint Diag (Lt ∪ Gt) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Diag, Lt, Gt, Finset.mem_union, Finset.mem_filter] at hp1 hp2
    omega
  have hd2 : Disjoint Lt Gt := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Lt, Gt, Finset.mem_filter] at hp1 hp2
    omega
  rw [hpart, Finset.sum_union hd1, Finset.sum_union hd2]
  have hDiag : ∑ p ∈ Diag, (f p.1 * star (f p.2)).re = (H : ℝ) := by
    have hbij : ∑ p ∈ Diag, (f p.1 * star (f p.2)).re = ∑ h ∈ I, (1 : ℝ) := by
      refine Finset.sum_nbij (fun p => p.1) ?_ ?_ ?_ ?_
      · intro p hp
        exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
      · intro p₁ hp₁ p₂ hp₂ heq
        have h1 := (Finset.mem_filter.mp hp₁).2
        have h2 := (Finset.mem_filter.mp hp₂).2
        ext <;> simp_all
      · intro h hh
        exact ⟨(h, h), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hh, hh⟩, rfl⟩, rfl⟩
      · intro p hp
        have hmem := Finset.mem_filter.mp hp
        have hp1 : p.1 ∈ I := (Finset.mem_product.mp hmem.1).1
        rw [← hmem.2, Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
          Complex.normSq_eq_norm_sq, hf p.1 hp1, one_pow]
    rw [hbij, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    have hnat : H + 1 - 1 = H := by omega
    rw [hnat]
  have hGt_eq_Lt : ∑ p ∈ Gt, (f p.1 * star (f p.2)).re = ∑ p ∈ Lt, (f p.1 * star (f p.2)).re := by
    refine Finset.sum_nbij (fun p => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      have hmem := Finset.mem_filter.mp hp
      have hprod := Finset.mem_product.mp hmem.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hprod.2, hprod.1⟩, hmem.2⟩
    · intro p₁ _ p₂ _ heq
      cases p₁; cases p₂; simp_all
    · intro p hp
      have hmem := Finset.mem_filter.mp hp
      have hprod := Finset.mem_product.mp hmem.1
      exact ⟨(p.2, p.1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hprod.2, hprod.1⟩, hmem.2⟩, rfl⟩
    · intro p _
      have hconj : star (f p.2 * star (f p.1)) = f p.1 * star (f p.2) := by
        simp [mul_comm]
      rw [← hconj, Complex.star_def, Complex.conj_re]
  have hLt_eq : ∑ p ∈ Lt, (f p.1 * star (f p.2)).re =
      ∑ d ∈ Finset.Icc 1 (H - 1), ∑ h₁ ∈ Finset.Icc 1 (H - d), (f h₁ * star (f (h₁ + d))).re := by
    rw [Finset.sum_sigma']
    refine Finset.sum_nbij (fun p => (⟨p.2 - p.1, p.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
    · intro p hp
      have hmem := Finset.mem_filter.mp hp
      have h1 := Finset.mem_Icc.mp (Finset.mem_product.mp hmem.1).1
      have h2 := Finset.mem_Icc.mp (Finset.mem_product.mp hmem.1).2
      have hlt := hmem.2
      refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
      · exact Finset.mem_Icc.mpr ⟨by dsimp only; omega, by dsimp only; omega⟩
      · exact Finset.mem_Icc.mpr ⟨by dsimp only; omega, by dsimp only; omega⟩
    · intro p₁ hp₁ p₂ hp₂ heq
      have hlt₁ := (Finset.mem_filter.mp (Finset.mem_coe.mp hp₁)).2
      have hlt₂ := (Finset.mem_filter.mp (Finset.mem_coe.mp hp₂)).2
      have hf1 : p₁.2 - p₁.1 = p₂.2 - p₂.1 := congrArg Sigma.fst heq
      have hf2 : p₁.1 = p₂.1 := by simpa using congrArg Sigma.snd heq
      ext
      · exact hf2
      · omega
    · rintro ⟨d, h₁⟩ hmem
      obtain ⟨hd, hh₁⟩ := Finset.mem_sigma.mp (Finset.mem_coe.mp hmem)
      dsimp only at hd hh₁
      have hd' := Finset.mem_Icc.mp hd
      have hh₁' := Finset.mem_Icc.mp hh₁
      refine ⟨(h₁, h₁ + d), ?_, ?_⟩
      · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
            Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, by omega⟩)
      · simp
    · intro p hp
      have hlt := (Finset.mem_filter.mp hp).2
      have hadd : p.1 + (p.2 - p.1) = p.2 := by omega
      simp [hadd]
  rw [hDiag, hGt_eq_Lt, hLt_eq]
  ring

private lemma integrable_of_continuous_on_omega
    (μ : ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (ℕ → Metric.sphere (0 : ℂ) 1) → E) (hf : Continuous f) :
    Integrable f (μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

private lemma short_sum_energy_le
    (μ : ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1)) (B : ℝ)
    (hB : ∀ n : ℕ, ∫ z, ‖∑ j ∈ Finset.Icc 1 n, gOf z j‖ ^ 2 ∂(μ : Measure _) ≤ B)
    (n H : ℕ) :
    ∫ z, ‖∑ h ∈ Finset.Icc 1 H, gOf z (n + h)‖ ^ 2 ∂(μ : Measure _) ≤ 4 * B := by
  let S : ℕ → (ℕ → Metric.sphere (0 : ℂ) 1) → ℂ := fun m z => ∑ j ∈ Finset.Icc 1 m, gOf z j
  have hshift_eq : ∀ z, ∑ h ∈ Finset.Icc 1 H, gOf z (n + h) = S (n + H) z - S n z := by
    intro z
    have hsplit : Finset.Icc 1 (n + H) = Finset.Icc 1 n ∪ Finset.Icc (n + 1) (n + H) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc 1 n) (Finset.Icc (n + 1) (n + H)) := by
      rw [Finset.disjoint_left]; intro j h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
    have hbij : ∑ h ∈ Finset.Icc 1 H, gOf z (n + h) = ∑ j ∈ Finset.Icc (n + 1) (n + H), gOf z j := by
      refine Finset.sum_nbij (fun h => n + h) ?_ ?_ ?_ ?_
      · intro h hh; simp only [Finset.mem_Icc] at hh ⊢; omega
      · intro a _ b _ hab; dsimp only at hab; omega
      · intro j hj; simp only [Finset.mem_coe, Finset.mem_Icc] at hj
        exact ⟨j - n, Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩),
          by dsimp only; omega⟩
      · intro _ _; rfl
    dsimp only [S]
    rw [hsplit, Finset.sum_union hdisj, ← hbij]
    ring
  have hpt : ∀ z, ‖∑ h ∈ Finset.Icc 1 H, gOf z (n + h)‖ ^ 2 ≤
      2 * ‖S (n + H) z‖ ^ 2 + 2 * ‖S n z‖ ^ 2 := by
    intro z
    rw [hshift_eq z]
    have htri : ‖S (n + H) z - S n z‖ ≤ ‖S (n + H) z‖ + ‖S n z‖ := norm_sub_le _ _
    have hsq : ‖S (n + H) z - S n z‖ ^ 2 ≤ (‖S (n + H) z‖ + ‖S n z‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    have h2 : (‖S (n + H) z‖ + ‖S n z‖) ^ 2 ≤ 2 * ‖S (n + H) z‖ ^ 2 + 2 * ‖S n z‖ ^ 2 := by
      nlinarith [sq_nonneg (‖S (n + H) z‖ - ‖S n z‖)]
    exact hsq.trans h2
  have hint_lhs : Integrable (fun z => ‖∑ h ∈ Finset.Icc 1 H, gOf z (n + h)‖ ^ 2) (μ : Measure _) :=
    integrable_of_continuous_on_omega μ _ (by
      refine Continuous.pow (Continuous.norm (continuous_finsetSum _ fun h _ => continuous_gOf _)) 2)
  have hint_S : ∀ m, Integrable (fun z => ‖S m z‖ ^ 2) (μ : Measure _) := fun m =>
    integrable_of_continuous_on_omega μ _ (by
      refine Continuous.pow (Continuous.norm (continuous_finsetSum _ fun j _ => continuous_gOf _)) 2)
  have hint_rhs : Integrable (fun z => 2 * ‖S (n + H) z‖ ^ 2 + 2 * ‖S n z‖ ^ 2) (μ : Measure _) :=
    ((hint_S (n + H)).const_mul 2).add ((hint_S n).const_mul 2)
  calc ∫ z, ‖∑ h ∈ Finset.Icc 1 H, gOf z (n + h)‖ ^ 2 ∂(μ : Measure _)
      ≤ ∫ z, (2 * ‖S (n + H) z‖ ^ 2 + 2 * ‖S n z‖ ^ 2) ∂(μ : Measure _) :=
        integral_mono hint_lhs hint_rhs hpt
    _ = 2 * (∫ z, ‖S (n + H) z‖ ^ 2 ∂(μ : Measure _)) +
        2 * (∫ z, ‖S n z‖ ^ 2 ∂(μ : Measure _)) := by
        rw [integral_add ((hint_S (n + H)).const_mul 2) ((hint_S n).const_mul 2),
          integral_const_mul, integral_const_mul]
    _ ≤ 2 * B + 2 * B := add_le_add (mul_le_mul_of_nonneg_left (hB (n + H)) zero_le_two)
        (mul_le_mul_of_nonneg_left (hB n) zero_le_two)
    _ = 4 * B := by ring

private lemma exists_large_corr_shift
    (μ : ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1)) (B : ℝ)
    (hB : ∀ n : ℕ, ∫ z, ‖∑ j ∈ Finset.Icc 1 n, gOf z j‖ ^ 2 ∂(μ : Measure _) ≤ B) :
    ∃ H : ℕ, 2 ≤ H ∧ ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X →
      ∃ d ∈ Finset.Icc 1 (H - 1),
        1 / (8 * (H : ℝ)) ≤
          ∫ z, ‖((1 / (∑ m ∈ Finset.Icc 1 X, (1 / (m : ℝ)))) : ℂ) *
            ∑ m ∈ Finset.Icc 1 X, ((1 / (m : ℝ)) : ℂ) * (gOf z m * star (gOf z (m + d)))‖
            ∂(μ : Measure _) := by
  have hB_nn : 0 ≤ B := by
    have h0 := hB 0
    simp only [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1), Finset.sum_empty, norm_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero] at h0
    exact h0
  let H : ℕ := Nat.ceil (8 * B) + 4
  have hH2 : 2 ≤ H := by dsimp only [H]; omega
  have hH_pos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  have hH_ge_8B : 8 * B ≤ (H : ℝ) := by
    have h1 : 8 * B ≤ (Nat.ceil (8 * B) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (8 * B) : ℝ) ≤ (H : ℝ) := by dsimp only [H]; push_cast; linarith
    exact h1.trans h2
  obtain ⟨X₀, hX₀1, hLX₀⟩ := harmonicSum_ge_eventually (24 * (H : ℝ) ^ 2)
  refine ⟨H, hH2, X₀, hX₀1, fun X hX => ?_⟩
  have hX1 : 1 ≤ X := le_trans hX₀1 hX
  let L : ℝ := ∑ m ∈ Finset.Icc 1 X, (1 / (m : ℝ))
  have hL_ge : 24 * (H : ℝ) ^ 2 ≤ L := hLX₀ X hX
  have hL_pos : 0 < L := harmonicSum_pos hX1
  let avg : ℕ → (ℕ → Metric.sphere (0 : ℂ) 1) → ℂ := fun d z =>
    ((1 / (∑ m ∈ Finset.Icc 1 X, (1 / (m : ℝ)))) : ℂ) *
      ∑ m ∈ Finset.Icc 1 X, ((1 / (m : ℝ)) : ℂ) * (gOf z m * star (gOf z (m + d)))
  have hsum_norm : (H : ℝ) / 4 ≤ 2 * (H : ℝ) * ∑ d ∈ Finset.Icc 1 (H - 1), ∫ z, ‖avg d z‖ ∂(μ : Measure _) := by
    have hstep1 : ∀ n ∈ Finset.Icc 1 X,
        (H : ℝ) + 2 * ∑ d ∈ Finset.Icc 1 (H - 1), ∑ h₁ ∈ Finset.Icc 1 (H - d),
          ∫ z, (gOf z (n + h₁) * star (gOf z (n + (h₁ + d)))).re ∂(μ : Measure _) ≤ 4 * B := by
      intro n _
      have hpt : ∀ z, ‖∑ h ∈ Finset.Icc 1 H, gOf z (n + h)‖ ^ 2 =
          (H : ℝ) + 2 * ∑ d ∈ Finset.Icc 1 (H - 1), ∑ h₁ ∈ Finset.Icc 1 (H - d),
            (gOf z (n + h₁) * star (gOf z (n + (h₁ + d)))).re := fun z =>
        norm_sq_sum_unit (fun h => gOf z (n + h)) H (fun h _ => norm_gOf z (n + h))
      have hint_term : ∀ d h₁, Integrable
          (fun z => (gOf z (n + h₁) * star (gOf z (n + (h₁ + d)))).re) (μ : Measure _) := fun d h₁ =>
        integrable_of_continuous_on_omega μ _ (by
          refine Complex.continuous_re.comp ((continuous_gOf _).mul (continuous_star.comp (continuous_gOf _))))
      have hint_in : ∀ d, Integrable (fun z => ∑ h₁ ∈ Finset.Icc 1 (H - d),
          (gOf z (n + h₁) * star (gOf z (n + (h₁ + d)))).re) (μ : Measure _) := fun d =>
        integrable_finsetSum _ fun h₁ _ => hint_term d h₁
      have hint_out : Integrable (fun z => ∑ d ∈ Finset.Icc 1 (H - 1), ∑ h₁ ∈ Finset.Icc 1 (H - d),
          (gOf z (n + h₁) * star (gOf z (n + (h₁ + d)))).re) (μ : Measure _) :=
        integrable_finsetSum _ fun d _ => hint_in d
      have heq_int : ∫ z, ‖∑ h ∈ Finset.Icc 1 H, gOf z (n + h)‖ ^ 2 ∂(μ : Measure _) =
          (H : ℝ) + 2 * ∑ d ∈ Finset.Icc 1 (H - 1), ∑ h₁ ∈ Finset.Icc 1 (H - d),
            ∫ z, (gOf z (n + h₁) * star (gOf z (n + (h₁ + d)))).re ∂(μ : Measure _) := by
        simp_rw [hpt]
        rw [integral_add (integrable_const _) (hint_out.const_mul 2), integral_const,
          probReal_univ, one_smul, integral_const_mul, integral_finsetSum _ (fun d _ => hint_in d)]
        congr 2
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [integral_finsetSum _ (fun h₁ _ => hint_term d h₁)]
      rw [← heq_int]
      exact short_sum_energy_le μ B hB n H
    have hlog_avg : (H : ℝ) * L + 2 * ∑ d ∈ Finset.Icc 1 (H - 1), ∑ h₁ ∈ Finset.Icc 1 (H - d),
        ∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)) *
          ∫ z, (gOf z (n + h₁) * star (gOf z (n + (h₁ + d)))).re ∂(μ : Measure _) ≤ 4 * B * L := by
      have hsum_le : ∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)) *
          ((H : ℝ) + 2 * ∑ d ∈ Finset.Icc 1 (H - 1), ∑ h₁ ∈ Finset.Icc 1 (H - d),
            ∫ z, (gOf z (n + h₁) * star (gOf z (n + (h₁ + d)))).re ∂(μ : Measure _)) ≤
          ∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)) * (4 * B) :=
        Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hstep1 n hn) (by positivity)
      have hrhs : ∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)) * (4 * B) = 4 * B * L := by
        rw [← Finset.sum_mul, mul_comm]
      have hlhs : ∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)) *
          ((H : ℝ) + 2 * ∑ d ∈ Finset.Icc 1 (H - 1), ∑ h₁ ∈ Finset.Icc 1 (H - d),
            ∫ z, (gOf z (n + h₁) * star (gOf z (n + (h₁ + d)))).re ∂(μ : Measure _)) =
          (H : ℝ) * L + 2 * ∑ d ∈ Finset.Icc 1 (H - 1), ∑ h₁ ∈ Finset.Icc 1 (H - d),
            ∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)) *
              ∫ z, (gOf z (n + h₁) * star (gOf z (n + (h₁ + d)))).re ∂(μ : Measure _) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        congr 1
        · rw [← Finset.sum_mul, mul_comm]
        · simp_rw [← mul_assoc, mul_comm (1 / (_ : ℝ)) 2, mul_assoc, ← Finset.mul_sum]
          congr 1
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.sum_comm]
      linarith
    have hshift_bound : ∀ d ∈ Finset.Icc 1 (H - 1), ∀ h₁ ∈ Finset.Icc 1 (H - d),
        -(∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)) *
            ∫ z, (gOf z (n + h₁) * star (gOf z (n + (h₁ + d)))).re ∂(μ : Measure _)) ≤
          L * (∫ z, ‖avg d z‖ ∂(μ : Measure _)) + 3 * (H : ℝ) := by
      intro d hd h₁ hh₁
      have hh₁_ge1 : 1 ≤ h₁ := (Finset.mem_Icc.mp hh₁).1
      have hh₁_leH : h₁ ≤ H := by
        have := (Finset.mem_Icc.mp hh₁).2
        omega
      let F : ℕ → ℂ := fun m => ∫ z, gOf z m * star (gOf z (m + d)) ∂(μ : Measure _)
      have hF_le : ∀ m, ‖F m‖ ≤ 1 := by
        intro m
        calc ‖∫ z, gOf z m * star (gOf z (m + d)) ∂(μ : Measure _)‖
            ≤ ∫ z, ‖gOf z m * star (gOf z (m + d))‖ ∂(μ : Measure _) := norm_integral_le_integral_norm _
          _ = ∫ _z, (1 : ℝ) ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
              dsimp only
              rw [norm_mul, norm_star, norm_gOf, norm_gOf, mul_one]
          _ = 1 := by
              rw [integral_const, probReal_univ, one_smul]
      have hint_prod : ∀ m, Integrable (fun z => gOf z m * star (gOf z (m + d))) (μ : Measure _) := fun m =>
        integrable_of_continuous_on_omega μ _
          ((continuous_gOf m).mul (continuous_star.comp (continuous_gOf (m + d))))
      have hre_eq : ∀ n : ℕ, (1 / (n : ℝ)) *
          ∫ z, (gOf z (n + h₁) * star (gOf z (n + (h₁ + d)))).re ∂(μ : Measure _) =
          (((1 / (n : ℝ)) : ℂ) * F (n + h₁)).re := by
        intro n
        have hadd : n + (h₁ + d) = (n + h₁) + d := by omega
        rw [hadd]
        have hre_int : ∫ z, (gOf z (n + h₁) * star (gOf z (n + h₁ + d))).re ∂(μ : Measure _) =
            (F (n + h₁)).re := by
          dsimp only [F]
          exact (Complex.reCLM.integral_comp_comm (hint_prod (n + h₁)))
        rw [hre_int, ← Complex.ofReal_one, ← Complex.ofReal_div,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      have hsum_re : ∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)) *
          ∫ z, (gOf z (n + h₁) * star (gOf z (n + (h₁ + d)))).re ∂(μ : Measure _) =
          (∑ n ∈ Finset.Icc 1 X, ((1 / (n : ℝ)) : ℂ) * F (n + h₁)).re := by
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl fun n _ => hre_eq n
      have hneg_le : -(∑ n ∈ Finset.Icc 1 X, ((1 / (n : ℝ)) : ℂ) * F (n + h₁)).re ≤
          ‖∑ n ∈ Finset.Icc 1 X, ((1 / (n : ℝ)) : ℂ) * F (n + h₁)‖ :=
        (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      have herr := log_shift_error_le F hF_le hh₁_ge1 hX1
      have htri : ‖∑ n ∈ Finset.Icc 1 X, ((1 / (n : ℝ)) : ℂ) * F (n + h₁)‖ ≤
          ‖∑ m ∈ Finset.Icc 1 X, ((1 / (m : ℝ)) : ℂ) * F m‖ + 3 * (h₁ : ℝ) := by
        have h := norm_add_le
          ((∑ n ∈ Finset.Icc 1 X, ((1 / (n : ℝ)) : ℂ) * F (n + h₁)) -
            (∑ m ∈ Finset.Icc 1 X, ((1 / (m : ℝ)) : ℂ) * F m))
          (∑ m ∈ Finset.Icc 1 X, ((1 / (m : ℝ)) : ℂ) * F m)
        have hsub : ((∑ n ∈ Finset.Icc 1 X, ((1 / (n : ℝ)) : ℂ) * F (n + h₁)) -
            (∑ m ∈ Finset.Icc 1 X, ((1 / (m : ℝ)) : ℂ) * F m)) +
            (∑ m ∈ Finset.Icc 1 X, ((1 / (m : ℝ)) : ℂ) * F m) =
            ∑ n ∈ Finset.Icc 1 X, ((1 / (n : ℝ)) : ℂ) * F (n + h₁) := sub_add_cancel _ _
        rw [hsub] at h
        linarith
      have hmain_int : ‖∑ m ∈ Finset.Icc 1 X, ((1 / (m : ℝ)) : ℂ) * F m‖ ≤
          L * ∫ z, ‖avg d z‖ ∂(μ : Measure _) := by
        have hswap : ∑ m ∈ Finset.Icc 1 X, ((1 / (m : ℝ)) : ℂ) * F m =
            ∫ z, ∑ m ∈ Finset.Icc 1 X, ((1 / (m : ℝ)) : ℂ) * (gOf z m * star (gOf z (m + d)))
              ∂(μ : Measure _) := by
          rw [integral_finsetSum _ (fun m _ => (hint_prod m).const_mul _)]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [integral_const_mul]
        have havg_scale : ∀ z, ‖∑ m ∈ Finset.Icc 1 X, ((1 / (m : ℝ)) : ℂ) * (gOf z m * star (gOf z (m + d)))‖ =
            L * ‖avg d z‖ := by
          intro z
          dsimp only [avg]
          rw [norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hL_pos)]
          field_simp [ne_of_gt hL_pos]
        rw [hswap]
        calc ‖∫ z, ∑ m ∈ Finset.Icc 1 X, ((1 / (m : ℝ)) : ℂ) * (gOf z m * star (gOf z (m + d)))
                ∂(μ : Measure _)‖
            ≤ ∫ z, ‖∑ m ∈ Finset.Icc 1 X, ((1 / (m : ℝ)) : ℂ) * (gOf z m * star (gOf z (m + d)))‖
                ∂(μ : Measure _) := norm_integral_le_integral_norm _
          _ = ∫ z, L * ‖avg d z‖ ∂(μ : Measure _) := by simp_rw [havg_scale]
          _ = L * ∫ z, ‖avg d z‖ ∂(μ : Measure _) := integral_const_mul _ _
      have hh₁_real : (h₁ : ℝ) ≤ (H : ℝ) := by exact_mod_cast hh₁_leH
      rw [hsum_re]
      linarith
    have hdouble : (H : ℝ) * L - 4 * B * L ≤
        2 * ∑ d ∈ Finset.Icc 1 (H - 1), ∑ _h₁ ∈ Finset.Icc 1 (H - d),
          (L * (∫ z, ‖avg d z‖ ∂(μ : Measure _)) + 3 * (H : ℝ)) := by
      have hsum_neg : -(∑ d ∈ Finset.Icc 1 (H - 1), ∑ h₁ ∈ Finset.Icc 1 (H - d),
          ∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)) *
            ∫ z, (gOf z (n + h₁) * star (gOf z (n + (h₁ + d)))).re ∂(μ : Measure _)) ≤
          ∑ d ∈ Finset.Icc 1 (H - 1), ∑ _h₁ ∈ Finset.Icc 1 (H - d),
            (L * (∫ z, ‖avg d z‖ ∂(μ : Measure _)) + 3 * (H : ℝ)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_le_sum fun d hd => ?_
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_le_sum fun h₁ hh₁ => hshift_bound d hd h₁ hh₁
      linarith
    have hrhs_bound :
        2 * ∑ d ∈ Finset.Icc 1 (H - 1), ∑ _h₁ ∈ Finset.Icc 1 (H - d),
          (L * (∫ z, ‖avg d z‖ ∂(μ : Measure _)) + 3 * (H : ℝ)) ≤
        2 * (H : ℝ) * L * (∑ d ∈ Finset.Icc 1 (H - 1), ∫ z, ‖avg d z‖ ∂(μ : Measure _)) +
          6 * (H : ℝ) ^ 3 := by
      have hinner : ∀ d ∈ Finset.Icc 1 (H - 1),
          ∑ _h₁ ∈ Finset.Icc 1 (H - d), (L * (∫ z, ‖avg d z‖ ∂(μ : Measure _)) + 3 * (H : ℝ)) ≤
          (H : ℝ) * (L * (∫ z, ‖avg d z‖ ∂(μ : Measure _)) + 3 * (H : ℝ)) := by
        intro d _
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        have hcard_le : ((H - d + 1 - 1 : ℕ) : ℝ) ≤ (H : ℝ) := by
          have hnat : H - d + 1 - 1 ≤ H := by omega
          exact_mod_cast hnat
        have hterm_nn : 0 ≤ L * (∫ z, ‖avg d z‖ ∂(μ : Measure _)) + 3 * (H : ℝ) := by
          have hint_nn : 0 ≤ ∫ z, ‖avg d z‖ ∂(μ : Measure _) :=
            integral_nonneg fun z => norm_nonneg _
          positivity
        exact mul_le_mul_of_nonneg_right hcard_le hterm_nn
      have h1 : ∑ d ∈ Finset.Icc 1 (H - 1), ∑ _h₁ ∈ Finset.Icc 1 (H - d),
            (L * (∫ z, ‖avg d z‖ ∂(μ : Measure _)) + 3 * (H : ℝ)) ≤
          ∑ d ∈ Finset.Icc 1 (H - 1),
            (H : ℝ) * (L * (∫ z, ‖avg d z‖ ∂(μ : Measure _)) + 3 * (H : ℝ)) :=
        Finset.sum_le_sum hinner
      have h2 : ∑ d ∈ Finset.Icc 1 (H - 1),
            (H : ℝ) * (L * (∫ z, ‖avg d z‖ ∂(μ : Measure _)) + 3 * (H : ℝ)) =
          (H : ℝ) * L * (∑ d ∈ Finset.Icc 1 (H - 1), ∫ z, ‖avg d z‖ ∂(μ : Measure _)) +
            ((H - 1 : ℕ) : ℝ) * (3 * (H : ℝ) ^ 2) := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.mul_sum, Finset.sum_const,
          Nat.card_Icc, nsmul_eq_mul]
        have hnat : H - 1 + 1 - 1 = H - 1 := by omega
        rw [hnat]
        ring
      have hH1_le : ((H - 1 : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast Nat.sub_le H 1
      have h3 : ((H - 1 : ℕ) : ℝ) * (3 * (H : ℝ) ^ 2) ≤ 3 * (H : ℝ) ^ 3 := by
        have := mul_le_mul_of_nonneg_right hH1_le (show 0 ≤ 3 * (H : ℝ) ^ 2 by positivity)
        linarith
      linarith
    have hL_comb : (H : ℝ) / 4 * L ≤
        2 * (H : ℝ) * L * (∑ d ∈ Finset.Icc 1 (H - 1), ∫ z, ‖avg d z‖ ∂(μ : Measure _)) := by
      have h6H3 : 6 * (H : ℝ) ^ 3 ≤ (H : ℝ) / 4 * L := by
        have := mul_le_mul_of_nonneg_left hL_ge (show 0 ≤ (H : ℝ) / 4 by positivity)
        linarith
      have h4B : 4 * B * L ≤ (H : ℝ) / 2 * L := by
        have := mul_le_mul_of_nonneg_right hH_ge_8B (le_of_lt hL_pos)
        linarith
      linarith
    have hmul : L * ((H : ℝ) / 4) ≤
        L * (2 * (H : ℝ) * ∑ d ∈ Finset.Icc 1 (H - 1), ∫ z, ‖avg d z‖ ∂(μ : Measure _)) := by
      linarith
    exact le_of_mul_le_mul_left hmul hL_pos
  by_contra hall
  push Not at hall
  have hsum_lt : ∑ d ∈ Finset.Icc 1 (H - 1), ∫ z, ‖avg d z‖ ∂(μ : Measure _) <
      ((H - 1 : ℕ) : ℝ) * (1 / (8 * (H : ℝ))) := by
    have hne : (Finset.Icc 1 (H - 1)).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
    have hlt := Finset.sum_lt_sum_of_nonempty hne fun d hd => hall d hd
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hlt
    have hnat : H - 1 + 1 - 1 = H - 1 := by omega
    rwa [hnat] at hlt
  have hH1_le : ((H - 1 : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast Nat.sub_le H 1
  have hbound : 2 * (H : ℝ) * (((H - 1 : ℕ) : ℝ) * (1 / (8 * (H : ℝ)))) ≤ (H : ℝ) / 4 := by
    have h1 : 2 * (H : ℝ) * (((H - 1 : ℕ) : ℝ) * (1 / (8 * (H : ℝ)))) =
        ((H - 1 : ℕ) : ℝ) / 4 := by field_simp [ne_of_gt hH_pos]; ring
    linarith
  have hmul_lt := mul_lt_mul_of_pos_left hsum_lt (show 0 < 2 * (H : ℝ) by positivity)
  linarith

private lemma markov_upper_unit
    (μ : ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1))
    (f : (ℕ → Metric.sphere (0 : ℂ) 1) → ℝ)
    (hf_cont : Continuous f) (hf_le1 : ∀ z, f z ≤ 1)
    {a : ℝ} (ha_pos : 0 < a) (ha_le : a ≤ ∫ z, f z ∂(μ : Measure _)) :
    ENNReal.ofReal (a / 2) ≤ (μ : Measure _) { z | a / 2 ≤ f z } := by
  let S : Set (ℕ → Metric.sphere (0 : ℂ) 1) := { z | a / 2 ≤ f z }
  have hS_meas : MeasurableSet S := (isClosed_le continuous_const hf_cont).measurableSet
  have hpt : ∀ z, f z ≤ a / 2 + S.indicator (fun _ => (1 : ℝ)) z := by
    intro z
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem hz]
      linarith [hf_le1 z]
    · rw [Set.indicator_of_notMem hz, add_zero]
      have hlt : f z < a / 2 := lt_of_not_ge hz
      exact le_of_lt hlt
  have hint_f : Integrable f (μ : Measure _) := integrable_of_continuous_on_omega μ f hf_cont
  have hint_ind : Integrable (S.indicator fun _ => (1 : ℝ)) (μ : Measure _) :=
    (integrable_const (1 : ℝ)).indicator hS_meas
  have hmono : ∫ z, f z ∂(μ : Measure _) ≤ ∫ z, (a / 2 + S.indicator (fun _ => (1 : ℝ)) z) ∂(μ : Measure _) :=
    integral_mono hint_f ((integrable_const _).add hint_ind) hpt
  rw [integral_add (integrable_const _) hint_ind, integral_const, probReal_univ, one_smul,
    integral_indicator hS_meas, setIntegral_const, smul_eq_mul, mul_one, Measure.real_def] at hmono
  have hreal : a / 2 ≤ ((μ : Measure _) S).toReal := by linarith
  have hfin : (μ : Measure _) S ≠ ⊤ := measure_ne_top _ _
  calc ENNReal.ofReal (a / 2) ≤ ENNReal.ofReal ((μ : Measure _) S).toReal :=
        ENNReal.ofReal_le_ofReal hreal
    _ = (μ : Measure _) S := ENNReal.ofReal_toReal hfin

private lemma markov_lower_bound
    (μ : ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1))
    (f : (ℕ → Metric.sphere (0 : ℂ) 1) → ℝ)
    (hf_cont : Continuous f) (hf_nn : ∀ z, 0 ≤ f z)
    (S : Set (ℕ → Metric.sphere (0 : ℂ) 1)) (hS_meas : MeasurableSet S)
    {c : ℝ} (hbound : ∀ z ∈ S, c ≤ f z) :
    c * ((μ : Measure _) S).toReal ≤ ∫ z, f z ∂(μ : Measure _) := by
  have hint_f : Integrable f (μ : Measure _) := integrable_of_continuous_on_omega μ f hf_cont
  have hint_ind : Integrable (S.indicator fun _ => c) (μ : Measure _) :=
    (integrable_const c).indicator hS_meas
  have hpt : ∀ z, S.indicator (fun _ => c) z ≤ f z := by
    intro z
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem hz]; exact hbound z hz
    · rw [Set.indicator_of_notMem hz]; exact hf_nn z
  have hmono := integral_mono hint_ind hint_f hpt
  rw [integral_indicator hS_meas, setIntegral_const, smul_eq_mul, Measure.real_def, mul_comm] at hmono
  exact hmono

private lemma exists_positive_measure_nonvanishing_corr
    (μ : ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1)) (B : ℝ)
    (hB : ∀ n : ℕ, ∫ z, ‖∑ j ∈ Finset.Icc 1 n, gOf z j‖ ^ 2 ∂(μ : Measure _) ≤ B) :
    ∃ (η : ℝ), 0 < η ∧ ∃ (E : Set (ℕ → Metric.sphere (0 : ℂ) 1)),
      ENNReal.ofReal η ≤ (μ : Measure _) E ∧
      ∀ z ∈ E, ∃ d : ℕ, 1 ≤ d ∧
        ¬ Filter.Tendsto
          (fun X : ℕ =>
            ((1 / (∑ m ∈ Finset.Icc 1 X, (1 / (m : ℝ)))) : ℂ) *
              ∑ m ∈ Finset.Icc 1 X, ((1 / (m : ℝ)) : ℂ) * (gOf z m * star (gOf z (m + d))))
          Filter.atTop (nhds 0) := by
  obtain ⟨H, hH2, X₀, hX₀1, hcorr⟩ := exists_large_corr_shift μ B hB
  have hH_pos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  let δ : ℝ := 1 / (16 * (H : ℝ))
  have hδ_pos : 0 < δ := by positivity
  let A : ℕ → ℕ → (ℕ → Metric.sphere (0 : ℂ) 1) → ℝ := fun X d z =>
    ‖((1 / (∑ m ∈ Finset.Icc 1 X, (1 / (m : ℝ)))) : ℂ) *
      ∑ m ∈ Finset.Icc 1 X, ((1 / (m : ℝ)) : ℂ) * (gOf z m * star (gOf z (m + d)))‖
  have hA_cont : ∀ X d, Continuous (A X d) := fun X d => by
    dsimp only [A]
    refine Continuous.norm (continuous_const.mul (continuous_finsetSum _ fun m _ =>
      continuous_const.mul ((continuous_gOf m).mul (continuous_star.comp (continuous_gOf (m + d))))))
  have hA_le1 : ∀ X, 1 ≤ X → ∀ d z, A X d z ≤ 1 := by
    intro X hX d z
    dsimp only [A]
    have hL_pos : 0 < ∑ m ∈ Finset.Icc 1 X, (1 / (m : ℝ)) := harmonicSum_pos hX
    rw [norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hL_pos)]
    have hsum : ‖∑ m ∈ Finset.Icc 1 X, ((1 / (m : ℝ)) : ℂ) * (gOf z m * star (gOf z (m + d)))‖ ≤
        ∑ m ∈ Finset.Icc 1 X, (1 / (m : ℝ)) := by
      calc ‖∑ m ∈ Finset.Icc 1 X, ((1 / (m : ℝ)) : ℂ) * (gOf z m * star (gOf z (m + d)))‖
          ≤ ∑ m ∈ Finset.Icc 1 X, ‖((1 / (m : ℝ)) : ℂ) * (gOf z m * star (gOf z (m + d)))‖ :=
            norm_sum_le _ _
        _ = ∑ m ∈ Finset.Icc 1 X, (1 / (m : ℝ)) := by
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg m),
              norm_mul, norm_star, norm_gOf, norm_gOf, mul_one, mul_one]
    calc (1 / ∑ m ∈ Finset.Icc 1 X, (1 / (m : ℝ))) *
            ‖∑ m ∈ Finset.Icc 1 X, ((1 / (m : ℝ)) : ℂ) * (gOf z m * star (gOf z (m + d)))‖
        ≤ (1 / ∑ m ∈ Finset.Icc 1 X, (1 / (m : ℝ))) * ∑ m ∈ Finset.Icc 1 X, (1 / (m : ℝ)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 1 := one_div_mul_cancel (ne_of_gt hL_pos)
  let E_step : ℕ → Set (ℕ → Metric.sphere (0 : ℂ) 1) := fun X =>
    ⋃ d ∈ Finset.Icc 1 (H - 1), { z | δ ≤ A X d z }
  have hE_meas : ∀ X, MeasurableSet (E_step X) := fun X =>
    Finset.measurableSet_biUnion _ fun d _ => (isClosed_le continuous_const (hA_cont X d)).measurableSet
  have hE_lb : ∀ X, X₀ ≤ X → ENNReal.ofReal δ ≤ (μ : Measure _) (E_step X) := by
    intro X hX
    obtain ⟨d, hd, hle⟩ := hcorr X hX
    have hX1 : 1 ≤ X := le_trans hX₀1 hX
    have hmark := markov_upper_unit μ (A X d) (hA_cont X d) (hA_le1 X hX1 d)
      (show 0 < 1 / (8 * (H : ℝ)) by positivity) hle
    have hhalf : (1 / (8 * (H : ℝ))) / 2 = δ := by dsimp only [δ]; ring
    rw [hhalf] at hmark
    exact hmark.trans (measure_mono (fun z hz => Set.mem_iUnion₂.mpr ⟨d, hd, hz⟩))
  let U : ℕ → Set (ℕ → Metric.sphere (0 : ℂ) 1) := fun N => ⋃ X ≥ N, E_step X
  have hU_meas : ∀ N, MeasurableSet (U N) := fun N =>
    MeasurableSet.iUnion fun X => MeasurableSet.iUnion fun _ => hE_meas X
  have hU_anti : Antitone U := by
    intro N₁ N₂ hle z hz
    simp only [U, Set.mem_iUnion] at hz ⊢
    obtain ⟨X, hXN, hXE⟩ := hz
    exact ⟨X, le_trans hle hXN, hXE⟩
  have hU_lb : ∀ N, ENNReal.ofReal δ ≤ (μ : Measure _) (U N) := by
    intro N
    let X := max N X₀
    have hsub : E_step X ⊆ U N := by
      intro z hz
      exact Set.mem_iUnion₂.mpr ⟨X, le_max_left N X₀, hz⟩
    exact (hE_lb X (le_max_right N X₀)).trans (measure_mono hsub)
  let E_inf : Set (ℕ → Metric.sphere (0 : ℂ) 1) := ⋂ N : ℕ, U N
  have hEinf_lb : ENNReal.ofReal δ ≤ (μ : Measure _) E_inf := by
    rw [hU_anti.measure_iInter (fun N => (hU_meas N).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
    exact le_iInf hU_lb
  refine ⟨δ, hδ_pos, E_inf, hEinf_lb, fun z hz => ?_⟩
  have hinf : ∀ N : ℕ, ∃ X ≥ N, ∃ d ∈ Finset.Icc 1 (H - 1), δ ≤ A X d z := by
    intro N
    have hzU : z ∈ U N := Set.mem_iInter.mp hz N
    obtain ⟨X, hXN, hzE⟩ := Set.mem_iUnion₂.mp hzU
    obtain ⟨d, hd, hAd⟩ := Set.mem_iUnion₂.mp hzE
    exact ⟨X, hXN, d, hd, hAd⟩
  have hex_d : ∃ d ∈ Finset.Icc 1 (H - 1), ∀ N : ℕ, ∃ X ≥ N, δ ≤ A X d z := by
    by_contra hnone
    push Not at hnone
    have hbd : ∀ d : Finset.Icc 1 (H - 1), ∃ N : ℕ, ∀ X ≥ N, A X d.1 z < δ :=
      fun d => hnone d.1 d.2
    choose NOf hNOf using hbd
    let Nmax : ℕ := Finset.univ.sup NOf
    obtain ⟨X, hXN, d, hd, hAd⟩ := hinf Nmax
    have hle_sup : NOf ⟨d, hd⟩ ≤ Nmax :=
      Finset.le_sup (f := NOf) (Finset.mem_univ (⟨d, hd⟩ : Finset.Icc 1 (H - 1)))
    have hlt := hNOf ⟨d, hd⟩ X (le_trans hle_sup hXN)
    linarith
  obtain ⟨d, hd, hinf_d⟩ := hex_d
  refine ⟨d, (Finset.mem_Icc.mp hd).1, fun htend => ?_⟩
  have hev := (Metric.tendsto_atTop.mp htend) δ hδ_pos
  obtain ⟨N, hN⟩ := hev
  obtain ⟨X, hXN, hAd⟩ := hinf_d N
  have hdist := hN X hXN
  rw [dist_zero_right] at hdist
  change A X d z < δ at hdist
  linarith

end

theorem main : H1 → H2 → OMA.R_Erdos67_erdos_67_variants_complex_R1.H2 := by
  intro h1 h2 μ B
  by_contra hnot
  push Not at hnot
  have hB : ∀ n : ℕ, ∫ z, ‖∑ j ∈ Finset.Icc 1 n, gOf z j‖ ^ 2 ∂(μ : Measure _) ≤ B := hnot
  have hB_nn : 0 ≤ B := by
    have h0 := hB 0
    simp only [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1), Finset.sum_empty, norm_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero] at h0
    exact h0
  obtain ⟨η, hη_pos, E, hE_lb, hE_corr⟩ := exists_positive_measure_nonvanishing_corr μ B hB
  let F : ℕ → (ℕ → Metric.sphere (0 : ℂ) 1) → ℝ := fun X z =>
    (1 / (∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)))) *
      ∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)) * ‖∑ j ∈ Finset.Icc 1 n, gOf z j‖ ^ 2
  have hF_cont : ∀ X, Continuous (F X) := fun X => by
    dsimp only [F]
    refine continuous_const.mul (continuous_finsetSum _ fun n _ =>
      continuous_const.mul (Continuous.pow (Continuous.norm
        (continuous_finsetSum _ fun j _ => continuous_gOf j)) 2))
  have hF_nn : ∀ X z, 0 ≤ F X z := fun X z => by
    dsimp only [F]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ => by positivity)
  have hF_int_le : ∀ X : ℕ, 1 ≤ X → ∫ z, F X z ∂(μ : Measure _) ≤ B := by
    intro X hX
    have hL_pos : 0 < ∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)) := harmonicSum_pos hX
    have hint_n : ∀ n : ℕ, Integrable (fun z => (1 / (n : ℝ)) * ‖∑ j ∈ Finset.Icc 1 n, gOf z j‖ ^ 2)
        (μ : Measure _) := fun n =>
      integrable_of_continuous_on_omega μ _ (continuous_const.mul
        (Continuous.pow (Continuous.norm (continuous_finsetSum _ fun j _ => continuous_gOf j)) 2))
    have heq : ∫ z, F X z ∂(μ : Measure _) =
        (1 / (∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)))) *
          ∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)) *
            ∫ z, ‖∑ j ∈ Finset.Icc 1 n, gOf z j‖ ^ 2 ∂(μ : Measure _) := by
      dsimp only [F]
      rw [integral_const_mul, integral_finsetSum _ (fun n _ => hint_n n)]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [integral_const_mul]
    rw [heq]
    have hsum_le : ∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)) *
          ∫ z, ‖∑ j ∈ Finset.Icc 1 n, gOf z j‖ ^ 2 ∂(μ : Measure _) ≤
        (∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ))) * B := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hB n) (by positivity)
    calc (1 / (∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)))) *
            ∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)) *
              ∫ z, ‖∑ j ∈ Finset.Icc 1 n, gOf z j‖ ^ 2 ∂(μ : Measure _)
        ≤ (1 / (∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ)))) *
            ((∑ n ∈ Finset.Icc 1 X, (1 / (n : ℝ))) * B) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = B := by field_simp [ne_of_gt hL_pos]
  have hE_div : ∀ z ∈ E, Filter.Tendsto (fun X => F X z) Filter.atTop Filter.atTop := by
    intro z hz
    obtain ⟨d, hd, hnot_tend⟩ := hE_corr z hz
    have hpret := h1 (gOf z) d hd (gOf_one z) (fun n _ => norm_gOf z n)
      (fun a b ha hb => gOf_mul z ha hb) hnot_tend
    exact h2 (gOf z) (gOf_one z) (fun n _ => norm_gOf z n)
      (fun a b ha hb => gOf_mul z ha hb) hpret
  let K : ℝ := 4 * (B + 1) / η
  have hK_pos : 0 < K := by positivity
  let G : ℕ → Set (ℕ → Metric.sphere (0 : ℂ) 1) := fun N => ⋂ X ≥ N, { z | K ≤ F X z }
  have hG_meas : ∀ N, MeasurableSet (G N) := fun N =>
    MeasurableSet.iInter fun X => MeasurableSet.iInter fun _ =>
      (isClosed_le continuous_const (hF_cont X)).measurableSet
  have hG_mono : Monotone G := by
    intro N₁ N₂ hle z hz
    simp only [G, Set.mem_iInter] at hz ⊢
    intro X hXN₂
    exact hz X (le_trans hle hXN₂)
  have hE_sub : E ⊆ ⋃ N : ℕ, G N := by
    intro z hz
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((Filter.tendsto_atTop.mp (hE_div z hz)) K)
    exact Set.mem_iUnion.mpr ⟨N, Set.mem_iInter₂.mpr hN⟩
  have hsup_ge : ENNReal.ofReal η ≤ ⨆ N : ℕ, (μ : Measure _) (G N) := by
    rw [← hG_mono.measure_iUnion]
    exact hE_lb.trans (measure_mono hE_sub)
  have hlt_sup : ENNReal.ofReal (η / 2) < ⨆ N : ℕ, (μ : Measure _) (G N) := by
    have hlt : ENNReal.ofReal (η / 2) < ENNReal.ofReal η :=
      (ENNReal.ofReal_lt_ofReal_iff hη_pos).mpr (by linarith)
    exact lt_of_lt_of_le hlt hsup_ge
  obtain ⟨N₀, hN₀_gt⟩ := lt_iSup_iff.mp hlt_sup
  let X₁ : ℕ := max N₀ 1
  have hX₁_ge1 : 1 ≤ X₁ := le_max_right N₀ 1
  have hX₁_geN₀ : N₀ ≤ X₁ := le_max_left N₀ 1
  have hmark := markov_lower_bound μ (F X₁) (hF_cont X₁) (hF_nn X₁) (G N₀) (hG_meas N₀)
    (fun z hz => Set.mem_iInter₂.mp hz X₁ hX₁_geN₀)
  have hμG_gt : η / 2 < ((μ : Measure _) (G N₀)).toReal := by
    have hfin : (μ : Measure _) (G N₀) ≠ ⊤ := measure_ne_top _ _
    have h1 := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hfin).mpr hN₀_gt
    rwa [ENNReal.toReal_ofReal (by positivity)] at h1
  have hK_mul : 2 * (B + 1) < K * ((μ : Measure _) (G N₀)).toReal := by
    have heq : K * (η / 2) = 2 * (B + 1) := by
      dsimp only [K]
      field_simp [ne_of_gt hη_pos]
      ring
    calc 2 * (B + 1) = K * (η / 2) := heq.symm
      _ < K * ((μ : Measure _) (G N₀)).toReal := mul_lt_mul_of_pos_left hμG_gt hK_pos
  have hF_le := hF_int_le X₁ hX₁_ge1
  linarith

end OMA.R_Erdos67_erdos_67_variants_complex_R1_H2_R2
