import FormalConjectures.ErdosProblems.«67»
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Reduction of `Erdos67.erdos_67` (The Erdős Discrepancy Problem)

Following Terence Tao, *The Erdős discrepancy problem*, Discrete Anal. (2016), Paper No. 1
(`arXiv:1509.05363`), we reduce `Erdos67.erdos_67` to two canonical theorems:
1. (`H1`) Tao's logarithmically averaged nonasymptotic two-point Elliott conjecture (Theorem 1.5)
   for $S^1$-valued completely multiplicative functions.
2. (`H2`) Tao's generalized Borwein–Choi–Coons theorem (Section 4): a stochastic $S^1$-valued
   completely multiplicative function with uniformly bounded $L^2$ partial sums cannot pretend
   with high probability to a modulated Dirichlet character of bounded conductor.

Inside `main`, we prove both Section 2 (the Polymath5 discrete Fourier/Plancherel reduction on
$(\mathbb{Z}/M\mathbb{Z})^r$ followed by weak-* compactness in `ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1)`)
and Section 3 (the van der Corput + Markov deduction of Proposition 1.6 from Theorem 1.5).
-/

-- Reduction Erdos67.erdos_67.R1 of The Erdős discrepancy problem
-- Credit: @tkaiman
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

open Filter Finset MeasureTheory Complex
open scoped Topology Classical BigOperators

namespace OMA.R_Erdos67_erdos_67_R1

/- ### Step 1: Evaluation of completely multiplicative functions on `ℕ → Metric.sphere (0 : ℂ) 1` -/

lemma mulEval_norm (z : ℕ → Metric.sphere (0 : ℂ) 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖if n = 0 then (0 : ℂ) else n.factorization.prod fun p a => (z p).1 ^ a‖ = 1 := by
  have hn0 : n ≠ 0 := by omega
  rw [if_neg hn0, Finsupp.prod, norm_prod]
  refine Finset.prod_eq_one fun p _ => ?_
  rw [norm_pow, mem_sphere_zero_iff_norm.mp (z p).2, one_pow]

lemma mulEval_continuous (n : ℕ) :
    Continuous (fun z : ℕ → Metric.sphere (0 : ℂ) 1 =>
      if n = 0 then (0 : ℂ) else n.factorization.prod fun p a => (z p).1 ^ a) := by
  by_cases hn : n = 0
  · simp [hn]; exact continuous_const
  · simp only [hn, ↓reduceIte, Finsupp.prod]
    exact continuous_finsetProd _ fun p _ =>
      (continuous_subtype_val.comp (continuous_apply p)).pow _

lemma energy_continuous (n : ℕ) :
    Continuous (fun z : ℕ → Metric.sphere (0 : ℂ) 1 =>
      ‖∑ k ∈ Finset.Icc 1 n,
        (if k = 0 then (0 : ℂ) else k.factorization.prod fun p a => (z p).1 ^ a)‖ ^ 2) :=
  ((continuous_finsetSum _ fun k _ => mulEval_continuous k).norm).pow 2

/- ### Step 2: Discrete Fourier transform and Plancherel on `Fin r → ZMod M` -/

lemma zmod_exp_add {M : ℕ} [NeZero M] (a b : ZMod M) :
    Complex.exp (2 * Real.pi * Complex.I * (((a + b).val : ℝ) / (M : ℝ))) =
      Complex.exp (2 * Real.pi * Complex.I * ((a.val : ℝ) / (M : ℝ))) *
      Complex.exp (2 * Real.pi * Complex.I * ((b.val : ℝ) / (M : ℝ))) := by
  rw [← Complex.exp_add]
  have hMpos : 0 < M := NeZero.pos M
  have hMne : (M : ℂ) ≠ 0 := by exact_mod_cast hMpos.ne'
  have hdiv := Nat.div_add_mod (a.val + b.val) M
  have hval : (a + b).val = (a.val + b.val) % M := ZMod.val_add a b
  have hq : ((a + b).val : ℂ) = (a.val : ℂ) + (b.val : ℂ) -
      (((a.val + b.val) / M : ℕ) : ℂ) * (M : ℂ) := by
    have h1 : (M : ℂ) * (((a.val + b.val) / M : ℕ) : ℂ) + (((a.val + b.val) % M : ℕ) : ℂ) =
        (a.val : ℂ) + (b.val : ℂ) := by exact_mod_cast hdiv
    rw [hval]
    linear_combination h1
  let kint : ℤ := -(((a.val + b.val) / M : ℕ) : ℤ)
  have hexp_eq :
      2 * Real.pi * Complex.I * (((a + b).val : ℝ) / (M : ℝ)) =
      (2 * Real.pi * Complex.I * ((a.val : ℝ) / (M : ℝ)) +
        2 * Real.pi * Complex.I * ((b.val : ℝ) / (M : ℝ))) +
      (kint : ℂ) * (2 * Real.pi * Complex.I) := by
    have hkint : (kint : ℂ) = -(((a.val + b.val) / M : ℕ) : ℂ) := by dsimp [kint]; push_cast; rfl
    rw [hkint]
    push_cast
    rw [hq]
    field_simp [hMne]
    ring
  rw [hexp_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma zmod_exp_neg {M : ℕ} [NeZero M] (a : ZMod M) :
    star (Complex.exp (2 * Real.pi * Complex.I * ((a.val : ℝ) / (M : ℝ)))) =
      Complex.exp (2 * Real.pi * Complex.I * (((-a).val : ℝ) / (M : ℝ))) := by
  have hmul : Complex.exp (2 * Real.pi * Complex.I * ((a.val : ℝ) / (M : ℝ))) *
      Complex.exp (2 * Real.pi * Complex.I * (((-a).val : ℝ) / (M : ℝ))) = 1 := by
    rw [← zmod_exp_add, add_neg_cancel, ZMod.val_zero]
    simp
  have hnorm : Complex.exp (2 * Real.pi * Complex.I * ((a.val : ℝ) / (M : ℝ))) *
      star (Complex.exp (2 * Real.pi * Complex.I * ((a.val : ℝ) / (M : ℝ)))) = 1 := by
    rw [Complex.star_def, Complex.mul_conj']
    have h1 : ‖Complex.exp (2 * Real.pi * Complex.I * ((a.val : ℝ) / (M : ℝ)))‖ = 1 := by
      have hrw : 2 * Real.pi * Complex.I * ((a.val : ℝ) / (M : ℝ)) =
          ((2 * Real.pi * ((a.val : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hrw, Complex.norm_exp_ofReal_mul_I]
    rw [h1]
    norm_num
  have hne : Complex.exp (2 * Real.pi * Complex.I * ((a.val : ℝ) / (M : ℝ))) ≠ 0 :=
    Complex.exp_ne_zero _
  exact mul_left_cancel₀ hne (hnorm.trans hmul.symm)

lemma zmod_exp_nat_mul {M : ℕ} [NeZero M] (k : ℕ) (a : ZMod M) :
    Complex.exp (2 * Real.pi * Complex.I * ((((k : ZMod M) * a).val : ℝ) / (M : ℝ))) =
      (Complex.exp (2 * Real.pi * Complex.I * ((a.val : ℝ) / (M : ℝ)))) ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, zmod_exp_add, ih, pow_succ]

lemma zmod_orthogonality {M : ℕ} [NeZero M] (ξ : ZMod M) :
    ∑ x : ZMod M, Complex.exp (2 * Real.pi * Complex.I * (((x * ξ).val : ℝ) / (M : ℝ))) =
      if ξ = 0 then (M : ℂ) else 0 := by
  split_ifs with hξ
  · subst hξ; simp
  · let w : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((ξ.val : ℝ) / (M : ℝ)))
    have hw_ne : w ≠ 1 := by
      intro hw1
      rw [Complex.exp_eq_one_iff] at hw1
      obtain ⟨n, hn⟩ := hw1
      have h2piI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
        exact_mod_cast Real.pi_ne_zero
      have hrat : ((ξ.val : ℝ) / (M : ℝ) : ℂ) = (n : ℂ) := by
        apply mul_left_cancel₀ h2piI
        dsimp [w] at hn
        linear_combination hn
      have hratR : (ξ.val : ℝ) / (M : ℝ) = (n : ℝ) := by exact_mod_cast hrat
      have hMpos : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
      have hpos : 0 < ξ.val := Nat.pos_of_ne_zero fun h0 => hξ ((ZMod.val_eq_zero ξ).mp h0)
      have hlt : ξ.val < M := ZMod.val_lt ξ
      have h0 : (0 : ℝ) < (n : ℝ) := by rw [← hratR]; positivity
      have h1 : (n : ℝ) < 1 := by rw [← hratR, div_lt_one hMpos]; exact_mod_cast hlt
      have hn0 : 0 < n := by exact_mod_cast h0
      have hn1 : n < 1 := by exact_mod_cast h1
      omega
    have hwM : w ^ M = 1 := by
      rw [← zmod_exp_nat_mul, ZMod.natCast_self, zero_mul, ZMod.val_zero]
      simp
    have hsum : ∑ x : ZMod M,
        Complex.exp (2 * Real.pi * Complex.I * (((x * ξ).val : ℝ) / (M : ℝ))) =
        ∑ k ∈ Finset.range M, w ^ k := by
      refine Finset.sum_bij (fun x _ => x.val) ?_ ?_ ?_ ?_
      · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
      · intro x₁ _ x₂ _ h; exact ZMod.val_injective M h
      · intro k hk
        refine ⟨(k : ZMod M), Finset.mem_univ _, ZMod.val_natCast_of_lt (Finset.mem_range.mp hk)⟩
      · intro x _
        have hx : ((x.val : ZMod M) * ξ) = x * ξ := by rw [ZMod.natCast_zmod_val]
        rw [← hx, zmod_exp_nat_mul]
    rw [hsum, geom_sum_eq hw_ne, hwM, sub_self, zero_div]

lemma vec_orthogonality {r M : ℕ} [NeZero M] (ξ ξ' : Fin r → ZMod M) :
    ∑ x : Fin r → ZMod M,
      (∏ i : Fin r, Complex.exp (2 * Real.pi * Complex.I * (((x i * ξ i).val : ℝ) / (M : ℝ)))) *
      star (∏ i : Fin r, Complex.exp (2 * Real.pi * Complex.I * (((x i * ξ' i).val : ℝ) / (M : ℝ)))) =
      if ξ = ξ' then (M : ℂ) ^ r else 0 := by
  have hterm : ∀ x : Fin r → ZMod M,
      (∏ i : Fin r, Complex.exp (2 * Real.pi * Complex.I * (((x i * ξ i).val : ℝ) / (M : ℝ)))) *
      star (∏ i : Fin r, Complex.exp (2 * Real.pi * Complex.I * (((x i * ξ' i).val : ℝ) / (M : ℝ)))) =
      ∏ i : Fin r, Complex.exp (2 * Real.pi * Complex.I * (((x i * (ξ i - ξ' i)).val : ℝ) / (M : ℝ))) := by
    intro x
    rw [Complex.star_def, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Complex.star_def, zmod_exp_neg, ← zmod_exp_add]
    congr 4
    ring
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun i (y : ZMod M) =>
    Complex.exp (2 * Real.pi * Complex.I * (((y * (ξ i - ξ' i)).val : ℝ) / (M : ℝ))))]
  simp_rw [zmod_orthogonality]
  split_ifs with h
  · subst h
    simp [Finset.prod_const]
  · have hex : ∃ i : Fin r, ξ i ≠ ξ' i := by
      by_contra hall
      push Not at hall
      exact h (funext hall)
    obtain ⟨i₀, hi₀⟩ := hex
    refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
    rw [if_neg (sub_ne_zero.mpr hi₀)]

lemma plancherel_finite {r M : ℕ} [NeZero M] (F : (Fin r → ZMod M) → ℂ) :
    let χ : (Fin r → ZMod M) → (Fin r → ZMod M) → ℂ := fun ξ x =>
      ∏ i : Fin r, Complex.exp (2 * Real.pi * Complex.I * (((x i * ξ i).val : ℝ) / (M : ℝ)))
    let Fhat : (Fin r → ZMod M) → ℂ := fun ξ =>
      ((M : ℂ) ^ r)⁻¹ * ∑ x : Fin r → ZMod M, F x * star (χ ξ x)
    ∑ ξ : Fin r → ZMod M, ‖Fhat ξ‖ ^ 2 =
      ((M : ℝ) ^ r)⁻¹ * ∑ x : Fin r → ZMod M, ‖F x‖ ^ 2 := by
  intro χ Fhat
  have hC : ((∑ ξ : Fin r → ZMod M, ‖Fhat ξ‖ ^ 2 : ℝ) : ℂ) =
      ((((M : ℝ) ^ r)⁻¹ * ∑ x : Fin r → ZMod M, ‖F x‖ ^ 2 : ℝ) : ℂ) := by
    have hnormSq : ∀ z : ℂ, (‖z‖ : ℂ) ^ 2 = z * star z := fun z => by
      simpa [Complex.star_def] using (Complex.mul_conj' z).symm
    push_cast
    simp_rw [hnormSq]
    have hM : (M : ℂ) ^ r ≠ 0 := pow_ne_zero r (by exact_mod_cast (NeZero.pos M).ne')
    calc
      ∑ ξ, Fhat ξ * star (Fhat ξ)
          = ∑ ξ, (((M : ℂ) ^ r)⁻¹ * ∑ x, F x * star (χ ξ x)) *
              (((M : ℂ) ^ r)⁻¹ * ∑ y, star (F y) * χ ξ y) := by
            refine Finset.sum_congr rfl fun ξ _ => ?_
            have hstarF : star (Fhat ξ) = ((M : ℂ) ^ r)⁻¹ * ∑ y, star (F y) * χ ξ y := by
              dsimp [Fhat]
              simp only [map_mul, map_inv₀, map_pow, Complex.conj_natCast, map_sum,
                RingHomCompTriple.comp_apply, RingHom.id_apply]
            rw [hstarF]
      _ = ((M : ℂ) ^ r)⁻¹ * ((M : ℂ) ^ r)⁻¹ *
            ∑ x, ∑ y, F x * star (F y) * (∑ ξ, χ ξ y * star (χ ξ x)) := by
            have h1 : ∀ ξ : Fin r → ZMod M,
                (((M : ℂ) ^ r)⁻¹ * ∑ x, F x * star (χ ξ x)) *
                  (((M : ℂ) ^ r)⁻¹ * ∑ y, star (F y) * χ ξ y) =
                ((M : ℂ) ^ r)⁻¹ * ((M : ℂ) ^ r)⁻¹ *
                  ∑ x, ∑ y, F x * star (F y) * (χ ξ y * star (χ ξ x)) := by
              intro ξ
              have hmul : (∑ x, F x * star (χ ξ x)) * (∑ y, star (F y) * χ ξ y) =
                  ∑ x, ∑ y, F x * star (F y) * (χ ξ y * star (χ ξ x)) := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun x _ => ?_
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun y _ => by ring
              calc
                (((M : ℂ) ^ r)⁻¹ * ∑ x, F x * star (χ ξ x)) *
                    (((M : ℂ) ^ r)⁻¹ * ∑ y, star (F y) * χ ξ y)
                    = ((M : ℂ) ^ r)⁻¹ * ((M : ℂ) ^ r)⁻¹ *
                        ((∑ x, F x * star (χ ξ x)) * ∑ y, star (F y) * χ ξ y) := by ring
                _ = ((M : ℂ) ^ r)⁻¹ * ((M : ℂ) ^ r)⁻¹ *
                      ∑ x, ∑ y, F x * star (F y) * (χ ξ y * star (χ ξ x)) := by rw [hmul]
            simp_rw [h1]
            rw [← Finset.mul_sum, Finset.sum_comm]
            congr 1
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [← Finset.mul_sum]
      _ = ((M : ℂ) ^ r)⁻¹ * ((M : ℂ) ^ r)⁻¹ * ∑ x, F x * star (F x) * (M : ℂ) ^ r := by
            congr 1
            refine Finset.sum_congr rfl fun x _ => ?_
            have horth : ∀ y : Fin r → ZMod M,
                ∑ ξ, χ ξ y * star (χ ξ x) = if y = x then (M : ℂ) ^ r else 0 := by
              intro y
              have hcomm : ∀ (a b : Fin r → ZMod M), χ a b =
                  ∏ i : Fin r, Complex.exp (2 * Real.pi * Complex.I * (((a i * b i).val : ℝ) / (M : ℝ))) :=
                fun a b => Finset.prod_congr rfl fun i _ => by rw [mul_comm (b i) (a i)]
              have heq : ∑ ξ, χ ξ y * star (χ ξ x) =
                  ∑ ξ : Fin r → ZMod M,
                    (∏ i : Fin r, Complex.exp (2 * Real.pi * Complex.I * (((ξ i * y i).val : ℝ) / (M : ℝ)))) *
                    star (∏ i : Fin r, Complex.exp (2 * Real.pi * Complex.I * (((ξ i * x i).val : ℝ) / (M : ℝ)))) := by
                refine Finset.sum_congr rfl fun ξ _ => ?_
                rw [hcomm ξ y, hcomm ξ x]
              rw [heq]
              exact vec_orthogonality y x
            simp_rw [horth]
            simp
      _ = ((M : ℂ) ^ r)⁻¹ * ∑ x, F x * star (F x) := by
            rw [← Finset.sum_mul]
            field_simp [hM]
  exact Complex.ofReal_injective hC

lemma plancherel_shift_sum {r M : ℕ} [NeZero M] (F : (Fin r → ZMod M) → ℂ)
    (S : Finset ℕ) (π : ℕ → Fin r → ZMod M) :
    let χ : (Fin r → ZMod M) → (Fin r → ZMod M) → ℂ := fun ξ x =>
      ∏ i : Fin r, Complex.exp (2 * Real.pi * Complex.I * (((x i * ξ i).val : ℝ) / (M : ℝ)))
    let Fhat : (Fin r → ZMod M) → ℂ := fun ξ =>
      ((M : ℂ) ^ r)⁻¹ * ∑ x : Fin r → ZMod M, F x * star (χ ξ x)
    ((M : ℝ) ^ r)⁻¹ * ∑ x : Fin r → ZMod M, ‖∑ j ∈ S, F (x + π j)‖ ^ 2 =
      ∑ ξ : Fin r → ZMod M, ‖Fhat ξ‖ ^ 2 * ‖∑ j ∈ S, χ ξ (π j)‖ ^ 2 := by
  intro χ Fhat
  let G : (Fin r → ZMod M) → ℂ := fun x => ∑ j ∈ S, F (x + π j)
  have hGhat : ∀ ξ : Fin r → ZMod M,
      ((M : ℂ) ^ r)⁻¹ * ∑ x : Fin r → ZMod M, G x * star (χ ξ x) =
        Fhat ξ * ∑ j ∈ S, χ ξ (π j) := by
    intro ξ
    have hχ_add : ∀ a b : Fin r → ZMod M, χ ξ (a + b) = χ ξ a * χ ξ b := by
      intro a b
      dsimp [χ]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [add_mul]
      simpa only [Complex.ofReal_natCast] using zmod_exp_add (a i * ξ i) (b i * ξ i)
    have hχ_sub : ∀ a b : Fin r → ZMod M, star (χ ξ (a - b)) = star (χ ξ a) * χ ξ b := by
      intro a b
      have h1 : χ ξ (a - b) * χ ξ b = χ ξ a := by rw [← hχ_add, sub_add_cancel]
      have h2 : star (χ ξ b) * χ ξ b = 1 := by
        have hst : star (χ ξ b) = ∏ i : Fin r,
            star (Complex.exp (2 * Real.pi * Complex.I * (((b i * ξ i).val : ℝ) / (M : ℝ)))) := by
          dsimp [χ]
          simp only [map_prod]
        rw [hst]
        dsimp [χ]
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_eq_one fun i _ => ?_
        have hn := zmod_exp_neg (b i * ξ i)
        have ha := zmod_exp_add (-(b i * ξ i)) (b i * ξ i)
        simp only [Complex.ofReal_natCast] at hn ha
        rw [← Complex.star_def, hn, ← ha, neg_add_cancel, ZMod.val_zero]; simp
      have h3 := congrArg star h1
      simp only [Complex.star_def, map_mul] at h3
      simp only [← Complex.star_def] at h3
      have h4 := congrArg (fun z => z * χ ξ b) h3
      rw [mul_assoc, h2, mul_one] at h4
      exact h4
    calc
      ((M : ℂ) ^ r)⁻¹ * ∑ x, G x * star (χ ξ x)
          = ((M : ℂ) ^ r)⁻¹ * ∑ j ∈ S, ∑ x, F (x + π j) * star (χ ξ x) := by
            congr 1
            simp_rw [G, Finset.sum_mul]
            exact Finset.sum_comm
      _ = ((M : ℂ) ^ r)⁻¹ * ∑ j ∈ S, (∑ y, F y * star (χ ξ y)) * χ ξ (π j) := by
            congr 1
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_bij (fun x _ => x + π j) (fun _ _ => Finset.mem_univ _)
              (fun x₁ _ x₂ _ h => add_right_cancel h)
              (fun y _ => ⟨y - π j, Finset.mem_univ _, sub_add_cancel y (π j)⟩) ?_
            intro x _
            have hx : star (χ ξ x) = star (χ ξ (x + π j)) * χ ξ (π j) := by
              have hx0 : x = (x + π j) - π j := (add_sub_cancel_right x (π j)).symm
              conv_lhs => rw [hx0]
              exact hχ_sub (x + π j) (π j)
            rw [hx, mul_assoc]
      _ = Fhat ξ * ∑ j ∈ S, χ ξ (π j) := by
            dsimp [Fhat]
            rw [← Finset.mul_sum]
            ring
  have hp := plancherel_finite G
  dsimp only at hp
  rw [← hp]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [hGhat ξ, norm_mul, mul_pow]

/- ### Step 3: Polymath5 Fourier reduction and weak-* compactness (Tao Section 2) -/

lemma bad_card_bound (r M X : ℕ) [NeZero M] (hXM : X < M) :
    ((Finset.univ.filter fun x : Fin r → ZMod M => ¬ ∀ i : Fin r, (x i).val + X < M).card : ℝ) *
      (M : ℝ) ≤ (r : ℝ) * (X : ℝ) * (M : ℝ) ^ r := by
  cases r with
  | zero =>
    have hBad0 : (Finset.univ.filter fun x : Fin 0 → ZMod M => ¬ ∀ i : Fin 0, (x i).val + X < M) = ∅ := by
      ext x; simp
    rw [hBad0]; simp
  | succ r' =>
    let Bad : Finset (Fin (r' + 1) → ZMod M) :=
      Finset.univ.filter fun x => ¬ ∀ i : Fin (r' + 1), (x i).val + X < M
    have hsub : Bad ⊆ Finset.univ.biUnion fun i : Fin (r' + 1) =>
        Finset.univ.filter fun x : Fin (r' + 1) → ZMod M => M ≤ (x i).val + X := by
      intro x hx
      have hnot := (Finset.mem_filter.mp hx).2
      push Not at hnot
      obtain ⟨i, hi⟩ := hnot
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    have hslice : ∀ i : Fin (r' + 1),
        (Finset.univ.filter fun x : Fin (r' + 1) → ZMod M => M ≤ (x i).val + X).card ≤ X * M ^ r' := by
      intro i
      let BadVal : Finset (ZMod M) := Finset.univ.filter fun y : ZMod M => M ≤ y.val + X
      have hBadVal : BadVal.card ≤ X := by
        have hinj : BadVal.card ≤ (Finset.Ico (M - X) M).card := by
          refine Finset.card_le_card_of_injOn (fun y : ZMod M => y.val) ?_ ?_
          · intro y hy
            have h1 : M ≤ y.val + X := (Finset.mem_filter.mp hy).2
            rw [Finset.mem_coe, Finset.mem_Ico]
            exact ⟨Nat.sub_le_of_le_add (by omega), ZMod.val_lt y⟩
          · intro y₁ _ y₂ _ h; exact ZMod.val_injective M h
        rw [Nat.card_Ico] at hinj
        omega
      let Rest : Type := {j : Fin (r' + 1) // j ≠ i} → ZMod M
      have hcard_rest : Fintype.card Rest = M ^ r' := by
        dsimp [Rest]
        rw [Fintype.card_fun, ZMod.card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
          Fintype.card_fin]
        simp
      have hinj2 : (Finset.univ.filter fun x : Fin (r' + 1) → ZMod M => M ≤ (x i).val + X).card ≤
          (BadVal ×ˢ (Finset.univ : Finset Rest)).card := by
        refine Finset.card_le_card_of_injOn (fun x => (x i, fun j => x j.1)) ?_ ?_
        · intro x hx
          exact Finset.mem_coe.mpr (Finset.mem_product.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩, Finset.mem_univ _⟩)
        · intro x₁ _ x₂ _ h
          ext j
          by_cases hji : j = i
          · subst hji; exact congrArg Prod.fst h
          · exact congrFun (congrArg Prod.snd h) ⟨j, hji⟩
      rw [Finset.card_product, Finset.card_univ, hcard_rest] at hinj2
      exact hinj2.trans (Nat.mul_le_mul_right _ hBadVal)
    have hBad_nat : Bad.card ≤ (r' + 1) * (X * M ^ r') := by
      calc
        Bad.card ≤ (Finset.univ.biUnion fun i : Fin (r' + 1) =>
            Finset.univ.filter fun x : Fin (r' + 1) → ZMod M => M ≤ (x i).val + X).card :=
          Finset.card_le_card hsub
        _ ≤ ∑ i : Fin (r' + 1),
            (Finset.univ.filter fun x : Fin (r' + 1) → ZMod M => M ≤ (x i).val + X).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _ : Fin (r' + 1), (X * M ^ r') := Finset.sum_le_sum fun i _ => hslice i
        _ = (r' + 1) * (X * M ^ r') := by simp
    have hBad_mul : Bad.card * M ≤ (r' + 1) * X * M ^ (r' + 1) := by
      calc
        Bad.card * M ≤ (r' + 1) * (X * M ^ r') * M := Nat.mul_le_mul_right M hBad_nat
        _ = (r' + 1) * X * M ^ (r' + 1) := by rw [pow_succ]; ring
    exact_mod_cast hBad_mul

lemma finite_level_prob_measure
    (f : ℕ → ({-1, 1} : Finset ℝ)) (C : ℝ) (_hC : 0 ≤ C)
    (hbd : ∀ d ≥ 1, ∀ m ≥ 1, |∑ k ∈ Finset.Icc 1 m, (f (k * d)).1| ≤ C)
    (X : ℕ) :
    ∃ μ : ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1), ∀ n ≤ X,
      ∫ z, ‖∑ k ∈ Finset.Icc 1 n,
        (if k = 0 then (0 : ℂ) else k.factorization.prod fun p a => (z p).1 ^ a)‖ ^ 2
        ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) ≤ C ^ 2 + 1 := by
  let P : Finset ℕ := (Finset.Icc 1 X).filter Nat.Prime
  let r : ℕ := P.card
  let p : Fin r → ℕ := fun i => (P.equivFin.symm i).val
  have hp_mem : ∀ i : Fin r, p i ∈ P := fun i => (P.equivFin.symm i).property
  have hp_prime : ∀ i : Fin r, (p i).Prime := fun i => (Finset.mem_filter.mp (hp_mem i)).2
  have hp_inj : Function.Injective p := fun i j h =>
    (P.equivFin.symm).injective (Subtype.ext h)
  let M : ℕ := (r + 1) * (X + 1) ^ 3 + 1
  have hM_pos : 0 < M := by dsimp [M]; positivity
  have : NeZero M := ⟨hM_pos.ne'⟩
  have hX_lt_M : X < M := by
    dsimp [M]
    have h1 : X + 1 ≤ (X + 1) ^ 3 := Nat.le_self_pow (by norm_num) (X + 1)
    have h2 : (X + 1) ^ 3 ≤ (r + 1) * (X + 1) ^ 3 := Nat.le_mul_of_pos_left _ (Nat.succ_pos r)
    omega
  let F : (Fin r → ZMod M) → ℂ := fun x =>
    ((f (∏ i : Fin r, (p i) ^ (x i).val)).1 : ℂ)
  have hF_norm : ∀ x : Fin r → ZMod M, ‖F x‖ = 1 := by
    intro x
    dsimp [F]
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hmem := (f (∏ i : Fin r, (p i) ^ (x i).val)).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h <;> rw [h] <;> norm_num
  let π : ℕ → Fin r → ZMod M := fun j i => ((j.factorization (p i) : ℕ) : ZMod M)
  let χ : (Fin r → ZMod M) → (Fin r → ZMod M) → ℂ := fun ξ x =>
    ∏ i : Fin r, Complex.exp (2 * Real.pi * Complex.I * (((x i * ξ i).val : ℝ) / (M : ℝ)))
  let Fhat : (Fin r → ZMod M) → ℂ := fun ξ =>
    ((M : ℂ) ^ r)⁻¹ * ∑ x : Fin r → ZMod M, F x * star (χ ξ x)
  have hsum_Fhat : ∑ ξ : Fin r → ZMod M, ‖Fhat ξ‖ ^ 2 = 1 := by
    have hp1 := plancherel_finite F
    dsimp only at hp1
    rw [hp1]
    simp_rw [hF_norm, one_pow]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card,
      nsmul_eq_mul, mul_one]
    push_cast
    have hMne : ((M : ℝ) ^ r) ≠ 0 := by positivity
    field_simp [hMne]
  let zOf : (Fin r → ZMod M) → (ℕ → Metric.sphere (0 : ℂ) 1) := fun ξ q =>
    if h : ∃ i : Fin r, p i = q then
      ⟨Complex.exp (2 * Real.pi * Complex.I * (((ξ h.choose).val : ℝ) / (M : ℝ))), by
        rw [mem_sphere_zero_iff_norm]
        have hrw : 2 * Real.pi * Complex.I * (((ξ h.choose).val : ℝ) / (M : ℝ)) =
            ((2 * Real.pi * (((ξ h.choose).val : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [hrw, Complex.norm_exp_ofReal_mul_I]⟩
    else ⟨1, by simp⟩
  have hzOf_eval : ∀ (ξ : Fin r → ZMod M) (j : ℕ), 1 ≤ j → j ≤ X →
      (if j = 0 then (0 : ℂ) else j.factorization.prod fun q a => (zOf ξ q).1 ^ a) =
        χ ξ (π j) := by
    intro ξ j hj1 hjX
    have hj0 : j ≠ 0 := by omega
    rw [if_neg hj0, Finsupp.prod]
    have hsupp : j.factorization.support ⊆ Finset.univ.image p := by
      intro q hq
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors (by simpa [Nat.support_factorization] using hq)
      have hqdvd : q ∣ j := Nat.dvd_of_mem_primeFactors (by simpa [Nat.support_factorization] using hq)
      have hqle : q ≤ X := (Nat.le_of_dvd (by omega) hqdvd).trans hjX
      have hqP : q ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hqp.one_le, hqle⟩, hqp⟩
      refine Finset.mem_image.mpr ⟨P.equivFin ⟨q, hqP⟩, Finset.mem_univ _, ?_⟩
      simp [p]
    have hprod_eq : ∏ q ∈ j.factorization.support, (zOf ξ q).1 ^ j.factorization q =
        ∏ q ∈ Finset.univ.image p, (zOf ξ q).1 ^ j.factorization q := by
      refine Finset.prod_subset hsupp fun q _ hq_not => ?_
      have : j.factorization q = 0 := Finsupp.notMem_support_iff.mp hq_not
      simp [this]
    rw [hprod_eq, Finset.prod_image (fun i _ j _ h => hp_inj h)]
    dsimp [χ]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hex : ∃ i' : Fin r, p i' = p i := ⟨i, rfl⟩
    have hch : hex.choose = i := hp_inj hex.choose_spec
    dsimp [zOf, π]
    rw [dif_pos hex, hch]
    exact (zmod_exp_nat_mul (j.factorization (p i)) (ξ i)).symm
  let μraw : Measure (ℕ → Metric.sphere (0 : ℂ) 1) :=
    ∑ ξ : Fin r → ZMod M, ENNReal.ofReal (‖Fhat ξ‖ ^ 2) • Measure.dirac (zOf ξ)
  have hμ_mass : μraw Set.univ = 1 := by
    dsimp [μraw]
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, measure_univ,
      mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _), hsum_Fhat, ENNReal.ofReal_one]
  let μ : ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1) := ⟨μraw, ⟨hμ_mass⟩⟩
  refine ⟨μ, fun n hnX => ?_⟩
  by_cases hn0 : n = 0
  · subst hn0
    have hzero : ∀ z : ℕ → Metric.sphere (0 : ℂ) 1,
        ‖∑ k ∈ Finset.Icc 1 0,
          (if k = 0 then (0 : ℂ) else k.factorization.prod fun p a => (z p).1 ^ a)‖ ^ 2 = 0 := by
      intro z; simp
    simp_rw [hzero, integral_zero]
    positivity
  have hint_eq : ∀ φ : (ℕ → Metric.sphere (0 : ℂ) 1) → ℝ,
      ∫ z, φ z ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) = ∑ ξ : Fin r → ZMod M, ‖Fhat ξ‖ ^ 2 * φ (zOf ξ) := by
    intro φ
    have hint_each : ∀ ξ : Fin r → ZMod M,
        Integrable φ (ENNReal.ofReal (‖Fhat ξ‖ ^ 2) • Measure.dirac (zOf ξ)) := fun ξ =>
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
    change ∫ z, φ z ∂μraw = _
    dsimp [μraw]
    rw [integral_finsetSum_measure (fun ξ _ => hint_each ξ)]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul,
      integral_dirac]
  rw [hint_eq]
  have hmatch : ∑ ξ : Fin r → ZMod M, ‖Fhat ξ‖ ^ 2 *
      ‖∑ k ∈ Finset.Icc 1 n,
        (if k = 0 then (0 : ℂ) else k.factorization.prod fun p a => (zOf ξ p).1 ^ a)‖ ^ 2 =
      ∑ ξ : Fin r → ZMod M, ‖Fhat ξ‖ ^ 2 * ‖∑ k ∈ Finset.Icc 1 n, χ ξ (π k)‖ ^ 2 := by
    refine Finset.sum_congr rfl fun ξ _ => ?_
    have hinner : ∑ k ∈ Finset.Icc 1 n,
        (if k = 0 then (0 : ℂ) else k.factorization.prod fun p a => (zOf ξ p).1 ^ a) =
        ∑ k ∈ Finset.Icc 1 n, χ ξ (π k) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
      exact hzOf_eval ξ k hk1 (hkn.trans hnX)
    rw [hinner]
  rw [hmatch, ← plancherel_shift_sum F (Finset.Icc 1 n) π]
  let Good : Finset (Fin r → ZMod M) := Finset.univ.filter fun x => ∀ i : Fin r, (x i).val + X < M
  let Bad : Finset (Fin r → ZMod M) := Finset.univ.filter fun x => ¬ ∀ i : Fin r, (x i).val + X < M
  have hpart : (Finset.univ : Finset (Fin r → ZMod M)) = Good ∪ Bad := by
    ext x
    simp only [Good, Bad, Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
    exact em _
  have hdisj : Disjoint Good Bad := Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
  have hgood_bd : ∀ x ∈ Good, ‖∑ k ∈ Finset.Icc 1 n, F (x + π k)‖ ^ 2 ≤ C ^ 2 := by
    intro x hx
    have hxg : ∀ i : Fin r, (x i).val + X < M := (Finset.mem_filter.mp hx).2
    let d : ℕ := ∏ i : Fin r, (p i) ^ (x i).val
    have hd_pos : 1 ≤ d := Finset.one_le_prod' fun i _ => Nat.one_le_pow _ _ (hp_prime i).pos
    have hshift : ∀ k ∈ Finset.Icc 1 n, F (x + π k) = ((f (k * d)).1 : ℂ) := by
      intro k hk
      obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
      have hkX : k ≤ X := hkn.trans hnX
      have hk0 : k ≠ 0 := by omega
      have hprod_k : ∏ i : Fin r, (p i) ^ (k.factorization (p i)) = k := by
        have hsupp : k.factorization.support ⊆ Finset.univ.image p := by
          intro q hq
          have hqp : q.Prime := Nat.prime_of_mem_primeFactors (by simpa [Nat.support_factorization] using hq)
          have hqdvd : q ∣ k := Nat.dvd_of_mem_primeFactors (by simpa [Nat.support_factorization] using hq)
          have hqle : q ≤ X := (Nat.le_of_dvd (by omega) hqdvd).trans hkX
          have hqP : q ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hqp.one_le, hqle⟩, hqp⟩
          refine Finset.mem_image.mpr ⟨P.equivFin ⟨q, hqP⟩, Finset.mem_univ _, ?_⟩
          simp [p]
        have h1 : ∏ i : Fin r, (p i) ^ (k.factorization (p i)) =
            ∏ q ∈ Finset.univ.image p, q ^ k.factorization q :=
          (Finset.prod_image (f := fun q => q ^ k.factorization q) (fun i _ j _ h => hp_inj h)).symm
        rw [h1, ← Finset.prod_subset hsupp (fun q _ hq => by
          have : k.factorization q = 0 := Finsupp.notMem_support_iff.mp hq
          simp [this])]
        exact Nat.prod_factorization_pow_eq_self hk0
      have hval_add : ∀ i : Fin r, (x i + π k i).val = (x i).val + k.factorization (p i) := by
        intro i
        have hfac_le : k.factorization (p i) ≤ X := by
          have hpow_le : (p i) ^ k.factorization (p i) ≤ k :=
            Nat.le_of_dvd (by omega) (Nat.ordProj_dvd k (p i))
          have h2le : 2 ^ k.factorization (p i) ≤ (p i) ^ k.factorization (p i) :=
            Nat.pow_le_pow_left (hp_prime i).two_le _
          have hlt2 : k.factorization (p i) < 2 ^ k.factorization (p i) := Nat.lt_two_pow_self
          omega
        have hsum_lt : (x i).val + k.factorization (p i) < M := by
          have := hxg i; omega
        have hpi_val : (π k i).val = k.factorization (p i) :=
          ZMod.val_natCast_of_lt (by omega)
        rw [ZMod.val_add, hpi_val, Nat.mod_eq_of_lt hsum_lt]
      have hprod_eq : ∏ i : Fin r, (p i) ^ (x i + π k i).val = k * d := by
        calc
          ∏ i : Fin r, (p i) ^ (x i + π k i).val
              = ∏ i : Fin r, (p i) ^ ((x i).val + k.factorization (p i)) :=
                Finset.prod_congr rfl fun i _ => by rw [hval_add i]
          _ = (∏ i : Fin r, (p i) ^ (x i).val) * ∏ i : Fin r, (p i) ^ k.factorization (p i) := by
                simp_rw [pow_add, Finset.prod_mul_distrib]
          _ = d * k := by rw [hprod_k]
          _ = k * d := mul_comm d k
      dsimp [F]
      rw [hprod_eq]
    rw [Finset.sum_congr rfl hshift, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    have h1 := hbd d hd_pos n (by omega)
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hbad_bd : ∀ x ∈ Bad, ‖∑ k ∈ Finset.Icc 1 n, F (x + π k)‖ ^ 2 ≤ (X : ℝ) ^ 2 := by
    intro x _
    have h1 : ‖∑ k ∈ Finset.Icc 1 n, F (x + π k)‖ ≤ (X : ℝ) := by
      calc
        ‖∑ k ∈ Finset.Icc 1 n, F (x + π k)‖
            ≤ ∑ k ∈ Finset.Icc 1 n, ‖F (x + π k)‖ := norm_sum_le _ _
        _ = (n : ℝ) := by simp [hF_norm]
        _ ≤ (X : ℝ) := by exact_mod_cast hnX
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hbad_card : (Bad.card : ℝ) * (M : ℝ) ≤ (r : ℝ) * (X : ℝ) * (M : ℝ) ^ r :=
    bad_card_bound r M X hX_lt_M
  have hGood_le : (Good.card : ℝ) ≤ (M : ℝ) ^ r := by
    have : Good.card ≤ Fintype.card (Fin r → ZMod M) := Finset.card_le_univ Good
    rw [Fintype.card_fun, Fintype.card_fin, ZMod.card] at this
    exact_mod_cast this
  have hMpow_pos : (0 : ℝ) < (M : ℝ) ^ r := pow_pos (by exact_mod_cast hM_pos) r
  have hBad_term : ((M : ℝ) ^ r)⁻¹ * ((Bad.card : ℝ) * (X : ℝ) ^ 2) ≤ 1 := by
    have hM_ge : (r : ℝ) * (X : ℝ) * (X : ℝ) ^ 2 ≤ (M : ℝ) := by
      have hnat : r * X * X ^ 2 ≤ M := by
        dsimp [M]
        have h1 : r ≤ r + 1 := Nat.le_succ r
        have h2 : X * X ^ 2 ≤ (X + 1) ^ 3 := by
          calc X * X ^ 2 = X ^ 3 := by ring
            _ ≤ (X + 1) ^ 3 := Nat.pow_le_pow_left (Nat.le_succ X) 3
        calc r * X * X ^ 2 = r * (X * X ^ 2) := by ring
          _ ≤ (r + 1) * (X + 1) ^ 3 := Nat.mul_le_mul h1 h2
          _ ≤ (r + 1) * (X + 1) ^ 3 + 1 := Nat.le_succ _
      exact_mod_cast hnat
    have hMposR : (0 : ℝ) < M := by exact_mod_cast hM_pos
    have hstep : (Bad.card : ℝ) * (X : ℝ) ^ 2 * (M : ℝ) ≤ (M : ℝ) ^ r * (M : ℝ) := by
      calc
        (Bad.card : ℝ) * (X : ℝ) ^ 2 * (M : ℝ)
            = ((Bad.card : ℝ) * (M : ℝ)) * (X : ℝ) ^ 2 := by ring
        _ ≤ ((r : ℝ) * (X : ℝ) * (M : ℝ) ^ r) * (X : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_right hbad_card (sq_nonneg _)
        _ = (M : ℝ) ^ r * ((r : ℝ) * (X : ℝ) * (X : ℝ) ^ 2) := by ring
        _ ≤ (M : ℝ) ^ r * (M : ℝ) := mul_le_mul_of_nonneg_left hM_ge hMpow_pos.le
    have hstep2 : (Bad.card : ℝ) * (X : ℝ) ^ 2 ≤ (M : ℝ) ^ r :=
      le_of_mul_le_mul_right hstep hMposR
    rw [inv_mul_le_iff₀ hMpow_pos, mul_one]
    exact hstep2
  calc
    ((M : ℝ) ^ r)⁻¹ * ∑ x : Fin r → ZMod M, ‖∑ k ∈ Finset.Icc 1 n, F (x + π k)‖ ^ 2
        = ((M : ℝ) ^ r)⁻¹ * ((∑ x ∈ Good, ‖∑ k ∈ Finset.Icc 1 n, F (x + π k)‖ ^ 2) +
            ∑ x ∈ Bad, ‖∑ k ∈ Finset.Icc 1 n, F (x + π k)‖ ^ 2) := by
          rw [hpart, Finset.sum_union hdisj]
    _ ≤ ((M : ℝ) ^ r)⁻¹ * ((Good.card : ℝ) * C ^ 2 + (Bad.card : ℝ) * (X : ℝ) ^ 2) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (inv_nonneg.mpr hMpow_pos.le)
          · calc ∑ x ∈ Good, ‖∑ k ∈ Finset.Icc 1 n, F (x + π k)‖ ^ 2
                ≤ ∑ _ ∈ Good, C ^ 2 := Finset.sum_le_sum hgood_bd
              _ = (Good.card : ℝ) * C ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
          · calc ∑ x ∈ Bad, ‖∑ k ∈ Finset.Icc 1 n, F (x + π k)‖ ^ 2
                ≤ ∑ _ ∈ Bad, (X : ℝ) ^ 2 := Finset.sum_le_sum hbad_bd
              _ = (Bad.card : ℝ) * (X : ℝ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((M : ℝ) ^ r)⁻¹ * ((Good.card : ℝ) * C ^ 2) +
          ((M : ℝ) ^ r)⁻¹ * ((Bad.card : ℝ) * (X : ℝ) ^ 2) := by ring
    _ ≤ C ^ 2 + 1 := by
          have hG : ((M : ℝ) ^ r)⁻¹ * ((Good.card : ℝ) * C ^ 2) ≤ C ^ 2 := by
            rw [inv_mul_le_iff₀ hMpow_pos]
            exact mul_le_mul_of_nonneg_right hGood_le (sq_nonneg C)
          linarith

lemma exists_global_prob_measure
    (f : ℕ → ({-1, 1} : Finset ℝ)) (C : ℝ) (hC : 0 ≤ C)
    (hbd : ∀ d ≥ 1, ∀ m ≥ 1, |∑ k ∈ Finset.Icc 1 m, (f (k * d)).1| ≤ C) :
    ∃ μ : ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1), ∀ n : ℕ,
      ∫ z, ‖∑ k ∈ Finset.Icc 1 n,
        (if k = 0 then (0 : ℂ) else k.factorization.prod fun p a => (z p).1 ^ a)‖ ^ 2
        ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) ≤ C ^ 2 + 1 := by
  let E : ℕ → (ℕ → Metric.sphere (0 : ℂ) 1) → ℝ := fun n z =>
    ‖∑ k ∈ Finset.Icc 1 n,
      (if k = 0 then (0 : ℂ) else k.factorization.prod fun p a => (z p).1 ^ a)‖ ^ 2
  let K : ℕ → Set (ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1)) := fun N =>
    {μ | ∀ n ≤ N, ∫ z, E n z ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) ≤ C ^ 2 + 1}
  have hclosed_one : ∀ n : ℕ,
      IsClosed {μ : ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1) |
        ∫ z, E n z ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) ≤ C ^ 2 + 1} := by
    intro n
    have hcont : Continuous (fun μ : ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1) =>
        ∫ z, E n z ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1))) :=
      ProbabilityMeasure.continuous_integral_continuousMap
        (⟨E n, energy_continuous n⟩ : C(ℕ → Metric.sphere (0 : ℂ) 1, ℝ))
    exact isClosed_le hcont continuous_const
  have hclosed : ∀ N : ℕ, IsClosed (K N) := by
    intro N
    have heq : K N = ⋂ n ∈ Finset.range (N + 1),
        {μ : ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1) |
          ∫ z, E n z ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) ≤ C ^ 2 + 1} := by
      ext μ; simp [K]
    rw [heq]
    exact isClosed_biInter fun n _ => hclosed_one n
  have hne : ∀ N : ℕ, (K N).Nonempty := fun N => finite_level_prob_measure f C hC hbd N
  have hanti : Antitone K := fun M N hMN μ hμ n hn => hμ n (hn.trans hMN)
  obtain ⟨μ, hμ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    K (fun N => hanti (Nat.le_succ N)) hne (hclosed 0).isCompact hclosed
  refine ⟨μ, fun n => ?_⟩
  exact (Set.mem_iInter.mp hμ n) n le_rfl

/- ### Step 4: Van der Corput and Markov deduction of Proposition 1.6 (Tao Section 3) -/

lemma sum_inv_Icc_two_le_log (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, (1 / (n : ℝ)) ≤ Real.log (N : ℝ) := by
  induction N with
  | zero => simp
  | succ m ih =>
    cases m with
    | zero => simp
    | succ k =>
      have hsub : Finset.Icc 2 (k + 2) = insert (k + 2) (Finset.Icc 2 (k + 1)) := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsub, Finset.sum_insert (by simp)]
      have hk1 : (0 : ℝ) < (k + 1 : ℕ) := by positivity
      have hk2 : (0 : ℝ) < (k + 2 : ℕ) := by positivity
      have hlog := Real.log_le_sub_one_of_pos (div_pos hk1 hk2)
      rw [Real.log_div hk1.ne' hk2.ne'] at hlog
      have h1 : ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) - 1 = -(1 / ((k + 2 : ℕ) : ℝ)) := by
        push_cast; field_simp; ring
      linarith

lemma sum_inv_Icc_ge_log_sub (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Real.log ((b + 1 : ℕ) : ℝ) - Real.log (a : ℝ) ≤ ∑ n ∈ Finset.Icc a b, (1 / (n : ℝ)) := by
  induction b, hab using Nat.le_induction with
  | base =>
    simp only [Finset.Icc_self, Finset.sum_singleton]
    have hapos : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    have ha1pos : (0 : ℝ) < (a + 1 : ℕ) := by positivity
    have hlog := Real.log_le_sub_one_of_pos (div_pos ha1pos hapos)
    rw [Real.log_div ha1pos.ne' hapos.ne'] at hlog
    have h1 : ((a + 1 : ℕ) : ℝ) / (a : ℝ) - 1 = 1 / (a : ℝ) := by push_cast; field_simp; ring
    linarith
  | succ k hka ih =>
    have hsub : Finset.Icc a (k + 1) = insert (k + 1) (Finset.Icc a k) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hsub, Finset.sum_insert (by simp)]
    have hk1pos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have hk2pos : (0 : ℝ) < (k + 2 : ℕ) := by positivity
    have hlog := Real.log_le_sub_one_of_pos (div_pos hk2pos hk1pos)
    rw [Real.log_div hk2pos.ne' hk1pos.ne'] at hlog
    have h1 : ((k + 2 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) - 1 = 1 / ((k + 1 : ℕ) : ℝ) := by
      push_cast; field_simp; ring
    linarith

lemma sum_inv_sqrt_bounds {X : ℕ} (hX : 100 ≤ X) :
    (1 / 3 : ℝ) * Real.log (X : ℝ) ≤ ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ)) ∧
    ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ)) ≤ Real.log (X : ℝ) := by
  have hsqrt_le : Nat.sqrt X + 1 ≤ X := by
    have h1 : Nat.sqrt X ≤ 10 → Nat.sqrt X + 1 ≤ X := by omega
    have h2 : Nat.sqrt X * Nat.sqrt X ≤ X := Nat.sqrt_le X
    nlinarith
  constructor
  · have h1 := sum_inv_Icc_ge_log_sub (Nat.sqrt X + 1) X (by omega) hsqrt_le
    have hXpos : (0 : ℝ) < X := by positivity
    have hlog_ge : Real.log (X : ℝ) ≤ Real.log ((X + 1 : ℕ) : ℝ) :=
      Real.log_le_log hXpos (by exact_mod_cast Nat.le_succ X)
    have hs_le : ((Nat.sqrt X + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (X : ℝ) := by
      have hsq : (Nat.sqrt X : ℝ) ≤ Real.sqrt (X : ℝ) := by
        rw [← Real.sqrt_sq (Nat.cast_nonneg (Nat.sqrt X))]
        exact Real.sqrt_le_sqrt (by rw [sq]; exact_mod_cast Nat.sqrt_le X)
      have h1le : (1 : ℝ) ≤ Real.sqrt (X : ℝ) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ X by omega))
      push_cast; linarith
    have hlog_s : Real.log ((Nat.sqrt X + 1 : ℕ) : ℝ) ≤ Real.log 2 + (1 / 2 : ℝ) * Real.log (X : ℝ) := by
      calc
        Real.log ((Nat.sqrt X + 1 : ℕ) : ℝ)
            ≤ Real.log (2 * Real.sqrt (X : ℝ)) := Real.log_le_log (by positivity) hs_le
        _ = Real.log 2 + Real.log (Real.sqrt (X : ℝ)) :=
              Real.log_mul (by norm_num) (Real.sqrt_pos.mpr hXpos).ne'
        _ = Real.log 2 + (1 / 2 : ℝ) * Real.log (X : ℝ) := by
              rw [Real.log_sqrt hXpos.le]; ring
    have hlog2 : 6 * Real.log 2 ≤ Real.log (X : ℝ) := by
      have h64 : (2 : ℝ) ^ 6 ≤ (X : ℝ) := by
        have : 64 ≤ X := by omega
        have : (64 : ℝ) ≤ X := by exact_mod_cast this
        linarith
      calc 6 * Real.log 2 = Real.log ((2 : ℝ) ^ 6) := by rw [Real.log_pow]; ring
        _ ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) h64
    linarith
  · have hsub : Finset.Icc (Nat.sqrt X + 1) X ⊆ Finset.Icc 2 X := by
      intro n hn
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
      have hs1 : 1 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by omega)
      exact Finset.mem_Icc.mpr ⟨by omega, h2⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans
      (sum_inv_Icc_two_le_log X)

lemma van_der_corput_pretentious
    (h1 : ∀ (h₁ h₂ : ℕ), h₁ ≠ h₂ → ∀ ε : ℝ, 0 < ε →
      ∃ A : ℝ, 1 ≤ A ∧ ∀ X : ℕ, A ≤ (X : ℝ) → ∀ z : ℕ → Metric.sphere (0 : ℂ) 1,
        let g : ℕ → ℂ := fun n =>
          if n = 0 then 0 else n.factorization.prod fun p a => (z p).1 ^ a
        ε * Real.log (X : ℝ) <
          ‖∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, g (n + h₁) * star (g (n + h₂)) / (n : ℂ)‖ →
        ∃ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
          1 ≤ q ∧ (q : ℝ) ≤ A ∧ |t| ≤ A * (X : ℝ) ∧
          ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
            (1 - (g p * star (χ (p : ZMod q)) *
              Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) ≤ A)
    (μ : ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1)) (B : ℝ) (hB : 0 ≤ B)
    (hL2 : ∀ n : ℕ,
      ∫ z, ‖∑ k ∈ Finset.Icc 1 n,
        (if k = 0 then (0 : ℂ) else k.factorization.prod fun p a => (z p).1 ^ a)‖ ^ 2
        ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) ≤ B) :
    ∀ ε : ℝ, 0 < ε → ∃ Q : ℝ, 1 ≤ Q ∧ ∀ X : ℕ, Q ≤ (X : ℝ) →
      (μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) {z : ℕ → Metric.sphere (0 : ℂ) 1 |
        ¬ ∃ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
            1 ≤ q ∧ (q : ℝ) ≤ Q ∧ |t| ≤ Q * (X : ℝ) ∧
            ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
              (1 - ((if p = 0 then (0 : ℂ) else p.factorization.prod fun q_1 a => (z q_1).1 ^ a) *
                star (χ (p : ZMod q)) *
                Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) ≤ Q} ≤
        ENNReal.ofReal ε := by
  intro ε hε
  let g : (ℕ → Metric.sphere (0 : ℂ) 1) → ℕ → ℂ := fun z n =>
    if n = 0 then 0 else n.factorization.prod fun p a => (z p).1 ^ a
  let H : ℕ := Nat.ceil (16 * (B + 1) / ε) + 4
  have hH4 : 4 ≤ H := by dsimp [H]; omega
  have hH_big : 16 * (B + 1) / ε + 3 ≤ (H : ℝ) := by
    have := Nat.le_ceil (16 * (B + 1) / ε)
    dsimp [H]; push_cast; linarith
  let Pairs : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 H ×ˢ Finset.Icc 1 H).filter fun p => p.1 ≠ p.2
  have hPairs_card : Pairs.card ≤ H ^ 2 := by
    calc Pairs.card ≤ (Finset.Icc 1 H ×ˢ Finset.Icc 1 H).card := Finset.card_filter_le _ _
      _ = H ^ 2 := by simp [sq]
  have hA_ex : ∀ p : ℕ × ℕ, ∃ A : ℝ, 1 ≤ A ∧
      (p.1 ≠ p.2 → ∀ X : ℕ, A ≤ (X : ℝ) → ∀ z : ℕ → Metric.sphere (0 : ℂ) 1,
        (1 / (2 * (H : ℝ) ^ 2)) * Real.log (X : ℝ) <
          ‖∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)‖ →
        ∃ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
          1 ≤ q ∧ (q : ℝ) ≤ A ∧ |t| ≤ A * (X : ℝ) ∧
          ∑ pr ∈ (Finset.Icc 1 X).filter Nat.Prime,
            (1 - (g z pr * star (χ (pr : ZMod q)) *
              Complex.exp (-Complex.I * t * Real.log (pr : ℝ))).re) / (pr : ℝ) ≤ A) := by
    intro p
    by_cases hne : p.1 ≠ p.2
    · obtain ⟨A, hA1, hA⟩ := h1 p.1 p.2 hne (1 / (2 * (H : ℝ) ^ 2)) (by positivity)
      exact ⟨A, hA1, fun _ => hA⟩
    · exact ⟨1, le_rfl, fun h => absurd h hne⟩
  choose Afn hAfn_ge1 hAfn using hA_ex
  let Q : ℝ := max 100 (∑ p ∈ Pairs, Afn p) + 1
  have hQ_ge1 : 1 ≤ Q := by
    have : (100 : ℝ) ≤ max 100 (∑ p ∈ Pairs, Afn p) := le_max_left _ _
    dsimp [Q]; linarith
  refine ⟨Q, hQ_ge1, fun X hXQ => ?_⟩
  have hX100 : 100 ≤ X := by
    have : (100 : ℝ) ≤ Q := by dsimp [Q]; linarith [le_max_left (100 : ℝ) (∑ p ∈ Pairs, Afn p)]
    have : (100 : ℝ) ≤ X := this.trans hXQ
    exact_mod_cast this
  have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have ⟨hinv_lo, hinv_hi⟩ := sum_inv_sqrt_bounds hX100
  let G : (ℕ → Metric.sphere (0 : ℂ) 1) → ℝ := fun z =>
    ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
      (1 / (n : ℝ)) * ‖∑ h ∈ Finset.Icc 1 H, g z (n + h)‖ ^ 2
  have hG_cont : Continuous G := by
    refine continuous_finsetSum _ fun n _ => continuous_const.mul ?_
    exact ((continuous_finsetSum _ fun h _ => mulEval_continuous (n + h)).norm).pow 2
  have hG_nn : ∀ z, 0 ≤ G z := fun z =>
    Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (sq_nonneg _)
  have hG_int : Integrable G (μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) :=
    hG_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace G)
  have hG_mean : ∫ z, G z ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) ≤ 4 * (B + 1) * Real.log (X : ℝ) := by
    have hterm_int : ∀ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
        Integrable (fun z => (1 / (n : ℝ)) * ‖∑ h ∈ Finset.Icc 1 H, g z (n + h)‖ ^ 2)
          (μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) := fun n _ =>
      (continuous_const.mul (((continuous_finsetSum _ fun h _ =>
        mulEval_continuous (n + h)).norm).pow 2)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    have hterm_le : ∀ n : ℕ,
        ∫ z, ‖∑ h ∈ Finset.Icc 1 H, g z (n + h)‖ ^ 2 ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) ≤ 4 * B := by
      intro n
      have hpw : ∀ z : ℕ → Metric.sphere (0 : ℂ) 1,
          ‖∑ h ∈ Finset.Icc 1 H, g z (n + h)‖ ^ 2 ≤
            2 * ‖∑ k ∈ Finset.Icc 1 (n + H), g z k‖ ^ 2 + 2 * ‖∑ k ∈ Finset.Icc 1 n, g z k‖ ^ 2 := by
        intro z
        have hdiff : ∑ h ∈ Finset.Icc 1 H, g z (n + h) =
            (∑ k ∈ Finset.Icc 1 (n + H), g z k) - (∑ k ∈ Finset.Icc 1 n, g z k) := by
          have hunion : Finset.Icc 1 (n + H) = Finset.Icc 1 n ∪ Finset.Icc (n + 1) (n + H) := by
            ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
          have hdisj : Disjoint (Finset.Icc 1 n) (Finset.Icc (n + 1) (n + H)) := by
            rw [Finset.disjoint_left]; intro k hk1 hk2
            simp only [Finset.mem_Icc] at hk1 hk2; omega
          have hshift : ∑ k ∈ Finset.Icc (n + 1) (n + H), g z k =
              ∑ h ∈ Finset.Icc 1 H, g z (n + h) := by
            refine Finset.sum_bij (fun k _ => k - n) ?_ ?_ ?_ ?_
            · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
            · intro k₁ hk₁ k₂ hk₂ h; simp only [Finset.mem_Icc] at hk₁ hk₂; omega
            · intro h hh; refine ⟨n + h, ?_, by omega⟩
              simp only [Finset.mem_Icc] at hh ⊢; omega
            · intro k hk; simp only [Finset.mem_Icc] at hk
              congr 1; omega
          rw [hunion, Finset.sum_union hdisj, hshift, add_sub_cancel_left]
        rw [hdiff]
        have htri : ‖(∑ k ∈ Finset.Icc 1 (n + H), g z k) - ∑ k ∈ Finset.Icc 1 n, g z k‖ ≤
            ‖∑ k ∈ Finset.Icc 1 (n + H), g z k‖ + ‖∑ k ∈ Finset.Icc 1 n, g z k‖ :=
          norm_sub_le _ _
        have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
        nlinarith [sq_nonneg (‖∑ k ∈ Finset.Icc 1 (n + H), g z k‖ - ‖∑ k ∈ Finset.Icc 1 n, g z k‖)]
      have hint1 : Integrable (fun z => ‖∑ h ∈ Finset.Icc 1 H, g z (n + h)‖ ^ 2)
          (μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) :=
        (((continuous_finsetSum _ fun h _ => mulEval_continuous (n + h)).norm).pow 2).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hint2 : Integrable (fun z => 2 * ‖∑ k ∈ Finset.Icc 1 (n + H), g z k‖ ^ 2)
          (μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) :=
        ((energy_continuous (n + H)).const_mul 2).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hint3 : Integrable (fun z => 2 * ‖∑ k ∈ Finset.Icc 1 n, g z k‖ ^ 2)
          (μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) :=
        ((energy_continuous n).const_mul 2).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      calc
        ∫ z, ‖∑ h ∈ Finset.Icc 1 H, g z (n + h)‖ ^ 2 ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1))
            ≤ ∫ z, (2 * ‖∑ k ∈ Finset.Icc 1 (n + H), g z k‖ ^ 2 +
                2 * ‖∑ k ∈ Finset.Icc 1 n, g z k‖ ^ 2) ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) :=
              integral_mono hint1 (hint2.add hint3) hpw
        _ = 2 * (∫ z, ‖∑ k ∈ Finset.Icc 1 (n + H), g z k‖ ^ 2 ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1))) +
            2 * (∫ z, ‖∑ k ∈ Finset.Icc 1 n, g z k‖ ^ 2 ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1))) := by
              rw [integral_add hint2 hint3, integral_const_mul, integral_const_mul]
        _ ≤ 4 * B := by linarith [hL2 (n + H), hL2 n]
    calc
      ∫ z, G z ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1))
          = ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
              ∫ z, (1 / (n : ℝ)) * ‖∑ h ∈ Finset.Icc 1 H, g z (n + h)‖ ^ 2
                ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) :=
            integral_finsetSum _ hterm_int
      _ = ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
              (1 / (n : ℝ)) * ∫ z, ‖∑ h ∈ Finset.Icc 1 H, g z (n + h)‖ ^ 2
                ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) :=
            Finset.sum_congr rfl fun n _ => integral_const_mul _ _
      _ ≤ ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ)) * (4 * B) :=
            Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hterm_le n) (by positivity)
      _ = (4 * B) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ)) := by
            rw [← Finset.sum_mul, mul_comm]
      _ ≤ (4 * B) * Real.log (X : ℝ) := mul_le_mul_of_nonneg_left hinv_hi (by positivity)
      _ ≤ 4 * (B + 1) * Real.log (X : ℝ) := by nlinarith
  let T : ℝ := (4 * (B + 1) / ε) * Real.log (X : ℝ)
  have hT_pos : 0 < T := by positivity
  have hmarkov : (μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) {z | T ≤ G z} ≤ ENNReal.ofReal ε := by
    have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hG_nn) hG_int T
    rw [measureReal_def] at hm
    have h1 : T * ((μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) {z | T ≤ G z}).toReal ≤ 4 * (B + 1) * Real.log (X : ℝ) :=
      hm.trans hG_mean
    have h2 : ((μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) {z | T ≤ G z}).toReal ≤ ε := by
      have hmul : T * ε = 4 * (B + 1) * Real.log (X : ℝ) := by dsimp [T]; field_simp [hε.ne']
      nlinarith
    have hfin : (μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) {z | T ≤ G z} ≠ ⊤ := measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal h2
  refine (measure_mono ?_).trans hmarkov
  intro z hz
  change T ≤ G z
  by_contra hlt
  push Not at hlt
  have hexpand : G z = (H : ℝ) * (∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ))) +
      (∑ p ∈ Pairs, ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
        g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)).re := by
    have hpoint : ∀ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
        (1 / (n : ℝ)) * ‖∑ h ∈ Finset.Icc 1 H, g z (n + h)‖ ^ 2 =
          (H : ℝ) * (1 / (n : ℝ)) +
          (∑ p ∈ Pairs, g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)).re := by
      intro n hn
      have hnorm : ((‖∑ h ∈ Finset.Icc 1 H, g z (n + h)‖ ^ 2 : ℝ) : ℂ) =
          (H : ℂ) + ∑ p ∈ Pairs, g z (n + p.1) * star (g z (n + p.2)) := by
        have hsq : ∀ w : ℂ, ((‖w‖ ^ 2 : ℝ) : ℂ) = w * star w := fun w => by
          rw [Complex.ofReal_pow, Complex.star_def, Complex.mul_conj']
        rw [hsq, Complex.star_def, map_sum, Finset.sum_mul]
        simp_rw [← Complex.star_def, Finset.mul_sum]
        rw [← Finset.sum_product']
        let Diag : Finset (ℕ × ℕ) :=
          (Finset.Icc 1 H ×ˢ Finset.Icc 1 H).filter fun p => p.1 = p.2
        have hpart : Finset.Icc 1 H ×ˢ Finset.Icc 1 H = Diag ∪ Pairs := by
          ext p; simp only [Diag, Pairs, Finset.mem_union, Finset.mem_filter]
          constructor
          · intro hp; rcases eq_or_ne p.1 p.2 with h | h
            · exact Or.inl ⟨hp, h⟩
            · exact Or.inr ⟨hp, h⟩
          · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
        have hdisj : Disjoint Diag Pairs :=
          Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
        rw [hpart, Finset.sum_union hdisj]
        congr 1
        have hdiag_eq : ∑ p ∈ Diag, g z (n + p.1) * star (g z (n + p.2)) =
            ∑ h ∈ Finset.Icc 1 H, (1 : ℂ) := by
          refine Finset.sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
          · intro p hp; exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
          · intro p₁ hp₁ p₂ hp₂ h
            have h1 := (Finset.mem_filter.mp hp₁).2
            have h2 := (Finset.mem_filter.mp hp₂).2
            ext <;> omega
          · intro h hh
            refine ⟨(h, h), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hh, hh⟩, rfl⟩, rfl⟩
          · intro p hp
            have heq := (Finset.mem_filter.mp hp).2
            have hp1 : 1 ≤ p.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1).1
            rw [← heq, Complex.star_def, Complex.mul_conj', mulEval_norm z (by omega)]
            simp
        rw [hdiag_eq]; simp
      have hre := congrArg Complex.re hnorm
      simp only [Complex.ofReal_re, Complex.add_re, Complex.natCast_re] at hre
      have hdiv : (∑ p ∈ Pairs, g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)).re =
          (1 / (n : ℝ)) * (∑ p ∈ Pairs, g z (n + p.1) * star (g z (n + p.2))).re := by
        rw [← Finset.sum_div, div_eq_mul_inv]
        have hinv : ((n : ℂ)⁻¹) = (((n : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
        rw [hinv, mul_comm, Complex.re_ofReal_mul]
        ring
      rw [hdiv, hre]; ring
    calc
      G z = ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
              ((H : ℝ) * (1 / (n : ℝ)) +
                (∑ p ∈ Pairs, g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)).re) :=
            Finset.sum_congr rfl hpoint
      _ = (H : ℝ) * (∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ))) +
            (∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
              ∑ p ∈ Pairs, g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)).re := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Complex.re_sum]
      _ = (H : ℝ) * (∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ))) +
            (∑ p ∈ Pairs, ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
              g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)).re := by
            rw [Finset.sum_comm]
  have hdiag_gt : T + Real.log (X : ℝ) ≤ (H : ℝ) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ)) := by
    have h1 : (4 * (B + 1) / ε + 1) * Real.log (X : ℝ) ≤ (H : ℝ) * ((1 / 3 : ℝ) * Real.log (X : ℝ)) := by
      have : 4 * (B + 1) / ε + 1 ≤ (H : ℝ) * (1 / 3 : ℝ) := by
        have hpos : 0 ≤ (B + 1) / ε := by positivity
        have hHb : 16 * ((B + 1) / ε) + 3 ≤ (H : ℝ) := by simpa [mul_div_assoc] using hH_big
        have hgoal : 4 * ((B + 1) / ε) + 1 ≤ (H : ℝ) * (1 / 3 : ℝ) := by linarith
        simpa [mul_div_assoc] using hgoal
      nlinarith
    have h2 : (H : ℝ) * ((1 / 3 : ℝ) * Real.log (X : ℝ)) ≤
        (H : ℝ) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hinv_lo (by positivity)
    dsimp [T]; linarith
  have hoff_gt : Real.log (X : ℝ) <
      ∑ p ∈ Pairs, ‖∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
        g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)‖ := by
    have hre_le : -(∑ p ∈ Pairs, ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
        g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)).re ≤
        ∑ p ∈ Pairs, ‖∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
          g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)‖ := by
      calc
        -(∑ p ∈ Pairs, ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
            g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)).re
            ≤ ‖∑ p ∈ Pairs, ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
                g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)‖ :=
              (neg_le_abs _).trans (Complex.abs_re_le_norm _)
        _ ≤ ∑ p ∈ Pairs, ‖∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
              g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)‖ := norm_sum_le _ _
    linarith
  have hex_pair : ∃ p ∈ Pairs,
      (1 / (2 * (H : ℝ) ^ 2)) * Real.log (X : ℝ) <
        ‖∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
          g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)‖ := by
    by_contra hno
    push Not at hno
    have hsum_le : ∑ p ∈ Pairs, ‖∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
        g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)‖ ≤
        (Pairs.card : ℝ) * ((1 / (2 * (H : ℝ) ^ 2)) * Real.log (X : ℝ)) := by
      calc
        _ ≤ ∑ _ ∈ Pairs, ((1 / (2 * (H : ℝ) ^ 2)) * Real.log (X : ℝ)) :=
              Finset.sum_le_sum hno
        _ = (Pairs.card : ℝ) * ((1 / (2 * (H : ℝ) ^ 2)) * Real.log (X : ℝ)) := by simp
    have hle_half : (Pairs.card : ℝ) * ((1 / (2 * (H : ℝ) ^ 2)) * Real.log (X : ℝ)) ≤
        (1 / 2 : ℝ) * Real.log (X : ℝ) := by
      have hP : (Pairs.card : ℝ) ≤ (H : ℝ) ^ 2 := by exact_mod_cast hPairs_card
      have hH2_pos : (0 : ℝ) < (H : ℝ) ^ 2 := by positivity
      calc
        (Pairs.card : ℝ) * ((1 / (2 * (H : ℝ) ^ 2)) * Real.log (X : ℝ))
            ≤ (H : ℝ) ^ 2 * ((1 / (2 * (H : ℝ) ^ 2)) * Real.log (X : ℝ)) :=
              mul_le_mul_of_nonneg_right hP (by positivity)
        _ = (1 / 2 : ℝ) * Real.log (X : ℝ) := by field_simp [hH2_pos.ne']
    linarith
  obtain ⟨p, hpPairs, hp_gt⟩ := hex_pair
  have hp_ne : p.1 ≠ p.2 := (Finset.mem_filter.mp hpPairs).2
  have hA_le_Q : Afn p ≤ Q := by
    have h1 : Afn p ≤ ∑ q ∈ Pairs, Afn q :=
      Finset.single_le_sum (fun q _ => le_trans zero_le_one (hAfn_ge1 q)) hpPairs
    have h2 : ∑ q ∈ Pairs, Afn q ≤ max 100 (∑ q ∈ Pairs, Afn q) := le_max_right _ _
    dsimp [Q]; linarith
  obtain ⟨q, χ, t, hq1, hqA, htA, hdist⟩ := hAfn p hp_ne X (hA_le_Q.trans hXQ) z hp_gt
  apply hz
  refine ⟨q, χ, t, hq1, hqA.trans hA_le_Q, ?_, hdist.trans hA_le_Q⟩
  exact htA.trans (mul_le_mul_of_nonneg_right hA_le_Q (Nat.cast_nonneg X))

/- ### Hypotheses and main reduction theorem -/

/-- Tao's logarithmically averaged nonasymptotic two-point Elliott conjecture (Tao 2016, Theorem 1.5)
specialized to $S^1$-valued completely multiplicative functions on $(\sqrt{X}, X]$. -/
def H1 : Prop :=
  ∀ (h₁ h₂ : ℕ), h₁ ≠ h₂ → ∀ ε : ℝ, 0 < ε →
    ∃ A : ℝ, 1 ≤ A ∧ ∀ X : ℕ, A ≤ (X : ℝ) → ∀ z : ℕ → Metric.sphere (0 : ℂ) 1,
      let g : ℕ → ℂ := fun n =>
        if n = 0 then 0 else n.factorization.prod fun p a => (z p).1 ^ a
      ε * Real.log (X : ℝ) <
        ‖∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, g (n + h₁) * star (g (n + h₂)) / (n : ℂ)‖ →
      ∃ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
        1 ≤ q ∧ (q : ℝ) ≤ A ∧ |t| ≤ A * (X : ℝ) ∧
        ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
          (1 - (g p * star (χ (p : ZMod q)) *
            Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) ≤ A

/-- Tao's generalized Borwein–Choi–Coons theorem (Tao 2016, Section 4): no probability distribution
over $S^1$-valued completely multiplicative functions with uniformly bounded $L^2$ partial sums
can be pretentious with probability $1 - \varepsilon$ for all $\varepsilon > 0$ and large $X$. -/
def H2 : Prop :=
  let mulEval : (ℕ → Metric.sphere (0 : ℂ) 1) → ℕ → ℂ := fun z n =>
    if n = 0 then 0 else n.factorization.prod fun p a => (z p).1 ^ a
  ∀ (μ : MeasureTheory.ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1)) (B : ℝ), 0 ≤ B →
    (∀ n : ℕ, ∫ z, ‖∑ k ∈ Finset.Icc 1 n, mulEval z k‖ ^ 2
      ∂(μ : MeasureTheory.Measure (ℕ → Metric.sphere (0 : ℂ) 1)) ≤ B) →
    (∀ ε : ℝ, 0 < ε → ∃ Q : ℝ, 1 ≤ Q ∧ ∀ X : ℕ, Q ≤ (X : ℝ) →
      (μ : MeasureTheory.Measure (ℕ → Metric.sphere (0 : ℂ) 1)) {z : ℕ → Metric.sphere (0 : ℂ) 1 |
        ¬ ∃ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
            1 ≤ q ∧ (q : ℝ) ≤ Q ∧ |t| ≤ Q * (X : ℝ) ∧
            ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
              (1 - (mulEval z p * star (χ (p : ZMod q)) *
                Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) ≤ Q} ≤
        ENNReal.ofReal ε) →
    False

theorem main : H1 → H2 → type_of% @Erdos67.erdos_67 := by
  intro h1 h2 f C hC
  by_contra hno
  push Not at hno
  have hbd : ∀ d ≥ 1, ∀ m ≥ 1, |∑ k ∈ Finset.Icc 1 m, (f (k * d)).1| ≤ C := hno
  obtain ⟨μ, hμ⟩ := exists_global_prob_measure f C hC.le hbd
  have hpret := van_der_corput_pretentious h1 μ (C ^ 2 + 1) (by positivity) hμ
  exact h2 μ (C ^ 2 + 1) (by positivity) hμ hpret

end OMA.R_Erdos67_erdos_67_R1
