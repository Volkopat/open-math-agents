import OMAStatements.S_oeis_a253974

open Complex Real Finset
open scoped BigOperators

namespace A253974

noncomputable def phi (r s : ℕ) (x y : ℝ) : ℝ :=
  (Real.cos ((r : ℝ) * x) * Real.cos ((s : ℝ) * y) +
    Real.cos ((s : ℝ) * x) * Real.cos ((r : ℝ) * y)) / 2

def moveOf (r s : ℕ) : Fin 8 → ℤ × ℤ
  | 0 => ((r : ℤ), (s : ℤ))
  | 1 => ((r : ℤ), -(s : ℤ))
  | 2 => (-(r : ℤ), (s : ℤ))
  | 3 => (-(r : ℤ), -(s : ℤ))
  | 4 => ((s : ℤ), (r : ℤ))
  | 5 => ((s : ℤ), -(r : ℤ))
  | 6 => (-(s : ℤ), (r : ℤ))
  | 7 => (-(s : ℤ), -(r : ℤ))

lemma moveOf_injective {r s : ℕ} (hr : 0 < r) (hrs : r < s) :
    Function.Injective (moveOf r s) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp only [moveOf, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; omega)

lemma two_cos (θ : ℝ) :
    exp (I * θ) + exp (I * -θ) = 2 * (Real.cos θ : ℂ) := by
  have hcos : 2 * cos (θ : ℂ) = exp (↑θ * I) + exp (-(↑θ * I)) := by
    simp [Complex.cos, div_eq_mul_inv, mul_left_comm, mul_comm]
  have h1 : exp (I * θ) = exp (↑θ * I) := by ring_nf
  have h2 : exp (I * -θ) = exp (-(↑θ * I)) := by
    rw [show (I * (-θ : ℂ)) = -(↑θ * I) by ring]
  rw [h1, h2, ← hcos, Complex.ofReal_cos]

lemma four_cos (α β : ℝ) :
    exp (I * (α + β)) + exp (I * (α - β)) + exp (I * (-α + β)) + exp (I * (-α - β)) =
      4 * (Real.cos α : ℂ) * Real.cos β := by
  have h14 : exp (I * (α + β)) + exp (I * (-α - β)) = 2 * (Real.cos (α + β) : ℂ) := by
    have : I * (-α - β : ℂ) = I * -(α + β : ℂ) := by ring
    simpa [this] using two_cos (α + β)
  have h23 : exp (I * (α - β)) + exp (I * (-α + β)) = 2 * (Real.cos (α - β) : ℂ) := by
    have : I * (-α + β : ℂ) = I * -(α - β : ℂ) := by ring
    simpa [this] using two_cos (α - β)
  calc
      exp (I * (α + β)) + exp (I * (α - β)) + exp (I * (-α + β)) + exp (I * (-α - β))
        = (exp (I * (α + β)) + exp (I * (-α - β))) +
            (exp (I * (α - β)) + exp (I * (-α + β))) := by ring
      _ = 2 * (Real.cos (α + β) : ℂ) + 2 * (Real.cos (α - β) : ℂ) := by rw [h14, h23]
      _ = 4 * (Real.cos α : ℂ) * Real.cos β := by
        have hreal :
            2 * Real.cos (α + β) + 2 * Real.cos (α - β) = 4 * Real.cos α * Real.cos β := by
          rw [Real.cos_add, Real.cos_sub]; ring
        exact_mod_cast hreal

lemma four_cast (a b : ℕ) (x y : ℝ) :
    exp (I * ((a : ℂ) * x + (b : ℂ) * y)) + exp (I * ((a : ℂ) * x + (-b : ℂ) * y)) +
        exp (I * ((-a : ℂ) * x + (b : ℂ) * y)) + exp (I * ((-a : ℂ) * x + (-b : ℂ) * y)) =
      4 * (Real.cos ((a : ℝ) * x) : ℂ) * Real.cos ((b : ℝ) * y) := by
  refine Eq.trans ?_ (four_cos ((a : ℝ) * x) ((b : ℝ) * y))
  congr 1
  · congr 1
    · congr 1
      · first | rfl | (congr 1; push_cast; ring)
      · first | rfl | (congr 1; push_cast; ring)
    · first | rfl | (congr 1; push_cast; ring)
  · first | rfl | (congr 1; push_cast; ring)

lemma sum_eight (f : Fin 8 → ℂ) :
    ∑ i : Fin 8, f i =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  simp [Fin.sum_univ_succ]
  abel

lemma exp_nat_nat (a b : ℕ) (x y : ℝ) :
    exp (I * (((a : ℤ) : ℂ) * x + ((b : ℤ) : ℂ) * y)) =
      exp (I * (((a : ℝ) * x + (b : ℝ) * y : ℝ) : ℂ)) := by
  congr 1
  push_cast
  ring

lemma exp_nat_neg (a b : ℕ) (x y : ℝ) :
    exp (I * (((a : ℤ) : ℂ) * x + ((-(b : ℤ)) : ℂ) * y)) =
      exp (I * (((a : ℝ) * x + -((b : ℝ) * y) : ℝ) : ℂ)) := by
  congr 1
  push_cast
  ring

lemma exp_neg_nat (a b : ℕ) (x y : ℝ) :
    exp (I * (((-(a : ℤ)) : ℂ) * x + ((b : ℤ) : ℂ) * y)) =
      exp (I * ((-((a : ℝ) * x) + (b : ℝ) * y : ℝ) : ℂ)) := by
  congr 1
  push_cast
  ring

lemma exp_neg_neg (a b : ℕ) (x y : ℝ) :
    exp (I * (((-(a : ℤ)) : ℂ) * x + ((-(b : ℤ)) : ℂ) * y)) =
      exp (I * ((-((a : ℝ) * x) + -((b : ℝ) * y) : ℝ) : ℂ)) := by
  congr 1
  push_cast
  ring

lemma sum_cexp_moves {r s : ℕ} (hr : 0 < r) (hrs : r < s) (x y : ℝ) :
    ∑ v ∈ OMA.S_oeis_a253974.moves r s,
        exp (I * ((v.1 : ℂ) * x + (v.2 : ℂ) * y)) =
      8 * (phi r s x y : ℂ) := by
  have himg : OMA.S_oeis_a253974.moves r s = univ.image (moveOf r s) := by
    ext v
    constructor
    · intro hv
      simp only [OMA.S_oeis_a253974.moves, mem_insert, mem_singleton] at hv
      simp only [mem_image, mem_univ, true_and]
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
      · exact ⟨6, rfl⟩
      · exact ⟨7, rfl⟩
    · intro hv
      simp only [mem_image, mem_univ, true_and] at hv
      rcases hv with ⟨i, rfl⟩
      fin_cases i <;> simp [moveOf, OMA.S_oeis_a253974.moves]
  rw [himg, sum_image ((moveOf_injective hr hrs).injOn), sum_eight]
  simp only [moveOf]
  push_cast
  have hA := four_cast r s x y
  have hB := four_cast s r x y
  have hreal :
      4 * Real.cos ((r : ℝ) * x) * Real.cos ((s : ℝ) * y) +
        4 * Real.cos ((s : ℝ) * x) * Real.cos ((r : ℝ) * y) =
        8 * phi r s x y := by
    simp only [phi]; ring
  calc
    exp (I * ((r : ℂ) * x + (s : ℂ) * y)) + exp (I * ((r : ℂ) * x + (-s : ℂ) * y)) +
        exp (I * ((-r : ℂ) * x + (s : ℂ) * y)) + exp (I * ((-r : ℂ) * x + (-s : ℂ) * y)) +
        exp (I * ((s : ℂ) * x + (r : ℂ) * y)) + exp (I * ((s : ℂ) * x + (-r : ℂ) * y)) +
        exp (I * ((-s : ℂ) * x + (r : ℂ) * y)) + exp (I * ((-s : ℂ) * x + (-r : ℂ) * y))
      = (exp (I * ((r : ℂ) * x + (s : ℂ) * y)) + exp (I * ((r : ℂ) * x + (-s : ℂ) * y)) +
          exp (I * ((-r : ℂ) * x + (s : ℂ) * y)) + exp (I * ((-r : ℂ) * x + (-s : ℂ) * y))) +
        (exp (I * ((s : ℂ) * x + (r : ℂ) * y)) + exp (I * ((s : ℂ) * x + (-r : ℂ) * y)) +
          exp (I * ((-s : ℂ) * x + (r : ℂ) * y)) + exp (I * ((-s : ℂ) * x + (-r : ℂ) * y))) := by
      abel
    _ = 4 * (Real.cos ((r : ℝ) * x) : ℂ) * Real.cos ((s : ℝ) * y) +
          4 * (Real.cos ((s : ℝ) * x) : ℂ) * Real.cos ((r : ℝ) * y) := by
      rw [hA, hB]
    _ = 8 * (phi r s x y : ℂ) := by exact_mod_cast hreal

open intervalIntegral MeasureTheory

lemma prod_fst_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℤ × ℤ) :
    (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

lemma prod_snd_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℤ × ℤ) :
    (∑ i ∈ s, f i).2 = ∑ i ∈ s, (f i).2 := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

lemma exp_two_pi_mul_I (k : ℤ) : exp ((k : ℂ) * (2 * π * I)) = 1 := by
  have h2 : exp (↑(2 * π) * I) = 1 := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_two_pi,
      Real.sin_two_pi]
    simp
  have hcoe : (2 * π * I : ℂ) = ↑(2 * π) * I := by
    have hnum : (2 : ℂ) * π = ↑(2 * π) := by
      rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul]
    rw [hnum]
  rw [Complex.exp_int_mul, hcoe, h2, one_zpow]

lemma integral_cexp_lattice (k : ℤ) :
    ∫ x in (0 : ℝ)..(2 * π), exp (I * (k : ℂ) * x) =
      if k = 0 then (2 * π : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp [intervalIntegral.integral_const, Algebra.smul_def]
  · have hc : I * (k : ℂ) ≠ 0 := by
      intro h
      apply hk
      have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
      have hk0 : (k : ℂ) = 0 := by
        exact (mul_eq_zero.mp h).resolve_left hI
      exact_mod_cast hk0
    rw [if_neg hk, integral_exp_mul_complex hc]
    have hper : exp ((I * (k : ℂ)) * ↑(2 * π)) = 1 := by
      have harg : (I * (k : ℂ)) * ↑(2 * π) = (k : ℂ) * (2 * π * I) := by
        push_cast
        ring
      rw [harg]
      exact exp_two_pi_mul_I k
    rw [hper]
    simp

lemma exp_split (a b : ℤ) (x y : ℝ) :
    exp (I * ((a : ℂ) * x + (b : ℂ) * y)) =
      exp (I * (a : ℂ) * x) * exp (I * (b : ℂ) * y) := by
  rw [← Complex.exp_add]
  congr 1
  ring

lemma integral_cexp_box (a b : ℤ) :
    ∫ x in (0 : ℝ)..(2 * π), ∫ y in (0 : ℝ)..(2 * π),
        exp (I * ((a : ℂ) * x + (b : ℂ) * y)) =
      if a = 0 ∧ b = 0 then (4 * π ^ 2 : ℂ) else 0 := by
  simp_rw [exp_split, intervalIntegral.integral_const_mul]
  rw [integral_cexp_lattice b]
  by_cases hb : b = 0
  · rw [if_pos hb, intervalIntegral.integral_mul_const, integral_cexp_lattice]
    by_cases ha : a = 0
    · rw [if_pos ha, if_pos (And.intro ha hb)]
      ring_nf
    · rw [if_neg ha, if_neg (fun h => ha h.1)]
      simp
  · rw [if_neg hb, if_neg (fun h => hb h.2)]
    simp

lemma indicator_eq_box (z : ℤ × ℤ) :
    (if z = 0 then (1 : ℂ) else 0) =
      (1 / (4 * π ^ 2)) *
        ∫ x in (0 : ℝ)..(2 * π), ∫ y in (0 : ℝ)..(2 * π),
          exp (I * ((z.1 : ℂ) * x + (z.2 : ℂ) * y)) := by
  rw [integral_cexp_box]
  by_cases hz : z = 0
  · simp [hz]
    field_simp
  · have hcoord : ¬ (z.1 = 0 ∧ z.2 = 0) := by
      rintro ⟨h1, h2⟩
      apply hz
      exact Prod.ext h1 h2
    simp [hz, hcoord]

lemma char_prod {n : ℕ} (f : Fin (2 * n) → ℤ × ℤ) (x y : ℝ) :
    exp (I * (((∑ i, f i).1 : ℂ) * x + ((∑ i, f i).2 : ℂ) * y)) =
      ∏ i, exp (I * (((f i).1 : ℂ) * x + ((f i).2 : ℂ) * y)) := by
  have hf1 : ((∑ i, f i).1 : ℂ) = ∑ i, ((f i).1 : ℂ) := by
    rw [prod_fst_sum]
    simp
  have hf2 : ((∑ i, f i).2 : ℂ) = ∑ i, ((f i).2 : ℂ) := by
    rw [prod_snd_sum]
    simp
  rw [hf1, hf2, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum,
    Complex.exp_sum]

lemma closedPaths_complex {r s n : ℕ} :
    (OMA.S_oeis_a253974.closedPaths r s n : ℂ) =
      (1 / (4 * π ^ 2)) *
        ∫ x in (0 : ℝ)..(2 * π), ∫ y in (0 : ℝ)..(2 * π),
          (∑ v ∈ OMA.S_oeis_a253974.moves r s,
            exp (I * ((v.1 : ℂ) * x + (v.2 : ℂ) * y))) ^ (2 * n) := by
  classical
  let paths := Fintype.piFinset fun _ : Fin (2 * n) => OMA.S_oeis_a253974.moves r s
  have hcard : (OMA.S_oeis_a253974.closedPaths r s n : ℂ) =
      ∑ f ∈ paths, if ∑ i, f i = 0 then (1 : ℂ) else 0 := by
    unfold OMA.S_oeis_a253974.closedPaths
    rw [Finset.natCast_card_filter]
  rw [hcard]
  have hsum :
      ∑ f ∈ paths, (if ∑ i, f i = 0 then (1 : ℂ) else 0) =
        (1 / (4 * π ^ 2)) *
          ∑ f ∈ paths,
            ∫ x in (0 : ℝ)..(2 * π), ∫ y in (0 : ℝ)..(2 * π),
              ∏ i, exp (I * (((f i).1 : ℂ) * x + ((f i).2 : ℂ) * y)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [indicator_eq_box (∑ i, f i)]
    refine congrArg (fun t : ℂ => ((1 : ℂ) / (4 * (π : ℂ) ^ 2)) * t) ?_
    refine intervalIntegral.integral_congr fun x _ => ?_
    refine intervalIntegral.integral_congr fun y _ => ?_
    exact char_prod f x y
  rw [hsum]
  congr 1
  let g : (Fin (2 * n) → ℤ × ℤ) → ℝ → ℝ → ℂ := fun f x y =>
    ∏ i, exp (I * (((f i).1 : ℂ) * x + ((f i).2 : ℂ) * y))
  have hcont : ∀ f, Continuous (Function.uncurry (g f)) := by
    intro f
    refine continuous_finsetProd Finset.univ fun i _ => ?_
    exact Complex.continuous_exp.comp (by fun_prop)
  have hinter : ∀ f x, IntervalIntegrable (g f x) volume 0 (2 * π) := by
    intro f x
    exact (hcont f).along_snd.intervalIntegrable 0 (2 * π)
  have houter : ∀ f, IntervalIntegrable
      (fun x => ∫ y in (0 : ℝ)..(2 * π), g f x y) volume 0 (2 * π) := by
    intro f
    apply Continuous.intervalIntegrable
    simpa [g, Function.uncurry] using
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (hcont f) 0 (2 * π)
  calc
    ∑ f ∈ paths, ∫ x in (0 : ℝ)..(2 * π), ∫ y in (0 : ℝ)..(2 * π), g f x y
      = ∫ x in (0 : ℝ)..(2 * π), ∑ f ∈ paths, ∫ y in (0 : ℝ)..(2 * π), g f x y := by
        rw [intervalIntegral.integral_finsetSum (fun f _ => houter f)]
    _ = ∫ x in (0 : ℝ)..(2 * π), ∫ y in (0 : ℝ)..(2 * π), ∑ f ∈ paths, g f x y := by
        refine intervalIntegral.integral_congr fun x _ => ?_
        rw [intervalIntegral.integral_finsetSum (fun f _ => hinter f x)]
    _ = ∫ x in (0 : ℝ)..(2 * π), ∫ y in (0 : ℝ)..(2 * π),
          (∑ v ∈ OMA.S_oeis_a253974.moves r s,
            exp (I * ((v.1 : ℂ) * x + (v.2 : ℂ) * y))) ^ (2 * n) := by
        refine intervalIntegral.integral_congr fun x _ => ?_
        refine intervalIntegral.integral_congr fun y _ => ?_
        symm
        simpa [g, paths] using
          (Finset.sum_pow' (OMA.S_oeis_a253974.moves r s)
            (fun v => exp (I * ((v.1 : ℂ) * x + (v.2 : ℂ) * y))) (2 * n))

lemma eight_pow (n : ℕ) : (8 : ℂ) ^ (2 * n) = ((64 : ℝ) ^ n : ℂ) := by
  rw [pow_mul]
  norm_num

lemma phi_pow (r s n : ℕ) (x y : ℝ) :
    ((8 : ℂ) * (phi r s x y : ℂ)) ^ (2 * n) =
      ((64 : ℝ) ^ n : ℂ) * ((phi r s x y ^ (2 * n) : ℝ) : ℂ) := by
  rw [mul_pow, ← Complex.ofReal_pow, eight_pow]

lemma closedPaths_real {r s n : ℕ} (hr : 0 < r) (hrs : r < s) :
    (OMA.S_oeis_a253974.closedPaths r s n : ℝ) =
      (64 : ℝ) ^ n / (4 * π ^ 2) *
        ∫ x in (0 : ℝ)..(2 * π), ∫ y in (0 : ℝ)..(2 * π), phi r s x y ^ (2 * n) := by
  have hC := closedPaths_complex (r := r) (s := s) (n := n)
  simp_rw [sum_cexp_moves hr hrs, phi_pow, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal] at hC
  have hreal :
      (OMA.S_oeis_a253974.closedPaths r s n : ℂ) =
        (((64 : ℝ) ^ n / (4 * π ^ 2) *
          ∫ x in (0 : ℝ)..(2 * π), ∫ y in (0 : ℝ)..(2 * π), phi r s x y ^ (2 * n) : ℝ) : ℂ) := by
    rw [hC]
    push_cast
    ring
  exact_mod_cast hreal

lemma abs_cos_mul_le_one (a b : ℝ) : |Real.cos a * Real.cos b| ≤ 1 := by
  rw [abs_mul]
  have h1 := Real.abs_cos_le_one a
  have h2 := Real.abs_cos_le_one b
  nlinarith [abs_nonneg (Real.cos a), abs_nonneg (Real.cos b)]

lemma abs_phi_le_one (r s : ℕ) (x y : ℝ) : |phi r s x y| ≤ 1 := by
  have hsum : |Real.cos ((r : ℝ) * x) * Real.cos ((s : ℝ) * y) +
      Real.cos ((s : ℝ) * x) * Real.cos ((r : ℝ) * y)| ≤ 2 := by
    calc
      _ ≤ |Real.cos ((r : ℝ) * x) * Real.cos ((s : ℝ) * y)| +
          |Real.cos ((s : ℝ) * x) * Real.cos ((r : ℝ) * y)| := abs_add_le _ _
      _ ≤ 1 + 1 := add_le_add (abs_cos_mul_le_one _ _) (abs_cos_mul_le_one _ _)
      _ = 2 := by norm_num
  simp only [phi]
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (div_le_one (by norm_num)).2 hsum

lemma abs_pair_eq_two {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hab : |a + b| = 2) :
    (a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1) := by
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 2)).1 hab with h | h
  · left
    have ha' := (abs_le.mp ha).2
    have hb' := (abs_le.mp hb).2
    exact ⟨by linarith, by linarith⟩
  · right
    have ha' := (abs_le.mp ha).1
    have hb' := (abs_le.mp hb).1
    exact ⟨by linarith, by linarith⟩

lemma phi_zero (r s : ℕ) : phi r s 0 0 = 1 := by
  simp [phi]

lemma phi_pi_pi (r s : ℕ) : phi r s π π = (-1 : ℝ) ^ (r + s) := by
  simp only [phi, Real.cos_nat_mul_pi]
  have h : ((-1 : ℝ) ^ r) * ((-1 : ℝ) ^ s) = (-1 : ℝ) ^ (r + s) := by
    rw [← pow_add]
  rw [h]
  ring

lemma cos_nat_two_pi (k : ℕ) : Real.cos ((k : ℝ) * (2 * π)) = 1 :=
  Real.cos_nat_mul_two_pi k

lemma abs_cos_eq_one_iff (x : ℝ) : |Real.cos x| = 1 ↔ ∃ k : ℤ, (k : ℝ) * π = x := by
  constructor
  · intro h
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 h with h | h
    · obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff x).1 h
      refine ⟨2 * n, ?_⟩
      calc
        ((2 * n : ℤ) : ℝ) * π = (n : ℝ) * (2 * π) := by push_cast; ring
        _ = x := hn
    · have hs : Real.sin x = 0 := (Real.sin_eq_zero_iff_cos_eq (x := x)).2 (Or.inr h)
      exact Real.sin_eq_zero_iff.1 hs
  · rintro ⟨k, rfl⟩
    rw [Real.cos_int_mul_pi, abs_zpow, abs_neg, abs_one, one_zpow]

lemma abs_mul_eq_one {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hab : |a * b| = 1) :
    |a| = 1 ∧ |b| = 1 := by
  rw [abs_mul] at hab
  have ha0 : 0 ≤ |a| := abs_nonneg a
  have hb0 : 0 ≤ |b| := abs_nonneg b
  constructor <;> nlinarith

lemma exists_piZ {r s : ℕ} (hcop : Nat.Coprime r s) {x : ℝ}
    (hrx : ∃ k : ℤ, (k : ℝ) * π = (r : ℝ) * x)
    (hsx : ∃ p : ℤ, (p : ℝ) * π = (s : ℝ) * x) :
    ∃ m : ℤ, (m : ℝ) * π = x := by
  obtain ⟨k, hk⟩ := hrx
  obtain ⟨p, hp⟩ := hsx
  have hbez : (1 : ℤ) = (r : ℤ) * Nat.gcdA r s + (s : ℤ) * Nat.gcdB r s := by
    have h := Nat.gcd_eq_gcd_ab r s
    rw [hcop] at h
    exact h
  have hbezR : (1 : ℝ) = (r : ℝ) * (Nat.gcdA r s) + (s : ℝ) * (Nat.gcdB r s) := by
    exact_mod_cast hbez
  refine ⟨Nat.gcdA r s * k + Nat.gcdB r s * p, ?_⟩
  calc
    (((Nat.gcdA r s * k + Nat.gcdB r s * p : ℤ) : ℝ)) * π
        = ((Nat.gcdA r s : ℝ) * (k : ℝ) + (Nat.gcdB r s : ℝ) * (p : ℝ)) * π := by
          push_cast; ring
    _ = (Nat.gcdA r s : ℝ) * ((k : ℝ) * π) + (Nat.gcdB r s : ℝ) * ((p : ℝ) * π) := by ring
    _ = (Nat.gcdA r s : ℝ) * ((r : ℝ) * x) + (Nat.gcdB r s : ℝ) * ((s : ℝ) * x) := by rw [hk, hp]
    _ = ((r : ℝ) * (Nat.gcdA r s : ℝ) + (s : ℝ) * (Nat.gcdB r s : ℝ)) * x := by ring
    _ = (1 : ℝ) * x := by rw [hbezR]
    _ = x := by ring

lemma abs_phi_eq_one {r s : ℕ} (hcop : Nat.Coprime r s) {x y : ℝ}
    (h : |phi r s x y| = 1) :
    (∃ k : ℤ, (k : ℝ) * π = x) ∧ (∃ m : ℤ, (m : ℝ) * π = y) := by
  set A := Real.cos ((r : ℝ) * x) * Real.cos ((s : ℝ) * y)
  set B := Real.cos ((s : ℝ) * x) * Real.cos ((r : ℝ) * y)
  have hAB : |A + B| = 2 := by
    have h' : |A + B| / 2 = 1 := by simpa [phi, A, B, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using h
    linarith
  have hA : |A| ≤ 1 := abs_cos_mul_le_one _ _
  have hB : |B| ≤ 1 := abs_cos_mul_le_one _ _
  rcases abs_pair_eq_two hA hB hAB with ⟨hA1, hB1⟩ | ⟨hA1, hB1⟩
  all_goals
    have hAabs : |A| = 1 := by simp [hA1]
    have hBabs : |B| = 1 := by simp [hB1]
    have hrx := (abs_mul_eq_one (Real.abs_cos_le_one _) (Real.abs_cos_le_one _) hAabs).1
    have hsy := (abs_mul_eq_one (Real.abs_cos_le_one _) (Real.abs_cos_le_one _) hAabs).2
    have hsx := (abs_mul_eq_one (Real.abs_cos_le_one _) (Real.abs_cos_le_one _) hBabs).1
    have hry := (abs_mul_eq_one (Real.abs_cos_le_one _) (Real.abs_cos_le_one _) hBabs).2
    exact ⟨exists_piZ hcop ((abs_cos_eq_one_iff _).1 hrx) ((abs_cos_eq_one_iff _).1 hsx),
      exists_piZ hcop ((abs_cos_eq_one_iff _).1 hry) ((abs_cos_eq_one_iff _).1 hsy)⟩

lemma eq_pi_or_two_pi {x : ℝ} (hx1 : π / 2 ≤ x) (hx2 : x ≤ 5 * π / 2)
    (h : ∃ k : ℤ, (k : ℝ) * π = x) : x = π ∨ x = 2 * π := by
  obtain ⟨k, hk⟩ := h
  have hpi : 0 < π := pi_pos
  have hx1' : π / 2 ≤ (k : ℝ) * π := by simpa [hk.symm] using hx1
  have hx2' : (k : ℝ) * π ≤ 5 * π / 2 := by simpa [hk.symm] using hx2
  have hklo : (1 : ℝ) / 2 ≤ (k : ℝ) := by
    apply le_of_mul_le_mul_right _ hpi
    nlinarith
  have hkhi : (k : ℝ) ≤ 5 / 2 := by
    apply le_of_mul_le_mul_right _ hpi
    nlinarith
  have hk1 : (1 : ℤ) ≤ k := by
    by_contra hlt
    have hk0 : k ≤ 0 := by omega
    have : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
    linarith
  have hk2 : k ≤ 2 := by
    by_contra hlt
    have hk3 : (3 : ℤ) ≤ k := by omega
    have : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
    linarith
  rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
  · exact Or.inl (by simpa using hk.symm)
  · exact Or.inr (by simpa using hk.symm)

lemma both_odd {r s : ℕ} (hcop : Nat.Coprime r s) (he : Even (r + s)) : Odd r ∧ Odd s := by
  have hr : Odd r := by
    rw [← Nat.not_even_iff_odd]
    intro hrE
    have hsE : Even s := ((Nat.even_add).1 he).mp hrE
    have h2 : 2 ∣ Nat.gcd r s := Nat.dvd_gcd (even_iff_two_dvd.1 hrE) (even_iff_two_dvd.1 hsE)
    rw [hcop] at h2
    omega
  have hs : Odd s := by
    rw [← Nat.not_even_iff_odd]
    intro hsE
    have hrE : Even r := ((Nat.even_add).1 he).mpr hsE
    exact (Nat.not_even_iff_odd.2 hr) hrE
  exact ⟨hr, hs⟩

lemma phi_two_pi (r s : ℕ) : phi r s (2 * π) (2 * π) = 1 := by
  simp [phi, Real.cos_nat_mul_two_pi]

lemma phi_pi_two (r s : ℕ) : phi r s π (2 * π) = (((-1 : ℝ) ^ r) + ((-1 : ℝ) ^ s)) / 2 := by
  simp only [phi, Real.cos_nat_mul_pi, cos_nat_two_pi]
  ring

lemma phi_two_pi_pi (r s : ℕ) : phi r s (2 * π) π = (((-1 : ℝ) ^ r) + ((-1 : ℝ) ^ s)) / 2 := by
  simp only [phi, Real.cos_nat_mul_pi, cos_nat_two_pi]
  ring

lemma phi_off_of_even {r s : ℕ} (hcop : Nat.Coprime r s) (he : Even (r + s)) :
    phi r s π (2 * π) = -1 ∧ phi r s (2 * π) π = -1 := by
  obtain ⟨hr, hs⟩ := both_odd hcop he
  constructor
  · rw [phi_pi_two, hr.neg_one_pow, hs.neg_one_pow]
    norm_num
  · rw [phi_two_pi_pi, hr.neg_one_pow, hs.neg_one_pow]
    norm_num

lemma cos_nat_add_pi (k : ℕ) (t : ℝ) :
    Real.cos ((k : ℝ) * (π + t)) = (-1 : ℝ) ^ k * Real.cos ((k : ℝ) * t) := by
  have h : (k : ℝ) * (π + t) = (k : ℝ) * t + (k : ℕ) * π := by ring
  rw [h, Real.cos_add_nat_mul_pi]

lemma cos_nat_add_two_pi (k : ℕ) (t : ℝ) :
    Real.cos ((k : ℝ) * ((2 * π) + t)) = Real.cos ((k : ℝ) * t) := by
  have h : (k : ℝ) * ((2 * π) + t) = (k : ℝ) * t + (k : ℕ) * (2 * π) := by ring
  rw [h, Real.cos_add_nat_mul_two_pi]

lemma phi_shift_pi (r s : ℕ) (t u : ℝ) :
    phi r s (π + t) (π + u) = (-1 : ℝ) ^ (r + s) * phi r s t u := by
  simp only [phi, cos_nat_add_pi]
  ring

lemma phi_shift_two (r s : ℕ) (t u : ℝ) :
    phi r s ((2 * π) + t) ((2 * π) + u) = phi r s t u := by
  simp only [phi]
  rw [cos_nat_add_two_pi r t, cos_nat_add_two_pi s u, cos_nat_add_two_pi s t, cos_nat_add_two_pi r u]

lemma phi_shift_pi_two {r s : ℕ} (hr : Odd r) (hs : Odd s) (t u : ℝ) :
    phi r s (π + t) ((2 * π) + u) = -phi r s t u := by
  simp only [phi]
  rw [cos_nat_add_pi r t, cos_nat_add_two_pi s u, cos_nat_add_pi s t, cos_nat_add_two_pi r u,
    hr.neg_one_pow, hs.neg_one_pow]
  ring

lemma phi_shift_two_pi {r s : ℕ} (hr : Odd r) (hs : Odd s) (t u : ℝ) :
    phi r s ((2 * π) + t) (π + u) = -phi r s t u := by
  simp only [phi]
  rw [cos_nat_add_two_pi r t, cos_nat_add_pi s u, cos_nat_add_two_pi s t, cos_nat_add_pi r u,
    hr.neg_one_pow, hs.neg_one_pow]
  ring

lemma neg_one_pow_sq (n k : ℕ) : (((-1 : ℝ) ^ k) ^ (2 * n)) = 1 := by
  rw [← pow_mul]
  have hcomm : k * (2 * n) = 2 * (k * n) := by ring
  rw [hcomm, pow_mul, neg_one_sq, one_pow]

lemma phi_shift_pi_pow (r s n : ℕ) (t u : ℝ) :
    phi r s (π + t) (π + u) ^ (2 * n) = phi r s t u ^ (2 * n) := by
  rw [phi_shift_pi, mul_pow, neg_one_pow_sq, one_mul]

lemma phi_shift_two_pow (r s n : ℕ) (t u : ℝ) :
    phi r s ((2 * π) + t) ((2 * π) + u) ^ (2 * n) = phi r s t u ^ (2 * n) := by
  rw [phi_shift_two]

lemma phi_shift_pi_two_pow {r s : ℕ} (hr : Odd r) (hs : Odd s) (n : ℕ) (t u : ℝ) :
    phi r s (π + t) ((2 * π) + u) ^ (2 * n) = phi r s t u ^ (2 * n) := by
  rw [phi_shift_pi_two hr hs, pow_mul, neg_sq, ← pow_mul]

lemma phi_shift_two_pi_pow {r s : ℕ} (hr : Odd r) (hs : Odd s) (n : ℕ) (t u : ℝ) :
    phi r s ((2 * π) + t) (π + u) ^ (2 * n) = phi r s t u ^ (2 * n) := by
  rw [phi_shift_two_pi hr hs, pow_mul, neg_sq, ← pow_mul]

noncomputable def aCoeff (r s : ℕ) : ℝ := (r : ℝ) ^ 2 + (s : ℝ) ^ 2

noncomputable def kRem (r s : ℕ) : ℝ := (3 / 16) * ((r : ℝ) ^ 4 + (s : ℝ) ^ 4)

lemma cos_err {θ : ℝ} (hθ : |θ| ≤ 1) :
    |Real.cos θ - (1 - θ ^ 2 / 2)| ≤ (1 / 8) * θ ^ 4 := by
  have h := Real.cos_bound hθ
  have h58 : (5 : ℝ) / 96 ≤ 1 / 8 := by norm_num
  have hpow : |θ| ^ 4 = θ ^ 4 := by
    rw [show |θ| ^ 4 = (|θ| ^ 2) ^ 2 by ring, sq_abs]
    ring
  have hnonneg : 0 ≤ |θ| ^ 4 := by positivity
  calc
    |Real.cos θ - (1 - θ ^ 2 / 2)| ≤ |θ| ^ 4 * (5 / 96) := h
    _ ≤ |θ| ^ 4 * (1 / 8) := mul_le_mul_of_nonneg_left h58 hnonneg
    _ = (1 / 8) * θ ^ 4 := by rw [hpow]; ring

lemma cos_prod_err {A B : ℝ} (hA : |A| ≤ 1) (hB : |B| ≤ 1) :
    |Real.cos A * Real.cos B - (1 - A ^ 2 / 2) * (1 - B ^ 2 / 2)| ≤
      (1 / 4) * (A ^ 4 + B ^ 4) := by
  set RA := Real.cos A - (1 - A ^ 2 / 2)
  set RB := Real.cos B - (1 - B ^ 2 / 2)
  have hRA : |RA| ≤ (1 / 8) * A ^ 4 := cos_err hA
  have hRB : |RB| ≤ (1 / 8) * B ^ 4 := cos_err hB
  have hE : Real.cos A * Real.cos B - (1 - A ^ 2 / 2) * (1 - B ^ 2 / 2) =
      (1 - A ^ 2 / 2) * RB + (1 - B ^ 2 / 2) * RA + RA * RB := by
    simp only [RA, RB]
    ring
  have hA2 : A ^ 2 ≤ 1 := by rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg A) hA
  have hB2 : B ^ 2 ≤ 1 := by rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg B) hB
  have hA2' : A ^ 2 / 2 ≤ 1 / 2 := by nlinarith
  have hB2' : B ^ 2 / 2 ≤ 1 / 2 := by nlinarith
  have h1A : |1 - A ^ 2 / 2| ≤ 1 := by
    rw [abs_of_nonneg (by nlinarith [sq_nonneg A])]
    nlinarith
  have h1B : |1 - B ^ 2 / 2| ≤ 1 := by
    rw [abs_of_nonneg (by nlinarith [sq_nonneg B])]
    nlinarith
  have hA4 : A ^ 4 ≤ 1 := by
    have : |A| ^ 4 ≤ 1 := pow_le_one₀ (abs_nonneg A) hA
    calc A ^ 4 = |A| ^ 4 := by rw [show A ^ 4 = (|A| ^ 2) ^ 2 by rw [sq_abs]; ring]; ring
      _ ≤ 1 := this
  have hB4 : B ^ 4 ≤ 1 := by
    have : |B| ^ 4 ≤ 1 := pow_le_one₀ (abs_nonneg B) hB
    calc B ^ 4 = |B| ^ 4 := by rw [show B ^ 4 = (|B| ^ 2) ^ 2 by rw [sq_abs]; ring]; ring
      _ ≤ 1 := this
  rw [hE]
  calc
    |(1 - A ^ 2 / 2) * RB + (1 - B ^ 2 / 2) * RA + RA * RB|
        ≤ |(1 - A ^ 2 / 2) * RB + (1 - B ^ 2 / 2) * RA| + |RA * RB| := abs_add_le _ _
    _ ≤ |(1 - A ^ 2 / 2) * RB| + |(1 - B ^ 2 / 2) * RA| + |RA * RB| := by
          have := abs_add_le ((1 - A ^ 2 / 2) * RB) ((1 - B ^ 2 / 2) * RA)
          linarith
    _ = |1 - A ^ 2 / 2| * |RB| + |1 - B ^ 2 / 2| * |RA| + |RA| * |RB| := by
          rw [abs_mul, abs_mul, abs_mul]
    _ ≤ (1 / 8) * B ^ 4 + (1 / 8) * A ^ 4 + ((1 / 8) * A ^ 4) * ((1 / 8) * B ^ 4) := by
          have hRA0 : 0 ≤ |RA| := abs_nonneg _
          have hRB0 : 0 ≤ |RB| := abs_nonneg _
          have h1 : |1 - A ^ 2 / 2| * |RB| ≤ 1 * ((1 / 8) * B ^ 4) :=
            mul_le_mul h1A hRB (abs_nonneg _) (by norm_num)
          have h2 : |1 - B ^ 2 / 2| * |RA| ≤ 1 * ((1 / 8) * A ^ 4) :=
            mul_le_mul h1B hRA (abs_nonneg _) (by norm_num)
          have h3 : |RA| * |RB| ≤ ((1 / 8) * A ^ 4) * ((1 / 8) * B ^ 4) :=
            mul_le_mul hRA hRB hRB0 (by positivity)
          linarith
    _ ≤ (1 / 4) * (A ^ 4 + B ^ 4) := by
          have hAB : 0 ≤ A ^ 4 := by positivity
          have hBB : 0 ≤ B ^ 4 := by positivity
          nlinarith

lemma fourth_sum (r s : ℕ) (x y : ℝ) :
    ((r : ℝ) * x) ^ 4 + ((s : ℝ) * y) ^ 4 + ((s : ℝ) * x) ^ 4 + ((r : ℝ) * y) ^ 4 =
      ((r : ℝ) ^ 4 + (s : ℝ) ^ 4) * (x ^ 4 + y ^ 4) := by ring

lemma square_sum (r s : ℕ) (x y : ℝ) :
    ((r : ℝ) * x) ^ 2 + ((s : ℝ) * y) ^ 2 + ((s : ℝ) * x) ^ 2 + ((r : ℝ) * y) ^ 2 =
      aCoeff r s * (x ^ 2 + y ^ 2) := by
  simp [aCoeff]
  ring

lemma angle_le_one {k m : ℕ} {x : ℝ} (hkm : (k : ℝ) ≤ m) (hx : |(m : ℝ) * x| ≤ 1) :
    |(k : ℝ) * x| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)] at hx
  exact (mul_le_mul_of_nonneg_right hkm (abs_nonneg x)).trans hx

lemma phi_taylor {r s : ℕ} {x y : ℝ} (hrs : r ≤ s)
    (hx : |(s : ℝ) * x| ≤ 1) (hy : |(s : ℝ) * y| ≤ 1) :
    |phi r s x y - (1 - aCoeff r s / 4 * (x ^ 2 + y ^ 2))| ≤
      kRem r s * (x ^ 2 + y ^ 2) ^ 2 := by
  have hrx : |(r : ℝ) * x| ≤ 1 := angle_le_one (Nat.cast_le.2 hrs) hx
  have hry : |(r : ℝ) * y| ≤ 1 := angle_le_one (Nat.cast_le.2 hrs) hy
  set A := (r : ℝ) * x
  set B := (s : ℝ) * y
  set C := (s : ℝ) * x
  set D := (r : ℝ) * y
  set ρ2 := x ^ 2 + y ^ 2
  have hA : |A| ≤ 1 := hrx
  have hB : |B| ≤ 1 := hy
  have hC : |C| ≤ 1 := hx
  have hD : |D| ≤ 1 := hry
  have hP := cos_prod_err hA hB
  have hQ := cos_prod_err hC hD
  have hmainP : (1 - A ^ 2 / 2) * (1 - B ^ 2 / 2) = 1 - (A ^ 2 + B ^ 2) / 2 + A ^ 2 * B ^ 2 / 4 := by
    ring
  have hmainQ : (1 - C ^ 2 / 2) * (1 - D ^ 2 / 2) = 1 - (C ^ 2 + D ^ 2) / 2 + C ^ 2 * D ^ 2 / 4 := by
    ring
  set EA := Real.cos A * Real.cos B - (1 - A ^ 2 / 2) * (1 - B ^ 2 / 2)
  set EB := Real.cos C * Real.cos D - (1 - C ^ 2 / 2) * (1 - D ^ 2 / 2)
  have hEA : |EA| ≤ (1 / 4) * (A ^ 4 + B ^ 4) := by simpa [EA] using hP
  have hEB : |EB| ≤ (1 / 4) * (C ^ 4 + D ^ 4) := by simpa [EB] using hQ
  have hdiff : phi r s x y - (1 - aCoeff r s / 4 * ρ2) =
      (A ^ 2 * B ^ 2 + C ^ 2 * D ^ 2) / 8 + (EA + EB) / 2 := by
    simp only [phi, aCoeff, EA, EB, A, B, C, D, ρ2]
    ring
  have hAB : A ^ 2 * B ^ 2 ≤ (A ^ 4 + B ^ 4) / 2 := by nlinarith [sq_nonneg (A ^ 2 - B ^ 2)]
  have hCD : C ^ 2 * D ^ 2 ≤ (C ^ 4 + D ^ 4) / 2 := by nlinarith [sq_nonneg (C ^ 2 - D ^ 2)]
  have hxy : x ^ 4 + y ^ 4 ≤ ρ2 ^ 2 := by
    simp only [ρ2]
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
  have hS : 0 ≤ A ^ 2 * B ^ 2 + C ^ 2 * D ^ 2 := by nlinarith [sq_nonneg A, sq_nonneg B, sq_nonneg C, sq_nonneg D]
  rw [hdiff]
  calc
    |(A ^ 2 * B ^ 2 + C ^ 2 * D ^ 2) / 8 + (EA + EB) / 2|
        ≤ |(A ^ 2 * B ^ 2 + C ^ 2 * D ^ 2) / 8| + |(EA + EB) / 2| := abs_add_le _ _
    _ = |A ^ 2 * B ^ 2 + C ^ 2 * D ^ 2| / 8 + |EA + EB| / 2 := by
          rw [abs_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8),
            abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ = (A ^ 2 * B ^ 2 + C ^ 2 * D ^ 2) / 8 + |EA + EB| / 2 := by
          rw [abs_of_nonneg hS]
    _ ≤ (A ^ 2 * B ^ 2 + C ^ 2 * D ^ 2) / 8 + (|EA| + |EB|) / 2 := by
          have := abs_add_le EA EB
          gcongr
    _ ≤ ((A ^ 4 + B ^ 4) / 2 + (C ^ 4 + D ^ 4) / 2) / 8 +
          ((1 / 4) * (A ^ 4 + B ^ 4) + (1 / 4) * (C ^ 4 + D ^ 4)) / 2 := by
          gcongr
    _ = (3 / 16) * (A ^ 4 + B ^ 4 + C ^ 4 + D ^ 4) := by ring
    _ = (3 / 16) * (((r : ℝ) ^ 4 + (s : ℝ) ^ 4) * (x ^ 4 + y ^ 4)) := by
          have hfour : A ^ 4 + B ^ 4 + C ^ 4 + D ^ 4 =
              ((r : ℝ) ^ 4 + (s : ℝ) ^ 4) * (x ^ 4 + y ^ 4) := by
            simp only [A, B, C, D]
            exact fourth_sum r s x y
          rw [hfour]
    _ ≤ (3 / 16) * (((r : ℝ) ^ 4 + (s : ℝ) ^ 4) * ρ2 ^ 2) := by
          have hcoef : 0 ≤ (3 / 16) * ((r : ℝ) ^ 4 + (s : ℝ) ^ 4) := by positivity
          calc
            (3 / 16) * (((r : ℝ) ^ 4 + (s : ℝ) ^ 4) * (x ^ 4 + y ^ 4))
                = ((3 / 16) * ((r : ℝ) ^ 4 + (s : ℝ) ^ 4)) * (x ^ 4 + y ^ 4) := by ring
            _ ≤ ((3 / 16) * ((r : ℝ) ^ 4 + (s : ℝ) ^ 4)) * ρ2 ^ 2 :=
                mul_le_mul_of_nonneg_left hxy hcoef
            _ = (3 / 16) * (((r : ℝ) ^ 4 + (s : ℝ) ^ 4) * ρ2 ^ 2) := by ring
    _ = kRem r s * ρ2 ^ 2 := by simp [kRem]; ring

lemma aCoeff_pos {r s : ℕ} (hr : 0 < r) : 0 < aCoeff r s := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
  have hs2 : 0 ≤ (s : ℝ) ^ 2 := by positivity
  simp only [aCoeff]
  linarith

lemma kRem_nonneg (r s : ℕ) : 0 ≤ kRem r s := by
  have hr4 : 0 ≤ (r : ℝ) ^ 4 := by positivity
  have hs4 : 0 ≤ (s : ℝ) ^ 4 := by positivity
  simp only [kRem]
  positivity

lemma phi_pos_exp {r s : ℕ} {x y : ℝ} (hrs : r ≤ s) (hr : 0 < r)
    (hx : |(s : ℝ) * x| ≤ 1) (hy : |(s : ℝ) * y| ≤ 1)
    (hclose : x ^ 2 + y ^ 2 ≤ aCoeff r s / (8 * (kRem r s + 1)))
    (hsmall : x ^ 2 + y ^ 2 ≤ 1 / (2 * (aCoeff r s + 1))) :
    0 < phi r s x y ∧ phi r s x y ≤ Real.exp (-(aCoeff r s / 8) * (x ^ 2 + y ^ 2)) := by
  set ρ2 := x ^ 2 + y ^ 2
  have hρ0 : 0 ≤ ρ2 := by simp only [ρ2]; nlinarith [sq_nonneg x, sq_nonneg y]
  have ha0 : 0 < aCoeff r s := aCoeff_pos hr
  have hk0 : 0 ≤ kRem r s := kRem_nonneg r s
  have hK : kRem r s * ρ2 ≤ aCoeff r s / 8 := by
    have hfrac : kRem r s / (kRem r s + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    calc
      kRem r s * ρ2 ≤ kRem r s * (aCoeff r s / (8 * (kRem r s + 1))) :=
          mul_le_mul_of_nonneg_left hclose hk0
      _ = (kRem r s / (kRem r s + 1)) * (aCoeff r s / 8) := by field_simp
      _ ≤ 1 * (aCoeff r s / 8) := mul_le_mul_of_nonneg_right hfrac (by positivity)
      _ = aCoeff r s / 8 := by ring
  have hrem : kRem r s * ρ2 ^ 2 ≤ (aCoeff r s / 8) * ρ2 := by
    calc
      kRem r s * ρ2 ^ 2 = (kRem r s * ρ2) * ρ2 := by ring
      _ ≤ (aCoeff r s / 8) * ρ2 := mul_le_mul_of_nonneg_right hK hρ0
  have ht := phi_taylor hrs hx hy
  have habs := abs_le.mp (by simpa [ρ2] using ht)
  have hupper : phi r s x y ≤ 1 - (aCoeff r s / 8) * ρ2 := by
    linarith [habs.2]
  have hlower : 1 - (3 * aCoeff r s / 8) * ρ2 ≤ phi r s x y := by
    linarith [habs.1]
  have h316 : (3 * aCoeff r s / 8) * ρ2 ≤ 3 / 16 := by
    calc
      (3 * aCoeff r s / 8) * ρ2 ≤ (3 * aCoeff r s / 8) * (1 / (2 * (aCoeff r s + 1))) :=
          mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = 3 * aCoeff r s / (16 * (aCoeff r s + 1)) := by field_simp; norm_num
      _ ≤ 3 / 16 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have hpos : 0 < phi r s x y := by linarith
  have hexp : 1 - (aCoeff r s / 8) * ρ2 ≤ Real.exp (-(aCoeff r s / 8) * ρ2) := by
    linarith [Real.add_one_le_exp (-(aCoeff r s / 8) * ρ2)]
  exact ⟨hpos, hupper.trans hexp⟩

lemma abs_exp_sub_le_of_nonpos {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a - b| := by
  have hint : IntervalIntegrable Real.exp MeasureTheory.volume a b :=
    Real.continuous_exp.intervalIntegrable a b
  have heq : ∫ t in a..b, Real.exp t = Real.exp b - Real.exp a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => Real.hasDerivAt_exp t) hint
  have hle : ‖∫ t in a..b, Real.exp t‖ ≤ 1 * |b - a| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const
      (f := Real.exp) (a := a) (b := b) (C := 1) ?_
    intro t ht
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
    rw [Set.mem_uIoc] at ht
    cases ht with
    | inl h => exact (Real.exp_le_one_iff).2 (h.2.trans hb)
    | inr h => exact (Real.exp_le_one_iff).2 (h.2.trans ha)
  calc
    |Real.exp a - Real.exp b| = |Real.exp b - Real.exp a| := abs_sub_comm _ _
    _ = |∫ t in a..b, Real.exp t| := by rw [heq]
    _ = ‖∫ t in a..b, Real.exp t‖ := by rw [Real.norm_eq_abs]
    _ ≤ 1 * |b - a| := hle
    _ = |a - b| := by rw [one_mul, abs_sub_comm]

open Filter
open scoped Topology

lemma tendsto_div_sqrt (c : ℝ) :
    Tendsto (fun n : ℕ => c / Real.sqrt (n : ℝ)) Filter.atTop (nhds 0) := by
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  simpa [div_eq_mul_inv, mul_zero] using (tendsto_inv_atTop_zero.comp hsqrt).const_mul c

lemma eventually_abs_le_one (c : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, |c / Real.sqrt (n : ℝ)| ≤ 1 := by
  have hball : Metric.ball 0 1 ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds 0 (by norm_num)
  filter_upwards [(tendsto_div_sqrt c).eventually hball] with n hn
  rw [Real.dist_eq, sub_zero] at hn
  exact hn.le

lemma eventually_sq_le (u v ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (u / Real.sqrt (n : ℝ)) ^ 2 + (v / Real.sqrt (n : ℝ)) ^ 2 ≤ ε := by
  have hu2 : Tendsto (fun n : ℕ => (u / Real.sqrt (n : ℝ)) ^ 2) Filter.atTop (nhds 0) :=
    ((continuous_pow 2).tendsto' 0 0 (by simp)).comp (tendsto_div_sqrt u)
  have hv2 : Tendsto (fun n : ℕ => (v / Real.sqrt (n : ℝ)) ^ 2) Filter.atTop (nhds 0) :=
    ((continuous_pow 2).tendsto' 0 0 (by simp)).comp (tendsto_div_sqrt v)
  have hsum : Tendsto (fun n : ℕ => (u / Real.sqrt (n : ℝ)) ^ 2 + (v / Real.sqrt (n : ℝ)) ^ 2)
      Filter.atTop (nhds 0) := by
    simpa [add_zero] using hu2.add hv2
  have hball : Metric.ball 0 ε ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds 0 hε
  filter_upwards [hsum.eventually hball] with n hn
  rw [Real.dist_eq, sub_zero] at hn
  have hnn : 0 ≤ (u / Real.sqrt (n : ℝ)) ^ 2 + (v / Real.sqrt (n : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (u / Real.sqrt (n : ℝ)), sq_nonneg (v / Real.sqrt (n : ℝ))]
  rw [abs_of_nonneg hnn] at hn
  exact hn.le

lemma rho_div {u v : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    (u / Real.sqrt (n : ℝ)) ^ 2 + (v / Real.sqrt (n : ℝ)) ^ 2 =
      (u ^ 2 + v ^ 2) / (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  have hs0 : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_ne_zero (Nat.cast_nonneg n)).2 hn0
  field_simp [hs0, hn0]
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  ring

lemma psi_taylor {r s : ℕ} {x y : ℝ} (hrs : r ≤ s)
    (hx : |(s : ℝ) * x| ≤ 1) (hy : |(s : ℝ) * y| ≤ 1) :
    |(1 - phi r s x y) - (aCoeff r s / 4) * (x ^ 2 + y ^ 2)| ≤
      kRem r s * (x ^ 2 + y ^ 2) ^ 2 := by
  have ht := phi_taylor hrs hx hy
  rw [abs_sub_comm] at ht
  convert ht using 2
  ring

lemma tendsto_two_n_psi {r s : ℕ} (_hr : 0 < r) (hrs : r ≤ s) (u v : ℝ) :
    Tendsto (fun n : ℕ => (2 * (n : ℝ)) *
        (1 - phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ))))
      Filter.atTop (nhds ((aCoeff r s / 2) * (u ^ 2 + v ^ 2))) := by
  set Q := u ^ 2 + v ^ 2
  rw [Metric.tendsto_atTop]
  intro ε hε
  have htail : Tendsto (fun n : ℕ => (2 * kRem r s * Q ^ 2) / (n : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (2 * kRem r s * Q ^ 2)
  have hball : Metric.ball 0 ε ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds 0 hε
  rw [← Filter.eventually_atTop]
  filter_upwards [eventually_abs_le_one ((s : ℝ) * u), eventually_abs_le_one ((s : ℝ) * v),
      htail.eventually hball, Filter.eventually_ge_atTop 1] with n hau hbv htn hn
  have hρ := rho_div (u := u) (v := v) hn
  have hau' : |(s : ℝ) * (u / Real.sqrt (n : ℝ))| ≤ 1 := by
    simpa [mul_div_assoc] using hau
  have hbv' : |(s : ℝ) * (v / Real.sqrt (n : ℝ))| ≤ 1 := by
    simpa [mul_div_assoc] using hbv
  have hnn : (0 : ℝ) < n := by exact_mod_cast (Nat.succ_le_iff.mp hn)
  have herr : |(2 * (n : ℝ)) * (1 - phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ))) -
      (aCoeff r s / 2) * Q| ≤ (2 * kRem r s * Q ^ 2) / (n : ℝ) := by
    have hmain : (2 * (n : ℝ)) * ((aCoeff r s / 4) * (Q / (n : ℝ))) = (aCoeff r s / 2) * Q := by
      field_simp [hnn.ne']
      ring
    have hrest : (2 * (n : ℝ)) * (kRem r s * (Q / (n : ℝ)) ^ 2) =
        (2 * kRem r s * Q ^ 2) / (n : ℝ) := by
      field_simp [hnn.ne']
    have hdiff : (2 * (n : ℝ)) * (1 - phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ))) -
        (aCoeff r s / 2) * Q =
        (2 * (n : ℝ)) * ((1 - phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ))) -
          (aCoeff r s / 4) * (Q / (n : ℝ))) := by
      rw [← hmain]
      ring
    have hraw := psi_taylor (r := r) (s := s) hrs hau' hbv'
    rw [hρ] at hraw
    have hscaled : |(2 * (n : ℝ)) *
        ((1 - phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ))) -
          (aCoeff r s / 4) * (Q / (n : ℝ)))| ≤
        (2 * (n : ℝ)) * (kRem r s * (Q / (n : ℝ)) ^ 2) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))]
      exact mul_le_mul_of_nonneg_left hraw (by positivity)
    rw [hdiff]
    exact hscaled.trans_eq hrest
  rw [Real.dist_eq, sub_zero] at htn
  have htail0 : 0 ≤ (2 * kRem r s * Q ^ 2) / (n : ℝ) := by
    refine div_nonneg ?_ hnn.le
    exact mul_nonneg (mul_nonneg (by norm_num) (kRem_nonneg r s)) (sq_nonneg Q)
  rw [abs_of_nonneg htail0] at htn
  have hdist : |(2 * (n : ℝ)) * (1 - phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ))) -
      (aCoeff r s / 2) * Q| < ε := lt_of_le_of_lt herr htn
  simpa [Real.dist_eq, Q] using hdist

lemma abs_log_one_sub {y : ℝ} (hy : |y| < 1) :
    |y + Real.log (1 - y)| ≤ y ^ 2 / (1 - |y|) := by
  simpa [Finset.sum_range_one, sq_abs] using Real.abs_log_sub_add_sum_range_le hy 1

lemma abs_log_phi {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    |Real.log x + (1 - x)| ≤ (1 - x) ^ 2 / x := by
  have hy : |1 - x| < 1 := by
    rw [abs_of_nonneg (sub_nonneg.2 hx1)]
    linarith
  have h := abs_log_one_sub hy
  have hsub : (1 : ℝ) - (1 - x) = x := by ring
  rw [abs_of_nonneg (sub_nonneg.2 hx1), hsub, add_comm] at h
  exact h

lemma phi_le_one (r s : ℕ) (x y : ℝ) : phi r s x y ≤ 1 :=
  (abs_le.mp (abs_phi_le_one r s x y)).2

lemma tendsto_psi_zero {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s) (u v : ℝ) :
    Tendsto (fun n : ℕ => 1 - phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)))
      Filter.atTop (nhds 0) := by
  set ψ : ℕ → ℝ := fun n => 1 - phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ))
  have h2n : Tendsto (fun n : ℕ => 2 * (n : ℝ)) Filter.atTop Filter.atTop := by
    simpa [mul_comm] using
      tendsto_natCast_atTop_atTop.atTop_mul_const (by norm_num : (0 : ℝ) < 2)
  have hinv : Tendsto (fun n : ℕ => (2 * (n : ℝ))⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp h2n
  have hprod : Tendsto (fun n : ℕ => ((2 * (n : ℝ)) * ψ n) * (2 * (n : ℝ))⁻¹)
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using (tendsto_two_n_psi hr hrs u v).mul hinv
  apply hprod.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : (2 * (n : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast (Nat.succ_le_iff.mp hn)
    positivity
  calc
    ((2 * (n : ℝ)) * ψ n) * (2 * (n : ℝ))⁻¹ =
        ψ n * ((2 * (n : ℝ)) * (2 * (n : ℝ))⁻¹) := by ring
    _ = ψ n * 1 := by rw [mul_inv_cancel₀ hn0]
    _ = ψ n := by ring

lemma tendsto_two_n_log {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s) (u v : ℝ) :
    Tendsto (fun n : ℕ => (2 * (n : ℝ)) *
        Real.log (phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ))))
      Filter.atTop (nhds (-((aCoeff r s / 2) * (u ^ 2 + v ^ 2)))) := by
  set x : ℕ → ℝ := fun n => u / Real.sqrt (n : ℝ)
  set y : ℕ → ℝ := fun n => v / Real.sqrt (n : ℝ)
  set ψ : ℕ → ℝ := fun n => 1 - phi r s (x n) (y n)
  set Q : ℝ := u ^ 2 + v ^ 2
  have hψ : Tendsto ψ Filter.atTop (nhds 0) := by
    simpa [ψ, x, y] using tendsto_psi_zero hr hrs u v
  have h2ψ : Tendsto (fun n : ℕ => (2 * (n : ℝ)) * ψ n) Filter.atTop
      (nhds ((aCoeff r s / 2) * Q)) := by
    simpa [ψ, x, y, Q] using tendsto_two_n_psi hr hrs u v
  have hhalf : ∀ᶠ n : ℕ in Filter.atTop, |ψ n| < 1 / 2 := by
    have hball : Metric.ball 0 (1 / 2) ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds 0 (by norm_num)
    filter_upwards [hψ.eventually hball] with n hn
    rw [Real.dist_eq, sub_zero] at hn
    exact hn
  have hpos : ∀ᶠ n : ℕ in Filter.atTop, 1 / 2 ≤ phi r s (x n) (y n) := by
    filter_upwards [hhalf] with n hn
    have hψlt : ψ n < 1 / 2 := (abs_lt.mp hn).2
    dsimp [ψ] at hψlt
    linarith
  have herr : ∀ᶠ n : ℕ in Filter.atTop,
      |(2 * (n : ℝ)) * Real.log (phi r s (x n) (y n)) + (2 * (n : ℝ)) * ψ n| ≤
        2 * ψ n * ((2 * (n : ℝ)) * ψ n) := by
    filter_upwards [hpos] with n hphi
    have hφ1 : phi r s (x n) (y n) ≤ 1 := phi_le_one r s (x n) (y n)
    have hφ0 : 0 < phi r s (x n) (y n) := by linarith
    have hlog := abs_log_phi hφ0 hφ1
    have hcoef : 0 ≤ 2 * (n : ℝ) := by positivity
    have habs : |(2 * (n : ℝ)) * Real.log (phi r s (x n) (y n)) + (2 * (n : ℝ)) * ψ n| =
        (2 * (n : ℝ)) * |Real.log (phi r s (x n) (y n)) + ψ n| := by
      have hψdef : ψ n = 1 - phi r s (x n) (y n) := rfl
      rw [← mul_add, abs_mul, abs_of_nonneg hcoef, hψdef]
    rw [habs]
    have hdiv : |Real.log (phi r s (x n) (y n)) + ψ n| ≤ 2 * ψ n ^ 2 := by
      have hlog' : |Real.log (phi r s (x n) (y n)) + ψ n| ≤
          ψ n ^ 2 / phi r s (x n) (y n) := by
        simpa [ψ] using hlog
      refine hlog'.trans ?_
      have hinv : (phi r s (x n) (y n))⁻¹ ≤ 2 := by
        have hφ0' : 0 < phi r s (x n) (y n) := by linarith
        have hle := (inv_le_inv₀ hφ0' (by norm_num : (0 : ℝ) < 1 / 2)).2 hphi
        have htwo : ((1 : ℝ) / 2)⁻¹ = 2 := by norm_num
        simpa [htwo] using hle
      rw [div_eq_mul_inv, mul_comm (2 : ℝ) (ψ n ^ 2)]
      exact mul_le_mul_of_nonneg_left hinv (sq_nonneg (ψ n))
    refine (mul_le_mul_of_nonneg_left hdiv hcoef).trans_eq ?_
    ring
  have hbound : Tendsto (fun n : ℕ => 2 * ψ n * ((2 * (n : ℝ)) * ψ n)) Filter.atTop (nhds 0) := by
    simpa only [mul_zero, zero_mul] using (hψ.const_mul 2).mul h2ψ
  have hlower : Tendsto (fun n : ℕ => -(2 * ψ n * ((2 * (n : ℝ)) * ψ n))) Filter.atTop (nhds 0) := by
    simpa only [neg_zero] using hbound.neg
  have hzero : Tendsto (fun n : ℕ =>
      (2 * (n : ℝ)) * Real.log (phi r s (x n) (y n)) + (2 * (n : ℝ)) * ψ n)
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hbound
      (by filter_upwards [herr] with n hn; exact (abs_le.mp hn).1)
      (by filter_upwards [herr] with n hn; exact (abs_le.mp hn).2)
  have hsum := h2ψ.neg.add hzero
  have hfun : (fun n : ℕ => -((2 * (n : ℝ)) * ψ n) +
      ((2 * (n : ℝ)) * Real.log (phi r s (x n) (y n)) + (2 * (n : ℝ)) * ψ n)) =
      fun n : ℕ => (2 * (n : ℝ)) * Real.log (phi r s (x n) (y n)) := by
    ext n
    ring
  have hL : -((aCoeff r s / 2) * Q) + 0 = -((aCoeff r s / 2) * Q) := by ring
  rw [hfun] at hsum
  simpa only [hL, Q] using hsum

lemma tendsto_phi_pow {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s) (u v : ℝ) :
    Tendsto (fun n : ℕ =>
        phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ^ (2 * n))
      Filter.atTop (nhds (Real.exp (-((aCoeff r s / 2) * (u ^ 2 + v ^ 2))))) := by
  set x : ℕ → ℝ := fun n => u / Real.sqrt (n : ℝ)
  set y : ℕ → ℝ := fun n => v / Real.sqrt (n : ℝ)
  have hlog := tendsto_two_n_log hr hrs u v
  have hexp := (Real.continuous_exp.tendsto
    (-((aCoeff r s / 2) * (u ^ 2 + v ^ 2))))
  have hcomp := hexp.comp (by simpa [x, y] using hlog)
  have hhalf : ∀ᶠ n : ℕ in Filter.atTop,
      1 / 2 ≤ phi r s (x n) (y n) := by
    have hψ := tendsto_psi_zero hr hrs u v
    have hball : Metric.ball 0 (1 / 2) ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds 0 (by norm_num)
    filter_upwards [hψ.eventually hball] with n hn
    rw [Real.dist_eq, sub_zero] at hn
    have hψlt : 1 - phi r s (x n) (y n) < 1 / 2 := by
      simpa [x, y] using (abs_lt.mp hn).2
    linarith
  apply hcomp.congr'
  filter_upwards [hhalf] with n hphi
  have hpos : 0 < phi r s (x n) (y n) := by linarith
  rw [← Real.exp_log (pow_pos hpos (2 * n)), Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]
  simp [x, y, Function.comp_apply]

lemma exp_add_sq (c u v : ℝ) :
    Real.exp (-c * (u ^ 2 + v ^ 2)) =
      Real.exp (-c * u ^ 2) * Real.exp (-c * v ^ 2) := by
  rw [← Real.exp_add]
  congr 1
  ring

lemma sq_gaussian (c R : ℝ) :
    ∫ u in (-R)..R, ∫ v in (-R)..R, Real.exp (-c * (u ^ 2 + v ^ 2)) =
      (∫ t in (-R)..R, Real.exp (-c * t ^ 2)) ^ 2 := by
  simp_rw [exp_add_sq, intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
  rw [pow_two]

lemma tendsto_interval_gaussian {c : ℝ} (hc : 0 < c) :
    Tendsto (fun R : ℝ => ∫ t in (-R)..R, Real.exp (-c * t ^ 2)) Filter.atTop
      (nhds (Real.sqrt (π / c))) := by
  have h := intervalIntegral_tendsto_integral (integrable_exp_neg_mul_sq hc)
    tendsto_neg_atTop_atBot tendsto_id
  rw [integral_gaussian c] at h
  exact h

lemma tendsto_sq_interval_gaussian {c : ℝ} (hc : 0 < c) :
    Tendsto (fun R : ℝ => (∫ t in (-R)..R, Real.exp (-c * t ^ 2)) ^ 2) Filter.atTop
      (nhds (π / c)) := by
  have h := (tendsto_interval_gaussian hc).mul (tendsto_interval_gaussian hc)
  have hsq : Real.sqrt (π / c) * Real.sqrt (π / c) = π / c := by
    rw [← pow_two, Real.sq_sqrt (div_nonneg pi_nonneg hc.le)]
  simpa [pow_two, hsq] using h

lemma tendsto_gaussian_tail {c : ℝ} (hc : 0 < c) :
    Tendsto (fun R : ℝ => π / c - (∫ t in (-R)..R, Real.exp (-c * t ^ 2)) ^ 2) Filter.atTop
      (nhds 0) := by
  simpa [sub_self] using
    (tendsto_const_nhds (x := π / c)).sub (tendsto_sq_interval_gaussian hc)

lemma abs_integral_le_const {a b C : ℝ} {f : ℝ → ℝ} (hC : ∀ t, |f t| ≤ C) :
    |∫ t in a..b, f t| ≤ C * |b - a| := by
  have hnorm : ‖∫ t in a..b, f t‖ ≤ C * |b - a| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (C := C) ?_
    intro t _ht
    rw [Real.norm_eq_abs]
    exact hC t
  simpa [Real.norm_eq_abs] using hnorm

lemma abs_double_le {a b c d C : ℝ} {f : ℝ → ℝ → ℝ} (hC : ∀ x y, |f x y| ≤ C) :
    |∫ x in a..b, ∫ y in c..d, f x y| ≤ C * |b - a| * |d - c| := by
  have hinner : ∀ x, |∫ y in c..d, f x y| ≤ C * |d - c| :=
    fun x => abs_integral_le_const (fun y => hC x y)
  have houter := abs_integral_le_const (C := C * |d - c|) (a := a) (b := b)
    (f := fun x => ∫ y in c..d, f x y) (fun x => hinner x)
  calc
    |∫ x in a..b, ∫ y in c..d, f x y| ≤ (C * |d - c|) * |b - a| := houter
    _ = C * |b - a| * |d - c| := by ring

lemma rescale_one {a b : ℝ} {n : ℕ} (hn : 1 ≤ n) (f : ℝ → ℝ) :
    ∫ x in a..b, f x =
      (Real.sqrt (n : ℝ))⁻¹ *
        ∫ u in (a * Real.sqrt (n : ℝ))..(b * Real.sqrt (n : ℝ)),
          f (u / Real.sqrt (n : ℝ)) := by
  set s : ℝ := Real.sqrt (n : ℝ)
  have hs : s ≠ 0 := (Real.sqrt_ne_zero (Nat.cast_nonneg n)).2
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn)
  have hdiv := intervalIntegral.integral_comp_div (a := a * s) (b := b * s) (c := s) (f := f) hs
  have ha : a * s / s = a := by field_simp [hs]
  have hb : b * s / s = b := by field_simp [hs]
  rw [ha, hb, smul_eq_mul] at hdiv
  rw [← inv_mul_cancel_left₀ hs (∫ x in a..b, f x)]
  exact congrArg (fun z => s⁻¹ * z) hdiv.symm

lemma rescale_square {η : ℝ} {n : ℕ} (hn : 1 ≤ n) (f : ℝ → ℝ → ℝ) :
    (n : ℝ) * ∫ x in (-η)..η, ∫ y in (-η)..η, f x y =
      ∫ u in (-η * Real.sqrt (n : ℝ))..(η * Real.sqrt (n : ℝ)),
        ∫ v in (-η * Real.sqrt (n : ℝ))..(η * Real.sqrt (n : ℝ)),
          f (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) := by
  set s : ℝ := Real.sqrt (n : ℝ)
  have hs : s ≠ 0 := (Real.sqrt_ne_zero (Nat.cast_nonneg n)).2
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hinner : ∀ x, ∫ y in (-η)..η, f x y =
      s⁻¹ * ∫ v in (-η * s)..(η * s), f x (v / s) := by
    intro x
    simpa only [s] using rescale_one hn (fun y => f x y)
  simp_rw [hinner, intervalIntegral.integral_const_mul]
  have houter := rescale_one (a := -η) (b := η) hn
    (fun x => ∫ v in (-η * s)..(η * s), f x (v / s))
  rw [show s = Real.sqrt (n : ℝ) from rfl] at houter
  rw [houter]
  have hinv : s⁻¹ * s⁻¹ = (n : ℝ)⁻¹ := by
    rw [← mul_inv, ← sq, hs2]
  calc
    (n : ℝ) * (s⁻¹ * (s⁻¹ *
        ∫ u in (-η * Real.sqrt (n : ℝ))..(η * Real.sqrt (n : ℝ)),
          ∫ v in (-η * s)..(η * s), f (u / s) (v / s))) =
        ((n : ℝ) * (s⁻¹ * s⁻¹)) *
          ∫ u in (-η * Real.sqrt (n : ℝ))..(η * Real.sqrt (n : ℝ)),
            ∫ v in (-η * s)..(η * s), f (u / s) (v / s) := by ring
    _ = ((n : ℝ) * (n : ℝ)⁻¹) *
          ∫ u in (-η * Real.sqrt (n : ℝ))..(η * Real.sqrt (n : ℝ)),
            ∫ v in (-η * s)..(η * s), f (u / s) (v / s) := by rw [hinv]
    _ = ∫ u in (-η * Real.sqrt (n : ℝ))..(η * Real.sqrt (n : ℝ)),
          ∫ v in (-η * s)..(η * s), f (u / s) (v / s) := by
      rw [mul_inv_cancel₀ hn0, one_mul]

lemma phi_add_two_pi_left (r s : ℕ) (t y : ℝ) :
    phi r s (t + 2 * π) y = phi r s t y := by
  simp only [phi]
  have h1 : (r : ℝ) * (t + 2 * π) = (r : ℝ) * t + (r : ℕ) * (2 * π) := by ring
  have h2 : (s : ℝ) * (t + 2 * π) = (s : ℝ) * t + (s : ℕ) * (2 * π) := by ring
  rw [h1, h2, Real.cos_add_nat_mul_two_pi, Real.cos_add_nat_mul_two_pi]

lemma phi_add_two_pi_right (r s : ℕ) (x t : ℝ) :
    phi r s x (t + 2 * π) = phi r s x t := by
  simp only [phi]
  have h1 : (s : ℝ) * (t + 2 * π) = (s : ℝ) * t + (s : ℕ) * (2 * π) := by ring
  have h2 : (r : ℝ) * (t + 2 * π) = (r : ℝ) * t + (r : ℕ) * (2 * π) := by ring
  rw [h1, h2, Real.cos_add_nat_mul_two_pi, Real.cos_add_nat_mul_two_pi]

lemma integral_window (r s n : ℕ) :
    ∫ x in (π / 2)..(5 * π / 2), ∫ y in (π / 2)..(5 * π / 2), phi r s x y ^ (2 * n) =
      ∫ x in (0 : ℝ)..(2 * π), ∫ y in (0 : ℝ)..(2 * π), phi r s x y ^ (2 * n) := by
  have hfive : 5 * π / 2 = π / 2 + 2 * π := by ring
  have hinner : ∀ x, ∫ y in (π / 2)..(5 * π / 2), phi r s x y ^ (2 * n) =
      ∫ y in (0 : ℝ)..(2 * π), phi r s x y ^ (2 * n) := by
    intro x
    have hper : Function.Periodic (fun y => phi r s x y ^ (2 * n)) (2 * π) := by
      intro y
      show phi r s x (y + 2 * π) ^ (2 * n) = phi r s x y ^ (2 * n)
      rw [phi_add_two_pi_right]
    rw [hfive]
    simpa [zero_add] using hper.intervalIntegral_add_eq (π / 2) 0
  simp_rw [hinner]
  have hper : Function.Periodic
      (fun x => ∫ y in (0 : ℝ)..(2 * π), phi r s x y ^ (2 * n)) (2 * π) := by
    intro x
    simp_rw [phi_add_two_pi_left]
  rw [hfive]
  simpa [zero_add] using hper.intervalIntegral_add_eq (π / 2) 0

lemma phi_pow_nonneg (r s n : ℕ) (x y : ℝ) : 0 ≤ phi r s x y ^ (2 * n) := by
  rw [show 2 * n = 2 * n from rfl, pow_mul]
  exact pow_nonneg (sq_nonneg _) _

lemma phi_pow_abs_le_one (r s n : ℕ) (x y : ℝ) : |phi r s x y ^ (2 * n)| ≤ 1 := by
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (abs_phi_le_one r s x y)

noncomputable def eta (r s : ℕ) : ℝ :=
  min (π / 4) (min (1 / ((s : ℝ) + 1))
    (min (Real.sqrt (aCoeff r s / (16 * (kRem r s + 1))))
      (Real.sqrt (1 / (4 * (aCoeff r s + 1))))))

lemma eta_pos {r s : ℕ} (hr : 0 < r) : 0 < eta r s := by
  have ha : 0 < aCoeff r s := aCoeff_pos hr
  have hk : 0 < kRem r s + 1 := by linarith [kRem_nonneg r s]
  have hπ : 0 < π / 4 := by positivity
  have h1 : 0 < 1 / ((s : ℝ) + 1) := by positivity
  have h2 : 0 < Real.sqrt (aCoeff r s / (16 * (kRem r s + 1))) := by positivity
  have h3 : 0 < Real.sqrt (1 / (4 * (aCoeff r s + 1))) := by positivity
  unfold eta
  exact lt_min hπ (lt_min h1 (lt_min h2 h3))

lemma eta_le_quarter (r s : ℕ) : eta r s ≤ π / 4 :=
  min_le_left _ _

lemma eta_le_inv (r s : ℕ) : eta r s ≤ 1 / ((s : ℝ) + 1) :=
  (min_le_right _ _).trans (min_le_left _ _)

lemma eta_sq_le_close {r s : ℕ} (hr : 0 < r) :
    (eta r s) ^ 2 ≤ aCoeff r s / (16 * (kRem r s + 1)) := by
  have ht : 0 ≤ aCoeff r s / (16 * (kRem r s + 1)) := by
    have ha : 0 < aCoeff r s := aCoeff_pos hr
    have hk : 0 < kRem r s + 1 := by linarith [kRem_nonneg r s]
    positivity
  have hle : eta r s ≤ Real.sqrt (aCoeff r s / (16 * (kRem r s + 1))) := by
    unfold eta
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsq := pow_le_pow_left₀ (eta_pos hr).le hle 2
  rw [Real.sq_sqrt ht] at hsq
  exact hsq

lemma eta_sq_le_small {r s : ℕ} (hr : 0 < r) :
    (eta r s) ^ 2 ≤ 1 / (4 * (aCoeff r s + 1)) := by
  have ht : 0 ≤ 1 / (4 * (aCoeff r s + 1)) := by
    have ha : 0 < aCoeff r s := aCoeff_pos hr
    positivity
  have hle : eta r s ≤ Real.sqrt (1 / (4 * (aCoeff r s + 1))) := by
    unfold eta
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsq := pow_le_pow_left₀ (eta_pos hr).le hle 2
  rw [Real.sq_sqrt ht] at hsq
  exact hsq

lemma angle_eta {r s : ℕ} {x : ℝ} (hx : |x| ≤ eta r s) : |(s : ℝ) * x| ≤ 1 := by
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hx' : |x| ≤ 1 / ((s : ℝ) + 1) := hx.trans (eta_le_inv r s)
  calc
    |(s : ℝ) * x| = (s : ℝ) * |x| := by rw [abs_mul, abs_of_nonneg hs]
    _ ≤ (s : ℝ) * (1 / ((s : ℝ) + 1)) := by
      gcongr
    _ ≤ 1 := by
      rw [mul_one_div]
      apply div_le_one_of_le₀
      · linarith
      · positivity

lemma rho_eta {r s : ℕ} (hr : 0 < r) {x y : ℝ} (hx : |x| ≤ eta r s) (hy : |y| ≤ eta r s) :
    x ^ 2 + y ^ 2 ≤ aCoeff r s / (8 * (kRem r s + 1)) ∧
      x ^ 2 + y ^ 2 ≤ 1 / (2 * (aCoeff r s + 1)) := by
  have hx2 : x ^ 2 ≤ (eta r s) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hy2 : y ^ 2 ≤ (eta r s) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hy 2
  have hsum : x ^ 2 + y ^ 2 ≤ 2 * (eta r s) ^ 2 := by linarith
  refine ⟨?_, ?_⟩
  · calc
      x ^ 2 + y ^ 2 ≤ 2 * (eta r s) ^ 2 := hsum
      _ ≤ 2 * (aCoeff r s / (16 * (kRem r s + 1))) := by gcongr; exact eta_sq_le_close hr
      _ = aCoeff r s / (8 * (kRem r s + 1)) := by field_simp; ring
  · calc
      x ^ 2 + y ^ 2 ≤ 2 * (eta r s) ^ 2 := hsum
      _ ≤ 2 * (1 / (4 * (aCoeff r s + 1))) := by gcongr; exact eta_sq_le_small hr
      _ = 1 / (2 * (aCoeff r s + 1)) := by field_simp; ring

lemma phi_pow_le_gauss {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s) {u v : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (hu : |u| ≤ eta r s * Real.sqrt (n : ℝ))
    (hv : |v| ≤ eta r s * Real.sqrt (n : ℝ)) :
    phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ^ (2 * n) ≤
      Real.exp (-(aCoeff r s / 4) * (u ^ 2 + v ^ 2)) := by
  set srt : ℝ := Real.sqrt (n : ℝ)
  have hsrt : srt ≠ 0 := (Real.sqrt_ne_zero (Nat.cast_nonneg n)).2
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn)
  have hx : |u / srt| ≤ eta r s := by
    rw [abs_div, abs_of_pos (Real.sqrt_pos.2 (by exact_mod_cast (Nat.succ_le_iff.mp hn) : (0 : ℝ) < n))]
    rw [div_le_iff₀ (Real.sqrt_pos.2 (by exact_mod_cast (Nat.succ_le_iff.mp hn) : (0 : ℝ) < n))]
    simpa [srt] using hu
  have hy : |v / srt| ≤ eta r s := by
    rw [abs_div, abs_of_pos (Real.sqrt_pos.2 (by exact_mod_cast (Nat.succ_le_iff.mp hn) : (0 : ℝ) < n))]
    rw [div_le_iff₀ (Real.sqrt_pos.2 (by exact_mod_cast (Nat.succ_le_iff.mp hn) : (0 : ℝ) < n))]
    simpa [srt] using hv
  have hρ := rho_eta hr hx hy
  have hangx := angle_eta hx
  have hangy := angle_eta hy
  have hpe := phi_pos_exp hrs hr hangx hangy hρ.1 hρ.2
  set ρ2 : ℝ := (u / srt) ^ 2 + (v / srt) ^ 2
  have hpow : (Real.exp (-(aCoeff r s / 8) * ρ2)) ^ (2 * n) =
      Real.exp ((2 * n : ℝ) * (-(aCoeff r s / 8) * ρ2)) := by
    rw [← Real.exp_log (pow_pos (Real.exp_pos _) (2 * n)), Real.log_pow, Real.log_exp]
    congr 1
    push_cast
    ring
  have hle := pow_le_pow_left₀ (hpe.1).le hpe.2 (2 * n)
  rw [hpow] at hle
  have harg : (2 * n : ℝ) * (-(aCoeff r s / 8) * ρ2) =
      -(aCoeff r s / 4) * (u ^ 2 + v ^ 2) := by
    have hρdiv : ρ2 = (u ^ 2 + v ^ 2) / (n : ℝ) := by
      simpa [ρ2, srt] using rho_div (u := u) (v := v) hn
    rw [hρdiv]
    have hnn : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
    field_simp [hnn]
    ring
  rw [harg] at hle
  simpa only [srt] using hle

lemma continuous_phi_pow_pair (r s n : ℕ) :
    Continuous fun p : ℝ × ℝ =>
      phi r s (p.1 / Real.sqrt (n : ℝ)) (p.2 / Real.sqrt (n : ℝ)) ^ (2 * n) := by
  unfold phi
  fun_prop

lemma tendsto_inner_fixed {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s) (R u : ℝ) :
    Tendsto
      (fun n : ℕ => ∫ v in (-R)..R,
        phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ^ (2 * n))
      Filter.atTop
      (nhds (∫ v in (-R)..R,
        Real.exp (-((aCoeff r s / 2) * (u ^ 2 + v ^ 2))))) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := -R) (b := R) (l := (Filter.atTop : Filter ℕ))
    (bound := fun _ => (1 : ℝ))
    (f := fun v => Real.exp (-((aCoeff r s / 2) * (u ^ 2 + v ^ 2))))
    (F := fun (n : ℕ) v =>
      phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ^ (2 * n))
    ?_ ?_ ?_ ?_
  · filter_upwards with n
    have hcont : Continuous fun v : ℝ =>
        phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ^ (2 * n) := by
      unfold phi
      fun_prop
    exact hcont.aestronglyMeasurable
  · filter_upwards with n
    refine Eventually.of_forall fun v _hv => ?_
    rw [Real.norm_eq_abs]
    exact phi_pow_abs_le_one r s n _ _
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun v _hv => tendsto_phi_pow hr hrs u v

lemma tendsto_square_fixed {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s) {R : ℝ} (hR : 0 ≤ R) :
    Tendsto
      (fun n : ℕ => ∫ u in (-R)..R, ∫ v in (-R)..R,
        phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ^ (2 * n))
      Filter.atTop
      (nhds (∫ u in (-R)..R, ∫ v in (-R)..R,
        Real.exp (-((aCoeff r s / 2) * (u ^ 2 + v ^ 2))))) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := -R) (b := R) (l := (Filter.atTop : Filter ℕ))
    (bound := fun _ => 2 * R)
    (f := fun u => ∫ v in (-R)..R,
      Real.exp (-((aCoeff r s / 2) * (u ^ 2 + v ^ 2))))
    (F := fun (n : ℕ) u => ∫ v in (-R)..R,
      phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ^ (2 * n))
    ?_ ?_ ?_ ?_
  · filter_upwards with n
    have hcont : Continuous fun u : ℝ => ∫ v in (-R)..R,
        phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ^ (2 * n) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun u v =>
          phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ^ (2 * n))
        (continuous_phi_pow_pair r s n) (-R) R
    exact hcont.aestronglyMeasurable
  · filter_upwards with n
    refine Eventually.of_forall fun u _hu => ?_
    rw [Real.norm_eq_abs]
    have hle := abs_integral_le_const (a := -R) (b := R) (C := 1)
      (f := fun v =>
        phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ^ (2 * n))
      (fun v => phi_pow_abs_le_one r s n _ _)
    rw [sub_neg_eq_add] at hle
    have hsum : R + R = 2 * R := by ring
    rw [hsum, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * R), one_mul] at hle
    exact hle
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun u _hu => tendsto_inner_fixed hr hrs R u

lemma tendsto_gauss_sq {c : ℝ} (hc : 0 < c) :
    Tendsto (fun R : ℝ => ∫ u in (-R)..R, ∫ v in (-R)..R,
        Real.exp (-c * (u ^ 2 + v ^ 2))) Filter.atTop (nhds (π / c)) := by
  have h := tendsto_sq_interval_gaussian hc
  simp_rw [← sq_gaussian] at h
  exact h

lemma tendsto_peak_gauss {r s : ℕ} (hr : 0 < r) :
    Tendsto (fun R : ℝ => ∫ u in (-R)..R, ∫ v in (-R)..R,
        Real.exp (-(aCoeff r s / 2) * (u ^ 2 + v ^ 2)))
      Filter.atTop (nhds (2 * π / aCoeff r s)) := by
  have hc : 0 < aCoeff r s / 2 := by
    have ha := aCoeff_pos (s := s) hr
    positivity
  have h := tendsto_gauss_sq hc
  have hπ : π / (aCoeff r s / 2) = 2 * π / aCoeff r s := by field_simp
  simpa [hπ] using h

lemma tendsto_dom_gauss {r s : ℕ} (hr : 0 < r) :
    Tendsto (fun R : ℝ => ∫ u in (-R)..R, ∫ v in (-R)..R,
        Real.exp (-(aCoeff r s / 4) * (u ^ 2 + v ^ 2)))
      Filter.atTop (nhds (4 * π / aCoeff r s)) := by
  have hc : 0 < aCoeff r s / 4 := by
    have ha := aCoeff_pos (s := s) hr
    positivity
  have h := tendsto_gauss_sq hc
  have hπ : π / (aCoeff r s / 4) = 4 * π / aCoeff r s := by field_simp
  simpa [hπ] using h

lemma square_exp_assoc (c R : ℝ) :
    ∫ u in (-R)..R, ∫ v in (-R)..R, Real.exp (-(c * (u ^ 2 + v ^ 2))) =
      ∫ u in (-R)..R, ∫ v in (-R)..R, Real.exp (-c * (u ^ 2 + v ^ 2)) := by
  refine intervalIntegral.integral_congr fun u _ => ?_
  refine intervalIntegral.integral_congr fun v _ => ?_
  rw [neg_mul]

lemma line_split {a b c d : ℝ} (f : ℝ → ℝ)
    (hab : IntervalIntegrable f volume a b) (hbc : IntervalIntegrable f volume b c)
    (hcd : IntervalIntegrable f volume c d) :
    (∫ x in a..d, f x) =
      (∫ x in a..b, f x) + (∫ x in b..c, f x) + (∫ x in c..d, f x) := by
  have hmid : IntervalIntegrable f volume a c := hab.trans hbc
  rw [(intervalIntegral.integral_add_adjacent_intervals hmid hcd).symm,
    (intervalIntegral.integral_add_adjacent_intervals hab hbc).symm]

lemma section_integrable {f : ℝ → ℝ → ℝ}
    (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2) (u a b : ℝ) :
    IntervalIntegrable (fun v => f u v) volume a b := by
  have hpair : Continuous fun v : ℝ => (u, v) := by fun_prop
  exact (hf.comp hpair).intervalIntegrable a b

lemma inner_continuous {f : ℝ → ℝ → ℝ}
    (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2) (a b : ℝ) :
    Continuous fun u : ℝ => ∫ v in a..b, f u v :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := f) hf a b

lemma rect_mono {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) {f g : ℝ → ℝ → ℝ}
    (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2)
    (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)
    (hle : ∀ u v, a ≤ u → u ≤ b → c ≤ v → v ≤ d → f u v ≤ g u v) :
    ∫ u in a..b, ∫ v in c..d, f u v ≤ ∫ u in a..b, ∫ v in c..d, g u v := by
  have hinner : ∀ u, a ≤ u → u ≤ b →
      ∫ v in c..d, f u v ≤ ∫ v in c..d, g u v := by
    intro u hu1 hu2
    refine intervalIntegral.integral_mono_on hcd (section_integrable hf u c d)
      (section_integrable hg u c d) ?_
    intro v hv
    exact hle u v hu1 hu2 hv.1 hv.2
  refine intervalIntegral.integral_mono_on hab
    ((inner_continuous hf c d).intervalIntegrable a b)
    ((inner_continuous hg c d).intervalIntegrable a b) ?_
  intro u hu
  exact hinner u hu.1 hu.2

lemma rect_nonneg {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (f : ℝ → ℝ → ℝ)
    (h0 : ∀ u v, 0 ≤ f u v) :
    0 ≤ ∫ u in a..b, ∫ v in c..d, f u v := by
  refine intervalIntegral.integral_nonneg hab ?_
  intro u _hu
  refine intervalIntegral.integral_nonneg hcd ?_
  intro v _hv
  exact h0 u v

lemma sq_split {A R : ℝ} (f : ℝ → ℝ → ℝ)
    (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2) :
    (∫ u in (-A)..A, ∫ v in (-A)..A, f u v) =
      (∫ u in (-R)..R, ∫ v in (-R)..R, f u v) +
        ((∫ u in (-A)..(-R), ∫ v in (-A)..A, f u v) +
          (∫ u in R..A, ∫ v in (-A)..A, f u v) +
          (∫ u in (-R)..R, ∫ v in (-A)..(-R), f u v) +
          (∫ u in (-R)..R, ∫ v in R..A, f u v)) := by
  have hv : ∀ u a b, IntervalIntegrable (fun v => f u v) volume a b :=
    fun u a b => section_integrable hf u a b
  have hvin : ∀ u, (∫ v in (-A)..A, f u v) =
      (∫ v in (-A)..(-R), f u v) + (∫ v in (-R)..R, f u v) + (∫ v in R..A, f u v) :=
    fun u => line_split (fun v => f u v) (hv u (-A) (-R)) (hv u (-R) R) (hv u R A)
  have hL : Continuous fun u => ∫ v in (-A)..(-R), f u v := inner_continuous hf (-A) (-R)
  have hM : Continuous fun u => ∫ v in (-R)..R, f u v := inner_continuous hf (-R) R
  have hRt : Continuous fun u => ∫ v in R..A, f u v := inner_continuous hf R A
  have hAll : Continuous fun u => ∫ v in (-A)..A, f u v := inner_continuous hf (-A) A
  have houter := line_split (fun u => ∫ v in (-A)..A, f u v)
    (hAll.intervalIntegrable (-A) (-R)) (hAll.intervalIntegrable (-R) R)
    (hAll.intervalIntegrable R A)
  have hmid : (∫ u in (-R)..R, ∫ v in (-A)..A, f u v) =
      (∫ u in (-R)..R, ∫ v in (-A)..(-R), f u v) +
        (∫ u in (-R)..R, ∫ v in (-R)..R, f u v) +
        (∫ u in (-R)..R, ∫ v in R..A, f u v) := by
    simp_rw [hvin]
    have hLM : IntervalIntegrable
        (fun u => (∫ v in (-A)..(-R), f u v) + ∫ v in (-R)..R, f u v) volume (-R) R :=
      (hL.intervalIntegrable (-R) R).add (hM.intervalIntegrable (-R) R)
    have h1 := intervalIntegral.integral_add (μ := volume) hLM
      (Continuous.intervalIntegrable (μ := volume) hRt (-R) R)
    have h2 := intervalIntegral.integral_add (μ := volume)
      (Continuous.intervalIntegrable (μ := volume) hL (-R) R)
      (Continuous.intervalIntegrable (μ := volume) hM (-R) R)
    rw [h1, h2]
  rw [houter, hmid]
  ring

lemma frame_le {A R : ℝ} (hR : 0 ≤ R) (hA : R ≤ A) {f g : ℝ → ℝ → ℝ}
    (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2)
    (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)
    (hle : ∀ u v, |u| ≤ A → |v| ≤ A → f u v ≤ g u v) :
    (∫ u in (-A)..A, ∫ v in (-A)..A, f u v) -
        (∫ u in (-R)..R, ∫ v in (-R)..R, f u v) ≤
      (∫ u in (-A)..A, ∫ v in (-A)..A, g u v) -
        (∫ u in (-R)..R, ∫ v in (-R)..R, g u v) := by
  have hordL : -A ≤ -R := by linarith
  have hordM : -R ≤ R := by linarith
  have hordR : R ≤ A := hA
  have habsL : ∀ u, -A ≤ u → u ≤ -R → |u| ≤ A := by
    intro u hu1 hu2
    rw [abs_of_nonpos (hu2.trans (by linarith : -R ≤ 0))]
    linarith
  have habsR : ∀ u, R ≤ u → u ≤ A → |u| ≤ A := by
    intro u hu1 hu2
    rw [abs_of_nonneg (hR.trans hu1)]
    linarith
  have habsM : ∀ u, -R ≤ u → u ≤ R → |u| ≤ A := by
    intro u hu1 hu2
    have : |u| ≤ R := abs_le.2 ⟨hu1, hu2⟩
    exact this.trans hA
  have habsV : ∀ v, -A ≤ v → v ≤ A → |v| ≤ A := fun v hv1 hv2 => abs_le.2 ⟨hv1, hv2⟩
  have h1 := rect_mono hordL (by linarith : -A ≤ A) hf hg
    (fun u v hu1 hu2 hv1 hv2 => hle u v (habsL u hu1 hu2) (habsV v hv1 hv2))
  have h2 := rect_mono hordR (by linarith : -A ≤ A) hf hg
    (fun u v hu1 hu2 hv1 hv2 => hle u v (habsR u hu1 hu2) (habsV v hv1 hv2))
  have h3 := rect_mono hordM hordL hf hg
    (fun u v hu1 hu2 hv1 hv2 => hle u v (habsM u hu1 hu2) (habsL v hv1 hv2))
  have h4 := rect_mono hordM hordR hf hg
    (fun u v hu1 hu2 hv1 hv2 => hle u v (habsM u hu1 hu2) (habsR v hv1 hv2))
  have hfdiff := sq_split (A := A) (R := R) f hf
  have hgdiff := sq_split (A := A) (R := R) g hg
  rw [hfdiff, hgdiff]
  linarith

lemma sq_mono_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : A ≤ B) (f : ℝ → ℝ → ℝ)
    (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2) (h0 : ∀ u v, 0 ≤ f u v) :
    (∫ u in (-A)..A, ∫ v in (-A)..A, f u v) ≤
      (∫ u in (-B)..B, ∫ v in (-B)..B, f u v) := by
  have hsplit := sq_split (A := B) (R := A) f hf
  have hnn1 := rect_nonneg (a := -B) (b := -A) (by linarith) (c := -B) (d := B) (by linarith) f h0
  have hnn2 := rect_nonneg (a := A) (b := B) hB (c := -B) (d := B) (by linarith) f h0
  have hnn3 := rect_nonneg (a := -A) (b := A) (by linarith) (c := -B) (d := -A) (by linarith) f h0
  have hnn4 := rect_nonneg (a := -A) (b := A) (by linarith) (c := A) (d := B) hB f h0
  rw [hsplit]
  linarith

lemma continuous_gauss (c : ℝ) :
    Continuous fun p : ℝ × ℝ => Real.exp (-c * (p.1 ^ 2 + p.2 ^ 2)) := by
  fun_prop

lemma sq_le_gauss {c : ℝ} (hc : 0 < c) {A : ℝ} (hA : 0 ≤ A) :
    (∫ u in (-A)..A, ∫ v in (-A)..A, Real.exp (-c * (u ^ 2 + v ^ 2))) ≤ π / c := by
  have hmono : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y →
      (∫ u in (-x)..x, ∫ v in (-x)..x, Real.exp (-c * (u ^ 2 + v ^ 2))) ≤
        (∫ u in (-y)..y, ∫ v in (-y)..y, Real.exp (-c * (u ^ 2 + v ^ 2))) :=
    fun hx hxy => sq_mono_nonneg hx hxy _ (continuous_gauss c) (fun _ _ => (Real.exp_pos _).le)
  by_contra hle
  have hlt : π / c < (∫ u in (-A)..A, ∫ v in (-A)..A,
      Real.exp (-c * (u ^ 2 + v ^ 2))) := lt_of_not_ge hle
  have hε : 0 < ((∫ u in (-A)..A, ∫ v in (-A)..A,
      Real.exp (-c * (u ^ 2 + v ^ 2))) - π / c) := sub_pos.mpr hlt
  obtain ⟨B, hB⟩ := (Metric.tendsto_atTop.1 (tendsto_gauss_sq hc)) _ hε
  have hdist := hB (max A B) (le_max_right A B)
  rw [Real.dist_eq] at hdist
  have hge := hmono hA (le_max_left A B)
  have hpos : 0 ≤ ((∫ u in (-max A B)..(max A B), ∫ v in (-max A B)..(max A B),
      Real.exp (-c * (u ^ 2 + v ^ 2))) - π / c) := by
    linarith
  rw [abs_of_nonneg hpos] at hdist
  linarith

lemma tendsto_eta_scaled {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s) :
    Tendsto (fun n : ℕ => (n : ℝ) * ∫ x in (-eta r s)..(eta r s),
        ∫ y in (-eta r s)..(eta r s), phi r s x y ^ (2 * n))
      Filter.atTop (nhds (2 * π / aCoeff r s)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [← Filter.eventually_atTop]
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨Rp, hRp⟩ := (Metric.tendsto_atTop.1 (tendsto_peak_gauss (s := s) hr)) (ε / 3) hε3
  obtain ⟨Rd, hRd⟩ := (Metric.tendsto_atTop.1 (tendsto_dom_gauss (s := s) hr)) (ε / 3) hε3
  let R : ℝ := max 0 (max Rp Rd)
  have hR0 : 0 ≤ R := le_max_left _ _
  have hRpR : Rp ≤ R := (le_max_left Rp Rd).trans (le_max_right 0 _)
  have hRdR : Rd ≤ R := (le_max_right Rp Rd).trans (le_max_right 0 _)
  have hc4 : 0 < aCoeff r s / 4 := by
    have ha := aCoeff_pos (s := s) hr
    positivity
  have hpeakClose : |(∫ u in (-R)..R, ∫ v in (-R)..R,
      Real.exp (-(aCoeff r s / 2) * (u ^ 2 + v ^ 2))) - 2 * π / aCoeff r s| < ε / 3 := by
    rw [← Real.dist_eq]
    exact hRp R hRpR
  have hdomClose : |(∫ u in (-R)..R, ∫ v in (-R)..R,
      Real.exp (-(aCoeff r s / 4) * (u ^ 2 + v ^ 2))) - 4 * π / aCoeff r s| < ε / 3 := by
    rw [← Real.dist_eq]
    exact hRd R hRdR
  have hdomLe : (∫ u in (-R)..R, ∫ v in (-R)..R,
      Real.exp (-(aCoeff r s / 4) * (u ^ 2 + v ^ 2))) ≤ 4 * π / aCoeff r s := by
    have hle := sq_le_gauss hc4 hR0
    have hπ : π / (aCoeff r s / 4) = 4 * π / aCoeff r s := by field_simp
    simpa [hπ] using hle
  have htail : 4 * π / aCoeff r s - (∫ u in (-R)..R, ∫ v in (-R)..R,
      Real.exp (-(aCoeff r s / 4) * (u ^ 2 + v ^ 2))) < ε / 3 := by
    rw [← Real.dist_eq] at hdomClose
    rw [Real.dist_eq, abs_sub_comm] at hdomClose
    rw [abs_of_nonneg (sub_nonneg.2 hdomLe)] at hdomClose
    exact hdomClose
  have hfix := tendsto_square_fixed hr hrs hR0
  have hball := Metric.ball_mem_nhds ((∫ u in (-R)..R, ∫ v in (-R)..R,
    Real.exp (-((aCoeff r s / 2) * (u ^ 2 + v ^ 2))))) hε3
  have hbig : Tendsto (fun n : ℕ => eta r s * Real.sqrt (n : ℝ)) Filter.atTop Filter.atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (eta_pos hr)
  filter_upwards [Filter.eventually_ge_atTop 1, hbig.eventually (Filter.eventually_ge_atTop R),
      hfix.eventually hball] with n hn hA hclose
  rw [Real.dist_eq] at hclose
  set A : ℝ := eta r s * Real.sqrt (n : ℝ)
  have hAR : R ≤ A := hA
  have hscale := rescale_square (η := eta r s) hn
    (fun x y => phi r s x y ^ (2 * n))
  have hFn : Continuous fun p : ℝ × ℝ =>
      phi r s (p.1 / Real.sqrt (n : ℝ)) (p.2 / Real.sqrt (n : ℝ)) ^ (2 * n) :=
    continuous_phi_pow_pair r s n
  have hGn : Continuous fun p : ℝ × ℝ =>
      Real.exp (-(aCoeff r s / 4) * (p.1 ^ 2 + p.2 ^ 2)) := continuous_gauss (aCoeff r s / 4)
  have hleFV : ∀ u v, |u| ≤ A → |v| ≤ A →
      phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ^ (2 * n) ≤
        Real.exp (-(aCoeff r s / 4) * (u ^ 2 + v ^ 2)) :=
    fun u v hu hv => phi_pow_le_gauss hr hrs hn hu hv
  have hframe := frame_le hR0 hAR hFn hGn hleFV
  have hGmono := sq_mono_nonneg hR0 hAR
    (fun u v => Real.exp (-(aCoeff r s / 4) * (u ^ 2 + v ^ 2))) hGn
    (fun _ _ => (Real.exp_pos _).le)
  have hGbig : (∫ u in (-A)..A, ∫ v in (-A)..A,
      Real.exp (-(aCoeff r s / 4) * (u ^ 2 + v ^ 2))) ≤ 4 * π / aCoeff r s := by
    have hle := sq_le_gauss hc4 (hR0.trans hAR)
    have hπ : π / (aCoeff r s / 4) = 4 * π / aCoeff r s := by field_simp
    simpa [hπ] using hle
  have hFmono := sq_mono_nonneg hR0 hAR
    (fun u v => phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ^ (2 * n))
    hFn (fun u v => phi_pow_nonneg r s n (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)))
  have hassoc := square_exp_assoc (aCoeff r s / 2) R
  set target : ℝ := 2 * π / aCoeff r s
  set mass : ℝ := 4 * π / aCoeff r s
  set Fbig : ℝ := ∫ u in (-A)..A, ∫ v in (-A)..A,
    phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ^ (2 * n)
  set Fsmall : ℝ := ∫ u in (-R)..R, ∫ v in (-R)..R,
    phi r s (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ^ (2 * n)
  set Gbig : ℝ := ∫ u in (-A)..A, ∫ v in (-A)..A,
    Real.exp (-(aCoeff r s / 4) * (u ^ 2 + v ^ 2))
  set Gsmall : ℝ := ∫ u in (-R)..R, ∫ v in (-R)..R,
    Real.exp (-(aCoeff r s / 4) * (u ^ 2 + v ^ 2))
  set Pneg : ℝ := ∫ u in (-R)..R, ∫ v in (-R)..R,
    Real.exp (-((aCoeff r s / 2) * (u ^ 2 + v ^ 2)))
  set Pmul : ℝ := ∫ u in (-R)..R, ∫ v in (-R)..R,
    Real.exp (-(aCoeff r s / 2) * (u ^ 2 + v ^ 2))
  have hPeq : Pneg = Pmul := hassoc
  have hinner : |Fsmall - target| < ε / 3 + ε / 3 := by
    have hsub : Fsmall - target = (Fsmall - Pneg) + (Pneg - target) := by ring
    have hpeak' : |Pneg - target| < ε / 3 := by
      rw [hPeq]
      exact hpeakClose
    calc
      |Fsmall - target| = |(Fsmall - Pneg) + (Pneg - target)| := by rw [hsub]
      _ ≤ |Fsmall - Pneg| + |Pneg - target| := abs_add_le _ _
      _ < ε / 3 + ε / 3 := add_lt_add hclose hpeak'
  have hframeAbs : Fbig - Fsmall < ε / 3 := by
    have hGdiff : Gbig - Gsmall ≤ mass - Gsmall := by linarith
    exact lt_of_le_of_lt (hframe.trans hGdiff) htail
  have hnn : 0 ≤ Fbig - Fsmall := by linarith
  have hgoal : |Fbig - target| < ε := by
    have hsub : Fbig - target = (Fbig - Fsmall) + (Fsmall - target) := by ring
    rw [hsub]
    calc
      |(Fbig - Fsmall) + (Fsmall - target)| ≤ |Fbig - Fsmall| + |Fsmall - target| :=
        abs_add_le _ _
      _ = (Fbig - Fsmall) + |Fsmall - target| := by rw [abs_of_nonneg hnn]
      _ < ε / 3 + (ε / 3 + ε / 3) := add_lt_add hframeAbs hinner
      _ = ε := by ring
  rw [Real.dist_eq, hscale]
  simp only [Fbig, A, neg_mul_eq_neg_mul] at hgoal
  exact hgoal


lemma continuous_phi (r s : ℕ) : Continuous fun p : ℝ × ℝ => phi r s p.1 p.2 := by
  unfold phi
  fun_prop

lemma continuous_phi_pow (r s n : ℕ) :
    Continuous fun p : ℝ × ℝ => phi r s p.1 p.2 ^ (2 * n) := by
  unfold phi
  fun_prop

lemma rect_const {a b c d C : ℝ} :
    ∫ _ in a..b, ∫ _ in c..d, (C : ℝ) = C * (b - a) * (d - c) := by
  simp_rw [intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma rect_le_const {a b c d C : ℝ} (hab : a ≤ b) (hcd : c ≤ d) {f : ℝ → ℝ → ℝ}
    (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2)
    (hle : ∀ u v, a ≤ u → u ≤ b → c ≤ v → v ≤ d → f u v ≤ C) :
    ∫ u in a..b, ∫ v in c..d, f u v ≤ C * (b - a) * (d - c) := by
  have hg : Continuous fun p : ℝ × ℝ => (C : ℝ) := continuous_const
  have hmono := rect_mono hab hcd hf hg hle
  rw [rect_const] at hmono
  exact hmono

lemma small_piZ {x : ℝ} (hx : |x| ≤ π / 4) (h : ∃ k : ℤ, (k : ℝ) * π = x) : x = 0 := by
  obtain ⟨k, hk⟩ := h
  have habs : |(k : ℝ)| * π ≤ π / 4 := by
    calc
      |(k : ℝ)| * π = |(k : ℝ) * π| := by rw [abs_mul, abs_of_pos pi_pos]
      _ = |x| := by rw [hk]
      _ ≤ π / 4 := hx
  have hk14 : |(k : ℝ)| ≤ 1 / 4 := by
    apply le_of_mul_le_mul_right _ pi_pos
    calc
      |(k : ℝ)| * π ≤ π / 4 := habs
      _ = (1 / 4) * π := by ring
  have hk0 : k = 0 := by
    by_contra hne
    have hone : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hne
    linarith
  rw [hk0] at hk
  simp at hk
  exact hk.symm

lemma abs_phi_eq_one_small {r s : ℕ} (hcop : Nat.Coprime r s) {x y : ℝ}
    (hx : |x| ≤ π / 4) (hy : |y| ≤ π / 4) (h : |phi r s x y| = 1) : x = 0 ∧ y = 0 := by
  obtain ⟨hxpi, hypi⟩ := abs_phi_eq_one hcop h
  exact ⟨small_piZ hx hxpi, small_piZ hy hypi⟩

noncomputable def delta : ℝ := π / 4

lemma small_square_lt {r s : ℕ} (hcop : Nat.Coprime r s) {a b c d : ℝ}
    (hx : ∀ u, a ≤ u → u ≤ b → |u| ≤ delta)
    (hy : ∀ v, c ≤ v → v ≤ d → |v| ≤ delta)
    (hz : ∀ u v, a ≤ u → u ≤ b → c ≤ v → v ≤ d → u ≠ 0 ∨ v ≠ 0)
    {u v : ℝ} (hu1 : a ≤ u) (hu2 : u ≤ b) (hv1 : c ≤ v) (hv2 : v ≤ d) :
    |phi r s u v| < 1 := by
  apply lt_of_le_of_ne (abs_phi_le_one r s u v)
  intro heq
  have hδ : delta = π / 4 := rfl
  obtain ⟨hu, hv⟩ := abs_phi_eq_one_small hcop (by simpa [hδ] using hx u hu1 hu2)
    (by simpa [hδ] using hy v hv1 hv2) heq
  rcases hz u v hu1 hu2 hv1 hv2 with h | h
  · exact h hu
  · exact h hv

lemma tendsto_rect_decay {r s : ℕ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hlt : ∀ u v, a ≤ u → u ≤ b → c ≤ v → v ≤ d → |phi r s u v| < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) * ∫ u in a..b, ∫ v in c..d, phi r s u v ^ (2 * n))
      Filter.atTop (nhds 0) := by
  let K : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc c d
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hne : K.Nonempty := (Set.nonempty_Icc.2 hab).prod (Set.nonempty_Icc.2 hcd)
  obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn hne (continuous_phi r s).abs.continuousOn
  rw [isMaxOn_iff] at hmax
  have hp1 : a ≤ p.1 ∧ p.1 ≤ b := Set.mem_Icc.mp (Set.mem_prod.mp hp).1
  have hp2 : c ≤ p.2 ∧ p.2 ≤ d := Set.mem_Icc.mp (Set.mem_prod.mp hp).2
  set ρ : ℝ := |phi r s p.1 p.2|
  have hρlt : ρ < 1 := hlt p.1 p.2 hp1.1 hp1.2 hp2.1 hp2.2
  have hρ0 : 0 ≤ ρ := abs_nonneg _
  have hρ2 : ρ ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one ρ).2 (by simpa [abs_of_nonneg hρ0] using hρlt)
  have hdecay : Tendsto (fun n : ℕ => (n : ℝ) * (ρ ^ 2) ^ n) Filter.atTop (nhds 0) :=
    tendsto_self_mul_const_pow_of_lt_one (sq_nonneg ρ) hρ2
  set area : ℝ := (b - a) * (d - c)
  have harea0 : 0 ≤ area := mul_nonneg (sub_nonneg.2 hab) (sub_nonneg.2 hcd)
  have hup : Tendsto (fun n : ℕ => area * ((n : ℝ) * (ρ ^ 2) ^ n)) Filter.atTop (nhds 0) := by
    have hmul := (tendsto_const_nhds (x := area)).mul hdecay
    simpa [mul_zero] using hmul
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hup) ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hnn : 0 ≤ (n : ℝ) * ∫ u in a..b, ∫ v in c..d, phi r s u v ^ (2 * n) :=
    mul_nonneg (Nat.cast_nonneg _)
      (rect_nonneg hab hcd (fun u v => phi r s u v ^ (2 * n))
        (fun u v => phi_pow_nonneg r s n u v))
  have hpoint : ∀ u v, a ≤ u → u ≤ b → c ≤ v → v ≤ d →
      phi r s u v ^ (2 * n) ≤ ρ ^ (2 * n) := by
    intro u v hu1 hu2 hv1 hv2
    have hleρ : |phi r s u v| ≤ ρ :=
      hmax (u, v) (Set.mk_mem_prod (Set.mem_Icc.mpr ⟨hu1, hu2⟩)
        (Set.mem_Icc.mpr ⟨hv1, hv2⟩))
    calc
      phi r s u v ^ (2 * n) = |phi r s u v| ^ (2 * n) := by
        rw [← abs_of_nonneg (phi_pow_nonneg r s n u v), abs_pow]
      _ ≤ ρ ^ (2 * n) := pow_le_pow_left₀ (abs_nonneg _) hleρ _
  have hint := rect_le_const hab hcd (f := fun u v => phi r s u v ^ (2 * n))
    (continuous_phi_pow r s n) hpoint
  have harea : ρ ^ (2 * n) * (b - a) * (d - c) = ρ ^ (2 * n) * area := by
    simp [area]
    ring
  rw [harea] at hint
  have hstep := mul_le_mul_of_nonneg_left hint (Nat.cast_nonneg n)
  have hpow : ρ ^ (2 * n) = (ρ ^ 2) ^ n := pow_mul ρ 2 n
  have hle : (n : ℝ) * ∫ u in a..b, ∫ v in c..d, phi r s u v ^ (2 * n) ≤
      area * ((n : ℝ) * (ρ ^ 2) ^ n) := by
    calc
      (n : ℝ) * ∫ u in a..b, ∫ v in c..d, phi r s u v ^ (2 * n) ≤
          (n : ℝ) * (ρ ^ (2 * n) * area) := hstep
      _ = area * ((n : ℝ) * (ρ ^ 2) ^ n) := by rw [hpow]; ring
  have hup0 : 0 ≤ area * ((n : ℝ) * (ρ ^ 2) ^ n) :=
    mul_nonneg harea0 (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sq_nonneg ρ) _))
  have hdist := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hup0] at hdist
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  exact hle.trans_lt hdist

lemma tendsto_delta_box {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s) (hcop : Nat.Coprime r s) :
    Tendsto (fun n : ℕ => (n : ℝ) * ∫ x in (-delta)..delta, ∫ y in (-delta)..delta,
        phi r s x y ^ (2 * n)) Filter.atTop (nhds (2 * π / aCoeff r s)) := by
  have hη : 0 < eta r s := eta_pos hr
  have hηle : eta r s ≤ delta := by simpa [delta] using eta_le_quarter r s
  have hD : -delta ≤ delta := by
    have h0 : 0 ≤ delta := by unfold delta; linarith [pi_pos]
    linarith
  have hL : -delta ≤ -(eta r s) := by linarith
  have hM : -(eta r s) ≤ eta r s := by linarith
  have hyD : ∀ v, -delta ≤ v → v ≤ delta → |v| ≤ delta := fun v hv1 hv2 =>
    abs_le.mpr ⟨hv1, hv2⟩
  have hxM : ∀ u, -(eta r s) ≤ u → u ≤ eta r s → |u| ≤ delta := fun u hu1 hu2 =>
    (abs_le.mpr ⟨hu1, hu2⟩).trans hηle
  have hxL : ∀ u, -delta ≤ u → u ≤ -(eta r s) → |u| ≤ delta := by
    intro u _ hu2
    have hu0 : u ≤ 0 := by linarith [hη, hu2]
    rw [abs_of_nonpos hu0]
    linarith
  have hxR : ∀ u, eta r s ≤ u → u ≤ delta → |u| ≤ delta := by
    intro u hu1 _
    rw [abs_of_nonneg (hη.le.trans hu1)]
    linarith
  have hyB : ∀ v, -delta ≤ v → v ≤ -(eta r s) → |v| ≤ delta := by
    intro v _ hv2
    have hv0 : v ≤ 0 := by linarith [hη, hv2]
    rw [abs_of_nonpos hv0]
    linarith
  have hyT : ∀ v, eta r s ≤ v → v ≤ delta → |v| ≤ delta := by
    intro v hv1 _
    rw [abs_of_nonneg (hη.le.trans hv1)]
    linarith
  have hzL : ∀ u v, -delta ≤ u → u ≤ -(eta r s) → -delta ≤ v → v ≤ delta →
      u ≠ 0 ∨ v ≠ 0 := by
    intro u _ _ hu2 _ _
    exact Or.inl (by intro h; linarith [hη, hu2, h])
  have hzR : ∀ u v, eta r s ≤ u → u ≤ delta → -delta ≤ v → v ≤ delta →
      u ≠ 0 ∨ v ≠ 0 := by
    intro u _ hu1 _ _ _
    exact Or.inl (by intro h; linarith [hη, hu1, h])
  have hzB : ∀ u v, -(eta r s) ≤ u → u ≤ eta r s → -delta ≤ v → v ≤ -(eta r s) →
      u ≠ 0 ∨ v ≠ 0 := by
    intro _ v _ _ _ hv2
    exact Or.inr (by intro h; linarith [hη, hv2, h])
  have hzT : ∀ u v, -(eta r s) ≤ u → u ≤ eta r s → eta r s ≤ v → v ≤ delta →
      u ≠ 0 ∨ v ≠ 0 := by
    intro _ v _ _ hv1 _
    exact Or.inr (by intro h; linarith [hη, hv1, h])
  have h1 := tendsto_rect_decay hL hD fun u v hu1 hu2 hv1 hv2 =>
    small_square_lt hcop hxL hyD hzL hu1 hu2 hv1 hv2
  have h2 := tendsto_rect_decay hηle hD fun u v hu1 hu2 hv1 hv2 =>
    small_square_lt hcop hxR hyD hzR hu1 hu2 hv1 hv2
  have h3 := tendsto_rect_decay hM hL fun u v hu1 hu2 hv1 hv2 =>
    small_square_lt hcop hxM hyB hzB hu1 hu2 hv1 hv2
  have h4 := tendsto_rect_decay hM hηle fun u v hu1 hu2 hv1 hv2 =>
    small_square_lt hcop hxM hyT hzT hu1 hu2 hv1 hv2
  have hsum := (tendsto_eta_scaled hr hrs).add (((h1.add h2).add h3).add h4)
  simp only [add_zero] at hsum
  refine hsum.congr fun n => ?_
  have hs := sq_split (A := delta) (R := eta r s)
    (fun x y => phi r s x y ^ (2 * n)) (continuous_phi_pow r s n)
  set S : ℝ := ∫ x in (-(eta r s))..(eta r s), ∫ y in (-(eta r s))..(eta r s),
    phi r s x y ^ (2 * n)
  set Lft : ℝ := ∫ x in (-delta)..(-(eta r s)), ∫ y in (-delta)..delta, phi r s x y ^ (2 * n)
  set Rgt : ℝ := ∫ x in (eta r s)..delta, ∫ y in (-delta)..delta, phi r s x y ^ (2 * n)
  set Bot : ℝ := ∫ x in (-(eta r s))..(eta r s),
    ∫ y in (-delta)..(-(eta r s)), phi r s x y ^ (2 * n)
  set Top : ℝ := ∫ x in (-(eta r s))..(eta r s),
    ∫ y in (eta r s)..delta, phi r s x y ^ (2 * n)
  set Big : ℝ := ∫ x in (-delta)..delta, ∫ y in (-delta)..delta, phi r s x y ^ (2 * n)
  have hs' : Big = S + (((Lft + Rgt) + Bot) + Top) := hs
  rw [hs']
  ring

lemma shift_square {c d dlt : ℝ} {f g : ℝ → ℝ → ℝ}
    (hfg : ∀ t u, f (c + t) (d + u) = g t u) :
    ∫ x in (c + (-dlt))..(c + dlt), ∫ y in (d + (-dlt))..(d + dlt), f x y =
      ∫ t in (-dlt)..dlt, ∫ u in (-dlt)..dlt, g t u := by
  have hinner : ∀ x, ∫ y in (d + (-dlt))..(d + dlt), f x y =
      ∫ u in (-dlt)..dlt, f x (d + u) := by
    intro x
    exact (intervalIntegral.integral_comp_add_left (a := -dlt) (b := dlt)
      (fun y => f x y) d).symm
  simp_rw [hinner]
  have houter :=
    (intervalIntegral.integral_comp_add_left (a := -dlt) (b := dlt)
      (fun x => ∫ u in (-dlt)..dlt, f x (d + u)) c).symm
  rw [houter]
  refine intervalIntegral.integral_congr fun t _ => ?_
  refine intervalIntegral.integral_congr fun u _ => ?_
  exact hfg t u

noncomputable def cut : ℕ → ℝ
  | 0 => π / 2
  | 1 => 3 * π / 4
  | 2 => 5 * π / 4
  | 3 => 7 * π / 4
  | 4 => 9 * π / 4
  | _ => 5 * π / 2

lemma cut_succ_le (k : ℕ) (hk : k < 5) : cut k ≤ cut (k + 1) := by
  interval_cases k <;> simp [cut] <;> linarith [pi_pos]

lemma cut_bounds (i : ℕ) (hi : i ≤ 5) : π / 2 ≤ cut i ∧ cut i ≤ 5 * π / 2 := by
  interval_cases i <;> refine ⟨?_, ?_⟩ <;> simp [cut] <;> linarith [pi_pos]

lemma cell_pi (r s n : ℕ) :
    ∫ x in cut 1..cut 2, ∫ y in cut 1..cut 2, phi r s x y ^ (2 * n) =
      ∫ t in (-delta)..delta, ∫ u in (-delta)..delta, phi r s t u ^ (2 * n) := by
  have hc1 : cut 1 = π + (-delta) := by simp [cut, delta]; ring
  have hc2 : cut 2 = π + delta := by simp [cut, delta]; ring
  rw [hc1, hc2]
  exact shift_square fun t u => phi_shift_pi_pow r s n t u

lemma cell_two (r s n : ℕ) :
    ∫ x in cut 3..cut 4, ∫ y in cut 3..cut 4, phi r s x y ^ (2 * n) =
      ∫ t in (-delta)..delta, ∫ u in (-delta)..delta, phi r s t u ^ (2 * n) := by
  have hc1 : cut 3 = 2 * π + (-delta) := by simp [cut, delta]; ring
  have hc2 : cut 4 = 2 * π + delta := by simp [cut, delta]; ring
  rw [hc1, hc2]
  exact shift_square fun t u => phi_shift_two_pow r s n t u

lemma cell_pi_two {r s : ℕ} (hr : Odd r) (hs : Odd s) (n : ℕ) :
    ∫ x in cut 1..cut 2, ∫ y in cut 3..cut 4, phi r s x y ^ (2 * n) =
      ∫ t in (-delta)..delta, ∫ u in (-delta)..delta, phi r s t u ^ (2 * n) := by
  have hx1 : cut 1 = π + (-delta) := by simp [cut, delta]; ring
  have hx2 : cut 2 = π + delta := by simp [cut, delta]; ring
  have hy1 : cut 3 = 2 * π + (-delta) := by simp [cut, delta]; ring
  have hy2 : cut 4 = 2 * π + delta := by simp [cut, delta]; ring
  rw [hx1, hx2, hy1, hy2]
  exact shift_square fun t u => phi_shift_pi_two_pow hr hs n t u

lemma cell_two_pi {r s : ℕ} (hr : Odd r) (hs : Odd s) (n : ℕ) :
    ∫ x in cut 3..cut 4, ∫ y in cut 1..cut 2, phi r s x y ^ (2 * n) =
      ∫ t in (-delta)..delta, ∫ u in (-delta)..delta, phi r s t u ^ (2 * n) := by
  have hx1 : cut 3 = 2 * π + (-delta) := by simp [cut, delta]; ring
  have hx2 : cut 4 = 2 * π + delta := by simp [cut, delta]; ring
  have hy1 : cut 1 = π + (-delta) := by simp [cut, delta]; ring
  have hy2 : cut 2 = π + delta := by simp [cut, delta]; ring
  rw [hx1, hx2, hy1, hy2]
  exact shift_square fun t u => phi_shift_two_pi_pow hr hs n t u

lemma index_of_pi (i : ℕ) (hi : i < 5) (hx1 : cut i ≤ π) (hx2 : π ≤ cut (i + 1)) : i = 1 := by
  interval_cases i
  · simp [cut] at hx2
    nlinarith [pi_pos]
  · rfl
  · simp [cut] at hx1
    nlinarith [pi_pos]
  · simp [cut] at hx1
    nlinarith [pi_pos]
  · simp [cut] at hx1
    nlinarith [pi_pos]

lemma index_of_two (i : ℕ) (hi : i < 5) (hx1 : cut i ≤ 2 * π) (hx2 : 2 * π ≤ cut (i + 1)) :
    i = 3 := by
  interval_cases i
  · simp [cut] at hx2
    nlinarith [pi_pos]
  · simp [cut] at hx2
    nlinarith [pi_pos]
  · simp [cut] at hx2
    nlinarith [pi_pos]
  · rfl
  · simp [cut] at hx1
    nlinarith [pi_pos]

lemma neg_one_abs (k : ℕ) : |(-1 : ℝ) ^ k| = 1 := by
  rw [abs_pow]
  simp

lemma even_of_signed_sum {r s : ℕ}
    (h : |((-1 : ℝ) ^ r + (-1 : ℝ) ^ s) / 2| = 1) : Even (r + s) := by
  have habs : |(-1 : ℝ) ^ r + (-1 : ℝ) ^ s| = 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    linarith
  rcases abs_pair_eq_two (neg_one_abs r).le (neg_one_abs s).le habs with ⟨hr1, hs1⟩ | ⟨hr1, hs1⟩
  · have hrE : Even r := by
      by_contra hodd
      rw [(Nat.not_even_iff_odd.mp hodd).neg_one_pow] at hr1
      norm_num at hr1
    have hsE : Even s := by
      by_contra hodd
      rw [(Nat.not_even_iff_odd.mp hodd).neg_one_pow] at hs1
      norm_num at hs1
    rw [Nat.even_add]
    exact iff_of_true hrE hsE
  · have hrO : Odd r := by
      by_contra he
      rw [(Nat.not_odd_iff_even.mp he).neg_one_pow] at hr1
      norm_num at hr1
    have hsO : Odd s := by
      by_contra he
      rw [(Nat.not_odd_iff_even.mp he).neg_one_pow] at hs1
      norm_num at hs1
    rw [Nat.even_add]
    exact iff_of_false (Nat.not_even_iff_odd.mpr hrO) (Nat.not_even_iff_odd.mpr hsO)

lemma abs_phi_one_window {r s : ℕ} (hcop : Nat.Coprime r s) {x y : ℝ}
    (hx1 : π / 2 ≤ x) (hx2 : x ≤ 5 * π / 2) (hy1 : π / 2 ≤ y) (hy2 : y ≤ 5 * π / 2)
    (h : |phi r s x y| = 1) :
    (x = π ∧ y = π) ∨ (x = 2 * π ∧ y = 2 * π) ∨
      (Even (r + s) ∧ ((x = π ∧ y = 2 * π) ∨ (x = 2 * π ∧ y = π))) := by
  obtain ⟨hxpi, hypi⟩ := abs_phi_eq_one hcop h
  rcases eq_pi_or_two_pi hx1 hx2 hxpi with rfl | rfl <;>
    rcases eq_pi_or_two_pi hy1 hy2 hypi with rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · refine Or.inr (Or.inr ⟨?_, Or.inl ⟨rfl, rfl⟩⟩)
    exact even_of_signed_sum (by rw [← phi_pi_two]; exact h)
  · refine Or.inr (Or.inr ⟨?_, Or.inr ⟨rfl, rfl⟩⟩)
    exact even_of_signed_sum (by rw [← phi_two_pi_pi]; exact h)
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)

abbrev PeakB (b : Bool) (i j : ℕ) : Prop :=
  (i = 1 ∧ j = 1) ∨ (i = 3 ∧ j = 3) ∨
    (b = true ∧ i = 1 ∧ j = 3) ∨ (b = true ∧ i = 3 ∧ j = 1)

lemma cell_abs_lt {r s : ℕ} (hcop : Nat.Coprime r s) (i j : ℕ) (hi : i < 5) (hj : j < 5)
    (hnot : ¬ PeakB (decide (Even (r + s))) i j) {x y : ℝ}
    (hx1 : cut i ≤ x) (hx2 : x ≤ cut (i + 1)) (hy1 : cut j ≤ y) (hy2 : y ≤ cut (j + 1)) :
    |phi r s x y| < 1 := by
  apply lt_of_le_of_ne (abs_phi_le_one r s x y)
  intro heq
  have hxlo : π / 2 ≤ x := (cut_bounds i (by omega)).1.trans hx1
  have hxhi : x ≤ 5 * π / 2 := hx2.trans (cut_bounds (i + 1) (by omega)).2
  have hylo : π / 2 ≤ y := (cut_bounds j (by omega)).1.trans hy1
  have hyhi : y ≤ 5 * π / 2 := hy2.trans (cut_bounds (j + 1) (by omega)).2
  rcases abs_phi_one_window hcop hxlo hxhi hylo hyhi heq with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨he, hrest⟩
  · exact hnot (Or.inl ⟨index_of_pi i hi hx1 hx2, index_of_pi j hj hy1 hy2⟩)
  · exact hnot (Or.inr (Or.inl ⟨index_of_two i hi hx1 hx2, index_of_two j hj hy1 hy2⟩))
  · rcases hrest with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hnot (Or.inr (Or.inr (Or.inl
        ⟨decide_eq_true he, index_of_pi i hi hx1 hx2, index_of_two j hj hy1 hy2⟩)))
    · exact hnot (Or.inr (Or.inr (Or.inr
        ⟨decide_eq_true he, index_of_two i hi hx1 hx2, index_of_pi j hj hy1 hy2⟩)))

lemma tendsto_cell {r s : ℕ} (hr : 0 < r) (hrs : r < s) (hcop : Nat.Coprime r s)
    (i j : ℕ) (hi : i < 5) (hj : j < 5) :
    Tendsto (fun n : ℕ => (n : ℝ) * ∫ x in cut i..cut (i + 1),
        ∫ y in cut j..cut (j + 1), phi r s x y ^ (2 * n)) Filter.atTop
      (nhds (if PeakB (decide (Even (r + s))) i j then 2 * π / aCoeff r s else 0)) := by
  by_cases hpk : PeakB (decide (Even (r + s))) i j
  · rw [if_pos hpk]
    have hEq : ∀ n, ∫ x in cut i..cut (i + 1), ∫ y in cut j..cut (j + 1),
        phi r s x y ^ (2 * n) =
        ∫ t in (-delta)..delta, ∫ u in (-delta)..delta, phi r s t u ^ (2 * n) := by
      intro n
      rcases hpk with ⟨hi1, hj1⟩ | ⟨hi1, hj1⟩ | ⟨hb, hi1, hj1⟩ | ⟨hb, hi1, hj1⟩
      · subst hi1
        subst hj1
        exact cell_pi r s n
      · subst hi1
        subst hj1
        exact cell_two r s n
      · subst hi1
        subst hj1
        obtain ⟨hrO, hsO⟩ := both_odd hcop (of_decide_eq_true hb)
        exact cell_pi_two hrO hsO n
      · subst hi1
        subst hj1
        obtain ⟨hrO, hsO⟩ := both_odd hcop (of_decide_eq_true hb)
        exact cell_two_pi hrO hsO n
    exact (tendsto_delta_box hr (le_of_lt hrs) hcop).congr fun n => by rw [hEq]
  · rw [if_neg hpk]
    exact tendsto_rect_decay (cut_succ_le i hi) (cut_succ_le j hj) fun u v hu1 hu2 hv1 hv2 =>
      cell_abs_lt hcop i j hi hj hpk hu1 hu2 hv1 hv2

lemma peak_card (b : Bool) :
    ((Finset.range 5 ×ˢ Finset.range 5).filter fun p : ℕ × ℕ => PeakB b p.1 p.2).card =
      if b then 4 else 2 := by
  cases b <;> decide

lemma peak_sum (b : Bool) (c : ℝ) :
    (∑ p ∈ Finset.range 5 ×ˢ Finset.range 5, if PeakB b p.1 p.2 then c else 0) =
      ((if b then 4 else 2 : ℕ) : ℝ) * c := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, peak_card]
  simp [nsmul_eq_mul]

lemma window_sum (r s n : ℕ) :
    ∫ x in (π / 2)..(5 * π / 2), ∫ y in (π / 2)..(5 * π / 2), phi r s x y ^ (2 * n) =
      ∑ p ∈ Finset.range 5 ×ˢ Finset.range 5,
        ∫ x in cut p.1..cut (p.1 + 1), ∫ y in cut p.2..cut (p.2 + 1),
          phi r s x y ^ (2 * n) := by
  have hf : Continuous fun q : ℝ × ℝ => phi r s q.1 q.2 ^ (2 * n) := continuous_phi_pow r s n
  have hc0 : cut 0 = π / 2 := by simp [cut]
  have hc5 : cut 5 = 5 * π / 2 := by simp [cut]
  have houter :
      ∫ x in cut 0..cut 5, ∫ y in cut 0..cut 5, phi r s x y ^ (2 * n) =
        ∑ i ∈ Finset.range 5, ∫ x in cut i..cut (i + 1),
          ∫ y in cut 0..cut 5, phi r s x y ^ (2 * n) := by
    symm
    refine sum_integral_adjacent_intervals ?_
    intro k _hk
    exact Continuous.intervalIntegrable (μ := volume)
      (inner_continuous (f := fun x y => phi r s x y ^ (2 * n)) hf (cut 0) (cut 5))
      (cut k) (cut (k + 1))
  have hinner : ∀ x, ∫ y in cut 0..cut 5, phi r s x y ^ (2 * n) =
      ∑ j ∈ Finset.range 5, ∫ y in cut j..cut (j + 1), phi r s x y ^ (2 * n) := by
    intro x
    symm
    refine sum_integral_adjacent_intervals ?_
    intro k _hk
    exact section_integrable (f := fun a b => phi r s a b ^ (2 * n)) hf x
      (cut k) (cut (k + 1))
  rw [← hc0, ← hc5, houter]
  simp_rw [hinner]
  have hpull : ∀ i ∈ Finset.range 5,
      (∫ x in cut i..cut (i + 1), ∑ j ∈ Finset.range 5,
        ∫ y in cut j..cut (j + 1), phi r s x y ^ (2 * n)) =
        ∑ j ∈ Finset.range 5, ∫ x in cut i..cut (i + 1),
          ∫ y in cut j..cut (j + 1), phi r s x y ^ (2 * n) := by
    intro i _hi
    exact integral_finsetSum (μ := volume) (fun j _hj =>
      Continuous.intervalIntegrable (μ := volume)
        (inner_continuous (f := fun x y => phi r s x y ^ (2 * n)) hf
          (cut j) (cut (j + 1))) (cut i) (cut (i + 1)))
  have hrew :
      (∑ i ∈ Finset.range 5, ∫ x in cut i..cut (i + 1), ∑ j ∈ Finset.range 5,
        ∫ y in cut j..cut (j + 1), phi r s x y ^ (2 * n)) =
      ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        ∫ x in cut i..cut (i + 1), ∫ y in cut j..cut (j + 1),
          phi r s x y ^ (2 * n) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact hpull i hi
  rw [hrew]
  exact (Finset.sum_product (s := Finset.range 5) (t := Finset.range 5)
    (f := fun p => ∫ x in cut p.1..cut (p.1 + 1),
      ∫ y in cut p.2..cut (p.2 + 1), phi r s x y ^ (2 * n))).symm

lemma tendsto_n_window {r s : ℕ} (hr : 0 < r) (hrs : r < s) (hcop : Nat.Coprime r s) :
    Tendsto (fun n : ℕ => (n : ℝ) * ∫ x in (π / 2)..(5 * π / 2),
        ∫ y in (π / 2)..(5 * π / 2), phi r s x y ^ (2 * n)) Filter.atTop
      (nhds ((if Even (r + s) then (4 : ℝ) else 2) * (2 * π / aCoeff r s))) := by
  have hsum := tendsto_finsetSum (Finset.range 5 ×ˢ Finset.range 5) fun p hp =>
    tendsto_cell hr hrs hcop p.1 p.2
      (Finset.mem_range.mp (Finset.mem_product.mp hp).1)
      (Finset.mem_range.mp (Finset.mem_product.mp hp).2)
  have hcount : ((if decide (Even (r + s)) then 4 else 2 : ℕ) : ℝ) =
      if Even (r + s) then 4 else 2 := by
    by_cases he : Even (r + s)
    · simp [he]
    · simp [he]
  rw [peak_sum, hcount] at hsum
  refine hsum.congr fun n => ?_
  symm
  calc
    (n : ℝ) * ∫ x in (π / 2)..(5 * π / 2), ∫ y in (π / 2)..(5 * π / 2),
        phi r s x y ^ (2 * n) =
      (n : ℝ) * ∑ p ∈ Finset.range 5 ×ˢ Finset.range 5,
        ∫ x in cut p.1..cut (p.1 + 1), ∫ y in cut p.2..cut (p.2 + 1),
          phi r s x y ^ (2 * n) := by rw [window_sum]
    _ = ∑ p ∈ Finset.range 5 ×ˢ Finset.range 5,
        (n : ℝ) * ∫ x in cut p.1..cut (p.1 + 1), ∫ y in cut p.2..cut (p.2 + 1),
          phi r s x y ^ (2 * n) := by rw [Finset.mul_sum]

lemma two_pow_six (n : ℕ) : (2 : ℝ) ^ (6 * n) = (64 : ℝ) ^ n := by
  have h64 : (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
  rw [h64, ← pow_mul]

lemma two_pow_six_succ (n : ℕ) : (2 : ℝ) ^ (6 * n + 1) = 2 * (64 : ℝ) ^ n := by
  rw [pow_add, pow_one, two_pow_six, mul_comm]

lemma ratio_eq {r s n : ℕ} (hr : 0 < r) (hrs : r < s) (hn : 1 ≤ n) :
    (OMA.S_oeis_a253974.closedPaths r s n : ℝ) /
        ((if Even (r + s) then (2 : ℝ) ^ (6 * n + 1) else (2 : ℝ) ^ (6 * n)) /
          (((r : ℝ) ^ 2 + (s : ℝ) ^ 2) * π * (n : ℝ))) =
      (((r : ℝ) ^ 2 + (s : ℝ) ^ 2) /
          ((if Even (r + s) then (8 : ℝ) else 4) * π)) *
        ((n : ℝ) * ∫ x in (π / 2)..(5 * π / 2),
          ∫ y in (π / 2)..(5 * π / 2), phi r s x y ^ (2 * n)) := by
  have hclosed := closedPaths_real (n := n) hr hrs
  rw [← integral_window r s n] at hclosed
  set I : ℝ := ∫ x in (π / 2)..(5 * π / 2), ∫ y in (π / 2)..(5 * π / 2),
    phi r s x y ^ (2 * n)
  set a : ℝ := (r : ℝ) ^ 2 + (s : ℝ) ^ 2
  have ha : a ≠ 0 := by simpa [a, aCoeff] using (aCoeff_pos (s := s) hr).ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have h64 : (64 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  by_cases he : Even (r + s)
  · rw [if_pos he, if_pos he, hclosed, two_pow_six_succ]
    field_simp [ha, hn0, h64, pi_ne_zero]
    ring
  · rw [if_neg he, if_neg he, hclosed, two_pow_six]
    field_simp [ha, hn0, h64, pi_ne_zero]

lemma tendsto_ratio {r s : ℕ} (hr : 0 < r) (hrs : r < s) (hcop : Nat.Coprime r s) :
    Tendsto (fun n : ℕ => (OMA.S_oeis_a253974.closedPaths r s n : ℝ) /
      ((if Even (r + s) then (2 : ℝ) ^ (6 * n + 1) else (2 : ℝ) ^ (6 * n)) /
        (((r : ℝ) ^ 2 + (s : ℝ) ^ 2) * Real.pi * (n : ℝ))))
      Filter.atTop (nhds 1) := by
  have hwin := tendsto_n_window hr hrs hcop
  set factor : ℝ := ((r : ℝ) ^ 2 + (s : ℝ) ^ 2) /
    ((if Even (r + s) then (8 : ℝ) else 4) * π)
  have ha : ((r : ℝ) ^ 2 + (s : ℝ) ^ 2) ≠ 0 := (aCoeff_pos (s := s) hr).ne'
  have hL : factor * ((if Even (r + s) then (4 : ℝ) else 2) *
      (2 * π / aCoeff r s)) = 1 := by
    by_cases he : Even (r + s)
    · simp only [factor, aCoeff, if_pos he]
      field_simp [ha]
      ring
    · simp only [factor, aCoeff, if_neg he]
      field_simp [ha]
      ring
  have hmul := (tendsto_const_nhds (x := factor)).mul hwin
  rw [hL] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (ratio_eq hr hrs hn).symm

end A253974

theorem OMA.solution : type_of% @OMA.S_oeis_a253974.main := by
  intro r s hr hrs hcop
  exact A253974.tendsto_ratio hr hrs hcop

