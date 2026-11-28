import OMAReductions.R_Erdos67_erdos_67_variants_complex_R1

/-!
Proof of `OMA.R_Erdos67_erdos_67_variants_complex_R1.H1` (Tao 2016, Section 2 / Polymath5 finite
Fourier-analytic reduction to a random completely multiplicative function with bounded partial
sums up to any finite horizon `N`).
-/

namespace Erdos67ComplexH1

open MeasureTheory

noncomputable def χ1 (M : ℕ) [NeZero M] (k : ZMod M) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (k.val : ℂ) / (M : ℂ))

lemma χ1_zero (M : ℕ) [NeZero M] : χ1 M 0 = 1 := by
  simp [χ1]

lemma norm_χ1 (M : ℕ) [NeZero M] (k : ZMod M) : ‖χ1 M k‖ = 1 := by
  have harg :
      2 * Real.pi * Complex.I * (k.val : ℂ) / (M : ℂ) =
        (((2 * Real.pi * (k.val : ℝ) / (M : ℝ)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [χ1, harg]
  exact Complex.norm_exp_ofReal_mul_I _

lemma χ1_add (M : ℕ) [NeZero M] (k l : ZMod M) : χ1 M (k + l) = χ1 M k * χ1 M l := by
  have hM0 : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hval : ((k.val + l.val : ℕ) : ℂ) = (((k + l).val : ℕ) : ℂ) + (M : ℂ) * (((k.val + l.val) / M : ℕ) : ℂ) := by
    have hnat : k.val + l.val = (k + l).val + M * ((k.val + l.val) / M) := by
      rw [ZMod.val_add]
      exact (Nat.mod_add_div (k.val + l.val) M).symm
    exact_mod_cast hnat
  have hexp :
      2 * Real.pi * Complex.I * (k.val : ℂ) / (M : ℂ) +
        2 * Real.pi * Complex.I * (l.val : ℂ) / (M : ℂ) =
        2 * Real.pi * Complex.I * ((k + l).val : ℂ) / (M : ℂ) +
          (((k.val + l.val) / M : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    have hsum : (k.val : ℂ) + (l.val : ℂ) = ((k.val + l.val : ℕ) : ℂ) := by push_cast; rfl
    calc
      2 * Real.pi * Complex.I * (k.val : ℂ) / (M : ℂ) +
          2 * Real.pi * Complex.I * (l.val : ℂ) / (M : ℂ)
          = 2 * Real.pi * Complex.I * ((k.val : ℂ) + (l.val : ℂ)) / (M : ℂ) := by ring
      _ = 2 * Real.pi * Complex.I * ((k.val + l.val : ℕ) : ℂ) / (M : ℂ) := by rw [hsum]
      _ = 2 * Real.pi * Complex.I *
            ((((k + l).val : ℕ) : ℂ) + (M : ℂ) * (((k.val + l.val) / M : ℕ) : ℂ)) / (M : ℂ) := by
            rw [hval]
      _ = 2 * Real.pi * Complex.I * ((k + l).val : ℂ) / (M : ℂ) +
            (((k.val + l.val) / M : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
            field_simp
  rw [χ1, χ1, χ1, ← Complex.exp_add, hexp, Complex.exp_add, Complex.exp_nat_mul,
    Complex.exp_two_pi_mul_I, one_pow, mul_one]

lemma ofReal_norm_sq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  rw [Complex.star_def, Complex.mul_conj, Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg z)]

lemma χ1_neg (M : ℕ) [NeZero M] (k : ZMod M) : χ1 M (-k) = star (χ1 M k) := by
  have h1 : χ1 M k * χ1 M (-k) = 1 := by
    rw [← χ1_add, add_neg_cancel, χ1_zero]
  have h2 : χ1 M k * star (χ1 M k) = 1 := by
    rw [← ofReal_norm_sq, norm_χ1]
    norm_num
  exact mul_left_cancel₀ (Complex.exp_ne_zero _) (h1.trans h2.symm)

lemma χ1_natCast_mul (M : ℕ) [NeZero M] (m : ℕ) (x : ZMod M) :
    χ1 M ((m : ZMod M) * x) = (χ1 M x) ^ m := by
  induction m with
  | zero =>
    simp [χ1_zero]
  | succ m ih =>
    rw [Nat.cast_succ, add_mul, one_mul, χ1_add, ih, pow_succ]

lemma sum_χ1_mul (M : ℕ) [NeZero M] (c : ZMod M) :
    (∑ u : ZMod M, χ1 M (c * u)) = if c = 0 then (M : ℂ) else 0 := by
  by_cases hc : c = 0
  · subst hc
    simp [χ1_zero, ZMod.card]
  · simp only [hc, ite_false]
    have hshift : χ1 M c * ∑ u : ZMod M, χ1 M (c * u) = ∑ u : ZMod M, χ1 M (c * u) := by
      rw [Finset.mul_sum]
      have hterm : ∀ u : ZMod M, χ1 M c * χ1 M (c * u) = χ1 M (c * (u + 1)) := by
        intro u
        rw [← χ1_add]
        congr 1
        ring
      simp_rw [hterm]
      exact Equiv.sum_comp (Equiv.addRight (1 : ZMod M)) (fun u => χ1 M (c * u))
    have hmul : (χ1 M c - 1) * ∑ u : ZMod M, χ1 M (c * u) = 0 := by
      rw [sub_mul, one_mul, hshift, sub_self]
    have hne : χ1 M c - 1 ≠ 0 := by
      intro h0
      have heq1 : χ1 M c = 1 := sub_eq_zero.mp h0
      have hdvd : M ∣ c.val :=
        (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (NeZero.ne M)).mp heq1
      have hlt : c.val < M := ZMod.val_lt c
      have hval0 : c.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
      exact hc ((ZMod.val_eq_zero c).mp hval0)
    exact (mul_eq_zero.mp hmul).resolve_left hne

noncomputable def ψ (M : ℕ) [NeZero M] {r : ℕ} (a u : Fin r → ZMod M) : ℂ :=
  ∏ i : Fin r, χ1 M (a i * u i)

lemma ψ_add_left (M : ℕ) [NeZero M] {r : ℕ} (a b u : Fin r → ZMod M) :
    ψ M (a + b) u = ψ M a u * ψ M b u := by
  simp only [ψ, Pi.add_apply, add_mul, χ1_add, Finset.prod_mul_distrib]

lemma star_ψ (M : ℕ) [NeZero M] {r : ℕ} (a u : Fin r → ZMod M) :
    star (ψ M a u) = ψ M (-a) u := by
  simp only [ψ, Pi.neg_apply, neg_mul, χ1_neg, Complex.star_def, map_prod]

lemma sum_ψ_right (M : ℕ) [NeZero M] {r : ℕ} (c : Fin r → ZMod M) :
    (∑ u : Fin r → ZMod M, ψ M c u) = if c = 0 then ((M ^ r : ℕ) : ℂ) else 0 := by
  have hprod :
      (∑ u : Fin r → ZMod M, ψ M c u) = ∏ i : Fin r, ∑ x : ZMod M, χ1 M (c i * x) :=
    (Fintype.prod_sum (fun i (x : ZMod M) => χ1 M (c i * x))).symm
  rw [hprod]
  by_cases hc : c = 0
  · subst hc
    simp [χ1_zero, ZMod.card]
  · simp only [hc, ite_false]
    have hex : ∃ i : Fin r, c i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hc (funext hall)
    obtain ⟨i, hi⟩ := hex
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [sum_χ1_mul]
    simp [hi]

noncomputable def dft (M : ℕ) [NeZero M] {r : ℕ}
    (H : (Fin r → ZMod M) → ℂ) (u : Fin r → ZMod M) : ℂ :=
  (((M ^ r : ℕ) : ℂ)⁻¹) * ∑ a : Fin r → ZMod M, H a * star (ψ M a u)

lemma dft_shift (M : ℕ) [NeZero M] {r : ℕ}
    (F : (Fin r → ZMod M) → ℂ) (s u : Fin r → ZMod M) :
    dft M (fun a => F (a + s)) u = ψ M s u * dft M F u := by
  simp only [dft]
  have hsum :
      (∑ a : Fin r → ZMod M, F (a + s) * star (ψ M a u)) =
        ψ M s u * ∑ b : Fin r → ZMod M, F b * star (ψ M b u) := by
    rw [Finset.mul_sum]
    have hcomp := Equiv.sum_comp (Equiv.addRight s)
      (fun b : Fin r → ZMod M => ψ M s u * (F b * star (ψ M b u)))
    rw [← hcomp]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Equiv.coe_addRight]
    rw [star_ψ, star_ψ]
    have hneg : -(a + s) = -s + -a := by abel
    rw [hneg, ψ_add_left]
    have hcancel : ψ M s u * ψ M (-s) u = 1 := by
      rw [← ψ_add_left, add_neg_cancel]
      simp [ψ, χ1_zero]
    calc
      F (a + s) * ψ M (-a) u
          = (ψ M s u * ψ M (-s) u) * (F (a + s) * ψ M (-a) u) := by rw [hcancel, one_mul]
      _ = ψ M s u * (F (a + s) * (ψ M (-s) u * ψ M (-a) u)) := by ring
  rw [hsum]
  ring

lemma dft_finset_sum (M : ℕ) [NeZero M] {r : ℕ} {ι : Type*}
    (s : Finset ι) (H : ι → (Fin r → ZMod M) → ℂ) (u : Fin r → ZMod M) :
    dft M (fun a => ∑ j ∈ s, H j a) u = ∑ j ∈ s, dft M (H j) u := by
  simp only [dft, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma plancherel (M : ℕ) [NeZero M] {r : ℕ} (H : (Fin r → ZMod M) → ℂ) :
    (∑ u : Fin r → ZMod M, ‖dft M H u‖ ^ 2) =
      (((M ^ r : ℕ) : ℝ)⁻¹) * ∑ a : Fin r → ZMod M, ‖H a‖ ^ 2 := by
  have hMr_ne : ((M ^ r : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero r (NeZero.ne M))
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.ofReal_pow, ofReal_norm_sq]
  have hstar_dft : ∀ u : Fin r → ZMod M,
      star (dft M H u) = (((M ^ r : ℕ) : ℂ)⁻¹) * ∑ b : Fin r → ZMod M, star (H b) * ψ M b u := by
    intro u
    simp only [dft, Complex.star_def, map_mul, map_inv₀, map_natCast, map_sum]
    simp only [← Complex.star_def, star_star]
  simp_rw [hstar_dft]
  simp only [dft]
  have hlhs :
      (∑ u : Fin r → ZMod M,
        ((((M ^ r : ℕ) : ℂ)⁻¹) * ∑ a : Fin r → ZMod M, H a * star (ψ M a u)) *
          ((((M ^ r : ℕ) : ℂ)⁻¹) * ∑ b : Fin r → ZMod M, star (H b) * ψ M b u)) =
        (((M ^ r : ℕ) : ℂ)⁻¹) * (((M ^ r : ℕ) : ℂ)⁻¹) *
          ∑ a : Fin r → ZMod M, ∑ b : Fin r → ZMod M,
            H a * star (H b) * ∑ u : Fin r → ZMod M, ψ M (b - a) u := by
    have h1 : ∀ u : Fin r → ZMod M,
        ((((M ^ r : ℕ) : ℂ)⁻¹) * ∑ a : Fin r → ZMod M, H a * star (ψ M a u)) *
          ((((M ^ r : ℕ) : ℂ)⁻¹) * ∑ b : Fin r → ZMod M, star (H b) * ψ M b u) =
        (((M ^ r : ℕ) : ℂ)⁻¹) * (((M ^ r : ℕ) : ℂ)⁻¹) *
          ∑ a : Fin r → ZMod M, ∑ b : Fin r → ZMod M,
            H a * star (H b) * ψ M (b - a) u := by
      intro u
      have hmul :
          (∑ a : Fin r → ZMod M, H a * star (ψ M a u)) *
            (∑ b : Fin r → ZMod M, star (H b) * ψ M b u) =
          ∑ a : Fin r → ZMod M, ∑ b : Fin r → ZMod M, H a * star (H b) * ψ M (b - a) u := by
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [star_ψ, sub_eq_add_neg, ψ_add_left]
        ring
      calc
        ((((M ^ r : ℕ) : ℂ)⁻¹) * ∑ a : Fin r → ZMod M, H a * star (ψ M a u)) *
            ((((M ^ r : ℕ) : ℂ)⁻¹) * ∑ b : Fin r → ZMod M, star (H b) * ψ M b u)
            = (((M ^ r : ℕ) : ℂ)⁻¹) * (((M ^ r : ℕ) : ℂ)⁻¹) *
                ((∑ a : Fin r → ZMod M, H a * star (ψ M a u)) *
                  (∑ b : Fin r → ZMod M, star (H b) * ψ M b u)) := by ring
        _ = (((M ^ r : ℕ) : ℂ)⁻¹) * (((M ^ r : ℕ) : ℂ)⁻¹) *
              ∑ a : Fin r → ZMod M, ∑ b : Fin r → ZMod M, H a * star (H b) * ψ M (b - a) u := by
              rw [hmul]
    simp_rw [h1]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
  rw [hlhs]
  have hinner : ∀ a : Fin r → ZMod M,
      (∑ b : Fin r → ZMod M, H a * star (H b) * ∑ u : Fin r → ZMod M, ψ M (b - a) u) =
        H a * star (H a) * ((M ^ r : ℕ) : ℂ) := by
    intro a
    simp_rw [sum_ψ_right, sub_eq_zero, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ a]
    simp
  simp_rw [hinner, ← Finset.sum_mul]
  calc
    (((M ^ r : ℕ) : ℂ)⁻¹) * (((M ^ r : ℕ) : ℂ)⁻¹) *
        ((∑ a : Fin r → ZMod M, H a * star (H a)) * ((M ^ r : ℕ) : ℂ))
        = (((M ^ r : ℕ) : ℂ)⁻¹) * ((((M ^ r : ℕ) : ℂ)⁻¹) * ((M ^ r : ℕ) : ℂ)) *
            ∑ a : Fin r → ZMod M, H a * star (H a) := by ring
    _ = (((M ^ r : ℕ) : ℂ)⁻¹) * ∑ a : Fin r → ZMod M, H a * star (H a) := by
          rw [inv_mul_cancel₀ hMr_ne, mul_one]
    _ = ((M : ℂ) ^ r)⁻¹ * ∑ a : Fin r → ZMod M, H a * star (H a) := by
          push_cast
          rfl

lemma finset_sum_measure_apply {α ι : Type*} [MeasurableSpace α] [DecidableEq ι]
    (s : Finset ι) (ν : ι → Measure α) (A : Set α) :
    (∑ u ∈ s, ν u) A = ∑ u ∈ s, ν u A := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert u s hu ih =>
    rw [Finset.sum_insert hu, Finset.sum_insert hu, Measure.add_apply, ih]

lemma integrable_and_integral_finset_sum_dirac
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [MeasurableSingletonClass α] [DecidableEq ι]
    (g : α → ℝ) (hg : Continuous g) (w : ι → ℝ) (hw : ∀ u, 0 ≤ w u) (z : ι → α)
    (s : Finset ι) :
    Integrable g (∑ u ∈ s, ENNReal.ofReal (w u) • Measure.dirac (z u)) ∧
      (∫ x, g x ∂(∑ u ∈ s, ENNReal.ofReal (w u) • Measure.dirac (z u))) =
        ∑ u ∈ s, w u * g (z u) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨integrable_zero_measure, ?_⟩
    simp [integral_zero_measure]
  | insert u s hu ih =>
    have hterm_int : Integrable g (ENNReal.ofReal (w u) • Measure.dirac (z u)) := by
      refine ⟨hg.aestronglyMeasurable, ?_⟩
      rw [HasFiniteIntegral, lintegral_smul_measure, lintegral_dirac]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp)
    rw [Finset.sum_insert hu, Finset.sum_insert hu]
    refine ⟨hterm_int.add_measure ih.1, ?_⟩
    rw [integral_add_measure hterm_int ih.1, ih.2, integral_smul_measure, integral_dirac,
      smul_eq_mul, ENNReal.toReal_ofReal (hw u)]

lemma card_slice_mul_le (M r N : ℕ) [NeZero M] (hNM : N < M) (i : Fin r) :
    (Finset.univ.filter (fun a : Fin r → ZMod M => M ≤ (a i).val + N)).card * M ≤
      N * M ^ r := by
  let T : Finset (ZMod M) := Finset.univ.filter (fun x : ZMod M => M ≤ x.val + N)
  have hT_card : T.card ≤ N := by
    have hinj : Set.InjOn ZMod.val (T : Set (ZMod M)) :=
      fun x _ y _ hxy => ZMod.val_injective M hxy
    have hmaps : Set.MapsTo ZMod.val (T : Set (ZMod M)) (Finset.Ico (M - N) M : Set ℕ) := by
      intro x hx
      rw [Finset.mem_coe, Finset.mem_filter] at hx
      rw [Finset.mem_coe, Finset.mem_Ico]
      have hlt : x.val < M := ZMod.val_lt x
      omega
    have hle := Finset.card_le_card_of_injOn ZMod.val hmaps hinj
    rw [Nat.card_Ico] at hle
    omega
  let eSplit :
      {a : Fin r → ZMod M // M ≤ (a i).val + N} ≃
        {x : ZMod M // x ∈ T} × ({j : Fin r // j ≠ i} → ZMod M) :=
    { toFun := fun a => (⟨a.1 i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.2⟩⟩, fun j => a.1 j.1)
      invFun := fun p =>
        ⟨fun j => if h : j = i then p.1.1 else p.2 ⟨j, h⟩, by
          have hp := (Finset.mem_filter.mp p.1.2).2
          simpa using hp⟩
      left_inv := fun a => by
        ext j
        by_cases h : j = i
        · subst h
          simp
        · simp [h]
      right_inv := fun p => by
        rcases p with ⟨⟨x, hx⟩, g⟩
        ext
        · simp
        · rename_i j
          simp [j.2] }
  have hcard_eq :
      (Finset.univ.filter (fun a : Fin r → ZMod M => M ≤ (a i).val + N)).card =
        T.card * M ^ (r - 1) := by
    rw [← Fintype.card_subtype]
    rw [Fintype.card_congr eSplit, Fintype.card_prod, Fintype.card_coe, Fintype.card_fun,
      ZMod.card, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  have hr_pos : 1 ≤ r := Nat.pos_of_ne_zero (by intro hr0; subst hr0; exact Fin.elim0 i)
  rw [hcard_eq, mul_assoc, ← pow_succ, Nat.sub_add_cancel hr_pos]
  exact Nat.mul_le_mul_right (M ^ r) hT_card

lemma card_bdry_mul_le (M r N : ℕ) [NeZero M] (hNM : N < M) :
    (Finset.univ.filter (fun a : Fin r → ZMod M => ¬ ∀ i : Fin r, (a i).val + N < M)).card * M ≤
      r * N * M ^ r := by
  have hsub :
      Finset.univ.filter (fun a : Fin r → ZMod M => ¬ ∀ i : Fin r, (a i).val + N < M) ⊆
        Finset.univ.biUnion
          (fun i : Fin r => Finset.univ.filter (fun a : Fin r → ZMod M => M ≤ (a i).val + N)) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    push Not at ha
    obtain ⟨i, hi⟩ := ha.2
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨Finset.mem_univ a, hi⟩⟩
  calc
    (Finset.univ.filter (fun a : Fin r → ZMod M => ¬ ∀ i : Fin r, (a i).val + N < M)).card * M
        ≤ (Finset.univ.biUnion (fun i : Fin r =>
            Finset.univ.filter (fun a : Fin r → ZMod M => M ≤ (a i).val + N))).card * M :=
          Nat.mul_le_mul_right M (Finset.card_le_card hsub)
    _ ≤ (∑ i : Fin r,
          (Finset.univ.filter (fun a : Fin r → ZMod M => M ≤ (a i).val + N)).card) * M :=
          Nat.mul_le_mul_right M Finset.card_biUnion_le
    _ = ∑ i : Fin r,
          (Finset.univ.filter (fun a : Fin r → ZMod M => M ≤ (a i).val + N)).card * M := by
          rw [Finset.sum_mul]
    _ ≤ ∑ _i : Fin r, N * M ^ r :=
          Finset.sum_le_sum fun i _ => card_slice_mul_le M r N hNM i
    _ = r * N * M ^ r := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_assoc]

lemma primeFactors_subset_filter_prime {j N : ℕ} (hj1 : 1 ≤ j) (hjN : j ≤ N) :
    j.primeFactors ⊆ (Finset.Icc 1 N).filter Nat.Prime := by
  intro p hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ j := Nat.dvd_of_mem_primeFactors hp
  have hp_le : p ≤ j := Nat.le_of_dvd (by omega) hp_dvd
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hp_prime.one_le, le_trans hp_le hjN⟩, hp_prime⟩

lemma factorization_lt_of_le {j N p : ℕ} (hj1 : 1 ≤ j) (hjN : j ≤ N) (hp : Nat.Prime p) :
    j.factorization p < N := by
  have hdvd : p ^ j.factorization p ∣ j := Nat.ordProj_dvd j p
  have hle1 : p ^ j.factorization p ≤ j := Nat.le_of_dvd (by omega) hdvd
  have hle2 : 2 ^ j.factorization p ≤ p ^ j.factorization p :=
    Nat.pow_le_pow_left hp.two_le _
  have hlt : j.factorization p < 2 ^ j.factorization p := Nat.lt_two_pow_self
  omega

lemma prod_primeFactors_eq_self {j : ℕ} (hj1 : 1 ≤ j) :
    ∏ p ∈ j.primeFactors, p ^ j.factorization p = j := by
  have h0 : j ≠ 0 := by omega
  have h := Nat.prod_factorization_pow_eq_self h0
  simpa [Finsupp.prod, Nat.support_factorization] using h

lemma solve_for_horizon
    (f : ℕ → Metric.sphere (0 : ℂ) 1) (C : ℝ)
    (hf : ∀ d ≥ 1, ∀ m ≥ 1, ‖∑ k ∈ Finset.Icc 1 m, (f (k * d)).1‖ ≤ C)
    (N : ℕ) (M : ℕ) [NeZero M]
    (hMN : N < M)
    (hM_bdry : ((Finset.Icc 1 N).filter Nat.Prime).card * N ^ 3 ≤ M) :
    ∃ μ : ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1),
      ∀ n ≤ N,
        (∫ z : (ℕ → Metric.sphere (0 : ℂ) 1),
          ‖∑ j ∈ Finset.Icc 1 n, ∏ p ∈ j.primeFactors, (z p).1 ^ j.factorization p‖ ^ 2
            ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1))) ≤ C ^ 2 + 1 := by
  let P : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime
  let r : ℕ := P.card
  let e : Fin r ≃ P := (Fintype.equivFinOfCardEq (Fintype.card_coe P)).symm
  let d : (Fin r → ZMod M) → ℕ := fun a => ∏ i : Fin r, (e i : ℕ) ^ (a i).val
  have hd_pos : ∀ a : Fin r → ZMod M, 1 ≤ d a := by
    intro a
    refine Finset.one_le_prod' fun i _ => ?_
    have hp : Nat.Prime (e i : ℕ) := (Finset.mem_filter.mp (e i).2).2
    exact Nat.one_le_pow _ _ hp.one_le
  let F : (Fin r → ZMod M) → ℂ := fun a => (f (d a)).1
  have hF_norm : ∀ a : Fin r → ZMod M, ‖F a‖ = 1 := fun a =>
    mem_sphere_zero_iff_norm.mp (f (d a)).2
  let w : (Fin r → ZMod M) → ℝ := fun u => ‖dft M F u‖ ^ 2
  have hw_nonneg : ∀ u, 0 ≤ w u := fun u => sq_nonneg _
  have hw_sum : ∑ u : Fin r → ZMod M, w u = 1 := by
    have hp := plancherel M F
    simp_rw [hF_norm, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at hp
    have hMr_ne : ((M ^ r : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero r (NeZero.ne M))
    rw [inv_mul_cancel₀ hMr_ne] at hp
    exact hp
  let z : (Fin r → ZMod M) → (ℕ → Metric.sphere (0 : ℂ) 1) := fun u p =>
    if hp : p ∈ P then
      ⟨χ1 M (u (e.symm ⟨p, hp⟩)), mem_sphere_zero_iff_norm.mpr (norm_χ1 M _)⟩
    else
      ⟨1, mem_sphere_zero_iff_norm.mpr norm_one⟩
  let μ₀ : Measure (ℕ → Metric.sphere (0 : ℂ) 1) :=
    ∑ u : Fin r → ZMod M, ENNReal.ofReal (w u) • Measure.dirac (z u)
  have hprob : IsProbabilityMeasure μ₀ := by
    refine ⟨?_⟩
    simp only [μ₀]
    rw [finset_sum_measure_apply]
    have hterm : ∀ u : Fin r → ZMod M,
        (ENNReal.ofReal (w u) • Measure.dirac (z u)) Set.univ = ENNReal.ofReal (w u) := by
      intro u
      rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.univ,
        Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, mul_one]
    simp_rw [hterm]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun u _ => hw_nonneg u), hw_sum, ENNReal.ofReal_one]
  refine ⟨⟨μ₀, hprob⟩, ?_⟩
  intro n hnN
  by_cases hn0 : n = 0
  · subst hn0
    have hzero :
        ∀ x : ℕ → Metric.sphere (0 : ℂ) 1,
          ‖∑ j ∈ Finset.Icc 1 0, ∏ p ∈ j.primeFactors, (x p).1 ^ j.factorization p‖ ^ 2 = 0 := by
      intro x
      simp
    simp only [ProbabilityMeasure.coe_mk, hzero, integral_zero]
    positivity
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
  let ev : ℕ → (Fin r → ZMod M) := fun j i => (j.factorization (e i : ℕ) : ZMod M)
  have hz_eval : ∀ (u : Fin r → ZMod M) (j : ℕ), 1 ≤ j → j ≤ N →
      (∏ p ∈ j.primeFactors, (z u p).1 ^ j.factorization p) = ψ M (ev j) u := by
    intro u j hj1 hjN
    have hsub : j.primeFactors ⊆ P := primeFactors_subset_filter_prime hj1 hjN
    have hprod_ext :
        (∏ p ∈ j.primeFactors, (z u p).1 ^ j.factorization p) =
          ∏ p ∈ P, (z u p).1 ^ j.factorization p := by
      refine Finset.prod_subset hsub ?_
      intro p _ hp_not
      have hfac0 : j.factorization p = 0 := by
        rw [← Nat.support_factorization] at hp_not
        exact Finsupp.notMem_support_iff.mp hp_not
      rw [hfac0, pow_zero]
    rw [hprod_ext, ← Finset.prod_coe_sort P (fun p => (z u p).1 ^ j.factorization p)]
    rw [← Fintype.prod_equiv e (fun i => (z u (e i : ℕ)).1 ^ j.factorization (e i : ℕ))
      (fun p : P => (z u p).1 ^ j.factorization p) (fun _ => rfl)]
    simp only [ψ]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hz_i : (z u (e i : ℕ)).1 = χ1 M (u i) := by
      have hp : (e i : ℕ) ∈ P := (e i).2
      simp only [z, hp, dite_true]
      have hsymm : e.symm ⟨(e i : ℕ), hp⟩ = i := e.symm_apply_apply i
      rw [hsymm]
    rw [hz_i, ← χ1_natCast_mul]
  let g : (ℕ → Metric.sphere (0 : ℂ) 1) → ℝ := fun x =>
    ‖∑ j ∈ Finset.Icc 1 n, ∏ p ∈ j.primeFactors, (x p).1 ^ j.factorization p‖ ^ 2
  have hg_cont : Continuous g := by fun_prop
  have hint_eq : (∫ x, g x ∂μ₀) = ∑ u : Fin r → ZMod M, w u * g (z u) :=
    (integrable_and_integral_finset_sum_dirac g hg_cont w hw_nonneg z Finset.univ).2
  change (∫ x, g x ∂μ₀) ≤ C ^ 2 + 1
  rw [hint_eq]
  have hsum_dft :
      (∑ u : Fin r → ZMod M, w u * g (z u)) =
        (((M ^ r : ℕ) : ℝ)⁻¹) *
          ∑ a : Fin r → ZMod M, ‖∑ j ∈ Finset.Icc 1 n, F (a + ev j)‖ ^ 2 := by
    let Hn : (Fin r → ZMod M) → ℂ := fun a => ∑ j ∈ Finset.Icc 1 n, F (a + ev j)
    have hdft_Hn : ∀ u : Fin r → ZMod M,
        ‖dft M Hn u‖ ^ 2 = w u * g (z u) := by
      intro u
      have h1 : dft M Hn u = (∑ j ∈ Finset.Icc 1 n, ψ M (ev j) u) * dft M F u := by
        simp only [Hn]
        rw [dft_finset_sum]
        simp_rw [dft_shift]
        rw [Finset.sum_mul]
      have h2 :
          (∑ j ∈ Finset.Icc 1 n, ∏ p ∈ j.primeFactors, (z u p).1 ^ j.factorization p) =
            ∑ j ∈ Finset.Icc 1 n, ψ M (ev j) u := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_Icc] at hj
        exact hz_eval u j hj.1 (le_trans hj.2 hnN)
      rw [h1, norm_mul, mul_pow]
      simp only [w, g]
      rw [h2, mul_comm]
    calc
      (∑ u : Fin r → ZMod M, w u * g (z u))
          = ∑ u : Fin r → ZMod M, ‖dft M Hn u‖ ^ 2 := by
              refine Finset.sum_congr rfl fun u _ => (hdft_Hn u).symm
      _ = (((M ^ r : ℕ) : ℝ)⁻¹) * ∑ a : Fin r → ZMod M, ‖Hn a‖ ^ 2 := plancherel M Hn
  rw [hsum_dft]
  let S_int : Finset (Fin r → ZMod M) :=
    Finset.univ.filter (fun a : Fin r → ZMod M => ∀ i : Fin r, (a i).val + N < M)
  let S_bdry : Finset (Fin r → ZMod M) :=
    Finset.univ.filter (fun a : Fin r → ZMod M => ¬ ∀ i : Fin r, (a i).val + N < M)
  have hsplit :
      (∑ a : Fin r → ZMod M, ‖∑ j ∈ Finset.Icc 1 n, F (a + ev j)‖ ^ 2) =
        (∑ a ∈ S_int, ‖∑ j ∈ Finset.Icc 1 n, F (a + ev j)‖ ^ 2) +
          (∑ a ∈ S_bdry, ‖∑ j ∈ Finset.Icc 1 n, F (a + ev j)‖ ^ 2) := by
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun a : Fin r → ZMod M => ∀ i : Fin r, (a i).val + N < M)
      (fun a : Fin r → ZMod M => ‖∑ j ∈ Finset.Icc 1 n, F (a + ev j)‖ ^ 2)).symm
  have hd_shift : ∀ a ∈ S_int, ∀ j ∈ Finset.Icc 1 n, d (a + ev j) = j * d a := by
    intro a ha j hj
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_Icc] at hj
    have hjN : j ≤ N := le_trans hj.2 hnN
    have hval_add : ∀ i : Fin r, ((a + ev j) i).val = (a i).val + j.factorization (e i : ℕ) := by
      intro i
      have hp : Nat.Prime (e i : ℕ) := (Finset.mem_filter.mp (e i).2).2
      have hfac_lt : j.factorization (e i : ℕ) < N := factorization_lt_of_le hj.1 hjN hp
      have hfac_lt_M : j.factorization (e i : ℕ) < M := lt_trans hfac_lt hMN
      have hev_val : (ev j i).val = j.factorization (e i : ℕ) := by
        simp only [ev, ZMod.val_natCast]
        exact Nat.mod_eq_of_lt hfac_lt_M
      have hsum_lt : (a i).val + j.factorization (e i : ℕ) < M := by
        have hai := ha.2 i
        omega
      rw [Pi.add_apply, ZMod.val_add, hev_val]
      exact Nat.mod_eq_of_lt hsum_lt
    have hprod_j : ∏ i : Fin r, (e i : ℕ) ^ j.factorization (e i : ℕ) = j := by
      rw [Fintype.prod_equiv e (fun i => (e i : ℕ) ^ j.factorization (e i : ℕ))
        (fun p : P => (p : ℕ) ^ j.factorization (p : ℕ)) (fun _ => rfl)]
      rw [Finset.prod_coe_sort P (fun p => p ^ j.factorization p)]
      have hsub : j.primeFactors ⊆ P := primeFactors_subset_filter_prime hj.1 hjN
      rw [← Finset.prod_subset hsub]
      · exact prod_primeFactors_eq_self hj.1
      · intro p _ hp_not
        have hfac0 : j.factorization p = 0 := by
          rw [← Nat.support_factorization] at hp_not
          exact Finsupp.notMem_support_iff.mp hp_not
        rw [hfac0, pow_zero]
    simp only [d]
    simp_rw [hval_add, pow_add]
    rw [Finset.prod_mul_distrib, hprod_j, mul_comm]
  have hint_bound :
      (∑ a ∈ S_int, ‖∑ j ∈ Finset.Icc 1 n, F (a + ev j)‖ ^ 2) ≤ ((M ^ r : ℕ) : ℝ) * C ^ 2 := by
    have hpt : ∀ a ∈ S_int, ‖∑ j ∈ Finset.Icc 1 n, F (a + ev j)‖ ^ 2 ≤ C ^ 2 := by
      intro a ha
      have hsum_eq :
          (∑ j ∈ Finset.Icc 1 n, F (a + ev j)) = ∑ j ∈ Finset.Icc 1 n, (f (j * d a)).1 := by
        refine Finset.sum_congr rfl fun j hj => ?_
        simp only [F, hd_shift a ha j hj]
      rw [hsum_eq]
      have hle : ‖∑ j ∈ Finset.Icc 1 n, (f (j * d a)).1‖ ≤ C := hf (d a) (hd_pos a) n hn1
      nlinarith [norm_nonneg (∑ j ∈ Finset.Icc 1 n, (f (j * d a)).1)]
    have hcard_le : (S_int.card : ℝ) ≤ ((M ^ r : ℕ) : ℝ) := by
      have hnat : S_int.card ≤ M ^ r := by
        calc
          S_int.card ≤ (Finset.univ : Finset (Fin r → ZMod M)).card := Finset.card_filter_le _ _
          _ = M ^ r := by simp [ZMod.card]
      exact_mod_cast hnat
    calc
      (∑ a ∈ S_int, ‖∑ j ∈ Finset.Icc 1 n, F (a + ev j)‖ ^ 2)
          ≤ ∑ _a ∈ S_int, C ^ 2 := Finset.sum_le_sum hpt
      _ = (S_int.card : ℝ) * C ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((M ^ r : ℕ) : ℝ) * C ^ 2 := mul_le_mul_of_nonneg_right hcard_le (sq_nonneg C)
  have hbdry_bound :
      (∑ a ∈ S_bdry, ‖∑ j ∈ Finset.Icc 1 n, F (a + ev j)‖ ^ 2) ≤ ((M ^ r : ℕ) : ℝ) := by
    have hpt : ∀ a ∈ S_bdry, ‖∑ j ∈ Finset.Icc 1 n, F (a + ev j)‖ ^ 2 ≤ (N : ℝ) ^ 2 := by
      intro a _
      have hcard_Icc : (Finset.Icc 1 n).card ≤ n := by
        have hsub : Finset.Icc 1 n ⊆ Finset.Ico 1 (n + 1) := by
          intro j hj
          rw [Finset.mem_Icc] at hj
          rw [Finset.mem_Ico]
          omega
        calc
          (Finset.Icc 1 n).card ≤ (Finset.Ico 1 (n + 1)).card := Finset.card_le_card hsub
          _ = n + 1 - 1 := Nat.card_Ico 1 (n + 1)
          _ = n := by omega
      have htr : ‖∑ j ∈ Finset.Icc 1 n, F (a + ev j)‖ ≤ (N : ℝ) := by
        calc
          ‖∑ j ∈ Finset.Icc 1 n, F (a + ev j)‖
              ≤ ∑ j ∈ Finset.Icc 1 n, ‖F (a + ev j)‖ := norm_sum_le _ _
          _ = ∑ _j ∈ Finset.Icc 1 n, (1 : ℝ) := by
                refine Finset.sum_congr rfl fun j _ => hF_norm (a + ev j)
          _ = ((Finset.Icc 1 n).card : ℝ) := by simp
          _ ≤ (n : ℝ) := Nat.cast_le.mpr hcard_Icc
          _ ≤ (N : ℝ) := Nat.cast_le.mpr hnN
      nlinarith [norm_nonneg (∑ j ∈ Finset.Icc 1 n, F (a + ev j))]
    have hnat_bound : S_bdry.card * N ^ 2 ≤ M ^ r := by
      have hM_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
      have hmul := card_bdry_mul_le M r N hMN
      have hstep : S_bdry.card * N ^ 2 * M ≤ M ^ r * M := by
        calc
          S_bdry.card * N ^ 2 * M
              = (S_bdry.card * M) * N ^ 2 := by ring
          _ ≤ (r * N * M ^ r) * N ^ 2 := Nat.mul_le_mul_right (N ^ 2) hmul
          _ = M ^ r * (r * N ^ 3) := by ring
          _ ≤ M ^ r * M := Nat.mul_le_mul_left (M ^ r) hM_bdry
      exact Nat.le_of_mul_le_mul_right hstep hM_pos
    calc
      (∑ a ∈ S_bdry, ‖∑ j ∈ Finset.Icc 1 n, F (a + ev j)‖ ^ 2)
          ≤ ∑ _a ∈ S_bdry, (N : ℝ) ^ 2 := Finset.sum_le_sum hpt
      _ = (S_bdry.card : ℝ) * (N : ℝ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((M ^ r : ℕ) : ℝ) := by exact_mod_cast hnat_bound
  have hMr_pos : (0 : ℝ) < ((M ^ r : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (pow_pos (Nat.pos_of_ne_zero (NeZero.ne M)) r)
  rw [hsplit]
  calc
    (((M ^ r : ℕ) : ℝ)⁻¹) *
        ((∑ a ∈ S_int, ‖∑ j ∈ Finset.Icc 1 n, F (a + ev j)‖ ^ 2) +
          (∑ a ∈ S_bdry, ‖∑ j ∈ Finset.Icc 1 n, F (a + ev j)‖ ^ 2))
        ≤ (((M ^ r : ℕ) : ℝ)⁻¹) * (((M ^ r : ℕ) : ℝ) * C ^ 2 + ((M ^ r : ℕ) : ℝ)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add hint_bound hbdry_bound)
            (inv_nonneg.mpr hMr_pos.le)
    _ = (((M ^ r : ℕ) : ℝ)⁻¹ * ((M ^ r : ℕ) : ℝ)) * (C ^ 2 + 1) := by ring
    _ = C ^ 2 + 1 := by rw [inv_mul_cancel₀ hMr_pos.ne', one_mul]

end Erdos67ComplexH1

theorem OMA.solution : OMA.R_Erdos67_erdos_67_variants_complex_R1.H1 := by
  intro f C _ hf
  refine ⟨C ^ 2 + 1, ?_⟩
  intro N
  let M : ℕ := ((Finset.Icc 1 N).filter Nat.Prime).card * N ^ 3 + N + 1
  have hM_ne : NeZero M := ⟨by omega⟩
  have hMN : N < M := by omega
  have hM_bdry : ((Finset.Icc 1 N).filter Nat.Prime).card * N ^ 3 ≤ M := by omega
  exact @Erdos67ComplexH1.solve_for_horizon f C hf N M hM_ne hMN hM_bdry
