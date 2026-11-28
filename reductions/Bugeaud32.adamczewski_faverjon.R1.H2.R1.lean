import OMAReductions.R_Bugeaud32_adamczewski_faverjon_R1

-- Reduction Bugeaud32.adamczewski_faverjon.R1.H2.R1 of step Bugeaud32.adamczewski_faverjon.R1.H2
-- Credit: @yuka30240

/-!
# Mahler orders and diagonal orbits

Starting from the finite-state systems of tkaiman's reduction, group the
transformation orders that share a positive power. Within each group, iterate
to a common order and eliminate the states over the polynomial ring. The
largest monomial at a positive point with independent logarithms proves
eventual nonvanishing for absolutely convergent complex series on its orbit.

The remaining steps are the common-order and distinct-order consequences of
the two purity theorems. Specialization at singular points is covered by
Lemma 10.1 in the proof of Theorem 1.1(i).
[Adamczewski and Faverjon, Sections 2, 4, and 10](https://arxiv.org/abs/2012.08283)
-/

namespace OMA.R_Bugeaud32_adamczewski_faverjon_R1_H2_R1

open Polynomial Filter
open scoped BigOperators Topology

/-- Choose a common positive power for each class of orders that share a
positive power. Distinct chosen orders have no common positive power. -/
private lemma synchronize_orders {ι : Type*} [Fintype ι] (k : ι → ℕ) :
    ∃ q : ι → ℕ, (∀ i, ∃ d : ℕ, 0 < d ∧ k i ^ d = q i) ∧
      ∀ i j, q i ≠ q j → ∀ a b : ℕ, 0 < a → 0 < b → q i ^ a ≠ q j ^ b := by
  classical
  let rel (x y : ℕ) := ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ x ^ a = y ^ b
  have refl (x : ℕ) : rel x x := ⟨1, 1, by decide, by decide, rfl⟩
  have symm {x y : ℕ} : rel x y → rel y x := by
    rintro ⟨a, b, ha, hb, h⟩
    exact ⟨b, a, hb, ha, h.symm⟩
  have trans {x y z : ℕ} : rel x y → rel y z → rel x z := by
    rintro ⟨a, b, ha, hb, hxy⟩ ⟨c, d, hc, hd, hyz⟩
    refine ⟨a * c, d * b, Nat.mul_pos ha hc, Nat.mul_pos hd hb, ?_⟩
    calc
      x ^ (a * c) = (y ^ b) ^ c := by rw [pow_mul, hxy]
      _ = (y ^ c) ^ b := by rw [← pow_mul, Nat.mul_comm b c, pow_mul]
      _ = z ^ (d * b) := by rw [hyz, pow_mul]
  let common (i : ι) (m : ℕ) :=
    ∀ j, rel (k i) (k j) → ∃ d : ℕ, 0 < d ∧ k j ^ d = m
  have exists_common (i : ι) : ∃ m, common i m := by
    have exponent (j : ι) : ∃ e : ℕ, 0 < e ∧
        (rel (k i) (k j) → ∃ f : ℕ, 0 < f ∧ k i ^ e = k j ^ f) := by
      by_cases hr : rel (k i) (k j)
      · obtain ⟨e, f, he, hf, h⟩ := hr
        exact ⟨e, he, fun _ => ⟨f, hf, h⟩⟩
      · exact ⟨1, by decide, fun h => (hr h).elim⟩
    choose e he witness using exponent
    let D := ∏ j, e j
    have hD : 0 < D := Finset.prod_pos fun j _ => he j
    refine ⟨k i ^ D, fun j hrel => ?_⟩
    obtain ⟨f, hf, heq⟩ := witness j hrel
    obtain ⟨c, hc⟩ : e j ∣ D := Finset.dvd_prod_of_mem e (Finset.mem_univ j)
    have hcpos : 0 < c := by
      by_contra! h
      have : c = 0 := by omega
      simp [hc, this] at hD
    exact ⟨f * c, Nat.mul_pos hf hcpos, by rw [hc, pow_mul, pow_mul, heq]⟩
  let q (i : ι) := Nat.find (exists_common i)
  have hp (i : ι) : ∃ d : ℕ, 0 < d ∧ k i ^ d = q i :=
    Nat.find_spec (exists_common i) i (refl _)
  refine ⟨q, hp, ?_⟩
  intro i j hne a b ha hb hab
  obtain ⟨u, hu, hi⟩ := hp i
  obtain ⟨v, hv, hj⟩ := hp j
  have hij : rel (k i) (k j) := ⟨u * a, v * b, Nat.mul_pos hu ha,
    Nat.mul_pos hv hb, by simpa only [pow_mul, hi, hj] using hab⟩
  apply hne
  apply Nat.find_congr'
  intro m
  exact ⟨fun h l hl => h l (trans hij hl), fun h l hl => h l (trans (symm hij) hl)⟩

/-- Express a state at level u in terms of all states at the common level u + v.
The coefficients are polynomials in the original argument. -/
private lemma iterate_dissection {σ : Type*} [Fintype σ] {k : ℕ} (hk : 0 < k)
    (F : σ → ℝ → ℝ) (tr : σ → Fin k → σ)
    (step : ∀ s z, |z| < 1 → F s z = ∑ j : Fin k, z ^ j.val * F (tr s j) (z ^ k))
    (s : σ) (u v : ℕ) :
    ∃ row : σ → Polynomial ℚ, ∀ z : ℝ, |z| < 1 →
      F s (z ^ (k ^ u)) = ∑ t, aeval z (row t) * F t (z ^ (k ^ (u + v))) := by
  classical
  induction v generalizing s u with
  | zero =>
    refine ⟨fun t => if t = s then 1 else 0, fun z _ => ?_⟩
    simp [apply_ite, ite_mul]
  | succ v ih =>
    choose row hrow using fun j : Fin k => ih (tr s j) (u + 1)
    refine ⟨fun t => ∑ j : Fin k, X ^ (k ^ u * j.val) * row j t, fun z hz => ?_⟩
    have hz' : |z ^ (k ^ u)| < 1 := by
      rw [abs_pow]
      exact pow_lt_one₀ (abs_nonneg z) hz (pow_ne_zero _ hk.ne')
    have hlevel : (z ^ (k ^ u)) ^ k = z ^ (k ^ (u + 1)) := by
      rw [← pow_mul, pow_succ k]
    have hlast : u + 1 + v = u + (v + 1) := by omega
    calc
      F s (z ^ (k ^ u)) =
          ∑ j : Fin k, (z ^ (k ^ u)) ^ j.val * F (tr s j) (z ^ (k ^ (u + 1))) := by
            rw [← hlevel]
            exact step s _ hz'
      _ = ∑ j : Fin k, ∑ t : σ,
          (aeval z (X ^ (k ^ u * j.val) * row j t)) * F t (z ^ (k ^ (u + (v + 1)))) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hrow j z hz, Finset.mul_sum, hlast]
            simp only [map_mul, map_pow, aeval_X, pow_mul, mul_assoc]
      _ = _ := by
        rw [Finset.sum_comm]
        simp only [map_sum, Finset.sum_mul]

/-- At any positive power of the transformation order, n states give a scalar
Mahler equation of order at most n. All n + 1 rows are compared at the same
iterate before taking a polynomial linear dependence. -/
private lemma scalar_equation {σ : Type*} [Fintype σ] {k : ℕ} (hk : 0 < k)
    (F : σ → ℝ → ℝ) (tr : σ → Fin k → σ)
    (step : ∀ s z, |z| < 1 → F s z = ∑ j : Fin k, z ^ j.val * F (tr s j) (z ^ k))
    (s : σ) (d : ℕ) :
    ∃ P : Fin (Fintype.card σ + 1) → Polynomial ℚ, (∃ j, P j ≠ 0) ∧
      ∀ z : ℝ, |z| < 1 →
        ∑ j, aeval z (P j) * F s (z ^ ((k ^ d) ^ j.val)) = 0 := by
  classical
  let n := Fintype.card σ
  have expand (j : Fin (n + 1)) :
      ∃ A : σ → Polynomial ℚ, ∀ z : ℝ, |z| < 1 →
        F s (z ^ ((k ^ d) ^ j.val)) = ∑ t, aeval z (A t) * F t (z ^ (k ^ (d * n))) := by
    have hj : j.val + (n - j.val) = n := by omega
    obtain ⟨A, hA⟩ := iterate_dissection hk F tr step s (d * j.val) (d * (n - j.val))
    exact ⟨A, by simpa only [← pow_mul, ← Nat.mul_add, hj] using hA⟩
  choose A hA using expand
  have hdep : ¬ LinearIndependent (Polynomial ℚ) A := by
    intro hind
    have hc := (Pi.basisFun (Polynomial ℚ) σ).card_le_card_of_linearIndependent hind
    have : n + 1 ≤ n := by simpa only [Fintype.card_fin] using hc
    omega
  obtain ⟨P, hzero, hnonzero⟩ := Fintype.not_linearIndependent_iff.mp hdep
  refine ⟨P, hnonzero, fun z hz => ?_⟩
  have cancel (t : σ) : ∑ j, aeval z (P j) * aeval z (A j t) = 0 := by
    have hpoly : ∑ j, P j * A j t = 0 := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using congrFun hzero t
    simpa only [map_sum, map_mul, map_zero] using congrArg (aeval z) hpoly
  change ∑ j : Fin (n + 1), aeval z (P j) * F s (z ^ ((k ^ d) ^ j.val)) = 0
  simp_rw [hA _ z hz, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, cancel, zero_mul, Finset.sum_const_zero]

/-- Distinct monomials have distinct values at a positive point with
independent logarithms. Only finitely many exceed any fixed positive bound. -/
private lemma monomial_weights {ι : Type*} [Fintype ι] (α : ι → ℝ)
    (hα : ∀ i, 0 < α i ∧ α i < 1) (hlog : LinearIndependent ℚ (fun i => Real.log (α i))) :
    let w := fun (m : ι → ℕ) => ∏ i, α i ^ m i
    Function.Injective w ∧ ∀ x : ℝ, 0 < x → {m | x ≤ w m}.Finite := by
  classical
  let w (m : ι → ℕ) := ∏ i, α i ^ m i
  have logw (m : ι → ℕ) : Real.log (w m) = ∑ i, (m i : ℚ) • Real.log (α i) := by
    rw [show Real.log (w m) = _ from Real.log_prod (fun i _ => pow_ne_zero (m i) (hα i).1.ne')]
    simp [Real.log_pow, Rat.smul_def]
  constructor
  · intro u v heq
    have hs : (∑ i, ((u i : ℚ) - v i) • Real.log (α i)) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← logw]
      exact sub_eq_zero.mpr (congrArg Real.log heq)
    ext i
    have hi := Fintype.linearIndependent_iff.mp hlog _ hs i
    exact_mod_cast sub_eq_zero.mp hi
  · intro x hx
    choose N hN using fun i => exists_pow_lt_of_lt_one hx (hα i).2
    refine (Set.Finite.pi' (fun i => Set.finite_Iio (N i))).subset ?_
    intro m hm i
    have hle : w m ≤ α i ^ m i := by
      simpa only [Finset.prod_singleton] using
        (Finset.prod_le_prod_of_subset_of_le_one (Finset.singleton_subset_iff.mpr (Finset.mem_univ i))
          (fun j _ => pow_nonneg (hα j).1.le (m j))
          (fun j _ _ => pow_le_one₀ (hα j).1.le (hα j).2.le))
    change m i < N i
    by_contra! h
    exact (hN i).not_ge (le_trans (le_trans hm hle)
      (pow_le_pow_of_le_one (hα i).1.le (hα i).2.le h))

/-- After division by the largest weight on the support, the series tends
to its nonzero leading coefficient. -/
private lemma dominant_monomial {M : Type*} (w : M → ℝ) (hw : ∀ m, 0 < w m)
    (hinj : Function.Injective w) (hfinite : ∀ x : ℝ, 0 < x → {m | x ≤ w m}.Finite)
    (c : M → ℂ) (hc : ∃ m, c m ≠ 0) {L : ℕ}
    (hsum : Summable (fun m => ‖c m‖ * w m ^ L)) :
    ∀ᶠ n : ℕ in atTop, (∑' m, w m ^ n • c m) ≠ 0 := by
  classical
  obtain ⟨b, hb⟩ := hc
  let S := {m | w b ≤ w m ∧ c m ≠ 0}
  have hS : S.Finite := (hfinite (w b) (hw b)).subset fun m hm => hm.1
  obtain ⟨p, hp, hmax⟩ := S.exists_max_image w hS ⟨b, le_rfl, hb⟩
  have htop {m} (hm : c m ≠ 0) : w m ≤ w p := by
    by_cases h : w b ≤ w m
    · exact hmax m ⟨h, hm⟩
    · exact (le_of_not_ge h).trans hp.1
  let ratio (m : M) := w m / w p
  have hpos (m) : 0 < ratio m := div_pos (hw m) (hw p)
  have hlimit (m : M) :
      Tendsto (fun n : ℕ => ratio m ^ n • c m) atTop (𝓝 (if m = p then c p else 0)) := by
    by_cases heq : m = p
    · subst m
      simp [ratio, (hw p).ne']
    · rw [if_neg heq]
      by_cases hcm : c m = 0
      · simp [hcm]
      · have hlt : ratio m < 1 :=
          (div_lt_one (hw p)).mpr ((htop hcm).lt_of_ne fun h => heq (hinj h))
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (hpos m).le hlt).smul_const (c m)
  have hs : Summable (fun m => ‖c m‖ * ratio m ^ L) := by
    simpa only [ratio, div_eq_mul_inv, mul_pow, inv_pow, mul_assoc] using (hsum.mul_right (w p ^ L)⁻¹)
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ m, ‖ratio m ^ n • c m‖ ≤ ‖c m‖ * ratio m ^ L := by
    filter_upwards [eventually_ge_atTop L] with n hn m
    by_cases hz : c m = 0
    · simp [hz]
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hpos m).le n), mul_comm]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (hpos m).le ((div_le_one (hw p)).mpr (htop hz)) hn) (norm_nonneg _)
  have hlim : Tendsto (fun n : ℕ => ∑' m, ratio m ^ n • c m) atTop (𝓝 (c p)) := by
    simpa only [tsum_ite_eq] using tendsto_tsum_of_dominated_convergence hs hlimit hbound
  filter_upwards [hlim.eventually_ne hp.2] with n hn
  contrapose! hn
  calc
    (∑' m, ratio m ^ n • c m) = (w p ^ n)⁻¹ • ∑' m, w m ^ n • c m := by
      rw [← tsum_const_smul'']
      apply tsum_congr
      intro m
      simp only [ratio, smul_smul, div_eq_inv_mul, mul_pow, inv_pow]
    _ = 0 := by rw [hn, smul_zero]

/-- Nonvanishing on the diagonal Mahler orbit for every nonzero complex power
series absolutely convergent at one point on the ray of powers of α. -/
private lemma diagonal_nonvanishing {ι : Type*} [Fintype ι] (q : ℕ) (hq : 2 ≤ q)
    (α : ι → ℝ) (hα : ∀ i, 0 < α i ∧ α i < 1)
    (hlog : LinearIndependent ℚ (fun i => Real.log (α i)))
    (c : (ι → ℕ) → ℂ) (hc : ∃ m, c m ≠ 0) (L : ℕ)
    (hL : Summable (fun m => ‖c m‖ * (∏ i, α i ^ m i) ^ L)) :
    ∀ᶠ n : ℕ in atTop, (∑' m, (∏ i, α i ^ m i) ^ (q ^ n) • c m) ≠ 0 := by
  obtain ⟨hinj, hfinite⟩ := monomial_weights α hα hlog
  have h := dominant_monomial (fun m : ι → ℕ => ∏ i, α i ^ m i)
    (fun m => Finset.prod_pos fun i _ => pow_pos (hα i).1 _) hinj hfinite c hc hL
  exact (tendsto_pow_atTop_atTop_of_one_lt (show 1 < q from hq)).eventually h

/-- The common-order case of the first purity theorem. Each series is given
by bounded natural coefficients and a scalar polynomial Mahler equation.
The hypothesis on complex series gives diagonal orbit admissibility. -/
def H1 : Prop :=
  ∀ (ι : Type) [Fintype ι] (q : ℕ) (α : ι → ℚ) (a : ι → ℕ → ℕ),
    let F := fun i (z : ℝ) => ∑' n : ℕ, (a i n : ℝ) * z ^ n
    2 ≤ q → (∀ i, 0 < α i ∧ α i < 1) →
    (∀ (c : (ι → ℕ) → ℂ), (∃ m, c m ≠ 0) → ∀ L : ℕ,
      Summable (fun m => ‖c m‖ * (∏ i, (α i : ℝ) ^ m i) ^ L) →
      ∀ᶠ n : ℕ in atTop, (∑' m, (∏ i, (α i : ℝ) ^ m i) ^ (q ^ n) • c m) ≠ 0) →
    (∀ i, ∃ B : ℕ, ∀ n, a i n ≤ B) →
    (∀ i, ∃ (m : ℕ) (P : Fin (m + 1) → Polynomial ℚ), (∃ j, P j ≠ 0) ∧
      ∀ z : ℝ, |z| < 1 → ∑ j, aeval z (P j) * F i (z ^ (q ^ j.val)) = 0) →
    (∀ i, Transcendental ℚ (F i (α i))) → AlgebraicIndependent ℚ (fun i => F i (α i))

/-- The dependence consequence of the second purity theorem. When distinct
orders have no common power, a polynomial relation among all values forces
a polynomial relation in one equal-order block. -/
def H2 : Prop :=
  ∀ (r : ℕ) (q : Fin r → ℕ) (α : Fin r → ℚ) (a : Fin r → ℕ → ℕ),
    let F := fun i (z : ℝ) => ∑' n : ℕ, (a i n : ℝ) * z ^ n
    let y := fun i => F i (α i)
    (∃ i j, q i ≠ q j) →
    (∀ i j, q i ≠ q j → ∀ u v : ℕ, 0 < u → 0 < v → q i ^ u ≠ q j ^ v) →
    (∀ i, 2 ≤ q i) → (∀ i, 0 < α i ∧ α i < 1) →
    (∀ t : Set.range q,
      let w := fun m : {i // q i = t.val} → ℕ => ∏ i, (α i.val : ℝ) ^ m i
      ∀ (c : ({i // q i = t.val} → ℕ) → ℂ), (∃ m, c m ≠ 0) → ∀ L : ℕ,
        Summable (fun m => ‖c m‖ * w m ^ L) →
        ∀ᶠ n : ℕ in atTop, (∑' m, w m ^ (t.val ^ n) • c m) ≠ 0) →
    (∀ i, ∃ B : ℕ, ∀ n, a i n ≤ B) →
    (∀ i, ∃ (m : ℕ) (P : Fin (m + 1) → Polynomial ℚ), (∃ j, P j ≠ 0) ∧
      ∀ z : ℝ, |z| < 1 → ∑ j, aeval z (P j) * F i (z ^ (q i ^ j.val)) = 0) →
    ∀ P : MvPolynomial (Fin r) ℚ, P ≠ 0 → MvPolynomial.aeval y P = 0 →
      ∃ (t : Set.range q) (Q : MvPolynomial {i // q i = t.val} ℚ),
        Q ≠ 0 ∧ MvPolynomial.aeval (fun i => y i.val) Q = 0

theorem main : H1 → H2 → OMA.R_Bugeaud32_adamczewski_faverjon_R1.H2 := by
  classical
  intro first second r k B α a hk hα hlog hsys htrans
  let F (i : Fin r) (z : ℝ) := ∑' n : ℕ, (a i n : ℝ) * z ^ n
  change AlgebraicIndependent ℚ (fun i => F i (α i))
  obtain ⟨q, hpowers, separate⟩ := synchronize_orders k
  choose d hd hq using hpowers
  have hq2 (i) : 2 ≤ q i := by
    rw [← hq i]
    exact one_lt_pow₀ (show 1 < k i from hk i) (hd i).ne'
  have bounded (i) : ∃ b : ℕ, ∀ n, a i n ≤ b := by
    obtain ⟨S, ha, hbound, _⟩ := hsys i
    exact ⟨B i, hbound _ ha⟩
  have scalar (i) : ∃ (m : ℕ) (P : Fin (m + 1) → Polynomial ℚ), (∃ j, P j ≠ 0) ∧
      ∀ z : ℝ, |z| < 1 → ∑ j, aeval z (P j) * F i (z ^ (q i ^ j.val)) = 0 := by
    obtain ⟨S, ha, _, tr, step⟩ := hsys i
    let G (s : S) (z : ℝ) := ∑' n : ℕ, (s.val n : ℝ) * z ^ n
    rw [← hq i]
    exact ⟨Fintype.card S, scalar_equation (by have := hk i; omega) G tr step ⟨a i, ha⟩ (d i)⟩
  have hαR (i) : 0 < (α i : ℝ) ∧ (α i : ℝ) < 1 := by exact_mod_cast hα i
  have order_bound (t : Set.range q) : 2 ≤ t.val := by
    obtain ⟨i, hi⟩ := t.property
    exact hi ▸ hq2 i
  have orbit (t : Set.range q) := diagonal_nonvanishing t.val (order_bound t)
    (fun i : {i // q i = t.val} => (α i.val : ℝ)) (fun i => hαR i.val)
    (hlog.comp _ Subtype.val_injective)
  by_cases hdistinct : ∃ i j, q i ≠ q j
  · rw [algebraicIndependent_iff]
    intro P hP
    by_contra hne
    obtain ⟨t, Q, hQ, heval⟩ :=
      second r q α a hdistinct separate hq2 hα orbit bounded scalar P hne hP
    have hblock := first {i // q i = t.val} t.val (fun i => α i.val) (fun i => a i.val)
      (order_bound t) (fun i => hα i.val) (orbit t) (fun i => bounded i.val)
      (fun i => by simpa only [i.property] using scalar i.val) (fun i => htrans i.val)
    exact hQ (algebraicIndependent_iff.mp hblock Q heval)
  · cases isEmpty_or_nonempty (Fin r) with
    | inl _ => exact algebraicIndependent_empty_type
    | inr h =>
      obtain ⟨i₀⟩ := h
      have hsame (i) : q i = q i₀ := by
        by_contra h
        exact hdistinct ⟨i, i₀, h⟩
      exact first (Fin r) (q i₀) α a (hq2 i₀) hα
        (diagonal_nonvanishing _ (hq2 i₀) (fun i => (α i : ℝ)) hαR hlog) bounded
        (fun i => by simpa only [hsame i] using scalar i) htrans

end OMA.R_Bugeaud32_adamczewski_faverjon_R1_H2_R1
