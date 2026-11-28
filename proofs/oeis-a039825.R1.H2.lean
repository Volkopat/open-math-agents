import OMAReductions.R_oeis_a039825_R1

/-!
# Proof of `oeis-a039825.R1.H2`

Gauss's triangular-number identity in truncated formal power series over `ℚ`:
for every `m` and `i ≤ 2 * m`, the `i`-th coefficient of
`∏_{j=0}^{m-1} (1 - X^(2(j+1))) * (∏_{j=0}^{m-1} (1 - X^(2j+1)))⁻¹`
is `1` if `i` is a triangular number `n(n+1)/2` and `0` otherwise.

Proof via the finite `q`-binomial theorem in `(ℚ⟦X⟧)[Y]`, specialized at `Y = X^(-N)`
inside `FractionRing (ℚ⟦X⟧)` (cleared by `X^(N(N+1)/2)`), then reduced modulo `X^(2m+1)`
with `N = 4m + 2`.
-/

-- Step oeis-a039825.R1.H2: hypothesis H2 of reduction oeis-a039825.R1
-- Credit: @lettucrisp

namespace OeisA039825H2

open PowerSeries Classical

/-- Congruence of power series modulo `X^(D + 1)`. -/
private def ModEq (D : ℕ) (f g : ℚ⟦X⟧) : Prop :=
  ∀ i ≤ D, coeff i f = coeff i g

private lemma ModEq.refl (D : ℕ) (f : ℚ⟦X⟧) : ModEq D f f := fun _ _ => rfl

private lemma ModEq.symm {D : ℕ} {f g : ℚ⟦X⟧} (h : ModEq D f g) : ModEq D g f :=
  fun i hi => (h i hi).symm

private lemma ModEq.trans {D : ℕ} {f g h : ℚ⟦X⟧} (h1 : ModEq D f g) (h2 : ModEq D g h) :
    ModEq D f h :=
  fun i hi => (h1 i hi).trans (h2 i hi)

private lemma ModEq.add {D : ℕ} {f₁ g₁ f₂ g₂ : ℚ⟦X⟧}
    (h1 : ModEq D f₁ g₁) (h2 : ModEq D f₂ g₂) : ModEq D (f₁ + f₂) (g₁ + g₂) := by
  intro i hi
  simp only [map_add, h1 i hi, h2 i hi]

private lemma ModEq.sub {D : ℕ} {f₁ g₁ f₂ g₂ : ℚ⟦X⟧}
    (h1 : ModEq D f₁ g₁) (h2 : ModEq D f₂ g₂) : ModEq D (f₁ - f₂) (g₁ - g₂) := by
  intro i hi
  simp only [map_sub, h1 i hi, h2 i hi]

private lemma ModEq.mul {D : ℕ} {f₁ g₁ f₂ g₂ : ℚ⟦X⟧}
    (h1 : ModEq D f₁ g₁) (h2 : ModEq D f₂ g₂) : ModEq D (f₁ * f₂) (g₁ * g₂) := by
  intro i hi
  simp only [PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp_eq := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [h1 p.1 (by omega), h2 p.2 (by omega)]

private lemma ModEq.finset_sum {ι : Type*} (s : Finset ι) (D : ℕ) (f g : ι → ℚ⟦X⟧)
    (h : ∀ x ∈ s, ModEq D (f x) (g x)) :
    ModEq D (∑ x ∈ s, f x) (∑ x ∈ s, g x) := by
  intro i hi
  simp only [map_sum]
  exact Finset.sum_congr rfl fun x hx => h x hx i hi

private lemma ModEq.finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (D : ℕ)
    (f g : ι → ℚ⟦X⟧) (h : ∀ x ∈ s, ModEq D (f x) (g x)) :
    ModEq D (∏ x ∈ s, f x) (∏ x ∈ s, g x) := by
  induction s using Finset.induction_on with
  | empty => exact ModEq.refl D 1
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact ModEq.mul (h a (Finset.mem_insert_self a s))
      (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

private lemma ModEq.inv {D : ℕ} {f g : ℚ⟦X⟧}
    (h : ModEq D f g) (hf0 : constantCoeff f ≠ 0) : ModEq D f⁻¹ g⁻¹ := by
  have hg0 : constantCoeff g ≠ 0 := by
    have h0 := h 0 (Nat.zero_le D)
    rw [PowerSeries.coeff_zero_eq_constantCoeff] at h0
    exact h0.symm.trans_ne hf0
  have hfg : ModEq D (f⁻¹ * (g * g⁻¹)) (f⁻¹ * (f * g⁻¹)) :=
    ModEq.mul (ModEq.refl D _) (ModEq.mul h.symm (ModEq.refl D _))
  rw [PowerSeries.mul_inv_cancel g hg0, mul_one] at hfg
  have hff : f⁻¹ * (f * g⁻¹) = g⁻¹ := by
    rw [← mul_assoc, mul_comm f⁻¹ f, PowerSeries.mul_inv_cancel f hf0, one_mul]
  rw [hff] at hfg
  exact hfg

private lemma modEq_X_pow_zero {D k : ℕ} (hk : D < k) : ModEq D (X ^ k : ℚ⟦X⟧) 0 := by
  intro i hi
  rw [PowerSeries.coeff_X_pow, map_zero, if_neg (by omega)]

private lemma modEq_one_sub_X_pow {D k : ℕ} (hk : D < k) :
    ModEq D (1 - X ^ k : ℚ⟦X⟧) 1 := by
  simpa using ModEq.sub (ModEq.refl D 1) (modEq_X_pow_zero hk)

private lemma modEq_one_add_X_pow {D k : ℕ} (hk : D < k) :
    ModEq D (1 + X ^ k : ℚ⟦X⟧) 1 := by
  simpa using ModEq.add (ModEq.refl D 1) (modEq_X_pow_zero hk)

private noncomputable def qFact (n : ℕ) : ℚ⟦X⟧ :=
  ∏ k ∈ Finset.range n, (1 - X ^ (k + 1))

private lemma constantCoeff_qFact (n : ℕ) : constantCoeff (qFact n) = 1 := by
  unfold qFact
  rw [map_prod]
  refine Finset.prod_eq_one fun k _ => ?_
  simp [map_sub, map_pow, PowerSeries.constantCoeff_X, zero_pow (Nat.succ_ne_zero k)]

private lemma qFact_mul_inv (n : ℕ) : qFact n * (qFact n)⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_qFact]; norm_num)

private lemma qFact_succ (n : ℕ) : qFact (n + 1) = qFact n * (1 - X ^ (n + 1)) := by
  unfold qFact
  rw [Finset.prod_range_succ]

private lemma inv_qFact_pred {n : ℕ} (hn : 1 ≤ n) :
    (qFact (n - 1))⁻¹ = (1 - X ^ n) * (qFact n)⁻¹ := by
  have hsucc : qFact n = qFact (n - 1) * (1 - X ^ n) := by
    have : n - 1 + 1 = n := by omega
    conv_lhs => rw [← this, qFact_succ]
    rw [this]
  calc (qFact (n - 1))⁻¹ = (qFact (n - 1))⁻¹ * (qFact n * (qFact n)⁻¹) := by
        rw [qFact_mul_inv, mul_one]
    _ = ((qFact (n - 1)) * (qFact (n - 1))⁻¹) * ((1 - X ^ n) * (qFact n)⁻¹) := by
        rw [hsucc]; ring
    _ = (1 - X ^ n) * (qFact n)⁻¹ := by rw [qFact_mul_inv, one_mul]

private noncomputable def qBinom (n r : ℕ) : ℚ⟦X⟧ :=
  qFact n * (qFact r)⁻¹ * (qFact (n - r))⁻¹

private lemma qBinom_zero (n : ℕ) : qBinom n 0 = 1 := by
  unfold qBinom
  have h0 : qFact 0 = 1 := by simp [qFact]
  rw [Nat.sub_zero, h0, inv_one, mul_one, qFact_mul_inv]

private lemma qBinom_self (n : ℕ) : qBinom n n = 1 := by
  unfold qBinom
  have h0 : qFact 0 = 1 := by simp [qFact]
  rw [Nat.sub_self, h0, inv_one, mul_one, qFact_mul_inv]

private lemma qBinom_succ {n r : ℕ} (hr1 : 1 ≤ r) (hrn : r ≤ n) :
    qBinom (n + 1) r = qBinom n r + X ^ (n + 1 - r) * qBinom n (r - 1) := by
  unfold qBinom
  have h1 : n + 1 - r - 1 = n - r := by omega
  have h2 : n - (r - 1) = n + 1 - r := by omega
  have hi1 : (qFact (n - r))⁻¹ = (1 - X ^ (n + 1 - r)) * (qFact (n + 1 - r))⁻¹ := by
    simpa [h1] using inv_qFact_pred (n := n + 1 - r) (by omega)
  have hi2 : (qFact (r - 1))⁻¹ = (1 - X ^ r) * (qFact r)⁻¹ :=
    inv_qFact_pred hr1
  rw [qFact_succ, h2, hi1, hi2]
  have hpow : X ^ (n + 1 - r) * X ^ r = (X ^ (n + 1) : ℚ⟦X⟧) := by
    rw [← pow_add, show n + 1 - r + r = n + 1 by omega]
  have hfac : (1 - X ^ (n + 1 - r)) + X ^ (n + 1 - r) * (1 - X ^ r) =
      (1 - X ^ (n + 1) : ℚ⟦X⟧) := by
    rw [mul_sub, mul_one, hpow]; ring
  calc qFact n * (1 - X ^ (n + 1)) * (qFact r)⁻¹ * (qFact (n + 1 - r))⁻¹
      = qFact n * (qFact r)⁻¹ * (qFact (n + 1 - r))⁻¹ *
          ((1 - X ^ (n + 1 - r)) + X ^ (n + 1 - r) * (1 - X ^ r)) := by
        rw [hfac]; ring
    _ = qFact n * (qFact r)⁻¹ * ((1 - X ^ (n + 1 - r)) * (qFact (n + 1 - r))⁻¹) +
          X ^ (n + 1 - r) * (qFact n * ((1 - X ^ r) * (qFact r)⁻¹) * (qFact (n + 1 - r))⁻¹) := by
        ring

private lemma tri_succ_arith (n : ℕ) : (n + 1) * n / 2 = n * (n - 1) / 2 + n := by
  cases n with
  | zero => simp
  | succ k =>
    have h1 : k + 1 - 1 = k := by omega
    rw [h1]
    have h2 : (k + 1 + 1) * (k + 1) = (k + 1) * k + 2 * (k + 1) := by ring
    rw [h2]
    omega

private lemma qBinom_thm (M : ℕ) :
    (∏ k ∈ Finset.range M, (1 + Polynomial.C (X ^ k : ℚ⟦X⟧) * Polynomial.X)) =
      ∑ r ∈ Finset.range (M + 1),
        Polynomial.C (qBinom M r * X ^ (r * (r - 1) / 2)) * Polynomial.X ^ r := by
  induction M with
  | zero =>
    simp [qBinom_zero]
  | succ M ih =>
    rw [Finset.prod_range_succ, ih, mul_add, mul_one, Finset.sum_mul]
    have hterm2 :
        (∑ r ∈ Finset.range (M + 1),
          Polynomial.C (qBinom M r * X ^ (r * (r - 1) / 2)) * Polynomial.X ^ r *
            (Polynomial.C (X ^ M : ℚ⟦X⟧) * Polynomial.X)) =
        ∑ r ∈ Finset.range (M + 1),
          Polynomial.C (X ^ M * (qBinom M r * X ^ (r * (r - 1) / 2))) *
            Polynomial.X ^ (r + 1) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [map_mul, pow_succ]
      ring
    rw [hterm2]
    rw [Finset.sum_range_succ' _ M, Finset.sum_range_succ _ M]
    have hlhs :
        (∑ k ∈ Finset.range M,
            Polynomial.C (qBinom M (k + 1) * X ^ ((k + 1) * k / 2)) * Polynomial.X ^ (k + 1)) +
          Polynomial.C (qBinom M 0 * X ^ (0 * (0 - 1) / 2)) * Polynomial.X ^ 0 +
        ((∑ r ∈ Finset.range M,
            Polynomial.C (X ^ M * (qBinom M r * X ^ (r * (r - 1) / 2))) * Polynomial.X ^ (r + 1)) +
          Polynomial.C (X ^ M * (qBinom M M * X ^ (M * (M - 1) / 2))) * Polynomial.X ^ (M + 1)) =
        Polynomial.C (qBinom (M + 1) 0 * X ^ 0) * Polynomial.X ^ 0 +
        (∑ k ∈ Finset.range M,
            Polynomial.C (qBinom (M + 1) (k + 1) * X ^ ((k + 1) * k / 2)) * Polynomial.X ^ (k + 1)) +
        Polynomial.C (qBinom (M + 1) (M + 1) * X ^ ((M + 1) * M / 2)) * Polynomial.X ^ (M + 1) := by
      have hmid :
          (∑ k ∈ Finset.range M,
              Polynomial.C (qBinom M (k + 1) * X ^ ((k + 1) * k / 2)) * Polynomial.X ^ (k + 1)) +
          (∑ r ∈ Finset.range M,
              Polynomial.C (X ^ M * (qBinom M r * X ^ (r * (r - 1) / 2))) * Polynomial.X ^ (r + 1)) =
          ∑ k ∈ Finset.range M,
              Polynomial.C (qBinom (M + 1) (k + 1) * X ^ ((k + 1) * k / 2)) *
                Polynomial.X ^ (k + 1) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkM : k + 1 ≤ M := Finset.mem_range.mp hk
        rw [← add_mul, ← map_add]
        congr 2
        rw [qBinom_succ (by omega) hkM, add_mul (qBinom M (k + 1))]
        congr 1
        have htri : (k + 1) * k / 2 + (M - k) = M + k * (k - 1) / 2 := by
          have := tri_succ_arith k
          omega
        have hpow : X ^ (M + 1 - (k + 1)) * X ^ ((k + 1) * k / 2) =
            (X ^ M * X ^ (k * (k - 1) / 2) : ℚ⟦X⟧) := by
          rw [← pow_add, ← pow_add, show M + 1 - (k + 1) = M - k by omega,
            add_comm (M - k), htri]
        have hsub : k + 1 - 1 = k := by omega
        rw [hsub]
        calc X ^ M * (qBinom M k * X ^ (k * (k - 1) / 2))
            = qBinom M k * (X ^ M * X ^ (k * (k - 1) / 2)) := by ring
          _ = qBinom M k * (X ^ (M + 1 - (k + 1)) * X ^ ((k + 1) * k / 2)) := by rw [← hpow]
          _ = X ^ (M + 1 - (k + 1)) * qBinom M k * X ^ ((k + 1) * k / 2) := by ring
      have h0 : qBinom M 0 = qBinom (M + 1) 0 := by rw [qBinom_zero, qBinom_zero]
      have htop : X ^ M * (qBinom M M * X ^ (M * (M - 1) / 2)) =
          qBinom (M + 1) (M + 1) * X ^ ((M + 1) * M / 2) := by
        rw [qBinom_self, qBinom_self, one_mul, one_mul, ← pow_add, add_comm M, ← tri_succ_arith]
      rw [h0, htop]
      calc (∑ k ∈ Finset.range M,
              Polynomial.C (qBinom M (k + 1) * X ^ ((k + 1) * k / 2)) * Polynomial.X ^ (k + 1)) +
            Polynomial.C (qBinom (M + 1) 0 * X ^ (0 * (0 - 1) / 2)) * Polynomial.X ^ 0 +
          ((∑ r ∈ Finset.range M,
              Polynomial.C (X ^ M * (qBinom M r * X ^ (r * (r - 1) / 2))) *
                Polynomial.X ^ (r + 1)) +
            Polynomial.C (qBinom (M + 1) (M + 1) * X ^ ((M + 1) * M / 2)) *
              Polynomial.X ^ (M + 1))
          = Polynomial.C (qBinom (M + 1) 0 * X ^ 0) * Polynomial.X ^ 0 +
            ((∑ k ∈ Finset.range M,
                Polynomial.C (qBinom M (k + 1) * X ^ ((k + 1) * k / 2)) * Polynomial.X ^ (k + 1)) +
              (∑ r ∈ Finset.range M,
                Polynomial.C (X ^ M * (qBinom M r * X ^ (r * (r - 1) / 2))) *
                  Polynomial.X ^ (r + 1))) +
            Polynomial.C (qBinom (M + 1) (M + 1) * X ^ ((M + 1) * M / 2)) *
              Polynomial.X ^ (M + 1) := by ring
        _ = _ := by rw [hmid]
    simp only [Nat.add_sub_cancel]
    rw [hlhs]
    rw [Finset.sum_range_succ _ (M + 1), Finset.sum_range_succ' _ M]
    simp only [Nat.add_sub_cancel]
    ring

private def triDist (N r : ℕ) : ℕ :=
  if r ≤ N then (N - r) * (N - r + 1) / 2 else (r - N - 1) * (r - N) / 2

private lemma triDist_identity (N r : ℕ) :
    r * (r - 1) / 2 + N * (N + 1) / 2 = N * r + triDist N r := by
  have hev : ∀ k : ℕ, 2 * (k * (k + 1) / 2) = k * (k + 1) := by
    intro k
    have hd : 2 ∣ k * (k + 1) := by
      rcases Nat.even_or_odd k with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact ⟨t * (t + t + 1), by ring⟩
      · exact ⟨(2 * t + 1) * (t + 1), by ring⟩
    exact Nat.mul_div_cancel' hd
  have hev' : ∀ k : ℕ, 2 * (k * (k - 1) / 2) = k * (k - 1) := by
    intro k
    cases k with
    | zero => simp
    | succ t => simpa [Nat.mul_comm] using hev t
  suffices h2 : 2 * (r * (r - 1) / 2 + N * (N + 1) / 2) = 2 * (N * r + triDist N r) by omega
  rw [mul_add 2 (r * (r - 1) / 2), mul_add 2 (N * r), hev' r, hev N]
  unfold triDist
  split_ifs with h
  · rw [hev (N - r)]
    cases r with
    | zero => simp
    | succ r' =>
      have hr : r' + 1 - 1 = r' := by omega
      rw [hr]
      zify [h]
      ring
  · push Not at h
    have hsub : r - N - 1 + 1 = r - N := by omega
    have h3 : 2 * ((r - N - 1) * (r - N) / 2) = (r - N - 1) * (r - N) := by
      simpa [hsub] using hev (r - N - 1)
    rw [h3]
    have hr1 : 1 ≤ r := by omega
    have hN1 : N + 1 ≤ r := by omega
    have hN : N ≤ r := by omega
    zify [hr1, hN1, hN]
    have hs1 : ((r - N - 1 : ℕ) : ℤ) = (r : ℤ) - (N : ℤ) - 1 := by omega
    rw [hs1]
    ring

private lemma sum_sub_range (N : ℕ) :
    ∑ k ∈ Finset.range N, (N - k) = N * (N + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ']
    have hstep : ∑ k ∈ Finset.range N, (N + 1 - (k + 1)) = ∑ k ∈ Finset.range N, (N - k) :=
      Finset.sum_congr rfl fun k _ => by omega
    rw [hstep, ih, Nat.sub_zero]
    have := tri_succ_arith (N + 1)
    simp only [Nat.add_sub_cancel] at this
    rw [Nat.mul_comm (N + 1) N] at this
    rw [Nat.mul_comm (N + 1) (N + 1 + 1)]
    omega

private lemma jacobi_finite (N : ℕ) :
    (∏ j ∈ Finset.range N, (1 + X ^ (j + 1) : ℚ⟦X⟧)) *
      (∏ t ∈ Finset.range N, (1 + X ^ t : ℚ⟦X⟧)) =
    ∑ r ∈ Finset.range (2 * N + 1), qBinom (2 * N) r * X ^ (triDist N r) := by
  let K := FractionRing ℚ⟦X⟧
  let ι : ℚ⟦X⟧ →+* K := algebraMap ℚ⟦X⟧ K
  have hι_inj : Function.Injective ι := IsFractionRing.injective ℚ⟦X⟧ K
  have hx_ne : (X : ℚ⟦X⟧) ≠ 0 := PowerSeries.X_ne_zero
  have hxK_ne : ι X ≠ 0 := by
    intro h
    exact hx_ne (hι_inj (h.trans (map_zero ι).symm))
  apply hι_inj
  have heval := congrArg (Polynomial.eval₂ ι ((ι X)⁻¹ ^ N)) (qBinom_thm (2 * N))
  have hmul := congrArg (fun z => (ι X) ^ (N * (N + 1) / 2) * z) heval
  have hlhs_eval :
      (ι X) ^ (N * (N + 1) / 2) *
        Polynomial.eval₂ ι ((ι X)⁻¹ ^ N)
          (∏ k ∈ Finset.range (2 * N), (1 + Polynomial.C (X ^ k : ℚ⟦X⟧) * Polynomial.X)) =
      ι ((∏ j ∈ Finset.range N, (1 + X ^ (j + 1) : ℚ⟦X⟧)) *
        (∏ t ∈ Finset.range N, (1 + X ^ t : ℚ⟦X⟧))) := by
    rw [Polynomial.eval₂_finsetProd]
    have hsplit : Finset.range (2 * N) =
        Finset.range N ∪ (Finset.range N).image (fun t => N + t) := by
      ext k
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_image]
      constructor
      · intro hk
        by_cases h : k < N
        · exact Or.inl h
        · exact Or.inr ⟨k - N, by omega, by omega⟩
      · rintro (h | ⟨t, ht, rfl⟩) <;> omega
    have hdisj : Disjoint (Finset.range N) ((Finset.range N).image (fun t => N + t)) := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      rw [Finset.mem_range] at hk1
      rcases Finset.mem_image.mp hk2 with ⟨t, _, rfl⟩
      omega
    rw [hsplit, Finset.prod_union hdisj, Finset.prod_image (fun a _ b _ hab => by omega)]
    rw [← mul_assoc, map_mul]
    congr 1
    · rw [← sum_sub_range N, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      rw [map_prod]
      have hrefl : ∏ j ∈ Finset.range N, ι (1 + X ^ (j + 1)) =
          ∏ k ∈ Finset.range N, ι (1 + X ^ (N - k)) := by
        rw [← Finset.prod_range_reflect (fun j => ι (1 + X ^ (j + 1))) N]
        refine Finset.prod_congr rfl fun k hk => ?_
        rw [Finset.mem_range] at hk
        congr 3
        omega
      rw [hrefl]
      refine Finset.prod_congr rfl fun k hk => ?_
      have hkN : k < N := Finset.mem_range.mp hk
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_mul,
        Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, map_add, map_one, map_pow]
      have hpow1 : (ι X) ^ (N - k) * ((ι X) ^ k * ((ι X)⁻¹) ^ N) = 1 := by
        rw [← mul_assoc, ← pow_add, show N - k + k = N by omega, ← mul_pow,
          mul_inv_cancel₀ hxK_ne, one_pow]
      rw [mul_add, mul_one, hpow1, add_comm]
    · rw [map_prod]
      refine Finset.prod_congr rfl fun t _ => ?_
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_mul,
        Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, map_add, map_one, map_pow]
      congr 1
      rw [pow_add, mul_comm ((ι X) ^ N), mul_assoc, ← mul_pow, mul_inv_cancel₀ hxK_ne, one_pow,
        mul_one]
  have hrhs_eval :
      (ι X) ^ (N * (N + 1) / 2) *
        Polynomial.eval₂ ι ((ι X)⁻¹ ^ N)
          (∑ r ∈ Finset.range (2 * N + 1),
            Polynomial.C (qBinom (2 * N) r * X ^ (r * (r - 1) / 2)) * Polynomial.X ^ r) =
      ι (∑ r ∈ Finset.range (2 * N + 1), qBinom (2 * N) r * X ^ (triDist N r)) := by
    rw [Polynomial.eval₂_finsetSum, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
      map_mul, map_pow]
    have hpow : (ι X) ^ (N * (N + 1) / 2) * ((ι X) ^ (r * (r - 1) / 2) * ((ι X)⁻¹ ^ N) ^ r) =
        (ι X) ^ (triDist N r) := by
      rw [← mul_assoc, ← pow_add, add_comm (N * (N + 1) / 2), triDist_identity N r,
        pow_add, ← pow_mul, mul_comm ((ι X) ^ (N * r)), mul_assoc, ← mul_pow,
        mul_inv_cancel₀ hxK_ne, one_pow, mul_one]
    calc (ι X) ^ (N * (N + 1) / 2) * (ι (qBinom (2 * N) r) * (ι X) ^ (r * (r - 1) / 2) *
          ((ι X)⁻¹ ^ N) ^ r)
        = ι (qBinom (2 * N) r) *
          ((ι X) ^ (N * (N + 1) / 2) * ((ι X) ^ (r * (r - 1) / 2) * ((ι X)⁻¹ ^ N) ^ r)) := by
          ring
      _ = ι (qBinom (2 * N) r) * (ι X) ^ (triDist N r) := by rw [hpow]
  rw [← hlhs_eval, ← hrhs_eval]
  exact hmul

private lemma modEq_qFact_of_le {D M : ℕ} (hDM : D ≤ M) :
    ModEq D (qFact M) (qFact D) := by
  unfold qFact
  have hsplit : M = D + (M - D) := by omega
  conv_lhs => rw [hsplit, Finset.prod_range_add]
  have htail : ModEq D (∏ x ∈ Finset.range (M - D), (1 - X ^ (D + x + 1) : ℚ⟦X⟧)) 1 := by
    have := ModEq.finset_prod (Finset.range (M - D)) D
      (fun x => (1 - X ^ (D + x + 1) : ℚ⟦X⟧)) (fun _ => 1)
      (fun x _ => modEq_one_sub_X_pow (by omega))
    simpa using this
  simpa [qFact] using ModEq.mul (ModEq.refl D (qFact D)) htail

private lemma modEq_plusProd_of_le {D M : ℕ} (hDM : D ≤ M) :
    ModEq D (∏ j ∈ Finset.range M, (1 + X ^ (j + 1) : ℚ⟦X⟧))
      (∏ j ∈ Finset.range D, (1 + X ^ (j + 1) : ℚ⟦X⟧)) := by
  have hsplit : M = D + (M - D) := by omega
  conv_lhs => rw [hsplit, Finset.prod_range_add]
  have htail : ModEq D (∏ x ∈ Finset.range (M - D), (1 + X ^ (D + x + 1) : ℚ⟦X⟧)) 1 := by
    have := ModEq.finset_prod (Finset.range (M - D)) D
      (fun x => (1 + X ^ (D + x + 1) : ℚ⟦X⟧)) (fun _ => 1)
      (fun x _ => modEq_one_add_X_pow (by omega))
    simpa using this
  simpa using ModEq.mul (ModEq.refl D _) htail

private lemma qFact_two_mul (m : ℕ) :
    qFact (2 * m) =
      (∏ j ∈ Finset.range m, (1 - X ^ (2 * (j + 1)) : ℚ⟦X⟧)) *
      (∏ j ∈ Finset.range m, (1 - X ^ (2 * j + 1) : ℚ⟦X⟧)) := by
  induction m with
  | zero => simp [qFact]
  | succ m ih =>
    have h2 : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
    rw [h2, qFact_succ, qFact_succ, ih, Finset.prod_range_succ, Finset.prod_range_succ]
    have e1 : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
    rw [e1]
    ring

private lemma tri_strictMono : StrictMono (fun n : ℕ => n * (n + 1) / 2) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
  rw [h]
  omega

private lemma tri_ge_self (n : ℕ) : n ≤ n * (n + 1) / 2 := by
  cases n with
  | zero => simp
  | succ k =>
    have : 2 * (k + 1) ≤ (k + 1) * (k + 1 + 1) := by nlinarith
    omega

private lemma sum_triDist_eq (m i : ℕ) (hi : i ≤ 2 * m) :
    (∑ r ∈ Finset.range (2 * (4 * m + 2) + 1),
      if triDist (4 * m + 2) r = i then (1 : ℚ) else 0) =
    if ∃ n : ℕ, n * (n + 1) / 2 = i then 2 else 0 := by
  set N := 4 * m + 2
  have hsplit : Finset.range (2 * N + 1) =
      Finset.range (N + 1) ∪ (Finset.range N).image (fun n => N + 1 + n) := by
    ext r
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_image]
    constructor
    · intro hr
      by_cases h : r < N + 1
      · exact Or.inl h
      · exact Or.inr ⟨r - N - 1, by omega, by omega⟩
    · rintro (h | ⟨n, hn, rfl⟩) <;> omega
  have hdisj : Disjoint (Finset.range (N + 1)) ((Finset.range N).image (fun n => N + 1 + n)) := by
    rw [Finset.disjoint_left]
    intro r hr1 hr2
    rw [Finset.mem_range] at hr1
    rcases Finset.mem_image.mp hr2 with ⟨n, _, rfl⟩
    omega
  rw [hsplit, Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ hab => by omega)]
  have h1 : (∑ r ∈ Finset.range (N + 1), if triDist N r = i then (1 : ℚ) else 0) =
      ∑ n ∈ Finset.range (N + 1), if n * (n + 1) / 2 = i then (1 : ℚ) else 0 := by
    rw [← Finset.sum_range_reflect (fun n => if n * (n + 1) / 2 = i then (1 : ℚ) else 0) (N + 1)]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrN : r ≤ N := by rw [Finset.mem_range] at hr; omega
    simp [triDist, hrN]
  have h2 : (∑ n ∈ Finset.range N, if triDist N (N + 1 + n) = i then (1 : ℚ) else 0) =
      ∑ n ∈ Finset.range N, if n * (n + 1) / 2 = i then (1 : ℚ) else 0 := by
    refine Finset.sum_congr rfl fun n _ => ?_
    have hnot : ¬ (N + 1 + n ≤ N) := by omega
    have hs2 : N + 1 + n - N = n + 1 := by omega
    simp [triDist, hnot, hs2]
  rw [h1, h2]
  have hcount : ∀ K : ℕ, 2 * m < K →
      (∑ n ∈ Finset.range K, if n * (n + 1) / 2 = i then (1 : ℚ) else 0) =
        if ∃ n : ℕ, n * (n + 1) / 2 = i then 1 else 0 := by
    intro K hK
    by_cases hex : ∃ n : ℕ, n * (n + 1) / 2 = i
    · rw [if_pos hex]
      rcases hex with ⟨n₀, hn₀⟩
      have hn₀K : n₀ ∈ Finset.range K := by
        rw [Finset.mem_range]
        have := tri_ge_self n₀
        omega
      rw [Finset.sum_eq_single n₀]
      · simp [hn₀]
      · intro n _ hne
        rw [if_neg]
        intro hEq
        exact hne (tri_strictMono.injective (hEq.trans hn₀.symm))
      · intro hnot; exact (hnot hn₀K).elim
    · rw [if_neg hex]
      refine Finset.sum_eq_zero fun n _ => ?_
      rw [if_neg]
      intro hEq
      exact hex ⟨n, hEq⟩
  rw [hcount (N + 1) (by omega), hcount N (by omega)]
  split_ifs <;> norm_num

end OeisA039825H2

theorem OMA.solution : OMA.R_oeis_a039825_R1.H2 := by
  classical
  intro m i hi
  dsimp only
  open PowerSeries OeisA039825H2 in
  set P : ℚ⟦X⟧ := ∏ j ∈ Finset.range m, (1 - X ^ (2 * (j + 1)))
  set Q : ℚ⟦X⟧ := ∏ j ∈ Finset.range m, (1 - X ^ (2 * j + 1))
  set D : ℕ := 2 * m
  set N : ℕ := 4 * m + 2
  set E : ℚ⟦X⟧ := ∏ j ∈ Finset.range D, (1 + X ^ (j + 1))
  have hP0 : PowerSeries.constantCoeff P = 1 := by
    rw [map_prod]
    refine Finset.prod_eq_one fun j _ => ?_
    simp [map_sub, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega : 2 * (j + 1) ≠ 0)]
  have hQ0 : PowerSeries.constantCoeff Q = 1 := by
    rw [map_prod]
    refine Finset.prod_eq_one fun j _ => ?_
    simp [map_sub, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega : 2 * j + 1 ≠ 0)]
  have hPinv : P * P⁻¹ = 1 := PowerSeries.mul_inv_cancel P (by rw [hP0]; norm_num)
  have hQinv : Q * Q⁻¹ = 1 := PowerSeries.mul_inv_cancel Q (by rw [hQ0]; norm_num)
  have hqFact_eq : OeisA039825H2.qFact D = P * Q := OeisA039825H2.qFact_two_mul m
  have hEqF_eq : E * OeisA039825H2.qFact D =
      ∏ j ∈ Finset.range D, (1 - X ^ (2 * (j + 1)) : ℚ⟦X⟧) := by
    unfold E OeisA039825H2.qFact
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [show 2 * (j + 1) = (j + 1) + (j + 1) by omega, pow_add]
    ring
  have hEqF_mod : OeisA039825H2.ModEq D (E * OeisA039825H2.qFact D) P := by
    rw [hEqF_eq]
    have hsplit : D = m + m := by omega
    conv_lhs => rw [hsplit, Finset.prod_range_add]
    have htail : OeisA039825H2.ModEq D
        (∏ x ∈ Finset.range m, (1 - X ^ (2 * (m + x + 1)) : ℚ⟦X⟧)) 1 := by
      have := OeisA039825H2.ModEq.finset_prod (Finset.range m) D
        (fun x => (1 - X ^ (2 * (m + x + 1)) : ℚ⟦X⟧)) (fun _ => 1)
        (fun x _ => OeisA039825H2.modEq_one_sub_X_pow (by omega))
      simpa using this
    simpa [P] using OeisA039825H2.ModEq.mul (OeisA039825H2.ModEq.refl D P) htail
  have hE_mod : OeisA039825H2.ModEq D E Q⁻¹ := by
    have hmul := OeisA039825H2.ModEq.mul hEqF_mod (OeisA039825H2.ModEq.refl D (P⁻¹ * Q⁻¹))
    have hL : E * OeisA039825H2.qFact D * (P⁻¹ * Q⁻¹) = E := by
      rw [hqFact_eq]
      calc E * (P * Q) * (P⁻¹ * Q⁻¹) = E * (P * P⁻¹) * (Q * Q⁻¹) := by ring
        _ = E := by rw [hPinv, hQinv, mul_one, mul_one]
    have hR : P * (P⁻¹ * Q⁻¹) = Q⁻¹ := by rw [← mul_assoc, hPinv, one_mul]
    rw [hL, hR] at hmul
    exact hmul
  have hLHS_mod : OeisA039825H2.ModEq D
      (((∏ j ∈ Finset.range N, (1 + X ^ (j + 1) : ℚ⟦X⟧)) *
        (∏ t ∈ Finset.range N, (1 + X ^ t : ℚ⟦X⟧))) * OeisA039825H2.qFact D)
      ((2 : ℚ⟦X⟧) * (P * Q⁻¹)) := by
    have hprod1 : OeisA039825H2.ModEq D
        (∏ j ∈ Finset.range N, (1 + X ^ (j + 1) : ℚ⟦X⟧)) E :=
      OeisA039825H2.modEq_plusProd_of_le (by omega)
    have hprod2_eq : (∏ t ∈ Finset.range N, (1 + X ^ t : ℚ⟦X⟧)) =
        (2 : ℚ⟦X⟧) * ∏ j ∈ Finset.range (N - 1), (1 + X ^ (j + 1) : ℚ⟦X⟧) := by
      have hN1 : N = (N - 1) + 1 := by omega
      conv_lhs => rw [hN1, Finset.prod_range_succ']
      rw [pow_zero]
      have h2 : (1 : ℚ⟦X⟧) + 1 = 2 := by ring
      rw [h2, mul_comm]
    have hprod2 : OeisA039825H2.ModEq D
        (∏ t ∈ Finset.range N, (1 + X ^ t : ℚ⟦X⟧)) ((2 : ℚ⟦X⟧) * E) := by
      rw [hprod2_eq]
      exact OeisA039825H2.ModEq.mul (OeisA039825H2.ModEq.refl D 2)
        (OeisA039825H2.modEq_plusProd_of_le (by omega))
    have hstep1 := OeisA039825H2.ModEq.mul
      (OeisA039825H2.ModEq.mul hprod1 hprod2)
      (OeisA039825H2.ModEq.refl D (OeisA039825H2.qFact D))
    have hstep2 : OeisA039825H2.ModEq D
        (E * ((2 : ℚ⟦X⟧) * E) * OeisA039825H2.qFact D)
        ((2 : ℚ⟦X⟧) * (P * Q⁻¹)) := by
      have hre : E * ((2 : ℚ⟦X⟧) * E) * OeisA039825H2.qFact D =
          (2 : ℚ⟦X⟧) * ((E * OeisA039825H2.qFact D) * E) := by ring
      rw [hre]
      exact OeisA039825H2.ModEq.mul (OeisA039825H2.ModEq.refl D 2)
        (OeisA039825H2.ModEq.mul hEqF_mod hE_mod)
    exact hstep1.trans hstep2
  have hRHS_mod : OeisA039825H2.ModEq D
      ((∑ r ∈ Finset.range (2 * N + 1),
          OeisA039825H2.qBinom (2 * N) r * X ^ (OeisA039825H2.triDist N r)) *
        OeisA039825H2.qFact D)
      (∑ r ∈ Finset.range (2 * N + 1), (X ^ (OeisA039825H2.triDist N r) : ℚ⟦X⟧)) := by
    rw [Finset.sum_mul]
    refine OeisA039825H2.ModEq.finset_sum _ D _ _ fun r hr => ?_
    by_cases hle : OeisA039825H2.triDist N r ≤ D
    · have hrD : D ≤ r ∧ D ≤ 2 * N - r := by
        have htr := hle
        unfold OeisA039825H2.triDist at htr
        split_ifs at htr with h
        · have hge := OeisA039825H2.tri_ge_self (N - r)
          omega
        · have hge := OeisA039825H2.tri_ge_self (r - N - 1)
          rw [show r - N - 1 + 1 = r - N by omega] at hge
          omega
      have hq1 : OeisA039825H2.ModEq D (OeisA039825H2.qFact (2 * N)) (OeisA039825H2.qFact D) :=
        OeisA039825H2.modEq_qFact_of_le (by omega)
      have hq2 : OeisA039825H2.ModEq D (OeisA039825H2.qFact r)⁻¹ (OeisA039825H2.qFact D)⁻¹ :=
        (OeisA039825H2.modEq_qFact_of_le hrD.1).inv (by rw [OeisA039825H2.constantCoeff_qFact]; norm_num)
      have hq3 : OeisA039825H2.ModEq D (OeisA039825H2.qFact (2 * N - r))⁻¹
          (OeisA039825H2.qFact D)⁻¹ :=
        (OeisA039825H2.modEq_qFact_of_le hrD.2).inv (by rw [OeisA039825H2.constantCoeff_qFact]; norm_num)
      have hqb : OeisA039825H2.ModEq D
          (OeisA039825H2.qBinom (2 * N) r * OeisA039825H2.qFact D) 1 := by
        unfold OeisA039825H2.qBinom
        have h1 := OeisA039825H2.ModEq.mul
          (OeisA039825H2.ModEq.mul (OeisA039825H2.ModEq.mul hq1 hq2) hq3)
          (OeisA039825H2.ModEq.refl D (OeisA039825H2.qFact D))
        have hsimp : OeisA039825H2.qFact D * (OeisA039825H2.qFact D)⁻¹ *
            (OeisA039825H2.qFact D)⁻¹ * OeisA039825H2.qFact D = 1 := by
          rw [OeisA039825H2.qFact_mul_inv, one_mul, mul_comm, OeisA039825H2.qFact_mul_inv]
        rw [hsimp] at h1
        exact h1
      have hre : OeisA039825H2.qBinom (2 * N) r * X ^ (OeisA039825H2.triDist N r) *
          OeisA039825H2.qFact D =
          (OeisA039825H2.qBinom (2 * N) r * OeisA039825H2.qFact D) *
            X ^ (OeisA039825H2.triDist N r) := by ring
      rw [hre]
      simpa using OeisA039825H2.ModEq.mul hqb (OeisA039825H2.ModEq.refl D _)
    · push Not at hle
      have h0 : OeisA039825H2.ModEq D (X ^ (OeisA039825H2.triDist N r) : ℚ⟦X⟧) 0 :=
        OeisA039825H2.modEq_X_pow_zero hle
      have hL0 : OeisA039825H2.ModEq D
          (OeisA039825H2.qBinom (2 * N) r * X ^ (OeisA039825H2.triDist N r) *
            OeisA039825H2.qFact D) 0 := by
        have := OeisA039825H2.ModEq.mul
          (OeisA039825H2.ModEq.mul (OeisA039825H2.ModEq.refl D (OeisA039825H2.qBinom (2 * N) r)) h0)
          (OeisA039825H2.ModEq.refl D (OeisA039825H2.qFact D))
        simpa using this
      exact hL0.trans h0.symm
  have hcomb : OeisA039825H2.ModEq D ((2 : ℚ⟦X⟧) * (P * Q⁻¹))
      (∑ r ∈ Finset.range (2 * N + 1), (X ^ (OeisA039825H2.triDist N r) : ℚ⟦X⟧)) := by
    have hjac := congrArg (fun f => f * OeisA039825H2.qFact D) (OeisA039825H2.jacobi_finite N)
    exact (hLHS_mod.symm.trans (by rw [hjac]; exact hRHS_mod))
  have hci := hcomb i hi
  have hL_coeff : PowerSeries.coeff i ((2 : ℚ⟦X⟧) * (P * Q⁻¹)) =
      2 * PowerSeries.coeff i (P * Q⁻¹) := by
    have h2 : (2 : ℚ⟦X⟧) = PowerSeries.C (2 : ℚ) := (map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2).symm
    rw [h2, PowerSeries.coeff_C_mul]
  have hR_coeff : PowerSeries.coeff i
      (∑ r ∈ Finset.range (2 * N + 1), (X ^ (OeisA039825H2.triDist N r) : ℚ⟦X⟧)) =
      if ∃ n : ℕ, n * (n + 1) / 2 = i then (2 : ℚ) else 0 := by
    rw [map_sum]
    have heq : (∑ r ∈ Finset.range (2 * N + 1),
        PowerSeries.coeff i (X ^ (OeisA039825H2.triDist N r) : ℚ⟦X⟧)) =
        ∑ r ∈ Finset.range (2 * N + 1),
          if OeisA039825H2.triDist N r = i then (1 : ℚ) else 0 := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [PowerSeries.coeff_X_pow]
      by_cases h : OeisA039825H2.triDist N r = i
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (Ne.symm h), if_neg h]
    rw [heq]
    exact OeisA039825H2.sum_triDist_eq m i hi
  rw [hL_coeff, hR_coeff] at hci
  split_ifs at hci ⊢ <;> linarith
