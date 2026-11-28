import OMAReductions.R_HardyLittlewood_first_hardy_littlewood_conjecture_R2_H2_R2

/-!
# Reduction R2.H2.R2.H2.R1: Circle Method (Discrete Parseval) for Pairwise Correlations

This reduction splits the higher-order (`|I| ≥ 2`) balanced `W`-tricked correlation
cancellation (`R2.H2.R2.H2`) into:
- `H1`: **Circle Method / Fourier pairwise cancellation** (`|I| = 2`) on each surviving
  residue class `r : ZMod W`, expressed via the discrete exponential sums
  `E_{W, r, c}(N, ξ) = ∑_{1 ≤ n ≤ N, n ≡ r (mod W)} (Λ_W(n + c) - 1) * exp(2πi ξ n / (N + 1))`.
- `H2`: **Higher-order (`|I| ≥ 3`) balanced correlation cancellation** (prime triples and beyond).

Inside this file we prove unconditionally:
1. Exact discrete orthogonality of additive characters on `Finset.range M`.
2. Exact discrete Parseval / Plancherel identity relating `∑_{n ∈ A} f n * g n` to the
   frequency-domain inner product `(1 / (N + 1)) * ∑_{ξ = 0}^{N} f̂(ξ) * conj(ĝ(ξ))`.
3. Averaging over surviving residue classes `r ∈ Surv(W)` to deduce all `|I| = 2` cases
   of `R2.H2.R2.H2` from `H1`.
-/

namespace OMA.R_HardyLittlewood_first_hardy_littlewood_conjecture_R2_H2_R2_H2_R1

open HardyLittlewood Filter Finset ArithmeticFunction Complex
open scoped Topology

/-- Circle Method / discrete Fourier cancellation for pairwise (`|I| = 2`) balanced
`W`-tricked correlations on every surviving residue class `r : ZMod W`. -/
def H1 : Prop :=
  ∀ {k : ℕ} (m : Fin (k + 2) → ℕ), m 0 = 0 → (∀ i ≠ 0, Even (m i)) →
    Function.Injective m →
    (∀ q : {q : ℕ // q.Prime ∧ 3 ≤ q}, ¬ Function.Surjective (fun i => (m i : ZMod q))) →
    ∀ (i₁ i₂ : Fin (k + 2)), i₁ ≠ i₂ →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ s : Finset {q : ℕ // q.Prime ∧ 3 ≤ q} in atTop,
    let W := 2 * ∏ q ∈ s, (q : ℕ)
    ∀ (r : ZMod W), (∀ i, IsUnit (r + (m i : ZMod W))) →
    ∀ᶠ N : ℕ in atTop,
      ‖((W : ℂ) / ((N : ℂ) * ((N + 1 : ℕ) : ℂ))) *
        ∑ ξ ∈ Finset.range (N + 1),
          (∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r),
            (((W.totient : ℝ) / (W : ℝ) * ArithmeticFunction.vonMangoldt (n + m i₁) - 1 : ℝ) : ℂ) *
              Complex.exp (2 * Real.pi * Complex.I * ((ξ : ℂ) * (n : ℂ) / ((N + 1 : ℕ) : ℂ)))) *
          starRingEnd ℂ
            (∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r),
              (((W.totient : ℝ) / (W : ℝ) * ArithmeticFunction.vonMangoldt (n + m i₂) - 1 : ℝ) : ℂ) *
                Complex.exp (2 * Real.pi * Complex.I * ((ξ : ℂ) * (n : ℂ) / ((N + 1 : ℕ) : ℂ))))‖ < ε

/-- Asymptotic cancellation of higher-order (`|I| ≥ 3`) balanced `W`-tricked von Mangoldt
correlations over coprime translates modulo `W = 2 * ∏ q ∈ s, q`. -/
def H2 : Prop :=
  ∀ {k : ℕ} (m : Fin (k + 2) → ℕ), m 0 = 0 → (∀ i ≠ 0, Even (m i)) →
    Function.Injective m →
    (∀ q : {q : ℕ // q.Prime ∧ 3 ≤ q}, ¬ Function.Surjective (fun i => (m i : ZMod q))) →
    ∀ (I : Finset (Fin (k + 2))), 3 ≤ I.card →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ s : Finset {q : ℕ // q.Prime ∧ 3 ≤ q} in atTop,
    let W := 2 * ∏ q ∈ s, (q : ℕ)
    ∀ᶠ N : ℕ in atTop,
      |(W : ℝ) / ((Nat.card {r : ZMod W // ∀ i, IsUnit (r + m i)} : ℝ) * (N : ℝ)) *
        ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ∀ i, Nat.Coprime (n + m i) W),
          ∏ i ∈ I, ((W.totient : ℝ) / (W : ℝ) * ArithmeticFunction.vonMangoldt (n + m i) - 1)| < ε

/- ### Part 1: Exact discrete orthogonality of additive characters and Parseval -/

lemma sum_exp_orthogonality (M a b : ℕ) (ha : a < M) (hb : b < M) :
    ∑ ξ ∈ Finset.range M,
      Complex.exp (2 * Real.pi * Complex.I * ((ξ : ℂ) * ((a : ℂ) - (b : ℂ)) / (M : ℂ))) =
      if a = b then (M : ℂ) else 0 := by
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  by_cases hab : a = b
  · subst hab
    simp [Finset.sum_const]
  · rw [if_neg hab]
    let z : ℂ := Complex.exp (2 * Real.pi * Complex.I * (((a : ℂ) - (b : ℂ)) / (M : ℂ)))
    have hterm : ∀ ξ : ℕ,
        Complex.exp (2 * Real.pi * Complex.I * ((ξ : ℂ) * ((a : ℂ) - (b : ℂ)) / (M : ℂ))) =
          z ^ ξ := by
      intro ξ
      dsimp only [z]
      rw [← Complex.exp_nat_mul]
      congr 1
      ring
    simp_rw [hterm]
    have hz1 : z ≠ 1 := by
      intro hz
      rw [Complex.exp_eq_one_iff] at hz
      obtain ⟨k, hk⟩ := hz
      have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have hratio : ((a : ℂ) - (b : ℂ)) / (M : ℂ) = (k : ℂ) := by
        apply mul_left_cancel₀ h2pi
        calc
          2 * (Real.pi : ℂ) * Complex.I * (((a : ℂ) - (b : ℂ)) / (M : ℂ))
              = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hk
          _ = 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) := mul_comm _ _
      have heq_c : (a : ℂ) - (b : ℂ) = (k : ℂ) * (M : ℂ) := by
        have := congrArg (· * (M : ℂ)) hratio
        simpa [div_mul_cancel₀ _ hM0] using this
      have heq_z : (a : ℤ) - (b : ℤ) = k * (M : ℤ) := by
        have hre := congrArg Complex.re heq_c
        simp only [Complex.sub_re, Complex.natCast_re, Complex.mul_re, Complex.intCast_re,
          Complex.intCast_im, Complex.natCast_im, mul_zero, sub_zero] at hre
        exact_mod_cast hre
      have hlt : |(a : ℤ) - (b : ℤ)| < (M : ℤ) := by
        rw [abs_lt]; constructor <;> omega
      have hge : (M : ℤ) ≤ |k * (M : ℤ)| := by
        have hk0 : k ≠ 0 := by
          intro h0; subst h0; simp at heq_z; omega
        rw [abs_mul, abs_of_pos (by omega : (0 : ℤ) < (M : ℤ))]
        have hk1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
        nlinarith
      rw [heq_z] at hlt
      omega
    rw [geom_sum_eq hz1]
    have hzM : z ^ M = 1 := by
      dsimp only [z]
      rw [← Complex.exp_nat_mul]
      have harg : (M : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (((a : ℂ) - (b : ℂ)) / (M : ℂ))) =
          (((a : ℤ) - (b : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast
        field_simp [hM0]
      rw [harg]
      exact Complex.exp_int_mul_two_pi_mul_I ((a : ℤ) - (b : ℤ))
    rw [hzM, sub_self, zero_div]

lemma discrete_parseval (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Ioc 0 N) (f g : ℕ → ℝ) :
    ((∑ n ∈ A, f n * g n : ℝ) : ℂ) =
      (1 / ((N + 1 : ℕ) : ℂ)) *
        ∑ ξ ∈ Finset.range (N + 1),
          (∑ n ∈ A, (f n : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * ((ξ : ℂ) * (n : ℂ) / ((N + 1 : ℕ) : ℂ)))) *
          starRingEnd ℂ
            (∑ n ∈ A, (g n : ℂ) *
              Complex.exp (2 * Real.pi * Complex.I * ((ξ : ℂ) * (n : ℂ) / ((N + 1 : ℕ) : ℂ)))) := by
  have hM0 : ((N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  have hconj : ∀ ξ : ℕ,
      starRingEnd ℂ
        (∑ n ∈ A, (g n : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((ξ : ℂ) * (n : ℂ) / ((N + 1 : ℕ) : ℂ)))) =
      ∑ n ∈ A, (g n : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((ξ : ℂ) * (n : ℂ) / ((N + 1 : ℕ) : ℂ)))) := by
    intro ξ
    rw [map_sum]
    apply sum_congr rfl; intro n _
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp [Complex.conj_I, map_ofNat]
  simp_rw [hconj]
  have hexp : ∀ ξ : ℕ,
      (∑ a ∈ A, (f a : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((ξ : ℂ) * (a : ℂ) / ((N + 1 : ℕ) : ℂ)))) *
      (∑ b ∈ A, (g b : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((ξ : ℂ) * (b : ℂ) / ((N + 1 : ℕ) : ℂ))))) =
      ∑ a ∈ A, ∑ b ∈ A, (f a : ℂ) * (g b : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((ξ : ℂ) * ((a : ℂ) - (b : ℂ)) / ((N + 1 : ℕ) : ℂ))) := by
    intro ξ
    rw [Finset.sum_mul]
    apply sum_congr rfl; intro a _
    rw [Finset.mul_sum]
    apply sum_congr rfl; intro b _
    have hmul :
        Complex.exp (2 * Real.pi * Complex.I * ((ξ : ℂ) * (a : ℂ) / ((N + 1 : ℕ) : ℂ))) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((ξ : ℂ) * (b : ℂ) / ((N + 1 : ℕ) : ℂ)))) =
        Complex.exp (2 * Real.pi * Complex.I * ((ξ : ℂ) * ((a : ℂ) - (b : ℂ)) / ((N + 1 : ℕ) : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [mul_mul_mul_comm, hmul]
  simp_rw [hexp]
  rw [Finset.sum_comm]
  have hswap : ∑ a ∈ A, ∑ ξ ∈ Finset.range (N + 1), ∑ b ∈ A,
        (f a : ℂ) * (g b : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((ξ : ℂ) * ((a : ℂ) - (b : ℂ)) / ((N + 1 : ℕ) : ℂ))) =
      ∑ a ∈ A, ∑ b ∈ A, (f a : ℂ) * (g b : ℂ) *
        ∑ ξ ∈ Finset.range (N + 1),
          Complex.exp (2 * Real.pi * Complex.I * ((ξ : ℂ) * ((a : ℂ) - (b : ℂ)) / ((N + 1 : ℕ) : ℂ))) := by
    apply sum_congr rfl; intro a _
    rw [Finset.sum_comm]
    apply sum_congr rfl; intro b _
    rw [← Finset.mul_sum]
  rw [hswap]
  have horth : ∑ a ∈ A, ∑ b ∈ A, (f a : ℂ) * (g b : ℂ) *
        ∑ ξ ∈ Finset.range (N + 1),
          Complex.exp (2 * Real.pi * Complex.I * ((ξ : ℂ) * ((a : ℂ) - (b : ℂ)) / ((N + 1 : ℕ) : ℂ))) =
      ((N + 1 : ℕ) : ℂ) * ∑ a ∈ A, (f a : ℂ) * (g a : ℂ) := by
    rw [Finset.mul_sum]
    apply sum_congr rfl; intro a ha
    have haN : a < N + 1 := Nat.lt_succ_of_le (mem_Ioc.mp (hA ha)).2
    have hinner : ∑ b ∈ A, (f a : ℂ) * (g b : ℂ) *
          ∑ ξ ∈ Finset.range (N + 1),
            Complex.exp (2 * Real.pi * Complex.I * ((ξ : ℂ) * ((a : ℂ) - (b : ℂ)) / ((N + 1 : ℕ) : ℂ))) =
        ∑ b ∈ A, if b = a then ((N + 1 : ℕ) : ℂ) * ((f a : ℂ) * (g a : ℂ)) else 0 := by
      apply sum_congr rfl; intro b hb
      have hbN : b < N + 1 := Nat.lt_succ_of_le (mem_Ioc.mp (hA hb)).2
      rw [sum_exp_orthogonality (N + 1) a b haN hbN]
      by_cases hba : b = a
      · subst hba; simp [mul_comm]
      · have hab : a ≠ b := Ne.symm hba
        simp [hab, hba]
    rw [hinner, Finset.sum_ite_eq' A a, if_pos ha]
  rw [horth, ← mul_assoc, one_div_mul_cancel hM0, one_mul]
  push_cast
  rfl

/- ### Part 2: Main reduction theorem -/

theorem main : H1 → H2 → OMA.R_HardyLittlewood_first_hardy_littlewood_conjecture_R2_H2_R2.H2 := by
  intro hH1 hH2 k m hzero heven hinj hlocal I hI2 ε hε
  classical
  by_cases hI3 : 3 ≤ I.card
  · exact hH2 m hzero heven hinj hlocal I hI3 ε hε
  · have hIeq : I.card = 2 := by omega
    obtain ⟨i₁, i₂, hne, rfl⟩ := Finset.card_eq_two.mp hIeq
    have h1 := hH1 m hzero heven hinj hlocal i₁ i₂ hne ε hε
    filter_upwards [h1] with s hs
    intro W
    have hWpos : 0 < W := OMA.R_HardyLittlewood_first_hardy_littlewood_conjecture_R2_H2_R2.wheel_pos s
    have : NeZero W := ⟨hWpos.ne'⟩
    let S := (Finset.univ : Finset (ZMod W)).filter (fun r => ∀ i, IsUnit (r + (m i : ZMod W)))
    have hScard : S.card = Nat.card {r : ZMod W // ∀ i, IsUnit (r + (m i : ZMod W))} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hSurv_pos_nat : 0 < Nat.card {r : ZMod W // ∀ i, IsUnit (r + (m i : ZMod W))} := by
      rw [OMA.R_HardyLittlewood_first_hardy_littlewood_conjecture_R2_H2_R2.surviving_card_wheel
        m hzero heven s]
      exact Finset.prod_pos fun q _ => by
        have : NeZero (q : ℕ) := ⟨q.2.1.ne_zero⟩
        have hlt : Nat.numResidues q m < q := by
          unfold Nat.numResidues
          calc
            _ < Nat.card (ZMod (q : ℕ)) :=
              Set.ncard_lt_card (fun h => hlocal q (Set.range_eq_univ.mp h))
            _ = (q : ℕ) := Nat.card_zmod _
        omega
    have hSpos : (0 : ℝ) < (S.card : ℝ) := by rw [hScard]; exact_mod_cast hSurv_pos_nat
    have hall : ∀ᶠ N : ℕ in atTop, ∀ r ∈ S,
        ‖((W : ℂ) / ((N : ℂ) * ((N + 1 : ℕ) : ℂ))) *
          ∑ ξ ∈ Finset.range (N + 1),
            (∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r),
              (((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i₁) - 1 : ℝ) : ℂ) *
                Complex.exp (2 * Real.pi * Complex.I * ((ξ : ℂ) * (n : ℂ) / ((N + 1 : ℕ) : ℂ)))) *
            starRingEnd ℂ
              (∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r),
                (((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i₂) - 1 : ℝ) : ℂ) *
                  Complex.exp (2 * Real.pi * Complex.I * ((ξ : ℂ) * (n : ℂ) / ((N + 1 : ℕ) : ℂ))))‖ < ε := by
      rw [Filter.eventually_all_finset]
      intro r hr
      exact hs r (mem_filter.mp hr).2
    filter_upwards [eventually_gt_atTop 0, hall] with N hN0 hNall
    have hdisj : Set.PairwiseDisjoint (S : Set (ZMod W))
        (fun r => (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r)) := by
      intro r1 _ r2 _ hrne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro n hn1 hn2
      exact hrne ((mem_filter.mp hn1).2.symm.trans (mem_filter.mp hn2).2)
    have hper : ∀ r ∈ S,
        |(W : ℝ) / (N : ℝ) *
          ∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r),
            ((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i₁) - 1) *
            ((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i₂) - 1)| < ε := by
      intro r hr
      have hpars := discrete_parseval N
        ((Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r))
        (Finset.filter_subset _ _)
        (fun n => (W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i₁) - 1)
        (fun n => (W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i₂) - 1)
      have hscale :
          (((W : ℝ) / (N : ℝ) *
            ∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r),
              ((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i₁) - 1) *
              ((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i₂) - 1) : ℝ) : ℂ) =
          ((W : ℂ) / ((N : ℂ) * ((N + 1 : ℕ) : ℂ))) *
            ∑ ξ ∈ Finset.range (N + 1),
              (∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r),
                (((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i₁) - 1 : ℝ) : ℂ) *
                  Complex.exp (2 * Real.pi * Complex.I * ((ξ : ℂ) * (n : ℂ) / ((N + 1 : ℕ) : ℂ)))) *
              starRingEnd ℂ
                (∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r),
                  (((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i₂) - 1 : ℝ) : ℂ) *
                    Complex.exp (2 * Real.pi * Complex.I * ((ξ : ℂ) * (n : ℂ) / ((N + 1 : ℕ) : ℂ)))) := by
        rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast,
          hpars]
        ring
      rw [← Real.norm_eq_abs, ← Complex.norm_real, hscale]
      exact hNall r hr
    have hsplit_eq :
        (W : ℝ) / ((Nat.card {r : ZMod W // ∀ i, IsUnit (r + m i)} : ℝ) * (N : ℝ)) *
          ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ∀ i, Nat.Coprime (n + m i) W),
            ∏ i ∈ ({i₁, i₂} : Finset (Fin (k + 2))),
              ((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i) - 1) =
        (1 / (S.card : ℝ)) * ∑ r ∈ S,
          ((W : ℝ) / (N : ℝ) *
            ∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r),
              ((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i₁) - 1) *
              ((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i₂) - 1)) := by
      rw [OMA.R_HardyLittlewood_first_hardy_littlewood_conjecture_R2_H2_R2.filter_coprime_eq_biUnion
        m W hWpos N, Finset.sum_biUnion hdisj, ← hScard, ← Finset.mul_sum]
      have hpair : ∀ r ∈ S,
          ∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r),
            ∏ i ∈ ({i₁, i₂} : Finset (Fin (k + 2))),
              ((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i) - 1) =
          ∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r),
            ((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i₁) - 1) *
            ((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i₂) - 1) := by
        intro r _
        apply sum_congr rfl; intro n _
        exact Finset.prod_pair hne
      rw [Finset.sum_congr rfl hpair]
      ring
    rw [hsplit_eq, abs_mul, abs_of_pos (one_div_pos.mpr hSpos)]
    have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hScard]; exact hSurv_pos_nat)
    calc
      (1 / (S.card : ℝ)) * |∑ r ∈ S, _|
          ≤ (1 / (S.card : ℝ)) * ∑ r ∈ S,
              |(W : ℝ) / (N : ℝ) *
                ∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r),
                  ((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i₁) - 1) *
                  ((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i₂) - 1)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ < (1 / (S.card : ℝ)) * ∑ _r ∈ S, ε :=
        mul_lt_mul_of_pos_left (Finset.sum_lt_sum_of_nonempty hSne hper) (one_div_pos.mpr hSpos)
      _ = ε := by
        rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, one_div_mul_cancel hSpos.ne', one_mul]

end OMA.R_HardyLittlewood_first_hardy_littlewood_conjecture_R2_H2_R2_H2_R1
