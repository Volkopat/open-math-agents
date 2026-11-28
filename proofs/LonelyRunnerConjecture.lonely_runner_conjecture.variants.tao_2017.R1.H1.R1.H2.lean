import OMAReductions.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1_H1_R1

/-!
# Arithmetic matching in rational boxes (Hu-Jing, Lemma 5.1)

Proves `OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1_H1_R1.H2`:
given a box `[1, A] × [1, B]` of area `A * B ≤ C * |U|` containing rational representations
`v i = ξ * a_i / b_i` of `|U| ≥ 2` distinct positive integer speeds, there exists a matching of
at least `η(C) * |U|` disjoint pairs in `U` whose pairwise reduced ratio height
`max (v i) (v j) / gcd (v i) (v j)` is at most `D(C)`.

Following Hu and Jing (arXiv:2610.23790, Lemma 5.1), we pick a finite set `P` of primes with
`∏ p ∈ P, (1 - 1 / p) ≤ 1 / (8 * C)`, split each coordinate into its `P`-smooth and `P`-rough
parts, discard speeds with `P`-smooth part above a cutoff `S(C)`, bound the distinct `P`-rough
pairs by periodicity modulo `∏ p ∈ P, p`, and extract a maximal matching.
-/

-- Step LonelyRunnerConjecture.lonely_runner_conjecture.variants.tao_2017.R1.H1.R1.H2: hypothesis H2 of reduction LonelyRunnerConjecture.lonely_runner_conjecture.variants.tao_2017.R1.H1.R1
-- Credit: @yhay81

namespace OMA.LonelyRunnerH2

open Finset
open scoped Classical

/- Section 1: Finite Euler product and smooth/rough decomposition -/

private def IsPSmooth (P : Finset ℕ) (n : ℕ) : Prop :=
  0 < n ∧ ∀ p, p.Prime → p ∣ n → p ∈ P

private def smoothPart (P : Finset ℕ) (n : ℕ) : ℕ :=
  ∏ p ∈ P, p ^ n.factorization p

private def roughPart (P : Finset ℕ) (n : ℕ) : ℕ :=
  n / smoothPart P n

private lemma smoothPart_pos {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    0 < smoothPart P n :=
  Finset.prod_pos fun p hp => pow_pos (hP p hp).pos _

private lemma smoothPart_dvd {P : Finset ℕ} (_hP : ∀ p ∈ P, p.Prime) {n : ℕ} (hn : 0 < n) :
    smoothPart P n ∣ n := by
  have hfac : n.factorization.prod (· ^ ·) = n := Nat.prod_factorization_pow_eq_self hn.ne'
  have hsub : ∏ p ∈ P, p ^ n.factorization p =
      ∏ p ∈ P ∩ n.factorization.support, p ^ n.factorization p := by
    symm
    apply Finset.prod_subset Finset.inter_subset_left
    intro p hpP hp
    have hnot : p ∉ n.factorization.support := fun h => hp (Finset.mem_inter.mpr ⟨hpP, h⟩)
    rw [Finsupp.notMem_support_iff.mp hnot, pow_zero]
  unfold smoothPart
  rw [hsub]
  conv_rhs => rw [← hfac]
  unfold Finsupp.prod
  exact Finset.prod_dvd_prod_of_subset _ _ _ Finset.inter_subset_right

private lemma smoothPart_mul_roughPart {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {n : ℕ}
    (hn : 0 < n) : smoothPart P n * roughPart P n = n :=
  Nat.mul_div_cancel' (smoothPart_dvd hP hn)

private lemma roughPart_pos {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {n : ℕ} (hn : 0 < n) :
    0 < roughPart P n := by
  have hmul := smoothPart_mul_roughPart hP hn
  by_contra h
  have h0 : roughPart P n = 0 := by omega
  rw [h0, mul_zero] at hmul
  omega

private lemma roughPart_le {P : Finset ℕ} (n : ℕ) : roughPart P n ≤ n :=
  Nat.div_le_self n _

private lemma isPSmooth_smoothPart {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    IsPSmooth P (smoothPart P n) := by
  refine ⟨smoothPart_pos hP n, fun q hq hqdvd => ?_⟩
  obtain ⟨p, hp, hqp⟩ := (hq.prime.dvd_finsetProd_iff _).mp hqdvd
  have hqp' : q ∣ p := hq.dvd_of_dvd_pow hqp
  have heq : q = p := (Nat.prime_dvd_prime_iff_eq hq (hP p hp)).mp hqp'
  rwa [heq]

private lemma not_dvd_roughPart {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {n : ℕ} (hn : 0 < n)
    {p : ℕ} (hp : p ∈ P) : ¬ p ∣ roughPart P n := by
  intro hdvd
  have hp_prime : p.Prime := hP p hp
  have hs_pos : 0 < smoothPart P n := smoothPart_pos hP n
  have hr_pos : 0 < roughPart P n := roughPart_pos hP hn
  have hmul : smoothPart P n * roughPart P n = n := smoothPart_mul_roughPart hP hn
  have hfac_mul : n.factorization p =
      (smoothPart P n).factorization p + (roughPart P n).factorization p := by
    conv_lhs => rw [← hmul]
    rw [Nat.factorization_mul hs_pos.ne' hr_pos.ne', Finsupp.add_apply]
  have hge : n.factorization p ≤ (smoothPart P n).factorization p := by
    have hpow : p ^ n.factorization p ∣ smoothPart P n := Finset.dvd_prod_of_mem _ hp
    exact (hp_prime.pow_dvd_iff_le_factorization hs_pos.ne').mp hpow
  have hr1 : 1 ≤ (roughPart P n).factorization p := by
    have : p ^ 1 ∣ roughPart P n := by simpa using hdvd
    exact (hp_prime.pow_dvd_iff_le_factorization hr_pos.ne').mp this
  omega

private lemma smoothPart_eq_self_of_isPSmooth {P : Finset ℕ} {n : ℕ} (hs : IsPSmooth P n) :
    smoothPart P n = n := by
  have hfac : n.factorization.prod (· ^ ·) = n := Nat.prod_factorization_pow_eq_self hs.1.ne'
  conv_rhs => rw [← hfac]
  unfold smoothPart Finsupp.prod
  symm
  apply Finset.prod_subset
  · intro p hp
    have hmem := Nat.support_factorization n
    rw [hmem, Nat.mem_primeFactors] at hp
    exact hs.2 p hp.1 hp.2.1
  · intro p _ hp
    simp [Finsupp.notMem_support_iff.mp hp]

private lemma factorization_le_self {n p : ℕ} (hn : 0 < n) (hp : p.Prime) :
    n.factorization p ≤ n := by
  have h1 : n.factorization p < 2 ^ n.factorization p := Nat.lt_two_pow_self
  have h2 : 2 ^ n.factorization p ≤ p ^ n.factorization p :=
    Nat.pow_le_pow_left hp.two_le _
  have h3 : p ^ n.factorization p ≤ n :=
    Nat.le_of_dvd hn (Nat.ordProj_dvd n p)
  omega

private lemma geom_sum_le_inv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    ∑ k ∈ range (M + 1), r ^ k ≤ (1 - r)⁻¹ := by
  have hne : r ≠ 1 := ne_of_lt hr1
  have hpos : 0 < 1 - r := sub_pos.mpr hr1
  rw [geom_sum_eq hne]
  have h1 : (r ^ (M + 1) - 1) / (r - 1) = (1 - r ^ (M + 1)) / (1 - r) := by
    have : r - 1 = -(1 - r) := by ring
    rw [this, div_neg]
    ring
  rw [h1, inv_eq_one_div]
  apply div_le_div_of_nonneg_right _ hpos.le
  linarith [pow_nonneg hr0 (M + 1)]

private lemma finite_euler_product {P : Finset ℕ} (_hP : ∀ p ∈ P, p.Prime)
    (w : ℕ → ℝ) (hw0 : ∀ p ∈ P, 0 ≤ w p) (hw1 : ∀ p ∈ P, w p < 1)
    (F : Finset ℕ) (M : ℕ)
    (hF : ∀ n ∈ F, IsPSmooth P n ∧ ∀ p ∈ P, n.factorization p ≤ M) :
    (∑ n ∈ F, ∏ p ∈ P, (w p) ^ n.factorization p) ≤ ∏ p ∈ P, (1 - w p)⁻¹ := by
  classical
  let g : P → Fin (M + 1) → ℝ := fun p k => (w p.1) ^ k.val
  let φ : ℕ → (P → Fin (M + 1)) := fun n p =>
    if h : n.factorization p.1 ≤ M then ⟨n.factorization p.1, Nat.lt_succ_of_le h⟩ else ⟨0, Nat.succ_pos M⟩
  have hinj : Set.InjOn φ (F : Set ℕ) := by
    intro a ha b hb hab
    have ha' := hF a ha
    have hb' := hF b hb
    rw [← smoothPart_eq_self_of_isPSmooth ha'.1, ← smoothPart_eq_self_of_isPSmooth hb'.1]
    unfold smoothPart
    apply Finset.prod_congr rfl
    intro p hp
    have hval := congrArg (fun f => (f ⟨p, hp⟩).val) hab
    simp only [φ, dif_pos (ha'.2 p hp), dif_pos (hb'.2 p hp)] at hval
    rw [hval]
  have hval_eq : ∀ n ∈ F, (∏ p ∈ P, (w p) ^ n.factorization p) =
      ∏ p : P, g p (φ n p) := by
    intro n hn
    rw [← Finset.prod_coe_sort P (fun p => (w p) ^ n.factorization p)]
    apply Finset.prod_congr rfl
    intro p _
    simp only [g, φ, dif_pos ((hF n hn).2 p.1 p.2)]
  have hstep1 : (∑ n ∈ F, ∏ p ∈ P, (w p) ^ n.factorization p) ≤
      ∑ e : P → Fin (M + 1), ∏ p : P, g p (e p) := by
    calc
      (∑ n ∈ F, ∏ p ∈ P, (w p) ^ n.factorization p)
          = ∑ n ∈ F, ∏ p : P, g p (φ n p) := Finset.sum_congr rfl hval_eq
      _ = ∑ e ∈ F.image φ, ∏ p : P, g p (e p) :=
        (Finset.sum_image (f := fun e : P → Fin (M + 1) => ∏ p : P, g p (e p))
          (fun a ha b hb h => hinj ha hb h)).symm
      _ ≤ ∑ e : P → Fin (M + 1), ∏ p : P, g p (e p) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro e _ _
        exact Finset.prod_nonneg fun p _ => pow_nonneg (hw0 p.1 p.2) _
  have hstep2 : (∑ e : P → Fin (M + 1), ∏ p : P, g p (e p)) =
      ∏ p : P, ∑ k : Fin (M + 1), g p k := (Fintype.prod_sum g).symm
  have hstep3 : (∏ p : P, ∑ k : Fin (M + 1), g p k) ≤ ∏ p ∈ P, (1 - w p)⁻¹ := by
    rw [← Finset.prod_coe_sort P (fun p => (1 - w p)⁻¹)]
    apply Finset.prod_le_prod
    · intro p _
      exact Finset.sum_nonneg fun k _ => pow_nonneg (hw0 p.1 p.2) _
    · intro p _
      have hsum : (∑ k : Fin (M + 1), g p k) = ∑ k ∈ range (M + 1), (w p.1) ^ k :=
        Fin.sum_univ_eq_sum_range (fun k => (w p.1) ^ k) (M + 1)
      rw [hsum]
      exact geom_sum_le_inv (hw0 p.1 p.2) (hw1 p.1 p.2) M
  linarith

private lemma harmonic_two_pow (k : ℕ) :
    1 + (k : ℝ) / 2 ≤ ∑ n ∈ Icc (1 : ℕ) (2 ^ k), (1 : ℝ) / (n : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsplit : Icc (1 : ℕ) (2 ^ (k + 1)) =
        Icc (1 : ℕ) (2 ^ k) ∪ Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1)) := by
      ext x
      simp only [mem_Icc, mem_union]
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega
    have hdisj : Disjoint (Icc (1 : ℕ) (2 ^ k)) (Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1))) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [mem_Icc] at hx1 hx2
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have hblock : (1 : ℝ) / 2 ≤ ∑ n ∈ Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1)), (1 : ℝ) / (n : ℝ) := by
      have hcard : (Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1))).card = 2 ^ k := by
        rw [Nat.card_Icc]
        have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        omega
      have hterm : ∀ n ∈ Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1)),
          (1 : ℝ) / (2 ^ (k + 1) : ℝ) ≤ (1 : ℝ) / (n : ℝ) := by
        intro n hn
        simp only [mem_Icc] at hn
        apply one_div_le_one_div_of_le
        · exact_mod_cast (show 0 < n by omega)
        · exact_mod_cast hn.2
      calc
        (1 : ℝ) / 2 = (2 ^ k : ℝ) * ((1 : ℝ) / (2 ^ (k + 1) : ℝ)) := by
          rw [pow_succ]; field_simp
        _ = ∑ _n ∈ Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1)), (1 : ℝ) / (2 ^ (k + 1) : ℝ) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]; push_cast; rfl
        _ ≤ ∑ n ∈ Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1)), (1 : ℝ) / (n : ℝ) := Finset.sum_le_sum hterm
    push_cast
    linarith

private lemma exists_prime_set_density_le {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ ∏ p ∈ P, (1 - (1 : ℝ) / p) ≤ ε := by
  let k := Nat.ceil (2 / ε)
  let N := 2 ^ k
  let P := (Icc 1 N).filter Nat.Prime
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  refine ⟨P, hP, ?_⟩
  have hw0 : ∀ p ∈ P, 0 ≤ (1 : ℝ) / p := fun p _ => by positivity
  have hw1 : ∀ p ∈ P, (1 : ℝ) / p < 1 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    rw [div_lt_one (by linarith)]
    linarith
  have hF : ∀ n ∈ Icc 1 N, IsPSmooth P n ∧ ∀ p ∈ P, n.factorization p ≤ N := by
    intro n hn
    rw [mem_Icc] at hn
    refine ⟨⟨by omega, fun p hp hpdvd => ?_⟩, fun p hp => (factorization_le_self (by omega) (hP p hp)).trans hn.2⟩
    refine Finset.mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.pos, (Nat.le_of_dvd (by omega) hpdvd).trans hn.2⟩, hp⟩
  have heuler := finite_euler_product hP (fun p => (1 : ℝ) / p) hw0 hw1 (Icc 1 N) N hF
  have hterm : ∀ n ∈ Icc 1 N, (∏ p ∈ P, ((1 : ℝ) / p) ^ n.factorization p) = (1 : ℝ) / n := by
    intro n hn
    have hs := (hF n hn).1
    have heq := smoothPart_eq_self_of_isPSmooth hs
    have hprod : (∏ p ∈ P, ((1 : ℝ) / p) ^ n.factorization p) =
        (1 : ℝ) / (∏ p ∈ P, (p : ℝ) ^ n.factorization p) := by
      simp only [one_div, inv_pow, Finset.prod_inv_distrib]
    rw [hprod]
    congr 1
    exact_mod_cast heq
  rw [Finset.sum_congr rfl hterm] at heuler
  have hharm : 1 / ε ≤ ∑ n ∈ Icc 1 N, (1 : ℝ) / (n : ℝ) := by
    have hk : 2 / ε ≤ (k : ℝ) := Nat.le_ceil _
    have h1 : 1 + (k : ℝ) / 2 ≤ ∑ n ∈ Icc 1 N, (1 : ℝ) / (n : ℝ) := harmonic_two_pow k
    have h2 : 1 / ε ≤ (k : ℝ) / 2 := by
      have : 2 / ε = 2 * (1 / ε) := by ring
      linarith
    linarith
  have hinv_pos : 0 < ∏ p ∈ P, (1 - (1 : ℝ) / p) :=
    Finset.prod_pos fun p hp => sub_pos.mpr (hw1 p hp)
  have hprod_inv : (∏ p ∈ P, (1 - (1 : ℝ) / p))⁻¹ = ∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹ :=
    (Finset.prod_inv_distrib (fun p : ℕ => 1 - (1 : ℝ) / p)).symm
  have hbig : 1 / ε ≤ (∏ p ∈ P, (1 - (1 : ℝ) / p))⁻¹ := by
    rw [hprod_inv]
    exact hharm.trans heuler
  rw [one_div] at hbig
  exact (inv_le_inv₀ hε hinv_pos).mp hbig

private lemma smooth_inv_sqrt_sum_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (A : ℕ) :
    (∑ s ∈ (Icc 1 A).filter (IsPSmooth P), (1 : ℝ) / Real.sqrt s) ≤
      ∏ p ∈ P, (1 - (1 : ℝ) / Real.sqrt p)⁻¹ := by
  have hw0 : ∀ p ∈ P, 0 ≤ (1 : ℝ) / Real.sqrt p := fun p _ => by positivity
  have hw1 : ∀ p ∈ P, (1 : ℝ) / Real.sqrt p < 1 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hsq : 1 < Real.sqrt p := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt zero_le_one (by linarith)
    rw [div_lt_one (by linarith)]
    exact hsq
  have hF : ∀ s ∈ (Icc 1 A).filter (IsPSmooth P),
      IsPSmooth P s ∧ ∀ p ∈ P, s.factorization p ≤ A := by
    intro s hs
    rw [Finset.mem_filter, mem_Icc] at hs
    exact ⟨hs.2, fun p hp => (factorization_le_self (by omega) (hP p hp)).trans hs.1.2⟩
  have heuler := finite_euler_product hP (fun p => (1 : ℝ) / Real.sqrt p) hw0 hw1
    ((Icc 1 A).filter (IsPSmooth P)) A hF
  have hterm : ∀ s ∈ (Icc 1 A).filter (IsPSmooth P),
      (∏ p ∈ P, ((1 : ℝ) / Real.sqrt p) ^ s.factorization p) = (1 : ℝ) / Real.sqrt s := by
    intro s hs
    have hsm : IsPSmooth P s := (Finset.mem_filter.mp hs).2
    have heq := smoothPart_eq_self_of_isPSmooth hsm
    have hprod : (∏ p ∈ P, ((1 : ℝ) / Real.sqrt p) ^ s.factorization p) =
        (1 : ℝ) / (∏ p ∈ P, (Real.sqrt p) ^ s.factorization p) := by
      simp only [one_div, inv_pow, Finset.prod_inv_distrib]
    rw [hprod]
    congr 1
    have hsqrt_pow : ∀ p ∈ P, (Real.sqrt p) ^ s.factorization p =
        Real.sqrt ((p ^ s.factorization p : ℕ) : ℝ) := by
      intro p _
      rw [Nat.cast_pow]
      symm
      refine (Real.sqrt_eq_iff_eq_sq (pow_nonneg (Nat.cast_nonneg p) _)
        (pow_nonneg (Real.sqrt_nonneg _) _)).mpr ?_
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg p)]
    rw [Finset.prod_congr rfl hsqrt_pow, ← Real.sqrt_prod _ (fun p _ => Nat.cast_nonneg _)]
    congr 1
    exact_mod_cast heq
  rwa [Finset.sum_congr rfl hterm] at heuler

private lemma card_large_smoothPart_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {C : ℝ} (_hC : 0 < C) {S : ℕ} (hS : 1 ≤ S)
    (hSbound : (∏ p ∈ P, (1 - (1 : ℝ) / Real.sqrt p)⁻¹) / Real.sqrt S ≤ 1 / (8 * C))
    (A : ℕ) :
    (((Icc 1 A).filter (fun a => S < smoothPart P a)).card : ℝ) ≤ (A : ℝ) / (8 * C) := by
  classical
  let bad := (Icc 1 A).filter (fun a => S < smoothPart P a)
  let T := (Icc (S + 1) A).filter (IsPSmooth P)
  have hmaps : ∀ a ∈ bad, smoothPart P a ∈ T := by
    intro a ha
    rw [Finset.mem_filter, mem_Icc] at ha
    rw [Finset.mem_filter, mem_Icc]
    have hdvd : smoothPart P a ∣ a := smoothPart_dvd hP (by omega)
    exact ⟨⟨by omega, (Nat.le_of_dvd (by omega) hdvd).trans ha.1.2⟩, isPSmooth_smoothPart hP a⟩
  have hfib : bad.card = ∑ s ∈ T, (bad.filter (fun a => smoothPart P a = s)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hfib_le : ∀ s ∈ T, ((bad.filter (fun a => smoothPart P a = s)).card : ℝ) ≤
      (A : ℝ) / (s : ℝ) := by
    intro s hs
    have hs_pos : 0 < s := ((Finset.mem_filter.mp hs).2).1
    have hcard_nat : (bad.filter (fun a => smoothPart P a = s)).card ≤ A / s := by
      have hinj : Set.InjOn (fun a => a / s) ((bad.filter (fun a => smoothPart P a = s)) : Set ℕ) := by
        intro a ha b hb hab
        simp only [Finset.mem_coe, Finset.mem_filter, bad, mem_Icc] at ha hb
        dsimp only at hab
        have hda : s ∣ a := ha.2 ▸ smoothPart_dvd hP (by omega)
        have hdb : s ∣ b := hb.2 ▸ smoothPart_dvd hP (by omega)
        rw [← Nat.mul_div_cancel' hda, ← Nat.mul_div_cancel' hdb, hab]
      have himg : (bad.filter (fun a => smoothPart P a = s)).image (fun a => a / s) ⊆ Icc 1 (A / s) := by
        intro q hq
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
        simp only [Finset.mem_filter, bad, mem_Icc] at ha
        have hda : s ∣ a := ha.2 ▸ smoothPart_dvd hP (by omega)
        have hqpos : 0 < a / s := Nat.div_pos (Nat.le_of_dvd (by omega) hda) hs_pos
        exact mem_Icc.mpr ⟨hqpos, Nat.div_le_div_right ha.1.1.2⟩
      calc
        (bad.filter (fun a => smoothPart P a = s)).card
            = ((bad.filter (fun a => smoothPart P a = s)).image (fun a => a / s)).card :=
          (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Icc 1 (A / s)).card := Finset.card_le_card himg
        _ = A / s := by rw [Nat.card_Icc, Nat.add_sub_cancel]
    calc
      ((bad.filter (fun a => smoothPart P a = s)).card : ℝ) ≤ ((A / s : ℕ) : ℝ) := by
        exact_mod_cast hcard_nat
      _ ≤ (A : ℝ) / (s : ℝ) := Nat.cast_div_le
  have hTsub : T ⊆ (Icc 1 A).filter (IsPSmooth P) := by
    intro s hs
    simp only [T, Finset.mem_filter, mem_Icc] at hs ⊢
    exact ⟨⟨by omega, hs.1.2⟩, hs.2⟩
  have hSpos : (0 : ℝ) < Real.sqrt S := Real.sqrt_pos.mpr (by exact_mod_cast hS)
  have hinv_le : ∀ s ∈ T, (1 : ℝ) / (s : ℝ) ≤ (1 / Real.sqrt S) * ((1 : ℝ) / Real.sqrt s) := by
    intro s hs
    have hs1 : S < s := by
      have := (Finset.mem_filter.mp hs).1
      rw [mem_Icc] at this; omega
    have hsR : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
    have hsq : Real.sqrt S ≤ Real.sqrt s := Real.sqrt_le_sqrt (by exact_mod_cast hs1.le)
    have hsq_pos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hsR
    have hmul : (s : ℝ) = Real.sqrt s * Real.sqrt s := (Real.mul_self_sqrt hsR.le).symm
    rw [one_div_mul_one_div, one_div_le_one_div hsR (mul_pos hSpos hsq_pos)]
    calc
      Real.sqrt S * Real.sqrt s ≤ Real.sqrt s * Real.sqrt s :=
        mul_le_mul_of_nonneg_right hsq hsq_pos.le
      _ = (s : ℝ) := hmul.symm
  calc
    (bad.card : ℝ) = ∑ s ∈ T, ((bad.filter (fun a => smoothPart P a = s)).card : ℝ) := by
      rw [hfib, Nat.cast_sum]
    _ ≤ ∑ s ∈ T, (A : ℝ) / (s : ℝ) := Finset.sum_le_sum hfib_le
    _ = (A : ℝ) * ∑ s ∈ T, (1 : ℝ) / (s : ℝ) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring
    _ ≤ (A : ℝ) * ∑ s ∈ T, (1 / Real.sqrt S) * ((1 : ℝ) / Real.sqrt s) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hinv_le) (Nat.cast_nonneg A)
    _ = (A : ℝ) * (1 / Real.sqrt S) * ∑ s ∈ T, (1 : ℝ) / Real.sqrt s := by
      rw [← Finset.mul_sum]; ring
    _ ≤ (A : ℝ) * (1 / Real.sqrt S) * ∑ s ∈ (Icc 1 A).filter (IsPSmooth P), (1 : ℝ) / Real.sqrt s := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg hTsub (fun _ _ _ => by positivity)
    _ ≤ (A : ℝ) * (1 / Real.sqrt S) * ∏ p ∈ P, (1 - (1 : ℝ) / Real.sqrt p)⁻¹ := by
      apply mul_le_mul_of_nonneg_left (smooth_inv_sqrt_sum_le hP A) (by positivity)
    _ = (A : ℝ) * ((∏ p ∈ P, (1 - (1 : ℝ) / Real.sqrt p)⁻¹) / Real.sqrt S) := by ring
    _ ≤ (A : ℝ) * (1 / (8 * C)) := mul_le_mul_of_nonneg_left hSbound (Nat.cast_nonneg A)
    _ = (A : ℝ) / (8 * C) := by ring

/- Section 2: Periodicity count of P-rough integers -/

private lemma totient_prod_primes {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    ((∏ p ∈ P, p).totient : ℝ) = (∏ p ∈ P, p : ℕ) * ∏ p ∈ P, (1 - (1 : ℝ) / p) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hp_prime : p.Prime := hP p (Finset.mem_insert_self p s)
    have hs_prime : ∀ q ∈ s, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      apply hp_prime.coprime_iff_not_dvd.mpr
      intro hdvd
      obtain ⟨q, hq, hqp⟩ := (hp_prime.prime.dvd_finsetProd_iff _).mp hdvd
      have heq := (Nat.prime_dvd_prime_iff_eq hp_prime (hs_prime q hq)).mp hqp
      exact hp (heq ▸ hq)
    rw [Finset.prod_insert hp, Finset.prod_insert hp, Nat.totient_mul hcop, Nat.totient_prime hp_prime]
    push_cast
    rw [ih hs_prime]
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
    have hp_sub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) * (1 - (1 : ℝ) / p) := by
      rw [Nat.cast_sub hp_prime.one_le, Nat.cast_one]
      field_simp [hp_pos.ne']
    rw [hp_sub]
    simp only [Nat.cast_prod]
    ring

private lemma card_rough_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (X : ℕ) :
    (((Icc 1 X).filter (fun r => ∀ p ∈ P, ¬ p ∣ r)).card : ℝ) ≤
      (X : ℝ) * (∏ p ∈ P, (1 - (1 : ℝ) / p)) + ((∏ p ∈ P, p : ℕ) : ℝ) := by
  classical
  let M : ℕ := ∏ p ∈ P, p
  have hMpos : 0 < M := Finset.prod_pos fun p hp => (hP p hp).pos
  let R := (Icc 1 X).filter (fun r => ∀ p ∈ P, ¬ p ∣ r)
  have hcop' : ∀ r ∈ R, Nat.Coprime M (r % M) := by
    intro r hr
    have hndvd : ∀ p ∈ P, ¬ p ∣ r := (Finset.mem_filter.mp hr).2
    have hcop_r : Nat.Coprime r M := by
      apply Nat.coprime_of_dvd'
      intro q hq hqr hqM
      obtain ⟨p, hp, hqp⟩ := (hq.prime.dvd_finsetProd_iff _).mp hqM
      have heq := (Nat.prime_dvd_prime_iff_eq hq (hP p hp)).mp hqp
      exact (hndvd p hp (heq ▸ hqr)).elim
    have hmod : Nat.Coprime (r % M) M := by
      change Nat.gcd (r % M) M = 1
      rw [← Nat.gcd_rec, Nat.gcd_comm]
      exact hcop_r
    exact hmod.symm
  let f : ℕ → ℕ × ℕ := fun r => (r / M, r % M)
  have hinj : Set.InjOn f (R : Set ℕ) := by
    intro a _ b _ hab
    have h1 : a / M = b / M := congrArg Prod.fst hab
    have h2 : a % M = b % M := congrArg Prod.snd hab
    rw [← Nat.div_add_mod a M, ← Nat.div_add_mod b M, h1, h2]
  have himg : R.image f ⊆ range (X / M + 1) ×ˢ (range M).filter (Nat.Coprime M) := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy
    have hrX : r ≤ X := (mem_Icc.mp (Finset.mem_filter.mp hr).1).2
    refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hrX)),
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt r hMpos), hcop' r hr⟩⟩
  have hnat : R.card ≤ (X / M + 1) * M.totient := by
    calc
      R.card = (R.image f).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (range (X / M + 1) ×ˢ (range M).filter (Nat.Coprime M)).card := Finset.card_le_card himg
      _ = (X / M + 1) * M.totient := by
        rw [Finset.card_product, Finset.card_range, Nat.totient_eq_card_coprime]
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  have hdiv : ((X / M : ℕ) : ℝ) ≤ (X : ℝ) / (M : ℝ) := Nat.cast_div_le
  have htot_le : (M.totient : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.totient_le M
  have htot_eq : (M.totient : ℝ) = (M : ℝ) * ∏ p ∈ P, (1 - (1 : ℝ) / p) := totient_prod_primes hP
  calc
    (R.card : ℝ) ≤ (((X / M + 1) * M.totient : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = ((X / M : ℕ) : ℝ) * (M.totient : ℝ) + (M.totient : ℝ) := by push_cast; ring
    _ ≤ ((X : ℝ) / (M : ℝ)) * (M.totient : ℝ) + (M : ℝ) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) M.totient]
    _ = (X : ℝ) * (∏ p ∈ P, (1 - (1 : ℝ) / p)) + (M : ℝ) := by
      rw [htot_eq]; field_simp [hMR.ne']

/- Section 3: Rational height transfer -/

private lemma height_le_of_mul_eq {u w X Y D : ℕ} (hX : 0 < X) (hY : 0 < Y)
    (hXD : X ≤ D) (hYD : Y ≤ D) (heq : u * Y = w * X) :
    max u w ≤ D * Nat.gcd u w := by
  by_cases hg0 : Nat.gcd u w = 0
  · have hu : u = 0 := (Nat.gcd_eq_zero_iff.mp hg0).1
    have hw : w = 0 := (Nat.gcd_eq_zero_iff.mp hg0).2
    simp [hu, hw]
  · set g := Nat.gcd u w
    have hg : 0 < g := Nat.pos_of_ne_zero hg0
    let u' := u / g
    let w' := w / g
    have hu_eq : g * u' = u := Nat.mul_div_cancel' (Nat.gcd_dvd_left u w)
    have hw_eq : g * w' = w := Nat.mul_div_cancel' (Nat.gcd_dvd_right u w)
    have hcop : Nat.Coprime u' w' := Nat.coprime_div_gcd_div_gcd hg
    have heq' : u' * Y = w' * X := by
      apply Nat.eq_of_mul_eq_mul_left hg
      calc
        g * (u' * Y) = (g * u') * Y := by ring
        _ = u * Y := by rw [hu_eq]
        _ = w * X := heq
        _ = (g * w') * X := by rw [hw_eq]
        _ = g * (w' * X) := by ring
    have hu_dvd : u' ∣ X := hcop.dvd_of_dvd_mul_left ⟨Y, by linarith⟩
    have hw_dvd : w' ∣ Y := hcop.symm.dvd_of_dvd_mul_left ⟨X, by linarith⟩
    have hu_le : u' ≤ D := (Nat.le_of_dvd hX hu_dvd).trans hXD
    have hw_le : w' ≤ D := (Nat.le_of_dvd hY hw_dvd).trans hYD
    rw [max_le_iff]
    constructor
    · calc
        u = u' * g := by rw [← hu_eq, mul_comm]
        _ ≤ D * g := Nat.mul_le_mul_right g hu_le
    · calc
        w = w' * g := by rw [← hw_eq, mul_comm]
        _ ≤ D * g := Nat.mul_le_mul_right g hw_le

private lemma mul_eq_of_rat_repr {u w a1 b1 a2 b2 : ℕ} {ξ : ℚ} (hξ : 0 < ξ)
    (hb1 : 0 < b1) (hb2 : 0 < b2)
    (h1 : (u : ℚ) = ξ * a1 / b1) (h2 : (w : ℚ) = ξ * a2 / b2) :
    u * (a2 * b1) = w * (a1 * b2) := by
  have hQ : ((u * (a2 * b1) : ℕ) : ℚ) = ((w * (a1 * b2) : ℕ) : ℚ) := by
    push_cast
    rw [h1, h2]
    have hb1' : (b1 : ℚ) ≠ 0 := by exact_mod_cast hb1.ne'
    have hb2' : (b2 : ℚ) ≠ 0 := by exact_mod_cast hb2.ne'
    field_simp [hb1', hb2']
  exact_mod_cast hQ

private lemma height_le_of_same_rough {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {u w a1 b1 a2 b2 S : ℕ} {ξ : ℚ} (hξ : 0 < ξ)
    (ha1 : 0 < a1) (hb1 : 0 < b1) (ha2 : 0 < a2) (hb2 : 0 < b2)
    (h1 : (u : ℚ) = ξ * a1 / b1) (h2 : (w : ℚ) = ξ * a2 / b2)
    (hra : roughPart P a1 = roughPart P a2) (hrb : roughPart P b1 = roughPart P b2)
    (hsa1 : smoothPart P a1 ≤ S) (hsb1 : smoothPart P b1 ≤ S)
    (hsa2 : smoothPart P a2 ≤ S) (hsb2 : smoothPart P b2 ≤ S) :
    max u w ≤ S ^ 2 * Nat.gcd u w := by
  have hmul := mul_eq_of_rat_repr hξ hb1 hb2 h1 h2
  have hr_pos : 0 < roughPart P a1 * roughPart P b1 :=
    mul_pos (roughPart_pos hP ha1) (roughPart_pos hP hb1)
  have hcancel : u * (smoothPart P a2 * smoothPart P b1) =
      w * (smoothPart P a1 * smoothPart P b2) := by
    apply Nat.eq_of_mul_eq_mul_right hr_pos
    calc
      u * (smoothPart P a2 * smoothPart P b1) * (roughPart P a1 * roughPart P b1)
          = u * ((smoothPart P a2 * roughPart P a2) * (smoothPart P b1 * roughPart P b1)) := by
            rw [hra]; ring
      _ = u * (a2 * b1) := by
            rw [smoothPart_mul_roughPart hP ha2, smoothPart_mul_roughPart hP hb1]
      _ = w * (a1 * b2) := hmul
      _ = w * ((smoothPart P a1 * roughPart P a1) * (smoothPart P b2 * roughPart P b2)) := by
            rw [smoothPart_mul_roughPart hP ha1, smoothPart_mul_roughPart hP hb2]
      _ = w * (smoothPart P a1 * smoothPart P b2) * (roughPart P a1 * roughPart P b1) := by
            rw [hrb]; ring
  have hXpos : 0 < smoothPart P a1 * smoothPart P b2 :=
    mul_pos (smoothPart_pos hP a1) (smoothPart_pos hP b2)
  have hYpos : 0 < smoothPart P a2 * smoothPart P b1 :=
    mul_pos (smoothPart_pos hP a2) (smoothPart_pos hP b1)
  have hXle : smoothPart P a1 * smoothPart P b2 ≤ S ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul hsa1 hsb2
  have hYle : smoothPart P a2 * smoothPart P b1 ≤ S ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul hsa2 hsb1
  exact height_le_of_mul_eq hXpos hYpos hXle hYle hcancel

/- Section 4: Greedy maximal matching -/

private lemma exists_maximal_matching' {α : Type*} [DecidableEq α]
    (R : α → α → Prop) :
    ∀ (k : ℕ) (U : Finset α), U.card ≤ k →
      ∃ (m : ℕ) (e : Fin m × Bool ↪ α),
        (∀ p : Fin m, e (p, false) ∈ U ∧ e (p, true) ∈ U ∧ R (e (p, false)) (e (p, true))) ∧
        (∀ x ∈ U \ (Finset.univ.image e), ∀ y ∈ U \ (Finset.univ.image e), x ≠ y → ¬ R x y) := by
  intro k
  induction k with
  | zero =>
    intro U hU
    refine ⟨0, ⟨fun p => p.1.elim0, fun p _ _ => p.1.elim0⟩, fun p => p.elim0, ?_⟩
    intro x hx _ _ _
    have hU0 : U = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hU)
    rw [hU0] at hx
    exact absurd (Finset.sdiff_subset hx) (Finset.notMem_empty x)
  | succ k ih =>
    intro U hU
    by_cases hex : ∃ x ∈ U, ∃ y ∈ U, x ≠ y ∧ R x y
    · obtain ⟨x, hxU, y, hyU, hxy, hRxy⟩ := hex
      let U' := (U.erase x).erase y
      have hcard' : U'.card ≤ k := by
        have hy' : y ∈ U.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hyU⟩
        have h1 : U'.card + 1 = (U.erase x).card := Finset.card_erase_add_one hy'
        have h2 : (U.erase x).card + 1 = U.card := Finset.card_erase_add_one hxU
        omega
      obtain ⟨m, e', he', hind'⟩ := ih U' hcard'
      let ef : Fin (m + 1) × Bool → α := fun pb =>
        match pb.1 with
        | ⟨0, _⟩ => if pb.2 then y else x
        | ⟨j + 1, hj⟩ => e' (⟨j, Nat.lt_of_succ_lt_succ hj⟩, pb.2)
      have he'_mem : ∀ p : Fin m, ∀ b : Bool, e' (p, b) ∈ U' := by
        intro p b
        cases b
        · exact (he' p).1
        · exact (he' p).2.1
      have he'_not_xy : ∀ p : Fin m, ∀ b : Bool, e' (p, b) ≠ x ∧ e' (p, b) ≠ y := by
        intro p b
        have h1 := Finset.mem_erase.mp (he'_mem p b)
        have h2 := Finset.mem_erase.mp h1.2
        exact ⟨h2.1, h1.1⟩
      have hinj : Function.Injective ef := by
        rintro ⟨⟨i, hi⟩, bi⟩ ⟨⟨j, hj⟩, bj⟩ heq
        cases i with
        | zero =>
          cases j with
          | zero =>
            simp only [ef] at heq
            cases bi <;> cases bj <;> simp_all
          | succ j' =>
            simp only [ef] at heq
            have hne := he'_not_xy ⟨j', Nat.lt_of_succ_lt_succ hj⟩ bj
            cases bi
            · exact absurd heq.symm hne.1
            · exact absurd heq.symm hne.2
        | succ i' =>
          cases j with
          | zero =>
            simp only [ef] at heq
            have hne := he'_not_xy ⟨i', Nat.lt_of_succ_lt_succ hi⟩ bi
            cases bj
            · exact absurd heq hne.1
            · exact absurd heq hne.2
          | succ j' =>
            simp only [ef] at heq
            have hpair := e'.injective heq
            have h1 := congrArg (fun z : Fin m × Bool => z.1.val) hpair
            have h2 := congrArg Prod.snd hpair
            dsimp at h1 h2
            exact Prod.ext (Fin.ext (congrArg (· + 1) h1)) h2
      let e : Fin (m + 1) × Bool ↪ α := ⟨ef, hinj⟩
      refine ⟨m + 1, e, ?_, ?_⟩
      · rintro ⟨i, hi⟩
        cases i with
        | zero => exact ⟨hxU, hyU, hRxy⟩
        | succ i' =>
          have hp := he' ⟨i', Nat.lt_of_succ_lt_succ hi⟩
          have hsub : U' ⊆ U := (Finset.erase_subset y _).trans (Finset.erase_subset x U)
          exact ⟨hsub hp.1, hsub hp.2.1, hp.2.2⟩
      · intro a ha b hb hab
        have hsub_sdiff : U \ (Finset.univ.image e) ⊆ U' \ (Finset.univ.image e') := by
          intro z hz
          rw [Finset.mem_sdiff] at hz ⊢
          have hz_notx : z ≠ x := by
            intro hzx
            apply hz.2
            exact Finset.mem_image.mpr ⟨(⟨0, Nat.succ_pos m⟩, false), Finset.mem_univ _, hzx.symm⟩
          have hz_noty : z ≠ y := by
            intro hzy
            apply hz.2
            exact Finset.mem_image.mpr ⟨(⟨0, Nat.succ_pos m⟩, true), Finset.mem_univ _, hzy.symm⟩
          refine ⟨Finset.mem_erase.mpr ⟨hz_noty, Finset.mem_erase.mpr ⟨hz_notx, hz.1⟩⟩, ?_⟩
          intro hmem
          obtain ⟨⟨p, bp⟩, _, hpz⟩ := Finset.mem_image.mp hmem
          apply hz.2
          exact Finset.mem_image.mpr ⟨(⟨p.val + 1, Nat.succ_lt_succ p.isLt⟩, bp), Finset.mem_univ _, hpz⟩
        exact hind' a (hsub_sdiff ha) b (hsub_sdiff hb) hab
    · push Not at hex
      refine ⟨0, ⟨fun p => p.1.elim0, fun p _ _ => p.1.elim0⟩, fun p => p.elim0, ?_⟩
      intro x hx y hy hne
      exact hex x (Finset.sdiff_subset hx) y (Finset.sdiff_subset hy) hne

private lemma rough_prod_bound {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {C : ℝ} (hCpos : 0 < C) (hdP : ∏ p ∈ P, (1 - (1 : ℝ) / p) ≤ 1 / (8 * C))
    {u : ℝ} (hu_pos : 0 < u)
    (hCMsqrt : ((∏ p ∈ P, p : ℕ) : ℝ) * C * Real.sqrt u ≤ u / 8)
    {X Y : ℕ} (hXpos : 0 < X) (hYX : Y ≤ X)
    (hXY_le : (X : ℝ) * (Y : ℝ) ≤ C * u) (hu_le_XY : u ≤ (X : ℝ) * (Y : ℝ)) :
    (((Icc 1 X).filter (fun r => ∀ p ∈ P, ¬ p ∣ r)).card : ℝ) * (Y : ℝ) ≤ u / 4 := by
  let M : ℕ := ∏ p ∈ P, p
  have hXposR : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hX_ge_sqrt : Real.sqrt u ≤ (X : ℝ) := by
    have h1 : u ≤ (X : ℝ) ^ 2 := by
      have hYXR : (Y : ℝ) ≤ (X : ℝ) := by exact_mod_cast hYX
      nlinarith
    rw [← Real.sqrt_sq hXposR.le]
    exact Real.sqrt_le_sqrt h1
  have hY_le : (Y : ℝ) ≤ C * Real.sqrt u := by
    have hsqrt_pos : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu_pos
    have h1 : (Y : ℝ) * Real.sqrt u ≤ C * u := by
      calc
        (Y : ℝ) * Real.sqrt u ≤ (Y : ℝ) * (X : ℝ) :=
          mul_le_mul_of_nonneg_left hX_ge_sqrt (Nat.cast_nonneg Y)
        _ = (X : ℝ) * (Y : ℝ) := mul_comm _ _
        _ ≤ C * u := hXY_le
    have hsq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu_pos.le
    nlinarith
  have hrough := card_rough_le hP X
  have hprod_nn : 0 ≤ ∏ p ∈ P, (1 - (1 : ℝ) / p) := by
    apply Finset.prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  have hc1 : (C * u) * (1 / (8 * C)) = u / 8 := by field_simp [hCpos.ne']
  have h1 : ((X : ℝ) * (Y : ℝ)) * (∏ p ∈ P, (1 - (1 : ℝ) / p)) ≤ u / 8 := by
    rw [← hc1]
    exact mul_le_mul hXY_le hdP hprod_nn (by positivity)
  have h2 : (M : ℝ) * (Y : ℝ) ≤ u / 8 := by
    have h2a : (M : ℝ) * (Y : ℝ) ≤ (M : ℝ) * (C * Real.sqrt u) :=
      mul_le_mul_of_nonneg_left hY_le (Nat.cast_nonneg M)
    linarith
  calc
    (((Icc 1 X).filter (fun r => ∀ p ∈ P, ¬ p ∣ r)).card : ℝ) * (Y : ℝ)
        ≤ ((X : ℝ) * (∏ p ∈ P, (1 - (1 : ℝ) / p)) + (M : ℝ)) * (Y : ℝ) :=
      mul_le_mul_of_nonneg_right hrough (Nat.cast_nonneg Y)
    _ = ((X : ℝ) * (Y : ℝ)) * (∏ p ∈ P, (1 - (1 : ℝ) / p)) + (M : ℝ) * (Y : ℝ) := by ring
    _ ≤ u / 8 + u / 8 := add_le_add h1 h2
    _ = u / 4 := by ring

/- Section 6: Main proof of H2 -/

theorem main :
    OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1_H1_R1.H2 := by
  classical
  intro C hC
  have hCpos : 0 < C := by linarith
  -- Choose finite prime set P with d_P = prod_{p in P} (1 - 1/p) <= 1 / (8 * C)
  obtain ⟨P, hP, hdP⟩ := exists_prime_set_density_le (ε := 1 / (8 * C)) (by positivity)
  let M : ℕ := ∏ p ∈ P, p
  have hMpos : 0 < M := Finset.prod_pos fun p hp => (hP p hp).pos
  let A_P : ℝ := ∏ p ∈ P, (1 - (1 : ℝ) / Real.sqrt p)⁻¹
  have hAP_pos : 0 < A_P := by
    apply Finset.prod_pos
    intro p hp
    apply inv_pos.mpr
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hsq : 1 < Real.sqrt p := by
      rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt zero_le_one (by linarith)
    rw [sub_pos, div_lt_one (by linarith)]
    exact hsq
  let S : ℕ := Nat.ceil ((8 * C * A_P) ^ 2) + 1
  have hS1 : 1 ≤ S := by omega
  have hSbound : A_P / Real.sqrt S ≤ 1 / (8 * C) := by
    have h1 : (8 * C * A_P) ^ 2 ≤ (S : ℝ) := by
      have := Nat.le_ceil ((8 * C * A_P) ^ 2)
      have hS' : ((Nat.ceil ((8 * C * A_P) ^ 2) : ℕ) : ℝ) ≤ (S : ℝ) := by exact_mod_cast (by omega : Nat.ceil ((8 * C * A_P) ^ 2) ≤ S)
      linarith
    have h2 : 8 * C * A_P ≤ Real.sqrt S := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 8 * C * A_P)]
      exact Real.sqrt_le_sqrt h1
    have hSpos : 0 < Real.sqrt S := Real.sqrt_pos.mpr (by exact_mod_cast hS1)
    rw [div_le_div_iff₀ hSpos (by positivity)]
    nlinarith
  let N0 : ℕ := max 2 (Nat.ceil ((8 * C * (M : ℝ)) ^ 2) + 1)
  have hN0_ge2 : 2 ≤ N0 := le_max_left _ _
  have hN0_pos : (0 : ℝ) < N0 := by exact_mod_cast (show 0 < N0 by omega)
  let D : ℕ := max (S ^ 2) (Nat.ceil (C * (N0 : ℝ)) + 1)
  have hD_pos : 0 < D := by
    have : 1 ≤ Nat.ceil (C * (N0 : ℝ)) + 1 := by omega
    exact lt_of_lt_of_le (by omega) (le_max_right _ _)
  let η : ℝ := min (1 / 4 : ℝ) (1 / (N0 : ℝ))
  have hη_pos : 0 < η := lt_min (by norm_num) (by positivity)
  refine ⟨D, η, hD_pos, hη_pos, ?_⟩
  intro n v hv U hU2 ξ A B hξ hA hB hAB hrepr
  have hU_pos : (0 : ℝ) < U.card := by exact_mod_cast (show 0 < U.card by omega)
  -- Choose a representation (a i, b i) for each i in U
  let a : Fin n → ℕ := fun i =>
    if hi : i ∈ U then (hrepr i hi).choose else 1
  let b : Fin n → ℕ := fun i =>
    if hi : i ∈ U then (hrepr i hi).choose_spec.choose else 1
  have hab : ∀ i ∈ U, 0 < a i ∧ a i ≤ A ∧ 0 < b i ∧ b i ≤ B ∧
      (v i : ℚ) = ξ * (a i : ℚ) / (b i : ℚ) := by
    intro i hi
    simp only [a, b, dif_pos hi]
    exact (hrepr i hi).choose_spec.choose_spec
  -- (a i, b i) is injective on U since v is injective
  have hab_inj : Set.InjOn (fun i => (a i, b i)) (U : Set (Fin n)) := by
    intro i hi j hj heq
    have ha_eq : a i = a j := congrArg Prod.fst heq
    have hb_eq : b i = b j := congrArg Prod.snd heq
    have hv_eq : (v i : ℚ) = (v j : ℚ) := by
      rw [(hab i hi).2.2.2.2, (hab j hj).2.2.2.2, ha_eq, hb_eq]
    exact v.injective (by exact_mod_cast hv_eq)
  -- Split into small case U.card < N0 and large case N0 <= U.card
  by_cases hsmall : U.card < N0
  · -- Small case: pick any two distinct elements x, y in U
    obtain ⟨x, hxU, y, hyU, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < U.card)
    let ef : Fin 1 × Bool → Fin n := fun pb => if pb.2 then y else x
    have hinj : Function.Injective ef := by
      rintro ⟨⟨i, hi⟩, bi⟩ ⟨⟨j, hj⟩, bj⟩ heq
      have hij : i = j := by omega
      subst hij
      simp only [ef] at heq
      cases bi <;> cases bj <;> simp_all
    refine ⟨1, ⟨ef, hinj⟩, ?_, ?_⟩
    · have h1 : η ≤ 1 / (N0 : ℝ) := min_le_right _ _
      have h2 : (U.card : ℝ) ≤ N0 := by exact_mod_cast hsmall.le
      calc
        η * (U.card : ℝ) ≤ (1 / (N0 : ℝ)) * (N0 : ℝ) :=
          mul_le_mul h1 h2 hU_pos.le (by positivity)
        _ = 1 := by field_simp [hN0_pos.ne']
        _ = ((1 : ℕ) : ℝ) := by norm_num
    · intro p
      have hax := hab x hxU
      have hay := hab y hyU
      refine ⟨hxU, hyU, ?_⟩
      have hmul := mul_eq_of_rat_repr hξ hax.2.2.1 hay.2.2.1 hax.2.2.2.2 hay.2.2.2.2
      have hAB_D : A * B ≤ D := by
        have hAB_R : ((A * B : ℕ) : ℝ) ≤ C * (N0 : ℝ) := by
          have hUN : (U.card : ℝ) ≤ N0 := by exact_mod_cast hsmall.le
          push_cast
          exact hAB.trans (mul_le_mul_of_nonneg_left hUN hCpos.le)
        have hceil : A * B ≤ Nat.ceil (C * (N0 : ℝ)) := Nat.le_ceil (C * (N0 : ℝ)) |> fun h => by
          exact_mod_cast hAB_R.trans h
        exact hceil.trans ((Nat.le_succ _).trans (le_max_right _ _))
      have hXle : a x * b y ≤ D := (Nat.mul_le_mul hax.2.1 hay.2.2.2.1).trans hAB_D
      have hYle : a y * b x ≤ D := (Nat.mul_le_mul hay.2.1 hax.2.2.2.1).trans hAB_D
      exact height_le_of_mul_eq (mul_pos hax.1 hay.2.2.1) (mul_pos hay.1 hax.2.2.1) hXle hYle hmul
  · -- Large case: N0 <= U.card
    have hlarge : N0 ≤ U.card := by omega
    let R : Fin n → Fin n → Prop := fun i j =>
      max (v i) (v j) ≤ D * Nat.gcd (v i) (v j)
    obtain ⟨m, e, he, hind⟩ := exists_maximal_matching' R U.card U le_rfl
    refine ⟨m, e, ?_, he⟩
    -- Bound the uncovered independent set U0 = U \ image(e)
    let U0 := U \ (Finset.univ.image e)
    -- Step A: |U| <= A * B
    have hU_le_AB : U.card ≤ A * B := by
      have himg : U.image (fun i => (a i, b i)) ⊆ Icc 1 A ×ˢ Icc 1 B := by
        intro p hp
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
        have h := hab i hi
        exact Finset.mem_product.mpr ⟨mem_Icc.mpr ⟨h.1, h.2.1⟩, mem_Icc.mpr ⟨h.2.2.1, h.2.2.2.1⟩⟩
      calc
        U.card = (U.image (fun i => (a i, b i))).card := (Finset.card_image_of_injOn hab_inj).symm
        _ ≤ (Icc 1 A ×ˢ Icc 1 B).card := Finset.card_le_card himg
        _ = A * B := by
          rw [Finset.card_product, Nat.card_Icc, Nat.card_Icc, Nat.add_sub_cancel, Nat.add_sub_cancel]
    -- Step B: Split U0 into large-smooth-part (U_bad_a, U_bad_b) and small-smooth-part U1
    let UbadA := U0.filter (fun i => S < smoothPart P (a i))
    let UbadB := U0.filter (fun i => S < smoothPart P (b i))
    let U1 := U0.filter (fun i => smoothPart P (a i) ≤ S ∧ smoothPart P (b i) ≤ S)
    have hU0_split : U0.card ≤ UbadA.card + UbadB.card + U1.card := by
      have hsub : U0 ⊆ UbadA ∪ UbadB ∪ U1 := by
        intro i hi
        by_cases h1 : S < smoothPart P (a i)
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, h1⟩))
        · by_cases h2 : S < smoothPart P (b i)
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, h2⟩))
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, by omega, by omega⟩)
      exact (Finset.card_le_card hsub).trans
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    -- Bound UbadA
    have hbadA : (UbadA.card : ℝ) ≤ (U.card : ℝ) / 8 := by
      have hsub_prod : UbadA.image (fun i => (a i, b i)) ⊆
          ((Icc 1 A).filter (fun x => S < smoothPart P x)) ×ˢ Icc 1 B := by
        intro p hp
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
        have hi' := Finset.mem_filter.mp hi
        have hiU : i ∈ U := Finset.sdiff_subset hi'.1
        have h := hab i hiU
        exact Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨mem_Icc.mpr ⟨h.1, h.2.1⟩, hi'.2⟩, mem_Icc.mpr ⟨h.2.2.1, h.2.2.2.1⟩⟩
      have hinjA : Set.InjOn (fun i => (a i, b i)) (UbadA : Set (Fin n)) :=
        hab_inj.mono (fun i hi => Finset.sdiff_subset (Finset.mem_filter.mp hi).1)
      have hcard_nat : UbadA.card ≤ ((Icc 1 A).filter (fun x => S < smoothPart P x)).card * B := by
        calc
          UbadA.card = (UbadA.image (fun i => (a i, b i))).card := (Finset.card_image_of_injOn hinjA).symm
          _ ≤ (((Icc 1 A).filter (fun x => S < smoothPart P x)) ×ˢ Icc 1 B).card := Finset.card_le_card hsub_prod
          _ = ((Icc 1 A).filter (fun x => S < smoothPart P x)).card * B := by
            rw [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel]
      have hsmooth := card_large_smoothPart_le hP hCpos hS1 hSbound A
      calc
        (UbadA.card : ℝ) ≤ (((Icc 1 A).filter (fun x => S < smoothPart P x)).card : ℝ) * (B : ℝ) := by
          exact_mod_cast hcard_nat
        _ ≤ ((A : ℝ) / (8 * C)) * (B : ℝ) := mul_le_mul_of_nonneg_right hsmooth (Nat.cast_nonneg B)
        _ = ((A : ℝ) * (B : ℝ)) / (8 * C) := by ring
        _ ≤ (C * (U.card : ℝ)) / (8 * C) := div_le_div_of_nonneg_right hAB (by positivity)
        _ = (U.card : ℝ) / 8 := by field_simp [hCpos.ne']
    -- Bound UbadB
    have hbadB : (UbadB.card : ℝ) ≤ (U.card : ℝ) / 8 := by
      have hsub_prod : UbadB.image (fun i => (a i, b i)) ⊆
          Icc 1 A ×ˢ ((Icc 1 B).filter (fun y => S < smoothPart P y)) := by
        intro p hp
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
        have hi' := Finset.mem_filter.mp hi
        have hiU : i ∈ U := Finset.sdiff_subset hi'.1
        have h := hab i hiU
        exact Finset.mem_product.mpr
          ⟨mem_Icc.mpr ⟨h.1, h.2.1⟩, Finset.mem_filter.mpr ⟨mem_Icc.mpr ⟨h.2.2.1, h.2.2.2.1⟩, hi'.2⟩⟩
      have hinjB : Set.InjOn (fun i => (a i, b i)) (UbadB : Set (Fin n)) :=
        hab_inj.mono (fun i hi => Finset.sdiff_subset (Finset.mem_filter.mp hi).1)
      have hcard_nat : UbadB.card ≤ A * ((Icc 1 B).filter (fun y => S < smoothPart P y)).card := by
        calc
          UbadB.card = (UbadB.image (fun i => (a i, b i))).card := (Finset.card_image_of_injOn hinjB).symm
          _ ≤ (Icc 1 A ×ˢ ((Icc 1 B).filter (fun y => S < smoothPart P y))).card := Finset.card_le_card hsub_prod
          _ = A * ((Icc 1 B).filter (fun y => S < smoothPart P y)).card := by
            rw [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel]
      have hsmooth := card_large_smoothPart_le hP hCpos hS1 hSbound B
      calc
        (UbadB.card : ℝ) ≤ (A : ℝ) * (((Icc 1 B).filter (fun y => S < smoothPart P y)).card : ℝ) := by
          exact_mod_cast hcard_nat
        _ ≤ (A : ℝ) * ((B : ℝ) / (8 * C)) := mul_le_mul_of_nonneg_left hsmooth (Nat.cast_nonneg A)
        _ = ((A : ℝ) * (B : ℝ)) / (8 * C) := by ring
        _ ≤ (C * (U.card : ℝ)) / (8 * C) := div_le_div_of_nonneg_right hAB (by positivity)
        _ = (U.card : ℝ) / 8 := by field_simp [hCpos.ne']
    -- Step C: Injectivity of rough pairs on U1
    have hrough_inj : Set.InjOn (fun i => (roughPart P (a i), roughPart P (b i))) (U1 : Set (Fin n)) := by
      intro i hi j hj heq
      by_contra hne
      have hi' := Finset.mem_filter.mp hi
      have hj' := Finset.mem_filter.mp hj
      have hiU : i ∈ U := Finset.sdiff_subset hi'.1
      have hjU : j ∈ U := Finset.sdiff_subset hj'.1
      have hai := hab i hiU
      have haj := hab j hjU
      have hS2D : S ^ 2 ≤ D := le_max_left _ _
      have hht : max (v i) (v j) ≤ S ^ 2 * Nat.gcd (v i) (v j) :=
        height_le_of_same_rough hP hξ hai.1 hai.2.2.1 haj.1 haj.2.2.1
          hai.2.2.2.2 haj.2.2.2.2 (congrArg Prod.fst heq) (congrArg Prod.snd heq)
          hi'.2.1 hi'.2.2 hj'.2.1 hj'.2.2
      have hRij : R i j := hht.trans (Nat.mul_le_mul_right _ hS2D)
      exact hind i hi'.1 j hj'.1 hne hRij
    -- Bound U1 by rough pairs (choosing the larger of A, B)
    have hU1_bound : (U1.card : ℝ) ≤ (U.card : ℝ) / 4 := by
      have hN0_sq : (8 * C * (M : ℝ)) ^ 2 ≤ (U.card : ℝ) := by
        have h1 : (8 * C * (M : ℝ)) ^ 2 ≤ (Nat.ceil ((8 * C * (M : ℝ)) ^ 2) : ℝ) := Nat.le_ceil _
        have h2 : (Nat.ceil ((8 * C * (M : ℝ)) ^ 2) : ℝ) ≤ (U.card : ℝ) := by
          exact_mod_cast (show Nat.ceil ((8 * C * (M : ℝ)) ^ 2) ≤ U.card by omega)
        linarith
      have hsqrtU : 8 * C * (M : ℝ) ≤ Real.sqrt (U.card : ℝ) := by
        rw [← Real.sqrt_sq (by positivity : 0 ≤ 8 * C * (M : ℝ))]
        exact Real.sqrt_le_sqrt hN0_sq
      have hCMsqrt : (M : ℝ) * C * Real.sqrt (U.card : ℝ) ≤ (U.card : ℝ) / 8 := by
        have hsq : Real.sqrt (U.card : ℝ) * Real.sqrt (U.card : ℝ) = (U.card : ℝ) :=
          Real.mul_self_sqrt (Nat.cast_nonneg _)
        nlinarith [Real.sqrt_nonneg (U.card : ℝ)]
      have hU_le_ABR : (U.card : ℝ) ≤ (A : ℝ) * (B : ℝ) := by exact_mod_cast hU_le_AB
      by_cases hBA : B ≤ A
      · have himg : U1.image (fun i => (roughPart P (a i), roughPart P (b i))) ⊆
            ((Icc 1 A).filter (fun r => ∀ p ∈ P, ¬ p ∣ r)) ×ˢ Icc 1 B := by
          intro q hq
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
          have hiU : i ∈ U := Finset.sdiff_subset (Finset.mem_filter.mp hi).1
          have h := hab i hiU
          refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨mem_Icc.mpr
            ⟨roughPart_pos hP h.1, (roughPart_le _).trans h.2.1⟩,
            fun p hp => not_dvd_roughPart hP h.1 hp⟩,
            mem_Icc.mpr ⟨roughPart_pos hP h.2.2.1, (roughPart_le _).trans h.2.2.2.1⟩⟩
        have hnat : U1.card ≤ ((Icc 1 A).filter (fun r => ∀ p ∈ P, ¬ p ∣ r)).card * B := by
          calc
            U1.card = (U1.image (fun i => (roughPart P (a i), roughPart P (b i)))).card :=
              (Finset.card_image_of_injOn hrough_inj).symm
            _ ≤ (((Icc 1 A).filter (fun r => ∀ p ∈ P, ¬ p ∣ r)) ×ˢ Icc 1 B).card :=
              Finset.card_le_card himg
            _ = ((Icc 1 A).filter (fun r => ∀ p ∈ P, ¬ p ∣ r)).card * B := by
              rw [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel]
        calc
          (U1.card : ℝ) ≤ (((Icc 1 A).filter (fun r => ∀ p ∈ P, ¬ p ∣ r)).card : ℝ) * (B : ℝ) := by
            exact_mod_cast hnat
          _ ≤ (U.card : ℝ) / 4 :=
            rough_prod_bound hP hCpos hdP hU_pos hCMsqrt hA hBA hAB hU_le_ABR
      · have hAB_le : A ≤ B := by omega
        have himg : U1.image (fun i => (roughPart P (a i), roughPart P (b i))) ⊆
            Icc 1 A ×ˢ ((Icc 1 B).filter (fun r => ∀ p ∈ P, ¬ p ∣ r)) := by
          intro q hq
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
          have hiU : i ∈ U := Finset.sdiff_subset (Finset.mem_filter.mp hi).1
          have h := hab i hiU
          refine Finset.mem_product.mpr ⟨mem_Icc.mpr
            ⟨roughPart_pos hP h.1, (roughPart_le _).trans h.2.1⟩,
            Finset.mem_filter.mpr ⟨mem_Icc.mpr
              ⟨roughPart_pos hP h.2.2.1, (roughPart_le _).trans h.2.2.2.1⟩,
              fun p hp => not_dvd_roughPart hP h.2.2.1 hp⟩⟩
        have hnat : U1.card ≤ A * ((Icc 1 B).filter (fun r => ∀ p ∈ P, ¬ p ∣ r)).card := by
          calc
            U1.card = (U1.image (fun i => (roughPart P (a i), roughPart P (b i)))).card :=
              (Finset.card_image_of_injOn hrough_inj).symm
            _ ≤ (Icc 1 A ×ˢ ((Icc 1 B).filter (fun r => ∀ p ∈ P, ¬ p ∣ r))).card :=
              Finset.card_le_card himg
            _ = A * ((Icc 1 B).filter (fun r => ∀ p ∈ P, ¬ p ∣ r)).card := by
              rw [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel]
        calc
          (U1.card : ℝ) ≤ (((Icc 1 B).filter (fun r => ∀ p ∈ P, ¬ p ∣ r)).card : ℝ) * (A : ℝ) := by
            have : (U1.card : ℝ) ≤ (A : ℝ) * (((Icc 1 B).filter (fun r => ∀ p ∈ P, ¬ p ∣ r)).card : ℝ) := by
              exact_mod_cast hnat
            linarith
          _ ≤ (U.card : ℝ) / 4 :=
            rough_prod_bound hP hCpos hdP hU_pos hCMsqrt hB hAB_le (by linarith) (by linarith)
    -- Step D: Combine to get m >= U.card / 4 >= η * U.card
    have hU0_le : (U0.card : ℝ) ≤ (U.card : ℝ) / 2 := by
      have hcast : (U0.card : ℝ) ≤ (UbadA.card : ℝ) + (UbadB.card : ℝ) + (U1.card : ℝ) := by
        exact_mod_cast hU0_split
      linarith
    have hsub_img : Finset.univ.image e ⊆ U := by
      intro x hx
      obtain ⟨⟨p, bp⟩, _, rfl⟩ := Finset.mem_image.mp hx
      cases bp
      · exact (he p).1
      · exact (he p).2.1
    have hcard_img : (Finset.univ.image e).card = 2 * m := by
      rw [Finset.card_image_of_injective _ e.injective, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_bool, mul_comm]
    have hcard_sdiff : U0.card + 2 * m = U.card := by
      rw [← hcard_img]
      exact Finset.card_sdiff_add_card_eq_card hsub_img
    have hη_le : η ≤ 1 / 4 := min_le_left _ _
    have hm_ge : (U.card : ℝ) / 4 ≤ (m : ℝ) := by
      have hcast : (U0.card : ℝ) + 2 * (m : ℝ) = (U.card : ℝ) := by exact_mod_cast hcard_sdiff
      linarith
    nlinarith [hη_le, hm_ge, hU_pos]

end OMA.LonelyRunnerH2

theorem OMA.solution :
    OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1_H1_R1.H2 :=
  OMA.LonelyRunnerH2.main
