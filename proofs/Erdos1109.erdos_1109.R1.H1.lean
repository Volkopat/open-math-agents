import OMAReductions.R_Erdos1109_erdos_1109_R1
import Mathlib

-- Credit: @ptc-prover-bot
/-!
# Erdős 1109, step R1.H1: `f N ≪ N ^ ε` for every `ε > 3 / 4`

The Erdős–Sárközy bound `f N ≪ N ^ (3 / 4) * log N` gives the step, since `log N = o(N ^ δ)`
for every `δ > 0`.

The proof of the Erdős–Sárközy bound below is the merged proof
`proofs/Erdos1109.erdos_1109.variants.erdos_sarkozy_upper.lean` by @MrSeizy (pull request 2469),
copied with its namespace renamed to `OMA.ES1109` because a proof file may only import the
reduction module and Mathlib. For each prime square, discrete orthogonality gives a lower bound
for the energy at its nonzero frequencies. Integration on disjoint short intervals bounds the
combined energy of all frequencies with denominator at most √N.
-/

open Finset MeasureTheory Complex
open scoped Pointwise ComplexConjugate

namespace OMA.ES1109
noncomputable section

private def freq (a : ℕ) : ℂ := a * (2 * Real.pi * I)
private def wave (a : ℕ) (t : ℝ) : ℂ := exp (freq a * t)
private def poly (A : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ a ∈ A, c a * wave a t

-- The sum of the squares of the samples vanishes, since no pair sums to zero modulo p².
private lemma prime_energy (A : Finset ℕ) (hA : ∀ n ∈ A + A, Squarefree n)
    {p : ℕ} (hp : p.Prime) :
    (A.card : ℝ) ^ 2 ≤ ∑ j ∈ (range (p ^ 2)).erase 0,
      ‖poly A (fun _ => 1) ((j : ℝ) / (p ^ 2 : ℕ))‖ ^ 2 := by
  let m := p ^ 2
  have hm : 0 < m := pow_pos hp.pos _
  let z := exp (2 * Real.pi * I / m)
  have hz : IsPrimitiveRoot z m := Complex.isPrimitiveRoot_exp m hm.ne'
  have orth (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A) :
      ∑ j ∈ range m, (z ^ (a + b)) ^ j = 0 := by
    have hbad := Nat.squarefree_iff_prime_squarefree.mp (hA _ (add_mem_add ha hb)) p hp
    have hn : z ^ (a + b) ≠ 1 := fun h => hbad (by simpa [m, pow_two] using (hz.pow_eq_one_iff_dvd _).mp h)
    have h := geom_sum_mul (z ^ (a + b)) m
    rw [← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hn)
  let F (j : ℕ) := poly A (fun _ => 1) ((j : ℝ) / m)
  have hF (j : ℕ) : F j = ∑ a ∈ A, (z ^ a) ^ j := by
    apply sum_congr rfl
    intro a _
    simp only [one_mul, z, ← Complex.exp_nat_mul, wave, freq, ofReal_div, ofReal_natCast]
    congr 1
    ring
  have hsum : ∑ j ∈ range m, F j ^ 2 = 0 := by
    simp_rw [hF, pow_two, sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_eq_zero
    intro a ha
    rw [sum_comm]
    apply sum_eq_zero
    intro b hb
    simpa only [← mul_pow, ← pow_add] using orth a b ha hb
  have h0 : F 0 = A.card := by simp [hF]
  have hs := sum_erase_add (range m) (fun j => F j ^ 2) (mem_range.mpr hm)
  rw [hsum, h0] at hs
  have he := eq_neg_of_add_eq_zero_left hs
  have h := norm_sum_le ((range m).erase 0) (fun j => F j ^ 2)
  rw [he] at h
  simpa [F, m, norm_pow] using h

private lemma wave_cont (a : ℕ) : Continuous (wave a) := by unfold wave; fun_prop
private lemma poly_cont (A : Finset ℕ) (c : ℕ → ℂ) : Continuous (poly A c) := by
  unfold poly
  exact continuous_finsetSum _ fun a _ => continuous_const.mul (wave_cont a)

private lemma poly_deriv (A : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (poly A c) (poly A (fun a => c a * freq a) t) t := by
  unfold poly
  apply HasDerivAt.fun_sum
  intro a ha
  have h := ((Complex.hasDerivAt_exp _).comp (t : ℂ)
    ((hasDerivAt_id (t : ℂ)).const_mul (freq a))).comp_ofReal
  simpa [wave, mul_assoc, mul_comm, mul_left_comm, Function.comp_def] using h.const_mul (c a)

private lemma wave_orth (a b : ℕ) :
    (∫ t in (0 : ℝ)..1, conj (wave a t) * wave b t) = if a = b then 1 else 0 := by
  have h (t : ℝ) : conj (wave a t) * wave b t = exp ((freq b - freq a) * t) := by
    simp only [wave, ← Complex.exp_conj, map_mul, conj_ofReal, ← Complex.exp_add, freq,
      map_natCast, map_ofNat, conj_I]
    congr 1
    ring
  simp_rw [h]
  split_ifs with hab
  · simp [hab]
  · have hn : freq b - freq a ≠ 0 := by
      rw [freq, freq, ← sub_mul]
      exact mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast Ne.symm hab))
        (mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero)
    rw [integral_exp_mul_complex hn]
    simp [Complex.exp_sub, freq, Complex.exp_nat_mul_two_pi_mul_I]

private lemma poly_energy (A : Finset ℕ) (c : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..1, ‖poly A c t‖ ^ 2) = ∑ a ∈ A, ‖c a‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal, Complex.ofReal_sum]
  simp only [Complex.sq_norm, Complex.normSq_eq_conj_mul_self, poly, map_sum, map_mul,
    sum_mul, mul_sum]
  have regroup (a b : ℕ) (t : ℝ) :
      conj (c a) * conj (wave a t) * (c b * wave b t) =
        (conj (c a) * c b) * (conj (wave a t) * wave b t) := by ring
  simp_rw [regroup]
  have hc (a b : ℕ) : Continuous (fun t => (conj (c a) * c b) * (conj (wave a t) * wave b t)) :=
    continuous_const.mul (((Complex.continuous_conj.comp (wave_cont a))).mul (wave_cont b))
  rw [intervalIntegral.integral_finsetSum (fun a _ =>
    (continuous_finsetSum _ fun b _ => hc b a).intervalIntegrable _ _)]
  apply sum_congr rfl
  intro a ha
  rw [intervalIntegral.integral_finsetSum (fun b _ => (hc b a).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_const_mul, wave_orth]
  simp [mul_ite, ha, eq_comm]

-- Bound the value at the left endpoint by integrating the fundamental theorem of calculus.
private lemma sample_one (g v : ℝ → ℝ) (hg : Continuous g) (hv : Continuous v)
    (hder : ∀ x, HasDerivAt g (v x) x) {d : ℝ} (hd : 0 < d) (t : ℝ) :
    d * g t ≤ ∫ x in t..t+d, g x + d * |v x| := by
  let L := ∫ x in t..t+d, |v x|
  have htd : t ≤ t+d := by linarith
  have hbound (x : ℝ) (hx : x ∈ Set.Icc t (t+d)) : g t ≤ g x + L := by
    have h := intervalIntegral.norm_integral_le_integral_norm (f := v) (μ := volume) hx.1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hder y)
      (hv.intervalIntegrable _ _), Real.norm_eq_abs] at h
    have h' := intervalIntegral.integral_mono_interval (f := fun y => |v y|) (μ := volume)
      (le_refl t) hx.1 hx.2 (Filter.Eventually.of_forall fun _ => abs_nonneg _) (hv.abs.intervalIntegrable _ _)
    simp only [Real.norm_eq_abs] at h
    dsimp [L]
    linarith [neg_abs_le (g x - g t)]
  have h := intervalIntegral.integral_mono_on (μ := volume) htd
    (continuous_const.intervalIntegrable _ _) ((hg.add continuous_const).intervalIntegrable _ _) hbound
  change (∫ _ in t..t+d, g t) ≤ ∫ x in t..t+d, g x + L at h
  rw [intervalIntegral.integral_add (hg.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const,
        intervalIntegral.integral_const] at h
  rw [intervalIntegral.integral_add (g := fun x => d * |v x|) (hg.intervalIntegrable _ _)
    ((continuous_const.mul hv.abs).intervalIntegrable _ _), intervalIntegral.integral_const_mul]
  simpa [L] using h

private lemma sample_many {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    {d : ℝ} (hd : 0 < d) (hr : ∀ i ∈ s, 0 ≤ t i ∧ t i + d ≤ 1)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → t i + d ≤ t j ∨ t j + d ≤ t i)
    (g v : ℝ → ℝ) (hg : Continuous g) (hv : Continuous v) (hg0 : ∀ x, 0 ≤ g x)
    (hder : ∀ x, HasDerivAt g (v x) x) :
    d * (∑ i ∈ s, g (t i)) ≤ ∫ x in (0 : ℝ)..1, g x + d * |v x| := by
  let J (i : ι) := Set.Ioc (t i) (t i+d)
  let f (x : ℝ) := g x + d * |v x|
  have hc : Continuous f := hg.add (continuous_const.mul hv.abs)
  have hij : Set.PairwiseDisjoint (↑s) J := by
    intro i hi j hj hne
    rcases hsep i hi j hj hne with h | h
    · exact Set.disjoint_left.mpr fun x hx hy => (not_lt_of_ge (hx.2.trans h)) hy.1
    · exact Set.disjoint_left.mpr fun x hx hy => (not_lt_of_ge (hy.2.trans h)) hx.1
  have hsub : (⋃ i ∈ s, J i) ⊆ Set.Ioc 0 1 := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨(hr i hi).1.trans_lt hx.1, hx.2.trans (hr i hi).2⟩
  rw [mul_sum, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  calc
    _ ≤ ∑ i ∈ s, ∫ x in J i, f x := by
      apply sum_le_sum
      intro i _
      simpa only [intervalIntegral.integral_of_le (show t i ≤ t i + d by linarith), f, J]
        using sample_one g v hg hv hder hd (t i)
    _ = _ := (integral_biUnion_finset s (fun _ _ => measurableSet_Ioc) hij
        (fun _ _ => hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)).symm
    _ ≤ _ := by
      apply setIntegral_mono_set (hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        (Filter.Eventually.of_forall fun x => add_nonneg (hg0 x) (mul_nonneg hd.le (abs_nonneg _)))
      exact Filter.Eventually.of_forall hsub

private def samples (Q : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  Q.primesLE.sigma fun p => (range (p^2)).erase 0
private def node (u : Σ _ : ℕ, ℕ) : ℝ := (u.2 : ℝ) / (u.1 ^ 2 : ℕ)

private lemma frac_gap {a b m n N : ℕ} (hm : 0 < m) (hn : 0 < n) (h : a*n < b*m)
    (hN : m*n ≤ N) :
    (a : ℝ) / m + 1 / N ≤ (b : ℝ) / n := by
  have hp : (0 : ℝ) < (m : ℝ) * n := by positivity
  have hle : (m : ℝ) * n ≤ N := by exact_mod_cast hN
  calc
    _ ≤ (a : ℝ) / m + 1 / ((m : ℝ)*n) := by
      gcongr
    _ ≤ _ := by
      have h' : (a : ℝ)*n + 1 ≤ (b : ℝ)*m := by exact_mod_cast h
      have hm' : (0:ℝ) < m := by exact_mod_cast hm
      have hn' : (0:ℝ) < n := by exact_mod_cast hn
      field_simp
      nlinarith

private lemma node_range {Q N : ℕ} (hN : Q^4 ≤ N) :
    ∀ u ∈ samples Q, 0 ≤ node u ∧ node u + 1 / N ≤ 1 := by
  rintro ⟨p,j⟩ hu
  obtain ⟨hp, hj⟩ := mem_sigma.mp hu
  obtain ⟨hpQ, hpr⟩ := Nat.mem_primesLE.mp hp
  have hjp := mem_range.mp (mem_of_mem_erase hj)
  have hpp : p^2 ≤ Q^2 := Nat.pow_le_pow_left hpQ 2
  have hq : Q^2 ≤ Q^4 := Nat.pow_le_pow_right (by have := hpr.pos; omega) (by decide)
  constructor
  · dsimp [node]; positivity
  · simpa [node] using frac_gap (a := j) (b := 1) (n := 1) (pow_pos hpr.pos 2)
      (by decide) (by simpa using hjp) (by simpa using hpp.trans (hq.trans hN))

private lemma node_sep {Q N : ℕ} (hN : Q^4 ≤ N) :
    ∀ u ∈ samples Q, ∀ v ∈ samples Q, u ≠ v →
      node u + 1 / N ≤ node v ∨ node v + 1 / N ≤ node u := by
  rintro ⟨p,j⟩ hu ⟨q,k⟩ hv hne
  obtain ⟨hpp,hj⟩ := mem_sigma.mp hu
  obtain ⟨hqq,hk⟩ := mem_sigma.mp hv
  obtain ⟨hpQ,hp⟩ := Nat.mem_primesLE.mp hpp
  obtain ⟨hqQ,hq⟩ := Nat.mem_primesLE.mp hqq
  have hm : p^2*q^2 ≤ N := calc
    _ ≤ Q^2*Q^2 := Nat.mul_le_mul (Nat.pow_le_pow_left hpQ _) (Nat.pow_le_pow_left hqQ _)
    _ = Q^4 := by ring
    _ ≤ N := hN
  rcases lt_trichotomy (j*q^2) (k*p^2) with h | h | h
  · exact Or.inl (frac_gap (pow_pos hp.pos _) (pow_pos hq.pos _) h hm)
  · exfalso
    by_cases he : p = q
    · subst q
      have hjk := Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) h
      exact hne (by cases hjk; rfl)
    · have hcop := ((Nat.coprime_primes hp hq).mpr he).pow 2 2
      have hd : p^2 ∣ j*q^2 := h.symm ▸ dvd_mul_left _ _
      have hdiv : p^2 ∣ j := hcop.dvd_of_dvd_mul_right hd
      exact (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero (ne_of_mem_erase hj))
        (mem_range.mp (mem_of_mem_erase hj))) hdiv
  · exact Or.inr (frac_gap (pow_pos hq.pos _) (pow_pos hp.pos _) h (by rwa [mul_comm]))

private lemma finite_sieve (A : Finset ℕ) {Q N : ℕ} (hN : Q^4 ≤ N) (hpos : 0 < N)
    (hA : A ⊆ Icc 1 N) (hsq : ∀ n ∈ A + A, Squarefree n) :
    (Q.primeCounting : ℝ) * A.card ≤ (2 + (2 * Real.pi)^2) * N := by
  let d : ℝ := 1 / N
  have hn : (0 : ℝ) < N := by exact_mod_cast hpos
  have hd : 0 < d := by dsimp [d]; positivity
  let S := poly A (fun _ => 1)
  let D := poly A freq
  let g (x : ℝ) := ‖S x‖ ^ 2
  let v (x : ℝ) := 2 * inner ℝ (S x) (D x)
  have hSc : Continuous S := poly_cont _ _
  have hDc : Continuous D := poly_cont _ _
  have hg : Continuous g := hSc.norm.pow _
  have hv : Continuous v := continuous_const.mul (hSc.inner hDc)
  have hder (x : ℝ) : HasDerivAt g (v x) x := by
    apply HasDerivAt.norm_sq
    simpa only [one_mul] using poly_deriv A (fun _ => 1) x
  have hsample := sample_many (samples Q) node hd (node_range hN) (node_sep hN)
    g v hg hv (fun _ => sq_nonneg _) hder
  have hpoint (x : ℝ) : g x + d * |v x| ≤ 2 * g x + d^2 * ‖D x‖ ^ 2 := by
    have h := abs_real_inner_le_norm (S x) (D x)
    dsimp only [g,v]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith [mul_le_mul_of_nonneg_left h hd.le, sq_nonneg (‖S x‖ - d * ‖D x‖)]
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (a := 0) (b := 1) zero_le_one
    (f := fun x => g x + d * |v x|) (g := fun x => 2 * g x + d^2 * ‖D x‖ ^ 2)
    ((hg.add (continuous_const.mul hv.abs)).intervalIntegrable _ _)
    (((continuous_const.mul hg).add (continuous_const.mul (hDc.norm.pow _))).intervalIntegrable _ _)
    (fun x _ => hpoint x)
  have hup := hsample.trans hmono
  rw [intervalIntegral.integral_add (f := fun x => 2*g x) (g := fun x => d^2*‖D x‖^2)
    ((continuous_const.mul hg).intervalIntegrable _ _)
    ((continuous_const.mul (hDc.norm.pow _)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hup
  have hgint : (∫ x in (0:ℝ)..1, g x) = A.card := by simpa [g,S] using poly_energy A (fun _ => 1)
  rw [hgint, show (∫ x in (0:ℝ)..1, ‖D x‖^2) = _ from poly_energy A freq] at hup
  have hD : d^2 * (∑ a ∈ A, ‖freq a‖^2) ≤ (A.card : ℝ) * (2 * Real.pi)^2 := by
    rw [mul_sum, ← nsmul_eq_mul, ← sum_const]
    apply sum_le_sum
    intro a ha
    have haN : (a : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp (hA ha)).2
    have hnorm : ‖freq a‖ = (a : ℝ) * (2 * Real.pi) := by simp [freq, abs_of_pos Real.pi_pos]
    rw [hnorm, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    dsimp [d]
    calc
      _ ≤ 1 / (N : ℝ) * (N * (2 * Real.pi)) := by gcongr
      _ = _ := by field_simp
  have hlo : (Q.primeCounting : ℝ) * (A.card : ℝ)^2 ≤ ∑ u ∈ samples Q, g (node u) := by
    rw [← Nat.primesLE_card_eq_primeCounting, ← nsmul_eq_mul, ← sum_const, samples, sum_sigma]
    exact sum_le_sum fun p hp => prime_energy A hsq (Nat.prime_of_mem_primesLE hp)
  have hall := (mul_le_mul_of_nonneg_left hlo hd.le).trans hup
  have hk : (Q.primeCounting : ℝ) * (A.card : ℝ)^2 ≤
      ((2 + (2 * Real.pi)^2) * A.card) * N := by
    apply (div_le_iff₀ hn).mp
    simp only [d, one_div] at hall hD
    rw [div_eq_inv_mul]
    nlinarith only [hall, hD]
  rcases eq_or_lt_of_le (Nat.zero_le A.card) with he | he
  · rw [← he]
    simp
    positivity
  · apply (mul_le_mul_iff_left₀ (show (0:ℝ) < A.card by exact_mod_cast he)).mp
    nlinarith only [hk]

end
end OMA.ES1109

private lemma counting_lower {x : ℝ} (hx : 100 ≤ x) :
    x / 4 ≤ (⌊x⌋₊.primeCounting : ℝ) * Real.log x := by
  have hx1 : 1 < x := by linarith
  have h := (div_le_iff₀ (Real.log_pos hx1)).mp (Chebyshev.pi_ge' hx1)
  have hlog := Real.log_le_sub_one_of_pos (x := (x+2)/4) (by positivity)
  rw [Real.log_div (by positivity) (by norm_num),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hlog
  have h1 : (0.6:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hx1.le), Real.log_two_lt_d9]

-- The cardinality bound for the supremum also appears in the lower-bound sibling by @senamakel.
private lemma attained (N : ℕ) : ∃ A : Finset ℕ,
    A ⊆ Icc 1 N ∧ (∀ n ∈ A + A, Squarefree n) ∧ A.card = Erdos1109.f N := by
  unfold Erdos1109.f
  apply Nat.sSup_mem (s := {k : ℕ | ∃ A : Finset ℕ,
    A ⊆ Icc 1 N ∧ (∀ n ∈ A + A, Squarefree n) ∧ A.card = k})
  · exact ⟨0, ∅, empty_subset _, by simp, rfl⟩
  · refine ⟨N, ?_⟩
    rintro k ⟨A, hA, -, rfl⟩
    simpa using card_le_card hA

-- Credit: @MrSeizy
theorem OMA.ES1109.sarkozy_upper :
    type_of% @Erdos1109.erdos_1109.variants.erdos_sarkozy_upper := by
  let C : ℝ := 2 + (2 * Real.pi)^2
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [Filter.eventually_ge_atTop (100^4 : ℕ)] with N hN
  have hn : 0 < N := by omega
  have hn' : 0 < (N : ℝ) := by exact_mod_cast hn
  let x := (N : ℝ) ^ ((4 : ℝ)⁻¹)
  have hx0 : 0 < x := Real.rpow_pos_of_pos hn' _
  have hx4 : x^4 = N := Real.rpow_inv_natCast_pow hn'.le (by decide : (4:ℕ) ≠ 0)
  have hx : 100 ≤ x := by
    have h : (100:ℝ)^4 ≤ x^4 := by rw [hx4]; exact_mod_cast hN
    exact le_of_pow_le_pow_left₀ (by decide : (4:ℕ) ≠ 0) hx0.le h
  have hf : ⌊x⌋₊ ^ 4 ≤ N := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg ⌊x⌋₊ : (0:ℝ) ≤ _) (Nat.floor_le hx0.le) 4
    rw [hx4] at h
    exact_mod_cast h
  have hl := counting_lower hx
  rw [show Real.log x = (4:ℝ)⁻¹ * Real.log N from Real.log_rpow hn' _] at hl
  have hcount : x ≤ (⌊x⌋₊.primeCounting : ℝ) * Real.log N := by linarith
  obtain ⟨A, hA, hsq, hcard⟩ := attained N
  have hs : (⌊x⌋₊.primeCounting : ℝ) * A.card ≤ C * N := OMA.ES1109.finite_sieve A hf hn hA hsq
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hprod : (N : ℝ)^((3:ℝ)/4) * x = N := by
    rw [show x = (N : ℝ)^((4:ℝ)⁻¹) from rfl, ← Real.rpow_add hn']
    norm_num
  simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (Erdos1109.f N) : (0:ℝ) ≤ _),
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hlog)]
  rw [← hcard]
  apply (mul_le_mul_iff_right₀ hx0).mp
  calc
    x * (A.card : ℝ) ≤ ((⌊x⌋₊.primeCounting : ℝ) * Real.log N) * A.card := by gcongr
    _ = ((⌊x⌋₊.primeCounting : ℝ) * A.card) * Real.log N := by ring
    _ ≤ (C * N) * Real.log N := mul_le_mul_of_nonneg_right hs hlog
    _ = x * (C * ((N : ℝ)^((3:ℝ)/4) * Real.log N)) := by
      linear_combination -(C * Real.log N) * hprod

/-- The step: `log N = o(N ^ (ε - 3 / 4))` turns the Erdős–Sárközy bound into `f N ≪ N ^ ε`. -/
theorem OMA.solution : OMA.R_Erdos1109_erdos_1109_R1.H1 := by
  intro ε hε
  have hup : (fun N : ℕ => (Erdos1109.f N : ℝ)) =O[Filter.atTop]
      fun N : ℕ => (N : ℝ) ^ ((3 : ℝ) / 4) * Real.log N := OMA.ES1109.sarkozy_upper
  have hlog : (fun N : ℕ => Real.log N) =O[Filter.atTop] fun N : ℕ => (N : ℝ) ^ (ε - 3 / 4) :=
    ((isLittleO_log_rpow_atTop (by linarith)).comp_tendsto tendsto_natCast_atTop_atTop).isBigO
  have hmul := (Asymptotics.isBigO_refl (fun N : ℕ => (N : ℝ) ^ ((3 : ℝ) / 4))
    Filter.atTop).mul hlog
  have hfin : (fun N : ℕ => (N : ℝ) ^ ((3 : ℝ) / 4) * Real.log N) =O[Filter.atTop]
      fun N : ℕ => (N : ℝ) ^ ε := by
    refine hmul.congr' Filter.EventuallyEq.rfl ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [← Real.rpow_add hN']
    congr 1
    ring
  exact hup.trans hfin

