import FormalConjectures.ErdosProblems.«1106»
import Mathlib

/-!
# Infinitely many prime divisors of partition numbers

The arithmetic argument counts products of nearby partition numbers around
square indices. Their logarithmic forward differences at successive orders
are separated, which makes those products distinct. A fixed finite set of
primes cannot support the resulting number of products.

To establish the forward difference estimates, the partition generating
function is integrated on a circle through its real saddle. The eta
inversion formula supplies a holomorphic approximation on the central arc.
The remaining arc, and the reflected Euler product on the central arc, both
contribute exponentially small relative errors. Cauchy's derivative bounds
then transfer the square-root leading term to every fixed difference order.
-/

section

open Nat Finset Filter

namespace Erdos1106Work

def prefixPrimes (f : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  (∏ i ∈ Icc 1 n, f i).primeFactors

theorem partitionNumber_pos (n : ℕ) : 0 < partitionNumber n :=
  Fintype.card_pos

theorem partitionNumber_le (n : ℕ) : partitionNumber n ≤ 2 ^ (n - 1) := by
  rw [← composition_card n]
  exact Fintype.card_le_of_surjective _ Partition.ofComposition_surj

theorem prefixPrimes_mono {f : ℕ → ℕ} (hf : ∀ i, f i ≠ 0) :
    Monotone (prefixPrimes f) := by
  intro m n h
  apply Nat.primeFactors_mono
  · apply Finset.prod_dvd_prod_of_subset
    intro i hi
    exact mem_Icc.mpr ⟨(mem_Icc.mp hi).1, (mem_Icc.mp hi).2.trans h⟩
  · exact prod_ne_zero_iff.mpr fun i _ ↦ hf i

theorem mem_prefixPrimes {f : ℕ → ℕ} (hf : ∀ i, f i ≠ 0) {n q : ℕ} :
    q ∈ prefixPrimes f n ↔ q.Prime ∧ ∃ i ∈ Icc 1 n, q ∣ f i := by
  have hprod : (∏ i ∈ Icc 1 n, f i) ≠ 0 := prod_ne_zero_iff.mpr fun i _ ↦ hf i
  rw [prefixPrimes, mem_primeFactors_of_ne_zero hprod]
  exact and_congr_right fun hq ↦ hq.prime.dvd_finsetProd_iff f

/-- Divergence of the prefix count is equivalent to arbitrarily large prime divisors
among the individual positive-index values. -/
theorem tendsto_prefixPrimes_iff {f : ℕ → ℕ} (hf : ∀ i, f i ≠ 0) :
    Tendsto (fun n ↦ (prefixPrimes f n).card) atTop atTop ↔
      ∀ b : ℕ, ∃ q i : ℕ, b < q ∧ q.Prime ∧ 1 ≤ i ∧ q ∣ f i := by
  constructor
  · intro h b
    obtain ⟨n, hn⟩ := eventually_atTop.mp (tendsto_atTop.1 h (b + 2))
    have hlarge := hn n le_rfl
    have hnot : ¬ prefixPrimes f n ⊆ range (b + 1) := by
      intro hs
      have hc := card_le_card hs
      rw [card_range] at hc
      omega
    obtain ⟨q, hq, hqb⟩ := Finset.not_subset.mp hnot
    obtain ⟨hp, i, hi, hd⟩ := (mem_prefixPrimes hf).mp hq
    exact ⟨q, i, by simpa [mem_range] using hqb, hp, (mem_Icc.mp hi).1, hd⟩
  · intro h
    have hmono := prefixPrimes_mono hf
    have hunb : ∀ k : ℕ, ∃ n, k ≤ (prefixPrimes f n).card := by
      intro k
      induction k with
      | zero => exact ⟨0, Nat.zero_le _⟩
      | succ k ih =>
        obtain ⟨n, hn⟩ := ih
        obtain ⟨q, i, hq, hp, hi, hd⟩ := h ((prefixPrimes f n).sup id)
        have hnew : q ∉ prefixPrimes f n := fun hmem ↦
          (not_lt_of_ge (Finset.le_sup (f := id) hmem)) hq
        have hin : q ∈ prefixPrimes f (max n i) :=
          (mem_prefixPrimes hf).2 ⟨hp, i, mem_Icc.mpr ⟨hi, le_max_right _ _⟩, hd⟩
        have hsub : insert q (prefixPrimes f n) ⊆ prefixPrimes f (max n i) :=
          insert_subset hin (hmono (le_max_left _ _))
        have hc := card_le_card hsub
        rw [card_insert_of_notMem hnew] at hc
        exact ⟨max n i, by omega⟩
    apply tendsto_atTop.2
    intro k
    obtain ⟨n, hn⟩ := hunb k
    exact eventually_atTop.mpr ⟨n, fun m hm ↦ hn.trans (card_le_card (hmono hm))⟩

/-- Products formed with small exponents from a short window of consecutive values. -/
def windowProduct (f : ℕ → ℕ) (k m : ℕ) (a : Fin k → Fin m) : ℕ :=
  ∏ j, f (m ^ 2 + j.val) ^ (a j).val

private theorem windowProduct_pos {f : ℕ → ℕ} (hf : ∀ i, 0 < f i)
    {k m : ℕ} (a : Fin k → Fin m) : 0 < windowProduct f k m a :=
  Finset.prod_pos fun _ _ ↦ pow_pos (hf _) _

private theorem windowProduct_bound {f : ℕ → ℕ} (hg : ∀ i, f i ≤ 2 ^ i)
    {k m : ℕ} (a : Fin k → Fin m) :
    windowProduct f k m a ≤ 2 ^ (k * m * (m ^ 2 + k)) := by
  calc
    _ ≤ ∏ _j : Fin k, 2 ^ (m * (m ^ 2 + k)) := by
      apply Finset.prod_le_prod
      · exact fun _ _ ↦ Nat.zero_le _
      · intro j _
        calc
          _ ≤ (2 ^ (m ^ 2 + j.val)) ^ (a j).val := Nat.pow_le_pow_left (hg _) _
          _ = 2 ^ ((m ^ 2 + j.val) * (a j).val) := (pow_mul ..).symm
          _ ≤ 2 ^ (m * (m ^ 2 + k)) := by
            apply Nat.pow_le_pow_right (by decide)
            rw [Nat.mul_comm m]
            exact Nat.mul_le_mul (by omega) (a j).isLt.le
    _ = _ := by simp [← pow_mul, Nat.mul_comm, Nat.mul_assoc]

/-- If all the window terms are supported on primes at most b, injectivity of the
window products forces the size of the digit box below the size of the valuation box. -/
theorem window_count_bound {f : ℕ → ℕ} (hf : ∀ i, 0 < f i) (hg : ∀ i, f i ≤ 2 ^ i)
    {k m b : ℕ}
    (hs : ∀ q i : ℕ, q.Prime → q ∣ f (m ^ 2 + i) → q ≤ b)
    (hi : Function.Injective (windowProduct f k m)) :
    m ^ k ≤ (k * m * (m ^ 2 + k) + 1) ^ (b + 1) := by
  classical
  let d := k * m * (m ^ 2 + k)
  let value := windowProduct f k m
  have hexp (a : Fin k → Fin m) (q : ℕ) : (value a).factorization q ≤ d := by
    by_cases hp : q.Prime
    · apply Nat.factorization_le_of_le_pow
      exact (windowProduct_bound hg a).trans (Nat.pow_le_pow_left hp.two_le d)
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  let code (a : Fin k → Fin m) (q : Fin (b + 1)) : Fin (d + 1) :=
    ⟨(value a).factorization q.val, Nat.lt_succ_of_le (hexp a q.val)⟩
  have hout (a : Fin k → Fin m) (q : ℕ) (hq : b < q) : (value a).factorization q = 0 := by
    by_cases hp : q.Prime
    · apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      obtain ⟨j, _, hj⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
      exact (not_lt_of_ge (hs q j.val hp (hp.dvd_of_dvd_pow hj))) hq
    · exact Nat.factorization_eq_zero_of_not_prime _ hp
  have hinj : Function.Injective code := by
    intro a a' h
    apply hi
    apply Nat.eq_of_factorization_eq (windowProduct_pos hf a).ne' (windowProduct_pos hf a').ne'
    intro q
    by_cases hq : q ≤ b
    · exact congrArg Fin.val (congrFun h ⟨q, Nat.lt_succ_of_le hq⟩)
    · rw [show (windowProduct f k m a).factorization q = 0 from hout a q (by omega),
          show (windowProduct f k m a').factorization q = 0 from hout a' q (by omega)]
  simpa [d] using Fintype.card_le_of_injective code hinj

/-- A reduction using only finite arithmetic on the target side. The remaining
window injectivity is the analytic step, obtainable from high-order finite
differences of the logarithm of the partition function. -/
theorem of_window_injectivity
    (hw : ∀ k, ∀ᶠ m : ℕ in atTop, Function.Injective (windowProduct partitionNumber k m)) :
    type_of% @Erdos1106.erdos_1106.parts.i := by
  apply (tendsto_prefixPrimes_iff fun i ↦ (partitionNumber_pos i).ne').2
  intro b
  by_contra! h
  let r := b + 1
  let k := 3 * r + 1
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp (hw k)
  let m := max (max m₀ k) ((2 * k + 1) ^ r) + 1
  have h0 : m₀ ≤ m := by dsimp [m]; omega
  have hk : k ≤ m := by dsimp [m]; omega
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hC : (2 * k + 1) ^ r < m := by dsimp [m]; omega
  have hs (q i : ℕ) (hp : q.Prime) (hd : q ∣ partitionNumber (m ^ 2 + i)) : q ≤ b := by
    by_contra! hq
    exact h q (m ^ 2 + i) hq hp (by nlinarith) hd
  have hg (i : ℕ) : partitionNumber i ≤ 2 ^ i :=
    (partitionNumber_le i).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hcount := window_count_bound partitionNumber_pos hg hs (hm₀ m h0)
  have hsq : k ≤ m ^ 2 := hk.trans (by nlinarith)
  have hfirst :
      k * m * (m ^ 2 + k) + 1 ≤ (2 * k + 1) * m ^ 3 := by
    have hh := Nat.mul_le_mul_left (k * m) hsq
    have hcube : 1 ≤ m ^ 3 := Nat.one_le_pow _ _ hm
    nlinarith only [hh, hcube]
  have hlt : ((2 * k + 1) * m ^ 3) ^ r < m ^ k := by
    calc
      _ = (2 * k + 1) ^ r * m ^ (3 * r) := by rw [mul_pow, pow_mul]
      _ < m * m ^ (3 * r) := Nat.mul_lt_mul_of_pos_right hC (pow_pos hm _)
      _ = m ^ k := by change _ = m ^ (3 * r + 1); rw [pow_succ, mul_comm]
  exact (not_lt_of_ge (hcount.trans (Nat.pow_le_pow_left hfirst r))) hlt

private def binomialMoment {k : ℕ} (c : Fin k → ℤ) (t : Fin k) : ℤ :=
  ∑ j, c j * (j.val.choose t.val : ℤ)

private theorem exists_ne_zero_moment {k : ℕ} {c : Fin k → ℤ}
    (hc : ∃ j, c j ≠ 0) : ∃ t, binomialMoment c t ≠ 0 := by
  classical
  let s := univ.filter (fun j ↦ c j ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨j, hj⟩ := hc
    exact ⟨j, mem_filter.mpr ⟨mem_univ _, hj⟩⟩
  let t := s.max' hs
  have ht : t ∈ s := max'_mem _ _
  refine ⟨t, ?_⟩
  have hw : binomialMoment c t = c t := by
    unfold binomialMoment
    rw [Finset.sum_eq_single t]
    · simp
    · intro j _ hj
      by_cases hj' : j < t
      · simp [Nat.choose_eq_zero_of_lt hj']
      · have hjt : t < j := lt_of_le_of_ne (le_of_not_gt hj') hj.symm
        have hj0 : c j = 0 := by
          by_contra hneq
          have hjmem : j ∈ s := by simp [s, hneq]
          exact (not_lt_of_ge (Finset.le_max' s j hjmem)) hjt
        simp [hj0]
    · simp
  rw [hw]
  simpa [s] using ht

private theorem binomialMoment_bound {k m : ℕ} {c : Fin k → ℤ}
    (hc : ∀ j, |c j| ≤ (m : ℤ)) (t : Fin k) :
    |binomialMoment c t| ≤ (k * 2 ^ k * m : ℕ) := by
  calc
    _ ≤ ∑ j : Fin k, |c j * (j.val.choose t.val : ℤ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin k, (m : ℤ) * 2 ^ k := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (j.val.choose t.val : ℤ))]
      have hjc : j.val.choose t.val ≤ 2 ^ k :=
        (Nat.choose_le_two_pow ..).trans (Nat.pow_le_pow_right (by decide) j.isLt.le)
      exact mul_le_mul (hc _) (by exact_mod_cast hjc) (by positivity) (by positivity)
    _ = _ := by simp; ring

private theorem separated_sum_ne_zero {k C : ℕ} {w : Fin k → ℤ} {d : Fin k → ℝ}
    (hw : ∃ t, w t ≠ 0) (hbound : ∀ t, |w t| ≤ (C : ℤ))
    (hsep : ∀ t, (C : ℝ) * ∑ j ∈ univ.filter (t < ·), |d j| < |d t|) :
    (∑ t, (w t : ℝ) * d t) ≠ 0 := by
  classical
  let s := univ.filter fun t ↦ w t ≠ 0
  have hs : s.Nonempty := by
    obtain ⟨j, hj⟩ := hw
    exact ⟨j, mem_filter.mpr ⟨mem_univ _, hj⟩⟩
  let t := s.min' hs
  have ht : w t ≠ 0 := by have := Finset.min'_mem s hs; simpa [t, s] using this
  let tail := univ.filter (t < ·)
  have hnin : t ∉ tail := by simp [tail]
  have hsum : ∑ j, (w j : ℝ) * d j =
      (w t : ℝ) * d t + ∑ j ∈ tail, (w j : ℝ) * d j := by
    rw [← Finset.sum_insert (f := fun j ↦ (w j : ℝ) * d j) hnin]
    symm
    apply Fintype.sum_subset
    intro j hj
    have hjw : w j ≠ 0 := fun hz ↦ hj (by simp [hz])
    have hle : t ≤ j := Finset.min'_le s j (by simp [s, hjw])
    rcases eq_or_lt_of_le hle with he | hl
    · simp [he]
    · exact mem_insert_of_mem (by simp [tail, hl])
  intro hz
  rw [hsum] at hz
  have he : (w t : ℝ) * d t = -(∑ j ∈ tail, (w j : ℝ) * d j) := by linarith
  have htone : (1 : ℝ) ≤ |(w t : ℝ)| := by
    have hwone : (1 : ℤ) ≤ |w t| := by have := abs_pos.mpr ht; omega
    exact_mod_cast hwone
  have hle : |d t| ≤ (C : ℝ) * ∑ j ∈ tail, |d j| := by
    calc
      |d t| ≤ |(w t : ℝ)| * |d t| := le_mul_of_one_le_left (abs_nonneg _) htone
      _ = |∑ j ∈ tail, (w j : ℝ) * d j| := by rw [← abs_mul, he, abs_neg]
      _ ≤ ∑ j ∈ tail, |(w j : ℝ) * d j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ (C : ℝ) * ∑ j ∈ tail, |d j| := by
        rw [Finset.mul_sum]
        apply sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hbound j) (abs_nonneg _)
  exact (not_lt_of_ge hle) (hsep t)

private theorem log_windowProduct {f : ℕ → ℕ} (hf : ∀ n, 0 < f n) {k m : ℕ}
    (a : Fin k → Fin m) :
    Real.log (windowProduct f k m a : ℝ) =
      ∑ j, ((a j).val : ℝ) * Real.log (f (m ^ 2 + j.val) : ℝ) := by
  rw [windowProduct, Nat.cast_prod, Real.log_prod]
  · simp [Real.log_pow]
  · intro j _
    have := hf (m ^ 2 + j.val)
    positivity

/-- A dominance inequality on the Newton coefficients makes every product
with exponents below m distinct. -/
theorem window_injective_of_separated_newton {f : ℕ → ℕ} (hf : ∀ n, 0 < f n)
    {k m : ℕ} (d : Fin k → ℝ)
    (hnew : ∀ j : Fin k, Real.log (f (m ^ 2 + j.val) : ℝ) =
      ∑ t : Fin k, (j.val.choose t.val : ℝ) * d t)
    (hsep : ∀ t : Fin k, (k * 2 ^ k * m : ℕ) * ∑ j ∈ univ.filter (t < ·), |d j| < |d t|) :
    Function.Injective (windowProduct f k m) := by
  intro a b h
  by_contra hne
  let c (j : Fin k) : ℤ := (a j).val - (b j).val
  have hc : ∃ j, c j ≠ 0 := by
    by_contra! hc0
    apply hne
    funext j
    apply Fin.ext
    have hh := hc0 j
    dsimp [c] at hh
    omega
  have hcb (j : Fin k) : |c j| ≤ (m : ℤ) := by
    have ha := (a j).isLt
    have hb := (b j).isLt
    dsimp [c]
    exact abs_le.mpr ⟨by omega, by omega⟩
  apply separated_sum_ne_zero (exists_ne_zero_moment hc)
    (binomialMoment_bound hcb) hsep
  have hlog := congrArg (fun n : ℕ ↦ Real.log (n : ℝ)) h
  change Real.log (windowProduct f k m a : ℝ) = Real.log (windowProduct f k m b : ℝ) at hlog
  rw [log_windowProduct hf, log_windowProduct hf] at hlog
  calc
    _ = ∑ j : Fin k, (c j : ℝ) * (∑ t : Fin k, (j.val.choose t.val : ℝ) * d t) := by
      simp only [binomialMoment, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
        Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
    _ = ∑ j : Fin k, (c j : ℝ) * Real.log (f (m ^ 2 + j.val) : ℝ) := by simp_rw [← hnew]
    _ = 0 := by simpa [c, sub_mul, Finset.sum_sub_distrib] using sub_eq_zero.mpr hlog

/-- The r-th forward difference of the logarithm of the partition function. -/
noncomputable def partitionLogDiff (r n : ℕ) : ℝ :=
  ((fwdDiff 1)^[r] (fun j : ℕ ↦ Real.log (partitionNumber j : ℝ))) n

/-- It suffices to show that fixed higher-order logarithmic differences are smaller
than a fixed lower-order difference by a factor that dominates the square root
of the index. This hypothesis concerns only the sizes of real finite differences. -/
theorem of_log_difference_separation
    (h : ∀ k : ℕ, ∀ᶠ m : ℕ in atTop, ∀ t : Fin k,
      (k * 2 ^ k * m : ℕ) * ∑ j ∈ univ.filter (t < ·), |partitionLogDiff j.val (m ^ 2)|
        < |partitionLogDiff t.val (m ^ 2)|) :
    type_of% @Erdos1106.erdos_1106.parts.i := by
  apply of_window_injectivity
  intro k
  filter_upwards [h k] with m hm
  apply window_injective_of_separated_newton partitionNumber_pos (fun t ↦ partitionLogDiff t.val (m ^ 2)) _ hm
  intro j
  let g (n : ℕ) := Real.log (partitionNumber n : ℝ)
  have hNewton := shift_eq_sum_fwdDiff_iter 1 g j.val (m ^ 2)
  calc
    _ = ∑ i ∈ range (j.val + 1), (j.val.choose i : ℝ) * partitionLogDiff i (m ^ 2) := by
      simpa [g, partitionLogDiff, nsmul_eq_mul] using hNewton
    _ = ∑ i ∈ range k, (j.val.choose i : ℝ) * partitionLogDiff i (m ^ 2) := by
      apply Finset.sum_subset (Finset.range_mono j.isLt)
      intro i _ hi
      have hji : j.val < i := by simpa [mem_range] using hi
      simp [Nat.choose_eq_zero_of_lt hji]
    _ = _ := (Fin.sum_univ_eq_sum_range (fun i ↦ (j.val.choose i : ℝ) * partitionLogDiff i (m ^ 2)) k).symm


/-- Two-sided order estimates at square indices, written without fractional exponents.
For fixed r these say that the absolute r-th difference has order m^(1-2r). -/
def SquareDifferenceBounds : Prop :=
  ∀ r : ℕ, ∃ A B : ℝ, 0 < A ∧ ∀ᶠ m : ℕ in atTop,
    A * m ≤ (m : ℝ) ^ (2 * r) * |partitionLogDiff r (m ^ 2)| ∧
    (m : ℝ) ^ (2 * r) * |partitionLogDiff r (m ^ 2)| ≤ B * m

private theorem eventually_separated_pair (h : SquareDifferenceBounds)
    {a b : ℕ} (hab : a < b) (C : ℕ) :
    ∀ᶠ m : ℕ in atTop, (C : ℝ) * m * |partitionLogDiff b (m ^ 2)| <
      |partitionLogDiff a (m ^ 2)| := by
  obtain ⟨A, _, hA, ha⟩ := h a
  obtain ⟨_, B, _, hb⟩ := h b
  obtain ⟨N, hN⟩ := exists_nat_gt ((C : ℝ) * B / A)
  filter_upwards [ha, hb, eventually_ge_atTop (max N 1)] with m hmA hmB hm
  have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast (le_max_right N 1).trans hm
  have hmpos : 0 < (m : ℝ) := by linarith
  have hNA : (C : ℝ) * B < m * A := (div_lt_iff₀ hA).mp
    (hN.trans_le (by exact_mod_cast (le_max_left N 1).trans hm))
  have hpow : (m : ℝ) ^ (2 * a) * m ^ (2 : ℕ) ≤ (m : ℝ) ^ (2 * b) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hm1 (by omega)
  have hscaled := (mul_le_mul_of_nonneg_right hpow (abs_nonneg _)).trans hmB.2
  by_contra! hfail
  have h0 := mul_le_mul_of_nonneg_left hfail (pow_nonneg hmpos.le (2*a))
  have h1 := mul_le_mul_of_nonneg_right (hmA.1.trans h0) hmpos.le
  have h2 := mul_le_mul_of_nonneg_left hscaled (show 0 ≤ (C : ℝ) by positivity)
  have h3 := mul_lt_mul_of_pos_right hNA hmpos
  nlinarith only [h1, h2, h3]

/-- The entire prime-factor conclusion follows from fixed-order estimates for
the forward differences of log p. -/
theorem of_square_difference_bounds (h : SquareDifferenceBounds) :
    type_of% @Erdos1106.erdos_1106.parts.i := by
  apply of_log_difference_separation
  intro k
  let C := (k + 1) * k * 2 ^ k
  have hpos (t : Fin k) : ∀ᶠ m : ℕ in atTop, 0 < |partitionLogDiff t.val (m ^ 2)| := by
    obtain ⟨A, B, hA, ht⟩ := h t.val
    filter_upwards [ht, eventually_ge_atTop 1] with m hm hm1
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm1
    have hp := (mul_pos hA hmpos).trans_le hm.1
    exact pos_of_mul_pos_right hp (pow_nonneg hmpos.le _)
  have hpairs (t j : Fin k) :
      ∀ᶠ m : ℕ in atTop, t < j → (C : ℝ) * m * |partitionLogDiff j.val (m ^ 2)| <
        |partitionLogDiff t.val (m ^ 2)| := by
    by_cases hlt : t < j
    · filter_upwards [eventually_separated_pair h hlt C] with m hm using fun _ ↦ hm
    · exact Filter.Eventually.of_forall fun _ hh ↦ (hlt hh).elim
  have hpairs' : ∀ᶠ m : ℕ in atTop, ∀ t j : Fin k, t < j →
      (C : ℝ) * m * |partitionLogDiff j.val (m ^ 2)| < |partitionLogDiff t.val (m ^ 2)| :=
    Filter.eventually_all.mpr fun t ↦ Filter.eventually_all.mpr (hpairs t)
  filter_upwards [hpairs', Filter.eventually_all.mpr hpos] with m hpair hpositive
  intro t
  let s := univ.filter (t < ·)
  let x := |partitionLogDiff t.val (m ^ 2)|
  have hsum : (C : ℝ) * m * (∑ j ∈ s, |partitionLogDiff j.val (m ^ 2)|) ≤ k * x := by
    calc
      _ = ∑ j ∈ s, (C : ℝ) * m * |partitionLogDiff j.val (m ^ 2)| := Finset.mul_sum ..
      _ ≤ ∑ _j ∈ s, x := sum_le_sum fun j hj ↦ (hpair t j (mem_filter.mp hj).2).le
      _ = (s.card : ℝ) * x := by simp
      _ ≤ k * x := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact_mod_cast (show s.card ≤ k by simpa using s.card_le_univ)
  change ((k * 2 ^ k * m : ℕ) : ℝ) * (∑ j ∈ s, |partitionLogDiff j.val (m ^ 2)|) < x
  by_contra! hfail
  have hmul := mul_le_mul_of_nonneg_left hfail (show 0 ≤ (k : ℝ) + 1 by positivity)
  dsimp [C] at hsum
  push_cast at hmul hsum
  have hx : 0 < x := hpositive t
  nlinarith only [hmul, hsum, hx]

end Erdos1106Work

end

section

/- # Euler's analytic generating function for the partition numbers -/

open Nat Finset Filter PowerSeries Complex
open scoped PowerSeries.WithPiTopology Topology

namespace Erdos1106Gen

noncomputable def geoPart (j : ℕ) : ℕ⟦X⟧ :=
  PowerSeries.mk fun n ↦ if j + 1 ∣ n then 1 else 0

noncomputable def row (k : ℕ) : ℕ⟦X⟧ := ∏ j ∈ range k, geoPart j

@[simp] theorem coeff_geoPart (j n : ℕ) :
    (geoPart j).coeff n = if j + 1 ∣ n then 1 else 0 := PowerSeries.coeff_mk _ _

theorem geoPart_eq (j : ℕ) : geoPart j = ∑' l : ℕ, (X : ℕ⟦X⟧) ^ ((j + 1) * l) := by
  have h0 : constantCoeff ((X : ℕ⟦X⟧) ^ (j + 1)) = 0 := by simp
  have hs : Summable fun l : ℕ ↦ (X : ℕ⟦X⟧) ^ ((j + 1) * l) := by
    simpa [pow_mul] using PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero h0
  ext n
  rw [coeff_geoPart, hs.map_tsum _ (PowerSeries.WithPiTopology.continuous_coeff ℕ n)]
  simp only [coeff_X_pow]
  split_ifs with hd
  · obtain ⟨a, rfl⟩ := hd
    simp
  · have hna (a : ℕ) : n ≠ (j + 1) * a := fun hh ↦ hd ⟨a, hh⟩
    simp only [if_neg (hna _), tsum_zero]

theorem coeff_row_eventually (n : ℕ) : ∀ᶠ k : ℕ in atTop, (row k).coeff n = partitionNumber n := by
  let g := Nat.Partition.genFun (R := ℕ) (fun _ _ ↦ 1)
  have h : HasProd geoPart g := by
    apply (Nat.Partition.hasProd_genFun (R := ℕ) (fun _ _ ↦ 1)).congr_fun
    intro j
    rw [geoPart_eq]
    have hs : Summable fun l : ℕ ↦ (X : ℕ⟦X⟧) ^ ((j + 1) * (l + 1)) := by
      simpa only [PowerSeries.smul_eq_C_mul, map_one, one_mul] using Nat.Partition.summable_genFun_term (R := ℕ) (fun _ _ ↦ 1) j
    simpa only [Nat.mul_zero, pow_zero, PowerSeries.smul_eq_C_mul, map_one, one_mul] using tsum_eq_zero_add' (f := fun l : ℕ ↦ (X : ℕ⟦X⟧) ^ ((j + 1) * l)) hs
  have hc := (PowerSeries.WithPiTopology.continuous_coeff ℕ n).continuousAt.tendsto.comp h.tendsto_prod_nat
  have hgc : g.coeff n = partitionNumber n := by simp [g, Nat.Partition.coeff_genFun, Finsupp.prod, partitionNumber]
  simpa [row, Function.comp_def, hgc, nhds_discrete, tendsto_pure] using hc

noncomputable def term (f : ℕ⟦X⟧) (z : ℂ) (n : ℕ) := (f.coeff n : ℂ) * z ^ n

structure Evaluates (f : ℕ⟦X⟧) (z y : ℂ) : Prop where
  absolute : Summable fun n ↦ ‖term f z n‖
  value : HasSum (term f z) y

theorem term_mul (f g : ℕ⟦X⟧) (z : ℂ) (n : ℕ) :
    term (f * g) z n = ∑ ij ∈ antidiagonal n, term f z ij.1 * term g z ij.2 := by
  simp only [term, PowerSeries.coeff_mul, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul]
  refine sum_congr rfl fun ij hij ↦ ?_
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hij, pow_add]
  ring

theorem Evaluates.mul {f g : ℕ⟦X⟧} {z y y' : ℂ} (h : Evaluates f z y) (h' : Evaluates g z y') :
    Evaluates (f * g) z (y * y') := by
  refine ⟨?_, ?_⟩
  · simpa only [term_mul] using summable_norm_sum_mul_antidiagonal_of_summable_norm h.absolute h'.absolute
  · rw [← h.value.tsum_eq, ← h'.value.tsum_eq, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm h.absolute h'.absolute]
    change HasSum (fun n ↦ term (f*g) z n) _
    simpa only [term_mul] using (summable_sum_mul_antidiagonal_of_summable_norm' h.absolute h.value.summable h'.absolute h'.value.summable).hasSum

theorem eval_one (z : ℂ) : Evaluates 1 z 1 := by
  have he (n : ℕ) : term 1 z n = if n = 0 then 1 else 0 := by
    by_cases hn : n = 0 <;> simp [term, PowerSeries.coeff_one, hn]
  constructor
  · exact (hasSum_single 0 (fun n hn ↦ by simp [he, hn]) (f := fun n ↦ ‖term 1 z n‖)).summable
  · have hs := hasSum_single 0 (fun n hn ↦ by simp [he, hn]) (f := term 1 z)
    simpa [he] using hs

theorem eval_geoPart {z : ℂ} (hz : ‖z‖ < 1) (j : ℕ) :
    Evaluates (geoPart j) z (1 - z ^ (j + 1))⁻¹ := by
  let embed (l : ℕ) := (j + 1) * l
  have inj : Function.Injective embed := fun _ _ h ↦ Nat.eq_of_mul_eq_mul_left (by omega : 0 < j + 1) h
  have ht (l : ℕ) : term (geoPart j) z (embed l) = (z ^ (j + 1)) ^ l := by
    simp [embed, term, pow_mul]
  have hzero (i : ℕ) (hi : i ∉ Set.range embed) : term (geoPart j) z i = 0 := by
    have hd : ¬j + 1 ∣ i := fun ⟨l, hl⟩ ↦ hi ⟨l, hl.symm⟩
    simp [term, hd]
  have hzpow : ‖z ^ (j + 1)‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hz (by omega)
  constructor
  · obtain ⟨v, hv⟩ := (summable_geometric_of_lt_one (norm_nonneg _) hzpow)
    refine ⟨v, (inj.hasSum_iff (fun i hi ↦ by simp [hzero i hi])).mp ?_⟩
    simpa [Function.comp_def, ht, norm_pow] using hv
  · apply (inj.hasSum_iff hzero).mp
    simpa [Function.comp_def, ht] using hasSum_geometric_of_norm_lt_one hzpow

theorem eval_row {z : ℂ} (hz : ‖z‖ < 1) (k : ℕ) :
    Evaluates (row k) z (∏ j ∈ range k, (1 - z ^ (j + 1))⁻¹) := by
  induction k with
  | zero => simpa [row] using eval_one z
  | succ k ih => simpa [row, prod_range_succ, mul_comm] using ih.mul (eval_geoPart hz k)

noncomputable def eulerDen (z : ℂ) : ℂ := ∏' j : ℕ, (1 - z ^ (j + 1))

theorem eulerDen_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : eulerDen z ≠ 0 := by
  unfold eulerDen
  simp_rw [sub_eq_add_neg]
  apply tprod_one_add_ne_zero_of_summable
  · intro j h
    have heq : z ^ (j + 1) = 1 := by linear_combination -h
    have hlt := pow_lt_one₀ (norm_nonneg _) hz (by omega : j + 1 ≠ 0)
    rw [← norm_pow, heq, norm_one] at hlt
    exact lt_irrefl _ hlt
  · simpa using (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hz)

theorem tendsto_rows {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun k : ℕ ↦ ∏ j ∈ range k, (1 - z ^ (j + 1))⁻¹) atTop (𝓝 (eulerDen z)⁻¹) := by
  simpa [eulerDen] using (ModularForm.multipliable_one_sub_pow hz).hasProd.tendsto_prod_nat.inv₀ (eulerDen_ne_zero hz)

theorem real_row_term_le {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (k n : ℕ) :
    ((row k).coeff n : ℝ) * ρ ^ n ≤ ∏ j ∈ range k, (1 - ρ ^ (j + 1))⁻¹ := by
  have ho : ‖(ρ : ℂ)‖ < 1 := by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ] using hρ1
  have hs : HasSum (fun i : ℕ ↦ ((row k).coeff i : ℝ) * ρ ^ i) (∏ j ∈ range k, (1 - ρ ^ (j + 1))⁻¹) := by
    apply Complex.hasSum_ofReal.mp
    have hh := (eval_row ho k).value
    change HasSum (fun n ↦ ((row k).coeff n : ℂ) * (ρ : ℂ) ^ n) _ at hh
    simpa [Complex.ofReal_prod] using hh
  rw [← hs.tsum_eq]
  exact hs.summable.le_tsum n (fun _ _ ↦ by positivity)

theorem partition_hasSum {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ ↦ (partitionNumber n : ℂ) * z ^ n) (eulerDen z)⁻¹ := by
  obtain ⟨ρ, hzr, hr1⟩ := exists_between hz
  have hr0 : 0 < ρ := (norm_nonneg _).trans_lt hzr
  have hrZ : ‖(ρ : ℂ)‖ < 1 := by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0] using hr1
  let B := ‖(eulerDen (ρ : ℂ))⁻¹‖ + 1
  have hB : ∀ᶠ k : ℕ in atTop, (∏ j ∈ range k, (1 - ρ ^ (j + 1))⁻¹) ≤ B := by
    have h := (tendsto_order.1 (tendsto_rows hrZ).norm).2 B (by dsimp [B]; linarith)
    filter_upwards [h] with k hk
    have hr : 0 ≤ ∏ j ∈ range k, (1 - ρ ^ (j + 1))⁻¹ :=
      prod_nonneg fun j _ ↦ inv_nonneg.2 (sub_nonneg.2 (pow_le_one₀ hr0.le hr1.le))
    have heq : (∏ j ∈ range k, (1 - (ρ : ℂ) ^ (j + 1))⁻¹) = ((∏ j ∈ range k, (1 - ρ ^ (j + 1))⁻¹ : ℝ) : ℂ) := by
      push_cast; rfl
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] at hk
    exact hk.le
  have hbound : ∀ᶠ k in atTop, ∀ n, ‖term (row k) z n‖ ≤ B * (‖z‖ / ρ) ^ n := by
    filter_upwards [hB] with k hk n
    have hh := (real_row_term_le hr0.le hr1 k n).trans hk
    rw [term, norm_mul, Complex.norm_natCast, norm_pow, div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hr0 n)).2
    nlinarith only [mul_le_mul_of_nonneg_right hh (pow_nonneg (norm_nonneg z) n)]
  have hab (n : ℕ) : Tendsto (fun k ↦ term (row k) z n) atTop (𝓝 ((partitionNumber n : ℂ) * z ^ n)) :=
    tendsto_const_nhds.congr' ((coeff_row_eventually n).mono fun k hk ↦ by simp [term, hk])
  have hsum : Summable (fun n : ℕ ↦ B * (‖z‖ / ρ) ^ n) :=
    (summable_geometric_of_lt_one (div_nonneg (norm_nonneg _) hr0.le) ((div_lt_one hr0).mpr hzr)).mul_left _
  have hlt := tendsto_tsum_of_dominated_convergence hsum hab hbound
  have hlim : Tendsto (fun k ↦ ∑' n, term (row k) z n) atTop (𝓝 (eulerDen z)⁻¹) :=
    (tendsto_rows hz).congr fun k ↦ (eval_row hz k).value.tsum_eq.symm
  have hs : Summable (fun n : ℕ ↦ (partitionNumber n : ℂ) * z ^ n) := by
    apply hsum.of_norm_bounded
    intro n
    exact le_of_tendsto (hab n).norm (hbound.mono fun k hk ↦ hk n)
  exact (tendsto_nhds_unique hlt hlim) ▸ hs.hasSum

end Erdos1106Gen

end

section

/- # The eta transformation and the coefficient integral for unrestricted partitions -/

open Nat Finset Filter Complex MeasureTheory Set
open scoped Topology Real Interval
open Erdos1106Gen

namespace Erdos1106Transform

private theorem csqrt_I_mul {z : ℂ} (hz : 0 < z.re) :
    Complex.sqrt (I*z) = Complex.sqrt I * Complex.sqrt z := by
  have hn : z ≠ 0 := by rintro rfl; simp at hz
  have harg := (abs_le.mp ((Complex.abs_arg_le_pi_div_two_iff).2 hz.le))
  have hlog := Complex.log_mul I_ne_zero hn (show I.arg + z.arg ∈ Set.Ioc (-Real.pi) Real.pi by
    rw [Complex.arg_I]; constructor <;> linarith [Real.pi_pos, harg.1, harg.2])
  rw [sqrt_eq_exp (mul_ne_zero I_ne_zero hn), sqrt_eq_exp I_ne_zero, sqrt_eq_exp hn,
    hlog, add_div, Complex.exp_add]

private theorem eta_laplace (z : ℂ) :
    ModularForm.eta (I * z / (2 * Real.pi)) = exp (-z / 24) * eulerDen (exp (-z)) := by
  have h (h : ℝ) : Function.Periodic.qParam h (I * z / (2 * Real.pi)) = exp (-z / h) := by
    rw [Function.Periodic.qParam]
    congr 1
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    ring_nf
    simp [I_sq]
  rw [ModularForm.eta, h 24, eulerDen]
  congr 1
  apply tprod_congr
  intro n
  simp only [ModularForm.eta_q, h 1, ofReal_one, div_one]

/-- The normalized partition generating function on the right half-plane. -/
theorem eta_inversion {z : ℂ} (hz : 0 < z.re) :
    (eulerDen (exp (-z)))⁻¹ =
      Complex.sqrt (z / (2 * Real.pi)) * exp (Real.pi ^ 2 / (6*z) - z/24)
        * (eulerDen (exp (-(4 * Real.pi ^ 2 / z))))⁻¹ := by
  let τ := I * z / (2 * Real.pi)
  let w := 4 * (Real.pi : ℂ)^2 / z
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hτ : τ ∈ UpperHalfPlane.upperHalfPlaneSet := by
    change 0 < (I * z / (2 * (Real.pi : ℂ))).im
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl]
    rw [Complex.div_ofReal_im, Complex.I_mul_im]
    exact div_pos hz (by positivity)
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have href : -1 / τ = I * w / (2 * Real.pi) := by
    dsimp [τ, w]; field_simp; ring_nf; simp [I_sq]
  have hzw : 0 < w.re := by
    dsimp [w]
    rw [show (4 * (Real.pi : ℂ)^2) = (((4*Real.pi^2 : ℝ)) : ℂ) by push_cast; rfl, div_eq_mul_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.inv_re]
    exact mul_pos (by positivity) (div_pos hz (Complex.normSq_pos.mpr hz0))
  have hzz : ‖exp (-z)‖ < 1 := by simpa [Complex.norm_exp, Real.exp_lt_one_iff] using hz
  have hww : ‖exp (-w)‖ < 1 := by simpa [Complex.norm_exp, Real.exp_lt_one_iff] using hzw
  have hreal : 0 < (z / ((2*Real.pi : ℝ) : ℂ)).re := by rw [Complex.div_ofReal_re]; positivity
  have hroot : Complex.sqrt τ = Complex.sqrt I * Complex.sqrt (z / (2*Real.pi)) := by
    dsimp [τ]
    rw [mul_div_assoc]
    apply csqrt_I_mul
    simpa using hreal
  have hE := ModularForm.eta_comp_eq_csqrt_I_inv hτ
  change ModularForm.eta (-1 / τ) = (Complex.sqrt I)⁻¹ * (Complex.sqrt τ * ModularForm.eta τ) at hE
  rw [href, eta_laplace, hroot, show ModularForm.eta τ = _ from eta_laplace z] at hE
  have hsI : Complex.sqrt I ≠ 0 := by simp [Complex.sqrt, I_ne_zero]
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel_left₀ hsI] at hE
  have hexp : exp (Real.pi ^ 2 / (6*z) - z/24) = exp (-z / 24) / exp (-w / 24) := by
    rw [← Complex.exp_sub]
    congr 1
    dsimp [w]
    field_simp
    ring
  change _ = Complex.sqrt (z/(2 * Real.pi)) * _ * (eulerDen (exp (-w)))⁻¹
  rw [hexp]
  field_simp [eulerDen_ne_zero hzz, eulerDen_ne_zero hww, Complex.exp_ne_zero] at hE ⊢
  linear_combination hE

private theorem orthogonality (l : ℤ) :
    (∫ θ in -Real.pi..Real.pi, exp ((l : ℂ) * I * θ)) =
      if l = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  by_cases hl : l = 0
  · subst l; simp [intervalIntegral.integral_const, two_mul]
  · rw [if_neg hl, integral_exp_mul_complex (mul_ne_zero (Int.cast_ne_zero.mpr hl) I_ne_zero)]
    have he : exp ((l : ℂ) * I * Real.pi) = exp ((l : ℂ) * I * (-Real.pi)) := by
      rw [show (l : ℂ) * I * Real.pi = (l : ℂ)*I*(-Real.pi) + (l : ℂ)*(2*Real.pi*I) by ring,
        Complex.exp_add, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow, mul_one]
    push_cast
    rw [he, sub_self, zero_div]

/-- Fourier coefficient extraction for the analytic Euler product on a circle of radius r. -/
theorem coefficient_integral {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    (∫ θ in -Real.pi..Real.pi,
      (eulerDen ((r : ℂ) * exp (I * θ)))⁻¹ * exp (-(n : ℂ) * I * θ)) =
      (2 * Real.pi : ℝ) * ((partitionNumber n : ℂ) * (r : ℂ)^n) := by
  let F (j : ℕ) (θ : ℝ) := (partitionNumber j : ℂ) * (r : ℂ)^j * exp (((j : ℂ) - n) * I * θ)
  have hh (θ : ℝ) : ∑' j, F j θ = (eulerDen ((r : ℂ) * exp (I * θ)))⁻¹ * exp (-(n : ℂ)*I*θ) := by
    have hnorm : ‖(r : ℂ) * exp (I * θ)‖ < 1 := by simpa [norm_mul, Complex.norm_exp, Real.norm_eq_abs, abs_of_nonneg hr] using hr1
    rw [← (partition_hasSum hnorm).tsum_eq, ← tsum_mul_right]
    apply tsum_congr
    intro j
    dsimp [F]
    rw [mul_pow, ← Complex.exp_nat_mul,
      show ((j : ℂ)-n)*I*θ = (j : ℂ)*(I*θ) + -(n : ℂ)*I*θ by ring, Complex.exp_add]
    ring
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hnF (j : ℕ) (θ : ℝ) : ‖F j θ‖ = (partitionNumber j : ℝ) * r ^ j := by
    simp [F, norm_pow, Complex.norm_exp, Complex.mul_re, Complex.mul_im, abs_of_nonneg hr]
  have hs : Summable fun j : ℕ ↦ (partitionNumber j : ℝ) * r^j := by
    have hn : ‖(r : ℂ)‖ < 1 := by simpa [abs_of_nonneg hr] using hr1
    apply Complex.summable_ofReal.mp
    simpa using (partition_hasSum hn).summable
  have hswap : ∑' j, (∫ θ in -Real.pi..Real.pi, F j θ) =
      ∫ θ in -Real.pi..Real.pi, ∑' j, F j θ := by
    simp_rw [intervalIntegral.integral_of_le hle]
    apply MeasureTheory.integral_tsum_of_summable_integral_norm
    · intro j
      apply Continuous.integrableOn_Icc _ |>.mono_set Set.Ioc_subset_Icc_self
      dsimp [F]
      fun_prop
    · simp only [hnF, MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hle, smul_eq_mul]
      exact hs.mul_left _
  simp_rw [← hh]
  rw [← hswap, tsum_eq_single n]
  · dsimp [F]
    simp [intervalIntegral.integral_const, sub_neg_eq_add, two_mul, Algebra.smul_def]
    ring
  · intro j hj
    dsimp [F]
    rw [intervalIntegral.integral_const_mul]
    have he := orthogonality ((j : ℤ)-n)
    push_cast at he
    rw [he, if_neg (by omega), mul_zero]

end Erdos1106Transform

end

section

/- # Circular integral and the real radial product -/

open Nat Filter Complex MeasureTheory Set
open scoped Topology Real Interval
open Erdos1106Gen Erdos1106Transform

namespace Erdos1106Contour

noncomputable def laplacePoint (t θ : ℝ) : ℂ := (t : ℂ) - I * θ

noncomputable def contour (n : ℕ) (t θ : ℝ) : ℂ :=
  let z := laplacePoint t θ
  (eulerDen (exp (-z)))⁻¹ * exp ((n : ℂ) * z)

private theorem exp_laplace (t θ : ℝ) :
    exp (-(laplacePoint t θ)) = (Real.exp (-t) : ℂ) * exp (I * θ) := by
  rw [laplacePoint, neg_sub, sub_eq_neg_add, Complex.exp_add]
  simp

theorem continuous_contour (n : ℕ) {t : ℝ} (ht : 0 < t) : Continuous (contour n t) := by
  let r := Real.exp (-t)
  have hr₀ : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  have hnorm (θ : ℝ) : ‖(r:ℂ) * exp (I*θ)‖ = r := by simp [Complex.norm_exp, abs_of_pos hr₀]
  have hsr : Summable (fun j : ℕ ↦ (partitionNumber j:ℝ)*r^j) := by
    have hz : ‖(r:ℂ)‖ < 1 := by simpa [abs_of_pos hr₀] using hr₁
    apply Complex.summable_ofReal.mp
    simpa using (partition_hasSum hz).summable
  let F (j : ℕ) (θ : ℝ) := (partitionNumber j : ℂ)*((r:ℂ)*exp (I*θ))^j
  have hsum (θ : ℝ) : ∑' j, F j θ = (eulerDen (exp (-(laplacePoint t θ))))⁻¹ := by
    rw [exp_laplace]
    exact (partition_hasSum ((hnorm θ).trans_lt hr₁)).tsum_eq
  have hc : Continuous fun θ ↦ ∑' j, F j θ := continuous_tsum (fun j ↦ by dsimp [F]; fun_prop) hsr (fun j θ ↦ by
    dsimp [F]; rw [norm_mul, norm_pow, hnorm, Complex.norm_natCast])
  unfold contour
  simp_rw [← hsum]
  exact hc.mul (by unfold laplacePoint; fun_prop)

theorem integral_contour (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ θ in -Real.pi..Real.pi, contour n t θ) = (2*Real.pi : ℝ) * (partitionNumber n : ℂ) := by
  let r := Real.exp (-t)
  have hr₀ : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  have he (θ : ℝ) : contour n t θ = exp ((n:ℂ)*t) *
      ((eulerDen ((r:ℂ)*exp (I*θ)))⁻¹ * exp (-(n:ℂ)*I*θ)) := by
    rw [contour, exp_laplace, laplacePoint, mul_sub, sub_eq_add_neg, Complex.exp_add]
    dsimp [r]; rw [show -(n:ℂ)*I*θ = -((n:ℂ)*(I*θ)) by ring]; ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, coefficient_integral hr₀.le hr₁ n]
  have hpow : (r : ℂ)^n = exp (-((n : ℂ)*t)) := by
    dsimp [r]; rw [Complex.ofReal_exp, ← Complex.exp_nat_mul]; push_cast; ring_nf
  rw [hpow, Complex.exp_neg]
  field_simp

theorem real_den {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    ∃ B : ℝ, 0 < B ∧ HasProd (fun j : ℕ ↦ 1-r^(j+1)) B ∧ eulerDen (r : ℂ) = B := by
  have hs : Summable (fun j : ℕ ↦ r^(j+1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr₀ hr₁)
  have hl : Summable (fun j : ℕ ↦ Real.log (1-r^(j+1))) := by
    simpa [sub_eq_add_neg] using Real.summable_log_one_add_of_summable hs.neg
  have hp (j : ℕ) : 0 < 1-r^(j+1) := sub_pos.mpr (pow_lt_one₀ hr₀ hr₁ (by omega))
  have h := Real.hasProd_of_hasSum_log hp hl.hasSum
  refine ⟨_, Real.exp_pos _, h, ?_⟩
  have hc := h.map Complex.ofRealHom Complex.continuous_ofReal
  unfold eulerDen
  apply HasProd.tprod_eq
  convert hc using 1
  · funext j; simp
  · rfl

end Erdos1106Contour

end

section

/- # Uniform bounds for the primary saddle integral -/

open Nat Finset Filter Complex MeasureTheory Set
open scoped Topology Real Interval
open Erdos1106Gen

namespace Erdos1106Major

private theorem p_le_pow (n : ℕ) : partitionNumber n ≤ 2 ^ n := by
  calc
    _ ≤ Fintype.card (Composition n) := Fintype.card_le_of_surjective _ Nat.Partition.ofComposition_surj
    _ = 2 ^ (n-1) := composition_card n
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

theorem euler_inv_near_zero {z : ℂ} (hz : ‖z‖ ≤ 1/4) :
    ‖(eulerDen z)⁻¹ - 1‖ ≤ 4 * ‖z‖ := by
  have h := partition_hasSum (hz.trans_lt (by norm_num))
  have hs := h.summable
  rw [← h.tsum_eq, hs.tsum_eq_zero_add, partitionNumber_zero]
  simp only [Nat.cast_one, pow_zero, one_mul, add_sub_cancel_left]
  have hp : 0 ≤ 2 * ‖z‖ := by positivity
  have hq : 2 * ‖z‖ < 1 := by linarith
  have hg : Summable (fun n : ℕ ↦ (2 * ‖z‖) ^ (n+1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hp hq)
  have hterm (n : ℕ) :
      ‖((partitionNumber (n+1) : ℂ) * z^(n+1))‖ ≤ (2 * ‖z‖)^(n+1) := by
    rw [norm_mul, norm_pow, Complex.norm_natCast, mul_pow]
    gcongr
    exact_mod_cast p_le_pow (n+1)
  calc
    _ ≤ ∑' n : ℕ, ‖(partitionNumber (n+1) : ℂ) * z^(n+1)‖ :=
      norm_tsum_le_tsum_norm (hg.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm)
    _ ≤ ∑' n : ℕ, (2 * ‖z‖) ^ (n+1) :=
      (hg.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm).tsum_le_tsum hterm hg
    _ = 2 * ‖z‖ / (1 - 2 * ‖z‖) := by
      simp_rw [pow_succ, tsum_mul_right, tsum_geometric_of_lt_one hp hq]
      ring
    _ ≤ 4 * ‖z‖ := (div_le_iff₀ (by linarith)).2 (by nlinarith [norm_nonneg z, mul_nonneg (norm_nonneg z) (sub_nonneg.mpr hz)])

noncomputable def amplitude (u : ℝ) : ℂ := Complex.sqrt (1 + I * u)
noncomputable def kernel (s : ℂ) (u : ℝ) : ℂ :=
  amplitude u * exp (-(s / (1 + I * u)) * u ^ 2)

noncomputable def saddle (s : ℂ) : ℂ :=
  ∫ u in (0:ℝ)..(1/100), kernel s u + kernel s (-u)

private theorem amp_sq (u : ℝ) : amplitude u ^ 2 = 1 + I*u := by
  simp [amplitude, Complex.sqrt]

private theorem amp_re_nonneg (u : ℝ) : 0 ≤ (amplitude u).re := by
  rw [amplitude, Complex.sqrt, Complex.cpow_inv_two_re]
  positivity

theorem amp_near_one (u : ℝ) : ‖amplitude u - 1‖ ≤ |u| := by
  have hfactor : (amplitude u - 1) * (amplitude u + 1) = I * u := by
    linear_combination amp_sq u
  have hnorm := congrArg norm hfactor
  simp only [norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul] at hnorm
  have h1 : 1 ≤ ‖amplitude u + 1‖ := by
    have := Complex.re_le_norm (amplitude u + 1)
    simp only [Complex.add_re, Complex.one_re] at this
    linarith [amp_re_nonneg u]
  rw [← hnorm]
  exact le_mul_of_one_le_right (norm_nonneg _) h1

private theorem amp_le (u : ℝ) (hu : |u| ≤ 1/100) : ‖amplitude u‖ ≤ 2 := by
  have h := norm_sub_norm_le (amplitude u) 1
  simp only [norm_one] at h
  linarith [amp_near_one u]

private theorem denom_formula (s : ℂ) (u : ℝ) :
    (s / (1 + I * u)).re = (s.re + s.im*u) / (1 + u^2) ∧
    (s / (1 + I * u)).im = (s.im - s.re*u) / (1 + u^2) := by
  simp [Complex.div_re, Complex.div_im, Complex.normSq_apply, pow_two, Complex.mul_re, Complex.mul_im]
  ring_nf
  trivial

private theorem denominator_bounds {s : ℂ} {u : ℝ} (hT : 0 < s.re)
    (hw : |s.im| ≤ s.re / 100) (hu : |u| ≤ 1/100) :
    s.re / 2 ≤ (s / (1 + I * u)).re ∧
    (s / (1 + I * u)).re ≤ 2 * s.re ∧
    |(s / (1 + I * u)).im| ≤ s.re / 40 := by
  obtain ⟨hre, him⟩ := denom_formula s u
  have hprod : |s.im * u| ≤ (s.re / 100) * (1/100) := by
    rw [abs_mul]; gcongr
  have hprod' := abs_le.mp hprod
  have hu2 : u^2 ≤ (1/100:ℝ)^2 := by
    rw [← sq_abs]; gcongr
  have huT := mul_le_mul_of_nonneg_left hu hT.le
  have hden : 0 < 1 + u^2 := by positivity
  rw [hre, him, le_div_iff₀ hden, div_le_iff₀ hden, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  constructor
  · nlinarith only [hprod'.1, mul_le_mul_of_nonneg_left hu2 hT.le, hT]
  constructor
  · nlinarith only [hprod'.2, mul_nonneg hT.le (sq_nonneg u), hT]
  · have ht : |s.im - s.re*u| ≤ |s.im| + |s.re*u| := by simpa [sub_eq_add_neg] using abs_add_le s.im (-(s.re*u))
    rw [abs_mul, abs_of_pos hT] at ht
    nlinarith only [ht, hw, huT, mul_nonneg hT.le (sq_nonneg u), hT]

theorem norm_kernel_le {s : ℂ} {u : ℝ} (hT : 0 < s.re)
    (hw : |s.im| ≤ s.re / 100) (hu : |u| ≤ 1/100) :
    ‖kernel s u‖ ≤ 2 * Real.exp (-(s.re/2) * u^2) := by
  rw [kernel, norm_mul, Complex.norm_exp, show -(s / (1 + I * ↑u)) * (↑u)^2 =
      -(s / (1 + I * ↑u)) * ((u^2 : ℝ) : ℂ) by push_cast; rfl, Complex.mul_re,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.ofReal_re, Complex.neg_re]
  apply mul_le_mul (amp_le u hu) _ (Real.exp_pos _).le (by norm_num)
  apply Real.exp_le_exp.mpr
  have hx := (denominator_bounds hT hw hu).1
  nlinarith [mul_le_mul_of_nonneg_right hx (sq_nonneg u)]

theorem re_kernel_core {s : ℂ} {u : ℝ} (hT : 0 < s.re)
    (hw : |s.im| ≤ s.re / 100) (hu : |u| ≤ 1/100) (hcore : s.re * u^2 ≤ 16) :
    (1/3 : ℝ) * Real.exp (-2*s.re*u^2) ≤ (kernel s u).re := by
  let v := -(s / (1+I*u)) * ((u^2 : ℝ) : ℂ)
  have hK : kernel s u = amplitude u * exp v := by simp [kernel, v]
  have hvr : v.re = -(s / (1+I*u)).re * u^2 := by simp only [v, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.neg_re]
  have hvi : v.im = -(s / (1+I*u)).im * u^2 := by simp only [v, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, Complex.neg_im]
  obtain ⟨_, hd, hi⟩ := denominator_bounds hT hw hu
  have hvim : |v.im| ≤ 1/2 := by
    rw [hvi, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg u)]
    nlinarith [mul_le_mul_of_nonneg_right hi (sq_nonneg u)]
  have hc : (1/2 : ℝ) ≤ Real.cos v.im := by
    have hsq : v.im^2 ≤ (1/2:ℝ)^2 := by rw [← sq_abs]; gcongr
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := v.im)]
  have href : Real.exp (-2*s.re*u^2) ≤ Real.exp v.re := by
    apply Real.exp_le_exp.mpr
    rw [hvr]
    nlinarith [mul_le_mul_of_nonneg_right hd (sq_nonneg u)]
  have he : kernel s u - exp v = (amplitude u - 1) * exp v := by rw [hK]; ring
  have hdiff := (abs_le.mp (Complex.abs_re_le_norm (kernel s u - exp v))).1
  rw [Complex.sub_re, he, norm_mul, Complex.norm_exp, Complex.exp_re] at hdiff
  nlinarith [mul_le_mul_of_nonneg_right ((amp_near_one u).trans hu) (Real.exp_pos v.re).le,
    mul_le_mul_of_nonneg_left hc (Real.exp_pos v.re).le, Real.exp_pos v.re]

private theorem one_I_ne (u : ℝ) : 1 + I * (u : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre

theorem continuous_amplitude : Continuous amplitude := by
  rw [continuous_iff_continuousAt]
  intro u
  have hin : ContinuousAt (fun v : ℝ ↦ (1:ℂ) + I * (v:ℂ)) u := by fun_prop
  exact ContinuousAt.comp (f := fun v : ℝ ↦ (1:ℂ) + I * (v:ℂ)) (Complex.continuousAt_sqrt (Or.inl (by simp : 0 ≤ (1 + I*(u : ℂ)).re))) hin

theorem continuous_kernel : Continuous (fun x : ℂ × ℝ ↦ kernel x.1 x.2) := by
  have hd : Continuous (fun x : ℂ × ℝ ↦ (1:ℂ) + I * (x.2:ℂ)) := by fun_prop
  have hq := continuous_fst.div hd (fun x ↦ one_I_ne x.2)
  exact (continuous_amplitude.comp continuous_snd).mul (Complex.continuous_exp.comp (hq.neg.mul (by fun_prop : Continuous (fun x : ℂ × ℝ ↦ (x.2:ℂ)^2))))

theorem continuous_kernel_right (s : ℂ) : Continuous (kernel s) :=
  continuous_kernel.comp (continuous_const.prodMk continuous_id)

private noncomputable def slopeKernel (u : ℝ) : ℂ := -(u : ℂ)^2 / (1+I*u)

private theorem kernel_alt (s : ℂ) (u : ℝ) :
    kernel s u = amplitude u * exp (s * slopeKernel u) := by
  rw [kernel, slopeKernel]
  congr 2
  ring

private theorem continuous_slopeKernel : Continuous slopeKernel := by
  exact (by fun_prop : Continuous (fun u : ℝ ↦ -(u:ℂ)^2)).div (by fun_prop) one_I_ne

private theorem kernel_deriv (s : ℂ) (u : ℝ) :
    HasDerivAt (fun z ↦ kernel z u) (kernel s u * slopeKernel u) s := by
  simp only [kernel_alt]
  convert! ((((hasDerivAt_id s).mul_const (slopeKernel u)).cexp).const_mul (amplitude u)) using 1
  simp
  ring

/-- Holomorphic dependence of the primary arc integral on the complex saddle parameter. -/
theorem differentiable_saddle : Differentiable ℂ saddle := by
  intro z
  let D (s : ℂ) (u : ℝ) := kernel s u * slopeKernel u + kernel s (-u) * slopeKernel (-u)
  let K (s : ℂ) (u : ℝ) := kernel s u + kernel s (-u)
  have hD : Continuous (fun p : ℂ × ℝ ↦ D p.1 p.2) := by
    unfold D
    exact (continuous_kernel.mul (continuous_slopeKernel.comp continuous_snd)).add
      ((continuous_kernel.comp (continuous_fst.prodMk continuous_snd.neg)).mul
        (continuous_slopeKernel.comp continuous_snd.neg))
  have hK (s : ℂ) : Continuous (K s) := (continuous_kernel_right s).add ((continuous_kernel_right s).comp continuous_neg)
  let A : Set (ℂ × ℝ) := Metric.closedBall z 1 ×ˢ Set.Icc 0 (1/100)
  have hA : IsCompact A := (isCompact_closedBall z 1).prod isCompact_Icc
  obtain ⟨B, hB⟩ := hA.bddAbove_image hD.norm.continuousOn
  let μ := volume.restrict (Ioc (0:ℝ) (1/100))
  have heq : saddle = fun s ↦ ∫ u, K s u ∂μ := by
    funext s; exact intervalIntegral.integral_of_le (by norm_num)
  rw [heq]
  have hd : ∀ᵐ u ∂μ, ∀ s ∈ Metric.closedBall z 1, HasDerivAt (fun x ↦ K x u) (D s u) s :=
    Filter.Eventually.of_forall fun u s _ ↦ (kernel_deriv s u).add (kernel_deriv s (-u))
  have hb : ∀ᵐ u ∂μ, ∀ s ∈ Metric.closedBall z 1, ‖D s u‖ ≤ B := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with u hu s hs
    exact hB ⟨(s,u), ⟨hs, hu.1.le, hu.2⟩, rfl⟩
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.closedBall z 1) (bound := fun _ ↦ B) (μ := μ) (F := K) (F' := D)
    (Metric.closedBall_mem_nhds z (by norm_num)) (Filter.Eventually.of_forall fun s ↦ (hK s).aestronglyMeasurable)
    ((hK z).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    ((hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable) hb
    ((continuous_const : Continuous fun _ : ℝ ↦ B).integrableOn_Icc.mono_set Ioc_subset_Icc_self) hd).2.differentiableAt


theorem saddle_norm_le {s : ℂ} (hT : 0 < s.re) (hw : |s.im| ≤ s.re/100) :
    ‖saddle s‖ ≤ 1 := by
  apply le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (C := 4) ?_)
  · norm_num
  intro u hu
  rw [Set.uIoc_of_le (by norm_num)] at hu
  have hu' : |u| ≤ 1/100 := by rw [abs_of_nonneg hu.1.le]; exact hu.2
  have h := norm_kernel_le hT hw hu'
  have hneg := norm_kernel_le hT hw (u := -u) (by simpa using hu')
  have he : Real.exp (-(s.re/2) * u^2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
  rw [neg_sq] at hneg
  exact (norm_add_le _ _).trans (by linarith)

/-- A Gaussian core dominates the signed tails throughout a fixed complex sector. -/
theorem saddle_re_lower {s : ℂ} (hT : 160000 ≤ s.re) (hw : |s.im| ≤ s.re/100) :
    Real.exp (-2) / (3 * Real.sqrt s.re) ≤ (saddle s).re := by
  let R := Real.sqrt s.re
  have hpos : 0 < s.re := by linarith
  have hR : 0 < R := Real.sqrt_pos.mpr hpos
  have hsq : R^2 = s.re := Real.sq_sqrt hpos.le
  have hlarge : 400 ≤ R := by nlinarith [sq_nonneg (R-400)]
  have h₁ : (0 : ℝ) ≤ 1/R := by positivity
  have h₄ : 1/R ≤ 4/R := by gcongr; norm_num
  have hδ : 4/R ≤ 1/100 := (div_le_iff₀ hR).mpr (by linarith)
  let g (u : ℝ) := (kernel s u + kernel s (-u)).re
  have hc := (continuous_kernel_right s).add ((continuous_kernel_right s).comp continuous_neg)
  have hg : Continuous g := Complex.continuous_re.comp hc
  have hint : (∫ u in (0:ℝ)..(1/100), g u) = (saddle s).re :=
    Complex.reCLM.intervalIntegral_comp_comm (hc.intervalIntegrable ..)
  have hcore {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 4/R) :
      (2/3 : ℝ) * Real.exp (-2*s.re*u^2) ≤ g u := by
    have hδu : |u| ≤ 1/100 := by rw [abs_of_nonneg hu]; exact hu'.trans hδ
    have hRu : 0 ≤ R*u := mul_nonneg hR.le hu
    have hRu' : R*u ≤ 4 := by simpa [mul_comm] using (le_div_iff₀ hR).mp hu'
    have hTu : s.re*u^2 ≤ 16 := by rw [← hsq]; nlinarith only [mul_nonneg (sub_nonneg.mpr hRu') (show 0 ≤ 4+R*u by linarith)]
    have hh := re_kernel_core hpos hw hδu hTu
    have hn := re_kernel_core hpos hw (u := -u) (by simpa using hδu) (by simpa using hTu)
    simp only [neg_sq] at hn
    dsimp [g]; linarith
  have hi₁ := intervalIntegral.integral_mono_on (μ := volume) h₁
    (f := fun _ ↦ (2/3:ℝ)*Real.exp (-2)) (g := g)
    (continuous_const.intervalIntegrable ..) (hg.intervalIntegrable ..) (by
      intro u hu
      have hRu : R*u ≤ 1 := by simpa [mul_comm] using (le_div_iff₀ hR).mp hu.2
      have hRu0 := mul_nonneg hR.le hu.1
      have hTu : s.re*u^2 ≤ 1 := by rw [← hsq]; nlinarith only [mul_nonneg (sub_nonneg.mpr hRu) (show 0 ≤ 1+R*u by linarith)]
      apply le_trans _ (hcore hu.1 (hu.2.trans h₄)); gcongr; linarith)
  have hi₂ := intervalIntegral.integral_mono_on (μ := volume) h₄ (f := fun _ ↦ (0:ℝ)) (g := g)
    (continuous_const.intervalIntegrable ..) (hg.intervalIntegrable ..) (by
      intro u hu; exact le_trans (by positivity) (hcore (h₁.trans hu.1) hu.2))
  have htail (u : ℝ) (hu : u ∈ Set.Icc (4/R) (1/100)) :
      -4 * Real.exp ((-2*R)*u) ≤ g u := by
    have hu0 := (h₁.trans h₄).trans hu.1
    have hu' : |u| ≤ 1/100 := by rw [abs_of_nonneg hu0]; exact hu.2
    have hRu : 4 ≤ R*u := by simpa [mul_comm] using (div_le_iff₀ hR).mp hu.1
    have he : Real.exp (-(s.re/2)*u^2) ≤ Real.exp ((-2*R)*u) := by
      apply Real.exp_le_exp.mpr
      rw [← hsq]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hRu) (mul_nonneg hR.le hu0)]
    have h := norm_kernel_le hpos hw hu'
    have hn := norm_kernel_le hpos hw (u := -u) (by simpa using hu')
    rw [neg_sq] at hn
    have h1 := (abs_le.mp (Complex.abs_re_le_norm (kernel s u))).1
    have h2 := (abs_le.mp (Complex.abs_re_le_norm (kernel s (-u)))).1
    dsimp [g]; linarith
  have hi₃ := intervalIntegral.integral_mono_on (μ := volume) hδ (f := fun u ↦ -4 * Real.exp ((-2*R)*u)) (g := g)
    ((by fun_prop : Continuous (fun u : ℝ ↦ -4 * Real.exp ((-2*R)*u))).intervalIntegrable ..)
    (hg.intervalIntegrable ..) htail
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left Real.exp (by positivity : -2*R ≠ 0),
    integral_exp, smul_eq_mul, show -2*R*(4/R) = -8 by field_simp; ring] at hi₃
  have ht : -2 * Real.exp (-8)/R ≤ ∫ u in (4/R)..(1/100), g u := by
    apply le_trans _ hi₃
    field_simp [hR.ne']
    nlinarith [Real.exp_pos (-(2 * R / 100))]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_zero] at hi₁ hi₂
  have h12 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable (0:ℝ) (1/R)) (hg.intervalIntegrable (1/R) (4/R))
  have h23 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable (0:ℝ) (4/R)) (hg.intervalIntegrable (4/R) (1/100))
  have he6 : 6 ≤ Real.exp 6 := by linarith [Real.add_one_le_exp (6:ℝ)]
  have he8 : 6 * Real.exp (-8) ≤ Real.exp (-2) := by
    have he := mul_le_mul_of_nonneg_right he6 (Real.exp_pos (-8)).le
    rwa [← Real.exp_add, show (6:ℝ)+ -8 = -2 by norm_num] at he
  change Real.exp (-2) / (3 * R) ≤ _
  rw [← hint, ← h23, ← h12]
  have hcoeff : Real.exp (-2)/(3*R) ≤ 1/R*(2/3 * Real.exp (-2)) + -2*Real.exp (-8)/R := by
    field_simp [hR.ne']; linarith
  linarith

end Erdos1106Major

end

section

/-
# Angular loss for the partition generating product

The first family of terms in the logarithm of the Euler product gives a geometric
series. An exact formula for that series gives an exponential loss outside a fixed
multiple of the saddle radius in the angular variable.
-/

namespace Erdos1106MinorArc

open Filter
open scoped BigOperators Topology

private lemma polar_norm (r θ : ℝ) (hr : 0 ≤ r) :
    ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
  simp [abs_of_nonneg hr, Complex.norm_exp]

private lemma polar_pow_re (r θ : ℝ) (j : ℕ) :
    (((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ j).re =
      r ^ j * Real.cos ((j : ℝ) * θ) := by
  have he : (Complex.exp ((θ : ℂ) * Complex.I)) ^ j =
      Complex.exp (((((j : ℝ) * θ : ℝ) : ℂ)) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    push_cast
    ring_nf
  rw [mul_pow, he, ← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]

lemma geometricAngularLoss (r θ : ℝ) (hr₀ : 0 < r) (hr₁ : r < 1) :
    (∑' j : ℕ, r ^ j * (1 - Real.cos ((j : ℝ) * θ))) =
      r * (1 + r) * (1 - Real.cos θ) /
        ((1 - r) * ((1 - r) ^ 2 + 2 * r * (1 - Real.cos θ))) := by
  let z : ℂ := (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
  have hz := polar_norm r θ hr₀.le
  have hzre : z.re = r * Real.cos θ := by
    simpa only [pow_one, Nat.cast_one, one_mul] using polar_pow_re r θ 1
  have hzpow := polar_pow_re r θ
  have hreal := hasSum_geometric_of_abs_lt_one (show |r| < 1 by rwa [abs_of_pos hr₀])
  have hcomplex := Complex.hasSum_re (hasSum_geometric_of_norm_lt_one (hz ▸ hr₁))
  have hsum := hreal.sub hcomplex
  simp only [hzpow, ← mul_one_sub] at hsum
  rw [hsum.tsum_eq, Complex.inv_re, Complex.sub_re, Complex.one_re, hzre]
  have hD : Complex.normSq (1 - z) =
      (1 - r) ^ 2 + 2 * r * (1 - Real.cos θ) := by
    rw [Complex.normSq_sub, Complex.normSq_one, Complex.normSq_eq_norm_sq, hz]
    simp [hzre]
    ring
  rw [hD]
  have hpos : 0 < 1 - r := sub_pos.mpr hr₁
  have hDpos : 0 < (1 - r) ^ 2 + 2 * r * (1 - Real.cos θ) :=
    add_pos_of_pos_of_nonneg (pow_pos hpos _) (by positivity [Real.cos_le_one θ])
  let D := (1 - r) ^ 2 + 2 * r * (1 - Real.cos θ)
  change (1 - r)⁻¹ - (1 - r * Real.cos θ) / D =
    r * (1 + r) * (1 - Real.cos θ) / ((1 - r) * D)
  field_simp [hpos.ne', show D ≠ 0 from hDpos.ne']
  dsimp [D]
  ring

lemma minorArcLoss (δ t θ : ℝ) (hδ : 0 < δ) (ht : 0 < t) (ht₁ : t ≤ 1)
    (hθ₀ : δ * t ≤ |θ|) (hθ₁ : |θ| ≤ Real.pi) :
    Real.exp (-1) / (Real.pi ^ 2 / (2 * δ ^ 2) + 2) / t ≤
      ∑' j : ℕ, Real.exp (-t) ^ j * (1 - Real.cos ((j : ℝ) * θ)) := by
  let r := Real.exp (-t)
  let x := 1 - Real.cos θ
  let C := Real.pi ^ 2 / (2 * δ ^ 2) + 2
  change Real.exp (-1) / C / t ≤ ∑' j : ℕ, r ^ j * (1 - Real.cos ((j : ℝ) * θ))
  have hr₀ : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  have hre : Real.exp (-1) ≤ r := Real.exp_monotone (by linarith)
  have hrsmall : 1 - r ≤ t := by linarith [Real.add_one_le_exp (-t)]
  have hx : 0 ≤ x := sub_nonneg.mpr (Real.cos_le_one θ)
  have hquad : 2 / Real.pi ^ 2 * (δ * t) ^ 2 ≤ x := by
    calc
      _ ≤ 2 / Real.pi ^ 2 * |θ| ^ 2 := by
        gcongr
      _ ≤ x := by
        rw [sq_abs]
        dsimp [x]
        linarith [Real.cos_le_one_sub_mul_cos_sq hθ₁]
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity) hquad
  have hc : 0 < C := by dsimp [C]; positivity
  have hsmall : t ^ 2 ≤ (C - 2) * x := by
    have hπ : (0 : ℝ) < Real.pi ^ 2 := by positivity [Real.pi_pos]
    have hδ₂ : 0 < 2 * δ ^ 2 := by positivity
    have hb := mul_le_mul_of_nonneg_left hquad
      (show 0 ≤ Real.pi ^ 2 / (2 * δ ^ 2) by positivity)
    have hcancel :
        Real.pi ^ 2 / (2 * δ ^ 2) * (2 / Real.pi ^ 2 * (δ * t) ^ 2) = t ^ 2 := by
      field_simp
    rw [hcancel] at hb
    simpa [C] using hb
  have hd : (1 - r) ^ 2 + 2 * r * x ≤ C * x := by
    have hpow : (1 - r) ^ 2 ≤ t ^ 2 :=
      pow_le_pow_left₀ (sub_nonneg.mpr hr₁.le) hrsmall _
    have hx' : 2 * r * x ≤ 2 * x := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hr₁.le) hx]
    linarith
  have hD : 0 < (1 - r) * ((1 - r) ^ 2 + 2 * r * x) :=
    mul_pos (sub_pos.mpr hr₁) (by positivity)
  have hden : (1 - r) * ((1 - r) ^ 2 + 2 * r * x) ≤ t * (C * x) :=
    mul_le_mul hrsmall hd (by positivity) ht.le
  have hnum : Real.exp (-1) * x ≤ r * (1 + r) * x := by
    exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg r]) hx
  rw [geometricAngularLoss r θ hr₀ hr₁]
  change Real.exp (-1) / C / t ≤ r * (1 + r) * x /
    ((1 - r) * ((1 - r) ^ 2 + 2 * r * x))
  have heqt : Real.exp (-1) / C / t = Real.exp (-1) * x / (t * (C * x)) := by
    field_simp
  rw [heqt]
  exact (div_le_div_of_nonneg_left (by positivity) hD hden).trans
    (div_le_div_of_nonneg_right hnum hD.le)

lemma factorLogLoss (z : ℂ) (hz : ‖z‖ < 1) :
    (‖z‖ - z.re) / 4 ≤ Real.log ‖1 - z‖ - Real.log (1 - ‖z‖) := by
  let a := ‖1 - z‖
  let b := 1 - ‖z‖
  have hz₁ : z ≠ 1 := by
    intro he
    simp [he] at hz
  have ha : 0 < a := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz₁))
  have hb : 0 < b := sub_pos.mpr hz
  have ha₂ : a ^ 2 ≤ 4 := by
    have htri : a ≤ 2 := calc
      a ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ 2 := by simp; linarith
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr htri)]
  have hdiff : a ^ 2 - b ^ 2 = 2 * (‖z‖ - z.re) := by
    dsimp [a, b]
    rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_one, Complex.normSq_eq_norm_sq]
    simp only [one_mul, Complex.conj_re]
    ring
  have hratio : (‖z‖ - z.re) / 2 ≤ (a ^ 2 - b ^ 2) / a ^ 2 := by
    rw [le_div_iff₀ (pow_pos ha _), hdiff]
    calc
      _ ≤ (‖z‖ - z.re) / 2 * 4 :=
        mul_le_mul_of_nonneg_left ha₂ (by linarith [Complex.re_le_norm z])
      _ = _ := by ring
  have hlog := Real.log_le_sub_one_of_pos (div_pos (pow_pos hb 2) (pow_pos ha 2))
  rw [Real.log_div (pow_ne_zero _ hb.ne') (pow_ne_zero _ ha.ne'),
    Real.log_pow, Real.log_pow] at hlog
  have hquotient : (a ^ 2 - b ^ 2) / a ^ 2 = 1 - b ^ 2 / a ^ 2 := by
    rw [sub_div, div_self (pow_ne_zero _ ha.ne')]
  rw [hquotient] at hratio
  norm_num at hlog
  change _ ≤ Real.log a - Real.log b
  linarith

lemma finiteEulerLogLoss (z : ℂ) (hz : ‖z‖ < 1) (N : ℕ) :
    (∑ j ∈ Finset.range N, (‖z‖ ^ (j + 1) - (z ^ (j + 1)).re) / 4) ≤
      Real.log ‖∏ j ∈ Finset.range N, (1 - z ^ (j + 1))‖ -
        Real.log (∏ j ∈ Finset.range N, (1 - ‖z‖ ^ (j + 1))) := by
  have hp (j : ℕ) : ‖z‖ ^ (j + 1) < 1 :=
    pow_lt_one₀ (norm_nonneg _) hz (by omega)
  have hpos (j : ℕ) : 0 < 1 - ‖z‖ ^ (j + 1) := sub_pos.mpr (hp j)
  have hnz (j : ℕ) : z ^ (j + 1) ≠ 1 := by
    intro he
    have h := hp j
    rw [← norm_pow, he, norm_one] at h
    exact (lt_irrefl _ h)
  rw [norm_prod, Real.log_prod (fun j _ ↦ norm_ne_zero_iff.mpr
    (sub_ne_zero.mpr (Ne.symm (hnz j)))), Real.log_prod (fun j _ ↦ (hpos j).ne'),
    ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun j _ ↦ by
    simpa only [norm_pow] using factorLogLoss (z ^ (j + 1)) (by rw [norm_pow]; exact hp j)

lemma eulerLogLoss (z A : ℂ) (B : ℝ) (hz : ‖z‖ < 1)
    (hA : HasProd (fun j : ℕ ↦ 1 - z ^ (j + 1)) A) (hA₀ : A ≠ 0)
    (hB : HasProd (fun j : ℕ ↦ 1 - ‖z‖ ^ (j + 1)) B) (hB₀ : B ≠ 0) :
    (∑' j : ℕ, (‖z‖ ^ (j + 1) - (z ^ (j + 1)).re) / 4) ≤
      Real.log ‖A‖ - Real.log B := by
  have hR : Summable (fun j : ℕ ↦ ‖z‖ ^ (j + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hz)
  have hZ : Summable (fun j : ℕ ↦ z ^ (j + 1)) :=
    (summable_nat_add_iff 1).mpr (hasSum_geometric_of_norm_lt_one hz).summable
  have hS := (hR.sub (Complex.hasSum_re hZ.hasSum).summable).div_const 4
  have ha := (Real.continuousAt_log (norm_ne_zero_iff.mpr hA₀)).tendsto.comp
    (hA.tendsto_prod_nat.norm)
  have hb := (Real.continuousAt_log hB₀).tendsto.comp hB.tendsto_prod_nat
  exact le_of_tendsto_of_tendsto' hS.hasSum.tendsto_sum_nat (ha.sub hb)
    (finiteEulerLogLoss z hz)

lemma minorEulerInvBound (δ t θ : ℝ) (hδ : 0 < δ) (ht : 0 < t) (ht₁ : t ≤ 1)
    (hθ₀ : δ * t ≤ |θ|) (hθ₁ : |θ| ≤ Real.pi)
    (A : ℂ) (B : ℝ)
    (hA : HasProd (fun j : ℕ ↦ 1 -
      ((Real.exp (-t) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ (j + 1)) A)
    (hA₀ : A ≠ 0)
    (hB : HasProd (fun j : ℕ ↦ 1 - Real.exp (-t) ^ (j + 1)) B)
    (hB₀ : 0 < B) :
    ‖A⁻¹‖ ≤ B⁻¹ * Real.exp
      (-(Real.exp (-1) / (Real.pi ^ 2 / (2 * δ ^ 2) + 2) / t / 4)) := by
  let r := Real.exp (-t)
  let z : ℂ := (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
  have hr₀ : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  have hz := polar_norm r θ hr₀.le
  have hBr : HasProd (fun j : ℕ ↦ 1 - ‖z‖ ^ (j + 1)) B := by
    rw [hz]
    exact hB
  have hl := eulerLogLoss z A B (hz ▸ hr₁) hA hA₀ hBr hB₀.ne'
  have eulerShift :
      (∑' j : ℕ, (‖z‖ ^ (j + 1) - (z ^ (j + 1)).re) / 4) =
        (∑' j : ℕ, r ^ j * (1 - Real.cos ((j : ℝ) * θ))) / 4 := by
    let sequence (j : ℕ) := r ^ j * (1 - Real.cos ((j : ℝ) * θ))
    have hterm (j : ℕ) : r ^ j - (z ^ j).re = sequence j := by
      rw [show (z ^ j).re = r ^ j * Real.cos ((j : ℝ) * θ) from polar_pow_re r θ j]
      simp only [sequence, mul_sub, mul_one]
    have hr := hasSum_geometric_of_abs_lt_one (show |r| < 1 by rwa [abs_of_pos hr₀])
    have hzS := Complex.hasSum_re (hasSum_geometric_of_norm_lt_one
      (show ‖z‖ < 1 by rw [hz]; exact hr₁))
    have hs : Summable sequence := by
      simpa only [hterm] using (hr.sub hzS).summable
    have hterm' (j : ℕ) : ‖z‖ ^ (j + 1) - (z ^ (j + 1)).re = sequence (j + 1) := by
      rw [hz]; exact hterm (j + 1)
    simp only [hterm', tsum_div_const]
    congr 1
    simpa [sequence] using hs.sum_add_tsum_nat_add 1
  rw [eulerShift] at hl
  have hu := minorArcLoss δ t θ hδ ht ht₁ hθ₀ hθ₁
  change _ ≤ ∑' j : ℕ, r ^ j * (1 - Real.cos ((j : ℝ) * θ)) at hu
  have hlog := (div_le_div_of_nonneg_right hu (by norm_num : 0 ≤ (4 : ℝ))).trans hl
  apply (Real.log_le_log_iff (norm_pos_iff.mpr (inv_ne_zero hA₀))
    (mul_pos (inv_pos.mpr hB₀) (Real.exp_pos _))).mp
  rw [norm_inv, Real.log_inv, Real.log_mul (inv_ne_zero hB₀.ne') (Real.exp_ne_zero _),
    Real.log_inv, Real.log_exp]
  linarith

end Erdos1106MinorArc

end

section

/- # An exponentially accurate integral approximation at integer arguments -/

open Nat Complex MeasureTheory Set
open scoped Topology Real Interval ComplexOrder
open Erdos1106Gen Erdos1106Transform Erdos1106Contour Erdos1106Major

namespace Erdos1106Coefficient

noncomputable def mass (t s : ℝ) : ℝ := Real.sqrt (t/(2*Real.pi)) * Real.exp (2*s)
noncomputable def reflected (t u : ℝ) : ℂ :=
  exp (-(4 * (Real.pi:ℂ)^2 / ((t:ℂ)*(1+I*u))))
noncomputable def minorConstant : ℝ :=
  Real.exp (-1) / (Real.pi^2 / (2*(1/100:ℝ)^2) + 2) / 4

theorem minorConstant_pos : 0 < minorConstant := by unfold minorConstant; positivity

private theorem one_I_ne (u : ℝ) : 1+I*(u:ℂ) ≠ 0 := by
  intro h; have h' := congrArg Complex.re h; simp at h'

private theorem csqrt_scale {r : ℝ} (hr : 0 < r) {v : ℂ} (hv : v ≠ 0) :
    Complex.sqrt ((r:ℂ)*v) = (Real.sqrt r:ℂ)*Complex.sqrt v := by
  have hr0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have heq : Complex.sqrt (r:ℂ) = (Real.sqrt r:ℂ) :=
    Complex.sqrt_of_nonneg (Complex.zero_le_real.mpr hr.le)
  rw [← heq, sqrt_eq_exp (mul_ne_zero hr0 hv), sqrt_eq_exp hr0, sqrt_eq_exp hv,
    Complex.log_ofReal_mul hr hv, ← Complex.ofReal_log hr.le, add_div, Complex.exp_add]

theorem contour_on_major {n : ℕ} {t s : ℝ} (ht : 0 < t)
    (hs : t*s = Real.pi^2/6) (hn : ((n:ℝ)-1/24)*t=s) (u : ℝ) :
    contour n t (-t*u) = (mass t s:ℂ)*kernel (s:ℂ) u * (eulerDen (reflected t u))⁻¹ := by
  let v : ℂ := 1+I*u
  have hv : v ≠ 0 := one_I_ne _
  have ht0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hscale : (t:ℂ)*s = (Real.pi:ℂ)^2/6 := by exact_mod_cast hs
  have hindex : ((n:ℂ)-1/24)*t = (s:ℂ) := by
    simpa using congrArg Complex.ofReal hn
  have hpt : laplacePoint t (-t*u) = (t:ℂ)*v := by dsimp [laplacePoint,v]; push_cast; ring
  have hre : 0 < ((t:ℂ)*v).re := by simpa [v,Complex.mul_re] using ht
  have hroot : Complex.sqrt ((t:ℂ)*v/(2*Real.pi)) = (Real.sqrt (t/(2*Real.pi)):ℂ)*amplitude u := by
    rw [show (t:ℂ)*v/(2*Real.pi)=((t/(2*Real.pi):ℝ):ℂ)*v by push_cast; ring]
    exact csqrt_scale (by positivity) hv
  have hexp : (Real.pi:ℂ)^2/(6*((t:ℂ)*v)) - (t:ℂ)*v/24 + (n:ℂ)*((t:ℂ)*v) =
      2*(s:ℂ) + -((s:ℂ)/v)*(u:ℂ)^2 := by
    have h1 : (Real.pi:ℂ)^2 / (6*((t:ℂ)*v)) = (s:ℂ)/v := by
      field_simp [ht0,hv] at hscale ⊢
      linear_combination -hscale
    rw [h1, show (s:ℂ)/v - (t:ℂ)*v/24 + (n:ℂ)*((t:ℂ)*v) = (s:ℂ)/v + (((n:ℂ)-1/24)*t)*v by ring, hindex]
    field_simp [hv]
    dsimp [v]; ring_nf; simp [I_sq,sub_eq_add_neg]
  rw [contour, hpt, eta_inversion hre, hroot, kernel, mass, Complex.ofReal_mul, Complex.ofReal_exp]
  rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
  let E := (Real.pi:ℂ)^2/(6*((t:ℂ)*v)) - (t:ℂ)*v/24
  let N := (n:ℂ)*((t:ℂ)*v)
  let Q := -((s:ℂ)/v)*(u:ℂ)^2
  let D := (eulerDen (reflected t u))⁻¹
  let c : ℂ := Real.sqrt (t/(2*Real.pi))
  change c * amplitude u * exp E * D * exp N = c * exp (2*(s:ℂ)) * (amplitude u * exp Q) * D
  calc
    _ = c * amplitude u * (exp E * exp N) * D := by ring
    _ = _ := by rw [← Complex.exp_add, show E+N = 2*(s:ℂ)+Q from hexp, Complex.exp_add]; ring

theorem reflected_norm {t u : ℝ} (ht : 0 < t) (hu : |u| ≤ 1/100) :
    ‖reflected t u‖ ≤ Real.exp (-4/t) := by
  have hu2 : u^2 ≤ 1 := by
    have hu' := abs_le.mp hu
    nlinarith [mul_nonneg (sub_nonneg.mpr (show u ≤ 1 by linarith)) (show 0 ≤ 1+u by linarith)]
  have hr : (4*(Real.pi:ℂ)^2/((t:ℂ)*(1+I*(u:ℂ)))).re = (4*Real.pi^2)/(t*(1+u^2)) := by
    simp [Complex.div_re,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,pow_two]
    field_simp
  rw [reflected, Complex.norm_exp, Complex.neg_re, hr]
  apply Real.exp_le_exp.mpr
  have hπ := Real.pi_gt_three
  have hd : 0 < 1+u^2 := by positivity
  rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ ht (mul_pos ht hd)]
  nlinarith only [mul_le_mul_of_nonneg_left hu2 ht.le,
    mul_le_mul_of_nonneg_left (show 2 ≤ Real.pi^2 by nlinarith [sq_nonneg (Real.pi-3)]) ht.le]


private theorem mass_pos {t : ℝ} (ht : 0 < t) (s : ℝ) : 0 < mass t s := by
  unfold mass; positivity

private theorem reflection_small {t u : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) (hu : |u| ≤ 1/100) :
    ‖reflected t u‖ ≤ 1/4 := by
  apply (reflected_norm ht hu).trans
  have he : 4 ≤ Real.exp (4/t) := by
    have h := Real.add_one_le_exp (4/t)
    have hx : 4 ≤ 4/t := (le_div_iff₀ ht).mpr (by linarith)
    linarith
  rw [neg_div, Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num : (0:ℝ)<4)]
  linarith

private theorem kernel_real_bound {s u : ℝ} (hs : 0 < s) (hu : |u| ≤ 1/100) :
    ‖kernel (s:ℂ) u‖ ≤ 2 := by
  have hh := norm_kernel_le (s := (s:ℂ)) hs (by simp; positivity) hu
  apply hh.trans
  simp only [Complex.ofReal_re]
  have he : Real.exp (-(s/2)*u^2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
  linarith

theorem major_error {n : ℕ} {t s : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) (hs₀ : 0 < s)
    (hs : t*s = Real.pi^2/6) (hn : ((n:ℝ)-1/24)*t=s) {u : ℝ} (hu : |u| ≤ 1/100) :
    ‖contour n t (-t*u) - (mass t s:ℂ)*kernel (s:ℂ) u‖ ≤ 8*mass t s*Real.exp (-4/t) := by
  rw [contour_on_major ht hs hn]
  rw [show (mass t s:ℂ)*kernel (s:ℂ) u * (eulerDen (reflected t u))⁻¹ - (mass t s:ℂ)*kernel (s:ℂ) u =
    (mass t s:ℂ)*kernel (s:ℂ) u * ((eulerDen (reflected t u))⁻¹-1) by ring, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mass_pos ht s)]
  have herr := (euler_inv_near_zero (reflection_small ht ht₁ hu)).trans
    (mul_le_mul_of_nonneg_left (reflected_norm ht hu) (by norm_num : (0:ℝ) ≤ 4))
  calc
    _ ≤ mass t s * 2 * (4 * Real.exp (-4/t)) := mul_le_mul
      (mul_le_mul_of_nonneg_left (kernel_real_bound hs₀ hu) (mass_pos ht s).le) herr
      (norm_nonneg _) (mul_nonneg (mass_pos ht s).le (by norm_num))
    _ = _ := by ring

private theorem radial_norm_le {n : ℕ} {t s : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1)
    (hs : t*s = Real.pi^2/6) (hn : ((n:ℝ)-1/24)*t=s) : ‖contour n t 0‖ ≤ 2*mass t s := by
  have he := contour_on_major ht hs hn (0:ℝ)
  have hkernel : kernel (s:ℂ) 0 = 1 := by simp [kernel,amplitude]
  rw [mul_zero, hkernel, mul_one] at he
  have h := euler_inv_near_zero (reflection_small ht ht₁ (u := 0) (by norm_num))
  have hnorm := norm_sub_norm_le (eulerDen (reflected t 0))⁻¹ (1:ℂ)
  simp only [norm_one] at hnorm
  have heul : ‖(eulerDen (reflected t 0))⁻¹‖ ≤ 2 := by
    linarith [reflection_small ht ht₁ (u := 0) (by norm_num)]
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mass_pos ht s)]
  nlinarith [mul_le_mul_of_nonneg_left heul (mass_pos ht s).le]

private theorem contour_norm {n : ℕ} {t θ : ℝ} :
    ‖contour n t θ‖ =
      ‖(eulerDen ((Real.exp (-t):ℂ)*exp ((θ:ℂ)*I)))⁻¹‖ * Real.exp ((n:ℝ)*t) := by
  have h : exp (-(laplacePoint t θ)) = (Real.exp (-t):ℂ)*exp ((θ:ℂ)*I) := by
    rw [laplacePoint, neg_sub, sub_eq_neg_add, Complex.exp_add]; simp [mul_comm]
  rw [contour, h, norm_mul, Complex.norm_exp]
  congr 2
  simp [laplacePoint,Complex.mul_re]

theorem minor_bound {n : ℕ} {t s θ : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1)
    (hs : t*s = Real.pi^2/6) (hn : ((n:ℝ)-1/24)*t=s)
    (hθ : (1/100:ℝ)*t ≤ |θ|) (hπ : |θ| ≤ Real.pi) :
    ‖contour n t θ‖ ≤ 2 * mass t s * Real.exp (-minorConstant/t) := by
  let r := Real.exp (-t)
  let z : ℂ := (r:ℂ)*exp ((θ:ℂ)*I)
  have hr₀ : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  have hz : ‖z‖ < 1 := by simpa [z,Complex.norm_exp,abs_of_pos hr₀] using hr₁
  obtain ⟨B, hBpos, hB,hE⟩ := real_den hr₀.le hr₁
  have hA := (ModularForm.multipliable_one_sub_pow hz).hasProd
  have h := Erdos1106MinorArc.minorEulerInvBound (1/100) t θ (by norm_num) ht ht₁ hθ hπ
    (eulerDen z) B hA (eulerDen_ne_zero hz) hB hBpos
  have hrad := radial_norm_le ht ht₁ hs hn
  rw [contour_norm] at hrad ⊢
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one] at hrad
  change ‖(eulerDen (r:ℂ))⁻¹‖ * Real.exp ((n:ℝ)*t) ≤ _ at hrad
  rw [hE, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hBpos] at hrad
  have heq : -(Real.exp (-1) / (Real.pi^2/(2*(1/100:ℝ)^2)+2)/t/4) = -minorConstant/t := by
    unfold minorConstant; ring
  rw [heq] at h
  change ‖(eulerDen z)⁻¹‖ * Real.exp ((n:ℝ)*t) ≤ _
  calc
    _ ≤ (B⁻¹ * Real.exp (-minorConstant/t))*Real.exp ((n:ℝ)*t) := by gcongr
    _ = (B⁻¹ * Real.exp ((n:ℝ)*t))*Real.exp (-minorConstant/t) := by ring
    _ ≤ _ := by gcongr


private theorem integral_kernel_scaled {t : ℝ} (ht : 0 < t) (s : ℂ) :
    (∫ θ in -(t/100)..(t/100), kernel s (-θ/t)) = (t:ℂ)*saddle s := by
  have h1 : ∫ u in -(1/100:ℝ)..(1/100), kernel s u = saddle s := by
    rw [saddle,intervalIntegral.integral_add (f := kernel s) (g := fun u:ℝ ↦ kernel s (-u)) ((continuous_kernel_right s).intervalIntegrable ..)
      (((continuous_kernel_right s).comp continuous_neg).intervalIntegrable ..),
      intervalIntegral.integral_comp_neg, neg_zero, add_comm]
    exact (intervalIntegral.integral_add_adjacent_intervals
      ((continuous_kernel_right s).intervalIntegrable ..)
      ((continuous_kernel_right s).intervalIntegrable ..)).symm
  rw [show (fun θ : ℝ ↦ kernel s (-θ/t)) = (fun θ : ℝ ↦ kernel s ((-1/t)*θ)) by funext θ; congr 1; ring]
  rw [intervalIntegral.integral_comp_mul_left _ (by positivity : -1/t ≠ 0),
    show (-1/t)*(-(t/100))=(1/100:ℝ) by field_simp,
    show (-1/t)*(t/100)= -(1/100:ℝ) by field_simp,
    intervalIntegral.integral_symm (a := -(1/100)) (b := 1/100), h1,
    show (-1/t)⁻¹ = -t by field_simp, Complex.real_smul, Complex.ofReal_neg, neg_mul_neg]

/-- The coefficient is uniformly exponentially close to the primary saddle integral. -/
theorem coefficient_error :
    ∃ k : ℝ, 0 < k ∧ ∀ (n : ℕ) (t s : ℝ), 0 < t → t ≤ 1 →
      t*s = Real.pi^2/6 → ((n:ℝ)-1/24)*t=s →
      ‖((2*Real.pi:ℝ):ℂ)*(partitionNumber n:ℂ) -
        ((t*mass t s:ℝ):ℂ)*saddle (s:ℂ)‖ ≤ (20*Real.pi)*mass t s*Real.exp (-k/t) := by
  let k := min (4:ℝ) minorConstant
  refine ⟨k, lt_min (by norm_num) minorConstant_pos, ?_⟩
  intro n t s ht ht₁ hs hn
  have hspos : 0 < s := by
    have h := Real.pi_pos
    by_contra! hh
    have hnon := mul_nonpos_of_nonneg_of_nonpos ht.le hh
    rw [hs] at hnon
    exact (not_lt.mpr hnon) (by positivity)
  let d := t/100
  let M := mass t s
  let C := 8*M*Real.exp (-k/t)
  have hd : 0 < d := by dsimp [d]; positivity
  have hdπ : d ≤ Real.pi := by dsimp [d]; linarith [Real.pi_gt_three]
  have hM : 0 < M := mass_pos ht s
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let F := contour n t
  let G (θ : ℝ) := (M:ℂ)*kernel (s:ℂ) (-θ/t)
  have hF : Continuous F := continuous_contour n ht
  have hG : Continuous G := continuous_const.mul ((continuous_kernel_right (s:ℂ)).comp (by fun_prop))
  have hGint : (∫ θ in -d..d, G θ) = ((t*mass t s:ℝ):ℂ)*saddle (s:ℂ) := by
    dsimp [G,d,M]
    rw [intervalIntegral.integral_const_mul,integral_kernel_scaled ht, Complex.ofReal_mul]
    ring
  have ham (θ : ℝ) (hθ : |θ| ≤ d) : ‖F θ - G θ‖ ≤ C := by
    have hu : |-θ/t| ≤ 1/100 := by
      rw [abs_div,abs_neg,abs_of_pos ht,div_le_iff₀ ht]; dsimp [d] at hθ; linarith
    have hh := major_error ht ht₁ hspos hs hn hu
    rw [show -t*(-θ/t)=θ by field_simp] at hh
    apply hh.trans
    dsimp [C,M]
    gcongr
    exact min_le_left _ _
  have hmn (θ : ℝ) (hθ : d ≤ |θ|) (hθπ : |θ| ≤ Real.pi) : ‖F θ‖ ≤ C := by
    have hδ : (1/100:ℝ)*t ≤ |θ| := by dsimp [d] at hθ; linarith
    apply (minor_bound ht ht₁ hs hn hδ hθπ).trans
    dsimp [C,M]
    gcongr
    · norm_num
    · exact min_le_right _ _
  have hleft : ‖∫ θ in -Real.pi..-d, F θ‖ ≤ C * (Real.pi-d) := by
    have hab : -Real.pi ≤ -d := neg_le_neg hdπ
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := -Real.pi) (b := -d) (f := F) (C := C) (by
      intro θ hθ; rw [Set.uIoc_of_le hab] at hθ
      apply hmn
      · rw [abs_of_nonpos (by linarith [hθ.2])]; linarith [hθ.2]
      · rw [abs_of_nonpos (by linarith [hθ.2])]; linarith [hθ.1])
    rwa [abs_of_nonneg (sub_nonneg.mpr hab), show -d- -Real.pi = Real.pi-d by ring] at hh
  have hright : ‖∫ θ in d..Real.pi, F θ‖ ≤ C * (Real.pi-d) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := d) (b := Real.pi) (f := F) (C := C) (by
      intro θ hθ; rw [Set.uIoc_of_le hdπ] at hθ
      apply hmn <;> rw [abs_of_pos (hd.trans hθ.1)]
      · exact hθ.1.le
      · exact hθ.2)
    rwa [abs_of_nonneg (sub_nonneg.mpr hdπ)] at hh
  have hmid : ‖∫ θ in -d..d, F θ-G θ‖ ≤ C*(2*d) := by
    have hab : -d ≤ d := by linarith
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := -d) (b := d) (f := fun θ ↦ F θ-G θ) (C := C) (by
      intro θ hθ; rw [Set.uIoc_of_le hab] at hθ; exact ham θ (abs_le.mpr ⟨hθ.1.le,hθ.2⟩))
    rwa [abs_of_nonneg (sub_nonneg.mpr hab), show d- -d=2*d by ring] at hh
  let l := ∫ θ in -Real.pi..-d, F θ
  let m := ∫ θ in -d..d, F θ-G θ
  let r := ∫ θ in d..Real.pi, F θ
  have hall : l + m + r = ((2*Real.pi:ℝ):ℂ)*(partitionNumber n:ℂ) -
      ((t*mass t s:ℝ):ℂ)*saddle (s:ℂ) := by
    dsimp only [l,m,r]
    rw [← integral_contour n ht, ← hGint, intervalIntegral.integral_sub (hF.intervalIntegrable ..) (hG.intervalIntegrable ..)]
    have h₁ := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hF.intervalIntegrable (-Real.pi) (-d)) (hF.intervalIntegrable (-d) d)
    have h₂ := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hF.intervalIntegrable (-Real.pi) d) (hF.intervalIntegrable d Real.pi)
    change _ = (∫ θ in -Real.pi..Real.pi, F θ) - _
    rw [← h₂,← h₁]
    abel
  rw [← hall]
  calc
    _ ≤ ‖l‖+‖m‖+‖r‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le l m) (le_refl ‖r‖))
    _ ≤ C*(Real.pi-d)+C*(2*d)+C*(Real.pi-d) := by gcongr
    _ ≤ _ := by
      dsimp [C,M]
      nlinarith only [mul_nonneg (mul_nonneg Real.pi_pos.le (mass_pos ht s).le) (Real.exp_pos (-k/t)).le]

end Erdos1106Coefficient

end

section

/-
# Smooth interpolation and partition-number differences

A derivative bound for a smooth interpolation controls its finite differences.
This file provides the generalized mean value theorem and relates real-variable
differences to differences of the sampled natural-index sequence.
-/

namespace Erdos1106DifferenceTransfer

open Set Filter
open scoped Topology

lemma hasDerivAt_iterate_fwdDiff (jet : ℕ → ℝ → ℝ) (X : ℝ)
    (hj : ∀ i x, X < x → HasDerivAt (jet i) (jet (i + 1) x) x)
    (r i : ℕ) (x : ℝ) (hx : X < x) :
    HasDerivAt (((fwdDiff 1)^[r]) (jet i)) (((fwdDiff 1)^[r]) (jet (i + 1)) x) x := by
  induction r generalizing x with
  | zero => simpa using hj i x hx
  | succ r ih =>
    simp only [Function.iterate_succ_apply', fwdDiff]
    exact ((ih (x + 1) (by linarith)).comp_add_const x 1).sub (ih x hx)

lemma fwdDiff_eq_jet_at (jet : ℕ → ℝ → ℝ) (X : ℝ)
    (hj : ∀ i x, X < x → HasDerivAt (jet i) (jet (i + 1) x) x)
    (r i : ℕ) (x : ℝ) (hx : X < x) :
    ∃ y ∈ Icc x (x + r), ((fwdDiff 1)^[r] (jet i)) x = jet (i + r) y := by
  induction r generalizing x i with
  | zero => exact ⟨x, by simp, by simp⟩
  | succ r ih =>
    obtain ⟨y, hy, heq⟩ := exists_hasDerivAt_eq_slope (((fwdDiff 1)^[r]) (jet i))
      (((fwdDiff 1)^[r]) (jet (i + 1))) (show x < x + 1 by linarith)
      (fun z hz ↦ (hasDerivAt_iterate_fwdDiff jet X hj r i z (hx.trans_le hz.1)).continuousAt.continuousWithinAt)
      (fun z hz ↦ hasDerivAt_iterate_fwdDiff jet X hj r i z (hx.trans hz.1))
    obtain ⟨z, hz, hz_eq⟩ := ih (i + 1) y (hx.trans hy.1)
    refine ⟨z, ⟨hy.1.le.trans hz.1, ?_⟩, ?_⟩
    · push_cast
      linarith [hz.2, hy.2]
    · have hden : x + 1 - x = 1 := by ring
      rw [hden, div_one] at heq
      rw [Function.iterate_succ_apply', fwdDiff, ← heq, hz_eq]
      congr 1
      omega

lemma fwdDiff_cast_nat (f : ℝ → ℝ) (r n : ℕ) :
    ((fwdDiff 1)^[r] (fun j : ℕ ↦ f j)) n = ((fwdDiff 1)^[r] f) n := by
  induction r generalizing n with
  | zero => rfl
  | succ r ih => simp [Function.iterate_succ_apply', fwdDiff, ih]

lemma sampledJetBounds (jet : ℕ → ℝ → ℝ) (X Y : ℝ)
    (hj : ∀ i x, X < x → HasDerivAt (jet i) (jet (i + 1) x) x)
    (r : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbound : ∀ x > Y, a * Real.sqrt x ≤ x ^ r * |jet r x| ∧
      x ^ r * |jet r x| ≤ b * Real.sqrt x) :
    ∀ᶠ m : ℕ in atTop,
      a / 2 ^ r * m ≤ (m : ℝ) ^ (2 * r) *
        |((fwdDiff 1)^[r] (fun n : ℕ ↦ jet 0 n)) (m ^ 2)| ∧
      (m : ℝ) ^ (2 * r) * |((fwdDiff 1)^[r] (fun n : ℕ ↦ jet 0 n)) (m ^ 2)| ≤
        (2 * b) * m := by
  have hc : Tendsto (fun m : ℕ ↦ (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hc.eventually_gt_atTop (max X Y), eventually_ge_atTop (r + 1)] with m hm hmr
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hrm : (r : ℝ) ≤ m := by exact_mod_cast (show r ≤ m by omega)
  have hmpow : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm1) (show (0 : ℝ) ≤ m by positivity)]
  have hx : X < (m : ℝ) ^ 2 := ((le_max_left _ _).trans_lt hm).trans_le hmpow
  have hy : Y < (m : ℝ) ^ 2 := ((le_max_right _ _).trans_lt hm).trans_le hmpow
  obtain ⟨y, hyI, heq⟩ := fwdDiff_eq_jet_at jet X hj r 0 ((m : ℝ) ^ 2) hx
  have h_y_upper : y ≤ 2 * (m : ℝ) ^ 2 := by linarith [hyI.2]
  have hslo : (m : ℝ) ≤ Real.sqrt y := by
    simpa only [Real.sqrt_sq (Nat.cast_nonneg m)] using Real.sqrt_le_sqrt hyI.1
  have hsup : Real.sqrt y ≤ 2 * (m : ℝ) := by
    have hy' : y ≤ (2 * (m : ℝ)) ^ 2 := by nlinarith [sq_nonneg (m : ℝ)]
    simpa only [Real.sqrt_sq (by positivity : 0 ≤ 2 * (m : ℝ))] using Real.sqrt_le_sqrt hy'
  have hpowlower : (m : ℝ) ^ (2 * r) ≤ y ^ r := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hyI.1 r
  have hpowupper : y ^ r ≤ 2 ^ r * (m : ℝ) ^ (2 * r) := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ ((by positivity : 0 ≤ (m : ℝ) ^ 2).trans hyI.1) h_y_upper r
  obtain ⟨hlower, hupper⟩ := hbound y (hy.trans_le hyI.1)
  rw [fwdDiff_cast_nat]
  push_cast
  simp only [zero_add] at heq
  rw [heq]
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ r)]
    calc
      a * (m : ℝ) ≤ a * Real.sqrt y := mul_le_mul_of_nonneg_left hslo ha
      _ ≤ y ^ r * |jet r y| := hlower
      _ ≤ (2 ^ r * (m : ℝ) ^ (2 * r)) * |jet r y| :=
        mul_le_mul_of_nonneg_right hpowupper (abs_nonneg _)
      _ = _ := by ring
  · calc
      (m : ℝ) ^ (2 * r) * |jet r y| ≤ y ^ r * |jet r y| :=
        mul_le_mul_of_nonneg_right hpowlower (abs_nonneg _)
      _ ≤ b * Real.sqrt y := hupper
      _ ≤ b * (2 * (m : ℝ)) := mul_le_mul_of_nonneg_left hsup hb
      _ = _ := by ring

lemma fwdDiff_expError (e : ℕ → ℝ) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 ≤ ε) (N : ℕ)
    (he : ∀ n ≥ N, |e n| ≤ C * Real.exp (-ε * Real.sqrt (n : ℝ)))
    (r n : ℕ) (hn : N ≤ n) :
    |((fwdDiff 1)^[r] e) n| ≤ 2 ^ r * C * Real.exp (-ε * Real.sqrt (n : ℝ)) := by
  induction r generalizing n with
  | zero => simpa using he n hn
  | succ r ih =>
    rw [Function.iterate_succ_apply', fwdDiff]
    have hmono : Real.exp (-ε * Real.sqrt (↑(n + 1) : ℝ)) ≤
        Real.exp (-ε * Real.sqrt (n : ℝ)) := by
      apply Real.exp_monotone
      exact mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ n))
        (neg_nonpos.mpr hε)
    calc
      _ ≤ |((fwdDiff 1)^[r] e) (n + 1)| + |((fwdDiff 1)^[r] e) n| := by
        simpa using abs_sub_le (((fwdDiff 1)^[r] e) (n + 1)) 0 (((fwdDiff 1)^[r] e) n)
      _ ≤ 2 ^ r * C * Real.exp (-ε * Real.sqrt (↑(n + 1) : ℝ)) +
          2 ^ r * C * Real.exp (-ε * Real.sqrt (n : ℝ)) :=
        add_le_add (ih (n + 1) (hn.trans (Nat.le_succ n))) (ih n hn)
      _ ≤ 2 ^ r * C * Real.exp (-ε * Real.sqrt (n : ℝ)) +
          2 ^ r * C * Real.exp (-ε * Real.sqrt (n : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hmono
          (show 0 ≤ (2 : ℝ) ^ r * C by positivity)) le_rfl
      _ = _ := by rw [pow_succ]; ring

lemma squareSampleError (g s : ℕ → ℝ) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) (N : ℕ)
    (he : ∀ n ≥ N, |g n - s n| ≤ C * Real.exp (-ε * Real.sqrt (n : ℝ)))
    (r : ℕ) (a b : ℝ) (ha : 0 < a)
    (hs : ∀ᶠ m : ℕ in atTop,
      a * m ≤ (m : ℝ) ^ (2 * r) * |((fwdDiff 1)^[r] s) (m ^ 2)| ∧
      (m : ℝ) ^ (2 * r) * |((fwdDiff 1)^[r] s) (m ^ 2)| ≤ b * m) :
    ∀ᶠ m : ℕ in atTop,
      (a / 2) * m ≤ (m : ℝ) ^ (2 * r) * |((fwdDiff 1)^[r] g) (m ^ 2)| ∧
      (m : ℝ) ^ (2 * r) * |((fwdDiff 1)^[r] g) (m ^ 2)| ≤ (b + a / 2) * m := by
  let e (n : ℕ) := g n - s n
  have hx : g = s + e := by ext n; simp [e]
  have hh : Tendsto (fun m : ℕ ↦ ((m : ℝ) ^ (2 * r)) *
      (2 ^ r * C * Real.exp (-ε * (m : ℝ)))) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      ((2 * r : ℕ) : ℝ) ε hε).comp tendsto_natCast_atTop_atTop).const_mul ((2 : ℝ) ^ r * C)
    simp only [Real.rpow_natCast, Function.comp_def, mul_zero] at h
    exact h.congr fun _ ↦ by ring
  filter_upwards [hs, hh.eventually (gt_mem_nhds (show 0 < a / 2 by linarith)),
    eventually_ge_atTop (N + 1)] with m hm hsmall hNm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hNm' : N ≤ m ^ 2 := by
    have hmN : N ≤ m := by omega
    simpa [pow_two] using hmN.trans
      (Nat.le_mul_of_pos_left m (show 0 < m by omega))
  have hE := fwdDiff_expError e C ε hC hε.le N he r _ hNm'
  rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg m)] at hE
  let u := ((fwdDiff 1)^[r] s) (m ^ 2)
  let v := ((fwdDiff 1)^[r] e) (m ^ 2)
  let q := (m : ℝ) ^ (2 * r)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hv : q * |v| ≤ (a / 2) * m := by
    apply (mul_le_mul_of_nonneg_left hE hq).trans
    have hhalf : 0 ≤ a / 2 := by positivity
    exact hsmall.le.trans (by nlinarith [mul_nonneg hhalf (sub_nonneg.mpr hm1)])
  have hU : q * |u + v| ≤ q * |u| + q * |v| := by
    simpa only [mul_add] using mul_le_mul_of_nonneg_left (abs_add_le u v) hq
  have hL : q * |u| ≤ q * |u + v| + q * |v| := by
    have habs : |u| ≤ |u + v| + |v| := by
      simpa using abs_sub_le (u + v) 0 v
    simpa only [mul_add] using mul_le_mul_of_nonneg_left habs hq
  rw [hx, fwdDiff_iter_add, Pi.add_apply]
  change (a / 2) * m ≤ q * |u + v| ∧ q * |u + v| ≤ (b + a / 2) * m
  change a * m ≤ q * |u| ∧ q * |u| ≤ b * m at hm
  obtain ⟨hmL, hmU⟩ := hm
  constructor <;> linarith

end Erdos1106DifferenceTransfer

end

section

/-
# Derivative estimates on a sector

An analytic function of logarithmic growth has small derivatives on the
interior real ray, by Cauchy's estimate on discs of radius proportional to the
real part. Subtracting the square-root term makes this applicable to the
logarithm of the partition-number approximation.
-/

namespace Erdos1106Sector

open Set Metric Filter
open scoped Topology

def sector (X ε : ℝ) : Set ℂ :=
  {w | X < w.re ∧ |w.im| < ε * w.re}

lemma isOpen_sector (X ε : ℝ) : IsOpen (sector X ε) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_im.abs (continuous_const.mul Complex.continuous_re))

lemma disk_in_sector (X ε x : ℝ) (hε : 0 < ε) (hx : max 2 (2 * X + 2) < x) :
    closedBall (x : ℂ) (min (1 / 4) (ε / 4) * x) ⊆ sector X ε := by
  let κ := min (1 / 4) (ε / 4)
  have hx₀ : 0 < x := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hx)
  have hxX : 2 * X + 2 < x := (le_max_right _ _).trans_lt hx
  intro z hz
  have hzn : ‖z - (x : ℂ)‖ ≤ κ * x := by
    simpa [κ, dist_eq_norm] using mem_closedBall.mp hz
  have hzr : |z.re - x| ≤ κ * x := by
    simpa only [Complex.sub_re, Complex.ofReal_re] using
      (Complex.abs_re_le_norm (z - (x : ℂ))).trans hzn
  have hzi : |z.im| ≤ κ * x := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using
      (Complex.abs_im_le_norm (z - (x : ℂ))).trans hzn
  have hκ : κ ≤ 1 / 4 := min_le_left _ _
  have hκ' : κ ≤ ε / 4 := min_le_right _ _
  have hquarter : κ * x ≤ x / 4 := by
    calc
      κ * x ≤ (1 / 4 : ℝ) * x := mul_le_mul_of_nonneg_right hκ hx₀.le
      _ = x / 4 := by ring
  have hzre : x / 2 < z.re := by linarith [(abs_le.mp hzr).1]
  refine ⟨by linarith, ?_⟩
  calc
    |z.im| ≤ κ * x := hzi
    _ ≤ (ε / 4) * x := mul_le_mul_of_nonneg_right hκ' hx₀.le
    _ < ε * z.re := by nlinarith [mul_pos hε (sub_pos.mpr hzre), mul_pos hε hx₀]

lemma cauchySector (G : ℂ → ℂ) (X ε C x : ℝ) (hε : 0 < ε) (hC : 0 ≤ C)
    (hG : DifferentiableOn ℂ G (sector X ε))
    (hbound : ∀ z ∈ sector X ε, ‖G z‖ ≤ C * (1 + Real.log ‖z‖))
    (hx : max 2 (2 * X + 2) < x) (r : ℕ) :
    ‖iteratedDeriv r G (x : ℂ)‖ ≤
      r.factorial * (C * (1 + Real.log (2 * x))) / (min (1 / 4) (ε / 4) * x) ^ r := by
  let κ := min (1 / 4) (ε / 4)
  have hx₀ : 0 < x := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hx)
  have hκ₀ : 0 < κ := lt_min (by norm_num) (by positivity)
  have hκ₁ : κ ≤ 1 := (min_le_left (1 / 4 : ℝ) _).trans (by norm_num)
  have hsubset := disk_in_sector X ε x hε hx
  refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le r (mul_pos hκ₀ hx₀)
    ((hG.mono (closure_ball_subset_closedBall.trans hsubset)).diffContOnCl) ?_
  intro z hz
  have hzne : z ≠ 0 := by
    have hz' := (hsubset (sphere_subset_closedBall hz)).1
    intro hh
    rw [hh, Complex.zero_re] at hz'
    have ht' := mem_sphere.mp hz
    rw [hh, dist_comm, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx₀] at ht'
    nlinarith [mul_pos (show 0 < 1 - κ by dsimp [κ]; linarith [min_le_left (1 / 4 : ℝ) (ε / 4)]) hx₀]
  have hnorm : ‖z‖ ≤ 2 * x := by
    have hdist : ‖z - (x : ℂ)‖ = κ * x := by simpa [dist_eq_norm, κ] using mem_sphere.mp hz
    calc
      _ ≤ ‖z - (x : ℂ)‖ + ‖(x : ℂ)‖ := by
        simpa using norm_add_le (z - (x : ℂ)) (x : ℂ)
      _ = κ * x + x := by simp [hdist, abs_of_pos hx₀]
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hκ₁) hx₀.le]
  refine (hbound z (hsubset (sphere_subset_closedBall hz))).trans ?_
  exact mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) (Real.log_le_log
    (norm_pos_iff.mpr hzne) hnorm)) hC

noncomputable def sqrtCoefficient (c : ℝ) : ℕ → ℝ
  | 0 => c
  | r + 1 => sqrtCoefficient c r * (1 / 2 - (r : ℝ))

lemma sqrtCoefficient_ne_zero (c : ℝ) (hc : c ≠ 0) (r : ℕ) :
    sqrtCoefficient c r ≠ 0 := by
  induction r with
  | zero => exact hc
  | succ r ih =>
    unfold sqrtCoefficient
    apply mul_ne_zero ih
    cases r with
    | zero => norm_num
    | succ r =>
      have : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos r
      linarith

lemma hasDerivAt_sqrtJet (c : ℝ) (r : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ sqrtCoefficient c r * y ^ (1 / 2 - (r : ℝ)))
      (sqrtCoefficient c (r + 1) * x ^ (1 / 2 - ((r + 1 : ℕ) : ℝ))) x := by
  have hf := (Real.hasDerivAt_rpow_const (p := 1 / 2 - (r : ℝ)) (Or.inl hx.ne')).const_mul
    (sqrtCoefficient c r)
  have he : sqrtCoefficient c (r + 1) * x ^ (1 / 2 - ((r + 1 : ℕ) : ℝ)) =
      sqrtCoefficient c r * ((1 / 2 - (r : ℝ)) * x ^ (1 / 2 - (r : ℝ) - 1)) := by
    rw [sqrtCoefficient, show 1 / 2 - ((r + 1 : ℕ) : ℝ) = 1 / 2 - (r : ℝ) - 1 by
      push_cast; ring]
    ring
  rw [he]
  exact hf

noncomputable def interpolatingJet (G : ℂ → ℂ) (c : ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  sqrtCoefficient c r * x ^ (1 / 2 - (r : ℝ)) + (iteratedDeriv r G (x : ℂ)).re

lemma hasDerivAt_interpolatingJet (G : ℂ → ℂ) (c X ε : ℝ) (hε : 0 < ε)
    (hG : DifferentiableOn ℂ G (sector X ε)) (r : ℕ) (x : ℝ) (hx : max 0 X < x) :
    HasDerivAt (interpolatingJet G c r) (interpolatingJet G c (r + 1) x) x := by
  have hx₀ : 0 < x := (le_max_left _ _).trans_lt hx
  have hxS : (x : ℂ) ∈ sector X ε := by
    exact ⟨by simpa using (le_max_right (0 : ℝ) X).trans_lt hx, by simpa using mul_pos hε hx₀⟩
  have hs := (hG.analyticOnNhd (isOpen_sector X ε)).iterated_deriv r
  have hd := (hs _ hxS).differentiableAt.hasDerivAt.real_of_complex
  have hd' : HasDerivAt (fun w : ℝ ↦ (iteratedDeriv r G (w : ℂ)).re)
      (iteratedDeriv (r + 1) G (x : ℂ)).re x := by
    simpa only [iteratedDeriv_eq_iterate, Function.iterate_succ_apply'] using hd
  exact (hasDerivAt_sqrtJet c r x hx₀).add hd' 

private lemma tendsto_logCorrection_div_sqrt :
    Tendsto (fun x : ℝ ↦ (1 + Real.log (2 * x)) / Real.sqrt x) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ ↦ Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hc := Real.tendsto_sqrt_atTop.const_div_atTop (1 + Real.log 2)
  apply (by simpa only [zero_add] using hc.add hlog :
    Tendsto (fun x : ℝ ↦ (1 + Real.log 2) / Real.sqrt x + Real.log x / Real.sqrt x)
      atTop (𝓝 0)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx.ne', ← add_div]
  congr 1
  ring

lemma eventually_interpolatingJetBounds (G : ℂ → ℂ) (c X ε C : ℝ)
    (hc : c ≠ 0) (hε : 0 < ε) (hC : 0 ≤ C)
    (hG : DifferentiableOn ℂ G (sector X ε))
    (hbound : ∀ z ∈ sector X ε, ‖G z‖ ≤ C * (1 + Real.log ‖z‖))
    (r : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      (|sqrtCoefficient c r| / 2) * Real.sqrt x ≤ x ^ r * |interpolatingJet G c r x| ∧
        x ^ r * |interpolatingJet G c r x| ≤ (2 * |sqrtCoefficient c r|) * Real.sqrt x := by
  let κ := min (1 / 4) (ε / 4)
  let K := (r.factorial : ℝ) * C / κ ^ r
  let d := sqrtCoefficient c r
  have hκ : 0 < κ := lt_min (by norm_num) (by positivity)
  have hd : 0 < |d| := abs_pos.mpr (sqrtCoefficient_ne_zero c hc r)
  have hlim : Tendsto (fun x : ℝ ↦ K * ((1 + Real.log (2 * x)) / Real.sqrt x))
      atTop (𝓝 0) := by simpa using tendsto_logCorrection_div_sqrt.const_mul K
  filter_upwards [eventually_gt_atTop (max 2 (2 * X + 2)),
    hlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < |d| / 2))] with x hx hsmall
  have hx₀ : 0 < x := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hx)
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx₀
  have hsmall' : K * (1 + Real.log (2 * x)) ≤ (|d| / 2) * Real.sqrt x := by
    rw [← mul_div_assoc, div_lt_iff₀ hsx] at hsmall
    exact hsmall.le
  have hres : x ^ r * |(iteratedDeriv r G (x : ℂ)).re| ≤
      (|d| / 2) * Real.sqrt x := by
    calc
      _ ≤ x ^ r * ‖iteratedDeriv r G (x : ℂ)‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
      _ ≤ x ^ r * ((r.factorial : ℝ) * (C * (1 + Real.log (2 * x))) / (κ * x) ^ r) :=
        mul_le_mul_of_nonneg_left (cauchySector G X ε C x hε hC hG hbound hx r) (by positivity)
      _ = K * (1 + Real.log (2 * x)) := by
        rw [mul_pow]
        dsimp [K]
        field_simp
      _ ≤ _ := hsmall'
  have hlead : x ^ r * |d * x ^ (1 / 2 - (r : ℝ))| = |d| * Real.sqrt x := by
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx₀ _), Real.sqrt_eq_rpow,
      Real.rpow_sub hx₀, Real.rpow_natCast]
    field_simp
  let u := d * x ^ (1 / 2 - (r : ℝ))
  let v := (iteratedDeriv r G (x : ℂ)).re
  have hup : |u + v| ≤ |u| + |v| := abs_add_le _ _
  have hlo : |u| ≤ |u + v| + |v| := by
    simpa using abs_sub_le (u + v) 0 v
  change (|d| / 2) * Real.sqrt x ≤ x ^ r * |u + v| ∧
    x ^ r * |u + v| ≤ (2 * |d|) * Real.sqrt x
  have hup' := mul_le_mul_of_nonneg_left hup (show 0 ≤ x ^ r by positivity)
  have hlo' := mul_le_mul_of_nonneg_left hlo (show 0 ≤ x ^ r by positivity)
  rw [mul_add] at hup' hlo'
  change x ^ r * |u| = |d| * Real.sqrt x at hlead
  change x ^ r * |v| ≤ (|d| / 2) * Real.sqrt x at hres
  have hpositive : 0 ≤ |d| * Real.sqrt x := by positivity
  constructor <;> linarith

end Erdos1106Sector

end

section

/-
# Transfer from a sectorial interpolation

An analytic interpolation with a square-root leading term, a logarithmic
sector bound on the remainder, and exponentially small error on the integers
gives the two-sided forward-difference estimates used in the arithmetic
reduction of Erdős Problem 1106(i).
-/

namespace Erdos1106AnalyticTransfer

open Erdos1106Sector Erdos1106DifferenceTransfer Filter
open scoped Topology

lemma sectorialInterpolation_implies_squareBounds (g : ℕ → ℝ) (F : ℂ → ℂ)
    (c X ε C ε' C' : ℝ) (N : ℕ)
    (hc : c ≠ 0) (hX : 0 ≤ X) (hε : 0 < ε) (hC : 0 ≤ C) (hε' : 0 < ε') (hC' : 0 ≤ C')
    (hF : DifferentiableOn ℂ F (sector X ε))
    (hbound : ∀ z ∈ sector X ε, ‖F z - (c : ℂ) * Complex.sqrt z‖ ≤ C * (1 + Real.log ‖z‖))
    (hclose : ∀ n ≥ N, |g n - (F (n : ℂ)).re| ≤ C' * Real.exp (-ε' * Real.sqrt (n : ℝ))) :
    ∀ r : ℕ, ∃ A B : ℝ, 0 < A ∧ ∀ᶠ m : ℕ in atTop,
      A * m ≤ (m : ℝ) ^ (2 * r) * |((fwdDiff 1)^[r] g) (m ^ 2)| ∧
      (m : ℝ) ^ (2 * r) * |((fwdDiff 1)^[r] g) (m ^ 2)| ≤ B * m := by
  let G (z : ℂ) := F z - (c : ℂ) * Complex.sqrt z
  have hG : DifferentiableOn ℂ G (sector X ε) := by
    refine hF.sub (DifferentiableOn.const_mul ?_ _)
    exact Complex.differentiableOn_sqrt.mono fun _ h ↦
      Complex.mem_slitPlane_iff.mpr (Or.inl (hX.trans_lt h.1))
  let jet := interpolatingJet G c
  have hjet (i : ℕ) (x : ℝ) (hx : max 0 X < x) :
      HasDerivAt (jet i) (jet (i + 1) x) x :=
    hasDerivAt_interpolatingJet G c X ε hε hG i x hx
  let sample (n : ℕ) := jet 0 n
  have hsample (n : ℕ) : sample n = (F (n : ℂ)).re := by
    have hsqrt : (Complex.sqrt (n : ℂ)).re = Real.sqrt (n : ℝ) := by
      simpa only [Complex.ofReal_natCast] using
        (Complex.re_sqrt_ofReal (a := (n : ℝ)))
    simp only [sample, jet, interpolatingJet, sqrtCoefficient, Nat.cast_zero, sub_zero,
      iteratedDeriv_zero, G, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, ← Real.sqrt_eq_rpow,
      Complex.ofReal_natCast, hsqrt]
    ring
  intro r
  obtain ⟨Y, hY⟩ := eventually_atTop.1
    (eventually_interpolatingJetBounds G c X ε C hc hε hC hG hbound r)
  let a := |sqrtCoefficient c r| / 2
  let b := 2 * |sqrtCoefficient c r|
  have ha : 0 < a := div_pos (abs_pos.mpr (sqrtCoefficient_ne_zero c hc r)) (by norm_num)
  have hs := sampledJetBounds jet (max 0 X) Y hjet r a b ha.le (by dsimp [b]; positivity)
    (fun x hx ↦ hY x hx.le)
  have ha' : 0 < a / 2 ^ r := div_pos ha (by positivity)
  refine ⟨(a / 2 ^ r) / 2, 2 * b + (a / 2 ^ r) / 2, div_pos ha' (by norm_num), ?_⟩
  apply squareSampleError g sample C' ε' hC' hε' N ?_ r _ _ ha' hs
  intro n hn
  rw [hsample]
  exact hclose n hn

end Erdos1106AnalyticTransfer

end

section

/- # Logarithmic comparison with the saddle integral -/

namespace Erdos1106LogModel

open Erdos1106Sector

lemma logRelativeError {a b ρ : ℝ} (ha : 0 < a) (hb : 0 < b) (hρ₀ : 0 ≤ ρ)
    (hρ : ρ ≤ 1 / 2) (h : |a - b| ≤ ρ * b) :
    |Real.log a - Real.log b| ≤ 2 * ρ := by
  let y := a / b
  have hy : 0 < y := div_pos ha hb
  have hx : |y - 1| ≤ ρ := by
    dsimp [y]
    have hdiv : a / b - 1 = (a - b) / b := by field_simp
    rw [hdiv, abs_div, abs_of_pos hb, div_le_iff₀ hb]
    exact h
  have hylo : (1 : ℝ) / 2 ≤ y := by linarith [(abs_le.mp hx).1]
  have hyhigh : y - 1 ≤ ρ := (abs_le.mp hx).2
  have hlo : -(2 * ρ) ≤ 1 - y⁻¹ := by
    have hm := mul_le_mul_of_nonneg_left hylo (show 0 ≤ 2 * ρ by positivity)
    rw [le_sub_comm, ← one_div, div_le_iff₀ hy]
    nlinarith [(abs_le.mp hx).1]
  rw [← Real.log_div ha.ne' hb.ne']
  change |Real.log y| ≤ 2 * ρ
  exact abs_le.mpr ⟨hlo.trans (Real.one_sub_inv_le_log_of_pos hy),
    (Real.log_le_sub_one_of_pos hy).trans (by linarith)⟩

lemma logRelativeError_of_complex {p ρ : ℝ} {A : ℂ} (hp : 0 < p) (hA : A ≠ 0)
    (hρ₀ : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2) (h : ‖(p : ℂ) - A‖ ≤ ρ * ‖A‖) :
    |Real.log p - Real.log ‖A‖| ≤ 2 * ρ := by
  apply logRelativeError hp (norm_pos_iff.mpr hA) hρ₀ hρ
  have hnorm := abs_norm_sub_norm_le (p : ℂ) A
  simpa [abs_of_pos hp] using hnorm.trans h

noncomputable def modelScale (a : ℝ) (w : ℂ) : ℂ :=
  (a : ℂ) * Complex.sqrt (w - 1 / 24)

noncomputable def logarithmicModel (J : ℂ → ℂ) (a L : ℝ) (w : ℂ) : ℂ :=
  let s := modelScale a w
  2 * s - (3 / 2 : ℂ) * Complex.log s + Complex.log (J s) + (L : ℂ)

noncomputable def saddleApproximation (J : ℂ → ℂ) (a K : ℝ) (w : ℂ) : ℂ :=
  let s := modelScale a w
  (K : ℂ) * Complex.exp (2 * s) * J s / s ^ (3 / 2 : ℂ)

private lemma sqrt_re_nonneg (z : ℂ) : 0 ≤ z.sqrt.re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  positivity

private lemma sqrt_squared (z : ℂ) : z.sqrt ^ 2 = z := by
  simp [Complex.sqrt]

lemma modelScale_sector {a : ℝ} (ha : 1 ≤ a) {w : ℂ}
    (hw : w ∈ sector (10 ^ 12) (1 / 200)) :
    160000 ≤ (modelScale a w).re ∧
      |(modelScale a w).im| ≤ (modelScale a w).re / 100 ∧
      ‖modelScale a w‖ ≤ (2 * a) * ‖w‖ := by
  let u := Complex.sqrt (w - 1 / 24)
  have hwR : (10 : ℝ) ^ 12 < w.re := hw.1
  have hwI : |w.im| < (1 / 200 : ℝ) * w.re := hw.2
  have hu : u ^ 2 = w - 1 / 24 := sqrt_squared _
  have hpos : 0 ≤ u.re := sqrt_re_nonneg _
  have hre : u.re ^ 2 - u.im ^ 2 = w.re - 1 / 24 := by
    have h := congrArg Complex.re hu
    norm_num [pow_two, Complex.mul_re, Complex.sub_re, Complex.div_re] at h
    nlinarith
  have him : 2 * u.re * u.im = w.im := by
    have h := congrArg Complex.im hu
    norm_num [pow_two, Complex.mul_im, Complex.sub_im, Complex.div_im] at h
    nlinarith
  have huR : (160000 : ℝ) ≤ u.re := by
    by_contra! hh
    have hs := pow_lt_pow_left₀ hh hpos (n := 2) (by decide)
    nlinarith [sq_nonneg u.im]
  have hu0 : 0 < u.re := lt_of_lt_of_le (by norm_num) huR
  have h2 : |w.im| = 2 * u.re * |u.im| := by
    rw [← him, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * u.re)]
  have huI : |u.im| ≤ u.re / 100 := by
    refine le_of_mul_le_mul_left ?_ (by positivity : 0 < 2 * u.re)
    rw [← h2]
    nlinarith [sq_nonneg u.im]
  have hwnorm : 1 ≤ ‖w‖ := (by linarith : 1 ≤ w.re).trans (Complex.re_le_norm _)
  have hunormsq : ‖u‖ ^ 2 = ‖w - 1 / 24‖ := by rw [← norm_pow, hu]
  have hsb : ‖u‖ ≤ 2 * ‖w‖ := by
    have hu2 : ‖u‖ ^ 2 ≤ ‖w‖ + 1 / 24 := by
      rw [hunormsq]
      simpa [norm_div] using norm_sub_le w (1 / 24 : ℂ)
    have hu3 : ‖u‖ ^ 2 ≤ (2 * ‖w‖) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hwnorm) (norm_nonneg w)]
    exact le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) (by positivity) hu3
  have ha₀ : 0 ≤ a := (by norm_num : 0 ≤ (1 : ℝ)).trans ha
  change 160000 ≤ ((a : ℂ) * u).re ∧
      |((a : ℂ) * u).im| ≤ ((a : ℂ) * u).re / 100 ∧
        ‖(a : ℂ) * u‖ ≤ (2 * a) * ‖w‖
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero, abs_mul, abs_of_nonneg ha₀, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg ha₀]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr ha) hpos]
  · calc
      a * |u.im| ≤ a * (u.re / 100) := mul_le_mul_of_nonneg_left huI ha₀
      _ = _ := by ring
  · calc
      a * ‖u‖ ≤ a * (2 * ‖w‖) := mul_le_mul_of_nonneg_left hsb ha₀
      _ = _ := by ring

lemma norm_log_le (z : ℂ) : ‖z.log‖ ≤ |Real.log ‖z‖| + Real.pi := by
  have hi : |z.log.im| ≤ Real.pi :=
    abs_le.mpr ⟨(Complex.neg_pi_lt_log_im z).le, Complex.log_im_le_pi z⟩
  calc
    ‖z.log‖ = ‖((z.log.re : ℝ) : ℂ) + ((z.log.im : ℝ) : ℂ) * Complex.I‖ := by
      rw [Complex.re_add_im]
    _ ≤ ‖((z.log.re : ℝ) : ℂ)‖ + ‖((z.log.im : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |Real.log ‖z‖| + |z.log.im| := by simp [Complex.log_re, Real.norm_eq_abs]
    _ ≤ _ := add_le_add le_rfl hi

lemma diff_logModel (J : ℂ → ℂ) (a L : ℝ) (ha : 1 ≤ a) (hJ : Differentiable ℂ J)
    (hJl : ∀ s : ℂ, 160000 ≤ s.re → |s.im| ≤ s.re / 100 → 0 < (J s).re) :
    DifferentiableOn ℂ (logarithmicModel J a L) (sector (10 ^ 12) (1 / 200)) := by
  have hs : DifferentiableOn ℂ (modelScale a) (sector (10 ^ 12) (1 / 200)) := by
    intro w hw
    have hT : (10 : ℝ) ^ 12 < w.re := hw.1
    have hslit : w - 1 / 24 ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      norm_num [Complex.sub_re, Complex.div_re]
      linarith
    exact (((Complex.differentiableAt_sqrt hslit).comp w
      (differentiableAt_id.sub_const _)).const_mul (a : ℂ)).differentiableWithinAt
  have hspos {w : ℂ} (hw : w ∈ sector (10 ^ 12) (1 / 200)) :
      0 < (modelScale a w).re := (by norm_num : (0 : ℝ) < 160000).trans_le
    (modelScale_sector ha hw).1
  have hJpos {w : ℂ} (hw : w ∈ sector (10 ^ 12) (1 / 200)) :
      0 < (J (modelScale a w)).re := by
    have h := modelScale_sector ha hw
    exact hJl _ h.1 h.2.1
  refine (((hs.const_mul 2).sub ((hs.clog ?_).const_mul (3 / 2))).add
    ((hJ.comp_differentiableOn hs).clog ?_)).add_const _
  · exact fun w hw ↦ Complex.mem_slitPlane_iff.mpr (Or.inl (hspos hw))
  · exact fun w hw ↦ Complex.mem_slitPlane_iff.mpr (Or.inl (hJpos hw))

lemma norm_shifted_sqrt_sub {w : ℂ} (hw : (10 : ℝ) ^ 12 < w.re) :
    ‖Complex.sqrt (w - 1 / 24) - Complex.sqrt w‖ ≤ (1 : ℝ) / 24 := by
  let u := Complex.sqrt (w - 1 / 24)
  let v := Complex.sqrt w
  have hu := sqrt_squared (w - 1 / 24)
  have hv := sqrt_squared w
  have hf : (u - v) * (u + v) = -(1 / 24 : ℂ) := by
    change u ^ 2 = w - 1 / 24 at hu
    change v ^ 2 = w at hv
    calc
      _ = u ^ 2 - v ^ 2 := by ring
      _ = _ := by rw [hu, hv]; ring
  have hnu : 0 ≤ u.re := sqrt_re_nonneg _
  have hnv : 0 ≤ v.re := sqrt_re_nonneg _
  have hure : (1 : ℝ) ≤ u.re := by
    have h := congrArg Complex.re hu
    norm_num [pow_two, Complex.mul_re, Complex.sub_re, Complex.div_re] at h
    change u.re * u.re - u.im * u.im = w.re - 1 / 24 at h
    by_contra! hh
    nlinarith [mul_nonneg hnu (sub_nonneg.mpr hh.le), sq_nonneg u.im]
  have hplus : (1 : ℝ) ≤ ‖u + v‖ := by
    have hr := Complex.re_le_norm (u + v)
    rw [Complex.add_re] at hr
    linarith
  change ‖u - v‖ ≤ _
  calc
    ‖u - v‖ ≤ ‖u - v‖ * ‖u + v‖ := le_mul_of_one_le_right (norm_nonneg _) hplus
    _ = _ := by rw [← norm_mul, hf]; norm_num [norm_div]

lemma logModel_bound (J : ℂ → ℂ) (a L : ℝ) (ha : 1 ≤ a)
    (hJl : ∀ s : ℂ, 160000 ≤ s.re → |s.im| ≤ s.re / 100 →
      Real.exp (-2) / (3 * Real.sqrt s.re) ≤ (J s).re)
    (hJu : ∀ s : ℂ, 160000 ≤ s.re → |s.im| ≤ s.re / 100 → ‖J s‖ ≤ 1) :
    ∃ C ≥ (0 : ℝ), ∀ w ∈ sector (10 ^ 12) (1 / 200),
      ‖logarithmicModel J a L w - ((2 * a : ℝ) : ℂ) * Complex.sqrt w‖ ≤
        C * (1 + Real.log ‖w‖) := by
  let B := Real.log (2 * a)
  let C := a + 2 * B + 3 * Real.pi + 4 + Real.log 3 + |L|
  have ha₀ : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Real.log_nonneg (by linarith)
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hC : 0 ≤ C := by dsimp [C]; positivity [Real.pi_pos]
  refine ⟨C, hC, ?_⟩
  intro w hw
  let s := modelScale a w
  let W := Real.log ‖w‖
  obtain ⟨hsre, hsim, hsnorm⟩ := modelScale_sector ha hw
  have hwr : (10 : ℝ) ^ 12 < w.re := hw.1
  have hwN : 1 ≤ ‖w‖ := (by linarith : 1 ≤ w.re).trans (Complex.re_le_norm _)
  have hW : 0 ≤ W := Real.log_nonneg hwN
  have hs₀ : 0 < s.re := (by norm_num : (0 : ℝ) < 160000).trans_le hsre
  have hsN : 1 ≤ ‖s‖ := (by linarith : (1 : ℝ) ≤ s.re).trans (Complex.re_le_norm _)
  have hlogS : Real.log ‖s‖ ≤ B + W := by
    have h := Real.log_le_log (by linarith : 0 < ‖s‖) hsnorm
    rw [Real.log_mul (by positivity : (2 * a : ℝ) ≠ 0) (by linarith : ‖w‖ ≠ 0)] at h
    exact h
  have hSn : ‖s.log‖ ≤ B + W + Real.pi := by
    refine (norm_log_le s).trans ?_
    rw [abs_of_nonneg (Real.log_nonneg hsN)]
    linarith
  have hl := hJl s hsre hsim
  have hj₀ : 0 < (J s).re := (by positivity : 0 < Real.exp (-2) / (3 * Real.sqrt s.re)).trans_le hl
  have hjN : 0 < ‖J s‖ := hj₀.trans_le (Complex.re_le_norm _)
  have hcorr := Real.log_le_log (by positivity : 0 < Real.exp (-2) / (3 * Real.sqrt s.re))
    (hl.trans (Complex.re_le_norm _))
  rw [Real.log_div (Real.exp_ne_zero _) (by positivity), Real.log_exp,
    Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by positivity), Real.log_sqrt hs₀.le] at hcorr
  have hrelog : Real.log s.re ≤ B + W :=
    (Real.log_le_log hs₀ (Complex.re_le_norm _)).trans hlogS
  have hJn : ‖(J s).log‖ ≤ 2 + Real.log 3 + (B + W) / 2 + Real.pi := by
    refine (norm_log_le (J s)).trans ?_
    rw [abs_of_nonpos (Real.log_nonpos hjN.le (hJu s hsre hsim))]
    linarith
  let A := 2 * s - ((2 * a : ℝ) : ℂ) * w.sqrt
  have hA : ‖A‖ ≤ a / 12 := by
    have he : A = ((2 * a : ℝ) : ℂ) * ((w - 1 / 24).sqrt - w.sqrt) := by
      unfold A s modelScale
      push_cast
      ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * a)]
    calc
      _ ≤ (2 * a) * (1 / 24) := mul_le_mul_of_nonneg_left (norm_shifted_sqrt_sub hwr) (by positivity)
      _ = _ := by ring
  have htriangle : ‖logarithmicModel J a L w - ((2 * a : ℝ) : ℂ) * w.sqrt‖ ≤
      ‖A‖ + (3 / 2 : ℝ) * ‖s.log‖ + ‖(J s).log‖ + |L| := by
    have he : logarithmicModel J a L w - ((2 * a : ℝ) : ℂ) * w.sqrt =
        ((A - (3 / 2 : ℂ) * s.log) + (J s).log) + (L : ℂ) := by
      unfold logarithmicModel A s
      ring
    rw [he]
    calc
      _ ≤ ‖(A - (3 / 2 : ℂ) * s.log) + (J s).log‖ + ‖(L : ℂ)‖ := norm_add_le _ _
      _ ≤ (‖A - (3 / 2 : ℂ) * s.log‖ + ‖(J s).log‖) + ‖(L : ℂ)‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (‖A‖ + ‖(3 / 2 : ℂ) * s.log‖) + ‖(J s).log‖ + ‖(L : ℂ)‖ :=
        add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
      _ = _ := by norm_num [norm_mul, norm_div, Real.norm_eq_abs]
  refine htriangle.trans ?_
  change _ ≤ C * (1 + W)
  have hC2 : 2 ≤ C := by dsimp [C]; linarith [Real.pi_pos, abs_nonneg L]
  calc
    _ ≤ a / 12 + (3 / 2) * (B + W + Real.pi) +
          (2 + Real.log 3 + (B + W) / 2 + Real.pi) + |L| := by linarith
    _ ≤ C + 2 * W := by dsimp [C]; linarith [Real.pi_pos]
    _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hC2) hW]

lemma re_logModel_eq_log_norm (J : ℂ → ℂ) (a K : ℝ) (hK : 0 < K) (w : ℂ)
    (hs : modelScale a w ≠ 0) (hJ : J (modelScale a w) ≠ 0) :
    (logarithmicModel J a (Real.log K) w).re = Real.log ‖saddleApproximation J a K w‖ := by
  let s := modelScale a w
  have hn : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hpow : ‖s ^ (3 / 2 : ℂ)‖ = ‖s‖ ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num]
    exact Complex.norm_cpow_real _ _
  have hJ₀ : ‖J s‖ ≠ 0 := norm_ne_zero_iff.mpr hJ
  change (2 * s - (3 / 2 : ℂ) * s.log + (J s).log + (Real.log K : ℂ)).re =
    Real.log ‖(K : ℂ) * Complex.exp (2 * s) * J s / s ^ (3 / 2 : ℂ)‖
  rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hK.le,
    Complex.norm_exp, hpow, Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) hJ₀, Real.log_mul hK.ne' (Real.exp_ne_zero _),
    Real.log_exp, Real.log_rpow hn]
  norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_re, Complex.log_re]
  ring

end Erdos1106LogModel

end

section

/-
# From the major-arc approximation to the Erdős target

The logarithm of the saddle estimate is an interpolation satisfying the
sector and integer approximation bounds needed by the arithmetic proof.
-/

namespace Erdos1106SaddleTransfer

open Filter Nat Erdos1106Sector Erdos1106LogModel
open scoped Topology

theorem of_saddle_relative_error (J : ℂ → ℂ) (a K ε C : ℝ)
    (ha : 1 ≤ a) (hK : 0 < K) (hε : 0 < ε) (hC : 0 ≤ C)
    (hJ : Differentiable ℂ J)
    (hJl : ∀ s : ℂ, 160000 ≤ s.re → |s.im| ≤ s.re / 100 →
      Real.exp (-2) / (3 * Real.sqrt s.re) ≤ (J s).re)
    (hJu : ∀ s : ℂ, 160000 ≤ s.re → |s.im| ≤ s.re / 100 → ‖J s‖ ≤ 1)
    (herror : ∀ᶠ n : ℕ in atTop,
      ‖(partitionNumber n : ℂ) - saddleApproximation J a K (n : ℂ)‖ ≤
        C * Real.exp (-ε * Real.sqrt (n : ℝ)) * ‖saddleApproximation J a K (n : ℂ)‖) :
    type_of% @Erdos1106.erdos_1106.parts.i := by
  have hJpos (s : ℂ) (hsR : 160000 ≤ s.re) (hsI : |s.im| ≤ s.re / 100) : 0 < (J s).re := by
    have hrs : 0 < s.re := (by norm_num : (0 : ℝ) < 160000).trans_le hsR
    exact (by positivity : 0 < Real.exp (-2) / (3 * Real.sqrt s.re)).trans_le (hJl s hsR hsI)
  let F := logarithmicModel J a (Real.log K)
  have hF := diff_logModel J a (Real.log K) ha hJ hJpos
  obtain ⟨D, hD, hbound⟩ := logModel_bound J a (Real.log K) ha hJl hJu
  have hl : ∀ᶠ n : ℕ in atTop,
      |Real.log (partitionNumber n : ℝ) - (F (n : ℂ)).re| ≤
        (2 * C) * Real.exp (-ε * Real.sqrt (n : ℝ)) := by
    have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hsqrt := Real.tendsto_sqrt_atTop.comp hnat
    have hb : Tendsto (fun n : ℕ ↦ -ε * Real.sqrt (n : ℝ)) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr hε)).2 hsqrt
    have hlim : Tendsto (fun n : ℕ ↦ C * Real.exp (-ε * Real.sqrt (n : ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero, Function.comp_apply] using (Real.tendsto_exp_atBot.comp hb).const_mul C
    filter_upwards [herror, hnat.eventually_gt_atTop ((10 : ℝ) ^ 12),
      hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn hnR hsmall
    have hsec : (n : ℂ) ∈ sector (10 ^ 12) (1 / 200) := by
      refine ⟨by simpa using hnR, ?_⟩
      have hpos : (0 : ℝ) < n := lt_trans (by norm_num) hnR
      simpa using (mul_pos (by norm_num : (0 : ℝ) < 1 / 200) hpos)
    let s := modelScale a (n : ℂ)
    have hs := modelScale_sector ha hsec
    have hsne : s ≠ 0 := by
      intro hz
      have h : 160000 ≤ s.re := hs.1
      norm_num [hz] at h
    have hJs : J s ≠ 0 := by
      intro he
      have h := hJpos s hs.1 hs.2.1
      simp [he] at h
    have hA : saddleApproximation J a K (n : ℂ) ≠ 0 := by
      unfold saddleApproximation
      apply div_ne_zero (mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hK.ne')
        (Complex.exp_ne_zero _)) hJs)
      exact Complex.cpow_ne_zero_iff.mpr (Or.inl hsne)
    have hpn : (0 : ℝ) < partitionNumber n := by
      exact_mod_cast Erdos1106Work.partitionNumber_pos n
    have hc := logRelativeError_of_complex hpn hA
      (by positivity : 0 ≤ C * Real.exp (-ε * Real.sqrt (n : ℝ))) hsmall.le
      (by simpa only [Complex.ofReal_natCast] using hn)
    rw [show (F (n : ℂ)).re = Real.log ‖saddleApproximation J a K (n : ℂ)‖ from
      re_logModel_eq_log_norm J a K hK _ hsne hJs]
    simpa only [mul_assoc] using hc
  obtain ⟨N, hN⟩ := eventually_atTop.1 hl
  apply Erdos1106Work.of_square_difference_bounds
  exact Erdos1106AnalyticTransfer.sectorialInterpolation_implies_squareBounds
    (fun n : ℕ ↦ Real.log (partitionNumber n : ℝ)) F
    (2 * a) (10 ^ 12) (1 / 200) D ε (2 * C) N
    (by positivity) (by positivity) (by positivity) hD hε (by positivity)
    hF hbound hN

end Erdos1106SaddleTransfer

end

section

/-
# Normalization of the partition coefficient estimate

The coefficient integral is scaled by 2π. Removing that scaling and the
mass factor gives the relative error needed for logarithmic comparison.
-/

namespace Erdos1106Scalar

open Filter Nat Erdos1106LogModel
open scoped Topology ComplexOrder

noncomputable def saddleConstant : ℝ := Real.pi ^ 2 / 6

noncomputable def saddleParameter : ℝ := Real.sqrt saddleConstant

noncomputable def saddlePrefactor : ℝ :=
  saddleConstant * Real.sqrt (saddleConstant / (2 * Real.pi)) / (2 * Real.pi)

lemma saddleConstant_pos : 0 < saddleConstant := by
  unfold saddleConstant
  positivity [Real.pi_pos]

lemma saddleParameter_ge_one : 1 ≤ saddleParameter := by
  unfold saddleParameter saddleConstant
  have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h : (1 : ℝ) ≤ Real.pi ^ 2 / 6 := by nlinarith
  simpa using Real.sqrt_le_sqrt h

lemma saddlePrefactor_pos : 0 < saddlePrefactor := by
  unfold saddlePrefactor
  positivity [saddleConstant_pos, Real.pi_pos]

private lemma scaledModel_eq (J : ℂ → ℂ) (n : ℕ) (hn : 1 ≤ n) (t s : ℝ)
    (ht : 0 < t) (hs : 0 < s) (hprod : t * s = saddleConstant)
    (hindex : ((n : ℝ) - 1 / 24) * t = s) :
    ((2 * Real.pi : ℝ) : ℂ) * saddleApproximation J saddleParameter saddlePrefactor (n : ℂ) =
      ((t * (Real.sqrt (t / (2 * Real.pi)) * Real.exp (2 * s)) : ℝ) : ℂ) * J (s : ℂ) := by
  let u := Real.sqrt ((n : ℝ) - 1 / 24)
  let a := saddleParameter
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hu₀ : 0 ≤ (n : ℝ) - 1 / 24 := by linarith
  have husq : u ^ 2 = (n : ℝ) - 1 / 24 := Real.sq_sqrt hu₀
  have hasq : a ^ 2 = saddleConstant := Real.sq_sqrt saddleConstant_pos.le
  have hsreal : a * u = s := by
    have he : (a * u) ^ 2 = s ^ 2 := by
      rw [mul_pow, hasq, husq]
      rw [← hprod]
      calc
        _ = (((n : ℝ) - 1 / 24) * t) * s := by ring
        _ = s ^ 2 := by rw [hindex, pow_two]
    exact (sq_eq_sq₀ (by dsimp [a, u, saddleParameter]; positivity)
      hs.le).mp he
  have hscale : modelScale saddleParameter (n : ℂ) = (s : ℂ) := by
    have hshift : (n : ℂ) - 1 / 24 = (((n : ℝ) - 1 / 24 : ℝ) : ℂ) := by push_cast; ring
    unfold modelScale
    rw [hshift, Complex.sqrt_of_nonneg (Complex.zero_le_real.mpr hu₀)]
    simp only [Complex.ofReal_re]
    change ((a : ℂ) * (u : ℂ)) = (s : ℂ)
    exact_mod_cast hsreal
  have hk : (2 * Real.pi) * saddlePrefactor / s ^ (3 / 2 : ℝ) =
      t * Real.sqrt (t / (2 * Real.pi)) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hs,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
    apply (div_eq_iff (by positivity : s * Real.sqrt s ≠ 0)).mpr
    have hsqrt : Real.sqrt (t / (2 * Real.pi)) * Real.sqrt s =
        Real.sqrt (saddleConstant / (2 * Real.pi)) := by
      rw [← Real.sqrt_mul (by positivity : 0 ≤ t / (2 * Real.pi))]
      congr 1
      rw [div_mul_eq_mul_div, hprod]
    calc
      _ = saddleConstant * Real.sqrt (saddleConstant / (2 * Real.pi)) := by
        unfold saddlePrefactor
        field_simp
      _ = _ := by rw [← hsqrt, ← hprod]; ring
  unfold saddleApproximation
  rw [hscale]
  dsimp only
  rw [← show (((s ^ (3 / 2 : ℝ) : ℝ) : ℂ)) = (s : ℂ) ^ (3 / 2 : ℂ) by
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
      Complex.ofReal_cpow hs.le (3 / 2 : ℝ)]
  have hkC : ((2 * Real.pi : ℝ) : ℂ) * (saddlePrefactor : ℂ) /
      ((s ^ (3 / 2 : ℝ) : ℝ) : ℂ) =
        ((t * Real.sqrt (t / (2 * Real.pi)) : ℝ) : ℂ) := by exact_mod_cast hk
  calc
    _ = (((2 * Real.pi : ℝ) : ℂ) * (saddlePrefactor : ℂ) /
        ((s ^ (3 / 2 : ℝ) : ℝ) : ℂ)) * Complex.exp (2 * (s : ℂ)) * J (s : ℂ) := by ring
    _ = _ := by
      have he := Complex.ofReal_exp (2 * s)
      push_cast at he
      rw [hkC, ← he]
      push_cast
      ring

private lemma sqrt_eventual_atTop :
    Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop

theorem relative_error_from_integral_bound (J : ℂ → ℂ) (k : ℝ) (hk : 0 < k)
    (hJl : ∀ s : ℂ, 160000 ≤ s.re → |s.im| ≤ s.re / 100 →
      Real.exp (-2) / (3 * Real.sqrt s.re) ≤ (J s).re)
    (hint : ∀ (n : ℕ) (t s : ℝ), 1 ≤ n → 0 < t → t ≤ 1 → 0 < s →
      t * s = saddleConstant → ((n : ℝ) - 1 / 24) * t = s →
      ‖((2 * Real.pi : ℝ) : ℂ) * (partitionNumber n : ℂ) -
        ((t * (Real.sqrt (t / (2 * Real.pi)) * Real.exp (2 * s)) : ℝ) : ℂ) *
          J (s : ℂ)‖ ≤
        (20 * Real.pi) * (Real.sqrt (t / (2 * Real.pi)) * Real.exp (2 * s)) *
          Real.exp (-k / t)) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      ‖(partitionNumber n : ℂ) -
        saddleApproximation J saddleParameter saddlePrefactor (n : ℂ)‖ ≤
        C * Real.exp (-ε * Real.sqrt (n : ℝ)) *
          ‖saddleApproximation J saddleParameter saddlePrefactor (n : ℂ)‖ := by
  let a := saddleParameter
  let ε := k / (4 * a)
  let C := 60 * Real.pi * Real.exp 2 * saddleConstant
  have ha : (1 : ℝ) ≤ a := saddleParameter_ge_one
  have ha₀ : 0 < a := by linarith
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity [Real.pi_pos, saddleConstant_pos]
  refine ⟨ε, C, hε, hC, ?_⟩
  have hpoly : Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.exp (-ε * Real.sqrt (n : ℝ)))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 ε hε).comp sqrt_eventual_atTop
    change Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ) ^ (2 : ℝ) *
      Real.exp (-ε * Real.sqrt (n : ℝ))) atTop (𝓝 0) at h
    simpa only [Real.rpow_two, Real.sq_sqrt (Nat.cast_nonneg _)] using h
  have hlarge := sqrt_eventual_atTop.eventually_ge_atTop (2 * max a 160000)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlarge,
    hpoly.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn hnlarge hnpoly
  let u := Real.sqrt ((n : ℝ) - 1 / 24)
  let t := a / u
  let s := a * u
  let M := Real.sqrt (t / (2 * Real.pi)) * Real.exp (2 * s)
  let P := saddleApproximation J a saddlePrefactor (n : ℂ)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have huarg : 0 ≤ (n : ℝ) - 1 / 24 := by linarith
  have hu2 : u ^ 2 = (n : ℝ) - 1 / 24 := Real.sq_sqrt huarg
  have huhalf : Real.sqrt (n : ℝ) / 2 ≤ u := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ Real.sqrt (n : ℝ) / 2)]
    apply Real.sqrt_le_sqrt
    have hsq := Real.sq_sqrt (Nat.cast_nonneg n)
    nlinarith
  have hul : max a 160000 ≤ u := by linarith
  have hu : 0 < u := ha₀.trans_le ((le_max_left _ _).trans hul)
  have ht : 0 < t := div_pos ha₀ hu
  have ht1 : t ≤ 1 := (div_le_one hu).2 ((le_max_left _ _).trans hul)
  have hs : 0 < s := mul_pos ha₀ hu
  have hsL : 160000 ≤ s :=
    ((le_max_right a 160000).trans hul).trans (le_mul_of_one_le_left hu.le ha)
  have hts : t * s = saddleConstant := by
    dsimp [t, s]
    rw [div_mul_eq_mul_div]
    change (a * (a * u)) / u = saddleConstant
    have hae : a ^ 2 = saddleConstant := Real.sq_sqrt saddleConstant_pos.le
    field_simp
    nlinarith [congrArg (fun x : ℝ ↦ x * u) hae]
  have hns : ((n : ℝ) - 1 / 24) * t = s := by
    rw [← hu2]
    dsimp [t, s]
    field_simp
  have hM : 0 < M := by dsimp [M]; positivity [Real.pi_pos]
  have hP := scaledModel_eq J n hn t s ht hs hts hns
  have hPnorm : (2 * Real.pi) * ‖P‖ = (t * M) * ‖J (s : ℂ)‖ := by
    change ((2 * Real.pi : ℝ) : ℂ) * P = ((t * M : ℝ) : ℂ) * J (s : ℂ) at hP
    have he := congrArg norm hP
    change ‖((2 * Real.pi : ℝ) : ℂ) * P‖ = ‖((t * M : ℝ) : ℂ) * J (s : ℂ)‖ at he
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (by positivity [Real.pi_pos] : 0 ≤ 2 * Real.pi),
      Real.norm_of_nonneg (mul_nonneg ht.le hM.le)] at he
    exact he
  have hj := hJl (s : ℂ) (by simpa using hsL)
    (by simpa using (show 0 ≤ s / 100 by positivity))
  have hj' : Real.exp (-2) / (3 * Real.sqrt s) ≤ ‖J (s : ℂ)‖ :=
    (by simpa using hj : Real.exp (-2) / (3 * Real.sqrt s) ≤ (J (s : ℂ)).re).trans
      (Complex.re_le_norm _)
  have hN := hint n t s hn ht ht1 hs hts hns
  have hdiff : ‖(partitionNumber n : ℂ) - P‖ ≤ 10 * M * Real.exp (-k / t) := by
    change ((2 * Real.pi : ℝ) : ℂ) * P = ((t * M : ℝ) : ℂ) * J (s : ℂ) at hP
    rw [← hP, ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity [Real.pi_pos])] at hN
    apply le_of_mul_le_mul_left ?_ (by positivity [Real.pi_pos] : 0 < 2 * Real.pi)
    change (2 * Real.pi) * ‖(partitionNumber n : ℂ) - P‖ ≤ _
    dsimp [M] at hN ⊢
    convert hN using 1
    ring
  have hmass : M ≤ (6 * Real.pi * Real.exp 2 * saddleConstant) / t ^ 2 * ‖P‖ := by
    have hnsqrt : Real.sqrt s ≤ s := by
      have hs1 : (1 : ℝ) ≤ s := by linarith
      calc
        Real.sqrt s ≤ Real.sqrt (s ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hs1)])
        _ = s := Real.sqrt_sq hs.le
    have hmass1 : (t * M) * (Real.exp (-2) / (3 * Real.sqrt s)) ≤
        (2 * Real.pi) * ‖P‖ := by
      rw [hPnorm]
      exact mul_le_mul_of_nonneg_left hj' (mul_nonneg ht.le hM.le)
    have h₁ : M ≤ (6 * Real.pi * Real.exp 2 * Real.sqrt s) / t * ‖P‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ ht]
      have hp : 0 < 3 * Real.sqrt s := by positivity
      rw [← mul_div_assoc, div_le_iff₀ hp] at hmass1
      have hE : Real.exp (-2) * Real.exp 2 = 1 := by
        rw [← Real.exp_add]; norm_num
      calc
        M * t = (t * M) * (Real.exp (-2) * Real.exp 2) := by rw [hE, mul_one]; ring
        _ = (t * M * Real.exp (-2)) * Real.exp 2 := by ring
        _ ≤ ((2 * Real.pi) * ‖P‖ * (3 * Real.sqrt s)) * Real.exp 2 :=
          mul_le_mul_of_nonneg_right hmass1 (Real.exp_pos 2).le
        _ = _ := by ring
    refine h₁.trans ?_
    have he : (6 * Real.pi * Real.exp 2 * saddleConstant) / t ^ 2 =
        (6 * Real.pi * Real.exp 2 * s) / t := by
      rw [← hts]
      field_simp
    rw [he]
    gcongr
  have h1t : Real.sqrt (n : ℝ) / (2 * a) ≤ 1 / t := by
    dsimp [t]
    rw [one_div_div, show Real.sqrt (n : ℝ) / (2 * a) =
      (Real.sqrt (n : ℝ) / 2) / a by field_simp]
    exact div_le_div_of_nonneg_right huhalf ha₀.le
  have hinv : 1 / t ^ 2 ≤ (n : ℝ) := by
    rw [one_div, ← inv_pow]
    have hi : t⁻¹ ≤ u := by
      dsimp [t]
      rw [inv_div]
      exact div_le_self hu.le ha
    exact (pow_le_pow_left₀ (inv_nonneg.mpr ht.le) hi 2).trans (by rw [hu2]; linarith)
  have hexp : Real.exp (-k / t) ≤ Real.exp (-ε * Real.sqrt (n : ℝ)) *
      Real.exp (-ε * Real.sqrt (n : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_monotone
    have hb := mul_le_mul_of_nonneg_left h1t hk.le
    have heq : k * (Real.sqrt (n : ℝ) / (2 * a)) =
        ε * Real.sqrt (n : ℝ) + ε * Real.sqrt (n : ℝ) := by dsimp [ε]; field_simp; ring
    rw [heq] at hb
    rw [mul_one_div] at hb
    calc
      -k / t = -(k / t) := by ring
      _ ≤ _ := by linarith only [hb]
  change _ ≤ C * Real.exp (-ε * Real.sqrt (n : ℝ)) * ‖P‖
  refine hdiff.trans ?_
  calc
    _ ≤ 10 * ((6 * Real.pi * Real.exp 2 * saddleConstant) / t ^ 2 * ‖P‖) *
        Real.exp (-k / t) := by gcongr
    _ = C * (1 / t ^ 2) * Real.exp (-k / t) * ‖P‖ := by dsimp [C]; ring
    _ ≤ C * (n : ℝ) * (Real.exp (-ε * Real.sqrt (n : ℝ)) *
        Real.exp (-ε * Real.sqrt (n : ℝ))) * ‖P‖ := by gcongr
    _ = C * Real.exp (-ε * Real.sqrt (n : ℝ)) *
        ((n : ℝ) * Real.exp (-ε * Real.sqrt (n : ℝ))) * ‖P‖ := by ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hnpoly.le
        (show 0 ≤ C * Real.exp (-ε * Real.sqrt (n : ℝ)) by positivity)
      simpa only [mul_one] using mul_le_mul_of_nonneg_right h (norm_nonneg P)

end Erdos1106Scalar

end

open Erdos1106Major Erdos1106Scalar

theorem OMA.solution : type_of% @Erdos1106.erdos_1106.parts.i := by
  obtain ⟨k, hk, hcoeff⟩ := Erdos1106Coefficient.coefficient_error
  obtain ⟨ε, C, hε, hC, hrelative⟩ :=
    relative_error_from_integral_bound saddle k hk (fun _ hR hI ↦ saddle_re_lower hR hI)
      (fun n t s _ ht ht₁ _ hs hn ↦ hcoeff n t s ht ht₁ hs hn)
  exact Erdos1106SaddleTransfer.of_saddle_relative_error saddle saddleParameter saddlePrefactor ε C
    saddleParameter_ge_one saddlePrefactor_pos hε hC differentiable_saddle
    (fun _ hR hI ↦ saddle_re_lower hR hI)
    (fun _ hR hI ↦ saddle_norm_le (by linarith) hI) hrelative
