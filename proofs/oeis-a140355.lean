import OMAStatements.S_oeis_a140355

/-!
A multiplier with increasing divisor counts exists for every finite length.
Credit: @VestigeClub.

For primes p up to the requested length, choose exponents floor(t / log p).
The divisor-count ratio for multiplying by i is a finite product whose
first-order limit, after subtracting one and multiplying by t, is log i.
Strict increase of the logarithm then gives all the required inequalities
simultaneously for a sufficiently large real parameter t.
-/

open Filter Topology

namespace OrderedDivisors

theorem scaled_prod_limit {ι : Type*} (s : Finset ι)
    (u : ℝ → ι → ℝ) (v : ι → ℝ)
    (hzero : ∀ i ∈ s, Tendsto (fun t => u t i) atTop (𝓝 0))
    (hscaled : ∀ i ∈ s, Tendsto (fun t => t * u t i) atTop (𝓝 (v i))) :
    Tendsto (fun t => t * ((∏ i ∈ s, (1 + u t i)) - 1)) atTop
      (𝓝 (∑ i ∈ s, v i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hz : ∀ i ∈ s, Tendsto (fun t => u t i) atTop (𝓝 0) :=
      fun i hi => hzero i (Finset.mem_insert_of_mem hi)
    have hs : ∀ i ∈ s, Tendsto (fun t => t * u t i) atTop (𝓝 (v i)) :=
      fun i hi => hscaled i (Finset.mem_insert_of_mem hi)
    have hp : Tendsto (fun t => ∏ i ∈ s, (1 + u t i)) atTop (𝓝 1) := by
      have h1 : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      simpa using tendsto_finsetProd s (fun i hi => h1.add (hz i hi))
    have hh := ((hscaled a (Finset.mem_insert_self a s)).mul hp).add (ih hz hs)
    convert hh using 1
    · funext t
      simp only [Finset.prod_insert ha]
      ring
    · simp [Finset.sum_insert ha]

end OrderedDivisors


open Filter Topology

namespace OrderedDivisors

theorem scaled_floor_limit (r : ℝ) (hr : 0 < r) (c : ℝ) :
    Tendsto (fun t : ℝ => t * (c / ((⌊t / r⌋₊ : ℝ) + 1))) atTop (𝓝 (c * r)) := by
  have hb : Tendsto (fun t : ℝ => (⌊t / r⌋₊ : ℝ) / t) atTop (𝓝 (1 / r)) := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using
      (tendsto_nat_floor_mul_div_atTop (le_of_lt (inv_pos.mpr hr)))
  have hi : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
  have hd : Tendsto (fun t : ℝ => ((⌊t / r⌋₊ : ℝ) + 1) / t) atTop (𝓝 (1 / r)) := by
    simpa only [add_div, add_zero] using hb.add hi
  have hh := (hd.inv₀ (by positivity)).const_mul c
  convert hh using 1
  · funext t
    simp only [inv_div]
    ring
  · simp

theorem floor_term_limit (r : ℝ) (hr : 0 < r) (c : ℝ) :
    Tendsto (fun t : ℝ => c / ((⌊t / r⌋₊ : ℝ) + 1)) atTop (𝓝 0) := by
  have hh := (scaled_floor_limit r hr c).mul
    (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  field_simp [ht.ne']

end OrderedDivisors


open Filter Topology

namespace OrderedDivisors

noncomputable def exponentVector (s : Finset ℕ) (e : ℕ → ℕ) : ℕ →₀ ℕ :=
  Finsupp.onFinset s (fun p => if p ∈ s then e p else 0)
    (by intro p hp; by_contra hn; simp [hn] at hp)

@[simp] theorem exponentVector_apply (s : Finset ℕ) (e : ℕ → ℕ) (p : ℕ) :
    exponentVector s e p = if p ∈ s then e p else 0 := rfl

theorem exponentVector_support (s : Finset ℕ) (e : ℕ → ℕ) :
    (exponentVector s e).support ⊆ s := by
  intro p hp
  by_contra hn
  simpa [Finsupp.mem_support_iff, hn] using hp

noncomputable def multiplier (s : Finset ℕ) (e : ℕ → ℕ) : ℕ :=
  (exponentVector s e).prod (fun p k => p ^ k)

theorem multiplier_pos (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (e : ℕ → ℕ) :
    0 < multiplier s e := by
  unfold multiplier Finsupp.prod
  exact Finset.prod_pos (fun p hp => pow_pos (hs p (exponentVector_support s e hp)).pos _)

theorem multiplier_factorization (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (e : ℕ → ℕ) :
    (multiplier s e).factorization = exponentVector s e := by
  apply Nat.prod_pow_factorization_eq_self
  intro p hp
  exact hs p (exponentVector_support s e hp)

theorem multiplier_support (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (e : ℕ → ℕ) :
    (multiplier s e).primeFactors ⊆ s := by
  rw [← Nat.support_factorization, multiplier_factorization s hs e]
  exact exponentVector_support s e

theorem factorization_eq_zero_outside {i p : ℕ} (hp : p ∉ i.primeFactors) :
    i.factorization p = 0 := by
  simpa only [← Nat.support_factorization, Finsupp.notMem_support_iff] using hp

theorem card_divisors_over (s : Finset ℕ) (i : ℕ) (hi : i ≠ 0)
    (his : i.primeFactors ⊆ s) :
    i.divisors.card = ∏ p ∈ s, (i.factorization p + 1) := by
  rw [Nat.card_divisors hi]
  exact Finset.prod_subset his (fun p _ hp => by simp [factorization_eq_zero_outside hp])

theorem divisor_ratio (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (e : ℕ → ℕ)
    (i : ℕ) (hi : i ≠ 0) (his : i.primeFactors ⊆ s) :
    (((i * multiplier s e).divisors.card : ℝ) / (multiplier s e).divisors.card) =
      ∏ p ∈ s, (1 + (i.factorization p : ℝ) / (e p + 1)) := by
  have hm := (multiplier_pos s hs e).ne'
  have hsub : (i * multiplier s e).primeFactors ⊆ s := by
    rw [Nat.primeFactors_mul hi hm]
    exact Finset.union_subset his (multiplier_support s hs e)
  rw [card_divisors_over s (i * multiplier s e) (mul_ne_zero hi hm) hsub,
    card_divisors_over s (multiplier s e) hm (multiplier_support s hs e)]
  push_cast
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  simp only [Nat.factorization_mul hi hm, Finsupp.add_apply,
    multiplier_factorization s hs e, exponentVector_apply, if_pos hp, Nat.cast_add]
  have h : (e p : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem log_over (s : Finset ℕ) (i : ℕ) (his : i.primeFactors ⊆ s) :
    Real.log i = ∑ p ∈ s, (i.factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  change (∑ p ∈ i.primeFactors, (i.factorization p : ℝ) * Real.log p) = _
  exact Finset.sum_subset his (fun p _ hp => by simp [factorization_eq_zero_outside hp])

end OrderedDivisors


open Filter Topology

namespace OrderedDivisors

noncomputable def exponentsAt (t : ℝ) (p : ℕ) : ℕ := ⌊t / Real.log p⌋₊

noncomputable def ratioAt (s : Finset ℕ) (i : ℕ) (t : ℝ) : ℝ :=
  ((i * multiplier s (exponentsAt t)).divisors.card : ℝ) /
    (multiplier s (exponentsAt t)).divisors.card

theorem ratio_limit (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (i : ℕ) (hi : i ≠ 0) (his : i.primeFactors ⊆ s) :
    Tendsto (fun t => t * (ratioAt s i t - 1)) atTop (𝓝 (Real.log i)) := by
  have hlog (p : ℕ) (hp : p ∈ s) : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast (hs p hp).one_lt)
  have h := scaled_prod_limit s
    (fun t p => (i.factorization p : ℝ) / ((⌊t / Real.log p⌋₊ : ℝ) + 1))
    (fun p => (i.factorization p : ℝ) * Real.log p)
    (fun p hp => floor_term_limit _ (hlog p hp) _)
    (fun p hp => scaled_floor_limit _ (hlog p hp) _)
  rw [← log_over s i his] at h
  convert h using 1
  funext t
  rw [ratioAt, divisor_ratio s hs (exponentsAt t) i hi his]
  rfl

theorem eventually_order (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (i j : ℕ) (hi : 0 < i) (hij : i < j)
    (his : i.primeFactors ⊆ s) (hjs : j.primeFactors ⊆ s) :
    ∀ᶠ t : ℝ in atTop,
      (i * multiplier s (exponentsAt t)).divisors.card <
        (j * multiplier s (exponentsAt t)).divisors.card := by
  have hj : 0 < j := hi.trans hij
  have hlim := (ratio_limit s hs j hj.ne' hjs).sub (ratio_limit s hs i hi.ne' his)
  have hl : 0 < Real.log (j : ℝ) - Real.log (i : ℝ) := by
    apply sub_pos.mpr
    exact Real.strictMonoOn_log (by change (0 : ℝ) < i; exact_mod_cast hi)
      (by change (0 : ℝ) < j; exact_mod_cast hj)
      (by exact_mod_cast hij)
  have he := (tendsto_order.1 hlim).1 0 hl
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with t ht hpos
  have hr : ratioAt s i t < ratioAt s j t := by nlinarith
  have hm := multiplier_pos s hs (exponentsAt t)
  have hd : 0 < ((multiplier s (exponentsAt t)).divisors.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, by simp [hm.ne']⟩
  exact_mod_cast (div_lt_div_iff_of_pos_right hd).mp hr

theorem all_lengths (n : ℕ) :
    ∃ m : ℕ, 0 < m ∧ ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ n →
      (i * m).divisors.card < (j * m).divisors.card := by
  let s := (Finset.range (n + 1)).filter Nat.Prime
  have hs : ∀ p ∈ s, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have sub (i : Fin (n+1)) : i.val.primeFactors ⊆ s := by
    intro p hp
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (lt_of_le_of_lt (Nat.le_of_mem_primeFactors hp) i.isLt),
      Nat.prime_of_mem_primeFactors hp⟩
  have pair (i j : Fin (n+1)) :
      ∀ᶠ t : ℝ in atTop, 1 ≤ i.val → i.val < j.val →
        (i.val * multiplier s (exponentsAt t)).divisors.card <
          (j.val * multiplier s (exponentsAt t)).divisors.card := by
    by_cases hi : 1 ≤ i.val
    · by_cases hij : i.val < j.val
      · filter_upwards [eventually_order s hs i j hi hij (sub i) (sub j)] with t ht
        exact fun _ _ => ht
      · exact Filter.Eventually.of_forall (fun _ _ h => False.elim (hij h))
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hi h))
  have hall : ∀ᶠ t : ℝ in atTop, ∀ i j : Fin (n+1), 1 ≤ i.val → i.val < j.val →
      (i.val * multiplier s (exponentsAt t)).divisors.card <
        (j.val * multiplier s (exponentsAt t)).divisors.card :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j => pair i j))
  obtain ⟨t, ht⟩ := hall.exists
  refine ⟨multiplier s (exponentsAt t), multiplier_pos s hs _, ?_⟩
  intro i j hi hij hj
  exact ht ⟨i, by omega⟩ ⟨j, by omega⟩ hi hij

end OrderedDivisors
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a140355.main) := by
  intro h
  have hu : (Set.univ : Set ℕ).Finite := h.subset (by
    intro n _
    exact OrderedDivisors.all_lengths n)
  exact Set.infinite_univ hu
