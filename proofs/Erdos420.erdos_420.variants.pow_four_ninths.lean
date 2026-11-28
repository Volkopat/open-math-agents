import FormalConjectures.ErdosProblems.«420»
import Mathlib

/-!
The factorial window of Erdős, Graham, Ivić, and Pomerance, Corollary 3
of the 1996 paper. The reduction is by @steveDOTdigital (PR 5169), its
factorial comparison by @OrangeHeadz (PR 5473), and its sieve estimate
by @jpollard-cs (PR 8125).
-/

section

/-!
# The four-ninths factorial window

Split the logarithm of each integer in the interval by prime-factor size.
The two estimates are the small-prime and middle-prime bounds in the proof of
Lemma 3 of Erdős, Graham, Ivić and Pomerance. A large prime factor forces
an explicit gain in the divisor function when this integer enters the factorial.
-/

namespace OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1

open Filter Finset Real
open scoped ArithmeticFunction.sigma Classical

/-- The small primes contribute at most (4/9+o(1)) times the logarithmic mass. -/
def H1 : Prop := ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
  let h := ⌊(n:ℝ)^((4:ℝ)/9)⌋₊
  (∑ i ∈ range h, ∑ p ∈ (n+i+1).primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ (n:ℝ)^((4:ℝ)/9)),
    ((n+i+1).factorization p : ℝ)*log p) ≤ (4/9+η)*(h:ℝ)*log n

/-- The exponent-pair estimate saves a fixed amount on intermediate primes. -/
def H2 : Prop := ∃ η : ℝ, 0 < η ∧ ∀ᶠ n : ℕ in atTop,
  let h := ⌊(n:ℝ)^((4:ℝ)/9)⌋₊
  (∑ i ∈ range h, ∑ p ∈ (n+i+1).primeFactors.filter (fun p : ℕ =>
    (n:ℝ)^((4:ℝ)/9) < p ∧ (p:ℝ) ≤ (n:ℝ)^((5:ℝ)/9+1/10000)),
    ((n+i+1).factorization p : ℝ)*log p) ≤ (5/9-η)*(h:ℝ)*log n

lemma divisors_mul_prime (a p : ℕ) (ha : a ≠ 0) (hp : p.Prime) :
    σ 0 (p*a) * (a.factorization p + 1) = σ 0 a * (a.factorization p + 2) := by
  let k := a.factorization p
  let b := a / p^k
  have hcop : p.Coprime b := Nat.coprime_ordCompl hp ha
  have hab : p^k*b = a := Nat.ordProj_mul_ordCompl_eq_self a p
  have hnext : p^(k+1)*b = p*a := by rw [← hab]; ring
  have h1 : σ 0 a = (k+1)*σ 0 b := by
    rw [← hab,ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_left k),
      ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  have h2 : σ 0 (p*a) = (k+2)*σ 0 b := by
    rw [← hnext,ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_left (k+1)),
      ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  rw [h1,h2]
  change _ * (k+1) = _ * (k+2)
  ring

lemma gain (n p : ℕ) (hp : p.Prime) (hd : p ∣ n+1) :
    (σ 0 n.factorial : ℝ) * (1+(p:ℝ)/(4*(n+1:ℝ))) ≤ σ 0 (n+1).factorial := by
  let a := n.factorial.factorization p
  let T := (σ 0 n.factorial : ℝ)
  let U := (σ 0 (p*n.factorial) : ℝ)
  have hpos : 0 < a+1 := by omega
  have hval : a*(p-1) ≤ n := (Nat.le_div_iff_mul_le (by have := hp.two_le; omega)).mp
    (Nat.factorization_factorial_le_div_pred hp n)
  have hpLE := Nat.le_of_dvd (Nat.succ_pos n) hd
  have hp2 := hp.two_le
  have hbound : p*(a+1) ≤ 4*(n+1) := by
    have h := Nat.mul_le_mul_left a (show p ≤ 2*(p-1) by omega)
    nlinarith
  have hboundR : (p:ℝ)*((a:ℝ)+1) ≤ 4*((n:ℝ)+1) := by exact_mod_cast hbound
  have heq : U*((a:ℝ)+1) = T*((a:ℝ)+2) := by
    dsimp [U,T,a]
    exact_mod_cast divisors_mul_prime n.factorial p (Nat.factorial_ne_zero _) hp
  have hr : (p:ℝ)/(4*((n:ℝ)+1)) ≤ 1/((a:ℝ)+1) :=
    (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by linarith)
  have hU : T*(1+1/((a:ℝ)+1)) = U := by
    field_simp
    nlinarith
  have hmono : σ 0 (p*n.factorial) ≤ σ 0 (n+1).factorial := by
    simp only [ArithmeticFunction.sigma_zero_apply]
    apply card_le_card (Nat.divisors_subset_of_dvd (Nat.factorial_ne_zero _) ?_)
    rw [Nat.factorial_succ]
    exact Nat.mul_dvd_mul hd (dvd_refl _)
  calc
    _ ≤ T*(1+1/((a:ℝ)+1)) := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    _ = U := hU
    _ ≤ _ := by dsimp [U]; exact_mod_cast hmono

lemma log_factors (m : ℕ) (hm : 0 < m) :
    log (m:ℝ) = ∑ p ∈ m.primeFactors, (m.factorization p : ℝ)*log p := by
  have h : (m:ℝ) = ∏ p ∈ m.primeFactors, (p:ℝ)^(m.factorization p) := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hm.ne'
  calc
    _ = log (∏ p ∈ m.primeFactors, (p:ℝ)^(m.factorization p)) := congrArg log h
    _ = _ := by rw [Real.log_prod (fun p hp => pow_ne_zero _
        (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero))]; simp only [Real.log_pow]
lemma count_large (n h : ℕ) (hn : 2 ≤ n) (hh : h ≤ n) (A B η : ℝ)
    (hs : (∑ i ∈ range h, ∑ p ∈ (n+i+1).primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ A),
      ((n+i+1).factorization p : ℝ)*log p) ≤ (4/9+η/2)*(h:ℝ)*log n)
    (hm : (∑ i ∈ range h, ∑ p ∈ (n+i+1).primeFactors.filter (fun p : ℕ => A < (p:ℝ) ∧ (p:ℝ) ≤ B),
      ((n+i+1).factorization p : ℝ)*log p) ≤ (5/9-η)*(h:ℝ)*log n) :
    η*h ≤ 4*((((range h).filter (fun i => ∃ p ∈ (n+i+1).primeFactors, B < (p:ℝ))).card : ℕ):ℝ) := by
  let w (i p : ℕ) := ((n+i+1).factorization p : ℝ)*log p
  let small (i : ℕ) := ∑ p ∈ (n+i+1).primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ A), w i p
  let mid (i : ℕ) := ∑ p ∈ (n+i+1).primeFactors.filter (fun p : ℕ => A < (p:ℝ) ∧ (p:ℝ) ≤ B), w i p
  let Hit (i : ℕ) := ∃ p ∈ (n+i+1).primeFactors, B < (p:ℝ)
  let G := (range h).filter (fun i => ∃ p ∈ (n+i+1).primeFactors, B < (p:ℝ))
  change η*h ≤ 4*(G.card:ℝ)
  change (∑ i ∈ range h, small i) ≤ _ at hs
  change (∑ i ∈ range h, mid i) ≤ _ at hm
  have hln : 0 < log (n:ℝ) := log_pos (by exact_mod_cast hn)
  have hw i p (hp : p ∈ (n+i+1).primeFactors) : 0 ≤ w i p := by
    apply mul_nonneg (Nat.cast_nonneg _) (log_nonneg _)
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
  have each i (hi : i ∈ range h) :
      log (n:ℝ) ≤ small i + mid i + (if Hit i then 2*log n else 0) := by
    have hm0 : 0 < n+i+1 := by omega
    by_cases he : Hit i
    · simp only [if_pos he]
      have hp1 : 0 ≤ small i := sum_nonneg (fun p hp => hw _ _ (mem_filter.mp hp).1)
      have hp2 : 0 ≤ mid i := sum_nonneg (fun p hp => hw _ _ (mem_filter.mp hp).1)
      linarith
    · simp only [if_neg he,add_zero]
      calc
        _ ≤ log ((n+i+1 : ℕ):ℝ) := log_le_log (by positivity) (by exact_mod_cast (show n ≤ n+i+1 by omega))
        _ = ∑ p ∈ (n+i+1).primeFactors, w i p := log_factors _ hm0
        _ = small i + mid i := by
          rw [← sum_filter_add_sum_filter_not (n+i+1).primeFactors (fun p => (p:ℝ) ≤ A)]
          dsimp only [small,mid]
          congr 1
          apply sum_congr _ (fun _ _ => rfl)
          ext p
          simp only [mem_filter, not_le]
          exact ⟨fun h => ⟨h.1,h.2,le_of_not_gt (fun h' => he ⟨p,h.1,h'⟩)⟩,
            fun h => ⟨h.1,h.2.1⟩⟩
  have hsum := sum_le_sum each
  have hconst : (∑ i ∈ range h, if Hit i then 2*log n else 0) = (G.card:ℝ)*(2*log n) := by
    rw [← Finset.sum_filter]; simp [G,Hit]
  simp only [sum_const,card_range,nsmul_eq_mul,sum_add_distrib,hconst] at hsum
  exact le_of_mul_le_mul_right (by nlinarith : (η*h)*log n ≤ (4*(G.card:ℝ))*log n) hln

lemma gain_window (n h : ℕ) (hn : 1 ≤ n) (hh : h ≤ n) (B : ℝ) (hB : 0 ≤ B) :
    let G := (range h).filter (fun i => ∃ p ∈ (n+i+1).primeFactors, B < (p:ℝ))
    (σ 0 n.factorial:ℝ)*(1+(G.card:ℝ)*(B/(8*n))) ≤ σ 0 (n+h).factorial := by
  let G := (range h).filter (fun i => ∃ p ∈ (n+i+1).primeFactors, B < (p:ℝ))
  have memG {i : ℕ} : i ∈ G ↔ i ∈ range h ∧ ∃ p ∈ (n+i+1).primeFactors, B < (p:ℝ) := by simp [G]
  let T (i : ℕ) := (σ 0 (n+i).factorial : ℝ)
  let u := B/(8*n)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hT : Monotone T := by
    intro a b hab
    dsimp [T]
    exact_mod_cast (show σ 0 (n+a).factorial ≤ σ 0 (n+b).factorial by
      simp only [ArithmeticFunction.sigma_zero_apply]
      exact card_le_card (Nat.divisors_subset_of_dvd (Nat.factorial_ne_zero _)
        (Nat.factorial_dvd_factorial (by omega))))
  have hinc (i : ℕ) (hi : i ∈ range h) :
      (if i ∈ G then T 0 * u else 0) ≤ T (i+1) - T i := by
    by_cases h : i ∈ G
    · simp only [if_pos h]
      obtain ⟨p,hp,hpB⟩ := (memG.mp h).2
      have hr := mem_range.mp hi
      have hnum : (n:ℝ)+i+1 ≤ 2*n := by exact_mod_cast (show n+i+1 ≤ 2*n by omega)
      have hstep := gain (n+i) p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
      push_cast at hstep
      have hfrac : u ≤ (p:ℝ)/(4*((n:ℝ)+i+1)) := by
        dsimp [u]
        exact div_le_div₀ (by positivity) hpB.le (by positivity) (by linarith)
      have h := (mul_le_mul_of_nonneg_left (add_le_add_right hfrac 1) (show 0 ≤ T i from Nat.cast_nonneg _))
      change T i * (1+(p:ℝ)/(4*((n:ℝ)+i+1))) ≤ T (i+1) at hstep
      have h0 := mul_le_mul_of_nonneg_right (hT (Nat.zero_le i)) hu
      linarith
    · simp only [if_neg h]
      exact sub_nonneg.mpr (hT (by omega))
  have ht := sum_le_sum hinc
  have hsub : ((range h).filter (· ∈ G)) = G := by
    ext i
    exact ⟨fun hi => (mem_filter.mp hi).2, fun hi => mem_filter.mpr ⟨(memG.mp hi).1,hi⟩⟩
  rw [← Finset.sum_filter, hsub, sum_const, nsmul_eq_mul, sum_range_sub] at ht
  change T 0*(1+(G.card:ℝ)*u) ≤ T h
  linarith
theorem main : H1 → H2 → type_of% @Erdos420.erdos_420.variants.pow_four_ninths := by
  intro hsmall hmiddle
  obtain ⟨η,hη,hmiddle⟩ := hmiddle
  have growth (r : ℝ) (hr : 0 < r) : Tendsto (fun n : ℕ => (n:ℝ)^r) atTop atTop :=
    (tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop
  filter_upwards [hsmall (η/2) (by positivity),hmiddle,eventually_ge_atTop (2:ℕ),
      (growth (4/9) (by norm_num)).eventually_ge_atTop 2,
      (growth (1/10000) (by norm_num)).eventually_ge_atTop (64/η)]
    with n hs hm hn hpow hbig
  let A := (n:ℝ)^((4:ℝ)/9)
  let B := (n:ℝ)^((5:ℝ)/9+1/10000)
  let h := ⌊A⌋₊
  let G := (range h).filter (fun i => ∃ p ∈ (n+i+1).primeFactors, B < (p:ℝ))
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 2 ≤ A := hpow
  have hfloor : A < (h:ℝ)+1 := Nat.lt_floor_add_one _
  have hh : h ≤ n := by
    have hA' : A ≤ (n:ℝ)^((1:ℝ)) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    rw [Real.rpow_one] at hA'
    exact_mod_cast (Nat.floor_le (show 0 ≤ A by linarith)).trans hA'
  have hc : η*h ≤ 4*(G.card:ℝ) := count_large n h hn hh A B η hs hm
  have hsave : η*A ≤ 8*(G.card:ℝ) := by
    have he : A ≤ 2*(h:ℝ) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left he hη.le]
  have hAB : A*B = (n:ℝ)*(n:ℝ)^((1:ℝ)/10000) := by
    dsimp [A,B]
    rw [← Real.rpow_add hnR,show (4:ℝ)/9 + (5/9+1/10000) = 1+1/10000 by ring,
      Real.rpow_add hnR, Real.rpow_one]
  have hηb : 64 ≤ η*(n:ℝ)^((1:ℝ)/10000) := by
    have h' := (div_le_iff₀ hη).mp hbig
    linarith
  have htotal : 8*(n:ℝ) ≤ (G.card:ℝ)*B := by
    have h' := mul_le_mul_of_nonneg_right hsave hB.le
    rw [mul_assoc η A B,hAB] at h'
    nlinarith [mul_le_mul_of_nonneg_left hηb hnR.le]
  have hgain := gain_window n h (by omega) hh B hB.le
  change (σ 0 n.factorial:ℝ)*(1+(G.card:ℝ)*(B/(8*n))) ≤ σ 0 (n+h).factorial at hgain
  have hhg : 1 ≤ (G.card:ℝ)*(B/(8*n)) := by
    rw [← mul_div_assoc]
    exact (one_le_div (by positivity)).mpr htotal
  have ht : (0:ℝ) < σ 0 n.factorial := by
    exact_mod_cast ArithmeticFunction.sigma_pos 0 _ (Nat.factorial_ne_zero n)
  change 2 ≤ (σ 0 (n+h).factorial:ℝ)/(σ 0 n.factorial:ℝ)
  apply (le_div_iff₀ ht).mpr
  exact (by nlinarith [mul_le_mul_of_nonneg_left (by linarith : (2:ℝ) ≤ 1+(G.card:ℝ)*(B/(8*n))) ht.le] :
    2 * (σ 0 n.factorial:ℝ) ≤ (σ 0 n.factorial:ℝ)*(1+(G.card:ℝ)*(B/(8*n)))).trans hgain

end OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1

end

section

-- Step Erdos420.erdos_420.variants.pow_four_ninths.R1.H1: hypothesis H1 of reduction Erdos420.erdos_420.variants.pow_four_ninths.R1

/-!
Let `h = ⌊n ^ (4/9)⌋`. The product `(n + 1) ⋯ (n + h)` equals `choose (n + h) h * h !`. For a
prime `p ≤ h` the exponent of `p` in the binomial coefficient is at most `log_p (n + h)`, so the
primes up to `h` contribute at most `log (h !) + π(h) log (n + h)` to the double sum. Now
`log (h !) ≤ h log h ≤ (4/9) h log n`, and by Chebyshev `π(h) log (n + h) = O(h)`.
-/

open Finset Real

namespace OMA

theorem prod_eq (n h : ℕ) : ∏ i ∈ range h, (n + i + 1) = (n + h).choose h * h.factorial := by
  have hM : n.factorial * ∏ i ∈ range h, (n + i + 1) = (n + h).factorial := by
    induction h with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ, ← mul_assoc, ih, ← add_assoc, Nat.factorial_succ]
      ring
  have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left h n)
  rw [Nat.add_sub_cancel] at h1
  apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos n)
  rw [hM, ← h1]
  ring

theorem core (n h : ℕ) :
    ∑ i ∈ range h, ∑ p ∈ (range (h + 1)).filter Nat.Prime,
        ((n + i + 1).factorization p : ℝ) * Real.log p ≤
      Real.log (h.factorial : ℝ) +
        (((range (h + 1)).filter Nat.Prime).card : ℝ) * Real.log ((n + h : ℕ) : ℝ) := by
  rw [Finset.sum_comm]
  have hfac : ∀ p : ℕ, ∑ i ∈ range h, ((n + i + 1).factorization p : ℝ) * Real.log p =
      (((n + h).choose h).factorization p : ℝ) * Real.log p +
        ((h.factorial).factorization p : ℝ) * Real.log p := by
    intro p
    have h1 : (∏ i ∈ range h, (n + i + 1)).factorization p =
        ∑ i ∈ range h, (n + i + 1).factorization p := by
      rw [Nat.factorization_prod (fun i _ => by omega)]
      exact Finsupp.finset_sum_apply _ _ _
    have h2 : ((n + h).choose h * h.factorial).factorization p =
        ((n + h).choose h).factorization p + (h.factorial).factorization p := by
      rw [Nat.factorization_mul (Nat.choose_pos (Nat.le_add_left h n)).ne'
        (Nat.factorial_ne_zero h)]
      rfl
    rw [← Finset.sum_mul, ← Nat.cast_sum, ← h1, OMA.prod_eq, h2]
    push_cast
    ring
  simp only [hfac]
  rw [Finset.sum_add_distrib, add_comm]
  apply add_le_add
  · -- the factorial part
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
    refine (Finset.sum_subset ?_ ?_).ge
    · intro p hp
      rw [Nat.support_factorization] at hp
      have hp' := Nat.mem_primeFactors.1 hp
      have hle : p ≤ h := (Nat.Prime.dvd_factorial hp'.1).1 hp'.2.1
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hp'.1⟩
    · intro p _ hnot
      have h0 : (h.factorial).factorization p = 0 := by
        by_contra hne
        exact hnot (Finsupp.mem_support_iff.2 hne)
      rw [h0]
      simp
  · -- the binomial part
    have hb : ∀ p ∈ (range (h + 1)).filter Nat.Prime,
        (((n + h).choose h).factorization p : ℝ) * Real.log p ≤ Real.log ((n + h : ℕ) : ℝ) := by
      intro p hp
      have hpp : p.Prime := (Finset.mem_filter.1 hp).2
      have hppos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
      have h1 : (((n + h).choose h).factorization p : ℝ) ≤ (Nat.log p (n + h) : ℝ) := by
        exact_mod_cast Nat.factorization_choose_le_log
      have hnh : n + h ≠ 0 := by
        have := Finset.mem_range.1 (Finset.mem_filter.1 hp).1
        have := hpp.two_le
        omega
      have h2 : ((p : ℝ) ^ Nat.log p (n + h)) ≤ ((n + h : ℕ) : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self p hnh
      have h3 := Real.log_le_log (pow_pos hppos _) h2
      rw [Real.log_pow] at h3
      exact (mul_le_mul_of_nonneg_right h1 hlogp).trans h3
    calc ∑ p ∈ (range (h + 1)).filter Nat.Prime,
          (((n + h).choose h).factorization p : ℝ) * Real.log p
        ≤ ∑ _p ∈ (range (h + 1)).filter Nat.Prime, Real.log ((n + h : ℕ) : ℝ) :=
          Finset.sum_le_sum hb
      _ = (((range (h + 1)).filter Nat.Prime).card : ℝ) * Real.log ((n + h : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]

end OMA

theorem OMA.erdos420Factorial : OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1.H1 := by
  unfold OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1.H1
  intro η hη
  have hY : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((4 : ℝ) / 9)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hX : Filter.Tendsto (fun n : ℕ => ((⌊(n : ℝ) ^ ((4 : ℝ) / 9)⌋₊ : ℕ) : ℝ))
      Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_nat_floor_atTop.comp hY)
  have hpi : ∀ᶠ n : ℕ in Filter.atTop,
      (Nat.primeCounting ⌊((⌊(n : ℝ) ^ ((4 : ℝ) / 9)⌋₊ : ℕ) : ℝ)⌋₊ : ℝ) ≤
        (Real.log 4 + 1) * ((⌊(n : ℝ) ^ ((4 : ℝ) / 9)⌋₊ : ℕ) : ℝ) /
          Real.log ((⌊(n : ℝ) ^ ((4 : ℝ) / 9)⌋₊ : ℕ) : ℝ) :=
    hX.eventually (Chebyshev.eventually_primeCounting_le one_pos)
  have hlogn : ∀ᶠ n : ℕ in Filter.atTop, max (15 / η) (9 * Real.log 2) ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop _
  filter_upwards [hpi, hlogn, hY.eventually_ge_atTop 2, Filter.eventually_ge_atTop 2]
    with n hpi hlogn hy2 hn2
  intro h
  have hdef : h = ⌊(n : ℝ) ^ ((4 : ℝ) / 9)⌋₊ := rfl
  rw [← hdef, Nat.floor_natCast] at hpi
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < n := by linarith
  have hy0 : (0 : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 9) := by linarith
  have hhle : (h : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 9) := by rw [hdef]; exact Nat.floor_le hy0
  have hhgt : (n : ℝ) ^ ((4 : ℝ) / 9) < (h : ℝ) + 1 := by rw [hdef]; exact Nat.lt_floor_add_one _
  clear_value h
  have hL1 : 15 / η ≤ Real.log (n : ℝ) := (le_max_left _ _).trans hlogn
  have hL2 : 9 * Real.log 2 ≤ Real.log (n : ℝ) := (le_max_right _ _).trans hlogn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
  have hlogy : Real.log ((n : ℝ) ^ ((4 : ℝ) / 9)) = 4 / 9 * Real.log (n : ℝ) :=
    Real.log_rpow hnpos _
  have hh1 : (1 : ℝ) ≤ h := by linarith
  have hhpos : (0 : ℝ) < h := by linarith
  -- `log h ≤ (4/9) log n` and `log h ≥ (1/3) log n`
  have hlogh_le : Real.log (h : ℝ) ≤ 4 / 9 * Real.log (n : ℝ) := by
    rw [← hlogy]
    exact Real.log_le_log hhpos hhle
  have hlogh_ge : 1 / 3 * Real.log (n : ℝ) ≤ Real.log (h : ℝ) := by
    have h1 : (n : ℝ) ^ ((4 : ℝ) / 9) ≤ 2 * (h : ℝ) := by linarith
    have h2 := Real.log_le_log (by linarith : (0 : ℝ) < (n : ℝ) ^ ((4 : ℝ) / 9)) h1
    rw [hlogy, Real.log_mul (by norm_num) hhpos.ne'] at h2
    linarith
  have hlogh_pos : 0 < Real.log (h : ℝ) := by linarith
  -- `h ≤ n`
  have hyn : (n : ℝ) ^ ((4 : ℝ) / 9) ≤ n := by
    calc (n : ℝ) ^ ((4 : ℝ) / 9) ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = n := Real.rpow_one _
  have hlognh : Real.log ((n + h : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have h1 : ((n + h : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by push_cast; linarith
    have h2 := Real.log_le_log (by push_cast; linarith : (0 : ℝ) < ((n + h : ℕ) : ℝ)) h1
    rw [Real.log_mul (by norm_num) hnpos.ne'] at h2
    linarith
  -- restrict the inner sums to the primes up to `h`
  have hinner : ∀ i ∈ range h,
      ∑ p ∈ (n + i + 1).primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 9)),
        ((n + i + 1).factorization p : ℝ) * Real.log p =
      ∑ p ∈ (range (h + 1)).filter Nat.Prime, ((n + i + 1).factorization p : ℝ) * Real.log p := by
    intro i _
    apply Finset.sum_subset
    · intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
      have hpp := (Nat.mem_primeFactors.1 hp1).1
      have hph : p ≤ h := by
        have : (p : ℝ) < (h : ℝ) + 1 := lt_of_le_of_lt hp2 hhgt
        have : p < h + 1 := by exact_mod_cast this
        omega
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hpp⟩
    · intro p hp hnot
      obtain ⟨hp1, hpp⟩ := Finset.mem_filter.1 hp
      have hph : p ≤ h := by have := Finset.mem_range.1 hp1; omega
      have hpy : (p : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 9) := by
        have : (p : ℝ) ≤ h := by exact_mod_cast hph
        linarith
      have hnp : p ∉ (n + i + 1).primeFactors := fun hmem =>
        hnot (Finset.mem_filter.2 ⟨hmem, hpy⟩)
      have h0 : (n + i + 1).factorization p = 0 := by
        by_contra hne
        apply hnp
        rw [← Nat.support_factorization]
        exact Finsupp.mem_support_iff.2 hne
      rw [h0]
      simp
  rw [Finset.sum_congr rfl hinner]
  refine (OMA.core n h).trans ?_
  -- the factorial term
  have hfact : Real.log (h.factorial : ℝ) ≤ 4 / 9 * (h : ℝ) * Real.log (n : ℝ) := by
    have h1 : (h.factorial : ℝ) ≤ (h : ℝ) ^ h := by exact_mod_cast Nat.factorial_le_pow h
    have h2 := Real.log_le_log (by exact_mod_cast Nat.factorial_pos h) h1
    rw [Real.log_pow] at h2
    have h3 : (h : ℝ) * Real.log (h : ℝ) ≤ (h : ℝ) * (4 / 9 * Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogh_le hhpos.le
    linarith
  -- the prime counting term
  have hcard : ((range (h + 1)).filter Nat.Prime).card = Nat.primeCounting h := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hlog4 : Real.log 4 + 1 ≤ 5 / 2 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have := Real.log_two_lt_d9
    linarith
  have hpi2 : (Nat.primeCounting h : ℝ) * Real.log ((n + h : ℕ) : ℝ) ≤ 15 * (h : ℝ) := by
    have h1 : (Nat.primeCounting h : ℝ) ≤ 5 / 2 * (h : ℝ) / (1 / 3 * Real.log (n : ℝ)) := by
      refine hpi.trans ?_
      rw [div_le_div_iff₀ hlogh_pos (by linarith)]
      have ha : (Real.log 4 + 1) * (h : ℝ) ≤ 5 / 2 * (h : ℝ) :=
        mul_le_mul_of_nonneg_right hlog4 hhpos.le
      have hb : 0 ≤ (Real.log 4 + 1) * (h : ℝ) := by
        have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        positivity
      calc (Real.log 4 + 1) * (h : ℝ) * (1 / 3 * Real.log (n : ℝ))
          ≤ (Real.log 4 + 1) * (h : ℝ) * Real.log (h : ℝ) :=
            mul_le_mul_of_nonneg_left hlogh_ge hb
        _ ≤ 5 / 2 * (h : ℝ) * Real.log (h : ℝ) :=
            mul_le_mul_of_nonneg_right ha hlogh_pos.le
    have h2 : 5 / 2 * (h : ℝ) / (1 / 3 * Real.log (n : ℝ)) * (2 * Real.log (n : ℝ)) =
        15 * (h : ℝ) := by
      field_simp
      ring
    have hpc0 : (0 : ℝ) ≤ Nat.primeCounting h := Nat.cast_nonneg _
    calc (Nat.primeCounting h : ℝ) * Real.log ((n + h : ℕ) : ℝ)
        ≤ (Nat.primeCounting h : ℝ) * (2 * Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hlognh hpc0
      _ ≤ 5 / 2 * (h : ℝ) / (1 / 3 * Real.log (n : ℝ)) * (2 * Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ = 15 * (h : ℝ) := h2
  have h15 : 15 * (h : ℝ) ≤ η * (h : ℝ) * Real.log (n : ℝ) := by
    have h1 : 15 ≤ η * Real.log (n : ℝ) := by
      have := mul_le_mul_of_nonneg_left hL1 hη.le
      rwa [mul_div_cancel₀ _ hη.ne'] at this
    nlinarith
  rw [hcard]
  have hsplit : (4 / 9 + η) * (h : ℝ) * Real.log (n : ℝ) =
      4 / 9 * (h : ℝ) * Real.log (n : ℝ) + η * (h : ℝ) * Real.log (n : ℝ) := by ring
  rw [hsplit]
  linarith

end

section

/-! Formal proof components for the four-ninths factorial window. -/

-- Source module BlockReduction
section

/-!
# A finite sieve reduction for the intermediate-prime estimate

The analytic input is an unweighted count of prime occurrences on 48 fixed
logarithmic bands. These bounds follow on paper by summing (19) of Erdős,
Graham, Ivić and Pomerance over multiplicative blocks. The theorem
prime_power_removal below proves the second hypothesis unconditionally.
-/

namespace OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2

open Finset Real Filter
open scoped Classical

/-- On each of the 48 fixed bands, count a prime only once per window term.
The tolerance absorbs the uniform error in the local sieve bound. -/
def H1 : Prop := ∀ᶠ n : ℕ in atTop,
  let edge (j : ℕ) : ℚ :=
    if j ≤ 16 then 4/9 + j*(77/162-4/9)/16
    else if j ≤ 32 then 77/162 + ((j-16 : ℕ) : ℚ)*(29/54-77/162)/16
    else 29/54 + ((j-32 : ℕ) : ℚ)*(50009/90000-29/54)/16
  let allowance (j : ℕ) : ℚ :=
    let v := edge (j+1)
    let θ := if j < 16 then (4/7)/(17/42-(5/7)*v)
             else if j < 32 then 1/(19/54-v/2) else 12
    (v-edge j)*θ + 1/1000000
  let h := ⌊(n:ℝ)^(4/9:ℝ)⌋₊
  let S := (range h).sigma (fun i => (n+i+1).primeFactors.filter (fun p : ℕ =>
    (n:ℝ)^(4/9:ℝ) < p ∧ (p:ℝ) ≤ (n:ℝ)^(5/9+1/10000:ℝ)))
  ∀ j < 48,
    ((S.filter (fun z => (n:ℝ)^(edge j : ℝ) < (z.2:ℝ) ∧
      (z.2:ℝ) ≤ (n:ℝ)^(edge (j+1) : ℝ))).card : ℝ) ≤ (allowance j : ℝ)*h

/-- Repeated prime powers in the middle range have negligible logarithmic weight. -/
def H2 : Prop := ∀ᶠ n : ℕ in atTop,
  let h := ⌊(n:ℝ)^(4/9:ℝ)⌋₊
  let S := (range h).sigma (fun i => (n+i+1).primeFactors.filter (fun p : ℕ =>
    (n:ℝ)^(4/9:ℝ) < p ∧ (p:ℝ) ≤ (n:ℝ)^(5/9+1/10000:ℝ)))
  (∑ z ∈ S, ((n+z.1+1).factorization z.2 : ℝ)*log z.2) ≤
    (∑ z ∈ S, log z.2) + (1/5000)*(h:ℝ)*log n

/-- An interval of length h contains at most (n+h)/(h+1)² pairs (m,p)
with p > h and p² ∣ m. The base p can be composite. -/
theorem square_hits (n h : ℕ) (s : Finset (ℕ × ℕ))
    (hits : ∀ z ∈ s, n < z.1 ∧ z.1 ≤ n+h ∧ h < z.2 ∧ z.2^2 ∣ z.1) :
    s.card ≤ (n+h)/(h+1)^2 := by
  let q (z : ℕ × ℕ) := z.1 / z.2^2
  have recover (z : ℕ × ℕ) (hz : z ∈ s) : q z * z.2^2 = z.1 :=
    Nat.div_mul_cancel (hits z hz).2.2.2
  have pos (z : ℕ × ℕ) (hz : z ∈ s) : 0 < q z := by
    by_contra! hn
    have hzero : q z = 0 := by omega
    have hrec := recover z hz
    rw [hzero, zero_mul] at hrec
    have := (hits z hz).1
    omega
  have gap {p r t : ℕ} (ht : 0 < t) (hp : h < p) (hpr : p < r) :
      t*p^2+h < t*r^2 := by
    have hstep : p^2 + (h+1) ≤ r^2 := by
      have hs := Nat.pow_le_pow_left (show p+1 ≤ r by omega) 2
      nlinarith
    have hh := Nat.mul_le_mul_left t hstep
    have hg := Nat.mul_le_mul_right (h+1) (show 1 ≤ t by omega)
    nlinarith
  have bound := Finset.card_le_card_of_injOn (s := s)
    (t := Icc 1 ((n+h)/(h+1)^2)) q (by
      intro z hz
      obtain ⟨_, hu, hp, _⟩ := hits z hz
      apply mem_Icc.mpr
      refine ⟨pos z hz, (Nat.le_div_iff_mul_le (by positivity)).mpr ?_⟩
      calc q z * (h+1)^2 ≤ q z * z.2^2 :=
             Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
           _ = z.1 := recover z hz
           _ ≤ n+h := hu) (by
      intro x hx y hy eq
      obtain ⟨hxl, hxu, hxp, _⟩ := hits x hx
      obtain ⟨hyl, hyu, hyp, _⟩ := hits y hy
      have rx := recover x hx
      have ry := recover y hy
      rw [← eq] at ry
      have hp : x.2 = y.2 := by
        rcases lt_trichotomy x.2 y.2 with h|h|h
        · have hg := gap (pos x hx) hxp h
          omega
        · exact h
        · have hg := gap (pos x hx) hyp h
          omega
      apply Prod.ext _ hp
      rw [hp] at rx
      omega)
  simpa using bound

/-- Replacing valuations by one copy per prime incurs at most the displayed
additive error. The input s may restrict the primes to any desired band. -/
theorem weighted_excess (n h : ℕ) (s : Finset (ℕ × ℕ)) (hcube : n+h < (h+1)^3)
    (hits : ∀ z ∈ s, n < z.1 ∧ z.1 ≤ n+h ∧ h < z.2 ∧ z.2.Prime ∧ z.2 ∣ z.1) :
    (∑ z ∈ s, (z.1.factorization z.2 : ℝ) * log z.2) ≤
      (∑ z ∈ s, log z.2) + (((n+h)/(h+1)^2 : ℕ) : ℝ) * log (n+h : ℕ) := by
  let t := s.filter (fun z => z.2^2 ∣ z.1)
  have bound := square_hits n h t (by
    intro z hz
    obtain ⟨hs, hd⟩ := mem_filter.mp hz
    obtain ⟨hl, hu, hp, _⟩ := hits z hs
    exact ⟨hl, hu, hp, hd⟩)
  have hlog : 0 ≤ log (n+h : ℕ) := Real.log_natCast_nonneg _
  have single (z : ℕ × ℕ) (hz : z ∈ s) :
      (z.1.factorization z.2 : ℝ) * log z.2 ≤
        log z.2 + (if z.2^2 ∣ z.1 then log (n+h : ℕ) else 0) := by
    obtain ⟨hl, hu, hp, hprime, hd⟩ := hits z hz
    have hm : z.1 ≠ 0 := by omega
    have ppos := hprime.pos
    have logp := Real.log_natCast_nonneg z.2
    have logle : log (z.2 : ℝ) ≤ log (n+h : ℕ) :=
      log_le_log (by exact_mod_cast ppos) (by exact_mod_cast (Nat.le_of_dvd (by omega) hd).trans hu)
    have exp_le : z.1.factorization z.2 ≤ 2 := by
      by_contra! hbig
      have hd3 := (hprime.pow_dvd_iff_le_factorization hm).mpr (show 3 ≤ z.1.factorization z.2 by omega)
      have hlo := Nat.pow_le_pow_left (show h+1 ≤ z.2 by omega) 3
      have hhi := Nat.le_of_dvd (show 0 < z.1 by omega) hd3
      omega
    split_ifs with hs
    · have he : (z.1.factorization z.2 : ℝ) ≤ 2 := by exact_mod_cast exp_le
      nlinarith [mul_nonneg (sub_nonneg.mpr he) logp]
    · have he : z.1.factorization z.2 ≤ 1 := by
        by_contra! hh
        exact hs ((hprime.pow_dvd_iff_le_factorization hm).mpr hh)
      have he' : (z.1.factorization z.2 : ℝ) ≤ 1 := by exact_mod_cast he
      nlinarith [mul_nonneg (sub_nonneg.mpr he') logp]
  calc (∑ z ∈ s, (z.1.factorization z.2 : ℝ) * log z.2) ≤ _ := sum_le_sum single
       _ = (∑ z ∈ s, log z.2) + (t.card : ℝ)*log (n+h : ℕ) := by
         rw [sum_add_distrib, ← sum_filter]
         simp [t]
       _ ≤ _ := by gcongr


/-- At the four-ninths window, the square-hit budget is at most 2 n^(1/9). -/
theorem four_ninths_scale : ∀ᶠ n : ℕ in Filter.atTop,
    let h := ⌊(n:ℝ)^(4/9 : ℝ)⌋₊
    n+h < (h+1)^3 ∧ (((n+h)/(h+1)^2 : ℕ) : ℝ) ≤ 2*(n:ℝ)^(1/9 : ℝ) := by
  have pw : Filter.Tendsto (fun n : ℕ => (n:ℝ)^(1/3:ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)).comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_ge_atTop (1:ℕ), pw.eventually_ge_atTop 2] with n hn hthird
  let A := (n:ℝ)^(4/9:ℝ)
  let h := ⌊A⌋₊
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hA : 0 ≤ A := Real.rpow_nonneg hn0.le _
  have hfloor : A < (h:ℝ)+1 := Nat.lt_floor_add_one A
  have hsmall : (h:ℝ) ≤ n := (Nat.floor_le hA).trans (by
    simpa [A] using Real.rpow_le_rpow_of_exponent_le hn1 (show (4:ℝ)/9 ≤ 1 by norm_num))
  have cube : A^3 = (n:ℝ)*(n:ℝ)^(1/3:ℝ) := by
    dsimp [A]
    rw [← Real.rpow_mul_natCast hn0.le, show (4/9:ℝ)*(3:ℕ) = 1+1/3 by norm_num, Real.rpow_add hn0, Real.rpow_one]
  have square : A^2*(n:ℝ)^(1/9:ℝ) = n := by
    dsimp [A]
    rw [← Real.rpow_mul_natCast hn0.le, ← Real.rpow_add hn0]
    norm_num
  change n+h < (h+1)^3 ∧ _
  constructor
  · have hcube : A^3 < ((h:ℝ)+1)^3 := pow_lt_pow_left₀ hfloor hA (by decide)
    have hn3 : (n:ℝ)+(h:ℝ) < ((h:ℝ)+1)^3 := by
      nlinarith [mul_nonneg hn0.le (sub_nonneg.mpr hthird)]
    exact_mod_cast hn3
  · let q := (n+h)/(h+1)^2
    have hdiv : q*(h+1)^2 ≤ n+h := Nat.div_mul_le_self _ _
    have hdivR : (q:ℝ)*((h:ℝ)+1)^2 ≤ (n:ℝ)+h := by exact_mod_cast hdiv
    have hs := pow_le_pow_left₀ hA hfloor.le 2
    have hx : 0 < A^2 := by dsimp [A]; positivity
    have hx' : (q:ℝ)*A^2 ≤ (2*(n:ℝ)^(1/9:ℝ))*A^2 := by
      nlinarith [mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg q)]
    exact (mul_le_mul_iff_left₀ hx).mp hx'


/-- The logarithmic cost of repeated hits is eventually at most one five-thousandth
of the total window scale. No estimate on the distribution of primes is used. -/
theorem four_ninths_error : ∀ᶠ n : ℕ in atTop,
    let h := ⌊(n:ℝ)^(4/9:ℝ)⌋₊
    n+h < (h+1)^3 ∧
    (((n+h)/(h+1)^2 : ℕ) : ℝ)*log (n+h : ℕ) ≤ (1/5000)*(h:ℝ)*log n := by
  have pw (r : ℝ) (hr : 0 < r) : Tendsto (fun n : ℕ => (n:ℝ)^r) atTop atTop :=
    (tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop
  filter_upwards [four_ninths_scale, eventually_ge_atTop (2:ℕ),
    (pw (1/3) (by norm_num)).eventually_ge_atTop 40000,
    (pw (4/9) (by norm_num)).eventually_ge_atTop 2] with n hs hn hthird hbig
  let A := (n:ℝ)^(4/9:ℝ)
  let h := ⌊A⌋₊
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0:ℝ) < n := by linarith
  have hA : 0 ≤ A := Real.rpow_nonneg hn0.le _
  have hle : (h:ℝ) ≤ n := (Nat.floor_le hA).trans (by
    simpa [A] using Real.rpow_le_rpow_of_exponent_le hn1 (show (4:ℝ)/9 ≤ 1 by norm_num))
  have hfloor : A < (h:ℝ)+1 := Nat.lt_floor_add_one A
  change 2 ≤ A at hbig
  have heq : (n:ℝ)^(1/9:ℝ)*(n:ℝ)^(1/3:ℝ) = A := by
    rw [← Real.rpow_add hn0]
    dsimp [A]
    norm_num
  change 40000 ≤ (n:ℝ)^(1/3:ℝ) at hthird
  have ninth := Real.rpow_nonneg hn0.le (1/9:ℝ)
  have coeff : 4*(n:ℝ)^(1/9:ℝ) ≤ (1/5000)*(h:ℝ) := by
    nlinarith [mul_nonneg ninth (sub_nonneg.mpr hthird)]
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have arg : (0:ℝ) < n+h := by positivity
  have logle : log (n+h : ℕ) ≤ 2*log n := by
    push_cast
    calc log ((n:ℝ)+h) ≤ log ((n:ℝ)^2) :=
           log_le_log arg (by nlinarith [mul_nonneg hn0.le (sub_nonneg.mpr hn2)])
         _ = 2*log n := by simp [Real.log_pow]
  refine ⟨hs.1, ?_⟩
  have lognonneg := Real.log_natCast_nonneg n
  calc
    _ ≤ (2*(n:ℝ)^(1/9:ℝ))*(2*log n) :=
      mul_le_mul hs.2 logle (Real.log_natCast_nonneg _) (by positivity)
    _ = (4*(n:ℝ)^(1/9:ℝ))*log n := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right coeff lognonneg

lemma crossing(f : ℕ → ℝ) (x : ℝ) (h0 : f 0 < x) (k : ℕ) (hk : x ≤ f k) :
    ∃ j < k, f j < x ∧ x ≤ f (j+1) := by
  induction k with
  | zero => exact (not_lt_of_ge hk h0).elim
  | succ k ih =>
    by_cases hend : x ≤ f k
    · obtain ⟨j, hj, lo, hi⟩ := ih hend
      exact ⟨j, by omega, lo, hi⟩
    · exact ⟨k, by omega, lt_of_not_ge hend, hk⟩

/-- The log weight of any set of hits in the complete middle range is bounded
by the finite unweighted counts. S can label a prime together with its position. -/
theorem first_power_mass (edge allowance : ℕ → ℚ)
    (edge0 : edge 0 = 4/9) (edge48 : edge 48 = 5/9+1/10000)
    (edge_nonnegative : ∀ j, 0 ≤ edge (j+1))
    (budget : (4/9 : ℚ) + ∑ j ∈ range 48, edge (j+1)*allowance j < 2499/2500)
    {α : Type*} (S : Finset α) (p : α → ℕ) (n h : ℕ) (hn : 1 ≤ n)
    (range_hits : ∀ z ∈ S, (n:ℝ)^(4/9:ℝ) < (p z:ℝ) ∧
      (p z:ℝ) ≤ (n:ℝ)^(5/9+1/10000:ℝ))
    (counts : ∀ j < 48,
      ((S.filter (fun z => (n:ℝ)^(edge j : ℝ) < (p z:ℝ) ∧
        (p z:ℝ) ≤ (n:ℝ)^(edge (j+1) : ℝ))).card : ℝ) ≤ (allowance j : ℝ)*h) :
    (∑ z ∈ S, log (p z)) ≤ (5/9-1/2500)*(h:ℝ)*log n := by
  let bin (j : ℕ) := S.filter (fun z => (n:ℝ)^(edge j : ℝ) < (p z:ℝ) ∧
                                      (p z:ℝ) ≤ (n:ℝ)^(edge (j+1) : ℝ))
  let cap (j : ℕ) := (edge (j+1) : ℝ)*log n
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have cap_pos (j : ℕ) : 0 ≤ cap j := by
    exact mul_nonneg (by exact_mod_cast edge_nonnegative j) (Real.log_natCast_nonneg n)
  have cover (z : α) (hz : z ∈ S) :
      ∃ j < 48, z ∈ bin j ∧ log (p z) ≤ cap j := by
    obtain ⟨hlo,hhi⟩ := range_hits z hz
    let f (j : ℕ) := (n:ℝ)^(edge j : ℝ)
    have hzero : f 0 < (p z:ℝ) := by simpa [f,edge0] using hlo
    have hlast : (p z:ℝ) ≤ f 48 := by simpa [f,edge48] using hhi
    obtain ⟨j, hj, lo, hi⟩ := crossing f (p z) hzero 48 hlast
    have pp : (0:ℝ) < p z := (Real.rpow_pos_of_pos hn0 _).trans lo
    refine ⟨j,hj,mem_filter.mpr ⟨hz, lo, hi⟩, ?_⟩
    simpa only [f, cap, log_rpow hn0] using Real.log_le_log pp hi
  have point (z : α) (hz : z ∈ S) : log (p z) ≤ ∑ j ∈ range 48, if z ∈ bin j then cap j else 0 := by
    obtain ⟨j,hj,hmem,hle⟩ := cover z hz
    apply hle.trans
    have hs := Finset.single_le_sum (f := fun j => if z ∈ bin j then cap j else 0)
      (fun j (_ : j ∈ range 48) => by split <;> first | exact cap_pos j | exact le_rfl) (mem_range.mpr hj)
    simpa only [if_pos hmem] using hs
  calc
    (∑ z ∈ S, log (p z)) ≤ _ := sum_le_sum point
    _ = ∑ j ∈ range 48, ((bin j).card : ℝ)*cap j := by
      rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      rw [← sum_filter]
      have filt : S.filter (fun z => z ∈ bin j) = bin j := by
        ext z
        simp [bin]
      simp [filt]
    _ ≤ ∑ j ∈ range 48, ((allowance j : ℝ)*h)*cap j := by
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (counts j (mem_range.mp hj)) (cap_pos j)
    _ = ((∑ j ∈ range 48, edge (j+1)*allowance j : ℚ) : ℝ)*h*log n := by
      push_cast
      simp only [sum_mul]
      apply sum_congr rfl
      intro j _
      dsimp [cap]
      ring
    _ ≤ _ := by
      have H := budget
      have R : (∑ j ∈ range 48, edge (j+1)*allowance j : ℚ) ≤ 5/9-1/2500 := by linarith
      have R' : ((∑ j ∈ range 48, edge (j+1)*allowance j : ℚ):ℝ) ≤ 5/9-1/2500 := by
        have v := (Rat.cast_le (K := ℝ)).mpr R
        norm_num at v ⊢
        exact v
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right R' (Nat.cast_nonneg _))
        (Real.log_natCast_nonneg _)

/-- The second input is already proved; its proof uses no sieve estimate. -/
theorem prime_power_removal : H2 := by
  filter_upwards [four_ninths_error] with n herr
  let h := ⌊(n:ℝ)^(4/9:ℝ)⌋₊
  let S := (range h).sigma (fun i => (n+i+1).primeFactors.filter (fun p : ℕ =>
    (n:ℝ)^(4/9:ℝ) < p ∧ (p:ℝ) ≤ (n:ℝ)^(5/9+1/10000:ℝ)))
  let e : (Σ _ : ℕ, ℕ) ↪ (ℕ × ℕ) := ⟨fun z => (n+z.1+1,z.2), by
    rintro ⟨i,p⟩ ⟨j,q⟩ heq
    have hi := congrArg Prod.fst heq
    have hp := congrArg Prod.snd heq
    change n+i+1=n+j+1 at hi
    change p=q at hp
    have ij : i=j := by omega
    subst j
    subst q
    rfl⟩
  have hA : (h:ℝ) ≤ (n:ℝ)^(4/9:ℝ) := Nat.floor_le (by positivity)
  have mass := weighted_excess n h (S.map e) herr.1 (by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := mem_map.mp hx
    obtain ⟨hi, hp⟩ := mem_sigma.mp hz
    have hilt := mem_range.mp hi
    obtain ⟨hp, hlo, _⟩ := mem_filter.mp hp
    change n < n+z.1+1 ∧ n+z.1+1 ≤ n+h ∧ h < z.2 ∧ z.2.Prime ∧ z.2 ∣ n+z.1+1
    exact ⟨by omega, by omega, by exact_mod_cast hA.trans_lt hlo,
      Nat.prime_of_mem_primeFactors hp, Nat.dvd_of_mem_primeFactors hp⟩)
  change (∑ z ∈ S, ((n+z.1+1).factorization z.2 : ℝ)*log z.2) ≤
    (∑ z ∈ S, log z.2) + (1/5000)*(h:ℝ)*log n
  have em (z : (Σ _ : ℕ, ℕ)) : e z = (n+z.1+1,z.2) := rfl
  simp only [Finset.sum_map, em] at mass
  exact mass.trans (add_le_add le_rfl herr.2)

set_option maxRecDepth 4000 in
theorem main : H1 → H2 → OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1.H2 := by
  intro hcount hrepeat
  refine ⟨1/5000, by norm_num, ?_⟩
  filter_upwards [hcount, hrepeat, eventually_ge_atTop (1:ℕ)] with n hc hr hn
  let edge (j : ℕ) : ℚ :=
    if j ≤ 16 then 4/9 + j*(77/162-4/9)/16
    else if j ≤ 32 then 77/162 + ((j-16 : ℕ) : ℚ)*(29/54-77/162)/16
    else 29/54 + ((j-32 : ℕ) : ℚ)*(50009/90000-29/54)/16
  let allowance (j : ℕ) : ℚ :=
    let v := edge (j+1)
    let θ := if j < 16 then (4/7)/(17/42-(5/7)*v)
             else if j < 32 then 1/(19/54-v/2) else 12
    (v-edge j)*θ + 1/1000000
  let h := ⌊(n:ℝ)^(4/9:ℝ)⌋₊
  let S := (range h).sigma (fun i => (n+i+1).primeFactors.filter (fun p : ℕ =>
    (n:ℝ)^(4/9:ℝ) < p ∧ (p:ℝ) ≤ (n:ℝ)^(5/9+1/10000:ℝ)))
  have zero : edge 0 = 4/9 := by norm_num [edge]
  have last : edge 48 = 5/9+1/10000 := by norm_num [edge]
  have nonneg (j : ℕ) : 0 ≤ edge (j+1) := by
    dsimp only [edge]
    split
    · norm_num
      positivity
    · split <;> norm_num <;> positivity
  have B : (4/9 : ℚ) + ∑ j ∈ range 48, edge (j+1)*allowance j < 2499/2500 := by
    dsimp only [edge, allowance]
    decide +kernel
  have sta := first_power_mass edge allowance zero last nonneg B S (fun z => z.2) n h hn
    (fun z hz => (mem_filter.mp (mem_sigma.mp hz).2).2) hc
  change (∑ z ∈ S, ((n+z.1+1).factorization z.2 : ℝ)*log z.2) ≤
    (∑ z ∈ S, log z.2) + (1/5000)*(h:ℝ)*log n at hr
  have bound := hr.trans (add_le_add sta le_rfl)
  have total : (∑ z ∈ S, ((n+z.1+1).factorization z.2 : ℝ)*log z.2) ≤
      (5/9-1/5000)*(h:ℝ)*log n := by linarith only [bound]
  simpa only [S, Finset.sum_sigma] using total

end OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2
end

-- Source module FactorialSelbergWeights
section

/-! Selberg weights for the divisor density 1/d on the squarefree integers
up to an integer level. The normalization is at least the harmonic sum.
The signed weights are bounded by one and their main term is exactly the
reciprocal normalizer. This supplies the main term of the short-interval
sieve in Erdős, Graham, Ivić and Pomerance (1996), equations (14)–(17). -/
noncomputable section
open Finset UniqueFactorizationMonoid

namespace FactorialSieve

def level (z : ℕ) : Finset ℕ := (Icc 1 z).filter Squarefree

def normalizer (z : ℕ) : ℝ := ∑ d ∈ level z, ((d.totient : ℝ)⁻¹)

private lemma equal_totient_ratios {a b : ℕ} (h : a.primeFactors = b.primeFactors) :
    a.totient * b = b.totient * a := by
  have ha := Nat.totient_eq_mul_prod_factors a
  have hb := Nat.totient_eq_mul_prod_factors b
  rw [h] at ha
  exact_mod_cast (show (a.totient : ℚ)*b = (b.totient : ℚ)*a by rw [ha,hb]; ring)

private lemma radical_fiber (z q : ℕ) (hq : 0 < q) :
    (∑ n ∈ (Icc 1 z).filter (fun n : ℕ => radical n = q), (n : ℝ)⁻¹) ≤
    (q.totient : ℝ)⁻¹ := by
  let S := (Icc 1 z).filter (fun n : ℕ => radical n = q)
  let M := q ^ z
  let t (n : ℕ) := (M/n)*q
  have hM : 0 < M := pow_pos hq _
  have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have info (n : ℕ) (hn : n ∈ S) :
      0 < n ∧ 0 < t n ∧ t n * n = M*q ∧ t n ∣ M ∧ (t n).totient*n = M*q.totient := by
    obtain ⟨hi,hr⟩ := mem_filter.mp hn
    obtain ⟨hpos,hle⟩ := mem_Icc.mp hi
    have hqdiv : q ∣ n := hr ▸ radical_dvd_self
    have hd : n ∣ M := by
      have hd1 := Nat.dvd_radical_pow_self (show n ≠ 0 by omega)
      rw [hr] at hd1
      exact hd1.trans (pow_dvd_pow q hle)
    have hm := Nat.div_mul_cancel hd
    have hqk := Nat.div_mul_cancel hqdiv
    have heq : t n*n=M*q := by dsimp [t]; rw [mul_right_comm, hm]
    have ht : 0 < t n := by
      by_contra! hbad
      have hh : t n = 0 := by omega
      rw [hh, zero_mul] at heq
      exact (Nat.ne_of_gt (Nat.mul_pos hM hq)) heq.symm
    have hdM : t n ∣ M := by
      refine ⟨n/q, ?_⟩
      dsimp [t]
      rw [mul_assoc, mul_comm q (n/q), hqk, hm]
    have factors : (t n).primeFactors = q.primeFactors := by
      apply Subset.antisymm
      · exact (Nat.primeFactors_mono hdM hM.ne').trans (by
          by_cases hz : z = 0
          · omega
          · simp [M, Nat.primeFactors_pow _ hz])
      · exact Nat.primeFactors_mono (dvd_mul_left q _) ht.ne'
    have ratio := equal_totient_ratios factors
    have cross : (t n).totient*n*q = M*q.totient*q := by
      calc (t n).totient*n*q = ((t n).totient*q)*n := by ring
           _ = q.totient*(t n*n) := by rw [ratio]; ring
           _ = M*q.totient*q := by rw [heq]; ring
    exact ⟨hpos,ht,heq,hdM,Nat.eq_of_mul_eq_mul_right hq cross⟩
  have inj : Set.InjOn t S := by
    intro a ha b hb e
    obtain ⟨_,ht,hab,_,_⟩ := info a ha
    obtain ⟨_,_,hbb,_,_⟩ := info b hb
    rw [← e] at hbb
    exact Nat.eq_of_mul_eq_mul_left ht (hab.trans hbb.symm)
  have small : S.image t ⊆ M.divisors := by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := mem_image.mp ha
    exact Nat.mem_divisors.mpr ⟨(info n hn).2.2.2.1,hM.ne'⟩
  have cnt : (∑ n ∈ S, (t n).totient) ≤ M := by
    rw [← Nat.sum_totient M, ← Finset.sum_image (f := Nat.totient) inj]
    exact sum_le_sum_of_subset_of_nonneg small (by intros; omega)
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  change (∑ n ∈ S, (n : ℝ)⁻¹) ≤ _
  calc
    _ = ∑ n ∈ S, ((t n).totient : ℝ)/(M*q.totient) := by
      apply sum_congr rfl
      intro n hn
      obtain ⟨hp,_,_,_,hh⟩ := info n hn
      have hpR : (0:ℝ) < n := by exact_mod_cast hp
      have hhR : ((t n).totient : ℝ)*n=(M:ℝ)*q.totient := by exact_mod_cast hh
      field_simp
      linarith
    _ = ((∑ n ∈ S, (t n).totient : ℕ):ℝ)/(M*q.totient) := by simp [sum_div]
    _ ≤ (M:ℝ)/(M*q.totient) := div_le_div_of_nonneg_right (by exact_mod_cast cnt) (by positivity)
    _ = _ := by field_simp

theorem harmonic_le_normalizer (z : ℕ) : (harmonic z : ℝ) ≤ normalizer z := by
  have maps (n : ℕ) (hn : n ∈ Icc 1 z) : radical n ∈ level z := by
    obtain ⟨hp,hle⟩ := mem_Icc.mp hn
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.radical_pos _,
      (Nat.radical_le_self_iff.mpr (by omega)).trans hle⟩, squarefree_radical⟩
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  simp only [Rat.cast_inv, Rat.cast_natCast]
  rw [← Finset.sum_fiberwise_of_maps_to maps (fun n : ℕ => (n:ℝ)⁻¹)]
  exact sum_le_sum (fun q hq => radical_fiber z q (mem_Icc.mp (mem_filter.mp hq).1).1)

theorem log_le_normalizer (z : ℕ) : Real.log ((z:ℝ)+1) ≤ normalizer z := by
  apply le_trans _ (harmonic_le_normalizer z)
  simpa using log_add_one_le_harmonic z


open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

def alpha (z d : ℕ) : ℝ := (μ d : ℝ) * ∑ q ∈ level z, if d ∣ q then (q.totient : ℝ)⁻¹ else 0
def weight (z d : ℕ) : ℝ := d * alpha z d / normalizer z

lemma mem_level {z d : ℕ} : d ∈ level z ↔ (1 ≤ d ∧ d ≤ z) ∧ Squarefree d := by
  simp [level]

lemma down {z q d : ℕ} (hq : q ∈ level z) (hd : d ∣ q) : d ∈ level z := by
  obtain ⟨⟨hp,hle⟩,hs⟩ := mem_level.mp hq
  exact mem_level.mpr ⟨⟨Nat.pos_of_dvd_of_pos hd hp,(Nat.le_of_dvd hp hd).trans hle⟩,hs.squarefree_of_dvd hd⟩

private lemma mu_sum (m : ℕ) : (∑ k ∈ m.divisors, (μ k : ℝ)) = if m=1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f m) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply, one_apply] at h
  split_ifs at h ⊢ <;> exact_mod_cast h

private lemma mu_interval {z q l : ℕ} (hq : q ∈ level z) (hl : l ∈ level z) :
    (∑ d ∈ level z, if l ∣ d ∧ d ∣ q then (μ d : ℝ) else 0) =
      if q=l then (μ l : ℝ) else 0 := by
  have lp := (mem_level.mp hl).1.1
  have qp := (mem_level.mp hq).1.1
  have qsf := (mem_level.mp hq).2
  by_cases hd : l ∣ q
  · obtain ⟨m, rfl⟩ := hd
    have mp : 0 < m := Nat.pos_of_mul_pos_left qp
    have shift (k : ℕ) (hk : k ∈ m.divisors) : l*k ∈ level z :=
      down hq (Nat.mul_dvd_mul_left l (Nat.dvd_of_mem_divisors hk))
    rw [← sum_filter]
    have ev : (∑ d ∈ (level z).filter (fun d => l ∣ d ∧ d ∣ l*m), (μ d : ℝ)) =
        ∑ k ∈ m.divisors, (μ l : ℝ)*(μ k : ℝ) := by
      symm
      apply sum_bij (fun k _ => l*k)
      · intro k hk
        exact mem_filter.mpr ⟨shift k hk, dvd_mul_right _ _, Nat.mul_dvd_mul_left _ (Nat.dvd_of_mem_divisors hk)⟩
      · intro a _ b _ he
        exact Nat.eq_of_mul_eq_mul_left lp he
      · intro d h
        obtain ⟨_, ⟨k,rfl⟩, hk⟩ := mem_filter.mp h
        exact ⟨k,Nat.mem_divisors.mpr ⟨Nat.dvd_of_mul_dvd_mul_left lp hk, mp.ne'⟩,rfl⟩
      · intro k hk
        have cop := Nat.coprime_of_squarefree_mul (mem_level.mp (shift k hk)).2
        exact_mod_cast (isMultiplicative_moebius.map_mul_of_coprime cop).symm
    rw [ev, ← mul_sum, mu_sum]
    by_cases hm : m=1
    · simp [hm]
    · have hne : l*m ≠ l := fun eq => hm (Nat.eq_of_mul_eq_mul_left lp (eq.trans (Nat.mul_one l).symm))
      simp [hm,hne]
  · have hne : q ≠ l := by rintro rfl; exact hd dvd_rfl
    rw [if_neg hne, sum_eq_zero]
    intro d _
    exact if_neg (fun h => hd (h.1.trans h.2))

/-- These are the diagonal coordinates of the unnormalized weights. -/
theorem transform {z l : ℕ} (hl : l ∈ level z) :
    (∑ d ∈ level z, if l ∣ d then alpha z d else 0) = (μ l : ℝ)*(l.totient : ℝ)⁻¹ := by
  calc
    _ = ∑ d ∈ level z, ∑ q ∈ level z, (if l ∣ d ∧ d ∣ q then (μ d : ℝ) else 0)*(q.totient : ℝ)⁻¹ := by
      apply sum_congr rfl
      intro d _
      by_cases hd : l ∣ d
      · simp only [if_pos hd, alpha, mul_sum]
        apply sum_congr rfl
        intro q _
        by_cases hq : d ∣ q <;> simp [hd,hq]
      · simp [hd]
    _ = ∑ q ∈ level z, (if q=l then (μ l : ℝ) else 0)*(q.totient : ℝ)⁻¹ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro q hq
      rw [← sum_mul, mu_interval hq hl]
    _ = _ := by simp [ite_mul, hl]

/-- Writing gcd(d,e) as a sum of totients diagonalizes the quadratic form. -/
theorem diagonal (z : ℕ) (a : ℕ → ℝ) :
    (∑ d ∈ level z, ∑ e ∈ level z, a d*a e*(d.gcd e : ℝ)) =
      ∑ l ∈ level z, (l.totient : ℝ)*(∑ d ∈ level z, if l ∣ d then a d else 0)^2 := by
  have expand {d e : ℕ} (hd : d ∈ level z) (he : e ∈ level z) :
      (d.gcd e : ℝ) = ∑ l ∈ level z, if l ∣ d ∧ l ∣ e then (l.totient : ℝ) else 0 := by
    rw [← sum_filter]
    have filt : (level z).filter (fun l => l ∣ d ∧ l ∣ e) = (d.gcd e).divisors := by
      ext l
      have gn : d.gcd e ≠ 0 := (Nat.gcd_pos_of_pos_left _ (mem_level.mp hd).1.1).ne'
      constructor
      · intro h
        exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd_iff.mpr (mem_filter.mp h).2,gn⟩
      · intro h
        have both := Nat.dvd_gcd_iff.mp (Nat.dvd_of_mem_divisors h)
        exact mem_filter.mpr ⟨down hd both.1,both⟩
    rw [filt, ← Nat.cast_sum, Nat.sum_totient]
  calc
    _ = ∑ d ∈ level z, ∑ e ∈ level z, ∑ l ∈ level z,
      (l.totient : ℝ)*(if l ∣ d then a d else 0)*(if l ∣ e then a e else 0) := by
      apply sum_congr rfl; intro d hd
      apply sum_congr rfl; intro e he
      rw [expand hd he, mul_sum]
      apply sum_congr rfl; intro l _
      by_cases h₁ : l ∣ d <;> by_cases h₂ : l ∣ e <;> simp [h₁,h₂]
      ring
    _ = _ := by
      simp_rw [sq, mul_sum, sum_mul]
      rw [sum_comm]
      -- Move the l-sum to the outside before collecting each of the two copies.
      conv_lhs => congr; rfl; intro e; rw [sum_comm]
      rw [sum_comm]
      apply sum_congr rfl; intro l _
      rw [sum_comm]
      apply sum_congr rfl; intro d _
      rw [mul_sum]
      apply sum_congr rfl; intro e _
      ring

theorem normalizer_pos {z : ℕ} (hz : 1 ≤ z) : 0 < normalizer z := by
  apply Finset.sum_pos' (fun q _ => by positivity)
  exact ⟨1, mem_level.mpr ⟨⟨le_rfl,hz⟩,squarefree_one⟩, by norm_num⟩

theorem weight_one {z : ℕ} (hz : 1 ≤ z) : weight z 1 = 1 := by
  simp [weight,alpha,normalizer]
  exact (normalizer_pos hz).ne'

/-- Exact value of the Selberg main term for the constructed weights. -/
theorem main_term {z : ℕ} (hz : 1 ≤ z) :
    (∑ d ∈ level z, ∑ e ∈ level z, weight z d*weight z e/(Nat.lcm d e : ℝ)) = (normalizer z)⁻¹ := by
  have gp := normalizer_pos hz
  have diag := diagonal z (alpha z)
  have eval : (∑ d ∈ level z, ∑ e ∈ level z, alpha z d*alpha z e*(d.gcd e : ℝ)) = normalizer z := by
    rw [diag]
    apply sum_congr rfl
    intro l hl
    rw [transform hl]
    have sqμ := moebius_sq_eq_one_of_squarefree (mem_level.mp hl).2
    have sqR : (μ l : ℝ)^2=1 := by exact_mod_cast sqμ
    have tp : (0:ℝ) < l.totient := by exact_mod_cast Nat.totient_pos.mpr (mem_level.mp hl).1.1
    rw [mul_pow, sqR, one_mul]
    field_simp
  calc
    _ = (∑ d ∈ level z, ∑ e ∈ level z, alpha z d*alpha z e*(d.gcd e : ℝ))/(normalizer z)^2 := by
      simp only [sum_div]
      apply sum_congr rfl; intro d hd
      apply sum_congr rfl; intro e he
      have hp := Nat.lcm_pos (mem_level.mp hd).1.1 (mem_level.mp he).1.1
      have lp : (0:ℝ) < Nat.lcm d e := by exact_mod_cast hp
      have eq : (d.gcd e : ℝ)*(d.lcm e : ℝ)=(d:ℝ)*e := by exact_mod_cast Nat.gcd_mul_lcm d e
      dsimp only [weight]
      field_simp
      linear_combination (alpha z d * alpha z e) * (-eq)
    _ = _ := by rw [eval]; field_simp

/-- For each multiple q of d, deleting a divisor of d gives a different
member of the level. Its least common multiple with d recovers q. -/
lemma divisor_budget (z d : ℕ) :
    (∑ q ∈ (level z).filter (fun q => d ∣ q), (d:ℝ)/(q.totient:ℝ)) ≤ normalizer z := by
  let F := (level z).filter (fun q => d ∣ q)
  let pairs := F ×ˢ d.divisors
  let f (x : ℕ × ℕ) := x.1/x.2
  have pair_facts (x : ℕ × ℕ) (hx : x ∈ pairs) :
      f x ∈ level z ∧ d.lcm (f x) = x.1 ∧ x.1/(f x) = x.2 := by
    obtain ⟨hq,ht⟩ := mem_product.mp hx
    obtain ⟨hL,hdq⟩ := mem_filter.mp hq
    have td := Nat.dvd_of_mem_divisors ht
    have tq := td.trans hdq
    have fs := Nat.div_mul_cancel tq
    have hf := Nat.div_dvd_of_dvd tq
    have cp := Nat.coprime_of_squarefree_mul (by rw [fs]; exact (mem_level.mp hL).2)
    refine ⟨down hL hf,Nat.dvd_antisymm (Nat.lcm_dvd hdq hf) ?_,Nat.div_div_self tq (mem_level.mp hL).2.ne_zero⟩
    change x.1 ∣ d.lcm (x.1/x.2)
    have hprod := cp.mul_dvd_of_dvd_of_dvd (Nat.dvd_lcm_right d (x.1/x.2))
      (td.trans (Nat.dvd_lcm_left d _))
    rwa [fs] at hprod
  have inj : Set.InjOn f pairs := by
    intro x hx y hy h
    obtain ⟨_,hl,hdiv⟩ := pair_facts x hx
    obtain ⟨_,hl',hdiv'⟩ := pair_facts y hy
    have qeq := hl.symm.trans ((congrArg (Nat.lcm d) h).trans hl')
    exact Prod.ext qeq (hdiv.symm.trans (by rw [qeq,h,hdiv']))
  have sub : pairs.image f ⊆ level z := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    exact (pair_facts y hy).1
  have row (q : ℕ) (hq : q ∈ F) :
      (d:ℝ)/(q.totient:ℝ) = ∑ t ∈ d.divisors, ((q/t).totient:ℝ)⁻¹ := by
    obtain ⟨hL,hdq⟩ := mem_filter.mp hq
    have pos := (mem_level.mp hL).1.1
    have ttl : (∑ t ∈ d.divisors, (t.totient:ℝ)) = d := by exact_mod_cast Nat.sum_totient d
    rw [← ttl, sum_div]
    apply sum_congr rfl
    intro t ht
    have tq := (Nat.dvd_of_mem_divisors ht).trans hdq
    have hf := Nat.div_mul_cancel tq
    have sf : Squarefree (q/t*t) := by rw [hf]; exact (mem_level.mp hL).2
    have cop := Nat.coprime_of_squarefree_mul sf
    have tot := Nat.totient_mul cop
    rw [hf] at tot
    have posT : 0 < t.totient := Nat.totient_pos.mpr (Nat.pos_of_mem_divisors ht)
    have posU : 0 < (q/t).totient := Nat.totient_pos.mpr (Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd tq) pos)
    rw [tot, Nat.cast_mul]
    field_simp
  calc
    _ = ∑ q ∈ F, ∑ t ∈ d.divisors, ((q/t).totient:ℝ)⁻¹ := sum_congr rfl row
    _ = ∑ x ∈ pairs, ((f x).totient:ℝ)⁻¹ := by rw [Finset.sum_product]
    _ = ∑ q ∈ pairs.image f, (q.totient:ℝ)⁻¹ := (sum_image (f := fun n : ℕ => (n.totient:ℝ)⁻¹) inj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub (by intros; positivity)

theorem weight_abs_le_one {z d : ℕ} (hz : 1 ≤ z) (hd : d ∈ level z) :
    |weight z d| ≤ 1 := by
  have sfree := (mem_level.mp hd).2
  have hm : |(μ d : ℝ)| = 1 := by exact_mod_cast abs_moebius_eq_one_of_squarefree sfree
  have gp := normalizer_pos hz
  let F := (level z).filter (fun q => d ∣ q)
  have nonneg : 0 ≤ ∑ q ∈ F, (q.totient:ℝ)⁻¹ := sum_nonneg (by intros; positivity)
  rw [weight,alpha, ← sum_filter, abs_div, abs_mul, abs_mul, hm, one_mul,
    abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos gp, abs_of_nonneg nonneg, div_le_one gp, mul_sum]
  simpa only [div_eq_mul_inv] using divisor_budget z d


theorem main_term_bound {z : ℕ} (hz : 1 ≤ z) :
    (∑ d ∈ level z, ∑ e ∈ level z, weight z d*weight z e/(Nat.lcm d e : ℝ)) ≤
    (Real.log ((z:ℝ)+1))⁻¹ := by
  rw [main_term hz]
  have pos : 0 < Real.log ((z:ℝ)+1) := Real.log_pos (by exact_mod_cast (show 1 < z+1 by omega))
  exact inv_anti₀ pos (log_le_normalizer z)

end FactorialSieve
end
end

-- Source module FiniteWindowSieve
section

/-! The finite Λ² majorant used in equations (14)–(15) of the factorial
divisor paper, with integer endpoints and arbitrary real signed weights. -/
noncomputable section
open Finset

namespace FiniteWindowSieve

/-- An exact finite upper sieve. Here N(m) is any nonnegative multiplicity
(e.g. the number of multiples of m in the short interval), S is the block
of moduli, and D is the support of the level weights, containing 1. -/
theorem lcm_majorant (S D : Finset ℕ) (N w : ℕ → ℝ)
    (hN : ∀ m ∈ S, 0 ≤ N m) (h1 : 1 ∈ D) (hw : w 1 = 1)
    (sifted : Finset ℕ) (hsub : sifted ⊆ S)
    (hrough : ∀ m ∈ sifted, ∀ d ∈ D, d ∣ m → d = 1) :
    (∑ m ∈ sifted, N m) ≤
      ∑ d ∈ D, ∑ e ∈ D, w d * w e *
        (∑ m ∈ S, if Nat.lcm d e ∣ m then N m else 0) := by
  let W (d m : ℕ) := if d ∣ m then w d else 0
  have exact_one (m : ℕ) (hm : m ∈ sifted) : (∑ d ∈ D, W d m) = 1 := by
    rw [sum_eq_single_of_mem 1 h1]
    · simp [W, hw]
    · intro d hd hne
      exact if_neg (fun h => hne (hrough m hm d hd h))
  calc
    (∑ m ∈ sifted, N m) = ∑ m ∈ sifted, N m * (∑ d ∈ D, W d m)^2 := by
      apply sum_congr rfl
      intro m hm
      simp [exact_one m hm]
    _ ≤ ∑ m ∈ S, N m * (∑ d ∈ D, W d m)^2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun m hm _ => mul_nonneg (hN m hm) (sq_nonneg _))
    _ = ∑ d ∈ D, ∑ e ∈ D, w d * w e *
        (∑ m ∈ S, if Nat.lcm d e ∣ m then N m else 0) := by
      simp_rw [sq, sum_mul, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro d hd
      rw [sum_comm]
      apply sum_congr rfl
      intro e he
      apply sum_congr rfl
      intro m hm
      by_cases hdm : d ∣ m <;> by_cases hem : e ∣ m <;>
        simp [W, Nat.lcm_dvd_iff, hdm, hem]
      ring

/-- In a block entirely above the level, every prime passes the upper sieve. -/
theorem prime_block (S D : Finset ℕ) (N w : ℕ → ℝ) (z : ℕ)
    (hN : ∀ m ∈ S, 0 ≤ N m) (h1 : 1 ∈ D) (hw : w 1 = 1)
    (hD : ∀ d ∈ D, d ≤ z) (hS : ∀ m ∈ S, z < m) :
    (∑ p ∈ S.filter Nat.Prime, N p) ≤
      ∑ d ∈ D, ∑ e ∈ D, w d * w e *
        (∑ m ∈ S, if Nat.lcm d e ∣ m then N m else 0) := by
  apply lcm_majorant S D N w hN h1 hw _ (filter_subset _ _)
  intro m hm d hd hdm
  obtain ⟨hs, hp⟩ := mem_filter.mp hm
  rcases (Nat.dvd_prime hp).mp hdm with hone | heq
  · exact hone
  · have := hD d hd
    have := hS m hs
    omega

end FiniteWindowSieve
end
end

-- Source module FactorialSelbergBlock
section

/-! Boundary error for the harmonic sum of the multiples of a single
modulus in a multiplicative interval. Both endpoints may be real. -/
noncomputable section
open Finset Real
namespace FactorialRounding

private lemma harmonic_bracket (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    log ((b:ℝ)+1) - log ((a:ℝ)+1) ≤ ∑ j ∈ Ioc a b, (j:ℝ)⁻¹ ∧
    (∑ j ∈ Ioc a b, (j:ℝ)⁻¹) ≤ log b - log a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b h ih =>
    have bp : (0:ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    have p : 0 < (b:ℝ)+1 := by positivity
    have pp : 0 < (b:ℝ)+1+1 := by positivity
    have top := Real.log_le_sub_one_of_pos (div_pos pp p)
    rw [log_div pp.ne' p.ne'] at top
    have low := Real.one_sub_inv_le_log_of_pos (div_pos p bp)
    rw [log_div p.ne' bp.ne'] at low
    have e₁ : ((b:ℝ)+1+1)/(b+1)-1 = ((b:ℝ)+1)⁻¹ := by field_simp; ring
    have e₂ : 1-(((b:ℝ)+1)/b)⁻¹ = ((b:ℝ)+1)⁻¹ := by field_simp; ring
    rw [e₁] at top
    rw [e₂] at low
    rw [sum_Ioc_succ_top h]
    push_cast
    exact ⟨by linarith [ih.1], by linarith [ih.2]⟩

lemma harmonic_floor_error (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) :
    |(∑ j ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, (j:ℝ)⁻¹) - log (v/u)| ≤ 2/u := by
  let a := ⌊u⌋₊
  let b := ⌊v⌋₊
  have up : 0 < u := by linarith
  have vp : 0 < v := by linarith
  have ha : 1 ≤ a := Nat.floor_pos.mpr hu
  have ap : (0:ℝ) < a := by exact_mod_cast ha
  have hab : a ≤ b := Nat.floor_mono huv
  have bp : (0:ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have al : (a:ℝ) ≤ u := Nat.floor_le up.le
  have ah : u < (a:ℝ)+1 := Nat.lt_floor_add_one u
  have bl : (b:ℝ) ≤ v := Nat.floor_le vp.le
  have bh : v < (b:ℝ)+1 := Nat.lt_floor_add_one v
  have e₁ : log ((a:ℝ)+1)-log u ≤ 1/u := by
    have h := Real.log_le_sub_one_of_pos (div_pos (by positivity : 0 < (a:ℝ)+1) up)
    rw [log_div (by positivity) up.ne'] at h
    apply h.trans
    rw [sub_le_iff_le_add, div_le_iff₀ up]
    field_simp
    linarith
  have e₂ : log u - log a ≤ 2/u := by
    have h := Real.log_le_sub_one_of_pos (div_pos up ap)
    rw [log_div up.ne' ap.ne'] at h
    apply h.trans
    have step : u/(a:ℝ)-1 ≤ 1/a := by
      rw [sub_le_iff_le_add, div_le_iff₀ ap]
      field_simp
      linarith
    apply step.trans
    apply (div_le_div_iff₀ ap up).mpr
    have haR : (1:ℝ) ≤ a := by exact_mod_cast ha
    linarith
  have entry := harmonic_bracket a b ha hab
  rw [log_div vp.ne' up.ne', abs_le]
  change - (2/u) ≤ (∑ j ∈ Ioc a b, (j:ℝ)⁻¹) - _ ∧ _ ≤ _
  constructor
  · linarith [entry.1,log_le_log vp bh.le, one_div_pos.mpr up, show 2/u = 2*(1/u) by ring]
  · linarith [entry.2,log_le_log bp bl]

lemma sum_multiples (u v : ℝ) (t : ℕ) (ht : 0 < t) (f : ℕ → ℝ) :
    (∑ m ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, if t ∣ m then f m else 0) =
    ∑ j ∈ Ioc ⌊u/(t:ℝ)⌋₊ ⌊v/(t:ℝ)⌋₊, f (j*t) := by
  rw [← sum_filter, Nat.floor_div_natCast, Nat.floor_div_natCast]
  symm
  apply sum_bij (fun j _ => j*t)
  · intro j hj
    obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hj
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul ht).mp hlo,
      (Nat.le_div_iff_mul_le ht).mp hhi⟩, dvd_mul_left t j⟩
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_right ht h
  · intro m hm
    obtain ⟨hm,hd⟩ := mem_filter.mp hm
    obtain ⟨lo,hi⟩ := mem_Ioc.mp hm
    have hrec :=  Nat.div_mul_cancel hd
    refine ⟨m/t, mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul ht).mpr (by rwa [hrec]), Nat.div_le_div_right hi⟩, hrec⟩
  · intros; rfl

theorem multiples_error (u v : ℝ) (t : ℕ) (ht : 0 < t) (htu : (t:ℝ) ≤ u) (huv : u ≤ v) :
    |(∑ m ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, if t ∣ m then (m:ℝ)⁻¹ else 0) - log (v/u)/t| ≤ 2/u := by
  have tp : (0:ℝ) < t := by exact_mod_cast ht
  have up := tp.trans_le htu
  have vp := up.trans_le huv
  have base := harmonic_floor_error (u/t) (v/t) ((one_le_div tp).mpr htu) (by gcongr)
  have ratio : (v/(t:ℝ))/(u/t) = v/u := by field_simp
  rw [ratio] at base
  rw [sum_multiples _ _ t ht]
  simp only [Nat.cast_mul, mul_inv_rev, ← mul_sum]
  rw [div_eq_inv_mul (log (v/u)) (t:ℝ), ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr tp)]
  calc _ ≤ (t:ℝ)⁻¹*(2/(u/t)) := mul_le_mul_of_nonneg_left base (by positivity)
       _ = _ := by field_simp

end FactorialRounding
namespace FactorialSieve
open Finset Real

/-- The number of positive multiples of m in (n,n+h]. -/
def multiplicity (n h m : ℕ) : ℕ := (n+h)/m-n/m

/-- The centered fractional part of x/m for natural inputs and positive m. -/
def saw (x m : ℕ) : ℝ := (x%m : ℕ)/ (m : ℝ) - 1/2

/-- The sawtooth sum with moduli divisible by t in the multiplicative block. -/
def remainder (u v : ℝ) (x t : ℕ) : ℝ :=
  ∑ m ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, if t ∣ m then saw x m else 0

def weightedRemainder (z : ℕ) (u v : ℝ) (x : ℕ) : ℝ :=
  ∑ d ∈ level z, ∑ e ∈ level z, weight z d * weight z e * remainder u v x (d.lcm e)

private lemma quotient_real (x m : ℕ) (hm : 0 < m) :
    ((x/m : ℕ):ℝ) = (x:ℝ)/m - saw x m - 1/2 := by
  have exactR : (m:ℝ)*((x/m : ℕ):ℝ)+(x%m:ℕ) = x := by exact_mod_cast Nat.div_add_mod x m
  have hp : (0:ℝ) < m := by exact_mod_cast hm
  unfold saw
  field_simp
  linarith

private lemma split_count (n h m : ℕ) (hm : 0 < m) :
    (multiplicity n h m : ℝ) = h*(m:ℝ)⁻¹ + saw n m - saw (n+h) m := by
  rw [multiplicity, Nat.cast_sub (Nat.div_le_div_right (Nat.le_add_right n h)),
    quotient_real _ _ hm, quotient_real _ _ hm, Nat.cast_add]
  ring

/-- The factorial-window form of the finite Selberg block bound. The oscillating
remainder is kept signed. The elementary endpoint error has the explicit
constant 2 and holds for arbitrary real endpoints u,v. -/
theorem short_interval_block (n h z : ℕ) (u v : ℝ) (hz : 1 ≤ z) (hzu : (z:ℝ)^2 ≤ u) (huv : u ≤ v) :
    (∑ p ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime, (multiplicity n h p:ℝ)) ≤
    (h:ℝ)*log (v/u)/log ((z:ℝ)+1) + 2*h*(z:ℝ)^2/u +
      (weightedRemainder z u v n - weightedRemainder z u v (n+h)) := by
  let S := Ioc ⌊u⌋₊ ⌊v⌋₊
  let L := log (v/u)
  let C := (h:ℝ)*(2/u)
  let H (t : ℕ) := ∑ m ∈ S, if t ∣ m then (m:ℝ)⁻¹ else 0
  let W (d e : ℕ) := weight z d * weight z e
  have zr : (1:ℝ) ≤ z := by exact_mod_cast hz
  have zu : (z:ℝ) ≤ u := by nlinarith [sq_nonneg ((z:ℝ)-1)]
  have up : 0 < u := by linarith
  have lpos : 0 ≤ L := log_nonneg ((one_le_div up).mpr huv)
  have sieve := FiniteWindowSieve.prime_block S (level z) (fun m => (multiplicity n h m : ℝ))
    (weight z) z (fun _ _ => Nat.cast_nonneg _) (mem_level.mpr ⟨⟨le_rfl,hz⟩,squarefree_one⟩)
    (weight_one hz) (fun d hd => (mem_level.mp hd).1.2) (fun m hm =>
      (Nat.le_floor zu).trans_lt (mem_Ioc.mp hm).1)
  have split_row (t : ℕ) :
      (∑ m ∈ S, if t ∣ m then (multiplicity n h m : ℝ) else 0) =
      (h:ℝ)*H t + remainder u v n t - remainder u v (n+h) t := by
    simp only [H, remainder, ← sum_sub_distrib, ← sum_add_distrib, mul_sum, S]
    apply sum_congr rfl
    intro m hm
    by_cases hd : t ∣ m
    · simp only [if_pos hd]
      apply split_count
      have := (mem_Ioc.mp hm).1
      omega
    · simp [hd]
  have pair (d : ℕ) (hd : d ∈ level z) (e : ℕ) (he : e ∈ level z) :
      W d e*(∑ m ∈ S, if d.lcm e ∣ m then (multiplicity n h m:ℝ) else 0) ≤
      (h:ℝ)*L*(W d e/(d.lcm e : ℝ)) + C +
        (W d e*remainder u v n (d.lcm e) - W d e*remainder u v (n+h) (d.lcm e)) := by
    let t := d.lcm e
    have tp : 0 < t := Nat.lcm_pos (mem_level.mp hd).1.1 (mem_level.mp he).1.1
    have tl : t ≤ z^2 := by
      calc t ≤ d*e := Nat.le_of_dvd (Nat.mul_pos (mem_level.mp hd).1.1 (mem_level.mp he).1.1)
                         (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _))
           _ ≤ _ := by rw [sq]; exact Nat.mul_le_mul (mem_level.mp hd).1.2 (mem_level.mp he).1.2
    have htu : (t:ℝ) ≤ u := (by exact_mod_cast tl : (t:ℝ) ≤ (z:ℝ)^2).trans hzu
    have herr := FactorialRounding.multiples_error u v t tp htu huv
    change |H t-L/t| ≤ 2/u at herr
    have wh : |W d e| ≤ 1 := by
      change |weight z d * weight z e| ≤ 1
      rw [abs_mul]
      simpa using mul_le_mul (weight_abs_le_one hz hd) (weight_abs_le_one hz he) (abs_nonneg _) zero_le_one
    have scaled : W d e*((h:ℝ)*(H t - L/t)) ≤ C := by
      apply (le_abs_self _).trans
      have ah : |(h:ℝ)| = (h:ℝ) := abs_of_nonneg (Nat.cast_nonneg h)
      rw [abs_mul (W d e) _,abs_mul (h:ℝ) _,ah]
      calc _ ≤ 1*((h:ℝ)*(2/u)) := mul_le_mul wh (mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg h))
                                      (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) zero_le_one
           _ = _ := one_mul _
    rw [split_row]
    change W d e*((h:ℝ)*H t + remainder u v n t - remainder u v (n+h) t) ≤ _
    dsimp only [t] at scaled ⊢
    simp only [div_eq_mul_inv] at scaled ⊢
    linear_combination scaled
  have total := (sum_le_sum (fun d hd => sum_le_sum (fun e he => pair d hd e he)))
  have mainBound := main_term_bound hz
  have cardBound : (level z).card ≤ z := by
    simpa [level] using Finset.card_le_card (filter_subset Squarefree (Icc 1 z))
  have cardR : ((level z).card : ℝ) ≤ z := by exact_mod_cast cardBound
  have Cr : 0 ≤ C := mul_nonneg (Nat.cast_nonneg h) (by positivity)
  have constant : ((level z).card : ℝ)*((level z).card*C) ≤ 2*h*(z:ℝ)^2/u := by
    calc _ ≤ (z:ℝ)*(z*C) := by gcongr
         _ = _ := by dsimp [C]; ring
  have mainB := mul_le_mul_of_nonneg_left mainBound (mul_nonneg (Nat.cast_nonneg h) lpos)
  dsimp only [weightedRemainder]
  apply sieve.trans
  calc
    _ ≤ _ := total
    _ = ((h:ℝ)*L)*(∑ d ∈ level z, ∑ e ∈ level z, W d e/(d.lcm e : ℝ)) +
        ((level z).card : ℝ)*((level z).card*C) +
        ((∑ d ∈ level z, ∑ e ∈ level z, W d e*remainder u v n (d.lcm e)) -
        (∑ d ∈ level z, ∑ e ∈ level z, W d e*remainder u v (n+h) (d.lcm e))) := by
      simp only [sum_add_distrib, sum_sub_distrib, mul_sum, sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      change _ ≤ (h:ℝ)*L/log ((z:ℝ)+1) + _ + _
      rw [div_eq_mul_inv]
      exact add_le_add (add_le_add mainB constant) le_rfl




private lemma decreasing_power_sum (N : ℕ) (hN : 1 ≤ N) (e : ℝ) (he : e ≤ 0) (hne : e ≠ -1) :
    (∑ n ∈ Icc 1 N, (n:ℝ)^e) ≤ 1 + ((N:ℝ)^(e+1)-1)/(e+1) := by
  have NR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have ant : AntitoneOn (fun x : ℝ => x^e) (Set.Icc 1 (N:ℝ)) :=
    fun x hx y _ hxy => Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy he
  have bound := AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ => x^e) hN (by simpa using ant)
  simp only [Nat.cast_one] at bound
  have miss : (0:ℝ) ∉ Set.uIcc 1 (N:ℝ) := by simp [Set.uIcc_of_le NR]
  rw [integral_rpow (Or.inr ⟨hne,miss⟩), Real.one_rpow] at bound
  have shift : (∑ n ∈ Ioc 1 N, (n:ℝ)^e) =
      ∑ i ∈ Ico 1 N, ((i+1 : ℕ):ℝ)^e := by
    symm
    apply sum_bij (fun i _ => i+1)
    · intro i hi
      obtain ⟨hl,hu⟩ := mem_Ico.mp hi
      exact mem_Ioc.mpr ⟨by omega, by omega⟩
    · intros; omega
    · intro n hn
      obtain ⟨hl,hu⟩ := mem_Ioc.mp hn
      exact ⟨n-1,mem_Ico.mpr ⟨by omega,by omega⟩,by omega⟩
    · intros; rfl
  have seteq : Icc 1 N = insert 1 (Ioc 1 N) := by ext i; simp; omega
  rw [seteq,sum_insert (by simp),shift,Nat.cast_one,Real.one_rpow]
  exact add_le_add le_rfl bound

private lemma quotient_box (z : ℕ) (s : ℝ) :
    (∑ d ∈ level z, ∑ e ∈ level z, (d.lcm e : ℝ)^(-s)) ≤
    ∑ g ∈ Icc 1 z, (g:ℝ)^(-s)*(∑ a ∈ Icc 1 (z/g), (a:ℝ)^(-s))^2 := by
  let P := (level z) ×ˢ (level z)
  let g (x : ℕ × ℕ) := x.1.gcd x.2
  let h (x : ℕ × ℕ) := (x.1/g x,x.2/g x)
  let w (a : ℕ) := (a:ℝ)^(-s)
  have nonneg (a : ℕ) : 0 ≤ w a := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have gmem (x : ℕ × ℕ) (hx : x ∈ P) : g x ∈ Icc 1 z := by
    have hd := (mem_level.mp (mem_product.mp hx).1).1
    exact mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left _ hd.1, (Nat.le_of_dvd hd.1 (Nat.gcd_dvd_left _ _)).trans hd.2⟩
  have result (t : ℕ) (ht : t ∈ Icc 1 z) :
      (∑ x ∈ P.filter (fun x => g x = t), w (x.1.lcm x.2)) ≤ w t*(∑ a ∈ Icc 1 (z/t), w a)^2 := by
    let F := P.filter (fun x => g x=t)
    let I := Icc 1 (z/t)
    have tp := (mem_Icc.mp ht).1
    have info (x : ℕ × ℕ) (hx : x ∈ F) :
        (h x).1*t=x.1 ∧ (h x).2*t=x.2 ∧ h x ∈ I ×ˢ I ∧ x.1.lcm x.2=t*(h x).1*(h x).2 := by
      obtain ⟨hp,heq⟩ := mem_filter.mp hx
      have d := (mem_level.mp (mem_product.mp hp).1).1
      have e := (mem_level.mp (mem_product.mp hp).2).1
      have t1 : t ∣ x.1 := heq ▸ Nat.gcd_dvd_left x.1 x.2
      have t2 : t ∣ x.2 := heq ▸ Nat.gcd_dvd_right x.1 x.2
      have r1 : (h x).1*t=x.1 := by dsimp [h]; rw [heq,Nat.div_mul_cancel t1]
      have r2 : (h x).2*t=x.2 := by dsimp [h]; rw [heq,Nat.div_mul_cancel t2]
      have hp1 : 1 ≤ (h x).1 := by
        change 1 ≤ x.1 / g x
        rw [heq]
        exact Nat.div_pos (Nat.le_of_dvd d.1 t1) tp
      have hp2 : 1 ≤ (h x).2 := by
        change 1 ≤ x.2 / g x
        rw [heq]
        exact Nat.div_pos (Nat.le_of_dvd e.1 t2) tp
      refine ⟨r1,r2,mem_product.mpr ⟨mem_Icc.mpr ⟨hp1,(Nat.le_div_iff_mul_le tp).mpr (r1.trans_le d.2)⟩,
        mem_Icc.mpr ⟨hp2,(Nat.le_div_iff_mul_le tp).mpr (r2.trans_le e.2)⟩⟩,?_⟩
      apply Nat.eq_of_mul_eq_mul_right tp
      calc x.1.lcm x.2 * t = x.1*x.2 := by rw [← heq,mul_comm]; exact Nat.gcd_mul_lcm _ _
           _ = _ := by nth_rw 1 [← r1,← r2]; ring
    have inj : Set.InjOn h F := by
      intro x hx y hy eq
      obtain ⟨a,b,_,_⟩ := info x hx
      obtain ⟨c,d,_,_⟩ := info y hy
      exact Prod.ext (a.symm.trans (by rw [eq,c])) (b.symm.trans (by rw [eq,d]))
    have sub : F.image h ⊆ I ×ˢ I := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
      exact (info x hx).2.2.1
    let wpair (y : ℕ × ℕ) := w t*w y.1*w y.2
    calc
      _ = ∑ x ∈ F, wpair (h x) := by
        apply sum_congr rfl
        intro x hx
        rw [(info x hx).2.2.2]
        simp only [wpair,w,Nat.cast_mul]
        rw [Real.mul_rpow (by positivity) (by positivity),Real.mul_rpow (Nat.cast_nonneg t) (by positivity)]
      _ = ∑ y ∈ F.image h, wpair y := (sum_image (f := wpair) inj).symm
      _ ≤ ∑ y ∈ I ×ˢ I, wpair y := sum_le_sum_of_subset_of_nonneg sub (fun y _ _ =>
        mul_nonneg (mul_nonneg (nonneg _) (nonneg _)) (nonneg _))
      _ = _ := by simp only [sum_product,wpair, I, sq,← mul_sum,← sum_mul]; ring
  have sums := sum_le_sum result
  rw [sum_fiberwise_of_maps_to gmem] at sums
  simpa only [P,sum_product,w] using sums

/-- With both input divisors at most z, the positive fractional moment has
no logarithmic loss for any fixed 0 ≤ s < 1. -/
theorem lcm_fractional_moment {z : ℕ} (hz : 1 ≤ z) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∑ d ∈ level z, ∑ e ∈ level z, (d.lcm e : ℝ)^(-s)) ≤
    ((1+1/(1-s))/(1-s)^2)*(z:ℝ)^(2*(1-s)) := by
  let r := 1-s
  have rp : 0 < r := sub_pos.mpr hs1
  have zr : (0:ℝ) < z := by exact_mod_cast hz
  let C := (z:ℝ)^(2*r)/r^2
  have Cp : 0 ≤ C := by dsimp [C]; positivity
  have row (g : ℕ) (hg : g ∈ Icc 1 z) :
      (g:ℝ)^(-s)*(∑ a ∈ Icc 1 (z/g), (a:ℝ)^(-s))^2 ≤ C*(g:ℝ)^(s-2) := by
    obtain ⟨gp,gz⟩ := mem_Icc.mp hg
    have gpR : (0:ℝ) < g := by exact_mod_cast gp
    have q1 : 1 ≤ z/g := (Nat.le_div_iff_mul_le gp).mpr (by simpa using gz)
    have hh := decreasing_power_sum (z/g) q1 (-s) (by linarith) (by linarith)
    rw [show -s+1=r by dsimp [r]; ring] at hh
    have cap : (∑ a ∈ Icc 1 (z/g), (a:ℝ)^(-s)) ≤ ((z:ℝ)/g)^r/r := by
      apply hh.trans
      have cmp := Real.rpow_le_rpow (Nat.cast_nonneg (z/g))
        (Nat.cast_div_le : ((z/g : ℕ):ℝ) ≤ (z:ℝ)/g) rp.le
      apply (le_div_iff₀ rp).mpr
      rw [add_mul, div_mul_cancel₀ _ rp.ne']
      dsimp [r] at *
      linarith
    have nneg : 0 ≤ ∑ a ∈ Icc 1 (z/g), (a:ℝ)^(-s) := sum_nonneg (by intros; positivity)
    calc _ ≤ (g:ℝ)^(-s)*(((z:ℝ)/g)^r/r)^2 :=
               mul_le_mul_of_nonneg_left (pow_le_pow_left₀ nneg cap _) (by positivity)
         _ = _ := by
           dsimp only [C]
           rw [Real.div_rpow zr.le gpR.le,div_pow,div_pow,← Real.rpow_mul_natCast zr.le,
               ← Real.rpow_mul_natCast gpR.le]
           have eq : (g:ℝ)^(-s) = (g:ℝ)^(s-2)*(g:ℝ)^(r*(2:ℕ)) := by
             rw [← Real.rpow_add gpR]
             congr 1
             dsimp [r]
             ring
           rw [eq,show r*(2:ℕ) = 2*r by norm_num; ring]
           field_simp
  have tail : (∑ g ∈ Icc 1 z, (g:ℝ)^(s-2)) ≤ 1+1/r := by
    have h := decreasing_power_sum z hz (s-2) (by linarith) (by linarith)
    rw [show s-2+1 = -r by dsimp [r]; ring] at h
    apply h.trans
    have np := Real.rpow_nonneg zr.le (-r)
    have hterm : ((z:ℝ)^(-r)-1)/(-r) = (1-(z:ℝ)^(-r))/r := by ring
    rw [hterm]
    gcongr
    linarith
  calc
    _ ≤ _ := quotient_box z s
    _ ≤ ∑ g ∈ Icc 1 z, C*(g:ℝ)^(s-2) := sum_le_sum row
    _ = C*(∑ g ∈ Icc 1 z, (g:ℝ)^(s-2)) := (mul_sum ..).symm
    _ ≤ C*(1+1/r) := mul_le_mul_of_nonneg_left tail Cp
    _ = _ := by dsimp [C,r]; ring


/-- The endpoint s=1 has at most three harmonic factors. -/
theorem reciprocal_lcm_sum (z : ℕ) :
    (∑ d ∈ level z, ∑ e ∈ level z, ((d.lcm e : ℝ)⁻¹)) ≤ (harmonic z : ℝ)^3 := by
  have box := quotient_box z 1
  simp only [Real.rpow_neg_one] at box
  apply box.trans
  have harm (N : ℕ) : (∑ j ∈ Icc 1 N, (j:ℝ)⁻¹) = (harmonic N : ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  calc
    _ ≤ ∑ g ∈ Icc 1 z, (g:ℝ)⁻¹*(harmonic z : ℝ)^2 := by
      apply sum_le_sum; intro g _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply pow_le_pow_left₀ (sum_nonneg (by intros; positivity)) _ 2
      rw [← harm]
      exact sum_le_sum_of_subset_of_nonneg (fun a ha =>
        mem_Icc.mpr ⟨(mem_Icc.mp ha).1,(mem_Icc.mp ha).2.trans (Nat.div_le_self _ _)⟩) (by intros; positivity)
    _ = _ := by rw [← sum_mul,harm]; ring

/-- Pass from a single-modulus exponent-pair bound to the whole signed
sieve remainder. The fractional-power term has no logarithmic loss. -/
theorem remainder_bound {z x : ℕ} (u v A B s : ℝ) (hz : 1 ≤ z)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (local_bound : ∀ t : ℕ, 1 ≤ t → t ≤ z^2 →
      |remainder u v x t| ≤ A*(t:ℝ)^(-s) + B/t) :
    |weightedRemainder z u v x| ≤
    A*(((1+1/(1-s))/(1-s)^2)*(z:ℝ)^(2*(1-s))) + B*(1+log z)^3 := by
  have entry (d e : ℕ) (hd : d ∈ level z) (he : e ∈ level z) :
      |weight z d*weight z e*remainder u v x (d.lcm e)| ≤
      A*(d.lcm e : ℝ)^(-s) + B*(d.lcm e : ℝ)⁻¹ := by
    have tp := Nat.lcm_pos (mem_level.mp hd).1.1 (mem_level.mp he).1.1
    have th : d.lcm e ≤ z^2 := by
      calc _ ≤ d*e := Nat.le_of_dvd (Nat.mul_pos (mem_level.mp hd).1.1 (mem_level.mp he).1.1)
                          (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _))
           _ ≤ _ := by rw [sq]; exact Nat.mul_le_mul (mem_level.mp hd).1.2 (mem_level.mp he).1.2
    have wt : |weight z d*weight z e| ≤ 1 := by
      rw [abs_mul]
      simpa using mul_le_mul (weight_abs_le_one hz hd) (weight_abs_le_one hz he) (abs_nonneg _) zero_le_one
    rw [abs_mul]
    apply (mul_le_mul_of_nonneg_right wt (abs_nonneg _)).trans
    simpa only [one_mul,div_eq_mul_inv] using local_bound _ tp th
  have hh : (0:ℝ) ≤ harmonic z := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact sum_nonneg (by intros; positivity)
  calc
    _ ≤ ∑ d ∈ level z, |∑ e ∈ level z, weight z d*weight z e*remainder u v x (d.lcm e)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ level z, ∑ e ∈ level z, (A*(d.lcm e : ℝ)^(-s) + B*(d.lcm e : ℝ)⁻¹) := by
      apply sum_le_sum; intro d hd
      exact (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun e he => entry d e hd he))
    _ = A*(∑ d ∈ level z, ∑ e ∈ level z, (d.lcm e : ℝ)^(-s)) +
        B*(∑ d ∈ level z, ∑ e ∈ level z, (d.lcm e : ℝ)⁻¹) := by simp only [sum_add_distrib,mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (lcm_fractional_moment hz s hs0 hs1) hA)
      (mul_le_mul_of_nonneg_left ((reciprocal_lcm_sum z).trans
        (pow_le_pow_left₀ hh (harmonic_le_one_add_log z) 3)) hB)

/-- The complete block inequality conditional only on the two endpoint
sawtooth estimates for individual moduli. -/
theorem short_interval_from_local (n h z : ℕ) (u v A B s : ℝ) (hz : 1 ≤ z) (hzu : (z:ℝ)^2 ≤ u)
    (huv : u ≤ v) (hA : 0 ≤ A) (hB : 0 ≤ B) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (bounds : ∀ x ∈ ({n,n+h} : Finset ℕ), ∀ t : ℕ, 1 ≤ t → t ≤ z^2 →
      |remainder u v x t| ≤ A*(t:ℝ)^(-s) + B/t) :
    (∑ p ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime, (multiplicity n h p:ℝ)) ≤
    (h:ℝ)*log (v/u)/log ((z:ℝ)+1) + 2*h*(z:ℝ)^2/u +
      2*(A*(((1+1/(1-s))/(1-s)^2)*(z:ℝ)^(2*(1-s))) + B*(1+log z)^3) := by
  apply (short_interval_block n h z u v hz hzu huv).trans
  apply add_le_add le_rfl
  have lo := (abs_le.mp (remainder_bound u v A B s hz hA hB hs0 hs1 (bounds n (by simp)))).2
  have hi := (abs_le.mp (remainder_bound u v A B s hz hA hB hs0 hs1 (bounds (n+h) (by simp)))).1
  linarith

end FactorialSieve
end
end

-- Source module ReciprocalGrid
section

/-! Exact realization of the reciprocal phases and their centered fractional
parts on a common finite grid. Its denominator may be enlarged arbitrarily. -/
noncomputable section
open Finset
namespace FactorialFourier

/-- Residue of x/m on the Q-grid when m divides Q. -/
def residue (Q x m : ℕ) : ZMod Q := ((x*(Q/m) : ℕ) : ZMod Q)

lemma residue_val {Q m : ℕ} [NeZero Q] (hm : 0 < m) (hd : m ∣ Q) (x : ℕ) :
    (residue Q x m).val = x % m * (Q/m) := by
  have h := Nat.div_mul_cancel hd
  rw [residue,ZMod.val_natCast]
  conv_lhs => arg 2; rw [← h,mul_comm]
  exact Nat.mul_mod_mul_right (Q/m) x m

theorem residue_saw {Q m : ℕ} [NeZero Q] (hm : 0 < m) (hd : m ∣ Q) (x : ℕ) :
    ((residue Q x m).val : ℝ)/Q-1/2 = FactorialSieve.saw x m := by
  rw [residue_val hm hd,FactorialSieve.saw,Nat.cast_mul]
  have h : ((Q/m:ℕ):ℝ)*m=(Q:ℝ) := by exact_mod_cast Nat.div_mul_cancel hd
  have qp : (0:ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have mp : (0:ℝ) < m := by exact_mod_cast hm
  have t : ((x%m:ℕ):ℝ)*(Q/m:ℕ)/Q=((x%m:ℕ):ℝ)/m := by
    apply (div_eq_div_iff qp.ne' mp.ne').mpr
    rw [mul_assoc,h]
  exact sub_left_inj.mpr t

/-- The Fourier coefficients of the list of residues are genuine
exponential sums in the reciprocal phase x/m. -/
theorem residue_character {Q m : ℕ} [NeZero Q] (hm : 0 < m) (hd : m ∣ Q) (x j : ℕ) :
    ZMod.stdAddChar ((j : ZMod Q)*residue Q x m) =
      Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*x/m) := by
  rw [residue,← Nat.cast_mul,ZMod.stdAddChar_apply,ZMod.toCircle_natCast]
  push_cast
  congr 1
  have h : ((Q/m:ℕ):ℂ)*m=(Q:ℂ) := by exact_mod_cast Nat.div_mul_cancel hd
  have qp : (Q:ℂ) ≠ 0 := by exact_mod_cast NeZero.ne Q
  have mp : (m:ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  apply (div_eq_div_iff qp mp).mpr
  linear_combination (2*(Real.pi:ℂ)*Complex.I*j*x)*h

/-- A common denominator whose size can be chosen independently of the
frequency cutoff, including when the interval is empty. -/
theorem exists_grid (v : ℝ) (H : ℕ)  :
    ∃ L : ℕ, 2 ≤ L ∧ ∀ m : ℕ, 0 < m → m ≤ ⌊v⌋₊ → m ∣ H*L := by
  refine ⟨2*Nat.factorial ⌊v⌋₊,by nlinarith [Nat.factorial_pos ⌊v⌋₊],?_⟩
  intro m hm hv
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (Nat.dvd_factorial hm hv) 2) H

theorem remainder_grid {Q : ℕ} [NeZero Q] (u v : ℝ) (x t : ℕ)
    (hQ : ∀ m : ℕ, 0 < m → m ≤ ⌊v⌋₊ → m ∣ Q) :
    FactorialSieve.remainder u v x t =
      ∑ m ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·), (((residue Q x m).val : ℝ)/Q-1/2) := by
  rw [FactorialSieve.remainder,sum_filter]
  apply sum_congr rfl; intro m hm
  split_ifs
  · obtain ⟨lo,hi⟩ := mem_Ioc.mp hm
    have mp : 0 < m := by omega
    exact (residue_saw mp (hQ m mp hi) x).symm
  · rfl

end FactorialFourier
end
end

-- Source module ReciprocalFolding
section

/-! Bounds for a symmetric spectrum on a finite cyclic group. -/
noncomputable section
open Finset
namespace FactorialFourier
variable {Q : ℕ} [NeZero Q]

/-- Each positive distance from zero is represented by at most two frequencies. -/
theorem sum_folded (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) :
    (∑ k ∈ (univ : Finset (ZMod Q)).erase 0, f (min k.val (Q-k.val)))
      ≤ 2*∑ j ∈ Icc 1 Q, f j := by
  classical
  let S := (univ : Finset (ZMod Q)).erase 0
  let P (k : ZMod Q) := k.val ≤ Q-k.val
  have positive {k : ZMod Q} (hk : k ∈ S) : 0 < k.val := by
    by_contra! h
    have hz : k.val=0 := by omega
    exact (mem_erase.mp hk).1 (by simpa using congrArg (fun n : ℕ => (n:ZMod Q)) hz)
  have left : ∑ k ∈ S.filter P, f (min k.val (Q-k.val)) ≤ ∑ j ∈ Icc 1 Q, f j := by
    let A := S.filter P
    have maps : A.image ZMod.val ⊆ Icc 1 Q := by
      intro j hj; obtain ⟨k,hk,rfl⟩ := mem_image.mp hj
      exact mem_Icc.mpr ⟨positive (mem_filter.mp hk).1,k.val_lt.le⟩
    calc
      _ = ∑ k ∈ A, f k.val := sum_congr rfl (fun k hk => by rw [min_eq_left (mem_filter.mp hk).2])
      _ = ∑ j ∈ A.image ZMod.val, f j := (sum_image (f:=f) (ZMod.val_injective Q).injOn).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg maps (fun j _ _ => hf j)
  have right : ∑ k ∈ S.filter (fun k => ¬ P k), f (min k.val (Q-k.val)) ≤ ∑ j ∈ Icc 1 Q, f j := by
    let A := S.filter (fun k => ¬ P k)
    let g (k : ZMod Q) := Q-k.val
    have maps : A.image g ⊆ Icc 1 Q := by
      intro j hj; obtain ⟨k,_,rfl⟩ := mem_image.mp hj
      have hh := k.val_lt; dsimp [g]; exact mem_Icc.mpr ⟨by omega,by omega⟩
    have inj : Set.InjOn g A := by
      intro a _ b _ eq
      have ha := a.val_lt; have hb := b.val_lt
      apply ZMod.val_injective Q; dsimp [g] at eq; omega
    calc
      _ = ∑ k ∈ A, f (g k) := sum_congr rfl (fun k hk => by
        exact congrArg f (min_eq_right (le_of_not_ge ((mem_filter.mp hk).2 : ¬ P k))))
      _ = ∑ j ∈ A.image g, f j := (sum_image (f:=f) inj).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg maps (fun j _ _ => hf j)
  change (∑ k ∈ S, _) ≤ _
  rw [← sum_filter_add_sum_filter_not S P,two_mul]
  exact add_le_add left right

/-- Reflection in the cyclic group conjugates the exponential sum. -/
theorem norm_spectrum_neg {ι : Type*} (s : Finset ι) (p : ι → ZMod Q) (k : ZMod Q) :
    ‖∑ i ∈ s, ZMod.stdAddChar ((-k)*p i)‖ = ‖∑ i ∈ s, ZMod.stdAddChar (k*p i)‖ := by
  have h (a : ZMod Q) : ZMod.stdAddChar (-a) = star (ZMod.stdAddChar a) := by
    rw [ZMod.stdAddChar_apply,AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj]
    rfl
  simp only [neg_mul,h,← star_sum]
  exact norm_star _

/-- A bound for positive integer frequencies automatically applies to their
folded representatives, including the order-two character when Q is even. -/
theorem spectrum_folded {ι : Type*} (s : Finset ι) (p : ι → ZMod Q) (f : ℕ → ℝ)
    (B : ∀ j : ℕ, 0 < j → ‖∑ i ∈ s, ZMod.stdAddChar ((j:ZMod Q)*p i)‖ ≤ f j)
    {k : ZMod Q} (hk : k≠0) :
    ‖∑ i ∈ s, ZMod.stdAddChar (k*p i)‖ ≤ f (min k.val (Q-k.val)) := by
  by_cases h : k.val ≤ Q-k.val
  · rw [min_eq_left h]
    have pos : 0 < k.val := by
      by_contra! hh
      apply hk
      have hz : k.val=0 := by omega
      simpa using congrArg (fun n : ℕ => (n:ZMod Q)) hz
    simpa using B k.val pos
  · rw [min_eq_right (le_of_not_ge h)]
    have pos : 0 < Q-k.val := Nat.sub_pos_of_lt k.val_lt
    have c : ((Q-k.val:ℕ):ZMod Q) = -k := by
      rw [Nat.cast_sub k.val_lt.le]; simp
    have b := B _ pos
    rwa [c,norm_spectrum_neg] at b

end FactorialFourier
end
end

-- Source module ReciprocalFrequency
section

/-! Finite frequency estimates for a one-sided moving average of the centered
fractional part. A cutoff H balances smoothing error against exponential sums.
Only finite sums occur, so the bounds do not depend on the common denominator. -/

noncomputable section
open Finset Real
namespace FactorialFourier

private lemma integral_power_tail (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b)
    (e : ℝ) (he : e ≤ 0) (hne : e ≠ -1) :
    ∑ j ∈ Ioc a b, (j:ℝ)^e ≤ ((b:ℝ)^(e+1) - (a:ℝ)^(e+1))/(e+1) := by
  have ar : (0:ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have br : (a:ℝ) ≤ b := by exact_mod_cast hab
  have ant : AntitoneOn (fun x : ℝ => x^e) (Set.Icc (a:ℝ) b) :=
    fun _ hx _ _ hxy => Real.rpow_le_rpow_of_nonpos (ar.trans_le hx.1) hxy he
  have bound := AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ => x^e) hab ant
  have miss : (0:ℝ) ∉ Set.uIcc (a:ℝ) b := by
    rw [Set.uIcc_of_le br]; intro h; exact ar.not_ge h.1
  rw [integral_rpow (Or.inr ⟨hne,miss⟩)] at bound
  refine le_of_eq_of_le ?_ bound
  symm
  apply sum_bij (fun i _ => i+1)
  · intro i hi; obtain ⟨l,u⟩ := mem_Ico.mp hi; exact mem_Ioc.mpr ⟨by omega, by omega⟩
  · intros; omega
  · intro j hj; obtain ⟨l,u⟩ := mem_Ioc.mp hj
    exact ⟨j-1,mem_Ico.mpr ⟨by omega,by omega⟩,by omega⟩
  · intros; rfl

private lemma power_initial (H : ℕ) (hH : 1 ≤ H) (k : ℝ) (hk : 0 < k) (hk1 : k ≤ 1) :
    ∑ j ∈ Icc 1 H, (j:ℝ)^(k-1) ≤ (H:ℝ)^k/k := by
  have p := integral_power_tail 1 H (by decide) hH (k-1) (by linarith) (by linarith)
  rw [show k-1+1=k by ring] at p
  simp only [Nat.cast_one,Real.one_rpow] at p
  have ss : Icc 1 H = insert 1 (Ioc 1 H) := by ext i; simp; omega
  rw [ss,sum_insert (by simp),Nat.cast_one,Real.one_rpow]
  apply (add_le_add le_rfl p).trans
  apply (le_div_iff₀ hk).mpr
  rw [add_mul,div_mul_cancel₀ _ hk.ne']
  linarith

private lemma power_tail (H K : ℕ) (hH : 1 ≤ H) (hK : H ≤ K) (k : ℝ) (hk : k < 1) :
    ∑ j ∈ Ioc H K, (j:ℝ)^(k-2) ≤ (H:ℝ)^(k-1)/(1-k) := by
  have a := integral_power_tail H K hH hK (k-2) (by linarith) (by linarith)
  rw [show k-2+1=k-1 by ring] at a
  apply a.trans
  have p : 0 < 1-k := by linarith
  have nonneg := Real.rpow_nonneg (Nat.cast_nonneg K) (k-1)
  rw [show k-1= -(1-k) by ring] at nonneg
  rw [show k-1= -(1-k) by ring, div_neg]
  apply (le_div_iff₀ p).mpr
  rw [neg_mul,div_mul_cancel₀ _ p.ne']
  linarith

/-- The weight allotted to a positive frequency j after smoothing at scale 1/H. -/
def frequencyWeight (H j : ℕ) : ℝ := min 1 ((H:ℝ)/j)/(j:ℝ)

/-- Summing a j^k exponential-sum bound costs O_k(H^k) for 0<k<1. -/
theorem frequency_power (H K : ℕ) (hH : 1 ≤ H) (hK : H ≤ K)
    (k : ℝ) (hk : 0 < k) (hk1 : k < 1) :
    ∑ j ∈ Icc 1 K, frequencyWeight H j * (j:ℝ)^k ≤
      (1/k+1/(1-k))*(H:ℝ)^k := by
  have hR : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have lo (j : ℕ) (hj : j ∈ Icc 1 H) :
      frequencyWeight H j * (j:ℝ)^k = (j:ℝ)^(k-1) := by
    obtain ⟨jp,jh⟩ := mem_Icc.mp hj
    have p : (0:ℝ) < j := by exact_mod_cast jp
    rw [frequencyWeight,min_eq_left ((one_le_div p).mpr (by exact_mod_cast jh)),Real.rpow_sub_one p.ne']
    ring
  have hi (j : ℕ) (hj : j ∈ Ioc H K) :
      frequencyWeight H j * (j:ℝ)^k = (H:ℝ)*(j:ℝ)^(k-2) := by
    obtain ⟨jh,_⟩ := mem_Ioc.mp hj
    have p : (0:ℝ) < j := hR.trans (by exact_mod_cast jh)
    rw [frequencyWeight,min_eq_right ((div_le_one p).mpr (by exact_mod_cast jh.le)),
       show k-2=(k-1)-1 by ring,Real.rpow_sub_one p.ne',Real.rpow_sub_one p.ne']
    ring
  have sets : Icc 1 K = Icc 1 H ∪ Ioc H K := by ext j; simp; omega
  have dis : Disjoint (Icc 1 H) (Ioc H K) := by rw [disjoint_left]; intro j hj hh
                                                exact (mem_Ioc.mp hh).1.not_ge (mem_Icc.mp hj).2
  rw [sets,sum_union dis,sum_congr rfl lo,sum_congr rfl hi,← mul_sum]
  apply (add_le_add (power_initial H hH k hk hk1.le)
    (mul_le_mul_of_nonneg_left (power_tail H K hH hK k hk1) hR.le)).trans
  rw [Real.rpow_sub_one hR.ne']
  field_simp; ring_nf; exact le_rfl

/-- A j^{-1} error in the exponential sum costs at most twice its coefficient. -/
theorem frequency_reciprocal (H K : ℕ) :
    ∑ j ∈ Icc 1 K, frequencyWeight H j / j ≤ 2 := by
  by_cases hK : 1 ≤ K
  · have p := power_tail 1 K (by decide) hK 0 (by norm_num)
    norm_num at p
    have ss : Icc 1 K = insert 1 (Ioc 1 K) := by ext i; simp; omega
    calc
      _ ≤ ∑ j ∈ Icc 1 K, (j:ℝ)^(-(2:ℝ)) := by
        apply sum_le_sum; intro j hj
        have jp : (0:ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
        rw [frequencyWeight,Real.rpow_neg jp.le,Real.rpow_two]
        calc _ ≤ (1/(j:ℝ))/j := by gcongr; exact min_le_left _ _
             _ = _ := by field_simp
      _ = 1 + ∑ j ∈ Ioc 1 K, (j:ℝ)^(-(2:ℝ)) := by rw [ss,sum_insert (by simp)]; simp
      _ ≤ 2 := by
        norm_num [Real.rpow_neg,Real.rpow_two] <;> linarith
  · simp [show K=0 by omega]

/-- A smoothed finite Fourier sum can be estimated uniformly in its upper
frequency K using only exponential-sum bounds of the form E*j^k + F/j. -/
theorem frequency_budget (H K : ℕ) (hH : 1 ≤ H) (hK : H ≤ K) (E F k : ℝ)
    (hE : 0 ≤ E) (hF : 0 ≤ F) (hk : 0 < k) (hk1 : k < 1) :
    ∑ j ∈ Icc 1 K, frequencyWeight H j * (E*(j:ℝ)^k + F/j) ≤
      E*((1/k+1/(1-k))*(H:ℝ)^k) + 2*F := by
  calc
    _ = E*(∑ j ∈ Icc 1 K, frequencyWeight H j*(j:ℝ)^k) +
          F*(∑ j ∈ Icc 1 K, frequencyWeight H j / j) := by
      rw [mul_sum,mul_sum,← sum_add_distrib]
      apply sum_congr rfl; intros; ring
    _ ≤ _ := by
      rw [mul_comm 2 F]
      exact add_le_add (mul_le_mul_of_nonneg_left (frequency_power H K hH hK k hk hk1) hE)
        (mul_le_mul_of_nonneg_left (frequency_reciprocal H K) hF)

end FactorialFourier
end
end

-- Source module ReciprocalSmoothing
section

/-! One-sided moving averages of a sawtooth on a finite cyclic grid.
The pointwise inequalities include discontinuities. Finite Fourier inversion
then factors the transform into the exponential sum over the input phases
and a geometric sum over the shifts. -/

noncomputable section
open Finset
namespace ReciprocalSmoothing

variable {Q : ℕ} [NeZero Q]

/-- Centered fractional part of a point on the grid of denominator Q. -/
def saw (a : ZMod Q) : ℝ := (a.val : ℝ) / Q - 1/2

omit [NeZero Q] in
private lemma saw_add_upper (a : ZMod Q) (j : ℕ) :
    saw (a + (j : ZMod Q)) ≤ saw a + (j:ℝ)/Q := by
  have nle : (a + (j : ZMod Q)).val ≤ a.val + j := by
    apply (ZMod.val_add_le _ _).trans
    rw [ZMod.val_natCast]
    exact Nat.add_le_add_left (Nat.mod_le ..) _
  have rle : ((a + (j : ZMod Q)).val : ℝ) ≤ (a.val:ℝ) + j := by exact_mod_cast nle
  have h := div_le_div_of_nonneg_right rle (Nat.cast_nonneg Q)
  unfold saw
  rw [add_div] at h
  linarith

omit [NeZero Q] in
private lemma saw_sub_lower (a : ZMod Q) (j : ℕ) :
    saw a ≤ saw (a - (j : ZMod Q)) + (j:ℝ)/Q := by
  simpa only [sub_add_cancel] using saw_add_upper (a - (j : ZMod Q)) j

private lemma sum_shift {L : ℕ} (hL : 0 < L) :
    (∑ j ∈ range L, (j:ℝ)/(Q:ℝ)) = (L:ℝ)*((L:ℝ)-1)/(2*Q) := by
  have hq : (Q:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne Q
  have eqn := Finset.sum_range_id_mul_two L
  have eqr : (∑ j ∈ range L, (j:ℝ)) * 2 = (L:ℝ)*((L:ℝ)-1) := by
    have e := congrArg (fun a : ℕ => (a:ℝ)) eqn
    push_cast [Nat.cast_sub (by omega : 1 ≤ L)] at e
    exact e
  rw [← sum_div]
  field_simp
  linear_combination eqr

/-- Upper and lower one-sided moving averages, with their exact mean shift. -/
theorem squeeze (a : ZMod Q) {L : ℕ} (hL : 0 < L) :
    ((∑ j ∈ range L, saw (a + (j : ZMod Q)))/(L:ℝ) - ((L:ℝ)-1)/(2*Q) ≤ saw a) ∧
    (saw a ≤ (∑ j ∈ range L, saw (a - (j : ZMod Q)))/(L:ℝ) + ((L:ℝ)-1)/(2*Q)) := by
  have lp : (0:ℝ) < L := by exact_mod_cast hL
  have h₁ := Finset.sum_le_sum (s := range L) (fun j _ => saw_add_upper a j)
  have h₂ := Finset.sum_le_sum (s := range L) (fun j _ => saw_sub_lower a j)
  simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, sum_shift (Q:=Q) hL] at h₁ h₂
  constructor
  · apply sub_le_iff_le_add.mpr
    apply (div_le_iff₀ lp).mpr
    linarith only [h₁, show ((L:ℝ)-1)/(2*Q)*L = L*((L:ℝ)-1)/(2*Q) by ring,
      show (saw a + ((L:ℝ)-1)/(2*Q))*L = (L:ℝ)*saw a + ((L:ℝ)-1)/(2*Q)*L by ring]
  · apply sub_le_iff_le_add.mp
    apply (le_div_iff₀ lp).mpr
    linarith only [h₂, show (saw a - ((L:ℝ)-1)/(2*Q))*L = (L:ℝ)*saw a - L*((L:ℝ)-1)/(2*Q) by ring]

/-- Fourier expansion of a translated sum over two independent lists. -/
theorem fourier_factor {ι κ : Type*} (s : Finset ι) (b : Finset κ) (p : ι → ZMod Q)
    (t : κ → ZMod Q) (f : ZMod Q → ℂ) :
    (∑ i ∈ s, ∑ j ∈ b, f (p i + t j)) =
    (Q:ℂ)⁻¹ * ∑ k : ZMod Q, ZMod.dft f k *
      (∑ i ∈ s, ZMod.stdAddChar (k*p i)) * (∑ j ∈ b, ZMod.stdAddChar (k*t j)) := by
  have invert (a : ZMod Q) : f a =
      (Q:ℂ)⁻¹ * ∑ k : ZMod Q, ZMod.stdAddChar (k*a) * ZMod.dft f k := by
    simpa only [smul_eq_mul, LinearEquiv.symm_apply_apply] using
      (ZMod.invDFT_apply (ZMod.dft f) a)
  calc
    _ = ∑ i ∈ s, ∑ j ∈ b, ((Q:ℂ)⁻¹ *
          ∑ k : ZMod Q, ZMod.dft f k * ZMod.stdAddChar (k*p i) * ZMod.stdAddChar (k*t j)) := by
        apply sum_congr rfl; intro i _
        apply sum_congr rfl; intro j _
        rw [invert, mul_right_inj' (inv_ne_zero (by exact_mod_cast (NeZero.ne Q)))]
        apply sum_congr rfl; intro k _
        rw [mul_add,AddChar.map_add_eq_mul]
        ring
    _ = (Q:ℂ)⁻¹ * ∑ i ∈ s, ∑ k : ZMod Q, ∑ j ∈ b,
          ZMod.dft f k * ZMod.stdAddChar (k*p i) * ZMod.stdAddChar (k*t j) := by
      simp only [mul_sum]
      apply sum_congr rfl; intro i _
      rw [sum_comm]
    _ = _ := by
      congr 1
      rw [sum_comm]
      apply sum_congr rfl; intro k _
      symm
      calc
        _ = (∑ i ∈ s, ZMod.dft f k * ZMod.stdAddChar (k*p i)) *
            (∑ j ∈ b, ZMod.stdAddChar (k*t j)) := by rw [← mul_sum]
        _ = ∑ i ∈ s, (ZMod.dft f k * ZMod.stdAddChar (k*p i)) *
            (∑ j ∈ b, ZMod.stdAddChar (k*t j)) := by rw [sum_mul]
        _ = _ := by simp only [mul_sum]

/-- Smoothing with the reflected shifts has the same spectral magnitudes. -/
private lemma reflected_box (k : ZMod Q) (L : ℕ) :
    ‖∑ j ∈ range L, ZMod.stdAddChar (k * -(j : ZMod Q))‖ =
    ‖∑ j ∈ range L, ZMod.stdAddChar (k * (j : ZMod Q))‖ := by
  have h (j : ℕ) : ZMod.stdAddChar (k * -(j : ZMod Q)) =
      (starRingEnd ℂ) (ZMod.stdAddChar (k * (j : ZMod Q))) := by
    rw [mul_neg,ZMod.stdAddChar_apply,AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj]
    rfl
  simp only [h, ← map_sum, Complex.norm_conj]

/-- The error from smoothing a sample of residues is bounded by a Fourier
sum. The mean shift accounts for possible jumps at the grid origin. -/
theorem discrepancy_bound {ι : Type*} (s : Finset ι) (p : ι → ZMod Q)
    {L : ℕ} (hL : 0 < L) :
    |∑ i ∈ s, saw (p i)| ≤
      (s.card:ℝ)*((L:ℝ)-1)/(2*Q) +
      (∑ k : ZMod Q, ‖ZMod.dft (fun a => (saw a : ℂ)) k‖ *
        ‖∑ i ∈ s, ZMod.stdAddChar (k*p i)‖ *
        ‖∑ j ∈ range L, ZMod.stdAddChar (k*(j : ZMod Q))‖)/((Q:ℝ)*L) := by
  let f : ZMod Q → ℂ := fun a => (saw a : ℂ)
  let spec := ∑ k : ZMod Q, ‖ZMod.dft f k‖ *
    ‖∑ i ∈ s, ZMod.stdAddChar (k*p i)‖ *
    ‖∑ j ∈ range L, ZMod.stdAddChar (k*(j : ZMod Q))‖
  have qp : (0:ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have lp : (0:ℝ) < L := by exact_mod_cast hL
  have shift_bound (t : ℕ → ZMod Q)
      (ht : ∀ k : ZMod Q, ‖∑ j ∈ range L, ZMod.stdAddChar (k*t j)‖ =
        ‖∑ j ∈ range L, ZMod.stdAddChar (k*(j : ZMod Q))‖) :
      |∑ i ∈ s, ∑ j ∈ range L, saw (p i+t j)|/(L:ℝ) ≤ spec/((Q:ℝ)*L) := by
    have hf := fourier_factor s (range L) p t f
    have bound := norm_sum_le (univ : Finset (ZMod Q)) (fun k =>
      ZMod.dft f k * (∑ i ∈ s, ZMod.stdAddChar (k*p i)) *
        (∑ j ∈ range L, ZMod.stdAddChar (k*t j)))
    simp only [norm_mul, ht] at bound
    have normleft : ‖∑ i ∈ s, ∑ j ∈ range L, f (p i + t j)‖ =
        |∑ i ∈ s, ∑ j ∈ range L, saw (p i + t j)| := by
      simp only [f, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    have absbound : |∑ i ∈ s, ∑ j ∈ range L, saw (p i+t j)| ≤ (Q:ℝ)⁻¹*spec := by
      rw [← normleft,hf,norm_mul,norm_inv,Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left bound (by positivity)
    apply (div_le_div_of_nonneg_right absbound lp.le).trans_eq
    field_simp
  have upper := shift_bound (fun j => -(j:ZMod Q)) (fun k => reflected_box k L)
  have lower := shift_bound (fun j => (j:ZMod Q)) (fun _ => rfl)
  simp only [← sub_eq_add_neg] at upper
  have h₁ := Finset.sum_le_sum (s := s) (fun i _ => (squeeze (p i) hL).1)
  have h₂ := Finset.sum_le_sum (s := s) (fun i _ => (squeeze (p i) hL).2)
  simp only [sum_sub_distrib,sum_add_distrib,← sum_div,sum_const,nsmul_eq_mul] at h₁ h₂
  have up := (div_le_div_of_nonneg_right (le_abs_self _) lp.le).trans upper
  have lo := (div_le_div_of_nonneg_right (neg_le_abs _) lp.le).trans lower
  change _ ≤ _ + spec/((Q:ℝ)*L)
  rw [abs_le]
  rw [neg_div] at lo
  rw [← mul_sub] at h₁ h₂
  constructor <;> linarith only [h₁,h₂,up,lo]

/-- Normalized form. The box multiplier is the mean of successive powers
of a root of unity, so coefficient bounds apply to each frequency. -/
theorem normalized_discrepancy {ι : Type*} (s : Finset ι) (p : ι → ZMod Q)
    {L : ℕ} (hL : 0 < L) :
    |∑ i ∈ s, saw (p i)| ≤ (s.card:ℝ)*((L:ℝ)-1)/(2*Q) +
      ∑ k : ZMod Q, (‖ZMod.dft (fun a => (saw a : ℂ)) k‖/(Q:ℝ)) *
        ‖∑ i ∈ s, ZMod.stdAddChar (k*p i)‖ *
        ‖(∑ j ∈ range L, (ZMod.stdAddChar k)^j)/(L:ℂ)‖ := by
  apply (discrepancy_bound s p hL).trans_eq
  congr 1
  rw [sum_div]
  apply sum_congr rfl; intro k _
  have h (j : ℕ) : ZMod.stdAddChar (k*(j:ZMod Q)) = (ZMod.stdAddChar k)^j := by
    rw [mul_comm,← nsmul_eq_mul,AddChar.map_nsmul_eq_pow]
  simp only [h,norm_div,Complex.norm_natCast]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end ReciprocalSmoothing

end
end

-- Source module ReciprocalFourier
section

/-! Finite Fourier coefficients of the centered sawtooth and a one-sided box on a cyclic grid. -/
noncomputable section
open Finset
namespace FactorialFourier

def sawCoeff (Q : ℕ) (w : ℂ) : ℂ :=
  ∑ m ∈ range Q, ((m : ℂ)/Q - 1/2) * w^m

def boxCoeff (L : ℕ) (w : ℂ) : ℂ :=
  (∑ m ∈ range L, w^m)/(L:ℂ)

private theorem weighted_geom (Q : ℕ) (w : ℂ) :
    (w-1)*(∑ m ∈ range Q, (m:ℂ)*w^m) =
      (Q:ℂ)*w^Q - w*(∑ m ∈ range Q, w^m) := by
  induction Q with
  | zero => simp
  | succ Q ih => rw [sum_range_succ,sum_range_succ,Nat.cast_succ,pow_succ,mul_add,ih]; ring

/-- Every nonconstant Fourier coefficient of the raw grid sawtooth. -/
theorem sawCoeff_eq {Q : ℕ} (hQ : 0<Q) {w : ℂ} (hw : w^Q=1) (hne : w≠1) :
    sawCoeff Q w = 1/(w-1) := by
  have g : ∑ m ∈ range Q, w^m = 0 := by
    have h := geom_sum_mul w Q
    rw [hw, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)
  have q : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  have s := weighted_geom Q w
  rw [hw,g] at s
  have eq : sawCoeff Q w =
      (∑ m ∈ range Q, (m:ℂ)*w^m)/Q - (1/2)*(∑ m ∈ range Q, w^m) := by
    rw [sawCoeff, sum_div, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl; intro m _; ring
  rw [eq,g,mul_zero,sub_zero]
  field_simp
  linear_combination s

/-- Taking absolute values termwise and using the geometric series give complementary bounds. -/
theorem boxCoeff_bound {L : ℕ} (hL : 0<L) {w : ℂ} (hn : ‖w‖=1) (hne : w≠1) :
    ‖boxCoeff L w‖ ≤ min 1 (2/((L:ℝ)*‖w-1‖)) := by
  have l : (0:ℝ)<L := by exact_mod_cast hL
  have d := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  rw [boxCoeff,norm_div,Complex.norm_natCast]
  apply le_min
  · apply (div_le_iff₀ l).mpr
    calc
      _ ≤ ∑ m ∈ range L, ‖w^m‖ := norm_sum_le _ _
      _ = _ := by simp [norm_pow,hn]
  · apply (le_div_iff₀ (mul_pos l d)).mpr
    rw [← mul_assoc,div_mul_cancel₀ _ l.ne',← norm_mul,geom_sum_mul]
    simpa [norm_pow,hn,one_add_one_eq_two] using norm_sub_le (w^L) 1

/-- The chord at phase x≥0 is bounded below in terms of its distance from either end of [0,1]. -/
theorem chord_lower (x : ℝ) (hx : 0≤x) (hx' : x≤1) :
    4*min x (1-x) ≤ ‖Complex.exp (Complex.I*(2*Real.pi*x : ℝ))-1‖ := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one,show 2*Real.pi*x/2 = Real.pi*x by ring]
  have hπ := Real.pi_pos
  have h := Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg hπ.le hx)
    (by simpa using mul_le_mul_of_nonneg_left hx' hπ.le)
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg zero_le_two h)]
  rcases le_total x (1-x) with hhalf|hhalf
  · rw [min_eq_left hhalf]
    have hh := Real.le_sin_mul (x:=2*x) (by linarith) (by linarith)
    rw [show Real.pi/2*(2*x)=Real.pi*x by ring] at hh
    linarith
  · rw [min_eq_right hhalf]
    have hh := Real.le_sin_mul (x:=2*(1-x)) (by linarith) (by linarith)
    rw [show Real.pi/2*(2*(1-x))=Real.pi-Real.pi*x by ring,Real.sin_pi_sub] at hh
    linarith

variable {Q : ℕ} [NeZero Q]

/-- A centered sawtooth on residues represented by integers in [0,Q). -/
def gridSaw (a : ZMod Q) : ℂ := (a.val:ℂ)/(Q:ℂ)-1/2

theorem sum_grid {M : Type*} [AddCommMonoid M] (f : ZMod Q → M) :
    ∑ k, f k = ∑ m ∈ range Q, f (m : ZMod Q) := by
  apply sum_bij (fun k _ => k.val)
  · intro k _; exact mem_range.mpr k.val_lt
  · intro a _ b _ h; simpa using congrArg (fun m : ℕ => (m : ZMod Q)) h
  · intro m hm
    exact ⟨(m:ZMod Q),mem_univ _,ZMod.val_natCast_of_lt (mem_range.mp hm)⟩
  · intro k _; rw [ZMod.natCast_zmod_val]

theorem std_pow (a : ZMod Q) (m : ℕ) :
    ZMod.stdAddChar a ^ m = ZMod.stdAddChar ((m:ZMod Q)*a) := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]

theorem std_ne_one {a : ZMod Q} (ha : a≠0) : ZMod.stdAddChar a ≠ 1 := by
  intro h
  apply ha
  apply ZMod.injective_stdAddChar
  simpa using h

theorem std_norm (a : ZMod Q) : ‖ZMod.stdAddChar a‖=1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

theorem dft_gridSaw_as_sum (k : ZMod Q) :
    ZMod.dft (gridSaw (Q:=Q)) k = sawCoeff Q (ZMod.stdAddChar (-k)) := by
  rw [ZMod.dft_apply, sum_grid,sawCoeff]
  apply sum_congr rfl; intro m hm
  rw [smul_eq_mul,gridSaw,ZMod.val_natCast_of_lt (mem_range.mp hm),std_pow,mul_neg,mul_comm]

/-- The exact, unnormalized discrete Fourier transform at nonzero frequency. -/
theorem dft_gridSaw_eq {k : ZMod Q} (hk : k≠0) :
    ZMod.dft (gridSaw (Q:=Q)) k = 1/(ZMod.stdAddChar (-k)-1) := by
  rw [dft_gridSaw_as_sum]
  apply sawCoeff_eq (Nat.pos_of_ne_zero (NeZero.ne _)) _ (std_ne_one (neg_ne_zero.mpr hk))
  simp [std_pow]

theorem dft_gridSaw_zero : ZMod.dft (gridSaw (Q:=Q)) 0 = -(1/2) := by
  have h : (0:ℕ)<Q := Nat.pos_of_ne_zero (NeZero.ne _)
  have hz : (Q:ℂ)≠0 := by exact_mod_cast h.ne'
  have hsum : (∑ m ∈ range Q, (m:ℂ))*2=(Q:ℂ)*(Q-1) := by
    have v := sum_range_id_mul_two Q
    have hv := congrArg (Nat.cast : ℕ → ℂ) v
    simpa [Nat.cast_sub (show 1≤Q by omega)] using hv
  rw [dft_gridSaw_as_sum]
  simp only [sawCoeff,neg_zero,AddChar.map_zero_eq_one,one_pow,mul_one,sum_sub_distrib,← sum_div,
    sum_const,card_range,nsmul_eq_mul]
  field_simp
  linear_combination hsum

/-- Distance of a frequency to the nearest multiple of Q. -/
def folded (k : ZMod Q) : ℕ := min k.val (Q-k.val)

theorem folded_pos {k : ZMod Q} (hk : k≠0) : 0 < folded k := by
  exact lt_min (Nat.pos_of_ne_zero ((ZMod.val_ne_zero k).mpr hk)) (Nat.sub_pos_of_lt k.val_lt)

theorem folded_neg {k : ZMod Q} (hk : k≠0) : folded (-k)=folded k := by
  let : NeZero k := ⟨hk⟩
  simp [folded,ZMod.val_neg_of_ne_zero,Nat.sub_sub_self k.val_lt.le,min_comm]

theorem std_chord (k : ZMod Q) :
    4*(folded k:ℝ)/Q ≤ ‖ZMod.stdAddChar k-1‖ := by
  have qp : (0:ℝ)<Q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne Q))
  have vk : (k.val:ℝ)≤Q := by exact_mod_cast k.val_lt.le
  have x := chord_lower (k.val/Q) (by positivity) ((div_le_one qp).mpr vk)
  have hh : ZMod.stdAddChar k =
    Complex.exp (Complex.I*(2*Real.pi*((k.val:ℝ)/Q):ℝ)) := by
    have eq := ZMod.stdAddChar_coe (N:=Q) (k.val:ℤ)
    simp only [Int.cast_natCast,ZMod.natCast_zmod_val] at eq
    rw [eq]
    congr 1
    push_cast
    ring
  rw [hh,folded,Nat.cast_min,Nat.cast_sub k.val_lt.le]
  rw [show (1:ℝ)-k.val/Q=(Q-k.val)/Q by field_simp]
    at x
  rw [min_div_div_right qp.le] at x
  simpa only [mul_div_assoc] using x

/-- The normalized sawtooth coefficient is bounded by 1/(4 times the folded frequency). -/
theorem normalized_dft_bound {k : ZMod Q} (hk : k≠0) :
    ‖ZMod.dft (gridSaw (Q:=Q)) k‖ / Q ≤ 1/(4*(folded k:ℝ)) := by
  have p : (0:ℝ)<Q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne Q))
  have m : (0:ℝ)<folded k := by exact_mod_cast folded_pos hk
  have d := norm_pos_iff.mpr (sub_ne_zero.mpr (std_ne_one (neg_ne_zero.mpr hk)))
  have chord := std_chord (-k)
  rw [folded_neg hk] at chord
  have h := (div_le_iff₀ p).mp chord
  rw [dft_gridSaw_eq hk,norm_div,norm_one,div_div]
  exact one_div_le_one_div_of_le (by positivity) h

/-- The finite box multiplier decays inversely beyond frequency Q/L. -/
theorem box_frequency_bound {L : ℕ} (hL : 0<L) {k : ZMod Q} (hk : k≠0) :
    ‖boxCoeff L (ZMod.stdAddChar k)‖ ≤ min 1 ((Q:ℝ)/(2*L*(folded k:ℝ))) := by
  have p : (0:ℝ)<Q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne Q))
  have l : (0:ℝ)<L := by exact_mod_cast hL
  have m : (0:ℝ)<folded k := by exact_mod_cast folded_pos hk
  have d := norm_pos_iff.mpr (sub_ne_zero.mpr (std_ne_one hk))
  apply (boxCoeff_bound hL (std_norm k) (std_ne_one hk)).trans
  apply min_le_min_left
  apply (div_le_div_iff₀ (mul_pos l d) (by positivity)).mpr
  have h := (div_le_iff₀ p).mp (std_chord k)
  calc
     2*(2*(L:ℝ)*folded k) = (4*(folded k:ℝ))*L := by ring
     _ ≤ (‖ZMod.stdAddChar k - 1‖*Q)*L := mul_le_mul_of_nonneg_right h l.le
     _ = _ := by ring

end FactorialFourier
end
end

-- Source module ReciprocalTransfer
section

/-! A finite Fourier transfer from ordinary exponential sums to the centered
fractional parts in a Selberg sieve block. No oscillation bound is assumed
at frequency zero and the estimate has no logarithm of the denominator. -/

noncomputable section
open Finset
namespace FactorialFourier

/-- Finite Fourier transfer on a common grid with Q=H L. -/
theorem grid_transfer {ι : Type*} {Q H L : ℕ} [NeZero Q]
    (s : Finset ι) (p : ι → ZMod Q) (hH : 1 ≤ H) (hL : 1 ≤ L) (hQ : Q=H*L)
    (E F k : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F) (hk : 0 < k) (hk1 : k < 1)
    (B : ∀ j : ℕ, 0 < j →
       ‖∑ i ∈ s, ZMod.stdAddChar ((j:ZMod Q)*p i)‖ ≤ E*(j:ℝ)^k+F/j) :
    |∑ i ∈ s, ReciprocalSmoothing.saw (p i)| ≤
      s.card/(2*(H:ℝ)) + (E*((1/k+1/(1-k))*(H:ℝ)^k)+2*F)/2 := by
  classical
  have hqr : (Q:ℝ)=(H:ℝ)*L := by exact_mod_cast hQ
  have qp : (0:ℝ)<Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hp : (0:ℝ)<H := by exact_mod_cast hH
  have lp : (0:ℝ)<L := by exact_mod_cast hL
  have f_eq : (fun a : ZMod Q => (ReciprocalSmoothing.saw a : ℂ)) = gridSaw := by
    funext a
    simp only [ReciprocalSmoothing.saw,gridSaw,Complex.ofReal_sub,Complex.ofReal_div,
      Complex.ofReal_natCast,Complex.ofReal_one,Complex.ofReal_ofNat]
  let spec (a : ZMod Q) := ‖∑ i ∈ s, ZMod.stdAddChar (a*p i)‖
  let raw (a : ZMod Q) := ‖ZMod.dft (gridSaw (Q:=Q)) a‖ / Q * spec a *
                            ‖boxCoeff L (ZMod.stdAddChar a)‖
  let M (j : ℕ) := E*(j:ℝ)^k+F/j
  let f (j : ℕ) := frequencyWeight H j * M j
  have Mpos (j : ℕ) : 0 ≤ M j := by dsimp [M]; positivity
  have fpos (j : ℕ) : 0 ≤ f j := by dsimp [f,frequencyWeight]; positivity
  have bound (a : ZMod Q) (ha : a ≠ 0) : raw a ≤ f (folded a)/4 := by
    have m : (0:ℝ)<folded a := by exact_mod_cast folded_pos ha
    have bb := box_frequency_bound (L:=L) hL ha
    have cmp : (Q:ℝ)/(2*L*(folded a:ℝ)) ≤ (H:ℝ)/(folded a) := by
      rw [hqr]; apply (div_le_div_iff₀ (by positivity) m).mpr
      nlinarith [mul_pos (mul_pos hp lp) m]
    have b := bb.trans (min_le_min_left 1 cmp)
    have aBound : spec a ≤ M (folded a) := spectrum_folded s p M B ha
    calc
      raw a ≤ 1/(4*(folded a:ℝ))*M (folded a)*min 1 ((H:ℝ)/folded a) :=
        mul_le_mul (mul_le_mul (normalized_dft_bound ha) aBound (norm_nonneg _) (by positivity))
          b (norm_nonneg _) (mul_nonneg (by positivity) (Mpos _))
      _ = _ := by dsimp [f,frequencyWeight]; ring
  have spec0 : spec 0 = s.card := by simp [spec]
  have zeroRaw : raw 0 = s.card/(2*(Q:ℝ)) := by
    have boxOne : boxCoeff L (ZMod.stdAddChar (0:ZMod Q)) = 1 := by
      simp [boxCoeff,(show (L:ℂ) ≠ 0 by exact_mod_cast (show L≠0 by omega))]
    dsimp only [raw]
    rw [boxOne,dft_gridSaw_zero,spec0]
    norm_num <;> ring
  have hCut : H ≤ Q := hQ ▸ Nat.le_mul_of_pos_right H hL
  have foldedBudget := sum_folded (Q:=Q) f fpos
  have total : (∑ a : ZMod Q, raw a) ≤
      s.card/(2*(Q:ℝ)) + (E*((1/k+1/(1-k))*(H:ℝ)^k)+2*F)/2 := by
    rw [← add_sum_erase _ _ (mem_univ (0:ZMod Q)),zeroRaw]
    apply add_le_add le_rfl
    calc
      _ ≤ ∑ a ∈ (univ : Finset (ZMod Q)).erase 0, f (folded a)/4 :=
        sum_le_sum (fun a ha => bound a (mem_erase.mp ha).1)
      _ = (∑ a ∈ (univ : Finset (ZMod Q)).erase 0, f (folded a))/4 := by rw [sum_div]
      _ ≤ _ := by
        have moment := frequency_budget H Q hH hCut E F k hE hF hk hk1
        change (∑ j ∈ Icc 1 Q, f j) ≤ _ at moment
        change (∑ a ∈ (univ : Finset (ZMod Q)).erase 0, f (folded a)) ≤ _ at foldedBudget
        linarith
  have start := ReciprocalSmoothing.normalized_discrepancy s p (L:=L) hL
  rw [f_eq] at start
  change _ ≤ _ + ∑ a : ZMod Q, raw a at start
  have rounding : (s.card:ℝ)*((L:ℝ)-1)/(2*Q)+s.card/(2*(Q:ℝ))=s.card/(2*(H:ℝ)) := by
    rw [hqr]; field_simp; ring
  linarith

/-- For a list of positive moduli a, denote its jth reciprocal exponential
sum by S(j). A bound E*j^k+F/j for S(j) bounds the actual sieve remainder. -/
theorem reciprocal_transfer (u v : ℝ) (x t H : ℕ) (hH : 1 ≤ H)
    (E F k : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F) (hk : 0 < k) (hk1 : k < 1)
    (B : ∀ j : ℕ, 0 < j →
      ‖∑ m ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·),
        Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*x/m)‖ ≤ E*(j:ℝ)^k+F/j) :
    |FactorialSieve.remainder u v x t| ≤
      ((Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·)).card/(2*(H:ℝ)) +
        (E*((1/k+1/(1-k))*(H:ℝ)^k)+2*F)/2 := by
  obtain ⟨L,lp,divs⟩ := exists_grid v H
  let Q := H*L
  have l : 1 ≤ L := by omega
  let _ : NeZero Q := ⟨(Nat.mul_pos hH l).ne'⟩
  let S := (Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·)
  have C (j : ℕ) (jp : 0<j) :
      ‖∑ m ∈ S, ZMod.stdAddChar ((j:ZMod Q)*residue Q x m)‖ ≤ E*(j:ℝ)^k+F/j := by
    refine le_of_eq_of_le (congrArg _ (sum_congr rfl ?_)) (B j jp)
    intro m hm
    obtain ⟨hl,hu⟩ := mem_Ioc.mp (mem_filter.mp hm).1
    have mp : 0 < m := by omega
    exact residue_character mp (divs m mp hu) x j
  rw [remainder_grid (Q:=Q) u v x t divs]
  exact grid_transfer S (residue Q x) hH l rfl E F k hE hF hk hk1 C

end FactorialFourier
end
end

-- Source module ReciprocalCubeRoot
section

/-! Optimization of the finite Fourier cutoff at exponent one half. -/

noncomputable section
namespace FactorialFourier

/-- Balancing the unsmoothed error against square-root growth in the
frequency gives the cube-root sawtooth estimate. Both degenerate cases
are included. The positive integer cutoff is available at every scale. -/
theorem optimize_half_power {R N E F : ℝ} (hN : 0 ≤ N) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (trivial : R ≤ N/2)
    (budget : ∀ H : ℕ, 1 ≤ H → R ≤ N/(2*(H:ℝ)) + 2*E*Real.sqrt H + F) :
    R ≤ 4*N^(1/3:ℝ)*E^(2/3:ℝ)+F := by
  rcases hE.eq_or_lt with he|ep
  · subst E
    rw [Real.zero_rpow (by norm_num : (2/3:ℝ) ≠ 0),mul_zero,zero_add]
    by_contra! bad
    have dp : 0 < R-F := by linarith
    obtain ⟨H,hH⟩ := exists_nat_gt (max 1 (N/(R-F)))
    have hp : 1 ≤ H := by
      have hh := (le_max_left (1:ℝ) (N/(R-F))).trans_lt hH
      exact_mod_cast hh.le
    have hc := (div_lt_iff₀ dp).mp ((le_max_right (1:ℝ) (N/(R-F))).trans_lt hH)
    have lo := budget H hp
    simp only [mul_zero,zero_mul,add_zero] at lo
    have hp' : (0:ℝ)<H := by exact_mod_cast hp
    have hi : N/(2*(H:ℝ)) < R-F := by
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith [mul_pos hp' dp]
    linarith
  by_cases hsmall : N≤E
  · have cmp := Real.rpow_le_rpow hN hsmall (by norm_num : 0 ≤ (2/3:ℝ))
    have sep : N=N^(1/3:ℝ)*N^(2/3:ℝ) := by
      rw [← Real.rpow_add_of_nonneg hN (by norm_num) (by norm_num)]
      norm_num
    have nbound : N ≤ N^(1/3:ℝ)*E^(2/3:ℝ) := by
      calc N = _ := sep
           _ ≤ _ := mul_le_mul_of_nonneg_left cmp (by positivity)
    linarith [show 0 ≤ N^(1/3:ℝ)*E^(2/3:ℝ) by positivity]
  have np : 0<N := ep.trans_le (le_of_not_ge hsmall)
  let a : ℝ := (N/E)^(1/3:ℝ)
  have a1 : 1 ≤ a := Real.one_le_rpow ((one_le_div ep).mpr (le_of_not_ge hsmall)) (by norm_num)
  have ap : 0<a := zero_lt_one.trans_le a1
  have cube : a^3=N/E := by
    dsimp [a]
    rw [← Real.rpow_mul_natCast (div_nonneg hN hE)]
    norm_num
  have ncube := (eq_div_iff ep.ne').mp cube
  have ea : E*a = N^(1/3:ℝ)*E^(2/3:ℝ) := by
    dsimp [a]
    rw [Real.div_rpow hN hE]
    have fac : E^(1/3:ℝ)*E^(2/3:ℝ)=E := by
      rw [← Real.rpow_add ep]
      norm_num
    have en := (Real.rpow_pos_of_pos ep (1/3:ℝ)).ne'
    field_simp
    linear_combination -fac
  let H : ℕ := ⌈a^2⌉₊
  have hlo : a^2 ≤ (H:ℝ) := Nat.le_ceil _
  have hhi : (H:ℝ) < a^2+1 := Nat.ceil_lt_add_one (sq_nonneg a)
  have hHr : (1:ℝ) ≤ H := (by nlinarith [sq_nonneg (a-1)] : (1:ℝ) ≤ a^2).trans hlo
  have hH : 1 ≤ H := by exact_mod_cast hHr
  have hcut : N/(2*(H:ℝ)) ≤ E*a/2 := by
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlo (mul_nonneg hE ap.le)]
  have hs : Real.sqrt H ≤ 3*a/2 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith [sq_nonneg (a-1)]⟩
  have hb := budget H hH
  calc R ≤ 4*(E*a)+F := by nlinarith [mul_le_mul_of_nonneg_left hs hE]
       _ = _ := by rw [ea]; ring

end FactorialFourier
end
end

-- Source module ReciprocalScale
section

/-! Scaling the square-root exponential-sum test after Fourier smoothing. -/
noncomputable section
namespace FactorialFourier

private lemma cube_one_third {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1/3:ℝ))^3 = x := by
  rw [← Real.rpow_mul_natCast hx]; norm_num

private lemma cube_two_thirds {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (2/3:ℝ))^3 = x^2 := by
  rw [← Real.rpow_mul_natCast hx]; norm_num

/-- The interval length and the square-root coefficient cancel all powers
of u in the fractional-power part of the sawtooth estimate. -/
theorem scale_one_third {N x t u : ℝ} (hN : 0 ≤ N) (hx : 0 ≤ x) (ht : 0 < t)
    (hu : 0 < u) (len : N ≤ 3*u/t) :
    4*N^(1/3:ℝ)*(335*Real.sqrt (x/u))^(2/3:ℝ) ≤ 280*(x/t)^(1/3:ℝ) := by
  have X : 0 ≤ x/u := div_nonneg hx hu.le
  have coeff : 0 ≤ 335*Real.sqrt (x/u) := by positivity
  have main : N*(x/u) ≤ 3*x/t := by
    apply (mul_le_mul_of_nonneg_right len X).trans
    apply le_of_eq; field_simp
  have l : (4*N^(1/3:ℝ)*(335*Real.sqrt (x/u))^(2/3:ℝ))^3 =
      (4:ℝ)^3*335^2*(N*(x/u)) := by
    rw [mul_pow,mul_pow,cube_one_third hN,cube_two_thirds coeff,mul_pow, Real.sq_sqrt X]
    ring
  have r : (280*(x/t)^(1/3:ℝ))^3 = 280^3*(x/t) := by
    rw [mul_pow,cube_one_third (div_nonneg hx ht.le)]
  have non : 0≤x/t := div_nonneg hx ht.le
  by_contra! contra
  have pow := pow_lt_pow_left₀ contra (show 0 ≤ 280*(x/t)^(1/3:ℝ) by positivity) (by decide : 3≠0)
  rw [l,r] at pow
  rw [mul_div_assoc] at main
  linarith

end FactorialFourier
end
end

-- Source module ReciprocalFirstDerivative
section

/-! A discrete first-derivative estimate for phases with increasing increments
in a single interval between integers. The proof uses the telescoping
cotangent multiplier, as in the Kusmin–Landau inequality. -/

noncomputable section
open Finset Complex
namespace ReciprocalFirstDerivative

/-- The unit character on the real line, with period one. -/
def wave (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * (2 * (Real.pi : ℂ) * I))

theorem wave_add (x y : ℝ) : wave (x+y) = wave x * wave y := by
  simp [wave, add_mul, Complex.exp_add]

theorem wave_int (k : ℤ) : wave (k : ℝ) = 1 := by
  simp [wave, Complex.exp_int_mul_two_pi_mul_I]

@[simp] theorem norm_wave (x : ℝ) : ‖wave x‖ = 1 := by
  convert Complex.norm_exp_ofReal_mul_I (x*(2*Real.pi)) using 2
  simp [wave, mul_assoc]

private lemma wave_ne_one {x : ℝ} (hx : 0 < x) (hx' : x < 1) :
    wave x ≠ 1 := by
  intro h
  obtain ⟨k,hk⟩ := Complex.exp_eq_one_iff.mp h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have c : (2 * (Real.pi : ℂ) * I) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hpi) I_ne_zero
  have eq : (x : ℂ) = (k : ℂ) := mul_right_cancel₀ c hk
  have eqr : x = (k : ℝ) := by exact_mod_cast eq
  rw [eqr] at hx hx'
  have hk0 : 0 < k := by exact_mod_cast hx
  have hk1 : k < 1 := by exact_mod_cast hx'
  omega

private def phaseCot (x : ℝ) := Real.cot (Real.pi*x)
private def multiplier (x : ℝ) : ℂ := (1 + I*(phaseCot x : ℂ))/2

private lemma multiplier_identity {x : ℝ} (hx : 0 < x) (hx' : x < 1) :
    (1-wave x)*multiplier x = 1 := by
  have hz := sub_ne_zero.mpr (wave_ne_one hx hx').symm
  have rat := Complex.cot_pi_eq_exp_ratio (x : ℂ)
  have hh : (phaseCot x : ℂ) = (wave x+1)/(I*(1-wave x)) := by
    simpa [phaseCot,Complex.ofReal_cot,Complex.ofReal_mul,wave,mul_comm,mul_left_comm,mul_assoc] using rat
  unfold multiplier
  rw [hh]
  field_simp
  ring

private lemma phaseCot_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    phaseCot b ≤ phaseCot a := by
  have sa : 0 < Real.sin (Real.pi*a) := Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ha)
    (by nlinarith [Real.pi_pos,mul_pos Real.pi_pos (by linarith : 0 < 1-a)])
  have sb : 0 < Real.sin (Real.pi*b) := Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos (ha.trans_le hab))
    (by nlinarith [Real.pi_pos,mul_pos Real.pi_pos (sub_pos.mpr hb)])
  have ap : 0 ≤ Real.pi*a := mul_nonneg Real.pi_pos.le ha.le
  have bp : Real.pi*b ≤ Real.pi := by simpa using mul_le_mul_of_nonneg_left hb.le Real.pi_pos.le
  have h := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0 ≤ Real.pi*b-Real.pi*a by nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hab)])
    (show Real.pi*b-Real.pi*a ≤ Real.pi by linarith)
  rw [Real.sin_sub] at h
  unfold phaseCot
  rw [Real.cot_eq_cos_div_sin,Real.cot_eq_cos_div_sin,div_le_div_iff₀ sb sa]
  linarith

private lemma phaseCot_bound {a δ : ℝ} (hδ : 0 < δ) (ha : δ ≤ a) (hb : a ≤ 1-δ) :
    |phaseCot a| ≤ 1/(2*δ) := by
  have halfsin (y : ℝ) (hy : 0 ≤ y) (hy' : y ≤ 1/2) : 2*y ≤ Real.sin (Real.pi*y) := by
    convert Real.le_sin_mul (x := 2*y) (by positivity) (by linarith) using 2
    ring
  have sinlo : 2*δ ≤ Real.sin (Real.pi*a) := by
    by_cases hl : a ≤ 1/2
    · linarith [halfsin a (hδ.le.trans ha) hl]
    · have h := halfsin (1-a) (by linarith) (by linarith)
      rw [show Real.pi*(1-a) = Real.pi-Real.pi*a by ring, Real.sin_pi_sub] at h
      linarith
  have hs : 0 < Real.sin (Real.pi*a) := by linarith
  rw [phaseCot,Real.cot_eq_cos_div_sin,abs_div,abs_of_pos hs]
  exact div_le_div₀ (by norm_num) (abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩)
    (by positivity) sinlo

private lemma norm_multiplier (a : ℝ) : ‖multiplier a‖ ≤ (1+|phaseCot a|)/2 := by
  have h := norm_add_le (1 : ℂ) (I*(phaseCot a : ℂ))
  simpa [multiplier,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs] using
    (div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2))

private lemma norm_multiplier_sub {a b : ℝ} (hc : phaseCot b ≤ phaseCot a) :
    ‖multiplier b - multiplier a‖ = (phaseCot a-phaseCot b)/2 := by
  have eq : multiplier b - multiplier a = I*((phaseCot b - phaseCot a : ℝ) : ℂ)/2 := by
    simp [multiplier]; ring
  rw [eq,norm_div,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hc)]
  simp

/-- Kusmin–Landau estimate for a block of unit phases. Only the increments
through the last term of the block are used. -/
theorem kusmin_landau {N : ℕ} (z : ℕ → ℂ) (a : ℕ → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (unit : ∀ j ≤ N+1, ‖z j‖ = 1)
    (step : ∀ j ≤ N, z (j+1) = z j * wave (a j))
    (band : ∀ j ≤ N, δ ≤ a j ∧ a j ≤ 1-δ)
    (inc : ∀ j < N, a j ≤ a (j+1)) :
    ‖∑ j ∈ range (N+1), z j‖ ≤ 1 + 1/δ := by
  let M (j : ℕ) := multiplier (a j)
  have edge (j : ℕ) (hj : j ≤ N) : (z j-z (j+1))*M j = z j := by
    rw [step j hj, ← mul_one_sub]
    dsimp only [M]
    rw [mul_assoc,multiplier_identity (hδ.trans_le (band j hj).1) (by linarith [(band j hj).2]),mul_one]
  let E (j : ℕ) := (∑ i ∈ range (j+1), z i) - z 0*M 0 + z (j+1)*M j
  have err (j : ℕ) (hj : j ≤ N) : ‖E j‖ ≤ (phaseCot (a 0)-phaseCot (a j))/2 := by
    induction j with
    | zero =>
      have h := edge 0 (by omega)
      have eq : E 0 = 0 := by
        simp only [E, zero_add, sum_range_one]
        linear_combination -h
      simp [eq]
    | succ j ih =>
      have cp := phaseCot_antitone (hδ.trans_le (band j (by omega)).1) (inc j (by omega))
        (by linarith [(band (j+1) hj).2])
      have eq : E (j+1) = E j + z (j+1)*(M (j+1)-M j) := by
        dsimp only [E]
        rw [sum_range_succ (n := j+1)]
        linear_combination -(edge (j+1) hj)
      rw [eq]
      apply (norm_add_le ..).trans
      rw [norm_mul,unit (j+1) (by omega),one_mul,show M (j+1)-M j =
        multiplier (a (j+1))-multiplier (a j) from rfl,norm_multiplier_sub cp]
      linarith [ih (by omega)]
  have end_eq : (∑ j ∈ range (N+1), z j) = E N + z 0*M 0 - z (N+1)*M N := by
    dsimp only [E]; ring
  rw [end_eq]
  apply (norm_sub_le ..).trans
  apply (add_le_add (norm_add_le ..) le_rfl).trans
  rw [norm_mul,norm_mul,unit 0 (by omega),unit (N+1) (by omega),one_mul,one_mul]
  have b0 := phaseCot_bound hδ (band 0 (by omega)).1 (band 0 (by omega)).2
  have bN := phaseCot_bound hδ (band N le_rfl).1 (band N le_rfl).2
  have m0 : ‖M 0‖ ≤ (1+|phaseCot (a 0)|)/2 := norm_multiplier _
  have mN : ‖M N‖ ≤ (1+|phaseCot (a N)|)/2 := norm_multiplier _
  have den : 2*(1/(2*δ)) = 1/δ := by field_simp
  linarith [err N le_rfl, le_abs_self (phaseCot (a 0)), neg_le_abs (phaseCot (a N))]

/-- Real-phase form. The successive first differences are nondecreasing
and remain at distance at least δ from the ends of one unit interval. -/
theorem first_difference_bound (f : ℕ → ℝ) (N : ℕ) (k : ℤ) {δ : ℝ} (hδ : 0 < δ)
    (band : ∀ j ≤ N, (k:ℝ)+δ ≤ f (j+1)-f j ∧ f (j+1)-f j ≤ (k:ℝ)+1-δ)
    (inc : ∀ j < N, f (j+1)-f j ≤ f (j+2)-f (j+1)) :
    ‖∑ j ∈ range (N+1), wave (f j)‖ ≤ 1 + 1/δ := by
  let a (j : ℕ) := f (j+1)-f j-(k:ℝ)
  apply kusmin_landau (fun j => wave (f j)) a hδ (by simp)
  · intro j _
    have eq : f (j+1) = f j + (a j+(k:ℝ)) := by dsimp [a]; ring
    rw [eq,wave_add,wave_add,wave_int,mul_one]
  · intro j hj
    dsimp [a]; constructor <;> linarith [(band j hj).1,(band j hj).2]
  · intro j hj
    dsimp [a]
    linarith [inc j hj]


/-- For small frequencies the reciprocal phase stays in a single
nonresonant strip. This yields the inverse-frequency term directly. -/
theorem reciprocal_low_frequency {B Y : ℝ} (N : ℕ) (hB : 0 < B) (hY : 0 < Y)
    (small : 2*Y ≤ B*(B+1)) :
    ‖∑ j ∈ range (N+1), wave (Y/(B+j))‖ ≤ 1 + (B+N)*(B+N+1)/Y := by
  let den (j : ℕ) : ℝ := (B+j)*(B+j+1)
  have pos (j : ℕ) : 0 < den j := by dsimp [den]; positivity
  have mon : Monotone den := by
    intro a b hab
    dsimp [den]
    have habR : (a:ℝ) ≤ b := by exact_mod_cast hab
    gcongr
  have diff (j : ℕ) : Y/(B+(j+1 : ℕ))-Y/(B+j) = -(Y/den j) := by
    dsimp [den]
    push_cast
    have p : (B+(j:ℝ)) ≠ 0 := by positivity
    have q : (B+(j:ℝ)+1) ≠ 0 := by positivity
    rw [← add_assoc]
    field_simp
    ring
  let δ := Y/den N
  have hd : 0 < δ := div_pos hY (pos _)
  have hl (j : ℕ) : Y/den j ≤ 1/2 := by
    apply (div_le_iff₀ (pos j)).mpr
    have z : den 0 = B*(B+1) := by simp [den]
    linarith [mon (Nat.zero_le j)]
  have up (j : ℕ) (hj : j ≤ N) : δ ≤ Y/den j :=
    div_le_div_of_nonneg_left hY.le (pos j) (mon hj)
  have raw := first_difference_bound (fun j => Y/(B+j)) N (-1) hd (by
    intro j hj
    rw [diff]
    norm_num
    constructor
    · linarith [hl j,hl N,show δ=Y/den N by rfl]
    · linarith [up j hj]) (by
    intro j hj
    rw [diff j,diff (j+1),neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hY.le (pos j) (mon (Nat.le_succ j)))
  convert raw using 2
  dsimp [δ,den]
  field_simp

end ReciprocalFirstDerivative
end
end

-- Source module ReciprocalWindowExponential
section

/-! Reindex the exponential sums on multiples in a real interval, and
apply the reciprocal-phase square-root estimate before smoothing. -/
noncomputable section
open Finset
namespace FactorialFourier

variable {u v : ℝ} {x t j : ℕ}

private lemma sum_on_multiples {A : Type*} [AddCommMonoid A]
    (u v : ℝ) (t : ℕ) (ht : 0 < t) (f : ℕ → A) :
    (∑ m ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·), f m) =
      ∑ q ∈ Icc (⌊u/(t:ℝ)⌋₊+1) ⌊v/(t:ℝ)⌋₊, f (q*t) := by
  rw [Nat.floor_div_natCast,Nat.floor_div_natCast]
  symm
  apply sum_bij (fun q _ => q*t)
  · intro q hq
    obtain ⟨lo,hi⟩ := mem_Icc.mp hq
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul ht).mp lo,
      (Nat.le_div_iff_mul_le ht).mp hi⟩,dvd_mul_left t q⟩
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_right ht h
  · intro m hm
    obtain ⟨hm,hd⟩ := mem_filter.mp hm
    obtain ⟨lo,hi⟩ := mem_Ioc.mp hm
    have h := Nat.div_mul_cancel hd
    exact ⟨m/t,mem_Icc.mpr ⟨(Nat.div_lt_iff_lt_mul ht).mpr (by rwa [h]),
      Nat.div_le_div_right hi⟩,h⟩
  · intros; rfl

/-- A factor-three interval contains at most 3u/t multiples of t. -/
theorem multiple_window_card (ht : 0 < t) (htu : (t:ℝ) ≤ u) (huv : u ≤ v) (hv : v ≤ 3*u) :
    (((Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·)).card:ℝ) ≤ 3*u/t := by
  have tp : (0:ℝ) < t := by exact_mod_cast ht
  have up := tp.trans_le htu
  have eq := sum_on_multiples u v t ht (fun _ => (1:ℝ))
  simp only [sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc] at eq
  rw [eq]
  have cardle : ⌊v/(t:ℝ)⌋₊+1-(⌊u/(t:ℝ)⌋₊+1) ≤ ⌊v/(t:ℝ)⌋₊ := by omega
  exact (show ((⌊v/(t:ℝ)⌋₊+1-(⌊u/(t:ℝ)⌋₊+1):ℕ):ℝ) ≤ ⌊v/(t:ℝ)⌋₊ by exact_mod_cast cardle).trans
    ((Nat.floor_le (div_nonneg (up.le.trans huv) tp.le)).trans (div_le_div_of_nonneg_right hv tp.le))

/-- Trivial bound including exact integer phases, which attain magnitude 1/2. -/
theorem remainder_le_half_card (u v : ℝ) (x t : ℕ) :
    |FactorialSieve.remainder u v x t| ≤ (((Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·)).card:ℝ)/2 := by
  rw [FactorialSieve.remainder,← sum_filter]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ _m ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·), (1:ℝ)/2 := by
      apply sum_le_sum; intro m hm
      have mp : 0 < m := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp (mem_filter.mp hm).1).1
      have p : (0:ℝ) < m := by exact_mod_cast mp
      have cut : ((x%m:ℕ):ℝ) < m := by exact_mod_cast Nat.mod_lt x mp
      have h : ((x%m:ℕ):ℝ)/m < 1 := (div_lt_one p).mpr cut
      unfold FactorialSieve.saw
      exact abs_le.mpr ⟨by linarith [show (0:ℝ) ≤ ((x%m:ℕ):ℝ)/m by positivity],by linarith⟩
    _ = _ := by simp; ring

/-- The square-root bound on an integer reciprocal block implies the
frequency estimate on the exact prime-sieve window. -/
theorem window_exponential_of_sqrt
    (sqrt_bound : ∀ {Y : ℝ} {M a b : ℕ}, 0 < Y → 1 ≤ M → M ≤ a → b ≤ 3*M →
      ‖∑ q ∈ Icc a b, ReciprocalFirstDerivative.wave (Y/(q:ℝ))‖ ≤
        335*(Real.sqrt (Y/M)+(M:ℝ)^2/Y))
    (hx : 0 < x) (ht : 0 < t) (hj : 0 < j) (htu : (t:ℝ) ≤ u) (huv : u ≤ v)
    (hv : v ≤ 3*u) :
    ‖∑ m ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·),
      Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*x/m)‖ ≤
      335*Real.sqrt ((x:ℝ)/u)*(j:ℝ)^(1/2:ℝ) + (1340*u^2/((x:ℝ)*t))/j := by
  let M := ⌊u/(t:ℝ)⌋₊+1
  let b := ⌊v/(t:ℝ)⌋₊
  let Y := (j:ℝ)*x/t
  have tp : (0:ℝ) < t := by exact_mod_cast ht
  have xp : (0:ℝ) < x := by exact_mod_cast hx
  have jp : (0:ℝ) < j := by exact_mod_cast hj
  have up := tp.trans_le htu
  have yp : 0 < Y := by dsimp [Y]; positivity
  have mn : 1 ≤ M := Nat.succ_le_succ (Nat.zero_le _)
  have mp : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have ml : u/t ≤ (M:ℝ) := by simpa only [M,Nat.cast_add,Nat.cast_one] using (Nat.lt_floor_add_one (u/(t:ℝ))).le
  have mu : (M:ℝ) ≤ 2*(u/t) := by
    simp only [M,Nat.cast_add,Nat.cast_one]
    linarith [Nat.floor_le (div_nonneg up.le tp.le), (one_le_div tp).mpr htu]
  have b3 : b ≤ 3*M := by
    have h₁ : (b:ℝ) ≤ v/t := Nat.floor_le (div_nonneg (up.le.trans huv) tp.le)
    have h₂ : v/t ≤ 3*(u/t) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hv tp.le
    exact_mod_cast (show (b:ℝ) ≤ 3*(M:ℝ) by linarith)
  have eq (q : ℕ) :
      Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*x/((q*t:ℕ):ℂ)) =
        ReciprocalFirstDerivative.wave (Y/(q:ℝ)) := by
    unfold ReciprocalFirstDerivative.wave
    dsimp [Y]; push_cast; simp only [div_eq_mul_inv,mul_inv_rev]; ring
  rw [sum_on_multiples u v t ht]
  simp only [eq]
  apply (sqrt_bound yp mn le_rfl b3).trans
  have ratio : Y/(M:ℝ) ≤ ((x:ℝ)/u)*j := by
    apply (div_le_div_of_nonneg_left yp.le (div_pos up tp) ml).trans_eq
    dsimp [Y]; field_simp
  have hsq : Real.sqrt (Y/(M:ℝ)) ≤ Real.sqrt ((x:ℝ)/u)*(j:ℝ)^(1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow,← Real.sqrt_mul (div_nonneg xp.le up.le)]
    exact Real.sqrt_le_sqrt ratio
  have hir : (M:ℝ)^2/Y ≤ (4*u^2/((x:ℝ)*t))/j := by
    apply (div_le_div_of_nonneg_right (pow_le_pow_left₀ mp.le mu 2) yp.le).trans_eq
    dsimp [Y]; field_simp <;> ring
  calc
    _ ≤ 335*(Real.sqrt ((x:ℝ)/u)*(j:ℝ)^(1/2:ℝ)+(4*u^2/((x:ℝ)*t))/j) :=
      mul_le_mul_of_nonneg_left (add_le_add hsq hir) (by norm_num)
    _ = _ := by ring

end FactorialFourier
end
end

-- Source module ReciprocalSpacing
section

/-! Spacing of the successive increments of a reciprocal phase.
The phase Y/j has positive downward increments Y/(j(j+1)). On a factor-three
interval they decrease at a controlled rate. The counting results bound
indices at which the increment approaches an integer, as needed in a
second-derivative estimate for exponential sums. -/

noncomputable section
open Finset
namespace ReciprocalSpacing

/-- The downward increment of the phase from j to j+1. -/
def gap (Y : ℝ) (j : ℕ) : ℝ := Y / ((j : ℝ) * (j+1))

theorem phase_sub_phase {Y : ℝ} {j : ℕ} (hj : 0 < j) :
    Y/(j:ℝ) - Y/((j:ℝ)+1) = gap Y j := by
  have jp : (0:ℝ) < j := by exact_mod_cast hj
  unfold gap
  field_simp
  ring

/-- A lower bound for the separation per index, valid on [M,3M]. -/
def step (Y : ℝ) (M : ℕ) : ℝ := 2*Y/(3*(M:ℝ)+1)^3

theorem step_pos {Y : ℝ} (hY : 0 < Y) (M : ℕ) : 0 < step Y M := by
  unfold step
  positivity

theorem separation {Y : ℝ} {M j k : ℕ} (hY : 0 ≤ Y)
    (hM : 1 ≤ M) (hj : M ≤ j) (hjk : j ≤ k) (hk : k ≤ 3*M) :
    ((k:ℝ)-j) * step Y M ≤ gap Y j-gap Y k := by
  have jp : (0:ℝ)<j := by exact_mod_cast (show 0<j by omega)
  have kp : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have jkle : (j:ℝ) ≤ k := by exact_mod_cast hjk
  have kcap : (k:ℝ) ≤ 3*(M:ℝ) := by exact_mod_cast hk
  let L : ℝ := 3*(M:ℝ)+1
  have Lp : 0 < L := by dsimp [L]; positivity
  have c₁ : (j+1:ℝ)*(k:ℝ)*((k:ℝ)+1) ≤ L^3 := by
    rw [pow_succ, sq]
    gcongr <;> dsimp [L] <;> linarith
  have c₂ : (j:ℝ)*((j:ℝ)+1)*(k:ℝ) ≤ L^3 := by
    rw [pow_succ, sq]
    gcongr <;> dsimp [L] <;> linarith
  have a := div_le_div_of_nonneg_left (show (0:ℝ) ≤ 1 by norm_num)
    (show 0 < ((j:ℝ)+1)*k*((k:ℝ)+1) by positivity) c₁
  have b := div_le_div_of_nonneg_left (show (0:ℝ) ≤ 1 by norm_num)
    (show 0 < (j:ℝ)*((j:ℝ)+1)*k by positivity) c₂
  calc
    _ = (Y*((k:ℝ)-j))*(1/L^3+1/L^3) := by unfold step; dsimp [L]; ring
    _ ≤ (Y*((k:ℝ)-j))*(1/(((j:ℝ)+1)*k*((k:ℝ)+1))+
        1/((j:ℝ)*((j:ℝ)+1)*k)) :=
      mul_le_mul_of_nonneg_left (add_le_add a b) (mul_nonneg hY (sub_nonneg.mpr jkle))
    _ = _ := by unfold gap; field_simp; ring

theorem gap_le {Y : ℝ} {M j : ℕ} (hY : 0 ≤ Y) (hM : 1 ≤ M) (hj : M ≤ j) :
    gap Y j ≤ Y/(M:ℝ)^2 := by
  have Mp : (0:ℝ)<M := by exact_mod_cast hM
  have jr : (M:ℝ) ≤ j := by exact_mod_cast hj
  unfold gap
  apply div_le_div_of_nonneg_left hY (sq_pos_of_pos Mp)
  rw [sq]
  gcongr
  linarith

/-- Indices at which the increment lies within η of a specified center. -/
def near (Y η k : ℝ) (M : ℕ) : Finset ℕ :=
  (Icc M (3*M)).filter fun j => |gap Y j-k| < η

/-- An arbitrary center catches at most 1+2η/step indices. -/
theorem near_card {Y η k : ℝ} {M : ℕ} (hY : 0 < Y) (hη : 0 ≤ η) (hM : 1 ≤ M) :
    ((near Y η k M).card:ℝ) ≤ 1+2*η/step Y M := by
  let S := near Y η k M
  have sp := step_pos hY M
  by_cases hs : S.Nonempty
  · let a := S.min' hs
    let b := S.max' hs
    have ha : a ∈ S := min'_mem S hs
    have hb : b ∈ S := max'_mem S hs
    have hab : a ≤ b := le_max' S a ha
    have ain := mem_filter.mp (show a ∈ near Y η k M from ha)
    have bin := mem_filter.mp (show b ∈ near Y η k M from hb)
    have sep := separation hY.le hM (mem_Icc.mp ain.1).1 hab (mem_Icc.mp bin.1).2
    have top := (abs_lt.mp ain.2).2
    have bot := (abs_lt.mp bin.2).1
    have width : (b:ℝ)-a ≤ 2*η/step Y M := (le_div_iff₀ sp).mpr (by linarith)
    have subset : S ⊆ Icc a b := fun j hj =>
      mem_Icc.mpr ⟨min'_le S j hj,le_max' S j hj⟩
    have bound := card_le_card subset
    rw [Nat.card_Icc] at bound
    have coeff : ((S.card : ℕ):ℝ) ≤ (b:ℝ)+1-a := by
      exact_mod_cast (show (S.card:ℤ) ≤ (b:ℤ)+1-a by omega)
    change (S.card:ℝ) ≤ _
    linarith
  · have heq : S = ∅ := not_nonempty_iff_eq_empty.mp hs
    change (S.card:ℝ) ≤ _
    rw [heq,card_empty,Nat.cast_zero]
    positivity

/-- A finite interval containing every integer approached by an increment. -/
def centers (Y η : ℝ) (M : ℕ) : Finset ℤ := Icc 0 ⌊Y/(M:ℝ)^2+η⌋

theorem center_mem {Y η : ℝ} {k : ℤ} {M j : ℕ} (hY : 0 ≤ Y) (hM : 1 ≤ M)
    (hη : η ≤ 1) (hj : M ≤ j) (hd : |gap Y j-(k:ℝ)| < η) :
    k ∈ centers Y η M := by
  obtain ⟨lo,hi⟩ := abs_lt.mp hd
  have gnon : 0 ≤ gap Y j := by unfold gap; positivity
  have neg : (-1:ℝ) < k := by linarith
  have nonneg : (0:ℤ) ≤ k := by
    have h : (-1:ℤ) < k := by exact_mod_cast neg
    omega
  exact mem_Icc.mpr ⟨nonneg,Int.le_floor.mpr (by linarith [gap_le hY hM hj])⟩

theorem centers_card {Y η : ℝ} (hY : 0 ≤ Y) (hη : 0 ≤ η) (M : ℕ) :
    ((centers Y η M).card:ℝ) ≤ Y/(M:ℝ)^2+η+1 := by
  let R := Y/(M:ℝ)^2+η
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hfl : (0:ℤ) ≤ ⌊R⌋ := Int.floor_nonneg.mpr hR
  change ((Icc (0:ℤ) ⌊R⌋).card:ℝ) ≤ R+1
  rw [Int.card_Icc,sub_zero]
  have h := Int.floor_le R
  have nonneg : 0 ≤ ⌊R⌋ + 1 := by omega
  exact_mod_cast (show (((⌊R⌋ + 1).toNat:ℤ):ℝ) ≤ R+1 by
    rw [Int.toNat_of_nonneg nonneg,Int.cast_add,Int.cast_one]
    linarith)

open scoped Classical in
/-- All near-resonant indices in the factor-three interval. -/
def resonant (Y η : ℝ) (M : ℕ) : Finset ℕ :=
  (Icc M (3*M)).filter fun j => ∃ k : ℤ, |gap Y j-(k:ℝ)| < η

theorem resonant_card {Y η : ℝ} {M : ℕ} (hY : 0 < Y) (hM : 1 ≤ M)
    (hη : 0 ≤ η) (hη' : η ≤ 1) :
    ((resonant Y η M).card : ℝ) ≤
      (Y/(M:ℝ)^2+η+1)*(1+2*η/step Y M) := by
  classical
  let C := centers Y η M
  let S := fun k : ℤ => near Y η (k:ℝ) M
  have sub : resonant Y η M ⊆ C.biUnion S := by
    intro j hj
    obtain ⟨mem,⟨k,hk⟩⟩ := mem_filter.mp hj
    exact mem_biUnion.mpr ⟨k,center_mem hY.le hM hη' (mem_Icc.mp mem).1 hk,
      mem_filter.mpr ⟨mem,hk⟩⟩
  have nbound := (card_le_card sub).trans (card_biUnion_le (s:=C) (t:=S))
  have rbound : ((resonant Y η M).card:ℝ) ≤ ∑ k ∈ C, ((S k).card:ℝ) := by exact_mod_cast nbound
  calc
    _ ≤ _ := rbound
    _ ≤ ∑ _k ∈ C,(1+2*η/step Y M) := sum_le_sum fun k _ => near_card (k:=(k:ℝ)) hY hη hM
    _ = (C.card:ℝ)*(1+2*η/step Y M) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (centers_card hY.le hη M) (by
      have := step_pos hY M
      positivity)


/-- Sum on an interval, given cancellation on every smaller interval in a
single safe cell of the increment. The cells left after removing near-integer
gaps are intervals because the gaps decrease. -/
theorem block_of_safe_cells {Y η K : ℝ} {M a b : ℕ} (hY : 0 < Y) (hM : 1 ≤ M)
    (ha : M ≤ a) (hb : b ≤ 3*M) (hη : 0 < η) (hη' : η ≤ 1) (hK : 0 ≤ K)
    (F : ℕ → ℂ) (unit : ∀ j, ‖F j‖ ≤ 1)
    (safe : ∀ c d : ℕ, a ≤ c → c ≤ d → d ≤ b → ∀ k : ℤ,
      (∀ j ∈ Icc c d, (k:ℝ)+η ≤ gap Y j ∧ gap Y j ≤ (k:ℝ)+1-η) →
      ‖∑ j ∈ Icc c d,F j‖ ≤ K) :
    ‖∑ j ∈ Icc a b,F j‖ ≤
      (Y/(M:ℝ)^2+η+1)*(1+2*η/step Y M + K) := by
  classical
  let U := Icc a b
  let B := U.filter fun j => ∃ k : ℤ, |gap Y j-(k:ℝ)| < η
  let G := U.filter fun j => ¬∃ k : ℤ, |gap Y j-(k:ℝ)| < η
  let C := centers Y η M
  let S (k : ℤ) := G.filter fun j => ⌊gap Y j⌋ = k
  have bounds {j : ℕ} (hj : j ∈ U) := mem_Icc.mp hj
  have badSub : B ⊆ resonant Y η M := by
    intro j hj
    obtain ⟨hj,hd⟩ := mem_filter.mp hj
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨ha.trans (bounds hj).1,(bounds hj).2.trans hb⟩,hd⟩
  have Gmap (j : ℕ) (hj : j ∈ G) : ⌊gap Y j⌋ ∈ C := by
    have jm := ha.trans (bounds (mem_filter.mp hj).1).1
    have pos : 0 ≤ gap Y j := by unfold gap; positivity
    apply mem_Icc.mpr
    refine ⟨Int.floor_nonneg.mpr pos,Int.floor_mono ?_⟩
    linarith [gap_le hY.le hM jm]
  have cellBounds {j : ℕ} {k : ℤ} (hj : j ∈ S k) :
      (k:ℝ)+η ≤ gap Y j ∧ gap Y j ≤ (k:ℝ)+1-η := by
    obtain ⟨hg,hf⟩ := mem_filter.mp hj
    have hn := (mem_filter.mp hg).2
    have fl := Int.floor_le (gap Y j)
    have fh := Int.lt_floor_add_one (gap Y j)
    rw [hf] at fl fh
    have h₁ : η ≤ |gap Y j-(k:ℝ)| := le_of_not_gt fun h => hn ⟨k,h⟩
    have h₂ : η ≤ |gap Y j-((k+1:ℤ):ℝ)| := le_of_not_gt fun h => hn ⟨k+1,h⟩
    push_cast at h₂
    rw [abs_of_nonneg (sub_nonneg.mpr fl)] at h₁
    rw [abs_of_nonpos (by linarith : gap Y j - ((k:ℝ)+1) ≤ 0)] at h₂
    constructor <;> linarith
  have makeCell {j : ℕ} {k : ℤ} (hj : j ∈ U)
      (hd : (k:ℝ)+η ≤ gap Y j ∧ gap Y j ≤ (k:ℝ)+1-η) : j ∈ S k := by
    have hf : ⌊gap Y j⌋ = k := Int.floor_eq_iff.mpr ⟨by linarith [hd.1],by linarith [hd.2]⟩
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨hj,?_⟩,hf⟩
    rintro ⟨l,hl⟩
    obtain ⟨low,high⟩ := abs_lt.mp hl
    by_cases e : l ≤ k
    · have er : (l:ℝ) ≤ k := by exact_mod_cast e
      linarith [hd.1]
    · have ei : k+1 ≤ l := by omega
      have er : (k:ℝ)+1 ≤ l := by exact_mod_cast ei
      linarith [hd.2]
  have mono {j k : ℕ} (hj : M ≤ j) (hjk : j ≤ k) (hk : k ≤ 3*M) :
      gap Y k ≤ gap Y j := by
    have sr := separation hY.le hM hj hjk hk
    have le : (0:ℝ) ≤ (k:ℝ)-(j:ℝ) := sub_nonneg.mpr (by exact_mod_cast hjk)
    have nonneg := mul_nonneg le (step_pos hY M).le
    linarith
  have sumcell (k : ℤ) : ‖∑ j ∈ S k,F j‖ ≤ K := by
    by_cases hs : (S k).Nonempty
    · let c := (S k).min' hs
      let d := (S k).max' hs
      have cm : c ∈ S k := min'_mem _ _
      have dm : d ∈ S k := max'_mem _ _
      have cu := bounds (mem_filter.mp (mem_filter.mp cm).1).1
      have du := bounds (mem_filter.mp (mem_filter.mp dm).1).1
      have cd : c ≤ d := le_max' _ _ cm
      have between (j : ℕ) (hj : j ∈ Icc c d) :
          (k:ℝ)+η ≤ gap Y j ∧ gap Y j ≤ (k:ℝ)+1-η := by
        obtain ⟨jl,jr⟩ := mem_Icc.mp hj
        have low := mono (ha.trans (cu.1.trans jl)) jr (du.2.trans hb)
        have high := mono (ha.trans cu.1) jl (jr.trans (du.2.trans hb))
        exact ⟨(cellBounds dm).1.trans low, high.trans (cellBounds cm).2⟩
      have eq : S k = Icc c d := by
        ext j
        constructor
        · intro hj
          exact mem_Icc.mpr ⟨min'_le _ _ hj,le_max' _ _ hj⟩
        · intro hj
          exact makeCell (mem_Icc.mpr ⟨cu.1.trans (mem_Icc.mp hj).1,(mem_Icc.mp hj).2.trans du.2⟩)
            (between j hj)
      rw [eq]
      exact safe c d cu.1 cd du.2 k between
    · rw [not_nonempty_iff_eq_empty.mp hs]
      simpa using hK
  have decomp : ∑ j ∈ B,F j + ∑ j ∈ G,F j = ∑ j ∈ U,F j :=
    sum_filter_add_sum_filter_not _ _ _
  have partition : ∑ k ∈ C,∑ j ∈ S k,F j = ∑ j ∈ G,F j :=
    Finset.sum_fiberwise_of_maps_to Gmap F
  have bcost : ‖∑ j ∈ B,F j‖ ≤ (resonant Y η M).card := by
    calc _ ≤ ∑ j ∈ B,‖F j‖ := norm_sum_le _ _
         _ ≤ ∑ _j ∈ B,(1:ℝ) := sum_le_sum fun j _ => unit j
         _ = B.card := by simp
         _ ≤ _ := by exact_mod_cast card_le_card badSub
  have gcost : ‖∑ j ∈ G,F j‖ ≤ (C.card:ℝ)*K := by
    rw [← partition]
    calc _ ≤ ∑ k ∈ C,‖∑ j ∈ S k,F j‖ := norm_sum_le _ _
         _ ≤ ∑ _k ∈ C,K := sum_le_sum fun k _ => sumcell k
         _ = _ := by simp
  rw [← decomp]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ ((resonant Y η M).card:ℝ)+(C.card:ℝ)*K := add_le_add bcost gcost
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add (resonant_card hY hM hη.le hη') (mul_le_mul_of_nonneg_right
        (centers_card hY.le hη.le M) hK)

end ReciprocalSpacing
end
end

-- Source module ReciprocalSecondDerivative
section

/-! A finite second-derivative estimate for the reciprocal phase. The
single-strip Kusmin–Landau inequality and the count of exceptional
increments give the square-root bound, uniformly on each subinterval of
a factor-three interval and for every positive real frequency. -/

noncomputable section
open Finset ReciprocalFirstDerivative
namespace ReciprocalSpacing

/-- A reciprocal phase sum on every subinterval of [M,3M]. The parameter η
balances the total number of near-integer increments and the cost of
cancellation on the remaining intervals. -/
theorem reciprocal_block {Y η : ℝ} {M a b : ℕ} (hY : 0 < Y) (hM : 1 ≤ M)
    (ha : M ≤ a) (hb : b ≤ 3*M) (hη : 0 < η) (hη' : η ≤ 1) :
    ‖∑ j ∈ Icc a b, wave (Y/(j:ℝ))‖ ≤
      (Y/(M:ℝ)^2+η+1)*(1+2*η/step Y M + (1+1/η)) := by
  apply block_of_safe_cells hY hM ha hb hη hη' (by positivity) _ (by simp)
  intro c d ac cd db k band
  let f (j : ℕ) : ℝ := Y/((c+j:ℕ):ℝ)
  have diff (j : ℕ) : f (j+1)-f j = -gap Y (c+j) := by
    have e := phase_sub_phase (Y:=Y) (j:=c+j) (by omega)
    dsimp [f]
    push_cast at *
    rw [← add_assoc]
    linarith
  have inc (j : ℕ) (hj : j < d-c) : f (j+1)-f j ≤ f (j+2)-f (j+1) := by
    rw [diff j,diff (j+1),neg_le_neg_iff]
    have sep := separation hY.le hM (j:=c+j) (k:=c+(j+1)) (by omega) (by omega) (by omega)
    have nonneg : 0 ≤ ((c+(j+1):ℕ):ℝ)-((c+j:ℕ):ℝ) := sub_nonneg.mpr (by exact_mod_cast (show c+j ≤ c+(j+1) by omega))
    linarith [mul_nonneg nonneg (step_pos hY M).le]
  have safe (j : ℕ) (hj : j ≤ d-c) :
      ((-k-1:ℤ):ℝ)+η ≤ f (j+1)-f j ∧ f (j+1)-f j ≤ ((-k-1:ℤ):ℝ)+1-η := by
    have bj := band (c+j) (mem_Icc.mpr ⟨by omega,by omega⟩)
    rw [diff]
    push_cast
    constructor <;> linarith [bj.1,bj.2]
  have h := first_difference_bound f (d-c) (-k-1) hη safe inc
  rw [← Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range,show d+1-c = d-c+1 by omega]
  simpa only [f, Nat.add_comm] using h


/-- The classical square-root exponent-pair bound for every reciprocal
phase, with an explicit absolute constant on a factor-three interval. -/
theorem reciprocal_sqrt_bound {Y : ℝ} {M a b : ℕ} (hY : 0 < Y) (hM : 1 ≤ M)
    (ha : M ≤ a) (hb : b ≤ 3*M) :
    ‖∑ j ∈ Icc a b, wave (Y/(j:ℝ))‖ ≤
      335*(Real.sqrt (Y/M) + (M:ℝ)^2/Y) := by
  let m : ℝ := M
  have m1 : 1 ≤ m := by dsimp [m]; exact_mod_cast hM
  have mp : 0 < m := by linarith
  have wp : 0 < Real.sqrt (Y/m) := Real.sqrt_pos.mpr (div_pos hY mp)
  let W := Real.sqrt (Y/m)
  have ws : W^2*m=Y := by
    rw [show W^2=Y/m from Real.sq_sqrt (div_nonneg hY.le mp.le),div_mul_cancel₀ _ mp.ne']
  change _ ≤ 335*(W+m^2/Y)
  have rp : 0 ≤ m^2/Y := by positivity
  by_cases ab : a ≤ b
  · have posA : 0 < (a:ℝ) := by exact_mod_cast (show 0<a by omega)
    have am : m ≤ a := by dsimp [m]; exact_mod_cast ha
    have bm : (b:ℝ) ≤ 3*m := by dsimp [m]; exact_mod_cast hb
    by_cases low : 2*Y ≤ m^2
    · have aa : m^2 ≤ (a:ℝ)*(a+1) := by rw [sq]; gcongr; linarith
      have h := reciprocal_low_frequency (b-a) posA hY (low.trans aa)
      have castN : ((b-a:ℕ):ℝ) = (b:ℝ)-a := Nat.cast_sub ab
      rw [castN,show (a:ℝ)+(b-a)=b by ring] at h
      rw [← Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range,show b+1-a = b-a+1 by omega]
      simp only [Nat.cast_add] 
      apply h.trans
      have prod : (b:ℝ)*(b+1) ≤ 12*m^2 := by
        calc _ ≤ (3*m)*(4*m) := mul_le_mul bm (by linarith) (by positivity) (by positivity)
             _ = _ := by ring
      have one : 1 ≤ m^2/Y := (le_div_iff₀ hY).mpr (by linarith)
      have hh := div_le_div_of_nonneg_right prod hY.le
      rw [show 12*m^2/Y=12*(m^2/Y) by ring] at hh
      linarith [show 0≤W from wp.le]
    · by_cases high : m^3 ≤ Y
      · have ms : m ≤ W := by
          by_contra! eq
          have q := mul_lt_mul_of_pos_right (pow_lt_pow_left₀ eq wp.le (by decide : 2≠0)) mp
          nlinarith
        have len : ((Icc a b).card:ℝ) ≤ 3*m := by
          rw [Nat.card_Icc]
          dsimp only [m]
          exact_mod_cast (show b+1-a ≤3*M by omega)
        calc _ ≤ ∑ j ∈ Icc a b,‖wave (Y/(j:ℝ))‖ := norm_sum_le _ _
             _ = (Icc a b).card := by simp
             _ ≤ 3*m := len
             _ ≤ _ := by linarith
      · let η := W/m
        have ep : 0 < η := div_pos wp mp
        have es : η ≤ 1 := by
          apply (div_le_one mp).mpr
          by_contra! e
          have q := mul_lt_mul_of_pos_right (pow_lt_pow_left₀ e mp.le (by decide : 2≠0)) mp
          nlinarith
        have ee : η^2* m^3 = Y := by
          dsimp only [η]
          rw [← ws]
          field_simp
        have raw := reciprocal_block hY hM ha hb ep es
        have c₁ : Y/m^2+η+1 ≤ 5*(Y/m^2) := by
          have z : (1:ℝ)/2 ≤ Y/m^2 := (le_div_iff₀ (sq_pos_of_pos mp)).mpr (by linarith)
          linarith
        have cap : (3*m+1)^3 ≤ 64*m^3 := by
          calc _ ≤ (4*m)^3 := by gcongr; linarith
               _ = _ := by ring
        have hterm : 2*η/step Y M ≤ 64/η := by
          change 2*η/(2*Y/(3*m+1)^3) ≤ 64/η
          have pp : (0:ℝ)<3*m+1 := by positivity
          field_simp
          nlinarith [mul_le_mul_of_nonneg_left cap (sq_nonneg η)]
        have c₂ : 1+2*η/step Y M+(1+1/η) ≤ 67/η := by
          have one : 1 ≤ 1/η := (one_le_div ep).mpr es
          linarith [show (67:ℝ)/η=1/η+2*(1/η)+64/η by ring]
        have non := step_pos hY M
        have est := mul_le_mul c₁ c₂ (by positivity) (by positivity)
        apply raw.trans (est.trans ?_)
        have alg : 5*(Y/m^2)*(67/η) = 335*W := by
          dsimp only [η]
          rw [← ws]
          field_simp
          ring
        rw [alg]
        linarith
  · rw [Icc_eq_empty ab,sum_empty,norm_zero]
    positivity

end ReciprocalSpacing
end
end

-- Source module ReciprocalPrimeBlock
section

/-! The unconditional square-root exponent-pair case of the factorial sieve.
The final prime block bound is uniform in every admissible integer and both
real endpoints. The constants are explicit. -/
noncomputable section
open Finset Real
namespace FactorialFourier

/-- Unconditional centered sawtooth estimate on a multiplicative interval.
It gives the (1/2,1/2) case of the local estimate in EGIP's Lemma 3. -/
theorem reciprocal_cube_root {x t : ℕ} {u v : ℝ} (hx : 0 < x) (ht : 0 < t)
    (htu : (t:ℝ) ≤ u) (huv : u ≤ v) (hv : v ≤ 3*u) :
    |FactorialSieve.remainder u v x t| ≤
      280*((x:ℝ)/t)^(1/3:ℝ) + 1340*u^2/((x:ℝ)*t) := by
  let N : ℝ := ((Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·)).card
  let E := 335*Real.sqrt ((x:ℝ)/u)
  let F := 1340*u^2/((x:ℝ)*t)
  have tp : (0:ℝ) < t := by exact_mod_cast ht
  have up := tp.trans_le htu
  have n0 : 0 ≤ N := by dsimp [N]; positivity
  have e0 : 0 ≤ E := by dsimp [E]; positivity
  have f0 : 0 ≤ F := by dsimp [F]; positivity
  have budget (H : ℕ) (hh : 1 ≤ H) :
      |FactorialSieve.remainder u v x t| ≤ N/(2*(H:ℝ)) + 2*E*Real.sqrt H + F := by
    have b := reciprocal_transfer u v x t H hh E F (1/2) e0 f0 (by norm_num) (by norm_num)
      (fun j hj => window_exponential_of_sqrt (@ReciprocalSpacing.reciprocal_sqrt_bound)
        hx ht hj htu huv hv)
    apply b.trans_eq
    rw [← Real.sqrt_eq_rpow]
    dsimp only [N]
    ring
  have opt := optimize_half_power n0 e0 f0 (remainder_le_half_card u v x t) budget
  exact opt.trans (add_le_add (scale_one_third n0 (Nat.cast_nonneg x) tp up
    (multiple_window_card ht htu huv hv)) le_rfl)

/-- A bound for the number of prime-divisor hits in one interval, with no
unproved premise on oscillatory sums. -/
theorem prime_block_sqrt (n h z : ℕ) (u v : ℝ) (hn : 0 < n) (hz : 1 ≤ z)
    (zu : (z:ℝ)^2 ≤ u) (huv : u ≤ v) (hv : v ≤ 3*u) :
    (∑ p ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime, (FactorialSieve.multiplicity n h p:ℝ)) ≤
    (h:ℝ)*log (v/u)/log ((z:ℝ)+1) + 2*h*(z:ℝ)^2/u +
      3150*((n:ℝ)+h)^(1/3:ℝ)*(z:ℝ)^(4/3:ℝ) +
      2680*u^2/(n:ℝ)*(1+log z)^3 := by
  let A := 280*((n:ℝ)+h)^(1/3:ℝ)
  let B := 1340*u^2/(n:ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have bounds (x : ℕ) (hx : x ∈ ({n,n+h} : Finset ℕ)) (t : ℕ) (ht : 1 ≤ t) (tz : t ≤ z^2) :
      |FactorialSieve.remainder u v x t| ≤ A*(t:ℝ)^(-(1/3:ℝ)) + B/t := by
    have nx : n ≤ x ∧ x ≤ n+h := by
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl|rfl <;> omega
    have xp := hn.trans_le nx.1
    have nr : (0:ℝ) < n := by exact_mod_cast hn
    have xr : (0:ℝ) < x := by exact_mod_cast xp
    have tr : (0:ℝ) < t := by exact_mod_cast ht
    have localBound := reciprocal_cube_root xp ht ((show (t:ℝ) ≤ (z:ℝ)^2 by exact_mod_cast tz).trans zu) huv hv
    refine localBound.trans (add_le_add ?_ ?_)
    · have xx : (x:ℝ)^(1/3:ℝ) ≤ ((n:ℝ)+h)^(1/3:ℝ) := by
        apply Real.rpow_le_rpow xr.le (by exact_mod_cast nx.2) (by norm_num)
      rw [Real.div_rpow xr.le tr.le,Real.rpow_neg tr.le]
      dsimp only [A]
      rw [div_eq_mul_inv,← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left xx (by norm_num)) (by positivity)
    · rw [← div_div]; dsimp only [B]
      apply div_le_div_of_nonneg_right _ tr.le
      exact div_le_div_of_nonneg_left (by positivity) nr (by exact_mod_cast nx.1)
  have total := FactorialSieve.short_interval_from_local n h z u v A B (1/3) hz zu huv hA hB
    (by norm_num) (by norm_num) bounds
  apply total.trans_eq
  dsimp only [A,B]
  norm_num
  ring

end FactorialFourier
end
end

-- Source module ReciprocalHitCount
section

/-! Counting the project’s prime hits by the prime and the corresponding
multiple. The source set may already have been restricted to a wider band. -/
open Finset
namespace FactorialFourier

theorem hit_card_le (n h : ℕ) (u v : ℝ) (hu : 0 ≤ u)
    (S : Finset ((i : ℕ) × ℕ))
    (hits : ∀ z ∈ S, z.1 < h ∧ z.2.Prime ∧ z.2 ∣ n+z.1+1 ∧ u < (z.2:ℝ) ∧ (z.2:ℝ) ≤ v) :
    (S.card : ℝ) ≤ ∑ p ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime, (FactorialSieve.multiplicity n h p:ℝ) := by
  classical
  let P := (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime
  let f (z : (i : ℕ) × ℕ) : (p : ℕ) × ℕ := ⟨z.2,(n+z.1+1)/z.2⟩
  have inj := card_le_card_of_injOn (s:=S) (t:=P.sigma (fun p => Ioc (n/p) ((n+h)/p))) f (by
    intro z hz
    obtain ⟨hi,prime,hd,lo,up⟩ := hits z hz
    have recover :=  Nat.div_mul_cancel hd
    apply mem_sigma.mpr
    refine ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.floor_lt hu).mpr lo,(Nat.le_floor up)⟩,prime⟩,?_⟩
    exact mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul prime.pos).mpr (by rw [recover]; omega),
      Nat.div_le_div_right (by omega)⟩) (by
    rintro ⟨i,p⟩ hi ⟨j,q⟩ hj eq
    have pq : p=q := congrArg Sigma.fst eq
    subst q
    have hq : (n+i+1)/p=(n+j+1)/p := congrArg (fun y : (k:ℕ) × ℕ => y.2) eq
    have l := Nat.div_mul_cancel (hits _ hi).2.2.1
    have r := Nat.div_mul_cancel (hits _ hj).2.2.1
    change (n+i+1)/p*p=n+i+1 at l
    change (n+j+1)/p*p=n+j+1 at r
    rw [hq] at l
    have e : i=j := by omega
    subst j; rfl)
  simp only [card_sigma,Nat.card_Ioc] at inj
  dsimp [P] at inj
  change (S.card:ℝ) ≤ ∑ p ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime, (((n+h)/p-n/p:ℕ):ℝ)
  exact_mod_cast inj

end FactorialFourier
end

-- Source module ReciprocalDyadic
section

/-! A clipped dyadic cover for the prime blocks in the four-ninths sieve.
The logarithmic main term telescopes exactly, the reciprocal rounding error
sums from the lower endpoint, and the quadratic error sums from the upper
endpoint. The summand may have either sign. -/

noncomputable section
open Finset Real
namespace FactorialDyadic

/-- An interval sum with the same open-left, closed-right convention as the sieve. -/
def intervalSum (f : ℕ → ℝ) (u v : ℝ) : ℝ := ∑ m ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, f m

private theorem interval_add (f : ℕ → ℝ) {u b v : ℝ} (hub : u ≤ b) (hbv : b ≤ v) :
    intervalSum f u b + intervalSum f b v = intervalSum f u v :=
  sum_Ioc_consecutive f (Nat.floor_mono hub) (Nat.floor_mono hbv)

private theorem covering (f : ℕ → ℝ) (D E F G : ℝ)
    (hE : 0 ≤ E) (hF : 0 ≤ F) (hG : 0 ≤ G) (K : ℕ) {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (cap : v ≤ u*2^K)
    (block : ∀ a b, u ≤ a → a ≤ b → b ≤ v → b ≤ 2*a →
      intervalSum f a b ≤ D*log (b/a) + E/a + F + G*a^2) :
    intervalSum f u v ≤ D*log (v/u) + E*(2/u-1/v) +
      (K:ℝ)*F + G*((4*v^2-u^2)/3) := by
  have hv := hu.trans_le huv
  induction K generalizing u with
  | zero =>
    have eq : v=u := le_antisymm (by simpa using cap) huv
    subst v
    simp only [intervalSum,Ioc_self,sum_empty,div_self hu.ne',Real.log_one,mul_zero,
      zero_add,Nat.cast_zero,zero_mul,add_zero]
    have h₁ : 0 ≤ E*(2/u-1/u) := by
      apply mul_nonneg hE; rw [← sub_div]; positivity
    have h₂ : 0 ≤ G*((4*u^2-u^2)/3) := by
      apply mul_nonneg hG; nlinarith [sq_nonneg u]
    linarith
  | succ K ih =>
    have up : u ≤ 2*u := by linarith
    by_cases small : v ≤ 2*u
    · apply (block u v le_rfl huv le_rfl small).trans
      have e : 1/v ≤ 1/u := one_div_le_one_div_of_le hu huv
      have e' : E/u ≤ E*(2/u-1/v) := by
        rw [div_eq_mul_one_div]; apply mul_le_mul_of_nonneg_left _ hE
        linarith [show 2/u = 2*(1/u) by ring]
      have g' : G*u^2 ≤ G*((4*v^2-u^2)/3) := by
        apply mul_le_mul_of_nonneg_left _ hG
        nlinarith [sq_le_sq' (by linarith : -v ≤ u) huv]
      rw [Nat.cast_succ]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) K) hF]
    · have split_le : 2*u ≤ v := le_of_not_ge small
      have pos : 0 < 2*u := by positivity
      have upper : v ≤ (2*u)*2^K := by rw [pow_succ] at cap; linarith only [cap,show u*(2^K*2)=(2*u)*2^K by ring]
      have first := block u (2*u) le_rfl up split_le le_rfl
      have rest := ih pos split_le upper
        (fun a b ha hab hb hba => block a b (up.trans ha) hab hb hba)
      rw [← interval_add f up split_le]
      apply (add_le_add first rest).trans
      apply le_of_eq
      rw [Real.log_div hv.ne' hu.ne', Real.log_div pos.ne' hu.ne', Real.log_div hv.ne' pos.ne',
        Nat.cast_succ]
      field_simp
      ring

/-- The exact logarithmic main term survives clipping the last block.
The number of blocks is at most 1+log(v/u)/log 2. The endpoint errors
have bounds 2E/u and (4/3)G v² regardless of the number of blocks. -/
theorem clipped_dyadic_sum (f : ℕ → ℝ) {u v D E F G : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hE : 0 ≤ E) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (block : ∀ a b, u ≤ a → a ≤ b → b ≤ v → b ≤ 2*a →
      intervalSum f a b ≤ D*log (b/a) + E/a + F + G*a^2) :
    intervalSum f u v ≤ D*log (v/u) + 2*E/u +
      (1+log (v/u)/log 2)*F + (4/3)*G*v^2 := by
  let q := log (v/u)/log 2
  let K := ⌊q⌋₊+1
  have hv := hu.trans_le huv
  have pos2 : 0 < log (2:ℝ) := Real.log_pos (by norm_num)
  have hq : 0 ≤ q := div_nonneg (log_nonneg ((le_div_iff₀ hu).mpr (by simpa using huv))) pos2.le
  have k_low : q ≤ (K:ℝ) := by
    dsimp [K]; push_cast; exact (Nat.lt_floor_add_one q).le
  have k_high : (K:ℝ) ≤ 1+q := by
    dsimp [K]; push_cast; linarith [Nat.floor_le hq]
  have cap : v ≤ u*2^K := by
    apply (Real.log_le_log_iff hv (by positivity)).mp
    rw [log_mul hu.ne' (by positivity),log_pow]
    have e := (div_le_iff₀ pos2).mp k_low
    rw [log_div hv.ne' hu.ne'] at e
    linarith
  apply (covering f D E F G hE hF hG K hu huv cap block).trans
  have low : E*(2/u-1/v) ≤ 2*E/u := by
    calc _ ≤ E*(2/u) := mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) hE
         _ = _ := by ring
  have high : G*((4*v^2-u^2)/3) ≤ (4/3)*G*v^2 := by
    nlinarith [mul_nonneg hG (sq_nonneg u)]
  have mid := mul_le_mul_of_nonneg_right k_high hF
  dsimp [q] at mid
  linarith

/-- Transfer the single-modulus bounds on clipped dyadic blocks directly to
a prime count over the whole band. Constants A and B are uniform over the
two endpoints and all subblocks. -/
theorem prime_band_from_local (n h z : ℕ) {u v A B s : ℝ}
    (hz : 1 ≤ z) (hzu : (z:ℝ)^2 ≤ u) (huv : u ≤ v)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (local_est : ∀ a b, u ≤ a → a ≤ b → b ≤ v → b ≤ 2*a →
      ∀ x ∈ ({n,n+h} : Finset ℕ), ∀ t : ℕ, 1 ≤ t → t ≤ z^2 →
        |FactorialSieve.remainder a b x t| ≤ A*(t:ℝ)^(-s) + B*a^2/t) :
    (∑ p ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime, (FactorialSieve.multiplicity n h p:ℝ)) ≤
      (h:ℝ)*log (v/u)/log ((z:ℝ)+1) + 4*h*(z:ℝ)^2/u +
      (1+log (v/u)/log 2)*
        (2*A*(((1+1/(1-s))/(1-s)^2)*(z:ℝ)^(2*(1-s)))) +
      (8/3)*B*(1+log z)^3*v^2 := by
  let f (p : ℕ) : ℝ := if p.Prime then FactorialSieve.multiplicity n h p else 0
  let M := (((1+1/(1-s))/(1-s)^2)*(z:ℝ)^(2*(1-s)))
  have hpow : 0 < 1-s := sub_pos.mpr hs1
  have mpos : 0 ≤ M := by dsimp [M]; positivity
  have zpos : 0 < (z:ℝ) := by exact_mod_cast (show 0<z by omega)
  have hu : 0 < u := (sq_pos_of_pos zpos).trans_le hzu
  have lg := Real.log_natCast_nonneg z
  have local_block (a b : ℝ) (ha : u ≤ a) (hab : a ≤ b) (hb : b ≤ v) (tw : b ≤ 2*a) :
      intervalSum f a b ≤ ((h:ℝ)/log ((z:ℝ)+1))*log (b/a) +
        (2*h*(z:ℝ)^2)/a + (2*A*M) + (2*B*(1+log z)^3)*a^2 := by
    have raw := FactorialSieve.short_interval_from_local n h z a b A (B*a^2) s hz
      (hzu.trans ha) hab hA (mul_nonneg hB (sq_nonneg _)) hs0 hs1 (local_est a b ha hab hb tw)
    dsimp only [intervalSum,f]
    rw [← sum_filter]
    apply raw.trans
    apply le_of_eq
    dsimp only [M]
    ring
  have total := clipped_dyadic_sum f hu huv (by positivity : 0 ≤ 2*h*(z:ℝ)^2)
    (by positivity : 0 ≤ 2*A*M) (by positivity : 0 ≤ 2*B*(1+log z)^3) local_block
  dsimp only [intervalSum,f] at total
  rw [← sum_filter] at total
  apply total.trans
  apply le_of_eq
  dsimp only [M]
  ring

/-- Fixed constants for the square-root exponent pair over any whole prime
band. The input is the unconditional single-block theorem with its original
upper limit b ≤ 3a. The cover only needs b ≤ 2a. -/
theorem prime_band_sqrt_of_block (n h z : ℕ) (u v : ℝ) (hn : 0 < n)
    (hz : 1 ≤ z) (zu : (z:ℝ)^2 ≤ u) (huv : u ≤ v)
    (single : ∀ a b : ℝ, (z:ℝ)^2 ≤ a → a ≤ b → b ≤ 3*a →
      (∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (FactorialSieve.multiplicity n h p:ℝ)) ≤
      (h:ℝ)*log (b/a)/log ((z:ℝ)+1) + 2*h*(z:ℝ)^2/a +
      3150*((n:ℝ)+h)^(1/3:ℝ)*(z:ℝ)^(4/3:ℝ) + 2680*a^2/(n:ℝ)*(1+log z)^3) :
    (∑ p ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime, (FactorialSieve.multiplicity n h p:ℝ)) ≤
      (h:ℝ)*log (v/u)/log ((z:ℝ)+1) + 4*h*(z:ℝ)^2/u +
      (1+log (v/u)/log 2)*(3150*((n:ℝ)+h)^(1/3:ℝ)*(z:ℝ)^(4/3:ℝ)) +
      (10720/3)*v^2/(n:ℝ)*(1+log z)^3 := by
  let f (p : ℕ) : ℝ := if p.Prime then FactorialSieve.multiplicity n h p else 0
  let F := 3150*((n:ℝ)+h)^(1/3:ℝ)*(z:ℝ)^(4/3:ℝ)
  let G := 2680/(n:ℝ)*(1+log z)^3
  have zpos : (0:ℝ) < z := by exact_mod_cast (show 0<z by omega)
  have hu := (sq_pos_of_pos zpos).trans_le zu
  have npos : (0:ℝ) < n := by exact_mod_cast hn
  have lg := Real.log_natCast_nonneg z
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have block (a b : ℝ) (ha : u ≤ a) (hab : a ≤ b) (_hb : b ≤ v) (tw : b ≤ 2*a) :
      intervalSum f a b ≤ ((h:ℝ)/log ((z:ℝ)+1))*log (b/a) +
        (2*h*(z:ℝ)^2)/a + F + G*a^2 := by
    dsimp only [intervalSum,f]
    rw [← sum_filter]
    apply (single a b (zu.trans ha) hab (by linarith)).trans_eq
    dsimp only [F,G]
    ring
  have total := clipped_dyadic_sum f hu huv (by positivity : 0 ≤ 2*h*(z:ℝ)^2) hF hG block
  dsimp only [intervalSum,f] at total
  rw [← sum_filter] at total
  apply total.trans_eq
  dsimp only [F,G]
  ring

end FactorialDyadic
end
end

-- Source module ReciprocalBandRates
section

/-! The power savings and allowance in the upper seventeen four-ninths sieve
bands. The sieve level has exponent just below one twelfth. -/

noncomputable section
open Filter Real
namespace ReciprocalBandRates

def c : ℝ := 4/9
def gamma : ℝ := 1/12-1/1000000

def window (n : ℕ) : ℝ := ⌊(n:ℝ)^c⌋₊

def errors (n : ℕ) (a b : ℝ) : ℝ :=
  (1+log n)^4*((n:ℝ)^(c+2*gamma-a)+(n:ℝ)^(1/3+4*gamma/3)+(n:ℝ)^(2*b-1))

theorem gamma_pos : 0 < gamma := by norm_num [gamma]

/-- A logarithmic factor of degree four is absorbed by any strict gap
in exponents, even after rounding the main scale down to an integer. -/
theorem power_rate {p d ε : ℝ} (hpd : p < d) (hd : 0 < d) (he : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (1+log n)^4*(n:ℝ)^p ≤ ε*(⌊(n:ℝ)^d⌋₊ : ℝ) := by
  have small := (isLittleO_log_rpow_rpow_atTop (4:ℝ) (sub_pos.mpr hpd)).bound
    (show 0 < ε/32 by positivity)
  have hncast : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := (tendsto_log_atTop.comp hncast).eventually_ge_atTop 1
  have hpwr := ((tendsto_rpow_atTop hd).comp hncast).eventually_ge_atTop 2
  filter_upwards [hncast.eventually small,hlog,hpwr,eventually_ge_atTop 1] with n hs hl hp hn
  change 1 ≤ log (n:ℝ) at hl
  change 2 ≤ (n:ℝ)^d at hp
  have np : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have logbound : (log (n:ℝ))^4 ≤ (ε/32)*(n:ℝ)^(d-p) := by
    simpa only [Real.rpow_ofNat,Real.norm_of_nonneg (show 0 ≤ (log (n:ℝ))^4 by positivity),
      Real.norm_of_nonneg (Real.rpow_nonneg np.le _)] using hs
  have logfour : (1+log n)^4 ≤ 16*(log n)^4 := by
    calc _ ≤ (2*log n)^4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
         _ = _ := by ring
  have floorbound : (n:ℝ)^d ≤ 2*(⌊(n:ℝ)^d⌋₊ : ℝ) := by
    linarith [Nat.lt_floor_add_one ((n:ℝ)^d)]
  calc
    _ ≤ (16*((ε/32)*(n:ℝ)^(d-p)))*(n:ℝ)^p := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg np.le _)
      exact logfour.trans (mul_le_mul_of_nonneg_left logbound (by norm_num))
    _ = (ε/2)*(n:ℝ)^d := by
      have eq : (n:ℝ)^(d-p)*(n:ℝ)^p = (n:ℝ)^d := by
        rw [← Real.rpow_add np, sub_add_cancel]
      linear_combination (ε/2)*eq
    _ ≤ ε*(⌊(n:ℝ)^d⌋₊ : ℝ) := by nlinarith [mul_le_mul_of_nonneg_left floorbound he.le]

/-- Each of the three error exponents is strictly below 4/9 throughout
the upper seventeen-band range. -/
theorem rate_gaps_wide (a b : ℝ) (ha : 1/2 ≤ a) (hb : b ≤ 50009/90000) :
    c+2*gamma-a < c ∧ 1/3+4*gamma/3 < c ∧ 2*b-1 < c := by
  unfold c gamma
  constructor
  · linarith
  constructor
  · norm_num
  · linarith

/-- Multiplying the summed dyadic errors by any fixed constant gives
eventually at most ε times the integer window length. -/
theorem eventual_errors_wide (a b C ε : ℝ) (ha : 1/2 ≤ a) (hb : b ≤ 50009/90000)
    (hC : 0 ≤ C) (he : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, C*errors n a b ≤ ε*window n := by
  have hgap := rate_gaps_wide a b ha hb
  have hc : 0<c := by norm_num [c]
  let η := ε/(3*(C+1))
  have hη : 0<η := by dsimp [η]; positivity
  have cap : 3*C*η ≤ ε := by
    dsimp only [η]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  filter_upwards [power_rate hgap.1 hc hη,power_rate hgap.2.1 hc hη,power_rate hgap.2.2 hc hη]
    with n h₁ h₂ h₃
  have hwindow : 0 ≤ window n := Nat.cast_nonneg _
  change (1+log n)^4*(n:ℝ)^_ ≤ η*window n at h₁ h₂ h₃
  have together : errors n a b ≤ 3*η*window n := by
    dsimp only [errors]
    simp only [mul_add]
    linarith only [h₁,h₂,h₃]
  calc _ ≤ C*(3*η*window n) := mul_le_mul_of_nonneg_left together hC
       _ = (3*C*η)*window n := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right cap hwindow

theorem rate_gaps (a b : ℝ) (ha : 29/54 ≤ a) (hb : b ≤ 50009/90000) :
    c+2*gamma-a < c ∧ 1/3+4*gamma/3 < c ∧ 2*b-1 < c :=
  rate_gaps_wide a b (by linarith) hb

theorem eventual_errors (a b C ε : ℝ) (ha : 29/54 ≤ a) (hb : b ≤ 50009/90000)
    (hC : 0 ≤ C) (he : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, C*errors n a b ≤ ε*window n :=
  eventual_errors_wide a b C ε (by linarith) hb hC he

/-- The real endpoint and the floor in the sieve level leave the
expected main coefficient for the complete band. -/
theorem floor_sieve_main (n : ℕ) (hn : 2 ≤ n) (a b : ℝ) (hab : a ≤ b) :
    log ((n:ℝ)^b/(n:ℝ)^a) / log ((⌊(n:ℝ)^gamma⌋₊ : ℝ)+1) ≤ (b-a)/gamma := by
  have nr : 1 < (n:ℝ) := by exact_mod_cast (show 1 < n by omega)
  have np : 0 < (n:ℝ) := by linarith
  have lp := Real.log_pos nr
  have flo := Nat.lt_floor_add_one ((n:ℝ)^gamma)
  have logfloor := Real.log_le_log (Real.rpow_pos_of_pos np gamma) flo.le
  rw [Real.log_rpow np] at logfloor
  have gp := gamma_pos
  have prod := mul_pos gp lp
  have pos : 0 < log ((⌊(n:ℝ)^gamma⌋₊ : ℝ)+1) := prod.trans_le logfloor
  rw [log_div (Real.rpow_pos_of_pos np _).ne' (Real.rpow_pos_of_pos np _).ne',
      Real.log_rpow np,Real.log_rpow np,div_le_div_iff₀ pos gp]
  nlinarith [mul_le_mul_of_nonneg_left logfloor (sub_nonneg.mpr hab)]

/-- Exact coefficient surplus from choosing a level with a strict power saving. -/
theorem reciprocal_surplus : 1/gamma-12 = 36/249997 := by norm_num [gamma]

/-- The loss from reducing the level exponent from 1/12 to gamma uses
less than half the project's additive band allowance. -/
theorem allowance_margin (w : ℝ) (hw : w ≤ 1/500) :
    w/gamma + 1/2000000 ≤ 12*w + 1/1000000 := by
  norm_num [gamma]
  linarith

/-- An asymptotic block estimate with the three explicit errors gives the
project's exact band allowance at every sufficiently large integer start. -/
theorem band_from_errors (T : ℕ → ℝ) (a b C : ℝ) (ha : 29/54 ≤ a) (hb : b ≤ 50009/90000)
    (hw : b-a ≤ 1/500) (hC : 0 ≤ C)
    (bound : ∀ᶠ n : ℕ in atTop, T n ≤ ((b-a)/gamma)*window n + C*errors n a b) :
    ∀ᶠ n : ℕ in atTop, T n ≤ ((b-a)*12+1/1000000)*window n := by
  filter_upwards [bound,eventual_errors a b C (1/2000000) ha hb hC (by norm_num)] with n h₁ h₂
  have m := allowance_margin (b-a) hw
  have ww : 0 ≤ window n := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right m ww]

/-- A band in the middle exponent-pair range ends exactly at the breakpoint,
where its allowance is also 12. Its width fits this wider margin. -/
theorem allowance_margin_wide (w : ℝ) (hw : w ≤ 1/250) :
    w/gamma + 1/4000000 ≤ 12*w + 1/1000000 := by
  norm_num [gamma]
  linarith

theorem band_from_errors_wide (T : ℕ → ℝ) (a b C : ℝ) (ha : 1/2 ≤ a) (hb : b ≤ 50009/90000)
    (hw : b-a ≤ 1/250) (hC : 0 ≤ C)
    (bound : ∀ᶠ n : ℕ in atTop, T n ≤ ((b-a)/gamma)*window n + C*errors n a b) :
    ∀ᶠ n : ℕ in atTop, T n ≤ ((b-a)*12+1/1000000)*window n := by
  filter_upwards [bound,eventual_errors_wide a b C (1/4000000) ha hb hC (by norm_num)] with n h₁ h₂
  have m := allowance_margin_wide (b-a) hw
  have ww : 0 ≤ window n := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right m ww]

end ReciprocalBandRates
end
end

-- Source module ReciprocalBandEnvelope
section

/-! Explicit comparison of the upper sieve-band errors with
three power savings, including the dyadic count and the rounded sieve level. -/
noncomputable section
open Real
namespace ReciprocalBandEnvelope


/-- The floor in the sieve level is nonzero and its square stays within the band. -/
theorem sieve_level_le (n : ℕ) (hn : 2≤n) (a : ℝ) (ha : (1:ℝ)/2 ≤ a) :
    1 ≤ ⌊(n:ℝ)^(1/12-1/1000000:ℝ)⌋₊ ∧ ((⌊(n:ℝ)^(1/12-1/1000000:ℝ)⌋₊ : ℕ):ℝ)^2 ≤ (n:ℝ)^a := by
  have n1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
  have n0 : (0:ℝ) ≤ n := by positivity
  have q1 : 1 ≤ (n:ℝ)^(1/12-1/1000000:ℝ) := Real.one_le_rpow n1 (by norm_num)
  constructor
  · exact Nat.floor_pos.mpr q1
  · calc _ ≤ ((n:ℝ)^(1/12-1/1000000:ℝ))^2 := pow_le_pow_left₀ (by positivity) (Nat.floor_le (by positivity)) _
         _ = (n:ℝ)^(2*(1/12-1/1000000:ℝ)) := by rw [← Real.rpow_mul_natCast n0]; norm_num
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le n1 (by linarith)

/-- A uniform envelope for all three errors over the high-prime range. -/
theorem band_envelope (n : ℕ) (hn : 2≤n) (a b : ℝ) (ha : (1:ℝ)/2 ≤ a)
    (hab : a≤b) (hb : b ≤ 50009/90000) :
    let X : ℝ := n
    let h : ℝ := ⌊X^(4/9:ℝ)⌋₊
    let z : ℝ := ⌊X^(1/12-1/1000000:ℝ)⌋₊
    let u := X^a
    let v := X^b
    4*h*z^2/u + (1+log (v/u)/log 2)*(3150*(X+h)^(1/3:ℝ)*z^(4/3:ℝ))
      + (10720/3)*v^2/X*(1+log z)^3 ≤
    50000*((1+log X)^4*(X^((4/9:ℝ)+2*(1/12-1/1000000:ℝ)-a)+X^(1/3+4*(1/12-1/1000000:ℝ)/3)+X^(2*b-1))) := by
  let X : ℝ := n
  let h : ℝ := ⌊X^(4/9:ℝ)⌋₊
  let z : ℝ := ⌊X^(1/12-1/1000000:ℝ)⌋₊
  let u := X^a
  let v := X^b
  let S := 1+log X
  let A := X^((4/9:ℝ)+2*(1/12-1/1000000:ℝ)-a)
  let B := X^(1/3+4*(1/12-1/1000000:ℝ)/3)
  let C := X^(2*b-1)
  change 4*h*z^2/u + (1+log (v/u)/log 2)*(3150*(X+h)^(1/3:ℝ)*z^(4/3:ℝ))
      + (10720/3)*v^2/X*(1+log z)^3 ≤ 50000*(S^4*(A+B+C))
  have n1 : 1≤X := by dsimp [X]; exact_mod_cast (show 1≤n by omega)
  have xp : 0<X := zero_lt_one.trans_le n1
  have up : 0<u := Real.rpow_pos_of_pos xp _
  have vp : 0<v := Real.rpow_pos_of_pos xp _
  have logp := Real.log_nonneg n1
  have s1 : 1≤S := by dsimp [S]; linarith
  have s0 : 0≤S := zero_le_one.trans s1
  have z1 : 1≤z := by dsimp [z,X]; exact_mod_cast (sieve_level_le n hn a ha).1
  have zp : 0<z := zero_lt_one.trans_le z1
  have hc : h ≤ X^(4/9:ℝ) := Nat.floor_le (by positivity)
  have hγ : z ≤ X^(1/12-1/1000000:ℝ) := Nat.floor_le (by positivity)
  have h0 : 0≤h := Nat.cast_nonneg _
  have hX : h≤X := hc.trans (by simpa using Real.rpow_le_rpow_of_exponent_le n1 (by norm_num : (4/9:ℝ) ≤ 1))
  have zX : z≤X := hγ.trans (by simpa using Real.rpow_le_rpow_of_exponent_le n1 (by norm_num : (1/12-1/1000000:ℝ) ≤ 1))
  have ap : 0≤A := Real.rpow_nonneg xp.le _
  have bp : 0≤B := Real.rpow_nonneg xp.le _
  have cp : 0≤C := Real.rpow_nonneg xp.le _
  have first : 4*h*z^2/u ≤ 4*A := by
    calc _ ≤ 4*X^(4/9:ℝ)*(X^(1/12-1/1000000:ℝ))^2/u := by gcongr
         _ = _ := by
           dsimp [A,u]
           rw [← Real.rpow_mul_natCast xp.le, Real.rpow_sub xp,Real.rpow_add xp]
           ring_nf
  have unitlog : 1/2 ≤ log (2:ℝ) := by
    have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : 0<(2:ℝ))
    norm_num at hl ⊢
    exact hl
  have log2p : 0 < log (2:ℝ) := by linarith
  have count : 1+log (v/u)/log 2 ≤ 2*S := by
    have l : log (v/u) = (b-a)*log X := by
      dsimp [u,v]; rw [Real.log_div vp.ne' up.ne',Real.log_rpow xp,Real.log_rpow xp]; ring
    have uv : b-a ≤ 1 := by linarith
    have d : log (v/u)/log 2 ≤ 2*log X := by
      apply (div_le_iff₀ log2p).mpr
      rw [l]
      nlinarith [mul_le_mul_of_nonneg_right uv logp,
        mul_le_mul_of_nonneg_left unitlog logp]
    dsimp [S]
    linarith
  have root : (X+h)^(1/3:ℝ) ≤ 2*(X^(1/3:ℝ)) := by
    calc _ ≤ (2*X)^(1/3:ℝ) := Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
         _ = (2:ℝ)^(1/3:ℝ)*X^(1/3:ℝ) := Real.mul_rpow (by norm_num) xp.le
         _ ≤ _ := mul_le_mul_of_nonneg_right (by
           simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
             (by norm_num : (1/3:ℝ)≤1)) (by positivity)
  have zpow := Real.rpow_le_rpow zp.le hγ (by norm_num : 0≤(4/3:ℝ))
  have power : 3150*(X+h)^(1/3:ℝ)*z^(4/3:ℝ) ≤ 6300*B := by
    calc _ ≤ 3150*(2*X^(1/3:ℝ))*(X^(1/12-1/1000000:ℝ))^(4/3:ℝ) := by gcongr
         _ = _ := by
           dsimp [B]; rw [← Real.rpow_mul xp.le,Real.rpow_add xp]
           ring_nf
  have middle : (1+log (v/u)/log 2)*(3150*(X+h)^(1/3:ℝ)*z^(4/3:ℝ)) ≤
      12600*S*B := by
    calc _ ≤ (2*S)*(6300*B) := mul_le_mul count power (by positivity) (by positivity)
         _ = _ := by ring
  have scale : v^2/X = C := by
    dsimp [C,v]
    rw [Real.rpow_sub xp,Real.rpow_one,← Real.rpow_mul_natCast xp.le]
    congr 2; ring
  have ceilLog : (1+log z)^3 ≤ S^3 := by
    apply pow_le_pow_left₀ (by linarith [Real.log_nonneg z1]) _ 3
    exact add_le_add le_rfl (Real.log_le_log zp zX)
  have last : (10720/3)*v^2/X*(1+log z)^3 ≤ (10720/3)*S^3*C := by
    rw [mul_div_assoc,scale]
    calc _ ≤ (10720/3)*C*S^3 := mul_le_mul_of_nonneg_left ceilLog (by positivity)
         _ = _ := by ring
  have L1 : 1≤S^4 := one_le_pow₀ s1
  have L2 : S≤S^4 := by simpa using pow_le_pow_right₀ s1 (by decide : 1≤4)
  have L3 : S^3≤S^4 := pow_le_pow_right₀ s1 (by decide)
  have f := mul_le_mul_of_nonneg_right L1 ap
  have m := mul_le_mul_of_nonneg_right L2 bp
  have e := mul_le_mul_of_nonneg_right L3 cp
  nlinarith [mul_nonneg (by positivity : 0≤S^4) ap,
    mul_nonneg (by positivity : 0≤S^4) bp,mul_nonneg (by positivity : 0≤S^4) cp]

end ReciprocalBandEnvelope
end
end

-- Source module PrimeBlockMesh
section

/-! A finite substitute for the limiting integral in the four-ninths sieve.
The 48 bands have fixed endpoints on the logarithmic scale. -/
noncomputable section
open Finset Real
open scoped Classical

namespace PrimeBlockMesh

/-- Equal subdivisions within each of the three exponent-pair ranges. -/
def edge (j : ℕ) : ℚ :=
  if j ≤ 16 then 4/9 + j*(77/162-4/9)/16
  else if j ≤ 32 then 77/162 + ((j-16 : ℕ) : ℚ)*(29/54-77/162)/16
  else 29/54 + ((j-32 : ℕ) : ℚ)*(50009/90000-29/54)/16

/-- An upper allowance per window position for unweighted prime hits in band j.
The additive tolerance absorbs the eventual error in the local sieve estimate. -/
def allowance (j : ℕ) : ℚ :=
  let v := edge (j+1)
  let θ := if j < 16 then (4/7)/(17/42-(5/7)*v)
           else if j < 32 then 1/(19/54-v/2) else 12
  (v-edge j)*θ + 1/1000000

set_option maxRecDepth 4000 in
theorem budget : (4/9 : ℚ) + ∑ j ∈ range 48, edge (j+1)*allowance j < 2499/2500 := by
  decide +kernel

private lemma crossing (f : ℕ → ℝ) (x : ℝ) (h0 : f 0 < x) (k : ℕ) (hk : x ≤ f k) :
    ∃ j < k, f j < x ∧ x ≤ f (j+1) := by
  induction k with
  | zero => exact (not_lt_of_ge hk h0).elim
  | succ k ih =>
    by_cases hend : x ≤ f k
    · obtain ⟨j, hj, lo, hi⟩ := ih hend
      exact ⟨j, by omega, lo, hi⟩
    · exact ⟨k, by omega, lt_of_not_ge hend, hk⟩

/-- The log weight of any set of hits in the complete middle range is bounded
by the finite unweighted counts. S can label a prime together with its position. -/
theorem first_power_mass {α : Type*} (S : Finset α) (p : α → ℕ) (n h : ℕ) (hn : 1 ≤ n)
    (range_hits : ∀ z ∈ S, (n:ℝ)^(4/9:ℝ) < (p z:ℝ) ∧
      (p z:ℝ) ≤ (n:ℝ)^(5/9+1/10000:ℝ))
    (counts : ∀ j < 48,
      ((S.filter (fun z => (n:ℝ)^(edge j : ℝ) < (p z:ℝ) ∧
        (p z:ℝ) ≤ (n:ℝ)^(edge (j+1) : ℝ))).card : ℝ) ≤ (allowance j : ℝ)*h) :
    (∑ z ∈ S, log (p z)) ≤ (5/9-1/2500)*(h:ℝ)*log n := by
  let bin (j : ℕ) := S.filter (fun z => (n:ℝ)^(edge j : ℝ) < (p z:ℝ) ∧
                                      (p z:ℝ) ≤ (n:ℝ)^(edge (j+1) : ℝ))
  let cap (j : ℕ) := (edge (j+1) : ℝ)*log n
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have cap_pos (j : ℕ) : 0 ≤ cap j := by
    have edge_nonneg : 0 ≤ edge (j+1) := by
      unfold edge
      split
      · norm_num
        positivity
      · split <;> norm_num <;> positivity
    exact mul_nonneg (by exact_mod_cast edge_nonneg) (Real.log_natCast_nonneg n)
  have cover (z : α) (hz : z ∈ S) :
      ∃ j < 48, z ∈ bin j ∧ log (p z) ≤ cap j := by
    obtain ⟨hlo,hhi⟩ := range_hits z hz
    let f (j : ℕ) := (n:ℝ)^(edge j : ℝ)
    have hzero : f 0 < (p z:ℝ) := by simpa [f,edge] using hlo
    have hlast : (p z:ℝ) ≤ f 48 := by norm_num [f,edge]; convert hhi using 2 <;> norm_num
    obtain ⟨j, hj, lo, hi⟩ := crossing f (p z) hzero 48 hlast
    have pp : (0:ℝ) < p z := (Real.rpow_pos_of_pos hn0 _).trans lo
    refine ⟨j,hj,mem_filter.mpr ⟨hz, lo, hi⟩, ?_⟩
    simpa only [f, cap, log_rpow hn0] using Real.log_le_log pp hi
  have point (z : α) (hz : z ∈ S) : log (p z) ≤ ∑ j ∈ range 48, if z ∈ bin j then cap j else 0 := by
    obtain ⟨j,hj,hmem,hle⟩ := cover z hz
    apply hle.trans
    have hs := Finset.single_le_sum (f := fun j => if z ∈ bin j then cap j else 0)
      (fun j (_ : j ∈ range 48) => by split <;> first | exact cap_pos j | exact le_rfl) (mem_range.mpr hj)
    simpa only [if_pos hmem] using hs
  calc
    (∑ z ∈ S, log (p z)) ≤ _ := sum_le_sum point
    _ = ∑ j ∈ range 48, ((bin j).card : ℝ)*cap j := by
      rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      rw [← sum_filter]
      have filt : S.filter (fun z => z ∈ bin j) = bin j := by
        ext z
        simp [bin]
      simp [filt]
    _ ≤ ∑ j ∈ range 48, ((allowance j : ℝ)*h)*cap j := by
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (counts j (mem_range.mp hj)) (cap_pos j)
    _ = ((∑ j ∈ range 48, edge (j+1)*allowance j : ℚ) : ℝ)*h*log n := by
      push_cast
      simp only [sum_mul]
      apply sum_congr rfl
      intro j _
      dsimp [cap]
      ring
    _ ≤ _ := by
      have H := budget
      have R : (∑ j ∈ range 48, edge (j+1)*allowance j : ℚ) ≤ 5/9-1/2500 := by linarith
      have R' : ((∑ j ∈ range 48, edge (j+1)*allowance j : ℚ):ℝ) ≤ 5/9-1/2500 := by
        have v := (Rat.cast_le (K := ℝ)).mpr R
        norm_num at v ⊢
        exact v
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right R' (Nat.cast_nonneg _))
        (Real.log_natCast_nonneg _)

end PrimeBlockMesh
end
end

-- Source module ReciprocalUpperBands
section

/-! The upper seventeen of the 48 prime-hit bounds in the four-ninths
factorial-window reduction. These are the bands assigned exponent pair
(1/2,1/2) by Erdős, Graham, Ivić and Pomerance, Lemma 3, together
with the preceding band whose right-endpoint allowance is also twelve. -/
noncomputable section
open Finset Real Filter
open scoped Classical
namespace FactorialUpperBands
open ReciprocalBandRates FactorialFourier PrimeBlockMesh

def primeHits (n h : ℕ) (u v : ℝ) : ℝ :=
  ∑ p ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime, (FactorialSieve.multiplicity n h p:ℝ)

/-- Any fixed band in the upper range with width at most 1/250 satisfies
the required asymptotic hit-count estimate with coefficient twelve. -/
theorem prime_hits_eventually (a b : ℝ) (ha : 1/2 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 50009/90000) (hw : b-a ≤ 1/250) :
    ∀ᶠ n : ℕ in atTop,
      primeHits n ⌊(n:ℝ)^c⌋₊ ((n:ℝ)^a) ((n:ℝ)^b) ≤ ((b-a)*12+1/1000000)*window n := by
  apply band_from_errors_wide _ a b 50000 ha hb hw (by norm_num)
  filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
  let z := ⌊(n:ℝ)^gamma⌋₊
  let h := ⌊(n:ℝ)^c⌋₊
  let u := (n:ℝ)^a
  let v := (n:ℝ)^b
  have level := ReciprocalBandEnvelope.sieve_level_le n hn a ha
  have huv : u ≤ v := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤n by omega)) hab
  have pos : 0<n := by omega
  have block := FactorialDyadic.prime_band_sqrt_of_block n h z u v pos level.1 level.2 huv
    (fun r s => prime_block_sqrt n h z r s pos level.1)
  have env := ReciprocalBandEnvelope.band_envelope n hn a b ha hab hb
  have mainB := mul_le_mul_of_nonneg_left (floor_sieve_main n hn a b hab) (Nat.cast_nonneg h)
  change (h:ℝ)*(log (v/u)/log ((z:ℝ)+1)) ≤ h*((b-a)/gamma) at mainB
  change primeHits n h u v ≤ _
  change primeHits n h u v ≤ _ at block
  change 4*h*(z:ℝ)^2/u +
    (1+log (v/u)/log 2)*(3150*((n:ℝ)+h)^(1/3:ℝ)*(z:ℝ)^(4/3:ℝ)) +
    (10720/3)*v^2/(n:ℝ)*(1+log z)^3 ≤ 50000*errors n a b at env
  change primeHits n h u v ≤ ((b-a)/gamma)*h+50000*errors n a b
  rw [← mul_div_assoc] at mainB
  rw [mul_comm (h:ℝ) ((b-a)/gamma)] at mainB
  linarith only [block,mainB,env]

def bandSet (n j : ℕ) : Finset ((_:ℕ) × ℕ) :=
  let h := ⌊(n:ℝ)^(4/9:ℝ)⌋₊
  let S := (range h).sigma (fun i => (n+i+1).primeFactors.filter (fun p : ℕ =>
    (n:ℝ)^(4/9:ℝ) < p ∧ (p:ℝ) ≤ (n:ℝ)^(5/9+1/10000:ℝ)))
  S.filter (fun z => (n:ℝ)^(edge j:ℝ) < (z.2:ℝ) ∧ (z.2:ℝ) ≤ (n:ℝ)^(edge (j+1):ℝ))

private theorem upper_params : ∀ j ∈ Ico 31 48,
    (1/2:ℝ) ≤ (edge j:ℝ) ∧ (edge j:ℝ) ≤ (edge (j+1):ℝ) ∧ (edge (j+1):ℝ) ≤ 50009/90000 ∧
      (edge (j+1):ℝ)-(edge j:ℝ) ≤ 1/250 ∧
      (allowance j:ℝ) = ((edge (j+1):ℝ)-(edge j:ℝ))*12+1/1000000 := by
  intro j hj
  obtain ⟨l,r⟩ := mem_Ico.mp hj
  interval_cases j <;> norm_num [edge,allowance]

/-- The same finite set of pairs and rational allowances as in H1 of the
48-band reduction, for every j from 31 through 47 simultaneously. -/
theorem upper_seventeen :
    ∀ᶠ n : ℕ in atTop, ∀ j ∈ Ico 31 48,
      ((bandSet n j).card:ℝ) ≤ (allowance j:ℝ)*⌊(n:ℝ)^(4/9:ℝ)⌋₊ := by
  apply (eventually_all_finset _).mpr
  intro j hj
  obtain ⟨ha,hab,hb,hw,teq⟩ := upper_params j hj
  let a : ℝ := edge j
  let b : ℝ := edge (j+1)
  have B := prime_hits_eventually a b ha hab hb hw
  filter_upwards [B] with n count
  have bridge := hit_card_le n ⌊(n:ℝ)^(4/9:ℝ)⌋₊ ((n:ℝ)^a) ((n:ℝ)^b)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) (bandSet n j) (by
      intro z hz
      obtain ⟨hs,hband⟩ := mem_filter.mp hz
      obtain ⟨hi,hp⟩ := mem_sigma.mp hs
      have prime := (mem_filter.mp hp).1
      exact ⟨mem_range.mp hi,Nat.prime_of_mem_primeFactors prime,
        Nat.dvd_of_mem_primeFactors prime,hband⟩)
  apply bridge.trans
  have eqA : (allowance j:ℝ) = (b-a)*12+1/1000000 := teq
  rw [eqA]
  exact count

end FactorialUpperBands
end
end

-- Source module ReciprocalAssembly
section

/-! Match the 48 prime-hit inequalities to the exact hypothesis of the
four-ninths reduction, including its open and closed endpoints. -/
noncomputable section
open Finset Filter
open FactorialUpperBands PrimeBlockMesh
namespace FactorialFullBands

theorem of_lower_thirty_one
    (lower : ∀ᶠ n : ℕ in atTop, ∀ j ∈ range 31,
      ((bandSet n j).card : ℝ) ≤ (allowance j : ℝ)*⌊(n:ℝ)^(4/9:ℝ)⌋₊) :
    OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2.H1 := by
  filter_upwards [lower,upper_seventeen] with n low high
  change ∀ j < 48, ((bandSet n j).card:ℝ) ≤ (allowance j:ℝ)*⌊(n:ℝ)^(4/9:ℝ)⌋₊
  intro j hj
  by_cases h : j<31
  · exact low j (mem_range.mpr h)
  · exact high j (mem_Ico.mpr ⟨by omega,hj⟩)

end FactorialFullBands
end
end

-- Source module ReciprocalLowerBandInput
section

noncomputable section
open Real
namespace FactorialLowerBands

/-- A full-band Selberg bound after summing scale-dependent local sieves. -/
def BandBound (p q s : ℝ) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (n h z : ℕ) (u v : ℝ), 0<n → 1≤z → (z:ℝ)^2≤u → u≤v →
    FactorialUpperBands.primeHits n h u v ≤
      (h:ℝ)*log (v/u)/log ((z:ℝ)+1) + 4*h*(z:ℝ)^2/u +
      C*(1+log (v/u)/log 2)*((n:ℝ)+h)^p*v^q*(z:ℝ)^(2*(1-s)) +
      C*(v^2/(n:ℝ))*(1+log z)^3

end FactorialLowerBands
end
end

-- Source module ReciprocalGeneralDyadic
section

/-! Pass from scale-dependent single-modulus estimates to a prime-count bound
on an arbitrary band. The constant is independent of the scale and the endpoints. -/
noncomputable section
open Finset Real
namespace FactorialDyadic

/-- A reciprocal sawtooth estimate on every factor-two interval and single modulus. -/
def UniformSaw (p q s : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x t : ℕ, 0 < x → 0 < t → ∀ u v : ℝ,
    (t:ℝ) ≤ u → u ≤ v → v ≤ 2*u → |FactorialSieve.remainder u v x t| ≤ 
      C*((x:ℝ)^p*u^q*(t:ℝ)^(-s)+u^2/((x:ℝ)*t))

/-- A single constant controls both dyadic error terms throughout the band. -/
theorem prime_band_from_saw (p q s : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hs : 0 ≤ s) (hs1 : s < 1)
    (local_est : UniformSaw p q s) : FactorialLowerBands.BandBound p q s := by
  obtain ⟨C,hC,local_est⟩ := local_est
  let M := (1+1/(1-s))/(1-s)^2
  have ds : 0 < 1-s := sub_pos.mpr hs1
  have m0 : 0 ≤ M := by dsimp [M]; positivity
  let K := max 1 (max (2*C*M) ((8/3)*C))
  refine ⟨K,le_max_left ..,?_⟩
  intro n h z u v hn hz zu uv
  have nz : 0 < (n:ℝ) := by exact_mod_cast hn
  have zz : 0 < (z:ℝ) := by exact_mod_cast hz
  have up : 0 < u := (sq_pos_of_pos zz).trans_le zu
  have vp := up.trans_le uv
  let X : ℝ := (n:ℝ)+h
  let A := C*X^p*v^q
  let B := C/(n:ℝ)
  have xp : 0 < X := by dsimp [X]; positivity
  have ap : 0 ≤ A := by dsimp [A]; positivity
  have bp : 0 ≤ B := by dsimp [B]; positivity
  have est (a b : ℝ) (ha : u ≤ a) (ab : a ≤ b) (bv : b ≤ v) (short : b ≤ 2*a) :
      ∀ x ∈ ({n,n+h} : Finset ℕ), ∀ t : ℕ, 1 ≤ t → t ≤ z^2 →
      |FactorialSieve.remainder a b x t| ≤ A*(t:ℝ)^(-s)+B*a^2/t := by
    intro x xmem t ht tz
    have nx : n ≤ x ∧ x ≤ n+h := by
      simp only [mem_insert,mem_singleton] at xmem
      rcases xmem with e|e <;> subst x <;> omega
    have tp : 0 < (t:ℝ) := by exact_mod_cast ht
    have l := local_est x t (hn.trans_le nx.1) ht a b
      ((by exact_mod_cast tz : (t:ℝ) ≤ (z:ℝ)^2).trans (zu.trans ha)) ab short
    apply l.trans
    have boundx : (x:ℝ) ≤ X := by dsimp [X]; exact_mod_cast nx.2
    have y := Real.rpow_le_rpow (Nat.cast_nonneg x) boundx hp
    have w := Real.rpow_le_rpow (up.le.trans ha) (ab.trans bv) hq
    have aa := mul_le_mul y w (Real.rpow_nonneg (up.le.trans ha) q) (Real.rpow_nonneg xp.le p)
    have xx : (n:ℝ) ≤ x := by exact_mod_cast nx.1
    have dd := div_le_div_of_nonneg_left (sq_nonneg a) (mul_pos nz tp)
      (mul_le_mul_of_nonneg_right xx tp.le)
    calc
      _ ≤ C*(X^p*v^q*(t:ℝ)^(-s)+a^2/((n:ℝ)*t)) := by
        exact mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_right aa (Real.rpow_nonneg tp.le _)) dd) hC.le
      _ = _ := by dsimp only [A,B]; ring
  have raw := prime_band_from_local n h z hz zu uv ap bp hs hs1 est
  apply raw.trans
  have K₁ : 2*C*M ≤ K := (le_max_left ..).trans (le_max_right ..)
  have K₂ : (8/3)*C ≤ K := (le_max_right ..).trans (le_max_right ..)
  let J := 1+log (v/u)/log 2
  have j0 : 0 ≤ J := by
    have one : 1 ≤ v/u := (one_le_div up).mpr uv
    have lg := log_nonneg one
    let two := log_pos (show (1:ℝ) < 2 by norm_num)
    dsimp [J]
    exact add_nonneg zero_le_one (div_nonneg lg two.le)
  have lz := Real.log_natCast_nonneg z
  have mid : J*(2*A*(M*(z:ℝ)^(2*(1-s)))) ≤ K*J*X^p*v^q*(z:ℝ)^(2*(1-s)) := by
    calc _ = (2*C*M)*(J*X^p*v^q*(z:ℝ)^(2*(1-s))) := by dsimp only [A]; ring
         _ ≤ K*(J*X^p*v^q*(z:ℝ)^(2*(1-s))) := mul_le_mul_of_nonneg_right K₁ (by positivity)
         _ = _ := by ring
  have last : (8/3)*B*(1+log z)^3*v^2 ≤ K*(v^2/(n:ℝ))*(1+log z)^3 := by
    calc _ = ((8/3)*C)*((v^2/(n:ℝ))*(1+log z)^3) := by dsimp only [B]; ring
         _ ≤ K*((v^2/(n:ℝ))*(1+log z)^3) := mul_le_mul_of_nonneg_right K₂ (by positivity)
         _ = _ := by ring
  exact add_le_add (add_le_add le_rfl mid) last

end FactorialDyadic
end
end

-- Source module ReciprocalAWindow
section

/-! Passage from an exponent pair for a real-base reciprocal phase to
the positive-frequency bound on a sieve interval. -/
noncomputable section
open Finset Real
namespace FactorialFourier

private theorem complex_multiples (u v : ℝ) (t : ℕ) (ht : 0 < t) (f : ℕ → ℂ) :
    (∑ m ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·), f m) =
      ∑ q ∈ Ioc ⌊u/(t:ℝ)⌋₊ ⌊v/(t:ℝ)⌋₊, f (q*t) := by
  rw [sum_filter]
  apply Complex.ext
  · simp only [Complex.re_sum,apply_ite Complex.re, Complex.zero_re]
    exact FactorialRounding.sum_multiples u v t ht (fun j => (f j).re)
  · simp only [Complex.im_sum,apply_ite Complex.im, Complex.zero_im]
    exact FactorialRounding.sum_multiples u v t ht (fun j => (f j).im)

/-- An exponential-sum bound for positive frequencies on the exact set
of multiples. The power exponents satisfy 0 ≤ l−2k ≤ 1 for both A-pairs. -/
theorem window_exponential_of_pair {k l C u v : ℝ} {x t j : ℕ}
    (block : ∀ {B Y : ℝ} (N : ℕ), 1 ≤ B → 0 < Y → (N:ℝ) ≤ 2*B+1 →
      ‖∑ i ∈ range N, ReciprocalFirstDerivative.wave (Y/(B+i))‖ ≤
        C*(B^l*(Y/B^2)^k+B^2/Y))
    (hC : 0 ≤ C) (hlo : 0 ≤ l-2*k) (hhi : l-2*k ≤ 1)
    (hx : 0 < x) (ht : 0 < t) (hj : 0 < j) (htu : (t:ℝ) ≤ u) (huv : u ≤ v)
    (hv : v ≤ 3*u) :
    ‖∑ m ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·), Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*x/m)‖ ≤
      ((2*C)*(x:ℝ)^k*u^(l-2*k)*(t:ℝ)^(k-l))*(j:ℝ)^k + ((4*C)*u^2/((x:ℝ)*t))/j := by
  let M := ⌊u/(t:ℝ)⌋₊+1
  let b := ⌊v/(t:ℝ)⌋₊
  let N := b+1-M
  let Y := (j:ℝ)*x/t
  have tp : (0:ℝ) < t := by exact_mod_cast ht
  have xp : (0:ℝ) < x := by exact_mod_cast hx
  have jp : (0:ℝ) < j := by exact_mod_cast hj
  have up := tp.trans_le htu
  have yp : 0 < Y := by dsimp [Y]; positivity
  have mn : 1 ≤ M := Nat.succ_le_succ (Nat.zero_le _)
  have mp : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have ml : u/t ≤ (M:ℝ) := by simpa only [M,Nat.cast_add,Nat.cast_one] using (Nat.lt_floor_add_one (u/(t:ℝ))).le
  have mu : (M:ℝ) ≤ 2*(u/t) := by
    simp only [M,Nat.cast_add,Nat.cast_one]
    linarith [Nat.floor_le (div_nonneg up.le tp.le), (one_le_div tp).mpr htu]
  have b3 : b ≤ 3*M := by
    have h₁ : (b:ℝ) ≤ v/t := Nat.floor_le (div_nonneg (up.le.trans huv) tp.le)
    have h₂ : v/t ≤ 3*(u/t) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hv tp.le
    exact_mod_cast (show (b:ℝ) ≤ 3*(M:ℝ) by linarith)
  have len : (N:ℝ) ≤ 2*(M:ℝ)+1 := by
    exact_mod_cast (show N ≤ 2*M+1 by dsimp [N]; omega)
  have eq (a : ℕ) :
      Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*x/(((M+a)*t:ℕ):ℂ)) =
        ReciprocalFirstDerivative.wave (Y/((M:ℝ)+a)) := by
    unfold ReciprocalFirstDerivative.wave
    congr 1
    dsimp [Y]; push_cast; simp only [div_eq_mul_inv,mul_inv_rev]; ring
  rw [complex_multiples u v t ht,← Icc_succ_left_eq_Ioc,← Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range]
  change ‖∑ a ∈ range N, Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*x/(((M+a)*t:ℕ):ℂ))‖ ≤ _
  simp only [eq]
  apply (block N (by exact_mod_cast mn : (1:ℝ) ≤ M) yp len).trans
  have hir : (M:ℝ)^2/Y ≤ (4*u^2/((x:ℝ)*t))/j := by
    apply (div_le_div_of_nonneg_right (pow_le_pow_left₀ mp.le mu 2) yp.le).trans_eq
    dsimp [Y]; field_simp; ring
  have id : (M:ℝ)^l*(Y/(M:ℝ)^2)^k = Y^k*(M:ℝ)^(l-2*k) := by
    rw [Real.div_rpow yp.le (sq_nonneg _),← Real.rpow_natCast_mul mp.le 2 k,Real.rpow_sub mp]
    norm_num
    ring
  have pwr : (M:ℝ)^(l-2*k) ≤ 2*(u/t)^(l-2*k) := by
    apply (Real.rpow_le_rpow mp.le mu hlo).trans
    rw [Real.mul_rpow zero_le_two (by positivity : 0 ≤ u/(t:ℝ))]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simpa using (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hhi)
  have powers : Y^k * (2*(u/t)^(l-2*k)) =
      2*(x:ℝ)^k*u^(l-2*k)*(t:ℝ)^(k-l)*(j:ℝ)^k := by
    dsimp only [Y]
    rw [Real.div_rpow (mul_pos jp xp).le tp.le,Real.mul_rpow jp.le xp.le,
        Real.div_rpow up.le tp.le]
    have den : (t:ℝ)^k*(t:ℝ)^(l-2*k) = (t:ℝ)^(l-k) := by
      rw [← Real.rpow_add tp]
      congr 1
      ring
    rw [show k-l = -(l-k) by ring,Real.rpow_neg tp.le,← den]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have main : (M:ℝ)^l*(Y/(M:ℝ)^2)^k ≤
      2*(x:ℝ)^k*u^(l-2*k)*(t:ℝ)^(k-l)*(j:ℝ)^k := by
    rw [id,← powers]
    exact mul_le_mul_of_nonneg_left pwr (by positivity)
  apply (mul_le_mul_of_nonneg_left (add_le_add main hir) hC).trans_eq
  ring

end FactorialFourier
end
end

-- Source module ReciprocalPowerCutoff
section

/-! Balancing the integer Fourier cutoff for every exponent 0<k<1.
The coefficient retains its full dependence on k, including the two
exponents 1/6 and 1/14 in the short factorial interval. -/

noncomputable section
namespace FactorialFourier

/-- Passing from an oscillatory bound of size E j^k + F/j to a centered
sawtooth sum trades the frequency power k for k/(1+k). -/
theorem optimize_power {R N E F C k : ℝ} (hN : 0 ≤ N) (hE : 0 ≤ E)
    (hF : 0 ≤ F) (hC : 0 ≤ C) (hk : 0 < k)
    (trivial : R ≤ N/2)
    (budget : ∀ H : ℕ, 1 ≤ H → R ≤ N/(2*(H:ℝ))+C*E*(H:ℝ)^k+F) :
    R ≤ (1+C)*(N^(k/(1+k))*E^(1/(1+k)))+F := by
  let p := 1/(1+k)
  let q := k/(1+k)
  let P := N^q*E^p
  have pp : 0<p := by dsimp [p]; positivity
  have qp : 0<q := by dsimp [q]; positivity
  have ps : q+p=1 := by dsimp [p,q]; field_simp; ring
  have pk : p*k=q := by dsimp [p,q]; ring
  have Pn : 0 ≤ P := by dsimp [P]; positivity
  change R ≤ (1+C)*P+F
  by_cases e : E=0
  · subst E
    have eq : P=0 := by dsimp [P]; rw [Real.zero_rpow pp.ne',mul_zero]
    rw [eq,mul_zero,zero_add]
    by_contra! bad
    have dp := sub_pos.mpr bad
    obtain ⟨H,high⟩ := exists_nat_gt (max 1 (N/(R-F)))
    have one := (le_max_left (1:ℝ) (N/(R-F))).trans_lt high
    have hp : (1:ℝ) ≤ H := one.le
    have h := budget H (by exact_mod_cast hp)
    simp only [mul_zero,zero_mul,add_zero] at h
    have s := (div_lt_iff₀ dp).mp ((le_max_right (1:ℝ) (N/(R-F))).trans_lt high)
    have top : N/(2*(H:ℝ)) < R-F := by
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith [mul_pos (show 0<(H:ℝ) by linarith) dp]
    linarith
  have ep : 0<E := lt_of_le_of_ne hE (Ne.symm e)
  by_cases small : N≤E
  · have nle : N≤P := by
      calc N = N^q*N^p := by rw [← Real.rpow_add_of_nonneg hN qp.le pp.le,ps,Real.rpow_one]
           _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN small pp.le) (by positivity)
    nlinarith only [nle,trivial,hN,hF,mul_nonneg hC Pn]
  have np : 0<N := ep.trans (lt_of_not_ge small)
  let a := (N/E)^p
  have a1 : 1 ≤ a := Real.one_le_rpow ((one_le_div ep).mpr (le_of_not_ge small)) pp.le
  have ea : E*a^k=P := by
    dsimp only [a,P]
    rw [← Real.rpow_mul (div_nonneg hN hE),pk,Real.div_rpow hN hE]
    have ef : E^q*E^p=E := by rw [← Real.rpow_add ep,ps,Real.rpow_one]
    have eq := (Real.rpow_pos_of_pos ep q).ne'
    field_simp
    linear_combination -ef
  have pa : P*a=N := by
    dsimp only [a,P]
    rw [Real.div_rpow hN hE]
    have nf : N^q*N^p=N := by rw [← Real.rpow_add np,ps,Real.rpow_one]
    have epow := (Real.rpow_pos_of_pos ep p).ne'
    field_simp
    linear_combination nf
  let H := ⌊a⌋₊
  have hH : 1 ≤ H := Nat.floor_pos.mpr a1
  have hHr : (1:ℝ) ≤ H := by exact_mod_cast hH
  have hpos : (0:ℝ) < H := by linarith
  have lo : (H:ℝ)≤a := Nat.floor_le (zero_le_one.trans a1)
  have hi : a≤2*(H:ℝ) := by linarith [Nat.lt_floor_add_one a]
  have inv : N/(2*(H:ℝ)) ≤ P := (div_le_iff₀ (by positivity)).mpr
    (by rw [← pa]; exact mul_le_mul_of_nonneg_left hi Pn)
  have growth : E*(H:ℝ)^k ≤ P := ea ▸ mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hpos.le lo hk.le) hE
  have ce := mul_le_mul_of_nonneg_left growth hC
  have h := budget H hH
  nlinarith only [h,ce,inv]

end FactorialFourier
end
end

-- Source module ReciprocalPowerRescale
section

/-! Rescale a cutoff-optimized exponential-sum estimate on reciprocal multiples. -/
noncomputable section
open Real
namespace FactorialFourier

/-- The length of the grid and the size of the exponential coefficient
combine to give the modulus exponent −l/(1+k). -/
theorem rescale_local_power {N E K x u t k l : ℝ} (hN : 0≤N) (hE : 0≤E)
    (hK : 1≤K) (hx : 0<x) (hu : 0<u) (ht : 0<t) (hk : 0≤k)
    (count : N ≤ 3*u/t) (amplitude : E ≤ K*x^k*u^(l-2*k)*t^(k-l)) :
    N^(k/(1+k))*E^(1/(1+k)) ≤
      (3*K)*x^(k/(1+k))*u^((l-k)/(1+k))*t^(-l/(1+k)) := by
  let a := k/(1+k)
  let b := 1/(1+k)
  have den : 0<1+k := by linarith
  have a0 : 0≤a := div_nonneg hk den.le
  have b0 : 0≤b := div_nonneg zero_le_one den.le
  have a1 : a≤1 := (div_le_one den).mpr (by linarith)
  have b1 : b≤1 := (div_le_one den).mpr (by linarith)
  have K0 : 0≤K := zero_le_one.trans hK
  have a3 : (3:ℝ)^a ≤ 3 := by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3) a1
  have bK : K^b ≤ K := by simpa using Real.rpow_le_rpow_of_exponent_le hK b1
  have r1 : k*b=a := by dsimp [a,b]; ring
  have r2 : a+(l-2*k)*b=(l-k)/(1+k) := by dsimp [a,b]; ring
  have r3 : -a+(k-l)*b = -l/(1+k) := by dsimp [a,b]; ring
  have tt : (t^a)⁻¹ = t^(-a) := (Real.rpow_neg ht.le a).symm
  calc
    N^a*E^b ≤ (3*u/t)^a*(K*x^k*u^(l-2*k)*t^(k-l))^b := by gcongr
    _ = (3^a*K^b)*x^a*u^((l-k)/(1+k))*t^(-l/(1+k)) := by
      rw [Real.div_rpow (by positivity) ht.le,Real.mul_rpow (by norm_num) hu.le,
        Real.mul_rpow (by positivity) (Real.rpow_nonneg ht.le _),
        Real.mul_rpow (by positivity) (Real.rpow_nonneg hu.le _),Real.mul_rpow K0 (Real.rpow_nonneg hx.le _),
        ← Real.rpow_mul hx.le,← Real.rpow_mul hu.le,← Real.rpow_mul ht.le,
        r1,← r2,← r3,Real.rpow_add hu,Real.rpow_add ht,div_eq_mul_inv,tt]
      ring
    _ ≤ _ := by gcongr

end FactorialFourier
end
end

-- Source module ReciprocalDifferencing
section

/-! A finite van der Corput differencing inequality. Shift averaging on the zero
extension preserves the endpoints of every correlation, including empty overlaps.
The normalization is the one used for the A-process of exponent pairs.
See S. W. Graham and G. Kolesnik, *Van der Corput's Method of Exponential Sums*,
Chapter 2. -/

noncomputable section
open Finset
open scoped ComplexConjugate

namespace FactorialDifferencing

/-- The correlation at lag d in a sequence of length N. -/
def corr (f : ℕ → ℂ) (N d : ℕ) : ℂ :=
  ∑ j ∈ range (N-d), f (j+d) * conj (f j)

private def shift (f : ℕ → ℂ) (N h x : ℕ) : ℂ :=
  if x ∈ Ico h (h+N) then f (x-h) else 0

private theorem sum_shift (f : ℕ → ℂ) (N h M : ℕ) (end_le : h+N ≤ M) :
    ∑ x ∈ range M, shift f N h x = ∑ j ∈ range N, f j := by
  have sub : Ico h (h+N) ⊆ range M := by
    intro x hx
    exact mem_range.mpr ((mem_Ico.mp hx).2.trans_le end_le)
  calc
    _ = ∑ x ∈ Ico h (h+N), shift f N h x := by
      symm
      exact sum_subset sub (by intro x _ hx; simp [shift,hx])
    _ = ∑ x ∈ Ico h (h+N), f (x-h) :=
      sum_congr rfl (by intro x hx; simp [shift,hx])
    _ = _ := by rw [sum_Ico_eq_sum_range]; simp

private theorem shift_mul (f : ℕ → ℂ) (N k h x : ℕ) (hk : k ≤ h) :
    shift f N k x * conj (shift f N h x) =
      shift (fun j => f (j+(h-k))*conj (f j)) (N-(h-k)) h x := by
  by_cases h₁ : x ∈ Ico k (k+N) <;> by_cases h₂ : x ∈ Ico h (h+N)
  · have h₃ : x ∈ Ico h (h+(N-(h-k))) := by
      simp only [mem_Ico] at *; omega
    simp only [shift, if_pos h₁, if_pos h₂, if_pos h₃]
    rw [show x-h+(h-k)=x-k by have := (mem_Ico.mp h₂).1; omega]
  · have h₃ : x ∉ Ico h (h+(N-(h-k))) := by
      simp only [mem_Ico] at *; omega
    simp [shift,h₂,h₃]
  · have h₃ : x ∉ Ico h (h+(N-(h-k))) := by
      simp only [mem_Ico] at *; omega
    simp [shift,h₁,h₃]
  · have h₃ : x ∉ Ico h (h+(N-(h-k))) := by
      simp only [mem_Ico] at *; omega
    simp [shift,h₂,h₃]

private theorem shift_overlap (f : ℕ → ℂ) (N k h M : ℕ)
    (hk : k ≤ h) (hM : h+N ≤ M) :
    ∑ x ∈ range M, shift f N k x * conj (shift f N h x) = corr f N (h-k) := by
  simp_rw [shift_mul f N k h _ hk]
  exact sum_shift _ _ _ _ (by omega)

private theorem norm_square_expand (g : ℕ → ℂ) (H : ℕ) :
    ‖∑ h ∈ range H, g h‖^2 =
      (∑ h ∈ range H, ‖g h‖^2) +
        2*∑ h ∈ range H, ∑ k ∈ range h, (g k * conj (g h)).re := by
  induction H with
  | zero => simp
  | succ H ih =>
    have pair (z w : ℂ) : ‖z+w‖^2 = ‖z‖^2+‖w‖^2+2*(z*conj w).re := by
      simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re]
      ring
    rw [sum_range_succ, pair, ih, sum_range_succ (f := fun h => ‖g h‖^2),
      sum_range_succ (f := fun h => ∑ k ∈ range h, (g k * conj (g h)).re)]
    rw [sum_mul, Complex.re_sum]
    ring

private theorem square_cs (g : ℕ → ℂ) (M : ℕ) :
    ‖∑ x ∈ range M, g x‖^2 ≤ (M:ℝ) * ∑ x ∈ range M, ‖g x‖^2 := by
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le (range M) g) 2).trans
  simpa using sq_sum_le_card_mul_sum_sq (s := range M) (f := fun x => ‖g x‖)

private theorem zero_corr (f : ℕ → ℂ) (N : ℕ) :
    (corr f N 0).re = ∑ j ∈ range N, ‖f j‖^2 := by
  simp only [corr, Nat.sub_zero, Nat.add_zero, Complex.re_sum, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- Sharp finite shift averaging, with the real part of each correlation and
the exact Cauchy--Schwarz prefactor N+H-1. No relation between H and N is needed. -/
theorem differencing_triangle (f : ℕ → ℂ) (N H : ℕ) :
    (H:ℝ)^2 * ‖∑ j ∈ range N, f j‖^2 ≤
      ((N+H-1:ℕ):ℝ)*((H:ℝ)*(∑ j ∈ range N, ‖f j‖^2) +
        2*∑ h ∈ range H, ∑ k ∈ range h, (corr f N (h-k)).re) := by
  let M := N+H-1
  let w (x : ℕ) := ∑ h ∈ range H, shift f N h x
  have avg : ∑ x ∈ range M, w x = (H:ℂ)*(∑ j ∈ range N, f j) := by
    dsimp only [w]
    rw [sum_comm]
    calc
      _ = ∑ _h ∈ range H, ∑ j ∈ range N, f j := by
        apply sum_congr rfl; intro h hh
        exact sum_shift f N h M (by dsimp [M]; have := mem_range.mp hh; omega)
      _ = _ := by simp
  have diag (h : ℕ) (hh : h ∈ range H) :
      ∑ x ∈ range M, ‖shift f N h x‖^2 = ∑ j ∈ range N, ‖f j‖^2 := by
    have eq := congrArg Complex.re (shift_overlap f N h h M le_rfl (by
      dsimp [M]; have := mem_range.mp hh; omega))
    simpa only [Complex.re_sum,Complex.mul_conj',← Complex.ofReal_pow,Complex.ofReal_re,Nat.sub_self,zero_corr] using eq
  have off (k h : ℕ) (hk : k ∈ range h) (hh : h ∈ range H) :
      ∑ x ∈ range M, (shift f N k x * conj (shift f N h x)).re = (corr f N (h-k)).re := by
    rw [← Complex.re_sum]
    exact congrArg Complex.re (shift_overlap f N k h M (mem_range.mp hk).le (by
      dsimp [M]; have := mem_range.mp hh; omega))
  have energy : ∑ x ∈ range M, ‖w x‖^2 =
      (H:ℝ)*(∑ j ∈ range N, ‖f j‖^2) +
      2*∑ h ∈ range H, ∑ k ∈ range h, (corr f N (h-k)).re := by
    dsimp only [w]
    simp_rw [norm_square_expand]
    rw [sum_add_distrib, ← mul_sum, sum_comm]
    congr 1
    · calc _ = ∑ _h ∈ range H, ∑ j ∈ range N, ‖f j‖^2 :=
                  sum_congr rfl (fun h hh => diag h hh)
           _ = _ := by simp
    · congr 1
      rw [sum_comm]
      apply sum_congr rfl; intro h hh
      rw [sum_comm]
      exact sum_congr rfl (fun k hk => off k h hk hh)
  have bound := square_cs w M
  rw [avg, norm_mul, mul_pow, energy] at bound
  simpa [M, Complex.norm_natCast] using bound


private theorem count_lags (F : ℕ → ℝ) (H : ℕ) :
    (∑ h ∈ range H, ∑ k ∈ range h, F (h-k)) =
      ∑ d ∈ range H, ((H-(d+1):ℕ):ℝ)*F (d+1) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [sum_range_succ, ih, sum_range_succ (f := fun d => ((H+1-(d+1):ℕ):ℝ)*F (d+1))]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
    have reflected : (∑ k ∈ range H, F (H-k)) = ∑ d ∈ range H, F (d+1) := by
      rw [← sum_range_reflect (fun d => F (d+1)) H]
      apply sum_congr rfl
      intro k hk
      have := mem_range.mp hk
      congr 1
      omega
    rw [reflected, ← sum_add_distrib]
    apply sum_congr rfl
    intro d hd
    have e : H+1-(d+1) = (H-(d+1))+1 := by have := mem_range.mp hd; omega
    rw [e, Nat.cast_succ]
    ring

/-- Finite van der Corput inequality with all overlapping pairs grouped by lag.
The multiplicity of lag d is H-d. Zero-length sequences and shifts past the
end are allowed. -/
theorem differencing (f : ℕ → ℂ) (N H : ℕ) :
    (H:ℝ)^2 * ‖∑ j ∈ range N, f j‖^2 ≤
      ((N+H-1:ℕ):ℝ)*((H:ℝ)*(∑ j ∈ range N, ‖f j‖^2) +
        2*∑ d ∈ range H, ((H-(d+1):ℕ):ℝ)*‖corr f N (d+1)‖) := by
  have h := differencing_triangle f N H
  rw [count_lags (fun d => (corr f N d).re)] at h
  apply h.trans
  gcongr with d hd
  exact Complex.re_le_norm _

/-- The additive character e(x)=exp(2πix). -/
def character (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x : ℝ):ℂ)*Complex.I)

private theorem character_diff (x y : ℝ) :
    character x * conj (character y) = character (x-y) := by
  unfold character
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- One A-process step for the exponential sum of a real phase. The new
phase is the first finite difference on the exact common interval. -/
theorem exponential_differencing (p : ℕ → ℝ) (N H : ℕ) :
    (H:ℝ)^2 * ‖∑ j ∈ range N, character (p j)‖^2 ≤
      ((N+H-1:ℕ):ℝ)*((H:ℝ)*N +
        2*∑ d ∈ range H, ((H-(d+1):ℕ):ℝ)*
          ‖∑ j ∈ range (N-(d+1)), character (p (j+(d+1))-p j)‖) := by
  simpa only [corr, character_diff, show ∀ x, ‖character x‖=1 from
    fun x => Complex.norm_exp_ofReal_mul_I _, one_pow, sum_const, card_range,
    nsmul_eq_mul,mul_one] using differencing (fun j => character (p j)) N H

private theorem triangular_number (H : ℕ) :
    2*(∑ j ∈ range H, (j:ℝ)) = (H:ℝ)*((H:ℝ)-1) := by
  induction H with
  | zero => simp
  | succ n ih => rw [sum_range_succ, Nat.cast_succ]; nlinarith only [ih]

/-- Uniform differenced-sum form. Any common bound on the nonzero shifts
can be fed directly to this inequality before optimizing the integer H. -/
theorem uniform_differencing (p : ℕ → ℝ) (N H : ℕ) (hH : 1 ≤ H) (E : ℝ)
    (bound : ∀ d, 0 < d → d < H →
      ‖∑ j ∈ range (N-d), character (p (j+d) - p j)‖ ≤ E) :
    (H:ℝ)*‖∑ j ∈ range N, character (p j)‖^2 ≤
      ((N+H-1:ℕ):ℝ)*((N:ℝ) + ((H:ℝ)-1)*E) := by
  let f := fun j => character (p j)
  have b := differencing_triangle f N H
  have diag : (∑ j ∈ range N, ‖f j‖^2) = (N:ℝ) := by
    have char_unit (x : ℝ) : ‖character x‖=1 := Complex.norm_exp_ofReal_mul_I _
    simp only [f, char_unit, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
  rw [diag] at b
  have each (h : ℕ) (hh : h ∈ range H) : (∑ k ∈ range h, (corr f N (h-k)).re) ≤ (h:ℝ)*E := by
    calc _ ≤ ∑ _k ∈ range h, E := by
           apply sum_le_sum
           intro k hk
           apply (Complex.re_le_norm _).trans
           have dpos : 0 < h-k := by have := mem_range.mp hk; omega
           have dlt : h-k < H := (Nat.sub_le ..).trans_lt (mem_range.mp hh)
           simpa [corr, f, character_diff] using bound _ dpos dlt
         _ = _ := by simp
  have tri := mul_le_mul_of_nonneg_left (sum_le_sum each) (show (0:ℝ) ≤ 2 by norm_num)
  rw [← sum_mul] at tri
  have tri' : 2*(∑ h ∈ range H, ∑ k ∈ range h, (corr f N (h-k)).re)
       ≤ (H:ℝ)*((H:ℝ)-1)*E := by
    calc _ ≤ _ := tri
         _ = _ := by rw [← mul_assoc, triangular_number]
  have pos : 0 < (H:ℝ) := by exact_mod_cast (show 0 < H by omega)
  apply (mul_le_mul_iff_right₀ pos).mp
  calc
    _ = (H:ℝ)^2 * ‖∑ j ∈ range N, f j‖^2 := by dsimp [f]; ring
    _ ≤ _ := b
    _ ≤ ((N+H-1:ℕ):ℝ)*((H:ℝ)*N + ((H:ℝ)*((H:ℝ)-1)*E)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl tri') (Nat.cast_nonneg _)
    _ = _ := by ring

/-- One A-step with both a uniform oscillatory term P and the reciprocal-lag
error B/d. Summing the latter only spends a harmonic factor. -/
theorem differencing_with_inverse_lag (p : ℕ → ℝ) (N H : ℕ) (hH : 1 ≤ H)
    {P B : ℝ} (hP : 0 ≤ P) (hB : 0 ≤ B)
    (bound : ∀ d, 0 < d → d < H →
      ‖∑ j ∈ range (N-d), character (p (j+d)-p j)‖ ≤ P+B/d) :
    (H:ℝ) * ‖∑ j ∈ range N, character (p j)‖^2 ≤
      ((N+H-1:ℕ):ℝ)*((N:ℝ)+2*((H:ℝ)*P+B*(1+Real.log H))) := by
  let E (d : ℕ) := ‖∑ j ∈ range (N-d), character (p (j+d)-p j)‖
  have each_lag (d : ℕ) (hd : d ∈ range H) :
      ((H-(d+1):ℕ):ℝ)*E (d+1) ≤ (H:ℝ)*(P+B/((d+1:ℕ):ℝ)) := by
    have leH : d+1 ≤ H := mem_range.mp hd
    by_cases eqH : d+1 = H
    · rw [eqH, Nat.sub_self, Nat.cast_zero, zero_mul]
      positivity
    · have posd : 0 < d+1 := Nat.succ_pos _
      exact mul_le_mul (by exact_mod_cast Nat.sub_le H (d+1))
        (bound _ posd (lt_of_le_of_ne leH eqH)) (norm_nonneg _) (Nat.cast_nonneg _)
  have sum_inv : (∑ d ∈ range H, ((d+1:ℕ):ℝ)⁻¹) = (harmonic H:ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have est : (∑ d ∈ range H, ((H-(d+1):ℕ):ℝ)*E (d+1)) ≤
      (H:ℝ)*((H:ℝ)*P+B*(1+Real.log H)) := by
    apply (sum_le_sum each_lag).trans
    rw [← mul_sum]
    simp only [div_eq_mul_inv,sum_add_distrib,← mul_sum,sum_inv,sum_const,card_range,
      nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log H) hB)) (Nat.cast_nonneg _)
  have base := exponential_differencing p N H
  have Hpos : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  apply (mul_le_mul_iff_right₀ Hpos).mp
  calc
    _ = (H:ℝ)^2*‖∑ j ∈ range N, character (p j)‖^2 := by ring
    _ ≤ _ := base
    _ ≤ ((N+H-1:ℕ):ℝ)*((H:ℝ)*N+2*((H:ℝ)*((H:ℝ)*P+B*(1+Real.log H)))) := by
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left est (by norm_num))) (Nat.cast_nonneg _)
    _ = _ := by ring

end FactorialDifferencing
end
end

-- Source module ReciprocalAOptimization
section

/-! Optimize an integer van der Corput shift for the second A-step.
M is the reference interval length, X the effective first difference of
the phase. Finite sums can occupy any shorter interval of length at most 3M.
The resulting exponents are (1/14,11/14). -/

noncomputable section
open Finset Real
namespace FactorialDifferencing

private lemma log_monomial {M X : ℝ} (hM : 0 < M) (hX : 0 < X) (a b : ℝ) :
    log (M^a*X^b) = a*log M+b*log X := by
  rw [log_mul (rpow_pos_of_pos hM _).ne' (rpow_pos_of_pos hX _).ne',
    log_rpow hM,log_rpow hX]

/-- Integer shift optimization converting the first A bound to the second.
The input estimate must hold for every integer shift length up to M. -/
theorem optimize_second_A {M X K S : ℝ} {N : ℕ} (hm : 1 ≤ M) (hx : 0 < X)
    (hk : 1 ≤ K) (hn : (N:ℝ) ≤ 3*M) (trivial_bound : S ≤ N)
    (previous : S ≤ K*(M^(2/3:ℝ)*X^(1/6:ℝ)+1/X))
    (step : ∀ H : ℕ, 1 ≤ H → (H:ℝ) ≤ M →
      (H:ℝ)*S^2 ≤ ((N:ℝ)+H)*((N:ℝ)+H*K*(M^(1/2:ℝ)*((H:ℝ)*X)^(1/6:ℝ)+M/X))) :
    S ≤ 8*K*(M^(11/14:ℝ)*X^(1/14:ℝ)+1/X) := by
  have mp : 0 < M := by linarith
  have kp : 0 < K := by linarith
  let T := M^(11/14:ℝ)*X^(1/14:ℝ)
  have tp : 0 < T := by dsimp [T]; positivity
  have lt' : log T = (11/14:ℝ)*log M+(1/14:ℝ)*log X := log_monomial mp hx _ _
  have ml := log_nonneg hm
  have extend (hs : S ≤ 8*K*T) : S ≤ 8*K*(T+1/X) := by
    exact hs.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity))
  by_cases small : X ≤ M^(5/4:ℝ)
  · have l := log_le_log hx small
    rw [log_rpow mp] at l
    have le : M^(2/3:ℝ)*X^(1/6:ℝ) ≤ T := by
      apply (log_le_log_iff (by positivity) tp).mp
      rw [log_monomial mp hx,lt']
      linarith
    apply previous.trans
    calc K*(M^(2/3:ℝ)*X^(1/6:ℝ)+1/X) ≤ K*(T+1/X) :=
           mul_le_mul_of_nonneg_left (add_le_add le le_rfl) kp.le
         _ ≤ 8*K*(T+1/X) := by gcongr; linarith
  have lsmall := log_le_log (rpow_pos_of_pos mp (5/4)) (le_of_not_ge small)
  rw [log_rpow mp] at lsmall
  by_cases large : M^3 ≤ X
  · have l := log_le_log (pow_pos mp 3) large
    rw [log_pow] at l
    have mt : M ≤ T := by
      apply (log_le_log_iff mp tp).mp
      rw [lt']
      norm_num at l ⊢
      linarith
    apply extend
    calc S ≤ (N:ℝ) := trivial_bound
         _ ≤ 3*M := hn
         _ ≤ 8*K*T := mul_le_mul (by linarith) mt mp.le (by positivity)
  have llarge := log_le_log hx (le_of_not_ge large)
  rw [log_pow] at llarge
  let Y := M^(3/7:ℝ)*X^(-(1/7):ℝ)
  let U := M^(4/7:ℝ)*X^(1/7:ℝ)
  have yp : 0 < Y := by dsimp [Y]; positivity
  have up : 0 < U := by dsimp [U]; positivity
  have ly : log Y = (3/7:ℝ)*log M+(-(1/7):ℝ)*log X := log_monomial mp hx _ _
  have lu : log U = (4/7:ℝ)*log M+(1/7:ℝ)*log X := log_monomial mp hx _ _
  have ylo : 1 ≤ Y := by
    apply (log_le_log_iff one_pos yp).mp
    rw [log_one,ly]; norm_num at llarge; linarith
  have ym : Y ≤ M := by
    apply (log_le_log_iff yp mp).mp
    rw [ly]; linarith
  have yx : Y ≤ X := by
    apply (log_le_log_iff yp hx).mp
    rw [ly]; linarith
  have product : Y*U = M := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (mul_pos yp up)) mp
    rw [log_mul yp.ne' up.ne',ly,lu]; ring
  have Tsq : T^2 = M*U := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (pow_pos tp 2)) (Set.mem_Ioi.mpr (mul_pos mp up))
    rw [log_pow, log_mul mp.ne' up.ne',lt',lu]; norm_num; ring
  have power_eq : M^(1/2:ℝ)*(Y*X)^(1/6:ℝ) = U := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) up
    rw [log_mul (rpow_pos_of_pos mp _).ne' (rpow_pos_of_pos (mul_pos yp hx) _).ne',
        log_rpow mp,log_rpow (mul_pos yp hx),log_mul yp.ne' hx.ne',ly,lu]
    ring
  let H := ⌊Y⌋₊
  have h1 : 1 ≤ H := Nat.floor_pos.mpr ylo
  have Hp : 0 < (H:ℝ) := by exact_mod_cast (show 0 < H by omega)
  have hy : (H:ℝ) ≤ Y := Nat.floor_le yp.le
  have floor_lower : Y ≤ 2*(H:ℝ) := by
    have lo : (1:ℝ) ≤ H := by exact_mod_cast h1
    have hi : Y < (H:ℝ)+1 := Nat.lt_floor_add_one _
    linarith
  have original := step H h1 (hy.trans ym)
  have shifted : M^(1/2:ℝ)*((H:ℝ)*X)^(1/6:ℝ)+M/X ≤ 2*U := by
    have pow_le : M^(1/2:ℝ)*((H:ℝ)*X)^(1/6:ℝ) ≤ U := by
      rw [← power_eq]
      gcongr
    have inv_le : M/X ≤ U := (div_le_iff₀ hx).mpr (by
      rw [← product]; simpa [mul_comm] using mul_le_mul_of_nonneg_right yx up.le)
    linarith
  have mass : M ≤ 2*(H:ℝ)*U := by
    rw [← product]
    exact mul_le_mul_of_nonneg_right floor_lower up.le
  have right : (N:ℝ)+H*K*(M^(1/2:ℝ)*((H:ℝ)*X)^(1/6:ℝ)+M/X) ≤
      8*(H:ℝ)*K*U := by
    have main := mul_le_mul_of_nonneg_left shifted (mul_nonneg Hp.le kp.le)
    have huK := mul_le_mul_of_nonneg_right hk (mul_nonneg Hp.le up.le)
    nlinarith only [main,mass,hn,huK]
  have ready : (H:ℝ)*S^2 ≤ (H:ℝ)*(32*K*(M*U)) := by
    apply original.trans
    calc _ ≤ (4*M)*(8*(H:ℝ)*K*U) := by
           apply mul_le_mul (by linarith [hy.trans ym]) right (by positivity) (by positivity)
         _ = _ := by ring
  have sqbound := (mul_le_mul_iff_right₀ Hp).mp ready
  apply extend
  apply le_of_sq_le_sq _ (by positivity)
  apply sqbound.trans
  rw [← Tsq]
  calc 32*K*T^2 ≤ 64*K^2*T^2 := by
         apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
         nlinarith [mul_nonneg kp.le (sub_nonneg.mpr hk)]
       _ = _ := by ring

/-- Second A-step in finite-sum form. Both preceding-pair hypotheses are
ordinary exponential sums on the exact (possibly empty) overlap. -/
theorem second_A_of_differences (p : ℕ → ℝ) {N : ℕ} {M X K : ℝ}
    (hm : 1 ≤ M) (hx : 0 < X) (hk : 1 ≤ K) (hn : (N:ℝ) ≤ 3*M)
    (previous : ‖∑ j ∈ range N, character (p j)‖ ≤ K*(M^(2/3:ℝ)*X^(1/6:ℝ)+1/X))
    (differences : ∀ d : ℕ, 1 ≤ d → (d:ℝ) ≤ M →
      ‖∑ j ∈ range (N-d), character (p (j+d)-p j)‖ ≤
        K*(M^(1/2:ℝ)*((d:ℝ)*X)^(1/6:ℝ)+M/((d:ℝ)*X))) :
    ‖∑ j ∈ range N, character (p j)‖ ≤ 8*K*(M^(11/14:ℝ)*X^(1/14:ℝ)+1/X) := by
  have mp : 0 < M := by linarith
  have kp : 0 < K := by linarith
  have tr : ‖∑ j ∈ range N, character (p j)‖ ≤ (N:ℝ) := by
    apply (norm_sum_le _ _).trans
    have unit (j : ℕ) : ‖character (p j)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    simp only [unit,sum_const,card_range,nsmul_eq_mul,mul_one,le_refl]
  apply optimize_second_A hm hx hk hn tr previous
  intro H hH HM
  let E := K*(M^(1/2:ℝ)*((H:ℝ)*X)^(1/6:ℝ)+M/X)
  have epos : 0 ≤ E := by dsimp [E]; positivity
  have hHR : (1:ℝ) ≤ H := by exact_mod_cast hH
  have each (d : ℕ) (hd : 0 < d) (dh : d < H) :
      ‖∑ j ∈ range (N-d), character (p (j+d)-p j)‖ ≤ E := by
    have dh' : (d:ℝ) ≤ H := by exact_mod_cast dh.le
    have dlo : (1:ℝ) ≤ d := by exact_mod_cast hd
    apply (differences d hd (dh'.trans HM)).trans
    dsimp [E]
    apply mul_le_mul_of_nonneg_left _ kp.le
    apply add_le_add
    · gcongr
    · apply div_le_div_of_nonneg_left mp.le hx
      simpa using mul_le_mul_of_nonneg_right dlo hx.le
  have b := uniform_differencing p N H hH E each
  have pref : ((N+H-1:ℕ):ℝ) ≤ (N:ℝ)+H := by exact_mod_cast Nat.sub_le (N+H) 1
  have hm0 : 0 ≤ (H:ℝ)-1 := sub_nonneg.mpr hHR
  apply b.trans
  calc _ ≤ ((N:ℝ)+H)*(N+H*E) := by
         apply mul_le_mul pref (by gcongr; linarith) (by positivity) (by positivity)
       _ = _ := by dsimp [E]; ring

end FactorialDifferencing
end
end

-- Source module ReciprocalMixedDifferences
section

/-! Mixed finite differences of reciprocal powers. A shift acts by
$D_h f(x)=f(x)-f(x+h)$. The two bounds retain the product of all shifts.
They apply before and after every differencing step in the factorial sieve. -/
noncomputable section
open Set

namespace FactorialReciprocal

/-- Iteratively difference the reciprocal power, with the completely monotone sign. -/
def diffPow : List ℝ → ℕ → ℝ → ℝ
  | [], p, x => (x^p)⁻¹
  | h :: hs, p, x => diffPow hs p x - diffPow hs p (x+h)

/-- Differentiating a mixed difference raises the reciprocal power by one. -/
theorem hasDerivAt_diffPow (hs : List ℝ) (p : ℕ) {x : ℝ} (hx : 0 < x)
    (nonneg : ∀ h ∈ hs, 0 ≤ h) :
    HasDerivAt (diffPow hs p) (-(p:ℝ)*diffPow hs (p+1) x) x := by
  induction hs generalizing x with
  | nil =>
    cases p with
    | zero => simpa [diffPow] using (hasDerivAt_const x (1:ℝ))
    | succ p =>
      have hd := (hasDerivAt_pow (p+1) x).inv (pow_ne_zero _ hx.ne')
      apply hd.congr_deriv
      change -(↑(p+1) * x^(p+1-1)) / (x^(p+1))^2 = -(↑(p+1):ℝ) * (x^(p+1+1))⁻¹
      rw [Nat.add_sub_cancel, pow_succ x (p+1), pow_succ x p]
      field_simp
  | cons h hs ih =>
    have h0 := nonneg h (by simp)
    have ht : ∀ y ∈ hs, 0 ≤ y := fun y hy => nonneg y (by simp [hy])
    have A := ih hx ht
    have B := (ih (x := x+h) (by linarith) ht).comp_add_const x h
    apply (A.sub B).congr_deriv
    change -(p:ℝ)*diffPow hs (p+1) x - (-(p:ℝ)*diffPow hs (p+1) (x+h)) =
      -(p:ℝ)*(diffPow hs (p+1) x - diffPow hs (p+1) (x+h))
    ring

private lemma jump (hs : List ℝ) (p : ℕ) {x h : ℝ} (hx : 0 < x) (hh : 0 < h)
    (nonneg : ∀ a ∈ hs, 0 ≤ a) :
    ∃ y ∈ Ioo x (x+h), diffPow (h::hs) p x = (h*p)*diffPow hs (p+1) y := by
  have hder (y : ℝ) (hy : 0 < y) := hasDerivAt_diffPow hs p hy nonneg
  obtain ⟨y,hy,eq⟩ := exists_hasDerivAt_eq_slope (diffPow hs p)
    (fun y => -(p:ℝ)*diffPow hs (p+1) y) (show x<x+h by linarith)
    (fun y hy => (hder y (lt_of_lt_of_le hx hy.1)).continuousAt.continuousWithinAt)
    (fun y hy => hder y (hx.trans hy.1))
  use y, hy
  rw [show x+h-x=h by ring] at eq
  have eq' := (eq_div_iff hh.ne').mp eq
  dsimp [diffPow]
  linarith only [show (-(p:ℝ)*diffPow hs (p+1) y)*h= -(h*p*diffPow hs (p+1) y) by ring,eq']

/-- Uniform estimates for arbitrarily many shifts on an interval away from zero. -/
theorem diffPow_bounds (hs : List ℝ) (p : ℕ) {x : ℝ} (hx : 0 < x)
    (nonneg : ∀ h ∈ hs, 0 ≤ h) :
    (p.ascFactorial hs.length : ℝ) * hs.prod / (x+hs.sum)^(p+hs.length) ≤ diffPow hs p x ∧
    diffPow hs p x ≤ (p.ascFactorial hs.length : ℝ) * hs.prod / x^(p+hs.length) := by
  induction hs generalizing p x with
  | nil => simp [diffPow,one_div]
  | cons h hs ih =>
    have h0 := nonneg h (by simp)
    have ht : ∀ a ∈ hs, 0 ≤ a := fun a ha => nonneg a (by simp [ha])
    by_cases zero : h=0
    · simp [zero,diffPow]
    have hh := lt_of_le_of_ne h0 (Ne.symm zero)
    obtain ⟨y,hy,eq⟩ := jump hs p hx hh ht
    have yp := hx.trans hy.1
    obtain ⟨lo,hi⟩ := ih (p+1) yp ht
    let b : ℝ := ((p+1).ascFactorial hs.length : ℝ) * hs.prod
    have posprod := List.prod_nonneg ht
    have bnon : 0 ≤ b := by dsimp [b]; positivity
    have ssum := List.sum_nonneg ht
    have coeff : (p.ascFactorial (h::hs).length : ℝ) * (h::hs).prod = (h*p)*b := by
      have fac : p.ascFactorial (hs.length+1) = p*(p+1).ascFactorial hs.length :=
        Nat.ascFactorial_succ.trans (Nat.succ_ascFactorial p hs.length).symm
      simp only [List.length_cons, List.prod_cons,fac,Nat.cast_mul]
      dsimp [b]
      ring
    have expo : p+(h::hs).length = (p+1)+hs.length := by simp; omega
    rw [coeff,expo, List.sum_cons, eq]
    change b/(y+hs.sum)^_ ≤ _ at lo
    change _ ≤ b/y^_ at hi
    have hp : 0 ≤ h*(p:ℝ) := by positivity
    constructor
    · rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ hp
      apply le_trans _ lo
      apply div_le_div_of_nonneg_left bnon (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by linarith [hy.2]) _
    · rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ hp
      apply hi.trans
      apply div_le_div_of_nonneg_left bnon (by positivity)
      exact pow_le_pow_left₀ hx.le hy.1.le _

/-- With nonnegative shifts every mixed reciprocal difference is nonnegative. -/
theorem diffPow_nonneg (hs : List ℝ) (p : ℕ) {x : ℝ} (hx : 0 < x)
    (nonneg : ∀ h ∈ hs, 0 ≤ h) : 0 ≤ diffPow hs p x := by
  have hp := List.prod_nonneg nonneg
  have hsum := List.sum_nonneg nonneg
  exact le_trans (by positivity) (diffPow_bounds hs p hx nonneg).1

/-- All these signed differences decrease with their base point. -/
theorem diffPow_antitoneOn (hs : List ℝ) (p : ℕ) (nonneg : ∀ h ∈ hs, 0 ≤ h) :
    AntitoneOn (diffPow hs p) (Ioi 0) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl|lt
  · exact le_rfl
  obtain ⟨w, hw, step⟩ := jump hs p hx (sub_pos.mpr lt) nonneg
  have h := diffPow_nonneg hs (p+1) (lt_trans hx hw.1) nonneg
  have good : 0 ≤ ((y-x)*p)*diffPow hs (p+1) w :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr lt.le) (Nat.cast_nonneg _)) h
  have val := good.trans step.ge
  change 0 ≤ diffPow hs p x - diffPow hs p (x+(y-x)) at val
  rw [show x+(y-x)=y by ring] at val
  exact sub_nonneg.mp val

/-- Exact derivatives of every order, including the shifted phases of the A process. -/
theorem iteratedDeriv_diffPow (hs : List ℝ) (p r : ℕ) {x : ℝ} (hx : 0 < x)
    (nonneg : ∀ h ∈ hs, 0 ≤ h) :
    iteratedDeriv r (diffPow hs p) x = (-1:ℝ)^r*(p.ascFactorial r : ℝ)*diffPow hs (p+r) x := by
  induction r generalizing p with
  | zero => simp
  | succ r ih =>
    have agree : Set.EqOn (deriv (diffPow hs p)) (fun y => -(p:ℝ)*diffPow hs (p+1) y) (Ioi 0) :=
      fun y hy => (hasDerivAt_diffPow hs p hy nonneg).deriv
    have eq := agree.iteratedDeriv_of_isOpen isOpen_Ioi r (show x∈Ioi 0 from hx)
    rw [iteratedDeriv_succ',eq,iteratedDeriv_const_mul_field, ih]
    have fac : p.ascFactorial (r+1)=p*(p+1).ascFactorial r :=
      Nat.ascFactorial_succ.trans (Nat.succ_ascFactorial p r).symm
    rw [fac, Nat.cast_mul, pow_succ,show p+1+r=p+(r+1) by omega]
    ring

/-- The r-th derivative of the mixed reciprocal phase has one sign. Its absolute
size lies between the corresponding derivatives at the two extreme endpoints. -/
theorem shifted_reciprocal_derivative_bounds (hs : List ℝ) (r : ℕ)
    {x : ℝ} (hx : 0 < x) (nonneg : ∀ h ∈ hs, 0 ≤ h) :
    ((r+hs.length).factorial : ℝ)*hs.prod/(x+hs.sum)^(r+hs.length+1) ≤
      |iteratedDeriv r (diffPow hs 1) x| ∧
    |iteratedDeriv r (diffPow hs 1) x| ≤
      ((r+hs.length).factorial : ℝ)*hs.prod/x^(r+hs.length+1) := by
  rw [iteratedDeriv_diffPow hs 1 r hx nonneg]
  simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,Nat.one_ascFactorial,
    abs_of_nonneg (Nat.cast_nonneg r.factorial : (0:ℝ) ≤ (r.factorial:ℝ)), abs_of_nonneg (diffPow_nonneg hs (1+r) hx nonneg)]
  obtain ⟨lo,hi⟩ := diffPow_bounds hs (1+r) hx nonneg
  have fac : (r.factorial : ℝ) * ((1+r).ascFactorial hs.length : ℝ) =
      ((r+hs.length).factorial : ℝ) := by
    exact_mod_cast (by simpa [Nat.add_comm 1 r] using Nat.factorial_mul_ascFactorial r hs.length :
      r.factorial * (1+r).ascFactorial hs.length = (r+hs.length).factorial)
  have expEq : 1+r+hs.length = r+hs.length+1 := by omega
  rw [expEq] at lo hi
  have left := mul_le_mul_of_nonneg_left lo (Nat.cast_nonneg r.factorial : (0:ℝ) ≤ _)
  have right := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg r.factorial : (0:ℝ) ≤ _)
  rw [← mul_div_assoc, ← mul_assoc, fac] at left right
  exact ⟨left,right⟩

end FactorialReciprocal
end
end

-- Source module ReciprocalGeneralSpacing
section

/-! A partition for exponential sums whose consecutive downward increments
decrease by at least a fixed amount per index. The finite argument
splits the resonant increments from the intervals in safe cells. -/
noncomputable section
open Finset
namespace SeparatedGaps
structure Profile where
  gap : ℕ → ℝ
  lo : ℕ
  hi : ℕ
  cap : ℝ
  step : ℝ
  step_pos : 0 < step
  nonneg : ∀ j, 0 ≤ gap j
  gap_le : ∀ {j}, lo ≤ j → gap j ≤ cap
  separation : ∀ {j k : ℕ}, lo ≤ j → j ≤ k → k ≤ hi →
    ((k:ℝ)-j)*step ≤ gap j-gap k

theorem Profile.cap_nonneg (P : Profile) : 0 ≤ P.cap :=
  (P.nonneg P.lo).trans (P.gap_le (j:=P.lo) le_rfl)

variable (P : Profile)

/-- Indices at which the increment lies within η of a specified center. -/
def near (η k : ℝ) : Finset ℕ :=
  (Icc P.lo (P.hi)).filter fun j => |P.gap j-k| < η

/-- An arbitrary center catches at most 1+2η/step indices. -/
lemma near_card {η k : ℝ} (hη : 0 ≤ η) :
    ((near P η k).card:ℝ) ≤ 1+2*η/P.step := by
  let S := near P η k
  have sp := P.step_pos
  by_cases hs : S.Nonempty
  · let a := S.min' hs
    let b := S.max' hs
    have ha : a ∈ S := min'_mem S hs
    have hb : b ∈ S := max'_mem S hs
    have hab : a ≤ b := le_max' S a ha
    have ain := mem_filter.mp (show a ∈ near P η k from ha)
    have bin := mem_filter.mp (show b ∈ near P η k from hb)
    have sep := P.separation (mem_Icc.mp ain.1).1 hab (mem_Icc.mp bin.1).2
    have top := (abs_lt.mp ain.2).2
    have bot := (abs_lt.mp bin.2).1
    have width : (b:ℝ)-a ≤ 2*η/P.step := (le_div_iff₀ sp).mpr (by linarith)
    have subset : S ⊆ Icc a b := fun j hj =>
      mem_Icc.mpr ⟨min'_le S j hj,le_max' S j hj⟩
    have bound := card_le_card subset
    rw [Nat.card_Icc] at bound
    have coeff : ((S.card : ℕ):ℝ) ≤ (b:ℝ)+1-a := by
      exact_mod_cast (show (S.card:ℤ) ≤ (b:ℤ)+1-a by omega)
    change (S.card:ℝ) ≤ _
    linarith
  · have heq : S = ∅ := not_nonempty_iff_eq_empty.mp hs
    change (S.card:ℝ) ≤ _
    rw [heq,card_empty,Nat.cast_zero]
    positivity

/-- A finite interval containing every integer approached by an increment. -/
def centers (η : ℝ) : Finset ℤ := Icc 0 ⌊P.cap+η⌋

lemma center_mem {η : ℝ} {k : ℤ} {j : ℕ}
    (hη : η ≤ 1) (hj : P.lo ≤ j) (hd : |P.gap j-(k:ℝ)| < η) :
    k ∈ centers P η := by
  obtain ⟨lo,hi⟩ := abs_lt.mp hd
  have gnon : 0 ≤ P.gap j := P.nonneg _
  have neg : (-1:ℝ) < k := by linarith
  have nonneg : (0:ℤ) ≤ k := by
    have h : (-1:ℤ) < k := by exact_mod_cast neg
    omega
  exact mem_Icc.mpr ⟨nonneg,Int.le_floor.mpr (by linarith [P.gap_le hj])⟩

lemma centers_card {η : ℝ} (hη : 0 ≤ η) :
    ((centers P η).card:ℝ) ≤ P.cap+η+1 := by
  let R := P.cap+η
  have hR : 0 ≤ R := by dsimp [R]; linarith [P.cap_nonneg]
  have hfl : (0:ℤ) ≤ ⌊R⌋ := Int.floor_nonneg.mpr hR
  change ((Icc (0:ℤ) ⌊R⌋).card:ℝ) ≤ R+1
  rw [Int.card_Icc,sub_zero]
  have h := Int.floor_le R
  have nonneg : 0 ≤ ⌊R⌋ + 1 := by omega
  exact_mod_cast (show (((⌊R⌋ + 1).toNat:ℤ):ℝ) ≤ R+1 by
    rw [Int.toNat_of_nonneg nonneg,Int.cast_add,Int.cast_one]
    linarith)

open scoped Classical in
/-- All near-resonant indices in the factor-three interval. -/
def resonant (η : ℝ) : Finset ℕ :=
  (Icc P.lo (P.hi)).filter fun j => ∃ k : ℤ, |P.gap j-(k:ℝ)| < η

lemma resonant_card {η : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1) :
    ((resonant P η).card : ℝ) ≤
      (P.cap+η+1)*(1+2*η/P.step) := by
  classical
  let C := centers P η
  let S := fun k : ℤ => near P η (k:ℝ)
  have sub : resonant P η ⊆ C.biUnion S := by
    intro j hj
    obtain ⟨mem,⟨k,hk⟩⟩ := mem_filter.mp hj
    exact mem_biUnion.mpr ⟨k,center_mem P hη' (mem_Icc.mp mem).1 hk,
      mem_filter.mpr ⟨mem,hk⟩⟩
  have nbound := (card_le_card sub).trans (card_biUnion_le (s:=C) (t:=S))
  have rbound : ((resonant P η).card:ℝ) ≤ ∑ k ∈ C, ((S k).card:ℝ) := by exact_mod_cast nbound
  calc
    _ ≤ _ := rbound
    _ ≤ ∑ _k ∈ C,(1+2*η/P.step) := sum_le_sum fun k _ => near_card P (k:=(k:ℝ)) hη
    _ = (C.card:ℝ)*(1+2*η/P.step) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (centers_card P hη) (by
      have := P.step_pos
      positivity)


/-- Sum on an interval, given cancellation on every smaller interval in a
single safe cell of the increment. The cells left after removing near-integer
gaps are intervals because the gaps decrease. -/
lemma block_of_safe_cells {η K : ℝ} {a b : ℕ}
    (ha : P.lo ≤ a) (hb : b ≤ P.hi) (hη : 0 < η) (hη' : η ≤ 1) (hK : 0 ≤ K)
    (F : ℕ → ℂ) (unit : ∀ j, ‖F j‖ ≤ 1)
    (safe : ∀ c d : ℕ, a ≤ c → c ≤ d → d ≤ b → ∀ k : ℤ,
      (∀ j ∈ Icc c d, (k:ℝ)+η ≤ P.gap j ∧ P.gap j ≤ (k:ℝ)+1-η) →
      ‖∑ j ∈ Icc c d,F j‖ ≤ K) :
    ‖∑ j ∈ Icc a b,F j‖ ≤
      (P.cap+η+1)*(1+2*η/P.step + K) := by
  classical
  let U := Icc a b
  let B := U.filter fun j => ∃ k : ℤ, |P.gap j-(k:ℝ)| < η
  let G := U.filter fun j => ¬∃ k : ℤ, |P.gap j-(k:ℝ)| < η
  let C := centers P η
  let S (k : ℤ) := G.filter fun j => ⌊P.gap j⌋ = k
  have bounds {j : ℕ} (hj : j ∈ U) := mem_Icc.mp hj
  have badSub : B ⊆ resonant P η := by
    intro j hj
    obtain ⟨hj,hd⟩ := mem_filter.mp hj
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨ha.trans (bounds hj).1,(bounds hj).2.trans hb⟩,hd⟩
  have Gmap (j : ℕ) (hj : j ∈ G) : ⌊P.gap j⌋ ∈ C := by
    have jm := ha.trans (bounds (mem_filter.mp hj).1).1
    have pos : 0 ≤ P.gap j := P.nonneg _
    apply mem_Icc.mpr
    refine ⟨Int.floor_nonneg.mpr pos,Int.floor_mono ?_⟩
    linarith [P.gap_le jm]
  have cellBounds {j : ℕ} {k : ℤ} (hj : j ∈ S k) :
      (k:ℝ)+η ≤ P.gap j ∧ P.gap j ≤ (k:ℝ)+1-η := by
    obtain ⟨hg,hf⟩ := mem_filter.mp hj
    have hn := (mem_filter.mp hg).2
    have fl := Int.floor_le (P.gap j)
    have fh := Int.lt_floor_add_one (P.gap j)
    rw [hf] at fl fh
    have h₁ : η ≤ |P.gap j-(k:ℝ)| := le_of_not_gt fun h => hn ⟨k,h⟩
    have h₂ : η ≤ |P.gap j-((k+1:ℤ):ℝ)| := le_of_not_gt fun h => hn ⟨k+1,h⟩
    push_cast at h₂
    rw [abs_of_nonneg (sub_nonneg.mpr fl)] at h₁
    rw [abs_of_nonpos (by linarith : P.gap j - ((k:ℝ)+1) ≤ 0)] at h₂
    constructor <;> linarith
  have makeCell {j : ℕ} {k : ℤ} (hj : j ∈ U)
      (hd : (k:ℝ)+η ≤ P.gap j ∧ P.gap j ≤ (k:ℝ)+1-η) : j ∈ S k := by
    have hf : ⌊P.gap j⌋ = k := Int.floor_eq_iff.mpr ⟨by linarith [hd.1],by linarith [hd.2]⟩
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨hj,?_⟩,hf⟩
    rintro ⟨l,hl⟩
    obtain ⟨low,high⟩ := abs_lt.mp hl
    by_cases e : l ≤ k
    · have er : (l:ℝ) ≤ k := by exact_mod_cast e
      linarith [hd.1]
    · have ei : k+1 ≤ l := by omega
      have er : (k:ℝ)+1 ≤ l := by exact_mod_cast ei
      linarith [hd.2]
  have mono {j k : ℕ} (hj : P.lo ≤ j) (hjk : j ≤ k) (hk : k ≤ P.hi) :
      P.gap k ≤ P.gap j := by
    have sr := P.separation hj hjk hk
    have le : (0:ℝ) ≤ (k:ℝ)-(j:ℝ) := sub_nonneg.mpr (by exact_mod_cast hjk)
    have nonneg := mul_nonneg le (P.step_pos).le
    linarith
  have sumcell (k : ℤ) : ‖∑ j ∈ S k,F j‖ ≤ K := by
    by_cases hs : (S k).Nonempty
    · let c := (S k).min' hs
      let d := (S k).max' hs
      have cm : c ∈ S k := min'_mem _ _
      have dm : d ∈ S k := max'_mem _ _
      have cu := bounds (mem_filter.mp (mem_filter.mp cm).1).1
      have du := bounds (mem_filter.mp (mem_filter.mp dm).1).1
      have cd : c ≤ d := le_max' _ _ cm
      have between (j : ℕ) (hj : j ∈ Icc c d) :
          (k:ℝ)+η ≤ P.gap j ∧ P.gap j ≤ (k:ℝ)+1-η := by
        obtain ⟨jl,jr⟩ := mem_Icc.mp hj
        have low := mono (ha.trans (cu.1.trans jl)) jr (du.2.trans hb)
        have high := mono (ha.trans cu.1) jl (jr.trans (du.2.trans hb))
        exact ⟨(cellBounds dm).1.trans low, high.trans (cellBounds cm).2⟩
      have eq : S k = Icc c d := by
        ext j
        constructor
        · intro hj
          exact mem_Icc.mpr ⟨min'_le _ _ hj,le_max' _ _ hj⟩
        · intro hj
          exact makeCell (mem_Icc.mpr ⟨cu.1.trans (mem_Icc.mp hj).1,(mem_Icc.mp hj).2.trans du.2⟩)
            (between j hj)
      rw [eq]
      exact safe c d cu.1 cd du.2 k between
    · rw [not_nonempty_iff_eq_empty.mp hs]
      simpa using hK
  have decomp : ∑ j ∈ B,F j + ∑ j ∈ G,F j = ∑ j ∈ U,F j :=
    sum_filter_add_sum_filter_not _ _ _
  have partition : ∑ k ∈ C,∑ j ∈ S k,F j = ∑ j ∈ G,F j :=
    Finset.sum_fiberwise_of_maps_to Gmap F
  have bcost : ‖∑ j ∈ B,F j‖ ≤ (resonant P η).card := by
    calc _ ≤ ∑ j ∈ B,‖F j‖ := norm_sum_le _ _
         _ ≤ ∑ _j ∈ B,(1:ℝ) := sum_le_sum fun j _ => unit j
         _ = B.card := by simp
         _ ≤ _ := by exact_mod_cast card_le_card badSub
  have gcost : ‖∑ j ∈ G,F j‖ ≤ (C.card:ℝ)*K := by
    rw [← partition]
    calc _ ≤ ∑ k ∈ C,‖∑ j ∈ S k,F j‖ := norm_sum_le _ _
         _ ≤ ∑ _k ∈ C,K := sum_le_sum fun k _ => sumcell k
         _ = _ := by simp
  rw [← decomp]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ ((resonant P η).card:ℝ)+(C.card:ℝ)*K := add_le_add bcost gcost
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add (resonant_card P hη.le hη') (mul_le_mul_of_nonneg_right
        (centers_card P hη.le) hK)

/-- A van der Corput block estimate for any phase with a bounded, separated
profile of nonnegative, decreasing downward increments. -/
theorem phase_block {a b : ℕ} {η : ℝ} (ha : P.lo ≤ a) (hb : b ≤ P.hi)
    (hη : 0 < η) (hη' : η ≤ 1) (phase : ℕ → ℝ)
    (diff : ∀ j, phase (j+1) - phase j = -P.gap j) :
    ‖∑ j ∈ Icc a b, ReciprocalFirstDerivative.wave (phase j)‖ ≤
      (P.cap+η+1)*(1+2*η/P.step + (1+1/η)) := by
  apply block_of_safe_cells P ha hb hη hη' (by positivity) _ (by simp)
  intro c d ac cd db k band
  let f (j : ℕ) : ℝ := phase (c+j)
  have decr (j : ℕ) : f (j+1)-f j = -P.gap (c+j) := by
    simpa only [f,← Nat.add_assoc] using diff (c+j)
  have inc (j : ℕ) (hj : j < d-c) : f (j+1)-f j ≤ f (j+2)-f (j+1) := by
    rw [decr j,decr (j+1),neg_le_neg_iff]
    have sep := P.separation (j:=c+j) (k:=c+(j+1)) (by omega) (by omega) (by omega)
    have nonneg : 0 ≤ ((c+(j+1):ℕ):ℝ)-((c+j:ℕ):ℝ) := sub_nonneg.mpr
      (by exact_mod_cast (show c+j ≤ c+(j+1) by omega))
    linarith [mul_nonneg nonneg P.step_pos.le]
  have safe (j : ℕ) (hj : j ≤ d-c) :
      ((-k-1:ℤ):ℝ)+η ≤ f (j+1)-f j ∧ f (j+1)-f j ≤ ((-k-1:ℤ):ℝ)+1-η := by
    have bj := band (c+j) (mem_Icc.mpr ⟨by omega,by omega⟩)
    rw [decr]
    push_cast
    constructor <;> linarith [bj.1,bj.2]
  have h := ReciprocalFirstDerivative.first_difference_bound f (d-c) (-k-1) hη safe inc
  rw [← Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range,show d+1-c = d-c+1 by omega]
  simpa only [f, Nat.add_comm] using h

/-- In the middle-frequency range the generic block estimate has square-root
size. The coefficient K measures the ratio between the largest downward gap
and its guaranteed decrease over M indices. -/
theorem middle_frequency {a b : ℕ} {M K : ℝ} (ha : P.lo ≤ a) (hb : b ≤ P.hi)
    (hM : 0 < M) (hK : 0 < K) (hcap : 1/2 ≤ P.cap) (upper : P.cap ≤ M)
    (curvature : P.cap/(K*M) ≤ P.step) (phase : ℕ → ℝ)
    (diff : ∀ j, phase (j+1)-phase j = -P.gap j) :
    ‖∑ j ∈ Icc a b, ReciprocalFirstDerivative.wave (phase j)‖ ≤
      5*(3+2*K)*Real.sqrt (M*P.cap) := by
  let d := Real.sqrt (P.cap/M)
  have cp : 0 < P.cap := by linarith
  have dp : 0 < d := Real.sqrt_pos.mpr (div_pos cp hM)
  have ds : d^2 = P.cap/M := Real.sq_sqrt (div_nonneg cp.le hM.le)
  have d1 : d ≤ 1 := by
    have hh := (div_le_one hM).mpr upper
    nlinarith
  have raw := phase_block P ha hb dp d1 phase diff
  have h₁ : P.cap+d+1 ≤ 5*P.cap := by linarith
  have sstep := (div_le_iff₀ (mul_pos hK hM)).mp curvature
  have ident := (eq_div_iff hM.ne').mp ds
  have cost : 2*d/P.step ≤ 2*K/d := by
    apply (div_le_div_iff₀ P.step_pos dp).mpr
    have cmp : d^2 ≤ P.step*K := (mul_le_mul_iff_left₀ hM).mp (by linarith [show P.step*(K*M)=P.step*K*M by ring])
    nlinarith
  have h₂ : 1+2*d/P.step+(1+1/d) ≤ (3+2*K)/d := by
    have one : 1 ≤ 1/d := (one_le_div dp).mpr d1
    rw [add_div]
    linarith [show (3:ℝ)/d=3*(1/d) by ring]
  have sp := P.step_pos
  have hh := mul_le_mul h₁ h₂ (by positivity) (by positivity)
  apply raw.trans (hh.trans ?_)
  have r : Real.sqrt (M*P.cap) = M*d := by
    have ms : (M*d)^2 = M*P.cap := by
      calc (M*d)^2 = M*(d^2*M) := by ring
           _ = _ := by rw [ident]
    rw [← ms, Real.sqrt_sq (mul_nonneg hM.le dp.le)]
  have cd : P.cap/d = M*d := (div_eq_iff dp.ne').mpr (by rw [← ident]; ring)
  rw [r]
  apply le_of_eq
  calc 5*P.cap*((3+2*K)/d) = 5*(3+2*K)*(P.cap/d) := by ring
       _ = _ := by rw [cd]

end SeparatedGaps
end
end

-- Source module ReciprocalShiftedBlocks
section

/-! An explicit second-derivative block estimate after arbitrary reciprocal
differencing shifts, specialized to a finite interval of indices. -/
noncomputable section
open Finset ReciprocalFirstDerivative
namespace FactorialReciprocal

/-- Gap profile for all indices between 0 and N after a list of positive shifts. -/
def shiftedProfile (hs : List ℝ) (N : ℕ) {C B : ℝ} (hB : 0 < B)
    (hC : 0 < C) (hn : ∀ t ∈ hs, 0 < t) : SeparatedGaps.Profile := by
  let g (j : ℕ) := C * diffPow (1::hs) 1 (B+j)
  let A := C*((hs.length+1).factorial : ℝ)*hs.prod / B^(hs.length+2)
  let K := C*((hs.length+2).factorial : ℝ)*hs.prod
  let L := K/(B+N+1+hs.sum)^(hs.length+3)
  have hsn : ∀ t ∈ hs, 0 ≤ t := fun t ht => (hn t ht).le
  have hp := List.prod_pos hn
  have hsum := List.sum_nonneg hsn
  have hkp : 0 < K := by dsimp [K]; positivity
  have hlp : 0 < L := by dsimp [L]; positivity
  have gt : ∀ t ∈ ((1:ℝ)::hs), 0 ≤ t := List.forall_mem_cons.mpr ⟨by norm_num,hsn⟩
  have gcap (j : ℕ) : g j ≤ A := by
    have e := (diffPow_bounds (1::hs) 1 (show 0 < B+j by positivity) gt).2
    have ce := mul_le_mul_of_nonneg_left e hC.le
    simp only [List.length_cons,Nat.one_ascFactorial,List.prod_cons,one_mul,
      show 1+(hs.length+1)=hs.length+2 by omega] at ce
    rw [← mul_div_assoc, ← mul_assoc] at ce
    apply ce.trans
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    apply pow_le_pow_left₀ hB.le
    exact le_add_of_nonneg_right (Nat.cast_nonneg j)
  have sep {j k : ℕ} (jk : j ≤ k) (kn : k ≤ N) : ((k:ℝ)-j)*L ≤ g j-g k := by
    let d : ℝ := (k:ℝ)-j
    have d0 : 0 ≤ d := sub_nonneg.mpr (by exact_mod_cast jk)
    have hh : ∀ t ∈ (d::1::hs), 0 ≤ t := List.forall_mem_cons.mpr ⟨d0,gt⟩
    have e := (diffPow_bounds (d::1::hs) 1 (show 0 < B+j by positivity) hh).1
    have ce := mul_le_mul_of_nonneg_left e hC.le
    have idx : B+j+d=B+k := by dsimp [d]; ring
    have ix : B+j+(d+(1+hs.sum)) = B+k+1+hs.sum := by dsimp [d]; ring
    simp only [List.length_cons,Nat.one_ascFactorial,List.prod_cons,one_mul,
      List.sum_cons,show 1+(hs.length+1+1)=hs.length+3 by omega,ix] at ce
    change _ ≤ C * (diffPow (1::hs) 1 (B+j)-diffPow (1::hs) 1 (B+j+d)) at ce
    rw [idx, mul_sub] at ce
    apply le_trans _ ce
    rw [← mul_div_assoc C]
    have coeff : C*((hs.length+1+1).factorial * (d*hs.prod)) = d*K := by dsimp [K]; ring
    rw [coeff]
    change d*(K / _) ≤ d*K/_
    rw [mul_div_assoc d K]
    apply mul_le_mul_of_nonneg_left _ d0
    apply div_le_div_of_nonneg_left hkp.le (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    have kh : (k:ℝ) ≤ N := by exact_mod_cast kn
    linarith
  exact {
    gap := g
    lo := 0
    hi := N
    cap := A
    step := L
    step_pos := hlp
    nonneg := fun j => mul_nonneg hC.le (diffPow_nonneg (1::hs) 1 (by positivity) gt)
    gap_le := fun {j} _ => gcap j
    separation := fun _ jk kn => sep jk kn
  }

private theorem mixed_increment (hs : List ℝ) (C B : ℝ) (j : ℕ) :
    C * diffPow hs 1 (B+(j+1 : ℕ)) - C * diffPow hs 1 (B+j) =
      -(C * diffPow (1::hs) 1 (B+j)) := by
  simp only [Nat.cast_add,Nat.cast_one,diffPow,← add_assoc]
  ring

/-- The optimal endpoints from two mixed reciprocal differences supply
a gap profile for the exponential-sum estimate. -/
theorem shifted_phase_block (hs : List ℝ) (N a b : ℕ) {C B η : ℝ} (hB : 0 < B)
    (hC : 0 < C) (hn : ∀ t ∈ hs, 0 < t) (hb : b ≤ N) (hη : 0 < η) (hη' : η ≤ 1) :
    let A := C*((hs.length+1).factorial : ℝ)*hs.prod / B^(hs.length+2)
    let L := C*((hs.length+2).factorial : ℝ)*hs.prod / (B+N+1+hs.sum)^(hs.length+3)
    ‖∑ j ∈ Icc a b,wave (C*diffPow hs 1 (B+j))‖ ≤
      (A+η+1)*(1+2*η/L+(1+1/η)) := by
  let P := shiftedProfile hs N hB hC hn
  apply SeparatedGaps.phase_block P (Nat.zero_le a) hb hη hη'
  exact mixed_increment hs C B

/-- Square-root cancellation in the regular frequency range of every shifted reciprocal phase.
The spacing ratio K is separated from the numerical endpoints of the block. -/
theorem shifted_middle_frequency (hs : List ℝ) (N a b : ℕ) {C B M K : ℝ}
    (hB : 0 < B) (hC : 0 < C) (hn : ∀ t ∈ hs, 0 < t) (hb : b ≤ N)
    (hM : 0 < M) (hK : 0 < K)
    (lower : 1/2 ≤ (shiftedProfile hs N hB hC hn).cap)
    (upper : (shiftedProfile hs N hB hC hn).cap ≤ M)
    (curvature : (shiftedProfile hs N hB hC hn).cap/(K*M) ≤ (shiftedProfile hs N hB hC hn).step) :
    ‖∑ j ∈ Icc a b,wave (C*diffPow hs 1 (B+j))‖ ≤
      5*(3+2*K)*Real.sqrt (M*(shiftedProfile hs N hB hC hn).cap) := by
  apply SeparatedGaps.middle_frequency (shiftedProfile hs N hB hC hn) (Nat.zero_le a)
    hb hM hK lower upper curvature
  exact mixed_increment hs C B

end FactorialReciprocal
end
end

-- Source module ReciprocalShiftedSums
section

/-! Cancellation in a nonresonant strip after any number of reciprocal
differencing steps. The inverse-frequency constant retains the product
of all shifts. -/
noncomputable section
open Finset ReciprocalFirstDerivative
namespace FactorialReciprocal

/-- An explicit low-frequency bound for every mixed difference of 1/x.
With m shifts, its effective first difference has scale C (m+1)! prod(h) / B^(m+2).
The hypothesis is that the largest such difference is at most one half. -/
theorem shifted_low_frequency (hs : List ℝ) (N : ℕ) {C B : ℝ} (hB : 0 < B)
    (hC : 0 ≤ C) (hn : ∀ a ∈ hs, 0 ≤ a)
    (pos : 0 < C * ((hs.length+1).factorial : ℝ) * hs.prod)
    (small : 2*(C * ((hs.length+1).factorial : ℝ) * hs.prod) ≤ B^(hs.length+2)) :
    ‖∑ j ∈ range (N+1), wave (C * diffPow hs 1 (B+j))‖ ≤
      1+(B+N+1+hs.sum)^(hs.length+2)/(C*((hs.length+1).factorial : ℝ)*hs.prod) := by
  let S := C*((hs.length+1).factorial : ℝ)*hs.prod
  let W := B+N+1+hs.sum
  let a (j : ℕ) := C*diffPow (1::hs) 1 (B+j)
  let δ := S/W^(hs.length+2)
  have hh : ∀ y ∈ ((1:ℝ)::hs), 0 ≤ y := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl|h
    · norm_num
    · exact hn _ h
  have sumh := List.sum_nonneg hn
  have wpos : 0 < W := by dsimp [W]; positivity
  have δpos : 0 < δ := div_pos pos (pow_pos wpos _)
  have ant : Antitone a := by
    intro i j hij
    have e : (i:ℝ) ≤ j := by exact_mod_cast hij
    exact mul_le_mul_of_nonneg_left (diffPow_antitoneOn (1::hs) 1 hh
      (show 0 < B+i by positivity) (show 0 < B+j by positivity) (by linarith)) hC
  have low : δ ≤ a N := by
    have h := (diffPow_bounds (1::hs) 1 (show 0 < B+N by positivity) hh).1
    have v := mul_le_mul_of_nonneg_left h hC
    simp only [List.length_cons,Nat.one_ascFactorial,List.prod_cons,one_mul,
      List.sum_cons,show 1+(hs.length+1)=hs.length+2 by omega] at v
    rw [← mul_div_assoc, ← mul_assoc, show B+N+(1+hs.sum)=W by dsimp [W]; ring] at v
    exact v
  have high : a 0 ≤ 1/2 := by
    have h := (diffPow_bounds (1::hs) 1 hB hh).2
    have v := mul_le_mul_of_nonneg_left h hC
    simp only [List.length_cons,Nat.one_ascFactorial,List.prod_cons,one_mul,
      show 1+(hs.length+1)=hs.length+2 by omega] at v
    rw [← mul_div_assoc, ← mul_assoc] at v
    have cap : S/B^(hs.length+2) ≤ 1/2 := (div_le_iff₀ (pow_pos hB _)).mpr (by dsimp [S]; linarith)
    simpa [a] using v.trans cap
  have gap (j : ℕ) : C*diffPow hs 1 (B+(j+1 : ℕ))-C*diffPow hs 1 (B+j) = -(a j) := by
    simp only [Nat.cast_add,Nat.cast_one,a,diffPow,← add_assoc]
    ring
  have bound := first_difference_bound (fun j => C*diffPow hs 1 (B+j)) N (-1) δpos (by
    intro j hj
    simp only [gap,Int.cast_neg,Int.cast_one]
    have ah := (ant (Nat.zero_le j)).trans high
    have dl := low.trans (ant hj)
    constructor <;> linarith) (by
    intro j _
    rw [gap j,gap (j+1),neg_le_neg_iff]
    exact ant (Nat.le_succ j))
  convert bound using 2
  dsimp [δ,S,W]
  rw [one_div_div]

end FactorialReciprocal
end
end

-- Source module ReciprocalShiftedSquareRoot
section

/-! The square-root exponent pair for reciprocal phases and every
iterated shift of total size at most the base point. -/
noncomputable section
open Finset ReciprocalFirstDerivative
namespace FactorialReciprocal

/-- A square-root estimate on all subintervals, uniform in the scale and shifts.
The displayed constant depends only on the number of differencing steps. -/
theorem shifted_sqrt_of_span (hs : List ℝ) (N a b : ℕ) {C B D : ℝ} (hB : 1 ≤ B)
    (hC : 0 < C) (hn : ∀ t ∈ hs, 0 < t) (hD : 1 ≤ D) (span : B+(N:ℝ)+1+hs.sum ≤ D*B)
    (hN : (N:ℝ) ≤ 2*B) (hb : b ≤ N) :
    let A := (C*((hs.length+1).factorial : ℝ)*hs.prod) / B^(hs.length+2)
    ‖∑ j ∈ Icc a b,wave (C*diffPow hs 1 (B+j))‖ ≤
      25*D^(hs.length+3)*(Real.sqrt (B*A)+1/A) := by
  let Q := C*((hs.length+1).factorial : ℝ)*hs.prod
  let k := hs.length+2
  let A := Q/B^k
  let K := D^(k+1)
  have bp : 0 < B := by linarith
  have hprod := List.prod_pos hn
  have hnn : ∀ t ∈ hs, 0 ≤ t := fun t ht => (hn t ht).le
  have sn := List.sum_nonneg hnn
  have qp : 0 < Q := by dsimp [Q]; positivity
  have ap : 0 < A := by dsimp [A]; positivity
  have kp : 1 ≤ K := one_le_pow₀ hD
  have kd : 0 < K := by linarith
  have pd : 0 < D := by linarith
  have ss := Real.sqrt_nonneg (B*A)
  have inv : 0 < 1/A := by positivity
  have qA : A*B^k=Q := div_mul_cancel₀ _ (pow_pos bp _).ne'
  change _ ≤ 25*K*(Real.sqrt (B*A)+1/A)
  by_cases ab : a ≤ b
  · have ar : (a:ℝ) ≤ b := by exact_mod_cast ab
    have br : (b:ℝ) ≤ N := by exact_mod_cast hb
    by_cases low : A < 1/2
    · have ba : 0 < B+a := by positivity
      have base : B^k ≤ (B+a)^k := pow_le_pow_left₀ bp.le (by linarith [Nat.cast_nonneg (α:=ℝ) a]) _
      have small : 2*Q ≤ (B+a)^k := by
        have e := (div_lt_iff₀ (pow_pos bp k)).mp (show Q/B^k < 1/2 from low)
        linarith
      have h := shifted_low_frequency hs (b-a) ba hC.le hnn qp small
      have castD : ((b-a:ℕ):ℝ) = b-a := Nat.cast_sub ab
      rw [castD,show B+a+((b:ℝ)-a)=B+b by ring] at h
      have bound : (B+b+1+hs.sum)^k ≤ (D*B)^k :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      have fac : (D*B)^k/Q ≤ K/A := by
        rw [mul_pow, show K=D^k*D by dsimp [K]; rw [pow_succ]]
        apply (div_le_div_iff₀ qp ap).mpr
        have mult : D^k*B^k*A=D^k*Q := by rw [← qA]; ring
        rw [mult]
        have pos : 0 ≤ D^k*Q := by positivity
        nlinarith [mul_nonneg (sub_nonneg.mpr hD) pos]
      have hfrac := (div_le_div_of_nonneg_right bound qp.le).trans fac
      have ka : 1 ≤ K/A := (le_div_iff₀ ap).mpr (by linarith)
      rw [← Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range,show b+1-a=b-a+1 by omega]
      simp only [Nat.cast_add]
      have hs' : ‖∑ l ∈ range (b-a+1),wave (C * diffPow hs 1 (B + ((a:ℝ)+l)))‖ ≤ 1+K/A := by
        simpa only [add_assoc] using h.trans (add_le_add le_rfl hfrac)
      apply hs'.trans
      have kr := mul_nonneg (show 0≤K by linarith) ss
      rw [mul_add,show 25*K*(1/A)=25*(K/A) by ring]
      nlinarith
    · by_cases hi : B < A
      · have len : ((Icc a b).card:ℝ) ≤ 3*B := by
          have le : (Icc a b).card ≤ N+1 := by rw [Nat.card_Icc]; omega
          have eh : ((Icc a b).card : ℝ) ≤ (N:ℝ)+1 := by exact_mod_cast le
          linarith
        have root : B ≤ Real.sqrt (B*A) := by
          rw [Real.le_sqrt bp.le (mul_nonneg bp.le ap.le)]
          nlinarith [mul_nonneg bp.le (sub_nonneg.mpr hi.le)]
        calc _ ≤ ∑ j ∈ Icc a b, ‖wave (C*diffPow hs 1 (B+j))‖ := norm_sum_le _ _
             _ = (Icc a b).card := by simp
             _ ≤ 3*B := len
             _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right kp (add_nonneg ss inv.le)]
      · let P := shiftedProfile hs N bp hC hn
        have apEq : P.cap = A := rfl
        have curv : P.cap/(K*B) ≤ P.step := by
          have num : Q ≤ C*((hs.length+2).factorial : ℝ)*hs.prod := by
            apply mul_le_mul_of_nonneg_right _ hprod.le
            apply mul_le_mul_of_nonneg_left _ hC.le
            exact_mod_cast (Nat.factorial_le (show hs.length+1 ≤ hs.length+2 by omega))
          have w : 0 < B+N+1+hs.sum := by positivity
          rw [apEq]
          change A/(K*B) ≤ C*((hs.length+2).factorial : ℝ)*hs.prod / (B+N+1+hs.sum)^(k+1)
          calc _ = Q/(D*B)^(k+1) := by
                 dsimp [A,K]
                 rw [mul_pow, pow_succ B k]
                 field_simp
               _ ≤ _ := div_le_div_of_nonneg_right num (by positivity)
               _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (pow_pos w _)
                         (pow_le_pow_left₀ w.le (by linarith) _)
        have h := shifted_middle_frequency hs N a b bp hC hn hb bp (show 0<K by linarith)
          (le_of_not_gt low) (le_of_not_gt hi) curv
        change _ ≤ 5*(3+2*K)*Real.sqrt (B*A) at h
        apply h.trans
        have c : 5*(3+2*K) ≤ 25*K := by linarith
        exact (mul_le_mul_of_nonneg_right c ss).trans
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right inv.le) (by positivity))
  · rw [Icc_eq_empty ab,sum_empty,norm_zero]
    positivity

theorem shifted_sqrt_bound (hs : List ℝ) (N a b : ℕ) {C B : ℝ} (hB : 1 ≤ B)
    (hC : 0 < C) (hn : ∀ t ∈ hs, 0 < t) (hsum : hs.sum ≤ B)
    (hN : (N:ℝ) ≤ 2*B) (hb : b ≤ N) :
    let A := (C*((hs.length+1).factorial : ℝ)*hs.prod) / B^(hs.length+2)
    ‖∑ j ∈ Icc a b,wave (C*diffPow hs 1 (B+j))‖ ≤
      25*(5:ℝ)^(hs.length+3)*(Real.sqrt (B*A)+1/A) := by
  apply shifted_sqrt_of_span hs N a b hB hC hn (by norm_num : (1:ℝ) ≤ 5) (by linarith) hN hb

/-- Two arbitrary shifts of size at most B are covered by the larger span constant six. -/
theorem shifted_sqrt_bound_two (hs : List ℝ) (N a b : ℕ) {C B : ℝ} (hB : 1 ≤ B)
    (hC : 0 < C) (hn : ∀ t ∈ hs, 0 < t) (hsum : hs.sum ≤ 2*B)
    (hN : (N:ℝ) ≤ 2*B) (hb : b ≤ N) :
    let A := (C*((hs.length+1).factorial : ℝ)*hs.prod) / B^(hs.length+2)
    ‖∑ j ∈ Icc a b,wave (C*diffPow hs 1 (B+j))‖ ≤
      25*(6:ℝ)^(hs.length+3)*(Real.sqrt (B*A)+1/A) := by
  apply shifted_sqrt_of_span hs N a b hB hC hn (by norm_num : (1:ℝ) ≤ 6) (by linarith) hN hb

end FactorialReciprocal
end
end

-- Source module ReciprocalFirstA
section

/-! Parameter optimization for a van der Corput A-step after a square-root
estimate. Below the crossover the original bound is sufficient. Above it
the single worst inverse-lag error fits into the diagonal budget. -/

noncomputable section
namespace ReciprocalAProcess

/-- The integer differencing scale in a square-root to one-sixth transition.
Here X denotes frequency divided by the square of the denominator scale M. -/
theorem first_A {M X K S : ℝ} {N : ℕ} (hM : 1 ≤ M) (hX : 0 < X)
    (hK : 1 ≤ K) (len : (N:ℝ) ≤ 3*M) (trivial : S ≤ N)
    (base : S ≤ K*(Real.sqrt (M*X)+1/X))
    (shifted : ∀ H : ℕ, 1 ≤ H → (H:ℝ) ≤ M →
      (H:ℝ)*S^2 ≤ ((N:ℝ)+H)*((N:ℝ)+H*K*(Real.sqrt (H*X)+M/X))) :
    S ≤ 8*K*(M^(2/3:ℝ)*X^(1/6:ℝ)+1/X) := by
  have m : 0<M := by linarith
  have kp : 0<K := by linarith
  let T := (M*X)^(1/3:ℝ)
  let W := Real.sqrt (M*T)
  have tp : 0<T := Real.rpow_pos_of_pos (mul_pos m hX) _
  have wp : 0<W := Real.sqrt_pos.mpr (mul_pos m tp)
  have cube : T^3=M*X := by
    dsimp [T]
    rw [← Real.rpow_mul_natCast (mul_nonneg m.le hX.le)]
    norm_num
  have ws : W^2=M*T := Real.sq_sqrt (mul_nonneg m.le tp.le)
  have powers : W=M^(2/3:ℝ)*X^(1/6:ℝ) := by
    dsimp [W,T]
    rw [Real.sqrt_eq_rpow,Real.mul_rpow m.le (by positivity),← Real.rpow_mul (by positivity),
      Real.mul_rpow m.le hX.le,← mul_assoc,← Real.rpow_add m]
    norm_num
  rw [← powers]
  have invpos : 0<1/X := one_div_pos.mpr hX
  have costnon : 0 ≤ K*(W+1/X) := by positivity
  by_cases small : X^2≤M
  · have XT : X≤T := by
      apply le_of_not_gt
      intro lt
      have q := pow_lt_pow_left₀ lt tp.le (by decide : 3≠0)
      nlinarith [mul_le_mul_of_nonneg_right small hX.le]
    have Wb : Real.sqrt (M*X) ≤ W := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left XT m.le)
    have := base.trans (mul_le_mul_of_nonneg_left (add_le_add Wb (le_refl (1/X))) kp.le)
    nlinarith only [this,costnon]
  by_cases high : M^2≤X
  · have MT : M≤T := by
      by_contra! lt
      have q := pow_lt_pow_left₀ lt tp.le (by decide : 3≠0)
      nlinarith [mul_le_mul_of_nonneg_left high m.le]
    have MW : M≤W := by
      by_contra! lt
      have q := pow_lt_pow_left₀ lt wp.le (by decide : 2≠0)
      nlinarith [mul_le_mul_of_nonneg_left MT m.le]
    have Wle := mul_le_mul_of_nonneg_right hK (show 0≤W+1/X by positivity)
    nlinarith only [trivial,len,MW,invpos.le,Wle,costnon]
  have sx : M<X^2 := lt_of_not_ge small
  have lx : X<M^2 := lt_of_not_ge high
  have x1 : 1≤X := by
    by_contra! bad
    have q := mul_lt_mul_of_pos_right bad hX
    nlinarith
  have t1 : 1≤T := by
    by_contra! lt
    have q := pow_lt_pow_left₀ lt tp.le (by decide : 3≠0)
    nlinarith [mul_le_mul hM x1 (by norm_num) m.le]
  have tm : T≤M := by
    by_contra! lt
    have q := pow_lt_pow_left₀ lt m.le (by decide : 3≠0)
    nlinarith [mul_lt_mul_of_pos_left lx m]
  have invcost : M/X ≤ T := by
    apply (div_le_iff₀ hX).mpr
    by_contra! lt
    have q := pow_lt_pow_left₀ lt (mul_nonneg tp.le hX.le) (by decide : 3≠0)
    rw [mul_pow,cube] at q
    have sqbound := mul_lt_mul_of_pos_right sx (by positivity : 0<X^2)
    have msq := mul_lt_mul_of_pos_left sx m
    have mc := mul_lt_mul_of_pos_left (msq.trans sqbound) m
    nlinarith only [q,mc]
  let H := ⌊M/T⌋₊
  have ratio : 1≤M/T := (one_le_div tp).mpr tm
  have hH : 1≤H := Nat.floor_pos.mpr ratio
  have hp : (0:ℝ)<H := by exact_mod_cast hH
  have hfloor : (H:ℝ) ≤ M/T := Nat.floor_le (div_nonneg m.le tp.le)
  have hMT : (H:ℝ)*T ≤ M := (le_div_iff₀ tp).mp hfloor
  have hcap : (H:ℝ) ≤ M := hfloor.trans (div_le_self m.le t1)
  have upper : M ≤ 2*(H:ℝ)*T := by
    have q := Nat.lt_floor_add_one (M/T)
    have z : M/T < 2*H := by linarith [show (1:ℝ) ≤ H by exact_mod_cast hH]
    exact (div_lt_iff₀ tp).mp z |>.le
  have growth : Real.sqrt ((H:ℝ)*X) ≤ T := by
    have h := mul_le_mul_of_nonneg_right hMT hX.le
    have hx : (H:ℝ)*X ≤ T^2 := (le_of_mul_le_mul_right (by
      calc _ = (H:ℝ)*T*X := by ring
           _ ≤ M*X := h
           _ = T^2*T := by rw [← cube]; ring) tp)
    exact (Real.sqrt_le_iff).mpr ⟨tp.le,hx⟩
  have raw := shifted H hH hcap
  have c1 : (N:ℝ)+H ≤ 4*M := by linarith
  have c2 : (N:ℝ)+H*K*(Real.sqrt ((H:ℝ)*X)+M/X) ≤ (H:ℝ)*T*(6+2*K) := by
    have c := mul_le_mul_of_nonneg_left (add_le_add growth invcost) (mul_nonneg hp.le kp.le)
    nlinarith only [c,len,upper]
  have rhs := mul_le_mul c1 c2 (by positivity) (by positivity)
  have ss : S^2 ≤ (4*M*T)*(6+2*K) := by
    apply le_of_mul_le_mul_left _ hp
    apply raw.trans (rhs.trans_eq ?_)
    ring
  have Ksq : 1≤K^2 := by nlinarith [sq_nonneg (K-1)]
  have ksq2 : K ≤ K^2 := by nlinarith [mul_nonneg kp.le (sub_nonneg.mpr hK)]
  have main : S ≤ 8*K*W := by
    by_contra! lt
    have q := pow_lt_pow_left₀ lt (by positivity : 0 ≤ 8*K*W) (by decide : 2≠0)
    have bound : 4*(6+2*K) ≤ 64*K^2 := by linarith
    have big := mul_le_mul_of_nonneg_right bound (mul_nonneg m.le tp.le)
    rw [mul_pow,mul_pow,ws] at q
    nlinarith only [q,big,ss]
  have add := mul_nonneg kp.le invpos.le
  nlinarith only [main,add]


/-- A shifted square-root bound yields the exponent pair (1/6,2/3)
on the original finite exponential sum. -/
theorem first_A_character (p : ℕ → ℝ) (N : ℕ) {M X K : ℝ}
    (hM : 1≤M) (hX : 0<X) (hK : 1≤K) (len : (N:ℝ) ≤ 3*M)
    (base : ‖∑ j ∈ Finset.range N, FactorialDifferencing.character (p j)‖ ≤
      K*(Real.sqrt (M*X)+1/X))
    (shifts : ∀ d : ℕ, 0<d → (d:ℝ) ≤ M →
      ‖∑ j ∈ Finset.range (N-d),FactorialDifferencing.character (p (j+d)-p j)‖ ≤
        K*(Real.sqrt ((d:ℝ)*X)+M/((d:ℝ)*X))) :
    ‖∑ j ∈ Finset.range N,FactorialDifferencing.character (p j)‖ ≤
      8*K*(M^(2/3:ℝ)*X^(1/6:ℝ)+1/X) := by
  refine first_A hM hX hK len ?_ base ?_
  · calc _ ≤ ∑ j ∈ Finset.range N, ‖FactorialDifferencing.character (p j)‖ := norm_sum_le _ _
         _ = (N:ℝ) := by simp only [show ∀ x, ‖FactorialDifferencing.character x‖=1 from
           fun x => Complex.norm_exp_ofReal_mul_I _, Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
  intro H hH hcap
  let E := K*(Real.sqrt ((H:ℝ)*X)+M/X)
  have pos : (0:ℝ)<H := by exact_mod_cast hH
  have epos : 0≤E := by dsimp [E]; positivity
  have each (d : ℕ) (hd : 0<d) (dh : d<H) :
      ‖∑ j ∈ Finset.range (N-d),FactorialDifferencing.character (p (j+d)-p j)‖ ≤ E := by
    have dx : (d:ℝ) ≤ H := by exact_mod_cast dh.le
    have d1 : (1:ℝ) ≤ d := by exact_mod_cast hd
    apply (shifts d hd (dx.trans hcap)).trans
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply add_le_add (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right dx hX.le))
    apply div_le_div_of_nonneg_left (by linarith) hX
    simpa using mul_le_mul_of_nonneg_right d1 hX.le
  have c := FactorialDifferencing.uniform_differencing p N H hH E each
  have fa : ((N+H-1:ℕ):ℝ) ≤ (N:ℝ)+H := by exact_mod_cast (show N+H-1 ≤ N+H by omega)
  have h₁ : 1 ≤ (H:ℝ) := by exact_mod_cast hH
  have fb : (N:ℝ)+((H:ℝ)-1)*E ≤ N+H*K*(Real.sqrt (H*X)+M/X) := by
    rw [mul_assoc]
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_right (by linarith) epos
  exact c.trans (mul_le_mul fa fb (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (sub_nonneg.mpr h₁) epos))
    (by positivity))

end ReciprocalAProcess
end
end

-- Source module ReciprocalShiftedFirstA
section

/-! An actual reciprocal exponential sum, after any fixed number of shifts,
satisfies the exponent-pair estimate (1/6, 2/3). The inverse-frequency cost
retains every shift. -/
noncomputable section
open Finset Real ReciprocalFirstDerivative
open scoped ComplexConjugate
namespace FactorialReciprocal

/-- Effective first-difference size for a reciprocal phase with shifts. -/
def effectiveSlope (hs : List ℝ) (C B : ℝ) : ℝ :=
  (C*((hs.length+1).factorial : ℝ)*hs.prod)/B^(hs.length+2)

def firstAWeight (hs : List ℝ) : ℝ :=
  25*(6:ℝ)^(hs.length+4)*((hs.length:ℝ)+2)

theorem character_eq_wave (x : ℝ) : FactorialDifferencing.character x = wave x := by
  unfold FactorialDifferencing.character wave
  congr 1
  push_cast
  ring

theorem wave_neg_eq_star (x : ℝ) : wave (-x) = star (wave x) := by
  unfold wave
  change _ = conj _
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul,Complex.ofReal_neg,Complex.conj_ofReal,Complex.conj_I,map_ofNat]
  ring

theorem effectiveSlope_cons {B C : ℝ} (hs : List ℝ) (d : ℝ) (hB : 0 < B) :
    effectiveSlope (d::hs) C B = ((hs.length:ℝ)+2)*d*effectiveSlope hs C B/B := by
  dsimp [effectiveSlope]
  rw [Nat.factorial_succ (hs.length+1),show hs.length+1+2=hs.length+2+1 by omega,
      pow_succ B (hs.length+2)]
  push_cast
  field_simp
  ring

private lemma sqrt_range (hs : List ℝ) (N : ℕ) {C B : ℝ} (hB : 1 ≤ B)
    (hC : 0 < C) (pos : ∀ t ∈ hs, 0 < t) (sum : hs.sum ≤ 2*B) (len : (N:ℝ) ≤ 2*B+1) :
    ‖∑ j ∈ range N, wave (C*diffPow hs 1 (B+j))‖ ≤
      25*(6:ℝ)^(hs.length+3)*(sqrt (B*effectiveSlope hs C B)+1/effectiveSlope hs C B) := by
  have bp : 0 < B := by linarith
  have xp : 0 < effectiveSlope hs C B := by
    have ph := List.prod_pos pos
    dsimp [effectiveSlope]; positivity
  cases N with
  | zero => simp only [range_zero,sum_empty,norm_zero]; positivity
  | succ n =>
    rw [Nat.range_succ_eq_Icc_zero]
    exact shifted_sqrt_bound_two hs n 0 n hB hC pos sum (by push_cast at len; linarith) le_rfl

/-- The first A-process estimate for any mixed difference of the reciprocal.
For each additional differencing lag d≤B the total shift in the square-root
estimate is at most 2B. -/
theorem shifted_first_A (hs : List ℝ) (N : ℕ) {C B : ℝ} (hB : 1 ≤ B)
    (hC : 0 < C) (pos : ∀ t ∈ hs, 0 < t) (sum : hs.sum ≤ B)
    (len : (N:ℝ) ≤ 2*B+1) :
    ‖∑ j ∈ range N, wave (C*diffPow hs 1 (B+j))‖ ≤
      8*firstAWeight hs*(B^(2/3:ℝ)*(effectiveSlope hs C B)^(1/6:ℝ)+1/effectiveSlope hs C B) := by
  let X := effectiveSlope hs C B
  let U := (hs.length:ℝ)+2
  let L := 25*(6:ℝ)^(hs.length+4)
  have bp : 0 < B := by linarith
  have xp : 0<X := by
    have ph := List.prod_pos pos
    dsimp [X,effectiveSlope]; positivity
  have up : 1 ≤ U := by dsimp [U]; linarith [Nat.cast_nonneg (α:=ℝ) hs.length]
  have lp : 1 ≤ L := by
    have h : 1≤(6:ℝ)^(hs.length+4) := one_le_pow₀ (by norm_num)
    dsimp [L]; linarith
  have weight_eq : firstAWeight hs = L*U := rfl
  have kp : 1 ≤ firstAWeight hs := weight_eq ▸ one_le_mul_of_one_le_of_one_le lp up
  let p (j : ℕ) := C*diffPow hs 1 (B+j)
  have base : ‖∑ j ∈ range N, FactorialDifferencing.character (p j)‖ ≤
      firstAWeight hs*(sqrt (B*X)+1/X) := by
    simp only [character_eq_wave,p]
    apply (sqrt_range hs N hB hC pos (by linarith) len).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity : 0 ≤ sqrt (B*X)+1/X)
    have inc : (6:ℝ)^(hs.length+3) ≤ 6^(hs.length+4) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have lku : L ≤ L*U := by simpa using mul_le_mul_of_nonneg_left up (by linarith : 0 ≤ L)
    rw [weight_eq]
    exact (mul_le_mul_of_nonneg_left inc (by norm_num)).trans lku
  have shifts (d : ℕ) (hd : 0<d) (dh : (d:ℝ) ≤ B) :
      ‖∑ j ∈ range (N-d), FactorialDifferencing.character (p (j+d)-p j)‖ ≤
      firstAWeight hs*(sqrt ((d:ℝ)*X)+B/((d:ℝ)*X)) := by
    have dp : 0 < (d:ℝ) := by exact_mod_cast hd
    have xp' : 0 < (d:ℝ)*X := mul_pos dp xp
    have pos' : ∀ t ∈ (d:ℝ)::hs, 0<t := by
      intro t ht; rcases List.mem_cons.mp ht with rfl|h
      · exact dp
      · exact pos _ h
    have sz : ((N-d:ℕ):ℝ) ≤ 2*B+1 :=
      (show ((N-d:ℕ):ℝ) ≤ N by exact_mod_cast Nat.sub_le N d).trans len
    have orig := sqrt_range ((d:ℝ)::hs) (N-d) hB hC pos' (by simp; linarith) sz
    have phase (j : ℕ) : FactorialDifferencing.character (p (j+d)-p j) =
        star (wave (C*diffPow ((d:ℝ)::hs) 1 (B+j))) := by
      rw [character_eq_wave,← wave_neg_eq_star]
      congr 1
      dsimp [p,diffPow]
      push_cast
      rw [← add_assoc]; ring
    simp_rw [phase]
    rw [←star_sum,norm_star]
    apply orig.trans
    have eq : effectiveSlope ((d:ℝ)::hs) C B = U*((d:ℝ)*X)/B := by
      rw [effectiveSlope_cons hs _ bp]; dsimp [X,U]; ring
    rw [eq]
    have baseEq : B*(U*((d:ℝ)*X)/B)=U*((d:ℝ)*X) := by field_simp
    have su : sqrt U ≤ U := (Real.sqrt_le_iff).mpr
      ⟨by linarith,by nlinarith [mul_nonneg (sub_nonneg.mpr up) (by linarith : 0≤U)]⟩
    have rt : sqrt (B*(U*((d:ℝ)*X)/B)) ≤ U*sqrt ((d:ℝ)*X) := by
      rw [baseEq,Real.sqrt_mul (by linarith : 0≤U)]
      exact mul_le_mul_of_nonneg_right su (Real.sqrt_nonneg _)
    have denom : (d:ℝ)*X ≤ U*((d:ℝ)*X) := by simpa using mul_le_mul_of_nonneg_right up xp'.le
    have inv : 1/(U*((d:ℝ)*X)/B) ≤ U*(B/((d:ℝ)*X)) := by
      rw [one_div_div]
      apply (div_le_div_of_nonneg_left bp.le xp' denom).trans
      simpa using mul_le_mul_of_nonneg_right up (div_nonneg bp.le xp'.le)
    change L*(sqrt (B*(U*((d:ℝ)*X)/B))+1/(U*((d:ℝ)*X)/B)) ≤ _
    calc _ ≤ L*(U*sqrt ((d:ℝ)*X)+U*(B/((d:ℝ)*X))) :=
           mul_le_mul_of_nonneg_left (add_le_add rt inv) (by linarith)
         _ = _ := by rw [weight_eq]; ring
  have raw := ReciprocalAProcess.first_A_character p N hB xp kp (by linarith) base shifts
  simpa only [character_eq_wave,p,X] using raw

/-- The first A-process exponent pair for the unshifted reciprocal with an
explicit absolute constant. B may be real, and the length is an integer. -/
theorem reciprocal_first_A {B Y : ℝ} (N : ℕ) (hB : 1 ≤ B) (hY : 0 < Y)
    (len : (N:ℝ) ≤ 2*B+1) :
    ‖∑ j ∈ range N, wave (Y/(B+j))‖ ≤
      518400*(B^(2/3:ℝ)*(Y/B^2)^(1/6:ℝ)+B^2/Y) := by
  have h := shifted_first_A [] N hB hY (by simp) (by simp; linarith) len
  norm_num [diffPow,effectiveSlope,firstAWeight,div_eq_mul_inv] at h ⊢
  exact h

/-- Natural endpoints for reindexing a sieve sum, including empty blocks. -/
theorem reciprocal_first_A_Icc {M b : ℕ} {Y : ℝ} (hm : 1 ≤ M) (hy : 0 < Y)
    (hb : b ≤ 3*M) :
    ‖∑ q ∈ Icc M b, wave (Y/(q:ℝ))‖ ≤
      518400*((M:ℝ)^(2/3:ℝ)*(Y/(M:ℝ)^2)^(1/6:ℝ)+(M:ℝ)^2/Y) := by
  have len : b+1-M ≤ 2*M+1 := by omega
  have bound := reciprocal_first_A (b+1-M) (by exact_mod_cast hm : (1:ℝ)≤M) hy
    (by exact_mod_cast len)
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simpa only [Nat.cast_add] using bound

end FactorialReciprocal
end
end

-- Source module ReciprocalSecondA
section

/-! A second van der Corput differencing step for reciprocal exponential sums,
giving the concrete (1/14,11/14) exponent pair with an absolute constant. -/

noncomputable section
open Finset Real ReciprocalFirstDerivative
namespace FactorialReciprocal

/-- Uniform (1/14,11/14) estimate for a reciprocal phase on a real-base
block. The length N can be zero and is bounded by 2B+1. -/
theorem reciprocal_second_A {B Y : ℝ} (N : ℕ) (hB : 1 ≤ B) (hY : 0 < Y)
    (len : (N:ℝ) ≤ 2*B+1) :
    ‖∑ j ∈ range N, wave (Y/(B+j))‖ ≤
      80000000*(B^(11/14:ℝ)*(Y/B^2)^(1/14:ℝ)+B^2/Y) := by
  let X := Y/B^2
  let p (j : ℕ) := Y/(B+j)
  have bp : 0 < B := by linarith
  have xp : 0 < X := by dsimp [X]; positivity
  have inv : 1/X = B^2/Y := by dsimp [X]; rw [one_div_div]
  have previous : ‖∑ j ∈ range N, FactorialDifferencing.character (p j)‖ ≤
      10000000*(B^(2/3:ℝ)*X^(1/6:ℝ)+1/X) := by
    simp only [character_eq_wave,p]
    apply (reciprocal_first_A N hB hY len).trans
    rw [inv]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have each (d : ℕ) (hd : 1 ≤ d) (dh : (d:ℝ) ≤ B) :
      ‖∑ j ∈ range (N-d), FactorialDifferencing.character (p (j+d)-p j)‖ ≤
      10000000*(B^(1/2:ℝ)*((d:ℝ)*X)^(1/6:ℝ)+B/((d:ℝ)*X)) := by
    have dp : 0 < (d:ℝ) := by exact_mod_cast (show 0<d by omega)
    have wp : 0 < (d:ℝ)*X := mul_pos dp xp
    have len' : ((N-d:ℕ):ℝ) ≤ 2*B+1 :=
      (show ((N-d:ℕ):ℝ) ≤ (N:ℝ) by exact_mod_cast Nat.sub_le N d).trans len
    have raw := shifted_first_A [(d:ℝ)] (N-d) hB hY (by simpa using dp) (by simpa using dh) len'
    have phase (j : ℕ) : FactorialDifferencing.character (p (j+d)-p j) =
        star (wave (Y*diffPow [(d:ℝ)] 1 (B+j))) := by
      rw [character_eq_wave,← wave_neg_eq_star]
      congr 1
      dsimp [p,diffPow]
      push_cast
      simp only [pow_one,div_eq_mul_inv,add_assoc]
      ring
    simp_rw [phase]
    rw [← star_sum, norm_star]
    apply raw.trans
    have slope : effectiveSlope [(d:ℝ)] Y B = 2*((d:ℝ)*X)/B := by
      rw [effectiveSlope_cons [] _ bp]
      norm_num [effectiveSlope,X]
      ring
    rw [slope]
    have c2 : (2:ℝ)^(1/6:ℝ) ≤ 2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        (by norm_num : (1/6:ℝ) ≤ 1)
    have power : B^(2/3:ℝ)*(2*((d:ℝ)*X)/B)^(1/6:ℝ) =
        (2:ℝ)^(1/6:ℝ)*(B^(1/2:ℝ)*((d:ℝ)*X)^(1/6:ℝ)) := by
      have wp' : 0 < 2*((d:ℝ)*X) := by positivity
      have up : 0 < 2*((d:ℝ)*X)/B := div_pos wp' bp
      apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
      rw [Real.log_mul (rpow_pos_of_pos bp _).ne' (rpow_pos_of_pos up _).ne',
        Real.log_mul (rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).ne' (by positivity),
        Real.log_mul (rpow_pos_of_pos bp _).ne' (rpow_pos_of_pos wp _).ne',
        Real.log_rpow bp,Real.log_rpow bp,Real.log_rpow up,
        Real.log_rpow (by norm_num : (0:ℝ)<2),Real.log_rpow wp,
        Real.log_div wp'.ne' bp.ne',Real.log_mul (by norm_num : (2:ℝ)≠0) wp.ne']
      ring
    have denom : 1/(2*((d:ℝ)*X)/B) ≤ B/((d:ℝ)*X) := by
      rw [one_div_div]
      exact div_le_div_of_nonneg_left bp.le wp (by linarith)
    let V := B^(1/2:ℝ)*((d:ℝ)*X)^(1/6:ℝ)
    let W := B/((d:ℝ)*X)
    have vp : 0 ≤ V := by dsimp [V]; positivity
    have w0 : 0 ≤ W := by dsimp [W]; positivity
    rw [power]
    change 8*firstAWeight [(d:ℝ)]*((2:ℝ)^(1/6:ℝ)*V+1/(2*((d:ℝ)*X)/B)) ≤ 10000000*(V+W)
    have coeff : 8*firstAWeight [(d:ℝ)] = 4665600 := by norm_num [firstAWeight]
    rw [coeff]
    calc _ ≤ 4665600*(2*V+W) := mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_right c2 vp) denom) (by norm_num)
         _ ≤ _ := by linarith
  have result := FactorialDifferencing.second_A_of_differences p hB xp
    (by norm_num : (1:ℝ) ≤ 10000000) (by linarith : (N:ℝ) ≤ 3*B) previous each
  rw [inv] at result
  norm_num only [show (8:ℝ)*10000000=80000000 by norm_num] at result
  simpa only [p,X,character_eq_wave] using result

/-- The natural-endpoint version used when reindexing multiples in the
sawtooth Fourier sums. The endpoints may define an empty interval. -/
theorem reciprocal_second_A_Icc {M b : ℕ} {Y : ℝ} (hm : 1 ≤ M) (hy : 0 < Y)
    (hb : b ≤ 3*M) :
    ‖∑ q ∈ Icc M b, wave (Y/(q:ℝ))‖ ≤
      80000000*((M:ℝ)^(11/14:ℝ)*(Y/(M:ℝ)^2)^(1/14:ℝ)+(M:ℝ)^2/Y) := by
  have le : b+1-M ≤ 2*M+1 := by omega
  have bound := reciprocal_second_A (b+1-M) (by exact_mod_cast hm : (1:ℝ) ≤ M) hy
    (by exact_mod_cast le)
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simpa only [Nat.cast_add] using bound

end FactorialReciprocal
end
end

-- Source module ReciprocalALocal
section

/-! Uniform individual-modulus sawtooth bounds for the two exponent pairs
obtained by one and two applications of van der Corput differencing. -/
noncomputable section
open Finset Real
namespace FactorialFourier

private theorem local_of_pair {k l C D u v : ℝ} {x t : ℕ}
    (block : ∀ {B Y : ℝ} (N : ℕ), 1 ≤ B → 0 < Y → (N:ℝ) ≤ 2*B+1 →
      ‖∑ i ∈ range N, ReciprocalFirstDerivative.wave (Y/(B+i))‖ ≤
        C*(B^l*(Y/B^2)^k+B^2/Y))
    (hk : 0 < k) (hk1 : k < 1) (hC : 1 ≤ C) (lo : 0 ≤ l-2*k) (hi : l-2*k ≤ 1)
    (cap : (1+(1/k+1/(1-k))/2)*(3*(2*C)) ≤ D)
    (hx : 0 < x) (ht : 0 < t) (htu : (t:ℝ) ≤ u) (huv : u ≤ v) (hv : v ≤ 3*u) :
    |FactorialSieve.remainder u v x t| ≤ D*(x:ℝ)^(k/(1+k))*u^((l-k)/(1+k))*
      (t:ℝ)^(-l/(1+k)) + (4*C)*u^2/((x:ℝ)*t) := by
  let N : ℝ := ((Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·)).card
  let E := (2*C)*(x:ℝ)^k*u^(l-2*k)*(t:ℝ)^(k-l)
  let F := (4*C)*u^2/((x:ℝ)*t)
  let c := (1/k+1/(1-k))/2
  have cp : 0 ≤ C := zero_le_one.trans hC
  have tp : (0:ℝ) < t := by exact_mod_cast ht
  have xp : (0:ℝ) < x := by exact_mod_cast hx
  have up := tp.trans_le htu
  have cn : 0 ≤ c := by dsimp [c]; have := sub_pos.mpr hk1; positivity
  have n0 : 0 ≤ N := by dsimp [N]; positivity
  have e0 : 0 ≤ E := by dsimp [E]; positivity
  have f0 : 0 ≤ F := by dsimp [F]; positivity
  have budget (H : ℕ) (hh : 1 ≤ H) :
      |FactorialSieve.remainder u v x t| ≤ N/(2*(H:ℝ)) + c*E*(H:ℝ)^k + F := by
    have b := reciprocal_transfer u v x t H hh E F k e0 f0 hk hk1
      (fun j hj => window_exponential_of_pair block cp lo hi hx ht hj htu huv hv)
    apply b.trans_eq
    dsimp only [N,c]; ring
  have opt := optimize_power n0 e0 f0 cn hk (remainder_le_half_card u v x t) budget
  have scale := rescale_local_power (l:=l) n0 e0 (show 1≤2*C by linarith) xp up tp hk.le
    (multiple_window_card ht htu huv hv) (show E ≤ (2*C)*(x:ℝ)^k*u^(l-2*k)*(t:ℝ)^(k-l) from le_rfl)
  have cap' : (1+c)*(3*(2*C)) ≤ D := cap
  calc
    _ ≤ (1+c)*((3*(2*C))*(x:ℝ)^(k/(1+k))*u^((l-k)/(1+k))*(t:ℝ)^(-l/(1+k)))+F :=
      opt.trans (add_le_add (mul_le_mul_of_nonneg_left scale (by linarith)) le_rfl)
    _ = ((1+c)*(3*(2*C)))*(x:ℝ)^(k/(1+k))*u^((l-k)/(1+k))*(t:ℝ)^(-l/(1+k))+F := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right cap' (by positivity)) (by positivity)) (by positivity)) le_rfl

/-- The one-sixth exponent pair yields the middle band estimate. -/
theorem reciprocal_middle_local {x t : ℕ} {u v : ℝ} (hx : 0 < x) (ht : 0 < t)
    (htu : (t:ℝ) ≤ u) (huv : u ≤ v) (hv : v ≤ 3*u) :
    |FactorialSieve.remainder u v x t| ≤
      15000000*(x:ℝ)^(1/7:ℝ)*u^(3/7:ℝ)*(t:ℝ)^(-(4/7:ℝ)) + 2073600*u^2/((x:ℝ)*t) := by
  have h := local_of_pair (k:=1/6) (l:=2/3) (C:=518400) (D:=15000000)
    (@FactorialReciprocal.reciprocal_first_A) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hx ht htu huv hv
  norm_num at h ⊢
  exact h

/-- Two A-process steps yield the estimate for the lowest band. -/
theorem reciprocal_lower_local {x t : ℕ} {u v : ℝ} (hx : 0 < x) (ht : 0 < t)
    (htu : (t:ℝ) ≤ u) (huv : u ≤ v) (hv : v ≤ 3*u) :
    |FactorialSieve.remainder u v x t| ≤
      5000000000*(x:ℝ)^(1/15:ℝ)*u^(2/3:ℝ)*(t:ℝ)^(-(11/15:ℝ)) + 320000000*u^2/((x:ℝ)*t) := by
  have h := local_of_pair (k:=1/14) (l:=11/14) (C:=80000000) (D:=5000000000)
    (@FactorialReciprocal.reciprocal_second_A) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hx ht htu huv hv
  norm_num at h ⊢
  exact h

end FactorialFourier
end
end

-- Source module ReciprocalProvedBandInputs
section

/-! Whole-band prime-count estimates obtained from the first and second
van der Corput A-process reciprocal estimates. -/
noncomputable section
open Real
namespace FactorialLowerBands

private theorem uniform_of_explicit (p q s C D : ℝ) (hC : 0 < C) (hD : D ≤ C)
    (block : ∀ {x t : ℕ} {u v : ℝ}, 0 < x → 0 < t → (t:ℝ) ≤ u → u ≤ v → v ≤ 3*u →
      |FactorialSieve.remainder u v x t| ≤ 
        C*(x:ℝ)^p*u^q*(t:ℝ)^(-s) + D*u^2/((x:ℝ)*t)) : FactorialDyadic.UniformSaw p q s := by
  refine ⟨C,hC,?_⟩
  intro x t hx ht u v htu huv hv
  have tp : 0 < (t:ℝ) := by exact_mod_cast ht
  have up := tp.trans_le htu
  apply (block hx ht htu huv (by linarith)).trans
  have bound := mul_le_mul_of_nonneg_right hD (show 0 ≤ u^2/((x:ℝ)*t) by positivity)
  linarith only [bound,show C*((x:ℝ)^p*u^q*(t:ℝ)^(-s)+u^2/((x:ℝ)*t)) =
    C*(x:ℝ)^p*u^q*(t:ℝ)^(-s) + C*(u^2/((x:ℝ)*t)) by ring,
    show D*u^2/((x:ℝ)*t) = D*(u^2/((x:ℝ)*t)) by ring]

/-- Whole-band estimate using the exponent pair (1/6, 2/3). -/
theorem middle_band_bound : BandBound (1/7) (3/7) (4/7) :=
  FactorialDyadic.prime_band_from_saw _ _ _ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (uniform_of_explicit _ _ _ 15000000 2073600 (by norm_num) (by norm_num)
      @FactorialFourier.reciprocal_middle_local)

/-- Whole-band estimate using the exponent pair (1/14, 11/14). -/
theorem lower_band_bound : BandBound (1/15) (2/3) (11/15) :=
  FactorialDyadic.prime_band_from_saw _ _ _ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (uniform_of_explicit _ _ _ 5000000000 320000000 (by norm_num) (by norm_num)
      @FactorialFourier.reciprocal_lower_local)

end FactorialLowerBands
end
end

-- Source module ReciprocalLowerBandRates
section

/-! Fixed rational sieve levels for the two lower exponent-pair ranges.
A level below the critical value leaves strict power savings in the error
terms and an arbitrarily small fixed loss in the prime-count coefficient. -/
noncomputable section
open Real Filter Finset
namespace FactorialLowerBands
open ReciprocalBandRates

private lemma admissible_level {X g a : ℝ} (hX : 1≤X) (hg : 0<g) (hga : 2*g≤a) :
    1≤⌊X^g⌋₊ ∧ ((⌊X^g⌋₊:ℕ):ℝ)^2 ≤ X^a := by
  have xp := zero_lt_one.trans_le hX
  refine ⟨Nat.floor_pos.mpr (Real.one_le_rpow hX hg.le),?_⟩
  calc _ ≤ (X^g)^2 := pow_le_pow_left₀ (by positivity) (Nat.floor_le (by positivity)) _
       _ = X^(2*g) := by rw [← Real.rpow_mul_natCast xp.le]; congr 1; ring
       _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hX hga

private lemma log_level {X g a b : ℝ} (hX : 1<X) (hg : 0<g) (hab : a≤b) :
    log (X^b/X^a)/log ((⌊X^g⌋₊:ℝ)+1) ≤ (b-a)/g := by
  have xp := zero_lt_one.trans hX
  have lx := Real.log_pos hX
  have lg := Real.log_le_log (Real.rpow_pos_of_pos xp g) (Nat.lt_floor_add_one (X^g)).le
  rw [Real.log_rpow xp] at lg
  have lp := (mul_pos hg lx).trans_le lg
  rw [Real.log_div (Real.rpow_pos_of_pos xp _).ne' (Real.rpow_pos_of_pos xp _).ne',
    Real.log_rpow xp,Real.log_rpow xp,div_le_div_iff₀ lp hg]
  nlinarith only [mul_le_mul_of_nonneg_left lg (sub_nonneg.mpr hab)]

/-- In the whole lower range the normalized sieve errors are dominated by three powers
of X, all with at most four logarithms. -/
theorem error_envelope (n : ℕ) (hn : 2≤n) {g a b p q s C : ℝ} (hg : 0<g)
    (hgu : g≤1) (ha : 0≤a) (hab : a≤b) (hb : b≤1) (hga : 2*g≤a)
    (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hs : s<1) (hC : 1≤C) :
    let X : ℝ := n
    let h : ℝ := ⌊X^c⌋₊
    let z : ℝ := ⌊X^g⌋₊
    let u := X^a
    let v := X^b
    4*h*z^2/u + C*(1+log (v/u)/log 2)*(X+h)^p*v^q*z^(2*(1-s)) +
      C*(v^2/X)*(1+log z)^3 ≤
      4*C*(1+log X)^4*(X^(c+2*g-a)+X^(p+b*q+g*(2*(1-s)))+X^(2*b-1)) := by
  let X : ℝ := n
  let h : ℝ := ⌊X^c⌋₊
  let z : ℝ := ⌊X^g⌋₊
  let u := X^a
  let v := X^b
  let T := 1+log X
  let E₁ := X^(c+2*g-a)
  let E₂ := X^(p+b*q+g*(2*(1-s)))
  let E₃ := X^(2*b-1)
  let r := 2*(1-s)
  change 4*h*z^2/u+C*(1+log (v/u)/log 2)*(X+h)^p*v^q*z^r+C*(v^2/X)*(1+log z)^3 ≤
    4*C*T^4*(E₁+E₂+E₃)
  have x1 : 1≤X := by dsimp [X]; exact_mod_cast (show 1≤n by omega)
  have xp := zero_lt_one.trans_le x1
  have cp : 0≤C := by linarith
  have gr : 0≤r := by dsimp [r]; linarith
  have up := Real.rpow_pos_of_pos xp a
  have vp := Real.rpow_pos_of_pos xp b
  have lx := Real.log_nonneg x1
  have t1 : 1≤T := by dsimp [T]; linarith
  have t0 := zero_le_one.trans t1
  have z1 : 1≤z := by dsimp [z]; exact_mod_cast (admissible_level x1 hg hga).1
  have zp := zero_lt_one.trans_le z1
  have hc : h ≤ X^c := Nat.floor_le (by positivity)
  have hz : z ≤ X^g := Nat.floor_le (by positivity)
  have h0 : 0≤h := Nat.cast_nonneg _
  have hx : h≤X := hc.trans (by simpa using Real.rpow_le_rpow_of_exponent_le x1 (show c≤1 by norm_num [c]))
  have zx : z≤X := hz.trans (by simpa using Real.rpow_le_rpow_of_exponent_le x1 hgu)
  have e1 : 0≤E₁ := Real.rpow_nonneg xp.le _
  have e2 : 0≤E₂ := Real.rpow_nonneg xp.le _
  have e3 : 0≤E₃ := Real.rpow_nonneg xp.le _
  have first : 4*h*z^2/u ≤ 4*E₁ := by
    calc _ ≤ 4*X^c*(X^g)^2/u := by gcongr
         _ = _ := by dsimp [E₁,u]; rw [← Real.rpow_mul_natCast xp.le,Real.rpow_sub xp,Real.rpow_add xp]; ring_nf
  have count : 1+log (v/u)/log 2 ≤ 2*T := by
    have l : log (v/u) = (b-a)*log X := by
      dsimp [u,v]; rw [Real.log_div vp.ne' up.ne',Real.log_rpow xp,Real.log_rpow xp]; ring
    have l2 : 1/2 ≤ log (2:ℝ) := by
      have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : 0<(2:ℝ))
      norm_num at hh ⊢
      exact hh
    have width : b-a ≤ 1 := by linarith
    have d : log (v/u)/log 2 ≤ 2*log X := by
      apply (div_le_iff₀ (by linarith : 0<log (2:ℝ))).mpr; rw [l]
      nlinarith [mul_le_mul_of_nonneg_right width lx,mul_le_mul_of_nonneg_left l2 lx]
    dsimp [T]; linarith
  have root : (X+h)^p ≤ 2*X^p := by
    calc _ ≤ (2*X)^p := Real.rpow_le_rpow (by positivity) (by linarith) hp
         _ = (2:ℝ)^p*X^p := Real.mul_rpow (by norm_num) xp.le
         _ ≤ _ := mul_le_mul_of_nonneg_right (by
           simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hp1) (by positivity)
  have poly : (X+h)^p*v^q*z^r ≤ 2*E₂ := by
    calc _ ≤ (2*X^p)*v^q*(X^g)^r := mul_le_mul
           (mul_le_mul_of_nonneg_right root (Real.rpow_nonneg vp.le _))
           (Real.rpow_le_rpow zp.le hz gr) (Real.rpow_nonneg zp.le _) (by positivity)
         _ = _ := by
           dsimp [v,E₂,r]
           rw [← Real.rpow_mul xp.le,← Real.rpow_mul xp.le,Real.rpow_add xp,Real.rpow_add xp]
           ring
  have mid : C*(1+log (v/u)/log 2)*(X+h)^p*v^q*z^r ≤ 4*C*T*E₂ := by
    have hcmp := mul_le_mul count poly (by positivity) (by positivity)
    have sc := mul_le_mul_of_nonneg_left hcmp cp
    linarith only [show C*((1+log (v/u)/log 2)*((X+h)^p*v^q*z^r))=
      C*(1+log (v/u)/log 2)*(X+h)^p*v^q*z^r by ring,sc,
      show C*(2*T*(2*E₂))=4*C*T*E₂ by ring]
  have scale : v^2/X = E₃ := by
    dsimp [E₃,v]; rw [Real.rpow_sub xp,Real.rpow_one,← Real.rpow_mul_natCast xp.le]; congr 2; ring
  have zlog : (1+log z)^3 ≤ T^3 :=
    pow_le_pow_left₀ (by linarith [Real.log_nonneg z1]) (add_le_add le_rfl (Real.log_le_log zp zx)) _
  have last : C*(v^2/X)*(1+log z)^3 ≤ C*T^3*E₃ := by
    rw [scale]
    exact (mul_le_mul_of_nonneg_left zlog (mul_nonneg cp e3)).trans_eq (by ring)
  have L1 : 1≤T^4 := one_le_pow₀ t1
  have L2 : T≤T^4 := by simpa using pow_le_pow_right₀ t1 (by decide : 1≤4)
  have L3 : T^3≤T^4 := pow_le_pow_right₀ t1 (by decide)
  have b1 : 4*E₁ ≤ 4*C*T^4*E₁ := by
    apply mul_le_mul_of_nonneg_right _ e1
    nlinarith [mul_le_mul_of_nonneg_left L1 cp]
  have b2 : 4*C*T*E₂ ≤ 4*C*T^4*E₂ := by gcongr
  have b3 : C*T^3*E₃ ≤ 4*C*T^4*E₃ := by
    apply mul_le_mul_of_nonneg_right _ e3
    nlinarith [mul_le_mul_of_nonneg_left L3 cp, mul_nonneg cp (show 0≤T^4 by positivity)]
  linarith only [first,mid,last,b1,b2,b3, show 4*C*T^4*(E₁+E₂+E₃) =
    4*C*T^4*E₁+4*C*T^4*E₂+4*C*T^4*E₃ by ring]

/-- A strict exponent saving in all three errors and positive allowance
above the fixed-level main term give the required eventual band count. -/
theorem prime_hits_of_band_bound (a b g p q s L : ℝ) (bb : BandBound p q s) (hg : 0<g)
    (hgu : g≤1) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hs : s<1)
    (gap₁ : 2*g<a) (gap₂ : p+b*q+g*(2*(1-s))<c) (gap₃ : 2*b-1<c)
    (margin : (b-a)/g<L) :
    ∀ᶠ n : ℕ in atTop,
      FactorialUpperBands.primeHits n ⌊(n:ℝ)^c⌋₊ ((n:ℝ)^a) ((n:ℝ)^b) ≤ L*window n := by
  obtain ⟨C,hC,estim⟩ := bb
  have cp : 0<C := by linarith
  have cpos : 0<c := by norm_num [c]
  let e := (L-(b-a)/g)/(12*C)
  have ep : 0<e := div_pos (sub_pos.mpr margin) (by positivity)
  have coeff : 12*C*e = L-(b-a)/g := by dsimp only [e]; field_simp
  filter_upwards [eventually_ge_atTop (2:ℕ),power_rate (show c+2*g-a<c by linarith) cpos ep,
    power_rate gap₂ cpos ep,power_rate gap₃ cpos ep] with n hn r₁ r₂ r₃
  let X := (n:ℝ)
  let h := ⌊X^c⌋₊
  let z := ⌊X^g⌋₊
  let u := X^a
  let v := X^b
  let T := (1+log X)^4
  let E₁ := X^(c+2*g-a)
  let E₂ := X^(p+b*q+g*(2*(1-s)))
  let E₃ := X^(2*b-1)
  have x1 : 1<X := by dsimp [X]; exact_mod_cast (show 1<n by omega)
  have hnon : 0 ≤ (h:ℝ) := Nat.cast_nonneg _
  have zu := admissible_level x1.le hg gap₁.le
  have uv := Real.rpow_le_rpow_of_exponent_le x1.le hab
  have cnt := estim n h z u v (by omega) zu.1 zu.2 uv
  have main := mul_le_mul_of_nonneg_left (log_level x1 hg hab) hnon
  rw [← mul_div_assoc] at main
  have env := error_envelope n hn hg hgu ha hab hb gap₁.le hp hp1 hq hs hC
  change 4*h*(z:ℝ)^2/u+C*(1+log (v/u)/log 2)*(X+h)^p*v^q*(z:ℝ)^(2*(1-s))+
    C*(v^2/X)*(1+log z)^3 ≤ 4*C*T*(E₁+E₂+E₃) at env
  change (h:ℝ)*log (v/u)/log ((z:ℝ)+1) ≤ (h:ℝ)*((b-a)/g) at main
  change T*E₁ ≤ e*(h:ℝ) at r₁
  change T*E₂ ≤ e*(h:ℝ) at r₂
  change T*E₃ ≤ e*(h:ℝ) at r₃
  have sum : T*(E₁+E₂+E₃) ≤ 3*e*(h:ℝ) := by
    rw [mul_add,mul_add]; linarith only [r₁,r₂,r₃]
  have tot : 4*C*T*(E₁+E₂+E₃) ≤ (L-(b-a)/g)*(h:ℝ) := by
    calc _ = (4*C)*(T*(E₁+E₂+E₃)) := by ring
         _ ≤ (4*C)*(3*e*(h:ℝ)) := mul_le_mul_of_nonneg_left sum (by positivity)
         _ = _ := by rw [← coeff]; ring
  change FactorialUpperBands.primeHits n h u v ≤ L*(h:ℝ)
  change FactorialUpperBands.primeHits n h u v ≤ (h:ℝ)*log (v/u)/log ((z:ℝ)+1)+
    4*h*(z:ℝ)^2/u+C*(1+log (v/u)/log 2)*(X+h)^p*v^q*(z:ℝ)^(2*(1-s))+
    C*(v^2/X)*(1+log z)^3 at cnt
  linarith only [cnt,main,env,tot,show (h:ℝ)*((b-a)/g)+(L-(b-a)/g)*(h:ℝ) = L*(h:ℝ) by ring]

end FactorialLowerBands
end
end

-- Source module ReciprocalLowerBandCertificate
section

/-! Exact certificates for the 31 lower bands in the 48-band prime sieve.
The level exponent is the reciprocal of the target coefficient, diminished
by one billionth. Its loss fits strictly within each stated allowance. -/

noncomputable section
open Finset
namespace FactorialLowerBands
open PrimeBlockMesh

def ampPower (j : ℕ) : ℝ := if j<16 then 1/15 else 1/7
def endpointPower (j : ℕ) : ℝ := if j<16 then 2/3 else 3/7
def modulusPower (j : ℕ) : ℝ := if j<16 then 11/15 else 4/7

/-- The unperturbed reciprocal coefficient follows from the indicated
exponent pair. Both formulas are rational at the mesh endpoints. -/
def levelPower (j : ℕ) : ℝ :=
  (if j<16 then 17/24-(5/4)*(edge (j+1):ℝ) else 19/54-(edge (j+1):ℝ)/2) - 1/1000000000

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 12000 in
/-- All size requirements, three strict power savings, and the allowance
comparison for each of the first 31 mesh intervals. -/
theorem lower_band_parameters (j : ℕ) (hj : j<31) :
    let a := (edge j:ℝ)
    let b := (edge (j+1):ℝ)
    let g := levelPower j
    let p := ampPower j
    let q := endpointPower j
    let s := modulusPower j
    0<g ∧ g≤1 ∧ 0≤a ∧ a≤b ∧ b≤1 ∧ 0≤p ∧ p≤1 ∧ 0≤q ∧ s<1 ∧
      2*g<a ∧ p+b*q+g*(2*(1-s))<ReciprocalBandRates.c ∧
      2*b-1<ReciprocalBandRates.c ∧ (b-a)/g < (allowance j:ℝ) := by
  interval_cases j <;>
    norm_num [levelPower,ampPower,endpointPower,modulusPower,edge,allowance,ReciprocalBandRates.c]

end FactorialLowerBands
end
end

-- Source module ReciprocalLowerBands
section

/-! Transfer the two lower exponent pairs to the exact sets and tolerances
of the first 31 entries in the four-ninths reduction. -/
noncomputable section
open Finset Filter
namespace FactorialLowerBands
open FactorialUpperBands PrimeBlockMesh ReciprocalBandRates

/-- The first 31 intervals of the catalog's 48-band statement, from the two
full-band estimates on prime hits. All 31 rational parameter comparisons are
discharged in the finite certificate. -/
theorem lower_thirty_one (first : BandBound (1/15) (2/3) (11/15))
    (middle : BandBound (1/7) (3/7) (4/7)) :
    ∀ᶠ n : ℕ in atTop, ∀ j ∈ range 31,
      ((bandSet n j).card:ℝ) ≤ (allowance j:ℝ)*⌊(n:ℝ)^(4/9:ℝ)⌋₊ := by
  apply (eventually_all_finset _).mpr
  intro j hj
  have hj' := mem_range.mp hj
  obtain ⟨hg,hgu,ha,hab,hb,hp,hp1,hq,hs,e₁,e₂,e₃,margin⟩ := lower_band_parameters j hj'
  have bnd : BandBound (ampPower j) (endpointPower j) (modulusPower j) := by
    by_cases small : j<16
    · simpa [ampPower,endpointPower,modulusPower,small] using first
    · simpa [ampPower,endpointPower,modulusPower,small] using middle
  have out := prime_hits_of_band_bound (edge j:ℝ) (edge (j+1):ℝ) (levelPower j)
    (ampPower j) (endpointPower j) (modulusPower j) (allowance j:ℝ)
    bnd hg hgu ha hab hb hp hp1 hq hs e₁ e₂ e₃ margin
  filter_upwards [out] with n high
  have card := FactorialFourier.hit_card_le n ⌊(n:ℝ)^(4/9:ℝ)⌋₊ ((n:ℝ)^(edge j:ℝ)) ((n:ℝ)^(edge (j+1):ℝ))
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) (bandSet n j) (by
      intro z hz
      obtain ⟨hi,hband⟩ := mem_filter.mp hz
      obtain ⟨ht,hp⟩ := mem_sigma.mp hi
      have inPrime := (mem_filter.mp hp).1
      exact ⟨mem_range.mp ht,Nat.prime_of_mem_primeFactors inPrime,Nat.dvd_of_mem_primeFactors inPrime,hband⟩)
  exact card.trans high

end FactorialLowerBands
end
end

-- Source module ReciprocalAllBands
section

/-! All 48 prime bands, followed by the repeated-prime-power deduction. -/
noncomputable section
namespace FactorialFullBands

theorem all_bands : OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2.H1 :=
  of_lower_thirty_one (FactorialLowerBands.lower_thirty_one
    FactorialLowerBands.lower_band_bound FactorialLowerBands.middle_band_bound)

theorem medium_prime_mass : OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1.H2 :=
  OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2.main all_bands
    OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2.prime_power_removal

end FactorialFullBands
end
end

theorem OMA.erdos420Sieve : OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1.H2 :=
  OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2.main
    FactorialFullBands.all_bands
    OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2.prime_power_removal

end

theorem OMA.solution : type_of% @Erdos420.erdos_420.variants.pow_four_ninths :=
  OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1.main
    OMA.erdos420Factorial OMA.erdos420Sieve
