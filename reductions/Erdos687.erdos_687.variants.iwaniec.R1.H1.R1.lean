import OMAReductions.R_Erdos687_erdos_687_variants_iwaniec_R1

-- Reduction Erdos687.erdos_687.variants.iwaniec.R1.H1.R1 of step Erdos687.erdos_687.variants.iwaniec.R1.H1
-- Credit: @JamesSlash

/-!
# Iwaniec's shifted-sieve gap bound from the strong prime number theorem

* `H1`: the prime number theorem with the de la Vallée Poussin error term, in the form
  `StrongPNT` of the PrimeNumberTheoremAnd project: `ψ(x) - x = O(x exp(-c √(log x)))`.
* `H2`: Iwaniec's theorem ([I78, Corollary], H. Iwaniec, *On the problem of Jacobsthal*,
  Demonstratio Math. 11 (1978)) conditional on the strong prime number theorem: if `m` consecutive
  integers are each divisible by one of `r ≥ 2` given primes, then `m ≤ C (r log r)²`.
  The Lean development jasondavies/iwaniec-linear-sieve derives it from `StrongPNT` through
  Iwaniec's linear sieve [I71].
* `main`: take the `r = π(x) ≥ 2` primes `p ≤ x`. By the elementary half of Mertens' third
  theorem, `∏_{p ≤ x} (1 - 1/p) ≤ 1 / log (x + 1) ≤ 1 / log r` (the helper lemmas for it are
  copied from the merged proof of Erdos360.erdos_360.R1.H2, PR #2521). Hence an interval of length
  `y ≥ C r² log r / ∏ (1 - 1/p)` has `y ≥ C (r log r)²`, which is too long to be covered by `H2`.
-/

namespace OMA.R_Erdos687_erdos_687_variants_iwaniec_R1_H1_R1

open Finset

/-- The strong prime number theorem (`StrongPNT` in PrimeNumberTheoremAnd). -/
def H1 : Prop :=
  ∃ c > 0, Asymptotics.IsBigO Filter.atTop (Chebyshev.psi - id)
    (fun x : ℝ ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)))

/-- Iwaniec's bound for Jacobsthal's problem, assuming the strong prime number theorem. -/
def H2 : Prop :=
  (∃ c > 0, Asymptotics.IsBigO Filter.atTop (Chebyshev.psi - id)
    (fun x : ℝ ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)))) →
  ∃ C : ℝ, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → 2 ≤ S.card →
    ∀ (x : ℤ) (m : ℕ), (∀ k < m, ∃ p ∈ S, (p : ℤ) ∣ x + k) →
      (m : ℝ) ≤ C * ((S.card : ℝ) * Real.log S.card) ^ 2

lemma geom_sum_le_inv_one_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    ∑ a ∈ Finset.range M, r ^ a ≤ (1 - r)⁻¹ := by
  have h1 : 0 < 1 - r := sub_pos.mpr hr1
  have hsum : (1 - r) * ∑ a ∈ Finset.range M, r ^ a = 1 - r ^ M := by
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      ring
  rw [← one_div, le_div_iff₀ h1, mul_comm, hsum]
  linarith [pow_nonneg hr0 M]

lemma sum_mult_smooth_le (f : ℕ → ℝ) (hf0 : ∀ a, 0 ≤ f a) (hf1 : f 1 = 1)
    (hfmul : ∀ a b, f (a * b) = f a * f b) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (hfQ : ∀ p ∈ Q, f p < 1) (M : ℕ) :
    ∑ k ∈ (Finset.Icc 1 M).filter (fun k => k.primeFactors ⊆ Q), f k ≤
      ∏ p ∈ Q, (1 - f p)⁻¹ := by
  classical
  induction Q using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty, Finset.subset_empty, Nat.primeFactors_eq_empty]
    have hsub : (Finset.Icc 1 M).filter (fun k => k = 0 ∨ k = 1) ⊆ {1} := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton] at hk ⊢
      omega
    calc
      ∑ k ∈ (Finset.Icc 1 M).filter (fun k => k = 0 ∨ k = 1), f k
          ≤ ∑ k ∈ ({1} : Finset ℕ), f k := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hf0 _
      _ = 1 := by simp [hf1]
  | insert p Q hpQ ih =>
    have hp : p.Prime := hQ p (Finset.mem_insert_self p Q)
    have hfp1 : f p < 1 := hfQ p (Finset.mem_insert_self p Q)
    have hQ' : ∀ q ∈ Q, q.Prime := fun q hq => hQ q (Finset.mem_insert_of_mem hq)
    have hfQ' : ∀ q ∈ Q, f q < 1 := fun q hq => hfQ q (Finset.mem_insert_of_mem hq)
    let S₁ := (Finset.Icc 1 M).filter (fun k => k.primeFactors ⊆ insert p Q)
    let S₀ := (Finset.Icc 1 M).filter (fun k => k.primeFactors ⊆ Q)
    let g : ℕ → ℕ × ℕ := fun k => (k.factorization p, k / p ^ (k.factorization p))
    have hginj : Set.InjOn g S₁ := by
      intro k₁ _ k₂ _ h
      calc
        k₁ = p ^ (k₁.factorization p) * (k₁ / p ^ (k₁.factorization p)) :=
          (Nat.mul_div_cancel' (Nat.ordProj_dvd k₁ p)).symm
        _ = p ^ (g k₁).1 * (g k₁).2 := rfl
        _ = p ^ (g k₂).1 * (g k₂).2 := by rw [h]
        _ = k₂ := Nat.mul_div_cancel' (Nat.ordProj_dvd k₂ p)
    have hgmem : ∀ k ∈ S₁, g k ∈ Finset.range (M + 1) ×ˢ S₀ := by
      intro k hk
      simp only [S₁, Finset.mem_filter, Finset.mem_Icc] at hk
      obtain ⟨⟨hk1, hkM⟩, hkp⟩ := hk
      have hk0 : k ≠ 0 := by omega
      have hpow_dvd : p ^ (k.factorization p) ∣ k := Nat.ordProj_dvd k p
      have hpow_le : p ^ (k.factorization p) ≤ k := Nat.ordProj_le p hk0
      have ha_lt : k.factorization p < M + 1 := by
        have h2a : 2 ^ (k.factorization p) ≤ p ^ (k.factorization p) :=
          Nat.pow_le_pow_left hp.two_le _
        have hlt : k.factorization p < 2 ^ (k.factorization p) := Nat.lt_two_pow_self
        omega
      have hm1 : 1 ≤ k / p ^ (k.factorization p) := Nat.div_pos hpow_le (pow_pos hp.pos _)
      have hmM : k / p ^ (k.factorization p) ≤ M := (Nat.div_le_self k _).trans hkM
      have hm_not_dvd : ¬ p ∣ k / p ^ (k.factorization p) := by
        have hm0 : k / p ^ (k.factorization p) ≠ 0 := by omega
        rw [hp.dvd_iff_one_le_factorization hm0, Nat.factorization_div hpow_dvd]
        simp [hp.factorization]
      have hmQ : (k / p ^ (k.factorization p)).primeFactors ⊆ Q := by
        intro q hq
        have hq_mem : q ∈ k.primeFactors := Nat.primeFactors_mono (Nat.div_dvd_of_dvd hpow_dvd) hk0 hq
        have hqp : q ≠ p := by
          intro hqe
          subst hqe
          exact hm_not_dvd (Nat.dvd_of_mem_primeFactors hq)
        exact (Finset.mem_insert.mp (hkp hq_mem)).resolve_left hqp
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr ha_lt,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm1, hmM⟩, hmQ⟩⟩
    have hf_pow : ∀ a : ℕ, f (p ^ a) = (f p) ^ a := by
      intro a
      induction a with
      | zero => simp [hf1]
      | succ a iha => rw [pow_succ, hfmul, iha, pow_succ]
    have hf_g : ∀ k : ℕ, f k = (f p) ^ (g k).1 * f (g k).2 := by
      intro k
      calc
        f k = f (p ^ (k.factorization p) * (k / p ^ (k.factorization p))) := by
            rw [Nat.mul_div_cancel' (Nat.ordProj_dvd k p)]
        _ = f (p ^ (k.factorization p)) * f (k / p ^ (k.factorization p)) := hfmul _ _
        _ = (f p) ^ (g k).1 * f (g k).2 := by rw [hf_pow]
    have hsum_le : ∑ k ∈ S₁, f k ≤
        ∑ x ∈ Finset.range (M + 1) ×ˢ S₀, (f p) ^ x.1 * f x.2 := by
      calc
        ∑ k ∈ S₁, f k = ∑ k ∈ S₁, (f p) ^ (g k).1 * f (g k).2 :=
          Finset.sum_congr rfl fun k _ => hf_g k
        _ = ∑ x ∈ S₁.image g, (f p) ^ x.1 * f x.2 :=
          (Finset.sum_image (f := fun x : ℕ × ℕ => (f p) ^ x.1 * f x.2) hginj).symm
        _ ≤ ∑ x ∈ Finset.range (M + 1) ×ˢ S₀, (f p) ^ x.1 * f x.2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
            exact hgmem k hk
          · intro x _ _
            exact mul_nonneg (pow_nonneg (hf0 p) _) (hf0 _)
    have hprod_sum : ∑ x ∈ Finset.range (M + 1) ×ˢ S₀, (f p) ^ x.1 * f x.2 =
        (∑ a ∈ Finset.range (M + 1), (f p) ^ a) * ∑ m ∈ S₀, f m := by
      rw [Finset.sum_product, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only
      rw [← Finset.mul_sum]
    have hgeom : ∑ a ∈ Finset.range (M + 1), (f p) ^ a ≤ (1 - f p)⁻¹ :=
      geom_sum_le_inv_one_sub (hf0 p) hfp1 (M + 1)
    have hih : ∑ m ∈ S₀, f m ≤ ∏ q ∈ Q, (1 - f q)⁻¹ := ih hQ' hfQ'
    have hS0_nonneg : 0 ≤ ∑ m ∈ S₀, f m := Finset.sum_nonneg fun _ _ => hf0 _
    have hinv_nonneg : 0 ≤ (1 - f p)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hfp1).le
    rw [Finset.prod_insert hpQ]
    calc
      ∑ k ∈ S₁, f k ≤ (∑ a ∈ Finset.range (M + 1), (f p) ^ a) * ∑ m ∈ S₀, f m :=
        hsum_le.trans_eq hprod_sum
      _ ≤ (1 - f p)⁻¹ * ∏ q ∈ Q, (1 - f q)⁻¹ :=
        mul_le_mul hgeom hih hS0_nonneg hinv_nonneg

lemma log_add_one_le_sum_inv (w : ℕ) :
    Real.log (w + 1 : ℝ) ≤ ∑ m ∈ Finset.Icc 1 w, (m : ℝ)⁻¹ := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le w))]
    have hw0 : (0 : ℝ) < (w + 1 : ℕ) := by positivity
    have hw1 : (0 : ℝ) < (w + 2 : ℕ) := by positivity
    have hlog : Real.log ((w + 1 + 1 : ℕ) : ℝ) - Real.log ((w + 1 : ℕ) : ℝ) ≤
        ((w + 1 : ℕ) : ℝ)⁻¹ := by
      have hdiv : (0 : ℝ) < ((w + 1 + 1 : ℕ) : ℝ) / ((w + 1 : ℕ) : ℝ) := by positivity
      have h1 := Real.log_le_sub_one_of_pos hdiv
      rw [Real.log_div hw1.ne' hw0.ne'] at h1
      have h2 : ((w + 1 + 1 : ℕ) : ℝ) / ((w + 1 : ℕ) : ℝ) - 1 = ((w + 1 : ℕ) : ℝ)⁻¹ := by
        push_cast
        field_simp
        ring
      linarith
    push_cast at hlog ih ⊢
    linarith


lemma prod_one_sub_inv_primesLE_le (w : ℕ) (hw : 1 ≤ w) :
    ∏ p ∈ Nat.primesLE w, (1 - (p : ℝ)⁻¹) ≤ (Real.log (w + 1 : ℝ))⁻¹ := by
  have hlog_pos : 0 < Real.log (w + 1 : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < w + 1)
  have hsub : Finset.Icc 1 w ⊆ (Finset.Icc 1 w).filter (fun k => k.primeFactors ⊆ Nat.primesLE w) := by
    intro k hk
    refine Finset.mem_filter.mpr ⟨hk, fun p hp => ?_⟩
    have hkm := (Finset.mem_Icc.mp hk).2
    have hpk : p ≤ k := Nat.le_of_mem_primeFactors hp
    exact Nat.mem_primesLE.mpr ⟨hpk.trans hkm, Nat.prime_of_mem_primeFactors hp⟩
  have hsum : ∑ m ∈ Finset.Icc 1 w, (m : ℝ)⁻¹ ≤ ∏ p ∈ Nat.primesLE w, (1 - (p : ℝ)⁻¹)⁻¹ := by
    calc
      ∑ m ∈ Finset.Icc 1 w, (m : ℝ)⁻¹
          ≤ ∑ m ∈ (Finset.Icc 1 w).filter (fun k => k.primeFactors ⊆ Nat.primesLE w), (m : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ ≤ ∏ p ∈ Nat.primesLE w, (1 - (p : ℝ)⁻¹)⁻¹ := by
        apply sum_mult_smooth_le (fun k => (k : ℝ)⁻¹) (fun _ => by positivity) (by simp)
          (fun a b => by push_cast; ring) (Nat.primesLE w)
          (fun p hp => Nat.prime_of_mem_primesLE hp)
          (fun p hp => by
            have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
            have : (p : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hp2
            linarith) w
  have hprod_inv : Real.log (w + 1 : ℝ) ≤ (∏ p ∈ Nat.primesLE w, (1 - (p : ℝ)⁻¹))⁻¹ := by
    calc
      Real.log (w + 1 : ℝ) ≤ ∑ m ∈ Finset.Icc 1 w, (m : ℝ)⁻¹ := log_add_one_le_sum_inv w
      _ ≤ ∏ p ∈ Nat.primesLE w, (1 - (p : ℝ)⁻¹)⁻¹ := hsum
      _ = (∏ p ∈ Nat.primesLE w, (1 - (p : ℝ)⁻¹))⁻¹ := by rw [Finset.prod_inv_distrib]
  have hprod_pos : 0 < ∏ p ∈ Nat.primesLE w, (1 - (p : ℝ)⁻¹) := by
    apply Finset.prod_pos
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
    have : (p : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hp2
    linarith
  exact (le_inv_comm₀ hlog_pos hprod_pos).mp hprod_inv

theorem main : H1 → H2 → OMA.R_Erdos687_erdos_687_variants_iwaniec_R1.H1 := by
  intro h1 h2
  obtain ⟨C, hC⟩ := h2 h1
  refine ⟨|C| + 1, by positivity, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 3] with x hx M y hy
  by_contra hno
  push_neg at hno
  set S := (Finset.range (x + 1)).filter Nat.Prime with hSdef
  have hSP : S = Nat.primesLE x := (Nat.primesLE_eq_filter_range x).symm
  have hScard : S.card = Nat.primeCounting x := by
    rw [hSP, Nat.primesLE_card_eq_primeCounting]
  have h2S : 2 ≤ S.card := by
    have hsub : ({2, 3} : Finset ℕ) ⊆ S := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rw [hSdef, Finset.mem_filter, Finset.mem_range]
      rcases hp with rfl | rfl
      · exact ⟨by omega, Nat.prime_two⟩
      · exact ⟨by omega, Nat.prime_three⟩
    have := Finset.card_le_card hsub
    simpa using this
  have hcov : ∀ k < y, ∃ p ∈ S, (p : ℤ) ∣ ((M + 1 : ℕ) : ℤ) + k := by
    intro k hk
    obtain ⟨p, hpx, hp, hpd⟩ := hno (M + 1 + k) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    refine ⟨p, ?_, ?_⟩
    · rw [hSdef, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp⟩
    · have hd : ((p : ℕ) : ℤ) ∣ ((M + 1 + k : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hpd
      push_cast at hd ⊢
      exact hd
  have hm := hC S (fun p hp => (Finset.mem_filter.mp hp).2) h2S ((M + 1 : ℕ) : ℤ) y hcov
  -- Mertens: the Euler product is at most `1 / log (x + 1)`
  have hV := prod_one_sub_inv_primesLE_le x (by omega)
  rw [← hSP] at hV
  have hVpos : 0 < ∏ p ∈ S, (1 - (p : ℝ)⁻¹) := OMA.R_Erdos687_erdos_687_variants_iwaniec_R1.eulerProd_pos x
  set V := ∏ p ∈ S, (1 - (p : ℝ)⁻¹) with hVdef
  set r : ℝ := (S.card : ℝ) with hrdef
  have hr2 : (2 : ℝ) ≤ r := by rw [hrdef]; exact_mod_cast h2S
  have hrx : r ≤ (x : ℝ) := by
    rw [hrdef, hScard]
    exact_mod_cast OMA.R_Erdos687_erdos_687_variants_iwaniec_R1.primeCounting_le_self x
  have hL : 0 < Real.log r := Real.log_pos (by linarith)
  have hLx : Real.log r ≤ Real.log ((x : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
  have hlogx1 : 0 < Real.log ((x : ℝ) + 1) := Real.log_pos (by
    have : (3 : ℝ) ≤ x := by exact_mod_cast hx
    linarith)
  -- `1 / V ≥ log (x + 1) ≥ log r`
  have hinvV : Real.log r ≤ V⁻¹ := by
    have : Real.log ((x : ℝ) + 1) ≤ V⁻¹ := by
      have h := (le_inv_comm₀ hVpos hlogx1).mp (by simpa using hV)
      exact h
    linarith
  have hy' : (|C| + 1) * (r ^ 2 * Real.log r) / V ≤ (y : ℝ) := by
    rw [hrdef, hScard] at *
    simpa [hScard] using hy
  have hbig : (|C| + 1) * (r * Real.log r) ^ 2 ≤ (y : ℝ) := by
    have hpos : 0 ≤ (|C| + 1) * (r ^ 2 * Real.log r) := by positivity
    calc (|C| + 1) * (r * Real.log r) ^ 2 = (|C| + 1) * (r ^ 2 * Real.log r) * Real.log r := by ring
      _ ≤ (|C| + 1) * (r ^ 2 * Real.log r) * V⁻¹ := mul_le_mul_of_nonneg_left hinvV hpos
      _ = (|C| + 1) * (r ^ 2 * Real.log r) / V := by rw [div_eq_mul_inv]
      _ ≤ y := hy'
  have hrl : 0 < (r * Real.log r) ^ 2 := by positivity
  have hCabs : C * (r * Real.log r) ^ 2 ≤ |C| * (r * Real.log r) ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self C) hrl.le
  have hm' : (y : ℝ) ≤ C * (r * Real.log r) ^ 2 := by simpa [hrdef] using hm
  nlinarith

end OMA.R_Erdos687_erdos_687_variants_iwaniec_R1_H1_R1
