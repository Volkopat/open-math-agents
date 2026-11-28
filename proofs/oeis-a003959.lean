import OMAStatements.S_oeis_a003959

/-!
The coefficient function is completely multiplicative on positive inputs.
To establish absolute convergence, first sum over smooth numbers and
bound the associated finite geometric products uniformly.
-/

namespace PrimePlusOne

open OMA.S_oeis_a003959 Finset

private theorem a_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    a (m*n) = a m * a n := by
  unfold a
  rw [Nat.factorization_mul hm hn]
  exact Finsupp.prod_add_index' (fun p => pow_zero (p+1)) (fun p => pow_add (p+1))

private theorem a_prime {p : ℕ} (hp : p.Prime) : a p = p+1 := by
  simp [a, hp.factorization]

private noncomputable def term (s : ℂ) : ℕ →*₀ ℂ where
  toFun n := LSeries.term (fun n => (a n : ℂ)) s n
  map_one' := by simp [a]
  map_zero' := LSeries.term_zero _ _
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    simp only [LSeries.term_of_ne_zero (mul_ne_zero hm hn),
      LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hn, a_mul hm hn, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, mul_div_mul_comm]

private noncomputable def posTerm (s : ℂ) : ℕ →* ℝ where
  toFun n := ‖term s n‖
  map_one' := by simp
  map_mul' m n := by simp [map_mul]

private theorem term_prime_norm (s : ℂ) {p : ℕ} (hp : p.Prime) :
    ‖term s p‖ = ((p : ℝ)+1) / (p : ℝ)^s.re := by
  change ‖LSeries.term (fun n => (a n : ℂ)) s p‖ = _
  rw [LSeries.term_of_ne_zero hp.ne_zero, a_prime hp, norm_div,
    Complex.norm_natCast_cpow_of_pos hp.pos]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
    Complex.norm_of_nonneg (by positivity)]

private theorem term_norm_upper (s : ℂ) {p : ℕ} (hp : p.Prime) :
    ‖term s p‖ ≤ (3/2:ℝ) * (p : ℝ)^(1-s.re) := by
  have hp₀ : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp₂ : 2 ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  rw [term_prime_norm s hp, Real.rpow_sub hp₀, Real.rpow_one, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (by linarith) (Real.rpow_nonneg hp₀.le _)

private theorem prime_norm_le (s : ℂ) (hs : 2 ≤ s.re) {p : ℕ} (hp : p.Prime) :
    ‖term s p‖ ≤ (3/4:ℝ) := by
  have hp₂ : 2 ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp₁ : (1:ℝ) ≤ p := by linarith
  have hpow : (p : ℝ)^(-1:ℝ) ≤ (2:ℝ)^(-1:ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hp₂ (by norm_num)
  have h := Real.rpow_le_rpow_of_exponent_le hp₁ (show 1 - s.re ≤ -1 by linarith)
  calc
    ‖term s p‖ ≤ (3/2:ℝ) * (p : ℝ)^(1-s.re) := term_norm_upper s hp
    _ ≤ (3/2:ℝ) * (2 : ℝ)^(-1:ℝ) := mul_le_mul_of_nonneg_left (h.trans hpow) (by norm_num)
    _ = (3/4:ℝ) := by norm_num [Real.rpow_neg_one]

private theorem inv_sub_le_exp {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 3/4) :
    (1-x)⁻¹ ≤ Real.exp (4*x) := by
  have hx₁ : 0 < 1-x := by linarith
  calc
    (1-x)⁻¹ ≤ 4*x+1 := by
      rw [← one_div]
      apply (div_le_iff₀ hx₁).2
      nlinarith [mul_nonneg hx (show 0 ≤ 3-4*x by linarith)]
    _ ≤ Real.exp (4*x) := Real.add_one_le_exp _

private theorem summable_term_norm (s : ℂ) (hs : 2 < s.re) :
    Summable (fun n : ℕ => ‖term s n‖) := by
  classical
  let B (n : ℕ) : ℝ := (3/2:ℝ) * (n : ℝ)^(1-s.re)
  have hB (n : ℕ) : 0 ≤ B n := by dsimp [B]; positivity
  have hsumB : Summable B := ((Real.summable_nat_rpow.mpr (by linarith : 1-s.re < -1)).mul_left _)
  apply summable_of_sum_le (c := Real.exp (4 * ∑' n, B n)) (fun n => norm_nonneg _)
  intro t
  let N := t.sup id + 1
  have hNor (p : ℕ) : ‖posTerm s p‖ = ‖term s p‖ := by
    change ‖(‖term s p‖ : ℝ)‖ = ‖term s p‖
    exact Real.norm_of_nonneg (norm_nonneg _)
  have hloc := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := posTerm s) (fun {_} hp => (hNor _).trans_lt ((prime_norm_le s hs.le hp).trans_lt (by norm_num))) N
  let f (n : ℕ) : ℝ := (N.smoothNumbers).indicator (fun n : ℕ => ‖term s n‖) n
  have hsumf : Summable f := by
    apply (summable_subtype_iff_indicator (s := N.smoothNumbers)).mp
    change Summable (fun n : N.smoothNumbers => ‖term s (n : ℕ)‖)
    exact hloc.1.congr (fun n => hNor n)
  have htsumf : (∑' n, f n) = ∏ p ∈ N.primesBelow, (1-‖term s p‖)⁻¹ := by
    change (∑' n, (N.smoothNumbers).indicator (fun n : ℕ => ‖term s n‖) n) = _
    rw [← _root_.tsum_subtype]
    exact hloc.2.tsum_eq
  have heq : (∑ n ∈ t, ‖term s n‖) = ∑ n ∈ t, f n := by
    apply sum_congr rfl
    intro n hn
    by_cases hn₀ : n = 0
    · simp [hn₀, f, Set.indicator]
    · have hlt : n < N := Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)
      have hsm := Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hn₀) hlt
      exact (Set.indicator_of_mem hsm (fun n : ℕ => ‖term s n‖)).symm
  have hss : (∑ p ∈ N.primesBelow, ‖term s p‖) ≤ ∑' n, B n :=
    (sum_le_sum fun p hp => term_norm_upper s (Nat.prime_of_mem_primesBelow hp)).trans
      (hsumB.sum_le_tsum _ (fun n _ => hB n))
  calc
    (∑ n ∈ t, ‖term s n‖) = ∑ n ∈ t, f n := heq
    _ ≤ ∑' n, f n := hsumf.sum_le_tsum _ (fun n _ => Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)
    _ = ∏ p ∈ N.primesBelow, (1-‖term s p‖)⁻¹ := htsumf
    _ ≤ ∏ p ∈ N.primesBelow, Real.exp (4*‖term s p‖) := by
      apply prod_le_prod
      · intro p hp
        have hq := prime_norm_le s hs.le (Nat.prime_of_mem_primesBelow hp)
        exact inv_nonneg.mpr (by linarith)
      · exact fun p hp => inv_sub_le_exp (norm_nonneg _) (prime_norm_le s hs.le (Nat.prime_of_mem_primesBelow hp))
    _ = Real.exp (4 * ∑ p ∈ N.primesBelow, ‖term s p‖) := by rw [← Real.exp_sum, mul_sum]
    _ ≤ Real.exp (4 * ∑' n, B n) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hss (by norm_num))

private theorem term_prime (s : ℂ) (p : Nat.Primes) :
    term s p = (p : ℂ)^(-s) + (p : ℂ)^(1-s) := by
  let q : ℕ := p.val
  have hp : q.Prime := p.prop
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  change LSeries.term (fun n => (a n : ℂ)) s q = (q : ℂ)^(-s) + (q : ℂ)^(1-s)
  rw [LSeries.term_of_ne_zero hp.ne_zero, a_prime hp, Nat.cast_add, Nat.cast_one,
    sub_eq_add_neg, Complex.cpow_add 1 (-s) hq, Complex.cpow_one,
    Complex.cpow_neg, div_eq_mul_inv]
  ring

end PrimePlusOne

theorem OMA.solution : type_of% @OMA.S_oeis_a003959.main := by
  intro s hs
  change (∑' n, PrimePlusOne.term s n) = _
  have h := EulerProduct.eulerProduct_completely_multiplicative_tprod
    (f := PrimePlusOne.term s) (PrimePlusOne.summable_term_norm s hs)
  rw [← h]
  congr 1
  ext p
  rw [PrimePlusOne.term_prime]
  ring_nf
