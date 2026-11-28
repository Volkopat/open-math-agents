import OMAReductions.R_Erdos967_erdos_967_variants_finite_R1

-- Step Erdos967.erdos_967.variants.finite.R1.H2
-- Credit: @LordMike
-- The logarithms of distinct primes are linearly independent over the rationals: clear
-- denominators, move the negative coefficients to the other side, exponentiate to an equality
-- of two products of prime powers and compare factorisations.

namespace OMA.E967FH2

/-- The exponent of `p j` in `∏ p i ^ f i`. -/
lemma key {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (f : Fin k → ℕ) (j : Fin k) : (∏ i, p i ^ f i).factorization (p j) = f j := by
  rw [Nat.factorization_prod (fun i _ => pow_ne_zero _ (hp i).ne_zero),
    Finsupp.finsetSum_apply, Finset.sum_eq_single j]
  · rw [Nat.factorization_pow, Finsupp.smul_apply, (hp j).factorization,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
  · intro i _ hij
    rw [Nat.factorization_pow, Finsupp.smul_apply, (hp i).factorization,
      Finsupp.single_apply, if_neg (fun h => hij (hinj h)), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

lemma log_prod_nat {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime) (f : Fin k → ℕ) :
    Real.log ((∏ i, p i ^ f i : ℕ) : ℝ) = ∑ i, (f i : ℝ) * Real.log (p i) := by
  push_cast
  rw [Real.log_prod (fun i _ => pow_ne_zero _ (Nat.cast_ne_zero.mpr (hp i).ne_zero))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_pow]

lemma int_case {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (a : Fin k → ℤ) (h : ∑ i, (a i : ℝ) * Real.log (p i) = 0) : ∀ i, a i = 0 := by
  have hb : ∑ i, ((a i).toNat : ℝ) * Real.log (p i) =
      ∑ i, ((-a i).toNat : ℝ) * Real.log (p i) := by
    have hc : ∀ i, ((a i : ℤ) : ℝ) = ((a i).toNat : ℝ) - ((-a i).toNat : ℝ) := by
      intro i
      have h1 : (a i : ℤ) = ((a i).toNat : ℤ) - ((-a i).toNat : ℤ) := by omega
      exact_mod_cast congrArg (Int.cast : ℤ → ℝ) h1
    simp only [hc, sub_mul, Finset.sum_sub_distrib] at h
    linarith
  rw [← log_prod_nat p hp, ← log_prod_nat p hp] at hb
  have hpos : ∀ f : Fin k → ℕ, (0 : ℝ) < ((∏ i, p i ^ f i : ℕ) : ℝ) := fun f => by
    exact_mod_cast Nat.pos_of_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hp i).ne_zero)
  have heq : (∏ i, p i ^ (a i).toNat) = ∏ i, p i ^ (-a i).toNat := by
    exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.mpr (hpos _)) (Set.mem_Ioi.mpr (hpos _)) hb
  intro j
  have h1 := key p hp hinj (fun i => (a i).toNat) j
  have h2 := key p hp hinj (fun i => (-a i).toNat) j
  rw [heq, h2] at h1
  omega

lemma rat_cast (q : ℚ) : (q : ℝ) * q.den = q.num := by
  exact_mod_cast Rat.mul_den_eq_num q

end OMA.E967FH2

theorem OMA.solution : OMA.R_Erdos967_erdos_967_variants_finite_R1.H2 := by
  intro k p hp hinj
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Rat.smul_def] at hg
  have hdvd : ∀ i, (g i).den ∣ ∏ j, (g j).den := fun i =>
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hdpos : 0 < ∏ j, (g j).den := Finset.prod_pos fun j _ => (g j).den_pos
  have hcast : ∀ i, (((g i).num * (((∏ j, (g j).den) / (g i).den : ℕ) : ℤ) : ℤ) : ℝ) =
      (g i : ℝ) * ((∏ j, (g j).den : ℕ) : ℝ) := by
    intro i
    have h1 : ((∏ j, (g j).den : ℕ) : ℝ) =
        ((g i).den : ℝ) * (((∏ j, (g j).den) / (g i).den : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' (hdvd i)).symm
    rw [h1, ← mul_assoc, OMA.E967FH2.rat_cast, Int.cast_mul, Int.cast_natCast]
  have key := OMA.E967FH2.int_case p hp hinj
    (fun i => (g i).num * (((∏ j, (g j).den) / (g i).den : ℕ) : ℤ)) (by
      simp only [hcast]
      have hs : ∑ i, (g i : ℝ) * ((∏ j, (g j).den : ℕ) : ℝ) * Real.log (p i) =
          ((∏ j, (g j).den : ℕ) : ℝ) * ∑ i, (g i : ℝ) * Real.log (p i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [hs, hg, mul_zero])
  intro i
  have hi := key i
  rcases mul_eq_zero.mp hi with h | h
  · exact Rat.zero_of_num_zero h
  · exfalso
    have h' : (∏ j, (g j).den) / (g i).den = 0 := by exact_mod_cast h
    have := Nat.div_pos (Nat.le_of_dvd hdpos (hdvd i)) (g i).den_pos
    omega
