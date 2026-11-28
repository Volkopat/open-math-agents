import OMAStatements.S_oeis_a093454

/-!
The even factors of n! supply 2^(n/2). For n ≥ 16 this already exceeds
the largest number in the triangular block. The 2-adic exponent of an LCM
is the maximum of the individual exponents, so n! cannot divide this LCM.
The remaining cases give the five integral quotients observed by R. G. Wilson.
-/

namespace TriangularBlockLCM

open OMA.S_oeis_a093454

private theorem even_factors (m : ℕ) : 2^m ∣ (2*m).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨k, hk⟩ := ih
    rw [show 2*(m+1) = (2*m+1)+1 by omega, Nat.factorial_succ, Nat.factorial_succ, hk, pow_succ]
    exact ⟨(m+1)*(2*m+1)*k, by ring⟩

private theorem growth (m : ℕ) (hm : 8 ≤ m) : (2*m+1)*(m+1) < 2^m := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have square := Nat.mul_le_mul_left m (show 1 ≤ m by omega)
    rw [pow_succ]
    nlinarith

private theorem block_small (n : ℕ) (hn : 16 ≤ n) : n*(n+1)/2 < 2^(n/2) := by
  let m := n/2
  have h₁ : n ≤ 2*m+1 := by dsimp [m]; omega
  have h₂ := Nat.mul_le_mul h₁ (show n+1 ≤ 2*m+2 by omega)
  rw [show (2*m+1)*(2*m+2) = 2*((2*m+1)*(m+1)) by ring] at h₂
  exact lt_of_le_of_lt (show n*(n+1)/2 ≤ (2*m+1)*(m+1) by omega)
    (growth m (by dsimp [m]; omega))

private theorem large_nonintegral (n : ℕ) (hn : 16 ≤ n) : ¬ n.factorial ∣ blockLcm n := by
  intro hd
  have nz (x : ℕ) (hx : x ∈ block n) : x ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (Nat.zero_lt_succ _) (Finset.mem_Icc.mp hx).1)
  have lcmnz : blockLcm n ≠ 0 := Finset.lcm_ne_zero_iff.mpr nz
  have factorial := (even_factors (n/2)).trans
    (Nat.factorial_dvd_factorial (show 2*(n/2) ≤ n by omega))
  have high := (Nat.prime_two.pow_dvd_iff_le_factorization lcmnz).mp (factorial.trans hd)
  unfold blockLcm at high
  rw [Finset.factorization_lcm (f := id) nz] at high
  have low : (block n).sup (fun x => x.factorization 2) ≤ n/2-1 := by
    apply Finset.sup_le
    intro x hx
    by_contra! h
    have exceeds := (Nat.prime_two.pow_dvd_iff_le_factorization (nz x hx)).mpr
      (show n/2 ≤ x.factorization 2 by omega)
    have lb := Nat.le_of_dvd (Nat.pos_of_ne_zero (nz x hx)) exceeds
    have ub := (Finset.mem_Icc.mp (show x ∈ block n from hx)).2
    have gap := block_small n hn
    omega
  change n/2 ≤ (block n).sup (fun x => x.factorization 2) at high
  omega

/-- The exact five positive indices giving an integer quotient. -/
theorem integral_iff (n : ℕ) (hn : 1 ≤ n) :
    n.factorial ∣ blockLcm n ↔ n ∈ ({1,2,3,4,6} : Finset ℕ) := by
  by_cases small : n < 16
  · interval_cases n <;> decide
  · have h := large_nonintegral n (by omega)
    simp only [h, false_iff, Finset.mem_insert, Finset.mem_singleton]
    omega

end TriangularBlockLCM

open OMA.S_oeis_a093454 TriangularBlockLCM

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a093454.main) := by
  intro finite
  obtain ⟨m, hm⟩ := finite.bddAbove
  have mem : m+16 ∈ {n : ℕ | 1 ≤ n ∧ ¬ n.factorial ∣ blockLcm n} :=
    ⟨by omega, large_nonintegral _ (by omega)⟩
  have := hm mem
  omega
