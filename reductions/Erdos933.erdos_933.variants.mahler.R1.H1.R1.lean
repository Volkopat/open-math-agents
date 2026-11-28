import OMAReductions.R_Erdos933_erdos_933_variants_mahler_R1
import Mathlib

/-!
Mahler's bound from the two-dimensional p-adic subspace theorem.
Use X and X-Y at the infinite place, and X,Y at the primes 2 and 3.
The norm product is written using the valuations of ab. Multiplying by
the positive denominator gives the inequality in H1.

Reference: J.-H. Evertse, The p-adic Subspace Theorem, May 2011,
Theorem 1.1, with r=n=2 and S={infinity,2,3}:
https://pub.math.leidenuniv.nl/~evertsejh/dio2011-padicsubspace.pdf
The subspace theorem is a remaining hypothesis, not proved here.
-/

namespace OMA.R_Erdos933_erdos_933_variants_mahler_R1_H1_R1
open Filter

/-- A fixed two-dimensional specialization of the p-adic subspace theorem. -/
def H1 : Prop :=
  ∀ (ε C : ℝ), 0 < ε → 0 < C →
    ∃ T : Finset (Submodule ℚ (ℚ × ℚ)),
      (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b →
        (a : ℝ) * |(a : ℝ) - (b : ℝ)| * (max (a : ℝ) (b : ℝ)) ^ ε ≤
          C * ((2 ^ padicValNat 2 (a*b) * 3 ^ padicValNat 3 (a*b) : ℕ) : ℝ) →
        ∃ W ∈ T, ((a : ℚ), (b : ℚ)) ∈ W

/-- A proper rational linear subspace meets this affine line in finitely many points. -/
def H2 : Prop :=
  ∀ W : Submodule ℚ (ℚ × ℚ), W ≠ ⊤ →
    {n : ℕ | ((n : ℚ), (n : ℚ) + 1) ∈ W}.Finite

theorem main : H1 → H2 → OMA.R_Erdos933_erdos_933_variants_mahler_R1.H1 := by
  intro subspace affine ε hε
  classical
  obtain ⟨T, proper, cover⟩ := subspace ε ((2 : ℝ)^ε) hε (by positivity)
  have hfinite := T.finite_toSet.biUnion (fun W hW => affine W (proper W hW))
  obtain ⟨B, hB⟩ := hfinite.bddAbove
  filter_upwards [eventually_ge_atTop (B+1), eventually_ge_atTop 1] with n hn hn1
  by_contra! bad
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn1
  have hsize : ((n : ℝ) + 1)^ε ≤ (2 : ℝ)^ε * (n : ℝ)^ε := by
    rw [← Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2) hn0.le]
    apply Real.rpow_le_rpow (by positivity) _ hε.le
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith
  have hpow : (n : ℝ) * (n : ℝ)^ε = (n : ℝ)^(1+ε) := by
    rw [Real.rpow_add hn0, Real.rpow_one]
  have hweight : (n : ℝ) * |(n : ℝ) - ((n+1 : ℕ) : ℝ)| *
      (max (n : ℝ) ((n+1 : ℕ) : ℝ))^ε ≤
      (2 : ℝ)^ε * ((2 ^ padicValNat 2 (n*(n+1)) *
        3 ^ padicValNat 3 (n*(n+1)) : ℕ) : ℝ) := by
    have hmax : max (n : ℝ) ((n+1 : ℕ) : ℝ) = (n : ℝ)+1 := by
      push_cast
      exact max_eq_right (by linarith)
    rw [hmax]
    norm_num only [Nat.cast_add, Nat.cast_one, sub_add_cancel_left, abs_neg, abs_one,
      mul_one]
    calc
      (n : ℝ) * ((n : ℝ)+1)^ε ≤ (n : ℝ) * ((2 : ℝ)^ε * (n : ℝ)^ε) :=
        mul_le_mul_of_nonneg_left hsize hn0.le
      _ = (2 : ℝ)^ε * (n : ℝ)^(1+ε) := by rw [← hpow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left bad (by positivity)
  obtain ⟨W, hWT, hnW⟩ := cover n (n+1) (by omega) (by omega)
    (by simp) hweight
  have hnB : n ≤ B := hB (by
    simp only [Set.mem_iUnion, Finset.mem_coe, Set.mem_ofPred_eq]
    refine ⟨W, hWT, ?_⟩
    simpa only [Nat.cast_add, Nat.cast_one] using hnW)
  omega

end OMA.R_Erdos933_erdos_933_variants_mahler_R1_H1_R1
