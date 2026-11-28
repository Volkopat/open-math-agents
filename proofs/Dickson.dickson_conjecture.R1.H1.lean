import OMAReductions.R_Dickson_dickson_conjecture_R1
import Mathlib

-- Step Dickson.dickson_conjecture.R1.H1: hypothesis H1 of reduction Dickson.dickson_conjecture.R1
-- Credit: @ivillar. At most one linear form: the empty family is trivial; for f = a X + b with a > 0 the Schinzel condition forces gcd(a, b) = 1, and Dirichlet's theorem (Mathlib Nat.forall_exists_prime_gt_and_zmodEq) gives infinitely many primes a n + b. Same argument as my Schinzel.schinzel_conjecture.R1.H1 step.

/-! Step Dickson.dickson_conjecture.R1.H1. -/

open Polynomial

namespace P8Dirichlet

lemma deg_one (f : ℤ[X]) (hdeg : f.natDegree = 1) (hlc : 0 < f.leadingCoeff)
    (hS : SchinzelCondition {f}) : Infinite {n : ℕ | (f.eval (n : ℤ)).natAbs.Prime} := by
  set a := f.coeff 1 with ha
  set b := f.coeff 0 with hb
  have hapos : 0 < a := by
    rw [ha, ← hdeg]
    exact hlc
  have heval : ∀ x : ℤ, f.eval x = a * x + b := by
    intro x
    conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdeg.le]
    simp [ha, hb]
  -- gcd(a, b) = 1 from the Schinzel condition
  have hcop : IsCoprime b (a.toNat : ℤ) := by
    rw [Int.toNat_of_nonneg hapos.le, Int.isCoprime_iff_gcd_eq_one]
    by_contra hne
    set g := Int.gcd b a with hg
    have hgpos : 0 < g := Int.gcd_pos_of_ne_zero_right b hapos.ne'
    have hp := Nat.minFac_prime hne
    obtain ⟨n, hn⟩ := hS (Nat.minFac g) hp
    apply hn f (Finset.mem_singleton_self f)
    rw [heval]
    have h1 : ((Nat.minFac g : ℕ) : ℤ) ∣ (g : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.minFac_dvd g)
    have hda : ((g : ℕ) : ℤ) ∣ a := Int.gcd_dvd_right b a
    have hdb : ((g : ℕ) : ℤ) ∣ b := Int.gcd_dvd_left b a
    exact dvd_add (dvd_mul_of_dvd_left (h1.trans hda) _) (h1.trans hdb)
  have hq : a.toNat ≠ 0 := by omega
  apply Set.infinite_coe_iff.mpr
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hpN, hpp, hmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq (N * a.toNat + b.natAbs) hq hcop
  have hdvd : (a.toNat : ℤ) ∣ (p : ℤ) - b := (Int.ModEq.symm hmod).dvd
  rw [Int.toNat_of_nonneg hapos.le] at hdvd
  obtain ⟨m, hm⟩ := hdvd
  have hpN' : ((N : ℤ) * a + |b|) < p := by
    have : (N * a.toNat + b.natAbs : ℕ) < p := hpN
    have h2 : ((N * a.toNat + b.natAbs : ℕ) : ℤ) = (N : ℤ) * a + |b| := by
      push_cast
      simp [Int.toNat_of_nonneg hapos.le]
    exact_mod_cast h2 ▸ (Int.ofNat_lt.mpr this)
  have hbabs : b ≤ |b| := le_abs_self b
  have hmN : (N : ℤ) < m := by
    by_contra hcon
    have hcon := not_lt.mp hcon
    have : a * m ≤ a * N := mul_le_mul_of_nonneg_left hcon hapos.le
    nlinarith
  refine ⟨m.toNat, ?_, ?_⟩
  · show (f.eval ((m.toNat : ℕ) : ℤ)).natAbs.Prime
    have hpm : a * m + b = (p : ℤ) := by linarith
    rw [heval, Int.toNat_of_nonneg (by omega), hpm]
    simpa using hpp
  · omega

theorem dickson_h1 : ∀ fs : Finset ℤ[X], (∀ f ∈ fs, f.degree = 1 ∧ BunyakovskyCondition f) →
    SchinzelCondition fs → fs.card ≤ 1 →
    Infinite {n : ℕ | ∀ f ∈ fs, (f.eval (n : ℤ)).natAbs.Prime} := by
  intro fs hB hS hcard
  rcases Finset.card_le_one_iff_subset_singleton.mp hcard with ⟨f, hf⟩
  rcases Finset.subset_singleton_iff.mp hf with rfl | rfl
  · simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, Set.setOf_true]
    exact Set.infinite_coe_iff.mpr Set.infinite_univ
  · obtain ⟨hdeg, hBf⟩ := hB f (Finset.mem_singleton_self f)
    have := deg_one f (Polynomial.natDegree_eq_of_degree_eq_some hdeg) hBf.2.2 hS
    simpa using this

end P8Dirichlet

theorem OMA.solution : OMA.R_Dickson_dickson_conjecture_R1.H1 :=
  P8Dirichlet.dickson_h1
