import OMAReductions.R_Erdos1140_erdos_1140_R1
import Mathlib

/-!
# Finiteness of exceptional primes in the classes 19 and 31 modulo 60

Credit: @connoranderson. This file transports the strong uniqueness result for
real quadratic orders of discriminant parameter `m = 2*n` to the exceptional
prime set in the Erdős 1140 finiteness problem. Its mathematical ingredients
are Epure and Gica's near-square shape result and the Mollin–Williams
Richaud–Degert classification. The kernel-checked Lean proofs are adapted from
@marcusbuffett's reductions and principal-ideal proof (PRs 4196 and 4648),
incorporating Frankie Wang's QuadraticNumberFields lemmas, and @mattdorman's
classification proof (PR 14620). The sieve equivalence in the original
reduction is due to @sntntHb and follows the variant proof by @TheWaler.

Sources: https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4196
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4648
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/14620
-/


open Erdos1140
namespace Erdos1140FiniteExceptions

private lemma square_mod (x : ℕ) : x^2%8=0 ∨ x^2%8=1 ∨ x^2%8=4 := by
  have h : ∀ a : Fin 8, a.val^2%8=0 ∨ a.val^2%8=1 ∨ a.val^2%8=4 := by decide
  simpa [Nat.pow_mod] using h ⟨x%8,Nat.mod_lt _ (by decide)⟩

private lemma no_root {n : ℕ} (res : n%4=3) (prop : Erdos1140Prop n)
    {p : ℕ} (hp : p.Prime) (odd : p ≠ 2) (le : p^2 ≤ 2*n) (a : ZMod p) :
    2*a^2 ≠ (n : ZMod p) := by
  intro eq
  let _ : Fact p.Prime := ⟨hp⟩
  let r := a.valMinAbs.natAbs
  have hr : r ≤ p/2 := ZMod.natAbs_valMinAbs_le a
  have oddp := hp.eq_two_or_odd.resolve_left odd
  have pr : 2*r+1 ≤ p := by omega
  have sp := square_mod p
  have gap : p^2+1 < 2*n := by omega
  have hsq := Nat.pow_le_pow_left pr 2
  have room : 2*r^2+p < n := by
    zify at pr gap ⊢
    nlinarith [mul_nonneg (show 0 ≤ (p:ℤ) - (2*r+1) by omega)
      (show 0 ≤ (p:ℤ) + (2*r+1) - 2 by omega)]
  have er : 2*(r:ZMod p)^2=(n:ZMod p) := by
    change 2*(a.valMinAbs.natAbs:ZMod p)^2 = _
    rw [ZMod.natCast_natAbs_valMinAbs]
    split <;> simpa using eq
  have hd : p ∣ n-2*r^2 := by
    apply (ZMod.natCast_eq_zero_iff ..).mp
    rw [Nat.cast_sub (by omega)]
    push_cast
    rw [er,sub_self]
  have prime := prop.2 r (by omega)
  have e := (Nat.prime_dvd_prime_iff_eq hp prime).mp hd
  omega

private lemma nearest (n : ℕ) : ∃ k d : ℕ, d ≤ (2*n).sqrt ∧
    (n=2*k^2+d ∨ 2*k^2=n+d) := by
  let s := (2*n).sqrt
  let j := s/2
  have lo : s^2 ≤ 2*n := Nat.sqrt_le' _
  have hi : 2*n < (s+1)^2 := Nat.lt_succ_sqrt' _
  have cases : s=2*j ∨ s=2*j+1 := by dsimp [j]; omega
  rcases cases with e | e
  · rw [e] at lo hi
    have low : 2*j^2 ≤ n := by nlinarith
    refine ⟨j,n-2*j^2,?_,Or.inl (by omega)⟩
    change n-2*j^2 ≤ s
    rw [e]
    have up : n ≤ 2*j^2+2*j := by nlinarith
    omega
  · rw [e] at lo hi
    have up : n ≤ 2*(j+1)^2 := by nlinarith
    refine ⟨j+1,2*(j+1)^2-n,?_,Or.inr (by omega)⟩
    change 2*(j+1)^2-n ≤ s
    rw [e]
    have h : 2*(j+1)^2 ≤ n+(2*j+1) := by nlinarith
    omega

private lemma shape {n : ℕ} (res : n%4=3) (prop : Erdos1140Prop n)
    (one : ∀ x : ℕ, n ≠ 2*x^2+1) : ∃ y : ℕ, 2*n+2=(4*y)^2 := by
  obtain ⟨k,d,le,h⟩ := nearest n
  have odd : d%2=1 := by rcases h with h|h <;> omega
  have d1 : d=1 := by
    by_contra hn
    let p := d.minFac
    have hp : p.Prime := Nat.minFac_prime hn
    have pd : p ∣ d := Nat.minFac_dvd _
    have pn : p ≠ 2 := by intro e; rw [e] at pd; omega
    have small : p^2 ≤ 2*n := Nat.le_sqrt'.mp ((Nat.le_of_dvd (by omega) pd).trans le)
    apply no_root res prop hp pn small (k : ZMod p)
    have zero := (ZMod.natCast_eq_zero_iff d p).mpr pd
    rcases h with h | h
    · have e := congrArg (fun x : ℕ => (x : ZMod p)) h
      push_cast at e
      simpa [zero] using e.symm
    · have e := congrArg (fun x : ℕ => (x : ZMod p)) h
      push_cast at e
      simpa [zero] using e
  subst d
  rcases h with h | h
  · exact (one k h).elim
  have ke : k%2=0 := by
    have ks := square_mod k
    by_contra hn
    have : k^2%2=1 := by rw [Nat.pow_mod]; simp [show k%2=1 by omega]
    omega
  refine ⟨k/2,?_⟩
  have ek : k=2*(k/2) := by omega
  conv_lhs at h => rw [ek]
  nlinarith

/-- Minkowski's bound for this real quadratic order is sqrt(2n). The small
odd primes are inert and the displayed norm-two element handles the ramified prime. -/
def H1 : Prop :=
  ∀ n : ℕ, n.Prime → n%4=3 → (∃ y : ℕ, 2*n+2=(4*y)^2) →
    (∀ p : ℕ, p.Prime → p ≠ 2 → p^2 ≤ 2*n → ∀ a : ZMod p, 2*a^2 ≠ (n:ZMod p)) →
    IsPrincipalIdealRing (Zsqrtd (2*(n:ℤ)))

/-- The class-number-one classification in the indicated Richaud–Degert family,
after removing the three known values 14, 62 and 398 of the radicand. -/
def H2 : Prop :=
  {m : ℕ | 398 < m ∧ (∃ y : ℕ, m+2=(4*y)^2) ∧ Squarefree m ∧
    IsPrincipalIdealRing (Zsqrtd (m:ℤ))}.Subsingleton


end Erdos1140FiniteExceptions

/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
The quadratic field, integrality, discriminant and real-place lemmas below are adapted
from WangFrankie/QuadraticNumberFields, revision a458ae67e9a10e91355afaebfdd55ecbceebc4bc,
under the Apache 2.0 license. The application to the prime ideals of the order is original.
-/
noncomputable section
section
lemma Squarefree.not_mul_self_dvd_of_not_isUnit {R : Type*} [Monoid R]
    {r p : R} (hr : Squarefree r) (hp : ¬ IsUnit p) : ¬ p * p ∣ r := by
  intro h
  have hp2 : p ^ 2 ∣ r := by simpa [pow_two] using h
  have hsq : Squarefree (p ^ 2) := Squarefree.squarefree_of_dvd hp2 hr
  have hbad : (2 : ℕ) = 0 ∨ (2 : ℕ) = 1 :=
    Squarefree.eq_zero_or_one_of_pow_of_not_isUnit hsq hp
  omega
lemma squarefree_int_not_dvd_four (d : ℤ) (hd : Squarefree d) : ¬ (4 : ℤ) ∣ d := by
  intro h
  exact Squarefree.not_mul_self_dvd_of_not_isUnit hd (p := (2 : ℤ))
    (fun hunit => absurd (Int.isUnit_iff.mp hunit) (by omega)) (by simpa using h)
lemma squarefree_int_emod_four (d : ℤ) (hd : Squarefree d) :
    d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by
  have hnd : ¬ (4 : ℤ) ∣ d := squarefree_int_not_dvd_four d hd
  omega
lemma eq_one_of_squarefree_isSquare {d : ℤ} (hd : Squarefree d) (hsq : IsSquare d) :
    d = 1 ∨ d = -1 := by
  obtain ⟨z, rfl⟩ := hsq
  have hsqz2 : Squarefree (z ^ 2) := by simpa [pow_two] using hd
  have huz : IsUnit z := by
    by_contra hne
    have h01 : (2 : ℕ) = 0 ∨ (2 : ℕ) = 1 :=
      Squarefree.eq_zero_or_one_of_pow_of_not_isUnit (x := z) (n := 2) hsqz2 hne
    norm_num at h01
  rcases Int.isUnit_iff.mp huz with rfl | rfl <;> simp
end

section
namespace QuadraticAlgebra

section CommSemiring

variable {R : Type*} [CommSemiring R] {a b : R}
theorem leftMulMatrix_eq (x : QuadraticAlgebra R a b) :
    Algebra.leftMulMatrix (basis a b) x = !![x.re, a * x.im; x.im, x.re + b * x.im] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    rw [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply]
    simp [QuadraticAlgebra.basis]

end CommSemiring
section Int

open Matrix
theorem trace_int (a b : ℤ) (x : QuadraticAlgebra ℤ a b) :
    Algebra.trace ℤ (QuadraticAlgebra ℤ a b) x = 2 * x.re + b * x.im := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis a b)]
  rw [leftMulMatrix_eq]
  simp [Matrix.trace, Fin.sum_univ_two]
  ring
theorem traceMatrix_basis_int (a b : ℤ) :
    Algebra.traceMatrix ℤ (QuadraticAlgebra.basis a b) =
      !![2, b; b, 2 * a + b ^ 2] := by
  ext i j
  simp only [Algebra.traceMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [trace_int, QuadraticAlgebra.basis, pow_two]
theorem discr_basis_int (a b : ℤ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis a b) = 4 * a + b ^ 2 := by
  rw [Algebra.discr_def, traceMatrix_basis_int]
  simp [Matrix.det_fin_two]
  ring

end Int

end QuadraticAlgebra
end

section
lemma nat_eq_one_of_squarefree_intcast_of_isSquare (m : ℕ)
    (hsm : Squarefree (m : ℤ)) (hsq : IsSquare (m : ℤ)) : m = 1 := by
  have hmz : (m : ℤ) = 1 ∨ (m : ℤ) = -1 :=
    eq_one_of_squarefree_isSquare hsm hsq
  cases hmz with
  | inl h => exact_mod_cast h
  | inr h => omega
lemma int_dvd_of_ratio_square (d₁ d₂ : ℤ) (hd₂ : d₂ ≠ 0)
    (hsq_d₂ : Squarefree d₂) (hr : IsSquare ((d₁ : ℚ) / (d₂ : ℚ))) : d₂ ∣ d₁ := by
  have hsq_den_nat : IsSquare (((d₁ : ℚ) / (d₂ : ℚ)).den) := (Rat.isSquare_iff.mp hr).2
  have hsq_den_int : IsSquare ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) := by
    rcases hsq_den_nat with ⟨n, hn⟩
    refine ⟨(n : ℤ), by exact_mod_cast hn⟩
  have hden_dvd : ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) ∣ d₂ := by
    simpa [← Rat.divInt_eq_div] using (Rat.den_dvd d₁ d₂)
  have hsqf_den_int : Squarefree ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) :=
    Squarefree.squarefree_of_dvd hden_dvd hsq_d₂
  have hden1_nat : ((d₁ : ℚ) / (d₂ : ℚ)).den = 1 :=
    nat_eq_one_of_squarefree_intcast_of_isSquare _ hsqf_den_int hsq_den_int
  exact (Rat.den_div_intCast_eq_one_iff d₁ d₂ hd₂).1 hden1_nat
end

section
lemma Int.sq_emod_four_of_even (n : ℤ) (h : 2 ∣ n) : n ^ 2 % 4 = 0 := by
  obtain ⟨k, rfl⟩ := h
  ring_nf
  omega
lemma Int.sq_emod_four_of_odd (n : ℤ) (h : ¬ 2 ∣ n) : n ^ 2 % 4 = 1 := by
  set k := n / 2
  have hk : n = 2 * k + 1 := by omega
  rw [hk]
  ring_nf
  omega

private lemma div4_iff_mod (a' b' d : ℤ) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔ (a' ^ 2 - d * b' ^ 2) % 4 = 0 := by
  omega

private lemma sq_eq_four_mul_div_of_even (n : ℤ) (h : 2 ∣ n) :
    n ^ 2 = 4 * (n ^ 2 / 4) := by
  have hn2 : n ^ 2 % 4 = 0 := Int.sq_emod_four_of_even n h
  omega

private lemma sq_eq_four_mul_div_add_one_of_odd (n : ℤ) (h : ¬ 2 ∣ n) :
    n ^ 2 = 4 * (n ^ 2 / 4) + 1 := by
  have hn2 : n ^ 2 % 4 = 1 := Int.sq_emod_four_of_odd n h
  omega

private lemma odd_eq_two_mul_div_add_one (n : ℤ) (h : ¬ 2 ∣ n) :
    n = 2 * (n / 2) + 1 := by
  omega

private lemma even_odd_impossible_of_mod_eq_zero
    (d a' b' : ℤ) (hd : Squarefree d)
    (hmod : (a' ^ 2 - d * b' ^ 2) % 4 = 0)
    (ha : 2 ∣ a') (hb : ¬ 2 ∣ b') : False := by
  have hmod' := hmod
  have ha_eq : a' ^ 2 = 4 * (a' ^ 2 / 4) := sq_eq_four_mul_div_of_even a' ha
  have hb_eq : b' ^ 2 = 4 * (b' ^ 2 / 4) + 1 := sq_eq_four_mul_div_add_one_of_odd b' hb
  rw [hb_eq] at hmod'
  ring_nf at hmod'
  have hdvd : (4 : ℤ) ∣ d := by omega
  exact squarefree_int_not_dvd_four d hd hdvd

private lemma odd_even_impossible_of_mod_eq_zero
    (d a' b' : ℤ) (hmod : (a' ^ 2 - d * b' ^ 2) % 4 = 0)
    (ha : ¬ 2 ∣ a') (hb : 2 ∣ b') : False := by
  have hmod' := hmod
  have ha_eq : a' ^ 2 = 4 * (a' ^ 2 / 4) + 1 := sq_eq_four_mul_div_add_one_of_odd a' ha
  have hb_eq : b' ^ 2 = 4 * (b' ^ 2 / 4) := sq_eq_four_mul_div_of_even b' hb
  rw [ha_eq, hb_eq] at hmod'
  ring_nf at hmod'
  omega

private lemma mod_four_eq_one_of_odd_odd_of_mod_eq_zero
    (d a' b' : ℤ) (hmod : (a' ^ 2 - d * b' ^ 2) % 4 = 0)
    (ha : ¬ 2 ∣ a') (hb : ¬ 2 ∣ b') : d % 4 = 1 := by
  have hmod' := hmod
  have ha_eq : a' ^ 2 = 4 * (a' ^ 2 / 4) + 1 := sq_eq_four_mul_div_add_one_of_odd a' ha
  have hb_eq : b' ^ 2 = 4 * (b' ^ 2 / 4) + 1 := sq_eq_four_mul_div_add_one_of_odd b' hb
  rw [ha_eq, hb_eq] at hmod'
  ring_nf at hmod'
  omega
theorem dvd_four_sub_sq_iff_even_even_or_odd_odd_mod_four_one
    (d a' b' : ℤ) (hd : Squarefree d) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔
      (2 ∣ a' ∧ 2 ∣ b') ∨ (¬ 2 ∣ a' ∧ ¬ 2 ∣ b' ∧ d % 4 = 1) := by
  constructor
  · intro hdvd
    have hmod : (a' ^ 2 - d * b' ^ 2) % 4 = 0 := (div4_iff_mod a' b' d).1 hdvd
    by_cases ha : 2 ∣ a' <;> by_cases hb : 2 ∣ b'
    · exact Or.inl ⟨ha, hb⟩
    · exact (even_odd_impossible_of_mod_eq_zero d a' b' hd hmod ha hb).elim
    · exact (odd_even_impossible_of_mod_eq_zero d a' b' hmod ha hb).elim
    · exact Or.inr ⟨ha, hb, mod_four_eq_one_of_odd_odd_of_mod_eq_zero d a' b' hmod ha hb⟩
  · intro h
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb, hd1⟩
    · obtain ⟨p, rfl⟩ := ha
      obtain ⟨q, rfl⟩ := hb
      exact ⟨p ^ 2 - d * q ^ 2, by ring⟩
    · have ha_eq : a' = 2 * (a' / 2) + 1 := odd_eq_two_mul_div_add_one a' ha
      have hb_eq : b' = 2 * (b' / 2) + 1 := odd_eq_two_mul_div_add_one b' hb
      rw [ha_eq, hb_eq]
      ring_nf
      have hd_eq : d = 4 * (d / 4) + 1 := by omega
      rw [hd_eq]
      ring_nf
      omega
theorem even_even_of_dvd_four_sub_sq_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1)
    (h : 4 ∣ (a' ^ 2 - d * b' ^ 2)) :
    2 ∣ a' ∧ 2 ∣ b' := by
  rcases (dvd_four_sub_sq_iff_even_even_or_odd_odd_mod_four_one d a' b' hd).mp h with
      hab | ⟨_, _, hd1⟩
  · exact hab
  · exact absurd hd1 hd4
theorem dvd_four_sub_sq_iff_even_even_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔ (2 ∣ a' ∧ 2 ∣ b') := by
  constructor
  · exact even_even_of_dvd_four_sub_sq_of_ne_one_mod_four d a' b' hd hd4
  · exact fun h => (dvd_four_sub_sq_iff_even_even_or_odd_odd_mod_four_one d a' b' hd).2 (Or.inl h)
end

section
abbrev Qsqrtd (d : ℚ) : Type := QuadraticAlgebra ℚ d 0
namespace Qsqrtd

open QuadraticAlgebra

variable {d : ℚ}

@[simp] theorem trace_eq_re_add_re_star (x : Qsqrtd d) :
    Algebra.trace ℚ (Qsqrtd d) x = x.re + (star x).re := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis d 0),
    QuadraticAlgebra.leftMulMatrix_eq, Matrix.trace_fin_two_of]
  simp

theorem trace_eq_two_re (x : Qsqrtd d) :
    Algebra.trace ℚ (Qsqrtd d) x = 2 * x.re := by
  rw [trace_eq_re_add_re_star]
  simp
  ring

abbrev norm {d : ℚ} (x : Qsqrtd d) : ℚ := QuadraticAlgebra.norm x

instance instFact_of_not_isSquare (d : ℚ) [Fact (¬ IsSquare d)] :
    Fact (∀ r : ℚ, r ^ 2 ≠ d + 0 * r) :=
  ⟨by intro r hr; exact (Fact.out : ¬ IsSquare d) ⟨r, by nlinarith [hr]⟩⟩

theorem finrank_ratAlgebra_eq_finrank_quadraticAlgebra (d : ℚ)
    [Fact (¬ IsSquare d)] :
    @Module.finrank ℚ (Qsqrtd d) _ _
      (@Algebra.toModule ℚ (Qsqrtd d) _ _ DivisionRing.toRatAlgebra) =
    @Module.finrank ℚ (Qsqrtd d) _ _
      (@Algebra.toModule ℚ (Qsqrtd d) _ _ QuadraticAlgebra.instAlgebra) := by
  symm
  refine @Algebra.finrank_eq_of_equiv_equiv ℚ (Qsqrtd d) _ _
    QuadraticAlgebra.instAlgebra ℚ (Qsqrtd d) _ _ DivisionRing.toRatAlgebra
    (RingEquiv.refl ℚ) (RingEquiv.refl (Qsqrtd d)) ?_
  exact RingHom.ext_rat _ _

section RatAlgebra

local instance ratAlg1140 (d:ℚ) [Fact (¬IsSquare d)] : Algebra ℚ (Qsqrtd d) := DivisionRing.toRatAlgebra

theorem finrank_ratAlgebra_eq_two (d : ℚ) [Fact (¬ IsSquare d)] :
    @Module.finrank ℚ (Qsqrtd d) _ _
      (@Algebra.toModule ℚ (Qsqrtd d) _ _ DivisionRing.toRatAlgebra) = 2 := by
  rw [finrank_ratAlgebra_eq_finrank_quadraticAlgebra]
  exact QuadraticAlgebra.finrank_eq_two d 0

instance instRatAlgebraIsQuadraticExtension (d : ℚ) [Fact (¬ IsSquare d)] :
    Algebra.IsQuadraticExtension ℚ (Qsqrtd d) where
  finrank_eq_two' := finrank_ratAlgebra_eq_two d

end RatAlgebra
end Qsqrtd

lemma not_isSquare_int_of_squarefree_ne_one {d : ℤ}
    (hd : Squarefree d) (h1 : d ≠ 1) : ¬ IsSquare d := by
  intro hsq
  rcases eq_one_of_squarefree_isSquare hd hsq with rfl | rfl <;> simp_all

lemma not_isSquare_ratCast_of_squarefree_ne_one {d : ℤ}
    (hd : Squarefree d) (h1 : d ≠ 1) : ¬ IsSquare ((d : ℤ) : ℚ) := by
  intro hsqQ
  exact not_isSquare_int_of_squarefree_ne_one hd h1 (Rat.isSquare_intCast_iff.mp hsqQ)

instance instFact_not_isSquare_ratCast_of_squarefree_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Fact (¬ IsSquare ((d : ℤ) : ℚ)) :=
  ⟨not_isSquare_ratCast_of_squarefree_ne_one
    (d := d) (Fact.out : Squarefree d) (Fact.out : d ≠ 1)⟩
end

section

class QuadraticField (K : Type*) [Field K] [Algebra ℚ K] : Prop where

  isQuadratic : Algebra.IsQuadraticExtension ℚ K

instance (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] :
    Algebra.IsQuadraticExtension ℚ K :=
  QuadraticField.isQuadratic

namespace QuadraticField

theorem finrank_eq_two (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] :
    Module.finrank ℚ K = 2 :=
  Algebra.IsQuadraticExtension.finrank_eq_two ℚ K

end QuadraticField

instance QuadraticField.instNumberField (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] : NumberField K where
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  to_finiteDimensional := by
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
    convert FiniteDimensional.of_finrank_pos (K := ℚ) (V := K) (by
      rw [QuadraticField.finrank_eq_two K]; omega) using 1
    congr 1
    exact Subsingleton.elim _ _

namespace Qsqrtd

instance instQuadraticField (d : ℚ) [Fact (¬ IsSquare d)] :
    QuadraticField (Qsqrtd d) where
  isQuadratic := inferInstance

section RatAlgebra

local instance ratAlgB1140 (d:ℚ) [Fact (¬IsSquare d)] : Algebra ℚ (Qsqrtd d) := DivisionRing.toRatAlgebra

instance instRatAlgebraQuadraticField (d : ℚ) [Fact (¬ IsSquare d)] :
    QuadraticField (Qsqrtd d) where
  isQuadratic := @Qsqrtd.instRatAlgebraIsQuadraticExtension d _

end RatAlgebra

end Qsqrtd
end

section
namespace QuadraticNumberFields

abbrev Zsqrtd (d : ℤ) : Type := QuadraticAlgebra ℤ d 0

namespace Zsqrtd

variable {d : ℤ}
theorem ext {x y : Zsqrtd d} (hre : x.re = y.re) (him : x.im = y.im) : x = y :=
  QuadraticAlgebra.ext hre him

def toQsqrtd (z : Zsqrtd d) : Qsqrtd (d : ℚ) := ⟨(z.re : ℚ), (z.im : ℚ)⟩

def toQsqrtdHom (d : ℤ) : Zsqrtd d →+* Qsqrtd (d : ℚ) where
  toFun := fun z => ⟨(z.re : ℚ), (z.im : ℚ)⟩
  map_one' := by
    change ({ re := ((1 : ℤ) : ℚ), im := ((0 : ℤ) : ℚ) } : Qsqrtd (d : ℚ)) = 1
    rfl
  map_mul' := by
    intro x y
    ext <;> simp [mul_assoc, mul_comm, mul_left_comm]
  map_zero' := by
    change ({ re := ((0 : ℤ) : ℚ), im := ((0 : ℤ) : ℚ) } : Qsqrtd (d : ℚ)) = 0
    rfl
  map_add' := by
    intro x y
    ext <;> simp

@[simp] theorem toQsqrtdHom_apply (d : ℤ) (z : Zsqrtd d) :
    toQsqrtdHom d z = toQsqrtd z := rfl

theorem toQsqrtdHom_injective (d : ℤ) : Function.Injective (toQsqrtdHom d) := by
  intro x y hxy
  ext
  · simpa [toQsqrtdHom] using congrArg QuadraticAlgebra.re hxy
  · simpa [toQsqrtdHom] using congrArg QuadraticAlgebra.im hxy

def halfInt (a' b' : ℤ) : Qsqrtd (d : ℚ) :=
  ⟨(a' : ℚ) / 2, (b' : ℚ) / 2⟩

theorem halfInt_mem_range_toQsqrtdHom_iff_even_even (d a' b' : ℤ) :
    (∃ z : Zsqrtd d, toQsqrtdHom d z = halfInt (d := d) a' b') ↔ (2 ∣ a' ∧ 2 ∣ b') := by
  constructor
  · rintro ⟨z, hz⟩
    have hm : (a' : ℚ) / 2 = z.re := by
      simpa [toQsqrtdHom, halfInt] using congrArg QuadraticAlgebra.re hz.symm
    have hn : (b' : ℚ) / 2 = z.im := by
      simpa [toQsqrtdHom, halfInt] using congrArg QuadraticAlgebra.im hz.symm
    refine ⟨?_, ?_⟩
    · refine ⟨z.re, ?_⟩
      have hq : (a' : ℚ) = 2 * z.re := by nlinarith [hm]
      exact_mod_cast hq
    · refine ⟨z.im, ?_⟩
      have hq : (b' : ℚ) = 2 * z.im := by nlinarith [hn]
      exact_mod_cast hq
  · rintro ⟨ha, hb⟩
    rcases ha with ⟨m, hm⟩
    rcases hb with ⟨n, hn⟩
    refine ⟨⟨m, n⟩, ?_⟩
    ext <;> simp [toQsqrtdHom, halfInt, hm, hn]
end Zsqrtd
end QuadraticNumberFields
end

section
namespace QuadraticNumberFields
namespace RingOfIntegers

abbrev halfInt (d : ℤ) (a' b' : ℤ) : Qsqrtd (d : ℚ) :=
  Zsqrtd.halfInt (d := d) a' b'

abbrev omegaHalf (d : ℤ) : Qsqrtd (d : ℚ) := halfInt d 1 1

@[simp] theorem halfInt_re (d a' b' : ℤ) :
    (halfInt d a' b').re = (a' : ℚ) / 2 := rfl

@[simp] theorem halfInt_im (d a' b' : ℤ) :
    (halfInt d a' b').im = (b' : ℚ) / 2 := rfl

theorem norm_halfInt (d a' b' : ℤ) :
    Qsqrtd.norm (halfInt d a' b') = (a' ^ 2 - (d : ℚ) * b' ^ 2) / 4 := by
  simp [halfInt, Qsqrtd.norm, QuadraticAlgebra.norm]
  ring

end RingOfIntegers
end QuadraticNumberFields
end

section
namespace QuadraticNumberFields
namespace RingOfIntegers
namespace TraceNorm

namespace Qsqrtd

theorem add_star_eq_trace_image {d : ℤ} (x : Qsqrtd (d : ℚ)) :
    x + star x =
      algebraMap ℚ (Qsqrtd (d : ℚ)) (Algebra.trace ℚ (Qsqrtd (d : ℚ)) x) := by
  ext
  · simp [Qsqrtd.trace_eq_re_add_re_star, star]
  · simp [star]

theorem norm_image_eq_mul_star {d : ℤ} (x : Qsqrtd (d : ℚ)) :
    algebraMap ℚ (Qsqrtd (d : ℚ)) (Qsqrtd.norm x) = x * star x := by
  simpa [Qsqrtd.norm, mul_comm] using
    (QuadraticAlgebra.algebraMap_norm_eq_mul_star (a := (d : ℚ)) (b := (0 : ℚ)) x)

end Qsqrtd

private lemma isIntegral_star {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (star x) :=
  map_isIntegral_int (starRingEnd (Qsqrtd (d : ℚ))) hx

theorem norm_eq_sqr_minus_d_sqr {d : ℤ} (x : Qsqrtd (d : ℚ)) :
    Qsqrtd.norm x = x.re ^ 2 - (d : ℚ) * x.im ^ 2 := by
  simp [Qsqrtd.norm, QuadraticAlgebra.norm]
  ring

private lemma isIntegral_trace_image {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (algebraMap ℚ (Qsqrtd (d : ℚ)) (Algebra.trace ℚ (Qsqrtd d) x)) := by
  simpa [Qsqrtd.add_star_eq_trace_image x] using hx.add (isIntegral_star hx)

private lemma isIntegral_trace {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (Algebra.trace ℚ (Qsqrtd d) x) :=
  (isIntegral_algHom_iff (algebraMap ℚ (Qsqrtd (d : ℚ))).toIntAlgHom
    (algebraMap ℚ (Qsqrtd (d : ℚ))).injective).1 (isIntegral_trace_image hx)

lemma exists_int_trace {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    ∃ a' : ℤ, (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x := by
  obtain ⟨a', ha'⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1
    (isIntegral_trace hx)
  exact ⟨a', by simpa using ha'⟩

private lemma isIntegral_norm_image {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (algebraMap ℚ (Qsqrtd (d : ℚ)) (Qsqrtd.norm x)) := by
  simpa [Qsqrtd.norm_image_eq_mul_star x] using hx.mul (isIntegral_star hx)

private lemma isIntegral_norm {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (Qsqrtd.norm x) :=
  (isIntegral_algHom_iff (algebraMap ℚ (Qsqrtd (d : ℚ))).toIntAlgHom
    (algebraMap ℚ (Qsqrtd (d : ℚ))).injective).1 (isIntegral_norm_image hx)

lemma exists_int_norm {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    ∃ n' : ℤ, (n' : ℚ) = Qsqrtd.norm x := by
  obtain ⟨n', hn'⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1
    (isIntegral_norm hx)
  exact ⟨n', by simpa using hn'⟩

lemma re_eq_half_trace_int {d : ℤ} {x : Qsqrtd (d : ℚ)} {a' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x) :
    x.re = (a' : ℚ) / 2 := by
  nlinarith [show 2 * x.re = (a' : ℚ) by
    calc
      2 * x.re = Algebra.trace ℚ (Qsqrtd d) x := (Qsqrtd.trace_eq_two_re x).symm
      _ = (a' : ℚ) := ha'trace.symm]

lemma isIntegral_of_sq_int {q : ℚ} {k : ℤ} (hq2 : q ^ 2 = (k : ℚ)) :
    IsIntegral ℤ q := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C k,
    Polynomial.monic_X_pow_sub_C (R := ℤ) (n := 2) k (by decide), ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
  simp [hq2]

private lemma double_im_sq_mul_eq
    (d : ℤ) {x : Qsqrtd (d : ℚ)} {a' n' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    (d : ℚ) * (2 * x.im) ^ 2 = (a' ^ 2 - 4 * n' : ℤ) := by
  have hre : x.re = (a' : ℚ) / 2 := re_eq_half_trace_int ha'trace
  have hnorm' :
      (n' : ℚ) = ((a' : ℚ) / 2) ^ 2 - (d : ℚ) * x.im ^ 2 := by
    calc
      (n' : ℚ) = Qsqrtd.norm x := hn'norm
      _ = x.re ^ 2 - (d : ℚ) * x.im ^ 2 := norm_eq_sqr_minus_d_sqr x
      _ = ((a' : ℚ) / 2) ^ 2 - (d : ℚ) * x.im ^ 2 := by simp [hre]
  have haux : (a' : ℚ) ^ 2 - 4 * (n' : ℚ) = 4 * (d : ℚ) * x.im ^ 2 := by
    nlinarith [hnorm']
  have hmcast : ((a' ^ 2 - 4 * n' : ℤ) : ℚ) = (a' : ℚ) ^ 2 - 4 * (n' : ℚ) := by
    norm_cast
  calc
    (d : ℚ) * (2 * x.im) ^ 2 = 4 * (d : ℚ) * x.im ^ 2 := by ring
    _ = (a' : ℚ) ^ 2 - 4 * (n' : ℚ) := by linarith [haux]
    _ = (a' ^ 2 - 4 * n' : ℤ) := hmcast.symm

private lemma double_im_sq_eq_ratio
    (d : ℤ) (hd0Q : (d : ℚ) ≠ 0) {x : Qsqrtd (d : ℚ)} {a' n' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    (2 * x.im) ^ 2 = (a' ^ 2 - 4 * n' : ℤ) / (d : ℚ) := by
  calc
    (2 * x.im) ^ 2 = ((d : ℚ) * (2 * x.im) ^ 2) / (d : ℚ) := by field_simp [hd0Q]
    _ = (a' ^ 2 - 4 * n' : ℤ) / (d : ℚ) := by
      simp [double_im_sq_mul_eq d ha'trace hn'norm]

private lemma isSquare_trace_norm_ratio
    (d : ℤ) (hd0Q : (d : ℚ) ≠ 0) {x : Qsqrtd (d : ℚ)} {a' n' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    IsSquare ((a' ^ 2 - 4 * n' : ℤ) / (d : ℚ)) :=
  ⟨2 * x.im, by simpa [pow_two] using (double_im_sq_eq_ratio d hd0Q ha'trace hn'norm).symm⟩

private lemma dvd_trace_norm_delta
    (d : ℤ) (hd0 : d ≠ 0) (hd_sf : Squarefree d) (hd0Q : (d : ℚ) ≠ 0)
    {x : Qsqrtd (d : ℚ)} {a' n' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    d ∣ (a' ^ 2 - 4 * n') :=
  int_dvd_of_ratio_square (a' ^ 2 - 4 * n') d hd0 hd_sf
    (isSquare_trace_norm_ratio d hd0Q ha'trace hn'norm)

private lemma double_im_sq_eq_int
    (d : ℤ) (hd0Q : (d : ℚ) ≠ 0) {x : Qsqrtd (d : ℚ)} {a' n' k : ℤ}
    (hk : a' ^ 2 - 4 * n' = d * k)
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    (2 * x.im) ^ 2 = (k : ℚ) := by
  have hmk : ((a' ^ 2 - 4 * n' : ℤ) : ℚ) = (d : ℚ) * k := by
    exact_mod_cast hk
  calc
    (2 * x.im) ^ 2 = (a' ^ 2 - 4 * n' : ℤ) / (d : ℚ) :=
      double_im_sq_eq_ratio d hd0Q ha'trace hn'norm
    _ = ((d : ℚ) * k) / (d : ℚ) := by simp [hmk]
    _ = (k : ℚ) := by field_simp [hd0Q]

private lemma exists_int_of_isIntegral_rat {q : ℚ} (hq : IsIntegral ℤ q) :
    ∃ b' : ℤ, (b' : ℚ) = q := by
  obtain ⟨b', hb'⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 hq
  exact ⟨b', by simpa using hb'⟩

private lemma im_eq_half_of_double_im_eq {d : ℤ} {x : Qsqrtd (d : ℚ)} {b' : ℤ}
    (hb' : (b' : ℚ) = 2 * x.im) :
    x.im = (b' : ℚ) / 2 := by
  nlinarith [hb']

lemma exists_int_double_im
    (d : ℤ) (hd_sf : Squarefree d) {x : Qsqrtd (d : ℚ)} {a' n' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    ∃ b' : ℤ, x.im = (b' : ℚ) / 2 := by
  have hd0 : d ≠ 0 := hd_sf.ne_zero
  have hd0Q : (d : ℚ) ≠ 0 := by
    exact_mod_cast hd0
  rcases dvd_trace_norm_delta d hd0 hd_sf hd0Q ha'trace hn'norm with ⟨k, hk⟩
  rcases exists_int_of_isIntegral_rat
      (isIntegral_of_sq_int (double_im_sq_eq_int d hd0Q hk ha'trace hn'norm)) with
    ⟨b', hb'⟩
  exact ⟨b', im_eq_half_of_double_im_eq hb'⟩

lemma dvd_four_sub_sq_of_norm_eq_int
    (a' b' d n' : ℤ)
    (hnorm :
      (n' : ℚ) = (((a' ^ 2 - d * b' ^ 2 : ℤ) : ℚ) / (4 : ℤ))) :
    (4 : ℤ) ∣ (a' ^ 2 - d * b' ^ 2) :=
  (Rat.den_div_intCast_eq_one_iff (a' ^ 2 - d * b' ^ 2) 4 (by norm_num)).1 <| by
    rw [← hnorm]
    simp

end TraceNorm
end RingOfIntegers
end QuadraticNumberFields
end

section
namespace QuadraticNumberFields
namespace RingOfIntegers

open scoped NumberField

section RingOfIntegersEquiv

noncomputable def ringOfIntegers_equiv_of_integralClosure
    (K : Type*) [Field K] (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K] :
    𝓞 K ≃+* R :=
  NumberField.RingOfIntegers.equiv (K := K) (R := R)

@[simp]
lemma ringOfIntegers_equiv_of_integralClosure_apply
    {K : Type*} [Field K] {R : Type*} [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K]
    (α : 𝓞 K) :
    algebraMap R K (ringOfIntegers_equiv_of_integralClosure K R α) = (algebraMap (𝓞 K) K) α := by
  change algebraMap R K ((IsIntegralClosure.equiv ℤ R K (𝓞 K)).symm α) =
    algebraMap (𝓞 K) K α
  have key := IsIntegralClosure.algebraMap_equiv ℤ R K (𝓞 K)
    ((IsIntegralClosure.equiv ℤ R K (𝓞 K)).symm α)
  rw [(IsIntegralClosure.equiv ℤ R K (𝓞 K)).apply_symm_apply α] at key
  exact key.symm

noncomputable def ringOfIntegers_equiv_of_embedding
    (K : Type*) [Field K]
    (R : Type*) [CommRing R]
    (φ : R →+* K)
    (h_inj : Function.Injective φ)
    (h_exists : ∀ x : K, IsIntegral ℤ x → ∃ z : R, φ z = x)
    (h_integral : ∀ z : R, IsIntegral ℤ (φ z)) :
    𝓞 K ≃+* R :=
  letI : Algebra R K := φ.toAlgebra
  letI : IsIntegralClosure R ℤ K :=
    { algebraMap_injective := by
        exact h_inj
      isIntegral_iff := by
        intro x
        refine ⟨fun hx => ?_, ?_⟩
        · rcases h_exists x hx with ⟨z, hz⟩
          exact ⟨z, hz⟩
        · rintro ⟨z, rfl⟩
          exact h_integral z }
  ringOfIntegers_equiv_of_integralClosure K R

lemma ringOfIntegers_equiv_of_embedding_apply
    {K : Type*} [Field K]
    {R : Type*} [CommRing R]
    (φ : R →+* K)
    (h_inj : Function.Injective φ)
    (h_exists : ∀ x : K, IsIntegral ℤ x → ∃ z : R, φ z = x)
    (h_integral : ∀ z : R, IsIntegral ℤ (φ z))
    (α : 𝓞 K) :
    φ (ringOfIntegers_equiv_of_embedding K R φ h_inj h_exists h_integral α) = (α : K) := by
  letI : Algebra R K := φ.toAlgebra
  letI : IsIntegralClosure R ℤ K :=
    { algebraMap_injective := h_inj
      isIntegral_iff := by
        intro x
        refine ⟨fun hx => ?_, ?_⟩
        · rcases h_exists x hx with ⟨z, hz⟩
          exact ⟨z, hz⟩
        · rintro ⟨z, rfl⟩
          exact h_integral z }
  change algebraMap R K _ = algebraMap (𝓞 K) K α
  exact ringOfIntegers_equiv_of_integralClosure_apply (R := R) α

end RingOfIntegersEquiv

theorem dvd_four_sub_sq_iff_exists_zsqrtd_image_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔
      ∃ z : Zsqrtd d, Zsqrtd.toQsqrtdHom d z = Zsqrtd.halfInt (d := d) a' b' := by
  rw [dvd_four_sub_sq_iff_even_even_of_ne_one_mod_four d a' b' hd hd4,
    (Zsqrtd.halfInt_mem_range_toQsqrtdHom_iff_even_even d a' b').symm]

theorem exists_zsqrtd_image_of_dvd_four_sub_sq_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1)
    (hdiv : 4 ∣ (a' ^ 2 - d * b' ^ 2)) :
    ∃ z : Zsqrtd d, Zsqrtd.toQsqrtdHom d z = Zsqrtd.halfInt (d := d) a' b' :=
  (dvd_four_sub_sq_iff_exists_zsqrtd_image_of_ne_one_mod_four d a' b' hd hd4).1 hdiv
private lemma isIntegral_of_intModel_image
    (R S : Type*) [CommRing R] [CommRing S]
    [Algebra.IsIntegral ℤ R] (φ : R →+* S) (z : R) :
    IsIntegral ℤ (φ z) :=
  map_isIntegral_int φ (Algebra.IsIntegral.isIntegral (R := ℤ) z)

lemma isIntegral_toQsqrtd (d : ℤ) (z : Zsqrtd d) :
    IsIntegral ℤ (Zsqrtd.toQsqrtdHom d z) :=
  isIntegral_of_intModel_image (Zsqrtd d) (Qsqrtd (d : ℚ)) (Zsqrtd.toQsqrtdHom d) z

private lemma eq_halfInt_of_re_im
    (d a' b' : ℤ) {x : Qsqrtd (d : ℚ)}
    (hre : x.re = (a' : ℚ) / 2) (him : x.im = (b' : ℚ) / 2) :
    x = Zsqrtd.halfInt (d := d) a' b' := by
  ext <;> simp [Zsqrtd.halfInt, hre, him]

private lemma int_norm_eq_norm_halfInt
    (d a' b' n' : ℤ) {x : Qsqrtd (d : ℚ)}
    (hxHalf : x = Zsqrtd.halfInt (d := d) a' b')
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    (n' : ℚ) = (((a' ^ 2 - d * b' ^ 2 : ℤ) : ℚ) / (4 : ℤ)) := by
  calc
    (n' : ℚ) = Qsqrtd.norm x := hn'norm
    _ = Qsqrtd.norm (Zsqrtd.halfInt (d := d) a' b') := by simp [hxHalf]
    _ = (a' ^ 2 - (d : ℚ) * b' ^ 2) / 4 := norm_halfInt d a' b'
    _ = (((a' ^ 2 - d * b' ^ 2 : ℤ) : ℚ) / (4 : ℤ)) := by norm_num

private lemma dvd_four_sub_sq_of_int_norm_halfInt
    (d a' b' n' : ℤ) {x : Qsqrtd (d : ℚ)}
    (hxHalf : x = Zsqrtd.halfInt (d := d) a' b')
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    (4 : ℤ) ∣ (a' ^ 2 - d * b' ^ 2) :=
  TraceNorm.dvd_four_sub_sq_of_norm_eq_int a' b' d n'
    (int_norm_eq_norm_halfInt d a' b' n' hxHalf hn'norm)

lemma exists_halfInt_with_div_four_of_isIntegral
    (d : ℤ) (hd_sf : Squarefree d) (_hd_ne : d ≠ 1)
    {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    ∃ a' b' : ℤ,
      x = Zsqrtd.halfInt (d := d) a' b' ∧
      (4 : ℤ) ∣ (a' ^ 2 - d * b' ^ 2) := by
  obtain ⟨a', ha'trace⟩ := TraceNorm.exists_int_trace hx
  obtain ⟨n', hn'norm⟩ := TraceNorm.exists_int_norm hx
  obtain ⟨b', him⟩ := TraceNorm.exists_int_double_im d hd_sf ha'trace hn'norm
  have hxHalf : x = Zsqrtd.halfInt (d := d) a' b' :=
    eq_halfInt_of_re_im d a' b'
      (TraceNorm.re_eq_half_trace_int ha'trace) him
  exact ⟨a', b', hxHalf, dvd_four_sub_sq_of_int_norm_halfInt d a' b' n' hxHalf hn'norm⟩

private lemma exists_intModel_of_isIntegral
    (d : ℤ) (hd_sf : Squarefree d) (hd_ne : d ≠ 1)
    (R : Type*) [CommRing R]
    (φ : R →+* Qsqrtd (d : ℚ))
    (h_lift :
      ∀ a' b' : ℤ, 4 ∣ (a' ^ 2 - d * b' ^ 2) →
        ∃ z : R, φ z = Zsqrtd.halfInt (d := d) a' b')
    {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    ∃ z : R, φ z = x := by
  rcases exists_halfInt_with_div_four_of_isIntegral d hd_sf hd_ne (x := x) hx with
    ⟨a', b', hxHalf, hdiv⟩
  rcases h_lift a' b' hdiv with ⟨z, hz⟩
  exact ⟨z, by simpa [hxHalf] using hz⟩

lemma exists_zsqrtd_of_isIntegral_of_ne_one_mod_four
    (d : ℤ) (hd_sf : Squarefree d) (hd_ne : d ≠ 1) (hd4 : d % 4 ≠ 1)
    {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    ∃ z : Zsqrtd d, Zsqrtd.toQsqrtdHom d z = x :=
  exists_intModel_of_isIntegral d hd_sf hd_ne (Zsqrtd d) (Zsqrtd.toQsqrtdHom d)
    (fun a' b' hdiv =>
      exists_zsqrtd_image_of_dvd_four_sub_sq_of_ne_one_mod_four d a' b' hd_sf hd4 hdiv)
    hx
end RingOfIntegers
end QuadraticNumberFields
end

section
open scoped NumberField

namespace QuadraticNumberFields
namespace RingOfIntegers

section SquarefreeIntegerParameter

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

noncomputable def ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one (hd4 : d % 4 ≠ 1) :
    𝓞 (Qsqrtd (d : ℚ)) ≃+* Zsqrtd d :=
  let hd_sf : Squarefree d := Fact.out
  let hd_ne : d ≠ 1 := Fact.out
  ringOfIntegers_equiv_of_embedding (Qsqrtd (d : ℚ)) (Zsqrtd d)
    (Zsqrtd.toQsqrtdHom d)
    (Zsqrtd.toQsqrtdHom_injective d)
    (fun _ hx => exists_zsqrtd_of_isIntegral_of_ne_one_mod_four d hd_sf hd_ne hd4 hx)
    (fun z => isIntegral_toQsqrtd d z)

end SquarefreeIntegerParameter

end RingOfIntegers
end QuadraticNumberFields
end

section
open scoped NumberField
namespace QuadraticNumberFields.RingOfIntegers

open Module

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]

def ringEquivToIntAlgEquiv {R S : Type*} [CommRing R] [Algebra ℤ R]
    [CommRing S] [Algebra ℤ S] (e : R ≃+* S) : R ≃ₐ[ℤ] S :=
  AlgEquiv.ofRingEquiv (f := e) fun n => by
    simp only [eq_intCast, map_intCast]

end QuadraticNumberFields.RingOfIntegers
end

section
open scoped NumberField

namespace QuadraticNumberFields
namespace RingOfIntegers

theorem discr_zsqrtd_basis (d : ℤ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis d 0 :
      Module.Basis (Fin 2) ℤ (Zsqrtd d)) = 4 * d := by
  rw [QuadraticAlgebra.discr_basis_int]
  ring
section SquarefreeIntegerParameter

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

theorem discr_of_mod_four_ne_one (hd4 : d % 4 ≠ 1) :
    NumberField.discr (Qsqrtd (d : ℚ)) = 4 * d := by
  let e := ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
  let f : Zsqrtd d ≃ₐ[ℤ] 𝓞 (Qsqrtd (d : ℚ)) :=
    ringEquivToIntAlgEquiv e.symm
  let b' : Module.Basis (Fin 2) ℤ (𝓞 (Qsqrtd (d : ℚ))) :=
    (QuadraticAlgebra.basis d 0).map f.toLinearEquiv
  rw [← NumberField.discr_eq_discr (Qsqrtd (d : ℚ)) b']
  change Algebra.discr ℤ (⇑f ∘ ⇑(QuadraticAlgebra.basis d 0)) = 4 * d
  rw [← Algebra.discr_eq_discr_of_algEquiv _ f]
  exact discr_zsqrtd_basis d

end SquarefreeIntegerParameter

end RingOfIntegers
end QuadraticNumberFields
end

section

namespace Qsqrtd
section InternalLemmas

variable {d : ℤ} [Fact (¬ IsSquare ((d : ℤ) : ℚ))]

instance : Algebra.IsQuadraticExtension ℚ (Qsqrtd (d : ℚ)) where
  finrank_eq_two' := QuadraticAlgebra.finrank_eq_two (d : ℚ) 0

theorem embedding_omega_sq
    (v : NumberField.InfinitePlace (Qsqrtd (d : ℚ))) :
    v.embedding QuadraticAlgebra.omega ^ 2 = ((d : ℚ) : ℂ) := by
  rw [sq, ← map_mul, QuadraticAlgebra.omega_mul_omega_eq_add]
  simp [Algebra.smul_def]

private theorem embedding_omega_sq_re
    (v : NumberField.InfinitePlace (Qsqrtd (d : ℚ))) :
    (v.embedding QuadraticAlgebra.omega).re ^ 2 -
    (v.embedding QuadraticAlgebra.omega).im ^ 2 = (d : ℝ) := by
  have := congr_arg Complex.re (embedding_omega_sq v)
  simp [sq, Complex.mul_re] at this; linarith

private theorem embedding_omega_sq_im
    (v : NumberField.InfinitePlace (Qsqrtd (d : ℚ))) :
    2 * (v.embedding QuadraticAlgebra.omega).re *
    (v.embedding QuadraticAlgebra.omega).im = 0 := by
  have := congr_arg Complex.im (embedding_omega_sq v)
  simp [sq, Complex.mul_im] at this; linarith

private theorem embedding_omega_im_eq_zero
    (v : NumberField.InfinitePlace (Qsqrtd (d : ℚ)))
    (hd : 0 < d) :
    (v.embedding QuadraticAlgebra.omega).im = 0 := by
  have hre := embedding_omega_sq_re v
  have him := embedding_omega_sq_im v
  rcases mul_eq_zero.mp him with h | h
  · rcases mul_eq_zero.mp h with h | h
    · norm_num at h
    · rw [h] at hre; simp at hre
      nlinarith [sq_nonneg (v.embedding QuadraticAlgebra.omega).im,
                 (show (d : ℝ) > 0 from by exact_mod_cast hd)]
  · exact h

private theorem conjugate_embedding_eq
    (v : NumberField.InfinitePlace (Qsqrtd (d : ℚ)))
    (hω_im : (v.embedding QuadraticAlgebra.omega).im = 0) :
    NumberField.ComplexEmbedding.conjugate v.embedding = v.embedding := by
  rw [← @RingHom.toRatAlgHom_toRingHom (Qsqrtd (d : ℚ)) ℂ _ _ _ _
    (NumberField.ComplexEmbedding.conjugate v.embedding),
    ← @RingHom.toRatAlgHom_toRingHom (Qsqrtd (d : ℚ)) ℂ _ _ _ _
    v.embedding]
  congr 1
  apply QuadraticAlgebra.algHom_ext
  change (NumberField.ComplexEmbedding.conjugate v.embedding).toRatAlgHom
    QuadraticAlgebra.omega = v.embedding.toRatAlgHom QuadraticAlgebra.omega
  simp only [RingHom.toRatAlgHom_apply, NumberField.ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.mpr hω_im

end InternalLemmas

section InfinitePlaceClassification

variable (d : ℤ) [Fact (¬ IsSquare ((d : ℤ) : ℚ))]

theorem isTotallyReal (hd : 0 < d) :
    NumberField.IsTotallyReal (Qsqrtd (d : ℚ)) := {
    isReal := fun v => by
      rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
      simpa using conjugate_embedding_eq v (embedding_omega_im_eq_zero v hd)
  }

theorem nrComplexPlaces_eq_zero_of_pos (hd : 0 < d) :
    NumberField.InfinitePlace.nrComplexPlaces (Qsqrtd (d : ℚ)) = 0 := by
  haveI := isTotallyReal d hd
  exact NumberField.IsTotallyReal.nrComplexPlaces_eq_zero (Qsqrtd (d : ℚ))

end InfinitePlaceClassification

end Qsqrtd
end

end
open NumberField Ideal
namespace SmallPrimes1140
noncomputable section
lemma of_le_same {K : Type} [Field K] [NumberField K] {I J:Ideal (𝓞 K)}
    (ij:I≤J) (h:I.absNorm=J.absNorm) (nz:J.absNorm≠0) : I=J := by
  obtain ⟨D,e⟩ := Ideal.dvd_iff_le.mpr ij
  have eq : J.absNorm * D.absNorm=J.absNorm*1 := by simpa only [e,map_mul,mul_one] using h
  have one : D.absNorm=1 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero nz) eq
  simpa [Ideal.absNorm_eq_one_iff.mp one] using e

def bridge (d:ℤ) : QuadraticAlgebra ℤ d 0 ≃+* _root_.Zsqrtd d where
  toFun z := ⟨z.re,z.im⟩
  invFun z := ⟨z.re,z.im⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' x y := by
    apply _root_.Zsqrtd.ext
    · change x.re*y.re+d*x.im*y.im=_
      rfl
    · change x.re*y.im+x.im*y.re+0*x.im*y.im=_
      simp only [_root_.Zsqrtd.im_mul]; ring

set_option maxHeartbeats 1200000 in
lemma small_principal (n:ℕ) (hn:n.Prime) (res:n%4=3) (y:ℕ) (shape:2*n+2=(4*y)^2)
    (nonsq:∀ p:ℕ, p.Prime → p≠2 → p^2≤2*n → ∀ a:ZMod p,2*a^2≠(n:ZMod p)) :
    IsPrincipalIdealRing (_root_.Zsqrtd (2*(n:ℤ))) := by
  classical
  let d:ℤ := 2*n
  have he : n≠2 := by omega
  have sf : Squarefree (2*n) := (Nat.squarefree_mul (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))).mpr ⟨Nat.prime_two.squarefree,hn.squarefree⟩
  letI : Fact (Squarefree d) := ⟨by dsimp [d]; exact_mod_cast (Int.squarefree_natCast.mpr sf)⟩
  letI : Fact (d≠1) := ⟨by dsimp [d]; omega⟩
  have dpos : 0<d := by dsimp [d]; omega
  have modfour : d%4≠1 := by dsimp [d]; omega
  let K := Qsqrtd (d:ℚ)
  let e := QuadraticNumberFields.RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d modfour
  let j : QuadraticAlgebra ℤ d 0 ≃ₐ[ℤ] 𝓞 K := QuadraticNumberFields.RingOfIntegers.ringEquivToIntAlgEquiv e.symm
  let w : QuadraticAlgebra ℤ d 0 := ⟨0,1⟩
  have ws : w^2=(d:QuadraticAlgebra ℤ d 0) := by
    ext <;> simp [w,pow_two]
  let t:𝓞 K := j w
  have ts : t^2=(d:𝓞 K) := by simpa only [map_pow,map_intCast] using congrArg j ws
  have rk := Qsqrtd.finrank_ratAlgebra_eq_two (d:ℚ)
  letI : IsPrincipalIdealRing (𝓞 K) := by
    apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime
    intro I hI bound
    let P:Ideal (𝓞 K) := I.val
    have nz : P≠⊥ := nonZeroDivisors.coe_ne_zero I
    letI : P.IsMaximal := hI.isMaximal nz
    change (P.absNorm:ℝ) ≤ _ at bound
    rw [show NumberField.InfinitePlace.nrComplexPlaces K=0 from Qsqrtd.nrComplexPlaces_eq_zero_of_pos d dpos,rk,
      show NumberField.discr K=4*d from QuadraticNumberFields.RingOfIntegers.discr_of_mod_four_ne_one d modfour] at bound
    have dd : (0:ℝ)≤d := by exact_mod_cast dpos.le
    norm_num [abs_of_nonneg dd,Real.sqrt_mul (by norm_num : (0:ℝ)≤4)] at bound
    have small : P.absNorm^2≤2*n := by
      have := Real.sq_sqrt dd
      have h : (P.absNorm:ℝ)^2≤d := by nlinarith [Nat.cast_nonneg (α:=ℝ) P.absNorm,Real.sqrt_nonneg (d:ℝ)]
      dsimp [d] at h
      exact_mod_cast h
    have pnz : P.absNorm≠0 := fun z => nz (Ideal.absNorm_eq_zero_iff.mp z)
    obtain ⟨p,i,ipos,pm,hp,hi⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
    have le : span {(p:𝓞 K)}≤P := (span_singleton_le_iff_mem _).2 pm
    have size : (span {(p:𝓞 K)}).absNorm=p^2 := by rw [absNorm_span_natCast,NumberField.RingOfIntegers.rank,rk]
    have dvd : P.absNorm ∣ p^2 := size ▸ Ideal.absNorm_dvd_absNorm_of_le le
    obtain ⟨k,hk,hk'⟩ := (Nat.dvd_prime_pow hp).mp dvd
    interval_cases k
    · exact (hI.ne_top (Ideal.absNorm_eq_one_iff.mp (by simpa using hk'))).elim
    · have norm : P.absNorm=p := by simpa using hk'
      have qq := (Ideal.absNorm_ne_zero_iff P).mp pnz
      letI := Fintype.ofFinite (𝓞 K ⧸ P)
      let u := ZMod.ringEquivOfPrime (𝓞 K ⧸ P) hp (by rw [←Nat.card_eq_fintype_card]; exact norm)
      let f := u.symm.toRingHom.comp (Ideal.Quotient.mk P)
      have r : f t ^ 2=2*(n:ZMod p) := by
        rw [←map_pow,ts,map_intCast]; simp [d]
      by_cases two : p=2
      · rcases two with rfl
        have ft : f t=0 := by simpa only [show (2:ZMod 2)=0 from rfl,zero_mul,pow_eq_zero_iff (by decide : 2≠0)] using r
        let v:𝓞 K := (4*y:ℕ)+t
        have vm : v∈P := by
          apply Ideal.Quotient.eq_zero_iff_mem.mp
          apply u.symm.injective
          change f v=u.symm 0
          change f (((4*y:ℕ):𝓞 K)+t)=_
          rw [map_add,map_natCast,ft,map_zero,Nat.cast_mul,Nat.cast_ofNat,show (4:ZMod 2)=0 from rfl,zero_mul,add_zero]
        have nelem : Algebra.norm ℤ v=2 := by
          let x : QuadraticAlgebra ℤ d 0 := (4*y:ℕ)+w
          have jx : j x=v := by simp only [x,v,t,map_add,map_natCast]
          rw [←jx,Algebra.norm_eq_of_algEquiv j, Algebra.norm_eq_matrix_det (QuadraticAlgebra.basis d 0),QuadraticAlgebra.leftMulMatrix_eq,Matrix.det_fin_two]
          have hs : 2*(n:ℤ)+2=(4*(y:ℤ))^2 := by exact_mod_cast shape
          simp [x,w,d,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat] <;> nlinarith
        have en : (Ideal.span {v}).absNorm=P.absNorm := by rw [Ideal.absNorm_span_singleton,nelem,norm]; decide
        exact ⟨v,(of_le_same ((Ideal.span_singleton_le_iff_mem _).mpr vm) en pnz).symm⟩
      · letI : Fact p.Prime := ⟨hp⟩
        have ht : (2:ZMod p)≠0 := by
          change ((2:ℕ):ZMod p)≠0
          rw [Ne,ZMod.natCast_eq_zero_iff]
          exact (fun z : p∣2 => two ((Nat.dvd_prime Nat.prime_two).mp z |>.resolve_left hp.ne_one))
        apply False.elim (nonsq p hp two (norm ▸ small) ((f t)/2) ?_)
        field_simp
        linear_combination r
    · exact ⟨(p:𝓞 K),(of_le_same le (size.trans hk'.symm) pnz).symm⟩
  exact IsPrincipalIdealRing.of_surjective (e.trans (bridge d)) (by exact (e.trans (bridge d)).surjective)
end
end SmallPrimes1140

private theorem Erdos1140FiniteExceptions.principal : Erdos1140FiniteExceptions.H1 := by
  rintro n hn res ⟨y,hy⟩ sieve
  exact SmallPrimes1140.small_principal n hn res y hy sieve



/-! Proof of the class-number-one classification for squarefree m = (4*y)^2 - 2 > 398
with at most one exception, closing Erdos 1140. -/

open scoped BigOperators Real Nat
open Finset Filter Topology

namespace Erdos1140H2Proof

/- Section 1: Algebraic descent, units, and finite-range elimination -/

private lemma zsqrtd_norm_eq_prime_of_pid {m p : ℕ}
    (hpid : IsPrincipalIdealRing (Zsqrtd (m : ℤ)))
    (hp : p.Prime) {a : ℤ} (ha : (p : ℤ) ∣ a ^ 2 - (m : ℤ)) :
    ∃ x k : ℤ, |x ^ 2 - (m : ℤ) * k ^ 2| = (p : ℤ) := by
  let _ : Fact p.Prime := ⟨hp⟩
  let I : Ideal (Zsqrtd (m : ℤ)) := Ideal.span {(p : Zsqrtd (m : ℤ)), ⟨a, -1⟩}
  have hgen := IsPrincipalIdealRing.principal I
  obtain ⟨α, hα⟩ := hgen.principal
  have hp_mem : (p : Zsqrtd (m : ℤ)) ∈ I := Ideal.subset_span (by simp)
  have ha_mem : (⟨a, -1⟩ : Zsqrtd (m : ℤ)) ∈ I := Ideal.subset_span (by simp)
  rw [hα, Ideal.mem_span_singleton] at hp_mem ha_mem
  obtain ⟨β, hβ⟩ := hp_mem
  obtain ⟨γ, hγ⟩ := ha_mem
  have hnorm_p : α.norm * β.norm = (p : ℤ) ^ 2 := by
    have h := congrArg Zsqrtd.norm hβ
    simp only [Zsqrtd.norm_mul, Zsqrtd.norm_natCast] at h
    rw [← sq] at h
    exact h.symm
  have hdvd : α.norm.natAbs ∣ p ^ 2 := by
    refine ⟨β.norm.natAbs, ?_⟩
    have := congrArg Int.natAbs hnorm_p
    simpa [Int.natAbs_mul, Int.natAbs_pow] using this.symm
  obtain ⟨e, he_le, he_eq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have he_ne0 : e ≠ 0 := by
    intro he0
    rw [he0, pow_zero] at he_eq
    have hunit : IsUnit α := by
      rw [Zsqrtd.isUnit_iff_norm_isUnit]
      exact Int.isUnit_iff_natAbs_eq.mpr he_eq
    have h1 : (1 : Zsqrtd (m : ℤ)) ∈ I := by
      rw [hα, Ideal.mem_span_singleton]
      exact hunit.dvd
    rw [Ideal.mem_span_pair] at h1
    obtain ⟨u, v, huv⟩ := h1
    have hmod : ((u * (p : Zsqrtd (m : ℤ)) + v * ⟨a, -1⟩).re : ZMod p) +
        (a : ZMod p) * ((u * (p : Zsqrtd (m : ℤ)) + v * ⟨a, -1⟩).im : ZMod p) = (1 : ZMod p) := by
      have h1re := congrArg (fun z : Zsqrtd (m : ℤ) => (z.re : ZMod p)) huv
      have h1im := congrArg (fun z : Zsqrtd (m : ℤ) => (z.im : ZMod p)) huv
      simp at h1re h1im
      simp [h1re, h1im]
    have hsq : (a : ZMod p) ^ 2 = (m : ZMod p) := by
      have h0 : ((a ^ 2 - (m : ℤ) : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ha
      push_cast at h0
      exact sub_eq_zero.mp h0
    have hzero : ((u * (p : Zsqrtd (m : ℤ)) + v * ⟨a, -1⟩).re : ZMod p) +
        (a : ZMod p) * ((u * (p : Zsqrtd (m : ℤ)) + v * ⟨a, -1⟩).im : ZMod p) = 0 := by
      have hre : (u * (p : Zsqrtd (m : ℤ)) + v * ⟨a, -1⟩).re =
          u.re * (p : ℤ) + (v.re * a - (m : ℤ) * v.im) := by
        simp; ring
      have him : (u * (p : Zsqrtd (m : ℤ)) + v * ⟨a, -1⟩).im =
          u.im * (p : ℤ) + (v.im * a - v.re) := by
        simp; ring
      rw [hre, him]
      push_cast
      have hp0 : (p : ZMod p) = 0 := ZMod.natCast_self p
      rw [hp0]
      linear_combination -(v.im : ZMod p) * hsq.symm
    rw [hzero] at hmod
    exact zero_ne_one hmod
  have he_ne2 : e ≠ 2 := by
    intro he2
    rw [he2] at he_eq
    have hβ_abs : β.norm.natAbs = 1 := by
      have hmul := congrArg Int.natAbs hnorm_p
      rw [Int.natAbs_mul, he_eq] at hmul
      have hp2_pos : 0 < p ^ 2 := pow_pos hp.pos 2
      have hsq_abs : ((p : ℤ) ^ 2).natAbs = p ^ 2 := by simp
      rw [hsq_abs] at hmul
      nlinarith
    have hβ_unit : IsUnit β := by
      rw [Zsqrtd.isUnit_iff_norm_isUnit]
      exact Int.isUnit_iff_natAbs_eq.mpr hβ_abs
    obtain ⟨u, hu⟩ := hβ_unit
    have hα_eq : α = (p : Zsqrtd (m : ℤ)) * ((u⁻¹ : (Zsqrtd (m : ℤ))ˣ) : Zsqrtd (m : ℤ)) := by
      rw [hβ, ← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [hα_eq, mul_assoc] at hγ
    have him := congrArg Zsqrtd.im hγ
    have him' : ((p : Zsqrtd (m : ℤ)) * (((u⁻¹ : (Zsqrtd (m : ℤ))ˣ) : Zsqrtd (m : ℤ)) * γ)).im =
        (p : ℤ) * (((u⁻¹ : (Zsqrtd (m : ℤ))ˣ) : Zsqrtd (m : ℤ)) * γ).im := by
      simp
    rw [him'] at him
    have hdvd1 : (p : ℤ) ∣ (-1 : ℤ) := ⟨_, him⟩
    have hdvd1' : p ∣ 1 := by
      simpa using Int.natAbs_dvd_natAbs.mpr hdvd1
    exact hp.not_dvd_one hdvd1'
  have he1 : e = 1 := by omega
  rw [he1, pow_one] at he_eq
  refine ⟨α.re, α.im, ?_⟩
  have hnorm_def : α.norm = α.re ^ 2 - (m : ℤ) * α.im ^ 2 := by
    simp [Zsqrtd.norm_def]; ring
  rw [← hnorm_def]
  have habs : |α.norm| = (α.norm.natAbs : ℤ) := Int.natCast_natAbs α.norm |>.symm
  rw [habs, he_eq]

private lemma descent_lower_bound {q : ℤ} (hq : 4 ≤ q) {x k : ℤ} (hx : 0 ≤ x) (hk : 1 ≤ k)
    (hodd : (x ^ 2 - (q ^ 2 - 2) * k ^ 2) % 2 ≠ 0)
    (hmin : k ≤ |q * (q * k - x) - k|) :
    2 * q - 3 ≤ |x ^ 2 - (q ^ 2 - 2) * k ^ 2| := by
  set r : ℤ := q * k - x
  have hform : x ^ 2 - (q ^ 2 - 2) * k ^ 2 = 2 * k ^ 2 - 2 * q * k * r + r ^ 2 := by
    dsimp [r]; ring
  have hcases : q * r ≤ 0 ∨ 2 * k ≤ q * r := by
    rcases le_or_gt 0 (q * r - k) with h | h
    · rw [abs_of_nonneg h] at hmin; right; omega
    · rw [abs_of_neg h] at hmin; left; omega
  rcases hcases with hle | hge
  · have hr0 : r ≤ 0 := by nlinarith
    have hr_ne0 : r ≠ 0 := by
      intro hr
      rw [hform, hr] at hodd
      omega
    have hr_le : r ≤ -1 := by omega
    have hpos : 2 * q + 3 ≤ 2 * k ^ 2 - 2 * q * k * r + r ^ 2 := by
      nlinarith
    rw [hform, abs_of_nonneg (by linarith)]
    linarith
  · have hr_pos : 1 ≤ r := by nlinarith
    have hr_le_qk : r ≤ q * k := by dsimp [r]; linarith
    have hneg : 2 * q - 3 ≤ 2 * q * k * r - 2 * k ^ 2 - r ^ 2 := by
      rcases le_or_gt r q with hrq | hrq
      · have h1 : 0 ≤ (k - 1) * (q * r - 2 * k) := by nlinarith
        have h2 : 0 ≤ (q * r - 2) * (k - 1) := by nlinarith
        have h3 : 0 ≤ (r - 1) * (2 * q - 1 - r) := by nlinarith
        nlinarith
      · have h1 : 0 ≤ (q * k - r) * (q * r - 2 * k) := by nlinarith
        have h2 : q * (2 * q * k * r - 2 * k ^ 2 - r ^ 2) =
            (q * k - r) * (q * r - 2 * k) + (q ^ 2 - 2) * r * k := by ring
        have h3 : q * (2 * q - 3) ≤ (q ^ 2 - 2) * r * k := by nlinarith
        nlinarith
    rw [hform]
    have hle0 : 2 * k ^ 2 - 2 * q * k * r + r ^ 2 ≤ 0 := by linarith
    rw [abs_of_nonpos hle0]
    linarith

private lemma odd_prime_ge_of_pid {m y p : ℕ} (hy : 1 ≤ y) (hm : m + 2 = (4 * y) ^ 2)
    (hpid : IsPrincipalIdealRing (Zsqrtd (m : ℤ)))
    (hp : p.Prime) (hp2 : p ≠ 2) {a : ℤ} (ha : (p : ℤ) ∣ a ^ 2 - (m : ℤ)) :
    8 * y - 3 ≤ p := by
  obtain ⟨x₀, k₀, h₀⟩ := zsqrtd_norm_eq_prime_of_pid hpid hp ha
  have hex : ∃ n : ℕ, ∃ x k : ℤ, k.natAbs = n ∧ |x ^ 2 - (m : ℤ) * k ^ 2| = (p : ℤ) :=
    ⟨k₀.natAbs, x₀, k₀, rfl, h₀⟩
  classical
  let n_min := Nat.find hex
  obtain ⟨x₁, k₁, hk₁_abs, hnorm₁⟩ := Nat.find_spec hex
  have hmin_all : ∀ x k : ℤ, |x ^ 2 - (m : ℤ) * k ^ 2| = (p : ℤ) → n_min ≤ k.natAbs :=
    fun x k h => Nat.find_min' hex ⟨x, k, rfl, h⟩
  set x : ℤ := |x₁|
  set k : ℤ := |k₁|
  have hx : 0 ≤ x := abs_nonneg x₁
  have hk0 : 0 ≤ k := abs_nonneg k₁
  have hnorm : |x ^ 2 - (m : ℤ) * k ^ 2| = (p : ℤ) := by
    simpa [x, k, sq_abs] using hnorm₁
  have hk_ne0 : k ≠ 0 := by
    intro hk_zero
    rw [hk_zero] at hnorm
    simp only [sq, mul_zero, sub_zero] at hnorm
    have hsq : x.natAbs ^ 2 = p := by
      have hxx : (x.natAbs : ℤ) * (x.natAbs : ℤ) = (p : ℤ) := by
        rw [Int.natAbs_of_nonneg hx]
        simpa [abs_of_nonneg (mul_self_nonneg x)] using hnorm
      have hxx' : ((x.natAbs ^ 2 : ℕ) : ℤ) = (p : ℤ) := by
        rw [Nat.cast_pow, sq]; exact hxx
      exact Int.ofNat.inj hxx'
    have hdiv : x.natAbs ∣ p := ⟨x.natAbs, by rw [← hsq, sq]⟩
    rcases hp.eq_one_or_self_of_dvd x.natAbs hdiv with h1 | hp_eq
    · rw [h1, one_pow] at hsq; exact hp.ne_one hsq.symm
    · rw [hp_eq] at hsq
      have : p ≥ 2 := hp.two_le
      nlinarith
  have hk1 : 1 ≤ k := by omega
  set q : ℤ := 4 * (y : ℤ)
  have hq4 : 4 ≤ q := by omega
  have hmq : (m : ℤ) = q ^ 2 - 2 := by
    have : (m : ℤ) + 2 = (4 * (y : ℤ)) ^ 2 := by exact_mod_cast hm
    dsimp [q]; linarith
  have hodd : (x ^ 2 - (q ^ 2 - 2) * k ^ 2) % 2 ≠ 0 := by
    have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
    rw [← hmq]
    intro heven
    have habs_mod : |x ^ 2 - (m : ℤ) * k ^ 2| % 2 = 0 := by
      rcases le_or_gt 0 (x ^ 2 - (m : ℤ) * k ^ 2) with h | h
      · rw [abs_of_nonneg h]; exact heven
      · rw [abs_of_neg h]; omega
    rw [hnorm] at habs_mod
    omega
  set x' : ℤ := (q ^ 2 - 1) * x - q * (m : ℤ) * k
  set k' : ℤ := (q ^ 2 - 1) * k - q * x
  have hk'_eq : k' = q * (q * k - x) - k := by dsimp [k']; ring
  have hnorm' : |x' ^ 2 - (m : ℤ) * k' ^ 2| = (p : ℤ) := by
    have hid : x' ^ 2 - (m : ℤ) * k' ^ 2 = x ^ 2 - (m : ℤ) * k ^ 2 := by
      dsimp [x', k']
      rw [hmq]
      ring
    rw [hid, hnorm]
  have hk_min : k ≤ |q * (q * k - x) - k| := by
    rw [← hk'_eq]
    have hle := hmin_all x' k' hnorm'
    have hk_eq_n : k.natAbs = n_min := by
      dsimp [k]; rw [Int.natAbs_abs]; exact hk₁_abs
    have : (k.natAbs : ℤ) ≤ (k'.natAbs : ℤ) := by exact_mod_cast (hk_eq_n ▸ hle)
    rw [Int.natAbs_of_nonneg hk0] at this
    simpa [Int.natCast_natAbs] using this
  have hbd := descent_lower_bound hq4 hx hk1 hodd hk_min
  rw [← hmq, hnorm] at hbd
  dsimp [q] at hbd
  omega

private def fundUnit (y : ℕ) (m : ℕ) : Zsqrtd (m : ℤ) :=
  ⟨16 * (y : ℤ) ^ 2 - 1, 4 * (y : ℤ)⟩

private def fundUnitInv (y : ℕ) (m : ℕ) : Zsqrtd (m : ℤ) :=
  ⟨16 * (y : ℤ) ^ 2 - 1, -(4 * (y : ℤ))⟩

private lemma fundUnit_mul_inv {m y : ℕ} (hm : m + 2 = (4 * y) ^ 2) :
    fundUnit y m * fundUnitInv y m = 1 := by
  have hmZ : (m : ℤ) = 16 * (y : ℤ) ^ 2 - 2 := by
    have : (m : ℤ) + 2 = (4 * (y : ℤ)) ^ 2 := by exact_mod_cast hm
    linarith
  ext <;> simp [fundUnit, fundUnitInv, hmZ] <;> ring

private def fundUnitU {m y : ℕ} (hm : m + 2 = (4 * y) ^ 2) : (Zsqrtd (m : ℤ))ˣ where
  val := fundUnit y m
  inv := fundUnitInv y m
  val_inv := fundUnit_mul_inv hm
  inv_val := by rw [mul_comm]; exact fundUnit_mul_inv hm

private lemma unit_eq_pm_fundUnit_zpow {m y : ℕ} (hy : 1 ≤ y) (hm : m + 2 = (4 * y) ^ 2)
    (u : (Zsqrtd (m : ℤ))ˣ) :
    ∃ (s : Bool) (n : ℤ), (u : Zsqrtd (m : ℤ)) =
      (if s then (1 : Zsqrtd (m : ℤ)) else -1) *
        ((fundUnitU hm ^ n : (Zsqrtd (m : ℤ))ˣ) : Zsqrtd (m : ℤ)) := by
  have hmain : ∀ N : ℕ, ∀ v : (Zsqrtd (m : ℤ))ˣ, (v : Zsqrtd (m : ℤ)).im.natAbs ≤ N →
      ∃ (s : Bool) (n : ℤ), (v : Zsqrtd (m : ℤ)) =
        (if s then (1 : Zsqrtd (m : ℤ)) else -1) *
          ((fundUnitU hm ^ n : (Zsqrtd (m : ℤ))ˣ) : Zsqrtd (m : ℤ)) := by
    intro N
    induction N with
    | zero =>
      intro v hv
      have him : (v : Zsqrtd (m : ℤ)).im = 0 := by omega
      have hnorm : |(v : Zsqrtd (m : ℤ)).norm| = 1 := by
        have hu : IsUnit (v : Zsqrtd (m : ℤ)).norm :=
          (Zsqrtd.isUnit_iff_norm_isUnit _).mp v.isUnit
        rcases Int.isUnit_iff.mp hu with h1 | h1 <;> simp [h1]
      have hre2 : (v : Zsqrtd (m : ℤ)).re ^ 2 = 1 := by
        have hd : (v : Zsqrtd (m : ℤ)).norm = (v : Zsqrtd (m : ℤ)).re ^ 2 := by
          simp [Zsqrtd.norm_def, him, sq]
        rw [hd, abs_of_nonneg (sq_nonneg _)] at hnorm
        exact hnorm
      rcases sq_eq_one_iff.mp hre2 with h1 | h1
      · refine ⟨true, 0, ?_⟩
        ext <;> simp [h1, him]
      · refine ⟨false, 0, ?_⟩
        ext <;> simp [h1, him]
    | succ N ih =>
      intro v hv
      by_cases hle : (v : Zsqrtd (m : ℤ)).im.natAbs ≤ N
      · exact ih v hle
      · have heq : (v : Zsqrtd (m : ℤ)).im.natAbs = N + 1 := by omega
        set a : ℤ := (v : Zsqrtd (m : ℤ)).re
        set b : ℤ := (v : Zsqrtd (m : ℤ)).im
        have hnorm : |a ^ 2 - (m : ℤ) * b ^ 2| = 1 := by
          have hu : IsUnit (v : Zsqrtd (m : ℤ)).norm :=
            (Zsqrtd.isUnit_iff_norm_isUnit _).mp v.isUnit
          have hd : (v : Zsqrtd (m : ℤ)).norm = a ^ 2 - (m : ℤ) * b ^ 2 := by
            simp [a, b, Zsqrtd.norm_def]; ring
          rw [← hd]
          rcases Int.isUnit_iff.mp hu with h1 | h1 <;> simp [h1]
        set q : ℤ := 4 * (y : ℤ)
        have hq4 : 4 ≤ q := by omega
        have hmq : (m : ℤ) = q ^ 2 - 2 := by
          have : (m : ℤ) + 2 = (4 * (y : ℤ)) ^ 2 := by exact_mod_cast hm
          dsimp [q]; linarith
        have hlt_abs : abs (q * (q * |b| - |a|) - |b|) < |b| := by
          by_contra hge
          push Not at hge
          have hnorm_abs : abs (|a| ^ 2 - (q ^ 2 - 2) * |b| ^ 2) = 1 := by
            simpa [sq_abs, ← hmq] using hnorm
          have hodd : (|a| ^ 2 - (q ^ 2 - 2) * |b| ^ 2) % 2 ≠ 0 := by
            rcases abs_eq (by norm_num : (0 : ℤ) ≤ 1) |>.mp hnorm_abs with h | h <;> omega
          have hb1 : 1 ≤ |b| := by
            have : (b.natAbs : ℤ) = |b| := Int.natCast_natAbs b
            omega
          have hbd := descent_lower_bound hq4 (abs_nonneg a) hb1 hodd hge
          rw [hnorm_abs] at hbd
          omega
        rcases le_or_gt 0 (a * b) with hab | hab
        · set w : (Zsqrtd (m : ℤ))ˣ := v * (fundUnitU hm)⁻¹
          have hw_im : (w : Zsqrtd (m : ℤ)).im = (q ^ 2 - 1) * b - q * a := by
            change (v : Zsqrtd (m : ℤ)).re * (-(4 * (y : ℤ))) +
              (v : Zsqrtd (m : ℤ)).im * (16 * (y : ℤ) ^ 2 - 1) = _
            dsimp [a, b, q]; ring
          have hw_abs : |(w : Zsqrtd (m : ℤ)).im| < |b| := by
            rw [hw_im]
            have hsame : abs ((q ^ 2 - 1) * b - q * a) = abs (q * (q * |b| - |a|) - |b|) := by
              rcases le_or_gt 0 b with hb | hb
              · have hb_pos : 0 < b := by
                  have : b ≠ 0 := by intro hb0; rw [hb0] at heq; simp at heq
                  omega
                have ha0 : 0 ≤ a := by nlinarith
                rw [abs_of_nonneg hb, abs_of_nonneg ha0]; ring_nf
              · have ha0 : a ≤ 0 := by nlinarith
                rw [abs_of_neg hb, abs_of_nonpos ha0]
                have : (q ^ 2 - 1) * b - q * a = -(q * (q * -b - -a) - -b) := by ring
                rw [this, abs_neg]
            rw [hsame]; exact hlt_abs
          have hw_le : (w : Zsqrtd (m : ℤ)).im.natAbs ≤ N := by
            have : ((w : Zsqrtd (m : ℤ)).im.natAbs : ℤ) < (b.natAbs : ℤ) := by
              simpa [Int.natCast_natAbs] using hw_abs
            omega
          obtain ⟨s, n, hsn⟩ := ih w hw_le
          refine ⟨s, n + 1, ?_⟩
          have hv_eq : (v : Zsqrtd (m : ℤ)) =
              (w : Zsqrtd (m : ℤ)) * (fundUnitU hm : Zsqrtd (m : ℤ)) := by
            have : v = w * fundUnitU hm := by dsimp [w]; group
            rw [this, Units.val_mul]
          rw [hv_eq, hsn, mul_assoc, zpow_add_one, Units.val_mul]
        · set w : (Zsqrtd (m : ℤ))ˣ := v * fundUnitU hm
          have hw_im : (w : Zsqrtd (m : ℤ)).im = (q ^ 2 - 1) * b + q * a := by
            change (v : Zsqrtd (m : ℤ)).re * (4 * (y : ℤ)) +
              (v : Zsqrtd (m : ℤ)).im * (16 * (y : ℤ) ^ 2 - 1) = _
            dsimp [a, b, q]; ring
          have hw_abs : |(w : Zsqrtd (m : ℤ)).im| < |b| := by
            rw [hw_im]
            have hopp : abs ((q ^ 2 - 1) * b + q * a) = abs (q * (q * |b| - |a|) - |b|) := by
              rcases le_or_gt 0 b with hb | hb
              · have ha0 : a ≤ 0 := by nlinarith
                rw [abs_of_nonneg hb, abs_of_nonpos ha0]; ring_nf
              · have ha0 : 0 ≤ a := by nlinarith
                rw [abs_of_neg hb, abs_of_nonneg ha0]
                have : (q ^ 2 - 1) * b + q * a = -(q * (q * -b - a) - -b) := by ring
                rw [this, abs_neg]
            rw [hopp]; exact hlt_abs
          have hw_le : (w : Zsqrtd (m : ℤ)).im.natAbs ≤ N := by
            have : ((w : Zsqrtd (m : ℤ)).im.natAbs : ℤ) < (b.natAbs : ℤ) := by
              simpa [Int.natCast_natAbs] using hw_abs
            omega
          obtain ⟨s, n, hsn⟩ := ih w hw_le
          refine ⟨s, n - 1, ?_⟩
          have hv_eq : (v : Zsqrtd (m : ℤ)) =
              (w : Zsqrtd (m : ℤ)) * (((fundUnitU hm)⁻¹ : (Zsqrtd (m : ℤ))ˣ) : Zsqrtd (m : ℤ)) := by
            have : v = w * (fundUnitU hm)⁻¹ := by dsimp [w]; group
            rw [this, Units.val_mul]
          rw [hv_eq, hsn, mul_assoc, zpow_sub_one, Units.val_mul]
  exact hmain (u : Zsqrtd (m : ℤ)).im.natAbs u le_rfl

private def smallOddPrimes : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]

private def hasSqrtMod (p r : ℕ) : Bool :=
  (List.range (p / 2 + 1)).any (fun a => (a * a) % p == r % p)

private def hasSmallSplitPrime (y : ℕ) : Bool :=
  let m := 16 * y * y - 2
  smallOddPrimes.any (fun p => decide (p < 8 * y - 3) && hasSqrtMod p m)

private def checkPow2 (lo : ℕ) : ℕ → Bool
  | 0 => hasSmallSplitPrime lo
  | d + 1 => checkPow2 lo d && checkPow2 (lo + 2 ^ d) d

private lemma checkPow2_spec : ∀ d lo y, checkPow2 lo d = true → lo ≤ y → y < lo + 2 ^ d →
    hasSmallSplitPrime y = true := by
  intro d
  induction d with
  | zero =>
    intro lo y hchk hlo hhi
    have : y = lo := by omega
    rwa [this]
  | succ d ih =>
    intro lo y hchk hlo hhi
    simp only [checkPow2, Bool.and_eq_true] at hchk
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
    by_cases hmid : y < lo + 2 ^ d
    · exact ih lo y hchk.1 hlo hmid
    · exact ih (lo + 2 ^ d) y hchk.2 (by omega) (by omega)

private lemma smallOddPrimes_prime : ∀ p ∈ smallOddPrimes, p.Prime ∧ p ≠ 2 := by
  decide

private lemma hasSqrtMod_spec {p r : ℕ} (h : hasSqrtMod p r = true) :
    ∃ a : ℤ, (p : ℤ) ∣ a ^ 2 - (r : ℤ) := by
  unfold hasSqrtMod at h
  rw [List.any_eq_true] at h
  obtain ⟨a, _, ha⟩ := h
  simp only [beq_iff_eq] at ha
  refine ⟨(a : ℤ), ?_⟩
  have hmod : ((a * a : ℕ) : ℤ) % (p : ℤ) = (r : ℤ) % (p : ℤ) := by exact_mod_cast ha
  have hd : (p : ℤ) ∣ ((a * a : ℕ) : ℤ) - (r : ℤ) := by
    rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, hmod, sub_self, Int.zero_emod]
  simpa [sq] using hd

private lemma checkPow2_6_12 : checkPow2 6 12 = true := by decide

private lemma y_ge_4102 {m y : ℕ} (hm398 : 398 < m) (hm : m + 2 = (4 * y) ^ 2)
    (hpid : IsPrincipalIdealRing (Zsqrtd (m : ℤ))) : 4102 ≤ y := by
  have hy6 : 6 ≤ y := by nlinarith
  by_contra hlt
  push Not at hlt
  have hcheck : hasSmallSplitPrime y = true :=
    checkPow2_spec 12 6 y checkPow2_6_12 hy6 (by omega)
  unfold hasSmallSplitPrime at hcheck
  rw [List.any_eq_true] at hcheck
  obtain ⟨p, hp_mem, hp_cond⟩ := hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp_cond
  obtain ⟨hp_lt, hp_qr⟩ := hp_cond
  obtain ⟨hp_prime, hp_ne2⟩ := smallOddPrimes_prime p hp_mem
  have hm_eq : 16 * y * y - 2 = m := by
    have h4 : (4 * y) ^ 2 = 16 * y * y := by ring
    omega
  rw [hm_eq] at hp_qr
  obtain ⟨a, ha⟩ := hasSqrtMod_spec hp_qr
  have hge := odd_prime_ge_of_pid (by omega) hm hpid hp_prime hp_ne2 ha
  omega

/- Section 2: Quadratic Dirichlet characters, primitivity, product character, and Polya-Vinogradov -/

private lemma exists_nonresidue_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ r : ℕ, 0 < r ∧ r < p ∧ jacobiSym (r : ℤ) p = -1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by
    intro h2
    have := ZMod.ringChar_zmod_n p
    rw [h2] at this
    exact hp2 this.symm)
  have ha0 : a ≠ 0 := by
    intro h0
    apply ha
    exact ⟨0, by simp [h0]⟩
  refine ⟨a.val, Nat.pos_of_ne_zero (fun h => ha0 (by simpa using (ZMod.val_eq_zero a).mp h)),
    ZMod.val_lt a, ?_⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  have hcast : ((a.val : ℕ) : ZMod p) = a := ZMod.natCast_zmod_val a
  rw [legendreSym.eq_neg_one_iff]
  simpa [Int.cast_natCast, hcast] using ha

private def quadChar (m : ℕ) (hm : 0 < m) : DirichletCharacter ℂ (4 * m) where
  toFun x := if x.val % 2 = 0 then 0 else (jacobiSym (m : ℤ) x.val : ℂ)
  map_one' := by
    have h1 : (1 : ZMod (4 * m)).val = 1 := ZMod.val_one'' (by omega)
    simp [h1]
  map_mul' a b := by
    let _ : NeZero (4 * m) := ⟨by omega⟩
    have hval : (a * b).val = (a.val * b.val) % (4 * m) := ZMod.val_mul a b
    have hmod2 : ((a.val * b.val) % (4 * m)) % 2 = (a.val * b.val) % 2 :=
      Nat.mod_mod_of_dvd _ (dvd_mul_of_dvd_left (by decide : 2 ∣ 4) m)
    by_cases ha : a.val % 2 = 0
    · have hab : (a * b).val % 2 = 0 := by
        rw [hval, hmod2, Nat.mul_mod, ha, zero_mul, Nat.zero_mod]
      simp [ha, hab]
    · by_cases hb : b.val % 2 = 0
      · have hab : (a * b).val % 2 = 0 := by
          rw [hval, hmod2, Nat.mul_mod, hb, mul_zero, Nat.zero_mod]
        simp [hb, hab]
      · have ha_odd : Odd a.val := Nat.odd_iff.mpr (by omega)
        have hb_odd : Odd b.val := Nat.odd_iff.mpr (by omega)
        have hab_odd : Odd (a.val * b.val) := ha_odd.mul hb_odd
        have hval_odd : (a * b).val % 2 ≠ 0 := by
          rw [hval, hmod2, Nat.odd_iff.mp hab_odd]
          decide
        simp only [ha, hb, hval_odd, ↓reduceIte]
        rw [hval, ← jacobiSym.mod_right' m hab_odd,
          jacobiSym.mul_right' (m : ℤ) (by omega) (by omega)]
        push_cast
        rfl
  map_nonunit' x hx := by
    let _ : NeZero (4 * m) := ⟨by omega⟩
    by_cases h2 : x.val % 2 = 0
    · simp [h2]
    · simp only [h2, ↓reduceIte]
      have hnotcop : Nat.gcd x.val (4 * m) ≠ 1 := by
        intro hcop
        have hu : IsUnit ((x.val : ℕ) : ZMod (4 * m)) :=
          (ZMod.isUnit_iff_coprime x.val (4 * m)).mpr hcop
        rw [ZMod.natCast_zmod_val] at hu
        exact hx hu
      have hcop4 : Nat.Coprime x.val 4 := by
        exact (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr (by omega))).pow_right 2
      have hnotcop_m : Nat.gcd x.val m ≠ 1 := by
        intro hcm
        exact hnotcop (hcop4.mul_right hcm).gcd_eq_one
      have hne0 : x.val ≠ 0 := by omega
      have hgc : (m : ℤ).gcd x.val ≠ 1 := by
        rw [Int.gcd_natCast_natCast, Nat.gcd_comm]
        exact hnotcop_m
      let _ : NeZero x.val := ⟨hne0⟩
      rw [jacobiSym.eq_zero_iff_not_coprime.mpr hgc]
      simp

private lemma quadChar_apply_nat {m : ℕ} (hm : 0 < m) (n : ℕ) :
    quadChar m hm (n : ZMod (4 * m)) =
      if n % 2 = 0 then 0 else (jacobiSym (m : ℤ) n : ℂ) := by
  let _ : NeZero (4 * m) := ⟨by omega⟩
  change (if (n : ZMod (4 * m)).val % 2 = 0 then 0 else (jacobiSym (m : ℤ) (n : ZMod (4 * m)).val : ℂ)) = _
  rw [ZMod.val_natCast]
  have hmod2 : (n % (4 * m)) % 2 = n % 2 :=
    Nat.mod_mod_of_dvd n (dvd_mul_of_dvd_left (by decide : 2 ∣ 4) m)
  rw [hmod2]
  by_cases h2 : n % 2 = 0
  · simp [h2]
  · simp only [h2, ↓reduceIte]
    rw [← jacobiSym.mod_right' m (Nat.odd_iff.mpr (by omega))]

private lemma quadChar_isReal {m : ℕ} (hm : 0 < m) (n : ℕ) :
    quadChar m hm n = ((quadChar m hm n).re : ℂ) ∧
      ((quadChar m hm n).re = 0 ∨ (quadChar m hm n).re = 1 ∨ (quadChar m hm n).re = -1) := by
  rw [quadChar_apply_nat]
  by_cases h2 : n % 2 = 0
  · simp [h2]
  · simp only [h2, ↓reduceIte]
    rcases jacobiSym.trichotomy (m : ℤ) n with h | h | h <;> simp [h]

private lemma quadChar_isPrimitive {m : ℕ} (hm : 0 < m) (hm4 : m % 4 = 2) (hsq : Squarefree m) :
    (quadChar m hm).IsPrimitive := by
  let _ : NeZero (4 * m) := ⟨by omega⟩
  rw [DirichletCharacter.isPrimitive_def]
  have hdvd := (quadChar m hm).conductor_dvd_level
  by_contra hne
  have hlt : (quadChar m hm).conductor < 4 * m :=
    lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdvd) hne
  obtain ⟨t, ht⟩ := hdvd
  have ht1 : 1 < t := by nlinarith
  let p := t.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpt : p ∣ t := Nat.minFac_dvd t
  have hp_dvd : p ∣ 4 * m := dvd_trans hpt ⟨(quadChar m hm).conductor, by linarith⟩
  have hdiv_dvd : 4 * m / p ∣ 4 * m := Nat.div_dvd_of_dvd hp_dvd
  have hcdvd : (quadChar m hm).conductor ∣ 4 * m / p := by
    obtain ⟨t', ht'⟩ := hpt
    refine ⟨t', ?_⟩
    have hmul : (4 * m / p) * p = 4 * m := Nat.div_mul_cancel hp_dvd
    have hp0 : 0 < p := hp.pos
    have : (4 * m / p) * p = ((quadChar m hm).conductor * t') * p := by
      calc (4 * m / p) * p = 4 * m := hmul
        _ = (quadChar m hm).conductor * t := ht
        _ = (quadChar m hm).conductor * (p * t') := by rw [ht']
        _ = ((quadChar m hm).conductor * t') * p := by ring
    exact Nat.eq_of_mul_eq_mul_right hp0 this
  have hfac : (quadChar m hm).FactorsThrough (4 * m / p) :=
    DirichletCharacter.FactorsThrough.mono (χ := quadChar m hm)
      (quadChar m hm).factorsThrough_conductor hcdvd hdiv_dvd
  have hdiv_pos : 0 < 4 * m / p := Nat.div_pos (Nat.le_of_dvd (by omega) hp_dvd) hp.pos
  let _ : NeZero (4 * m / p) := ⟨by omega⟩
  have hker := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hdiv_dvd).mp hfac
  by_cases hp2 : p = 2
  · let k := m / 2
    have hm2k : m = 2 * k := by omega
    have hk_odd : k % 2 = 1 := by omega
    have hcop : Nat.Coprime 8 k :=
      (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hk_odd)).pow_left 3
    let e := ZMod.chineseRemainder hcop
    let _ : NeZero (8 * k) := ⟨by omega⟩
    let xZ : ZMod (8 * k) := e.symm (5, 1)
    let x : ℕ := xZ.val
    have hx8Z : (x : ZMod 8) = 5 := by
      have h1 : (e xZ).1 = 5 := by simp [xZ]
      have h2 : (xZ.cast : ZMod 8) = 5 := by simpa [e, ZMod.chineseRemainder] using h1
      rw [← ZMod.natCast_zmod_val xZ, ZMod.cast_natCast (dvd_mul_right 8 k)] at h2
      exact h2
    have hx8 : x % 8 = 5 := by
      have := congrArg ZMod.val hx8Z
      rw [ZMod.val_natCast] at this
      exact this.trans (by decide : (5 : ZMod 8).val = 5)
    have hxk : (x : ZMod k) = 1 := by
      have h1 : (e xZ).2 = 1 := by simp [xZ]
      have h2 : (xZ.cast : ZMod k) = 1 := by simpa [e, ZMod.chineseRemainder] using h1
      rw [← ZMod.natCast_zmod_val xZ, ZMod.cast_natCast (dvd_mul_left k 8)] at h2
      exact h2
    have hx_cop : Nat.Coprime x (4 * m) := by
      have h4m : 4 * m = 8 * k := by omega
      rw [h4m]
      refine Nat.Coprime.mul_right ?_ ?_
      · rw [Nat.coprime_iff_gcd_eq_one]
        have : Nat.gcd x 8 = Nat.gcd (x % 8) 8 := by rw [Nat.gcd_comm, Nat.gcd_rec, Nat.gcd_comm]
        rw [this, hx8]; decide
      · rw [← ZMod.isUnit_iff_coprime, hxk]; exact isUnit_one
    have hx_unit : IsUnit (x : ZMod (4 * m)) := (ZMod.isUnit_iff_coprime x (4 * m)).mpr hx_cop
    have hx_mod : (x : ZMod (4 * m / p)) = 1 := by
      have hdiv : 4 * m / p = 4 * k := by rw [hp2]; omega
      have h1 : 4 ∣ x - 1 := by omega
      have h2 : k ∣ x - 1 := by
        have hxk' := (ZMod.natCast_eq_natCast_iff x 1 k).mp (by simpa using hxk)
        exact (Nat.modEq_iff_dvd' (by omega : 1 ≤ x)).mp hxk'.symm
      have hcop4k : Nat.Coprime 4 k :=
        (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hk_odd)).pow_left 2
      have h4k : 4 * k ∣ x - 1 := hcop4k.mul_dvd_of_dvd_of_dvd h1 h2
      have hmeq : x ≡ 1 [MOD (4 * m / p)] := by
        rw [hdiv]
        exact (Nat.modEq_iff_dvd' (by omega : 1 ≤ x)).mpr h4k |>.symm
      simpa using (ZMod.natCast_eq_natCast_iff x 1 (4 * m / p)).mpr hmeq
    have hmem : hx_unit.unit ∈ (ZMod.unitsMap hdiv_dvd).ker := by
      rw [MonoidHom.mem_ker]
      ext
      simpa [ZMod.unitsMap_def, hx_unit.unit_spec] using hx_mod
    have h1 := hker hmem
    rw [MonoidHom.mem_ker] at h1
    have hval1 : quadChar m hm (x : ZMod (4 * m)) = 1 := by
      have := congrArg Units.val h1
      simpa [hx_unit.unit_spec] using this
    have hval2 : quadChar m hm (x : ZMod (4 * m)) = -1 := by
      rw [quadChar_apply_nat]
      have hx_odd : x % 2 = 1 := by omega
      simp only [hx_odd, Nat.one_ne_zero, ↓reduceIte]
      have hx_odd' : Odd x := Nat.odd_iff.mpr hx_odd
      have hJ : jacobiSym (m : ℤ) x = -1 := by
        rw [hm2k, Nat.cast_mul, Nat.cast_ofNat, jacobiSym.mul_left, jacobiSym.at_two hx_odd',
          ZMod.χ₈_nat_mod_eight, hx8]
        have hχ8 : ZMod.χ₈ (5 : ℕ) = -1 := by decide
        rw [hχ8]
        have hJk : jacobiSym (k : ℤ) x = 1 := by
          rw [jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr hk_odd) (by omega)]
          have : (x : ℤ) % (k : ℤ) = (1 : ℤ) % (k : ℤ) := by
            have := (ZMod.natCast_eq_natCast_iff x 1 k).mp (by simpa using hxk)
            exact_mod_cast this
          rw [jacobiSym.mod_left' this, jacobiSym.one_left]
        rw [hJk, mul_one]
      rw [hJ]; norm_num
    rw [hval1] at hval2
    norm_num at hval2
  · have hp_dvd_m : p ∣ m := (hp.dvd_mul.mp hp_dvd).resolve_left (fun h => by
      have h22 : p ∣ 2 ^ 2 := by simpa using h
      obtain ⟨e, he_le, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h22
      have he0 : e ≠ 0 := by intro h0; rw [h0] at he; exact hp.ne_one he
      have : e = 1 ∨ e = 2 := by omega
      rcases this with rfl | rfl
      · exact hp2 (by simpa using he)
      · rw [he] at hp; exact absurd hp (by decide))
    obtain ⟨r, hr⟩ := hp_dvd_m
    have hp_not_dvd_r : ¬ p ∣ r := by
      intro hpr
      have : p * p ∣ m := by rw [hr]; exact mul_dvd_mul_left p hpr
      exact hp.not_isUnit (hsq p this)
    have hcop : Nat.Coprime p (4 * r) := by
      refine Nat.Coprime.mul_right ?_ ?_
      · exact (hp.coprime_iff_not_dvd.mpr (fun h => hp2 (Nat.le_antisymm (Nat.le_of_dvd (by decide) h) hp.two_le))).pow_right 2
      · exact hp.coprime_iff_not_dvd.mpr hp_not_dvd_r
    obtain ⟨a, ha_pos, ha_lt, ha_nr⟩ := exists_nonresidue_prime hp hp2
    let e := ZMod.chineseRemainder hcop
    have hr_pos : 0 < r := by
      by_contra h0; push Not at h0; have : r = 0 := by omega
      rw [this, mul_zero] at hr; omega
    let _ : NeZero (p * (4 * r)) := ⟨Nat.mul_ne_zero hp.ne_zero (by omega)⟩
    let xZ : ZMod (p * (4 * r)) := e.symm ((a : ZMod p), 1)
    let x : ℕ := xZ.val
    have hxp : (x : ZMod p) = (a : ZMod p) := by
      have h1 : (e xZ).1 = (a : ZMod p) := by simp [xZ]
      have h2 : (xZ.cast : ZMod p) = (a : ZMod p) := by simpa [e, ZMod.chineseRemainder] using h1
      rw [← ZMod.natCast_zmod_val xZ, ZMod.cast_natCast (dvd_mul_right p (4 * r))] at h2
      exact h2
    have hx4r : (x : ZMod (4 * r)) = 1 := by
      have h1 : (e xZ).2 = 1 := by simp [xZ]
      have h2 : (xZ.cast : ZMod (4 * r)) = 1 := by simpa [e, ZMod.chineseRemainder] using h1
      rw [← ZMod.natCast_zmod_val xZ, ZMod.cast_natCast (dvd_mul_left (4 * r) p)] at h2
      exact h2
    have hx_mod4 : x % 4 = 1 := by
      have h4 : (4 : ℕ) ∣ 4 * r := dvd_mul_right 4 r
      have h1 : (x : ZMod 4) = 1 := by
        have := congrArg (ZMod.castHom h4 (ZMod 4)) hx4r
        simpa using this
      have := congrArg ZMod.val h1
      rw [ZMod.val_natCast] at this
      exact this.trans (by decide : (1 : ZMod 4).val = 1)
    have hx_cop_p : Nat.Coprime x p := by
      rw [Nat.coprime_comm]
      exact hp.coprime_iff_not_dvd.mpr (fun h => by
        have h0 : (x : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff x p).mpr h
        rw [hxp] at h0
        have hd : p ∣ a := (ZMod.natCast_eq_zero_iff a p).mp h0
        exact Nat.not_lt_of_ge (Nat.le_of_dvd ha_pos hd) ha_lt)
    have hx_cop : Nat.Coprime x (4 * m) := by
      have h4m : 4 * m = p * (4 * r) := by rw [hr]; ring
      rw [h4m]
      refine Nat.Coprime.mul_right hx_cop_p ?_
      rw [← ZMod.isUnit_iff_coprime, hx4r]; exact isUnit_one
    have hx_unit : IsUnit (x : ZMod (4 * m)) := (ZMod.isUnit_iff_coprime x (4 * m)).mpr hx_cop
    have hdiv : 4 * m / p = 4 * r := by
      rw [hr, show 4 * (p * r) = p * (4 * r) by ring, Nat.mul_div_cancel_left _ hp.pos]
    have hx_mod_div : (x : ZMod (4 * m / p)) = 1 := by
      have hmeq : x ≡ 1 [MOD (4 * m / p)] := by
        rw [hdiv]
        exact (ZMod.natCast_eq_natCast_iff x 1 (4 * r)).mp (by simpa using hx4r)
      simpa using (ZMod.natCast_eq_natCast_iff x 1 (4 * m / p)).mpr hmeq
    have hmem : hx_unit.unit ∈ (ZMod.unitsMap hdiv_dvd).ker := by
      rw [MonoidHom.mem_ker]
      ext
      simpa [ZMod.unitsMap_def, hx_unit.unit_spec] using hx_mod_div
    have h1 := hker hmem
    rw [MonoidHom.mem_ker] at h1
    have hval1 : quadChar m hm (x : ZMod (4 * m)) = 1 := by
      have := congrArg Units.val h1
      simpa [hx_unit.unit_spec] using this
    have hval2 : quadChar m hm (x : ZMod (4 * m)) = -1 := by
      rw [quadChar_apply_nat]
      have hx_odd : x % 2 = 1 := by omega
      simp only [hx_odd, Nat.one_ne_zero, ↓reduceIte]
      have hJ : jacobiSym (m : ℤ) x = -1 := by
        rw [hr, Nat.cast_mul, jacobiSym.mul_left]
        have hJp : jacobiSym (p : ℤ) x = -1 := by
          rw [jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left hp2)) hx_mod4]
          have hmod : (x : ℤ) % (p : ℤ) = (a : ℤ) % (p : ℤ) := by
            have := (ZMod.natCast_eq_natCast_iff x a p).mp hxp
            exact_mod_cast this
          rw [jacobiSym.mod_left' hmod, ha_nr]
        have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
        have hr2 : r % 2 = 0 := by
          have := congrArg (· % 2) hr
          rw [Nat.mul_mod, hp_odd, one_mul, Nat.mod_mod] at this
          omega
        let s := r / 2
        have hrs : r = 2 * s := by omega
        have hs_odd : s % 2 = 1 := by
          have : m = 2 * (p * s) := by rw [hr, hrs]; ring
          have : (p * s) % 2 = 1 := by omega
          rw [Nat.mul_mod, hp_odd, one_mul, Nat.mod_mod] at this
          exact this
        have hx8 : x % 8 = 1 := by
          have h8 : (8 : ℕ) ∣ 4 * r := by rw [hrs]; exact ⟨s, by ring⟩
          have h1 : (x : ZMod 8) = 1 := by
            have := congrArg (ZMod.castHom h8 (ZMod 8)) hx4r
            rw [map_natCast, map_one] at this; exact this
          have := congrArg ZMod.val h1
          rw [ZMod.val_natCast] at this
          exact this.trans (by decide : (1 : ZMod 8).val = 1)
        have hJr : jacobiSym (r : ℤ) x = 1 := by
          rw [hrs, Nat.cast_mul, Nat.cast_ofNat, jacobiSym.mul_left,
            jacobiSym.at_two (Nat.odd_iff.mpr hx_odd), ZMod.χ₈_nat_mod_eight, hx8]
          have hχ8 : ZMod.χ₈ (1 : ℕ) = 1 := by decide
          rw [hχ8, one_mul]
          rw [jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr hs_odd) hx_mod4]
          have hs_dvd : s ∣ 4 * r := by rw [hrs]; exact ⟨8, by ring⟩
          have hxs : (x : ZMod s) = 1 := by
            have := congrArg (ZMod.castHom hs_dvd (ZMod s)) hx4r
            rw [map_natCast, map_one] at this; exact this
          have hmod : (x : ℤ) % (s : ℤ) = (1 : ℤ) % (s : ℤ) := by
            have := (ZMod.natCast_eq_natCast_iff x 1 s).mp (by simpa using hxs)
            exact_mod_cast this
          rw [jacobiSym.mod_left' hmod, jacobiSym.one_left]
        rw [hJp, hJr, mul_one]
      rw [hJ]; norm_num
    rw [hval1] at hval2
    norm_num at hval2

/- Product character chi3 and nonnegativity of the fourfold Dirichlet convolution -/

private noncomputable def prodPrimChar {m₁ m₂ : ℕ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    Σ (D₃ : ℕ), DirichletCharacter ℂ D₃ :=
  let _ : NeZero (4 * m₁ * m₂) := ⟨by positivity⟩
  let h1 : 4 * m₁ ∣ 4 * m₁ * m₂ := dvd_mul_right (4 * m₁) m₂
  let h2 : 4 * m₂ ∣ 4 * m₁ * m₂ := ⟨m₁, by ring⟩
  let χp : DirichletCharacter ℂ (4 * m₁ * m₂) :=
    DirichletCharacter.changeLevel h1 (quadChar m₁ hm₁) *
    DirichletCharacter.changeLevel h2 (quadChar m₂ hm₂)
  ⟨χp.conductor, χp.primitiveCharacter⟩

private lemma prodPrimChar_spec {m₁ m₂ : ℕ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hm₁4 : m₁ % 4 = 2) (hm₂4 : m₂ % 4 = 2)
    (hsq₁ : Squarefree m₁) (hsq₂ : Squarefree m₂) (hne : m₁ ≠ m₂) :
    let D₃ := (prodPrimChar hm₁ hm₂).1
    let χ₃ := (prodPrimChar hm₁ hm₂).2
    1 < D₃ ∧ D₃ ≤ 4 * m₁ * m₂ ∧ χ₃.IsPrimitive ∧
    (∀ n : ℕ, χ₃ n = ((χ₃ n).re : ℂ) ∧ ((χ₃ n).re = 0 ∨ (χ₃ n).re = 1 ∨ (χ₃ n).re = -1)) ∧
    (∀ p : ℕ, p.Prime →
      (¬ p ∣ 4 * m₁ * m₂ → χ₃ p = quadChar m₁ hm₁ p * quadChar m₂ hm₂ p) ∧
      ((p ∣ m₁ ∧ ¬ p ∣ m₂) → χ₃ p = 0) ∧
      ((p ∣ m₂ ∧ ¬ p ∣ m₁) → χ₃ p = 0)) := by
  let _ : NeZero (4 * m₁ * m₂) := ⟨by positivity⟩
  let h1 : 4 * m₁ ∣ 4 * m₁ * m₂ := dvd_mul_right (4 * m₁) m₂
  let h2 : 4 * m₂ ∣ 4 * m₁ * m₂ := ⟨m₁, by ring⟩
  let χp : DirichletCharacter ℂ (4 * m₁ * m₂) :=
    DirichletCharacter.changeLevel h1 (quadChar m₁ hm₁) *
    DirichletCharacter.changeLevel h2 (quadChar m₂ hm₂)
  change 1 < χp.conductor ∧ χp.conductor ≤ 4 * m₁ * m₂ ∧ χp.primitiveCharacter.IsPrimitive ∧
    (∀ n : ℕ, χp.primitiveCharacter n = ((χp.primitiveCharacter n).re : ℂ) ∧
      ((χp.primitiveCharacter n).re = 0 ∨ (χp.primitiveCharacter n).re = 1 ∨
        (χp.primitiveCharacter n).re = -1)) ∧
    (∀ p : ℕ, p.Prime →
      (¬ p ∣ 4 * m₁ * m₂ → χp.primitiveCharacter p = quadChar m₁ hm₁ p * quadChar m₂ hm₂ p) ∧
      ((p ∣ m₁ ∧ ¬ p ∣ m₂) → χp.primitiveCharacter p = 0) ∧
      ((p ∣ m₂ ∧ ¬ p ∣ m₁) → χp.primitiveCharacter p = 0))
  have hcond_dvd : χp.conductor ∣ 4 * m₁ * m₂ := χp.conductor_dvd_level
  have hcond_pos : 0 < χp.conductor := Nat.pos_of_dvd_of_pos hcond_dvd (by positivity)
  let _ : NeZero χp.conductor := ⟨by omega⟩
  have hcond_le : χp.conductor ≤ 4 * m₁ * m₂ := Nat.le_of_dvd (by positivity) hcond_dvd
  -- Helper: if odd prime p divides exactly one of m1, m2, then p divides χp.conductor
  have hp_dvd_cond : ∀ p : ℕ, p.Prime →
      ((p ∣ m₁ ∧ ¬ p ∣ m₂) ∨ (p ∣ m₂ ∧ ¬ p ∣ m₁)) → p ∣ χp.conductor := by
    intro p hp hor
    have hp2 : p ≠ 2 := by
      intro h2eq; rw [h2eq] at hor
      rcases hor with ⟨_, hnd⟩ | ⟨_, hnd⟩ <;> exact hnd (by omega)
    -- Directly show p divides conductor
    by_contra hp_nd
    have hcop_pc : Nat.Coprime p χp.conductor := hp.coprime_iff_not_dvd.mpr hp_nd
    -- Build x coprime to 4 m1 m2 with x = 1 mod conductor (and mod 4 r) and J(x | p) = -1
    -- Let m1 m2 / p = R; note p does not divide R because p divides exactly one of m1, m2 and both are squarefree
    have hp_dvd_prod : p ∣ m₁ * m₂ := by
      rcases hor with ⟨h, _⟩ | ⟨h, _⟩
      · exact dvd_mul_of_dvd_left h m₂
      · exact dvd_mul_of_dvd_right h m₁
    obtain ⟨R, hR⟩ := hp_dvd_prod
    have hp_nd_R : ¬ p ∣ R := by
      intro hpR
      have hp2_dvd : p * p ∣ m₁ * m₂ := by rw [hR]; exact mul_dvd_mul_left p hpR
      rcases hor with ⟨hd1, hnd2⟩ | ⟨hd2, hnd1⟩
      · obtain ⟨a, ha⟩ := hd1
        rw [ha] at hp2_dvd
        have h1' : p ∣ a * m₂ := by
          obtain ⟨c, hc⟩ := hp2_dvd
          refine ⟨c, ?_⟩
          have : p * (a * m₂) = p * (p * c) := by linarith
          exact Nat.eq_of_mul_eq_mul_left hp.pos this
        rcases hp.dvd_mul.mp h1' with hpa | hpm2
        · exact hp.not_isUnit (hsq₁ p (by rw [ha]; exact mul_dvd_mul_left p hpa))
        · exact hnd2 hpm2
      · obtain ⟨a, ha⟩ := hd2
        rw [ha] at hp2_dvd
        have h1' : p ∣ m₁ * a := by
          obtain ⟨c, hc⟩ := hp2_dvd
          refine ⟨c, ?_⟩
          have : p * (m₁ * a) = p * (p * c) := by linarith
          exact Nat.eq_of_mul_eq_mul_left hp.pos this
        rcases hp.dvd_mul.mp h1' with hpm1 | hpa
        · exact hnd1 hpm1
        · exact hp.not_isUnit (hsq₂ p (by rw [ha]; exact mul_dvd_mul_left p hpa))
    -- Note 4 m1 m2 = p (4 R), gcd(p, 4 R) = 1, and conductor divides 4 R
    have h4prod : 4 * m₁ * m₂ = p * (4 * R) := by
      have : m₁ * m₂ = p * R := hR
      linarith
    have hcop_p4R : Nat.Coprime p (4 * R) := by
      refine Nat.Coprime.mul_right ?_ ?_
      · exact (hp.coprime_iff_not_dvd.mpr (fun h => hp2 (Nat.le_antisymm (Nat.le_of_dvd (by decide) h) hp.two_le))).pow_right 2
      · exact hp.coprime_iff_not_dvd.mpr hp_nd_R
    have hcond_dvd_4R : χp.conductor ∣ 4 * R := by
      have h1' : χp.conductor ∣ p * (4 * R) := h4prod ▸ hcond_dvd
      exact (Nat.coprime_comm.mp hcop_pc).dvd_of_dvd_mul_left h1'
    obtain ⟨a, ha_pos, ha_lt, ha_nr⟩ := exists_nonresidue_prime hp hp2
    let e := ZMod.chineseRemainder hcop_p4R
    have hR_pos : 0 < R := by
      by_contra h0; push Not at h0; have : R = 0 := by omega
      rw [this, mul_zero] at hR
      have : 0 < m₁ * m₂ := Nat.mul_pos hm₁ hm₂
      omega
    let _ : NeZero (p * (4 * R)) := ⟨Nat.mul_ne_zero hp.ne_zero (by omega)⟩
    let xZ : ZMod (p * (4 * R)) := e.symm ((a : ZMod p), 1)
    let x : ℕ := xZ.val
    have hxp : (x : ZMod p) = (a : ZMod p) := by
      have h1' : (e xZ).1 = (a : ZMod p) := by simp [xZ]
      have h2' : (xZ.cast : ZMod p) = (a : ZMod p) := by simpa [e, ZMod.chineseRemainder] using h1'
      rw [← ZMod.natCast_zmod_val xZ, ZMod.cast_natCast (dvd_mul_right p (4 * R))] at h2'
      exact h2'
    have hx4R : (x : ZMod (4 * R)) = 1 := by
      have h1' : (e xZ).2 = 1 := by simp [xZ]
      have h2' : (xZ.cast : ZMod (4 * R)) = 1 := by simpa [e, ZMod.chineseRemainder] using h1'
      rw [← ZMod.natCast_zmod_val xZ, ZMod.cast_natCast (dvd_mul_left (4 * R) p)] at h2'
      exact h2'
    have hx_cop_p : Nat.Coprime x p := by
      rw [Nat.coprime_comm]
      exact hp.coprime_iff_not_dvd.mpr (fun h => by
        have h0 : (x : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff x p).mpr h
        rw [hxp] at h0
        have hd : p ∣ a := (ZMod.natCast_eq_zero_iff a p).mp h0
        exact Nat.not_lt_of_ge (Nat.le_of_dvd ha_pos hd) ha_lt)
    have hx_cop : Nat.Coprime x (4 * m₁ * m₂) := by
      rw [h4prod]
      refine Nat.Coprime.mul_right hx_cop_p ?_
      rw [← ZMod.isUnit_iff_coprime, hx4R]; exact isUnit_one
    have hx_cond : (x : ZMod χp.conductor) = 1 := by
      have := congrArg (ZMod.castHom hcond_dvd_4R (ZMod χp.conductor)) hx4R
      rw [map_natCast, map_one] at this
      exact this
    have hx_copZ : IsCoprime (x : ℤ) ((4 * m₁ * m₂ : ℕ) : ℤ) := by
      rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast, Int.natAbs_natCast]
      exact hx_cop
    have hval1 : χp (x : ZMod (4 * m₁ * m₂)) = 1 := by
      have hpr := χp.primitiveCharacter_apply_of_isCoprime hx_copZ
      simp only [Int.cast_natCast] at hpr
      rw [← hpr, hx_cond, map_one]
    have hx_mod4 : x % 4 = 1 := by
      have h4 : (4 : ℕ) ∣ 4 * R := dvd_mul_right 4 R
      have h1' : (x : ZMod 4) = 1 := by
        have := congrArg (ZMod.castHom h4 (ZMod 4)) hx4R
        simpa using this
      have := congrArg ZMod.val h1'
      rw [ZMod.val_natCast] at this
      exact this.trans (by decide : (1 : ZMod 4).val = 1)
    have hx_odd : x % 2 = 1 := by omega
    have hval2 : χp (x : ZMod (4 * m₁ * m₂)) = -1 := by
      have hc1 : DirichletCharacter.changeLevel h1 (quadChar m₁ hm₁) (x : ZMod (4 * m₁ * m₂)) =
          quadChar m₁ hm₁ (x : ZMod (4 * m₁)) := by
        simpa using DirichletCharacter.changeLevel_eq_cast_of_dvd' (quadChar m₁ hm₁) h1 hx_copZ
      have hc2 : DirichletCharacter.changeLevel h2 (quadChar m₂ hm₂) (x : ZMod (4 * m₁ * m₂)) =
          quadChar m₂ hm₂ (x : ZMod (4 * m₂)) := by
        simpa using DirichletCharacter.changeLevel_eq_cast_of_dvd' (quadChar m₂ hm₂) h2 hx_copZ
      change DirichletCharacter.changeLevel h1 (quadChar m₁ hm₁) (x : ZMod (4 * m₁ * m₂)) *
        DirichletCharacter.changeLevel h2 (quadChar m₂ hm₂) (x : ZMod (4 * m₁ * m₂)) = -1
      rw [hc1, hc2, quadChar_apply_nat, quadChar_apply_nat]
      simp only [hx_odd, Nat.one_ne_zero, ↓reduceIte]
      have hJ : jacobiSym (m₁ : ℤ) x * jacobiSym (m₂ : ℤ) x = -1 := by
        rw [← jacobiSym.mul_left, ← Nat.cast_mul, hR, Nat.cast_mul, jacobiSym.mul_left]
        have hJp : jacobiSym (p : ℤ) x = -1 := by
          rw [jacobiSym.quadratic_reciprocity_one_mod_four'
            (Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left hp2)) hx_mod4]
          have hmod : (x : ℤ) % (p : ℤ) = (a : ℤ) % (p : ℤ) := by
            have := (ZMod.natCast_eq_natCast_iff x a p).mp hxp
            exact_mod_cast this
          rw [jacobiSym.mod_left' hmod, ha_nr]
        have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
        have hR4 : R % 4 = 0 := by
          have : (m₁ * m₂) % 4 = 0 := by rw [Nat.mul_mod, hm₁4, hm₂4]
          rw [hR] at this
          have h4dvd : 4 ∣ p * R := Nat.dvd_of_mod_eq_zero this
          have hcop4p : Nat.Coprime 4 p :=
            (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hp_odd)).pow_left 2
          exact Nat.mod_eq_zero_of_dvd (hcop4p.dvd_of_dvd_mul_left h4dvd)
        let S := R / 4
        have hRS : R = 4 * S := by omega
        have hS_odd : S % 2 = 1 := by
          have hm12 : (m₁ / 2) % 2 = 1 ∧ (m₂ / 2) % 2 = 1 := by omega
          have hprod : m₁ * m₂ = 4 * ((m₁ / 2) * (m₂ / 2)) := by
            have e1 : m₁ = 2 * (m₁ / 2) := by omega
            have e2 : m₂ = 2 * (m₂ / 2) := by omega
            calc m₁ * m₂ = (2 * (m₁ / 2)) * (2 * (m₂ / 2)) := by rw [← e1, ← e2]
              _ = 4 * ((m₁ / 2) * (m₂ / 2)) := by ring
          have hps : p * S = (m₁ / 2) * (m₂ / 2) := by nlinarith
          have hodd_prod : ((m₁ / 2) * (m₂ / 2)) % 2 = 1 := by
            rw [Nat.mul_mod, hm12.1, hm12.2]
          rw [← hps, Nat.mul_mod, hp_odd, one_mul, Nat.mod_mod] at hodd_prod
          exact hodd_prod
        have hJR : jacobiSym (R : ℤ) x = 1 := by
          rw [hRS, Nat.cast_mul, Nat.cast_ofNat, jacobiSym.mul_left,
            jacobiSym.at_four (Nat.odd_iff.mpr hx_odd), one_mul]
          rw [jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr hS_odd) hx_mod4]
          have hS_dvd : S ∣ 4 * R := by rw [hRS]; exact ⟨16, by ring⟩
          have hxS : (x : ZMod S) = 1 := by
            have := congrArg (ZMod.castHom hS_dvd (ZMod S)) hx4R
            rw [map_natCast, map_one] at this
            exact this
          have hmod : (x : ℤ) % (S : ℤ) = (1 : ℤ) % (S : ℤ) := by
            have := (ZMod.natCast_eq_natCast_iff x 1 S).mp (by simpa using hxS)
            exact_mod_cast this
          rw [jacobiSym.mod_left' hmod, jacobiSym.one_left]
        rw [hJp, hJR, mul_one]
      have : ((jacobiSym (m₁ : ℤ) x : ℂ) * (jacobiSym (m₂ : ℤ) x : ℂ)) =
          ((jacobiSym (m₁ : ℤ) x * jacobiSym (m₂ : ℤ) x : ℤ) : ℂ) := by push_cast; rfl
      rw [this, hJ]; norm_num
    rw [hval1] at hval2
    norm_num at hval2
  have hex_diff : ∃ p : ℕ, p.Prime ∧ ((p ∣ m₁ ∧ ¬ p ∣ m₂) ∨ (p ∣ m₂ ∧ ¬ p ∣ m₁)) := by
    by_contra hall
    push Not at hall
    have hpf : m₁.primeFactors = m₂.primeFactors := by
      ext p
      simp only [Nat.mem_primeFactors, ne_eq, hm₁.ne', hm₂.ne', not_false_eq_true, and_true]
      constructor
      · rintro ⟨hp, hd1⟩
        exact ⟨hp, (hall p hp).1 hd1⟩
      · rintro ⟨hp, hd2⟩
        exact ⟨hp, (hall p hp).2 hd2⟩
    have hprod1 : ∏ p ∈ m₁.primeFactors, p = m₁ :=
      Nat.prod_primeFactors_of_squarefree hsq₁
    have hprod2 : ∏ p ∈ m₂.primeFactors, p = m₂ :=
      Nat.prod_primeFactors_of_squarefree hsq₂
    exact hne (by rw [← hprod1, ← hprod2, hpf])
  have hcond_gt1 : 1 < χp.conductor := by
    obtain ⟨p, hp, hor⟩ := hex_diff
    have hd := hp_dvd_cond p hp hor
    have hle := Nat.le_of_dvd hcond_pos hd
    exact lt_of_lt_of_le hp.one_lt hle
  have hreal : ∀ n : ℕ, χp.primitiveCharacter n = ((χp.primitiveCharacter n).re : ℂ) ∧
      ((χp.primitiveCharacter n).re = 0 ∨ (χp.primitiveCharacter n).re = 1 ∨
        (χp.primitiveCharacter n).re = -1) := by
    intro n
    by_cases hu : IsUnit (n : ZMod χp.conductor)
    · have hsurj : Function.Surjective (ZMod.unitsMap hcond_dvd) :=
        ZMod.unitsMap_surjective hcond_dvd
      obtain ⟨v, hv⟩ := hsurj hu.unit
      have hv_val : ((v : ZMod (4 * m₁ * m₂)).val : ZMod (4 * m₁ * m₂)) = (v : ZMod (4 * m₁ * m₂)) :=
        ZMod.natCast_zmod_val _
      have hv_cop : IsCoprime ((v : ZMod (4 * m₁ * m₂)).val : ℤ) (4 * m₁ * m₂ : ℕ) := by
        rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast, Int.natAbs_natCast]
        have := (ZMod.isUnit_iff_coprime (v : ZMod (4 * m₁ * m₂)).val (4 * m₁ * m₂)).mp
          (by rw [hv_val]; exact v.isUnit)
        exact this
      have hcast : (((v : ZMod (4 * m₁ * m₂)).val : ℕ) : ZMod χp.conductor) = (n : ZMod χp.conductor) := by
        have h1' := congrArg Units.val hv
        simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, hu.unit_spec] at h1'
        rw [← h1', ← hv_val]
        simp
      have heq : χp.primitiveCharacter (n : ZMod χp.conductor) =
          χp ((v : ZMod (4 * m₁ * m₂)).val : ZMod (4 * m₁ * m₂)) := by
        rw [← hcast]
        simpa using (χp.primitiveCharacter_apply_of_isCoprime hv_cop)
      have hc1 : DirichletCharacter.changeLevel h1 (quadChar m₁ hm₁)
          ((v : ZMod (4 * m₁ * m₂)).val : ZMod (4 * m₁ * m₂)) =
          quadChar m₁ hm₁ ((v : ZMod (4 * m₁ * m₂)).val : ZMod (4 * m₁)) := by
        simpa using DirichletCharacter.changeLevel_eq_cast_of_dvd' (quadChar m₁ hm₁) h1 hv_cop
      have hc2 : DirichletCharacter.changeLevel h2 (quadChar m₂ hm₂)
          ((v : ZMod (4 * m₁ * m₂)).val : ZMod (4 * m₁ * m₂)) =
          quadChar m₂ hm₂ ((v : ZMod (4 * m₁ * m₂)).val : ZMod (4 * m₂)) := by
        simpa using DirichletCharacter.changeLevel_eq_cast_of_dvd' (quadChar m₂ hm₂) h2 hv_cop
      have hprod_eq : χp.primitiveCharacter (n : ZMod χp.conductor) =
          quadChar m₁ hm₁ ((v : ZMod (4 * m₁ * m₂)).val : ZMod (4 * m₁)) *
          quadChar m₂ hm₂ ((v : ZMod (4 * m₁ * m₂)).val : ZMod (4 * m₂)) := by
        rw [heq]
        dsimp [χp]
        rw [hc1, hc2]
      rw [hprod_eq]
      obtain ⟨hr1, hv1⟩ := quadChar_isReal hm₁ (v : ZMod (4 * m₁ * m₂)).val
      obtain ⟨hr2, hv2⟩ := quadChar_isReal hm₂ (v : ZMod (4 * m₁ * m₂)).val
      set c1 : ℝ := (quadChar m₁ hm₁ ((v : ZMod (4 * m₁ * m₂)).val : ZMod (4 * m₁))).re
      set c2 : ℝ := (quadChar m₂ hm₂ ((v : ZMod (4 * m₁ * m₂)).val : ZMod (4 * m₂))).re
      rw [hr1, hr2, ← Complex.ofReal_mul]
      simp only [Complex.ofReal_re]
      refine ⟨trivial, ?_⟩
      rcases hv1 with h1' | h1' | h1' <;> rcases hv2 with h2' | h2' | h2' <;>
        rw [h1', h2'] <;> norm_num
    · rw [MulChar.map_nonunit _ hu]
      simp
  refine ⟨hcond_gt1, hcond_le, χp.primitiveCharacter_isPrimitive, hreal, ?_⟩
  intro p hp
  refine ⟨?_, ?_, ?_⟩
  · intro hp_nd
    have hcop : IsCoprime (p : ℤ) (4 * m₁ * m₂ : ℕ) := by
      rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
      exact hp.coprime_iff_not_dvd.mpr hp_nd
    have hpr := χp.primitiveCharacter_apply_of_isCoprime hcop
    have hc1 := DirichletCharacter.changeLevel_eq_cast_of_dvd' (quadChar m₁ hm₁) h1 hcop
    have hc2 := DirichletCharacter.changeLevel_eq_cast_of_dvd' (quadChar m₂ hm₂) h2 hcop
    simp only [Int.cast_natCast] at hpr hc1 hc2
    rw [hpr]
    change DirichletCharacter.changeLevel h1 (quadChar m₁ hm₁) (p : ZMod (4 * m₁ * m₂)) *
      DirichletCharacter.changeLevel h2 (quadChar m₂ hm₂) (p : ZMod (4 * m₁ * m₂)) = _
    rw [hc1, hc2]
  · intro h12
    have hd := hp_dvd_cond p hp (Or.inl h12)
    apply MulChar.map_nonunit
    intro hu
    have hcop := (ZMod.isUnit_iff_coprime p χp.conductor).mp hu
    exact hp.not_dvd_one (Nat.dvd_gcd dvd_rfl hd |>.trans (by rw [hcop.gcd_eq_one]))
  · intro h21
    have hd := hp_dvd_cond p hp (Or.inr h21)
    apply MulChar.map_nonunit
    intro hu
    have hcop := (ZMod.isUnit_iff_coprime p χp.conductor).mp hu
    exact hp.not_dvd_one (Nat.dvd_gcd dvd_rfl hd |>.trans (by rw [hcop.gcd_eq_one]))

/- Polya-Vinogradov inequality for any primitive nontrivial Dirichlet character -/

private lemma norm_gaussSum_primitive {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt (N : ℝ) := by
  have h1 := congrFun (ZMod.dft_dft (χ : ZMod N → ℂ)) (-1 : ZMod N)
  simp only [neg_neg, map_one, smul_eq_mul, mul_one] at h1
  have h2 : ZMod.dft (ZMod.dft (χ : ZMod N → ℂ)) (-1) =
      gaussSum χ ZMod.stdAddChar * (χ (-1) * gaussSum χ⁻¹ ZMod.stdAddChar) := by
    have hft : ZMod.dft (χ : ZMod N → ℂ) = fun k => χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar := by
      ext k; exact hχ.fourierTransform_eq_inv_mul_gaussSum k
    rw [hft, ZMod.dft_mul_const]
    dsimp only
    have hneg : ZMod.dft (fun k : ZMod N => (⇑(χ⁻¹) : ZMod N → ℂ) (-k)) (-1) =
        ZMod.dft (⇑(χ⁻¹) : ZMod N → ℂ) 1 := by
      have := congrFun (ZMod.dft_comp_neg (⇑(χ⁻¹) : ZMod N → ℂ)) (-1)
      simpa using this
    rw [hneg]
    have hinv : χ⁻¹.IsPrimitive := by
      rw [DirichletCharacter.isPrimitive_def] at hχ ⊢
      have hcond : χ⁻¹.conductor = χ.conductor := by
        have hfac_iff : ∀ d : ℕ, χ⁻¹.FactorsThrough d ↔ χ.FactorsThrough d := by
          intro d
          have hunit_inv : ∀ u : (ZMod N)ˣ, (MulChar.toUnitHom χ⁻¹) u = ((MulChar.toUnitHom χ) u)⁻¹ := by
            intro u
            apply eq_inv_of_mul_eq_one_left
            ext
            change χ⁻¹ (u : ZMod N) * χ (u : ZMod N) = 1
            rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply u.isUnit]
          constructor <;> intro hf
          · have hd := hf.dvd
            rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd] at hf ⊢
            intro u hu
            have h1' := hf hu
            rw [MonoidHom.mem_ker] at h1' ⊢
            rw [hunit_inv, inv_eq_one] at h1'
            exact h1'
          · have hd := hf.dvd
            rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd] at hf ⊢
            intro u hu
            have h1' := hf hu
            rw [MonoidHom.mem_ker] at h1' ⊢
            rw [hunit_inv, h1', inv_one]
        unfold DirichletCharacter.conductor
        congr 1
        ext d
        exact hfac_iff d
      rw [hcond, hχ]
    rw [hinv.fourierTransform_eq_inv_mul_gaussSum 1]
    simp [mul_comm]
  have heq : (N : ℂ) = gaussSum χ ZMod.stdAddChar * (χ (-1) * gaussSum χ⁻¹ ZMod.stdAddChar) := by
    rw [← h1, h2]
  have hstar : ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ = ‖gaussSum χ ZMod.stdAddChar‖ := by
    have hst := star_gaussSum_eq χ ZMod.stdAddChar
    have hinv_add : (ZMod.stdAddChar (N := N))⁻¹ = ZMod.stdAddChar.mulShift (-1 : ZMod N) := by
      ext j
      simp [AddChar.mulShift_apply, AddChar.inv_apply, AddChar.map_neg_eq_inv]
    rw [hinv_add] at hst
    have hshift := gaussSum_mulShift_eq χ⁻¹ (ZMod.stdAddChar (N := N)) (-1 : (ZMod N)ˣ)
    have hneg1 : ((-1 : (ZMod N)ˣ) : ZMod N) = -1 := rfl
    rw [hneg1] at hshift
    rw [hshift] at hst
    have hunit : ‖χ (-1)‖ = 1 := χ.unit_norm_eq_one (-1 : (ZMod N)ˣ)
    have hn := congrArg norm hst
    simp only [inv_inv, norm_star, norm_mul, hunit, one_mul] at hn
    exact hn.symm
  have hnorm_eq : (N : ℝ) = ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 := by
    have hn := congrArg norm heq
    have hunit : ‖χ (-1)‖ = 1 := χ.unit_norm_eq_one (-1 : (ZMod N)ˣ)
    simp only [Complex.norm_natCast, norm_mul, hunit, one_mul, hstar, ← sq] at hn
    exact hn
  rw [hnorm_eq, Real.sqrt_sq (norm_nonneg _)]

private lemma harmonic_le_log_add_one (M : ℕ) (hM : 1 ≤ M) :
    ∑ k ∈ Icc 1 M, (1 : ℝ) / (k : ℝ) ≤ Real.log (M : ℝ) + 1 := by
  induction M with
  | zero => omega
  | succ n ih =>
    rcases eq_or_lt_of_le (Nat.zero_le n) with rfl | hn
    · simp
    · have hsplit : ∑ k ∈ Icc 1 (n + 1), (1 : ℝ) / (k : ℝ) =
          (∑ k ∈ Icc 1 n, (1 : ℝ) / (k : ℝ)) + 1 / ((n + 1 : ℕ) : ℝ) := by
        rw [Finset.sum_Icc_succ_top (by omega)]
      rw [hsplit]
      have hstep : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
        have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
        have hn1_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
        rw [← Real.log_div hn1_pos.ne' hn_pos.ne']
        have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hn1_pos hn_pos)
        have hcalc : 1 - (((n + 1 : ℕ) : ℝ) / (n : ℝ))⁻¹ = 1 / ((n + 1 : ℕ) : ℝ) := by
          push_cast; field_simp; ring
        linarith
      linarith [ih hn]

private lemma polya_vinogradov {N : ℕ} [NeZero N] (hN : 1 < N) {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (a b : ℕ) :
    ‖∑ n ∈ Icc a b, χ (n : ZMod N)‖ ≤ Real.sqrt (N : ℝ) * (Real.log (N : ℝ) + 1) := by
  have hinv : ∀ n : ℕ, (N : ℂ) * χ (n : ZMod N) =
      gaussSum χ ZMod.stdAddChar *
        ∑ k : ZMod N, χ⁻¹ (-k) * ZMod.stdAddChar (k * (n : ZMod N)) := by
    intro n
    have h := congrFun (ZMod.dft_dft (χ : ZMod N → ℂ)) (-(n : ZMod N))
    simp only [neg_neg, smul_eq_mul] at h
    rw [← h, ZMod.dft_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum k, smul_eq_mul]
    have hadd : ZMod.stdAddChar (-(k * -(n : ZMod N))) = ZMod.stdAddChar (k * (n : ZMod N)) := by
      congr 1; ring
    rw [hadd]
    ring
  have hsum : (N : ℂ) * (∑ n ∈ Icc a b, χ (n : ZMod N)) =
      gaussSum χ ZMod.stdAddChar *
        ∑ k : ZMod N, χ⁻¹ (-k) * (∑ n ∈ Icc a b, ZMod.stdAddChar (k * (n : ZMod N))) := by
    rw [Finset.mul_sum]
    calc ∑ n ∈ Icc a b, (N : ℂ) * χ (n : ZMod N)
        = ∑ n ∈ Icc a b, gaussSum χ ZMod.stdAddChar *
            ∑ k : ZMod N, χ⁻¹ (-k) * ZMod.stdAddChar (k * (n : ZMod N)) :=
          Finset.sum_congr rfl fun n _ => hinv n
      _ = gaussSum χ ZMod.stdAddChar *
            ∑ n ∈ Icc a b, ∑ k : ZMod N, χ⁻¹ (-k) * ZMod.stdAddChar (k * (n : ZMod N)) := by
          rw [← Finset.mul_sum]
      _ = gaussSum χ ZMod.stdAddChar *
            ∑ k : ZMod N, ∑ n ∈ Icc a b, χ⁻¹ (-k) * ZMod.stdAddChar (k * (n : ZMod N)) := by
          rw [Finset.sum_comm]
      _ = _ := by
          congr 1; refine Finset.sum_congr rfl fun k _ => (Finset.mul_sum ..).symm
  have hgeom : ∀ k : ZMod N, k ≠ 0 →
      ‖∑ n ∈ Icc a b, ZMod.stdAddChar (k * (n : ZMod N))‖ ≤
        1 / Real.sin (Real.pi * (k.val : ℝ) / (N : ℝ)) := by
    intro k hk
    set z : ℂ := ZMod.stdAddChar k
    have hz_eq : ∀ n : ℕ, ZMod.stdAddChar (k * (n : ZMod N)) = z ^ n := by
      intro n
      induction n with
      | zero => simp [z]
      | succ n ih =>
        rw [Nat.cast_succ, mul_add, mul_one, AddChar.map_add_eq_mul, ih, pow_succ]
    have hval_pos : 0 < k.val := Nat.pos_of_ne_zero (fun h0 => hk ((ZMod.val_eq_zero k).mp h0))
    have hval_lt : k.val < N := ZMod.val_lt k
    have hsin_pos : 0 < Real.sin (Real.pi * (k.val : ℝ) / (N : ℝ)) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · rw [div_lt_iff₀ (by positivity : (0 : ℝ) < N)]
        have : (k.val : ℝ) < (N : ℝ) := by exact_mod_cast hval_lt
        nlinarith [Real.pi_pos]
    set θ : ℝ := Real.pi * (k.val : ℝ) / (N : ℝ)
    have hze : z = Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) := by
      have h1 : z = Complex.exp (2 * Real.pi * Complex.I * (k.val : ℂ) / (N : ℂ)) := by
        rw [show z = (ZMod.toCircle k : ℂ) from rfl, ZMod.toCircle_apply]
      rw [h1]
      congr 1; dsimp [θ]; push_cast; ring
    have hnorm_sub : ‖1 - z‖ = 2 * Real.sin θ := by
      rw [hze]
      have h1 : 1 - Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) =
          Complex.exp ((θ : ℂ) * Complex.I) * (-2 * Complex.I * (Real.sin θ : ℂ)) := by
        rw [Complex.exp_mul_I, Complex.exp_mul_I]
        have hcos : Real.cos (2 * θ) = 1 - 2 * Real.sin θ ^ 2 := by
          have := Real.cos_two_mul' θ
          have := Real.sin_sq_add_cos_sq θ
          linarith
        have hsin : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
        have hce1 : Complex.cos ((2 * θ : ℝ) : ℂ) = (Real.cos (2 * θ) : ℂ) := by
          exact_mod_cast (Complex.ofReal_cos (2 * θ)).symm
        have hse1 : Complex.sin ((2 * θ : ℝ) : ℂ) = (Real.sin (2 * θ) : ℂ) := by
          exact_mod_cast (Complex.ofReal_sin (2 * θ)).symm
        have hce2 : Complex.cos (θ : ℂ) = (Real.cos θ : ℂ) := (Complex.ofReal_cos θ).symm
        have hse2 : Complex.sin (θ : ℂ) = (Real.sin θ : ℂ) := (Complex.ofReal_sin θ).symm
        rw [hce1, hse1, hce2, hse2, hcos, hsin]
        have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
        simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul,
          Complex.ofReal_ofNat, Complex.ofReal_pow]
        linear_combination 2 * (Real.sin θ : ℂ) ^ 2 * hI2
      rw [h1, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      have h2 : (-2 * Complex.I * (Real.sin θ : ℂ)) = ((-(2 * Real.sin θ) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [h2, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_neg,
        abs_of_pos (by positivity)]
    have hz_ne1 : z ≠ 1 := by
      intro hz1
      rw [hz1, sub_self, norm_zero] at hnorm_sub
      linarith
    have hz_norm : ‖z‖ = 1 := by
      rw [hze, Complex.norm_exp_ofReal_mul_I]
    by_cases hab : a ≤ b
    · have hgs : ∀ m, a ≤ m → (1 - z) * ∑ n ∈ Icc a m, z ^ n = z ^ a - z ^ (m + 1) := by
        intro m hm
        induction m, hm using Nat.le_induction with
        | base => simp [pow_succ]; ring
        | succ m hm ih =>
          rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
          ring
      have hsum_eq : ∑ n ∈ Icc a b, ZMod.stdAddChar (k * (n : ZMod N)) =
          (z ^ a - z ^ (b + 1)) / (1 - z) := by
        rw [Finset.sum_congr rfl fun n _ => hz_eq n, eq_div_iff (sub_ne_zero.mpr hz_ne1.symm),
          mul_comm, hgs b hab]
      rw [hsum_eq, norm_div, hnorm_sub]
      have hnum : ‖z ^ a - z ^ (b + 1)‖ ≤ 2 := by
        calc ‖z ^ a - z ^ (b + 1)‖ ≤ ‖z ^ a‖ + ‖z ^ (b + 1)‖ := norm_sub_le _ _
          _ = 1 + 1 := by simp [hz_norm]
          _ = 2 := by norm_num
      calc ‖z ^ a - z ^ (b + 1)‖ / (2 * Real.sin θ)
          ≤ 2 / (2 * Real.sin θ) :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ = 1 / Real.sin θ := by field_simp
    · have hempty : Icc a b = ∅ := Finset.Icc_eq_empty hab
      rw [hempty, Finset.sum_empty, norm_zero]
      positivity
  have hsin_sum : ∑ k ∈ Finset.univ.erase (0 : ZMod N),
      (1 : ℝ) / Real.sin (Real.pi * (k.val : ℝ) / (N : ℝ)) ≤ (N : ℝ) * (Real.log (N : ℝ) + 1) := by
    have hbij : ∑ k ∈ Finset.univ.erase (0 : ZMod N),
        (1 : ℝ) / Real.sin (Real.pi * (k.val : ℝ) / (N : ℝ)) =
        ∑ j ∈ Icc 1 (N - 1), (1 : ℝ) / Real.sin (Real.pi * (j : ℝ) / (N : ℝ)) := by
      refine Finset.sum_bij (fun k _ => k.val) ?_ ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk
        simp only [Finset.mem_Icc]
        exact ⟨Nat.pos_of_ne_zero (fun h0 => hk ((ZMod.val_eq_zero k).mp h0)),
          Nat.le_sub_one_of_lt (ZMod.val_lt k)⟩
      · intro k₁ _ k₂ _ heq
        exact ZMod.val_injective N heq
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        refine ⟨(j : ZMod N), ?_, ?_⟩
        · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          intro h0
          have hv : ((j : ZMod N).val) = 0 := by rw [h0, ZMod.val_zero]
          rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at hv
          omega
        · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      · intro _ _; rfl
    rw [hbij]
    have hterm : ∀ j ∈ Icc 1 (N - 1),
        (1 : ℝ) / Real.sin (Real.pi * (j : ℝ) / (N : ℝ)) ≤
          (N : ℝ) / (2 * ((min j (N - j) : ℕ) : ℝ)) := by
      intro j hj
      simp only [Finset.mem_Icc] at hj
      let m := min j (N - j)
      have hm_pos : 1 ≤ m := by omega
      have hm_half : 2 * m ≤ N := by omega
      have hsin_eq : Real.sin (Real.pi * (j : ℝ) / (N : ℝ)) =
          Real.sin (Real.pi * (m : ℝ) / (N : ℝ)) := by
        dsimp [m]
        rcases le_or_gt j (N - j) with hle | hgt
        · rw [min_eq_left hle]
        · rw [min_eq_right hgt.le]
          have hsub : Real.pi * ((N - j : ℕ) : ℝ) / (N : ℝ) =
              Real.pi - Real.pi * (j : ℝ) / (N : ℝ) := by
            rw [Nat.cast_sub (by omega)]; field_simp
          rw [hsub, Real.sin_pi_sub]
      rw [hsin_eq]
      have harg_le : Real.pi * (m : ℝ) / (N : ℝ) ≤ Real.pi / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have : 2 * (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm_half
        nlinarith [Real.pi_pos]
      have hmul := Real.mul_le_sin (by positivity) harg_le
      have hsimp : 2 / Real.pi * (Real.pi * (m : ℝ) / (N : ℝ)) = 2 * (m : ℝ) / (N : ℝ) := by
        field_simp [Real.pi_ne_zero]
      rw [hsimp] at hmul
      have hpos : (0 : ℝ) < 2 * (m : ℝ) / (N : ℝ) := by positivity
      calc (1 : ℝ) / Real.sin (Real.pi * (m : ℝ) / (N : ℝ))
          ≤ 1 / (2 * (m : ℝ) / (N : ℝ)) := one_div_le_one_div_of_le hpos hmul
        _ = (N : ℝ) / (2 * (m : ℝ)) := by field_simp
        _ = (N : ℝ) / (2 * ((min j (N - j) : ℕ) : ℝ)) := rfl
    calc ∑ j ∈ Icc 1 (N - 1), (1 : ℝ) / Real.sin (Real.pi * (j : ℝ) / (N : ℝ))
        ≤ ∑ j ∈ Icc 1 (N - 1), (N : ℝ) / (2 * ((min j (N - j) : ℕ) : ℝ)) :=
          Finset.sum_le_sum hterm
      _ ≤ 2 * ∑ m ∈ Icc 1 (N / 2), (N : ℝ) / (2 * (m : ℝ)) := by
          have hsplit : ∑ j ∈ Icc 1 (N - 1), (N : ℝ) / (2 * ((min j (N - j) : ℕ) : ℝ)) =
              (∑ j ∈ Icc 1 (N / 2), (N : ℝ) / (2 * ((min j (N - j) : ℕ) : ℝ))) +
              (∑ j ∈ Icc (N / 2 + 1) (N - 1), (N : ℝ) / (2 * ((min j (N - j) : ℕ) : ℝ))) := by
            have hunion : Icc 1 (N - 1) = Icc 1 (N / 2) ∪ Icc (N / 2 + 1) (N - 1) := by
              ext j; simp only [Finset.mem_Icc, Finset.mem_union]; omega
            have hdisj : Disjoint (Icc 1 (N / 2)) (Icc (N / 2 + 1) (N - 1)) := by
              rw [Finset.disjoint_left]; intro j h1 h2
              simp only [Finset.mem_Icc] at h1 h2; omega
            rw [hunion, Finset.sum_union hdisj]
          rw [hsplit]
          have hfirst : ∑ j ∈ Icc 1 (N / 2), (N : ℝ) / (2 * ((min j (N - j) : ℕ) : ℝ)) =
              ∑ m ∈ Icc 1 (N / 2), (N : ℝ) / (2 * (m : ℝ)) := by
            refine Finset.sum_congr rfl fun j hj => ?_
            simp only [Finset.mem_Icc] at hj
            rw [min_eq_left (by omega)]
          have hsecond : ∑ j ∈ Icc (N / 2 + 1) (N - 1), (N : ℝ) / (2 * ((min j (N - j) : ℕ) : ℝ)) ≤
              ∑ m ∈ Icc 1 (N / 2), (N : ℝ) / (2 * (m : ℝ)) := by
            have hbij2 : ∑ j ∈ Icc (N / 2 + 1) (N - 1), (N : ℝ) / (2 * ((min j (N - j) : ℕ) : ℝ)) =
                ∑ m ∈ Icc 1 (N - 1 - N / 2), (N : ℝ) / (2 * (m : ℝ)) := by
              refine Finset.sum_bij (fun j _ => N - j) ?_ ?_ ?_ ?_
              · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
              · intro j₁ hj₁ j₂ hj₂ heq; simp only [Finset.mem_Icc] at hj₁ hj₂; omega
              · intro m hm; simp only [Finset.mem_Icc] at hm
                refine ⟨N - m, ?_, by omega⟩
                simp only [Finset.mem_Icc]; omega
              · intro j hj; simp only [Finset.mem_Icc] at hj
                rw [min_eq_right (by omega)]
            rw [hbij2]
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
            intro m hm; simp only [Finset.mem_Icc] at hm ⊢; omega
          linarith
      _ = (N : ℝ) * ∑ m ∈ Icc 1 (N / 2), (1 : ℝ) / (m : ℝ) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => by ring
      _ ≤ (N : ℝ) * (Real.log ((N / 2 : ℕ) : ℝ) + 1) := by
          gcongr
          exact harmonic_le_log_add_one (N / 2) (by omega)
      _ ≤ (N : ℝ) * (Real.log (N : ℝ) + 1) := by
          have hpos2 : (0 : ℝ) < ((N / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N / 2)
          have hle2 : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.div_le_self N 2
          gcongr
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hnorm_sum : (N : ℝ) * ‖∑ n ∈ Icc a b, χ (n : ZMod N)‖ ≤
      Real.sqrt (N : ℝ) * ((N : ℝ) * (Real.log (N : ℝ) + 1)) := by
    calc (N : ℝ) * ‖∑ n ∈ Icc a b, χ (n : ZMod N)‖
        = ‖(N : ℂ) * ∑ n ∈ Icc a b, χ (n : ZMod N)‖ := by rw [norm_mul, Complex.norm_natCast]
      _ = ‖gaussSum χ ZMod.stdAddChar‖ *
            ‖∑ k : ZMod N, χ⁻¹ (-k) * ∑ n ∈ Icc a b, ZMod.stdAddChar (k * (n : ZMod N))‖ := by
          rw [hsum, norm_mul]
      _ = Real.sqrt (N : ℝ) *
            ‖∑ k ∈ Finset.univ.erase (0 : ZMod N),
              χ⁻¹ (-k) * ∑ n ∈ Icc a b, ZMod.stdAddChar (k * (n : ZMod N))‖ := by
          rw [norm_gaussSum_primitive hχ]
          congr 2
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod N))]
          have h0 : χ⁻¹ (-(0 : ZMod N)) = 0 := by
            simp only [neg_zero]
            exact MulChar.map_nonunit _ (by
              intro hu
              have h1 := (ZMod.isUnit_iff_coprime 0 N).mp (by simpa using hu)
              simp at h1; omega)
          rw [h0, zero_mul, zero_add]
      _ ≤ Real.sqrt (N : ℝ) *
            ∑ k ∈ Finset.univ.erase (0 : ZMod N),
              ‖χ⁻¹ (-k) * ∑ n ∈ Icc a b, ZMod.stdAddChar (k * (n : ZMod N))‖ := by
          gcongr; exact norm_sum_le _ _
      _ ≤ Real.sqrt (N : ℝ) *
            ∑ k ∈ Finset.univ.erase (0 : ZMod N),
              (1 : ℝ) / Real.sin (Real.pi * (k.val : ℝ) / (N : ℝ)) := by
          gcongr with k hk
          rw [norm_mul]
          calc ‖χ⁻¹ (-k)‖ * ‖∑ n ∈ Icc a b, ZMod.stdAddChar (k * (n : ZMod N))‖
              ≤ 1 * (1 / Real.sin (Real.pi * (k.val : ℝ) / (N : ℝ))) := by
                gcongr
                · exact χ⁻¹.norm_le_one (-k)
                · exact hgeom k (Finset.mem_erase.mp hk).1
            _ = _ := one_mul _
      _ ≤ Real.sqrt (N : ℝ) * ((N : ℝ) * (Real.log (N : ℝ) + 1)) := by gcongr
  nlinarith

/- Section 3: Dirichlet convolution, nonnegativity, and elementary upper bound on sum (1 * chi_m) -/

private def dconv (f g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, f d * g (n / d)

private def isMult (f : ℕ → ℝ) : Prop :=
  f 1 = 1 ∧ ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b

private lemma dconv_one (f g : ℕ → ℝ) : dconv f g 1 = f 1 * g 1 := by
  simp [dconv]

private lemma dconv_comm (f g : ℕ → ℝ) (n : ℕ) : dconv f g n = dconv g f n := by
  unfold dconv
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · refine Finset.sum_bij (fun d _ => n / d) ?_ ?_ ?_ ?_
    · intro d hd
      exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), hn⟩
    · intro d₁ hd₁ d₂ hd₂ heq
      have h1 := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd₁)
      have h2 := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd₂)
      have hpos : 0 < n / d₁ := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
        (Nat.dvd_of_mem_divisors hd₁)) (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd₁) (Nat.pos_of_ne_zero hn))
      have : d₁ * (n / d₁) = d₂ * (n / d₁) := by rw [h1, heq, h2]
      exact Nat.eq_of_mul_eq_mul_right hpos this
    · intro d hd
      refine ⟨n / d, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), hn⟩, ?_⟩
      exact Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hn
    · intro d hd
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hn, mul_comm]

private lemma dconv_assoc (f g h : ℕ → ℝ) (n : ℕ) :
    dconv (dconv f g) h n = dconv f (dconv g h) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [dconv]
  · unfold dconv
    have hL : ∑ d ∈ n.divisors, (∑ a ∈ d.divisors, f a * g (d / a)) * h (n / d) =
        ∑ p ∈ n.divisors.sigma (fun d => d.divisors), f p.2 * g (p.1 / p.2) * h (n / p.1) := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun d _ => Finset.sum_mul ..
    have hR : ∑ a ∈ n.divisors, f a * (∑ b ∈ (n / a).divisors, g b * h (n / a / b)) =
        ∑ p ∈ n.divisors.sigma (fun a => (n / a).divisors), f p.1 * (g p.2 * h (n / p.1 / p.2)) := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun a _ => Finset.mul_sum ..
    rw [hL, hR]
    refine Finset.sum_bij (fun p _ => ⟨p.2, p.1 / p.2⟩) ?_ ?_ ?_ ?_
    · intro ⟨d, a⟩ hp
      simp only [Finset.mem_sigma, Nat.mem_divisors] at hp ⊢
      obtain ⟨⟨hdn, _⟩, ⟨had, hd0⟩⟩ := hp
      have ha_pos : 0 < a := Nat.pos_of_dvd_of_pos had (Nat.pos_of_ne_zero hd0)
      have han : a ∣ n := dvd_trans had hdn
      have hna0 : n / a ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) han) ha_pos)
      refine ⟨⟨han, hn⟩, ⟨?_, hna0⟩⟩
      obtain ⟨k, hk⟩ := hdn
      obtain ⟨j, hj⟩ := had
      refine ⟨k, ?_⟩
      have h1 : d / a = j := by rw [hj, Nat.mul_div_cancel_left _ ha_pos]
      have h2 : n / a = j * k := by
        rw [hk, hj, mul_assoc, Nat.mul_div_cancel_left _ ha_pos]
      rw [h1, h2]
    · intro ⟨d₁, a₁⟩ hp₁ ⟨d₂, a₂⟩ hp₂ heq
      simp only [Finset.mem_sigma, Nat.mem_divisors] at hp₁ hp₂
      have ha : a₁ = a₂ := congrArg Sigma.fst heq
      have hq : d₁ / a₁ = d₂ / a₂ := by
        have := congrArg Sigma.snd heq; simpa using this
      have h1 := Nat.mul_div_cancel' hp₁.2.1
      have h2 := Nat.mul_div_cancel' hp₂.2.1
      have hd : d₁ = d₂ := by rw [← h1, ← h2, hq, ha]
      cases ha; cases hd; rfl
    · intro ⟨a, b⟩ hp
      simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
      obtain ⟨⟨han, _⟩, ⟨hbn, hna0⟩⟩ := hp
      have ha_pos : 0 < a := Nat.pos_of_dvd_of_pos han (Nat.pos_of_ne_zero hn)
      have hb_pos : 0 < b := Nat.pos_of_dvd_of_pos hbn (Nat.pos_of_ne_zero hna0)
      refine ⟨⟨a * b, a⟩, ?_, ?_⟩
      · simp only [Finset.mem_sigma, Nat.mem_divisors]
        refine ⟨⟨?_, hn⟩, ⟨dvd_mul_right a b, Nat.mul_ne_zero ha_pos.ne' hb_pos.ne'⟩⟩
        obtain ⟨k, hk⟩ := hbn
        refine ⟨k, ?_⟩
        have := Nat.mul_div_cancel' han
        rw [← this, hk]; ring
      · simp [Nat.mul_div_cancel_left _ ha_pos]
    · intro ⟨d, a⟩ hp
      simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
      obtain ⟨⟨hdn, _⟩, ⟨had, hd0⟩⟩ := hp
      have ha_pos : 0 < a := Nat.pos_of_dvd_of_pos had (Nat.pos_of_ne_zero hd0)
      have hdiv : n / a / (d / a) = n / d := by
        obtain ⟨k, hk⟩ := hdn
        obtain ⟨j, hj⟩ := had
        have h1 : d / a = j := by rw [hj, Nat.mul_div_cancel_left _ ha_pos]
        have hj_pos : 0 < j := by
          by_contra h0; push Not at h0; have : j = 0 := by omega
          rw [this, mul_zero] at hj; exact hd0 hj
        have h2 : n / a = j * k := by rw [hk, hj, mul_assoc, Nat.mul_div_cancel_left _ ha_pos]
        have h3 : n / d = k := by rw [hk, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
        rw [h1, h2, h3, Nat.mul_div_cancel_left _ hj_pos]
      rw [hdiv, mul_assoc]

private lemma dconv_isMult {f g : ℕ → ℝ} (hf : isMult f) (hg : isMult g) :
    isMult (dconv f g) := by
  refine ⟨by rw [dconv_one, hf.1, hg.1, mul_one], ?_⟩
  intro a b hcop
  rcases eq_or_ne a 0 with rfl | ha
  · simp [dconv]
  rcases eq_or_ne b 0 with rfl | hb
  · simp [dconv]
  unfold dconv
  have hbij : ∑ d ∈ (a * b).divisors, f d * g (a * b / d) =
      ∑ p ∈ a.divisors ×ˢ b.divisors, f (p.1 * p.2) * g (a * b / (p.1 * p.2)) := by
    symm
    refine Finset.sum_bij (fun p _ => p.1 * p.2) ?_ ?_ ?_ ?_
    · intro ⟨d₁, d₂⟩ hp
      simp only [Finset.mem_product, Nat.mem_divisors] at hp ⊢
      exact ⟨mul_dvd_mul hp.1.1 hp.2.1, Nat.mul_ne_zero ha hb⟩
    · intro ⟨d₁, d₂⟩ hp₁ ⟨d₁', d₂'⟩ hp₂ heq
      simp only [Finset.mem_product, Nat.mem_divisors] at hp₁ hp₂
      have hcop1 : Nat.Coprime d₁ d₂' := hcop.coprime_dvd_left hp₁.1.1 |>.coprime_dvd_right hp₂.2.1
      have hcop2 : Nat.Coprime d₁' d₂ := hcop.coprime_dvd_left hp₂.1.1 |>.coprime_dvd_right hp₁.2.1
      have hd1 : d₁ ∣ d₁' := hcop1.dvd_of_dvd_mul_right ⟨d₂, by linarith⟩
      have hd1' : d₁' ∣ d₁ := hcop2.dvd_of_dvd_mul_right ⟨d₂', by linarith⟩
      have heq1 : d₁ = d₁' := Nat.dvd_antisymm hd1 hd1'
      have hd1_pos : 0 < d₁ := Nat.pos_of_dvd_of_pos hp₁.1.1 (Nat.pos_of_ne_zero ha)
      have heq2 : d₂ = d₂' := Nat.eq_of_mul_eq_mul_left hd1_pos (heq1 ▸ heq)
      ext <;> assumption
    · intro d hd
      rw [Nat.mem_divisors] at hd
      refine ⟨(Nat.gcd d a, Nat.gcd d b), ?_, ?_⟩
      · simp only [Finset.mem_product, Nat.mem_divisors]
        exact ⟨⟨Nat.gcd_dvd_right d a, ha⟩, ⟨Nat.gcd_dvd_right d b, hb⟩⟩
      · have h1 := hcop.gcd_mul d
        rw [Nat.gcd_eq_left hd.1] at h1
        exact h1.symm
    · intro _ _; rfl
  rw [hbij, Finset.sum_product, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d₂ hd₂ => ?_
  have hd1a : d₁ ∣ a := Nat.dvd_of_mem_divisors hd₁
  have hd2b : d₂ ∣ b := Nat.dvd_of_mem_divisors hd₂
  have hcop12 : Nat.Coprime d₁ d₂ := hcop.coprime_dvd_left hd1a |>.coprime_dvd_right hd2b
  have hcopq : Nat.Coprime (a / d₁) (b / d₂) :=
    (hcop.coprime_dvd_left (Nat.div_dvd_of_dvd hd1a)).coprime_dvd_right (Nat.div_dvd_of_dvd hd2b)
  have hdiv : a * b / (d₁ * d₂) = (a / d₁) * (b / d₂) := by
    obtain ⟨q₁, hq₁⟩ := hd1a
    obtain ⟨q₂, hq₂⟩ := hd2b
    have hd1p : 0 < d₁ := Nat.pos_of_dvd_of_pos ⟨q₁, hq₁⟩ (Nat.pos_of_ne_zero ha)
    have hd2p : 0 < d₂ := Nat.pos_of_dvd_of_pos ⟨q₂, hq₂⟩ (Nat.pos_of_ne_zero hb)
    rw [hq₁, hq₂, Nat.mul_div_cancel_left _ hd1p, Nat.mul_div_cancel_left _ hd2p,
      show d₁ * q₁ * (d₂ * q₂) = (d₁ * d₂) * (q₁ * q₂) by ring,
      Nat.mul_div_cancel_left _ (Nat.mul_pos hd1p hd2p)]
  rw [hdiv, hf.2 d₁ d₂ hcop12, hg.2 (a / d₁) (b / d₂) hcopq]
  ring

private lemma isMult_nonneg_of_prime_pow {f : ℕ → ℝ} (hf : isMult f)
    (hp : ∀ p e : ℕ, p.Prime → 0 ≤ f (p ^ e)) :
    ∀ n : ℕ, 1 ≤ n → 0 ≤ f n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    rcases eq_or_lt_of_le hn with rfl | hn1
    · rw [hf.1]; norm_num
    · let p := n.minFac
      have hpp : p.Prime := Nat.minFac_prime (by omega)
      let e := n.factorization p
      have he_pos : 1 ≤ e :=
        Nat.pos_of_ne_zero ((Finsupp.mem_support_iff).mp (Nat.mem_primeFactors.mpr ⟨hpp, Nat.minFac_dvd n, by omega⟩))
      have hpe_dvd : p ^ e ∣ n := Nat.ordProj_dvd n p
      let r := n / p ^ e
      have hmul : p ^ e * r = n := Nat.mul_div_cancel' hpe_dvd
      have hcop : Nat.Coprime (p ^ e) r := by
        have hnd : ¬ p ∣ r := Nat.not_dvd_ordCompl hpp (show n ≠ 0 by omega)
        exact (hpp.coprime_iff_not_dvd.mpr hnd).pow_left e
      have hr_pos : 1 ≤ r := by
        by_contra h0; push Not at h0
        have hr0 : r = 0 := Nat.lt_one_iff.mp h0
        rw [hr0, mul_zero] at hmul; omega
      have hr_lt : r < n := by
        have hpe1 : 1 < p ^ e := one_lt_pow₀ hpp.one_lt (by omega)
        have h1 : 1 * r < p ^ e * r := Nat.mul_lt_mul_of_pos_right hpe1 hr_pos
        rw [one_mul, hmul] at h1
        exact h1
      rw [← hmul, hf.2 _ _ hcop]
      exact mul_nonneg (hp p e hpp) (ih r hr_lt hr_pos)

private lemma dconv_prime_pow {f g : ℕ → ℝ} {p : ℕ} (hp : p.Prime) (e : ℕ) :
    dconv f g (p ^ e) = ∑ j ∈ range (e + 1), f (p ^ j) * g (p ^ (e - j)) := by
  unfold dconv
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hj
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.pow_div (by omega) hp.pos]

private lemma dconv_one_complMult_prime_pow {c : ℝ} {χ : ℕ → ℝ} {p : ℕ} (hp : p.Prime)
    (hχ : ∀ k, χ (p ^ k) = c ^ k) (hc : c = 0 ∨ c = 1 ∨ c = -1) (e : ℕ) :
    0 ≤ dconv (fun _ => 1) χ (p ^ e) := by
  rw [dconv_prime_pow hp]
  have hsum : ∑ j ∈ range (e + 1), (1 : ℝ) * χ (p ^ (e - j)) = ∑ j ∈ range (e + 1), c ^ j := by
    have h1 : ∑ j ∈ range (e + 1), (1 : ℝ) * χ (p ^ (e - j)) = ∑ j ∈ range (e + 1), c ^ (e - j) :=
      Finset.sum_congr rfl fun j _ => by rw [one_mul, hχ]
    rw [h1]
    refine Finset.sum_bij (fun j _ => e - j) ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
    · intro j₁ hj₁ j₂ hj₂ heq; simp only [Finset.mem_range] at hj₁ hj₂; omega
    · intro j hj; simp only [Finset.mem_range] at hj
      exact ⟨e - j, Finset.mem_range.mpr (by omega), by omega⟩
    · intro _ _; rfl
  rw [hsum]
  rcases hc with rfl | rfl | rfl
  · refine Finset.sum_nonneg fun j _ => by positivity
  · refine Finset.sum_nonneg fun j _ => by positivity
  · clear hsum
    have hnn_neg1 : ∀ n : ℕ, 0 ≤ ∑ j ∈ range (n + 1), (-1 : ℝ) ^ j := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
        · have h0 : ∑ j ∈ range (2 * m + 1 + 1), (-1 : ℝ) ^ j = 0 := by
            clear ih
            induction m with
            | zero => simp
            | succ t iht =>
              have h1 : 2 * (t + 1) + 1 + 1 = (2 * t + 1 + 1) + 2 := by omega
              rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, iht]
              have hev : Even (2 * t + 1 + 1) := ⟨t + 1, by omega⟩
              have hodd : Odd (2 * t + 1 + 1 + 1) := ⟨t + 1, by omega⟩
              rw [hev.neg_one_pow, hodd.neg_one_pow]; ring
          linarith
        · rw [Finset.sum_range_succ]
          have hev : Even (2 * m + 1 + 1) := ⟨m + 1, by omega⟩
          rw [hev.neg_one_pow]
          linarith
    exact hnn_neg1 e

private noncomputable def chiRe {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : ℝ :=
  (χ (n : ZMod N)).re

private lemma chiRe_complMult {N : ℕ} {χ : DirichletCharacter ℂ N}
    (hreal : ∀ n : ℕ, χ (n : ZMod N) = ((χ (n : ZMod N)).re : ℂ)) :
    chiRe χ 1 = 1 ∧ ∀ a b : ℕ, chiRe χ (a * b) = chiRe χ a * chiRe χ b := by
  refine ⟨by simp [chiRe], ?_⟩
  intro a b
  unfold chiRe
  have h := map_mul χ (a : ZMod N) (b : ZMod N)
  rw [← Nat.cast_mul, hreal (a * b), hreal a, hreal b, ← Complex.ofReal_mul] at h
  exact Complex.ofReal_injective h

private lemma chiRe_isMult {N : ℕ} {χ : DirichletCharacter ℂ N}
    (hreal : ∀ n : ℕ, χ (n : ZMod N) = ((χ (n : ZMod N)).re : ℂ)) :
    isMult (chiRe χ) :=
  ⟨(chiRe_complMult hreal).1, fun a b _ => (chiRe_complMult hreal).2 a b⟩

private lemma chiRe_pow {N : ℕ} {χ : DirichletCharacter ℂ N}
    (hreal : ∀ n : ℕ, χ (n : ZMod N) = ((χ (n : ZMod N)).re : ℂ)) (p k : ℕ) :
    chiRe χ (p ^ k) = (chiRe χ p) ^ k := by
  induction k with
  | zero => simp [(chiRe_complMult hreal).1]
  | succ k ih => rw [pow_succ, (chiRe_complMult hreal).2, ih, pow_succ]

private lemma dconv_one_chiRe_nonneg {N : ℕ} {χ : DirichletCharacter ℂ N}
    (hreal : ∀ n : ℕ, χ (n : ZMod N) = ((χ (n : ZMod N)).re : ℂ) ∧
      ((χ (n : ZMod N)).re = 0 ∨ (χ (n : ZMod N)).re = 1 ∨ (χ (n : ZMod N)).re = -1)) :
    ∀ n : ℕ, 1 ≤ n → 0 ≤ dconv (fun _ => 1) (chiRe χ) n := by
  have hm : isMult (dconv (fun _ => 1) (chiRe χ)) :=
    dconv_isMult ⟨rfl, fun _ _ _ => by ring⟩ (chiRe_isMult (fun n => (hreal n).1))
  refine isMult_nonneg_of_prime_pow hm fun p e hp => ?_
  exact dconv_one_complMult_prime_pow hp (chiRe_pow (fun n => (hreal n).1) p) (hreal p).2 e

private lemma four_conv_nonneg {m₁ m₂ : ℕ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hm₁4 : m₁ % 4 = 2) (hm₂4 : m₂ % 4 = 2)
    (hsq₁ : Squarefree m₁) (hsq₂ : Squarefree m₂) (hne : m₁ ≠ m₂) :
    let χ₁ := chiRe (quadChar m₁ hm₁)
    let χ₂ := chiRe (quadChar m₂ hm₂)
    let χ₃ := chiRe (prodPrimChar hm₁ hm₂).2
    let f := dconv (fun _ => 1) (dconv χ₁ (dconv χ₂ χ₃))
    f 1 = 1 ∧ ∀ n : ℕ, 1 ≤ n → 0 ≤ f n := by
  have hspec := prodPrimChar_spec hm₁ hm₂ hm₁4 hm₂4 hsq₁ hsq₂ hne
  obtain ⟨_, _, _, hreal₃, hprimes⟩ := hspec
  let χ₁ := chiRe (quadChar m₁ hm₁)
  let χ₂ := chiRe (quadChar m₂ hm₂)
  let χ₃ := chiRe (prodPrimChar hm₁ hm₂).2
  let f := dconv (fun _ => 1) (dconv χ₁ (dconv χ₂ χ₃))
  have hmult₁ : isMult χ₁ := chiRe_isMult (fun n => (quadChar_isReal hm₁ n).1)
  have hmult₂ : isMult χ₂ := chiRe_isMult (fun n => (quadChar_isReal hm₂ n).1)
  have hmult₃ : isMult χ₃ := chiRe_isMult (fun n => (hreal₃ n).1)
  have hmult_f : isMult f :=
    dconv_isMult ⟨rfl, fun _ _ _ => by ring⟩ (dconv_isMult hmult₁ (dconv_isMult hmult₂ hmult₃))
  refine ⟨hmult_f.1, isMult_nonneg_of_prime_pow hmult_f fun p e hp => ?_⟩
  have hpow₁ : ∀ k, χ₁ (p ^ k) = (χ₁ p) ^ k := chiRe_pow (fun n => (quadChar_isReal hm₁ n).1) p
  have hpow₂ : ∀ k, χ₂ (p ^ k) = (χ₂ p) ^ k := chiRe_pow (fun n => (quadChar_isReal hm₂ n).1) p
  have hpow₃ : ∀ k, χ₃ (p ^ k) = (χ₃ p) ^ k := chiRe_pow (fun n => (hreal₃ n).1) p
  have hdconv_nn : ∀ (u v : ℕ → ℝ), (∀ k, 0 ≤ u (p ^ k)) → (∀ k, 0 ≤ v (p ^ k)) →
      0 ≤ dconv u v (p ^ e) := by
    intro u v hu hv
    rw [dconv_prime_pow hp]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hu j) (hv (e - j))
  -- Direct formula: f(p^e) is nonnegative in all valid (a, b, c) cases
  have h123 : ∀ (a b c : ℝ),
      (∀ k, χ₁ (p ^ k) = a ^ k) → (∀ k, χ₂ (p ^ k) = b ^ k) → (∀ k, χ₃ (p ^ k) = c ^ k) →
      (a = 0 ∨ a = 1 ∨ a = -1) → (b = 0 ∨ b = 1 ∨ b = -1) → (c = 0 ∨ c = 1 ∨ c = -1) →
      ((a = 0 ∧ b = 0) ∨ (a = 0 ∧ c = 0) ∨ (b = 0 ∧ c = 0) ∨ c = a * b) →
      0 ≤ f (p ^ e) := by
    intro a b c ha hb hc ha3 hb3 hc3 hcond
    have hre1 : f (p ^ e) = dconv (dconv (fun _ => 1) χ₁) (dconv χ₂ χ₃) (p ^ e) := by
      change dconv (fun _ => 1) (dconv χ₁ (dconv χ₂ χ₃)) (p ^ e) = _
      rw [dconv_assoc]
    have hre2 : f (p ^ e) = dconv (dconv (fun _ => 1) χ₂) (dconv χ₁ χ₃) (p ^ e) := by
      change dconv (fun _ => 1) (dconv χ₁ (dconv χ₂ χ₃)) (p ^ e) = _
      have hcomm12 : dconv χ₁ χ₂ = dconv χ₂ χ₁ := funext (dconv_comm χ₁ χ₂)
      have hswap : dconv χ₁ (dconv χ₂ χ₃) = dconv χ₂ (dconv χ₁ χ₃) := by
        ext n; rw [← dconv_assoc, hcomm12, dconv_assoc]
      rw [hswap, dconv_assoc]
    have hre3 : f (p ^ e) = dconv (dconv (fun _ => 1) χ₃) (dconv χ₁ χ₂) (p ^ e) := by
      change dconv (fun _ => 1) (dconv χ₁ (dconv χ₂ χ₃)) (p ^ e) = _
      have hswap : dconv χ₁ (dconv χ₂ χ₃) = dconv χ₃ (dconv χ₁ χ₂) := by
        ext n; rw [← dconv_assoc, dconv_comm (dconv χ₁ χ₂) χ₃]
      rw [hswap, dconv_assoc]
    have hpair_zero : ∀ (u v : ℕ → ℝ), (∀ k, u (p ^ k) = (0 : ℝ) ^ k) →
        (∀ k, v (p ^ k) = (0 : ℝ) ^ k) → ∀ k, 0 ≤ dconv u v (p ^ k) := by
      intro u v hu hv k
      rw [dconv_prime_pow hp]
      exact Finset.sum_nonneg fun j _ => by rw [hu, hv]; positivity
    have hpair_one : ∀ (u v : ℕ → ℝ) (cv : ℝ), (∀ k, u (p ^ k) = (1 : ℝ) ^ k) →
        (∀ k, v (p ^ k) = cv ^ k) → (cv = 0 ∨ cv = 1 ∨ cv = -1) →
        ∀ k, 0 ≤ dconv u v (p ^ k) := by
      intro u v cv hu hv hcv k
      have h1 : dconv u v (p ^ k) = dconv (fun _ => 1) v (p ^ k) := by
        rw [dconv_prime_pow hp, dconv_prime_pow hp]
        exact Finset.sum_congr rfl fun j _ => by rw [hu, one_pow]
      rw [h1]
      exact dconv_one_complMult_prime_pow hp hv hcv k
    rcases hcond with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · rw [hre3]
      exact hdconv_nn _ _ (fun k => dconv_one_complMult_prime_pow hp hc hc3 k)
        (hpair_zero χ₁ χ₂ ha hb)
    · rw [hre2]
      exact hdconv_nn _ _ (fun k => dconv_one_complMult_prime_pow hp hb hb3 k)
        (hpair_zero χ₁ χ₃ ha hc)
    · rw [hre1]
      exact hdconv_nn _ _ (fun k => dconv_one_complMult_prime_pow hp ha ha3 k)
        (hpair_zero χ₂ χ₃ hb hc)
    · rcases ha3 with rfl | rfl | rfl <;> rcases hb3 with rfl | rfl | rfl
      · rw [hre3]; exact hdconv_nn _ _ (fun k => dconv_one_complMult_prime_pow hp hc hc3 k)
          (hpair_zero χ₁ χ₂ ha hb)
      · rw [hre2]; exact hdconv_nn _ _ (fun k => dconv_one_complMult_prime_pow hp hb (Or.inr (Or.inl rfl)) k)
          (hpair_zero χ₁ χ₃ ha (by simpa using hc))
      · rw [hre2]; exact hdconv_nn _ _ (fun k => dconv_one_complMult_prime_pow hp hb (Or.inr (Or.inr rfl)) k)
          (hpair_zero χ₁ χ₃ ha (by simpa using hc))
      · rw [hre1]; exact hdconv_nn _ _ (fun k => dconv_one_complMult_prime_pow hp ha (Or.inr (Or.inl rfl)) k)
          (hpair_zero χ₂ χ₃ hb (by simpa using hc))
      · rw [hre1]; exact hdconv_nn _ _ (fun k => dconv_one_complMult_prime_pow hp ha (Or.inr (Or.inl rfl)) k)
          (hpair_one χ₂ χ₃ 1 hb (by simpa using hc) (Or.inr (Or.inl rfl)))
      · rw [hre2]; exact hdconv_nn _ _ (fun k => dconv_one_complMult_prime_pow hp hb (Or.inr (Or.inr rfl)) k)
          (hpair_one χ₁ χ₃ (-1) ha (by simpa using hc) (Or.inr (Or.inr rfl)))
      · rw [hre1]; exact hdconv_nn _ _ (fun k => dconv_one_complMult_prime_pow hp ha (Or.inr (Or.inr rfl)) k)
          (hpair_zero χ₂ χ₃ hb (by simpa using hc))
      · rw [hre1]; exact hdconv_nn _ _ (fun k => dconv_one_complMult_prime_pow hp ha (Or.inr (Or.inr rfl)) k)
          (hpair_one χ₂ χ₃ (-1) hb (by simpa using hc) (Or.inr (Or.inr rfl)))
      · rw [hre1]; exact hdconv_nn _ _ (fun k => dconv_one_complMult_prime_pow hp ha (Or.inr (Or.inr rfl)) k)
          (fun k => by rw [dconv_comm]; exact hpair_one χ₃ χ₂ (-1) (by simpa using hc) hb (Or.inr (Or.inr rfl)) k)
  apply h123 (χ₁ p) (χ₂ p) (χ₃ p) hpow₁ hpow₂ hpow₃ (quadChar_isReal hm₁ p).2
    (quadChar_isReal hm₂ p).2 (hreal₃ p).2
  by_cases hpd : p ∣ 4 * m₁ * m₂
  · have hq1_zero : p ∣ 4 * m₁ → χ₁ p = 0 := by
      intro hd
      dsimp [χ₁, chiRe]
      let _ : NeZero (4 * m₁) := ⟨by positivity⟩
      rw [MulChar.map_nonunit _ (by
        intro hu
        have hc := (ZMod.isUnit_iff_coprime p (4 * m₁)).mp hu
        exact hp.not_dvd_one (Nat.dvd_gcd dvd_rfl hd |>.trans (by rw [hc.gcd_eq_one])))]
      simp
    have hq2_zero : p ∣ 4 * m₂ → χ₂ p = 0 := by
      intro hd
      dsimp [χ₂, chiRe]
      let _ : NeZero (4 * m₂) := ⟨by positivity⟩
      rw [MulChar.map_nonunit _ (by
        intro hu
        have hc := (ZMod.isUnit_iff_coprime p (4 * m₂)).mp hu
        exact hp.not_dvd_one (Nat.dvd_gcd dvd_rfl hd |>.trans (by rw [hc.gcd_eq_one])))]
      simp
    by_cases hp2 : p = 2
    · left
      exact ⟨hq1_zero (by rw [hp2]; exact dvd_mul_of_dvd_left (by decide : 2 ∣ 4) m₁),
             hq2_zero (by rw [hp2]; exact dvd_mul_of_dvd_left (by decide : 2 ∣ 4) m₂)⟩
    · have hp_dvd_m1m2 : p ∣ m₁ * m₂ := by
        have h1' : p ∣ 4 * (m₁ * m₂) := by simpa [mul_assoc] using hpd
        exact (hp.dvd_mul.mp h1').resolve_left (fun h => by
          have h22 : p ∣ 2 ^ 2 := by simpa using h
          obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h22
          have hk0 : k ≠ 0 := by intro h0; rw [h0] at hk; exact hp.ne_one hk
          have : k = 1 ∨ k = 2 := by omega
          rcases this with rfl | rfl
          · exact hp2 (by simpa using hk)
          · rw [hk] at hp; exact absurd hp (by decide))
      by_cases hm1d : p ∣ m₁
      · by_cases hm2d : p ∣ m₂
        · left; exact ⟨hq1_zero (dvd_mul_of_dvd_right hm1d 4), hq2_zero (dvd_mul_of_dvd_right hm2d 4)⟩
        · right; left
          exact ⟨hq1_zero (dvd_mul_of_dvd_right hm1d 4), by
            dsimp [χ₃, chiRe]; rw [(hprimes p hp).2.1 ⟨hm1d, hm2d⟩]; simp⟩
      · have hm2d : p ∣ m₂ := (hp.dvd_mul.mp hp_dvd_m1m2).resolve_left hm1d
        right; right; left
        exact ⟨hq2_zero (dvd_mul_of_dvd_right hm2d 4), by
          dsimp [χ₃, chiRe]; rw [(hprimes p hp).2.2 ⟨hm2d, hm1d⟩]; simp⟩
  · right; right; right
    have h := (hprimes p hp).1 hpd
    dsimp [χ₁, χ₂, χ₃, chiRe]
    have h1r := (quadChar_isReal hm₁ p).1
    have h2r := (quadChar_isReal hm₂ p).1
    rw [h]
    conv_lhs => rw [h1r, h2r, ← Complex.ofReal_mul]
    rw [Complex.ofReal_re]

/- Section 3b: Elementary upper bound on partial sums via Z[sqrt(m)] lattice points -/

private lemma not_sq_of_squarefree_gt_one {m : ℕ} (hm1 : 1 < m) (hsq : Squarefree m) (k : ℤ) :
    (m : ℤ) ≠ k * k := by
  intro h
  have hk : k.natAbs * k.natAbs = m := by
    have := congrArg Int.natAbs h
    simpa [Int.natAbs_mul] using this.symm
  have hunit : IsUnit k.natAbs := hsq k.natAbs (by rw [hk])
  have hk1 : k.natAbs = 1 := Nat.isUnit_iff.mp hunit
  rw [hk1, mul_one] at hk
  omega

private lemma zsqrtd_isDomain {m : ℕ} (hm1 : 1 < m) (hsq : Squarefree m) :
    IsDomain (Zsqrtd (m : ℤ)) := by
  have hinj : Function.Injective (Zsqrtd.toReal (show (0 : ℤ) ≤ m by positivity)) :=
    Zsqrtd.toReal_injective (by positivity) (not_sq_of_squarefree_gt_one hm1 hsq)
  exact hinj.isDomain (Zsqrtd.toReal (show (0 : ℤ) ≤ m by positivity))

private lemma zsqrtd_norm_pow {d : ℤ} (z : Zsqrtd d) (n : ℕ) :
    (z ^ n).norm = z.norm ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Zsqrtd.norm_mul, ih]

private lemma zsqrtd_irreducible_of_norm_prime {m p : ℕ} (hm1 : 1 < m) (hsq : Squarefree m)
    (hp : p.Prime) {w : Zsqrtd (m : ℤ)} (hnorm : w.norm.natAbs = p) : Irreducible w := by
  let _ : IsDomain (Zsqrtd (m : ℤ)) := zsqrtd_isDomain hm1 hsq
  refine ⟨?_, ?_⟩
  · intro hu
    have h1 : w.norm.natAbs = 1 :=
      Int.isUnit_iff_natAbs_eq.mp ((Zsqrtd.isUnit_iff_norm_isUnit w).mp hu)
    rw [hnorm] at h1
    exact hp.ne_one h1
  · intro a b hab
    have hmul : a.norm.natAbs * b.norm.natAbs = p := by
      have := congrArg (fun z : Zsqrtd (m : ℤ) => z.norm.natAbs) hab
      simpa [Zsqrtd.norm_mul, Int.natAbs_mul, hnorm] using this.symm
    rcases hp.eq_one_or_self_of_dvd a.norm.natAbs ⟨b.norm.natAbs, hmul.symm⟩ with ha1 | hap
    · left
      rw [Zsqrtd.isUnit_iff_norm_isUnit]
      exact Int.isUnit_iff_natAbs_eq.mpr ha1
    · right
      rw [hap] at hmul
      have hb1 : b.norm.natAbs = 1 := by
        have hp_pos : 0 < p := hp.pos
        nlinarith
      rw [Zsqrtd.isUnit_iff_norm_isUnit]
      exact Int.isUnit_iff_natAbs_eq.mpr hb1

private lemma zsqrtd_split_primes_of_pid {m p : ℕ} (hm1 : 1 < m) (hsq : Squarefree m)
    (hpid : IsPrincipalIdealRing (Zsqrtd (m : ℤ)))
    (hp : p.Prime) (hp2 : p ≠ 2) (hnd : ¬ p ∣ m) (hJ : jacobiSym (m : ℤ) p = 1) :
    ∃ w₁ w₂ : Zsqrtd (m : ℤ),
      w₁.norm.natAbs = p ∧ w₂.norm.natAbs = p ∧
      Irreducible w₁ ∧ Irreducible w₂ ∧ ¬ Associated w₁ w₂ := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : IsDomain (Zsqrtd (m : ℤ)) := zsqrtd_isDomain hm1 hsq
  have hleg : legendreSym p (m : ℤ) = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]; exact hJ
  have hsq_mod : IsSquare ((m : ℤ) : ZMod p) := (legendreSym.eq_one_iff p (by
    intro h0
    have hd : (p : ℤ) ∣ (m : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (m : ℤ) p).mp h0
    exact hnd (Int.ofNat_dvd.mp hd))).mp hleg
  obtain ⟨r, hr⟩ := hsq_mod
  let a : ℤ := (r.val : ℤ)
  have ha_sq : (p : ℤ) ∣ a ^ 2 - (m : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast [a]
    rw [ZMod.natCast_zmod_val, sq, ← hr]
    simp
  have ha_nd : ¬ (p : ℤ) ∣ a := by
    intro hpa
    have hr0 : r = 0 := by
      have h0 : (a : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr hpa
      simpa [a, ZMod.natCast_zmod_val] using h0
    rw [hr0, mul_zero] at hr
    have hd : (p : ℤ) ∣ (m : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (m : ℤ) p).mp hr
    exact hnd (Int.ofNat_dvd.mp hd)
  have hgen_norm : ∀ (s : ℤ), s ^ 2 = 1 →
      ∃ w : Zsqrtd (m : ℤ), Ideal.span {(p : Zsqrtd (m : ℤ)), ⟨a, s⟩} = Ideal.span {w} ∧
        w.norm.natAbs = p := by
    intro s hs
    let I : Ideal (Zsqrtd (m : ℤ)) := Ideal.span {(p : Zsqrtd (m : ℤ)), ⟨a, s⟩}
    obtain ⟨w, hw⟩ := (IsPrincipalIdealRing.principal I).principal
    have hp_mem : (p : Zsqrtd (m : ℤ)) ∈ I := Ideal.subset_span (by simp)
    have ha_mem : (⟨a, s⟩ : Zsqrtd (m : ℤ)) ∈ I := Ideal.subset_span (by simp)
    rw [hw, Ideal.mem_span_singleton] at hp_mem ha_mem
    obtain ⟨β, hβ⟩ := hp_mem
    obtain ⟨γ, hγ⟩ := ha_mem
    have hnorm_p : w.norm * β.norm = (p : ℤ) ^ 2 := by
      have h := congrArg Zsqrtd.norm hβ
      simp only [Zsqrtd.norm_mul, Zsqrtd.norm_natCast] at h
      rw [← sq] at h; exact h.symm
    have hdvd : w.norm.natAbs ∣ p ^ 2 := by
      refine ⟨β.norm.natAbs, ?_⟩
      have := congrArg Int.natAbs hnorm_p
      simpa [Int.natAbs_mul, Int.natAbs_pow] using this.symm
    obtain ⟨e, he_le, he_eq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have he_ne0 : e ≠ 0 := by
      intro he0; rw [he0, pow_zero] at he_eq
      have hu : IsUnit w := (Zsqrtd.isUnit_iff_norm_isUnit w).mpr (Int.isUnit_iff_natAbs_eq.mpr he_eq)
      have h1 : (1 : Zsqrtd (m : ℤ)) ∈ I := by rw [hw, Ideal.mem_span_singleton]; exact hu.dvd
      rw [Ideal.mem_span_pair] at h1
      obtain ⟨u, v, huv⟩ := h1
      have hre : (u * (p : Zsqrtd (m : ℤ)) + v * ⟨a, s⟩).re =
          u.re * (p : ℤ) + (v.re * a + (m : ℤ) * v.im * s) := by simp
      have him : (u * (p : Zsqrtd (m : ℤ)) + v * ⟨a, s⟩).im =
          u.im * (p : ℤ) + (v.re * s + v.im * a) := by simp
      have hmod : ((u * (p : Zsqrtd (m : ℤ)) + v * ⟨a, s⟩).re : ZMod p) -
          (s : ZMod p) * (a : ZMod p) * ((u * (p : Zsqrtd (m : ℤ)) + v * ⟨a, s⟩).im : ZMod p) = 1 := by
        have h1re := congrArg (fun z : Zsqrtd (m : ℤ) => (z.re : ZMod p)) huv
        have h1im := congrArg (fun z : Zsqrtd (m : ℤ) => (z.im : ZMod p)) huv
        simp at h1re h1im; simp [h1re, h1im]
      rw [hre, him] at hmod
      push_cast at hmod
      have hp0 : (p : ZMod p) = 0 := ZMod.natCast_self p
      have hs2 : (s : ZMod p) ^ 2 = 1 := by
        have := congrArg (fun z : ℤ => (z : ZMod p)) hs
        simpa using this
      have ha2 : (a : ZMod p) ^ 2 = (m : ZMod p) := by
        have h0 : ((a ^ 2 - (m : ℤ) : ℤ) : ZMod p) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ha_sq
        push_cast at h0; exact sub_eq_zero.mp h0
      rw [hp0] at hmod
      have hzero : (u.re : ZMod p) * 0 + ((v.re : ZMod p) * (a : ZMod p) +
          (m : ZMod p) * (v.im : ZMod p) * (s : ZMod p)) -
          (s : ZMod p) * (a : ZMod p) * ((u.im : ZMod p) * 0 +
          ((v.re : ZMod p) * (s : ZMod p) + (v.im : ZMod p) * (a : ZMod p))) = 0 := by
        linear_combination -(v.re : ZMod p) * (a : ZMod p) * hs2 -
          (v.im : ZMod p) * (s : ZMod p) * ha2
      rw [hzero] at hmod
      exact zero_ne_one hmod
    have he_ne2 : e ≠ 2 := by
      intro he2; rw [he2] at he_eq
      have hβ_abs : β.norm.natAbs = 1 := by
        have hmul := congrArg Int.natAbs hnorm_p
        rw [Int.natAbs_mul, he_eq] at hmul
        have hp2_pos : 0 < p ^ 2 := pow_pos hp.pos 2
        have hsq_abs : ((p : ℤ) ^ 2).natAbs = p ^ 2 := by simp
        rw [hsq_abs] at hmul; nlinarith
      obtain ⟨u, hu⟩ := (Zsqrtd.isUnit_iff_norm_isUnit β).mpr (Int.isUnit_iff_natAbs_eq.mpr hβ_abs)
      have hw_eq : w = (p : Zsqrtd (m : ℤ)) * ((u⁻¹ : (Zsqrtd (m : ℤ))ˣ) : Zsqrtd (m : ℤ)) := by
        rw [hβ, ← hu, mul_assoc, Units.mul_inv, mul_one]
      rw [hw_eq, mul_assoc] at hγ
      have him := congrArg Zsqrtd.im hγ
      have him' : ((p : Zsqrtd (m : ℤ)) * (((u⁻¹ : (Zsqrtd (m : ℤ))ˣ) : Zsqrtd (m : ℤ)) * γ)).im =
          (p : ℤ) * (((u⁻¹ : (Zsqrtd (m : ℤ))ˣ) : Zsqrtd (m : ℤ)) * γ).im := by simp
      rw [him'] at him
      have hdvd_s : (p : ℤ) ∣ s := ⟨_, him⟩
      have hdvd1 : p ∣ 1 := by
        have hs1 : s.natAbs = 1 := by
          have := congrArg Int.natAbs hs; simpa [Int.natAbs_pow] using this
        simpa [hs1] using Int.natAbs_dvd_natAbs.mpr hdvd_s
      exact hp.not_dvd_one hdvd1
    have he1 : e = 1 := by omega
    rw [he1, pow_one] at he_eq
    exact ⟨w, hw, he_eq⟩
  obtain ⟨w₁, hw₁_id, hw₁_n⟩ := hgen_norm (-1) (by norm_num)
  obtain ⟨w₂, hw₂_id, hw₂_n⟩ := hgen_norm 1 (by norm_num)
  refine ⟨w₁, w₂, hw₁_n, hw₂_n, zsqrtd_irreducible_of_norm_prime hm1 hsq hp hw₁_n,
    zsqrtd_irreducible_of_norm_prime hm1 hsq hp hw₂_n, ?_⟩
  intro hassoc
  have hid_eq : Ideal.span {(p : Zsqrtd (m : ℤ)), ⟨a, -1⟩} =
      Ideal.span {(p : Zsqrtd (m : ℤ)), ⟨a, 1⟩} := by
    rw [hw₁_id, hw₂_id, Ideal.span_singleton_eq_span_singleton]
    exact hassoc
  have hmem : (⟨a, 1⟩ : Zsqrtd (m : ℤ)) ∈ Ideal.span {(p : Zsqrtd (m : ℤ)), ⟨a, -1⟩} := by
    rw [hid_eq]; exact Ideal.subset_span (by simp)
  have h2a_mem : (⟨2 * a, 0⟩ : Zsqrtd (m : ℤ)) ∈ Ideal.span {(p : Zsqrtd (m : ℤ)), ⟨a, -1⟩} := by
    have hsum : (⟨2 * a, 0⟩ : Zsqrtd (m : ℤ)) = ⟨a, 1⟩ + ⟨a, -1⟩ := by
      ext
      · simp; ring
      · simp
    rw [hsum]
    exact Ideal.add_mem _ hmem (Ideal.subset_span (by simp))
  rw [Ideal.mem_span_pair] at h2a_mem
  obtain ⟨u, v, huv⟩ := h2a_mem
  have hre : (u * (p : Zsqrtd (m : ℤ)) + v * ⟨a, -1⟩).re =
      u.re * (p : ℤ) + (v.re * a - (m : ℤ) * v.im) := by simp; ring
  have him : (u * (p : Zsqrtd (m : ℤ)) + v * ⟨a, -1⟩).im =
      u.im * (p : ℤ) + (v.im * a - v.re) := by simp; ring
  have hmod : ((u * (p : Zsqrtd (m : ℤ)) + v * ⟨a, -1⟩).re : ZMod p) +
      (a : ZMod p) * ((u * (p : Zsqrtd (m : ℤ)) + v * ⟨a, -1⟩).im : ZMod p) = (2 * a : ZMod p) := by
    have h1re := congrArg (fun z : Zsqrtd (m : ℤ) => (z.re : ZMod p)) huv
    have h1im := congrArg (fun z : Zsqrtd (m : ℤ) => (z.im : ZMod p)) huv
    simp at h1re h1im; simp [h1re, h1im]
  rw [hre, him] at hmod
  push_cast at hmod
  have hp0 : (p : ZMod p) = 0 := ZMod.natCast_self p
  have ha2 : (a : ZMod p) ^ 2 = (m : ZMod p) := by
    have h0 : ((a ^ 2 - (m : ℤ) : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ha_sq
    push_cast at h0; exact sub_eq_zero.mp h0
  rw [hp0] at hmod
  have hzero : (u.re : ZMod p) * 0 + ((v.re : ZMod p) * (a : ZMod p) - (m : ZMod p) * (v.im : ZMod p)) +
      (a : ZMod p) * ((u.im : ZMod p) * 0 + ((v.im : ZMod p) * (a : ZMod p) - (v.re : ZMod p))) = 0 := by
    linear_combination (v.im : ZMod p) * ha2
  rw [hzero] at hmod
  have hdvd2a : (p : ℤ) ∣ 2 * a := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact hmod.symm
  have hpZ : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  rcases hpZ.dvd_or_dvd hdvd2a with h2 | ha'
  · have : p ∣ 2 := Int.ofNat_dvd.mp h2
    exact hp2 (Nat.le_antisymm (Nat.le_of_dvd (by decide) this) hp.two_le)
  · exact ha_nd ha'

private lemma exists_nonassoc_of_norm {m y : ℕ} (hy : 1 ≤ y) (hm : m + 2 = (4 * y) ^ 2)
    (hsq : Squarefree m) (hpid : IsPrincipalIdealRing (Zsqrtd (m : ℤ))) :
    ∀ n : ℕ, 1 ≤ n →
      ∃ S : Finset (Zsqrtd (m : ℤ)),
        (S.card : ℝ) = dconv (fun _ => 1) (chiRe (quadChar m (by nlinarith))) n ∧
        (∀ α ∈ S, α.norm.natAbs = n) ∧
        (∀ α ∈ S, ∀ β ∈ S, Associated α β → α = β) := by
  have hm_pos : 0 < m := by nlinarith
  have hm1 : 1 < m := by nlinarith
  let _ : IsDomain (Zsqrtd (m : ℤ)) := zsqrtd_isDomain hm1 hsq
  let χ := chiRe (quadChar m hm_pos)
  let a := dconv (fun _ => 1) χ
  have ha_mult : isMult a :=
    dconv_isMult ⟨rfl, fun _ _ _ => by ring⟩ (chiRe_isMult (fun n => (quadChar_isReal hm_pos n).1))
  have hpp : ∀ p e : ℕ, p.Prime →
      ∃ S : Finset (Zsqrtd (m : ℤ)),
        (S.card : ℝ) = a (p ^ e) ∧
        (∀ α ∈ S, α.norm.natAbs = p ^ e) ∧
        (∀ α ∈ S, ∀ β ∈ S, Associated α β → α = β) := by
    intro p e hp
    have hpow : ∀ k, χ (p ^ k) = (χ p) ^ k := chiRe_pow (fun n => (quadChar_isReal hm_pos n).1) p
    have ha_pe : a (p ^ e) = ∑ j ∈ range (e + 1), (χ p) ^ j := by
      dsimp [a]
      rw [dconv_prime_pow hp]
      have h1 : ∑ j ∈ range (e + 1), (1 : ℝ) * χ (p ^ (e - j)) = ∑ j ∈ range (e + 1), (χ p) ^ (e - j) :=
        Finset.sum_congr rfl fun j _ => by rw [one_mul, hpow]
      rw [h1]
      refine Finset.sum_bij (fun j _ => e - j) ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
      · intro j₁ hj₁ j₂ hj₂ heq; simp only [Finset.mem_range] at hj₁ hj₂; omega
      · intro j hj; simp only [Finset.mem_range] at hj
        exact ⟨e - j, Finset.mem_range.mpr (by omega), by omega⟩
      · intro _ _; rfl
    by_cases hp2 : p = 2
    · subst hp2
      have hχ2 : χ 2 = 0 := by
        dsimp [χ, chiRe]
        have h := quadChar_apply_nat hm_pos 2
        simpa using congrArg Complex.re h
      have ha2 : a (2 ^ e) = 1 := by
        rw [ha_pe, hχ2, Finset.sum_eq_single 0]
        · simp
        · intro j _ hj0; exact zero_pow hj0
        · intro h0; exact absurd (Finset.mem_range.mpr (Nat.zero_lt_succ e)) h0
      let w : Zsqrtd (m : ℤ) := ⟨4 * (y : ℤ), 1⟩
      have hwn : w.norm = 2 := by
        have hmZ : (m : ℤ) = 16 * (y : ℤ) ^ 2 - 2 := by
          have : (m : ℤ) + 2 = (4 * (y : ℤ)) ^ 2 := by exact_mod_cast hm
          linarith
        simp [w, Zsqrtd.norm_def, hmZ]; ring
      refine ⟨{w ^ e}, ?_, ?_, ?_⟩
      · simp [ha2]
      · intro α hα; simp only [Finset.mem_singleton] at hα; rw [hα]
        have : (w ^ e).norm = 2 ^ e := by rw [zsqrtd_norm_pow, hwn]
        rw [this]; simp
      · intro α hα β hβ _; simp only [Finset.mem_singleton] at hα hβ; rw [hα, hβ]
    · by_cases hpm : p ∣ m
      · have hχp : χ p = 0 := by
          dsimp [χ, chiRe]; rw [quadChar_apply_nat]
          have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
          simp only [hp_odd, Nat.one_ne_zero, ↓reduceIte]
          let _ : NeZero p := ⟨hp.ne_zero⟩
          have hgc : (m : ℤ).gcd p ≠ 1 := by
            rw [Int.gcd_natCast_natCast, Nat.gcd_eq_right hpm]; exact hp.ne_one
          rw [jacobiSym.eq_zero_iff_not_coprime.mpr hgc]; simp
        have hap : a (p ^ e) = 1 := by
          rw [ha_pe, hχp, Finset.sum_eq_single 0]
          · simp
          · intro j _ hj0; exact zero_pow hj0
          · intro h0; exact absurd (Finset.mem_range.mpr (Nat.zero_lt_succ e)) h0
        obtain ⟨x, k, hxk⟩ := zsqrtd_norm_eq_prime_of_pid hpid hp (a := 0) (by
          simpa using Int.ofNat_dvd.mpr hpm)
        let w : Zsqrtd (m : ℤ) := ⟨x, k⟩
        have hwn : w.norm.natAbs = p := by
          have hd : w.norm = x ^ 2 - (m : ℤ) * k ^ 2 := by simp [w, Zsqrtd.norm_def]; ring
          have habs : |w.norm| = (p : ℤ) := by rw [hd]; exact hxk
          have := congrArg Int.natAbs habs
          simpa [Int.natAbs_abs] using this
        refine ⟨{w ^ e}, ?_, ?_, ?_⟩
        · simp [hap]
        · intro α hα; simp only [Finset.mem_singleton] at hα
          rw [hα, zsqrtd_norm_pow, Int.natAbs_pow, hwn]
        · intro α hα β hβ _; simp only [Finset.mem_singleton] at hα hβ; rw [hα, hβ]
      · have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
        have hcop : (m : ℤ).gcd p = 1 := by
          rw [Int.gcd_natCast_natCast, Nat.gcd_comm]
          exact (hp.coprime_iff_not_dvd.mpr hpm).gcd_eq_one
        rcases jacobiSym.eq_one_or_neg_one hcop with hJ1 | hJm1
        · have hχp : χ p = 1 := by
            dsimp [χ, chiRe]; rw [quadChar_apply_nat]
            simp [hp_odd, hJ1]
          have hap : a (p ^ e) = (e + 1 : ℕ) := by
            rw [ha_pe, hχp]; simp
          obtain ⟨w₁, w₂, h1n, h2n, hirr1, hirr2, hna⟩ :=
            zsqrtd_split_primes_of_pid hm1 hsq hpid hp hp2 hpm hJ1
          have hprime1 : Prime w₁ := hirr1.prime
          have hne_assoc_j : ∀ j₁ j₂ : ℕ, j₁ ≤ e → j₂ ≤ e →
              Associated (w₁ ^ j₁ * w₂ ^ (e - j₁)) (w₁ ^ j₂ * w₂ ^ (e - j₂)) → j₁ = j₂ := by
            intro j₁ j₂ hj₁ hj₂ hass
            have hle_imp : ∀ u v : ℕ, u ≤ e → v ≤ e → u < v →
                ¬ Associated (w₁ ^ u * w₂ ^ (e - u)) (w₁ ^ v * w₂ ^ (e - v)) := by
              intro u v hue hve huv hass'
              obtain ⟨unit, hu⟩ := hass'
              have hfac1 : w₁ ^ u * w₂ ^ (e - u) = (w₁ ^ u * w₂ ^ (e - v)) * w₂ ^ (v - u) := by
                rw [mul_assoc, ← pow_add, show e - v + (v - u) = e - u by omega]
              have hfac2 : w₁ ^ v * w₂ ^ (e - v) = (w₁ ^ u * w₂ ^ (e - v)) * w₁ ^ (v - u) := by
                rw [mul_right_comm, ← pow_add, show u + (v - u) = v by omega]
              have hcancel : w₂ ^ (v - u) * (unit : Zsqrtd (m : ℤ)) = w₁ ^ (v - u) := by
                have hne0 : w₁ ^ u * w₂ ^ (e - v) ≠ 0 := by
                  apply mul_ne_zero <;> exact pow_ne_zero _ (by
                    intro h0; first | exact hirr1.ne_zero h0 | exact hirr2.ne_zero h0)
                apply mul_left_cancel₀ hne0
                calc (w₁ ^ u * w₂ ^ (e - v)) * (w₂ ^ (v - u) * (unit : Zsqrtd (m : ℤ)))
                    = (w₁ ^ u * w₂ ^ (e - u)) * (unit : Zsqrtd (m : ℤ)) := by rw [← mul_assoc, hfac1]
                  _ = w₁ ^ v * w₂ ^ (e - v) := hu
                  _ = (w₁ ^ u * w₂ ^ (e - v)) * w₁ ^ (v - u) := hfac2
              have hdvd_pow : w₁ ∣ w₂ ^ (v - u) := by
                have h1 : w₁ ∣ w₁ ^ (v - u) := dvd_pow_self w₁ (by omega)
                rw [← hcancel] at h1
                exact (Units.dvd_mul_right.mp h1)
              have hdvd12 : w₁ ∣ w₂ := hprime1.dvd_of_dvd_pow hdvd_pow
              obtain ⟨c, hc⟩ := hdvd12
              rcases hirr2.isUnit_or_isUnit hc with hu1 | huc
              · exact hirr1.not_isUnit hu1
              · exact hna (associated_of_dvd_dvd ⟨c, hc⟩ (by
                  obtain ⟨v', hv'⟩ := huc
                  refine ⟨(v'⁻¹ : (Zsqrtd (m : ℤ))ˣ), ?_⟩
                  rw [hc, ← hv', mul_assoc, Units.mul_inv, mul_one]))
            rcases lt_trichotomy j₁ j₂ with hlt | heq | hgt
            · exact absurd hass (hle_imp j₁ j₂ hj₁ hj₂ hlt)
            · exact heq
            · exact absurd hass.symm (hle_imp j₂ j₁ hj₂ hj₁ hgt)
          let S := (range (e + 1)).image (fun j => w₁ ^ j * w₂ ^ (e - j))
          have hinj : Set.InjOn (fun j => w₁ ^ j * w₂ ^ (e - j)) (range (e + 1) : Set ℕ) := by
            intro j₁ hj₁ j₂ hj₂ heq
            simp only [Finset.mem_coe, Finset.mem_range] at hj₁ hj₂
            dsimp only at heq
            exact hne_assoc_j j₁ j₂ (by omega) (by omega) (by rw [heq])
          refine ⟨S, ?_, ?_, ?_⟩
          · rw [Finset.card_image_of_injOn hinj, Finset.card_range, hap]
          · intro α hα
            rw [Finset.mem_image] at hα
            obtain ⟨j, hj, rfl⟩ := hα
            simp only [Finset.mem_range] at hj
            rw [Zsqrtd.norm_mul, zsqrtd_norm_pow, zsqrtd_norm_pow, Int.natAbs_mul,
              Int.natAbs_pow, Int.natAbs_pow, h1n, h2n, ← pow_add, Nat.add_sub_of_le (by omega)]
          · intro α hα β hβ hass
            rw [Finset.mem_image] at hα hβ
            obtain ⟨j₁, hj₁, rfl⟩ := hα
            obtain ⟨j₂, hj₂, rfl⟩ := hβ
            simp only [Finset.mem_range] at hj₁ hj₂
            have := hne_assoc_j j₁ j₂ (by omega) (by omega) hass
            rw [this]
        · have hχp : χ p = -1 := by
            dsimp [χ, chiRe]; rw [quadChar_apply_nat]
            simp [hp_odd, hJm1]
          rcases Nat.even_or_odd' e with ⟨k, rfl | rfl⟩
          · have hap : a (p ^ (2 * k)) = 1 := by
              rw [ha_pe, hχp]
              clear hχp hcop hJm1 hpm ha_pe
              induction k with
              | zero => simp
              | succ t iht =>
                have h1 : 2 * (t + 1) + 1 = (2 * t + 1) + 2 := by omega
                rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, iht]
                have hodd : Odd (2 * t + 1) := ⟨t, by omega⟩
                have hev : Even (2 * t + 1 + 1) := ⟨t + 1, by omega⟩
                rw [hodd.neg_one_pow, hev.neg_one_pow]; ring
            refine ⟨{(p : Zsqrtd (m : ℤ)) ^ k}, ?_, ?_, ?_⟩
            · simp [hap]
            · intro α hα; simp only [Finset.mem_singleton] at hα; rw [hα]
              rw [zsqrtd_norm_pow, Zsqrtd.norm_natCast, Int.natAbs_pow, Int.natAbs_mul,
                Int.natAbs_natCast, ← sq, ← pow_mul]
            · intro α hα β hβ _; simp only [Finset.mem_singleton] at hα hβ; rw [hα, hβ]
          · have hap : a (p ^ (2 * k + 1)) = 0 := by
              rw [ha_pe, hχp]
              clear hχp hcop hJm1 hpm ha_pe
              induction k with
              | zero => simp
              | succ t iht =>
                have h1 : 2 * (t + 1) + 1 + 1 = (2 * t + 1 + 1) + 2 := by omega
                rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, iht]
                have hev : Even (2 * t + 1 + 1) := ⟨t + 1, by omega⟩
                have hodd : Odd (2 * t + 1 + 1 + 1) := ⟨t + 1, by omega⟩
                rw [hev.neg_one_pow, hodd.neg_one_pow]; ring
            refine ⟨∅, by simp [hap], by simp, by simp⟩
  have hmul_step : ∀ {n₁ n₂ : ℕ}, 1 ≤ n₁ → 1 ≤ n₂ → Nat.Coprime n₁ n₂ →
      ∀ S₁ S₂ : Finset (Zsqrtd (m : ℤ)),
        (S₁.card : ℝ) = a n₁ → (S₂.card : ℝ) = a n₂ →
        (∀ α ∈ S₁, α.norm.natAbs = n₁) → (∀ β ∈ S₂, β.norm.natAbs = n₂) →
        (∀ α ∈ S₁, ∀ α' ∈ S₁, Associated α α' → α = α') →
        (∀ β ∈ S₂, ∀ β' ∈ S₂, Associated β β' → β = β') →
        ∃ S : Finset (Zsqrtd (m : ℤ)),
          (S.card : ℝ) = a (n₁ * n₂) ∧
          (∀ γ ∈ S, γ.norm.natAbs = n₁ * n₂) ∧
          (∀ γ ∈ S, ∀ γ' ∈ S, Associated γ γ' → γ = γ') := by
    intro n₁ n₂ hn₁ hn₂ hcop S₁ S₂ hc1 hc2 hnorm1 hnorm2 hna1 hna2
    have hcop_ideal : ∀ α β : Zsqrtd (m : ℤ), α.norm.natAbs = n₁ → β.norm.natAbs = n₂ →
        ∃ r s : Zsqrtd (m : ℤ), r * α + s * β = 1 := by
      intro α β hα hβ
      let I : Ideal (Zsqrtd (m : ℤ)) := Ideal.span {α, β}
      obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal I).principal
      have hα_mem : α ∈ I := Ideal.subset_span (by simp)
      have hβ_mem : β ∈ I := Ideal.subset_span (by simp)
      rw [hg, Ideal.mem_span_singleton] at hα_mem hβ_mem
      obtain ⟨q₁, hq₁⟩ := hα_mem
      obtain ⟨q₂, hq₂⟩ := hβ_mem
      have hd1 : g.norm.natAbs ∣ n₁ := by
        refine ⟨q₁.norm.natAbs, ?_⟩
        have := congrArg (fun z : Zsqrtd (m : ℤ) => z.norm.natAbs) hq₁
        simpa [Zsqrtd.norm_mul, Int.natAbs_mul, hα] using this
      have hd2 : g.norm.natAbs ∣ n₂ := by
        refine ⟨q₂.norm.natAbs, ?_⟩
        have := congrArg (fun z : Zsqrtd (m : ℤ) => z.norm.natAbs) hq₂
        simpa [Zsqrtd.norm_mul, Int.natAbs_mul, hβ] using this
      have hg1 : g.norm.natAbs = 1 :=
        Nat.dvd_one.mp ((Nat.dvd_gcd hd1 hd2).trans (by rw [hcop.gcd_eq_one]))
      have hgu : IsUnit g := (Zsqrtd.isUnit_iff_norm_isUnit g).mpr (Int.isUnit_iff_natAbs_eq.mpr hg1)
      have h1_mem : (1 : Zsqrtd (m : ℤ)) ∈ I := by rw [hg, Ideal.mem_span_singleton]; exact hgu.dvd
      rw [Ideal.mem_span_pair] at h1_mem
      exact h1_mem
    have hpair_assoc : ∀ α₁ ∈ S₁, ∀ β₁ ∈ S₂, ∀ α₂ ∈ S₁, ∀ β₂ ∈ S₂,
        Associated (α₁ * β₁) (α₂ * β₂) → α₁ = α₂ ∧ β₁ = β₂ := by
      intro α₁ hα₁ β₁ hβ₁ α₂ hα₂ β₂ hβ₂ hass
      obtain ⟨u, hu⟩ := hass
      obtain ⟨r₁, s₁, hrs₁⟩ := hcop_ideal α₁ β₂ (hnorm1 α₁ hα₁) (hnorm2 β₂ hβ₂)
      have hdvd12 : α₁ ∣ α₂ := by
        refine ⟨r₁ * α₂ + s₁ * β₁ * (u : Zsqrtd (m : ℤ)), ?_⟩
        calc α₂ = (r₁ * α₁ + s₁ * β₂) * α₂ := by rw [hrs₁, one_mul]
          _ = r₁ * α₁ * α₂ + s₁ * (α₂ * β₂) := by ring
          _ = r₁ * α₁ * α₂ + s₁ * (α₁ * β₁ * (u : Zsqrtd (m : ℤ))) := by rw [hu]
          _ = α₁ * (r₁ * α₂ + s₁ * β₁ * (u : Zsqrtd (m : ℤ))) := by ring
      obtain ⟨r₂, s₂, hrs₂⟩ := hcop_ideal α₂ β₁ (hnorm1 α₂ hα₂) (hnorm2 β₁ hβ₁)
      have hdvd21 : α₂ ∣ α₁ := by
        refine ⟨r₂ * α₁ + s₂ * β₂ * ((u⁻¹ : (Zsqrtd (m : ℤ))ˣ) : Zsqrtd (m : ℤ)), ?_⟩
        have hu' : α₁ * β₁ = α₂ * β₂ * ((u⁻¹ : (Zsqrtd (m : ℤ))ˣ) : Zsqrtd (m : ℤ)) := by
          calc α₁ * β₁ = (α₁ * β₁ * (u : Zsqrtd (m : ℤ))) *
                ((u⁻¹ : (Zsqrtd (m : ℤ))ˣ) : Zsqrtd (m : ℤ)) := by
                rw [mul_assoc, Units.mul_inv, mul_one]
            _ = α₂ * β₂ * ((u⁻¹ : (Zsqrtd (m : ℤ))ˣ) : Zsqrtd (m : ℤ)) := by rw [hu]
        calc α₁ = (r₂ * α₂ + s₂ * β₁) * α₁ := by rw [hrs₂, one_mul]
          _ = r₂ * α₂ * α₁ + s₂ * (α₁ * β₁) := by ring
          _ = r₂ * α₂ * α₁ + s₂ * (α₂ * β₂ * ((u⁻¹ : (Zsqrtd (m : ℤ))ˣ) : Zsqrtd (m : ℤ))) := by rw [hu']
          _ = α₂ * (r₂ * α₁ + s₂ * β₂ * ((u⁻¹ : (Zsqrtd (m : ℤ))ˣ) : Zsqrtd (m : ℤ))) := by ring
      have hα_eq : α₁ = α₂ := hna1 α₁ hα₁ α₂ hα₂ (associated_of_dvd_dvd hdvd12 hdvd21)
      subst hα_eq
      have hα_ne0 : α₁ ≠ 0 := by
        intro h0; have := hnorm1 α₁ hα₁; rw [h0] at this; simp at this; omega
      have hβ_u : β₁ * (u : Zsqrtd (m : ℤ)) = β₂ := by
        apply mul_left_cancel₀ hα_ne0
        simpa [mul_assoc] using hu
      exact ⟨rfl, hna2 β₁ hβ₁ β₂ hβ₂ ⟨u, hβ_u⟩⟩
    let S := (S₁ ×ˢ S₂).image (fun p => p.1 * p.2)
    have hinj : Set.InjOn (fun p : Zsqrtd (m : ℤ) × Zsqrtd (m : ℤ) => p.1 * p.2)
        ((S₁ ×ˢ S₂ : Finset _) : Set _) := by
      intro ⟨α₁, β₁⟩ hp₁ ⟨α₂, β₂⟩ hp₂ heq
      simp only [Finset.mem_coe, Finset.mem_product] at hp₁ hp₂
      obtain ⟨h1, h2⟩ := hpair_assoc α₁ hp₁.1 β₁ hp₁.2 α₂ hp₂.1 β₂ hp₂.2 (by dsimp only at heq; rw [heq])
      ext <;> simp [h1, h2]
    refine ⟨S, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injOn hinj, Finset.card_product, Nat.cast_mul, hc1, hc2,
        ha_mult.2 n₁ n₂ hcop]
    · intro γ hγ
      rw [Finset.mem_image] at hγ
      obtain ⟨⟨α, β⟩, hp, rfl⟩ := hγ
      rw [Finset.mem_product] at hp
      rw [Zsqrtd.norm_mul, Int.natAbs_mul, hnorm1 α hp.1, hnorm2 β hp.2]
    · intro γ hγ γ' hγ' hass
      rw [Finset.mem_image] at hγ hγ'
      obtain ⟨⟨α₁, β₁⟩, hp₁, rfl⟩ := hγ
      obtain ⟨⟨α₂, β₂⟩, hp₂, rfl⟩ := hγ'
      rw [Finset.mem_product] at hp₁ hp₂
      obtain ⟨h1, h2⟩ := hpair_assoc α₁ hp₁.1 β₁ hp₁.2 α₂ hp₂.1 β₂ hp₂.2 hass
      rw [h1, h2]
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    rcases eq_or_lt_of_le hn with rfl | hn1
    · refine ⟨{1}, ?_, by simp, by intro α hα β hβ _; simp at hα hβ; rw [hα, hβ]⟩
      have ha1 : a 1 = 1 := ha_mult.1
      simpa [a] using ha1.symm
    · let p := n.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      let e := n.factorization p
      have he_pos : 1 ≤ e :=
        Nat.pos_of_ne_zero ((Finsupp.mem_support_iff).mp
          (Nat.mem_primeFactors.mpr ⟨hp, Nat.minFac_dvd n, by omega⟩))
      have hpe_dvd : p ^ e ∣ n := Nat.ordProj_dvd n p
      let r := n / p ^ e
      have hmul : p ^ e * r = n := Nat.mul_div_cancel' hpe_dvd
      have hcop : Nat.Coprime (p ^ e) r := by
        have hnd : ¬ p ∣ r := Nat.not_dvd_ordCompl hp (show n ≠ 0 by omega)
        exact (hp.coprime_iff_not_dvd.mpr hnd).pow_left e
      have hr_pos : 1 ≤ r := by
        by_contra h0; push Not at h0
        have hr0 : r = 0 := Nat.lt_one_iff.mp h0
        rw [hr0, mul_zero] at hmul; omega
      have hr_lt : r < n := by
        have hpe1 : 1 < p ^ e := one_lt_pow₀ hp.one_lt (by omega)
        have h1 : 1 * r < p ^ e * r := Nat.mul_lt_mul_of_pos_right hpe1 hr_pos
        rw [one_mul, hmul] at h1
        exact h1
      obtain ⟨S₁, hc1, hn1, hna1⟩ := hpp p e hp
      obtain ⟨S₂, hc2, hn2, hna2⟩ := ih r hr_lt hr_pos
      obtain ⟨S, hc, hnorm, hna⟩ :=
        hmul_step (Nat.one_le_pow e p hp.pos) hr_pos hcop S₁ S₂ hc1 hc2 hn1 hn2 hna1 hna2
      rw [hmul] at hc hnorm
      exact ⟨S, hc, hnorm, hna⟩

/- 1D hyperbolic-sector integral and lattice-point upper bound -/

private lemma antitone_sqrt_sub_linear {X c : ℝ} (hX : 0 ≤ X) (hc : 1 ≤ c) :
    AntitoneOn (fun t : ℝ => Real.sqrt (X + t ^ 2) - c * t) (Set.Ici 0) := by
  intro s hs t ht hst
  simp only [Set.mem_Ici] at hs ht
  dsimp only
  have h1 : Real.sqrt (X + t ^ 2) - Real.sqrt (X + s ^ 2) ≤ t - s := by
    rcases eq_or_lt_of_le hst with rfl | hlt
    · simp
    · have hsum_pos : 0 < t + s := by linarith
      have ht_le : t ≤ Real.sqrt (X + t ^ 2) := by
        calc t = Real.sqrt (t ^ 2) := (Real.sqrt_sq ht).symm
          _ ≤ Real.sqrt (X + t ^ 2) := Real.sqrt_le_sqrt (by linarith)
      have hs_le : s ≤ Real.sqrt (X + s ^ 2) := by
        calc s = Real.sqrt (s ^ 2) := (Real.sqrt_sq hs).symm
          _ ≤ Real.sqrt (X + s ^ 2) := Real.sqrt_le_sqrt (by linarith)
      have hge : t + s ≤ Real.sqrt (X + t ^ 2) + Real.sqrt (X + s ^ 2) := by linarith
      have hdiff_nn : 0 ≤ Real.sqrt (X + t ^ 2) - Real.sqrt (X + s ^ 2) :=
        sub_nonneg.mpr (Real.sqrt_le_sqrt (by nlinarith))
      have hprod : (Real.sqrt (X + t ^ 2) - Real.sqrt (X + s ^ 2)) *
          (Real.sqrt (X + t ^ 2) + Real.sqrt (X + s ^ 2)) = t ^ 2 - s ^ 2 := by
        have hsq1 : Real.sqrt (X + t ^ 2) ^ 2 = X + t ^ 2 := Real.sq_sqrt (by positivity)
        have hsq2 : Real.sqrt (X + s ^ 2) ^ 2 = X + s ^ 2 := Real.sq_sqrt (by positivity)
        nlinarith
      have hmul_le : (Real.sqrt (X + t ^ 2) - Real.sqrt (X + s ^ 2)) * (t + s) ≤
          (t - s) * (t + s) := by
        calc (Real.sqrt (X + t ^ 2) - Real.sqrt (X + s ^ 2)) * (t + s)
            ≤ (Real.sqrt (X + t ^ 2) - Real.sqrt (X + s ^ 2)) *
                (Real.sqrt (X + t ^ 2) + Real.sqrt (X + s ^ 2)) := by gcongr
          _ = t ^ 2 - s ^ 2 := hprod
          _ = (t - s) * (t + s) := by ring
      exact le_of_mul_le_mul_right hmul_le hsum_pos
  have h2 : t - s ≤ c * (t - s) := by nlinarith
  linarith

private lemma hyperbolic_sector_integral {X ε : ℝ} (hX : 0 < X) (hε : 1 < ε) :
    let c := (ε ^ 2 + 1) / (ε ^ 2 - 1)
    let T := Real.sqrt X * (ε ^ 2 - 1) / (2 * ε)
    ∫ t in (0 : ℝ)..T, (Real.sqrt (X + t ^ 2) - c * t) = X / 2 * Real.log ε := by
  intro c T
  have hε2 : 0 < ε ^ 2 - 1 := by nlinarith
  have hT_pos : 0 < T := by dsimp [T]; positivity
  let F : ℝ → ℝ := fun t =>
    (1 / 2) * t * Real.sqrt (X + t ^ 2) + (X / 2) * Real.log (t + Real.sqrt (X + t ^ 2)) -
      (1 / 2) * c * t ^ 2
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt F (Real.sqrt (X + t ^ 2) - c * t) t := by
    intro t ht
    have hXt_pos : 0 < X + t ^ 2 := by positivity
    have hsqrt_pos : 0 < Real.sqrt (X + t ^ 2) := Real.sqrt_pos.mpr hXt_pos
    have harg_pos : 0 < t + Real.sqrt (X + t ^ 2) := by
      have hgt : |t| < Real.sqrt (X + t ^ 2) := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg t) (by linarith)
      linarith [neg_abs_le t]
    have hd_sq : HasDerivAt (fun x : ℝ => X + x ^ 2) (2 * t) t := by
      have h1 := (hasDerivAt_const t X).add (hasDerivAt_pow 2 t)
      have h2 : (0 : ℝ) + ((2 : ℕ) : ℝ) * t ^ (2 - 1) = 2 * t := by norm_num
      rw [h2] at h1
      exact h1
    have hd_sqrt : HasDerivAt (fun x : ℝ => Real.sqrt (X + x ^ 2))
        (t / Real.sqrt (X + t ^ 2)) t := by
      have h1 := hd_sq.sqrt hXt_pos.ne'
      have h2 : 2 * t / (2 * Real.sqrt (X + t ^ 2)) = t / Real.sqrt (X + t ^ 2) := by field_simp
      rwa [h2] at h1
    have hd_term1 : HasDerivAt (fun x : ℝ => (1 / 2) * x * Real.sqrt (X + x ^ 2))
        ((1 / 2) * Real.sqrt (X + t ^ 2) + (1 / 2) * t * (t / Real.sqrt (X + t ^ 2))) t := by
      have h1 := ((hasDerivAt_id t).const_mul (1 / 2)).mul hd_sqrt
      have h2 : (1 / 2) * 1 * Real.sqrt (X + t ^ 2) + (1 / 2) * t * (t / Real.sqrt (X + t ^ 2)) =
          (1 / 2) * Real.sqrt (X + t ^ 2) + (1 / 2) * t * (t / Real.sqrt (X + t ^ 2)) := by ring
      simpa only [id_eq] using (h2 ▸ h1)
    have hd_log : HasDerivAt (fun x : ℝ => Real.log (x + Real.sqrt (X + x ^ 2)))
        (1 / Real.sqrt (X + t ^ 2)) t := by
      have hsum_d : HasDerivAt (fun x : ℝ => x + Real.sqrt (X + x ^ 2))
          (1 + t / Real.sqrt (X + t ^ 2)) t := (hasDerivAt_id t).add hd_sqrt
      have h1 := hsum_d.log harg_pos.ne'
      have h2 : (1 + t / Real.sqrt (X + t ^ 2)) / (t + Real.sqrt (X + t ^ 2)) =
          1 / Real.sqrt (X + t ^ 2) := by
        have hne1 : t + Real.sqrt (X + t ^ 2) ≠ 0 := harg_pos.ne'
        have hne2 : Real.sqrt (X + t ^ 2) ≠ 0 := hsqrt_pos.ne'
        field_simp; ring
      rwa [h2] at h1
    have hd_term2 : HasDerivAt (fun x : ℝ => (X / 2) * Real.log (x + Real.sqrt (X + x ^ 2)))
        ((X / 2) * (1 / Real.sqrt (X + t ^ 2))) t :=
      hd_log.const_mul (X / 2)
    have hd_term3 : HasDerivAt (fun x : ℝ => (1 / 2) * c * x ^ 2) (c * t) t := by
      have h1 := (hasDerivAt_pow 2 t).const_mul ((1 / 2) * c)
      have h2 : (1 / 2) * c * (((2 : ℕ) : ℝ) * t ^ (2 - 1)) = c * t := by norm_num; ring
      rwa [h2] at h1
    have hd_all := (hd_term1.add hd_term2).sub hd_term3
    have hval : (1 / 2) * Real.sqrt (X + t ^ 2) + (1 / 2) * t * (t / Real.sqrt (X + t ^ 2)) +
        (X / 2) * (1 / Real.sqrt (X + t ^ 2)) - c * t = Real.sqrt (X + t ^ 2) - c * t := by
      have hsq : Real.sqrt (X + t ^ 2) ^ 2 = X + t ^ 2 := Real.sq_sqrt hXt_pos.le
      have hne : Real.sqrt (X + t ^ 2) ≠ 0 := hsqrt_pos.ne'
      field_simp
      linarith [hsq]
    rwa [hval] at hd_all
  have hcont : ContinuousOn (fun t : ℝ => Real.sqrt (X + t ^ 2) - c * t) (Set.uIcc 0 T) := by
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have hsqrtT : Real.sqrt (X + T ^ 2) = Real.sqrt X * (ε ^ 2 + 1) / (2 * ε) := by
    have hval : X + T ^ 2 = (Real.sqrt X * (ε ^ 2 + 1) / (2 * ε)) ^ 2 := by
      dsimp [T]
      field_simp
      rw [Real.sq_sqrt hX.le]
      ring
    rw [hval, Real.sqrt_sq (by positivity)]
  have hcancel : (1 / 2) * T * Real.sqrt (X + T ^ 2) - (1 / 2) * c * T ^ 2 = 0 := by
    rw [hsqrtT]; dsimp [T, c]; field_simp; ring
  have hlogT : T + Real.sqrt (X + T ^ 2) = ε * Real.sqrt X := by
    rw [hsqrtT]; dsimp [T]; field_simp; ring
  have hF0 : F 0 = (X / 2) * Real.log (Real.sqrt X) := by
    dsimp [F]; simp
  have hFT : F T = (X / 2) * Real.log (ε * Real.sqrt X) := by
    dsimp [F]
    rw [hlogT]
    linarith [hcancel]
  rw [hFT, hF0, Real.log_mul (by positivity) (Real.sqrt_pos.mpr hX).ne']
  ring

private lemma finset_Ioc_int_card_le (a b : ℝ) (hab : a ≤ b) :
    ((Finset.Ioc ⌊a⌋ ⌊b⌋).card : ℝ) ≤ (b - a) + 1 := by
  have hcard : (Finset.Ioc ⌊a⌋ ⌊b⌋).card = (⌊b⌋ - ⌊a⌋).toNat := Int.card_Ioc ⌊a⌋ ⌊b⌋
  rw [hcard]
  have hle : ⌊a⌋ ≤ ⌊b⌋ := Int.floor_le_floor hab
  have hsub : ((⌊b⌋ - ⌊a⌋).toNat : ℝ) = (⌊b⌋ : ℝ) - (⌊a⌋ : ℝ) := by
    have h1 : ((⌊b⌋ - ⌊a⌋).toNat : ℤ) = ⌊b⌋ - ⌊a⌋ := Int.toNat_of_nonneg (by omega)
    exact_mod_cast h1
  rw [hsub]
  linarith [Int.floor_le b, Int.lt_floor_add_one a]

private lemma sum_antitone_scaled_le_integral {f : ℝ → ℝ} {T h : ℝ} (_hT : 0 < T) (hh : 0 < h)
    (hf_anti : AntitoneOn f (Set.Ici 0)) (hf_cont : ContinuousOn f (Set.Icc 0 T))
    (hf_nn : ∀ t ∈ Set.Icc 0 T, 0 ≤ f t) :
    ∀ K : ℕ, (K : ℝ) * h ≤ T →
      ∑ k ∈ Icc 1 K, f ((k : ℝ) * h) ≤ (1 / h) * ∫ t in (0 : ℝ)..T, f t := by
  intro K hKh
  have hstep : ∀ k ∈ Icc 1 K,
      h * f ((k : ℝ) * h) ≤ ∫ t in (((k - 1 : ℕ) : ℝ) * h)..((k : ℝ) * h), f t := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have ha_le_b : ((k - 1 : ℕ) : ℝ) * h ≤ (k : ℝ) * h := by
      have : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : k - 1 ≤ k)
      nlinarith
    have hsub : Set.uIcc (((k - 1 : ℕ) : ℝ) * h) ((k : ℝ) * h) ⊆ Set.Icc 0 T := by
      rw [Set.uIcc_of_le ha_le_b]
      intro t ht
      refine ⟨le_trans (by positivity) ht.1, le_trans ht.2 ?_⟩
      have : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast hk.2
      nlinarith
    have hint : IntervalIntegrable f MeasureTheory.volume (((k - 1 : ℕ) : ℝ) * h) ((k : ℝ) * h) :=
      (hf_cont.mono hsub).intervalIntegrable
    have hconst : h * f ((k : ℝ) * h) =
        ∫ _ in (((k - 1 : ℕ) : ℝ) * h)..((k : ℝ) * h), f ((k : ℝ) * h) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      have : (k : ℝ) * h - ((k - 1 : ℕ) : ℝ) * h = h := by
        rw [Nat.cast_sub hk.1, Nat.cast_one]; ring
      rw [this]
    rw [hconst]
    refine intervalIntegral.integral_mono_on ha_le_b intervalIntegrable_const hint ?_
    intro t ht
    exact hf_anti (le_trans (by positivity) ht.1) (by exact mul_nonneg (Nat.cast_nonneg k) hh.le) ht.2
  have hsum_int : ∀ M : ℕ, (M : ℝ) * h ≤ T →
      ∑ k ∈ Icc 1 M, ∫ t in (((k - 1 : ℕ) : ℝ) * h)..((k : ℝ) * h), f t =
        ∫ t in (0 : ℝ)..((M : ℝ) * h), f t := by
    intro M
    induction M with
    | zero => intro _; simp
    | succ M ih =>
      intro hMh
      have hMh' : (M : ℝ) * h ≤ T := by
        have : (M : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ M
        nlinarith
      rw [Finset.sum_Icc_succ_top (by omega), ih hMh']
      have h1 : (((M + 1 - 1 : ℕ) : ℝ) * h) = (M : ℝ) * h := by simp
      rw [h1]
      have hsub1 : Set.uIcc (0 : ℝ) ((M : ℝ) * h) ⊆ Set.Icc 0 T := by
        rw [Set.uIcc_of_le (by positivity)]; intro t ht; exact ⟨ht.1, le_trans ht.2 hMh'⟩
      have hsub2 : Set.uIcc ((M : ℝ) * h) (((M + 1 : ℕ) : ℝ) * h) ⊆ Set.Icc 0 T := by
        have hle : (M : ℝ) * h ≤ ((M + 1 : ℕ) : ℝ) * h := by
          have : (M : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ M
          nlinarith
        rw [Set.uIcc_of_le hle]
        intro t ht; exact ⟨le_trans (by positivity) ht.1, le_trans ht.2 hMh⟩
      exact intervalIntegral.integral_add_adjacent_intervals
        ((hf_cont.mono hsub1).intervalIntegrable)
        ((hf_cont.mono hsub2).intervalIntegrable)
  have htail : ∫ t in (0 : ℝ)..((K : ℝ) * h), f t ≤ ∫ t in (0 : ℝ)..T, f t := by
    have hsub1 : Set.uIcc (0 : ℝ) ((K : ℝ) * h) ⊆ Set.Icc 0 T := by
      rw [Set.uIcc_of_le (by positivity)]; intro t ht; exact ⟨ht.1, le_trans ht.2 hKh⟩
    have hsub2 : Set.uIcc ((K : ℝ) * h) T ⊆ Set.Icc 0 T := by
      rw [Set.uIcc_of_le hKh]; intro t ht; exact ⟨le_trans (by positivity) ht.1, ht.2⟩
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      ((hf_cont.mono hsub1).intervalIntegrable (μ := MeasureTheory.volume))
      ((hf_cont.mono hsub2).intervalIntegrable (μ := MeasureTheory.volume))
    have hnn : 0 ≤ ∫ t in ((K : ℝ) * h)..T, f t :=
      intervalIntegral.integral_nonneg hKh (fun t ht => hf_nn t ⟨le_trans (by positivity) ht.1, ht.2⟩)
    linarith
  have hmul : h * ∑ k ∈ Icc 1 K, f ((k : ℝ) * h) ≤ ∫ t in (0 : ℝ)..T, f t := by
    calc h * ∑ k ∈ Icc 1 K, f ((k : ℝ) * h)
        = ∑ k ∈ Icc 1 K, h * f ((k : ℝ) * h) := Finset.mul_sum ..
      _ ≤ ∑ k ∈ Icc 1 K, ∫ t in (((k - 1 : ℕ) : ℝ) * h)..((k : ℝ) * h), f t :=
          Finset.sum_le_sum hstep
      _ = ∫ t in (0 : ℝ)..((K : ℝ) * h), f t := hsum_int K hKh
      _ ≤ ∫ t in (0 : ℝ)..T, f t := htail
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hh, mul_comm]
  exact hmul

private noncomputable def wedgeSet (m X : ℕ) (ε : ℝ) : Finset (ℤ × ℤ) :=
  let c : ℝ := (ε ^ 2 + 1) / (ε ^ 2 - 1)
  let T : ℝ := Real.sqrt (X : ℝ) * (ε ^ 2 - 1) / (2 * ε)
  let K_pos : ℕ := Nat.floor (T / Real.sqrt (m : ℝ))
  let K_neg : ℕ := Nat.floor T
  let S_pos : Finset (ℤ × ℤ) :=
    (Icc 0 K_pos).biUnion fun k =>
      (Finset.Ioc ⌊c * ((k : ℝ) * Real.sqrt (m : ℝ))⌋
        ⌊Real.sqrt ((X : ℝ) + ((k : ℝ) * Real.sqrt (m : ℝ)) ^ 2)⌋).image (fun x => (x, (k : ℤ)))
  let S_neg : Finset (ℤ × ℤ) :=
    (Icc 0 K_neg).biUnion fun x =>
      (Finset.Ioc ⌊(c * (x : ℝ)) / Real.sqrt (m : ℝ)⌋
        ⌊Real.sqrt ((X : ℝ) + (x : ℝ) ^ 2) / Real.sqrt (m : ℝ)⌋).image (fun k => ((x : ℤ), k))
  S_pos ∪ S_neg

private lemma wedgeSet_card_le {m X : ℕ} (hm : 1 ≤ m) (hX : 1 ≤ X) {ε : ℝ} (hε : 1 < ε) :
    ((wedgeSet m X ε).card : ℝ) ≤
      (2 * Real.log ε / Real.sqrt (4 * (m : ℝ))) * (X : ℝ) +
        (2 * ((ε ^ 2 - 1) / (2 * ε) + 1) + 4) * (Real.sqrt (X : ℝ) + 1) := by
  have hXR_pos : (0 : ℝ) < (X : ℝ) := by positivity
  have hε2_pos : 0 < ε ^ 2 - 1 := by nlinarith
  have hsqrtm_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by positivity)
  set c : ℝ := (ε ^ 2 + 1) / (ε ^ 2 - 1)
  have hc_gt1 : 1 < c := by dsimp [c]; rw [one_lt_div hε2_pos]; linarith
  set T : ℝ := Real.sqrt (X : ℝ) * (ε ^ 2 - 1) / (2 * ε)
  have hT_pos : 0 < T := by dsimp [T]; positivity
  let K_pos : ℕ := Nat.floor (T / Real.sqrt (m : ℝ))
  let K_neg : ℕ := Nat.floor T
  let S_pos : Finset (ℤ × ℤ) :=
    (Icc 0 K_pos).biUnion fun k =>
      (Finset.Ioc ⌊c * ((k : ℝ) * Real.sqrt (m : ℝ))⌋
        ⌊Real.sqrt ((X : ℝ) + ((k : ℝ) * Real.sqrt (m : ℝ)) ^ 2)⌋).image (fun x => (x, (k : ℤ)))
  let S_neg : Finset (ℤ × ℤ) :=
    (Icc 0 K_neg).biUnion fun x =>
      (Finset.Ioc ⌊(c * (x : ℝ)) / Real.sqrt (m : ℝ)⌋
        ⌊Real.sqrt ((X : ℝ) + (x : ℝ) ^ 2) / Real.sqrt (m : ℝ)⌋).image (fun k => ((x : ℤ), k))
  let f : ℝ → ℝ := fun t => Real.sqrt ((X : ℝ) + t ^ 2) - c * t
  have hf_anti : AntitoneOn f (Set.Ici 0) := antitone_sqrt_sub_linear hXR_pos.le hc_gt1.le
  have hf_cont : ContinuousOn f (Set.Icc 0 T) := by dsimp [f]; fun_prop
  have hf_T : f T = 0 := by
    dsimp [f, T, c]
    have hval : (X : ℝ) + (Real.sqrt (X : ℝ) * (ε ^ 2 - 1) / (2 * ε)) ^ 2 =
        (Real.sqrt (X : ℝ) * (ε ^ 2 + 1) / (2 * ε)) ^ 2 := by
      field_simp
      rw [Real.sq_sqrt hXR_pos.le]
      ring
    rw [hval, Real.sqrt_sq (by positivity)]; field_simp; ring
  have hf_nn : ∀ t ∈ Set.Icc 0 T, 0 ≤ f t := fun t ht => by
    rw [← hf_T]; exact hf_anti ht.1 hT_pos.le ht.2
  have hint_eq : ∫ t in (0 : ℝ)..T, f t = (X : ℝ) / 2 * Real.log ε :=
    hyperbolic_sector_integral hXR_pos hε
  have hSpos_card : (S_pos.card : ℝ) ≤
      (Real.log ε / (2 * Real.sqrt (m : ℝ))) * (X : ℝ) +
        (((ε ^ 2 - 1) / (2 * ε) + 1) + 2) * (Real.sqrt (X : ℝ) + 1) := by
    have h1 : (S_pos.card : ℝ) ≤ ∑ k ∈ Icc 0 K_pos,
        ((Finset.Ioc ⌊c * ((k : ℝ) * Real.sqrt (m : ℝ))⌋
          ⌊Real.sqrt ((X : ℝ) + ((k : ℝ) * Real.sqrt (m : ℝ)) ^ 2)⌋).card : ℝ) := by
      have hle := Finset.card_biUnion_le (s := Icc 0 K_pos)
        (t := fun k => (Finset.Ioc ⌊c * ((k : ℝ) * Real.sqrt (m : ℝ))⌋
          ⌊Real.sqrt ((X : ℝ) + ((k : ℝ) * Real.sqrt (m : ℝ)) ^ 2)⌋).image (fun x => (x, (k : ℤ))))
      have hle' : S_pos.card ≤ ∑ k ∈ Icc 0 K_pos,
          (Finset.Ioc ⌊c * ((k : ℝ) * Real.sqrt (m : ℝ))⌋
            ⌊Real.sqrt ((X : ℝ) + ((k : ℝ) * Real.sqrt (m : ℝ)) ^ 2)⌋).card :=
        hle.trans (Finset.sum_le_sum fun _ _ => Finset.card_image_le)
      exact_mod_cast hle'
    have hKpos_le : (K_pos : ℝ) * Real.sqrt (m : ℝ) ≤ T := by
      have hfl : (K_pos : ℝ) ≤ T / Real.sqrt (m : ℝ) := Nat.floor_le (by positivity)
      exact (le_div_iff₀ hsqrtm_pos).mp hfl
    have h2 : ∀ k ∈ Icc 0 K_pos,
        ((Finset.Ioc ⌊c * ((k : ℝ) * Real.sqrt (m : ℝ))⌋
          ⌊Real.sqrt ((X : ℝ) + ((k : ℝ) * Real.sqrt (m : ℝ)) ^ 2)⌋).card : ℝ) ≤
          f ((k : ℝ) * Real.sqrt (m : ℝ)) + 1 := by
      intro k hk
      simp only [Finset.mem_Icc] at hk
      have hkt : (k : ℝ) * Real.sqrt (m : ℝ) ≤ T := by
        have : (k : ℝ) ≤ (K_pos : ℝ) := by exact_mod_cast hk.2
        nlinarith
      have hfnn' : 0 ≤ f ((k : ℝ) * Real.sqrt (m : ℝ)) := hf_nn _ ⟨by positivity, hkt⟩
      have hle' : c * ((k : ℝ) * Real.sqrt (m : ℝ)) ≤
          Real.sqrt ((X : ℝ) + ((k : ℝ) * Real.sqrt (m : ℝ)) ^ 2) := by
        dsimp [f] at hfnn'; linarith
      simpa [f] using finset_Ioc_int_card_le _ _ hle'
    have hsplit0 : ∑ k ∈ Icc 0 K_pos, (f ((k : ℝ) * Real.sqrt (m : ℝ)) + 1) =
        (f 0 + 1) + (∑ k ∈ Icc 1 K_pos, f ((k : ℝ) * Real.sqrt (m : ℝ))) + (K_pos : ℝ) := by
      have hunion : Icc 0 K_pos = insert 0 (Icc 1 K_pos) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hunion, Finset.sum_insert (by simp), Finset.sum_add_distrib]
      simp [Nat.card_Icc]; ring
    have hint_pos := sum_antitone_scaled_le_integral hT_pos hsqrtm_pos hf_anti hf_cont hf_nn K_pos hKpos_le
    have hf0 : f 0 = Real.sqrt (X : ℝ) := by simp [f]
    have hKpos_bd : (K_pos : ℝ) ≤ T := by
      have hm_ge1 : (1 : ℝ) ≤ Real.sqrt (m : ℝ) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hm)
      nlinarith
    have hscaled : (1 / Real.sqrt (m : ℝ)) * ∫ t in (0 : ℝ)..T, f t =
        (Real.log ε / (2 * Real.sqrt (m : ℝ))) * (X : ℝ) := by
      rw [hint_eq]; ring
    have hT_eq : T = ((ε ^ 2 - 1) / (2 * ε)) * Real.sqrt (X : ℝ) := by dsimp [T]; ring
    have hsum_bd : ∑ k ∈ Icc 1 K_pos, f ((k : ℝ) * Real.sqrt (m : ℝ)) ≤
        (Real.log ε / (2 * Real.sqrt (m : ℝ))) * (X : ℝ) := by linarith [hint_pos, hscaled]
    calc (S_pos.card : ℝ)
        ≤ ∑ k ∈ Icc 0 K_pos, (f ((k : ℝ) * Real.sqrt (m : ℝ)) + 1) := h1.trans (Finset.sum_le_sum h2)
      _ = (Real.sqrt (X : ℝ) + 1) + (∑ k ∈ Icc 1 K_pos, f ((k : ℝ) * Real.sqrt (m : ℝ))) + (K_pos : ℝ) := by
          rw [hsplit0, hf0]
      _ ≤ (Real.sqrt (X : ℝ) + 1) + (Real.log ε / (2 * Real.sqrt (m : ℝ))) * (X : ℝ) + T := by
          linarith
      _ ≤ (Real.log ε / (2 * Real.sqrt (m : ℝ))) * (X : ℝ) +
            (((ε ^ 2 - 1) / (2 * ε) + 1) + 2) * (Real.sqrt (X : ℝ) + 1) := by
          rw [hT_eq]
          have : 0 ≤ (ε ^ 2 - 1) / (2 * ε) := by positivity
          have : 0 ≤ Real.sqrt (X : ℝ) := Real.sqrt_nonneg _
          nlinarith
  have hSneg_card : (S_neg.card : ℝ) ≤
      (Real.log ε / (2 * Real.sqrt (m : ℝ))) * (X : ℝ) +
        (((ε ^ 2 - 1) / (2 * ε) + 1) + 2) * (Real.sqrt (X : ℝ) + 1) := by
    have h1 : (S_neg.card : ℝ) ≤ ∑ x ∈ Icc 0 K_neg,
        ((Finset.Ioc ⌊(c * (x : ℝ)) / Real.sqrt (m : ℝ)⌋
          ⌊Real.sqrt ((X : ℝ) + (x : ℝ) ^ 2) / Real.sqrt (m : ℝ)⌋).card : ℝ) := by
      have hle := Finset.card_biUnion_le (s := Icc 0 K_neg)
        (t := fun x => (Finset.Ioc ⌊(c * (x : ℝ)) / Real.sqrt (m : ℝ)⌋
          ⌊Real.sqrt ((X : ℝ) + (x : ℝ) ^ 2) / Real.sqrt (m : ℝ)⌋).image (fun k => ((x : ℤ), k)))
      have hle' : S_neg.card ≤ ∑ x ∈ Icc 0 K_neg,
          (Finset.Ioc ⌊(c * (x : ℝ)) / Real.sqrt (m : ℝ)⌋
            ⌊Real.sqrt ((X : ℝ) + (x : ℝ) ^ 2) / Real.sqrt (m : ℝ)⌋).card :=
        hle.trans (Finset.sum_le_sum fun _ _ => Finset.card_image_le)
      exact_mod_cast hle'
    have hKneg_le : (K_neg : ℝ) * 1 ≤ T := by simpa using Nat.floor_le hT_pos.le
    have h2 : ∀ x ∈ Icc 0 K_neg,
        ((Finset.Ioc ⌊(c * (x : ℝ)) / Real.sqrt (m : ℝ)⌋
          ⌊Real.sqrt ((X : ℝ) + (x : ℝ) ^ 2) / Real.sqrt (m : ℝ)⌋).card : ℝ) ≤
          f (x : ℝ) / Real.sqrt (m : ℝ) + 1 := by
      intro x hx
      simp only [Finset.mem_Icc] at hx
      have hxt : (x : ℝ) ≤ T := by
        have : (x : ℝ) ≤ (K_neg : ℝ) := by exact_mod_cast hx.2
        linarith
      have hfnn' : 0 ≤ f (x : ℝ) := hf_nn _ ⟨by positivity, hxt⟩
      have hle' : (c * (x : ℝ)) / Real.sqrt (m : ℝ) ≤
          Real.sqrt ((X : ℝ) + (x : ℝ) ^ 2) / Real.sqrt (m : ℝ) := by
        apply div_le_div_of_nonneg_right _ hsqrtm_pos.le
        dsimp [f] at hfnn'; linarith
      have hbd := finset_Ioc_int_card_le _ _ hle'
      have hsub : Real.sqrt ((X : ℝ) + (x : ℝ) ^ 2) / Real.sqrt (m : ℝ) -
          (c * (x : ℝ)) / Real.sqrt (m : ℝ) = f (x : ℝ) / Real.sqrt (m : ℝ) := by
        dsimp [f]; rw [sub_div]
      rwa [hsub] at hbd
    have hsplit0 : ∑ x ∈ Icc 0 K_neg, (f (x : ℝ) / Real.sqrt (m : ℝ) + 1) =
        (f 0 / Real.sqrt (m : ℝ) + 1) +
          (∑ x ∈ Icc 1 K_neg, f ((x : ℝ) * 1)) / Real.sqrt (m : ℝ) + (K_neg : ℝ) := by
      have hunion : Icc 0 K_neg = insert 0 (Icc 1 K_neg) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hunion, Finset.sum_insert (by simp), Finset.sum_add_distrib, ← Finset.sum_div]
      simp [Nat.card_Icc]; ring
    have hint_neg := sum_antitone_scaled_le_integral hT_pos one_pos hf_anti hf_cont hf_nn K_neg hKneg_le
    have hf0 : f 0 / Real.sqrt (m : ℝ) ≤ Real.sqrt (X : ℝ) := by
      have hf0' : f 0 = Real.sqrt (X : ℝ) := by simp [f]
      have hm_ge1 : (1 : ℝ) ≤ Real.sqrt (m : ℝ) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hm)
      rw [hf0']; exact div_le_self (Real.sqrt_nonneg _) hm_ge1
    have hdiv_le : (∑ x ∈ Icc 1 K_neg, f ((x : ℝ) * 1)) / Real.sqrt (m : ℝ) ≤
        (Real.log ε / (2 * Real.sqrt (m : ℝ))) * (X : ℝ) := by
      have h1' : (∑ x ∈ Icc 1 K_neg, f ((x : ℝ) * 1)) / Real.sqrt (m : ℝ) ≤
          ((X : ℝ) / 2 * Real.log ε) / Real.sqrt (m : ℝ) := by
        apply div_le_div_of_nonneg_right _ hsqrtm_pos.le
        simpa [hint_eq] using hint_neg
      have h2' : ((X : ℝ) / 2 * Real.log ε) / Real.sqrt (m : ℝ) =
          (Real.log ε / (2 * Real.sqrt (m : ℝ))) * (X : ℝ) := by ring
      linarith
    have hT_eq : T = ((ε ^ 2 - 1) / (2 * ε)) * Real.sqrt (X : ℝ) := by dsimp [T]; ring
    calc (S_neg.card : ℝ)
        ≤ ∑ x ∈ Icc 0 K_neg, (f (x : ℝ) / Real.sqrt (m : ℝ) + 1) := h1.trans (Finset.sum_le_sum h2)
      _ = (f 0 / Real.sqrt (m : ℝ) + 1) +
            (∑ x ∈ Icc 1 K_neg, f ((x : ℝ) * 1)) / Real.sqrt (m : ℝ) + (K_neg : ℝ) := hsplit0
      _ ≤ (Real.sqrt (X : ℝ) + 1) + (Real.log ε / (2 * Real.sqrt (m : ℝ))) * (X : ℝ) + T := by
          linarith
      _ ≤ (Real.log ε / (2 * Real.sqrt (m : ℝ))) * (X : ℝ) +
            (((ε ^ 2 - 1) / (2 * ε) + 1) + 2) * (Real.sqrt (X : ℝ) + 1) := by
          rw [hT_eq]
          have : 0 ≤ (ε ^ 2 - 1) / (2 * ε) := by positivity
          have : 0 ≤ Real.sqrt (X : ℝ) := Real.sqrt_nonneg _
          nlinarith
  have h4m : Real.sqrt (4 * (m : ℝ)) = 2 * Real.sqrt (m : ℝ) := by
    rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have hW_union : ((wedgeSet m X ε).card : ℝ) ≤ (S_pos.card : ℝ) + (S_neg.card : ℝ) := by
    change ((S_pos ∪ S_neg).card : ℝ) ≤ _
    exact_mod_cast Finset.card_union_le S_pos S_neg
  have hlog_eq : 2 * Real.log ε / (2 * Real.sqrt (m : ℝ)) =
      Real.log ε / (2 * Real.sqrt (m : ℝ)) + Real.log ε / (2 * Real.sqrt (m : ℝ)) := by ring
  rw [h4m, hlog_eq]
  linarith [hW_union, hSpos_card, hSneg_card]

private lemma mem_wedgeSet_of_bounds {m X : ℕ} (hm : 1 ≤ m) (hX : 1 ≤ X) {ε : ℝ} (hε : 1 < ε)
    {x k : ℤ} (hnorm_pos : 1 ≤ (x ^ 2 - (m : ℤ) * k ^ 2).natAbs)
    (hnorm_le : (x ^ 2 - (m : ℤ) * k ^ 2).natAbs ≤ X)
    (hlo : Real.sqrt ((x ^ 2 - (m : ℤ) * k ^ 2).natAbs : ℝ) ≤ (x : ℝ) + (k : ℝ) * Real.sqrt (m : ℝ))
    (hhi : (x : ℝ) + (k : ℝ) * Real.sqrt (m : ℝ) <
      ε * Real.sqrt ((x ^ 2 - (m : ℤ) * k ^ 2).natAbs : ℝ)) :
    (x, k) ∈ wedgeSet m X ε := by
  have hε_pos : 0 < ε := by linarith
  have hε2_pos : 0 < ε ^ 2 - 1 := by nlinarith
  have hXR_pos : (0 : ℝ) < (X : ℝ) := by positivity
  have hsqrtm_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by positivity)
  set c : ℝ := (ε ^ 2 + 1) / (ε ^ 2 - 1)
  set T : ℝ := Real.sqrt (X : ℝ) * (ε ^ 2 - 1) / (2 * ε)
  set z : ℤ := x ^ 2 - (m : ℤ) * k ^ 2
  set n : ℕ := z.natAbs
  set r : ℝ := Real.sqrt (n : ℝ)
  have hr_pos : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast hnorm_pos)
  set uR : ℝ := (x : ℝ) + (k : ℝ) * Real.sqrt (m : ℝ)
  set vR : ℝ := (x : ℝ) - (k : ℝ) * Real.sqrt (m : ℝ)
  have huv : uR * vR = (z : ℝ) := by
    dsimp [z]; push_cast
    dsimp [uR, vR]
    have hsq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt (by positivity)
    linear_combination -(k : ℝ) ^ 2 * hsq
  have huv_abs : |uR * vR| = (n : ℝ) := by
    rw [huv, ← Int.cast_abs, ← Int.natCast_natAbs z]
    rfl
  have huv_leX : |uR * vR| ≤ (X : ℝ) := by rw [huv_abs]; exact_mod_cast hnorm_le
  have huR_pos : 0 < uR := lt_of_lt_of_le hr_pos hlo
  have hr2 : r ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hv_lo : uR / ε ^ 2 < |vR| := by
    have hsq : uR ^ 2 < ε ^ 2 * (n : ℝ) := by
      have h2 : uR ^ 2 < (ε * r) ^ 2 := by nlinarith
      rw [mul_pow, hr2] at h2; exact h2
    rw [← huv_abs, abs_mul, abs_of_pos huR_pos] at hsq
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hv_hi : |vR| ≤ uR := by
    have hsq : (n : ℝ) ≤ uR ^ 2 := by nlinarith
    rw [← huv_abs, abs_mul, abs_of_pos huR_pos] at hsq
    nlinarith
  have hv_ne0 : vR ≠ 0 := by
    intro hv0; rw [hv0, abs_zero] at hv_lo; linarith [div_pos huR_pos (by positivity : (0 : ℝ) < ε ^ 2)]
  have hc2 : c ^ 2 - 1 = (2 * ε / (ε ^ 2 - 1)) ^ 2 := by dsimp [c]; field_simp; ring
  have hle_T_of : ∀ t : ℝ, 0 ≤ t → c * t ≤ Real.sqrt ((X : ℝ) + t ^ 2) → t ≤ T := by
    intro t ht hct
    have h1 : (c * t) ^ 2 ≤ (X : ℝ) + t ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hct 2
      rwa [Real.sq_sqrt (by positivity)] at this
    have h2 : (2 * ε / (ε ^ 2 - 1) * t) ^ 2 ≤ (Real.sqrt (X : ℝ)) ^ 2 := by
      rw [Real.sq_sqrt hXR_pos.le]
      have h3 : (c ^ 2 - 1) * t ^ 2 ≤ (X : ℝ) := by nlinarith
      rw [hc2] at h3
      linarith [show (2 * ε / (ε ^ 2 - 1) * t) ^ 2 = (2 * ε / (ε ^ 2 - 1)) ^ 2 * t ^ 2 by ring]
    have h3 : 2 * ε / (ε ^ 2 - 1) * t ≤ Real.sqrt (X : ℝ) :=
      le_of_sq_le_sq h2 (Real.sqrt_nonneg _)
    dsimp [T]
    rw [le_div_iff₀ (by positivity)]
    rw [div_mul_eq_mul_div, div_le_iff₀ hε2_pos] at h3
    linarith
  unfold wedgeSet
  rcases lt_or_gt_of_ne hv_ne0 with hv_neg | hv_pos
  · apply Finset.mem_union_right
    rw [Finset.mem_biUnion]
    have hw_eq : |vR| = -vR := abs_of_neg hv_neg
    have hx_nn : (0 : ℝ) ≤ (x : ℝ) := by dsimp [uR, vR] at hv_hi hw_eq; linarith
    have hx_nat : 0 ≤ x := by exact_mod_cast hx_nn
    have hkx_lo : c * (x : ℝ) < (k : ℝ) * Real.sqrt (m : ℝ) := by
      rw [hw_eq] at hv_lo; dsimp [uR, vR] at hv_lo
      rw [div_lt_iff₀ (by positivity)] at hv_lo
      dsimp [c]; rw [div_mul_eq_mul_div, div_lt_iff₀ hε2_pos]; linarith
    have hkx_hi : (k : ℝ) * Real.sqrt (m : ℝ) ≤ Real.sqrt ((X : ℝ) + (x : ℝ) ^ 2) := by
      have h1 : (m : ℝ) * (k : ℝ) ^ 2 - (x : ℝ) ^ 2 ≤ (X : ℝ) := by
        have h2 : -(uR * vR) = (m : ℝ) * (k : ℝ) ^ 2 - (x : ℝ) ^ 2 := by
          dsimp [uR, vR]; have hsq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt (by positivity)
          linear_combination (k : ℝ) ^ 2 * hsq
        have h3 : -(uR * vR) = |uR * vR| := (abs_of_neg (mul_neg_of_pos_of_neg huR_pos hv_neg)).symm
        linarith
      have him_nn : 0 ≤ (k : ℝ) * Real.sqrt (m : ℝ) := by
        have : 0 ≤ c * (x : ℝ) := by positivity
        linarith
      rw [← Real.sqrt_sq him_nn]
      apply Real.sqrt_le_sqrt
      have hsq : ((k : ℝ) * Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) * (k : ℝ) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
      linarith
    have hx_leT : (x : ℝ) ≤ T := hle_T_of (x : ℝ) hx_nn (hkx_lo.le.trans hkx_hi)
    refine ⟨x.toNat, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      refine ⟨Nat.zero_le _, Nat.le_floor ?_⟩
      have : (x.toNat : ℝ) = (x : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hx_nat
      linarith
    · rw [Finset.mem_image]
      refine ⟨k, ?_, ?_⟩
      · simp only [Finset.mem_Ioc]
        have hre_eq : (x.toNat : ℝ) = (x : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hx_nat
        rw [hre_eq]
        refine ⟨Int.floor_lt.mpr ((div_lt_iff₀ hsqrtm_pos).mpr hkx_lo),
          Int.le_floor.mpr ((le_div_iff₀ hsqrtm_pos).mpr hkx_hi)⟩
      · ext <;> simp [Int.toNat_of_nonneg hx_nat]
  · apply Finset.mem_union_left
    rw [Finset.mem_biUnion]
    have hw_eq : |vR| = vR := abs_of_pos hv_pos
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) := by dsimp [uR, vR] at hv_hi hw_eq; nlinarith [hsqrtm_pos]
    have hk_nat : 0 ≤ k := by exact_mod_cast hk_nn
    have hxk_lo : c * ((k : ℝ) * Real.sqrt (m : ℝ)) < (x : ℝ) := by
      rw [hw_eq] at hv_lo; dsimp [uR, vR] at hv_lo
      rw [div_lt_iff₀ (by positivity)] at hv_lo
      dsimp [c]; rw [div_mul_eq_mul_div, div_lt_iff₀ hε2_pos]; linarith
    have hxk_hi : (x : ℝ) ≤ Real.sqrt ((X : ℝ) + ((k : ℝ) * Real.sqrt (m : ℝ)) ^ 2) := by
      have h1 : (x : ℝ) ^ 2 - (m : ℝ) * (k : ℝ) ^ 2 ≤ (X : ℝ) := by
        have h2 : uR * vR = (x : ℝ) ^ 2 - (m : ℝ) * (k : ℝ) ^ 2 := by
          dsimp [uR, vR]; have hsq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt (by positivity)
          linear_combination -(k : ℝ) ^ 2 * hsq
        have h3 : uR * vR = |uR * vR| := (abs_of_pos (mul_pos huR_pos hv_pos)).symm
        linarith
      have hre_nn : 0 ≤ (x : ℝ) := by
        have : 0 ≤ c * ((k : ℝ) * Real.sqrt (m : ℝ)) := by positivity
        linarith
      rw [← Real.sqrt_sq hre_nn]
      apply Real.sqrt_le_sqrt
      have hsq : ((k : ℝ) * Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) * (k : ℝ) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
      linarith
    have hk_leT : (k : ℝ) * Real.sqrt (m : ℝ) ≤ T :=
      hle_T_of ((k : ℝ) * Real.sqrt (m : ℝ)) (by positivity) (hxk_lo.le.trans hxk_hi)
    refine ⟨k.toNat, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      refine ⟨Nat.zero_le _, Nat.le_floor ?_⟩
      rw [le_div_iff₀ hsqrtm_pos]
      have hkt : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk_nat
      rw [hkt]; exact hk_leT
    · rw [Finset.mem_image]
      refine ⟨x, ?_, ?_⟩
      · simp only [Finset.mem_Ioc]
        have him_eq : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk_nat
        rw [him_eq]
        exact ⟨Int.floor_lt.mpr hxk_lo, Int.le_floor.mpr hxk_hi⟩
      · ext <;> simp [Int.toNat_of_nonneg hk_nat]

private lemma exists_wedge_rep {m y X : ℕ} (hy : 1 ≤ y) (hm : m + 2 = (4 * y) ^ 2)
    (hsq : Squarefree m) (hX : 1 ≤ X) (α : Zsqrtd (m : ℤ))
    (hα1 : 1 ≤ α.norm.natAbs) (hαX : α.norm.natAbs ≤ X) :
    let ε : ℝ := (16 * (y : ℝ) ^ 2 - 1) + 4 * (y : ℝ) * Real.sqrt (m : ℝ)
    ∃ p ∈ wedgeSet m X ε, Associated α ⟨p.1, p.2⟩ := by
  have hm_pos : 0 < m := by nlinarith
  have hm1 : 1 < m := by nlinarith
  let _ : IsDomain (Zsqrtd (m : ℤ)) := zsqrtd_isDomain hm1 hsq
  let ι : Zsqrtd (m : ℤ) →+* ℝ := Zsqrtd.toReal (show (0 : ℤ) ≤ m by positivity)
  have hι_inj : Function.Injective ι :=
    Zsqrtd.toReal_injective (by positivity) (not_sq_of_squarefree_gt_one hm1 hsq)
  set ε : ℝ := (16 * (y : ℝ) ^ 2 - 1) + 4 * (y : ℝ) * Real.sqrt (m : ℝ)
  have hε_eq : ι (fundUnitU hm : Zsqrtd (m : ℤ)) = ε := by
    simp [ι, fundUnitU, fundUnit, Zsqrtd.toReal, ε]
  have hε_gt1 : 1 < ε := by
    have hy1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
    have hsq_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by positivity)
    dsimp [ε]; nlinarith
  have hε_pos : 0 < ε := by linarith
  have hlogε_pos : 0 < Real.log ε := Real.log_pos hε_gt1
  have hα_ne0 : α ≠ 0 := by intro h0; rw [h0] at hα1; simp at hα1
  have hια_ne0 : ι α ≠ 0 := fun h0 => hα_ne0 (hι_inj (by rwa [map_zero]))
  obtain ⟨β, hβ_assoc, hιβ_pos⟩ : ∃ β : Zsqrtd (m : ℤ), Associated α β ∧ 0 < ι β := by
    rcases lt_or_gt_of_ne hια_ne0 with hlt | hgt
    · refine ⟨-α, Associated.symm ⟨-1, by simp⟩, by rw [map_neg]; linarith⟩
    · exact ⟨α, Associated.refl _, hgt⟩
  let r : ℝ := Real.sqrt (α.norm.natAbs : ℝ)
  have hr_pos : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast hα1)
  let j : ℤ := ⌊Real.log (ι β / r) / Real.log ε⌋
  let γ : Zsqrtd (m : ℤ) := β * ((fundUnitU hm ^ (-j) : (Zsqrtd (m : ℤ))ˣ) : Zsqrtd (m : ℤ))
  have hγ_assoc : Associated α γ := hβ_assoc.trans ⟨fundUnitU hm ^ (-j), rfl⟩
  have hι_zpow : ∀ n : ℤ, ι ((fundUnitU hm ^ n : (Zsqrtd (m : ℤ))ˣ) : Zsqrtd (m : ℤ)) = ε ^ n := by
    intro n
    have h1 : Units.map (ι : Zsqrtd (m : ℤ) →* ℝ) (fundUnitU hm ^ n) =
        (Units.map (ι : Zsqrtd (m : ℤ) →* ℝ) (fundUnitU hm)) ^ n := map_zpow _ _ _
    have h2 := congrArg Units.val h1
    change ι ((fundUnitU hm ^ n : (Zsqrtd (m : ℤ))ˣ) : Zsqrtd (m : ℤ)) =
      (((Units.map (ι : Zsqrtd (m : ℤ) →* ℝ) (fundUnitU hm)) ^ n : ℝˣ) : ℝ) at h2
    rw [Units.val_zpow_eq_zpow_val] at h2
    change ι ((fundUnitU hm ^ n : (Zsqrtd (m : ℤ))ˣ) : Zsqrtd (m : ℤ)) =
      (ι (fundUnitU hm : Zsqrtd (m : ℤ))) ^ n at h2
    rw [hε_eq] at h2
    exact h2
  have hιγ : ι γ = ι β * ε ^ (-j) := by
    dsimp [γ]; rw [map_mul, hι_zpow (-j)]
  have hιγ_lo : r ≤ ι γ := by
    rw [hιγ]
    have hfl : (j : ℝ) ≤ Real.log (ι β / r) / Real.log ε := Int.floor_le _
    have hlog_le : (j : ℝ) * Real.log ε ≤ Real.log (ι β / r) := (le_div_iff₀ hlogε_pos).mp hfl
    have hexp := Real.exp_le_exp.mpr hlog_le
    rw [Real.exp_log (div_pos hιβ_pos hr_pos)] at hexp
    have hpow : Real.exp ((j : ℝ) * Real.log ε) = ε ^ j := by
      rw [mul_comm, ← Real.rpow_def_of_pos hε_pos, Real.rpow_intCast]
    rw [hpow, le_div_iff₀ hr_pos] at hexp
    have hεj_pos : 0 < ε ^ j := zpow_pos hε_pos j
    rw [zpow_neg, ← div_eq_mul_inv, le_div_iff₀ hεj_pos]
    linarith
  have hιγ_hi : ι γ < ε * r := by
    rw [hιγ]
    have hfl : Real.log (ι β / r) / Real.log ε < (j : ℝ) + 1 := Int.lt_floor_add_one _
    have hlog_lt : Real.log (ι β / r) < ((j : ℝ) + 1) * Real.log ε := (div_lt_iff₀ hlogε_pos).mp hfl
    have hexp := Real.exp_lt_exp.mpr hlog_lt
    rw [Real.exp_log (div_pos hιβ_pos hr_pos)] at hexp
    have hpow : Real.exp (((j : ℝ) + 1) * Real.log ε) = ε ^ j * ε := by
      rw [add_mul, one_mul, Real.exp_add, Real.exp_log hε_pos,
        mul_comm (j : ℝ), ← Real.rpow_def_of_pos hε_pos, Real.rpow_intCast]
    rw [hpow, div_lt_iff₀ hr_pos] at hexp
    have hεj_pos : 0 < ε ^ j := zpow_pos hε_pos j
    rw [zpow_neg, ← div_eq_mul_inv, div_lt_iff₀ hεj_pos]
    nlinarith
  have hγn : γ.norm.natAbs = α.norm.natAbs := by
    obtain ⟨u, hu⟩ := hγ_assoc
    have hu1 : u.val.norm.natAbs = 1 :=
      Int.isUnit_iff_natAbs_eq.mp ((Zsqrtd.isUnit_iff_norm_isUnit u.val).mp u.isUnit)
    have := congrArg (fun z : Zsqrtd (m : ℤ) => z.norm.natAbs) hu
    simpa [Zsqrtd.norm_mul, Int.natAbs_mul, hu1] using this.symm
  have hγ_norm_eq : γ.norm = γ.re ^ 2 - (m : ℤ) * γ.im ^ 2 := by
    simp [Zsqrtd.norm_def]; ring
  have hιγ_eq : ι γ = (γ.re : ℝ) + (γ.im : ℝ) * Real.sqrt (m : ℝ) := by
    simp [ι, Zsqrtd.toReal]
  refine ⟨(γ.re, γ.im), ?_, hγ_assoc⟩
  apply mem_wedgeSet_of_bounds (by omega) hX hε_gt1
  · rw [← hγ_norm_eq, hγn]; exact hα1
  · rw [← hγ_norm_eq, hγn]; exact hαX
  · rw [← hγ_norm_eq, hγn, ← hιγ_eq]; exact hιγ_lo
  · rw [← hγ_norm_eq, hγn, ← hιγ_eq]; exact hιγ_hi

private lemma sum_a_le_regulator_bound {m y : ℕ} (hy : 1 ≤ y) (hm : m + 2 = (4 * y) ^ 2)
    (hsq : Squarefree m) (hpid : IsPrincipalIdealRing (Zsqrtd (m : ℤ))) :
    let hm_pos : 0 < m := by nlinarith
    let ε : ℝ := (16 * (y : ℝ) ^ 2 - 1) + 4 * (y : ℝ) * Real.sqrt (m : ℝ)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      ∑ n ∈ Icc 1 X, dconv (fun _ => 1) (chiRe (quadChar m hm_pos)) n ≤
        (2 * Real.log ε / Real.sqrt (4 * (m : ℝ))) * (X : ℝ) + C * (Real.sqrt (X : ℝ) + 1) := by
  have hm_pos : 0 < m := by nlinarith
  set ε : ℝ := (16 * (y : ℝ) ^ 2 - 1) + 4 * (y : ℝ) * Real.sqrt (m : ℝ)
  have hε_gt1 : 1 < ε := by
    have hy1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
    have hsq_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by positivity)
    dsimp [ε]; nlinarith
  have hε2_pos : 0 < ε ^ 2 - 1 := by nlinarith
  refine ⟨2 * ((ε ^ 2 - 1) / (2 * ε) + 1) + 4, by positivity, ?_⟩
  intro X hX
  classical
  let Sn : ∀ n : ℕ, 1 ≤ n → Finset (Zsqrtd (m : ℤ)) :=
    fun n hn => (exists_nonassoc_of_norm hy hm hsq hpid n hn).choose
  have hSn_spec : ∀ n (hn : 1 ≤ n),
      ((Sn n hn).card : ℝ) = dconv (fun _ => 1) (chiRe (quadChar m hm_pos)) n ∧
      (∀ α ∈ Sn n hn, α.norm.natAbs = n) ∧
      (∀ α ∈ Sn n hn, ∀ β ∈ Sn n hn, Associated α β → α = β) :=
    fun n hn => (exists_nonassoc_of_norm hy hm hsq hpid n hn).choose_spec
  let dom : Finset (Σ n : ℕ, Zsqrtd (m : ℤ)) :=
    (Icc 1 X).sigma (fun n => if h : 1 ≤ n then Sn n h else ∅)
  have hdom_card : (dom.card : ℝ) =
      ∑ n ∈ Icc 1 X, dconv (fun _ => 1) (chiRe (quadChar m hm_pos)) n := by
    rw [Finset.card_sigma, Nat.cast_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_Icc] at hn
    rw [dif_pos hn.1]
    exact (hSn_spec n hn.1).1
  let embed : (Σ n : ℕ, Zsqrtd (m : ℤ)) → ℤ × ℤ := fun x =>
    if h : 1 ≤ x.2.norm.natAbs ∧ x.2.norm.natAbs ≤ X then
      (exists_wedge_rep hy hm hsq hX x.2 h.1 h.2).choose
    else (0, 0)
  have hembed_mem : ∀ x ∈ dom, embed x ∈ wedgeSet m X ε := by
    intro ⟨n, α⟩ hx
    simp only [dom, Finset.mem_sigma, Finset.mem_Icc] at hx
    rw [dif_pos hx.1.1] at hx
    have hαn : α.norm.natAbs = n := (hSn_spec n hx.1.1).2.1 α hx.2
    have hcond : 1 ≤ α.norm.natAbs ∧ α.norm.natAbs ≤ X := ⟨by omega, by omega⟩
    dsimp [embed]; rw [dif_pos hcond]
    exact (exists_wedge_rep hy hm hsq hX α hcond.1 hcond.2).choose_spec.1
  have hembed_inj : Set.InjOn embed (dom : Set _) := by
    intro ⟨n₁, α₁⟩ hx₁ ⟨n₂, α₂⟩ hx₂ heq
    simp only [Finset.mem_coe, dom, Finset.mem_sigma, Finset.mem_Icc] at hx₁ hx₂
    rw [dif_pos hx₁.1.1] at hx₁
    rw [dif_pos hx₂.1.1] at hx₂
    have h1n : α₁.norm.natAbs = n₁ := (hSn_spec n₁ hx₁.1.1).2.1 α₁ hx₁.2
    have h2n : α₂.norm.natAbs = n₂ := (hSn_spec n₂ hx₂.1.1).2.1 α₂ hx₂.2
    have hc1 : 1 ≤ α₁.norm.natAbs ∧ α₁.norm.natAbs ≤ X := ⟨by omega, by omega⟩
    have hc2 : 1 ≤ α₂.norm.natAbs ∧ α₂.norm.natAbs ≤ X := ⟨by omega, by omega⟩
    dsimp [embed] at heq
    rw [dif_pos hc1, dif_pos hc2] at heq
    have hs1 := (exists_wedge_rep hy hm hsq hX α₁ hc1.1 hc1.2).choose_spec.2
    have hs2 := (exists_wedge_rep hy hm hsq hX α₂ hc2.1 hc2.2).choose_spec.2
    rw [← heq] at hs2
    have hass : Associated α₁ α₂ := hs1.trans hs2.symm
    have hn_eq : n₁ = n₂ := by
      obtain ⟨u, hu⟩ := hass
      have hu1 : u.val.norm.natAbs = 1 :=
        Int.isUnit_iff_natAbs_eq.mp ((Zsqrtd.isUnit_iff_norm_isUnit u.val).mp u.isUnit)
      have := congrArg (fun z : Zsqrtd (m : ℤ) => z.norm.natAbs) hu
      simpa [Zsqrtd.norm_mul, Int.natAbs_mul, hu1, h1n, h2n] using this
    subst hn_eq
    have hα_eq : α₁ = α₂ := (hSn_spec n₁ hx₁.1.1).2.2 α₁ hx₁.2 α₂ hx₂.2 hass
    subst hα_eq; rfl
  have hcard_le : (dom.card : ℝ) ≤ ((wedgeSet m X ε).card : ℝ) := by
    exact_mod_cast Finset.card_le_card_of_injOn embed hembed_mem hembed_inj
  rw [hdom_card] at hcard_le
  exact hcard_le.trans (wedgeSet_card_le (by omega) hX hε_gt1)

/- Section 4a: Analytic bounds, Abel summation, L-functions, and Euler-Maclaurin -/

private lemma polya_vinogradov_re {N : ℕ} [NeZero N] (hN : 1 < N)
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (a b : ℕ) :
    |∑ n ∈ Icc a b, chiRe χ n| ≤ Real.sqrt (N : ℝ) * (Real.log (N : ℝ) + 1) := by
  have hsum : ∑ n ∈ Icc a b, chiRe χ n = (∑ n ∈ Icc a b, χ (n : ZMod N)).re := by
    simp [chiRe, Complex.re_sum]
  rw [hsum]
  exact (Complex.abs_re_le_norm _).trans (polya_vinogradov hN hχ a b)

private lemma abs_chiRe_le_one {N : ℕ} {χ : DirichletCharacter ℂ N}
    (hreal : ∀ n : ℕ, χ (n : ZMod N) = ((χ (n : ZMod N)).re : ℂ) ∧
      ((χ (n : ZMod N)).re = 0 ∨ (χ (n : ZMod N)).re = 1 ∨ (χ (n : ZMod N)).re = -1))
    (n : ℕ) : |chiRe χ n| ≤ 1 := by
  unfold chiRe
  rcases (hreal n).2 with h | h | h <;> simp [h]

private lemma log_le_rpow_div_e {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    Real.log x ≤ x ^ a / (a * Real.exp 1) := by
  have hpos : 0 < x ^ a / Real.exp 1 := div_pos (Real.rpow_pos_of_pos hx a) (Real.exp_pos 1)
  have h1 : Real.log (x ^ a / Real.exp 1) ≤ x ^ a / Real.exp 1 - 1 :=
    Real.log_le_sub_one_of_pos hpos
  rw [Real.log_div (Real.rpow_pos_of_pos hx a).ne' (Real.exp_pos 1).ne',
    Real.log_rpow hx, Real.log_exp] at h1
  have h2 : a * Real.log x ≤ x ^ a / Real.exp 1 := by linarith
  rw [le_div_iff₀ (mul_pos ha (Real.exp_pos 1))]
  have h3 := (le_div_iff₀ (Real.exp_pos 1)).mp h2
  linarith

private lemma log_le_16_rpow {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 16 * x ^ ((1 : ℝ) / 40) := by
  have he : (5 : ℝ) / 2 < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h1 := log_le_rpow_div_e hx (by norm_num : (0 : ℝ) < (1 : ℝ) / 40)
  have hden : (1 : ℝ) / 16 < ((1 : ℝ) / 40) * Real.exp 1 := by linarith
  have hxp : 0 ≤ x ^ ((1 : ℝ) / 40) := (Real.rpow_pos_of_pos hx _).le
  have hdiv : x ^ ((1 : ℝ) / 40) / (((1 : ℝ) / 40) * Real.exp 1) ≤
      x ^ ((1 : ℝ) / 40) / ((1 : ℝ) / 16) :=
    div_le_div_of_nonneg_left hxp (by norm_num) hden.le
  linarith

private lemma log_add_one_le_17_rpow {x : ℝ} (hx : 1 ≤ x) :
    Real.log x + 1 ≤ 17 * x ^ ((1 : ℝ) / 40) := by
  have h1 : Real.log x ≤ 16 * x ^ ((1 : ℝ) / 40) := log_le_16_rpow (by linarith)
  have h2 : (1 : ℝ) ≤ x ^ ((1 : ℝ) / 40) := Real.one_le_rpow hx (by norm_num)
  linarith

private lemma log_le_4_rpow {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 4 * x ^ ((1 : ℝ) / 10) := by
  have he : (5 : ℝ) / 2 < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h1 := log_le_rpow_div_e hx (by norm_num : (0 : ℝ) < (1 : ℝ) / 10)
  have hden : (1 : ℝ) / 4 < ((1 : ℝ) / 10) * Real.exp 1 := by linarith
  have hxp : 0 ≤ x ^ ((1 : ℝ) / 10) := (Real.rpow_pos_of_pos hx _).le
  have hdiv : x ^ ((1 : ℝ) / 10) / (((1 : ℝ) / 10) * Real.exp 1) ≤
      x ^ ((1 : ℝ) / 10) / ((1 : ℝ) / 4) :=
    div_le_div_of_nonneg_left hxp (by norm_num) hden.le
  linarith

private lemma log_add_one_le_5_rpow {x : ℝ} (hx : 1 ≤ x) :
    Real.log x + 1 ≤ 5 * x ^ ((1 : ℝ) / 10) := by
  have h1 : Real.log x ≤ 4 * x ^ ((1 : ℝ) / 10) := log_le_4_rpow (by linarith)
  have h2 : (1 : ℝ) ≤ x ^ ((1 : ℝ) / 10) := Real.one_le_rpow hx (by norm_num)
  linarith

private lemma sum_inv_sqrt_le (N : ℕ) :
    ∑ k ∈ Icc 1 N, (1 : ℝ) / Real.sqrt (k : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hsplit : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    have hstep : (1 : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
        2 * Real.sqrt ((n + 1 : ℕ) : ℝ) - 2 * Real.sqrt (n : ℝ) := by
      have hpos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
      rw [div_le_iff₀ hpos]
      have hsq1 : Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 = (n : ℝ) + 1 := by
        rw [Real.sq_sqrt (by positivity)]; push_cast; ring
      have hsq0 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
      have hle : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ n)
      nlinarith
    linarith

private lemma sum_rpow_neg_le {s : ℝ} (hs1 : s ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ Icc 1 N, (k : ℝ) ^ (-s) ≤ (N : ℝ) ^ (1 - s) * (Real.log (N : ℝ) + 1) := by
  have hterm : ∀ k ∈ Icc 1 N, (k : ℝ) ^ (-s) ≤ (N : ℝ) ^ (1 - s) * ((1 : ℝ) / (k : ℝ)) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hkn : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk.2
    have hpow : (k : ℝ) ^ (1 - s) ≤ (N : ℝ) ^ (1 - s) :=
      Real.rpow_le_rpow hk_pos.le hkn (by linarith)
    have heq : (k : ℝ) ^ (-s) = (k : ℝ) ^ (1 - s) * ((1 : ℝ) / (k : ℝ)) := by
      rw [one_div, ← Real.rpow_neg_one (k : ℝ), ← Real.rpow_add hk_pos]
      congr 1; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hpow (by positivity)
  calc ∑ k ∈ Icc 1 N, (k : ℝ) ^ (-s)
      ≤ ∑ k ∈ Icc 1 N, (N : ℝ) ^ (1 - s) * ((1 : ℝ) / (k : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (N : ℝ) ^ (1 - s) * ∑ k ∈ Icc 1 N, (1 : ℝ) / (k : ℝ) := by
        rw [← Finset.mul_sum]
    _ ≤ (N : ℝ) ^ (1 - s) * (Real.log (N : ℝ) + 1) := by
        exact mul_le_mul_of_nonneg_left (harmonic_le_log_add_one N hN)
          (Real.rpow_nonneg (by positivity) _)

private lemma abs_dconv_le {f g F G : ℕ → ℝ}
    (hf : ∀ n, 1 ≤ n → |f n| ≤ F n) (hg : ∀ n, 1 ≤ n → |g n| ≤ G n)
    {n : ℕ} (hn : 1 ≤ n) :
    |dconv f g n| ≤ dconv F G n := by
  unfold dconv
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  have hd_pos : 1 ≤ d := Nat.pos_of_mem_divisors hd
  have hnd_pos : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)) hd_pos
  rw [abs_mul]
  exact mul_le_mul (hf d hd_pos) (hg (n / d) hnd_pos) (abs_nonneg _) ((abs_nonneg _).trans (hf d hd_pos))

private lemma sum_dconv_eq_double (f g w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → w (a * b) = w a * w b) :
    ∑ n ∈ Icc 1 N, dconv f g n * w n =
      ∑ p ∈ (Icc 1 N ×ˢ Icc 1 N).filter (fun p => p.1 * p.2 ≤ N),
        g p.1 * w p.1 * (f p.2 * w p.2) := by
  have h1 : ∑ n ∈ Icc 1 N, dconv f g n * w n =
      ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, f d * g (n / d) * w n := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [dconv, Finset.sum_mul]
  rw [h1, Finset.sum_sigma']
  refine Finset.sum_bij (fun x _ => (x.1 / x.2, x.2)) ?_ ?_ ?_ ?_
  · intro ⟨n, d⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors, Finset.mem_filter,
      Finset.mem_product] at hx ⊢
    obtain ⟨⟨hn1, hnN⟩, hd_dvd, hn0⟩ := hx
    have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos hd_dvd (by omega)
    have hd_le : d ≤ n := Nat.le_of_dvd (by omega) hd_dvd
    have hq_pos : 1 ≤ n / d := Nat.div_pos hd_le hd_pos
    have hmul : n / d * d = n := Nat.div_mul_cancel hd_dvd
    refine ⟨⟨⟨hq_pos, (Nat.div_le_self n d).trans hnN⟩, ⟨hd_pos, hd_le.trans hnN⟩⟩, ?_⟩
    rw [hmul]; exact hnN
  · intro ⟨n₁, d₁⟩ hx₁ ⟨n₂, d₂⟩ hx₂ heq
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hx₁ hx₂
    simp only [Prod.mk.injEq] at heq
    have h1 : n₁ / d₁ * d₁ = n₁ := Nat.div_mul_cancel hx₁.2.1
    have h2 : n₂ / d₂ * d₂ = n₂ := Nat.div_mul_cancel hx₂.2.1
    have hn : n₁ = n₂ := by rw [← h1, ← h2, heq.1, heq.2]
    subst hn; have hd : d₁ = d₂ := heq.2; subst hd; rfl
  · intro ⟨a, b⟩ hab
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hab
    obtain ⟨⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩⟩, habN⟩ := hab
    refine ⟨⟨a * b, b⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
      exact ⟨⟨by nlinarith, habN⟩, dvd_mul_left b a, by positivity⟩
    · simp only [Prod.mk.injEq, and_true]
      exact Nat.mul_div_cancel a (by omega)
  · intro ⟨n, d⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx
    have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos hx.2.1 (by omega)
    have hq_pos : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd (by omega) hx.2.1) hd_pos
    have hmul : n / d * d = n := Nat.div_mul_cancel hx.2.1
    have hwn : w n = w (n / d) * w d := by
      conv_lhs => rw [← hmul]
      exact hw _ _ hq_pos hd_pos
    rw [hwn]; ring

private lemma dirichlet_hyperbola (f g w : ℕ → ℝ) {N U : ℕ} (hU1 : 1 ≤ U) (hUN : U ≤ N)
    (hw : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → w (a * b) = w a * w b) :
    ∑ n ∈ Icc 1 N, dconv f g n * w n =
      (∑ d ∈ Icc 1 U, g d * w d * ∑ k ∈ Icc 1 (N / d), f k * w k) +
      (∑ k ∈ Icc 1 (N / U), f k * w k * ∑ d ∈ Icc (U + 1) (N / k), g d * w d) := by
  rw [sum_dconv_eq_double f g w N hw]
  set S := (Icc 1 N ×ˢ Icc 1 N).filter (fun p => p.1 * p.2 ≤ N)
  set A := S.filter (fun p => p.1 ≤ U)
  set B := S.filter (fun p => U < p.1)
  have hAB_disj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hpA hpB
    simp only [A, B, Finset.mem_filter] at hpA hpB
    omega
  have hAB_union : A ∪ B = S := by
    ext p
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hp; by_cases h : p.1 ≤ U
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, by omega⟩
  rw [← hAB_union, Finset.sum_union hAB_disj]
  congr 1
  · trans (∑ d ∈ Icc 1 U, ∑ k ∈ Icc 1 (N / d), g d * w d * (f k * w k))
    · rw [Finset.sum_sigma']
      refine Finset.sum_bij (fun p _ => ⟨p.1, p.2⟩) ?_ ?_ ?_ ?_
      · intro ⟨d, k⟩ hp
        simp only [A, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
        simp only [Finset.mem_sigma, Finset.mem_Icc]
        refine ⟨⟨hp.1.1.1.1, hp.2⟩, ⟨hp.1.1.2.1, ?_⟩⟩
        exact (Nat.le_div_iff_mul_le (by omega : 0 < d)).mpr (by rw [mul_comm]; exact hp.1.2)
      · intro ⟨d₁, k₁⟩ _ ⟨d₂, k₂⟩ _ h
        simp only [Sigma.mk.inj_iff] at h
        obtain ⟨rfl, hk⟩ := h
        simp only [heq_eq_eq] at hk; rw [hk]
      · intro ⟨d, k⟩ hdk
        simp only [Finset.mem_sigma, Finset.mem_Icc] at hdk
        refine ⟨(d, k), ?_, rfl⟩
        simp only [A, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        have hdkN : d * k ≤ N := by
          have := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hdk.2.2
          linarith
        exact ⟨⟨⟨⟨hdk.1.1, hdk.1.2.trans hUN⟩, ⟨hdk.2.1, by nlinarith⟩⟩, hdkN⟩, hdk.1.2⟩
      · intro _ _; rfl
    · refine Finset.sum_congr rfl fun d _ => by rw [← Finset.mul_sum]
  · trans (∑ k ∈ Icc 1 (N / U), ∑ d ∈ Icc (U + 1) (N / k), f k * w k * (g d * w d))
    · rw [Finset.sum_sigma']
      refine Finset.sum_bij (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
      · intro ⟨d, k⟩ hp
        simp only [B, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
        simp only [Finset.mem_sigma, Finset.mem_Icc]
        have hkU : k ≤ N / U := by
          rw [Nat.le_div_iff_mul_le (by omega : 0 < U)]
          nlinarith
        have hdk : d ≤ N / k :=
          (Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr hp.1.2
        exact ⟨⟨hp.1.1.2.1, hkU⟩, ⟨by omega, hdk⟩⟩
      · intro ⟨d₁, k₁⟩ _ ⟨d₂, k₂⟩ _ h
        simp only [Sigma.mk.inj_iff] at h
        obtain ⟨rfl, hd⟩ := h
        simp only [heq_eq_eq] at hd; rw [hd]
      · intro ⟨k, d⟩ hkd
        simp only [Finset.mem_sigma, Finset.mem_Icc] at hkd
        refine ⟨(d, k), ?_, rfl⟩
        simp only [B, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        have hdkN : d * k ≤ N :=
          (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp hkd.2.2
        exact ⟨⟨⟨⟨by omega, by nlinarith⟩, ⟨hkd.1.1, by nlinarith⟩⟩, hdkN⟩, by omega⟩
      · intro ⟨d, k⟩ _; ring
    · refine Finset.sum_congr rfl fun k _ => by rw [← Finset.mul_sum]

private lemma sum_dconv_one_left (g : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, dconv (fun _ => 1) g n = ∑ d ∈ Icc 1 N, g d * ((N / d : ℕ) : ℝ) := by
  rcases eq_or_lt_of_le (Nat.zero_le N) with rfl | hN
  · simp
  · have h := dirichlet_hyperbola (fun _ => 1) g (fun _ => 1) hN le_rfl (fun _ _ _ _ => by ring)
    simp only [mul_one, one_mul, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at h
    rw [h]
    have h2 : ∑ k ∈ Icc 1 (N / N), ∑ d ∈ Icc (N + 1) (N / k), g d = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      simp only [Finset.mem_Icc] at hk
      have hdiv : N / k ≤ N := Nat.div_le_self N k
      have hemp : Icc (N + 1) (N / k) = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hemp, Finset.sum_empty]
    rw [h2, add_zero]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Nat.add_sub_cancel]

private lemma sum_tau_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, dconv (fun _ => 1) (fun _ => 1) n ≤ (N : ℝ) * (Real.log (N : ℝ) + 1) := by
  rw [sum_dconv_one_left]
  calc ∑ d ∈ Icc 1 N, (1 : ℝ) * ((N / d : ℕ) : ℝ)
      ≤ ∑ d ∈ Icc 1 N, (N : ℝ) * ((1 : ℝ) / (d : ℝ)) := by
        refine Finset.sum_le_sum fun d hd => ?_
        simp only [Finset.mem_Icc] at hd
        rw [one_mul, mul_one_div, le_div_iff₀ (by exact_mod_cast (by omega : 0 < d))]
        exact_mod_cast Nat.div_mul_le_self N d
    _ = (N : ℝ) * ∑ d ∈ Icc 1 N, (1 : ℝ) / (d : ℝ) := by rw [← Finset.mul_sum]
    _ ≤ (N : ℝ) * (Real.log (N : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (harmonic_le_log_add_one N hN) (by positivity)

private lemma sum_tau3_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, dconv (fun _ => 1) (dconv (fun _ => 1) (fun _ => 1)) n ≤
      (N : ℝ) * (Real.log (N : ℝ) + 1) ^ 2 := by
  have hcomm : ∀ n, dconv (fun _ => 1) (dconv (fun _ => 1) (fun _ => 1)) n =
      dconv (dconv (fun _ => 1) (fun _ => 1)) (fun _ => 1) n := fun n => dconv_comm _ _ n
  simp_rw [hcomm]
  have h := dirichlet_hyperbola (dconv (fun _ => 1) (fun _ => 1)) (fun _ => 1) (fun _ => 1)
    hN le_rfl (fun _ _ _ _ => by ring)
  simp only [mul_one, one_mul] at h
  rw [h]
  have h2 : ∑ k ∈ Icc 1 (N / N),
      dconv (fun _ => 1) (fun _ => 1) k * ∑ d ∈ Icc (N + 1) (N / k), (1 : ℝ) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hemp : Icc (N + 1) (N / k) = ∅ := Finset.Icc_eq_empty (by have := Nat.div_le_self N k; omega)
    rw [hemp, Finset.sum_empty, mul_zero]
  rw [h2, add_zero]
  calc ∑ d ∈ Icc 1 N, ∑ k ∈ Icc 1 (N / d), dconv (fun _ => 1) (fun _ => 1) k
      ≤ ∑ d ∈ Icc 1 N, ((N / d : ℕ) : ℝ) * (Real.log (N : ℝ) + 1) := by
        refine Finset.sum_le_sum fun d hd => ?_
        simp only [Finset.mem_Icc] at hd
        have hnd : 1 ≤ N / d := Nat.div_pos hd.2 hd.1
        have htau := sum_tau_le hnd
        have hlog : Real.log ((N / d : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
          Real.log_le_log (by exact_mod_cast hnd) (by exact_mod_cast Nat.div_le_self N d)
        exact htau.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    _ ≤ ∑ d ∈ Icc 1 N, ((N : ℝ) * ((1 : ℝ) / (d : ℝ))) * (Real.log (N : ℝ) + 1) := by
        refine Finset.sum_le_sum fun d hd => ?_
        simp only [Finset.mem_Icc] at hd
        have hlog_nn : 0 ≤ Real.log (N : ℝ) + 1 := by
          have : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
          linarith
        refine mul_le_mul_of_nonneg_right ?_ hlog_nn
        rw [mul_one_div, le_div_iff₀ (by exact_mod_cast (by omega : 0 < d))]
        exact_mod_cast Nat.div_mul_le_self N d
    _ = (N : ℝ) * (Real.log (N : ℝ) + 1) * ∑ d ∈ Icc 1 N, (1 : ℝ) / (d : ℝ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun d _ => by ring
    _ ≤ (N : ℝ) * (Real.log (N : ℝ) + 1) * (Real.log (N : ℝ) + 1) := by
        have hlog_nn : 0 ≤ Real.log (N : ℝ) + 1 := by
          have : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
          linarith
        exact mul_le_mul_of_nonneg_left (harmonic_le_log_add_one N hN) (by positivity)
    _ = (N : ℝ) * (Real.log (N : ℝ) + 1) ^ 2 := by ring

/- Abel summation (summation by parts) -/

private lemma sum_sub_succ_eq (w : ℕ → ℝ) {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    ∑ n ∈ Icc p (q - 1), (w n - w (n + 1)) = w p - w q := by
  induction q, hpq using Nat.le_induction with
  | base =>
    have hemp : Icc p (p - 1) = ∅ := Finset.Icc_eq_empty (by omega)
    simp [hemp]
  | succ m hpm ih =>
    have hm1 : m + 1 - 1 = m := by omega
    rw [hm1]
    rcases eq_or_lt_of_le hpm with rfl | hpm_lt
    · simp
    · have hIcc2 : Icc p m = insert m (Icc p (m - 1)) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc2, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih]
      ring

private lemma abel_sum_identity (a w : ℕ → ℝ) {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    ∑ n ∈ Icc p q, a n * w n =
      (∑ k ∈ Icc p q, a k) * w q +
      ∑ n ∈ Icc p (q - 1), (∑ k ∈ Icc p n, a k) * (w n - w (n + 1)) := by
  induction q, hpq using Nat.le_induction with
  | base =>
    have hemp : Icc p (p - 1) = ∅ := Finset.Icc_eq_empty (by omega)
    simp [hemp]
  | succ m hpm ih =>
    have hm1 : m + 1 - 1 = m := by omega
    have hIcc1 : Icc p (m + 1) = insert (m + 1) (Icc p m) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hm1, hIcc1, Finset.sum_insert (by simp), ih]
    have hsum_add : ∑ k ∈ insert (m + 1) (Icc p m), a k =
        a (m + 1) + ∑ k ∈ Icc p m, a k := Finset.sum_insert (by simp)
    rw [hsum_add]
    rcases eq_or_lt_of_le hpm with rfl | hpm_lt
    · have hemp : Icc p (p - 1) = ∅ := Finset.Icc_eq_empty (by omega)
      simp [hemp]; ring
    · have hIcc2 : Icc p m = insert m (Icc p (m - 1)) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hsum_sub : ∑ n ∈ Icc p m, (∑ k ∈ Icc p n, a k) * (w n - w (n + 1)) =
          (∑ k ∈ Icc p m, a k) * (w m - w (m + 1)) +
          ∑ n ∈ Icc p (m - 1), (∑ k ∈ Icc p n, a k) * (w n - w (n + 1)) := by
        conv_lhs => rw [hIcc2, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
      rw [hsum_sub]; ring

private lemma abel_antitone_bound (a w : ℕ → ℝ) {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q)
    {M : ℝ} (_hM : 0 ≤ M)
    (hB : ∀ n ∈ Icc p q, |∑ k ∈ Icc p n, a k| ≤ M)
    (hw_nn : ∀ n ∈ Icc p q, 0 ≤ w n)
    (hw_anti : ∀ n ∈ Icc p (q - 1), w (n + 1) ≤ w n) :
    |∑ n ∈ Icc p q, a n * w n| ≤ M * w p := by
  rw [abel_sum_identity a w hp hpq]
  have h1 : |(∑ k ∈ Icc p q, a k) * w q| ≤ M * w q := by
    rw [abs_mul, abs_of_nonneg (hw_nn q (Finset.mem_Icc.mpr ⟨hpq, le_rfl⟩))]
    exact mul_le_mul_of_nonneg_right (hB q (Finset.mem_Icc.mpr ⟨hpq, le_rfl⟩))
      (hw_nn q (Finset.mem_Icc.mpr ⟨hpq, le_rfl⟩))
  have h2 : |∑ n ∈ Icc p (q - 1), (∑ k ∈ Icc p n, a k) * (w n - w (n + 1))| ≤
      ∑ n ∈ Icc p (q - 1), M * (w n - w (n + 1)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    have hdiff : 0 ≤ w n - w (n + 1) := sub_nonneg.mpr (hw_anti n hn)
    rw [abs_mul, abs_of_nonneg hdiff]
    have hnq : n ∈ Icc p q := by
      simp only [Finset.mem_Icc] at hn ⊢; omega
    exact mul_le_mul_of_nonneg_right (hB n hnq) hdiff
  have htele : ∑ n ∈ Icc p (q - 1), M * (w n - w (n + 1)) = M * (w p - w q) := by
    rw [← Finset.mul_sum, sum_sub_succ_eq w hp hpq]
  calc |(∑ k ∈ Icc p q, a k) * w q +
        ∑ n ∈ Icc p (q - 1), (∑ k ∈ Icc p n, a k) * (w n - w (n + 1))|
      ≤ |(∑ k ∈ Icc p q, a k) * w q| +
        |∑ n ∈ Icc p (q - 1), (∑ k ∈ Icc p n, a k) * (w n - w (n + 1))| := abs_add_le _ _
    _ ≤ M * w q + M * (w p - w q) := by linarith
    _ = M * w p := by ring

private lemma abel_full_identity (a w : ℕ → ℝ) {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    ∑ n ∈ Icc p q, a n * w n =
      (∑ k ∈ Icc 1 q, a k) * w q - (∑ k ∈ Icc 1 (p - 1), a k) * w p +
      ∑ n ∈ Icc p (q - 1), (∑ k ∈ Icc 1 n, a k) * (w n - w (n + 1)) := by
  have hB : ∀ n, p ≤ n → ∑ k ∈ Icc p n, a k =
      (∑ k ∈ Icc 1 n, a k) - (∑ k ∈ Icc 1 (p - 1), a k) := by
    intro n hpn
    have hunion : Icc 1 n = Icc 1 (p - 1) ∪ Icc p n := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Icc 1 (p - 1)) (Icc p n) := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2; simp only [Finset.mem_Icc] at hk1 hk2; omega
    rw [hunion, Finset.sum_union hdisj]; ring
  rw [abel_sum_identity a w hp hpq, hB q hpq]
  have hsum : ∑ n ∈ Icc p (q - 1), (∑ k ∈ Icc p n, a k) * (w n - w (n + 1)) =
      (∑ n ∈ Icc p (q - 1), (∑ k ∈ Icc 1 n, a k) * (w n - w (n + 1))) -
      (∑ k ∈ Icc 1 (p - 1), a k) * (∑ n ∈ Icc p (q - 1), (w n - w (n + 1))) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_Icc] at hn
    rw [hB n hn.1]; ring
  rw [hsum, sum_sub_succ_eq w hp hpq]; ring

private lemma integral_rpow_neg_eq {α a b : ℝ} (hα : α ≠ 1) (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, t ^ (-α) = (a ^ (1 - α) - b ^ (1 - α)) / (α - 1) := by
  have h1 : 1 - α ≠ 0 := sub_ne_zero.mpr hα.symm
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => t ^ (1 - α) / (1 - α)) (x ^ (-α)) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx_pos : 0 < x := lt_of_lt_of_le ha hx.1
    have hd := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hx_pos.ne')).div_const (1 - α)
    have hval : (1 - α) * x ^ (1 - α - 1) / (1 - α) = x ^ (-α) := by
      have hexp : 1 - α - 1 = -α := by ring
      rw [hexp, mul_div_cancel_left₀ _ h1]
    rw [← hval]
    exact hd
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-α)) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro x hx
    exact (Real.continuousAt_rpow_const x (-α) (Or.inl (lt_of_lt_of_le ha hx.1).ne')).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  field_simp [h1]
  ring

private lemma abel_pow_tail_bound {a : ℕ → ℝ} {K s : ℝ} (hK : 0 ≤ K)
    (hA : ∀ n : ℕ, 1 ≤ n → |∑ k ∈ Icc 1 n, a k| ≤ K * (n : ℝ) ^ ((7 : ℝ) / 10))
    (hs1 : (49 : ℝ) / 50 ≤ s) {U Q : ℕ} (hU : 1 ≤ U) (hUQ : U < Q) :
    |∑ d ∈ Icc (U + 1) Q, a d * (d : ℝ) ^ (-s)| ≤
      K * ((Q : ℝ) ^ ((7 : ℝ) / 10 - s) + 5 * (U : ℝ) ^ ((7 : ℝ) / 10 - s)) := by
  rw [abel_full_identity a (fun n => (n : ℝ) ^ (-s)) (by omega) (by omega)]
  have hU_sub : U + 1 - 1 = U := by omega
  rw [hU_sub]
  have hQ_pos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
  have hU_pos : (0 : ℝ) < (U : ℝ) := by exact_mod_cast (by omega : 0 < U)
  have hU1_pos : (0 : ℝ) < ((U + 1 : ℕ) : ℝ) := by positivity
  have ht1 : |(∑ k ∈ Icc 1 Q, a k) * (Q : ℝ) ^ (-s)| ≤ K * (Q : ℝ) ^ ((7 : ℝ) / 10 - s) := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hQ_pos.le _)]
    calc |∑ k ∈ Icc 1 Q, a k| * (Q : ℝ) ^ (-s)
        ≤ (K * (Q : ℝ) ^ ((7 : ℝ) / 10)) * (Q : ℝ) ^ (-s) :=
          mul_le_mul_of_nonneg_right (hA Q (by omega)) (Real.rpow_nonneg hQ_pos.le _)
      _ = K * (Q : ℝ) ^ ((7 : ℝ) / 10 - s) := by
          rw [mul_assoc, ← Real.rpow_add hQ_pos, sub_eq_add_neg]
  have ht2 : |(∑ k ∈ Icc 1 U, a k) * ((U + 1 : ℕ) : ℝ) ^ (-s)| ≤
      K * (U : ℝ) ^ ((7 : ℝ) / 10 - s) := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hU1_pos.le _)]
    have hpow_le : ((U + 1 : ℕ) : ℝ) ^ (-s) ≤ (U : ℝ) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos hU_pos (by exact_mod_cast Nat.le_succ U) (by linarith)
    calc |∑ k ∈ Icc 1 U, a k| * ((U + 1 : ℕ) : ℝ) ^ (-s)
        ≤ (K * (U : ℝ) ^ ((7 : ℝ) / 10)) * (U : ℝ) ^ (-s) :=
          mul_le_mul (hA U hU) hpow_le (Real.rpow_nonneg hU1_pos.le _) (by positivity)
      _ = K * (U : ℝ) ^ ((7 : ℝ) / 10 - s) := by
          rw [mul_assoc, ← Real.rpow_add hU_pos, sub_eq_add_neg]
  have ht3 : |∑ d ∈ Icc (U + 1) (Q - 1),
        (∑ k ∈ Icc 1 d, a k) * ((d : ℝ) ^ (-s) - ((d + 1 : ℕ) : ℝ) ^ (-s))| ≤
      4 * K * (U : ℝ) ^ ((7 : ℝ) / 10 - s) := by
    have hterm : ∀ d ∈ Icc (U + 1) (Q - 1),
        |(∑ k ∈ Icc 1 d, a k) * ((d : ℝ) ^ (-s) - ((d + 1 : ℕ) : ℝ) ^ (-s))| ≤
          K * s * ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ), t ^ ((7 : ℝ) / 10 - s - 1) := by
      intro d hd
      simp only [Finset.mem_Icc] at hd
      have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
      have hd1_le : (d : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ d
      have hdiff_eq : (d : ℝ) ^ (-s) - ((d + 1 : ℕ) : ℝ) ^ (-s) =
          s * ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ), t ^ (-(s + 1)) := by
        rw [integral_rpow_neg_eq (by linarith) hd_pos hd1_le]
        have h1 : 1 - (s + 1) = -s := by ring
        have h2 : s + 1 - 1 = s := by ring
        rw [h1, h2, mul_div_cancel₀ _ (by linarith)]
      have hdiff_nn : 0 ≤ (d : ℝ) ^ (-s) - ((d + 1 : ℕ) : ℝ) ^ (-s) := by
        exact sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos hd_pos hd1_le (by linarith))
      rw [abs_mul, abs_of_nonneg hdiff_nn, hdiff_eq]
      calc |∑ k ∈ Icc 1 d, a k| * (s * ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ), t ^ (-(s + 1)))
          ≤ (K * (d : ℝ) ^ ((7 : ℝ) / 10)) *
              (s * ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ), t ^ (-(s + 1))) := by
            refine mul_le_mul_of_nonneg_right (hA d (by omega)) ?_
            rw [← hdiff_eq]; exact hdiff_nn
        _ = K * s * ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ),
              (d : ℝ) ^ ((7 : ℝ) / 10) * t ^ (-(s + 1)) := by
            rw [intervalIntegral.integral_const_mul]; ring
        _ ≤ K * s * ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ), t ^ ((7 : ℝ) / 10 - s - 1) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine intervalIntegral.integral_mono_on hd1_le ?_ ?_ fun t ht => ?_
            · refine ContinuousOn.intervalIntegrable ?_
              rw [Set.uIcc_of_le hd1_le]
              intro t ht
              exact (continuousAt_const.mul (Real.continuousAt_rpow_const t (-(s + 1))
                (Or.inl (lt_of_lt_of_le hd_pos ht.1).ne'))).continuousWithinAt
            · refine ContinuousOn.intervalIntegrable ?_
              rw [Set.uIcc_of_le hd1_le]
              intro t ht
              exact (Real.continuousAt_rpow_const t _
                (Or.inl (lt_of_lt_of_le hd_pos ht.1).ne')).continuousWithinAt
            · have ht_pos : 0 < t := lt_of_lt_of_le hd_pos ht.1
              have hdt : (d : ℝ) ^ ((7 : ℝ) / 10) ≤ t ^ ((7 : ℝ) / 10) :=
                Real.rpow_le_rpow hd_pos.le ht.1 (by norm_num)
              calc (d : ℝ) ^ ((7 : ℝ) / 10) * t ^ (-(s + 1))
                  ≤ t ^ ((7 : ℝ) / 10) * t ^ (-(s + 1)) :=
                    mul_le_mul_of_nonneg_right hdt (Real.rpow_nonneg ht_pos.le _)
                _ = t ^ ((7 : ℝ) / 10 - s - 1) := by
                    rw [← Real.rpow_add ht_pos]; congr 1; ring
    have hsum_int : ∀ m : ℕ, U + 1 ≤ m →
        ∑ d ∈ Icc (U + 1) (m - 1), ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ), t ^ ((7 : ℝ) / 10 - s - 1) =
          ∫ t in ((U + 1 : ℕ) : ℝ)..(m : ℝ), t ^ ((7 : ℝ) / 10 - s - 1) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => simp
      | succ k hk ih =>
        have hk1 : k + 1 - 1 = k := by omega
        rw [hk1]
        have hIcc : Icc (U + 1) k = insert k (Icc (U + 1) (k - 1)) := by
          ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih, add_comm]
        have hint : ∀ a b : ℝ, 0 < a → a ≤ b →
            IntervalIntegrable (fun t : ℝ => t ^ ((7 : ℝ) / 10 - s - 1)) MeasureTheory.volume a b := by
          intro a b ha hab
          refine ContinuousOn.intervalIntegrable ?_
          rw [Set.uIcc_of_le hab]
          intro t ht
          exact (Real.continuousAt_rpow_const t _
            (Or.inl (lt_of_lt_of_le ha ht.1).ne')).continuousWithinAt
        exact intervalIntegral.integral_add_adjacent_intervals
          (hint ((U + 1 : ℕ) : ℝ) (k : ℝ) (by positivity) (by exact_mod_cast hk))
          (hint (k : ℝ) ((k + 1 : ℕ) : ℝ) (by exact_mod_cast (by omega : 0 < k))
            (by exact_mod_cast Nat.le_succ k))
    calc |∑ d ∈ Icc (U + 1) (Q - 1),
            (∑ k ∈ Icc 1 d, a k) * ((d : ℝ) ^ (-s) - ((d + 1 : ℕ) : ℝ) ^ (-s))|
        ≤ ∑ d ∈ Icc (U + 1) (Q - 1),
            |(∑ k ∈ Icc 1 d, a k) * ((d : ℝ) ^ (-s) - ((d + 1 : ℕ) : ℝ) ^ (-s))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc (U + 1) (Q - 1),
            K * s * ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ), t ^ ((7 : ℝ) / 10 - s - 1) :=
          Finset.sum_le_sum hterm
      _ = K * s * ∫ t in ((U + 1 : ℕ) : ℝ)..(Q : ℝ), t ^ ((7 : ℝ) / 10 - s - 1) := by
          rw [← Finset.mul_sum, hsum_int Q (by omega)]
      _ = K * s * ((((U + 1 : ℕ) : ℝ) ^ ((7 : ℝ) / 10 - s) - (Q : ℝ) ^ ((7 : ℝ) / 10 - s)) /
            (s - (7 : ℝ) / 10)) := by
          have heq : (fun t : ℝ => t ^ ((7 : ℝ) / 10 - s - 1)) =
              (fun t : ℝ => t ^ (-(s + 1 - (7 : ℝ) / 10))) := by
            ext t; congr 1; ring
          rw [heq, integral_rpow_neg_eq (by linarith) hU1_pos (by exact_mod_cast (by omega : U + 1 ≤ Q))]
          have h1 : 1 - (s + 1 - (7 : ℝ) / 10) = (7 : ℝ) / 10 - s := by ring
          have h2 : s + 1 - (7 : ℝ) / 10 - 1 = s - (7 : ℝ) / 10 := by ring
          rw [h1, h2]
      _ ≤ K * s * (((U + 1 : ℕ) : ℝ) ^ ((7 : ℝ) / 10 - s) / (s - (7 : ℝ) / 10)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine div_le_div_of_nonneg_right ?_ (by linarith)
          linarith [Real.rpow_nonneg hQ_pos.le ((7 : ℝ) / 10 - s)]
      _ ≤ 4 * K * (U : ℝ) ^ ((7 : ℝ) / 10 - s) := by
          have hpow : ((U + 1 : ℕ) : ℝ) ^ ((7 : ℝ) / 10 - s) ≤ (U : ℝ) ^ ((7 : ℝ) / 10 - s) :=
            Real.rpow_le_rpow_of_nonpos hU_pos (by exact_mod_cast Nat.le_succ U) (by linarith)
          have hcoef : s / (s - (7 : ℝ) / 10) ≤ 4 := by
            rw [div_le_iff₀ (by linarith)]; linarith
          have h1 : K * s * (((U + 1 : ℕ) : ℝ) ^ ((7 : ℝ) / 10 - s) / (s - (7 : ℝ) / 10)) =
              K * (s / (s - (7 : ℝ) / 10)) * ((U + 1 : ℕ) : ℝ) ^ ((7 : ℝ) / 10 - s) := by ring
          rw [h1]
          calc K * (s / (s - (7 : ℝ) / 10)) * ((U + 1 : ℕ) : ℝ) ^ ((7 : ℝ) / 10 - s)
              ≤ K * 4 * (U : ℝ) ^ ((7 : ℝ) / 10 - s) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hcoef hK) hpow
                  (Real.rpow_nonneg hU1_pos.le _) (by positivity)
            _ = 4 * K * (U : ℝ) ^ ((7 : ℝ) / 10 - s) := by ring
  calc |(∑ k ∈ Icc 1 Q, a k) * (Q : ℝ) ^ (-s) -
        (∑ k ∈ Icc 1 U, a k) * ((U + 1 : ℕ) : ℝ) ^ (-s) +
        ∑ d ∈ Icc (U + 1) (Q - 1),
          (∑ k ∈ Icc 1 d, a k) * ((d : ℝ) ^ (-s) - ((d + 1 : ℕ) : ℝ) ^ (-s))|
      ≤ |(∑ k ∈ Icc 1 Q, a k) * (Q : ℝ) ^ (-s) -
          (∑ k ∈ Icc 1 U, a k) * ((U + 1 : ℕ) : ℝ) ^ (-s)| +
        |∑ d ∈ Icc (U + 1) (Q - 1),
          (∑ k ∈ Icc 1 d, a k) * ((d : ℝ) ^ (-s) - ((d + 1 : ℕ) : ℝ) ^ (-s))| := abs_add_le _ _
    _ ≤ |(∑ k ∈ Icc 1 Q, a k) * (Q : ℝ) ^ (-s)| +
        |(∑ k ∈ Icc 1 U, a k) * ((U + 1 : ℕ) : ℝ) ^ (-s)| +
        |∑ d ∈ Icc (U + 1) (Q - 1),
          (∑ k ∈ Icc 1 d, a k) * ((d : ℝ) ^ (-s) - ((d + 1 : ℕ) : ℝ) ^ (-s))| := by
        linarith [abs_sub ((∑ k ∈ Icc 1 Q, a k) * (Q : ℝ) ^ (-s))
          ((∑ k ∈ Icc 1 U, a k) * ((U + 1 : ℕ) : ℝ) ^ (-s))]
    _ ≤ K * (Q : ℝ) ^ ((7 : ℝ) / 10 - s) + K * (U : ℝ) ^ ((7 : ℝ) / 10 - s) +
        4 * K * (U : ℝ) ^ ((7 : ℝ) / 10 - s) := by linarith
    _ = K * ((Q : ℝ) ^ ((7 : ℝ) / 10 - s) + 5 * (U : ℝ) ^ ((7 : ℝ) / 10 - s)) := by ring

/- Real Dirichlet L-functions and derivatives -/

private noncomputable def Lpartial (a : ℕ → ℝ) (N : ℕ) (s : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, a n * (n : ℝ) ^ (-s)

private noncomputable def Lval (a : ℕ → ℝ) (s : ℝ) : ℝ :=
  limUnder atTop (fun N => Lpartial a N s)

private noncomputable def LderivPartial (a : ℕ → ℝ) (N : ℕ) (s : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, -(a n * Real.log (n : ℝ) * (n : ℝ) ^ (-s))

private noncomputable def Lderiv (a : ℕ → ℝ) (s : ℝ) : ℝ :=
  limUnder atTop (fun N => LderivPartial a N s)

private lemma rpow_neg_tendsto_zero {s : ℝ} (hs : 0 < s) :
    Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) ^ (-s)) atTop (nhds 0) := by
  have h1 : Tendsto (fun N : ℕ => Real.log ((N + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
  have h2 : Tendsto (fun N : ℕ => -s * Real.log ((N + 1 : ℕ) : ℝ)) atTop atBot :=
    (Filter.Tendsto.const_mul_atTop_of_neg (by linarith) h1)
  have h3 : Tendsto (fun N : ℕ => Real.exp (-s * Real.log ((N + 1 : ℕ) : ℝ))) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp h2
  refine h3.congr fun N => ?_
  rw [Real.rpow_def_of_pos (by positivity)]
  congr 1; ring

private lemma log_mul_rpow_neg_antitone {s : ℝ} (hs : 0 < s) {a b : ℝ}
    (ha : 1 ≤ s * Real.log a) (ha_pos : 0 < a) (hab : a ≤ b) :
    Real.log b * b ^ (-s) ≤ Real.log a * a ^ (-s) := by
  have hderiv : ∀ x ∈ Set.Icc a b,
      HasDerivAt (fun t : ℝ => Real.log t * t ^ (-s))
        (x ^ (-s - 1) * (1 - s * Real.log x)) x := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hx.1
    have hd1 : HasDerivAt Real.log (x⁻¹) x := Real.hasDerivAt_log hx_pos.ne'
    have hd2 : HasDerivAt (fun t : ℝ => t ^ (-s)) (-s * x ^ (-s - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx_pos.ne')
    have hval : x⁻¹ * x ^ (-s) + Real.log x * (-s * x ^ (-s - 1)) =
        x ^ (-s - 1) * (1 - s * Real.log x) := by
      have hpow : x⁻¹ * x ^ (-s) = x ^ (-s - 1) := by
        rw [← Real.rpow_neg_one x, ← Real.rpow_add hx_pos]; congr 1; ring
      rw [hpow]; ring
    rw [← hval]
    exact hd1.mul hd2
  have hanti : AntitoneOn (fun t : ℝ => Real.log t * t ^ (-s)) (Set.Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a b) ?_ ?_ ?_
    · intro x hx
      exact (hderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Set.Icc a b := interior_subset hx
      rw [(hderiv x hx').deriv]
      have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hx'.1
      have hlog : Real.log a ≤ Real.log x := Real.log_le_log ha_pos hx'.1
      have hnonpos : 1 - s * Real.log x ≤ 0 := by nlinarith
      exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hx_pos.le _) hnonpos
  exact hanti ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

private lemma Lpartial_sub_eq (a : ℕ → ℝ) (s : ℝ) {N Q : ℕ} (hNQ : N < Q) :
    Lpartial a Q s - Lpartial a N s = ∑ n ∈ Icc (N + 1) Q, a n * (n : ℝ) ^ (-s) := by
  unfold Lpartial
  have hunion : Icc 1 Q = Icc 1 N ∪ Icc (N + 1) Q := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Icc 1 N) (Icc (N + 1) Q) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2; simp only [Finset.mem_Icc] at hk1 hk2; omega
  rw [hunion, Finset.sum_union hdisj]; ring

private lemma LderivPartial_sub_eq (a : ℕ → ℝ) (s : ℝ) {N Q : ℕ} (hNQ : N < Q) :
    LderivPartial a Q s - LderivPartial a N s =
      -(∑ n ∈ Icc (N + 1) Q, a n * (Real.log (n : ℝ) * (n : ℝ) ^ (-s))) := by
  unfold LderivPartial
  have hunion : Icc 1 Q = Icc 1 N ∪ Icc (N + 1) Q := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Icc 1 N) (Icc (N + 1) Q) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2; simp only [Finset.mem_Icc] at hk1 hk2; omega
  rw [hunion, Finset.sum_union hdisj, add_sub_cancel_left, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n _ => by ring

private lemma tendsto_Lval {χ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hχ : ∀ a b : ℕ, |∑ n ∈ Icc a b, χ n| ≤ M) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun N => Lpartial χ N s) atTop (nhds (Lval χ s)) := by
  have hcauchy : CauchySeq (fun N => Lpartial χ N s) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hlim : Tendsto (fun N : ℕ => M * ((N + 1 : ℕ) : ℝ) ^ (-s)) atTop (nhds 0) := by
      simpa using (rpow_neg_tendsto_zero hs).const_mul M
    obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hlim) ε hε
    refine ⟨N₀, fun m hm n hn => ?_⟩
    rw [Real.dist_eq]
    rcases lt_trichotomy m n with hlt | rfl | hgt
    · rw [abs_sub_comm, Lpartial_sub_eq χ s hlt]
      have hb : |∑ k ∈ Icc (m + 1) n, χ k * (k : ℝ) ^ (-s)| ≤ M * ((m + 1 : ℕ) : ℝ) ^ (-s) :=
        abel_antitone_bound χ (fun k => (k : ℝ) ^ (-s)) (by omega) (by omega) hM
          (fun k _ => hχ (m + 1) k)
          (fun k _ => Real.rpow_nonneg (by positivity) _)
          (fun k hk => Real.rpow_le_rpow_of_nonpos
            (by exact_mod_cast (by simp only [Finset.mem_Icc] at hk; omega : 0 < k))
            (by exact_mod_cast Nat.le_succ k) (by linarith))
      have hε' := hN₀ m hm
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hε'
      exact hb.trans_lt hε'
    · simpa using hε
    · rw [Lpartial_sub_eq χ s hgt]
      have hb : |∑ k ∈ Icc (n + 1) m, χ k * (k : ℝ) ^ (-s)| ≤ M * ((n + 1 : ℕ) : ℝ) ^ (-s) :=
        abel_antitone_bound χ (fun k => (k : ℝ) ^ (-s)) (by omega) (by omega) hM
          (fun k _ => hχ (n + 1) k)
          (fun k _ => Real.rpow_nonneg (by positivity) _)
          (fun k hk => Real.rpow_le_rpow_of_nonpos
            (by exact_mod_cast (by simp only [Finset.mem_Icc] at hk; omega : 0 < k))
            (by exact_mod_cast Nat.le_succ k) (by linarith))
      have hε' := hN₀ n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hε'
      exact hb.trans_lt hε'
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hEq : Lval χ s = L := hL.limUnder_eq
  rw [hEq]; exact hL

private lemma abs_Lval_sub_partial_le {χ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hχ : ∀ a b : ℕ, |∑ n ∈ Icc a b, χ n| ≤ M) {s : ℝ} (hs : 0 < s) (N : ℕ) :
    |Lval χ s - Lpartial χ N s| ≤ M * ((N + 1 : ℕ) : ℝ) ^ (-s) := by
  have hlim : Tendsto (fun Q => |Lpartial χ Q s - Lpartial χ N s|) atTop
      (nhds |Lval χ s - Lpartial χ N s|) :=
    ((tendsto_Lval hM hχ hs).sub_const _).abs
  refine le_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_gt_atTop N] with Q hQ
  rw [Lpartial_sub_eq χ s hQ]
  exact abel_antitone_bound χ (fun k => (k : ℝ) ^ (-s)) (by omega) (by omega) hM
    (fun k _ => hχ (N + 1) k)
    (fun k _ => Real.rpow_nonneg (by positivity) _)
    (fun k hk => Real.rpow_le_rpow_of_nonpos
      (by exact_mod_cast (by simp only [Finset.mem_Icc] at hk; omega : 0 < k))
      (by exact_mod_cast Nat.le_succ k) (by linarith))

private lemma tendsto_Lderiv_and_uniform {χ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hχ : ∀ a b : ℕ, |∑ n ∈ Icc a b, χ n| ≤ M) :
    (∀ s ∈ Set.Ioo ((1 : ℝ) / 2) 2,
      Tendsto (fun N => LderivPartial χ N s) atTop (nhds (Lderiv χ s))) ∧
    TendstoUniformlyOn (LderivPartial χ) (Lderiv χ) atTop (Set.Ioo ((1 : ℝ) / 2) 2) := by
  have hlog8 : (2 : ℝ) < Real.log (8 : ℝ) := by
    have h8 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) := by norm_num
    rw [h8, Real.log_pow]; push_cast
    linarith [Real.log_two_gt_d9]
  have hdiff_bound : ∀ s ∈ Set.Ioo ((1 : ℝ) / 2) 2, ∀ N Q : ℕ, 7 ≤ N → N < Q →
      |LderivPartial χ Q s - LderivPartial χ N s| ≤
        M * Real.log ((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) ^ (-s) := by
    intro s hs N Q hN hNQ
    rw [LderivPartial_sub_eq χ s hNQ, abs_neg, mul_assoc]
    refine abel_antitone_bound χ (fun k => Real.log (k : ℝ) * (k : ℝ) ^ (-s)) (by omega) (by omega) hM
      (fun k _ => hχ (N + 1) k) ?_ ?_
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      exact mul_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k)))
        (Real.rpow_nonneg (by positivity) _)
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      have hk8 : (8 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 8 ≤ k)
      have hlogk : (2 : ℝ) < Real.log (k : ℝ) :=
        hlog8.trans_le (Real.log_le_log (by norm_num) hk8)
      have hsl : 1 ≤ s * Real.log (k : ℝ) := by nlinarith [hs.1]
      exact log_mul_rpow_neg_antitone (by linarith [hs.1]) hsl
        (by exact_mod_cast (by omega : 0 < k)) (by exact_mod_cast Nat.le_succ k)
  have hbound_unif : Tendsto (fun N : ℕ => M * (4 * ((N + 1 : ℕ) : ℝ) ^ (-(2 : ℝ) / 5)))
      atTop (nhds 0) := by
    have h := (rpow_neg_tendsto_zero (by norm_num : (0 : ℝ) < (2 : ℝ) / 5)).const_mul (M * 4)
    simpa [mul_assoc, neg_div] using h
  have hstep_le : ∀ s ∈ Set.Ioo ((1 : ℝ) / 2) 2, ∀ N : ℕ, 7 ≤ N →
      M * Real.log ((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) ^ (-s) ≤
        M * (4 * ((N + 1 : ℕ) : ℝ) ^ (-(2 : ℝ) / 5)) := by
    intro s hs N hN
    have hx : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N + 1)
    have hlog : Real.log ((N + 1 : ℕ) : ℝ) ≤ 4 * ((N + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 10) :=
      log_le_4_rpow (by linarith)
    have hpow : ((N + 1 : ℕ) : ℝ) ^ (-s) ≤ ((N + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith [hs.1])
    calc M * Real.log ((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) ^ (-s)
        ≤ M * (4 * ((N + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 10)) *
            ((N + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hlog hM) hpow
            (Real.rpow_nonneg (by linarith) _) (by positivity)
      _ = M * (4 * ((N + 1 : ℕ) : ℝ) ^ (-(2 : ℝ) / 5)) := by
          rw [mul_assoc, mul_assoc, ← Real.rpow_add (by linarith)]; congr 3; ring
  have hpt : ∀ s ∈ Set.Ioo ((1 : ℝ) / 2) 2,
      Tendsto (fun N => LderivPartial χ N s) atTop (nhds (Lderiv χ s)) := by
    intro s hs
    have hcauchy : CauchySeq (fun N => LderivPartial χ N s) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hbound_unif) ε hε
      refine ⟨max 7 N₀, fun m hm n hn => ?_⟩
      rw [Real.dist_eq]
      rcases lt_trichotomy m n with hlt | rfl | hgt
      · rw [abs_sub_comm]
        have h1 := (hdiff_bound s hs m n (le_trans (le_max_left _ _) hm) hlt).trans
          (hstep_le s hs m (le_trans (le_max_left _ _) hm))
        have h2 := hN₀ m (le_trans (le_max_right _ _) hm)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h2
        exact h1.trans_lt h2
      · simpa using hε
      · have h1 := (hdiff_bound s hs n m (le_trans (le_max_left _ _) hn) hgt).trans
          (hstep_le s hs n (le_trans (le_max_left _ _) hn))
        have h2 := hN₀ n (le_trans (le_max_right _ _) hn)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h2
        exact h1.trans_lt h2
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
    have hEq : Lderiv χ s = L := hL.limUnder_eq
    rw [hEq]; exact hL
  refine ⟨hpt, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hbound_unif) (ε / 2) (by linarith)
  filter_upwards [Filter.eventually_ge_atTop (max 7 N₀)] with N hN s hs
  rw [Real.dist_eq]
  have hlim : Tendsto (fun Q => |LderivPartial χ Q s - LderivPartial χ N s|) atTop
      (nhds |Lderiv χ s - LderivPartial χ N s|) :=
    ((hpt s hs).sub_const _).abs
  have hle : |Lderiv χ s - LderivPartial χ N s| ≤
      M * (4 * ((N + 1 : ℕ) : ℝ) ^ (-(2 : ℝ) / 5)) := by
    refine le_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_gt_atTop N] with Q hQ
    exact (hdiff_bound s hs N Q (le_trans (le_max_left _ _) hN) hQ).trans
      (hstep_le s hs N (le_trans (le_max_left _ _) hN))
  have h2 := hN₀ N (le_trans (le_max_right _ _) hN)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h2
  linarith

private lemma hasDerivAt_Lval {χ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hχ : ∀ a b : ℕ, |∑ n ∈ Icc a b, χ n| ≤ M)
    {s : ℝ} (hs : s ∈ Set.Ioo ((1 : ℝ) / 2) 2) :
    HasDerivAt (Lval χ) (Lderiv χ s) s := by
  have hunif := (tendsto_Lderiv_and_uniform hM hχ).2
  refine hasDerivAt_of_tendstoUniformlyOn (f := Lpartial χ) isOpen_Ioo hunif ?_ ?_ hs
  · refine Filter.Eventually.of_forall fun N x _ => ?_
    unfold Lpartial LderivPartial
    have hterm : ∀ n ∈ Icc 1 N,
        HasDerivAt (fun t : ℝ => χ n * (n : ℝ) ^ (-t))
          (-(χ n * Real.log (n : ℝ) * (n : ℝ) ^ (-x))) x := by
      intro n hn
      simp only [Finset.mem_Icc] at hn
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have heq : (fun t : ℝ => χ n * (n : ℝ) ^ (-t)) =
          (fun t : ℝ => χ n * Real.exp (-t * Real.log (n : ℝ))) := by
        ext t; rw [Real.rpow_def_of_pos hn_pos]; congr 2; ring
      rw [heq]
      have hd : HasDerivAt (fun t : ℝ => -t * Real.log (n : ℝ)) (-Real.log (n : ℝ)) x := by
        simpa using ((hasDerivAt_id x).neg).mul_const (Real.log (n : ℝ))
      have hd2 := (hd.exp).const_mul (χ n)
      have hval : χ n * (Real.exp (-x * Real.log (n : ℝ)) * -Real.log (n : ℝ)) =
          -(χ n * Real.log (n : ℝ) * (n : ℝ) ^ (-x)) := by
        rw [Real.rpow_def_of_pos hn_pos]
        have : Real.log (n : ℝ) * -x = -x * Real.log (n : ℝ) := by ring
        rw [this]; ring
      rw [← hval]
      exact hd2
    exact HasDerivAt.fun_sum hterm
  · intro x hx
    exact tendsto_Lval hM hχ (by linarith [hx.1])

private lemma continuousOn_Lval {χ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hχ : ∀ a b : ℕ, |∑ n ∈ Icc a b, χ n| ≤ M) :
    ContinuousOn (Lval χ) (Set.Icc ((49 : ℝ) / 50) 1) := by
  intro s hs
  exact (hasDerivAt_Lval hM hχ ⟨by linarith [hs.1], by linarith [hs.2]⟩).continuousAt.continuousWithinAt

private lemma abs_Lval_one_le {χ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hχ : ∀ a b : ℕ, |∑ n ∈ Icc a b, χ n| ≤ M) (hχ1 : ∀ n, |χ n| ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    |Lval χ 1| ≤ (Real.log (N : ℝ) + 1) + M / ((N + 1 : ℕ) : ℝ) := by
  have htail := abs_Lval_sub_partial_le hM hχ (by norm_num : (0 : ℝ) < 1) N
  rw [Real.rpow_neg_one, ← div_eq_mul_inv] at htail
  have hpart : |Lpartial χ N 1| ≤ Real.log (N : ℝ) + 1 := by
    unfold Lpartial
    calc |∑ n ∈ Icc 1 N, χ n * (n : ℝ) ^ (-(1 : ℝ))|
        ≤ ∑ n ∈ Icc 1 N, |χ n * (n : ℝ) ^ (-(1 : ℝ))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Icc 1 N, (1 : ℝ) / (n : ℝ) := by
          refine Finset.sum_le_sum fun n _ => ?_
          have hinv_nn : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
          rw [abs_mul, Real.rpow_neg_one, abs_of_nonneg hinv_nn, one_div]
          calc |χ n| * (n : ℝ)⁻¹ ≤ 1 * (n : ℝ)⁻¹ :=
                mul_le_mul_of_nonneg_right (hχ1 n) hinv_nn
            _ = (n : ℝ)⁻¹ := one_mul _
      _ ≤ Real.log (N : ℝ) + 1 := harmonic_le_log_add_one N hN
  calc |Lval χ 1| = |(Lval χ 1 - Lpartial χ N 1) + Lpartial χ N 1| := by ring_nf
    _ ≤ |Lval χ 1 - Lpartial χ N 1| + |Lpartial χ N 1| := abs_add_le _ _
    _ ≤ (Real.log (N : ℝ) + 1) + M / ((N + 1 : ℕ) : ℝ) := by linarith

private lemma abs_Lderiv_le {χ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hχ : ∀ a b : ℕ, |∑ n ∈ Icc a b, χ n| ≤ M) (hχ1 : ∀ n, |χ n| ≤ 1)
    {s : ℝ} (hs1 : (49 : ℝ) / 50 ≤ s) (hs2 : s ≤ 1) {N : ℕ} (hN : 4 ≤ N) :
    |Lderiv χ s| ≤
      (N : ℝ) ^ (1 - s) * Real.log (N : ℝ) * (Real.log (N : ℝ) + 1) +
      M * Real.log ((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) ^ (-s) := by
  have hlog4 : (50 : ℝ) / 49 < Real.log (4 : ℝ) := by
    have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [h4, Real.log_pow]; push_cast
    linarith [Real.log_two_gt_d9]
  have htail : |Lderiv χ s - LderivPartial χ N s| ≤
      M * Real.log ((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) ^ (-s) := by
    have hlim : Tendsto (fun Q => |LderivPartial χ Q s - LderivPartial χ N s|) atTop
        (nhds |Lderiv χ s - LderivPartial χ N s|) :=
      (((tendsto_Lderiv_and_uniform hM hχ).1 s ⟨by linarith, by linarith⟩).sub_const _).abs
    refine le_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_gt_atTop N] with Q hQ
    rw [LderivPartial_sub_eq χ s hQ, abs_neg, mul_assoc]
    refine abel_antitone_bound χ (fun k => Real.log (k : ℝ) * (k : ℝ) ^ (-s)) (by omega) (by omega) hM
      (fun k _ => hχ (N + 1) k) ?_ ?_
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      exact mul_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k)))
        (Real.rpow_nonneg (by positivity) _)
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      have hk4 : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 4 ≤ k)
      have hlogk : (50 : ℝ) / 49 < Real.log (k : ℝ) :=
        hlog4.trans_le (Real.log_le_log (by norm_num) hk4)
      have hsl : 1 ≤ s * Real.log (k : ℝ) := by nlinarith
      exact log_mul_rpow_neg_antitone (by linarith) hsl
        (by exact_mod_cast (by omega : 0 < k)) (by exact_mod_cast Nat.le_succ k)
  have hpart : |LderivPartial χ N s| ≤
      (N : ℝ) ^ (1 - s) * Real.log (N : ℝ) * (Real.log (N : ℝ) + 1) := by
    unfold LderivPartial
    calc |∑ n ∈ Icc 1 N, -(χ n * Real.log (n : ℝ) * (n : ℝ) ^ (-s))|
        ≤ ∑ n ∈ Icc 1 N, |-(χ n * Real.log (n : ℝ) * (n : ℝ) ^ (-s))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Icc 1 N, Real.log (N : ℝ) * (n : ℝ) ^ (-s) := by
          refine Finset.sum_le_sum fun n hn => ?_
          simp only [Finset.mem_Icc] at hn
          rw [abs_neg, abs_mul, abs_mul,
            abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hn.1)),
            abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
          have hlog : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
            Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hn.2)
          have h1 : |χ n| * Real.log (n : ℝ) ≤ Real.log (N : ℝ) := by
            calc |χ n| * Real.log (n : ℝ) ≤ 1 * Real.log (n : ℝ) :=
                  mul_le_mul_of_nonneg_right (hχ1 n) (Real.log_nonneg (by exact_mod_cast hn.1))
              _ = Real.log (n : ℝ) := one_mul _
              _ ≤ Real.log (N : ℝ) := hlog
          exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (by positivity) _)
      _ = Real.log (N : ℝ) * ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-s) := by rw [← Finset.mul_sum]
      _ ≤ Real.log (N : ℝ) * ((N : ℝ) ^ (1 - s) * (Real.log (N : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (sum_rpow_neg_le hs2 (by omega))
            (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N)))
      _ = (N : ℝ) ^ (1 - s) * Real.log (N : ℝ) * (Real.log (N : ℝ) + 1) := by ring
  calc |Lderiv χ s| = |(Lderiv χ s - LderivPartial χ N s) + LderivPartial χ N s| := by ring_nf
    _ ≤ |Lderiv χ s - LderivPartial χ N s| + |LderivPartial χ N s| := abs_add_le _ _
    _ ≤ _ := by linarith

/- Hyperbola limit for L(1, χ) -/

private lemma tendsto_div_sq_sum_dconv_one {χ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hχ : ∀ a b : ℕ, |∑ n ∈ Icc a b, χ n| ≤ M) (hχ1 : ∀ n, |χ n| ≤ 1) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 (N ^ 2), dconv (fun _ => 1) χ n) / ((N ^ 2 : ℕ) : ℝ))
      atTop (nhds (Lval χ 1)) := by
  have hlim1 : Tendsto (fun N : ℕ => Lpartial χ N 1) atTop (nhds (Lval χ 1)) :=
    tendsto_Lval hM hχ (by norm_num)
  have hdiff_zero : Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 (N ^ 2), dconv (fun _ => 1) χ n) / ((N ^ 2 : ℕ) : ℝ) - Lpartial χ N 1)
      atTop (nhds 0) := by
    refine squeeze_zero_norm' (a := fun N : ℕ => (1 + M) / (N : ℝ)) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      rw [Real.norm_eq_abs]
      have hN2 : N ≤ N ^ 2 := by nlinarith
      have hhyp := dirichlet_hyperbola (fun _ => 1) χ (fun _ => 1) hN hN2 (fun _ _ _ _ => by ring)
      simp only [mul_one, one_mul, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hhyp
      have hNdiv : N ^ 2 / N = N := by rw [sq, Nat.mul_div_cancel _ (by omega)]
      rw [hNdiv] at hhyp
      have hN2_pos : (0 : ℝ) < ((N ^ 2 : ℕ) : ℝ) := by positivity
      have h1 : (∑ d ∈ Icc 1 N, χ d * (((N ^ 2 / d + 1 - 1 : ℕ) : ℝ))) / ((N ^ 2 : ℕ) : ℝ) -
          Lpartial χ N 1 =
          (∑ d ∈ Icc 1 N, χ d * (((N ^ 2 / d : ℕ) : ℝ) - ((N ^ 2 : ℕ) : ℝ) / (d : ℝ))) /
            ((N ^ 2 : ℕ) : ℝ) := by
        unfold Lpartial
        rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun d hd => ?_
        simp only [Finset.mem_Icc] at hd
        rw [Nat.add_sub_cancel, Real.rpow_neg_one]
        have hd_ne : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
        field_simp [hN2_pos.ne', hd_ne]
      have hrew : (∑ n ∈ Icc 1 (N ^ 2), dconv (fun _ => 1) χ n) / ((N ^ 2 : ℕ) : ℝ) -
          Lpartial χ N 1 =
          (∑ d ∈ Icc 1 N, χ d * (((N ^ 2 / d : ℕ) : ℝ) - ((N ^ 2 : ℕ) : ℝ) / (d : ℝ))) /
            ((N ^ 2 : ℕ) : ℝ) +
          (∑ k ∈ Icc 1 N, ∑ d ∈ Icc (N + 1) (N ^ 2 / k), χ d) / ((N ^ 2 : ℕ) : ℝ) := by
        rw [hhyp, add_div, add_sub_right_comm, h1]
      rw [hrew]
      have hb1 : |(∑ d ∈ Icc 1 N, χ d * (((N ^ 2 / d : ℕ) : ℝ) - ((N ^ 2 : ℕ) : ℝ) / (d : ℝ))) /
          ((N ^ 2 : ℕ) : ℝ)| ≤ (N : ℝ) / ((N ^ 2 : ℕ) : ℝ) := by
        rw [abs_div, abs_of_pos hN2_pos]
        refine div_le_div_of_nonneg_right ?_ hN2_pos.le
        calc |∑ d ∈ Icc 1 N, χ d * (((N ^ 2 / d : ℕ) : ℝ) - ((N ^ 2 : ℕ) : ℝ) / (d : ℝ))|
            ≤ ∑ d ∈ Icc 1 N, |χ d * (((N ^ 2 / d : ℕ) : ℝ) - ((N ^ 2 : ℕ) : ℝ) / (d : ℝ))| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ d ∈ Icc 1 N, (1 : ℝ) := by
              refine Finset.sum_le_sum fun d hd => ?_
              simp only [Finset.mem_Icc] at hd
              have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
              have hdiv_le : ((N ^ 2 / d : ℕ) : ℝ) ≤ ((N ^ 2 : ℕ) : ℝ) / (d : ℝ) := by
                rw [le_div_iff₀ hd_pos]; exact_mod_cast Nat.div_mul_le_self (N ^ 2) d
              have hdiv_ge : ((N ^ 2 : ℕ) : ℝ) / (d : ℝ) - 1 < ((N ^ 2 / d : ℕ) : ℝ) := by
                rw [sub_lt_iff_lt_add, div_lt_iff₀ hd_pos]
                have hlt : N ^ 2 < (N ^ 2 / d + 1) * d := by
                  have hmod := Nat.div_add_mod (N ^ 2) d
                  have hltm := Nat.mod_lt (N ^ 2) (by omega : 0 < d)
                  nlinarith
                exact_mod_cast hlt
              have habs : |((N ^ 2 / d : ℕ) : ℝ) - ((N ^ 2 : ℕ) : ℝ) / (d : ℝ)| ≤ 1 := by
                rw [abs_le]; constructor <;> linarith
              rw [abs_mul]
              exact (mul_le_mul (hχ1 d) habs (abs_nonneg _) zero_le_one).trans (by norm_num)
          _ = (N : ℝ) := by simp
      have hb2 : |(∑ k ∈ Icc 1 N, ∑ d ∈ Icc (N + 1) (N ^ 2 / k), χ d) / ((N ^ 2 : ℕ) : ℝ)| ≤
          ((N : ℝ) * M) / ((N ^ 2 : ℕ) : ℝ) := by
        rw [abs_div, abs_of_pos hN2_pos]
        refine div_le_div_of_nonneg_right ?_ hN2_pos.le
        calc |∑ k ∈ Icc 1 N, ∑ d ∈ Icc (N + 1) (N ^ 2 / k), χ d|
            ≤ ∑ k ∈ Icc 1 N, |∑ d ∈ Icc (N + 1) (N ^ 2 / k), χ d| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ Icc 1 N, M := Finset.sum_le_sum fun k _ => hχ (N + 1) (N ^ 2 / k)
          _ = (N : ℝ) * M := by simp
      have hsimp : (N : ℝ) / ((N ^ 2 : ℕ) : ℝ) + ((N : ℝ) * M) / ((N ^ 2 : ℕ) : ℝ) =
          (1 + M) / (N : ℝ) := by
        have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
        push_cast; field_simp [hN_ne]
      exact (abs_add_le _ _).trans (by linarith)
    · have h1 := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
      simpa [div_eq_mul_inv] using h1.const_mul (1 + M)
  have hsum := hdiff_zero.add hlim1
  simpa using hsum

private lemma Lval_one_nonneg {χ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hχ : ∀ a b : ℕ, |∑ n ∈ Icc a b, χ n| ≤ M) (hχ1 : ∀ n, |χ n| ≤ 1)
    (hnn : ∀ n : ℕ, 1 ≤ n → 0 ≤ dconv (fun _ => 1) χ n) :
    0 ≤ Lval χ 1 := by
  refine ge_of_tendsto (tendsto_div_sq_sum_dconv_one hM hχ hχ1) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  refine div_nonneg ?_ (by positivity)
  exact Finset.sum_nonneg fun n hn => hnn n (Finset.mem_Icc.mp hn).1

private lemma Lval_one_le_of_pid {m y : ℕ} (hy : 1 ≤ y) (hm : m + 2 = (4 * y) ^ 2)
    (hsq : Squarefree m) (hpid : IsPrincipalIdealRing (Zsqrtd (m : ℤ))) :
    let hm_pos : 0 < m := by nlinarith
    Lval (chiRe (quadChar m hm_pos)) 1 ≤
      2 * Real.log (4 * (m : ℝ)) / Real.sqrt (4 * (m : ℝ)) := by
  have hm_pos : 0 < m := by nlinarith
  have hm4 : m % 4 = 2 := by
    have hm16 : m + 2 = 16 * y ^ 2 := by linarith
    omega
  let _ : NeZero (4 * m) := ⟨by omega⟩
  have hprim := quadChar_isPrimitive hm_pos hm4 hsq
  have hM : 0 ≤ Real.sqrt ((4 * m : ℕ) : ℝ) * (Real.log ((4 * m : ℕ) : ℝ) + 1) := by
    have : 1 ≤ ((4 * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 4 * m)
    exact mul_nonneg (Real.sqrt_nonneg _) (by linarith [Real.log_nonneg this])
  have hlim := tendsto_div_sq_sum_dconv_one hM
    (polya_vinogradov_re (by omega) hprim) (abs_chiRe_le_one (quadChar_isReal hm_pos))
  obtain ⟨C, hC_nn, hbound⟩ := sum_a_le_regulator_bound hy hm hsq hpid
  set ε : ℝ := (16 * (y : ℝ) ^ 2 - 1) + 4 * (y : ℝ) * Real.sqrt (m : ℝ)
  have hε_pos : 0 < ε := by
    have hy1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
    have hsq_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by positivity)
    dsimp [ε]; nlinarith
  have hε_lt : ε < 4 * (m : ℝ) := by
    have hm_eq : (m : ℝ) = 16 * (y : ℝ) ^ 2 - 2 := by
      have : (m : ℝ) + 2 = (4 * (y : ℝ)) ^ 2 := by exact_mod_cast hm
      linarith
    have hsq_lt : Real.sqrt (m : ℝ) < 4 * (y : ℝ) := by
      rw [Real.sqrt_lt' (by positivity)]
      nlinarith
    have hy1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
    dsimp [ε]; nlinarith
  have hlim_rhs : Tendsto (fun N : ℕ =>
      2 * Real.log ε / Real.sqrt (4 * (m : ℝ)) +
      C * ((N : ℝ) + 1) / ((N ^ 2 : ℕ) : ℝ))
      atTop (nhds (2 * Real.log ε / Real.sqrt (4 * (m : ℝ)))) := by
    have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have h0 : Tendsto (fun N : ℕ => C * ((N : ℝ) + 1) / ((N ^ 2 : ℕ) : ℝ)) atTop (nhds 0) := by
      have haux : Tendsto (fun N : ℕ => C * ((N : ℝ)⁻¹ + ((N : ℝ)⁻¹) ^ 2)) atTop (nhds 0) := by
        simpa using ((hinv.add (hinv.pow 2)).const_mul C)
      refine haux.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      push_cast; field_simp [hN_ne]
    simpa using (tendsto_const_nhds.add h0)
  have hle_ε : Lval (chiRe (quadChar m hm_pos)) 1 ≤
      2 * Real.log ε / Real.sqrt (4 * (m : ℝ)) := by
    refine le_of_tendsto_of_tendsto hlim hlim_rhs ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hN2_pos : 1 ≤ N ^ 2 := by nlinarith
    have hb := hbound (N ^ 2) hN2_pos
    have hsqN : Real.sqrt ((N ^ 2 : ℕ) : ℝ) = (N : ℝ) := by
      push_cast; exact Real.sqrt_sq (by positivity)
    rw [hsqN] at hb
    have hN2_rpos : (0 : ℝ) < ((N ^ 2 : ℕ) : ℝ) := by positivity
    rw [div_le_iff₀ hN2_rpos]
    calc ∑ n ∈ Icc 1 (N ^ 2), dconv (fun _ => 1) (chiRe (quadChar m hm_pos)) n
        ≤ (2 * Real.log ε / Real.sqrt (4 * (m : ℝ))) * ((N ^ 2 : ℕ) : ℝ) +
          C * ((N : ℝ) + 1) := hb
      _ = (2 * Real.log ε / Real.sqrt (4 * (m : ℝ)) +
          C * ((N : ℝ) + 1) / ((N ^ 2 : ℕ) : ℝ)) * ((N ^ 2 : ℕ) : ℝ) := by
          field_simp [hN2_rpos.ne']
  have hlog_le : Real.log ε ≤ Real.log (4 * (m : ℝ)) := Real.log_le_log hε_pos hε_lt.le
  refine hle_ε.trans ?_
  exact div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

/- Elementary Euler-Maclaurin for s in (0, 1) -/

private noncomputable def emTerm (s : ℝ) (k : ℕ) : ℝ :=
  ∫ t in ((k + 1 : ℕ) : ℝ)..((k + 2 : ℕ) : ℝ), (t ^ (-s) - ((k + 2 : ℕ) : ℝ) ^ (-s))

private noncomputable def gammaVal (s : ℝ) : ℝ :=
  1 - ∑' k : ℕ, emTerm s k

private noncomputable def zetaVal (s : ℝ) : ℝ :=
  gammaVal s - 1 / (1 - s)

private lemma emTerm_bounds {s : ℝ} (hs : 0 < s) (k : ℕ) :
    0 ≤ emTerm s k ∧ emTerm s k ≤ ((k + 1 : ℕ) : ℝ) ^ (-s) - ((k + 2 : ℕ) : ℝ) ^ (-s) := by
  unfold emTerm
  have hle : ((k + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ k + 2)
  have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (-s) - ((k + 2 : ℕ) : ℝ) ^ (-s))
      MeasureTheory.volume ((k + 1 : ℕ) : ℝ) ((k + 2 : ℕ) : ℝ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hle]
    intro t ht
    exact ((Real.continuousAt_rpow_const t (-s)
      (Or.inl (lt_of_lt_of_le hpos ht.1).ne')).sub continuousAt_const).continuousWithinAt
  have hlen : ((k + 2 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ) = 1 := by push_cast; ring
  constructor
  · have h0 : ∫ _t in ((k + 1 : ℕ) : ℝ)..((k + 2 : ℕ) : ℝ), (0 : ℝ) ≤
        ∫ t in ((k + 1 : ℕ) : ℝ)..((k + 2 : ℕ) : ℝ), (t ^ (-s) - ((k + 2 : ℕ) : ℝ) ^ (-s)) := by
      refine intervalIntegral.integral_mono_on hle intervalIntegrable_const hint fun t ht => ?_
      exact sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hpos ht.1) ht.2 (by linarith))
    simpa using h0
  · have h1 : ∫ t in ((k + 1 : ℕ) : ℝ)..((k + 2 : ℕ) : ℝ), (t ^ (-s) - ((k + 2 : ℕ) : ℝ) ^ (-s)) ≤
        ∫ _t in ((k + 1 : ℕ) : ℝ)..((k + 2 : ℕ) : ℝ),
          (((k + 1 : ℕ) : ℝ) ^ (-s) - ((k + 2 : ℕ) : ℝ) ^ (-s)) := by
      refine intervalIntegral.integral_mono_on hle hint intervalIntegrable_const fun t ht => ?_
      exact sub_le_sub_right (Real.rpow_le_rpow_of_nonpos hpos ht.1 (by linarith)) _
    rw [intervalIntegral.integral_const, smul_eq_mul, hlen, one_mul] at h1
    exact h1

private lemma emTerm_summable {s : ℝ} (hs : 0 < s) : Summable (emTerm s) := by
  refine summable_of_sum_range_le (c := 1) (fun k => (emTerm_bounds hs k).1) fun n => ?_
  have htele : ∀ m : ℕ,
      ∑ k ∈ range m, (((k + 1 : ℕ) : ℝ) ^ (-s) - ((k + 2 : ℕ) : ℝ) ^ (-s)) =
        1 - ((m + 1 : ℕ) : ℝ) ^ (-s) := by
    intro m
    induction m with
    | zero => simp
    | succ r ih => rw [Finset.sum_range_succ, ih]; ring
  calc ∑ k ∈ range n, emTerm s k
      ≤ ∑ k ∈ range n, (((k + 1 : ℕ) : ℝ) ^ (-s) - ((k + 2 : ℕ) : ℝ) ^ (-s)) :=
        Finset.sum_le_sum fun k _ => (emTerm_bounds hs k).2
    _ = 1 - ((n + 1 : ℕ) : ℝ) ^ (-s) := htele n
    _ ≤ 1 := by linarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)) (-s)]

private lemma gammaVal_bounds {s : ℝ} (hs : 0 < s) :
    0 ≤ gammaVal s ∧ gammaVal s ≤ 1 := by
  unfold gammaVal
  have hsum := emTerm_summable hs
  have hnn : 0 ≤ ∑' k : ℕ, emTerm s k := tsum_nonneg fun k => (emTerm_bounds hs k).1
  have hle1 : ∑' k : ℕ, emTerm s k ≤ 1 := by
    refine le_of_tendsto hsum.hasSum.tendsto_sum_nat ?_
    refine Filter.Eventually.of_forall fun n => ?_
    have htele : ∀ m : ℕ,
        ∑ k ∈ range m, (((k + 1 : ℕ) : ℝ) ^ (-s) - ((k + 2 : ℕ) : ℝ) ^ (-s)) =
          1 - ((m + 1 : ℕ) : ℝ) ^ (-s) := by
      intro m
      induction m with
      | zero => simp
      | succ r ih => rw [Finset.sum_range_succ, ih]; ring
    calc ∑ k ∈ range n, emTerm s k
        ≤ ∑ k ∈ range n, (((k + 1 : ℕ) : ℝ) ^ (-s) - ((k + 2 : ℕ) : ℝ) ^ (-s)) :=
          Finset.sum_le_sum fun k _ => (emTerm_bounds hs k).2
      _ = 1 - ((n + 1 : ℕ) : ℝ) ^ (-s) := htele n
      _ ≤ 1 := by linarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)) (-s)]
  constructor <;> linarith

private lemma zetaVal_bounds {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    zetaVal s < 0 ∧ |zetaVal s| ≤ 1 / (1 - s) := by
  unfold zetaVal
  obtain ⟨h0, h1⟩ := gammaVal_bounds hs0
  have hgt : 1 < 1 / (1 - s) := by rw [lt_div_iff₀ (by linarith)]; linarith
  refine ⟨by linarith, ?_⟩
  rw [abs_of_neg (by linarith)]; linarith

private lemma sum_rpow_euler_maclaurin {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {Y : ℝ} (hY : 1 ≤ Y) :
    |∑ k ∈ Icc 1 (Nat.floor Y), (k : ℝ) ^ (-s) -
      (((Y ^ (1 - s) - 1) / (1 - s)) + gammaVal s)| ≤ 2 * Y ^ (-s) := by
  set N : ℕ := Nat.floor Y
  have hN1 : 1 ≤ N := Nat.le_floor (by norm_cast)
  have hNY : (N : ℝ) ≤ Y := Nat.floor_le (by linarith)
  have hYN1 : Y < (N : ℝ) + 1 := Nat.lt_floor_add_one Y
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hident : ∀ m : ℕ, 1 ≤ m →
      ∑ k ∈ Icc 1 m, (k : ℝ) ^ (-s) - ((m : ℝ) ^ (1 - s) - 1) / (1 - s) =
        1 - ∑ k ∈ range (m - 1), emTerm s k := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => simp
    | succ r hr ih =>
      have hr1 : r + 1 - 1 = r := by omega
      rw [hr1]
      have hIcc : Icc 1 (r + 1) = insert (r + 1) (Icc 1 r) := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp)]
      have hrange : range r = insert (r - 1) (range (r - 1)) := by
        ext j; simp only [Finset.mem_range, Finset.mem_insert]; omega
      rw [hrange, Finset.sum_insert (by simp)]
      have hem : emTerm s (r - 1) =
          (((r + 1 : ℕ) : ℝ) ^ (1 - s) - (r : ℝ) ^ (1 - s)) / (1 - s) -
          ((r + 1 : ℕ) : ℝ) ^ (-s) := by
        unfold emTerm
        have h1 : r - 1 + 1 = r := by omega
        have h2 : r - 1 + 2 = r + 1 := by omega
        rw [h1, h2]
        have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
        have hle : (r : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ r
        have hint1 : IntervalIntegrable (fun t : ℝ => t ^ (-s))
            MeasureTheory.volume (r : ℝ) ((r + 1 : ℕ) : ℝ) := by
          refine ContinuousOn.intervalIntegrable ?_
          rw [Set.uIcc_of_le hle]
          intro t ht
          exact (Real.continuousAt_rpow_const t (-s)
            (Or.inl (lt_of_lt_of_le hr_pos ht.1).ne')).continuousWithinAt
        rw [intervalIntegral.integral_sub hint1 intervalIntegrable_const,
          integral_rpow_neg_eq (by linarith) hr_pos hle,
          intervalIntegral.integral_const, smul_eq_mul]
        have hlen : ((r + 1 : ℕ) : ℝ) - (r : ℝ) = 1 := by push_cast; ring
        rw [hlen, one_mul]
        have hneg : ((r : ℝ) ^ (1 - s) - ((r + 1 : ℕ) : ℝ) ^ (1 - s)) / (s - 1) =
            (((r + 1 : ℕ) : ℝ) ^ (1 - s) - (r : ℝ) ^ (1 - s)) / (1 - s) := by
          field_simp [show s - 1 ≠ 0 by linarith, show 1 - s ≠ 0 by linarith]; ring
        rw [hneg]
      rw [hem]
      have hdiv : (((r + 1 : ℕ) : ℝ) ^ (1 - s) - 1) / (1 - s) =
          (((r + 1 : ℕ) : ℝ) ^ (1 - s) - (r : ℝ) ^ (1 - s)) / (1 - s) +
          ((r : ℝ) ^ (1 - s) - 1) / (1 - s) := by ring
      linarith
  have hsum := emTerm_summable hs0
  have htsum_split : ∑' k : ℕ, emTerm s k =
      ∑ k ∈ range (N - 1), emTerm s k + ∑' k : ℕ, emTerm s (k + (N - 1)) :=
    (hsum.sum_add_tsum_nat_add (N - 1)).symm
  have htail_nn : 0 ≤ ∑' k : ℕ, emTerm s (k + (N - 1)) :=
    tsum_nonneg fun k => (emTerm_bounds hs0 _).1
  have htail_le : ∑' k : ℕ, emTerm s (k + (N - 1)) ≤ (N : ℝ) ^ (-s) := by
    have hsum_shift : Summable (fun k => emTerm s (k + (N - 1))) :=
      (summable_nat_add_iff (N - 1)).mpr hsum
    refine le_of_tendsto hsum_shift.hasSum.tendsto_sum_nat ?_
    refine Filter.Eventually.of_forall fun n => ?_
    have htele : ∀ m : ℕ,
        ∑ k ∈ range m,
          (((k + (N - 1) + 1 : ℕ) : ℝ) ^ (-s) - ((k + (N - 1) + 2 : ℕ) : ℝ) ^ (-s)) =
        (N : ℝ) ^ (-s) - ((m + N : ℕ) : ℝ) ^ (-s) := by
      intro m
      induction m with
      | zero => simp
      | succ r ih =>
        rw [Finset.sum_range_succ, ih]
        have h1 : r + (N - 1) + 1 = r + N := by omega
        have h2 : r + (N - 1) + 2 = r + 1 + N := by omega
        rw [h1, h2]; ring
    calc ∑ k ∈ range n, emTerm s (k + (N - 1))
        ≤ ∑ k ∈ range n,
            (((k + (N - 1) + 1 : ℕ) : ℝ) ^ (-s) - ((k + (N - 1) + 2 : ℕ) : ℝ) ^ (-s)) :=
          Finset.sum_le_sum fun k _ => (emTerm_bounds hs0 _).2
      _ = (N : ℝ) ^ (-s) - ((n + N : ℕ) : ℝ) ^ (-s) := htele n
      _ ≤ (N : ℝ) ^ (-s) := by
          linarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ ((n + N : ℕ) : ℝ)) (-s)]
  have hint_eq : (Y ^ (1 - s) - (N : ℝ) ^ (1 - s)) / (1 - s) = ∫ t in (N : ℝ)..Y, t ^ (-s) := by
    rw [integral_rpow_neg_eq (by linarith) hN_pos hNY]
    field_simp [show s - 1 ≠ 0 by linarith, show 1 - s ≠ 0 by linarith]; ring
  have hint_nn : 0 ≤ ∫ t in (N : ℝ)..Y, t ^ (-s) := by
    refine intervalIntegral.integral_nonneg hNY fun t ht => ?_
    exact Real.rpow_nonneg (le_trans hN_pos.le ht.1) _
  have hint_le : ∫ t in (N : ℝ)..Y, t ^ (-s) ≤ (N : ℝ) ^ (-s) := by
    have hint1 : IntervalIntegrable (fun t : ℝ => t ^ (-s)) MeasureTheory.volume (N : ℝ) Y := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hNY]
      intro t ht
      exact (Real.continuousAt_rpow_const t (-s)
        (Or.inl (lt_of_lt_of_le hN_pos ht.1).ne')).continuousWithinAt
    have h1 : ∫ t in (N : ℝ)..Y, t ^ (-s) ≤ ∫ _t in (N : ℝ)..Y, (N : ℝ) ^ (-s) :=
      intervalIntegral.integral_mono_on hNY hint1 intervalIntegrable_const fun t ht =>
        Real.rpow_le_rpow_of_nonpos hN_pos ht.1 (by linarith)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    calc ∫ t in (N : ℝ)..Y, t ^ (-s) ≤ (Y - (N : ℝ)) * (N : ℝ) ^ (-s) := h1
      _ ≤ 1 * (N : ℝ) ^ (-s) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hN_pos.le _)
      _ = (N : ℝ) ^ (-s) := one_mul _
  have hdiff : ∑ k ∈ Icc 1 N, (k : ℝ) ^ (-s) - (((Y ^ (1 - s) - 1) / (1 - s)) + gammaVal s) =
      (∑' k : ℕ, emTerm s (k + (N - 1))) - ∫ t in (N : ℝ)..Y, t ^ (-s) := by
    have hi := hident N hN1
    unfold gammaVal
    rw [htsum_split, ← hint_eq]
    have hsub : (Y ^ (1 - s) - 1) / (1 - s) - ((N : ℝ) ^ (1 - s) - 1) / (1 - s) =
        (Y ^ (1 - s) - (N : ℝ) ^ (1 - s)) / (1 - s) := by ring
    linarith
  rw [hdiff]
  have habs_N : |(∑' k : ℕ, emTerm s (k + (N - 1))) - ∫ t in (N : ℝ)..Y, t ^ (-s)| ≤
      (N : ℝ) ^ (-s) := by
    rw [abs_le]; constructor <;> linarith
  have hN_Y : (N : ℝ) ^ (-s) ≤ 2 * Y ^ (-s) := by
    have hY2 : Y ≤ 2 * (N : ℝ) := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
      linarith
    calc (N : ℝ) ^ (-s) = (2 : ℝ) ^ s * (2 * (N : ℝ)) ^ (-s) := by
          rw [Real.mul_rpow (by norm_num) hN_pos.le, ← mul_assoc,
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          simp
      _ ≤ (2 : ℝ) ^ (1 : ℝ) * Y ^ (-s) := by
          refine mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1.le)
            (Real.rpow_le_rpow_of_nonpos (by linarith) hY2 (by linarith))
            (Real.rpow_nonneg (by linarith) _) (by positivity)
      _ = 2 * Y ^ (-s) := by rw [Real.rpow_one]
  exact habs_N.trans hN_Y

/- Section 4b: Two-character contradiction and final theorem -/

private lemma rpow_neg_le_two_pow {x a : ℝ} {e : ℕ} {k : ℤ}
    (hx : (2 : ℝ) ^ e ≤ x) (ha : a ≤ 0) (hk : (e : ℝ) * a ≤ (k : ℝ)) :
    x ^ a ≤ (2 : ℝ) ^ k := by
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  calc x ^ a ≤ ((2 : ℝ) ^ e) ^ a := Real.rpow_le_rpow_of_nonpos h2pos hx ha
    _ = (2 : ℝ) ^ ((e : ℝ) * a) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    _ ≤ (2 : ℝ) ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hk
    _ = (2 : ℝ) ^ k := Real.rpow_intCast 2 k

private lemma step1_Lval_neg {m y : ℕ} (hy : 4102 ≤ y) (hm : m + 2 = (4 * y) ^ 2)
    (hsq : Squarefree m) (hpid : IsPrincipalIdealRing (Zsqrtd (m : ℤ))) :
    let hm_pos : 0 < m := by nlinarith
    Lval (chiRe (quadChar m hm_pos)) ((49 : ℝ) / 50) < 0 := by
  have hm_pos : 0 < m := by nlinarith
  have hm4 : m % 4 = 2 := by
    have hm16 : m + 2 = 16 * y ^ 2 := by linarith
    omega
  set D : ℕ := 4 * m
  have hD_big : 2 ^ 30 ≤ D := by
    have hm16 : m + 2 = 16 * y ^ 2 := by linarith
    have hD8 : D + 8 = 64 * y ^ 2 := by dsimp [D]; omega
    have hy2 : 64 * 4102 ^ 2 ≤ 64 * y ^ 2 := by nlinarith
    omega
  have hD_rbig : (2 : ℝ) ^ (30 : ℕ) ≤ (D : ℝ) := by exact_mod_cast hD_big
  have hD_pos : (0 : ℝ) < (D : ℝ) := by positivity
  have hD_ge1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (by omega : 1 ≤ D)
  let _ : NeZero D := ⟨by omega⟩
  have hprim : (quadChar m hm_pos).IsPrimitive := quadChar_isPrimitive hm_pos hm4 hsq
  set χ : ℕ → ℝ := chiRe (quadChar m hm_pos)
  set M : ℝ := Real.sqrt (D : ℝ) * (Real.log (D : ℝ) + 1)
  have hM_nn : 0 ≤ M := mul_nonneg (Real.sqrt_nonneg _) (by linarith [Real.log_nonneg hD_ge1])
  have hχ_pv : ∀ a b : ℕ, |∑ n ∈ Icc a b, χ n| ≤ M :=
    polya_vinogradov_re (by omega) hprim
  have hχ1 : ∀ n, |χ n| ≤ 1 := abs_chiRe_le_one (quadChar_isReal hm_pos)
  have hM_le : M ≤ 17 * (D : ℝ) ^ ((21 : ℝ) / 40) := by
    dsimp [M]
    rw [Real.sqrt_eq_rpow]
    calc (D : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (D : ℝ) + 1)
        ≤ (D : ℝ) ^ ((1 : ℝ) / 2) * (17 * (D : ℝ) ^ ((1 : ℝ) / 40)) :=
          mul_le_mul_of_nonneg_left (log_add_one_le_17_rpow hD_ge1) (Real.rpow_nonneg hD_pos.le _)
      _ = 17 * (D : ℝ) ^ ((21 : ℝ) / 40) := by
          rw [mul_left_comm, ← Real.rpow_add hD_pos]; congr 2; norm_num
  have hL1_le : Lval χ 1 ≤ 32 * (D : ℝ) ^ (-(19 : ℝ) / 40) := by
    have h1 : Lval χ 1 ≤ 2 * Real.log (D : ℝ) / Real.sqrt (D : ℝ) := by
      have := Lval_one_le_of_pid (by omega) hm hsq hpid
      simpa [χ, D] using this
    refine h1.trans ?_
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hD_pos.le, ← neg_div]
    calc 2 * Real.log (D : ℝ) * (D : ℝ) ^ (-(1 : ℝ) / 2)
        ≤ 2 * (16 * (D : ℝ) ^ ((1 : ℝ) / 40)) * (D : ℝ) ^ (-(1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right (by linarith [log_le_16_rpow hD_pos])
            (Real.rpow_nonneg hD_pos.le _)
      _ = 32 * ((D : ℝ) ^ ((1 : ℝ) / 40) * (D : ℝ) ^ (-(1 : ℝ) / 2)) := by ring
      _ = 32 * (D : ℝ) ^ (-(19 : ℝ) / 40) := by
          rw [← Real.rpow_add hD_pos]; congr 2; norm_num
  change Lval χ ((49 : ℝ) / 50) < 0
  by_contra hge
  push Not at hge
  set s₀ : ℝ := (49 : ℝ) / 50
  set X₁ : ℕ := D ^ 4
  set U₁ : ℕ := D ^ 2
  have hU₁1 : 1 ≤ U₁ := Nat.one_le_pow 2 D (by omega)
  have hU₁X₁ : U₁ ≤ X₁ := by
    have : D ^ 2 ≤ D ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    exact this
  have hX₁_div_U₁ : X₁ / U₁ = U₁ := by
    have hmul : X₁ = U₁ * U₁ := by dsimp [X₁, U₁]; ring
    rw [hmul, Nat.mul_div_cancel _ (by omega)]
  have hsum_ge1 : (1 : ℝ) ≤ ∑ n ∈ Icc 1 X₁, dconv (fun _ => 1) χ n * (n : ℝ) ^ (-s₀) := by
    have h1mem : (1 : ℕ) ∈ Icc 1 X₁ := Finset.mem_Icc.mpr ⟨le_rfl, le_trans hU₁1 hU₁X₁⟩
    have h1val : dconv (fun _ => 1) χ 1 * ((1 : ℕ) : ℝ) ^ (-s₀) = 1 := by
      have hχ_one : χ 1 = 1 := (chiRe_complMult (fun n => (quadChar_isReal hm_pos n).1)).1
      rw [dconv_one, hχ_one]; simp
    calc (1 : ℝ) = dconv (fun _ => 1) χ 1 * ((1 : ℕ) : ℝ) ^ (-s₀) := h1val.symm
      _ ≤ ∑ n ∈ Icc 1 X₁, dconv (fun _ => 1) χ n * (n : ℝ) ^ (-s₀) := by
          refine Finset.single_le_sum (f := fun n : ℕ => dconv (fun _ => 1) χ n * (n : ℝ) ^ (-s₀))
            (fun n hn => ?_) h1mem
          exact mul_nonneg (dconv_one_chiRe_nonneg (quadChar_isReal hm_pos) n (Finset.mem_Icc.mp hn).1)
            (Real.rpow_nonneg (by positivity) _)
  have hw_mul : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      ((a * b : ℕ) : ℝ) ^ (-s₀) = (a : ℝ) ^ (-s₀) * (b : ℝ) ^ (-s₀) := by
    intro a b _ _
    push_cast; exact Real.mul_rpow (by positivity) (by positivity)
  have hhyp := dirichlet_hyperbola (fun _ => 1) χ (fun n => (n : ℝ) ^ (-s₀)) hU₁1 hU₁X₁ hw_mul
  rw [hX₁_div_U₁] at hhyp
  simp only [one_mul] at hhyp
  have hX₁_cast : (X₁ : ℝ) = (D : ℝ) ^ (4 : ℕ) := by push_cast [X₁]; rfl
  have hU₁_cast : (U₁ : ℝ) = (D : ℝ) ^ (2 : ℕ) := by push_cast [U₁]; rfl
  have hX₁_pow : (X₁ : ℝ) ^ ((1 : ℝ) / 50) = (D : ℝ) ^ ((2 : ℝ) / 25) := by
    rw [hX₁_cast, ← Real.rpow_natCast, ← Real.rpow_mul hD_pos.le]; congr 1; norm_num
  have hS1_le : ∑ d ∈ Icc 1 U₁, χ d * (d : ℝ) ^ (-s₀) * ∑ k ∈ Icc 1 (X₁ / d), (k : ℝ) ^ (-s₀) ≤
      (4 : ℝ) / 5 + (3 : ℝ) / 100 := by
    have hsplit_d : ∀ d ∈ Icc 1 U₁,
        χ d * (d : ℝ) ^ (-s₀) * ∑ k ∈ Icc 1 (X₁ / d), (k : ℝ) ^ (-s₀) =
          50 * (X₁ : ℝ) ^ ((1 : ℝ) / 50) * (χ d * (d : ℝ) ^ (-(1 : ℝ))) +
          zetaVal s₀ * (χ d * (d : ℝ) ^ (-s₀)) +
          χ d * (d : ℝ) ^ (-s₀) *
            (∑ k ∈ Icc 1 (X₁ / d), (k : ℝ) ^ (-s₀) -
              ((((X₁ : ℝ) / (d : ℝ)) ^ (1 - s₀) - 1) / (1 - s₀) + gammaVal s₀)) := by
      intro d hd
      simp only [Finset.mem_Icc] at hd
      have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
      have hY_pow : (d : ℝ) ^ (-s₀) * (((X₁ : ℝ) / (d : ℝ)) ^ (1 - s₀) / (1 - s₀)) =
          50 * (X₁ : ℝ) ^ ((1 : ℝ) / 50) * (d : ℝ) ^ (-(1 : ℝ)) := by
        rw [Real.div_rpow (by positivity) hd_pos.le]
        have hs_sub : (1 : ℝ) - s₀ = (1 : ℝ) / 50 := by dsimp [s₀]; norm_num
        rw [hs_sub]
        have hd_comb : (d : ℝ) ^ (-s₀) * ((d : ℝ) ^ ((1 : ℝ) / 50))⁻¹ = (d : ℝ) ^ (-(1 : ℝ)) := by
          rw [← Real.rpow_neg hd_pos.le, ← Real.rpow_add hd_pos]; congr 1; dsimp [s₀]; ring
        calc (d : ℝ) ^ (-s₀) * ((X₁ : ℝ) ^ ((1 : ℝ) / 50) / (d : ℝ) ^ ((1 : ℝ) / 50) / ((1 : ℝ) / 50))
            = 50 * (X₁ : ℝ) ^ ((1 : ℝ) / 50) * ((d : ℝ) ^ (-s₀) * ((d : ℝ) ^ ((1 : ℝ) / 50))⁻¹) := by
              ring
          _ = 50 * (X₁ : ℝ) ^ ((1 : ℝ) / 50) * (d : ℝ) ^ (-(1 : ℝ)) := by rw [hd_comb]
      have hzeta : ((((X₁ : ℝ) / (d : ℝ)) ^ (1 - s₀) - 1) / (1 - s₀) + gammaVal s₀) =
          ((X₁ : ℝ) / (d : ℝ)) ^ (1 - s₀) / (1 - s₀) + zetaVal s₀ := by
        unfold zetaVal; ring
      rw [hzeta]
      calc χ d * (d : ℝ) ^ (-s₀) * ∑ k ∈ Icc 1 (X₁ / d), (k : ℝ) ^ (-s₀)
          = χ d * ((d : ℝ) ^ (-s₀) * (((X₁ : ℝ) / (d : ℝ)) ^ (1 - s₀) / (1 - s₀))) +
            zetaVal s₀ * (χ d * (d : ℝ) ^ (-s₀)) +
            χ d * (d : ℝ) ^ (-s₀) *
              (∑ k ∈ Icc 1 (X₁ / d), (k : ℝ) ^ (-s₀) -
                (((X₁ : ℝ) / (d : ℝ)) ^ (1 - s₀) / (1 - s₀) + zetaVal s₀)) := by ring
        _ = _ := by rw [hY_pow]; ring
    rw [Finset.sum_congr rfl hsplit_d, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    have hmain1 : 50 * (X₁ : ℝ) ^ ((1 : ℝ) / 50) * Lpartial χ U₁ 1 ≤
        (4 : ℝ) / 5 + (1 : ℝ) / 100 := by
      have htail := abs_Lval_sub_partial_le hM_nn hχ_pv (by norm_num : (0 : ℝ) < 1) U₁
      have hLpart_le : Lpartial χ U₁ 1 ≤ Lval χ 1 + M * (U₁ : ℝ) ^ (-(1 : ℝ)) := by
        have h1 : Lpartial χ U₁ 1 - Lval χ 1 ≤ M * ((U₁ + 1 : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
          linarith [(abs_le.mp htail).1]
        have h2 : ((U₁ + 1 : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ (U₁ : ℝ) ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast Nat.le_succ U₁) (by norm_num)
        nlinarith
      have htermA : 50 * (X₁ : ℝ) ^ ((1 : ℝ) / 50) * Lval χ 1 ≤ (4 : ℝ) / 5 := by
        calc 50 * (X₁ : ℝ) ^ ((1 : ℝ) / 50) * Lval χ 1
            ≤ 50 * (D : ℝ) ^ ((2 : ℝ) / 25) * (32 * (D : ℝ) ^ (-(19 : ℝ) / 40)) := by
              rw [hX₁_pow]
              exact mul_le_mul_of_nonneg_left hL1_le (by positivity)
          _ = 1600 * (D : ℝ) ^ (-(79 : ℝ) / 200) := by
              rw [mul_assoc, mul_left_comm ((D : ℝ) ^ ((2 : ℝ) / 25)), ← Real.rpow_add hD_pos]
              have hexp : (2 : ℝ) / 25 + -(19 : ℝ) / 40 = -(79 : ℝ) / 200 := by norm_num
              rw [hexp]; ring
          _ ≤ 1600 * (2 : ℝ) ^ (-11 : ℤ) := by
              refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
              exact rpow_neg_le_two_pow hD_rbig (by norm_num) (by norm_num)
          _ ≤ (4 : ℝ) / 5 := by norm_num
      have htermB : 50 * (X₁ : ℝ) ^ ((1 : ℝ) / 50) * (M * (U₁ : ℝ) ^ (-(1 : ℝ))) ≤ (1 : ℝ) / 100 := by
        have hU₁_inv : (U₁ : ℝ) ^ (-(1 : ℝ)) = (D : ℝ) ^ (-(2 : ℝ)) := by
          rw [hU₁_cast, ← Real.rpow_natCast, ← Real.rpow_mul hD_pos.le]; congr 1; norm_num
        calc 50 * (X₁ : ℝ) ^ ((1 : ℝ) / 50) * (M * (U₁ : ℝ) ^ (-(1 : ℝ)))
            ≤ 50 * (D : ℝ) ^ ((2 : ℝ) / 25) * ((17 * (D : ℝ) ^ ((21 : ℝ) / 40)) * (D : ℝ) ^ (-(2 : ℝ))) := by
              rw [hX₁_pow, hU₁_inv]
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hM_le (Real.rpow_nonneg hD_pos.le _)) (by positivity)
          _ = 850 * (D : ℝ) ^ (-(279 : ℝ) / 200) := by
              have hcomb : (D : ℝ) ^ ((2 : ℝ) / 25) * ((D : ℝ) ^ ((21 : ℝ) / 40) * (D : ℝ) ^ (-(2 : ℝ))) =
                  (D : ℝ) ^ (-(279 : ℝ) / 200) := by
                rw [← Real.rpow_add hD_pos, ← Real.rpow_add hD_pos]; congr 1; norm_num
              calc 50 * (D : ℝ) ^ ((2 : ℝ) / 25) * (17 * (D : ℝ) ^ ((21 : ℝ) / 40) * (D : ℝ) ^ (-(2 : ℝ)))
                  = 850 * ((D : ℝ) ^ ((2 : ℝ) / 25) * ((D : ℝ) ^ ((21 : ℝ) / 40) * (D : ℝ) ^ (-(2 : ℝ)))) := by
                    ring
                _ = 850 * (D : ℝ) ^ (-(279 : ℝ) / 200) := by rw [hcomb]
          _ ≤ 850 * (2 : ℝ) ^ (-30 : ℤ) := by
              refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
              exact rpow_neg_le_two_pow hD_rbig (by norm_num) (by norm_num)
          _ ≤ (1 : ℝ) / 100 := by norm_num
      have hmul := mul_le_mul_of_nonneg_left hLpart_le (by positivity : (0 : ℝ) ≤ 50 * (X₁ : ℝ) ^ ((1 : ℝ) / 50))
      linarith
    have hmain2 : zetaVal s₀ * Lpartial χ U₁ s₀ ≤ (1 : ℝ) / 100 := by
      obtain ⟨hz_neg, hz_abs⟩ := zetaVal_bounds (by norm_num : (0 : ℝ) < s₀) (by norm_num : s₀ < 1)
      have hz_50 : |zetaVal s₀| ≤ 50 := by
        have : (1 : ℝ) / (1 - s₀) = 50 := by dsimp [s₀]; norm_num
        linarith
      have htail := abs_Lval_sub_partial_le hM_nn hχ_pv (by norm_num : (0 : ℝ) < s₀) U₁
      have hrew : zetaVal s₀ * Lpartial χ U₁ s₀ =
          zetaVal s₀ * Lval χ s₀ + zetaVal s₀ * (Lpartial χ U₁ s₀ - Lval χ s₀) := by ring
      rw [hrew]
      have h1 : zetaVal s₀ * Lval χ s₀ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hz_neg.le hge
      have h2 : zetaVal s₀ * (Lpartial χ U₁ s₀ - Lval χ s₀) ≤ (1 : ℝ) / 100 := by
        have habs : |zetaVal s₀ * (Lpartial χ U₁ s₀ - Lval χ s₀)| ≤ 50 * M * (U₁ : ℝ) ^ (-s₀) := by
          rw [abs_mul, abs_sub_comm]
          have hU_le : ((U₁ + 1 : ℕ) : ℝ) ^ (-s₀) ≤ (U₁ : ℝ) ^ (-s₀) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast Nat.le_succ U₁) (by norm_num)
          calc |zetaVal s₀| * |Lval χ s₀ - Lpartial χ U₁ s₀|
              ≤ 50 * (M * ((U₁ + 1 : ℕ) : ℝ) ^ (-s₀)) :=
                mul_le_mul hz_50 htail (abs_nonneg _) (by norm_num)
            _ ≤ 50 * (M * (U₁ : ℝ) ^ (-s₀)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU_le hM_nn) (by norm_num)
            _ = 50 * M * (U₁ : ℝ) ^ (-s₀) := by ring
        have hU₁_s : (U₁ : ℝ) ^ (-s₀) = (D : ℝ) ^ (-(49 : ℝ) / 25) := by
          rw [hU₁_cast, ← Real.rpow_natCast, ← Real.rpow_mul hD_pos.le]; congr 1; dsimp [s₀]; norm_num
        calc zetaVal s₀ * (Lpartial χ U₁ s₀ - Lval χ s₀)
            ≤ |zetaVal s₀ * (Lpartial χ U₁ s₀ - Lval χ s₀)| := le_abs_self _
          _ ≤ 50 * M * (U₁ : ℝ) ^ (-s₀) := habs
          _ ≤ 50 * (17 * (D : ℝ) ^ ((21 : ℝ) / 40)) * (D : ℝ) ^ (-(49 : ℝ) / 25) := by
              rw [hU₁_s]
              exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hD_pos.le _)
          _ = 850 * (D : ℝ) ^ (-(287 : ℝ) / 200) := by
              rw [mul_assoc, mul_assoc, ← Real.rpow_add hD_pos]
              have hexp : (21 : ℝ) / 40 + -(49 : ℝ) / 25 = -(287 : ℝ) / 200 := by norm_num
              rw [hexp]; ring
          _ ≤ 850 * (2 : ℝ) ^ (-30 : ℤ) := by
              refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
              exact rpow_neg_le_two_pow hD_rbig (by norm_num) (by norm_num)
          _ ≤ (1 : ℝ) / 100 := by norm_num
      linarith
    have hrem : ∑ d ∈ Icc 1 U₁,
          χ d * (d : ℝ) ^ (-s₀) *
            (∑ k ∈ Icc 1 (X₁ / d), (k : ℝ) ^ (-s₀) -
              ((((X₁ : ℝ) / (d : ℝ)) ^ (1 - s₀) - 1) / (1 - s₀) + gammaVal s₀)) ≤ (1 : ℝ) / 100 := by
      calc ∑ d ∈ Icc 1 U₁,
              χ d * (d : ℝ) ^ (-s₀) *
                (∑ k ∈ Icc 1 (X₁ / d), (k : ℝ) ^ (-s₀) -
                  ((((X₁ : ℝ) / (d : ℝ)) ^ (1 - s₀) - 1) / (1 - s₀) + gammaVal s₀))
          ≤ ∑ d ∈ Icc 1 U₁, (2 * (X₁ : ℝ) ^ (-s₀)) := by
            refine Finset.sum_le_sum fun d hd => ?_
            simp only [Finset.mem_Icc] at hd
            have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
            have hY1 : (1 : ℝ) ≤ (X₁ : ℝ) / (d : ℝ) := by
              rw [one_le_div hd_pos]; exact_mod_cast hd.2.trans hU₁X₁
            have hfl : Nat.floor ((X₁ : ℝ) / (d : ℝ)) = X₁ / d := Nat.floor_div_eq_div _ _
            have hem := sum_rpow_euler_maclaurin (by norm_num : (0 : ℝ) < s₀)
              (by norm_num : s₀ < 1) hY1
            rw [hfl] at hem
            have hterm_le : |χ d * (d : ℝ) ^ (-s₀) *
                (∑ k ∈ Icc 1 (X₁ / d), (k : ℝ) ^ (-s₀) -
                  ((((X₁ : ℝ) / (d : ℝ)) ^ (1 - s₀) - 1) / (1 - s₀) + gammaVal s₀))| ≤
                2 * (X₁ : ℝ) ^ (-s₀) := by
              rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hd_pos.le _)]
              have hdiv_pow : ((X₁ : ℝ) / (d : ℝ)) ^ (-s₀) = (X₁ : ℝ) ^ (-s₀) * (d : ℝ) ^ s₀ := by
                rw [Real.div_rpow (by positivity) hd_pos.le, div_eq_mul_inv,
                  ← Real.rpow_neg hd_pos.le, neg_neg]
              calc |χ d| * (d : ℝ) ^ (-s₀) *
                    |∑ k ∈ Icc 1 (X₁ / d), (k : ℝ) ^ (-s₀) -
                      ((((X₁ : ℝ) / (d : ℝ)) ^ (1 - s₀) - 1) / (1 - s₀) + gammaVal s₀)|
                  ≤ 1 * (d : ℝ) ^ (-s₀) * (2 * ((X₁ : ℝ) / (d : ℝ)) ^ (-s₀)) := by
                    refine mul_le_mul (mul_le_mul_of_nonneg_right (hχ1 d)
                      (Real.rpow_nonneg hd_pos.le _)) hem (abs_nonneg _)
                      (mul_nonneg zero_le_one (Real.rpow_nonneg hd_pos.le _))
                _ = 2 * (X₁ : ℝ) ^ (-s₀) * ((d : ℝ) ^ (-s₀) * (d : ℝ) ^ s₀) := by
                    rw [hdiv_pow]; ring
                _ = 2 * (X₁ : ℝ) ^ (-s₀) := by
                    rw [← Real.rpow_add hd_pos, neg_add_cancel, Real.rpow_zero, mul_one]
            exact (le_abs_self _).trans hterm_le
        _ = (U₁ : ℝ) * (2 * (X₁ : ℝ) ^ (-s₀)) := by simp
        _ = 2 * (D : ℝ) ^ (-(48 : ℝ) / 25) := by
            have hX₁_s : (X₁ : ℝ) ^ (-s₀) = (D : ℝ) ^ (-(98 : ℝ) / 25) := by
              rw [hX₁_cast, ← Real.rpow_natCast, ← Real.rpow_mul hD_pos.le]
              congr 1; dsimp [s₀]; norm_num
            rw [hX₁_s, hU₁_cast, ← Real.rpow_natCast]
            calc (D : ℝ) ^ ((2 : ℕ) : ℝ) * (2 * (D : ℝ) ^ (-(98 : ℝ) / 25))
                = 2 * ((D : ℝ) ^ ((2 : ℕ) : ℝ) * (D : ℝ) ^ (-(98 : ℝ) / 25)) := by ring
              _ = 2 * (D : ℝ) ^ (-(48 : ℝ) / 25) := by
                  rw [← Real.rpow_add hD_pos]; congr 2; norm_num
        _ ≤ 2 * (2 : ℝ) ^ (-30 : ℤ) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact rpow_neg_le_two_pow hD_rbig (by norm_num) (by norm_num)
        _ ≤ (1 : ℝ) / 100 := by norm_num
    unfold Lpartial at hmain1 hmain2
    linarith only [hmain1, hmain2, hrem]
  have hS2_le : ∑ k ∈ Icc 1 U₁, (k : ℝ) ^ (-s₀) * ∑ d ∈ Icc (U₁ + 1) (X₁ / k), χ d * (d : ℝ) ^ (-s₀) ≤
      (1 : ℝ) / 100 := by
    have hinner : ∀ k ∈ Icc 1 U₁,
        |∑ d ∈ Icc (U₁ + 1) (X₁ / k), χ d * (d : ℝ) ^ (-s₀)| ≤ M * (U₁ : ℝ) ^ (-s₀) := by
      intro k _
      by_cases hk : U₁ + 1 ≤ X₁ / k
      · have hb := abel_antitone_bound χ (fun d => (d : ℝ) ^ (-s₀)) (by omega) hk hM_nn
          (fun d _ => hχ_pv (U₁ + 1) d)
          (fun d _ => Real.rpow_nonneg (by positivity) _)
          (fun d hd => Real.rpow_le_rpow_of_nonpos
            (by exact_mod_cast (by simp only [Finset.mem_Icc] at hd; omega : 0 < d))
            (by exact_mod_cast Nat.le_succ d) (by norm_num))
        have hU_le : ((U₁ + 1 : ℕ) : ℝ) ^ (-s₀) ≤ (U₁ : ℝ) ^ (-s₀) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast Nat.le_succ U₁) (by norm_num)
        exact hb.trans (mul_le_mul_of_nonneg_left hU_le hM_nn)
      · have hemp : Icc (U₁ + 1) (X₁ / k) = ∅ := Finset.Icc_eq_empty (by omega)
        rw [hemp, Finset.sum_empty, abs_zero]
        exact mul_nonneg hM_nn (Real.rpow_nonneg (by positivity) _)
    calc ∑ k ∈ Icc 1 U₁, (k : ℝ) ^ (-s₀) * ∑ d ∈ Icc (U₁ + 1) (X₁ / k), χ d * (d : ℝ) ^ (-s₀)
        ≤ ∑ k ∈ Icc 1 U₁, (k : ℝ) ^ (-s₀) * (M * (U₁ : ℝ) ^ (-s₀)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hinner k hk))
            (Real.rpow_nonneg (by positivity) _)
      _ = (∑ k ∈ Icc 1 U₁, (k : ℝ) ^ (-s₀)) * (M * (U₁ : ℝ) ^ (-s₀)) := by rw [← Finset.sum_mul]
      _ ≤ ((U₁ : ℝ) ^ (1 - s₀) * (Real.log (U₁ : ℝ) + 1)) * (M * (U₁ : ℝ) ^ (-s₀)) := by
          exact mul_le_mul_of_nonneg_right (sum_rpow_neg_le (by norm_num) hU₁1)
            (mul_nonneg hM_nn (Real.rpow_nonneg (by positivity) _))
      _ ≤ ((U₁ : ℝ) ^ ((1 : ℝ) / 50) * (5 * (U₁ : ℝ) ^ ((1 : ℝ) / 10))) *
            ((17 * (D : ℝ) ^ ((21 : ℝ) / 40)) * (U₁ : ℝ) ^ (-s₀)) := by
          have hs_sub : (1 : ℝ) - s₀ = (1 : ℝ) / 50 := by dsimp [s₀]; norm_num
          rw [hs_sub]
          refine mul_le_mul
            (mul_le_mul_of_nonneg_left (log_add_one_le_5_rpow (by exact_mod_cast hU₁1))
              (Real.rpow_nonneg (by positivity) _))
            (mul_le_mul_of_nonneg_right hM_le (Real.rpow_nonneg (by positivity) _))
            (mul_nonneg hM_nn (Real.rpow_nonneg (by positivity) _))
            (by positivity)
      _ = 85 * (D : ℝ) ^ (-(239 : ℝ) / 200) := by
          have hU1 : (U₁ : ℝ) ^ ((1 : ℝ) / 50) = (D : ℝ) ^ ((1 : ℝ) / 25) := by
            rw [hU₁_cast, ← Real.rpow_natCast, ← Real.rpow_mul hD_pos.le]; congr 1; norm_num
          have hU2 : (U₁ : ℝ) ^ ((1 : ℝ) / 10) = (D : ℝ) ^ ((1 : ℝ) / 5) := by
            rw [hU₁_cast, ← Real.rpow_natCast, ← Real.rpow_mul hD_pos.le]; congr 1; norm_num
          have hU3 : (U₁ : ℝ) ^ (-s₀) = (D : ℝ) ^ (-(49 : ℝ) / 25) := by
            rw [hU₁_cast, ← Real.rpow_natCast, ← Real.rpow_mul hD_pos.le]
            congr 1; dsimp [s₀]; norm_num
          rw [hU1, hU2, hU3]
          have hcomb : (D : ℝ) ^ ((1 : ℝ) / 25) * (D : ℝ) ^ ((1 : ℝ) / 5) *
              ((D : ℝ) ^ ((21 : ℝ) / 40) * (D : ℝ) ^ (-(49 : ℝ) / 25)) =
              (D : ℝ) ^ (-(239 : ℝ) / 200) := by
            rw [← Real.rpow_add hD_pos, ← Real.rpow_add hD_pos, ← Real.rpow_add hD_pos]
            congr 1; norm_num
          calc (D : ℝ) ^ ((1 : ℝ) / 25) * (5 * (D : ℝ) ^ ((1 : ℝ) / 5)) *
                (17 * (D : ℝ) ^ ((21 : ℝ) / 40) * (D : ℝ) ^ (-(49 : ℝ) / 25))
              = 85 * ((D : ℝ) ^ ((1 : ℝ) / 25) * (D : ℝ) ^ ((1 : ℝ) / 5) *
                  ((D : ℝ) ^ ((21 : ℝ) / 40) * (D : ℝ) ^ (-(49 : ℝ) / 25))) := by ring
            _ = 85 * (D : ℝ) ^ (-(239 : ℝ) / 200) := by rw [hcomb]
      _ ≤ 85 * (2 : ℝ) ^ (-30 : ℤ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact rpow_neg_le_two_pow hD_rbig (by norm_num) (by norm_num)
      _ ≤ (1 : ℝ) / 100 := by norm_num
  linarith

/- Partial sum bounds for double and triple convolutions -/

private lemma partial_sum_dconv2_le {χ₂ χ₃ : ℕ → ℝ} {M₂ M₃ : ℝ}
    (hM₂ : 1 ≤ M₂) (hM₃ : 1 ≤ M₃)
    (hχ₂ : ∀ a b : ℕ, |∑ n ∈ Icc a b, χ₂ n| ≤ M₂)
    (hχ₃ : ∀ a b : ℕ, |∑ n ∈ Icc a b, χ₃ n| ≤ M₃)
    (hχ₂1 : ∀ n, |χ₂ n| ≤ 1) (hχ₃1 : ∀ n, |χ₃ n| ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Icc 1 N, dconv χ₂ χ₃ n| ≤ 3 * Real.sqrt ((N : ℝ) * M₂ * M₃) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  set t : ℝ := Real.sqrt ((N : ℝ) * M₃ / M₂)
  have ht_pos : 0 < t := Real.sqrt_pos.mpr (by positivity)
  by_cases ht1 : t < 1
  · have hNM : (N : ℝ) * M₃ < M₂ := by
      have hsq : t ^ 2 < 1 := by nlinarith
      rw [Real.sq_sqrt (by positivity)] at hsq
      rwa [div_lt_one (by linarith)] at hsq
    have hcomm : ∑ n ∈ Icc 1 N, dconv χ₂ χ₃ n =
        ∑ k ∈ Icc 1 N, χ₂ k * ∑ d ∈ Icc 1 (N / k), χ₃ d := by
      have hc : ∀ n, dconv χ₂ χ₃ n = dconv χ₃ χ₂ n := fun n => dconv_comm _ _ n
      simp_rw [hc]
      have h := dirichlet_hyperbola χ₃ χ₂ (fun _ => 1) hN le_rfl (fun _ _ _ _ => by ring)
      simp only [mul_one] at h
      rw [h]
      have h2 : ∑ d ∈ Icc 1 (N / N), χ₃ d * ∑ k ∈ Icc (N + 1) (N / d), χ₂ k = 0 := by
        refine Finset.sum_eq_zero fun d _ => ?_
        have hemp : Icc (N + 1) (N / d) = ∅ := Finset.Icc_eq_empty (by have := Nat.div_le_self N d; omega)
        rw [hemp, Finset.sum_empty, mul_zero]
      rw [h2, add_zero]
    rw [hcomm]
    calc |∑ k ∈ Icc 1 N, χ₂ k * ∑ d ∈ Icc 1 (N / k), χ₃ d|
        ≤ ∑ k ∈ Icc 1 N, |χ₂ k * ∑ d ∈ Icc 1 (N / k), χ₃ d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Icc 1 N, M₃ := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          exact (mul_le_mul (hχ₂1 k) (hχ₃ 1 (N / k)) (abs_nonneg _) zero_le_one).trans (by linarith)
      _ = (N : ℝ) * M₃ := by simp
      _ ≤ Real.sqrt ((N : ℝ) * M₂ * M₃) := by
          rw [Real.le_sqrt (by positivity) (by positivity)]
          calc ((N : ℝ) * M₃) ^ 2 = ((N : ℝ) * M₃) * ((N : ℝ) * M₃) := sq _
            _ ≤ M₂ * ((N : ℝ) * M₃) := mul_le_mul_of_nonneg_right hNM.le (by positivity)
            _ = (N : ℝ) * M₂ * M₃ := by ring
      _ ≤ 3 * Real.sqrt ((N : ℝ) * M₂ * M₃) := by linarith [Real.sqrt_nonneg ((N : ℝ) * M₂ * M₃)]
  · push Not at ht1
    by_cases htN : (N : ℝ) < t
    · have hNM : (N : ℝ) * M₂ < M₃ := by
        have hsq : (N : ℝ) ^ 2 < t ^ 2 := by nlinarith
        rw [Real.sq_sqrt (by positivity), lt_div_iff₀ (by linarith)] at hsq
        nlinarith
      have h := dirichlet_hyperbola χ₂ χ₃ (fun _ => 1) hN le_rfl (fun _ _ _ _ => by ring)
      simp only [mul_one] at h
      have h2 : ∑ k ∈ Icc 1 (N / N), χ₂ k * ∑ d ∈ Icc (N + 1) (N / k), χ₃ d = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        have hemp : Icc (N + 1) (N / k) = ∅ := Finset.Icc_eq_empty (by have := Nat.div_le_self N k; omega)
        rw [hemp, Finset.sum_empty, mul_zero]
      rw [h, h2, add_zero]
      calc |∑ d ∈ Icc 1 N, χ₃ d * ∑ k ∈ Icc 1 (N / d), χ₂ k|
          ≤ ∑ d ∈ Icc 1 N, |χ₃ d * ∑ k ∈ Icc 1 (N / d), χ₂ k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ Icc 1 N, M₂ := by
            refine Finset.sum_le_sum fun d _ => ?_
            rw [abs_mul]
            exact (mul_le_mul (hχ₃1 d) (hχ₂ 1 (N / d)) (abs_nonneg _) zero_le_one).trans (by linarith)
        _ = (N : ℝ) * M₂ := by simp
        _ ≤ Real.sqrt ((N : ℝ) * M₂ * M₃) := by
            rw [Real.le_sqrt (by positivity) (by positivity)]
            calc ((N : ℝ) * M₂) ^ 2 = ((N : ℝ) * M₂) * ((N : ℝ) * M₂) := sq _
              _ ≤ ((N : ℝ) * M₂) * M₃ := mul_le_mul_of_nonneg_left hNM.le (by positivity)
              _ = (N : ℝ) * M₂ * M₃ := by ring
        _ ≤ 3 * Real.sqrt ((N : ℝ) * M₂ * M₃) := by linarith [Real.sqrt_nonneg ((N : ℝ) * M₂ * M₃)]
    · push Not at htN
      set U : ℕ := Nat.floor t
      have hU1 : 1 ≤ U := Nat.le_floor (by norm_cast)
      have hUN : U ≤ N := Nat.floor_le_of_le htN
      have hUt : (U : ℝ) ≤ t := Nat.floor_le ht_pos.le
      have ht2U : t ≤ 2 * (U : ℝ) := by
        have hlt : t < (U : ℝ) + 1 := Nat.lt_floor_add_one t
        have : (1 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU1
        linarith
      have h := dirichlet_hyperbola χ₂ χ₃ (fun _ => 1) hU1 hUN (fun _ _ _ _ => by ring)
      simp only [mul_one] at h
      rw [h]
      have hb1 : |∑ d ∈ Icc 1 U, χ₃ d * ∑ k ∈ Icc 1 (N / d), χ₂ k| ≤ (U : ℝ) * M₂ := by
        calc |∑ d ∈ Icc 1 U, χ₃ d * ∑ k ∈ Icc 1 (N / d), χ₂ k|
            ≤ ∑ d ∈ Icc 1 U, |χ₃ d * ∑ k ∈ Icc 1 (N / d), χ₂ k| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ d ∈ Icc 1 U, M₂ := by
              refine Finset.sum_le_sum fun d _ => ?_
              rw [abs_mul]
              exact (mul_le_mul (hχ₃1 d) (hχ₂ 1 (N / d)) (abs_nonneg _) zero_le_one).trans (by linarith)
          _ = (U : ℝ) * M₂ := by simp
      have hb2 : |∑ k ∈ Icc 1 (N / U), χ₂ k * ∑ d ∈ Icc (U + 1) (N / k), χ₃ d| ≤
          ((N / U : ℕ) : ℝ) * M₃ := by
        calc |∑ k ∈ Icc 1 (N / U), χ₂ k * ∑ d ∈ Icc (U + 1) (N / k), χ₃ d|
            ≤ ∑ k ∈ Icc 1 (N / U), |χ₂ k * ∑ d ∈ Icc (U + 1) (N / k), χ₃ d| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ Icc 1 (N / U), M₃ := by
              refine Finset.sum_le_sum fun k _ => ?_
              rw [abs_mul]
              exact (mul_le_mul (hχ₂1 k) (hχ₃ (U + 1) (N / k)) (abs_nonneg _) zero_le_one).trans (by linarith)
          _ = ((N / U : ℕ) : ℝ) * M₃ := by simp
      have hU_pos : (0 : ℝ) < (U : ℝ) := by exact_mod_cast (by omega : 0 < U)
      have hNU_le : ((N / U : ℕ) : ℝ) ≤ 2 * (N : ℝ) / t := by
        calc ((N / U : ℕ) : ℝ) ≤ (N : ℝ) / (U : ℝ) := by
              rw [le_div_iff₀ hU_pos]; exact_mod_cast Nat.div_mul_le_self N U
          _ ≤ 2 * (N : ℝ) / t := by
              rw [div_le_div_iff₀ hU_pos ht_pos]; nlinarith
      have htM2 : t * M₂ = Real.sqrt ((N : ℝ) * M₂ * M₃) := by
        have hsq : (t * M₂) ^ 2 = (N : ℝ) * M₂ * M₃ := by
          dsimp [t]
          rw [mul_pow, Real.sq_sqrt (by positivity)]
          field_simp [show M₂ ≠ 0 by linarith]
        rw [← Real.sqrt_sq (by positivity : 0 ≤ t * M₂), hsq]
      have hNM3t : (N : ℝ) / t * M₃ = Real.sqrt ((N : ℝ) * M₂ * M₃) := by
        rw [div_mul_eq_mul_div, div_eq_iff ht_pos.ne']
        dsimp [t]
        rw [← Real.sqrt_mul (by positivity)]
        have : (N : ℝ) * M₂ * M₃ * ((N : ℝ) * M₃ / M₂) = ((N : ℝ) * M₃) ^ 2 := by
          field_simp [show M₂ ≠ 0 by linarith]
        rw [this, Real.sqrt_sq (by positivity)]
      calc |(∑ d ∈ Icc 1 U, χ₃ d * ∑ k ∈ Icc 1 (N / d), χ₂ k) +
            ∑ k ∈ Icc 1 (N / U), χ₂ k * ∑ d ∈ Icc (U + 1) (N / k), χ₃ d|
          ≤ |∑ d ∈ Icc 1 U, χ₃ d * ∑ k ∈ Icc 1 (N / d), χ₂ k| +
            |∑ k ∈ Icc 1 (N / U), χ₂ k * ∑ d ∈ Icc (U + 1) (N / k), χ₃ d| := abs_add_le _ _
        _ ≤ (U : ℝ) * M₂ + ((N / U : ℕ) : ℝ) * M₃ := by linarith
        _ ≤ t * M₂ + (2 * (N : ℝ) / t) * M₃ := by
            have h1 : (U : ℝ) * M₂ ≤ t * M₂ := mul_le_mul_of_nonneg_right hUt (by linarith)
            have h2 : ((N / U : ℕ) : ℝ) * M₃ ≤ (2 * (N : ℝ) / t) * M₃ :=
              mul_le_mul_of_nonneg_right hNU_le (by linarith)
            linarith
        _ = t * M₂ + 2 * ((N : ℝ) / t * M₃) := by ring
        _ = 3 * Real.sqrt ((N : ℝ) * M₂ * M₃) := by rw [htM2, hNM3t]; ring

private lemma partial_sum_dconv3_le {χ₁ χ₂ χ₃ : ℕ → ℝ} {M₁ M₂ M₃ : ℝ}
    (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (hM₃ : 1 ≤ M₃)
    (hχ₁ : ∀ a b : ℕ, |∑ n ∈ Icc a b, χ₁ n| ≤ M₁)
    (hχ₂ : ∀ a b : ℕ, |∑ n ∈ Icc a b, χ₂ n| ≤ M₂)
    (hχ₃ : ∀ a b : ℕ, |∑ n ∈ Icc a b, χ₃ n| ≤ M₃)
    (hχ₁1 : ∀ n, |χ₁ n| ≤ 1) (hχ₂1 : ∀ n, |χ₂ n| ≤ 1) (hχ₃1 : ∀ n, |χ₃ n| ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Icc 1 N, dconv χ₁ (dconv χ₂ χ₃) n| ≤
      38 * (M₁ * M₂ * M₃) ^ ((1 : ℝ) / 3) * (N : ℝ) ^ ((7 : ℝ) / 10) := by
  set h := dconv χ₂ χ₃
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  set A : ℝ := M₁ * (Real.log (N : ℝ) + 1)
  set B : ℝ := Real.sqrt (M₂ * M₃) * (N : ℝ)
  have hA_ge1 : 1 ≤ A := by
    have : 1 ≤ Real.log (N : ℝ) + 1 := by linarith [Real.log_nonneg hN_ge1]
    dsimp [A]; nlinarith
  have hB_ge1 : 1 ≤ B := by
    have : 1 ≤ Real.sqrt (M₂ * M₃) := by
      rw [Real.le_sqrt zero_le_one (by positivity)]; nlinarith
    dsimp [B]; nlinarith
  have hA_pos : 0 < A := by linarith
  have hB_pos : 0 < B := by linarith
  have hH_bound : ∀ n : ℕ, 1 ≤ n → |∑ d ∈ Icc 1 n, h d| ≤ 3 * Real.sqrt (M₂ * M₃) * Real.sqrt (n : ℝ) := by
    intro n hn
    have hb := partial_sum_dconv2_le hM₂ hM₃ hχ₂ hχ₃ hχ₂1 hχ₃1 hn
    refine hb.trans_eq ?_
    have : (n : ℝ) * M₂ * M₃ = (M₂ * M₃) * (n : ℝ) := by ring
    rw [this, Real.sqrt_mul (by positivity)]; ring
  have hsum_h_abs : ∀ U : ℕ, 1 ≤ U → U ≤ N → ∑ d ∈ Icc 1 U, |h d| ≤ (U : ℝ) * (Real.log (N : ℝ) + 1) := by
    intro U hU1 hUN
    calc ∑ d ∈ Icc 1 U, |h d|
        ≤ ∑ d ∈ Icc 1 U, dconv (fun _ => 1) (fun _ => 1) d :=
          Finset.sum_le_sum fun d hd => abs_dconv_le (fun n _ => hχ₂1 n) (fun n _ => hχ₃1 n)
            (Finset.mem_Icc.mp hd).1
      _ ≤ (U : ℝ) * (Real.log (U : ℝ) + 1) := sum_tau_le hU1
      _ ≤ (U : ℝ) * (Real.log (N : ℝ) + 1) := by
          have hlog : Real.log (U : ℝ) ≤ Real.log (N : ℝ) :=
            Real.log_le_log (by exact_mod_cast hU1) (by exact_mod_cast hUN)
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hAB_bound : |∑ n ∈ Icc 1 N, dconv χ₁ h n| ≤ 19 * A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) := by
    set t : ℝ := (B / A) ^ ((2 : ℝ) / 3)
    have ht_pos : 0 < t := Real.rpow_pos_of_pos (div_pos hB_pos hA_pos) _
    have ht_mul : A * t = A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) := by
      dsimp [t]
      rw [Real.div_rpow hB_pos.le hA_pos.le, div_eq_mul_inv, ← Real.rpow_neg hA_pos.le, ← neg_div]
      calc A * (B ^ ((2 : ℝ) / 3) * A ^ (-(2 : ℝ) / 3))
          = (A ^ (1 : ℝ) * A ^ (-(2 : ℝ) / 3)) * B ^ ((2 : ℝ) / 3) := by rw [Real.rpow_one]; ring
        _ = A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) := by
            rw [← Real.rpow_add hA_pos]; congr 2; norm_num
    have hB_div_sqrt_t : B / Real.sqrt t = A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) := by
      rw [Real.sqrt_eq_rpow]
      dsimp [t]
      rw [← Real.rpow_mul (div_pos hB_pos hA_pos).le]
      have hexp : (2 : ℝ) / 3 * ((1 : ℝ) / 2) = (1 : ℝ) / 3 := by norm_num
      rw [hexp, Real.div_rpow hB_pos.le hA_pos.le, div_div_eq_mul_div,
        div_eq_mul_inv, ← Real.rpow_neg hB_pos.le, ← neg_div]
      calc B * A ^ ((1 : ℝ) / 3) * B ^ (-(1 : ℝ) / 3)
          = A ^ ((1 : ℝ) / 3) * (B ^ (1 : ℝ) * B ^ (-(1 : ℝ) / 3)) := by rw [Real.rpow_one]; ring
        _ = A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) := by
            rw [← Real.rpow_add hB_pos]; congr 2; norm_num
    by_cases ht1 : t < 1
    · have hBA : B < A := by
        by_contra hle; push Not at hle
        have : 1 ≤ t := Real.one_le_rpow ((one_le_div hA_pos).mpr hle) (by norm_num)
        linarith
      have hcomm : ∑ n ∈ Icc 1 N, dconv χ₁ h n =
          ∑ k ∈ Icc 1 N, χ₁ k * ∑ d ∈ Icc 1 (N / k), h d := by
        have hc : ∀ n, dconv χ₁ h n = dconv h χ₁ n := fun n => dconv_comm _ _ n
        simp_rw [hc]
        have hhyp := dirichlet_hyperbola h χ₁ (fun _ => 1) hN le_rfl (fun _ _ _ _ => by ring)
        simp only [mul_one] at hhyp
        rw [hhyp]
        have h2 : ∑ d ∈ Icc 1 (N / N), h d * ∑ k ∈ Icc (N + 1) (N / d), χ₁ k = 0 := by
          refine Finset.sum_eq_zero fun d _ => ?_
          have hemp : Icc (N + 1) (N / d) = ∅ := Finset.Icc_eq_empty (by have := Nat.div_le_self N d; omega)
          rw [hemp, Finset.sum_empty, mul_zero]
        rw [h2, add_zero]
      rw [hcomm]
      calc |∑ k ∈ Icc 1 N, χ₁ k * ∑ d ∈ Icc 1 (N / k), h d|
          ≤ ∑ k ∈ Icc 1 N, |χ₁ k * ∑ d ∈ Icc 1 (N / k), h d| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Icc 1 N, 3 * Real.sqrt (M₂ * M₃) * Real.sqrt (N : ℝ) * ((1 : ℝ) / Real.sqrt (k : ℝ)) := by
            refine Finset.sum_le_sum fun k hk => ?_
            simp only [Finset.mem_Icc] at hk
            have hk_pos : 1 ≤ N / k := Nat.div_pos hk.2 hk.1
            rw [abs_mul]
            calc |χ₁ k| * |∑ d ∈ Icc 1 (N / k), h d|
                ≤ 1 * (3 * Real.sqrt (M₂ * M₃) * Real.sqrt ((N / k : ℕ) : ℝ)) :=
                  mul_le_mul (hχ₁1 k) (hH_bound (N / k) hk_pos) (abs_nonneg _) zero_le_one
              _ ≤ 3 * Real.sqrt (M₂ * M₃) * Real.sqrt ((N : ℝ) / (k : ℝ)) := by
                  rw [one_mul]
                  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
                  rw [le_div_iff₀ (by exact_mod_cast (by omega : 0 < k))]
                  exact_mod_cast Nat.div_mul_le_self N k
              _ = 3 * Real.sqrt (M₂ * M₃) * Real.sqrt (N : ℝ) * ((1 : ℝ) / Real.sqrt (k : ℝ)) := by
                  rw [Real.sqrt_div hN_pos.le]; ring
        _ = 3 * Real.sqrt (M₂ * M₃) * Real.sqrt (N : ℝ) * ∑ k ∈ Icc 1 N, (1 : ℝ) / Real.sqrt (k : ℝ) := by
            rw [← Finset.mul_sum]
        _ ≤ 3 * Real.sqrt (M₂ * M₃) * Real.sqrt (N : ℝ) * (2 * Real.sqrt (N : ℝ)) :=
            mul_le_mul_of_nonneg_left (sum_inv_sqrt_le N) (by positivity)
        _ = 6 * B := by
            dsimp [B]
            calc 3 * Real.sqrt (M₂ * M₃) * Real.sqrt (N : ℝ) * (2 * Real.sqrt (N : ℝ))
                = 6 * Real.sqrt (M₂ * M₃) * (Real.sqrt (N : ℝ) ^ 2) := by ring
              _ = 6 * (Real.sqrt (M₂ * M₃) * (N : ℝ)) := by rw [Real.sq_sqrt hN_pos.le]; ring
        _ ≤ 6 * (A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3)) := by
            have hB_le : B ≤ A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) := by
              calc B = B ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) := by
                    rw [← Real.rpow_add hB_pos]; norm_num
                _ ≤ A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) :=
                    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hB_pos.le hBA.le (by norm_num))
                      (Real.rpow_nonneg hB_pos.le _)
            linarith
        _ ≤ 19 * A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) := by
            have : 0 ≤ A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) := by positivity
            linarith
    · push Not at ht1
      by_cases htN : (N : ℝ) < t
      · have hAN_le : A * (N : ℝ) ≤ A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) := by
          rw [← ht_mul]
          exact mul_le_mul_of_nonneg_left htN.le hA_pos.le
        have hhyp := dirichlet_hyperbola χ₁ h (fun _ => 1) hN le_rfl (fun _ _ _ _ => by ring)
        simp only [mul_one] at hhyp
        have h2 : ∑ k ∈ Icc 1 (N / N), χ₁ k * ∑ d ∈ Icc (N + 1) (N / k), h d = 0 := by
          refine Finset.sum_eq_zero fun k _ => ?_
          have hemp : Icc (N + 1) (N / k) = ∅ := Finset.Icc_eq_empty (by have := Nat.div_le_self N k; omega)
          rw [hemp, Finset.sum_empty, mul_zero]
        rw [hhyp, h2, add_zero]
        calc |∑ d ∈ Icc 1 N, h d * ∑ k ∈ Icc 1 (N / d), χ₁ k|
            ≤ ∑ d ∈ Icc 1 N, |h d * ∑ k ∈ Icc 1 (N / d), χ₁ k| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ d ∈ Icc 1 N, |h d| * M₁ := by
              refine Finset.sum_le_sum fun d _ => ?_
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (hχ₁ 1 (N / d)) (abs_nonneg _)
          _ = (∑ d ∈ Icc 1 N, |h d|) * M₁ := by rw [← Finset.sum_mul]
          _ ≤ ((N : ℝ) * (Real.log (N : ℝ) + 1)) * M₁ :=
              mul_le_mul_of_nonneg_right (hsum_h_abs N hN le_rfl) (by linarith)
          _ = A * (N : ℝ) := by dsimp [A]; ring
          _ ≤ A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) := hAN_le
          _ ≤ 19 * A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) := by
              have : 0 ≤ A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) := by positivity
              linarith
      · push Not at htN
        set U : ℕ := Nat.floor t
        have hU1 : 1 ≤ U := Nat.le_floor (by norm_cast)
        have hUN : U ≤ N := Nat.floor_le_of_le htN
        have hUt : (U : ℝ) ≤ t := Nat.floor_le ht_pos.le
        have hU_pos : (0 : ℝ) < (U : ℝ) := by exact_mod_cast (by omega : 0 < U)
        have ht2U : t ≤ 2 * (U : ℝ) := by
          have hlt : t < (U : ℝ) + 1 := Nat.lt_floor_add_one t
          have : (1 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU1
          linarith
        have hhyp := dirichlet_hyperbola χ₁ h (fun _ => 1) hU1 hUN (fun _ _ _ _ => by ring)
        simp only [mul_one] at hhyp
        rw [hhyp]
        have hb1 : |∑ d ∈ Icc 1 U, h d * ∑ k ∈ Icc 1 (N / d), χ₁ k| ≤
            A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) := by
          calc |∑ d ∈ Icc 1 U, h d * ∑ k ∈ Icc 1 (N / d), χ₁ k|
              ≤ ∑ d ∈ Icc 1 U, |h d * ∑ k ∈ Icc 1 (N / d), χ₁ k| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ d ∈ Icc 1 U, |h d| * M₁ := by
                refine Finset.sum_le_sum fun d _ => ?_
                rw [abs_mul]
                exact mul_le_mul_of_nonneg_left (hχ₁ 1 (N / d)) (abs_nonneg _)
            _ = (∑ d ∈ Icc 1 U, |h d|) * M₁ := by rw [← Finset.sum_mul]
            _ ≤ ((U : ℝ) * (Real.log (N : ℝ) + 1)) * M₁ :=
                mul_le_mul_of_nonneg_right (hsum_h_abs U hU1 hUN) (by linarith)
            _ = A * (U : ℝ) := by dsimp [A]; ring
            _ ≤ A * t := mul_le_mul_of_nonneg_left hUt hA_pos.le
            _ = A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) := ht_mul
        have hb2 : |∑ k ∈ Icc 1 (N / U), χ₁ k * ∑ d ∈ Icc (U + 1) (N / k), h d| ≤
            18 * (A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3)) := by
          have hterm : ∀ k ∈ Icc 1 (N / U),
              |χ₁ k * ∑ d ∈ Icc (U + 1) (N / k), h d| ≤
                3 * Real.sqrt (M₂ * M₃) * Real.sqrt (N : ℝ) * ((1 : ℝ) / Real.sqrt (k : ℝ)) +
                3 * Real.sqrt (M₂ * M₃) * Real.sqrt (U : ℝ) := by
            intro k hk
            simp only [Finset.mem_Icc] at hk
            rw [abs_mul]
            have hinner : |∑ d ∈ Icc (U + 1) (N / k), h d| ≤
                3 * Real.sqrt (M₂ * M₃) * Real.sqrt (N : ℝ) * ((1 : ℝ) / Real.sqrt (k : ℝ)) +
                3 * Real.sqrt (M₂ * M₃) * Real.sqrt (U : ℝ) := by
              by_cases hle : U + 1 ≤ N / k
              · have hsplit : ∑ d ∈ Icc (U + 1) (N / k), h d =
                    (∑ d ∈ Icc 1 (N / k), h d) - (∑ d ∈ Icc 1 U, h d) := by
                  have hunion : Icc 1 (N / k) = Icc 1 U ∪ Icc (U + 1) (N / k) := by
                    ext d; simp only [Finset.mem_Icc, Finset.mem_union]; omega
                  have hdisj : Disjoint (Icc 1 U) (Icc (U + 1) (N / k)) := by
                    rw [Finset.disjoint_left]
                    intro d hd1 hd2; simp only [Finset.mem_Icc] at hd1 hd2; omega
                  rw [hunion, Finset.sum_union hdisj]; ring
                rw [hsplit]
                have h1 := hH_bound (N / k) (by omega)
                have h2 := hH_bound U hU1
                have hsq_le : Real.sqrt ((N / k : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) * ((1 : ℝ) / Real.sqrt (k : ℝ)) := by
                  have hdiv : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / (k : ℝ) := by
                    rw [le_div_iff₀ (by exact_mod_cast (by omega : 0 < k))]
                    exact_mod_cast Nat.div_mul_le_self N k
                  calc Real.sqrt ((N / k : ℕ) : ℝ) ≤ Real.sqrt ((N : ℝ) / (k : ℝ)) := Real.sqrt_le_sqrt hdiv
                    _ = Real.sqrt (N : ℝ) * ((1 : ℝ) / Real.sqrt (k : ℝ)) := by
                        rw [Real.sqrt_div hN_pos.le]; ring
                calc |(∑ d ∈ Icc 1 (N / k), h d) - (∑ d ∈ Icc 1 U, h d)|
                    ≤ |∑ d ∈ Icc 1 (N / k), h d| + |∑ d ∈ Icc 1 U, h d| := abs_sub _ _
                  _ ≤ 3 * Real.sqrt (M₂ * M₃) * Real.sqrt ((N / k : ℕ) : ℝ) +
                      3 * Real.sqrt (M₂ * M₃) * Real.sqrt (U : ℝ) := by linarith
                  _ ≤ 3 * Real.sqrt (M₂ * M₃) * (Real.sqrt (N : ℝ) * ((1 : ℝ) / Real.sqrt (k : ℝ))) +
                      3 * Real.sqrt (M₂ * M₃) * Real.sqrt (U : ℝ) := by
                      linarith [mul_le_mul_of_nonneg_left hsq_le
                        (by positivity : 0 ≤ 3 * Real.sqrt (M₂ * M₃))]
                  _ = _ := by ring
              · have hemp : Icc (U + 1) (N / k) = ∅ := Finset.Icc_eq_empty (by omega)
                rw [hemp, Finset.sum_empty, abs_zero]
                positivity
            calc |χ₁ k| * |∑ d ∈ Icc (U + 1) (N / k), h d|
                ≤ 1 * (3 * Real.sqrt (M₂ * M₃) * Real.sqrt (N : ℝ) * ((1 : ℝ) / Real.sqrt (k : ℝ)) +
                    3 * Real.sqrt (M₂ * M₃) * Real.sqrt (U : ℝ)) :=
                  mul_le_mul (hχ₁1 k) hinner (abs_nonneg _) zero_le_one
              _ = _ := one_mul _
          have hNU_le : ((N / U : ℕ) : ℝ) ≤ (N : ℝ) / (U : ℝ) := by
            rw [le_div_iff₀ hU_pos]; exact_mod_cast Nat.div_mul_le_self N U
          have hsq_NU : Real.sqrt ((N / U : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) / Real.sqrt (U : ℝ) := by
            rw [← Real.sqrt_div hN_pos.le]; exact Real.sqrt_le_sqrt hNU_le
          have hinv_sqU : (1 : ℝ) / Real.sqrt (U : ℝ) ≤ 2 / Real.sqrt t := by
            have hsq_t : Real.sqrt t ≤ 2 * Real.sqrt (U : ℝ) := by
              calc Real.sqrt t ≤ Real.sqrt (2 * (U : ℝ)) := Real.sqrt_le_sqrt ht2U
                _ = Real.sqrt 2 * Real.sqrt (U : ℝ) := Real.sqrt_mul (by norm_num) _
                _ ≤ 2 * Real.sqrt (U : ℝ) := by
                    have hsq2 : Real.sqrt 2 ≤ 2 := by
                      rw [Real.sqrt_le_left (by norm_num)]; norm_num
                    exact mul_le_mul_of_nonneg_right hsq2 (Real.sqrt_nonneg _)
            rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hU_pos) (Real.sqrt_pos.mpr ht_pos)]
            linarith
          calc |∑ k ∈ Icc 1 (N / U), χ₁ k * ∑ d ∈ Icc (U + 1) (N / k), h d|
              ≤ ∑ k ∈ Icc 1 (N / U), |χ₁ k * ∑ d ∈ Icc (U + 1) (N / k), h d| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ k ∈ Icc 1 (N / U),
                  (3 * Real.sqrt (M₂ * M₃) * Real.sqrt (N : ℝ) * ((1 : ℝ) / Real.sqrt (k : ℝ)) +
                   3 * Real.sqrt (M₂ * M₃) * Real.sqrt (U : ℝ)) :=
                Finset.sum_le_sum hterm
            _ = 3 * Real.sqrt (M₂ * M₃) * Real.sqrt (N : ℝ) *
                  (∑ k ∈ Icc 1 (N / U), (1 : ℝ) / Real.sqrt (k : ℝ)) +
                ((N / U : ℕ) : ℝ) * (3 * Real.sqrt (M₂ * M₃) * Real.sqrt (U : ℝ)) := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc,
                  nsmul_eq_mul, Nat.add_sub_cancel]
            _ ≤ 3 * Real.sqrt (M₂ * M₃) * Real.sqrt (N : ℝ) * (2 * Real.sqrt ((N / U : ℕ) : ℝ)) +
                ((N : ℝ) / (U : ℝ)) * (3 * Real.sqrt (M₂ * M₃) * Real.sqrt (U : ℝ)) := by
                have h1 := mul_le_mul_of_nonneg_left (sum_inv_sqrt_le (N / U))
                  (by positivity : 0 ≤ 3 * Real.sqrt (M₂ * M₃) * Real.sqrt (N : ℝ))
                have h2 := mul_le_mul_of_nonneg_right hNU_le
                  (by positivity : 0 ≤ 3 * Real.sqrt (M₂ * M₃) * Real.sqrt (U : ℝ))
                linarith
            _ ≤ 3 * Real.sqrt (M₂ * M₃) * Real.sqrt (N : ℝ) *
                  (2 * (Real.sqrt (N : ℝ) / Real.sqrt (U : ℝ))) +
                ((N : ℝ) / (U : ℝ)) * (3 * Real.sqrt (M₂ * M₃) * Real.sqrt (U : ℝ)) := by
                have h1 := mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hsq_NU (by norm_num : (0 : ℝ) ≤ 2))
                  (by positivity : 0 ≤ 3 * Real.sqrt (M₂ * M₃) * Real.sqrt (N : ℝ))
                linarith
            _ = 9 * B * ((1 : ℝ) / Real.sqrt (U : ℝ)) := by
                have h1 : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
                  Real.mul_self_sqrt hN_pos.le
                have h2 : Real.sqrt (U : ℝ) / (U : ℝ) = 1 / Real.sqrt (U : ℝ) := by
                  rw [div_eq_div_iff hU_pos.ne' (Real.sqrt_pos.mpr hU_pos).ne', one_mul,
                    Real.mul_self_sqrt hU_pos.le]
                dsimp [B]
                calc 3 * Real.sqrt (M₂ * M₃) * Real.sqrt (N : ℝ) *
                      (2 * (Real.sqrt (N : ℝ) / Real.sqrt (U : ℝ))) +
                    (N : ℝ) / (U : ℝ) * (3 * Real.sqrt (M₂ * M₃) * Real.sqrt (U : ℝ))
                    = 6 * Real.sqrt (M₂ * M₃) * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) *
                        (1 / Real.sqrt (U : ℝ)) +
                      3 * Real.sqrt (M₂ * M₃) * (N : ℝ) * (Real.sqrt (U : ℝ) / (U : ℝ)) := by ring
                  _ = 6 * Real.sqrt (M₂ * M₃) * (N : ℝ) * (1 / Real.sqrt (U : ℝ)) +
                      3 * Real.sqrt (M₂ * M₃) * (N : ℝ) * (1 / Real.sqrt (U : ℝ)) := by rw [h1, h2]
                  _ = 9 * (Real.sqrt (M₂ * M₃) * (N : ℝ)) * (1 / Real.sqrt (U : ℝ)) := by ring
            _ ≤ 9 * B * (2 / Real.sqrt t) := mul_le_mul_of_nonneg_left hinv_sqU (by positivity)
            _ = 18 * (B / Real.sqrt t) := by ring
            _ = 18 * (A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3)) := by rw [hB_div_sqrt_t]
        exact (abs_add_le _ _).trans (by linarith)
  refine hAB_bound.trans ?_
  have h5_cube : (5 : ℝ) ^ ((1 : ℝ) / 3) ≤ 2 := by
    have h1 : ((5 : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) ≤ (2 : ℝ) ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    by_contra hlt; push Not at hlt
    have : (2 : ℝ) ^ (3 : ℕ) < ((5 : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) := by
      gcongr
    linarith
  have hA_rpow : A ^ ((1 : ℝ) / 3) ≤ M₁ ^ ((1 : ℝ) / 3) * (2 * (N : ℝ) ^ ((1 : ℝ) / 30)) := by
    dsimp [A]
    rw [Real.mul_rpow (by linarith) (by linarith [Real.log_nonneg hN_ge1])]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by linarith) _)
    calc (Real.log (N : ℝ) + 1) ^ ((1 : ℝ) / 3)
        ≤ (5 * (N : ℝ) ^ ((1 : ℝ) / 10)) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (by linarith [Real.log_nonneg hN_ge1])
            (log_add_one_le_5_rpow hN_ge1) (by norm_num)
      _ = (5 : ℝ) ^ ((1 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 30) := by
          rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hN_pos.le _),
            ← Real.rpow_mul hN_pos.le]; congr 2; norm_num
      _ ≤ 2 * (N : ℝ) ^ ((1 : ℝ) / 30) :=
          mul_le_mul_of_nonneg_right h5_cube (Real.rpow_nonneg hN_pos.le _)
  have hB_rpow : B ^ ((2 : ℝ) / 3) = (M₂ * M₃) ^ ((1 : ℝ) / 3) * (N : ℝ) ^ ((2 : ℝ) / 3) := by
    dsimp [B]
    rw [Real.mul_rpow (Real.sqrt_nonneg _) hN_pos.le, Real.sqrt_eq_rpow,
      ← Real.rpow_mul (by positivity)]
    congr 2; norm_num
  have hM_comb : M₁ ^ ((1 : ℝ) / 3) * (M₂ * M₃) ^ ((1 : ℝ) / 3) =
      (M₁ * M₂ * M₃) ^ ((1 : ℝ) / 3) := by
    rw [← Real.mul_rpow (by linarith) (by positivity), mul_assoc]
  have hN_comb : (N : ℝ) ^ ((1 : ℝ) / 30) * (N : ℝ) ^ ((2 : ℝ) / 3) = (N : ℝ) ^ ((7 : ℝ) / 10) := by
    rw [← Real.rpow_add hN_pos]; congr 1; norm_num
  calc 19 * A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3)
      ≤ 19 * (M₁ ^ ((1 : ℝ) / 3) * (2 * (N : ℝ) ^ ((1 : ℝ) / 30))) *
          ((M₂ * M₃) ^ ((1 : ℝ) / 3) * (N : ℝ) ^ ((2 : ℝ) / 3)) := by
        rw [hB_rpow]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA_rpow (by norm_num))
          (by positivity)
    _ = 38 * (M₁ ^ ((1 : ℝ) / 3) * (M₂ * M₃) ^ ((1 : ℝ) / 3)) *
          ((N : ℝ) ^ ((1 : ℝ) / 30) * (N : ℝ) ^ ((2 : ℝ) / 3)) := by ring
    _ = 38 * (M₁ * M₂ * M₃) ^ ((1 : ℝ) / 3) * (N : ℝ) ^ ((7 : ℝ) / 10) := by
        rw [hM_comb, hN_comb]

/- Product limit for L-series of double and triple convolutions -/

private lemma tendsto_Lpartial_dconv2 {χ₂ χ₃ : ℕ → ℝ} {M₂ M₃ s : ℝ}
    (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃)
    (hχ₂ : ∀ a b : ℕ, |∑ n ∈ Icc a b, χ₂ n| ≤ M₂)
    (hχ₃ : ∀ a b : ℕ, |∑ n ∈ Icc a b, χ₃ n| ≤ M₃)
    (hχ₂1 : ∀ n, |χ₂ n| ≤ 1) (hχ₃1 : ∀ n, |χ₃ n| ≤ 1)
    (hs1 : (49 : ℝ) / 50 ≤ s) (hs2 : s ≤ 1) :
    Tendsto (fun N => Lpartial (dconv χ₂ χ₃) N s) atTop (nhds (Lval χ₂ s * Lval χ₃ s)) := by
  have hs_pos : 0 < s := by linarith
  have hlim_sqrt : Tendsto Nat.sqrt atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b ^ 2, fun n hn => ?_⟩
    exact Nat.le_sqrt.mpr (by simpa [sq] using hn)
  have hmain : Tendsto (fun N => Lpartial χ₃ (Nat.sqrt N) s * Lval χ₂ s) atTop
      (nhds (Lval χ₃ s * Lval χ₂ s)) :=
    ((tendsto_Lval hM₃ hχ₃ hs_pos).comp hlim_sqrt).mul_const (Lval χ₂ s)
  have hdiff : Tendsto (fun N => Lpartial (dconv χ₂ χ₃) N s - Lpartial χ₃ (Nat.sqrt N) s * Lval χ₂ s)
      atTop (nhds 0) := by
    have h0 : Tendsto (fun N : ℕ =>
        M₂ * (N : ℝ) ^ (-(12 : ℝ) / 25) + 10 * M₃ * (N : ℝ) ^ (-(37 : ℝ) / 100)) atTop (nhds 0) := by
      have h1 : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) ^ (-(12 : ℝ) / 25)) atTop (nhds 0) := by
        simpa [neg_div] using rpow_neg_tendsto_zero (by norm_num : (0 : ℝ) < (12 : ℝ) / 25)
      have h1' : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(12 : ℝ) / 25)) atTop (nhds 0) := by
        have := h1.comp (tendsto_sub_atTop_nat 1)
        refine this.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop 1] with N hN
        simp only [Function.comp_apply, Nat.sub_add_cancel hN]
      have h2 : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) ^ (-(37 : ℝ) / 100)) atTop (nhds 0) := by
        simpa [neg_div] using rpow_neg_tendsto_zero (by norm_num : (0 : ℝ) < (37 : ℝ) / 100)
      have h2' : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(37 : ℝ) / 100)) atTop (nhds 0) := by
        have := h2.comp (tendsto_sub_atTop_nat 1)
        refine this.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop 1] with N hN
        simp only [Function.comp_apply, Nat.sub_add_cancel hN]
      simpa using (h1'.const_mul M₂).add (h2'.const_mul (10 * M₃))
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [Filter.eventually_ge_atTop 4] with N hN
    rw [Real.norm_eq_abs]
    set U : ℕ := Nat.sqrt N
    have hU1 : 1 ≤ U := Nat.le_sqrt.mpr (by omega)
    have hUN : U ≤ N := Nat.sqrt_le_self N
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hU_le_sq : (U : ℝ) ≤ Real.sqrt (N : ℝ) := by
      rw [Real.le_sqrt (by positivity) hN_pos.le, sq]; exact_mod_cast Nat.sqrt_le N
    have hsq_lt_U1 : Real.sqrt (N : ℝ) < ((U + 1 : ℕ) : ℝ) := by
      rw [Real.sqrt_lt' (by positivity), sq]
      exact_mod_cast Nat.lt_succ_sqrt N
    have hNU_le : ((N / U : ℕ) : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
      have hU_pos : (0 : ℝ) < (U : ℝ) := by exact_mod_cast (by omega : 0 < U)
      have hsq2U : Real.sqrt (N : ℝ) ≤ 2 * (U : ℝ) := by
        have : (1 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU1
        push_cast at hsq_lt_U1; linarith
      calc ((N / U : ℕ) : ℝ) ≤ (N : ℝ) / (U : ℝ) := by
            rw [le_div_iff₀ hU_pos]; exact_mod_cast Nat.div_mul_le_self N U
        _ ≤ 2 * Real.sqrt (N : ℝ) := by
            rw [div_le_iff₀ hU_pos]
            calc (N : ℝ) = Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) := (Real.mul_self_sqrt hN_pos.le).symm
              _ ≤ Real.sqrt (N : ℝ) * (2 * (U : ℝ)) :=
                  mul_le_mul_of_nonneg_left hsq2U (Real.sqrt_nonneg _)
              _ = 2 * Real.sqrt (N : ℝ) * (U : ℝ) := by ring
    have hw_mul : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        ((a * b : ℕ) : ℝ) ^ (-s) = (a : ℝ) ^ (-s) * (b : ℝ) ^ (-s) := by
      intro a b _ _; push_cast; exact Real.mul_rpow (by positivity) (by positivity)
    have hhyp := dirichlet_hyperbola χ₂ χ₃ (fun n => (n : ℝ) ^ (-s)) hU1 hUN hw_mul
    have hrew : Lpartial (dconv χ₂ χ₃) N s - Lpartial χ₃ U s * Lval χ₂ s =
        (∑ d ∈ Icc 1 U, χ₃ d * (d : ℝ) ^ (-s) * (Lpartial χ₂ (N / d) s - Lval χ₂ s)) +
        (∑ k ∈ Icc 1 (N / U), χ₂ k * (k : ℝ) ^ (-s) *
          ∑ d ∈ Icc (U + 1) (N / k), χ₃ d * (d : ℝ) ^ (-s)) := by
      unfold Lpartial at hhyp ⊢
      rw [hhyp, Finset.sum_mul, add_sub_right_comm, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun d _ => by ring
    rw [hrew]
    have hb1 : |∑ d ∈ Icc 1 U, χ₃ d * (d : ℝ) ^ (-s) * (Lpartial χ₂ (N / d) s - Lval χ₂ s)| ≤
        M₂ * (N : ℝ) ^ (-(12 : ℝ) / 25) := by
      calc |∑ d ∈ Icc 1 U, χ₃ d * (d : ℝ) ^ (-s) * (Lpartial χ₂ (N / d) s - Lval χ₂ s)|
          ≤ ∑ d ∈ Icc 1 U, |χ₃ d * (d : ℝ) ^ (-s) * (Lpartial χ₂ (N / d) s - Lval χ₂ s)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ Icc 1 U, M₂ * (N : ℝ) ^ (-s) := by
            refine Finset.sum_le_sum fun d hd => ?_
            simp only [Finset.mem_Icc] at hd
            have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
            have htail := abs_Lval_sub_partial_le hM₂ hχ₂ hs_pos (N / d)
            rw [abs_sub_comm] at htail
            have hdiv_lt : (N : ℝ) / (d : ℝ) < ((N / d + 1 : ℕ) : ℝ) := by
              rw [div_lt_iff₀ hd_pos]
              have hmod := Nat.div_add_mod N d
              have hltm := Nat.mod_lt N (by omega : 0 < d)
              exact_mod_cast (by nlinarith : N < (N / d + 1) * d)
            have hpow_le : ((N / d + 1 : ℕ) : ℝ) ^ (-s) ≤ ((N : ℝ) / (d : ℝ)) ^ (-s) :=
              Real.rpow_le_rpow_of_nonpos (div_pos hN_pos hd_pos) hdiv_lt.le (by linarith)
            have hdiv_pow : ((N : ℝ) / (d : ℝ)) ^ (-s) = (N : ℝ) ^ (-s) * (d : ℝ) ^ s := by
              rw [Real.div_rpow hN_pos.le hd_pos.le, div_eq_mul_inv,
                ← Real.rpow_neg hd_pos.le, neg_neg]
            rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hd_pos.le _)]
            calc |χ₃ d| * (d : ℝ) ^ (-s) * |Lpartial χ₂ (N / d) s - Lval χ₂ s|
                ≤ 1 * (d : ℝ) ^ (-s) * (M₂ * ((N : ℝ) / (d : ℝ)) ^ (-s)) :=
                  mul_le_mul (mul_le_mul_of_nonneg_right (hχ₃1 d) (Real.rpow_nonneg hd_pos.le _))
                    (htail.trans (mul_le_mul_of_nonneg_left hpow_le hM₂))
                    (abs_nonneg _) (mul_nonneg zero_le_one (Real.rpow_nonneg hd_pos.le _))
              _ = M₂ * (N : ℝ) ^ (-s) * ((d : ℝ) ^ (-s) * (d : ℝ) ^ s) := by rw [hdiv_pow]; ring
              _ = M₂ * (N : ℝ) ^ (-s) := by
                  rw [← Real.rpow_add hd_pos, neg_add_cancel, Real.rpow_zero, mul_one]
        _ = (U : ℝ) * (M₂ * (N : ℝ) ^ (-s)) := by simp
        _ ≤ Real.sqrt (N : ℝ) * (M₂ * (N : ℝ) ^ (-s)) :=
            mul_le_mul_of_nonneg_right hU_le_sq (by positivity)
        _ = M₂ * (N : ℝ) ^ ((1 : ℝ) / 2 - s) := by
            rw [Real.sqrt_eq_rpow]
            calc (N : ℝ) ^ ((1 : ℝ) / 2) * (M₂ * (N : ℝ) ^ (-s))
                = M₂ * ((N : ℝ) ^ ((1 : ℝ) / 2) * (N : ℝ) ^ (-s)) := by ring
              _ = M₂ * (N : ℝ) ^ ((1 : ℝ) / 2 - s) := by
                  rw [← Real.rpow_add hN_pos, sub_eq_add_neg]
        _ ≤ M₂ * (N : ℝ) ^ (-(12 : ℝ) / 25) := by
            refine mul_le_mul_of_nonneg_left ?_ hM₂
            exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) (by linarith)
    have hb2 : |∑ k ∈ Icc 1 (N / U), χ₂ k * (k : ℝ) ^ (-s) *
          ∑ d ∈ Icc (U + 1) (N / k), χ₃ d * (d : ℝ) ^ (-s)| ≤
        10 * M₃ * (N : ℝ) ^ (-(37 : ℝ) / 100) := by
      have hNU1 : 1 ≤ N / U := Nat.div_pos hUN hU1
      have hinner : ∀ k ∈ Icc 1 (N / U),
          |∑ d ∈ Icc (U + 1) (N / k), χ₃ d * (d : ℝ) ^ (-s)| ≤ M₃ * (N : ℝ) ^ (-s / 2) := by
        intro k _
        by_cases hk : U + 1 ≤ N / k
        · have hb := abel_antitone_bound χ₃ (fun d => (d : ℝ) ^ (-s)) (by omega) hk hM₃
            (fun d _ => hχ₃ (U + 1) d)
            (fun d _ => Real.rpow_nonneg (by positivity) _)
            (fun d hd => Real.rpow_le_rpow_of_nonpos
              (by exact_mod_cast (by simp only [Finset.mem_Icc] at hd; omega : 0 < d))
              (by exact_mod_cast Nat.le_succ d) (by linarith))
          have hpow : ((U + 1 : ℕ) : ℝ) ^ (-s) ≤ (N : ℝ) ^ (-s / 2) := by
            calc ((U + 1 : ℕ) : ℝ) ^ (-s) ≤ (Real.sqrt (N : ℝ)) ^ (-s) :=
                  Real.rpow_le_rpow_of_nonpos (Real.sqrt_pos.mpr hN_pos) hsq_lt_U1.le (by linarith)
              _ = (N : ℝ) ^ (-s / 2) := by
                  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN_pos.le]; congr 1; ring
          exact hb.trans (mul_le_mul_of_nonneg_left hpow hM₃)
        · have hemp : Icc (U + 1) (N / k) = ∅ := Finset.Icc_eq_empty (by omega)
          rw [hemp, Finset.sum_empty, abs_zero]
          exact mul_nonneg hM₃ (Real.rpow_nonneg hN_pos.le _)
      have h2rpow : (2 : ℝ) ^ ((3 : ℝ) / 25) ≤ 2 := by
        calc (2 : ℝ) ^ ((3 : ℝ) / 25) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      calc |∑ k ∈ Icc 1 (N / U), χ₂ k * (k : ℝ) ^ (-s) *
              ∑ d ∈ Icc (U + 1) (N / k), χ₃ d * (d : ℝ) ^ (-s)|
          ≤ ∑ k ∈ Icc 1 (N / U), |χ₂ k * (k : ℝ) ^ (-s) *
              ∑ d ∈ Icc (U + 1) (N / k), χ₃ d * (d : ℝ) ^ (-s)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Icc 1 (N / U), (k : ℝ) ^ (-s) * (M₃ * (N : ℝ) ^ (-s / 2)) := by
            refine Finset.sum_le_sum fun k hk => ?_
            rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
            calc |χ₂ k| * (k : ℝ) ^ (-s) * |∑ d ∈ Icc (U + 1) (N / k), χ₃ d * (d : ℝ) ^ (-s)|
                ≤ 1 * (k : ℝ) ^ (-s) * (M₃ * (N : ℝ) ^ (-s / 2)) :=
                  mul_le_mul (mul_le_mul_of_nonneg_right (hχ₂1 k)
                    (Real.rpow_nonneg (by positivity) _)) (hinner k hk) (abs_nonneg _)
                    (mul_nonneg zero_le_one (Real.rpow_nonneg (by positivity) _))
              _ = _ := by ring
        _ = (∑ k ∈ Icc 1 (N / U), (k : ℝ) ^ (-s)) * (M₃ * (N : ℝ) ^ (-s / 2)) := by
            rw [← Finset.sum_mul]
        _ ≤ (((N / U : ℕ) : ℝ) ^ (1 - s) * (Real.log ((N / U : ℕ) : ℝ) + 1)) *
              (M₃ * (N : ℝ) ^ (-s / 2)) :=
            mul_le_mul_of_nonneg_right (sum_rpow_neg_le hs2 hNU1) (by positivity)
        _ ≤ (((N / U : ℕ) : ℝ) ^ ((1 : ℝ) / 50) * (5 * ((N / U : ℕ) : ℝ) ^ ((1 : ℝ) / 10))) *
              (M₃ * (N : ℝ) ^ (-s / 2)) := by
            have hNU_ge1 : (1 : ℝ) ≤ ((N / U : ℕ) : ℝ) := by exact_mod_cast hNU1
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul
              (Real.rpow_le_rpow_of_exponent_le hNU_ge1 (by linarith))
              (log_add_one_le_5_rpow hNU_ge1)
              (by linarith [Real.log_nonneg hNU_ge1])
              (Real.rpow_nonneg (by linarith) _)
        _ = 5 * M₃ * (((N / U : ℕ) : ℝ) ^ ((3 : ℝ) / 25) * (N : ℝ) ^ (-s / 2)) := by
            have hcomb : ((N / U : ℕ) : ℝ) ^ ((1 : ℝ) / 50) * ((N / U : ℕ) : ℝ) ^ ((1 : ℝ) / 10) =
                ((N / U : ℕ) : ℝ) ^ ((3 : ℝ) / 25) := by
              rw [← Real.rpow_add (by exact_mod_cast (by omega : 0 < N / U))]; congr 1; norm_num
            calc ((N / U : ℕ) : ℝ) ^ ((1 : ℝ) / 50) * (5 * ((N / U : ℕ) : ℝ) ^ ((1 : ℝ) / 10)) *
                  (M₃ * (N : ℝ) ^ (-s / 2))
                = 5 * M₃ * (((N / U : ℕ) : ℝ) ^ ((1 : ℝ) / 50) * ((N / U : ℕ) : ℝ) ^ ((1 : ℝ) / 10) *
                    (N : ℝ) ^ (-s / 2)) := by ring
              _ = _ := by rw [hcomb]
        _ ≤ 5 * M₃ * ((2 * Real.sqrt (N : ℝ)) ^ ((3 : ℝ) / 25) * (N : ℝ) ^ (-s / 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow (by positivity) hNU_le (by norm_num))
              (Real.rpow_nonneg hN_pos.le _)
        _ ≤ 5 * M₃ * (2 * (N : ℝ) ^ ((3 : ℝ) / 50) * (N : ℝ) ^ (-s / 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
              ← Real.rpow_mul hN_pos.le]
            have hexp : (1 : ℝ) / 2 * ((3 : ℝ) / 25) = (3 : ℝ) / 50 := by norm_num
            rw [hexp]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right h2rpow (Real.rpow_nonneg hN_pos.le _))
              (Real.rpow_nonneg hN_pos.le _)
        _ = 10 * M₃ * (N : ℝ) ^ ((3 : ℝ) / 50 - s / 2) := by
            calc 5 * M₃ * (2 * (N : ℝ) ^ ((3 : ℝ) / 50) * (N : ℝ) ^ (-s / 2))
                = 10 * M₃ * ((N : ℝ) ^ ((3 : ℝ) / 50) * (N : ℝ) ^ (-s / 2)) := by ring
              _ = 10 * M₃ * (N : ℝ) ^ ((3 : ℝ) / 50 - s / 2) := by
                  rw [← Real.rpow_add hN_pos]; congr 2; ring
        _ ≤ 10 * M₃ * (N : ℝ) ^ (-(37 : ℝ) / 100) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) (by linarith)
    exact (abs_add_le _ _).trans (by linarith)
  have hsum := hdiff.add hmain
  simpa [mul_comm] using hsum

private lemma tendsto_Lpartial_dconv3 {χ₁ χ₂ χ₃ : ℕ → ℝ} {M₁ M₂ M₃ s : ℝ}
    (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (hM₃ : 1 ≤ M₃)
    (hχ₁ : ∀ a b : ℕ, |∑ n ∈ Icc a b, χ₁ n| ≤ M₁)
    (hχ₂ : ∀ a b : ℕ, |∑ n ∈ Icc a b, χ₂ n| ≤ M₂)
    (hχ₃ : ∀ a b : ℕ, |∑ n ∈ Icc a b, χ₃ n| ≤ M₃)
    (hχ₁1 : ∀ n, |χ₁ n| ≤ 1) (hχ₂1 : ∀ n, |χ₂ n| ≤ 1) (hχ₃1 : ∀ n, |χ₃ n| ≤ 1)
    (hs1 : (49 : ℝ) / 50 ≤ s) (hs2 : s ≤ 1) :
    Tendsto (fun N => Lpartial (dconv χ₁ (dconv χ₂ χ₃)) N s) atTop
      (nhds (Lval χ₁ s * Lval χ₂ s * Lval χ₃ s)) := by
  set h := dconv χ₂ χ₃
  set g := dconv χ₁ h
  have hs_pos : 0 < s := by linarith
  have hlim_sqrt : Tendsto Nat.sqrt atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b ^ 2, fun n hn => Nat.le_sqrt.mpr (by simpa [sq] using hn)⟩
  have hmain : Tendsto (fun N => Lpartial h (Nat.sqrt N) s * Lval χ₁ s) atTop
      (nhds (Lval χ₂ s * Lval χ₃ s * Lval χ₁ s)) :=
    ((tendsto_Lpartial_dconv2 (by linarith) (by linarith) hχ₂ hχ₃ hχ₂1 hχ₃1 hs1 hs2).comp
      hlim_sqrt).mul_const (Lval χ₁ s)
  set C₂ : ℝ := 3 * Real.sqrt (M₂ * M₃)
  have hC₂_nn : 0 ≤ C₂ := by positivity
  have hH_710 : ∀ n : ℕ, 1 ≤ n → |∑ d ∈ Icc 1 n, h d| ≤ C₂ * (n : ℝ) ^ ((7 : ℝ) / 10) := by
    intro n hn
    have hb := partial_sum_dconv2_le hM₂ hM₃ hχ₂ hχ₃ hχ₂1 hχ₃1 hn
    have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    calc |∑ d ∈ Icc 1 n, h d| ≤ 3 * Real.sqrt ((n : ℝ) * M₂ * M₃) := hb
      _ = C₂ * (n : ℝ) ^ ((1 : ℝ) / 2) := by
          dsimp [C₂]
          have : (n : ℝ) * M₂ * M₃ = (M₂ * M₃) * (n : ℝ) := by ring
          rw [this, Real.sqrt_mul (mul_nonneg (by linarith) (by linarith)),
            Real.sqrt_eq_rpow (n : ℝ)]; ring
      _ ≤ C₂ * (n : ℝ) ^ ((7 : ℝ) / 10) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn_ge1 (by norm_num)) hC₂_nn
  have hdiff : Tendsto (fun N => Lpartial g N s - Lpartial h (Nat.sqrt N) s * Lval χ₁ s)
      atTop (nhds 0) := by
    have h0 : Tendsto (fun N : ℕ =>
        5 * M₁ * (N : ℝ) ^ (-(43 : ℝ) / 100) + 120 * C₂ * (N : ℝ) ^ (-(2 : ℝ) / 25))
        atTop (nhds 0) := by
      have h1 : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) ^ (-(43 : ℝ) / 100)) atTop (nhds 0) := by
        simpa [neg_div] using rpow_neg_tendsto_zero (by norm_num : (0 : ℝ) < (43 : ℝ) / 100)
      have h1' : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(43 : ℝ) / 100)) atTop (nhds 0) := by
        refine (h1.comp (tendsto_sub_atTop_nat 1)).congr' ?_
        filter_upwards [Filter.eventually_ge_atTop 1] with N hN
        simp only [Function.comp_apply, Nat.sub_add_cancel hN]
      have h2 : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) ^ (-(2 : ℝ) / 25)) atTop (nhds 0) := by
        simpa [neg_div] using rpow_neg_tendsto_zero (by norm_num : (0 : ℝ) < (2 : ℝ) / 25)
      have h2' : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(2 : ℝ) / 25)) atTop (nhds 0) := by
        refine (h2.comp (tendsto_sub_atTop_nat 1)).congr' ?_
        filter_upwards [Filter.eventually_ge_atTop 1] with N hN
        simp only [Function.comp_apply, Nat.sub_add_cancel hN]
      simpa using (h1'.const_mul (5 * M₁)).add (h2'.const_mul (120 * C₂))
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [Filter.eventually_ge_atTop 4] with N hN
    rw [Real.norm_eq_abs]
    set U : ℕ := Nat.sqrt N
    have hU1 : 1 ≤ U := Nat.le_sqrt.mpr (by omega)
    have hUN : U ≤ N := Nat.sqrt_le_self N
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hU_pos : (0 : ℝ) < (U : ℝ) := by exact_mod_cast (by omega : 0 < U)
    have hU_le_sq : (U : ℝ) ≤ Real.sqrt (N : ℝ) := by
      rw [Real.le_sqrt (by positivity) hN_pos.le, sq]; exact_mod_cast Nat.sqrt_le N
    have hsq_le_2U : Real.sqrt (N : ℝ) ≤ 2 * (U : ℝ) := by
      have hlt : Real.sqrt (N : ℝ) < ((U + 1 : ℕ) : ℝ) := by
        rw [Real.sqrt_lt' (by positivity), sq]; exact_mod_cast Nat.lt_succ_sqrt N
      have : (1 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU1
      push_cast at hlt; linarith
    have hNU_le : ((N / U : ℕ) : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
      calc ((N / U : ℕ) : ℝ) ≤ (N : ℝ) / (U : ℝ) := by
            rw [le_div_iff₀ hU_pos]; exact_mod_cast Nat.div_mul_le_self N U
        _ ≤ 2 * Real.sqrt (N : ℝ) := by
            rw [div_le_iff₀ hU_pos]
            calc (N : ℝ) = Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) := (Real.mul_self_sqrt hN_pos.le).symm
              _ ≤ Real.sqrt (N : ℝ) * (2 * (U : ℝ)) :=
                  mul_le_mul_of_nonneg_left hsq_le_2U (Real.sqrt_nonneg _)
              _ = 2 * Real.sqrt (N : ℝ) * (U : ℝ) := by ring
    have hw_mul : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        ((a * b : ℕ) : ℝ) ^ (-s) = (a : ℝ) ^ (-s) * (b : ℝ) ^ (-s) := by
      intro a b _ _; push_cast; exact Real.mul_rpow (by positivity) (by positivity)
    have hhyp := dirichlet_hyperbola χ₁ h (fun n => (n : ℝ) ^ (-s)) hU1 hUN hw_mul
    have hrew : Lpartial g N s - Lpartial h U s * Lval χ₁ s =
        (∑ d ∈ Icc 1 U, h d * (d : ℝ) ^ (-s) * (Lpartial χ₁ (N / d) s - Lval χ₁ s)) +
        (∑ k ∈ Icc 1 (N / U), χ₁ k * (k : ℝ) ^ (-s) *
          ∑ d ∈ Icc (U + 1) (N / k), h d * (d : ℝ) ^ (-s)) := by
      unfold Lpartial at hhyp ⊢
      rw [hhyp, Finset.sum_mul, add_sub_right_comm, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun d _ => by ring
    rw [hrew]
    have hb1 : |∑ d ∈ Icc 1 U, h d * (d : ℝ) ^ (-s) * (Lpartial χ₁ (N / d) s - Lval χ₁ s)| ≤
        5 * M₁ * (N : ℝ) ^ (-(43 : ℝ) / 100) := by
      calc |∑ d ∈ Icc 1 U, h d * (d : ℝ) ^ (-s) * (Lpartial χ₁ (N / d) s - Lval χ₁ s)|
          ≤ ∑ d ∈ Icc 1 U, |h d * (d : ℝ) ^ (-s) * (Lpartial χ₁ (N / d) s - Lval χ₁ s)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ Icc 1 U, dconv (fun _ => 1) (fun _ => 1) d * (M₁ * (N : ℝ) ^ (-s)) := by
            refine Finset.sum_le_sum fun d hd => ?_
            simp only [Finset.mem_Icc] at hd
            have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
            have htail := abs_Lval_sub_partial_le (by linarith) hχ₁ hs_pos (N / d)
            rw [abs_sub_comm] at htail
            have hdiv_lt : (N : ℝ) / (d : ℝ) < ((N / d + 1 : ℕ) : ℝ) := by
              rw [div_lt_iff₀ hd_pos]
              have hmod := Nat.div_add_mod N d
              have hltm := Nat.mod_lt N (by omega : 0 < d)
              exact_mod_cast (by nlinarith : N < (N / d + 1) * d)
            have hpow_le : ((N / d + 1 : ℕ) : ℝ) ^ (-s) ≤ ((N : ℝ) / (d : ℝ)) ^ (-s) :=
              Real.rpow_le_rpow_of_nonpos (div_pos hN_pos hd_pos) hdiv_lt.le (by linarith)
            have hdiv_pow : ((N : ℝ) / (d : ℝ)) ^ (-s) = (N : ℝ) ^ (-s) * (d : ℝ) ^ s := by
              rw [Real.div_rpow hN_pos.le hd_pos.le, div_eq_mul_inv,
                ← Real.rpow_neg hd_pos.le, neg_neg]
            have hhd : |h d| ≤ dconv (fun _ => 1) (fun _ => 1) d :=
              abs_dconv_le (fun n _ => hχ₂1 n) (fun n _ => hχ₃1 n) hd.1
            have htau_nn : 0 ≤ dconv (fun _ => 1) (fun _ => 1) d := (abs_nonneg _).trans hhd
            rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hd_pos.le _)]
            calc |h d| * (d : ℝ) ^ (-s) * |Lpartial χ₁ (N / d) s - Lval χ₁ s|
                ≤ dconv (fun _ => 1) (fun _ => 1) d * (d : ℝ) ^ (-s) *
                    (M₁ * ((N : ℝ) / (d : ℝ)) ^ (-s)) :=
                  mul_le_mul (mul_le_mul_of_nonneg_right hhd (Real.rpow_nonneg hd_pos.le _))
                    (htail.trans (mul_le_mul_of_nonneg_left hpow_le (by linarith)))
                    (abs_nonneg _) (mul_nonneg htau_nn (Real.rpow_nonneg hd_pos.le _))
              _ = dconv (fun _ => 1) (fun _ => 1) d * (M₁ * (N : ℝ) ^ (-s)) *
                    ((d : ℝ) ^ (-s) * (d : ℝ) ^ s) := by rw [hdiv_pow]; ring
              _ = dconv (fun _ => 1) (fun _ => 1) d * (M₁ * (N : ℝ) ^ (-s)) := by
                  rw [← Real.rpow_add hd_pos, neg_add_cancel, Real.rpow_zero, mul_one]
        _ = (∑ d ∈ Icc 1 U, dconv (fun _ => 1) (fun _ => 1) d) * (M₁ * (N : ℝ) ^ (-s)) := by
            rw [← Finset.sum_mul]
        _ ≤ ((U : ℝ) * (Real.log (U : ℝ) + 1)) * (M₁ * (N : ℝ) ^ (-s)) :=
            mul_le_mul_of_nonneg_right (sum_tau_le hU1) (by positivity)
        _ ≤ ((U : ℝ) * (5 * (U : ℝ) ^ ((1 : ℝ) / 10))) * (M₁ * (N : ℝ) ^ (-s)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (log_add_one_le_5_rpow (by exact_mod_cast hU1)) hU_pos.le)
              (by positivity)
        _ = 5 * M₁ * ((U : ℝ) ^ ((11 : ℝ) / 10) * (N : ℝ) ^ (-s)) := by
            have hU11 : (U : ℝ) * (U : ℝ) ^ ((1 : ℝ) / 10) = (U : ℝ) ^ ((11 : ℝ) / 10) := by
              conv_lhs => arg 1; rw [← Real.rpow_one (U : ℝ)]
              rw [← Real.rpow_add hU_pos]; congr 1; norm_num
            calc (U : ℝ) * (5 * (U : ℝ) ^ ((1 : ℝ) / 10)) * (M₁ * (N : ℝ) ^ (-s))
                = 5 * M₁ * ((U : ℝ) * (U : ℝ) ^ ((1 : ℝ) / 10) * (N : ℝ) ^ (-s)) := by ring
              _ = _ := by rw [hU11]
        _ ≤ 5 * M₁ * ((Real.sqrt (N : ℝ)) ^ ((11 : ℝ) / 10) * (N : ℝ) ^ (-s)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow hU_pos.le hU_le_sq (by norm_num)) (Real.rpow_nonneg hN_pos.le _)
        _ = 5 * M₁ * (N : ℝ) ^ ((11 : ℝ) / 20 - s) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN_pos.le, ← Real.rpow_add hN_pos]
            congr 2; ring
        _ ≤ 5 * M₁ * (N : ℝ) ^ (-(43 : ℝ) / 100) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) (by linarith)
    have hb2 : |∑ k ∈ Icc 1 (N / U), χ₁ k * (k : ℝ) ^ (-s) *
          ∑ d ∈ Icc (U + 1) (N / k), h d * (d : ℝ) ^ (-s)| ≤
        120 * C₂ * (N : ℝ) ^ (-(2 : ℝ) / 25) := by
      have hNU1 : 1 ≤ N / U := Nat.div_pos hUN hU1
      have hU_pow : (U : ℝ) ^ ((7 : ℝ) / 10 - s) ≤ 2 * (N : ℝ) ^ (-(7 : ℝ) / 50) := by
        have h1 : (U : ℝ) ^ ((7 : ℝ) / 10 - s) ≤ (U : ℝ) ^ (-(7 : ℝ) / 25) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hU1) (by linarith)
        have h2 : (U : ℝ) ^ (-(7 : ℝ) / 25) ≤ (Real.sqrt (N : ℝ) / 2) ^ (-(7 : ℝ) / 25) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
        have h3 : (Real.sqrt (N : ℝ) / 2) ^ (-(7 : ℝ) / 25) =
            (2 : ℝ) ^ ((7 : ℝ) / 25) * (N : ℝ) ^ (-(7 : ℝ) / 50) := by
          rw [Real.div_rpow (Real.sqrt_nonneg _) (by norm_num), div_eq_mul_inv,
            ← Real.rpow_neg (by norm_num), Real.sqrt_eq_rpow,
            ← Real.rpow_mul hN_pos.le]
          have h2e : -(-(7 : ℝ) / 25) = (7 : ℝ) / 25 := by norm_num
          have hexp : (1 : ℝ) / 2 * (-(7 : ℝ) / 25) = -(7 : ℝ) / 50 := by norm_num
          rw [h2e, hexp]; ring
        have h2p : (2 : ℝ) ^ ((7 : ℝ) / 25) ≤ 2 := by
          calc (2 : ℝ) ^ ((7 : ℝ) / 25) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
        calc (U : ℝ) ^ ((7 : ℝ) / 10 - s) ≤ (2 : ℝ) ^ ((7 : ℝ) / 25) * (N : ℝ) ^ (-(7 : ℝ) / 50) := by
              rw [← h3]; exact h1.trans h2
          _ ≤ 2 * (N : ℝ) ^ (-(7 : ℝ) / 50) :=
              mul_le_mul_of_nonneg_right h2p (Real.rpow_nonneg hN_pos.le _)
      have hinner : ∀ k ∈ Icc 1 (N / U),
          |∑ d ∈ Icc (U + 1) (N / k), h d * (d : ℝ) ^ (-s)| ≤
            12 * C₂ * (N : ℝ) ^ (-(7 : ℝ) / 50) := by
        intro k _
        by_cases hk : U < N / k
        · have hb := abel_pow_tail_bound hC₂_nn hH_710 hs1 hU1 hk
          have hQ_le : ((N / k : ℕ) : ℝ) ^ ((7 : ℝ) / 10 - s) ≤ (U : ℝ) ^ ((7 : ℝ) / 10 - s) :=
            Real.rpow_le_rpow_of_nonpos hU_pos (by exact_mod_cast hk.le) (by linarith)
          calc |∑ d ∈ Icc (U + 1) (N / k), h d * (d : ℝ) ^ (-s)|
              ≤ C₂ * (6 * (U : ℝ) ^ ((7 : ℝ) / 10 - s)) := hb.trans (by
                exact mul_le_mul_of_nonneg_left (by linarith) hC₂_nn)
            _ ≤ C₂ * (6 * (2 * (N : ℝ) ^ (-(7 : ℝ) / 50))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU_pow (by norm_num)) hC₂_nn
            _ = 12 * C₂ * (N : ℝ) ^ (-(7 : ℝ) / 50) := by ring
        · have hemp : Icc (U + 1) (N / k) = ∅ := Finset.Icc_eq_empty (by omega)
          rw [hemp, Finset.sum_empty, abs_zero]; positivity
      have h2rpow : (2 : ℝ) ^ ((3 : ℝ) / 25) ≤ 2 := by
        calc (2 : ℝ) ^ ((3 : ℝ) / 25) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      calc |∑ k ∈ Icc 1 (N / U), χ₁ k * (k : ℝ) ^ (-s) *
              ∑ d ∈ Icc (U + 1) (N / k), h d * (d : ℝ) ^ (-s)|
          ≤ ∑ k ∈ Icc 1 (N / U), |χ₁ k * (k : ℝ) ^ (-s) *
              ∑ d ∈ Icc (U + 1) (N / k), h d * (d : ℝ) ^ (-s)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Icc 1 (N / U), (k : ℝ) ^ (-s) * (12 * C₂ * (N : ℝ) ^ (-(7 : ℝ) / 50)) := by
            refine Finset.sum_le_sum fun k hk => ?_
            rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
            calc |χ₁ k| * (k : ℝ) ^ (-s) * |∑ d ∈ Icc (U + 1) (N / k), h d * (d : ℝ) ^ (-s)|
                ≤ 1 * (k : ℝ) ^ (-s) * (12 * C₂ * (N : ℝ) ^ (-(7 : ℝ) / 50)) :=
                  mul_le_mul (mul_le_mul_of_nonneg_right (hχ₁1 k)
                    (Real.rpow_nonneg (by positivity) _)) (hinner k hk) (abs_nonneg _)
                    (mul_nonneg zero_le_one (Real.rpow_nonneg (by positivity) _))
              _ = _ := by ring
        _ = (∑ k ∈ Icc 1 (N / U), (k : ℝ) ^ (-s)) * (12 * C₂ * (N : ℝ) ^ (-(7 : ℝ) / 50)) := by
            rw [← Finset.sum_mul]
        _ ≤ (((N / U : ℕ) : ℝ) ^ (1 - s) * (Real.log ((N / U : ℕ) : ℝ) + 1)) *
              (12 * C₂ * (N : ℝ) ^ (-(7 : ℝ) / 50)) :=
            mul_le_mul_of_nonneg_right (sum_rpow_neg_le hs2 hNU1) (by positivity)
        _ ≤ (((N / U : ℕ) : ℝ) ^ ((1 : ℝ) / 50) * (5 * ((N / U : ℕ) : ℝ) ^ ((1 : ℝ) / 10))) *
              (12 * C₂ * (N : ℝ) ^ (-(7 : ℝ) / 50)) := by
            have hNU_ge1 : (1 : ℝ) ≤ ((N / U : ℕ) : ℝ) := by exact_mod_cast hNU1
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul
              (Real.rpow_le_rpow_of_exponent_le hNU_ge1 (by linarith))
              (log_add_one_le_5_rpow hNU_ge1)
              (by linarith [Real.log_nonneg hNU_ge1])
              (Real.rpow_nonneg (by linarith) _)
        _ = 60 * C₂ * (((N / U : ℕ) : ℝ) ^ ((3 : ℝ) / 25) * (N : ℝ) ^ (-(7 : ℝ) / 50)) := by
            have hcomb : ((N / U : ℕ) : ℝ) ^ ((1 : ℝ) / 50) * ((N / U : ℕ) : ℝ) ^ ((1 : ℝ) / 10) =
                ((N / U : ℕ) : ℝ) ^ ((3 : ℝ) / 25) := by
              rw [← Real.rpow_add (by exact_mod_cast (by omega : 0 < N / U))]; congr 1; norm_num
            calc ((N / U : ℕ) : ℝ) ^ ((1 : ℝ) / 50) * (5 * ((N / U : ℕ) : ℝ) ^ ((1 : ℝ) / 10)) *
                  (12 * C₂ * (N : ℝ) ^ (-(7 : ℝ) / 50))
                = 60 * C₂ * (((N / U : ℕ) : ℝ) ^ ((1 : ℝ) / 50) * ((N / U : ℕ) : ℝ) ^ ((1 : ℝ) / 10) *
                    (N : ℝ) ^ (-(7 : ℝ) / 50)) := by ring
              _ = _ := by rw [hcomb]
        _ ≤ 60 * C₂ * ((2 * Real.sqrt (N : ℝ)) ^ ((3 : ℝ) / 25) * (N : ℝ) ^ (-(7 : ℝ) / 50)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow (by positivity) hNU_le (by norm_num))
              (Real.rpow_nonneg hN_pos.le _)
        _ ≤ 60 * C₂ * (2 * (N : ℝ) ^ ((3 : ℝ) / 50) * (N : ℝ) ^ (-(7 : ℝ) / 50)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
              ← Real.rpow_mul hN_pos.le]
            have hexp : (1 : ℝ) / 2 * ((3 : ℝ) / 25) = (3 : ℝ) / 50 := by norm_num
            rw [hexp]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right h2rpow (Real.rpow_nonneg hN_pos.le _))
              (Real.rpow_nonneg hN_pos.le _)
        _ = 120 * C₂ * (N : ℝ) ^ (-(2 : ℝ) / 25) := by
            calc 60 * C₂ * (2 * (N : ℝ) ^ ((3 : ℝ) / 50) * (N : ℝ) ^ (-(7 : ℝ) / 50))
                = 120 * C₂ * ((N : ℝ) ^ ((3 : ℝ) / 50) * (N : ℝ) ^ (-(7 : ℝ) / 50)) := by ring
              _ = 120 * C₂ * (N : ℝ) ^ (-(2 : ℝ) / 25) := by
                  rw [← Real.rpow_add hN_pos]; congr 2; norm_num
    exact (abs_add_le _ _).trans (by linarith)
  have hsum := hdiff.add hmain
  have hmul : Lval χ₂ s * Lval χ₃ s * Lval χ₁ s = Lval χ₁ s * Lval χ₂ s * Lval χ₃ s := by ring
  rw [hmul] at hsum
  simpa using hsum

/- Uniform tail bound for h_s(t) = (X^(1-s)*t^(-1) - t^(-s)) / (1 - s) -/

private noncomputable def hsFun (X s t : ℝ) : ℝ :=
  (X ^ (1 - s) * t ^ (-(1 : ℝ)) - t ^ (-s)) / (1 - s)

private lemma hsFun_abs_le {X s t : ℝ} (hX : 0 < X) (ht : 0 < t)
    (_hs1 : (49 : ℝ) / 50 ≤ s) (hs2 : s < 1) :
    |hsFun X s t| ≤ t ^ (-s) * max ((X / t) ^ (1 - s)) 1 * |Real.log (X / t)| := by
  set u : ℝ := X / t
  have hu : 0 < u := div_pos hX ht
  set a : ℝ := 1 - s
  have ha : 0 < a := by linarith
  have hrew : hsFun X s t = t ^ (-s) * ((u ^ a - 1) / a) := by
    unfold hsFun
    have h1 : X ^ a * t ^ (-(1 : ℝ)) = t ^ (-s) * u ^ a := by
      dsimp [u, a]
      rw [Real.div_rpow hX.le ht.le, div_eq_mul_inv, ← Real.rpow_neg ht.le]
      calc X ^ (1 - s) * t ^ (-(1 : ℝ))
          = X ^ (1 - s) * (t ^ (-s) * t ^ (-(1 - s))) := by
            rw [← Real.rpow_add ht]; congr 2; ring
        _ = t ^ (-s) * (X ^ (1 - s) * t ^ (-(1 - s))) := by ring
    rw [h1]; ring
  rw [hrew, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le _)]
  have hmvt : |(u ^ a - 1) / a| ≤ max (u ^ a) 1 * |Real.log u| := by
    let φf : ℝ → ℝ := fun r => Real.exp (r * (a * Real.log u))
    have hderiv : ∀ r : ℝ, HasDerivAt φf (a * Real.log u * φf r) r := by
      intro r
      have h1 : HasDerivAt (fun x : ℝ => x * (a * Real.log u)) (a * Real.log u) r := by
        simpa using (hasDerivAt_id r).mul_const (a * Real.log u)
      have h2 := h1.exp
      have hval : Real.exp (r * (a * Real.log u)) * (a * Real.log u) = a * Real.log u * φf r := by
        dsimp [φf]; ring
      rw [← hval]; exact h2
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope φf (fun r => a * Real.log u * φf r)
      zero_lt_one (fun r _ => (hderiv r).continuousAt.continuousWithinAt) (fun r _ => hderiv r)
    have hφ0 : φf 0 = 1 := by simp [φf]
    have hφ1 : φf 1 = u ^ a := by
      dsimp [φf]; rw [one_mul, Real.rpow_def_of_pos hu]; congr 1; ring
    rw [hφ1, hφ0, sub_zero, div_one] at hslope
    have hdiv_eq : (u ^ a - 1) / a = Real.log u * φf c := by
      rw [← hslope]; field_simp [ha.ne']
    rw [hdiv_eq, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hφc_le : φf c ≤ max (u ^ a) 1 := by
      dsimp [φf]
      rcases le_or_gt 0 (a * Real.log u) with hnn | hneg
      · have : c * (a * Real.log u) ≤ 1 * (a * Real.log u) :=
          mul_le_mul_of_nonneg_right hc.2.le hnn
        have hle : Real.exp (c * (a * Real.log u)) ≤ u ^ a := by
          rw [← hφ1]; exact Real.exp_le_exp.mpr this
        exact hle.trans (le_max_left _ _)
      · have : c * (a * Real.log u) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc.1.le hneg.le
        have hle : Real.exp (c * (a * Real.log u)) ≤ 1 := by
          rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr this
        exact hle.trans (le_max_right _ _)
    calc |Real.log u| * φf c ≤ |Real.log u| * max (u ^ a) 1 :=
          mul_le_mul_of_nonneg_left hφc_le (abs_nonneg _)
      _ = max (u ^ a) 1 * |Real.log u| := mul_comm _ _
  calc t ^ (-s) * |(u ^ a - 1) / a|
      ≤ t ^ (-s) * (max (u ^ a) 1 * |Real.log u|) :=
        mul_le_mul_of_nonneg_left hmvt (Real.rpow_nonneg ht.le _)
    _ = t ^ (-s) * max (u ^ a) 1 * |Real.log u| := by ring

private lemma hasDerivAt_hsFun {X s t : ℝ} (ht : 0 < t) (hs2 : s < 1) :
    HasDerivAt (hsFun X s) (-(t ^ (-(1 : ℝ)) * hsFun X s t + t ^ (-s - 1))) t := by
  unfold hsFun
  have hd1 : HasDerivAt (fun x : ℝ => X ^ (1 - s) * x ^ (-(1 : ℝ)))
      (X ^ (1 - s) * (-(1 : ℝ) * t ^ (-(1 : ℝ) - 1))) t :=
    (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).const_mul _
  have hd2 : HasDerivAt (fun x : ℝ => x ^ (-s)) (-s * t ^ (-s - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have hd := (hd1.sub hd2).div_const (1 - s)
  have hval : (X ^ (1 - s) * (-(1 : ℝ) * t ^ (-(1 : ℝ) - 1)) - -s * t ^ (-s - 1)) / (1 - s) =
      -(t ^ (-(1 : ℝ)) * ((X ^ (1 - s) * t ^ (-(1 : ℝ)) - t ^ (-s)) / (1 - s)) + t ^ (-s - 1)) := by
    have h1 : t ^ (-(1 : ℝ)) * t ^ (-(1 : ℝ)) = t ^ (-(1 : ℝ) - 1) := by
      rw [← Real.rpow_add ht, sub_eq_add_neg]
    have h2 : t ^ (-(1 : ℝ)) * t ^ (-s) = t ^ (-s - 1) := by
      rw [← Real.rpow_add ht]; congr 1; ring
    have hne : 1 - s ≠ 0 := by linarith
    rw [← h1, ← h2]
    field_simp [hne]
    ring
  rw [← hval]
  exact hd

private lemma abel_hs_tail_bound {g : ℕ → ℝ} {K s L1 Ls : ℝ} {P : ℕ}
    (hK : 0 ≤ K) (hP : 2 ≤ P)
    (hG : ∀ n : ℕ, 1 ≤ n → |∑ k ∈ Icc 1 n, g k| ≤ K * (n : ℝ) ^ ((7 : ℝ) / 10))
    (hs1 : (49 : ℝ) / 50 ≤ s) (hs2 : s < 1)
    (hL1 : Tendsto (fun N => Lpartial g N 1) atTop (nhds L1))
    (hLs : Tendsto (fun N => Lpartial g N s) atTop (nhds Ls)) :
    let X : ℕ := P ^ 4
    let U : ℕ := P ^ 3
    |(((X : ℝ) ^ (1 - s) / (1 - s)) * L1 - (1 / (1 - s)) * Ls) -
      ∑ d ∈ Icc 1 U, g d * hsFun (X : ℝ) s (d : ℝ)| ≤
      54 * K * (P : ℝ) ^ ((3 : ℝ) / 25) * (U : ℝ) ^ ((7 : ℝ) / 10 - s) := by
  set X : ℕ := P ^ 4
  set U : ℕ := P ^ 3
  have hP_pos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
  have hP_ge1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast (by omega : 1 ≤ P)
  have hU1 : 1 ≤ U := Nat.one_le_pow 3 P (by omega)
  have hUX : U < X := by
    have : P ^ 3 * 1 < P ^ 3 * P := Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
    have hXeq : X = P ^ 3 * P := by dsimp [X]; ring
    omega
  have hU_pos : (0 : ℝ) < (U : ℝ) := by positivity
  have hX_pos : (0 : ℝ) < (X : ℝ) := by positivity
  have hXU : (X : ℝ) / (U : ℝ) = (P : ℝ) := by
    have hXeq : (X : ℝ) = (U : ℝ) * (P : ℝ) := by push_cast [X, U]; ring
    rw [hXeq, mul_div_cancel_left₀ _ hU_pos.ne']
  have hderiv_le : ∀ t : ℝ, 0 < t →
      |-(t ^ (-(1 : ℝ)) * hsFun (X : ℝ) s t + t ^ (-s - 1))| ≤
        t ^ (-s - 1) * (max (((X : ℝ) / t) ^ (1 - s)) 1 * |Real.log ((X : ℝ) / t)| + 1) := by
    intro t ht
    rw [abs_neg]
    have hhs := hsFun_abs_le hX_pos ht hs1 hs2
    have h1 : t ^ (-(1 : ℝ)) * t ^ (-s) = t ^ (-s - 1) := by
      rw [← Real.rpow_add ht]; congr 1; ring
    calc |t ^ (-(1 : ℝ)) * hsFun (X : ℝ) s t + t ^ (-s - 1)|
        ≤ |t ^ (-(1 : ℝ)) * hsFun (X : ℝ) s t| + |t ^ (-s - 1)| := abs_add_le _ _
      _ = t ^ (-(1 : ℝ)) * |hsFun (X : ℝ) s t| + t ^ (-s - 1) := by
          rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le _),
            abs_of_nonneg (Real.rpow_nonneg ht.le _)]
      _ ≤ t ^ (-(1 : ℝ)) * (t ^ (-s) * max (((X : ℝ) / t) ^ (1 - s)) 1 * |Real.log ((X : ℝ) / t)|) +
            t ^ (-s - 1) := by gcongr
      _ = t ^ (-s - 1) * (max (((X : ℝ) / t) ^ (1 - s)) 1 * |Real.log ((X : ℝ) / t)| + 1) := by
          rw [← mul_assoc, ← mul_assoc, h1]; ring
  have hreg1 : ∀ t : ℝ, (U : ℝ) ≤ t → t ≤ (X : ℝ) →
      |-(t ^ (-(1 : ℝ)) * hsFun (X : ℝ) s t + t ^ (-s - 1))| ≤
        5 * (P : ℝ) ^ ((3 : ℝ) / 25) * t ^ (-s - 1) := by
    intro t htU htX
    have ht_pos : 0 < t := lt_of_lt_of_le hU_pos htU
    have h1le : (1 : ℝ) ≤ (X : ℝ) / t := (one_le_div ht_pos).mpr htX
    have hleP : (X : ℝ) / t ≤ (P : ℝ) := by
      rw [← hXU]; exact div_le_div_of_nonneg_left hX_pos.le hU_pos htU
    have hmax : max (((X : ℝ) / t) ^ (1 - s)) 1 ≤ (P : ℝ) ^ ((1 : ℝ) / 50) := by
      rw [max_le_iff]
      refine ⟨?_, Real.one_le_rpow hP_ge1 (by norm_num)⟩
      calc ((X : ℝ) / t) ^ (1 - s) ≤ (P : ℝ) ^ (1 - s) :=
            Real.rpow_le_rpow (by linarith) hleP (by linarith)
        _ ≤ (P : ℝ) ^ ((1 : ℝ) / 50) :=
            Real.rpow_le_rpow_of_exponent_le hP_ge1 (by linarith)
    have hlog : |Real.log ((X : ℝ) / t)| ≤ 4 * (P : ℝ) ^ ((1 : ℝ) / 10) := by
      rw [abs_of_nonneg (Real.log_nonneg h1le)]
      exact (Real.log_le_log (by linarith) hleP).trans (log_le_4_rpow hP_pos)
    have hcoef : max (((X : ℝ) / t) ^ (1 - s)) 1 * |Real.log ((X : ℝ) / t)| + 1 ≤
        5 * (P : ℝ) ^ ((3 : ℝ) / 25) := by
      have h1P : (1 : ℝ) ≤ (P : ℝ) ^ ((3 : ℝ) / 25) := Real.one_le_rpow hP_ge1 (by norm_num)
      calc max (((X : ℝ) / t) ^ (1 - s)) 1 * |Real.log ((X : ℝ) / t)| + 1
          ≤ (P : ℝ) ^ ((1 : ℝ) / 50) * (4 * (P : ℝ) ^ ((1 : ℝ) / 10)) + 1 := by
            linarith [mul_le_mul hmax hlog (abs_nonneg _) (Real.rpow_nonneg hP_pos.le _)]
        _ = 4 * (P : ℝ) ^ ((3 : ℝ) / 25) + 1 := by
            rw [mul_left_comm, ← Real.rpow_add hP_pos]; congr 2; norm_num
        _ ≤ 5 * (P : ℝ) ^ ((3 : ℝ) / 25) := by linarith
    calc |-(t ^ (-(1 : ℝ)) * hsFun (X : ℝ) s t + t ^ (-s - 1))|
        ≤ t ^ (-s - 1) * (max (((X : ℝ) / t) ^ (1 - s)) 1 * |Real.log ((X : ℝ) / t)| + 1) :=
          hderiv_le t ht_pos
      _ ≤ t ^ (-s - 1) * (5 * (P : ℝ) ^ ((3 : ℝ) / 25)) :=
          mul_le_mul_of_nonneg_left hcoef (Real.rpow_nonneg ht_pos.le _)
      _ = 5 * (P : ℝ) ^ ((3 : ℝ) / 25) * t ^ (-s - 1) := by ring
  have hreg2 : ∀ t : ℝ, (X : ℝ) ≤ t →
      |-(t ^ (-(1 : ℝ)) * hsFun (X : ℝ) s t + t ^ (-s - 1))| ≤
        5 * (X : ℝ) ^ (-(1 : ℝ) / 10) * t ^ ((1 : ℝ) / 10 - s - 1) := by
    intro t htX
    have ht_pos : 0 < t := lt_of_lt_of_le hX_pos htX
    have hle1 : (X : ℝ) / t ≤ 1 := (div_le_one ht_pos).mpr htX
    have hmax : max (((X : ℝ) / t) ^ (1 - s)) 1 = 1 :=
      max_eq_right (Real.rpow_le_one (by positivity) hle1 (by linarith))
    have hlog : |Real.log ((X : ℝ) / t)| + 1 ≤ 5 * (t / (X : ℝ)) ^ ((1 : ℝ) / 10) := by
      have hneg : Real.log ((X : ℝ) / t) = -Real.log (t / (X : ℝ)) := by
        rw [Real.log_div hX_pos.ne' ht_pos.ne', Real.log_div ht_pos.ne' hX_pos.ne']; ring
      rw [hneg, abs_neg, abs_of_nonneg (Real.log_nonneg ((one_le_div hX_pos).mpr htX))]
      exact log_add_one_le_5_rpow ((one_le_div hX_pos).mpr htX)
    calc |-(t ^ (-(1 : ℝ)) * hsFun (X : ℝ) s t + t ^ (-s - 1))|
        ≤ t ^ (-s - 1) * (max (((X : ℝ) / t) ^ (1 - s)) 1 * |Real.log ((X : ℝ) / t)| + 1) :=
          hderiv_le t ht_pos
      _ = t ^ (-s - 1) * (|Real.log ((X : ℝ) / t)| + 1) := by rw [hmax, one_mul]
      _ ≤ t ^ (-s - 1) * (5 * (t / (X : ℝ)) ^ ((1 : ℝ) / 10)) :=
          mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg ht_pos.le _)
      _ = 5 * (X : ℝ) ^ (-(1 : ℝ) / 10) * t ^ ((1 : ℝ) / 10 - s - 1) := by
          rw [Real.div_rpow ht_pos.le hX_pos.le, div_eq_mul_inv, ← Real.rpow_neg hX_pos.le]
          calc t ^ (-s - 1) * (5 * (t ^ ((1 : ℝ) / 10) * (X : ℝ) ^ (-((1 : ℝ) / 10))))
              = 5 * (X : ℝ) ^ (-(1 : ℝ) / 10) * (t ^ ((1 : ℝ) / 10) * t ^ (-s - 1)) := by
                rw [neg_div]; ring
            _ = 5 * (X : ℝ) ^ (-(1 : ℝ) / 10) * t ^ ((1 : ℝ) / 10 - s - 1) := by
                rw [← Real.rpow_add ht_pos]; congr 2; ring
  have hlim_tot : Tendsto (fun Q : ℕ =>
      (∑ d ∈ Icc 1 Q, g d * hsFun (X : ℝ) s (d : ℝ)) -
      ∑ d ∈ Icc 1 U, g d * hsFun (X : ℝ) s (d : ℝ))
      atTop (nhds ((((X : ℝ) ^ (1 - s) / (1 - s)) * L1 - (1 / (1 - s)) * Ls) -
        ∑ d ∈ Icc 1 U, g d * hsFun (X : ℝ) s (d : ℝ))) := by
    have h1 : Tendsto (fun Q : ℕ =>
        ((X : ℝ) ^ (1 - s) / (1 - s)) * Lpartial g Q 1 - (1 / (1 - s)) * Lpartial g Q s)
        atTop (nhds (((X : ℝ) ^ (1 - s) / (1 - s)) * L1 - (1 / (1 - s)) * Ls)) :=
      (hL1.const_mul _).sub (hLs.const_mul _)
    have h2 : ∀ Q : ℕ, ∑ d ∈ Icc 1 Q, g d * hsFun (X : ℝ) s (d : ℝ) =
        ((X : ℝ) ^ (1 - s) / (1 - s)) * Lpartial g Q 1 - (1 / (1 - s)) * Lpartial g Q s := by
      intro Q
      unfold Lpartial hsFun
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d _ => by ring
    simp_rw [h2]
    exact h1.sub_const _
  have hlim_rhs : Tendsto (fun Q : ℕ =>
      5 * K * (X : ℝ) ^ (-(1 : ℝ) / 10) * (Q : ℝ) ^ ((4 : ℝ) / 5 - s) +
      54 * K * (P : ℝ) ^ ((3 : ℝ) / 25) * (U : ℝ) ^ ((7 : ℝ) / 10 - s))
      atTop (nhds (54 * K * (P : ℝ) ^ ((3 : ℝ) / 25) * (U : ℝ) ^ ((7 : ℝ) / 10 - s))) := by
    have hq : Tendsto (fun Q : ℕ => (Q : ℝ) ^ ((4 : ℝ) / 5 - s)) atTop (nhds 0) := by
      have hpos : 0 < s - (4 : ℝ) / 5 := by linarith
      have h0 := rpow_neg_tendsto_zero hpos
      refine (h0.comp (tendsto_sub_atTop_nat 1)).congr' ?_
      filter_upwards [Filter.eventually_ge_atTop 1] with Q hQ
      simp only [Function.comp_apply, Nat.sub_add_cancel hQ]
      congr 1; ring
    simpa using (hq.const_mul (5 * K * (X : ℝ) ^ (-(1 : ℝ) / 10))).add_const _
  refine le_of_tendsto_of_tendsto hlim_tot.abs hlim_rhs ?_
  filter_upwards [Filter.eventually_gt_atTop X] with Q hQX
  have hUQ : U + 1 ≤ Q := by omega
  have hsplit_sum : (∑ d ∈ Icc 1 Q, g d * hsFun (X : ℝ) s (d : ℝ)) -
      ∑ d ∈ Icc 1 U, g d * hsFun (X : ℝ) s (d : ℝ) =
      ∑ d ∈ Icc (U + 1) Q, g d * hsFun (X : ℝ) s (d : ℝ) := by
    have hunion : Icc 1 Q = Icc 1 U ∪ Icc (U + 1) Q := by
      ext d; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Icc 1 U) (Icc (U + 1) Q) := by
      rw [Finset.disjoint_left]
      intro d hd1 hd2; simp only [Finset.mem_Icc] at hd1 hd2; omega
    rw [hunion, Finset.sum_union hdisj]; ring
  rw [hsplit_sum, abel_full_identity g (fun d => hsFun (X : ℝ) s (d : ℝ)) (by omega) hUQ]
  have hU_sub : U + 1 - 1 = U := by omega
  rw [hU_sub]
  have hQ_pos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
  have hbQ : |(∑ k ∈ Icc 1 Q, g k) * hsFun (X : ℝ) s (Q : ℝ)| ≤
      5 * K * (X : ℝ) ^ (-(1 : ℝ) / 10) * (Q : ℝ) ^ ((4 : ℝ) / 5 - s) := by
    rw [abs_mul]
    have hXQ : (X : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQX.le
    have hhsQ : |hsFun (X : ℝ) s (Q : ℝ)| ≤
        5 * (X : ℝ) ^ (-(1 : ℝ) / 10) * (Q : ℝ) ^ ((1 : ℝ) / 10 - s) := by
      have h1 := hsFun_abs_le hX_pos hQ_pos hs1 hs2
      have hmax : max (((X : ℝ) / (Q : ℝ)) ^ (1 - s)) 1 = 1 :=
        max_eq_right (Real.rpow_le_one (by positivity) ((div_le_one hQ_pos).mpr hXQ) (by linarith))
      rw [hmax, mul_one] at h1
      have hlog : |Real.log ((X : ℝ) / (Q : ℝ))| ≤ 5 * ((Q : ℝ) / (X : ℝ)) ^ ((1 : ℝ) / 10) := by
        have hneg : Real.log ((X : ℝ) / (Q : ℝ)) = -Real.log ((Q : ℝ) / (X : ℝ)) := by
          rw [Real.log_div hX_pos.ne' hQ_pos.ne', Real.log_div hQ_pos.ne' hX_pos.ne']; ring
        rw [hneg, abs_neg, abs_of_nonneg (Real.log_nonneg ((one_le_div hX_pos).mpr hXQ))]
        linarith [log_add_one_le_5_rpow ((one_le_div hX_pos).mpr hXQ)]
      calc |hsFun (X : ℝ) s (Q : ℝ)|
          ≤ (Q : ℝ) ^ (-s) * (5 * ((Q : ℝ) / (X : ℝ)) ^ ((1 : ℝ) / 10)) :=
            h1.trans (mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hQ_pos.le _))
        _ = 5 * (X : ℝ) ^ (-(1 : ℝ) / 10) * (Q : ℝ) ^ ((1 : ℝ) / 10 - s) := by
            rw [Real.div_rpow hQ_pos.le hX_pos.le, div_eq_mul_inv, ← Real.rpow_neg hX_pos.le]
            calc (Q : ℝ) ^ (-s) * (5 * ((Q : ℝ) ^ ((1 : ℝ) / 10) * (X : ℝ) ^ (-((1 : ℝ) / 10))))
                = 5 * (X : ℝ) ^ (-(1 : ℝ) / 10) * ((Q : ℝ) ^ ((1 : ℝ) / 10) * (Q : ℝ) ^ (-s)) := by
                  rw [neg_div]; ring
              _ = _ := by rw [← Real.rpow_add hQ_pos, sub_eq_add_neg]
    calc |∑ k ∈ Icc 1 Q, g k| * |hsFun (X : ℝ) s (Q : ℝ)|
        ≤ (K * (Q : ℝ) ^ ((7 : ℝ) / 10)) *
            (5 * (X : ℝ) ^ (-(1 : ℝ) / 10) * (Q : ℝ) ^ ((1 : ℝ) / 10 - s)) :=
          mul_le_mul (hG Q (by omega)) hhsQ (abs_nonneg _) (by positivity)
      _ = 5 * K * (X : ℝ) ^ (-(1 : ℝ) / 10) * (Q : ℝ) ^ ((4 : ℝ) / 5 - s) := by
          calc K * (Q : ℝ) ^ ((7 : ℝ) / 10) *
                (5 * (X : ℝ) ^ (-(1 : ℝ) / 10) * (Q : ℝ) ^ ((1 : ℝ) / 10 - s))
              = 5 * K * (X : ℝ) ^ (-(1 : ℝ) / 10) *
                  ((Q : ℝ) ^ ((7 : ℝ) / 10) * (Q : ℝ) ^ ((1 : ℝ) / 10 - s)) := by ring
            _ = _ := by rw [← Real.rpow_add hQ_pos]; congr 2; ring
  have hbU : |(∑ k ∈ Icc 1 U, g k) * hsFun (X : ℝ) s ((U + 1 : ℕ) : ℝ)| ≤
      4 * K * (P : ℝ) ^ ((3 : ℝ) / 25) * (U : ℝ) ^ ((7 : ℝ) / 10 - s) := by
    rw [abs_mul]
    have hU1_pos : (0 : ℝ) < ((U + 1 : ℕ) : ℝ) := by positivity
    have hU1_leX : ((U + 1 : ℕ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast hUX
    have hU_leU1 : (U : ℝ) ≤ ((U + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ U
    have hhsU : |hsFun (X : ℝ) s ((U + 1 : ℕ) : ℝ)| ≤
        4 * (P : ℝ) ^ ((3 : ℝ) / 25) * (U : ℝ) ^ (-s) := by
      have h1 := hsFun_abs_le hX_pos hU1_pos hs1 hs2
      have h1le : (1 : ℝ) ≤ (X : ℝ) / ((U + 1 : ℕ) : ℝ) := (one_le_div hU1_pos).mpr hU1_leX
      have hleP : (X : ℝ) / ((U + 1 : ℕ) : ℝ) ≤ (P : ℝ) := by
        rw [← hXU]; exact div_le_div_of_nonneg_left hX_pos.le hU_pos hU_leU1
      have hmax : max (((X : ℝ) / ((U + 1 : ℕ) : ℝ)) ^ (1 - s)) 1 ≤ (P : ℝ) ^ ((1 : ℝ) / 50) := by
        rw [max_le_iff]
        refine ⟨?_, Real.one_le_rpow hP_ge1 (by norm_num)⟩
        calc ((X : ℝ) / ((U + 1 : ℕ) : ℝ)) ^ (1 - s) ≤ (P : ℝ) ^ (1 - s) :=
              Real.rpow_le_rpow (by linarith) hleP (by linarith)
          _ ≤ (P : ℝ) ^ ((1 : ℝ) / 50) :=
              Real.rpow_le_rpow_of_exponent_le hP_ge1 (by linarith)
      have hlog : |Real.log ((X : ℝ) / ((U + 1 : ℕ) : ℝ))| ≤ 4 * (P : ℝ) ^ ((1 : ℝ) / 10) := by
        rw [abs_of_nonneg (Real.log_nonneg h1le)]
        exact (Real.log_le_log (by linarith) hleP).trans (log_le_4_rpow hP_pos)
      have hpowU : ((U + 1 : ℕ) : ℝ) ^ (-s) ≤ (U : ℝ) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos hU_pos hU_leU1 (by linarith)
      calc |hsFun (X : ℝ) s ((U + 1 : ℕ) : ℝ)|
          ≤ (U : ℝ) ^ (-s) * (P : ℝ) ^ ((1 : ℝ) / 50) * (4 * (P : ℝ) ^ ((1 : ℝ) / 10)) := by
            refine h1.trans ?_
            exact mul_le_mul
              (mul_le_mul hpowU hmax (by positivity) (Real.rpow_nonneg hU_pos.le _))
              hlog (abs_nonneg _) (by positivity)
        _ = 4 * (P : ℝ) ^ ((3 : ℝ) / 25) * (U : ℝ) ^ (-s) := by
            calc (U : ℝ) ^ (-s) * (P : ℝ) ^ ((1 : ℝ) / 50) * (4 * (P : ℝ) ^ ((1 : ℝ) / 10))
                = 4 * ((P : ℝ) ^ ((1 : ℝ) / 50) * (P : ℝ) ^ ((1 : ℝ) / 10)) * (U : ℝ) ^ (-s) := by
                  ring
              _ = _ := by rw [← Real.rpow_add hP_pos]; congr 2; norm_num
    calc |∑ k ∈ Icc 1 U, g k| * |hsFun (X : ℝ) s ((U + 1 : ℕ) : ℝ)|
        ≤ (K * (U : ℝ) ^ ((7 : ℝ) / 10)) * (4 * (P : ℝ) ^ ((3 : ℝ) / 25) * (U : ℝ) ^ (-s)) :=
          mul_le_mul (hG U hU1) hhsU (abs_nonneg _) (by positivity)
      _ = 4 * K * (P : ℝ) ^ ((3 : ℝ) / 25) * (U : ℝ) ^ ((7 : ℝ) / 10 - s) := by
          calc K * (U : ℝ) ^ ((7 : ℝ) / 10) * (4 * (P : ℝ) ^ ((3 : ℝ) / 25) * (U : ℝ) ^ (-s))
              = 4 * K * (P : ℝ) ^ ((3 : ℝ) / 25) * ((U : ℝ) ^ ((7 : ℝ) / 10) * (U : ℝ) ^ (-s)) := by
                ring
            _ = _ := by rw [← Real.rpow_add hU_pos, sub_eq_add_neg]
  have hstep_diff : ∀ d : ℕ, 1 ≤ d →
      |hsFun (X : ℝ) s (d : ℝ) - hsFun (X : ℝ) s ((d + 1 : ℕ) : ℝ)| ≤
        ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ),
          |-(t ^ (-(1 : ℝ)) * hsFun (X : ℝ) s t + t ^ (-s - 1))| := by
    intro d hd
    have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hle : (d : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ d
    have hcont : ContinuousOn (fun t : ℝ => -(t ^ (-(1 : ℝ)) * hsFun (X : ℝ) s t + t ^ (-s - 1)))
        (Set.uIcc (d : ℝ) ((d + 1 : ℕ) : ℝ)) := by
      rw [Set.uIcc_of_le hle]
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le hd_pos ht.1
      have h1 := Real.continuousAt_rpow_const t (-(1 : ℝ)) (Or.inl ht_pos.ne')
      have h2 := Real.continuousAt_rpow_const t (-s) (Or.inl ht_pos.ne')
      have h3 := Real.continuousAt_rpow_const t (-s - 1) (Or.inl ht_pos.ne')
      have hhs_cont : ContinuousAt (hsFun (X : ℝ) s) t :=
        (((continuousAt_const.mul h1).sub h2).div_const _)
      exact ((h1.mul hhs_cont).add h3).neg.continuousWithinAt
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_hsFun (lt_of_lt_of_le hd_pos (by rw [Set.uIcc_of_le hle] at ht; exact ht.1)) hs2)
      hcont.intervalIntegrable
    rw [abs_sub_comm, ← hftc]
    exact intervalIntegral.abs_integral_le_integral_abs hle
  have hsum_mid : |∑ d ∈ Icc (U + 1) (Q - 1),
        (∑ k ∈ Icc 1 d, g k) * (hsFun (X : ℝ) s (d : ℝ) - hsFun (X : ℝ) s ((d + 1 : ℕ) : ℝ))| ≤
      50 * K * (P : ℝ) ^ ((3 : ℝ) / 25) * (U : ℝ) ^ ((7 : ℝ) / 10 - s) := by
    have hunion : Icc (U + 1) (Q - 1) = Icc (U + 1) (X - 1) ∪ Icc X (Q - 1) := by
      ext d; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Icc (U + 1) (X - 1)) (Icc X (Q - 1)) := by
      rw [Finset.disjoint_left]
      intro d hd1 hd2; simp only [Finset.mem_Icc] at hd1 hd2; omega
    rw [hunion, Finset.sum_union hdisj]
    have hint_rpow : ∀ α : ℝ, ∀ a b : ℝ, 0 < a → a ≤ b →
        IntervalIntegrable (fun t : ℝ => t ^ α) MeasureTheory.volume a b := by
      intro α a b ha hab
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hab]
      intro t ht
      exact (Real.continuousAt_rpow_const t α
        (Or.inl (lt_of_lt_of_le ha ht.1).ne')).continuousWithinAt
    have hsum_adj : ∀ α : ℝ, ∀ A B : ℕ, 1 ≤ A → A ≤ B →
        ∑ d ∈ Icc A (B - 1), ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ), t ^ α =
          ∫ t in (A : ℝ)..(B : ℝ), t ^ α := by
      intro α A B hA hAB
      induction B, hAB using Nat.le_induction with
      | base =>
        have hemp : Icc A (A - 1) = ∅ := Finset.Icc_eq_empty (by omega)
        simp [hemp]
      | succ k hk ih =>
        have hk1 : k + 1 - 1 = k := by omega
        rw [hk1]
        have hIcc : Icc A k = insert k (Icc A (k - 1)) := by
          ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih, add_comm]
        exact intervalIntegral.integral_add_adjacent_intervals
          (hint_rpow α (A : ℝ) (k : ℝ) (by exact_mod_cast (by omega : 0 < A)) (by exact_mod_cast hk))
          (hint_rpow α (k : ℝ) ((k + 1 : ℕ) : ℝ) (by exact_mod_cast (by omega : 0 < k))
            (by exact_mod_cast Nat.le_succ k))
    have hpart1 : |∑ d ∈ Icc (U + 1) (X - 1),
          (∑ k ∈ Icc 1 d, g k) * (hsFun (X : ℝ) s (d : ℝ) - hsFun (X : ℝ) s ((d + 1 : ℕ) : ℝ))| ≤
        20 * K * (P : ℝ) ^ ((3 : ℝ) / 25) * (U : ℝ) ^ ((7 : ℝ) / 10 - s) := by
      have hterm1 : ∀ d ∈ Icc (U + 1) (X - 1),
          |(∑ k ∈ Icc 1 d, g k) * (hsFun (X : ℝ) s (d : ℝ) - hsFun (X : ℝ) s ((d + 1 : ℕ) : ℝ))| ≤
            5 * K * (P : ℝ) ^ ((3 : ℝ) / 25) *
              ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ), t ^ ((7 : ℝ) / 10 - s - 1) := by
        intro d hd
        simp only [Finset.mem_Icc] at hd
        have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
        have hle : (d : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ d
        rw [abs_mul]
        have hint_abs : IntervalIntegrable
            (fun t : ℝ => |-(t ^ (-(1 : ℝ)) * hsFun (X : ℝ) s t + t ^ (-s - 1))|)
            MeasureTheory.volume (d : ℝ) ((d + 1 : ℕ) : ℝ) := by
          refine ContinuousOn.intervalIntegrable ?_
          rw [Set.uIcc_of_le hle]
          intro t ht
          have ht_pos : 0 < t := lt_of_lt_of_le hd_pos ht.1
          have h1 := Real.continuousAt_rpow_const t (-(1 : ℝ)) (Or.inl ht_pos.ne')
          have h2 := Real.continuousAt_rpow_const t (-s) (Or.inl ht_pos.ne')
          have h3 := Real.continuousAt_rpow_const t (-s - 1) (Or.inl ht_pos.ne')
          have hhs_cont : ContinuousAt (hsFun (X : ℝ) s) t :=
            (((continuousAt_const.mul h1).sub h2).div_const _)
          exact ((h1.mul hhs_cont).add h3).neg.abs.continuousWithinAt
        have hint_le : ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ),
              |-(t ^ (-(1 : ℝ)) * hsFun (X : ℝ) s t + t ^ (-s - 1))| ≤
            ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ),
              5 * (P : ℝ) ^ ((3 : ℝ) / 25) * t ^ (-s - 1) := by
          refine intervalIntegral.integral_mono_on hle hint_abs
            ((hint_rpow (-s - 1) (d : ℝ) ((d + 1 : ℕ) : ℝ) hd_pos hle).const_mul _)
            fun t ht => hreg1 t (le_trans (by exact_mod_cast (by omega : U ≤ d)) ht.1)
              (le_trans ht.2 (by exact_mod_cast (by omega : d + 1 ≤ X)))
        calc |∑ k ∈ Icc 1 d, g k| * |hsFun (X : ℝ) s (d : ℝ) - hsFun (X : ℝ) s ((d + 1 : ℕ) : ℝ)|
            ≤ (K * (d : ℝ) ^ ((7 : ℝ) / 10)) *
                ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ), 5 * (P : ℝ) ^ ((3 : ℝ) / 25) * t ^ (-s - 1) :=
              mul_le_mul (hG d (by omega)) ((hstep_diff d (by omega)).trans hint_le)
                (abs_nonneg _) (by positivity)
          _ = 5 * K * (P : ℝ) ^ ((3 : ℝ) / 25) *
                ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ), (d : ℝ) ^ ((7 : ℝ) / 10) * t ^ (-s - 1) := by
              rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]; ring
          _ ≤ 5 * K * (P : ℝ) ^ ((3 : ℝ) / 25) *
                ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ), t ^ ((7 : ℝ) / 10 - s - 1) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              refine intervalIntegral.integral_mono_on hle
                ((hint_rpow (-s - 1) (d : ℝ) ((d + 1 : ℕ) : ℝ) hd_pos hle).const_mul _)
                (hint_rpow _ (d : ℝ) ((d + 1 : ℕ) : ℝ) hd_pos hle) fun t ht => ?_
              have ht_pos : 0 < t := lt_of_lt_of_le hd_pos ht.1
              calc (d : ℝ) ^ ((7 : ℝ) / 10) * t ^ (-s - 1)
                  ≤ t ^ ((7 : ℝ) / 10) * t ^ (-s - 1) :=
                    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hd_pos.le ht.1 (by norm_num))
                      (Real.rpow_nonneg ht_pos.le _)
                _ = t ^ ((7 : ℝ) / 10 - s - 1) := by rw [← Real.rpow_add ht_pos]; congr 1; ring
      calc |∑ d ∈ Icc (U + 1) (X - 1),
              (∑ k ∈ Icc 1 d, g k) * (hsFun (X : ℝ) s (d : ℝ) - hsFun (X : ℝ) s ((d + 1 : ℕ) : ℝ))|
          ≤ ∑ d ∈ Icc (U + 1) (X - 1),
              |(∑ k ∈ Icc 1 d, g k) * (hsFun (X : ℝ) s (d : ℝ) - hsFun (X : ℝ) s ((d + 1 : ℕ) : ℝ))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ Icc (U + 1) (X - 1),
              5 * K * (P : ℝ) ^ ((3 : ℝ) / 25) *
                ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ), t ^ ((7 : ℝ) / 10 - s - 1) :=
            Finset.sum_le_sum hterm1
        _ = 5 * K * (P : ℝ) ^ ((3 : ℝ) / 25) *
              ∫ t in ((U + 1 : ℕ) : ℝ)..(X : ℝ), t ^ ((7 : ℝ) / 10 - s - 1) := by
            rw [← Finset.mul_sum, hsum_adj _ (U + 1) X (by omega) hUX]
        _ = 5 * K * (P : ℝ) ^ ((3 : ℝ) / 25) *
              ((((U + 1 : ℕ) : ℝ) ^ ((7 : ℝ) / 10 - s) - (X : ℝ) ^ ((7 : ℝ) / 10 - s)) /
                (s - (7 : ℝ) / 10)) := by
            have heq : (fun t : ℝ => t ^ ((7 : ℝ) / 10 - s - 1)) =
                (fun t : ℝ => t ^ (-(s + 1 - (7 : ℝ) / 10))) := by ext t; congr 1; ring
            rw [heq, integral_rpow_neg_eq (by linarith) (by positivity) (by exact_mod_cast hUX)]
            have h1 : 1 - (s + 1 - (7 : ℝ) / 10) = (7 : ℝ) / 10 - s := by ring
            have h2 : s + 1 - (7 : ℝ) / 10 - 1 = s - (7 : ℝ) / 10 := by ring
            rw [h1, h2]
        _ ≤ 5 * K * (P : ℝ) ^ ((3 : ℝ) / 25) *
              ((U : ℝ) ^ ((7 : ℝ) / 10 - s) / ((7 : ℝ) / 25)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hnum : ((U + 1 : ℕ) : ℝ) ^ ((7 : ℝ) / 10 - s) - (X : ℝ) ^ ((7 : ℝ) / 10 - s) ≤
                (U : ℝ) ^ ((7 : ℝ) / 10 - s) := by
              have h1 := Real.rpow_le_rpow_of_nonpos hU_pos
                (by exact_mod_cast Nat.le_succ U : (U : ℝ) ≤ ((U + 1 : ℕ) : ℝ))
                (by linarith : (7 : ℝ) / 10 - s ≤ 0)
              linarith [Real.rpow_nonneg hX_pos.le ((7 : ℝ) / 10 - s)]
            calc (((U + 1 : ℕ) : ℝ) ^ ((7 : ℝ) / 10 - s) - (X : ℝ) ^ ((7 : ℝ) / 10 - s)) /
                    (s - (7 : ℝ) / 10)
                ≤ (U : ℝ) ^ ((7 : ℝ) / 10 - s) / (s - (7 : ℝ) / 10) :=
                  div_le_div_of_nonneg_right hnum (by linarith)
              _ ≤ (U : ℝ) ^ ((7 : ℝ) / 10 - s) / ((7 : ℝ) / 25) :=
                  div_le_div_of_nonneg_left (Real.rpow_nonneg hU_pos.le _) (by norm_num) (by linarith)
        _ ≤ 20 * K * (P : ℝ) ^ ((3 : ℝ) / 25) * (U : ℝ) ^ ((7 : ℝ) / 10 - s) := by
            have hnn : 0 ≤ K * (P : ℝ) ^ ((3 : ℝ) / 25) * (U : ℝ) ^ ((7 : ℝ) / 10 - s) := by positivity
            linarith
    have hpart2 : |∑ d ∈ Icc X (Q - 1),
          (∑ k ∈ Icc 1 d, g k) * (hsFun (X : ℝ) s (d : ℝ) - hsFun (X : ℝ) s ((d + 1 : ℕ) : ℝ))| ≤
        30 * K * (P : ℝ) ^ ((3 : ℝ) / 25) * (U : ℝ) ^ ((7 : ℝ) / 10 - s) := by
      have hterm2 : ∀ d ∈ Icc X (Q - 1),
          |(∑ k ∈ Icc 1 d, g k) * (hsFun (X : ℝ) s (d : ℝ) - hsFun (X : ℝ) s ((d + 1 : ℕ) : ℝ))| ≤
            5 * K * (X : ℝ) ^ (-(1 : ℝ) / 10) *
              ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ), t ^ ((4 : ℝ) / 5 - s - 1) := by
        intro d hd
        simp only [Finset.mem_Icc] at hd
        have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
        have hle : (d : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ d
        rw [abs_mul]
        have hint_abs : IntervalIntegrable
            (fun t : ℝ => |-(t ^ (-(1 : ℝ)) * hsFun (X : ℝ) s t + t ^ (-s - 1))|)
            MeasureTheory.volume (d : ℝ) ((d + 1 : ℕ) : ℝ) := by
          refine ContinuousOn.intervalIntegrable ?_
          rw [Set.uIcc_of_le hle]
          intro t ht
          have ht_pos : 0 < t := lt_of_lt_of_le hd_pos ht.1
          have h1 := Real.continuousAt_rpow_const t (-(1 : ℝ)) (Or.inl ht_pos.ne')
          have h2 := Real.continuousAt_rpow_const t (-s) (Or.inl ht_pos.ne')
          have h3 := Real.continuousAt_rpow_const t (-s - 1) (Or.inl ht_pos.ne')
          have hhs_cont : ContinuousAt (hsFun (X : ℝ) s) t :=
            (((continuousAt_const.mul h1).sub h2).div_const _)
          exact ((h1.mul hhs_cont).add h3).neg.abs.continuousWithinAt
        have hint_le : ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ),
              |-(t ^ (-(1 : ℝ)) * hsFun (X : ℝ) s t + t ^ (-s - 1))| ≤
            ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ),
              5 * (X : ℝ) ^ (-(1 : ℝ) / 10) * t ^ ((1 : ℝ) / 10 - s - 1) := by
          refine intervalIntegral.integral_mono_on hle hint_abs
            ((hint_rpow ((1 : ℝ) / 10 - s - 1) (d : ℝ) ((d + 1 : ℕ) : ℝ) hd_pos hle).const_mul _)
            fun t ht => hreg2 t (le_trans (by exact_mod_cast hd.1) ht.1)
        calc |∑ k ∈ Icc 1 d, g k| * |hsFun (X : ℝ) s (d : ℝ) - hsFun (X : ℝ) s ((d + 1 : ℕ) : ℝ)|
            ≤ (K * (d : ℝ) ^ ((7 : ℝ) / 10)) *
                ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ),
                  5 * (X : ℝ) ^ (-(1 : ℝ) / 10) * t ^ ((1 : ℝ) / 10 - s - 1) :=
              mul_le_mul (hG d (by omega)) ((hstep_diff d (by omega)).trans hint_le)
                (abs_nonneg _) (by positivity)
          _ = 5 * K * (X : ℝ) ^ (-(1 : ℝ) / 10) *
                ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ),
                  (d : ℝ) ^ ((7 : ℝ) / 10) * t ^ ((1 : ℝ) / 10 - s - 1) := by
              rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]; ring
          _ ≤ 5 * K * (X : ℝ) ^ (-(1 : ℝ) / 10) *
                ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ), t ^ ((4 : ℝ) / 5 - s - 1) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              refine intervalIntegral.integral_mono_on hle
                ((hint_rpow _ (d : ℝ) ((d + 1 : ℕ) : ℝ) hd_pos hle).const_mul _)
                (hint_rpow _ (d : ℝ) ((d + 1 : ℕ) : ℝ) hd_pos hle) fun t ht => ?_
              have ht_pos : 0 < t := lt_of_lt_of_le hd_pos ht.1
              calc (d : ℝ) ^ ((7 : ℝ) / 10) * t ^ ((1 : ℝ) / 10 - s - 1)
                  ≤ t ^ ((7 : ℝ) / 10) * t ^ ((1 : ℝ) / 10 - s - 1) :=
                    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hd_pos.le ht.1 (by norm_num))
                      (Real.rpow_nonneg ht_pos.le _)
                _ = t ^ ((4 : ℝ) / 5 - s - 1) := by rw [← Real.rpow_add ht_pos]; congr 1; ring
      calc |∑ d ∈ Icc X (Q - 1),
              (∑ k ∈ Icc 1 d, g k) * (hsFun (X : ℝ) s (d : ℝ) - hsFun (X : ℝ) s ((d + 1 : ℕ) : ℝ))|
          ≤ ∑ d ∈ Icc X (Q - 1),
              |(∑ k ∈ Icc 1 d, g k) * (hsFun (X : ℝ) s (d : ℝ) - hsFun (X : ℝ) s ((d + 1 : ℕ) : ℝ))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ Icc X (Q - 1),
              5 * K * (X : ℝ) ^ (-(1 : ℝ) / 10) *
                ∫ t in (d : ℝ)..((d + 1 : ℕ) : ℝ), t ^ ((4 : ℝ) / 5 - s - 1) :=
            Finset.sum_le_sum hterm2
        _ = 5 * K * (X : ℝ) ^ (-(1 : ℝ) / 10) *
              ∫ t in (X : ℝ)..(Q : ℝ), t ^ ((4 : ℝ) / 5 - s - 1) := by
            rw [← Finset.mul_sum, hsum_adj _ X Q (by omega) hQX.le]
        _ = 5 * K * (X : ℝ) ^ (-(1 : ℝ) / 10) *
              (((X : ℝ) ^ ((4 : ℝ) / 5 - s) - (Q : ℝ) ^ ((4 : ℝ) / 5 - s)) /
                (s - (4 : ℝ) / 5)) := by
            have heq : (fun t : ℝ => t ^ ((4 : ℝ) / 5 - s - 1)) =
                (fun t : ℝ => t ^ (-(s + 1 - (4 : ℝ) / 5))) := by ext t; congr 1; ring
            rw [heq, integral_rpow_neg_eq (by linarith) hX_pos (by exact_mod_cast hQX.le)]
            have h1 : 1 - (s + 1 - (4 : ℝ) / 5) = (4 : ℝ) / 5 - s := by ring
            have h2 : s + 1 - (4 : ℝ) / 5 - 1 = s - (4 : ℝ) / 5 := by ring
            rw [h1, h2]
        _ ≤ 5 * K * (X : ℝ) ^ (-(1 : ℝ) / 10) * ((X : ℝ) ^ ((4 : ℝ) / 5 - s) / ((1 : ℝ) / 6)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hnum : (X : ℝ) ^ ((4 : ℝ) / 5 - s) - (Q : ℝ) ^ ((4 : ℝ) / 5 - s) ≤
                (X : ℝ) ^ ((4 : ℝ) / 5 - s) := by
              linarith [Real.rpow_nonneg hQ_pos.le ((4 : ℝ) / 5 - s)]
            calc ((X : ℝ) ^ ((4 : ℝ) / 5 - s) - (Q : ℝ) ^ ((4 : ℝ) / 5 - s)) / (s - (4 : ℝ) / 5)
                ≤ (X : ℝ) ^ ((4 : ℝ) / 5 - s) / (s - (4 : ℝ) / 5) :=
                  div_le_div_of_nonneg_right hnum (by linarith)
              _ ≤ (X : ℝ) ^ ((4 : ℝ) / 5 - s) / ((1 : ℝ) / 6) :=
                  div_le_div_of_nonneg_left (Real.rpow_nonneg hX_pos.le _) (by norm_num) (by linarith)
        _ = 30 * K * (X : ℝ) ^ ((7 : ℝ) / 10 - s) := by
            calc 5 * K * (X : ℝ) ^ (-(1 : ℝ) / 10) * ((X : ℝ) ^ ((4 : ℝ) / 5 - s) / ((1 : ℝ) / 6))
                = 30 * K * ((X : ℝ) ^ (-(1 : ℝ) / 10) * (X : ℝ) ^ ((4 : ℝ) / 5 - s)) := by ring
              _ = _ := by rw [← Real.rpow_add hX_pos]; congr 2; ring
        _ ≤ 30 * K * (P : ℝ) ^ ((3 : ℝ) / 25) * (U : ℝ) ^ ((7 : ℝ) / 10 - s) := by
            have h1 : (X : ℝ) ^ ((7 : ℝ) / 10 - s) ≤ (U : ℝ) ^ ((7 : ℝ) / 10 - s) :=
              Real.rpow_le_rpow_of_nonpos hU_pos (by exact_mod_cast hUX.le) (by linarith)
            have h2 : (1 : ℝ) ≤ (P : ℝ) ^ ((3 : ℝ) / 25) := Real.one_le_rpow hP_ge1 (by norm_num)
            have h3 : 30 * K * (X : ℝ) ^ ((7 : ℝ) / 10 - s) ≤ 30 * K * (U : ℝ) ^ ((7 : ℝ) / 10 - s) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
            calc 30 * K * (X : ℝ) ^ ((7 : ℝ) / 10 - s)
                ≤ 30 * K * (U : ℝ) ^ ((7 : ℝ) / 10 - s) := h3
              _ = 30 * K * 1 * (U : ℝ) ^ ((7 : ℝ) / 10 - s) := by ring
              _ ≤ 30 * K * (P : ℝ) ^ ((3 : ℝ) / 25) * (U : ℝ) ^ ((7 : ℝ) / 10 - s) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity))
                    (Real.rpow_nonneg hU_pos.le _)
    exact (abs_add_le _ _).trans (by linarith)
  calc |(∑ k ∈ Icc 1 Q, g k) * hsFun (X : ℝ) s (Q : ℝ) -
        (∑ k ∈ Icc 1 U, g k) * hsFun (X : ℝ) s ((U + 1 : ℕ) : ℝ) +
        ∑ d ∈ Icc (U + 1) (Q - 1),
          (∑ k ∈ Icc 1 d, g k) * (hsFun (X : ℝ) s (d : ℝ) - hsFun (X : ℝ) s ((d + 1 : ℕ) : ℝ))|
      ≤ |(∑ k ∈ Icc 1 Q, g k) * hsFun (X : ℝ) s (Q : ℝ) -
          (∑ k ∈ Icc 1 U, g k) * hsFun (X : ℝ) s ((U + 1 : ℕ) : ℝ)| +
        |∑ d ∈ Icc (U + 1) (Q - 1),
          (∑ k ∈ Icc 1 d, g k) * (hsFun (X : ℝ) s (d : ℝ) - hsFun (X : ℝ) s ((d + 1 : ℕ) : ℝ))| :=
        abs_add_le _ _
    _ ≤ |(∑ k ∈ Icc 1 Q, g k) * hsFun (X : ℝ) s (Q : ℝ)| +
        |(∑ k ∈ Icc 1 U, g k) * hsFun (X : ℝ) s ((U + 1 : ℕ) : ℝ)| +
        |∑ d ∈ Icc (U + 1) (Q - 1),
          (∑ k ∈ Icc 1 d, g k) * (hsFun (X : ℝ) s (d : ℝ) - hsFun (X : ℝ) s ((d + 1 : ℕ) : ℝ))| := by
        linarith [abs_sub ((∑ k ∈ Icc 1 Q, g k) * hsFun (X : ℝ) s (Q : ℝ))
          ((∑ k ∈ Icc 1 U, g k) * hsFun (X : ℝ) s ((U + 1 : ℕ) : ℝ))]
    _ ≤ _ := by linarith

/- Step 2 main hyperbola inequality and final contradiction -/

private lemma step2_hyperbola_core {g : ℕ → ℝ} {L1 Ls s : ℝ} {P : ℕ}
    (hP_big : 2 ^ 60 ≤ P) (hs1 : (49 : ℝ) / 50 ≤ s) (hs2 : s < 1)
    (hG_bound : ∀ n : ℕ, 1 ≤ n →
      |∑ k ∈ Icc 1 n, g k| ≤ (646 * (P : ℝ) ^ ((7 : ℝ) / 20)) * (n : ℝ) ^ ((7 : ℝ) / 10))
    (hg_abs : ∀ d : ℕ, 1 ≤ d → |g d| ≤ dconv (fun _ => 1) (dconv (fun _ => 1) (fun _ => 1)) d)
    (hf1 : dconv (fun _ => 1) g 1 = 1)
    (hf_nn : ∀ n : ℕ, 1 ≤ n → 0 ≤ dconv (fun _ => 1) g n)
    (hlim1 : Tendsto (fun N => Lpartial g N 1) atTop (nhds L1))
    (hlims : Tendsto (fun N => Lpartial g N s) atTop (nhds Ls)) :
    (1 : ℝ) ≤ (((P ^ 4 : ℕ) : ℝ) ^ (1 - s) / (1 - s)) * L1 + zetaVal s * Ls + (1 : ℝ) / 16 := by
  have hP_rbig : (2 : ℝ) ^ (60 : ℕ) ≤ (P : ℝ) := by exact_mod_cast hP_big
  have hP_pos : (0 : ℝ) < (P : ℝ) := by positivity
  have hP_ge1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast (by omega : 1 ≤ P)
  set K : ℝ := 646 * (P : ℝ) ^ ((7 : ℝ) / 20)
  have hK_nn : 0 ≤ K := by positivity
  set X : ℕ := P ^ 4
  set U : ℕ := P ^ 3
  have hU1 : 1 ≤ U := Nat.one_le_pow 3 P (by omega)
  have hUX : U ≤ X := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hX_div_U : X / U = P := by
    have hmul : X = P * U := by dsimp [X, U]; ring
    rw [hmul, Nat.mul_div_cancel _ (by omega)]
  have hsum_ge1 : (1 : ℝ) ≤ ∑ n ∈ Icc 1 X, dconv (fun _ => 1) g n * (n : ℝ) ^ (-s) := by
    have h1mem : (1 : ℕ) ∈ Icc 1 X := Finset.mem_Icc.mpr ⟨le_rfl, le_trans hU1 hUX⟩
    have h1val : dconv (fun _ => 1) g 1 * ((1 : ℕ) : ℝ) ^ (-s) = 1 := by rw [hf1]; simp
    calc (1 : ℝ) = dconv (fun _ => 1) g 1 * ((1 : ℕ) : ℝ) ^ (-s) := h1val.symm
      _ ≤ ∑ n ∈ Icc 1 X, dconv (fun _ => 1) g n * (n : ℝ) ^ (-s) := by
          refine Finset.single_le_sum (f := fun n : ℕ => dconv (fun _ => 1) g n * (n : ℝ) ^ (-s))
            (fun n hn => ?_) h1mem
          exact mul_nonneg (hf_nn n (Finset.mem_Icc.mp hn).1) (Real.rpow_nonneg (by positivity) _)
  have hw_mul : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      ((a * b : ℕ) : ℝ) ^ (-s) = (a : ℝ) ^ (-s) * (b : ℝ) ^ (-s) := by
    intro a b _ _; push_cast; exact Real.mul_rpow (by positivity) (by positivity)
  have hhyp := dirichlet_hyperbola (fun _ => 1) g (fun n => (n : ℝ) ^ (-s)) hU1 hUX hw_mul
  rw [hX_div_U] at hhyp
  simp only [one_mul] at hhyp
  have hX_cast : (X : ℝ) = (P : ℝ) ^ (4 : ℕ) := by push_cast [X]; rfl
  have hU_cast : (U : ℝ) = (P : ℝ) ^ (3 : ℕ) := by push_cast [U]; rfl
  have hU_pos : (0 : ℝ) < (U : ℝ) := by positivity
  have hU_pow : (U : ℝ) ^ ((7 : ℝ) / 10 - s) ≤ (P : ℝ) ^ (-(21 : ℝ) / 25) := by
    calc (U : ℝ) ^ ((7 : ℝ) / 10 - s)
        ≤ (U : ℝ) ^ (-(7 : ℝ) / 25) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hU1) (by linarith)
      _ = (P : ℝ) ^ (-(21 : ℝ) / 25) := by
          rw [hU_cast, ← Real.rpow_natCast, ← Real.rpow_mul hP_pos.le]; congr 1; norm_num
  have hKU : K * (U : ℝ) ^ ((7 : ℝ) / 10 - s) ≤ 646 * (P : ℝ) ^ (-(49 : ℝ) / 100) := by
    calc K * (U : ℝ) ^ ((7 : ℝ) / 10 - s)
        ≤ 646 * (P : ℝ) ^ ((7 : ℝ) / 20) * (P : ℝ) ^ (-(21 : ℝ) / 25) :=
          mul_le_mul_of_nonneg_left hU_pow hK_nn
      _ = 646 * (P : ℝ) ^ (-(49 : ℝ) / 100) := by
          rw [mul_assoc, ← Real.rpow_add hP_pos]; congr 2; norm_num
  have hKPU : K * (P : ℝ) ^ ((3 : ℝ) / 25) * (U : ℝ) ^ ((7 : ℝ) / 10 - s) ≤
      646 * (P : ℝ) ^ (-(37 : ℝ) / 100) := by
    calc K * (P : ℝ) ^ ((3 : ℝ) / 25) * (U : ℝ) ^ ((7 : ℝ) / 10 - s)
        = (P : ℝ) ^ ((3 : ℝ) / 25) * (K * (U : ℝ) ^ ((7 : ℝ) / 10 - s)) := by ring
      _ ≤ (P : ℝ) ^ ((3 : ℝ) / 25) * (646 * (P : ℝ) ^ (-(49 : ℝ) / 100)) :=
          mul_le_mul_of_nonneg_left hKU (Real.rpow_nonneg hP_pos.le _)
      _ = 646 * (P : ℝ) ^ (-(37 : ℝ) / 100) := by
          rw [mul_left_comm, ← Real.rpow_add hP_pos]; congr 2; norm_num
  have hS1_split : ∑ d ∈ Icc 1 U, g d * (d : ℝ) ^ (-s) * ∑ k ∈ Icc 1 (X / d), (k : ℝ) ^ (-s) =
      (∑ d ∈ Icc 1 U, g d * hsFun (X : ℝ) s (d : ℝ)) +
      gammaVal s * Lpartial g U s +
      ∑ d ∈ Icc 1 U, g d * (d : ℝ) ^ (-s) *
        (∑ k ∈ Icc 1 (X / d), (k : ℝ) ^ (-s) -
          ((((X : ℝ) / (d : ℝ)) ^ (1 - s) - 1) / (1 - s) + gammaVal s)) := by
    unfold Lpartial
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [Finset.mem_Icc] at hd
    have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hhs_eq : (d : ℝ) ^ (-s) * ((((X : ℝ) / (d : ℝ)) ^ (1 - s) - 1) / (1 - s)) =
        hsFun (X : ℝ) s (d : ℝ) := by
      unfold hsFun
      rw [Real.div_rpow (by positivity) hd_pos.le, div_eq_mul_inv ((X : ℝ) ^ (1 - s)),
        ← Real.rpow_neg hd_pos.le]
      have hd_comb : (d : ℝ) ^ (-s) * (d : ℝ) ^ (-(1 - s)) = (d : ℝ) ^ (-(1 : ℝ)) := by
        rw [← Real.rpow_add hd_pos]; congr 1; ring
      calc (d : ℝ) ^ (-s) * (((X : ℝ) ^ (1 - s) * (d : ℝ) ^ (-(1 - s)) - 1) / (1 - s))
          = ((X : ℝ) ^ (1 - s) * ((d : ℝ) ^ (-s) * (d : ℝ) ^ (-(1 - s))) - (d : ℝ) ^ (-s)) /
              (1 - s) := by ring
        _ = ((X : ℝ) ^ (1 - s) * (d : ℝ) ^ (-(1 : ℝ)) - (d : ℝ) ^ (-s)) / (1 - s) := by rw [hd_comb]
    calc g d * (d : ℝ) ^ (-s) * ∑ k ∈ Icc 1 (X / d), (k : ℝ) ^ (-s)
        = g d * ((d : ℝ) ^ (-s) * ((((X : ℝ) / (d : ℝ)) ^ (1 - s) - 1) / (1 - s))) +
          gammaVal s * (g d * (d : ℝ) ^ (-s)) +
          g d * (d : ℝ) ^ (-s) *
            (∑ k ∈ Icc 1 (X / d), (k : ℝ) ^ (-s) -
              ((((X : ℝ) / (d : ℝ)) ^ (1 - s) - 1) / (1 - s) + gammaVal s)) := by ring
      _ = _ := by rw [hhs_eq]
  have hE1 : ∑ d ∈ Icc 1 U, g d * (d : ℝ) ^ (-s) *
        (∑ k ∈ Icc 1 (X / d), (k : ℝ) ^ (-s) -
          ((((X : ℝ) / (d : ℝ)) ^ (1 - s) - 1) / (1 - s) + gammaVal s)) ≤ (1 : ℝ) / 64 := by
    calc ∑ d ∈ Icc 1 U, g d * (d : ℝ) ^ (-s) *
            (∑ k ∈ Icc 1 (X / d), (k : ℝ) ^ (-s) -
              ((((X : ℝ) / (d : ℝ)) ^ (1 - s) - 1) / (1 - s) + gammaVal s))
        ≤ ∑ d ∈ Icc 1 U, dconv (fun _ => 1) (dconv (fun _ => 1) (fun _ => 1)) d *
            (2 * (X : ℝ) ^ (-s)) := by
          refine Finset.sum_le_sum fun d hd => ?_
          simp only [Finset.mem_Icc] at hd
          have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
          have hY1 : (1 : ℝ) ≤ (X : ℝ) / (d : ℝ) := by
            rw [one_le_div hd_pos]; exact_mod_cast hd.2.trans hUX
          have hfl : Nat.floor ((X : ℝ) / (d : ℝ)) = X / d := Nat.floor_div_eq_div _ _
          have hem := sum_rpow_euler_maclaurin (by linarith) hs2 hY1
          rw [hfl] at hem
          have hdiv_pow : ((X : ℝ) / (d : ℝ)) ^ (-s) = (X : ℝ) ^ (-s) * (d : ℝ) ^ s := by
            rw [Real.div_rpow (by positivity) hd_pos.le, div_eq_mul_inv,
              ← Real.rpow_neg hd_pos.le, neg_neg]
          have htau3_nn : 0 ≤ dconv (fun _ => 1) (dconv (fun _ => 1) (fun _ => 1)) d :=
            (abs_nonneg _).trans (hg_abs d hd.1)
          refine (le_abs_self _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hd_pos.le _)]
          calc |g d| * (d : ℝ) ^ (-s) *
                |∑ k ∈ Icc 1 (X / d), (k : ℝ) ^ (-s) -
                  ((((X : ℝ) / (d : ℝ)) ^ (1 - s) - 1) / (1 - s) + gammaVal s)|
              ≤ dconv (fun _ => 1) (dconv (fun _ => 1) (fun _ => 1)) d * (d : ℝ) ^ (-s) *
                  (2 * ((X : ℝ) / (d : ℝ)) ^ (-s)) :=
                mul_le_mul (mul_le_mul_of_nonneg_right (hg_abs d hd.1) (Real.rpow_nonneg hd_pos.le _))
                  hem (abs_nonneg _) (mul_nonneg htau3_nn (Real.rpow_nonneg hd_pos.le _))
            _ = dconv (fun _ => 1) (dconv (fun _ => 1) (fun _ => 1)) d * (2 * (X : ℝ) ^ (-s)) *
                  ((d : ℝ) ^ (-s) * (d : ℝ) ^ s) := by rw [hdiv_pow]; ring
            _ = dconv (fun _ => 1) (dconv (fun _ => 1) (fun _ => 1)) d * (2 * (X : ℝ) ^ (-s)) := by
                rw [← Real.rpow_add hd_pos, neg_add_cancel, Real.rpow_zero, mul_one]
      _ = (∑ d ∈ Icc 1 U, dconv (fun _ => 1) (dconv (fun _ => 1) (fun _ => 1)) d) *
            (2 * (X : ℝ) ^ (-s)) := by rw [← Finset.sum_mul]
      _ ≤ ((U : ℝ) * (Real.log (U : ℝ) + 1) ^ 2) * (2 * (X : ℝ) ^ (-s)) :=
          mul_le_mul_of_nonneg_right (sum_tau3_le hU1) (by positivity)
      _ ≤ ((U : ℝ) * (5 * (U : ℝ) ^ ((1 : ℝ) / 10)) ^ 2) * (2 * (X : ℝ) ^ (-(49 : ℝ) / 50)) := by
          have hlogU : (Real.log (U : ℝ) + 1) ^ 2 ≤ (5 * (U : ℝ) ^ ((1 : ℝ) / 10)) ^ 2 := by
            have h1 := log_add_one_le_5_rpow (by exact_mod_cast hU1 : (1 : ℝ) ≤ (U : ℝ))
            have h0 : 0 ≤ Real.log (U : ℝ) + 1 := by
              linarith [Real.log_nonneg (by exact_mod_cast hU1 : (1 : ℝ) ≤ (U : ℝ))]
            nlinarith
          have hXs : (X : ℝ) ^ (-s) ≤ (X : ℝ) ^ (-(49 : ℝ) / 50) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (le_trans hU1 hUX)) (by linarith)
          exact mul_le_mul (mul_le_mul_of_nonneg_left hlogU hU_pos.le)
            (mul_le_mul_of_nonneg_left hXs (by norm_num)) (by positivity) (by positivity)
      _ = 50 * (P : ℝ) ^ (-(8 : ℝ) / 25) := by
          have hU12 : (U : ℝ) * (5 * (U : ℝ) ^ ((1 : ℝ) / 10)) ^ 2 = 25 * (P : ℝ) ^ ((18 : ℝ) / 5) := by
            have hsq : ((U : ℝ) ^ ((1 : ℝ) / 10)) ^ 2 = (U : ℝ) ^ ((1 : ℝ) / 5) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hU_pos.le]; congr 1; norm_num
            have hU65 : (U : ℝ) * (U : ℝ) ^ ((1 : ℝ) / 5) = (P : ℝ) ^ ((18 : ℝ) / 5) := by
              conv_lhs => arg 1; rw [← Real.rpow_one (U : ℝ)]
              rw [← Real.rpow_add hU_pos, hU_cast, ← Real.rpow_natCast, ← Real.rpow_mul hP_pos.le]
              congr 1; norm_num
            calc (U : ℝ) * (5 * (U : ℝ) ^ ((1 : ℝ) / 10)) ^ 2
                = 25 * ((U : ℝ) * ((U : ℝ) ^ ((1 : ℝ) / 10)) ^ 2) := by ring
              _ = 25 * ((U : ℝ) * (U : ℝ) ^ ((1 : ℝ) / 5)) := by rw [hsq]
              _ = 25 * (P : ℝ) ^ ((18 : ℝ) / 5) := by rw [hU65]
          have hXpow : (X : ℝ) ^ (-(49 : ℝ) / 50) = (P : ℝ) ^ (-(98 : ℝ) / 25) := by
            rw [hX_cast, ← Real.rpow_natCast, ← Real.rpow_mul hP_pos.le]; congr 1; norm_num
          rw [hU12, hXpow]
          calc 25 * (P : ℝ) ^ ((18 : ℝ) / 5) * (2 * (P : ℝ) ^ (-(98 : ℝ) / 25))
              = 50 * ((P : ℝ) ^ ((18 : ℝ) / 5) * (P : ℝ) ^ (-(98 : ℝ) / 25)) := by ring
            _ = 50 * (P : ℝ) ^ (-(8 : ℝ) / 25) := by
                rw [← Real.rpow_add hP_pos]; congr 2; norm_num
      _ ≤ 50 * (2 : ℝ) ^ (-19 : ℤ) :=
          mul_le_mul_of_nonneg_left (rpow_neg_le_two_pow hP_rbig (by norm_num) (by norm_num)) (by norm_num)
      _ ≤ (1 : ℝ) / 64 := by norm_num
  have hE2 : |gammaVal s * (Lpartial g U s - Ls)| ≤ (1 : ℝ) / 64 := by
    have htail_g : |Ls - Lpartial g U s| ≤ 5 * K * (U : ℝ) ^ ((7 : ℝ) / 10 - s) := by
      have hlim_rhs : Tendsto (fun Q : ℕ =>
          K * ((Q : ℝ) ^ ((7 : ℝ) / 10 - s) + 5 * (U : ℝ) ^ ((7 : ℝ) / 10 - s)))
          atTop (nhds (5 * K * (U : ℝ) ^ ((7 : ℝ) / 10 - s))) := by
        have hq : Tendsto (fun Q : ℕ => (Q : ℝ) ^ ((7 : ℝ) / 10 - s)) atTop (nhds 0) := by
          have h0 := rpow_neg_tendsto_zero (by linarith : 0 < s - (7 : ℝ) / 10)
          refine (h0.comp (tendsto_sub_atTop_nat 1)).congr' ?_
          filter_upwards [Filter.eventually_ge_atTop 1] with Q hQ
          simp only [Function.comp_apply, Nat.sub_add_cancel hQ]
          congr 1; ring
        have hq' := (hq.add_const (5 * (U : ℝ) ^ ((7 : ℝ) / 10 - s))).const_mul K
        simpa [mul_comm, mul_assoc, mul_left_comm] using hq'
      refine le_of_tendsto_of_tendsto ((hlims.sub_const _).abs) hlim_rhs ?_
      filter_upwards [Filter.eventually_gt_atTop U] with Q hUQ
      rw [Lpartial_sub_eq g s hUQ]
      exact abel_pow_tail_bound hK_nn hG_bound hs1 hU1 hUQ
    obtain ⟨hg0, hg1⟩ := gammaVal_bounds (by linarith : 0 < s)
    rw [abs_mul, abs_of_nonneg hg0, abs_sub_comm]
    calc gammaVal s * |Ls - Lpartial g U s|
        ≤ 1 * (5 * K * (U : ℝ) ^ ((7 : ℝ) / 10 - s)) :=
          mul_le_mul hg1 htail_g (abs_nonneg _) zero_le_one
      _ = 5 * (K * (U : ℝ) ^ ((7 : ℝ) / 10 - s)) := by ring
      _ ≤ 5 * (646 * (P : ℝ) ^ (-(49 : ℝ) / 100)) :=
          mul_le_mul_of_nonneg_left hKU (by norm_num)
      _ = 3230 * (P : ℝ) ^ (-(49 : ℝ) / 100) := by ring
      _ ≤ 3230 * (2 : ℝ) ^ (-29 : ℤ) :=
          mul_le_mul_of_nonneg_left (rpow_neg_le_two_pow hP_rbig (by norm_num) (by norm_num)) (by norm_num)
      _ ≤ (1 : ℝ) / 64 := by norm_num
  have hE3 : ∑ k ∈ Icc 1 P, (k : ℝ) ^ (-s) * ∑ d ∈ Icc (U + 1) (X / k), g d * (d : ℝ) ^ (-s) ≤
      (1 : ℝ) / 64 := by
    have hinner : ∀ k ∈ Icc 1 P,
        |∑ d ∈ Icc (U + 1) (X / k), g d * (d : ℝ) ^ (-s)| ≤ 6 * K * (U : ℝ) ^ ((7 : ℝ) / 10 - s) := by
      intro k _
      by_cases hk : U < X / k
      · have hb := abel_pow_tail_bound hK_nn hG_bound hs1 hU1 hk
        have hQ_le : ((X / k : ℕ) : ℝ) ^ ((7 : ℝ) / 10 - s) ≤ (U : ℝ) ^ ((7 : ℝ) / 10 - s) :=
          Real.rpow_le_rpow_of_nonpos hU_pos (by exact_mod_cast hk.le) (by linarith)
        exact hb.trans (by
          calc K * (((X / k : ℕ) : ℝ) ^ ((7 : ℝ) / 10 - s) + 5 * (U : ℝ) ^ ((7 : ℝ) / 10 - s))
              ≤ K * ((U : ℝ) ^ ((7 : ℝ) / 10 - s) + 5 * (U : ℝ) ^ ((7 : ℝ) / 10 - s)) :=
                mul_le_mul_of_nonneg_left (by linarith) hK_nn
            _ = 6 * K * (U : ℝ) ^ ((7 : ℝ) / 10 - s) := by ring)
      · have hemp : Icc (U + 1) (X / k) = ∅ := Finset.Icc_eq_empty (by omega)
        rw [hemp, Finset.sum_empty, abs_zero]; positivity
    calc ∑ k ∈ Icc 1 P, (k : ℝ) ^ (-s) * ∑ d ∈ Icc (U + 1) (X / k), g d * (d : ℝ) ^ (-s)
        ≤ ∑ k ∈ Icc 1 P, (k : ℝ) ^ (-s) * (6 * K * (U : ℝ) ^ ((7 : ℝ) / 10 - s)) :=
          Finset.sum_le_sum fun k hk =>
            mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hinner k hk))
              (Real.rpow_nonneg (by positivity) _)
      _ = (∑ k ∈ Icc 1 P, (k : ℝ) ^ (-s)) * (6 * K * (U : ℝ) ^ ((7 : ℝ) / 10 - s)) := by
          rw [← Finset.sum_mul]
      _ ≤ ((P : ℝ) ^ (1 - s) * (Real.log (P : ℝ) + 1)) * (6 * K * (U : ℝ) ^ ((7 : ℝ) / 10 - s)) :=
          mul_le_mul_of_nonneg_right (sum_rpow_neg_le hs2.le (by omega)) (by positivity)
      _ ≤ ((P : ℝ) ^ ((1 : ℝ) / 50) * (5 * (P : ℝ) ^ ((1 : ℝ) / 10))) *
            (6 * K * (U : ℝ) ^ ((7 : ℝ) / 10 - s)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul
            (Real.rpow_le_rpow_of_exponent_le hP_ge1 (by linarith))
            (log_add_one_le_5_rpow hP_ge1)
            (by linarith [Real.log_nonneg hP_ge1])
            (Real.rpow_nonneg hP_pos.le _)
      _ = 30 * (K * (P : ℝ) ^ ((3 : ℝ) / 25) * (U : ℝ) ^ ((7 : ℝ) / 10 - s)) := by
          have hP325 : (P : ℝ) ^ ((1 : ℝ) / 50) * (P : ℝ) ^ ((1 : ℝ) / 10) =
              (P : ℝ) ^ ((3 : ℝ) / 25) := by
            rw [← Real.rpow_add hP_pos]; congr 1; norm_num
          calc (P : ℝ) ^ ((1 : ℝ) / 50) * (5 * (P : ℝ) ^ ((1 : ℝ) / 10)) *
                (6 * K * (U : ℝ) ^ ((7 : ℝ) / 10 - s))
              = 30 * (K * ((P : ℝ) ^ ((1 : ℝ) / 50) * (P : ℝ) ^ ((1 : ℝ) / 10)) *
                  (U : ℝ) ^ ((7 : ℝ) / 10 - s)) := by ring
            _ = _ := by rw [hP325]
      _ ≤ 30 * (646 * (P : ℝ) ^ (-(37 : ℝ) / 100)) :=
          mul_le_mul_of_nonneg_left hKPU (by norm_num)
      _ = 19380 * (P : ℝ) ^ (-(37 : ℝ) / 100) := by ring
      _ ≤ 19380 * (2 : ℝ) ^ (-22 : ℤ) :=
          mul_le_mul_of_nonneg_left (rpow_neg_le_two_pow hP_rbig (by norm_num) (by norm_num)) (by norm_num)
      _ ≤ (1 : ℝ) / 64 := by norm_num
  have hE4 : |(((X : ℝ) ^ (1 - s) / (1 - s)) * L1 - (1 / (1 - s)) * Ls) -
      ∑ d ∈ Icc 1 U, g d * hsFun (X : ℝ) s (d : ℝ)| ≤ (1 : ℝ) / 64 := by
    have htb : |(((X : ℝ) ^ (1 - s) / (1 - s)) * L1 - (1 / (1 - s)) * Ls) -
        ∑ d ∈ Icc 1 U, g d * hsFun (X : ℝ) s (d : ℝ)| ≤
        54 * K * (P : ℝ) ^ ((3 : ℝ) / 25) * (U : ℝ) ^ ((7 : ℝ) / 10 - s) :=
      abel_hs_tail_bound hK_nn (by omega : 2 ≤ P) hG_bound hs1 hs2 hlim1 hlims
    calc |(((X : ℝ) ^ (1 - s) / (1 - s)) * L1 - (1 / (1 - s)) * Ls) -
            ∑ d ∈ Icc 1 U, g d * hsFun (X : ℝ) s (d : ℝ)|
        ≤ 54 * (K * (P : ℝ) ^ ((3 : ℝ) / 25) * (U : ℝ) ^ ((7 : ℝ) / 10 - s)) :=
          htb.trans_eq (by ring)
      _ ≤ 54 * (646 * (P : ℝ) ^ (-(37 : ℝ) / 100)) :=
          mul_le_mul_of_nonneg_left hKPU (by norm_num)
      _ = 34884 * (P : ℝ) ^ (-(37 : ℝ) / 100) := by ring
      _ ≤ 34884 * (2 : ℝ) ^ (-22 : ℤ) :=
          mul_le_mul_of_nonneg_left (rpow_neg_le_two_pow hP_rbig (by norm_num) (by norm_num)) (by norm_num)
      _ ≤ (1 : ℝ) / 64 := by norm_num
  have hzeta_eq : (((X : ℝ) ^ (1 - s) / (1 - s)) * L1 - (1 / (1 - s)) * Ls) +
      gammaVal s * Ls =
      ((X : ℝ) ^ (1 - s) / (1 - s)) * L1 + zetaVal s * Ls := by
    unfold zetaVal; ring
  have hE4_lo : ∑ d ∈ Icc 1 U, g d * hsFun (X : ℝ) s (d : ℝ) ≤
      (((X : ℝ) ^ (1 - s) / (1 - s)) * L1 - (1 / (1 - s)) * Ls) + (1 : ℝ) / 64 := by
    linarith only [abs_le.mp hE4]
  have hE2_lo : gammaVal s * Lpartial g U s ≤ gammaVal s * Ls + (1 : ℝ) / 64 := by
    have hdiff : gammaVal s * Lpartial g U s - gammaVal s * Ls =
        gammaVal s * (Lpartial g U s - Ls) := by ring
    linarith only [abs_le.mp hE2, hdiff]
  have h1 : (1 : ℝ) ≤ (∑ d ∈ Icc 1 U, g d * hsFun (X : ℝ) s (d : ℝ)) +
      gammaVal s * Lpartial g U s +
      (∑ d ∈ Icc 1 U, g d * (d : ℝ) ^ (-s) *
        (∑ k ∈ Icc 1 (X / d), (k : ℝ) ^ (-s) -
          ((((X : ℝ) / (d : ℝ)) ^ (1 - s) - 1) / (1 - s) + gammaVal s))) +
      ∑ k ∈ Icc 1 P, (k : ℝ) ^ (-s) * ∑ d ∈ Icc (U + 1) (X / k), g d * (d : ℝ) ^ (-s) := by
    have h := hsum_ge1
    rw [hhyp, hS1_split] at h
    exact h
  linarith only [h1, hE1, hE2_lo, hE3, hE4_lo, hzeta_eq]

private lemma step2_hyperbola_bound {m₁ m₂ y₁ y₂ : ℕ}
    (hy₁ : 4102 ≤ y₁) (hm₁ : m₁ + 2 = (4 * y₁) ^ 2) (hsq₁ : Squarefree m₁)
    (hy₂ : 4102 ≤ y₂) (hm₂ : m₂ + 2 = (4 * y₂) ^ 2) (hsq₂ : Squarefree m₂)
    (hne : m₁ ≠ m₂) {s : ℝ} (hs1 : (49 : ℝ) / 50 ≤ s) (hs2 : s < 1) :
    let hm₁_pos : 0 < m₁ := by nlinarith
    let hm₂_pos : 0 < m₂ := by nlinarith
    let P : ℕ := (4 * m₁) * (4 * m₂)
    let χ₁ := chiRe (quadChar m₁ hm₁_pos)
    let χ₂ := chiRe (quadChar m₂ hm₂_pos)
    let χ₃ := chiRe (prodPrimChar hm₁_pos hm₂_pos).2
    (1 : ℝ) ≤ (((P ^ 4 : ℕ) : ℝ) ^ (1 - s) / (1 - s)) * (Lval χ₁ 1 * Lval χ₂ 1 * Lval χ₃ 1) +
      zetaVal s * (Lval χ₁ s * Lval χ₂ s * Lval χ₃ s) + (1 : ℝ) / 16 := by
  have hm₁_pos : 0 < m₁ := by nlinarith
  have hm₂_pos : 0 < m₂ := by nlinarith
  have hm₁4 : m₁ % 4 = 2 := by
    have : m₁ + 2 = 16 * y₁ ^ 2 := by linarith
    omega
  have hm₂4 : m₂ % 4 = 2 := by
    have : m₂ + 2 = 16 * y₂ ^ 2 := by linarith
    omega
  set D₁ : ℕ := 4 * m₁
  set D₂ : ℕ := 4 * m₂
  set D₃ : ℕ := (prodPrimChar hm₁_pos hm₂_pos).1
  set P : ℕ := D₁ * D₂
  have hD₁_big : 2 ^ 30 ≤ D₁ := by
    have h1 : D₁ + 8 = 64 * y₁ ^ 2 := by dsimp [D₁]; linarith
    have h2 : 64 * 4102 ^ 2 ≤ 64 * y₁ ^ 2 := by nlinarith
    omega
  have hD₂_big : 2 ^ 30 ≤ D₂ := by
    have h1 : D₂ + 8 = 64 * y₂ ^ 2 := by dsimp [D₂]; linarith
    have h2 : 64 * 4102 ^ 2 ≤ 64 * y₂ ^ 2 := by nlinarith
    omega
  have hP_big : 2 ^ 60 ≤ P := by
    calc 2 ^ 60 = 2 ^ 30 * 2 ^ 30 := by norm_num
      _ ≤ D₁ * D₂ := Nat.mul_le_mul hD₁_big hD₂_big
  have hP_pos : (0 : ℝ) < (P : ℝ) := by positivity
  obtain ⟨hD₃_gt1, hD₃_le, hprim₃, hreal₃, _⟩ := prodPrimChar_spec hm₁_pos hm₂_pos hm₁4 hm₂4 hsq₁ hsq₂ hne
  have hD₃_le_P : D₃ ≤ P := by
    have : P = 4 * (4 * m₁ * m₂) := by dsimp [P, D₁, D₂]; ring
    omega
  let _ : NeZero D₁ := ⟨by omega⟩
  let _ : NeZero D₂ := ⟨by omega⟩
  let _ : NeZero D₃ := ⟨by omega⟩
  have hprim₁ : (quadChar m₁ hm₁_pos).IsPrimitive := quadChar_isPrimitive hm₁_pos hm₁4 hsq₁
  have hprim₂ : (quadChar m₂ hm₂_pos).IsPrimitive := quadChar_isPrimitive hm₂_pos hm₂4 hsq₂
  set χ₁ := chiRe (quadChar m₁ hm₁_pos)
  set χ₂ := chiRe (quadChar m₂ hm₂_pos)
  set χ₃ := chiRe (prodPrimChar hm₁_pos hm₂_pos).2
  set M₁ : ℝ := Real.sqrt (D₁ : ℝ) * (Real.log (D₁ : ℝ) + 1)
  set M₂ : ℝ := Real.sqrt (D₂ : ℝ) * (Real.log (D₂ : ℝ) + 1)
  set M₃ : ℝ := Real.sqrt (D₃ : ℝ) * (Real.log (D₃ : ℝ) + 1)
  have hM_ge1 : ∀ N : ℕ, 2 ≤ N → (1 : ℝ) ≤ Real.sqrt (N : ℝ) * (Real.log (N : ℝ) + 1) := by
    intro N hN
    have h1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
      rw [Real.le_sqrt zero_le_one (by positivity)]; exact_mod_cast (by omega : 1 ≤ N)
    have h2 : (1 : ℝ) ≤ Real.log (N : ℝ) + 1 := by
      linarith [Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N) : (1 : ℝ) ≤ (N : ℝ))]
    nlinarith
  have hM₁_ge1 : 1 ≤ M₁ := hM_ge1 D₁ (by omega)
  have hM₂_ge1 : 1 ≤ M₂ := hM_ge1 D₂ (by omega)
  have hM₃_ge1 : 1 ≤ M₃ := hM_ge1 D₃ (by omega)
  have hχ₁_pv : ∀ a b, |∑ n ∈ Icc a b, χ₁ n| ≤ M₁ := polya_vinogradov_re (by omega) hprim₁
  have hχ₂_pv : ∀ a b, |∑ n ∈ Icc a b, χ₂ n| ≤ M₂ := polya_vinogradov_re (by omega) hprim₂
  have hχ₃_pv : ∀ a b, |∑ n ∈ Icc a b, χ₃ n| ≤ M₃ := polya_vinogradov_re hD₃_gt1 hprim₃
  have hχ₁1 : ∀ n, |χ₁ n| ≤ 1 := abs_chiRe_le_one (quadChar_isReal hm₁_pos)
  have hχ₂1 : ∀ n, |χ₂ n| ≤ 1 := abs_chiRe_le_one (quadChar_isReal hm₂_pos)
  have hχ₃1 : ∀ n, |χ₃ n| ≤ 1 := abs_chiRe_le_one hreal₃
  have hM_rpow : ∀ N : ℕ, 1 ≤ N →
      Real.sqrt (N : ℝ) * (Real.log (N : ℝ) + 1) ≤ 17 * (N : ℝ) ^ ((21 : ℝ) / 40) := by
    intro N hN
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    rw [Real.sqrt_eq_rpow]
    calc (N : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (N : ℝ) + 1)
        ≤ (N : ℝ) ^ ((1 : ℝ) / 2) * (17 * (N : ℝ) ^ ((1 : ℝ) / 40)) :=
          mul_le_mul_of_nonneg_left (log_add_one_le_17_rpow (by exact_mod_cast hN))
            (Real.rpow_nonneg hN_pos.le _)
      _ = 17 * (N : ℝ) ^ ((21 : ℝ) / 40) := by
          rw [mul_left_comm, ← Real.rpow_add hN_pos]; congr 2; norm_num
  have hG_bound : ∀ n : ℕ, 1 ≤ n →
      |∑ k ∈ Icc 1 n, dconv χ₁ (dconv χ₂ χ₃) k| ≤
        (646 * (P : ℝ) ^ ((7 : ℝ) / 20)) * (n : ℝ) ^ ((7 : ℝ) / 10) := by
    intro n hn
    have hb := partial_sum_dconv3_le hM₁_ge1 hM₂_ge1 hM₃_ge1 hχ₁_pv hχ₂_pv hχ₃_pv hχ₁1 hχ₂1 hχ₃1 hn
    refine hb.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _))
    have hMprod : M₁ * M₂ * M₃ ≤ (17 : ℝ) ^ (3 : ℕ) * (P : ℝ) ^ ((21 : ℝ) / 20) := by
      have h1 := hM_rpow D₁ (by omega)
      have h2 := hM_rpow D₂ (by omega)
      have h3 : M₃ ≤ 17 * (P : ℝ) ^ ((21 : ℝ) / 40) :=
        (hM_rpow D₃ (by omega)).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hD₃_le_P) (by norm_num)) (by norm_num))
      have h12 : M₁ * M₂ ≤ (17 * (D₁ : ℝ) ^ ((21 : ℝ) / 40)) * (17 * (D₂ : ℝ) ^ ((21 : ℝ) / 40)) :=
        mul_le_mul h1 h2 (by linarith) (by positivity)
      calc M₁ * M₂ * M₃
          ≤ ((17 * (D₁ : ℝ) ^ ((21 : ℝ) / 40)) * (17 * (D₂ : ℝ) ^ ((21 : ℝ) / 40))) *
              (17 * (P : ℝ) ^ ((21 : ℝ) / 40)) := mul_le_mul h12 h3 (by linarith) (by positivity)
        _ = (17 : ℝ) ^ (3 : ℕ) * ((P : ℝ) ^ ((21 : ℝ) / 40) * (P : ℝ) ^ ((21 : ℝ) / 40)) := by
            have hD12 : (D₁ : ℝ) ^ ((21 : ℝ) / 40) * (D₂ : ℝ) ^ ((21 : ℝ) / 40) =
                (P : ℝ) ^ ((21 : ℝ) / 40) := by
              rw [← Real.mul_rpow (by positivity) (by positivity)]; push_cast [P]; rfl
            calc 17 * (D₁ : ℝ) ^ ((21 : ℝ) / 40) * (17 * (D₂ : ℝ) ^ ((21 : ℝ) / 40)) *
                  (17 * (P : ℝ) ^ ((21 : ℝ) / 40))
                = (17 : ℝ) ^ (3 : ℕ) * (((D₁ : ℝ) ^ ((21 : ℝ) / 40) * (D₂ : ℝ) ^ ((21 : ℝ) / 40)) *
                    (P : ℝ) ^ ((21 : ℝ) / 40)) := by ring
              _ = _ := by rw [hD12]
        _ = (17 : ℝ) ^ (3 : ℕ) * (P : ℝ) ^ ((21 : ℝ) / 20) := by
            rw [← Real.rpow_add hP_pos]; congr 2; norm_num
    calc 38 * (M₁ * M₂ * M₃) ^ ((1 : ℝ) / 3)
        ≤ 38 * ((17 : ℝ) ^ (3 : ℕ) * (P : ℝ) ^ ((21 : ℝ) / 20)) ^ ((1 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hMprod (by norm_num)) (by norm_num)
      _ = 646 * (P : ℝ) ^ ((7 : ℝ) / 20) := by
          rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hP_pos.le _),
            ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul hP_pos.le]
          have h1 : ((3 : ℕ) : ℝ) * ((1 : ℝ) / 3) = 1 := by norm_num
          have h2 : (21 : ℝ) / 20 * ((1 : ℝ) / 3) = (7 : ℝ) / 20 := by norm_num
          rw [h1, h2, Real.rpow_one]; ring
  have hg_abs : ∀ d : ℕ, 1 ≤ d →
      |dconv χ₁ (dconv χ₂ χ₃) d| ≤ dconv (fun _ => 1) (dconv (fun _ => 1) (fun _ => 1)) d :=
    fun d hd => abs_dconv_le (fun n _ => hχ₁1 n)
      (fun n hn => abs_dconv_le (fun k _ => hχ₂1 k) (fun k _ => hχ₃1 k) hn) hd
  have hf_spec := four_conv_nonneg hm₁_pos hm₂_pos hm₁4 hm₂4 hsq₁ hsq₂ hne
  exact step2_hyperbola_core hP_big hs1 hs2 hG_bound hg_abs hf_spec.1 hf_spec.2
    (tendsto_Lpartial_dconv3 hM₁_ge1 hM₂_ge1 hM₃_ge1 hχ₁_pv hχ₂_pv hχ₃_pv hχ₁1 hχ₂1 hχ₃1
      (by norm_num) le_rfl)
    (tendsto_Lpartial_dconv3 hM₁_ge1 hM₂_ge1 hM₃_ge1 hχ₁_pv hχ₂_pv hχ₃_pv hχ₁1 hχ₂1 hχ₃1
      hs1 hs2.le)

private lemma Lderiv_bound_of_P {χ : ℕ → ℝ} {M : ℝ} {P : ℕ}
    (hP_big : 2 ^ 60 ≤ P) (hM_nn : 0 ≤ M)
    (hM_le : M ≤ Real.sqrt (P : ℝ) * (Real.log (P : ℝ) + 1))
    (hχ_pv : ∀ a b, |∑ n ∈ Icc a b, χ n| ≤ M) (hχ1 : ∀ n, |χ n| ≤ 1)
    {ξ : ℝ} (hξ1 : (49 : ℝ) / 50 ≤ ξ) (hξ2 : ξ ≤ 1) :
    |Lderiv χ ξ| ≤ 578 * (P : ℝ) ^ ((3 : ℝ) / 50) := by
  have hP_pos : (0 : ℝ) < (P : ℝ) := by positivity
  have hP_ge1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast (by omega : 1 ≤ P)
  set N₀ : ℕ := Nat.sqrt P
  have hN₀_ge4 : 4 ≤ N₀ := Nat.le_sqrt.mpr (by omega)
  have hN₀_le_sq : (N₀ : ℝ) ≤ Real.sqrt (P : ℝ) := by
    rw [Real.le_sqrt (by positivity) hP_pos.le, sq]; exact_mod_cast Nat.sqrt_le P
  have hsq_lt_N₀1 : Real.sqrt (P : ℝ) < ((N₀ + 1 : ℕ) : ℝ) := by
    rw [Real.sqrt_lt' (by positivity), sq]; exact_mod_cast Nat.lt_succ_sqrt P
  have hN₀1_le_P : ((N₀ + 1 : ℕ) : ℝ) ≤ (P : ℝ) := by
    have h1 : N₀ + 1 ≤ P := by
      have : N₀ * N₀ ≤ P := Nat.sqrt_le P
      nlinarith
    exact_mod_cast h1
  have hb := abs_Lderiv_le hM_nn hχ_pv hχ1 hξ1 hξ2 hN₀_ge4
  have hN₀_rpow : (N₀ : ℝ) ^ (1 - ξ) ≤ (P : ℝ) ^ ((1 : ℝ) / 100) := by
    calc (N₀ : ℝ) ^ (1 - ξ) ≤ (Real.sqrt (P : ℝ)) ^ (1 - ξ) :=
          Real.rpow_le_rpow (by positivity) hN₀_le_sq (by linarith)
      _ = (P : ℝ) ^ ((1 - ξ) / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hP_pos.le]; congr 1; ring
      _ ≤ (P : ℝ) ^ ((1 : ℝ) / 100) :=
          Real.rpow_le_rpow_of_exponent_le hP_ge1 (by linarith)
  have hN₀1_rpow : ((N₀ + 1 : ℕ) : ℝ) ^ (-ξ) ≤ (P : ℝ) ^ (-ξ / 2) := by
    calc ((N₀ + 1 : ℕ) : ℝ) ^ (-ξ) ≤ (Real.sqrt (P : ℝ)) ^ (-ξ) :=
          Real.rpow_le_rpow_of_nonpos (Real.sqrt_pos.mpr hP_pos) hsq_lt_N₀1.le (by linarith)
      _ = (P : ℝ) ^ (-ξ / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hP_pos.le]; congr 1; ring
  have hlogN₀ : Real.log (N₀ : ℝ) ≤ Real.log (P : ℝ) :=
    Real.log_le_log (by positivity) (hN₀_le_sq.trans (by rw [Real.sqrt_le_left hP_pos.le]; nlinarith))
  have hlogN₀1 : Real.log ((N₀ + 1 : ℕ) : ℝ) ≤ Real.log (P : ℝ) :=
    Real.log_le_log (by positivity) hN₀1_le_P
  have hlog_nn : 0 ≤ Real.log (P : ℝ) := Real.log_nonneg hP_ge1
  have ht1 : (N₀ : ℝ) ^ (1 - ξ) * Real.log (N₀ : ℝ) * (Real.log (N₀ : ℝ) + 1) ≤
      (P : ℝ) ^ ((1 : ℝ) / 100) * (Real.log (P : ℝ) + 1) ^ 2 := by
    have h0 : 0 ≤ Real.log (N₀ : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N₀))
    have h1 : Real.log (N₀ : ℝ) * (Real.log (N₀ : ℝ) + 1) ≤ (Real.log (P : ℝ) + 1) ^ 2 := by
      nlinarith only [h0, hlogN₀, hlog_nn]
    calc (N₀ : ℝ) ^ (1 - ξ) * Real.log (N₀ : ℝ) * (Real.log (N₀ : ℝ) + 1)
        = (N₀ : ℝ) ^ (1 - ξ) * (Real.log (N₀ : ℝ) * (Real.log (N₀ : ℝ) + 1)) := by ring
      _ ≤ (P : ℝ) ^ ((1 : ℝ) / 100) * (Real.log (P : ℝ) + 1) ^ 2 :=
          mul_le_mul hN₀_rpow h1 (by positivity) (Real.rpow_nonneg hP_pos.le _)
  have ht2 : M * Real.log ((N₀ + 1 : ℕ) : ℝ) * ((N₀ + 1 : ℕ) : ℝ) ^ (-ξ) ≤
      (P : ℝ) ^ ((1 : ℝ) / 100) * (Real.log (P : ℝ) + 1) ^ 2 := by
    have hM_comb : Real.sqrt (P : ℝ) * (P : ℝ) ^ (-ξ / 2) ≤ (P : ℝ) ^ ((1 : ℝ) / 100) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hP_pos]
      exact Real.rpow_le_rpow_of_exponent_le hP_ge1 (by linarith)
    have hlog1_nn : 0 ≤ Real.log ((N₀ + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N₀ + 1))
    calc M * Real.log ((N₀ + 1 : ℕ) : ℝ) * ((N₀ + 1 : ℕ) : ℝ) ^ (-ξ)
        ≤ (Real.sqrt (P : ℝ) * (Real.log (P : ℝ) + 1)) * (Real.log (P : ℝ) + 1) *
            (P : ℝ) ^ (-ξ / 2) := by
          exact mul_le_mul (mul_le_mul hM_le (by linarith only [hlogN₀1]) hlog1_nn (by positivity))
            hN₀1_rpow (Real.rpow_nonneg (by positivity) _) (by positivity)
      _ = (Real.sqrt (P : ℝ) * (P : ℝ) ^ (-ξ / 2)) * (Real.log (P : ℝ) + 1) ^ 2 := by ring
      _ ≤ (P : ℝ) ^ ((1 : ℝ) / 100) * (Real.log (P : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right hM_comb (sq_nonneg _)
  calc |Lderiv χ ξ| ≤ 2 * (P : ℝ) ^ ((1 : ℝ) / 100) * (Real.log (P : ℝ) + 1) ^ 2 := by
        linarith only [hb, ht1, ht2]
    _ ≤ 2 * (P : ℝ) ^ ((1 : ℝ) / 100) * (17 * (P : ℝ) ^ ((1 : ℝ) / 40)) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h1 := log_add_one_le_17_rpow hP_ge1
        nlinarith only [h1, hlog_nn]
    _ = 578 * (P : ℝ) ^ ((3 : ℝ) / 50) := by
        have hsq : ((P : ℝ) ^ ((1 : ℝ) / 40)) ^ 2 = (P : ℝ) ^ ((1 : ℝ) / 20) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hP_pos.le]; congr 1; norm_num
        calc 2 * (P : ℝ) ^ ((1 : ℝ) / 100) * (17 * (P : ℝ) ^ ((1 : ℝ) / 40)) ^ 2
            = 578 * ((P : ℝ) ^ ((1 : ℝ) / 100) * ((P : ℝ) ^ ((1 : ℝ) / 40)) ^ 2) := by ring
          _ = 578 * ((P : ℝ) ^ ((1 : ℝ) / 100) * (P : ℝ) ^ ((1 : ℝ) / 20)) := by rw [hsq]
          _ = 578 * (P : ℝ) ^ ((3 : ℝ) / 50) := by
              rw [← Real.rpow_add hP_pos]; congr 2; norm_num

private lemma two_solutions_false {m₁ m₂ y₁ y₂ : ℕ}
    (hy₁ : 4102 ≤ y₁) (hm₁ : m₁ + 2 = (4 * y₁) ^ 2) (hsq₁ : Squarefree m₁)
    (hpid₁ : IsPrincipalIdealRing (Zsqrtd (m₁ : ℤ)))
    (hy₂ : 4102 ≤ y₂) (hm₂ : m₂ + 2 = (4 * y₂) ^ 2) (hsq₂ : Squarefree m₂)
    (hpid₂ : IsPrincipalIdealRing (Zsqrtd (m₂ : ℤ)))
    (hne : m₁ ≠ m₂) : False := by
  have hm₁_pos : 0 < m₁ := by nlinarith
  have hm₂_pos : 0 < m₂ := by nlinarith
  have hm₁4 : m₁ % 4 = 2 := by
    have : m₁ + 2 = 16 * y₁ ^ 2 := by linarith
    omega
  have hm₂4 : m₂ % 4 = 2 := by
    have : m₂ + 2 = 16 * y₂ ^ 2 := by linarith
    omega
  set D₁ : ℕ := 4 * m₁
  set D₂ : ℕ := 4 * m₂
  set D₃ : ℕ := (prodPrimChar hm₁_pos hm₂_pos).1
  set P : ℕ := D₁ * D₂
  have hD₁_big : 2 ^ 30 ≤ D₁ := by
    have h1 : D₁ + 8 = 64 * y₁ ^ 2 := by dsimp [D₁]; linarith
    have h2 : 64 * 4102 ^ 2 ≤ 64 * y₁ ^ 2 := by nlinarith
    omega
  have hD₂_big : 2 ^ 30 ≤ D₂ := by
    have h1 : D₂ + 8 = 64 * y₂ ^ 2 := by dsimp [D₂]; linarith
    have h2 : 64 * 4102 ^ 2 ≤ 64 * y₂ ^ 2 := by nlinarith
    omega
  have hP_big : 2 ^ 60 ≤ P := by
    calc 2 ^ 60 = 2 ^ 30 * 2 ^ 30 := by norm_num
      _ ≤ D₁ * D₂ := Nat.mul_le_mul hD₁_big hD₂_big
  have hP_rbig : (2 : ℝ) ^ (60 : ℕ) ≤ (P : ℝ) := by exact_mod_cast hP_big
  have hP_pos : (0 : ℝ) < (P : ℝ) := by positivity
  have hP_ge1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast (by omega : 1 ≤ P)
  obtain ⟨hD₃_gt1, hD₃_le, hprim₃, hreal₃, _⟩ := prodPrimChar_spec hm₁_pos hm₂_pos hm₁4 hm₂4 hsq₁ hsq₂ hne
  have hD₃_le_P : D₃ ≤ P := by
    have : P = 4 * (4 * m₁ * m₂) := by dsimp [P, D₁, D₂]; ring
    omega
  let _ : NeZero D₁ := ⟨by omega⟩
  let _ : NeZero D₂ := ⟨by omega⟩
  let _ : NeZero D₃ := ⟨by omega⟩
  have hprim₁ : (quadChar m₁ hm₁_pos).IsPrimitive := quadChar_isPrimitive hm₁_pos hm₁4 hsq₁
  have hprim₂ : (quadChar m₂ hm₂_pos).IsPrimitive := quadChar_isPrimitive hm₂_pos hm₂4 hsq₂
  set χ₁ := chiRe (quadChar m₁ hm₁_pos)
  set χ₂ := chiRe (quadChar m₂ hm₂_pos)
  set χ₃ := chiRe (prodPrimChar hm₁_pos hm₂_pos).2
  set M₁ : ℝ := Real.sqrt (D₁ : ℝ) * (Real.log (D₁ : ℝ) + 1)
  set M₂ : ℝ := Real.sqrt (D₂ : ℝ) * (Real.log (D₂ : ℝ) + 1)
  set M₃ : ℝ := Real.sqrt (D₃ : ℝ) * (Real.log (D₃ : ℝ) + 1)
  have hM_nn : ∀ N : ℕ, 1 ≤ N → 0 ≤ Real.sqrt (N : ℝ) * (Real.log (N : ℝ) + 1) := fun N hN =>
    mul_nonneg (Real.sqrt_nonneg _) (by linarith [Real.log_nonneg (by exact_mod_cast hN : (1 : ℝ) ≤ (N : ℝ))])
  have hM₁_nn : 0 ≤ M₁ := hM_nn D₁ (by omega)
  have hM₂_nn : 0 ≤ M₂ := hM_nn D₂ (by omega)
  have hM₃_nn : 0 ≤ M₃ := hM_nn D₃ (by omega)
  have hχ₁_pv : ∀ a b, |∑ n ∈ Icc a b, χ₁ n| ≤ M₁ := polya_vinogradov_re (by omega) hprim₁
  have hχ₂_pv : ∀ a b, |∑ n ∈ Icc a b, χ₂ n| ≤ M₂ := polya_vinogradov_re (by omega) hprim₂
  have hχ₃_pv : ∀ a b, |∑ n ∈ Icc a b, χ₃ n| ≤ M₃ := polya_vinogradov_re hD₃_gt1 hprim₃
  have hχ₁1 : ∀ n, |χ₁ n| ≤ 1 := abs_chiRe_le_one (quadChar_isReal hm₁_pos)
  have hχ₂1 : ∀ n, |χ₂ n| ≤ 1 := abs_chiRe_le_one (quadChar_isReal hm₂_pos)
  have hχ₃1 : ∀ n, |χ₃ n| ≤ 1 := abs_chiRe_le_one hreal₃
  have hL₁_neg : Lval χ₁ ((49 : ℝ) / 50) < 0 := step1_Lval_neg hy₁ hm₁ hsq₁ hpid₁
  have hL₂_neg : Lval χ₂ ((49 : ℝ) / 50) < 0 := step1_Lval_neg hy₂ hm₂ hsq₂ hpid₂
  have hL₁_nn : 0 ≤ Lval χ₁ 1 :=
    Lval_one_nonneg hM₁_nn hχ₁_pv hχ₁1 (dconv_one_chiRe_nonneg (quadChar_isReal hm₁_pos))
  have hL₂_nn : 0 ≤ Lval χ₂ 1 :=
    Lval_one_nonneg hM₂_nn hχ₂_pv hχ₂1 (dconv_one_chiRe_nonneg (quadChar_isReal hm₂_pos))
  have hL₃_nn : 0 ≤ Lval χ₃ 1 :=
    Lval_one_nonneg hM₃_nn hχ₃_pv hχ₃1 (dconv_one_chiRe_nonneg hreal₃)
  have hL₁_le : Lval χ₁ 1 ≤ 32 * (D₁ : ℝ) ^ (-(19 : ℝ) / 40) := by
    have hD_pos : (0 : ℝ) < (D₁ : ℝ) := by positivity
    have h1 : Lval χ₁ 1 ≤ 2 * Real.log (D₁ : ℝ) / Real.sqrt (D₁ : ℝ) := by
      simpa [χ₁, D₁] using Lval_one_le_of_pid (by omega) hm₁ hsq₁ hpid₁
    refine h1.trans ?_
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hD_pos.le, ← neg_div]
    calc 2 * Real.log (D₁ : ℝ) * (D₁ : ℝ) ^ (-(1 : ℝ) / 2)
        ≤ 2 * (16 * (D₁ : ℝ) ^ ((1 : ℝ) / 40)) * (D₁ : ℝ) ^ (-(1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right (by linarith [log_le_16_rpow hD_pos]) (Real.rpow_nonneg hD_pos.le _)
      _ = 32 * ((D₁ : ℝ) ^ ((1 : ℝ) / 40) * (D₁ : ℝ) ^ (-(1 : ℝ) / 2)) := by ring
      _ = 32 * (D₁ : ℝ) ^ (-(19 : ℝ) / 40) := by
          rw [← Real.rpow_add hD_pos]; congr 2; norm_num
  have hL₂_le : Lval χ₂ 1 ≤ 32 * (D₂ : ℝ) ^ (-(19 : ℝ) / 40) := by
    have hD_pos : (0 : ℝ) < (D₂ : ℝ) := by positivity
    have h1 : Lval χ₂ 1 ≤ 2 * Real.log (D₂ : ℝ) / Real.sqrt (D₂ : ℝ) := by
      simpa [χ₂, D₂] using Lval_one_le_of_pid (by omega) hm₂ hsq₂ hpid₂
    refine h1.trans ?_
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hD_pos.le, ← neg_div]
    calc 2 * Real.log (D₂ : ℝ) * (D₂ : ℝ) ^ (-(1 : ℝ) / 2)
        ≤ 2 * (16 * (D₂ : ℝ) ^ ((1 : ℝ) / 40)) * (D₂ : ℝ) ^ (-(1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right (by linarith [log_le_16_rpow hD_pos]) (Real.rpow_nonneg hD_pos.le _)
      _ = 32 * ((D₂ : ℝ) ^ ((1 : ℝ) / 40) * (D₂ : ℝ) ^ (-(1 : ℝ) / 2)) := by ring
      _ = 32 * (D₂ : ℝ) ^ (-(19 : ℝ) / 40) := by
          rw [← Real.rpow_add hD_pos]; congr 2; norm_num
  have hL12_le : Lval χ₁ 1 * Lval χ₂ 1 ≤ 1024 * (P : ℝ) ^ (-(19 : ℝ) / 40) := by
    calc Lval χ₁ 1 * Lval χ₂ 1
        ≤ (32 * (D₁ : ℝ) ^ (-(19 : ℝ) / 40)) * (32 * (D₂ : ℝ) ^ (-(19 : ℝ) / 40)) :=
          mul_le_mul hL₁_le hL₂_le hL₂_nn (by positivity)
      _ = 1024 * ((D₁ : ℝ) ^ (-(19 : ℝ) / 40) * (D₂ : ℝ) ^ (-(19 : ℝ) / 40)) := by ring
      _ = 1024 * (P : ℝ) ^ (-(19 : ℝ) / 40) := by
          rw [← Real.mul_rpow (by positivity) (by positivity)]; push_cast [P]; rfl
  have hM₃_le_P : M₃ ≤ Real.sqrt (P : ℝ) * (Real.log (P : ℝ) + 1) := by
    have hD₃_rpos : (0 : ℝ) < (D₃ : ℝ) := by exact_mod_cast (by omega : 0 < D₃)
    have hD₃_rle : (D₃ : ℝ) ≤ (P : ℝ) := by exact_mod_cast hD₃_le_P
    have hlog_le : Real.log (D₃ : ℝ) ≤ Real.log (P : ℝ) := Real.log_le_log hD₃_rpos hD₃_rle
    dsimp [M₃]
    exact mul_le_mul (Real.sqrt_le_sqrt hD₃_rle) (by linarith only [hlog_le])
      (by linarith only [Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ D₃) : (1 : ℝ) ≤ (D₃ : ℝ))])
      (Real.sqrt_nonneg _)
  set N₀ : ℕ := Nat.sqrt P
  have hN₀_ge4 : 4 ≤ N₀ := Nat.le_sqrt.mpr (by omega)
  have hN₀_le_sq : (N₀ : ℝ) ≤ Real.sqrt (P : ℝ) := by
    rw [Real.le_sqrt (by positivity) hP_pos.le, sq]; exact_mod_cast Nat.sqrt_le P
  have hsq_lt_N₀1 : Real.sqrt (P : ℝ) < ((N₀ + 1 : ℕ) : ℝ) := by
    rw [Real.sqrt_lt' (by positivity), sq]; exact_mod_cast Nat.lt_succ_sqrt P
  have hL₃_one_le : Lval χ₃ 1 ≤ 34 * (P : ℝ) ^ ((1 : ℝ) / 40) := by
    have hb := abs_Lval_one_le hM₃_nn hχ₃_pv hχ₃1 (by omega : 1 ≤ N₀)
    have hlogN₀ : Real.log (N₀ : ℝ) ≤ Real.log (P : ℝ) :=
      Real.log_le_log (by positivity) (hN₀_le_sq.trans (by
        rw [Real.sqrt_le_left hP_pos.le]; nlinarith only [hP_ge1]))
    have hdiv_le : M₃ / ((N₀ + 1 : ℕ) : ℝ) ≤ Real.log (P : ℝ) + 1 := by
      rw [div_le_iff₀ (by positivity)]
      calc M₃ ≤ Real.sqrt (P : ℝ) * (Real.log (P : ℝ) + 1) := hM₃_le_P
        _ ≤ ((N₀ + 1 : ℕ) : ℝ) * (Real.log (P : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right hsq_lt_N₀1.le (by linarith only [Real.log_nonneg hP_ge1])
        _ = (Real.log (P : ℝ) + 1) * ((N₀ + 1 : ℕ) : ℝ) := mul_comm _ _
    have hlogP := log_add_one_le_17_rpow hP_ge1
    calc Lval χ₃ 1 ≤ |Lval χ₃ 1| := le_abs_self _
      _ ≤ (Real.log (N₀ : ℝ) + 1) + M₃ / ((N₀ + 1 : ℕ) : ℝ) := hb
      _ ≤ 2 * (Real.log (P : ℝ) + 1) := by linarith only [hlogN₀, hdiv_le]
      _ ≤ 2 * (17 * (P : ℝ) ^ ((1 : ℝ) / 40)) := by linarith only [hlogP]
      _ = 34 * (P : ℝ) ^ ((1 : ℝ) / 40) := by ring
  have hL₃_deriv_le : ∀ ξ : ℝ, (49 : ℝ) / 50 ≤ ξ → ξ ≤ 1 →
      |Lderiv χ₃ ξ| ≤ 578 * (P : ℝ) ^ ((3 : ℝ) / 50) := fun ξ hξ1 hξ2 =>
    Lderiv_bound_of_P hP_big hM₃_nn hM₃_le_P hχ₃_pv hχ₃1 hξ1 hξ2
  -- Case split on L₃(49/50)
  by_cases hL₃_sign : 0 ≤ Lval χ₃ ((49 : ℝ) / 50)
  · -- Case A: L₃(49/50) ≥ 0
    have hstep := step2_hyperbola_bound hy₁ hm₁ hsq₁ hy₂ hm₂ hsq₂ hne
      (s := (49 : ℝ) / 50) le_rfl (by norm_num)
    have hsec : zetaVal ((49 : ℝ) / 50) *
        (Lval χ₁ ((49 : ℝ) / 50) * Lval χ₂ ((49 : ℝ) / 50) * Lval χ₃ ((49 : ℝ) / 50)) ≤ 0 := by
      have hz := (zetaVal_bounds (by norm_num : (0 : ℝ) < (49 : ℝ) / 50) (by norm_num)).1
      have hprod : 0 ≤ Lval χ₁ ((49 : ℝ) / 50) * Lval χ₂ ((49 : ℝ) / 50) *
          Lval χ₃ ((49 : ℝ) / 50) :=
        mul_nonneg (mul_nonneg_of_nonpos_of_nonpos hL₁_neg.le hL₂_neg.le) hL₃_sign
      exact mul_nonpos_of_nonpos_of_nonneg hz.le hprod
    have hmain : (((P ^ 4 : ℕ) : ℝ) ^ (1 - (49 : ℝ) / 50) / (1 - (49 : ℝ) / 50)) *
        (Lval χ₁ 1 * Lval χ₂ 1 * Lval χ₃ 1) ≤ (1 : ℝ) / 2 := by
      have hP4 : (((P ^ 4 : ℕ) : ℝ) ^ (1 - (49 : ℝ) / 50) / (1 - (49 : ℝ) / 50)) =
          50 * (P : ℝ) ^ ((2 : ℝ) / 25) := by
        have hcast : ((P ^ 4 : ℕ) : ℝ) = (P : ℝ) ^ (4 : ℕ) := by push_cast; rfl
        rw [hcast, ← Real.rpow_natCast, ← Real.rpow_mul hP_pos.le]
        have h1 : ((4 : ℕ) : ℝ) * (1 - (49 : ℝ) / 50) = (2 : ℝ) / 25 := by norm_num
        have h2 : (1 : ℝ) - (49 : ℝ) / 50 = (1 : ℝ) / 50 := by norm_num
        rw [h1, h2]; ring
      rw [hP4]
      calc 50 * (P : ℝ) ^ ((2 : ℝ) / 25) * (Lval χ₁ 1 * Lval χ₂ 1 * Lval χ₃ 1)
          ≤ 50 * (P : ℝ) ^ ((2 : ℝ) / 25) *
              ((1024 * (P : ℝ) ^ (-(19 : ℝ) / 40)) * (34 * (P : ℝ) ^ ((1 : ℝ) / 40))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hL12_le hL₃_one_le hL₃_nn (by positivity)) (by positivity)
        _ = 1740800 * (P : ℝ) ^ (-(37 : ℝ) / 100) := by
            have hcomb : (P : ℝ) ^ ((2 : ℝ) / 25) *
                ((P : ℝ) ^ (-(19 : ℝ) / 40) * (P : ℝ) ^ ((1 : ℝ) / 40)) =
                (P : ℝ) ^ (-(37 : ℝ) / 100) := by
              rw [← Real.rpow_add hP_pos, ← Real.rpow_add hP_pos]; congr 1; norm_num
            calc 50 * (P : ℝ) ^ ((2 : ℝ) / 25) *
                  (1024 * (P : ℝ) ^ (-(19 : ℝ) / 40) * (34 * (P : ℝ) ^ ((1 : ℝ) / 40)))
                = 1740800 * ((P : ℝ) ^ ((2 : ℝ) / 25) *
                    ((P : ℝ) ^ (-(19 : ℝ) / 40) * (P : ℝ) ^ ((1 : ℝ) / 40))) := by ring
              _ = _ := by rw [hcomb]
        _ ≤ 1740800 * (2 : ℝ) ^ (-22 : ℤ) :=
            mul_le_mul_of_nonneg_left (rpow_neg_le_two_pow hP_rbig (by norm_num) (by norm_num))
              (by norm_num)
        _ ≤ (1 : ℝ) / 2 := by norm_num
    change (1 : ℝ) ≤ (((P ^ 4 : ℕ) : ℝ) ^ (1 - (49 : ℝ) / 50) / (1 - (49 : ℝ) / 50)) *
        (Lval χ₁ 1 * Lval χ₂ 1 * Lval χ₃ 1) +
        zetaVal ((49 : ℝ) / 50) *
          (Lval χ₁ ((49 : ℝ) / 50) * Lval χ₂ ((49 : ℝ) / 50) * Lval χ₃ ((49 : ℝ) / 50)) +
        (1 : ℝ) / 16 at hstep
    linarith
  · -- Case B: L₃(49/50) < 0
    push Not at hL₃_sign
    rcases eq_or_lt_of_le hL₃_nn with hL₃_zero | hL₃_pos
    · -- Subcase B2: L₃(1) = 0
      have hcont₁ : ContinuousAt (Lval χ₁) 1 :=
        (hasDerivAt_Lval hM₁_nn hχ₁_pv (by norm_num : (1 : ℝ) ∈ Set.Ioo ((1 : ℝ) / 2) 2)).continuousAt
      have hcont₂ : ContinuousAt (Lval χ₂) 1 :=
        (hasDerivAt_Lval hM₂_nn hχ₂_pv (by norm_num : (1 : ℝ) ∈ Set.Ioo ((1 : ℝ) / 2) 2)).continuousAt
      have hε₁_pos : 0 < (D₁ : ℝ) ^ (-(19 : ℝ) / 40) := Real.rpow_pos_of_pos (by positivity) _
      have hε₂_pos : 0 < (D₂ : ℝ) ^ (-(19 : ℝ) / 40) := Real.rpow_pos_of_pos (by positivity) _
      obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.continuousAt_iff.mp hcont₁ _ hε₁_pos
      obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := Metric.continuousAt_iff.mp hcont₂ _ hε₂_pos
      set δ : ℝ := min δ₁ δ₂
      have hδ_pos : 0 < δ := lt_min hδ₁_pos hδ₂_pos
      set s : ℝ := max ((49 : ℝ) / 50) (1 - δ / 2)
      have hs1 : (49 : ℝ) / 50 ≤ s := le_max_left _ _
      have hs2 : s < 1 := max_lt (by norm_num) (by linarith)
      have hs_dist : dist s 1 < δ := by
        rw [Real.dist_eq, abs_of_neg (by linarith)]
        have : 1 - δ / 2 ≤ s := le_max_right _ _
        linarith
      have hL₁s : |Lval χ₁ s| ≤ 33 * (D₁ : ℝ) ^ (-(19 : ℝ) / 40) := by
        have hd := hδ₁ (lt_of_lt_of_le hs_dist (min_le_left _ _))
        rw [Real.dist_eq] at hd
        have : |Lval χ₁ 1| = Lval χ₁ 1 := abs_of_nonneg hL₁_nn
        calc |Lval χ₁ s| = |(Lval χ₁ s - Lval χ₁ 1) + Lval χ₁ 1| := by ring_nf
          _ ≤ |Lval χ₁ s - Lval χ₁ 1| + |Lval χ₁ 1| := abs_add_le _ _
          _ ≤ 33 * (D₁ : ℝ) ^ (-(19 : ℝ) / 40) := by linarith
      have hL₂s : |Lval χ₂ s| ≤ 33 * (D₂ : ℝ) ^ (-(19 : ℝ) / 40) := by
        have hd := hδ₂ (lt_of_lt_of_le hs_dist (min_le_right _ _))
        rw [Real.dist_eq] at hd
        have : |Lval χ₂ 1| = Lval χ₂ 1 := abs_of_nonneg hL₂_nn
        calc |Lval χ₂ s| = |(Lval χ₂ s - Lval χ₂ 1) + Lval χ₂ 1| := by ring_nf
          _ ≤ |Lval χ₂ s - Lval χ₂ 1| + |Lval χ₂ 1| := abs_add_le _ _
          _ ≤ 33 * (D₂ : ℝ) ^ (-(19 : ℝ) / 40) := by linarith
      obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (Lval χ₃) (Lderiv χ₃) hs2
        ((continuousOn_Lval hM₃_nn hχ₃_pv).mono (Set.Icc_subset_Icc hs1 le_rfl))
        (fun x hx => hasDerivAt_Lval hM₃_nn hχ₃_pv ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      have hL₃s : |Lval χ₃ s| ≤ (1 - s) * (578 * (P : ℝ) ^ ((3 : ℝ) / 50)) := by
        have heq : Lval χ₃ s = -(1 - s) * Lderiv χ₃ ξ := by
          rw [hslope, ← hL₃_zero, zero_sub]
          field_simp [show 1 - s ≠ 0 by linarith]
        rw [heq, abs_mul, abs_neg, abs_of_pos (by linarith : 0 < 1 - s)]
        exact mul_le_mul_of_nonneg_left (hL₃_deriv_le ξ (by linarith [hξ.1]) hξ.2.le) (by linarith)
      have hz_abs := (zetaVal_bounds (by linarith : 0 < s) hs2).2
      have hsec_le : |zetaVal s * (Lval χ₁ s * Lval χ₂ s * Lval χ₃ s)| ≤ (1 : ℝ) / 16 := by
        have h12 : |Lval χ₁ s| * |Lval χ₂ s| ≤ 1089 * (P : ℝ) ^ (-(19 : ℝ) / 40) := by
          calc |Lval χ₁ s| * |Lval χ₂ s|
              ≤ (33 * (D₁ : ℝ) ^ (-(19 : ℝ) / 40)) * (33 * (D₂ : ℝ) ^ (-(19 : ℝ) / 40)) :=
                mul_le_mul hL₁s hL₂s (abs_nonneg _) (by positivity)
            _ = 1089 * ((D₁ : ℝ) ^ (-(19 : ℝ) / 40) * (D₂ : ℝ) ^ (-(19 : ℝ) / 40)) := by ring
            _ = 1089 * (P : ℝ) ^ (-(19 : ℝ) / 40) := by
                rw [← Real.mul_rpow (by positivity) (by positivity)]; push_cast [P]; rfl
        have hz3 : |zetaVal s| * |Lval χ₃ s| ≤ 578 * (P : ℝ) ^ ((3 : ℝ) / 50) := by
          calc |zetaVal s| * |Lval χ₃ s|
              ≤ (1 / (1 - s)) * ((1 - s) * (578 * (P : ℝ) ^ ((3 : ℝ) / 50))) :=
                mul_le_mul hz_abs hL₃s (abs_nonneg _) (by positivity)
            _ = 578 * (P : ℝ) ^ ((3 : ℝ) / 50) := by field_simp [show 1 - s ≠ 0 by linarith]
        rw [abs_mul, abs_mul, abs_mul]
        calc |zetaVal s| * (|Lval χ₁ s| * |Lval χ₂ s| * |Lval χ₃ s|)
            = (|Lval χ₁ s| * |Lval χ₂ s|) * (|zetaVal s| * |Lval χ₃ s|) := by ring
          _ ≤ (1089 * (P : ℝ) ^ (-(19 : ℝ) / 40)) * (578 * (P : ℝ) ^ ((3 : ℝ) / 50)) :=
              mul_le_mul h12 hz3 (by positivity) (by positivity)
          _ = 629442 * (P : ℝ) ^ (-(83 : ℝ) / 200) := by
              calc 1089 * (P : ℝ) ^ (-(19 : ℝ) / 40) * (578 * (P : ℝ) ^ ((3 : ℝ) / 50))
                  = 629442 * ((P : ℝ) ^ (-(19 : ℝ) / 40) * (P : ℝ) ^ ((3 : ℝ) / 50)) := by ring
                _ = _ := by rw [← Real.rpow_add hP_pos]; congr 2; norm_num
          _ ≤ 629442 * (2 : ℝ) ^ (-24 : ℤ) :=
              mul_le_mul_of_nonneg_left (rpow_neg_le_two_pow hP_rbig (by norm_num) (by norm_num))
                (by norm_num)
          _ ≤ (1 : ℝ) / 16 := by norm_num
      have hstep := step2_hyperbola_bound hy₁ hm₁ hsq₁ hy₂ hm₂ hsq₂ hne hs1 hs2
      change (1 : ℝ) ≤ (((P ^ 4 : ℕ) : ℝ) ^ (1 - s) / (1 - s)) *
          (Lval χ₁ 1 * Lval χ₂ 1 * Lval χ₃ 1) +
          zetaVal s * (Lval χ₁ s * Lval χ₂ s * Lval χ₃ s) + (1 : ℝ) / 16 at hstep
      rw [← hL₃_zero, mul_zero, mul_zero, zero_add] at hstep
      linarith [(abs_le.mp hsec_le).2]
    · -- Subcase B1: L₃(1) > 0, apply IVT on [49/50, 1]
      have hivt := intermediate_value_Icc (by norm_num : (49 : ℝ) / 50 ≤ 1)
        (continuousOn_Lval hM₃_nn hχ₃_pv)
      have h0mem : (0 : ℝ) ∈ Set.Icc (Lval χ₃ ((49 : ℝ) / 50)) (Lval χ₃ 1) := ⟨hL₃_sign.le, hL₃_pos.le⟩
      obtain ⟨β, hβ_mem, hβ_zero⟩ := hivt h0mem
      have hβ_lt1 : β < 1 := by
        rcases eq_or_lt_of_le hβ_mem.2 with rfl | hlt
        · linarith
        · exact hlt
      obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (Lval χ₃) (Lderiv χ₃) hβ_lt1
        ((continuousOn_Lval hM₃_nn hχ₃_pv).mono (Set.Icc_subset_Icc hβ_mem.1 le_rfl))
        (fun x hx => hasDerivAt_Lval hM₃_nn hχ₃_pv ⟨by linarith [hx.1, hβ_mem.1], by linarith [hx.2]⟩)
      have hL₃_div : Lval χ₃ 1 / (1 - β) ≤ 578 * (P : ℝ) ^ ((3 : ℝ) / 50) := by
        have heq : Lval χ₃ 1 / (1 - β) = Lderiv χ₃ ξ := by
          rw [hslope, hβ_zero, sub_zero]
        rw [heq]
        exact (le_abs_self _).trans (hL₃_deriv_le ξ (by linarith [hξ.1, hβ_mem.1]) hξ.2.le)
      have hstep := step2_hyperbola_bound hy₁ hm₁ hsq₁ hy₂ hm₂ hsq₂ hne hβ_mem.1 hβ_lt1
      change (1 : ℝ) ≤ (((P ^ 4 : ℕ) : ℝ) ^ (1 - β) / (1 - β)) *
          (Lval χ₁ 1 * Lval χ₂ 1 * Lval χ₃ 1) +
          zetaVal β * (Lval χ₁ β * Lval χ₂ β * Lval χ₃ β) + (1 : ℝ) / 16 at hstep
      rw [hβ_zero, mul_zero, mul_zero, add_zero] at hstep
      have hP4_le : ((P ^ 4 : ℕ) : ℝ) ^ (1 - β) ≤ (P : ℝ) ^ ((2 : ℝ) / 25) := by
        have hcast : ((P ^ 4 : ℕ) : ℝ) = (P : ℝ) ^ (4 : ℕ) := by push_cast; rfl
        rw [hcast, ← Real.rpow_natCast, ← Real.rpow_mul hP_pos.le]
        exact Real.rpow_le_rpow_of_exponent_le hP_ge1 (by linarith [hβ_mem.1])
      have hmain : (((P ^ 4 : ℕ) : ℝ) ^ (1 - β) / (1 - β)) *
          (Lval χ₁ 1 * Lval χ₂ 1 * Lval χ₃ 1) ≤ (3 : ℝ) / 5 := by
        have hrew : (((P ^ 4 : ℕ) : ℝ) ^ (1 - β) / (1 - β)) *
            (Lval χ₁ 1 * Lval χ₂ 1 * Lval χ₃ 1) =
            ((P ^ 4 : ℕ) : ℝ) ^ (1 - β) * (Lval χ₁ 1 * Lval χ₂ 1) * (Lval χ₃ 1 / (1 - β)) := by ring
        rw [hrew]
        calc ((P ^ 4 : ℕ) : ℝ) ^ (1 - β) * (Lval χ₁ 1 * Lval χ₂ 1) * (Lval χ₃ 1 / (1 - β))
            ≤ (P : ℝ) ^ ((2 : ℝ) / 25) * (1024 * (P : ℝ) ^ (-(19 : ℝ) / 40)) *
                (578 * (P : ℝ) ^ ((3 : ℝ) / 50)) :=
              mul_le_mul
                (mul_le_mul hP4_le hL12_le (mul_nonneg hL₁_nn hL₂_nn) (Real.rpow_nonneg hP_pos.le _))
                hL₃_div (div_nonneg hL₃_nn (by linarith)) (by positivity)
          _ = 591872 * (P : ℝ) ^ (-(67 : ℝ) / 200) := by
              have hcomb : (P : ℝ) ^ ((2 : ℝ) / 25) * (P : ℝ) ^ (-(19 : ℝ) / 40) *
                  (P : ℝ) ^ ((3 : ℝ) / 50) = (P : ℝ) ^ (-(67 : ℝ) / 200) := by
                rw [← Real.rpow_add hP_pos, ← Real.rpow_add hP_pos]; congr 1; norm_num
              calc (P : ℝ) ^ ((2 : ℝ) / 25) * (1024 * (P : ℝ) ^ (-(19 : ℝ) / 40)) *
                    (578 * (P : ℝ) ^ ((3 : ℝ) / 50))
                  = 591872 * ((P : ℝ) ^ ((2 : ℝ) / 25) * (P : ℝ) ^ (-(19 : ℝ) / 40) *
                      (P : ℝ) ^ ((3 : ℝ) / 50)) := by ring
                _ = _ := by rw [hcomb]
          _ ≤ 591872 * (2 : ℝ) ^ (-20 : ℤ) :=
              mul_le_mul_of_nonneg_left (rpow_neg_le_two_pow hP_rbig (by norm_num) (by norm_num))
                (by norm_num)
          _ ≤ (3 : ℝ) / 5 := by norm_num
      linarith

end Erdos1140H2Proof

private theorem Erdos1140FiniteExceptions.classify :
    Erdos1140FiniteExceptions.H2 := by
  intro m₁ hm₁ m₂ hm₂
  by_contra hne
  obtain ⟨hm₁398, ⟨y₁, hy₁_eq⟩, hsq₁, hpid₁⟩ := hm₁
  obtain ⟨hm₂398, ⟨y₂, hy₂_eq⟩, hsq₂, hpid₂⟩ := hm₂
  have hy₁ : 4102 ≤ y₁ := Erdos1140H2Proof.y_ge_4102 hm₁398 hy₁_eq hpid₁
  have hy₂ : 4102 ≤ y₂ := Erdos1140H2Proof.y_ge_4102 hm₂398 hy₂_eq hpid₂
  exact Erdos1140H2Proof.two_solutions_false hy₁ hy₁_eq hsq₁ hpid₁ hy₂ hy₂_eq hsq₂ hpid₂ hne



namespace Erdos1140FiniteExceptions
private theorem unique_exceptional_primes : ({n : ℕ | 199 < n ∧ n.Prime ∧ (n % 60 = 19 ∨ n % 60 = 31) ∧
      (∀ x : ℕ, n ≠ 2 * x^2 + 1) ∧
      ∀ p : ℕ, p.Prime → p^2 ≤ n → ∀ r < p,
        2 * r^2 + p < n → ¬ (2 * r^2 ≡ n [MOD p])} : Set ℕ).Subsingleton := by
  have lift {n : ℕ} (h : 199<n ∧ n.Prime ∧ (n%60=19 ∨ n%60=31) ∧
      (∀ x : ℕ, n ≠ 2*x^2+1) ∧ ∀ p : ℕ, p.Prime → p^2 ≤ n → ∀ r < p,
        2*r^2+p<n → ¬ (2*r^2 ≡ n [MOD p])) :
      398<2*n ∧ (∃ y : ℕ, 2*n+2=(4*y)^2) ∧ Squarefree (2*n) ∧
        IsPrincipalIdealRing (Zsqrtd ((2*n:ℕ):ℤ)) := by
    obtain ⟨hn,hp,r,one,sieve⟩ := h
    have res : n%4=3 := by omega
    have prop := (OMA.R_Erdos1140_erdos_1140_R1.sieve_iff n (by omega)).2 ⟨one,sieve⟩
    have e := shape res prop one
    have cop : Nat.Coprime 2 n := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
    refine ⟨by omega,e,?_,?_⟩
    · exact (Nat.squarefree_mul cop).mpr ⟨Nat.prime_two.squarefree,hp.squarefree⟩
    · simpa using principal n hp res e (fun _ hp hn le a => no_root res prop hp hn le a)
  intro a ha b hb
  have e := classify (lift ha) (lift hb)
  omega


end Erdos1140FiniteExceptions

theorem OMA.solution : OMA.R_Erdos1140_erdos_1140_R1.H2 :=
  Erdos1140FiniteExceptions.unique_exceptional_primes.finite
