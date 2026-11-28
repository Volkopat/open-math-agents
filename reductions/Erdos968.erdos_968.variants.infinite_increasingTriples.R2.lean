import FormalConjectures.ErdosProblems.«968»
import Mathlib

/-!
An isolated reduced residue class and Linnik's least-prime theorem give an
alternative to invoking a theorem on consecutive prime gaps. The square of the
modulus lets us place the central prime above twice the modulus while keeping
its logarithm under control.

Credit: @yuka30240
-/

namespace OMA.R_Erdos968_erdos_968_variants_infinite_increasingTriples_R2

private lemma normalized_le_log (n : ℕ) :
    Erdos968.u n ≤ 16 * Real.log (Nat.nth Nat.Prime n) := by
  let p := Nat.nth Nat.Prime n
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_nth_prime n).two_le
  have hcount : Nat.primeCounting p = n + 1 :=
    Nat.count_nth_succ (fun hf => (Nat.infinite_setOfPred_prime hf).elim)
  have hc := Chebyshev.pi_ge p
  rw [div_le_iff₀ (Real.log_pos (by linarith : (1 : ℝ) < p)), hcount] at hc
  push_cast at hc
  have ht := Real.log_le_sub_one_of_pos (show 0 < ((p : ℝ) + 1) / 2 by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at ht
  have hlo : (0.69 : ℝ) * p ≤ p * Real.log 2 := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.log_two_gt_d9]) (by positivity)
  change (p : ℝ) / (n + 1) ≤ 16 * Real.log p
  rw [div_le_iff₀ (by positivity)]
  nlinarith only [hc, ht, hlo, Real.log_two_lt_d9, hp]

private lemma increasing_of_gap (n : ℕ)
    (h : Erdos968.u n < (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n) :
    Erdos968.u n < Erdos968.u (n + 1) := by
  unfold Erdos968.u at h ⊢
  push_cast
  rw [div_lt_iff₀ (by positivity)] at h
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- All other primes lie outside the covered offsets. Primes dividing q are
handled separately, since they need not be coprime to q. -/
private lemma radius_le_prime_dist {q a r p : ℕ} (hq : 0 < q) (hr : r ≤ q)
    (hcover : ∀ d, 0 < d → d ≤ r → ¬ (a + d).Coprime q ∧ ¬ (a + (q - d)).Coprime q)
    (hlift : 2 * q ≤ p) (hres : p ≡ a [MOD q])
    {s : ℕ} (hs : s.Prime) (hne : s ≠ p) : r ≤ Nat.dist s p := by
  by_cases hsmall : s ≤ q
  · rw [Nat.dist_eq_sub_of_le (by omega)]
    omega
  have hunit := hs.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hq (by omega))
  by_contra! hclose
  rcases lt_or_gt_of_ne hne with hleft | hright
  · rw [Nat.dist_eq_sub_of_le hleft.le] at hclose
    let d := p - s
    have hd : 0 < d := Nat.sub_pos_of_lt hleft
    have hdr : d ≤ r := hclose.le
    have heq : p + (q - d) = s + q := by dsimp [d] at *; omega
    have hshift := hres.add_right (q - d)
    rw [heq] at hshift
    have hsmod : s ≡ a + (q - d) [MOD q] := by simpa [Nat.ModEq] using hshift
    exact (hcover d hd hdr).2 (hsmod.gcd_eq.symm.trans hunit)
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hright.le] at hclose
    let d := s - p
    have hshift := hres.add_right d
    have heq : p + d = s := by dsimp [d]; omega
    rw [heq] at hshift
    exact (hcover d (Nat.sub_pos_of_lt hright) hclose.le).1 (hshift.gcd_eq.symm.trans hunit)

/-- An isolated invertible class on the circle of residues modulo q.
This is the fixed-logarithmic-radius consequence of Maier and Rassias,
*The ternary Goldbach problem with a prime and two isolated primes*, Theorem 2.1.
The term a + (q - d) represents the offset to the left without truncated subtraction. -/
def H1 : Prop := ∀ K Q : ℕ, ∃ q ≥ Q, ∃ a r : ℕ,
    a < q ∧ a.Coprime q ∧ r ≤ q ∧ (K : ℝ) * Real.log q ≤ r ∧
    ∀ d, 0 < d → d ≤ r → ¬ (a + d).Coprime q ∧ ¬ (a + (q - d)).Coprime q

/-- Linnik's bound for the least prime in a reduced residue class.
For q ≥ 2 the absolute multiplicative constant can be absorbed into the exponent. -/
def H2 : Prop := ∃ L : ℕ, ∀ q a : ℕ, 2 ≤ q → a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ p ≤ q ^ L

theorem main : H1 → H2 → type_of% @Erdos968.erdos_968.variants.infinite_increasingTriples := by
  rintro hcovering ⟨L, hlinnik⟩
  apply Set.infinite_of_forall_exists_gt
  intro N
  let P := Nat.nth Nat.Prime
  have hmono : StrictMono P := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  obtain ⟨q, hlarge, a, r, ha, hunit, hr, hlength, hcover⟩ :=
    hcovering (32 * L + 1) (max 4 (P (N + 1)))
  have hq : 4 ≤ q := (le_max_left _ _).trans hlarge
  have haMod : a + q * 2 ≡ a [MOD q] := Nat.add_mul_mod_self_left a q 2
  have hcop : (a + q * 2).Coprime q := haMod.gcd_eq.trans hunit
  obtain ⟨p, hp, hclass, hbound⟩ := hlinnik (q ^ 2) (a + q * 2) (by nlinarith) (hcop.pow_right 2)
  have hrep : a + q * 2 < q ^ 2 := by nlinarith
  have hmin := hclass.symm.le_of_lt_add (show a + q * 2 < p + q ^ 2 by omega)
  have hres := (hclass.of_dvd (dvd_pow_self q (by decide : 2 ≠ 0))).trans haMod
  have hsep {s : ℕ} (hs : s.Prime) (hne : s ≠ p) : r ≤ Nat.dist s p :=
    radius_le_prime_dist (by omega : 0 < q) hr hcover (by omega : 2 * q ≤ p) hres hs hne
  have hscale := Real.log_le_log (by exact_mod_cast hp.pos)
    (show (p : ℝ) ≤ ((q : ℝ) ^ 2) ^ L by exact_mod_cast hbound)
  rw [Real.log_pow, Real.log_pow] at hscale
  push_cast at hlength hscale
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hwide : 16 * Real.log p < r := by nlinarith only [hlength, hscale, hlog]
  let k := Nat.count Nat.Prime p
  have hk : P k = p := Nat.nth_count hp
  have hNk : N + 1 < k := by
    apply hmono.lt_iff_lt.mp
    rw [hk]
    have := (le_max_right 4 (P (N + 1))).trans hlarge
    omega
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  have hmid : P (n + 1) = p := by simpa only [hn] using hk
  have hleft : P n < p := by
    rw [← hmid]
    exact hmono (Nat.lt_succ_self n)
  have hright : p < P (n + 2) := by
    rw [← hmid]
    exact hmono (Nat.lt_succ_self (n + 1))
  have hleftGap := hsep (Nat.prime_nth_prime n) hleft.ne
  have hrightGap := hsep (Nat.prime_nth_prime (n + 2)) hright.ne'
  rw [Nat.dist_eq_sub_of_le hleft.le] at hleftGap
  rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hright.le] at hrightGap
  have hlogLeft := Real.log_le_log (by exact_mod_cast (Nat.prime_nth_prime n).pos)
    (show (P n : ℝ) ≤ p by exact_mod_cast hleft.le)
  have h1 : (r : ℝ) ≤ (p : ℝ) - P n := by
    rw [le_sub_iff_add_le]
    exact_mod_cast (show r + P n ≤ p by omega)
  have h2 : (r : ℝ) ≤ (P (n + 2) : ℝ) - p := by
    rw [le_sub_iff_add_le]
    exact_mod_cast (show r + p ≤ P (n + 2) by omega)
  refine ⟨n, ⟨increasing_of_gap n ?_, increasing_of_gap (n + 1) ?_⟩, by omega⟩
  · change Erdos968.u n < (P (n + 1) : ℝ) - P n
    rw [hmid]
    linarith [show Erdos968.u n ≤ 16 * Real.log (P n) from normalized_le_log n]
  · change Erdos968.u (n + 1) < (P (n + 2) : ℝ) - P (n + 1)
    have hu : Erdos968.u (n + 1) ≤ 16 * Real.log (P (n + 1)) := normalized_le_log _
    rw [hmid] at hu ⊢
    linarith

end OMA.R_Erdos968_erdos_968_variants_infinite_increasingTriples_R2
