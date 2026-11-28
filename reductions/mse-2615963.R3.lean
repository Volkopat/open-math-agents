import OMAStatements.S_mse_2615963
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Reduction of the Chebyshev primality congruence (MSE 2615963)

Reduces the primality equivalence
`n.Prime ↔ ∑ k ∈ Finset.range n, C (n - 1) k ≡ -1 [ZMOD n]`
for `n > 1` into two components:
- `H1` (provable): exact finite-field character sum identity for `∑ k ∈ range p, C m k [ZMOD p]`
  for every odd prime `p` and `m : ℕ`.
- `H2` (open signed-Giuga core): no odd squarefree composite integer `n` with at least 5 prime
  factors satisfies at every prime `p ∣ n` either
  `(p - 1) ∣ (n - 1) ∧ ¬((p + 1) ∣ (n - 1)) ∧ n / p ≡ 1 [ZMOD p]` or
  `(p + 1) ∣ (n - 1) ∧ ¬((p - 1) ∣ (n - 1)) ∧ n / p ≡ -1 [ZMOD p]`.

`main` handles `n = 2`, proves the forward (prime) direction from `H1`, and in the converse
direction proves via periodicity modulo prime factors that any composite counterexample must be
squarefree, odd, satisfy the signed Giuga-Korselt condition at every prime factor, and have at
least 5 distinct prime factors (ruling out 2, 3, and 4 prime factors via exact divisibility and
signed reciprocal-sum parity bounds).
-/

namespace OMA.R_mse_2615963_R3

-- Closed-form evaluation of the sum of rescaled Chebyshev polynomials C_m(k) modulo an odd prime p.
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ m : ℕ,
    Int.ModEq (p : ℤ)
      (∑ k ∈ Finset.range p, (Polynomial.Chebyshev.C ℤ (m : ℤ)).eval (k : ℤ))
      ((if (p - 1) ∣ m then (-1 : ℤ) else 0) + (if (p + 1) ∣ m then (1 : ℤ) else 0))

-- Open signed-Giuga core: no odd squarefree composite number with at least 5 prime factors
-- satisfies the signed Giuga-Korselt condition at every prime divisor.
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → ¬ n.Prime → Squarefree n → Odd n → 5 ≤ n.primeFactors.card →
    (∀ p ∈ n.primeFactors,
      ((p - 1) ∣ (n - 1) ∧ ¬ ((p + 1) ∣ (n - 1)) ∧ Int.ModEq (p : ℤ) ((n / p : ℕ) : ℤ) 1) ∨
      ((p + 1) ∣ (n - 1) ∧ ¬ ((p - 1) ∣ (n - 1)) ∧ Int.ModEq (p : ℤ) ((n / p : ℕ) : ℤ) (-1))) →
    False

lemma poly_eval_modEq (P : Polynomial ℤ) (p : ℕ) (a b : ℤ)
    (h : Int.ModEq (p : ℤ) a b) :
    Int.ModEq (p : ℤ) (P.eval a) (P.eval b) := by
  rw [← ZMod.intCast_eq_intCast_iff] at h ⊢
  have hev : ∀ x : ℤ, ((P.eval x : ℤ) : ZMod p) =
      (P.map (Int.castRingHom (ZMod p))).eval (x : ZMod p) := by
    intro x
    simp [Polynomial.eval_map]
  rw [hev a, hev b, h]

lemma sum_range_mul_modEq (P : Polynomial ℤ) (p q : ℕ) :
    Int.ModEq (p : ℤ)
      (∑ k ∈ Finset.range (q * p), P.eval (k : ℤ))
      ((q : ℤ) * ∑ k ∈ Finset.range p, P.eval (k : ℤ)) := by
  induction q with
  | zero => simp [Int.ModEq]
  | succ q ih =>
    rw [Nat.succ_mul, Finset.sum_range_add]
    have hstep : Int.ModEq (p : ℤ)
        (∑ k ∈ Finset.range p, P.eval ((q * p + k : ℕ) : ℤ))
        (∑ k ∈ Finset.range p, P.eval (k : ℤ)) := by
      rw [← ZMod.intCast_eq_intCast_iff]
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ZMod.intCast_eq_intCast_iff]
      apply poly_eval_modEq
      rw [Int.ModEq]
      have hre : (q : ℤ) * (p : ℤ) + (k : ℤ) = (k : ℤ) + (p : ℤ) * (q : ℤ) := by ring
      rw [hre]
      exact Int.add_mul_emod_self_left (k : ℤ) (p : ℤ) (q : ℤ)
    have hcomb := ih.add hstep
    simpa [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hcomb

lemma sum_range_dvd_modEq (P : Polynomial ℤ) {p n : ℕ} (hp : p ∣ n) :
    Int.ModEq (p : ℤ)
      (∑ k ∈ Finset.range n, P.eval (k : ℤ))
      (((n / p : ℕ) : ℤ) * ∑ k ∈ Finset.range p, P.eval (k : ℤ)) := by
  have hn : n / p * p = n := Nat.div_mul_cancel hp
  conv_lhs => rw [← hn]
  exact sum_range_mul_modEq P p (n / p)

lemma not_zero_modEq_neg_one {p : ℕ} (hp : 1 < p)
    (h : Int.ModEq (p : ℤ) 0 (-1)) : False := by
  have hdvd : (p : ℤ) ∣ (-1 : ℤ) - 0 := Int.modEq_iff_dvd.mp h
  simp only [sub_zero] at hdvd
  have h1 : (p : ℤ) ∣ 1 := dvd_neg.mp hdvd
  have hle : (p : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) h1
  omega

lemma squarefree_of_sum_modEq {n : ℕ}
    (hs : Int.ModEq (n : ℤ)
      (∑ k ∈ Finset.range n, (Polynomial.Chebyshev.C ℤ ((n : ℤ) - 1)).eval (k : ℤ)) (-1)) :
    Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hp_dvd : p ∣ n := dvd_trans (dvd_mul_left p p) hpp
  have hp_dvd_div : p ∣ n / p := by
    obtain ⟨m, hm⟩ := hpp
    rw [hm, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
    exact dvd_mul_right p m
  have h1 : Int.ModEq (p : ℤ)
      (∑ k ∈ Finset.range n, (Polynomial.Chebyshev.C ℤ ((n : ℤ) - 1)).eval (k : ℤ)) (-1) :=
    hs.of_dvd (Int.ofNat_dvd.mpr hp_dvd)
  have h2 := sum_range_dvd_modEq (Polynomial.Chebyshev.C ℤ ((n : ℤ) - 1)) hp_dvd
  have h3 : Int.ModEq (p : ℤ) ((n / p : ℕ) : ℤ) 0 := by
    rw [Int.modEq_zero_iff_dvd]
    exact Int.ofNat_dvd.mpr hp_dvd_div
  have h4 : Int.ModEq (p : ℤ)
      (((n / p : ℕ) : ℤ) * ∑ k ∈ Finset.range p, (Polynomial.Chebyshev.C ℤ ((n : ℤ) - 1)).eval (k : ℤ))
      0 := by
    simpa using h3.mul_right (∑ k ∈ Finset.range p, (Polynomial.Chebyshev.C ℤ ((n : ℤ) - 1)).eval (k : ℤ))
  exact not_zero_modEq_neg_one hp.one_lt (h4.symm.trans (h2.symm.trans h1))

lemma odd_of_sum_modEq (h1 : H1) {n : ℕ} (hn : 1 < n) (hnp : ¬ n.Prime)
    (hsqf : Squarefree n)
    (hs : Int.ModEq (n : ℤ)
      (∑ k ∈ Finset.range n, (Polynomial.Chebyshev.C ℤ ((n : ℤ) - 1)).eval (k : ℤ)) (-1)) :
    Odd n := by
  by_contra hnotodd
  rw [Nat.not_odd_iff_even] at hnotodd
  have h2dvd : 2 ∣ n := even_iff_two_dvd.mp hnotodd
  have hdiv_gt1 : 1 < n / 2 := by
    by_contra hle
    have hdiv1 : n / 2 = 1 := by omega
    have hn2 : n = 2 := by omega
    exact hnp (hn2 ▸ Nat.prime_two)
  obtain ⟨p, hp, hpdvd_div⟩ := Nat.exists_prime_and_dvd (by omega : n / 2 ≠ 1)
  have hpdvd : p ∣ n := dvd_trans hpdvd_div (Nat.div_dvd_of_dvd h2dvd)
  have hp2 : p ≠ 2 := by
    intro heq
    subst heq
    have h4 : 2 * 2 ∣ n := by
      obtain ⟨m, hm⟩ := hpdvd_div
      refine ⟨m, ?_⟩
      have := Nat.div_mul_cancel h2dvd
      omega
    exact (Nat.squarefree_iff_prime_squarefree.mp hsqf 2 Nat.prime_two) h4
  have hp_odd : Odd p := hp.odd_of_ne_two hp2
  have hpm1_even : Even (p - 1) := by
    obtain ⟨t, ht⟩ := hp_odd
    exact ⟨t, by omega⟩
  have hpp1_even : Even (p + 1) := by
    obtain ⟨t, ht⟩ := hp_odd
    exact ⟨t + 1, by omega⟩
  have hnm1_odd : Odd (n - 1) := by
    obtain ⟨t, ht⟩ := hnotodd
    exact ⟨t - 1, by omega⟩
  have hnd1 : ¬ ((p - 1) ∣ (n - 1)) := fun hd =>
    Nat.not_even_iff_odd.mpr hnm1_odd (even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp hpm1_even) hd))
  have hnd2 : ¬ ((p + 1) ∣ (n - 1)) := fun hd =>
    Nat.not_even_iff_odd.mpr hnm1_odd (even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp hpp1_even) hd))
  have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have hcheb := h1 p hp hp2 (n - 1)
  rw [hcast, if_neg hnd1, if_neg hnd2, add_zero] at hcheb
  have hmod1 : Int.ModEq (p : ℤ)
      (∑ k ∈ Finset.range n, (Polynomial.Chebyshev.C ℤ ((n : ℤ) - 1)).eval (k : ℤ)) (-1) :=
    hs.of_dvd (Int.ofNat_dvd.mpr hpdvd)
  have hmod2 := sum_range_dvd_modEq (Polynomial.Chebyshev.C ℤ ((n : ℤ) - 1)) hpdvd
  have hmod3 : Int.ModEq (p : ℤ)
      (((n / p : ℕ) : ℤ) * ∑ k ∈ Finset.range p, (Polynomial.Chebyshev.C ℤ ((n : ℤ) - 1)).eval (k : ℤ))
      0 := by
    simpa using hcheb.mul_left ((n / p : ℕ) : ℤ)
  exact not_zero_modEq_neg_one hp.one_lt (hmod3.symm.trans (hmod2.symm.trans hmod1))

lemma signed_giuga_at_prime (h1 : H1) {n : ℕ} (hn : 1 < n) (hodd : Odd n)
    (hs : Int.ModEq (n : ℤ)
      (∑ k ∈ Finset.range n, (Polynomial.Chebyshev.C ℤ ((n : ℤ) - 1)).eval (k : ℤ)) (-1))
    {p : ℕ} (hp_mem : p ∈ n.primeFactors) :
    ((p - 1) ∣ (n - 1) ∧ ¬ ((p + 1) ∣ (n - 1)) ∧ Int.ModEq (p : ℤ) ((n / p : ℕ) : ℤ) 1) ∨
    ((p + 1) ∣ (n - 1) ∧ ¬ ((p - 1) ∣ (n - 1)) ∧ Int.ModEq (p : ℤ) ((n / p : ℕ) : ℤ) (-1)) := by
  have ⟨hp, hpdvd, _⟩ := Nat.mem_primeFactors.mp hp_mem
  have hp2 : p ≠ 2 := by
    intro heq
    subst heq
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hpdvd)
  have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have hcheb := h1 p hp hp2 (n - 1)
  rw [hcast] at hcheb
  have hmod1 : Int.ModEq (p : ℤ)
      (∑ k ∈ Finset.range n, (Polynomial.Chebyshev.C ℤ ((n : ℤ) - 1)).eval (k : ℤ)) (-1) :=
    hs.of_dvd (Int.ofNat_dvd.mpr hpdvd)
  have hmod2 := sum_range_dvd_modEq (Polynomial.Chebyshev.C ℤ ((n : ℤ) - 1)) hpdvd
  have hprod : Int.ModEq (p : ℤ)
      (((n / p : ℕ) : ℤ) * ((if (p - 1) ∣ (n - 1) then (-1 : ℤ) else 0) +
        (if (p + 1) ∣ (n - 1) then (1 : ℤ) else 0)))
      (-1) :=
    (hcheb.mul_left ((n / p : ℕ) : ℤ)).symm.trans (hmod2.symm.trans hmod1)
  by_cases hd1 : (p - 1) ∣ (n - 1)
  · by_cases hd2 : (p + 1) ∣ (n - 1)
    · rw [if_pos hd1, if_pos hd2] at hprod
      simp only [neg_add_cancel, mul_zero] at hprod
      exact False.elim (not_zero_modEq_neg_one hp.one_lt hprod)
    · left
      refine ⟨hd1, hd2, ?_⟩
      rw [if_pos hd1, if_neg hd2, add_zero, mul_neg, mul_one] at hprod
      simpa using hprod.neg
  · by_cases hd2 : (p + 1) ∣ (n - 1)
    · right
      refine ⟨hd2, hd1, ?_⟩
      rw [if_neg hd1, if_pos hd2, zero_add, mul_one] at hprod
      exact hprod
    · rw [if_neg hd1, if_neg hd2] at hprod
      simp only [add_zero, mul_zero] at hprod
      exact False.elim (not_zero_modEq_neg_one hp.one_lt hprod)

lemma prime_dvd_of_card_two {n p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hodd : Odd n) (hn : n = p * q)
    (hcond : ((q - 1) ∣ (n - 1) ∧ ¬ ((q + 1) ∣ (n - 1)) ∧ Int.ModEq (q : ℤ) ((n / q : ℕ) : ℤ) 1) ∨
             ((q + 1) ∣ (n - 1) ∧ ¬ ((q - 1) ∣ (n - 1)) ∧ Int.ModEq (q : ℤ) ((n / q : ℕ) : ℤ) (-1))) :
    False := by
  have hdiv : n / q = p := by rw [hn, Nat.mul_div_cancel _ hq.pos]
  rw [hdiv] at hcond
  have hp_odd : Odd p := by
    rcases Nat.even_or_odd p with he | ho
    · exfalso
      have : Even n := by rw [hn]; exact he.mul_right q
      exact Nat.not_even_iff_odd.mpr hodd this
    · exact ho
  have hq_odd : Odd q := by
    rcases Nat.even_or_odd q with he | ho
    · exfalso
      have : Even n := by rw [hn]; exact he.mul_left p
      exact Nat.not_even_iff_odd.mpr hodd this
    · exact ho
  rcases hcond with ⟨_, _, hmod⟩ | ⟨_, _, hmod⟩
  · have hdvd : (q : ℤ) ∣ (p : ℤ) - 1 := Int.modEq_iff_dvd.mp hmod.symm
    have hpos : (0 : ℤ) < (p : ℤ) - 1 := by have := hp.two_le; omega
    have hle := Int.le_of_dvd hpos hdvd
    omega
  · have hdvd : (q : ℤ) ∣ (p : ℤ) + 1 := by
      have := Int.modEq_iff_dvd.mp hmod.symm
      simpa [sub_neg_eq_add] using this
    have hpos : (0 : ℤ) < (p : ℤ) + 1 := by omega
    have hle := Int.le_of_dvd hpos hdvd
    have heq : q = p + 1 := by omega
    obtain ⟨a, ha⟩ := hp_odd
    obtain ⟨b, hb⟩ := hq_odd
    omega

lemma prime_dvd_of_card_three {n p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) (hn : n = p * q * r)
    (hcond : ((r - 1) ∣ (n - 1) ∧ ¬ ((r + 1) ∣ (n - 1)) ∧ Int.ModEq (r : ℤ) ((n / r : ℕ) : ℤ) 1) ∨
             ((r + 1) ∣ (n - 1) ∧ ¬ ((r - 1) ∣ (n - 1)) ∧ Int.ModEq (r : ℤ) ((n / r : ℕ) : ℤ) (-1))) :
    False := by
  have hdiv : n / r = p * q := by rw [hn, Nat.mul_div_cancel _ hr.pos]
  rw [hdiv] at hcond
  have hp2 : 2 ≤ p := hp.two_le
  have hq3 : 3 ≤ q := by omega
  have hr4 : 4 ≤ r := by omega
  have hpq_le : p * q ≤ (r - 2) * (r - 1) := Nat.mul_le_mul (by omega) (by omega)
  rcases hcond with ⟨hd1, _, hmod⟩ | ⟨hd1, _, hmod⟩
  · have h1 : (r : ℤ) ∣ ((p * q : ℕ) : ℤ) - 1 := Int.modEq_iff_dvd.mp hmod.symm
    have h2 : ((r - 1 : ℕ) : ℤ) ∣ ((p * q : ℕ) : ℤ) - 1 := by
      have hd1z : ((r - 1 : ℕ) : ℤ) ∣ ((n - 1 : ℕ) : ℤ) := Int.ofNat_dvd.mpr hd1
      have hcast1 : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
      have hcast2 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
        have : 1 ≤ n := by rw [hn]; exact Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos
        omega
      rw [hcast1, hcast2] at hd1z
      have hsplit : (n : ℤ) - 1 = ((r : ℤ) - 1) * ((p * q : ℕ) : ℤ) + (((p * q : ℕ) : ℤ) - 1) := by
        rw [hn]; push_cast; ring
      rw [hsplit] at hd1z
      rw [hcast1]
      exact (dvd_add_right (dvd_mul_right ((r : ℤ) - 1) _)).mp hd1z
    have hcop : IsCoprime (r : ℤ) ((r - 1 : ℕ) : ℤ) := by
      refine ⟨1, -1, ?_⟩
      have : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
      rw [this]; ring
    have hmul : (r : ℤ) * ((r - 1 : ℕ) : ℤ) ∣ ((p * q : ℕ) : ℤ) - 1 := hcop.mul_dvd h1 h2
    have hpos : (0 : ℤ) < ((p * q : ℕ) : ℤ) - 1 := by
      have : 2 ≤ p * q := by nlinarith
      omega
    have hle := Int.le_of_dvd hpos hmul
    have hcast1 : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
    rw [hcast1] at hle
    have hpq_le_z : ((p * q : ℕ) : ℤ) ≤ ((r : ℤ) - 2) * ((r : ℤ) - 1) := by
      have : ((p * q : ℕ) : ℤ) ≤ (((r - 2) * (r - 1) : ℕ) : ℤ) := Int.ofNat_le.mpr hpq_le
      have h1' : ((r - 2 : ℕ) : ℤ) = (r : ℤ) - 2 := by omega
      have h2' : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
      simpa [Nat.cast_mul, h1', h2'] using this
    nlinarith
  · have h1 : (r : ℤ) ∣ ((p * q : ℕ) : ℤ) + 1 := by
      have := Int.modEq_iff_dvd.mp hmod.symm
      simpa [sub_neg_eq_add] using this
    have h2 : ((r + 1 : ℕ) : ℤ) ∣ ((p * q : ℕ) : ℤ) + 1 := by
      have hd1z : ((r + 1 : ℕ) : ℤ) ∣ ((n - 1 : ℕ) : ℤ) := Int.ofNat_dvd.mpr hd1
      have hcast2 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
        have : 1 ≤ n := by rw [hn]; exact Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos
        omega
      rw [hcast2] at hd1z
      have hsplit : (n : ℤ) - 1 = ((r + 1 : ℕ) : ℤ) * ((p * q : ℕ) : ℤ) - (((p * q : ℕ) : ℤ) + 1) := by
        rw [hn]; push_cast; ring
      rw [hsplit] at hd1z
      exact (dvd_sub_right (dvd_mul_right ((r + 1 : ℕ) : ℤ) _)).mp hd1z
    have hcop : IsCoprime (r : ℤ) ((r + 1 : ℕ) : ℤ) := by
      refine ⟨-1, 1, ?_⟩
      push_cast; ring
    have hmul : (r : ℤ) * ((r + 1 : ℕ) : ℤ) ∣ ((p * q : ℕ) : ℤ) + 1 := hcop.mul_dvd h1 h2
    have hpos : (0 : ℤ) < ((p * q : ℕ) : ℤ) + 1 := by omega
    have hle := Int.le_of_dvd hpos hmul
    have hpq_le_z : ((p * q : ℕ) : ℤ) ≤ ((r : ℤ) - 2) * ((r : ℤ) - 1) := by
      have : ((p * q : ℕ) : ℤ) ≤ (((r - 2) * (r - 1) : ℕ) : ℤ) := Int.ofNat_le.mpr hpq_le
      have h1' : ((r - 2 : ℕ) : ℤ) = (r : ℤ) - 2 := by omega
      have h2' : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
      simpa [Nat.cast_mul, h1', h2'] using this
    push_cast at hle
    nlinarith

lemma odd_primes_four_bounds {p1 p2 p3 p4 : ℕ}
    (hp1 : p1.Prime) (hp2 : p2.Prime) (hp3 : p3.Prime) (hp4 : p4.Prime)
    (hodd1 : Odd p1) (h12 : p1 < p2) (h23 : p2 < p3) (h34 : p3 < p4) :
    3 ≤ p1 ∧ 5 ≤ p2 ∧ 7 ≤ p3 ∧ 11 ≤ p4 := by
  have h1 : 3 ≤ p1 := by
    have := hp1.two_le
    obtain ⟨t, ht⟩ := hodd1
    omega
  have h2 : 5 ≤ p2 := by
    have hne4 : p2 ≠ 4 := fun h => by subst h; exact absurd hp2 (by decide)
    omega
  have h3 : 7 ≤ p3 := by
    have hne6 : p3 ≠ 6 := fun h => by subst h; exact absurd hp3 (by decide)
    omega
  have h4 : 11 ≤ p4 := by
    have hne8 : p4 ≠ 8 := fun h => by subst h; exact absurd hp4 (by decide)
    have hne9 : p4 ≠ 9 := fun h => by subst h; exact absurd hp4 (by decide)
    have hne10 : p4 ≠ 10 := fun h => by subst h; exact absurd hp4 (by decide)
    omega
  exact ⟨h1, h2, h3, h4⟩

lemma prime_dvd_of_card_four {n p1 p2 p3 p4 : ℕ}
    (hp1 : p1.Prime) (hp2 : p2.Prime) (hp3 : p3.Prime) (hp4 : p4.Prime)
    (h12 : p1 < p2) (h23 : p2 < p3) (h34 : p3 < p4)
    (hodd : Odd n) (hn : n = p1 * p2 * p3 * p4)
    (hc1 : Int.ModEq (p1 : ℤ) ((n / p1 : ℕ) : ℤ) 1 ∨ Int.ModEq (p1 : ℤ) ((n / p1 : ℕ) : ℤ) (-1))
    (hc2 : Int.ModEq (p2 : ℤ) ((n / p2 : ℕ) : ℤ) 1 ∨ Int.ModEq (p2 : ℤ) ((n / p2 : ℕ) : ℤ) (-1))
    (hc3 : Int.ModEq (p3 : ℤ) ((n / p3 : ℕ) : ℤ) 1 ∨ Int.ModEq (p3 : ℤ) ((n / p3 : ℕ) : ℤ) (-1))
    (hc4 : Int.ModEq (p4 : ℤ) ((n / p4 : ℕ) : ℤ) 1 ∨ Int.ModEq (p4 : ℤ) ((n / p4 : ℕ) : ℤ) (-1)) :
    False := by
  have hodd1 : Odd p1 := by
    rcases Nat.even_or_odd p1 with he | ho
    · exfalso
      have : Even n := by rw [hn]; exact ((he.mul_right p2).mul_right p3).mul_right p4
      exact Nat.not_even_iff_odd.mpr hodd this
    · exact ho
  obtain ⟨hb1, hb2, hb3, hb4⟩ := odd_primes_four_bounds hp1 hp2 hp3 hp4 hodd1 h12 h23 h34
  have hsign : ∀ {p m : ℕ},
      (Int.ModEq (p : ℤ) (m : ℤ) 1 ∨ Int.ModEq (p : ℤ) (m : ℤ) (-1)) →
      ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ Int.ModEq (p : ℤ) (e * (m : ℤ)) 1 := by
    intro p m h
    rcases h with h | h
    · exact ⟨1, Or.inl rfl, by simpa using h⟩
    · exact ⟨-1, Or.inr rfl, by simpa using h.neg⟩
  obtain ⟨e1, he1, hm1⟩ := hsign hc1
  obtain ⟨e2, he2, hm2⟩ := hsign hc2
  obtain ⟨e3, he3, hm3⟩ := hsign hc3
  obtain ⟨e4, he4, hm4⟩ := hsign hc4
  set q1 : ℕ := n / p1
  set q2 : ℕ := n / p2
  set q3 : ℕ := n / p3
  set q4 : ℕ := n / p4
  have hd1 : q1 = p2 * p3 * p4 := by
    dsimp [q1]; rw [hn, show p1 * p2 * p3 * p4 = p1 * (p2 * p3 * p4) by ring, Nat.mul_div_cancel_left _ hp1.pos]
  have hd2 : q2 = p1 * p3 * p4 := by
    dsimp [q2]; rw [hn, show p1 * p2 * p3 * p4 = p2 * (p1 * p3 * p4) by ring, Nat.mul_div_cancel_left _ hp2.pos]
  have hd3 : q3 = p1 * p2 * p4 := by
    dsimp [q3]; rw [hn, show p1 * p2 * p3 * p4 = p3 * (p1 * p2 * p4) by ring, Nat.mul_div_cancel_left _ hp3.pos]
  have hd4 : q4 = p1 * p2 * p3 := by
    dsimp [q4]; rw [hn, show p1 * p2 * p3 * p4 = p4 * (p1 * p2 * p3) by ring, Nat.mul_div_cancel_left _ hp4.pos]
  set S : ℤ := e1 * (q1 : ℤ) + e2 * (q2 : ℤ) + e3 * (q3 : ℤ) + e4 * (q4 : ℤ) - 1
  have hS1 : (p1 : ℤ) ∣ S := by
    have hsub : (p1 : ℤ) ∣ e1 * (q1 : ℤ) - 1 := Int.modEq_iff_dvd.mp hm1.symm
    have h2 : (p1 : ℤ) ∣ e2 * (q2 : ℤ) := by
      rw [hd2]; push_cast; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
    have h3 : (p1 : ℤ) ∣ e3 * (q3 : ℤ) := by
      rw [hd3]; push_cast; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
    have h4 : (p1 : ℤ) ∣ e4 * (q4 : ℤ) := by
      rw [hd4]; push_cast; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
    have hrew : S = (e1 * (q1 : ℤ) - 1) + e2 * (q2 : ℤ) + e3 * (q3 : ℤ) + e4 * (q4 : ℤ) := by
      dsimp [S]; ring
    rw [hrew]
    exact dvd_add (dvd_add (dvd_add hsub h2) h3) h4
  have hS2 : (p2 : ℤ) ∣ S := by
    have hsub : (p2 : ℤ) ∣ e2 * (q2 : ℤ) - 1 := Int.modEq_iff_dvd.mp hm2.symm
    have h1 : (p2 : ℤ) ∣ e1 * (q1 : ℤ) := by
      rw [hd1]; push_cast; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
    have h3 : (p2 : ℤ) ∣ e3 * (q3 : ℤ) := by
      rw [hd3]; push_cast; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
    have h4 : (p2 : ℤ) ∣ e4 * (q4 : ℤ) := by
      rw [hd4]; push_cast; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
    have hrew : S = (e2 * (q2 : ℤ) - 1) + e1 * (q1 : ℤ) + e3 * (q3 : ℤ) + e4 * (q4 : ℤ) := by
      dsimp [S]; ring
    rw [hrew]
    exact dvd_add (dvd_add (dvd_add hsub h1) h3) h4
  have hS3 : (p3 : ℤ) ∣ S := by
    have hsub : (p3 : ℤ) ∣ e3 * (q3 : ℤ) - 1 := Int.modEq_iff_dvd.mp hm3.symm
    have h1 : (p3 : ℤ) ∣ e1 * (q1 : ℤ) := by
      rw [hd1]; push_cast; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
    have h2 : (p3 : ℤ) ∣ e2 * (q2 : ℤ) := by
      rw [hd2]; push_cast; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
    have h4 : (p3 : ℤ) ∣ e4 * (q4 : ℤ) := by
      rw [hd4]; push_cast; exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
    have hrew : S = (e3 * (q3 : ℤ) - 1) + e1 * (q1 : ℤ) + e2 * (q2 : ℤ) + e4 * (q4 : ℤ) := by
      dsimp [S]; ring
    rw [hrew]
    exact dvd_add (dvd_add (dvd_add hsub h1) h2) h4
  have hS4 : (p4 : ℤ) ∣ S := by
    have hsub : (p4 : ℤ) ∣ e4 * (q4 : ℤ) - 1 := Int.modEq_iff_dvd.mp hm4.symm
    have h1 : (p4 : ℤ) ∣ e1 * (q1 : ℤ) := by
      rw [hd1]; push_cast; exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
    have h2 : (p4 : ℤ) ∣ e2 * (q2 : ℤ) := by
      rw [hd2]; push_cast; exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
    have h3 : (p4 : ℤ) ∣ e3 * (q3 : ℤ) := by
      rw [hd3]; push_cast; exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
    have hrew : S = (e4 * (q4 : ℤ) - 1) + e1 * (q1 : ℤ) + e2 * (q2 : ℤ) + e3 * (q3 : ℤ) := by
      dsimp [S]; ring
    rw [hrew]
    exact dvd_add (dvd_add (dvd_add hsub h1) h2) h3
  have hcop : ∀ {a b : ℕ}, a.Prime → b.Prime → a ≠ b → IsCoprime (a : ℤ) (b : ℤ) :=
    fun ha hb hab => (ha.coprime_iff_not_dvd.mpr fun h => hab ((hb.dvd_iff_eq ha.ne_one).mp h).symm).isCoprime
  have hS12 : (p1 : ℤ) * (p2 : ℤ) ∣ S := (hcop hp1 hp2 (by omega)).mul_dvd hS1 hS2
  have hS123 : (p1 : ℤ) * (p2 : ℤ) * (p3 : ℤ) ∣ S :=
    ((hcop hp1 hp3 (by omega)).mul_left (hcop hp2 hp3 (by omega))).mul_dvd hS12 hS3
  have hSn : (n : ℤ) ∣ S := by
    have hcop123_4 : IsCoprime ((p1 : ℤ) * (p2 : ℤ) * (p3 : ℤ)) (p4 : ℤ) :=
      ((hcop hp1 hp4 (by omega)).mul_left (hcop hp2 hp4 (by omega))).mul_left (hcop hp3 hp4 (by omega))
    have hmul := hcop123_4.mul_dvd hS123 hS4
    rw [hn]; push_cast; exact hmul
  have hS_ne : S ≠ 0 := by
    have hdiv_odd : ∀ d : ℕ, d ∣ n → Odd (n / d) := by
      intro d hd
      rcases Nat.even_or_odd (n / d) with he | ho
      · exfalso
        have : Even n := by rw [← Nat.div_mul_cancel hd]; exact he.mul_right d
        exact Nat.not_even_iff_odd.mpr hodd this
      · exact ho
    have ho1 : Odd q1 := hdiv_odd p1 (by rw [hn]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _)
    have ho2 : Odd q2 := hdiv_odd p2 (by rw [hn]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _)
    have ho3 : Odd q3 := hdiv_odd p3 (by rw [hn]; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
    have ho4 : Odd q4 := hdiv_odd p4 (by rw [hn]; exact dvd_mul_left _ _)
    have hm2_eq : S % 2 = 1 := by
      obtain ⟨k1, hk1⟩ := ho1
      obtain ⟨k2, hk2⟩ := ho2
      obtain ⟨k3, hk3⟩ := ho3
      obtain ⟨k4, hk4⟩ := ho4
      have hS_eq : S = e1 * (2 * (k1 : ℤ) + 1) + e2 * (2 * (k2 : ℤ) + 1) +
          e3 * (2 * (k3 : ℤ) + 1) + e4 * (2 * (k4 : ℤ) + 1) - 1 := by
        dsimp [S]; rw [hk1, hk2, hk3, hk4]; push_cast; ring
      rw [hS_eq]
      rcases he1 with rfl | rfl <;> rcases he2 with rfl | rfl <;>
        rcases he3 with rfl | rfl <;> rcases he4 with rfl | rfl <;> omega
    omega
  obtain ⟨k, hk⟩ := hSn
  have hk_ne : k ≠ 0 := fun h => hS_ne (by rw [hk, h, mul_zero])
  have hn_le_absS : (n : ℤ) ≤ |S| := by
    rw [hk, abs_mul, abs_of_nonneg (Int.natCast_nonneg n)]
    have hk1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk_ne
    nlinarith
  have habs_term : ∀ e : ℤ, ∀ m : ℕ, (e = 1 ∨ e = -1) → |e * (m : ℤ)| = (m : ℤ) := by
    intro e m he
    rcases he with rfl | rfl <;> simp [abs_of_nonneg (Int.natCast_nonneg m)]
  have habs_S : |S| ≤ (q1 : ℤ) + (q2 : ℤ) + (q3 : ℤ) + (q4 : ℤ) + 1 := by
    have h1 := abs_sub (e1 * (q1 : ℤ) + e2 * (q2 : ℤ) + e3 * (q3 : ℤ) + e4 * (q4 : ℤ)) 1
    have h2 := abs_add_le (e1 * (q1 : ℤ) + e2 * (q2 : ℤ) + e3 * (q3 : ℤ)) (e4 * (q4 : ℤ))
    have h3 := abs_add_le (e1 * (q1 : ℤ) + e2 * (q2 : ℤ)) (e3 * (q3 : ℤ))
    have h4 := abs_add_le (e1 * (q1 : ℤ)) (e2 * (q2 : ℤ))
    rw [habs_term e1 q1 he1, habs_term e2 q2 he2] at h4
    rw [habs_term e3 q3 he3] at h3
    rw [habs_term e4 q4 he4] at h2
    simp only [abs_one] at h1
    change |e1 * (q1 : ℤ) + e2 * (q2 : ℤ) + e3 * (q3 : ℤ) + e4 * (q4 : ℤ) - 1| ≤ _
    linarith
  have hq1 : 3 * (q1 : ℤ) ≤ (n : ℤ) := by
    have : p1 * q1 = n := Nat.mul_div_cancel' (by rw [hn]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _)
    have : 3 * q1 ≤ p1 * q1 := Nat.mul_le_mul_right _ hb1
    omega
  have hq2 : 5 * (q2 : ℤ) ≤ (n : ℤ) := by
    have : p2 * q2 = n := Nat.mul_div_cancel' (by rw [hn]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _)
    have : 5 * q2 ≤ p2 * q2 := Nat.mul_le_mul_right _ hb2
    omega
  have hq3 : 7 * (q3 : ℤ) ≤ (n : ℤ) := by
    have : p3 * q3 = n := Nat.mul_div_cancel' (by rw [hn]; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
    have : 7 * q3 ≤ p3 * q3 := Nat.mul_le_mul_right _ hb3
    omega
  have hq4 : 11 * (q4 : ℤ) ≤ (n : ℤ) := by
    have : p4 * q4 = n := Nat.mul_div_cancel' (by rw [hn]; exact dvd_mul_left _ _)
    have : 11 * q4 ≤ p4 * q4 := Nat.mul_le_mul_right _ hb4
    omega
  have hn_ge : (1155 : ℤ) ≤ (n : ℤ) := by
    have : 3 * 5 * 7 * 11 ≤ p1 * p2 * p3 * p4 :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hb1 hb2) hb3) hb4
    rw [hn]; omega
  linarith

lemma prod_orderEmbOfFin {s : Finset ℕ} {k : ℕ} (hk : s.card = k) :
    ∏ i : Fin k, s.orderEmbOfFin hk i = ∏ x ∈ s, x := by
  let e := s.orderEmbOfFin hk
  have hrange : Finset.univ.image (fun i : Fin k => e i) = s := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact Finset.orderEmbOfFin_mem s hk i
    · intro hx
      have hmem : x ∈ Set.range e := by
        rw [Finset.range_orderEmbOfFin s hk]
        exact hx
      exact hmem
  conv_rhs => rw [← hrange]
  rw [Finset.prod_image]
  intro a _ b _ hab
  exact e.injective hab

lemma five_le_card_primeFactors {n : ℕ} (hn : 1 < n) (hnp : ¬ n.Prime)
    (hsqf : Squarefree n) (hodd : Odd n)
    (hcond : ∀ p ∈ n.primeFactors,
      ((p - 1) ∣ (n - 1) ∧ ¬ ((p + 1) ∣ (n - 1)) ∧ Int.ModEq (p : ℤ) ((n / p : ℕ) : ℤ) 1) ∨
      ((p + 1) ∣ (n - 1) ∧ ¬ ((p - 1) ∣ (n - 1)) ∧ Int.ModEq (p : ℤ) ((n / p : ℕ) : ℤ) (-1))) :
    5 ≤ n.primeFactors.card := by
  have hprod : ∏ p ∈ n.primeFactors, p = n := Nat.prod_primeFactors_of_squarefree hsqf
  by_contra hlt
  have hcases : n.primeFactors.card = 0 ∨ n.primeFactors.card = 1 ∨
      n.primeFactors.card = 2 ∨ n.primeFactors.card = 3 ∨ n.primeFactors.card = 4 := by omega
  rcases hcases with hc | hc | hc | hc | hc
  · have hemp : n.primeFactors = ∅ := Finset.card_eq_zero.mp hc
    rw [hemp, Finset.prod_empty] at hprod
    omega
  · let e := n.primeFactors.orderEmbOfFin hc
    have hpe : e 0 = n := by
      have hp := prod_orderEmbOfFin hc
      rw [hprod, Fin.prod_univ_one] at hp
      exact hp
    have hmem : e 0 ∈ n.primeFactors := Finset.orderEmbOfFin_mem n.primeFactors hc 0
    exact hnp (hpe ▸ Nat.prime_of_mem_primeFactors hmem)
  · let e := n.primeFactors.orderEmbOfFin hc
    have hpe : e 0 * e 1 = n := by
      have hp := prod_orderEmbOfFin hc
      rw [hprod, Fin.prod_univ_two] at hp
      exact hp
    have hm0 := Finset.orderEmbOfFin_mem n.primeFactors hc 0
    have hm1 := Finset.orderEmbOfFin_mem n.primeFactors hc 1
    exact prime_dvd_of_card_two (Nat.prime_of_mem_primeFactors hm0)
      (Nat.prime_of_mem_primeFactors hm1) (e.strictMono (by decide : (0 : Fin 2) < 1))
      hodd hpe.symm (hcond (e 1) hm1)
  · let e := n.primeFactors.orderEmbOfFin hc
    have hpe : e 0 * e 1 * e 2 = n := by
      have hp := prod_orderEmbOfFin hc
      rw [hprod, Fin.prod_univ_three] at hp
      linarith [hp]
    have hm0 := Finset.orderEmbOfFin_mem n.primeFactors hc 0
    have hm1 := Finset.orderEmbOfFin_mem n.primeFactors hc 1
    have hm2 := Finset.orderEmbOfFin_mem n.primeFactors hc 2
    exact prime_dvd_of_card_three (Nat.prime_of_mem_primeFactors hm0)
      (Nat.prime_of_mem_primeFactors hm1) (Nat.prime_of_mem_primeFactors hm2)
      (e.strictMono (by decide : (0 : Fin 3) < 1))
      (e.strictMono (by decide : (1 : Fin 3) < 2))
      hpe.symm (hcond (e 2) hm2)
  · let e := n.primeFactors.orderEmbOfFin hc
    have hpe : e 0 * e 1 * e 2 * e 3 = n := by
      have hp := prod_orderEmbOfFin hc
      rw [hprod, Fin.prod_univ_four] at hp
      linarith [hp]
    have hm0 := Finset.orderEmbOfFin_mem n.primeFactors hc 0
    have hm1 := Finset.orderEmbOfFin_mem n.primeFactors hc 1
    have hm2 := Finset.orderEmbOfFin_mem n.primeFactors hc 2
    have hm3 := Finset.orderEmbOfFin_mem n.primeFactors hc 3
    have drop : ∀ {p : ℕ}, p ∈ n.primeFactors →
        Int.ModEq (p : ℤ) ((n / p : ℕ) : ℤ) 1 ∨ Int.ModEq (p : ℤ) ((n / p : ℕ) : ℤ) (-1) := by
      intro p hp
      rcases hcond p hp with ⟨_, _, h⟩ | ⟨_, _, h⟩
      · exact Or.inl h
      · exact Or.inr h
    exact prime_dvd_of_card_four (Nat.prime_of_mem_primeFactors hm0)
      (Nat.prime_of_mem_primeFactors hm1) (Nat.prime_of_mem_primeFactors hm2)
      (Nat.prime_of_mem_primeFactors hm3)
      (e.strictMono (by decide : (0 : Fin 4) < 1))
      (e.strictMono (by decide : (1 : Fin 4) < 2))
      (e.strictMono (by decide : (2 : Fin 4) < 3))
      hodd hpe.symm (drop hm0) (drop hm1) (drop hm2) (drop hm3)

theorem main : H1 → H2 → type_of% @OMA.S_mse_2615963.main := by
  intro h1 h2 n hn
  constructor
  · intro hp
    by_cases hp2 : n = 2
    · subst hp2
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
      norm_num [Polynomial.Chebyshev.C_one, Int.ModEq]
    · have hcheb := h1 n hp hp2 (n - 1)
      have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
      have hd1 : (n - 1) ∣ (n - 1) := dvd_refl _
      have hd2 : ¬ ((n + 1) ∣ (n - 1)) := by
        intro hd
        have hle := Nat.le_of_dvd (by omega) hd
        omega
      rw [hcast, if_pos hd1, if_neg hd2, add_zero] at hcheb
      exact hcheb
  · intro hs
    by_contra hnp
    have hsqf : Squarefree n := squarefree_of_sum_modEq hs
    have hodd : Odd n := odd_of_sum_modEq h1 hn hnp hsqf hs
    have hcond : ∀ p ∈ n.primeFactors,
        ((p - 1) ∣ (n - 1) ∧ ¬ ((p + 1) ∣ (n - 1)) ∧ Int.ModEq (p : ℤ) ((n / p : ℕ) : ℤ) 1) ∨
        ((p + 1) ∣ (n - 1) ∧ ¬ ((p - 1) ∣ (n - 1)) ∧ Int.ModEq (p : ℤ) ((n / p : ℕ) : ℤ) (-1)) :=
      fun p hp => signed_giuga_at_prime h1 hn hodd hs hp
    have hcard : 5 ≤ n.primeFactors.card := five_le_card_primeFactors hn hnp hsqf hodd hcond
    exact h2 n hn hnp hsqf hodd hcard hcond

end OMA.R_mse_2615963_R3
