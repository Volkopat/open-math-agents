import OMAStatements.S_oeis_a328308

-- Problem: A328308: a(n) = 1 if k-th arithmetic derivative of n is zero for some k, otherwise 0.
-- Upstream: formal-conjectures statements/oeis-a328308.lean:0 (declaration OMA.S_oeis_a328308.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: for n > 0 the iterates of D starting at n reach 0 exactly when those starting at D(n)
-- do, so a(n) = a(D(n)), which is the claim when every exponent satisfies e < p. If p^e || n with
-- e >= p, then p^p | n; for x > 0 with p^p | x, every term e_q * x/q of D(x) is a multiple of p^p
-- (for q = p use e_p = p, where the term is x, or e_p > p, where p^p | x/p; for q <> p use
-- coprimality), and the p-term is positive. So all iterates are positive and a(n) = 0.

namespace N18A328308

open OMA.S_oeis_a328308

theorem term_dvd (x p q : ℕ) (hx : x ≠ 0) (hp : p.Prime) (hpx : p ^ p ∣ x)
    (hq : q ∈ x.primeFactors) : p ^ p ∣ x.factorization q * (x / q) := by
  rw [Nat.mem_primeFactors] at hq
  obtain ⟨hqp, hqx, _⟩ := hq
  by_cases hpq : q = p
  · rw [hpq] at hqx ⊢
    have he : p ≤ x.factorization p := (hp.pow_dvd_iff_le_factorization hx).mp hpx
    rcases Nat.eq_or_lt_of_le he with h1 | h2
    · rw [← h1, Nat.mul_div_cancel' hqx]
      exact hpx
    · have h3 : p ^ (p + 1) ∣ x := (hp.pow_dvd_iff_le_factorization hx).mpr h2
      have h4 : p ^ p ∣ x / p := by
        apply Nat.dvd_div_of_mul_dvd
        rw [← pow_succ']
        exact h3
      exact dvd_mul_of_dvd_right h4 _
  · have hcop : Nat.Coprime (p ^ p) q := by
      apply Nat.Coprime.pow_left
      exact (Nat.coprime_primes hp hqp).mpr (fun h => hpq h.symm)
    have h5 : p ^ p ∣ q * (x / q) := by
      rw [Nat.mul_div_cancel' hqx]
      exact hpx
    exact dvd_mul_of_dvd_right (hcop.dvd_of_dvd_mul_left h5) _

theorem D_dvd (x p : ℕ) (hx : x ≠ 0) (hp : p.Prime) (hpx : p ^ p ∣ x) : p ^ p ∣ D x := by
  unfold D
  exact Finset.dvd_sum (fun q hq => term_dvd x p q hx hp hpx hq)

theorem D_ne_zero (x p : ℕ) (hx : x ≠ 0) (hp : p.Prime) (hpx : p ^ p ∣ x) : D x ≠ 0 := by
  have hpdx : p ∣ x := (dvd_pow_self p hp.ne_zero).trans hpx
  have hmem : p ∈ x.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdx, hx⟩
  have hpos : 0 < x.factorization p * (x / p) := by
    have h1 : 0 < x.factorization p := Nat.Prime.factorization_pos_of_dvd hp hx hpdx
    have h2 : 0 < x / p := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hx) hpdx) hp.pos
    exact Nat.mul_pos h1 h2
  have hle : x.factorization p * (x / p) ≤ D x := by
    unfold D
    exact Finset.single_le_sum (f := fun q => x.factorization q * (x / q))
      (fun q _ => Nat.zero_le _) hmem
  omega

theorem iter_pp (p : ℕ) (hp : p.Prime) :
    ∀ k x : ℕ, x ≠ 0 → p ^ p ∣ x → D^[k] x ≠ 0 ∧ p ^ p ∣ D^[k] x := by
  intro k
  induction k with
  | zero =>
    intro x hx hpx
    exact ⟨hx, hpx⟩
  | succ k ih =>
    intro x hx hpx
    have e : D^[k + 1] x = D^[k] (D x) := Function.iterate_succ_apply D k x
    rw [e]
    exact ih (D x) (D_ne_zero x p hx hp hpx) (D_dvd x p hx hp hpx)

theorem a_eq_zero (x p : ℕ) (hx : x ≠ 0) (hp : p.Prime) (hpx : p ^ p ∣ x) : a x = 0 := by
  have hne : ¬ ∃ k : ℕ, D^[k] x = 0 := by
    rintro ⟨k, hk⟩
    exact (iter_pp p hp k x hx hpx).1 hk
  unfold a
  rw [if_neg hne]

theorem main0 : a 0 = 1 := by
  have h : ∃ k : ℕ, D^[k] 0 = 0 := ⟨0, rfl⟩
  unfold a
  rw [if_pos h]

theorem main1 (n : ℕ) (hn : 0 < n) : a n = A359550 n * a (D n) := by
  by_cases hall : ∀ p ∈ n.primeFactors, n.factorization p < p
  · have hA : A359550 n = 1 := by
      unfold A359550
      rw [if_neg (by omega : ¬ n = 0)]
      apply Finset.prod_eq_one
      intro p hp
      show (if n.factorization p < p then 1 else 0) = 1
      rw [if_pos (hall p hp)]
    have hiff : (∃ k : ℕ, D^[k] n = 0) ↔ (∃ k : ℕ, D^[k] (D n) = 0) := by
      constructor
      · rintro ⟨k, hk⟩
        cases k with
        | zero => exact absurd (show n = 0 from hk) (by omega)
        | succ k => exact ⟨k, (Function.iterate_succ_apply D k n).symm.trans hk⟩
      · rintro ⟨k, hk⟩
        exact ⟨k + 1, (Function.iterate_succ_apply D k n).trans hk⟩
    rw [hA, one_mul]
    unfold a
    by_cases h : ∃ k : ℕ, D^[k] n = 0
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
  · have hex : ∃ p, p ∈ n.primeFactors ∧ p ≤ n.factorization p := by
      by_contra hno
      apply hall
      intro p hp
      by_contra hlt
      exact hno ⟨p, hp, by omega⟩
    obtain ⟨p, hp, hle⟩ := hex
    have hp' := Nat.mem_primeFactors.mp hp
    have hpx : p ^ p ∣ n := (hp'.1.pow_dvd_iff_le_factorization (by omega)).mpr hle
    have hA : A359550 n = 0 := by
      unfold A359550
      rw [if_neg (by omega : ¬ n = 0)]
      apply Finset.prod_eq_zero hp
      show (if n.factorization p < p then 1 else 0) = 0
      rw [if_neg (by omega : ¬ n.factorization p < p)]
    rw [hA, zero_mul, a_eq_zero n p (by omega) hp'.1 hpx]

end N18A328308

open OMA.S_oeis_a328308 N18A328308 in
theorem OMA.solution : type_of% @OMA.S_oeis_a328308.main := by
  exact ⟨main0, fun n hn => main1 n hn⟩
