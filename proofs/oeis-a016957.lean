import OMAStatements.S_oeis_a016957

/-!
# Proof of Rascoe's conjecture on A016957 (`a(n) = 6n + 4`)

* `σ(m)` is odd iff every odd prime has even exponent in `m` (`odd_sigma_iff`), so for
  `m = 6k + 4` the abundance is odd iff `m` is a square: twice a square is impossible mod 3.
* `A186423 (4t + j)` has an explicit closed form; its odd values are `6t² + 4t + 1` and
  `6t² + 8t + 3`, i.e. `t - 1` runs over the `k` with `6k + 4 = (6t + 2)²` or `(6t + 4)²`.
-/

namespace OMA.S_oeis_a016957.Proof

open OMA.S_oeis_a016957 ArithmeticFunction
open scoped ArithmeticFunction.sigma

lemma odd_prod_iff {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    Odd (∏ i ∈ s, f i) ↔ ∀ i ∈ s, Odd (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Nat.odd_mul, ih, Finset.forall_mem_insert]

lemma odd_sigma_prime_pow {p e : ℕ} (hp : p.Prime) :
    Odd (σ 1 (p ^ e)) ↔ (p ≠ 2 → Even e) := by
  rw [sigma_one_apply_prime_pow hp]
  by_cases h2 : p = 2
  · subst h2
    simp only [ne_eq, not_true_eq_false, IsEmpty.forall_iff, iff_true]
    rw [Finset.sum_range_succ', Nat.odd_add]
    have : ∑ i ∈ Finset.range e, 2 ^ (i + 1) = 2 * ∑ i ∈ Finset.range e, 2 ^ i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]; simp
  · have hpo : Odd p := hp.odd_of_ne_two h2
    simp only [ne_eq, h2, not_false_eq_true, forall_const]
    rw [Nat.odd_iff, Finset.sum_nat_mod,
      Finset.sum_congr rfl (fun i _ => Nat.odd_iff.mp (hpo.pow (n := i))), Nat.even_iff]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    omega

lemma odd_sigma_iff {m : ℕ} (hm : m ≠ 0) :
    Odd (σ 1 m) ↔ ∀ p ∈ m.primeFactors, p ≠ 2 → Even (m.factorization p) := by
  rw [isMultiplicative_sigma.multiplicative_factorization (σ 1) hm, Finsupp.prod,
    Nat.support_factorization, odd_prod_iff]
  exact forall₂_congr fun p hp => odd_sigma_prime_pow (Nat.prime_of_mem_primeFactors hp)

lemma not_two_mul_sq (k b : ℕ) : 6 * k + 4 ≠ 2 * b ^ 2 := by
  intro h
  have h' : b ^ 2 = 3 * k + 2 := by omega
  have hz : ((b : ZMod 3)) ^ 2 = 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod 3)) h'
    push_cast at this
    rw [this]
    have : (3 : ZMod 3) = 0 := by decide
    rw [this]; ring
  generalize (b : ZMod 3) = x at hz
  revert x hz; decide

lemma odd_sigma_iff_isSquare (k : ℕ) : Odd (σ 1 (6 * k + 4)) ↔ IsSquare (6 * k + 4) := by
  rw [odd_sigma_iff (by omega)]
  constructor
  · intro h
    obtain ⟨c, b, hc, hb, hbc, hsq⟩ := Nat.sq_mul_squarefree_of_pos (show 0 < 6 * k + 4 by omega)
    by_cases hc1 : c = 1
    · subst hc1; exact ⟨b, by rw [← hbc]; ring⟩
    exfalso
    -- every prime factor of `c` is `2`
    have hall : ∀ q ∈ c.primeFactors, q = 2 := by
      intro q hq
      have hqp := Nat.prime_of_mem_primeFactors hq
      have hqc := Nat.dvd_of_mem_primeFactors hq
      by_contra hq2
      have hmem : q ∈ (6 * k + 4).primeFactors := by
        rw [Nat.mem_primeFactors]
        exact ⟨hqp, hbc ▸ Dvd.dvd.mul_left hqc _, by omega⟩
      have he := h q hmem hq2
      rw [← hbc, Nat.factorization_mul (by positivity) (by omega),
        Nat.factorization_pow] at he
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at he
      have h1 : c.factorization q = 1 := by
        have hle := hsq.natFactorization_le_one q
        have hpos : 0 < c.factorization q :=
          hqp.factorization_pos_of_dvd (by omega) hqc
        omega
      rw [h1] at he
      exact Nat.not_even_iff_odd.mpr ⟨b.factorization q, by ring⟩ he
    have hpf : c.primeFactors = {2} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨?_, hall⟩
      obtain ⟨q, hq⟩ : c.primeFactors.Nonempty := by
        rw [Nat.nonempty_primeFactors]; omega
      exact hall q hq ▸ hq
    have hc2 : c = 2 := by
      rw [← Nat.prod_primeFactors_of_squarefree hsq, hpf]; simp
    subst hc2
    exact not_two_mul_sq k b (by rw [← hbc]; ring)
  · rintro ⟨s, hs⟩ p _ _
    rw [hs, Nat.factorization_mul (by rintro rfl; omega) (by rintro rfl; omega)]
    exact ⟨_, rfl⟩

lemma key (k : ℕ) : A088827 (a k) ↔ IsSquare (6 * k + 4) := by
  rw [← odd_sigma_iff_isSquare]
  unfold A088827 a
  have he : Even (6 * k + 4) := ⟨3 * k + 2, by ring⟩
  simp only [he, true_and]
  constructor
  · intro h
    have : Odd ((σ 1 (6 * k + 4) : ℤ) - 2 * ((6 * k + 4 : ℕ) : ℤ) + 2 * ((6 * k + 4 : ℕ) : ℤ)) :=
      h.add_even (even_two_mul _)
    simpa using this
  · intro h
    exact (Int.odd_coe_nat _ |>.mpr h).sub_even (even_two_mul _)

lemma A186421_4 (t : ℕ) :
    A186421 (4 * t) = 4 * t ∧ A186421 (4 * t + 1) = 2 * t + 1 ∧
      A186421 (4 * t + 2) = 4 * t + 2 ∧ A186421 (4 * t + 3) = 2 * t + 1 := by
  unfold A186421
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [if_pos ⟨2 * t, by ring⟩]
  · rw [if_neg (by rw [Nat.not_even_iff_odd]; exact ⟨2 * t, by ring⟩)]; omega
  · rw [if_pos ⟨2 * t + 1, by ring⟩]
  · rw [if_neg (by rw [Nat.not_even_iff_odd]; exact ⟨2 * t + 1, by ring⟩)]; omega

lemma A186423_succ (n : ℕ) : A186423 (n + 1) = A186423 n + A186421 (n + 1) := by
  unfold A186423; rw [Finset.sum_range_succ]

lemma A186423_4 (t : ℕ) :
    A186423 (4 * t) = 6 * t ^ 2 + 2 * t ∧ A186423 (4 * t + 1) = 6 * t ^ 2 + 4 * t + 1 ∧
      A186423 (4 * t + 2) = 6 * t ^ 2 + 8 * t + 3 ∧
      A186423 (4 * t + 3) = 6 * t ^ 2 + 10 * t + 4 := by
  induction t with
  | zero => decide
  | succ t ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    obtain ⟨g0, g1, g2, g3⟩ := A186421_4 (t + 1)
    have e0 : A186423 (4 * (t + 1)) = 6 * (t + 1) ^ 2 + 2 * (t + 1) := by
      rw [show 4 * (t + 1) = (4 * t + 3) + 1 by ring, A186423_succ, h3,
        show 4 * t + 3 + 1 = 4 * (t + 1) by ring, g0]; ring
    have e1 : A186423 (4 * (t + 1) + 1) = 6 * (t + 1) ^ 2 + 4 * (t + 1) + 1 := by
      rw [A186423_succ, e0, g1]; ring
    have e2 : A186423 (4 * (t + 1) + 2) = 6 * (t + 1) ^ 2 + 8 * (t + 1) + 3 := by
      rw [show 4 * (t + 1) + 2 = (4 * (t + 1) + 1) + 1 by ring, A186423_succ, e1, g2]; ring
    have e3 : A186423 (4 * (t + 1) + 3) = 6 * (t + 1) ^ 2 + 10 * (t + 1) + 4 := by
      rw [show 4 * (t + 1) + 3 = (4 * (t + 1) + 2) + 1 by ring, A186423_succ, e2, g3]; ring
    exact ⟨e0, e1, e2, e3⟩

lemma isSquare_iff (k : ℕ) : IsSquare (6 * k + 4) ↔ ∃ t ∈ A186424, k = t - 1 := by
  constructor
  · rintro ⟨s, hs⟩
    have hmod : s % 6 * (s % 6) % 6 = 4 := by rw [← Nat.mul_mod, ← hs]; omega
    have hlt : s % 6 < 6 := Nat.mod_lt _ (by norm_num)
    obtain ⟨q, hq⟩ : ∃ q, s = 6 * q + s % 6 := ⟨s / 6, by omega⟩
    interval_cases hr : s % 6 <;> simp at hmod
    · -- s = 6q + 2
      refine ⟨6 * q ^ 2 + 4 * q + 1, ⟨⟨3 * q ^ 2 + 2 * q, by ring⟩, 4 * q + 1, (A186423_4 q).2.1⟩, ?_⟩
      have : 6 * k = 6 * (6 * q ^ 2 + 4 * q) := by rw [hq] at hs; nlinarith
      omega
    · -- s = 6q + 4
      refine ⟨6 * q ^ 2 + 8 * q + 3, ⟨⟨3 * q ^ 2 + 4 * q + 1, by ring⟩, 4 * q + 2, (A186423_4 q).2.2.1⟩, ?_⟩
      have : 6 * k = 6 * (6 * q ^ 2 + 8 * q + 2) := by rw [hq] at hs; nlinarith
      omega
  · rintro ⟨t, ⟨hodd, i, rfl⟩, rfl⟩
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ i = 4 * q + r := ⟨i / 4, i % 4, Nat.mod_lt _ (by norm_num), by omega⟩
    obtain ⟨h0, h1, h2, h3⟩ := A186423_4 q
    interval_cases r
    · rw [add_zero, h0] at hodd
      exact absurd hodd (Nat.not_odd_iff_even.mpr ⟨3 * q ^ 2 + q, by ring⟩)
    · rw [h1, Nat.add_sub_cancel]; exact ⟨6 * q + 2, by ring⟩
    · rw [h2, show 6 * q ^ 2 + 8 * q + 3 - 1 = 6 * q ^ 2 + 8 * q + 2 by omega]
      exact ⟨6 * q + 4, by ring⟩
    · rw [h3] at hodd
      exact absurd hodd (Nat.not_odd_iff_even.mpr ⟨3 * q ^ 2 + 5 * q + 2, by ring⟩)

end OMA.S_oeis_a016957.Proof

open OMA.S_oeis_a016957 OMA.S_oeis_a016957.Proof ArithmeticFunction in
open scoped ArithmeticFunction.sigma in
theorem OMA.solution : type_of% @OMA.S_oeis_a016957.main := by
  refine ⟨⟨0, (key 0).mpr ⟨2, by norm_num⟩⟩, ⟨2, ⟨even_two, ?_⟩, fun n => by unfold a; omega⟩,
    fun k => (key k).trans (isSquare_iff k)⟩
  have : σ 1 2 = 3 := by decide
  rw [this]; decide
