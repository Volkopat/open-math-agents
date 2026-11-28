import OMAStatements.S_oeis_a006532
import Mathlib

-- Problem: A006532: Infinitely Many Numbers Whose Sum of Divisors Is a Square.
-- Upstream: formal-conjectures statements/oeis-a006532.lean:0 (declaration OMA.S_oeis_a006532.main)
-- Credit: @npnelson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof. Fix N. Let c(X) be the number of primes up to X.
-- (1) Counting. From 4^n < n * C(2n, n) and C(2n, n) <= (2n)^c(2n) we get, for n = 2^i,
--     2^(i+1) < i + (i+1) c(2^(i+1)). If c(2Y) <= c(Y) + K held for all Y then c(2^i) <= K i,
--     which contradicts the previous line at i + 1 = K + 10. So for every K there is Y with
--     c(2Y) > c(Y) + K.
-- (2) Pigeonhole. Take K = c(N+2) and such a Y. Let A be the set of primes p with
--     N + 2 < p <= 2Y and B the set of primes up to Y; then |A| > |B|. Every p in A is odd, so
--     each prime factor of p + 1 is at most (p + 1) / 2 <= Y and lies in B. Map a subset T of A
--     to the set of l in B for which the exponent of l in the product of (p + 1), p in T, is
--     odd. There are more subsets of A than subsets of B, so two different subsets T1, T2 have
--     the same image, and for T = (T1 minus T2) union (T2 minus T1), which is nonempty, every
--     prime has even exponent in the product of (p + 1) over T. So that product is a square.
-- (3) For n = the product of the primes in T, sigma(n) is the product of (p + 1) over T, a
--     square, and n > N because T contains a prime above N.

namespace SigmaSquare006532Proof

/-- A positive number all of whose prime exponents are even is a square. -/
theorem isSquare_of_even (m : ℕ) (hm : m ≠ 0) (h : ∀ p, Even (m.factorization p)) :
    IsSquare m := by
  refine ⟨m.factorization.prod (fun p k => p ^ (k / 2)), ?_⟩
  calc m = m.factorization.prod (fun p k => p ^ k) :=
        (Nat.prod_factorization_pow_eq_self hm).symm
    _ = m.factorization.prod (fun p k => p ^ (k / 2) * p ^ (k / 2)) := by
        refine Finsupp.prod_congr (fun p _ => ?_)
        show p ^ m.factorization p = p ^ (m.factorization p / 2) * p ^ (m.factorization p / 2)
        obtain ⟨t, ht⟩ := h p
        rw [← pow_add]
        congr 1
        omega
    _ = _ := Finsupp.prod_mul

/-- The parity pattern of a set of atoms. -/
def pat (B T : Finset ℕ) : Finset ℕ :=
  B.filter (fun l => Odd (∑ p ∈ T, (p + 1).factorization l))

theorem mem_pat {B T : Finset ℕ} {l : ℕ} :
    l ∈ pat B T ↔ l ∈ B ∧ Odd (∑ p ∈ T, (p + 1).factorization l) :=
  Finset.mem_filter

theorem pigeon (A B : Finset ℕ)
    (hAB : ∀ p ∈ A, ∀ l : ℕ, l.Prime → l ∣ p + 1 → l ∈ B) (hcard : B.card < A.card) :
    ∃ T : Finset ℕ, T ⊆ A ∧ T.Nonempty ∧ IsSquare (∏ p ∈ T, (p + 1)) := by
  classical
  have hmaps : Set.MapsTo (pat B) (A.powerset : Set (Finset ℕ)) (B.powerset : Set (Finset ℕ)) := by
    intro T _
    exact Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _))
  have hc : B.powerset.card < A.powerset.card := by
    rw [Finset.card_powerset, Finset.card_powerset]
    exact Nat.pow_lt_pow_right (by norm_num) hcard
  obtain ⟨T1, h1, T2, h2, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc hmaps
  have h1' := Finset.mem_powerset.1 h1
  have h2' := Finset.mem_powerset.1 h2
  refine ⟨(T1 \ T2) ∪ (T2 \ T1), ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact h1' (Finset.mem_sdiff.1 h).1
    · exact h2' (Finset.mem_sdiff.1 h).1
  · rw [Finset.nonempty_iff_ne_empty]
    intro he
    apply hne
    obtain ⟨ha, hb⟩ := Finset.union_eq_empty.1 he
    exact Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.1 ha)
      (Finset.sdiff_eq_empty_iff_subset.1 hb)
  · apply isSquare_of_even
    · exact Finset.prod_ne_zero_iff.2 (fun p _ => Nat.add_one_ne_zero p)
    · intro l
      rw [Nat.factorization_prod (fun p _ => Nat.add_one_ne_zero p), Finsupp.finsetSum_apply]
      have hdisj : Disjoint (T1 \ T2) (T2 \ T1) := disjoint_sdiff_sdiff
      rw [Finset.sum_union hdisj]
      by_cases hl : l ∈ B
      · have e1 : ∑ p ∈ T1 ∩ T2, (p + 1).factorization l + ∑ p ∈ T1 \ T2, (p + 1).factorization l
            = ∑ p ∈ T1, (p + 1).factorization l := Finset.sum_inter_add_sum_sdiff T1 T2 _
        have e2 : ∑ p ∈ T2 ∩ T1, (p + 1).factorization l + ∑ p ∈ T2 \ T1, (p + 1).factorization l
            = ∑ p ∈ T2, (p + 1).factorization l := Finset.sum_inter_add_sum_sdiff T2 T1 _
        rw [Finset.inter_comm] at e2
        have hmem : l ∈ pat B T1 ↔ l ∈ pat B T2 := by rw [heq]
        rw [mem_pat, mem_pat] at hmem
        have ho : Odd (∑ p ∈ T1, (p + 1).factorization l) ↔
            Odd (∑ p ∈ T2, (p + 1).factorization l) := by
          constructor
          · intro h
            exact (hmem.1 ⟨hl, h⟩).2
          · intro h
            exact (hmem.2 ⟨hl, h⟩).2
        rw [Nat.odd_iff, Nat.odd_iff] at ho
        rw [Nat.even_iff]
        omega
      · have hz : ∀ p ∈ A, (p + 1).factorization l = 0 := by
          intro p hp
          by_cases hlp : l.Prime
          · exact Nat.factorization_eq_zero_of_not_dvd (fun hd => hl (hAB p hp l hlp hd))
          · exact Nat.factorization_eq_zero_of_not_prime _ hlp
        rw [Finset.sum_eq_zero (fun p hp => hz p (h1' (Finset.mem_sdiff.1 hp).1)),
          Finset.sum_eq_zero (fun p hp => hz p (h2' (Finset.mem_sdiff.1 hp).1))]
        exact ⟨0, rfl⟩

/-- The primes up to `X`. -/
def P (X : ℕ) : Finset ℕ := (Finset.range (X + 1)).filter Nat.Prime

/-- The number of primes up to `X`. -/
def c (X : ℕ) : ℕ := (P X).card

theorem mem_P {X p : ℕ} : p ∈ P X ↔ p ≤ X ∧ p.Prime := by
  unfold P
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩

theorem cheb (n : ℕ) (hn : 4 ≤ n) : 4 ^ n < n * (2 * n) ^ c (2 * n) := by
  have h1 := Nat.four_pow_lt_mul_centralBinom n hn
  have h2 : Nat.centralBinom n ≤ (2 * n) ^ c (2 * n) := by
    have h3 : ∏ p ∈ Finset.range (2 * n + 1), p ^ (Nat.centralBinom n).factorization p
        = ∏ p ∈ P (2 * n), p ^ (Nat.centralBinom n).factorization p := by
      unfold P
      symm
      apply Finset.prod_filter_of_ne
      intro p _ hp
      by_contra hnp
      apply hp
      rw [Nat.factorization_eq_zero_of_not_prime _ hnp, pow_zero]
    have h4 : ∏ p ∈ P (2 * n), p ^ (Nat.centralBinom n).factorization p
        ≤ (2 * n) ^ c (2 * n) := by
      unfold c
      apply Finset.prod_le_pow_card
      intro p _
      exact Nat.pow_factorization_choose_le (by omega)
    calc Nat.centralBinom n
        = ∏ p ∈ Finset.range (2 * n + 1), p ^ (Nat.centralBinom n).factorization p :=
          (Nat.prod_pow_factorization_centralBinom n).symm
      _ = ∏ p ∈ P (2 * n), p ^ (Nat.centralBinom n).factorization p := h3
      _ ≤ (2 * n) ^ c (2 * n) := h4
  calc 4 ^ n < n * Nat.centralBinom n := h1
    _ ≤ n * (2 * n) ^ c (2 * n) := Nat.mul_le_mul_left n h2

theorem cheb2 (i : ℕ) (hi : 2 ≤ i) : 2 * 2 ^ i < i + (i + 1) * c (2 * 2 ^ i) := by
  have h4 : 4 ≤ 2 ^ i := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
  have h := cheb (2 ^ i) h4
  have e1 : (4 : ℕ) ^ (2 ^ i) = 2 ^ (2 * 2 ^ i) := by
    rw [pow_mul]
    norm_num
  have e2 : 2 ^ i * (2 * 2 ^ i) ^ c (2 * 2 ^ i) = 2 ^ (i + (i + 1) * c (2 * 2 ^ i)) := by
    rw [pow_add, pow_mul, pow_succ']
  rw [e1, e2] at h
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h

theorem c_one : c 1 = 0 := by
  unfold c
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro p hp
  obtain ⟨h1, h2⟩ := mem_P.1 hp
  have := h2.two_le
  omega

theorem c_pow (K : ℕ) (h : ∀ Y, c (2 * Y) ≤ c Y + K) (i : ℕ) : c (2 ^ i) ≤ K * i := by
  induction i with
  | zero =>
    rw [pow_zero, c_one]
    exact Nat.zero_le _
  | succ i ih =>
    rw [pow_succ']
    have h1 := h (2 ^ i)
    calc c (2 * 2 ^ i) ≤ c (2 ^ i) + K := h1
      _ ≤ K * i + K := by omega
      _ = K * (i + 1) := by ring

theorem cube_le (j : ℕ) (hj : 10 ≤ j) : j ^ 3 ≤ 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have h1 : 10 * (j * j) ≤ j * (j * j) := Nat.mul_le_mul_right (j * j) hj
    have h2 : j ≤ j * j := Nat.le_mul_self j
    have e1 : (j + 1) ^ 3 = j * (j * j) + 3 * (j * j) + 3 * j + 1 := by ring
    have e2 : j ^ 3 = j * (j * j) := by ring
    have e3 : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
    rw [e1, e3]
    rw [e2] at ih
    omega

theorem exists_many (K : ℕ) : ∃ Y, c Y + K < c (2 * Y) := by
  by_contra hcon
  have hcon' : ∀ Y, c (2 * Y) ≤ c Y + K := fun Y => Nat.le_of_not_lt (fun h => hcon ⟨Y, h⟩)
  have hc := c_pow K hcon' (K + 10)
  have hch := cheb2 (K + 9) (by omega)
  have e : 2 * 2 ^ (K + 9) = 2 ^ (K + 10) := by ring
  rw [e] at hch
  have hcube := cube_le (K + 10) (by omega)
  have h5 : (K + 9 + 1) * c (2 ^ (K + 10)) ≤ (K + 10) * (K * (K + 10)) :=
    Nat.mul_le_mul (by omega) hc
  have e3 : (K + 10) ^ 3 = (K + 10) * (K * (K + 10)) + 10 * ((K + 10) * (K + 10)) := by ring
  have h7 : K + 10 ≤ (K + 10) * (K + 10) := Nat.le_mul_self (K + 10)
  have h6 : K + 9 + (K + 10) * (K * (K + 10)) ≤ (K + 10) ^ 3 := by
    rw [e3]
    omega
  exact absurd (lt_of_lt_of_le hch (le_trans (Nat.add_le_add_left h5 _) (le_trans h6 hcube)))
    (lt_irrefl _)

theorem main_step (N : ℕ) :
    ∃ n, N < n ∧ 0 < n ∧ IsSquare (ArithmeticFunction.sigma 1 n) := by
  classical
  obtain ⟨Y, hY⟩ := exists_many (c (N + 2))
  have hAmem : ∀ p ∈ (P (2 * Y)).filter (fun p => N + 2 < p),
      p.Prime ∧ p ≤ 2 * Y ∧ N + 2 < p := by
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
    obtain ⟨h3, h4⟩ := mem_P.1 h1
    exact ⟨h4, h3, h2⟩
  have hcard : (P Y).card < ((P (2 * Y)).filter (fun p => N + 2 < p)).card := by
    have hsub : P (2 * Y) ⊆ (P (2 * Y)).filter (fun p => N + 2 < p) ∪ P (N + 2) := by
      intro p hp
      obtain ⟨h3, h4⟩ := mem_P.1 hp
      by_cases h : N + 2 < p
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hp, h⟩)
      · exact Finset.mem_union_right _ (mem_P.2 ⟨by omega, h4⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le ((P (2 * Y)).filter (fun p => N + 2 < p)) (P (N + 2))
    unfold c at hY
    omega
  have hfac : ∀ p ∈ (P (2 * Y)).filter (fun p => N + 2 < p),
      ∀ l : ℕ, l.Prime → l ∣ p + 1 → l ∈ P Y := by
    intro p hp l hl hdvd
    obtain ⟨hpp, hpY, hpN⟩ := hAmem p hp
    obtain ⟨k, hk⟩ := hdvd
    apply mem_P.2
    refine ⟨?_, hl⟩
    have hodd : p % 2 = 1 := by
      rcases hpp.eq_two_or_odd with h | h
      · omega
      · exact h
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with h | h
      · exfalso
        interval_cases k
        · omega
        · rcases hl.eq_two_or_odd with h2 | h2 <;> omega
      · exact h
    have h3 := Nat.mul_le_mul_left l hk2
    omega
  obtain ⟨T, hTA, hTne, hsq⟩ := pigeon _ (P Y) hfac hcard
  have hprime : ∀ p ∈ T, p.Prime := fun p hp => (hAmem p (hTA hp)).1
  have hpos : 0 < ∏ p ∈ T, p := Finset.prod_pos (fun p hp => (hprime p hp).pos)
  refine ⟨∏ p ∈ T, p, ?_, hpos, ?_⟩
  · obtain ⟨p0, hp0⟩ := hTne
    have h1 := (hAmem p0 (hTA hp0)).2.2
    have h2 : p0 ≤ ∏ p ∈ T, p := Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem _ hp0)
    omega
  · rw [ArithmeticFunction.IsMultiplicative.map_prod_of_prime
      ArithmeticFunction.isMultiplicative_sigma T hprime]
    have e : ∏ p ∈ T, ArithmeticFunction.sigma 1 p = ∏ p ∈ T, (p + 1) := by
      refine Finset.prod_congr rfl (fun p hp => ?_)
      rw [ArithmeticFunction.sigma_one_apply, (hprime p hp).sum_divisors]
    rw [e]
    exact hsq

end SigmaSquare006532Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a006532.main := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, h1, h2, h3⟩ := SigmaSquare006532Proof.main_step N
  exact ⟨n, ⟨h2, h3⟩, h1⟩
