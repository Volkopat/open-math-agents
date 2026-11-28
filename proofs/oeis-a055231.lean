import OMAStatements.S_oeis_a055231
import Mathlib

/-!
# A055231: Yanev's formula for the powerfree part of a product

a(n) is the product of the primes in P1(n) = {p : v_p(n) = 1}. Split P1(n) = A ⊔ B by whether p ∣ m,
and P1(m) = C ⊔ D by whether p ∣ n. Since v_p(nm) = v_p(n) + v_p(m), P1(nm) = A ⊔ C. For a set S of
primes, gcd(k, ∏_{p∈S} p) = ∏_{p∈S, p∣k} p, so gcd(n, a(m)) = ∏_D p and gcd(m, a(n)) = ∏_B p. Hence
a(n)a(m) = a(nm)·gcd(n, a(m))·gcd(m, a(n)), which is the stated division.
-/

namespace PA055231

/-- The primes dividing `n` exactly once. -/
def P1 (n : ℕ) : Finset ℕ := n.primeFactors.filter (fun p => n.factorization p = 1)

theorem a_eq (n : ℕ) : OMA.S_oeis_a055231.a n = ∏ p ∈ P1 n, p := rfl

theorem gcd_prod (k : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Nat.gcd k (∏ p ∈ S, p) = ∏ p ∈ S.filter (· ∣ k), p := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert q S hq ih =>
    have hqp : q.Prime := hS q (Finset.mem_insert_self q S)
    have hS' : ∀ p ∈ S, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hcop : Nat.Coprime q (∏ p ∈ S, p) := by
      apply Nat.Coprime.prod_right
      intro p hp
      exact (Nat.coprime_primes hqp (hS' p hp)).mpr (fun h => hq (h ▸ hp))
    rw [Finset.prod_insert hq, Nat.Coprime.gcd_mul k hcop, ih hS', Finset.filter_insert]
    by_cases hqk : q ∣ k
    · rw [if_pos hqk, Finset.prod_insert (fun h => hq (Finset.mem_filter.mp h).1),
        Nat.gcd_eq_right hqk]
    · rw [if_neg hqk, (Nat.Prime.coprime_iff_not_dvd hqp).mpr hqk |>.symm |> Nat.Coprime.gcd_eq_one,
        one_mul]

theorem prime_of_mem {n p : ℕ} (h : p ∈ P1 n) : p.Prime :=
  Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp h).1

theorem P1_mul (n m : ℕ) (hn : n ≠ 0) (hm : m ≠ 0) :
    P1 (n * m) = (P1 n).filter (fun p => ¬ p ∣ m) ∪ (P1 m).filter (fun p => ¬ p ∣ n) := by
  ext p
  simp only [P1, Finset.mem_union, Finset.mem_filter, Nat.mem_primeFactors]
  rw [Nat.factorization_mul hn hm, Finsupp.add_apply]
  constructor
  · rintro ⟨⟨hp, hpd, -⟩, he⟩
    have hn' : n.factorization p = 0 ∨ m.factorization p = 0 := by omega
    rcases hn' with h0 | h0
    · right
      have hnd : ¬ p ∣ n := fun hd => by
        have := hp.factorization_pos_of_dvd hn hd; omega
      have hmd : p ∣ m := by
        rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
        · exact absurd h hnd
        · exact h
      exact ⟨⟨⟨hp, hmd, hm⟩, by omega⟩, hnd⟩
    · left
      have hmd : ¬ p ∣ m := fun hd => by
        have := hp.factorization_pos_of_dvd hm hd; omega
      have hnd : p ∣ n := by
        rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
        · exact h
        · exact absurd h hmd
      exact ⟨⟨⟨hp, hnd, hn⟩, by omega⟩, hmd⟩
  · rintro (⟨⟨⟨hp, hpd, -⟩, he⟩, hnd⟩ | ⟨⟨⟨hp, hpd, -⟩, he⟩, hnd⟩)
    · have : m.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hnd
      exact ⟨⟨hp, Dvd.dvd.mul_right hpd m, mul_ne_zero hn hm⟩, by omega⟩
    · have : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hnd
      exact ⟨⟨hp, Dvd.dvd.mul_left hpd n, mul_ne_zero hn hm⟩, by omega⟩

end PA055231

theorem OMA.solution : type_of% @OMA.S_oeis_a055231.main := by
  intro n m hn hm
  have hn0 : n ≠ 0 := by omega
  have hm0 : m ≠ 0 := by omega
  set A := (PA055231.P1 n).filter (fun p => ¬ p ∣ m)
  set B := (PA055231.P1 n).filter (fun p => p ∣ m)
  set C := (PA055231.P1 m).filter (fun p => ¬ p ∣ n)
  set D := (PA055231.P1 m).filter (fun p => p ∣ n)
  have hAC : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro p hA hC
    have h1 : p ∣ n := Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp (Finset.mem_filter.mp hA).1).1
    exact (Finset.mem_filter.mp hC).2 h1
  have hnm : OMA.S_oeis_a055231.a (n * m) = (∏ p ∈ A, p) * ∏ p ∈ C, p := by
    rw [PA055231.a_eq, PA055231.P1_mul n m hn0 hm0, Finset.prod_union hAC]
  have hna : OMA.S_oeis_a055231.a n = (∏ p ∈ B, p) * ∏ p ∈ A, p := by
    rw [PA055231.a_eq, Finset.prod_filter_mul_prod_filter_not]
  have hma : OMA.S_oeis_a055231.a m = (∏ p ∈ D, p) * ∏ p ∈ C, p := by
    rw [PA055231.a_eq, Finset.prod_filter_mul_prod_filter_not]
  have hG1 : Nat.gcd n (OMA.S_oeis_a055231.a m) = ∏ p ∈ D, p := by
    rw [PA055231.a_eq, PA055231.gcd_prod n _ (fun p hp => PA055231.prime_of_mem hp)]
  have hG2 : Nat.gcd m (OMA.S_oeis_a055231.a n) = ∏ p ∈ B, p := by
    rw [PA055231.a_eq, PA055231.gcd_prod m _ (fun p hp => PA055231.prime_of_mem hp)]
  have hpos : 0 < (∏ p ∈ D, p) * ∏ p ∈ B, p := by
    apply Nat.mul_pos
    · exact Finset.prod_pos fun p hp =>
        (PA055231.prime_of_mem (Finset.mem_filter.mp hp).1).pos
    · exact Finset.prod_pos fun p hp =>
        (PA055231.prime_of_mem (Finset.mem_filter.mp hp).1).pos
  rw [hG1, hG2, hna, hma, hnm]
  symm
  apply Nat.div_eq_of_eq_mul_left hpos
  ring
