import OMAStatements.S_oeis_a089758
import Mathlib

-- Problem: A089758: Primes arising in A089757.
-- Upstream: formal-conjectures statements/oeis-a089758.lean:0 (declaration OMA.S_oeis_a089758.main)
-- Credit: @npnelson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof. The greedy sequence is built from a state (b, c): b is the previous term (0 at the
-- start) and c is the current chain value. The chain value always satisfies c = 1 mod 3 and
-- c = 1 mod 10: it starts at 1, and each step adds m * 10 ^ L with 3 | m and L >= 1. Hence c is
-- coprime to q = 3 * 10 ^ L, where L is the number of digits of c, and Dirichlet's theorem on
-- primes in arithmetic progressions gives a prime p = c mod q with p > c + q * b. Then
-- p = 3 t * 10 ^ L + c with t > b, so m = 3 t is a positive multiple of 3 above b whose
-- concatenation with c is the prime p. So the candidate set is nonempty at every step and the
-- least element exists.

namespace Chain089758Proof

open OMA.S_oeis_a089758

/-- Candidates for the next term, given the previous term `b` and the chain value `c`. -/
def S (b c : ℕ) : Set ℕ :=
  {m : ℕ | 0 < m ∧ 3 ∣ m ∧ b < m ∧ Nat.Prime (concat10 m c)}

theorem S_nonempty (b c : ℕ) (h3 : c % 3 = 1) (h10 : c % 10 = 1) : (S b c).Nonempty := by
  have hc3 : Nat.Coprime c 3 := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h3]; rfl
  have hc10 : Nat.Coprime c 10 := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h10]; rfl
  have hcop : Nat.Coprime c (3 * 10 ^ (Nat.digits 10 c).length) :=
    Nat.Coprime.mul_right hc3 (Nat.Coprime.pow_right _ hc10)
  have hq : 3 * 10 ^ (Nat.digits 10 c).length ≠ 0 := by positivity
  obtain ⟨p, hgt, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (c + 3 * 10 ^ (Nat.digits 10 c).length * b) hq hcop
  have hcp : c ≤ p := by omega
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hcp).1 hmod.symm
  have hbt : b < t := by
    have h1 : 3 * 10 ^ (Nat.digits 10 c).length * b < 3 * 10 ^ (Nat.digits 10 c).length * t := by
      omega
    exact Nat.lt_of_mul_lt_mul_left h1
  refine ⟨3 * t, by omega, Dvd.intro t rfl, by omega, ?_⟩
  have e : concat10 (3 * t) c = p := by
    have h2 : p = 3 * 10 ^ (Nat.digits 10 c).length * t + c := by omega
    rw [h2]
    unfold concat10
    ring
  rw [e]
  exact hp

/-- The next term. -/
noncomputable def nxt (b c : ℕ) : ℕ := sInf (S b c)

/-- The state: previous term (0 at the start) and chain value. -/
noncomputable def st : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 => (nxt (st n).1 (st n).2, concat10 (nxt (st n).1 (st n).2) (st n).2)

/-- The greedy sequence. -/
noncomputable def a (n : ℕ) : ℕ := nxt (st n).1 (st n).2

theorem st_zero : st 0 = (0, 1) := by
  rw [st]

theorem st_succ (n : ℕ) : st (n + 1) = (a n, concat10 (a n) (st n).2) := by
  rw [st]
  rfl

theorem inv (n : ℕ) : (st n).2 % 3 = 1 ∧ (st n).2 % 10 = 1 := by
  induction n with
  | zero =>
    rw [st_zero]
    exact ⟨rfl, rfl⟩
  | succ n ih =>
    have hmem : a n ∈ S (st n).1 (st n).2 := Nat.sInf_mem (S_nonempty _ _ ih.1 ih.2)
    obtain ⟨k, hk⟩ := hmem.2.1
    have hne : (st n).2 ≠ 0 := by
      intro h
      have := ih.1
      rw [h] at this
      omega
    have hL : (Nat.digits 10 (st n).2).length ≠ 0 := by
      intro h
      exact (Nat.digits_ne_nil_iff_ne_zero.2 hne) (List.length_eq_zero_iff.1 h)
    obtain ⟨L', hL'⟩ := Nat.exists_eq_succ_of_ne_zero hL
    rw [st_succ]
    show (concat10 (a n) (st n).2) % 3 = 1 ∧ (concat10 (a n) (st n).2) % 10 = 1
    unfold concat10
    rw [hL']
    have e1 : a n * 10 ^ (L' + 1) = 3 * (k * 10 ^ (L' + 1)) := by
      rw [hk]; ring
    have e2 : a n * 10 ^ (L' + 1) = 10 * (a n * 10 ^ L') := by
      ring
    have h3 := ih.1
    have h10 := ih.2
    constructor
    · rw [e1]; omega
    · rw [e2]; omega

theorem a_mem (n : ℕ) : a n ∈ S (st n).1 (st n).2 :=
  Nat.sInf_mem (S_nonempty _ _ (inv n).1 (inv n).2)

theorem a_le (n m : ℕ) (hm : m ∈ S (st n).1 (st n).2) : a n ≤ m :=
  Nat.sInf_le hm

theorem chain_eq (n : ℕ) : chainVal a n = (st n).2 := by
  induction n with
  | zero =>
    rw [st_zero]
    rfl
  | succ n ih =>
    rw [st_succ]
    show concat10 (a n) (chainVal a n) = concat10 (a n) (st n).2
    rw [ih]

theorem bound_iff (n m : ℕ) (hm : 0 < m) : (∀ i < n, a i < m) ↔ (st n).1 < m := by
  induction n with
  | zero =>
    rw [st_zero]
    constructor
    · intro _
      exact hm
    · intro _ i hi
      omega
  | succ n ih =>
    rw [st_succ]
    show (∀ i < n + 1, a i < m) ↔ a n < m
    constructor
    · intro h
      exact h n (Nat.lt_succ_self n)
    · intro h i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h1 | h1
      · have h2 : (st n).1 < a n := (a_mem n).2.2.1
        exact ih.2 (lt_trans h2 h) i h1
      · rw [h1]
        exact h

end Chain089758Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a089758.main := by
  refine ⟨Chain089758Proof.a, fun n => ⟨?_, ?_⟩⟩
  · obtain ⟨h0, h3, hb, hp⟩ := Chain089758Proof.a_mem n
    refine ⟨h0, h3, (Chain089758Proof.bound_iff n _ h0).2 hb, ?_⟩
    rw [Chain089758Proof.chain_eq]
    exact hp
  · intro m hm
    obtain ⟨h0, h3, hall, hp⟩ := hm
    apply Chain089758Proof.a_le
    rw [Chain089758Proof.chain_eq] at hp
    exact ⟨h0, h3, (Chain089758Proof.bound_iff n m h0).1 hall, hp⟩
