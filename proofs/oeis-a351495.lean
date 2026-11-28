import OMAStatements.S_oeis_a351495
import Mathlib

-- Problem: A351495: a(0) = 1 and a(n+1) is the least unused positive multiple of the least prime
-- not dividing a(n); the sequence exists and is a permutation of the positive integers.
-- Upstream: formal-conjectures statements/oeis-a351495.lean:0 (declaration OMA.S_oeis_a351495.main)
-- Credit: @npnelson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof. Write p(n) for the least prime not dividing a(n).
-- Existence: define the sequence by recursion on the history; both least elements exist because
-- a(n) > 0 and only finitely many values are used.
-- Injectivity is built into the rule. Since a is injective, {n | a(n+1) <= B} is finite for
-- every B (*).
-- (L) If p(n) = q for infinitely many n, every positive multiple m of q occurs: otherwise
--     a(n+1) <= m at each such n, against (*).
-- (B) p(n) = 2 for infinitely many n. If not, a(n) is even for all n > N. Let S be the sum of
--     a(0..N). For n > N the prime q = p(n) is odd and a(n+1) is an even multiple of q, so q
--     itself was used, at an index <= N (later terms are even); thus q <= S. The odd number
--     q (2S + 1) exceeds S, so it is never used, and a(n+1) <= q (2S + 1) <= S (2S + 1) for all
--     n > N, against (*).
-- (O) For an odd prime q, the even numbers (q-1)! (q t + 1) all occur by (L) and (B); at such an
--     index all primes below q divide a(n) and q does not, so p(n) = q. Hence p(n) = q
--     infinitely often and every multiple of q occurs by (L).
-- Every m >= 2 is a multiple of its least prime factor, and a(0) = 1.

namespace Greedy351495Proof

open OMA.S_oeis_a351495

/-- The greedy rule with the primes `p n` made explicit. -/
def Spec (a p : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ (∀ n, IsLeast {q : ℕ | q.Prime ∧ ¬ q ∣ a n} (p n)) ∧
    (∀ n, IsLeast {m : ℕ | 0 < m ∧ p n ∣ m ∧ ∀ i ≤ n, a i ≠ m} (a (n + 1)))

theorem pos {a p : ℕ → ℕ} (h : Spec a p) (n : ℕ) : 0 < a n := by
  cases n with
  | zero =>
    rw [h.1]
    norm_num
  | succ n => exact (h.2.2 n).1.1

theorem ne_of_lt {a p : ℕ → ℕ} (h : Spec a p) {i j : ℕ} (hij : i < j) : a i ≠ a j := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  exact (h.2.2 n).1.2.2 i (by omega)

theorem inj {a p : ℕ → ℕ} (h : Spec a p) : Function.Injective a := by
  intro i j hij
  rcases Nat.lt_trichotomy i j with h1 | h1 | h1
  · exact absurd hij (ne_of_lt h h1)
  · exact h1
  · exact absurd hij.symm (ne_of_lt h h1)

theorem p_prime {a p : ℕ → ℕ} (h : Spec a p) (n : ℕ) : (p n).Prime := (h.2.1 n).1.1

theorem p_not_dvd {a p : ℕ → ℕ} (h : Spec a p) (n : ℕ) : ¬ p n ∣ a n := (h.2.1 n).1.2

theorem p_dvd_succ {a p : ℕ → ℕ} (h : Spec a p) (n : ℕ) : p n ∣ a (n + 1) := (h.2.2 n).1.2.1

theorem succ_le {a p : ℕ → ℕ} (h : Spec a p) (n m : ℕ) (hm : 0 < m) (hd : p n ∣ m)
    (hu : ∀ i ≤ n, a i ≠ m) : a (n + 1) ≤ m :=
  (h.2.2 n).2 ⟨hm, hd, hu⟩

theorem p_eq {a p : ℕ → ℕ} (h : Spec a p) (n q : ℕ) (hq : q.Prime) (hnd : ¬ q ∣ a n)
    (hall : ∀ r : ℕ, r.Prime → r < q → r ∣ a n) : p n = q := by
  have h1 : p n ≤ q := (h.2.1 n).2 ⟨hq, hnd⟩
  rcases Nat.lt_or_eq_of_le h1 with h2 | h2
  · exact absurd (hall (p n) (p_prime h n) h2) (p_not_dvd h n)
  · exact h2

theorem finite_le {a p : ℕ → ℕ} (h : Spec a p) (B : ℕ) : {n : ℕ | a (n + 1) ≤ B}.Finite := by
  have hinj : Function.Injective (fun n => a (n + 1)) := by
    intro x y hxy
    have h1 : x + 1 = y + 1 := inj h hxy
    omega
  exact Set.Finite.preimage hinj.injOn (Set.finite_Iic B)

theorem appears {a p : ℕ → ℕ} (h : Spec a p) (q : ℕ) (hinf : {n : ℕ | p n = q}.Infinite)
    (m : ℕ) (hm : 0 < m) (hd : q ∣ m) : ∃ j, a j = m := by
  by_contra hne
  have hne' : ∀ j, a j ≠ m := fun j hj => hne ⟨j, hj⟩
  apply hinf
  apply (finite_le h m).subset
  intro n hn
  have hn' : p n = q := hn
  exact succ_le h n m hm (by rw [hn']; exact hd) (fun i _ => hne' i)

theorem two_infinite {a p : ℕ → ℕ} (h : Spec a p) : {n : ℕ | p n = 2}.Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  have heven : ∀ n, N < n → 2 ∣ a n := by
    intro n hn
    by_contra hnd
    have h2 : p n = 2 := p_eq h n 2 Nat.prime_two hnd (fun r hr hlt => by
      have := hr.two_le
      omega)
    have h3 : n ≤ N := hN h2
    omega
  have hS_le : ∀ j, j ≤ N → a j ≤ ∑ j ∈ Finset.range (N + 1), a j := by
    intro j hj
    exact Finset.single_le_sum (f := a) (fun i _ => Nat.zero_le _)
      (Finset.mem_range.2 (by omega))
  have hbound : ∀ n, N < n →
      a (n + 1) ≤ (∑ j ∈ Finset.range (N + 1), a j) * (2 * (∑ j ∈ Finset.range (N + 1), a j) + 1) := by
    intro n hn
    have hq := p_prime h n
    have hqodd : ¬ 2 ∣ p n := by
      intro h2
      have h3 : 2 = p n := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 h2
      apply p_not_dvd h n
      rw [← h3]
      exact heven n hn
    have hused : ∃ i, i ≤ n ∧ a i = p n := by
      by_contra hcon
      have hu : ∀ i ≤ n, a i ≠ p n := fun i hi hai => hcon ⟨i, hi, hai⟩
      have h1 : a (n + 1) ≤ p n := succ_le h n (p n) hq.pos dvd_rfl hu
      have h2 : p n ≤ a (n + 1) := Nat.le_of_dvd (pos h (n + 1)) (p_dvd_succ h n)
      have h3 : a (n + 1) = p n := le_antisymm h1 h2
      apply hqodd
      rw [← h3]
      exact heven (n + 1) (by omega)
    obtain ⟨i, hi, hai⟩ := hused
    have hiN : i ≤ N := by
      by_contra hcon
      apply hqodd
      rw [← hai]
      exact heven i (by omega)
    have hqS : p n ≤ ∑ j ∈ Finset.range (N + 1), a j := by
      rw [← hai]
      exact hS_le i hiN
    have hM : ∀ i ≤ n, a i ≠ p n * (2 * (∑ j ∈ Finset.range (N + 1), a j) + 1) := by
      intro i _ hai
      have hodd : ¬ 2 ∣ p n * (2 * (∑ j ∈ Finset.range (N + 1), a j) + 1) := by
        intro h2
        rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h3 | h3
        · exact hqodd h3
        · omega
      have hiN : i ≤ N := by
        by_contra hcon
        apply hodd
        rw [← hai]
        exact heven i (by omega)
      have h4 := hS_le i hiN
      have h5 : 2 * (∑ j ∈ Finset.range (N + 1), a j) + 1
          ≤ p n * (2 * (∑ j ∈ Finset.range (N + 1), a j) + 1) :=
        Nat.le_mul_of_pos_left _ hq.pos
      omega
    have h6 := succ_le h n (p n * (2 * (∑ j ∈ Finset.range (N + 1), a j) + 1))
      (Nat.mul_pos hq.pos (by omega)) (Dvd.intro _ rfl) hM
    exact le_trans h6 (Nat.mul_le_mul_right _ hqS)
  have hfin2 := finite_le h
    ((∑ j ∈ Finset.range (N + 1), a j) * (2 * (∑ j ∈ Finset.range (N + 1), a j) + 1))
  exact Set.Ioi_infinite N (hfin2.subset (fun n hn => hbound n hn))

theorem prime_infinite {a p : ℕ → ℕ} (h : Spec a p) (q : ℕ) (hq : q.Prime) :
    {n : ℕ | p n = q}.Infinite := by
  by_cases hq2 : q = 2
  · rw [hq2]
    exact two_infinite h
  · have hq3 : 3 ≤ q := by
      have := hq.two_le
      omega
    have hT : ∀ t : ℕ, ∃ j, a j = (q - 1).factorial * (q * t + 1) := by
      intro t
      apply appears h 2 (two_infinite h)
      · exact Nat.mul_pos (Nat.factorial_pos _) (by omega)
      · exact Dvd.dvd.mul_right (Nat.dvd_factorial (by norm_num) (by omega)) _
    choose j hj using hT
    apply Set.infinite_of_injective_forall_mem (f := j)
    · intro s t hst
      have h1 : (q - 1).factorial * (q * s + 1) = (q - 1).factorial * (q * t + 1) := by
        rw [← hj s, ← hj t, hst]
      have h2 := Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos _) h1
      have h3 : q * s = q * t := by omega
      exact Nat.eq_of_mul_eq_mul_left hq.pos h3
    · intro t
      show p (j t) = q
      apply p_eq h (j t) q hq
      · rw [hj t]
        intro hd
        rcases (Nat.Prime.dvd_mul hq).1 hd with h1 | h1
        · have h2 := (Nat.Prime.dvd_factorial hq).1 h1
          omega
        · have h2 : q ∣ 1 := (Nat.dvd_add_right (Dvd.intro t rfl)).1 h1
          have h3 := Nat.le_of_dvd (by norm_num) h2
          omega
      · intro r hr hlt
        rw [hj t]
        exact Dvd.dvd.mul_right (Nat.dvd_factorial hr.pos (by omega)) _

theorem surj {a p : ℕ → ℕ} (h : Spec a p) (m : ℕ) (hm : 0 < m) : ∃ j, a j = m := by
  by_cases h1 : m = 1
  · exact ⟨0, by rw [h.1, h1]⟩
  · have hq := Nat.minFac_prime h1
    exact appears h m.minFac (prime_infinite h m.minFac hq) m hm (Nat.minFac_dvd m)

/-- The sequence, defined by recursion on its history. -/
noncomputable def seq : ℕ → ℕ
  | 0 => 1
  | n + 1 => sInf {m : ℕ | 0 < m ∧ sInf {q : ℕ | q.Prime ∧ ¬ q ∣ seq n} ∣ m ∧
      ∀ i, i ≤ n → seq i ≠ m}
termination_by n => n
decreasing_by all_goals omega

theorem seq_zero : seq 0 = 1 := by
  rw [seq]

theorem seq_succ (n : ℕ) :
    seq (n + 1) = sInf {m : ℕ | 0 < m ∧ sInf {q : ℕ | q.Prime ∧ ¬ q ∣ seq n} ∣ m ∧
      ∀ i, i ≤ n → seq i ≠ m} := by
  rw [seq]

theorem primes_nonempty (x : ℕ) (hx : 0 < x) : {q : ℕ | q.Prime ∧ ¬ q ∣ x}.Nonempty := by
  obtain ⟨q, hq1, hq2⟩ := Nat.exists_infinite_primes (x + 1)
  exact ⟨q, hq2, Nat.not_dvd_of_pos_of_lt hx (by omega)⟩

theorem mult_nonempty (f : ℕ → ℕ) (n q : ℕ) (hq : 0 < q) :
    {m : ℕ | 0 < m ∧ q ∣ m ∧ ∀ i, i ≤ n → f i ≠ m}.Nonempty := by
  refine ⟨q * (∑ i ∈ Finset.range (n + 1), f i + 1), Nat.mul_pos hq (Nat.succ_pos _),
    Dvd.intro _ rfl, ?_⟩
  intro i hi heq
  have h1 : f i ≤ ∑ i ∈ Finset.range (n + 1), f i :=
    Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
  have h2 : (∑ i ∈ Finset.range (n + 1), f i + 1) ≤ q * (∑ i ∈ Finset.range (n + 1), f i + 1) :=
    Nat.le_mul_of_pos_left _ hq
  omega

theorem seq_pos (n : ℕ) : 0 < seq n := by
  induction n with
  | zero =>
    rw [seq_zero]
    norm_num
  | succ n ih =>
    rw [seq_succ]
    have hp := Nat.sInf_mem (primes_nonempty (seq n) ih)
    exact (Nat.sInf_mem (mult_nonempty seq n _ hp.1.pos)).1

theorem seq_greedy : Greedy seq := by
  refine ⟨seq_zero, fun n => ?_⟩
  have hne := primes_nonempty (seq n) (seq_pos n)
  have hp := Nat.sInf_mem hne
  refine ⟨sInf {q : ℕ | q.Prime ∧ ¬ q ∣ seq n}, ⟨hp, fun q hq => Nat.sInf_le hq⟩, ?_⟩
  rw [seq_succ]
  exact ⟨Nat.sInf_mem (mult_nonempty seq n _ hp.1.pos), fun m hm => Nat.sInf_le hm⟩

end Greedy351495Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a351495.main := by
  refine ⟨⟨Greedy351495Proof.seq, Greedy351495Proof.seq_greedy⟩, ?_⟩
  intro a hG
  obtain ⟨h0, hrest⟩ := hG
  choose p hp1 hp2 using hrest
  have h : Greedy351495Proof.Spec a p := ⟨h0, hp1, hp2⟩
  refine ⟨Greedy351495Proof.inj h, ?_⟩
  ext m
  constructor
  · rintro ⟨j, rfl⟩
    exact Greedy351495Proof.pos h j
  · intro hm
    exact Greedy351495Proof.surj h m hm
