import FormalConjectures.OEIS.«110835»

-- Reduction OeisA110835.conjecture.R1 of Smallest $m > 0$ such that there are no primes between $nm$ and $n(m+1)$ inclusive.
-- Credit: @TheLittleOne1234
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Sierpinski's conjecture asks for a prime in [n m, n (m + 1)] for every 1 ≤ m < n. The split is by
-- the size of the multiplier m. For m ≤ 5 the interval is [x, x (1 + 1/m)] with x = n m and
-- 1 + 1/m ≥ 6/5, so H1 follows from Nagura's theorem (1952: a prime in (x, 6x/5) for x ≥ 25)
-- plus finitely many small cases: a known result, not yet formalized. H2 (6 ≤ m < n) is the open
-- part; at m = n - 1 it contains Oppermann's conjecture. The proof of main also shows that the set
-- in the definition of `a` is never empty (long runs of composites after a factorial), so that
-- sInf is a genuine minimum and not the junk value 0.

namespace OMA.R_OeisA110835_conjecture_R1

/-- Small multipliers (known: Nagura 1952 plus small cases). -/
def H1 : Prop := ∀ n m : ℕ, 1 ≤ m → m ≤ 5 → m < n →
  ∃ p : ℕ, p.Prime ∧ n * m ≤ p ∧ p ≤ n * (m + 1)

/-- Large multipliers (open; contains Oppermann's conjecture at m = n - 1). -/
def H2 : Prop := ∀ n m : ℕ, 6 ≤ m → m < n →
  ∃ p : ℕ, p.Prime ∧ n * m ≤ p ∧ p ≤ n * (m + 1)

/-- For every n > 0 some interval [n m, n (m + 1)] with m > 0 contains no prime: it sits inside
the composite run (2n+2)! + 2, ..., (2n+2)! + (2n+2). -/
lemma nonempty_free (n : ℕ) (hn : 0 < n) :
    ∃ m : ℕ, m > 0 ∧ ∀ p : ℕ, p.Prime → ¬ (n * m ≤ p ∧ p ≤ n * (m + 1)) := by
  refine ⟨((2 * n + 2).factorial + 1) / n + 1, Nat.succ_pos _, ?_⟩
  rintro p hp ⟨h1, h2⟩
  have hF : 0 < (2 * n + 2).factorial := Nat.factorial_pos _
  have hdm := Nat.div_add_mod ((2 * n + 2).factorial + 1) n
  have hr := Nat.mod_lt ((2 * n + 2).factorial + 1) hn
  generalize ((2 * n + 2).factorial + 1) / n = q at h1 h2 hdm
  generalize ((2 * n + 2).factorial + 1) % n = r at hdm hr
  have e1 : n * (q + 1) = n * q + n := by ring
  have e2 : n * (q + 1 + 1) = n * q + n + n := by ring
  rw [e1] at h1
  rw [e2] at h2
  generalize n * q = A at h1 h2 hdm
  have hj : p - (2 * n + 2).factorial ∣ (2 * n + 2).factorial :=
    Nat.dvd_factorial (by omega) (by omega)
  have hjp : p - (2 * n + 2).factorial ∣ p := by
    have hsplit : p = (2 * n + 2).factorial + (p - (2 * n + 2).factorial) := by omega
    have : p - (2 * n + 2).factorial ∣ (2 * n + 2).factorial + (p - (2 * n + 2).factorial) :=
      (Nat.dvd_add_right hj).2 dvd_rfl
    rwa [← hsplit] at this
  rcases hp.eq_one_or_self_of_dvd _ hjp with h | h <;> omega

theorem main : H1 → H2 → type_of% @OeisA110835.conjecture := by
  intro h1 h2 n hn
  obtain ⟨m0, hm0, hfree0⟩ := nonempty_free n hn
  show n ≤ sInf {m : ℕ | m > 0 ∧ ∀ p : ℕ, p.Prime → ¬ (n * m ≤ p ∧ p ≤ n * (m + 1))}
  apply le_csInf
  · exact ⟨m0, hm0, hfree0⟩
  rintro b ⟨hb, hfree⟩
  by_contra hle
  have hlt : b < n := Nat.lt_of_not_le hle
  obtain ⟨p, hp, hp1, hp2⟩ : ∃ p : ℕ, p.Prime ∧ n * b ≤ p ∧ p ≤ n * (b + 1) := by
    rcases Nat.lt_or_ge 5 b with h | h
    · exact h2 n b (by omega) hlt
    · exact h1 n b hb h hlt
  exact hfree p hp ⟨hp1, hp2⟩

end OMA.R_OeisA110835_conjecture_R1
