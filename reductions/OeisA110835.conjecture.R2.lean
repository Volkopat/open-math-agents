import FormalConjectures.OEIS.«110835»

-- Reduction OeisA110835.conjecture.R2 of Smallest $m > 0$ such that there are no primes between $nm$ and $n(m+1)$ inclusive.
-- Credit: @TheLittleOne1234
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Sierpinski's conjecture asks for a prime in [n m, n (m + 1)] for every 1 ≤ m < n. The split is by
-- the multiplier m. With x = n m the window is [x, x (1 + 1/m)].
-- H1 (1 ≤ m ≤ 7): follows from explicit Chebyshev-type bounds: a prime in (x, 6x/5] for x ≥ 25
--   (Nagura 1952), in (x, 7x/6] for x ≥ 32 and in (x, 8x/7] for x ≥ 33, plus finitely many small windows.
-- H2 (8 ≤ m < n): open; at m = n - 1 it is Oppermann's conjecture (a prime in (n (n - 1), n ^ 2)).
-- The proof of main also shows that the set in the definition of `a` is never empty (an aligned
-- window inside the composite run N! + 2, ..., N! + N with N = 2 n + 1), so sInf is a genuine minimum.

namespace OMA.R_OeisA110835_conjecture_R2

/-- Small multipliers `1 ≤ m ≤ 7`: a prime in `[n m, n (m + 1)]`. -/
def H1 : Prop := ∀ n m : ℕ, 1 ≤ m → m ≤ 7 → m < n →
  ∃ p : ℕ, p.Prime ∧ n * m ≤ p ∧ p ≤ n * (m + 1)

/-- Large multipliers `8 ≤ m < n` (open; contains Oppermann's conjecture at `m = n - 1`). -/
def H2 : Prop := ∀ n m : ℕ, 8 ≤ m → m < n →
  ∃ p : ℕ, p.Prime ∧ n * m ≤ p ∧ p ≤ n * (m + 1)

/-- The set defining `a n` is never empty: an aligned window inside `N!+2 .. N!+N`, `N = 2n+1`. -/
theorem set_nonempty (n : ℕ) (hn : 0 < n) :
    ∃ m : ℕ, m > 0 ∧ ∀ p : ℕ, p.Prime → ¬ (n * m ≤ p ∧ p ≤ n * (m + 1)) := by
  set N := 2 * n + 1 with hN
  have hF : 0 < N.factorial := Nat.factorial_pos N
  refine ⟨(N.factorial + 1) / n + 1, Nat.succ_pos _, ?_⟩
  intro p hp ⟨hlo, hhi⟩
  have h1 : N.factorial + 1 < n * ((N.factorial + 1) / n + 1) := by
    have := Nat.lt_mul_div_succ (N.factorial + 1) hn
    simpa [mul_comm] using this
  have h2 : n * ((N.factorial + 1) / n) ≤ N.factorial + 1 := Nat.mul_div_le _ _
  have hlo' : N.factorial + 2 ≤ p := by omega
  have hhi' : p ≤ N.factorial + N := by
    have : n * ((N.factorial + 1) / n + 1 + 1) = n * ((N.factorial + 1) / n) + 2 * n := by ring
    omega
  set j := p - N.factorial with hj
  have hj2 : 2 ≤ j := by omega
  have hjN : j ≤ N := by omega
  have hjdvd : j ∣ p := by
    have hd : j ∣ N.factorial := Nat.dvd_factorial (by omega) hjN
    have : p = N.factorial + j := by omega
    rw [this]; exact (Nat.dvd_add_right hd).mpr dvd_rfl
  rcases hp.eq_one_or_self_of_dvd j hjdvd with h | h
  · omega
  · omega

theorem main : H1 → H2 → type_of% @OeisA110835.conjecture := by
  intro h1 h2 n hn
  obtain ⟨m0, hm0, hfree0⟩ := set_nonempty n hn
  show n ≤ sInf {m : ℕ | m > 0 ∧ ∀ p : ℕ, p.Prime → ¬ (n * m ≤ p ∧ p ≤ n * (m + 1))}
  apply le_csInf
  · exact ⟨m0, hm0, hfree0⟩
  rintro b ⟨hb, hfree⟩
  by_contra hle
  have hlt : b < n := Nat.lt_of_not_le hle
  obtain ⟨p, hp, hp1, hp2⟩ : ∃ p : ℕ, p.Prime ∧ n * b ≤ p ∧ p ≤ n * (b + 1) := by
    rcases Nat.lt_or_ge 7 b with h | h
    · exact h2 n b (by omega) hlt
    · exact h1 n b hb h hlt
  exact hfree p hp ⟨hp1, hp2⟩

end OMA.R_OeisA110835_conjecture_R2
