import OMAStatements.S_oeis_a027697

/-! Express the prime race and its growing lead through counting functions. -/

namespace OMA.R_oeis_a027697_R1

open Filter OMA.S_oeis_a027697

/-- Both parity classes contain infinitely many primes. -/
def H1 : Prop :=
  {p : ℕ | p.Prime ∧ Odd (s2 p)}.Infinite ∧
    {p : ℕ | p.Prime ∧ Even (s2 p)}.Infinite

/-- At each even-parity prime other than the second, strictly more odd-parity
primes precede it than even-parity primes. -/
def H2 : Prop :=
  ∀ x : ℕ, x.Prime ∧ Even (s2 x) →
    Nat.count (fun p => p.Prime ∧ Even (s2 p)) x ≠ 1 →
    Nat.count (fun p => p.Prime ∧ Even (s2 p)) x <
      Nat.count (fun p => p.Prime ∧ Odd (s2 p)) x

/-- At sufficiently large odd-parity primes, the lead survives any fixed shift
of the cutoff for counting even-parity primes. -/
def H3 : Prop :=
  ∀ B : ℕ, ∀ᶠ x : ℕ in atTop, x.Prime ∧ Odd (s2 x) →
    Nat.count (fun p => p.Prime ∧ Even (s2 p)) (x + B) ≤
      Nat.count (fun p => p.Prime ∧ Odd (s2 p)) x

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a027697.main := by
  intro hInfinite hDominance hShift
  obtain ⟨hOdd, hEven⟩ := hInfinite
  constructor
  · intro n hn hSecond
    have hPrime : (evil n).Prime ∧ Even (s2 (evil n)) :=
      Nat.nth_mem_of_infinite hEven (n - 1)
    have hIndex : Nat.count (fun p => p.Prime ∧ Even (s2 p)) (evil n) = n - 1 :=
      Nat.count_nth_of_infinite hEven (n - 1)
    have hCount := hDominance (evil n) hPrime (by rw [hIndex]; omega)
    rw [hIndex] at hCount
    exact Nat.nth_lt_of_lt_count hCount
  · refine tendsto_atTop.2 fun b => ?_
    obtain ⟨X, hX⟩ := eventually_atTop.1 (hShift b.toNat)
    filter_upwards [eventually_ge_atTop (X + 1)] with n hn
    have hIndex : Nat.count (fun p => p.Prime ∧ Odd (s2 p)) (odious n) = n - 1 :=
      Nat.count_nth_of_infinite hOdd (n - 1)
    have hBound : Nat.count (fun p => p.Prime ∧ Odd (s2 p)) (odious n) ≤ odious n :=
      Nat.count_le _
    have hLarge : X ≤ odious n := by omega
    have hPrime : (odious n).Prime ∧ Odd (s2 (odious n)) :=
      Nat.nth_mem_of_infinite hOdd (n - 1)
    have hCount := hX (odious n) hLarge hPrime
    rw [hIndex] at hCount
    have hGap : odious n + b.toNat ≤ evil n :=
      (Nat.count_le_iff_le_nth hEven).mp hCount
    omega

end OMA.R_oeis_a027697_R1
