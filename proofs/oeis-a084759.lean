import OMAStatements.S_oeis_a084759

/-!
Distinct gaps eventually exceed every fixed integer. If a gap r were
missing, the greedy rule would therefore make a(n)+r prime for all large n.
Parity would force all later gaps to be even. Three unused odd gaps d,d+2,d+4
would then yield three simultaneous primes greater than 3 in a complete
residue system modulo 3.
-/

namespace CompositeGaps

open OMA.S_oeis_a084759 Finset Filter

private noncomputable def gap (n : ℕ) := a (n+1) - a n

private def candidates (n : ℕ) : Set ℕ :=
  {m | IsComposite m ∧ a n < m ∧ ∀ i < n, m - a n ≠ gap i}

private theorem next_eq (n : ℕ) : a (n+1) = sInf (candidates n) := by
  rw [a]
  rfl

private theorem available (n : ℕ) : (candidates n).Nonempty := by
  let b := (range n).sup gap
  let m := 2*(a n+b+2)
  have big : 2 < m := by dsimp [m]; omega
  have composite : IsComposite m := by
    refine ⟨by omega, ?_⟩
    intro hp
    have := hp.eq_one_or_self_of_dvd 2 (show 2 ∣ m from ⟨_, rfl⟩)
    omega
  refine ⟨m, composite, by dsimp [m]; omega, ?_⟩
  intro i hi
  have le : gap i ≤ b := le_sup (f := gap) (mem_range.mpr hi)
  dsimp [m]
  omega

private theorem chosen (n : ℕ) : a (n+1) ∈ candidates n := by
  rw [next_eq]
  exact Nat.sInf_mem (available n)

private theorem increasing : StrictMono a :=
  strictMono_nat_of_lt_succ fun n => (chosen n).2.1

private theorem large (n : ℕ) : 4 ≤ a n := by
  have h := increasing.monotone (Nat.zero_le n)
  rwa [show a 0 = 4 by rw [a]] at h

private theorem unique_gaps : Function.Injective gap := by
  intro i j h
  rcases lt_trichotomy i j with hlt | eq | hgt
  · exact False.elim ((chosen j).2.2 i hlt h.symm)
  · exact eq
  · exact False.elim ((chosen i).2.2 j hgt h)

private theorem missing_forces_primes {r : ℕ} (hr : 0 < r) (miss : ∀ n, gap n ≠ r) :
    ∀ᶠ n in atTop, (a n+r).Prime := by
  filter_upwards [(tendsto_atTop.mp unique_gaps.nat_tendsto_atTop) (r+1)] with n hn
  by_contra hp
  have valid : a n+r ∈ candidates n := by
    refine ⟨⟨by have := large n; omega, hp⟩, by omega, ?_⟩
    intro i _
    simpa using (miss i).symm
  have le := csInf_le (OrderBot.bddBelow _) valid
  rw [← next_eq] at le
  unfold gap at hn
  omega

private theorem misses_none (r : ℕ) (hr : 0 < r) : ∃ n, gap n = r := by
  by_contra! miss
  obtain ⟨N, after⟩ := eventually_atTop.mp (missing_forces_primes hr miss)
  have parity (n : ℕ) (hn : N ≤ n) : (a n+r)%2 = 1 := by
    have bigger := large n
    exact (after n hn).mod_two_eq_one_iff_ne_two.mpr (by omega)
  have gaps_even (n : ℕ) (hn : N ≤ n) : gap n % 2 = 0 := by
    have := parity n hn
    have := parity (n+1) (by omega)
    have := increasing (Nat.lt_succ_self n)
    unfold gap
    omega
  let B := (range N).sup gap
  have missing_odd (s : ℕ) (hs : B < s) (odd : s % 2 = 1) : ∀ n, gap n ≠ s := by
    intro n
    by_cases hn : n < N
    · have h : gap n ≤ B := le_sup (f := gap) (mem_range.mpr hn)
      omega
    · have := gaps_even n (by omega)
      omega
  let d := 2*B+1
  have p₀ := missing_forces_primes (r := d) (by dsimp [d]; omega)
    (missing_odd d (by dsimp [d]; omega) (by dsimp [d]; omega))
  have p₂ := missing_forces_primes (r := d+2) (by omega)
    (missing_odd (d+2) (by dsimp [d]; omega) (by dsimp [d]; omega))
  have p₄ := missing_forces_primes (r := d+4) (by omega)
    (missing_odd (d+4) (by dsimp [d]; omega) (by dsimp [d]; omega))
  obtain ⟨n, hn, hn₂, hn₄⟩ := (p₀.and (p₂.and p₄)).exists
  have avoid (p : ℕ) (hp : p.Prime) (h3 : 3 < p) : p % 3 ≠ 0 := by
    intro h
    have := hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h)
    omega
  have big := large n
  have := avoid _ hn (by omega)
  have := avoid _ hn₂ (by omega)
  have := avoid _ hn₄ (by omega)
  omega

end CompositeGaps

open OMA.S_oeis_a084759 CompositeGaps

theorem OMA.solution : type_of% @OMA.S_oeis_a084759.main := by
  intro r hr
  obtain ⟨n, hn⟩ := misses_none r hr
  exact ⟨n+1, by omega, by simpa [gap] using hn⟩
