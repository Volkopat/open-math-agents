import OMAStatements.S_oeis_a087372

theorem OMA.h04_prime_gap (B : ℕ) (hB : 2 ≤ B) :
    ∃ p : ℕ, p.Prime ∧ B + 2 < p ∧
      ∀ j : ℕ, p - B < j → j < p → ¬ j.Prime := by
  have hex := Nat.exists_infinite_primes (B.factorial + 2)
  let p := Nat.find hex
  have hp : B.factorial + 2 ≤ p ∧ p.Prime := Nat.find_spec hex
  have hgap : B.factorial + B < p := by
    by_contra hnot
    have hupper : p ≤ B.factorial + B := by omega
    let d := p - B.factorial
    have hd2 : 2 ≤ d := by omega
    have hdB : d ≤ B := by omega
    have hdiv : d ∣ p := by
      have heq : p = B.factorial + d := by omega
      rw [heq]
      exact Nat.dvd_add (Nat.dvd_factorial (by omega) hdB) (dvd_refl d)
    have heq : p = d := (hp.2.dvd_iff_eq (by omega : d ≠ 1)).mp hdiv
    have hpos := Nat.factorial_pos B
    omega
  have hself := Nat.self_le_factorial B
  refine ⟨p, hp.2, by omega, ?_⟩
  intro j hjlow hjhigh hjprime
  have hj : B.factorial + 2 ≤ j := by omega
  have hmin : p ≤ j := Nat.find_min' hex ⟨hj, hjprime⟩
  omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a087372.main) := by
  change ¬ (∃ M : ℕ, ∀ n : ℕ, 1 ≤ n →
    sInf {k : ℕ | (3 ^ k + 2 * n).Prime} < M)
  rintro ⟨M, hM⟩
  let B : ℕ := 3 ^ (M + 1)
  have hB : 2 ≤ B := by
    dsimp [B]
    rw [pow_succ]
    have hpos : 0 < 3 ^ M := Nat.pow_pos (by decide)
    omega
  obtain ⟨p, hp, hlarge, hgap⟩ := OMA.h04_prime_gap B hB
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hBodd : B % 2 = 1 := by simp [B, Nat.pow_mod]
  let n : ℕ := (p - B) / 2
  have heq : B + 2 * n = p := by dsimp [n]; omega
  have hn : 1 ≤ n := by omega
  have hset : Set.Nonempty {k : ℕ | (3 ^ k + 2 * n).Prime} :=
    ⟨M + 1, by change (B + 2 * n).Prime; rw [heq]; exact hp⟩
  let k : ℕ := sInf {j : ℕ | (3 ^ j + 2 * n).Prime}
  have hkprime : (3 ^ k + 2 * n).Prime := Nat.sInf_mem hset
  have hklt : k < M + 1 := by have := hM n hn; dsimp [k]; omega
  have hpow : 3 ^ k < B := Nat.pow_lt_pow_right (by decide) hklt
  have hpowpos : 0 < 3 ^ k := Nat.pow_pos (by decide)
  exact hgap (3 ^ k + 2 * n) (by omega) (by omega) hkprime
