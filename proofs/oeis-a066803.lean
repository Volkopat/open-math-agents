import OMAStatements.S_oeis_a066803

-- Problem: A066803: a(n) = gcd(2^n + 1, 3^n + 1).
-- Upstream: formal-conjectures statements/oeis-a066803.lean:0 (declaration OMA.S_oeis_a066803.main)
-- Credit: @laurenceday (the owner of the agent is credited as the solver)
--
-- Disproof. The conjecture a(2^k) = 1 for k != 1 fails at k = 38:
-- the prime p = 3 * 2^41 + 1 = 6597069766657 divides both 2^(2^38) + 1 and 3^(2^38) + 1.
-- Reason: p is the classical factor of the Fermat number F_38, so 2^(2^38) = -1 mod p, and
-- 3 * 2^41 = -1 mod p gives 3^(2^38) = (2^(2^38))^(-41) = (-1)^(-41) = -1 mod p.
-- (The same argument works for every prime 3 * 2^m + 1 with m odd that divides a Fermat number.)
-- Each divisibility is checked below by 38 modular squarings; the huge powers are never evaluated.

/-- `OMA.sqIter p j x` squares `x` modulo `p`, `j` times. -/
def OMA.sqIter (p : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | j + 1, x => OMA.sqIter p j (x * x % p)

theorem OMA.sqIter_spec (p : ℕ) :
    ∀ (j x : ℕ), x ^ (2 ^ j) % p = OMA.sqIter p j (x % p) % p := by
  intro j
  induction j with
  | zero =>
    intro x
    simp [OMA.sqIter]
  | succ j ih =>
    intro x
    have h : x ^ (2 ^ (j + 1)) = (x * x) ^ (2 ^ j) := by
      rw [pow_succ, pow_mul', pow_two]
    rw [h, ih (x * x)]
    show OMA.sqIter p j (x * x % p) % p = OMA.sqIter p j (x % p * (x % p) % p) % p
    rw [Nat.mul_mod]

theorem OMA.dvd_of_sqIter (b : ℕ)
    (e : OMA.sqIter 6597069766657 38 (b % 6597069766657) % 6597069766657 = 6597069766656) :
    6597069766657 ∣ b ^ (2 ^ 38) + 1 := by
  have h : b ^ (2 ^ 38) % 6597069766657 = 6597069766656 :=
    (OMA.sqIter_spec 6597069766657 38 b).trans e
  have h2 : (b ^ (2 ^ 38) + 1) % 6597069766657
      = (6597069766656 + 1 % 6597069766657) % 6597069766657 := by
    rw [Nat.add_mod, h]
  exact Nat.dvd_of_mod_eq_zero (h2.trans (by decide))

theorem OMA.gcd_ne_one_of_dvd {a b p : ℕ} (hp : 1 < p) (ha : p ∣ a) (hb : p ∣ b) :
    Nat.gcd a b ≠ 1 := by
  intro h
  have hd := Nat.dvd_gcd ha hb
  rw [h] at hd
  exact absurd (Nat.le_of_dvd Nat.one_pos hd) (Nat.not_le.mpr hp)

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a066803.main) := by
  intro h
  refine OMA.gcd_ne_one_of_dvd (p := 6597069766657) (by decide) ?_ ?_ (h 38 (by decide))
  · exact OMA.dvd_of_sqIter 2 (by decide)
  · exact OMA.dvd_of_sqIter 3 (by decide)
