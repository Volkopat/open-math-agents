import OMAReductions.R_OeisA2326_conjecture1_R1

/-!
For every prime below 2^21, its cube does not divide 2^(p-1) - 1.
The divisibility test uses a modular power and checks a finite interval in the kernel.
-/

namespace OMA.A002326Finite

/-- Compute the residue in two stages to keep the intermediate powers small. -/
private def residue (p : ℕ) : ℕ :=
  let e := p - 1
  let m := p ^ 3
  let u := (1 <<< (e / 64)) % m
  (u ^ 64 <<< (e % 64)) % m

private theorem residue_eq (p : ℕ) : residue p = 2 ^ (p - 1) % p ^ 3 := by
  unfold residue
  simp only [Nat.shiftLeft_eq, one_mul]
  calc
    _ = ((2 ^ ((p - 1) / 64)) ^ 64 * 2 ^ ((p - 1) % 64)) % p ^ 3 :=
      ((Nat.mod_modEq _ _).pow 64).mul_right _
    _ = _ := by
      rw [← pow_mul, ← pow_add]
      have h := Nat.mod_add_div (p - 1) 64
      congr 2
      omega

/-- A proper common factor with the product of the primes through 31 skips a composite. -/
private def passes (p : ℕ) : Bool :=
  let g := p.gcd 200560490130
  (decide (1 < g ∧ g < p)) || (residue p != 1)

private theorem passes_prime {p : ℕ} (hp : p.Prime) (h : passes p = true) :
    ¬ p ^ 3 ∣ 2 ^ (p - 1) - 1 := by
  have hg := (Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p 200560490130)
  have hproper : ¬ (1 < p.gcd 200560490130 ∧ p.gcd 200560490130 < p) := by
    rcases hg with h | h <;> omega
  have hne : 2 ^ (p - 1) % p ^ 3 ≠ 1 := by
    simpa [passes, hproper, residue_eq] using h
  intro hd
  have he := (Nat.modEq_iff_dvd' (Nat.one_le_two_pow (n := p - 1))).2 hd
  change 1 % p ^ 3 = 2 ^ (p - 1) % p ^ 3 at he
  have hbig : 1 < p ^ 3 := Nat.one_lt_pow (by decide) hp.one_lt
  rw [Nat.mod_eq_of_lt hbig] at he
  exact hne he.symm

/-- Check the interval starting at lo and having length 2^depth. -/
private def scan : ℕ → ℕ → Bool
  | 0, lo => passes lo
  | d + 1, lo => scan d lo && scan d (lo + 2 ^ d)

private theorem scan_spec (d lo : ℕ) (ok : scan d lo = true)
    (p : ℕ) (lower : lo ≤ p) (upper : p < lo + 2 ^ d) : passes p = true := by
  induction d generalizing lo with
  | zero =>
    have : p = lo := by
      simp only [pow_zero] at upper
      omega
    subst p
    exact ok
  | succ d ih =>
    simp only [scan, Bool.and_eq_true] at ok
    obtain ⟨left, right⟩ := ok
    rw [pow_succ] at upper
    by_cases h : p < lo + 2 ^ d
    · exact ih lo left lower h
    · exact ih (lo + 2 ^ d) right (by omega) (by omega)

private theorem join {d lo : ℕ} (left : scan d lo = true)
    (right : scan d (lo + 2 ^ d) = true) : scan (d + 1) lo = true := by
  simp only [scan, left, right, Bool.and_self]

-- Each leaf of the range proof checks 2048 consecutive candidates.
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem range_checked : scan 21 2 = true := by
  iterate 10 (all_goals apply join)
  all_goals decide +kernel

theorem prime_cube_not_dvd {p : ℕ} (hp : p.Prime) (limit : p < 2 ^ 21) :
    ¬ p ^ 3 ∣ 2 ^ (p - 1) - 1 := by
  exact passes_prime hp (scan_spec 21 2 range_checked p hp.two_le (by omega))

end OMA.A002326Finite

theorem OMA.solution : OMA.R_OeisA2326_conjecture1_R1.H1 := by
  intro p hp hlt
  exact OMA.A002326Finite.prime_cube_not_dvd hp (by omega)
