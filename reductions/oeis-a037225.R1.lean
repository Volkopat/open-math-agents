import OMAStatements.S_oeis_a037225

/-!
# Reduction R1 of OEIS A037225: `a(n) = φ(2n + 1)`

The entry records two conjectures of Alain Rocchelli:

* if `2n + 1` is composite then `φ(2n + 1)` does not divide `2n`;
* `φ(2n + 1) ≠ n` for every `n`.

Both are instances of Lehmer's totient problem: a solution of either would give a
composite `m = 2n + 1` with `φ(m) ∣ m - 1`.  The reduction splits both
conjectures according to whether `2n + 1` is squarefree.

The central proved fact is that `p ∣ φ(m)` whenever `p` is a prime with
`p ^ 2 ∣ m`.  Therefore a solution of `φ(m) ∣ m - 1` forces `m` to be
squarefree: from `p ∣ m` and `p ∣ φ(m) ∣ m - 1` we get `p ∣ 1`.  This removes
every non-squarefree `m`; non-squarefree integers have density
`1 - 6 / π ^ 2 ≈ 0.392`, and among the odd values `m = 2n + 1` the density is
`1 - 8 / π ^ 2 ≈ 0.189` (37889 of the 200001 odd numbers up to 400001).

For the second conjecture there is a second obstruction: `φ(m)` is even for
`m > 2`, whereas `(m - 1) / 2` is odd when `m ≡ 3 (mod 4)`.  So `a(n) ≠ n`
holds for every `m ≡ 3 (mod 4)` as well.

The hypotheses:

* `H1` (proved): non-squarefree composite `m`: `φ(m) ∤ m - 1`.
* `H2` (open): squarefree composite `m`: `φ(m) ∤ m - 1`.
* `H3` (proved): non-squarefree `m`, or `m ≡ 3 (mod 4)`: `φ(m) ≠ (m - 1) / 2`.
* `H4` (open): squarefree `m ≡ 1 (mod 4)`: `φ(m) ≠ (m - 1) / 2`.

So the open core is exactly: squarefree composite `m` for the divisibility
conjecture, and squarefree `m ≡ 1 (mod 4)` for the equality conjecture.

Numerically (sieve for `φ` and squarefreeness, `n ≤ 200000`), no `n` violates
either conjecture, and every `n` with `2n + 1` not squarefree satisfies both `H1`
and `H3`.
-/

namespace OMA.R_oeis_a037225_R1

/-- `H1`: for a non-squarefree composite `2n + 1`, the totient does not divide
`2n`.  A prime `p` with `p ^ 2 ∣ 2n + 1` divides `φ(2n + 1)`, hence would divide
both `2n + 1` and `2n`. -/
def H1 : Prop :=
  ∀ n : ℕ, (∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ 2 * n + 1) →
    (∃ d : ℕ, d ∣ 2 * n + 1 ∧ 1 < d ∧ d < 2 * n + 1) →
    ¬ (2 * n + 1).totient ∣ 2 * n

/-- `H2`: the remaining case of the divisibility conjecture, where `2n + 1` is
squarefree.  This is the open part. -/
def H2 : Prop :=
  ∀ n : ℕ, ¬ (∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ 2 * n + 1) →
    (∃ d : ℕ, d ∣ 2 * n + 1 ∧ 1 < d ∧ d < 2 * n + 1) →
    ¬ (2 * n + 1).totient ∣ 2 * n

/-- `H3`: `φ(2n + 1) ≠ n` when `2n + 1` is not squarefree, or when
`2n + 1 ≡ 3 (mod 4)`.  In the second case `(2n + 1 - 1) / 2` is odd while
`φ` is even. -/
def H3 : Prop :=
  ∀ n : ℕ, ((∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ 2 * n + 1) ∨ (2 * n + 1) % 4 = 3) →
    (2 * n + 1).totient ≠ n

/-- `H4`: the remaining case of the equality conjecture: `2n + 1` squarefree and
`≡ 1 (mod 4)`.  This is the open part. -/
def H4 : Prop :=
  ∀ n : ℕ, ¬ (∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ 2 * n + 1) → (2 * n + 1) % 4 = 1 →
    (2 * n + 1).totient ≠ n

/-- A prime whose square divides `m` divides `φ(m)`: `φ(p ^ 2) ∣ φ(m)` and
`φ(p ^ 2) = p * (p - 1)`. -/
lemma prime_dvd_totient_of_sq_dvd {p m : ℕ} (hp : p.Prime) (h : p ^ 2 ∣ m) :
    p ∣ m.totient := by
  have hdvd : (p ^ 2).totient ∣ m.totient := Nat.totient_dvd_of_dvd h
  have hpφ : p ∣ (p ^ 2).totient := by
    have hh := Nat.totient_prime_pow_succ hp 1
    have hp2 : p ^ (1 + 1) = p ^ 2 := by norm_num
    rw [hp2] at hh
    rw [hh]
    simpa using dvd_mul_right p (p - 1)
  exact hpφ.trans hdvd

/-- A divisor of both `2n + 1` and `2n` divides `1`. -/
lemma dvd_one_of_dvd_succ {p n : ℕ} (hpm : p ∣ 2 * n + 1) (hp2n : p ∣ 2 * n) :
    p ∣ 1 := by
  have h := Nat.dvd_sub hpm hp2n
  have h1 : 2 * n + 1 - 2 * n = 1 := by omega
  rwa [h1] at h

theorem H1_proof : H1 := by
  intro n hE hcomp hdiv
  obtain ⟨p, hp, hsq⟩ := hE
  have hpφ : p ∣ (2 * n + 1).totient := prime_dvd_totient_of_sq_dvd hp hsq
  have hp2n : p ∣ 2 * n := hpφ.trans hdiv
  have hpm : p ∣ 2 * n + 1 := (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hsq
  exact hp.not_dvd_one (dvd_one_of_dvd_succ hpm hp2n)

theorem H3_proof : H3 := by
  intro n h heq
  rcases h with hE | hmod
  · obtain ⟨p, hp, hsq⟩ := hE
    have hpφ : p ∣ (2 * n + 1).totient := prime_dvd_totient_of_sq_dvd hp hsq
    have hpn : p ∣ n := by
      rwa [heq] at hpφ
    have hp2n : p ∣ 2 * n := by
      have h2 := dvd_mul_of_dvd_right hpn 2
      simpa [mul_comm] using h2
    have hpm : p ∣ 2 * n + 1 := (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hsq
    exact hp.not_dvd_one (dvd_one_of_dvd_succ hpm hp2n)
  · have h2m : 2 < 2 * n + 1 := by omega
    have heven : (2 * n + 1).totient % 2 = 0 := by
      obtain ⟨k, hk⟩ := Nat.totient_even h2m
      omega
    rw [heq] at heven
    omega

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a037225.main := by
  intro h1 h2 h3 h4
  constructor
  · intro n hcomp
    by_cases hE : ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ 2 * n + 1
    · simpa [OMA.S_oeis_a037225.a] using h1 n hE hcomp
    · simpa [OMA.S_oeis_a037225.a] using h2 n hE hcomp
  · intro n
    by_cases hE : ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ 2 * n + 1
    · simpa [OMA.S_oeis_a037225.a] using h3 n (Or.inl hE)
    · by_cases hmod : (2 * n + 1) % 4 = 1
      · simpa [OMA.S_oeis_a037225.a] using h4 n hE hmod
      · simpa [OMA.S_oeis_a037225.a] using h3 n (Or.inr (by omega))

end OMA.R_oeis_a037225_R1
