import OMAStatements.S_mo_435208
import Mathlib

/-!
# mo-435208 (Q1): the question is exactly the infinitude of non-Wieferich primes

`main` (Q1) says: if only finitely many odd primes are non-Wieferich, then only finitely many odd
squarefree numbers are non-Wieferich. This file shows that Q1 is true only vacuously.

* Theorem `U` (unconditional, proved here): infinitely many odd squarefree numbers are
  non-Wieferich. The witnesses are `n = 3 r` for primes `r ≡ 2 (mod 3)`, `r > 3`. Then
  `φ(3 r) = 2 (r - 1)`, `r - 1 ≡ 1 (mod 3)`, and `2 ^ φ = 4 * 64 ^ k ≡ 4 (mod 9)`. So
  `9 ∤ 2 ^ φ - 1`, while `9 ∣ (3 r) ^ 2`. Dirichlet's theorem (Mathlib) supplies the primes.
* `main_iff` (proved here): Q1 holds if and only if there are infinitely many odd
  non-Wieferich primes. That statement is open. It follows from the abc conjecture
  (Silverman, J. Number Theory 30 (1988)).

The reduction routes the open direction through Mersenne numbers.
* `H1` (open): for infinitely many primes `q`, the Mersenne number `2 ^ q - 1` is not powerful,
  that is, some prime divides it exactly once. This is implied by the conjecture that every
  `2 ^ q - 1` is squarefree, and it also follows from abc.
* `H2` (elementary, proved here as `H2_holds`): if a prime `p` divides `2 ^ q - 1` exactly once
  (`q` prime), then `q < p` and `p` is non-Wieferich. The proof uses the order of `2` mod `p` and
  the lifting-the-exponent lemma: `v_p(2 ^ (p - 1) - 1) = v_p(2 ^ q - 1) + v_p((p - 1) / q) = 1`.
`main` then follows. If non-Wieferich primes were bounded by `B`, a prime `q > B` from `H1`
would give a non-Wieferich prime `p > q > B`.
-/

namespace OMA.R_mo_435208_R1

open OMA.S_mo_435208 (IsWieferich)

/-- For infinitely many primes `q`, the Mersenne number `2 ^ q - 1` is not powerful: some prime
divides it exactly once. -/
def H1 : Prop :=
  {q : ℕ | q.Prime ∧ ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ q - 1 ∧ ¬ p ^ 2 ∣ 2 ^ q - 1}.Infinite

/-- A prime dividing a prime-exponent Mersenne number exactly once exceeds the exponent and is
non-Wieferich. This is elementary (order of 2 and lifting the exponent); see `H2_holds`. -/
def H2 : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p ∣ 2 ^ q - 1 → ¬ p ^ 2 ∣ 2 ^ q - 1 →
    q < p ∧ ¬ p ^ 2 ∣ 2 ^ (p - 1) - 1

theorem ne_two_of_dvd_mersenne {p q : ℕ} (hq : q.Prime) (hdvd : p ∣ 2 ^ q - 1) : p ≠ 2 := by
  rintro rfl
  have h2 : 2 ∣ 2 ^ q := dvd_pow_self 2 hq.ne_zero
  have h1 : 1 ≤ 2 ^ q := Nat.one_le_two_pow
  omega

theorem H2_holds : H2 := by
  intro p q hp hq hdvd hndvd
  have := Fact.mk hp
  have hp2 : p ≠ 2 := ne_two_of_dvd_mersenne hq hdvd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpow1 : 1 ≤ 2 ^ q := Nat.one_le_two_pow
  have h1 : (2 : ZMod p) ^ q = 1 := by
    have h := (ZMod.natCast_eq_zero_iff (2 ^ q - 1) p).2 hdvd
    rw [Nat.cast_sub hpow1] at h
    push_cast at h
    exact sub_eq_zero.1 h
  have hord : orderOf (2 : ZMod p) = q := by
    have hd : orderOf (2 : ZMod p) ∣ q := orderOf_dvd_of_pow_eq_one h1
    rcases (Nat.dvd_prime hq).1 hd with h | h
    · exfalso
      rw [orderOf_eq_one_iff] at h
      have h' : ((2 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by exact_mod_cast h
      have := (ZMod.natCast_eq_natCast_iff' 2 1 p).1 h'
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      omega
    · exact h
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 p).1 h')
    omega
  have hqdvd : q ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one h20
  obtain ⟨m, hm⟩ := hqdvd
  have hq2 := hq.two_le
  have hm0 : m ≠ 0 := by
    rintro rfl
    omega
  have hmle : m ≤ p - 1 := by
    rw [hm]
    exact Nat.le_mul_of_pos_left m (by omega)
  have hqp : q < p := by
    have := Nat.le_of_dvd (by omega) ⟨m, hm⟩
    omega
  refine ⟨hqp, ?_⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hne : 2 ^ q - 1 ≠ 0 := by
    have := Nat.one_lt_two_pow hq.ne_zero
    omega
  have hv1 : padicValNat p (2 ^ q - 1) = 1 := by
    have a := (padicValNat_dvd_iff_le (p := p) (n := 1) hne).1 (by simpa using hdvd)
    have b : ¬ 2 ≤ padicValNat p (2 ^ q - 1) := fun h =>
      hndvd ((padicValNat_dvd_iff_le hne).2 h)
    omega
  have hvm : padicValNat p m = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hnp : ¬ p ∣ 2 ^ q := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have key := padicValNat.pow_sub_pow (p := p) hodd (x := 2 ^ q) (y := 1)
    (Nat.one_lt_two_pow hq.ne_zero) hdvd hnp hm0
  rw [one_pow, ← pow_mul, ← hm, hv1, hvm] at key
  intro hcon
  have hne' : 2 ^ (p - 1) - 1 ≠ 0 := by
    have := Nat.one_lt_two_pow (n := p - 1) (by omega)
    omega
  have := (padicValNat_dvd_iff_le hne').1 hcon
  omega

/-- `3 r` is not a Wieferich number for a prime `r ≡ 2 (mod 3)`. -/
theorem not_wieferich_three_mul {r : ℕ} (hr : r.Prime) (h3 : r % 3 = 2) :
    ¬ IsWieferich (3 * r) := by
  intro h
  have hr3 : r ≠ 3 := by
    rintro rfl
    norm_num at h3
  have hcop : Nat.Coprime 3 r := (Nat.coprime_primes Nat.prime_three hr).2 (Ne.symm hr3)
  have htot : Nat.totient (3 * r) = 2 * (r - 1) := by
    rw [Nat.totient_mul hcop, Nat.totient_prime Nat.prime_three, Nat.totient_prime hr]
  unfold IsWieferich at h
  rw [htot] at h
  have h9 : 9 ∣ 2 ^ (2 * (r - 1)) - 1 := by
    have : (9 : ℕ) ∣ (3 * r) ^ 2 := ⟨r ^ 2, by ring⟩
    exact this.trans h
  obtain ⟨k, hk⟩ : ∃ k, r - 1 = 3 * k + 1 := ⟨(r - 1) / 3, by omega⟩
  rw [hk] at h9
  have hpow : 2 ^ (2 * (3 * k + 1)) = 64 ^ k * 4 := by
    rw [show 2 * (3 * k + 1) = 6 * k + 2 by ring, pow_add, pow_mul]
    norm_num
  rw [hpow] at h9
  have hmod : 64 ^ k * 4 % 9 = 4 := by
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  omega

/-- Theorem U: there are infinitely many odd squarefree non-Wieferich numbers. -/
theorem U : {n : ℕ | Odd n ∧ Squarefree n ∧ ¬ IsWieferich n}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have hu : IsUnit (2 : ZMod 3) := ⟨⟨2, 2, by decide, by decide⟩, rfl⟩
  obtain ⟨r, hrB, hr, hr2⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu (B + 3)
  have h3 : r % 3 = 2 := by
    rw [← ZMod.val_natCast, hr2]
    rfl
  have hr3 : r ≠ 3 := by omega
  have hrn2 : r ≠ 2 := by omega
  have hcop : Nat.Coprime 3 r := (Nat.coprime_primes Nat.prime_three hr).2 (Ne.symm hr3)
  have hmem : 3 * r ∈ {n : ℕ | Odd n ∧ Squarefree n ∧ ¬ IsWieferich n} :=
    ⟨Odd.mul (by decide) (hr.odd_of_ne_two hrn2),
      Nat.squarefree_mul_iff.2 ⟨hcop, Nat.prime_three.squarefree, hr.squarefree⟩,
      not_wieferich_three_mul hr h3⟩
  have := hB hmem
  omega

/-- Q1 is equivalent to the infinitude of odd non-Wieferich primes (so it holds only
vacuously, by `U`). -/
theorem main_iff : type_of% @OMA.S_mo_435208.main ↔
    {p : ℕ | p.Prime ∧ p ≠ 2 ∧ ¬ IsWieferich p}.Infinite := by
  constructor
  · intro h hfin
    exact U (h hfin)
  · intro h hfin
    exact (h hfin).elim

theorem main : H1 → H2 → type_of% @OMA.S_mo_435208.main := by
  intro h1 h2 hfin
  exfalso
  obtain ⟨B, hB⟩ := hfin.bddAbove
  obtain ⟨q, ⟨hq, p, hp, hdvd, hndvd⟩, hqB⟩ := not_bddAbove_iff.1 h1.not_bddAbove B
  obtain ⟨hqp, hnw⟩ := h2 p q hp hq hdvd hndvd
  have hmem : p ∈ {p : ℕ | p.Prime ∧ p ≠ 2 ∧ ¬ IsWieferich p} := by
    refine ⟨hp, ne_two_of_dvd_mersenne hq hdvd, ?_⟩
    unfold IsWieferich
    rw [Nat.totient_prime hp]
    exact hnw
  have := hB hmem
  omega

end OMA.R_mo_435208_R1
