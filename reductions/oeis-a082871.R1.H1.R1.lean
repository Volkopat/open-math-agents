import OMAReductions.R_oeis_a082871_R1
import Mathlib

/-!
# Brocard's equation at primes above n

For q = n+d+1 prime, write D = (-1)^d d! modulo q. Wilson's theorem gives
n! D = -1. Multiplying a putative square 1+n! by D² shows that D(D-1)
must be a square modulo q. The primes n < q ≤ 2n give a finite collection
of tests for each n.

When p = n+1 itself is prime, Wilson's theorem also forces p to divide the
root, so p² divides 1+n! and the quotient must still be square. This gives a
separate residual problem indexed by Wilson primes. When n+1 is composite,
only inputs passing the finite collection of tests require an odd-exponent
prime factor of 1+n!. Every prime factor of 1+n! is greater than n.

As a consequence of the gap tests, the file proves there are arbitrarily large
runs of ten consecutive inputs for which the factorial plus one is nonsquare.

The use of modular nonresidues in computational searches for Brocard's
equation is due to Berndt and Galway, as documented in
`Erdos398.erdos_398.R1.H3.R1`. These two steps concern the unbounded inputs.
-/

namespace OMA.R_oeis_a082871_R1_H1_R1

/-- Wilson's theorem, with the last d factors separated off. -/
lemma gap_factorial_identity {n d p : ℕ} [Fact p.Prime] (h : n + d + 1 = p) :
    (n.factorial : ZMod p) * ((-1) ^ d * (d.factorial : ZMod p)) = -1 := by
  have hprod := Nat.factorial_mul_descFactorial (show d ≤ p - 1 by omega)
  rw [show p - 1 - d = n by omega] at hprod
  have hcast := congrArg (fun m : ℕ => (m : ZMod p)) hprod
  simpa only [Nat.cast_mul, ZMod.cast_descFactorial (show d ≤ p by omega),
    ZMod.wilsons_lemma] using hcast

/-- A Brown number survives a quadratic-residue test depending only on the gap
to any greater prime. The signed factorial is (-1)^d d!, where d = p - n - 1. -/
theorem gap_square {n d p : ℕ} [Fact p.Prime] (h : n + d + 1 = p)
    (sq : IsSquare (1 + n.factorial)) :
    let D := (-1 : ZMod p) ^ d * (d.factorial : ZMod p)
    IsSquare (D * (D - 1)) := by
  let D := (-1 : ZMod p) ^ d * (d.factorial : ZMod p)
  obtain ⟨r, hr⟩ := sq
  have hr' : 1 + (n.factorial : ZMod p) = (r : ZMod p) * (r : ZMod p) := by
    simpa using congrArg (fun k : ℕ => (k : ZMod p)) hr
  have hw : (n.factorial : ZMod p) * D = -1 := gap_factorial_identity h
  change IsSquare (D * (D - 1))
  refine ⟨D * r, ?_⟩
  calc
    D * (D - 1) = D * (D + (n.factorial : ZMod p) * D) := by rw [hw]; ring
    _ = D * D * (1 + (n.factorial : ZMod p)) := by ring
    _ = (D * r) * (D * r) := by rw [hr']; ring

/-- A gap obstruction found modulo an odd seed repeats on a prime progression. -/
theorem periodic_gap_obstruction {n d p r M : ℕ} [Fact p.Prime]
    (h : n + d + 1 = p) (hp : Odd p) (hr : Odd r)
    (hpclass : p ≡ r [MOD M]) :
    let a := (-1 : ℤ)^d * d.factorial
    let c := a * (a - 1)
    4 * c.natAbs ∣ M → jacobiSym c r = -1 → ¬ IsSquare (1 + n.factorial) := by
  dsimp only
  let a := (-1 : ℤ)^d * d.factorial
  let c := a * (a - 1)
  intro hM hseed hs
  have heq : p % (4 * c.natAbs) = r % (4 * c.natAbs) := hpclass.of_dvd hM
  have hJac : jacobiSym c p = -1 := by
    rw [jacobiSym.mod_right c hp, heq, ← jacobiSym.mod_right c hr]
    exact hseed
  apply ZMod.nonsquare_of_jacobiSym_eq_neg_one hJac
  simpa [c, a] using gap_square h hs

/-- A single progression produces infinitely many runs of ten consecutive
non-Brown numbers. The seed is 181 and the relevant Wilson gaps are 9 through 18. -/
theorem ten_consecutive_exclusions (N : ℕ) :
    ∃ n > N, ∀ k ≤ 9, ¬ IsSquare (1 + (n + k).factorial) := by
  let M : ℕ :=
    369646198116184849581367504438392355144477419220442326633638324478769311259068905341578015319955884364328742119636992000
  obtain ⟨p, hpN, hp, hclass⟩ := Nat.forall_exists_prime_gt_and_modEq (N + 19)
    (q := M) (a := 181) (by decide) (by decide)
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨p - 19, by omega, ?_⟩
  intro k hk
  have facts : ∀ d : ℕ, 9 ≤ d → d ≤ 18 →
      let a := (-1 : ℤ)^d * d.factorial
      let c := a * (a - 1)
      4 * c.natAbs ∣ M ∧ jacobiSym c 181 = -1 := by
    intro d lo hi
    interval_cases d <;> norm_num [Nat.factorial, M]
  have data := facts (18-k) (by omega) (by omega)
  exact periodic_gap_obstruction (d := 18-k) (by omega) (hp.odd_of_ne_two (by omega))
    (by decide) hclass data.1 data.2

/-- For a Wilson prime bigger than seven, the Wilson quotient divided by p
cannot be a square. This quotient is ((p-1)!+1)/p². -/
def H1 : Prop := ∀ p : ℕ, 7 < p → p.Prime → p^2 ∣ 1 + (p-1).factorial →
    ¬ IsSquare ((1 + (p-1).factorial) / p^2)

/-- For composite successors surviving the finite Wilson-gap sieve, find a
prime factor of odd multiplicity above n. -/
def H2 : Prop := ∀ n : ℕ, 7 < n → ¬ (n+1).Prime →
    (∀ d : ℕ, d < n → (n+d+1).Prime →
      let D := (-1 : ZMod (n+d+1))^d * (d.factorial : ZMod (n+d+1))
      IsSquare (D * (D-1))) →
    ∃ q : ℕ, q.Prime ∧ n < q ∧ Odd ((1 + n.factorial).factorization q)

theorem main : H1 → H2 → OMA.R_oeis_a082871_R1.H1 := by
  intro hprime hcomp n hs
  by_cases hn : 7 < n
  · exfalso
    by_cases hp : (n+1).Prime
    · let p := n+1
      have : Fact p.Prime := ⟨hp⟩
      have hpred : p-1 = n := by simp [p]
      have hd : p ∣ 1 + n.factorial := by
        apply (ZMod.natCast_eq_zero_iff _ _).mp
        rw [← hpred]
        simp [ZMod.wilsons_lemma]
      obtain ⟨r, hr⟩ := hs
      rw [hr] at hd
      obtain ⟨s, hrs⟩ := (hp.dvd_mul.mp hd).elim id id
      have heq : 1 + (p-1).factorial = p^2 * (s*s) := by
        rw [hpred, hr, hrs]
        ring
      have hd2 : p^2 ∣ 1 + (p-1).factorial := ⟨s*s, heq⟩
      apply hprime p (by dsimp [p]; omega) hp hd2
      refine ⟨s, ?_⟩
      rw [heq, Nat.mul_div_cancel_left _ (pow_pos hp.pos 2)]
    · have htest (d : ℕ) (_ : d < n) (hq : (n+d+1).Prime) := @gap_square n d (n+d+1) ⟨hq⟩ rfl hs
      obtain ⟨q, _, _, hodd⟩ := hcomp n hn hp htest
      obtain ⟨r, hr⟩ := hs
      have hr0 : r ≠ 0 := by
        intro h
        simp [h] at hr
      rw [hr, Nat.factorization_mul hr0 hr0, Finsupp.add_apply] at hodd
      obtain ⟨k, hk⟩ := hodd
      omega
  · have checked : ∀ a : Fin 8, IsSquare (1+a.val.factorial) → a.val=4 ∨ a.val=5 ∨ a.val=7 := by
      decide +kernel
    exact checked ⟨n, by omega⟩ hs

end OMA.R_oeis_a082871_R1_H1_R1
