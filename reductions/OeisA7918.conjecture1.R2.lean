import FormalConjectures.OEIS.«7918»
import Mathlib

/-! We verify a finite initial range and isolate the remaining estimate
on the least step passing a finite prime sieve. The elementary lower
bound follows Sloane's observation in A007918 and its earlier formalization
by @Raimo33, using the reduction by @mbilenko03. The initial positive
differences come from A061558 and Izykowski's 20-term record. -/

namespace PrimeProgressions

/-- Arbitrarily large steps which survive a sieve by all primes through B. -/
theorem local_sieve (p B T : ℕ) (hp : p.Prime) :
    ∃ t : ℕ, T < t ∧ ∀ k : ℕ, 0 < k → k < p →
      B < p+k*(primorial (p-1)*t) ∧
      ∀ q : ℕ, q.Prime → q ≤ B → ¬ q ∣ p+k*(primorial (p-1)*t) := by
  let F := B.primesLE.erase p
  let M := ∏ q ∈ F, q
  have primes (q : ℕ) (hq : q ∈ F) : q.Prime :=
    (Nat.mem_primesLE.mp (Finset.mem_erase.mp hq).2).2
  have Mpos : 0 < M := Finset.prod_pos (fun q hq => (primes q hq).pos)
  have pM : ¬p ∣ M := by
    intro hd
    obtain ⟨q,hq,dvd⟩ := (hp.prime.dvd_finsetProd_iff (fun q : ℕ => q)).mp hd
    exact (Finset.mem_erase.mp hq).1 (((primes q hq).dvd_iff_eq hp.ne_one).mp dvd)
  let z := T+B+1
  let t := M*(1+p*z)
  have pz : ¬p ∣ 1+p*z := fun h => hp.not_dvd_one ((Nat.dvd_add_iff_left (dvd_mul_right p z)).mpr h)
  have pt : ¬p ∣ t := fun h => (hp.dvd_mul.mp h).elim pM pz
  have pW : ¬p ∣ primorial (p-1) := by
    rw [hp.dvd_primorial_iff]
    have := hp.pos
    omega
  have zle : z ≤ t := (Nat.le_mul_of_pos_left z hp.pos).trans
    ((Nat.le_add_left (p*z) 1).trans (Nat.le_mul_of_pos_left _ Mpos))
  refine ⟨t,by dsimp [z] at zle; omega,?_⟩
  intro k hk hkp
  constructor
  · have Wt := Nat.le_mul_of_pos_left t (primorial_pos (p-1))
    have kt := Nat.le_mul_of_pos_left (primorial (p-1)*t) hk
    dsimp [z] at zle
    omega
  intro q hq hqB bad
  by_cases eqp : q = p
  · subst q
    have hprod := (Nat.dvd_add_iff_right (dvd_refl p)).mpr bad
    have kfree : ¬p ∣ k := fun h => (Nat.not_le.mpr hkp) (Nat.le_of_dvd hk h)
    exact (hp.dvd_mul.mp hprod).elim kfree (fun h => (hp.dvd_mul.mp h).elim pW pt)
  · have mem : q ∈ F := Finset.mem_erase.mpr ⟨eqp,Nat.mem_primesLE.mpr ⟨hqB,hq⟩⟩
    have hdM : q ∣ M := Finset.dvd_prod_of_mem (fun i : ℕ => i) mem
    have hdt : q ∣ t := dvd_mul_of_dvd_left hdM _
    have hprod := dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hdt (primorial (p-1))) k
    exact eqp ((hp.dvd_iff_eq hq.ne_one).mp ((Nat.dvd_add_iff_left hprod).mpr bad)).symm

/-- Every prime progression of length p beginning at p has all primes below p
in its step, while p itself cannot divide the step. -/
theorem necessary_step (p d : ℕ) (hp : p.Prime) (hd : 0 < d)
    (terms : ∀ k : ℕ, k < p → (p+k*d).Prime) :
    primorial (p-1) ∣ d ∧ ¬p ∣ d := by
  have small {q : ℕ} (hq : q.Prime) (hqp : q < p) : q ∣ d := by
    by_contra bad
    let : Fact (q.Prime) := ⟨hq⟩
    have nonzero : (d : ZMod q) ≠ 0 := fun h => bad ((ZMod.natCast_eq_zero_iff d q).mp h)
    let r : ZMod q := -(p : ZMod q)/d
    let k := r.val
    have hk : k < p := r.val_lt.trans hqp
    have congruence : q ∣ p+k*d := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      push_cast
      rw [show (k : ZMod q) = r from ZMod.natCast_zmod_val r]
      dsimp [r]
      field_simp
      ring
    have eq := ((terms k hk).dvd_iff_eq hq.ne_one).mp congruence
    omega
  constructor
  · rw [primorial_eq_prod_primesLE]
    apply Finset.prod_dvd_of_isRelPrime
    · intro a ha b hb ne
      have hA := (Nat.mem_primesLE.mp ha).2
      have hB := (Nat.mem_primesLE.mp hb).2
      apply Nat.coprime_iff_isRelPrime.mp
      exact hA.coprime_iff_not_dvd.mpr (fun h => ne ((hB.dvd_iff_eq hA.ne_one).mp h).symm)
    · intro q hm
      obtain ⟨hle,hq⟩ := Nat.mem_primesLE.mp hm
      exact small hq (by have := hp.pos; omega)
  · intro bad
    have h := terms 1 hp.one_lt
    rw [one_mul] at h
    have eq := (h.dvd_iff_eq hp.ne_one).mp (dvd_add (dvd_refl p) bad)
    omega

end PrimeProgressions

namespace OMA.R_OeisA7918_conjecture1_R2

open OeisA7918

/-- The recorded progressions through length 20 start at the least possible prime. -/
def H1 : Prop := ∀ n : ℕ, 0 < n → n ≤ 20 → ∃ d, isApOfNPrimes n (a n) d

/-- At some finite sieve depth, the last candidate in the least admissible
progression is below the square of the first possible unsieved factor. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → 19 < p → ∃ B : ℕ,
    let W := primorial (p-1)
    let t := sInf {t : ℕ | 0 < t ∧ ∀ k, 0 < k → k < p →
      ∀ q : ℕ, q.Prime → q ≤ B → ¬q ∣ p+k*(W*t)}
    p+(p-1)*(W*t) < (B+1)^2

theorem main : H1 → H2 → type_of% @OeisA7918.conjecture1 := by
  intro small large n hn
  obtain ⟨p, np, hp⟩ := Nat.exists_infinite_primes n
  have hnset : {r : ℕ | r.Prime ∧ n ≤ r}.Nonempty := ⟨p,hp,np⟩
  have least : (a n).Prime ∧ n ≤ a n := Nat.sInf_mem hnset
  have prime_cases (p : ℕ) (hp : p.Prime) (large_p : 19 < p) : ∃ d, isApOfNPrimes p p d := by
    obtain ⟨B, limit⟩ := large p hp large_p
    let W := primorial (p-1)
    let S := {t : ℕ | 0 < t ∧ ∀ k, 0 < k → k < p →
      ∀ q : ℕ, q.Prime → q ≤ B → ¬q ∣ p+k*(W*t)}
    have nonempty : S.Nonempty := by
      obtain ⟨t, ht, ok⟩ := PrimeProgressions.local_sieve p B 0 hp
      exact ⟨t, ht, fun k hk hkp => (ok k hk hkp).2⟩
    let t := sInf S
    have good := Nat.sInf_mem nonempty
    change 0 < t ∧ ∀ k, 0 < k → k < p →
      ∀ q : ℕ, q.Prime → q ≤ B → ¬q ∣ p+k*(W*t) at good
    change p+(p-1)*(W*t) < (B+1)^2 at limit
    refine ⟨W*t, Nat.mul_pos (primorial_pos _) good.1, ?_⟩
    intro k hk
    rcases k with _ | k
    · simpa using hp
    let y := p + (k+1)*(W*t)
    change y.Prime
    have yge : p ≤ y := Nat.le_add_right _ _
    have large_y : 2 ≤ y := hp.two_le.trans yge
    by_contra bad
    have low := Nat.minFac_sq_le_self (by omega : 0 < y) bad
    have nofac := good.2 (k+1) (by omega) hk y.minFac (Nat.minFac_prime (by omega))
    have fac : B < y.minFac := lt_of_not_ge (fun hb => nofac hb (Nat.minFac_dvd y))
    have lo := Nat.pow_le_pow_left (show B+1 ≤ y.minFac by omega) 2
    have hi : y ≤ p+(p-1)*(W*t) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
    omega
  have exists_witness : ∃ d, isApOfNPrimes n (a n) d := by
    by_cases h : n ≤ 20
    · exact small n hn h
    obtain ⟨d, hd, all⟩ := prime_cases (a n) least.1 (by omega)
    exact ⟨d, hd, fun k hk => all k (hk.trans_le least.2)⟩
  obtain ⟨d,witness⟩ := exists_witness
  apply le_antisymm
  · refine le_csInf (s := {p0 : ℕ | ∃ step, isApOfNPrimes n p0 step})
      ⟨a n,d,witness⟩ ?_
    rintro p0 ⟨step,hstep,hprimes⟩
    have first : p0.Prime := by simpa using hprimes 0 hn
    apply Nat.sInf_le
    refine ⟨first, ?_⟩
    by_contra! hlt
    have term := hprimes p0 hlt
    rw [show p0+p0*step = p0*(1+step) by ring] at term
    rcases Nat.prime_mul_iff.mp term with ⟨_,one⟩ | ⟨_,one⟩ <;> have := first.two_le <;> omega
  · exact Nat.sInf_le ⟨d,witness⟩

end OMA.R_OeisA7918_conjecture1_R2
