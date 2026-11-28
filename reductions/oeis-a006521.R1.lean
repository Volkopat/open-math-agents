import OMAStatements.S_oeis_a006521
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Novák numbers n satisfy n ∣ 2^n + 1. OEIS A272361 relates repeated prime
factors of the reduced quotient to base-2 Wieferich primes. Here two
applications of lifting the exponent give the exact local valuation.
The first hypothesis excludes the remaining primes from Novák numerators.
The case k = 2 of the second conjecture is witnessed by every power of 3.
-/

namespace OMA.R_oeis_a006521_R1

/-- Remaining Wieferich primes cannot divide a Novák numerator. -/
def H1 : Prop := ∀ p : ℕ, 10000 < p → p.Prime → p ^ 2 ∣ 2 ^ (p - 1) - 1 →
  ∀ n : ℕ, 0 < n → n ∣ 2 ^ n + 1 → ¬ p ∣ 2 ^ n + 1

/-- The generalized congruence at bases above two. -/
def H2 : Prop := ∀ k : ℕ, 3 ≤ k →
  {m : ℕ | 0 < m ∧ (m : ℤ) ∣ (k : ℤ) ^ m - (1 - k)}.Infinite

lemma two_not_dvd_numerator (n : ℕ) (hn : 0 < n) : ¬ 2 ∣ 2 ^ n + 1 := by
  have : 2 ∣ 2 ^ n := dvd_pow_self _ hn.ne'
  omega

lemma odd_novak (n : ℕ) (hn : 0 < n) (hdiv : n ∣ 2 ^ n + 1) : Odd n := by
  exact Nat.not_even_iff_odd.mp fun he =>
    two_not_dvd_numerator n hn ((even_iff_two_dvd.mp he).trans hdiv)

/-- At a prime of the numerator, cancelling n removes exactly its p-adic contribution. -/
theorem quotient_valuation {p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hdiv : n ∣ 2 ^ n + 1) (hpn : p ∣ 2 ^ n + 1) :
    padicValNat p ((2 ^ n + 1) / n) = padicValNat p (2 ^ (p - 1) - 1) := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := fun h => two_not_dvd_numerator n hn (h ▸ hpn)
  have hpodd := hp.odd_of_ne_two hp2
  have hnd : ¬ p ∣ 2 := by
    intro h
    have hle := Nat.le_of_dvd (by decide : 0 < 2) h
    exact hp2 (Nat.le_antisymm hle hp.two_le)
  obtain ⟨r, hr⟩ := hpodd
  have hpge := hp.two_le
  have hrpos : 0 < r := by omega
  have hpred : p - 1 = 2 * r := by omega
  have hrval : padicValNat p r = 0 := padicValNat.eq_zero_of_not_dvd fun h => by
    have := Nat.le_of_dvd hrpos h
    omega
  let b : ℕ := 2 ^ n
  have hb : 1 < b := Nat.one_lt_pow hn.ne' (by decide)
  have hnb : ¬ p ∣ b := fun h => hnd (hp.dvd_of_dvd_pow h)
  have hdminus : ¬ p ∣ b - 1 := by
    intro h
    have hsub := Nat.dvd_sub hpn h
    change p ∣ (b + 1) - (b - 1) at hsub
    apply hnd
    simpa [show b + 1 - (b - 1) = 2 by omega] using hsub
  have fac : b ^ 2 - 1 = (b + 1) * (b - 1) := by
    simpa using Nat.pow_two_sub_pow_two b 1
  have hq : p ∣ b ^ 2 - 1 := fac ▸ dvd_mul_of_dvd_left hpn _
  have hbsq : 1 < b ^ 2 := Nat.one_lt_pow (by decide) hb
  have left := padicValNat.pow_sub_pow (p := p) (x := b ^ 2) (y := 1)
    (hp.odd_of_ne_two hp2) hbsq hq (fun h => hnb (hp.dvd_of_dvd_pow h)) hrpos.ne'
  simp only [one_pow] at left
  rw [fac, padicValNat.mul (by omega) (by omega), padicValNat.eq_zero_of_not_dvd hdminus,
    hrval, add_zero, add_zero] at left
  have hflt := Nat.ModEq.pow_totient (hp.coprime_iff_not_dvd.mpr hnd).symm
  rw [Nat.totient_prime hp] at hflt
  have hlarge : 1 < 2 ^ (p - 1) := Nat.one_lt_pow (by omega) (by decide)
  have hbase := (Nat.modEq_iff_dvd' hlarge.le).mp hflt.symm
  have right := padicValNat.pow_sub_pow (p := p) (x := 2 ^ (p - 1)) (y := 1)
    (hp.odd_of_ne_two hp2) hlarge hbase (fun h => hnd (hp.dvd_of_dvd_pow h)) hn.ne'
  simp only [one_pow] at right
  have heq : (b ^ 2) ^ r = (2 ^ (p - 1)) ^ n := by
    dsimp [b]
    simp only [← pow_mul, hpred]
    congr 1
    ring
  rw [heq] at left
  rw [padicValNat.div_of_dvd hdiv]
  change padicValNat p (b + 1) - padicValNat p n = _
  rw [← left, right, Nat.add_sub_cancel]

/-- The quotient is squarefree exactly when none of the primes of 2^n+1 is Wieferich. -/
theorem squarefree_criterion {n : ℕ} (hn : 0 < n) (hd : n ∣ 2 ^ n + 1) :
    Squarefree ((2 ^ n + 1) / n) ↔
      ∀ p : ℕ, p.Prime → p ∣ 2 ^ n + 1 → ¬ p ^ 2 ∣ 2 ^ (p - 1) - 1 := by
  have hq : 0 < (2 ^ n + 1) / n := Nat.div_pos (Nat.le_of_dvd (by positivity) hd) hn
  have same (p : ℕ) (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1) :
      p ^ 2 ∣ (2 ^ n + 1) / n ↔ p ^ 2 ∣ 2 ^ (p - 1) - 1 := by
    let : Fact p.Prime := ⟨hp⟩
    have hpgt := hp.one_lt
    have hpos : 1 < 2 ^ (p - 1) := Nat.one_lt_pow (by omega) (by decide)
    rw [padicValNat_dvd_iff_le hq.ne', padicValNat_dvd_iff_le (Nat.sub_ne_zero_of_lt hpos),
      quotient_valuation hp hn hd hpn]
  constructor
  · intro hs p hp hpn hw
    exact Nat.squarefree_iff_prime_squarefree.mp hs p hp (by simpa [pow_two] using (same p hp hpn).2 hw)
  · intro h
    apply Nat.squarefree_iff_prime_squarefree.mpr
    intro p hp hsq
    have hpn : p ∣ 2 ^ n + 1 := ((dvd_mul_right p p).trans hsq).trans (Nat.div_dvd_of_dvd hd)
    exact h p hp hpn ((same p hp hpn).1 (by simpa [pow_two] using hsq))

lemma numerator_mod {p n : ℕ} (h : p ∣ 2 ^ n + 1) : (2 : ZMod p) ^ n = -1 := by
  have h0 := (ZMod.natCast_eq_zero_iff _ _).2 h
  push_cast at h0
  exact eq_neg_of_add_eq_zero_left h0

lemma excludes_1093 {n : ℕ} (hn : Odd n) : ¬ 1093 ∣ 2 ^ n + 1 := by
  intro h
  have hx := numerator_mod h
  have cert : (2 : ZMod 1093) ^ 182 = -1 := by
    have c : (2 : ℤ) ^ 182 ≡ -1 [ZMOD (1093 : ℕ)] := by decide +kernel
    simpa only [Int.cast_pow, Int.cast_ofNat, Int.cast_neg, Int.cast_one] using
      (ZMod.intCast_eq_intCast_iff _ _ _).2 c
  have bad : (1 : ZMod 1093) = -1 := calc
    1 = ((2 : ZMod 1093) ^ n) ^ 182 := by rw [hx, (by decide : Even 182).neg_one_pow]
    _ = ((2 : ZMod 1093) ^ 182) ^ n := by rw [← pow_mul, Nat.mul_comm, pow_mul]
    _ = -1 := by rw [cert, hn.neg_one_pow]
  exact (by decide : (1 : ZMod 1093) ≠ -1) bad

lemma excludes_3511 (n : ℕ) : ¬ 3511 ∣ 2 ^ n + 1 := by
  intro h
  have hx := numerator_mod h
  have cert : (2 : ZMod 3511) ^ 1755 = 1 := by
    have c : (2 : ℤ) ^ 1755 ≡ 1 [ZMOD (3511 : ℕ)] := by decide +kernel
    simpa only [Int.cast_pow, Int.cast_ofNat, Int.cast_neg, Int.cast_one] using
      (ZMod.intCast_eq_intCast_iff _ _ _).2 c
  have bad : (1 : ZMod 3511) = -1 := calc
    1 = ((2 : ZMod 3511) ^ 1755) ^ n := by rw [cert, one_pow]
    _ = ((2 : ZMod 3511) ^ n) ^ 1755 := by rw [← pow_mul, Nat.mul_comm, pow_mul]
    _ = -1 := by rw [hx, (by decide : Odd 1755).neg_one_pow]
  exact (by decide : (1 : ZMod 3511) ≠ -1) bad

/-- Direct enumeration of the Wieferich condition through 10000. -/
lemma small_wieferich : ∀ p : Fin 10001, p.val.Prime → p.val ^ 2 ∣ 2 ^ (p.val - 1) - 1 →
    p.val = 1093 ∨ p.val = 3511 := by
  have checked : ((List.range 10001).filter fun j => decide (2 ≤ j ∧ (2 ^ (j - 1) - 1) % (j ^ 2) = 0)) =
      [1093, 3511] := by decide +kernel
  intro p hp hw
  have hmem : p.val ∈ (List.range 10001).filter (fun j => decide (2 ≤ j ∧ (2 ^ (j - 1) - 1) % (j ^ 2) = 0)) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr p.isLt, decide_eq_true ⟨hp.two_le, Nat.dvd_iff_mod_eq_zero.mp hw⟩⟩
  rw [checked] at hmem
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hmem

lemma three_pow_novak (t : ℕ) : 3 ^ t ∣ 2 ^ (3 ^ t) + 1 := by
  have h := padicValNat.pow_add_pow (p := 3) (x := 2) (y := 1) (by decide)
    (by decide) (by decide) ((by decide : Odd 3).pow (n := t))
  simp only [one_pow] at h
  rw [padicValNat.prime_pow] at h
  exact (padicValNat_dvd_iff_le (p := 3) (by positivity)).2 (by omega)

lemma base_two_infinite : {m : ℕ | 0 < m ∧ (m : ℤ) ∣ (2 : ℤ) ^ m - (1 - 2)}.Infinite := by
  apply (Set.infinite_range_of_injective (pow_right_strictMono₀ (by decide : 1 < (3 : ℕ))).injective).mono
  rintro _ ⟨t, rfl⟩
  refine ⟨by positivity, ?_⟩
  have h := three_pow_novak t
  norm_num
  exact_mod_cast h

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a006521.main := by
  intro h1 h2
  constructor
  · intro n hn hd
    apply (squarefree_criterion hn hd).2
    intro p hp hpn hw
    by_cases hs : p ≤ 10000
    · rcases small_wieferich ⟨p, by omega⟩ hp hw with rfl | rfl
      · exact excludes_1093 (odd_novak n hn hd) hpn
      · exact excludes_3511 n hpn
    · exact h1 p (by omega) hp hw n hn hd hpn
  · intro k hk
    rcases eq_or_ne k 2 with rfl | hk2
    · exact base_two_infinite
    · exact h2 k (by omega)

end OMA.R_oeis_a006521_R1
