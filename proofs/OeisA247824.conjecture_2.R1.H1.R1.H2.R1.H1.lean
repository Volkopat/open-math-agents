import OMAReductions.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Count
import Mathlib.Tactic

/- Easy leaves in the Lagarias–Miller–Odlyzko decomposition.
The prime-counting formula uses the Legendre/Meissel reduction by @physbuzz,
crediting Daniel Veljjanoski and @rleshner, in
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9315 . -/

open Finset
namespace Astra247824.Leaves
open OMA.R_OeisA247824_conjecture_2_R1_H1_R1

def survivors (ps : List ℕ) (x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter (fun n => ∀ p ∈ ps, ¬ p ∣ n)

def signedSieve (ps : List ℕ) (x : ℕ) : ℤ := (survivors ps x).card

def descendingPrimes (y : ℕ) : List ℕ :=
  ((List.range (y+1)).filter (fun p => decide p.Prime)).reverse

theorem mem_descending {p y : ℕ} : p ∈ descendingPrimes y ↔ p ∈ Nat.primesLE y := by
  simp [descendingPrimes, Nat.mem_primesLE]

open ArithmeticFunction

def remainingBound (y d : ℕ) := if d = 1 then y else d.minFac-1

def denominators (y : ℕ) := (Icc 1 y).filter Squarefree

abbrev Edge := Sigma (fun _ : ℕ => ℕ)

def edges (y : ℕ) : Finset Edge :=
  (denominators y).sigma (fun d => Nat.primesLE (remainingBound y d))

def special (y : ℕ) := (edges y).filter (fun e => ¬e.1*e.2 ≤ y)

def edgeValue (x : ℕ) (e : Edge) : ℤ :=
  -moebius e.1 * signedSieve (descendingPrimes (e.2-1)) (x/(e.1*e.2))

private theorem edge_facts {d p y : ℕ} (hm : (⟨d,p⟩ : Edge) ∈ edges y) :
    0 < d ∧ Squarefree d ∧ p.Prime ∧ p ≤ y ∧ (d = 1 ∨ p < d.minFac) := by
  obtain ⟨hd, hp⟩ := Finset.mem_sigma.mp hm
  obtain ⟨hd, hs⟩ := Finset.mem_filter.mp hd
  obtain ⟨pos, bound⟩ := Finset.mem_Icc.mp hd
  obtain ⟨pp, prime⟩ := Nat.mem_primesLE.mp hp
  change 1 ≤ d at pos
  change d ≤ y at bound
  change p ≤ remainingBound y d at pp
  by_cases one : d = 1
  · simp only [remainingBound, if_pos one] at pp
    exact ⟨pos, hs, prime, pp, Or.inl one⟩
  · simp only [remainingBound, if_neg one] at pp
    have := Nat.minFac_le pos
    have := Nat.minFac_pos d
    exact ⟨pos, hs, prime, by omega, Or.inr (by omega)⟩

def easyFlat (x y : ℕ) : ℤ :=
  ∑ e ∈ (special y).filter (fun e => x/(e.1*e.2) < e.2^2), edgeValue x e

/- At a cube-root cutoff each easy leaf has a prime denominator `d`. The
remaining endpoint is at least `p`. Its Möbius weight is consequently positive. -/
theorem easy_facts {x y : ℕ} {e : Edge} (hx : y^3 ≤ x) (he : e ∈ special y)
    (small : x/(e.1*e.2) < e.2^2) :
    e.1.Prime ∧ e.2 ≤ x/(e.1*e.2) := by
  rcases e with ⟨d,p⟩
  obtain ⟨edge, cross⟩ := Finset.mem_filter.mp he
  obtain ⟨pos, _, prime, py, before⟩ := edge_facts edge
  have dy : d ≤ y := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_sigma.mp edge).1).1).2
  have dp : 0 < d*p := Nat.mul_pos pos prime.pos
  change ¬d*p ≤ y at cross
  change x/(d*p) < p^2 at small
  have dd : d ≠ 1 := by intro h; subst d; simp_all
  have bound {u : ℕ} (hu : u ≤ y) : u ≤ x/(d*p) := by
    apply (Nat.le_div_iff_mul_le dp).mpr
    calc u*(d*p) ≤ y*(y*y) := Nat.mul_le_mul hu (Nat.mul_le_mul dy py)
         _ = y^3 := by ring
         _ ≤ x := hx
  refine ⟨?_, bound py⟩
  by_contra bad
  have min := Nat.minFac_sq_le_self pos bad
  have pp : p^2 ≤ d := (Nat.pow_le_pow_left ((before.resolve_left dd).le) 2).trans min
  exact small.not_ge (bound (pp.trans dy))

/- Below the square of the first unsieved prime, the survivors consist of one
and the primes strictly above the sieving bound. -/
theorem signedSieve_below_square {p t : ℕ} (hp : p.Prime) (lower : p ≤ t) (upper : t < p^2) :
    signedSieve (descendingPrimes (p-1)) t =
      1 + (Nat.primeCounting t : ℤ) - (Nat.primeCounting (p-1) : ℤ) := by
  have suc : p-1+1 = p := Nat.sub_add_cancel hp.pos
  have cube : t < (p-1+1)^3 := by
    rw [suc]
    exact upper.trans_le (Nat.pow_le_pow_right hp.pos (by decide : 2≤3))
  have card := meissel (x:=t) (y:=p-1) (z:=p-1) (hp.pos.trans_le lower)
    ((Nat.sub_le p 1).trans lower) cube (by simpa only [suc] using upper)
  have none : (Nat.primesLE (p-1)).filter (p-1 < ·) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q h
    exact (Finset.mem_filter.mp h).2.not_ge (Nat.le_of_mem_primesLE (Finset.mem_filter.mp h).1)
  simp only [none, Finset.sum_empty, add_zero, Nat.primesLE_card_eq_primeCounting] at card
  simp only [signedSieve, survivors, mem_descending]
  omega

/- Each easy leaf can be evaluated using prime ranks, with a positive sign. -/
theorem easyFlat_primeCounting (x y : ℕ) (hx : y^3 ≤ x) : easyFlat x y =
    ((special y).filter (fun e : Edge => x/(e.1*e.2) < e.2^2)).sum (fun e : Edge =>
      1 + (Nat.primeCounting (x/(e.1*e.2)) : ℤ) - (Nat.primeCounting (e.2-1) : ℤ)) := by
  apply Finset.sum_congr rfl
  intro e mem
  obtain ⟨hs, small⟩ := Finset.mem_filter.mp mem
  obtain ⟨prime, lower⟩ := easy_facts hx hs small
  have primeP := (edge_facts (Finset.mem_filter.mp hs).1).2.2.1
  rw [edgeValue, moebius_apply_prime prime, neg_neg, one_mul, signedSieve_below_square primeP lower small]


end Astra247824.Leaves

/- Reindexing and quotient grouping for easy leaves in the LMO partial sieve. -/

namespace Astra247824.Leaves
open Finset

/- For fixed p, the larger prime denominator ranges over a single interval. -/
def easyLower (x p : ℕ) := max p (x/p^3)

def primeFiber (x y p : ℕ) := (Nat.primesLE y).filter (easyLower x p < ·)

def orderedPairs (x y : ℕ) : Finset Edge := (Nat.primesLE y).sigma (primeFiber x y)

def pairArgument (x : ℕ) (e : Edge) := x/(e.1*e.2)

def swapPair (e : Edge) : Edge := ⟨e.2, e.1⟩

private theorem small_iff_cube {x d p : ℕ} (hd : 0 < d) (hp : 0 < p) :
    x/(d*p) < p^2 ↔ x/p^3 < d := by
  rw [Nat.div_lt_iff_lt_mul (Nat.mul_pos hd hp), Nat.div_lt_iff_lt_mul (pow_pos hp 3)]
  ring_nf

private theorem ordered_iff {x y : ℕ} (hx : y^3 ≤ x) (e : Edge) :
    e ∈ (special y).filter (fun u => x/(u.1*u.2) < u.2^2) ↔ swapPair e ∈ orderedPairs x y := by
  rcases e with ⟨d,p⟩
  constructor
  · intro he
    obtain ⟨hs, small⟩ := Finset.mem_filter.mp he
    obtain ⟨dp, _⟩ := easy_facts hx hs small
    change d.Prime at dp
    obtain ⟨edge, _⟩ := Finset.mem_filter.mp hs
    obtain ⟨dm, pm⟩ := Finset.mem_sigma.mp edge
    have dy : d ≤ y := (Finset.mem_Icc.mp (Finset.mem_filter.mp dm).1).2
    obtain ⟨bound, prime⟩ := Nat.mem_primesLE.mp pm
    change p ≤ remainingBound y d at bound
    simp only [remainingBound, if_neg dp.ne_one, dp.minFac_eq] at bound
    have pd : p < d := by have := dp.pos; omega
    refine Finset.mem_sigma.mpr ⟨Nat.mem_primesLE.mpr ⟨pd.le.trans dy, prime⟩, Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨dy,dp⟩, ?_⟩⟩
    exact max_lt pd ((small_iff_cube dp.pos prime.pos).mp small)
  · intro he
    obtain ⟨pm, dm⟩ := Finset.mem_sigma.mp he
    obtain ⟨py, pp⟩ := Nat.mem_primesLE.mp pm
    obtain ⟨dp, gap⟩ := Finset.mem_filter.mp dm
    obtain ⟨dy, prime⟩ := Nat.mem_primesLE.mp dp
    change d.Prime at prime
    change p.Prime at pp
    change p ≤ y at py
    change d ≤ y at dy
    change max p (x/p^3) < d at gap
    obtain ⟨pd, cut⟩ := max_lt_iff.mp gap
    have small := (small_iff_cube prime.pos pp.pos).mpr cut
    have crossing : ¬d*p ≤ y := by
      intro low
      have bound : p^2*(d*p) ≤ x := calc
        p^2*(d*p) ≤ y^2*y := Nat.mul_le_mul (Nat.pow_le_pow_left py 2) low
        _ = y^3 := by ring
        _ ≤ x := hx
      exact small.not_ge ((Nat.le_div_iff_mul_le (Nat.mul_pos prime.pos pp.pos)).mpr bound)
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr ⟨?_, ?_⟩, crossing⟩, small⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨prime.pos, dy⟩, prime.squarefree⟩
    · apply Nat.mem_primesLE.mpr
      refine ⟨?_, pp⟩
      change p ≤ remainingBound y d
      simp only [remainingBound, if_neg prime.ne_one, prime.minFac_eq]
      omega

/- Reindex by the smaller prime first, retaining only the larger primes strictly
above both p and floor(x/p^3). This removes the Möbius and minFac tests. -/
theorem sum_ordered {x y : ℕ} (hx : y^3 ≤ x) (f : Edge → ℤ) :
    ∑ e ∈ (special y).filter (fun u => x/(u.1*u.2) < u.2^2), f (swapPair e) =
      ∑ e ∈ orderedPairs x y, f e := by
  apply Finset.sum_bij (fun e _ => swapPair e) (fun e he => (ordered_iff hx e).mp he)
  · intro e _ g _ eq
    exact congrArg swapPair eq
  · intro e he
    exact ⟨swapPair e, (ordered_iff hx (swapPair e)).mpr he, rfl⟩
  · intros; rfl

def orderedTerm (x : ℕ) (rank : ℕ → ℤ) (e : Edge) : ℤ :=
  rank (pairArgument x e) + (1 - rank (e.1-1))

/- A certified lookup function is required only at the rank arguments actually
used by the prime pairs. -/
theorem easyFlat_ordered (x y : ℕ) (hx : y^3 ≤ x) (rank : ℕ → ℤ)
    (valid : ∀ e ∈ orderedPairs x y,
      rank (pairArgument x e) = Nat.primeCounting (pairArgument x e) ∧
      rank (e.1-1) = Nat.primeCounting (e.1-1)) :
    easyFlat x y = ∑ e ∈ orderedPairs x y, orderedTerm x rank e := by
  rw [easyFlat_primeCounting x y hx, ← sum_ordered hx]
  apply Finset.sum_congr rfl
  intro e he
  obtain ⟨v, u⟩ := valid (swapPair e) ((ordered_iff hx e).mp he)
  unfold orderedTerm
  rw [v,u]
  simp only [pairArgument, swapPair, Nat.mul_comm e.2 e.1]
  ring

theorem primeFiber_card (x y p : ℕ) :
    (primeFiber x y p).card = Nat.primeCounting y - Nat.primeCounting (min y (easyLower x p)) := by
  have eq : primeFiber x y p = (Nat.primesLE y) \ (Nat.primesLE (min y (easyLower x p))) := by
    ext d
    by_cases hp : d.Prime <;> simp [primeFiber, Nat.mem_primesLE, hp]
    omega
  rw [eq, Finset.card_sdiff_of_subset (Nat.primesLE_mono (min_le_left _ _))]
  simp only [Nat.primesLE_card_eq_primeCounting]

def easyOffset (x y : ℕ) (rank : ℕ → ℤ) : ℤ :=
  (Nat.primesLE y).sum (fun p => ((primeFiber x y p).card : ℤ) * (1-rank (p-1)))

def arguments (x y : ℕ) := (orderedPairs x y).image (pairArgument x)

def frequency (x y t : ℕ) := ((orderedPairs x y).filter (fun e => pairArgument x e = t)).card

/- Grouping repeated quotients requires only one rank lookup per distinct argument. -/
theorem easyFlat_grouped (x y : ℕ) (hx : y^3 ≤ x) (rank : ℕ → ℤ)
    (valid : ∀ e ∈ orderedPairs x y,
      rank (pairArgument x e) = Nat.primeCounting (pairArgument x e) ∧
      rank (e.1-1) = Nat.primeCounting (e.1-1)) :
    easyFlat x y = easyOffset x y rank +
      ∑ t ∈ arguments x y, (frequency x y t : ℤ) * rank t := by
  rw [easyFlat_ordered x y hx rank valid]
  unfold orderedTerm
  rw [Finset.sum_add_distrib, add_comm]
  have grouped := Finset.sum_fiberwise_of_maps_to' (s := orderedPairs x y) (t := arguments x y)
    (g := pairArgument x) (fun _ he => Finset.mem_image_of_mem _ he) rank
  simp only [Finset.sum_const, nsmul_eq_mul] at grouped
  have offset : (∑ e ∈ orderedPairs x y, (1-rank (e.1-1))) = easyOffset x y rank := by
    simp only [orderedPairs, Finset.sum_sigma, Finset.sum_const, nsmul_eq_mul, easyOffset]
  rw [offset, ← grouped]
  rfl


/- On an ascending prime list one can skip the entire prefix at the cutoff. -/
theorem ordered_rank_arguments {x y : ℕ} {e : Edge} (he : e ∈ orderedPairs x y) :
    pairArgument x e ≤ Nat.sqrt x ∧ e.1-1 ≤ y := by
  rcases e with ⟨p,d⟩
  obtain ⟨pm, dm⟩ := Finset.mem_sigma.mp he
  obtain ⟨py, pp⟩ := Nat.mem_primesLE.mp pm
  obtain ⟨prime, gap⟩ := Finset.mem_filter.mp dm
  have dpos : 0 < d := (Nat.prime_of_mem_primesLE prime).pos
  change max p (x/p^3) < d at gap
  obtain ⟨pd, cut⟩ := max_lt_iff.mp gap
  have small : x/(p*d) < p^2 := by
    rw [Nat.mul_comm p d]
    exact (small_iff_cube dpos pp.pos).mpr cut
  have bound : x/(p*d) ≤ p*d := small.le.trans (by simpa only [pow_two] using Nat.mul_le_mul_left p pd.le)
  exact ⟨Nat.le_sqrt.mpr ((Nat.mul_le_mul_left _ bound).trans (Nat.div_mul_le_self x (p*d))),
    (Nat.sub_le p 1).trans py⟩

theorem rank_valid_of_table {x y : ℕ} (rank : ℕ → ℤ)
    (table : ∀ n ≤ max y (Nat.sqrt x), rank n = Nat.primeCounting n) (e : Edge)
    (he : e ∈ orderedPairs x y) : rank (pairArgument x e) = Nat.primeCounting (pairArgument x e) ∧
      rank (e.1-1) = Nat.primeCounting (e.1-1) :=
  ⟨table _ ((ordered_rank_arguments he).1.trans (le_max_right ..)),
   table _ ((ordered_rank_arguments he).2.trans (le_max_left ..))⟩

end Astra247824.Leaves

namespace Astra247824
open Finset
def multiplesMask (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => 2^p * multiplesMask p k + 1

theorem multiplesMask_fast {p : ℕ} (hp : 0 < p) (k : ℕ) :
    multiplesMask p k = (2^(p*k)-1)/(2^p-1) := by
  have gt : 1 < (2:ℕ)^p := Nat.one_lt_pow (by omega) (by decide)
  have d : 2^p-1+1 = (2:ℕ)^p := by omega
  have mul (n : ℕ) : multiplesMask p n * (2^p-1) + 1 = (2^p)^n := by
    induction n with
    | zero => simp [multiplesMask]
    | succ n ih =>
      rw [multiplesMask, pow_succ, ← ih]
      calc
        _ = 2^p * multiplesMask p n * (2^p-1) + ((2^p-1)+1) := by ring
        _ = _ := by rw [d]; ring
  have e : multiplesMask p k * (2^p-1) = 2^(p*k)-1 := by
    rw [pow_mul]; have := mul k; omega
  rw [← e, Nat.mul_div_cancel _ (by omega)]

theorem multiplesMask_spec {p : ℕ} (hp : 0 < p) (k i : ℕ) :
    (multiplesMask p k).testBit i = true ↔ ∃ j < k, i = p*j := by
  induction k generalizing i with
  | zero => simp [multiplesMask]
  | succ k ih =>
    have gt : 1 < (2:ℕ)^p := Nat.one_lt_pow (by omega) (by decide)
    rw [multiplesMask, Nat.testBit_two_pow_mul_add _ gt]
    by_cases low : i < p
    · simp only [low, if_true]
      have one : (1:ℕ).testBit i = true ↔ i = 0 := by
        cases i <;> simp [Nat.testBit_succ]
      rw [one]
      constructor
      · rintro rfl; exact ⟨0, by omega, (Nat.mul_zero p).symm⟩
      · rintro ⟨j, _, rfl⟩
        cases j with
        | zero => simp
        | succ j => rw [Nat.mul_succ] at low; omega
    · simp only [low, if_false, ih]
      constructor
      · rintro ⟨j,hj,he⟩
        refine ⟨j+1, by omega, ?_⟩
        rw [Nat.mul_succ]; omega
      · rintro ⟨j,hj,he⟩
        cases j with
        | zero => simp only [Nat.mul_zero] at he; omega
        | succ j =>
          refine ⟨j, by omega, ?_⟩
          rw [Nat.mul_succ] at he; omega

/- The bits of one segment divisible by `p`. The leading segment offset is reduced modulo `p`. -/
def packedDivisors (p lo width : ℕ) : ℕ :=
  ((2^(p*((lo%p+width)/p+1))-1)/(2^p-1)) >>> (lo%p)

theorem packedDivisors_spec {p lo width i : ℕ} (hp : 0 < p) (hi : i < width) :
    (packedDivisors p lo width).testBit i = true ↔ p ∣ lo+i := by
  unfold packedDivisors
  rw [Nat.testBit_shiftRight, ← multiplesMask_fast hp, multiplesMask_spec hp]
  have moved : p ∣ lo%p+i ↔ p ∣ lo+i := by
    have h : p ∣ p*(lo/p) := ⟨_,rfl⟩
    calc
      p ∣ lo%p+i ↔ p ∣ p*(lo/p)+(lo%p+i) := Nat.dvd_add_iff_right h
      _ ↔ p ∣ lo+i := by rw [← Nat.add_assoc, Nat.div_add_mod]
  rw [← moved]
  constructor
  · rintro ⟨j,_,he⟩; exact ⟨j,he⟩
  · rintro ⟨j,he⟩
    refine ⟨j, Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hp).mpr ?_), he⟩
    rw [Nat.mul_comm, ← he]; omega

/- Clear the bits of all multiples of a prime simultaneously. -/
def clearDivisors (mask p lo width : ℕ) : ℕ :=
  mask ^^^ (mask &&& packedDivisors p lo width)

theorem clearDivisors_spec {mask p lo width i : ℕ} (hp : 0 < p) (hi : i < width) :
    (clearDivisors mask p lo width).testBit i = true ↔ mask.testBit i = true ∧ ¬ p ∣ lo+i := by
  have cutoff := packedDivisors_spec (lo:=lo) hp hi
  unfold clearDivisors
  rw [Nat.testBit_xor, Nat.testBit_and]
  cases hm : mask.testBit i <;> cases hb : (packedDivisors p lo width).testBit i <;> simp_all

/- A block of `width` consecutive integers after all the indicated sieve stages. -/
def blockMask (lo width : ℕ) : List ℕ → ℕ
  | [] => 2^width-1
  | p::ps => clearDivisors (blockMask lo width ps) p lo width

theorem blockMask_spec {ps : List ℕ} {lo width i : ℕ} (hi : i < width)
    (positive : ∀ p ∈ ps, 0 < p) :
    (blockMask lo width ps).testBit i = true ↔ ∀ p ∈ ps, ¬ p ∣ lo+i := by
  induction ps with
  | nil => simp [blockMask, Nat.testBit_two_pow_sub_one, hi]
  | cons p ps ih =>
    rw [blockMask, clearDivisors_spec (positive p (by simp)) hi,
      ih (fun q hq => positive q (List.mem_cons_of_mem p hq))]
    simp only [List.forall_mem_cons, and_comm]

/- In each segment, counting set bits gives the exact number of survivors. -/

end Astra247824

namespace Astra247824.GlobalRank
open Astra247824 Finset

/- Trial divisors required to sieve all queried endpoints. -/
def seedPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem seed_literal : seedPrimes =
    (List.range 3008).filter (fun n => decide (2 ≤ n ∧ n.minFac = n)) := by decide +kernel

theorem mem_seed {p : ℕ} : p ∈ seedPrimes ↔ p < 3008 ∧ p.Prime := by
  rw [seed_literal]
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, Nat.prime_def_minFac]

private def bitsOfList : List ℕ → ℕ
  | [] => 0
  | p :: ps => 2^p ||| bitsOfList ps

private theorem bitsOfList_spec (ps : List ℕ) (i : ℕ) :
    (bitsOfList ps).testBit i = true ↔ i ∈ ps := by
  induction ps with
  | nil => simp [bitsOfList]
  | cons p ps ih =>
    simp only [bitsOfList, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq, ih, List.mem_cons]
    rw [eq_comm (a:=p) (b:=i)]

private def lowWord : ℕ := 0x28000000a08220008008020208200808000220808220008000a20a00200800220200a00828808228820808a00800200220200028008000020a08808020000800000220808008220008208008220a20800208828200000a00220820228000808a00020208800000800020200a20a00028008028a00208020008028020808a20808200000a00028000208200200a28820008000808008020028820000820820200a00200a20000028820000200828228220008808808220800808008008228a00800828808228800200800020208200000000828008a20a08a00008020020a08220020208200808028000020820208228800020a00a00828028220020808208800208220200808800008a20008a20008028a00a00200800220220808820808020200808220028208a00800a20828208020a08200820000a00208808808008a20208828028020220208820808228020800228800200a20a08208028228800800a28028208820a00a08800228a20208828828208a20a08a28ac

private theorem low_eq : lowWord = bitsOfList seedPrimes := by decide +kernel

private theorem low_spec (i : ℕ) : lowWord.testBit i = true ↔ i < 3008 ∧ i.Prime := by
  rw [low_eq,bitsOfList_spec,mem_seed]

private theorem prime_above {n : ℕ} (high : 3008 ≤ n) (lim : n ≤ 9041343) :
    (∀ p ∈ seedPrimes, ¬ p ∣ n) ↔ n.Prime := by
  constructor
  · intro survive
    by_contra notprime
    have hp := Nat.minFac_prime (by omega : n ≠ 1)
    have hs := Nat.minFac_sq_le_self (by omega : 0 < n) notprime
    have lt : n.minFac < 3008 := by
      by_contra! ge
      have big := Nat.pow_le_pow_left ge 2
      omega
    exact survive _ (mem_seed.mpr ⟨lt,hp⟩) (Nat.minFac_dvd n)
  · intro prime p mem divided
    obtain ⟨bound,hp⟩ := mem_seed.mp mem
    obtain h|h := prime.eq_one_or_self_of_dvd p divided
    · exact hp.ne_one h
    · omega

/- Sieve an entire 65,536-bit segment. Chunk zero restores primes in the seed list. -/
def computedChunk (c : ℕ) : ℕ :=
  let mask := blockMask (65536*c) 65536 seedPrimes
  if c=0 then ((mask >>> 3008) <<< 3008) ||| lowWord else mask

theorem computedChunk_spec {c i : ℕ} (hi : i < 65536) (lim : 65536*c+i ≤ 9041343) :
    (computedChunk c).testBit i = true ↔ (65536*c+i).Prime := by
  have positive (p : ℕ) (hp : p ∈ seedPrimes) : 0 < p := (mem_seed.mp hp).2.pos
  by_cases c0 : c=0
  · subst c
    simp only [computedChunk, if_true, Nat.mul_zero, Nat.zero_add, Nat.testBit_or,
      Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, low_spec] at *
    by_cases small : i < 3008
    · simp [small, Nat.not_le.mpr small]
    · have large : 3008 ≤ i := by omega
      have args : 3008+(i-3008)=i := by omega
      rw [args]
      simpa only [large, small, false_and, true_and, or_false] using
        (blockMask_spec (lo:=0) hi positive).trans (by simpa only [Nat.zero_add] using prime_above large lim)
  · simp only [computedChunk, if_neg c0]
    exact (blockMask_spec hi positive).trans (prime_above (by omega) lim)

def allFrom (f : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, first => f first
  | depth+1, first => allFrom f depth first && allFrom f depth (first + 2^depth)

theorem allFrom_at {f : ℕ → Bool} {depth first i : ℕ} (h : allFrom f depth first = true)
    (lo : first ≤ i) (hi : i < first+2^depth) : f i = true := by
  induction depth generalizing first with
  | zero =>
    have eq : i = first := by simp only [pow_zero] at hi; omega
    exact eq ▸ h
  | succ depth ih =>
    obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp h
    rw [pow_succ] at hi
    by_cases boundary : i < first+2^depth
    · exact ih left lo boundary
    · exact ih right (by omega) (by omega)


end Astra247824.GlobalRank

namespace Astra247824.GlobalRank
open Finset

set_option maxRecDepth 16384 in
private abbrev B : ℕ := 2^20

/- Pack n consecutive radix-2^20 digits, starting with the least significant. -/
set_option maxRecDepth 16384 in
def packDigits : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n+1, f => f 0 + B * packDigits n (fun i => f (i+1))

set_option maxRecDepth 16384 in
def lane (w i : ℕ) : ℕ := (w >>> (20*i)) % B

set_option maxRecDepth 16384 in
private theorem extract (n : ℕ) (f : ℕ → ℕ) (small : ∀ i<n, f i<B)
    (i : ℕ) (hi : i<n) : lane (packDigits n f) i = f i := by
  unfold lane
  rw [Nat.shiftRight_eq_div_pow, pow_mul]
  induction n generalizing i f with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [packDigits, Nat.mod_eq_of_lt (small 0 (by omega))]
    | succ i =>
      rw [packDigits, pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by decide),
        Nat.div_eq_of_lt (small 0 (by omega)), Nat.zero_add]
      exact ih (fun k => f (k+1)) (fun k hk => small _ (by omega)) i (by omega)

set_option maxRecDepth 16384 in
private theorem pack_append (m n : ℕ) (f : ℕ → ℕ) :
    packDigits (m+n) f = packDigits m f + B^m * packDigits n (fun i => f (m+i)) := by
  induction m generalizing f with
  | zero => simp [packDigits]
  | succ m ih =>
    rw [Nat.succ_add, packDigits, packDigits, ih, pow_succ]
    simp only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    ring

/- Number of set bits strictly before position n. -/
set_option maxRecDepth 16384 in
def bitPrefix (w n : ℕ) : ℕ := Nat.count (fun i => w.testBit i = true) n

set_option maxRecDepth 16384 in
theorem packDigits_addLength (m n : ℕ) (f : ℕ → ℕ) :
    packDigits (m+n) f = packDigits m f + (2^20)^m * packDigits n (fun i => f (m+i)) :=
  pack_append m n f

set_option maxRecDepth 16384 in
theorem lane_packDigits (n : ℕ) (f : ℕ → ℕ) (small : ∀ i<n, f i<2^20)
    (i : ℕ) (hi : i<n) : lane (packDigits n f) i = f i := extract n f small i hi

set_option maxRecDepth 16384 in
theorem packDigits_congr (n : ℕ) (f g : ℕ → ℕ) (agree : ∀ i<n, f i = g i) :
    packDigits n f = packDigits n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [packDigits, packDigits, agree 0 (by omega),
      ih (fun i => f (i+1)) (fun i => g (i+1)) (fun i hi => agree _ (by omega))]


end Astra247824.GlobalRank

/- Exact packed prefix summation by a radix-2^20 multiplication. -/
namespace Astra247824.GlobalRank
open Finset
private abbrev radix : ℕ := 1048576

def repunit (n : ℕ) := packDigits n (fun _ => 1)

private theorem repunit_first (n : ℕ) : repunit (n+1) = 1 + radix*repunit n := rfl

private theorem repunit_last (n : ℕ) : repunit (n+1) = repunit n + radix^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    calc repunit (n+1+1) = 1+radix*(repunit n+radix^n) := by rw [repunit_first (n+1), ih]
         _ = repunit (n+1)+radix^(n+1) := by rw [repunit_first, pow_succ]; ring

private theorem append_mod (t k m : ℕ) (ht : t < radix) (hm : 0 < m) :
    (t+radix*k) % (radix*m) = t+radix*(k%m) := by
  have decomp := Nat.mod_add_div k m
  have small := Nat.mod_lt k hm
  have lt : t+radix*(k%m) < radix*m := calc
    t+radix*(k%m) < radix+radix*(k%m) := Nat.add_lt_add_right ht _
    _ = radix*(k%m+1) := by ring
    _ ≤ radix*m := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt small)
  calc (t+radix*k) % (radix*m) = ((t+radix*(k%m)) + (radix*m)*(k/m)) % (radix*m) := by
        congr 1
        calc t+radix*k = t+radix*((k%m) + m*(k/m)) := by rw [decomp]
             _ = _ := by ring
       _ = t+radix*(k%m) := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt lt]

private theorem packed_step (v marks n : ℕ) (hv : v<radix) :
    ((v+radix*marks)*repunit (n+1)) % radix^(n+1) =
      v + radix*(((v+marks)*repunit n) % radix^n) := by
  have expr : (v+radix*marks)*repunit (n+1) =
      (v+radix*((v+marks)*repunit n)) + radix^(n+1)*marks := by
    calc (v+radix*marks)*repunit (n+1) =
          v*(1+radix*repunit n) + radix*marks*(repunit n+radix^n) := by
          rw [← repunit_first, ← repunit_last, Nat.add_mul]
         _ = _ := by rw [pow_succ]; ring
  rw [expr, Nat.add_mul_mod_self_left, pow_succ', append_mod _ _ _ hv (by positivity)]

private theorem sum_first (f : ℕ → ℕ) (n : ℕ) :
    ∑ i ∈ range (n+1), f i = f 0 + ∑ i ∈ range n, f (i+1) := by
  rw [sum_range_succ', Nat.add_comm]

/- When every desired rank is less than the radix, one multiplication
produces all prefix ranks. The radix bounds exclude carries between lanes. -/
theorem pack_prefix (base n : ℕ) (f : ℕ → ℕ)
    (small : ∀ i<n, base + ∑ j ∈ range (i+1), f j < radix) :
    packDigits n (fun i => base+∑ j ∈ range (i+1), f j) =
      ((base+packDigits n f)*repunit n) % radix^n := by
  induction n generalizing base f with
  | zero => simp [packDigits, repunit]
  | succ n ih =>
    let v := base+f 0
    let g := fun j => f (j+1)
    have sh (i : ℕ) : v+∑ j ∈ range (i+1), g j = base+∑ j ∈ range ((i+1)+1), f j := by
      rw [sum_first f (i+1)]
      dsimp [v,g]
      omega
    have h := ih v g (fun i hi => (sh i) ▸ small (i+1) (by omega))
    have hv : v<radix := by simpa [v] using small 0 (by omega)
    have spin : (fun i => base+∑ j ∈ range ((i+1)+1), f j) =
        (fun i => v+∑ j ∈ range (i+1), g j) := funext (fun i => (sh i).symm)
    rw [packDigits, packDigits, spin, h]
    simp only [zero_add, sum_range_one]
    change v + radix*_ = ((base+(f 0+radix*packDigits n g))*repunit (n+1)) % radix^(n+1)
    rw [← Nat.add_assoc]
    exact (packed_step v (packDigits n g) n hv).symm

end Astra247824.GlobalRank

/- Build all inclusive prime ranks of a page by a single packed prefix sum. -/
namespace Astra247824.GlobalRank
open Finset

set_option maxRecDepth 16384 in
def pairMark (w i : ℕ) : ℕ :=
  (if w.testBit (2*i) then 1 else 0) + (if w.testBit (2*i+1) then 1 else 0)

set_option maxRecDepth 16384 in
private theorem marks_before (w n : ℕ) :
    ∑ i ∈ range n, pairMark w i = bitPrefix w (2*n) := by
  induction n with
  | zero => simp [bitPrefix]
  | succ n ih =>
    rw [sum_range_succ, ih, Nat.mul_succ]
    simp only [bitPrefix, pairMark, Nat.count_succ]
    omega

set_option maxRecDepth 16384 in
private def markByte (w : ℕ) : ℕ := (0x2000020000200002000020000200002000010000200002000020000100002000020000200000000020000200001000020000200002000010000100002000020000100001000020000200001000000000200002000010000200002000020000100001000020000200001000010000200002000010000000002000020000000002000020000200000000010000200002000000000100002000020000000000000020000100002000020000200001000020000100002000010000200001000020000100002000000000200001000010000200002000010000100001000020000100001000010000200001000010000000002000010000100002000020000100001000010000200001000010000100002000010000100000000020000100000000020000200001000000000100002000010000000001000020000100000000000000200001000020000200002000010000200001000020000100002000010000200001000020000000002000010000100002000020000100001000010000200001000010000100002000010000100000000020000100001000020000200001000010000100002000010000100001000020000100001000000000200001000000000200002000010000000001000020000100000000010000200001000000000000002000000000200002000020000000002000010000200000000020000100002000000000200000000020000000001000020000200000000010000100002000000000100001000020000000001000000000200000000010000200002000000000100001000020000000001000010000200000000010000000002000000000000002000020000000000000010000200000000000000100002000000000000000000010000200002000020000100002000020000100001000020000200001000010000200002000000000100002000010000200001000020000100001000010000200001000010000100002000010000000001000020000100002000010000200001000010000100002000010000100001000020000100000000010000200000000020000100002000000000100001000020000000001000010000200000000000000100001000020000200001000010000200001000010000100002000010000100001000020000000001000010000100002000010000100001000010000100001000010000100001000010000100000000010000100001000020000100001000010000100001000010000100001000010000100001000000000100001000000000200001000010000000001000010000100000000010000100001000000000000001000010000200002000010000100002000010000100001000020000100001000010000200000000010000100001000020000100001000010000100001000010000100001000010000100001000000000100001000010000200001000010000100001000010000100001000010000100001000010000000001000010000000002000010000100000000010000100001000000000100001000010000000000000010000000002000020000100000000020000100001000000000200001000010000000002000000000100000000010000200001000000000100001000010000000001000010000100000000010000000001000000000100002000010000000001000010000100000000010000100001000000000100000000010000000000000020000100000000000000100001000000000000001000010000000000000000000100002000020000200001000020000200001000010000200002000010000100002000020000000001000020000100002000010000200001000010000100002000010000100001000020000100000000010000200001000020000100002000010000100001000020000100001000010000200001000000000100002000000000200001000020000000001000010000200000000010000100002000000000000001000010000200002000010000100002000010000100001000020000100001000010000200000000010000100001000020000100001000010000100001000010000100001000010000100001000000000100001000010000200001000010000100001000010000100001000010000100001000010000000001000010000000002000010000100000000010000100001000000000100001000010000000000000010000100002000020000100001000020000100001000010000200001000010000100002000000000100001000010000200001000010000100001000010000100001000010000100001000010000000001000010000100002000010000100001000010000100001000010000100001000010000100000000010000100000000020000100001000000000100001000010000000001000010000100000000000000100000000020000200001000000000200001000010000000002000010000100000000020000000001000000000100002000010000000001000010000100000000010000100001000000000100000000010000000001000020000100000000010000100001000000000100001000010000000001000000000100000000000000200001000000000000001000010000000000000010000100000000000000000000000020000200002000000000200002000010000000002000020000100000000020000200000000000000200001000020000000002000010000100000000020000100001000000000200001000000000000002000010000200000000020000100001000000000200001000010000000002000010000000000000020000000002000000000200000000010000000002000000000100000000020000000000000000000100002000020000000001000020000100000000010000200001000000000100002000000000000001000010000200000000010000100001000000000100001000010000000001000010000000000000010000100002000000000100001000010000000001000010000100000000010000100000000000000100000000020000000001000000000100000000010000000001000000000100000000000000000001000020000200000000010000200001000000000100002000010000000001000020000000000000010000100002000000000100001000010000000001000010000100000000010000100000000000000100001000020000000001000010000100000000010000100001000000000100001000000000000001000000000200000000010000000001000000000100000000010000000001000000000000000000000000200002000000000000002000010000000000000020000100000000000000200000000000000000001000020000000000000010000100000000000000100001000000000000001000000000000000000010000200000000000000100001000000000000001000010000000000000010000000000000000000000002000000000000000000010000000000000000000100000000000000000000 >>> (80*(w%256))) % (2^80)

set_option maxRecDepth 16384 in
private theorem allByteMarks : ∀ v : Fin 256, markByte v.val = packDigits 4 (pairMark v.val) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem markByte_spec (w : ℕ) : markByte w = packDigits 4 (pairMark w) := by
  have h := allByteMarks ⟨w%256, Nat.mod_lt _ (by decide)⟩
  change markByte (w%256) = packDigits 4 (pairMark (w%256)) at h
  rw [show markByte (w%256) = markByte w by simp [markByte]] at h
  rw [h]
  apply packDigits_congr
  intro i hi
  unfold pairMark
  rw [show 256=2^8 by decide, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  have low : 2*i<8 := by omega
  have high : 2*i+1<8 := by omega
  simp [low,high]

/- Expand each pair of bits into one radix-2^20 digit. -/
set_option maxRecDepth 16384 in
def spreadMarks (w : ℕ) : ℕ → ℕ
  | 0 => markByte w
  | k+1 => let half := 4*2^k
           spreadMarks w k + (spreadMarks (w >>> (2*half)) k <<< (20*half))

set_option maxRecDepth 16384 in
private theorem marks_shift (w h j : ℕ) : pairMark (w >>> (2*h)) j = pairMark w (h+j) := by
  simp only [pairMark, Nat.testBit_shiftRight, Nat.mul_add, Nat.add_assoc]

set_option maxRecDepth 16384 in
theorem spreadMarks_spec (w k : ℕ) :
    spreadMarks w k = packDigits (4*2^k) (pairMark w) := by
  induction k generalizing w with
  | zero => exact markByte_spec w
  | succ k ih =>
    let h := 4*2^k
    have shape : 4*2^(k+1) = h+h := by dsimp [h]; rw [pow_succ]; omega
    rw [spreadMarks, shape, packDigits_addLength, ih, ih]
    change packDigits h (pairMark w) + (packDigits h (pairMark (w >>> (2*h))) <<< (20*h)) = _
    have move : pairMark (w >>> (2*h)) = (fun i => pairMark w (h+i)) :=
      funext (marks_shift w h)
    rw [move, Nat.shiftLeft_eq, pow_mul]
    exact congrArg (packDigits h (pairMark w) + ·) (Nat.mul_comm _ _)

/- Compute a full page of inclusive odd-position ranks. -/
set_option maxRecDepth 16384 in
def makePage (base w k : ℕ) : ℕ :=
  let n := 4*2^k
  let ones := ((1 <<< (20*n))-1)/1048575
  ((base + spreadMarks w k)*ones) % (1 <<< (20*n))

set_option maxRecDepth 16384 in
private theorem repunit_geo (n : ℕ) : repunit n * 1048575 + 1 = 1048576^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h : repunit (n+1) = 1 + 1048576*repunit n := rfl
    rw [h, pow_succ]
    calc (1+1048576*repunit n)*1048575+1 = (repunit n*1048575+1)*1048576 := by ring
         _ = _ := by rw [ih]

set_option maxRecDepth 16384 in
private theorem repunit_div (n : ℕ) : repunit n = ((1 <<< (20*n))-1)/1048575 := by
  have geo := repunit_geo n
  have pow : (1 <<< (20*n) : ℕ) = 1048576^n := by rw [Nat.shiftLeft_eq, Nat.one_mul, pow_mul]; rfl
  rw [pow, show 1048576^n-1=repunit n*1048575 by omega, Nat.mul_div_cancel _ (by decide)]

set_option maxRecDepth 16384 in
theorem makePage_spec (base w k : ℕ) (room : base+2*(4*2^k) < 1048576) :
    makePage base w k = packDigits (4*2^k) (fun i => base+bitPrefix w (2*(i+1))) := by
  let n := 4*2^k
  have small : ∀ i<n, base + ∑ j ∈ range (i+1), pairMark w j < 1048576 := by
    intro i hi
    rw [marks_before]
    have count := Nat.count_le (p := fun j => w.testBit j=true) (n:=2*(i+1))
    change base + Nat.count (fun j => w.testBit j=true) (2*(i+1)) < 1048576
    dsimp [n] at hi
    omega
  have conv := pack_prefix base n (pairMark w) small
  simp only [marks_before] at conv
  rw [conv, makePage, ← repunit_div, spreadMarks_spec, Nat.shiftLeft_eq, Nat.one_mul, pow_mul]
  rfl

end Astra247824.GlobalRank

/- Procedural prime masks with one closed kernel-certified numeral per segment. -/
namespace Astra247824.Compact
open Astra247824 Astra247824.GlobalRank
private def shiftedDiv (p lo width : ℕ) : ℕ :=
  (((1 <<< (p*((lo%p+width)/p+1)))-1)/((1 <<< p)-1)) >>> (lo%p)

private def shiftedMask (lo width : ℕ) : List ℕ → ℕ
  | [] => (1 <<< width)-1
  | p::ps => let mask := shiftedMask lo width ps
             mask ^^^ (mask &&& shiftedDiv p lo width)

private theorem shifted_eq (lo width : ℕ) (ps : List ℕ) :
    shiftedMask lo width ps = blockMask lo width ps := by
  induction ps with
  | nil => simp [shiftedMask, blockMask, Nat.shiftLeft_eq]
  | cons p ps ih => simp only [shiftedMask,blockMask,clearDivisors,ih,shiftedDiv,packedDivisors,
      Nat.shiftLeft_eq, Nat.one_mul]


def normChunk (c : ℕ) : ℕ :=
  let bits := shiftedMask (65536*c) 65536 seedPrimes
  if c=0 then ((bits >>> 3008) <<< 3008) ||| 0x28000000a08220008008020208200808000220808220008000a20a00200800220200a00828808228820808a00800200220200028008000020a08808020000800000220808008220008208008220a20800208828200000a00220820228000808a00020208800000800020200a20a00028008028a00208020008028020808a20808200000a00028000208200200a28820008000808008020028820000820820200a00200a20000028820000200828228220008808808220800808008008228a00800828808228800200800020208200000000828008a20a08a00008020020a08220020208200808028000020820208228800020a00a00828028220020808208800208220200808800008a20008a20008028a00a00200800220220808820808020200808220028208a00800a20828208020a08200820000a00208808808008a20208828028020220208820808228020800228800200a20a08208028228800800a28028208820a00a08800228a20208828828208a20a08a28ac else bits

private theorem normChunk_eq (c : ℕ) : normChunk c = computedChunk c := by
  simp only [normChunk, computedChunk, shifted_eq] <;> rfl

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm0 : {w : ℕ // normChunk 0 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm1 : {w : ℕ // normChunk 1 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm2 : {w : ℕ // normChunk 2 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm3 : {w : ℕ // normChunk 3 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm4 : {w : ℕ // normChunk 4 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm5 : {w : ℕ // normChunk 5 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm6 : {w : ℕ // normChunk 6 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm7 : {w : ℕ // normChunk 7 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm8 : {w : ℕ // normChunk 8 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm9 : {w : ℕ // normChunk 9 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm10 : {w : ℕ // normChunk 10 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm11 : {w : ℕ // normChunk 11 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm12 : {w : ℕ // normChunk 12 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm13 : {w : ℕ // normChunk 13 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm14 : {w : ℕ // normChunk 14 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm15 : {w : ℕ // normChunk 15 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm16 : {w : ℕ // normChunk 16 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm17 : {w : ℕ // normChunk 17 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm18 : {w : ℕ // normChunk 18 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm19 : {w : ℕ // normChunk 19 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm20 : {w : ℕ // normChunk 20 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm21 : {w : ℕ // normChunk 21 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm22 : {w : ℕ // normChunk 22 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm23 : {w : ℕ // normChunk 23 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm24 : {w : ℕ // normChunk 24 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm25 : {w : ℕ // normChunk 25 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm26 : {w : ℕ // normChunk 26 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm27 : {w : ℕ // normChunk 27 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm28 : {w : ℕ // normChunk 28 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm29 : {w : ℕ // normChunk 29 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm30 : {w : ℕ // normChunk 30 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm31 : {w : ℕ // normChunk 31 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm32 : {w : ℕ // normChunk 32 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm33 : {w : ℕ // normChunk 33 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm34 : {w : ℕ // normChunk 34 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm35 : {w : ℕ // normChunk 35 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm36 : {w : ℕ // normChunk 36 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm37 : {w : ℕ // normChunk 37 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm38 : {w : ℕ // normChunk 38 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm39 : {w : ℕ // normChunk 39 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm40 : {w : ℕ // normChunk 40 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm41 : {w : ℕ // normChunk 41 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm42 : {w : ℕ // normChunk 42 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm43 : {w : ℕ // normChunk 43 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm44 : {w : ℕ // normChunk 44 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm45 : {w : ℕ // normChunk 45 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm46 : {w : ℕ // normChunk 46 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm47 : {w : ℕ // normChunk 47 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm48 : {w : ℕ // normChunk 48 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm49 : {w : ℕ // normChunk 49 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm50 : {w : ℕ // normChunk 50 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm51 : {w : ℕ // normChunk 51 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm52 : {w : ℕ // normChunk 52 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm53 : {w : ℕ // normChunk 53 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm54 : {w : ℕ // normChunk 54 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm55 : {w : ℕ // normChunk 55 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm56 : {w : ℕ // normChunk 56 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm57 : {w : ℕ // normChunk 57 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm58 : {w : ℕ // normChunk 58 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm59 : {w : ℕ // normChunk 59 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm60 : {w : ℕ // normChunk 60 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm61 : {w : ℕ // normChunk 61 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm62 : {w : ℕ // normChunk 62 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm63 : {w : ℕ // normChunk 63 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm64 : {w : ℕ // normChunk 64 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm65 : {w : ℕ // normChunk 65 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm66 : {w : ℕ // normChunk 66 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm67 : {w : ℕ // normChunk 67 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm68 : {w : ℕ // normChunk 68 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm69 : {w : ℕ // normChunk 69 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm70 : {w : ℕ // normChunk 70 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm71 : {w : ℕ // normChunk 71 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm72 : {w : ℕ // normChunk 72 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm73 : {w : ℕ // normChunk 73 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm74 : {w : ℕ // normChunk 74 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm75 : {w : ℕ // normChunk 75 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm76 : {w : ℕ // normChunk 76 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm77 : {w : ℕ // normChunk 77 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm78 : {w : ℕ // normChunk 78 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm79 : {w : ℕ // normChunk 79 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm80 : {w : ℕ // normChunk 80 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm81 : {w : ℕ // normChunk 81 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm82 : {w : ℕ // normChunk 82 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm83 : {w : ℕ // normChunk 83 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm84 : {w : ℕ // normChunk 84 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm85 : {w : ℕ // normChunk 85 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm86 : {w : ℕ // normChunk 86 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm87 : {w : ℕ // normChunk 87 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm88 : {w : ℕ // normChunk 88 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm89 : {w : ℕ // normChunk 89 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm90 : {w : ℕ // normChunk 90 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm91 : {w : ℕ // normChunk 91 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm92 : {w : ℕ // normChunk 92 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm93 : {w : ℕ // normChunk 93 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm94 : {w : ℕ // normChunk 94 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm95 : {w : ℕ // normChunk 95 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm96 : {w : ℕ // normChunk 96 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm97 : {w : ℕ // normChunk 97 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm98 : {w : ℕ // normChunk 98 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm99 : {w : ℕ // normChunk 99 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm100 : {w : ℕ // normChunk 100 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm101 : {w : ℕ // normChunk 101 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm102 : {w : ℕ // normChunk 102 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm103 : {w : ℕ // normChunk 103 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm104 : {w : ℕ // normChunk 104 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm105 : {w : ℕ // normChunk 105 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm106 : {w : ℕ // normChunk 106 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm107 : {w : ℕ // normChunk 107 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm108 : {w : ℕ // normChunk 108 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm109 : {w : ℕ // normChunk 109 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm110 : {w : ℕ // normChunk 110 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm111 : {w : ℕ // normChunk 111 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm112 : {w : ℕ // normChunk 112 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm113 : {w : ℕ // normChunk 113 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm114 : {w : ℕ // normChunk 114 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm115 : {w : ℕ // normChunk 115 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm116 : {w : ℕ // normChunk 116 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm117 : {w : ℕ // normChunk 117 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm118 : {w : ℕ // normChunk 118 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm119 : {w : ℕ // normChunk 119 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm120 : {w : ℕ // normChunk 120 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm121 : {w : ℕ // normChunk 121 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm122 : {w : ℕ // normChunk 122 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm123 : {w : ℕ // normChunk 123 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm124 : {w : ℕ // normChunk 124 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm125 : {w : ℕ // normChunk 125 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm126 : {w : ℕ // normChunk 126 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm127 : {w : ℕ // normChunk 127 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm128 : {w : ℕ // normChunk 128 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm129 : {w : ℕ // normChunk 129 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm130 : {w : ℕ // normChunk 130 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm131 : {w : ℕ // normChunk 131 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm132 : {w : ℕ // normChunk 132 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm133 : {w : ℕ // normChunk 133 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm134 : {w : ℕ // normChunk 134 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm135 : {w : ℕ // normChunk 135 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm136 : {w : ℕ // normChunk 136 = w} := ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
private def cm137 : {w : ℕ // normChunk 137 = w} := ⟨_, by conv => lhs; whnf⟩

def primeChunk (a : ℕ) : ℕ :=
  (if a < 69 then (if a < 34 then (if a < 17 then (if a < 8 then (if a < 4 then (if a < 2 then (if a < 1 then cm0.val else cm1.val) else (if a < 3 then cm2.val else cm3.val)) else (if a < 6 then (if a < 5 then cm4.val else cm5.val) else (if a < 7 then cm6.val else cm7.val))) else (if a < 12 then (if a < 10 then (if a < 9 then cm8.val else cm9.val) else (if a < 11 then cm10.val else cm11.val)) else (if a < 14 then (if a < 13 then cm12.val else cm13.val) else (if a < 15 then cm14.val else (if a < 16 then cm15.val else cm16.val))))) else (if a < 25 then (if a < 21 then (if a < 19 then (if a < 18 then cm17.val else cm18.val) else (if a < 20 then cm19.val else cm20.val)) else (if a < 23 then (if a < 22 then cm21.val else cm22.val) else (if a < 24 then cm23.val else cm24.val))) else (if a < 29 then (if a < 27 then (if a < 26 then cm25.val else cm26.val) else (if a < 28 then cm27.val else cm28.val)) else (if a < 31 then (if a < 30 then cm29.val else cm30.val) else (if a < 32 then cm31.val else (if a < 33 then cm32.val else cm33.val)))))) else (if a < 51 then (if a < 42 then (if a < 38 then (if a < 36 then (if a < 35 then cm34.val else cm35.val) else (if a < 37 then cm36.val else cm37.val)) else (if a < 40 then (if a < 39 then cm38.val else cm39.val) else (if a < 41 then cm40.val else cm41.val))) else (if a < 46 then (if a < 44 then (if a < 43 then cm42.val else cm43.val) else (if a < 45 then cm44.val else cm45.val)) else (if a < 48 then (if a < 47 then cm46.val else cm47.val) else (if a < 49 then cm48.val else (if a < 50 then cm49.val else cm50.val))))) else (if a < 60 then (if a < 55 then (if a < 53 then (if a < 52 then cm51.val else cm52.val) else (if a < 54 then cm53.val else cm54.val)) else (if a < 57 then (if a < 56 then cm55.val else cm56.val) else (if a < 58 then cm57.val else (if a < 59 then cm58.val else cm59.val)))) else (if a < 64 then (if a < 62 then (if a < 61 then cm60.val else cm61.val) else (if a < 63 then cm62.val else cm63.val)) else (if a < 66 then (if a < 65 then cm64.val else cm65.val) else (if a < 67 then cm66.val else (if a < 68 then cm67.val else cm68.val))))))) else (if a < 103 then (if a < 86 then (if a < 77 then (if a < 73 then (if a < 71 then (if a < 70 then cm69.val else cm70.val) else (if a < 72 then cm71.val else cm72.val)) else (if a < 75 then (if a < 74 then cm73.val else cm74.val) else (if a < 76 then cm75.val else cm76.val))) else (if a < 81 then (if a < 79 then (if a < 78 then cm77.val else cm78.val) else (if a < 80 then cm79.val else cm80.val)) else (if a < 83 then (if a < 82 then cm81.val else cm82.val) else (if a < 84 then cm83.val else (if a < 85 then cm84.val else cm85.val))))) else (if a < 94 then (if a < 90 then (if a < 88 then (if a < 87 then cm86.val else cm87.val) else (if a < 89 then cm88.val else cm89.val)) else (if a < 92 then (if a < 91 then cm90.val else cm91.val) else (if a < 93 then cm92.val else cm93.val))) else (if a < 98 then (if a < 96 then (if a < 95 then cm94.val else cm95.val) else (if a < 97 then cm96.val else cm97.val)) else (if a < 100 then (if a < 99 then cm98.val else cm99.val) else (if a < 101 then cm100.val else (if a < 102 then cm101.val else cm102.val)))))) else (if a < 120 then (if a < 111 then (if a < 107 then (if a < 105 then (if a < 104 then cm103.val else cm104.val) else (if a < 106 then cm105.val else cm106.val)) else (if a < 109 then (if a < 108 then cm107.val else cm108.val) else (if a < 110 then cm109.val else cm110.val))) else (if a < 115 then (if a < 113 then (if a < 112 then cm111.val else cm112.val) else (if a < 114 then cm113.val else cm114.val)) else (if a < 117 then (if a < 116 then cm115.val else cm116.val) else (if a < 118 then cm117.val else (if a < 119 then cm118.val else cm119.val))))) else (if a < 129 then (if a < 124 then (if a < 122 then (if a < 121 then cm120.val else cm121.val) else (if a < 123 then cm122.val else cm123.val)) else (if a < 126 then (if a < 125 then cm124.val else cm125.val) else (if a < 127 then cm126.val else (if a < 128 then cm127.val else cm128.val)))) else (if a < 133 then (if a < 131 then (if a < 130 then cm129.val else cm130.val) else (if a < 132 then cm131.val else cm132.val)) else (if a < 135 then (if a < 134 then cm133.val else cm134.val) else (if a < 136 then cm135.val else (if a < 137 then cm136.val else cm137.val))))))))

private theorem selected (a : Fin 138) : primeChunk a.val = normChunk a.val := by
  fin_cases a
  · exact cm0.property.symm
  · exact cm1.property.symm
  · exact cm2.property.symm
  · exact cm3.property.symm
  · exact cm4.property.symm
  · exact cm5.property.symm
  · exact cm6.property.symm
  · exact cm7.property.symm
  · exact cm8.property.symm
  · exact cm9.property.symm
  · exact cm10.property.symm
  · exact cm11.property.symm
  · exact cm12.property.symm
  · exact cm13.property.symm
  · exact cm14.property.symm
  · exact cm15.property.symm
  · exact cm16.property.symm
  · exact cm17.property.symm
  · exact cm18.property.symm
  · exact cm19.property.symm
  · exact cm20.property.symm
  · exact cm21.property.symm
  · exact cm22.property.symm
  · exact cm23.property.symm
  · exact cm24.property.symm
  · exact cm25.property.symm
  · exact cm26.property.symm
  · exact cm27.property.symm
  · exact cm28.property.symm
  · exact cm29.property.symm
  · exact cm30.property.symm
  · exact cm31.property.symm
  · exact cm32.property.symm
  · exact cm33.property.symm
  · exact cm34.property.symm
  · exact cm35.property.symm
  · exact cm36.property.symm
  · exact cm37.property.symm
  · exact cm38.property.symm
  · exact cm39.property.symm
  · exact cm40.property.symm
  · exact cm41.property.symm
  · exact cm42.property.symm
  · exact cm43.property.symm
  · exact cm44.property.symm
  · exact cm45.property.symm
  · exact cm46.property.symm
  · exact cm47.property.symm
  · exact cm48.property.symm
  · exact cm49.property.symm
  · exact cm50.property.symm
  · exact cm51.property.symm
  · exact cm52.property.symm
  · exact cm53.property.symm
  · exact cm54.property.symm
  · exact cm55.property.symm
  · exact cm56.property.symm
  · exact cm57.property.symm
  · exact cm58.property.symm
  · exact cm59.property.symm
  · exact cm60.property.symm
  · exact cm61.property.symm
  · exact cm62.property.symm
  · exact cm63.property.symm
  · exact cm64.property.symm
  · exact cm65.property.symm
  · exact cm66.property.symm
  · exact cm67.property.symm
  · exact cm68.property.symm
  · exact cm69.property.symm
  · exact cm70.property.symm
  · exact cm71.property.symm
  · exact cm72.property.symm
  · exact cm73.property.symm
  · exact cm74.property.symm
  · exact cm75.property.symm
  · exact cm76.property.symm
  · exact cm77.property.symm
  · exact cm78.property.symm
  · exact cm79.property.symm
  · exact cm80.property.symm
  · exact cm81.property.symm
  · exact cm82.property.symm
  · exact cm83.property.symm
  · exact cm84.property.symm
  · exact cm85.property.symm
  · exact cm86.property.symm
  · exact cm87.property.symm
  · exact cm88.property.symm
  · exact cm89.property.symm
  · exact cm90.property.symm
  · exact cm91.property.symm
  · exact cm92.property.symm
  · exact cm93.property.symm
  · exact cm94.property.symm
  · exact cm95.property.symm
  · exact cm96.property.symm
  · exact cm97.property.symm
  · exact cm98.property.symm
  · exact cm99.property.symm
  · exact cm100.property.symm
  · exact cm101.property.symm
  · exact cm102.property.symm
  · exact cm103.property.symm
  · exact cm104.property.symm
  · exact cm105.property.symm
  · exact cm106.property.symm
  · exact cm107.property.symm
  · exact cm108.property.symm
  · exact cm109.property.symm
  · exact cm110.property.symm
  · exact cm111.property.symm
  · exact cm112.property.symm
  · exact cm113.property.symm
  · exact cm114.property.symm
  · exact cm115.property.symm
  · exact cm116.property.symm
  · exact cm117.property.symm
  · exact cm118.property.symm
  · exact cm119.property.symm
  · exact cm120.property.symm
  · exact cm121.property.symm
  · exact cm122.property.symm
  · exact cm123.property.symm
  · exact cm124.property.symm
  · exact cm125.property.symm
  · exact cm126.property.symm
  · exact cm127.property.symm
  · exact cm128.property.symm
  · exact cm129.property.symm
  · exact cm130.property.symm
  · exact cm131.property.symm
  · exact cm132.property.symm
  · exact cm133.property.symm
  · exact cm134.property.symm
  · exact cm135.property.symm
  · exact cm136.property.symm
  · exact cm137.property.symm

theorem primeChunk_bit (a i : ℕ) (ha : a<138) (hi : i<65536) (lim : 65536*a+i≤9041343) :
    (primeChunk a).testBit i=true ↔ (65536*a+i).Prime := by
  rw [selected ⟨a,ha⟩, normChunk_eq]
  exact computedChunk_spec hi lim

def pageMask (a : ℕ) := primeChunk (a/4) >>> (16384*(a%4))

theorem pageMask_bit (a i : ℕ) (hi : i<16384) (lim : 16384*a+i≤9041343) :
    (pageMask a).testBit i=true ↔ (16384*a+i).Prime := by
  rw [pageMask, Nat.testBit_shiftRight]
  have loc : 65536*(a/4)+(16384*(a%4)+i) = 16384*a+i := by omega
  rw [primeChunk_bit _ _ (by omega) (by omega) (loc ▸ lim), loc]

end Astra247824.Compact

/- A nine-stage bit distribution builds 512 packed ranks at a time. -/
namespace Astra247824.EasyReplay
open Astra247824.GlobalRank

private def stage (a b w : ℕ) := (w ||| (w <<< a)) &&& b

private def mask256 : {w : ℕ // ((((1 <<< 10240)-1)/((1 <<< 10240)-1)) * ((1 <<< 512)-1) * (1+(1 <<< 5120)) : ℕ) = w} := ⟨_, by conv => lhs; whnf⟩

private def mask128 : {w : ℕ // ((((1 <<< 10240)-1)/((1 <<< 5120)-1)) * ((1 <<< 256)-1) * (1+(1 <<< 2560)) : ℕ) = w} := ⟨_, by conv => lhs; whnf⟩

private def mask64 : {w : ℕ // ((((1 <<< 10240)-1)/((1 <<< 2560)-1)) * ((1 <<< 128)-1) * (1+(1 <<< 1280)) : ℕ) = w} := ⟨_, by conv => lhs; whnf⟩

private def mask32 : {w : ℕ // ((((1 <<< 10240)-1)/((1 <<< 1280)-1)) * ((1 <<< 64)-1) * (1+(1 <<< 640)) : ℕ) = w} := ⟨_, by conv => lhs; whnf⟩

private def mask16 : {w : ℕ // ((((1 <<< 10240)-1)/((1 <<< 640)-1)) * ((1 <<< 32)-1) * (1+(1 <<< 320)) : ℕ) = w} := ⟨_, by conv => lhs; whnf⟩

private def mask8 : {w : ℕ // ((((1 <<< 10240)-1)/((1 <<< 320)-1)) * ((1 <<< 16)-1) * (1+(1 <<< 160)) : ℕ) = w} := ⟨_, by conv => lhs; whnf⟩

private def mask4 : {w : ℕ // ((((1 <<< 10240)-1)/((1 <<< 160)-1)) * ((1 <<< 8)-1) * (1+(1 <<< 80)) : ℕ) = w} := ⟨_, by conv => lhs; whnf⟩

private def mask2 : {w : ℕ // ((((1 <<< 10240)-1)/((1 <<< 80)-1)) * ((1 <<< 4)-1) * (1+(1 <<< 40)) : ℕ) = w} := ⟨_, by conv => lhs; whnf⟩

private def mask1 : {w : ℕ // ((((1 <<< 10240)-1)/((1 <<< 40)-1)) * ((1 <<< 2)-1) * (1+(1 <<< 20)) : ℕ) = w} := ⟨_, by conv => lhs; whnf⟩

private def passes : List (ℕ × ℕ) := [(4608, mask256.val), (2304, mask128.val), (1152, mask64.val), (576, mask32.val), (288, mask16.val), (144, mask8.val), (72, mask4.val), (36, mask2.val), (18, mask1.val)]

private def run : List (ℕ × ℕ) → ℕ → ℕ
  | [], w => w
  | (a,b)::xs, w => run xs (stage a b w)

private def distribute (w : ℕ) := run passes ((w % 2^1024) &&& 0x5555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555)

private theorem stage_or (a b x y : ℕ) :
    stage a b (x ||| y) = stage a b x ||| stage a b y := by
  unfold stage
  rw [Nat.shiftLeft_or_distrib, ← Nat.and_or_distrib_right]
  congr 1
  ac_rfl

private theorem run_or (xs : List (ℕ × ℕ)) (x y : ℕ) :
    run xs (x ||| y) = run xs x ||| run xs y := by
  induction xs generalizing x y with
  | nil => rfl
  | cons h xs ih => rcases h with ⟨a,b⟩; rw [run, stage_or, ih]; rfl

private theorem distr_or (x y : ℕ) :
    distribute (x ||| y) = distribute x ||| distribute y := by
  unfold distribute
  rw [Nat.or_mod_two_pow, Nat.and_or_distrib_right, run_or]

private theorem zero_d : distribute 0 = 0 := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem unit_test : ∀ i : Fin 1024, distribute (2^i.val) =
    (if i.val % 2 = 0 then 2^(20*(i.val/2)) else 0) := by decide +kernel

private theorem truncStep (w n : ℕ) : w % 2^(n+1) =
    (w % 2^n) ||| (if w.testBit n then 2^n else 0) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases il : i<n
  · have is : i<n+1 := by omega
    have ine : i≠n := by omega
    split <;> simp [il, is, Ne.symm ine]
  · by_cases eq : i=n
    · subst i; split <;> simp_all
    · have is : ¬i<n+1 := by omega
      split <;> simp [il, is, Ne.symm eq]

private theorem pack_bound (n : ℕ) (f : ℕ → ℕ) (small : ∀ i, f i ≤ 1) :
    packDigits n f < 2^(20*n) := by
  induction n generalizing f with
  | zero => simp [packDigits]
  | succ n ih =>
    have bound := ih (fun i => f (i+1)) (fun i => small (i+1))
    have zerop := small 0
    rw [Nat.mul_succ, pow_add, packDigits]
    simp only [show 2^20=1048576 by decide, Nat.mul_comm _ 1048576] at *
    omega

private def mark (w i : ℕ) : ℕ := if w.testBit (2*i) then 1 else 0

private theorem distrib_prefix (n : ℕ) (hn : n≤512) (w : ℕ) :
    distribute (w % 2^(2*n)) = packDigits n (mark w) := by
  induction n with
  | zero => change distribute (w % 1) = 0; rw [Nat.mod_one, zero_d]
  | succ n ih =>
    have low := ih (by omega)
    have ev := unit_test ⟨2*n,by omega⟩
    have odd := unit_test ⟨2*n+1,by omega⟩
    change distribute (2^(2*n)) = _ at ev
    change distribute (2^(2*n+1)) = _ at odd
    simp [Nat.add_mod] at ev odd
    rw [show 2*(n+1)=2*n+1+1 by omega, truncStep w (2*n+1), distr_or]
    have extra : distribute (if w.testBit (2*n+1) then 2^(2*n+1) else 0) = 0 := by
      by_cases hh : w.testBit (2*n+1) = true
      · rw [if_pos hh, odd]
      · rw [if_neg hh, zero_d]
    rw [extra, Nat.or_zero, truncStep, distr_or, low, packDigits_addLength n 1]
    have small : ∀ i, mark w i ≤ 1 := by intro i; unfold mark; split <;> decide
    by_cases h : w.testBit (2*n) = true
    · rw [if_pos h, ev, Nat.or_two_pow_eq_add_of_lt (pack_bound n (mark w) small)]
      simp [packDigits, mark, h, pow_mul]
    · simp [h, zero_d, packDigits, mark]

private theorem wide_even (w : ℕ) : distribute w = packDigits 512 (mark w) := by
  have h := distrib_prefix 512 (by decide) w
  simpa only [show 2*512=1024 by decide, distribute, Nat.mod_mod] using h

private theorem pack_plus (n : ℕ) (f g : ℕ → ℕ) :
    packDigits n (fun i => f i+g i) = packDigits n f + packDigits n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [packDigits]
    rw [ih (fun i => f (i+1)) (fun i => g (i+1))]
    simp only [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm]

def wideMarks (w : ℕ) := distribute w + distribute (w >>> 1)

theorem wideMarks_spec (w : ℕ) : wideMarks w = packDigits 512 (pairMark w) := by
  rw [wideMarks, wide_even, wide_even, ←pack_plus]
  simp only [mark, Nat.testBit_shiftRight, Nat.add_comm 1]
  rfl

def wideSpread (w : ℕ) : ℕ → ℕ
  | 0 => wideMarks w
  | k+1 => let h := 512*2^k
           wideSpread w k + (wideSpread (w >>> (2*h)) k <<< (20*h))

theorem wideSpread_spec (w k : ℕ) :
    wideSpread w k = packDigits (512*2^k) (pairMark w) := by
  induction k generalizing w with
  | zero => change wideMarks w = packDigits 512 (pairMark w); exact wideMarks_spec w
  | succ k ih =>
    let h := 512*2^k
    have shape : 512*2^(k+1)=h+h := by dsimp [h]; rw [pow_succ]; omega
    rw [wideSpread, shape, packDigits_addLength, ih, ih]
    have move : pairMark (w >>> (2*h)) = (fun i => pairMark w (h+i)) := by
      funext i
      simp only [pairMark, Nat.testBit_shiftRight, Nat.mul_add, Nat.add_assoc]
    change packDigits h (pairMark w) + (packDigits h (pairMark (w >>> (2*h))) <<< (20*h)) = _
    rw [move, Nat.shiftLeft_eq, pow_mul]
    exact congrArg (packDigits h (pairMark w) + ·) (Nat.mul_comm _ _)

def widePage (base w : ℕ) : ℕ :=
  let n := 8192
  let v := base+wideSpread w 4
  (((v <<< (20*n))-v)/1048575) % (1 <<< (20*n))

theorem widePage_eq (base w : ℕ) : widePage base w = makePage base w 11 := by
  unfold widePage makePage
  rw [wideSpread_spec, spreadMarks_spec]
  let t := base+packDigits 8192 (pairMark w)
  let big : ℕ := 1 <<< (20*8192)
  change ((t <<< (20*8192))-t)/1048575 % big = t*((big-1)/1048575) % big
  have dvd : 1048575 ∣ big-1 := by decide +kernel
  have shift : t <<< (20*8192) = t*big := by simp [big, Nat.shiftLeft_eq]
  rw [shift, ←Nat.mul_div_assoc t dvd, Nat.mul_sub, Nat.mul_one]

end Astra247824.EasyReplay

/- Materialize 552 dense inclusive-rank pages from the procedural prime sieve. -/
namespace Astra247824.Compact
open Astra247824.GlobalRank

private def basePiece (a : ℕ) : ℕ :=
  (if a < 9 then (if a < 4 then (if a < 2 then (if a < 1 then 0xa49409fb309acb095e00910608c0b087130823707d37078450734006e3f069130640705efe059d8054bf04f9b04a650452803fe503a970353f02fdb02a5e024df01f490198e013bb00db80076c00000 else 0x13bcc137331327c12ddf12952124b01201311b63116bd1121910d6a108b31040a0ff440faa20f5e20f1290ec5d0e7bb0e2f00de340d9780d4a70cfec0cb1f0c6750c1a10bcd40b7f00b3220ae4e0a97e) else (if a < 3 then 0x1cd681c8ed1c4821c00c1bb781b6eb1b26d1ade81a9461a4da1a04519bbf19738192c518e41189b21852b1809c17c0b17771172f416e62169ee16549160b015bfa1576d152e414e351499b144f014069 else 0x25b8325728252bc24e58249f52457a240f923cad23849233dc22f6a22af7226822221a21d8621934214a92103b20bc520749202fc1fe6a1fa0d1f59d1f1211ecb11e82c1e3c11df3a1dace1d6461d1e4)) else (if a < 6 then (if a < 5 then 0x2e7022e2b72de462d9f22d5a62d13a2ccf02c8942c43f2bfe52bb8a2b7362b2dd2ae912aa1d2a5ca2a17a29d1c298e02947c2903228bc128748282f627ea027a45275ed2719026d1d268b82644625fdb else 0x370b836c6636834363d535f7b35b4535702352cf34e7f34a2a345dc3418e33d5133905334ba3307632c41327fb323a331f4531ace316883123d30de73099630577300fd2fca22f8522f4042efaa2eb4c) else (if a < 7 then 0x3f8bd3f4ac3f05e3ec003e7c73e3933df443db0f3d6ec3d2c23ce7b3ca6d3c6453c20a3bdaf3b9653b5213b0d13ac893a86d3a42c39fe839bb23976a3932238ede38a8d38648381e537d9237939374f5 else (if a < 8 then 0x47fbf47b91477524733846f2246ae7466ad4627245e4b459ea455a94517044d63449324450d440d143c874385a4340b42fda42bb8427744233641ee741ab8416844126840e2c409d54059e4014f3fd02 else 0x5059c501694fd284f9044f4e44f0c14ec8b4e8624e4394e0054dbc84d7b84d3a44cf7c4cb314c6fd4c2c14be764ba2f4b6164b1f14adaf4a99a4a5594a13d49d0f498f2494cc4909948c75488484840b)))) else (if a < 13 then (if a < 11 then (if a < 10 then 0x58a845865b5822357e10579fb575de571ad56d88569765654a5612855cff558ec554bd550a654c7b5483e5441253fe053bc2537975334e52f1d52af5526c05229851e6f51a55516385121550df9509c1 else 0x60e4460a2960614601ee5fdb25f99d5f5905f1895ed6c5e9505e5385e11f5dcfa5d8f25d4ce5d0b95cc9d5c8865c4655c0475bc205b7fa5b3f15afb75aba15a7845a35459f4859b1e59702592d458ea3) else (if a < 12 then 0x6916568d4a6892f6850c6811267ce1678ec674cf670ae66c9866888664536605165c39658256543364fff64bd5647c5643ba63fa363b8b637606332b62ef662ad2626ca622ae61e9c61a746166561252 else 0x713d670fd570bce707ad7039f6ff8c6fb5c6f7456f33e6ef336eb276e73c6e30a6def96daca6d6b66d2a36ce8f6ca856c6536c2536be416ba1e6b61f6b2106adf06a9fa6a5ff6a1ed69ddc699cd6958e)) else (if a < 15 then (if a < 14 then 0x79604791f678df1789e3785ca781b877dae7799f775997718c76d8a7697b7657b7618375d637594f755497513774d10748e7744e4740dc73ccc7389f7348b7308472c7e728617244c7201971c05717f1 else 0x81729812fc80f0880ae0806f4802ea7fee77faec7f6ec7f2eb7eecc7eac67e6ba7e2b37dea57da917d66d7d2777ce837ca597c6577c2507be657ba477b6597b23a7ae327aa207a62e7a21279e0d79a01) else (if a < 16 then 0x897b5893d188fae88bbb887bb883a787f9d87ba5877ad8739b86f9a86b86867748637885f6785b80857568536584f7684b758475e8436683f6483b65837698335782f6182b4f8274c8235081f3e81b34 else (if a < 17 then 0x91822914249102690c299083d9043d900488fc438f8458f42f8f03f8ec2f8e81a8e40b8e0188dc0b8d8078d4148d0058cc088c7e48c3ea8bfe68bbcd8b7c68b3c08afa38abaa8a7bc8a3c689fbf89bc3 else 0x937fb934069302b92c14928249242e9203791c18)))))
def pageBase (a : ℕ) := (basePiece (a/32) >>> (20*(a%32))) % 1048576

def computedPage (a : ℕ) := makePage (pageBase a) (pageMask a) 11

private def rapidPage (a : ℕ) := Astra247824.EasyReplay.widePage (pageBase a) (pageMask a)

private def rapidCertificate (a : ℕ) (q : {w : ℕ // rapidPage a = w}) :
    {w : ℕ // computedPage a = w} :=
  ⟨q.val, (Astra247824.EasyReplay.widePage_eq (pageBase a) (pageMask a)).symm.trans q.property⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp0 := rapidCertificate 0 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp1 := rapidCertificate 1 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp2 := rapidCertificate 2 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp3 := rapidCertificate 3 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp4 := rapidCertificate 4 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp5 := rapidCertificate 5 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp6 := rapidCertificate 6 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp7 := rapidCertificate 7 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp8 := rapidCertificate 8 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp9 := rapidCertificate 9 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp10 := rapidCertificate 10 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp11 := rapidCertificate 11 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp12 := rapidCertificate 12 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp13 := rapidCertificate 13 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp14 := rapidCertificate 14 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp15 := rapidCertificate 15 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp16 := rapidCertificate 16 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp17 := rapidCertificate 17 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp18 := rapidCertificate 18 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp19 := rapidCertificate 19 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp20 := rapidCertificate 20 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp21 := rapidCertificate 21 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp22 := rapidCertificate 22 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp23 := rapidCertificate 23 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp24 := rapidCertificate 24 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp25 := rapidCertificate 25 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp26 := rapidCertificate 26 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp27 := rapidCertificate 27 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp28 := rapidCertificate 28 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp29 := rapidCertificate 29 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp30 := rapidCertificate 30 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp31 := rapidCertificate 31 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp32 := rapidCertificate 32 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp33 := rapidCertificate 33 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp34 := rapidCertificate 34 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp35 := rapidCertificate 35 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp36 := rapidCertificate 36 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp37 := rapidCertificate 37 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp38 := rapidCertificate 38 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp39 := rapidCertificate 39 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp40 := rapidCertificate 40 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp41 := rapidCertificate 41 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp42 := rapidCertificate 42 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp43 := rapidCertificate 43 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp44 := rapidCertificate 44 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp45 := rapidCertificate 45 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp46 := rapidCertificate 46 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp47 := rapidCertificate 47 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp48 := rapidCertificate 48 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp49 := rapidCertificate 49 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp50 := rapidCertificate 50 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp51 := rapidCertificate 51 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp52 := rapidCertificate 52 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp53 := rapidCertificate 53 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp54 := rapidCertificate 54 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp55 := rapidCertificate 55 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp56 := rapidCertificate 56 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp57 := rapidCertificate 57 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp58 := rapidCertificate 58 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp59 := rapidCertificate 59 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp60 := rapidCertificate 60 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp61 := rapidCertificate 61 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp62 := rapidCertificate 62 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp63 := rapidCertificate 63 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp64 := rapidCertificate 64 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp65 := rapidCertificate 65 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp66 := rapidCertificate 66 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp67 := rapidCertificate 67 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp68 := rapidCertificate 68 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp69 := rapidCertificate 69 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp70 := rapidCertificate 70 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp71 := rapidCertificate 71 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp72 := rapidCertificate 72 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp73 := rapidCertificate 73 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp74 := rapidCertificate 74 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp75 := rapidCertificate 75 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp76 := rapidCertificate 76 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp77 := rapidCertificate 77 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp78 := rapidCertificate 78 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp79 := rapidCertificate 79 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp80 := rapidCertificate 80 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp81 := rapidCertificate 81 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp82 := rapidCertificate 82 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp83 := rapidCertificate 83 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp84 := rapidCertificate 84 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp85 := rapidCertificate 85 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp86 := rapidCertificate 86 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp87 := rapidCertificate 87 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp88 := rapidCertificate 88 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp89 := rapidCertificate 89 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp90 := rapidCertificate 90 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp91 := rapidCertificate 91 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp92 := rapidCertificate 92 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp93 := rapidCertificate 93 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp94 := rapidCertificate 94 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp95 := rapidCertificate 95 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp96 := rapidCertificate 96 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp97 := rapidCertificate 97 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp98 := rapidCertificate 98 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp99 := rapidCertificate 99 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp100 := rapidCertificate 100 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp101 := rapidCertificate 101 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp102 := rapidCertificate 102 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp103 := rapidCertificate 103 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp104 := rapidCertificate 104 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp105 := rapidCertificate 105 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp106 := rapidCertificate 106 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp107 := rapidCertificate 107 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp108 := rapidCertificate 108 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp109 := rapidCertificate 109 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp110 := rapidCertificate 110 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp111 := rapidCertificate 111 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp112 := rapidCertificate 112 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp113 := rapidCertificate 113 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp114 := rapidCertificate 114 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp115 := rapidCertificate 115 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp116 := rapidCertificate 116 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp117 := rapidCertificate 117 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp118 := rapidCertificate 118 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp119 := rapidCertificate 119 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp120 := rapidCertificate 120 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp121 := rapidCertificate 121 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp122 := rapidCertificate 122 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp123 := rapidCertificate 123 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp124 := rapidCertificate 124 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp125 := rapidCertificate 125 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp126 := rapidCertificate 126 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp127 := rapidCertificate 127 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp128 := rapidCertificate 128 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp129 := rapidCertificate 129 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp130 := rapidCertificate 130 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp131 := rapidCertificate 131 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp132 := rapidCertificate 132 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp133 := rapidCertificate 133 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp134 := rapidCertificate 134 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp135 := rapidCertificate 135 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp136 := rapidCertificate 136 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp137 := rapidCertificate 137 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp138 := rapidCertificate 138 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp139 := rapidCertificate 139 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp140 := rapidCertificate 140 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp141 := rapidCertificate 141 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp142 := rapidCertificate 142 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp143 := rapidCertificate 143 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp144 := rapidCertificate 144 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp145 := rapidCertificate 145 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp146 := rapidCertificate 146 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp147 := rapidCertificate 147 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp148 := rapidCertificate 148 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp149 := rapidCertificate 149 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp150 := rapidCertificate 150 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp151 := rapidCertificate 151 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp152 := rapidCertificate 152 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp153 := rapidCertificate 153 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp154 := rapidCertificate 154 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp155 := rapidCertificate 155 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp156 := rapidCertificate 156 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp157 := rapidCertificate 157 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp158 := rapidCertificate 158 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp159 := rapidCertificate 159 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp160 := rapidCertificate 160 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp161 := rapidCertificate 161 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp162 := rapidCertificate 162 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp163 := rapidCertificate 163 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp164 := rapidCertificate 164 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp165 := rapidCertificate 165 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp166 := rapidCertificate 166 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp167 := rapidCertificate 167 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp168 := rapidCertificate 168 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp169 := rapidCertificate 169 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp170 := rapidCertificate 170 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp171 := rapidCertificate 171 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp172 := rapidCertificate 172 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp173 := rapidCertificate 173 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp174 := rapidCertificate 174 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp175 := rapidCertificate 175 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp176 := rapidCertificate 176 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp177 := rapidCertificate 177 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp178 := rapidCertificate 178 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp179 := rapidCertificate 179 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp180 := rapidCertificate 180 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp181 := rapidCertificate 181 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp182 := rapidCertificate 182 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp183 := rapidCertificate 183 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp184 := rapidCertificate 184 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp185 := rapidCertificate 185 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp186 := rapidCertificate 186 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp187 := rapidCertificate 187 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp188 := rapidCertificate 188 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp189 := rapidCertificate 189 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp190 := rapidCertificate 190 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp191 := rapidCertificate 191 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp192 := rapidCertificate 192 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp193 := rapidCertificate 193 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp194 := rapidCertificate 194 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp195 := rapidCertificate 195 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp196 := rapidCertificate 196 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp197 := rapidCertificate 197 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp198 := rapidCertificate 198 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp199 := rapidCertificate 199 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp200 := rapidCertificate 200 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp201 := rapidCertificate 201 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp202 := rapidCertificate 202 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp203 := rapidCertificate 203 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp204 := rapidCertificate 204 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp205 := rapidCertificate 205 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp206 := rapidCertificate 206 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp207 := rapidCertificate 207 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp208 := rapidCertificate 208 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp209 := rapidCertificate 209 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp210 := rapidCertificate 210 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp211 := rapidCertificate 211 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp212 := rapidCertificate 212 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp213 := rapidCertificate 213 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp214 := rapidCertificate 214 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp215 := rapidCertificate 215 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp216 := rapidCertificate 216 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp217 := rapidCertificate 217 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp218 := rapidCertificate 218 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp219 := rapidCertificate 219 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp220 := rapidCertificate 220 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp221 := rapidCertificate 221 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp222 := rapidCertificate 222 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp223 := rapidCertificate 223 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp224 := rapidCertificate 224 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp225 := rapidCertificate 225 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp226 := rapidCertificate 226 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp227 := rapidCertificate 227 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp228 := rapidCertificate 228 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp229 := rapidCertificate 229 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp230 := rapidCertificate 230 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp231 := rapidCertificate 231 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp232 := rapidCertificate 232 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp233 := rapidCertificate 233 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp234 := rapidCertificate 234 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp235 := rapidCertificate 235 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp236 := rapidCertificate 236 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp237 := rapidCertificate 237 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp238 := rapidCertificate 238 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp239 := rapidCertificate 239 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp240 := rapidCertificate 240 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp241 := rapidCertificate 241 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp242 := rapidCertificate 242 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp243 := rapidCertificate 243 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp244 := rapidCertificate 244 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp245 := rapidCertificate 245 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp246 := rapidCertificate 246 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp247 := rapidCertificate 247 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp248 := rapidCertificate 248 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp249 := rapidCertificate 249 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp250 := rapidCertificate 250 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp251 := rapidCertificate 251 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp252 := rapidCertificate 252 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp253 := rapidCertificate 253 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp254 := rapidCertificate 254 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp255 := rapidCertificate 255 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp256 := rapidCertificate 256 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp257 := rapidCertificate 257 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp258 := rapidCertificate 258 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp259 := rapidCertificate 259 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp260 := rapidCertificate 260 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp261 := rapidCertificate 261 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp262 := rapidCertificate 262 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp263 := rapidCertificate 263 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp264 := rapidCertificate 264 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp265 := rapidCertificate 265 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp266 := rapidCertificate 266 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp267 := rapidCertificate 267 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp268 := rapidCertificate 268 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp269 := rapidCertificate 269 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp270 := rapidCertificate 270 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp271 := rapidCertificate 271 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp272 := rapidCertificate 272 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp273 := rapidCertificate 273 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp274 := rapidCertificate 274 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp275 := rapidCertificate 275 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp276 := rapidCertificate 276 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp277 := rapidCertificate 277 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp278 := rapidCertificate 278 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp279 := rapidCertificate 279 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp280 := rapidCertificate 280 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp281 := rapidCertificate 281 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp282 := rapidCertificate 282 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp283 := rapidCertificate 283 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp284 := rapidCertificate 284 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp285 := rapidCertificate 285 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp286 := rapidCertificate 286 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp287 := rapidCertificate 287 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp288 := rapidCertificate 288 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp289 := rapidCertificate 289 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp290 := rapidCertificate 290 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp291 := rapidCertificate 291 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp292 := rapidCertificate 292 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp293 := rapidCertificate 293 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp294 := rapidCertificate 294 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp295 := rapidCertificate 295 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp296 := rapidCertificate 296 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp297 := rapidCertificate 297 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp298 := rapidCertificate 298 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp299 := rapidCertificate 299 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp300 := rapidCertificate 300 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp301 := rapidCertificate 301 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp302 := rapidCertificate 302 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp303 := rapidCertificate 303 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp304 := rapidCertificate 304 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp305 := rapidCertificate 305 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp306 := rapidCertificate 306 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp307 := rapidCertificate 307 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp308 := rapidCertificate 308 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp309 := rapidCertificate 309 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp310 := rapidCertificate 310 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp311 := rapidCertificate 311 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp312 := rapidCertificate 312 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp313 := rapidCertificate 313 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp314 := rapidCertificate 314 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp315 := rapidCertificate 315 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp316 := rapidCertificate 316 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp317 := rapidCertificate 317 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp318 := rapidCertificate 318 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp319 := rapidCertificate 319 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp320 := rapidCertificate 320 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp321 := rapidCertificate 321 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp322 := rapidCertificate 322 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp323 := rapidCertificate 323 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp324 := rapidCertificate 324 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp325 := rapidCertificate 325 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp326 := rapidCertificate 326 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp327 := rapidCertificate 327 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp328 := rapidCertificate 328 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp329 := rapidCertificate 329 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp330 := rapidCertificate 330 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp331 := rapidCertificate 331 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp332 := rapidCertificate 332 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp333 := rapidCertificate 333 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp334 := rapidCertificate 334 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp335 := rapidCertificate 335 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp336 := rapidCertificate 336 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp337 := rapidCertificate 337 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp338 := rapidCertificate 338 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp339 := rapidCertificate 339 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp340 := rapidCertificate 340 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp341 := rapidCertificate 341 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp342 := rapidCertificate 342 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp343 := rapidCertificate 343 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp344 := rapidCertificate 344 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp345 := rapidCertificate 345 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp346 := rapidCertificate 346 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp347 := rapidCertificate 347 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp348 := rapidCertificate 348 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp349 := rapidCertificate 349 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp350 := rapidCertificate 350 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp351 := rapidCertificate 351 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp352 := rapidCertificate 352 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp353 := rapidCertificate 353 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp354 := rapidCertificate 354 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp355 := rapidCertificate 355 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp356 := rapidCertificate 356 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp357 := rapidCertificate 357 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp358 := rapidCertificate 358 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp359 := rapidCertificate 359 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp360 := rapidCertificate 360 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp361 := rapidCertificate 361 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp362 := rapidCertificate 362 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp363 := rapidCertificate 363 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp364 := rapidCertificate 364 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp365 := rapidCertificate 365 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp366 := rapidCertificate 366 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp367 := rapidCertificate 367 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp368 := rapidCertificate 368 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp369 := rapidCertificate 369 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp370 := rapidCertificate 370 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp371 := rapidCertificate 371 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp372 := rapidCertificate 372 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp373 := rapidCertificate 373 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp374 := rapidCertificate 374 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp375 := rapidCertificate 375 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp376 := rapidCertificate 376 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp377 := rapidCertificate 377 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp378 := rapidCertificate 378 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp379 := rapidCertificate 379 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp380 := rapidCertificate 380 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp381 := rapidCertificate 381 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp382 := rapidCertificate 382 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp383 := rapidCertificate 383 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp384 := rapidCertificate 384 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp385 := rapidCertificate 385 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp386 := rapidCertificate 386 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp387 := rapidCertificate 387 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp388 := rapidCertificate 388 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp389 := rapidCertificate 389 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp390 := rapidCertificate 390 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp391 := rapidCertificate 391 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp392 := rapidCertificate 392 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp393 := rapidCertificate 393 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp394 := rapidCertificate 394 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp395 := rapidCertificate 395 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp396 := rapidCertificate 396 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp397 := rapidCertificate 397 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp398 := rapidCertificate 398 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp399 := rapidCertificate 399 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp400 := rapidCertificate 400 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp401 := rapidCertificate 401 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp402 := rapidCertificate 402 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp403 := rapidCertificate 403 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp404 := rapidCertificate 404 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp405 := rapidCertificate 405 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp406 := rapidCertificate 406 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp407 := rapidCertificate 407 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp408 := rapidCertificate 408 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp409 := rapidCertificate 409 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp410 := rapidCertificate 410 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp411 := rapidCertificate 411 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp412 := rapidCertificate 412 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp413 := rapidCertificate 413 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp414 := rapidCertificate 414 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp415 := rapidCertificate 415 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp416 := rapidCertificate 416 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp417 := rapidCertificate 417 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp418 := rapidCertificate 418 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp419 := rapidCertificate 419 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp420 := rapidCertificate 420 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp421 := rapidCertificate 421 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp422 := rapidCertificate 422 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp423 := rapidCertificate 423 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp424 := rapidCertificate 424 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp425 := rapidCertificate 425 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp426 := rapidCertificate 426 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp427 := rapidCertificate 427 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp428 := rapidCertificate 428 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp429 := rapidCertificate 429 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp430 := rapidCertificate 430 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp431 := rapidCertificate 431 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp432 := rapidCertificate 432 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp433 := rapidCertificate 433 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp434 := rapidCertificate 434 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp435 := rapidCertificate 435 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp436 := rapidCertificate 436 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp437 := rapidCertificate 437 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp438 := rapidCertificate 438 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp439 := rapidCertificate 439 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp440 := rapidCertificate 440 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp441 := rapidCertificate 441 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp442 := rapidCertificate 442 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp443 := rapidCertificate 443 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp444 := rapidCertificate 444 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp445 := rapidCertificate 445 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp446 := rapidCertificate 446 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp447 := rapidCertificate 447 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp448 := rapidCertificate 448 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp449 := rapidCertificate 449 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp450 := rapidCertificate 450 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp451 := rapidCertificate 451 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp452 := rapidCertificate 452 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp453 := rapidCertificate 453 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp454 := rapidCertificate 454 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp455 := rapidCertificate 455 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp456 := rapidCertificate 456 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp457 := rapidCertificate 457 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp458 := rapidCertificate 458 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp459 := rapidCertificate 459 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp460 := rapidCertificate 460 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp461 := rapidCertificate 461 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp462 := rapidCertificate 462 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp463 := rapidCertificate 463 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp464 := rapidCertificate 464 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp465 := rapidCertificate 465 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp466 := rapidCertificate 466 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp467 := rapidCertificate 467 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp468 := rapidCertificate 468 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp469 := rapidCertificate 469 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp470 := rapidCertificate 470 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp471 := rapidCertificate 471 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp472 := rapidCertificate 472 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp473 := rapidCertificate 473 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp474 := rapidCertificate 474 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp475 := rapidCertificate 475 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp476 := rapidCertificate 476 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp477 := rapidCertificate 477 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp478 := rapidCertificate 478 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp479 := rapidCertificate 479 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp480 := rapidCertificate 480 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp481 := rapidCertificate 481 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp482 := rapidCertificate 482 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp483 := rapidCertificate 483 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp484 := rapidCertificate 484 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp485 := rapidCertificate 485 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp486 := rapidCertificate 486 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp487 := rapidCertificate 487 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp488 := rapidCertificate 488 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp489 := rapidCertificate 489 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp490 := rapidCertificate 490 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp491 := rapidCertificate 491 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp492 := rapidCertificate 492 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp493 := rapidCertificate 493 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp494 := rapidCertificate 494 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp495 := rapidCertificate 495 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp496 := rapidCertificate 496 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp497 := rapidCertificate 497 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp498 := rapidCertificate 498 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp499 := rapidCertificate 499 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp500 := rapidCertificate 500 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp501 := rapidCertificate 501 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp502 := rapidCertificate 502 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp503 := rapidCertificate 503 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp504 := rapidCertificate 504 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp505 := rapidCertificate 505 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp506 := rapidCertificate 506 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp507 := rapidCertificate 507 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp508 := rapidCertificate 508 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp509 := rapidCertificate 509 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp510 := rapidCertificate 510 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp511 := rapidCertificate 511 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp512 := rapidCertificate 512 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp513 := rapidCertificate 513 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp514 := rapidCertificate 514 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp515 := rapidCertificate 515 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp516 := rapidCertificate 516 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp517 := rapidCertificate 517 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp518 := rapidCertificate 518 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp519 := rapidCertificate 519 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp520 := rapidCertificate 520 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp521 := rapidCertificate 521 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp522 := rapidCertificate 522 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp523 := rapidCertificate 523 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp524 := rapidCertificate 524 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp525 := rapidCertificate 525 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp526 := rapidCertificate 526 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp527 := rapidCertificate 527 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp528 := rapidCertificate 528 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp529 := rapidCertificate 529 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp530 := rapidCertificate 530 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp531 := rapidCertificate 531 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp532 := rapidCertificate 532 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp533 := rapidCertificate 533 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp534 := rapidCertificate 534 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp535 := rapidCertificate 535 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp536 := rapidCertificate 536 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp537 := rapidCertificate 537 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp538 := rapidCertificate 538 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp539 := rapidCertificate 539 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp540 := rapidCertificate 540 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp541 := rapidCertificate 541 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp542 := rapidCertificate 542 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp543 := rapidCertificate 543 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp544 := rapidCertificate 544 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp545 := rapidCertificate 545 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp546 := rapidCertificate 546 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp547 := rapidCertificate 547 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp548 := rapidCertificate 548 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp549 := rapidCertificate 549 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp550 := rapidCertificate 550 ⟨_, by conv => lhs; whnf⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 131072 in
def cp551 := rapidCertificate 551 ⟨_, by conv => lhs; whnf⟩

def rankPage (a : ℕ) : ℕ :=
  (if a < 276 then (if a < 138 then (if a < 69 then (if a < 34 then (if a < 17 then (if a < 8 then (if a < 4 then (if a < 2 then (if a < 1 then cp0.val else cp1.val) else (if a < 3 then cp2.val else cp3.val)) else (if a < 6 then (if a < 5 then cp4.val else cp5.val) else (if a < 7 then cp6.val else cp7.val))) else (if a < 12 then (if a < 10 then (if a < 9 then cp8.val else cp9.val) else (if a < 11 then cp10.val else cp11.val)) else (if a < 14 then (if a < 13 then cp12.val else cp13.val) else (if a < 15 then cp14.val else (if a < 16 then cp15.val else cp16.val))))) else (if a < 25 then (if a < 21 then (if a < 19 then (if a < 18 then cp17.val else cp18.val) else (if a < 20 then cp19.val else cp20.val)) else (if a < 23 then (if a < 22 then cp21.val else cp22.val) else (if a < 24 then cp23.val else cp24.val))) else (if a < 29 then (if a < 27 then (if a < 26 then cp25.val else cp26.val) else (if a < 28 then cp27.val else cp28.val)) else (if a < 31 then (if a < 30 then cp29.val else cp30.val) else (if a < 32 then cp31.val else (if a < 33 then cp32.val else cp33.val)))))) else (if a < 51 then (if a < 42 then (if a < 38 then (if a < 36 then (if a < 35 then cp34.val else cp35.val) else (if a < 37 then cp36.val else cp37.val)) else (if a < 40 then (if a < 39 then cp38.val else cp39.val) else (if a < 41 then cp40.val else cp41.val))) else (if a < 46 then (if a < 44 then (if a < 43 then cp42.val else cp43.val) else (if a < 45 then cp44.val else cp45.val)) else (if a < 48 then (if a < 47 then cp46.val else cp47.val) else (if a < 49 then cp48.val else (if a < 50 then cp49.val else cp50.val))))) else (if a < 60 then (if a < 55 then (if a < 53 then (if a < 52 then cp51.val else cp52.val) else (if a < 54 then cp53.val else cp54.val)) else (if a < 57 then (if a < 56 then cp55.val else cp56.val) else (if a < 58 then cp57.val else (if a < 59 then cp58.val else cp59.val)))) else (if a < 64 then (if a < 62 then (if a < 61 then cp60.val else cp61.val) else (if a < 63 then cp62.val else cp63.val)) else (if a < 66 then (if a < 65 then cp64.val else cp65.val) else (if a < 67 then cp66.val else (if a < 68 then cp67.val else cp68.val))))))) else (if a < 103 then (if a < 86 then (if a < 77 then (if a < 73 then (if a < 71 then (if a < 70 then cp69.val else cp70.val) else (if a < 72 then cp71.val else cp72.val)) else (if a < 75 then (if a < 74 then cp73.val else cp74.val) else (if a < 76 then cp75.val else cp76.val))) else (if a < 81 then (if a < 79 then (if a < 78 then cp77.val else cp78.val) else (if a < 80 then cp79.val else cp80.val)) else (if a < 83 then (if a < 82 then cp81.val else cp82.val) else (if a < 84 then cp83.val else (if a < 85 then cp84.val else cp85.val))))) else (if a < 94 then (if a < 90 then (if a < 88 then (if a < 87 then cp86.val else cp87.val) else (if a < 89 then cp88.val else cp89.val)) else (if a < 92 then (if a < 91 then cp90.val else cp91.val) else (if a < 93 then cp92.val else cp93.val))) else (if a < 98 then (if a < 96 then (if a < 95 then cp94.val else cp95.val) else (if a < 97 then cp96.val else cp97.val)) else (if a < 100 then (if a < 99 then cp98.val else cp99.val) else (if a < 101 then cp100.val else (if a < 102 then cp101.val else cp102.val)))))) else (if a < 120 then (if a < 111 then (if a < 107 then (if a < 105 then (if a < 104 then cp103.val else cp104.val) else (if a < 106 then cp105.val else cp106.val)) else (if a < 109 then (if a < 108 then cp107.val else cp108.val) else (if a < 110 then cp109.val else cp110.val))) else (if a < 115 then (if a < 113 then (if a < 112 then cp111.val else cp112.val) else (if a < 114 then cp113.val else cp114.val)) else (if a < 117 then (if a < 116 then cp115.val else cp116.val) else (if a < 118 then cp117.val else (if a < 119 then cp118.val else cp119.val))))) else (if a < 129 then (if a < 124 then (if a < 122 then (if a < 121 then cp120.val else cp121.val) else (if a < 123 then cp122.val else cp123.val)) else (if a < 126 then (if a < 125 then cp124.val else cp125.val) else (if a < 127 then cp126.val else (if a < 128 then cp127.val else cp128.val)))) else (if a < 133 then (if a < 131 then (if a < 130 then cp129.val else cp130.val) else (if a < 132 then cp131.val else cp132.val)) else (if a < 135 then (if a < 134 then cp133.val else cp134.val) else (if a < 136 then cp135.val else (if a < 137 then cp136.val else cp137.val)))))))) else (if a < 207 then (if a < 172 then (if a < 155 then (if a < 146 then (if a < 142 then (if a < 140 then (if a < 139 then cp138.val else cp139.val) else (if a < 141 then cp140.val else cp141.val)) else (if a < 144 then (if a < 143 then cp142.val else cp143.val) else (if a < 145 then cp144.val else cp145.val))) else (if a < 150 then (if a < 148 then (if a < 147 then cp146.val else cp147.val) else (if a < 149 then cp148.val else cp149.val)) else (if a < 152 then (if a < 151 then cp150.val else cp151.val) else (if a < 153 then cp152.val else (if a < 154 then cp153.val else cp154.val))))) else (if a < 163 then (if a < 159 then (if a < 157 then (if a < 156 then cp155.val else cp156.val) else (if a < 158 then cp157.val else cp158.val)) else (if a < 161 then (if a < 160 then cp159.val else cp160.val) else (if a < 162 then cp161.val else cp162.val))) else (if a < 167 then (if a < 165 then (if a < 164 then cp163.val else cp164.val) else (if a < 166 then cp165.val else cp166.val)) else (if a < 169 then (if a < 168 then cp167.val else cp168.val) else (if a < 170 then cp169.val else (if a < 171 then cp170.val else cp171.val)))))) else (if a < 189 then (if a < 180 then (if a < 176 then (if a < 174 then (if a < 173 then cp172.val else cp173.val) else (if a < 175 then cp174.val else cp175.val)) else (if a < 178 then (if a < 177 then cp176.val else cp177.val) else (if a < 179 then cp178.val else cp179.val))) else (if a < 184 then (if a < 182 then (if a < 181 then cp180.val else cp181.val) else (if a < 183 then cp182.val else cp183.val)) else (if a < 186 then (if a < 185 then cp184.val else cp185.val) else (if a < 187 then cp186.val else (if a < 188 then cp187.val else cp188.val))))) else (if a < 198 then (if a < 193 then (if a < 191 then (if a < 190 then cp189.val else cp190.val) else (if a < 192 then cp191.val else cp192.val)) else (if a < 195 then (if a < 194 then cp193.val else cp194.val) else (if a < 196 then cp195.val else (if a < 197 then cp196.val else cp197.val)))) else (if a < 202 then (if a < 200 then (if a < 199 then cp198.val else cp199.val) else (if a < 201 then cp200.val else cp201.val)) else (if a < 204 then (if a < 203 then cp202.val else cp203.val) else (if a < 205 then cp204.val else (if a < 206 then cp205.val else cp206.val))))))) else (if a < 241 then (if a < 224 then (if a < 215 then (if a < 211 then (if a < 209 then (if a < 208 then cp207.val else cp208.val) else (if a < 210 then cp209.val else cp210.val)) else (if a < 213 then (if a < 212 then cp211.val else cp212.val) else (if a < 214 then cp213.val else cp214.val))) else (if a < 219 then (if a < 217 then (if a < 216 then cp215.val else cp216.val) else (if a < 218 then cp217.val else cp218.val)) else (if a < 221 then (if a < 220 then cp219.val else cp220.val) else (if a < 222 then cp221.val else (if a < 223 then cp222.val else cp223.val))))) else (if a < 232 then (if a < 228 then (if a < 226 then (if a < 225 then cp224.val else cp225.val) else (if a < 227 then cp226.val else cp227.val)) else (if a < 230 then (if a < 229 then cp228.val else cp229.val) else (if a < 231 then cp230.val else cp231.val))) else (if a < 236 then (if a < 234 then (if a < 233 then cp232.val else cp233.val) else (if a < 235 then cp234.val else cp235.val)) else (if a < 238 then (if a < 237 then cp236.val else cp237.val) else (if a < 239 then cp238.val else (if a < 240 then cp239.val else cp240.val)))))) else (if a < 258 then (if a < 249 then (if a < 245 then (if a < 243 then (if a < 242 then cp241.val else cp242.val) else (if a < 244 then cp243.val else cp244.val)) else (if a < 247 then (if a < 246 then cp245.val else cp246.val) else (if a < 248 then cp247.val else cp248.val))) else (if a < 253 then (if a < 251 then (if a < 250 then cp249.val else cp250.val) else (if a < 252 then cp251.val else cp252.val)) else (if a < 255 then (if a < 254 then cp253.val else cp254.val) else (if a < 256 then cp255.val else (if a < 257 then cp256.val else cp257.val))))) else (if a < 267 then (if a < 262 then (if a < 260 then (if a < 259 then cp258.val else cp259.val) else (if a < 261 then cp260.val else cp261.val)) else (if a < 264 then (if a < 263 then cp262.val else cp263.val) else (if a < 265 then cp264.val else (if a < 266 then cp265.val else cp266.val)))) else (if a < 271 then (if a < 269 then (if a < 268 then cp267.val else cp268.val) else (if a < 270 then cp269.val else cp270.val)) else (if a < 273 then (if a < 272 then cp271.val else cp272.val) else (if a < 274 then cp273.val else (if a < 275 then cp274.val else cp275.val))))))))) else (if a < 414 then (if a < 345 then (if a < 310 then (if a < 293 then (if a < 284 then (if a < 280 then (if a < 278 then (if a < 277 then cp276.val else cp277.val) else (if a < 279 then cp278.val else cp279.val)) else (if a < 282 then (if a < 281 then cp280.val else cp281.val) else (if a < 283 then cp282.val else cp283.val))) else (if a < 288 then (if a < 286 then (if a < 285 then cp284.val else cp285.val) else (if a < 287 then cp286.val else cp287.val)) else (if a < 290 then (if a < 289 then cp288.val else cp289.val) else (if a < 291 then cp290.val else (if a < 292 then cp291.val else cp292.val))))) else (if a < 301 then (if a < 297 then (if a < 295 then (if a < 294 then cp293.val else cp294.val) else (if a < 296 then cp295.val else cp296.val)) else (if a < 299 then (if a < 298 then cp297.val else cp298.val) else (if a < 300 then cp299.val else cp300.val))) else (if a < 305 then (if a < 303 then (if a < 302 then cp301.val else cp302.val) else (if a < 304 then cp303.val else cp304.val)) else (if a < 307 then (if a < 306 then cp305.val else cp306.val) else (if a < 308 then cp307.val else (if a < 309 then cp308.val else cp309.val)))))) else (if a < 327 then (if a < 318 then (if a < 314 then (if a < 312 then (if a < 311 then cp310.val else cp311.val) else (if a < 313 then cp312.val else cp313.val)) else (if a < 316 then (if a < 315 then cp314.val else cp315.val) else (if a < 317 then cp316.val else cp317.val))) else (if a < 322 then (if a < 320 then (if a < 319 then cp318.val else cp319.val) else (if a < 321 then cp320.val else cp321.val)) else (if a < 324 then (if a < 323 then cp322.val else cp323.val) else (if a < 325 then cp324.val else (if a < 326 then cp325.val else cp326.val))))) else (if a < 336 then (if a < 331 then (if a < 329 then (if a < 328 then cp327.val else cp328.val) else (if a < 330 then cp329.val else cp330.val)) else (if a < 333 then (if a < 332 then cp331.val else cp332.val) else (if a < 334 then cp333.val else (if a < 335 then cp334.val else cp335.val)))) else (if a < 340 then (if a < 338 then (if a < 337 then cp336.val else cp337.val) else (if a < 339 then cp338.val else cp339.val)) else (if a < 342 then (if a < 341 then cp340.val else cp341.val) else (if a < 343 then cp342.val else (if a < 344 then cp343.val else cp344.val))))))) else (if a < 379 then (if a < 362 then (if a < 353 then (if a < 349 then (if a < 347 then (if a < 346 then cp345.val else cp346.val) else (if a < 348 then cp347.val else cp348.val)) else (if a < 351 then (if a < 350 then cp349.val else cp350.val) else (if a < 352 then cp351.val else cp352.val))) else (if a < 357 then (if a < 355 then (if a < 354 then cp353.val else cp354.val) else (if a < 356 then cp355.val else cp356.val)) else (if a < 359 then (if a < 358 then cp357.val else cp358.val) else (if a < 360 then cp359.val else (if a < 361 then cp360.val else cp361.val))))) else (if a < 370 then (if a < 366 then (if a < 364 then (if a < 363 then cp362.val else cp363.val) else (if a < 365 then cp364.val else cp365.val)) else (if a < 368 then (if a < 367 then cp366.val else cp367.val) else (if a < 369 then cp368.val else cp369.val))) else (if a < 374 then (if a < 372 then (if a < 371 then cp370.val else cp371.val) else (if a < 373 then cp372.val else cp373.val)) else (if a < 376 then (if a < 375 then cp374.val else cp375.val) else (if a < 377 then cp376.val else (if a < 378 then cp377.val else cp378.val)))))) else (if a < 396 then (if a < 387 then (if a < 383 then (if a < 381 then (if a < 380 then cp379.val else cp380.val) else (if a < 382 then cp381.val else cp382.val)) else (if a < 385 then (if a < 384 then cp383.val else cp384.val) else (if a < 386 then cp385.val else cp386.val))) else (if a < 391 then (if a < 389 then (if a < 388 then cp387.val else cp388.val) else (if a < 390 then cp389.val else cp390.val)) else (if a < 393 then (if a < 392 then cp391.val else cp392.val) else (if a < 394 then cp393.val else (if a < 395 then cp394.val else cp395.val))))) else (if a < 405 then (if a < 400 then (if a < 398 then (if a < 397 then cp396.val else cp397.val) else (if a < 399 then cp398.val else cp399.val)) else (if a < 402 then (if a < 401 then cp400.val else cp401.val) else (if a < 403 then cp402.val else (if a < 404 then cp403.val else cp404.val)))) else (if a < 409 then (if a < 407 then (if a < 406 then cp405.val else cp406.val) else (if a < 408 then cp407.val else cp408.val)) else (if a < 411 then (if a < 410 then cp409.val else cp410.val) else (if a < 412 then cp411.val else (if a < 413 then cp412.val else cp413.val)))))))) else (if a < 483 then (if a < 448 then (if a < 431 then (if a < 422 then (if a < 418 then (if a < 416 then (if a < 415 then cp414.val else cp415.val) else (if a < 417 then cp416.val else cp417.val)) else (if a < 420 then (if a < 419 then cp418.val else cp419.val) else (if a < 421 then cp420.val else cp421.val))) else (if a < 426 then (if a < 424 then (if a < 423 then cp422.val else cp423.val) else (if a < 425 then cp424.val else cp425.val)) else (if a < 428 then (if a < 427 then cp426.val else cp427.val) else (if a < 429 then cp428.val else (if a < 430 then cp429.val else cp430.val))))) else (if a < 439 then (if a < 435 then (if a < 433 then (if a < 432 then cp431.val else cp432.val) else (if a < 434 then cp433.val else cp434.val)) else (if a < 437 then (if a < 436 then cp435.val else cp436.val) else (if a < 438 then cp437.val else cp438.val))) else (if a < 443 then (if a < 441 then (if a < 440 then cp439.val else cp440.val) else (if a < 442 then cp441.val else cp442.val)) else (if a < 445 then (if a < 444 then cp443.val else cp444.val) else (if a < 446 then cp445.val else (if a < 447 then cp446.val else cp447.val)))))) else (if a < 465 then (if a < 456 then (if a < 452 then (if a < 450 then (if a < 449 then cp448.val else cp449.val) else (if a < 451 then cp450.val else cp451.val)) else (if a < 454 then (if a < 453 then cp452.val else cp453.val) else (if a < 455 then cp454.val else cp455.val))) else (if a < 460 then (if a < 458 then (if a < 457 then cp456.val else cp457.val) else (if a < 459 then cp458.val else cp459.val)) else (if a < 462 then (if a < 461 then cp460.val else cp461.val) else (if a < 463 then cp462.val else (if a < 464 then cp463.val else cp464.val))))) else (if a < 474 then (if a < 469 then (if a < 467 then (if a < 466 then cp465.val else cp466.val) else (if a < 468 then cp467.val else cp468.val)) else (if a < 471 then (if a < 470 then cp469.val else cp470.val) else (if a < 472 then cp471.val else (if a < 473 then cp472.val else cp473.val)))) else (if a < 478 then (if a < 476 then (if a < 475 then cp474.val else cp475.val) else (if a < 477 then cp476.val else cp477.val)) else (if a < 480 then (if a < 479 then cp478.val else cp479.val) else (if a < 481 then cp480.val else (if a < 482 then cp481.val else cp482.val))))))) else (if a < 517 then (if a < 500 then (if a < 491 then (if a < 487 then (if a < 485 then (if a < 484 then cp483.val else cp484.val) else (if a < 486 then cp485.val else cp486.val)) else (if a < 489 then (if a < 488 then cp487.val else cp488.val) else (if a < 490 then cp489.val else cp490.val))) else (if a < 495 then (if a < 493 then (if a < 492 then cp491.val else cp492.val) else (if a < 494 then cp493.val else cp494.val)) else (if a < 497 then (if a < 496 then cp495.val else cp496.val) else (if a < 498 then cp497.val else (if a < 499 then cp498.val else cp499.val))))) else (if a < 508 then (if a < 504 then (if a < 502 then (if a < 501 then cp500.val else cp501.val) else (if a < 503 then cp502.val else cp503.val)) else (if a < 506 then (if a < 505 then cp504.val else cp505.val) else (if a < 507 then cp506.val else cp507.val))) else (if a < 512 then (if a < 510 then (if a < 509 then cp508.val else cp509.val) else (if a < 511 then cp510.val else cp511.val)) else (if a < 514 then (if a < 513 then cp512.val else cp513.val) else (if a < 515 then cp514.val else (if a < 516 then cp515.val else cp516.val)))))) else (if a < 534 then (if a < 525 then (if a < 521 then (if a < 519 then (if a < 518 then cp517.val else cp518.val) else (if a < 520 then cp519.val else cp520.val)) else (if a < 523 then (if a < 522 then cp521.val else cp522.val) else (if a < 524 then cp523.val else cp524.val))) else (if a < 529 then (if a < 527 then (if a < 526 then cp525.val else cp526.val) else (if a < 528 then cp527.val else cp528.val)) else (if a < 531 then (if a < 530 then cp529.val else cp530.val) else (if a < 532 then cp531.val else (if a < 533 then cp532.val else cp533.val))))) else (if a < 543 then (if a < 538 then (if a < 536 then (if a < 535 then cp534.val else cp535.val) else (if a < 537 then cp536.val else cp537.val)) else (if a < 540 then (if a < 539 then cp538.val else cp539.val) else (if a < 541 then cp540.val else (if a < 542 then cp541.val else cp542.val)))) else (if a < 547 then (if a < 545 then (if a < 544 then cp543.val else cp544.val) else (if a < 546 then cp545.val else cp546.val)) else (if a < 549 then (if a < 548 then cp547.val else cp548.val) else (if a < 550 then cp549.val else (if a < 551 then cp550.val else cp551.val))))))))))


end Astra247824.Compact

/- Select the certificate for a normalized rank page. -/
namespace Astra247824.Compact

set_option maxRecDepth 32768 in
private theorem part0 (a : ℕ) (low : 0≤a) (high : a<16) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp0.property.symm
  · exact cp1.property.symm
  · exact cp2.property.symm
  · exact cp3.property.symm
  · exact cp4.property.symm
  · exact cp5.property.symm
  · exact cp6.property.symm
  · exact cp7.property.symm
  · exact cp8.property.symm
  · exact cp9.property.symm
  · exact cp10.property.symm
  · exact cp11.property.symm
  · exact cp12.property.symm
  · exact cp13.property.symm
  · exact cp14.property.symm
  · exact cp15.property.symm

set_option maxRecDepth 32768 in
private theorem part16 (a : ℕ) (low : 16≤a) (high : a<32) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp16.property.symm
  · exact cp17.property.symm
  · exact cp18.property.symm
  · exact cp19.property.symm
  · exact cp20.property.symm
  · exact cp21.property.symm
  · exact cp22.property.symm
  · exact cp23.property.symm
  · exact cp24.property.symm
  · exact cp25.property.symm
  · exact cp26.property.symm
  · exact cp27.property.symm
  · exact cp28.property.symm
  · exact cp29.property.symm
  · exact cp30.property.symm
  · exact cp31.property.symm

set_option maxRecDepth 32768 in
private theorem part32 (a : ℕ) (low : 32≤a) (high : a<48) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp32.property.symm
  · exact cp33.property.symm
  · exact cp34.property.symm
  · exact cp35.property.symm
  · exact cp36.property.symm
  · exact cp37.property.symm
  · exact cp38.property.symm
  · exact cp39.property.symm
  · exact cp40.property.symm
  · exact cp41.property.symm
  · exact cp42.property.symm
  · exact cp43.property.symm
  · exact cp44.property.symm
  · exact cp45.property.symm
  · exact cp46.property.symm
  · exact cp47.property.symm

set_option maxRecDepth 32768 in
private theorem part48 (a : ℕ) (low : 48≤a) (high : a<64) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp48.property.symm
  · exact cp49.property.symm
  · exact cp50.property.symm
  · exact cp51.property.symm
  · exact cp52.property.symm
  · exact cp53.property.symm
  · exact cp54.property.symm
  · exact cp55.property.symm
  · exact cp56.property.symm
  · exact cp57.property.symm
  · exact cp58.property.symm
  · exact cp59.property.symm
  · exact cp60.property.symm
  · exact cp61.property.symm
  · exact cp62.property.symm
  · exact cp63.property.symm

set_option maxRecDepth 32768 in
private theorem part64 (a : ℕ) (low : 64≤a) (high : a<80) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp64.property.symm
  · exact cp65.property.symm
  · exact cp66.property.symm
  · exact cp67.property.symm
  · exact cp68.property.symm
  · exact cp69.property.symm
  · exact cp70.property.symm
  · exact cp71.property.symm
  · exact cp72.property.symm
  · exact cp73.property.symm
  · exact cp74.property.symm
  · exact cp75.property.symm
  · exact cp76.property.symm
  · exact cp77.property.symm
  · exact cp78.property.symm
  · exact cp79.property.symm

set_option maxRecDepth 32768 in
private theorem part80 (a : ℕ) (low : 80≤a) (high : a<96) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp80.property.symm
  · exact cp81.property.symm
  · exact cp82.property.symm
  · exact cp83.property.symm
  · exact cp84.property.symm
  · exact cp85.property.symm
  · exact cp86.property.symm
  · exact cp87.property.symm
  · exact cp88.property.symm
  · exact cp89.property.symm
  · exact cp90.property.symm
  · exact cp91.property.symm
  · exact cp92.property.symm
  · exact cp93.property.symm
  · exact cp94.property.symm
  · exact cp95.property.symm

set_option maxRecDepth 32768 in
private theorem part96 (a : ℕ) (low : 96≤a) (high : a<112) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp96.property.symm
  · exact cp97.property.symm
  · exact cp98.property.symm
  · exact cp99.property.symm
  · exact cp100.property.symm
  · exact cp101.property.symm
  · exact cp102.property.symm
  · exact cp103.property.symm
  · exact cp104.property.symm
  · exact cp105.property.symm
  · exact cp106.property.symm
  · exact cp107.property.symm
  · exact cp108.property.symm
  · exact cp109.property.symm
  · exact cp110.property.symm
  · exact cp111.property.symm

set_option maxRecDepth 32768 in
private theorem part112 (a : ℕ) (low : 112≤a) (high : a<128) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp112.property.symm
  · exact cp113.property.symm
  · exact cp114.property.symm
  · exact cp115.property.symm
  · exact cp116.property.symm
  · exact cp117.property.symm
  · exact cp118.property.symm
  · exact cp119.property.symm
  · exact cp120.property.symm
  · exact cp121.property.symm
  · exact cp122.property.symm
  · exact cp123.property.symm
  · exact cp124.property.symm
  · exact cp125.property.symm
  · exact cp126.property.symm
  · exact cp127.property.symm

set_option maxRecDepth 32768 in
private theorem part128 (a : ℕ) (low : 128≤a) (high : a<144) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp128.property.symm
  · exact cp129.property.symm
  · exact cp130.property.symm
  · exact cp131.property.symm
  · exact cp132.property.symm
  · exact cp133.property.symm
  · exact cp134.property.symm
  · exact cp135.property.symm
  · exact cp136.property.symm
  · exact cp137.property.symm
  · exact cp138.property.symm
  · exact cp139.property.symm
  · exact cp140.property.symm
  · exact cp141.property.symm
  · exact cp142.property.symm
  · exact cp143.property.symm

set_option maxRecDepth 32768 in
private theorem part144 (a : ℕ) (low : 144≤a) (high : a<160) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp144.property.symm
  · exact cp145.property.symm
  · exact cp146.property.symm
  · exact cp147.property.symm
  · exact cp148.property.symm
  · exact cp149.property.symm
  · exact cp150.property.symm
  · exact cp151.property.symm
  · exact cp152.property.symm
  · exact cp153.property.symm
  · exact cp154.property.symm
  · exact cp155.property.symm
  · exact cp156.property.symm
  · exact cp157.property.symm
  · exact cp158.property.symm
  · exact cp159.property.symm

set_option maxRecDepth 32768 in
private theorem part160 (a : ℕ) (low : 160≤a) (high : a<176) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp160.property.symm
  · exact cp161.property.symm
  · exact cp162.property.symm
  · exact cp163.property.symm
  · exact cp164.property.symm
  · exact cp165.property.symm
  · exact cp166.property.symm
  · exact cp167.property.symm
  · exact cp168.property.symm
  · exact cp169.property.symm
  · exact cp170.property.symm
  · exact cp171.property.symm
  · exact cp172.property.symm
  · exact cp173.property.symm
  · exact cp174.property.symm
  · exact cp175.property.symm

set_option maxRecDepth 32768 in
private theorem part176 (a : ℕ) (low : 176≤a) (high : a<192) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp176.property.symm
  · exact cp177.property.symm
  · exact cp178.property.symm
  · exact cp179.property.symm
  · exact cp180.property.symm
  · exact cp181.property.symm
  · exact cp182.property.symm
  · exact cp183.property.symm
  · exact cp184.property.symm
  · exact cp185.property.symm
  · exact cp186.property.symm
  · exact cp187.property.symm
  · exact cp188.property.symm
  · exact cp189.property.symm
  · exact cp190.property.symm
  · exact cp191.property.symm

set_option maxRecDepth 32768 in
private theorem part192 (a : ℕ) (low : 192≤a) (high : a<208) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp192.property.symm
  · exact cp193.property.symm
  · exact cp194.property.symm
  · exact cp195.property.symm
  · exact cp196.property.symm
  · exact cp197.property.symm
  · exact cp198.property.symm
  · exact cp199.property.symm
  · exact cp200.property.symm
  · exact cp201.property.symm
  · exact cp202.property.symm
  · exact cp203.property.symm
  · exact cp204.property.symm
  · exact cp205.property.symm
  · exact cp206.property.symm
  · exact cp207.property.symm

set_option maxRecDepth 32768 in
private theorem part208 (a : ℕ) (low : 208≤a) (high : a<224) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp208.property.symm
  · exact cp209.property.symm
  · exact cp210.property.symm
  · exact cp211.property.symm
  · exact cp212.property.symm
  · exact cp213.property.symm
  · exact cp214.property.symm
  · exact cp215.property.symm
  · exact cp216.property.symm
  · exact cp217.property.symm
  · exact cp218.property.symm
  · exact cp219.property.symm
  · exact cp220.property.symm
  · exact cp221.property.symm
  · exact cp222.property.symm
  · exact cp223.property.symm

set_option maxRecDepth 32768 in
private theorem part224 (a : ℕ) (low : 224≤a) (high : a<240) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp224.property.symm
  · exact cp225.property.symm
  · exact cp226.property.symm
  · exact cp227.property.symm
  · exact cp228.property.symm
  · exact cp229.property.symm
  · exact cp230.property.symm
  · exact cp231.property.symm
  · exact cp232.property.symm
  · exact cp233.property.symm
  · exact cp234.property.symm
  · exact cp235.property.symm
  · exact cp236.property.symm
  · exact cp237.property.symm
  · exact cp238.property.symm
  · exact cp239.property.symm

set_option maxRecDepth 32768 in
private theorem part240 (a : ℕ) (low : 240≤a) (high : a<256) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp240.property.symm
  · exact cp241.property.symm
  · exact cp242.property.symm
  · exact cp243.property.symm
  · exact cp244.property.symm
  · exact cp245.property.symm
  · exact cp246.property.symm
  · exact cp247.property.symm
  · exact cp248.property.symm
  · exact cp249.property.symm
  · exact cp250.property.symm
  · exact cp251.property.symm
  · exact cp252.property.symm
  · exact cp253.property.symm
  · exact cp254.property.symm
  · exact cp255.property.symm

set_option maxRecDepth 32768 in
private theorem part256 (a : ℕ) (low : 256≤a) (high : a<272) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp256.property.symm
  · exact cp257.property.symm
  · exact cp258.property.symm
  · exact cp259.property.symm
  · exact cp260.property.symm
  · exact cp261.property.symm
  · exact cp262.property.symm
  · exact cp263.property.symm
  · exact cp264.property.symm
  · exact cp265.property.symm
  · exact cp266.property.symm
  · exact cp267.property.symm
  · exact cp268.property.symm
  · exact cp269.property.symm
  · exact cp270.property.symm
  · exact cp271.property.symm

set_option maxRecDepth 32768 in
private theorem part272 (a : ℕ) (low : 272≤a) (high : a<288) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp272.property.symm
  · exact cp273.property.symm
  · exact cp274.property.symm
  · exact cp275.property.symm
  · exact cp276.property.symm
  · exact cp277.property.symm
  · exact cp278.property.symm
  · exact cp279.property.symm
  · exact cp280.property.symm
  · exact cp281.property.symm
  · exact cp282.property.symm
  · exact cp283.property.symm
  · exact cp284.property.symm
  · exact cp285.property.symm
  · exact cp286.property.symm
  · exact cp287.property.symm

set_option maxRecDepth 32768 in
private theorem part288 (a : ℕ) (low : 288≤a) (high : a<304) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp288.property.symm
  · exact cp289.property.symm
  · exact cp290.property.symm
  · exact cp291.property.symm
  · exact cp292.property.symm
  · exact cp293.property.symm
  · exact cp294.property.symm
  · exact cp295.property.symm
  · exact cp296.property.symm
  · exact cp297.property.symm
  · exact cp298.property.symm
  · exact cp299.property.symm
  · exact cp300.property.symm
  · exact cp301.property.symm
  · exact cp302.property.symm
  · exact cp303.property.symm

set_option maxRecDepth 32768 in
private theorem part304 (a : ℕ) (low : 304≤a) (high : a<320) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp304.property.symm
  · exact cp305.property.symm
  · exact cp306.property.symm
  · exact cp307.property.symm
  · exact cp308.property.symm
  · exact cp309.property.symm
  · exact cp310.property.symm
  · exact cp311.property.symm
  · exact cp312.property.symm
  · exact cp313.property.symm
  · exact cp314.property.symm
  · exact cp315.property.symm
  · exact cp316.property.symm
  · exact cp317.property.symm
  · exact cp318.property.symm
  · exact cp319.property.symm

set_option maxRecDepth 32768 in
private theorem part320 (a : ℕ) (low : 320≤a) (high : a<336) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp320.property.symm
  · exact cp321.property.symm
  · exact cp322.property.symm
  · exact cp323.property.symm
  · exact cp324.property.symm
  · exact cp325.property.symm
  · exact cp326.property.symm
  · exact cp327.property.symm
  · exact cp328.property.symm
  · exact cp329.property.symm
  · exact cp330.property.symm
  · exact cp331.property.symm
  · exact cp332.property.symm
  · exact cp333.property.symm
  · exact cp334.property.symm
  · exact cp335.property.symm

set_option maxRecDepth 32768 in
private theorem part336 (a : ℕ) (low : 336≤a) (high : a<352) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp336.property.symm
  · exact cp337.property.symm
  · exact cp338.property.symm
  · exact cp339.property.symm
  · exact cp340.property.symm
  · exact cp341.property.symm
  · exact cp342.property.symm
  · exact cp343.property.symm
  · exact cp344.property.symm
  · exact cp345.property.symm
  · exact cp346.property.symm
  · exact cp347.property.symm
  · exact cp348.property.symm
  · exact cp349.property.symm
  · exact cp350.property.symm
  · exact cp351.property.symm

set_option maxRecDepth 32768 in
private theorem part352 (a : ℕ) (low : 352≤a) (high : a<368) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp352.property.symm
  · exact cp353.property.symm
  · exact cp354.property.symm
  · exact cp355.property.symm
  · exact cp356.property.symm
  · exact cp357.property.symm
  · exact cp358.property.symm
  · exact cp359.property.symm
  · exact cp360.property.symm
  · exact cp361.property.symm
  · exact cp362.property.symm
  · exact cp363.property.symm
  · exact cp364.property.symm
  · exact cp365.property.symm
  · exact cp366.property.symm
  · exact cp367.property.symm

set_option maxRecDepth 32768 in
private theorem part368 (a : ℕ) (low : 368≤a) (high : a<384) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp368.property.symm
  · exact cp369.property.symm
  · exact cp370.property.symm
  · exact cp371.property.symm
  · exact cp372.property.symm
  · exact cp373.property.symm
  · exact cp374.property.symm
  · exact cp375.property.symm
  · exact cp376.property.symm
  · exact cp377.property.symm
  · exact cp378.property.symm
  · exact cp379.property.symm
  · exact cp380.property.symm
  · exact cp381.property.symm
  · exact cp382.property.symm
  · exact cp383.property.symm

set_option maxRecDepth 32768 in
private theorem part384 (a : ℕ) (low : 384≤a) (high : a<400) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp384.property.symm
  · exact cp385.property.symm
  · exact cp386.property.symm
  · exact cp387.property.symm
  · exact cp388.property.symm
  · exact cp389.property.symm
  · exact cp390.property.symm
  · exact cp391.property.symm
  · exact cp392.property.symm
  · exact cp393.property.symm
  · exact cp394.property.symm
  · exact cp395.property.symm
  · exact cp396.property.symm
  · exact cp397.property.symm
  · exact cp398.property.symm
  · exact cp399.property.symm

set_option maxRecDepth 32768 in
private theorem part400 (a : ℕ) (low : 400≤a) (high : a<416) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp400.property.symm
  · exact cp401.property.symm
  · exact cp402.property.symm
  · exact cp403.property.symm
  · exact cp404.property.symm
  · exact cp405.property.symm
  · exact cp406.property.symm
  · exact cp407.property.symm
  · exact cp408.property.symm
  · exact cp409.property.symm
  · exact cp410.property.symm
  · exact cp411.property.symm
  · exact cp412.property.symm
  · exact cp413.property.symm
  · exact cp414.property.symm
  · exact cp415.property.symm

set_option maxRecDepth 32768 in
private theorem part416 (a : ℕ) (low : 416≤a) (high : a<432) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp416.property.symm
  · exact cp417.property.symm
  · exact cp418.property.symm
  · exact cp419.property.symm
  · exact cp420.property.symm
  · exact cp421.property.symm
  · exact cp422.property.symm
  · exact cp423.property.symm
  · exact cp424.property.symm
  · exact cp425.property.symm
  · exact cp426.property.symm
  · exact cp427.property.symm
  · exact cp428.property.symm
  · exact cp429.property.symm
  · exact cp430.property.symm
  · exact cp431.property.symm

set_option maxRecDepth 32768 in
private theorem part432 (a : ℕ) (low : 432≤a) (high : a<448) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp432.property.symm
  · exact cp433.property.symm
  · exact cp434.property.symm
  · exact cp435.property.symm
  · exact cp436.property.symm
  · exact cp437.property.symm
  · exact cp438.property.symm
  · exact cp439.property.symm
  · exact cp440.property.symm
  · exact cp441.property.symm
  · exact cp442.property.symm
  · exact cp443.property.symm
  · exact cp444.property.symm
  · exact cp445.property.symm
  · exact cp446.property.symm
  · exact cp447.property.symm

set_option maxRecDepth 32768 in
private theorem part448 (a : ℕ) (low : 448≤a) (high : a<464) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp448.property.symm
  · exact cp449.property.symm
  · exact cp450.property.symm
  · exact cp451.property.symm
  · exact cp452.property.symm
  · exact cp453.property.symm
  · exact cp454.property.symm
  · exact cp455.property.symm
  · exact cp456.property.symm
  · exact cp457.property.symm
  · exact cp458.property.symm
  · exact cp459.property.symm
  · exact cp460.property.symm
  · exact cp461.property.symm
  · exact cp462.property.symm
  · exact cp463.property.symm

set_option maxRecDepth 32768 in
private theorem part464 (a : ℕ) (low : 464≤a) (high : a<480) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp464.property.symm
  · exact cp465.property.symm
  · exact cp466.property.symm
  · exact cp467.property.symm
  · exact cp468.property.symm
  · exact cp469.property.symm
  · exact cp470.property.symm
  · exact cp471.property.symm
  · exact cp472.property.symm
  · exact cp473.property.symm
  · exact cp474.property.symm
  · exact cp475.property.symm
  · exact cp476.property.symm
  · exact cp477.property.symm
  · exact cp478.property.symm
  · exact cp479.property.symm

set_option maxRecDepth 32768 in
private theorem part480 (a : ℕ) (low : 480≤a) (high : a<496) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp480.property.symm
  · exact cp481.property.symm
  · exact cp482.property.symm
  · exact cp483.property.symm
  · exact cp484.property.symm
  · exact cp485.property.symm
  · exact cp486.property.symm
  · exact cp487.property.symm
  · exact cp488.property.symm
  · exact cp489.property.symm
  · exact cp490.property.symm
  · exact cp491.property.symm
  · exact cp492.property.symm
  · exact cp493.property.symm
  · exact cp494.property.symm
  · exact cp495.property.symm

set_option maxRecDepth 32768 in
private theorem part496 (a : ℕ) (low : 496≤a) (high : a<512) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp496.property.symm
  · exact cp497.property.symm
  · exact cp498.property.symm
  · exact cp499.property.symm
  · exact cp500.property.symm
  · exact cp501.property.symm
  · exact cp502.property.symm
  · exact cp503.property.symm
  · exact cp504.property.symm
  · exact cp505.property.symm
  · exact cp506.property.symm
  · exact cp507.property.symm
  · exact cp508.property.symm
  · exact cp509.property.symm
  · exact cp510.property.symm
  · exact cp511.property.symm

set_option maxRecDepth 32768 in
private theorem part512 (a : ℕ) (low : 512≤a) (high : a<528) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp512.property.symm
  · exact cp513.property.symm
  · exact cp514.property.symm
  · exact cp515.property.symm
  · exact cp516.property.symm
  · exact cp517.property.symm
  · exact cp518.property.symm
  · exact cp519.property.symm
  · exact cp520.property.symm
  · exact cp521.property.symm
  · exact cp522.property.symm
  · exact cp523.property.symm
  · exact cp524.property.symm
  · exact cp525.property.symm
  · exact cp526.property.symm
  · exact cp527.property.symm

set_option maxRecDepth 32768 in
private theorem part528 (a : ℕ) (low : 528≤a) (high : a<544) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp528.property.symm
  · exact cp529.property.symm
  · exact cp530.property.symm
  · exact cp531.property.symm
  · exact cp532.property.symm
  · exact cp533.property.symm
  · exact cp534.property.symm
  · exact cp535.property.symm
  · exact cp536.property.symm
  · exact cp537.property.symm
  · exact cp538.property.symm
  · exact cp539.property.symm
  · exact cp540.property.symm
  · exact cp541.property.symm
  · exact cp542.property.symm
  · exact cp543.property.symm

set_option maxRecDepth 32768 in
private theorem part544 (a : ℕ) (low : 544≤a) (high : a<552) :
    rankPage a = computedPage a := by
  interval_cases a
  · exact cp544.property.symm
  · exact cp545.property.symm
  · exact cp546.property.symm
  · exact cp547.property.symm
  · exact cp548.property.symm
  · exact cp549.property.symm
  · exact cp550.property.symm
  · exact cp551.property.symm

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 32768 in
theorem rankPage_eq (a : ℕ) (ha : a<552) : rankPage a = computedPage a := by
  by_cases h272 : a<272
  · by_cases h128 : a<128
    · by_cases h64 : a<64
      · by_cases h32 : a<32
        · by_cases h16 : a<16
          · exact part0 a (by omega) (by omega)
          · exact part16 a (by omega) (by omega)
        · by_cases h48 : a<48
          · exact part32 a (by omega) (by omega)
          · exact part48 a (by omega) (by omega)
      · by_cases h96 : a<96
        · by_cases h80 : a<80
          · exact part64 a (by omega) (by omega)
          · exact part80 a (by omega) (by omega)
        · by_cases h112 : a<112
          · exact part96 a (by omega) (by omega)
          · exact part112 a (by omega) (by omega)
    · by_cases h192 : a<192
      · by_cases h160 : a<160
        · by_cases h144 : a<144
          · exact part128 a (by omega) (by omega)
          · exact part144 a (by omega) (by omega)
        · by_cases h176 : a<176
          · exact part160 a (by omega) (by omega)
          · exact part176 a (by omega) (by omega)
      · by_cases h224 : a<224
        · by_cases h208 : a<208
          · exact part192 a (by omega) (by omega)
          · exact part208 a (by omega) (by omega)
        · by_cases h240 : a<240
          · exact part224 a (by omega) (by omega)
          · by_cases h256 : a<256
            · exact part240 a (by omega) (by omega)
            · exact part256 a (by omega) (by omega)
  · by_cases h416 : a<416
    · by_cases h336 : a<336
      · by_cases h304 : a<304
        · by_cases h288 : a<288
          · exact part272 a (by omega) (by omega)
          · exact part288 a (by omega) (by omega)
        · by_cases h320 : a<320
          · exact part304 a (by omega) (by omega)
          · exact part320 a (by omega) (by omega)
      · by_cases h368 : a<368
        · by_cases h352 : a<352
          · exact part336 a (by omega) (by omega)
          · exact part352 a (by omega) (by omega)
        · by_cases h384 : a<384
          · exact part368 a (by omega) (by omega)
          · by_cases h400 : a<400
            · exact part384 a (by omega) (by omega)
            · exact part400 a (by omega) (by omega)
    · by_cases h480 : a<480
      · by_cases h448 : a<448
        · by_cases h432 : a<432
          · exact part416 a (by omega) (by omega)
          · exact part432 a (by omega) (by omega)
        · by_cases h464 : a<464
          · exact part448 a (by omega) (by omega)
          · exact part464 a (by omega) (by omega)
      · by_cases h512 : a<512
        · by_cases h496 : a<496
          · exact part480 a (by omega) (by omega)
          · exact part496 a (by omega) (by omega)
        · by_cases h528 : a<528
          · exact part512 a (by omega) (by omega)
          · by_cases h544 : a<544
            · exact part528 a (by omega) (by omega)
            · exact part544 a (by omega) (by omega)

end Astra247824.Compact

/- A full prime-count oracle from the segmented prime masks and page boundary counts. -/
namespace Astra247824.Compact
open Astra247824.GlobalRank Finset

private def okBase (a : ℕ) : Bool := a≥552 ||
  (decide (pageBase a < 700000) &&
   (a≥551 || pageBase (a+1) == lane (rankPage a) 8191))

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32768 in
private theorem baseChecks : allFrom okBase 10 0 = true := by decide +kernel

private theorem baseEntry (a : ℕ) (ha : a<552) : pageBase a < 700000 ∧
    (a≥551 ∨ pageBase (a+1) = lane (rankPage a) 8191) := by
  have h := allFrom_at baseChecks (Nat.zero_le a) (show a<0+2^10 by omega)
  simpa only [okBase, show ¬a≥552 by omega, decide_false, Bool.false_or,
    Bool.and_eq_true_iff, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] using h

private theorem page_prefix (a j : ℕ) (ha : a<552) (hj : j<8192) :
    lane (rankPage a) j = pageBase a + bitPrefix (pageMask a) (2*(j+1)) := by
  have small := (baseEntry a ha).1
  rw [rankPage_eq a ha, computedPage, makePage_spec _ _ _ (by norm_num <;> omega),
    lane_packDigits _ _ _ j (by norm_num <;> omega)]
  intro i hi
  have c := Nat.count_le (p:=fun p => (pageMask a).testBit p=true) (n:=2*(i+1))
  change pageBase a + Nat.count (fun p => (pageMask a).testBit p=true) (2*(i+1)) < 1048576
  norm_num at hi
  omega

private theorem prefix_primes (a len : ℕ) (hsmall : len≤16384) (endpt : 16384*a+len≤9041344) :
    bitPrefix (pageMask a) len = Nat.count (fun i => (16384*a+i).Prime) len := by
  simp only [bitPrefix, Nat.count_eq_card_filter_range]
  apply congrArg Finset.card
  apply filter_congr
  intro i hi
  have inside := mem_range.mp hi
  exact pageMask_bit a i (by omega) (by omega)

private theorem base_count (a : ℕ) (ha : a<552) :
    pageBase a = Nat.count Nat.Prime (16384*a) := by
  induction a with
  | zero => decide +kernel
  | succ a ih =>
    have next := (baseEntry a (by omega)).2.resolve_left (by omega)
    rw [next, page_prefix a 8191 (by omega) (by decide), ih (by omega),
      Nat.mul_succ 16384 a, Nat.count_add]
    apply congrArg (Nat.count Nat.Prime (16384*a) + ·)
    exact prefix_primes a 16384 (by decide) (by omega)

def rankOdd (k : ℕ) := lane (rankPage (k/8192)) (k%8192)

theorem rankOdd_correct (k : ℕ) (hk : 2*k+1≤9041343) :
    rankOdd k = Nat.primeCounting (2*k+1) := by
  let a := k/8192
  let j := k%8192
  have ha : a<552 := by dsimp [a]; omega
  have hj : j<8192 := by dsimp [j]; omega
  have split : 2*k+1+1 = 16384*a + 2*(j+1) := by dsimp [a,j]; omega
  change lane (rankPage a) j = Nat.count Nat.Prime (2*k+1+1)
  rw [page_prefix _ _ ha hj, base_count _ ha, split, Nat.count_add]
  apply congrArg (Nat.count Nat.Prime (16384*a) + ·)
  exact prefix_primes a _ (by omega) (by omega)

end Astra247824.Compact

/- Dense page selector backed by the procedural sieve. -/
namespace Astra247824.DenseRank
abbrev rankPage := Astra247824.Compact.rankPage
end Astra247824.DenseRank

/- Look up a prime-count rank at either an even or an odd endpoint. -/
namespace Astra247824.DenseRank
/- Each packed digit is an inclusive rank at the odd argument 2*k+1. -/
def oddRank (k : ℕ) : ℕ :=
  (rankPage (k/8192) >>> (20*(k%8192))) % 2^20

/- Inclusive rank at an arbitrary argument. Only the exceptional even prime
2 needs special handling. -/
def denseRank (n : ℕ) := if n<3 then n/2 else oddRank ((n-1)/2)

theorem primeCounting_odd (n : ℕ) (hn : 3≤n) :
    Nat.primeCounting n = Nat.primeCounting (2*((n-1)/2)+1) := by
  let k := (n-1)/2
  change Nat.primeCounting n = Nat.primeCounting (2*k+1)
  have either : n=2*k+1 ∨ n=2*k+2 := by dsimp [k]; omega
  rcases either with single | even
  · rw [single]
  · rw [even]
    change Nat.count Nat.Prime ((2*k+2)+1) = Nat.count Nat.Prime (2*k+2)
    apply Nat.count_succ_eq_count_iff.mpr
    rw [show 2*k+2 = 2*(k+1) by omega, Nat.prime_mul_iff]
    omega

end Astra247824.DenseRank

/- The page-based rank oracle agrees with Mathlib throughout the required range. -/
namespace Astra247824.DenseRank
theorem denseRank_correct {n : ℕ} (hn : n≤9041343) : denseRank n=Nat.primeCounting n := by
  by_cases tiny : n<3
  · interval_cases n <;> decide +kernel
  · rw [denseRank, if_neg tiny, primeCounting_odd n (by omega)]
    exact Astra247824.Compact.rankOdd_correct ((n-1)/2) (by omega)
end Astra247824.DenseRank

/- Certified indexed lookup for every prime at the cutoff. Each prime occupies sixteen bits. -/

namespace Astra247824.Table

private def row : ℕ → ℕ
  | 0 => 0x2cf02c502bd02b302ab02a502a102950293028d0287028302810277026b02690265025f025902570251024b0241023b02390233022d0223021d020b020901fd01f701f301eb01e701df01d301cf01cd01c901c101bb01b701b101af01a501a301990191018d0185017f017b0175016f01670161015d015b0151014b013d0139013701330125011b01190115010f010d0107010100fb00f100ef00e900e500e300df00d300c700c500c100bf00b500b300ad00a700a3009d00970095008b00890083007f0071006d006b00670065006100590053004f004900470043003d003b0035002f002b00290025001f001d001700130011000d000b0007000500030002
  | 1 => 0x653064d064906470641063d062f062b0623061f06170611060d060705fb05f305e705db05d505d105cf05cb05c905bf05b305ad05ab05a7059f059905950593058f058105770565055d05570551052f05290527051b051705150511050b0509050304ff04fd04eb04e104d504cf04cd04c704c104bd04b104a904a3049d0493048b0481047f04690463045d0455044f044904450443043f042d04270425041b0419040f0409040703fd03fb03f503f103e503df03d703d103cb03c703b903b303ad03a903a10397038f038b037703730371036d035f035b035903550347033d033b03370335032b0329031d03130305030102f902f502ef02e702e302dd02d7
  | 2 => 0xa610a570a490a3d0a390a310a210a1f0a1309fd09f709f509ef09eb09e309d909c709ad09a909a3099b098f0989098509770971096b095f09590955094f094d094909430935092f092b09250923091d0907090508f908f508ef08e908e108dd08db08cb08c308bf08bd08ad08a5089f089b088308710869085f085d0859085308510841083f083308290827082308210815080f080507f707ed07eb07e107db07d307cf07cd07c907c307bb07b5079f079d078d078b07790773076d0761075707550751074f074b074507370727071f0713070906fd06fb06f706f106df06d906d306cd06c506bb06b906ad06a306a1069d06850683067f06790665065b0655
  | 3 => 0xe570e4b0e3b0e350e2f0e270e210e1d0e170e090dff0dfd0df30de70de50ddb0dd50dd30dcd0dc90dc70dbd0db70dab0da30d8d0d8b0d870d850d810d790d690d550d4f0d3f0d3d0d2d0d2b0d210d1f0d130d0f0d030d010cfb0cf70cf10ceb0ce50ce30cc70cbb0cb90cb50cb30c9d0c950c910c890c830c770c730c6d0c610c5f0c5b0c410c310c2f0c250c110c0b0c070bfb0bf50be90be10bdd0bcf0bcb0bc30bb90bb70b9b0b990b930b8d0b890b7b0b6f0b650b5d0b570b510b470b3f0b2d0b290b230b1b0b150b110b030af30af10aed0ae70ae50ad90acf0ac10abd0ab50aab0aa90a9f0a990a970a930a8b0a850a810a7f0a7b0a750a6f0a670a63
  | 4 => 0x128f127d127912731271125f12531247124112371231122b12291223121f121d120d11fb11f511ef11e711d711d111c511c311ab11a711a511a1119b118d11831181116f11691163115f1159114711451139112d11271115110b110510fd10f310f110e710c910c110bb10b110af10a510a3109d1093109110871085107b1079107310691051103f103d1039102b10251021101f100f10030ffd0ffb0fef0fe90fd90fd30fd10fbb0fb50fb30fad0fa70fa30fa10f950f7f0f6b0f670f5b0f590f530f4f0f4d0f470f430f310f290f250f170f0d0f0b0f070ef90eef0eed0edb0ed50ed10ec30eb90eb70eb10e9b0e950e8f0e870e7d0e750e710e6b0e5d0e59
  | 5 => 0x16d916d316cf16c316bd16b516af16a9169f169716931675166f166d16691655164f1645163d163916331625161b161916151613160f1609160715f715d715cd15c515c115bb15b5159b15971591158f1583157f157d156b15671565155f154915431541153d1537152b15291525151f15171511150b150514e714e314d514cb14bd14b714b114a1149f1499148d14751471146f146b1459144d1445143b1433142f1421141b13ff13f913f313ed13eb13df13d913d513c313bb13af139f139d13931391138b13871381137b136d13691367135d1357134f1349134513431337132d13271319130d130712fd12df12d112cd12c112bf12b912b512b312af1297
  | 6 => 0x1b3b1b371b311b2f1b251b231b051aff1afb1af31ae31ad71ad51acf1ac91ab91ab11aad1aab1aa71a931a891a871a7d1a7b1a6b1a691a511a4d1a3f1a351a2f1a2d1a231a211a171a111a051a0319fd19ed19db19cf19c719b519b119ab19a919a319991997199319811979195b19511949194519331931191b191518fd18f518eb18e518df18d918d718d118c718c118b918b318ad18a7189d189b188f1885187f187d1877187118671855184d18491843183b18371835181d1813180717ff17f517f317e917e117d517cb17c917bf17b917b317a5179f179b1795178d177b17771763175d1741173317271723170f170916f916f716ed16eb16e516e116db
  | 7 => 0x1fe11fd31fbb1fb51faf1fa51f9d1f991f971f911f851f7b1f751f671f511f4b1f491f391f1b1f0f1f0d1f011efd1ef71eef1ee31edd1ecb1ec71ec51ec11ebb1ead1ea11e951e8f1e891e711e6d1e4f1e4d1e491e3d1e2f1e2b1e251e171e131e0b1e071e011df91df51de11ddb1dd71dc51db71db31da71da51d9f1d991d951d891d871d7d1d7b1d751d711d691d631d5d1d531d4b1d411d3f1d391d351d231d211d1b1d091cf91cf31ce11cc91cb71cb51ca51ca31c991c8d1c8b1c811c731c551c4f1c4b1c451c3d1c331c2d1c2b1c271c191c131c091bf71bef1bd91bd71bd11bc51bbf1ba71b9d1b911b831b7f1b731b6b1b651b591b551b4f1b471b41
  | 8 => 0x245f244d24432441243d242924192417240b240523f923f323ef23e323dd23d523c923c523bf23b123ad23a72395238f2383236b2363235923532351234523352333232f23292327230b2309230322f722ed22e522e122db22bd22b722a3229f229d229122872285227f2275227322672263224f224b22392231222b22252221221b220f2209220321fb21f521f121e921e521dd21d721c721c121b521b321af21a1219721952185217d2173215f215b2159214f2149214121352113210d20ff20fb20ef20ed20e720e320c520c320b920b120ab20a12089207d2077206920652063205f2051204d20472033202d20292027201d201b20111fff1ff31feb1fe7
  | 9 => 0x28db28d928d528c128bd28bb289f28972881287528672861285d285b28512849283f283d28312821281f281b2813280d2807280327ef27e327d127c527c127b927b327af27a7279d279b2795277f27772773276d276b275f27552753274d273727352719271726f526ef26dd26d526cb26c926c326b326ad269f269b268f26832681267b266f2669266526592653264b263f263b2635262926272615260f260b260525f925f725e125d925cf25cd25bd25b125ab259f259d25972593258d25812573254f254b2543253d25312527251925132507250124fb24f724f524df24dd24d924d724cd24cb24c524bb24b524af24a1249b2485247f247d2479246b2467
  | 10 => 0x2dd32dc72dc52db52db32da92da12d9d2d892d712d652d612d4d2d492d432d3b2d1f2d1d2d072cff2cef2ce92ce32ce12cdb2ccf2ccb2cb72cb32cad2c9f2c932c872c812c772c692c592c572c412c392c352c2f2c232c172c0f2c092bfd2bf92bf32beb2be72bcd2bbd2ba92ba52ba32b992b972b8d2b7b2b6f2b6d2b692b552b4f2b4b2b3f2b3d2b332b312b272b132afb2af12aeb2ae32add2acd2ac52abb2ab92a9d2a972a8b2a892a832a732a6d2a6b2a652a5f2a552a4f2a2f2a252a1d2a132a0129f329ed29e929e329d729d529c329bf29ab29a729a1299b298f298729832975296f29692965295d2947293f2923292129112905290328f728ed28df
  | 11 => 0x326b3263325d325932353229321d32173215320931ff31f731ed31db31d531c731c331b131a9319f31993191317f3173316d31673161315d314b314531433139312d3127312131193109310330fd30fb30ef30e530df30d730d130cb30c730bf30b930a930a3309530913085307d307930713067305b30593055303b303730293023300d30012ff92ff52fed2fe72fdd2fdb2fd12fcf2fc32fb32fab2fa52f832f812f7d2f752f6f2f572f512f4d2f4b2f452f412f292f272f112f0b2f092f052eeb2ee72ed32ecd2ec32ec12eb72eb12ea52ea32e9d2e972e932e852e7f2e792e6f2e5b2e572e3f2e392e372e332e2d2e252e1f2e192e0d2e072e032e012ddf
  | 12 => 0x373f371b37073703370136f736e936e336d136cd36bb36b936af36ad368f368b366d366b366136593653364f364d363b363736353631362336113607360535ef35e735dd35d535c335bf35bd35b735a1359b3599358f358d3581357d357b35773571356f356535513541353b3533352d351d3517350934ff34f134e134d334c934bb34af34a5349d34973491348b3481346d346934633457345534453437341b34193413340f340133fd33f133eb33d333cb33c133b933ad33a333a13383337f33793373336b3367335f335b334733413335332f332b3325330732f932f332ed32e932d132cf32cb32c932b732b332ad32a7329f3299328d327b32773275326f
  | 13 => 0x3be33be13bd73bd13bcb3bc33bb93bb73bad3ba73ba53b9f3b9b3b893b813b7b3b713b5f3b593b533b453b393b2d3b233b213b1b3b113b033afd3af33aeb3ae53ae13ad53acd3ab73aa93aa53a873a793a6d3a673a633a5b3a513a4b3a313a2b3a273a1f3a153a133a0339fb39ef39eb39e539dd39cd39bf39bb39b339af39a739a1399b39953991398b3983397d3979396b395b394d3941393d392f392939253923391d390138ff38e338e138dd38d738d538cf38c938c538b738a73899388f387d3871386f3865385f38573853384b38473841383538333821380b380537f737f337f137df37d537c937ab37a937a3378d377f37753761375d374f37493745
  | 14 => 0x40db40bd40b740b140a940a340914087406d40674061405d40454043403f4031402b40254021401b3ffd3ff13feb3fe93fdd3fd33fcd3fbf3fad3f913f8b3f7d3f793f673f653f5f3f593f413f3d3f3b3f373f0d3f0b3eff3eef3ee73ee13edb3ed73ec93ec53ec33ebf3ebd3eb93ea13e873e813e773e653e633e573e413e333e2f3e293e233e1d3e113e0f3e093e053df33dcf3dc93dc13dbb3db53daf3dab3d9d3d973d913d853d7b3d793d753d733d6f3d433d3f3d373d333d2d3d213d1f3d1b3d193d0d3d033cf73cf13cdf3cdd3cd13cc73cbf3cb53ca73c973c893c853c713c6b3c653c5b3c533c4f3c433c353c293c1f3c173c113c0d3c013bff3bf5
  | 15 => 0x45c745bb45af45ad45a3458f457f457d4577456145554553454945414531452b45134511450544fb44f944db44d744c944bf44bd44ad44ab44a544a1448f4483446f4465445944534451444b4445443f443b442944234417440b440943f943f143ed43eb43e743e143cf43c743bd43b543af43a943a54393438d438b43694357434f43394337433343274325431f430f430742f142e342dd42d342cb42c542b5429d42974291428942854283427d42734261425b425542534243422f42294223421f42194207420541f941f341ef41e741cb41bf41bd41b741ab4193417b4177416b41654159413f413b41354133412141154111410b410940f940f740eb40df
  | 16 => 0x4aef4aed4adb4ad54ac54ac34ab14a8f4a894a874a814a7d4a6b4a5d4a574a454a414a394a234a1d4a0f4a0349e749e549e149df49d349b549ab49974973496d4969496349554945493d4937492b491f4919490d490348f748ef48e548cd48b948a1489b48974879486d486b485b485948554847483d4831481d48194813480b4807480147fb47ed47e147dd47cb47c347bf47b147a54799478947874783477d4771476f475d4751474d474b47394735472f472947234717470f470546f946e546df46d546d346cf46c946c746b146a9469d468d468b4681467f467b4679465d46454643463d4639463346274625461346094603460145f745f545ef45e345d9
  | 17 => 0x4fa94fa54f914f874f854f814f7b4f754f6d4f674f634f494f3f4f2d4f254f194f094f074efb4ee94ed74ed14ecd4ec14eb54eb34eaf4ea14e9b4e954e914e8b4e854e794e674e5f4e534e4f4e3d4e374e354e2b4e1d4e194e174e0b4e054dfb4df94ded4de14dd74dcf4dc94db34db14d9b4d954d8d4d834d814d6b4d654d594d514d414d334d2f4d294d274d1b4d0f4d054cfd4cf34cf14ce74ce14ccd4c994c934c8d4c7f4c794c734c674c614c574c554c4b4c334c2d4c214c1b4c154c0f4c0d4c074c014bf74bf14be94be54be34bdf4bdd4bd94bcb4bbf4bbb4bb54bb34bad4b854b774b6d4b654b594b494b434b3b4b314b254b1f4b134b0d4b0b4b07
  | 18 => 0x549d5491548f5471546d546b5461545f5455545354495441543b54375435541954135411540d53ff53fb53f553f353ef53e953db53b953ab539f53995395538f5387538353815363535d534b5347534553415323531d531552ff52eb52e552db52c952c752c352bb52b152ab52a5529d5297529352815273526d5261524b524552435227521f521b521952155213520951f751f551e351df51d351cb51c151b951a751a351a15197518f5189517951715149514751355125512351175111510d510b510750fb50ef50ed50e350d550c950b750a1509f5093508350775071505350475045503f50355029501d501b50034fff4ffd4fdb4fd94fcf4fbb4fb74faf
  | 19 => 0x599f59995989597b5975595d5957594d594b59455921591b5917590358ff58f958f158df58d558d358c758c158bd58b558ab58a958a35897588d587b5873586f586d585d585b5855582d582b58275815580f580d580357ef57e557d357d157c557b557af57a957a15789577d5777576d5761575f574d57475723571f5713570b57075705570156ff56f356e756d556b156ad569b568f568d5689568356755671566b565f565d564d564b563f56395633562f562356175615560f560b55fd55f355ed55e755d955c955b755b155a9559755855579556f55675563555b5551554f553d5539552b5527551b550d550754fd54f754eb54e954df54d154c554b354a9
  | 20 => 0x5e495e455e395e315e2d5e2b5e275e215e1b5e135e0d5e075dfd5df15deb5ddd5dd75dd35dc75dc15db95dad5da95da35d955d795d6d5d675d655d5b5d555d4f5d475d415d3d5d315d195d175d135d0b5d055cf95ced5cdd5cd75cd15cc95cc35cbf5cbd5ca75c895c875c7d5c775c755c6f5c515c4d5c4b5c475c395c335c2f5c295c1d5c0f5c0b5c095c055bfd5bf35bf15beb5bd55bc95bb15ba35b975b875b795b675b4b5b495b3d5b2b5b255b1f5b195b0f5b015afd5afb5aef5ae55ad35abb5aa95aa35aa15a9d5a955a855a7f5a775a675a5b5a4d5a3b5a2f5a295a1f5a175a135a115a0d5a0159ff59f559f359ed59e959e359db59d159bd59b359b1
  | 21 => 0x63eb63e963d963c563c163b3637f637d63776371636d6367635f634f63436341632f631d6317630d630562ff62fb62e962dd62db62d762d562ad62a5629f629b6295628d62836265625f62536251624b6241623b62276221621d6217620961ff61f161e161cd61c961c761b5619d61936191618b61876179616f615b61576155614b6139612d611b6113610f610960f560e960df60d960cd60bf60bb60ad609d608560796073606b6065605f60536037602f602360115ffb5fe75fe35fd55fcf5fc55fbd5fb35fa15f995f955f7b5f775f655f635f5d5f575f475f3b5f355f335f275f115f095efd5ed95ebb5eb75eaf5ea55e9f5e8b5e855e755e735e695e57
  | 22 => 0x68d768d168c568bd68b1689f689968876871686b68696863685d68596857684d684b6845683f683b6839682d681768116809680367e567df67cd67c167bd67ab6791678567816779676f675b67516745673f673767316727671f67196713670366f566eb66e366d166cd66c566b966b5669b66976695668b6689667d66736661665b664d66476641663b66316629661d6607660165ff65fb65f365e365c565b965ad65a565a16593658f658d657d6571655f65576553654d654b653f6539652f65216511650b64f964f764f164db64c964c764c164ab64a3649f6493648d648564756467645d644f644964436439642b64276421641564096403640163f563ef
  | 23 => 0x6e156e036df76ddb6dcf6dcd6dc36dc16db76db16da56d996d936d7f6d7b6d736d616d5d6d4f6d3f6d396d316d2b6d276d256d0f6d0d6cfd6cf56ceb6ccb6cc76cb36caf6ca96ca16c9b6c976c916c8f6c836c7d6c776c736c676c656c5f6c5b6c596c556c356c316c2b6c296c196c056bff6bef6be16bdb6bbf6bbd6b9f6b956b936b896b876b756b5f6b596b576b416b396b2d6b276b236b116b0f6b056ae76ae16ac96ac16aa36a936a916a8d6a876a7b6a756a696a676a4b6a3d6a376a2b6a0769f769e569e369df69d369c569c169bb69b569b369a36997698969836971696b6965694f694969476943692f69296917690d690b690168ff68ef68ed68e1
  | 24 => 0x730372fd72f572ef72e372d972d772cd72cb72c772b372a3729b7295728f727f72777271726772557243723b722f7225721972177211720771fb71f571ef71e171db71d171cb71c971c371ad71957187718371697163715f715d71597151713371217115710570ff70f970ed70e570cf70c770c370bb70ab70a57091708d708770797075706370577051704f703970337027701f7019700f6ffd6ff76ff56ff16fe96fe36fd76fd36fcd6fcb6fbf6fbb6fb56faf6fa36f9d6f9b6f8f6f856f836f7d6f796f656f616f536f4d6f3d6f2f6f1f6f176f116f0d6efb6ef96ef36ee96ee36ebf6ebd6e9f6e956e936e896e816e7b6e776e756e456e3b6e336e296e17
  | 25 => 0x788b7885788378797877786d786178597853783d7835782b7825780777f977f377ef77e977e177d577cf77c577b977b377ad77a777817771775f775d7759774b77417735772d7721771d771b7705770376f176df76db76c376b776b5769f768b76857673766f766976637655763f763d7633762d7621760f760375fb75f575eb75e575d975d175bb75b975b575a775a1759d75977591758b75897577756b755f754d753d753b7525751f750774fb74e774e174dd74b974b774b174ab74a7749b748d7489747b746b745d7441743f7439742d741b741573f373e773e573df73c973c173bd73ab739f7393738d73857381737f7361735b7357733d732b7321730d
  | 26 => 0x7dd57dcb7dbf7dbd7db77dad7d9f7d8f7d8d7d777d757d637d597d537d4d7d457d3f7d3b7d397d337d1d7d1b7d097d037cf77ced7ce57cdb7cd57ca37c937c8b7c817c737c697c677c497c377c317c1b7c197c077bfd7bf17bef7beb7be97bd37bc77bb37baf7ba97ba17b9b7b8b7b777b717b5f7b557b4f7b3b7b377b357b2b7b1d7b197b177b017af97af57aed7aa57aa17a9f7a9b7a937a7d7a697a657a5f7a597a577a4b7a2d7a277a237a1b7a157a117a0f7a0579ff79f779f379d979d579cf79cd79c979b779b179af79ab79a379937991797379697967795d7957794b793f7939792b79257907790178fb78e578dd78d978d378bf78ad78a178977895
  | 27 => 0x82c782bd82b582b1829382858281827b826f8261824f824982458243823f823382318225821f82158209820781df81c781bb81b381af81a7819d819b8189817f817d815f815981538143813b8131812f811d8119810d810580ff80f580e780e180db80d780cb80c980bd80ad80ab80a58095808f808d80778065804b80478041803f80238021801d8015800f800b80037fed7fcf7fcd7fc97fc37fb57faf7f8d7f877f797f6d7f637f617f5b7f4b7f437f3d7f397f337f317f197f157f137efb7ef77ef17eeb7edf7ed37ebb7eb97ead7ea77e9d7e9b7e917e7d7e797e737e717e6b7e677e617e557e477e437e417e357e2f7e2b7e297e057e017dfb7ded7de9
  | 28 => 0x87c587bb87b387a987a1878f8785877f87778771876b875b875987478735872f872b871f871d871786f586ef86e986d786d186cf86c586c386b786b386a786a586998687867d86758663864d8641863f8639862f86218617860f860985ff85fd85f985eb85e185db85d585d385cd85b785a985a585a38587857b856f856d8563855d8551854f854b850d850984f784f184ef84e384cd84af84a984958491848b8483847784658461844f84478441843b8425842384138411840583ff83ed83e983e783dd83d783d583cb83b983b183a7838f836f83698365835d835783538351834d8341833f83358333832d83298321831b830b82fd82f982f182df82d582cf
  | 29 => 0x8d418d378d298d238d0d8d0b8d018cf38ce98ce38cdd8cc58cb18cad8cab8ca78c9f8c998c8f8c898c818c7b8c6f8c5d8c538c478c3b8c398c278c1d8c178c0b8bff8bfd8bf78be18bdb8bd98bd58bbb8baf8ba98ba38b938b918b5d8b578b218b138b0d8b098b078af58af18ad78ad18acd8acb8ac78ac18ab58ab38aa38a858a798a778a6d8a5f8a5b8a4f8a498a418a358a238a198a0b89ff89fb89f589ef89db89d189cf89c389b989b3899b89958981896389578951894d89458939892d89278923891b8911890b890988fd88f388ed88eb88d388cf88a5889388918885887b8867886188518843883d88378821881f881b8819880387f787dd87cb87c7
  | 30 => 0x92759271926b925792479241922f92219215920391f991f391f191ed91db91d991c991c191bd91bb919d91999185917b916791619151914f9145913d913391279113910390fd90e990df90c590c190b990af909d909b9095908b90859073906d9053904f90439041903b90379031902590239017900d90078ff98fef8fe18fd58fc98fb98fb78fb38fad8fab8f9f8f998f8d8f838f718f698f658f598f538f4b8f458f3f8f2d8f238f1d8f158eff8ef78eeb8ee78edb8ed38ecf8ec78ebd8eb18eaf8eab8e918e8d8e7f8e798e758e738e698e638e518e258e1f8e158e018df78df58ddf8dd98dd38dcb8dc58db58dad8da78d9b8d918d858d798d718d5f8d5b
  | 31 => 0x97d997d397cd97c397b797b197a597939787977f976f975d975b975197499743973997379733972b97259715970f970d96fd96fb96ef96e596d396d196cb96c196a996a796a1969d968f9665963d963b96359631962f961f95f995e995e395cf95bd95b995b795b195ad959f959b958f958995819575955f955d9557954b95399535952d9527952195179509950594e794e194c394b594a5949f9497947b946d946994679463944f944b9445943f94139409940193f793ef93e593dd93d793c793b593b393a793979395937393559343933d933b931f93199311930b930192f392e792d792d592cb92c592c392bf92b992ad92ab92a19299928d92879283927d
  | 32 => 0x9d159d019cfd9cf19ce99ce39cd99cd79cc19cbf9cbb9caf9ca39c9d9c979c7f9c679c659c5f9c4d9c499c359c2f9c2b9c239c119c019bf99bdd9bcf9bcb9bc59bbd9bb79bb19ba79ba19b9f9b959b939b8d9b779b6f9b639b599b519b459b359b2f9b279b1d9b179aff9af79af39aeb9acf9ac79ac39ab79a9d9a919a8b9a7f9a759a619a579a559a4f9a4b9a259a1b9a139a0f99fb99f199e599d799cd99cb99c799bf99af99ad999b999599919985997d9953994999479941993d993b99319929991f9917990d98fb98f998f598e398dd98cf98c998c398bf98b998b198a7988798839881986f986b98519841983b982f98299815980b9809980597f797eb
  | 33 => 0xa28ba289a283a27da279a26ba24da247a243a231a22fa229a223a213a207a1fba1eda1e3a1c5a1c3a1b7a1ada1aba1a5a18da187a17da175a153a141a135a12fa129a11ba111a10fa10ba105a0fda0f3a0f1a0e5a0dfa0dba0d9a0c9a0bda0b7a0b5a0aba09da099a079a075a061a05ba057a04fa03fa039a033a021a00da0019ff59feb9fe59fdf9fc79fc19fb39faf9fa39f959f919f8f9f899f7d9f779f739f6d9f619f539f439f3b9f379f2f9f239f059efb9ef99ef59ebf9ebd9eb39ea19e959e8f9e879e819e6f9e5f9e539e519e479e3b9e339e2d9e279e239e179e0b9df19ded9deb9de79dc39da99da59d9f9d979d619d5b9d559d3d9d319d2d9d27
  | 34 => 0xa759a757a74da745a72da729a723a715a70fa6ffa6f7a6f1a6e7a6dfa6d5a6cfa6cda6c9a6c1a6bba6b5a6aba699a693a691a673a65da651a64ba649a63da625a60da603a5fba5f7a5e9a5e3a5dfa5dda5d9a5d3a5cba5c5a5c1a5a9a5a7a5a3a59da597a58ba585a577a56da561a55ba553a543a53ba535a52ba529a511a4ffa4f3a4efa4eda4e1a4d5a4d1a4cba4c5a4c3a4b9a4ada49ba493a475a469a463a459a457a44da43ba427a423a421a41da40fa3ffa3fda3f1a3e7a3e5a3e1a3dba3d5a3c7a3b7a3afa3a9a3a5a39fa397a387a37ba379a373a355a351a349a331a32ba321a31fa309a301a2f7a2d7a2d1a2c5a2bba2b3a2afa2a9a29ba295a291
  | 35 => 0xa987a985a97fa943a939a937a931a91ba913a907a8fda8e5a8d7a8c7a8c1a8b5a8a9a897a88fa87da86da85fa855a83ba837a82ba829a81da80ba805a7fba7eda7e3a7d7a7d1a7c9a7bfa7b9a7b1a7aba795a793a76fa76ba765
  | _ => 0


private def quickPrime (p : ℕ) :=
  (Astra247824.Compact.pageMask (p/16384)).testBit (p%16384)

private theorem quickPrime_correct (p : ℕ) (hp : p≤43399) : quickPrime p = true ↔ p.Prime := by
  have index : 16384*(p/16384)+p%16384=p := by omega
  have h := Astra247824.Compact.pageMask_bit (p/16384) (p%16384)
    (Nat.mod_lt _ (by decide)) (by omega)
  simpa only [quickPrime, index] using h

/- Zero-based lookup; only indices less than 4525 are used. -/
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
def primeAt (i : ℕ) : ℕ := ((row (i/128)) >>> (16*(i%128))) % 65536

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private def entryOK (i : ℕ) : Bool :=
  if 4525 ≤ i then true else
    let p := primeAt i
    (2 ≤ p && p ≤ 43399 && quickPrime p) &&
      (4525 ≤ i+1 || p < primeAt (i+1))

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private def block : ℕ → ℕ → Bool
  | 0, i => entryOK i
  | k+1, i => block k i && block k (i+2^k)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem blockAt {k i j : ℕ} (h : block k i = true) (lo : i ≤ j) (hi : j < i+2^k) :
    entryOK j = true := by
  induction k generalizing i with
  | zero =>
    simp only [pow_zero] at hi
    have e : j=i := by omega
    subst j
    exact h
  | succ k ih =>
    have ⟨left,right⟩ := Bool.and_eq_true_iff.mp h
    rw [pow_succ] at hi
    by_cases h' : j < i+2^k
    · exact ih left lo h'
    · exact ih right (by omega) (by omega)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check0 : block 7 0 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check1 : block 7 128 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check2 : block 7 256 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check3 : block 7 384 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check4 : block 7 512 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check5 : block 7 640 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check6 : block 7 768 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check7 : block 7 896 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check8 : block 7 1024 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check9 : block 7 1152 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check10 : block 7 1280 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check11 : block 7 1408 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check12 : block 7 1536 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check13 : block 7 1664 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check14 : block 7 1792 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check15 : block 7 1920 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check16 : block 7 2048 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check17 : block 7 2176 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check18 : block 7 2304 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check19 : block 7 2432 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check20 : block 7 2560 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check21 : block 7 2688 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check22 : block 7 2816 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check23 : block 7 2944 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check24 : block 7 3072 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check25 : block 7 3200 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check26 : block 7 3328 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check27 : block 7 3456 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check28 : block 7 3584 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check29 : block 7 3712 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check30 : block 7 3840 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check31 : block 7 3968 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check32 : block 7 4096 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check33 : block 7 4224 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check34 : block 7 4352 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem check35 : block 7 4480 = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem checked (j : Fin 36) : block 7 (128*j.val) = true := by
  fin_cases j
  · exact check0
  · exact check1
  · exact check2
  · exact check3
  · exact check4
  · exact check5
  · exact check6
  · exact check7
  · exact check8
  · exact check9
  · exact check10
  · exact check11
  · exact check12
  · exact check13
  · exact check14
  · exact check15
  · exact check16
  · exact check17
  · exact check18
  · exact check19
  · exact check20
  · exact check21
  · exact check22
  · exact check23
  · exact check24
  · exact check25
  · exact check26
  · exact check27
  · exact check28
  · exact check29
  · exact check30
  · exact check31
  · exact check32
  · exact check33
  · exact check34
  · exact check35

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
private theorem spec (i : Fin 4525) :
    (primeAt i.val).Prime ∧ primeAt i.val ≤ 43399 ∧
      (i.val+1 < 4525 → primeAt i.val < primeAt (i.val+1)) := by
  let j : Fin 36 := ⟨i.val/128, by omega⟩
  have h := blockAt (checked j) (j:=i.val) (by dsimp [j]; omega) (by dsimp [j]; omega)
  have hi := i.isLt
  simp only [entryOK, if_neg (by omega : ¬4525 ≤ i.val), Bool.and_eq_true_iff,
    Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hp,hy⟩,hm⟩,hs⟩ := h
  exact ⟨(quickPrime_correct _ hy).mp hm,hy,fun hlt => hs.resolve_left (by omega)⟩

/- With the separately verified prime count, the table enumerates exactly the official list. -/
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
theorem agrees (hc : (Nat.primesLE 43399).card = 4525) :
    List.ofFn (fun i : Fin 4525 => primeAt i.val) =
      (List.range 43400).filter (fun p => decide p.Prime) := by
  let l := List.ofFn (fun i : Fin 4525 => primeAt i.val)
  let r := (List.range 43400).filter (fun p => decide p.Prime)
  change l = r
  have asc : StrictMono (fun i : Fin 4525 => primeAt i.val) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    exact (spec i.castSucc).2.2 (by simp; omega)
  have hl : l.Pairwise (· < ·) := List.pairwise_ofFn.mpr asc
  have hr : r.Pairwise (· < ·) := List.pairwise_lt_range.filter _
  have incl : l.toFinset ⊆ Nat.primesLE 43399 := by
    intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hp)
    exact Nat.mem_primesLE.mpr ⟨(spec i).2.1,(spec i).1⟩
  have eq : l.toFinset = Nat.primesLE 43399 := Finset.eq_of_subset_of_card_le incl (by
    have len : l.length = 4525 := List.length_ofFn
    rw [List.toFinset_card_of_nodup hl.nodup, hc, len])
  apply List.Perm.eq_of_pairwise (le := (· < ·)) (fun _ _ _ _ h₁ h₂ => by omega) hl hr
  apply (List.perm_ext_iff_of_nodup hl.nodup hr.nodup).mpr
  intro x
  rw [← List.mem_toFinset, eq]
  simp [r, Nat.mem_primesLE]
  omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
def rawPrimeWord (i : ℕ) := row i

end Astra247824.Table

theorem Astra247824.cutoff : (Nat.primesLE 43399).card = 4525 := by
  rw [Nat.primesLE_card_eq_primeCounting, ← Astra247824.DenseRank.denseRank_correct (n:=43399) (by decide)]
  decide +kernel

/- Exact correction from boundary ranks in an indexed prime table. -/

namespace Astra247824.Leaves

open Finset

/- A candidate upper-bound index needs only the two adjoining list entries. -/
def brackets (f : ℕ → ℕ) (n z j : ℕ) : Prop :=
  j ≤ n ∧ (j = 0 ∨ f (j-1) ≤ z) ∧ (j = n ∨ z < f j)

private theorem ofBrackets {f : ℕ → ℕ} {n z j : ℕ}
    (sorted : ∀ i < n, ∀ k < n, i < k → f i < f k) (h : brackets f n z j) :
    ∀ i < n, f i ≤ z ↔ i < j := by
  obtain ⟨bound, prev, next⟩ := h
  intro i hi
  constructor
  · intro fi
    by_contra! ij
    have jn : j < n := by omega
    have fj := next.resolve_left jn.ne
    rcases eq_or_lt_of_le ij with eq | lt
    · subst i; omega
    · have := sorted j jn i hi lt; omega
  · intro ij
    have gt : j ≠ 0 := by omega
    have fj := prev.resolve_left gt
    have jj : j-1 < n := by omega
    rcases (show i ≤ j-1 by omega).eq_or_lt with eq | lt
    · simpa only [eq] using fj
    · exact (sorted i hi (j-1) jj lt).le.trans fj

private theorem index_injective {f : ℕ → ℕ} {n : ℕ}
    (sorted : ∀ i < n, ∀ k < n, i < k → f i < f k) :
    ∀ i ∈ range n, ∀ j ∈ range n, f i = f j → i=j := by
  intro i hi j hj eq
  rcases lt_trichotomy i j with lt | same | gt
  · exact ((sorted i (mem_range.mp hi) j (mem_range.mp hj) lt).ne eq).elim
  · exact same
  · exact ((sorted j (mem_range.mp hj) i (mem_range.mp hi) gt).ne eq.symm).elim

private theorem rank_prefix {f : ℕ → ℕ} {n y z j : ℕ}
    (sorted : ∀ i < n, ∀ k < n, i < k → f i < f k)
    (complete : (range n).image f = Nat.primesLE y)
    (bound : j ≤ n) (belowCut : ∀ i < n, f i ≤ z ↔ i < j) :
    Nat.primeCounting (min y z) = j := by
  have image : (range j).image f = Nat.primesLE (min y z) := by
    ext p
    constructor
    · intro hp
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
      have ij := mem_range.mp hi
      have inn : i < n := ij.trans_le bound
      have pm : f i ∈ Nat.primesLE y := complete ▸ mem_image_of_mem f (mem_range.mpr inn)
      obtain ⟨fy, prime⟩ := Nat.mem_primesLE.mp pm
      exact Nat.mem_primesLE.mpr ⟨le_min fy ((belowCut i inn).mpr ij),prime⟩
    · intro hp
      obtain ⟨both, prime⟩ := Nat.mem_primesLE.mp hp
      obtain ⟨py,pz⟩ := le_min_iff.mp both
      have py' : p ∈ (range n).image f := complete.symm ▸ Nat.mem_primesLE.mpr ⟨py, prime⟩
      obtain ⟨i, hi, rfl⟩ := mem_image.mp py'
      exact mem_image.mpr ⟨i, mem_range.mpr ((belowCut i (mem_range.mp hi)).mp pz), rfl⟩
  rw [← Nat.primesLE_card_eq_primeCounting, ← image, card_image_of_injOn, card_range]
  intro i hi k hk eq
  exact index_injective sorted i (mem_range.mpr ((mem_range.mp hi).trans_le bound))
    k (mem_range.mpr ((mem_range.mp hk).trans_le bound)) eq

/- Evaluate the rank-independent correction using one certified upper-bound
index per row of the short prime table. -/
theorem offset_indices (x y n : ℕ) (f upper : ℕ → ℕ)
    (sorted : ∀ i < n, ∀ k < n, i < k → f i < f k)
    (complete : (range n).image f = Nat.primesLE y)
    (caps : ∀ i < n, brackets f n (easyLower x (f i)) (upper i)) :
    easyOffset x y (fun z => (Nat.primeCounting z : ℤ)) =
      ∑ i ∈ range n, ((n-upper i : ℕ) : ℤ) * (1-(i : ℤ)) := by
  have countY : Nat.primeCounting y = n := by
    rw [← Nat.primesLE_card_eq_primeCounting, ← complete, card_image_of_injOn, card_range]
    exact index_injective sorted
  unfold easyOffset
  rw [← complete, Finset.sum_image (index_injective sorted)]
  apply sum_congr rfl
  intro i hi
  have inn := mem_range.mp hi
  have pm : f i ∈ Nat.primesLE y := complete ▸ mem_image_of_mem f hi
  obtain ⟨fy, prime⟩ := Nat.mem_primesLE.mp pm
  have prior : Nat.primeCounting (f i-1) = i := by
    have belowCut : ∀ k < n, f k ≤ f i-1 ↔ k < i := by
      intro k kn
      have pos := prime.pos
      constructor
      · intro less
        rcases lt_trichotomy k i with lt | same | gt
        · exact lt
        · subst k; omega
        · have := sorted i inn k kn gt; omega
      · intro less
        have := sorted k kn i inn less
        omega
    simpa only [min_eq_right ((Nat.sub_le _ _).trans fy)] using
      rank_prefix sorted complete inn.le belowCut
  have cutoff := caps i inn
  dsimp only
  rw [primeFiber_card, countY, rank_prefix sorted complete cutoff.1 (ofBrackets sorted cutoff), prior]


theorem easyPairCount_indices (x y n : ℕ) (f upper : ℕ → ℕ)
    (sorted : ∀ i < n, ∀ k < n, i < k → f i < f k)
    (complete : (range n).image f = Nat.primesLE y)
    (caps : ∀ i < n, brackets f n (easyLower x (f i)) (upper i)) :
    ((orderedPairs x y).card : ℤ) = ∑ i ∈ range n, ((n-upper i : ℕ) : ℤ) := by
  have countY : Nat.primeCounting y = n := by
    rw [← Nat.primesLE_card_eq_primeCounting, ← complete, card_image_of_injOn, card_range]
    exact index_injective sorted
  rw [orderedPairs, Finset.card_sigma, Nat.cast_sum, ← complete, Finset.sum_image (index_injective sorted)]
  apply sum_congr rfl
  intro i hi
  have cutoff := caps i (mem_range.mp hi)
  rw [primeFiber_card, countY, rank_prefix sorted complete cutoff.1 (ofBrackets sorted cutoff)]


namespace EasyNumerics


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private def middle : Array ℕ := #[
  4509, 4386, 4289, 4135, 4112, 4077, 4028, 4015, 3965, 3934, 3920, 3882, 3793, 3777, 3732, 3480, 3432, 3398,
  3343, 3233, 3177, 3087, 3069, 3056, 3032, 2998, 2958, 2936, 2922, 2892, 2829, 2777, 2767, 2749, 2738, 2724,
  2699, 2637, 2582, 2545, 2491, 2463, 2448, 2421, 2387, 2370, 2339, 2323, 2269, 2252, 2229, 2225, 2210, 2184,
  2176, 2158, 2129, 2059, 2039, 2027, 2022, 1944, 1933, 1928, 1899, 1865, 1861, 1831, 1808, 1792, 1772, 1756,
  1708, 1690, 1680, 1675, 1650, 1628, 1599, 1581, 1545, 1514, 1500, 1489, 1485, 1475, 1471, 1452, 1425, 1412,
  1400, 1372, 1368, 1337, 1336, 1298, 1288, 1274, 1266, 1258, 1254, 1249, 1233, 1227, 1210, 1206, 1190, 1170,
  1151, 1144, 1127, 1124, 1116, 1114, 1102, 1082, 1078, 1059, 1057, 1048, 1045, 1042, 1027, 1018, 998, 970,
  966, 956, 945, 930, 928, 926, 916, 902, 900, 893, 886, 880, 872, 869, 856, 855, 836, 832,
  830, 822, 818, 811, 799, 793, 790, 787, 783, 781, 777, 765, 759, 756, 742, 738, 736, 725,
  720, 712, 708, 693, 682, 675, 668, 665, 659, 657, 654, 641, 634, 633, 622, 617, 615, 607,
  599, 595, 593, 591, 589, 585, 580, 576, 575, 574, 572, 566, 565, 564, 560, 556, 554, 549,
  546, 542, 535, 529, 524, 522, 521, 519, 518, 510, 503, 500, 498, 492, 489, 487, 480, 478,
  474, 470, 467, 462, 461, 455, 449, 446, 446, 445, 443, 434, 434
]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private def upper (i : ℕ) : ℕ :=
  if i < 202 then 4525 else if i < 431 then middle[i-202]! else i+1

open Finset
open Astra247824.Table (primeAt)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private def x : ℕ := 81744924555066

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private def entry (i : ℕ) : Bool :=
  if 4525 ≤ i then true else
    let j := upper i
    let z := easyLower x (primeAt i)
    decide (j ≤ 4525) && (j == 0 || decide (primeAt (j-1) ≤ z)) &&
      (j == 4525 || decide (z < primeAt j))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private def allBlock : ℕ → ℕ → Bool
  | 0, i => entry i
  | k+1, i => allBlock k i && allBlock k (i+2^k)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private theorem atBlock {k i j : ℕ} (h : allBlock k i = true) (lo : i ≤ j) (hi : j < i+2^k) :
    entry j = true := by
  induction k generalizing i with
  | zero =>
    simp only [pow_zero] at hi
    have eq : j=i := by omega
    subst j
    exact h
  | succ k ih =>
    have ⟨left,right⟩ := Bool.and_eq_true_iff.mp h
    rw [pow_succ] at hi
    by_cases low : j < i+2^k
    · exact ih left lo low
    · exact ih right (by omega) (by omega)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private theorem verifiedBrackets : allBlock 13 0 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private theorem everyBracket (i : ℕ) (hi : i<4525) : brackets primeAt 4525 (easyLower x (primeAt i)) (upper i) := by
  have h := atBlock verifiedBrackets (Nat.zero_le i) (show i<0+2^13 by omega)
  simpa only [entry, if_neg (by omega : ¬4525 ≤ i), Bool.and_eq_true_iff, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq, brackets, and_assoc] using h

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private def tree (f : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, i => f i
  | k+1, i => tree f k i + tree f k (i+2^k)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private theorem tree_eq (f : ℕ → ℤ) (k i : ℕ) :
    tree f k i = ∑ j ∈ range (2^k), f (i+j) := by
  induction k generalizing i with
  | zero => simp [tree]
  | succ k ih =>
    rw [tree, ih, ih, pow_succ, Nat.mul_two, Finset.sum_range_add]
    simp only [Nat.add_assoc]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private def padded (f : ℕ → ℤ) (i : ℕ) := if i<4525 then f i else 0

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private theorem paddedTree (f : ℕ → ℤ) : tree (padded f) 13 0 = ∑ i ∈ range 4525, f i := by
  rw [tree_eq]
  simp only [Nat.zero_add]
  calc ∑ i ∈ range (2^13), padded f i = ∑ i ∈ range 4525, padded f i := by
        symm
        apply Finset.sum_subset (Finset.range_mono (by decide))
        intro i _ outside
        exact if_neg (by simpa only [Finset.mem_range] using outside)
       _ = _ := Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private def adjustment (i : ℕ) : ℤ := ((4525-upper i : ℕ) : ℤ)*(1-(i:ℤ))
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private def numPairs (i : ℕ) : ℤ := (4525-upper i : ℕ)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private theorem numericOffset : tree (padded adjustment) 13 0 = -15264628604 := by decide +kernel
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private theorem numericPairs : tree (padded numPairs) 13 0 = 9074711 := by decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private theorem table_cert (count : (Nat.primesLE 43399).card = 4525) :
    (∀ i < 4525, ∀ j < 4525, i < j → primeAt i < primeAt j) ∧
    (range 4525).image primeAt = Nat.primesLE 43399 := by
  have hlist := Astra247824.Table.agrees count
  have asc : StrictMono (fun i : Fin 4525 => primeAt i.val) := List.pairwise_ofFn.mp (by
    rw [hlist]; exact List.pairwise_lt_range.filter _)
  refine ⟨fun i hi j hj less => @asc ⟨i,hi⟩ ⟨j,hj⟩ less, ?_⟩
  ext p
  have pm : p ∈ List.ofFn (fun i : Fin 4525 => primeAt i.val) ↔ p ∈ Nat.primesLE 43399 := by
    rw [hlist, List.mem_filter, Nat.mem_primesLE]
    simp only [List.mem_range, decide_eq_true_eq]
    constructor <;> rintro ⟨h,q⟩ <;> exact ⟨by omega,q⟩
  rw [← pm, List.mem_ofFn, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, hit⟩; exact ⟨⟨i,mem_range.mp hi⟩,hit⟩
  · rintro ⟨i, hit⟩; exact ⟨i.val,mem_range.mpr i.isLt,hit⟩

/- The exact negative correction for the easy subtotal. -/
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem offset_value : easyOffset 81744924555066 43399 (fun n => (Nat.primeCounting n : ℤ)) = -15264628604 := by
  obtain ⟨asc, complete⟩ := table_cert Astra247824.cutoff
  exact (offset_indices x 43399 4525 primeAt upper asc complete everyBracket).trans
    ((paddedTree adjustment).symm.trans numericOffset)

/- The exact number of easy leaves for the H2 instance. -/
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem easy_pair_count : ((orderedPairs 81744924555066 43399).card : ℤ) = 9074711 := by
  obtain ⟨asc, complete⟩ := table_cert Astra247824.cutoff
  exact (easyPairCount_indices x 43399 4525 primeAt upper asc complete everyBracket).trans
    ((paddedTree numPairs).symm.trans numericPairs)

/- After the verified signed offset, only this positive weighted sum of prime
ranks remains for the easy child of the H2 reduction. -/
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem easy_value_iff_rank_sum : easyFlat 81744924555066 43399 = 350834593981 ↔
    (∑ t ∈ arguments 81744924555066 43399,
      (frequency 81744924555066 43399 t : ℤ) * (Nat.primeCounting t : ℤ)) = 366099222585 := by
  have h := easyFlat_grouped 81744924555066 43399 (by decide)
    (fun t => (Nat.primeCounting t : ℤ)) (fun _ _ => ⟨rfl,rfl⟩)
  rw [offset_value] at h
  omega

/- First larger-prime index contributing to row i of the positive sum. -/
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def primeStart (i : ℕ) : ℕ := upper i

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem indexed_primes :
    (∀ i < 4525, ∀ j < 4525, i < j → primeAt i < primeAt j) ∧
      (range 4525).image primeAt = Nat.primesLE 43399 :=
  table_cert Astra247824.cutoff

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem primeStart_spec (i : ℕ) (hi : i < 4525) :
    primeStart i ≤ 4525 ∧ ∀ j < 4525,
      primeAt j ≤ easyLower x (primeAt i) ↔ j < primeStart i :=
  ⟨(everyBracket i hi).1, ofBrackets indexed_primes.1 (everyBracket i hi)⟩

end EasyNumerics

end Astra247824.Leaves

/- Indexed positive subtotal of the easy special leaves. -/
namespace Astra247824.Leaves.EasyNumerics
open Finset
open Astra247824.Table (primeAt)

set_option maxRecDepth 16384 in
private def input : ℕ := 81744924555066

/- Kernel-computable, nonnegative component of the easy special leaves. -/
set_option maxRecDepth 16384 in
def indexPositive (rank : ℕ → ℕ) : ℕ :=
  ∑ i ∈ range 4525, ∑ j ∈ Ico (primeStart i) 4525, rank (input / primeAt i / primeAt j)

set_option maxRecDepth 16384 in
private theorem inj_cutoff : ∀ a ∈ range 4525, ∀ b ∈ range 4525, primeAt a = primeAt b → a=b := by
  intro a ha b hb eq
  have asc := indexed_primes.1
  rcases lt_trichotomy a b with lt | same | gt
  · exact ((asc a (mem_range.mp ha) b (mem_range.mp hb) lt).ne eq).elim
  · exact same
  · exact ((asc b (mem_range.mp hb) a (mem_range.mp ha) gt).ne eq.symm).elim

set_option maxRecDepth 16384 in
private theorem primeFiber_image (i : ℕ) (hi : i<4525) :
    (Ico (primeStart i) 4525).image primeAt = primeFiber input 43399 (primeAt i) := by
  have cut := (primeStart_spec i hi).2
  ext d
  rw [mem_image, primeFiber, mem_filter, ← indexed_primes.2, mem_image]
  constructor
  · rintro ⟨j,hj,rfl⟩
    obtain ⟨lo, high⟩ := mem_Ico.mp hj
    refine ⟨⟨j,mem_range.mpr high,rfl⟩, ?_⟩
    exact lt_of_not_ge (fun bad => (cut j high).mp bad |>.not_ge lo)
  · rintro ⟨⟨j,hj,rfl⟩, low⟩
    have high := mem_range.mp hj
    refine ⟨j, mem_Ico.mpr ⟨?_, high⟩, rfl⟩
    exact le_of_not_gt (fun small => low.not_ge ((cut j high).mpr small))

set_option maxRecDepth 16384 in
private theorem positive_as_pairs (rank : ℕ → ℕ) :
    indexPositive rank = ∑ e ∈ orderedPairs input 43399, rank (pairArgument input e) := by
  unfold indexPositive
  rw [orderedPairs, sum_sigma, ← indexed_primes.2, sum_image inj_cutoff]
  apply sum_congr rfl
  intro i hi
  rw [← primeFiber_image _ (mem_range.mp hi), sum_image]
  · apply sum_congr rfl
    intro j _
    simp only [pairArgument, Nat.div_div_eq_div_mul]
  · intro a ha b hb eq
    exact inj_cutoff a (mem_range.mpr (mem_Ico.mp ha).2) b (mem_range.mpr (mem_Ico.mp hb).2) eq

set_option maxRecDepth 16384 in
private theorem pair_rank_congr (x y limit : ℕ) (rank : ℕ → ℕ)
    (valid : ∀ n≤limit, rank n = Nat.primeCounting n) (cap : x.sqrt≤limit) :
    (∑ e ∈ orderedPairs x y, (rank (pairArgument x e) : ℤ)) =
    ∑ e ∈ orderedPairs x y, (Nat.primeCounting (pairArgument x e) : ℤ) := by
  apply sum_congr rfl
  intro e he
  exact congrArg Int.ofNat (valid _ ((@ordered_rank_arguments x y e he).1.trans cap))

set_option maxRecDepth 16384 in
private theorem fiber_bound (x y p d : ℕ) (pm : p ∈ Nat.primesLE y) (dm : d ∈ primeFiber x y p) :
    x/p/d ≤ x.sqrt := by
  have member : (⟨p,d⟩ : Edge) ∈ orderedPairs x y := mem_sigma.mpr ⟨pm,dm⟩
  simpa only [pairArgument, Nat.div_div_eq_div_mul] using (@ordered_rank_arguments x y ⟨p,d⟩ member).1

set_option maxRecDepth 16384 in
private theorem input_sqrt : Nat.sqrt input ≤ 9041289 := Nat.le_of_lt_succ <| Nat.sqrt_lt.mpr (by decide +kernel)

/- The exact numerical target after replacing all primes and both row
boundaries by certified indexed lookups. -/
set_option maxRecDepth 16384 in
theorem easy_value_iff_indexPositive
    (rank : ℕ → ℕ) (valid : ∀ n ≤ 9041289, rank n = Nat.primeCounting n) :
    easyFlat 81744924555066 43399 = 350834593981 ↔ indexPositive rank = 366099222585 := by
  have ordered := easyFlat_ordered 81744924555066 43399 (by decide)
    (fun n => (Nat.primeCounting n : ℤ)) (fun _ _ => ⟨rfl,rfl⟩)
  have pos := positive_as_pairs rank
  change indexPositive rank = ∑ e ∈ orderedPairs 81744924555066 43399,
    rank (pairArgument 81744924555066 e) at pos
  have val : (indexPositive rank : ℤ) =
      ∑ e ∈ orderedPairs 81744924555066 43399, (Nat.primeCounting (pairArgument 81744924555066 e) : ℤ) := by
    rw [pos, Nat.cast_sum]
    exact pair_rank_congr 81744924555066 43399 9041289 rank valid input_sqrt
  have offset :
      (∑ e ∈ orderedPairs 81744924555066 43399, (1-(Nat.primeCounting (e.1-1):ℤ))) = -15264628604 := by
    rw [← offset_value]
    simp only [orderedPairs, sum_sigma, sum_const, nsmul_eq_mul, easyOffset]
  simp only [orderedTerm, Finset.sum_add_distrib] at ordered
  rw [← val, offset] at ordered
  omega

/- Last rows of the same indexed positive sum, used for independently
checkable proper subtotals. -/
set_option maxRecDepth 16384 in
def tailPositive (a : ℕ) (rank : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Ico a 4525, ∑ j ∈ Ico (primeStart i) 4525, rank (input / primeAt i / primeAt j)

set_option maxRecDepth 16384 in
theorem tailPositive_congr {rank rank' : ℕ → ℕ} (a : ℕ)
    (valid : ∀ n ≤ 9041289, rank n = rank' n) :
    tailPositive a rank = tailPositive a rank' := by
  apply sum_congr rfl
  intro i hi
  have small := (mem_Ico.mp hi).2
  apply sum_congr rfl
  intro j hj
  apply valid
  have large : primeAt j ∈ primeFiber input 43399 (primeAt i) :=
    primeFiber_image i small ▸ mem_image_of_mem primeAt hj
  have pm : primeAt i ∈ Nat.primesLE 43399 :=
    indexed_primes.2 ▸ mem_image_of_mem primeAt (mem_range.mpr small)
  exact (fiber_bound input 43399 (primeAt i) (primeAt j) pm large).trans input_sqrt

end Astra247824.Leaves.EasyNumerics

/- Exact easy child of the public LMO reduction. -/
namespace Astra247824.Leaves.EasyNumerics
open Finset

def officialEasy : Prop :=
  let x := 81744924555066
  let y := 43399
  let edges := ((Icc 1 y).filter Squarefree).sigma (fun d => Nat.primesLE (if d=1 then y else d.minFac-1))
  let leaves := (edges.filter (fun e => ¬ e.1*e.2 ≤ y)).filter (fun e => x/(e.1*e.2) < e.2^2)
  (∑ e ∈ leaves, (1 + (Nat.primeCounting (x/(e.1*e.2)) : ℤ) - (Nat.primeCounting (e.2-1) : ℤ))) = 350834593981

theorem officialEasy_iff_index (rank : ℕ → ℕ)
    (valid : ∀ n≤9041289, rank n=Nat.primeCounting n) :
    officialEasy ↔ indexPositive rank = 366099222585 := by
  rw [← easy_value_iff_indexPositive rank valid,
    easyFlat_primeCounting 81744924555066 43399 (by decide)] <;> rfl

end Astra247824.Leaves.EasyNumerics

/- Local rank pages for consecutive packed divisors. -/

namespace Astra247824.DenseRank
open Finset

def primeDigit (w i : ℕ) := (w >>> (16*i)) % 65536
def afterDigits (w n : ℕ) := w >>> (16*n)

private theorem afterDigit (w n i : ℕ) :
    primeDigit (afterDigits w n) i = primeDigit w (n+i) := by
  simp only [primeDigit, afterDigits, Nat.shiftRight_add, Nat.mul_add]

private def foldWord (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, w => f (w % 65536) + foldWord f n (w >>> 16)

private theorem foldWord_spec (f : ℕ → ℕ) (n w : ℕ) :
    foldWord f n w = ∑ i ∈ range n, f (primeDigit w i) := by
  induction n generalizing w with
  | zero => simp [foldWord]
  | succ n ih =>
    rw [foldWord, ih, sum_range_succ']
    have eq : ∀ i, primeDigit (w >>> 16) i = primeDigit w (i+1) := by
      intro i
      change primeDigit (afterDigits w 1) i = _
      rw [afterDigit, Nat.add_comm]
    have summed : (∑ i ∈ range n, f (primeDigit (w >>> 16) i)) =
        ∑ i ∈ range n, f (primeDigit w (i+1)) :=
      sum_congr rfl (fun i _ => congrArg f (eq i))
    rw [summed, show primeDigit w 0 = w%65536 by simp [primeDigit]]
    exact Nat.add_comm _ _

def rankPageIndex (v : ℕ) := ((v-1)/2)/8192

def pageLocal (data v : ℕ) :=
  if v<3 then v/2 else (data >>> (20*(((v-1)/2)%8192))) % 2^20

private theorem pageLocal_eq (q v : ℕ) (hp : rankPageIndex v=q) :
    pageLocal (rankPage q) v = denseRank v := by
  subst q
  rfl

/- Carry the most recent rank page while scanning packed divisors. On a
page change the new page is loaded once and reused by subsequent queries. -/
def cached (z : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | n+1, w, a, data =>
    let q := z/(w%65536)
    let b := rankPageIndex q
    if b=a then pageLocal data q + cached z n (w >>> 16) a data
    else let next := rankPage b
         pageLocal next q + cached z n (w >>> 16) b next

theorem cached_spec (z w n a : ℕ) :
    cached z n w a (rankPage a) = ∑ i ∈ range n, denseRank (z/(primeDigit w i)) := by
  rw [← foldWord_spec (fun d => denseRank (z/d)) n w]
  induction n generalizing w a with
  | zero => rfl
  | succ n ih =>
    rw [cached, foldWord]
    dsimp only
    split
    · rename_i same
      rw [ih, pageLocal_eq _ _ same]
    · rw [ih, pageLocal_eq _ _ rfl]

end Astra247824.DenseRank

/- Enumerate the easy-leaf prime divisor intervals in fixed-width blocks. -/

namespace Astra247824.DenseRank
open Finset
open Astra247824.Table (primeAt)
open Astra247824.Leaves.EasyNumerics (primeStart indexed_primes indexPositive)

-- The sixteen-bit cutoff-prime entries are those of the certified PrimeTable.
set_option maxRecDepth 16384 in
def primeWord (i : ℕ) := Astra247824.Table.rawPrimeWord i

set_option maxRecDepth 16384 in
private theorem primeWord_lookup (i : ℕ) :
    primeDigit (primeWord (i/128)) (i%128) = primeAt i := by rfl

set_option maxRecDepth 16384 in
def segmentLo (start c : ℕ) := max start (128*c)
set_option maxRecDepth 16384 in
def segmentHi (c : ℕ) := min 4525 (128*(c+1))

set_option maxRecDepth 16384 in
def cellValue (z start c : ℕ) :=
  let lo := segmentLo start c
  cached z (segmentHi c - lo) (afterDigits (primeWord c) (lo-128*c)) 552 (rankPage 552)

set_option maxRecDepth 16384 in
private theorem shiftedPrimeDigit (w n i : ℕ) :
    primeDigit (afterDigits w n) i = primeDigit w (n+i) := by
  simp only [primeDigit, afterDigits, Nat.shiftRight_add, Nat.mul_add]

set_option maxRecDepth 16384 in
private theorem digitInRange {c lo n i : ℕ} (low : 128*c≤lo) (bound : lo+n≤128*(c+1)) (hi : i<n) :
    primeDigit (afterDigits (primeWord c) (lo-128*c)) i = primeAt (lo+i) := by
  rw [shiftedPrimeDigit, ← primeWord_lookup (lo+i)]
  rw [show (lo+i)/128=c by omega, show (lo+i)%128=lo-128*c+i by omega]

set_option maxRecDepth 16384 in
private theorem cellValue_eq (z start c : ℕ) :
    cellValue z start c = ∑ j ∈ Ico (segmentLo start c) (segmentHi c), denseRank (z/primeAt j) := by
  let lo := segmentLo start c
  let hi := segmentHi c
  by_cases empty : hi≤lo
  · have none : Ico lo hi = ∅ := Ico_eq_empty_of_le empty
    change cached z (hi-lo) _ 552 (rankPage 552) = ∑ j ∈ Ico lo hi, _
    rw [Nat.sub_eq_zero_of_le empty, none, Finset.sum_empty] <;> rfl
  · have A : 128*c≤lo := le_max_right _ _
    have B' : hi≤128*(c+1) := min_le_right _ _
    have C : hi≤4525 := min_le_left _ _
    have dw := fun i (ii : i<hi-lo) => digitInRange (c:=c) (lo:=lo) (n:=hi-lo) A (by omega) ii
    change cached z (hi-lo) _ 552 (rankPage 552) = ∑ j ∈ Ico lo hi, _
    rw [cached_spec, Finset.sum_Ico_eq_sum_range]
    apply sum_congr rfl
    intro i ii
    change denseRank (z / primeDigit (afterDigits (primeWord c) (lo-128*c)) i) =
      denseRank (z / primeAt (lo+i))
    rw [dw i (mem_range.mp ii)]

set_option maxRecDepth 16384 in
private def balance (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, i => f i
  | k+1, i => balance f k i + balance f k (i+2^k)

set_option maxRecDepth 16384 in
private theorem balance_eq (f : ℕ → ℕ) (k i : ℕ) :
    balance f k i = ∑ j ∈ range (2^k), f (i+j) := by
  induction k generalizing i with
  | zero => simp [balance]
  | succ k ih =>
    rw [balance, ih, ih, pow_succ, Nat.mul_two, Finset.sum_range_add]
    simp only [Nat.add_assoc]

set_option maxRecDepth 16384 in
def rowValue (z start : ℕ) : ℕ := balance (fun c => cellValue z start c) 5 0 +
  balance (fun c => cellValue z start c) 2 32

set_option maxRecDepth 16384 in
theorem rowValue_eq (z start : ℕ) :
    rowValue z start = ∑ j ∈ Ico start 4525, denseRank (z/primeAt j) := by
  rw [rowValue, balance_eq, balance_eq]
  change (∑ j ∈ range 32, cellValue z start (0+j)) + (∑ j ∈ range 4, cellValue z start (32+j)) = _
  simp only [Nat.zero_add]
  rw [← Finset.sum_range_add]
  change (∑ c ∈ range 36, cellValue z start c) = _
  have split := Finset.sum_fiberwise_of_maps_to (s:=Ico start 4525) (t:=range 36) (g:=fun j => j/128)
    (fun j hj => mem_range.mpr (by have := (mem_Ico.mp hj).2; omega)) (fun j => denseRank (z/primeAt j))
  rw [← split]
  apply sum_congr rfl
  intro c hc
  rw [cellValue_eq]
  apply sum_congr _ (fun _ _ => rfl)
  ext j
  simp only [mem_Ico, mem_filter, segmentLo, segmentHi, max_le_iff, lt_min_iff]
  omega

set_option maxRecDepth 16384 in
def paddedRow (i : ℕ) :=
  if i<4525 then rowValue (81744924555066 / primeAt i) (primeStart i) else 0

set_option maxRecDepth 16384 in
def rowTree (k i : ℕ) := balance paddedRow k i

set_option maxRecDepth 16384 in
theorem rowTree_sum (k i : ℕ) : rowTree k i = ∑ j ∈ range (2^k), paddedRow (i+j) := balance_eq paddedRow k i

set_option maxRecDepth 16384 in
theorem rowTree_step (k i : ℕ) : rowTree (k+1) i = rowTree k i + rowTree k (i+2^k) := rfl

set_option maxRecDepth 16384 in
theorem rowTree_total : rowTree 13 0 = indexPositive denseRank := by
  rw [rowTree, balance_eq]
  simp only [Nat.zero_add]
  have trunc : (∑ i ∈ range (2^13), paddedRow i) = ∑ i ∈ range 4525, paddedRow i := by
    symm
    apply sum_subset (range_mono (by decide))
    intro i _ outside
    exact if_neg (by simpa only [mem_range] using outside)
  rw [trunc]
  apply sum_congr rfl
  intro i hi
  rw [paddedRow, if_pos (mem_range.mp hi), rowValue_eq] <;> rfl
end Astra247824.DenseRank

/- Exact batched prime-rank addresses and monotone page selection for a row of divisors. -/
namespace Astra247824.EasyReplay.PackedRanks

/- Exact reciprocal division below z*d<C. No approximation is made at an integral quotient. -/
theorem quotient (z d C : ℕ) (hd : 0 < d) (hC : 0 < C) (room : z*d < C) :
    z*((C+d-1)/d)/C = z/d := by
  let r := (C+d-1)/d
  have division := Nat.mod_add_div (C+d-1) d
  have rem := Nat.mod_lt (C+d-1) hd
  have rmin : C ≤ d*r := by dsimp [r]; omega
  have rmax : d*r ≤ C+d-1 := by dsimp [r]; exact Nat.mul_div_le (C+d-1) d
  have below : z*r*d ≤ z*(C+d-1) := by
    rw [Nat.mul_assoc, Nat.mul_comm r d]
    exact Nat.mul_le_mul_left z rmax
  have main : z*r*d < (z+1)*C := by
    have step : z*(C+d-1) ≤ z*C+z*d := by
      rw [← Nat.mul_add]
      exact Nat.mul_le_mul_left z (Nat.sub_le _ _)
    rw [Nat.succ_mul]
    omega
  have high : z+1 ≤ (z/d+1)*d := by
    have := Nat.mod_add_div z d
    have := Nat.mod_lt z hd
    rw [Nat.succ_mul, Nat.mul_comm _ d]
    omega
  have hlt : z*r < (z/d+1)*C := by
    apply Nat.lt_of_mul_lt_mul_right (show z*r*d < ((z/d+1)*C)*d from ?_)
    calc z*r*d < (z+1)*C := main
         _ ≤ ((z/d+1)*d)*C := Nat.mul_le_mul_right C high
         _ = (z/d+1)*C*d := by rw [Nat.mul_assoc, Nat.mul_comm d C, ← Nat.mul_assoc]
  have low : (z/d)*C ≤ z*r := by
    refine Nat.le_of_mul_le_mul_right (show ((z/d)*C)*d ≤ z*r*d from ?_) hd
    calc (z/d)*C*d = (z/d*d)*C := by rw [Nat.mul_assoc, Nat.mul_comm C d, ← Nat.mul_assoc]
         _ ≤ z*C := Nat.mul_le_mul_right C (Nat.div_mul_le_self z d)
         _ ≤ z*(d*r) := Nat.mul_le_mul_left z rmin
         _ = z*r*d := by rw [Nat.mul_comm d r, Nat.mul_assoc]
  exact Nat.le_antisymm (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hC).mpr hlt))
    ((Nat.le_div_iff_mul_le hC).mpr low)

private abbrev B : ℕ := 2^112

def pack : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n+1, f => f 0 + B*pack n (fun i => f (i+1))

def lane (u i : ℕ) := (u/B^i)%B

theorem pack_agree (n : ℕ) (f g : ℕ → ℕ) (h : ∀ i<n, f i=g i) : pack n f=pack n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [pack, pack, h 0 (by omega), ih (fun i => f (i+1)) (fun i => g (i+1)) (fun i hi => h _ (by omega))]

theorem pack_times (n z : ℕ) (f : ℕ → ℕ) :
    z*pack n f = pack n (fun i => z*f i) := by
  induction n generalizing f with
  | zero => simp [pack]
  | succ n ih =>
    rw [pack, pack, Nat.mul_add, Nat.mul_left_comm, ih]

theorem pack_plus (n : ℕ) (f g : ℕ → ℕ) :
    pack n f + pack n g = pack n (fun i => f i+g i) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [pack]
    rw [← ih (fun i => f (i+1)) (fun i => g (i+1)), Nat.mul_add]
    omega

theorem pack_digit (n : ℕ) (f : ℕ → ℕ) (h : ∀ i<n, f i<B) (i : ℕ) (hi : i<n) :
    lane (pack n f) i=f i := by
  induction n generalizing f i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [lane, pack, Nat.mod_eq_of_lt (h 0 (by omega))]
    | succ i =>
      unfold lane
      rw [pack, pow_succ', ←Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by decide),
        Nat.div_eq_of_lt (h 0 (by omega)), Nat.zero_add]
      exact ih _ (fun i hi => h _ (by omega)) i (by omega)

theorem pack_mask (w m n : ℕ) (hm : m<B) :
    w &&& pack n (fun _ => m) = pack n (fun i => lane w i &&& m) := by
  induction n generalizing w with
  | zero => simp [pack]
  | succ n ih =>
    let rest := pack n (fun _ => m)
    have modv : (m+B*rest)%B=m := by rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hm]
    have divv : (m+B*rest)/B=rest := by rw [Nat.add_mul_div_left _ _ (by decide),Nat.div_eq_of_lt hm,Nat.zero_add]
    rw [pack, pack, ← Nat.mod_add_div (w &&& (m+B*rest)) B, Nat.and_mod_two_pow, Nat.and_div_two_pow, modv, divv]
    rw [show (w/B &&& rest) = _ from ih (w/B)]
    simp only [show lane w 0 = w%B by simp [lane]]
    change (w%B &&& m) + B*pack n (fun i => lane (w/B) i &&& m) =
      (w%B &&& m) + B*pack n (fun i => lane w (i+1) &&& m)
    congr 2
    apply pack_agree
    intro i hi
    rw [lane, lane, Nat.div_div_eq_div_mul, pow_succ']

private theorem bit_window (w i skip len : ℕ) (size : skip+len≤112) :
    (lane (w >>> skip) i) % 2^len = ((lane w i) >>> skip) % 2^len := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [lane, ←Nat.pow_mul, ←Nat.shiftRight_eq_div_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]
  by_cases small : j<len
  · have h : j<112 := by omega
    have hs : skip+j<112 := by omega
    simp [small,h,hs,Nat.add_comm,Nat.add_assoc]
  · simp [small]

theorem window_pack (n : ℕ) (f : ℕ → ℕ) (h : ∀ i<n, f i<B) (skip len : ℕ) (size : skip+len ≤112) :
    (pack n f >>> skip) &&& pack n (fun _ => 2^len-1) =
      pack n (fun i => (f i >>> skip) % 2^len) := by
  have bound : 2^len-1<B := by
    have hpower := Nat.pow_le_pow_right (show 0<2 by decide) (show len≤112 by omega)
    change 2^len-1 < 2^112
    omega
  rw [pack_mask _ _ _ bound]
  apply pack_agree
  intro i hi
  rw [Nat.and_two_pow_sub_one_eq_mod, bit_window _ _ _ _ size, pack_digit _ _ h _ hi]

abbrev reciprocalBase : ℕ := 2^64
def reciprocal (d : ℕ) := (reciprocalBase+d-1)/d

def quotients (n z encoded : ℕ) :=
  ((z*encoded) >>> 64) &&& pack n (fun _ => 2^45-1)

theorem quotients_eq (n z : ℕ) (d : ℕ → ℕ) (hz : z<2^40)
    (hd : ∀ i<n, 0<d i ∧ d i<65536) :
    quotients n z (pack n (fun i => reciprocal (d i))) = pack n (fun i => z/d i) := by
  have product {i} (hi : i<n) : z*d i < reciprocalBase :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_of_lt hz) (Nat.le_of_lt (hd i hi).2)) (by decide)
  have fits {i} (hi : i<n) : z*reciprocal (d i) < 2^112 := by
    have denom := (hd i hi).2
    have recBound : reciprocal (d i) ≤ 2^65 := by
      apply Nat.le_trans (Nat.div_le_self _ _)
      change 2^64 + d i - 1 ≤ 2^65
      omega
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_of_lt hz) recBound) (by decide)
  unfold quotients
  rw [pack_times, window_pack _ _ (fun _ hi => fits hi) _ _ (by decide)]
  apply pack_agree
  intro i hi
  rw [Nat.shiftRight_eq_div_pow]
  change (z*((reciprocalBase+d i-1)/d i)/reciprocalBase) % 2^45 = z/d i
  rw [quotient _ _ _ (hd i hi).1 (by decide) (product hi), Nat.mod_eq_of_lt]
  have := Nat.div_le_self z (d i)
  omega

def item (q : ℕ) := 20*(((q-1)/2)%8192) + 2^18*((q-1)/16384)

def items (n qs : ℕ) :=
  let bits := (qs - pack n (fun _ => 1)) >>> 1
  20*(bits &&& pack n (fun _ => 8191)) +
    2^18*((bits >>> 13) &&& pack n (fun _ => 2^27-1))

theorem items_eq (n : ℕ) (q : ℕ → ℕ) (hq : ∀ i<n, 0<q i ∧ q i<2^40) :
    items n (pack n q) = pack n (fun i => item (q i)) := by
  have restore : pack n (fun i => q i-1) + pack n (fun _ => 1) = pack n q := by
    rw [pack_plus]
    apply pack_agree
    intro i hi
    have := (hq i hi).1
    omega
  have sub : pack n q - pack n (fun _ => 1) = pack n (fun i => q i-1) := by omega
  have fits : ∀ i<n, q i-1 < 2^112 := by
    intro i hi
    have := (hq i hi).2
    omega
  simp only [items]
  rw [sub, ← Nat.shiftRight_add]
  rw [show 8191=2^13-1 by decide, window_pack _ _ fits 1 13 (by decide),
    window_pack _ _ fits 14 27 (by decide), pack_times, pack_times, pack_plus]
  apply pack_agree
  intro i hi
  simp only [Nat.shiftRight_eq_div_pow, item]
  have hsmall : (q i-1)/2^14 < 2^27 := by
    apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
    have := (hq i hi).2
    omega
  rw [Nat.mod_eq_of_lt hsmall]
  rfl

/- Each 112-bit lane contains the shift and page of its exact prime-count query. -/
theorem packedAddresses (n z : ℕ) (d : ℕ → ℕ) (lo : 196608 ≤ z) (hi : z<2^40)
    (hd : ∀ i<n, 0<d i ∧ d i<65536) :
    items n (quotients n z (pack n (fun i => reciprocal (d i)))) =
      pack n (fun i => item (z/d i)) := by
  rw [quotients_eq _ _ _ hi hd]
  apply items_eq
  intro i h
  have denom := hd i h
  exact ⟨Nat.div_pos (by omega) denom.1, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hi⟩

def tally : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n+1, f => f 0 + tally n (fun i => f (i+1))

theorem tally_congr (n : ℕ) (f g : ℕ → ℕ) (h : ∀ i<n, f i=g i) :
    tally n f=tally n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [tally,tally,h 0 (by omega),ih (fun i => f (i+1)) (fun i => g (i+1)) (fun i hi => h _ (by omega))]

theorem tally_add (m n : ℕ) (f : ℕ → ℕ) :
    tally (m+n) f=tally m f+tally n (fun i => f (m+i)) := by
  induction m generalizing f with
  | zero => simp [tally]
  | succ m ih =>
    rw [Nat.succ_add,tally,tally,ih,Nat.add_assoc]
    congr 3
    funext i
    rw [Nat.succ_add,Nat.add_one]

def pageAt (w i : ℕ) := (w >>> (112*i+18)) &&& (2^27-1)
def offsetAt (w i : ℕ) := (w >>> (112*i)) &&& (2^18-1)
def readAt (pages : ℕ → ℕ) (w i : ℕ) :=
  (pages (pageAt w i) >>> offsetAt w i) &&& (2^20-1)

private theorem page_drop (w m i : ℕ) :
    pageAt (w >>> (112*m)) i=pageAt w (m+i) := by
  simp only [pageAt, ← Nat.shiftRight_add, Nat.mul_add, Nat.add_assoc]

private theorem offset_drop (w m i : ℕ) :
    offsetAt (w >>> (112*m)) i=offsetAt w (m+i) := by
  simp only [offsetAt, ← Nat.shiftRight_add, Nat.mul_add]

private theorem read_drop (pages : ℕ → ℕ) (w m i : ℕ) :
    readAt pages (w >>> (112*m)) i=readAt pages w (m+i) := by
  simp only [readAt,page_drop,offset_drop]

def plain (page : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, w => ((page >>> (w &&& (2^18-1))) &&& (2^20-1)) + plain page n (w >>> 112)

private theorem plain_spec (n page w : ℕ) :
    plain page n w=tally n (fun i => (page >>> offsetAt w i) &&& (2^20-1)) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [plain,tally,ih]
    simp only [show offsetAt w 0 = w &&& (2^18-1) by simp [offsetAt]]
    congr 1
    apply tally_congr
    intro i _
    rw [show 112=112*1 by decide,offset_drop,Nat.add_comm 1]

def cover (pages : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, w => readAt pages w 0
  | k+1, w =>
    let h := 1 <<< k
    let p := pageAt w 0
    if p=pageAt w (2*h-1) then plain (pages p) (2*h) w
    else cover pages k w + cover pages k (w >>> (112*h))

theorem cover_spec (pages : ℕ → ℕ) (k w : ℕ)
    (desc : ∀ i j, i≤j → j<2^k → pageAt w j≤pageAt w i) :
    cover pages k w=tally (2^k) (readAt pages w) := by
  induction k generalizing w with
  | zero => simp [cover,tally]
  | succ k ih =>
    let h := 2^k
    have hp : 0<h := Nat.two_pow_pos _
    have hk : 2^(k+1)=2*h := by rw [pow_succ']
    rw [hk] at desc ⊢
    simp only [cover, Nat.shiftLeft_eq, Nat.one_mul]
    change (if pageAt w 0=pageAt w (2*h-1) then _ else _) = _
    split
    · rename_i same
      rw [plain_spec]
      apply tally_congr
      intro i hi
      have upper := desc 0 i (by omega) hi
      have lower := desc i (2*h-1) (by omega) (by omega)
      rw [show pageAt w 0=pageAt w i by omega]
      rfl
    · have first : ∀ i j, i≤j → j<h → pageAt w j≤pageAt w i :=
        fun i j hij hj => desc i j hij (by omega)
      have last : ∀ i j, i≤j → j<h → pageAt (w >>> (112*h)) j≤pageAt (w >>> (112*h)) i := by
        intro i j hij hj
        rw [page_drop,page_drop]
        exact desc _ _ (by omega) (by omega)
      rw [ih _ first, ih _ last]
      rw [show 2*h=h+h by omega, tally_add]
      congr 1
      apply tally_congr
      intro i _
      exact read_drop _ _ _ _

private theorem lane_window (w i skip len : ℕ) (size : skip+len≤112) :
    (w >>> (112*i+skip))%2^len = ((lane w i) >>> skip)%2^len := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [lane, ←Nat.pow_mul, ←Nat.shiftRight_eq_div_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]
  by_cases small : j<len
  · have hs : skip+j<112 := by omega
    simp [small,hs,Nat.add_assoc]
  · simp [small]

private theorem payload_page (n : ℕ) (f : ℕ → ℕ) (bound : ∀ i<n, f i<2^45) (i : ℕ) (hi : i<n) :
    pageAt (pack n f) i=f i/2^18 := by
  have small : f i/2^18 < 2^27 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0<2^18)).mpr (bound i hi)
  rw [pageAt,Nat.and_two_pow_sub_one_eq_mod,lane_window _ _ _ _ (by decide),
    pack_digit _ _ (fun j hj => Nat.lt_trans (bound j hj) (by decide)) _ hi,Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt small]

private theorem payload_offset (n : ℕ) (f : ℕ → ℕ) (bound : ∀ i<n, f i<2^45) (i : ℕ) (hi : i<n) :
    offsetAt (pack n f) i=f i%2^18 := by
  rw [offsetAt,Nat.and_two_pow_sub_one_eq_mod]
  rw [show 112*i=112*i+0 by omega,lane_window _ _ _ _ (by decide),
    pack_digit _ _ (fun j hj => Nat.lt_trans (bound j hj) (by decide)) _ hi,Nat.shiftRight_zero]

theorem packedLookup (pages : ℕ → ℕ) (k : ℕ) (f : ℕ → ℕ)
    (bound : ∀ i<2^k, f i<2^45)
    (desc : ∀ i j, i≤j → j<2^k → f j/2^18≤f i/2^18) :
    cover pages k (pack (2^k) f)=
      tally (2^k) (fun i => (pages (f i/2^18) >>> (f i%2^18)) &&& (2^20-1)) := by
  rw [cover_spec]
  · apply tally_congr
    intro i hi
    rw [readAt,payload_page _ _ bound i hi,payload_offset _ _ bound i hi]
  · intro i j hij hj
    rw [payload_page _ _ bound j hj,payload_page _ _ bound i (by omega)]
    exact desc _ _ hij hj

def groupRank (pages : ℕ → ℕ) (k z encoded : ℕ) :=
  cover pages k (items (2^k) (quotients (2^k) z encoded))

def pairRank (pages : ℕ → ℕ) (q : ℕ) :=
  (pages ((q-1)/16384) >>> (20*(((q-1)/2)%8192))) % 2^20

private theorem lowBound (q : ℕ) : 20*(((q-1)/2)%8192) < 2^18 := by
  have := Nat.mod_lt ((q-1)/2) (by decide : 0 < 8192)
  omega

private theorem itemBound (q : ℕ) (h : q<2^40) : item q<2^45 := by
  have := lowBound q
  unfold item
  omega

private theorem itemPage (q : ℕ) : item q/2^18=(q-1)/16384 := by
  rw [item, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (lowBound q), Nat.zero_add]

private theorem itemOffset (q : ℕ) : item q%2^18=20*(((q-1)/2)%8192) := by
  rw [item,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (lowBound q)]

/- For any increasing block of divisors, one packed reciprocal multiplication and a page split
    give the sum of the same individual rank queries. -/
theorem groupRank_eq (pages : ℕ → ℕ) (k z : ℕ) (d : ℕ → ℕ) (lo : 196608 ≤ z)
    (hi : z<2^40) (hd : ∀ i<2^k, 0<d i ∧ d i<65536)
    (increasing : ∀ i j, i≤j → j<2^k → d i≤d j) :
    groupRank pages k z (pack (2^k) (fun i => reciprocal (d i))) =
      tally (2^k) (fun i => pairRank pages (z/d i)) := by
  rw [groupRank,packedAddresses _ _ _ lo hi hd,packedLookup]
  · apply tally_congr
    intro i _
    rw [itemPage,itemOffset,Nat.and_two_pow_sub_one_eq_mod,pairRank]
  · intro i _
    exact itemBound _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hi)
  · intro i j hij hj
    rw [itemPage,itemPage]
    exact Nat.div_le_div_right (Nat.sub_le_sub_right
      (Nat.div_le_div_left (increasing i j hij hj) (hd i (by omega)).1) 1)

end Astra247824.EasyReplay.PackedRanks

/- Specialize the packed rank calculation to the certified 128-prime words of A247824. -/
namespace Astra247824.DenseRank

open Finset
open Astra247824.Table (primeAt)
open Astra247824.EasyReplay.PackedRanks

set_option maxRecDepth 16384 in
private theorem allIncreasing : StrictMono (fun i : Fin 4525 => primeAt i.val) := by
  have sorted : (List.ofFn (fun i : Fin 4525 => primeAt i.val)).Pairwise (· < ·) := by
    rw [Astra247824.Table.agrees Astra247824.cutoff]
    exact List.pairwise_lt_range.filter _
  exact List.pairwise_ofFn.mp sorted

set_option maxRecDepth 16384 in
private theorem tableBound (i : Fin 4525) : 0<primeAt i.val ∧ primeAt i.val<65536 := by
  have member : primeAt i.val ∈ List.ofFn (fun j : Fin 4525 => primeAt j.val) :=
    List.mem_ofFn.mpr ⟨i,rfl⟩
  rw [Astra247824.Table.agrees Astra247824.cutoff] at member
  have h := List.mem_filter.mp member
  have hp : (primeAt i.val).Prime := of_decide_eq_true h.2
  have := List.mem_range.mp h.1
  exact ⟨hp.pos,by omega⟩

set_option maxRecDepth 16384 in
private theorem wordAt (c i : ℕ) (hi : i<128) :
    primeDigit (primeWord c) i=primeAt (128*c+i) := by
  have h : primeDigit (primeWord ((128*c+i)/128)) ((128*c+i)%128)=primeAt (128*c+i) := rfl
  rw [show (128*c+i)/128=c by omega,show (128*c+i)%128=i by omega] at h
  exact h

set_option maxRecDepth 16384 in
def reciprocalWord (w : ℕ) := pack 128 (fun i => reciprocal (primeDigit w i))

set_option maxRecDepth 16384 in
private def mask45 : {x : ℕ // pack 128 (fun _ => 2^45-1)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 16384 in
private def rankMask13 : {x : ℕ // pack 128 (fun _ => 8191)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 16384 in
private def mask27 : {x : ℕ // pack 128 (fun _ => 2^27-1)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 16384 in
private def ones112 : {x : ℕ // pack 128 (fun _ => 1)=x} := ⟨_,by conv => lhs; whnf⟩

set_option maxRecDepth 16384 in
private def ranks128 (z r : ℕ) :=
  let qs := ((z*r) >>> 64) &&& mask45.val
  let bits := (qs-ones112.val) >>> 1
  cover rankPage 7 (20*(bits &&& rankMask13.val) + 2^18*((bits >>> 13) &&& mask27.val))

set_option maxRecDepth 16384 in
private theorem ranks128_eq (z r : ℕ) : ranks128 z r=groupRank rankPage 7 z r := by
  unfold ranks128 groupRank items quotients
  rw [←mask45.property,←ones112.property,←rankMask13.property,←mask27.property]
  rfl

set_option maxRecDepth 16384 in
private theorem tally_range (n : ℕ) (f : ℕ → ℕ) : tally n f=∑ i ∈ range n, f i := by
  induction n generalizing f with
  | zero => simp [tally]
  | succ n ih =>
    rw [tally, ih, sum_range_succ']
    exact Nat.add_comm _ _

set_option maxRecDepth 16384 in
def packedCell (z enc fallback : ℕ) :=
  if 196608≤z ∧ z<2^40 then ranks128 z enc else fallback

set_option maxRecDepth 16384 in
theorem packedCell_eq (z c enc fallback : ℕ) (hc : c<35)
    (encode : reciprocalWord (primeWord c)=enc)
    (old : fallback = ∑ i ∈ range 128, denseRank (z/primeAt (128*c+i))) :
    packedCell z enc fallback=fallback := by
  by_cases zone : 196608≤z ∧ z<2^40
  · rw [packedCell, if_pos zone, ranks128_eq, ← encode, reciprocalWord]
    have bound (i : ℕ) (hi : i<128) :
        0<primeDigit (primeWord c) i ∧ primeDigit (primeWord c) i<65536 := by
      rw [wordAt _ _ hi]
      exact tableBound ⟨_,by omega⟩
    have asc (i j : ℕ) (hij : i≤j) (hj : j<128) :
        primeDigit (primeWord c) i≤primeDigit (primeWord c) j := by
      rw [wordAt _ _ (by omega),wordAt _ _ hj]
      exact allIncreasing.monotone (show (⟨128*c+i,by omega⟩ : Fin 4525)≤⟨128*c+j,by omega⟩ by
        change 128*c+i≤128*c+j
        omega)
    rw [show 128=2^7 by decide,groupRank_eq rankPage 7 _ _ zone.1 zone.2 bound asc,tally_range,old,
      show 2^7=128 by decide]
    apply sum_congr rfl
    intro i hi
    have i128 : i<128 := mem_range.mp hi
    have d := bound i i128
    have qlarge : 3≤z/primeDigit (primeWord c) i :=
      (Nat.le_div_iff_mul_le d.1).mpr (by omega)
    rw [←wordAt c i i128,denseRank,if_neg (by omega)]
    simp only [pairRank, oddRank, Nat.div_div_eq_div_mul]
  · rw [packedCell,if_neg zone]

end Astra247824.DenseRank

/- Unrolled full prime blocks for individual easy-leaf rows. -/
namespace Astra247824.DenseRank
open Finset
open Astra247824.Table (primeAt)
/- Start a fresh block at the page of its first quotient. -/
def fresh (z : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, w =>
    let q := z/(w%65536)
    let b := rankPageIndex q
    let data := rankPage b
    pageLocal data q + cached z n (w >>> 16) b data

private theorem fresh_eq_at (z n w a : ℕ) :
    fresh z n w = cached z n w a (rankPage a) := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [fresh,cached]
    dsimp only
    split
    · rename_i same
      rw [same]
    · rfl



private theorem halfQuot (z d : ℕ) : (z-d)/(2*d)=((z/d)-1)/2 := by
  by_cases zero : d=0
  · subst d; simp
  have pos : 0<d := by omega
  rw [Nat.mul_comm 2 d, ← Nat.div_div_eq_div_mul]
  by_cases fits : d≤z
  · have parts : (z-d)+d=z := Nat.sub_add_cancel fits
    have quot := Nat.add_div_right (z-d) pos
    rw [parts] at quot
    rw [quot]; simp
  · rw [Nat.sub_eq_zero_of_le (by omega), Nat.div_eq_of_lt (by omega : z<d)]
    simp

private theorem mask16 (v : ℕ) : v &&& 65535 = v % 65536 :=
  Nat.and_two_pow_sub_one_eq_mod v 16
private theorem mask13 (v : ℕ) : v &&& 8191 = v % 8192 :=
  Nat.and_two_pow_sub_one_eq_mod v 13
private theorem mask20 (v : ℕ) : v &&& 1048575 = v % 2^20 :=
  Nat.and_two_pow_sub_one_eq_mod v 20

def thin (z : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | n+1, w, a, data =>
    let d := w &&& 65535
    let k := (z-d)/(2*d)
    let b := k >>> 13
    let sh := 20*(k &&& 8191)
    if b=a then ((data >>> sh) &&& 1048575) + thin z n (w >>> 16) a data
    else let next := rankPage b
         ((next >>> sh) &&& 1048575) + thin z n (w >>> 16) b next

private theorem div13 (k : ℕ) : k >>> 13 = k/8192 := by rw [Nat.shiftRight_eq_div_pow]

private theorem thin_eq (z n w a : ℕ) (hz : 196608 ≤ z) :
    thin z n w a (rankPage a) = cached z n w a (rankPage a) := by
  induction n generalizing w a with
  | zero => rfl
  | succ n ih =>
    rw [thin, cached]
    simp only [mask16, halfQuot, mask13, mask20, div13]
    let q := z/(w%65536)
    let b := rankPageIndex q
    let sh := 20*(((q-1)/2)%8192)
    change (if b=a then ((rankPage a >>> sh) % 2^20) + thin z n (w >>> 16) a (rankPage a) else
      ((rankPage b >>> sh) % 2^20) + thin z n (w >>> 16) b (rankPage b)) =
      (if b=a then pageLocal (rankPage a) q + cached z n (w >>> 16) a (rankPage a) else
       pageLocal (rankPage b) q + cached z n (w >>> 16) b (rankPage b))
    have atRank : ((rankPage b >>> sh) % 2^20) = pageLocal (rankPage b) q := by
      by_cases zero : w%65536 = 0
      · have q0 : q=0 := by simp [q,zero]
        dsimp only [b,sh]
        rw [q0]
        decide +kernel
      · have hd := Nat.mod_lt w (by decide : 0<65536)
        have high : 3≤q := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
        simp [pageLocal,Nat.not_lt.mpr high,sh]
    by_cases same : b=a
    · subst a
      simp only [atRank,ih]
    · simp only [if_neg same,atRank,ih]
private theorem thin_seed (z n w : ℕ) :
    thin z n w (z+1) 0 = thin z n w (z+1) (rankPage (z+1)) := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [thin]
    have div := Nat.div_le_self (z-(w &&& 65535)) (2*(w &&& 65535))
    have shrink := Nat.div_le_self ((z-(w &&& 65535))/(2*(w &&& 65535))) 8192
    have bound := Nat.sub_le z (w &&& 65535)
    have diff : (z-(w &&& 65535))/(2*(w &&& 65535))/8192 ≠ z+1 := by omega
    simp only [div13, if_neg diff]

def speedFresh (z n w : ℕ) :=
  if 196608 ≤ z then thin z n w (z+1) 0 else fresh z n w

private theorem speedFresh_eq (z n w : ℕ) : speedFresh z n w = fresh z n w := by
  by_cases hz : 196608 ≤ z
  · rw [speedFresh,if_pos hz,thin_seed,thin_eq _ _ _ _ hz,←fresh_eq_at]
  · rw [speedFresh,if_neg hz]

private theorem cellEq (z lo c : ℕ) (low : 128*c ≤ lo) (high : lo ≤ segmentHi c) :
    speedFresh z (segmentHi c - lo) (primeWord c >>> (16*(lo-128*c))) =
      ∑ j ∈ Ico lo (segmentHi c), denseRank (z/primeAt j) := by
  rw [speedFresh_eq, fresh_eq_at _ _ _ 552, cached_spec, sum_Ico_eq_sum_range]
  apply sum_congr rfl
  intro i hi
  have h := mem_range.mp hi
  have stop := min_le_right 4525 (128*(c+1))
  have endp : lo+i < 128*(c+1) := by unfold segmentHi at *; omega
  change denseRank (z / (((primeWord c >>> (16*(lo-128*c))) >>> (16*i)) % 65536)) = _
  have rep : primeDigit (primeWord ((lo+i)/128)) ((lo+i)%128) = primeAt (lo+i) := rfl
  rw [show (lo+i)/128=c by omega, show (lo+i)%128=lo-128*c+i by omega] at rep
  simp only [primeDigit, Nat.mul_add, Nat.shiftRight_add] at rep ⊢
  rw [rep]

def upperSlice (z lo : ℕ) := ∑ j ∈ Ico lo 4525, denseRank (z/primeAt j)
set_option maxRecDepth 32768 in
private def rec0 : {x : ℕ // reciprocalWord (primeWord 0)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec1 : {x : ℕ // reciprocalWord (primeWord 1)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec2 : {x : ℕ // reciprocalWord (primeWord 2)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec3 : {x : ℕ // reciprocalWord (primeWord 3)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec4 : {x : ℕ // reciprocalWord (primeWord 4)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec5 : {x : ℕ // reciprocalWord (primeWord 5)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec6 : {x : ℕ // reciprocalWord (primeWord 6)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec7 : {x : ℕ // reciprocalWord (primeWord 7)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec8 : {x : ℕ // reciprocalWord (primeWord 8)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec9 : {x : ℕ // reciprocalWord (primeWord 9)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec10 : {x : ℕ // reciprocalWord (primeWord 10)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec11 : {x : ℕ // reciprocalWord (primeWord 11)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec12 : {x : ℕ // reciprocalWord (primeWord 12)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec13 : {x : ℕ // reciprocalWord (primeWord 13)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec14 : {x : ℕ // reciprocalWord (primeWord 14)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec15 : {x : ℕ // reciprocalWord (primeWord 15)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec16 : {x : ℕ // reciprocalWord (primeWord 16)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec17 : {x : ℕ // reciprocalWord (primeWord 17)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec18 : {x : ℕ // reciprocalWord (primeWord 18)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec19 : {x : ℕ // reciprocalWord (primeWord 19)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec20 : {x : ℕ // reciprocalWord (primeWord 20)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec21 : {x : ℕ // reciprocalWord (primeWord 21)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec22 : {x : ℕ // reciprocalWord (primeWord 22)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec23 : {x : ℕ // reciprocalWord (primeWord 23)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec24 : {x : ℕ // reciprocalWord (primeWord 24)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec25 : {x : ℕ // reciprocalWord (primeWord 25)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec26 : {x : ℕ // reciprocalWord (primeWord 26)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec27 : {x : ℕ // reciprocalWord (primeWord 27)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec28 : {x : ℕ // reciprocalWord (primeWord 28)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec29 : {x : ℕ // reciprocalWord (primeWord 29)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec30 : {x : ℕ // reciprocalWord (primeWord 30)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec31 : {x : ℕ // reciprocalWord (primeWord 31)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec32 : {x : ℕ // reciprocalWord (primeWord 32)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec33 : {x : ℕ // reciprocalWord (primeWord 33)=x} := ⟨_,by conv => lhs; whnf⟩
set_option maxRecDepth 32768 in
private def rec34 : {x : ℕ // reciprocalWord (primeWord 34)=x} := ⟨_,by conv => lhs; whnf⟩

private def s36 (_z : ℕ) := 0
private theorem t36 (z : ℕ) : s36 z = upperSlice z 4525 := by simp [s36, upperSlice]

private def s35 (z : ℕ) := speedFresh z 45 (primeWord 35) + s36 z
private theorem t35 (z : ℕ) : s35 z = upperSlice z 4480 := by
  have one := cellEq z 4480 35 (by decide) (by decide)
  change speedFresh z 45 (primeWord 35) = ∑ j ∈ Ico 4480 4525, denseRank (z/primeAt j) at one
  rw [s35,one,t36]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s34 (z : ℕ) := packedCell z rec34.val (speedFresh z 128 (primeWord 34)) + s35 z
private theorem t34 (z : ℕ) : s34 z = upperSlice z 4352 := by
  have one := cellEq z 4352 34 (by decide) (by decide)
  change speedFresh z 128 (primeWord 34) = ∑ j ∈ Ico 4352 4480, denseRank (z/primeAt j) at one
  rw [s34,packedCell_eq z 34 _ _ (by decide) rec34.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t35]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s33 (z : ℕ) := packedCell z rec33.val (speedFresh z 128 (primeWord 33)) + s34 z
private theorem t33 (z : ℕ) : s33 z = upperSlice z 4224 := by
  have one := cellEq z 4224 33 (by decide) (by decide)
  change speedFresh z 128 (primeWord 33) = ∑ j ∈ Ico 4224 4352, denseRank (z/primeAt j) at one
  rw [s33,packedCell_eq z 33 _ _ (by decide) rec33.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t34]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s32 (z : ℕ) := packedCell z rec32.val (speedFresh z 128 (primeWord 32)) + s33 z
private theorem t32 (z : ℕ) : s32 z = upperSlice z 4096 := by
  have one := cellEq z 4096 32 (by decide) (by decide)
  change speedFresh z 128 (primeWord 32) = ∑ j ∈ Ico 4096 4224, denseRank (z/primeAt j) at one
  rw [s32,packedCell_eq z 32 _ _ (by decide) rec32.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t33]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s31 (z : ℕ) := packedCell z rec31.val (speedFresh z 128 (primeWord 31)) + s32 z
private theorem t31 (z : ℕ) : s31 z = upperSlice z 3968 := by
  have one := cellEq z 3968 31 (by decide) (by decide)
  change speedFresh z 128 (primeWord 31) = ∑ j ∈ Ico 3968 4096, denseRank (z/primeAt j) at one
  rw [s31,packedCell_eq z 31 _ _ (by decide) rec31.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t32]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s30 (z : ℕ) := packedCell z rec30.val (speedFresh z 128 (primeWord 30)) + s31 z
private theorem t30 (z : ℕ) : s30 z = upperSlice z 3840 := by
  have one := cellEq z 3840 30 (by decide) (by decide)
  change speedFresh z 128 (primeWord 30) = ∑ j ∈ Ico 3840 3968, denseRank (z/primeAt j) at one
  rw [s30,packedCell_eq z 30 _ _ (by decide) rec30.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t31]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s29 (z : ℕ) := packedCell z rec29.val (speedFresh z 128 (primeWord 29)) + s30 z
private theorem t29 (z : ℕ) : s29 z = upperSlice z 3712 := by
  have one := cellEq z 3712 29 (by decide) (by decide)
  change speedFresh z 128 (primeWord 29) = ∑ j ∈ Ico 3712 3840, denseRank (z/primeAt j) at one
  rw [s29,packedCell_eq z 29 _ _ (by decide) rec29.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t30]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s28 (z : ℕ) := packedCell z rec28.val (speedFresh z 128 (primeWord 28)) + s29 z
private theorem t28 (z : ℕ) : s28 z = upperSlice z 3584 := by
  have one := cellEq z 3584 28 (by decide) (by decide)
  change speedFresh z 128 (primeWord 28) = ∑ j ∈ Ico 3584 3712, denseRank (z/primeAt j) at one
  rw [s28,packedCell_eq z 28 _ _ (by decide) rec28.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t29]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s27 (z : ℕ) := packedCell z rec27.val (speedFresh z 128 (primeWord 27)) + s28 z
private theorem t27 (z : ℕ) : s27 z = upperSlice z 3456 := by
  have one := cellEq z 3456 27 (by decide) (by decide)
  change speedFresh z 128 (primeWord 27) = ∑ j ∈ Ico 3456 3584, denseRank (z/primeAt j) at one
  rw [s27,packedCell_eq z 27 _ _ (by decide) rec27.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t28]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s26 (z : ℕ) := packedCell z rec26.val (speedFresh z 128 (primeWord 26)) + s27 z
private theorem t26 (z : ℕ) : s26 z = upperSlice z 3328 := by
  have one := cellEq z 3328 26 (by decide) (by decide)
  change speedFresh z 128 (primeWord 26) = ∑ j ∈ Ico 3328 3456, denseRank (z/primeAt j) at one
  rw [s26,packedCell_eq z 26 _ _ (by decide) rec26.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t27]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s25 (z : ℕ) := packedCell z rec25.val (speedFresh z 128 (primeWord 25)) + s26 z
private theorem t25 (z : ℕ) : s25 z = upperSlice z 3200 := by
  have one := cellEq z 3200 25 (by decide) (by decide)
  change speedFresh z 128 (primeWord 25) = ∑ j ∈ Ico 3200 3328, denseRank (z/primeAt j) at one
  rw [s25,packedCell_eq z 25 _ _ (by decide) rec25.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t26]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s24 (z : ℕ) := packedCell z rec24.val (speedFresh z 128 (primeWord 24)) + s25 z
private theorem t24 (z : ℕ) : s24 z = upperSlice z 3072 := by
  have one := cellEq z 3072 24 (by decide) (by decide)
  change speedFresh z 128 (primeWord 24) = ∑ j ∈ Ico 3072 3200, denseRank (z/primeAt j) at one
  rw [s24,packedCell_eq z 24 _ _ (by decide) rec24.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t25]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s23 (z : ℕ) := packedCell z rec23.val (speedFresh z 128 (primeWord 23)) + s24 z
private theorem t23 (z : ℕ) : s23 z = upperSlice z 2944 := by
  have one := cellEq z 2944 23 (by decide) (by decide)
  change speedFresh z 128 (primeWord 23) = ∑ j ∈ Ico 2944 3072, denseRank (z/primeAt j) at one
  rw [s23,packedCell_eq z 23 _ _ (by decide) rec23.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t24]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s22 (z : ℕ) := packedCell z rec22.val (speedFresh z 128 (primeWord 22)) + s23 z
private theorem t22 (z : ℕ) : s22 z = upperSlice z 2816 := by
  have one := cellEq z 2816 22 (by decide) (by decide)
  change speedFresh z 128 (primeWord 22) = ∑ j ∈ Ico 2816 2944, denseRank (z/primeAt j) at one
  rw [s22,packedCell_eq z 22 _ _ (by decide) rec22.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t23]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s21 (z : ℕ) := packedCell z rec21.val (speedFresh z 128 (primeWord 21)) + s22 z
private theorem t21 (z : ℕ) : s21 z = upperSlice z 2688 := by
  have one := cellEq z 2688 21 (by decide) (by decide)
  change speedFresh z 128 (primeWord 21) = ∑ j ∈ Ico 2688 2816, denseRank (z/primeAt j) at one
  rw [s21,packedCell_eq z 21 _ _ (by decide) rec21.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t22]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s20 (z : ℕ) := packedCell z rec20.val (speedFresh z 128 (primeWord 20)) + s21 z
private theorem t20 (z : ℕ) : s20 z = upperSlice z 2560 := by
  have one := cellEq z 2560 20 (by decide) (by decide)
  change speedFresh z 128 (primeWord 20) = ∑ j ∈ Ico 2560 2688, denseRank (z/primeAt j) at one
  rw [s20,packedCell_eq z 20 _ _ (by decide) rec20.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t21]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s19 (z : ℕ) := packedCell z rec19.val (speedFresh z 128 (primeWord 19)) + s20 z
private theorem t19 (z : ℕ) : s19 z = upperSlice z 2432 := by
  have one := cellEq z 2432 19 (by decide) (by decide)
  change speedFresh z 128 (primeWord 19) = ∑ j ∈ Ico 2432 2560, denseRank (z/primeAt j) at one
  rw [s19,packedCell_eq z 19 _ _ (by decide) rec19.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t20]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s18 (z : ℕ) := packedCell z rec18.val (speedFresh z 128 (primeWord 18)) + s19 z
private theorem t18 (z : ℕ) : s18 z = upperSlice z 2304 := by
  have one := cellEq z 2304 18 (by decide) (by decide)
  change speedFresh z 128 (primeWord 18) = ∑ j ∈ Ico 2304 2432, denseRank (z/primeAt j) at one
  rw [s18,packedCell_eq z 18 _ _ (by decide) rec18.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t19]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s17 (z : ℕ) := packedCell z rec17.val (speedFresh z 128 (primeWord 17)) + s18 z
private theorem t17 (z : ℕ) : s17 z = upperSlice z 2176 := by
  have one := cellEq z 2176 17 (by decide) (by decide)
  change speedFresh z 128 (primeWord 17) = ∑ j ∈ Ico 2176 2304, denseRank (z/primeAt j) at one
  rw [s17,packedCell_eq z 17 _ _ (by decide) rec17.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t18]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s16 (z : ℕ) := packedCell z rec16.val (speedFresh z 128 (primeWord 16)) + s17 z
private theorem t16 (z : ℕ) : s16 z = upperSlice z 2048 := by
  have one := cellEq z 2048 16 (by decide) (by decide)
  change speedFresh z 128 (primeWord 16) = ∑ j ∈ Ico 2048 2176, denseRank (z/primeAt j) at one
  rw [s16,packedCell_eq z 16 _ _ (by decide) rec16.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t17]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s15 (z : ℕ) := packedCell z rec15.val (speedFresh z 128 (primeWord 15)) + s16 z
private theorem t15 (z : ℕ) : s15 z = upperSlice z 1920 := by
  have one := cellEq z 1920 15 (by decide) (by decide)
  change speedFresh z 128 (primeWord 15) = ∑ j ∈ Ico 1920 2048, denseRank (z/primeAt j) at one
  rw [s15,packedCell_eq z 15 _ _ (by decide) rec15.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t16]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s14 (z : ℕ) := packedCell z rec14.val (speedFresh z 128 (primeWord 14)) + s15 z
private theorem t14 (z : ℕ) : s14 z = upperSlice z 1792 := by
  have one := cellEq z 1792 14 (by decide) (by decide)
  change speedFresh z 128 (primeWord 14) = ∑ j ∈ Ico 1792 1920, denseRank (z/primeAt j) at one
  rw [s14,packedCell_eq z 14 _ _ (by decide) rec14.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t15]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s13 (z : ℕ) := packedCell z rec13.val (speedFresh z 128 (primeWord 13)) + s14 z
private theorem t13 (z : ℕ) : s13 z = upperSlice z 1664 := by
  have one := cellEq z 1664 13 (by decide) (by decide)
  change speedFresh z 128 (primeWord 13) = ∑ j ∈ Ico 1664 1792, denseRank (z/primeAt j) at one
  rw [s13,packedCell_eq z 13 _ _ (by decide) rec13.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t14]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s12 (z : ℕ) := packedCell z rec12.val (speedFresh z 128 (primeWord 12)) + s13 z
private theorem t12 (z : ℕ) : s12 z = upperSlice z 1536 := by
  have one := cellEq z 1536 12 (by decide) (by decide)
  change speedFresh z 128 (primeWord 12) = ∑ j ∈ Ico 1536 1664, denseRank (z/primeAt j) at one
  rw [s12,packedCell_eq z 12 _ _ (by decide) rec12.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t13]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s11 (z : ℕ) := packedCell z rec11.val (speedFresh z 128 (primeWord 11)) + s12 z
private theorem t11 (z : ℕ) : s11 z = upperSlice z 1408 := by
  have one := cellEq z 1408 11 (by decide) (by decide)
  change speedFresh z 128 (primeWord 11) = ∑ j ∈ Ico 1408 1536, denseRank (z/primeAt j) at one
  rw [s11,packedCell_eq z 11 _ _ (by decide) rec11.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t12]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s10 (z : ℕ) := packedCell z rec10.val (speedFresh z 128 (primeWord 10)) + s11 z
private theorem t10 (z : ℕ) : s10 z = upperSlice z 1280 := by
  have one := cellEq z 1280 10 (by decide) (by decide)
  change speedFresh z 128 (primeWord 10) = ∑ j ∈ Ico 1280 1408, denseRank (z/primeAt j) at one
  rw [s10,packedCell_eq z 10 _ _ (by decide) rec10.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t11]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s9 (z : ℕ) := packedCell z rec9.val (speedFresh z 128 (primeWord 9)) + s10 z
private theorem t9 (z : ℕ) : s9 z = upperSlice z 1152 := by
  have one := cellEq z 1152 9 (by decide) (by decide)
  change speedFresh z 128 (primeWord 9) = ∑ j ∈ Ico 1152 1280, denseRank (z/primeAt j) at one
  rw [s9,packedCell_eq z 9 _ _ (by decide) rec9.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t10]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s8 (z : ℕ) := packedCell z rec8.val (speedFresh z 128 (primeWord 8)) + s9 z
private theorem t8 (z : ℕ) : s8 z = upperSlice z 1024 := by
  have one := cellEq z 1024 8 (by decide) (by decide)
  change speedFresh z 128 (primeWord 8) = ∑ j ∈ Ico 1024 1152, denseRank (z/primeAt j) at one
  rw [s8,packedCell_eq z 8 _ _ (by decide) rec8.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t9]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s7 (z : ℕ) := packedCell z rec7.val (speedFresh z 128 (primeWord 7)) + s8 z
private theorem t7 (z : ℕ) : s7 z = upperSlice z 896 := by
  have one := cellEq z 896 7 (by decide) (by decide)
  change speedFresh z 128 (primeWord 7) = ∑ j ∈ Ico 896 1024, denseRank (z/primeAt j) at one
  rw [s7,packedCell_eq z 7 _ _ (by decide) rec7.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t8]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s6 (z : ℕ) := packedCell z rec6.val (speedFresh z 128 (primeWord 6)) + s7 z
private theorem t6 (z : ℕ) : s6 z = upperSlice z 768 := by
  have one := cellEq z 768 6 (by decide) (by decide)
  change speedFresh z 128 (primeWord 6) = ∑ j ∈ Ico 768 896, denseRank (z/primeAt j) at one
  rw [s6,packedCell_eq z 6 _ _ (by decide) rec6.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t7]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s5 (z : ℕ) := packedCell z rec5.val (speedFresh z 128 (primeWord 5)) + s6 z
private theorem t5 (z : ℕ) : s5 z = upperSlice z 640 := by
  have one := cellEq z 640 5 (by decide) (by decide)
  change speedFresh z 128 (primeWord 5) = ∑ j ∈ Ico 640 768, denseRank (z/primeAt j) at one
  rw [s5,packedCell_eq z 5 _ _ (by decide) rec5.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t6]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s4 (z : ℕ) := packedCell z rec4.val (speedFresh z 128 (primeWord 4)) + s5 z
private theorem t4 (z : ℕ) : s4 z = upperSlice z 512 := by
  have one := cellEq z 512 4 (by decide) (by decide)
  change speedFresh z 128 (primeWord 4) = ∑ j ∈ Ico 512 640, denseRank (z/primeAt j) at one
  rw [s4,packedCell_eq z 4 _ _ (by decide) rec4.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t5]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s3 (z : ℕ) := packedCell z rec3.val (speedFresh z 128 (primeWord 3)) + s4 z
private theorem t3 (z : ℕ) : s3 z = upperSlice z 384 := by
  have one := cellEq z 384 3 (by decide) (by decide)
  change speedFresh z 128 (primeWord 3) = ∑ j ∈ Ico 384 512, denseRank (z/primeAt j) at one
  rw [s3,packedCell_eq z 3 _ _ (by decide) rec3.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t4]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s2 (z : ℕ) := packedCell z rec2.val (speedFresh z 128 (primeWord 2)) + s3 z
private theorem t2 (z : ℕ) : s2 z = upperSlice z 256 := by
  have one := cellEq z 256 2 (by decide) (by decide)
  change speedFresh z 128 (primeWord 2) = ∑ j ∈ Ico 256 384, denseRank (z/primeAt j) at one
  rw [s2,packedCell_eq z 2 _ _ (by decide) rec2.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t3]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s1 (z : ℕ) := packedCell z rec1.val (speedFresh z 128 (primeWord 1)) + s2 z
private theorem t1 (z : ℕ) : s1 z = upperSlice z 128 := by
  have one := cellEq z 128 1 (by decide) (by decide)
  change speedFresh z 128 (primeWord 1) = ∑ j ∈ Ico 128 256, denseRank (z/primeAt j) at one
  rw [s1,packedCell_eq z 1 _ _ (by decide) rec1.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t2]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def s0 (z : ℕ) := packedCell z rec0.val (speedFresh z 128 (primeWord 0)) + s1 z
private theorem t0 (z : ℕ) : s0 z = upperSlice z 0 := by
  have one := cellEq z 0 0 (by decide) (by decide)
  change speedFresh z 128 (primeWord 0) = ∑ j ∈ Ico 0 128, denseRank (z/primeAt j) at one
  rw [s0,packedCell_eq z 0 _ _ (by decide) rec0.property (by simpa only [sum_Ico_eq_sum_range] using one),one,t1]
  exact sum_Ico_consecutive _ (by decide) (by decide)

private def suffix (z : ℕ) : ℕ → ℕ
  | 0 => s0 z
  | 1 => s1 z
  | 2 => s2 z
  | 3 => s3 z
  | 4 => s4 z
  | 5 => s5 z
  | 6 => s6 z
  | 7 => s7 z
  | 8 => s8 z
  | 9 => s9 z
  | 10 => s10 z
  | 11 => s11 z
  | 12 => s12 z
  | 13 => s13 z
  | 14 => s14 z
  | 15 => s15 z
  | 16 => s16 z
  | 17 => s17 z
  | 18 => s18 z
  | 19 => s19 z
  | 20 => s20 z
  | 21 => s21 z
  | 22 => s22 z
  | 23 => s23 z
  | 24 => s24 z
  | 25 => s25 z
  | 26 => s26 z
  | 27 => s27 z
  | 28 => s28 z
  | 29 => s29 z
  | 30 => s30 z
  | 31 => s31 z
  | 32 => s32 z
  | 33 => s33 z
  | 34 => s34 z
  | 35 => s35 z
  | _ => 0

private theorem suffix_spec (z c : ℕ) (hc : c ≤ 35) :
    suffix z c = upperSlice z (128*c) := by
  interval_cases c
  · exact t0 z
  · exact t1 z
  · exact t2 z
  · exact t3 z
  · exact t4 z
  · exact t5 z
  · exact t6 z
  · exact t7 z
  · exact t8 z
  · exact t9 z
  · exact t10 z
  · exact t11 z
  · exact t12 z
  · exact t13 z
  · exact t14 z
  · exact t15 z
  · exact t16 z
  · exact t17 z
  · exact t18 z
  · exact t19 z
  · exact t20 z
  · exact t21 z
  · exact t22 z
  · exact t23 z
  · exact t24 z
  · exact t25 z
  · exact t26 z
  · exact t27 z
  · exact t28 z
  · exact t29 z
  · exact t30 z
  · exact t31 z
  · exact t32 z
  · exact t33 z
  · exact t34 z
  · exact t35 z

def quickRow (z start : ℕ) :=
  let c := start/128
  let n := min 4525 (128*(c+1))-start
  speedFresh z n ((primeWord c) >>> (16*(start%128))) + suffix z (c+1)

theorem quickRow_spec (z start : ℕ) (hs : start ≤ 4525) :
    quickRow z start = upperSlice z start := by
  let c := start/128
  have low : 128*c ≤ start := by dsimp [c]; omega
  have stop : start ≤ segmentHi c := by dsimp [c,segmentHi]; omega
  have hc : c ≤ 35 := by dsimp [c]; omega
  have eq := cellEq z start c low stop
  have mod : start%128=start-128*c := by dsimp [c]; omega
  change speedFresh z (segmentHi c-start) ((primeWord c) >>> (16*(start%128))) + suffix z (c+1) = _
  rw [mod,eq]
  by_cases last : c=35
  · rw [last]
    change (∑ j ∈ Ico start 4525, _) + 0 = _
    rfl
  · rw [suffix_spec z (c+1) (by omega)]
    have hi : segmentHi c = 128*(c+1) := by dsimp [segmentHi]; omega
    rw [hi]
    exact sum_Ico_consecutive _ (by omega) (by omega)
theorem quickRow_eq (z start : ℕ) (hs : start ≤ 4525) : quickRow z start = rowValue z start :=
  (quickRow_spec z start hs).trans (rowValue_eq z start).symm

end Astra247824.DenseRank

/- Check literal row parameters separately from the numerical rank sum. -/
namespace Astra247824.DenseRank
open Finset Astra247824.Leaves.EasyNumerics
open Astra247824.Table (primeAt)

def rowArgsOk (i z s : ℕ) :=
  if i<4525 then z==81744924555066 / primeAt i && s==primeStart i
  else s==4525

private theorem rowArgs_sound {i z s : ℕ} (good : rowArgsOk i z s = true) :
    quickRow z s = paddedRow i := by
  by_cases hi : i<4525
  · simp only [rowArgsOk,if_pos hi,Bool.and_eq_true,beq_iff_eq] at good
    rw [paddedRow, if_pos hi, good.1, good.2]
    exact quickRow_eq _ _ (primeStart_spec i hi).1
  · simp only [rowArgsOk,if_neg hi,beq_iff_eq] at good
    rw [paddedRow,if_neg hi,good,quickRow_spec z 4525 (by omega)]
    simp [upperSlice]

def validRows : ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | i, (z,s)::ds => rowArgsOk i z s && validRows (i+1) ds

def quickTotal : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (z,s)::ds => quickRow z s + quickTotal ds

private theorem batch_sum (ds : List (ℕ × ℕ)) (i : ℕ) (ok : validRows i ds = true) :
    quickTotal ds = ∑ j ∈ range ds.length, paddedRow (i+j) := by
  induction ds generalizing i with
  | nil => simp [quickTotal]
  | cons e ds ih =>
    rcases e with ⟨z,s⟩
    simp only [validRows,Bool.and_eq_true] at ok
    rw [quickTotal, rowArgs_sound ok.1, ih (i+1) ok.2, List.length_cons, sum_range_succ']
    simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]
    exact Nat.add_comm _ _

theorem certifiedBatch (ds : List (ℕ × ℕ)) (i k : ℕ) (length : ds.length = 2^k)
    (ok : validRows i ds = true) : rowTree k i = quickTotal ds := by
  rw [rowTree_sum,←length]
  exact (batch_sum ds i ok).symm
end Astra247824.DenseRank

/- A 32-bit digit records each row's claimed subtotal. The kernel checks rows separately. -/
namespace Astra247824.DenseRank

private def digitSum : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, w => w%4294967296 + digitSum n (w >>> 32)

private theorem nextValue (r : ℕ×ℕ) (rs : List (ℕ×ℕ)) (w : ℕ)
    (head : quickRow r.1 r.2=w%4294967296)
    (tail : quickTotal rs=digitSum rs.length (w >>> 32)) :
    quickTotal (r::rs)=digitSum (r::rs).length w := by
  rcases r with ⟨z,s⟩
  exact congrArg₂ (·+·) head tail

def recordedBatch (ds : List (ℕ×ℕ)) (i w : ℕ)
    (length : ds.length=2^4 := by decide)
    (valid : validRows i ds=true := by decide +kernel)
    (evidence : quickTotal ds=digitSum ds.length w := by
      repeat' (apply nextValue; · decide +kernel)
      rfl) : {n : ℕ // rowTree 4 i=n} :=
  ⟨digitSum ds.length w,(certifiedBatch ds i 4 length valid).trans evidence⟩

end Astra247824.DenseRank

/- Numerical positive contributions of the ordered smaller-prime rows. -/



namespace Astra247824.DenseRank

private theorem glueRows {k i j a b v : ℕ} (idx : i+2^k=j) (l : rowTree k i=a)
    (r : rowTree k j=b) (sum : a+b=v) : rowTree (k+1) i=v := by
  rw [rowTree_step,idx,l,r,sum]

private theorem beyond_cutoff (k i : ℕ) (hi : 4525 ≤ i) : rowTree k i = 0 := by
  induction k generalizing i with
  | zero => change paddedRow i = 0; exact if_neg (by omega)
  | succ k ih => rw [rowTree_step, ih i hi, ih (i+2^k) (hi.trans (Nat.le_add_right i (2^k))), Nat.zero_add]



private def d_s_4_0 : List (ℕ × ℕ) := [(40872462277533,4525),(27248308185022,4525),(16348984911013,4525),(11677846365009,4525),(7431356777733,4525),(6288071119620,4525),(4808524973827,4525),(4302364450266,4525),(3554127154568,4525),(2818790501898,4525),(2636933050163,4525),(2209322285272,4525),(1993778647684,4525),(1901044757094,4525),(1739253713937,4525),(1542357067076,4525)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_0 := recordedBatch d_s_4_0 0 0x0

private def d_s_4_16 : List (ℕ × ℕ) := [(1385507195848,4525),(1340080730410,4525),(1220073500821,4525),(1151336965564,4525),(1119793487055,4525),(1034745880443,4525),(984878609097,4525),(918482298371,4525),(842731180980,4525),(809355688664,4525),(793640044223,4525),(763971257523,4525),(749953436285,4525),(723406411991,4525),(643660823268,4525),(624007057672,4525)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_16 := recordedBatch d_s_4_16 16 0x0

private theorem s_5_0 : rowTree 5 0 = 0 := by
  exact glueRows (by decide) s_4_0.property s_4_16.property (by decide)

private def d_s_4_32 : List (ℕ × ℕ) := [(596678281423,4525),(588092982410,4525),(548623654731,4525),(541357116258,4525),(520668309267,4525),(501502604632,4525),(489490566198,4525),(472514014769,4525),(456675556173,4525),(451629417431,4525),(427983898194,4525),(423548831891,4525),(414948855609,4525),(410778515352,4525),(387416704052,4525),(366569168408,4525)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_32 := recordedBatch d_s_4_32 32 0x0

private def d_s_4_48 : List (ℕ × ℕ) := [(360109799802,4525),(356964736048,4525),(350836586073,4525),(342028973033,4525),(339190558319,4525),(325676990259,4525),(318073636401,4525),(310817203631,4525),(303884477899,4525),(301641788026,4525),(295108030884,4525),(290907204822,4525),(288851323516,4525),(278992916570,4525),(266270112557,4525),(262845416575,4525)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_48 := recordedBatch d_s_4_48 48 0x0

private theorem s_5_32 : rowTree 5 32 = 0 := by
  exact glueRows (by decide) s_4_32.property s_4_48.property (by decide)

private theorem s_6_0 : rowTree 6 0 = 0 := by
  exact glueRows (by decide) s_5_0 s_5_32 (by decide)

private def d_s_4_64 : List (ℕ × ℕ) := [(261165893147,4525),(257870424463,4525),(246963518293,4525),(242566541706,4525),(235576151455,4525),(234226144856,4525),(231572024235,4525),(227701739707,4525),(222738214046,4525),(219155293713,4525),(215685816767,4525),(213433223381,4525),(210141194228,4525),(205906610969,4525),(203852679688,4525),(199865341210,4525)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_64 := recordedBatch d_s_4_64 64 0x0

private def d_s_4_80 : List (ℕ × ℕ) := [(195095285334,4525),(194168466876,4525),(189663398039,4525),(188787354630,4525),(186207117437,4525),(184525789063,4525),(182059965601,4525),(178872920251,4525),(177320877559,4525),(176554912645,4525),(175042665000,4525),(170657462536,4525),(167854054527,4525),(166486608055,4525),(163817484078,4525),(162514760546,4525)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_80 := recordedBatch d_s_4_80 80 0x0

private theorem s_5_64 : rowTree 5 64 = 0 := by
  exact glueRows (by decide) s_4_64.property s_4_80.property (by decide)

private def d_s_4_96 : List (ℕ × ℕ) := [(160599065923,4525),(156900047130,4525),(156300046950,4525),(151099675702,4525),(149442275237,4525),(146759290045,4525),(145195247877,4525),(143664190782,4525),(143160988712,4525),(141672312920,4525),(139258815255,4525),(137849788457,4525),(136468989240,4525),(136014849509,4525),(134670386416,4525),(133352242341,4525)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_96 := recordedBatch d_s_4_96 96 0x0

private def d_s_4_112 : List (ℕ × ℕ) := [(132487722131,4525),(132059651946,4525),(129548216410,4525),(127527183393,4525),(127130520303,4525),(126344551089,4525),(125183651692,4525),(124043891585,4525),(123668569674,4525),(121463483737,4525),(120745826521,4525),(119685101837,4525),(118299456664,4525),(116611875256,4525),(115296085409,4525),(113692523720,4525)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_112 := recordedBatch d_s_4_112 112 0x0

private theorem s_5_96 : rowTree 5 96 = 0 := by
  exact glueRows (by decide) s_4_96.property s_4_112.property (by decide)

private theorem s_6_64 : rowTree 6 64 = 0 := by
  exact glueRows (by decide) s_5_64 s_5_96 (by decide)

private theorem s_7_0 : rowTree 7 0 = 0 := by
  exact glueRows (by decide) s_6_0 s_6_64 (by decide)

private def d_s_4_128 : List (ℕ × ℕ) := [(112441436802,4525),(111521043049,4525),(110615594797,4525),(110020086884,4525),(108848101937,4525),(107985369293,4525),(107417772082,4525),(106300292009,4525),(105750225815,4525),(103869027388,4525),(102565777358,4525),(101044406124,4525),(100795221399,4525),(99567508593,4525),(99325546239,4525),(98845132472,4525)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_128 := recordedBatch d_s_4_128 128 0x0

private def d_s_4_144 : List (ℕ × ℕ) := [(98606664119,4525),(97431376108,4525),(95832267942,4525),(95384976143,4525),(95162892380,4525),(94721812925,4525),(93209720131,4525),(92786520493,4525),(92576358499,4525),(92158877739,4525),(90126708439,4525),(89730981948,4525),(88949863498,4525),(87992383805,4525),(87241114786,4525),(86870270515,4525)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_144 := recordedBatch d_s_4_144 144 0x0

private theorem s_5_128 : rowTree 5 128 = 0 := by
  exact glueRows (by decide) s_4_128.property s_4_144.property (by decide)

private def d_s_4_160 : List (ℕ × ℕ) := [(86319878094,4525),(85776416112,4525),(84534565206,4525),(84186328069,4525),(83669318889,4525),(83158621114,4525),(82487310348,4525),(81990897246,4525),(81015782512,4525),(80695878139,4525),(80220730672,4525),(80063589182,4525),(79287026726,4525),(79133518446,4525),(78676539514,4525),(77926524838,4525)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_160 := recordedBatch d_s_4_160 160 0x0

private def d_s_4_176 : List (ℕ × ℕ) := [(77778234590,4525),(77045169231,4525),(76900211246,4525),(76468591725,4525),(75202322497,4525),(74926603625,4525),(74789500965,4525),(74516795401,4525),(74111445652,4525),(73710482015,4525),(73182564507,4525),(72791562382,4525),(72404716169,4525),(71020785886,4525),(70897592849,4525),(70287983280,4525)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_176 := recordedBatch d_s_4_176 176 0x0

private theorem s_5_160 : rowTree 5 160 = 0 := by
  exact glueRows (by decide) s_4_160.property s_4_176.property (by decide)

private theorem s_6_128 : rowTree 6 128 = 0 := by
  exact glueRows (by decide) s_5_128 s_5_160 (by decide)

private def d_s_4_192 : List (ℕ × ℕ) := [(69807792105,4525),(69216701570,4525),(68866827763,4525),(68520473223,4525),(68064050420,4525),(67390704497,4525),(67169206700,4525),(66839676659,4525),(66513364161,4525),(66405300207,4525),(66083204975,4509),(65448298282,4386),(64928454769,4289),(64013253371,4135),(63913154460,4112),(63713892872,4077)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_192 := recordedBatch d_s_4_192 192 0x3263c8802e636aa02bbecaa01a5677100f76985001c546500000000000000000000000000000000000000000000000000000000000000000000000000000000

private def d_s_4_208 : List (ℕ × ℕ) := [(63417319282,4028),(63319074016,4015),(63026156171,3965),(62832378597,3934),(62735935959,3920),(62543936155,3882),(61974923847,3793),(61881093531,3777),(61601299589,3732),(60062398644,3480),(59798774363,3432),(59537454155,3398),(59192559417,3343),(58430968230,3233),(58016270088,3177),(57445484578,3087)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_208 := recordedBatch d_s_4_208 208 0xa8b199009d5e09309687d430891f5d908266d0307e5dba60787e5ea05a65a750551c3b30533a915048e1b6a0446e9d4042d25f903f3ea03039799fa037ffab4

private theorem s_5_192 : rowTree 5 192 = 1907003950 := by
  exact glueRows (by decide) s_4_192.property s_4_208.property (by decide)

private def d_s_4_224 : List (ℕ × ℕ) := [(57284460094,3069),(57204285902,3056),(57044608900,3032),(56806757856,2998),(56492691468,2958),(56336956964,2936),(56259411256,2922),(56028049729,2892),(55570988820,2829),(55195762697,2777),(55121324716,2767),(54973049465,2749),(54899210580,2738),(54752126292,2724),(54532971684,2699),(54099883888,2637)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_224 := recordedBatch d_s_4_224 224 0xe2052c50d9c6c490d6a3d9f0d4fa2250d3863320d13ffda0cff60840c93ff190c131d890bd6cecc0bb93eae0b8c8a000b3d166a0af8a0600ac810a20aad89d7

private def d_s_4_240 : List (ℕ × ℕ) := [(53673620850,2582),(53393157776,2545),(52977916108,2491),(52772707911,2463),(52636783358,2448),(52434204332,2421),(52166512160,2387),(52033688450,2370),(51770059882,2339),(51639244823,2323),(51186552633,2269),(51058666180,2252),(50868030214,2229),(50804800842,2225),(50678812495,2210),(50490997254,2184)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_240 := recordedBatch d_s_4_240 240 0x11f0a8ce11b4c1bc1193ba7c118d623a115ad45911348fa310bf6a2b109cba19105a96231035944c0fec1ee10fb14e850f92654f0f557cad0ee247000e93aef5

private theorem s_5_224 : rowTree 5 224 = 7724787463 := by
  exact glueRows (by decide) s_4_224.property s_4_240.property (by decide)

private theorem s_6_192 : rowTree 6 192 = 9631791413 := by
  exact glueRows (by decide) s_5_192 s_5_224 (by decide)

private theorem s_7_128 : rowTree 7 128 = 9631791413 := by
  exact glueRows (by decide) s_6_128 s_6_192 (by decide)

private theorem s_8_0 : rowTree 8 0 = 9631791413 := by
  exact glueRows (by decide) s_7_0 s_7_128 (by decide)

private def d_s_4_256 : List (ℕ × ℕ) := [(50428701144,2176),(50242731748,2158),(49935812190,2129),(49333086635,2059),(49155095944,2039),(49037147303,2027),(48978384994,2022),(48284066482,1944),(48170256072,1933),(48113551827,1928),(47832021389,1899),(47498503518,1865),(47443368865,1861),(47169604474,1831),(46952857297,1808),(46791599630,1792)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_256 := recordedBatch d_s_4_256 256 0x1559a6761535608b14ffe8ab14b9a4c414b2413f1465ca9e1424e89e141a92591402d2a213515801134763a2132d6dcd13009eab126337121227d02f1202c8c4

private def d_s_4_272 : List (ℕ × ℕ) := [(46631445838,1772),(46472384624,1756),(46001645782,1708),(45846844955,1690),(45744221911,1680),(45693082479,1675),(45388631068,1650),(45138003619,1628),(44840880172,1599),(44644961526,1581),(44258215785,1545),(43925268433,1514),(43784105278,1500),(43690499494,1489),(43643846532,1485),(43550838867,1475)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_272 := recordedBatch d_s_4_272 272 0x1846dd3e182cc96618239e0f1805e77417e3100c17993531174451ef171aa0e316d5ccc716a4e736167019c616647f8a164d625f162081a115b06564158b9d52

private theorem s_5_256 : rowTree 5 256 = 11499281983 := by
  exact glueRows (by decide) s_4_256.property s_4_272.property (by decide)

private def d_s_4_288 : List (ℕ × ℕ) := [(43504483531,1471),(43274179224,1452),(43001012390,1425),(42865718172,1412),(42731272637,1400),(42332949018,1372),(42289148761,1368),(41941982839,1337),(41898987470,1336),(41431791462,1298),(41306177137,1288),(41139871441,1274),(41016018341,1266),(40933863072,1258),(40892908731,1254),(40811245409,1249)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_288 := recordedBatch d_s_4_288 288 0x1a596a261a503f641a453bcf1a2f43e31a1fa5b619fcf0ac19e5612d198b4162198d569c19402e7f1936294918fd619518e04f3c18bf8ad3187aeb5718501e65

private def d_s_4_304 : List (ℕ × ℕ) := [(40648893364,1233),(40527974494,1227),(40328033820,1210),(40288282185,1206),(40090693749,1190),(39817303728,1170),(39624296924,1151),(39509388378,1144),(39281559132,1127),(39243842801,1124),(39168627002,1116),(39131127120,1114),(38944699645,1102),(38723318121,1082),(38686665667,1078),(38395925108,1059)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_304 := recordedBatch d_s_4_304 304 0x1c34f6b51c0bc6f61bfef16b1bc593d51bac7ae81ba963951b90975d1b88e4be1b5ff1861b529c3d1b1b5eb81aecfa391ac4e39a1ab964fe1a8d919a1a8607e2

private theorem s_5_288 : rowTree 5 288 = 14190951484 := by
  exact glueRows (by decide) s_4_288.property s_4_304.property (by decide)

private theorem s_6_256 : rowTree 6 256 = 25690233467 := by
  exact glueRows (by decide) s_5_256 s_5_288 (by decide)

private def d_s_4_320 : List (ℕ × ℕ) := [(38359889514,1057),(38252187438,1048),(38180721417,1045),(38145088453,1042),(37967916653,1027),(37827359812,1018),(37514880475,998),(37106184546,970),(37038932739,966),(36938510869,956),(36805459052,945),(36542210350,930),(36509568805,928),(36444460345,926),(36314937607,916),(36058634563,902)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_320 := recordedBatch d_s_4_320 320 0x1dabbd751d918a941d74d2ed1d7692141d7226521d54d0ec1d3450b91d13088f1d0acba71cc67b731c9a51361c86a4ef1c5c03181c538b6b1c516ac61c3865bd

private def d_s_4_336 : List (ℕ × ℕ) := [(36026850839,900),(35963451190,893),(35837318963,886),(35743298887,880),(35649770848,872),(35587690272,869),(35402739088,856),(35372100629,855),(35038544601,836),(34948663768,832),(34918805875,830),(34829537518,822),(34770278415,818),(34681766888,811),(34476982098,799),(34389955639,793)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_336 := recordedBatch d_s_4_336 336 0x1ec534f51eb3efad1e9828ee1e81a7871e76a8271e5aa6081e5536da1e5092001e282efc1e28b7211e04d8ab1e007cc31de6a2211dd80d971dca60c51db074fc

private theorem s_5_320 : rowTree 5 320 = 15887787769 := by
  exact glueRows (by decide) s_4_320.property s_4_336.property (by decide)

private def d_s_4_352 : List (ℕ × ℕ) := [(34332181669,790),(34303367417,787),(34217214129,783),(34160018618,781),(34074582974,777),(33904987372,765),(33820821081,759),(33737071628,756),(33543259973,742),(33488293549,738),(33406180856,736),(33243157606,725),(33135356528,720),(33054963427,712),(33001584398,708),(32658779286,693)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_352 := recordedBatch d_s_4_352 352 0x1fb765211fa42e901f9696ae1f7590c21f6df6831f4cc9b81f526eeb1f459bf41f193c5f1f190b141f068a991ee1f8c11edc10d31edc44841ed6a7e41ecad765

private def d_s_4_368 : List (ℕ × ℕ) := [(32425594825,682),(32297481056,675),(32195716642,668),(32145074539,665),(32069409397,659),(32044266779,657),(31969074913,654),(31696364697,641),(31549565632,634),(31525231220,633),(31331899024,622),(31236119432,617),(31188448895,615),(31046306325,607),(30882102211,599),(30765872997,595)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_368 := recordedBatch d_s_4_368 368 0x209642892096265a20851162206ec538206c39542060309d2041d4072040ba6d20336b0d201b32bf2018a82220110b591ffa50ae1ff2045e1fdad7001fca0ef1

private theorem s_5_352 : rowTree 5 352 = 17023101390 := by
  exact glueRows (by decide) s_4_352.property s_4_368.property (by decide)

private theorem s_6_320 : rowTree 6 320 = 32910889159 := by
  exact glueRows (by decide) s_5_320 s_5_352 (by decide)

private theorem s_7_256 : rowTree 7 256 = 58601122626 := by
  exact glueRows (by decide) s_6_256 s_6_320 (by decide)

private def d_s_4_384 : List (ℕ × ℕ) := [(30742732062,593),(30696554470,591),(30604614210,589),(30536019632,585),(30467731850,580),(30422376090,576),(30399748811,575),(30354595081,574),(30287115433,572),(30197607888,566),(30153052215,565),(30130823647,564),(30064334150,560),(29954168030,556),(29932231620,554),(29823029753,549)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_384 := recordedBatch d_s_4_384 384 0x20ff237320f5199820eb683220e95acd20dc0d8120da2fd520de13f120c7ae2620c9e7bc20cdf83d20cc437620b9f0ca20a6141d2099c78720a232c4209f1d1a

private def d_s_4_400 : List (ℕ × ℕ) := [(29736240289,546),(29693034709,542),(29542798899,535),(29436415036,529),(29309761403,524),(29288758350,522),(29225929408,521),(29184192986,519),(29163369445,518),(28997844822,510),(28854544495,503),(28813861316,500),(28753051197,498),(28672369188,492),(28612154201,489),(28572151190,487)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_400 := recordedBatch d_s_4_400 400 0x21a2a8a6219cfc8821949bf32178e7df21790cdd216b6a16215913bd2144f7eb214281b2213da1cf214681c5213c1a0721360eec2122d42121139d3f20ffb4df

private theorem s_5_384 : rowTree 5 384 = 17750482757 := by
  exact glueRows (by decide) s_4_384.property s_4_400.property (by decide)

private def d_s_4_416 : List (ℕ × ℕ) := [(28393513218,480),(28314833583,478),(28217095117,474),(28158775251,470),(28100695962,467),(28023628575,462),(27927886762,461),(27813856602,455),(27681992737,449),(27644546687,446),(27588567180,446),(27532813928,445),(27514279554,443),(27257393983,434),(27239228442,434),(27148762721,432)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_416 := recordedBatch d_s_4_416 416 0x21ec9d6221f4fcc721fa5a9c21f3c9ac21e72a0521ee70de21fec1a821eed5b021dfbb6c21cbc21b21de70d521c8f83721bf7e0f21ad83e221a6cc4e21abdd91

private def d_s_4_432 : List (ℕ × ℕ) := [(27076821647,433),(27040993898,434),(26916339991,435),(26880935401,436),(26810404904,437),(26705300410,438),(26653056587,439),(26549179784,440),(26514733880,441),(26463232293,442),(26292995997,443),(26208696555,444),(26191901491,445),(26058311939,446),(25844111462,447),(25811469704,448)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_432 := recordedBatch d_s_4_432 432 0x1fd669791fe855b4202f7449205f1e44206ca829208e01cb20c8aa8120e0963220f38501211aefb621333d6c215b2a492178fc2c218c7c4a21ba670321ce2533

private theorem s_5_416 : rowTree 5 416 = 17913979016 := by
  exact glueRows (by decide) s_4_416.property s_4_432.property (by decide)

private theorem s_6_384 : rowTree 6 384 = 35664461773 := by
  exact glueRows (by decide) s_5_384 s_5_416 (by decide)

private def d_s_4_448 : List (ℕ × ℕ) := [(25795179727,449),(25697870026,450),(25649489976,451),(25617337685,452),(25521362645,453),(25473644298,454),(25410296722,455),(25378740936,456),(25315863906,457),(25144547694,458),(25129088396,459),(25098226759,460),(25082824349,461),(24990805428,462),(24778697955,463),(24763685112,464)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_448 := recordedBatch d_s_4_448 448 0x1e25115f1e3128711e76309a1e98ac8f1ea5125e1eb5f7621ec26ab21efc172c1f166dcf1f27b7f61f4248c91f5857c71f7c800b1f8e24021fa48b1a1fc94746

private def d_s_4_464 : List (ℕ × ℕ) := [(24718755535,465),(24673988697,466),(24629383716,467),(24599736549,468),(24555399385,469),(24540655825,470),(24452564928,471),(24423341665,472),(24336089477,473),(24321608019,474),(24249458485,475),(24235079915,476),(24120662306,477),(24106436023,478),(23993227048,479),(23951047335,480)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_464 := recordedBatch d_s_4_464 464 0x1cc3e13f1cd72dc61cfec0171d0a2fbf1d3239c11d3dc9791d59e1361d6586281d8609a61d95fa5f1db6d0381dc2ac931dd70ebd1de7411e1dfbc4361e105edb

private theorem s_5_448 : rowTree 5 448 = 16223779976 := by
  exact glueRows (by decide) s_4_448.property s_4_464.property (by decide)

private def d_s_4_480 : List (ℕ × ℕ) := [(23811513124,481),(23701050900,482),(23646203226,483),(23618874474,484),(23605233772,485),(23577999583,486),(23564406040,487),(23415905057,488),(23362367692,489),(23282519098,490),(23242799134,491),(23176899505,492),(23163764396,493),(23137538792,494),(23098311544,495),(23085265336,496)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_480 := recordedBatch d_s_4_480 480 0x1b5f0d891b6987bd1b7b5fe31b8998741b9424681bad913f1bbfaa351bdd22681bf338bf1c2431531c2f1c181c3de6791c48dce81c57b8531c6e6b541c94ff08

private def d_s_4_496 : List (ℕ × ℕ) := [(23046214985,497),(22981423827,498),(22968509287,499),(22891325834,500),(22827401439,501),(22814659379,502),(22751161857,503),(22662856821,504),(22625221299,505),(22600200319,506),(22562772441,507),(22513061017,508),(22475920966,509),(22438903254,510),(22340782879,511),(22267753896,512)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_496 := recordedBatch d_s_4_496 496 0x1a11c6241a2c65111a4e06e61a5ec24a1a6f8ecb1a83e3ed1a94d1171aa250fc1ab35fe81ad296801aeaf4111af52b801b0db9531b2a07711b3463c61b4d5181

private theorem s_5_480 : rowTree 5 480 = 14663913807 := by
  exact glueRows (by decide) s_4_480.property s_4_496.property (by decide)

private theorem s_6_448 : rowTree 6 448 = 30887693783 := by
  exact glueRows (by decide) s_5_448 s_5_480 (by decide)

private theorem s_7_384 : rowTree 7 384 = 66552155556 := by
  exact glueRows (by decide) s_6_384 s_6_448 (by decide)

private theorem s_8_256 : rowTree 8 256 = 125153278182 := by
  exact glueRows (by decide) s_7_256 s_7_384 (by decide)

private theorem s_9_0 : rowTree 9 0 = 134785069595 := by
  exact glueRows (by decide) s_8_0 s_8_256 (by decide)

private def d_s_4_512 : List (ℕ × ℕ) := [(22255628792,513),(22231418154,514),(22147094162,515),(22111150812,516),(22087253324,517),(22039612983,518),(21980350781,519),(21933169990,520),(21897917105,521),(21862777361,522),(21734890868,523),(21700271981,524),(21688756846,525),(21631363999,526),(21551522424,527),(21528818687,528)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_512 := recordedBatch d_s_4_512 512 0x18e3adbe18efdf62190bb87b19217a79192ab2fb193a430819637ee51973506019832fa2199660b719acec1119c04f4c19cd2ca419dd641b19fb04001a08103f

private def d_s_4_528 : List (ℕ × ℕ) := [(21494852630,529),(21393594492,530),(21382402447,531),(21326617415,532),(21249005603,533),(21226934446,534),(21215916053,535),(21160995225,536),(21084582036,537),(21062850954,538),(21019522899,539),(20922683530,540),(20901284723,541),(20869268459,542),(20858618156,543),(20837350128,544)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_528 := recordedBatch d_s_4_528 528 0x17cb2c4517d68b4017df107717ed5e1217f8d3c21818c1f4182a3a951835de8c1850666a18652157186df3941879c96b1894c9cb18a9e47218b2da3818d46c87

private theorem s_5_512 : rowTree 5 512 = 13349684401 := by
  exact glueRows (by decide) s_4_512.property s_4_528.property (by decide)

private def d_s_4_544 : List (ℕ × ℕ) := [(20805529283,545),(20794943921,546),(20731657254,547),(20710647214,548),(20606232557,549),(20492585749,550),(20431123357,551),(20420915452,552),(20400530210,553),(20370028545,554),(20339617953,555),(20329501257,556),(20299211461,557),(20188916906,558),(20178949532,559),(20149106372,560)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_544 := recordedBatch d_s_4_544 544 0x16bb556616c894b016d08c9b16f35a791700d2081708e8801716707c17240195172ee34217370d76174d006a177108111792a54f179dde2417b481ef17bcf7bf

private def d_s_4_560 : List (ℕ × ℕ) := [(20069954469,561),(20040432595,562),(19981648632,563),(19971884816,564),(19942650537,565),(19884437984,566),(19807347844,567),(19797753585,568),(19778592924,569),(19749921371,570),(19683343259,571),(19664403308,572),(19654946995,573),(19570247678,574),(19458444312,575),(19412235705,576)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_560 := recordedBatch d_s_4_560 560 0x15a6385615b757cd15d9cf3215f52ff715fcbb611606c84b161d7a6b162a2a4a16345bea163c044a16559b9b166a3be4167730d9167efc951693d9b616a0f5c9

private theorem s_5_544 : rowTree 5 544 = 12182675556 := by
  exact glueRows (by decide) s_4_544.property s_4_560.property (by decide)

private theorem s_6_512 : rowTree 6 512 = 25532359957 := by
  exact glueRows (by decide) s_5_512 s_5_544 (by decide)

private def d_s_4_576 : List (ℕ × ℕ) := [(19384615735,577),(19375426535,578),(19329610913,579),(19320473778,580),(19274917367,581),(19265831853,582),(19220532460,583),(19193454931,584),(19184446034,585),(19139528109,586),(19130569753,587),(19085903468,588),(19059203673,589),(19023719933,590),(18891824486,591),(18848264827,592)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_576 := recordedBatch d_s_4_576 576 0x14c5985b14d59c3a14fcafe3150aae1515166b821526db67152e00a2153e8f2b1545bd1e1551a9fb1562608115699f14157a73211581bc881592addf159a047e

private def d_s_4_592 : List (ℕ × ℕ) := [(18839576988,593),(18796257658,594),(18761745364,595),(18735944202,596),(18693099600,597),(18616471089,598),(18591067672,599),(18540468259,600),(18490143532,601),(18481782626,602),(18406873351,603),(18382038352,604),(18365518884,605),(18340795278,606),(18316138148,607),(18242562944,608)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_592 := recordedBatch d_s_4_592 592 0x13e052bd13f7acf7140274e9140d44461415fa8c1420da541438aed6143f58bf1450e384146287b1146dab6414861daf1495d5d914a1280c14aec0bd14beada5

private theorem s_5_576 : rowTree 5 576 = 11152320478 := by
  exact glueRows (by decide) s_4_576.property s_4_592.property (by decide)

private def d_s_4_608 : List (ℕ × ℕ) := [(18234424393,609),(18193840319,610),(18137325173,611),(18113211733,612),(18097171696,613),(18089162326,614),(18073164836,615),(17977770959,616),(17969866905,617),(17922588150,618),(17899041943,619),(17836553470,620),(17805472566,621),(17782232881,622),(17759053781,623),(17689877635,624)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_608 := recordedBatch d_s_4_608 608 0x130e89d713244dd2132e627013387f621344a10a1358cb2b13630b02137363ca1379aef213966258139eccd213a52d7813ad9e5413b8291213cb090813d9d6d9

private def d_s_4_624 : List (ℕ × ℕ) := [(17628838592,625),(17621238317,626),(17606057410,627),(17583335030,628),(17575773931,629),(17553129601,630),(17530543546,631),(17493029008,632),(17470597254,633),(17425905895,634),(17381442601,635),(17315171479,636),(17307839202,637),(17285879584,638),(17271270770,639),(17205835519,640)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_624 := recordedBatch d_s_4_624 624 0x12535e9f1267c7e6126f6f021278ef27127ec3fb12937a5f12a2ba1212b20f4912bbc92f12c955b712d3217612dcf4b012e2f9a212ecd94812f4d1d712fae049

private theorem s_5_608 : rowTree 5 608 = 10241150416 := by
  exact glueRows (by decide) s_4_608.property s_4_624.property (by decide)

private theorem s_6_576 : rowTree 6 576 = 21393470894 := by
  exact glueRows (by decide) s_5_576 s_5_608 (by decide)

private theorem s_7_512 : rowTree 7 512 = 46925830851 := by
  exact glueRows (by decide) s_6_512 s_6_576 (by decide)

private def d_s_4_640 : List (ℕ × ℕ) := [(17176912072,641),(17090722256,642),(17076441310,643),(17069309783,644),(17055064584,645),(17033741311,646),(17026645397,647),(16984193757,648),(16970090212,649),(16920911727,650),(16816483142,651),(16781959465,652),(16761313216,653),(16720172745,654),(16672430054,655),(16652052262,656)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_640 := recordedBatch d_s_4_640 640 0x118bbc4f119483a411a4206211b21dba11bb02ea11c764bd11e541d111f55b4c11fcb919120b30ae1210d52e121a0ad012217b281227289f122ea18d12482dd1

private def d_s_4_656 : List (ℕ × ℕ) := [(16618199746,657),(16577757971,658),(16571036804,659),(16557610807,660),(16537512554,661),(16510790659,662),(16490805841,663),(16457605104,664),(16450980993,665),(16437748754,666),(16391603079,667),(16371905578,668),(16352255362,669),(16339181402,670),(16319609613,671),(16313096099,672)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_656 := recordedBatch d_s_4_656 656 0x10fdca7d1102f6cd110b5b0a1112277c111a95b811230cec11320bb21138ee71113e325e114a0c321152a330115ce94111658cb2116c8c761171e3dd117f9ef5

private theorem s_5_640 : rowTree 5 640 = 9437710159 := by
  exact glueRows (by decide) s_4_640.property s_4_656.property (by decide)

private def d_s_4_672 : List (ℕ × ℕ) := [(16280606364,673),(16274123940,674),(16222449802,675),(16183909038,676),(16158316773,677),(16101029063,678),(16088353582,679),(16069377738,680),(16031560022,681),(16025274368,682),(16006446946,683),(15987663711,684),(15968924507,685),(15882052565,686),(15863559975,687),(15820577618,688)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_672 := recordedBatch d_s_4_672 672 0x104de7c4105bbb111063a04e107c2be910842c6b108c30d210943c39109938b910a5ebcc10ae08ca10b49dc810c622c210cfea7810dce37d10ed19bf10f23fce

private def d_s_4_688 : List (ℕ × ℕ) := [(15808339693,689),(15783920555,690),(15753502515,691),(15729252367,692),(15693016808,693),(15638975426,694),(15627016737,695),(15621044249,696),(15609112956,697),(15537906207,698),(15502545904,699),(15484926038,700),(15479061646,701),(15432305938,702),(15414845286,703),(15397424101,704)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_688 := recordedBatch d_s_4_688 688 0xfb30f9b0fba75f30fc1e1330fd05d0f0fd503430fdc81fb0fe847110ffcbe501002eaad1007a79c100dd783101e3a5b102a548b10338d30103e46d41047908d

private theorem s_5_672 : rowTree 5 672 = 8754743695 := by
  exact glueRows (by decide) s_4_672.property s_4_688.property (by decide)

private theorem s_6_640 : rowTree 6 640 = 18192453854 := by
  exact glueRows (by decide) s_5_640 s_5_672 (by decide)

private def d_s_4_704 : List (ℕ × ℕ) := [(15356927400,705),(15328131362,706),(15287997859,707),(15276569716,708),(15191400214,709),(15174480147,710),(15157597729,711),(15140752834,712),(15118351129,713),(15101593304,714),(15090442044,715),(15084872588,716),(15051541991,717),(15034931865,718),(15023878800,719),(15018358360,720)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_704 := recordedBatch d_s_4_704 704 0xf26759f0f2ad5ed0f3089920f37901f0f4295c90f46fed40f4cc08c0f53d7190f5c4c240f636e770f6a97f40f71c5e60f8955230f8f3b930f9c0a030fa62458

private def d_s_4_720 : List (ℕ × ℕ) := [(15001821353,721),(14941495988,722),(14925127725,723),(14919679604,724),(14908795286,725),(14860011735,726),(14854611040,727),(14843821419,728),(14811546395,729),(14806180864,730),(14790107572,731),(14779411418,732),(14710261751,733),(14694395929,734),(14678564294,735),(14668028809,736)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_720 := recordedBatch d_s_4_720 720 0xea3be9b0ea9281f0eafd1580eb67f8b0ec9c0890ecf3f740ed6045a0eda43d80ee4e06c0eea6d7f0eeeb4e60efd46220f02e12f0f0732170f0e1c1d0f1f793f

private theorem s_5_704 : rowTree 5 704 = 8116623974 := by
  exact glueRows (by decide) s_4_704.property s_4_720.property (by decide)

private def d_s_4_736 : List (ℕ × ℕ) := [(14647003145,737),(14620805679,738),(14537599956,739),(14496351224,740),(14491211585,741),(14475814513,742),(14465567962,743),(14460450124,744),(14450225305,745),(14445118316,746),(14419637423,747),(14384114825,748),(14368944376,749),(14358848507,750),(14338699272,751),(14313592112,752)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_736 := recordedBatch d_s_4_736 736 0xe2318220e2bbdef0e333fc40e386d100e3ec8450e49e66f0e52b03a0e56bbbc0e5bf8a10e6005af0e6547cc0e6bbf580e6fd23b0e7c5f4f0e92cbd70e9bdf2a

private def d_s_4_752 : List (ℕ × ℕ) := [(14298569976,753),(14248723122,754),(14238795428,755),(14233836767,756),(14218981484,757),(14145167772,758),(14135383806,759),(14115856424,760),(14091522936,761),(14076963071,762),(14062433262,763),(14043106778,764),(14028646740,765),(13999815816,766),(13990231825,767),(13975880416,768)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_752 := recordedBatch d_s_4_752 752 0xda92a350daf273b0db40cd00dbd65bf0dc36f220dca9a910dd0ac460dd6c4a10ddf1d7f0de65e690deb5f560dff3b9f0e0571110e095ce20e0e71ba0e1cce27

private theorem s_5_736 : rowTree 5 736 = 7574774488 := by
  exact glueRows (by decide) s_4_736.property s_4_752.property (by decide)

private theorem s_6_704 : rowTree 6 704 = 15691398462 := by
  exact glueRows (by decide) s_5_704 s_5_736 (by decide)

private theorem s_7_640 : rowTree 7 640 = 33883852316 := by
  exact glueRows (by decide) s_6_640 s_6_704 (by decide)

private theorem s_8_512 : rowTree 8 512 = 80809683167 := by
  exact glueRows (by decide) s_7_512 s_7_640 (by decide)

private def d_s_4_768 : List (ℕ × ℕ) := [(13971103154,769),(13956790943,770),(13947265749,771),(13933002310,772),(13928254311,773),(13904562775,774),(13899834136,775),(13862120494,776),(13848030587,777),(13801270395,778),(13791956226,779),(13764088997,780),(13731719226,781),(13667434301,782),(13653737189,783),(13608277768,784)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_768 := recordedBatch d_s_4_768 768 0xd2b01580d37ed5e0d3d9e4b0d4ee1240d58ddb90d61d7400d6694d00d73e81e0d79c5460d850e6a0d88ca930d90e1050d94a1b20d9a90da0d9f6d640da56406

private def d_s_4_784 : List (ℕ × ℕ) := [(13599222185,785),(13558620758,786),(13540653396,787),(13527209094,788),(13518261047,789),(13504861152,790),(13473697800,791),(13460386062,792),(13447100601,793),(13425016349,794),(13420608201,795),(13398610810,796),(13372308940,797),(13354831654,798),(13333049185,799),(13328701215,800)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_784 := recordedBatch d_s_4_784 784 0xcc39a880cc709930cce6aa40cd4d4ba0cdd3e230ce4b5060ce830c80cefaeaa0cf531690cfab6670d044a890d09daab0d0e684d0d13fe350d1a9c0a0d2664f1

private theorem s_5_768 : rowTree 5 768 = 7083806175 := by
  exact glueRows (by decide) s_4_768.property s_4_784.property (by decide)

private def d_s_4_800 : List (ℕ × ℕ) := [(13307003834,801),(13289696724,802),(13263820307,803),(13242333477,804),(13191048015,805),(13186792152,806),(13178288659,807),(13161314531,808),(13148612603,809),(13140158263,810),(13123282156,811),(13085468953,812),(13064555626,813),(13052039686,814),(13039547703,815),(13035389021,816)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_800 := recordedBatch d_s_4_800 800 0xc5b5ecf0c5ea7850c63cecb0c68f7ca0c7004240c7adbed0c81054a0c854f3e0c8a8e260c90c39e0c95147e0c98717e0ca664a60cada87a0cb5ebc00cbc433e

private def d_s_4_816 : List (ℕ × ℕ) := [(13022928876,817),(13002214817,818),(12977444761,819),(12973325591,820),(12952768904,821),(12940466131,822),(12928186708,823),(12915930566,824),(12899625146,825),(12887423073,826),(12867137502,827),(12854996784,828),(12850954968,829),(12838844754,830),(12826757344,831),(12814692672,832)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_816 := recordedBatch d_s_4_816 816 0xc054ca70c0a40630c0f34d30c142cb90c175db00c1c5a330c2327390c282a0d0c2e19790c3323350c3831700c3d419d0c4428790c4768e90c4f45970c563d06

private theorem s_5_800 : rowTree 5 800 = 6631248089 := by
  exact glueRows (by decide) s_4_800.property s_4_816.property (by decide)

private theorem s_6_768 : rowTree 6 768 = 13715054264 := by
  exact glueRows (by decide) s_5_768 s_5_800 (by decide)

private def d_s_4_832 : List (ℕ × ℕ) := [(12794635241,833),(12778634446,834),(12730871290,835),(12718986238,836),(12675596922,837),(12671667114,838),(12636408185,839),(12628599498,840),(12613011040,841),(12593579503,842),(12535642471,843),(12520282517,844),(12485859867,845),(12478236079,846),(12474427675,847),(12455420471,848)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_832 := recordedBatch d_s_4_832 832 0xb92d3b90b9925aa0b9c28060b9fff5d0ba9b8060baf45e40bbe301e0bc4aac20bca4f240bce3fbd0bd83c850bdb56b20be7213b0bec00a20bf8c8fc0bfe9831

private def d_s_4_848 : List (ℕ × ℕ) := [(12444043926,849),(12440256362,850),(12428907488,851),(12421353070,852),(12387471519,853),(12372472310,854),(12350041479,855),(12316547318,856),(12286926883,857),(12275855917,858),(12272170027,859),(12250101087,860),(12239096355,861),(12220799006,862),(12217146099,863),(12198914274,864)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_848 := recordedBatch d_s_4_848 848 0xb3913090b3f1be50b41fd3e0b480ba80b4c86a60b5368ca0b56511d0b5ad4860b6363cd0b6ccd9c0b73d15e0b7939cb0b82c0610b868d980b8b31730b8e2db3

private theorem s_5_832 : rowTree 5 832 = 6216865098 := by
  exact glueRows (by decide) s_4_832.property s_4_848.property (by decide)

private def d_s_4_864 : List (ℕ × ℕ) := [(12195274437,865),(12184367946,866),(12166233748,867),(12140936366,868),(12133727854,869),(12090655902,870),(12087080371,871),(12058552080,872),(12054995510,873),(12037244081,874),(12033700066,875),(12016011253,876),(11980789177,877),(11973769526,878),(11970262784,879),(11963255459,880)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_864 := recordedBatch d_s_4_864 864 0xae5a3c90ae925cf0aebe97a0aef6e7c0af903d90afed6510b01a1f30b077c3f0b0a49200b1278640b154ab70b20a1550b243f720b2bc5e00b31c4d60b363501

private def d_s_4_880 : List (ℕ × ℕ) := [(11949265393,881),(11921383193,882),(11910960885,883),(11900556784,884),(11897092789,885),(11876351090,886),(11848807733,887),(11835083908,888),(11828233910,889),(11817973768,890),(11766938902,891),(11763552245,892),(11746648161,893),(11743273172,894),(11733159832,895),(11726427278,896)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_880 := recordedBatch d_s_4_880 880 0xa93a32d0a9700230a9b16af0a9dbefb0aa3471a0aa5f22c0ab2c4230ab6eb330aba583d0abf3d4d0ac716690acd80050ad03ab30ad471cf0ad8aafb0ae0a244

private theorem s_5_864 : rowTree 5 864 = 5842161138 := by
  exact glueRows (by decide) s_4_864.property s_4_880.property (by decide)

private theorem s_6_832 : rowTree 6 832 = 12059026236 := by
  exact glueRows (by decide) s_5_832 s_5_864 (by decide)

private theorem s_7_768 : rowTree 7 768 = 25774080500 := by
  exact glueRows (by decide) s_6_768 s_6_832 (by decide)

private def d_s_4_896 : List (ℕ × ℕ) := [(11716342920,897),(11706275892,898),(11692880067,899),(11682853302,900),(11676178339,901),(11656199138,902),(11646235155,903),(11632976313,904),(11613144559,905),(11606548992,906),(11583523388,907),(11563859747,908),(11547524304,909),(11508506906,910),(11498793719,911),(11479416452,912)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_896 := recordedBatch d_s_4_896 896 0xa411d540a470b4b0a4af4960a5508800a5a5b2e0a6061470a67202b0a6a6b9f0a7081530a7536640a793a6d0a7f5b790a82b0be0a86bc1c0a8b7e1f0a8f8f4a

private def d_s_4_912 : List (ℕ × ℕ) := [(11469752287,913),(11466534514,914),(11431257803,915),(11418483664,916),(11389845973,917),(11373998129,918),(11364510573,919),(11342434377,920),(11336142636,921),(11332999383,922),(11323580074,923),(11307915971,924),(11295415856,925),(11286058892,926),(11279829523,927),(11270498353,928)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_912 := recordedBatch d_s_4_912 912 0x9f8327909fbefef09ff0a740a02cbaf0a0735ba0a0c49540a1012af0a128bff0a15ae250a1c1ed20a1fefd70a25155e0a2cec9a0a3172d40a3ab1da0a3d3a20

private theorem s_5_896 : rowTree 5 896 = 5506099631 := by
  exact glueRows (by decide) s_4_896.property s_4_912.property (by decide)

private def d_s_4_928 : List (ℕ × ℕ) := [(11224073123,929),(11202538653,930),(11187207411,931),(11184146197,932),(11165814035,933),(11150583079,934),(11147541873,935),(11123271813,936),(11120245484,937),(11093082447,938),(11057070817,939),(11030215160,940),(11021292241,941),(10997568216,942),(10971000477,943),(10962173066,944)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_928 := recordedBatch d_s_4_928 928 0x99c54a7099fdb4d09a70c5609adaa4609b13c5809b8843d09c1b36909c910f809cb72ac09d23be209d4a05e09d98c7c09df1f3909e1884c09e67da609ecc195

private def d_s_4_944 : List (ℕ × ℕ) := [(10959233751,945),(10932850682,946),(10927005020,947),(10918248237,948),(10915332428,949),(10900776710,950),(10889160057,951),(10874674012,952),(10866000871,953),(10857341553,954),(10845817242,955),(10840064256,956),(10831446211,957),(10828576573,958),(10814251164,959),(10811390630,960)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_944 := recordedBatch d_s_4_944 944 0x96270050964af4409694624096b88e2096ef8350971d2d30975dcfb09795158097cc5ed09816c8a09857ff1098a2d21098c793f098ff9bd0992e025099a034d

private theorem s_5_928 : rowTree 5 928 = 5170023247 := by
  exact glueRows (by decide) s_4_928.property s_4_944.property (by decide)

private theorem s_6_896 : rowTree 6 896 = 10676122878 := by
  exact glueRows (by decide) s_5_896 s_5_928 (by decide)

private def d_s_4_960 : List (ℕ × ℕ) := [(10794259151,961),(10788560717,962),(10780024338,963),(10771501456,964),(10768663490,965),(10751667046,966),(10746013481,967),(10726272740,968),(10700998109,969),(10695397691,970),(10687008047,971),(10659137378,972),(10653580679,973),(10642484644,974),(10634177774,975),(10628647062,976)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_960 := recordedBatch d_s_4_960 960 0x9231e7a0925d9f1092925db092d0317092fc28e09370875093a5cbb093d21860943e67b09498d42094c58ed0951732d0953addb09571140095a7694095d48a7

private def d_s_4_976 : List (ℕ × ℕ) := [(10617602877,977),(10612089387,978),(10592837184,979),(10584607607,980),(10579128323,981),(10559995421,982),(10543650787,983),(10538213813,984),(10535497429,985),(10494919059,986),(10489532215,987),(10457326922,988),(10449306475,989),(10441298320,990),(10425318780,991),(10409388075,992)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_976 := recordedBatch d_s_4_976 976 0x8ddb0a908e26fad08e732b808ea5d0408ed8a0308f5931d08f83a790901f71e090419970906c817090ba9a809111b040913ceda09171111091c8ea5091f480f

private theorem s_5_960 : rowTree 5 960 = 4899505296 := by
  exact glueRows (by decide) s_4_960.property s_4_976.property (by decide)

private def d_s_4_992 : List (ℕ × ℕ) := [(10390863678,993),(10382944818,994),(10377672280,995),(10375038019,996),(10369773506,997),(10346149165,998),(10338298286,999),(10322632220,1000),(10312214526,1001),(10304415045,1002),(10299221942,1003),(10283673991,1004),(10281087228,1005),(10265593941,1006),(10227064250,1007),(10206633107,1008)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_992 := recordedBatch d_s_4_992 992 0x89cdd3f08a2690408ab91ac08b028eb08b231e308b6cc2a08b95a6508bc6e4f08c0086108c4afde08c7ca1808ce09b908d0a1a708d2b40308d54d9a08d86e3c

private def d_s_4_1008 : List (ℕ × ℕ) := [(10204084952,1009),(10196448117,1010),(10168543917,1011),(10150866081,1012),(10143308667,1013),(10130737954,1014),(10115694165,1015),(10108189013,1016),(10105689770,1017),(10100694990,1018),(10090720226,1019),(10078279442,1020),(10070829685,1021),(10063390933,1022),(10033745495,1023),(10016532845,1024)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1008 := recordedBatch d_s_4_1008 1008 0x85fcf710864a4af086bea80086ed69b0871c44d0875ad6b08791b6e087b8f3d087d861608807a860884ec600888e118088bdba00890d74b0897da1c089adc6e

private theorem s_5_992 : rowTree 5 992 = 4626050642 := by
  exact glueRows (by decide) s_4_992.property s_4_1008.property (by decide)

private theorem s_6_960 : rowTree 6 960 = 9525555938 := by
  exact glueRows (by decide) s_5_960 s_5_992 (by decide)

private theorem s_7_896 : rowTree 7 896 = 20201678816 := by
  exact glueRows (by decide) s_6_896 s_6_960 (by decide)

private theorem s_8_768 : rowTree 8 768 = 45975759316 := by
  exact glueRows (by decide) s_7_768 s_7_896 (by decide)

private theorem s_9_512 : rowTree 9 512 = 126785442483 := by
  exact glueRows (by decide) s_8_512 s_8_768 (by decide)

private theorem s_10_0 : rowTree 10 0 = 261570512078 := by
  exact glueRows (by decide) s_9_0 s_9_512 (by decide)

private def d_s_4_1024 : List (ℕ × ℕ) := [(10009174060,1025),(10004274208,1026),(9994488880,1027),(9979846728,1028),(9957963765,1029),(9945847980,1030),(9943428360,1031),(9931347898,1032),(9928935327,1033),(9924113700,1034),(9916890034,1035),(9892886912,1036),(9885708617,1037),(9880928871,1038),(9864236099,1039),(9859477090,1040)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1024 := recordedBatch d_s_4_1024 1024 0x82a523f082ca7990831504e0833a81008367802083c914d083f64f90841c1d50843a70908477139084957aa084d237e0852dc190857295a085a8519085cec77

private def d_s_4_1040 : List (ℕ × ℕ) := [(9857099307,1041),(9852347180,1042),(9835750758,1043),(9828655110,1044),(9814494483,1045),(9786295289,1046),(9774593394,1047),(9767585679,1048),(9758257676,1049),(9746622696,1050),(9744299029,1051),(9709576500,1052),(9704965517,1053),(9698057249,1054),(9695756678,1055),(9681976140,1056)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1040 := recordedBatch d_s_4_1040 1040 0x7f1deca07f5e31907f7b0de07fa62dc07fca3510804b60f080689a5080a2abd080d58d8081015410813bc06081a9603081ebb4a0821817b08262031082874a3

private theorem s_5_1024 : rowTree 5 1024 = 4378436058 := by
  exact glueRows (by decide) s_4_1024.property s_4_1040.property (by decide)

private def d_s_4_1056 : List (ℕ × ℕ) := [(9677391328,1057),(9661378626,1058),(9654532249,1059),(9615918663,1060),(9602363979,1061),(9593348733,1062),(9586598399,1063),(9575368929,1064),(9573126192,1065),(9568643866,1066),(9546295054,1067),(9535159752,1068),(9526270196,1069),(9508540718,1070),(9506329172,1071),(9495286857,1072)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1056 := recordedBatch d_s_4_1056 1056 0x7b8c18707bc2cb107bde94507c29e7d07c5a2fb07c917b307ceb18b07d0e1c507d2a58407d6217807d8c1e707dbd3b507dfc3da07e888cf07eb33fb07efa243

private def d_s_4_1072 : List (ℕ × ℕ) := [(9479870643,1073),(9475475200,1074),(9473279007,1075),(9460123198,1076),(9453558986,1077),(9436098875,1078),(9429567949,1079),(9420874098,1080),(9416533182,1081),(9407863339,1082),(9403534401,1083),(9397048460,1084),(9388414442,1085),(9381949334,1086),(9375493124,1087),(9362607325,1088)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1072 := recordedBatch d_s_4_1072 1072 0x78adbaf078e93f6079114da079396a407968141079905c2079b2160079e102f07a02e0f07a31ff607a5a97307aa477f07acd44c07b0a29807b25c9207b48183

private theorem s_5_1056 : rowTree 5 1056 = 4146244380 := by
  exact glueRows (by decide) s_4_1056.property s_4_1072.property (by decide)

private theorem s_6_1024 : rowTree 6 1024 = 8524680438 := by
  exact glueRows (by decide) s_5_1024 s_5_1056 (by decide)

private def d_s_4_1088 : List (ℕ × ℕ) := [(9356177698,1089),(9351896185,1090),(9345481257,1091),(9339075123,1092),(9330547261,1093),(9311416397,1094),(9307175743,1095),(9286030280,1096),(9281812712,1097),(9269182963,1098),(9267081346,1099),(9256587538,1100),(9250302654,1101),(9248209588,1102),(9237758453,1103),(9225248228,1104)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1088 := recordedBatch d_s_4_1088 1088 0x75ce0160760752c0763aa5607654e3c0767bb94076af2f5076c990407703a99077246ac077783e6077992fd077e71ad078152990783ce190786491607885e6f

private def d_s_4_1104 : List (ℕ × ℕ) := [(9223166484,1105),(9219005814,1106),(9198258642,1107),(9192052688,1108),(9161148106,1109),(9154992110,1110),(9150892707,1111),(9142704904,1112),(9132490733,1113),(9120263812,1114),(9114162621,1115),(9112130705,1116),(9083778703,1117),(9081760310,1118),(9075710509,1119),(9071681783,1120)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1104 := recordedBatch d_s_4_1104 1104 0x72cb172072ea5b50730f9cf07328f8907390a10073aa1dc073cfbbc0740794d074398cd0746596a0748570e074ab6ae0751b80e07541d4e07593935075b3eb1

private theorem s_5_1088 : rowTree 5 1088 = 3948066326 := by
  exact glueRows (by decide) s_4_1088.property s_4_1104.property (by decide)

private def d_s_4_1120 : List (ℕ × ℕ) := [(9069668762,1121),(9053596694,1122),(9041579975,1123),(9039580289,1124),(9033586534,1125),(9023614588,1126),(9015652868,1127),(8991851782,1128),(8979998303,1129),(8974083275,1130),(8956384853,1131),(8950500881,1132),(8946582527,1133),(8932895263,1134),(8927042104,1135),(8923144258,1136)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1120 := recordedBatch d_s_4_1120 1120 0x6fe490f07002b6f07026a9d07061c4f070801ed070a43c7070eb5690710fb7507145a280719ef32071c9888071fa2b40721f1420723827a0726efc1072b1ddc

private def d_s_4_1136 : List (ℕ × ℕ) := [(8911471116,1137),(8903705974,1138),(8897890993,1139),(8886283786,1140),(8882421444,1141),(8876634222,1142),(8865082372,1143),(8859317714,1144),(8847810862,1145),(8845895958,1146),(8830606519,1147),(8811568885,1148),(8807771205,1149),(8805873592,1150),(8796397778,1151),(8779392606,1152)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1136 := recordedBatch d_s_4_1136 1136 0x6d18d3806d5c8ed06d8a61f06da230a06dbf90a06e0981906e4876006e6081606e94a4b06eb805e06eec59006f0fd6f06f2dbdb06f6259806f861d606faf92f

private theorem s_5_1120 : rowTree 5 1120 = 3752665586 := by
  exact glueRows (by decide) s_4_1120.property s_4_1136.property (by decide)

private theorem s_6_1088 : rowTree 6 1088 = 7700731912 := by
  exact glueRows (by decide) s_5_1088 s_5_1120 (by decide)

private theorem s_7_1024 : rowTree 7 1024 = 16225412350 := by
  exact glueRows (by decide) s_6_1024 s_6_1088 (by decide)

private def d_s_4_1152 : List (ℕ × ℕ) := [(8771855838,1153),(8768092304,1154),(8754945330,1155),(8751196291,1156),(8749322974,1157),(8743707835,1158),(8723180509,1159),(8717598864,1160),(8704602763,1161),(8699044860,1162),(8693494050,1163),(8684258425,1164),(8678726463,1165),(8676884041,1166),(8667683655,1167),(8665845919,1168)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1152 := recordedBatch d_s_4_1152 1152 0x6ab094806ac7a4a06af3ddd06b0af8a06b2cc7606b5951c06b7b37406b9d2ce06bd4c0806bf6d6506c446c906c66c8006c7e48206c9b3f506cd3a7106cf0bc2

private def d_s_4_1168 : List (ℕ × ℕ) := [(8662172783,1169),(8660337382,1170),(8640199191,1171),(8638373090,1172),(8634723202,1173),(8629254149,1174),(8623792019,1175),(8612888479,1176),(8607447041,1177),(8594777053,1178),(8585749874,1179),(8574942259,1180),(8569548648,1181),(8562367712,1182),(8558781756,1183),(8526642803,1184)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1168 := recordedBatch d_s_4_1168 1168 0x6808c2306875e3c068917ea068b75b5068d82f906908a1806933f2d06969cae0698af54069bbd31069dd205069fe72106a1a9bb06a3181006a7d37806a94382

private theorem s_5_1152 : rowTree 5 1152 = 3576890247 := by
  exact glueRows (by decide) s_4_1152.property s_4_1168.property (by decide)

private def d_s_4_1184 : List (ℕ × ℕ) := [(8514209411,1185),(8503581041,1186),(8498276801,1187),(8494744316,1188),(8489451090,1189),(8487688148,1190),(8477125848,1191),(8471854550,1192),(8461331596,1193),(8447341588,1194),(8445596089,1195),(8436879405,1196),(8429919001,1197),(8410836974,1198),(8409106527,1199),(8398738780,1200)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1184 := recordedBatch d_s_4_1184 1184 0x658d129065bb374065d0d8c06617c540663c60a0666613a0667bf5d066b4c3a066e3aad06703b2306732d1c06748eee067691d306784477067a487d067d4059

private def d_s_4_1200 : List (ℕ × ℕ) := [(8393564488,1201),(8390118500,1202),(8384954821,1203),(8369501848,1204),(8367788366,1205),(8357522191,1206),(8352398544,1207),(8348986268,1208),(8338766148,1209),(8331966624,1210),(8326874254,1211),(8316708165,1212),(8313324982,1213),(8308255366,1214),(8298134661,1215),(8293083550,1216)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1200 := recordedBatch d_s_4_1200 1200 0x635a8040637905f063a5d3f063c47e2063de7710640b8f20642a5dd0644e05e0647b58b064958c1064b491d064e221d064f79c406533f14065532fd0656db52

private theorem s_5_1184 : rowTree 5 1184 = 3407877921 := by
  exact glueRows (by decide) s_4_1184.property s_4_1200.property (by decide)

private theorem s_6_1152 : rowTree 6 1152 = 6984768168 := by
  exact glueRows (by decide) s_5_1152 s_5_1184 (by decide)

private def d_s_4_1216 : List (ℕ × ℕ) := [(8291401212,1217),(8281321502,1218),(8271266270,1219),(8267919950,1220),(8256229123,1221),(8251228884,1222),(8237924473,1223),(8232946374,1224),(8231288345,1225),(8223008203,1226),(8216396075,1227),(8201557595,1228),(8196623338,1229),(8168774313,1230),(8167142027,1231),(8144358329,1232)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1216 := recordedBatch d_s_4_1216 1216 0x60b951e061089970611d0340617a82506198403061d1a01061f42510621b5ed062302830624e342062838a2062a1c59062d2bb2062ec63506318cd806345673

private def d_s_4_1232 : List (ℕ × ℕ) := [(8142735785,1233),(8124930380,1234),(8120087866,1235),(8118474978,1236),(8110420136,1237),(8100775399,1238),(8099170172,1239),(8094358308,1240),(8091153573,1241),(8084751711,1242),(8067198712,1243),(8062424751,1244),(8060834686,1245),(8052893759,1246),(8046552274,1247),(8043385275,1248)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1232 := recordedBatch d_s_4_1232 1232 0x5ea7b7d05ebfeb305ee0e1605f0658105f1a49805f36f5705f76fac05f9856805fb0d1105fcdce205fe1e6b0600c525060326120604691906063cd3060a4fd3

private theorem s_5_1216 : rowTree 5 1216 = 3249741152 := by
  exact glueRows (by decide) s_4_1216.property s_4_1232.property (by decide)

private def d_s_4_1248 : List (ℕ × ℕ) := [(8038639448,1249),(8032320384,1250),(8029164576,1251),(8019712013,1252),(8005574826,1253),(7996177692,1254),(7980564732,1255),(7977449453,1256),(7972781093,1257),(7968118194,1258),(7961909472,1259),(7958808738,1260),(7957259277,1261),(7944885271,1262),(7935629992,1263),(7934089542,1264)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1248 := recordedBatch d_s_4_1248 1248 0x5c87d9505c9b23305cc37db05cf480d05d07e5005d1f96705d3fc4405d5bbfc05d77c3205d8f78f05dc994305df2b1a05e28d9605e523ef05e6a53305e8b26a

private def d_s_4_1264 : List (ℕ × ℕ) := [(7926396252,1265),(7920252354,1266),(7912585863,1267),(7911054345,1268),(7907993088,1269),(7903405641,1270),(7892722270,1271),(7883588056,1272),(7866896790,1273),(7860844749,1274),(7839735739,1275),(7838232290,1276),(7835227121,1277),(7820235774,1278),(7817244387,1279),(7815749551,1280)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1264 := recordedBatch d_s_4_1264 1264 0x5a5869e05a6b20505a81e5105ab92ed05ad00b205ae2dd505b2aee605b4a31705b8667705bae20705bda31a05bf59e305c0ce9805c2011505c4404905c63d42

private theorem s_5_1248 : rowTree 5 1248 = 3101498879 := by
  exact glueRows (by decide) s_4_1248.property s_4_1264.property (by decide)

private theorem s_6_1216 : rowTree 6 1216 = 6351240031 := by
  exact glueRows (by decide) s_5_1216 s_5_1248 (by decide)

private theorem s_7_1152 : rowTree 7 1152 = 13336008199 := by
  exact glueRows (by decide) s_6_1152 s_6_1216 (by decide)

private theorem s_8_1024 : rowTree 8 1024 = 29561420549 := by
  exact glueRows (by decide) s_7_1024 s_7_1152 (by decide)

private def d_s_4_1280 : List (ℕ × ℕ) := [(7812761593,1281),(7802321709,1282),(7794881715,1283),(7785972431,1284),(7784489530,1285),(7775603971,1286),(7763788066,1287),(7762313603,1288),(7741729761,1289),(7735868700,1290),(7719796444,1291),(7713968534,1292),(7711057877,1293),(7706696007,1294),(7702339070,1295),(7692192016,1296)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1280 := recordedBatch d_s_4_1280 1280 0x58244330584db8105867c1605881c9505897ecc058b5ed3058ef9370590dc3c05953a700596613905994743059baede059cd80b059f42a205a16d2505a41afc

private def d_s_4_1296 : List (ℕ × ℕ) := [(7689297766,1297),(7683515796,1298),(7674859126,1299),(7670538102,1300),(7666221940,1301),(7663347197,1302),(7649005759,1303),(7646143911,1304),(7633292049,1305),(7631866730,1306),(7623325986,1307),(7619062778,1308),(7616223288,1309),(7611968018,1310),(7602057523,1311),(7589353314,1312)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1296 := recordedBatch d_s_4_1296 1296 0x5630700056601e2056886fc056a1be7056b748f056d0a04056f5750057074ba05737b7f0574d83705781fb105797d1a057b17b3057cb38e057f0a330580e500

private theorem s_5_1280 : rowTree 5 1280 = 2958180704 := by
  exact glueRows (by decide) s_4_1280.property s_4_1296.property (by decide)

private def d_s_4_1312 : List (ℕ × ℕ) := [(7582313751,1313),(7576691496,1314),(7569675391,1315),(7547310918,1316),(7543132283,1317),(7536178164,1318),(7532011845,1319),(7527850129,1320),(7526463912,1321),(7522308323,1322),(7511249155,1323),(7507110345,1324),(7505731756,1325),(7497470838,1326),(7493347195,1327),(7474163349,1328)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1312 := recordedBatch d_s_4_1312 1312 0x54245e9054646250547ccf5054a03d8054b17fa054ca175054f4f300550d9230551ef1c05537a0b055506780557091b05589669055d28c9055f30500560fcad

private def d_s_4_1328 : List (ℕ × ℕ) := [(7472796832,1329),(7465971737,1330),(7460520631,1331),(7449642263,1332),(7445571049,1333),(7440149681,1334),(7436088834,1335),(7429330596,1336),(7413160837,1337),(7399739708,1338),(7393047350,1339),(7391710331,1340),(7385032483,1341),(7383698361,1342),(7375703740,1343),(7373042712,1344)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1328 := recordedBatch d_s_4_1328 1328 0x5245db00525a0280527c14f0528cd02052ab7da052bc372052dafab0530b6a30534311b053622af0537a2a305395d9a053adf3b053d7ee9053f3d3805413446

private theorem s_5_1312 : rowTree 5 1312 = 2822583538 := by
  exact glueRows (by decide) s_4_1312.property s_4_1328.property (by decide)

private theorem s_6_1280 : rowTree 6 1280 = 5780764242 := by
  exact glueRows (by decide) s_5_1280 s_5_1312 (by decide)

private def d_s_4_1344 : List (ℕ × ℕ) := [(7369054769,1345),(7355792725,1346),(7353146042,1347),(7351823415,1348),(7343897633,1349),(7332040950,1350),(7325470432,1351),(7324157741,1352),(7317601338,1353),(7316291466,1354),(7313673128,1355),(7300609498,1356),(7290192147,1357),(7273327213,1358),(7270739531,1359),(7265569687,1360)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1344 := recordedBatch d_s_4_1344 1344 0x505e77605078b170508c3f7050c4d56050ecd500511ba3a0512f6250513fc5a0515dd150516e3b90518c53d051b8338051d9ed9051ea806051fe85a0522e40a

private def d_s_4_1360 : List (ℕ × ℕ) := [(7261697126,1361),(7259117712,1362),(7251390451,1363),(7247532986,1364),(7242396080,1365),(7234704359,1366),(7227028958,1367),(7223197362,1368),(7220645221,1369),(7215546346,1370),(7201561497,1371),(7200292834,1372),(7190159605,1373),(7181316397,1374),(7175013126,1375),(7171236472,1376)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1360 := recordedBatch d_s_4_1360 1360 0x4ea0b3a04eb6e2104ed3a5604ef6e0504f1d89b04f2d6ab04f5e03904f77d0f04f8b0d504fa196604fc227704fe2ca804ffcc3105013817050343a405047ac1

private theorem s_5_1344 : rowTree 5 1344 = 2697209012 := by
  exact glueRows (by decide) s_4_1344.property s_4_1360.property (by decide)

private def d_s_4_1376 : List (ℕ × ℕ) := [(7163695079,1377),(7156169531,1378),(7147409683,1379),(7143662025,1380),(7141165768,1381),(7128710609,1382),(7126224789,1383),(7118777719,1384),(7115060018,1385),(7113821647,1386),(7110109120,1387),(7106400465,1388),(7096529608,1389),(7091604455,1390),(7078095467,1391),(7076869929,1392)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1376 := recordedBatch d_s_4_1376 1376 0x4ce9dda04cf935a04d27d4204d40aa304d660ee04d7bda904d91a3004da122f04db705f04dd667504de91b304e1559d04e282f804e3e3a404e611b304e80e2d

private def d_s_4_1392 : List (ℕ × ℕ) := [(7059756849,1393),(7054882588,1394),(7051231308,1395),(7048799220,1396),(7036663902,1397),(7034241851,1398),(7026985692,1399),(7012518191,1400),(7000507369,1401),(6998110140,1402),(6993320605,1403),(6987342897,1404),(6986148581,1405),(6976608735,1406),(6975418086,1407),(6968282717,1408)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1392 := recordedBatch d_s_4_1392 1392 0x4b1698e04b3478704b4360304b6759904b7641204b914c704ba954604bbb60604be5d8c04c1667804c34da604c4719104c71eec04c8435c04c999db04cb2244

private theorem s_5_1376 : rowTree 5 1376 = 2576681767 := by
  exact glueRows (by decide) s_4_1376.property s_4_1392.property (by decide)

private theorem s_6_1344 : rowTree 6 1344 = 5273890779 := by
  exact glueRows (by decide) s_5_1344 s_5_1376 (by decide)

private theorem s_7_1280 : rowTree 7 1280 = 11054655021 := by
  exact glueRows (by decide) s_6_1280 s_6_1344 (by decide)

private def d_s_4_1408 : List (ℕ × ℕ) := [(6961161930,1409),(6941065174,1410),(6939886624,1411),(6937530726,1412),(6933999877,1413),(6926948949,1414),(6923428860,1415),(6919912346,1416),(6915229215,1417),(6911721024,1418),(6909384207,1419),(6908216391,1420),(6904715309,1421),(6890746401,1422),(6888423742,1423),(6876833898,1424)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1408 := recordedBatch d_s_4_1408 1408 0x49758800499e22a049af8f6049de18a049f286904a0128a04a12b3604a2731004a3eaaf04a5331b04a67c9b04a8547904a99f0204aaba9304aba66c04af8c82

private def d_s_4_1424 : List (ℕ × ℕ) := [(6871053589,1425),(6867590065,1426),(6864130032,1427),(6856070163,1428),(6853770818,1429),(6850324692,1430),(6846882029,1431),(6845735244,1432),(6838862591,1433),(6835431436,1434),(6829720490,1435),(6828579446,1436),(6822879939,1437),(6819464799,1438),(6808105651,1439),(6805838361,1440)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1424 := recordedBatch d_s_4_1424 1424 0x480d7e20481e7870484600c04859d9b048735e104881a6d0489b434048af3c1048cbd7f048da32f048ee47a049025bf0491398b0493331e0494762f0495b8ca

private theorem s_5_1408 : rowTree 5 1408 = 2465015200 := by
  exact glueRows (by decide) s_4_1408.property s_4_1424.property (by decide)

private def d_s_4_1440 : List (ℕ × ℕ) := [(6791137704,1441),(6788881700,1442),(6787754260,1443),(6784374185,1444),(6772009324,1445),(6770887480,1446),(6757454290,1447),(6755220606,1448),(6751872846,1449),(6750757664,1450),(6748528403,1451),(6745187272,1452),(6731855765,1453),(6728531118,1454),(6724103360,1455),(6721891666,1456)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1440 := recordedBatch d_s_4_1440 1440 0x468b22d0469bac6046b1af8046c501d046f0e620470448f04714f2604722e6204736546047470d9047736100478168a047ab29f047bed0b047ccf0c047ddd36

private def d_s_4_1456 : List (ℕ × ℕ) := [(6720786364,1457),(6702051697,1458),(6698756416,1459),(6694367746,1460),(6685607635,1461),(6679052582,1462),(6677961323,1463),(6672510370,1464),(6671421248,1465),(6665980963,1466),(6662721049,1467),(6658379453,1468),(6656210777,1469),(6651877659,1470),(6645388550,1471),(6633524673,1472)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1456 := recordedBatch d_s_4_1456 1456 0x4503ef10452b958045463da0455bb560456be15045816e304594524045ac7d7045ba208045d26b1045e010e045fb0290461b6fd046312be0464456c0467d547

private theorem s_5_1440 : rowTree 5 1440 = 2364305136 := by
  exact glueRows (by decide) s_4_1440.property s_4_1456.property (by decide)

private theorem s_6_1408 : rowTree 6 1408 = 4829320336 := by
  exact glueRows (by decide) s_5_1408 s_5_1440 (by decide)

private def d_s_4_1472 : List (ℕ × ℕ) := [(6630296419,1473),(6622776031,1474),(6620630481,1475),(6606718221,1476),(6604583061,1477),(6603515999,1478),(6597120858,1479),(6591801028,1480),(6587551338,1481),(6585428547,1482),(6581187066,1483),(6574835080,1484),(6572720475,1485),(6565330058,1486),(6562167821,1487),(6553750064,1488)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1472 := recordedBatch d_s_4_1472 1472 0x4397497043b6374043c879d043e4fe4043f4c300440ec0504423b65044338ca04448880044602100447a5b104487ba804497a85044c4278044d420a044f145d

private def d_s_4_1488 : List (ℕ × ℕ) := [(6550598970,1489),(6546402222,1490),(6544305864,1491),(6541163843,1492),(6538024838,1493),(6533844181,1494),(6530712195,1495),(6525498886,1496),(6519253892,1497),(6518214221,1498),(6515097198,1499),(6511983155,1500),(6503693575,1501),(6499556695,1502),(6496457486,1503),(6493361232,1504)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1488 := recordedBatch d_s_4_1488 1488 0x425e1e60426feef04281c6904296192042b4632042c657d042d84a6042e5486042fec4504315d2f04327e7f0433c6f60434e93904360b6b043705840438515c

private theorem s_5_1472 : rowTree 5 1472 = 2268453205 := by
  exact glueRows (by decide) s_4_1472.property s_4_1488.property (by decide)

private def d_s_4_1504 : List (ℕ × ℕ) := [(6487177569,1505),(6482033506,1506),(6481005673,1507),(6477924126,1508),(6468697044,1509),(6466650150,1510),(6463582237,1511),(6460517233,1512),(6457455135,1513),(6451339638,1514),(6442188080,1515),(6438129050,1516),(6435088133,1517),(6430026315,1518),(6425982592,1519),(6416902783,1520)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1504 := recordedBatch d_s_4_1504 1504 0x410335a04122eff04136b7c0414cfca0415e6f5041725db04192636041ab42b041bcdbf041ce726041e022d041ef5db0420fa9f042216a70422e44604244f10

private def d_s_4_1520 : List (ℕ × ℕ) := [(6414888531,1521),(6407848597,1522),(6404836210,1523),(6395816020,1524),(6390815773,1525),(6386821201,1526),(6381835003,1527),(6375861832,1528),(6374867391,1529),(6371885926,1530),(6365931356,1531),(6359987905,1532),(6342223954,1533),(6340256306,1534),(6337307121,1535),(6333379139,1536)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1520 := recordedBatch d_s_4_1520 1520 0x3f9ccd803faffdd03fc0e9803fcf80f040034ac0401b612040336fa040448c504050f5e040691bd0407f05004092956040a88c2040c80d4040d959f040f43b7

private theorem s_5_1504 : rowTree 5 1504 = 2180207071 := by
  exact glueRows (by decide) s_4_1504.property s_4_1520.property (by decide)

private theorem s_6_1472 : rowTree 6 1472 = 4448660276 := by
  exact glueRows (by decide) s_5_1472 s_5_1504 (by decide)

private theorem s_7_1408 : rowTree 7 1408 = 9277980612 := by
  exact glueRows (by decide) s_6_1408 s_6_1472 (by decide)

private theorem s_8_1280 : rowTree 8 1280 = 20332635633 := by
  exact glueRows (by decide) s_7_1280 s_7_1408 (by decide)

private theorem s_9_1024 : rowTree 9 1024 = 49894056182 := by
  exact glueRows (by decide) s_8_1024 s_8_1280 (by decide)

private def d_s_4_1536 : List (ℕ × ℕ) := [(6331416974,1537),(6328476004,1538),(6327496288,1539),(6325537766,1540),(6316739398,1541),(6310887404,1542),(6307965472,1543),(6304073768,1544),(6301158140,1545),(6298245208,1546),(6296304748,1547),(6287587459,1548),(6286620361,1549),(6284687057,1550),(6283720851,1551),(6272149509,1552)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1536 := recordedBatch d_s_4_1536 1536 0x3e6fe2303e9482e03ea092703eaee3e03ebaf6d03ed91ab03ee77c003ef828503f08d2103f1bc8d03f2c7fb03f4423703f6298003f7121103f7d63603f8e3fe

private def d_s_4_1552 : List (ℕ × ℕ) := [(6270225094,1553),(6267340685,1554),(6264458928,1555),(6257745124,1556),(6243406748,1557),(6240546954,1558),(6238641880,1559),(6235786448,1560),(6230083420,1561),(6227235815,1562),(6217762573,1563),(6215871382,1564),(6212092450,1565),(6210204706,1566),(6206432659,1567),(6203606629,1568)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1552 := recordedBatch d_s_4_1552 1552 0x3d3646103d4664803d58a9903d669ab03d78f1703d86f4b03da670e03db6b5403dcd8bd03dddd0b03debf5a03dfc4f003e2751103e409cf03e5124203e61a52

private theorem s_5_1536 : rowTree 5 1536 = 2093496303 := by
  exact glueRows (by decide) s_4_1536.property s_4_1552.property (by decide)

private def d_s_4_1568 : List (ℕ × ℕ) := [(6200783171,1569),(6198902294,1570),(6184832000,1571),(6183896251,1572),(6179221751,1573),(6173621671,1574),(6169893920,1575),(6165240557,1576),(6161522918,1577),(6150396851,1578),(6147621610,1579),(6142078635,1580),(6140233197,1581),(6133782888,1582),(6131942431,1583),(6129183816,1584)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1568 := recordedBatch d_s_4_1568 1568 0x3bf41eb03c03ce803c1161503c298fa03c3729303c4d40403c5d0c103c7fee103c91ee103ca61b603cb821003cce7c503ce2bd403cee6c003d184ba03d263ce

private def d_s_4_1584 : List (ℕ × ℕ) := [(6128264829,1585),(6115427886,1586),(6109029560,1587),(6101733563,1588),(6100822789,1589),(6095363847,1590),(6092638037,1591),(6090822185,1592),(6081759136,1593),(6077237718,1594),(6074528093,1595),(6071820883,1596),(6069116085,1597),(6065513434,1598),(6061016130,1599),(6055628161,1600)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1584 := recordedBatch d_s_4_1584 1584 0x3ab8ab303ace06003ae16b003af2c2903b021c003b117ad03b20de603b3463703b5237103b5f9b703b6f1aa03b84cbd03b9028203baa1dd03bc20cd03be8a33

private theorem s_5_1568 : rowTree 5 1568 = 2009796615 := by
  exact glueRows (by decide) s_4_1568.property s_4_1584.property (by decide)

private theorem s_6_1536 : rowTree 6 1536 = 4103292918 := by
  exact glueRows (by decide) s_5_1536 s_5_1568 (by decide)

private def d_s_4_1600 : List (ℕ × ℕ) := [(6049354292,1601),(6044880910,1602),(6038629279,1603),(6031500372,1604),(6025276373,1605),(6020838517,1606),(6014636491,1607),(6011982389,1608),(6004916223,1609),(6002270692,1610),(5998746940,1611),(5996106840,1612),(5989077921,1613),(5980314913,1614),(5975943018,1615),(5975069406,1616)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1600 := recordedBatch d_s_4_1600 1600 0x39722d20397d15f0398fd2d039ac723039c5424039d43b8039e52d5039f42ab03a0d1a603a1c2d303a3343003a465ae03a5d8c403a76cc903a8e0b603aa14b4

private def d_s_4_1616 : List (ℕ × ℕ) := [(5972450102,1617),(5970705175,1618),(5969833093,1619),(5968089695,1620),(5962865603,1621),(5961995810,1622),(5957650649,1623),(5956782376,1624),(5954179077,1625),(5944653083,1626),(5942060373,1627),(5941196638,1628),(5939469923,1629),(5931712107,1630),(5928270690,1631),(5923974531,1632)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1616 := recordedBatch d_s_4_1616 1616 0x3871d8e038843c603894aed038aec6d038bb7cf038c6460038d4ec3038f312403901bf10390c9a60391f4810392a2300393ebbf0394b9220395676503963573

private theorem s_5_1600 : rowTree 5 1600 = 1928741360 := by
  exact glueRows (by decide) s_4_1600.property s_4_1616.property (by decide)

private def d_s_4_1632 : List (ℕ × ℕ) := [(5920542084,1633),(5911123331,1634),(5910268567,1635),(5905998450,1636),(5898327769,1637),(5892375445,1638),(5890676987,1639),(5889828125,1640),(5888131135,1641),(5880506766,1642),(5879660832,1643),(5877969695,1644),(5875434813,1645),(5872058369,1646),(5867843267,1647),(5867000972,1648)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1632 := recordedBatch d_s_4_1632 1632 0x376818e03772a05037848d803794ad7037a2f6a037af62a037b9eeb037d38c0037e0018037ea9b2037f71920380d0e003826d0e038390ff03843bbf038616d8

private def d_s_4_1648 : List (ℕ × ℕ) := [(5854395513,1649),(5852718877,1650),(5840174648,1651),(5839340278,1652),(5835172000,1653),(5834339058,1654),(5826853272,1655),(5825192371,1656),(5817730023,1657),(5815246820,1658),(5809460916,1659),(5805335171,1660),(5804510726,1661),(5802862536,1662),(5794635610,1663),(5779885777,1664)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1648 := recordedBatch d_s_4_1648 1648 0x36205120364903a0366374b0366f8fb03679d9f0368b671036a09a2036ae905036c76ca036d3a03036ec9e3036f705603708bea037132f5037375ed03743b14

private theorem s_5_1632 : rowTree 5 1632 = 1855250576 := by
  exact glueRows (by decide) s_4_1632.property s_4_1648.property (by decide)

private theorem s_6_1600 : rowTree 6 1600 = 3783991936 := by
  exact glueRows (by decide) s_5_1600 s_5_1632 (by decide)

private theorem s_7_1536 : rowTree 7 1536 = 7887284854 := by
  exact glueRows (by decide) s_6_1536 s_6_1600 (by decide)

private def d_s_4_1664 : List (ℕ × ℕ) := [(5777434769,1665),(5775801918,1666),(5773354372,1667),(5767651489,1668),(5766024162,1669),(5757901285,1670),(5753848423,1671),(5748183992,1672),(5739305241,1673),(5736888522,1674),(5736083401,1675),(5724033649,1676),(5719227912,1677),(5715229291,1678),(5708045845,1679),(5707248799,1680)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1664 := recordedBatch d_s_4_1664 1664 0x34fd0b20350704b0351ed6c0352fcd10354278903564ef10356f01e0357c8df03598293035acd15035be055035d81e7035e4008035f8dbf0360699c036128db

private def d_s_4_1680 : List (ℕ × ℕ) := [(5705655374,1681),(5700085388,1682),(5697701579,1683),(5688977977,1684),(5681860329,1685),(5681070578,1686),(5676336681,1687),(5673972690,1688),(5672397790,1689),(5669250610,1690),(5667678330,1691),(5664536383,1692),(5662182209,1693),(5658262930,1694),(5657479725,1695),(5652785046,1696)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1680 := recordedBatch d_s_4_1680 1680 0x340533c034176100342120903431af40343edee0344dbbe034593420346824503473a7503480e68034933cc0349d196034b4a73034cfae9034dd15d034f15f1

private theorem s_5_1664 : rowTree 5 1664 = 1778302264 := by
  exact glueRows (by decide) s_4_1664.property s_4_1680.property (by decide)

private def d_s_4_1696 : List (ℕ × ℕ) := [(5645757618,1697),(5641861036,1698),(5636414849,1699),(5630203495,1700),(5624779780,1701),(5623232066,1702),(5620912092,1703),(5618594030,1704),(5617821768,1705),(5615506255,1706),(5613963639,1707),(5613192649,1708),(5602420982,1709),(5601653159,1710),(5590925692,1711),(5588632293,1712)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1696 := recordedBatch d_s_4_1696 1696 0x32fc1b903308ea603327b69033314f20335036403359daf03365210033721030337bb9b03388af003395a87033a0f91033b4919033c9e9a033dd9d3033ee07b

private def d_s_4_1712 : List (ℕ × ℕ) := [(5587868244,1713),(5586340774,1714),(5584051134,1715),(5578715932,1716),(5577193460,1717),(5572631028,1718),(5567317615,1719),(5561257538,1720),(5555965782,1721),(5554455701,1722),(5552192118,1723),(5549176875,1724),(5546917592,1725),(5545412424,1726),(5543156204,1727),(5540901820,1728)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1712 := recordedBatch d_s_4_1712 1712 0x321950103225e180323275f0323d72c0324a09a032583d703264dca0326fe1303282eab03297a83032aabe1032bc4b5032c772d032daa47032e7701032f295e

private theorem s_5_1696 : rowTree 5 1696 = 1710785805 := by
  exact glueRows (by decide) s_4_1696.property s_4_1712.property (by decide)

private theorem s_6_1664 : rowTree 6 1664 = 3489088069 := by
  exact glueRows (by decide) s_5_1664 s_5_1696 (by decide)

private def d_s_4_1728 : List (ℕ × ℕ) := [(5538649268,1729),(5535648713,1730),(5534149655,1731),(5531153972,1732),(5529657346,1733),(5524425529,1734),(5518458418,1735),(5515479694,1736),(5513247761,1737),(5511760808,1738),(5507304760,1739),(5504338061,1740),(5498414243,1741),(5497674662,1742),(5493979740,1743),(5491027376,1744)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1728 := recordedBatch d_s_4_1728 1728 0x3134d3103142a7c0315214a0315b50c0316f7100317d5990318e68a0319942f031a5ab7031b3a11031c7eba031dab34031e5a24031f3bda031fea7e0320cc69

private def d_s_4_1744 : List (ℕ × ℕ) := [(5489552384,1745),(5487341381,1746),(5477780912,1747),(5475579379,1748),(5471914087,1749),(5468985385,1750),(5467522209,1751),(5465328913,1752),(5460947595,1753),(5455844927,1754),(5444942686,1755),(5443492345,1756),(5438422231,1757),(5430473962,1758),(5427589439,1759),(5423268397,1760)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1744 := recordedBatch d_s_4_1744 1744 0x302e6080303ed700304c57c030645c9030766a103080fbe0309f2e7030b1570030c20ee030ce386030d8e48030e69bc030f5da7031021f40311dbff0312a102

private theorem s_5_1728 : rowTree 5 1728 = 1649473415 := by
  exact glueRows (by decide) s_4_1728.property s_4_1744.property (by decide)

private def d_s_4_1760 : List (ℕ × ℕ) := [(5421829578,1761),(5419672780,1762),(5416799718,1763),(5413212671,1764),(5411062722,1765),(5406052810,1766),(5402479978,1767),(5400338544,1768),(5399625110,1769),(5396060766,1770),(5391789760,1771),(5387525509,1772),(5382559067,1773),(5380433394,1774),(5378309398,1775),(5371947463,1776)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1760 := recordedBatch d_s_4_1760 1760 0x2f4d6c002f61de602f6da1502f7962e02f8b09a02f9b3a502fab79602fba3ab02fc326c02fcf06202fddd9102fefa2102ffb8cd0300a74303017e5503023ddb

private def d_s_4_1776 : List (ℕ × ℕ) := [(5368419554,1777),(5366305032,1778),(5363488258,1779),(5357161318,1780),(5355757357,1781),(5353652796,1782),(5352951643,1783),(5350849286,1784),(5347349025,1785),(5346649522,1786),(5343154752,1787),(5340362223,1788),(5338269741,1789),(5336178899,1790),(5332697798,1791),(5332002123,1792)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1776 := recordedBatch d_s_4_1776 1776 0x2e86aa402e8f57f02e9dc0b02ea946b02eb4d6802ec1d3502ed040902ed8fc002ee771d02ef314002efbd5c02f0775d02f11adb02f25f6a02f331d202f3ecdb

private theorem s_5_1760 : rowTree 5 1760 = 1587314736 := by
  exact glueRows (by decide) s_4_1760.property s_4_1776.property (by decide)

private theorem s_6_1728 : rowTree 6 1728 = 3236788151 := by
  exact glueRows (by decide) s_5_1728 s_5_1760 (by decide)

private theorem s_7_1664 : rowTree 7 1664 = 6725876220 := by
  exact glueRows (by decide) s_6_1664 s_6_1728 (by decide)

private theorem s_8_1536 : rowTree 8 1536 = 14613161074 := by
  exact glueRows (by decide) s_7_1536 s_7_1664 (by decide)

private def d_s_4_1792 : List (ℕ × ℕ) := [(5325749205,1793),(5322281695,1794),(5321588734,1795),(5317434759,1796),(5316051541,1797),(5313978063,1798),(5311215941,1799),(5307767323,1800),(5303634889,1801),(5298821841,1802),(5294703319,1803),(5293331901,1804),(5290591195,1805),(5287169300,1806),(5285118287,1807),(5283068865,1808)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1792 := recordedBatch d_s_4_1792 1792 0x2db031502dbb75002dc6c3502dd4cfd02de184902deb7d702dfafad02e0bf2702e1b8d202e29b8602e368f102e41fd102e4c02002e5bb5402e6459502e72ad3

private def d_s_4_1808 : List (ℕ × ℕ) := [(5276248922,1809),(5274887046,1810),(5270126010,1811),(5264695340,1812),(5259952677,1813),(5256570288,1814),(5253867507,1815),(5250492938,1816),(5246449172,1817),(5245775816,1818),(5239723386,1819),(5237709012,1820),(5233684906,1821),(5230336205,1822),(5226323416,1823),(5225655216,1824)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1808 := recordedBatch d_s_4_1808 1808 0x2ccbacc02cd408202ce30bd02cf0ce202cffead02d0afee02d1e28802d2694702d35c1902d4392202d5012802d5df3002d6e99c02d80a6202d9169702d9b465

private theorem s_5_1792 : rowTree 5 1792 = 1531044709 := by
  exact glueRows (by decide) s_4_1792.property s_4_1808.property (by decide)

private def d_s_4_1824 : List (ℕ × ℕ) := [(5224319329,1825),(5223651642,1826),(5219649099,1827),(5217650127,1828),(5216318330,1829),(5213656773,1830),(5212327013,1831),(5197744296,1832),(5196422640,1833),(5195762064,1834),(5194441415,1835),(5193781342,1836),(5190483494,1837),(5186531600,1838),(5184557909,1839),(5182585719,1840)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1824 := recordedBatch d_s_4_1824 1824 0x2c069ec02c116bd02c1c40702c2b04002c387dd02c40b8102c4a45c02c5284002c5c1a102c8021002c89bcd02c9609102c9fac602caaa9202cb9ac502cc2051

private def d_s_4_1840 : List (ℕ × ℕ) := [(5177989773,1841),(5176678142,1842),(5174711942,1843),(5172747235,1844),(5170784018,1845),(5168168714,1846),(5166208971,1847),(5154481654,1848),(5148637938,1849),(5147341134,1850),(5145397152,1851),(5144749484,1852),(5140866898,1853),(5138927802,1854),(5136990168,1855),(5135053995,1856)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1840 := recordedBatch d_s_4_1840 1840 0x2b3b5b902b45f5e02b5092c02b5b28d02b699b802b71ac502b7c59602b85b0102b9809802bb607d02bc0c3702bcccda02bd787602be24f302bed17302bf6935

private theorem s_5_1824 : rowTree 5 1824 = 1476111746 := by
  exact glueRows (by decide) s_4_1824.property s_4_1840.property (by decide)

private theorem s_6_1792 : rowTree 6 1792 = 3007156455 := by
  exact glueRows (by decide) s_5_1792 s_5_1824 (by decide)

private def d_s_4_1856 : List (ℕ × ℕ) := [(5133764024,1857),(5129254223,1858),(5122183379,1859),(5118334766,1860),(5117693893,1861),(5111933247,1862),(5108738488,1863),(5106823549,1864),(5098542041,1865),(5090921377,1866),(5089653480,1867),(5089019769,1868),(5087752819,1869),(5087119581,1870),(5085853577,1871),(5081427522,1872)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1856 := recordedBatch d_s_4_1856 1856 0x2a672af02a7664602a7f89502a876d502a908f702a987b202aa1a2c02ab735902ace0a502ad881b02ae57c502af77cf02aff81702b0dcbd02b226ce02b320ae

private def d_s_4_1872 : List (ℕ × ℕ) := [(5080164349,1873),(5078270768,1874),(5076378597,1875),(5073857895,1876),(5068823994,1877),(5065055118,1878),(5064427517,1879),(5051283727,1880),(5050035494,1881),(5049411610,1882),(5048164302,1883),(5040693380,1884),(5038829104,1885),(5036966205,1886),(5036345545,1887),(5030766481,1888)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1872 := recordedBatch d_s_4_1872 1872 0x299b9b2029acec5029b4aa4029becce029c8eea029ddf06029e6ee6029eebc5029f7bf802a17bfc02a1f91a02a2d80502a3de7f02a4968702a53ba002a5e106

private theorem s_5_1856 : rowTree 5 1856 = 1421975156 := by
  exact glueRows (by decide) s_4_1856.property s_4_1872.property (by decide)

private def d_s_4_1888 : List (ℕ × ℕ) := [(5029528367,1889),(5025199763,1890),(5023346927,1891),(5014718394,1892),(5009187116,1893),(5004893439,1894),(5003055545,1895),(4999995385,1896),(4996328131,1897),(4995717445,1898),(4993886282,1899),(4990227980,1900),(4981105633,1901),(4979285165,1902),(4978072258,1903),(4976254005,1904)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1888 := recordedBatch d_s_4_1888 1888 0x28cb9e1028d57b1028de36b028e8194028fff6f0290d6c3029176920291f08d0292c81e02938dd002942dba0295197402962b4602979c5d02983d3a02992b1b

private def d_s_4_1904 : List (ℕ × ℕ) := [(4974437081,1905),(4970202745,1906),(4968994259,1907),(4968390236,1908),(4961153398,1909),(4959949308,1910),(4958144268,1911),(4956340541,1912),(4948539533,1913),(4945545680,1914),(4940165864,1915),(4938375192,1916),(4935989647,1917),(4934202001,1918),(4932415649,1919),(4923503255,1920)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1904 := recordedBatch d_s_4_1904 1904 0x2801d430281904b02822b4e0282c6040283732902840ebb0285176c0285d7d502872a550287c714028863e40288ee17028a30e0028aa953028b34ac028c1c16

private theorem s_5_1888 : rowTree 5 1888 = 1368325972 := by
  exact glueRows (by decide) s_4_1888.property s_4_1904.property (by decide)

private theorem s_6_1856 : rowTree 6 1856 = 2790301128 := by
  exact glueRows (by decide) s_5_1856 s_5_1888 (by decide)

private theorem s_7_1792 : rowTree 7 1792 = 5797457583 := by
  exact glueRows (by decide) s_6_1792 s_6_1856 (by decide)

private def d_s_4_1920 : List (ℕ × ℕ) := [(4922317369,1921),(4918763135,1922),(4915214031,1923),(4914623011,1924),(4909899967,1925),(4909310224,1926),(4907541847,1927),(4906363636,1928),(4902832396,1929),(4897545057,1930),(4896958279,1931),(4895198787,1932),(4894026495,1933),(4886420261,1934),(4882917660,1935),(4881168242,1936)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1920 := recordedBatch d_s_4_1920 1920 0x274e58702757d270276491e027790ed027817ee0278b04b02792594027a28b0027af6b6027b7e3f027c1758027c8d0e027d8072027df63c027ec5b3027f94fe

private def d_s_4_1936 : List (ℕ × ℕ) := [(4877673163,1937),(4876509249,1938),(4869537413,1939),(4862585483,1940),(4859116956,1941),(4857384547,1942),(4856807352,1943),(4853347061,1944),(4845292191,1945),(4842995707,1946),(4841848282,1947),(4840128163,1948),(4836691589,1949),(4836119301,1950),(4830974797,1951),(4829262394,1952)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1936 := recordedBatch d_s_4_1936 1936 0x268b82a02694c27026a4699026ab917026b8092026c160c026c9971026d3f68026e919f026f5b98026fcee90270650302712f1b027261b80273949102741a80

private theorem s_5_1920 : rowTree 5 1920 = 1317474927 := by
  exact glueRows (by decide) s_4_1920.property s_4_1936.property (by decide)

private def d_s_4_1952 : List (ℕ × ℕ) := [(4828121466,1953),(4826411085,1954),(4824701915,1955),(4819013414,1956),(4814472263,1957),(4813905220,1958),(4812204895,1959),(4810505770,1960),(4805415587,1961),(4802592359,1962),(4800900014,1963),(4800336165,1964),(4799208862,1965),(4796955845,1966),(4795267469,1967),(4793580282,1968)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1952 := recordedBatch d_s_4_1952 1952 0x25e9124025f22cd025fb4730260572f0260d86f026149450261daf802628efe026385ad026418430264ab3002651c83026603d402670d750267a15402683549

private def d_s_4_1968 : List (ℕ × ℕ) := [(4786843389,1969),(4782362637,1970),(4780684516,1971),(4778448854,1972),(4775657215,1973),(4773983796,1974),(4770083710,1975),(4763967862,1976),(4761747804,1977),(4757313889,1978),(4755653298,1979),(4755100026,1980),(4751783093,1981),(4750678477,1982),(4750126361,1983),(4744061549,1984)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1968 := recordedBatch d_s_4_1968 1968 0x252f841025407060254754b0254f3bd0255b343025621f20256b0ca02579110025830670259432f025a144d025aa496025b55df025bf74b025c8804025d6b55

private theorem s_5_1952 : rowTree 5 1952 = 1270121760 := by
  exact glueRows (by decide) s_4_1952.property s_4_1968.property (by decide)

private theorem s_6_1920 : rowTree 6 1920 = 2587596687 := by
  exact glueRows (by decide) s_5_1920 s_5_1952 (by decide)

private def d_s_4_1984 : List (ℕ × ℕ) := [(4741860000,1985),(4736913980,1986),(4727599592,1987),(4727052828,1988),(4725413292,1989),(4720501504,1990),(4719411382,1991),(4717777142,1992),(4716144034,1993),(4713968315,1994),(4711251487,1995),(4709080278,1996),(4704202368,1997),(4702578643,1998),(4701496782,1999),(4700956038,2000)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_1984 := recordedBatch d_s_4_1984 1984 0x24840580248acbc024928b60249b44f024a9ec3024b3a42024be5dd024c823c024d0e8b024d9aa8024e1797024f0488024f9205024fff0902516c73025259bc

private def d_s_4_2000 : List (ℕ × ℕ) := [(4699874924,2001),(4697714186,2002),(4693398665,2003),(4692859782,2004),(4689629083,2005),(4686402829,2006),(4684791366,2007),(4679963620,2008),(4678892138,2009),(4677285835,2010),(4675680635,2011),(4674076536,2012),(4673542081,2013),(4671939449,2014),(4668737481,2015),(4666072524,2016)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2000 := recordedBatch d_s_4_2000 2000 0x23e9890023f3f65023ff6df0240803c0240ead1024174070241fdb002428791024302450243e8e70244738402452c7a0245e5570246512f024729d70247c4a8

private theorem s_5_1984 : rowTree 5 1984 = 1224608542 := by
  exact glueRows (by decide) s_4_1984.property s_4_2000.property (by decide)

private def d_s_4_2016 : List (ℕ × ℕ) := [(4660751727,2017),(4657565070,2018),(4652793246,2019),(4651734169,2020),(4650146456,2021),(4649617459,2022),(4645389813,2023),(4644861898,2024),(4642224121,2025),(4638536262,2026),(4637483664,2027),(4629604380,2028),(4629080047,2029),(4626460159,2030),(4623320205,2031),(4622797294,2032)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2016 := recordedBatch d_s_4_2016 2016 0x234224102348af702353d1b0235e14d02364a55023784360237fc1e0238bf05023964700239cdde023aa116023b0ae1023b92c7023c0b90023ceee0023da4df

private def d_s_4_2032 : List (ℕ × ℕ) := [(4616531572,2033),(4614967795,2034),(4610802896,2035),(4608723265,2036),(4606126362,2037),(4605607333,2038),(4602495611,2039),(4596801695,2040),(4595251253,2041),(4594734672,2042),(4590606197,2043),(4585456024,2044),(4582885269,2045),(4582371464,2046),(4579291051,2047),(4576214776,2048)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2032 := recordedBatch d_s_4_2032 2032 0x229714a022a202a022acf44022b3614022bd65f022cbff3022d8d47022df43f022e78ed022f72de023023cb02308bcf02312df80231c2230232913c023316aa

private theorem s_5_2016 : rowTree 5 2016 = 1181894579 := by
  exact glueRows (by decide) s_4_2016.property s_4_2032.property (by decide)

private theorem s_6_1984 : rowTree 6 1984 = 2406503121 := by
  exact glueRows (by decide) s_5_1984 s_5_2016 (by decide)

private theorem s_7_1920 : rowTree 7 1920 = 4994099808 := by
  exact glueRows (by decide) s_6_1920 s_6_1984 (by decide)

private theorem s_8_1792 : rowTree 8 1792 = 10791557391 := by
  exact glueRows (by decide) s_7_1792 s_7_1920 (by decide)

private theorem s_9_1536 : rowTree 9 1536 = 25404718465 := by
  exact glueRows (by decide) s_8_1536 s_8_1792 (by decide)

private theorem s_10_1024 : rowTree 10 1024 = 75298774647 := by
  exact glueRows (by decide) s_9_1024 s_9_1536 (by decide)

private theorem s_11_0 : rowTree 11 0 = 336869286725 := by
  exact glueRows (by decide) s_10_0 s_10_1024 (by decide)

private def d_s_4_2048 : List (ℕ × ℕ) := [(4571608106,2049),(4569052850,2050),(4565990311,2051),(4564460581,2052),(4563950899,2053),(4561404193,2054),(4560895193,2055),(4559368874,2056),(4556827278,2057),(4552259539,2058),(4551752578,2059),(4548713179,2060),(4547195002,2061),(4546183446,2062),(4544666956,2063),(4544161685,2064)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2048 := recordedBatch d_s_4_2048 2048 0x22079290220de0302215f710221d2c40222547d0223006c0223659d02243ca20224dae902255d4c0225c2de0226619a0226c75d02274a2f0227f8640228978f

private def d_s_4_2064 : List (ℕ × ℕ) := [(4538107175,2065),(4531063940,2066),(4530561689,2067),(4529557519,2068),(4529055601,2069),(4526547680,2070),(4526046429,2071),(4522040413,2072),(4519040552,2073),(4517042855,2074),(4511558284,2075),(4511060347,2076),(4509567195,2077),(4508572310,2078),(4508075031,2079),(4505590285,2080)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2064 := recordedBatch d_s_4_2064 2064 0x216e91a021783180217e675021857980218d6b702193a3a021a2881021ab5b6021b5ef0021c2391021c876e021d23a6021d87c0021dfa4d021e5ee2021f79b1

private theorem s_5_2048 : rowTree 5 2048 = 1140236369 := by
  exact glueRows (by decide) s_4_2048.property s_4_2064.property (by decide)

private def d_s_4_2080 : List (ℕ × ℕ) := [(4504100752,2081),(4499142746,2082),(4496173178,2083),(4493701531,2084),(4491726169,2085),(4488766380,2086),(4487287948,2087),(4485810489,2088),(4484334003,2089),(4483350219,2090),(4478928527,2091),(4478437766,2092),(4477456567,2093),(4474515548,2094),(4470111256,2095),(4469622426,2096)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2080 := recordedBatch d_s_4_2080 2080 0x20dbe7d020e2046020eed95020f92f702100264021064470211322d0211a21c02121f9b02129d0c02131a990213c0b202144c030214e55502158c2802166a4a

private def d_s_4_2096 : List (ℕ × ℕ) := [(4466691686,2097),(4465227757,2098),(4464252337,2099),(4463764787,2100),(4459868217,2101),(4456950251,2102),(4454036100,2103),(4450641071,2104),(4449672013,2105),(4447735162,2106),(4443383407,2107),(4442417507,2108),(4439522324,2109),(4436149376,2110),(4434705395,2111),(4433262354,2112)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2096 := recordedBatch d_s_4_2096 2096 0x204a72d0205214b02059b3c020649af0206ebee02075946020822b40208ab2e0209194b0209c982020a6c43020b0fdc020bcdd9020c2f2a020c9e19020d1a04

private theorem s_5_2080 : rowTree 5 2080 = 1101868676 := by
  exact glueRows (by decide) s_4_2080.property s_4_2096.property (by decide)

private theorem s_6_2048 : rowTree 6 2048 = 2242105045 := by
  exact glueRows (by decide) s_5_2048 s_5_2080 (by decide)

private def d_s_4_2112 : List (ℕ × ℕ) := [(4432300848,2113),(4430379088,2114),(4428938860,2115),(4427979229,2116),(4423187303,2117),(4420317122,2118),(4417928149,2119),(4414587922,2120),(4413634498,2121),(4413157941,2122),(4409349185,2123),(4408873553,2124),(4406021913,2125),(4398908925,2126),(4397962261,2127),(4396543029,2128)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2112 := recordedBatch d_s_4_2112 2112 0x1fba3ca01fc1bde01fc872a01fd97e601fe368e01fe95bd01ff4e4c01ffacfe020018f40200c5a8020158830201f8e30202cce40203396a0203b30002043a05

private def d_s_4_2128 : List (ℕ × ℕ) := [(4390875251,2129),(4386163253,2130),(4380522188,2131),(4378176024,2132),(4376300902,2133),(4373491228,2134),(4371152588,2135),(4368349519,2136),(4366949332,2137),(4364151649,2138),(4361357549,2139),(4359961840,2140),(4358102284,2141),(4354387927,2142),(4351143053,2143),(4349753874,2144)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2128 := recordedBatch d_s_4_2128 2128 0x1f1b22501f2279101f2cdee01f3810501f4035001f478ad01f5141701f5af3301f6255d01f6c1d301f7518601f7edad01f870ef01f9014b01f9ea3001fab9b1

private theorem s_5_2112 : rowTree 5 2112 = 1063218704 := by
  exact glueRows (by decide) s_4_2112.property s_4_2128.property (by decide)

private def d_s_4_2144 : List (ℕ × ℕ) := [(4348828246,2145),(4347440544,2146),(4339132892,2147),(4334531234,2148),(4332234064,2149),(4325357138,2150),(4322612477,2151),(4322155372,2152),(4321241452,2153),(4320784637,2154),(4314399353,2155),(4311668577,2156),(4308487037,2157),(4307124956,2158),(4302138021,2159),(4300327453,2160)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2144 := recordedBatch d_s_4_2144 2144 0x1e79f4601e81da001e8effa01e9627c01ea05c601ea9cb001eb94d901ebf05801ec57ae01ecb32d01ed4ac501ee505c01eedcdc01efa69101f0d42501f14952

private def d_s_4_2160 : List (ℕ × ℕ) := [(4299422739,2161),(4295356237,2162),(4294002445,2163),(4290846913,2164),(4286796609,2165),(4285897580,2166),(4284549743,2167),(4284100652,2168),(4282753945,2169),(4275138567,2170),(4271117851,2171),(4270671571,2172),(4267104690,2173),(4265768645,2174),(4261765526,2175),(4261321198,2176)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2160 := recordedBatch d_s_4_2160 2160 0x1dec17a01df1a6d01dfd09b01e0410201e0eb8b01e144cc01e1fbbf01e310d401e3826001e3dc2c01e44d4101e4b36b01e56c4a01e60d2401e67f6d01e738fb

private theorem s_5_2144 : rowTree 5 2144 = 1022507359 := by
  exact glueRows (by decide) s_4_2144.property s_4_2160.property (by decide)

private theorem s_6_2112 : rowTree 6 2112 = 2085726063 := by
  exact glueRows (by decide) s_5_2112 s_5_2144 (by decide)

private theorem s_7_2048 : rowTree 7 2048 = 4327831108 := by
  exact glueRows (by decide) s_6_2048 s_6_2112 (by decide)

private def d_s_4_2176 : List (ℕ × ℕ) := [(4255996488,2177),(4255110330,2178),(4254667389,2179),(4253339120,2180),(4250685068,2181),(4249359284,2182),(4246710195,2183),(4244505143,2184),(4242742749,2185),(4241421914,2186),(4237903704,2187),(4235268874,2188),(4233514141,2189),(4231322768,2190),(4228258653,2191),(4219528444,2192)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2176 := recordedBatch d_s_4_2176 2176 0x1d5b99b01d6e72b01d781d401d8072301d880e201d911ba01d9b9d901da28f601daa36b01db292f01dbbb2b01dc2a6c01dcbccb01dd2c5a01dd84fa01dde958

private def d_s_4_2192 : List (ℕ × ℕ) := [(4218222021,2193),(4217786726,2194),(4216481382,2195),(4215611601,2196),(4213004409,2197),(4209966758,2198),(4209099662,2199),(4208666249,2200),(4207799688,2201),(4207366542,2202),(4206500517,2203),(4204769536,2204),(4203472235,2205),(4201311844,2206),(4200016675,2207),(4198722304,2208)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2192 := recordedBatch d_s_4_2192 2192 0x1cee9e401cf566b01cfc2d701d0456901d0b1e301d1299601d18b5e01d1e20201d243c701d29a5c01d2fc5e01d3966301d424ef01d4872801d4f4d401d54c0b

private theorem s_5_2176 : rowTree 5 2176 = 986093586 := by
  exact glueRows (by decide) s_4_2176.property s_4_2192.property (by decide)

private def d_s_4_2208 : List (ℕ × ℕ) := [(4198291025,2209),(4196997718,2210),(4195705207,2211),(4194413492,2212),(4191832447,2213),(4190543115,2214),(4185393710,2215),(4183251857,2216),(4182823750,2217),(4180684526,2218),(4179402042,2219),(4176839433,2220),(4175559307,2221),(4174279965,2222),(4171297880,2223),(4170021147,2224)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2208 := recordedBatch d_s_4_2208 2208 0x1c762c801c7cd1001c8639301c8ce7001c939b401c9c53e01ca308501cab18701cb074101cb884701cc567101ccc24101cd4f0a01cdbb4b01ce275701ce93c6

private def d_s_4_2224 : List (ℕ × ℕ) := [(4168745196,2225),(4157719574,2226),(4153494464,2227),(4152228605,2228),(4150120554,2229),(4149699200,2230),(4147593716,2231),(4145910866,2232),(4143809223,2233),(4141290063,2234),(4138773963,2235),(4138354910,2236),(4137098261,2237),(4136260919,2238),(4133332889,2239),(4129991641,2240)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2224 := recordedBatch d_s_4_2224 2224 0x1bed64401bf730401c005c501c0641701c0cd0801c120e701c1aa1601c2335101c2b19e01c325fb01c3a47101c3f8cc01c4778901c4e1b401c596f401c6f7e6

private theorem s_5_2208 : rowTree 5 2208 = 953650156 := by
  exact glueRows (by decide) s_4_2208.property s_4_2224.property (by decide)

private theorem s_6_2176 : rowTree 6 2176 = 1939743742 := by
  exact glueRows (by decide) s_5_2176 s_5_2208 (by decide)

private def d_s_4_2240 : List (ℕ × ℕ) := [(4128323042,2241),(4125822669,2242),(4124573619,2243),(4120000229,2244),(4119584969,2245),(4117509925,2246),(4115851394,2247),(4114608373,2248),(4110057044,2249),(4109643786,2250),(4105103427,2251),(4103866888,2252),(4102219328,2253),(4100161737,2254),(4097695350,2255),(4095231930,2256)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2240 := recordedBatch d_s_4_2240 2240 0x1b6ec3f01b7711501b7f6c401b8723101b8e38f01b94a9c01ba039201ba561001bb104901bb77be01bbe96801bc65f701bcb8f101bd73a701bddbf601be6347

private def d_s_4_2256 : List (ℕ × ℕ) := [(4094821647,2257),(4092771469,2258),(4091542347,2259),(4089086316,2260),(4088677264,2261),(4087859406,2262),(4084999478,2263),(4082959120,2264),(4082551293,2265),(4081328301,2266),(4077663718,2267),(4076850259,2268),(4074411830,2269),(4072787830,2270),(4069138561,2271),(4066709345,2272)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2256 := recordedBatch d_s_4_2256 2256 0x1afb34301b0368901b0d78001b146f201b1ca8b01b225bf01b2c78601b32d6701b37edb01b3f89601b486d901b4e30401b5350b01b5b94401b61f8501b69a09

private theorem s_5_2240 : rowTree 5 2240 = 920586225 := by
  exact glueRows (by decide) s_4_2240.property s_4_2256.property (by decide)

private def d_s_4_2272 : List (ℕ × ℕ) := [(4065495825,2273),(4064283028,2274),(4063474899,2275),(4062263308,2276),(4061052439,2277),(4058229884,2278),(4057424160,2279),(4057021418,2280),(4054606644,2281),(4052194743,2282),(4051391413,2283),(4050187016,2284),(4046578117,2285),(4042975644,2286),(4040577556,2287),(4040178152,2288)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2272 := recordedBatch d_s_4_2272 2272 0x1a8bf6501a90f4301a9900b01aa2e6401aacd0501ab312801ab8b6301ac0cd401ac8e6e01acdf5601ad39a701adc5a101ae2a1001ae8eb801aee92a01af4e56

private def d_s_4_2288 : List (ℕ × ℕ) := [(4036985755,2289),(4034594766,2290),(4033002346,2291),(4029423993,2292),(4027438762,2293),(4022286303,2294),(4021494787,2295),(4020308097,2296),(4018726933,2297),(4017541876,2298),(4016357517,2299),(4015568333,2300),(4015173857,2301),(4013202639,2302),(4009266003,2303),(4008479603,2304)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2288 := recordedBatch d_s_4_2288 2288 0x1a1646701a1bc7601a260af01a2d63501a324e701a37d8001a3df6501a441ec01a4adc101a50fea01a568c701a62c0401a6a1e801a73ecf01a7ab9601a82b5d

private theorem s_5_2272 : rowTree 5 2272 = 890021480 := by
  exact glueRows (by decide) s_4_2272.property s_4_2288.property (by decide)

private theorem s_6_2240 : rowTree 6 2240 = 1810607705 := by
  exact glueRows (by decide) s_5_2240 s_5_2272 (by decide)

private theorem s_7_2176 : rowTree 7 2176 = 3750351447 := by
  exact glueRows (by decide) s_6_2176 s_6_2240 (by decide)

private theorem s_8_2048 : rowTree 8 2048 = 8078182555 := by
  exact glueRows (by decide) s_7_2048 s_7_2176 (by decide)

private def d_s_4_2304 : List (ℕ × ℕ) := [(4007300581,2305),(4005729629,2306),(4004944615,2307),(4001024157,2308),(3999066804,2309),(3998675564,2310),(3992036165,2311),(3991646298,2312),(3990866794,2313),(3986196155,2314),(3985807428,2315),(3983476660,2316),(3981148617,2317),(3979210658,2318),(3978048788,2319),(3977661649,2320)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2304 := recordedBatch d_s_4_2304 2304 0x19a3374019a80f0019ae0f3019b53e9019bd056019c4c89019c9a61019d4fb7019da6d7019df4f0019ed949019f27b4019f9bbd01a03ee301a0972e01a10256

private def d_s_4_2320 : List (ℕ × ℕ) := [(3975340395,2321),(3969549097,2322),(3968392861,2323),(3966082410,2324),(3963005989,2325),(3960701805,2326),(3960318034,2327),(3956101464,2328),(3952658215,2329),(3950366044,2330),(3947695202,2331),(3945789668,2332),(3945408782,2333),(3943125008,2334),(3940843877,2335),(3940084087,2336)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2320 := recordedBatch d_s_4_2320 2320 0x1927b730192d09101934a2d0193c3a301940fef01947ff80195028601957c12019611980196ba40019706f20197815001980ecc0198898c0198e9150199b800

private theorem s_5_2304 : rowTree 5 2304 = 859174649 := by
  exact glueRows (by decide) s_4_2304.property s_4_2320.property (by decide)

private def d_s_4_2336 : List (ℕ × ℕ) := [(3939704301,2337),(3938944950,2338),(3937806472,2339),(3935531488,2340),(3935152580,2341),(3932123938,2342),(3928722283,2343),(3928344685,2344),(3920807931,2345),(3919304049,2346),(3916299743,2347),(3915174316,2348),(3913674752,2349),(3911801912,2350),(3911427558,2351),(3910679067,2352)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2336 := recordedBatch d_s_4_2336 2336 0x18b9b15018beeb5018c39b5018ca852018d0e09018d6ac5018df416018e59bc018f4e8e018f9a0c01902d300190b77c0191036201917c940191dac201922f68

private def d_s_4_2352 : List (ℕ × ℕ) := [(3907314399,2353),(3905820849,2354),(3903955516,2355),(3902464532,2356),(3900230190,2357),(3899485977,2358),(3896140534,2359),(3895769172,2360),(3892430101,2361),(3890577533,2362),(3890207231,2363),(3889466838,2364),(3889096748,2365),(3888356778,2366),(3886877683,2367),(3881709699,2368)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2352 := recordedBatch d_s_4_2352 2352 0x184db57018594e60185f8a801864b7a018695920186e8440187327f01879f8d01882ee9018879480189094401895c640189d2aa018a378f018aa54d018b0a34

private theorem s_5_2336 : rowTree 5 2336 = 829248939 := by
  exact glueRows (by decide) s_4_2336.property s_4_2352.property (by decide)

private theorem s_6_2304 : rowTree 6 2304 = 1688423588 := by
  exact glueRows (by decide) s_5_2304 s_5_2336 (by decide)

private def d_s_4_2368 : List (ℕ × ℕ) := [(3881341083,2369),(3880235655,2370),(3876187801,2371),(3873983439,2372),(3872882198,2373),(3870315068,2374),(3867019468,2375),(3866287875,2376),(3865191004,2377),(3863729477,2378),(3862634057,2379),(3861539258,2380),(3859715971,2381),(3858258580,2382),(3857530298,2383),(3857166260,2384)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2368 := recordedBatch d_s_4_2368 2368 0x17e975e017ee03a017f315e017f9334017ffe1d0180577e0180b167018113c301816dc30181bf7f01824c8f0182c90401832367018397e6018436fc018491dd

private def d_s_4_2384 : List (ℕ × ℕ) := [(3853893006,2385),(3852076931,2386),(3850988107,2387),(3847363136,2388),(3843383542,2389),(3841938457,2390),(3840855356,2391),(3835449000,2392),(3834729303,2393),(3834369555,2394),(3833650262,2395),(3830416782,2396),(3829340167,2397),(3823966157,2398),(3823608426,2399),(3822893165,2400)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2384 := recordedBatch d_s_4_2384 2384 0x177871b0177d6ce01781e4d0178d89d017930db0179ba2f017a0aa3017a5280017aa2d2017b5f1b017bb80c017c1984017cb4cb017d483e017da14e017e0b78

private theorem s_5_2368 : rowTree 5 2368 = 801191990 := by
  exact glueRows (by decide) s_4_2368.property s_4_2384.property (by decide)

private def d_s_4_2400 : List (ℕ × ℕ) := [(3821463445,2401),(3820391856,2402),(3819677798,2403),(3818607210,2404),(3816467834,2405),(3813974924,2406),(3807934250,2407),(3805452472,2408),(3804389842,2409),(3803681753,2410),(3803327806,2411),(3802266363,2412),(3801559064,2413),(3799085586,2414),(3798379469,2415),(3798026509,2416)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2400 := recordedBatch d_s_4_2400 2400 0x171645a0171ab210171f9980172707e0172bf67017315f901735c9f0173ab8d017402cd017479fb017541a40175b940017628f4017680680176cfe601772757

private def d_s_4_2416 : List (ℕ × ℕ) := [(3796968022,2417),(3792036208,2418),(3791684426,2419),(3790981058,2420),(3789926494,2421),(3788521321,2422),(3786766320,2423),(3786415515,2424),(3784662463,2425),(3784312048,2426),(3782560943,2427),(3782210917,2428),(3781511058,2429),(3776270363,2430),(3775921500,2431),(3773829673,2432)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2416 := recordedBatch d_s_4_2416 2416 0x16b60f5016bcdc0016c13b1016cc700016d1487016d5a93016dbff7016e05f0016e6ba5016eb1c0016f178a016f7572016fcb7e017019aa0170603301710dcd

private theorem s_5_2400 : rowTree 5 2400 = 774220626 := by
  exact glueRows (by decide) s_4_2400.property s_4_2416.property (by decide)

private theorem s_6_2368 : rowTree 6 2368 = 1575412616 := by
  exact glueRows (by decide) s_5_2368 s_5_2400 (by decide)

private theorem s_7_2304 : rowTree 7 2304 = 3263836204 := by
  exact glueRows (by decide) s_6_2304 s_6_2368 (by decide)

private def d_s_4_2432 : List (ℕ × ℕ) := [(3771740163,2433),(3770000671,2434),(3766873625,2435),(3764791809,2436),(3762365929,2437),(3760635071,2438),(3760289091,2439),(3758214544,2440),(3757178129,2441),(3755452040,2442),(3754417147,2443),(3752004615,2444),(3749939196,2445),(3749251229,2446),(3746845329,2447),(3746158496,2448)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2432 := recordedBatch d_s_4_2432 2432 0x165229b01656edb0165e18801662db80166992d01670c0e016760390167c3db016818810168839c0168c8cc01692ca30169a052016a0c1e016a8f2b016af434

private def d_s_4_2448 : List (ℕ × ℕ) := [(3743070861,2449),(3742728105,2450),(3741015264,2451),(3739646120,2452),(3738961924,2453),(3737594282,2454),(3735886136,2455),(3733838421,2456),(3730771053,2457),(3727708721,2458),(3726349298,2459),(3725330381,2460),(3722276970,2461),(3719567027,2462),(3717199061,2463),(3716185141,2464)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2448 := recordedBatch d_s_4_2448 2448 0x15ec5f9015f1857015f88750160004301607f900160d1e301612cbd0161acae01622c4e016295ce0162f813016352df01639ea50163f9f201645cb50164a13a

private theorem s_5_2432 : rowTree 5 2432 = 748445914 := by
  exact glueRows (by decide) s_4_2432.property s_4_2448.property (by decide)

private def d_s_4_2464 : List (ℕ × ℕ) := [(3715171774,2465),(3713484057,2466),(3711123827,2467),(3710450027,2468),(3709439785,2469),(3709103160,2470),(3707084692,2471),(3705068420,2472),(3704396816,2473),(3703389867,2474),(3702383466,2475),(3700372303,2476),(3700037322,2477),(3697359652,2478),(3697025216,2479),(3695019868,2480)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2464 := recordedBatch d_s_4_2464 2464 0x1593b700159a2bd0159e5b4015a5b80015a9ea3015b05f9015b57e9015ba977015bf414015c5ba8015cc3c3015d0730015d5938015da3d2015e1343015e73b8

private def d_s_4_2480 : List (ℕ × ℕ) := [(3694018010,2481),(3693350406,2482),(3691015693,2483),(3690016004,2484),(3689349846,2485),(3689016857,2486),(3687020186,2487),(3684029228,2488),(3683365230,2489),(3677399997,2490),(3674424621,2491),(3672443710,2492),(3670464934,2493),(3670135345,2494),(3669476345,2495),(3669146934,2496)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2480 := recordedBatch d_s_4_2480 2480 0x1535af501539ccd0153e5c1015427ad01548d810154f2ed01556dc10156294d015673270156ee7d015755260157979a0157e1530158322601589fd80158ea1f

private theorem s_5_2464 : rowTree 5 2464 = 723479697 := by
  exact glueRows (by decide) s_4_2464.property s_4_2480.property (by decide)

private theorem s_6_2432 : rowTree 6 2432 = 1471925611 := by
  exact glueRows (by decide) s_5_2432 s_5_2464 (by decide)

private def d_s_4_2496 : List (ℕ × ℕ) := [(3668488289,2497),(3667171708,2498),(3665198608,2499),(3664541379,2500),(3658636913,2501),(3657654685,2502),(3654711161,2503),(3654384396,2504),(3652425028,2505),(3650793825,2506),(3649815803,2507),(3647861330,2508),(3643958657,2509),(3642659621,2510),(3641685951,2511),(3640712802,2512)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2496 := recordedBatch d_s_4_2496 2496 0x14d548c014da327014df20a014e4772014ed4cb014f38b3014f87cf014fe4e20150492501508ab401510461015153f501520d5d015256310152baf701531219

private def d_s_4_2512 : List (ℕ × ℕ) := [(3638120279,2513),(3636178308,2514),(3635854848,2515),(3632946293,2516),(3631332439,2517),(3628109030,2518),(3626499470,2519),(3626177729,2520),(3625212850,2521),(3622321290,2522),(3621679347,2523),(3621358461,2524),(3614952662,2525),(3613993746,2526),(3613674221,2527),(3611120049,2528)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2512 := recordedBatch d_s_4_2512 2512 0x1474a4f0147b95a0147f97c01484731014907540149477801498e8a014a04db014a52d7014a9330014aeee2014b6cbf014bc8a6014c4010014c80c9014ce416

private theorem s_5_2496 : rowTree 5 2496 = 698605039 := by
  exact glueRows (by decide) s_4_2496.property s_4_2512.property (by decide)

private def d_s_4_2528 : List (ℕ × ℕ) := [(3610801031,2529),(3610163165,2530),(3608888108,2531),(3606022522,2532),(3604432495,2533),(3602526312,2534),(3601573976,2535),(3601256643,2536),(3599670815,2537),(3598403158,2538),(3597769664,2539),(3596819842,2540),(3594921700,2541),(3594605538,2542),(3593025561,2543),(3590185100,2544)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2528 := recordedBatch d_s_4_2528 2528 0x142070601427aea0142d44d014313cf014374160143c099014406a7014459e10144b41f0144f3760145402b0145a11c0145fb0d014670260146c40f01470a7a

private def d_s_4_2544 : List (ℕ × ℕ) := [(3588924114,2545),(3587978956,2546),(3587349126,2547),(3584203295,2548),(3583574790,2549),(3582632447,2550),(3576988778,2551),(3576049895,2552),(3575737043,2553),(3574173606,2554),(3573236200,2555),(3569491487,2556),(3568556535,2557),(3566376883,2558),(3563889111,2559),(3562957091,2560)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2544 := recordedBatch d_s_4_2544 2544 0x13c4f94013c9ab5013d05c8013d6a66013db5d5013e3b6b013e8704013edffd013f1eba013f6a6a0140168c014062a30140a82401412254014167cf0141b412

private theorem s_5_2528 : rowTree 5 2528 = 674848063 := by
  exact glueRows (by decide) s_4_2528.property s_4_2544.property (by decide)

private theorem s_6_2496 : rowTree 6 2496 = 1373453102 := by
  exact glueRows (by decide) s_5_2496 s_5_2528 (by decide)

private theorem s_7_2432 : rowTree 7 2432 = 2845378713 := by
  exact glueRows (by decide) s_6_2432 s_6_2496 (by decide)

private theorem s_8_2304 : rowTree 8 2304 = 6109214917 := by
  exact glueRows (by decide) s_7_2304 s_7_2432 (by decide)

private theorem s_9_2048 : rowTree 9 2048 = 14187397472 := by
  exact glueRows (by decide) s_8_2048 s_8_2304 (by decide)

private def d_s_4_2560 : List (ℕ × ℕ) := [(3560163954,2561),(3559853876,2562),(3558304294,2563),(3555209174,2564),(3553663633,2565),(3552428167,2566),(3551502131,2567),(3550885042,2568),(3549959810,2569),(3549651507,2570),(3548110792,2571),(3547802810,2572),(3545956038,2573),(3545340875,2574),(3545033373,2575),(3544418529,2576)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2560 := recordedBatch d_s_4_2560 2560 0x1375bb401379fb10137dd35013820f701387e2b0138bbc5013912830139502e01399acc0139dee7013a2984013a7ad0013ad1af013b48f9013ba033013bde2a

private def d_s_4_2576 : List (ℕ × ℕ) := [(3543189482,2577),(3541654371,2578),(3540733943,2579),(3538894521,2580),(3536138969,2581),(3533998727,2582),(3532166294,2583),(3529726005,2584),(3528507124,2585),(3527593516,2586),(3525159539,2587),(3523943809,2588),(3523336259,2589),(3523032562,2590),(3522121787,2591),(3519392282,2592)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2576 := recordedBatch d_s_4_2576 2576 0x131f0f201325f0e0132a8060132e4fd013327f0013377500133dee90134288d013478670134e06001353c2801359ec301360dd201366aa70136b48501370b6f

private theorem s_5_2560 : rowTree 5 2560 = 652164374 := by
  exact glueRows (by decide) s_4_2560.property s_4_2576.property (by decide)

private def d_s_4_2592 : List (ℕ × ℕ) := [(3515759518,2593),(3513039862,2594),(3511530759,2595),(3509721547,2596),(3509420192,2597),(3508817639,2598),(3506710332,2599),(3505206661,2600),(3504305078,2601),(3503403958,2602),(3502503301,2603),(3499804108,2604),(3498006956,2605),(3497707610,2606),(3493522140,2607),(3490836766,2608)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2592 := recordedBatch d_s_4_2592 2592 0x12c5130012cbcec012d4639012d8234012ddc81012e488d012e908d012ed8ee012f20f5012f7599012fd63f013018bd0130550b0130afc30131043a01317153

private def d_s_4_2608 : List (ℕ × ℕ) := [(3488750994,2609),(3486370305,2610),(3484586919,2611),(3482508607,2612),(3478951549,2613),(3477175743,2614),(3473924803,2615),(3473039238,2616),(3472744150,2617),(3471269461,2618),(3470090612,2619),(3469501487,2620),(3469207000,2621),(3468618176,2622),(3466558863,2623),(3464795683,2624)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2608 := recordedBatch d_s_4_2608 2608 0x126f6eb01274f140127acd70127ed9e012828a3012869410128b5ee012908700129437901298a21012a002a012a58e9012ad522012b3401012b8cfc012bf1c9

private theorem s_5_2592 : rowTree 5 2592 = 629425218 := by
  exact glueRows (by decide) s_4_2592.property s_4_2608.property (by decide)

private theorem s_6_2560 : rowTree 6 2560 = 1281589592 := by
  exact glueRows (by decide) s_5_2560 s_5_2592 (by decide)

private def d_s_4_2624 : List (ℕ × ℕ) := [(3463914765,2625),(3463327736,2626),(3462447564,2627),(3460395570,2628),(3459809732,2629),(3459516888,2630),(3458931348,2631),(3454546108,2632),(3453670393,2633),(3453378587,2634),(3452503465,2635),(3451045913,2636),(3450754550,2637),(3446390006,2638),(3443196350,2639),(3442906311,2640)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2624 := recordedBatch d_s_4_2624 2624 0x121fdae0122379b0122aa8c0123344801236e980123bfa20124057001243ffe0124860d012510f50125515701258c1f0125cc5d0126299e012670100126b089

private def d_s_4_2640 : List (ℕ × ℕ) := [(3442326380,2641),(3441456849,2642),(3440298158,2643),(3439429652,2644),(3438561584,2645),(3436248877,2646),(3434516388,2647),(3432785644,2648),(3431920926,2649),(3430768647,2650),(3430192797,2651),(3429904945,2652),(3426454481,2653),(3424731851,2654),(3424158026,2655),(3423297648,2656)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2640 := recordedBatch d_s_4_2640 2640 0x11d3d5c011d8240011dc12e011e16a3011e8d2b011ec6ec011f0677011f5123011f963e011fec1c0120423d0120a3840120e89a01212dd3012178e20121be23

private theorem s_5_2624 : rowTree 5 2624 = 608111484 := by
  exact glueRows (by decide) s_4_2624.property s_4_2640.property (by decide)

private def d_s_4_2656 : List (ℕ × ℕ) := [(3422151151,2657),(3421291782,2658),(3420432844,2659),(3419002239,2660),(3418716262,2661),(3417858617,2662),(3416144617,2663),(3412151962,2664),(3410159132,2665),(3409305774,2666),(3408737106,2667),(3407032240,2668),(3405896610,2669),(3405045384,2670),(3403344208,2671),(3402777527,2672)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2656 := recordedBatch d_s_4_2656 2656 0x11878b00118b6c901190b0b01194e92011998020119ec3f011a2aa2011a6ea1011ac8d6011b4955011b9df0011be231011c1b83011c6add011caf0d011cf394

private def d_s_4_2672 : List (ℕ × ℕ) := [(3401927860,2673),(3399946951,2674),(3399098696,2675),(3397403456,2676),(3395992046,2677),(3395145763,2678),(3394299902,2679),(3393172743,2680),(3392327864,2681),(3391483406,2682),(3390920668,2683),(3390639369,2684),(3390076911,2685),(3388952554,2686),(3387267416,2687),(3386706075,2688)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2672 := recordedBatch d_s_4_2672 2672 0x1141563011452b50114a5560114edca01152b8d011563ef0115a1bd0115e4d701162857011670890116b39f0116f6be0117448c011798520117dbe201183536

private theorem s_5_2656 : rowTree 5 2656 = 588031074 := by
  exact glueRows (by decide) s_4_2656.property s_4_2672.property (by decide)

private theorem s_6_2624 : rowTree 6 2624 = 1196142558 := by
  exact glueRows (by decide) s_5_2624 s_5_2656 (by decide)

private theorem s_7_2560 : rowTree 7 2560 = 2477732150 := by
  exact glueRows (by decide) s_6_2560 s_6_2624 (by decide)

private def d_s_4_2688 : List (ℕ × ℕ) := [(3384742849,2689),(3382222042,2690),(3380823216,2691),(3380543590,2692),(3378308242,2693),(3377470749,2694),(3374682101,2695),(3373846405,2696),(3372454497,2697),(3371341797,2698),(3370785722,2699),(3366621002,2700),(3361636902,2701),(3359978813,2702),(3358874329,2703),(3355840738,2704)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2688 := recordedBatch d_s_4_2688 2688 0x10ea8be010f13ba010f5a6f010fabdc01103b810110bb8d0110f8930111402101118cc30111cf5201123682011279070112d5fb01130df101135b190113bd4d

private def d_s_4_2704 : List (ℕ × ℕ) := [(3354188361,2705),(3353913123,2706),(3353087680,2707),(3351438012,2708),(3349240978,2709),(3348417832,2710),(3347595092,2711),(3347320935,2712),(3344855540,2713),(3344308168,2714),(3340754610,2715),(3340208579,2716),(3339117052,2717),(3336663723,2718),(3335302319,2719),(3334213996,2720)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2704 := recordedBatch d_s_4_2704 2704 0x109fa18010a3f9e010a8a43010ae909010b2f39010b6b02010bdebb010c1ad5010c7a84010cb176010cf30e010d340d010d8eb4010ddf83010e20e0010e5813

private theorem s_5_2688 : rowTree 5 2688 = 567833985 := by
  exact glueRows (by decide) s_4_2688.property s_4_2704.property (by decide)

private def d_s_4_2720 : List (ℕ × ℕ) := [(3332854591,2721),(3332039479,2722),(3330139102,2723),(3329596535,2724),(3326886352,2725),(3323910240,2726),(3321479198,2727),(3319860478,2728),(3318782207,2729),(3315013770,2730),(3313401343,2731),(3312595718,2732),(3311790485,2733),(3310717449,2734),(3309913129,2735),(3308305660,2736)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2720 := recordedBatch d_s_4_2720 2720 0x1050d0d01055af201059a8f0105df4101061e8f01065e120106ac8e010722d00107677a0107b63f0108145801087c070108df9201091adf01096f4e0109af80

private def d_s_4_2736 : List (ℕ × ℕ) := [(3305095401,2737),(3302958687,2738),(3301091327,2739),(3300558184,2740),(3298693537,2741),(3297096944,2742),(3296299227,2743),(3294970557,2744),(3293377565,2745),(3290725999,2746),(3289931362,2747),(3289401817,2748),(3288343238,2749),(3285963924,2750),(3284379627,2751),(3282006044,2752)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2736 := recordedBatch d_s_4_2736 2736 0x1002891010083540100d00801012b1201016e870101a87f0101e759010247ab0102950b0102dd9801031c9101036a340103bcae0103f6e501044a010104a1b7

private theorem s_5_2720 : rowTree 5 2720 = 547060449 := by
  exact glueRows (by decide) s_4_2720.property s_4_2736.property (by decide)

private theorem s_6_2688 : rowTree 6 2688 = 1114894434 := by
  exact glueRows (by decide) s_5_2688 s_5_2720 (by decide)

private def d_s_4_2752 : List (ℕ × ℕ) := [(3280688869,2753),(3280425561,2754),(3279899071,2755),(3277269155,2756),(3275955779,2757),(3274118819,2758),(3273594351,2759),(3272807965,2760),(3272545920,2761),(3271236326,2762),(3268097571,2763),(3265747455,2764),(3265486539,2765),(3264964834,2766),(3262358804,2767),(3260276973,2768)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2752 := recordedBatch d_s_4_2752 2752 0xfba46400fbf8f100fc56fb00fc8fdc00fcc43f00fd1e6a00fd86bf00fdce3600fe027f00fe409400fe7a1100fecadc00ff127100ff71e300ffab7f00ffe046

private def d_s_4_2768 : List (ℕ × ℕ) := [(3258457549,2769),(3257159204,2770),(3255343258,2771),(3254565615,2772),(3254047392,2773),(3253270368,2774),(3250682966,2775),(3249907548,2776),(3248616005,2777),(3247841573,2778),(3247583510,2779),(3246035998,2780),(3245262795,2781),(3241402298,2782),(3240117505,2783),(3239090405,2784)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2768 := recordedBatch d_s_4_2768 2768 0xf7391f00f77a1600f7bfbb00f832c300f86f9300f8ba3400f8ee0c00f92af400f9714200f9ae8c00fa0b2600fa482500fa80c700fabe1a00fb0dd800fb543b

private theorem s_5_2752 : rowTree 5 2752 = 527585386 := by
  exact glueRows (by decide) s_4_2752.property s_4_2768.property (by decide)

private def d_s_4_2784 : List (ℕ × ℕ) := [(3238320506,2785),(3237807444,2786),(3237038156,2787),(3236013006,2788),(3230896982,2789),(3230641605,2790),(3230130973,2791),(3229875718,2792),(3228345031,2793),(3226051720,2794),(3225542538,2795),(3224779066,2796),(3223761665,2797),(3222490817,2798),(3221728788,2799),(3219444864,2800)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2784 := recordedBatch d_s_4_2784 2784 0xf2f4ef00f34b8900f3874f00f3cc3b00f40c9600f4485a00f47fe300f4d6eb00f5205800f5539900f58b2a00f5be5600f6472d00f6884800f6c46c00f6fc84

private def d_s_4_2800 : List (ℕ × ℕ) := [(3217164176,2801),(3216910965,2802),(3215392540,2803),(3213370201,2804),(3212359985,2805),(3211602740,2806),(3211098108,2807),(3210341458,2808),(3209585164,2809),(3209333145,2810),(3202794520,2811),(3201038671,2812),(3200537353,2813),(3198033119,2814),(3196032550,2815),(3195782655,2816)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2800 := recordedBatch d_s_4_2800 2800 0xee77c100eea9db00eefa5f00ef53d100ef8aa400efd6e700f0763000f0a8b100f0e42d00f11f7e00f1566700f191b100f1d16b00f2234100f26c1600f29ed6

private theorem s_5_2784 : rowTree 5 2784 = 509176105 := by
  exact glueRows (by decide) s_4_2784.property s_4_2800.property (by decide)

private theorem s_6_2752 : rowTree 6 2752 = 1036761491 := by
  exact glueRows (by decide) s_5_2752 s_5_2784 (by decide)

private theorem s_7_2688 : rowTree 7 2688 = 2151655925 := by
  exact glueRows (by decide) s_6_2688 s_6_2752 (by decide)

private theorem s_8_2560 : rowTree 8 2560 = 4629388075 := by
  exact glueRows (by decide) s_7_2560 s_7_2688 (by decide)

private def d_s_4_2816 : List (ℕ × ℕ) := [(3195282983,2817),(3194533766,2818),(3193036387,2819),(3192786960,2820),(3192038914,2821),(3190543872,2822),(3189050230,2823),(3188303933,2824),(3187806596,2825),(3186067137,2826),(3184825829,2827),(3184081508,2828),(3183337534,2829),(3181602948,2830),(3180365115,2831),(3178633765,2832)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2816 := recordedBatch d_s_4_2816 2816 0xea777800eac24700eb04ef00eb4fcc00eb8a1a00ebc45d00ec071d00ec528500ec88bc00ecc32600ed0a9100ed51e800ed8ca000edbea600ee068400ee415d

private def d_s_4_2832 : List (ℕ × ℕ) := [(3176657387,2833),(3175670119,2834),(3174930071,2835),(3173451009,2836),(3172958295,2837),(3171973324,2838),(3169267807,2839),(3168530739,2840),(3168285126,2841),(3166076321,2842),(3163380850,2843),(3162646518,2844),(3162401816,2845),(3160201204,2846),(3159468347,2847),(3157515723,2848)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2832 := recordedBatch d_s_4_2832 2832 0xe63f6500e68d0600e6c65200e7187700e749a700e7831d00e7ddad00e8303300e8618600e89b0900e8f61400e933e800e969b800e9b04d00e9ea4f00ea28aa

private theorem s_5_2816 : rowTree 5 2816 = 491408246 := by
  exact glueRows (by decide) s_4_2816.property s_4_2832.property (by decide)

private def d_s_4_2848 : List (ℕ × ℕ) := [(3155809155,2849),(3154591307,2850),(3153861050,2851),(3152401548,2852),(3152158429,2853),(3151429297,2854),(3150943397,2855),(3149972045,2856),(3147788692,2857),(3146334804,2858),(3144398375,2859),(3144156488,2860),(3143672828,2861),(3141981187,2862),(3141498195,2863),(3140532657,2864)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2848 := recordedBatch d_s_4_2848 2848 0xe259b000e2962e00e2ca8100e3134800e347e100e3785600e3c56b00e409ff00e45b4300e497d400e4cc6500e5054200e5360900e57b8200e5b46800e5f5df

private def d_s_4_2864 : List (ℕ × ℕ) := [(3139085463,2865),(3137639602,2866),(3134030769,2867),(3132109450,2868),(3131149674,2869),(3130670007,2870),(3130430228,2871),(3129711112,2872),(3127077179,2873),(3125642356,2874),(3124686539,2875),(3123492589,2876),(3122776657,2877),(3122061053,2878),(3121345777,2879),(3119678073,2880)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2864 := recordedBatch d_s_4_2864 2864 0xde3f9200de871100debeaa00def66f00df2e6900df6da100dfa91500dfecc600e0444600e07c4f00e0aca500e0e0a100e11c9800e168aa00e1d0b100e2153d

private theorem s_5_2848 : rowTree 5 2848 = 474211460 := by
  exact glueRows (by decide) s_4_2848.property s_4_2864.property (by decide)

private theorem s_6_2816 : rowTree 6 2816 = 965619706 := by
  exact glueRows (by decide) s_5_2816 s_5_2848 (by decide)

private def d_s_4_2880 : List (ℕ × ℕ) := [(3118963888,2881),(3116823294,2882),(3115635345,2883),(3114211000,2884),(3113973736,2885),(3112787957,2886),(3112550910,2887),(3112076923,2888),(3108999526,2889),(3108526621,2890),(3107108767,2891),(3106164249,2892),(3105692206,2893),(3103569784,2894),(3102627416,2895),(3101450261,2896)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2880 := recordedBatch d_s_4_2880 2880 0xda5b4c00da9a0d00dad4d600db22f900db565a00db914900dbd3d100dc073200dc64cf00dc985200dcc7d700dd06d800dd366400dd79af00ddb91a00de0828

private def d_s_4_2896 : List (ℕ × ℕ) := [(3099803744,2897),(3097924150,2898),(3097219889,2899),(3096515949,2900),(3095577860,2901),(3094406047,2902),(3093703385,2903),(3092766999,2904),(3092065081,2905),(3090662201,2906),(3089494106,2907),(3087160563,2908),(3085995113,2909),(3085063386,2910),(3084597734,2911),(3083201620,2912)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2896 := recordedBatch d_s_4_2896 2896 0xd6817600d6c2d300d6f55900d72f7200d76d6a00d7be9500d7fc3b00d83dcd00d8748100d8aec400d8e58100d923a500d95e2300d9949200d9cb5f00da1515

private theorem s_5_2880 : rowTree 5 2880 = 457685922 := by
  exact glueRows (by decide) s_4_2880.property s_4_2896.property (by decide)

private def d_s_4_2912 : List (ℕ × ℕ) := [(3080181037,2913),(3078093329,2914),(3077629778,2915),(3076239963,2916),(3074157592,2917),(3073464095,2918),(3070001297,2919),(3069309674,2920),(3068387994,2921),(3067697097,2922),(3065166468,2923),(3063787884,2924),(3063558241,2925),(3063099057,2926),(3062410540,2927),(3061722332,2928)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2912 := recordedBatch d_s_4_2912 2912 0xd2805c00d2b5b400d2eb4c00d31cdd00d34adc00d38b4600d3de1700d413c900d44d0b00d4827e00d4e47100d51a1b00d565f200d5a71400d5d96600d62609

private def d_s_4_2928 : List (ℕ × ℕ) := [(3061492998,2929),(3060346844,2930),(3060117716,2931),(3059659563,2932),(3058972591,2933),(3058285927,2934),(3058057108,2935),(3057370855,2936),(3054857227,2937),(3052803695,2938),(3052119798,2939),(3050069943,2940),(3048704902,2941),(3047795554,2942),(3046432547,2943),(3045751501,2944)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2928 := recordedBatch d_s_4_2928 2928 0xcee09500cf159a00cf54e900cf8d3d00cfccbb00d0176300d04c5100d096c900d0e8b100d11de400d14ba500d180e900d1b63600d1e7d900d215d500d2523b

private theorem s_5_2912 : rowTree 5 2912 = 441342356 := by
  exact glueRows (by decide) s_4_2912.property s_4_2928.property (by decide)

private theorem s_6_2880 : rowTree 6 2880 = 899028278 := by
  exact glueRows (by decide) s_5_2880 s_5_2912 (by decide)

private theorem s_7_2816 : rowTree 7 2816 = 1864647984 := by
  exact glueRows (by decide) s_6_2816 s_6_2880 (by decide)

private def d_s_4_2944 : List (ℕ × ℕ) := [(3044617101,2945),(3043256935,2946),(3043030359,2947),(3041218964,2948),(3040992692,2949),(3039861833,2950),(3039635762,2951),(3038505912,2952),(3036474297,2953),(3035797695,2954),(3033544533,2955),(3033094302,2956),(3032869237,2957),(3032194241,2958),(3029721824,2959),(3029048228,2960)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2944 := recordedBatch d_s_4_2944 2944 0xcb3ecb00cb731800cbc2ec00cbf72300cc245e00cc554300cca20d00ccd65f00cd1fc900cd5b4500cd888e00cdc43f00cdf1bb00ce381400ce65ae00cea4d6

private def d_s_4_2960 : List (ℕ × ℕ) := [(3028374932,2961),(3026356838,2962),(3025684737,2963),(3024117663,2964),(3022775748,2965),(3020988379,2966),(3020765106,2967),(3020095487,2968),(3019426164,2969),(3018980114,2970),(3017419975,2971),(3016083996,2972),(3015638932,2973),(3015416450,2974),(3013415584,2975),(3011639264,2976)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2960 := recordedBatch d_s_4_2960 2960 0xc79c9c00c7e0de00c828a600c8555500c8855d00c8c35400c9045900c934a500c9681d00c99bcd00c9c88800ca0dda00ca4c3c00ca8e1400cac1fb00cb0ad5

private theorem s_5_2944 : rowTree 5 2944 = 426006717 := by
  exact glueRows (by decide) s_4_2944.property s_4_2960.property (by decide)

private def d_s_4_2976 : List (ℕ × ℕ) := [(3007650191,2977),(3006322847,2978),(3005659615,2979),(3004113209,2980),(3001025168,2981),(3000804836,2982),(2999483526,2983),(2998823308,2984),(2997503742,2985),(2996844394,2986),(2996404990,2987),(2996185337,2988),(2994429266,2989),(2991142176,2990),(2990266838,2991),(2987643892,2992)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2976 := recordedBatch d_s_4_2976 2976 0xc3a01f00c3f08600c426a600c4815900c4c4c000c4f0d300c5204e00c5534500c5906a00c5c37d00c600a200c62cc200c684f200c6c57e00c6f8ae00c7360b

private def d_s_4_2992 : List (ℕ × ℕ) := [(2986988875,2993),(2983718091,2994),(2982629421,2995),(2982411782,2996),(2980454462,2997),(2980019851,2998),(2979368172,2999),(2978065669,3000),(2977197966,3001),(2974814387,3002),(2974597887,3003),(2973948577,3004),(2971570197,3005),(2969627077,3006),(2969411331,3007),(2968333075,3008)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_2992 := recordedBatch d_s_4_2992 2992 0xbff8cc00c0311500c05c5f00c0a1a900c0ed8d00c11f5600c14ac400c1972100c1cc9600c2086600c23a9c00c2698b00c2af8d00c2db2000c3141e00c36dd1

private theorem s_5_2976 : rowTree 5 2976 = 410122414 := by
  exact glueRows (by decide) s_4_2976.property s_4_2992.property (by decide)

private theorem s_6_2944 : rowTree 6 2944 = 836129131 := by
  exact glueRows (by decide) s_5_2944 s_5_2976 (by decide)

private def d_s_4_3008 : List (ℕ × ℕ) := [(2968117517,3009),(2967040200,3010),(2963812934,3011),(2963598033,3012),(2960592682,3013),(2959949471,3014),(2958449732,3015),(2956737604,3016),(2956096067,3017),(2953959619,3018),(2952252683,3019),(2952039455,3020),(2951399955,3021),(2950973775,3022),(2947568764,3023),(2947143690,3024)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3008 := recordedBatch d_s_4_3008 3008 0xbc412f00bc6ef200bcc8d100bcf6aa00bd27a900bd528c00bd93b000bddb2100be0c6700be4dc200be8bed00bebd5b00bf126b00bf3d9300bf955d00bfcd98

private def d_s_4_3024 : List (ℕ × ℕ) := [(2946931199,3025),(2946506309,3026),(2945869204,3027),(2945656897,3028),(2944383696,3029),(2943959540,3030),(2943323535,3031),(2942687805,3032),(2941417169,3033),(2941205503,3034),(2940570687,3035),(2940147629,3036),(2939513271,3037),(2938667884,3038),(2938034164,3039),(2937611835,3040)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3024 := recordedBatch d_s_4_3024 3024 0xb93ec500b96c0300b99c8400b9d06100ba00e800ba2e5e00ba5f0800ba89bd00bac3c100baf46300bb255400bb532600bb8d6400bbb7e400bbe89b00bc167b

private theorem s_5_3008 : rowTree 5 3008 = 394941370 := by
  exact glueRows (by decide) s_4_3008.property s_4_3024.property (by decide)

private def d_s_4_3040 : List (ℕ × ℕ) := [(2935502012,3041),(2935080412,3042),(2931711959,3043),(2930660902,3044),(2929820599,3045),(2928141439,3046),(2927931679,3047),(2925626303,3048),(2925416904,3049),(2924998194,3050),(2924370355,3051),(2923533655,3052),(2922906445,3053),(2921235198,3054),(2919774424,3055),(2919357328,3056)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3040 := recordedBatch d_s_4_3040 3040 0xb5c4a400b5f18100b62d8600b66cc400b69c9000b6cfc500b6ffe000b72cf200b7571f00b79f8d00b7c99700b8090a00b83c7000b8731a00b8cb5d00b8f8d5

private def d_s_4_3056 : List (ℕ × ℕ) := [(2917481871,3057),(2916649108,3058),(2916232904,3059),(2914153668,3060),(2913530475,3061),(2912284889,3062),(2911040367,3063),(2910418505,3064),(2909382658,3065),(2909175577,3066),(2908140615,3067),(2907933711,3068),(2906692904,3069),(2903801802,3070),(2902564519,3071),(2900710569,3072)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3056 := recordedBatch d_s_4_3056 3056 0xb24ef800b28fa800b2c81d00b317ce00b3500c00b3799a00b3aedf00b3d89400b40e1600b43d9500b4765300b4aef600b4dea100b5234b00b5500600b582f5

private theorem s_5_3040 : rowTree 5 3040 = 380927006 := by
  exact glueRows (by decide) s_4_3040.property s_4_3056.property (by decide)

private theorem s_6_3008 : rowTree 6 3008 = 775868376 := by
  exact glueRows (by decide) s_5_3008 s_5_3040 (by decide)

private theorem s_7_2944 : rowTree 7 2944 = 1611997507 := by
  exact glueRows (by decide) s_6_2944 s_6_3008 (by decide)

private theorem s_8_2816 : rowTree 8 2816 = 3476645491 := by
  exact glueRows (by decide) s_7_2816 s_7_2944 (by decide)

private theorem s_9_2560 : rowTree 9 2560 = 8106033566 := by
  exact glueRows (by decide) s_8_2560 s_8_2816 (by decide)

private theorem s_10_2048 : rowTree 10 2048 = 22293431038 := by
  exact glueRows (by decide) s_9_2048 s_9_2560 (by decide)

private def d_s_4_3072 : List (ℕ × ℕ) := [(2900504721,3073),(2898653400,3074),(2897625910,3075),(2896804442,3076),(2895778261,3077),(2890862699,3078),(2890658246,3079),(2890249427,3080),(2889636415,3081),(2888819470,3082),(2887798938,3083),(2887594918,3084),(2886575251,3085),(2883520567,3086),(2883317151,3087),(2879660568,3088)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3072 := recordedBatch d_s_4_3072 3072 0xaec0a100af1a4f00af430900af943400afc8dc00aff1e700b0266800b0583e00b086e400b0b2cc00b0dbe900b1485600b17d7500b1af9200b1e4a700b22581

private def d_s_4_3088 : List (ℕ × ℕ) := [(2879052039,3089),(2878038395,3090),(2877430552,3091),(2877227994,3092),(2875406259,3093),(2875001742,3094),(2874395181,3095),(2873586830,3096),(2871971491,3097),(2870559558,3098),(2868947620,3099),(2868343610,3100),(2866935241,3101),(2866533104,3102),(2864524110,3103),(2864122650,3104)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3088 := recordedBatch d_s_4_3088 3088 0xab8cbf00abb7be00abf91400ac244100ac5d7800ac8b7d00acc76b00ad00c300ad3d0700ad6df900ad9c4f00adc7d600ae072c00ae2fdc00ae5e6a00ae9251

private theorem s_5_3072 : rowTree 5 3072 = 366529169 := by
  exact glueRows (by decide) s_4_3072.property s_4_3088.property (by decide)

private def d_s_4_3104 : List (ℕ × ℕ) := [(2863520669,3105),(2863320065,3106),(2862317467,3107),(2861115276,3108),(2860915009,3109),(2860314376,3110),(2859113866,3111),(2858513989,3112),(2857914364,3113),(2857514753,3114),(2856316592,3115),(2856116996,3116),(2855518376,3117),(2855119435,3118),(2853923281,3119),(2853325580,3120)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3104 := recordedBatch d_s_4_3104 3104 0xa8a10d00a8cea400a9043e00a92f4100a95cd200a984e100a9ba9300a9e57c00aa136100aa410800aa76fa00aaa4eb00aacd0a00ab033300ab366a00ab5ece

private def d_s_4_3120 : List (ℕ × ℕ) := [(2852529034,3121),(2852130928,3122),(2851931917,3123),(2851335050,3124),(2849545946,3125),(2848552969,3126),(2847957515,3127),(2847163963,3128),(2845974464,3129),(2845380088,3130),(2843202829,3131),(2843005062,3132),(2842411925,3133),(2841226393,3134),(2839449948,3135),(2839055484,3136)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3120 := recordedBatch d_s_4_3120 3120 0xa58cd200a5b71800a5f3de00a6292700a6560d00a67dc400a6c09100a6eda400a722eb00a752ca00a7801000a7b31f00a7f0d100a81e4900a8466200a87109

private theorem s_5_3104 : rowTree 5 3104 = 353389843 := by
  exact glueRows (by decide) s_4_3104.property s_4_3120.property (by decide)

private theorem s_6_3072 : rowTree 6 3072 = 719919012 := by
  exact glueRows (by decide) s_5_3072 s_5_3104 (by decide)

private def d_s_4_3136 : List (ℕ × ℕ) := [(2837675723,3137),(2837084807,3138),(2836691000,3139),(2834723603,3140),(2834133916,3141),(2832562616,3142),(2831777619,3143),(2831385284,3144),(2830600940,3145),(2828446232,3146),(2827663514,3147),(2826490251,3148),(2825903984,3149),(2825317960,3150),(2823756418,3151),(2822586393,3152)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3136 := recordedBatch d_s_4_3136 3136 0xa263ba00a297c800a2d12300a2fdcc00a32a5a00a35ea900a38dc900a3cf4d00a3fe6500a4288300a4581300a491b100a4bedd00a4fde600a5283b00a55521

private def d_s_4_3152 : List (ℕ × ℕ) := [(2820833174,3153),(2817915976,3154),(2817139075,3155),(2816750785,3156),(2816556681,3157),(2816168551,3158),(2815586558,3159),(2813067364,3160),(2812680196,3161),(2811325946,3162),(2809007407,3163),(2806885436,3164),(2806307272,3165),(2806114604,3166),(2805536759,3167),(2804574211,3168)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3152 := recordedBatch d_s_4_3152 3152 0x9f2e46009f5f27009f8add009fb1ba009fddb700a01df700a060e800a0974c00a0c0e300a106d600a132e600a15c6d00a1836300a1ad2600a1dc2600a227c8

private theorem s_5_3136 : rowTree 5 3136 = 340280510 := by
  exact glueRows (by decide) s_4_3136.property s_4_3152.property (by decide)

private def d_s_4_3168 : List (ℕ × ℕ) := [(2803997000,3169),(2802651097,3170),(2802074677,3171),(2801498493,3172),(2800346838,3173),(2799387848,3174),(2798812769,3175),(2798621128,3176),(2797471837,3177),(2796514814,3178),(2795367252,3179),(2794602733,3180),(2792884094,3181),(2791167567,3182),(2790214853,3183),(2789643536,3184)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3168 := recordedBatch d_s_4_3168 3168 0x9c2a81009c55df009c862e009cc067009cfa81009d2899009d5bd1009d8c18009dbf3f009de5d2009e118e009e4243009e7534009ea0cc009ecc7c009f026a

private def d_s_4_3184 : List (ℕ × ℕ) := [(2788882145,3185),(2787360608,3186),(2786790459,3187),(2786220544,3188),(2785461020,3189),(2783943212,3190),(2782048278,3191),(2781669600,3192),(2781480300,3193),(2780534186,3194),(2780345041,3195),(2779399699,3196),(2778266137,3197),(2777699702,3198),(2776944816,3199),(2776378920,3200)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3184 := recordedBatch d_s_4_3184 3184 0x9944e300996fa100999cde0099c7b70099f9a6009a2965009a4f8c009a7f32009aa572009ace1b009b0a58009b41b2009b6f2a009b9a59009bc555009bfca7

private theorem s_5_3168 : rowTree 5 3168 = 327370168 := by
  exact glueRows (by decide) s_4_3168.property s_4_3184.property (by decide)

private theorem s_6_3136 : rowTree 6 3136 = 667650678 := by
  exact glueRows (by decide) s_5_3136 s_5_3168 (by decide)

private theorem s_7_3072 : rowTree 7 3072 = 1387569690 := by
  exact glueRows (by decide) s_6_3072 s_6_3136 (by decide)

private def d_s_4_3200 : List (ℕ × ℕ) := [(2775436273,3201),(2773552897,3202),(2772612168,3203),(2770920462,3204),(2768480528,3205),(2768105535,3206),(2767543235,3207),(2764735162,3208),(2764548160,3209),(2764174231,3210),(2763426677,3211),(2762866277,3212),(2761746158,3213),(2760626947,3214),(2758949831,3215),(2758577415,3216)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3200 := recordedBatch d_s_4_3200 3200 0x962eb30096568000968ef20096c05b0096f19d00971bd8009748b10097708d009796460097dd2a0098076b00982f97009871ee0098aab10098da060099154a

private def d_s_4_3216 : List (ℕ × ℕ) := [(2757832885,3217),(2755787498,3218),(2755230191,3219),(2755044472,3220),(2753930686,3221),(2750779841,3222),(2750224558,3223),(2748560053,3224),(2747451502,3225),(2746897562,3226),(2746712965,3227),(2744131207,3228),(2742842148,3229),(2741370420,3230),(2740083952,3231),(2739716612,3232)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3216 := recordedBatch d_s_4_3216 3216 0x9315ae00933d0900936f850093a4590093d71f00941a1c00943f3500946909009499e30094d1390094fb170095452e0095761900959b690095c57b00960247

private theorem s_5_3200 : rowTree 5 3200 = 314693191 := by
  exact glueRows (by decide) s_4_3200.property s_4_3216.property (by decide)

private def d_s_4_3232 : List (ℕ × ℕ) := [(2738431695,3233),(2737331298,3234),(2736964695,3235),(2736414975,3236),(2735865475,3237),(2735682358,3238),(2732390432,3239),(2732025151,3240),(2731477413,3241),(2729653205,3242),(2728559850,3243),(2726375764,3244),(2725830289,3245),(2723832080,3246),(2723650569,3247),(2722199359,3248)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3232 := recordedBatch d_s_4_3232 3232 0x9016ad00904aa600906f0b0090aa060090d3300091103e0091402e0091790c0091a2060091c91600921427009238f60092625e00928be30092b3020092e305

private def d_s_4_3248 : List (ℕ × ℕ) := [(2720568594,3249),(2719482502,3250),(2718397278,3251),(2716771064,3252),(2716590494,3253),(2716048926,3254),(2715507575,3255),(2714966440,3256),(2714605803,3257),(2714065027,3258),(2712804053,3259),(2712443990,3260),(2712263995,3261),(2710285619,3262),(2709566924,3263),(2708489597,3264)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3248 := recordedBatch d_s_4_3248 3248 0x8d4f02008d7e17008da8a7008de2a6008e06fa008e2d6a008e5e6e008e8717008ead63008ed5f0008efe9c008f2762008f4bba008f81ed008fb11f008fe092

private theorem s_5_3232 : rowTree 5 3232 = 302108293 := by
  exact glueRows (by decide) s_4_3232.property s_4_3248.property (by decide)

private theorem s_6_3200 : rowTree 6 3200 = 616801484 := by
  exact glueRows (by decide) s_5_3200 s_5_3232 (by decide)

private def d_s_4_3264 : List (ℕ × ℕ) := [(2707951255,3265),(2707054493,3266),(2706516722,3267),(2705800024,3268),(2704725690,3269),(2703115788,3270),(2702043584,3271),(2701507801,3272),(2700615301,3273),(2700436872,3274),(2698475705,3275),(2697229173,3276),(2696695297,3277),(2696161633,3278),(2695805974,3279),(2694206669,3280)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3264 := recordedBatch d_s_4_3264 3264 0x8a88f1008abdaa008ae37a008b0b35008b3332008b6391008b9ccc008bc0e3008bed3c008c151d008c43ac008c78a5008ca737008cd1a8008cf9d9008d26b1

private def d_s_4_3280 : List (ℕ × ℕ) := [(2693673989,3281),(2691899909,3282),(2689951118,3283),(2689774096,3284),(2688712447,3285),(2686591663,3286),(2686238525,3287),(2684650548,3288),(2683064448,3289),(2682888330,3290),(2680952561,3291),(2680776721,3292),(2680425109,3293),(2679370826,3294),(2678668432,3295),(2677615531,3296)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3280 := recordedBatch d_s_4_3280 3280 0x87af760087dcdd00880680008834050088598300887cc30088b4fe0088d8af00890c6b008940a60089662e0089a0620089ce920089f236008a2aa7008a60fd

private theorem s_5_3264 : rowTree 5 3264 = 290278567 := by
  exact glueRows (by decide) s_4_3264.property s_4_3280.property (by decide)

private def d_s_4_3296 : List (ℕ × ℕ) := [(2676738745,3297),(2675512210,3298),(2675161977,3299),(2674986896,3300),(2673412190,3301),(2672014008,3302),(2668699179,3303),(2668176536,3304),(2667654098,3305),(2667131865,3306),(2666088012,3307),(2665218758,3308),(2664697478,3309),(2663655529,3310),(2662961349,3311),(2662440952,3312)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3296 := recordedBatch d_s_4_3296 3296 0x84ee650085154200853e3300856b47008592070085bd270085ea69008611780086387300865f940086a6fd0086d86500870bd700872f0700875448008783d8

private def d_s_4_3312 : List (ℕ × ℕ) := [(2662094133,3313),(2661574074,3314),(2660361394,3315),(2657766510,3316),(2657248140,3317),(2656384640,3318),(2655694244,3319),(2653797505,3320),(2653280682,3321),(2652591899,3322),(2651559393,3323),(2650699586,3324),(2650527692,3325),(2649668553,3326),(2649496793,3327),(2648981644,3328)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3312 := recordedBatch d_s_4_3312 3312 0x82486500826ef8008291a90082bbf20082deb1008309120083357e00835df9008384bf0083bacb0083e34200840e4c008434f50084739f0084a26f0084c977

private theorem s_5_3296 : rowTree 5 3296 = 278587483 := by
  exact glueRows (by decide) s_4_3296.property s_4_3312.property (by decide)

private theorem s_6_3264 : rowTree 6 3264 = 568866050 := by
  exact glueRows (by decide) s_5_3264 s_5_3296 (by decide)

private theorem s_7_3200 : rowTree 7 3200 = 1185667534 := by
  exact glueRows (by decide) s_6_3200 s_6_3264 (by decide)

private theorem s_8_3072 : rowTree 8 3072 = 2573237224 := by
  exact glueRows (by decide) s_7_3072 s_7_3200 (by decide)

private def d_s_4_3328 : List (ℕ × ℕ) := [(2648123507,3329),(2647951946,3330),(2647094477,3331),(2646066246,3332),(2644525397,3333),(2642815445,3334),(2642302891,3335),(2641961299,3336),(2641278379,3337),(2639402168,3338),(2638890936,3339),(2638379903,3340),(2635827703,3341),(2635317855,3342),(2634128977,3343),(2633619786,3344)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3328 := recordedBatch d_s_4_3328 3328 0x7f955b007fbb5e007fe8c100800ec700804b980080719c008097e80080cdac0080f5a0008119fe00814027008173b80081a57d0081d1970081fbcc00821e5e

private def d_s_4_3344 : List (ℕ × ℕ) := [(2632601995,3345),(2631584990,3346),(2631076782,3347),(2630230205,3348),(2630060955,3349),(2629215031,3350),(2626680522,3351),(2626511729,3352),(2625162161,3353),(2624487897,3354),(2624150895,3355),(2623982427,3356),(2623477151,3357),(2621962490,3358),(2621626136,3359),(2621457991,3360)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3344 := recordedBatch d_s_4_3344 3344 0x7d0c63007d2e35007d51c1007d82a1007da825007dca10007dedde007e1574007e4480007e668b007ea2dc007ecc9b007eeeb6007f184e007f3e38007f69d9

private theorem s_5_3328 : rowTree 5 3328 = 267455964 := by
  exact glueRows (by decide) s_4_3328.property s_4_3344.property (by decide)

private def d_s_4_3360 : List (ℕ × ℕ) := [(2620953687,3361),(2620617592,3362),(2618435073,3363),(2618099623,3364),(2617428982,3365),(2616926227,3366),(2616088730,3367),(2615921295,3368),(2615586489,3369),(2615084441,3370),(2614415343,3371),(2614080923,3372),(2613579453,3373),(2611074984,3374),(2610074541,3375),(2609907875,3376)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3360 := recordedBatch d_s_4_3360 3360 0x7a904a007ab1eb007adc6b007b1748007b3cb9007b603e007b876f007baca9007bd035007bf1e5007c1b02007c404d007c6793007c8b25007cc2f0007ce6cd

private def d_s_4_3376 : List (ℕ × ℕ) := [(2609408004,3377),(2608908325,3378),(2608575312,3379),(2606911520,3380),(2605083799,3381),(2604419809,3382),(2604087940,3383),(2603922038,3384),(2603590297,3385),(2597633371,3386),(2596973172,3387),(2596643199,3388),(2595983503,3389),(2594171068,3390),(2594006427,3391),(2593677207,3392)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3376 := recordedBatch d_s_4_3376 3376 0x77e86d00780b6f00782c9000785f65007886140078a92f0078cfa900792ecc007951fa00797375007996870079bd6a0079f0d8007a2276007a45d8007a6ae9

private theorem s_5_3360 : rowTree 5 3360 = 256789453 := by
  exact glueRows (by decide) s_4_3360.property s_4_3376.property (by decide)

private theorem s_6_3328 : rowTree 6 3328 = 524245417 := by
  exact glueRows (by decide) s_5_3328 s_5_3360 (by decide)

private def d_s_4_3392 : List (ℕ × ℕ) := [(2592525595,3393),(2591703641,3394),(2591539313,3395),(2591210719,3396),(2589568997,3397),(2589076887,3398),(2588257117,3399),(2586782840,3400),(2586291788,3401),(2584656292,3402),(2583349383,3403),(2582859633,3404),(2582206922,3405),(2581717605,3406),(2581391497,3407),(2579762191,3408)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3392 := recordedBatch d_s_4_3392 3392 0x7561c1007591ed0075b45f0075d8a50075feb80076230100765026007680770076a4e30076d3d10076fbb90077203d007750c2007773a5007794b30077bcb9

private def d_s_4_3408 : List (ℕ × ℕ) := [(2578785594,3409),(2576997085,3410),(2576834616,3411),(2576509741,3412),(2576347333,3413),(2575373320,3414),(2574562204,3415),(2573103483,3416),(2572941504,3417),(2571161090,3418),(2570675950,3419),(2569221628,3420),(2566801411,3421),(2566640225,3422),(2565834601,3423),(2564707575,3424)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3408 := recordedBatch d_s_4_3408 3408 0x72d764007301b9007328ec00734962007380c40073ae700073d2550074039d0074244400745248007479ef0074a3010074c3b50074e609007506d10075385e

private theorem s_5_3392 : rowTree 5 3392 = 246016639 := by
  exact glueRows (by decide) s_4_3392.property s_4_3408.property (by decide)

private def d_s_4_3424 : List (ℕ × ℕ) := [(2563903163,3425),(2563259996,3426),(2561974631,3427),(2557966159,3428),(2557485985,3429),(2556686096,3430),(2556046544,3431),(2555247555,3432),(2554289427,3433),(2553810633,3434),(2552375325,3435),(2552215946,3436),(2550464090,3437),(2549986728,3438),(2549827647,3439),(2549509545,3440)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3424 := recordedBatch d_s_4_3424 3424 0x705361007075060070951e0070b8470070e8be007108e90071360f0071595d007181b40071a8600071cd7f0071f449007217b200725f4700728b380072b065

private def d_s_4_3440 : List (ℕ × ℕ) := [(2549032540,3441),(2548396812,3442),(2547920224,3443),(2547443814,3444),(2546650193,3445),(2545222921,3446),(2545064433,3447),(2543322378,3448),(2543164127,3449),(2541898832,3450),(2540792731,3451),(2540003248,3452),(2539529794,3453),(2539372015,3454),(2538425753,3455),(2537637741,3456)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3440 := recordedBatch d_s_4_3440 3440 0x6df844006e1e31006e45e9006e65bb006e889c006eaeab006ed7e0006f02ca006f22c0006f5278006f7262006f9ed2006fc52c006fe85300700ba300703059

private theorem s_5_3424 : rowTree 5 3424 = 235436354 := by
  exact glueRows (by decide) s_4_3424.property s_4_3440.property (by decide)

private theorem s_6_3392 : rowTree 6 3392 = 481452993 := by
  exact glueRows (by decide) s_5_3392 s_5_3424 (by decide)

private theorem s_7_3328 : rowTree 7 3328 = 1005698410 := by
  exact glueRows (by decide) s_6_3328 s_6_3392 (by decide)

private def d_s_4_3456 : List (ℕ × ℕ) := [(2536063182,3457),(2535748504,3458),(2534647749,3459),(2534176289,3460),(2533862079,3461),(2531037698,3462),(2530880973,3463),(2530567580,3464),(2530097637,3465),(2529158273,3466),(2529001780,3467),(2528688853,3468),(2527594216,3469),(2526656710,3470),(2526188218,3471),(2525875986,3472)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3456 := recordedBatch d_s_4_3456 3456 0x6ba387006bc485006be6fa006c0e11006c36d4006c580f006c7793006c9eb6006cc149006ce27d006d0215006d3c17006d5d3c006d8001006da935006dca73

private def d_s_4_3472 : List (ℕ × ℕ) := [(2525407783,3473),(2525251754,3474),(2524783783,3475),(2524471898,3476),(2522913630,3477),(2522135218,3478),(2521979593,3479),(2521201756,3480),(2520735284,3481),(2519802859,3482),(2519647521,3483),(2517784967,3484),(2516854723,3485),(2515925165,3486),(2515460644,3487),(2514996294,3488)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3472 := recordedBatch d_s_4_3472 3472 0x695cb500697efa0069a1030069c7a60069ee5b006a1e16006a3d68006a642f006a868d006aac20006acb6f006af121006b1e0d006b3eec006b617b006b8111

private theorem s_5_3456 : rowTree 5 3456 = 225596988 := by
  exact glueRows (by decide) s_4_3456.property s_4_3472.property (by decide)

private def d_s_4_3488 : List (ℕ × ℕ) := [(2514686822,3489),(2512831593,3490),(2512677114,3491),(2512368213,3492),(2510516401,3493),(2510362207,3494),(2509899737,3495),(2509591519,3496),(2509129333,3497),(2508513350,3498),(2507282291,3499),(2506820956,3500),(2506667215,3501),(2505898793,3502),(2504977309,3503),(2503903101,3504)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3488 := recordedBatch d_s_4_3488 3488 0x671a59006741dc0067680400678cda0067abdb0067cdb80067f6ec00681a5000683c2600685cd900687eee00689dfe0068ccfb0068ed9900690ca600693bff

private def d_s_4_3504 : List (ℕ × ℕ) := [(2503443008,3505),(2500839004,3506),(2500380037,3507),(2499309767,3508),(2498851360,3509),(2498545849,3510),(2498393121,3511),(2496104447,3512),(2494428749,3513),(2493819962,3514),(2493515680,3515),(2493059396,3516),(2492451277,3517),(2492147329,3518),(2491995383,3519),(2489870078,3520)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3504 := recordedBatch d_s_4_3504 3504 0x64c1a70064f2c50065115c0065316500655464006575d5006595ea0065b8fa0065e628006618ec006637a8006657d0006679760066a0cf0066c2840066f89c

private theorem s_5_3488 : rowTree 5 3488 = 216009025 := by
  exact glueRows (by decide) s_4_3488.property s_4_3504.property (by decide)

private theorem s_6_3456 : rowTree 6 3456 = 441606013 := by
  exact glueRows (by decide) s_5_3456 s_5_3488 (by decide)

private def d_s_4_3520 : List (ℕ × ℕ) := [(2489718409,3521),(2489263514,3522),(2488960343,3523),(2486991528,3524),(2485630326,3525),(2483968657,3526),(2483817706,3527),(2483364965,3528),(2482158459,3529),(2481706322,3530),(2481555646,3531),(2480350898,3532),(2479448104,3533),(2479297702,3534),(2478395675,3535),(2478095145,3536)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3520 := recordedBatch d_s_4_3520 3520 0x6284c70062a4940062c9be0062e81800630d460063353f006353ae006374b500639ce20063be060063dc99006408cb0064325e006461e2006481be0064a30a

private def d_s_4_3536 : List (ℕ × ℕ) := [(2477644486,3537),(2477193992,3538),(2476143475,3539),(2475393651,3540),(2474943975,3541),(2474344660,3542),(2473446233,3543),(2473146902,3544),(2471800809,3545),(2471651333,3546),(2470904227,3547),(2470306867,3548),(2469113014,3549),(2468665616,3550),(2468218380,3551),(2465984631,3552)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3536 := recordedBatch d_s_4_3536 3536 0x604a5900607b4100609bf50060bcac0060e41c00610626006129b6006147c4006170e9006190820061b5740061d7aa0061f8d300621c6c006242ce006263ce

private theorem s_5_3520 : rowTree 5 3520 = 206480328 := by
  exact glueRows (by decide) s_4_3520.property s_4_3536.property (by decide)

private def d_s_4_3552 : List (ℕ × ℕ) := [(2465835858,3553),(2465092263,3554),(2463754921,3555),(2463606417,3556),(2462864166,3557),(2462270687,3558),(2461974055,3559),(2461381004,3560),(2460491965,3561),(2458715810,3562),(2455761244,3563),(2455613702,3564),(2454728823,3565),(2453991911,3566),(2453549976,3567),(2452666583,3568)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3552 := recordedBatch d_s_4_3552 3552 0x5e0b5c005e2f99005e4fd5005e72d4005e96f4005eb4a7005eeb66005f1795005f3be1005f5db9005f7d06005f9f27005fc238005fe03c0060091a00602c56

private def d_s_4_3568 : List (ℕ × ℕ) := [(2452519413,3569),(2451636761,3570),(2451342686,3571),(2451195674,3572),(2450901704,3573),(2450460881,3574),(2449139364,3575),(2448112502,3576),(2447233019,3577),(2446793515,3578),(2446500600,3579),(2445475949,3580),(2443283156,3581),(2442991080,3582),(2442407139,3583),(2441677605,3584)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3568 := recordedBatch d_s_4_3568 3568 0x5be6b4005c0928005c2a58005c4934005c7861005c9d9e005cbc68005cdc8b005d0075005d25d6005d4dba005d6dde005d8cc3005daa71005dc976005deda1

private theorem s_5_3552 : rowTree 5 3552 = 197180519 := by
  exact glueRows (by decide) s_4_3552.property s_4_3568.property (by decide)

private theorem s_6_3520 : rowTree 6 3520 = 403660847 := by
  exact glueRows (by decide) s_5_3520 s_5_3552 (by decide)

private theorem s_7_3456 : rowTree 7 3456 = 845266860 := by
  exact glueRows (by decide) s_6_3456 s_6_3520 (by decide)

private theorem s_8_3328 : rowTree 8 3328 = 1850965270 := by
  exact glueRows (by decide) s_7_3328 s_7_3456 (by decide)

private theorem s_9_3072 : rowTree 9 3072 = 4424202494 := by
  exact glueRows (by decide) s_8_3072 s_8_3328 (by decide)

private def d_s_4_3584 : List (ℕ × ℕ) := [(2441094291,3585),(2440656989,3586),(2439928500,3587),(2438618315,3588),(2438036462,3589),(2437745640,3590),(2436728308,3591),(2435566682,3592),(2435131357,3593),(2434551167,3594),(2434261176,3595),(2433826318,3596),(2433681400,3597),(2432957068,3598),(2432812254,3599),(2431943728,3600)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3584 := recordedBatch d_s_4_3584 3584 0x59d1dc0059f55a005a1272005a34ab005a51f8005a71af005a9015005ab143005ad105005af6f7005b1beb005b3a91005b5bb8005b8341005ba596005bc586

private def d_s_4_3600 : List (ℕ × ℕ) := [(2431654358,3601),(2431509698,3602),(2431220431,3603),(2430786658,3604),(2430208536,3605),(2429919578,3606),(2429486270,3607),(2427177901,3608),(2425449501,3609),(2424730061,3610),(2424154816,3611),(2422861512,3612),(2422143605,3613),(2422000075,3614),(2421569587,3615),(2420852446,3616)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3600 := recordedBatch d_s_4_3600 3600 0x57b6a20057d85f0057f7ad0058149f0058367e00585cfd00587d8f00589f370058c9cf0058f93e005918df0059372e0059580d005977ba005996190059b354

private theorem s_5_3584 : rowTree 5 3584 = 188216251 := by
  exact glueRows (by decide) s_4_3584.property s_4_3600.property (by decide)

private def d_s_4_3616 : List (ℕ × ℕ) := [(2420709069,3617),(2420422365,3618),(2419133040,3619),(2418703569,3620),(2417845087,3621),(2417702066,3622),(2416558505,3623),(2416415636,3624),(2414845190,3625),(2414417241,3626),(2413989444,3627),(2413419283,3628),(2412137406,3629),(2411852729,3630),(2410572514,3631),(2409719793,3632)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3616 := recordedBatch d_s_4_3616 3616 0x55a09b0055c31d0055e92d0056070e00562d1e00564d7600566c8100568b8e0056b4580056d1280056f62f00571304005736080057553d00577b8f005799af

private def d_s_4_3632 : List (ℕ × ℕ) := [(2409151647,3633),(2408725713,3634),(2408441841,3635),(2407023484,3636),(2406598302,3637),(2404474646,3638),(2402919678,3639),(2402072362,3640),(2401931200,3641),(2401507816,3642),(2400238557,3643),(2399956682,3644),(2395596065,3645),(2395315279,3646),(2395174911,3647),(2394333046,3648)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3632 := recordedBatch d_s_4_3632 3632 0x536ef30053911a0053ad660053cadf0054094b005426d700544c5d00546afd005487680054a9940054d1760054fe0400551ceb005543e20055618f00558070

private theorem s_5_3616 : rowTree 5 3616 = 179411164 := by
  exact glueRows (by decide) s_4_3616.property s_4_3632.property (by decide)

private theorem s_6_3584 : rowTree 6 3584 = 367627415 := by
  exact glueRows (by decide) s_5_3584 s_5_3616 (by decide)

private def d_s_4_3648 : List (ℕ × ℕ) := [(2393912336,3649),(2393211480,3650),(2393071359,3651),(2392230972,3652),(2391391175,3653),(2389433940,3654),(2389294261,3655),(2389014950,3656),(2388037876,3657),(2386504088,3658),(2386086124,3659),(2385946836,3660),(2385529067,3661),(2385111445,3662),(2384415732,3663),(2383442416,3664)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3648 := recordedBatch d_s_4_3648 3648 0x51688400518b380051abaa0051c9f20051e82f0052045400522281005249a000526c46005289860052a5ac0052d05a0052f201005313c500532ffc00535096

private def d_s_4_3664 : List (ℕ × ℕ) := [(2383164472,3665),(2383025524,3666),(2382331027,3667),(2381914524,3668),(2381359412,3669),(2380665886,3670),(2379695629,3671),(2379003071,3672),(2378587731,3673),(2378449316,3674),(2377619166,3675),(2376098728,3676),(2374856179,3677),(2374304352,3678),(2373614929,3679),(2372374976,3680)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3664 := recordedBatch d_s_4_3664 3664 0x4f650b004f8918004fa929004fc811004fec7200501337005034810050508000506e8f00508eeb0050b15c0050d1720050f0c000510ef500512f5700514b5a

private theorem s_5_3648 : rowTree 5 3648 = 170627803 := by
  exact glueRows (by decide) s_4_3648.property s_4_3664.property (by decide)

private def d_s_4_3680 : List (ℕ × ℕ) := [(2371549060,3681),(2371411463,3682),(2370586217,3683),(2370311263,3684),(2369486783,3685),(2369349426,3686),(2368662877,3687),(2368525615,3688),(2368113924,3689),(2366879710,3690),(2366468591,3691),(2366057615,3692),(2363731444,3693),(2363321418,3694),(2363184775,3695),(2362365244,3696)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3680 := recordedBatch d_s_4_3680 3680 0x4d6ec6004d8f86004dab1b004dc8ac004df4d8004e127e004e305d004e5440004e720d004e8dca004ead76004ec922004eea2d004f070a004f2824004f43d5

private def d_s_4_3696 : List (ℕ × ℕ) := [(2362092193,3697),(2361682736,3698),(2360455215,3699),(2359228969,3700),(2359092798,3701),(2358003996,3702),(2357595955,3703),(2357188054,3704),(2356644407,3705),(2356236836,3706),(2355557864,3707),(2354336699,3708),(2353794366,3709),(2353116801,3710),(2352575029,3711),(2351898165,3712)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3696 := recordedBatch d_s_4_3696 3696 0x4b7928004b9868004bb6d6004bd61b004bf487004c1820004c37b2004c5533004c73cb004c914d004caecd004cd18c004ced01004d10b9004d3492004d5236

private theorem s_5_3680 : rowTree 5 3680 = 162272165 := by
  exact glueRows (by decide) s_4_3680.property s_4_3696.property (by decide)

private theorem s_6_3648 : rowTree 6 3648 = 332899968 := by
  exact glueRows (by decide) s_5_3648 s_5_3680 (by decide)

private theorem s_7_3584 : rowTree 7 3584 = 700527383 := by
  exact glueRows (by decide) s_6_3584 s_6_3648 (by decide)

private def d_s_4_3712 : List (ℕ × ℕ) := [(2351762839,3713),(2351492234,3714),(2350275281,3715),(2348519681,3716),(2347710289,3717),(2346227850,3718),(2346093176,3719),(2345823874,3720),(2345689246,3721),(2344209358,3722),(2343806077,3723),(2343402934,3724),(2342462806,3725),(2341389297,3726),(2340986985,3727),(2339646943,3728)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3712 := recordedBatch d_s_4_3712 3712 0x497c880049a02e0049bd2b0049df18004a0013004a1d36004a3a39004a5f0d004a7a3a004a9661004ab188004ad68f004af6b7004b1e35004b417a004b5dde

private def d_s_4_3728 : List (ℕ × ℕ) := [(2338977497,3729),(2338174667,3730),(2338040916,3731),(2336837842,3732),(2334035478,3733),(2333768936,3734),(2332170966,3735),(2332037901,3736),(2331638796,3737),(2330973924,3738),(2330176578,3739),(2330043740,3740),(2329645317,3741),(2328981582,3742),(2328450866,3743),(2328185598,3744)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3728 := recordedBatch d_s_4_3728 3728 0x478b7c0047a7420047c4f70047e3600048003400481aff00483aa10048593b004875f3004890c90048b61b0048d20900490058004922f900493ded00495dc0

private theorem s_5_3712 : rowTree 5 3712 = 153982080 := by
  exact glueRows (by decide) s_4_3712.property s_4_3728.property (by decide)

private def d_s_4_3744 : List (ℕ × ℕ) := [(2327787810,3745),(2326992642,3746),(2326198018,3747),(2325668569,3748),(2325403935,3749),(2325007097,3750),(2324213828,3751),(2322233020,3752),(2320914356,3753),(2320519049,3754),(2318939166,3755),(2318544531,3756),(2317887105,3757),(2317098686,3758),(2316967335,3759),(2316310803,3760)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3744 := recordedBatch d_s_4_3744 3744 0x459c980045bad30045d54b0045f458004612a000462f16004653d000467030004693140046bab90046da220046f6b70047126b00472fef00474f7300476ed0

private def d_s_4_3760 : List (ℕ × ℕ) := [(2314998854,3761),(2314605559,3762),(2314212398,3763),(2313950365,3764),(2313164621,3765),(2312248594,3766),(2311594733,3767),(2310418714,3768),(2309635367,3769),(2309113430,3770),(2308722132,3771),(2307939934,3772),(2307679320,3773),(2306767631,3774),(2306116866,3775),(2305986757,3776)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3760 := recordedBatch d_s_4_3760 3760 0x43be3e0043d88f0043f656004415ec0044311c00444fc500446bd7004488c30044a7990044c9540044e7340045070e0045261f0045415800455dac004579ef

private theorem s_5_3744 : rowTree 5 3744 = 145882322 := by
  exact glueRows (by decide) s_4_3744.property s_4_3760.property (by decide)

private theorem s_6_3712 : rowTree 6 3712 = 299864402 := by
  exact glueRows (by decide) s_5_3712 s_5_3744 (by decide)

private def d_s_4_3776 : List (ℕ × ℕ) := [(2305206411,3777),(2303257855,3778),(2302219972,3779),(2302090302,3780),(2301312591,3781),(2300923932,3782),(2300664899,3783),(2300535405,3784),(2300276459,3785),(2299888151,3786),(2298206993,3787),(2297948572,3788),(2296786394,3789),(2296657335,3790),(2296399262,3791),(2296012261,3792)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3776 := recordedBatch d_s_4_3776 3776 0x41e723004202e400421dc1004237e0004258f6004273c7004298350042b4160042cf1a0042e93d0043044b0043201a00433eaf004358e90043793900439f9f

private def d_s_4_3792 : List (ℕ × ℕ) := [(2295109766,3793),(2291635349,3794),(2291249952,3795),(2287915266,3796),(2287787203,3797),(2286763212,3798),(2286379452,3799),(2285995820,3800),(2285228943,3801),(2283569141,3802),(2283314001,3803),(2283186452,3804),(2282803891,3805),(2281402264,3806),(2281020301,3807),(2280893009,3808)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3792 := recordedBatch d_s_4_3792 3792 0x3ff30b00400cde0040282a00404a30004065c100407f9e00409a650040be410040dc7c0040f7ed004113990041333800414d3300417c46004197e20041c80a

private theorem s_5_3776 : rowTree 5 3776 = 137943747 := by
  exact glueRows (by decide) s_4_3776.property s_4_3792.property (by decide)

private def d_s_4_3808 : List (ℕ × ℕ) := [(2280129551,3809),(2279366604,3810),(2278985323,3811),(2278350136,3812),(2277207692,3813),(2277080825,3814),(2276319917,3815),(2275559517,3816),(2274926239,3817),(2273787225,3818),(2273028516,3819),(2272649352,3820),(2272143996,3821),(2271765126,3822),(2271133958,3823),(2270755425,3824)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3808 := recordedBatch d_s_4_3808 3808 0x3e2595003e40a1003e5d79003e7888003e947e003eafa1003ecd35003eed1e003f09f9003f2791003f4555003f5ee8003f7f25003f9c1b003fb76d003fd53f

private def d_s_4_3824 : List (ℕ × ℕ) := [(2270250911,3825),(2269998738,3826),(2269872672,3827),(2269620583,3828),(2268360977,3829),(2266851295,3830),(2266474188,3831),(2266097207,3832),(2265469183,3833),(2264590535,3834),(2263963346,3835),(2263837950,3836),(2262459509,3837),(2262083862,3838),(2261207838,3839),(2260582521,3840)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3824 := recordedBatch d_s_4_3824 3824 0x3c5ca6003c78f1003c96d8003cb1bb003cd2c8003cec23003d08a4003d26a5003d4334003d5e47003d793f003d9b50003dbbce003dd615003defa0003e09de

private theorem s_5_3808 : rowTree 5 3808 = 130221605 := by
  exact glueRows (by decide) s_4_3808.property s_4_3824.property (by decide)

private theorem s_6_3776 : rowTree 6 3776 = 268165352 := by
  exact glueRows (by decide) s_5_3776 s_5_3808 (by decide)

private theorem s_7_3712 : rowTree 7 3712 = 568029754 := by
  exact glueRows (by decide) s_6_3712 s_6_3776 (by decide)

private theorem s_8_3584 : rowTree 8 3584 = 1268557137 := by
  exact glueRows (by decide) s_7_3584 s_7_3712 (by decide)

private def d_s_4_3840 : List (ℕ × ℕ) := [(2258958315,3841),(2258708644,3842),(2257585808,3843),(2257087129,3844),(2256339522,3845),(2255592410,3846),(2254970195,3847),(2254223990,3848),(2253851072,3849),(2253354041,3850),(2252360635,3851),(2251988334,3852),(2251492124,3853),(2251120110,3854),(2250748218,3855),(2249385667,3856)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3840 := recordedBatch d_s_4_3840 3840 0x3a9206003ab288003acd1a003ae79e003b02ec003b1d8e003b3bd1003b5743003b71f4003b8ecf003bab20003bc81f003be512003c00a2003c1fdd003c39e7

private def d_s_4_3856 : List (ℕ × ℕ) := [(2249261881,3857),(2248643153,3858),(2247406718,3859),(2246789010,3860),(2246418548,3861),(2243705556,3862),(2242597584,3863),(2242228503,3864),(2241613638,3865),(2241490705,3866),(2241244881,3867),(2240876245,3868),(2240016566,3869),(2239771064,3870),(2238176616,3871),(2237931517,3872)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3856 := recordedBatch d_s_4_3856 3856 0x38caff0038e47b0039061300391f9b00393cce00395714003970af003989750039a5590039bfb20039de69003a06d1003a2146003a3d41003a5cfc003a78f9

private theorem s_5_3840 : rowTree 5 3840 = 122700349 := by
  exact glueRows (by decide) s_4_3840.property s_4_3856.property (by decide)

private def d_s_4_3872 : List (ℕ × ℕ) := [(2237808988,3873),(2237074096,3874),(2236462054,3875),(2235972662,3876),(2235728046,3877),(2235238975,3878),(2234505769,3879),(2234261474,3880),(2233528909,3881),(2233040799,3882),(2231699597,3883),(2231212286,3884),(2230846943,3885),(2230238303,3886),(2229143589,3887),(2228778922,3888)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3872 := recordedBatch d_s_4_3872 3872 0x37157700372f7e00374ddd0037694b0037836d00379e450037be210037d90b0037f55800380ebc00382b08003845e000385f5d00387a30003895c80038b224

private def d_s_4_3888 : List (ℕ × ℕ) := [(2228414376,3889),(2227928498,3890),(2227564230,3891),(2226836049,3892),(2226593428,3893),(2226108345,3894),(2225017680,3895),(2224412216,3896),(2223686095,3897),(2223323212,3898),(2222597801,3899),(2222476946,3900),(2222114457,3901),(2221872864,3902),(2221752087,3903),(2220786344,3904)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3888 := recordedBatch d_s_4_3888 3888 0x356ab0003587d40035a0490035b99a0035d36a0035ebdb003607d2003621a900363da3003658ee003676f5003691790036aac40036c6cd0036e0ab0036fb77

private theorem s_5_3872 : rowTree 5 3872 = 115436873 := by
  exact glueRows (by decide) s_4_3872.property s_4_3888.property (by decide)

private theorem s_6_3840 : rowTree 6 3840 = 238137222 := by
  exact glueRows (by decide) s_5_3840 s_5_3872 (by decide)

private def d_s_4_3904 : List (ℕ × ℕ) := [(2220062588,3905),(2219339303,3906),(2218496066,3907),(2217894146,3908),(2217052007,3909),(2216691286,3910),(2216090344,3911),(2215369645,3912),(2215249574,3913),(2214529422,3914),(2214169521,3915),(2213929652,3916),(2213569946,3917),(2213450070,3918),(2212731087,3919),(2212491529,3920)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3904 := recordedBatch d_s_4_3904 3904 0x33c18a0033da820033f5ff00340e46003427d5003440d800345a580034760800348e740034aa0b0034c50b0034dec50034fb400035166a0035331300354ec3

private def d_s_4_3920 : List (ℕ × ℕ) := [(2210935670,3921),(2210576937,3922),(2209501434,3923),(2209143165,3924),(2208546309,3925),(2208188350,3926),(2208069056,3927),(2206995992,3928),(2206400295,3929),(2205923969,3930),(2205685884,3931),(2204139578,3932),(2203545422,3933),(2202358071,3934),(2202002116,3935),(2201053462,3936)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3920 := recordedBatch d_s_4_3920 3920 0x320b2f003227ab003240f400325ea70032794b003299110032b1e00032cc0d0032e6ad003303f200331c35003335970033507e00336a16003387a60033a12e

private theorem s_5_3904 : rowTree 5 3904 = 108383166 := by
  exact glueRows (by decide) s_4_3904.property s_4_3920.property (by decide)

private def d_s_4_3936 : List (ℕ × ℕ) := [(2199868795,3937),(2199158606,3938),(2198567132,3939),(2198094182,3940),(2197503281,3941),(2197385138,3942),(2196440458,3943),(2196086413,3944),(2194907084,3945),(2194317895,3946),(2193140465,3947),(2192905130,3948),(2191141730,3949),(2191024271,3950),(2190789391,3951),(2190319781,3952)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3936 := recordedBatch d_s_4_3936 3936 0x305ef500307892003090ee0030a8bc0030c8f40030e15c0030fec1003118fd0031366d00314f7d00316bb70031839200319e0c0031b7ec0031d2410031ed6d

private def d_s_4_3952 : List (ℕ × ℕ) := [(2189381164,3953),(2189263894,3954),(2188209025,3955),(2187974747,3956),(2187857628,3957),(2187506343,3958),(2186921120,3959),(2185868506,3960),(2185167327,3961),(2184349853,3962),(2183299713,3963),(2182949890,3964),(2182017578,3965),(2180853308,3966),(2180504269,3967),(2180271638,3968)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3952 := recordedBatch d_s_4_3952 3952 0x2eba0f002ed239002eeae0002f07c9002f2395002f3c6d002f58cc002f73e7002f8eb4002fab42002fc560002fde4d002ff5fd00300e5700302aec003042c3

private theorem s_5_3936 : rowTree 5 3936 = 101341540 := by
  exact glueRows (by decide) s_4_3936.property s_4_3952.property (by decide)

private theorem s_6_3904 : rowTree 6 3904 = 209724706 := by
  exact glueRows (by decide) s_5_3904 s_5_3936 (by decide)

private theorem s_7_3840 : rowTree 7 3840 = 447861928 := by
  exact glueRows (by decide) s_6_3840 s_6_3904 (by decide)

private def d_s_4_3968 : List (ℕ × ℕ) := [(2179806526,3969),(2179457822,3970),(2179225415,3971),(2178876897,3972),(2178180195,3973),(2177715975,3974),(2177135977,3975),(2177020015,3976),(2176324500,3977),(2175976909,3978),(2175745243,3979),(2175629429,3980),(2175282060,3981),(2174703358,3982),(2174587655,3983),(2173662471,3984)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3968 := recordedBatch d_s_4_3968 3968 0x2d2add002d4641002d5db3002d775d002d8ff5002da777002dbf91002dd82e002df270002e09e8002e23a2002e3ccd002e5732002e6ffe002e881b002ea0dd

private def d_s_4_3984 : List (ℕ × ℕ) := [(2172969099,3985),(2172160724,3986),(2171583682,3987),(2171237604,3988),(2170776337,3989),(2170430516,3990),(2168818141,3991),(2168703063,3992),(2168357902,3993),(2167323078,3994),(2165600565,3995),(2163651691,3996),(2163537161,3997),(2162621353,3998),(2161935007,3999),(2161820658,4000)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_3984 := recordedBatch d_s_4_3984 3984 0x2b8676002b9daf002bb772002bd26f002be9b4002c09bf002c288b002c4437002c5cb3002c73fe002c923c002caab7002cc3d1002cdc58002cf5df002d109b

private theorem s_5_3968 : rowTree 5 3968 = 94577866 := by
  exact glueRows (by decide) s_4_3968.property s_4_3984.property (by decide)

private def d_s_4_4000 : List (ℕ × ℕ) := [(2160792063,4001),(2159878578,4002),(2159536220,4003),(2159079912,4004),(2158509797,4005),(2158053923,4006),(2157484350,4007),(2157028908,4008),(2156459876,4009),(2153959699,4010),(2153619215,4011),(2153278838,4012),(2153051980,4013),(2151918407,4014),(2151691836,4015),(2151578568,4016)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4000 := recordedBatch d_s_4_4000 4000 0x29eefc002a0600002a1d73002a38ff002a5081002a686f002a807a002aa262002abb8d002ad43f002aed71002b060f002b1f42002b37f0002b501d002b6b08

private def d_s_4_4016 : List (ℕ × ℕ) := [(2151352068,4017),(2150559694,4018),(2148976696,4019),(2148524839,4020),(2148186070,4021),(2147283210,4022),(2146493830,4023),(2144804254,4024),(2144466658,4025),(2142780270,4026),(2142555619,4027),(2141769710,4028),(2141208700,4029),(2140872235,4030),(2140535875,4031),(2140087560,4032)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4016 := recordedBatch d_s_4_4016 4016 0x2857aa00286fca0028877700289f1e0028b7ce0028d18c0028e8d50029064600291e1300293bdf002955b400296ff8002987c60029a01d0029bdb90029d7a2

private theorem s_5_4000 : rowTree 5 4000 = 87818295 := by
  exact glueRows (by decide) s_4_4000.property s_4_4016.property (by decide)

private theorem s_6_3968 : rowTree 6 3968 = 182396161 := by
  exact glueRows (by decide) s_5_3968 s_5_4000 (by decide)

private def d_s_4_4032 : List (ℕ × ℕ) := [(2139863473,4033),(2138855662,4034),(2138184315,4035),(2137848799,4036),(2137736984,4037),(2136507790,4038),(2135837915,4039),(2135391566,4040),(2135056926,4041),(2134387961,4042),(2134165066,4043),(2133385300,4044),(2133162614,4045),(2132828673,4046),(2132717382,4047),(2132494836,4048)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4032 := recordedBatch d_s_4_4032 4032 0x26d5170026ec15002702a300271a190027310c00274a850027618f00277a7f002791fe0027a9f70027c3020027de680027f50700280ca8002825d90028407e

private def d_s_4_4048 : List (ℕ × ℕ) := [(2131493952,4049),(2130382959,4050),(2130049888,4051),(2129162205,4052),(2127056921,4053),(2126171731,4054),(2126061134,4055),(2125839974,4056),(2125508321,4057),(2125397794,4058),(2123189645,4059),(2120876023,4060),(2120105935,4061),(2119886013,4062),(2119556215,4063),(2119446305,4064)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4048 := recordedBatch d_s_4_4048 4048 0x254099002556d900256dfc002584c200259dc60025bd1c0025dbfe0025f260002609b500262098002637020026508100266f4b002688f80026a04a0026baf0

private theorem s_5_4032 : rowTree 5 4032 = 81277865 := by
  exact glueRows (by decide) s_4_4032.property s_4_4048.property (by decide)

private def d_s_4_4064 : List (ℕ × ℕ) := [(2118128275,4065),(2117579580,4066),(2117250500,4067),(2117140829,4068),(2116154302,4069),(2115606629,4070),(2114949795,4071),(2114840363,4072),(2113965309,4073),(2113855978,4074),(2113528054,4075),(2112654086,4076),(2112326534,4077),(2111889956,4078),(2111671735,4079),(2111562641,4080)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4064 := recordedBatch d_s_4_4064 4064 0x23c4e80023db040023f198002409090024200a0024393e002450410024665c00247faf002495f80024ae620024c6430024e0100024f64e00250d7500252575

private def d_s_4_4080 : List (ℕ × ℕ) := [(2111017342,4081),(2110690298,4082),(2110254396,4083),(2109709772,4084),(2109600881,4085),(2108621367,4086),(2107751451,4087),(2107316763,4088),(2106665065,4089),(2105688275,4090),(2105037585,4091),(2104712391,4092),(2104062303,4093),(2103520870,4094),(2103196144,4095),(2102871518,4096)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4080 := recordedBatch d_s_4_4080 4080 0x224a29002260f5002277b200228f5b0022a75c0022be0f0022d60a0022ef520023074f00231e9c0023378b002350fc0023670d00237ec9002396130023ad17

private theorem s_5_4064 : rowTree 5 4064 = 74904170 := by
  exact glueRows (by decide) s_4_4064.property s_4_4080.property (by decide)

private theorem s_6_4032 : rowTree 6 4032 = 156182035 := by
  exact glueRows (by decide) s_5_4032 s_5_4064 (by decide)

private theorem s_7_3968 : rowTree 7 3968 = 338578196 := by
  exact glueRows (by decide) s_6_3968 s_6_4032 (by decide)

private theorem s_8_3840 : rowTree 8 3840 = 786440124 := by
  exact glueRows (by decide) s_7_3840 s_7_3968 (by decide)

private theorem s_9_3584 : rowTree 9 3584 = 2054997261 := by
  exact glueRows (by decide) s_8_3584 s_8_3840 (by decide)

private theorem s_10_3072 : rowTree 10 3072 = 6479199755 := by
  exact glueRows (by decide) s_9_3072 s_9_3584 (by decide)

private theorem s_11_2048 : rowTree 11 2048 = 28772630793 := by
  exact glueRows (by decide) s_10_2048 s_10_3072 (by decide)

private theorem s_12_0 : rowTree 12 0 = 365641917518 := by
  exact glueRows (by decide) s_11_0 s_11_2048 (by decide)

private def d_s_4_4096 : List (ℕ × ℕ) := [(2101898242,4097),(2101249892,4098),(2100493988,4099),(2100278116,4100),(2100170196,4101),(2099630764,4102),(2098552731,4103),(2098229537,4104),(2097583448,4105),(2097260552,4106),(2096399983,4107),(2095003064,4108),(2094788318,4109),(2093822508,4110),(2093715251,4111),(2093500769,4112)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4096 := recordedBatch d_s_4_4096 4096 0x20d0560020e6790020fc360021153100212b5a002145d800215e680021750d00218cd60021a37b0021bcdf0021d48d0021ea69002200be0022190a0022311e

private def d_s_4_4112 : List (ℕ × ℕ) := [(2091786497,4113),(2091251363,4114),(2090823453,4115),(2090502635,4116),(2090288811,4117),(2089968157,4118),(2089647602,4119),(2088900021,4120),(2088579793,4121),(2087619699,4122),(2087406464,4123),(2087299863,4124),(2086340944,4125),(2085808592,4126),(2085382906,4127),(2084851043,4128)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4112 := recordedBatch d_s_4_4112 4112 0x1f5d97001f749c001f8b66001fa26f001fbb19001fd0a6001fe6b1001fff430020159600202d930020440400205a7100207076002086dc00209dae0020b4dc

private theorem s_5_4096 : rowTree 5 4096 = 68722974 := by
  exact glueRows (by decide) s_4_4096.property s_4_4112.property (by decide)

private def d_s_4_4128 : List (ℕ × ℕ) := [(2084425747,4129),(2083894372,4130),(2083788130,4131),(2083575677,4132),(2083257079,4133),(2083150902,4134),(2082620176,4135),(2080394079,4136),(2079970600,4137),(2079335704,4138),(2079124158,4139),(2078806921,4140),(2077855787,4141),(2077750160,4142),(2076905524,4143),(2076483464,4144)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4128 := recordedBatch d_s_4_4128 4128 0x1def6b001e05cd001e1d9e001e3301001e4b4b001e6169001e7732001e8e63001ea4c7001ec1ad001ed88f001eee13001f045b001f1a48001f2fcf001f46ea

private def d_s_4_4144 : List (ℕ × ℕ) := [(2076272498,4145),(2076167032,4146),(2075639858,4147),(2074902265,4148),(2074270459,4149),(2073744249,4150),(2072692627,4151),(2072482431,4152),(2072062167,4153),(2071537075,4154),(2069544154,4155),(2069334596,4156),(2069020338,4157),(2068915607,4158),(2068392109,4159),(2067345908,4160)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4144 := recordedBatch d_s_4_4144 4144 0x1c8262001c9aa2001cb127001cc65f001cdc3f001cf1d6001d0d34001d23eb001d3a3d001d4ff3001d6843001d7efc001d960e001dad98001dc449001dd99f

private theorem s_5_4128 : rowTree 5 4128 = 62693709 := by
  exact glueRows (by decide) s_4_4128.property s_4_4144.property (by decide)

private theorem s_6_4096 : rowTree 6 4096 = 131416683 := by
  exact glueRows (by decide) s_5_4096 s_5_4128 (by decide)

private def d_s_4_4160 : List (ℕ × ℕ) := [(2066823204,4161),(2066196308,4162),(2065883003,4163),(2065256677,4164),(2063900940,4165),(2063275816,4166),(2063067525,4167),(2062651069,4168),(2061194799,4169),(2060779099,4170),(2060571312,4171),(2060155864,4172),(2058910524,4173),(2058599424,4174),(2058081133,4175),(2057666689,4176)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4160 := recordedBatch d_s_4_4160 4160 0x1b172f001b2d3d001b438d001b5949001b71d9001b87ed001b9d56001bb361001bccd8001be2d9001bf846001c0f1b001c2847001c3f13001c54ef001c6bce

private def d_s_4_4176 : List (ℕ × ℕ) := [(2057355964,4177),(2056527825,4178),(2055907159,4179),(2055493589,4180),(2054976861,4181),(2054357129,4182),(2053944183,4183),(2052809436,4184),(2052500177,4185),(2052397111,4186),(2051881938,4187),(2051778935,4188),(2051469986,4189),(2050955278,4190),(2050646578,4191),(2050337970,4192)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4176 := recordedBatch d_s_4_4176 4176 0x19b7450019ccbb0019e2320019f847001a0dcc001a22b6001a38c5001a4dae001a633f001a7b46001a912d001aa797001abdd1001ad3c5001aea54001b0189

private theorem s_5_4160 : rowTree 5 4160 = 56734994 := by
  exact glueRows (by decide) s_4_4160.property s_4_4176.property (by decide)

private def d_s_4_4192 : List (ℕ × ℕ) := [(2049926638,4193),(2049618247,4194),(2049412704,4195),(2048693630,4196),(2047256995,4197),(2046846897,4198),(2046027195,4199),(2045105815,4200),(2044696579,4201),(2044492022,4202),(2044185264,4203),(2043163402,4204),(2042959152,4205),(2042040532,4206),(2041734509,4207),(2041632522,4208)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4192 := recordedBatch d_s_4_4192 4192 0x18572300186bdf00188121001898100018ad100018c44b0018d9920018ee9b0019043600191b5400193224001947cb001960930019771400198c280019a18d

private def d_s_4_4208 : List (ℕ × ℕ) := [(2040409468,4209),(2039187880,4210),(2038882711,4211),(2038577634,4212),(2037967753,4213),(2037358237,4214),(2037155146,4215),(2037053615,4216),(2035937450,4217),(2035836041,4218),(2035329147,4219),(2035025132,4220),(2034619920,4221),(2034012405,4222),(2033809980,4223),(2032798462,4224)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4208 := recordedBatch d_s_4_4208 4208 0x16fa68001711490017261800173c0d001751610017667300177c25001790bb0017a8130017bca30017d1810017e7750017fd530018127b001827af00183f65

private theorem s_5_4192 : rowTree 5 4192 = 50953128 := by
  exact glueRows (by decide) s_4_4192.property s_4_4208.property (by decide)

private theorem s_6_4160 : rowTree 6 4160 = 107688122 := by
  exact glueRows (by decide) s_5_4160 s_5_4192 (by decide)

private theorem s_7_4096 : rowTree 7 4096 = 239104805 := by
  exact glueRows (by decide) s_6_4096 s_6_4160 (by decide)

private def d_s_4_4224 : List (ℕ × ℕ) := [(2031888955,4225),(2031585967,4226),(2031384025,4227),(2030778440,4228),(2029568353,4229),(2029266056,4230),(2028963850,4231),(2026248036,4232),(2025846312,4233),(2025545123,4234),(2025344380,4235),(2024040521,4236),(2022237947,4237),(2022037859,4238),(2021937830,4239),(2021737802,4240)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4224 := recordedBatch d_s_4_4224 4224 0x159baa0015b03b0015c4930015d9120015f1bd0016091900161db80016329c001647d2001662f1001677ea00168cdd0016a4370016ba030016ced30016e3c9

private def d_s_4_4240 : List (ℕ × ℕ) := [(2020438581,4241),(2019839503,4242),(2019240781,4243),(2019041286,4244),(2018742117,4245),(2018443036,4246),(2018044401,4247),(2017446742,4248),(2016948963,4249),(2016849437,4250),(2016252486,4251),(2015457100,4252),(2014563041,4253),(2014265198,4254),(2013868211,4255),(2013570573,4256)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4240 := recordedBatch d_s_4_4240 4240 0x14489b00145d2600147203001486a000149c8a0014b2630014c7ba0014dbf40014f1150015067a00151b7800153037001544f40015597100156eed0015846a

private theorem s_5_4224 : rowTree 5 4224 = 45243149 := by
  exact glueRows (by decide) s_4_4224.property s_4_4240.property (by decide)

private def d_s_4_4256 : List (ℕ × ℕ) := [(2012975560,4257),(2012083701,4258),(2011588565,4259),(2011489568,4260),(2008820302,4261),(2008622860,4262),(2008524154,4263),(2008030768,4264),(2006552064,4265),(2005961192,4266),(2005567471,4267),(2005370668,4268),(2004977178,4269),(2004190662,4270),(2003502966,4271),(2002913889,4272)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4256 := recordedBatch d_s_4_4256 4256 0x12f3db001308cb00131df200133378001347ff00135c31001370e3001385f700139d020013b2000013c6050013da3f0013f42b0014084000141d3e0014334e

private def d_s_4_4272 : List (ℕ × ℕ) := [(2002619480,4273),(2002423255,4274),(2002128990,4275),(2001540720,4276),(2001246714,4277),(2001148732,4278),(2000952795,4279),(2000267319,4280),(1999680142,4281),(1999484493,4282),(1998800023,4283),(1998506822,4284),(1997334878,4285),(1997042106,4286),(1996749421,4287),(1996261802,4288)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4272 := recordedBatch d_s_4_4272 4272 0x11ab840011c0110011d44d0011e8780011fe7b001212be001227d200123be6001250bd001265f0001279fa00128dd80012a2210012b7090012cb610012df8a

private theorem s_5_4256 : rowTree 5 4256 = 39683382 := by
  exact glueRows (by decide) s_4_4256.property s_4_4272.property (by decide)

private theorem s_6_4224 : rowTree 6 4224 = 84926531 := by
  exact glueRows (by decide) s_5_4224 s_5_4256 (by decide)

private def d_s_4_4288 : List (ℕ × ℕ) := [(1995676974,4289),(1995092489,4290),(1994119107,4291),(1993243874,4292),(1992952301,4293),(1992660813,4294),(1991883928,4295),(1991495713,4296),(1991301662,4297),(1991010657,4298),(1990041253,4299),(1989847485,4300),(1988298702,4301),(1988105274,4302),(1987428571,4303),(1986945493,4304)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4288 := recordedBatch d_s_4_4288 4288 0x1061ba001075ff00108aab00109e790010b4d90010c8a70010de020010f214001105e900111a2100112f1e001143250011573f00116c8100118205001196ce

private def d_s_4_4304 : List (ℕ × ℕ) := [(1986848906,4305),(1986559200,4306),(1985980043,4307),(1985208357,4308),(1985111939,4309),(1984919130,4310),(1984629987,4311),(1984051953,4312),(1983955647,4313),(1983474257,4314),(1983089312,4315),(1982800702,4316),(1982608342,4317),(1982512176,4318),(1982031485,4319),(1981358910,4320)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4304 := recordedBatch d_s_4_4304 4304 0xf21c7000f3645000f4a6f000f5dfa000f71a8000f857f000f9986000fadce000fc148000fd5b0000fe98f000ffd5f001010f2001025c700103a3500104e25

private theorem s_5_4288 : rowTree 5 4288 = 34289980 := by
  exact glueRows (by decide) s_4_4288.property s_4_4304.property (by decide)

private def d_s_4_4320 : List (ℕ × ℕ) := [(1981070803,4321),(1980782780,4322),(1980206985,4323),(1979343920,4324),(1977715736,4325),(1977333024,4326),(1976854841,4327),(1976568043,4328),(1975421680,4329),(1975135297,4330),(1975039854,4331),(1974562780,4332),(1973990595,4333),(1973895263,4334),(1972466388,4335),(1971990556,4336)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4320 := recordedBatch d_s_4_4320 4320 0xdde61000df24b000e07bf000e1b16000e2f3f000e433e000e5697000e6a3f000e7f51000e930d000ea71f000ebb16000ed11f000ee5eb000efa2e000f0df7

private def d_s_4_4336 : List (ℕ × ℕ) := [(1971324777,4337),(1970754467,4338),(1970184487,4339),(1969425026,4340),(1969140379,4341),(1968855814,4342),(1968760977,4343),(1967907859,4344),(1967718377,4345),(1967434223,4346),(1966014684,4347),(1965352933,4348),(1965163943,4349),(1964880526,4350),(1964597191,4351),(1964502765,4352)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4336 := recordedBatch d_s_4_4336 4336 0xca221000cb545000cc8a9000cdc1c000cef5e000d0358000d1879000d2c00000d3f54000d53a4000d66e0000d7a62000d8dfa000da237000db635000dca38

private theorem s_5_4320 : rowTree 5 4320 = 29012680 := by
  exact glueRows (by decide) s_4_4320.property s_4_4336.property (by decide)

private theorem s_6_4288 : rowTree 6 4288 = 63302660 := by
  exact glueRows (by decide) s_5_4288 s_5_4320 (by decide)

private theorem s_7_4224 : rowTree 7 4224 = 148229191 := by
  exact glueRows (by decide) s_6_4224 s_6_4288 (by decide)

private theorem s_8_4096 : rowTree 8 4096 = 387333996 := by
  exact glueRows (by decide) s_7_4096 s_7_4224 (by decide)

private def d_s_4_4352 : List (ℕ × ℕ) := [(1964219539,4353),(1964030767,4354),(1963747677,4355),(1963087451,4356),(1962804633,4357),(1962616132,4358),(1962239241,4359),(1961768330,4360),(1961203535,4361),(1960921259,4362),(1959417161,4363),(1958947603,4364),(1958572119,4365),(1957540280,4366),(1957446530,4367),(1956977916,4368)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4352 := recordedBatch d_s_4_4352 4352 0xb6878000b7c03000b8f04000ba351000bb6c0000bca4e000bdf4a000bf2a3000c0660000c19f9000c2d7a000c40b0000c5412000c6800000c7b65000c8eb2

private def d_s_4_4368 : List (ℕ × ℕ) := [(1956696856,4369),(1955573420,4370),(1955199228,4371),(1955012186,4372),(1953610509,4373),(1953330415,4374),(1953237068,4375),(1952677174,4376),(1951931148,4377),(1951558348,4378),(1951278842,4379),(1951092549,4380),(1950813176,4381),(1950440804,4382),(1949696485,4383),(1949045672,4384)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4368 := recordedBatch d_s_4_4368 4368 0xa3194000a4505000a58a9000a6bd8000a7ef7000a91fa000aa528000ab86b000acc18000adf97000af28a000b05bf000b1a54000b2d77000b40d0000b5526

private theorem s_5_4352 : rowTree 5 4352 = 23849422 := by
  exact glueRows (by decide) s_4_4352.property s_4_4368.property (by decide)

private def d_s_4_4384 : List (ℕ × ℕ) := [(1948766885,4385),(1948488178,4386),(1948302418,4387),(1948209551,4388),(1947745349,4389),(1947188598,4390),(1947095837,4391),(1946354069,4392),(1945705485,4393),(1945520255,4394),(1945427653,4395),(1945242475,4396),(1944317117,4397),(1943485046,4398),(1943023093,4399),(1942930728,4400)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4384 := recordedBatch d_s_4_4384 4384 0x8ff910009125500092583000938fd00094cad00095f8d0009725b0009853e000998b60009ac340009bf040009d25f0009e5a10009f877000a0b66000a1e7c

private def d_s_4_4400 : List (ℕ × ℕ) := [(1942469038,4401),(1942192129,4402),(1941638549,4403),(1940255976,4404),(1939887623,4405),(1939059339,4406),(1938507542,4407),(1938047951,4408),(1937956059,4409),(1937680436,4410),(1937404890,4411),(1937221237,4412),(1936670486,4413),(1936120048,4414),(1936028338,4415),(1935844946,4416)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4400 := recordedBatch d_s_4_4400 4400 0x7cf5e0007e2140007f4ba000807d100081ae000082d9c0008407400085344000865ee000878f600088c0800089f750008b27b0008c6610008d9800008ec6d

private theorem s_5_4384 : rowTree 5 4384 = 18793947 := by
  exact glueRows (by decide) s_4_4384.property s_4_4400.property (by decide)

private theorem s_6_4352 : rowTree 6 4352 = 42643369 := by
  exact glueRows (by decide) s_5_4352 s_5_4384 (by decide)

private def d_s_4_4416 : List (ℕ × ℕ) := [(1935294977,4417),(1934470609,4418),(1933372544,4419),(1933281095,4420),(1932823979,4421),(1932549813,4422),(1932184379,4423),(1931453927,4424),(1931088907,4425),(1930815233,4426),(1930268118,4427),(1929812426,4428),(1929174817,4429),(1928901686,4430),(1928355654,4431),(1928082754,4432)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4416 := recordedBatch d_s_4_4416 4416 0x6a14b0006b3ed0006c6c30006d96b0006ec5c0006ff2400071205000724be0007378700074a9700075d610007701d000783070007959f0007a9230007bc5b

private def d_s_4_4432 : List (ℕ × ℕ) := [(1927809932,4433),(1927628093,4434),(1927537186,4435),(1926446976,4436),(1926265394,4437),(1925993086,4438),(1925630127,4439),(1925357998,4440),(1925176622,4441),(1925085946,4442),(1924904621,4443),(1924632697,4444),(1923998506,4445),(1923817386,4446),(1923455247,4447),(1923002765,4448)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4432 := recordedBatch d_s_4_4432 4432 0x577b600058a5000059cdb0005af520005c2150005d4a10005e71b0005f98d00060c0d00061ea200063145000643e100065667000669a800067c2100068eaf

private theorem s_5_4416 : rowTree 5 4416 = 13833646 := by
  exact glueRows (by decide) s_4_4416.property s_4_4432.property (by decide)

private def d_s_4_4448 : List (ℕ × ℕ) := [(1921917676,4449),(1920833812,4450),(1920292338,4451),(1920202122,4452),(1919931525,4453),(1919390559,4454),(1918399581,4455),(1917049894,4456),(1916959982,4457),(1916690298,4458),(1915881701,4459),(1915432775,4460),(1915163520,4461),(1914894341,4462),(1914535554,4463),(1914356210,4464)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4448 := recordedBatch d_s_4_4448 4448 0x44e84000460ce0004732e0004858e000497e70004aa620004bd0d0004cf6e0004e1be0004f4df000507b500051a4500052cb900053f0d000551aa000564b7

private def d_s_4_4464 : List (ℕ × ℕ) := [(1914266551,4465),(1913997624,4466),(1913549581,4467),(1913191297,4468),(1912743630,4469),(1912475131,4470),(1912117250,4471),(1911401888,4472),(1911133765,4473),(1910508438,4474),(1910240566,4475),(1910062026,4476),(1908991489,4477),(1908634909,4478),(1908189373,4479),(1908100290,4480)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4464 := recordedBatch d_s_4_4464 4464 0x3296b00033b8600034dcc000360080003728f000384c2000397000003a96b0003bbae0003ce290003e0830003f2cf0004052f0004178c000429f200043c45

private theorem s_5_4448 : rowTree 5 4448 = 8961068 := by
  exact glueRows (by decide) s_4_4448.property s_4_4464.property (by decide)

private theorem s_6_4416 : rowTree 6 4416 = 22794714 := by
  exact glueRows (by decide) s_5_4416 s_5_4448 (by decide)

private theorem s_7_4352 : rowTree 7 4352 = 65438083 := by
  exact glueRows (by decide) s_6_4352 s_6_4416 (by decide)

private def d_s_4_4480 : List (ℕ × ℕ) := [(1907565970,4481),(1907298923,4482),(1907120933,4483),(1905520514,4484),(1905431681,4485),(1904455060,4486),(1904188882,4487),(1903834095,4488),(1903568091,4489),(1903124916,4490),(1902770525,4491),(1902504818,4492),(1901973627,4493),(1901531195,4494),(1900912135,4495),(1900470196,4496)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4480 := recordedBatch d_s_4_4480 4480 0x206a3000218b200022ad500023cf000024f14000261270002734b00028575000297920002a9b00002bbcf0002ce2c0002e0400002f2df000304fd00031727

private def d_s_4_4496 : List (ℕ × ℕ) := [(1900205131,4497),(1899410380,4498),(1898880916,4499),(1898792700,4500),(1898263580,4501),(1898087272,4502),(1896942068,4503),(1896501973,4504),(1895886183,4505),(1895182912,4506),(1894392356,4507),(1894041209,4508),(1893251605,4509),(1892725567,4510),(1892199823,4511),(1891937060,4512)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4496 := recordedBatch d_s_4_4496 4496 0xe7120000f8eb00010ad200011cb400012ea100014086000152780001646c000176600001885b00019a770001ac690001be710001d0620001e26b0001f499

private theorem s_5_4480 : rowTree 5 4480 = 4178837 := by
  exact glueRows (by decide) s_4_4480.property s_4_4496.property (by decide)

private def d_s_4_4512 : List (ℕ × ℕ) := [(1891236715,4513),(1890624339,4514),(1889575473,4515),(1889138789,4516),(1888615034,4517),(1888266026,4518),(1887306918,4519),(1887045512,4520),(1886958393,4521),(1886522917,4522),(1883914280,4523),(1883653813,4524),(1883567007,4525),(0,4525),(0,4525),(0,4525)]
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private def s_4_4512 := recordedBatch d_s_4_4512 4512 0x11ae0000235d00003519000046d50000588f00006a4a00007c1300008ddb00009fa90000b1780000c3550000d531

private theorem s_4_4528 : rowTree 4 4528 = 0 := beyond_cutoff _ _ (by decide)

private theorem s_5_4512 : rowTree 5 4512 = 354151 := by
  exact glueRows (by decide) s_4_4512.property s_4_4528 (by decide)

private theorem s_6_4480 : rowTree 6 4480 = 4532988 := by
  exact glueRows (by decide) s_5_4480 s_5_4512 (by decide)

private theorem s_6_4544 : rowTree 6 4544 = 0 := beyond_cutoff _ _ (by decide)

private theorem s_7_4480 : rowTree 7 4480 = 4532988 := by
  exact glueRows (by decide) s_6_4480 s_6_4544 (by decide)

private theorem s_8_4352 : rowTree 8 4352 = 69971071 := by
  exact glueRows (by decide) s_7_4352 s_7_4480 (by decide)

private theorem s_9_4096 : rowTree 9 4096 = 457305067 := by
  exact glueRows (by decide) s_8_4096 s_8_4352 (by decide)

private theorem s_9_4608 : rowTree 9 4608 = 0 := beyond_cutoff _ _ (by decide)

private theorem s_10_4096 : rowTree 10 4096 = 457305067 := by
  exact glueRows (by decide) s_9_4096 s_9_4608 (by decide)

private theorem s_10_5120 : rowTree 10 5120 = 0 := beyond_cutoff _ _ (by decide)

private theorem s_11_4096 : rowTree 11 4096 = 457305067 := by
  exact glueRows (by decide) s_10_4096 s_10_5120 (by decide)

private theorem s_11_6144 : rowTree 11 6144 = 0 := beyond_cutoff _ _ (by decide)

private theorem s_12_4096 : rowTree 12 4096 = 457305067 := by
  exact glueRows (by decide) s_11_4096 s_11_6144 (by decide)

private theorem finalRows : rowTree 13 0 = 366099222585 := by
  exact glueRows (by decide) s_12_0 s_12_4096 (by decide)

theorem positive_rows_0_13 : rowTree 13 0 = 366099222585 := finalRows




end Astra247824.DenseRank

/- Total contribution of the easy leaves in the concrete LMO decomposition. -/
theorem Astra247824.verifiedEasy : Astra247824.Leaves.EasyNumerics.officialEasy :=
  (Astra247824.Leaves.EasyNumerics.officialEasy_iff_index _ (fun _ hn =>
    Astra247824.DenseRank.denseRank_correct (by omega))).mpr
      (Astra247824.DenseRank.rowTree_total.symm.trans Astra247824.DenseRank.positive_rows_0_13)

theorem OMA.solution : OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1.H1 := Astra247824.verifiedEasy
