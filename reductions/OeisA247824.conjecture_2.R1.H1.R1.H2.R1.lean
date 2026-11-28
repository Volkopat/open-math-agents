import OMAReductions.R_OeisA247824_conjecture_2_R1_H1_R1
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals

/-! Exact Lagarias–Miller–Odlyzko splitting at y=43399. The cutoff prime count is evaluated in the kernel. Ordinary, easy, and hard
leaves are independently evaluable finite sums.
The recursion proof adapts @physbuzz's parent reduction (PR #9315), which credits
Daniel Veljjanoski and @rleshner. For the leaf decomposition see Lagarias,
Miller and Odlyzko, Math. Comp. 44 (1985), §3,
https://www-users.cse.umn.edu/~odlyzko/doc/arch/meissel.lehmer.pdf . -/

-- Credit: @Medrov
namespace OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1
open Finset ArithmeticFunction OMA.R_OeisA247824_conjecture_2_R1_H1_R1

/-- Easy leaves, evaluated by prime ranks. -/
def H1 : Prop :=
  let x := 81744924555066
  let y := 43399
  let edges := ((Icc 1 y).filter Squarefree).sigma (fun d => Nat.primesLE (if d=1 then y else d.minFac-1))
  let leaves := (edges.filter (fun e => ¬ e.1*e.2 ≤ y)).filter (fun e => x/(e.1*e.2) < e.2^2)
  (∑ e ∈ leaves, (1 + (Nat.primeCounting (x/(e.1*e.2)) : ℤ) - (Nat.primeCounting (e.2-1) : ℤ))) = 350834593981

/-- Hard leaves, evaluated by sieved prefix counts. -/
def H2 : Prop :=
  let x := 81744924555066
  let y := 43399
  let edges := ((Icc 1 y).filter Squarefree).sigma (fun d => Nat.primesLE (if d=1 then y else d.minFac-1))
  let leaves := (edges.filter (fun e => ¬ e.1*e.2 ≤ y)).filter (fun e => x/(e.1*e.2) ≥ e.2^2)
  (∑ e ∈ leaves, (-moebius e.1 *
      (((Icc 1 (x/(e.1*e.2))).filter (fun n => ((List.range (e.2-1+1)).filter (fun q : ℕ => decide q.Prime)).reverse.all (fun q => decide (¬q ∣ n)))).card : ℤ))) = 4055588135707

/-- Ordinary leaves of the partial sieve. -/
def H3 : Prop := ∑ d ∈ (Icc 1 43399).filter Squarefree, moebius d * ((81744924555066 / d : ℕ) : ℤ) = -78587373822

section

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
private theorem merge_parts
    (ordinary : ∑ d ∈ (Icc 1 43399).filter Squarefree, moebius d * ((81744924555066 / d : ℕ) : ℤ) = -78587373822)
    (cutoff : (Nat.primesLE 43399).card = 4525) : H1 → H2 → OMA.R_OeisA247824_conjecture_2_R1_H1_R1.H2 := by
  intro easy hard
  let survivors (ps : List ℕ) (x : ℕ) : Finset ℕ :=
    (Icc 1 x).filter (fun n => ∀ p ∈ ps, ¬ p ∣ n)

  let signedSieve (ps : List ℕ) (x : ℕ) : ℤ := (survivors ps x).card

  have mem_survivors {ps : List ℕ} {x n : ℕ} :
      n ∈ survivors ps x ↔ (1 ≤ n ∧ n ≤ x) ∧ ∀ p ∈ ps, ¬ p ∣ n := by simp [survivors]

  have signedSieve_nil (x : ℕ) : signedSieve [] x = x := by
    simp [signedSieve, survivors, Nat.card_Icc]

  have signedSieve_cons {p : ℕ} {ps : List ℕ} (hp : p.Prime)
      (distinct : ∀ q ∈ ps, q.Prime ∧ q ≠ p) (x : ℕ) :
      signedSieve (p :: ps) x = signedSieve ps x - signedSieve ps (x/p) := by
    have split : survivors (p :: ps) x = (survivors ps x).filter (fun n => ¬ p ∣ n) := by
      clear * -
      ext n; simp [survivors, List.mem_cons]; tauto
    have mult : (survivors ps x).filter (fun n => p ∣ n) = (survivors ps (x/p)).image (p * ·) := by
      ext n
      simp only [Finset.mem_filter, mem_survivors, Finset.mem_image]
      constructor
      · rintro ⟨⟨⟨h1, hx⟩, hq⟩, ⟨m, rfl⟩⟩
        refine ⟨m, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
        · rcases Nat.eq_zero_or_pos m with rfl | hm
          · simp at h1
          · exact hm
        · exact (Nat.le_div_iff_mul_le hp.pos).2 (by rwa [mul_comm])
        · intro q hm hdvd
          exact hq q hm (dvd_mul_of_dvd_right hdvd p)
      · rintro ⟨m, ⟨⟨h1, hm⟩, hq⟩, rfl⟩
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, dvd_mul_right p m⟩
        · exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero hp.ne_zero (by omega))
        · rw [mul_comm]; exact (Nat.le_div_iff_mul_le hp.pos).1 hm
        · intro q hmem hdvd
          obtain ⟨prime, neq⟩ := distinct q hmem
          rcases prime.dvd_mul.mp hdvd with h | h
          · exact neq ((Nat.prime_dvd_prime_iff_eq prime hp).mp h)
          · exact hq q hmem h
    have card := Finset.card_filter_add_card_filter_not (s := survivors ps x) (fun n => p ∣ n)
    rw [mult, Finset.card_image_of_injective _ (mul_right_injective₀ hp.ne_zero)] at card
    dsimp only [signedSieve]
    rw [split]
    omega

  let descendingPrimes (y : ℕ) : List ℕ :=
    ((List.range (y+1)).filter (fun p => decide p.Prime)).reverse

  have mem_descending {p y : ℕ} : p ∈ descendingPrimes y ↔ p ∈ Nat.primesLE y := by
    simp [descendingPrimes, Nat.mem_primesLE]

  have descending_sorted (y : ℕ) : (descendingPrimes y).Pairwise (· > ·) :=
    List.pairwise_reverse.mpr (List.pairwise_lt_range.filter _)

  have descending_succ (b : ℕ) : descendingPrimes (b+1) =
      if (b+1).Prime then (b+1) :: descendingPrimes b else descendingPrimes b := by
    by_cases hp : (b+1).Prime <;>
      simp [descendingPrimes, List.range_succ (n := b+1), List.filter_append, hp]


  have signedSieve_telescope (z b : ℕ) :
      signedSieve (descendingPrimes b) z = z -
        ∑ p ∈ Nat.primesLE b, signedSieve (descendingPrimes (p-1)) (z/p) := by
    induction b with
    | zero =>
      rw [show descendingPrimes 0 = [] by rfl, Nat.primesLE_zero]
      simp [signedSieve_nil]
    | succ b ih =>
      rw [descending_succ, Nat.primesLE_succ]
      by_cases hp : (b+1).Prime
      · have fresh : b+1 ∉ Nat.primesLE b := fun h => by have := Nat.le_of_mem_primesLE h; omega
        simp only [if_pos hp, Finset.sum_insert fresh, Nat.add_sub_cancel]
        rw [signedSieve_cons hp (fun q h => ⟨Nat.prime_of_mem_primesLE (mem_descending.mp h),
          by have := Nat.le_of_mem_primesLE (mem_descending.mp h); omega⟩), ih]
        ring
      · simpa only [if_neg hp] using ih


  let remainingBound (y d : ℕ) := if d = 1 then y else d.minFac-1

  let denominators (y : ℕ) := (Icc 1 y).filter Squarefree

  let Edge := Sigma (fun _ : ℕ => ℕ)

  let edges (y : ℕ) : Finset Edge :=
    (denominators y).sigma (fun d => Nat.primesLE (remainingBound y d))

  let internal (y : ℕ) := (edges y).filter (fun e => e.1*e.2 ≤ y)

  let special (y : ℕ) := (edges y).filter (fun e => ¬e.1*e.2 ≤ y)

  let nodeValue (x y d : ℕ) : ℤ :=
    moebius d * signedSieve (descendingPrimes (remainingBound y d)) (x/d)

  let edgeValue (x : ℕ) (e : Edge) : ℤ :=
    -moebius e.1 * signedSieve (descendingPrimes (e.2-1)) (x/(e.1*e.2))

  have node_step (x y d : ℕ) : nodeValue x y d =
      moebius d * (x/d : ℕ) + ∑ p ∈ Nat.primesLE (remainingBound y d), edgeValue x ⟨d,p⟩ := by
    dsimp only [nodeValue]
    rw [signedSieve_telescope, mul_sub, Finset.mul_sum]
    simp only [edgeValue, Nat.div_div_eq_div_mul, neg_mul, Finset.sum_neg_distrib]
    ring

  have edge_facts {d p y : ℕ} (hm : (⟨d,p⟩ : Edge) ∈ edges y) :
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

  have child_facts {d p y : ℕ} (hm : (⟨d,p⟩ : Edge) ∈ edges y) :
      d*p ≠ 1 ∧ Squarefree (d*p) ∧ (d*p).minFac = p ∧ moebius (d*p) = -moebius d := by
    obtain ⟨hd, sf, prime, _, before⟩ := edge_facts hm
    have nd : ¬p ∣ d := by
      rintro dv
      rcases before with rfl | lt
      · exact prime.not_dvd_one dv
      · exact lt.not_ge (Nat.minFac_le_of_dvd prime.two_le dv)
    have cop : d.Coprime p := (prime.coprime_iff_not_dvd.mpr nd).symm
    have one : d*p ≠ 1 := fun h => prime.not_dvd_one (h ▸ dvd_mul_left p d)
    have upper : (d*p).minFac ≤ p := Nat.minFac_le_of_dvd prime.two_le (dvd_mul_left p d)
    have lower : p ≤ (d*p).minFac := by
      apply Or.resolve_left (Nat.le_minFac.mpr ?_) one
      intro q hq hdiv
      rcases hq.dvd_mul.mp hdiv with dq | pq
      · rcases before with rfl | lt
        · exact (hq.not_dvd_one dq).elim
        · exact lt.le.trans (Nat.minFac_le_of_dvd hq.two_le dq)
      · rw [(Nat.prime_dvd_prime_iff_eq hq prime).mp pq]
    refine ⟨one, (Nat.squarefree_mul cop).mpr ⟨sf, prime.squarefree⟩, le_antisymm upper lower, ?_⟩
    rw [isMultiplicative_moebius.map_mul_of_coprime cop, moebius_apply_prime prime, mul_neg_one]

  have internal_target {y : ℕ} {e : Edge} (he : e ∈ internal y) :
      e.1*e.2 ∈ (denominators y).erase 1 := by
    obtain ⟨edge, limit⟩ := Finset.mem_filter.mp he
    obtain ⟨one, sf, _, _⟩ := child_facts edge
    refine Finset.mem_erase.mpr ⟨one, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_,limit⟩, sf⟩⟩
    obtain ⟨pos, _, pp, _, _⟩ := edge_facts edge
    exact Nat.mul_pos pos pp.pos

  have internal_parent {y n : ℕ} (hn : n ∈ (denominators y).erase 1) :
      ∃ e ∈ internal y, e.1*e.2 = n := by
    obtain ⟨hne, hnode⟩ := Finset.mem_erase.mp hn
    obtain ⟨ni, sf⟩ := Finset.mem_filter.mp hnode
    obtain ⟨np, ny⟩ := Finset.mem_Icc.mp ni
    let p := n.minFac
    let d := n / p
    have prime : p.Prime := Nat.minFac_prime hne
    have prod : d*p = n := Nat.div_mul_cancel (Nat.minFac_dvd n)
    have ds : Squarefree (d*p) := prod.symm ▸ sf
    obtain ⟨cop, dsq, _⟩ := Nat.squarefree_mul_iff.mp ds
    have dpos : 0 < d := Nat.pos_of_ne_zero (by intro z; simp [z] at prod; omega)
    have dBound : d ≤ n := Nat.le_of_dvd np (prod ▸ dvd_mul_right d p)
    have pBound : p ≤ n := Nat.minFac_le np
    have pp : p ≤ remainingBound y d := by
      by_cases one : d = 1
      · simpa [remainingBound, one] using pBound.trans ny
      · dsimp only [remainingBound]
        rw [if_neg one]
        have dq := Nat.minFac_prime one
        have dv : d.minFac ∣ n := prod ▸ dvd_mul_of_dvd_left (Nat.minFac_dvd d) p
        have low : p ≤ d.minFac := Nat.minFac_le_of_dvd dq.two_le dv
        have neq : p ≠ d.minFac := fun h => (prime.coprime_iff_not_dvd.mp cop.symm) (h ▸ Nat.minFac_dvd d)
        omega
    refine ⟨⟨d,p⟩, Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr ⟨?_, Nat.mem_primesLE.mpr ⟨pp,prime⟩⟩, prod ▸ ny⟩, prod⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨dpos, dBound.trans ny⟩, dsq⟩

  have sum_internal (x y : ℕ) :
      ∑ e ∈ internal y, edgeValue x e = ∑ n ∈ (denominators y).erase 1, nodeValue x y n := by
    apply Finset.sum_bij (fun e _ => e.1*e.2) (fun _ he => internal_target he)
    · intro ⟨d,p⟩ hm ⟨d',p'⟩ hm' eq
      change d*p = d'*p' at eq
      obtain ⟨_, _, hp, _⟩ := child_facts (Finset.mem_filter.mp hm).1
      obtain ⟨_, _, hp', _⟩ := child_facts (Finset.mem_filter.mp hm').1
      have pe : p = p' := hp.symm.trans ((congrArg Nat.minFac eq).trans hp')
      subst p'
      have prime := (edge_facts (Finset.mem_filter.mp hm).1).2.2.1
      have de : d = d' := Nat.eq_of_mul_eq_mul_right prime.pos eq
      subst d'
      rfl
    · intro n hn
      obtain ⟨e, he, val⟩ := internal_parent hn
      exact ⟨e, he, val⟩
    · intro ⟨d,p⟩ he
      obtain ⟨one, _, minFac, mu⟩ := child_facts (Finset.mem_filter.mp he).1
      simp only [edgeValue, nodeValue, remainingBound, if_neg one, minFac, mu]


  have flat_decomposition (x y : ℕ) (hy : 0 < y) :
      signedSieve (descendingPrimes y) x =
        (∑ d ∈ denominators y, moebius d * (x/d : ℕ)) + ∑ e ∈ special y, edgeValue x e := by
    have roots := Finset.sum_congr (s₁ := denominators y) rfl (fun d _ => node_step x y d)
    rw [Finset.sum_add_distrib] at roots
    have unroll := Finset.sum_sigma (denominators y)
      (fun d => Nat.primesLE (remainingBound y d)) (edgeValue x)
    change ∑ e ∈ edges y, edgeValue x e = _ at unroll
    rw [← unroll] at roots
    have split := Finset.sum_filter_add_sum_filter_not (edges y) (fun e => e.1*e.2 ≤ y) (edgeValue x)
    change (∑ e ∈ internal y, edgeValue x e) + (∑ e ∈ special y, edgeValue x e) = _ at split
    rw [sum_internal x y] at split
    have one : 1 ∈ denominators y := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl,hy⟩, squarefree_one⟩
    have erased := Finset.add_sum_erase (denominators y) (nodeValue x y) one
    have root : nodeValue x y 1 = signedSieve (descendingPrimes y) x := by
      simp [nodeValue, remainingBound]
    rw [← root]
    rw [← split, ← erased] at roots
    omega

  let ordinaryFlat (x y : ℕ) : ℤ := ∑ d ∈ denominators y, moebius d * (x/d : ℕ)

  let easyFlat (x y : ℕ) : ℤ :=
    ∑ e ∈ (special y).filter (fun e => x/(e.1*e.2) < e.2^2), edgeValue x e

  let hardFlat (x y : ℕ) : ℤ :=
    ∑ e ∈ (special y).filter (fun e => ¬x/(e.1*e.2) < e.2^2), edgeValue x e

  have flat_three_sums (x y : ℕ) (hy : 0 < y) :
      signedSieve (descendingPrimes y) x = ordinaryFlat x y + easyFlat x y + hardFlat x y := by
    have part := Finset.sum_filter_add_sum_filter_not (special y)
      (fun e => x/(e.1*e.2) < e.2^2) (edgeValue x)
    change easyFlat x y + hardFlat x y = _ at part
    rw [flat_decomposition x y hy, ← part, ← add_assoc]


  have easy_facts {x y : ℕ} {e : Edge} (hx : y^3 ≤ x) (he : e ∈ special y)
      (small : x/(e.1*e.2) < e.2^2) :
      e.1.Prime ∧ e.2 ≤ x/(e.1*e.2) := by
    rcases e with ⟨d,p⟩
    obtain ⟨edge, cross⟩ := Finset.mem_filter.mp he
    obtain ⟨pos, _, prime, py, before⟩ := edge_facts edge
    have dy : d ≤ y := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_sigma.mp edge).1).1).2
    have dp : 0 < d*p := Nat.mul_pos pos prime.pos
    change ¬d*p ≤ y at cross
    change x/(d*p) < p^2 at small
    have dd : d ≠ 1 := by intro h; subst d; simp only [one_mul] at cross; exact cross py
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


  have signedSieve_below_square {p t : ℕ} (hp : p.Prime) (lower : p ≤ t) (upper : t < p^2) :
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


  have easyFlat_primeCounting (x y : ℕ) (hx : y^3 ≤ x) : easyFlat x y =
      ((special y).filter (fun e : Edge => x/(e.1*e.2) < e.2^2)).sum (fun e : Edge =>
        1 + (Nat.primeCounting (x/(e.1*e.2)) : ℤ) - (Nat.primeCounting (e.2-1) : ℤ)) := by
    apply Finset.sum_congr rfl
    intro e mem
    obtain ⟨hs, small⟩ := Finset.mem_filter.mp mem
    obtain ⟨prime, lower⟩ := easy_facts hx hs small
    have primeP := (edge_facts (Finset.mem_filter.mp hs).1).2.2.1
    dsimp only [edgeValue]
    rw [moebius_apply_prime prime, neg_neg, one_mul, signedSieve_below_square primeP lower small]


  have base : ordinaryFlat 81744924555066 43399 = -78587373822 := ordinary
  have low : easyFlat 81744924555066 43399 = 350834593981 := by
    rw [easyFlat_primeCounting _ _ (by decide)]
    exact easy
  have high : hardFlat 81744924555066 43399 = 4055588135707 := by
    simpa only [H2, hardFlat, special, edges, remainingBound, denominators, edgeValue,
      signedSieve, survivors, descendingPrimes, List.all_eq_true, decide_eq_true_eq, not_lt] using hard
  have flat := flat_three_sums 81744924555066 43399 (by decide)
  rw [base, low, high] at flat
  unfold OMA.R_OeisA247824_conjecture_2_R1_H1_R1.H2
  rw [legendre_range, cutoff]
  simp only [signedSieve, survivors, mem_descending] at flat
  have finish (v : ℕ) (h : (v : ℤ) = -78587373822 + 350834593981 + 4055588135707) :
      v + 4525 = 4327835360391 := by clear * - h; omega
  exact finish _ flat

private theorem cutoff : (Nat.primesLE 43399).card = 4525 := by
  let small : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199]
  have small_eq : (List.range 209).filter (fun p => decide p.Prime) = small := by
    clear * -
    decide +kernel +revert
  have small_card : (Nat.primesLE 208).card = 46 := by
    rw [Nat.primesLE_card_eq_primeCounting]
    change (List.range 209).countP (fun p => decide p.Prime) = 46
    rw [List.countP_eq_length_filter, small_eq]
    rfl
  let sieve (p : ℕ) (f : ℕ → ℕ) (t : ℕ) := if t < p then (if t=0 then 0 else 1) else f t - f (t/p)
  have small_sieved : small.reverse.foldr sieve id 43399 = 4480 := by
    clear * -
    decide +kernel +revert
  rw [Nat.primesLE_card_eq_primeCounting]
  apply rank_of_parts (y:=208) (z:=208) (a:=4526) (b:=0)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [small_eq, small_card]
    change small.reverse.foldr sieve id 43399 + 46 = 4526
    rw [small_sieved]
  · exact empty_correction _ _
  · decide

end

theorem main : H1 → H2 → H3 → OMA.R_OeisA247824_conjecture_2_R1_H1_R1.H2 := fun e h o => merge_parts o cutoff e h

end OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1
