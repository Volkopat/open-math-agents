import OMAStatements.S_oeis_a068873

-- Credit: @jacklarmer
-- The 27 proposed values are due to Jean-François Alcover (OEIS A068873).

open Finset

namespace A068873Cert

/-- Each removed prime below the cutoff must be replaced by a prime above it. -/
lemma window_bound (B S : Finset ℕ) (c : ℕ)
    (hc : B.card = S.card) (hb : ∀ b ∈ B \ S, b ≤ c) (hs : ∀ s ∈ S \ B, c ≤ s) :
    (∑ b ∈ B, b) ≤ ∑ s ∈ S, s ∧
    (∀ b ∈ B \ S, (∑ x ∈ B, x) + (c - b) ≤ ∑ x ∈ S, x) ∧
    (∀ s ∈ S \ B, (∑ x ∈ B, x) + (s - c) ≤ ∑ x ∈ S, x) := by
  have split (F G : Finset ℕ) :
      (∑ x ∈ F \ G, x) + (∑ x ∈ F ∩ G, x) = ∑ x ∈ F, x := by
    rw [← sum_union (disjoint_sdiff_inter F G), sdiff_union_inter]
  have cardEq : (S \ B).card = (B \ S).card := by
    rw [card_sdiff, card_sdiff, hc, inter_comm B S]
  have removed : (∑ b ∈ B \ S, b) + (∑ b ∈ B \ S, (c - b)) = (B \ S).card * c := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _b ∈ B \ S, c := by
        apply sum_congr rfl
        intro b bm
        have := hb b bm
        omega
      _ = _ := by simp
  have added : (∑ s ∈ S \ B, s) = (S \ B).card * c + (∑ s ∈ S \ B, (s - c)) := by
    calc
      _ = ∑ s ∈ S \ B, (c + (s - c)) := by
        apply sum_congr rfl
        intro s sm
        have := hs s sm
        omega
      _ = _ := by simp [sum_add_distrib]
  rw [cardEq] at added
  have bsplit := split B S
  have ssplit := split S B
  rw [inter_comm S B] at ssplit
  refine ⟨by omega, ?_, ?_⟩
  · intro b bm
    have bound : c - b ≤ ∑ x ∈ B \ S, (c - x) :=
      single_le_sum (fun x _ => Nat.zero_le (c - x)) bm
    omega
  · intro s sm
    have bound : s - c ≤ ∑ x ∈ S \ B, (x - c) :=
      single_le_sum (fun x _ => Nat.zero_le (x - c)) sm
    omega

end A068873Cert

open Finset

namespace A068873Cert

/-- A subset of size `k` and sum `s` sets bit `k * stride + s`. -/
def masks : List ℕ → ℕ → ℕ
  | [], _ => 1
  | p :: xs, stride =>
      let m := masks xs stride
      m ||| (m <<< (stride + p))

lemma reaches_mask (xs : List ℕ) (stride : ℕ) (S : Finset ℕ)
    (hS : S ⊆ xs.toFinset) :
    (masks xs stride).testBit (S.card * stride + ∑ s ∈ S, s) = true := by
  induction xs generalizing S with
  | nil =>
    have h : S = ∅ := by simpa using hS
    subst S
    simp [masks]
  | cons p xs ih =>
    rw [List.toFinset_cons] at hS
    simp only [masks, Nat.testBit_or, Bool.or_eq_true]
    by_cases hp : p ∈ S
    · right
      have ht := ih (S.erase p) (Finset.subset_insert_iff.mp hS)
      have hcard := Finset.card_erase_add_one hp
      have hsum := Finset.add_sum_erase S (fun x => x) hp
      have hidx : S.card * stride + (∑ s ∈ S, s) =
          (S.erase p).card * stride + (∑ s ∈ S.erase p, s) + (stride + p) := by
        rw [← hcard, Nat.add_mul, Nat.one_mul]
        change p + (∑ x ∈ S.erase p, x) = ∑ x ∈ S, x at hsum
        omega
      rw [hidx, Nat.testBit_shiftLeft]
      simp [ht]
    · left
      exact ih S ((Finset.subset_insert_iff_of_notMem hp).mp hS)

end A068873Cert

namespace A068873Cert

def primePool : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37,
   41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
   97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
   157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
   227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281,
   283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359,
   367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433,
   439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
   509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593,
   599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
   661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743,
   751, 757]

def primeTest (q : ℕ) : Bool :=
  decide (2 ≤ q) && (List.range 26).all (fun k => decide (q % (k + 2) ≠ 0 ∨ q = k + 2))

lemma primeTest_correct {q : ℕ} (hq : q ≤ 760) : primeTest q = true ↔ q.Prime := by
  simp only [primeTest, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨h2, h⟩
    by_contra hn
    have hfac := Nat.minFac_prime (by omega : q ≠ 1)
    have hs := Nat.minFac_sq_le_self (by omega : 0 < q) hn
    have hl : q.minFac < 28 := by
      by_contra! hc
      have hh := Nat.pow_le_pow_left hc 2
      omega
    have hmin := hfac.two_le
    have hm := h (q.minFac - 2) (by omega)
    rw [Nat.sub_add_cancel hmin] at hm
    rcases hm with hr | he
    · exact hr (Nat.mod_eq_zero_of_dvd q.minFac_dvd)
    · exact hn (he.symm ▸ hfac)
  · intro hp
    refine ⟨hp.two_le, fun k _ => ?_⟩
    by_cases hz : q % (k + 2) = 0
    · right
      have hor := hp.eq_one_or_self_of_dvd (k + 2) (Nat.dvd_of_mod_eq_zero hz)
      omega
    · exact Or.inl hz

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma primePool_eq : primePool = (List.range 761).filter (fun q => decide q.Prime) := by
  have tab : primePool = (List.range 761).filter primeTest := by decide +kernel
  rw [tab]
  apply List.filter_congr
  intro q h
  have bound := List.mem_range.mp h
  apply Bool.eq_iff_iff.mpr
  simpa using primeTest_correct (q := q) (by omega)

lemma mem_primePool {q : ℕ} (hbound : q ≤ 760) (hprime : q.Prime) : q ∈ primePool.toFinset := by
  rw [primePool_eq]
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨by omega, hprime⟩

lemma prime_of_mem_primePool {q : ℕ} (h : q ∈ primePool) : q.Prime := by
  rw [primePool_eq] at h
  exact of_decide_eq_true (List.mem_filter.mp h).2

end A068873Cert

namespace A068873Cert

open OMA.S_oeis_a068873 Finset

def primeCutoffs : List ℕ :=
  [229,233,239,241,251,257,263,269,271,277,281,283,293,307,
   311,313,317,331,337,347,349,353,359,367,373,379,383]

def prefixSums : List ℕ :=
  [5117,5350,5589,5830,6081,6338,6601,6870,7141,7418,7699,7982,8275,8582,
   8893,9206,9523,9854,10191,10538,10887,11240,11599,11966,12339,12718,13101]

def cutoff (i : Fin conjecturedValues.length) : ℕ := primeCutoffs[i.val]!

def baseSum (i : Fin conjecturedValues.length) : ℕ := prefixSums[i.val]!

def smallest (i : Fin conjecturedValues.length) : Finset ℕ :=
  (range (cutoff i + 1)).filter Nat.Prime

def smallSum (i : Fin conjecturedValues.length) : ℕ := (smallest i).sum id

def primesThrough (c : ℕ) : List ℕ := primePool.filter (fun p => decide (p ≤ c))

def checkCutoff (n : ℕ) : Bool :=
  let c := primeCutoffs[n]!
  let s := prefixSums[n]!
  let ps := primesThrough c
  decide (ps.length = 50 + n ∧ ps.sum = s ∧ c ≤ 760 ∧ conjecturedValues[n]! + c ≤ 760 + s)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma allCutoffs : (List.range 27).all checkCutoff = true := by decide +kernel

lemma cutoff_row (i : Fin conjecturedValues.length) :
    (primesThrough (cutoff i)).length = 50 + i.val ∧
    (primesThrough (cutoff i)).sum = baseSum i ∧ cutoff i ≤ 760 ∧
    conjecturedValues[i] + cutoff i ≤ 760 + baseSum i := by
  have h := List.all_eq_true.mp allCutoffs i.val (List.mem_range.mpr i.isLt)
  change decide ((primesThrough (cutoff i)).length = 50 + i.val ∧
    (primesThrough (cutoff i)).sum = baseSum i ∧ cutoff i ≤ 760 ∧
    conjecturedValues[i.val]! + cutoff i ≤ 760 + baseSum i) = true at h
  have he : conjecturedValues[i.val]! = conjecturedValues[i] := by
    rw [getElem!_pos conjecturedValues i.val i.isLt, Fin.getElem_fin]
  have row := of_decide_eq_true h
  rw [he] at row
  exact row

lemma cutoff_finset (i : Fin conjecturedValues.length) :
    smallest i = (primesThrough (cutoff i)).toFinset := by
  ext p
  simp only [smallest, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
    List.mem_toFinset, primesThrough, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hp⟩
    exact ⟨List.mem_toFinset.mp (mem_primePool (h.trans (cutoff_row i).2.2.1) hp), h⟩
  · rintro ⟨h, hc⟩
    exact ⟨hc, prime_of_mem_primePool h⟩

lemma primesThrough_nodup (c : ℕ) : (primesThrough c).Nodup := by
  exact (show primePool.Nodup by rw [primePool_eq]; exact List.nodup_range.filter _).filter _

lemma smallSum_eq (i : Fin conjecturedValues.length) : smallSum i = baseSum i := by
  rw [smallSum, cutoff_finset i, List.sum_toFinset id (primesThrough_nodup _)]
  simpa using (cutoff_row i).2.1

theorem cutoff_certificate : ∀ i : Fin conjecturedValues.length,
    (smallest i).card = 50 + i.val ∧ cutoff i ≤ 760 ∧
    conjecturedValues[i] + cutoff i ≤ 760 + smallSum i := by
  intro i
  rw [cutoff_finset i, List.toFinset_card_of_nodup (primesThrough_nodup _), smallSum_eq i]
  exact ⟨(cutoff_row i).1, (cutoff_row i).2.2⟩

end A068873Cert

namespace A068873Cert

open OMA.S_oeis_a068873

def trialDivisors : List ℕ :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113]

/- Flags enumerate the possible prime values between the least sum and the proposed answer. -/
def flags : List ℕ := [0x4, 0x200808820800000220a002280002282000008288200288202082080000002, 0x0, 0x820008220808000220000208000000800200220000208000a00a088282200, 0x500, 0x8828200a20000808000000200808800028000020800000808020820a08020, 0x0, 0xa08008200000200800800220020208008820208220a00a0000000822020002002, 0x0, 0x220808800008220000800220028208800a00a08808208020200a08800028200008000, 0x0, 0x820000208a00a00800020020220800200000208200808a08008020800200000828000800, 0x11000, 0x20000228008028200a00220000220000808208820020820208808808200020800a20008028000, 0x0, 0x20008200208228000028a00a08020820008200000828800220200008028800008000a00208008, 0x10400, 0x8008808220200a08000020220a00200a08000028000000a00000000820000808028200020800220020028, 0x100004, 0x200020a08200820000000200808020000800208820028000220000220820020220008208808000020200000, 0x4, 0x20808000000a00000808000820a08008800008820008008008200800200028000020220800800808200220808, 0x0, 0x8200000800808808200a00a00200020208000000028808200000208a08800000a00000828800000220000208028, 0x110, 0x800000020008208800000a280002208202080080002282202088000000008008008280080202008000208002200008, 0x100104]

def gapFlag (i : Fin conjecturedValues.length) := flags[i.val]!

def marks : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (off, value) :: rest => (value <<< off) ||| marks rest

def gapRows : List (ℕ × ℕ) := (List.finRange conjecturedValues.length).map
  (fun i => ((50 + i.val) * 65536 + baseSum i, gapFlag i))

/- The 134 primes up to 760 sum to 46191, so a stride of 65536 separates cardinalities. -/
set_option maxRecDepth 50000 in
theorem mask_disjoint : masks primePool 65536 &&& marks gapRows = 0 := by decide +kernel

def gapTest (base target flag : ℕ) : Bool := (List.range (target - base)).all
  (fun j => flag.testBit j || trialDivisors.any (fun d => (base + j) % d == 0))

set_option maxRecDepth 50000 in
theorem gap_rows_checked : (List.finRange conjecturedValues.length).all
    (fun i => gapTest (baseSum i) conjecturedValues[i] (gapFlag i)) = true := by decide +kernel

lemma marks_mem {rows : List (ℕ × ℕ)} {off f j : ℕ}
    (hmem : (off, f) ∈ rows) (hbit : f.testBit j = true) :
    (marks rows).testBit (off+j) = true := by
  induction rows with
  | nil => simp at hmem
  | cons row rows ih =>
    rcases row with ⟨a, b⟩
    rw [List.mem_cons] at hmem
    rw [marks, Nat.testBit_or, Bool.or_eq_true]
    rcases hmem with h | h
    · cases h
      left
      rw [Nat.testBit_shiftLeft]
      simpa using hbit
    · exact Or.inr (ih h)

lemma gap_bit (i : Fin conjecturedValues.length) {j : ℕ}
    (hj : j < conjecturedValues[i] - baseSum i) (hp : (baseSum i + j).Prime) :
    (gapFlag i).testBit j = true := by
  have row := List.all_eq_true.mp gap_rows_checked i (List.mem_finRange i)
  have check := List.all_eq_true.mp row j (List.mem_range.mpr hj)
  simp only [Bool.or_eq_true] at check
  rcases check with h | h
  · exact h
  · obtain ⟨d, hd, hz⟩ := List.any_eq_true.mp h
    have ds : trialDivisors.all (fun d => decide (1 < d ∧ d ≤ 113)) = true := by decide +kernel
    have hd' : 1 < d ∧ d ≤ 113 := of_decide_eq_true (List.all_eq_true.mp ds d hd)
    have bs : (List.finRange conjecturedValues.length).all (fun k => decide (113 < baseSum k)) = true := by decide +kernel
    have hb : 113 < baseSum i := of_decide_eq_true (List.all_eq_true.mp bs i (List.mem_finRange i))
    have dvd : d ∣ baseSum i + j := Nat.dvd_of_mod_eq_zero (eq_of_beq hz)
    rcases hp.eq_one_or_self_of_dvd d dvd with h | h <;> omega

theorem gap_certificate (i : Fin conjecturedValues.length) (j : Fin (conjecturedValues[i] - smallSum i))
    (hp : (smallSum i + j.val).Prime) :
    (masks primePool 65536).testBit ((50 + i.val) * 65536 + (smallSum i + j.val)) = false := by
  have e := smallSum_eq i
  rcases j with ⟨j, hj⟩
  change (smallSum i + j).Prime at hp
  change (masks primePool 65536).testBit ((50 + i.val) * 65536 + (smallSum i + j)) = false
  rw [e] at hp hj ⊢
  have hm : ((50 + i.val) * 65536 + baseSum i, gapFlag i) ∈ gapRows :=
    List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  have bit := marks_mem hm (gap_bit i hj hp)
  have both := congrArg (fun a => a.testBit ((50 + i.val) * 65536 + (baseSum i + j))) mask_disjoint
  change (masks primePool 65536 &&& marks gapRows).testBit _ = _ at both
  rw [Nat.testBit_and, ← Nat.add_assoc, bit] at both
  simpa [Nat.add_assoc] using both

end A068873Cert

namespace A068873Cert
open OMA.S_oeis_a068873

/-- Each row gives a prime cutoff and the primes to remove and add for an upper witness. -/
def upperTable : List (ℕ × List ℕ × List ℕ) :=
  [(229, [211], [241]),
    (239, [227], [263]),
    (239, [239], [241]),
    (251, [], []),
    (251, [251], [271]),
    (263, [], []),
    (263, [263], [269]),
    (271, [269], [281]),
    (271, [271], [281]),
    (281, [281], [283]),
    (281, [], []),
    (293, [], []),
    (293, [293], [311]),
    (311, [311], [313]),
    (311, [], []),
    (317, [], []),
    (317, [307], [331]),
    (337, [331], [353]),
    (337, [317], [349]),
    (349, [349], [353]),
    (349, [349], [353]),
    (359, [], []),
    (359, [349], [367]),
    (373, [373], [379]),
    (373, [349], [383]),
    (383, [], []),
    (383, [383], [409])]

def upperPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409]

def upperList (i : Fin conjecturedValues.length) : List ℕ :=
  let row := upperTable[i.val]!
  upperPrimes.filter (fun p =>
    (p ≤ row.1 && (i.val % 2 == 0 || p != 2) && !row.2.1.contains p) || row.2.2.contains p)

set_option maxRecDepth 10000 in
theorem upperPrimes_nodup : upperPrimes.Nodup := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem upperPrimes_prime (p : ℕ) (hp : p ∈ upperPrimes) : p.Prime := by
  simp only [upperPrimes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem targets_prime (i : Fin conjecturedValues.length) : conjecturedValues[i].Prime := by
  fin_cases i
  · change Nat.Prime 5147
    norm_num1
  · change Nat.Prime 5623
    norm_num1
  · change Nat.Prime 5591
    norm_num1
  · change Nat.Prime 6079
    norm_num1
  · change Nat.Prime 6101
    norm_num1
  · change Nat.Prime 6599
    norm_num1
  · change Nat.Prime 6607
    norm_num1
  · change Nat.Prime 7151
    norm_num1
  · change Nat.Prime 7151
    norm_num1
  · change Nat.Prime 7699
    norm_num1
  · change Nat.Prime 7699
    norm_num1
  · change Nat.Prime 8273
    norm_num1
  · change Nat.Prime 8293
    norm_num1
  · change Nat.Prime 8893
    norm_num1
  · change Nat.Prime 8893
    norm_num1
  · change Nat.Prime 9521
    norm_num1
  · change Nat.Prime 9547
    norm_num1
  · change Nat.Prime 10211
    norm_num1
  · change Nat.Prime 10223
    norm_num1
  · change Nat.Prime 10889
    norm_num1
  · change Nat.Prime 10891
    norm_num1
  · change Nat.Prime 11597
    norm_num1
  · change Nat.Prime 11617
    norm_num1
  · change Nat.Prime 12343
    norm_num1
  · change Nat.Prime 12373
    norm_num1
  · change Nat.Prime 13099
    norm_num1
  · change Nat.Prime 13127
    norm_num1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem upperNumbers : ∀ i : Fin conjecturedValues.length,
    (upperList i).length = 50 + i.val ∧
      (upperList i).sum = conjecturedValues[i] := by
  intro i
  fin_cases i <;> decide +kernel

theorem member (i : Fin conjecturedValues.length) :
    conjecturedValues[i] ∈ {p : ℕ | p.Prime ∧
      ∃ S : Finset ℕ, S.card = 50 + i.val ∧ (∀ q ∈ S, q.Prime) ∧ S.sum id = p} := by
  obtain ⟨hlen, hsum⟩ := upperNumbers i
  have hd : (upperList i).Nodup := by
    unfold upperList
    exact upperPrimes_nodup.filter _
  refine ⟨targets_prime i, (upperList i).toFinset, (List.toFinset_card_of_nodup hd).trans hlen, ?_, ?_⟩
  · intro p h
    have hk : p ∈ upperList i := List.mem_toFinset.mp h
    unfold upperList at hk
    exact upperPrimes_prime p (List.mem_filter.mp hk).1
  · rw [List.sum_toFinset id hd]
    simpa using hsum

end A068873Cert

namespace A068873Cert

open OMA.S_oeis_a068873 Finset

theorem lower (i : Fin conjecturedValues.length) (p : ℕ) (hp : p.Prime)
    (S : Finset ℕ) (hc : S.card = 50 + i.val) (hpr : ∀ q ∈ S, q.Prime)
    (hsum : S.sum id = p) : conjecturedValues[i] ≤ p := by
  by_contra! hbad
  obtain ⟨hcard, hcut, hbudget⟩ := cutoff_certificate i
  have in_small : ∀ q : ℕ, q ∈ smallest i ↔ q ≤ cutoff i ∧ q.Prime := by
    intro q
    simp [smallest]
  have caps := window_bound (smallest i) S (cutoff i) (hcard.trans hc.symm)
    (fun q h => ((in_small q).mp (mem_sdiff.mp h).1).1)
    (by
      intro q h
      obtain ⟨hq, hno⟩ := mem_sdiff.mp h
      by_contra! hl
      exact hno ((in_small q).mpr ⟨hl.le, hpr _ hq⟩))
  have subset : S ⊆ primePool.toFinset := by
    intro q hq
    have hq760 : q ≤ 760 := by
      by_cases hm : q ∈ smallest i
      · exact ((in_small q).mp hm).1.trans hcut
      · have v := caps.2.2 q (mem_sdiff.mpr ⟨hq, hm⟩)
        change smallSum i + (q - cutoff i) ≤ S.sum id at v
        omega
    exact mem_primePool hq760 (hpr q hq)
  have hbit := reaches_mask primePool 65536 S subset
  change (masks primePool 65536).testBit (S.card * 65536 + S.sum id) = true at hbit
  rw [hc, hsum] at hbit
  have lo : smallSum i ≤ p := by
    have h := caps.1
    change smallSum i ≤ S.sum id at h
    simpa only [hsum] using h
  let j : Fin (conjecturedValues[i] - smallSum i) := ⟨p - smallSum i, by omega⟩
  have es : smallSum i + j.val = p := Nat.add_sub_of_le lo
  have hgap := gap_certificate i j
  rw [es] at hgap
  rw [hgap hp] at hbit
  contradiction

end A068873Cert

open OMA.S_oeis_a068873 in
theorem OMA.solution : type_of% @OMA.S_oeis_a068873.main := by
  intro i
  apply le_antisymm
  · exact Nat.sInf_le (A068873Cert.member i)
  · apply le_csInf ⟨_, A068873Cert.member i⟩
    rintro p ⟨hp, S, hc, hpr, hsum⟩
    exact A068873Cert.lower i p hp S hc hpr hsum
