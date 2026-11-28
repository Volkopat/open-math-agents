import OMAReductions.R_OeisA238281_conjecture_3_R1
import Mathlib

/- A bitmap for a bounded arithmetic progression. -/
namespace OMA.PrimeProgression

abbrev Bit (word i : ℕ) := word.testBit i = true

def repeatMarks (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | d+1, k =>
      if k = 0 then 0 else
        let h := k/2
        let lower := repeatMarks p d h
        let upper := lower <<< (p*h)
        let extra := if k%2 = 1 then 1 <<< (p*(2*h)) else 0
        lower ||| (upper ||| extra)

private theorem or_bit {a b i : ℕ} : Bit (a ||| b) i ↔ Bit a i ∨ Bit b i := by simp [Bit]

private theorem shift_bit {a s i : ℕ} : Bit (a <<< s) i ↔ s ≤ i ∧ Bit a (i-s) := by simp [Bit]

private theorem one_mark {s i : ℕ} : Bit (1 <<< s) i ↔ i = s := by
  rw [shift_bit]
  by_cases h : s ≤ i
  · simp only [h, true_and, Bit, Nat.testBit_one_eq_true_iff_self_eq_zero]
    omega
  · simp [h]
    omega

theorem repeatMarks_bit (p d k i : ℕ) (hk : k < 2^d) :
    Bit (repeatMarks p d k) i ↔ ∃ j < k, i = p*j := by
  induction d generalizing k i with
  | zero =>
    have : k = 0 := by simpa using hk
    subst k
    simp [Bit, repeatMarks]
  | succ d ih =>
    by_cases hz : k = 0
    · subst k; simp [repeatMarks, Bit]
    rw [repeatMarks, if_neg hz]
    dsimp only
    have hd : k/2 < 2^d := by rw [Nat.pow_succ] at hk; omega
    rw [or_bit, or_bit, shift_bit, ih (k/2) i hd]
    have sec : Bit (repeatMarks p d (k/2)) (i-p*(k/2)) ↔
        ∃ j < k/2, i-p*(k/2) = p*j := ih _ _ hd
    rw [sec]
    constructor
    · rintro (⟨j, hj, eq⟩ | (⟨hle, j, hj, hq⟩ | tail))
      · exact ⟨j, by omega, eq⟩
      · refine ⟨k/2+j, by omega, ?_⟩
        rw [Nat.mul_add]
        omega
      · by_cases h : k%2 = 1
        · rw [if_pos h, one_mark] at tail
          exact ⟨2*(k/2), by omega, tail⟩
        · rw [if_neg h] at tail
          simp [Bit] at tail
    · rintro ⟨j,hj,rfl⟩
      by_cases hj' : j < k/2
      · exact Or.inl ⟨j,hj',rfl⟩
      · right
        by_cases hhigh : j < 2*(k/2)
        · left
          exact ⟨Nat.mul_le_mul_left p (by omega), j-k/2, by omega, (Nat.mul_sub p j (k/2)).symm⟩
        · right
          have h0 : k%2 = 1 := by omega
          have h1 : j = 2*(k/2) := by omega
          rw [if_pos h0, one_mark, h1]

def firstOffset (p base : ℕ) : ℕ :=
  p*p/2 + p*((base-p*p/2 +(p-1))/p) - base

def primeMarks (p depth base width : ℕ) : ℕ :=
  let offset := firstOffset p base
  if offset < width then
    repeatMarks p depth (1+(width-1-offset)/p) <<< offset
  else 0

def composite (ps : List ℕ) (depth base width : ℕ) : ℕ :=
  ps.foldr (fun p mask => primeMarks p depth base width ||| mask)
    (if base=0 then 1 else 0)

private theorem mark_contains {p d base width i j : ℕ} (hp : 0 < p)
    (hw : width < 2^d) (hi : i < width)
    (hj : base+i = p*p/2 + p*j) : Bit (primeMarks p d base width) i := by
  let start := p*p/2
  let need := base-start
  let q := (need+(p-1))/p
  change base+i = start+p*j at hj
  have hbase : base ≤ start+p*q := by
    have hmod := Nat.mod_lt (need+(p-1)) hp
    have hdiv := Nat.div_add_mod (need+(p-1)) p
    change p*q+(need+(p-1))%p=need+(p-1) at hdiv
    dsimp [need] at hdiv hmod
    omega
  have hq : q ≤ j := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    rw [Nat.succ_mul, Nat.mul_comm j p]
    dsimp [need]
    omega
  let t := j-q
  let offset := firstOffset p base
  have ht : p*t = p*j-p*q := Nat.mul_sub p j q
  have hoff : offset = start+p*q-base := rfl
  have he : i = offset+p*t := by
    rw [ht,hoff]
    have hmul := Nat.mul_le_mul_left p hq
    omega
  have hinside : offset < width := by omega
  have hcount : t < 1+(width-1-offset)/p := by
    have hm : p*t ≤ width-1-offset := by omega
    have hdiv := (Nat.le_div_iff_mul_le hp).mpr (by simpa only [Nat.mul_comm] using hm : t*p ≤ width-1-offset)
    omega
  have hdepth : 1+(width-1-offset)/p < 2^d := by
    have hd := Nat.div_le_self (width-1-offset) p
    omega
  unfold primeMarks
  rw [if_pos hinside, shift_bit]
  refine ⟨by omega, (repeatMarks_bit _ _ _ _ hdepth).mpr ⟨t,hcount,?_⟩⟩
  omega

private theorem marked_if_mem {ps : List ℕ} {p depth base width i : ℕ}
    (hp : p ∈ ps) (hm : Bit (primeMarks p depth base width) i) :
    Bit (composite ps depth base width) i := by
  induction ps with
  | nil => simp at hp
  | cons q ps ih =>
    change Bit (primeMarks q depth base width ||| composite ps depth base width) i
    rw [or_bit]
    rcases List.mem_cons.mp hp with rfl|h
    · exact Or.inl hm
    · exact Or.inr (ih h)

private theorem unit_marked (ps : List ℕ) (depth width : ℕ) :
    Bit (composite ps depth 0 width) 0 := by
  induction ps with
  | nil => simp [composite, Bit]
  | cons p ps ih =>
    change Bit (primeMarks p depth 0 width ||| composite ps depth 0 width) 0
    exact or_bit.mpr (Or.inr ih)

private theorem odd_factor {p q x : ℕ} (he : x=p*q) (odd : x%2=1) :
    p%2=1 ∧ q%2=1 := by
  rw [he, Nat.mul_mod] at odd
  have hp := Nat.mod_lt p (by decide : 0<2)
  have hq := Nat.mod_lt q (by decide : 0<2)
  have notp : p%2≠0 := by intro h; simp [h] at odd
  have notq : q%2≠0 := by intro h; simp [h] at odd
  omega

theorem unmarked_prime {ps : List ℕ} {bound depth base width i : ℕ}
    (complete : ∀ p ≤ bound, p.Prime → p%2=1 → p ∈ ps)
    (hwidth : width < 2^depth) (hi : i<width)
    (hxbound : 2*(base+i)+1 < (bound+1)^2)
    (hx : (composite ps depth base width).testBit i = false) :
    (2*(base+i)+1).Prime := by
  let x := 2*(base+i)+1
  have hpos : 0<x := by dsimp [x]; omega
  have hn : x ≠ 1 := by
    intro eq
    have hb : base=0 := by dsimp [x] at eq; omega
    have hz : i=0 := by dsimp [x] at eq; omega
    rw [hb,hz] at hx
    have hu := unit_marked ps depth width
    change (composite ps depth 0 width).testBit 0 = true at hu
    rw [hx] at hu
    contradiction
  by_contra notPrime
  let p := x.minFac
  have prime : p.Prime := Nat.minFac_prime hn
  have sq : p^2 ≤ x := Nat.minFac_sq_le_self hpos notPrime
  have small : p ≤ bound := by
    by_contra! h
    have hs : (bound+1)^2 ≤ p^2 := Nat.pow_le_pow_left (by omega) 2
    change x < (bound+1)^2 at hxbound
    omega
  obtain ⟨q, eq⟩ := Nat.minFac_dvd x
  change x = p*q at eq
  have odd : x%2=1 := by dsimp [x]; omega
  obtain ⟨op, oq⟩ := odd_factor eq odd
  have hp := prime.pos
  have order : p ≤ q := by
    rw [eq, pow_two] at sq
    exact Nat.le_of_mul_le_mul_left sq hp
  let j := (q-p)/2
  have qp : q=p+2*j := by dsimp [j]; omega
  have mul : p*q = p*p + 2*(p*j) := by rw [qp]; ring
  have oddSquare : (p*p)%2=1 := by rw [Nat.mul_mod,op]
  have hline : base+i = p*p/2+p*j := by dsimp [x] at eq; omega
  have hh := marked_if_mem (complete p small prime op) (mark_contains hp hwidth hi hline)
  change (composite ps depth base width).testBit i = true at hh
  rw [hx] at hh
  contradiction

end OMA.PrimeProgression

namespace OMA.PrimePopulation

def population (width word : ℕ) : ℕ :=
  ∑ i ∈ Finset.range width, (word.testBit i).toNat

private theorem divide (left right word : ℕ) :
    population (left+right) word = population left word + population right (word >>> left) := by
  unfold population
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.testBit_shiftRight]

private theorem crop (width word : ℕ) :
    population width (word % (1 <<< width)) = population width word := by
  unfold population
  apply Finset.sum_congr rfl
  intro i member
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_mod_two_pow]
  simp [Finset.mem_range.mp member]

private def octet (word : ℕ) : ℕ := (0x8776766576656554766565546554544376656554655454436554544354434332766565546554544365545443544343326554544354434332544343324332322176656554655454436554544354434332655454435443433254434332433232216554544354434332544343324332322154434332433232214332322132212110 >>> (4*(word%256)))%16

set_option maxRecDepth 30000 in
private theorem octet_table : ∀ i : Fin 256, octet i.val = population 8 i.val := by decide +kernel

private theorem octet_exact (word : ℕ) : octet word = population 8 word := by
  have exact_table := octet_table ⟨word%256, Nat.mod_lt _ (by decide)⟩
  have lookup : octet (word%256) = octet word := by simp [octet]
  rw [lookup] at exact_table
  exact exact_table.trans (crop 8 word)

private def pop32 (word : ℕ) : ℕ :=
  octet word + (octet (word >>> 8) + (octet (word >>> 16) + octet (word >>> 24)))

private theorem pop32_exact (word : ℕ) : pop32 word = population 32 word := by
  rw [show (32 : ℕ) = 8+(8+(8+8)) by decide, divide 8 24, divide 8 16, divide 8 8]
  simp only [pop32, octet_exact, ← Nat.shiftRight_add]

private def width (n : ℕ) : ℕ := 32*2^n

private theorem double_width (n : ℕ) : width (n+1) = width n + width n := by
  simp [width, Nat.pow_succ, Nat.mul_two, Nat.mul_add]

private theorem population_full (n : ℕ) : population n ((1 <<< n)-1) = n := by
  unfold population
  calc
    _ = ∑ _i ∈ Finset.range n, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]
      simp [Finset.mem_range.mp hi]
    _ = _ := by simp

def countBlock : ℕ → ℕ → ℕ
  | 0, word => if word = 0 then 0 else
      if word = (1 <<< width 0)-1 then width 0 else pop32 word
  | step+1, word =>
    if word = 0 then 0 else if word = (1 <<< width (step+1))-1 then width (step+1) else
      let half := width step
      countBlock step (word % (1 <<< half)) + countBlock step (word >>> half)

theorem exactCount (depth word : ℕ) : countBlock depth word = population (width depth) word := by
  induction depth generalizing word with
  | zero =>
    by_cases empty : word = 0
    · subst word
      simp [countBlock, population]
    · by_cases full : word = (1 <<< width 0)-1
      · rw [countBlock, if_neg empty, if_pos full, full, population_full]
      · rw [countBlock, if_neg empty, if_neg full]
        exact pop32_exact word
  | succ depth ih =>
    by_cases empty : word = 0
    · subst word
      simp [countBlock, population]
    · by_cases full : word = (1 <<< width (depth+1))-1
      · rw [countBlock, if_neg empty, if_pos full, full, population_full]
      · rw [countBlock, if_neg empty, if_neg full]
        dsimp only
        rw [ih, ih, double_width, divide, crop]

theorem boundedCount (left right word : ℕ) (fit : word < 2^left) :
    population (left+right) word = population left word := by
  have zero : word >>> left = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt fit
  rw [divide, zero]
  simp [population]

theorem card_eq (width word : ℕ) :
    population width word = ((Finset.range width).filter (fun i => word.testBit i)).card := by
  classical
  calc
    population width word = ∑ i ∈ Finset.range width, (if word.testBit i then (1:ℕ) else 0) := by
      unfold population
      apply Finset.sum_congr rfl
      intro i _
      cases word.testBit i <;> decide
    _ = _ := by simp

def prefixPop (depth width word : ℕ) : ℕ :=
  countBlock depth (word % (1 <<< width))

theorem prefixPop_exact {depth width word : ℕ} (h : width ≤ 32*2^depth) :
    prefixPop depth width word = population width word := by
  unfold prefixPop
  rw [exactCount]
  have hw : PrimePopulation.width depth = width+(PrimePopulation.width depth-width) := by
    change width ≤ PrimePopulation.width depth at h
    omega
  conv_lhs => rw [hw,divide,crop]
  have hz : (word % (1 <<< width)) >>> width = 0 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.div_eq_of_lt (Nat.mod_lt _ (by positivity))
  simp [hz,population]

def oddCount (width : ℕ) : ℕ :=
  Nat.count (fun i => (2*i+1).Prime) width

def checkedSegment (ps : List ℕ) (markDepth popDepth base width : ℕ) : ℕ :=
  width - prefixPop popDepth width (OMA.PrimeProgression.composite ps markDepth base width)

theorem checkedSegment_lower {ps : List ℕ} {bound markDepth popDepth base width : ℕ}
    (complete : ∀ p ≤ bound, p.Prime → p%2=1 → p∈ps)
    (hw : width < 2^markDepth)
    (hpop : width ≤ 32*2^popDepth)
    (limit : 2*(base+width) ≤ (bound+1)^2) :
    checkedSegment ps markDepth popDepth base width ≤
      Nat.count (fun i => (2*(base+i)+1).Prime) width := by
  let word := OMA.PrimeProgression.composite ps markDepth base width
  unfold checkedSegment
  change width - prefixPop popDepth width word ≤ _
  rw [prefixPop_exact hpop,card_eq,Nat.count_eq_card_filter_range]
  have all := Finset.card_filter_add_card_filter_not (s:=Finset.range width) (fun i => word.testBit i = true)
  rw [Finset.card_range] at all
  have decomp : width-((Finset.range width).filter fun i => word.testBit i = true).card =
      ((Finset.range width).filter fun i => ¬word.testBit i = true).card := by omega
  rw [decomp]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hin,hzero⟩ := Finset.mem_filter.mp hi
  have hlt := Finset.mem_range.mp hin
  exact Finset.mem_filter.mpr ⟨hin,OMA.PrimeProgression.unmarked_prime complete hw hlt
    (by omega) (Bool.eq_false_iff.mpr hzero)⟩

theorem checkedSegment_add {ps : List ℕ} {bound markDepth popDepth base width current : ℕ}
    (complete : ∀ p ≤ bound, p.Prime → p%2=1 → p∈ps)
    (hw : width<2^markDepth) (hpop : width≤32*2^popDepth)
    (limit : 2*(base+width)≤(bound+1)^2) (hc : current ≤ oddCount base) :
    current + checkedSegment ps markDepth popDepth base width ≤ oddCount (base+width) := by
  unfold oddCount at hc ⊢
  rw [Nat.count_add]
  exact Nat.add_le_add hc (checkedSegment_lower complete hw hpop limit)

theorem oddCount_le_primeCounting {n slots : ℕ} (lo : 2 ≤ n) (hi : slots ≤ (n+1)/2) :
    1+oddCount slots ≤ n.primeCounting := by
  let f : ℕ ↪ ℕ := ⟨fun i => 2*i+1, by intro i j eq; change 2*i+1 = 2*j+1 at eq; omega⟩
  let odd := ((Finset.range slots).filter (fun i => (2*i+1).Prime)).map f
  have two : 2 ∉ odd := by
    intro h
    obtain ⟨i,_,eq⟩ := Finset.mem_map.mp h
    change 2*i+1 = 2 at eq
    omega
  have incl : insert 2 odd ⊆ Nat.primesLE n := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Nat.mem_primesLE.mpr ⟨lo,Nat.prime_two⟩
    · obtain ⟨i,hi',eq⟩ := Finset.mem_map.mp hx
      obtain ⟨hr,hp⟩ := Finset.mem_filter.mp hi'
      have hlt := Finset.mem_range.mp hr
      change 2*i+1 = x at eq
      exact Nat.mem_primesLE.mpr ⟨by omega,eq ▸ hp⟩
  have h := Finset.card_le_card incl
  rw [Finset.card_insert_of_notMem two,Nat.primesLE_card_eq_primeCounting] at h
  have hc : odd.card = oddCount slots := by
    unfold odd oddCount
    rw [Finset.card_map,Nat.count_eq_card_filter_range]
  omega

end OMA.PrimePopulation

namespace OMA.PrimePopulation

theorem oddCount_eq_primeCounting {n : ℕ} (hn : 2≤n) :
    n.primeCounting = 1+oddCount ((n+1)/2) := by
  apply le_antisymm ?_ (oddCount_le_primeCounting hn (slots := (n+1)/2) (le_refl _))
  let f : ℕ ↪ ℕ := ⟨fun i => 2*i+1, by
    intro i j eq
    change 2*i+1=2*j+1 at eq
    omega⟩
  let odd := ((Finset.range ((n+1)/2)).filter (fun i => (2*i+1).Prime)).map f
  have two : 2 ∉ odd := by
    intro has
    obtain ⟨i,_,eq⟩ := Finset.mem_map.mp has
    change 2*i+1=2 at eq
    omega
  have covers : Nat.primesLE n ⊆ insert 2 odd := by
    intro p hp
    obtain ⟨hpn,prime⟩ := Nat.mem_primesLE.mp hp
    apply Finset.mem_insert.mpr
    rcases prime.eq_two_or_odd with e|r
    · exact Or.inl e
    · right
      have value : 2*(p/2)+1=p := by omega
      have hlt : p/2<(n+1)/2 := by omega
      exact Finset.mem_map.mpr ⟨p/2,Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hlt,value.symm ▸ prime⟩,value⟩
  have h := Finset.card_le_card covers
  rw [Finset.card_insert_of_notMem two,Nat.primesLE_card_eq_primeCounting] at h
  have eq : odd.card=oddCount ((n+1)/2) := by
    unfold odd oddCount
    rw [Finset.card_map,Nat.count_eq_card_filter_range]
  omega

end OMA.PrimePopulation

/- The test uses each odd trial divisor up through the relevant square root. -/
namespace OMA.PrimeSieveBase

private def checks (trial q : ℕ) : Bool :=
  decide (3≤q ∧ q%2=1) &&
  (List.range' 3 (trial-2)).all (fun k => decide (q≤k ∨ q%k≠0))

def smallPrimes (bound trial : ℕ) : List ℕ :=
  (List.range (bound+1)).filter (checks trial)

theorem mem_smallPrimes {q bound trial : ℕ} (hq : q≤bound) (prime : q.Prime) (odd : q%2=1) :
    q ∈ smallPrimes bound trial := by
  unfold smallPrimes checks
  simp only [List.mem_filter,List.mem_range,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
  refine ⟨by omega,⟨by have := prime.two_le; omega,odd⟩,?_⟩
  intro k member
  have lower := (List.mem_range'_1.mp member).1
  by_cases order : q≤k
  · exact Or.inl order
  · right
    intro zero
    exact Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero zero) (by omega) (by omega) prime

theorem prime_of_mem_smallPrimes {q bound trial : ℕ} (stop : bound<(trial+1)^2)
    (member : q ∈ smallPrimes bound trial) : q.Prime := by
  unfold smallPrimes checks at member
  simp only [List.mem_filter,List.mem_range,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at member
  obtain ⟨within,⟨large,odd⟩,filter⟩ := member
  by_contra hn
  let p := q.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have dvd : p∣q := Nat.minFac_dvd q
  have podd : p%2=1 := hp.eq_two_or_odd.resolve_left (by
    intro h
    rw [h] at dvd
    have zero := Nat.mod_eq_zero_of_dvd dvd
    omega)
  have plarge : 3≤p := by have := hp.two_le; omega
  have psmall : p≤trial := by
    by_contra! ht
    have hpow : (trial+1)^2≤p^2 := Nat.pow_le_pow_left ht 2
    have hl := Nat.minFac_sq_le_self (by omega : 0<q) hn
    change p^2≤q at hl
    omega
  have lt : p<q := (Nat.not_prime_iff_minFac_lt (by omega : 2≤q)).mp hn
  have hb : p ∈ List.range' 3 (trial-2) := List.mem_range'_1.mpr ⟨plarge,by omega⟩
  exact (filter p hb).elim (fun h => (Nat.not_le_of_lt lt) h) (fun h => h (Nat.mod_eq_zero_of_dvd dvd))

end OMA.PrimeSieveBase

namespace OMA.PrimePopulation

abbrev Row := ℕ × ℕ × ℕ × ℕ

def popDepth (span : ℕ) : ℕ :=
  if span ≤ 32 then 0 else (span/32).log2+1

private theorem depth_bound (span : ℕ) : span ≤ 32*2^(popDepth span) := by
  unfold popDepth
  split
  · simpa
  · have h : span/32 < 2^((span/32).log2+1) := Nat.lt_log2_self
    omega

def sliceOdd (word left span : ℕ) : ℕ :=
  span - prefixPop (popDepth span) span (word >>> left)

end OMA.PrimePopulation

namespace OMA.PrimeProgression

private theorem prime_of_no_mark {ps : List ℕ} {depth base width i : ℕ}
    (roster : ∀ p ∈ ps, p.Prime ∧ p%2=1)
    (hw : width<2^depth)
    (prime : (2*(base+i)+1).Prime) : (composite ps depth base width).testBit i = false := by
  induction ps with
  | nil =>
    by_cases hb : base=0
    · subst base
      have hi : i≠0 := by intro hz; subst i; exact Nat.not_prime_one prime
      change (1 : ℕ).testBit i = false
      exact Bool.eq_false_iff.mpr fun ht => hi (Nat.testBit_one_eq_true_iff_self_eq_zero.mp ht)
    · simp [composite, hb]
  | cons p ps ih =>
    obtain ⟨hp, odd⟩ := roster p (by simp)
    have tail : (composite ps depth base width).testBit i = false :=
      ih (fun q hq => roster q (List.mem_cons_of_mem _ hq))
    change (primeMarks p depth base width ||| composite ps depth base width).testBit i = false
    rw [Nat.testBit_or, tail, Bool.or_false]
    by_contra hm
    have flagged : Bit (primeMarks p depth base width) i := by
      cases h : (primeMarks p depth base width).testBit i <;> simp_all [Bit]
    let s := p*p/2
    let k := (base-s+(p-1))/p
    let offset := firstOffset p base
    have hoff : offset = s+p*k-base := rfl
    have hbase : base ≤ s+p*k := by
      have hmod := Nat.mod_lt (base-s+(p-1)) hp.pos
      have hdiv := Nat.div_add_mod (base-s+(p-1)) p
      change p*k+(base-s+(p-1))%p=base-s+(p-1) at hdiv
      omega
    change Bit (if offset < width then repeatMarks p depth (1+(width-1-offset)/p) <<< offset else 0) i at flagged
    split at flagged
    · rename_i hinside
      rw [shift_bit] at flagged
      have hdepth : 1+(width-1-offset)/p < 2^depth := by
        have hd := Nat.div_le_self (width-1-offset) p
        omega
      obtain ⟨j, _, hj⟩ := (repeatMarks_bit _ _ _ _ hdepth).mp flagged.2
      have hrow : base+i=s+p*(k+j) := by rw [Nat.mul_add]; omega
      have parity : (p*p)%2=1 := by rw [Nat.mul_mod, odd]
      have hs : 2*s+1=p*p := by dsimp [s]; omega
      have factor : 2*(base+i)+1=p*(p+2*(k+j)) := by
        rw [hrow]
        calc
          2 * (s + p * (k + j)) + 1 = (2*s+1)+2*(p*(k+j)) := by ring
          _ = _ := by rw [hs]; ring
      have lt : p < 2*(base+i)+1 := by
        rw [factor]
        calc
          p < p*2 := by have := hp.pos; omega
          _ ≤ p*(p+2*(k+j)) := Nat.mul_le_mul_left _ (by have := hp.two_le; omega)
      exact (Nat.not_prime_of_dvd_of_lt ⟨_, factor⟩ hp.two_le lt) prime
    · simp [Bit] at flagged

theorem unmarked_iff_prime {ps : List ℕ} {bound depth base width i : ℕ}
    (roster : ∀ p ∈ ps, p.Prime ∧ p%2=1)
    (complete : ∀ p ≤ bound, p.Prime → p%2=1 → p ∈ ps)
    (hw : width<2^depth) (hi : i<width) (cap : 2*(base+width)≤(bound+1)^2) :
    (composite ps depth base width).testBit i = false ↔ (2*(base+i)+1).Prime :=
  ⟨unmarked_prime complete hw hi (by omega), prime_of_no_mark roster hw⟩

end OMA.PrimeProgression

namespace OMA.PrimePopulation

theorem sliceOdd_exact {ps : List ℕ} {bound markDepth base width left span : ℕ}
    (roster : ∀ p ∈ ps, p.Prime ∧ p%2=1)
    (complete : ∀ p ≤ bound, p.Prime → p%2=1 → p ∈ ps)
    (hw : width<2^markDepth) (cap : 2*(base+width)≤(bound+1)^2)
    (inside : left+span ≤ width) :
    sliceOdd (OMA.PrimeProgression.composite ps markDepth base width) left span =
      Nat.count (fun i => (2*(base+left+i)+1).Prime) span := by
  let word := OMA.PrimeProgression.composite ps markDepth base width
  unfold sliceOdd
  change span-prefixPop (popDepth span) span (word >>> left) = _
  rw [prefixPop_exact (depth_bound span), card_eq, Nat.count_eq_card_filter_range]
  have all := Finset.card_filter_add_card_filter_not (s:=Finset.range span)
    (fun i => (word >>> left).testBit i = true)
  rw [Finset.card_range] at all
  have decomp : span-((Finset.range span).filter fun i => (word >>> left).testBit i = true).card =
      ((Finset.range span).filter fun i => ¬(word >>> left).testBit i = true).card := by omega
  rw [decomp]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Bool.not_eq_true, Nat.testBit_shiftRight]
  constructor
  · intro ⟨hi, hm⟩
    exact ⟨hi, by simpa only [Nat.add_assoc] using
      (OMA.PrimeProgression.unmarked_iff_prime roster complete hw (by omega) cap).mp hm⟩
  · intro ⟨hi, hp⟩
    exact ⟨hi, (OMA.PrimeProgression.unmarked_iff_prime roster complete hw (by omega) cap).mpr
      (by simpa only [Nat.add_assoc] using hp)⟩

theorem from_two_endpoints {a b : ℕ} (ha : 2≤a) (hab : a≤b) :
    b.primeCounting-a.primeCounting =
      Nat.count (fun i => (2*((a+1)/2+i)+1).Prime) ((b+1)/2-(a+1)/2) := by
  let x := (a+1)/2
  let y := (b+1)/2
  rw [oddCount_eq_primeCounting ha, oddCount_eq_primeCounting (ha.trans hab)]
  let f : ℕ → Prop := fun i => (2*i+1).Prime
  change 1+Nat.count f y-(1+Nat.count f x) = Nat.count (fun i => f (x+i)) (y-x)
  have hsplit : Nat.count f y = Nat.count f x+Nat.count (fun i => f (x+i)) (y-x) := by
    conv_lhs => rw [show y=x+(y-x) by dsimp [x,y]; omega]
    exact Nat.count_add f x (y-x)
  omega

theorem index_bound {n k : ℕ} (hn : 0<n) (h : k.primeCounting<n) : k<Nat.nth Nat.Prime (n-1) := by
  by_contra! hk
  have hp := Nat.prime_nth_prime (n-1)
  have count : (Nat.nth Nat.Prime (n-1)).primeCounting = n := by
    rw [Nat.primeCounting_eq_primeCounting'_succ]
    unfold Nat.primeCounting'
    rw [Nat.count_succ]
    simp only [hp, if_true]
    rw [show Nat.count Nat.Prime (Nat.nth Nat.Prime (n-1)) = n-1 from Nat.primeCounting'_nth_eq _]
    omega
  have := Nat.monotone_primeCounting hk
  omega

end OMA.PrimePopulation

namespace OMA.PrimeIntervalTriple

open OMA.PrimePopulation

abbrev Witness := ℕ × ℕ × ℕ

def Witness.correct (r : Witness) : Prop :=
  let (n,k,_) := r
  0<k ∧ k<Nat.nth Nat.Prime (n-1) ∧
    ((k+1)*n).primeCounting-(k*n).primeCounting =
      ((k+2)*n).primeCounting-((k+1)*n).primeCounting ∧
    ((k+2)*n).primeCounting-((k+1)*n).primeCounting =
      ((k+3)*n).primeCounting-((k+2)*n).primeCounting

private def slots (x : ℕ) : ℕ := (x+1)/2

def check (base width word rankWord : ℕ) (r : Witness) : Bool :=
  let (n,k,c) := r
  let a := slots (k*n)
  let b := slots ((k+1)*n)
  let d := slots ((k+2)*n)
  let e := slots ((k+3)*n)
  decide (4<n ∧ 0<k ∧ base≤a ∧ e≤base+width) &&
    (decide (k<n+1) || decide (2≤k ∧ k≤3770 ∧ 1+sliceOdd rankWord 0 (slots k)<n)) &&
    decide (sliceOdd word (a-base) (b-a) = c ∧
      sliceOdd word (b-base) (d-b) = c ∧ sliceOdd word (d-base) (e-d) = c)

private theorem slice_difference {ps : List ℕ} {bound depth base width a b : ℕ}
    (primes : ∀ p ∈ ps, p.Prime ∧ p%2=1)
    (complete : ∀ p ≤ bound, p.Prime → p%2=1 → p ∈ ps)
    (hw : width<2^depth) (cap : 2*(base+width)≤(bound+1)^2)
    (lo : 2≤a) (ord : a≤b) (ha : base ≤ slots a) (hb : slots b≤base+width) :
    sliceOdd (OMA.PrimeProgression.composite ps depth base width) (slots a-base) (slots b-slots a) =
      b.primeCounting-a.primeCounting := by
  have hslots : slots a ≤ slots b := by unfold slots; omega
  have inside : slots a-base+(slots b-slots a) ≤ width := by omega
  rw [sliceOdd_exact primes complete hw cap inside, from_two_endpoints lo ord]
  rw [show base+(slots a-base)=slots a by omega]
  rfl

theorem sound {ps rankPrimes : List ℕ} {bound depth base width : ℕ}
    (primes : ∀ p ∈ ps, p.Prime ∧ p%2=1)
    (complete : ∀ p ≤ bound, p.Prime → p%2=1 → p ∈ ps)
    (rankGood : ∀ p ∈ rankPrimes, p.Prime ∧ p%2=1)
    (rankComplete : ∀ p ≤ 61, p.Prime → p%2=1 → p ∈ rankPrimes)
    (hw : width<2^depth) (cap : 2*(base+width)≤(bound+1)^2) {r : Witness}
    (h : check base width (OMA.PrimeProgression.composite ps depth base width)
      (OMA.PrimeProgression.composite rankPrimes 11 0 1885) r = true) : r.correct := by
  obtain ⟨n,k,c⟩ := r
  simp only [check,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨hn,hk,ha,he⟩, hidx⟩, s₀,s₁,s₂⟩ := h
  have index : k<Nat.nth Nat.Prime (n-1) := by
    rcases hidx with fast|slow
    · have := Nat.add_two_le_nth_prime (n-1)
      omega
    · obtain ⟨hlo,hhi,hpop⟩ := slow
      have hinside : 0+slots k ≤ 1885 := by unfold slots; omega
      have hcount := sliceOdd_exact rankGood rankComplete (by decide : 1885<2^11)
        (by decide : 2*(0+1885)≤(61+1)^2) hinside
      rw [hcount] at hpop
      apply index_bound (by omega)
      rw [oddCount_eq_primeCounting hlo]
      simpa only [Nat.zero_add,slots,oddCount] using hpop
  have hstart : 2≤k*n := by
    calc
      2 ≤ n := by omega
      _ ≤ k*n := by simpa using Nat.mul_le_mul_right n (show 1≤k by omega)
  have o₀ : k*n≤(k+1)*n := Nat.mul_le_mul_right n (by omega)
  have o₁ : (k+1)*n≤(k+2)*n := Nat.mul_le_mul_right n (by omega)
  have o₂ : (k+2)*n≤(k+3)*n := Nat.mul_le_mul_right n (by omega)
  have hmono {x y : ℕ} (hxy : x≤y) : slots x ≤ slots y := by unfold slots; omega
  have h₀ := slice_difference primes complete hw cap hstart o₀ ha
    (((hmono o₁).trans (hmono o₂)).trans he)
  have h₁ := slice_difference primes complete hw cap (hstart.trans o₀) o₁
    (ha.trans (hmono o₀)) ((hmono o₂).trans he)
  have h₂ := slice_difference primes complete hw cap ((hstart.trans o₀).trans o₁) o₂
    ((ha.trans (hmono o₀)).trans (hmono o₁)) he
  exact ⟨hk,index,(h₀.symm.trans s₀).trans (h₁.symm.trans s₁).symm,
    (h₁.symm.trans s₁).trans (h₂.symm.trans s₂).symm⟩

def rowBits (rows : List Witness) : ℕ :=
  rows.foldr (fun row bits => (1 <<< row.1) ||| bits) 0

theorem rowBits_member {rows : List Witness} {n : ℕ} :
    (rowBits rows).testBit n = true ↔ ∃ row ∈ rows, row.1=n := by
  induction rows with
  | nil => simp [rowBits]
  | cons r rs ih =>
    change OMA.PrimeProgression.Bit ((1 <<< r.1) ||| rowBits rs) n ↔ _
    rw [OMA.PrimeProgression.or_bit, OMA.PrimeProgression.one_mark]
    change (n=r.1 ∨ (rowBits rs).testBit n = true) ↔ _
    rw [ih]
    constructor
    · rintro (eq|⟨row,hrow,eq⟩)
      · exact ⟨r,by simp,eq.symm⟩
      · exact ⟨row,List.mem_cons_of_mem _ hrow,eq⟩
    · rintro ⟨row,hrow,eq⟩
      rcases List.mem_cons.mp hrow with rfl|hm
      · exact Or.inl eq.symm
      · exact Or.inr ⟨row,hm,eq⟩

theorem append_correct {xs ys : List Witness} (hx : ∀ row ∈ xs, Witness.correct row)
    (hy : ∀ row ∈ ys, Witness.correct row) : ∀ row ∈ xs++ys, Witness.correct row := by
  intro row hm
  rcases List.mem_append.mp hm with h|h
  · exact hx row h
  · exact hy row h

end OMA.PrimeIntervalTriple

namespace OMA.PrimeIntervalTriple

private def primes : List ℕ := [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283,1289,1291,1297,1301,1303,1307,1319,1321,1327,1361,1367,1373,1381,1399,1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,1511,1523,1531,1543,1549,1553,1559,1567,1571,1579,1583,1597,1601,1607,1609,1613,1619,1621,1627,1637,1657,1663,1667,1669,1693,1697,1699,1709,1721,1723,1733,1741,1747,1753,1759,1777,1783,1787,1789,1801,1811,1823,1831,1847,1861,1867,1871,1873,1877,1879,1889,1901,1907,1913,1931,1933,1949,1951,1973,1979,1987,1993,1997,1999,2003,2011,2017,2027,2029,2039,2053,2063,2069,2081,2083,2087,2089,2099,2111,2113,2129,2131,2137,2141,2143,2153,2161,2179,2203,2207,2213,2221,2237,2239,2243,2251,2267,2269,2273,2281,2287,2293,2297,2309,2311,2333,2339,2341,2347,2351,2357,2371,2377,2381,2383,2389,2393,2399,2411,2417,2423,2437,2441,2447,2459,2467,2473,2477,2503,2521,2531,2539,2543,2549,2551,2557,2579,2591,2593]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem primes_exact : primes = OMA.PrimeSieveBase.smallPrimes 2595 50 := by decide +kernel

private theorem primes_prime : ∀ p ∈ primes, p.Prime ∧ p%2=1 := by
  intro p hp
  rw [primes_exact] at hp
  exact ⟨OMA.PrimeSieveBase.prime_of_mem_smallPrimes (by decide) hp,
    by unfold OMA.PrimeSieveBase.smallPrimes OMA.PrimeSieveBase.checks at hp
       simp only [List.mem_filter,Bool.and_eq_true,decide_eq_true_eq] at hp
       exact hp.2.1.2⟩

private theorem primes_complete : ∀ p ≤ 2595, p.Prime → p%2=1 → p ∈ primes := by
  rw [primes_exact]
  intro p hp hprime hodd
  exact OMA.PrimeSieveBase.mem_smallPrimes hp hprime hodd

private def rankPrimes : List ℕ := [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem rankPrimes_exact : rankPrimes = OMA.PrimeSieveBase.smallPrimes 61 7 := by decide +kernel

private theorem rankPrimes_prime : ∀ p ∈ rankPrimes, p.Prime ∧ p%2=1 := by
  intro p hp
  rw [rankPrimes_exact] at hp
  exact ⟨OMA.PrimeSieveBase.prime_of_mem_smallPrimes (by decide) hp,
    by unfold OMA.PrimeSieveBase.smallPrimes OMA.PrimeSieveBase.checks at hp
       simp only [List.mem_filter,Bool.and_eq_true,decide_eq_true_eq] at hp
       exact hp.2.1.2⟩

private theorem rankPrimes_complete : ∀ p ≤ 61, p.Prime → p%2=1 → p ∈ rankPrimes := by
  rw [rankPrimes_exact]
  intro p hp hprime hodd
  exact OMA.PrimeSieveBase.mem_smallPrimes hp hprime hodd

private def rankMask : ℕ := 0x6ffdb77badfa7dfdb76b7ef3df3d9a7b7ddff92efeffb7f3f9e7d7cd6d9fff7c9ffbaedf5be5ffefe7bfed7dbeebf5de7ffcdafdf7bb6f77faddafdfcb3ef7ebbcf65da5b74f7efaefe7dffb35deff7ffaddf6bf6df6b2dfb59bff3eb6e9fdd3fbb5ffdfeef2cfe7de4fb7bf79edd2ddbff3f9fedbef25bf7f77def96ff6dbbcfbcbff96ffbd9a6bf5d76b7ddf7da4f7d97697ef7fbb6ffff67d2cd3fdefb36beedbdde7fedbb697fb3cf679afb76d7edaef75ff4bf4bf793cfbdfaeb75b77bbddaf9b4f7cb66decdbdbfcfb5d77d2ed679eebb5b769edfa5fbcb36de697df279b5b3cd7e92ed659b4b3491

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def rankMatches : PLift (OMA.PrimeProgression.composite rankPrimes 11 0 1885 = rankMask) :=
  ⟨by decide +kernel⟩

private def rows0 : List Witness :=
  [(6,1,2),
  (11,1,3),
  (13,1,3),
  (17,1,4),
  (5,4,1),
  (21,1,5),
  (23,1,5),
  (26,1,6),
  (7,4,2),
  (33,1,7),
  (9,5,2),
  (18,3,4),
  (8,7,2),
  (31,2,6),
  (63,1,12),
  (15,5,3),
  (41,2,8),
  (43,2,8),
  (25,4,5),
  (12,9,2),
  (28,4,5),
  (112,1,19),
  (114,1,19),
  (16,8,3),
  (27,5,5),
  (48,3,9),
  (10,15,2),
  (76,2,13),
  (14,13,2),
  (46,4,8),
  (65,3,11),
  (103,2,17),
  (77,3,13),
  (81,3,13),
  (44,6,7),
  (29,12,5),
  (20,18,3),
  (34,12,6),
  (35,12,6),
  (145,3,22),
  (157,3,23),
  (121,4,18),
  (122,4,18),
  (265,2,39),
  (30,18,5),
  (42,13,7),
  (201,3,29),
  (69,9,10),
  (125,5,18),
  (324,2,46),
  (50,13,7),
  (169,4,24),
  (339,2,47),
  (19,38,3),
  (52,14,8),
  (61,12,9),
  (24,31,3),
  (53,15,8),
  (73,11,11),
  (163,5,24),
  (22,38,3),
  (95,9,14),
  (216,4,30),
  (54,17,8),
  (32,29,5),
  (58,16,9),
  (68,14,10),
  (60,16,9),
  (37,26,6),
  (104,10,14),
  (72,15,10),
  (123,9,16),
  (36,32,5),
  (173,7,24),
  (306,4,41),
  (106,12,15),
  (262,5,34),
  (92,15,13),
  (39,36,6),
  (38,37,6),
  (51,28,8),
  (305,5,40),
  (520,3,66),
  (321,5,41),
  (108,15,13),
  (71,23,8),
  (66,25,8),
  (118,14,15),
  (79,21,10),
  (119,14,15),
  (67,25,8),
  (129,13,16),
  (211,8,27),
  (213,8,27),
  (101,17,13),
  (75,23,9)]

private def mask0 : ℕ := 0xf7fdafb7dd7ebbcfff9b5fbef76deeff5bb5fbf967defd779ecbb4b6e9efdf5dfcfbff66bbdfefff5bbed7edbed65bf6b37fe7d6dd3fba7f76bffbfdde59fcfbc9f6f7ef3dba5bb7fe7f3fdb7de4b7efeefbdf2dfedb779f797ff2dff7b34d7ebaed6fbbefb49efb2ed2fdeff76dfffecfa59a7fbdf66d7ddb7bbcffdb76d2ff679ecf35f6edafdb5deebfe97e97ef279f7bf5d6eb6ef77bb5f369ef96cdbd9b7b7f9f6baefa5dacf3dd76b6ed3dbf4bf7966dbcd2fbe4f36b679afd25dacb3696692

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches0 : PLift ((OMA.PrimeProgression.composite primes 11 3 1557) = mask0) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified0 : PLift (rows0.all (check 3 1557 mask0 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct0 : ∀ r ∈ rows0, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified0.down r hr
  rw [←maskMatches0.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows1 : List Witness :=
  [(96,18,12),
  (872,2,108),
  (877,2,108),
  (147,12,18),
  (444,4,56),
  (356,5,46),
  (259,7,32),
  (115,16,15),
  (97,19,13),
  (168,11,22),
  (89,21,12),
  (137,14,17),
  (647,3,81),
  (663,3,83),
  (668,3,83),
  (338,6,43),
  (49,45,7),
  (56,40,8),
  (78,31,8),
  (40,68,5),
  (57,48,7),
  (347,8,42),
  (215,13,25),
  (47,61,5),
  (80,36,9),
  (181,16,21),
  (164,18,19),
  (74,40,8),
  (424,7,51),
  (601,5,72),
  (55,57,6),
  (209,15,26),
  (131,24,16),
  (189,17,24),
  (179,18,22),
  (180,18,23),
  (148,22,19),
  (155,21,20),
  (142,23,18),
  (102,34,13),
  (193,18,24),
  (99,36,12),
  (275,13,33),
  (325,11,39),
  (140,26,17),
  (203,18,25),
  (176,21,21),
  (925,4,108),
  (64,58,7),
  (928,4,108),
  (59,63,7),
  (311,12,37),
  (45,83,5),
  (234,16,27),
  (312,12,37),
  (159,24,20),
  (182,21,22),
  (383,10,45),
  (491,8,56),
  (188,21,21),
  (396,10,46),
  (792,5,92),
  (572,7,67),
  (149,27,17),
  (507,8,59),
  (508,8,59),
  (83,49,10),
  (228,18,26),
  (316,13,37),
  (242,17,28),
  (516,8,60),
  (518,8,60),
  (208,20,23),
  (85,49,9),
  (521,8,60),
  (301,14,36),
  (856,5,98),
  (390,11,44),
  (392,11,45),
  (90,48,10),
  (310,14,35),
  (395,11,46),
  (725,6,83),
  (86,51,10),
  (134,33,16),
  (404,11,47),
  (171,26,20),
  (345,13,40),
  (499,9,58),
  (100,45,12),
  (98,46,12),
  (648,7,75),
  (93,49,11),
  (571,8,66),
  (576,8,67),
  (437,11,50)]

private def mask1 : ℕ := 0xee97fde79fcffebf7b3cf6f9bfbfdf77facde5feefffdeebfcffdbffbbdb66f6edb79f7b36f7fbadd3ffbdf779eefbcf6dfb5bbfd7fdbffefdf5ff6fe79acd7dbb6f75fffb2ffb7badfbc967f7fff7badbffd67d3fd37fecb7cb76dbfff5fbdfb6fe6fbffa5fefbbdd7edfff6d9f6bfddf7f3cd6dfa7b769f7b7efb7bfff7ebe697ff77facff7df6f6cd3fbfdb77f6f9ffd2dfbcff6d6ff3efb7fbdbbcf7ffeede79bcf3cdeffeff2fda7f7d9f6fecffd9b4fbff7fd7cd35feebf797ef3fdafde6ffdb77badfa7dfdb76b7ef3df3d9a7b7ddff92efeffb7f3f9e7d7cd6d9fff7c9ffbaedf5be5ffefe7bfed7dbeebf5de7ffcdafdf7bb6f77faddafdfcb3ef7ebbcf65da5b74f7efaefe7dffb35deff7ffaddf6bf6df6b2dfb59bff3eb6e9fdd3fbb5ffdfeef2cfe7de4fb7bf79edd2ddbff3f9fedbef25bf7f77def96ff6dbb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches1 : PLift ((OMA.PrimeProgression.composite primes 12 864 2560) = mask1) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified1 : PLift (rows1.all (check 864 2560 mask1 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct1 : ∀ r ∈ rows1, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified1.down r hr
  rw [←maskMatches1.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows2 : List Witness :=
  [(965,5,110),
  (353,14,41),
  (550,9,64),
  (166,30,19),
  (501,10,57),
  (557,9,63),
  (629,8,72),
  (504,10,57),
  (509,10,58),
  (70,73,7),
  (570,9,65),
  (467,11,53),
  (289,18,33),
  (239,22,28),
  (170,31,20),
  (278,19,32),
  (183,29,22),
  (130,41,16),
  (105,51,13),
  (187,29,22),
  (133,41,16),
  (606,9,69),
  (473,12,54),
  (519,11,59),
  (136,42,15),
  (482,12,55),
  (980,6,108),
  (981,6,108),
  (331,18,37),
  (150,40,18),
  (1500,4,167),
  (94,64,11),
  (82,74,10),
  (296,21,34),
  (298,21,34),
  (421,15,47),
  (489,13,54),
  (402,16,44),
  (811,8,89),
  (813,8,90),
  (198,33,23),
  (386,17,44),
  (128,52,16),
  (165,41,19),
  (84,81,10),
  (379,18,43),
  (976,7,108),
  (1157,6,128),
  (884,8,97),
  (885,8,97),
  (88,82,8),
  (87,83,8),
  (382,19,41),
  (280,26,31),
  (672,11,75),
  (681,11,77),
  (938,8,105),
  (627,12,70),
  (755,10,84),
  (756,10,84),
  (253,30,27),
  (285,27,30),
  (243,32,25),
  (167,47,18),
  (874,9,97),
  (232,34,24),
  (300,27,33),
  (153,53,16),
  (281,29,31),
  (326,25,36),
  (292,28,33),
  (111,75,11),
  (420,20,47),
  (249,34,28),
  (409,21,47),
  (110,79,13),
  (223,39,25),
  (224,39,25),
  (463,19,52),
  (192,46,21),
  (141,63,15),
  (156,57,17),
  (377,24,42),
  (533,17,58),
  (62,147,7),
  (172,53,20),
  (218,42,25),
  (220,42,25),
  (308,31,33),
  (406,24,43),
  (337,29,36),
  (1400,7,148),
  (758,13,79),
  (548,18,57),
  (430,23,45),
  (283,35,30)]

private def mask2 : ℕ := 0x1fffafffcf769fe97eff79ffbbddfe9bff679f4b3dff7f6edfdbf7bf7f7ef7efbddb6f7fd6f9fdfbffe6bf5f6ffeef77de7ffeb6ebaffb7dadfffbf6d7ff27fadbb7dfe9aed7fffdf7d9f7bbdfedfaff77b77fbedb5fecf7db77f6cfbdbb6bb7f6fd7dd77be5ffebf6ffdf75dbcf3efeedfffe5dbffb4d7ff3ff65ffebfede7b7cdafdb7bfebffb2ddb7da7fffbef9fcf75ff7ff7d7fd6efff9ffbbfb66faffadfbefb7bf7f3ff75befbb7d6ebffdfdff4f3dfef97fdaf9e7bfeffef6edfdde7ffdbe6fecdbdbfffbddeff7ed6f9febfeb6fbafdb5dffbbffe7f7cfbdfa5ff4fffbbff7dfb4f779f7f2edaffbeff7d76bbcdffbacfbcdff9fff3fffdbfdde6fedfafbe6fb5f6efadf3fdadf3ff779fdf6f9adf7effffaedf7bf6fb69ff93cdedbf6ffd97ebbfde5ff7f3edf6beddf5bf5bfdbeffeef67dfcb3ffe6fbdd6fffdbfe9f79bcfaffaff76d6fb6ed75dbfb7cbf79fddeffa7b77dfffedfaf9afffcf76f7ff7dbf4bf5bfed3cf7fbeeb7effedbdd37dedfbff67f7ffef9f5bbedfe96fdf7db7ff5fff97dfadfaeb75ff6bfdfaf9b5f3cd76deef35fe6ff7f6ff7ff7f9fcf7cf7efffdaddecbf6f7fbbff37dbffbdf7ebeedf5bb6b3cfffdaefef9b7f74bfef3cfe7ff5fbd9e7b7cdfdfefbbfd66f2ff77ffef75fe7fedffddedb37b76dbcfbd9b7bfdd6e9ffdefbbcf77de7b6fdaddfebfedfff7efaffb7f3cd66beddb7bafffd97fdbdd6fde4b3fbfffbdd6dffeb3e9fe9bff65be5bb6dfffafdefdb7f37dffd2ff7ddeebf6fffb6cfb5feefbf9e6b6fd3dbb4fbdbf7dbdfffb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches2 : PLift ((OMA.PrimeProgression.composite primes 13 2413 4587) = mask2) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified2 : PLift (rows2.all (check 2413 4587 mask2 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct2 : ∀ r ∈ rows2, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified2.down r hr
  rw [←maskMatches2.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows3 : List Witness :=
  [(481,21,50),
  (676,15,71),
  (113,90,12),
  (261,39,27),
  (408,25,42),
  (680,15,70),
  (354,29,37),
  (428,24,44),
  (313,33,32),
  (370,28,37),
  (346,30,35),
  (135,77,14),
  (151,69,16),
  (282,37,29),
  (174,60,18),
  (498,21,51),
  (327,32,33),
  (524,20,54),
  (191,55,19),
  (206,51,21),
  (146,72,15),
  (229,46,23),
  (204,52,21),
  (272,39,28),
  (237,45,24),
  (255,42,26),
  (412,26,42),
  (219,49,22),
  (186,58,19),
  (109,99,11),
  (1366,8,143),
  (126,87,13),
  (479,23,50),
  (443,25,46),
  (227,49,22),
  (116,97,12),
  (143,79,14),
  (269,43,28),
  (416,28,45),
  (158,74,18),
  (441,27,49),
  (351,34,39),
  (152,79,16),
  (1367,9,143),
  (1241,10,132),
  (107,118,11),
  (154,82,16),
  (160,79,17),
  (706,18,73),
  (1864,7,192),
  (196,67,20),
  (1877,7,193),
  (1879,7,193),
  (490,27,49),
  (442,30,44),
  (1659,8,171),
  (132,104,13),
  (643,22,69),
  (214,67,24),
  (268,54,29),
  (537,27,59),
  (394,38,42),
  (139,108,16),
  (1713,9,173),
  (241,64,26),
  (1715,9,173),
  (258,60,27),
  (535,29,54),
  (162,96,17),
  (1041,15,106),
  (1042,15,106),
  (1962,8,197),
  (297,53,29),
  (277,57,27),
  (195,81,19),
  (120,132,12),
  (468,34,45),
  (210,76,20),
  (320,50,31),
  (302,53,29),
  (91,177,8),
  (246,66,23),
  (250,65,24),
  (362,45,35),
  (314,52,31),
  (355,46,36),
  (270,61,26),
  (475,35,49),
  (388,43,39),
  (453,37,46),
  (256,66,27),
  (264,64,28),
  (221,77,23),
  (465,37,49),
  (233,74,24),
  (413,42,44)]

private def mask3 : ℕ := 0xdda7ffd97eb2dfbfffdfbed6e9fffb7fa5fffb77feffb7bfcbbdb76bfdfb7dffb3ffee93dfe7fafbbddfe9eedfddffffcff7f3ed2fbe7bf7dfeffcfbfbedfffbe6f7df3ffa7fff9effaed7fde5b76bffdeff77dfcfbfdfed7df2fdb5b7dfeefaff67bf4fb79f7deedff9ffb779ffb7ddfdfacfbef779edff7fffffdb7edbede7bffb7db66dedd25fbeb37ffff7ef77dfdbbdf6fb2ffe7fb7f3fdfffecd7fbf6ff5dffb7efbffe4fbfff7bfeffffb5bf7f76fbedf7beef7ff7fdffdafffdf3f97ef7dff5badbf7d7fbafdf7dfcb7cff7d3fd6dbeef7dff6f2cffddf7f3c9fff7ff35be7fbd9e6fbdfefbe7bfefe6ffdf3ddfdbff9f79fffafde7f35fefbfef7d9b6bfdbef9fdd2dfeef76d7fb3fffdfeeffcbe6feeffdfb7bb7f7ff6dd37bfdb3fbfedadfe7daefffbe6fbffbffafb7dffeb3fdf59fcfbebfff6ddbfdefff6d7ff2fdb5bfff7d9f7b7eff7ffdbf5fe6dffd2fffff3efeedafd25ffdffedeff3effdfadb7cd7fbfffeddb6bf6df792fffffaeb7c9f7bedfe7deef7efefd7fdb7bafbf7deed7cf7f9edbbcf66bfddbdfedbf7df79bdfb7bb5f77fefd7ffefdf6bbdbffdaef3fbbeb77f7ebaedb5bb5fbfbf7d7ed37ffcfff966d7efefdeff7cf6ebadf3fdffb7e9fef7dfff9bff7ef7fd7ed6ffffbfe9efdbfd7f9e7ffebfff3dda7fa5fbfde7feef77fa6ffd9e7d2cf7fdfdbb7f6fdefdfdfbdfbef76dbdff5be7f7efff9afd7dbffbbddf79fffadbaebfedf6b7ffefdb5ffc9feb6edf7fa6bb5ffff7df67deef7fb7ebfddeddfefb6d7fb3df6ddfdb3ef6edaedfdbf5f75def97ffafdbff7dd76f3cfbfbb7fff976ffed35ffcffd97ffaffb79edf36bf6deffaffecb76df69fffefbe7f3dd7fdffdf5ff5bbffe7feefed9bebfeb7efbedefdfcffdd6fbeedf5bafff7f7fd3cf7fbe5ff6be79effbffbdbb7f779fff6f9bfb36f6fffef77bfdfb5be7faffadbeebf6d77feefff9fdf3ef7e97fd3ffeeffdf7ed3dde7dfcbb6bfefbfdf5daef37fee

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches3 : PLift ((OMA.PrimeProgression.composite primes 13 5051 5740) = mask3) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified3 : PLift (rows3.all (check 5051 5740 mask3 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct3 : ∀ r ∈ rows3, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified3.down r hr
  rw [←maskMatches3.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows4 : List Witness :=
  [(1450,12,146),
  (240,74,26),
  (226,79,25),
  (994,18,99),
  (124,146,14),
  (144,126,15),
  (117,159,9),
  (1356,14,138),
  (1117,17,114),
  (304,64,32),
  (333,59,34),
  (1406,14,144),
  (184,107,20),
  (257,77,27),
  (944,21,96),
  (1324,15,135),
  (197,101,21),
  (624,32,64),
  (1051,19,108),
  (558,36,57),
  (175,115,17),
  (263,77,26),
  (701,29,71),
  (1364,15,138),
  (178,115,17),
  (1140,18,116),
  (574,36,59),
  (414,50,43),
  (266,78,27),
  (771,27,79),
  (446,47,47),
  (450,48,45),
  (946,23,95),
  (1678,13,166),
  (911,24,91),
  (456,48,46),
  (510,43,51),
  (848,26,85),
  (291,76,28),
  (1312,17,128),
  (447,50,45),
  (531,43,54),
  (1907,12,186),
  (1917,12,189),
  (1466,16,144),
  (127,186,14),
  (138,175,12),
  (230,105,19),
  (212,114,18),
  (260,93,22),
  (185,131,15),
  (177,137,14),
  (1755,14,169),
  (988,25,94),
  (634,39,61),
  (604,41,59),
  (200,124,19),
  (861,29,84),
  (225,111,22),
  (385,65,38),
  (334,75,33),
  (783,32,76),
  (318,79,31),
  (375,67,37),
  (1399,18,137),
  (407,62,41),
  (526,48,52),
  (207,122,20),
  (352,72,35),
  (1335,19,131),
  (273,93,27),
  (530,48,53),
  (238,107,23),
  (287,89,29),
  (393,65,40),
  (366,70,37),
  (288,89,29),
  (759,34,74),
  (343,76,35),
  (276,95,28),
  (907,29,89),
  (784,34,77),
  (1590,17,152),
  (161,168,14),
  (1004,27,95),
  (254,113,25),
  (739,39,68),
  (703,41,65),
  (365,79,34),
  (1031,28,95),
  (608,48,56),
  (425,69,39),
  (890,33,82),
  (552,54,52),
  (1504,20,148),
  (290,104,27)]

private def mask4 : ℕ := 0x37fffb6ff679f5f3eff7bbfdffbe6f7ef76f2fded9bff7e9fff7df3dbe5fffffffaff67dffbfff6ffaddf7faff76dff9fcfb7fa7b3dfeef7ff7fff6bb4be79aedfdfaeff7b77bafffdfadf7eff697cfb7be7ffff7ff7dd779fef3fff6dfdde7fafbb7bf6d7cfbf9bfb3ff7fbffd67ffcbb5dffbfff2dfb7fffb7efbcdfddacffe9ffd6df7dffcfb79effacd6fbf4fb4ffffadfaffbdf37bf7f3ff3fdedbb4dff9fedf7bbdbfffffdfddefde7ffeff6ffcff7be4ffdf7fd6edfdff6ff7b7fd3dfa7feebbffffffffa5dffbfeb67dfffb5da7b75ffeb2ff65dfcfffde7b7df6fdbfff6dffbadff7fbef3d9e7beedffbbdbfff7ed6efb7bedb7fffefeff2fdefbbe9ff9feff5ffdf3ff7fdbfd6dfbff3dbeff7ddbdbeeffcbf6b6cff7df7fbf9ffb7ff7dff6bfffe6d7dfafdfdfbffe6fbfdbfffdf37feebfdf7dba7ffed7ffbfdeffbdbb7de797fdfddb7f76f7fbfddf7be6f7db7edecdffbffbf5ffed2efffdfefbfb6fbbff75dfdbfeb7ebfdf67fedf76f7fb2edf59f5b7d9f79affafdbfbf7f76bfcdedffff3fff79eed3fffffbddeff3fdf7ffdf3cf6fbedff5dfebf7f6ed3ff3fbbdfffd7fd6ed67db5f34bfffacfeffb7f7edfff3fff79e7fbff67feefb5fe7bfff6ffeefffdfcb7dbe7ffdfb7dffff7f7f97dfad9fdf7edfedbff65ff6ff79e7f3ef6fbbeff6ff7fecda79b4fbff6edfffb7fbebfdffefaef7fdefb76f76dfdfbddfebbebffd3cfbdfedfb6deefbff65dfdfffbefbafd3fbeff759f6f7efedfe6ffdfe6ffdd7dbbfbf7bf6defd6fbecfb4feffafdffffff36b77f7cff7fb7bb5fef93ffffbb5bbdfffb7cdedff6b7ef7efeffa7fbffbcd7ef7fd3dfefbfdd6ffbef6fbf5fbfbffbeddb7dfff77dfeffdff5fb7bbdfeebffd7f9b7f7d9f7feefbfffefffd77b7fdbf9eff7ebee96ddb7bedfb5f6efadfbffefb3db76beffe5dbefbfb6ed3ff7ffe7b37ffe97ed6fbf4bbcdffbeffefdf7f7eff7ffcfbfdb6f7e9f7bfdffdfecbbfb77f7dfbfdf6f74be79addeffbcff6fefdbffb79bfffed7fd6eff79f6bbcdf7bfdd3f9bffff97fb3dff7bfcfbfb6effefb7be7fb7fffd7dd27df7fbfffebfdf2dfadf3f9f6d7df35fbdb7efeff6eff7fbef75de7fafd7dfb7b7cf7efbfdefbe7ffe9e79eed3ffecbf596fdfffefdf6b74fffdbfd2fffdbbff7fdbdfe5dedbb5fefdbeffd9fff749eff3fd7ddeeff4f76feeffffe7fbf9f697df3dfbeff7fe7dfdf6fffdf37bef9ffd3fffcf7fd76bfef2dbb5ffef7fbbefe7dfeff6bef97edadbeff77d7fb3dfa7dbcfbef76ffcffdbbcffdbeefefd67df7bbcf6ffbfffffedbf6df6f3dffdbedb36f6e92fdf59bffffbf7bbefeddefb7d97ff3fdbf9feffff66bfdfb7faeffdbf7dfff27dfffbdff7fffdadfbfbb7df6fbdf77bffbfeffed7ffef9fcbf7beffadd6dfbebfdd7efbefe5be7fbe9feb6df77beffb7967feefbf9e4fffbff9adf3fdecf37deff7df3dff7f37fef9eefedffcfbcfffd7ef3f9aff7dff7becdb5fedf7cfe

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches4 : PLift ((OMA.PrimeProgression.composite primes 14 8700 8596) = mask4) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified4 : PLift (rows4.all (check 8700 8596 mask4 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct4 : ∀ r ∈ rows4, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified4.down r hr
  rw [←maskMatches4.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows5 : List Witness :=
  [(190,159,17),
  (231,132,23),
  (636,48,62),
  (986,31,96),
  (927,33,91),
  (903,34,89),
  (853,36,83),
  (740,42,72),
  (901,35,88),
  (1263,25,123),
  (860,37,85),
  (597,55,59),
  (236,141,25),
  (222,150,24),
  (615,55,57),
  (1414,24,132),
  (194,177,19),
  (528,66,47),
  (1936,18,180),
  (500,70,46),
  (1670,21,157),
  (1532,23,144),
  (1470,24,138),
  (542,66,53),
  (704,51,68),
  (1278,29,117),
  (248,153,22),
  (578,66,56),
  (682,56,65),
  (445,86,42),
  (618,62,59),
  (575,67,56),
  (363,107,35),
  (1996,20,186),
  (435,93,42),
  (637,64,64),
  (349,117,34),
  (731,56,73),
  (244,170,25),
  (368,113,38),
  (323,129,32),
  (422,99,43),
  (1998,21,185),
  (1088,39,100),
  (1577,27,142),
  (1423,30,129),
  (1298,33,117),
  (373,115,32),
  (1430,30,128),
  (1005,43,90),
  (397,109,35),
  (199,218,18),
  (315,138,29),
  (419,104,40),
  (502,87,46),
  (245,180,23),
  (1299,34,118),
  (942,47,83),
  (540,82,48),
  (1030,43,91),
  (1114,40,101),
  (666,67,60),
  (842,53,76),
  (451,99,40),
  (859,52,76),
  (799,56,71),
  (762,59,67),
  (644,70,57),
  (461,98,41),
  (1992,23,185),
  (997,46,91),
  (1914,24,178),
  (939,49,87),
  (1841,25,171),
  (1842,25,171),
  (1846,25,172),
  (1778,26,165),
  (1494,31,138),
  (1409,33,131),
  (1957,24,181),
  (802,59,75),
  (833,57,79),
  (709,67,67),
  (626,76,59),
  (405,118,37),
  (1544,31,142),
  (1408,34,131),
  (873,55,82),
  (789,61,74),
  (317,152,30),
  (503,96,48),
  (645,75,62),
  (381,127,37),
  (622,78,60),
  (284,171,27),
  (684,71,65)]

private def mask5 : ℕ := 0x5ff5bffbf7defdb79f6ff6fffbaff7ffaeb779f7dbdf7fff5ff7ffffaef67ffff77de7feed7dfbff7d97ef6ffb7fbff7cf6ffedf7fbf4ffddf7f6edff9edfbcf7edeff3fdfff37feeb7efbdbfdbb7d7efbeff5bbfb37df79acdbffbff7c9f7feffaffb7f3df7e97ff7dbf4ffdffffbcfafbfff75fe7dbff6fdfcff6f77b7dfffdf5bf7dfefeffefbfebfefffb2dfff9afbf7b7fffcff7fb6ffeb7ebfdd77bfebf79fffadfbfff7fb6fe6bbddbddfcbf79ffb3fffdfa7b3ffefdbfdefbbeb7cbffdecfbfbf7f7cbffb6fdedffffbcf66ffeff5faeff5f67f3ff2ffecffef7f9fddfffbeb37f67dfefe5dbff7df7ed3ef6f9fdff6ffffeff6f9e7bff977becfb5bfcffffff97df3ffaeff5feeffcdafff6b37bf7dffd3dfbeff7d7ff3eff7befbbfdffd6efedffef3dfefb7ff7fdb7fffd76faedfdbbff7df7edfef3dbe7fff97fd3cff7fe5fbdbf7bbdf6ffbdb76d6fffeff7be7bfcdfef3effddb5bbdfefdfdfbfdfff7cb76bbfdbffe6f7ff7fd7fffdffdfbfdf7deddff9e6bfffe7daffaffbeb3fbf6b7eff79fdbbdffefaef7dbf6b3ffefbfdfff9f7bfcdffb3dffddeffbe9eff6ddfffacff7de7fedfffdeefb5bfffffdbfdbdf7697fffefadbf7ffef6fd6eff7bfdfbcff7d7ddeffb6f7ffffb6fdefdf7f7f9779efd77fafbf7fffdbcff7fe6b3fffedfddffffdbfebeeb7efbddfdbbefeebfef7ddf4ff7df7fbcfafff6b7797ffeefefdb4fbed6efffd7fff7ffd9efdbffffffdf34b77ffdfa7deefbffe6bbdf3fbedf7cd7fdafd67bbdff7fe7fefdffffff7497fb7fff5bfeffdde7f6fd3dbe5fff9ffdfefb7ff6f7efee9bffffffef37feefbdffdfbfb7df7fbbfdfdfbdffebe7dfedefdefb77b76ffcffffadf3ddffd6fdbfbb7bbd976deff67ffeffdf67dffdffdeebf696ed7ff2dbedfbdf6efeede7ff7fbe9f7d6cf7dfeefffdf6f3dfeffa5fbf9f796dfbfbb5bbfbe6fffd77ff6f3ff77bfffb7deeb7ed66d7efffdaff36fefbefdefffcfbcdffdbddfffeff7db7ef2dde7da7f7d9efd7fff5ff6bbfb6ff7fdf7dedbffb7ebefd37dadf7efeebbefffde5ffffff9eff7dbb7fbfbe7beedafbefff4bfffefff5bbffffff6dffdf5bfdff5f76f3ff2fbedbffbff9bfd7fdaeff7f77ffdfaddb7b3cdffbbef77dfdbbdbffbaefffbafbffdf6fbdff79affffdeebfef7dfbcbbf9fed7ddffffef34f77bbdfe5fedfb6b77bfffa7fafff7f6fb7fde5fbeff6defb7dfefbbfbfcf76f2edfd9fcfbdfe6f7ff35fbffffdffffcd3fbffff7f6ffbfd35fafb77dff9beff5db7bf5fffb7ffefdfdbbffefd2ffadbffffef77bbddbfbfcfbf9fffefffdfecfffb76f7efbf9ecb7cf77dadd6ffbfb7fbf7dfef65fe7f74fffd7fdeffb7f3ddefbfefedff7bffd77bfcdedfedffebe6b7cfbdbf7bf7df7f2cfb7deff75f6edbfdeddffbbebeebbdf2fff5fb4f6ff7ffffdbdff79ffb6edfddbef7df77fafff7bf6ffcf7ef6dffdff4bb7b76fbfdefbe7fbdbef9bff65ffefb6fe7fffffdbffffff7ed3fd7ffb4b7cfefffdf3dfafb77dfef7efadbfef3ef6ffedff7ffefb5df7daef67decffebffffdfe7deffb7f7edbff27fefbffdfe9eef77fbdbb6fe7fbfdaf9bfffdb7fb3cfaf9f7fbddfeffdf37bf7bb797ef6cdffbf4fffbef9edf2fffffffd7fb3effdfffb7fd6efbfd7fbb6ffcfe7dbfd3d9eff77bffbfffb5da5f3cd76fefd77fbdbbdd7ffefd6fbf7fb4be7dbdf3ffffbffbeebbcff79fffb6feef3fd7ddbdfb6be7dfcdfd9ffbfdffeb3ffe5daeffdfff96fdbfffdbf7de6feed67ff4ffeb6fbeffe7dbcf7fd66b7dfa7da7fffd6fd7fdef9bdfbf9ff9fef6dda6ffcff6fbddedfffffefeef7ef3fff7fb7fe7fbdf27fefbfeb76feffb7fbdbfe9efd3ff75dffffffffd2effdff5b3efffdaed3dbafff597fb2efe7ffef3dbefb7edfffb6ffdd6ffbfdf79ecf3df76ffddedfffbf6b77dbdf6dbffff7f7f97ef7ddf4ffcff7faffef9ffbfedfeb6fdff9edf7fbe

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches5 : PLift ((OMA.PrimeProgression.composite primes 14 15105 11315) = mask5) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified5 : PLift (rows5.all (check 15105 11315 mask5 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct5 : ∀ r ∈ rows5, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified5.down r hr
  rw [←maskMatches5.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows6 : List Witness :=
  [(369,132,36),
  (617,79,60),
  (588,83,56),
  (1883,26,175),
  (235,209,23),
  (247,199,24),
  (1611,31,148),
  (1515,33,139),
  (1391,36,126),
  (401,125,34),
  (1521,33,139),
  (1570,32,143),
  (1862,27,170),
  (202,249,17),
  (1801,28,164),
  (267,193,25),
  (818,63,75),
  (359,144,32),
  (1331,39,121),
  (1485,35,134),
  (765,68,68),
  (888,59,80),
  (417,126,39),
  (797,66,73),
  (1283,41,117),
  (892,59,81),
  (344,153,32),
  (702,75,65),
  (205,257,20),
  (879,60,80),
  (713,74,65),
  (600,88,56),
  (686,77,63),
  (669,79,62),
  (546,97,51),
  (384,138,35),
  (1153,46,106),
  (295,180,27),
  (1084,49,98),
  (932,57,85),
  (274,194,25),
  (389,137,35),
  (599,89,54),
  (763,70,69),
  (593,91,53),
  (436,124,39),
  (1646,33,156),
  (836,65,79),
  (350,156,30),
  (322,170,28),
  (293,187,25),
  (1415,39,134),
  (720,77,69),
  (711,78,68),
  (913,61,88),
  (900,62,87),
  (963,58,91),
  (1028,55,97),
  (930,61,89),
  (828,69,77),
  (937,61,86),
  (1006,57,92),
  (989,58,90),
  (625,92,58),
  (612,94,57),
  (299,193,29),
  (761,76,70),
  (630,92,59),
  (367,158,34),
  (924,63,83),
  (715,82,65),
  (1729,34,155),
  (307,193,28),
  (815,73,70),
  (1294,46,112),
  (693,86,61),
  (1013,59,87),
  (410,146,35),
  (832,72,72),
  (1547,39,135),
  (687,88,60),
  (1836,33,165),
  (1955,31,174),
  (868,70,75),
  (734,83,63),
  (717,85,61),
  (1672,37,148),
  (303,205,26),
  (1902,33,169),
  (286,224,23),
  (1021,64,92),
  (399,165,34),
  (549,121,52),
  (494,135,47),
  (517,129,49),
  (487,137,46)]

private def mask6 : ℕ := 0x3ff96ffffdeff7fdffbfdfff9feffdf769ffff7bf6fff9f7dfdf6fbfdfffb77dafd65ffef77f7ef7ef7dbedbf4deef7ef7fdfff7fdf7dbef3ddf7b77df6baffedfa6f3ddffbfed7fff7fbf9efdfdf27fe6fbebe7bbfdffdbebb7beff7ffafde5f75fffb6fde7bfefbedfff7cf6fbbebf7ffef7efbfbb7f3fbeeb7ef77ff5bbfdfef7fdaf9f5bfffeeffdfffdfefffdf6bbffbffe5fb7d7fdaeffffbcff6dff9bff7fbf7f74d7fbfefbfbfff3cb67deffb5fafbbdf67f6dd3f9ffbfdfff9efd6dfbef7ebffd7efedfe7bfdffef7fd65ff6fb5de7bfddeffa7f76fffbfdfbd9fef7cdfebfffb7fbcff7f7ffeefefdf4fffb6ebbdf3dfbffffbf7b7ffe7dbfff5feeffffeddfcff5dfffeddbffe7f7e9fff7eff7bf5ffebf6deffbffeffbfb6ffffdaf9fdfb5beefbfdbddedb3fd779fefb59e7bfdfeedbff6dfb5ff5fe7becfbdbb7b7e9f7fafffdbfff7cff7ffeff5fbdbfdb77ffcffffe4f3fff79bfdbffaef7ff77fbdfefbbdf77fefd7ff6fdb7bf6deff7ef6fff6bf6b77fffdbfbfdfffd7fd7dd3ffbffffbf6dbcff7ffcb3dff7fbdfaddffb77d67dbefedfefffddeff6ff6fffeffedffb6fdfdbb7b76d7eb7fdff9b5ffdd7ed7cdffbffbb7fe7f6fd67fffb77feeffddf7ffffbf9efbbff77fffb77d7fdbffffbbdbf4be79fef7fffef7fbf6f2ffaddfdfbdfe79eddb5beffffff7dbefaffffbb7f7efefdeffbdb7effebfdf37ffdbbffff9bef6dff4f36ffffaefafdfef7edffbbfffddfdfffbffbedf77fb5fb7f76ffcd77fe6b7ffefdaff7ffafbff97ed3ff3ddb7bbcdeeffffffbbdff5be79efdfddeeff5b7ef6ede7fecf3edf7d7fdbfba6bbffffffdffffe7f76feedfdf6ddfebffdfef3ff6dfedbffdfffaffe79f7b779f797ffbfbaffffdfff6cfb5daff3f97fbfcf7ffb6bb7d7effdfafff5ff6fe7fbff6ddeffb796effdfb5dafbbdf7ebaffffbb7f7cfff9ffdedff7bfff7efeededfe7f3ffefd7cf77bfcff79f6f7ed77df7bbebf7daffffdadff6defb3cfa7fbfbf7f6e9ffd6dff7b7f9efdbdd7ffaff7cdffbffde5decfbcb7ef6dfbfbbdbbdffeffdf7ffe5fbcfff9eff75feff77be6dbffef9fffb6f7fdfefe5bfcbbfdffb6ed2ddb7ff7ffefadfb7bb4ffd9e7b7ef7fff6fbfdefdfefbf9fff7dfeeffdd27fbff7fff7b7ef2dbfff77f7fdeedffdbeb3ffefbbfd6fdeeffcf7ffaeff7fafffdf76dfdffdbafffdb7fdfcdbfbfcbf5f67fafd2ffeffb6fe6b3ffb5bf7f75dfedeeff7fffbffbefd7df6fbfef77ff7beffe7bb7ffddf7d6ff35bfebbfdf6ffddafdfff7cff6fbffafdadb3e9ffbfcffdff5ffdffefaff75bfebfdbffd7ef7f9e7ffd9fffaefe7be7fbebee9eeff5fffbf5feed6dfbfdfcfb5fe7feffadffdfbef7edbcfb7fb7ffdd7fbffd75bbcfbedefbfffaffbffffd77b3ffffbbef3ff76befdffbecbf7b7fdbfdffbe7b7ff6fbfdfa7feefbfb76ffcf6fde7bf6f7f9fefff9bff75bf7dedfeddbebf7df7faddfd9befbcd66dffdffbe4fbff7fd7fdbf9efbf4bffbedfa7feffffde7d7dfffbaff3edffb7efe7fb7bbdbefffefadfbeff7f7ff7dff5ff7ffd96fffcd7dfbdbfffe7fbfdb7ff5bf5feebbdff5fbcfffd6fdfffbfdb7f35deedeefe5fbcffd9fffefd3d9fff7edfef7ddf5be5ffef67dfdfbfbe5ffdb7ef6ffffde7b37ff7fafd77fafb3f9ff97ff67ff7bfcfeefffdf59bfb3eff7f2edffbefbf69f7b7cfeffb7ffff7fb7cf3dffcbbdf67dadfe7ff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches6 : PLift ((OMA.PrimeProgression.composite primes 14 24354 9882) = mask6) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified6 : PLift (rows6.all (check 24354 9882 mask6 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct6 : ∀ r ∈ rows6, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified6.down r hr
  rw [←maskMatches6.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows7 : List Witness :=
  [(251,268,24),
  (620,109,53),
  (914,74,78),
  (357,190,30),
  (252,270,21),
  (427,160,36),
  (358,191,31),
  (714,98,69),
  (512,137,48),
  (764,92,71),
  (690,102,64),
  (348,203,32),
  (589,121,55),
  (562,127,52),
  (329,217,31),
  (496,144,45),
  (1038,69,93),
  (1994,36,180),
  (719,100,63),
  (654,110,58),
  (1144,63,101),
  (688,105,60),
  (809,90,72),
  (736,99,66),
  (1302,56,114),
  (1017,72,91),
  (582,126,52),
  (573,128,52),
  (1439,51,129),
  (834,88,75),
  (1708,43,152),
  (875,84,79),
  (1472,50,132),
  (846,87,76),
  (866,85,77),
  (1798,41,158),
  (429,172,38),
  (459,161,41),
  (271,273,25),
  (418,178,38),
  (1034,72,92),
  (1020,73,90),
  (678,110,60),
  (957,79,84),
  (485,156,41),
  (371,205,31),
  (1463,52,129),
  (1337,57,118),
  (539,144,46),
  (455,171,37),
  (378,206,31),
  (376,208,31),
  (391,201,33),
  (1295,61,117),
  (919,86,84),
  (1216,65,111),
  (850,93,77),
  (1255,63,115),
  (1236,64,114),
  (1131,70,104),
  (1100,72,101),
  (374,212,34),
  (515,155,48),
  (929,86,85),
  (449,178,41),
  (646,124,61),
  (341,235,33),
  (587,137,54),
  (471,171,44),
  (732,111,65),
  (478,170,43),
  (1695,48,148),
  (1548,53,133),
  (1207,68,104),
  (1054,78,91),
  (936,88,80),
  (555,149,47),
  (466,178,39),
  (1979,42,169),
  (544,153,47),
  (1322,63,113),
  (1984,42,171),
  (918,91,79),
  (1523,55,131),
  (893,94,78),
  (1235,68,109),
  (1359,62,117),
  (454,187,39),
  (894,95,78),
  (372,229,33),
  (1496,57,129),
  (415,206,36),
  (1178,73,103),
  (1379,64,122),
  (332,267,32),
  (328,271,30)]

private def mask7 : ℕ := 0x74bb6b7efedfbffeff76b67f7ef2ffbdffdd7ff6fff7bbffb6fff9add7fbeffffb7ffafde5bfef7ebfeffddf7fbfffddefffdda7ffefbfbf6fffd2ffbdf7eb6e9ffff7fedb77ffeb6efffdbdff59e79bff3f9fffffbf7beefb7ff7f7ed6fdffdfdbbcff7b7fffeff7fedbfcff7dbdf3fdfdffff7e97df7fbafffcfffd2ff67dbffffbffbbddfddf7bf4d7ef7effdbf7fbf976ffdd35bedbf5ff7f6ef37ff7fbdbe7befd7ddbfffffffbbcf2ffb7f74dffd3ffed9bef7eff7b7dfafdb6f77fffbefdeffaeffed7eb7effffbfbf5b6fd7cfb7bfebb6bffbfdfbfdfdbf7b6ef7ff259aff7ff6fbbffffbf4b77fff9fcfffff7ff7bf6ffcdffff5f7eff7ffff3dbfefbffe7fafdf7fffbbffffbeffefdefffeff7d3dfaf9fdf7edffdaefeffbff76bffdfdd7f9feb75dffb3cdeffe5ffcb67f6cff7bbfff7b6fd7fdffdffbf6bf6faffa7ffcf7ff67ffcfef9f5ff7dffbaffe7fbefbddf797fffffeeb76ffefffdf5fbdfbddfebefffffe7ffdf76fbff67feef7ef6efbfdefdeef3e9eff7dfa5fedbb5fffbafd77bfdb7e9fff6effffe7b7ddffffffe7fedfbfffed6cf3ffbefffdfefeddf7fe6ff5f67daffb7feff76bffdfefe5de7f7ffefb3ffe7fbdbffff7d6edef9bfffdf7efbede5bfefbef6fbfdf3dbf7ffdbffffcf3fff7f3fb7ffbdfb7dbeb7fbf6bfcffffefffddfef3ed7fbf5bb6defdbcfbffe7ffcb77fffdfddecf7dde7f7fdb5bfffbff66dfffb7ff5fbfff6fbddf7fafbf7bfeffdfafbffbfcfefbffdef9febbedf7f2ffbffffbfedf7b6ddbd9edffefe7ffdf7ffa7bf7967d7ffbffffbfefeebedd7dffdfb6feff7ff7ffbdf37fffdeffe7db6ff4fff93ff7ffffb7fbf6bbdff59eff3ff76d7cdbfffefffb7efbcf7fff6ffdf6ffadd3dfadf77be7bffffffb7f7cdee97ffe5fbdb3dfe7f7efeddffbfdffebbefbdff4fbed7f9eef77ffffb597edeefffffdbfdfefbbffe7dadf7ff76f3ffffdbdff4feef6fff7dfebf6dff93dd2fbefff7bfeb6cfbfffdfbf9f7b7ed3fbe7bffbefd2cfb7fe6f75fffdeffbdfbff3f9ff9feffdff7fb7f6fbeeffddbdf7d9ef9fdfadfa6fffd7ffedff7dfeffcf76dffd7fff4fbfb6fd3eda7bffbbefffffff25fefbff96ebbef7f9efb7fffefbfff7fb5f7cbf7deefafdeeff5bf7fbcfffbb6ffd976ffddfdffdff5dffffef3fffefbdfee9effafdfdfb6d67ffffbfbb7b7fffeb7fdfdfbdb3fbe7fecfbddf7ffcf7ffbfffdff6ffed6ff6ff7fbafff79f6d6ff3fbfeffdff7bbdfbddfdbbfdfebfff6fff5fbdffefafdefbf5f759f79bff7dbfeb7fd7eb6cdfdbaff3cdffdfdf3fffdbbdd77f6fff7de4fb4ffefbdff5fbebfffeefbeffdbedbf7dfff3edffdb7ff79ffdecf7fbfeb7ebfefeffbfdb7f3fdffd6ff7fbfcbfdd7edbddffbfcff7f779ffdefffdfb7fe6b7dfedfffff4f7fb7fd779ffffddfff2cd7dffeb7fbfff7efeffbeffeb6edffdf7be5fb5ff6fbef37ffdb7ebe6dbddffdffffedffd3cfbdfb7bb7f7fbeefefdf5b3fbef9befeffefff5ffffaefa7fffffdfeeb7fdb5faebf7d6ffeff779f7f3cb77dfffefffdf3ef7edbdff5be7fbfdfebbff67ffcbf6bfff6dfaddffbffdf7b2efbd9edf7ffe6fedff5ff6bfdffefbdd7fff7bf6f779ffd7fffdf7edffdbef6f9bff76ffe9eedf7bb7fb6ffff6df6ffbebfff77b3dff5fedf7eff7f6fffffeeffffeedbfff7dfcff4ff6beffafdafb77d6eb7cf7fffdbfefffd7ff6ddf6fbd9ef97fdaffffbfdd7efffdafbe6fffdeffffd7dfbebffb7fdecfe7fe4f7fffe9bff7ffecf3ebfed7df7fdb5f77f6efeef7d9f6fb6fef9fefbfbfeffd976ffddfdfbfffebffb7cfbdffdff59fef6ef67de7ff5b669effedffcbbebffbfdff5bb5fbdfffbbef7fdfdf7cde7becfbf9bef7cf7eb3fdfffbdfbfbffbeeffdff5bfdf67dfede7fefbbff6f9bff37dedfffbe6ffdffdbafbbfdffbaedfd9fcbf6fe7f2df7fdf6f7dff7b2dfffdfef3fdf7feff3dfa6fbfff7d3ff3ffefb7efeefffdfffbfffeff7ffff27bb5bfdd7ff3ed77ffebfebfffffd3ddbeff69fff7cdfddeffffb6fffcf77bbfff7f7fdeed379fdffffe6ffdfb5fedbbf9f7d7ef7fdbff7efefdffd77bf6f36bff96ffffdeff7fdffbfdfff9feffdf769ffff7bf6fff9f7dfdf6fbfdfffb77dafd65ffef77f7ef7ef7dbedbf4deef7ef7fdfff7fdf7dbef3ddf7b77df6baffedfa6f3ddffbfed7fff7fbf9

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches7 : PLift ((OMA.PrimeProgression.composite primes 14 33634 12563) = mask7) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified7 : PLift (rows7.all (check 33634 12563 mask7 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct7 : ∀ r ∈ rows7, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified7.down r hr
  rw [←maskMatches7.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows8 : List Witness :=
  [(1448,62,130),
  (699,129,60),
  (433,209,36),
  (1519,60,136),
  (1171,78,105),
  (438,210,42),
  (361,256,34),
  (1269,73,114),
  (1237,75,110),
  (553,169,49),
  (1126,83,100),
  (423,222,38),
  (870,108,78),
  (628,150,58),
  (403,234,38),
  (398,237,37),
  (484,195,45),
  (1325,72,114),
  (1737,55,148),
  (476,201,41),
  (738,130,61),
  (568,169,47),
  (584,165,48),
  (1581,61,135),
  (1307,74,112),
  (1844,53,159),
  (1812,54,156),
  (1152,85,99),
  (432,228,38),
  (1540,64,135),
  (1517,65,133),
  (560,177,47),
  (1950,51,167),
  (603,165,52),
  (527,189,45),
  (464,215,39),
  (1724,58,147),
  (1613,62,139),
  (364,275,31),
  (279,368,20),
  (1718,60,146),
  (1012,102,85),
  (434,238,37),
  (551,188,47),
  (951,111,80),
  (1705,62,145),
  (474,227,43),
  (661,163,59),
  (658,164,59),
  (1933,56,165),
  (470,231,42),
  (1229,89,104),
  (1177,93,98),
  (563,195,47),
  (1445,76,122),
  (596,185,51),
  (426,259,36),
  (1270,87,110),
  (953,116,84),
  (1814,61,154),
  (1912,58,163),
  (1340,83,113),
  (1326,84,113),
  (477,234,41),
  (1722,65,146),
  (1978,57,169),
  (1712,66,148),
  (1007,113,85),
  (506,225,43),
  (1524,75,129),
  (1412,81,120),
  (1794,64,153),
  (839,137,72),
  (1644,70,141),
  (1694,68,145),
  (1956,59,168),
  (934,124,79),
  (1507,77,126),
  (440,264,36),
  (727,160,62),
  (1444,81,124),
  (749,157,64),
  (1238,95,107),
  (697,169,59),
  (513,230,40),
  (662,179,55),
  (1925,62,167),
  (716,167,65),
  (564,214,51),
  (788,154,68),
  (1576,77,136),
  (773,157,67),
  (664,183,57),
  (1482,82,127),
  (1599,76,137),
  (966,126,82)]

private def mask8 : ℕ := 0x1b5ffff7efee97df7ffbff77d7fdeff7dff6b759effffd7fba6ffcf7ff7ffffbbdf3effef6dfb5fb5fbdde7daffb7ffff7df7f9efff7fbefb7f77d7dfefdeff75f7fbbfdf79f6bf7fffbbdf2dbbfff7bffbefdf59fff7fff79efffffb7ff5ff6f2cf6fdfebf5bf6bffdefffeffef6ff3efeffafb7df7e9fffffff5f34fffb2dfbffe7f7fbf6f3dfeddbcffef7fdfffffbfebb5bfefbddf7ff7ff7bfebafdf5fffbfe977dbffbdbbfb7dfeef3ffe5ff7bf59f7feef6ddf6bfcbfffbfdf5feffbdff7beedf7fefff7f6effddbfdeff7ef6fffddafdeefffd7f9bef6ddfffbefeef3ff7fbbfff79ffffcf3fdfebffb7fb2efb7fadffffe69ffdfdff4ffdff6d7dff7de4fffb7f9fdfbfdfefbf9e69bdfafff5f3edefbfedfdfbdffffff9ffdffff6f7ef7ffbffa7be7f7cdf6dfddfdbb7fbfb67fbfdffde7b37b6ebfddf5dfffbffffbbcfb7dfdffffefd3ff7f9b6bfefffd2ef3ddefb77d7eb6dfffdf5fbcfeebfcfb7bf6ff5f7fdeedb7dfff77ffefffff5fbeb77dffbfdf7fdbdbfff7ef7ef6fbf5bfffeff6df3dfe6ffedfef3ddeffecfffdefbfcf75fafbf79f7defdff9e7b7cbfededff7fedb3fbfef7efffff7fbcfffbffd7fffef7c9ffdffdadffff75bf7ffcffd9e5fbef76dffffffb7fffd7ed2dfefbfdf7dfe7dfffb5dffbbfd6ebbffef9fdfb7dffb7effffbff76bffb7cf7dfaeff7ffffeffafda7ffd9ffbfcdfdff7fffbeffaddafffff3cbf7feffb7decbffde6ffcfbddbdb7fd6fb3ff67dfdffcffffeddff9efb74ffffffdb5fbffbf9eeffcf7dffefbdde7f7ede7ff5fffb77bbfff7fbcbf6ffebbef6ffa5f77fefdfefeddfdb3ffffdbdf7dfe6ff6ff7ffffefdfffbc9ffdfddf7bf5bf7dffdbdf77beffffbf6befd7fffef3ef77fbdfed9efffff6fdfeffd9fdfff9fff3dd2f9afb77d7ef2cdb7bb7fffbf7f6ffb7fbcbbfdeedffdefdfff3dfffbbff7fffcff6d67b3ff7fdefbf7deff7fde7fb5bfdff7daffff9bebffb7ffbffefbedffdf7edfef3fbaebb7ffeffcf779ecffebe6fedfedffffffb76dfdfffdf7ffedfff7ef77dfebbdfffbafd2fff6bf7ffeffedadffcf7fbefb7edbdfbefb5dfffffdbfdefbf4fe7bfdd3fffdffef7ff3fff7ff7bfcffefaeffdfbfbfeffff3dd3fbe7ffff77ffffedfaffbe96697ddb7facff7de7d2dfbfdf7f7df66bbffbfdfdf7ff77dfdf3fbfffffd7ff6fdffbfcfb69f7f7fffdbfeffdfffbffdbfffcfbcd7ff6cf7fba6bf7b77fbfdefdeef76f7f9bfff7dffbfebf6bfff6ffbff36f7e9bff779b7f7f9effefffddbebf7df6faffffdbefbe97fdffd75feffffbffdafdbfbfff37bff9edff5ffffb7f67b7dffffadf3ffffbeeff5db4bbdfe7f7efff9b7ffedfebfcff7ffefffd6fb7edbdba5bf7b7ff3df3fdfeb7dfffffff7fdfcf7fdeebbdfafbffff7fefffef7fffdfb5df7f6fffdffeff6ff6f6ddefde4f3df7ebffff7bfebffffef3ff7f9efbb5f7fdaff3dffef3f9eef7ffb5df5bffdeef6ff7dfbffbfde7ffcf7d9bef76ffef7efbffbef7fd6797edbdfb4bb7fffdbfd67feef7df7f9fffbffedb7ffffdfdfafbafbf4ffff2ff7fbbeffcff7d7ffffba7f77f7ef6dde5dfeffdd7f9fef7fbfebf7977fbdff7bf5ff6feedefd3dffff7ebefdbff2fdb7f7ff6ffbed7fbfdffffff9fffedfaefffffffeffb5dfdfbfff6bfddfdfeebf7dfffefd7f9efb3ebfefbffefdfcbbefefd7ffb59bfff7fefd3ff65df6ff5befb2efbd9fff7fffff2dfffbf7fff9eededfb7fb5bbfde7d6df2fbfdffcb7f9bfdfffecfb7f7fffffe7dbfbf6d7ef7efeddfdf77fffbefffffe6f7fb7ffbddedfafffdb6ffffdbfba7bb5dffdfefbfff6bbdb67fadd7ffffbb79f79fdf7ffb7ff6fffdefff7fffb75ff7dfdf6dfbfb7fdf7bfcff5ffcfbdbe7f7edb5bbcbfddf7f7ffafdfef36f7effdf67dffffeff6f3effdff5f3ef6ffffd67ff7ff5bef9ffd6dfe7ffdb7efbeda79e5f7fff6f7effdffcbff9efdfefffffdff5f6fbeddffdbff76b6ebfeff7ffdf7edfff3ef65fffbbfbf7dfcffffffb7effff6dfffbfdffd9779fedffff6ff7f7effcfe7ffeb7dfefbfdfaffecfffffffbff2dfb5fffd7edffd75dbdff4feffbdfaffe7bfff77feefbf9bfffd9eebefd37bfefbdfefd3ff379fdf75be7defdbfdeebffdf6b7ff2fff7bbfdff9afd7fbbeff7befdfdd7fbbeffe97ef3edbdfeffbddf7f6fd7dbbdfffb66dfffffbe5bf7be7bbff25feeff7dffdbef7dbffbf6d7edffffffb7fb7de7dfeffdbbfff5bfebfefffbaff7fff79efd37bbdfbdf7ffedde7dfcbf7bfefedf75fffbffb7eb7efe7feffb7fffbeedffdfdf3fdefffedfdbfeb7dff6b6efedff6fffbe69fef7dbfdff7d7ffadd77fe5ffef7fbfff77feeb7ed7f9fffbffefbfcdeef7fff7bbffbc9f7b7ed7ffbeff6bf6fbfdedde7f3cb7e9fefbffe6ffdbfffecfa7feffb7fe7dbffbffbcff7bf7dfdf6ddbdfbdd7f9eeffdff4bfcfffbedffdbb7ffdffff7edffbfeffef6ffecffdfb6ff7d77fffd779e4fbfbff9edffffeff7ff7effcffffa7ff4dee9ffdf79ffff5befb7ffbd9a7ffff7ff3fdffdfef7fbffdecf37ff7bf7feeffff7fbf4bbdbf6ffdff5fbfffed7fd3ff3ddedbbcdfff6fff5bfdffffef9bffafff7bfeb77baddf7dfeffeffefecdfffaefb5ffef3df7f9f7bbeffffeff7fdbdffebef9fdf3dfedb7fdeebeffffdbcf37bffdeddadbfffffdfebafdbfbeefbdd7fdffd75bfcfbdbeef7efffdf7b7ff76daff67dbdf3effef7dff5ba5f77fffdbed6fffef3fbffd7efeffe6bf5dfebadffdff5fbfb7fffcfffbbdbf7be7d3cfefffdbf7f66dbff3fdfff37d6f9fdfefbbffbdf6fffefe7ffeb3dff7f6efeffe7bf5d7fbafde7ba7f7fdffdfcffdffcffdff7f3fdfffffbbff6ffbfd2ffedff6967f7fffddf7ff6dfffeed7dff4ff69e7bfff7ddeff7d9fef6edbfdb7ffffeedfff37bf6ffdbffd2eff7beef3df6efefdbddbcf3ef67d7ffefbe7b7ffffd7ef7d9fff7dbe7d2edadfbfb7efffbfddad9fdfbcbfef7ff75ffdbffdeeffedbffe6b75fefbfffedffebf796ffbdfaffbff77dfeffff77bfff769fffbefefdbfff4bfef7dfadba7fffdffb6ddfffadbbfff6f7fd679e6ffcfe7ffffefdefbbedffdfdfb5bf7ff7f6ef3fdedffffbfdffb6ff3fdf6f7cff7f7fffdfa5f7dfeebfff3fff4bfd9f6ffffeffeef77f77defd35fbdfbff6fdfefe5dbff74d6fb6fd7fdfdbbcdffdfef6f9efbf5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches8 : PLift ((OMA.PrimeProgression.composite primes 15 44888 18273) = mask8) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified8 : PLift (rows8.all (check 44888 18273 mask8 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct8 : ∀ r ∈ rows8, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified8.down r hr
  rw [←maskMatches8.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows9 : List Witness :=
  [(1242,98,106),
  (330,370,28),
  (1288,95,110),
  (1188,103,101),
  (651,188,56),
  (586,209,50),
  (1319,93,112),
  (858,143,73),
  (1227,100,105),
  (909,135,78),
  (1980,62,169),
  (841,146,72),
  (1949,63,166),
  (1890,65,161),
  (768,160,65),
  (754,163,64),
  (707,174,60),
  (1172,105,100),
  (899,137,77),
  (1839,67,157),
  (922,134,79),
  (847,146,72),
  (871,142,74),
  (923,134,78),
  (865,143,74),
  (457,271,38),
  (532,233,45),
  (649,191,55),
  (335,371,29),
  (336,372,28),
  (380,329,33),
  (556,225,49),
  (561,223,49),
  (309,405,27),
  (495,253,42),
  (1151,109,97),
  (1022,123,87),
  (1057,119,89),
  (906,139,76),
  (794,160,69),
  (743,171,65),
  (753,169,67),
  (590,216,53),
  (559,228,51),
  (538,237,49),
  (1681,76,143),
  (595,215,52),
  (579,221,51),
  (1629,79,138),
  (1195,108,100),
  (1113,116,93),
  (1009,128,84),
  (979,132,81),
  (851,152,71),
  (886,146,74),
  (780,166,65),
  (864,150,70),
  (712,183,59),
  (577,226,47),
  (751,175,65),
  (897,148,74),
  (522,255,42),
  (514,259,41),
  (689,197,59),
  (653,209,56),
  (933,147,78),
  (869,158,73),
  (541,256,44),
  (685,203,59),
  (679,205,59),
  (1132,123,99),
  (1056,132,91),
  (1025,136,88),
  (483,289,42),
  (1027,138,82),
  (776,183,61),
  (744,191,58),
  (718,198,56),
  (677,210,52),
  (983,145,79),
  (830,172,65),
  (823,174,67),
  (806,178,67),
  (534,269,42),
  (710,203,60),
  (1676,86,142),
  (1388,104,115),
  (1625,89,138),
  (1096,132,92),
  (1434,101,121),
  (567,256,48),
  (1938,75,166),
  (217,672,18),
  (1642,89,140),
  (876,167,72),
  (1244,119,109)]

private def mask9 : ℕ := 0x3fffebefdedbb7f76dff96ff6fbafb76f77f6dff7fadffede7fefd3fffdfbdbfed2ffefbeff36beffbfff7fffb3ff7e9fcf7d9fffbdf6eb3effdfb7ffedf79ffdffbf7bffff7bfffb5fe5f7ddfef6fdbffbfffdd7edbfd2fffdfb7fe7dffffddfcb36bffbfdff7ff7b36f6efbfff7bbff3fbf7fbcf6ffb6ffcf7ff7dff5deff3e9ffbffffffe5ff7ff7f3dde79fdb3fff7fbfd37dbeb7fdeef7efbdfefb3dffefefdef9bdffd9e7deef2ffb6f7edfffaefe5bbff7fb66ffefbffbcff7f7fd3dfe7fe5ffdb7fbfff6ffefb7ebeff7cfbfdeff75f6fdbff77ffcffdfffb7effd9bff7e977f7fff7dbcffffeefeffbffefbfdffffbfd6fff7f7db76bbfd7dfedfbf9efdfefadffdf7ed6ffefdfdbffb3fff7badfbffb6f7ddf6b7fdeffe6f3eff7f7df3fff7bb7bffdfcff7fe5bffbeefaffe7fffbb6bf7dbffbdfedffdfeff2effddffbb7feff7fd7d9bfffefffbefdbdfecfbdf7ff6ef37fbffbdfeef6dfefbfeffeff6fefd37fbcf3fd7f97efe7ffdbfdfefffed7ddffb7cbfff3edfd9feff6bfff3efbffe5f7e9efdedd77bbdbfddeffbefffff5fb7f76ffff6dfbfbffff6fbeff7fedff6def9ffdedbfef7eff797fffddefbffdf6f6dfb7deefffd77ffeff7fadbb7fe7ffdfbf9fef7df7e9ffd7ffeeff7d77bfdf6dbfdff7ffe93ff7fffdfff9effedfefdfeb7fb7fffefff9bffff96ededf7fffdfbddf7deefe7fefbbfbfe9fdfbddacfb6f6ff7ff6fbf7ffeffebffff5bfcbb5ffffeffbfdfebff97efffdefffffffbe6b7ef7fff5bff97ffafff7de7f7cffeffdf3ffbfbffff79bcfeddb5bbffefffefeffb6ff7defbefffddffbffdfffeddb7fadfbcdfff7df3fff6bbddf7dfdff79feb7ef7fffdde7faff77bfe9bfff7de7bbcd7ebeed6fbf7fffdf7bfcf3fbfeff5ffef6fff7dbfffdd6ff6edbfbbcfbdfe7fafff7bf6ffdb6ffbfdfffedbffff7bfefa7fe5ffcd7efeff6f9fef3efffb2fd7fde7b77b7ffecfedbffffebfeb7fd35bfeff7df6faffbfbedfbef6fdedfb5dfdff7dffffcfafffffbdd6f9ffd7fbf6f77deffedfefbf7ffdb77bbedbfbfcffff77becff7ff7bffdeed7ff3fdedfbeb7f9bfd6ffacb7fb7ffbffff9f7bbfffef3eff7df7fffbefffffbddffbf6ff6b7edffbeeffcbfff7ff75fffff5fefdaefbfdf6b35f7ffedfaffeef3fb7fd3efe7fefbf5dffb7fff59fffbede7f6fd7ffb6ffcdf6fbfffddbdffef6edfcffffa7fbfd7ff7dfb7ffdbf7b77ffff6fdbdffeb7edfffbfdf7f76ffed6ffefdb5fb5be7fbfdffdbff7dff7baddbffb5f7cfff9efffffefffd976f7cdfffffbb5fe7bbffe7fffbbf9f6dfcfe7fffb3ffefd3ffefdf6b75deff3ddedfeebf4bf6fbddaddedffebefdefdbdfafbf7ff6ffdf6ffe7bf7b7effff3ffffbbf9f6dfff77befffdf6ffefdf59febffdef9efdad9aef7dffeffdfbfde4fbf97fb7cffdfa7fbdfeff2dfbfbfef3ebeeffdff7dfefbeff7b7ef3ddeffffd7ff2effdfb7b7cfffdfefbffbef7ff77f2efffdfffbe96ffffffffb5fbfdfff6ffbf9fff35be6dfffe5fedbf7f76dfdfb7bbffbfffe9aff6ddbfffdbe7d7efffdffffebfef7dfe7bfefbfffef6cfb7fafbbf9fffefdf7dfcffdff6fbfff5dffbf7d77ffcfbd9fdff4deefbffefbf5fbebfffaedbdfaff7dbfeffeff5ba7fbfdfedffd37fbfbffffff2cf7fbe6bbdf6fdedd75fefffff6e97df77fefffcfefb7fdf5bf7f3fbf7d7fdbdbafffdffebedfbffadfffdf79fff7fbfffbdf66dfef67ffefbcffffefd37dedf7f96fdfdfff9f7b7fdeffbfdffdf6bbcfff9adfefffef76ffffaddafff7f3fdeef7fff7fedfbf9efffdd7fbfdf3ff6ebefffdffffffbf7f3efb5ff5fbffffbfff6dbffb359e7ffef7ffb7f76bffb6efbddfdf3dff797edbfff5ffdf66fbfdf79fdf7ff7fdbff7ddafb77f6ff7fff5dbfbfcfeedfffefbffff7bffb6efafdf7fffdfff3cffdfa6fffbf69eef37feebb5ff7f3ff7fbf6fffbfe9afdfffecfbeb7fbffffd9bfbb7fefbefdf7bb4f3dde7f7fdffdbebfe9f6fffffdbe7ffeffef6ed3ffeeff5dfff7cfff9effb6b6fbedfe7dafbffd67dbdff5fbfbfcfeef3efefdb7ffd9f7ffffedfbeffeff6ffdff7bbfffeb77b6ff3dffeff7f76decdf79edbb6fff9add7ffeefbff7edbffedffdff5ffef7fdf7bfeb3edef9bff3dfefff6ff6f7fdff9fff7e9ffffeffdbedff7bffffff37df5ffffeffadd6fdbdf77ffefbdfe7bfdfffd6ffeff65bbebf7beffeffffdeebf6d7fffdfbfba5f7dffeffddf5ff7bfdf7fdadd67bffff5fee9bff3dffdffffeef7cfbffbdb7ed7ed7ef779f6bfedffffdf7dfe7bffdfefbedfddf5f7fbf7bfdd7dfeeff7de7dafdfffeef7cb6efffdeffefbf7d67ffdfffde7bffffedffd7fdbcb3dbf7fafd6fdafff7bfffbffbdbfcfbfbfebedf7dfa7ffffffd7cd3ffecb7efff9fdfefdbcf7fb76f3ffbdff7ffffeffaed6ffbef77dffdffdeffaebf7d7ffeffa5df6ffef6efedf7fbbcfff97fdefd67dffbbdb77daff2fffeff7d7fbfef7fdefbb7dffbffdfdbbff76ff7bfdfbdbfff76bf7bbfff5fe6fbdb77ffefbfbbcffdfeefffde7ffff3cff7faffedfecbbedfeb7ffff9a7ff7f7fd3ff7fdb5f7fdf793ffedfe7f7eff7fbefe79a6f7ebffd7cfb7beffb7f7ef7fffffe7ff7fffdb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches9 : PLift ((OMA.PrimeProgression.composite primes 14 60858 15026) = mask9) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified9 : PLift (rows9.all (check 60858 15026 mask9 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct9 : ∀ r ∈ rows9, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified9.down r hr
  rw [←maskMatches9.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows10 : List Witness :=
  [(505,297,43),
  (838,181,70),
  (1265,120,105),
  (1370,111,114),
  (511,298,42),
  (803,190,66),
  (816,187,68),
  (614,249,50),
  (638,240,52),
  (1225,125,100),
  (1964,78,160),
  (631,243,53),
  (1704,90,140),
  (1300,118,109),
  (882,174,73),
  (656,234,54),
  (1348,114,111),
  (1166,132,98),
  (632,244,53),
  (1655,94,135),
  (1840,85,152),
  (1682,93,139),
  (1721,91,144),
  (1668,94,139),
  (1404,112,115),
  (611,258,48),
  (1584,100,131),
  (1368,116,113),
  (840,190,71),
  (1566,102,131),
  (1175,136,96),
  (1045,153,86),
  (1304,123,109),
  (737,218,61),
  (1362,118,112),
  (999,161,81),
  (969,166,79),
  (822,196,67),
  (926,174,76),
  (921,175,75),
  (1719,94,139),
  (1701,96,137),
  (1960,85,164),
  (1892,89,158),
  (1534,110,129),
  (439,386,39),
  (319,532,28),
  (1068,160,89),
  (342,500,28),
  (486,353,42),
  (787,219,65),
  (1793,99,149),
  (605,295,56),
  (633,282,58),
  (1394,130,116),
  (960,189,81),
  (955,190,81),
  (400,454,36),
  (1002,182,84),
  (1382,132,117),
  (652,280,54),
  (554,330,45),
  (488,375,39),
  (609,301,51),
  (448,410,36),
  (659,280,58),
  (915,202,80),
  (387,486,31),
  (1183,159,97),
  (1800,105,148),
  (1767,107,145),
  (800,237,64),
  (607,314,51),
  (619,308,51),
  (844,226,71),
  (1109,172,94),
  (536,357,46),
  (855,224,73),
  (1023,188,84),
  (1499,129,122),
  (948,204,77),
  (1899,102,154),
  (837,233,69),
  (692,282,55),
  (583,335,46),
  (941,208,79),
  (1058,185,89),
  (1316,149,108),
  (294,667,22),
  (1334,147,109),
  (1211,162,99),
  (1182,166,96),
  (777,253,65),
  (1245,158,103),
  (462,426,39),
  (760,259,64)]

private def mask10 : ℕ := 0x2dfffb7f9eedbdf6fff5ff7f7fdafff7bb6fb7fefdfffbffbff75b76bfffb7ffcf7dff7d7fdffbecbbfb7ff3cf77ff7bb5f7fdfdfe7fbfbbfffeffcf2fff5bfdf6ebfedfdfb7f77ff7fedfbfffebf7dfff3ffffdbff7fff797dffdff6bb7977ffcffffeef34b6fffff77ffdfbfdf7f7efb5fbdfb5feff7fd7ffbefbd9ff9efd7dbf7ffcf7ef7dff5fe6f7f9ffd7edfffefbfdf6ef7ffafbf5ffffe69efdb7dfcbfffffdbffaffedbb7dfff3ef6dffeb7fdf79ffd3fbeff7efffbffdf7fafffd9e7becfffbe5fb5d7ef7dfafffff3ef7edfdf6dfafff7bf6f3fff7fffbbedffb3fdfdbf7fbffe7fbefbddefb7f97efffdfdfaff7d9febfcffdfedfbdffffeefffff6ffebef9bffbfffff76d67bfeffdbffb77feeb7ffedbf4bfffe7b6fdafdbfffff77fadff7ba4ffdf6fdfefffffffb7dffffcfbfbf5fbdf7efefdb7dfffb79f7bbfff5bedf7dffed7ffe5ff6b7fbf7dbfd2fdbfffdd7efffdfdbeeffc9ffbeed7fffebfdff6d6ffa7bedbffff7fbdf7ffbfb7effebbffefbfdffff6ff7ffefdffffcbffbfffedfefbfddffb7ddaf9f7ffef7ef7effdba7ffffeed3cfb7ffcfb5feedbdfaffbffbfbf7ffefa5ff5fbddfff6fdffdbeb77bfff6cdbdff7bffdfeffdfafffff7d9fef6edffffdff7f6efbfd6fbe6f7dfeedfff2dfedbf7f6fbbdfbddb7ffff7fdefffd9f4f7e9efd6ef7ffe7fff9fffbffbfbb5ffe9fe9effffbaefb5ffff2fdf7dfdf77b6ffffdaddfdbbff77f7ff7fbaffffdffd2ffe7bbdffcfffdeed7d9f7ffedffbfefe7bf4fbcf6ff6cd37ffdfffffff7cffffe7f7ffe7daffffdfdf7f97ebfef7fbf7bb6dffdfefffffff75de7fbffeddbebf6bf6b7fffd9efffcf77b7fdbfba5fffb76feffffbfffffff6faff3dfeef77d7efbdf6ffffbffdffbeff77ff5fffbeffafffddb7b7cff7f7dfb5fecfffb7f9fffbdfbdff7d6ffbddeffe5fb7bffbeff6ddfcfb6bff97dfb79f7f74f7ffaffffbf4fbdbffbeff7f9efbffffffedfe7fe6fbfbffd7cdbfbfeffd97ef2fff7befbf7ff7baddb5ffdff7df6ffefefffdbbffeef7efedbf7b7dff7bbfdedbaef77df7fffffddeefbeb7ffefffffffffdd6ffefdefbfeb7cf7edbdfeffbfff6ffefbfff7befbfddef93fffdffdfbefeff6fffd9bff77b77f6edb7de7fffbffd7fffdfa6ff5d6effcd2fbfef74ff6feff6fffffbefffdfff6d9eff7ffffb7fde5fbdbfcdf7bbfd3fdeff7e9f7fbffffffff3dfefdfeffdbe7fffbffdbcfefbedbbcfeffaffe5dfffb6b7ffbff75fadbf6fef9affedfb5ff5ff7f3cdfddffbf4f7efaede5ffef7fdffb7ff3dbacbbffeedefff7dfff7ffe6bfffafdaeffeffef7dfffdb7b75f6effef7d9b6ffedff97ff3ddffff79ffbfefed9bfffff7ff7fdb7bbdbfdfe7f2ff3fff6bb7ffedbff3dfbfb7ff77ffff7fbf5f7dfefb3eff7bfefbcdffd7fdfdbffb77f7ebbfdaffecfbdbff9efff5bffffdbf7dfffe7fffff4f6effdffdffeff6d67ffffaf9a7bb7def9ffffddb5f7dbf79ecf6ffafbffffefbffbfbfffbffe7feefb5fbffbfdf7d7fd37fedbfef6fbfddefdedffeffff3dfb7fe5f3ef7eb6eff7df7fbdbf7f2fdefbb7ffcffff7cdffdf7fbfdfeb7ff77fe7bbfde6facf7ffe7b7cfe7dfdfbdfbebb7be7f3fffdffdffcf7e9bef75bfdffcfffbfef2ffffff5f7ef7cffffe7fbfdf79efff7ffffff97ed7fdeffecf37bffdfdfeffffb7f9ffbbefe7ffffbdffffeffefbffbfffef97edff9fefffdffbeffbfdb7fffff6fecdffbb6ff7bffdfedffbeef7ef6fdaff37fafb37defffcff7ff7ffff7fd3fdeffbfb3ddf7d2efedda7fffff7f6cdb7fefffdb7f9ffd3fbe6ff7bfef3cdefdfdbbff7ebbddf5dfebf79f7dbffb5fffb7ddfef7fd6fffdb7fbffbaef6fff6f75dfffefdffbecf7cb77d7edffbe5bb7dffd7ffffff4f7fffebedd65ffeb3ff6ff7df37dffb3ff7ed7fff79fdbfedf7ffcf3fbbfbfebf7fbdfbdfbcffcfff9fdff7fefbf5bf7d6fd2fffff3fbefdaffe7fafffffef9fffbffbff7dffff7edffbfdb76ffff2df7ffafffef7ebfdfefdf7fbfb67fffdbfffebf5defffffeffecbfdb7ffbfda7fafbfff77ffef3d9e7ff6dfff3effdffef7dfe79bfdfd9f6f7cb77fecfffbe5f7dbf7d6fd35faffffdfededdb7beff37ff6ffff37fbcb7f97ff3efe7de7fbdf6ff7ededdfefff9ff97ffafdeebf7bf7f3dff7ffdfffbfebfedf7fbdbf7feef3fff7dfdbfdbefdedfffdfeffffffffdf7ffbff3cdffbffdef9fffbfbe7deddfdfeeffddffbffda7df7f7fbffb7ed7dbf5fbfbe7fffdbfffeb7cf7efbfdbfdffbfef67fbef77fa7f7fdffdfff7ddb7f7fdef9adf3ffe7bf7d77fffdeddf6ffedefbeefbffa5fff9f7f6efaf9eebfdf7fbffdf7daefffd6ef7ffff9ffffffff9effffdf4ff6bf7ffef3f9b7ffdd7fffefb7fedfbf9ffb6dd7fffdfffffedaed7fdffb7efffbbdff5dffb77b76f7efaddbdf77dff9eff7fffff369efbffdfdbbef76f7ebfefeffa5fbfde7d6ffbfff5fbdff7fadf77fffffef76dfff75dbeffebeeb7ffe5ffdfb6f7fb3edf5df7fffbefb7cf7dffef74ff7beffe7fbffffdf7dfedffbbcff7ffeffef27ffefffbef9ffd2fdbfbfffefd7ffb7fefb77f6edefd77ff5b3ddfffadf7fdffb76ff6ffeffdbe7ffdb7ef7ffb7ffdff5be6f2dfbffedfbebf6bafdbddefbffdfefbcff7fb7bfddfefafffdbb5fb5fe7ffefedbb7ffdb77f3fdffdfcf7ed77b6ffbfbbfbf7feeffdd6fbf7ffeff7bffd77fafb36ffeffef67fe7fbfd7fbbff7fbf5fbcbf7ffef2fbf7fffb7ff7cdbfdbefffffeffdf77fb6fb7f7fd7ffef9f7f3ffffbfddaffeef7fb67f7ff7fbffff6feefffdf5dbdbfefefd7ffffbbfbfdff6faffeddbdffefeff7fffdbeebb79ffffff77fe6fbeff7fbffedfbff769efd7fffffb7f7ffeefbff65dbdbf7dffffcf7d9ffffcdf7ffddfdbf5fbdfff96efb5bfebb7977feedbfdfefbdffffadd27fbfbbf9ffffcfeffbdfbcf7efaed65ffeb7fdffffffbfbf7ffdf76b7ffed9fffbf977f7efbdfefbfdbf7dafffffeff7fbfefaddfffbff7edefffdfadff7ff5f6fbfefffdfff349fff6fdffff6f7cff7b3ddafbfffbdb76dffffdbafbfdbefd3fdbffffbf5feeffddf7ffdfffbf6bfef35ffff3effef7ffffbfdf7ffff9bdf7fdfebffbf7fedfedfbdffe97fbedf7fffeff7bffdbff2f9edffef6edfdff7deefbefe7b3ff77bbdffcfffd7fd7fbf6fbfbefd2cdfffffbfddfefbcdb7feeffddeff7dd7fff7fb7dfed6ddf7ffdb7fbffdfffa5dffff7f66f7ffafbf7b7cfffffef6ffbefb7de7faff3ddfffff9fffecfeddfcffef7fdedf77fedbbd9fffaefff9eebf5beedbff77dbef77f7ed7ff2dfedff7f6fbfedff9fffbfbfffffd3ddb6ffddf7fffffffbffbdfefbfedffff6bbfb67deffe7bfff35fffbbffbffacf779e7dfffeffeff3efefbbfd67fbeb7ebfffbcdffffebfef7effcdefdbff7ebffd7dff7fffbbdd7efffdbfbedbb7f77dfdf3fffdffebfe9fdff7df5bfddffd3efef9f7b7dbe79ecfefbafff7dfffeefe7ffdf7fbf6defdbdfbffb5ffffffdefbf7b7fbf6bfdffdffcb37ff7f3ef77fe7ffff6ffbefff9f5fb7fefb2ed6ffe7f7ed7ef2ffff9b7ffdfe6f7cff7faeff5b7fdbdfafdfff7cf7fbbfdbffffff6bf7b3ef35ffffb7f7fb7effffb5ff7dffbfdfafdfff7ebf6ffffefbf6f3cfefffeffffb7bf7d6fdbddafbf7bbeff7ffff6fdefbf7fee9bdf7ffbdffddfef2ff77dfff7f9f7f7fffdbffbfdf76bbffffbfcffed77defff5bbdfb7fe7feedf7ffffbcff79efffffeef3fbfeb7ff6dff7ff4feff7ffef9ffb7ebef93edaf9e6bfdd7effddbfdbff7fd67dfedbffeebff9fff7cfbfffff77b7f9fdfffdfdbbebee9beff7baff75f7fffeff7bfcbfefffdfcfffffef76ff7beffffde5f7cf7ffffffdbeebbdff7fbcff7feebffffffffff7ffcbff9e7f7df75fb5ffedee9eed7fbb5ffedf7b7cf7dfe7f7ddfff7ddeffbdfbe96ffffdbdfaeffdfeffbef67bfeb77f7fbfffa7dffbfef76fbdffffb5bfff7ed3ff77fbfbbcff7f6fdaffeef7cffeffcdff9ecfffbfeffddbffeffbfb77fefd7fbedf77bef9effafdfcfff9ff97ffbfbf7b36d7efefff5bffff4df7f3ff3dbfff7ff7fffffeddadfbfdf7ffff77fbebfdffedffd679efbfdf76dedf3ffeefb7b7fb7ffb59efbffffffbffffbf5ff6ff7d2efffffff75dffb6cfffde7fbff6e97cf7fbb7bf7ff6dffff7bf7f3db7f9fffaffecfbfdffffcfe7da7bf5d7effffffbf5bfeff7bbededdbfffeffefbfde5fbff3cf7effff3ffe7ffd97efbff37ff5fbebe7fffd7dfbdb76feedbff2dfedf75f6edeefedbfeff5bffdbcffdfa7fffbf7b7fda5ffdf7dfe6d7dff7ffeffff67fefd3f9efb3fff7bedd67dffbf6fffdbef3ffbff7ef7fffef7fff6bfcbefbbfdedfb7ff7fffbafdb7fa5fffbf6ffcfbffffbbf966d7ff7fbfeffef66deddf7ffef77

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches10 : PLift ((OMA.PrimeProgression.composite primes 15 74993 25230) = mask10) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified10 : PLift (rows10.all (check 74993 25230 mask10 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct10 : ∀ r ∈ rows10, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified10.down r hr
  rw [←maskMatches10.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows11 : List Witness :=
  [(581,339,50),
  (616,320,53),
  (411,480,35),
  (460,429,39),
  (591,334,48),
  (857,231,69),
  (1040,191,82),
  (1929,103,154),
  (458,435,37),
  (1935,103,155),
  (1954,102,157),
  (1115,180,90),
  (889,226,72),
  (623,324,49),
  (1122,180,88),
  (1052,192,82),
  (1218,166,96),
  (1383,147,113),
  (757,269,60),
  (747,273,60),
  (592,345,48),
  (497,411,41),
  (1662,123,140),
  (1033,198,86),
  (1289,159,109),
  (728,282,61),
  (1369,150,116),
  (1276,161,107),
  (967,213,82),
  (1044,198,89),
  (1193,174,101),
  (1206,173,101),
  (1147,182,96),
  (1518,139,121),
  (1735,122,135),
  (1784,119,140),
  (1930,110,151),
  (671,317,54),
  (694,308,55),
  (1944,110,156),
  (621,346,45),
  (1660,130,135),
  (1711,127,143),
  (1461,149,121),
  (750,291,63),
  (1046,209,89),
  (340,643,29),
  (947,231,79),
  (1064,207,88),
  (1085,203,90),
  (1421,155,116),
  (691,319,56),
  (1918,115,156),
  (1212,182,98),
  (791,279,65),
  (724,305,59),
  (1250,177,101),
  (1258,176,103),
  (1744,127,142),
  (1641,135,134),
  (708,313,58),
  (1139,195,93),
  (1939,115,158),
  (1597,140,127),
  (722,310,60),
  (1365,164,109),
  (431,520,36),
  (1675,134,137),
  (1167,193,94),
  (683,331,53),
  (642,353,52),
  (1220,189,93),
  (1723,134,132),
  (1791,129,137),
  (1179,196,90),
  (635,364,48),
  (1086,213,84),
  (949,244,72),
  (1173,198,90),
  (493,472,36),
  (1372,170,107),
  (480,486,37),
  (1296,180,101),
  (1150,203,89),
  (1541,152,121),
  (1204,195,94),
  (1249,189,99),
  (1411,168,113),
  (1318,180,105),
  (1089,218,86),
  (805,295,65),
  (1931,123,157),
  (1653,144,136),
  (1689,141,139),
  (452,527,37),
  (1740,137,141)]

private def mask11 : ℕ := 0xf96ffefdb6bfff76bbffa7bfcf7ff7ff7fff7bffff5ff6dfedbfff6bbefe7bbdfafffff7fdf7bfdfffff5f7ff7ed7ffffdb7bbdbffdfcfeffeebfdf76bafdf7ffff7fbe7bfdd7dfa6ffdbf6fedfbffeffbfff6fafdfdffebff9efdfef7fbbdfbcfffffefef9bdf7dde7d7fdadbf7ff6d7ef3dfffdf7f7fd77d7dd7fffcbbff67f6ffa7feffb7befbbffe7ffcff6b6ef7dff79affbff7ff6efffbf7bffbf79bcfbdfbfbfff76f7ffefdbcfbdbefbfdfbffedff5b77dbffbfdfef77f779fdff7fffbb7df6ffffafbffffddfe9bff7fff5f74fffffedbffaff7ddfebbefefde4ffed77fefdbdfaffffbf6fecdf7ff5ff5ffefedfe7deff7ffeef7dfbddf7bf5d6fbfefffbfef36fff97ffbdfafffef7ef7dda7ffeffdd7fdeff7fff6fbfbffd6fff7ff7fb5fe7fefd3fdbebbffefbbff7dfe5fb7deefeef7dffff7fbffdfcf7fdfeb77df7f6ffbffacffddeedfdffdbf7bb7b6ffbdd37bfffb5be7ffff37deebfe977ffeff7bfdbfcdfffbfff7bf5fbebffdbcdefffff7df7ffbddfdffffbff7fdffffffeeffdbeff7df6fbf5b7effefefdffdbcb76fffffcfe5fbdffddfef3fffdfffbbe9e79ffffffb7ff59ffbeeded9feffdbefdfeffffbdfbff77d7ff37beffbff77daffffdadffeb7ffbfff7de7ffff7ef7eff5ff7bb7bfffaffbfdf7f7ff77fbcfb7feffff9fe97fff5ffdffdff6f3ffffbf6f7eff6fafd6ffadffff67ffffbffeffbefff9fefefffcf7fdf7fadf7ffffb7ddffbeddfffa5fbcf67dfdfbdfbffb7d7effcd77beffb7b6efffdefdbffbfbf79fdffd9e7f7dffed2fff7fffff7feff3dd3ffb6f7dff7fedda5bf6fbddeff7edfdffdfbff7ef7efff9fcb7ffe7fbdfbffffffeff7d7ffeffa5fb7feffaef77fffb3ffffbfefbffffbf4f7fffdfadbe5ffebf7dfdf77bfeff7be7f3ffafffdf3fffffbfffdffcffeff7dbdfb7bb7ff5deffeffe7bfff3dfefb7fdefbf7b7fd7fbffdefdf7ffcdf6fecff7bf5bffbffd7ffffdffffef7f9fdfeffefbb7de6ffcffffb5ffff6fd7fd7fbbfb7dfe7d3ef7fdfffffff7bbffbfbfdf7f977bfdd75fafff7be7f3fde7defffdf779fddbfdafb3ffeff7ffbffeffffdff9fff7dfbef7cfe7feef7f9affffdfef3efeddf7ffd96ff7ef7ffbdff7b7fffdfbfff4f7dfffdbff75faff7fffe97efaf9f7f37deefeff6dbbdfbffffb6fdbdbeebf5f7ffefdff9fcfbcffff6fffffe6bfdbf7facd67df7b75befffff35fbef37fee9fef7ddf7fbdffef7ed6ffbff77fefbffdfdba7bf6bf7bbdfafdb5fffbefffffbdffdfb7fe6ffede7bf4fbdb6fbfff2ffbfb7e9fedfffbfff7bfcdeedaff7fdfcb3fff7baddfd9efff7ff6fadff59feffedfef7dd3fbffffdd7ef6ffbfbefff7bfebefff5ffffffbfebfeffdfffbbfffff7ef7ddbff779ff9fcdafbe6ffe9f7faefe5dbff7df76deddfffffff5fefdedfe7df7f3ef76dfdfe7faefffbffdfdff7fffff6ffed3fff7ffdff4bf7b6efefbffffedffb6edb7beefffdfe9fdff7ff5ff79fedfefbf9f7bfeffedffdfdffef7efe7b7efffbadff5f7ff7fffdfb6fb6fefb3df7ffeff7dff7bbefff9e7f3fbeffeedf7fffbbd9eff3effffe5fb5bf7fafff5fffff79fe93fffdde7ff6fefd2ffffff4bb7bf7bfef3dbffbf7ffefeeff5feef3edefb7fff7fbfbffdf7f6efb7dfdbbfffebeddf7dedffff7efbdfedbedfb7feffffd77ff7bb5dffdbdf6fbeebfedfebfcfefbfff3ef6edfdf7ffedffdfe7f7fffffecb37ffffbff2dffff7efe7dfffafbfffbefff97effdfbefb7fe7b7fdffbf6ffcdf6f7ddafdb4fbcd7ffffff7fafff5f7ff3cfbfde7f7cf7edbdf6fffdbf6fe7f7ff65dbffffdfedfff7fdf5ffdbefdfffaffb7f7dbfffbffbfdfdfbdf6f9eedb7faffbff7fffff2fffcf3ef7e9fffeddfcfb7d779fffa7bfffbfdfeffeff5fb7bffbffdeed2dfffb7cbfff3fdfdbf7fbcfffbeefb7bb7fff9e6ffffffff7b77feffbdf6ddecbff9f7ffffffbb5b3df7ffbfffffbfffd9f7d2ef2f9fefffd7eb7dfbdffefbdf6ed7fffffbffbdbf6f6efe7ffff3ff7ffbdd77faeb7fb7fdbdf7fffdffefffbeedf5bfdfffffff6ffff9afff4df6f2dfb7feef7fd77b7ef3dff4bbfd6fdfed3ffe7fbdb77defffdfadbf7dffd7dfaffe7fbedeeffffe7bbebffdfff6fffdfefff7bf7f6ddf7dbef7cfee9fcdfdbfdffff7efeed6fdefbf7fefbefd37ffebfedef97df77dfff3fd6ebfff7f9b7bf4fefbbddbffffffff77ffefedfbff7fdffb6dfb5ff4bbff7ffbfdff9efffebff9bffffdeffb7ffefbdffddb7bfed6fdbfdffdffffcbe7ffff3fdefff6ff7bbcfbdfe4f7cbf69ffff7fbefb5f67ffedbfffeb7ffefbeffedffcf7fb7fdfff379ffbfddefbffdf59feb77df7f7ff7fba6ffef7ffecfe7ffdfbfbefffdff7bfebfd9ffdfef3ffefff5ffefedfffdbfbbfb76d7dff7bffbf7ffff3ff6fdf6fbdbfff6ddedffebffd7efefdfffa6ffdbfffefffdfbdfffdefd6fdf79f5ffeff6bbff67fefbbeff6fbef7ffffb75feef3fdffff7bf7dffffffedff7ff5ffeffddfdfaff7ed7f97dd7fbadfffdfed6df77ff5fbffe7fbdf3ddfcfb6df6ffff77bbdf7ffffbefdffdfdbfd9ffbefdfdbaffffd7fb7dde7be5fbebfe97ef7fbf6ffdf7edbff77ffff7ef6effffffdeebf79f7bfffafdbdfffdefdbefffff7b77fe7beef7dfe6ff7b7fb6edefbbffbd9f7fedf7dffdfb5ff7dbefffffdbb6fee9fddbdffef7efffffffffbfdb3fdfedfffeddbebfffffdbff7dbb7bf5dfff7efeffffffebeffffd7dfe5ff7f6ffbddbfdfeffeff7bfffbfdeffb797fffcf2ddffffedefbafffdbf5f7f9eff2fd7fdffbf79f7f7fffd9bffbefeedffdfffaffbdbf6feddf7ff6f3cbf6deffe7fefffebfed3cf7fff7ffff6ff7ede5bfffbebf7d7cdfffbeffddf6bffff7dfdf7dfe7ffffbffb5ffdd6fdbffbfbf4f7ffe7dffd3fdfdbf6f6ebfefe5fafbf5d7ebafff7fbfb7ddffd6df6fde7bfff7ffadfbf9aefbfd7ff7ff3dbf7fbdf77f3ffbf9e5fb7bf7feffb7deef7ffeefbdf2dfb7b7dfff96efedbbcfbdbf7dffdfffeff77ff7bbffa7ffcfff97fdfcfbfffdbfff77dfff7fdeeffcf7edefff5feff3effeffef679affb4feeffefe5df7ffebf7bfdd3fbbff76b7fbffffd9eef7dffedeefbffecbff97edbddfffffbbff7efbdf3ffedff7fe7bfff67bbdfbdffebfedf5bfcb3ede7b6fdeffeeffed7ff3cffdbb7fbefe7dfff35fefffdf6effff6fbfebbebfeffffe7dbdb3ef77fffffd9b5ff5fffbfffffdfffffde7d7fdafffff77f77fbedbdbf7ffd977f7eff5bffff5de6f7cfafbedb74ffefffdffffcbbfd76dbefe7bf5b3effefffd7fff7bf6ffff7fd7fffeff7ffff2dfeddf5fbfff6beef7dfb5bf7beed2ff37fffbfdf77defffdfbfbf79efdfdfb7baff76fefb7fde7dffff5bffdfddafff7f7cffffbfda7bfff3fbf7dfff7dffeff7be7d7fdbfffeb3ff6ffbfd35fffbfed66ffcf779fffffdfefffffffbcf76bffdbfffddf7ff5b77becfedffef3effebefdffbe7fbf96fffffefffffb4befdefff7dedfbfdffffffff9eff3cffed3fde79fcb3fbf7ffefedba7ff7bfffbffbffffffedf7f6df7dbb7fbf9efdfef3fdfeff6ff7feffa5fafbffbf7dbff3dbbff7ef7fbfef7ffbef7ffefffededbfebf5f7fbfcfbfffdf7dfefd7fffffe6fbdf7fd3eff7bfebfdbeedefd75faeffff7e93efb5be7bf7dffbbfdedbbffb7df7baffbdfffb7c9feffcfbffbcfbfff7feeffdff6fffd7effcdefff5f7dfe7dbffeffefb7fd7f97dffffe7fb5def9bfdffff7bbddffffddefdeff7eff7ffefb5daffffffefffdfdbfdbfff6ff3ddb7bedffebfefeffb5ffef76df6ffdfbfff7ff7feeb6ed7fff6fff9efbfefaffbff7d977f6ffe79eeffef76beffbfbfcff7f77fffdff9e5ffeb7fbedd7fdbfbf6feeffeffdbf7fffd7efbffe7ffffb7fefffef2fbffbfed76f2efff9ffffdde696dffffeefffbf7fbefefdf6bf7bf6bfdfeffafff7df7b3ff3dfafb7efff9efdefbfebfcdeff3ffafdbfffdf7fbeddefff5f7ebffffcd3dfb6fbf97fffffb7ff5ffdb76fbffe7dedbffd6ffbef3ffa7f7dfefdfff7ffbeff5fffb3cf7d9fff7cbf6bafdefbf5ffffe7defdbfbedbf5ffef7ede7ffe

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches11 : PLift ((OMA.PrimeProgression.composite primes 15 98480 23320) = mask11) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified11 : PLift (rows11.all (check 98480 23320 mask11 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct11 : ∀ r ∈ rows11, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified11.down r hr
  rw [←maskMatches11.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows12 : List Witness :=
  [(1871,128,154),
  (580,417,47),
  (1805,134,146),
  (1509,161,122),
  (657,370,55),
  (1010,242,82),
  (1015,241,82),
  (1516,162,126),
  (1396,176,116),
  (1223,201,101),
  (1217,202,101),
  (1514,165,120),
  (655,391,49),
  (1657,155,130),
  (1095,235,87),
  (1866,138,145),
  (1626,159,127),
  (972,266,76),
  (1377,188,105),
  (1075,241,82),
  (1825,142,143),
  (1143,227,88),
  (674,385,52),
  (991,262,76),
  (804,323,60),
  (920,283,72),
  (1471,177,116),
  (812,321,62),
  (984,265,77),
  (752,347,58),
  (1347,194,108),
  (469,558,36),
  (1650,159,133),
  (1528,172,123),
  (1163,226,94),
  (745,354,60),
  (883,299,70),
  (917,288,73),
  (1989,134,165),
  (1853,144,155),
  (1451,184,120),
  (1458,184,117),
  (1595,172,127),
  (1542,179,121),
  (1076,257,83),
  (735,377,56),
  (1726,162,141),
  (472,595,41),
  (360,784,28),
  (721,396,54),
  (1345,214,108),
  (705,410,58),
  (545,532,46),
  (770,378,59),
  (1168,250,89),
  (1059,276,82),
  (1293,227,99),
  (543,541,43),
  (1282,230,99),
  (1190,248,91),
  (852,347,67),
  (1488,199,114),
  (801,372,61),
  (854,349,65),
  (881,344,74),
  (726,418,63),
  (769,395,63),
  (565,538,49),
  (1202,253,99),
  (786,388,64),
  (723,422,59),
  (1495,205,116),
  (1538,200,116),
  (1539,200,119),
  (1077,287,83),
  (1116,277,86),
  (1112,278,86),
  (1108,280,86),
  (1433,218,115),
  (729,431,57),
  (1261,250,104),
  (1256,251,103),
  (896,352,74),
  (1733,182,145),
  (1947,162,161),
  (862,366,71),
  (781,404,65),
  (1067,296,88),
  (1103,287,93),
  (993,319,84),
  (1032,307,86),
  (977,325,83),
  (1062,299,90),
  (1605,198,131),
  (975,326,81),
  (978,325,81)]

private def mask12 : ℕ := 0x7f379f7befd6fbffff5ffebeedbfffff3df77fffff7be5bbfbfeffcfffdfff3ebf6dedf3ffaef77fef9ffff7beffffd7eb2ff7fdffb77bef9fff7fbf7f7cdfefecfedffffbffff9fedfdfbdbf7d77fbcd67befffff77dbfd6dfedff7fffbfdfaffb7b7ef7fffffef9f5f7dfffdbdd6fbfff7ff77fbffefdb7fbcf7fdfcff7ffcffdbeefffdb7feff7efef9effffdefbf79fe9fff3fdafffdffeb3ff6dbfcff6be7dfcfefbb7ffed77fafdfffeff3cdfffffdbdfa7ffdd66ffff7fff6f3ef7fdbff77dedbbfbe6dfdf75fffb75f6effef7fdffbf7deff7ef7dfa7bfebffbaefb5ffeffdfffbfff35fecff7feef6cfefbfff36ffefbdd37fbefbffefbbef3fffdff7ffedefdf7df5ffefff9efd6f9e6f7df7ebfcdf79beffef7fd7ffbffffff7f6fd7cd3fffcff7f7ffeff75fffbb69fff3cfb7bbff77dfffaef65ffdbfdffff7cdffdbfb7ddf7ffdde7fb4fffff796fffdfefbbddf7fffdfffe7b77f7fbbddf7ffeb7eff7d7df7f9b7ffcfeef6ef6ffffbf4deff3efafbffff6d7fffdffd9bff3fbf7b7fdf7fbdff5feffadff7dfcff5beebeffefdbffbef7edfdfa7ffdffef6fbefffddbcffedffbfddffdfff75ffff2dfb7ffdf7ebf6bfef75fe6bffbefdbcfbfbe7fbebefbfffefffefbed7ff7ff6f9ffffff7fb6fdfddf7bff9ffb7ffaffb7bf7ff7ffdffdfb7ffcdefdffd75fbffffdefd7fd37beffb7f7efedffdfbeff7f67ffff37defffdfffd2fd6ddbffbfbe7feefadfffbf5ffffbfda59eefbf9efbeed7ffaffbfffff6fdff9f6b7dff7bbff3fdbdbb7d6eb7ffbdfffb7ffffffef7dbbff779efdaefedfeeffdd7ffffde5fa7fbff6fffffb7fedfbdd7ff2cfffdf7ff6fe7ffff7fdbfbf6f7fb3ff2fffdff4fefb3fde7ff7bbffffbfdffdfb6bf7dfeb7dfe7fecfbf9eebecd3fffeffffefdbede7ff5f37f7ffbfdb7fffffefef9ffffdbf5f7ffff96ffe7ff4bfdbffffedfffe6b7cbffffffeffb7ffdf7effdf7dbedff59f7ffffbfffdbb6bfefefdf7dffffffeedbefbdfeffbfd7ffbedfdbfff35fefbbdffdba6f7ebfff7fdfdffff7ed76dffff5beeff5f76f7ffbfdfcbffbfeffddefffdb37fffdbeffffe7b7fd6fffedfd9fffbeffffecfffdffbfe9fff7dfbf9efffedfedfffb5fffbb7ff7f6df7f9fcff7be7baffafffdf7fd77ffffa7fafb3ddeff7ffeffb7bfedef9fdd7fdffb7d977bffff7da5ffdf7ffecffdfaefffbeffffdefbfeff7fe7fbffbdfaff7ef679bcffdff7bf7dfff7ff7ffb5b379fff7efffdbffffffebaefbdbbefffdefdefdfffefffdff7f7dfe7dfdf76fffffff7ffbff7f97fbfdf65feffb6ffff6edf7ffef7fdfff7ef3fbf6ffcffffbedad9bdffffef9fcdfdfeeff79f7dfffe7deff7fffe9bff6fdbdb7eb7f9befffbfdfbdf7fd3efffbbdffffff9efdffbafb77df6f6ffb79f7fbef779fcfffbffff5b77ffefe7fe7bbdbefffddfffeefb7df7ffdffdfb7bffffedaef7fbfdff7de7b3ff3ffffff7ff6fbddafbfdf7fbeffeed37feeff596ffeede7defffefefdffdb7defffffffd7df67bbffbff7eb2ffff9fefb6bffd2fd7dfe7f7fb7fbbddb7dedfbff7ff7ddf7fefbfffe6fafdb7beebfcff6bedfe7fbdbbfdfff3ff7fdbfff6dfeffede7ff7ffddef97ef6fbafbf7ff7fedfbdfeff7dff7defdffbf7fbfd7ef7cd7ffe5ffcbfedbdfe5defffe9feb7fff7beffbcd6ffafdeddb5f7effffefffdfffb75ff7fecfeffaffbd977b6cf7fbf6fb7dfefedda7ffef7df77dffdf7ffeff7f7fbfefad9b5f7fffedffdffdfdfbedf7fffffffefbfcf76fbfffdbbff3f97ff7fdf7ffffffbffffef27dfffb7b7edaffbdffcf7fbfebfff65ffff77feebeedfddfef74fffffdfffba7f75f7fb7edffbfcfbf9f7f7fffdff4bfddfff2ff6fbf5fffff6fedf7dfbfbfeb6effcffffafbbedfff3ef7ddfebb5be7ffddedbe7f77ffeb3efbfffff7c9eff7ff75fbfbfff7fd7dd3f9ffbfff76bbffe5ffdf3eff7bfefefffdff6f7ef6eff7bbffb7deffafdffff7ffedffb7ddf79fcf7fbfff6fdfffe7ffdf6efbff27ff7ffcfeebfdd3ffafb7ff6ffbff7ffbfb7ddffdeffeddf7ff5bff9edf6ffffff6ffffeffffbb6ffcfe7feff3ffbdfbf967dfdff7bf6fb5ff7ffffefffdbffdffdfcf7ffaffb5f7fd7fdffbf7bf79efdfcf2ffffffdb7ff7edf7bbff3fd7effdff5faefffbeeffcfafdffbfff77dfddffdfefb6b6fbbfffffbdfb7f6f9eff7fbfdb7edf7ffffbffefff6d7efffff7feef7fbfefefd7dbefff5fffd3cfffbeef3fffffffde5dfebff97ebbcf6ffb5fb7dffdffff59fcb7fff797ef2fffebffffffeededfffffdf76bfcdbfbbeff7ff7feefbfdfdf7ff6fdedfeffbef36fffb3ff27bb5b7dfffdeef77ff7ff5bfff7ffffffef7fd7efbffaffffffdfe6bedffdffdbffbf6ffddb7df7bfdfe7dfffeffedf7ffe6ffef2fff7b3dffe9ffd77fb7fbdfffbbed6dbbeb7fdfff7ffefde6fbfffffffdf7fedfbdff7dbff77ffdb77ffedaff27fafbbfd6fd7df7f9e7bbfd7ff7fffddbdfb7be7b7ffbfbffffdbfff3fff5ffdf7fb7fbfedbfbfebfddf6fafd7ffffff7fffdffdeddbef7fbf7ffffb7deff7ffffb2ffffbb6ffcbff9fedfddb6f7fffffbffefdaffffbefbfff7dfeebfdf6efeff6fff7b37bf6dbfff5ffeffebefbbdfbffadb3dfefdfffefbf5f77ff7bbfdfdfeef77ffff3ffbdbbffff9e7beffbdbffbf5dfffffdff9f7bbebfebefff7dfff77f6ffbcfbfbe7ffdfffffed7ddfefb7deffefd3fdffffe977bedfffdb7f7ebfffeef77fa7ff7ffed3efbfffcbffb76dfdd7fffdffeff7bbff3dbfdf7ff6ffefff5bffb34fffd2dfaffffbfd97fbeefe7ff4fbdff6f7ef75ff7bfffffffedefdeefb7feffaff6dffdffef66d3df7dfb7b7effffeeff7db4bfffffbfdd7fbb6bfffffbefdbfff5fbebf7f7fff7fefbb7bf7f6ffbfbeefb7ff7beddeffacfffbfebbcff79e7f35fffd7ef679feb3dbffdfcfedfffbff9f6f6fdfffb7f7f9fffeed7fba7fffffff6df77de7ffdbefdbffedfbdfb7fe7bfffadfbdffef6fdfed779ffffefffbfefbfbafff7f7ffeffffdbeffff7ed6cfffbbefb7fffdfdfffbeef3ffffbfdfbfdffbbeffff3dffffefbffffed7fffdbb6ffede7bedf2fdfff7db77baffbddb7ffcf7ffffd7dbbfffff7fffffefdfff7fbefbedde7fbef76f7effdfefdaff3fffed3ff6fdb5bbcbffdbdfafbe7fffbfffbeffffedfffff7ffddfffefff7ffef3edffdeebf4ffebeffffffff7ffe7d7ffffbb5bbfdef9effedbfcf3f9f7ffef2fdbebfeffeb6dfefbffffeffff7ffbfbe4fffdffdbff77dfef7dfe6fbdf77feff77f7fbfefbfff7bfcfeffeff67db5ff6ff792cdfdbeeffcdfef7ffe5fbef7df6f9fedbdff7fb7b7fdeefbfbfff7fbff9bfda5ffef7fbe6bfcfb7fbdffcdeff7fdffdfebbefffbfffef9ffb7eb76ffcdffbfeffef7fbfff37fe6ff59fefbff77be7ff7f7fffddbffeffffffff7efbdffffffd7ef3fd7fdbeb7cbf7ffdffdfe6f7ebf7ffffa5feefbfd7edfefbffa7fffffed6dd37bffffeff7bedd7fffffffb6ffbff7dfa7f36fffbfffe5df6fffbe7bbffffff7bf7f7ff2cff7dbfffddeebfdf7dfb4fffb7fdeef2fff5b76f6fdeff3fffdfb796fd3efff9fdb3dd7fbfffffffff35ffffbfdafdf6bfedf6ffcdedff7f3ff76ffdfbfffefb7bfef7ffbfdf5bbdb6ebefd77dfdbfedffffcf77fefb74feeffff7dfb5b37fef9affeddf7ff7dffffcffffbff7cf6ff6ffbffadfb5f77d7ffffdeeff4fffbbffb7faef7ef7fbbff6fffdff6f7ff6ffffdf6f7fdff9fef7fdeebfdb7ef6dfa7bfdf7ffe7ffddf7bb7bffffefeefb7ffffbfffffbddfddbfff6d67bfffefff7fb7f6ffbfffdfffb37de7dfedfdda6ffff7ef3ffbfbe7f7fdf7d6cff7bfcbb7ffff2cf7fdffbffbfedffdedfeefffff7bbffadde7f7efff97fd77ff7f77defbeff6fffefffff7f6cdffdf7fbfbfe9fffb5bffff7d7ff6fd3fffcbfcf7f9fdfefdbdffffff9bdffffbdfffdffbaff6f9f7f76bfff6edbffffffcf7ef7dfffbf5ffefeebfef3dbfdfbff76d2ffff9f5ffdfefdfffe7fffbb7ff69bffafff7bf5f7fdbed7fffefbf9f7d6fd7ffbfbfed77bfeff5bbff7effeffdd7ffe4bfdd77dbedff9ecb7efefffffbdfbfff7b7ffbef77dffbbedeff7ff679bffb7deff7cfff9a7ff5ff6bfdfbfdfcfbdfffb7dffdff6ff7f66dfcfffff5ffdb77dffdeffbeb77dffbfeff5bb5b3edffd6fff7dfdf3ebf7dbfffdfeff75fffffefbffeff7e9eff7fdffffebbfbfffbfdb7dfdbf7be7deddfddfcbf7befbbffefdf7bfdd7ff3ef6f9feffefffdbfdbdfbfffdf77befffffbcfbebefffeff7ff6bf7ffefeffeffffffff77bffde7fecf3fbfeffffedbffbbfd7edffded9f5fbffe7b3df7ffb7b77f77f7fffffa7ffede7feff3ffbdffddfffbfdffbf5fbcbffdfffbffafff6d77f3ef65bafbfdf7f96eff5ffcf35dfffbdffffbfffdbf7bfcdffbe7ffdf77f6ff7dbaefbfd7fdfcfeffedff7bfffedf3fdfdbff9febfffbf9edf77dffbfefefff5b7fbffffef2fbbef7edfffaedfffe7fbeff7defdfdbbdfffb6efeddefdffffdfeefbff37ffcfbeff7bbef7ddbff7dfeed6fde5df7fbfbfff3ddbfbf7ffddfff6edf5df7f3ffe7b6eff7ff5bf79effeffe7dffb3ffefdbffeddfdffed77ffdfffffff75fefbbfd6fbfdff7deff6ffbfdbeff5f76ffffefbfef3dbfe96fff7bb7bfffeffedfb79eefb4f7ffbdfbffeffb6fe7b7ff2fdafffef6ebefdffbfcff49ffb2df3dfaefffbfffbfdbffb7fffbffdecf3dbb7ffdff7fffdfffffff7ffffeddf5fbfbffd77bfdfeffbdfffdffb7edfffbdffffe7fbefed9b7bf6ffebfddb7bfdfbcf66ffff35be5bbf9eedbefb7bfcb7ebe7bfdf67dbcf3fbfefbffbd9ffb7dffe9efd6dff7ff59fffefffffefbfeff6f6dfadfb6fbcdffd7ff3fbfebfff77ffff77be4b77f6efffd7dffffbffefffcf3ffe7ffedeffbef67fbfffe9efbbff7fbffff6ff6feefb7dacffd97f97edfdffebfffefffdde7bf6f7db7fdbffbddefb37fffffffff9b7ffdd6fd3ffe7fbdf7ddffd6fd7fbffffcbfeffffa7be6f7ff7effedb7bedbff9f7ffffbfbf5b7efe7bfdf7fdaef7fff79fdfe5dedbb5dfffeffffdfdb7dfe7faff6ffe7ffff7ff7fdbfffdf7fdf6b7ddffbedfb7ffffbdfffde7ffcb7efbddf7dbff3fb7ff7ffa7bb7f3dfef97edfd9fdffffe7feedfffffbfed7ffbcfb7fb6ffebe6f7cfffffdbb7de7d7efffffdff7b7e9eff7dfaef77d7fffef77bedb77f7ff7efffbffbbefffbafdbffbfffdf7ff3fffd9bdfbebeffecdfdbffbf7f7ef3ff67beffbdffeffdf75feff3edeef7fff7bbfb7effedfffe5db6f37ff7bfcffdff7ff69f7ffffbfff6ffff7ff7ff75fbebfdfeedeffefffcb7dfeedafdbffedfbffffd7df65ff7fbdffedeedffbfef7fdefb7fffffe7ffff7ffbefb79fdf7e9f7d7ef77bfefffbf6f2effffe7f7fbeedffdaffffb7fd7fbfeffdbaff35f7fffedfdbbeffc9f7dffdffdefbfffffb7fff7fa6f3ddfffefff7feeffff7ff6cde7ff7fb6bffdffffdffebb7beff3dff7fbdbfedefdefd759fdff6fffdedfbddffffd9ffbbdfbd9ffffdfefbfffb7ffffbd9eff6ed37ffcffdfffffffefdeef76d77bfff3fff7f7ff7fdfedfddfdff6befd6dfafdffb7697ffbedf7df6ffdd7fbfedbfbb5fbfbfefecf3fdfdbffbeeffdfbffbebf7d769bfffdbfff75ffe9bffedffeff7bf792ffbffffb77fffffdfa5fe7f7eff7dfdff7ffeffdff7f2efefdf5bfff67fbdfe7dfef7eb6ef7ef7f9fffbedeffbfdfddbfbbfbfffefdffbf7bfddfff3efafffff7fbe7ffdfbfffcffdf7ffbdd7ffedfbcf6ffbffbfdadf3ffeff7ffe7fedfbeffedbff7ffffffddf79bedfdfaebffbf7feefe79fffbe9efdffd3dff7bbdd67fffdffff5bf7bfebfff7ddaebfebff9fdff7ffdb75f7e9efdffdbfff7defbfefeffffffd977feefa79bffbeb6fdefdb7fadff5f7ededd7fbe7f7df76beffe5ffdf76bfedbcfefdffff5f7fd7ffeffffbfeff7ffcfffbf7bffb7fb6effffefffdde7feeffffa7bfdfefdbff7fffdf7fb67dbfd6dfeff3eff79bff75fbfff5def9eedf7bbfbf7fe7fbdf2ffa6fffb7ef6dffdbbefbff76d6fffdbe6fb7fefdfffefff5fbffffffff2ffbffb7feff7effffbdff5dffbeff67db6bbffff96ffffdf6ffed7ebfdffdffeffed7fb7ff7fbbffbffeff6edf7deef77ff7fbfd6ffadbffbfef7efefbadb75ffffbff7ffffbbebeff7cffd9ffbf6b77fafde7feff3ffeffefffdbffbf7bf7f3cfffff6ff5b76fbddadffdb3effedfff6dffdffed7ff2ffe79fcb7cdf7b7ffbfdf6f74dfefffdefde5f3fff7ffeff5fbebbfb76deffe79f6fb7b6efffdffdffff7ffff7ffff9effffdeef7edffffeff7fffdbff7ddbffffff7ffefedffdfbfdfefecdb5fb7fbf97fd7fdf7ffef74bfedfdfbfdfdfbef6ff7ffb7df7ffff7eb7fdff9bebf4ffff7ef2d9ffbf6f7ffbefb7ff7ffebfebedf7dbffff797fd6ef7fdffbfefffdbdfffffffb79779bdf7dbbfbb5ffebefd7dbfdffefe7dbefaddefff6bffbffdafbf6f7ff6fbfdfb7ffdbbd9ffdefdf7ffcfbcf6ffaff3fdefb76deefbff27fffbf5ffefbef6ffb7fbf9f7fbcf7fdefb7e9ffffcfeffa4f7dffedfcf7fbffff7df6fbefe7bedff4fffbbff7fdeefb7feef7ffffbffffdf7e9ffff7ff6ffddffdacd6ddeffffff6fecdedbafffddfe9fedffbfcbff977feefbfdf5f3effebfff7fffdf7fdefb7ef3ffefb7fd6ff6ededfb7f7f9e7feffeffefffedffb2fdffbfff3cfeff7cfffbfffb7df6dbfd77ffcf7fbf79bffe5ffcfffb66fbffa7fffbfcd7fb7ffffdfebfddf7badffffefff69ffbfcffdff5f7fff6b7ffbffffbf5ffffaefaf9fcbffbffdbff6dfbef77d7f9fff2fdfdbb7f6edfeffdfbef76dffb7dd6f9f7b7dbfef2dfffbb5ffcff7feff3dbeefbfd7ffffdefbedfbfbfeffdfb7feff76df7bfef7dbefffffff93ffe7ff5f77bff96ffefdb6bfff76bbffa7bfcf7ff7ff7fff7bffff5ff6dfedbfff6bbefe7bbdfafffff7fdf7bfdfffff5f7ff7ed7ffffdb7bbdbffdfcfeffeebfdf76bafdf7ffff7fbe7bfdd7dfa6ffdbf6fedfbffeffbfff6fafdfdffebff9efdfef7fbbdfbcfffffefef9bdf7dde7d7fdadbf7ff6d7ef3dfffdf7f7fd77d7dd7fffcbbff67f6ffa7feffb7befbbffe7ffcff6b6ef7dff79affbff7ff6efffbf7bffbf79bcfbdfbfbfff76f7ffefdbcfbdbefbfdfbffedff5b77dbffbfdfef77f779fdff7fffbb7df6ffffafbffffddfe9bff7fff5f74fffffedbffaff7ddfebbefefde4ffed77fefdbdfaffffbf6fecdf7ff5ff5ffefedfe7deff7ffeef7dfbddf7bf5d6fbfe

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches12 : PLift ((OMA.PrimeProgression.composite primes 16 119744 41559) = mask12) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified12 : PLift (rows12.all (check 119744 41559 mask12 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct12 : ∀ r ∈ rows12, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified12.down r hr
  rw [←maskMatches12.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows13 : List Witness :=
  [(807,394,69),
  (660,482,57),
  (569,560,50),
  (767,417,62),
  (1425,225,112),
  (1248,257,97),
  (808,397,63),
  (796,403,63),
  (733,438,58),
  (1608,200,127),
  (492,655,37),
  (1738,186,140),
  (523,620,45),
  (1827,178,145),
  (817,404,65),
  (610,542,49),
  (1511,219,117),
  (1392,238,109),
  (1073,309,83),
  (1588,209,124),
  (1545,215,121),
  (1464,227,113),
  (1305,255,103),
  (971,343,76),
  (863,386,68),
  (1371,243,108),
  (1104,302,87),
  (1863,179,146),
  (1380,242,108),
  (1506,222,121),
  (1301,257,104),
  (1267,264,102),
  (1530,219,119),
  (696,484,55),
  (1037,326,79),
  (829,408,62),
  (1833,185,142),
  (1750,194,137),
  (1180,288,92),
  (1453,234,117),
  (790,431,63),
  (1456,234,116),
  (585,583,46),
  (1673,204,131),
  (1251,273,98),
  (1568,218,124),
  (1036,330,82),
  (1900,180,149),
  (1880,182,148),
  (1306,262,102),
  (1876,183,149),
  (1999,172,157),
  (1943,177,153),
  (1821,189,145),
  (1679,205,133),
  (1582,219,123),
  (821,422,64),
  (1274,272,99),
  (1520,228,119),
  (695,500,56),
  (670,519,53),
  (1633,213,130),
  (1279,272,101),
  (742,469,58),
  (1024,340,81),
  (1666,209,133),
  (970,359,77),
  (1924,181,152),
  (1417,246,112),
  (1441,242,114),
  (1357,257,108),
  (1395,250,111),
  (1848,189,149),
  (1407,249,115),
  (1483,237,119),
  (1185,297,95),
  (1748,203,133),
  (529,675,42),
  (904,395,74),
  (547,657,37),
  (1575,229,123),
  (1352,267,107),
  (1039,348,82),
  (1669,217,133),
  (1820,199,145),
  (1685,215,136),
  (1481,245,121),
  (843,431,69),
  (1594,228,128),
  (1560,233,126),
  (867,420,70),
  (1091,334,88),
  (1102,331,87),
  (825,443,67),
  (1314,280,92),
  (598,618,44)]

private def mask13 : ℕ := 0xdbb6ffff7fbffffdfeffbfff6ffedbdfffbf7df7fffd7fbeeff6fffdfff2ffedf37deebbdffd9f5bf7fef9ffde7bfffbebe7dfff3fffffffff7ffeffdbacffff7ff7ddfffeffffbfff6ede7ffefb5b7ffbdfbddfeff7b6efbcfa7befbf7fffffffffffff7edffd6edffdefbf7dfefbdfb5ffdf7db6ebfcfbfff5ff7f7ffbdd37ffcffffefbbff6fffdf3ef7ffffff7ff5fbfffffaff7fffffbcfffffddffbeff77bf6f6ffffbf6f7dffed7effdfe6bffff6f6ffffff7bbffefbfddfdffdfff9e6f7ffeddf7ffdffff2fdffdf5fbffefbbddbfbfeff6bfffbefffdafffebfff6edfffbcbfff77fbfd77df6bbdb7fbeff77fffffff77ffff7fdafbf5deebfff75bfefb7defbefdef9f7f77b7ff7cfb7beff7fff7d7ffbfff6ffdf7fffdd3fff5f3fbe7bedf77fbffbe9ffdfff7fdfdb3ed7ef6fdf7fb7b7ddf7b3df7fbfebffffff6dde5fb7ffffeffeedfffffbffd6fdfefa7fe5fbdf7effffa7dfdbf6f77bfefb5bedf74dffb6ffedff7ff7fe7b7dfefdfff75ffeffffffbe7ffdf6fb7ef3fffffbdbf7ffcfbfbfebfcf7fdafd3fdecb7fdfeb3fffddf7ff6ffed3fffd9feff7dffb7efbddefbfdff6ffeff5fb5fbfdfedfcf7fbadff7ff7ffdffffecbbff7fbaff7dfbfb7edfefbffe5fbdfbffefbafdedbfdfb7ff7d7ddef9febffdfef7fdafbfff7cffeffed7fffebffff7deef37ff6f7cfefffdd7fdefff6d6ffbefffbb7fbffffbbff75db6f75bffdbdfeffe6fff97fb2cfefdf5ffff67dffffdbeffb7d67ffeffffffb3eb7f9fffaddfcf7efeedfffafbfffffdffffed67fb7bf7fffdffd7ffeff7ddffffdfffffdfbdbe7befdf5bb5bb7ff6f3dfffff5f77befdfdfadfffbb7df7b3ffbffbdfb6dfefeef67ff4fffbfffeed3fdbfbfebfffeefef9b7ffffffdfdf77bbebbfdf6faddf79ffff7b67deddfffeefffd7e93ffeffefffffeff3ff7fffdff79f797ed3ffffb7fff6f3ffa5fbff3dff7fffffffffff5f7ffbfd7fffef7ffe7dffff5feff7efeffffffdfb7bf4f6fdffd6fff5b7cbffffffff9feff5f7efeffb7fffffdfefdfff7fbf7fffffefeddbfbedf7fffedfddf7fefb7f9f7bfff77fa7ffddff9eff7dff5ffebef9befaffbeffcffffafdaddfef7fff6ffdfbdfadbb7feffbff27fe7b3eff7fbfdefdfdbf6beedbdf3fff7ff6d6ff3fff7bfffbebefbedf3dfffff7ff7fafdf59e5fffbf6b7dff7fe5fffff6ffed7fbfeffff76deffffffdfffbffbfef6ddfdb3efff96ffefdb6b35fffb3fdaf9aeffff76fffdffff6f7fff7dfed3ffefff79eeffcf7fbe7fbdfffbbff2ffadffefefffef75defbf4ffff6ff7fffef3fbffffdf7dbfff77ffefefff7ffefbe9f7f7ff77fefbf59ffffefbfffeff6fefbeffe7fbffbff7ff3ffe5dbdf77f7fffefeffffffcfef97fd7fbffbf6dffbbefedfbdfff97fdfef7fbbdffdfeff3ef77de5b3fbfedfdfbdffffbf9febbdfbdffff7fffffbfdffbfffbefe7b6fdedde6bfcf7eb3ddffffefff977feed7ffeefbfbeedeffe7df7b7ebffbfffb7ffcfb7fffffef67baff7fdeed3fdfddb5b7ffef92ffffdfff7dbf6bfdffdbfdffe96ededffffbffbdd6fdbef3fffdfb6f7edeffbdffefbed7fd7df37bbfffef7ffafff7dfcfb7bf7fbdf7ffeff75d7ff7ffefff7fff9ffb7df3dfb7fbfdf7d6fff7bfeff7fe7bbff3ffbfbf7d6f97ffffbf5f3ffeffbfff7ff5fbedf7bfff6ffbeff59febfdfe79aff7cd77f6ff77ffcbfdf77dfddf7fffff7be7dfdd7ddbff7efeffbefff9edffeffebaff7fbb7fb7be7f2ffbfbffb77bffffefbffbeffdf7edfef7dff7bf7d6effcfa7ffef74ff79fff6dffffbff6ff7dffdfe7f36d6efbff67bbfb7ffffbadf7fbbfffdbf6faffb59eefbff7edfff75ffdbff9f7ffdfefffffb6b66fbfff5ffebffffff7dffddf7fb7fefbfeffdffebf4fffffed7ffbff7ebf7b2edafffeffdd67b7ddbffedffdf77dfffafff7fffbf7befdffdefbb7b6fffffef9a7b35f7edbfdefbfffffdfffaefadbffff7df7b7cfffbafffefe7ffff7dfa6ffdbfffbedbfbfffbdb7fbbff7fffef7fb77dfffafbadbfeffffeffe5bb4f3edf7fefdfffbfbfeff7b6cff5dfef7fbf7fffffdfb7ff7befdbdd27de6ff5fffbafdffdfff77dffb3efbf9f7bfffeffbff77dfebbf9ffb7ed7fdfffffb7ffbdffffeff7df7f9efffdbedbfdd7ed6dfe79fffbffe69bddfffbffff9feb7ffefbf5bfdfeffffdfffbefbfdefbfff3d9efbfedf7ffcdafdfff7fff7f6cd75fe4ff5df7dbdf6fff7f3fffededfbfdffb37f6fdbefffbafff7f7fbffdfdfbfbfcdf7f7ffedbbeff5f77b2ffb7dedfbeb7ffecff5bfebf7f6ffeede7bfeff7fffbfffffdfebfffeebfff37ffdf7fffeb7ff7fdffbfedff9bdfbfda7f7fd77f6fdedfbff3ed6fffed7ffefff79eff7ef77befbfeffefffffdfafff7ff6dfffffbbdbfedfff3fd6d9b6f74ff7d2ddffff6fffbfff7eff5ff7fffbeeb7fdf5bffffffe6d7cfbf9ffffeff7feffb7deebffde6bfcfaf9f7ffddfffffdefbfcf37fffd6fd2fdffb77b7fbfedfddbdf7effffeddf7bf7fbfff7fbff7fdfffbdfe6feddf7faefffd7ff7fffdbedfb6ffffeedffdfdbfedffdfdf3f9fff77ff7b3efa5feffbf9ffdfcdffbb6bbfffefbffb7ff4f3cf7ffffdeffacbfefefffefefbefb77fffd3ff6fdfff7edffbedf6dfb7bfdf7effdfb7bf7f3ebfeffffffff7bb79eef6dd7fffdbbfbefbbfff7fbfffebfe9fdfbdfeffbff7f92ed6ddf7fbdfffbbdd3dff7fffbf7f6fff5dbdfbfdee97eff7feffffd7ff2ff7fdf5b7dfff9fdffdfbfb7ff7ffbdfefdffffcd6effede5df6bfefefffefeffffbfeffeffcfb5befffdde7feffbffecfb5f6fd7df6fff7fbef7ffbffbfffdff7ff7f7fff7bbfbfdffedeefefbffbf7def9edfafbfebfdffeffedfffefffeff7f7ffbdbeffffbefd7ddbfbf7bfebf7bfffffdfff36bfefbfffdff5f7dfeef2ff6fdffb3f9f7d6ef2fbf6ff6b7efacdf5feffffffffffdbdfefff5f77ffefa7bfcb37f7fdffdf7feef7fdffdbdf77bedbfcffeffffe5df6ffcfffd7ffbfbf7ffcdf6befdf7ba7f7fffe97df7fffdfffdffdbdf7fdeef77f76dfdfffdfef3efeedfff2ffadff4d7ffeffefdbebf5beff7edbdbbeff4dfebbffefff7fbfb7ff7ddffff7bffffef2efa7beff7fb6effdd67feffbfde7ffefffff5f7ff7fd7effdfbdf74ffffbffafdefff5df6f7ddffdfefbef7fbeefbfff5fb5ff7dbffe7fffb7fbffbfddf7dfff76ffff3df7fbb5bfdd7fdafd77dfcbf7bfffbfffd9f7f7fbfffffdadbecffed7fb7dfb7bb7fbfbffffdf37ffcbf6ffffeff27fbdbbfbf7f3effddfff7efefffef6dbf7ff6fffb7ff7ddbef7ff77f7eff7dbeffffefdffff7fbcbbdf7fdfcdf7bedbfefeeffff77fbffb7f7ed3effd9edbbff7efeff75bbffbebe7f7fdbfdf7bffdffbbffa5ffeffdde6bffd3fffebf7dfefeddffbf7fffbefbeff6fdfefbefffffdfedbffff4dfffffd7fdf4b7edffdbedfffffffff76fefdefbfff3e9eebfcfbfff5fbfdf7f7efff9e7ff6f7edfdf3ddbefff9ffbfdff5dfdfbffefd3ffefbffff5bf79ffd2dfaef7dffffaffeffeeffcff797efb7fb7fbddefd6ffefbedb7efffbfdfeffbebf7f7effffefff7bbef7f97efe7ffcbfeff7fbcfeddaff779fefaffbfdb7fffff7ffff7ffecbf5ff6ffefbf9fcffcfeffedd3dfafffeff7b3ffedfffb76d7f9fedfddf6b7ffffbbfdafffffff9f7b7dfffdb6ffeb6edfef3dfb6bfff6ff7efefdfcffffefbfddbffffbf7d7797df3dfbdffcdefdeffeffbef7d9ffb7ffbfdfff7fdfffbcff5bbfffcf77f7ff35ffdfffdf7feffbfbe5f3ffe7bfffeffecfffdffffef77bf7f37f7ef2ffefbb6ffdbfff7fffdbffffcdf6f7ffa7bb7ffeffebefdf7fb7ffdde7f3ef2fde7fbff7f9fdfbfdfdb7eff7bfefe7be5ffdf6fb3ed6ffbdf3cdffffffadbe6bfdf7efaffff9bdfbfbfff6fffffeefbfffedacdefffeb3fbfeffdd2fffeffffffb7fff5fffb76dfe9ffdfd9f5f7e9f79fffedfefbfdd7fffffffdfcfffbf7fffffdbfffbfbf7fbed27fedf3ebfedfffeffedbfff6ebfdff79b7f7dffff6ffe5dfcbfdbf7d3ddbffbebfef7ffbffe5ff5ffef7eb6eff7bfffbfff6f7ef37ffeffdfe79fdf37fbdff7ffff7cfefbbfb3dd6e9ffd77bfff75fe7feefff9eef77b7ef7ffbddfdf7ed7f9ffd3fff7ffdb7edbfd7f9e6bbfb6fffdff7deff37ffffbefed9effbfdeefbedf5dfdbf7feffbffbfff6ff6bfebfefffff7fbf977feefffff6bbfffffadfeffe6f3eff7dfff3fffcbff9ffb7ffe59eff37ffffffdff9bdffedffffff7dbbff76b7ff7ffbfda7ffdbefbfcff7bf6fbdffffeffe79f7bfeff7ffff7fdfcbf6fe6f3ef7dfadf7fffebffd7ddb7ffffe7beefffffef7cb77f7fdff9fffbffe7d7edbdbe7ff5deeffdf3fffef7dffffafd65feffbff6ef7df3ffeff7efef9bfdfd9fdbffff7ffff3fdbfbf7b7efaeff79acf7dffffeefb7fadbfdbfeffff7fbf5ff6f6fdeffffffdf3ebefbfffb7badf7ffeffeeff7ffdfb6ff79effbf9fefff9ffb7ddfffb6ffdfefdfdf3dffffbdf7ef3fd3ffe7fb5fffbffd67fedb7f9fed7cfbf9fdf76fffdaeff5fbfffdfe79bfffffb7bf4fffbacdfffefffede7deffb7feefbdb77f7cdbfbeebfff6ebeddffdeffbff7efbdfefdefbf4f7fd7ff75df6bffdffbfff7ffe6bfd9feffdded9fdf7ffe6dffdf7ba6ff7df7ffdf77de7fffbfefffdbdfbefbebffdfff3dfadf3cdefbefd7f9bef37dffdeffafff7fffffefedfaf9a

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches13 : PLift ((OMA.PrimeProgression.composite primes 15 158979 26952) = mask13) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified13 : PLift (rows13.all (check 158979 26952 mask13 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct13 : ∀ r ∈ rows13, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified13.down r hr
  rw [←maskMatches13.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows14 : List Witness :=
  [(1986,187,156),
  (640,582,50),
  (1437,260,114),
  (1725,218,131),
  (1614,233,123),
  (793,475,61),
  (1438,262,111),
  (650,580,48),
  (613,617,49),
  (594,637,47),
  (1035,367,78),
  (1011,378,80),
  (1691,226,133),
  (1297,295,105),
  (1158,331,93),
  (1753,222,144),
  (1602,243,133),
  (1069,365,89),
  (1254,314,93),
  (1291,305,96),
  (1317,299,98),
  (1208,326,90),
  (985,400,73),
  (1579,253,118),
  (880,456,65),
  (1262,318,93),
  (987,407,74),
  (1981,203,148),
  (1889,213,142),
  (1169,347,90),
  (1731,235,136),
  (1710,238,137),
  (895,455,73),
  (935,436,75),
  (1651,247,131),
  (1781,229,140),
  (774,527,61),
  (1082,377,86),
  (1606,254,127),
  (819,499,65),
  (641,638,51),
  (1513,271,115),
  (1804,228,140),
  (1687,244,131),
  (931,450,72),
  (566,743,42),
  (785,536,60),
  (1203,351,94),
  (1026,414,76),
  (912,468,70),
  (1053,406,79),
  (1977,217,162),
  (1210,357,100),
  (958,451,78),
  (1460,296,118),
  (1092,400,80)]

private def mask14 : ℕ := 0x7ffeefefdfef75df7ffefefbbfb75ffefbefb7badffdbf7d6ffb7feeff7dfed6eff7feeff7feebfdf37dfff7ef77bfffefdedff7fffdfefefbb7f77bffffdfeffffffcff6beddf5ffdfbef77f6fd3fffdffddfff7dfb7ffeb7ff6efbdf7fdfeff697fbfefbffaffbddefdffff7dfdf7edefb7ddefbbfffdffef3ffffbffffcff7dfdffdfedbffbf7ffdfb7df7fbdffffbfdefdefff6d7ff3df7ffffbfff7eb6ef75ffcbffffff7df3ffb6fffdfff6edeffb7fbfdefffed75ffcff7b6ffffdffbedfb6b7ffffdffdfeff7defbbdfffff7f3cf7ff6fdff9ffb7efeffbff3f9bfbff97ebfefbdfefffff7efffd3fbadff7fefdffff7bf6bfefffdadff7fffbf7b7ef7ff3ffbdbf5dff9eeffdffffbdbefb3ff7ffeff74d7ebffded9adf7dffeffdfffbe7bbf97ffbef6fff7bfeb7edeffe7ffeb3fdeebbff2fffffbfd7fffff75fb7bb69f7ffddbddeeb76bfeffdfeffe7fbdbffbeffffbf5ff79ffffdf77feef3ff6ffaff2dfbdbffbeed7ffb7db7f7ddefbefff7ff4bfedffffef7f9fff7ebfefbffffdb7f3efffd7ffb5fefbfdbfeffcde7bedbfefffdbff7fffdb7ffe7f7ef77fedff5d6fdfef7fbfeb35df7feddbfffef7fb7fb6edf79fdfffbf6bfcfffbbfbf7ff7defdfffe5f7fff6deddffffff3ff6ff7ff3dde7fbefeebbeffddf5ff7de7f7ef6dfb7f7ed7ffbdfbffafffe9f69fdffdffdbb7b6efeddeffffbf5feefadf2dffcffe97fdfefff9ffbf7fee9ffff5bb7f7effff7ddfffefffcdf6ffeff5dbffbdfefdeff3dbf7fb7beff7fdb7fffbbfb7efaff75fefb3ff77ffdf3dbadf7edfebbef6fdfcb3fbf79bffefdfffff9f7bbfdefff4fbeffff7fdbfbfdffff7ef7efefde7bbfffffffdfffffbbfdfff3dff5ffffb4feff3fded9f6b3cdfff3ffadff6ff7ffff2eff7fa5f3fbefffef37fbebfdde6deff2fdfebf5f77fedf3fdfffff96fbfdfadbf7f7fdff9eef77fbffffbffdefffdff6ffffffbffdefbbdffcd7fdfeff7bffff7b6edfed7fffffbcb6fbbff6fdfcfffff7fbdfffdfdfbfffe9ffdff9feb7ffffd6df2dfffff7bfffecdaffb4ffcf67bfedfffa7fbdffff7ff37ffeff6b6fffdfffffff3ff6fbffff7db5ffff7fdaed65fbff3dfeff6ff3ffafffc97ff7fff7dfeffff7effcd3ffafff7d7ff3fff7be5ff5feebfdffffefbb797e9bff3dbfff7fd6ffbffeffbcf7effffeff7ffffb7edf6fffdffbeef7effff7fd7fbf5fff9fffbffef9f5f7fffffaff3dfeffbffeebfef75be7fb7deebfffffffdf7fdfff7dfffdbefffbf7f7cff7dfcfff9fe9ffdbdfbfff5f77dbcdffbf5ffef77ffff3ffbfb7fbef9fefbffb7ffedffbffd6f9ffb7d9f79bfffd9f7ffcff7f6efb7feffffd7fd7ef3dfefff7deffbfd6fff7ffffeebbfdffffcb7ebeeffefbfdb7bbdd7ef3efffff7bbe9e7dfdf7fbffffebf7b6ffeffbef3dbe7fefdbdfffbfdfffdfdfb7fe7b7fff6dfdf65feebf7bf7ffffb7fbfbbcd7f9bfd77dfefb7ffff6df6dbbfb77bffb7dfbfdffffebef97cf35fffbffb77ffcd7fffeb7dfffdfffb7ffff76b67dffffffeffb7feffefdfddbdfbfde7faffbfdaeffdbfefffff5dfcf3cb76dfdf7fff7bf7ffefffdbfbffffefeffedfefffff3ef669bfff5fadf7cfffffefffff7f77be7b7fdeddf7f7fdf7bbfdeffedfffdfffeff75fafbf79fef7cfffdf5fbdf7fdefff7deffbffff93ffff9aff3df7edbffffbb6fffffff7edff9f6fffdfebfcfbdfeff3ff7efedd77ba5bf7fe6f7dff7ffcfffbf7ffffedffdffed77ffcffffedff4dfff7fdffffeb7f9e7dffdefffef76ffffbffefda6fbe97fdefdffbb5bbdbf6dfdfefffeffdf7edbdff7dfefffde6fbdfb7fffffefff92ffffff5b7fdffb6df7fdbeb7db7fb3edafbbefbfdf7bfffbdff4fff97fffedffffeff7fefbeffafffef77f669bdfefdedfbffffbeef75df7ffdff7feed7fbbebfcf7effcdb7bfffbf9f6ffeff7bfdff7befd2cfffbfeffdbeedfffe5fedf7fbe7f3effdbf7fbfffe9bfffdbf6ff7beffbefbdfbeb75dfff6edfddffffff7e9eff7ffb7bffffffeddff9edf7ff7fffdffffefff7f7fbfff67ffdfb7ffefbfde5bf5fbf9ff96cd3ffefff7ffffbdfeddaffbfdfffeed3ffffbfdf6fffffefbedfbdb67dbfff7fedf7fffebfcfaffefffdd7fdafd77bbebfcbffdeedeffb7bfdf77feffbfdfef3fffeffefffffcff7feff7df3fbedb77fe7defd77feeff7fefdbef7fdbdfb5fefdffdffdbdfb4bffdbdf2dba7ff79f7fafffdbedfbfdfefeffb5bfcff7f76fedfbf9fcfffb77bfdff5daffbff7ffbff35fb7f75fef97fff7ffefffbeffeef2fdffbfeffebfedfdfecffd9fff7ff7fff7bbff6fd6dfffff7f7fbf7dbffffffdffffffb7ffafbbdffed7efeefe7dfcff4de7f7fdbfdffbfeff6bfffe7bfffbdfeffefdffbfffbff7fffffafbe7bbdbe7fadffdfffff6dfedfffffbf7bffffeb7ffefdf5ff5fffb3dd3fbf7bf6bf7bfddbfbe4fbedeffeffb5faffffbffffdde7deffbffee9edf2ffafbffd7fd3ff6ddb7ffcffefbed7fdbff7dfffbbdfbdffeffefffb3ddffbf5ffef7efeedf7fbebfddeff2cfefffdffdffebffffdffdfbedf6ffef37bf7f7efefbbff65fffbffdefffedbd9f7f77ffff3ddaffedf3fb7fbfcffdfacfffbfff3ff67fe7ff6ffeffff7fdedbfedeef7ff759efb7fdeed7fff5dfdff5be7f3fffdfefffdf77b7ffefdb7fbfb6effdd7fff6fbdfe7d6ffff9feb3ff7fdfffbdfbdfffdffbfdf6ffbdb7ef7fbbedeffbcfffff7dfdffddbfbf5bfeffede79f7fbfb6efefffffbdfb7fffdbef77ff4bf7bf7bfdfb5ffefffbeefbdf6d9b7ff5fffdaffffbf6ffddffbbfdfd9efbffb7fb7eff5fbdf7ede6ffffb7fb5bbfff7dbedf7fefbb6ffffedf67dbeffff7fffdfedde7bffd6fbafdeddfdf3ebef9ffd7dfeffffbffbeffefffdf7dfefffffbffbdfbff7fdaff7fffffbdf7f9ffdf7dfcffffee97cfbfbf5b3fdfffeffeffb7f7fdf7bafd7fffebf6ffffeffed9fffffb7ff7fdbfff7bf7f67feef3fff7f77fe6dfff3dfeff7ebf7fbef67da7bbfdfffaeffdffdf7cdff9afdfffe7ff6dfff7ffa7fbffbef77f6cfb7beffbff7effffff9fcffcf77fbdfe5deef7ffffffffff9b7bbfffeb7ffffffdfb7fefffffffff7ffff7fb2fdbddbff7dfe6bfef37ff7fff9f7fbfd3f9fff77f67dedffffadfbfdfffbff759fdf3df6ff7fff7df7b7dfe7dfffafff7ffdd7efecff7dfff7ebefdefd3dffefbfbffffedffffebfdbffbaff77dffb779ffbffff7faff77ffedfefe5db7fff9efffff2ffbffffdf6baffedfb7ffc96fbffffdbffffffeff7dda7feef7cf6efefffffbffbfbfebbcfe79fdbbff7ef7efe7ff7ffffff93ffbf9feff5b76fffdb7fe5fbff76feffb7fefbf5ffff3ffefffebfdfe7fbff3fffdbfefef9fefbfff5ffffffdafdf7bffb7dde7feeffffb6ffddffb7dffffedf7ef77d7ef7dff7fffbf6faffefffefb5f7efffffffedfbf9eeffcffdbbffbed7fbfeffffbffffdefdfdf7ddfef7ffffbbddbdbf7f7cb7fdeefbfff6fffbf7f6ff3fbfcffdff6bffdf5ffcfbefeff3ffffffdb7dd7fbaefff9f7bfebffd7dfadbf7f7ebffb3ddfffedffd9e7bffdffffffff96effcfb7ff7f77be7dbffb5feebbfbeeffff7ddfff77d7efeffedffdf37ffffbefff9feff79f7ffffb79fef7df76bfff7fbf4bbfdfedefdffdf5b3fbeefefdb7dffbb6ffffbff6fde5ffef7eb7ed6fbfff77befbfdfbdfffbfdff7faeffffa4ffd9ffdefdfffbdffff67feff27fe7ff5ff7bffd3fffffb7d6fdfffe5dbffb7f7edbffe7ffcffefffb7fdedbf7bf7f7efbfdadbefffe9effffdffffffffffff7ed6ffefbfef66bfdff5fbfb76bf7ffefffdb7bf7fff97fd7ffbef37ff7beeffdfa7f77f7fffefafbeff7f9e7ffdfffbedfffdf7dafdff9fffffbfffeff75feff7ef6fdfffb7bf7f7fffed7fd7fbfffb5be7feffedffffff9f6f6fdf7bbefffde7f7efb5fecbf5ff7feefafffdb7cbfefbfffdfeff7ff7793ffbffefbb4d7fbffdfffb4fbfdff9bff7fdbfb7ddfff7ffff9fdffcb7ffeefffbfefbddfefbdfbfdf5ffdbffbffdefdeffbef77dfdfbf9eff7ffee96ffffff7fbfdf7bedd7dfb6bfdf77fbfda5bf6f3fd7ffeedffbffff79fed7dfffbfef3efefdedfffdbeb7fd7edfdf6dfa5fbffefd6ffe7db7ffcbeff7effd9f6bfcbfffecff5fbffbfff6feff7fbedffdff6fbefefdf5bffb7effff6ffbebb7dff9fcf27bedf75dffdfed6fbfcf3eff7b7fdffbefbfedffbfdfaf9edf7effedfdf7fff4fb7f6ff3eff7feebb7fffbffdfdfefffeffff3dffffa5bb6fefdbfff7bbdffcfef9feffdfaeff7f7efffdaddfef3dfe7fecdfffffff5b77fbff77dfef7fbee9edfafffcff6ffffffff7ffdfbeffeb2efefdf5f36fe7f6edaffbfbfddfeffffef9ecfffd6fffed35fb7bffbffffcf77bf5b7ebeedbffbfdeffbff6ef7df6ffbdfbeffebbff77ffefbc9ffb2fdbffaff7ef7fffcff7df7fffffe9efd7fffebbfff7f2df77ff6fbdbffdedf2ffbefff9ffd3ffe5beffbff7ef7fd75ff7ffefef93fdfdbfff7fffff6fff7deffbd96fbffffffbeff5befffedf7ff5fb7f6ffbffa5dafff7f67bfdfbdbffffdfffd2fdffff4ffffffd7effffeef7fbf6fedfbffa7fbfdeef7ffbdffeffdff6f7ffefdf5fffb7ffbfff7dfdbffdf6f7ffbffa7bf5defdfff7fdb6ffefefdefd3dfbfffedfffaffffbefffdfffdfffbfbadff5f7ffadf779ffbfdff6dfdff7dfeffff67f3dfe79bffb5ffe9fefefdf5bbfffff7cd6f9e7ff7bfffacffdff6ffeffebeffb5ff7fbfb6fdbfdefbfff3fff7ffffe5feef7ef67b3effdbeff77deffffdfdfb4fbffeffadfff9efb7dffeffedffbedf3cff7fecf7dfefbf7dfff7dff7fedbfdffffadfb5ffffb7f6fd7eff5bfdfffdfebbef75fffbf7ff7decd7fff7ffebfefeefefbf7f3cf7f96ffbffbdbf7f6ef7fdbfdefb7dff7dfdfafdbef7fb77fbff7ffe5f76f6fdeedffdbfff79ff9bfdaf9ffbf7f77f6cfffdbffbfff79fedffbffbffdfedbdfb7ffff3ffffbbfdafffdb3f977fbdf6fbeffbfdffb7effffbcb7ebfff6dffddbebfcff6f7ffe7dbef7fdf6befd77feebf7ffedfff3fffeff7b6ffbffefffebf7de7ffff7fbbfffff7efefd77ff7f7f9e7dfff6dff6ffffffb7dffdffcfffd779ffdbdffdfbff67feffffdeff74bf7fedfb7faffb7df6d3ffaffaff7cffff7ede7dfff7cfffffffedff6f7ef7fbbdfedbf6ffdf77ffcf3ffa7fbfb7fdffdffdfdbfffffdbdf67ffefffb7ff7ffeffbff36dfedfffedfbfff4fe7baff3fbfeffe977bfffb79f7ffffefbedffffe5fbfbfffafd6fdf7fb5f7fdbffbdffeffe9feb7cfafdfdffef7fb3ff77bfdf3ffffbbcdfdfe6bfdffef7efbfdb5fffffffeef3dfb7bf7bfededdfffedff4f7fdefd77deff77bf7ffffe5dfdfbfd7fb7fdffbbeb7fff7bfddef9eeff7bf6f7ffafdefffedffbfddffff7ffdb77f7cf6fffdfbebe7defff7dbefffdfebbeff7fbfffffeffefdffbbebfddf7bbdf7dff6ffedfff7fdedfedf7f97ededdffbf6fbfffffffdbf9fdbbcfffdaffedffefbff7ef3ffbddbffbffefbbfff7bffffdbf7f2dffd9ffff6d7ebaddbfde7ffddf7beeffdfecbfdbf6d7ffbf9fef7fb66fffffdfedff7fefffffbdbbffffd6fffefefbfdbf6fff9fdfefdeff7d97ebaffffbbff3ffffdfddfffefbb7d7effff2fffdbfebeefefdffdadff6be7ffdfbd9bfff6feff2eff7ffefff9ff92fdafdbfffdb77fecde5bbffbdbf79ffd35ffdfbdff6f6efffde7fbef76fbddf7dedf7e977f7cffffbfbfff7fdbfff7fbff7e9ffffef7ffeebf7d7fb2fffffeffbfbf7d7ef7dfb6ff5bf6fecf7fdefb7dbeedfff6fffff3ff7effffedff5fffd7ff7ff75dfef77ffffeddffff7f7cffeb6ffffffdfbf976befff5bfdffffe7f2eda7bf6ffeffffbfdefdfffbebffb3ffe7ff7f7fd6fbeed7ddb7ff5befb7ef3fdf7b77f77f2ffffffffbfbefdfddf7bbfff5d7fdafdffffcfb5f66ffdfefffffb6ff7dbdfbffffb3df7ef7eff7bf6f3cfffdffd7dbb6ffff7fbffffdfeffbfff6ffedbdfffbf7df7fffd7fbeeff6fffdfff2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches14 : PLift ((OMA.PrimeProgression.composite primes 16 185691 34347) = mask14) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified14 : PLift (rows14.all (check 185691 34347 mask14 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct14 : ∀ r ∈ rows14, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified14.down r hr
  rw [←maskMatches14.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows15 : List Witness :=
  [(772,576,54),
  (525,850,37),
  (798,560,59)]

private def mask15 : ℕ := 0x1b3edfdfecfff9eebfcfbdfbdbffdffffdd2ffefffdf7fdffd65dbdfbff6effefffbb7ff6f7fdfffe5ff7bfffefffdf7fffffffdfffbffbddb5f7ffeeb7fffffeeffff76deef3f9fef7fbfedefff5fbdf77feff7fffdbbdbfdfef96ffe7dffbb7ffff3fdbfffebfedffffcfffbf6fbffefd7cd7dfeefffffeffdd77fffff4f7efadfafdbfffebf7dbff7dfbfffddeff7eff7fbef3f9eff7ff7ddfffffb76ffdfaffffffef7fffedbffeefbfbfff7ffafbf6ffefe79ffdeffbdfbfbf6f3fff5bffb3dffffbedf7ff6fffbefffedfffe7ff6dffffddb7fb7fbff77bfcffdbffff5dfffeefe7dffbb7b7ffafffddffbf7b7edfffffffdffdfefdefd77bfffbfff7d7efbfbffff6d7fbfffe79feffdd7efeefffbb5bb5feefedde7ff7ffdffefbffb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches15 : PLift ((OMA.PrimeProgression.composite primes 12 222336 2301) = mask15) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified15 : PLift (rows15.all (check 222336 2301 mask15 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct15 : ∀ r ∈ rows15, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified15.down r hr
  rw [←maskMatches15.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows16 : List Witness :=
  [(1280,356,97),
  (1160,393,88),
  (1564,292,115),
  (1927,237,139),
  (1667,274,123),
  (902,510,67),
  (1760,263,138),
  (1197,390,95),
  (1559,300,125),
  (968,485,78),
  (826,573,67),
  (748,633,60),
  (1246,383,95),
  (1016,470,81),
  (1162,411,90),
  (1133,423,87),
  (1048,458,81),
  (1094,440,84),
  (1003,480,77),
  (673,723,54),
  (1462,333,114),
  (1252,389,99),
  (1120,436,88),
  (998,490,77),
  (1897,258,146),
  (1346,367,106)]

private def mask16 : ℕ := 0x3bf6beedbffefffdffe9fdf77fbefff9fffaef77befb75ffefffdbddfeb7efef9bdf6fbefff6dffbffff7dfdfb6de7baff7ffffbfedfefaffa7fbffbfd6ffedf3fffdfbfff6facfb7feeffebffbffdfdfbff77f6fbffff7fefff5fffbffff7db6b7dbf7dfff7fbffff5bfef6cdffdfff3fdfedffdffff5fffff6f7df7fdf7ff7b76dfddffdbfbffdff9bff35fafb3fffedbff7dff7bbc9ff9fcd3fff7f7fdfffaefafbbefbede7d6fdfdbefbbffeffbdf7fbfef3dbf6bffff5ffcbfefffdfff7fdb7bf5ffeffedffffdfb7fe7b6dd6fdb7b7fd77faeff5ff4ffdfe7fefff7ffcfffb7fd3ef6fbf7bfff6f9edfbffbff7ff7fdbeffdbbdbbfdefb7ffefdb7ffcdf7feffafdbfffe97efefffdfaef3fbfffefdfdbf7ff5b7ffbddffffeff6f7efffd2ffeff7fbfefbdf3ffedf7cdeefeef7ddb4f3fbffdfedfdbbeffdf7ffffff7bbdf7fbf7ffff7fbecbffde7dfffe7df6f3cfefdffdf7ffdf7fd7fd7fff7badbbefffffff7fdbeffe9ffdfffffffffffffef7fdbd9b7fbeb7ff6eff7ffdffdffededfafdffbb7bffdedf7dfffbbf9f6dfdfe7bffffcd7ff2edffbfffb6ffffedfaf9a7ffcff6fbdfffdbefffd77beefffffcffdfe7fffde7fe7b3ef6effdfbfdefbbfffff7cfffbbfffeffff3fdf5dfff7c9f7b2ff7fdbeff5bfffaffefff7ffdffebffdb5fe6ff7f6ff7ef77ffeb76ffffeffe7dfcfbefe7f3ffe7bf7f3fd7ef6fd67ffeff7bffffcf2fdbff7fbffffdfa7deffffb77feef75fe7fbff6ff6efffdfdff6fe7feffb7dfebffb7ebbffffbbdffddeefbff7dffefbebf7fbffedbffb7dff7b7edb7be7fffde6deddfffb7ffdffef7ffefdfeffcf67fbffeddaeb37f7ff3ef65fe5bffdeeb7ff7fffffbedfffbcdbfdbfff7bfffecfefffdf3ddfeb7efbfbb7bb7deffecfbfff4fbffeffffffdfeeb36f7f97ffb5bfdfbfffed7fdffbf7ffd9ffd6fffffbff7dbf6fecfffbb7f7edff97edfdffffbfff6faffbfbe7bfffeefefd35fbcbfefefb7ef7fdf7f37defffedefff7b3cfffbbcdedfbeffff7ff3fdef9fdffdbf7f7dff7bbcbf7ffefeff7fbfdfbdbffffffe5dffffeffeffcfbfbeff7ef7fffededff7ff7ff7beff7fff7bf6dffb7ddf5ffff7fffff7fffffe6fffd6ffeddefbfeff5befbbff7dffff7ff7ffffffdfbffbffffdeedf7fb7ff7dfffffd7fba7bfeffff7dffffa7ffcf77fedfbffaeffdf7ff3fdffdfdfbff6efbdfe7fedb7fdf7dbffbddfff7fdfefeeffdffdfb7bf79fcffdfb6b7fb77befff7fedfbddfffefdb7bfdff5defdffdeffe7bbef7fdefdbffeefffd76bbcfffdf5ffdf7ffefff7bfff7efffffdfbdbffbfcffef3ffbddfdfbfb76f7df35fe5ff5feedbffaffefffdf769bfdffffebf7b66dfdf75ffdfbffeff7fde5fbdfbdffffffdbf9bff7fdf6baffbfffdffdfffbffd7dbe5bffb6fdfefe7ffeffcbeedfdf6fdfffbedffbfdfefbeffbff7efeeffddbdff7fffd2fffffeff7fd77fadfadbbdfbeb7edfddffbecfbdf77faef77ffefffbf7dffdfdfbefbedfedfffffbf7ffffffd7edefbb6bb5ffff3cffddeff75b7fb3efbfdf7ffffffffedfffe7bf7bfedbdff79e5ff4bffffdfa7dfffb7de7fbff6fbbfbf6deebfffffbfffffff7b7ff6fbeeff7bfebeefefbfef3dfffdedfbfff7bbdf7fd7fd77beef3fffededfffffeffffef97ff77ff5ff6d7efaff77bbdf779efdfedfd9e7f7eff7ffdfb5ffdfbd9ffffddfffbcffd9eedadd77ffff75fefffffe7dbcfffb77bfcfbfdeff7df7f97ff7fffef7ebffdbffefdfeff6f77f3cfb7fe7ffdd6fffffb7fffbf5ffefedfa7dfdb7efffbbff7ffefff7fe7fbefaffbfbfdfffbbefffffdfbfdffffdfafff7f7c9ffbafffffeef7fd7fb7cff7ffdff7ff6f6ff6fbfcffdf76ffdd75dfffffff6dfff3dffffb5f6ffbedf5fffbfdff7ffedafdffff7f7ff6fff5be6ffdfe797efb7fbfbffb6fd6ef3fdfeb77f7ebefd67feeffe9e7bfef3f9bfbf7fffbfedf7ffdfbefef9afdff9e7f7f97ffaede7ffdfbdf7fffef75bfffb79eeffdfbffffff6ff7baddb5dffffef77ffcffddefb7efff9ffff5df7fbdffff3cfbdbbfff4df7fffdaffbff3dff7d6ff75fefff7feff7dfbffedf76f77fbffafdedbbeff7dbdfe7de5f7df7fdaff6fffffbffeff3ed7ffffffdf7efedfbfdfffbf976d6ff37fbcffddfff2ffe7ff6f7fb77fefffddfcb7fb77dbffbfbefffffffdbefefffdffcfef9ffdffdf7b7eff6fffdf7bfef3ed7fbffd77fffbffbe7f3fdfffffbbeffffbdf67feffbf9f7bbefefba7fffffebffd77db5f77fffd6dffddffbffff7b7cdfdbbff7fb6ffefdf7beffbffe7f6fda7deeffcf7ebfdfefdbefb7f6fdfdf7fff5f3fffeffffef9fcbfdbeffeefeddbeffcffffbcfefbfeffff76ffff3dbb7ff7d6fd7ffb7dfff75fffbfdf77feffb797fdbef2fdfff7ddeefbefe7bb5fbe9f7bfff7dfbfbf4ff7f7ddfdda6ffdf6ebfdffffe4bfdff7fbffefdefbfdff7dfdf3ffeeff7deedfefadffdbffd7efeeff5fbffb7feff3efffbf7ffeff7bfdfbfde5f7fdeff7fd7dfbebbdf7effefefbf6ffdfffbfffb7fefff7b7effffefda5fbddeffafdffbbeffcff7b6ddfdbb6ff5bf6faffb7ff7fbd9fef7df7fbfffbfdf6fffd7ffefb7fbe7ffff75fbfb7ebee9fff75deffbddeffefdefbf7ff4be79fffedfbfff7bffb6efefdeef3edee9edff5fffbb7d7fd6df27ff7b7eff7ffdfeffafbfebfffbff3ffafbf7dffdbfd7fbfcff7ffffaedbffffb7fff6beffffdbfffdfefdefff5fadbffffeffcfbfdfdffdb6edeffbfffdfffdeff7effffafbfddeff7fdedbf5ffffeff3dfefdfefffd76bbfdeddeffbefffdfcfbfbb7ffffeefbef3fbfeff5feffbff7fdedf7fdffdbfff7bedffffffb7ffefdf7ff5bfffedf3fdbeb7dfffffcffdfa4f7fbf7dfef35bfeffd976f7fde79f5bbeff7fefdffdacffe97e9bffffdf7ff7f7ffafdf5ffebbcfeffffd7ddf7bfdbfff3dff7ff7f3fde7f6dfbffbebff9fff2cf7ffeefbff7efbddedfbdfbffe7dfcfedbeff37f7fdbfdedbffb7fbf7f7ededfbfffdfffbedde7bfdffc97effff7dffdff5fe6f6ddffbe7b7db7fbbffbffffff7bffffffe7ffdff7ffedefff79f6f77defdffffffbfffdb76feffaddbcfbff7fbecfbdbefffd9efdffdbf9eeffebeffedff5ffff77ff7fbff77bfffbfdfeb6ff6dffefffbfff6dfbffbebffd7ffbfdffdfcffffffffffbdfa7bffbf7dfed7fbeeffffefdfff7dffcbff97efbff7ffb5bbcffebeff6fff7f77dffd7ff7fbbfffd9fffecff59aff3eff6d7dff7ffcfbfbfededfffffef3effefefdaddeffbfdeff7dffffffbf7dfffeededdbffbeffffaeffdff7f7edffbbdfbdff7f7dd66f7df7ffbfffffeffeedefffdffff6fbefdf7ffdfbfffff7dfb7fe7f75d7effffffffcfbfff797fdfdbffbf6bfef2ffafbbff7effeb7efffbe7ffff7effcfffff7b37b7edadd3dfeebfedf7f7efffdf7b3ffffdfef7fbfdfb7df7bbdf6ffa7ff79fffbfdbffefffff67fefdbffb5bbffffffff7fdf7b3dbfffffd7fffffb6b77dfeffd9ffff7ffef7eff7fffbbebf7bfffbfdfff7ef76bbddffbe7fffdf6dfffb5ffffbdffefbdd2fbf5ffdbf7dfff35fbefbfbefb7ffe7dffbfcd7ffeedffbbcf7dff7bffdff9feb7fffffbcff7fe5ffef7ffefd7ffa6ff797fdbdf2fdedbf5ffffadf7dfedffef7ebfeffffbdffffeef7ffefff7f3fff79fdfffbf7bf7b76beefefbbeffdfeff7eff5feffb7feffeffb7bf4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches16 : PLift ((OMA.PrimeProgression.composite primes 15 227840 21170) = mask16) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified16 : PLift (rows16.all (check 227840 21170 mask16 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct16 : ∀ r ∈ rows16, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified16.down r hr
  rw [←maskMatches16.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows17 : List Witness :=
  [(1272,396,99),
  (990,511,72),
  (1155,438,84),
  (1142,443,84),
  (1446,350,110),
  (1868,271,142),
  (1699,298,129),
  (1630,312,124)]

private def mask17 : ℕ := 0x1f75df7bffd7edbff65ffdbbeff7fffdfffa7bfedffb3fdfddb6f7ebe7beff7ffe6bf5dffffedff9fdbfdf6fdbffa7ffdf76feffbefa79afff6defd6fffdffdfbdfffbfffeffbef7ff7fbfcfffff7ffff7fdeffffbbfffdf7ffbcfb7ffcffdbffbedfeddfdf7fdeedfffbfffdf77dffbfffe5ffdf75bf7bbfd7dff7bf6b77feeff5ffef7eb7ffeef7fbfdbf79eefecde7ffdf3ff7ffaff6fdbefbfffff3df7dfefffff7fd6fdeffb7f7ffff9fddbffffffc9ffb3efe7fefffffeff6cfffffcff5fefffdf77df7f7fb6edefd7fdffbfef6ffbef2dbe7f7ff7fbffd7ddfef3fff7d7fdafffebf7f7ffaddffda6ffdb7ef7fdf7badbb7feeffffbffeefbebfebffd7ffefbfeb6ff7ff7dbfdffffff9efdffbf7f77bffd7fffdfaeb77df6b3fffdff6ffedf7bfdfffff7fbfbfffbfdbf9ffff4f77bfdfafdefb7fdf6ffffeffb5fbfd7ffaffe7dfdbb7bffdfdf7ffefff6d7effffaf9efffddeefeff3dbfdfffff7dbedbf9ffbf7ff6fedfedffef7ff76bfdfbfffdff4dfffbfff7bfeff7de79fefafbeffffffffeffafffdf3cff6b7ff37feffbfff6f7fdffbeff75b7efbfdbffefb77bfff7cfffde5ff7f7fbfef67fbdf7e9ffdbdf7f9efff6ffefbffb5da7fffdefb7dffffbeff79ffdfdf6fbfdf7ff7fffffffdeefbff77dfffb5fffff5dfffafd7fff7f3f9ffb6fd6fdb6fffbf7fefde7bbefbdf7fbfcf7ffe7bfdf66fbfd3ffffb7fbefdbff3fdedb7edfedbcfe5ffff37f7ed6efffbbfb7e9fffaff3dff7ffff7ffffdb5bfff7cf76fffdfdff4fffff6faffffffdfbcff6befdf5deffbff7ffbefbdbffb35feff7ffefbf7ffedefb7ed7dde7f7fff7bedffd9fdf7cdfef7ffb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches17 : PLift ((OMA.PrimeProgression.composite primes 13 251856 4869) = mask17) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified17 : PLift (rows17.all (check 251856 4869 mask17 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct17 : ∀ r ∈ rows17, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified17.down r hr
  rw [←maskMatches17.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows18 : List Witness :=
  [(1849,280,141),
  (995,521,76),
  (1610,322,123)]

private def mask18 : ℕ := 0x3bffffdb7ffeeffffeffbebffffeff7bf7fbffe7d7ff7fff4f7ebf79fdffdffcbbeff7d7ef2f9ffbf7fefffefefbfcbfeff7bfef7ffaff779fffefdbffecffddf69fdf77ff6bfff7efffd6f9f7bfeff6fbfffffedff6f67bbfff7daff3ef7eb7fdfdfbff3cfeffffdffbf7b7cb77f6ddf7ff7fbffe6feed3ffefbbdfefdfddf7ffeffcb6efeff7dfffff7d67f3efffbe5bf7feeffeffdfbebffbffdffd7dffebf5df7ffefe7be7fbfd7f9fefffffffffd7ed7cfef9ecbbdffe9edf7fffefffbfefffff7fedf77ffed7fdf79ffbbfdffd7dd3dfeeff7ffffefdadfefffebfef7ddfdff5ffddffdaffe7df4fbdf7ffeffedfbff779f6bffffdbf5fbef7f9effefffef7fde7decdfdfffb7fdffb3ffeffbff7fbffd7fff7fa4ffdf67d2efbfdefffeffffbdfbddffff7befbfffe5ff7f3edff9fffffbf7f7ddfffbef2ffe7f7ddf6fecdef9fdffcf7ffeff77bf7fbfd77fbffafbfff76ffffffffddae

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches18 : PLift ((OMA.PrimeProgression.composite primes 12 258860 2774) = mask18) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified18 : PLift (rows18.all (check 258860 2774 mask18 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct18 : ∀ r ∈ rows18, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified18.down r hr
  rw [←maskMatches18.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows19 : List Witness :=
  [(1136,465,85),
  (1014,521,77),
  (1098,483,81),
  (1341,397,100),
  (1952,275,145),
  (992,543,73),
  (1123,484,81),
  (1552,351,116),
  (1561,349,116),
  (1047,521,78),
  (1146,476,87),
  (1268,431,97),
  (1569,349,121),
  (1228,446,94),
  (1353,405,104),
  (766,717,58),
  (1473,374,112),
  (1752,315,132),
  (1643,336,123),
  (814,679,64),
  (898,619,68),
  (891,625,64)]

private def mask19 : ℕ := 0x1bede7ffdfbddfffbffbffe7bf7ff6feffbfdfdf7c9eff6ffbffbdffdbefdfcfffffebfdbffdedfeffbefb7fff9fffe5befbffdeff7fdffbfdfbfdf7d7fdff9aeffcdf6befff5bbefffffff7ff7dfe7fff9eff7edbfdf7fbdfeebfddfdfbffbef7fdbffffff7ff5dfff2fff7ffcfbdfe7d3cfbffbff77ff6ffdff7fb7f7ebe7ffedffbedff7ffffecfffdeefb7feebbffffffebffff6fffffffb7fbcfeedaff7dbf7bf5dffffddfd9eeff4df6bbedefbf5fbe977ffdf7dfa6ff5bf7feff6fff5bfdfeffffd7ffbff77d6effef65bbdfbddfffaff7fffdff7bff9fddbdbf7ffff7efbdfffffff7ebff97ffffff6ff5fffdeddb7bffbffffebfffbfffcfffd7ffbff7f9fff77fefbefffdbb7bfe9fffbefffff7ff7ff7beddaffbcfbfffffeef77ff5ffd97fffed2fbfdb3df76dfdff5dffbb7fe6dfdfbffaffffd7ff7fffdfb7f7cffff6fffdfffbf5bffb7ffaffe7fbdd7ffeedbffe7bffdfffeddf7bfcfffbe7faffedfefbffdffbfef3dfb7ff5f6fdfedfdff6f37befb7efadffef76f76fedffffedf7ffffbfff3ffaffbfd7efbdfef9fdff4bfededdbffbff77dffffffafdf5ffdf6efbefe5fffb3fdff97ffbfdeffffdffb3ffefff5f7f9eebfffffffcbfdffefbffbfbfdf75fe7feffefdffffef7ed7cfffdb7f3fdeffbfd77fb7b3fffffbedfffaefffb7ef7cdaffaff7d9ffffffbdbefbb5ff7f7edffbfdff7f7fdbfdfddfef7efefbfffe7df7bfdffff7efeddbffb5ff7defdaffaef7cfffb7ffff9fcf7f9efbffdbffbebf7df7f2dfb7be7ffeffefbdf6ffeff3ef67dfffffdeff7efffbfed7dffefff9ffbaedffde7b7fffef3effdfe7ffcfffb6fff7ffdbf7ff6feffffff7f3cbf6dbddfdfecff7f7f9fefe5fbfb37fefffedf7bfdf7dfffffdd6fffeffcf7fbbfdeffe4fbdfeffecff7fffbf59effffdafff7fb6bffbbdda5ffff77deebfff7dfb7b7efffb7fff7df7bf7be7f3efff9beff6f76ffddf5ffdfbfdfff7fd7dbbefbfffef7fdbfdedfbdff7fffd7ffffb7ffffbbeff7faff74fffdfededbf7fbffeff3fd7ddeeff6f77feefef9b5f7fbefffdf3dfacbfffeffbdfe7feebb7fffffdfffdbeff6b7ffbffbfbf7ffef6fd6ff7ffbefb5fefffffffbffffddf7bfddb7bfdf7cbf7d7effdffdfbfff7dbffffffff7fb6ebbfdbffedff7be6ffdfbfdbff3efffb2fff5fb7f7cfefffff7ddafb7dbfef7fdfdffff3fbf79fddf7fffff7d6ffaef7fdfff37b6ffefdaffedbbffffdfdffffeffffdffdeff77fbdfbffeff3dfbffa7ff6ffeb7ffffdfcffef77f6ed3fbffbffb7efbdf3fff4bfdfffdfdff5fbeffffffb7ffafbf7b7fdffbffd7ffb7ffffffffff2fdffff7ff7f6dfffdadfbcffffffff7ba6bffd7fffeff7be5b7cbefdfdfa5faffffffed7ef779ffbfed6effffe7dfffb6ffff7fffdff7ff5ff6bbffe5de6ffdbeed6fdfdffcbb5dfefeffffbfffbcff7dbfff5dbcf7fdfeffffb7bffb77defdffd6ffb5fffffffffd7ddf7b7cbf7feedfdbf6ffffefffdfffffdffdbeff3dfbfdf7bb7f7ebbdd37fbcf77bffd3ff65ff7f7ff7ffbefffdffb7eff7fadd7fff6f7dbffbafff7fbffbcdff96cdf5ffdfbff77fefff7becfbdfffbbfdf5fefb7efeefbffefbafffef7ffbeffdff6fbffeffffffdbffb77dfff7edff9aff7fffef6cf3fffffbd9f7deff3f9ffb3ffffbbffafffff36b7f97fffdbfdf3fdfefefdfd9b7bbdfe7fbff7fbfefffffefffffdffeffcfeff7ed3ffffbf7feff7ede7ff7bf7be6bbfffffbffffbff93ff7ffe7ffffefbffff5dfcf37bff9bffafdf7fffd76fbefe5bafffff77ffedfdfffff5d6fffffb7ffefb6fe7beddf7dfcf3efffffcfffbffbbdf6effed67ff6f7effff7df3fff7bff9ffb2fdfdde7ffffe7fffd35ff4bffbf6ffcfffdfef7fffffbff6fdfdbffb6fffdfedbaffb5fffb7ff6fbffbffdf7d7effdff7ffeffffffffffbcffdbffd7dffdff6fbffeefbffb7befbf7b7fffdf75ffebb7d67bfdfedfadbbfdff9eef7fffcf7c9ffb7ef3fdf7b7fdfefbefefffcfff9febfdf7dba4ff7f77feffafffdf7fb66dffdeddbdf3ffff9bfff79f7fbcdfff6ff77fb7bf4ff7ffff7f9effffdfef7dfb7bf7fbeff6b7ffbdfe7fbf9ffdfedf7de6ffffffffff75ffef3fbf7f7ffefffdbbdf7efbef77fbdff5ffffbffafdbffffdffb7ddeffedffede7dfdf7ffffffdfffdefff79e7b3ef6ffadfeffeff7fdfeffff77ff5fffd7ffbedf5bfdfffbefbfdd7ffb7ffeffefbdfafde5fbdb76bfcd7fff6fbfb77feffb7beeffefffdefd67fbff7ffeeffffefbbffb7fffbfffffdb7fffbf7bfddefff6bf6ffff2efbddbff3ef7fbfeff7fefbf79feffcd6fbfff3fff7dffffdfafff7defb3dfb7dbffbfd7fb7ff6f9f4ffffefdecdffbeffff977fafdf7dbffbf97edffdbdbeefffff6d7fd6fbffffdbffbbffedfeebb6fffffff77bffb76f6ed3ff6fffffffdfffbefedfffb779ffbbcff5ffeffefeffefffffffff7ff6d6dfffdf6ff7bf7bffdbffadff7beff3ff77ffdff6fffb6effdffff7efffbaddafff7bffb7ef3dfe7bbffbdbefffed3fff7fbd97edbffffff5fbffeebfff6fdafff6bf7dbcfbdfedbf6ffff6effffb7ff7defdaff7d9bebfdb7ffffff7ff7fbd97ffffff5bfdfbf96efeefbfdfdffcfffdfdf2ffeff7fffff3dfefbffbb7f7edbffe7dfebbfbfff3ffaffe6bf6fffffcdadff5f7f97fdfeff7ffcbf7ffef3df77dfdfffff79fdf6ddfff37dffffff7fff7f3fd7fbfffefdbcf77bffffefafdefff7f7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches19 : PLift ((OMA.PrimeProgression.composite primes 14 264120 15654) = mask19) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified19 : PLift (rows19.all (check 264120 15654 mask19 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct19 : ∀ r ∈ rows19, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified19.down r hr
  rw [←maskMatches19.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows20 : List Witness :=
  [(1885,301,148),
  (1529,372,120),
  (1928,297,145),
  (887,646,64),
  (1671,343,125),
  (1921,299,145),
  (1239,464,96),
  (1310,439,101),
  (1315,438,101),
  (1680,343,127),
  (1497,385,113),
  (1736,332,133),
  (1060,544,81),
  (1734,333,131),
  (1424,406,108),
  (1574,368,121),
  (1609,360,124),
  (1018,569,79),
  (1587,365,122),
  (1373,422,107),
  (1403,415,105),
  (1344,435,109),
  (1191,491,97),
  (1196,489,98),
  (1001,588,69),
  (954,617,67),
  (950,620,66),
  (1087,542,77),
  (698,845,49),
  (1070,553,82),
  (1828,324,142),
  (1550,384,114),
  (782,762,60),
  (1632,367,123),
  (945,634,71),
  (1465,409,111),
  (1385,433,105),
  (1619,371,123),
  (1273,473,97),
  (1901,317,142),
  (1970,308,149),
  (778,780,60),
  (1130,538,86),
  (1061,573,82),
  (1194,510,91),
  (1803,338,134),
  (1277,478,98),
  (831,738,62)]

private def mask20 : ℕ := 0x1b79aef7dfff9fdffffb7bbff7fdfeff7df4fb7ff7dafde7defbff97ff7ef7fdedff5ffffefff7bf7ffe9fffefdbfbeffff9feffffbddfdf7fbe6feffffffdfb59f7dfddafbe7fb7b67ffff67fbebffbfedffffdff5ffef7ffffdf7ff4fbefffffeffffa7bf6bf7f7ddffbbef7ffffb7df3dffffffbf6ffdf77df5bffffebeddfffefff6defd7ff3dff5fbdffefeedff9beb3edffffdfadff7ffff77befdaf9edfbdd76f7dffffe7fffdf7fffd3fff6bfeff6ffff7ddfdb7fb67dbffefbf7bb7fffbbff6dffcffdbfff7ffffbf7f7ffffbfffb7fb4ffddef9edffffafffdb7ff7dd7fdf5ff4ffefadf65fbefb7f77d3efb7fbfbb7fff96ffe7bffff7ff7fefdffbf7f7fdfefefff59beffff7efeed77feeff5ffffffdefff5fbfb7ffffdbfdffffef6ff3dff79f7ff6feff7ff7dffdf37fef9eff2ddb7f7e9feffcdf7faff7edefb7effffafbb79feffdfffdf7bbdf77fbfffffeebffdf7bbffefde7fb6ffedfffefffff7fbfffbfffd9effffff6f2ffbdfeffffdf6ffcffdbbfffddfef7fff7fe5b35fefffddbddbfbffdfedfdfadbedf3ff7ff6ff6ddfdf76df7bfedefdbfff6dffbaffafffffbcf7ff6dffffa7bf7b6efbefffdffbbdb7fffddfddedff7fe7f3dffffffb3ff7efbefff9bef75be79eeffffa7ff5ffffffdbfbf7f7efe6dfef3ffffff5feff3ffb7becf7dff6ffdfedfadfffff7ffdfa7fb7f7cffffeeffffbdffdfefdffdffbfffff97fffffedde6fbc9ffffdd7ffedfbfdfed2ff3fdf4f7ebf6dfffa5ffeb3fbffb7effffb7bb5feffbfffdfb4f7fffff7ed6ffffbfcdf7bfefb7fb5fffff6f7fdfffaffffdfef3cfffffeb7fbffffddffffef77fee9fef759f7ff6f7ff6fdf7dfdbb6df7dfff7fdefffffffbeffbfffff3df7697fdffbbcffdb7fdbffefffcf77ff7fefd6fdfffffd7797dfffbf5bfeffed7ffff9fefbf9f7dffdfddeeffeffefecffddaef7edffb7fd3fbe7fffde7ffed6fdeffbeff7dffff5ffff76fefdfef77daffb5fefdfef6dfbfffdfeffffffffffff5b7ffbfdb7dffffcf6e96cdf7fecbf7d7ff3df77deefbfff7befff7fbdbffff6d7df67fbfbfef7efbfff79ffffdfffbbffefff7ffef76fbfdffdfcfff9efdfffbffbcfbfb6ffaff7fdfebf6fffbbdff7fedfb7bf7d3ff3dfffbbedfed7ffffbbff77df79fddffbfef7fb7ffbddf59f7fbcf7ff6dff5fefff797ffbeda7ff7bb5fffffdf77dbffffb76f7ff7fbadb7ffeebafffdff7bfdfeffbffbf9fffff9fffeffbfff6fbfbefdfeffdfedfb5f6efeefb7befb74ffffeffbfffdfbedfe9bdffffadf3cfeffffd65ff7f76bfffbffffbffbff977f7eff7bbff7ff77dfff7dfffbfdbe7f7dfa7ffeb3ff7f9afd6fdffb37d7effff3ffffffddeff3fdefffefb7bffbfcdbffeeffdf7efbffeffaffbfdffb7cdf7fb7ffdbeedbfff7bf7fb7fef9fffffdedbbebefb7dff7dbff77feefbfdffbffff4bffdfffbfdfffff9f6beddafffcfffbeedefdf7ff7fbdb7fffff37bfeb7df66fffdffffefffd7fffdf3ffb7bbedffbeef6fffdffebffffdfffdefff4ffebbdfaffedfbff67ffffbdfffbffff6ffcf7fdedff6bfeffdf35fffffff7793efedffdfb5d7fbbefe7ff7ff7fefd7ef2fbbfb75ffffedfff9bdfbfdf7ffff7fff4bffffff7ed7fbffffeb7effdd3dfeffbf96fbbdfefdefbfdd7ffefdff9bdff7befb6ed7fff7ffebf7ffdffffaffbfff6ffdffdffcfb7d6efaff7ffeffbebff9ffde7dedbfedf7ffdfa59afbfffffd7ffefff7b7ffffffddfd9bfbffffffefdfffe6ffcffeb7fff7ffcffffefffcdefbedfb7befdaddbfdffb7f9ff9fcf6dff5b75f7e9fffefdf7f37fe7dbef7fff7ffc9fff7fdff9eff7df7fbefdf5ff7ffff66fbfde7befffcf77fedfe5fefbbfff7f3efa7bfff7efeef7efe5bf7fbebefffffbdfbfff6f77fbfdfffafffdbefbffffffb7bffffffaff7fffeb74ffedefdfffeefb6d6fb7ff3fdffb3edfff7ffe7ff4ff7deff2fd3ffaeffd9ffbbffe7beef7dffef6fdbffeefbfb7fd7dd6ffffff7ffebedfafffdf7f9f6bfdf75df7f7efefdeff6fdbcffdffff2ff3dbb7f7cbf7ffdffdfa7fbffffdfed77fefbf7d77feefffffdfbff7fffddb7fbfb7effffbeffd9afffdfeff7ed7ffbef3fdffb7ffefdefffdf7efbdfafbf7fffdff9fdf3fbefff7ffff7dfe7ff6bf7fe7beddfffbfffebfebfff67fefffefffb7ed7dffeff7dff97ffffde7b7eff7b7fdbffb7fffff7fffffdbffbbdb7edfffa7dfffbcbeeffffb7ffeff7d66bfeffdbfff76dffd7ffffffdf7fbffd7cfbfdfebf7bfeb3fffdbfff7fffebfff37bafffffe7fefdf7bfcfbfff7fefffddfebfff67f7ffe7bedbfcdfebfefef9fffffbf7fedfffff7ff4d7ffbfdf5bfffbefefffedbffb5fffbfef6ff37befffffe7ffff75dbdf7fbffd7ffeddbff3effffbfdfdff7f3dfffbbfd3fbfef77f7eb7dfedfeefbcfe7befdbfff6bffbf7f6fdffdfcff4f6ffbfdbddefff797ebfefef9edbb7f7ff6eff5df5ffedefffdffffb7b7cbffffeff7dedffdb6ededfbffb4ff7d7fffcdf7bedf3db7ffbff75fecf76ff7ffdfefbfdfbeffff2ff67df6bff9ffffcdffba7ff5ffefeffa7dfffbddefd7fffdffdffdffff6ef67bffbf6f6fdfff7ddffff7fff93ef65fb5b3ffffbbeffddb5b7ffefdbfdeffeff76d77fafffdfbdffedfedffdffbbfbffd7fd7ff6f9feffff7fbfffefdfefb6fffd3df65baffb7deefbffedbf7fb5bf7ffff7f9f7bfff7eb6edfdfafffedf6b6fff5ffeffdffff3ffbfdf6fb6f7f9efffffbff3fdf7ffffeffbfbf7dffffeff7fb5ff6fefdbdf7fff7ffdbffb7cdf7ffff7db77f7fdbfff7ff5f6ffbcdefff7fffb7ebbddf7defbffd76dbffbfbe7fffdefb6ff7ddfdbfdde7f6efbffffbfdffffbcdbffbcf7df6fffefbffecfffdf7f7dda7ff6b3ffe7dfff6ffbff7effefbdfff9efffdf6ff6ef7fbfeffffff9fefffffebfe9f6ffddb5fe7fbfffefefffdbf4fff9fff6dff7dfeff5b7effdf7dffdbf7be7ffcfaffb7fbff7f9ffdfd9ffb7ffeff7efafdfebf7f77f3ddefbbdfff9ff9efff5fb4ffdb7fffcf7f9ffb7dfffdfdf7ffefbb7de7fbefedffdbf6ffe9efdfdbfcbf7bffb2ffbfff7f75ff7f7ffbdbffffff77ffcdf5faefff9efffefffbedf7ebf6fffdffffdf3fffff3fff7fbdb7cffffefde5dfeffdff7ffededff7f76dfff7fde5dfcffebe6ffcd75fa7ff7feff6ff3ffefff7feffbffa5faefbffff9fefffffdfb6ffebffdfffb6fbffef9fffedffff7fd7ebecfefde7fffdf7bfdd3ffefbffdf6deddefff5ffdb76defdf7fefb3ffeef7ffbd9e7ffefeffffd6fbbfbfffefdffdfdfbfb7ddffffcffdfe6fbdd7fb6ff7fbf7bbfdffdbeff7fffffefff9efdf7dfdfbef66d7ffefbb5ffefff9effef9fcbfefffbbef7ffefff7f77f2ffefbf7f7cbfef7ff3fff7bfdbffffef67ffffffffffaff7ddaeb7f9f6dbef3dff5fffd7ff3ed6fdfdff5dffbadfffbe7fffdffb7edbffffffe96ef7efb7bfefbfdf7ffff779edf7effe9fdfe7fbdffeb77dfdfffbf7ff6ffedbed7ddfebffbeff3cdfdbffff7bf7b7fff79f7f7ffe7bffffdfbffffd66fbedefff5ff7f66bfffbdfbdff6ff7ffff2fdedff6fffffefffff5f3dfffffddafbafbfef7efacffdfffffebf7fedd7dffffb5bfff7fdaffffffcf76bfdffffeff7f9f69fffbfdeff7fdeff3ffefff5bf7df7ffcfafbbebfdf77faffe5fe7fbffefb7ffbdfffffffe7dfffaf9f5b37f6fdfff7ffaefff9f7dfef7dfbdbfffffdfefe7fbffbcdffffffbfbffbf7ff6ffcdbfdbff3effef6ddb7bf7ffdffffaefaffe4fb5ff79eddbfdfff3ff6fbbdf7dfa7fbefffdffd67bbff7dfefb7ffbffa7f7ff7ffefdbfdacf7ebfffffd7ffedfffbffd2ddb7ffef3db7fbbdff5deffb7f7ff7ffe7daffffdeffffffdbfdff7ff79fdf7ffeef7fbffbedfff9bef3fffedefdffbedffdff7dbeff7bffb3df7fbfdfb7fecf3edffffdffffb5fbff7edaef6dffdf7eff7f6ef3f9e6bfe9ffffcdaf9edfbfff7ffffffffdff7d7ffbddf7feeff4fee9bff27dfdf7fbffdfefbffb5bfddeebbed7dffcfbefe7d3ffefbaffffb76bfcdffffdffef7fbfdfbfba7fffff7ffffe7fffffcbe6dffd75dfff3fd7fdbffe5bf5bffdeebaefefffff76befdffdffbbfbfebfffbffefdeefbdf7efeef7fff7ffddfefffdf7bfdf37ffffaffafdfffffbf7b7fff5bffb74f6ef3fdffdf6ffdff7f6effdbeff7cb7fffefe5bb7f7dfeff7efb7bf7fbfff7f6cd7fbffb7fff7fffd3ffedbfefe7bfffb7d

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches20 : PLift ((OMA.PrimeProgression.composite primes 15 283693 24193) = mask20) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified20 : PLift (rows20.all (check 283693 24193 mask20 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct20 : ∀ r ∈ rows20, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified20.down r hr
  rw [←maskMatches20.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows21 : List Witness :=
  [(824,753,60),
  (1758,353,129),
  (1810,344,130),
  (1976,316,141),
  (1972,317,139),
  (940,666,66),
  (1480,423,104),
  (1826,343,132),
  (1859,337,136),
  (1381,454,96),
  (1875,335,137),
  (1779,355,137),
  (675,938,51),
  (602,1053,48),
  (810,784,61),
  (849,748,64),
  (1029,621,75),
  (1732,369,126),
  (952,676,75),
  (1111,580,86),
  (1857,347,145),
  (1074,600,83),
  (1622,398,123),
  (1436,450,107),
  (1443,449,104),
  (795,815,59),
  (1418,457,103),
  (1363,478,105),
  (1612,405,119),
  (1491,438,110),
  (1390,471,101),
  (1055,622,78),
  (1313,503,98),
  (700,947,54),
  (1000,663,77),
  (916,724,71),
  (1727,385,125),
  (1858,360,139),
  (1459,459,110),
  (1260,533,96),
  (1065,631,81),
  (1124,598,83),
  (1072,628,81),
  (1802,374,132),
  (1698,397,125),
  (1522,443,112),
  (1536,439,113),
  (943,720,74)]

private def mask21 : ℕ := 0x5bbdfffd77ffefafff7f77b7fbffdbfdfcffeb6fffcffdde5fffd6ffafff7fbff7c9ffbbffffdf7f7ef7effcffdbe6ffddee9fdf7ffefbfffe6fafff7fedff7f77bffffdffeffedfef7dfbdfe7ffddff97effffbcf7ede7deffedbf6ffc9fff7efbffadfbefe7ffedfdffcbfdff7dffd6fbeeb7fbf79edd7ddfdbb7f7efbffe5bbffbddefbfff6fff5bfffeffedf3fbf7ff7dfef6edffbacfffbf7beff3ffeffb5f7ff7cfafff5f7ff7fdfdf2fffffbfdf7b3fffdbfdf7dffeb7efffdb4bbdde7ffffffda6b7fd76fafdefbbfffdbe7f7dfbfba6ff7d7ff3efffdeffffbffbadd77defbffbfff3ffbfbf7bf7ffff7ff6dff7fffdfffefffdfbff75f7ffeffbfff4ffef77dffffdffcff59ffffffe79f6ff7fffdfdfbffbcf3ffffffff65fbfffef7fdfff65ffebfefefbbdfed9f6ff6d77b7ddff9fffbff7fffddf5fb6bf7ff7fbefffffebbfbfffffdfffbffb7fffdbcff5fbdfbcffffeef7fdbeffcdffffdffdfeff75fffbaddb7fe7ffcbf7ffcdfffeebf5fe7d6ffbfbfff75ffeffffffffdfbed6efbef679fff7ffeff6efffdb7f7ffffdbff6fdfff77977fbffbddbcf7f9febefd75ffffbffffdeffafbefff7ff7dedfa5fbffbfd67bbdf379bdbbff7ffffdffffdf7ebfffbfdffbeff7dffeffddbdffeffdffeb7ef75ffffb7be7ffddbfdfdf7cffffefff7dfef77fefffdf7ffffbfedeedbeffdfffffffff9fed3fdafffdb7ebfefefdf7fbcd6f9fdd37bfffbdf7efedfe7ff6ff7f66ffffbffeeb3f9feb7ff7fdffff6f7eb6ffefbfdf37fffd6dd7d9f7bf7ffff7fffdfbcfbfffedeffbfffeffdbfefffd7ffffffcfffbbfdb7fadf7fdff97efefbe7f76d7fd6ff6fdfcfbdff7fbcffd9beb77b7fffdfb7ffff7cffef7efbfbfefffd7effedf7bffbfebf7fbffb5ffdf7efeff7efafdfdff5f7fbaefefdfefbffe7fbddfffb6ff5ff7befdf5ffdf7fdf7f6ffbdfafff7dfffafdffde7f7fbfebfff7ddbfbf6ff7f3ffb5fa7f7ef7fffef7fdfdfb7beff6ff7fbefb76df6fefffddefffcfffffcf37ffefbfdffd6ddefbf7fb4b77fffff5ffdfffbffdbef2d9efbffd7ffefff7ff7ffffe7f7dfafdbef7cdf7ffeff7be5f7ff6fffffffbb7fffb6edfcfbffeffb7ff7bffd7ddefff7ff69fdfffbbdf7ffefdaff6fdf7b7fffff6cf7f9f7ff597ebffff7fffffef7ffffffdfffff7ffefffdffbecffdff6fbfff7faffbfd7ebfef75ffdfbffeff7fdfd9ffbbcfeffbefefbf7ffcd7efeedf7fffffefe69fdf7dbf7bf7fefd2ffffdf4f7fbefbffdefffcfbfdfffbdfffbe5ff7defffffff9bffb5ff7feefffbeff7efffb3dffffaff3eb7fdefdf5fe5bfff77ffff3fbe7f7fbffdbff25ffdfffffeffefffbffbbfffebffdf5fb7ff5ff7bfcf6dffef75bfef3ffedffcffeffffefdfffbcfb7befdffd6ffffbfdffebefdf7fadbbff7fd3ff7fff7fbdfffdbef77ffff75bf7dfdf6fbb6ffcffefbdda7feffbf977bedfbffb7fbfbffffdf7ffe5fffff6bedfbfdfff7f97793ffef9bdbb5defbeeff5ffff7dfefdbfdff9efbffdf7ffefe7fbdfffdf6fefff7bbcbbddffdbfdffdefb74b67fefffdfbefbebffd3ffbdffdffeffebffdff9bff7ffe793cdbd9efbffffff7ffbffe7fffdf7bfdf7fbfcfb7fe7ffedf7ff4fbff7ffefff7fafb7ff67ffffa59ffbfcfffdffd6fdffbbf9fff7ff6ffaef7ef77fefff7ff7f7cd7effddbffedffff6fffefa7df5fbff6fdbdff5ffdffefffb3fff5ffdff5f7fbbfdedffef3ddffbeed2ffefff7ffffeefffbfeffeff6f7ffffbb5fffffedbffafffcbfdff7faffeffbeff7f6ffffffddbfb7efef97ffffdfebb49fffbeffddefff7bffbbfdbf9b7fff9fefecf75fefbff977fffdff9fdffcf66bffd3dfeefb7bffffeffffedf7cf7f9eefffdfeb7fdefdeff3fbf7bfedf7f6ffe5bb7fbfbe7f7fdf5bffbfdfeef7edf7dffff7fe7fbfdeffaff3ebf7bbcfb7fedffddeefaffedfbfbf5fffffdfeffb7bfdff7ffdfb7bfffbe9f7feffffbffbb5f7ff7dfb7decff7ff6defde7ffeb7ef7ff7ffe7fffff7feff7ed6ffb6f3dbff9ffffdff7bffb7efefdf7df7f3ff67b7ff3fbb7ffddf7dfef6fdf5b7fff7beddffffeff7bf7dfcff7fbfff7fefdfefefdffff7ff7d7ffff9afffef7fb3ffbfdedffc9febfdf77fbdff7fefdffde7deefbeffeffffadffffffd6effcf77be7fbeffebeff77dfdbffdffffff6fdeff77dfebafffdbf4f7edffffed3dffeffff77fffd77dfffb7f7fbedffdfacf76dfed7ffbfbfffffdfedbef6ffffbf7ff7f7fffdffeff7f7ebbfdffde7ffff7fffffbfff5bffb7ffecdbfffebf5fe7dbdfb5feff7fbf7ffff7ddbfb7edfffbededbfcfb5dfffbffbfffef77f7fbffdafbbcf7ff7ff7ddbffefbffbf7dafd7f9f7fb5f7ffaff77ffffb79eedfdfef9e7fbddffffff7dbbfbffdffb7fdfdbbfffeffeb3eff5fe4fbff7fdfeffdfb7fb5deefeedf7be7ff5be7fffff7dfebbefefb7ffe5fb7ffdd6ff2ffefdfcffcff7d3dfefbfff7fffffffdbfdfef7ffeedffdfffe5bffffef7ffa7ffdffeffeffff37fefbf69eeb7fff7fafb7fdffdfff6d9b5ffdfffdedffdbe6f7eb77b3fffddbffff97fbedfffbaebf5de7ffdd7fbfcbbef7fbfffefffebfff67f7ff6fdffbffdfff7ffefbfebb6be7fbcdeffe7fff97ffeedfdfe6ffefffdffffffffbb7f6efbff3fffebfffefdfddfffaef7ed77f3ffe79efff5f7fb6fff5ffdfbcfffdfdfeffb7b7fffeb3dfedbbfffdfe7ffffffbfffbffffd7ef77bf5fb6ff7fffd3ffeffffbefdfff7dfe7bffdefbbfffdfbffb5ffffffffddfef7dffffedff7befffefefdeff35fedfbfbe6d6cff7dffbbeffffadd67dbfffeb77fbeff59f5f3efffd3fdff9feffffefdfdd2fbffffeffff7ffb5bfdfffb66b7ff7fff6bffdeefedfb7fe7f75feffffdffdfdfffdf7bfefb7faff3cf7ffffdffffffbffefffefafffff74dfff3dfbffadfbcff7bedf77bbffffbf7daff6f9f6fbdf7fdffde7fffbbf9fffbdf3fbeffb7dfed3fd7ffb7ff5defdeefeddffb7fd7fb7efbffbefbefe7ffdd3fbb6ff7bfff3ffffdeefbffefdfdfa7dfefbef76ffdfe79ffbfef7ebeed6fdfdb77ffffbdfbfffeffff7fbffdb7defffe9ffb6fd7fffffffbfef3ddbfdffffdfff9bdfe5dbfbffff6b3ef3dfffff5ffedfff7dfbdffdbfffafffdbafbfedf6fffdfdffdf7cf7ef7ddffbe6fbfdf7f2dffffe6ff4befdffde7defbf7f7edfefeffffffeffefffffddfffbedfffeddbdfeebf59f7fefff7fbdf3dfef96fdbfffebb7f7edfcfbfbf7f3fb7fbeff2ffedbbfdf6dfcfffff5f7fdeff2fd6fbf7ffedfffaff7dffeb7fbf6f3cdbdbefffe97fbfeff7feebbff77ffed6fde7fffffffbfff7fedff69effbcf6fdfffb7f7edffdfdfbffb6bf7bbfdfffaffffffff3ffefffdf7ebf7d7fffffeeffdf6efbdd77befbfebfededffddfeb3fbfeffef37defffcffffbfdeffffff7bfffbfdbdfa7bfff7ffefffddf5fffbe7ffffffffefffb6ef6df3fffdb3fbeeffff37feffff9fffbef7ffedfbedeed7fded9bdf3ffef9fffefbfefffff6f7ffff9fff3ffe6ffdf75fbebfd9ffdfdfffff7bfdf77fbff7dfbdbfff7ff7cfffbadbfedffffffeffb5bb7bf7dbdfefdb7bffffefedfffbb7fffd7f97eff7bbffb5fffffcfffdfdbf6ffffbdffffedfffbffd7ff7d9e7f35ffefffde7df6fbdfffbbed7dde7bf7ff7bafff5fffffe9f6fffffffffbfddf6f2ef37ff7b7ffe7beddfdfbfb7f97fffdf6fffff7fdeffeeff5dfffb4bffffdfffbe7b76fffffddfffadfffd76fedf7ffbdfffbfffaff7fdfeffff7fffff3fdeffb7ffebbfffdbf7ffff7ffbeffddbfb77fffffdf7dff7bf7fffb7ffefffeffcde7dffdbfffeff5d7ff7fffffffffcbffbffdefffef3efffd3dff7fe5b3ddffbefffdff4bffbfff7cf6fdeff75f7ff3efffdeffbcf67beddb7ffdfbffe7ffddbfdefffeff6dfffffffcbf7f7edfdf3ffffbf7dffbaefffbbcfbdde7feffeffbff7dbffffeded9bfffdffebfffffbe5fffff6f7df6fbf5bf6f6ffedfefffffbebff9fffe79fdff6fffb2ef7fdfdbbf9f7dfefbfbaeffeffffecff5fefffdbf7fefd7fff5fffb77dffdf7beef77bff9ffd65dbfbbf977d7cfffff5bfffff9fff7fff7ffedf7fbfdffdefff4f7ff3dff79beffef7effff3dbf7bb7f67ffcdfffedbfeb7ffbdd77dbdf7ffeffbffbffb7ff7d7edbff6dbf6bf7df7daef3fbffff6df7fbfff7fbdf7ff6ef6ddffffdbffffef7fd27bf7b7dffffffffdfaffb7bf7f7cf7ffffffef7e93effdff6ff4ff7feffbdff7f76bfffbefbdffef7fbffffdf7dfbfbffbeededfff9fdf7efeffedd7ffbfffebffd7ffafdfdbbff7f97eff7ffebfffeff2fdefdf7fffffebbdde5fe4ffcffededff5beffbfffedbfdbfbe4fffbefbfffe5dffffed7ef3effd9b5ffcfffbfffe7dbdb7ffe7dffdffdbfbf6bf7becfedff5f3cbffbfef75ffebfdfffdfdfe7de7fb7fffdbdfa7dbefffffffbff7ffbdbfff7ffbff759bff77fefd7fdbffffffebf6bbefbfdfffffb7e96ff7ffecfffbeedfdfefffff7fffebfff7ddfeff7f7fbfffafbe5f7ff7fdbfffdffdfb6fff9efdffde6ff4dfefafdffdf5ffdb7fd6fdf7be5fffbfff6cfe7fe7ffeffebfddfdfeffbedeff3dff79fff7ffeff7edffffdffedfff6ffefffeffdfffb7cdaffbfffcfeebfffbfbfeffdde7d3ff2fffefbdf66ffdfffffff77fefdfffffdb7bfff7fd7ff77dbdbffff7fbeffdbfff7cb7eb7dfffdf7ffebfff6cfbfbbffffbeed7ff77bffffdfefffdf35fbffbfbefbfffed9fdbfcdfeffff7dbfff7fde7ffefefffff74ffebfefffbbff3edffdeffb7fedffddf7fbcde7dfeffefffdffd6dfeebfff7ffbffaffefbf7defbbfde7bb5ff7fff92cf3fbffffdbf7ffefbfffdfffffebefdfdbbdbffffffbdf7fff6f3ebf7dfffaffffff7dfeffcfbfdefff5f7ebffdf7bffb7ddffbefdfffffffcffff2fdb5beff3fffff7efbdfedbffdffffefbffe7f77ff7dffd7dfbfb7fbf7dbcffffaff37f7ff6ffefff7bf6befffffbffffffdd77bfedb5fedffed6f9ffdfdfedffff66feffff9febbef779fddffdfef7ffffdfcf67fffb7ddeebfed77ffdfbdbf7feeffdfe7b7ff7fb6fdbdfadfffbe79fdf7fffdfffd77f7ed3fdfcb3fbeefafff7ffdffedefffffbffffb76feed7ffe7bf6ff5de7b3ffffbeffffdfffffffdffff7cfeff6edbdff7bf7f7ffbef7fbeffffbfefafff7fedfbffffb7ff3f9b5ffedef9fef6ffbcbffffff7ff3fff7f7e9fefbffbffe4ffffff9eff37fadfb7dfedfcdffdefbf7ffffafdeffbdf3fffefbff7fdefbbdfeff2ff77ffef3cdfff7ffffbf6fffffefbddf5dfffbfdf6d6ffbfbefffdfe7d6fffffffff5bfefefdffdfdf3eb77fbffbdfaff3ff7fbfeff5bbfffe9f7f7dfbffaff76f77f7fdffde6fbfdf7dfdff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches21 : PLift ((OMA.PrimeProgression.composite primes 15 310236 30659) = mask21) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified21 : PLift (rows21.all (check 310236 30659 mask21 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct21 : ∀ r ∈ rows21, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified21.down r hr
  rw [←maskMatches21.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows22 : List Witness :=
  [(1498,459,109),
  (667,1031,49),
  (1479,465,108),
  (1454,473,106),
  (1990,347,148),
  (1909,363,142),
  (1489,466,111),
  (1071,648,82),
  (962,726,67),
  (1941,361,148),
  (1915,366,146),
  (1118,628,89),
  (1878,374,144),
  (1873,375,144),
  (1973,356,153),
  (1639,429,127),
  (1604,441,123),
  (1527,464,113),
  (961,740,70),
  (639,1113,46),
  (1440,494,105),
  (1746,408,127),
  (1079,662,79),
  (1019,701,75),
  (1624,443,125),
  (1831,396,133),
  (1232,589,91),
  (1093,664,82),
  (1176,619,85),
  (1665,438,123),
  (1720,424,127),
  (1420,514,103),
  (1097,666,82),
  (1128,648,83),
  (1851,395,138),
  (1648,445,122),
  (1884,390,141),
  (1537,480,113),
  (1135,652,82),
  (1164,638,78),
  (820,909,58),
  (1623,462,122),
  (1080,696,81),
  (665,1133,53),
  (1683,451,129),
  (1338,568,101),
  (1475,516,113),
  (1585,481,121),
  (1428,534,110),
  (1374,555,106),
  (1714,445,132),
  (1690,453,127),
  (1616,474,120),
  (1192,643,87),
  (1049,731,76),
  (1563,491,117),
  (905,848,68),
  (1508,509,113),
  (1271,604,95),
  (1127,682,84),
  (1589,485,115),
  (741,1047,53),
  (1205,644,90),
  (1083,717,81),
  (1393,558,104),
  (1898,410,143),
  (1219,640,94),
  (1449,543,109),
  (1457,541,109),
  (1397,565,103),
  (1811,436,135),
  (1234,640,90),
  (1688,468,126),
  (1904,415,144),
  (1855,426,140),
  (1664,475,125),
  (827,957,61),
  (1656,478,124),
  (1636,485,125),
  (1376,577,104),
  (1339,593,100),
  (1361,584,101),
  (835,952,64),
  (1141,697,86),
  (775,1035,55),
  (996,810,71),
  (1222,662,93),
  (1492,543,110),
  (1398,580,102),
  (1066,761,78),
  (1607,505,117)]

private def mask22 : ℕ := 0x5f7df7ffffeffbefaddbeffd97ff3ddefbf7ffeb7fbfff7dfbdfb7bffdbff7fbfef3dfffffffffdfdff6de6f7ffa7fefbfdffeb6eff7bfefb7fefd3df7fffef77f7ffbedf5bfeffdf7ff7ef77fbffffffef6fd7fffefffff69effe7dbdfbfdf6ffef6fbbfb7ff7fbefffffbcffd9ff9fefedbfff77f77feffeffadf3efffdeff7ffeffff97ff3edefbfffbcfffdfdf27dbefb6b6ffbdfffbffbf7feefefd7dbf7ffeff7ffdfbdff7ffeffef7dfedfeff7dfeeb7fffffbfbbfdfededfefffef3eb77fbffb5dafffef7ff7dfbd9bff7ddfed7ffffdbffbfdffffff7ddffffefffffcfffbf6f3ddefffcdbffe7bffffffeefe7bf5bffbefffddb7facb7fff79fdfbddfdf77feeb6fffddfff7fdffdafdffbf6f7fd7ff3effdfeef7ffffbfeffdbb5bfdff6dbffbf9f7bbeffeffddfffaef77ff7dfdf7fbffbbffefdffffddf5fb7deffeedefbb7bfebffbfdfbffe7fffff7f6df77fbdbf7deff7efffdfeffdb7fdffffdffefb7bffffffa7bfdb37f7ef6fdfdfb7bbdde79edd6ffefbffdf7b7efefdfcffffe7dfff7fbeefb5ffef7fde7fffffdf76fbff7ffadb7f97fbbef35defb7ffffffff7ffbfb3dbfffedfbfbfff76b7efecfedfe7fbfbf7dffd77faeff79f7d7ffa7ffff76ffefbdfefffcf7fd7fdfeffffffbf7f7ffffd7dbfebb7dffb7cfffbf7bff977bfedfffb7fffdffbfcff5feeff59e6ffff3ffffb7ff77dbffbddfdbfffefdfdffffeff3ff7ff7ff67bbfb7ffe7fffffddf7bfff77f3ffbfdffffef77f6ffffbeffbfbe7f2edeffffbbcbfebbfffdffffbfdffbbdff5fb5b7ffeffeedfddb6ffffffdbeffdffeb7df7ef7fffdffff7ede6ffdffdfefffffefdfefffdfff3fff6ffddeffbfbf6fffffff679bfffdf7fdbff65ffdff7bffdfedfddfebfefffbbddad9feffeffff7fdf7bf5bb7bfffaef7fff7f7dbeefefffffedfffff6f7effdbb7b3efeefbfff7fb7f7dfffb2fd7ddeebfddfeb7ffbdfedfffde79fddb7ff4bbff76ffffe7dedf75f7fdefd6ffbfffed6effff6ddffff7fffb2ff75bfdf7f9efd7fdffdbfffdffefafff5df5fff9ffbfefffbb6fbfd7ffeedbfbf5fbfbefdeff3dfbffbedefd7ffbddfffb7fffffff779f7ffeff7bbff6f9febffff7ffedf5faff7c9ffdfed7ffefbf7beffefd7fbf7bfeff7fbfff7fefff6fff97dfbffffbbdfeff7fd7fffdffffe7fbedadfeeff5df7ffffb79bfffdb76f7ffffbbefbffeef7dff7fffbfff7fbbfffdfafff7fefffff65fafb74dfefffdffff6bbeff7f7ef3fffffffbffbfddfd9fefffdfff7ff37fb7fffdefdaffff9f6fbff7efeff77ffff3ebffbbff75bfff75f7ffefffdff7bbffffdeffaffe7f7ff7fbacdfdbedfffbf6dfedf7ffffffdfef7efe79febf6f76baffe7fedbf7f7797cf7dfb5ffedff9eefffff6ff5feffadffffb6f75ffffbcfefba5ffdb7fd7ff7fbecfbfdf7ffdfffbfdfb7f7fdedf7ffedf3ebffffeff5bf5f35ffff7fdefdbfbfd9eff7dfbdfffffd9fef7fda7bfffbfffe9fffffbfebffffef3ffe7ffef7fbffffdfeddbeffefefffffeffeff77f6fdefdf5bffbfcdfff7efffdffff6d7efedff7bbfffdb7ef7ffffbefff7feedbffa7fe6fb7feebbdff5deebbfbfeffffbdff7bf7f6fdeff7fbfdff7ffff6ffafdfef7ddfffefdbfbfcf3cd67bfff3dffdfffff7dfef6ffedff7fe7feddfffffffedfffbdfefbefffff7ed3ed77dbff7cfefd3dfffdf6bf4fffb7cff5deeffffe7b6fdfdffdfbffeefaddf7bf7ff6fffbaffffdfebb79ff9fffafbffbbefffdffd75bfef3fdfffbffaffffffdd7ebfffa5bf5ffff6fffff3ffa4fff9ffdefd6ffefb34bffffdf77ffefb6f7ef7efb7dffbfffffffff6ddbfbbfffff3edfdbbfbffdf7bedfe5fa6fffffefecdffff5fff9fffecfffffeffffffbfff67ffeff7ff797dfffffdbbdf6edbff7fbb4ffdffff6ef6ffbff7efffffffffdeef7e9efb7dd75fecffdf6effcdef9eff3ef7fbafff7dffbf79fff7ff3ddf7fb7d6fbbfd7fffdb7edefffddbdfe6ff4ffff6effffeffbfffed6fff5fefff7ff7feff37feffbdbfebfff7ffbfffffe6f7eff7defbf7deffffff7ff5ffdfeffbfd6d9efbfe977f7ddf7facffddfffecff7fbfff7f7edbefffff7b37b7ededf2fffffbfbeffbef37ffdb7dd6efffdff9feff4ff79affff9ffbff976f7ffffffffbff7edfff3ffefff59feffefffdfdffebefbbffbdfbfbffd67fbfff5bfdbfddefffeffdff6fb7dfff6ff7ddb6ffcd7ffefffdfaef7fbef9ffdf7ffdbb7ff6d7ffff9f5ff6ff6feffbfdadf7fdffbbff75fb7fbdfeff2ffff9f6f7fdffbfcf7f9fffffdffb6ffedbbdf7fbff9ecff7ffffffbffdaff6fffdfffff7bbdd7fdbcff7feefbff3dbf7ff6feff3fdfffbffbefe7deffefbbefffffffbffb7ffff7dff7d7df75bf7bfffe7dfcdffbefb76ffedbfd2fdfffb7ff7bfdffffeff7ef7fbbfff7fbfffd9f7dadffdfefbfdff7b7edaddb4fffd77feffb7ffeff5ff7f6edffdffbf4f6fffddafdedf77fffbfffaffafffff7edafded9f6bfffefdfffbfdeff7ddfff7ffb5de5ffdb77feed3fffffffd7fd3ff7fdf7f7fbffdeffb7ffdfbfbffbbef3dbbff7fffebbef75bfff7cdffbffd6ffbffffbffbfefa5bfdf3fff7f7ff3fffcbffffffbff7fdfcfbeffffbff7ddeebfffeffbdfefbf7fb6feffeff7fff7f36fefd7dffffbebff9feffeff5fefffd9ff97fdfdbf7ff7feffbdfafff6fb5ff7deffe7fbff3ffeef7fffdfb5b75deeb6ff7fdffb3ebfffeedefdafb77ffff7fdfdfbff7fd7fbfedfdfffbbfd6fffef7fffdffeb7fdefff7dffbffbfed7dfa7ffdf7ddeedaffef9ffbb6fe7fedd3ffbfffdbf7b3ffe7bfdffdf76dedff7fefffdffffffdffbffffff77ffff7ffacb3ebf6d7cfa79f7f7edffb7efff9f5ff4ffffefdffffff76fffb7cffddb7fffbf79effbfff4ffffe6dbcfffdf7fffbfebafde7fbff7fdeffbfff7defffffeedffffffbebfcfe7bfdfffbfff7ffffbfeff5dfdf7fbf7fffd37bfffbdfefdfffafbfefbdfe6ffff35dbdbfebefd7ffff9a7bf4defffeffddbfb77fff9fcfffbfff77dffffddf7ffcfbedf7feefffbacff79fff7fdafde7bfcf6ffedf37fbeffebf7dbefffbbffbcf6ffeff6fbbff7ebeff3ddffbf7ffcf77f3ddeddaffffffff7cfbdfaebfdfeff7dfafffdfffbffbfff7dffdf7fd76bbffaffbfffefffd7fdefbfcfb7bfffeefffffff7cd77fffde7bfffbefffbeed7fff7bfff6ffadf3fbffbb7ffe9ffff5decfb79fefbdfbfdf7fffffff7fffdff4b7cfffffffbfdeef7fff7f7effdbfef7fdf6ffeff7bbdfbfbeff6fdaffecffefefbffdfddafff6f7797dfaffbdffff7fbeedf5dbcbffff7ffeffddb6fff97ff7edb7fffffed7ef7dfbffbdfff9e7dbcff79ffbf7ff79ffffffeef7ff6e9feffdfffb7ddfedbfffffb6f7f9ff9fff6fbfef7ffffffedefbf4f3ffe6f7fd7fff5ffff77fadff7deeb74feedfff6dffefffdeff3dfaddffbffdffbeef77bf7fb7dffffed7fdefff7bfffbffbffefffd96fffddbdfbebf5ff7ffdf7fff7ffef7ffeffbddfdf3fdfe97efedfe7fbff7f9eff7ffbfbffbf797efffdfef7fffefaffbdff7f3dfefffdf77fedbf79fff7fdffbf5bfff7ffbdffdffdffe9f6ffff7fffdbbfd7ffffd7ffb5bffdffdaefedfb7ffef7fffefff9eff7fffed7fdf7ba6fb7f7ff7ffefbeeb7fbf7ffdd6dffef7fbeffbffaffefbfffffdfffedff5ffdbffffed6dfeff77df6f2efbffbcffeffedfcf3fffcfb7ff7dfef2fdf6f7fbff9efffffadff79ff9fffff9affbcdffd7fff5bfdff6fffdefdbfbbff7ff7fbefdff9eeffcfffffedbfff7ff79fedfef27ffebffbf7ffdd2ffffbb6bffffff7fbf7fffdfedbff65dfefbffeff2fffdff7ff7f7fbbcffffbcf3eff7b7fdfdfedffffe7fefff7defbbefffdbddf7ffffbf97ff3dff5ff7fbcf7ef7ffffdfff7dbffbfffedbefff7b76beffafdfdffef76bfddf7fe6bff9f7ffef7fffff35bf7fffdbddfff3fbfeffff7fbedffcf6fb3fdf7bfeffcff7dfddaffa7ff7df7fadff7ffffffff6decfffbf6bb7f6fd6efefffffbcf7fdfdfbffedffffe7fbdff7fedbfefee9effffdbcf7fff796cfbffe7bf79fefeefefffeffff7ffeef77ffefb5bfffefde7fffbbff679ffda7fffffeff6b7ff67bffbfff7fbfef7ddfdf3ebeffeffffdeebffb7ffbddfdfedfbebfebffdf7bbffffdf7d3dfffbedbf6feffeffffffeff79e6f7ff7fbbff7fffefbeff5ff6fbddf7d3edafdaff7fffebfdff7fa4ffcdffb6ffb7ffdfbddf7f7ffffff6fffff7ffdf2dfbebf7ffef7cf3fdffbffd7ffefdedfb7bfffe79edd7fdfefffbfeffeff7fe7fbf977f6effffbffffbfffeddbfbfef75feffbff7dfefffef7e9fffb7bf5b7ffffd2fdffdb7fbfdfffeefffbe7ffdffeffede7bfef7ef6fd7eff7fedbf5d7ff7ddf7ff5f7ef66fbffbddbfffefe7dbefbfdeff7ffeefbfd7fbfdbb5dff9affafffff76bf7feffbfffdfbdffeb7ffb5ffffb7dfedeffb7fe7ffdff6bffdffdedbf6bffdbdf3f9aff7dfee9bff6dbfffbe9effeed7d9ffbffffeb2fffdde7ffdff6fffffffa7ffdbffdfff2fbfcbffbefbfdff7ffefbefefffeff7dfff3ed7ff7fdf79fdffdff7fbff6fbfeffddffb3dff5bafffef7ededdb5faffbfbfefbdfbfbf4fbffffbffdefdffb37d7eb7ef7ffbdff7defdeff6ddbef7dff7bfffafffeb7ff7effdfeffe7f7fbeff7fdbffaebf7df7f6effffe5f37f6ffeffe7dfefbfdfedfdffffffbb6fffffefedbb7bbdfffbbeffffffffcd77b2ffffdefffff7fd7cdbfbffbfffffffdff7ffff75f6fdeddedfbffbefffdfef67ffdffcfff97ffffbfcffdde7fffdefbb6ffedfef3dfffdb6fbf977deed75fb6bfffffdbffe79ffbf6bfe9fddffdedffeff7fbffefdb5fffdefb6fdf5bfeffe9fff6ffefdefffdbfff7fffddf7f3efffbedd7dbeefbdf7fd6fdefbffff6ffeffdff5dfdb7fd67fbffafdbdb7df7ef7efeffbfffeffff7cdbfdbeff7dfffffdf7fe7fffb7fbeef75bfdfb7d6edfef779e5bffbfefbffadffcfffd7fdbefffdfdf76ffeffff6fffdf36ff7fbfdefdffff6f77bfdfbf9b7f7dfffb6ffbfbf7bbfff6fefde79fcbbefeffffd7dfeffb7defffcfe7bffff5deffbfdeffb7f3fbffbfed3ffb6bff9f7bfeff5ffef3fbeff7df7ffb5ffffeedeff6ffeffffff7bafdfffbcffefe7b7fff7bfdffeffe9ffdefff5bfedffdffd7ddbfb7fbfefaefbdbfefbe9ffffdff7bf6ffffe7ffffaffeffbfffffadffffafffedf7f7ef7ffefff7fffbeef6fdbdbfddf7feddffbbff76fffffffaffbdf3fbfff7ffffbafff5deff2ffbffeefbeff7bafff5fffff7bfefbfffddeffffffebfef67fffff5fe7faeffdfe7bffdfeffffbdff5ffcdefbfff7ffbdffdd7ff7cdbfbf6ff5f67fffdbdfedff7bfff3ffadfffbfed6fdffdffdfcf34fff9bdfafbf7f7fff7fbfff7bfefbfb66ffffffbefbfff7ed7ff7fbfdffdbfefbffb5feff36ffed7fff5dafbfddfedaffe7ff5ff79e7b7ddbdfb7bffbfebfefb5bffffffffbeeff7badff7feedfcfbf9e7fbefef9bff2fdffbfefff9fffe7fe7b7dffef6fdf7dffbfffffdfff7fff6bffdfeb6ffffbefffffeebeddfdfffff5feefbdfb7ffcf3db77fbffbffffb3f9fffbefbffbdf7dffffeedefdbffbcfeff7ffeffeefffffeb2ddefbffffe976dfff7dff6bf7bfff7fdefdf7bfdf7effdd77feebf7dfef7efbffadbbef6ffbff77fb4bf5fffbeff7fdbffffdfef6ffefbfffbeb6efecfb5bf5fbff7fdeed67ffeb37bfefefff5fffb7edfedfdfefdf7fffffed7ff7ddb6bfdff7ffcdbfbefb77dfff7efffbfdfffd77fefdfdff7fb7dfefffdffffcffefffffff6fdbffb796fd3cffdfb7fbff7fbffdffbfff3ebf7b3ffefbbfffcbffb7dfb7dfef7ff7fb7dffffffbfff7effffffffeb75be6ffddefffebbfbff9fefbddf7fbdf7efafd6ddffff79f7fbffbfbffb77bfff7dfffdb6f7dfe69edf7dfbfffdb6efaff7ffe5ff5b77fefff7fbdfbedeef7dffffffbbfdfe9bfff7fbcffdfff9aefefdffff7ffff3fffdfeff3fbef9ffdf7fe7ffdfe6f7cd3fbfff7fbfedbfdfffedffefffbbefaffb7bfddff97ffed9ffb7edefdfdfeffafffeb7fbfefeffaffffd7fbffdbfffdff5f7fffff77de6fbfffebbfd7ffafff6f6fd7ff2dfbfffff6fb7ffffff7fff9fff3ff2dfa7fffff7f3ffffbbdffdff6feffbffbcbfdb6edafdffdf7b3fff7feddedfedf77fefb3ffefffdfbff7fdfffffff4b76fe79ffdffdfef7ddfff6ffef9f7ffff6fffffffff6fbdf7edfffb7ffdffcbefffdf37ffff77f7effffbfbf5bf7dffdfef77ff6ff7fffbffd6dbfeffedffbedfb7ff7f3dd7ffeeffffefbbffeef7ffffbfeffcf67dbfdffffdf7fbfff3eff7fafbbffffdefdfffb6fffbffbfff3ffffbf797ffbdfff9f5fbfbef9fffbfbfeff5fe7dfffffdfefb7fe7ffffbffffffeffeffdffdfbffb7dffdfed6fbfff7dbff96cfed9beffdff7beffbffecf7eff6fffd7dbffffffffdfdf6ffe7fffb6f9fddedffffbefefbfef75bedbbffffdfefffdfdf7dfeff6ffbfdb7ff79f7b3cdffffcffef6ffffd7dff6ffdfeff6fff7dfdfffb779efdbfdbfb7ffffffdf7fba7b7fdffffedffdbfb7fff7f3ed3dffeff5dfff7ffa5ffffffbfff7fd3fffdbffbffdacff7fe6f77beffadf7fdfefbfbfed3ffffdfffffdffffff7dff4ff6defb3fffffaef7fdf7f6ddfffb5f7fff6ffffbfbeeffd9fefeefffff7bfffe7fbdde7fbffbefffb7dfe7bffffcf6efbff7fffff36ff7f7efbdbeefffbffb7ffffdf4f7f9ffbffd7ffbcbf7ff6ffedfffe4fb5befdaffa7fbdff7dffdfcfafbbdfffd6ebeff77bfeb7fbf7dfddfdfa7ffdf7efaefbfbf6f7ff7effddbfff7fffbfeffff67fffbbfbf7beff7dfbff7f9eeb7ff77fe5f7fffefeffedbf7ff7befffdf3ffbeff7bf7fbeff7dffffcdffdefdf5fbffbdd7ff6fdbfde7ffebfedfdf7dffcff6bffd3ff35fafffffeef3ffffffcfbeff7f2cfefbffffebfebfefbf9eeffdbffb6cffdffdbf7defdedfefdfebfebfedffdbfffff7fd7fbbeffdfefffefffdfffffffeffffe7fedd7fdafb7c97ffffffffe5fbcbffffffb7fefbffdefd3ffe7be7bf6f7ebffd7dfeff7fb6ff7ff77dfff7ffefb3effddfdfb5fffdfffffbf7ff5ffffbedb7baef3ffe7f6eff5bfebffbeefeefff9fdb75f7ebffd3ffbcb7fbffbfdfffbe5f77fefdeef7fdf7fb6bfffbefeddf7bf6ffeb6ffbffffffef76dffffdfe4fffbe6fbdf77fffbfdffefbfdafffdf7eb77dbefefbfdffefffdefff5fbef77bf79fcffffaebfcdf6f6fdffff4f7ffffdeffffbeffbffefffcffffe6ffdf7fbffdbfdecbf7fefb3dfb7db5fffd7fffff7ddf7b76bef9fffbffffffdb7ffaefeffbeffdf7effdd3dfefffddf7fbfd6fdfdff7fefdfdfffffff77df7d3ffb7deffffffff7ffffbbefb6befdfed7d9f6b7df7ff7fff5fe5fffdf6ffeff7ff7ff79e7f7df7fbeeb7ebffbedff5decfff9fffbefefbb5bfefffbbff67fbfffeffff7ff7fdafff6fffbeffb59bdfbdde6f7fff7ff5ffffffd6ddfffedff5ffefffd77defbf7b7ebbef65ff5bfefffffef6fff5fbfbe7f2edfdfffffeff7bafff7fe7fffbffbfdffdfb7ff7f7fdfefbfff7fbffeffbff7fdfdf7fbef9fffa7bedbfff6ffbfff7ffebbfdf7dfedffdeef7db7ff6dfbd9e6ffefeed7fdfdbffff7bf7f2efff9fff77fe7dffffdfaebf7ffebfffffffdfbfd7ebffdff9fdb7cdefbbdd3fba6ff5ffffbffaf9bdf3edffbeefbfffffb7d6fdedfffdf6ffff7edfffe7dffff7f7ef7df37fffffcfeff7ffff9fdffeff7feffbdfb7f7fff7b7ffffbe7ffebfedeeff5fafbf5f6efbfdbfffdf77ff7dfdff7ffff3ebefbbffbfdefffdfeefefdfddfcb7cdfffbdf6fde7fff9ffffefe7dfff3dbe6fffdf7fb6fb7ffff7cfff9f7bbffefffffb5deffbedf6bbcf7ffefff6dffdeff6dffefb7fef9afffdbffb7cffffffff7ffef7db779fff35bfefffbfef6ede7ffdfbdff7dbffa7fffbfedf7ffff7dbbfffefeef7effffb7bbffffdbefbffefffcf7effedf7be7f7e97ef7fdfffffffddf7ffcf3ffecfbff6fdfdfffdfcffedf7bfffe7fefff6f7ff6ffe5dfebf59ffffffffbaeb7dd7ef6fdbfbe5fbedf7b6ddfffbdfffffffbfd6fbf7bbffffbbffbfffdfff96fb7efffffff7ed7fd6ef7ffb5b77fff9bef6ffa6fffdffbedfffffff7fffededf3ffacffdffff3edbfbeff74fefbfddfdfefff6fe69fffb7dfdf7cd7ff6ed67dfebf5be7ffffedbbfff7dfebfdfffdfdfbef6effff7dfbdfffff6ffedffbeff7fbff9fdf7fdefbbffefdbff7ddbdf77d6fbafdfdfb7ff7ffff6ed3ffafff7f76feffafbf6fbfdefffdf7fbbffbdbfffffdefffffb7ff6deffe7ffef37f7fdbdfbfdfffbfdfffbefffff7b3fbefd7cfbfbbfb7fbf6b6eff5daff3df67feeffdbb7ff7b6efbdfafbfdf3ef77deff7fffcfb6bfeffffedfb7f77fff9affff9ffbfefffdbdffffefff6b7ff6cffffeef3d9ffd7df77bf5fb7feff6fff79fffb7ffebeff77feeb7ffeef7fffffedf77defb7fd7fbb5fbd9efbfedfffe7ff4f7ff7ffeffbfffedffb7fdfdffcff7fffdfdfbffe7bffb769efd6ffeff7ffeedfdfbf9efff7ffedbeff5ffeffedfff6dffffefb7fb7efbfff5ffdf7fbffbfefb7ffcff7ffed7fdafbfeb3ff76dbdfefffefbfdffffffaf9bffbfdfff6ffff9bfffeff7befffffa7ffebfffbdffdbb7ffffefffeffdfafbb7feffffd77feefb4feffbffefdbfbb7f7ffffff7bb7ff5fefbfff7fffefffde7b6fd6f9ffffeffffbdfb7fecffdf7f9fff75fffbbdff6ffffa7bfdbf6feebffd77ffef7fbf6fbfff7ba7fb4ffff3ef6fffefffdffbbeffddfffffffff3dfedfb7ffeffefffdfffaeff59fefeef6fde5bbdbfedbdf7dffdfbefffbfcffdbaff77fff9aff7dfbffbdfffd7cfedff7ff7d7fbffde7dfffbdb76fffd7fbe4fffbf7fefd6fdfefbffeffbff2ffeebf6df7f3cfbfdf7b77fefbfefffbf5ffffffbfdffddb6ffdd76fecfeffbfffffffdfdf77ffffffbffdeffaffefffdbeebffdbfffdf7ff77ffffb7ff7f3ef7efbfde7ffcbfeffffbfdadffffffdfef7ffbfbe7ffdbfff7ff75bf7bfffffdaef77ff4bfdfe7fedfb7fadbfffe6dbef3fdf7bfff7fbfeff7ffff76defbefd7f9bfffe97fbefff7ffffbff6fd6df7fbfefff9fff3dfffbfebb5b7ffefd3ddffffff7fbbcfe7defffff7fbfefef9f7ff7df7f7ffbfbfff7effef6efbddbdfbdf7fbeef7dbfdffff67fafd37befff5ff7dfff6dfbffbfb779fefefff7bfdf7ffbfdffdf7bbefffbfffefdffb77bfef3dffddffffddfe9fdf3dbeeff5f66fefdaf9e7ff7fef9fffffffdff7bfeffdfa7dafff5d7ffaedefbbdfbd9ffffef6dbfef7e9ffb7fdf5ffff3eff7fffffffefffddfff3ffafdfef7eb7ffedd77feef76beedfef7ddfff3dffef3edef9ffffcbf7ffdfbdbefbffff7f2fdf5dfff7ffe7dfdfbffacffff6fdbdfffff4f3fb7fdffffdfbfffff67bfefedfbdbb7fff9fefeffbfffffeff7ffefdffbfedffffcdefdafffef7fd7cdfdff7fffbfffbcdafdfeff6bf7fbff67feffbf9ff9bef7fbfff74deedaffe7df4fb5beffefd7ddfebf7d77fefdbffb6ffdb67f6fdbffffff79fefefff7fffbbff67feffeffeff7fdffb7eff7dfffbff6fdfedefbf6fbffeff7ff3fbefbf7dfeffcdbdfbfffed77ffddbffb4bf5ff6ffef77ffcf77b7fffdfbffbfbbedfeffffbdfbfff5f7fdffd75bbfbf7ff7f6ddeffe6f77f77bfffbf9edfbd9f7f6ff7dfeffbfbeeffdd37fffb3dbefdffdffdfffffbeff7fffffefff7dffb3fff7ff7b7dbf7ffffffff7bf7f77beffffdf6f7c9ffdeedfdfedff7befd3ed6ffffbf5fffdfffa5dedfbed7e9bdfbfbedffedfedefffdfbdf3cfe7fedfbfff7f74dffbfedffff7fffdf6becf7fbbdfb7ff6dfddf7bf6f7eff7bfff2ddbef7ff76ffffadfbdf7df7fbfff7ffbdff7de7bbededfbeffffffffcffdbfffbdfeebedfffbfdfbff77fadf77ff7bfdbe6dbfdffdfff3e97fffdffffedff7feefffffdffdff6df7f2ffbddbfbf7ffef3dfb7faefffffef6ef3fff6fbdb6edfff7fbecff6fefbffd35dbcfff9f7dfefffbadfb7fff9afdf7ff7bfffffdaffffdb6fffffeffdfefff7fbffeeffdff7beefbfde7f7ff379fdf3fff7faff3ddedff6bff97cfedfe7f7dfffbbeffdfffb3dfff9fefbfff7ffdffffefdef9fdfffbf7d7efbdfb6ffdf6ffbdf77feeffff7effddfffadbfff6fd3dffdfbffbffefbffd6fffcbfe9ffbbefaffe7fffd76fbcfffbffffcff6becfbdfffbffdfffeddafbfffffffeffffedffcffed7ff7ef7dfffffddefdffff7bf7f3cdeff7ff6fdb7bffdfeb6ffeffaffbcfeff7dff5bf6bfdf6ff7edffdf5fb7f7ffedfedffffbfbfebbffffdffb7ffffb7ffffdbdf7fff7f7dfffffeffef7ebadfbfbbeffef7f97fdbfbeffbdfefd6fde79effffffefbffffffefffb7ff3eff5fedfb6fefdffd7dbf7ffffefbfffbffe7ff4ffef2ddfffb7fff9eebffdfffacbffdffd6dfefde7b37feffeffefffeb3ffffdbdff7ff7f76deff6ef6fdfdfb5fe7ffdffddffbf4ffff3fdaf9fdfffb7edfcfffbeffb7ff6daffffdffbf7b7edbdffdffdbf7bffb7cf6ffb5fffdeed7efffffff7fff7ffef3ffa7b77fffbfefffffffbef7fbfcdbffafffddefdbff6ffeff7cf7ebfdfb7fadf76dffffff6fbf7bfedfffaff7d9ffbfcbf7d7df6dfafffeffffbfff7bf6fbcdf7befff5fa7bbff6fffeff7fecbfffe7ffff67fbfbffd7fffffff9fdfbdf6ffaef77fbcffe9efdfffbfdfeb76d77b6edffff4f3fffefedd7fffffffbfffacf77fedfbfff7fedfefffffffd6fbbff3fdedfbff7eb2fff59b7f3fff7bedfff9ffff4bfef6ffffff6f7d97ff7edfdfb7fffbffdfffefffffbcf77deffeddeff7fd7fbfffefdb7ff4f7ff7ffefbfff7fff7bbddefdf6bfdffefadff7ffef7effe9fddfffffbb7deef6cf3fbfdbf6ff79edd7fdeff7ffefffdf37ff7fbdfeebbfffddf6fb7ff7fbcfadbf6fff977f7efbffaffbc9f7d6dff7bf6ffffe6f7fdffbfffbdffefbfdffdeff7fbf6d7ff7ddffbffdefffed67ffcbfdde7ffefefbf7fffd7ffffdffdefffcfe7ffcffdffdbfff7fffcfffdfdf7fff7faff6fffdf77fe7f3ffbfdedbbef7fdefff7fbfff7de7bffdfffffbffbfebeefefdfdfbff7fffffb7fa6ffdd7ef3ed3fbfebfeb77bbdffffbdfb7fffffdf77fa7b7fdefffff7ffffb3fdeffbfd6fdf7f7fd77fbefb5ff5fbfdfffefff7bfdbf5d6effddf7feffbdf6fbfffbfdfeb7fffff7efedfb7b75f7fdfef75ff6b7ffeff7dfefbfeffff7ff2fdefbb5fbff7fb7ff7dff7ff5ffedfdfbffefbb7fefdefdafffebf7bffdfdf7fbb7f77ffffeef6fdffbb6ff7dfdfbfbafffed7efffdf

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches22 : PLift ((OMA.PrimeProgression.composite primes 16 343791 64387) = mask22) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified22 : PLift (rows22.all (check 343791 64387 mask22 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct22 : ∀ r ∈ rows22, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified22.down r hr
  rw [←maskMatches22.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows23 : List Witness :=
  [(779,1051,59),
  (1101,745,84),
  (1596,515,125),
  (1349,610,103),
  (1303,634,92),
  (1184,698,83),
  (1389,595,100),
  (1224,677,91),
  (1429,584,102),
  (1329,628,94),
  (1971,424,142),
  (1469,570,105),
  (1593,526,118),
  (1783,470,131),
  (1757,477,129),
  (1266,662,91),
  (1259,666,91),
  (1823,460,133),
  (1170,718,87),
  (1558,542,114),
  (1551,546,116),
  (1230,689,89),
  (1209,701,87),
  (1770,479,129),
  (1565,542,115),
  (1081,785,81),
  (1154,737,80),
  (1134,751,79),
  (845,1009,59)]

private def mask23 : ℕ := 0x1efbfff7becfffbfffb7ffedbff27fe7f7dff7ffffb7ffeffeff7f7ffeffffbfdd7fb6ff7fffdbfffffbecfefba7bfebfef3fdaffaffffb7ffffdffffefbddf6fbed6fffdb37f7fbfdf7fdfdff79f7f7ffedfadbb7ffebfedfdfbdbfcbffdffffdff6ffebf7fffdf5ffffbcffefefffdfeffbffe6fffff7ff6ffcfffbffdeffbefbff77f3ffbddfffb7f7ff7fd77bf6bf4ff7b7ff6d9fffffff7f3dff7fb5ffd9f69ffff7ffffffb7fdeff7fbffbfeffeffdf3ffadfb7fef9befbf9aff7fdffbffffdbfcffffefd7fffffeef7fbfebbdde5ffff7dfeeffff7dbefbb7bfedffd7fdf7fbefeffbff7ffadf76dfebbffb7fb5ff6defbbff6dff6fb7fefd7fdbfff6f77f77ffedffbbdffff6fbffd7ffbfbffdfff7ffbfbfefb7fffdbfdffffebfff77fffff7ff5fb6f7ed6fdff9f6fff9fff3ddafdfebfdd7ffeedf7ffdf7f9f6f6df7dbfdbffbeedfffefdf7fb5ffffffdaffbcb7f9efffff7fffff36defffedefffff7edfffeefffbbfff4ffffbdfffbfdf7f97edfeff7fbebbfb7effdf3ffefff7bffbfdda7dfdfbff66bfffad9eff7ef7ff6eff7bfebf5fefb3efbdff6fffff7f6dfefdb7fbebfebffff7ff7ff5feffefde7ffdffdbeebfdfbfffeffff7fd3ff3fdf5fbfdfefbfdffff5ffcfffffdf3ffb7b77b7fffdfb7df7ffdb6fbeedfdffdfffbfff7fdb7feff7dffe9bffbdfedf77ff6dbef7fdb7fb5feedbff7dfb5f75bef97fffd9fef7fbffffeffd9edf7fff7f6dfbffffffdf7effff7ffedbfff7fdedfa5dbff379feffffffbefbf5f7ffeeff7df7ff7ffffecffdfffffc9f7fbdfb7dfdf3fbf7f7ff7fff6ff5ff6dfffeffe5fffbffbfffbfffeffffe7ffefb7bffffedeedefdffdbfbbfdffdbef6dfafbfff77fbefefdfff7ed7ebffffdfffbf7b6ffedfb7fffffff66dffdfddffffffeebbcf67fffff5ffed2ef6fdb5bb4dffffff7fbfff7df77bffdafffff3ebfed7cfb5bfdbfddfefffdf7ffffffffffadf67ffff77befd7cfedff7fffdff9fff6fdfdbfcfffb7efbffb7bf7d76fffffdfa6f7efeffecf7fff5ffdfe7ffcdffff6bf7befbeffeffffff6d77dbefeffffbbdf7fffedf7bfebbeff7ffdfffff7ffeb7fbedfffbfef3ef76d7ff3ffa7bb7beff3cfe7bfcfbeff7ffff6ffbdb3edfff3ff35bbfb7fdfefeefffffcb77ff7b7ef7fffff77ffffbdfbfff6fff9efdffff5ffdfbddfffffffffe7bfefefdbff7fdfdbfef76d7eff5badbf5fffdefffffb6f3dbffffcdef9efbff9f6fafffffaff3f97fffffb5fbdbf5bfeffdfefffef7dfefdeffefffefb6f6fbffffffffff6defbfef7ddfdf3fbffdecfefde7ffdffefeddfffbffbfdfe9ffff7ba7bb7fffdbff77bfebfffeefffdffdfcff7d66bfffefbeffbff6ef3edf5dfdfffdf7f3ffaffbfffddfffedfafffff7ffefdfffbfbfeffdff7f3ff6f9eebb5f77fffdfdffdbffd67dbffffbfdbfef7ff3fd75dbef76fffdfffefbafb7ddfeb3efaf9ffffffffffff3ffffbf7fe7d7cdfffecffdbfe9fdfeffeffffb66ffffbfffdbf7f7fdfedffff6f7ffff96efffbeef7fbfffffdf7db7ffedefbffd7ffe5bbfffff6fdefbf7fffffefbfffddefff6fff93efafff7ffffeffbeff5ffff379ffb7dfbfdfff74ff7f6cfedfb7fffbe7fffd3ffffffdd6fdbff7fffdffef77faffbdfeeffeffeb7efef9bff35f6fdeffffbbfbfffffd6edfdbf6bfdf7fffefb7ba6ffdfffbfedf5fffbf79fef7ff2fbfffb7feffbff7fdecf7edffbbef7ffffb37ffffbfd7fff5bfffffffcfedfe7ffffffb7edf7bbff3cdfff7fdfffe7ffdfe7deddf7ffff7dbfffbfde7dbebb7fe7ffffafbb7bfdfffb7fffffffbffdfffbefadde7fffdffbfdfff9b4ffefffffeffffbdbbff7ffefdafff5bf7f7ebfdff7fbffbef7f93ff7fdefff7f7fd7ffedff7ffdfef9edd7fdffffdf7ef6ffffdedf7dfefffeff5be6ffffffdfcfffff7bf7bf7fefd6dfbdbb7ff6bfdff5ffff7efeedeff75dbdb37fffb2ddbdbbfffffffbfedadff6ffedefbfed37feebfdf6ffffdffff6ffdfff9bdf67dbff3fbffffffeffbfbfffffd3ed77fbebfddefbfdf7dbeeff4f7ebfcdafbe7fbebffb6cf7ffbffffdfed3ff3fffcb7fff6ffdfbfffdfbfd7ffbffa7fefffdfeff2ffedbbfffddffdfefefbeebf7df7b6fff7df7fff9f7bffdfdff7fbff7fdaefb79ffff7b7edfff37fecffebfeb7cf3f9fdfbef7fd7ffffbf5ff7befdbefffffef7ff7ef6efbfdfffffffedeff37becffdfffdffd27dfdbfff7e9efdf7ffff7ef7fbbdfffdb5ffffffbfffffdfffbfff7f6ff7ddbeff6f7fbbffe7bf5ffdb7ffffdf7ff7bf7dfedfcf77befff5be7defffdfbef7f96fd7ff6dffff7ef7fdeffedffffffff7fbff3dfaef7dffffffffdffffbfdf7bfff7fffcbbddfffaefefdfcbfcff7ffdf2ffafff6f6ed7df6fbefbffd7fbfedf5ffffb7fffbbdfffde7f7fdfff7dfafdb7ffdff7feffbfbbdffdfeffafdffffff7ebe7ffffbffbff3fbf7dfefadfefb7effebeff7fbfebbfbffb7ff6dbe7f74bffffddaffbef3ddffffedfdffdffffeef3cfef9edff7bf6fbffffffef77fe7f3ff7fff5bfddef9feffdbbef3efffbfff6fff7ffcdfffbefefdedffdd77bfdfbdffcff7f7ff2fdbfdfefbeffebfddeddfff76b77ffdfa5fefb7dffeb3fff7ffeffcdfff6ef3fdf7b7f97ffaedf7bedfffdfef7dff7fe5ff5dfeffcfef9feb7fff7fbffeffeeff7d77dfefedfedf37fffffeffffffb7dffff2ffff9afffef7effeff5dbffbdf7fd7df37fffff7bffdfffe79effbcf7fbedf25dbffbfbeedfcff7bfdff6dffbfef67ff6bffdffbffdfd9f7ffdffefbdfe5beff7fb77f7ff3dfffffffeff7fde7dfcffdffffedd67ffdfbf9fef3dfe7fafb77f6ef2ffffbfebbcdefd3cffdffffffffff3ffbf9aff7ebf6d7edfdfedff59ffdbff27feeff7fffbeff7dffcbb7fefffcfffbf7fbdd6ff6ef67ffefb6dfffffffdfbeb7fffefffdffbfffbef779ecf77ffefffb7ffffd7fbf6f7fbffffff3fffdbf6beff7cf77db5fbeffedbff7dfffb7cdeff7fffdfffff5ffeb6fdefbfef3ff76deef7dff7fbfd7fffff77feff7cfe7bfffb7dbcf3ffffb3ffa7bbdf7ef7efffd7ddfdff6fefdfffff9f7fffb7ff3efffffdffcbefbedd77fe7fbfdeff7edbfde7bf7bfeffffefdacbf7b76dbef3f9fdbfffff9aff7fbbcf3dffffefdbddfefffdfef7dffd9f7f3ff76beffffff7bfffffdecdffffffffff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches23 : PLift ((OMA.PrimeProgression.composite primes 15 409365 18205) = mask23) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified23 : PLift (rows23.all (check 409365 18205 mask23 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct23 : ∀ r ∈ rows23, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified23.down r hr
  rw [←maskMatches23.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows24 : List Witness :=
  [(1358,638,103),
  (1284,675,99),
  (1775,490,125)]

private def mask24 : ℕ := 0xfffffb7f7ff7fdeffffdfff3dbf7dfddeddffb77ff7b3dfafbbef7cff7fefdfdff5bfffffdeff3fff7fb6f7effddb7ffcffed7fbfefaffbffffdffdaed75ffdffefffbbcf7fdfffffbfffefdfffffffff6edfff7dbe7fbfd77f3ff3fffff3fbe79fffbffecffef67d7ffffdedf7cffefffdf5ffffbfffffeff6fbaff75bffb7ffbfdffffd97ff7ffffffdff7fffffcfffbe7b7ffffdfdf3dffcf3ff7fd3efeffffffcdfefaef77fb4fbf9fff6ffffbefb76d7ff7efaf9ecfbff77bedfbfbbdbffb7ef6fff7dfeff7f7ffefdbffeff77fffdffffd9ffbb5feefeeff7fbff7ebfffefd7fdfffffbffffefbfffdfbfdf7bfcfffffebf5f7ffffdffffeffef6ffafdbdfbff3ed6fbfdfedfbdf3ff7efffd77ffdf7dffff3efefbafbfff7efeffb7dfeffe9fed7dffdffefb7feff7dfef9edf7effebbdfb5fefbf7ff79fdfedfedffddffdfef6ddfdfbfff79fff2ffb7ffef7fb7fdbffffffcf77f7ddffbfefbfd6ff6ff6fdfef3fff7fafd67fbfb3fbfff7ff6ffbfb7dffffbef6fdfebfcbfffedd3ffeff76b7fbbffbf9b5f7ffe7dfffb7fedffdffef7fdbf9ffb3fffe9fff67ffdfbefe7bfefb5fbff7ed7fbfeff7dffb7edfff3ddffbaff7dbf7ffdfffdf5fffbffdfdfbffe7bf7beefffdefdfefbcffefbdd3ffefb77b6fffcffdff5bf7dfebaeff7ffdbfdfeffbdd2ffb7f77ffefbddf7bfff7df77fefdf5bfffb7beedeeffffefb37ff7fffdbfdfdbfeb7eb7ffef9edffffeeffffffdbfffedeff7dfbf

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches24 : PLift ((OMA.PrimeProgression.composite primes 13 433202 4336) = mask24) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified24 : PLift (rows24.all (check 433202 4336 mask24 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct24 : ∀ r ∈ rows24, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified24.down r hr
  rw [←maskMatches24.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows25 : List Witness :=
  [(1253,703,91),
  (1824,484,134),
  (1780,496,131),
  (1663,531,122),
  (1285,693,96),
  (1330,672,98),
  (1213,738,90),
  (1874,479,131),
  (1320,685,102),
  (1311,690,102),
  (1138,795,88),
  (730,1242,58)]

private def mask25 : ℕ := 0x3ffe6defff7deef77dffffcfefff5bf6deeffed6dbbdf3fdf7bbff3fffebf5bfffafffdffffbfbeefefd7ffbfbbfbeffbdfafbffff4fff9efffdfaff7fdffb7dfe5fbfffcffed6fde7ff5b7efffffedfdbeffffb7efbcfbdfb7ffc9ff97fff7bfebfdf77feeda7dfdfb7fe6ffdf7ffbdfffde7ffffeffedf37deffbeffddfdbbfbf7decffdfb6f7dbffbbffafbefffefe7f6ffbdbbefffd6ff7ddb7fedf3ebfebffd7ffaff76f77ffffef9f7fbfffff7ede5dffff5dfff6efbffffff7bf7f7fdfd9ffffdbeed6ff75feebfdf6fffdfffff7b7efeebfffefffeffff77bfff37feffbff7e9eeff5bf5bf7dffd7df6fffff7cf7fffffe7df4ffdb6fdffdf7baebbdffedbffaf9f4ff6b77fbffafdfff769f7b7ff7fbffffdfffbaffffffdbb7fefffff3dbbeffef7ffafdadfa7fbff77ffff7dfefffdbf7f7dfffbf7ff7feffadffffeef7ebffbbffedffffb7f6fdfffefdffb37fefd7cffddf7bf7dffffefb7ffdf7eff7f7ddfffedffdbfffeefbfff6b77bfefffdfffbffbff6fdfefb5bbfff5fffdeef6fdfff7cdf7b7ffffbf6ff6dffbeffefbefffed7effdd7fbfcffff7ffbdf7fffebfdfff9fffeddefbbebfef7ffb7de7f7ffeffbff77ff6fffde7feeffddffbf7ffeffdffdff7fbebe7bfdfb5be5ff5fffdfff6ffefffdbfe9fffe5fbdb3ffeeffdfafdf5fffffe9effe7dffb3efffffedffffebf6ffef3ddbfdfefbf9f7bffdfdfa5bb79f7ffdff7bfeff7fffbefffffeff3ff7ed7ff6fbbfbfff7fbaed7fbfdf3ffeffeff7dbfef7fff7fefde7bfdf3fdffdfdf7fbafffddfedbdf7ffffb7ffffffffb7dfff7eb7fdfefefbf7fffffffbeff7fbdffebefbfed3f9afff7fffffefb7ffffbff6fffdffdbffbbfb7efffd6fff7fb7bffdefff7facffffeedfffffbadff5ffef2ff7fdf4fbffffbbfffddf7f75ff6f3dde7deef7fb7ebfefb7fe5fffbf6fffdf7ff7f7ff77dafffdfefbfffe7ffdffdfe5f7fdff9feffdbbeb76bffdeff3ffa6ff7bfffbffefdeffbcf6fffcdf7bedfffdfff6ffafdfcffef76bfff75ffdff7b7fdbffbfdf7ffeffff7fdf7fffff4ffffaeffdfbfbfff7efaedb7beff7dffe97ffbfffefbfb6fd7ff2fbfdfffffffbdffdffdff796fffeffdffffb7f7ffeffedfbcfbdfeffbfdef9e7b7efffbbedf7ba7f3fb7effdf77fbffbff7fffcdbfffcfffb7ffaddefdaff76ffed3dff7feff7cdfedffffddfff3dfff96ffefff7ff6ffeffcfffffff7f9f7f7eff7baffbff7ff6ffe7feeffdf6fdbddffffff3fd7797dff7ffdfbffefdaff7ddb6f379efdbdf3fdefbffb77fefff7deffffff6befdbfbbdbfdfeffeffbfffdff5feffbdfafffffb7dffdfefffbeffbdfffbbef6dffcff5de7feffffbfebfef76fffdffbe7f7cd76ffff77badff5f7effdfefdfeffefefbbffbfffcbf6f7effefffff5bf7f7fb6ff7fdb7f77bfffbdfbfdbefffd7ffedfffbfff7fd6ebeff7ffeffbdbeff7fda7dffbbff77feddfdffffb7f769fff77fe5bbcfffd7edffff7ffcfe7d7efbfbb7b74dfff3efe5bffffdf6fbfcf3ffeffb7dffdefff7dfdfffff6fbdfefffcf7ff6f9fffbf9bffb6feedfffedbf4ff7befb6efffbffbfed7ff7dfafffffbeffff7ddf7ffeffff77faef7ffffb7fffefefdf5fffffedefffffbf9f7fbcd7ff7fdefff7f76ffff6dfbfbe6f7c9ffffefffffdfbff7fdffd3dfbfbfddfffeef7ffffffdfefbbffefdeff7fdfed7cfbdfaffbddefdefff7fffb7fff7f7fffdbeff74f7ffaedfd9fff7cfffdfcfbfff7fbdbe6fbdfbfbfff37fe6feddfffffffefeeffff6fdefb77d7ebeefef9ffff5bffdfddbdffff77ff7f2fdeffedf7efe7dffff7be7ffff6ff3ddffff7fbcf77ffffffdedffef6efbcf37bafbfdfee9ffdefffdff5ff7bbfdff9f7bffffef7dff7fe6fffbfff7dfb7fbcfffbeeffef3ffffbfdb669ffffffaff7ff77ffff7ddbfbfdd6fffffffff5f77ff79fddfffe6bfcdfeffcdeffa6ffff6fdfef3ffb7ff7dffd3ffffdecbf7fffbeffbffefff7de6dfdfb59f5f75ffeb3efffdfcf779ffbfffadbbfffdffffffdf5feffff9ffbeedbdfbffbff6ff6edf7dfff7ff6fbffdb7dbdbfff7fb3ffedff5b77feffbfdffdf6bfddfffbff7fbffbffd7ef7cfffffdffeff6ffeff7fffbff9f6ffffbfffeb37ffefafdbfffff37beffbcfedfe7f77d7ffbfdf5dfff3fdffdeefbffeff77df6b7ffefbfffbedfffffffdffcbf7ff6fbfd37ff6ffdf6effff3ffefbfefffb7dff7fadf3edfffefd75ff7ffdbff9acfaffb7ff7ffffacfedfbefbfffeffff7dbbdff7b7ff2fdf7ffdfffff6ffdfeddfcbffff6ffdfbfdb7b7fdffbefff7bfef3dbffffcfbddfffffbffbffde59ffffdf76beff7fffdff7d6fdfcf3fff5ff7bf7fedf3fffffbfbfeffff7fffdfbfd7ffbedffbfff7edffffff2dfefffc9ffbeffb5fbffbedfededffffaffbfbf7dedfe7df4ffdff7fedfbffefbb7beffbcf7ffe5ff7de

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches25 : PLift ((OMA.PrimeProgression.composite primes 14 440430 13995) = mask25) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified25 : PLift (rows25.all (check 440430 13995 mask25 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct25 : ∀ r ∈ rows25, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified25.down r hr
  rw [←maskMatches25.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows26 : List Witness :=
  [(1240,737,89),
  (1432,639,106),
  (1572,583,115),
  (1455,632,106),
  (1787,519,128),
  (1869,498,134),
  (1323,707,93),
  (1535,610,110),
  (1484,631,106),
  (1477,634,105),
  (1321,709,94),
  (956,980,67),
  (1754,538,121),
  (1854,509,129),
  (1926,490,134),
  (1772,533,123),
  (1697,557,119),
  (1501,630,106),
  (1932,491,139),
  (1533,619,113),
  (910,1045,65),
  (1562,609,112),
  (1050,906,74),
  (1333,718,95),
  (1119,859,84),
  (1105,870,83),
  (1309,735,95)]

private def mask26 : ℕ := 0xfbf9ffb7edefff7fffbfffeddffffef7cbf7bffff7fffbfdf77f3ddffff7f7fbf7dfddfdfbdfb7d67ffefbffefbf7dffdfefedffeb3cdefdfdfafbe7ffdf7ff7ffffba7ffdb7efeed77bfffb7ffed7ffafffeff6bf7fbffbffeffb6df7ffdf3d9ffff7ffef6fffffbdb7dbffb6edfd9bfffcb77ffffe7fbfffefefffef7dbefffdbfff7ffef9ffb77f67fedf6fdfcf7fdf79bcffddbdfbff6ffbff7ffffffcdeffbfffddffbfdf7fb3ddf79fdfffbe7d7dff5bbdff7feff6ffffff5f7dffeffdd7fffef37fff9bff3fff7f35fffd6ffffffcb3fbffd6edfdfeeff6fffb6ffb79f6f7ebfffffdffbfffb7fffdefdaffffbfefefffdf7fdffbf7deeffcfe7bbfbf6f7fffff77bb6ffe9ffb6efbddafff7d77f2fdaddbeffff7f9fcff5ff7ffd97fdfff2ffffffdff6fffdafffcffffef97ff379bdbbcd7e97ffefbfdf36feffadffffefff7ffebfedefffdffefffb7dfbdfe5bfffeedbefffff4ffcbffdfffffdfffb7bfefbcfffdbfffddffbeff77fbff7cde7ffffbfdaff7cfffffefedbf6f7ff7697fff7feeffdbf7fefd7ffeebfdfffdefdbfdfefffbffffef25befffffffb6edf7dbdfffff797ffbdde7ff7bf7b7dfffdbdffffffffeffffb5bff9effafdb7fedfbdf7fdeffffdeffffb769fffbdfefffeffe93fd7f9f6ffdff7f7ffefbe6b75b76ffefff9fffffbfef7fd7fbfcfffffff6cd7fbf7f7eff6beffbffefb7fdfff3dffffaff7fdefb3ffffdfcfffde7dffdadfefffdfffffffe7dadffffefbedfbffefff7f6ffbdfefbeeffdbf79edff7dfcb7fff6dfffe7beffb7feffbedf7ffefbfff7bffdefdeffffffefefffdfefffffeef7ffbfffffbffe6d6ffafbfff77feebbffb7fffffefffd7ff6dffdffedfffffde5ff5b7cff7fbdd7ffbeffdb7efaeffffe7f3ebfffeeffffb6fffffffbfff7bfcbbefe6fffff7dfdffebf69fffb5bfdff6dfef7ffeddf7ff79fff3df3fffff7c9ffffedb7ffff3e97f9fffffffdbf7f76feffb7feeff5ff7ffdfffdffbbedffbbdfeffeff7cf7ffffd7dff7bb4bffbbedffbf7bfd9fff6fffdffdfffd6fd6efffbedbfffeefbdff7ffff3fbffdfdffddfef7fd77fbffefff7f75fefd2fdefffdb7fff7fffffdbbeffeffefbfdbfbfff7ddffbfdff7fbebffbe7f7ffbf9f7bf6b6ffffdafdfdfb79ffbfdfef9fffbfd6f9eefffdffbf7bf7dbffedff6fffff7b7ffbf9fdfbfffefedf3ffb7fbdf77f7edf7bedb7ef7efeffbffeebfff77f3fff7fb7ffddffbffdf5bfffbfffffeefffde6bf7fffb3dfaffffffedf7bfefbdfb7fbfb6ff3dfffdfcbfdffffbffefffef7fdff9bcf7f9b7fb5feeffff6dfb6fffff79fff3fdaff77ffef6fdbfdaef7ff76fedffffefbffd77dafd6f9f7ff7feefffdbdfafffffefbfdf65bf7ffcfefbffff7dfdf7ffe7b7efbddb6b7cdfff7cffffaffffdffbedf7ffbfffdd7edfcde7be7fb7f7ffffdaffffb7f9e7d7eff5bffffffffd7ffffbbcfff9ffffdf6dfeef7ffffffddaf9fefbf9ffd7effdbf7bffb77ffff3fff7fbffeedffff7dfffffffefbffb5fbfbfff7fbeed7dff4f7efffbfdfbffb6ff7b7ffffffdfaff3dbffffcffdbaefbdf7fdffd7fff7b7fbfefadfefdfdff7bfed3ef75fffffdd6fdbfdffdfeffdfffbbfdfffeff7697fb2efb7bf7ffdffff7ff7fffdbf7dfffeef7fffdfffffedfffadfeefb7df7fbffaf9bfff5feff7efefbb7bfefef93ffffff7ffdbffbfffe5fe7fbdbfffedfb7fe7fffd7fdfdfeffefff7f7efefdfffbdf3f9e7ffffb7bfdff7fefb2effddf4fffdfff6cf7dff7ffd9fffbffa7ff7f3ffef9efffdffeffffe6f6fff7fefb3ef77bbdffffaffffffedfcfffdfff77ffff7efffdffb7ffffdfedeffefffcb7efeffefbfdffebffffcfb7be7bfddfffbeff7dfcf77b67fedfedfbff3eff69feffffeffbeffff2ff6fffff7dfef96fdfffffb7fff7befdffff7f7fdfeb7fff7fecbfdfe7f2edb7befffdbffffdfbfffcfbfd7ff3fff7dffb7ffffbbedfdfb5bf7fefd3efaffeff7dbf7f7ffafdf7ffede6fefdf7fadff5ffff7ffbf9edfbcb7fdfdffddfdfbff77bfdfff9bfbfff7ef6efffbf6fbfff7ffef2fffefffd7ffbffa7bfffbef7ff6ff7dfe5ff7ffefbdf7fbecb7ebf7bbdffdfaff77ff7fbff7ffbff7fdfedafdffbfdf37beffeef6ffbebfeff6b7cff5baefbff7ff7ff77fedfbdfffd7cfffbe6ffdf76ffdd3fdbfffffefd7cfefbffbbfdeef7ef77fbffbebefd3ff7fdb6ff7dffbfefffdf7fffbfe97cdffbfdbbfffffbfd7ffeef3ff77faff77deefb7fefb7efbfff7ffef7edffff7dfcbbf9ffffddffbfef7fb77f7ffe7fa7fbcffedfffbfbefff79f7fbfff7ffff7ff7fbfdd77fbff7ebe79fffbfdb7ffff7fbffdef9f7bfffe7bfcfffbffffdd7fb3ededdfeffffe7befdf5ff5ffffefdfffefffebfdffffedff7fadffebffdfdfffdb7bffffedfef75bfdfbfbf7f6ddefdf7ff7fffffefbddedf7c9fed6fff7feffb7f77f3ddbfff6ff5befbefff5ffefbfbe7d3ff2dfbff3edfffefff7bfebf5fffbbffffdbff7edfffffffffbcf3ff7fdfdff5ff6ffffffdfefe7fe5ffff7efaff35feffbffffdfdfbfdafffcdfebeff6ddf7ffdff7deffbfdf6f7db7fbfdfbffb6f7dfefffef77ffcffdbfed7fdbf9fef7ff76fefffffbffbff77ffdffffffff5ffffbfd7ddbff7edefffff3dde7bff9f7fbfde5bffffedfedfefffbf5ff7bf6faff6fdffff7ffffafdfffbebb7f7f9fffedfbff75ffff3fdff9fef75ff79ecdffbbfb7fdf6ffddeffbcfffbfebfff7ffb5bfdf6fd6fdbfde6fb7fefbffd6dfffff7ff7fbdfbfdbdfb7fffdfff77ff6b7fff79ecf6ffeeffdb7eb7ddfffbdfff977fecfbdbfeffdfffd7ffb7fedfffb6ffffde7ffdffeff7f7ffefbf5bbffffbfef6fbbffb5feffaef7ffbfb7ffffffffed9f7ffdfe7f7edf5bf5bfff77f7ff7fdfcff5fefbfffffffcbf7d7fffefaddf5bbefeefefde7ff6f7cbffffffafbbfbf7ffffefff59e5fbeffebfdf3fbfefffdf7fbfd7fbf7fb7beedbfdafdefbffdffb3ffb5de7fbfdfffeff7fbffbfe9fff6efbfdf7fffffffafffdffdf7fff6b7effdffebffbf6fbedeffe5ffef7fdffffffbdf3ebffffdff7fefff5f6fdeffffdbdfbeff7dfeffdfbfbfcffef7cff5ffffbddef9fffbffeffbdffffefdffbe5bbffffbfdf35dbfbffff6fbef27ffdfffdfff6fdefbffffedefbbfdfffa7f7efffb2ffbffbff7ff6797effdbbebbff7fdafdffdfff7cff6bbfffffbdf77beffbdf7ffe7bffdeefbefefff5bb4dffb7cdffdfffffb7ef7fdf7defffcbf6dfcffffffff5ff7fbcdbf9f7bfffe7dfffefffff36bff97ef7fffff7edfedfefe5fbff77ffffefd2f9fff7cff7f7ddffffefffb6fffffffffffb7b6efbfdf7dedff7f7fbffdb7fadf3ffffdfefbfbafbfedffffff77ffdbffbeffffdafbf7ffdffebffff5ff6fbeffffeedbffeffffb6ff6ddbfffeff5ff7dfddffdfdbfef7fdbfffdbeff3cffef6fffdbf6bfebffd7effdbffbf7df7beffa7ff7fbfbfeffdf7dffdff5deeffcfe7de7bffffedeffbddfefb6feefbdffffedf77fffb7ffffbbeffeff7b7efbf9f7bfcff7fffdaf9f7fbff7ff7ef75faffbdfffdfdf67ffebfeffebbfd6dffebb6f66f7df6ddffbfff6fffeffdffeb7ffef9fcfefdafb77d76befdff9fcffefefffffb7fe5ff5bfff7ffb79fcbf7fe7fefdffdfcfbffefffffb7fbff7dfffbafdefdfcb75fffd6dd6ddefbf7fffbbcfeffeffbfbfff7ff77bb7fffbeffefd779f6f75ffebbfff5faebffd77dfcffdbbff3ffffffef6dffcff4dffdaedfdffffff97fb6ffeffbffffdffdeffffbbffffb7ffbffff9efbfdfe7dffd35dbeffffefbfdfa7de7ff6dfff7fff7ff7b7f9efb7cdffbf7bf6dffffefffffdffdf669efd3dbfffbfff7ffdf67be7f7ffe7fbfffddfef36bfff7ffbdff5bbfdefbbfdffffdbfcdffd6fffffe7ffdbfeffdffffb7ffcfeef7fd37fefbb7befffdf6fffff3fb67ffddb5ffefffdffb7efedff7f37feef3effdbf7bff9efffefffffeffdff7beffadffcffdd76fedfbffbdfffde6d7ffefdecbfff7f9efdfdffffffbf7fbdfffdeff3cf7ef3fdf7dffff6df7fbef3ffefff79f7fffff7bbff7fdf7ffdf77fffffff7fd2efefbfff3eff6fbfffdfaff37fffb7efedfeff3ffefd7ffe79bffbfdf797ffefdefbfeff7b7ffeddf5f7ebfffffd3ffb6fffbffd3fdffdefffefefbffd67fffbbfdeedbef7fbfdff4ffff7ef6ffbebb5dffb7ef7dffeffddfeffdff7ff5fffb7fbfedb5fedfb7976feefeffe7fbdfeebedfe7fbfbbfff6f7fff79fdffff7ffbfdeffb7bffdefffdd3ddefffdbf6fbfdafbadfff9e7fffd7ffbeffd9fedfff77dfeb7ffffdbdffffbfff7ff7ffcfefbbfff7deffefff5bffb36deffedffdff6ffcff7ffdfef9ffffcbff96efffbe6fb5ffefaefe7ffff7fbef9fff37ffefbfdf7ffff7ffedbfed7ff6fdffdfef779ef9fffbddb7ffff77ffdfbfffff7df7efffff7bfdffd97ff3fd37bffbf5ffefffff5faefbef7ffbdff7bffffed7edafdfddbef36ffffeddefbffffef7fbfcfb79eefffbe6ffdfbdbedfbffffffcd37df6fffbf7beff3fdbff3ffefffdfbffffffff6fdbff7fbffff7befdfef

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches26 : PLift ((OMA.PrimeProgression.composite primes 15 456940 26081) = mask26) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified26 : PLift (rows26.all (check 456940 26081 mask26 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct26 : ∀ r ∈ rows26, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified26.down r hr
  rw [←maskMatches26.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows27 : List Witness :=
  [(1792,547,127),
  (1110,885,78)]

private def mask27 : ℕ := 0x7deff77fbebffdffdfcf7fdb5f77d7efefd7fdfff7ddffdbdf3ffbfffdbfffafff7feefbeff7f6fffdfb5fffff7dfdda7ffebfdb7ffeffffffebbfbffd3effdfffffedfed7fdff9ffffedeffaffbdbb7b77f76baedfd9fffffbefffdf7fff7fbff67ffddffdf7bfef7edffff7fedf7ffeff3efffdadf36dfffeffff9ffffdffffeffbf9ffbff976ffdfffbe4f3ff7ffeddfdfe7bfdfffdbfd6ffefbbdbfebbdd6fffdfb7fffffffffbb7ffddffb7fff5ff4fbdfefb6ef7fbffff6b7ffffdefbbdfbe9f7fffffffaffffbfffffdefbfdf74feffbffe7ffff7e9ffd7dff5fbfbf4f7fd2ffffbffff5fef9bff6ffe7fffffff6cfbffeffffdfed6ddfffbfbf7fe7deefffff5bffbeedfdd3fdffb7ebffffff77be5f77feffbef7dfbff7cbffffdfadbefbf6df7fffdbfffef3cb7fffdff5ffcfffbffffcf37fe7bfffeffbff65dffbbfffff7cff7deff76feefefdffff6ffdbfffbefff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches27 : PLift ((OMA.PrimeProgression.composite primes 12 490112 2728) = mask27) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified27 : PLift (rows27.all (check 490112 2728 mask27 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct27 : ∀ r ∈ rows27, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified27.down r hr
  rw [←maskMatches27.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows28 : List Witness :=
  [(1405,705,100),
  (1649,601,118),
  (1549,640,111),
  (1684,589,120),
  (1221,814,91),
  (1199,830,89),
  (964,1035,69)]

private def mask28 : ℕ := 0x1f3dff79fffb5fffbfffffd7ff2fdb5f7ef7ff7fdef9fdff5feff3edafbeeff7d7fbfdffffe5fffbfebfcdffbf7bffbfef7ffffdffff5bf7fedffffbebf7feef3effffbdf7ddffbbffffbf4fffff7dbefff9ffbfeff7ffedf5feff7dff7f7fff7bbfbfdbf6feff6fdf6b7ef77dffff5faefb7fffbfef6dff7ffcdfff3fd6dffffffdef9efdfdffefffbf6bbeff5ffdffdfeffeddfffb7fb7d7ffedfbfff6fffb67ffff3ddfeff79f7f7fffd9e7fffffff2fdefdfef3efffb7dfef9f7bfdf76f7fdb7ffefffffef7edbfffefbdf7ef6ef3ffedbbefffbedffffbcb7f9e69bdf7dfb7f37dffb6fdffffffbe9ef9edfffbbff7fbffbfffefdffffcf67dfcfffbbefbdfeffefff7ffeffcbfffedfffdbef77feed7ffff9f7bf4d7effef6ffffbfdfffbbdf2ffe7f7eff6fedfffffdfffdeeffffbdfedfbff76fbdfefbfcbf6fe7bbfdffffef7ebefffefb5dbfb3cffefffdfffb7bbfffff6ffbffe7fffdfff3ffefdf6fffbf7f6fdb7feebf7f6fd3fdffdfefffb67bbffadffff7fbfebbcf7fffff7dfefd6fffdffcffdbff9fcf2dffeffcd77ffede7fbff7fffff6fd3fbefbf7f7edfdfeffedbf6ff7fbdfa7ffdf3fbffffffefdafffefffdbff7fff7f7effff7cfbfbf6ffed7ffefff7fafffebf7f6ddfdba7ffdfffdfdfaffefff5f7ffbdfeffbfb7fb7efbffa5fbffbddffdffffdfbfb7dfffbffdefdbefffdf7bfddffffff7dd77dffdffba7ffff77ffdf2fdfefbfffebffdf7dfcffeffffbffe7befb37d6efaff77dbcbfffffdbfffdffef77b7ef7ffefbbdf3ebffbeffb7bfefb7bfff6ff3fdffb7ff7efefdffffdf7fff6dfdfb7bffbfcffffbed6dfb6bfdff7f6ddfffb7ff4dfffbdfffde7ffedfff7efbfffdfffb6fffed7ffefbfd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches28 : PLift ((OMA.PrimeProgression.composite primes 13 495263 5053) = mask28) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified28 : PLift (rows28.all (check 495263 5053 mask28 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct28 : ∀ r ∈ rows28, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified28.down r hr
  rw [←maskMatches28.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows29 : List Witness :=
  [(1281,791,92),
  (1215,834,88),
  (1378,741,99),
  (1747,585,127),
  (1442,710,106),
  (973,1054,70),
  (1159,885,82),
  (1174,874,85),
  (1137,909,82),
  (1856,558,129),
  (1426,727,99)]

private def mask29 : ℕ := 0xfdfffe5f3ef67bfddbfffeffffffbbff75defffddeefaffedbb5bf4dff9fdfbfffff7cdffbfffbf9fdfffdeff7edfffe7ffdd7fdbdfefdf7f7fffffffffddfdf37f66fbff6fbaff3cdffbbff7fdfffb7deffadffffffbf6ff7bfedfffbfffffefdedff7ff5fffffef6ffafffebb7fff9bfffdffff37f6fdfef7ffeffbffffdfefefdf7f3ffef9ffd2fbf6fffffefaffefffefffffed7ddbffffbffd6fdfcff7ffdbb4fe7bffdffdedff6f7ff7efffbeff77ffffeef75ffffb59ffdfcd7dfffbf7f77ffffafff4fbcfeff7fdbfbefbf7bf6fefff7dfef7ff76dbffffffcbfebffdfdfefff5bfeffff6ef77ff6bffdeffffffdde7bf6bfefbefeffbffffffff6edfffe6ffdbefffffe7dffb77feefffdaffbff3fff6dfef35fefffffef9beff7dbfffdfeffedfefdbff7dfffffdff7fe5f3dd77dedff5ba7fb7bfff7fdeffeebbfbfe9fff7dffcffebf6bfffbffbffbffffbffff7bfcff7bffdfffffdeeb7fb77fbddfdfb7ffdff69fcffdfadff5feff3fdefbffbf6f6fffdfb5ffdfffdffdfffbfbfdffdf7eb7ff67bffff7ff7d2efadfeff77d7fffcffdfffffd9f7feff37bf7fbfffef7cf3fbfdffdfffdbff2fdfdbbffefffcf2f9f7bf6d7fdffd7fbfff3ffff9fedfdffff7ff7ffffffdffcfbff6eb6ff77bfffffb77d3fff7ffcffff77faffbddaffb6defd3ffedbedfb4ffeb6efe7fffff7fffbbdfffdf7ffdff7b2ffadff6ffffe7b7ffffbf6fff966fffd6fffdf7df6fbafd7ffedffeb6ff7dfffbf7f3edffd6ffefdf7b7ebff9bef7ddf7ffdffefbdfe7ffff7fdffdffff5fe7ffff77fbffffffdf7ffffbfffb7fafffffe6fbcfbdfffbbfffeb7efefffefbf9efdfed3fbf7f779f7ffffbdffdfbdde7dffff7ffffbffeffaff3fffeffeb7ffffdedfffb3fbf7ffefedff7f76deedffd779fdff7feffffd3fdffff7dfff6eff7fbffffde7bedffffeebbffffdedfffff6ffdbeffbffafffef7fdff9bef659fffb7f7ef6effdffcffdfe7d7fdffff7b7fdfffeeffffb5ffefeef6edfdfb6bfdf6edfffeffe5ff7fe7baddfdfefbf7d7fffef77df7b7dffeb7fffffffbf7be7fbefaf9ffff7bfefffdbffedffebef9effffffcfb7f7ffeffbf9eebfffffbfff67fffbffdfebffffffa7bb7ffef7fdf7bb6f3ffffbbefad9eeff7d7fb6ddfdfeffffdffffddfffbefffff7d6ff27df7bf7b77fffdfffbfb7ff7f9fff7ffa5f7dfffdaeff7fffbffde7ffefbfbfeff7d77bbfdefde7ffefffdfdff5ffcfbdfffd3ffa7df7ffdb7ebfdf77ffebffbffbfff2dbfffffffed2fdfdffeffffe7feef7dfb6f77df7ffdfefdbfffe9ff9eff3fff7ff5f77fbffefbfcb3ffffffffbfdefb3ed7effff7fdf5fbff7f9bfffdfbffbdbeff3dfffdfef76ffeb7fdbfdfdffcb7ef7fff5fb7ff7fe6daff77fedbfffee9eff67dbeffff77bbefbdffdb75defbbfdf7fbdff7ff7f7ffbffeef76bffb7ffeffeff3cff7dffdf7ffebffffedbdf77dffbfcf66dfffbffefffff7fb7df77fffff5d7efbfff7bfff7ebff93ffffffff7edf6fbfffffeff7f9e7fefffffbdffffeffedfb7bfeffdf7fdbffffdaff3ff6effefa79efbf4fff9bfd7ffb5fffbffdbfd7dff6bfdffffafdfffaff7ddefbfedbfbffbffbefffef7fbedbffbf6bfdff7fbffffdf693dffdfedfbffff92ffffbffff7dffffcdbffeef75f7ffaedefffdf7dbfefedffffbcfffff7deff7fbefb7ff76feff6dffff7effef3dffdbffffedeffbffffff5ff6fefbefdfdba7fff97ff2cdf79bdffeff7f7ff3ffe5fff96edffdffdfeb3cb67ffdfedfbefffb67d3ffbfdffb77fff9fedfdffff7dff7b7ffbfbefbffdfffedff7db6fbdfeefeefffbbffbdf7ef7ffffffdbf6ffebbff3fdedbf796fffdfffff7ff5ffefaef7ddfeff7dffdbcdaf9b7ff6f77feffffffdfbe9ffb7ff75fadff79f7feffa7defffefeedadfbffefbfebffffef7ffbfb3dffef7ff6dbf7bbedffd7ef6fdffffe97fbeedfffaff3eff6bfcdffbbfff7ff7f7ffeffefb7ff77bbdffffffbfeffebbdff7fb7ff6f6ffeffffffdfbedfffeffff9f7bffff6fffdfffeeffcd7fdeff7dbfffbffe6f7fdeffe7ff6b7fffff67dffffffe6ffef3fffff76deedfed759bfbfffffdfef6fdbfbfddf7feffbfbfcf7fd7fffdf7dbe6fbfde7ffed7fffffb6bffbedffffeeff7feffbdf3fba7ffff7ffeeffffbeff5fe7ffdf3f9ffff7ffff7ffb5bfcfffbf6f6fdf7fedfbf9fed7cff7bf7fffff6dedfb7fbdfb7bffffefeddf5fbedfffbfffdffcfffde7bbfdbd9fef759fef7edfffe4fbffffbfffbffffffff77ffdd7fdf5ffebeedadd7ffeffbfbfefbfffdfe7bb7ffefafffddfdfb7de7feffbffeef7effeffdfbddfefffb7fbedffffffbbfde7fadf3fbf7ff4fffbfff2ffbebbed6effefffbffbbff7efffffffbcffd9f7ffdd6ddbff7fb7ffbefa7df6f7ffef9fedffbedfff97ff3ffb7ffff3ffe7fefffffeefffdf7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches29 : PLift ((OMA.PrimeProgression.composite primes 14 506636 13972) = mask29) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified29 : PLift (rows29.all (check 506636 13972 mask29 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct29 : ∀ r ∈ rows29, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified29.down r hr
  rw [←maskMatches29.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows30 : List Witness :=
  [(1749,601,124),
  (1555,676,107),
  (1187,886,82),
  (1652,638,119),
  (1974,537,140),
  (1860,570,131),
  (1186,900,89),
  (1148,931,84),
  (1201,892,83)]

private def mask30 : ℕ := 0x1db7ffaedffffffff9efffed37bbdffd9ffdefff7fefff7be7ffddf7ffdbffff79bdfefdfffbcf7fb3ffeffffffeffff7dd3ffaeb7fdfeffdfefffcfffde7ffcf7dff7fbfbe7f7ffffdf4ffeffffaffbffadbf7bffdfdf3fbfff7edfffbede7ffcfffdefdfefeffaff75dfefffda7bf5fbdf77f7fffffe6ffdd7ed3eff7fffbbdb66fbddfffbfff7feffffffdff5bf7fffffffedff7ffffef9eed7fff7b76bffbefff7fffffffe7b7efbffb7bf5ffefffffffefffdfef9fffedfeebbffefdfdff5fbfbf7dfebfffeffbef3f9ffffdf7f9bff75ffffeeffdbaffbedff97ef75ffcfffbf7f7dd2fff5f7ff67bbdffffffb76ffeffffb7fffbb7dffbffd7fbbfbffbf7dfddfffffffd9ffbffff7ffffbcd7ef6fdf5bfeff7fe6dbff7fdf7b3fb77fafffddbcf7eb77fbff7fbffff6dfeffedf79ffbb7fe7f2cffffffbf7ffebafffdffef7efffd6ffbffeeffdb6ed3ddafff7b3fffebbdf37ffffbfbf7ffffafbfdbffffe9eedefbfff7cfffbeffffbaeffedf7fffff7ff5f7cf6fdffffdbbffbfd6fffcd27ff7ffffe7bbff7dfefffff7f9bdf77fe7ffcffedaffefdbebfffef92ddfdfbefffff7fbfda7fbff7ff7fbfefbfffefbfdf6f7efff9f6ffff77dedf37ffeb7eff7f7eff7bf5ffcf6fdfff7d9febbfdfffbffafbeebfcffff7ffeffeff7ebffbeefbdffffffbf6deff6fdefb37ffffbfd7fdbfbbefffdbff7dff5ffddfff6ff7fbbff3ffffdeddffbb6fffffffefdef9effbeffeb6edfdfafbf7f6fdffffffe7f37fefffffafdfefffdffb7ff75ffff36ffffaef75dfebf7bfff7ff7ddb7bffbf7ffddffdf7ffcbeeffef7fffdffdfefffffafbedbffb76fffffddffff7fffd3ff7f9fdfbed7f93ff7dff4f36feffffdbffffff7dfefbfdedbfffbdde7f7ff7fffdbffff7f7cfbfff4bfffeffaffedfeff37d6fffdf6dfbffffd6f9fedffbf7ffeff7bfff7dfefbf49fffecdedbfcffcf6ef7fff7bf7bbddf7f7fff7df7bb5f7fffddb7dbff7fb6ed7dfbfde7fbffefffefefffdfff9ffb7dd7dfe6fffbf7feefbffadfbddf79fff3fbfcbffd67feffbfff5f3fffffbffb5fbcfffbffffcffffb7bffdefdfff7ffbfbfcfffbedf6fffeff7ffef3fffffb7ffdfffffdfbfffdffffeff7ddffdefffff66dfdf3fdfeffeffeb3effddf7bbdf7ffaff6ddf6ff5dfffefd7ffbfff7dfff6fdfdfbdfffb6fdeedf7bffbffff7fbff67df7b7eff7dffdffffcf7fbf7dffffffbfb7fffffffff5dffbbf9fffefdffffff7ff77f2ffffdedffedf6f7dfb7fbcfb7d66ffddefffeff5f76fedfbdffeff7bffdbfff7baff3dffffffff5bbfff5fefdefdeffffbfdf76f7fde5fbeffef7ff7efffbf7bfff6effefbffe5fb7fffffff6ffbdfb7fee9bfff5df7f7ddffdbefefff5b3fff7decfefffefffdfffbfff7feff7cbefb6fd3fbbeff7b6ed7efbfff4ffeff6ffffafdeff7fbfebfff65ffdf3dffefeffeddffb7fbffbbfd2fff7bf7f7fbfdfb79fdf7fb6fffefbdfafff7feffefff7ffdf3fffebfdfedfbcff6bff9fdff7bffff4f7ffffff7bfcbfedffffffbfbeeffdf7ebfffe7fb7ffdf7ff6ffffbf5fb7bfffbef7fdf6ff7feefffd6fffdfb7fffbfcfbffffbbfdfed7ef7ddbff7fdf7f7cf6ffbffffdffb3ddbffb6ffede7fedffdfbffb5df7fffd7fdfcf74fffbefff7defbb7f6fd7dfafbefbfddfefbfff5bfdffdfefffffff9b6ffeffefbffe7dfeffff76f6efbfbafbffdfeffff37bfcffffe7feffe5ffdfffb7edfeffdffdffff6ffaff6ffffff7befb7ffffdffff797fffedbfdeff7cf7edfff7fbb7fffb7fdfcf6fffdf75bffdadf67fffbbebffb7cf779ffff7ffffbfdf7dbdff6be7faedffffffffffeffffb5dffffdf779efdbdbffffffffdffd67bf6fbdfe7daffb7dfff7edfeffdfbffeff77fee9ffdffff6f3ffffffffeddaeb7fff7fefdf7bfffbffff97ddffbfffb797ffeffafbefbf7ffeffff7fdffff69efd3ffffdedfbff6fd7fffffffff4df7becf7fff6f7fb7fbffff5feefbfbfeffcfbfffebbfd77fefdefdefffcff7bbff77fafbfff77dfffefdaff3edeffbed6ffffbbfde7bfffeddf7ff7ffff7edf7bb7ffeffffffff5ff4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches30 : PLift ((OMA.PrimeProgression.composite primes 14 525575 11873) = mask30) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified30 : PLift (rows30.all (check 525575 11873 mask30 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct30 : ∀ r ∈ rows30, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified30.down r hr
  rw [←maskMatches30.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows31 : List Witness :=
  [(1806,599,125),
  (1598,677,113),
  (1822,594,126),
  (1763,617,127),
  (908,1207,63),
  (1993,550,140),
  (1818,603,129),
  (982,1121,72)]

private def mask31 : ℕ := 0x7fdf7effefffffffb5d6efacff7dfdfbff76fedf7dfffffffeff7cfffdfdf3ff7fdffdefbbefffbf7badfbffeff7df77bbefafbeff7f9eebfddbfbbdffffffdefd37dfcf3dbfffffffffbebf6f7effffe7fb7b7cfefd7ffffff5ff6dffbbed6dffff7edf6bafffdbffffdbfffedfb7fffbbfd67dfdfefbfefbffeeffddb7fbdffff67f3ff77fedff6f6fbffdf59ffff6fffb3df2fdf6ffddfebeefefffdffdfeff7ef7ffbfbfdb6ffbfffffffffff7ffefdf7dedbfff6f93ffbdfb5ffefffffffe7ffdf7ffeffbdf7dfbfff5bfefaffa7fefffed7fd7fff7bbffb7df6ffedfffeeb7cfeeffdd7ffbef3ebf7dffff5ffdbffffffeefe7fb7bb7befdfdf2dbffbfdff7f6cfffdfdfbedfeb6ed3ffafff7de7f3ff6fff7bf5ff7bfdf3ffbffbfd6fffeff5fb7f3ff6ffbffffdfdbf7ffffffffffffbf7dfefaffffff6ffcff7f6ff7fbbdff7fffffddff9fff3dbeebffff5fedfffdfff3dfbfdffff7deef2ffffbfdf7ddffd7fffdfb7fffbfffefdefdb4fbdde7ffeffdbbffffbf7dbefffdecff6fffbffffddadff7dfeffdfe7fadfffd7fbbffe7ff5ffefffdfdf6fdefffe9fff3dff7dfefbdf77bfdf3dbfffbfffefbcdff9f7bf6ffeffdfbffbeff7fffbbdf7ffbff35dfffeed75ffeffebffb7edef9ffbfeff7fefffffeff7dffebfddbffe7fbfd7ffbffffdeff3efeffefffffeeb37deff3cfffbedbb7feffbffffbfdfff9f7dbdf7ffbeb7fdf6b6ffe7fffffdbffb7ffbfff6bbd9f7fffd77ffffbffeffaff2ffbffbfbf6dfefe7bf7b7fffef3ff67bfdfbeffffbdd6f9f7ff5bfefffdbd9aefbffeff7dd75ff6bfff6fffedf7fedfffbffdfff7ffbff7ebe6ffcf77fe7bfdfef93ff7dbbfbfedf7fbffadfbfffdf7ff2ededfeff3eb7f97ffffbf6ff7d67dffdbfffff7eff6bfdfedffebfef76f7ff6dfbff3ff7ebffd7f9ffbfc9fff7ffbd9f7f7fff7baddbffbcffcdfeffeffdffcff7fffdeefefdfff77bffffdfffffdfb79eff7effd9edf75f6ffeffefdf6f7dff7fbddefbf7bfebf7fecfe7faffffbffdfeffdfffbfdbfedfff3fff7ffdf67fbffb7faffb6f77fbdff79ffb7dfffdbefefffcf37de7bfef7ffffbf497ebfcfffbf5f3cf7fbfffffbadbf797edfefafde7bbdf669fff77fefbbfbf79ffff59f7f7fffffefdfddf7ff7fffbffdef9e7fff9f6feddffffdfffbfff6ff77ff4ffddf7f3ff3ffe7fffffffaddeffffb7f9ff9ffffdfbff7ffffb7fffdfffff5bff9fddffdfefffffefbffefdb7f7d97ffedff5fbffbfffff7effffeffbeb7fdbfff7ffdff6befffffbfdf7ff6f7f97fdfdfbfffffefbaffbffb7f75ffefefdbf9f7f3f96effef7ffb5fbfff7faff2fbedbf4fefffffffdfdff6fef97ff7fffff3fffefffd77bbdfbebfffeddafff7ffeb7ff7dfe7df6fbcdfff6df7dfffbb7b7ffbdfff9fff77bff9fffaffecff7bf7fbcffddffffddeffbef77bffffffffbeff7ddfefffdfffeeff79ffffff6eb7ddf7fafffff77fbff6fdfefffbf7dfffb5feebfefff9fff6f9fdffddfef7fdff9fdf76beffecffdfa6bffffeb3eff7dedfbf9e7f7ffbfbffffdfefdffdffbfef76b7ffefd77feebf7f7fbfffb5fb7ff6feffeffffbfff7dffff7efef9efbfdff7f3ffbddffffdfffffdffdfeffb796ff3dfffffdbffb6ededfffdafbfffeffbefffdb7fb7f6fdeffefbf7ff5df7dedd7ffefff6bfffffded9eeffdbfefffdbdffdff5d7ffefdbffe7ffff7fdefdfffbdbbefeeffeff7fbfffcdfef3eff7bfebb6ff7f7fffddbff76ff7ffefffffcf7fbefbfdffdff7ff7be6fbff7fbf6bfdf7f9adf2fffdf7ffeff3ffbfbfffb6ffe97effdbffbb5fe7ffffffbfef7fffffffff7ff7f7fbf6deeff7fefbfddfed7cdffffcbfffeffeffafdfffbe977fbfff5fffff7ffef3ff7ddf6f759f7ffed6ffffbfeb7fffcffffe7fbedefffedfffbdff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches31 : PLift ((OMA.PrimeProgression.composite primes 14 540897 10987) = mask31) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified31 : PLift (rows31.all (check 540897 10987 mask31 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct31 : ∀ r ∈ rows31, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified31.down r hr
  rw [←maskMatches31.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows32 : List Witness :=
  [(1751,644,127),
  (1923,588,142),
  (1940,583,144),
  (1350,838,101),
  (1531,742,106),
  (1233,922,84),
  (1510,756,103),
  (1835,623,126),
  (1865,613,128),
  (1934,595,141),
  (1474,781,103),
  (1776,649,131)]

private def mask32 : ℕ := 0x3ffbfff7ffaff7c9ffffdfe7de7fbf9e7ffcfffbf6fbfdf7feff77ffdf3ffffbeffeffbefb6fe6dfffefdfdb76f7eb3fd77dfff7fdf7feed6ffbfb7effff7effdff7fffbff9ffd7dbfdfbfd6ffbcf7fbffff6b7effdffdfbebf7feff7ffa7fe5ff7f7f9ffdedff5b7fdefbfcfbfffff7edfffbefbddbfffc9f6beffb5bbdbb5f67fffd77becffffffffffeffecbbfff6ffcf25bffbbffff9fff7fffebbedf7f7ff2ffffffedfefffdfddbdf7fff7bfcffdff6bffdeeffff3fbf7f3ff7fdfdfadffdfbffe7ffeff7fbfbf7f7fffffe7dbfff7fe7d3df3ffaffffb7fbfdff7bfffbdbf7d7df37ff7ff5b6fdffdafdfffb5ffffffff5dafbffffedfffffbfff7fdfebffff7dffbbd9ffbbfffdbffff5ffebeefaffbff7edffd7fd3fbeefffbffdfedbffefffef6f9afd77dfdb7eb7ff7ef7ffbdbbff6fdaef7fffebfebffdbffbfbffffd9fef2dfefff7ffef7eb6cdfffefffffffd6efeffffffffe7feddfdffdbfebffdffffffb7ffff6ff2efff9bff7cdfffeedffdb6ff7ffeffdfff9beffffffdfff7ffb7bbfbefdfdf67deff75befbfffbfdffff79fff3dfaf9edfb7ffedefdfdffff76befb7ff3ddf6fffbffb7edbdbfeffff7efeef7dbefffd96fdefdffffdbb6fe6befdfdfbeb3fdffb7ff7fbf7b7ddffbffffdffcb76ffff7cffffeeffffffb7efa7df5ffdde7fefdffbbdbffd7fffcd77ffdffcbefdbff3ffffbf7ff6bfefbfffffbdfeffaff7dbb6fbdff7dbededfefbfff7eb7ffefbeeffff7ff7ff7ffa6fbf9ffd6dff7fffffffe6feffbddeeb76feefbffffdf7bfcfffffffefbb7b3fbefdafdfdfeeffdbfffbeffdfb6fbfffefeffffff7bfdff7dfdfa7ffcfbfff7ffffb5ffffffdf79ffffddefffef6fbffff7bfdbbfffff3ff7ffbfffdff7fecfbffefffcfeeffdd75bfffffd77fffd67bf5bbff77ffdf77ffebff9fe97cfeffa5fbffefdefd7ffb7f75fefbfeffdfb7f7edfffaefbfbadfbc966f7fff5fadbfddefffffffffefbdff6bbdff5ffeffffe6dfdffdff7f37f7ffbfdffffebffff7fffdeffffb77dffb6ffffdfdf7ffffffff3ffbffb7dfff2efefff4ff7bfebfff7fffcf7fbffffff2ffefbfdfefffeff7fb6f3dfff97dd6fbefffff7ef7cfefffcfbff76feff3fffeff7beeffdf77df4fbcf7ffefdffffdffeff7d3fff7bf7bf7fefd7efeffffbb5df7f6ffef9ffbfdbf7feededffef7cdefb7fdf7fbdff7b67fffdffbfeffeff7dbffbfdadfffffedffff7fefbb5ffff7efffdffbfdfefd7ff7fbe7bf7dffbffffdbaffffbffdfdff7ff6fffff7f3efbfdf5bffbffdbfdfffbef3f96e9fff6fffff3dfefb6eff7bfdf7ebefbfedafdffbfff7efefff7fbfffdbfebfef7ffe5ff7bffffddfffefff4bfefbdffddedff6bfffbdff79fff3fffff7ef7f9febf5fff97effffeefffd7ebeffefbfffbeff7feffffff6fbf9fffeffe7ffef37f7ffeffedffdbffde6ffdfff9fdf3cd7ef3ed7fffff7fff7f7edadbf6ffd97ebfddeddeffbf9efffdd75fffff7f7fffefffbefb7cffffeff77fffb37ff6ffffedffdfbddeeffed77fbeffddffbbffafdbfff6ffff6fdb5bfcf7fffffffffffafffddfffacffffecf37ff7dfff67ffeffebffd3efffffdffff7efeef779fdf779effffdfdfb7fffbffbbefe5fadfbdf7ffedfffff4ff7fffdbff7fbfff74f77daffffdfeff7f7ebfcffffbfb7edeebefdff9b7fbcfffffcffddf7ffdffff7ffb7ba7f3f9ff97ffffffffffbfffeffefffdf7ff6fdeffb7ffebffff7ffdfafdbfbfddff93ed7ffffb37fefdfedefff7ffeb77ffefe7ffffbf97f9ffdffbffbfdf7fd7ffffffebbfbffbfddfdfaffb7ff7d3ff3ffeff7ff7fffeffd9fcfbfdf7faffbffefff79f6bffffdfeeffcff7ffef75fb5bbfb77defffffffff6fe7bfffb7fadff6ff79fef7dfffffed6ff7fdfffb7fb6dff9afdefbffffcfffb7dfff9bdf7dbe6dedf7ffffbffdfefbdd7fffdbf7bf6feffffffff7fbfff7eff7de7f77fffd7ff6dffff75fefdaefbfbf7f7dffebfdde5bfcffffe79fefbdbfffb7f7ff6ddffbfef7ff6fbfffffdedb7fb7fbfff75ff5ffcfeffefdfd9f7fb6feff7cfffffffff9f7f7dffd9fffffb77b7cdbffbfffddf7d6dffffeff75f7effddafffeb76f77bfefbfffff7ffffb2ff67bbcfffdf7ffdfafdb6ffcf77ffffffff6ffcffefefdfdffcbfdf77ffcdafde7f7ffffffdfeddffbbe977bfefeddefff6feffffdf7fb5fffbf7fbffbfdb6ff5b7ff2fdfdbfefbdd77deddfdfedfb7bffffffefbeef7fff7bffdffdffbfffe7f7fff7ff5ffffffb6ffef9fdbfcbfff3edbfde6ffdf7fb7cfbdbfeffedfef7efbfffffbfb7ff7eff7df5f7efe6feff7ffbcf37f7fffcf6fdfdbffdeffeff67bbdff4fff9ffdffffeff6977bfffffffdffff7697fdbfffebfddf6fefff79e6ffff67fbfffdffebffdffdfcfadffffbddfffaff6dbb7b7efffffdfffffff76ff7fbffaddfdf7fdfff6dffffffbbffe6dbdf7ffe7ff6f6fbeff6fdfdff7ff7f7ffb79ffff5def9eff7f9bffbddffdffdeffb7ff7ffeffefa7ff7fbdbfedfcdfffffff7bf6feff3ffe5b7efe7bfffffffcf7ffe6b3ffb5dbdb7ff6ff2edff9fdbfebf7dbed3fffff7fb7ffefde7feffffbe69ffff5fb5fbffeffbddfffe7f3fffffedffffbcfbef7fffdff7bffbbeffeb3ffedffeffffeff7fdbf

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches32 : PLift ((OMA.PrimeProgression.composite primes 14 563822 15154) = mask32) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified32 : PLift (rows32.all (check 563822 15154 mask32 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct32 : ∀ r ∈ rows32, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified32.down r hr
  rw [←maskMatches32.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows33 : List Witness :=
  [(1129,1031,79),
  (1557,748,110),
  (1592,732,113),
  (1628,716,117),
  (1634,716,115),
  (1290,912,97),
  (1264,932,97)]

private def mask33 : ℕ := 0x7ffffffe977ffcdff9feffff7efedfffbbcfbff77dbffe7bfdbffb7ffffffffeef3fbef97ffbffedbf7dfebeffffdbfffe9f7f6ffbddfeb7edfef2dfafda7ffdd77ffdfbffb4fbf9fffafdb7ffff7efff9eff7dfbfbfff7fd7efb7baff7fffef7ff7ffb4bfdfffffdf7fbbeb7db7efefdf5daff3cbefdfeffdbfdfb5b77ffffafdffb7fbffffffbffeebffff7b7cfe5ff7ffddffdffffd9bdfb5ffffecd3ffa6ff59fff7fdefdbff3ff7fbfffffff7ffddfefadd6fdf6fbef7fffddeffedffff7ef7ff359effbdfeef3eff7fffbbebeffffd7fbf7ffeffefecdfdfffffeffeb7ff35fb6bbfb67fbddefbf7fbdfe6fefdbdffffbfbe7fbffafdfdffffefffedf79bdb7efefdfdfbf9affffdffb3efeddeeffdb7edfff7dffffffdffffdfbfff5bf5f6ffbdf2dfefff7b7edfffbddefff7fff96fff7dfef3ffffdfdfaddf7ffeffebbffe7ff6f7ff67b7ffbffaefbfffff7efefbf5b7ef6efffdfffbfbffff7f3fff5fbdffef6effedffbfef37fffbbed6fdf7ffdf7ffeefef9b5f3ff7ff7edb7ff5bfddffd6fff7deeffffefbefd7dfffbfe97f9fdfe7fffffefffdeedffdfff7fbffb7fdfddffb7fff7bbfdfffaff3fff6fedd7fff7fbffeef3ed7fdf6fbff6ebffffddfcff7dffbfdf7dde7bb7deff7ff7dffeffcdf7dbffeddf7b7f9feffddffbffffd9f6ffeff5bffff5fe7daffbfffcfffbef9fddfddfffb7fffbfffffffff7effe93ffe79fef7ffeff7ff6fff6bffbffb7ffffbfcffdff7f7ff77bbdbfff6ffbffffdfdfffbeefbff2fdaeff7bffdfffefdf5bf6fffbfffefff4f74fffffffffdbfff49fff6dffdbf5fbed6efefff7fefbffff6faffefff7ffdfffdffff5ffefb7f7f93ef779e7bffd6ffffffdff7bf79efb7dffdffeffdfffbbffafdfef7dfeebfedbffffbf7d7fdbff6ffffff7ff7fbfffddbcf7ff67bffffffbdb3fffebaff67fffffddffdbffffdffff6bfefbddfd9fff7ff6e9ffd7dbeeffff76f3fdefbfdb7ef7ffbddbffffbffbefbfefb7fffb7fdfeffedeffb7ffc9f79feffdbeff75d7fffffffdafffdff6fffffdfeefbff67dbffefff5bbff7edffde5ffdffffeeffdfaffafffcdeff3efedbf5fffbefbaefffffff76dffbedfffffeffdfff96cfbdfefbff977feff3fdf6f3dff7bfddb7ffef7fbffffff3d9fffffffefefdffbb7bf7dffffdd3fffeb7cf77fbffffbe4f7ffffd7eff7fbffffbfffffd77ff6fffbfefeff6fdeffbfb66f3df77fbdfffdff92effddbfbf7bf7dbdf7ddfffffffebfedffbeff7fff79fefbdfafbffdeefecfefff7bf5ffffffdbfdbffff9ffdfefedfe7ff7ffffaef6dff6ffdbfffbedefff7bf7ff7feedbfde5fbf97fdefd7ffbefff9eef7ff7ffedf7ff7fffffbddbffffffedbdffdbadffefefdbffe7ffff36be7b7efefbefb75ff7befff7de6f7fdffdffdfffffff5fffffcff7ffff7fb7ffbff3fdfcbbfffff3ff6ffffff6d6e97fffddf6ff7fe7becfbfffeb7df7efaffffdfffbdbefbedd77ffffbfdffffeff7dfefb6f769fdfbffbef76ff7fbff67dafffff7ff7fdffff7fffbfffafd6f9bffffffffbdfb5ffdfbffe

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches33 : PLift ((OMA.PrimeProgression.composite primes 14 582000 8920) = mask33) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified33 : PLift (rows33.all (check 582000 8920 mask33 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct33 : ∀ r ∈ rows33, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified33.down r hr
  rw [←maskMatches33.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows34 : List Witness :=
  [(1402,848,101),
  (1275,933,93),
  (1413,842,103),
  (1214,981,88),
  (1189,1002,86),
  (746,1605,51),
  (1435,835,101),
  (1739,690,118),
  (1257,955,88),
  (1795,671,121),
  (1502,806,113),
  (1961,618,145),
  (1008,1208,69),
  (1419,860,97),
  (1645,742,115)]

private def mask34 : ℕ := 0x7bdbbfffdfffffefbfbbefffd77f6fdffbffff5ffff7ffaffe5b3cb76dbffffdeff77b7ef7ff6ffa7fb4dfff7efffff5ffdfffb3ffaffffbffff7fefffffafffffe6ffff3ffbdfbffffdeefffdf6f3cff6befdeffedfbf9efbfef3fdbff3fffedeffef9feffeff7d6fffffffffeb7ebfddfffa5fffffefffdf5feefbfb7fffcff7de7bfdffffbffb7fedf3ffe7f7ffb7ff5bfcfefbfff7ffbdbfddf7bbfdefff7bf7dfebfeffffb7f3fdefbeefb7fedbffbe7dfddefffcbf7f6ffefdefdbdf7fffeffcfeffbfffffffdfff75dbef3dfffdfdf3ffefffeffff6efbddfdfffdf7feffbdfffff7bfff3dfe7ff6f3ffffdffffddbef7ffeebfff37bb5ff5fffb6edfdbfff75bffffffffdeffffd77f3ffafff5fffdf6feed7fbeffbdffef3efefff7bf6bffffff6fdfcbf6beff7efb7deffb6ffff7ff77fffffffffdecffffffbf7dfeffededfb7fbfffffecf7fffdfffdffdfffffdffb7ffef9ffff7ffcb3fdf6bfdf379e5b7fd7e97fdeddf6bf7ff7f6cd7fdb7ffefffbffffdbe6fbebfeffdf7ffffbb7ffed2ff77ffebffbfffefffdfedf3fdeffbffffffdf3fffebbfde7bffffdbffbbfffddbeffdd7fbfddfffaff7efeff7df3ffbfffff7ed6efefbfef77f7fffffedffebf6d7ffbcf3fdf7bffdefffefffffdffefffbefdfdbb6bf5bfffbffe7faffffdf6ffdf7fff5bb7d7ffeffffffeffebefbffda5ffdff6f76fffff7fefbb4fffbbffefdb7f7ddffd3df6dfafb76bfef6efbdfbef7cffef7ff75fe6ff7f76fefd77fefb7fbefffffffdfcf76fe7d7effdfefffddeefaffeddbff3cfffffffaffeffffbfffefff5ffdfbfd7f9ffdffbaffffffffffd3fdfeffdb77dffffddefff7ff7f7ff6ffe7b37fffd7efefffefbcffff6df2fbf7b7ff77bfeff79fdf7fff7bfefbffb6bffbeff7fd7fff7fbeffffadd3dfbdfbfdffdfeffddffffff7fb6eff7ff5f34fe7f6ffefdb7fffbf7ffedf7dbef7eb6effdfbffbfffdfeefbffbf9ffbb7f77fadfaffbfbfff77f7dfffbfff75dee9eff6fffebbffeffbfd3dbfefffffefadde5ff6f7ebefdfefbfffcfbfdf7dfffffdf7bfdf7ffbfff7dbefffbffb7ffe7baffbef6ff6efed9f7fbfbfff7dd3dfefbfe977fedfedbafffeff7b6fdb7feefff9ffffeff7ffebfff76fffd2dffebffbefdfdf7fbbdffddefdbff75fbffbffe7f7ffffbb7ff6df7f7fffffbcf7effff6fdfdfb7bbdf6ffadd7fbefbbcb7fbbfd2fffdfb6dfff3efbfffdff7d7ebbffffdbff77fe7fbfffdff7f75f7ffbffffff4ffcdf7dfff7dff7fbdbeff6fd27ffdf7cfe6deffedfffb7ffffffff37fafbfffffbbfdffdfdbfdfe7dfcd2ddeff7ffffffefffdfefbfd7efeedf7ff5ff7bffdfcf3f9fdffdbf7dfdffffedbffbeffbcfff9bdbfdfff9efff7ff7f3efffd6fdbfdffbffd7fb6ffbdfffffdf7edefff7ff6bbfdf6f7ef77bfdf7dfeedffd6ffbffbef7fffffbf9f7fffffef7edefbbfb3effffbdffdfeebf6dfffffff7faeffffefdfffffbf7ff7b77dfdfffbffff4ff7bffd3fdeffbeff7bfdfaffeffbeffed2ffff9febffbf7b7fdffffeffffffffefb7ff6ffdfefffeffdffdbffffffeef77befffff67befdfddfdf77df69fdffddefbf7dffffff7dfbcb7ebf7fffd6dffeffdbfffbffffffffbffefdfeff7ba6fb7deef3dd7ffffbfdfffdafdefdefffeff7dbefefff7f76ffedbfd7dfffbf5fffb7ef7dbafb7fdfefffff79bdffebf7feeff5ffeff5dfffffdffdffffdb7ebfdfadfbefb7b779fefffffdbbcf7effefe5df7bffdffdeffffdfffffb7ffedff7dffffdbf7fffd3fbaeffff7fdfffffbe7ffefffffdde7dffff7bffd3ffffbeff7dfefbfefeffb7bf7fefffef7dfbfb7f97ffbefbffedffefffbfef77ffdffdf7ff7cfef9ffbf6fffffffbfdfdfffdf6bbcf6f9b7ff7fefdeef67dbfbfd9ffffcffdbfeffdd7ffbdfbffbffbfb7fd6fdbfbffffffe7f7cfffff5ff7ffebadfefdfef3ff6ffbffbdfffffdfffdefd7fdffffffefd6edbddb7f75dfff3fffffeffffffe9fedfffeefbffffdafda7ff7bb7fffdffdfdfeebf7bffbbdf779fff77ffedfeffddfebf6fef96ef7ffeeffdff7bfffeffbcfbfbfedffffffeffb5d7ffffdafffeff7f76ffddeffacfbfff7ffffffbffffef7f9ffdffbf6fbefeff7ddefbffb76f7efbedfd9fcfbfff7b6efbffe5fbfff6ffcf7fdfff7dffffadf6fffdbffd7ff3ffffff7fbddffdbedffffdfb69e7bbfdedffffffbfefffff5df6ffdfffbffdbfbffffff76ffefeffedfbdbf7fedf6fdbefbef7fffff77dedbf5fffb2ffe5fbfb7ffef9fdfbd9f6bf6fffbecfb7feffbfffffeffffffdfb7f7ffeddbffe5fbff77ffff37dbffbff7ff7ffbdbafffddfefffff7ff7ffdff7bbddffbe7ff7ffffefde7ffefbfd7edfdd3fffcff7feff6cfff9f7fbefef9fffb7fbdff7feeb7cfaffbfbffdfedbedfdbfeffffff9bff7fff7f75fffbefffffeff7cfeffedfffff7fbfff6dfdfeffe7fbff769efffdfeebb6ff7fbdf2dbf7ffffeed7ffeddfebbe9f7ffff7fdf7f7fdfeb2fdbffaffffbffffcf3dffdfffbfeffedaffffffcfe6bbdfe7ffff7fbe7ffff3dfedfbff6f9ffff5dfef7effffbfd7ffe7bfdffebffdf7dffffef77dedffffefbffd6fffdf77bfcfb7be6bfffffffffbfb6f97ffffbedbf5fffbbfffdffeffffffffdfbfff7b76ffebfcfefbf4fffdffdfff37bffbfdde7fffdbf9edbfef7ffbfd3ffedb7f97fdfff75dfff7ffeefbffedbfebffbfff7ed7fbf7ff5bfff3eff7fbffbf9efffcdffffcbffffff7ffffdf6f75ffebfddfddfff3ff7f9fef2fbffff7d6ff2eff5bbdff7bfffeedfffb7bfeffef2fdefdfdf3fff7ffedf7fefff5fffdbfd2ffefff7befbfdd7dffeffef6ffbdffffe7f7ef7fb6ed7ffb7b76dfffbffefffebfdff6ffdfffffdfbdde7bfffbfffdfbfbffd6eff7fefbbcf7ffffff5dbefffd67d3dfe7bf7fbcffebfff7dfbff7dbffdafdffdffffff7efbefefbe6ffdd77f7df7dffdbff9effedd77defffdfeffeff77feffffbfedbffefbbdbfff7ffbef75ffdfbfdf796ef3fbfff7d9fff7ffe5fedf7cffeffdfb7be7fbfbfef6fd7f9fff7ff76ffdff5fbffffbfe9fcfadff7fbeffffbff7dffff7fdf7f3efbfffeffeff7b7ffffffef3ff6fb7df7fff7fffbf7dadf77ffdf77f6fbffd37fffbb7ffeffcfa5bb5ffcf7effffffffcf3fbfffefdfdffeffdb7efbffb7ffff7dbfebfdd77ff6fbfbfff2ffefbf5f7ebffdedfbfd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches34 : PLift ((OMA.PrimeProgression.composite primes 15 594448 18315) = mask34) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified34 : PLift (rows34.all (check 594448 18315 mask34 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct34 : ∀ r ∈ rows34, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified34.down r hr
  rw [←maskMatches34.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows35 : List Witness :=
  [(1886,653,125),
  (1386,892,101)]

private def mask35 : ℕ := 0xfffffeffeebff9fff7efbfffcffedefbeedf7fedfbff7fdedffffefb74ff6fbdfeffacfb7f7fffeffdfbfff7def9efffdffef7fbffbeedefdfeff5b77bfdff5dbff7ff7f9eddb7faefffdf7feef6fff6fbffeffeff6fdffbffdfef7cf7ffffbffd6ef7ffeffbdb7fdf7facf3ffe7ff69ffbefff7fe7ffffefd7df7fbfffbdf66faffe7bffff6f7ffbfd3fffffbfd779ffffddeff7cfeefbfdefffdffe9f7bbeffdff7bf5bf6f7ffeffb7fbedfffffff7fffbbfff7faffaf9edf36fefffddfdfbdbf7bf7ffff7dfadff7fefd2effdfbefbddfffbefedbb6ff7dffbfedffffff7fbffdfffbfbb6bfdd6edefd77fffb3fbf6fbffefffdf76f7ffbcfbfdeffbff7efffffddf7bfffffbfed7fbbfff79ffffffffff5ffffffdfefb5fffbf5ff7faefbfffcf7ebe7ffdfffffef7fff7b3ffffffdff5fffbfffe5ff5fbcfef9fff6fdbfffedf6fedfef9afffffeedeef75bfffb7bfeffdfb7ffeffcfeffffff7dfdff797fb7ef3dde7bffdfefefffdfffbf7bffdfffadbf6fffffeffeffdffcfbefe7f7ff7fffeff796fffffbffffbf7f77bfffafdeffff9feffff7fdbfbbeffffbffffffff3f9efffdf7ffffff6dffbaedbddbffbebf7d7fdfffe4ffdfffd3dffffedf7fffebbdfffdffb3fffeffdfb5fedffefffbfefe5fffb7fff7f7efff9beffdd7ffbfffffedffdbff9ffffdbbfff7bffdaffffff7f77f6fdbdd7dffcfbefffbbff7ffbfb77dfefbfffffffffdbe7fffffffafb7fdfeffffffdb5fbfbe7deefb7bf5ff7df7daff6fffeff7f779ff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches35 : PLift ((OMA.PrimeProgression.composite primes 13 615779 4456) = mask35) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified35 : PLift (rows35.all (check 615779 4456 mask35 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct35 : ∀ r ∈ rows35, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified35.down r hr
  rw [←maskMatches35.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows36 : List Witness :=
  [(1942,641,142),
  (1375,909,90)]

private def mask36 : ℕ := 0xfffdbcbfffe7deffff9eefffbfeffdff5db7f7dbffffffb7feebfff7fffcdfffeeff7f7fffdff5fffbf6bffffeff79fffffffffafffdffefb5fefbeffafbf6bffb7effddedff5fffbff9feffdffefbdd6fffdfe7feeffdfffbffffffbfbffbf7dbef77bafffff7efbfffffbfbbefff9bddbdfeeffdbf6ffededdf7f7fffeffddbdfaebffde7dbdfbfff6bffffeffddadffeb7fdffffffe5bffff4fffffffe7ffcbfdfffffffffdb7b7efffbeffbfffffbfd7fffdf75fbeff7b7ffbffe79fffbdb7fffffaffeeff7dfeb3df7dffff7ff7ff6ff7f9fdffffeffecfbdfeef75b7ff6ffffff6fffff7dfddfffb7fff9f7d7ff37fffbbebf7dfffe7daffffffebfdff7ffdf7cd7f9befffff7b36ffff3df7dfbeb7fbffffefffbeefbcd7ffffdbfbb7ff79fef7cff7ffdffebffdfdfbffaef37defbbffeddb5fb7fef9ffdf7ff7ff7df79efd7fdeff7ff7fffdfedbfcfffdeffffd7fbbcfbdffef7ff7f9ffbf6feefffd35dbfffffeff7cf7d9edffffefffede7fbff3fdef9adfffdeebffbfff7cfb7ff5fffd7fdecffdffffb7ffefbdfb7beef7db77feff77feffb6ff79fdfefbffffcd7edbff6ffbeffdff7defffffe7b7dffef7fdfddf7fff9feffefbfbefbffdf6fffff7ff7bf7feedffdbffeefffde7b7dfeddf5f3dd6fbbfd7fff7bb49efbaedaffbff7c9fff6efb7ffffffffeb7ddf5ffdff7ffff3ddefdf7fffb7efefdfdfeef3ebffffcfb79bfffdffe97ff7fff6ffcff7ffefff9fff7fd7fbffdffbfffffdffffffbdffebfdff7dfddefbffbfff7f9fdd3fffdfffbe7ffefedfedf

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches36 : PLift ((OMA.PrimeProgression.composite primes 13 622411 4589) = mask36) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified36 : PLift (rows36.all (check 622411 4589 mask36 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct36 : ∀ r ∈ rows36, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified36.down r hr
  rw [←maskMatches36.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows37 : List Witness :=
  [(1771,711,121),
  (1617,779,112),
  (1231,1025,88),
  (1837,690,134),
  (1327,961,94),
  (1161,1101,82),
  (1816,704,130)]

private def mask37 : ℕ := 0x1edfcdfffeeffff7ffaedffbe7b7fb7ffffffffbeff7bf69fdf7ffedfffd7fdfff6fffdfb7bffdfffffff7ffefffb2effddeefbfbf6ffffb5bfdffddeef7fd2fff7bfffffdeffe7fbefbff7ef7dff5de7bf6f7fdbffefdf4bb7fe7fbffadfefb7fbf6fffffdde7f7fdeff7dfbffbdff7d77f7cf7fbfcffcffebbdff5ffffbfbeff7ffa7daff37fefbeffedbf5bf5fffffffbffbeb7f9feffffedbecffeff6feff7fbf7fff9fed7ff77bfdbfef77fbfff5dbfffe9f7ffff3fdffbffdfffeff6dff5f7fbe7fecfedfffbf7f7fbbfdeffb7ffedf7dfefffffdff7fefdecfffbffff7f77dbdfbfffef7fffeb7cff79edb7ffffffffefff7ffddffdbcfbfff6ff6bfeb6dfbfff5ffeffef6edb5fbfbfddfeffdf37feebf7bff9fffbdffffffd7fdfcf2ffffff5ffffbfd65bbff77beff6dffffafb77d7effffffffefbfdffdfeffdbafbbdffff7dd77ffefbff6e9bdfefffeffeffff7cfaffe7fbfd6fb3fff5fbfffcffff7ffbddb6f7fbffbbfdbdfffffefe7fefdffbf7ffffe7dfefafdfdfb7befffdde7dbffbff7fdbff77ff5ffdf7efffff7bb7f7dff7ffffbfde7fff9ffbfffbddfdffcf7fffffbdffdfb7be6ffcff7befbf4ff7feffeddfeb7fff7dffffdbbfbb7deffeeffdff6f3fbf7bbffefdfef7fdfffeddffdf7fffd6ffffdbffeefffb7ff7fdefdf7bf5b7effff7ddeebf6dff97ffbfbfffb5f7efaef6dfbffbffe7dfef3fbbfb7fbfffbdfefdadf3fbfebfffbdff7fffdffffcf77fefff7b77ffffbffadfb7ffff7dfbffffbffdffbbff7fffff3ddffbfedfdbfffffbfff3effdfaff7ffeffffd75feffffd77ffff7fffff7ff7efbdf77fbdff7bf7d3ffbfdffbfdffeffff7ddfcffcfeffbdffdbfff7ff7fb7efaf9effffbfeffffb7bf7fb5dfff6ddeffe7ffdffffedf67fffbbfbeedfffe59bff7effef3fd779ffbffdeff7effffe7ffed77befffffe5f7fde6ffdff5fe5fb79fedafdbfbfffffff7fffffffedff6de7dfff7dfefbbfffffffff7bbff7dfff9edfafdffffc9f7f6fdefbbeffdb6ff7fd7fbeebfdbffffcfbfbfdfbcffeffffffdadbf6f6fffff3fbf7f7efef9fffffdb7fffdeffbddaffbeffdff7bfcdeffecfbfd7fb7ffffbefbf797ef6dfbfdf6ffcff7bafd3fffff7fdfef7ff75feff3dffedfffffbf7bfffffffef3d9efbfdfffb2cfb5bfdfbfbefffdd75ffefffdfed6ef77feeffdf6fffddefffeb7fbeedfefafbfdff7dfffbfdfddbeb7ffe7beffffff7ffff7ef3ffefbbffff9ffffdf7fbafbfdfffd7ffb7fffbf7fee9fffedffefbebfef7cfe7ff5bb6ffffbedffbf7f7d9ffd6dffffbfbfddffbfdfbfdbfffeb66dfedb7bfdfffdf7fffda7fedffebf7dffffffefb76ff7b7ffffde7f7efffbaeff7ffdf76fffd6ffaffefff7f7ff3effdbeffffd6eb7ffbdbbdfbff6effff3fbf7ffebe7ffdfefdfdff7ff79fff7f9f7f7fdfebaff7fbbff7fff7ffffadbffffff7effedeffe6ffed76ffffbfbbfffdffffffd6f9edfb7bf7fadffffeff3e96efbefffff7ffffeffbfd6ffb7fbebeff2ff7fbfeff5ff7b3eff5fbff7fd66bedf7fff6fffb77fffdb7be5fbebffbffdb5deff7f9e6bfffa5fbfbf7dff9ffff7dfffffdffd7efedbb7f77f77fecfeffe6f7dbeffffdbdffdbf7defffcdffdfdffff7f9effffdecf769fef3df7fff7f3dffff7ff6ddb5bb7ff7bedfbffbff77fffbeffad9bfffef7fd7cff5ffffbfffffaffffbffbffbffdbffe7ffeb3ffeff7ef7dfffffdfffffffe7df5bfdfffb7dd2f9f7ffeffef7fffdfadffedeffffff5ff7bbffe7feefefdffb3ffeebefde7ffffffbefd7ffb5bafbbfffebeefffdfcb37ffff7dd2ffe6ffeffffeffffff7f3cf7ed6df7fbeffbfffefbfdf7bf4ff7fe7fffd65fffb7fb7effef7fbaff77dffbbfffdfbffffdefb3df7fff6f7ebffffffaffeff3e9efdffffdbffff5bfef7fdf79fff7ff66ffdf7fdafbbfd7f9fffffdafbffffffaff7fbbfffcfffbfffbfbffbf7b7ff6ddf7deff3fffedfeffdbf7ff7df7ffcf7fffdffffe7bbffffffef36d7ffbdf3ffe7ffcf6ff3edffbfdf7f9f7ffefeddfeb7fff7feddf7fe7fbfdfeffcff7fa7ff7b77ffffefffeffcb7efbddfffffbbefefbbffedffdfbeffebffdffbfff7fbffdeef6dffff7df76b7efbffbdffdbee9eff7fff7fffff7f7fd7fbffffdf7fbeffffdbeff7fef

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches37 : PLift ((OMA.PrimeProgression.composite primes 14 629591 12365) = mask37) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified37 : PLift (rows37.all (check 629591 12365 mask37 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct37 : ∀ r ∈ rows37, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified37.down r hr
  rw [←maskMatches37.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows38 : List Witness :=
  [(1709,756,120),
  (1638,793,119),
  (1063,1222,77),
  (1686,772,118),
  (1546,844,107)]

private def mask38 : ℕ := 0x1ffffef7efffbfcf2ffbff77fffbeff75ffebf7fff96fdefdb7bfdffeffffbfffdffcdf7d7edffbefff7ffefeffb7de7f7ffff9fffe5decff6d7fb3ff37ff7bfffeef7fdfdfbdf77be7dffffdffefff9fefeffbfbfff7efffbeef77fbefffdffd7efefffdfffbefbffff5fbef3ffeebfdff7bb7fffdfffeff7fdf7bf5beffadfbffbffffb7fffcdffbfeffffefbefdffbbfff7f6ed2edb7fffffeff6fbffeffbef3fbfebfcf3ffffbfcdfefeffe7ff4fffbfffaefffffeffcff7b6fff5deff7fd6edfdd7ffbffbfb77f2fdefffefbcff6fbfd7dfeff7fb7fdbfff79f7ffdf7efbefffffdff6fffffed7ffaef7dff6f6fffdda6f7dffededfffffffbfd7ffbdde7fffffff6f9fffe5fafffffffb7cfbfbffbfffefdfffe7ff4fbefffb7ffedff7bfebfff7fdfffbefffb7fdfef7fff7fb5defffdd77dfdffefffffff77feff7effffbef7ffb7fb5d6f9ffdfdfffb3f9ffbbdffffafff7f77f3ffe7dfdffd977ffddfdfa7fffde7ffddeffe7fffbfefedfedfbebfef76fbefefdf7b3fffff7fff5bf7bf5feff3fd6fdeff77df7baefb7faef7edfebfdffffbfbbddefffefff9f7ff7f7ffeff3fffefb7b7fdfffbdfffb77fffffffe7ffefb7ffffeddaffe7f7fbfefaefefdb6fbdfe6f7dfbfbf7ffdfeff7ef3ffffffcfe7bbfdeddfdb3ff6fffff7fbffffddeeffefffffebf7deffbdd6dff7bffd76fefdeffa7fffb7ff7ffbfbbfbb5be7ffffe7fe7ff5ff7faffbffbcb7eff7d7fff5bf7fffffff2efefffef3fdffdfcfffbefffdbfebefde7fbffffdefdeddb7fbcfffdffdfff6fde7bb7ffefeffffdbefffb669fdfbffbff7fd6fffef7ffbeffcff7deefefbb6b7fdfff7fdffbeffbfbfededfffbfdfffbeeffff77fffb3cfffffff3ddecff6ff7b7efbfff5f37f7ebffdffffebfdfe7fbef6dfeeff7dfff7cffdffdfbfdf7beef77ff7ff5ff7ffffe7bffb7ffeeffdfbfffff3ff7fffffffff7f7edfebeeff7dfeffffeffedfefbeff7c9ffffffaddf7fffbf6f7fffdffffffbfedbffffdfef7fff7dfffedfefb3f9f7dbffefbffbf5f6fdeff75ffef74bff9eefaffbfbfd9ffb7efb7bbff3ef77b7fdf7ffcbfff76f3fdeffeffbff77feffffdafbf7f6fffeffdbfdfbdfffbfedefbb5f76dfff3df7fbb7fffff6bfdff7ffcf7dffed6ffffff7fbff6fdffdbffeefbeff7fafd75faffffb7fffffffba7fbdffeb7fdffbf6bfedfffbffeddffb77ffff3cdeffbef7fbffdffffffe7bbff77f2ef2fdfdff7fe7dbddffdffb7fbffbbcfb7fb7ff5f7edeff7ffffffffffbbfdbffffffcbffb3fff7ffff3db6fbefdf7bfffffffff6df6ffffffdbff9bdf7ffecffebfeffdfff9ffbbffffb3fdfdbfeffcde7fffd3dbe7f76ff7ffefbf9eeffedfff6ff7fffefffff7dfff6fff5ffdbeebfff67fbffffbe7fbffedbfffb4f7fd6fff5dbfff5ff7beffafdffffefffffdff79edf7eb7fdffffdfffbf7dfefbedfffffbbebeeffff2fdbffbe977d7ef7ffedf7effffbef7fff5f7fbf7bfefefbfeb76ff7ffffbdfecf7fbf7bfedfffedfb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches38 : PLift ((OMA.PrimeProgression.composite primes 14 646002 8729) = mask38) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified38 : PLift (rows38.all (check 646002 8729 mask38 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct38 : ∀ r ∈ rows38, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified38.down r hr
  rw [←maskMatches38.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows39 : List Witness :=
  [(1583,831,114),
  (1490,884,106)]

private def mask39 : ℕ := 0x2fff7df6ffdfffd7ffadfe6bfdd77bbefed9fffbf9f6f6ef3ffedff7fe6dfcfffdfdfbfbfffbffbffbdf7efe6fbdf37befffffefbbfdff9feb7fffffefffffb7bfffffffddfffffffffffd6dd7fbe7ff7b6ffedfbfffebfffefbbddf5dffbb6fefffdffdbaffffffefbfdfddfdffddf7bfdfeffe7fff976baffbfffefffbf7ffffb7fbfffdfffdfefefdeeb3df6ffffde7ffdf77dffffff3fbffbfef7ffeffedff5ff7bffdafdeffb6bf797ebfcff79ffffd9fff7ef37ba7fff9fff7ff7ffefff5fffdfff3dfaef7ffe7ffefffdffff7dfebeef77ffeff7bf7deeffffafff6bffb7edefdfef7edf7dfffb7ffdfbff7ff6fde7bffbf7b6edbffffdfffbebeff7dfe7ffdbffdeefeed75ff7f3ffff9ecfffbe7bfcbfff3fff5ffefbffeebeefffbfdfbdbeefbffe7feff75ffffbfdf7fefb7f9f7dfeffd9f7bbfdfef3ffffff5bbcfffbffffdbf7b7dffefeffe7baffbfd6fbffd7fff7fffbffffefffbfff37f77ffff37dbebfede7fbdf7dfbff7fdeffeff6fbf7ff7defdedfadbffff5b7fbefdb7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches39 : PLift ((OMA.PrimeProgression.composite primes 12 657737 3078) = mask39) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified39 : PLift (rows39.all (check 657737 3078 mask39 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct39 : ∀ r ∈ rows39, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified39.down r hr
  rw [←maskMatches39.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows40 : List Witness :=
  [(974,1366,70),
  (1493,895,108),
  (1343,995,95),
  (1717,779,126),
  (1427,942,96),
  (1043,1289,71),
  (1620,830,110),
  (1416,950,97),
  (1422,947,97),
  (1467,921,104)]

private def mask40 : ℕ := 0x5ff7fff97edff9fff76bffb7cdaf9e6ff7ff7ffdffffbff3dbffbfddfdffeffff6ffeed37ffefbeffefbfd67fffbfffefffdffdffdf3effff3edf7ff7ff7fe7dbdfffffffff9fffbedafbf5f3ff7fdfcffdfbeffdbffdfffffbedb76fe69ffdadfefffefeedbffbfdf7fbfdffd7fdeffb6fbdffffbefedfbefffdfffffffddfdfbfbfffefdb7ffffbfdeefaef3f9fcffeff6ffffafffef3fff7f7ef7ddb7bb6ffffafdefbbcfbdfffd7fd2fbafffffffffefbfbf7ffcffffefdffbfffbfff7d3ff7ffedf3df7ffedfe7defbfff7f93dff5fefff5d7effeffffffffede7deefff9bebffffef2efefdfcfffd7fffddbfff5ffdfefffefffff4fb7fffffff7fdfcbf6f7efffffdfeff37f7e93ffefdfdf3fdffd2df6ddeeffcf77ffffbf9fffffdfeb7ffb5ffdfbdff6fbcdf7fedbfefffdbfdfdfbfff79eefbcffdfa7bbfffff7fd6dffcf7cbffdeffbdfefff7f7fffffeddfefffbe69fedbfbbfbfff6fdefdb7ff7ffff7f9fffeffbfbffb6fd7cff7fffffffffffffe7ffffff9fffffdfdbbff76ff7fefffdbfff7fbf7dfefbffe5fbdfffdefd6ffffbf7f7ffadf37fbef3f9ff97fffffbffbef7edffffffbfffefe7fefdafba6bfed7eb7ffffbf7fbfb67f6fff7faffffdffdfddf7fffbfeffebfdffffbdf7fb7efbeff5fbfbfdfeefafffffffbffdef96ff6ffb7ffdf7ffefdb7ff7fbebffdffffdbafbffbfefecfbfffeb3fffe9efdffffcf3fdffffeffdfbdf7effeffff6f9b7b7e9ffffef7fbfeff7d7fffffeffb5fbfdfeffeffdbedff79ffdfff2fffff75fefdeff7ffffbb6beeffcffffbffb7ffffffdef9fdfb4ffff7fdffdfeff6f7efedfe7bbffbdff7fffff7ff4bfdffeffdf67ff7f3fb6ffffdbfdeebfff7ffbdfa7bfdfffffffbedffffcbfe9fff3cffdfffbffbf7beffffdfff7eb7ebfff7ffe5ffff67ffef3ffecffcbe7dffdfdfeffffd7fdbffff9adfbdfffffedf5ffcbfffffd3efffdf7bfddfff7dfffff7ffdfefb6dffdfbffffbfef7efb7ff5f76feffedf6dfbdfffffffbcffddf5ff6fffbaefe7ff7ffebf79fefffdfef7cf7fffddeffe5fbfdeededf7fffdbffbf7f6fdffbfffffbfffbdf3dfaffb7f7eb7fffffe7bf6dffbfefff9fffff9e7d7ff3ffe6b7fbffffdfe5ff7f7dfe6bffffffbdfb7ff7fbfd6fffff74f67dbfd6fdfebf7bf7ffcfedde5f3ffffdbfdffff7f7ddfff2cdff9ffffff77feffaffb6fbefffffff37ffebfd977f7ffe7be7fb6bffbffff7dffff7bfeffff3ffffbb7f7edffdffbfcbbf9fffffd3dffeffdf7fbffdb7dfeffef7ff6efbdba5ff7f6fdbffefdf7bfff7ffafffdfffb3eff7dbff75bf7fb4ffe93fff7bffff6fefffff7fdaffffb7ff7cffd9bef7fbfebfdff7fe4fffbf6f7ffafffebfdfffbfdfe5faeff7d77dbffb5ffffb7fffdffdfffb7f3ddeffefd2ffffbffff7ffedf5df7ffeb7fdfcfbdfeebffd7ff3ff7fffeff7f7ffaddf7ffdf3796fffcfb7ffdffddeedaffffff6ffddf7faff7f9bfb77bfefedfb5bedf7dff7feeffdbefbfffffdffffffe6ffffffbbffeffecb3ffffffcf77fbff7fffef3fd7ffbff37fefbfddfdfe6bf79fff7dffdff7fbfff7d7df77fedbf5dfedeff6ffe4ffff7fbfffefdbffffffeffdfbfff5ff6ffff2ed7ddfef76befffffbf9beffff7fbfffffffdfbeff6f6ef7dbf7fbdff6dbedaffefbfdbfffffd2fffffff96efbeff7be7b3fdeefbfdf7fffbfcde7b7cfbffaeffff77bfefedfffffedefffcdffffffb7f6fdaff37fffff6ffedfffbfffebffdfe9fdf77bedf7dfff9eff7f9bff3dfffdeffbffffffdf7ef7fdfdffffbff7efffdffbfffffbf6fefff7ff5bfcffffbfff7fafff7fffb3efbfff7f7ef6efbfdedbbff36be79fffbdfbfffdbffffffffffefbcd6efedfbffffffd9ffd7efffdeefb7f7ffbdff5dffbffdeef3ffb5dedfbffeefafdf5ff5bffdffb7ffbffffb7fbfffefff7fbff3f9eeffdf7ffbefbf9e6fafff7fffffff77feff6fdeeffebfeffffedbbdff6fff96ff6fdbef7f9ffbfdffffe7f7eb7ffeedf7df7fbd96fffef77bfdfbdbfff2fff7fffbffb6f9fdffddffffeff7dfffbffe7fbddffb3fffffffb7ffeffbed6fbefffddf7f7fdbdbbff7cd76dfeffdbbfbbfdfff6dff7dfcbfff769fff6fdeef37f7fdffffffbfff5f7efffd779fdffeffff2fdeffeffffb77f7dffffe5fffdfedfff77ffffbfbeff3fdbfdf6fbdfe6d

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches40 : PLift ((OMA.PrimeProgression.composite primes 14 665242 12512) = mask40) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified40 : PLift (rows40.all (check 665242 12512 mask40 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct40 : ∀ r ∈ rows40, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified40.down r hr
  rw [←maskMatches40.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows41 : List Witness :=
  [(1764,771,128),
  (1090,1248,77),
  (1702,800,119),
  (1809,755,130),
  (1700,806,118),
  (1336,1028,95),
  (1243,1105,88)]

private def mask41 : ℕ := 0x3d7ff37da7ffeffefbefffffdfffdf7bedfadbf7fffdfff2ddffffef7eff7b7ff3ffffffdf77ffefafff7bb5fe6ffffefffcff7dffdfff6ffadb7fd6f97edfdfbdbfdff7fafffffffbfedfef6dfe7bb7f7fffefedffffbfbb7f6fffcfbfbfeffcffefffd2ddfdfbef7797efff9efffcfffbafff5ff7f7fbfffbffbffbeb7fff6feffbffb5ffffeff6fd77fefffdfeefecdf7ffdf74fe6dffdfffbebbffffdfeff5fb7ffff7ffbedf79bfb76bffffff2fbefffcd76ffdfbfbbfffedfedfff3dffefff9e7fedfbfdfff3ff7efeffefffeff6b7efbef7dfefffdffffffff5bbef35ff7f7efbfbffffefffb6ffffdf7f7fdfff6fd77bfebf7bfffbdf3fffef36f6ffbffffffffffb77fbcfed9b7bbffffdbff77bf7ffdde7f2dfeffbfffdf7fb7efffdfff7cf77dffffffb6fffb6fdffdffdedb7fffeffdff7ffeb77df6b7fff7ff5fffdfef7fff5ff5f7fff7dfedbf9fff77f7fffcffffe5fff9f6fffdffbf7bf7ff7d7eff7ffdff7feedbff7ddacfb7defffdf6fffffbfdfffeeffffbdffffeffffd7ffefbffb77fedfbf9b5fbdfefdfdfbfbf6bffbfefbef77ffebfdbe7ffff6ffeeff7fefd7efbfffdbfcf7effffe79fdf77de7bfdffdfefbfdfffb3dfbdfedffff77feefbfffdfff9e6feed67ff7ffffefbbfdfffffbf7deeffdfefba5ff5f7ed7fffffffb7fff7deffff9fef7eff7f7ffb7fe7f7f9febfff3fbefbffffff7ed3fbfdfbfbf6fffd3ffffb7fbe6bfef75ffdfffd7fffeffd9f7f769fffbff3dfffff7bf7f7ffbfdffffff7f9feff5fa4ff5ffffaffaffedb3dfffdbdf67fafff7f6ed3fffd9ffff4dfeffffefff7ff7bffbbfdedbefb7fd77ffedbfbeffff9ffdffffdfffbffbe6ffdd6f9f6ffdfe7dffdbffbdffffe7f7ff77dffbffdfff7fffd9bebfefefdeff3fff7bfedf7fefdefbf5fbefeff6cfffbbffb7b7ffbefefff4bb5f7fbaffbffedf36f7ef3df7ffb7ffefffdfefedffdb3dffffbffefff7ff5ffffaefedffffffde7bffd3ffffffd97ffeefffffef7df7ffbffe7dedffff77ffffffffdb76f7ffffd7fff6fbfdfffffdedbf7fff97fbbeff7dfdffebefd7ef3dfe5bfddffd6ef77ffff37bfffedfbfffeffffefbfdfe7bf7f7cffffefdfffbebbffefbfffefffff76ffeffddbf9feffddf797ed7dffdff5feef3dd3fbfebfffefffdf7ddffbbfbf7f7efaffafb77f7fdefff5fb6f7f9ffdeffffdbffffd7ff7ffbfdf6fff9ffbeeffdfaffb7befdbffe7beeffeb77fffdbdfedf7edf6fbff6fbeff7fd7ffeefedfffb3dffff7edfffbfffff7ff3fff7de6fbfffef6cf7dffffffdfff3dfffdfcbf6fef9bfff5facbfffe6dfdffdffdf37feffbfff7ffdfbfdf7fbff3fdffff4bffbfddffdfffbdd7eb7dfbfffcfffb77fefffffeffb5b7effffeffffb7fdfef3dfbfbe5ff6ffffeff75dbffffffffefdfffafb77ff7bbefe5fecf7ffeedffdffbfdfbfbefdfef77fe4fb5b7fbfff7dfbfffedfedfcffffffb3ed7ffffff79fdbbffffdfeffddafff4ff6fafdedbaff7dfeffffdbdbe7fb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches41 : PLift ((OMA.PrimeProgression.composite primes 14 680022 8686) = mask41) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified41 : PLift (rows41.all (check 680022 8686 mask41 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct41 : ∀ r ∈ rows41, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified41.down r hr
  rw [←maskMatches41.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows42 : List Witness :=
  [(1913,735,135),
  (1893,743,135),
  (1743,807,124),
  (1198,1177,88)]

private def mask42 : ℕ := 0xff7ffeffdff7bf4fbff67ffed7dfbffffdeffbffffbfdf7fbfefbdfffdaefff9ffd7ef3fffdf3ef6ffbeffdfbff77bfff2efaffbfb7cf76ffffe7faeffdd6ebefdbfffdffdf7ffefde7bf7fbdbf6fbfdb5dfebfef7effff759ffbb7dfefbfffdfb7ffe9effecfbddfeffedfff6efefff7f3fffeb6ef7fff6ff7ff7dfefbfbe5ff7bf7fbff7fdfef7fffe9fdffdfeffffdfedefdf7ff5ffdff7f3df7fbf7bfdffffbedbfbbfffc9efd7ddf5ff7ffdffef7cdffbf7bf7b7f9efd7ffbfff7ff7dfdfefff7fbdfffd6efffbbebfebefffff7dbafffef77f6fdbddedffdfffb7ffbffadbf7f77feffbffffbfdff7bfddefffdb37bfefbdfaffffbfddfefffffd9fffb69f7f7cffddffffff76fbffbfbe7f7dffff7dfb5fe5fffdf7ffffbfbfffb7beedeff65ffcffffffffef65dfdfbefff9fedffbfffb4fffb3dfef9bebfeb7fffedffdbffffbfffecfbffb7fbdffffbef7fffeffcfeffafff7ffdf7ff77dffff5be7bffdfffefffffbdbbfdef97dfefffff7ff7fbffff5bf7fbd977dfef35fbfff5d7edfeffffefb37feffefd3ffbef7e97fb7ffedbfff77ffefbffffbb6bf4dfff7ff6ddf7ffeff7faefbdff5fbf9fffffffdbedbffdfefeefe7fffbb5beffeff7fdbcfbefff9fffb7ffff7ffefdffff7bbffffbe7ffffffbeeb7f

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches42 : PLift ((OMA.PrimeProgression.composite primes 12 703028 3792) = mask42) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified42 : PLift (rows42.all (check 703028 3792 mask42 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct42 : ∀ r ∈ rows42, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified42.down r hr
  rw [←maskMatches42.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows43 : List Witness :=
  [(1997,711,140)]

private def mask43 : ℕ := 0x7fffef7edffbeffefff7ffff6ebfeffdbfdffff77dbddb7beff7df7ffffff5ffdbffde6ffdfe7ff7bfdf7fbfff7fbbfb7cdffbfeffdfefff5f76ffddffbeff3edffb7ef75fedbf7f67fbff7ffffff7feebaff77dbdbf6dfff3dfbddfffbdd6ff6ffffffcbfedffffdfbffefff5ffffeffffbfcffedf79eedf7beebffffef7ff7ffeeffcbfffeddf7ffdffef7fd7ef7ffb7fffd7ff3ede79ffbf5de7bbff6d9f7bf6bf7f6dffffb4ffdfff9fdff7fb6ffdffff7df2fbffbf7f77feffbffbeffeffff7effdbeff7edefdeffff9bdff7feff3ffeffeeffcbf7bffffdffffffffedeffbfbe6ffd9fff7ffefdf5bbffeffffde5fefbb7ffeffcfffff7bffffefbff6fdf6b7fdffbeedfddf6f77fffbfedfdbfeffd9efbeffbfbeffffdf7feefe7ff7fb7f6effdfffdbefffbf6f7ffff9f7f7dfefdfefe79fef75fffdbdf3dfefbffbffbaffbfff7f7f9eed7fdbfbffffddeef7fffffefff5ffebeffffffcf76fe6fffffdbfffbfdfff3ef67fbdbfcdffbfffedbf7ffddfff6f

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches43 : PLift ((OMA.PrimeProgression.composite primes 12 709934 2995) = mask43) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified43 : PLift (rows43.all (check 709934 2995 mask43 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct43 : ∀ r ∈ rows43, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified43.down r hr
  rw [←maskMatches43.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows44 : List Witness :=
  [(1181,1211,87),
  (1807,792,135),
  (1401,1022,103),
  (1078,1329,80),
  (1287,1116,89),
  (1387,1037,95),
  (1106,1302,76),
  (1742,827,121)]

private def mask44 : ℕ := 0x3fff5fffbffdfebffdeddf7f3efffffff6fbe7bffbf6f6fffdfbdfbcb6fffdff7bafbf7f7ffbff3fff7ffcbefbeffbdfffb7eb76ffff7f9b7bf7ffeb2ffeffffff5def9edd6dfffffef77faefeffbffffd7ff7edffbacbf5f6fffdffffffffffffbfdf67fefbfebffdbffffffff37f6fd7fdffff7fbedeffbffefdffffcff7fefdbdbffffff76befd7ffb7fffbffdbdfb7fedbbfffebbff3dffebb7ffefbdff5fbff7effff7fdefffeb7ddf7f7fdeddbfffff7fb7dfff9fcf7df7eb7effdfffbf7ffff7ddbfffffbebeedbdf77dfffbfd7ebfffffdbfbbfdfefefff7bb6bfdff7dfdffdfeff7fbf7f7ffffff7f3ebfffeedffbfdfbf9fffffd37fefbfff7fffdfb7fecff6fe6bfffafffdf3df7ef7edffffff75ff7f7dfffbb6f75d7ebbefffdfeffefe7bffff7fb7bfffeffacff7fe6ff7feebfffeffedbff97ff7df7fdbdffed7fdfef7fffeff5dff92ffaffbff7dbf6bfedbfdfdf7dfffbfffbfbbffbdb76ffcdffffffffff7dfff7ffffbfedffbfeffdff7fb7defffffedffdf7fbf7b7ef3f9beff7dffffffffdfefbff6effffffff5bbfbeefacf7ffedfbfb77dbff6ffefffedefdfeff5fefb7ff7fd6ffe7dbcffcbf7dbddfdfe7b7effeffdde5feefbff6fd7fdfffefff7ffffeffbfbfdbfef7ffeff7fdfffffffff7df75fbfb77d7ffbed7fffdbb6bff9affeffeef7ff77bfffefdfdfbf96efeffbffbfbf5ff6fedfffdf6fbfb7ffafff7fffb7fbefdbdffdbeff3dfff9bedefbf5ff6df7b7fd6dffffffbfffafffffa6f7d9f7ffffbffbdbbdfffdfefffffcbfdf7fbedff7fbffffdf7d7ffefffdffed7fdffff5ffcb3edffdffdffdbff7edffb6cff7bf5fffbf7dfdff7ba7fb7fffd3fdbffffffefe7bbfffffbff3ffeed7fff79ffffffffb6fff5fb7bbf9e7f6fd7fbbfbfcffffeedfffbdffdfffdfefb7bedbbdfeff7ddf79eeb76ff7bbffbffeeb7fffff3efe7ff5ffef6fdffde7dffbf6dffdfdf3fbffbf6f76ffdfef9ffffe9febedf77bffbf7bf6fefffffecffdf6fbefdfdffefb79ff9fefbdffff75dffbfffedbfffb7dffffefef9beffef7ff2fdb7deefbfffeb7fdf5bbfffdf76f7efaffffbffbffffdda7feffbfbfeffdf7ffb5ffefffbeed7fbfff7cbeffadfbddffbf7d7ff6dfffdfefffb67ffffbfbedff5fe7dfefbfbfff36ff79fdfb7faefbfd67d7dfffffdb7fffef6ffe7ffdffeffffafffddeff77dfefffff79feffef77ffed3dffffbfd6fdfef7fdedf7ebeeffffffdefbffb6ffbcfbfdfdf77dffdbef7fbbffbcbefdefdbdfffbf6bfff6dde7fbefbdf76defff7ff7fbfb7edfcf6fdfeff7f67fadffffbebb7fffbfefa5ff5bfdf6ffefdedfffff7feff7ff7fbfeffdbfffbffbfffefff967fffd3fffeb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches44 : PLift ((OMA.PrimeProgression.composite primes 13 715096 7834) = mask44) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified44 : PLift (rows44.all (check 715096 7834 mask44 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct44 : ∀ r ∈ rows44, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified44.down r hr
  rw [←maskMatches44.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows45 : List Witness :=
  [(1099,1320,77)]

private def mask45 : ℕ := 0x1febf5f76beedb7ff7f7effff7ff7ffedff7feffeddfffe5bffffe9effefdafbbebff9fdf77fefff4fefdffffdffeff7feffbcfffbeffff9fffafdafdedf7efefdffdfdfffff59f6dfeff7df7f77f7ebffffffbfb7fbffffff2fbb7f7fd7ffaef6f9bfff6fffffedbf9feb77f7fb3ddefbeffbfd7fbffd7fff7ffffffffef7ffeff3dbffdfff27fffbfff77f3ef2ffffbf7feef7edfffbebfddefbffffffffff7ffef7dffddfefffdffdeedbffafffdfefd7fd7fffcffcbe7fffdf7dfdfffd76d7ffa7ba7ffdfffffff6d9f7f7cff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches45 : PLift ((OMA.PrimeProgression.composite primes 11 725340 1649) = mask45) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified45 : PLift (rows45.all (check 725340 1649 mask45 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct45 : ∀ r ∈ rows45, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified45.down r hr
  rw [←maskMatches45.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows46 : List Witness :=
  [(1165,1256,83)]

private def mask46 : ℕ := 0xff67bffbfcbf7fffd7fff7b7fbf7ffffef9efffef7fb7dffffedbf59f7fbddffffdf76f7fdefdb5dffffebf7ffffe5ffdbf7dfffbefffbb5bf5feffedffffe7ff79ffb3fdbfffff7ed679ffdfffb6fbffe6d3ffe7ff6f7fffefbff6fdaff3fffedbdfffba7ffefeedfeffd9f7bfefe7bfefbf9ffff7fffb6cffdfaff7f9eeffeffffeefffdfff7ed7ffffff7befdbffffffcf779fff7ffffdadb34defffffffdbdfb6dfff3ff7ffeff7fdf7f3dfedbbff7cff6f6ffbfbffbffb7fffff7ffffffff6ffadf3dfedbfefef97dff7db7ffffffffff6fdf7ff7ffff2fd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches46 : PLift ((OMA.PrimeProgression.composite primes 11 731620 1748) = mask46) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified46 : PLift (rows46.all (check 731620 1748 mask46 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct46 : ∀ r ∈ rows46, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified46.down r hr
  rw [←maskMatches46.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows47 : List Witness :=
  [(1832,807,132),
  (1919,773,133),
  (1476,1011,106),
  (878,1703,62)]

private def mask47 : ℕ := 0x36defffed7dfffbffde7dbffeddbfffdffefedfbfbbef7fbffffff7fbf7fffff7daffaffecf77bfe9fdfedffef3ff6fd7ffffbadf7dfffdfffff9f7bfffffffffbdfffb75f7ebbfdbdffffbef67ffffbfbe5fb7bf7dfcf37fffb77ff6dfff6fffefbfdf6dfdfbdffdfbfd7fbbeff7ffdf3dff7ffef6ddbeffdff7ffffbd9bff3effff6dff7ff5bffd7fffffe7ffebfff6effffb7fefbb7d7ffbfffd9edfb7feffafd7dbfff7fffffafd3ffffffebfef7ffffdedfbfbffd6fffdff6fbdbffffdd7fbffff5ff79eff37dfcffeb77f7ffbfdfff3ffeef3ffffbfcf7e9f797ffefdefff6b7fffffb5ffef7ebffffeff5be7bbdffffbddfffe7ff7ff7dfff7ffbfff7df7b3cf3ffbdbf5deef2ff7fbb5ffcfffffcdefbe6ff7fffb6efffdaff7d9e6feefffbb7bbfdf7ffffff9fff7efffdfffeffeff77ff7fbff67dffff5f6eb7fffddfffb7ffffaedbdff7bfed7ffbeff79ffffcbfffedffffffbf7dfed7efefbffff5bef9afd7dfbff76f7fb7ffffdeff3cf6ed7efe7fffff5df7fbffbffaeffdf77fbfdfdbacfbffefd6dffdffebbf9ffffef3f9f4ffefffffffffdfff7ff66dfff7fdffbfffffb6ff7fffef7fbe7ffed6fbbeffdbffbffdeffb7fbfbfff6efb7bffbb7f66dfedf7fffbfff7fdfff3fdfdfbfffffbcfe5fe7bfcf7edefdeffb7ff5defffef3ffeeffddf7bfdfbfdbff7efffb7effdffeffdff7f3efa7fecbffffe9bffadfbfbbefeffbcfe5fffff7defffed6fffff7ffefb6ddff9aff77f77fedfaffeffbcbff9edf77bedfbff76f7dfffbfff3ef7fffdda5ffcfbef7ffbfff5bbfff7f7ffafd7ffbfffdbefdfdfeddbfffddfff6ffffbffffffe6ffcf7fbb7ff5967ffffefffdffef7f9efde7fbfbfff7edfffff9efbfcffeb7ffe7fffffffeff7ff6f9efbf5f7fbfeff79fefbefe7b7ff77fffff7ffeffdff7dfeb7dbf7ffdfafdbef7f9ffdfef7dffdb77fff9fffedff4fbfbf7daffbdfbff7dd7fffefbffe5f7edefdffdbfbbffffdffffcd7fdf5fb5beffafff5feeff7fffb3ffef9ffbf6d6ffeffffdfdffffffdeffbffefb7fbfffbffedffcf7dbe6f7fdfffffffdff7fbdd3fbffff7f77bbffeffbfbf7bfedffffffffbbddfedbff67fffffdfffbbfffdfe7b74bf7ffeffdfe7f7ffffffefbdffdfffffffafdffbffb76ffebffff7dbdffedffdbff6ddafbfdf7edeef7dfffff7deffefdadbe6ff6ffff2fff7ffeffed77f7efb5fe7ffff7fd7fdffbffffdbfedffd7fdbeb7ebefffffa5bffbfffefbfef7dffffff9f7b7dfaffffbf797fbfedbfdaef7fffedecff7ffdff7d7efbed7f9fdffff77feff7dfedfb79ffdbefbffbdff4fffdffff79f7f7eff7f2ffffbffffdd7fbaedf7bb7fffff7f6ff7dbafff7ffeffdf6fbfdffef6ffbffffdaffb7d76bfdff5ff7b7cdefffefffdfebf7bf797df3ffbff77fffffddfffbff7cf7ff6edbfffffffbffdeffafdfefbffeffeff77dffbbfb7ef7ffefdfff7ff6edbfdf7fffffe9ff97ddffbffbffdfef3dfbfbbffbfdf6b7fdf5bfebff9eef3ff3fffdffdffebeffafdfffffde6fbdfafbfdfbffeffbfdeffffffdbf7dfffff9beb7fffffaffe7ff5f7cdf7f6eff7bbcbffb6effff77fffffefffbbdf2ddffffef67bfcfbffeffffffff3ffffbf6b779ffbecfaffbef7dbfebfedefdf7f7f977dffdbdfaefbff7ff2fd3ffefffef77fffdfddedff7ff7dfdfe7ffdfbfffefffff5dfdbb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches47 : PLift ((OMA.PrimeProgression.composite primes 14 739212 9722) = mask47) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified47 : PLift (rows47.all (check 739212 9722 mask47 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct47 : ∀ r ∈ rows47, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified47.down r hr
  rw [←maskMatches47.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows48 : List Witness :=
  [(1896,794,136),
  (1554,970,112),
  (1332,1134,94),
  (1906,795,132),
  (1226,1239,82),
  (1200,1266,81),
  (1447,1055,99)]

private def mask48 : ℕ := 0x7e7ffff37b779ffdf7dffffffeeb7df7dff7f77defbfef6f9fcb7fffffefffffefffffffb7efe7fbefffffe9fffbffbfbb7dffd6dfa7fffbfdfffbeddfdfbfbb7bffd7cff7ff7b7efeffbffffbfdffdfffbbdd7fbbfffe9fef3fff7defffdbee96efbfff7fbfff6d7edefffff3fffebfff7ffaef3fbef9fef6fdffffcffffefff7dbff77df7bbdffffbfbfef7fbbfdedbaeffeffff6efffffffb5f6fdbef7fffffffbeeffdfffdbdbb7ff7dfdfbf9f7ff7ffefbffffdbebf59ffbbdfff9b7ffcff7ffdde7feeffed7fb7ef3fffffbfb77f6fde7becffeffffefdffffffbfdff9fffe7de7f7ff7ffffdfddbfbf6bef9ffd7fbf6ff6ff7fefffffaffbfffedffff7fb7ffffffdbffffff7ffdbe6fbdfbdffebfefeffffffdfeff77defdafdf79feffeff797fffdffff7df7fbffdbffa7f3fbffffff7dfe4bffbefffffafdffb7dfffdbfdfdfedbb6ff7bfff2ffe7fffdeffffffdbbfb7fffff3efffff7b779fffeffedbfdfbcf7fffddbffbdfbdbffd6ef67bfffbfffeffdfffdfff7fd679fdf7ffb5ffffffd2edffffeb3fbffdfcffdfafbffbfebfefe7fecffcfe7beff7ffb7bffb6ff6ffff9ffff4ff6beff27dffff7b7fd3efef9ffbffdfffbeffffb6fb7fffbefffdbfff779fefeedffbe5f7dd6fd7dffffbcfbdf7efaeff7dedf7ebeffbffefdffffefeefbdfbd9e7bb7fffffedffbbff7fbfffeffffffebffdf7bfcffffb7f7f9eff7fdffff6fbdffefbffb7ff5ff4f7fdfff7dfecbf7deffffffffafffffefdfff6fff7f7efffd6cfff9eff77bfffeffefbbffbdbffffedf7bedbfddffffffa7fedfb6bf6bfddfdfffffedf7fffffffffb7fdeffefdffbb6fbffef9eef6fffffffbf7f7effdfedf3edffb7dffdffdff7f77ffdfffbfeffeff7dffd75facfffbf7fbdffddfffb4f7fb3fdefff5ff6feffbff3d9effffd7fffdffdbbdfffbf6f7dffdffdfbffffffcdffff7f7dffedbddf7ffff7ff7fbfef77faff37dfedefff7df7b7ffef9ffd3fdfffffd76f2fff7ffdfffbfeffddbdbbfbffbefffed6ffecffcfffffdf7ffffffe9ff9fdfffbbdf77fffdfef7fdbffb79ff9fdf3ffffff7fffbadde7fbeffefefd7effdfffff5ff7f6efe7ffebf7ff7fffd77ffffbebffb7cff5bffffff6ef7ffff9b6bfffefbfedbfdf7ff7ffebfffedde7f7f977dfddf7fe6bffde7dffffffeeff7beedefdffdffb7eff6fbff7dfaffbdfeff3fffd9ffffd9f7d7fffdff7f7ffffbefdf7ff5fbcfffffdd7ffbffbfb6ff2df6ffe7f37fffdfdfefdfdffffeefbffa7fedbf6dffffef7f9fdf7eff79fffaffe7ff7b7ffbefbddf7fbd9efdfed7fffeffff6ff2eff7fffbbdb66fedff7ffdff6ff7f7dfffbfffbff7fbbffffdbff7eff7dfffafffef7ddffbfffbffeffbfff7bfeffffaffbfdffffdd7ffffb7eff7dfffb7ffeb77fffbbdf6fbfff7cd7efffd6dffcf3efffdeefffdbebf7b77fffdfffe4fffdfefffff7fafbfdffedfdfff9ffff5ff6dffff7fbfbbef6ebfdff7dffffdf7ffefff79f7bffbff9adfff9eef77bfef6cfb7fe7fffbef9eff3dbf6ffffe7ffffa7ffffbdf77fffd77dfcb7f9fe9fefaf9bfffffefd7fdfffffbfefff9eeffdfb7f7fffef7cdffbfffbdf7fffef35ff7bffbe7fffff7bffff7fefffddf5dacfffbeef3efbffefffff7ebefdffffefb5ff7fedfedbb6f7edfff7ffff9fef7dfffd6fdfffe7fb7d7efeff3ffedffdb7fffffffdecfb7fffdfdffffe7ff7d7ebffd65ff6ffdffff7ef7f9fffffb7ffafff7ff4fffbeefeefbdfbdffdff7fafd2fbffff7b67bfddffffef77bfffbfff5fafbbffff96ffe7fbcbf4fe79fff6fdffffcb77bffdfdbfefbff7ffeed7fbbfbffd6edbef6fdf7ff6fefffffffdffbbeb7ffbffffdfdf77fff9bffe7fbdbbfdfff6ff3dff7ffed7effdffdfeffbffffbffdbdffdff7b7ffeffb79fff7dffefaff67daef3fbf6dfdfeffbdbbdffef7ed75fb7f7ddff93fffddfefffdf7bfefe7defffeb6fb7ffffffcff7be7f7cfffdf7bffbffdbdfeffbebf7d7effffaffffffffefdfef7dfbebffbffbfcdfffefffcf7ffedfbffa5f7fff7ffdfffbf4fbfbf7d3ffffdefffffeffbdfffffffbfdfff7dfef9fdf7edfebeff7fdf7bfcff7f7efbdfe7bffdf7f7edbf9fffbf9effeeffffaeff597fdffd67ffff3cb7efefdeffbff3fdf7fbffbfff7fbefffb7fd77dfdbfefeff7df3fdfff77f7ef7ffeffefffdbfeffcfb7fbfbffbeed6edf7ff4ffcfffffdf75ffdffffe7dfefffdf5b7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches48 : PLift ((OMA.PrimeProgression.composite primes 14 752712 12751) = mask48) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified48 : PLift (rows48.all (check 752712 12751 mask48 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct48 : ∀ r ∈ rows48, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified48.down r hr
  rw [←maskMatches48.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows49 : List Witness :=
  [(1615,952,113)]

private def mask49 : ℕ := 0x7ffffdffddf7faffeddffffedf7ffcfb7ffcf3ff77dffdbfbbcffdffed7ffff9efb75bffffdffddaef77dffbfffb7bffffdffef6fff7fbff3ffffbafd3dbbfbf6df6ffdffffeff7fdfff7ff3ffffff7dffffedbffe4fbff7ffbff65deef77b7f97ffe7ffff3cf6efbff779fdfffbf7f3ffffdfebffb7ff7fdffff7ffefefbfeffffedfb7d7efecfa7bfffbff76ffff75fedb779eff7ffafff5fbdf7ffbff6ffbdffede7ffdf7fbaeffdbfff7edbdffefffff7d7cfffffdbbfff7dfdfefbfeffcbffdedf6fffffbff7ff7ffeffaffbfdffb7fdf7dffbbfbf7ffdf3fff7ffebfff7dfffbffffeffe9ecf3dfaffffdf7d3dfefbfefbdbf6bfffefffef7fbefdbffedfbdf7df7ffffff7bb4bfcff797df3ffe6ffebfffeedfdfb7ffdb67ffdff7feefbfdeffbfd7fbf7ffffe7ffffaffef

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches49 : PLift ((OMA.PrimeProgression.composite primes 12 768740 2423) = mask49) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified49 : PLift (rows49.all (check 768740 2423 mask49 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct49 : ∀ r ∈ rows49, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified49.down r hr
  rw [←maskMatches49.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows50 : List Witness :=
  [(1850,839,134)]

private def mask50 : ℕ := 0x7fffbf5d7ef6fdfffeebffff7bfdf7ffbdbbeb77dbefe5ffdf7cffffeefffbffffffefdbed6f9efbf79f7bedffdfbfffeff7dfdd7ffe7ffffeff2cfbffe7ffffe7dfdfefdfebf69efffef77bfdff5deff7fdff9befbcbffdfffafbfffffdf7b7ffbfff7fffbf7bfeffdba7ffdbeeffedb7ffff7ef6f9ffdb7feeff6f6fb3eff5fa5ff6fffb3fdffdbfbffde7ffff6fdfffffff6feefff9fff3cbeeffed3ffa5ff5b6ffbeff7bedbf7ff7dfffffffdfbfd7ef7dff7bf7f3ff7f97fffdffffb7ffff3ff6fdefffddfffffff7beffbfdeebeef3ffffbbf97fffedb7ffdff5fefffffa7fbdfffbffbfffefbffbfefffdefd7fff7f7cbfffbfdeddbeb7fffff7ffffff7ffed7edeff3ffeebfff76d6df77dffbb5fe7fadfffdffffffefd7efbfdefbb5dfef7ffed9f7b7fbf7ffed7ffeeb7fbffbefff7ff7fffbf7f7ff7dbbffb7f76fadde7bf5f7fff7fbfffdfbdf36fefd7ffbddf7fffd7edeffffdff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches50 : PLift ((OMA.PrimeProgression.composite primes 12 776075 2775) = mask50) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified50 : PLift (rows50.all (check 776075 2775 mask50 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct50 : ∀ r ∈ rows50, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified50.down r hr
  rw [←maskMatches50.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows51 : List Witness :=
  [(1969,809,139),
  (1777,898,120),
  (1658,965,125),
  (1384,1160,94)]

private def mask51 : ℕ := 0x5beb7dffebaddfdff7fffb7effdfbfffffffdffffdf3ffeefb7f7efedfffdefbbf9fedfdf7ffeffffdfff3ffefffffbf9fffffd7fbbfff6b7ffaddfdff6fbfb67ffffbfbfdbb79f6d7fff7feefbdf7effffeffeff3eff7dfffffffdbfcffefffff5fb7bfedffffdf6ffffff6b77b3dfbfbfdffeffff7cff7faffffdeedbefeffffbb5fef9bff7ffffbbff6fdfffb7ffdff7dffd7fff7fbdffd9eff6ffafdb6ffdffefbdfbfbfff7dd77bfedf5ff7ff7b6ef3cdefffff7dbfebfffedffffbe977ffefbffb7fb6ffebeefffdfef7dfe7d7cf3dffff7fffff3efedff7f7ffffffff7ffeefffdeff6ff37dedfbdfefffffb5faffbff6fdfffff9efffeffeb2fdff9fffffffff2cdffdffffddfef7efbddf7ffff77befd7fbffbffbfefffdb79f5f7fbffdbff6ffffffff7ff7df7ffffff6f6fbbffffffefffde7d7fdbdfaff75d7fbfdff5fedfbfdffbefd7fbe5fbfbfedbffffbe7bfcbe6fbddb7feefffd7effffeddfffbef6ffafdedff7b37ff7feffff9e7f75bf7fbfff5ffdfffde79fdd7fbfdfffd6edfffe7fe4fbff6fbeff75fffff7bffbfefffbfdf36f6fbefd7fffff3d9f7becfefdb6ff4b7ffffff79f7f3fb6fdfdffdffefbdffff3ff3fdfdbf7beffeffb5daff76ffedbffe7dfff7fffff6ff7fbbff379ef9aefffffefffff7f7fffffffffcd76fffdfdfa5ffdde7fbffbfbedbfcb77bbfd6ffbdb7ebf7d7efa7fbffbddefbffffddffbf4dffbaef2fffff7ef7ef6ffffbeefffbfff7df3dffffb5d67dfdfffffcff4fffffddb7feefffbf7d3ffaffffffff6fbfffefffeff7dfff6fdbfdb7f7fffeb6ede7fa6f7ef7ff7dff7fe7ffddefd7ffffff7ffff6fbfff6ddbff3ebf6fffffffffffcfefdfffffff5b7fbefffef6f9ffffd9f7feddbfffdf7efefbefdffbfdffdffeffdfffbf6fbdffefefdbffbffbfffef3dfefbe7ff7ffefeedf79ffbffbfffbef7ddfeff7f7ffeddedbaff7e9ffffff3fffffffdefffdfbfdfffb7b7f9efd7dfbebfff6ffbef7fffdfbfdefffef77bbebf7fffd7dfffdaff77d7eb6ffe7fadfbfb7fffcff5fffbf7ffff7ef7fdf6b77b6fdbdf75ffefffff7ffefefdffffedefd6ef7f9bef7cfffb7ffffdfff7fdffffffff9befbfffffedfbffa7ff7d7ffeef779fffffffeffdfbfdbdffefeff7ffffda5bfcdffb3effdffeff5fefffff6ffeff7effffbcfafdfdfffbfff7ff3ffbfbff97ff2edf7ffebfdbe6bfdfffdfdbffbeff7ffbdfffbf6ffefffdfdbf7f75df7dfefad9ffbf6fffbfedf5dfdffdfffdfdff7bb4bffffefefff7bf5b7db7efadf7dfefbf7beeffff77dfdffdd7eb3fffdffdfb7ff7dffffdbeeff7dfefefffffeefffd76b6cd7ffbebffbf7fefd2fbf5fffb77dafffffffffefefffefbffe7b76dff9ffdffdbffffbffffedeffefbf5bffffcfeffe6f7effff7df77fe7ffddf6ffeff79ffbbef7f9bdfbfdfdfffffffbdfaddffff7ffef6efe

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches51 : PLift ((OMA.PrimeProgression.composite primes 14 796461 8335) = mask51) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified51 : PLift (rows51.all (check 796461 8335 mask51 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct51 : ∀ r ∈ rows51, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified51.down r hr
  rw [←maskMatches51.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows52 : List Witness :=
  [(1774,912,127),
  (1773,913,123),
  (959,1688,68),
  (1342,1207,92)]

private def mask52 : ℕ := 0x3effbfdeffbeffff7cfbdbfdff5f7e9fff6fbf5fffbffdbff7dff7f7fff7ffffefdbfffff7ed7dfb7bfdffff6fffff7fde5fb7ffebffdbffacbfefffdfdfb7db7fb7fffdaffedfffbffff7dbef6dfbff7dbffb7eff5fbef3dfe7feefb5fbfbbfffffffd67fefb7df7ffeff7ffbff7ef7ef7ffeffe7fbffffb3ffffffebf5be7ffefefdfffff9ffbfffb7bedffdffeffcff7fe4bfdff7defd3f9ffbf7ff7faff7ffeef3eff7f3ffb7bedb3ffffbffdffdfeb7dffffefdefbb7ffebf7ffede7dfffbebefffedbffb6ffffeff7ddfffefff5bffffff3dffff3e9ffbfcff5dfdbfefff9bef77fbdf7ddffdecf7fffff7ed76feefffffefffbefd7fff7ffeffdbefd7ffbfbeffb5f7ffaffb7ffff7fbf6dbffefde7b37f7efffd6fffeb3fdffdfffeffffffcffff3ffef9e7f7ff6ffeed7dfe7ffddf6ffff6fff7f3fbfffbffffdbdbf6dffbfdffffaff36f7ffeefff9ffff7fe7f7ffbddbefffff7bedfbfbeef7cbfeffdf7dfa7fffb77dfdfb7bfeff6f7f9bffefdeffff967ffcf6fff5fbedffb7edfffb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches52 : PLift ((OMA.PrimeProgression.composite primes 12 808944 3090) = mask52) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified52 : PLift (rows52.all (check 808944 3090 mask52 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct52 : ∀ r ∈ rows52, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified52.down r hr
  rw [←maskMatches52.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows53 : List Witness :=
  [(1567,1057,103),
  (1601,1035,104)]

private def mask53 : ℕ := 0x65fbffbfffffbdfeffffbb5fefb7ff7dff7bbfff7f7ef7fff6b7ffffffffedfb7f7fbeeffcdbfffffffbe7fafdb7ffffb5fffbbfdffffdbf7fefffefe7ffdbffffef7fff79f4fbcdffd3fffffeefffbf6ffffbddaff3effef7cffdff7bffffffeedff9f7f3ff77befffffbef76ffeb7ff3fff7bffdffffff6ffbcbffdfffecfbdfffffedf7fffdedbadfbfbffdfcff5fb7fffdfffeddf7ff6fffbff9ffdffdffbb7ff6f7dffdbeffffdff93fdfdffefbfdf7beddbfbf7fffbfebeefbdff6fffff6bffff7ffffbffffd6dfffffefffbfebefd77ffcfbe9ff97ff6fffff3fdfefffdeffbcffffefdfff7fbeffff9f7b7effdffdfbcf7ffeeff5bfffffdeef7ffffbefffcffefbdf75fedff79efffff7ffffff5defbbff7ffffffdffff7fdbfff7f7fb7fbbefaffeeffdb7fdfef3fbbebfdffededfb79f5bbff679fffe7fbefffff7ffef6fde7f7ef7ed7fd7fbbebffdfffffffdfffff7f7ffffd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches53 : PLift ((OMA.PrimeProgression.composite primes 12 828160 2759) = mask53) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified53 : PLift (rows53.all (check 828160 2759 mask53 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct53 : ∀ r ∈ rows53, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified53.down r hr
  rw [←maskMatches53.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows54 : List Witness :=
  [(1354,1244,98),
  (1410,1196,94),
  (1121,1509,79),
  (1728,979,120)]

private def mask54 : ℕ := 0xfd7f9fffffdeffffffffeff7e9fffeeffffeefbcdffd7fdb7bbfff5df7f2fff7fedfffb7effddffdeeb7fb76ffefafff7fbdfefbfffedbfefbffefffefefdf7f7fb77f6efbf9fcf7efffbedff7fbcff7dfefbff6fff7f3fbefdeff2ffbcffffff9bef7ffadffdffeffeff7ffdbf5dffdfdfefbfeffffffbeffffbeefbeff7ffdfb7befffdf6fffedbfbeeffff7ffbfd7ffbff7fbeed7fffdfe5ff7ffefeef67ff7f3fdeff7ff6dbb7b7ed77fbedfffecfffdff97fffdfffbf7fefffcdffdfeffef7ffefdeffeff7fdffd3ef67bb7ff4ffefaeff7bbfffffef9fdfffffebf797fb7ffa5fefffffefdfcffffefff79fedfdff7ffefb7f779fffbdffdf76ff79ffff7ffdfbef6fbefd7dffebbffffb7fdffbfff7dff6fbffefbb7ffeffffefffffbdfffb66fafd77bf6fbcfffdfdff7dedff6bfff7ffffdb7bfefff93ed7dbfdfffdf7defffffaeffdf7efbdfefff6fff977dfff7fbfefb59efdfef7fffeff6bfebefdb5dfffbffeffbff6f9b7fbfdfef7fdefff7fffbfffbfdfffa7f7fdfff3ffbfdf7fff96ebfdfffbedbff9ffdeef7fffdffffeedbffedfffbbfff6b7ffbdfbff3cdfe9fffefffeff4fe7defdffdefffff7fffcde5fbefbff7fbfffffbb5bfdff6d7ffff9feffef6fffffe7fbeff6fffffdfb7fffbfcf7ef7ff7fff7bf7bfffedf3fff7fffffebffff5faff7ffffdecfffff5bb7b7ffaffbffedfbfbf7fbffffffebbedffb7ffffdbfff7fffbefff7ffdfff9ffdfcdffbe7b7dff7f3fdb7fbefbdbeed7fdffbfebbff6fffff77fedfbefffbfffffdadb77fe7f3ff3fdefffffff9afdedfbdf77df7bfdffdfeffff9fffbffefbbfffdd77feefffff7fffffed6dfb7defb7ff7ffaff6ffefff7b7ff7dfedffff7edffd7ffffdfffb7ffff2fdadbf7b7fffef7edf5ff7f7fdf6ffef7ffedfbff7ef3ef7fff7f7cff7bffdbffaffb6bf7bffff5feffbefffbefde7fbfb7efefb3ffaf9efffcb77ffdfe5bfeffffffdeff77bbffb7f6ff7fd2fde4fb5f77fbffffffdbfeffe9ffff7be7ffddfeffff65fb7b7fdf7ffdf6fdbff7eff7fffdadbfdfbffefbeedffbbfff79f7dffffffe7f7efefbedff7feebfffffdfef7dd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches54 : PLift ((OMA.PrimeProgression.composite primes 13 842188 6260) = mask54) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified54 : PLift (rows54.all (check 842188 6260 mask54 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct54 : ∀ r ∈ rows54, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified54.down r hr
  rw [←maskMatches54.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows55 : List Witness :=
  [(1107,1540,78)]

private def mask55 : ℕ := 0x1fddf7f7cbffbffdbfff4f7db779fedf7fbffffd77deffaffe7ffffff9fdfb7ffebffdf6b3ef7fff7bf6feef7ef75fb6f7ffefffffaffffffeff7f3ffbddb7fff97ffffffffeebffdffdfffbffe5bb7feffadfbfffcffffef9fff37bafff7dff9fff6dffef37bf7beffbfdf6ff7ffff6dfe7bfff3fb7effdf7dfbefbfbffdefdbfffffbeffefffdf7ffdbb7de7b7ef2ddffffef7ffbffffdf7ffeffffadf7ffeffffffefbfdfdfbffbcb7fbfff77fedfff97fdbfff7deeffebe79fddbfffff7ffefbbdf77bbdf3dffedefffdbfffb5bf

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches55 : PLift ((OMA.PrimeProgression.composite primes 11 852390 1661) = mask55) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified55 : PLift (rows55.all (check 852390 1661 mask55 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct55 : ∀ r ∈ rows55, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified55.down r hr
  rw [←maskMatches55.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows56 : List Witness :=
  [(1631,1052,113),
  (1505,1141,104)]

private def mask56 : ℕ := 0xffeb7ff77dbffffbf79efdffba6bfeffebbffbdffdf7ff77d7ff7ffbebf7f7ffafdfffe5ff7ffffbffffffdf37dfeffcfa7fefbfff7fd7ffffdf6bbffffffcdffdefff5bf6f6dffffefffebffffdfbffe6ffdff7f3ff7fbf7b3fbffffdd37fecb76dfef7efffffdbbddfff7edfdff5f75feffeed2fbefffdffff7edff9feffff77d7edf5ffdfffd6ffeffe7feff7fbfebfffffdfdbfefe6ffdfff9bfbb6f7ffffdffffffffff7bfffffbfff7ff7eb7fff79e4ffffffdfcff7fe7ff5966ffedeffffffdbfededfffffdfbe9779beffdbadf3effeffffe5bf7f7fff7f7dfbfdbeb7ff7ff7efefda7f7fbeefedffffbfffffeeffefbfff7ffff77fffffdfafffed6fb7dffdfbfffefefbefff5dffffdbf7f3edbfbffbf7ffffaefbfffefbfdf7beff7fbfdff7fffdfdff7ffcb7efeebfffefdffffed7ffbdfefffdf77f6edffd6fdffbfedffbbef3ffefbf7f76facffd9fdffe9ffdeddffbffbf7feff7ef7ffe5fbdff79affffffdf7ffffdfdf7dfb7f3ffef

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches56 : PLift ((OMA.PrimeProgression.composite primes 12 857906 2954) = mask56) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified56 : PLift (rows56.all (check 857906 2954 mask56 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct56 : ∀ r ∈ rows56, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified56.down r hr
  rw [←maskMatches56.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows57 : List Witness :=
  [(1292,1341,88),
  (1967,881,133)]

private def mask57 : ℕ := 0xf6fdfdfffff6dffd77feeb7ffeeb7cff5fedfffffedfff7ffb4b7fde7fefdfdfb7ff7bfffffff5ffdf3ebef9effffff7fb5fe7f7df7fdfffffff7dfddffffefbfbfefbff6fffff7cf6edffde7dffff5dffb2ffbfdfffff97ef3dff7ffff7edffffefbfffeffdffffbffffffcfbdff6bbdfbdfaef77df7dbffff9fff3fd6ffeeffddfffbfdef9adfefdfebfdffff6fff7dffffffe6feff3ffa7fbff7ffffdffbefbfebe6fedf2ffaff7ffe7ffdff7fefffefffdbffe7dbffb7dff97cdedffff7fbf6fffdfdbbef7ff7fffff7ffaefbdf77feedffffcffcfffbbff6ffbef7edf7fffff7dfdffdffffaedffff7fb7bffbbefeffffbfef77f7efffbf7ffeb7f97ff3dbaffffbffdbfff7dedffdf7effddbfffdfffd7ffbffe5faffffdfffafffdfffff6bf7dfddefbfebffd7fb2fdf7deeffffffbecd7ffafff7f7ffbdfbfffefb7beffffd65dfdffffefbfef7ddffffffffbfffffdbdff7bffdbcfbfdb7fffd7efefdbfdfcfbfbefdefdbfbbeff7f77dbffffbecf75b77dfdfb7dffbf7fffd7ffbfbeffbfdffbeff7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches57 : PLift ((OMA.PrimeProgression.composite primes 12 866286 3128) = mask57) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified57 : PLift (rows57.all (check 866286 3128 mask57 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct57 : ∀ r ∈ rows57, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified57.down r hr
  rw [←maskMatches57.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows58 : List Witness :=
  [(1788,981,118)]

private def mask58 : ℕ := 0x3f7f3efafffff77dffbfddefffef7dffebffdbfffffbfffff6edffdf7fb7ff6fefdb7dffffebeffbff3ddeffbfffffbedffffffffbe7dffdfffffff4bfff2cff7df7fbfd6fd7efbdfbefbfb77fbef77ffefffbffffff7ddadf77ff7d7dfbdbedfbff7ebbff77ffefffff7defdeffffbfefffffeff5bfff7df7f9fffb7bf7ff7d77f7cfffff7bfebeffbdffffbdffffff97dfbffbfffddffbefd7d9bdff6ffffefd3ffa7ffff7fffefb5ffdffdbfefedffdfeeff5df7f7ddffffffbebffbaffe7deffffb77ffcfeddf7b7ffefdfefefffdffffefbfffffdbfbffdfef6fff7de4ffdffebeef7dfb6bffffef7efffdf5f37bffdedde5ffff77feffbfff7dfdf7dfffdffdefbfffbefe7fbffeffbefffff7f2fdffffff7ebf7ffdf77ff6fb7ffff3fffffedfbfbf7fbff6fdefbbfde7dbeff5fffb7ffeedeff75ff6bfdffff7ededfbfffedffbfefe7fb5fffbfffffdfffb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches58 : PLift ((OMA.PrimeProgression.composite primes 12 877014 2682) = mask58) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified58 : PLift (rows58.all (check 877014 2682 mask58 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct58 : ∀ r ∈ rows58, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified58.down r hr
  rw [←maskMatches58.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows59 : List Witness :=
  [(1486,1188,104),
  (1756,1006,123),
  (1145,1550,78),
  (1891,941,134),
  (1308,1363,91)]

private def mask59 : ℕ := 0x6f7ddf7dfff3fbbfb77ffefbfff7bedfbcde7fffff7bfdbfd97ffffdb7bfffb4feeffff7ffeebfeb77ffff7fbffffefefdfffefffffbe9fffbddefdeeffff7ebbcdffff5fffbf6dfffbfbffff7deefeff77dfeffff7fdedf6ffbfffebefdfefffffff37fffb2ff77ffefb5fefbefdbfbeff77dfeffffefff7fbfb7ef6fd7dfbdffdf6efedd7f9f6b7fb7fffffffdfefbffefbfffeffb7ffed6efefd75fbdf7f9fffeffffffffffbfff3ffffbffffebefdeed7dffcfbfbe7f3fff7fedf7dbff9ffdffdfeffedfef7df3f9bfbbff7f97eff5fbefffbf7ffffafbfebfddfebffdffdefffdf7ebfddbffefbffde7dfcfbfbf5ff7ff7bedfb7fefff7fffbfef7dff7fbdd7fbefd67fb7f34bfff3fffffbfffcbffffefffbeef3ffe7ffdd3ffa7ffdffef7fdf7bfdfffffffbffffdfeff7beef7dfb5ffdff4dfff7fffddbfbbfbeffbefffbe6f76df7b7fffdfafffff76ffed3fbfebbfb7fffff6fffdfffbffffff6fdefff6b7f9feffffe7bf5ffffbff6ffffbbeff7dedffffffb77ffff7fdeddb6ffcbffbffdbffe4fb5f77ffdf7f9f7f3fbef9bfdb7fbff7ffefdfcff5fb7ffdfef9bfffdbb4ff7feffbdfeffaef7ef7fb3ffffdfeffffffb7cdbffe7ff5f6fffdfffbeff7effffaddfffedffffefdbeff79e7fbff6fd7fff7ffcfbe9ffbefffffbfffeb7ef6ddfffe6ffdff7bedffffb6fffff6d7cf7fffdbf7ff6ffdfafffef3edffffffa79bdff6dfefffffdbfcbf5ff7f3fd7f9afbfedf7fafff7dfff3dfeedfcdffbbfbfd97fdfdf779ffff7f77fbdfe7fbfbf7d7ffbfffffeffffffed3ffefff4ffdbefd7ddffdfff7dffeffeffdff7ffdbffffeffffbefb7be7defdf7ff7bbff6efbfdefffeffff76fbffe5df7b7dffffbfdefdffbf6fffdbffffdffffdbffbaffef9fdfbfffffffd37befbf7de7d7efaffeffbfbf6fedffdfbff779fffbffeffb7fb7f6f9ffdf7dffff6fffd6cfbffe7f77f7fbfdfb7fbdf3ebfff7cdf7ffeffdff7dfff6ffefbbffeebbfdf7dfcff79ffffffffffffb7feffeeff7fbfb7cfefbbff7fdffff5bfffeefbfbfdffcdffdfef3fbeeff7ff7dbedbfdefff7b7efffdfffadfbef6ef3fff7df7ffef7ff6ef7fdfebfffffdbfdfdbe7bfcdffbffdb5ff4fbfb6ff7fd77bf7fbffe6f7ed37fecbffbef9bdfffffdf7ff7fbfff7fdb7bfedefbeff7dffcf7dfef9ffdff9bfbf7dfffffff5dfefbef7e9fdf7fffdfffbfedfdfffdeeff7f77defde7fffbfff7fb7efa79efbffdfffafdedbffff7fe7dfff7fbb7bfe9feffefbdfaeffff7fffff7dbf7bfff7effdd6fbfdffefffffff3ffeffffff6dffff5bffbfff7efeffeffb7fffff7f7dffdfaeff4bfff3dfbdfbeffef7ffffdf7bffff7feef6efb7dffff6b7ffedf75fffb77befbfff77fb5f7ddefbeff7dfbdbfdff7dffd7ffffffefffb7ffb5dfef7e9eff7efbdfeffffffffedfeffffb7dff6faff7dfedb77f7effefb7bbffbffefdbfffdff7bbe9eff7df7ffbff7edffbaffffbf7fffff6d7fff7ffdff5dffdbffefffef77fe7ffdfbffadffe9efffff7dfffbbfd6effefe79bffbffeff6ffeffb7f7ef7ff7ffeffaff7ffefdfdf3dff6fbfffedbdf7fde7bb7ffefafdbfdffb7ffe6f3df7f9b7ff5feef7fffffbcf37ff7fbffbfbf7ffffffbeffbfffcffdbf7d6fd35fefbf7ffeffefffbf5f7cfffdedd7fffeffedfeffef6fdfdbb5f7ffbeffd9f6bf7bffffcfadffefffff7bfddfdffffbedefffcf77fbcbf7defffdfffdfff75fe7ffffffffcfffbef9fef3dbefff7fff9efdfd9bfffcbff9fffff9f6fffff7fffdaffb7fbfdf7ffddf5feeffdbe6fefdbfdf7ffefeffbfd3ddefbbfffefbdfafbfdf76fff9fef7fbffff6ff7faff7ddefbfdb76fbffedffffbffffbefdfffe

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches59 : PLift ((OMA.PrimeProgression.composite primes 14 882684 10680) = mask59) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified59 : PLift (rows59.all (check 882684 10680 mask59 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct59 : ∀ r ∈ rows59, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified59.down r hr
  rw [←maskMatches59.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows60 : List Witness :=
  [(1872,981,123),
  (1845,999,128),
  (1526,1209,109)]

private def mask60 : ℕ := 0x7fb5ffedf6f7ff77bffbbfbf7ffdd67dfef3ef6f9fdff5ffffb6d77f7cfbfbbfbf7fffb7ed7dfffbf5fefd7dffdfbff7fffefeffadffeffef76beeff7fffff7fffdfed7ffffbfff7fdeddf7feebfff6edbffeffe7f7ffffd7ffffffdf37bf7f7cffffafff6f7fb3fff5fedfbcf7ffeffffbe7fffb6fd7edf7ffdffcffeffffa7ffff77beefbef2dbb7fb6feedffd6fbffffdfffb7efbffbff7fdfff7ffefff5f7dfeeb7ff7fbe5bffdfffeeff7feff77ffefefdf7daffffd6fdbeff7ff7fbefefffff6fdb7bff9effeedffbbef75ffffadfafdeeffdbf6d6ffbfffefffff7fbdf6fbfeffffef9ffff7fefb7fde6fffffffffbffdeff2fd779fefbddfff6fffd9ffffdbfeffdfbdfaff7ffffbfcf7dff6bb5bf7ffffeffe7fb6fffdaddffdfdbfefffd7ffbddbfffffff9afdfdffcbfdfeffeffffbe7ffef77f6ffafffeffedfff6efbfbafbfdd7ff6fdffff6fbdffeffdd77dbfbffff6dbff2fbf7fb7fffbbeffddfdff7fefb7dfaffffffef7fffedf7df7f7ddef9efff7fa7ffff7ef3fffffffbbffeeffffaffbeffeb6fb7ef7d9efb7dd7fd7ffedffdfbefefbbdfef9e7bffb77ffcdef9e7ffff77f7fffdbfeffddffd7efb7df5fbebe6bffff7dbff7efffbfefb7fa7ff7dfebfff7dfbef7f9fffafd6dffeff7dffffeff5bedf7fdffbeefbfbffff5ff7ffffe79feffcfe7fbfd7fdffbffdf6ffff6fff5fbffefd6ffffdf7bfd9ffdbcfbfbfefffdfefbffe5fe7f3eff7ffddfffbebfdfefffffb7ff5fbffffbbdffdfbdf76ff6bfcfefffdf7efeffaff7ffbffbcbefbfffefffff7ed7efeffff9fff7dffff7dfffffdbbff7efecdf7dffb77f7e9ffd65fffffebfeffeffdfe5ff6f7ffefff5db7f7fdefbfff7fffff7f9f6b6efedfbeffebe6dfefbffbdfffffffbfdfffeffffb6fffdfefdffffffe797ffbffbdf3ffffbffdffdb7f7fbefd3ff3ffbff7dffffbfff5feffbfd67ffffffbbffb7f6ffedfffbf7ffcffffeffaffedf7fb7ff3dfffbf7fb7d7effffffbb6ff6df7f7ff6dfffb7ffffbffdff9a7fbff6ff6ff7fbf6fffbfffbeffffeebffbffdfff25dfefbfffeffefe7fefff7fffbbff77ff5bf6fffdbfffdfe7ffd9f7b6cff7ffffffbf7dfdfbfffcfffb7fffcfffff6ff7ffffbfdefdffb7fff6dfcfa

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches60 : PLift ((OMA.PrimeProgression.composite primes 13 918216 6540) = mask60) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified60 : PLift (rows60.all (check 918216 6540 mask60 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct60 : ∀ r ∈ rows60, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified60.down r hr
  rw [←maskMatches60.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows61 : List Witness :=
  [(1963,945,139),
  (1578,1176,111),
  (1693,1097,118),
  (1618,1151,117),
  (1328,1408,91)]

private def mask61 : ℕ := 0x3ffdf3ffffdbff7d9ffbfebffdfedfdfeeff6b77ffdfffbbff3fff7deffbfbf7bf7dffffdf37ffef75f6efbff6ffffbbfde6fffff7fbdfbddffbfff7dbffbfdfffb7ddfdbbff7fd7fffddfffe6fbeb7fbffdf7fbcffff67ffeffffffbf5bef9bdf6fdefbffffeffefbffafbfffffb7fffdbfcffedff96ffffdfff75f7effedbfffdfff9f6feeff7be6ff7dfffbedf7fedf7ebe79effafffdfffdf7dbffefdfdfbfffefffdf7fb7bffbf7f3ffbfdeebffdfffbdfeddf7ffdfe6ffeffdfb5bffffef6cffffe7f75ff7fadfbfffefffd77ffefffbbff75feebbfdfdff7ffdff79fededfffff5f77beddbfdf7fbffe7ffdff7fb7fbffffffdf6fdfdfffbfffaffb7deff7ffffbfdfbffffbf7d7fbbfffdffffb7bf7d7ed7fffeffdff6ffdff7ff6fbd9eebfff7ffbfbff9fefbeffffe5ffff7ffeffffdfdf76ffedfffbffa7ff4feedefdff9f7bfddff9befeddbeff7ff7f7fdfdff6f7fffeffeff5ffebfddfffbed6fdefffff7ffffd37dbfbffbf6bfcffdfb7bf7f7f9ffd6fdf5f3f9ff9ecfefffff7fdffbaffeffbffffffffeeffffecfffffedfddbf9fdfffff6badf67fbdffef7ff7efffdeff7dffeb3efe5bfeffffeffecd3dfb7fffff7fedfbfbffffcff7befffffbfbbfd7ffaff7fff6b7cfffbfffedfecf7ff6ff3eff5dbdf77dfffffdf5fbef77fffb6df7f9f7ffcff7fedfedbfdfbcf6fffdfffffffbddfedbdf7fffffb7f76bbddadfeff3fd7ed7df37deff7ffee9bff7fff4ff7beff7ff7f9f6bfdf7ffbedbfff5f7ff77ffff7fbfebfd9e6dffdffbedfbfff7ffdde7ffebbfffffbcff5da7fbef7ff7edefff7bfddfff3ffffff7bfff76fbffbffeffff9fffedffdfefff5ffff2fff7ffefb7bf6bedfafdfff7ff77bffff7bf7ff6dff9effedbbcffdfefdeefaf9beb7fffef3ffb7bf7f7fb7fffcdfdbedffffeffedfffff7b3eb7ebbfff7ffcffebeef7eff7befbfeffffeffffbffbffdffd7ef7dfbef7f97ffbffff9fefbefffdfefb5ffcffdf7ffeffbfdfff37b66fffffffbeff7defdffffffbdbbfdfefbfffdbbfbbdfe7ffdfbdff7ffcd7fffcfbfffcfbedefffcd7dff5fffdeeffcffffffbf6fffffdf37fedffff6effff7fff7ffedeffbfdffbfeffdbe7bbfd3dffeff7ffefeefa5feeffdffff6fdb7be7ffdff7d2efffffcf3dffefefdffdfffbfd6fdfffafdfdbfffefbaffe7fffffebe7f7fd7dfefbf7df7feffaddfdf7ffffdedf7fbfdff7d7effff77ffffffff7deffe7dafbb7fffb7dfb79bfb3dd7efbffffff7fbfbff97dfff9efff7bfff2ffadffeffddffd7dfbfbfdfbfffefeffb79fff3fb6fbffd7dfffffefe6fbdfe7fedf77dfef7fd6ffbeb3ffffffff7ffbeff7fffbffdffdadffdf6fbfffb7be5fb7ff6ffffe7bfebffbffdfff75deef3fff6dfff7ffefff6ffedbfff7df6fbc9ffffffbfdafbffb7efaefffbbeffdfffdfdfb7fb5fffbfed3ffbffffbb6fffbadf7ffaef7ffffbfffff9edf37f6ffeedf7ffebf6fe7fbffefdb7ffdbfffffff7dffffdfeffffffffb7fffffff3ff77fffff7f76fffdadfefffeb6fdbdfffde7bfdfffb7ef7fdb6bf5be7bbcfedbfff7fffebffda5ffffbcf6fb7ffbdffffbff6ef7cfbffeef74feffffdbfffcf7fbfffbeffdfb5ffdf7edeef75ff7f3fbfff7ef2ffffffd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches61 : PLift ((OMA.PrimeProgression.composite primes 14 927518 9386) = mask61) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified61 : PLift (rows61.all (check 927518 9386 mask61 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct61 : ∀ r ∈ rows61, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified61.down r hr
  rw [←maskMatches61.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows62 : List Witness :=
  [(1766,1070,122)]

private def mask62 : ℕ := 0x1bfff7bf6ffffb7fb7ffefef9ffff5ffdff5dffb3fdbffffffffffbbffffdfff7ebefbfff3fff7ff7d7edfefefffef77fffdafd7fffdf36bfff3ff65fefbbedffdeffffffdfbdfe7feffafdb6fffffff7fffdde6fffff6deffffba7bffd7ef7dfa7be7fbeff7beffffffdf3e96ef7fff7fffff7dffbfefffdfdbfffffdbdfeddf6bf7b7ffffda7fafffdbe7deedf7faebfddfff7dfb7ff5bbefeffbdfefdfdffebffbfcf7ffffbbdffff6fdf5bffff5bffbfffbffeebfed7fbfcfedfe7fbffe7f7effdfeffffbf7ffdfffdf4bfdf77fbff7dffebbffe7bfffbdfaffffd6fdbffefdfdb76bffb7fdeffe7f77f7effddfffaffbdf7fdefffffbfff7beffeeff7ff7fbdbffbffdf7dfebfeffff3dfb79bff7ff6f93effddf7fffffff2ef6ffffb7dbf7b6efbfbf6f7fbfedfefffbb5fbdffffaed7fdfefbefffffffffffffffdf7f3ffffbb5ffef7fbeffe5ffe

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches62 : PLift ((OMA.PrimeProgression.composite primes 12 944810 2649) = mask62) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified62 : PLift (rows62.all (check 944810 2649 mask62 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct62 : ∀ r ∈ rows62, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified62.down r hr
  rw [←maskMatches62.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows63 : List Witness :=
  [(1819,1045,120),
  (1571,1210,103),
  (1512,1261,110),
  (1894,1008,134),
  (1815,1052,128)]

private def mask63 : ℕ := 0x1fadff7fe7f75ff79fdfefffebf7bfedbefffbf7f35f6fbefd6dffffbddeffffdfffffffdf77ffffbfdfdffdd7ff6fffdbbdff7f66f7ed3f9ffbf7bffdbffe5dfdfbfbffbfff7fbf5fffdefdfefffbfff7dbfffaefadff6bfdf7fbeffffbffffe97ebfdfffbbeffffefdffdffdeefb7f77fefdf7feff37fe6f7ff6fff5f3fffffffdff9b7fbfbe7fbfd6fbbeff6ffef3cfedde6ffc9ffb7fffdfbfbfffffdbfdbfdfefffbfeffff7ddaefffb7f93ffffdfff7efeffeef77fb6ffede7fffffdfffbffbfefeffe7bbeffcf7fb7fffffedbffbffdfdf6fffefffbffdfff37feefb79ffdfcf7fff5fbffefb3fd6fbbdb3edf7bedfffbf7b75dfebfffbdfbfffff77feef7ffb5bb7dffffdfefff7f7ef7fbffff7ffffb6be7ffefffdbdffef7f92fffffffffcff7dfdd7dbf7f75f7ff7efb5bfff3ff7f9fffffffebffd67f6efbfbffbf7fffbfdfbfdfdfffbefffffeffe7bf7defbbef7fbbdff7bf79ffd7dffef76bf7f7ffedfeef3fd67ffddfdbfdbbdd7ff7fdffffdf3effffefffddeebbeffed7ff7d9fff7edeffbffffff4ffdfffffcdefbf7fffb7ff7fdb7defffddf7f6efbffa7bffbefffcdbfbf4f7fbfe9bfdfffbff37ffff3efbfdfdbf7f6f97efefbb7fbfff7d6df6ffb6ffff7ffbfde7fa6f7fffffecfbffafbb7dffffefe7fedfbfffefbfdfdffff77befb7ffbdfedffffffbfeff5ffdf3fdffffffbddb7f7d9fefffdbdbb5fbdff7f6fdf7ffebffbf7feffe79feff6feffefff7dfcbffdffd7ffefdbdbbff7ff7fdfffb7ff5ffffffdffdffff7ffffbffb79b7ffeb7ef6cf75bbffffbf6f6fffffffbfdbfefffdafffff77f67dfdfbfffdfbef7fffff7f9febffdefbfffbffaef76ff7feddf79ffffedf7bfeff5fedffffeefbef7fbf6ffff7ffbffbdffffb69e7bfef25ff7fbff7fffffffffff7ebefd7efefffff7dd7ff7efbfdb7fbffef9fdff5baefffdefdeffaf9ffffef6f9fffbdffffb7ffebbdf7fdffbfdfffffefe7bf5f75fefffeffd9bfffdffefbefb7ff7fbff77ffff7dffdbf7deef3ffffff5f7ebefffdfbfdfcbf7f76bfffffdfdbf6ffffffff7fbdffc9ffffefffdffbfefffb6ffb5bfdf3df7fd7ff77ba7fbfff7faedeffffbf7f77defffffafbbff7edbeff5ffdbfcdfffeff67ffdffedf7bfff3fdfefffdf7ffffbfff5f7fdf7dfefffbffbbfb7ffecd2ffefffdfffdffff7deef7efffdfdfbffe7fffffedbffffbffffefffd7df7db

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches63 : PLift ((OMA.PrimeProgression.composite primes 13 950428 6989) = mask63) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified63 : PLift (rows63.all (check 950428 6989 mask63 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct63 : ∀ r ∈ rows63, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified63.down r hr
  rw [←maskMatches63.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows64 : List Witness :=
  [(1905,1008,131)]

private def mask64 : ℕ := 0x3ffaffbdfeed6df3dffeffdbfedfff37ffefffbf7fbddffdfdbff9ff9befff9fff7fffe93ff7ffbcf7dbfffefdfddfff7cdffbfefbfff6f7cf67fefffffadbfffeff7efffbefbbfff7fbffe7ffefffbf7bbcff5dffffdfefd6fdefbf7ff4fffffefaffffff7d7ff6cdffbfdf7eff7fffffdbeffffbe7dfffe7ffdf35fffffffbffbfb3fbeeffdfa5bfdf3ffff9fedf7dbffff9fffffffdffefffdf7b7fdbfdecffeffebffdfdfaebf7bfffbfdbffe7b7cb7f9ffd6fdefbbebfff7ffb7ffdfbfdfed7ffffbb5ff79ffbfff7ffafbf7ffffbddffdf4f7fbf7dfdff7bf7fb7f7fd7ffe7deffffffebfffeffaffffffedfff77fffbfff7fdfffffbf7ffefe7ffed6ffe6ff5bffbbcdfddedfbf96ffefff7ffffffbf6fecfffdfcbfefffdeffefffdffff77dfffadfb7fbfdfffaef7ffbdff6ff7b7ffbdbbff7fff7fffda7bedffddf7feddbffeeffddfefbfd77fffb7ebe6dfdff7fbeffef7fbfffadff5bf4feff7ffffdfdf7eff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches64 : PLift ((OMA.PrimeProgression.composite primes 12 960120 2858) = mask64) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified64 : PLift (rows64.all (check 960120 2858 mask64 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct64 : ∀ r ∈ rows64, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified64.down r hr
  rw [←maskMatches64.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows65 : List Witness :=
  [(1487,1298,100),
  (1478,1306,100),
  (1937,998,130),
  (1991,971,134),
  (1573,1234,113)]

private def mask65 : ℕ := 0x2ff7fbefbdde6feddf79f7bfcf7fbfdd7ffeefbebffd7effffadf7dfffdbed65ffff7fbffffefefdffffddf7f3fff5bbfffeb6effdffdbbefff9fff7df6ffe6f3fbffdeddffdffbbffffffffedfb7fbddffbffd7dffffffdf797ddffdb6ffedffffffefbf7f7df7ef6fdfffeebf5ffff3fdfffeef7fbefdfffa5fefbbfbefffffeffb7fb7ffe93ef7fff7bffdffd3ffffdffbffb77b3fdbfbbdffdbefffdd7dba6ffdf7ffbffb7bffb77f77bfffe7ffffbfdfebfff77bf5fbfdfffffdffbb4bfcbffffff7dfffbffffffbffafdefffe9ffb7ddfdbefbbf9f7ffcf3fffdfffffffedfeddbcf37defbbdfbfdfdb7edfefefff5bffffddfffbefbffeffffbffb7dfbfff4fbfffffedfffbe7bfff76dbcf77ffef3dbf7deffeffbfbf7ffe97ef77ffdbfdf6fffffe79bdf7ffeff7ffbfbf7ffdffef7dfffdfdf7ff7f9fed3fffcfbfbfeffeff7fe7ff7b6fdfff7ffadfb6b7effcff5bfffbeffff7ff7fffdf3fdfff7fd6dbbfffebf7f6dffffefffcdff9ffd77befbffd7fffdfbfbf5f76fefbfddfdffcf7fbeff3efe7fb7fb5dfffeefffdb7f7dbefbbfdaffafff6b77ffffafdfef7fb76dffdfdfedffdf7ed3ff7ffffbfcbfefaff77dbebf7feeffeff7ffffbff7edbfdfdbf5ff7fffbbffff9ffbffffef6efffff7f7ffe7d7efbdfa6fb79f7fffdefffcbffffffafd3ffedf36f7ffbeffffbdffefffdfefff9bdfbffff9bdf7ffbfbfff77bffdff9fefbfb7fdfdf7ffbffb5beffffff7ff5bfef7ffffdfffbfffef6e9bdfbdfaff7dffeffffffdfefbffff97ff6dbf6b779ffffeffffb4f7dfffbfefbffbeffdfffdffdbffe6b7ff76baffefdffffff7eb7ff6dbedff7fefdfffedfffb7ffefffdfffff6bf5dffbeffafbedf7eb6effffbfbb7fffdefdfef7fffff77f77ffdffffbffbeffebbffe7ff5ff6dfff3eff5ffff77bf7b7dfffbefbfcffffefdafdfeffffffdeef7ffb5ffff6ff7dfefdffbfcbeedffd3fdfffbfbffbbcff7dbffbff7f9bed75ffeffefff96efefffffffdfff6ffbdbf5fbff6effdff7ffdfb7f7ffafdffbfff3df7ebfffe5fefb7ef77ffdfe7fbfffffffdbff7dfbcfbffe7dffdefff7fffbffbbfff7df7ffeff7ffeff5bafbf7bfedfffffdf7ff6fffffdf3ffbef7ff67bfcf6ffb7fffdffbbefefff7fffdefffeffffbfff7bfef6ffbffeef7fd7fbeddf7bf7fffb7efeffefdf5f7fffffbdd3fdfef3ff7fdbdf2fff7ff6dfffeffffbbdf3fdf7f3edffdb7fffdf6faffafffdffdff797edfdff5ff7ffffbefe7ff7f3db779bfdf7fefbf7bffdfefeffbdf77ffff3ffffdffffd9ff9afffffaffffffefbddeffb7ffdffff7efbfffdbffbfef7fde7fe7ff7b7ffafd3dffeff7fe7ffff35dfff3df7fbfeffdfffbb7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches65 : PLift ((OMA.PrimeProgression.composite primes 13 965063 7838) = mask65) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified65 : PLift (rows65.all (check 965063 7838 mask65 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct65 : ∀ r ∈ rows65, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified65.down r hr
  rw [←maskMatches65.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows66 : List Witness :=
  [(1621,1214,105)]

private def mask66 : ℕ := 0xff3fd7fffff7dbbfbf7be6fafff7ffefffbefffdfedffff3fdf6ffffbdbb7fbcfeffefffddffbf59ef97efffdf6ff6ffffeffffffef7cff7dffd7ffeffffffffeff3fbffbbef7fffdf7dffdfbed7effcf3fbbdbffdffdfff7fdfdffdffff3dfffdeff7fdf6feefbfbffffdff6feefbdfe7fff9fffffdbffffffdfeeffffefdecfffd7fffdf37fe7f7effefbedffbfdb3ffe7d6dfffdafff6ffffbefe5ff5fbddfeffdf7ffaffffbefffef7fff5bfcff7ffdfbfdffffffe7bbdffdff7f7dfffbbfff5ffdfbdff7f6ffefbeeffdfffb6ffefbbff7fffeffffbfbf5ffddfefeefe7ff5bfffeffffd7ddfef7fd7e9ffffffeffbffeff7ff7dfb7ff6fe7bfdfffbaffffdfff3eff7dbff3fdfffeffbffffbff9eeffcd77bfff77ff7dbfdfffadff7b779fffeffeff36ffe9ffffffffbbfbf7d

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches66 : PLift ((OMA.PrimeProgression.composite primes 12 983947 2432) = mask66) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified66 : PLift (rows66.all (check 983947 2432 mask66 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct66 : ∀ r ∈ rows66, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified66.down r hr
  rw [←maskMatches66.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows67 : List Witness :=
  [(1149,1733,81)]

private def mask67 : ℕ := 0x6ebff9ffbfff3ffbff3fd7e9aeff5dfdffedffdecfbffeffffffffeffafbfffffbffbfddb7fecff7fffdbfd6fdfcf7ffffdfdfffdfffffffe9fff7fbe7b3fd7ed2ffe7bfff77fe7f6fdedff7f7ff7fffffaddeffbeff7f7cfb5be7ff7ffefbffbfdffbfefff9bfffffbeff7f7f9bff6dffff3ff7edfef67ffdfb7feff7ffedbbeffdbfefefdbddfdf7dfff97ff3fffdfffb7ffeefffde6f7effedfdfaffeffbfdffb7ff77bfffb5ffebefd77bfdf3f9f7dfeffdfeff77ff6fefff5ffdf7fb76dffdffbffbbfbe7dfdf6fffdffcfff9bffffffdf3efeebff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches67 : PLift ((OMA.PrimeProgression.composite primes 11 995609 1723) = mask67) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified67 : PLift (rows67.all (check 995609 1723 mask67 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct67 : ∀ r ∈ rows67, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified67.down r hr
  rw [←maskMatches67.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows68 : List Witness :=
  [(1910,1057,134)]

private def mask68 : ℕ := 0x6bf6feffbfff7dfeffffff97ffaf9f7fbcfffffffe7df7b37fff9efdbfff6b77ffeffffffffdf7fbefffddbfbfffbd967dbffefffdf7efffffffb7feff7eb7f9fffaf9ffb7fffff6fdf7ffdffdbf7dffdfdfbfb7fffefadfefba7f7fd7fd7dfb7ffebb5de7fbfffffffff7b76ffdffffbeff6fe6dbffb7ffff3ddff97ffefffffbffffdadf7fffff7f9f7ffefff9fff7d9eef7edfdffebfff77ffffe7ff7bfcbf79bfffffefff6ffffbefefda7ffedfe9fffeddfefb7fefb2ef3fde7ff6bf7f6efb5dfeffffeffffff5ffffb7dfffbffffbf7fbfb6ebeffedfeffbf97ff7ff7ddaffbfdffb7fdffbb7f77fef9ffd7fbffffc9fff6efe5ffff7df6fffdfbdffebf5f6edfff6f9fcbfffffffdd7ffeff76beefffff7bfdbffffffbeffffb7bbf9ffd6efffbfebffdf7baffbdbafffcdefbffd3ffeffbfffef7efbfdffff7ffefeffa7ffffbf9ffffdfedff7ffdfefdfffedbfef7ffffd3edffdf6ffed76b3ddb7ff5ffefff9ffd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches68 : PLift ((OMA.PrimeProgression.composite primes 12 1009435 2865) = mask68) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified68 : PLift (rows68.all (check 1009435 2865 mask68 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct68 : ∀ r ∈ rows68, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified68.down r hr
  rw [←maskMatches68.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows69 : List Witness :=
  [(1786,1145,118)]

private def mask69 : ℕ := 0x3fffffd7ddf79eeff5f6effdfffdeffbfb7ff3dfbfbf5f77dffbffdfffbfbff9ffdafffffffb7fbffbeefafdf4ffdf77fefdf7ffcffffe7faef3fffff7cfefffddbfdbffffffffbffb7db7b3effedaffe7ffffffbffd7edffbf7bfedfef7effdfefffdffeffeffdbbffbfdfff7df7fff5f7dffffaffffdedfffff7b7ef3ffffff5deebbffefffefb5defd6fffffbfffed7ef7ffbdff5fbfffebffff7fecfffdffffdd7ffefffffefdefdfdffebb6dfedfdff7bfffbfffef6ff7f9fffffbf7ffff7dfe6fff9febfdff7ffcfff9f69ffffffbcfbdb7fffddf7bf5ff4bffbefdfffaeb3fbfedffff5bffbffffff7ffffffdbbdbf7dbeffd9feff5ffef3edffbfffffbfef7ff7dbfdbbfdfff7ef2fdf5fbeffeffff7fdbef7ffef97efffdfdf37feff7effddfcbfdfe7baff3dfafffdbfffffff5fffffff6e9eedfdbfffffffffffdff9f7fffff7fffd7dffdbffbe7ffef

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches69 : PLift ((OMA.PrimeProgression.composite primes 12 1022485 2679) = mask69) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified69 : PLift (rows69.all (check 1022485 2679 mask69 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct69 : ∀ r ∈ rows69, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified69.down r hr
  rw [←maskMatches69.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows70 : List Witness :=
  [(1355,1526,94)]

private def mask70 : ℕ := 0x1fdffb7fde7bffb7ddf7fbfdffbaff7fbfffefdf7bb5ffcfefd7edbfbaffbffeffbcfffffdff5ff7bfffeffffbf7bffffffbdffdff6feffaffedfbffb7bef97dfffdf7ffdfffffdfe7fecffedf7b7fdbdffffb59eef6dfffffefffff69edfafffff3ff7effcffffb7ffffeefaffe7ffffbcbff97df6f9ffbffd7efeefbdfbdf7ff76f6ffb7bf7bfdffeffdf7fdfcfbfb77ffff6fffdfbe97ffbdf7ffffffedefbefd7fbbffffdf7f7dfffdfebfdf77bbfdffdaff7fb7fdffff7fb4fffff6d3dfffdeff76fff9fffbfdefff7ff7b7cf3dbbdfbedfeb6fff7dfdffffefb6ff7fffef7fffffaededdffffd9fe9ffffdff7ffff77fbffafffcfffbef9fdffffef

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches70 : PLift ((OMA.PrimeProgression.composite primes 11 1033865 2033) = mask70) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified70 : PLift (rows70.all (check 1033865 2033 mask70 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct70 : ∀ r ∈ rows70, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified70.down r hr
  rw [←maskMatches70.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows71 : List Witness :=
  [(1730,1219,116)]

private def mask71 : ℕ := 0x3fcfaffbfbf7f77bbfdf7fedfffbfebfdf7ffe5bb7ffeffcf3fbffffdbfefefffffbcffffe7bbfff5fedfb5dfed7ffff9bdffdff7faffbffefbfdff7fafffffa7fffb77f7ddfdfafff7feeffdd37ffdfbefeffefdaffbfffffefffdfb79fff77fefb7ff7fffffb7ffffffdbddbfbffffeffeffdffcffddefbeffbffefff7fffd6ffff9edfb7f77dffdf7faffbf9f6bbfffd9fdffff7ffffdffff7fbefffb3fd3dbfeff7bffbaffbffa5fffde6ffffbfbfefffff7deefffdffbf5fffbbdf6fffff77fe7fbdf7fbe7f36f7ffbfff7dbcfffff7bfedfdff7b7ffffbffdaf9afffff77f7effffeeffffeedfddff9ffbbeffedfff2dffcff7bfebfffefff5b3fdffb7ef77ffeffdfe7dfdffffe6ffddfeb6ffbdffeffedff9efdfdbfdff7df7fffff7dfff7fbefffffffdfeff6f77f7ffeffbffbedfffeef65fffbb5ffff3fdafff7f7cfffffcf

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches71 : PLift ((OMA.PrimeProgression.composite primes 12 1054435 2595) = mask71) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified71 : PLift (rows71.all (check 1054435 2595 mask71 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct71 : ∀ r ∈ rows71, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified71.down r hr
  rw [←maskMatches71.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows72 : List Witness :=
  [(1881,1127,125),
  (1543,1377,109)]

private def mask72 : ℕ := 0x3aefff9f7f3fffdbb5ffef6ffffd7dffffbfd7fdfdde7ffdfffbffffdfe7fefb77ff7f3eff5fb7ffefff97eff7ffcf7ffe79fdfffbb6ff7b77ffedf5bfffffb77b7fd7dbbeffffeff6ffaffffff5fffdfdf77ffebfe9779fff7ffb5ffefeffffdfddfeb7dbefffcf7dde6ffef7fffffaffeffffbffdffdfdbeeff5dffd3df7fde7b3ffffffffffffdbb7bffffffb5bfdfbff7ffffdf7fbdf74bffd6cffdfeef75d7fbfffffff6ffdff6d6dffdfb7fbdfffffdfffdf6f3ff7fdbfdf7defbf6ffebfeffdfbdf7ed7e9befffbf7ff7fe79effedfffffdb77ffefefff6f7dbeeffdfb7bbfff59e7faefffbfcffdf76feddbffffb36dffbfdfeffbfffdf7effffefdffbbdffffbfdbdffff7df7ebffdbffeefffbeef7ff7fff7bbfbe7fbffb7feebfffffffff7ddfff7ffefbfdfeffffbbfdff9eedf7ffcffefe7fffd7fdefbffb7eb7ffb7fbffbdf7ffffffffecbfd977f7cfffdffbbefe7dfdff7ffff76b6ed3dffdbfdfb7ffffefdffbffbfffffffdd7fbffff7dfffeefafff7fbffe7f6fd3ffbdffff6ffaedffff4ff7b7fdfffffdfcbfefefffffefdbdbf6ffefeffefbfcf3edffdeefefdfffffbfeffdfe5deffbddefdfefffbedfbfb6ff7ffbfdfff7fbfebbfdf7dfdff7ff6f7ff77faffbdf7ff3fffdfbebbfbefbfedafbf6f7cffffffdfdbbff7df6fffeffffefff7ff7fbfdefffdfbeb7ffafdfffeff7fbe7ffff65bf7ff7d6fffffffffdfb6dfffaffbdbbfbffd77f7cdfddffffddfedfdffffbffffbf7fbdfffdfff3effeffffeffbffb7dffd7ffe7befbb6fffb7edf5bb5fffdffd7ff6f9bfffedfffaeffffe7ffcfe6dff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches72 : PLift ((OMA.PrimeProgression.composite primes 13 1059944 4726) = mask72) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified72 : PLift (rows72.all (check 1059944 4726 mask72 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct72 : ∀ r ∈ rows72, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified72.down r hr
  rw [←maskMatches72.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows73 : List Witness :=
  [(1741,1232,115),
  (1553,1385,109)]

private def mask73 : ℕ := 0x3fffff67df7bf7dffb7efafbfffffb77fedfe5dbfffff6fd6dd7ffaeff7ff7defffffe5ffdb7ebbdfeddfef7f9f7bfdfe7ffffb7d7fdffdfdffcfbfdffdeffef9bfffdd7fffffffdbffbffffffcf75fbeffdfefdfefeffeeff6f7fbfffb7dfcbffb7ebbff6fdeffb7d7efbff7fdbfbfdbfffeefbfdbfffff76fbffffffcf7fdf7dfdff7feffbdfefdeeff7bfebfcffedffdfdfeefffdf7bfffe7fedf3cdfffffffffbfbbdfefd7fd7dbe6b7cdfeb7ffefdeffffdf7b7ffbfbf7fbfdf7ffffb7dfcbfeffe9fff6ffafbf7fef97dfffff7f3ddefffef6fff5ff7bf7b7fdbffeef7edfff7fdbfdfffbff7fdefff7bf7fffffff3fdffdf7bb5f7efffdfffbeb3effed7dfefbfdffeffebeef7fbbdf37deffbddffdffbfcff7fbefefffff7f96ffeeffdffdbfffe7dfef77beef76ffffbff2ffedf76de7ffffbfff7ff7d7ebffff7fbeffcdf7f7ffefbbfff5ffefffffdbe7fffdffbfdf77bfffffff7f7cfe7fffffebffbefdbddbffffbffbbffffff7f77f6ffbffff9f7f7fbf7ffffbfbbff7fbfffbedf7dfff3fdffffedfffe7bffd7fdadff79f7b7fb7fdaff77ffdfb7fffdffffddbfbb6ffffffd77bfeffcbf7bfffbf9eff7ef77f7fffdfa7fffdfedecfbfffcbf5bfed6efffbf7ffffefdffd7dffdfbff7fffffe7fadffddff9fffffbfdf37fefb3fd7fffefffd7efedfffdbfffefeef6df7ffefffff7ff3efefbfffbdf7ffbff77feffbefe6b7dfb7fbfffefeffefffddf6b7d9f7f3efeddffffdfffbefffffb7ffebff9ffd7ffbdfff97ef7ffefdfffbffefbfdd77dedbfeff6f7ffedff7bfff7fd7edfffb7f7dbeffbef7f9ffff79ffffddfffedf7effefeffffffffffbf7d3ffffdedffffee9ffdbfffcf3effffffff5fefffef7fbffd6fbfefbdfe7f6cffdfe7bf7ff7ffffa7fbdf7edfeb6edfdff7ff7ff6fedfe7ffff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches73 : PLift ((OMA.PrimeProgression.composite primes 13 1072456 5326) = mask73) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified73 : PLift (rows73.all (check 1072456 5326 mask73 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct73 : ∀ r ∈ rows73, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified73.down r hr
  rw [←maskMatches73.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows74 : List Witness :=
  [(1959,1123,136),
  (1703,1293,118),
  (1847,1193,129),
  (1637,1348,118),
  (1834,1204,126),
  (1965,1128,129),
  (1647,1346,106)]

private def mask74 : ℕ := 0x1fffadffeff6d77f6ddef9affbfbffdeffb7fbfff5fefffefefff6f7dff6fbff3fdfef3ef77ffff7fbf5f77defbffd7dffcfffff7fefffffbebfffffbefdffbaef3fffef7dff7ffdfb5fe7dfffaffefffcfefdfff77ffefbefffb3dff7fa5ff6fffffeffffffbf7ff7fbfffdffef77bffffffffffcfbcdfedfefbdffefbdbf7f6ff7fbfeb75f6effffffdadbfff6fffffffdb5fbfdfffeeffdffdbbfbfffedf7fdeeff6d7ff3ffffbfffff9effedf77ffffffb6efefdff9feb7dffefbfffdffcfffbf7ffcfffbfff75ffedffdf5fb6ff79ffbfedeffefffcffef7ffa5fbef7ff6ffeffffbfefffff7fbff6fffff74f7effdf3ffaffffffffbef2ffffffedeebbefffdb7ffffffb6cfffbf7ffcdfff3ffadff7fffdeffeffbfffebffdfedfff7ffeffb7f77ffffffffcfff9ffdfffa59f7f3fffef3fdfffbff7dfffbfef6fdf7f7eb7ffafdfdbeff7fffefffdb7ffdbfddf6fbcf7fdf7f7ff77defdf5feff7fbffdfcfefdfff3ffff97ff7f9bfbfdbefffeffffeeffff7ff7efbdfaefff977bedfffff6ff7f7ffeddefff5f7ebffdefff7feebbfbf6fbdfe7fffbf6ffefffd6dfffffffffb3fd3fbeffffffef7dfb59fff7efe6fffffdfedbbffe7feed2fff7ffff7fdbddf5faff76fef9bffbfbffff5f7edeeff5dfebffff7fefdbfffefffd77fbfdffbeff7ff7effefffbeffffd7ff3cdffffffffffebeff6ffeffffde7dffff7dfdffddffdfffe7ff5fffffffadfedbbfff7bfffbffbffa5fffff7ffefffffefbff7ffeffefdfcffffefdbffffdfdf7edfef3cf77fbdbfef6ff7effffbfffd9effbffadfffff7ff7f7edffffffbebffbfdfffbb6ffffefdfffe7ffdbffbf7bffdedffcbffff7bbffbdfafffef6ff6fd77ffebffde7f7dffdff6ffedf7bfffa7df5f7ebff9fdf7fbefffdb7edefdb79efff5bfffffff5ffdbbffffffffbfdffbfeffedffdfdfb6f7fffff7dffffefff5ffff6efbfdfffffdf69ffdbdbfffbfdfffeff7fffff7fff6bffdadfafbbfffefbdfffbf7fffd7f97ffefdbffffffff3fdedffef74bffffdfedff5ffef6fb6df37bfdbf7df6dacfb7dfdbfdff7bbdfb7fffbfff7797ff3f9f5fbef7f9bfde7bffff59fffbfd3fdafb7fd7eb6ffa7feeffedf7bfff3ffbefbfbffdafff7dfffffffefafdffdbfbf7fefd7ff7d9ffffff7fffefe7dbfbf79efdfff7fbffff4ffff6efefda7fbff6fdfff3dfbffb7b7fffdff7fefffff7fdbfdaffeef76f7fdfffedbeffffd7f9fff7ffbffffffffaffedbb6b77ffffffda7dbefbdf6fd7edf7ffcffffeefffffffedffff7ffffdfdfffb7fdf79fefffdbffffd6efbff7ddf6bfd9efbfcd7fbb7f7797ffbefefdadfbfdf7ffedfdfedffdffedaff77ff7f7fbf69bffefdefb77bf7ffdf6ddffb37defffefefff5bb7be7f7cf7dfbfbfff7ffafffdfbfffcfffbeff7ffbcfff9fed7dfffffef7fff7ffff3fffeff6bffffefeffadbbfdffffedeffffb3dff7d3ff3fffebfedfefedfff9ffffdff7f7fdfffafff7bfffbedfffefbfef77bffdbffffbbfbeed3dffdffdff5ffffeffeffbcb7dff7f6effdbfff7ef76baffeffb6fffd7fdfffbffbcff7beffffdefdfdf76ffffffd7ffbff7ef7ed7df6fff7bfff6ffeefef9b7ff49efb7ffffdffff5bfffadfbdbbff7fbefffedf5ff4fffff7fbeff7feffbfb7fdeddbffbdffedefdfffe7bffffdffffbff7ddbdf77defbeefeddffffef76f7dfbf9adfbffff97fffdfe4bffbffffedefff7ffffefdbdfaffefbf7f6ff7ffffbe5fb6fef9beff7dfcffeff7f7fffffffffdff7b3dfffff7ffcdf7beff7dbf7ff7defdffffffefbfefffffdfedfbebffd67ffffaffa7f7fffeb3eff7dfffffbefdfddbfbf7ffef7ff7ddfffffffd966ffdf7dfefbbfbfffbedffff5b7eff6ffff7fdfdbff9eed3effdbbfbbcf6fbffdf5bbff3dbe7dfffedfffffdbffbfdfeffb6ffdfefbfddb7bf7ffffffdeedffffdf3fffeffff77dbeff7fffbbc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches74 : PLift ((OMA.PrimeProgression.composite primes 14 1099979 11229) = mask74) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified74 : PLift (rows74.all (check 1099979 11229 mask74 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct74 : ∀ r ∈ rows74, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified74.down r hr
  rw [←maskMatches74.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows75 : List Witness :=
  [(1696,1321,116),
  (1796,1249,125)]

private def mask75 : ℕ := 0x77f7ffecff5feffbfd77b7ffffbbffbf9fff7dff7fe4bf7fffdfddffdbdbfff7f9fff7f9bff7effefbed6f9f6ffe9ffffcdaffffffeb7fbedfefdfffffdfffeef7fbfcff5ffed3ef6ffefbbdbffdafffffbfbfefff9feffffbdff7d7fb3fdfdfbffbdff7fecfefff7ff7fffb7dff7ffff3ff7fbffffffe5ffffeeffeff7bffb7ef6fbbfdf5fffffedf6f7df3fdfdffefeebfff7fdbeff7bff93efbddffbff9f7feffefdfef7fdffffeff7beffff9f7d7ff7fdfcffff67fefdb5dffbf6fefb3ffffbedffcfff9ffff7dffb7dbf7dbefaffb7ff7fffb7ddadbfefffffff6fdf7fbffffbfefeedf7dfcff5feffbdffddeef7fbe7d7cffd9bff77dff9efd6ffbffb5ff7fbff7dffeffed7effdfffff5fbcffedfdf7ffb5bfddffffdffffffffffffdfff7fffff3fb7fffdfef9edbbedfef3fdffdbffb7ffff2ffbdffff7edfff6dfbdfbff3dff6f7ff7ffbfbbff6ffadfffbe5ff6feffffdfdfeebfebffdfffefdbfb3dfeffffd67ff4fff9ffb2fdffda7ffef77f7dffffffffffffbfef3fffffbffeeffffff9edff6ff6dfdfbfffff7e9ff9fefbffe7f7fdfefffdfdffffbfff7bfed3fbfefffdffffefbf9fff7ff6fbedffdfffffff77f7ff6fdf4fbfff7fffdf5fefb3ffe6ffffe79ffb7fd7fffef67bf5ffdfe7ffffedbe7bff9fffefdf7bfffffdfff6df3dfe7fbdff7daddff9fffb4f7ebfffaffbff7f9ffdfef37feff7f

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches75 : PLift ((OMA.PrimeProgression.composite primes 12 1120208 4088) = mask75) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified75 : PLift (rows75.all (check 1120208 4088 mask75 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct75 : ∀ r ∈ rows75, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified75.down r hr
  rw [←maskMatches75.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows76 : List Witness :=
  [(1813,1248,127)]

private def mask76 : ℕ := 0xffdf7ffeff2dffffbeb7fff6fffff5fb6f7fbfffeed7fbffbf7bfef7dff7ffcfb7befbefdfffffffeb77f3fffffffff4feff6fff5dfdbbfff7b3cfbffbff7f97fbfdfe7bbeffffefdefdffbffbbffefd6efefdffb3eff7ffff27dfef7fdffbfdf7d9bfb37f7fdffdfffffff6dffdfcdfdff7bf6ffff6fdbffaffbeb77d7ff3dbfdffdffef3fff7dfebbffefffffafdfef3ef6fffffb7ff5f77dff9bfff7ffebfdbff97fdefbbff7edffffddffff7f3fff7f7fffffbdfb7ffffbff7ffefffdfefffff3fffdbf6ffff3ff75fedbfedeebeff7ddfdffefefd6cf6ffa7f75ffefafffdfbdfbfffeffff35beefbdbf7dfff77ffcf76feebfffefdeefbefffdffffffefbfdd7fbbff7fbf4fbefefdefd6f9feffdd7ffffdeddffffdfe6ffdf3dffdff7f66d7dfffbefbfffe7dfffeffedbbfbefffcfff9ffbfdf6f9bffffff7ffc9f7fefffffefbfcd7ef6dffffeeffff7effff7fffcfb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches76 : PLift ((OMA.PrimeProgression.composite primes 12 1131312 2720) = mask76) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified76 : PLift (rows76.all (check 1131312 2720 mask76 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct76 : ∀ r ∈ rows76, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified76.down r hr
  rw [←maskMatches76.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows77 : List Witness :=
  [(1640,1388,108),
  (1431,1592,92),
  (1782,1283,122)]

private def mask77 : ℕ := 0x3ffb7fff7bb5bfdfffffdf3fdffbfefffbfefe5ff7ffff6ebeff75fbfbb7f7ff7df7ffffff7feefeff75dafff7b7fdbefffbfdf3efffbffff5ff6ff7fffffedbddeff7f9fff6fdb7dbff7dfefb7fdfffefffdffffffdffdfdf7fb7ffaffe5dffbfedefbfef27bf5ffdfeef7ed7fbfff77fe7befdffdb6f75ffffeeffdde4ffffeef7dffffffff7ffedbffa7feeffdff7bfffffffeff7d76ffdfaf9fdf37f7ffffdefdffb7fbffffffefde7fffb77fbede7be6fff9ff9fdd77ff6bfffeefffdbfbfdffff7fbfff75feefffff7ffef7dffdfffd6fd2ed7ffb7fffbeffffd7dfefffcdffbfede7fbdf7edefffdff7bffff7d7ffeffffdffffdf779bffedfbff7eff7dfcffdbf7bf7ffff3efedbffff7ff7fbcd7fbe7bf7ff6f6dffffbef7dbffb6ff77faffb5feeffffffffcbfff6edffd2dfbdfbfffffbfff7deffb6fefbeffeffb5f7fdefbefdbffffffcbfffffffdbbfffeff6fffd3dfaffbdfffffddffdf7ffebfffaffa7fefb7f9ffb3ffffbbfbfdfffd3fff7ffdbbdbe7b7ffbdbfff7fffebfefafff5ffffe7bfed3dfadbffdf6dfcfbf9fffbff67dbdfffdfff3ef77ffffffffdb36ffeffff67dffb7ffffffffbffffff6d76f7ffb7ffffbfbffbeffffba6ffffeff7fff7de7bfdf7fffff3fffefb797ffbffbdfbffbfffffefdeddbdb7ffffd6ffbdfa6fffdf6fffdfffffffe97797df7ffefbf7ffff3ddf7dfff7cbffffddefdedffefefffff2fbffffffffdffff7fffffcfffbfdfbdfffb7dbffbfddffbfdffcfffdfefffff6ffff77feff77dfffffb7fdeffbdffffbefeebfffafdb7f7ff7ef3ffffbbcff7feffeedffff6fffbffbbffffdeefbef6ff6fffdfbfffffeeffddffbfff77bfebadff7dffb7ff7ed3dfffdf7ffdd7fffeffffbeffffffbffdff9beffff7efedfbdfedf3dd7fb7fff7ff7fbdbf7faff6fffcfb6ff7dfffb7dfffbef7ed7ffffff7ffffffbfede5bffb77fffdfff7dffebf6fffb7dfeffb4ffff77fedf7ffb5fffbfffbfdf7fe5ffff7fdeff67fbefbfdfefffffffbff7cfffbefd7ffb7fffbf7b3fffdff7ff6bfefedff7fe7ffdf7fffcff5ff7ff5beefffde7dffbffbeffafd7ffffffffeefbff2fff5ff7deeffefff9f4fb7fffffdfbfff7f7797fffefedfeffbf9efffedb7ffffffffef7ff3fff6bffbffbbffffdfeff7ffed3dfbf9effbef7fbbffff9febbf9f7b7ffed9f7fffffffbffbdbedf7cfeed6cfbfff7fff97ff7ffff9f6bbcf7fffdfe5ffeff7b6fbffffffbdfb6f7fb7eff5ff7ffdffffbdfffdffffdf7efafdf7bf7fffbe7ffefb7ffefbfffedfeffffefff5ffebafdfddbffbffffbffff7df7b7effef7fffdffff3fde7b7efbffff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches77 : PLift ((OMA.PrimeProgression.composite primes 13 1138160 7666) = mask77) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified77 : PLift (rows77.all (check 1138160 7666 mask77 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct77 : ∀ r ∈ rows77, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified77.down r hr
  rw [←maskMatches77.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows78 : List Witness :=
  [(1958,1181,126),
  (1982,1171,132)]

private def mask78 : ℕ := 0x7f6ffff7ef779bfbf7f7ff7fd67ffdff7fffbefdffff7bfe9f7baeff7fbfffcdf7feef7ffa7bfdffff3efefffff77ff79adfadffdf3efffffffeffefb7fdeffffdefbb5fb6df7ffffefdf6ffeff6f7ffffbafffdf67f7ff7ffe7ffffffdfdfeffe7fbdffefbdfbffaff77ff6fffffdfb7b7fffefeeff7ff5f7dfffbfedbfbffffdfffbfffefbfef7f9fff7ef7dfffffff6ff7dda7ffebb6fffbffff7ffcffff7fffdf77ff5ffffeedbef6fdb7ff7ffffffdfdfefbfdff7bfffbfdf5ffef6e97ddbdfffff7dfed3ff7fffeff5ffefbdf7fffffffffe9fefa7bb7f3cfffdbfd7dffdf3ffe7f7dffdff6ffedffbfdffffe6f7f9fff6dd7fff6fffff7dbfff7ff6fbeb7ffffdbfffdbfef67ffffed9ffffffffd2effdfbeffd9ffd6dfbdffffffbf7b6efbfbfdffdbfedecd37fe6fffdefffef77fefbffbf7bedfefffff7ffeef7ff3fffff7ff7ffeffeffbfbffbfffbef3fffffffbffffede7df5fbdf77ffddfffaffb7ffffaed3fff7f7cfffdfdfeddbebbfdfef7ff7dffdfbef7ffaffffffff3dff79ffdfd9efbffffebffdaffeefffdefffffb7fe6bff9ffffdff7bfffbebfffefdefdfffbefeffbffefbeffffd7fffedefdf7b7ebfff7df7ddfebffbfffafffddeffbdfeff7fdffffdff7d76feef77ff4ff4fffbbfdf5faffbef7fd7dff7ffff3dfeff7ffffbf7fbfdf7b7fffffe6fffb7ffbefaffbff3cdffd7dfbdbfeffff7effffef9e5f76ffefeffb7dbebf7fffdbff3fff5ff7f6fd7efffdf7ffffe7ffedfffeeff5f7fbeedf7fbffbff6ffecfbfbedfffdfff2df3fdeeb7fbfffbff7fffefbfff7dfdff7fefb37ffff7edffffebffbf7befffffbfbffff6ffffff9fdffe9f7deefbdff7ffdffff6dfffffeff7f7effffedfffff7d7fdfffbdfefbf7fefdffdffbf5ffddefd6df6f9fff7effef3dfed9bffbeffffeeffffbffb7feff7dfb7fedfbff7ffbfde7fedbffffedfdff5daffffffff3effffffbb7bff9edf7fbf7f7efffbfffefbf6f7fffff6efffbbfbfdf7fffffefff4bfffffdedf77dbdbffdf69fef6ffa7ffdf6ef3ff7ffb7fbd9ffdbfffddefffe977bbfdbffbdfbfbe6ffffbffffffffffffefffffefb5ff7bfff7dffefb7defffefbdffdf77dffd6ede7bbffbfbffd6ffbf9ffbfdffffafdbffe7ffcffffffffffefbb7be7d7cfffdf7f3ffefffff77fecbb69efb7ff3ffbffffffff6efffbf7bff9ffdfffbffbff77ffffeffaffbefbdbf79fddf7fffffddf7fffd3fffeb7df7fffddf5fbfff7fffbfdfffff7ffffffb6f

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches78 : PLift ((OMA.PrimeProgression.composite primes 13 1156199 7235) = mask78) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified78 : PLift (rows78.all (check 1156199 7235 mask78 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct78 : ∀ r ∈ rows78, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified78.down r hr
  rw [←maskMatches78.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows79 : List Witness :=
  [(1861,1253,131)]

private def mask79 : ℕ := 0x7fddffbbfbff9befffbffff6d7ff6ffed9fffbffe7b6ffafdfff75ff7fefdefbb7f7f9febfdff7fbefffbfffeffffbffffdbffdffd75fffbbfff7b3dfb5bfdbf7dffb7fdff9ffb7fbeffeff3fdf7ffdf7fbbddfffbdfbeb6fdfff3fffdff5fefdbff6fffdbfdff7fffdf7dfcfbedf79fffb7bf7f7cffebffff7ffff76ffff7df2fffff7fb7ffffda7be6ffebfff6edfdbf7fbfb7fdfff7fdfff74ffefbdff7fbff7fbfef7cf3fbbfffffefbfffeffbffffbffdeefffdbffffbffbfdfa7bf5f7ff77dedff7fa6ffdbfffeeffffefbfef6fdfdfbdfaff37fffd3efbfdfdbf4f7fbfed75bbfbbffefbefd7ffb6bffdf7f7efffdfcfffd7ed6effffffbbdd7ffeff67ff5ffffff9bffadfedb7eff7bfefa7deff7ff7fdeff7fbf4fffbfffbff7f9f7ffebfffffff7bb6fbe9eeffffbdfffbffd76f2dfafffffbeffe9addfffedb77bf7ffef75feffffdfff7ef6ffbffffdf7fefdfdfffffdf77ffefbf9efff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches79 : PLift ((OMA.PrimeProgression.composite primes 12 1165917 2791) = mask79) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified79 : PLift (rows79.all (check 1165917 2791 mask79 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct79 : ∀ r ∈ rows79, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified79.down r hr
  rw [←maskMatches79.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows80 : List Witness :=
  [(1797,1306,124)]

private def mask80 : ℕ := 0xdffb7ebffbbfdfd9eeff6dfeb7dfe5fbeffdff6ffdffffb6fffb7fdedfeffeef3cbeffffdffffdf7ff7e9fefffffdfb4dffdffff7fffffffffd2effdfbff7fbffffffb7ffefbcf7fffcfffffdbf5ffff7ef7fbfffffbeededfb5fffff7deef7dfedfb7bbff7ff3fd7f9bfbbddf7feffeffb7f7dff7bfefffdecf7ebe7bfeff5fe6bf7dffdfffefbedf7cf7efbdff7ffdfbef7fd7ff7f9ffffdfeebfedffffebbddffbffdedffffffff7fedffffe7fffffff7efffffebf7b76d6dfffbfcff7ff7ffdfe7fbffffd6fbbfff7bbff3efffbeffff9b6fffdeff7fd3fbefffe9f7f6ddfffffffefffdfcd7ffefffff6fd3efb7dfffffbeffefff7fadffff6f97dfbddeff7fffebfff67ffdffffef9bdffddfeffebfefbeff5bbfffdd7fbffdb7bbdfffbfffeffffbf5b3dffefbfdbfffcb3edf7ffef77fe7ff7f7ed3fd7ddf7f7fbeff3df7ffffffebf6fbfff5ff5fbffeff7ffb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches80 : PLift ((OMA.PrimeProgression.composite primes 12 1173441 2696) = mask80) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified80 : PLift (rows80.all (check 1173441 2696 mask80 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct80 : ∀ r ∈ rows80, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified80.down r hr
  rw [←maskMatches80.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows81 : List Witness :=
  [(1975,1215,133)]

private def mask81 : ℕ := 0x3efbfdf7fffdfe5ffffb6ff7f7cfbfbf7ffddeebffd6fffeffcdfffefd7f9bfffedfef3fffdffcffefef9fefbffadbfdb6fdafdeffffbbdffefbfdffffffff9f7ffffefbeffffd6fbefffddfdff7fe7fffdbfdfefffff7baefffbedfbcffed7ff7fff6fbfdeff3ff27feffffff7fffdffffffffd6797efffdefff4dfff2fff5dffbfdbefffedafdb6f7ebffbbdfb5fbfffdfe7fffd77ffebbffeedfddbfdedbbfffffbffb7dffffef779fefff9fdf76feffefffdfbefb7fefdfedbfdf7ffdd7ebedff7bfff7f9f7f7fd7dff4fff9f7f7ff67ff5f7fffffefd3fffdfbeff7fbff3ffefffff6ffbfffffffbfffffffdfbffbfff4fffbfdfeffaef7cd7fd7df7ffb7bffbf7f7dfbffefffebffbfddfdfeebffdf7bfffbdbbfffffffdbedffdfeffdff7deffefdbef77f7ff7edbfffffbdbfffedffffbdffdf6fdbfff7bfff75ffffffdbffffbf6ff6fbffefbedfffdffdaff65fbfffcff7fefdfdbeff77b7ffbedf7bf7ffdfffffdf3fbfffb7fffd3efbfbfdb74

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches81 : PLift ((OMA.PrimeProgression.composite primes 12 1199813 2962) = mask81) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified81 : PLift (rows81.all (check 1199813 2962 mask81 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct81 : ∀ r ∈ rows81, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified81.down r hr
  rw [←maskMatches81.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows82 : List Witness :=
  [(1995,1212,137)]

private def mask82 : ℕ := 0x1eeff7fbfb7fdefd3efbffb7f7fdffbfeff7ff7fffbef97ff7fbffbbfff6ffef27ffdffdbf7ffffffffffbeb77bfdffffe7b7efffdfffff9fcffcfffbeef7fff7ffebfffeeff5fbeffcfefdfdd37ffebf7f6fffff7f9f5f77bf79efdf5dfcf7fdffbfdffdffffbff6ff2edfdbfdf3ffffffdf6dfbfffeb7ffeeff7dfdf7cf6efffffdbfcbffdefdffdafff7fffbf7bbfffffafbffb6edfdff7fa7f35fefd7edffff5fbddfff2ffedfefff7ffff7efbfdefffebeed7dffffaefbdfeffaffbfdf5fbdf7edbff7dfffff7f679ffffffbff3ffff9eeff7dffffddf7fffdbfdffb7fff6fbeff5deef7effeffff7dfffff79ffffddf7fffbbfb67ffff7fdbfff797fffff779b7b7ffeef2efefdffffdfe7f2ed7fbbfff7f7ebffdfffbeffff77f7fdf7ffffffbf7deefffff6ffdfffdffdf7fadbffbf6dffffdfbdffff7ef7fd77dfeffddefbfffafbfebf49f7ffffeffffffeb6ff6cfffffdbfdfefdbef6fde5fbdffeffffbffffff7feefbffbffefff4d7ffefffd9fcb7fde

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches82 : PLift ((OMA.PrimeProgression.composite primes 12 1208970 2993) = mask82) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified82 : PLift (rows82.all (check 1208970 2993 mask82 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct82 : ∀ r ∈ rows82, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified82.down r hr
  rw [←maskMatches82.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows83 : List Witness :=
  [(1987,1222,130)]

private def mask83 : ℕ := 0x17be7dbfdf7fefbf7fefdfdf7fdfdff5f7efffdefffdb77ff7bfef7fbfffffff7f7ffe7fbcffedeef7dff7ffefbfdfed6fdffbfcbfff7efffff7fefbf7bf7dfcfbdffff3ef7ffffd6fdffffdfefffff7fbfffffb7fbbfdf79e7fffdf7defff5fb5fffdfefbfdbfdffffefeedbfff7ffdfbeb6f9feffffeffbef7fb7fdfddfff7ffffbeffbfff7bfdfffbfffe5bbeffeffedfef7dbfeff7d7ff7ffffde5fffbfebbdf7fdfdf37f77f7ffbffbdb7fdeebffff7fb6b7ddfffbefbfff7fff9f7ffffadbefffeff7f7fffdbfefbdf6ffefde7dfcf7ffeefbffffffeb7edf6dbefeffbfbfdf6ffefffdffffbfbeff7ed7fff6ffeb7ffffdefdefffffe7f7dfbfffcbffbeff7dfeffedffffeffbff7fffcbfffe6dffff7bfdff6f7f9fefffbffbbdbf7ffeffdffeff7dfeffddffbedfbcf7fb7fffffb7ff7bffdeffefbe7b75bff9bffffffefbfd66bfeffffffffedeff7fd7fbbfbfede7feffffff7fffdf7ffffbfff4f7ef7effef7dfffff7beffeef67ffdbfdfe69fffed

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches83 : PLift ((OMA.PrimeProgression.composite primes 12 1214057 2981) = mask83) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified83 : PLift (rows83.all (check 1214057 2981 mask83 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct83 : ∀ r ∈ rows83, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified83.down r hr
  rw [←maskMatches83.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows84 : List Witness :=
  [(1677,1476,112)]

private def mask84 : ℕ := 0xbf5ffff7f9beff7bffffdfffd3edaffffff7d7ff7fffdfbcffdfff9ffff7bf6fbfdfedeffe7de4bfff77fffdbdfaeff7b7e97ffaffeffbff6ffbfffddf7ff6dfffadf7ffeff7fdffbefffffeffbfd76fefffffbfbffff7feffffffffb7bfffbfdf5fadf7ebeef7dff7fe7ffef7f92ffffdbffbffffd7ffedbe7b77ffeffcfbf9fef7ff7effffffffebf7f7ffbedb7ff5ffef76bfdf7fffdf7efefdfdfbfff5fbdfefbbff7d9fdf3dffffbffffbfffffdffffffe5ffeffeff69ecfbfbfdfbfdf6ffffa79f6f3ff7ffbddf7fefffff7fdfffbdbb7fffd7fffff77ff7fff9f7f6dd7fbb7f7ffffbafdfdbf6fffdffbfeff7ffcfff9efd7dfafbf5b77bffffff7ffeeff7fefbbffff9bfbf4ffebfeff79ffffedffd7ff3fdf6ffcd76ffdfffbeffbdbfedffffffb7ffff7fffefaffffffcb7ffefdf5ffff7fff79feff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches84 : PLift ((OMA.PrimeProgression.composite primes 12 1237626 2516) = mask84) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified84 : PLift (rows84.all (check 1237626 2516 mask84 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct84 : ∀ r ∈ rows84, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified84.down r hr
  rw [←maskMatches84.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows85 : List Witness :=
  [(1985,1257,134)]

private def mask85 : ℕ := 0xffdbfffffffebffd75ff5fbffe7bfffafbffbff9f7b6ddbfdfffbdfef9fdff7bfffbfbf6ffffffffff3ff7effffedfeefffd7ff7ffffffdffefeebbfffddf7b7efe7feff7ddbfbf49febefff7fadfffdfef7cfffbffbffff7fadfe7bedfbdf7ffbfff5dfffffb76bfdfefdbdffff7ffbffffdf5bfffffd7ef6f9a7f7fbfeffcdf7fbfffddefdfeff7ffdffffefffef77fffbb7f6efedf7ffedf7fffeb7fffffefb7fffffffd7ffbdbb7df7beedeffefff7fffbbedbffadfffb6efeffbfbfffffd77fbffbfbecbffb7f9aff7fffef7ffefd3efafff7ff6dffd3ff6fbfefffdfff3ef7dff7bff9ffffdfb5df5f7ddf7ffefffff4bf7f76ffff7fdf7ffeffebfddaffedffff7f9befbfdffffcffebfeffdfb7b7efefdeffefdffbfef7ff7dff5fbcffdfffdfdd77faefffffed7fdf79f4ffefefbbfdfffeffffb7e97dff7bffbf7dfefefffffffb7ddefb7edafdfebfdffeffffffff7fffdffbfffbdbbdbfddf7f7cfefdf7ffeffffbdfe7feefbfbf7bfffefff5bfd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches85 : PLift ((OMA.PrimeProgression.composite primes 12 1247573 2977) = mask85) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified85 : PLift (rows85.all (check 1247573 2977 mask85 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct85 : ∀ r ∈ rows85, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified85.down r hr
  rw [←maskMatches85.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows86 : List Witness :=
  [(1761,1425,122)]

private def mask86 : ℕ := 0x1f7fbfdfbfffffbedfeffdf3fdfdffcfef96fff7df7fffdeff7efbddb7b7cd7efffdedbeffbfde7f7edfdfedffffffffdffffedb7ffffbeff67ffff7eff6ffef7dfa5ffff7ff3effd9ffbbebffd7dfefffffffffef2fdbf9fdf7fff7ffff7dfefff7beef6ff2fff6bb5fefbfffbffbffbff7fffffa5bfdf7dfefbeefe7dfeff7df79ffffdffff77f7ff2dfffdadffdb76bfff7ffaefffb7effff7fde7bfff6fffffbddfdbffbfff7cfb5fafff7dffdbfff7bfeffebe7b3efffdfff7db7fffefedffff7fdf7dedff5fadff7feff7fdbfdffffdb7ebefdffdedb7ffffffff379b5ffcdfeffff6fdf6f7ffeffedfbfdbeff6ffeffffe7df6fff9eefedff7ffdfffbf7fbcfbf9f4ff6befdfff3ddfff7ffffffdf7fdbdfbfffffeefffffefbddfffaefadffeb7fb7ff7dfe7ff5ffefefffdf77bbebfff7fdffff7fffbbfff7feddfdffef7fd6f97efeffffff6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches86 : PLift ((OMA.PrimeProgression.composite primes 12 1254713 2641) = mask86) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified86 : PLift (rows86.all (check 1254713 2641 mask86 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct86 : ∀ r ∈ rows86, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified86.down r hr
  rw [←maskMatches86.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows87 : List Witness :=
  [(1817,1394,118),
  (1706,1485,112)]

private def mask87 : ℕ := 0x379edfbefe6fedfb5ff7fb7f6ed6cdf7ffff7fffeffff7dfeebf796fbfcfffbf7fbefffbfffefbf7f7dfefdfffefdefffddf7ffdff5dbdffefffb7dfffbb7bff9fffecffffeffffffefedf6ffbfbfffffdfefffbfffbedfff3ffe7fffbf7dffbbfffffbff7cbfff7ffedfecf3dfeef7fdbfff6fb7b7efbffeffe7f3dfffdfffedfffbffbfef7cfe7fbfffcffff6ff67ff7f7ddffb6fdeffefbfef7ffbedfffb7fbff7f9fdfb7fffffdbfefedfefbfffbffeffbfff7fffffffeff7dfbffffbb5d7edffdffdfdbf7fefbefdefbbfff7bffbeefe7ffff7c977feeff7fe7bf7fefd2dfffffff3ebfeffdfffdbdbfefeff7ff77befb7edfef7ffe7bffbff9effbef6dbaff7fffffbffbdfb7ffcdfedffffdfaeff7beffbdfffdf5b3dff7ffffaffafff7ffffffffddfdb7fffff6fdf7dfef76feffeffffff7ffdffffeeffffffffdf7fd7edbfffeff59efd7dfffbf6fbdf76ffffbfffff7fff7b3ef3f9ffffffefb7e

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches87 : PLift ((OMA.PrimeProgression.composite primes 12 1266449 2815) = mask87) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified87 : PLift (rows87.all (check 1266449 2815 mask87 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct87 : ∀ r ∈ rows87, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified87.down r hr
  rw [←maskMatches87.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows88 : List Witness :=
  [(1916,1335,133)]

private def mask88 : ℕ := 0x3bfffffbdff7f7ebfffefbbfbbff6f9efdf7ff5f7ffeffeefbddbefff977feeffddfdfffffe97fd3fff4ffff7ffbffffbf7fb7fffffdfbfdbff3ff6ffbef67befffcdfefefdffff5f7f9eff7edfffe7bf6fffbeffe7dbfffddffd7fdfffffbfffffffcdf7ff6fb5bff9bff7ffbdbffbeedffff79adb37ffff3ff67fb7fffbffffcffdbbff7ffffffddf7be7ffffefd7fff7fe4ffd97ffbdf7fdffbbfff6bfddf7ffcbfebf6dfff3dffff7fdff9efdfffbdffdfe7fbffbffeef7cffff3fdfffedffeff7dfdfbffb7bfdff6dadd7fffdbfdbffdffd67ffff3ef77d7ff6dfffbbddefffedffdffbffbeffffdbfde7f7ef7ebfdff5bfdf7efffffdf35fb6fffbeff6ffafbfebbcfefbefd7fffefffbff97eff5fedfffdeeffeff7bfeff4dfff3ffefffffff9ffbeefffdfefbeffeffdd7ffb7bbdfeff7dfffdfffbdfefffffe5fedfbf9ffffef77fffbfffeef2fffdffff35bf7f6efeffffb7fffefafffdfeef3dfffd6ffb7feebbdfe

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches88 : PLift ((OMA.PrimeProgression.composite primes 12 1278930 2874) = mask88) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified88 : PLift (rows88.all (check 1278930 2874 mask88 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct88 : ∀ r ∈ rows88, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified88.down r hr
  rw [←maskMatches88.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows89 : List Witness :=
  [(1895,1355,130)]

private def mask89 : ℕ := 0x3fdeffe5fbfffff6fff7bf6ffdfffffdf6ffffb3ffee9effeffbdf7fff79fffffff7fbfffffbef75dffb7ffff97cfaf9fff76ff7ffffffda5ffcbf7fffdf5fe5fb7bfffeffbfdefb7fb6ffbffefffdfb69f6b3cffdfbdbbfdffbffd7dffeff7feffbffafdffff7f7ff3ddedffeffdfffbfeff7fb4fffff7dffdf79ffb7dffffffffddfdbfed77ffffffdb7f7ffffbfedffffcbbffefdadf7fdf6f77dfefbffff9feffddfef7df7fff5fb7b6edbefbf9eeff7bff9fff3fffebbfd67bfdf3f9bfff6f6fffffffbfdf3e9f7dffffdfeffffbf7fefffdbfffbddfe9effffbfffffdfedfef7ffecf3ff7ffbdfbfdffffefffdbff6fdfdfffd7fbbefe7ffdfffdfffadf7dfefbf7ffff7dff7ff7ffff76f7effffffbf7b7efffdf7bfcf7ffe7fffdadffdffff7fbfefe5dfdfb7dfebfffffdb7f7fbf79fdd7dffebf6bf7f7dfffbbffbffeeb7edffff6bfdffffbcff7beff7ffe6fbdfbdfbff77bfffbefffdffb3ddfebeed7fd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches89 : PLift ((OMA.PrimeProgression.composite primes 12 1283863 2842) = mask89) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified89 : PLift (rows89.all (check 1283863 2842 mask89 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct89 : ∀ r ∈ rows89, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified89.down r hr
  rw [←maskMatches89.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows90 : List Witness :=
  [(1988,1302,131),
  (1468,1764,96),
  (1790,1450,120),
  (1911,1359,127)]

private def mask90 : ℕ := 0x3dfffbfdf7ebe6ffffbfffdbff9fffbfff5fffbf7d6fbeff7fff7f3e9f7dfdd6dbffffefffbeedffffef7ef6efefdfffe7bfdffff7dfefdfffbeb77dafffdfbcbffffeffff77bffffef6ff7edffdfdbbffe7f7df3ffbfff6f7fbedff79feffdbf7ffffbfff7fb7f7fffcdffffefb7ffffefdb5ffff77f7fdfffbfbedff7feffffffdff6ffffffdffd6fbe6fffdf7b7edfdbbfffef7ed7fffdbe7bbfd7fdfdf77fefffefeffeff6ffefffedfeffdf77bbffffdffdfeff5df5fbdbffd6fffd9fefffbf6bbffe5faff7ebf7b7fffdbeffffdffdffdbfffffbff6ffeffefffdb7eff69fffefbffb3df7efffd7ffbffb7dfffbef6ddffffcf7fbfdfffdf7f7e9efdeef7ffbffffbe6fedfefffcf37ffffffd7fffdbfff7fdbffb7ffdffdf7ffeff779fdb7ebe7bfdfffffffffffffaddefdfff3cfff9efffffefffdbeff7edefbf6fb7fef9fddf7fffffebf6f7effdbbfffff6ffeff7ddbdff4ff7f7ffafff7f7ffffffffafdbcffcf6fbfdff7faffb7b7ffeede7fefbfdff6ffffffdefbfff6793ff3f9bdfbcffeffffef9f6ffdfe7fffffddf6f7dbfff7ffbfff6fbfbfffffdf5fa5fffdffd6ffffbfeffdfefdeff7fdbff7fdfffbffedfbfff6dfffffdfdfbcf3fbefb7fd7fffebffd76ffdfefbfeffeffebedd77ff5bfff7fffffefff7bbdfffdeff7fdefb36fff93df25dfdfbffeebbfff7bf5fbeff7dbfd7dbeeb7ffffffcffffa7fbd9fff7ff7ffbdbffbf7fbfff7ff6ff7ffffefdbddafffff6ef7dfffdbfbf6fffd6fde7ffebfdbf7dedfffdbefffffefeefa7fefffe9efffdffdbe7ffffeff7efb7fffbffbf7fbfd37dfcffefffbbffb7de7ff7dfff7ff7dbfebfddf7dfdf7ffffff7fffffefef9fffbf97fbffff7bacfffdf7fedfaffe7f7fffe9bfffddfcffff7fdfffffdafff7fefffeff7ff7bb5befbbef6fff7fffbf7f7effdfbdffffffdfcfffffebfddfffedd7f9f7f74b7f9edfb7ffcfbfffff7effddfff7dfeefffff7bb6ffdfefbffdfffbffffffeb3fdeffaffbff7ef7df7ffbfffdbefd7ffbfdffff6fefbfdda7fffbbfdffffcffffedbffdffffefeffffbb7fffdefffdbbfff6ff6bedfbdbaefbffffffff77fefff7ffff6efbfde7bfef77ffdf67fbff7fdffffdfeffb5ffdffffeef67dfffbeffff3ff3fdeeff5d77fefda7fbfffff76bffdfdff7bffff7d3ff6ffeefbff769efd6fffeff7d6edbfff7fb7fbfd7ff7efffffdffcbffbffffd9effffd7efffdf7beef3ffffbfdff7ff7ff7f7efbffafbfeffdfefff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches90 : PLift ((OMA.PrimeProgression.composite primes 13 1294188 7203) = mask90) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified90 : PLift (rows90.all (check 1294188 7203 mask90 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct90 : ∀ r ∈ rows90, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified90.down r hr
  rw [←maskMatches90.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows91 : List Witness :=
  [(1968,1341,136),
  (1762,1498,122),
  (1654,1600,112),
  (1125,2355,78),
  (1635,1623,117)]

private def mask91 : ℕ := 0x76ffff6cfbfffff7cbeebffdffbe7ff5d7ffbed6ffffffffffdbff3ddefff7bf7fffff5dfff7ff7fdbfdffffeffddeffbdfffff7f7edfffeeff7facfffb7efffdbfbfffbff66fbdfef9e7fbfbf7fefdf7ffcb3fbf7f7ef77bffb3df7fd7fde5ffefbffe7bfedbdbb7f7fb7ff7ffbffe6ffdfeef7ef7dffefffffedfefff9ffffebefdeff75fbcf7efe7bfefe7bfdfbfd7fb7edffbffbfddf7fedfeffafffebffb2eff7deefffbefdefd3fbbeffff7ffbdfffbfdff7f7ffeddffdffbfffe7b3ef37fe5bffdefd7ffeffffffddeffaef7ffb7f7df7efffff7ba7ffeff7bffdbffffbbfbe7feefe7ffcff5f76ffff77fbfb7f97ffbefefbffbf5fffd2effdff7ffffef97df7ffffbf6dfef7ffbfbafffffefb7fdb5ffdffdfffdbdf77de7b7fffedefdedffefff9efbfffefbb5ffcf6fffffef9bef77dffb6ffbfdeeffdffebbffffffdf7eb77fffff7fefbfdffedfffffffef3efefdfdfefdffbf7feef3fff7ffdffff6fdffff7dffbf6ff7bfffbdfffff7f77ffefafffff7ff76fffd3fbe6fbd97fffffefbfffbfffefefdffdfeb3fdfef3ffffff5b3fd7fbfff6dffff7dbffdfffbf9f7f76ffff3efaddf5fbfdf7beddffbeffbfffef2cdf7ff5bfdbffdeff7fdaffff9eeffff3ffffb3fffffeff77ffdff5be7fefffdbeeff79fffeffeffbffbff7797ffb7fffffdfffd7ff7f9fdbfcb77faffbffbfff7ffebfef7d9efbfefeffbffffdf7b3fdfff7edbfff7fff9fefaffedfa7fbdf7fffcdfffb7bb7dfffbdf7fbeffffb7fbfff3fffffff9fedfffa5befff4f6efffff7bfdb7fdffffed7ddbefffffefefdaffbfffcfffbfddbdffffffdeffffd6ffffb36ff7fbfffdfbeffffefffdfaddbfbbffffb7ffefff5bfe9ff9bff7ffefffdffff6edf7ffdfffd76d6effdfb7fb7f6ffeddff9fcffef7ebbff6dfeff77ff7ffcfefff7ffef7efbed77fffbbfbefffedfdff7ffe9f7bedfffdfef7dfffbfffb7fb4fb7de7f7ff7fdfdfffffedffd3ffbff7efe7d7ef75fadf37f7ffefdffbb6ffffeffffdaffaffffbfffffff7daeffdbf7f7dff7fbfbffbfef7fdfffefffffeeffffffffffbff7edfdfffdf7fffffe9fef77ffefb59efdedfffbb7b7d977fbedf5fefffcfffb7fdb7bfeff7d77fffdbfbe6f37f67dfff3ffbff3ebf6ffdf7fbeff7efffd6ff6f9bff3fdfffbcfff9f7ff6dffffdfffbffffff66d7dd7ffa7ff7ff7ffeff7fe7fbff7fbeffbddbffffbefdfdfedfeffffdffbfed7dbffbfdfffffffbfbf7ffdffff2dfa79f6fff9fed7fd7fff5fbffefd7ffafdeff7fbfefbfff7dffbf6bfebfdfa79f7fbff7ef3ef7dffdffedf7faff7dfffbf7ffeb3dffdffdffff67dfefffbfefff9f7deff6f9ffbfdbfedfdffffafffedf7b7ff7fbffb3edffffffeddbffffff7fbedfdfeeff6ffefffdeffefffffffb7ef37fadfffd7ffeff77ffcffdbff9affb7fffbf7fe7ffffefffffbdf6f9bef7fffef3fde7feff7ddffffff7fb6efa7fffffed7697df3fbb7fbddfef3dff7fe5b7effefffd3ffffbfeffedfffe7ff5fbdffff3ff75fbfbffbf7dbff3dbaef76bfff3ffffdf6fbdfee9fedffffdfffffffadff7ff7f36ffffffffffefbf7d6f97ffbfdeff7fdffdeffffbf5ffcffffffffddfeff6bf7ffcfef9f6f7fd6eb7fffdfeefbfbe7fffdf79fffbfff6ffffbdfeeffffeebbcfbfff7f7df6ebfffefdbdff7dffffdf7ffb6ff4dffbffff5fb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches91 : PLift ((OMA.PrimeProgression.composite primes 14 1319544 9711) = mask91) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified91 : PLift (rows91.all (check 1319544 9711 mask91 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct91 : ∀ r ∈ rows91, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified91.down r hr
  rw [←maskMatches91.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows92 : List Witness :=
  [(1946,1375,133),
  (1887,1418,128),
  (1452,1846,98)]

private def mask92 : ℕ := 0x6fffeb7fffebbdfffbefbfffeffaff7fff6bfdfefffdf7fbffbf7fffb6fdfdff5fbebff9fdff7fffff79f6d7dfe7fefb7ffffffffedffff7fff6ffef25bf5ffef7fdfef75dfff75fe7fedfedde6ffdf7effffefff7f7f9ffbfcfffffffbfffedbdff7deebb7ffe9ffde7dffff6bfeffdf3dfffffefffb7ff7ffbdff6fefbbffffdefff5ffefffffddfef3ef76dffffdfffffff6fd7efbfbedb3ffe7feffb5ffffffdfefbffe7fefb7fd7ff3fd7fdfeffcfffd7cdeddbfbfebffffffffdedfff9fefffffdbfffb7d7ff7dfbfff5bf6bfedfff37fffbffdffd7ffbfdffff6d6efefff7ff7fffff7bfefbddeeffcdfeffffbdbe7ffff6eb6dfffbbdfffdf7d7dff7ffefbcf7efafdf7fefff7deffbffb7dedffef7ffffdfdfb7f7fdefffffffffff76bf6faeffffeeffdbffb6ed7fffffbff67fedfffbffff7bf7dbff7dffdbf69ff97ffbffedf77fef93ffe7dfdbfe9f7bbff7dbffb7db77f7cdffbeefffbfebfeff7bf5fffd6ffffdefffff7fff6fefdfffeeffeff7ffff2ddeffbfdfffbff6fff6bfffe7bfeffdffeffed7fffefa7fafffd9efffffffbffbbdfffd6fd37beef7fffffedffddffff6bffdfffe7ffff7ef7f9ffdefdf7bf7ff7f7ddfffafbfeff6f7efffbbdffffeffeffffffdff5ff6ffefff9f5bfffffdfdfaffecff6dff97ff7dfffffff7fffedfffb6bf6ffffeffafbfffffdfefacfffdadfffb7ffffd75fbfbbdbfff3ffbfbfdfbcbfefafdaddfdb7fff7ffcff5fffbffdeebeffffff7bf5fefffdd6fff7ffe9f7ffefadfecf7effff7ed

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches92 : PLift ((OMA.PrimeProgression.composite primes 13 1337875 4499) = mask92) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified92 : PLift (rows92.all (check 1337875 4499 mask92 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct92 : ∀ r ∈ rows92, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified92.down r hr
  rw [←maskMatches92.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows93 : List Witness :=
  [(1716,1570,117)]

private def mask93 : ℕ := 0x3ffffffffff7dffb7eff7bb7fffdfffeefffdf7f7fbeffffffdfb6ffdf77bedfefdf6ffed67dfcffffe7ff79fffbffbfdfef77beffffffdfffbffdeff7ff2fbbff3edfed3ff7fffffb4ff7f7effdbeeb769feffdfe7ff7fbfbfff7edbffe5bf7b77faefffbffbffff7dbdfedfafb7fdf7ffdf3fdbfbbdffffffffdbfefbffe7bfef6fdbff7ebfebfffef9bdffff7fbeff7ffe4fbfffefbddfffffffdfffffdfbfdffbb7b6efbefefbedffff6efbfdf7dfffbfbf7fefdfffeff75ff6fefffffedfbfd7ffedfbdfb7fb79fffbcd3fbfefb7bffbffdf5fffb7fbfe9ffff7fbff74ffffbfdffdf6bffbfffffdfddbff7eb7fffcff7ffff7edfeffdf7dfefbbfdfff2fff79f7fffffeffdfb7ffdffebfffffff5dbfb37d7ebffdfdfffff5bf7ffcfbdbf6f77f7ffeefffbbff7dbefbeffffbb6fb7ff7f7fdff9f6fffbf7fafd77faebfffe

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches93 : PLift ((OMA.PrimeProgression.composite primes 12 1347060 2574) = mask93) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified93 : PLift (rows93.all (check 1347060 2574 mask93 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct93 : ∀ r ∈ rows93, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified93.down r hr
  rw [←maskMatches93.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows94 : List Witness :=
  [(1922,1416,124),
  (1799,1513,116)]

private def mask94 : ℕ := 0x679fffffbf7f7ef7dfbffb7fe6defdbfdffbfff7fbbff7fdfdbffd76ffff379effffdfff3fdffbf5ffeffffefffffeeffffffbfddefbbefffd6f9ffdffff7ff5f6ff7efb7beeff5ffebffffdfaeffedfef7ffbfffdffdf7ffefff7ff6bb4ffff3efffffff7d9ffbfedffbfffffdeef6ef3fbfffff9f6fffffffe6bf6fffffff75dffb7fff7dbffafff7fffffffefffdffcfbdff7beeffffffbfdfffbffdffdbffbdf67f6ffffbbffbfff7d7fdf7fefff5fe7fffffdffefb6f7fffefffdfdfb6dffb6efefbfff7ffe7bfff7dbb7f7fbffbfeff5fbdf3ff67f7ff3dfbfbbdde7fedf3fbf7ffffefdfff7fdecf37feff7ffefff7b7ffeedffde79bdbffbffffed7fbf7bf7f76f7ffedffffbef6efffd7dfedbb5df6ffdd3fbfdf7ffe7bffff7feffffdfffbff7fdfff7ffeedbfffdfffb3eff7deff7dff6f7efffbfffeffeef7df7fbffdfdfffbfff7fd3fdefbf6ffffffdfffefdffb37fefdbdf6ffb7ffff6ffbfff7fffffdffffeffa

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches94 : PLift ((OMA.PrimeProgression.composite primes 12 1360776 2883) = mask94) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified94 : PLift (rows94.all (check 1360776 2883 mask94 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct94 : ∀ r ∈ rows94, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified94.down r hr
  rw [←maskMatches94.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows95 : List Witness :=
  [(1852,1500,122)]

private def mask95 : ℕ := 0x3bef7ef6ffbfff7ff5dfffedfefffcb7ffefdffdfddbff7fb7effffb5fffffff6ffaef67bbfffcfeff7ffbf9f6ffffffb7dfbfff5fbf9ffdfedf7fbebfff7ffffdffbeffbfffffbdfb7ffefbedf7ffdf7ffffffedeed7fd7ddf5f7cfefb3efffdeef77ff7beefefbf7fffbfffefdbfffffb7dffd7fdbffffbbefffbeffffffeff6d7fb7dfeffffbfcfff97efedbbff7fffffbcd6ffefff5bffbfefed9fffbcf6effdff7fbdfbfd7effffb7ffebfcbeeffff7ffbdf7ff6ff3ff3ffffffff6fdbfffdffdffdbf7ffefafdefff7ffefffdeffe5ffcfeebfdd7fbfdbffb77fffff7bfefb5fffffffafdfffffd7ed3cffdbf7bf7fffb6ffe7fbdbffdeffafffdba7ff7ffff6dfffffdf7ff7ff7efbfbb7bbffeeffddf7fefffefffbbfff7fbefbff7fffffa5bffbf7dfe97ff6fdffffdffffeefeffe7ffdffff7fffddb6ffffefdfff7fbfeff7ffef3edffdffbf6feedffdbffbff77def9fdf6dfefff5df

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches95 : PLift ((OMA.PrimeProgression.composite primes 12 1389000 2778) = mask95) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified95 : PLift (rows95.all (check 1389000 2778 mask95 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct95 : ∀ r ∈ rows95, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified95.down r hr
  rw [←maskMatches95.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows96 : List Witness :=
  [(1600,1751,113)]

private def mask96 : ℕ := 0xfd9a6f7fbffffddbdbe7f7fdefdfefbfffcfbfb7effeff7bf7fbfb7fbffdf7dfffffdffdfeff7fbdbffffeb7edffdbdb7dfefdefffffaff7ef7ffafdffffdfbfd7efffff7fffff5d7edffdefbe4bfeffedfdff7ffcf7ffeeffff6f9f7bfdd7ffbfd67ff7fffff7bfcfbfdbffffff7fefff7fa7fffde7befff7fefbffd7ff6ffffff5f3dbfefedf3dfedfbfdffd3efb7ffdfbcdef97fff7ff7ffcfffb7dfafff7bfcbf7f2dff7bf7ffdb76d7cf3fff7ffd9eff7ff77fffbfffeefbfd7ffefbfed7ff7dfffdbfffffeed7ffffdfcfb7def9affbfdfeb75b77bfcdf5bbef7cb7fffffbfffffb7fffdfffefdfcff7fe6fbdff7ffff7ef77ffdfffff5ff6fffdaffe7bffbfefffffdf6fdefff7dffbecdbffbffbe9fffedfffbf6bffdfff6ffefdfcfb7f7ffaffedfbeffffeffbdf

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches96 : PLift ((OMA.PrimeProgression.composite primes 12 1400800 2400) = mask96) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified96 : PLift (rows96.all (check 1400800 2400 mask96 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct96 : ∀ r ∈ rows96, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified96.down r hr
  rw [←maskMatches96.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows97 : List Witness :=
  [(1156,2466,77)]

private def mask97 : ℕ := 0x3bfff7ffddfed7fdbfbfdfbdbfffefde7ffcf3fbfeffdff5dfeb7efff9befaf9f7fffdeffefffdfbffb7befffddfdfbff7f9fffefffdffffbff6efeffbdff7bffdeefbfd7fff7ffebe7dafdffdffbffb76ffefefda7bfddffd7fff7dffb3ffffffef7dbeffffff7f3fff5feffbffef9fdff7ff7fb7fefffeffffffb3ff77bfffbfdfebff9efdffff7fbff35fefbfff6dbb6fbebf79effffbf7fffffffbfdefbbcfffdeff7fdffffefbfd6ff3fd37ffef7ef7efffffdfaff7ffffdfcfe7bfff7edeffbefffffebbddf7bbefffdfff7fdffb7dfbffb4ffeff7fe

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches97 : PLift ((OMA.PrimeProgression.composite primes 11 1425348 1734) = mask97) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified97 : PLift (rows97.all (check 1425348 1734 mask97 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct97 : ∀ r ∈ rows97, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified97.down r hr
  rw [←maskMatches97.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows98 : List Witness :=
  [(1586,1819,107)]

private def mask98 : ℕ := 0x7bffffd7fdfefbf9ffbfdfeeb7fff5db7bffff7f7ddafbe7ffef7ffafdf5dfff3fbe7ffedffbefffdffef3dfffbfdffff77faffeffbfffeff7f7ff3ffbfff7feff2ff75ff6ffdfffbaffbddffbfd9ffffffa7ff7fbfdefbefd7ffbcff7de7ffffe7ff7ffdf67bfff37ffdbbffffb7dffffaff7efffdfed7dbbfb7fdef97ff6ddfeffeffefefff5fbdfffdfebfcfffffffffbf7d7efbfdefffff7fdedfffffef37f7fffdfbfbadf3cf7ff3fff7ffeb3ffffbfedffdfeff7d7efffffffadfbdbffbefdffbb5ffdf67feffafbfffbdffefbddfffefffedfef3ef3dfe7bffdffbeffffdb7bf5ff7bbffedffebf7b7ff6ffefff7ffebf6fffffffedff5f77ffefbfbeef3dfeffefffdfffff7feedfffffffdf7ffffbeed779b7fbdbefd7fffffeeb7dffeffeff7ffcffe97fb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches98 : PLift ((OMA.PrimeProgression.composite primes 12 1442467 2379) = mask98) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified98 : PLift (rows98.all (check 1442467 2379 mask98 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct98 : ∀ r ∈ rows98, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified98.down r hr
  rw [←maskMatches98.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows99 : List Witness :=
  [(1707,1706,112)]

private def mask99 : ℕ := 0x137f7ebfeff7bf7bfdfff9bfdffdf7fff9fffbffe7befffffffffdfbfbefbfdb7fdffff7bf7ffdff7fbffa7ffdfbe9f7d7effdfefffdfeef7ffedfb5bf79efdfdffffbff7cdf6ffefafffdfbffefb7ef75ffefffbfed7ffffdf6ffefeffffdfffedfbfd7effffefbe7bfff7ed6ff77bffb77deff7ffffdfeffe977b7dff5fbffbfdeff7df7dfbeff7fe7ffefbfffefbff7fdbdd7ffbfb7fbefffdfffffff3ffffd6fdfffffffefff9ffdffffeb7cd7ffedff7ffdffdbffffed7ffbfbfff77fbed6ffeebb5feedfdfffffdbb7d7fbfdfefdfdffffeeffffffbb6ff7fefb6effdffffffdffbeffbffbdf7dbf7defffdbfeff7dffdaedbf9efffffee9eddefffcbbefefbffffffbfbffd7ffbff7f9f4ffdffff2ffff9effffbfebfcdffff7fbfbffbfdff5ffffb7deffedff7fe5ffefeffadfffdeff77ff6f3ff7dfbfbf7f7ffffff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches99 : PLift ((OMA.PrimeProgression.composite primes 12 1456071 2561) = mask99) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified99 : PLift (rows99.all (check 1456071 2561 mask99 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct99 : ∀ r ∈ rows99, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified99.down r hr
  rw [←maskMatches99.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows100 : List Witness :=
  [(1903,1542,136)]

private def mask100 : ℕ := 0x7bffd76f7cdefffcfbff6fdfdffdfeefb5fffffdffffffbf4ffffefd6ffbff37fffdbef3fdbdffffffb7ff7fffff37feffeffffff6ff4b7ffaedbfbf4fbdb7f9effb7beffbfbfff6ddffbfebfffffffddefffdf7fb7ef7ff7ddb7fbcffffeff779fef7ebffdffd7fffefffbf7fbcff5fb5ffedef9fdff5fadffdffeffff6fff7f35f7fdfdf6ffbebbeff7fffff7ffdffef7ff3ff7dbbcffdfff96ffefffef7ddfeb7ffe79efffd9fededf75bf6fffff7ffffef9fff3ff7efffdbffffbb7ffeffef3dfedff6d7f9ffd7ffffff6fefd3dfadfffff7d77bbfdefff7fbffeefefdbfbedfbfbeff7efa7dfebfdbf7ffffbfdfdff6fef97ffbfba7f3ffffdeeffd9fffbfbfff7dffdfefffdb7fbbfffdbf4fbfff6f7dd3dfbfbfffffffed77dfeff6feffefffffadbf7b6fbbeffdfffbffdffbeff67ff5ffdbefdefdffdfeffff7fbeedffdbdfffd7ed7dff7befbbfff7fefdff9fdfffb7ffbffb5dbfffeb6ebffffd9effb6dffbf

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches100 : PLift ((OMA.PrimeProgression.composite primes 12 1467213 2855) = mask100) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified100 : PLift (rows100.all (check 1467213 2855 mask100 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct100 : ∀ r ∈ rows100, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified100.down r hr
  rw [←maskMatches100.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows101 : List Witness :=
  [(1759,1737,117)]

private def mask101 : ℕ := 0x3efbf7feff3cf3ffffb77f6fdbdfeddffbf7befffefffbf7ffcf6fffedf7dfdf34fffdeefbdfb7fffffffffdf7ffef7fdfefefdfdffdfffffefffdfffffffdffeffdfbffeefbff77bbdffdfa7f77fee96ffff9fffff9efdaffefdffffdffff2efefff5ffdb7ebfcd7fffffffb6fd6ed27dedbfefffdffdfffeff76f6f9bffb7fb5bfdf7ffeef77dbfffffeff3fd3dffeff5dfff7fffdffffbdfe6ffddbfff7ffffffffdfbfff6bf7ff7bfdfefffcbffdf6f7dfbfff5ffffee9bffffbf6f7cdfffafffd9beffff77bfdffdffdffefeffffd3ffacfffbffdfffffffdfffffeffff3ffbfbf797ef3cf77dffffef7ff6fdfffbfb3fff7ffffbfdeff7ebf7ffdfafdfefffdf7fecffdfbffb5d76dbdfafbe7ffffffffff65fbefffbffbfeff7ffdbbed6ffffffffbcf7fdf7bbffefff7f7ff7ffeffefdf6fffb7fffcfffbfcfb7f7fffff6fbe7b7efe7feff7f

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches101 : PLift ((OMA.PrimeProgression.composite primes 12 1527692 2638) = mask101) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified101 : PLift (rows101.all (check 1527692 2638 mask101 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct101 : ∀ r ∈ rows101, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified101.down r hr
  rw [←maskMatches101.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows102 : List Witness :=
  [(1953,1570,137),
  (1360,2261,95)]

private def mask102 : ℕ := 0x3bff6dfbdbf6fffbfefefbf7fb7dffbbdf3fdb7f7fff7feddedfbff7ef6effdff7fbfffdb6ffbef77bfcbffff7fffffffefffeb6eb7ff779f7ffdffff7efefffff7fffff2efbffbff7fdf7beede7fbffbffffdffd37fffbffde7d7edfffedffefe6bffdefdfdbffbffbbdffdbadf37f6fffffefffefbdbfffbfdffbf7bf7ffffbfdfffedf7fb6ffecffffb6bfdbffd3dff7deefbfff7fbdfffdfffbfbf7fbffeffffff4d7f92fd6fffebf7ff7ffcfedbeeff7ffef7dfbf9f5ffff77bfedfffeefb5ffffbcff7df7ffdf7fdffffffffff7bffbbfffffe7b77d7fdeffffff7f7efffb7ff3fda7fff9fef3cffffbcffedf6ffedb7bfffbdfe7fffd2fdedff4ff7ffffafffffb6ff7dfdfffbe7fffdfebaeff5ff6f76bffd6dfbdff7f7cf7ff3effffedffddf7f6ff7ffefbf7feef7fdffdecbf7feffedf77fbeb379e7bfcfefbb5f3fdeebffdffbf5fbfbefdeffbf9afff4f7ff7dffffefffed77dffdffffcfffffff7ffff9ffff7ff7fbff7fdffb7fdeff7fff7bffbfcfeff6fdfffb7fbe9f7fbffffbe7b7dffffbffffdffffd9fe9fefffffcbfffffdfcdefffff74f67bbfdefffdff7fffffdfefdbffb4fefdfff67ff7bbedfffeffffdfff76bf7ffffaf9f7f3dfff97fdf5fffff7dfefeddff9efb77b7efeff3ffefff69fff7fffddfffffd7fb7ffedfffb3edefbbefbdff7f77b7ff7fdbfdfdf7fdefd7fdf7faffffdfedaddffbf7bfcbffffffffdeff7fb7fdfcff7fffbb6dfff7eff79febfcfffb3fdfd9f7f7fff7f7ffffffdffeff7ffef3dffefb7d76dbdf6ffffbbdfe6dffd6ffbff7fb7fdbff7dfbffffffefefdedfbebfeff7fbdd7ffe7f7eff7b6ddfdfeff3eff6fffffdbbfff7bffffdd37ffdfbebfeffffbddefbfffffdbcf379bfbf5fefbaffffff7ffdfffd3efffffef7edffbfcfb7fefffdb6f9fffffbafff7ffff7fdffbf5ffffffdaffe7dfdf3fd7fbbef67dffbfcfffffef6fbfebffbef9fcf7fdf7ff5b7ffeedffdafffff7f9fdff7ffdff7fffd3dfeffe5fb7bf6dbddbfffeffff7fbfdfffbaffbfffff7eff7bfff7fbf7bffdaf9befffffffbdfe7fb5ffc9fff6fd7ffbeffdfe7ffff77ff6fbcfeebfdd7dfedffffeffffffdff7ffefffbbfdfffbcbfdbe

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches102 : PLift ((OMA.PrimeProgression.composite primes 13 1533105 6415) = mask102) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified102 : PLift (rows102.all (check 1533105 6415 mask102 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct102 : ∀ r ∈ rows102, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified102.down r hr
  rw [←maskMatches102.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows103 : List Witness :=
  [(1888,1656,129),
  (1867,1676,125),
  (2000,1566,129)]

private def mask103 : ℕ := 0x6feffffbfdff5fe7f6ffbfffdffefff9fddffdfefb7fffd7cfeffa7f7fdee9ffff7bf7fffff7bfdfbfffff7fffff6fdfffeeffddf7f6ffbffb4ff5dfffffdffffefb7bff9fffbdfeeffeff7fbef7ffffffffffdeede7ff5bbfdeff7dfeffffbfef7eb6edfffbef7db77dffffdbaffb7f6ffffdfffe5ff4f77ffffbfdffff7fe6f7ffffffdbfdfeeffeffffb7ffddff9fffbfbfeff6f7effdfedfe5ffff7fbfedfffacbbfbffffefafdf5ffffffdbdfffffdf7ff7effff67dedb36fffffffffbf6bb79effffdbfbfebff9fffffdedffdf7fffef7ffb7ffebf7ff7feff7fdf7f7dbff9fffadffefb7fffdfcff7fb5ffffffd7fdeffbff76fe7b6fffdffeffdd77bbdfefbb5fffdf7d6fff7fbeffdffefffd6ffe7b77fffdbdfefffffb7f66ffdf3fbffbfedfff6ed7fdfdbff9fff2dfefffff7fffffeffeddffffcdfffffdbdff6ffdf77f7fd6fbfdf3efffdfffbfdbfb3ffe7ffff6fbefbfdfffbbfdf7fb7ffdffff7cdffdf6ff6ffffffffddfffbdfe7fffdfffffbfff7ff2fff7fffb7fff7fadfefffffffdefd7ffff9fff3ffefbffdefffff3effff2edbdffeb7dffffeefa7de6f3dfffd7df37bedfffbfefefdefdf7ffebefdaffaddfebb7ffefbfff7fffff4fffbfff7fdbff7fbf7d7fffddffff6df7baffeffb5fff9ff9eed7ffb7fff97ffedf7ffecfbff77dffffdfeff7ef7fffffb5df7f7ff6ed6fde7fffffdff7dbdd7dbefbffbfffbcfbfffefbc9efffff3fffcbfff7ff3fd77bfff77ffffffdfffeff76bfff3ef6ffefffffeff7efefdfdf75dffdfffffbb6fff97fbfedff9bdf3df6fdfefffba7ffdd6ef7df7f9fffffbfffbfffffbdffffe6fbffffdeff7fdffffefedfffbff9f7ffcffdbffffebf6ffcfbd9ffffefe797ef3fffcfb5ffff3df2ffffff5b6ebfffaffbeffef6ff7efeffedfbddefbefdfdfffffdffffadf7fdbfbfdbfffbfffd9f5fbef67ffffbfbafffdbefffffffbfefbef7ffbfdb7dfffb697effff7dbbfffffffffff6dfb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches103 : PLift ((OMA.PrimeProgression.composite primes 13 1563264 5736) = mask103) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified103 : PLift (rows103.all (check 1563264 5736 mask103 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct103 : ∀ r ∈ rows103, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified103.down r hr
  rw [←maskMatches103.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows104 : List Witness :=
  [(1603,1984,112),
  (1948,1633,134),
  (1966,1621,135)]

private def mask104 : ℕ := 0xbefffe97effffbfbe7fff9f7fedffffeeff5d7ff6df6fdfff3fffedffffffeff7f9ffdbfffdbefb35feefffdffbf4bfeff7dfffffff6ffcbfffbeff7bfdffeff7f6ff7dfbeffffffd3cdeffeebffb7ffeffb7fbdbb7b7fbbfff7fa5ff5feff3ffffdf7b7dfeffeffafdffffdff7fafdffbaefbfff7bffff7fbffbdfffdfffe7ffdffcf7effffbfffeb3fdf6ffff7ffffff4ffffefdefbfffbfffffbedfdfe7ffed7ff3fde5deff7f9f7bfcfffffebf7beff7ffffdeff7fff6dbdf6fdffff6dfeffef6ffb7ffdffff3ffe59ffbf5dfff7dffddafff4dfff7dfaf9b6fbdbf79ffff7ff6ffdff7ffedff9ffbbff7f9bfde5fefbffbf7ffffe79f5f7ff6ffffdf79f7ffcfeffeeffdfafb77fffbbddef9fff3e9f7deefffffdff7dfffbef7fbffffefefffddfffadbffffeffffffda7ffddfed3ff7fdfef7dbffdfff2fdbfff7fffb7fdf7be4ffff7efeddfdfeffbffefdfdfbffffff7fefbfffadffcfffbefffef6dff7f7fdfefbfd6dbffff5ff7fbff2d9febfffffffefe7dfcfbdfffbedd77fffbffdfeffcf7ffffbfffeefbdf3dffefbf97f9fffffffdbb7fefb6fdfdffdffebf7f7ffffbf6bf7bfffbffbdfeefbdf6e9eefbfbfdbffbf7ffedafffffbfff79fff7fffef77dfef7efefbbfbf6ffffffdffff6bffff7d2ddfdff7bfeffffffdf5bb6fffdffb7cf7ffedbb7f77f3ffffdffffff7fbffffdfbfffefffffdf2fdbfffffefbbefefbfcf3ffffffefafff7fffff7f7fdafffcfffffffeedbdfbcffddf7f6fffffe5f3ef7efbfdf7dbdb76ff7ffef7ffe7b7ef6ff7ef67ff5ff69e7beff7fbfff77dfffbfffffeff7effed6df7dfa7bfdfffffdfbfdfff7cff7dbdd75ffdff7fffffffb79fdb7ffffbeededdf7fffde7f3ff6fff7ffcbfff7edf7fbefbef6fd7fd35fffbf7dfeffcf77bfebffbfffbffbfdfdb3ff77dfdffdfb7f7dffebbff7ffbff7fdeffbff3fbf7b77bfffaffaffb7fbfde7f6ffbdfedffdbfff7ffffbeef7ff7ffbdff7fefb3fd7ffbffffdafbbff7ffbedffffff3ffefbfcdefbffbfddfffeefb5dbffbffeff7fd3dba6bfffe7dbff3fffefffbf7befd6fffcff7deeffdff5fb7ffffff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches104 : PLift ((OMA.PrimeProgression.composite primes 13 1590176 6216) = mask104) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified104 : PLift (rows104.all (check 1590176 6216 mask104 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct104 : ∀ r ∈ rows104, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified104.down r hr
  rw [←maskMatches104.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows105 : List Witness :=
  [(1556,2067,104),
  (1503,2141,100)]

private def mask105 : ℕ := 0x3febeef7ffffbfffefdbefe7dfcb3df7fbfdfbffbeff7ff6fbdffdffdf7edeffeff7fffffffff79fddffbb7f7cf7ffeffffbefffddfedeef7ffacbffbfef2ed7fbfff7dbffdbff3ffeeff6fffffeffdfffbb7d7effedfffbfbfffffd7dfffff6ff5bf7bfdfbf9bff7ffffdffd7fbecffdf77f2ff3fbedff7bf7ffdfedfbdf3ffefffdfffde7bbfd7fffff77bbffb7bffdeffafbfff7eb7ff7efeddf7fbefeebffd3dfffffff6fdaffffff7fffff7ffdffffedfffbffbfff3fdbfbbfdeffbeff7ffdf7fde7bfefedfbeffdbf7fefff5bf7ffff7fffff7ffb7fffbf7ffdfefffeff6ff7dfdfadfefbfe97effef6f9effbff7fbfffefffdff69ffdedfbfdffffeffff6dfffdfefffb6f9fdffdbbdff5ffefbedbfbf7fb6ff7bfff37ffff7fbff97efadfb7f76fefdfff6fbbdfffbf7ffffffda7bfdffffaffeffeeffddefd7ddbfbf7bffffff3ff7ffefbfefeefbfff7fafff7fefd3df3ffefb7fdffdbffefff7ffdfe7ffdfffffff76d77beffe7bfcf3dffff7cfbdfffbbfdfed7ffffdfeb7ffff9eff7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches105 : PLift ((OMA.PrimeProgression.composite primes 12 1608126 3090) = mask105) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified105 : PLift (rows105.all (check 1608126 3090 mask105 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct105 : ∀ r ∈ rows105, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified105.down r hr
  rw [←maskMatches105.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows106 : List Witness :=
  [(1808,1786,121)]

private def mask106 : ℕ := 0xfffeff7fffffffff4bfffeffb5dffbffde7dbffafffdffffffd7ff7fbfef7eff7f6ef6f9ffbf6f7ef7dffffedffd97effff7fff5ff79fff6ef7fffcfffbefbfdffffbcbfff7fdbef3fdb5f77dfffafff5bfeffffffbfff7ffbef7fd7ebfdfb5bfcffef7ffffdf7ff7bbdbf7feefe79efffdbfffaddb7fffbbfffedfefb5bffbbff6fb7ffed9bfffffe7fadf7ffe7f7fff7bfffbffeffffbefd7fd7dffdffd9fedfdfffffdf37fffbafdf7dbfbfef7ff7eff5ffdffdffeb7fd7fbfeb7ffffffddedbbeffdf7fffcfefbf7fbdffedfdff5fffff7d76f2fffffeffb7fe6fffdbffffffffeeffeff7fafb7ffffbefdfdffcf7dfffffff6dfb7ff6df7fbedbffeefffdeedfcdfdbfeffdffefefdbfff7ffdb7ffbdfefdbffffb77f7fffdfbfb7ef7fbbffffffdff5ffff3efffbffff7dfff7eff5bffffdbf7dedfbfffeff7ffeffed6f9ffb3ff67bffff5ffcf7ff7fbbefff9fdb76d

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches106 : PLift ((OMA.PrimeProgression.composite primes 12 1614544 2712) = mask106) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified106 : PLift (rows106.all (check 1614544 2712 mask106 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct106 : ∀ r ∈ rows106, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified106.down r hr
  rw [←maskMatches106.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows107 : List Witness :=
  [(1591,2053,106)]

private def mask107 : ℕ := 0x3ffeffb59ffffff6f9fffb7bfebffdfffaeff6fffbfffaddffb7fd7ef7effddfcf3fffff6ff3fffebff977fffdefffdfffbffdeffb5fe7bfdd7ffffd7fbfeff7befbfdffffadbb7fffd3ffbfffdffffef97effffbfff59e7d3ff7f9fffffffffbffb7fedffffff96fffdbbfbb7df7dffdffff7ffdffedfffbffbdfffdfffbeffddeff3fffff3fdfdff6f7fdef9fdd6fdf6fffbf7f7dfedff7f3ffefffdff7fefbf5ffed2ffe7dffbfffe6ffff3fffdbffffefbef75ffdff4fefdbfdffdfefbefefbfffedff6b7ff77f7ffff9fffbdf7ef7fdf5fbdbfffffd7ddf7ffff3ef7fbfff3fffdff7f77bfffb5fb7bfefffbffffffbdbfebfffacf6ffaffff97ffaedff9ffffeffedfef7fbfffb7d7ffbff6fffcffff7fffdffffffbfed76bbdfff9bdffcfffdffffd9f4f3fff7d

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches107 : PLift ((OMA.PrimeProgression.composite primes 12 1633162 2386) = mask107) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified107 : PLift (rows107.all (check 1633162 2386 mask107 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct107 : ∀ r ∈ rows107, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified107.down r hr
  rw [←maskMatches107.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows108 : List Witness :=
  [(1870,1794,114)]

private def mask108 : ℕ := 0x1fffff6bffff7ffffbfdfdf3effed6fffdfbdff7feef6dde7fe7ffdbffdbff7ffeebf7fefb7ff6fff5fbffffb7efff9ffffefff9ffffdfefbffdf7f6ddeffbcffdd7fdfeffdbfcff7fefffffffffffffb6fffddffdbef7ef7ed7ffbffbdfbfffedbffffdf7fffbfff7fdbfbeef7ffffffdffdde5ffff6fffddffbfdfffffefeefbfbeebfffffbfffafffffbfdeff7ff7fff5bfcdfffbff7fffdfbffe7fefdfdbafb7cdf7bfdfffdfff3ef7ffffffffbfbfdffffbdfefdefb75ffedffffffafbf7f7effff65dfdbbdfeffafffffbffffdeff6ff7f9b6f7fffebbffedffffffbfffeddbfbfeff7f77ffffb7bfffffbefdeff7ffbffffdff9fffbffa7ffef6ff7fdfffb5ffcfffb7ffefbe7ffeffffbffa5dffffe9ffffefffffefff97effdf67fffbfef76fedf7ffecff7beff3ffbffbdfbdfff9fff6fdfdf77fffbeefbfffff7fff7f3fffdbbefffdefdffffdbb5bffdeeffdde7ffffbfffffbffefffdfbff6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches108 : PLift ((OMA.PrimeProgression.composite primes 12 1677390 2805) = mask108) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified108 : PLift (rows108.all (check 1677390 2805 mask108 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct108 : ∀ r ∈ rows108, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified108.down r hr
  rw [←maskMatches108.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows109 : List Witness :=
  [(1525,2236,108)]

private def mask109 : ℕ := 0xbfbfff6ef3df3ffedbffdfe9fef7f9b5b3efe7f7ffffbf7ffcffff3dda7bfdffffeebfdfbffffbbfdf7dbcf7fdfebf7ffeffdfffdfdf7ff7edfff7fdb7fbfffffeeff7bfeff6ffffbef7fdbfb7fb7ffedffdfbffbdfe7d6fdf7ffebfff7ffeeff7be7ffffe7fbdfaffbfbffbef9ffffddfdbbeffefffdfd9ffbffff7b2efffdfef77dfefbffedfaefff9fffffffdff6ff5deedeff77fe5fbffefbefff7fedfb7f6effffa7dfdff7f7ffafd7f9fcfbf9ffbbffffdbff7dff6f6fdefffefffbffffcfbdbeffbf9fef6ed7ffedf7ebfefeddbffffb7ffff97ffb5feff77feebeefffbffb7ffe7dbcdedfbfff7df7b2fffffeff7cf6fdffdfffb7ffddffdadf7fdedfbff7ffedffffeefb6fffd7eff5bbfb7fdffbfffe7ffffbdfefffffbdfff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches109 : PLift ((OMA.PrimeProgression.composite primes 12 1704950 2288) = mask109) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified109 : PLift (rows109.all (check 1704950 2288 mask109 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct109 : ∀ r ∈ rows109, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified109.down r hr
  rw [←maskMatches109.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows110 : List Witness :=
  [(1247,2771,81),
  (1765,1962,116)]

private def mask110 : ℕ := 0x3fdffffcbfff7ff3dff6f7fff7beefffffcf7d9f7ffff7ffecfbdb7ff7efef9fdff5ff7feffe7ffdfbfffe93dffffafbfdf7fffffedff5f7fbf7d7efefbeff77bfffbdfffbe7fffffff7efffffffffffef7fd77bfebfdff7fbffbfdbef37fe7ffcf3fbbdb77d7fffef6fffffbffe7ffff6fdffffcbf6ffcdffff7ffedeeffddffbf7fbff7effff7fffdfb5be7fbfd35ffefbfdee9bfffdbe5fffffefafffdbf5bbfff7fbeffdfefff7ffefadfefffff7fff796ffbfff7fff9e7dffdfffeffbffefbfffa7deebf6fe7fffffd9effffd6ffffdefdbfbfe9ffbffffdfffffdbfffefdb7feff3edffdfff7dbfcff7f66faff7fbedf77ff7bbffffdfdf7effef7fffffe7ff7fffdefffffbff7ffffbeefbffeff7dbffbeffefdfeffcffffeefbdfffbbddeef7fff7bf4ffdffffffd7ffefb7ef7ff7efafff7fbdfefdfefe7bf7fbffffbfdf3f9b7bffdf7f3dfbdffeffddfef6ef7fffefb7feeffffbffffffff7ebffdbfffffffb7fffff7f9effbffef9ffdedfbeb74ff7fedd7ffffb7fffff3fdefdefffff7efffd7fffefff9ffffffbfdefbfeb6ffeff7fdadfbeffefbdffdfadf7fdefdfff7fffffb7fffdfef6fdf6bfdf77fbcdfdffcfffb7ffeffb5fbffbdbfff7ffff9f5b77ffffedffffbfbfffffb7ef67bfffb7ffff7ffe7fbffbddff9fedefbf7fffffef6fdb5fb5f7fb7fffefbfffefffbffd6dff7ff7f37f7fbbff6fdffffff7fdbfffffb7fbeffff2ff7fffefbfbe7f7edfffffffddffffdfbffaff7fffffefdffff5fb5bfff7ffefdeff3fbeefffdbffefbbffffffefa5df7ffff7fdfeffdfffff4de7fbef6fdffb7fffefbffbfbffffef7f9fdffdfb7ff7b7fdfefef9eefffffedefdf7fafff7f6fdfdff79f5fbedff97ff7fffefb6ffff7fffffe6ff4fffffdffdffefbddffbfdf3dfbffff9feffffffbfcffdfefffff7dffdfffdeef7ffbdfb7f7fd7ebeef67ffef77df7dffd3ffbff7f977f6dfffdf7fbefff9ffdf7ffeffddfefefff7ffdf7eff6dfdfeffffbf7f7fdbffff9fdbf7f6ffffdffbfdfb7bff9fdffdfe7f7fff7ffdfbdff7ffdfffbeff3fbfcff7fe6ffcfffffef3fbf7defdf5fffb7fdefffdff7daffffffffffd7fff4ffe9fff2ef7fdafffeb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches110 : PLift ((OMA.PrimeProgression.composite primes 13 1727719 6394) = mask110) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified110 : PLift (rows110.all (check 1727719 6394 mask110 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct110 : ∀ r ∈ rows110, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified110.down r hr
  rw [←maskMatches110.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows111 : List Witness :=
  [(1745,2018,108)]

private def mask111 : ℕ := 0x3dfeffffbdfffdfff3ffefdfff7efffffedffffcfbeffeb7ffbfbb7bff976faffffbe7bbff77fefffffeff7f97ffbff6fdefff5ffeffeff7fffbfffffb3fffdfbfff7dfef3cff7fe6fbfdefd7efffbf7bbfffffbedfffffffdff7bfffb5fbdffffffffdfef9e7fb7defbeff6ffbeffeffffedfffde7bfff7ff3cfffffffffd6effff37ff6fffbfffaedf7bfdbf6beefefffddeff77ff6b3ffbdffff3ffffb7edfdbffb75fffdfff6dffff7f9fffffff7dbffbfdeeffffffbfeffffe7fefdefdeff7ffffbfdfeddffbfefffdbdfedfa7bf4fffbfffffbffffefffb6dfff9ffb7fffefaefffbf4ffffffd7df7dfbffffb7fdefdafff7fffffffafda5ffffffbf7bbff77fbfbbffffbffdeffffbfede79edffffbfffff76bbfff5feeffdffef7ddfffefbfff7ff3fd2fdffffef7ffbffeffffbf6ff6ffef7dfedff6ffffffff7fb7bb7ff7f7fffdff7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches111 : PLift ((OMA.PrimeProgression.composite primes 12 1760705 2618) = mask111) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified111 : PLift (rows111.all (check 1760705 2618 mask111 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct111 : ∀ r ∈ rows111, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified111.down r hr
  rw [←maskMatches111.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows112 : List Witness :=
  [(1920,1861,127),
  (1580,2267,105)]

private def mask112 : ℕ := 0xfffdf696eff7fb6fbffefffdf37dfffffb7ffbfd3ddffbf6ff7bfdf7fffdfbef6efeffff9feffedffb3dfaffffffdffff6effddf7fbfbffbeef75ffffbfdfffbffbffffffefefdeddffffdf3fff69fdff7faff7dd7ebbeffffbefb4bfffeffefffffffbfff3fffdfe4fffffebfdffffbfbffd77f3edfffeeffffeffedf6fffdffffffbfff7f9ffff4ffffafd6fbb5f77fffffefbfbfeff7dffb6edf59effbfd7efedf3fff5fbdf77f7fff7bf4fbdffefadfbfdfeb7ffee9bff6fffdbfdffff7efffffffffffffeedfffffbffffebeefe7ffef7db779fef7ffb5ff7defdeffefff7fbeb7ffffdffdfdbffffeb7efe7befbb4f7fdffff7bbdbbe9ffffff7dffeffdbfff7ffafdfefbffeef7ffffffebf5ff6ffffe7dfffbfff7dbdd3ffffffefe7ffdfefff5f7ffee9ffd7dbfdf7cfffbbddbfbaeff7df7fbefafdfff3ffefd6fffdffffbdffefafdffffefffbffbedfffdfff3ff7effcfaddf7ffff6fbbfdffffdbf7ff7bbffff9eff7fb7effddf5fffffedf6beeffffafbf5ffeffff6fff7ff6fefbfddaffbdf7e9fffbeff79fffbfd7fffedefbb5ff7dff9fffffffefffff7bfdffffbff3cfefdefd7ffe6fffffff7dd7ffe7fb7bfffffff5fadfbeb6fffffffffdffedff9fffffff6f7fffffbdffddfebfdb77ffedb7fffffffffbfeff5fffbf7bf6f7fdbfdf6f7fff7fafdbffbcffedfeffff77ba7ff5fffffffedbbfbffffff7ff6fffffffbfefaedf5bedf7ff7fbfcf7fbafffdbfefaffbfff4bfffeededfbfdfffbfff6ffdfffff7ff5fffb3eff7fffbfe9fff7ffadbf7ffdffffeffe7ffffbebfefeeffdbb7fffffffbef67bfffbdfeffbffb5dffffed6ff3ffedfffff7f7fbfedf7dfefffbefffdfeffefbfff7ef6dfbfffffbfff6dfdfbfbb6fffbe7ffed77dedfbeffedefffddfdf7ff67fbdfefffdb3fffed3ff7fbf6b3fbffd3ed7fbffff7dfffffffdbf7ffeb77feef3fbbffbfde7f7fdf7feebffbffffdfbfdbfbffdffb7dffffffff7ffedfff6fbb7f7effffefdbffffff6b7ffefff7ba7ffcff7bfdf3fffeffff7efefd779effb6ffffbddfffffff6fffb7dff79ffbf7ffebefffffb7f7ffef9fefbfbf7f7fdf7fbefbffbfffddfefeffbfff7bffff7dbfd7ffeef3fb7fbeff6ffffbb7b77fffffffe5b35dfebbfff7fbdf7fbfffadffffffff5bf7f3edfdbfffbcff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches112 : PLift ((OMA.PrimeProgression.composite primes 13 1786560 6740) = mask112) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified112 : PLift (rows112.all (check 1786560 6740 mask112 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct112 : ∀ r ∈ rows112, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified112.down r hr
  rw [←maskMatches112.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows113 : List Witness :=
  [(1769,2037,121)]

private def mask113 : ℕ := 0x1fbfdfdf7fdf7f7eff7fffffdfeefbfdef9f7ffffffdffd7dff7fffbffbffdfd9eff3efefbfddffff7ffffefd3effffeefb5b77bbdffdfffbffd6f9fdfbfbfff7cfffdbffffdfdbfebf7fedfafbb7bf5fffb6fde7bfdf7fdfffeff77ff7ffdf67dbefafff6bf7f7ebbff6fffefffd76f7cf3fff7f3efffbbfd7fffff74bfffacffddeff7fffff7fdefdbdf7dfefdeffb7fb7ff7ff7ffefb7ffff74b7ffffdefdffffef6fffffefdfff3fdffdbefffdf7fbdbffdbcf3dfb7f75bfeffefa7ffeffffe7b6fd75ffffffdfffbffffdf5fffbffbfffbfdfef7ffefb3cfedffdf7fd7fffede7ffefb6dff9bfdbffeff7ebfef7ffbfbeefffff7defd77bbdbfff76f7dfffffef3dbeffefde7dfebffdfffbffb5fffff7ffffefd75fbdffedfff7ef7dfb6b7edffbeffbdfa7f3ffe7ffddffbbffffbe7dffd7ffe7ffffffdafdeffffbbfffebfffedfbfbbeffffbff7f

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches113 : PLift ((OMA.PrimeProgression.composite primes 12 1801727 2653) = mask113) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified113 : PLift (rows113.all (check 1801727 2653 mask113 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct113 : ∀ r ∈ rows113, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified113.down r hr
  rw [←maskMatches113.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows114 : List Witness :=
  [(1951,1852,131)]

private def mask114 : ℕ := 0x5effffffcff6ffdfff9fffbdb7fffeff7fb7fb7bfffafdfffefbfdffeffdfffffdfffb7ff7ef3fdfdbf7fefb6ffffff5ff6dfff3ef7ddbfb7fd7ff6fdbfffeffedff9feffdfa5fffdffdffd7fdffbf7ffefeffedfffbf7def97ff7f9edf3cf7fbaffefffcf7cbfff3fffdbffff7d7fb3efe7be7ffffefffff3ffa7bfffe6ffcd7fff7ffcbffbfff6ffbefb7ffef3cfeffffffef6ffbfdfffbefbebeffffdeffefb7dfffbefdedffcfbcfeebedfffffdbffff7ffcfffffdffff7fdedfffdaffbfb7e9bffbdbedfbdffefffdfddfff7f9ffbffd3dbeefffdffbbffffff4f7dffff7fffffb7bbf9f6ffeffffeef3dff7ffff7ffeeb7fffedfffefffdbbfffffefffffb6fbe9f7deedeffb7ff5bfeffddafff7ffdd7fdfcfffffffb7f6ffbfffffefbfefe7dfdff5fffff7ff7f7eff7fe5fbdf7f97ff6ffb7bbfde7dfffbfbbfff59fff6fff7ffffbdd7fdefff5fe7ffdf76f2fdefbfdffebf79bffffdfdff6bfffbfffdfbfbfef7ffbeff5bf6fffdff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches114 : PLift ((OMA.PrimeProgression.composite primes 12 1806626 2927) = mask114) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified114 : PLift (rows114.all (check 1806626 2927 mask114 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct114 : ∀ r ∈ rows114, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified114.down r hr
  rw [←maskMatches114.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows115 : List Witness :=
  [(1286,2833,85)]

private def mask115 : ℕ := 0x17fefffff6ffb7fff97ffaedffdbffbfff7dffdf7feefbdb6ff7dff7ff5fffbfefefdf7fbfbf7deeffdfb7bedffddfe9fefffdfff7ffe7bfffaffffffdf7effefbdfe5f7dd7f9fed7fffdfb7f7fffffefdfef76ff7dafd6ffbffbfbfefbff77ba7fb6fffffff7fdfffbcfefd3ff3ffffbfdffef3ffbfffdffffe6d7cfb7ff6ff5ffff6efeffe6bfffffbffdffffefffdefffdfafbfffbffff97ff75ffdbf5ffffffdedfafffff7efbffffff6fbfd77dfefffff6ff7ffeffed7fdf7ffffef9fffe7fffff79efffcff5bbdfb7dffbaefffffebf7dffbfdf7dfeef75bffbfdffddf4fff97efeff7fbbfffdbeffbffefbfebfff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches115 : PLift ((OMA.PrimeProgression.composite primes 11 1821619 1929) = mask115) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified115 : PLift (rows115.all (check 1821619 1929 mask115 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct115 : ∀ r ∈ rows115, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified115.down r hr
  rw [←maskMatches115.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows116 : List Witness :=
  [(1674,2200,109)]

private def mask116 : ℕ := 0x7fffdfedbf6dfed7fdffffff7fffff7ffbffffffffffbbddedbb4f7fbffffff7fbf7fffd67dfeffffedffdb77fefff7fecbbfff797dfa7be7ffffffdfefefffebfffffd7cdefbffbf7dffb3eff5ffefbedfff7fd3fff7fffdefd7efbf9e6ffdfffffdf3ffffff7f76ffdf7f9f5f77fff9fef7ffbdf3fffffffd7fbefbffdfff7fdf79efffdd7ff6fff7fffbffdfffbff77bedb77befdefdfdfefffef7fb3efefff7ffddffffefe5fbff7ffffffcffdbe7ffeff6ffefefffef7dffeffefffbfdbbffeffafd37ff4ffff6f9fff6fdfdbbff7fd7dfffdf7f3fdfefefff7dbffffbffbbddef9aff7fffff3ffff9f6fbf9feffcf7fbfefbfff7ffff2f9fdfffffffbddbffffb7fdffdfff3ffefffff7ff7ff7ffbff7f9efffffaffbfffeb77f6ffedfaefbddf7b7ffb5feebfffffdbdfffffefffb7fffdff5dbdbf6be

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches116 : PLift ((OMA.PrimeProgression.composite primes 12 1841400 2511) = mask116) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified116 : PLift (rows116.all (check 1841400 2511 mask116 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct116 : ∀ r ∈ rows116, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified116.down r hr
  rw [←maskMatches116.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows117 : List Witness :=
  [(1661,2294,113)]

private def mask117 : ℕ := 0xfefbdfbfdbff7df7fbeefffffef7e9f7dbdfffff7f7797ffbffefffffffdfff7edbdbfcfbdd76d3ffbffe5b7cffeffddefdfff77bffffef2dfb7b77def9fed77fffbf7ffffaffeffffffe9fff2dff7fbdffdffeffef77ffdff7fe7feffffbffff5f6ffffffffedffebef9beff5bfffbfd7eb7ffe7fffb3fdefbffd7ffb6bfdffffffde7bffffdff6fffdfdfffbffffef7df2fffefffbefbffffffaffbed6ff7eff5defb75ffedaffedfbfb7dffff2fdffff7ff7dffffefa7bb7fffff7ffff75ffffb5de6dffdffdeeffff6fbffdefffffbeff7bfdf7f9f7ffffffdfffefbbff77fefffdf7dffebffff7bfffb7dbff7eff7f7fdbfbffbf5ffffbdfefdedff7fffdedd7ffbfb3ed7fbfdfedfffff6fffbfffffbfffbffffffdfeddf7ffcd7eb6dfb7feff7fb7effff7dfa5ffdb66d7dfe7ffff35bfebffd6f

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches117 : PLift ((OMA.PrimeProgression.composite primes 12 1905167 2492) = mask117) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified117 : PLift (rows117.all (check 1905167 2492 mask117 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct117 : ∀ r ∈ rows117, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified117.down r hr
  rw [←maskMatches117.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows118 : List Witness :=
  [(1692,2351,106)]

private def mask118 : ℕ := 0x1ffff7ffdff6fffffff6fbffff7f77fbffb5dfffffdfffedffdfeffffbf6fbfffffffb7cbf6ffdfeffffff7df79fffffbfdf7efffb6ffffdb7bfedffffffefdbfbfedf7b3cdfddb4ffffffd7ef7ffe7ff7fffd3ef3ffeefb7fe7fefdf7dbdfbffefd3cfffffdf7ffefffffefff7bbf9ef9affbfdfebffd7ffeffbfff7f7effffffff5fffbf7d77ffffffbeffbfffe9ffdaffeef7f9f7ffcff5bbdf7dfefffef7d9f7bfdfeff7fd7dbfffffdfff7dfffbf5ffebff9fcff7ff7bf5fefdeffffffef37fefbeffffffff7fff7ffdff7fedff4f7ff7fff5bbdff6df7fffdfffb7fffffff2ffffffffbff77deef77bbeff5f6edefffffffff5feeffff75fffffeff6f7ff7fbfdb77feefbed7dff7ff79f7f3fffffb7fffbfff7dfbfdbff7f9effffffffeffbffeff7edaffefbfefe7dffffffaefffdfef7dfffdffbfff7e9bfde

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches118 : PLift ((OMA.PrimeProgression.composite primes 12 1988946 2538) = mask118) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified118 : PLift (rows118.all (check 1988946 2538 mask118 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct118 : ∀ r ∈ rows118, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified118.down r hr
  rw [←maskMatches118.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows119 : List Witness :=
  [(1351,2997,86)]

private def mask119 : ℕ := 0x1efbbcfee9bdfffffffbffeef3dfadffdffefefd7ffffff7f7fffffbcffdfa6bfd9fffbeffdbfdf7dffeffdf7fffefbfdffdbffeffffffff67befda7feefffd7fffdf7fffff7ef7ff6ef6fffefffbefdeefffff7fff9fef3ddffffffbe9f7feeffffefff7ff7d3fd3ffefffcbefffffffffefffff6fbffffbf5b7ffffdafd7fffef7fff7ffef6dfbefff9f7bfdfe59fcfffdffdfffb7fe6ffff7ff3fd6fbefb7fbffffffbfdfefbfdffb3ffeffedfbed7ffbefefbfffbedffbfdd7ffe7bfdbfff3ffb5fbffffb7ef7ef7ffbdbffd7fffffffffffbfbf7bffdaffffbf7d7ff7cfff9e7fbfdff9fffe7fbffffdffd7fffdfbff7ff7effedb5deffffdfebff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches119 : PLift ((OMA.PrimeProgression.composite primes 11 2024474 2026) = mask119) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified119 : PLift (rows119.all (check 2024474 2026 mask119 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct119 : ∀ r ∈ rows119, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified119.down r hr
  rw [←maskMatches119.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows120 : List Witness :=
  [(1983,2079,132),
  (1908,2165,116)]

private def mask120 : ℕ := 0x77f7ff7fdeeffdffefff9f7faedfd9bfffddffbfdfff9eff7cf7efffffffe7ffdbfed2ffffffdf7cff7fffdbfdffffffeefffff5ffffffffffefd7fbffbffde7beeffffb7bfefffffdfeddbffffb7eb7ff7dffefffff7fbffafffdffdf77dfffefffeffff6fffffa5df7bfdf7effff7ffb7fbe9ff9aef7fdefffdff7facfffde7ffcbffd7dd7fbfffffd76fbfd2fff7ffff7efefff7ffdffefffffcf7ffbfffffefdfedefbfdffdfffdfdfbfff7f7ddfff7fdfffbff3ff67f6dff5bffbf7ffff7fd7ffecf7fb77ffffffffdff7bffdfef7fdafffcfefb7ffffdffbffffffeef2fdbfbf797ef6ffff9fffffbf7ffffffffdfb7ffedfcfbfbf7fb7ffffaff7dffffbfdf7fbef67befff7fff97efff9feffffffb3ffffff7bfcdfef3fff7fa6f7fffedfff7dfeefbfffffbdfafffffbcffffedde5fbdfbfb7fffeffffffbf7feeffff7fffcbf7fefd6ddffffff7dbfffffffffffffcf77d7efbfbffffff7fdefdbfbe7bffff79fffafffffffdf6f7efe7bffb7fffefbfdeffffbbffffbfcffdfffffdff7bfedafdf5f7fdeff6ddbfffeff5bf6fbffffffffb7bfefedffffbdb7effffbfff7ff7fbef6ff3ff77fffffede7d7fdfdfffff7ff6beddffffffbdbfff7df77fbefb5fffffffe7ffffbcfefdfdf7fdffbffb7fb3ffaffffbbffeff3ef7ddf7ffcdffffdfafdbfff7f77fffffffb5f3ddffdeedf5bfdffffeffeff77befb3fffefeffa7ffcff7f7fb7dffffedfbed7fbfff77bbdfb5bfffbfdfffe6fff9fefffff5bfeffdf7ef6fffffedbf7defdffdffff5f7fff79afffffffbf7d7ebffffffb5bf7f7ffbffffbf4ff6feffbffefdffff4dfefeefeffeff7ef6fffdffffb7bbdb77dfffffff5ffff6fffdfbffeeb7fb6ef7dfe7ff7ff5f7fbbfdffdf5bf7df7fedfbfffff7ffffbfcffffedf7fbe6ffff7fbfcbffdffffefffffcfbcffffeff3ffffbffbefd7ffbd9aff76defb3fff7ff5fbffffbacfeffbeff6bfffaffb7fefffdfffffdfffbf6bf7f76fffdffffdff7fefbbff75defffffffdfcfe7ff7ff7f7fdafffdbfebb79e79fff6ffffffcbffb7efedffefffd77deffb5fafbfff7efeddbf9efbfff7efffdffdfffffff7dfffaddbfbf6d6ffbff77ffdfb6dffb6ffbfffff7effef7dfffbbfffede7feff7dfffbbfdfffeff7fdf7f3fb7effddffffef3fdfff7ffb7befbbdffe9ffffdffcff7dfff7fdfffbeffefffffefff9feffdf67fed

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches120 : PLift ((OMA.PrimeProgression.composite primes 13 2061329 6943) = mask120) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified120 : PLift (rows120.all (check 2061329 6943 mask120 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct120 : ∀ r ∈ rows120, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified120.down r hr
  rw [←maskMatches120.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows121 : List Witness :=
  [(1838,2260,123)]

private def mask121 : ℕ := 0x1fff6fbfbf7f7cf2fff6f34ffedfffedfffffedffffeffdfb7fbfdeef3fffddb7ffdfffd7efffdfffffdfffeffefffef7e9ffffef75fe6ffddfffaedfffedf7ff7ffeffedfeffffffeffdfbfbbdb7dfffb7fdedfbef7dfeffbfffdfe7ffc97fb7ffafff7fff9febfcdbffbfbb7ffff6ddf7ffdfffffebbffa7defbbfff7fffffddfff77f7fbfff7ffbef3e9f7dbfd7fdbfbffbffffdfffbefffefef97fff7ff7fbdf76d6eff7dfffbfffeffdd7dffff3fdefbfdf7dfffffff6efeefffdfffbf9fffadfbffefffdbf7f3ffb7ffffff9eef7fd3fffebbffffffed27ff7ff6fe7ffffa7dfcf779eff7ffefdb7f3fd7fb7fff7dbcb7ffff9ffffddaeffff7ff6dfffbfffbed7fffffbdfeeffffe6f7ff3fbefbbeb77ffff75fadf77ff79bffe7defb7dffffbef7fdf7bbffe7bbffefbfeff7ff7beffefbffffcfffb7fdfdfbffb7f7ff7fffffe5bfebffbffffdfedbfffefffef75dbfff7f7fbfff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches121 : PLift ((OMA.PrimeProgression.composite primes 12 2076940 2757) = mask121) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified121 : PLift (rows121.all (check 2076940 2757 mask121 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct121 : ∀ r ∈ rows121, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified121.down r hr
  rw [←maskMatches121.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows122 : List Witness :=
  [(1945,2153,132)]

private def mask122 : ℕ := 0x16ff5d77b7ffbfdb7fbdbe7bfdf7fbfeffddeff7ff3fffef3ffffdeffeffbffbfffff3dff7fffffdfff97ffffdf7ffefffdefdafffeb76fffbbedfdfffffcfeebfdff7baffffdf6d2dfff9efffdff6dfff77ffcbf7fefb7dfbfbbdff4fefbefdffff7ffdfffd6ffedfefffddffbfeff7fbdfbfdfeffff37ffebff9fefeffefbfdff5f77fbfffffefff6f7ff7cffdbf7fbff6ff2ff67ff5fbedf7dffdfffbfffe9fff7ffefff7fbfff7decf7dfbfffdf7ffffdffffdff7bf7defdbfdfefbfbe7bffff7dedffdd7fdbffffdbeb7dfffbeddeffa7ff6bf7fefff5bfffffb7ebfff3ffefbf7feeffdd2ffe5ff7feefbff7ffbfb77fffd7ef6dfedffff7efffdefbf7ff6fffdadffffa7ffe9fff6fff5feeffdf7fbeeff5bfcffffffffddffdf5ffeffebbffeffefbb7b7fdbff7fbe7ffff7fbbfdffff6fb6fe7f6edaffffbfef7ff7eff79e7fffdfefefff7ffdbffdf7ffedefff6ffebefdbdf3fffeffffefbfeff7dedff7d6fbeffffdbfbfffefdb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches122 : PLift ((OMA.PrimeProgression.composite primes 12 2093793 2917) = mask122) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified122 : PLift (rows122.all (check 2093793 2917 mask122 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct122 : ∀ r ∈ rows122, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified122.down r hr
  rw [←maskMatches122.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows123 : List Witness :=
  [(1882,2235,124)]

private def mask123 : ℕ := 0x7fbafff7ffffbff7fffcfefdbfbf7def97edffdfcfbffeff7fdfdbfffffffeffcfbfbfffffdffbfcfbfffffbfbfff6cf2fbf4b3fbfeffff67ffff7ebfffbeffffefff7defb6fdeffbffffdf7f7ffbfdaebfedffb7edfffaffbeff7fefd7fbe6fffdffdfdf6fbe7ff6ffffaffbfffffbfdf6f7ff77dbff77fef9ffffddfcfbdbe7b7fdfddf7bfebffbfeffffaffffbf7d7ffbffaffb7ffed7dfefbffffeff6fbff7fffefffdf7bfff67dffb7cfeffbfd6dfffffffffdbefeffefbf7bfefaefefdfff7fdffbfcdffbf7ffdfffdfdf27ffdfbfff7ffffbfdbdffed77bfffbfbf7f3ffefdffdf5dffb7dff7b7efefbbfbffd7fb7ffffffef7ddfef7fdf7fb7bffb7ffeefffbffff5f7ffbffedffcbf7feefbffffffffffd6ff7fdffff7ff7fff9bef7ffb7b77b7fb7dfffffff3ffffdfeff7faefffbfffaffbf9fff35fffdfffedffef36f779fdfefbfdfbfffff3fdeddfeff5feffedd7ffaebf5ffeb7fffd9f7fbf9f

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches123 : PLift ((OMA.PrimeProgression.composite primes 12 2103135 2823) = mask123) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified123 : PLift (rows123.all (check 2103135 2823 mask123 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct123 : ∀ r ∈ rows123, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified123.down r hr
  rw [←maskMatches123.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows124 : List Witness :=
  [(1830,2463,112)]

private def mask124 : ℕ := 0x1fff9b7bf6ffffffdfffe7ffcffff3ffbffaffbffe7feffbdffffffdefdfffefffff7db7fbffff7ffdbfeb7fd7cfedfffbfdfeffbeffddfdffeffffeff7ffe7ff6f7ffbefffffdffcbf7dedffffb7bfffe7feff7ffffffebf6bffd6fffcf7f9e7fbef7fbfff7ddfeffedefff4f7ddfff3fdffde7bfef7fb2edfffedffdfffdfefffbbfbfdfeffffff7fe7ffffffffdf25ffffbedffd7dfbf9bdbfedeff7ffe7dfffffffff6ffffffeffef7fbfdffdfbff7fdefbeef37ffcfffffff7efefdf6bffffffeffbffadfbffffbbfffffadffdf6fffef7fff6f7f9ffdfffbdde7fffbf7fbefe7dbffbedffd7fd3ffe5fffbeff7efeffffbbfffeffdffddfcffff7ffbdfbfffdf77f6f9fffffdfff75dffffdfffbffffffffffddf7fb6ffeffebeff75ffffffff6fefd37bffb3cfefbfdfbddffffff6fbfef7dffffbefffb3ff7fffeffefef9fefeffffffff7fbeffafdbdffddfffedff7fe6fbdf7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches124 : PLift ((OMA.PrimeProgression.composite primes 12 2253645 2745) = mask124) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified124 : PLift (rows124.all (check 2253645 2745 mask124 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct124 : ∀ r ∈ rows124, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified124.down r hr
  rw [←maskMatches124.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows125 : List Witness :=
  [(1789,2572,116)]

private def mask125 : ℕ := 0xadfbdff7feff279effbfbe79efffffefff6fff97ffffdbfffffffbeefeffbefbfbffdfefffdfff7dbfffbffaddf7ffefeeffefffffffffd7ffffdbf9edfffbf7fbffadfbffbf977dfcfefdbffb6fffbefdffbfff77de7fffffdbffbfcff7ffffbfbfeffed6fffddbfbbffbfbfedbddfffffb3effffadfffdbffb79efbbff37bffbbcffeffeffdbf7b7ffffdffffffe7bf7dfef3efe7ff7fffbefffcfffff5fb7deffffdfffffffdf6fffffffdbebfff6ff7dfa7fedbb5d6ff7ff77ff6ffddf7dbef7fdffffebfff7ffffbfff7dbffffdff5fefbffbf6fbeff7feff7fb77feff75ffff77dffdfef3fffffffffebffded9f6f74de7ffeffdbbffffbf7ffeffffacf7edfffeeffdffdff5fffdefdf7ff4f7effebbfff7dbfb7ff66ffffb7fa7ff6dfffbfff7fffbbcff7bbffbddffff7bffbfefffdfeffdfffd6ffffffebfdbfffbcfbfff6bf5ffedfffb7ffdffffeff7f

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches125 : PLift ((OMA.PrimeProgression.composite primes 12 2300654 2684) = mask125) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified125 : PLift (rows125.all (check 2300654 2684 mask125 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct125 : ∀ r ∈ rows125, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified125.down r hr
  rw [←maskMatches125.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows126 : List Witness :=
  [(1768,2784,116)]

private def mask126 : ℕ := 0xeffdfffffeff7ffddf79eff7ff66befdbdbfeff7fe6d7effffe7bffb7ebafffdfffff7dffffffe7ff7f37dffb7efe7dbebbffffbfedfd9f7f7dfffbfdfffde6fffd7fffdfffff5fbff7fdbff7ffe6bffffffbdf7fdedfff97fb7ffbfbfdffffefdbfff7ffdbfffe7dfff7dfffbf79fefffdffbbffbcbfebfeff7ffdffddf7fffdefdfefbdbefdfdfeffafff7ff6ffff7fbbfb7ffffb6ff75dbfff7ffff7ffffff6bf6fffffddffff6ffef7fbecdfdfe7bff9f7daddff9f6f7fbfffedfb7fffbffbeef7cffdffdffff7fbbfdfdffffffff7fbfdfddbfffdf7ef6efef9edfffff7ffdff7fefbfdff7f6cff7fffffdbe6feddffdfffbff6ed3ff6ddffbf7ffffbfffdfb5bffbffbbeffddf7f77ff7fbffedffff3ff6fdfdffffbdbf7dfedfffffff5fffbffffff37ffebbffee97ffff9bdff7d7fbeffffbf6ffeff7b6ffefbe7ff7b7fffddadfbef7dffff7fdb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches126 : PLift ((OMA.PrimeProgression.composite primes 12 2461056 2652) = mask126) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified126 : PLift (rows126.all (check 2461056 2652 mask126 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct126 : ∀ r ∈ rows126, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified126.down r hr
  rw [←maskMatches126.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows127 : List Witness :=
  [(1627,3276,109)]

private def mask127 : ℕ := 0x1bfd76dffd77fffbfdff6fadfefffef769eeffcf7f9ffffcffef7ef7fff7ffefffbfffffbffb77bf6f3ffbddb7f7ff6fdeedffffcfbffffdffff7ffefbdfffbaffbffffbfed7fffdff7fe5fbef7e97ffffffebffffffefdefffeff7b77faeffdff7f7fb7f9fdffffeffbfb77f7fdaffeff76beefefd3fdfeb7fdf6dfffafdf7fbffeef3fffffffffdbfffbefbdfeeff7b7fbbfffdfbef7dbf7ffcffffedbbffffd7ffefbeffffbffdbffe7fedffefffd3dffdbaff3cffffffdf7ffeff5ff7fbefbfdffbf6f76ffdff7dbff7ffefbeff3ffbebfdbefffdf6fdf5f7dbffdbff77fffffefffffff7dfbdf75fff9ffdfdffffbffffb7df7fff6ffeb7ebbefffdefffefeef6ffffbefbfd9fffbefbffefff6ff7fedff5fbff37df797ffffdfdffdfffdbefefffff35ff7dbcf7f9beb7fd7fffeff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches127 : PLift ((OMA.PrimeProgression.composite primes 12 2665026 2441) = mask127) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified127 : PLift (rows127.all (check 2665026 2441 mask127 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct127 : ∀ r ∈ rows127, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified127.down r hr
  rw [←maskMatches127.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows128 : List Witness :=
  [(1843,3125,117)]

private def mask128 : ℕ := 0x6ffafffeffeff6f7fdff9feffdf7ff7fdffbe7fbdf7ffbddf7bfff7dfffffff3ddfff3fffff7eff7deffbeffffffff5fbfb76de7f3fffddaff7fff7fecfbffaff7fbf7defffdbbfff7bffffcd6ffe7ffcfffdeffaffeeff6defdfffffbbffffdef97ff7fdbffffbffbfffffbfff77fffffefa5df7ffd9ffffefffbf7bffdfff7fdf7fffffeff7bbfdfffefff6defffdfbffffbfffeefbffff9ffbbf9fffbff7dfbeffdb7ffbffe79fdffcbeff6ddfffe7bfffeedfdfe7fffffff76bbff7dffebffbeff7ffffbefffff7effedff9fefffff7f6fffd9afff7d76f2fdfdfb7ffedeffeefb7fbffbdffedffdbfdf7ffffefbafdfdffcff7b67bfffeddfdbfffff9efdffff7fbfff7dfdf7f9fff7d9ffffdff7fe5fbefffffffb5fffff7dfff7fff7fefbbdf7efeffefffdffebef93dff7ffffffdfffbffeffb7f77ffffedd2fffeb75df7ffffeffb7ffff7fbfff3dbffff5ff7f7ddafffef76fe7fb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches128 : PLift ((OMA.PrimeProgression.composite primes 12 2879688 2764) = mask128) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified128 : PLift (rows128.all (check 2879688 2764 mask128 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct128 : ∀ r ∈ rows128, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified128.down r hr
  rw [←maskMatches128.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows129 : List Witness :=
  [(1829,3526,121)]

private def mask129 : ℕ := 0xfda7ffdffff3efffbbfbfe9ffdfffadffffffdfef7effffe7f7edf7f7edffbeeffdff7f7ff6fdffff7beffffffddfdfb6fffdfdfedfe7f7cfffffffffbfff75fefd7ffafbb7bffff7beffbfdffffdffef6fff7fe7ff7bffdbffb7df6b7db7efbffffdffff7f7fb7ef6fbefb76dfe9fedfddfeffefefdfff7fffffffdffffddfdff7f7efe6ffff3dfa7fbf9effbfff7dfff7fbf7fffff5feef3ffeff7ffffbf7bfeffef2effddfcfb6bfffefdffdefff7bfffbfffddfdffdffff7cfb7ffdfbfdfefbedfffe7bffff7dbdfb5ffef3ffeedfff2f9bfbbfd6f9affffffcfbfffffffd6f9ffb77d7effdffffedfbfd67d6ffbffeffffd77fbfdefffdf3effefaffbffefbf7fefffff35be5bbef7ffbff75bfdf7effff3ff3fbbfffdff7baffffffffff9769edfffff6bfffefdfddefbefff7fefbffffdfffffffffdfffff9adffcf6fb7fffffbeffddf7fffffdfb7ff7f7ff7cff7fb7fbe9eff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches129 : PLift ((OMA.PrimeProgression.composite primes 12 3224527 2744) = mask129) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified129 : PLift (rows129.all (check 3224527 2744 mask129 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct129 : ∀ r ∈ rows129, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified129.down r hr
  rw [←maskMatches129.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def rows130 : List Witness :=
  [(1785,3770,115)]

private def mask130 : ℕ := 0x2ffefff7fe7f7fff7fffbf6ffe97fdfffbff7fbef9fefafffff7f9f7ffffbfdf7f7ef77fffdffbadffddfffffdf7dedbf5f6fdffffdfffbbed6fbfdff7fb5bfef7ffefff7dfff7dbffd6fd7ffeffffffffbffffdfdfbfffff7ef7dbffff7fe6fbddbfdeeff6feffadfa7dedff7ffff7ffffdffbf5f6fbeed7fff6ffebf7f6fdffbffffddf6bfefbffadfbdf7effdf77bb7ffddf7ffffffffdfbeb7ffbfde7dffbfffffdbcfedbffbfef7fffeff7dffff7dffdfdfbffbfffdff6ffdffdfbdfbfff7d6ffffff6fb7befdbefe7fe7ffff77faff7dfffb7fffeffffafbfff36fffbffffffbeffffffd6ffefdafb74f77f3efb79efffcbffffff7fffefffbefffffbfdefb7ebffdffd7dfbef7efefffdfe7dbffffffffbff7dfbcbbfff79bddffffef7ef7fb7fff7ffdffefe6d7ffffbfffffffffbdfffbffbfdf7fbafffffffb3ffeedfcfafbffbfcfeffffdf5df5bf5df

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def maskMatches130 : PLift ((OMA.PrimeProgression.composite primes 12 3364725 2678) = mask130) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def verified130 : PLift (rows130.all (check 3364725 2678 mask130 rankMask) = true) :=
  ⟨by decide +kernel⟩

private theorem correct130 : ∀ r ∈ rows130, Witness.correct r := by
  intro r hr
  have checked := List.all_eq_true.mp verified130.down r hr
  rw [←maskMatches130.down,←rankMatches.down] at checked
  exact sound primes_prime primes_complete rankPrimes_prime rankPrimes_complete
    (by decide) (by decide) checked

private def tier0 : List Witness := (rows0 ++ (rows1 ++ (rows2 ++ (rows3 ++ (rows4 ++ (rows5 ++ (rows6 ++ (rows7 ++ (rows8 ++ (rows9 ++ (rows10 ++ rows11)))))))))))

set_option maxRecDepth 20000 in
private theorem tierOK0 : ∀ r ∈ tier0, Witness.correct r :=
  (append_correct correct0 (append_correct correct1 (append_correct correct2 (append_correct correct3 (append_correct correct4 (append_correct correct5 (append_correct correct6 (append_correct correct7 (append_correct correct8 (append_correct correct9 (append_correct correct10 correct11)))))))))))

private def tier1 : List Witness := (rows12 ++ (rows13 ++ (rows14 ++ (rows15 ++ (rows16 ++ (rows17 ++ (rows18 ++ (rows19 ++ (rows20 ++ (rows21 ++ (rows22 ++ rows23)))))))))))

set_option maxRecDepth 20000 in
private theorem tierOK1 : ∀ r ∈ tier1, Witness.correct r :=
  (append_correct correct12 (append_correct correct13 (append_correct correct14 (append_correct correct15 (append_correct correct16 (append_correct correct17 (append_correct correct18 (append_correct correct19 (append_correct correct20 (append_correct correct21 (append_correct correct22 correct23)))))))))))

private def tier2 : List Witness := (rows24 ++ (rows25 ++ (rows26 ++ (rows27 ++ (rows28 ++ (rows29 ++ (rows30 ++ (rows31 ++ (rows32 ++ (rows33 ++ (rows34 ++ rows35)))))))))))

set_option maxRecDepth 20000 in
private theorem tierOK2 : ∀ r ∈ tier2, Witness.correct r :=
  (append_correct correct24 (append_correct correct25 (append_correct correct26 (append_correct correct27 (append_correct correct28 (append_correct correct29 (append_correct correct30 (append_correct correct31 (append_correct correct32 (append_correct correct33 (append_correct correct34 correct35)))))))))))

private def tier3 : List Witness := (rows36 ++ (rows37 ++ (rows38 ++ (rows39 ++ (rows40 ++ (rows41 ++ (rows42 ++ (rows43 ++ (rows44 ++ (rows45 ++ (rows46 ++ rows47)))))))))))

set_option maxRecDepth 20000 in
private theorem tierOK3 : ∀ r ∈ tier3, Witness.correct r :=
  (append_correct correct36 (append_correct correct37 (append_correct correct38 (append_correct correct39 (append_correct correct40 (append_correct correct41 (append_correct correct42 (append_correct correct43 (append_correct correct44 (append_correct correct45 (append_correct correct46 correct47)))))))))))

private def tier4 : List Witness := (rows48 ++ (rows49 ++ (rows50 ++ (rows51 ++ (rows52 ++ (rows53 ++ (rows54 ++ (rows55 ++ (rows56 ++ (rows57 ++ (rows58 ++ rows59)))))))))))

set_option maxRecDepth 20000 in
private theorem tierOK4 : ∀ r ∈ tier4, Witness.correct r :=
  (append_correct correct48 (append_correct correct49 (append_correct correct50 (append_correct correct51 (append_correct correct52 (append_correct correct53 (append_correct correct54 (append_correct correct55 (append_correct correct56 (append_correct correct57 (append_correct correct58 correct59)))))))))))

private def tier5 : List Witness := (rows60 ++ (rows61 ++ (rows62 ++ (rows63 ++ (rows64 ++ (rows65 ++ (rows66 ++ (rows67 ++ (rows68 ++ (rows69 ++ (rows70 ++ rows71)))))))))))

set_option maxRecDepth 20000 in
private theorem tierOK5 : ∀ r ∈ tier5, Witness.correct r :=
  (append_correct correct60 (append_correct correct61 (append_correct correct62 (append_correct correct63 (append_correct correct64 (append_correct correct65 (append_correct correct66 (append_correct correct67 (append_correct correct68 (append_correct correct69 (append_correct correct70 correct71)))))))))))

private def tier6 : List Witness := (rows72 ++ (rows73 ++ (rows74 ++ (rows75 ++ (rows76 ++ (rows77 ++ (rows78 ++ (rows79 ++ (rows80 ++ (rows81 ++ (rows82 ++ rows83)))))))))))

set_option maxRecDepth 20000 in
private theorem tierOK6 : ∀ r ∈ tier6, Witness.correct r :=
  (append_correct correct72 (append_correct correct73 (append_correct correct74 (append_correct correct75 (append_correct correct76 (append_correct correct77 (append_correct correct78 (append_correct correct79 (append_correct correct80 (append_correct correct81 (append_correct correct82 correct83)))))))))))

private def tier7 : List Witness := (rows84 ++ (rows85 ++ (rows86 ++ (rows87 ++ (rows88 ++ (rows89 ++ (rows90 ++ (rows91 ++ (rows92 ++ (rows93 ++ (rows94 ++ rows95)))))))))))

set_option maxRecDepth 20000 in
private theorem tierOK7 : ∀ r ∈ tier7, Witness.correct r :=
  (append_correct correct84 (append_correct correct85 (append_correct correct86 (append_correct correct87 (append_correct correct88 (append_correct correct89 (append_correct correct90 (append_correct correct91 (append_correct correct92 (append_correct correct93 (append_correct correct94 correct95)))))))))))

private def tier8 : List Witness := (rows96 ++ (rows97 ++ (rows98 ++ (rows99 ++ (rows100 ++ (rows101 ++ (rows102 ++ (rows103 ++ (rows104 ++ (rows105 ++ (rows106 ++ rows107)))))))))))

set_option maxRecDepth 20000 in
private theorem tierOK8 : ∀ r ∈ tier8, Witness.correct r :=
  (append_correct correct96 (append_correct correct97 (append_correct correct98 (append_correct correct99 (append_correct correct100 (append_correct correct101 (append_correct correct102 (append_correct correct103 (append_correct correct104 (append_correct correct105 (append_correct correct106 correct107)))))))))))

private def tier9 : List Witness := (rows108 ++ (rows109 ++ (rows110 ++ (rows111 ++ (rows112 ++ (rows113 ++ (rows114 ++ (rows115 ++ (rows116 ++ (rows117 ++ (rows118 ++ rows119)))))))))))

set_option maxRecDepth 20000 in
private theorem tierOK9 : ∀ r ∈ tier9, Witness.correct r :=
  (append_correct correct108 (append_correct correct109 (append_correct correct110 (append_correct correct111 (append_correct correct112 (append_correct correct113 (append_correct correct114 (append_correct correct115 (append_correct correct116 (append_correct correct117 (append_correct correct118 correct119)))))))))))

private def tier10 : List Witness := (rows120 ++ (rows121 ++ (rows122 ++ (rows123 ++ (rows124 ++ (rows125 ++ (rows126 ++ (rows127 ++ (rows128 ++ (rows129 ++ rows130))))))))))

set_option maxRecDepth 20000 in
private theorem tierOK10 : ∀ r ∈ tier10, Witness.correct r :=
  (append_correct correct120 (append_correct correct121 (append_correct correct122 (append_correct correct123 (append_correct correct124 (append_correct correct125 (append_correct correct126 (append_correct correct127 (append_correct correct128 (append_correct correct129 correct130))))))))))

private def allRows : List Witness := (tier0 ++ (tier1 ++ (tier2 ++ (tier3 ++ (tier4 ++ (tier5 ++ (tier6 ++ (tier7 ++ (tier8 ++ (tier9 ++ tier10))))))))))

set_option maxRecDepth 20000 in
private theorem allCorrect : ∀ r ∈ allRows, Witness.correct r :=
  (append_correct tierOK0 (append_correct tierOK1 (append_correct tierOK2 (append_correct tierOK3 (append_correct tierOK4 (append_correct tierOK5 (append_correct tierOK6 (append_correct tierOK7 (append_correct tierOK8 (append_correct tierOK9 tierOK10))))))))))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private def coverage : PLift (rowBits allRows = ((1 <<< 1996)-1) <<< 5) := ⟨by decide +kernel⟩

private theorem intervalBit {start len n : ℕ} (hlo : start ≤ n) (hhi : n-start < len) :
    ((((1 : ℕ) <<< len)-1) <<< start).testBit n = true := by
  rw [Nat.testBit_shiftLeft]
  simp only [hlo,decide_true,Bool.true_and,Nat.shiftLeft_eq,Nat.one_mul]
  rw [Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hhi

theorem three_intervals (n : ℕ) (hn : 4<n) (hmax : n≤2000) :
    ∃ r ∈ allRows, r.1=n ∧ Witness.correct r := by
  have flag : (rowBits allRows).testBit n = true := by
    rw [coverage.down]
    exact intervalBit (by omega) (by omega)
  obtain ⟨r,hr,eq⟩ := rowBits_member.mp flag
  exact ⟨r,hr,eq,allCorrect r hr⟩

end OMA.PrimeIntervalTriple

theorem OMA.solution : OMA.R_OeisA238281_conjecture_3_R1.H1 := by
  intro n hn hmax
  obtain ⟨row, _, hn', proof⟩ := OMA.PrimeIntervalTriple.three_intervals n hn hmax
  obtain ⟨m,k,c⟩ := row
  change m=n at hn'
  subst m
  exact ⟨k,proof⟩