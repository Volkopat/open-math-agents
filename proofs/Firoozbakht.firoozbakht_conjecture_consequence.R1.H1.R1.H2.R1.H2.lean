import OMAReductions.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1
import Mathlib

/-! A bitmap for a bounded arithmetic progression. -/
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

theorem sliceOdd_lower {ps : List ℕ} {bound markDepth base width left span : ℕ}
    (complete : ∀ p ≤ bound, p.Prime → p%2=1 → p∈ps)
    (hw : width<2^markDepth) (cap : 2*(base+width)≤(bound+1)^2)
    (inside : left+span ≤ width) :
    sliceOdd (OMA.PrimeProgression.composite ps markDepth base width) left span ≤
      Nat.count (fun i => (2*(base+(left+i))+1).Prime) span := by
  let word := OMA.PrimeProgression.composite ps markDepth base width
  unfold sliceOdd
  rw [prefixPop_exact (depth_bound span), card_eq, Nat.count_eq_card_filter_range]
  have all := Finset.card_filter_add_card_filter_not (s:=Finset.range span) (fun i => (word >>> left).testBit i = true)
  rw [Finset.card_range] at all
  have decomp : span-((Finset.range span).filter fun i => (word >>> left).testBit i = true).card =
      ((Finset.range span).filter fun i => ¬(word >>> left).testBit i = true).card := by omega
  rw [show OMA.PrimeProgression.composite ps markDepth base width = word from rfl, decomp]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hin,hzero⟩ := Finset.mem_filter.mp hi
  have hlt := Finset.mem_range.mp hin
  rw [Nat.testBit_shiftRight] at hzero
  exact Finset.mem_filter.mpr ⟨hin,OMA.PrimeProgression.unmarked_prime complete hw
    (by omega : left+i<width) (by omega) (Bool.eq_false_iff.mpr hzero)⟩

def checkRows (base width word : ℕ) : ℕ → ℕ → List Row → Bool
  | _, _, [] => true
  | left, count, row::rest =>
      let n := row.1
      let slots := (n+1)/2
      let span := slots-(base+left)
      let delta := sliceOdd word left span
      (decide (2≤n ∧ base+left ≤ slots ∧ slots ≤ base+width ∧ row.2.2.1 ≤ 1+count+delta)) &&
        checkRows base width word (slots-base) (row.2.2.1-1) rest

theorem checkRows_counts {ps : List ℕ} {bound markDepth base width : ℕ}
    (complete : ∀ p ≤ bound, p.Prime → p%2=1 → p∈ps)
    (hw : width<2^markDepth) (cap : 2*(base+width)≤(bound+1)^2) (rows : List Row)
    {left count : ℕ} (start : count ≤ oddCount (base+left))
    (check : checkRows base width (OMA.PrimeProgression.composite ps markDepth base width)
      left count rows = true) :
    ∀ row ∈ rows, 2≤row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) := by
  induction rows generalizing left count with
  | nil => simp
  | cons r rows ih =>
    let word := OMA.PrimeProgression.composite ps markDepth base width
    let slots := (r.1+1)/2
    let span := slots-(base+left)
    simp only [checkRows, Bool.and_eq_true, decide_eq_true_eq] at check
    obtain ⟨⟨hn, hleft, hend, hcount⟩,hrest⟩ := check
    change base+left ≤ slots at hleft
    change slots ≤ base+width at hend
    have inside : left+span ≤ width := by dsimp [span]; omega
    have hdelta := sliceOdd_lower complete hw cap inside
    have slotsEq : (base+left)+span = slots := by dsimp [span]; omega
    have hc : count+sliceOdd word left span ≤ oddCount slots := by
      rw [← slotsEq, oddCount, Nat.count_add]
      exact Nat.add_le_add start (by simpa only [Nat.add_assoc] using hdelta)
    change r.2.2.1 ≤ 1+count+sliceOdd word left span at hcount
    have hl : r.2.2.1 ≤ 1+oddCount slots := by omega
    have next : r.2.2.1-1 ≤ oddCount (base+(slots-base)) := by
      have heq : base+(slots-base)=slots := by omega
      rw [heq]
      omega
    intro row hrow
    rcases List.mem_cons.mp hrow with rfl|hm
    · exact ⟨hn,hl⟩
    · exact ih next hrest row hm

theorem checkRows_sound {ps : List ℕ} {bound markDepth base width : ℕ}
    (complete : ∀ p ≤ bound, p.Prime → p%2=1 → p∈ps)
    (hw : width<2^markDepth) (cap : 2*(base+width)≤(bound+1)^2) (rows : List Row)
    {left count : ℕ} (start : count ≤ oddCount (base+left))
    (check : checkRows base width (OMA.PrimeProgression.composite ps markDepth base width)
      left count rows = true) :
    ∀ row ∈ rows, row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have h := checkRows_counts complete hw cap rows start check row hr
  exact h.2.trans (oddCount_le_primeCounting h.1 (le_refl _))

end OMA.PrimePopulation

open OMA.PrimePopulation OMA.PrimeProgression

private def basePrimes : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347]

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def rosterEquality : PLift (OMA.PrimeSieveBase.smallPrimes 5349 73 = basePrimes) :=
  ⟨by decide +kernel⟩

private theorem baseComplete : ∀ p ≤ 5349, p.Prime → p%2=1 → p∈basePrimes := by
  intro p hp prime odd
  rw [← rosterEquality.down]
  exact OMA.PrimeSieveBase.mem_smallPrimes hp prime odd

private theorem bounds_from_counts {rows : List Row}
    (h : ∀ row ∈ rows, 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2)) :
    ∀ row ∈ rows, row.2.2.1 ≤ row.1.primeCounting := by
  intro row hr
  have hrow := h row hr
  exact hrow.2.trans (oddCount_le_primeCounting hrow.1 (le_refl _))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem dispatchMiddle
    (check35 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk035_data), row.2.2.1 ≤ row.1.primeCounting)
    (check36 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk036_data), row.2.2.1 ≤ row.1.primeCounting)
    (check37 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk037_data), row.2.2.1 ≤ row.1.primeCounting)
    (check38 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk038_data), row.2.2.1 ≤ row.1.primeCounting)
    (check39 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk039_data), row.2.2.1 ≤ row.1.primeCounting)
    (check40 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk040_data), row.2.2.1 ≤ row.1.primeCounting)
    (check41 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk041_data), row.2.2.1 ≤ row.1.primeCounting)
    (check42 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk042_data), row.2.2.1 ≤ row.1.primeCounting)
    (check43 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk043_data), row.2.2.1 ≤ row.1.primeCounting)
    (check44 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk044_data), row.2.2.1 ≤ row.1.primeCounting)
    (check45 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk045_data), row.2.2.1 ≤ row.1.primeCounting)
    (check46 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk046_data), row.2.2.1 ≤ row.1.primeCounting)
    (check47 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk047_data), row.2.2.1 ≤ row.1.primeCounting)
    (check48 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk048_data), row.2.2.1 ≤ row.1.primeCounting)
    (check49 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk049_data), row.2.2.1 ≤ row.1.primeCounting)
    (check50 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk050_data), row.2.2.1 ≤ row.1.primeCounting)
    (check51 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk051_data), row.2.2.1 ≤ row.1.primeCounting)
    (check52 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk052_data), row.2.2.1 ≤ row.1.primeCounting)
    (check53 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk053_data), row.2.2.1 ≤ row.1.primeCounting)
    (check54 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk054_data), row.2.2.1 ≤ row.1.primeCounting)
    (check55 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk055_data), row.2.2.1 ≤ row.1.primeCounting)
    (check56 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk056_data), row.2.2.1 ≤ row.1.primeCounting)
    (check57 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk057_data), row.2.2.1 ≤ row.1.primeCounting)
    (check58 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk058_data), row.2.2.1 ≤ row.1.primeCounting)
    (check59 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk059_data), row.2.2.1 ≤ row.1.primeCounting)
    (check60 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk060_data), row.2.2.1 ≤ row.1.primeCounting)
    (check61 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk061_data), row.2.2.1 ≤ row.1.primeCounting)
    (check62 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk062_data), row.2.2.1 ≤ row.1.primeCounting)
    (check63 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk063_data), row.2.2.1 ≤ row.1.primeCounting)
    (check64 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk064_data), row.2.2.1 ≤ row.1.primeCounting)
    (check65 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk065_data), row.2.2.1 ≤ row.1.primeCounting)
    (check66 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk066_data), row.2.2.1 ≤ row.1.primeCounting)
    (check67 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk067_data), row.2.2.1 ≤ row.1.primeCounting)
    (check68 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk068_data), row.2.2.1 ≤ row.1.primeCounting)
    (check69 : ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk069_data), row.2.2.1 ≤ row.1.primeCounting) : OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.H2 := by
  unfold OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.H2
  rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.middleRows_data]
  exact List.forall_mem_append.mpr ⟨check35,List.forall_mem_append.mpr ⟨check36,List.forall_mem_append.mpr ⟨check37,List.forall_mem_append.mpr ⟨check38,List.forall_mem_append.mpr ⟨check39,List.forall_mem_append.mpr ⟨check40,List.forall_mem_append.mpr ⟨check41,List.forall_mem_append.mpr ⟨check42,List.forall_mem_append.mpr ⟨check43,List.forall_mem_append.mpr ⟨check44,List.forall_mem_append.mpr ⟨check45,List.forall_mem_append.mpr ⟨check46,List.forall_mem_append.mpr ⟨check47,List.forall_mem_append.mpr ⟨check48,List.forall_mem_append.mpr ⟨check49,List.forall_mem_append.mpr ⟨check50,List.forall_mem_append.mpr ⟨check51,List.forall_mem_append.mpr ⟨check52,List.forall_mem_append.mpr ⟨check53,List.forall_mem_append.mpr ⟨check54,List.forall_mem_append.mpr ⟨check55,List.forall_mem_append.mpr ⟨check56,List.forall_mem_append.mpr ⟨check57,List.forall_mem_append.mpr ⟨check58,List.forall_mem_append.mpr ⟨check59,List.forall_mem_append.mpr ⟨check60,List.forall_mem_append.mpr ⟨check61,List.forall_mem_append.mpr ⟨check62,List.forall_mem_append.mpr ⟨check63,List.forall_mem_append.mpr ⟨check64,List.forall_mem_append.mpr ⟨check65,List.forall_mem_append.mpr ⟨check66,List.forall_mem_append.mpr ⟨check67,List.forall_mem_append.mpr ⟨check68,check69⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate00 : PLift (checkedSegment basePrimes 20 13 0 262144 = 43389) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state00 : 43389 ≤ oddCount 262144 := by
  have h := checkedSegment_add baseComplete (markDepth := 20) (popDepth := 13)
    (base := 0) (width := 262144) (current := 0) (by decide) (by decide) (by decide) (Nat.zero_le (oddCount 0))
  rw [gate00.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate01 : PLift (checkedSegment basePrimes 20 13 262144 262144 = 38635) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state01 : 82024 ≤ oddCount 524288 := by
  have h := checkedSegment_add baseComplete (markDepth := 20) (popDepth := 13)
    (base := 262144) (width := 262144) (current := 43389) (by decide) (by decide) (by decide) state00
  rw [gate01.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate02 : PLift (checkedSegment basePrimes 20 13 524288 262144 = 37243) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state02 : 119267 ≤ oddCount 786432 := by
  have h := checkedSegment_add baseComplete (markDepth := 20) (popDepth := 13)
    (base := 524288) (width := 262144) (current := 82024) (by decide) (by decide) (by decide) state01
  rw [gate02.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate03 : PLift (checkedSegment basePrimes 20 13 786432 262144 = 36343) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state03 : 155610 ≤ oddCount 1048576 := by
  have h := checkedSegment_add baseComplete (markDepth := 20) (popDepth := 13)
    (base := 786432) (width := 262144) (current := 119267) (by decide) (by decide) (by decide) state02
  rw [gate03.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate04 : PLift (checkedSegment basePrimes 20 13 1048576 262144 = 35697) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state04 : 191307 ≤ oddCount 1310720 := by
  have h := checkedSegment_add baseComplete (markDepth := 20) (popDepth := 13)
    (base := 1048576) (width := 262144) (current := 155610) (by decide) (by decide) (by decide) state03
  rw [gate04.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate05 : PLift (checkedSegment basePrimes 20 13 1310720 262144 = 35241) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state05 : 226548 ≤ oddCount 1572864 := by
  have h := checkedSegment_add baseComplete (markDepth := 20) (popDepth := 13)
    (base := 1310720) (width := 262144) (current := 191307) (by decide) (by decide) (by decide) state04
  rw [gate05.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate06 : PLift (checkedSegment basePrimes 20 13 1572864 262144 = 34829) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state06 : 261377 ≤ oddCount 1835008 := by
  have h := checkedSegment_add baseComplete (markDepth := 20) (popDepth := 13)
    (base := 1572864) (width := 262144) (current := 226548) (by decide) (by decide) (by decide) state05
  rw [gate06.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate07 : PLift (checkedSegment basePrimes 20 13 1835008 262144 = 34569) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state07 : 295946 ≤ oddCount 2097152 := by
  have h := checkedSegment_add baseComplete (markDepth := 20) (popDepth := 13)
    (base := 1835008) (width := 262144) (current := 261377) (by decide) (by decide) (by decide) state06
  rw [gate07.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate08 : PLift (checkedSegment basePrimes 20 13 2097152 262144 = 34230) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state08 : 330176 ≤ oddCount 2359296 := by
  have h := checkedSegment_add baseComplete (markDepth := 20) (popDepth := 13)
    (base := 2097152) (width := 262144) (current := 295946) (by decide) (by decide) (by decide) state07
  rw [gate08.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate09 : PLift (checkedSegment basePrimes 20 13 2359296 262144 = 34018) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state09 : 364194 ≤ oddCount 2621440 := by
  have h := checkedSegment_add baseComplete (markDepth := 20) (popDepth := 13)
    (base := 2359296) (width := 262144) (current := 330176) (by decide) (by decide) (by decide) state08
  rw [gate09.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate10 : PLift (checkedSegment basePrimes 20 13 2621440 262144 = 33711) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state10 : 397905 ≤ oddCount 2883584 := by
  have h := checkedSegment_add baseComplete (markDepth := 20) (popDepth := 13)
    (base := 2621440) (width := 262144) (current := 364194) (by decide) (by decide) (by decide) state09
  rw [gate10.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate11 : PLift (checkedSegment basePrimes 20 13 2883584 262144 = 33596) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state11 : 431501 ≤ oddCount 3145728 := by
  have h := checkedSegment_add baseComplete (markDepth := 20) (popDepth := 13)
    (base := 2883584) (width := 262144) (current := 397905) (by decide) (by decide) (by decide) state10
  rw [gate11.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate12 : PLift (checkedSegment basePrimes 20 13 3145728 262144 = 33379) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state12 : 464880 ≤ oddCount 3407872 := by
  have h := checkedSegment_add baseComplete (markDepth := 20) (popDepth := 13)
    (base := 3145728) (width := 262144) (current := 431501) (by decide) (by decide) (by decide) state11
  rw [gate12.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate13 : PLift (checkedSegment basePrimes 20 13 3407872 245995 = 31270) :=
  ⟨by
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state13 : 496150 ≤ oddCount 3653867 := by
  have h := checkedSegment_add baseComplete (markDepth := 20) (popDepth := 13)
    (base := 3407872) (width := 245995) (current := 464880) (by decide) (by decide) (by decide) state12
  rw [gate13.down] at h
  exact h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate14 : PLift (checkRows 3653867 159053 (composite basePrimes 20 3653867 159053) 0 496150 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk035_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk035_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts35 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk035_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 3653867) (width := 159053)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk035_data) (left := 0) (count := 496150) state13 gate14.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked35 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk035_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts35

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state14 : 516211 ≤ oddCount 3812920 := by
  let row : Row := (7625840, 7630540, 516212, 5852)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk035_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk035_data]
    decide
  have h := (counts35 row mem).2
  have slot : (row.1+1)/2 = 3812920 := by decide
  have value : row.2.2.1 = 516212 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate15 : PLift (checkRows 3812920 164757 (composite basePrimes 20 3812920 164757) 0 516211 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk036_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk036_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts36 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk036_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 3812920) (width := 164757)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk036_data) (left := 0) (count := 516211) state14 gate15.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked36 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk036_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts36

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state15 : 536974 ≤ oddCount 3977677 := by
  let row : Row := (7955354, 7960809, 536975, 5868)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk036_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk036_data]
    decide
  have h := (counts36 row mem).2
  have slot : (row.1+1)/2 = 3977677 := by decide
  have value : row.2.2.1 = 536975 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate16 : PLift (checkRows 3977677 160428 (composite basePrimes 20 3977677 160428) 0 536974 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk037_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk037_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts37 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk037_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 3977677) (width := 160428)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk037_data) (left := 0) (count := 536974) state15 gate16.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked37 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk037_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts37

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state16 : 557108 ≤ oddCount 4138105 := by
  let row : Row := (8276209, 8282017, 557109, 5883)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk037_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk037_data]
    decide
  have h := (counts37 row mem).2
  have slot : (row.1+1)/2 = 4138105 := by decide
  have value : row.2.2.1 = 557109 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate17 : PLift (checkRows 4138105 164044 (composite basePrimes 20 4138105 164044) 0 557108 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk038_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk038_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts38 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk038_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 4138105) (width := 164044)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk038_data) (left := 0) (count := 557108) state16 gate17.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked38 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk038_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts38

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state17 : 577711 ≤ oddCount 4302149 := by
  let row : Row := (8604298, 8610288, 577712, 5897)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk038_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk038_data]
    decide
  have h := (counts38 row mem).2
  have slot : (row.1+1)/2 = 4302149 := by decide
  have value : row.2.2.1 = 577712 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate18 : PLift (checkRows 4302149 197426 (composite basePrimes 20 4302149 197426) 0 577711 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk039_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk039_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts39 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk039_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 4302149) (width := 197426)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk039_data) (left := 0) (count := 577711) state17 gate18.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked39 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk039_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts39

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state18 : 602431 ≤ oddCount 4499575 := by
  let row : Row := (8999150, 9004918, 602432, 5913)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk039_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk039_data]
    decide
  have h := (counts39 row mem).2
  have slot : (row.1+1)/2 = 4499575 := by decide
  have value : row.2.2.1 = 602432 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate19 : PLift (checkRows 4499575 188777 (composite basePrimes 20 4499575 188777) 0 602431 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk040_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk040_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts40 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk040_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 4499575) (width := 188777)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk040_data) (left := 0) (count := 602431) state18 gate19.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked40 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk040_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts40

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state19 : 625965 ≤ oddCount 4688352 := by
  let row : Row := (9376703, 9383919, 625966, 5929)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk040_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk040_data]
    decide
  have h := (counts40 row mem).2
  have slot : (row.1+1)/2 = 4688352 := by decide
  have value : row.2.2.1 = 625966 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate20 : PLift (checkRows 4688352 200224 (composite basePrimes 20 4688352 200224) 0 625965 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk041_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk041_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts41 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk041_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 4688352) (width := 200224)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk041_data) (left := 0) (count := 625965) state19 gate20.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked41 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk041_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts41

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state20 : 650830 ≤ oddCount 4888576 := by
  let row : Row := (9777151, 9783208, 650831, 5944)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk041_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk041_data]
    decide
  have h := (counts41 row mem).2
  have slot : (row.1+1)/2 = 4888576 := by decide
  have value : row.2.2.1 = 650831 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate21 : PLift (checkRows 4888576 182511 (composite basePrimes 20 4888576 182511) 0 650830 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk042_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk042_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts42 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk042_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 4888576) (width := 182511)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk042_data) (left := 0) (count := 650830) state20 gate21.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked42 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk042_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts42

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state21 : 673433 ≤ oddCount 5071087 := by
  let row : Row := (10142174, 10148599, 673434, 5958)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk042_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk042_data]
    decide
  have h := (counts42 row mem).2
  have slot : (row.1+1)/2 = 5071087 := by decide
  have value : row.2.2.1 = 673434 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate22 : PLift (checkRows 5071087 173784 (composite basePrimes 20 5071087 173784) 0 673433 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk043_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk043_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts43 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk043_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 5071087) (width := 173784)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk043_data) (left := 0) (count := 673433) state21 gate22.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked43 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk043_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts43

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state22 : 694969 ≤ oddCount 5244871 := by
  let row : Row := (10489742, 10495812, 694970, 5970)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk043_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk043_data]
    decide
  have h := (counts43 row mem).2
  have slot : (row.1+1)/2 = 5244871 := by decide
  have value : row.2.2.1 = 694970 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate23 : PLift (checkRows 5244871 209300 (composite basePrimes 20 5244871 209300) 0 694969 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk044_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk044_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts44 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk044_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 5244871) (width := 209300)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk044_data) (left := 0) (count := 694969) state22 gate23.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked44 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk044_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts44

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state23 : 720855 ≤ oddCount 5454171 := by
  let row : Row := (10908342, 10916145, 720856, 5985)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk044_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk044_data]
    decide
  have h := (counts44 row mem).2
  have slot : (row.1+1)/2 = 5454171 := by decide
  have value : row.2.2.1 = 720856 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate24 : PLift (checkRows 5454171 230505 (composite basePrimes 20 5454171 230505) 0 720855 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk045_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk045_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts45 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk045_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 5454171) (width := 230505)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk045_data) (left := 0) (count := 720855) state23 gate24.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked45 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk045_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts45

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state24 : 749252 ≤ oddCount 5684676 := by
  let row : Row := (11369352, 11376715, 749253, 6000)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk045_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk045_data]
    decide
  have h := (counts45 row mem).2
  have slot : (row.1+1)/2 = 5684676 := by decide
  have value : row.2.2.1 = 749253 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate25 : PLift (checkRows 5684676 236518 (composite basePrimes 20 5684676 236518) 0 749252 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk046_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk046_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts46 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk046_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 5684676) (width := 236518)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk046_data) (left := 0) (count := 749252) state24 gate25.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked46 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk046_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts46

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state25 : 778351 ≤ oddCount 5921194 := by
  let row : Row := (11842388, 11850288, 778352, 6015)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk046_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk046_data]
    decide
  have h := (counts46 row mem).2
  have slot : (row.1+1)/2 = 5921194 := by decide
  have value : row.2.2.1 = 778352 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate26 : PLift (checkRows 5921194 257761 (composite basePrimes 20 5921194 257761) 0 778351 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk047_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk047_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts47 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk047_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 5921194) (width := 257761)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk047_data) (left := 0) (count := 778351) state25 gate26.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked47 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk047_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts47

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state26 : 809989 ≤ oddCount 6178955 := by
  let row : Row := (12357910, 12367194, 809990, 6031)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk047_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk047_data]
    decide
  have h := (counts47 row mem).2
  have slot : (row.1+1)/2 = 6178955 := by decide
  have value : row.2.2.1 = 809990 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate27 : PLift (checkRows 6178955 288518 (composite basePrimes 20 6178955 288518) 0 809989 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk048_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk048_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts48 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk048_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 6178955) (width := 288518)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk048_data) (left := 0) (count := 809989) state26 gate27.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked48 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk048_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts48

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state27 : 845298 ≤ oddCount 6467473 := by
  let row : Row := (12934946, 12943060, 845299, 6047)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk048_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk048_data]
    decide
  have h := (counts48 row mem).2
  have slot : (row.1+1)/2 = 6467473 := by decide
  have value : row.2.2.1 = 845299 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate28 : PLift (checkRows 6467473 262568 (composite basePrimes 20 6467473 262568) 0 845298 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk049_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk049_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts49 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk049_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 6467473) (width := 262568)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk049_data) (left := 0) (count := 845298) state27 gate28.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked49 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk049_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts49

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state28 : 877222 ≤ oddCount 6730041 := by
  let row : Row := (13460082, 13467635, 877223, 6062)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk049_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk049_data]
    decide
  have h := (counts49 row mem).2
  have slot : (row.1+1)/2 = 6730041 := by decide
  have value : row.2.2.1 = 877223 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate29 : PLift (checkRows 6730041 259512 (composite basePrimes 20 6730041 259512) 0 877222 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk050_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk050_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts50 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk050_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 6730041) (width := 259512)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk050_data) (left := 0) (count := 877222) state28 gate29.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked50 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk050_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts50

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state29 : 908819 ≤ oddCount 6989553 := by
  let row : Row := (13979106, 13987308, 908820, 6076)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk050_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk050_data]
    decide
  have h := (counts50 row mem).2
  have slot : (row.1+1)/2 = 6989553 := by decide
  have value : row.2.2.1 = 908820 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate30 : PLift (checkRows 6989553 275562 (composite basePrimes 20 6989553 275562) 0 908819 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk051_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk051_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts51 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk051_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 6989553) (width := 275562)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk051_data) (left := 0) (count := 908819) state29 gate30.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked51 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk051_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts51

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state30 : 942288 ≤ oddCount 7265115 := by
  let row : Row := (14530230, 14538267, 942289, 6090)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk051_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk051_data]
    decide
  have h := (counts51 row mem).2
  have slot : (row.1+1)/2 = 7265115 := by decide
  have value : row.2.2.1 = 942289 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate31 : PLift (checkRows 7265115 289485 (composite basePrimes 20 7265115 289485) 0 942288 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk052_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk052_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts52 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk052_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 7265115) (width := 289485)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk052_data) (left := 0) (count := 942288) state30 gate31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked52 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk052_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts52

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state31 : 977303 ≤ oddCount 7554600 := by
  let row : Row := (15109199, 15118340, 977304, 6105)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk052_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk052_data]
    decide
  have h := (counts52 row mem).2
  have slot : (row.1+1)/2 = 7554600 := by decide
  have value : row.2.2.1 = 977304 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate32 : PLift (checkRows 7554600 269840 (composite basePrimes 20 7554600 269840) 0 977303 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk053_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk053_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts53 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk053_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 7554600) (width := 269840)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk053_data) (left := 0) (count := 977303) state31 gate32.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked53 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk053_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts53

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state32 : 1009918 ≤ oddCount 7824440 := by
  let row : Row := (15648880, 15658554, 1009919, 6118)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk053_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk053_data]
    decide
  have h := (counts53 row mem).2
  have slot : (row.1+1)/2 = 7824440 := by decide
  have value : row.2.2.1 = 1009919 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate33 : PLift (checkRows 7824440 295343 (composite basePrimes 20 7824440 295343) 0 1009918 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk054_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk054_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts54 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk054_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 7824440) (width := 295343)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk054_data) (left := 0) (count := 1009918) state32 gate33.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked54 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk054_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts54

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state33 : 1045539 ≤ oddCount 8119783 := by
  let row : Row := (16239565, 16247785, 1045540, 6131)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk054_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk054_data]
    decide
  have h := (counts54 row mem).2
  have slot : (row.1+1)/2 = 8119783 := by decide
  have value : row.2.2.1 = 1045540 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate34 : PLift (checkRows 8119783 291783 (composite basePrimes 20 8119783 291783) 0 1045539 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk055_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk055_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts55 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk055_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 8119783) (width := 291783)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk055_data) (left := 0) (count := 1045539) state33 gate34.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked55 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk055_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts55

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state34 : 1080660 ≤ oddCount 8411566 := by
  let row : Row := (16823132, 16834680, 1080661, 6145)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk055_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk055_data]
    decide
  have h := (counts55 row mem).2
  have slot : (row.1+1)/2 = 8411566 := by decide
  have value : row.2.2.1 = 1080661 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate35 : PLift (checkRows 8411566 335914 (composite basePrimes 20 8411566 335914) 0 1080660 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk056_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk056_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts56 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk056_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 8411566) (width := 335914)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk056_data) (left := 0) (count := 1080660) state34 gate35.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked56 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk056_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts56

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state35 : 1121073 ≤ oddCount 8747480 := by
  let row : Row := (17494959, 17506889, 1121074, 6159)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk056_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk056_data]
    decide
  have h := (counts56 row mem).2
  have slot : (row.1+1)/2 = 8747480 := by decide
  have value : row.2.2.1 = 1121074 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate36 : PLift (checkRows 8747480 374291 (composite basePrimes 20 8747480 374291) 0 1121073 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk057_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk057_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts57 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk057_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 8747480) (width := 374291)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk057_data) (left := 0) (count := 1121073) state35 gate36.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked57 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk057_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts57

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state36 : 1165872 ≤ oddCount 9121771 := by
  let row : Row := (18243541, 18253998, 1165873, 6174)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk057_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk057_data]
    decide
  have h := (counts57 row mem).2
  have slot : (row.1+1)/2 = 9121771 := by decide
  have value : row.2.2.1 = 1165873 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate37 : PLift (checkRows 9121771 379597 (composite basePrimes 20 9121771 379597) 0 1165872 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk058_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk058_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts58 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk058_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 9121771) (width := 379597)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk058_data) (left := 0) (count := 1165872) state36 gate37.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked58 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk058_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts58

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state37 : 1211203 ≤ oddCount 9501368 := by
  let row : Row := (19002735, 19016402, 1211204, 6190)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk058_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk058_data]
    decide
  have h := (counts58 row mem).2
  have slot : (row.1+1)/2 = 9501368 := by decide
  have value : row.2.2.1 = 1211204 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate38 : PLift (checkRows 9501368 375472 (composite basePrimes 20 9501368 375472) 0 1211203 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk059_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk059_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts59 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk059_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 9501368) (width := 375472)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk059_data) (left := 0) (count := 1211203) state37 gate38.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked59 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk059_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts59

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state38 : 1255898 ≤ oddCount 9876840 := by
  let row : Row := (19753680, 19765907, 1255899, 6204)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk059_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk059_data]
    decide
  have h := (counts59 row mem).2
  have slot : (row.1+1)/2 = 9876840 := by decide
  have value : row.2.2.1 = 1255899 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate39 : PLift (checkRows 9876840 393800 (composite basePrimes 20 9876840 393800) 0 1255898 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk060_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk060_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts60 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk060_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 9876840) (width := 393800)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk060_data) (left := 0) (count := 1255898) state38 gate39.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked60 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk060_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts60

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state39 : 1302704 ≤ oddCount 10270640 := by
  let row : Row := (20541280, 20552117, 1302705, 6218)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk060_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk060_data]
    decide
  have h := (counts60 row mem).2
  have slot : (row.1+1)/2 = 10270640 := by decide
  have value : row.2.2.1 = 1302705 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate40 : PLift (checkRows 10270640 393267 (composite basePrimes 20 10270640 393267) 0 1302704 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk061_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk061_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts61 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk061_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 10270640) (width := 393267)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk061_data) (left := 0) (count := 1302704) state39 gate40.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked61 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk061_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts61

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state40 : 1349378 ≤ oddCount 10663907 := by
  let row : Row := (21327813, 21339799, 1349379, 6232)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk061_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk061_data]
    decide
  have h := (counts61 row mem).2
  have slot : (row.1+1)/2 = 10663907 := by decide
  have value : row.2.2.1 = 1349379 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate41 : PLift (checkRows 10663907 422741 (composite basePrimes 20 10663907 422741) 0 1349378 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk062_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk062_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts62 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk062_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 10663907) (width := 422741)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk062_data) (left := 0) (count := 1349378) state40 gate41.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked62 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk062_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts62

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state41 : 1399459 ≤ oddCount 11086648 := by
  let row : Row := (22173296, 22185041, 1399460, 6246)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk062_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk062_data]
    decide
  have h := (counts62 row mem).2
  have slot : (row.1+1)/2 = 11086648 := by decide
  have value : row.2.2.1 = 1399460 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate42 : PLift (checkRows 11086648 402564 (composite basePrimes 20 11086648 402564) 0 1399459 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk063_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk063_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts63 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk063_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 11086648) (width := 402564)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk063_data) (left := 0) (count := 1399459) state41 gate42.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked63 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk063_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts63

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state42 : 1446944 ≤ oddCount 11489212 := by
  let row : Row := (22978424, 22992841, 1446945, 6260)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk063_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk063_data]
    decide
  have h := (counts63 row mem).2
  have slot : (row.1+1)/2 = 11489212 := by decide
  have value : row.2.2.1 = 1446945 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate43 : PLift (checkRows 11489212 436270 (composite basePrimes 20 11489212 436270) 0 1446944 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk064_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk064_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts64 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk064_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 11489212) (width := 436270)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk064_data) (left := 0) (count := 1446944) state42 gate43.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked64 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk064_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts64

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state43 : 1498311 ≤ oddCount 11925482 := by
  let row : Row := (23850964, 23862016, 1498312, 6273)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk064_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk064_data]
    decide
  have h := (counts64 row mem).2
  have slot : (row.1+1)/2 = 11925482 := by decide
  have value : row.2.2.1 = 1498312 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate44 : PLift (checkRows 11925482 454570 (composite basePrimes 20 11925482 454570) 0 1498311 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk065_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk065_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts65 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk065_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 11925482) (width := 454570)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk065_data) (left := 0) (count := 1498311) state43 gate44.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked65 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk065_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts65

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state44 : 1551889 ≤ oddCount 12380052 := by
  let row : Row := (24760103, 24774326, 1551890, 6287)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk065_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk065_data]
    decide
  have h := (counts65 row mem).2
  have slot : (row.1+1)/2 = 12380052 := by decide
  have value : row.2.2.1 = 1551890 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate45 : PLift (checkRows 12380052 453475 (composite basePrimes 20 12380052 453475) 0 1551889 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk066_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk066_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts66 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk066_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 12380052) (width := 453475)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk066_data) (left := 0) (count := 1551889) state44 gate45.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked66 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk066_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts66

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state45 : 1604957 ≤ oddCount 12833527 := by
  let row : Row := (25667054, 25682550, 1604958, 6301)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk066_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk066_data]
    decide
  have h := (counts66 row mem).2
  have slot : (row.1+1)/2 = 12833527 := by decide
  have value : row.2.2.1 = 1604958 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate46 : PLift (checkRows 12833527 458243 (composite basePrimes 20 12833527 458243) 0 1604957 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk067_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk067_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts67 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk067_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 12833527) (width := 458243)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk067_data) (left := 0) (count := 1604957) state45 gate46.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked67 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk067_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts67

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state46 : 1658716 ≤ oddCount 13291770 := by
  let row : Row := (26583540, 26596880, 1658717, 6313)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk067_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk067_data]
    decide
  have h := (counts67 row mem).2
  have slot : (row.1+1)/2 = 13291770 := by decide
  have value : row.2.2.1 = 1658717 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate47 : PLift (checkRows 13291770 491465 (composite basePrimes 20 13291770 491465) 0 1658716 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk068_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk068_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts68 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk068_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 13291770) (width := 491465)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk068_data) (left := 0) (count := 1658716) state46 gate47.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked68 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk068_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts68

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state47 : 1716124 ≤ oddCount 13783235 := by
  let row : Row := (27566469, 27582669, 1716125, 6327)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk068_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk068_data]
    decide
  have h := (counts68 row mem).2
  have slot : (row.1+1)/2 = 13783235 := by decide
  have value : row.2.2.1 = 1716125 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def gate48 : PLift (checkRows 13783235 527127 (composite basePrimes 20 13783235 527127) 0 1716124 (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk069_data) = true) :=
  ⟨by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk069_data]
    decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem counts69 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk069_data), 2 ≤ row.1 ∧ row.2.2.1 ≤ 1+oddCount ((row.1+1)/2) :=
  checkRows_counts baseComplete (markDepth := 20) (base := 13783235) (width := 527127)
    (by decide) (by decide) (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk069_data) (left := 0) (count := 1716124) state47 gate48.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem checked69 :
    ∀ row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk069_data), row.2.2.1 ≤ row.1.primeCounting :=
  bounds_from_counts counts69

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private theorem state48 : 1777637 ≤ oddCount 14310362 := by
  let row : Row := (28620723, 28638959, 1777638, 6341)
  have mem : row ∈ (Classical.choose OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk069_data) := by
    rw [Classical.choose_spec OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.chunk069_data]
    decide
  have h := (counts69 row mem).2
  have slot : (row.1+1)/2 = 14310362 := by decide
  have value : row.2.2.1 = 1777638 := rfl
  rw [slot,value] at h
  omega

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
theorem OMA.solution : OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1_H2_R1.H2 :=
  dispatchMiddle checked35 checked36 checked37 checked38 checked39 checked40 checked41 checked42 checked43 checked44 checked45 checked46 checked47 checked48 checked49 checked50 checked51 checked52 checked53 checked54 checked55 checked56 checked57 checked58 checked59 checked60 checked61 checked62 checked63 checked64 checked65 checked66 checked67 checked68 checked69